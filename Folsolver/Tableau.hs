{-# OPTIONS_GHC -XTypeSynonymInstances -XMultiParamTypeClasses -XFlexibleInstances -XTypeFamilies #-}

module Folsolver.Tableau
 ( tableau, checkTableau, proofSATTableau, Proofer(..), simplePick ) where

import Codec.TPTP
import Folsolver.Normalform
import Folsolver.Data.Tableau
import Folsolver.TPTP
import Folsolver.Proofer

import Data.Set (Set) 
import qualified Data.Set as S
import Data.Maybe (fromJust, fromMaybe)

import Text.PrettyPrint.HughesPJ as Pretty

simplePick :: [TPTP_Input] -> (TPTP_Input, [TPTP_Input])
simplePick (f:fs) = (f,fs)

tableau
  :: ([TPTP_Input] -> (TPTP_Input, [TPTP_Input]))  -- pick function fuer die naechste formula
  -> [TPTP_Input]  -- noch zu nutztende formulas
  -> Tableau
tableau pick formulas = tableau0 pick formulas (leaf formulas)

tableau0
  :: ([TPTP_Input] -> (TPTP_Input, [TPTP_Input]))  -- pick function fuer die naechste formula
  -> [TPTP_Input]  -- noch nicht genutzten formulas
  -> Tableau    -- kurzzeitiges Tableau (brauchen wir fuer mehrere alpha schritte)
  -> Tableau
tableau0 pick [] t       = t
tableau0 pick formulas t = 
  let
    name1 = AtomicWord "test"
    (f,fs) = pick formulas
    ab = abFormula $ formula f
  in case ab of
    Alpha a1 a2 -> 
        let
            at1 = AFormula (name1) (Role "theorem") a1 (Annotations (GTerm (GApp (AtomicWord "alpha1") [GTerm (GWord (name f))])) NoUsefulInfo)
            at2 = AFormula (name1) (Role "theorem") a2 (Annotations (GTerm (GApp (AtomicWord "alpha2") [GTerm (GWord (name f))])) NoUsefulInfo)
        in
            tableau0 pick (fs++[at1,at2]) (leaf $ value t ++ [at1, at2])               -- handle alpha formulas
    Beta b1 b2  -> 
        let
            bt1 = AFormula (name1) (Role "theorem") b1 (Annotations (GTerm (GApp (AtomicWord "beta1") [GTerm (GWord (name f))])) NoUsefulInfo)
            bt2 = AFormula (name1) (Role "theorem") b2 (Annotations (GTerm (GApp (AtomicWord "beta2") [GTerm (GWord (name f))])) NoUsefulInfo)
        in
            tableau0 pick (fs++[bt1]) (leaf [bt1])  <# value t #> tableau0 pick (fs++[bt2]) (leaf [bt2])  -- handle beta formulas
    NoType _    -> case stripDoubleNeg $ formula f of
      Just f0     -> 
        let
            f1 = AFormula (name1) (Role "theorem") f0 (Annotations (GTerm (GApp (AtomicWord "nneg") [GTerm (GWord (name f))])) NoUsefulInfo)
        in
            tableau0 pick (fs++[f1]) (leaf $ value t ++ [f1])                    -- handle double negate
      Nothing     -> tableau0 pick fs t

{-
 - | This function iterates over the tableau and checks
 - | whether the negate of a new formula already occured.
 - | If this is the case, it will step back with true.
 - | If we reach the bottom we will step back with false.
 -}
checkTableau 
    :: 
    Tableau             -- Current branch of the tableau
    -> Set Formula      -- Formulas seen so far
    -> Bool             
checkTableau BinEmpty _     = False
checkTableau t forms        = 
    let
        (cond, nForms)      = isClosed (map formula $ value t) forms
    in
        cond || (checkTableau (left t) nForms && checkTableau (right t) nForms)

isClosed :: [Formula] -> Set Formula -> (Bool, Set Formula)
isClosed [] forms              = (False, forms)
isClosed (x:xs) forms
    | isTrue x                  = isClosed xs forms
    | isFalse x                 = (True, forms)
    | S.member (noDoubleNeg ((.~.) x)) forms  = (True, forms)
    | otherwise                 = isClosed xs (S.insert x forms)
            
proofSATTableau 
    :: 
    Tableau             -- Current branch of the tableau
    -> Set Formula      -- Formulas seen so far
    -> Proof Tableau 
proofSATTableau BinEmpty forms = mkSATProof $ filter isLiteral $ S.toList $ forms
proofSATTableau t forms
    | closed                = 
        let
            witTPTP = filter (((==) $ fromJust witness).formula) $ value t
            tillWit = takeWhile (((/=) $ fromJust witness).formula) $ value t
        in
            mkNSATProof $ leaf $ witTPTP ++ tillWit
    | isSATProof proofLeft  = proofLeft
    | isSATProof proofRight = proofRight
    | otherwise             = mkNSATProof $ fromNSATProofT proofLeft <# value t #> fromNSATProofT proofRight
    where
        (closed, nForms, witness)  = isClosedWithWitness (map formula $ value t) forms
        proofLeft   = proofSATTableau (left t) nForms
        proofRight  = proofSATTableau (right t) nForms

isClosedWithWitness :: [Formula] -> Set Formula -> (Bool, Set Formula, Maybe Formula)
isClosedWithWitness [] forms              = (False, forms, Nothing)
isClosedWithWitness (x:xs) forms
    | isTrue x                  = isClosedWithWitness xs forms
    | isFalse x                 = (True, forms, Just x)
    | S.member (noDoubleNeg ((.~.) x)) forms  = (True, forms, Just x)
    | otherwise                 = isClosedWithWitness xs (S.insert x forms)
  
instance Proofer Tableau where
  data NSATProof Tableau = NSAT {fromNSATproofT :: Tableau} deriving Show
  data Picker Tableau = Picker {pick :: [TPTP_Input] -> (TPTP_Input, [TPTP_Input])}
  mkProofer (Picker picker) formulas = tableau picker formulas
  
  isSAT tableau formulas = not $ checkTableau tableau formulas
  proofSAT = proofSATTableau

mkNSATProof = mkProof . NSAT
fromNSATProofT = fromNSATproofT . getNSATProof0

instance HasPretty (NSATProof Tableau) where
  pretty (NSAT nsatproof) = Pretty.text "  [ tableau proof ]" $$ pretty nsatproof
