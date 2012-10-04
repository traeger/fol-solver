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

simplePick :: [Formula] -> (Formula, [Formula])
simplePick (f:fs) = (f,fs)

tableau
  :: ([Formula] -> (Formula, [Formula]))  -- pick function fuer die naechste formula
  -> [Formula]  -- noch nicht genutzten formulas
  -> Tableau
tableau pick formulas = tableau0 pick formulas (leaf formulas)

tableau0
  :: ([Formula] -> (Formula, [Formula]))  -- pick function fuer die naechste formula
  -> [Formula]  -- noch nicht genutzten formulas
  -> Tableau    -- kurzzeitiges Tableau (brauchen wir fuer mehrere alpha schritte)
  -> Tableau
tableau0 pick [] t       = t
tableau0 pick formulas t = 
  let
    (f,fs) = pick formulas
    ab = abFormula f
  in case ab of
    Alpha a1 a2 -> tableau0 pick (fs++[a1,a2]) (leaf $ value t ++ [a1, a2])               -- handle alpha formulas
    Beta b1 b2  -> tableau0 pick (fs++[b1]) (leaf [b1])  <# value t #> tableau0 pick (fs++[b2]) (leaf [b2])  -- handle beta formulas
    NoType _    -> case stripDoubleNeg f of
      Just f0     -> tableau0 pick (fs++[f0]) (leaf $ value t ++ [f0])                    -- handle double negate
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
        (cond, nForms)      = isClosed (value t) forms
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
    | closed                = mkNSATProof $ leaf $ (flip (++) [fromJust witness]) $ takeWhile ((fromJust witness) /=) $ value t
    | isSATProof proofLeft  = proofLeft
    | isSATProof proofRight = proofRight
    | otherwise             = mkNSATProof $ fromNSATProofT proofLeft <# value t #> fromNSATProofT proofRight
    where
        (closed, nForms, witness)  = isClosedWithWitness (value t) forms
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
  data Picker Tableau = Picker {pick :: [Formula] -> (Formula, [Formula])}
  mkProofer (Picker picker) formulas = tableau picker formulas
  
  isSAT tableau formulas = not $ checkTableau tableau formulas
  proofSAT = proofSATTableau

mkNSATProof = mkProof . NSAT
fromNSATProofT = fromNSATproofT . getNSATProof0

instance HasPretty (NSATProof Tableau) where
  pretty (NSAT nsatproof) = Pretty.text "  [ tableau proof ]" $$ pretty nsatproof
