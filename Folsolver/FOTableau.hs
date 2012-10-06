{-# OPTIONS_GHC -XTypeSynonymInstances -XMultiParamTypeClasses -XFlexibleInstances -XTypeFamilies #-}

module Folsolver.Tableau
 ( tableau, checkTableau, proofSATTableau, Proofer(..), simplePick
 , checkT, proofT, subProof, decToBin ) where

import Codec.TPTP
import Folsolver.Normalform
import Folsolver.Data.Tableau
import Folsolver.TPTP
import Folsolver.Proofer
import Folsolver.Data.TPTP_gen

import Data.Set (Set) 
import qualified Data.Set as S
import Data.Maybe (fromJust, fromMaybe)
import Data.List (nub)

import Text.PrettyPrint.HughesPJ as Pretty

simplePick :: [TPTP_Input] -> (TPTP_Input, [TPTP_Input])
simplePick (f:fs) = (f,fs)

tableau
  :: ([TPTP_Input] -> (TPTP_Input, [TPTP_Input]))  -- pick function fuer die naechste formula
  -> [TPTP_Input]  -- noch zu nutztende formulas
  -> Tableau
tableau pick formulas = tableau0 pick 1 formulas (leaf formulas)

tableau0
  :: ([TPTP_Input] -> (TPTP_Input, [TPTP_Input]))  -- pick function fuer die naechste formula
  -> Integer
  -> [TPTP_Input]  -- noch nicht genutzten formulas
  -> Tableau    -- kurzzeitiges Tableau (brauchen wir fuer mehrere alpha schritte)
  -> Tableau
tableau0 pick pos [] t          = t
tableau0 pick pos formulas t    = 
  let
    nameFun p q = "genFunction_"++(show p)++"_"++(show q)
    (f,fs) = pick formulas
    ab = abFormula $ formula f
  in case ab of
    Alpha a1 a2 -> 
        let
            at1 = mkTPTP (nameFun pos $ (length $ value t)) "plain" a1 [("alpha1",[show.name $ f])]
            at2 = mkTPTP (nameFun pos $ (length $ value t)+1) "plain" a2 [("alpha2",[show.name $ f])]
        in
            tableau0 pick pos (fs++[at1,at2]) (leaf $ value t ++ [at1, at2])               -- handle alpha formulas
    Beta b1 b2  -> 
        let
            bt1 = mkTPTP (nameFun (pos * 2) 1) "plain" b1 [("beta1",[show.name $ f])]
            bt2 = mkTPTP (nameFun ((2*pos)+1) 1) "plain" b2 [("beta2",[show.name $ f])]
        in
            tableau0 pick (2*pos) (fs++[bt1]) (leaf [bt1])  <# value t #> tableau0 pick (2*pos + 1) (fs++[bt2]) (leaf [bt2])  -- handle beta formulas
    NoType _    -> case stripDoubleNeg $ formula f of
      Just f0     -> 
        let
            f1 = mkTPTP (nameFun pos $ (length $ value t)) "plain" f0 [("negate",[show.name $ f])]
        in
            tableau0 pick pos (fs++[f1]) (leaf $ value t ++ [f1])                    -- handle double negate
      Nothing     -> tableau0 pick pos fs t

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
    -> Set TPTP_Input      -- Formulas seen so far
    -> Proof Tableau 
proofSATTableau BinEmpty forms = mkSATProof $ nub $ filter isLiteral $ (map formula) $ S.toList $ forms
proofSATTableau t forms
    | closed                = 
        let
            witTPTP     = head $ filter ((==) $ fromJust witness) $ value t
            tillWit     = takeWhile ((/=) $ fromJust witness) $ value t
            wName       = let (AtomicWord x) = name witTPTP in drop 12 x
            cond        = head $ filter (((==) (noDoubleNeg ((.~.) $ formula witTPTP))).formula) ((S.toList forms)++(value t))
            term        = wrapF (BinOp (formula cond) (:&:) (formula witTPTP))
            contradict = mkTPTP ("contradict_"++wName) "plain" term [("contradiction_of",[show $ name cond, show $ name witTPTP])]
        in
            mkNSATProof $ leaf $ tillWit ++ [witTPTP,contradict]
    | isSATProof proofLeft  = proofLeft
    | isSATProof proofRight = proofRight
    | otherwise             = mkNSATProof $ fromNSATProofT proofLeft <# value t #> fromNSATProofT proofRight
    where
        (closed, nForms, witness)  = isClosedWithWitness (value t) forms
        proofLeft   = proofSATTableau (left t) nForms
        proofRight  = proofSATTableau (right t) nForms

isClosedWithWitness :: [TPTP_Input] -> Set TPTP_Input -> (Bool, Set TPTP_Input, Maybe TPTP_Input)
isClosedWithWitness [] forms              = (False, forms, Nothing)
isClosedWithWitness (x:xs) forms
    | isTrue (formula x)        = isClosedWithWitness xs forms
    | isFalse (formula x)       = (True, forms, Just x)
    | S.member (noDoubleNeg ((.~.) (formula x))) (S.map formula forms)  
                                = (True, forms, Just x)
    | otherwise                 = isClosedWithWitness xs (S.insert x forms)
  
instance Proofer Tableau where
  data NSATProof Tableau = NSAT {fromNSATproofT :: Tableau} deriving Show
  data Picker Tableau = Picker {pick :: [TPTP_Input] -> (TPTP_Input, [TPTP_Input])}
  mkProofer (Picker picker) formulas = tableau picker formulas
  
  isSAT tableau = not $ checkTableau tableau S.empty
  proofSAT t = proofSATTableau t S.empty

mkNSATProof = mkProof . NSAT
fromNSATProofT = fromNSATproofT . getNSATProof0

instance HasPretty (NSATProof Tableau) where
  pretty (NSAT nsatproof) = Pretty.text "  [ tableau proof ]" $$ pretty nsatproof

-- | shorthands to use a tableau proofer
proofT = proof (Picker simplePick)
checkT = check (Picker simplePick)

-- | shows a subtree
subProof :: Int -> Proof Tableau -> Tableau
subProof number (t) = (subProof0 number $ fromNSATProofT t)
subProof0 :: Int -> Tableau -> Tableau
subProof0 number t = 
  let 
    (path, t0) = subtree (tail $ map (intToBool) $ decToBin $ number) t
  in
    if number < 2 then t 
    else modRootValue ((concat path) ++ ) t0 where
      intToBool 0 = False
      intToBool _ = True
      
decToBin 0 = [0]
decToBin x = reverse $ decToBin' x where
  decToBin' 0 = []
  decToBin' y = let (a,b) = quotRem y 2 in [b] ++ decToBin' a
