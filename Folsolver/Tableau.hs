{-# OPTIONS_GHC -XTypeSynonymInstances -XMultiParamTypeClasses -XFlexibleInstances -XTypeFamilies #-}

module Folsolver.Tableau
 ( tableau, tableauProof, simplePick ) where

import Codec.TPTP
import Folsolver.Normalform
import Folsolver.Data.Tableau
import Folsolver.TPTP
import Folsolver.Proofer

import Data.Set (Set) 
import qualified Data.Set as S
import Data.Maybe (fromJust, fromMaybe)

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
    Beta b1 b2  -> tableau0 pick fs (leaf [b1])  <# value t #> tableau0 pick fs (leaf [b2])  -- handle beta formulas
    NoType _    -> case stripDoubleNeg f of
      Just f0     -> tableau0 pick (fs++[f0]) (leaf $ value t ++ [f0])                    -- handle double negate
      Nothing     -> tableau0 pick fs t

{- 
 - | This tableau Proover takes a List of TPTP inputs,
 - | momentarily only axiom and conjecture,
 - |
 - | It returns true iff the input is satisfiable.
 -}
tableauProof :: ([Formula] -> (Formula, [Formula])) -> [TPTP_Input] -> Bool
tableauProof pick input = checkTableau (tableau pick $ transformInput input) S.empty

{- 
 - | This tableau Proover takes a List of TPTP inputs,
 - | momentarily only axiom and conjecture,
 - |
 - | It returns true iff the input is satisfiable.
 -}
tableauProofWithProof :: ([Formula] -> (Formula, [Formula])) -> [TPTP_Input] -> SATProof Tableau
tableauProofWithProof pick input = checkTableauWithProof (tableau pick $ transformInput input) S.empty
 
  
{-
 - | Takes the formulas from the input
 - | if it is a conjecture it will be negated
 -} 
transformInput :: [TPTP_Input] -> [Formula]
transformInput []                                           = []
transformInput (AFormula _ (Role "conjecture") f _:xs)      = ((.~.) f) : transformInput xs
transformInput (AFormula _ (Role "axiom") f _:xs)           = f : transformInput xs
transformInput (_:xs)                                       = transformInput xs

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
            
checkTableauWithProof 
    :: 
    Tableau             -- Current branch of the tableau
    -> Set Formula      -- Formulas seen so far
    -> SATProof Tableau 
checkTableauWithProof BinEmpty forms = mkSATProofT $ S.toList $ forms
checkTableauWithProof t forms
    | closed                 = mkSATProofT $ (flip (++) [fromJust witness]) $ takeWhile ((fromJust witness) ==) $ value t
    | isSATProofT proofLeft  = proofLeft
    | isSATProofT proofRight = proofRight
    | otherwise              = mkNSATProofT $ fromNSATproofT proofLeft <# value t #> fromNSATproofT proofRight
    where
        (closed, nForms, witness)  = isClosedWithProof (value t) forms
        proofLeft   = checkTableauWithProof (left t) nForms
        proofRight  = checkTableauWithProof (right t) nForms

isClosedWithProof :: [Formula] -> Set Formula -> (Bool, Set Formula, Maybe Formula)
isClosedWithProof [] forms              = (False, forms, Nothing)
isClosedWithProof (x:xs) forms
    | isTrue x                  = isClosedWithProof xs forms
    | isFalse x                 = (True, forms, Just x)
    | S.member (noDoubleNeg ((.~.) x)) forms  = (True, forms, Just x)
    | otherwise                 = isClosedWithProof xs (S.insert x forms)
  
instance SATProofer Tableau where
  data SATProof Tableau
   = SAT {witnessT :: [Formula]} 
   | NSAT {fromNSATproofT :: Tableau} deriving Show
  
  isSAT tableau formulas = checkTableau tableau formulas
  proofSAT tableau formulas = checkTableauWithProof tableau formulas
  witnessSAT proof = if isSATProofT proof 
                        then Just $ witnessT proof 
                        else Nothing
  
mkSATProofT  :: [Formula] -> SATProof Tableau
mkNSATProofT :: Tableau -> SATProof Tableau
mkSATProofT = SAT
mkNSATProofT = NSAT

isSATProofT, isNSATProofT :: SATProof Tableau -> Bool
isSATProofT (SAT _) = True
isSATProofT _ = False
isNSATProofT (NSAT _) = True
isNSATProofT _ = False