module Folsolver.Tableau
 ( tableau, tableauProof, simplePick ) where

import Codec.TPTP
import Folsolver.Normalform
import Folsolver.Data.Tableau
import Folsolver.TPTP

import Data.Set (Set) 
import qualified Data.Set as S

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
    Alpha a1 a2 -> tableau0 pick (fs++[a1,a2]) (leaf $ value t ++ [a1, a2])                        -- handle alpha formulas
    Beta b1 b2  -> tableau0 pick fs (leaf [b1])  <# value t #> tableau0 pick fs (leaf [b2])        -- handle beta formulas
    NoType _    -> case unwrapF f of
      (:~:) f0     -> case unwrapF f0 of
        (:~:) f1      -> tableau0 pick (fs++[f1]) (leaf $ value t ++ [f1])                       -- handle double negate
        otherwise     -> tableau0 pick fs t
      otherwise -> tableau0 pick fs t

{- 
 - | This tableau Proover takes a List of TPTP inputs,
 - | momentarily only axiom and conjecture,
 - |
 - | It returns true iff the input is satisfiable.
 -}
tableauProof :: ([Formula] -> (Formula, [Formula])) -> [TPTP_Input] -> Bool
tableauProof pick input = checkTableau (tableau pick $ transformInput input) S.empty
 
  
{-
 - | Takes the formulas from the input
 - | if it is a conjecture it will be negated
 -} 
transformInput :: [TPTP_Input] -> [Formula]
transformInput []                                           = []
transformInput (AFormula _ (Role "conjecture") f _:xs)      = (f .~.) : transformInput xs
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
        (cond, nForms)      = checkNode (value t) forms
    in
        cond || (checkTableau (left t) nForms && checkTableau (right t) nForms)


checkNode :: [Formula] -> Set Formula -> (Bool,Set Formula)
checkNode [] forms              = (False, forms)
checkNode (x:xs) forms
    | S.member (x .~.) forms  = (True, forms)
    | otherwise                 = checkNode xs (S.insert x forms)
