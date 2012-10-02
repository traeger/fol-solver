module Folsolver.Tableau
 ( tableau ) where

import Codec.TPTP
import Folsolver.Normalform
import Folsolver.Data.Tableau
import Folsolver.TPTP

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
    Alpha a1 a2 -> tableau0 pick (fs++[a1,a2]) (leaf $ (value t) ++ [a1, a2])                      -- handle alpha formulas
    Beta b1 b2  -> (tableau0 pick fs (leaf [b1]) ) <# (value t) #> (tableau0 pick fs (leaf [b2]) ) -- handle beta formulas
    NoType _    -> case (unwrapF f) of
      (:~:) f0     -> case (unwrapF f0) of
        (:~:) f1      -> tableau0 pick (fs++[f1]) (leaf $ (value t) ++ [f1])                       -- handle double negate
        otherwise     -> tableau0 pick fs t
      otherwise -> tableau0 pick fs t