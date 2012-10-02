module Folsolver.Tableau
 ( tableau ) where

import Codec.TPTP
import Folsolver.Normalform
import Folsolver.Data.Tableau

simplePick :: [Formula] -> (Formula, [Formula])
simplePick (f:fs) = (f,fs)

tableau
  :: ([Formula] -> (Formula, [Formula]))  -- pick function fuer die naechste formula
  -> [Formula]  -- noch nicht genutzten formulas
  -> Tableau
tableau pick formulas = tableau0 pick formulas (leaf [])

tableau0
  :: ([Formula] -> (Formula, [Formula]))  -- pick function fuer die naechste formula
  -> [Formula]  -- noch nicht genutzten formulas
  -> Tableau    -- kurzzeitiges Tableau (brauchen wir Ufer mehrere alpha schritte)
  -> Tableau
tableau0 pick [] t       = t
tableau0 pick formulas t = 
  let
    (f,fs) = pick formulas
    ab = abFormula f
  in case ab of
    Alpha a1 a2 -> tableau0 pick fs $ leaf $ (value t) ++ [a1, a2]
    Beta b1 b2  -> (tableau0 pick fs (leaf [b1]) ) <# (value t)++[f] #> (tableau0 pick fs (leaf [b2]) )
    NoType _    -> tableau0 pick fs $ leaf $ (value t) ++ ([f])