module Folsolver.Normalform
 ( abFormula, ABFormula(..)
 , isAlpha, isBeta, isLiteral
   --
 , mkNeg, negQ, negNormal, negNormalNeg
 ) where

import Folsolver.Normalform.ABFormula
import Folsolver.Normalform.NegNF
