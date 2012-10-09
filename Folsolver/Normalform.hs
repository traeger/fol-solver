module Folsolver.Normalform
 ( abFormula, ABFormula(..)
 , isAlpha, isBeta, isLiteral, isAlphaFormula
   --
 , mkNeg, negQ, negNormal, negNormalNeg
 , isSimple, isQuant, reduction
 , RedFormula(..)
 , unifyFormula, unifyTerm, unifyEquals, variableRename
 ) where

import Folsolver.Normalform.ABFormula
import Folsolver.Normalform.NegNF
import Folsolver.Normalform.Unification
