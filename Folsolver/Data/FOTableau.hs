module Folsolver.Data.FOTableau
 ( FOTableau(..), module Folsolver.Data.BinTreeS
 , TC, mkTC, ($+$), ($++$), ($*$), formsTC, dequantsTC, formsTCT, dequantsTCT
 ) where

import Folsolver.Data.BinTreeS
import Codec.TPTP
import Data.Map

type TC = ([TPTP_Input],[V])
mkTC :: TC
mkTC = ([], [])

infixl 9 $+$ 
infixl 9 $++$ 
infixl 9 $*$ 

-- | adds an formula
($+$) :: TC -> TPTP_Input -> TC
($++$) :: TC -> [TPTP_Input] -> TC
-- | adds an universal quantifier variable, with its dequantifier variable
-- | (variables introduced via a gamma-rule)
($*$) :: TC -> (V, [V]) -> TC
(fs, dequantVars) $+$ formula = (fs++[formula], dequantVars)
(fs, dequantVars) $++$ formulas = (fs++formulas, dequantVars)
(fs, dequantVars) $*$ (q, ds) = (fs, ds++dequantVars)

-- | formulas
formsTC :: TC -> [TPTP_Input]
formsTC = fst
formsTCT :: BinTreeS TC -> [TPTP_Input]
formsTCT = fst . value

-- | de-quantified variables. (variables introduced via a gamma-rule)
dequantsTC :: TC -> [V]
dequantsTC = snd
dequantsTCT :: BinTreeS TC -> [V]
dequantsTCT = snd . value

type FOTableau = BinTreeS TC
