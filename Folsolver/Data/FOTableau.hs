module Folsolver.Data.FOTableau
 ( FOTableau(..), module Folsolver.Data.BinTreeS
 , TC, mkTC, ($*$), formTC, dequantsTC, formTCT, dequantsTCT
 ) where

import Folsolver.Data.BinTreeS
import Codec.TPTP
import Data.Map

type TC = (TPTP_Input,[V])
mkTC :: TPTP_Input -> TC
mkTC formula = (formula, [])

infixl 9 $*$ 

-- | adds an universal quantifier variable, with its dequantifier variable
-- | (variables introduced via a gamma-rule)
($*$) :: TC -> (V, [V]) -> TC
(fs, dequantVars) $*$ (q, ds) = (fs, ds++dequantVars)

-- | formulas
formTC :: TC -> TPTP_Input
formTC = fst
formTCT :: BinTreeS TC -> TPTP_Input
formTCT = fst . value

-- | de-quantified variables. (variables introduced via a gamma-rule)
dequantsTC :: TC -> [V]
dequantsTC = snd
dequantsTCT :: BinTreeS TC -> [V]
dequantsTCT = snd . value

type FOTableau = BinTreeS TC
