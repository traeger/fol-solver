module Folsolver.TPTP
 ( wrapF
 , pretty
 , transformOnInput
 ) where

import Codec.TPTP
import Data.Functor.Identity

-- wrap F around a Formula0 using Identity
-- reverse of unwrapF on Identity
wrapF :: Formula0 (T Identity) (F Identity) -> F Identity
wrapF e = F $ Identity e

-- pretty print of a formula
pretty :: Formula -> String
pretty f = (toTPTP f) ""

transformOnInput :: (Formula -> Formula) -> TPTP_Input -> TPTP_Input
transformOnInput fun (AFormula name role form anno) = AFormula name role (fun form) anno