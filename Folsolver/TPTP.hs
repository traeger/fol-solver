module Folsolver.TPTP
 ( wrapF
 , pretty, parseFormula
 , transformOnInput
 , true, isTrue
 , false, isFalse
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

-- | True and False represented in our system
true , false :: Formula
true    = wrapF $ PredApp (AtomicWord "true") []
false   = wrapF $ PredApp (AtomicWord "false") []

-- | Checks for True and False
isTrue , isFalse :: Formula -> Bool
isTrue  x   = case unwrapF x of
    (:~:) x0    -> isFalse x0
    _           -> x == true
isFalse x   = case unwrapF x of
    (:~:) x0    -> isTrue x0
    _           -> x == false 

parseFormula :: String -> [Formula]
parseFormula = map formula . parse
