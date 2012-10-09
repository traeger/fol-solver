{-# OPTIONS_GHC -XTypeSynonymInstances -XFlexibleInstances #-}

module Folsolver.TPTP
 ( wrapF
 , parse
 , parseFormula
 , transformOnInput
 , true, isTrue
 , false, isFalse
 , stripDoubleNeg, noDoubleNeg
 , HasPretty(..), Formula(..)
 , rnd, rndIO 
 , HasPretty(..)
 ) where

import Folsolver.HasPretty

import Codec.TPTP
import Data.Functor.Identity
import System.Random
import System.IO.Unsafe
import Data.Maybe (fromMaybe)
import Data.List (intercalate)

import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Set (Set)
import Data.Map (Map)

import Text.PrettyPrint.HughesPJ as Pretty

-- wrap F around a Formula0 using Identity
-- reverse of unwrapF on Identity
wrapF :: Formula0 (T Identity) (F Identity) -> F Identity
wrapF e = F $ Identity e

-- pretty print of a term
instance HasPretty Term where
  pretty f = Pretty.text $ (toTPTP f) ""

-- pretty print of a formula
instance HasPretty Formula where
  pretty f = Pretty.text $ (toTPTP f) ""

-- pretty to print TPTP
instance HasPretty TPTP_Input where
    pretty f = Pretty.text $ (toTPTP f) ""

instance HasPretty V where
  pretty (V v) = Pretty.text "V(" <> (Pretty.text $ v) <> Pretty.text ")"

instance HasPretty AtomicWord where
  pretty (AtomicWord s) = Pretty.text $ s

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

-- | Parse a set of axioms and conjectures and extract the formulas from them
parseFormula :: String -> [Formula]
parseFormula = map formula . parse

-- | strip a double negation for a formula 
-- | if the formula is not double negated, Nothing is returned.
stripDoubleNeg :: Formula -> Maybe Formula
stripDoubleNeg x = case unwrapF x of
  (:~:) x0 -> case unwrapF x0 of
    (:~:) x1 -> Just x1
    _        -> Nothing
  _        -> Nothing

-- | removes a double negation from a formula if present
-- |       ~~x --> x where x can be any formula
-- | otherwise --> id
noDoubleNeg :: Formula -> Formula
noDoubleNeg x = fromMaybe x (stripDoubleNeg x)
  
-- | returns a random value uniformly distributed in the closed interval [min,max] 
-- | in an IO-Monad
rndIO :: Random a => a -> a -> IO a
rndIO min max = getStdRandom (randomR (min,max))
-- | returns a random value uniformly distributed in the closed interval [min,max] 
-- | (uses unsafePerformIO, so be careful!)
rnd :: Random a => a -> a -> a
rnd min max = unsafePerformIO $ rndIO min max
