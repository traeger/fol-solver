{-# OPTIONS_GHC -XTypeSynonymInstances -XFlexibleInstances #-}

-- | this is a priority queue, where
-- | the order is
-- | atom < negate alpha < beta < delta < gamma

module Folsolver.Normalform.FormulaPQueue
 ( FormPQ(..), PQueue(..), HasRedFormula(..)
 , (|>), peek, fromList, toList
 , PQ.empty
 ) where

import Codec.TPTP
import Folsolver.Normalform.ABFormula
import Folsolver.Data.PQueue(PQueue)
import qualified Folsolver.Data.PQueue as PQ

class HasRedFormula a where
  redFormula :: a -> RedFormula
  
instance HasRedFormula Formula where
  redFormula = reduction

type FormPQ a = PQueue RedFormula a
(|>) :: HasRedFormula a => FormPQ a -> a -> FormPQ a
pq |> x = pq PQ.|> (redFormula x, x)

peek :: HasRedFormula a => FormPQ a -> (a, FormPQ a)
peek pq = let ((k,a), pq') = PQ.peek pq in (a, pq')

fromList :: HasRedFormula a => [a] -> FormPQ a
fromList = PQ.fromList . map (\x -> (redFormula x, x))

toList :: HasRedFormula a => FormPQ a -> [a]
toList = map snd . PQ.toList

instance Ord RedFormula where
  (AlphaR x1 x2) <= (AlphaR y1 y2)  = (x1, x2) <= (y1, y2)
  (BetaR x1 x2)  <= (BetaR y1 y2)   = (x1, y2) <= (y1, y2)
  (GammaR x v) <= (GammaR y w)      = (x, v) <= (y, w)
  (DeltaR x v) <= (DeltaR y w)      = (x, v) <= (y, w)
  (DNegate x) <= (DNegate y)        = x <= y
  (AtomR x) <= (AtomR y)            = x <= y
  a <= b                            = abConstPrio a <= abConstPrio b

-- | priority of the constructor terms of ab-formulas
-- | atom < negate alpha < beta < delta < gamma
abConstPrio :: RedFormula -> Int
abConstPrio (AtomR _)    = 1
abConstPrio (DNegate _)  = 2
abConstPrio (AlphaR _ _) = 3
abConstPrio (BetaR _ _)  = 4
abConstPrio (DeltaR _ _) = 5
abConstPrio (GammaR _ _) = 6