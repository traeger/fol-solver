module Folsolver.Data.PQueue where

import Data.PurePriorityQueue (MinMaxQueue)
import qualified Data.PurePriorityQueue as PQ
import Data.Maybe (fromJust)

data PQueue k a = PQEmpty | Q (MinMaxQueue k a)

instance (Ord k, Show k, Show a) => Show (PQueue k a) where
  show PQEmpty = "{}"
  show q = "PQueue.fromList( " ++ (show $ toList q) ++ " )"

(|>) :: Ord k => PQueue k a -> (k,a) -> PQueue k a
PQEmpty |> (k,a)  = Q $ PQ.singleton a k
Q pq |> (k,a) = Q $ PQ.insert a k pq

empty :: PQueue k a
empty = PQEmpty

isEmpty :: PQueue k a -> Bool
isEmpty PQEmpty = True
isEmpty _       = False

peek :: Ord k => PQueue k a -> ((k,a), PQueue k a)
peek PQEmpty = error "peek does not support empty PQueues."
peek (Q pq) = 
  let 
    ((a,k), tail) = fromJust $ PQ.minView pq 
  in case () of
    _ | PQ.null tail -> ((k,a), PQEmpty)
      | otherwise    -> ((k,a), Q $ tail)

toList :: Ord k => PQueue k a -> [(k,a)]
toList PQEmpty = []
toList (Q pq) = map (\(x,y) -> (y,x)) $ PQ.toAscList pq

fromList :: Ord k => [(k,a)] -> PQueue k a
fromList [] = PQEmpty
fromList (x:xs) = (fromList xs) |> x