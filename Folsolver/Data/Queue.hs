module Folsolver.Data.Queue where

data Queue a = QEmpty | Q [a] [a]

instance (Show a) => Show (Queue a) where
  show q = "toList ( " ++ (show $ toList q) ++ " )"  

(|>) :: Queue a -> a -> Queue a
QEmpty |> x  = Q [x] []
Q ls rs |> x = Q ls (x:rs)

empty :: Queue a
empty = QEmpty

isEmpty :: Queue a -> Bool
isEmpty QEmpty = True
isEmpty _      = False

peek :: Queue a -> (a, Queue a)
peek QEmpty = error "peek does not support empty queues."
peek (Q (l:[]) []) = (l, QEmpty)
peek (Q (l:ls) rs) = (l, Q ls rs)
peek (Q [] rs) = peek (Q (reverse rs) [])

toList :: Queue a -> [a]
toList QEmpty    = []
toList (Q ls rs) = ls ++ (reverse rs)

fromList :: [a] -> Queue a
fromList [] = QEmpty
fromList xs = Q xs []