module Folsolver.Data.BinTree
 ( BinTree(..)
 , empty, leaf, (<#), (#>)
 ) where

data BinTree v
 = BinNode {left :: BinTree v, value :: v, right :: BinTree v}
 | BinEmpty deriving (Show, Eq)

empty :: BinTree v
empty = BinEmpty

leaf :: v -> BinTree v
leaf v = empty <# v #> empty

-- | l <# v #> r creates a new binary tree
-- | with l as the left child, v as the value an
-- | r as the right child of the new tree
(<#) :: BinTree v -> v -> (BinTree v -> BinTree v)
(#>) :: (BinTree v -> BinTree v) -> BinTree v -> BinTree v
infixl 9 <#
infixr 2 #>

left <# v = BinNode left v
lefthalf #> right = lefthalf right

instance Functor BinTree where
  fmap f BinEmpty = BinEmpty
  fmap f tree = (fmap f $ left tree) <# (f $ value tree) #> (fmap f $ right tree)