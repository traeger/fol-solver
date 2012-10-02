module Folsolver.Data.BinTree where

data BinTree v
 = BinNode {left :: BinTree v, value :: v, right :: BinTree v}
 | BinLeaf deriving (Show, Eq)

empty :: BinTree v
empty = BinLeaf

-- | l <# v #> r creates a new binary tree
-- | with l as the left child, v as the value an
-- | r as the right child of the new tree
(<#) :: BinTree v -> v -> (BinTree v -> BinTree v)
(#>) :: (BinTree v -> BinTree v) -> BinTree v -> BinTree v
infixl 6 <#
infixr 5 #>

left <# v = BinNode left v
lefthalf #> right = lefthalf right

instance Functor BinTree where
  fmap f tree = (fmap f $ left tree) <# (f $ value tree) #> (fmap f $ right tree)