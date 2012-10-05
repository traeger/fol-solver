module Folsolver.Data.BinTree
 ( BinTree(..)
 , empty, leaf, (<#), (#>)
 , subtree, modRootValue
 ) where

import Folsolver.TPTP
import Text.PrettyPrint.HughesPJ as Pretty hiding (empty)
import qualified Text.PrettyPrint.HughesPJ as Pretty (empty)

import qualified Control.Arrow as Arrow (first)

data BinTree v
 = BinNode {left :: BinTree v, value :: v, right :: BinTree v}
 | BinEmpty deriving (Eq)

instance (Show v) => Show (BinTree v) where
  show BinEmpty = "^"
  show tree = "(" ++ (show $ left tree) ++ ") <# " ++ (show $ value tree) ++ " #> (" ++ (show $ right tree) ++ ")"

instance (HasPretty v) => HasPretty (BinTree v) where
  pretty BinEmpty = Pretty.empty
  pretty tree = 
       (pretty $ value tree)
    $$ Pretty.nest 2 ( 
         (pretty $ left tree) 
      $$ (pretty $ right tree)
    )

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

-- | modifies the root value of a tree
modRootValue :: (v -> v) -> BinTree v -> BinTree v
modRootValue _ BinEmpty = BinEmpty
modRootValue f t = left t <# f (value t) #> right t

-- | subtree of a given path through the tree
-- | each element on the path will be returned together with the
-- | subtree where the path ends
-- |   when a False is find as a first element of a path the left subtree
-- |   will be chosen, otherwise (case True) the right subtree.
subtree :: [Bool] -> BinTree v -> ([v], BinTree v)
subtree _ BinEmpty = ([], BinEmpty)
subtree [] t = ([], t)
subtree (False:xs) t = Arrow.first (value t :) $ subtree xs (left t)
subtree (True:xs) t = Arrow.first (value t :) $ subtree xs (right t)
