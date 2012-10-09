module Folsolver.Data.BinTreeS
 ( BinTreeS(..)
 , empty, leaf, (<#), (#>), (<|>)
 , subtree, modRootValue
 ) where

import Folsolver.TPTP
import Text.PrettyPrint.HughesPJ as Pretty hiding (empty)
import qualified Text.PrettyPrint.HughesPJ as Pretty (empty)

import qualified Control.Arrow as Arrow (first)

data BinTreeS v
 = BinNode {left :: BinTreeS v, value :: v, right :: BinTreeS v}
 | SNode {subTree :: BinTreeS v, value :: v}
 | BinEmpty deriving (Eq)

instance (Show v) => Show (BinTreeS v) where
  show BinEmpty = "^"
  show (SNode t v) = "( "++show v++" --> "++show t++" )"
  show tree = "(" ++ (show $ left tree) ++ ") <# " ++ (show $ value tree) ++ " #> (" ++ (show $ right tree) ++ ")"


instance (HasPretty v) => HasPretty (BinTreeS v) where
  pretty BinEmpty = Pretty.empty
  pretty (SNode t v) = (pretty v) $$ (pretty t)
  pretty tree =
       (pretty $ value tree)
    $$ Pretty.nest 2 (
         (pretty $ left tree)
      $$ (pretty $ right tree)
    )

empty :: BinTreeS v
empty = BinEmpty

leaf :: v -> BinTreeS v
leaf v = empty <# v #> empty

-- | l <# v #> r creates a new binary tree
-- | with l as the left child, v as the value an
-- | r as the right child of the new tree
(<#) :: BinTreeS v -> v -> (BinTreeS v -> BinTreeS v)
(#>) :: (BinTreeS v -> BinTreeS v) -> BinTreeS v -> BinTreeS v
(<|>) :: v -> BinTreeS v -> BinTreeS v
infixl 8 <#
infixr 2 #>
infixl 9 <|>

left <# v = BinNode left v
lefthalf #> right = lefthalf right

v <|> t = SNode t v

instance Functor BinTreeS where
    fmap f BinEmpty     = BinEmpty
    fmap f (SNode t v)  = f v <|> fmap f t
    fmap f tree = (fmap f $ left tree) <# (f $ value tree) #> (fmap f $ right tree)

-- | modifies the root value of a tree
modRootValue :: (v -> v) -> BinTreeS v -> BinTreeS v
modRootValue _ BinEmpty     = BinEmpty
modRootValue f (SNode t v)  = f v <|> t
modRootValue f t            = left t <# f (value t) #> right t

-- | subtree of a given path through the tree
-- | each element on the path will be returned together with the
-- | subtree where the path ends
-- |   when a False is find as a first element of a path the left subtree
-- |   will be chosen, otherwise (case True) the right subtree.
subtree :: [Bool] -> BinTreeS v -> ([v], BinTreeS v)
subtree _ BinEmpty      = ([], BinEmpty)
subtree [] t = ([], t)
subtree x (SNode t v)   = Arrow.first (v :) $  subtree x t
subtree (False:xs) t    = Arrow.first (value t :) $ subtree xs (left t)
subtree (True:xs) t     = Arrow.first (value t :) $ subtree xs (right t)
