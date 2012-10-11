{-# OPTIONS_GHC -XTypeSynonymInstances -XFlexibleInstances #-}

module Folsolver.HasPretty
 ( HasPretty(..)
 , module Pretty
 ) where

import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map as Map
import Data.Map (Map)

import Text.PrettyPrint.HughesPJ as Pretty

class HasPretty a where
  pretty :: a -> Pretty.Doc

instance (HasPretty a) => HasPretty [a] where
  pretty as = Pretty.brackets $ Pretty.cat $ (Pretty.punctuate Pretty.comma) $ map pretty as

instance (HasPretty a, HasPretty b) => HasPretty (a,b) where
  pretty (a,b) = Pretty.parens $ pretty a <> Pretty.comma <> pretty b

instance (HasPretty a) => HasPretty (Set a) where
  pretty as = pretty $ Set.toList as

instance (HasPretty a, HasPretty b) => HasPretty (Map a b) where
  pretty as = pretty $ Map.toList as

instance HasPretty Int where
  pretty i = Pretty.text $ show i

instance HasPretty String where
  pretty s = Pretty.text $ s
