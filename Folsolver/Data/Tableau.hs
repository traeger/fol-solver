module Folsolver.Data.Tableau 
 ( Tableau(..), BinTree(..)
 , empty, leaf, (<#), (#>)
 ) where

import Folsolver.Data.BinTree
import Codec.TPTP

type Tableau = BinTree [Formula]