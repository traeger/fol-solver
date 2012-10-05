module Folsolver.Data.Tableau 
 ( Tableau(..), module Folsolver.Data.BinTree
 ) where

import Folsolver.Data.BinTree
import Codec.TPTP

type Tableau = BinTree [TPTP_Input]
