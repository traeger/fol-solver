module Folsolver.Data.FOTableau
 ( FOTableau(..), module Folsolver.Data.BinTreeS
 ) where

import Folsolver.Data.BinTreeS
import Codec.TPTP

type FOTableau = BinTreeS ([TPTP_Input] , [V])
