module Main 
 ( module Folsolver.TPTP
 , module Folsolver.Proofer
 , module Folsolver.FOTableau
 , module Folsolver.Examples
 , module Codec.TPTP
 , module Folsolver.LP
 , main
 ) where

import Folsolver.TPTP
import Folsolver.Proofer
import Folsolver.FOTableau
import Codec.TPTP
import Folsolver.Examples
import Folsolver.LP

import qualified Text.PrettyPrint.HughesPJ as Pretty

import System.Environment

proofFiles :: [(AtomicWord, [TPTP_Input])] -> [(Pretty.Doc, Pretty.Doc)]
proofFiles = map (\x -> (pretty $ fst x, pretty $ isNSATProof $ proofFOT $ snd x))


main :: IO ()
main = do
  interact (\x -> show $ pretty $ proofFOT $ parse x)