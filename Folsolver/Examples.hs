module Folsolver.Examples
 ( readExample, readExampleUnsafe
 , axiom
 ) where

import System.IO
import System.IO.Unsafe
import Codec.TPTP

readExample :: String -> IO [TPTP_Input]
readExample filename = do
  content <- readFile filename
  return $ parse content

readExampleUnsafe :: String -> [TPTP_Input]
readExampleUnsafe = unsafePerformIO . readExample

axiom = readExampleUnsafe "Data/Examples/axiom.tptp"