module Folsolver.Examples
 ( readExample, readExampleUnsafe
 , axiom1, axiom2, axiom3
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

axiom1 = readExampleUnsafe "Data/Examples/axiom1.tptp"
axiom2 = readExampleUnsafe "Data/Examples/axiom2.tptp"
axiom3 = readExampleUnsafe "Data/Examples/axiom3.tptp"