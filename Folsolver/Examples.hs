module Folsolver.Examples
 ( readExample, readExampleUnsafe
 , axiom1, axiom2, axiom3, f, uninterfunc, arithmetic1, arithmetic2
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
uninterfunc = readExampleUnsafe "Data/Examples/uninterfunc.tptp"
f = readExampleUnsafe "Data/Examples/f.tptp"

arithmetic1 = readExampleUnsafe "Data/Examples/arithmetic1.tptp"
arithmetic2 = readExampleUnsafe "Data/Examples/arithmetic2.tptp"