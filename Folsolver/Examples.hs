module Folsolver.Examples where

import System.IO
import System.IO.Unsafe
import Codec.TPTP
import System.Directory

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
quant1 = readExampleUnsafe "Data/Examples/quant_1.tptp"
quant2 = readExampleUnsafe "Data/Examples/quant_2.tptp"
quant3 = readExampleUnsafe "Data/Examples/quant_3.tptp"
quant4 = readExampleUnsafe "Data/Examples/quant_4.tptp"
quant5 = readExampleUnsafe "Data/Examples/Cant/quant_5.tptp"

agatha = readExampleUnsafe "Data/Examples/agatha.tptp"

arithmetic1 = readExampleUnsafe "Data/Examples/arithmetic1.tptp"
arithmetic2 = readExampleUnsafe "Data/Examples/arithmetic2.tptp"
arithmetic3 = readExampleUnsafe "Data/Examples/arithmetic3.tptp"

counter1 = readExampleUnsafe "Data/Examples/Counter/counter1.tptp"

counters = map snd countersS
examples = map snd examplesS
cant = map snd cantS

countersS = readDirUnsafe "Data/Examples/Counter/SYN/"
examplesS = readDirUnsafe "Data/Examples/"
cantS = readDirUnsafe "Data/Examples/Cant/"

readDirUnsafe :: String -> [(AtomicWord, [TPTP_Input])]
readDirUnsafe dir = unsafePerformIO $ do
  files <- getDirectoryContents dir
  let files0 = map (dir ++ ) $ files
  let files1 = filter (unsafePerformIO . doesFileExist) $ files0
  let cs = zip (map AtomicWord files1) (map readExampleUnsafe $ files1)
  return cs
