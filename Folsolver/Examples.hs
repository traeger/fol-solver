{-# OPTIONS_GHC -XOverloadedStrings #-}

module Folsolver.Examples
 ( readExample, readExampleUnsafe
 , axiom1, axiom2, axiom3, f, uninterfunc, infinitalpha
 ) where

import System.IO
import System.IO.Unsafe
import Codec.TPTP
import Folsolver.TPTP

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

infinitalpha :: TPTP_Input
infinitalpha = 
  let 
    f = f .&. f 
    [a,b] = parseFormula "fof(ax,axiom,a). fof(ax,axiom,~a)."
  in
    AFormula ("infinit alpha") (Role "plain") (a .&. (b .&. f)) NoAnnotations 