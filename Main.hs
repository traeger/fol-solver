module Main 
 ( module Folsolver.TPTP
 , module Folsolver.Proofer
 , module Folsolver.FOTableau
 , module Folsolver.Examples
 , main
 ) where

import Folsolver.TPTP
import Folsolver.Proofer
import Folsolver.FOTableau
import Folsolver.Examples

import System.IO
import Control.Monad

readInput :: [String] -> IO ([String])
readInput xs = do
    end <- isEOF
    if end then return xs
    else do
        x <- readLn
        readInput (x:xs)

main = do
    input <- liftM reverse $ readInput []
    putStrLn $ show $  pretty $ proofFOT $ parse $ concat input
    return ()
