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

import Text.PrettyPrint.HughesPJ (($$))
import qualified Text.PrettyPrint.HughesPJ as Pretty

import System.Environment

proofFiles :: [(AtomicWord, [TPTP_Input])] -> [(Pretty.Doc, Pretty.Doc)]
proofFiles = map (\x -> (pretty $ fst x, pretty $ isNSATProof $ proofFOT $ snd x))

-- | reads a TPTP-input from stdin (as a string, as long as the stdin is not closed)
-- | proofs the tptp-input, prints the proof to the stdout.
-- | * the TPTP-input has to be conform to the TPTP-syntax 
-- |   (http://www.cs.miami.edu/~tptp/TPTP/SyntaxBNF.html)
-- |   see also (http://hackage.haskell.org/package/logic-TPTP)
-- | * first-order-logic with arithmetic is supported (fof)
main :: IO ()
main = do
  interact showProof where
    
showProof x =
  let
    parsed = parse x                                         -- parse the input
    problem = Pretty.nest 2 $ Pretty.cat $ map pretty parsed -- pretty prints the problem
    proof = pretty $ proofFOT parsed                         -- pretty prints the proof
  in show ( (Pretty.text "Problem:") $$ problem $$ Pretty.text "" ) ++
     show (Pretty.text "Result:" $$ Pretty.text "") ++
     show ( proof )