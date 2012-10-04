{-# OPTIONS_GHC -XTypeFamilies #-}

module Folsolver.Proofer 
 ( SATProofer(..)
 ) where

import Codec.TPTP
import Data.Set
import Data.Maybe (isJust)

class SATProofer p where
  data SATProof p :: *
  
  -- | tests whether a set of formulas is satisfiable
  isSAT :: p -> Set Formula -> Bool
  -- | proofs whether a set of formulas is satisfiable
  -- | gives an counter example if it is not satisfiable
  proofSAT :: p -> Set Formula -> SATProof p
  -- | whether a proof is a satisfiable proof
  isSATProof :: SATProof p -> Bool
  isSATProof proof = isJust $ witnessSAT proof
  -- | whether a proof is a unsatisfiable proof
  isNSATProof :: SATProof p -> Bool
  isNSATProof = not . isSATProof
  -- | the witness of a SAT proof, Nothing if the proof was no SAT proof
  witnessSAT :: SATProof p -> Maybe ([Formula])