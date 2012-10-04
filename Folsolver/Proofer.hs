{-# OPTIONS_GHC -XTypeFamilies -XMultiParamTypeClasses -XFlexibleInstances -XFlexibleContexts -XUndecidableInstances #-}

module Folsolver.Proofer 
 ( Proofer(..), Proof, IsProof(..), HasPretty(..)
 , witnessSAT, witnessSAT0, getNSATProof, getNSATProof0
 ) where

import Codec.TPTP
import Data.Set
import Data.Maybe (isJust, fromJust)
import Folsolver.TPTP

class HasPretty (NSATProof p) => Proofer p where
  data NSATProof p :: *
  
  -- | tests whether a set of formulas is satisfiable
  isSAT :: p -> Set Formula -> Bool
  isSAT p = isSATProof . (proofSAT p)
  -- | proofs whether a set of formulas is satisfiable
  -- | gives an counter example if it is not satisfiable
  proofSAT :: p -> Set Formula -> Proof p
  -- | whether a proof is a satisfiable proof
  isSATProof :: Proof p -> Bool
  isSATProof (SAT _) = True
  isSATProof _       = False
  -- | whether a proof is a unsatisfiable proof
  isNSATProof :: Proof p -> Bool
  isNSATProof (NSAT _) = True
  isNSATProof _        = False
  
  -- | minmal definition: proofSAT
  
data Proof p = SAT [Formula] | NSAT (NSATProof p)
instance HasPretty (NSATProof p) => HasPretty (Proof p) where
  pretty (SAT satproof)   = "satisfiable: " ++ show satproof
  pretty (NSAT nsatproof) = "unsatisfiable: " ++ pretty nsatproof

class (Proofer p) => IsProof a p where
  mkProof :: a -> Proof p

instance (Proofer p) => IsProof [Formula] p where
  mkProof = SAT
  
instance (Proofer p) => IsProof (NSATProof p) p where
  mkProof = NSAT
  
-- | the witness of a SAT proof, Nothing if the proof was no SAT proof
witnessSAT :: Proof p -> Maybe ([Formula])
witnessSAT (SAT formulas) = Just formulas
witnessSAT _ = Nothing
-- | like getSATProof but assumes that the proof was a SAT proof
witnessSAT0 :: Proof p -> [Formula]
witnessSAT0 = fromJust . witnessSAT
-- | the nsat proof, Nothing if the proof was no NSAT proof
getNSATProof :: Proof p -> Maybe (NSATProof p)
getNSATProof (NSAT nsatp) = Just nsatp
getNSATProof _ = Nothing
-- | like getNSATProof but assumes that the proof was a NSAT proof
getNSATProof0 :: Proof p -> NSATProof p
getNSATProof0 = fromJust . getNSATProof