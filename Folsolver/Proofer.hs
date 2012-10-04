{-# OPTIONS_GHC -XTypeFamilies -XMultiParamTypeClasses -XFlexibleInstances -XFlexibleContexts -XUndecidableInstances #-}

module Folsolver.Proofer 
 ( Proofer(..), Proof, IsProof(..), mkSATProof
 , witnessSAT, witnessSAT0, getNSATProof, getNSATProof0
 , isTaut, proofTaut
 , isTautInput, proofTautInput, mkProoferInput
 , axiomsFromInput, conjecturesFromInput, transformInput
 ) where

import Codec.TPTP
import Data.Set as Set
import Data.Maybe (isJust, fromJust)
import Folsolver.TPTP
import Data.List (intercalate)
import Text.PrettyPrint.HughesPJ as Pretty

class HasPretty (NSATProof p) => Proofer p where
  data NSATProof p :: *
  data Picker p :: *
  
  mkProofer :: Picker p -> [Formula] -> p
  
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
  
  -- | minmal definition: NSATProof p, proofSAT
  
data Proof p = SAT [Formula] | NSAT (NSATProof p) | TAUTOLOGY (NSATProof p) | CONTRADICTION [Formula]
instance HasPretty (NSATProof p) => HasPretty (Proof p) where
  pretty (SAT witness)            = Pretty.text "satisfiable:"   $$ Pretty.nest 2 (pretty witness)
  pretty (NSAT nsatproof)         = Pretty.text "unsatisfiable:" $$ Pretty.nest 2 (pretty nsatproof)
  pretty (TAUTOLOGY nsatproof)    = Pretty.text "tautology:"     $$ Pretty.nest 2 (pretty nsatproof)
  pretty (CONTRADICTION witness)  = Pretty.text "contradiction:" $$ Pretty.nest 2 (pretty witness)
class (Proofer p) => IsProof a p where
  mkProof :: a -> Proof p

instance (Proofer p) => IsProof [Formula] p where
  mkProof = SAT
  
instance (Proofer p) => IsProof (NSATProof p) p where
  mkProof = NSAT

-- | synonym for mkProof for naming conventions
mkSATProof :: IsProof [Formula] p => [Formula] -> Proof p
mkSATProof = mkProof
  
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

axiomsFromInput, conjecturesFromInput :: [TPTP_Input] -> [Formula]
axiomsFromInput [] = []
axiomsFromInput (AFormula _ (Role "axiom") f _:xs) = f : axiomsFromInput xs
axiomsFromInput (_:xs) = axiomsFromInput xs
conjecturesFromInput [] = []
conjecturesFromInput (AFormula _ (Role "conjecture") f _:xs) = f : conjecturesFromInput xs
conjecturesFromInput (_:xs) = conjecturesFromInput xs

{-
 - | Takes the formulas from the input
 - | if it is a conjecture it will be negated
 -} 
transformInput :: [TPTP_Input] -> [Formula]
transformInput []                                           = []
transformInput (AFormula _ (Role "conjecture") f _:xs)      = ((.~.) f) : transformInput xs
transformInput (AFormula _ (Role "axiom") f _:xs)           = f : transformInput xs
transformInput (_:xs)                                       = transformInput xs

-- |
-- |
transformInputForTautologieCheck :: [TPTP_Input] -> ([Formula], [Formula])
transformInputForTautologieCheck input = 
  let
    axioms = axiomsFromInput input
    conjectures = conjecturesFromInput input
  in (axioms, conjectures)

mkProoferInput :: Proofer p => Picker p -> [TPTP_Input] -> p
mkProoferInput picker input = mkProofer picker $ transformInput input

-- |
-- |
isTautInput :: Proofer p => Picker p -> [TPTP_Input] -> Bool
isTautInput picker input = uncurry (isTaut picker) $ transformInputForTautologieCheck input

isTaut :: Proofer p => Picker p -> [Formula] -> [Formula] -> Bool
isTaut picker axioms conjectures = not $ isSAT (mkProofer picker $ axioms ++ (Prelude.map (.~.) conjectures)) Set.empty

-- |
-- |
proofTautInput :: Proofer p => Picker p -> [TPTP_Input] -> Proof p
proofTautInput picker input = uncurry (proofTaut picker) $ transformInputForTautologieCheck input

proofTaut :: Proofer p => Picker p -> [Formula] -> [Formula] -> Proof p
proofTaut picker axioms conjectures = 
  case proofSAT (mkProofer picker $ axioms ++ (Prelude.map (.~.) conjectures)) Set.empty of
    NSAT nsatproof -> TAUTOLOGY nsatproof
    SAT witness    -> CONTRADICTION witness