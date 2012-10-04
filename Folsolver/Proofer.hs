{-# OPTIONS_GHC -XTypeFamilies -XMultiParamTypeClasses -XFlexibleInstances -XFlexibleContexts -XUndecidableInstances #-}

module Folsolver.Proofer 
 ( Proofer(..), Proof, IsProof(..), mkSATProof
 , witnessSAT, witnessSAT0, getNSATProof, getNSATProof0
 , isTaut, proofTaut
 , axiomsFromInput, conjecturesFromInput
 , check, proof, checkInput, proofInput, (|-), updateF
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
  
  mkProofer :: Picker p -> [TPTP_Input] -> p
  
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

axiomsFromInput, conjecturesFromInput :: [TPTP_Input] -> [TPTP_Input]
axiomsFromInput [] = []
axiomsFromInput (a@(AFormula _ (Role "axiom") f _):xs) = a : axiomsFromInput xs
axiomsFromInput (_:xs) = axiomsFromInput xs
conjecturesFromInput [] = []
conjecturesFromInput (a@(AFormula _ (Role "conjecture") f _):xs) = a : conjecturesFromInput xs
conjecturesFromInput (_:xs) = conjecturesFromInput xs

-- |
-- |
transformInputForTautologieCheck :: [TPTP_Input] -> ([TPTP_Input], [TPTP_Input])
transformInputForTautologieCheck input = 
  let
    axioms = axiomsFromInput input
    conjectures = conjecturesFromInput input
  in (axioms, conjectures)

-- mkProoferInput :: Proofer p => Picker p -> [TPTP_Input] -> p
-- mkProoferInput picker input = mkProofer picker $ transformInput input

-- | checks whether the given set of formulas are a tautologie
isTaut :: Proofer p => Picker p -> [TPTP_Input] -> Bool
isTaut picker formulas = not $ isSAT (mkProofer picker formulas) Set.empty

-- | proofs whether the given set of formulas are a tautologie
proofTaut :: Proofer p => Picker p -> [TPTP_Input] -> Proof p
proofTaut picker formulas = 
  case proofSAT (mkProofer picker formulas) Set.empty of
    NSAT nsatproof -> TAUTOLOGY nsatproof
    SAT witness    -> CONTRADICTION witness
    
-- | syncatic models operator
(|-) :: [TPTP_Input] -> [TPTP_Input] -> ([TPTP_Input], [TPTP_Input])
axioms |- conjectures = (axioms, conjectures)

-- | checks if a given tptp input is a tautologie
-- | thus if axioms |- conjectures
checkInput :: Proofer p => Picker p -> [TPTP_Input] -> Bool
checkInput picker input = check picker $ transformInputForTautologieCheck input

-- | proofs whether a given tptp input is a tautologie
-- | thus if axioms |- conjectures
proofInput :: Proofer p => Picker p -> [TPTP_Input] -> Proof p
proofInput picker input = proof picker $ transformInputForTautologieCheck input

-- | usage: check picker $ axioms |- conjectures
check :: Proofer p => Picker p -> ([TPTP_Input], [TPTP_Input]) -> Bool
check picker (axioms, conjectures) = isTaut picker (axioms ++ (Prelude.map negateConjecture conjectures))

updateF :: (Formula -> Formula) -> TPTP_Input -> TPTP_Input
updateF form (AFormula name role f ann)  = (AFormula name role (form f) ann)
updateF _ x                              = x

-- | usage: proof picker $ axioms |- conjectures
proof :: Proofer p => Picker p -> ([TPTP_Input], [TPTP_Input]) -> Proof p
proof picker (axioms, conjectures) = proofTaut picker (axioms ++ (Prelude.map negateConjecture conjectures))

negateConjecture :: TPTP_Input -> TPTP_Input
negateConjecture (AFormula n@(AtomicWord name) role f _) = 
    (AFormula (AtomicWord $ "not_"++name) (Role "Theorem") (noDoubleNeg ((.~.) f)) (Annotations (GTerm (GApp (AtomicWord "negConjunction") [GTerm (GWord n)])) NoUsefulInfo))
