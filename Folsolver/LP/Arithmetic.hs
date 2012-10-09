{-# OPTIONS_GHC -XOverloadedStrings -XTypeSynonymInstances -XFlexibleInstances #-}

module Folsolver.LP.Arithmetic where
 
import Codec.TPTP
import Data.Functor.Identity
import Folsolver.TPTP

import qualified Data.Set as Set
import Data.Set (Set)

wrapT :: Term0 (T Identity) -> Term
wrapT t = T $ Identity t

-- terms
(.+),(.-),(.*),(./) :: Term -> Term -> Term
f1 .+ f2 = wrapT $ FunApp namePlus  [f1,f2]
f1 .- f2 = wrapT $ FunApp nameMinus [f1,f2]
f1 .* f2 = wrapT $ FunApp nameMult  [f1,f2]
f1 ./ f2 = wrapT $ FunApp nameDiv   [f1,f2]

namePlus, nameMinus, nameMult, nameDiv :: AtomicWord
namePlus  = "$sum"
nameMinus = "$minus"
nameMult  = "$mult"
nameDiv   = "$div"

isPlus, isMinus, isMult, isDiv :: Term -> Bool
isPlus  = hasFunName namePlus
isMinus = hasFunName nameMinus
isMult  = hasFunName nameMult
isDiv   = hasFunName nameDiv

arithmeticOpNames = [namePlus, nameMinus, nameMult, nameDiv]

hasFunName :: AtomicWord -> Term -> Bool
hasFunName name t = case unwrapT t of
  FunApp op _ -> op == name

-- realations
(.=>),(.<=),(.>),(.<),(.=),(./=) :: Term -> Term -> Formula
t1 .> t2  = wrapF $ PredApp nameGreater [t1,t2]
t1 .< t2  = wrapF $ PredApp nameLesser [t1,t2]
t1 .=> t2 = wrapF $ PredApp nameGreaterEq [t1,t2]
t1 .<= t2 = wrapF $ PredApp nameLesserEq [t1,t2]
t1 .=  t2 = wrapF $ InfixPred t1 (:=:) t2
t1 ./= t2 = wrapF $ InfixPred t1 (:!=:) t2

nameLesser, nameGreater, nameLesserEq, nameGreaterEq :: AtomicWord
nameLesser = "$lesser"
nameGreater = "$greater"
nameLesserEq = "$lessereq"
nameGreaterEq = "$greatereq"

isLesser, isGreater, isLesserEq, isGreaterEq, isEq, isNeq :: Formula -> Bool
isLesser f = case unwrapF f of
  PredApp name _ -> name == nameLesser
  _              -> False
isGreater f = case unwrapF f of
  PredApp name _ -> name == nameGreater
  _              -> False
isLesserEq f = case unwrapF f of
  PredApp name _ -> name == nameLesserEq
  _              -> False
isGreaterEq f = case unwrapF f of
  PredApp name _ -> name == nameGreaterEq
  _              -> False
isEq f = case unwrapF f of
  InfixPred _ (:=:) _ -> True
  _                   -> False
isNeq f = case unwrapF f of
  InfixPred _ (:!=:) _ -> True
  _                    -> False

relationOpNames = [nameLesserEq, nameGreaterEq]
relationOpNamesNeg = [nameLesser, nameGreater]

-- whether a formula is arithmetic
isArithmetic :: Formula -> Bool
isArithmetic = isArithmeticFormula

-- whether a formula is arithmetic
isArithmeticFormula :: Formula -> Bool
isArithmeticFormula = isArithmeticFormula0 False

isArithmeticFormula0 
  :: Bool      -- whether to negate the formula
  -> Formula   -- formula to check
  -> Bool
isArithmeticFormula0 neg f = case unwrapF f of
  (:~:) f0               -> isArithmeticFormula0 (not neg) f0
  InfixPred t1 (:=:) t2  -> not neg && (isArithmeticTerm t1) && (isArithmeticTerm t2)
  InfixPred t1 (:!=:) t2 -> neg && (isArithmeticTerm t1) && (isArithmeticTerm t2)
  PredApp op [t1,t2]
    | not neg   -> (elem op relationOpNames) && (isArithmeticTerm t1) && (isArithmeticTerm t2)
    | otherwise -> (elem op relationOpNamesNeg) && (isArithmeticTerm t1) && (isArithmeticTerm t2)
  _                      -> False

-- whether a term is arithmetic
isArithmeticTerm :: Term -> Bool
isArithmeticTerm t = case unwrapT t of
  Var v             -> True
  NumberLitTerm r   -> True
  FunApp op [t1,t2] -> 
       (elem op arithmeticOpNames)
    && (isArithmeticTerm t1)
    && (isArithmeticTerm t2)
  _                 -> False

-- all structures which has variables
class HasVar a where
  -- variables of such a structure
  variables :: a -> Set V
  
instance HasVar Term where
  variables t = case unwrapT t of
    Var v              -> Set.singleton v
    FunApp fname terms -> Set.unions $ map variables terms -- function
    _                  -> Set.empty

instance HasVar Formula where
  variables formulas = 
    let 
      terms = Set.toList $ termsOfFormula formulas
    in 
      Set.unions $ map variables terms
      
instance (HasVar a) => (HasVar [a]) where
  variables as = Set.unions $ map variables as
  
-- | get terms
termsOfFormula :: Formula -> Set Term
termsOfFormula formulas =
  let
    folder :: Formula -> Set Term
    folder = foldF 
      (\f0 -> folder f0)                               -- handle negation
      (\_ _ f0 -> folder f0)                           -- handle quantification
      (\f0 _ f1 -> Set.union (folder f0) (folder f1))  -- handle bin op
      (\t0 _ t1 -> Set.fromList [t0, t1])              -- handle equality/inequality
      (\_ ts -> Set.fromList ts)                       -- handle predicates
  in folder formulas