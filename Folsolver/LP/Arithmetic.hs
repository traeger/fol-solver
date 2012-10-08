{-# OPTIONS_GHC -XOverloadedStrings #-}

module Folsolver.LP.Arithmetic
 ( isArithmetic, isArithmeticFormula, isArithmeticTerm
 ) where
 
import Codec.TPTP
import Data.Functor.Identity
import Folsolver.TPTP

wrapT :: Term0 (T Identity) -> Term
wrapT t = T $ Identity t

-- terms
(.+),(.-),(.*),(./) :: Term -> Term -> Term
f1 .+ f2 = wrapT $ FunApp namePlus  [f1,f2]
f1 .- f2 = wrapT $ FunApp nameMinus [f1,f2]
f1 .* f2 = wrapT $ FunApp nameMult  [f1,f2]
f1 ./ f2 = wrapT $ FunApp nameDiv   [f1,f2]

namePlus, nameMinus, nameMult, nameDiv :: AtomicWord
namePlus  = "$plus"
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
(.=>),(.<=),(.=),(./=) :: Term -> Term -> Formula
t1 .=> t2 = wrapF $ PredApp nameGreaterEq [t1,t2]
t1 .<= t2 = wrapF $ PredApp nameLessEq [t1,t2]
t1 .=  t2 = wrapF $ InfixPred t1 (:=:) t2
t1 ./= t2 = wrapF $ InfixPred t1 (:!=:) t2

nameLessEq, nameGreaterEq :: AtomicWord
nameLessEq = "$lesseq"
nameGreaterEq = "$greatereq"

isLessEq, isGreaterEq, isEq, isNeq :: Formula -> Bool
isLessEq f = case unwrapF f of
  PredApp name _ -> name == nameLessEq
isGreaterEq f = case unwrapF f of
  PredApp name _ -> name == nameGreaterEq
isEq f = case unwrapF f of
  InfixPred _ (:=:) _ -> True
  _                   -> False
isNeq f = case unwrapF f of
  InfixPred _ (:!=:) _ -> True
  _                    -> False

relationOpNames = [nameLessEq, nameGreaterEq]

----
isArithmetic :: Formula -> Bool
isArithmetic = isArithmeticFormula

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
  PredApp op [t1,t2] -> 
       (elem op relationOpNames)
    && (isArithmeticTerm t1)
    && (isArithmeticTerm t2)
  _                      -> False

isArithmeticTerm :: Term -> Bool
isArithmeticTerm t = case unwrapT t of
  Var v             -> True
  NumberLitTerm r   -> True
  FunApp op [t1,t2] -> 
       (elem op arithmeticOpNames)
    && (isArithmeticTerm t1)
    && (isArithmeticTerm t2)
  _                 -> False