{-# OPTIONS_GHC -XOverloadedStrings #-}

module Folsolver.LP.Arithmetic
 ( isArithmetic, isArithmeticFormula, isArithmeticTerm
 ) where
 
import Codec.TPTP

isArithmetic :: Formula -> Bool
isArithmetic = isArithmeticFormula

isArithmeticFormula :: Formula -> Bool
isArithmeticFormula = isArithmeticFormula0 False

isArithmeticFormula0 
  :: Bool      -- whether to negate the formula
  -> Formula   -- formula to check
  -> Bool
isArithmeticFormula0 neg f = case unwrap f of
  (:~:) f0               -> isArithmeticFormula (not neg) f0
  InfixPred t1 (:=:) t2  -> not neg && (isArithmeticTerm t1) && (isArithmeticTerm t2)
  InfixPred t1 (:!=:) t2 -> neg && (isArithmeticTerm t1) && (isArithmeticTerm t2)
  PredApp op [t1,t2] -> 
       (member op ["=>","<="])
    && (isArithmeticTerm t1)
    && (isArithmeticTerm t2)
  _                      -> False

isArithmeticTerm :: Term -> Bool
isArithmeticTerm t = case unwrapT t of
  Var v             -> True
  NumberLitTerm r   -> True
  FunApp op [t1,t2] -> 
       (member op ["+","-","*","/"])
    && (isArithmeticTerm t1)
    && (isArithmeticTerm t2)
  _                 -> False