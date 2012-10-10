{-# OPTIONS_GHC -XTypeSynonymInstances -XFlexibleInstances #-}

module Folsolver.Normalform.Unification
    ( unifyFormula
    , unifyTerm
    , unifyEquals
    , variableRename
    , removeVarOccurance
    ) where

import Codec.TPTP
import Data.Map (Map)
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S

import Data.Maybe

import Data.Functor.Identity

import Control.Monad

unifyFormula 
    :: Maybe (Map V Term)   -- Yet assigned Parameters
    -> Formula              -- Formula one to unify
    -> Formula              -- Formula two to unify
    -> Maybe (Map V Term)   -- Map of substituitions, Nothing if not unifyable
unifyFormula Nothing _ _    = Nothing
unifyFormula m'@(Just m) f1 f2 = case (unwrapF f1, unwrapF f2) of
    (InfixPred t11 op1 t12, InfixPred t21 op2 t22)
        -> if op1 == op2 then unifyTerm (unifyTerm m' t11 t21) t12 t22 else Nothing
    (PredApp fun1 args1, PredApp fun2 args2)
        -> if fun1 == fun2 && (length args1) == (length args2) then foldl (\m (a,b) -> unifyTerm m a b) m' $ zip args1 args2 else Nothing
    (BinOp f11 op1 f12, BinOp f21 op2 f22)   
        -> if op1 == op2 then unifyFormula (unifyFormula m' f11 f21) f12 f22 else Nothing
    (Quant _ _ _, Quant _ _ _)
        -> Nothing          -- We do not unify Quantified Formulas
    ((:~:) f11, (:~:) f22)
        -> unifyFormula m' f11 f22
    _  -> Nothing          -- If the types do not match

wrapT :: Term0 (T Identity) -> Term
wrapT x = T $ Identity x

wrapF :: Formula0 (T Identity) (F Identity) -> Formula
wrapF x = F $ Identity x

unifyTerm
    :: Maybe (Map V Term)   -- Yet assigned Parameters
    -> Term                 -- Term one to unify
    -> Term                 -- Term two to unify
    -> Maybe (Map V Term)   -- Map of substituitions, possible empty
unifyTerm Nothing _ _
    = Nothing
unifyTerm m'@(Just m) a b   = case (unwrapT a, unwrapT b) of
    (Var v1, Var v2)            -> case (M.lookup v1 m, M.lookup v2 m) of
        (Nothing, Nothing)  -> Just (M.insert v1 b m)
        (Just t1, Nothing)  -> if containsT v2 t1 then Nothing else Just (M.insert v2 t1 m)
        (Nothing, Just t2)  -> if containsT v1 t2 then Nothing else Just (M.insert v1 t2 m)
        (Just t1, Just t2)  -> unifyTerm m' t1 t2
    (Var v1, NumberLitTerm t)   -> case M.lookup v1 m of
        Nothing             -> Just (M.insert v1 b m)
        (Just t2)           -> if t2 == b then m' else unifyTerm m' t2 b
    (Var v1, FunApp fun args)   -> case M.lookup v1 m of
        Nothing             -> if containsT v1 b then Nothing else Just (M.insert v1 b m)
        (Just t1)           -> unifyTerm m' t1 b
    (NumberLitTerm t, Var v1)   -> unifyTerm m' b a
    (FunApp fun args, Var v1)   -> unifyTerm m' b a
    (NumberLitTerm t1, NumberLitTerm t2)
                            -> if t1 == t2 then m' else Nothing
    (FunApp fun1 args1, FunApp fun2 args2)
                            -> if fun1 /= fun2 then Nothing else foldl (\m (a,b) -> unifyTerm m a b) m' $ zip args1 args2
    _                   -> Nothing

containsT :: V -> Term -> Bool
containsT x t   = case unwrapT t of
    (Var v)                 -> x == v
    (NumberLitTerm _)       -> False
    (DistinctObjectTerm _)  -> False
    (FunApp _ args)         -> or $ map (containsT x) args

unifyEquals :: Map V Term -> Formula -> Formula -> (Bool, Map V Term)
unifyEquals m a b 
    | isJust newMap     = (True, fromJust newMap)
    | otherwise         = (False, m)
    where
        newMap = unifyFormula (Just m) a b

variableRename 
    :: V            -- Ersetzte diese Variable
    -> Term         -- Durch diesen Term
    -> Formula      -- in dieser Formel
    -> Formula
variableRename x y f    = case unwrapF f of
    (BinOp f1 op f2)        -> wrapF $ BinOp (variableRename x y f1) op (variableRename x y f2)
    (Quant q v f0)          -> if elem x v then f else wrapF $ Quant q v (variableRename x y f0)
    (InfixPred t1 op t2)    -> wrapF $ InfixPred (variableRenameT x y t1) op (variableRenameT x y t2)
    (PredApp fun args)      -> wrapF $ PredApp fun (map (variableRenameT x y) args)
    (:~:) f0                -> (.~.) (variableRename x y f0)

variableRenameT :: V -> Term -> Term -> Term
variableRenameT x y t   = case unwrapT t of
    Var v               -> if x == v then y else wrapT (Var v)
    FunApp fun args     -> wrapT $ FunApp fun (map (variableRenameT x y) args)
    _                   -> t

-- | removes all substitutions where one of the variables occur
-- | (in the left or in the right part of the substitution)
removeVarOccurance :: [V] -> (Map V Term) -> (Map V Term)
removeVarOccurance vars subst = 
  let
    varsSet = S.fromList vars
    subst0 = foldr M.delete subst vars
  in
    M.filter (\ term -> not $ occurs varsSet term) subst0

-- | occures vars term is true iff one variable in vars
-- | is in the term
occurs :: Set V -> Term -> Bool
occurs vars term = not $ S.null $ S.intersection (variables term) vars

-- all structures which has variables
class HasVar a where
  -- variables of such a structure
  variables :: a -> Set V
  
instance HasVar Term where
  variables t = case unwrapT t of
    Var v              -> S.singleton v
    FunApp fname terms -> S.unions $ map variables terms -- function
    _                  -> S.empty

instance HasVar Formula where
  variables formulas = 
    let 
      terms = S.toList $ termsOfFormula formulas
    in 
      S.unions $ map variables terms
      
instance (HasVar a) => (HasVar [a]) where
  variables as = S.unions $ map variables as
  
-- | get terms
termsOfFormula :: Formula -> Set Term
termsOfFormula formulas =
  let
    folder :: Formula -> Set Term
    folder = foldF 
      (\f0 -> folder f0)                               -- handle negation
      (\_ _ f0 -> folder f0)                           -- handle quantification
      (\f0 _ f1 -> S.union (folder f0) (folder f1))  -- handle bin op
      (\t0 _ t1 -> S.fromList [t0, t1])              -- handle equality/inequality
      (\_ ts -> S.fromList ts)                       -- handle predicates
  in folder formulas