{-# OPTIONS_GHC -XOverloadedStrings #-}

module Folsolver.LP.LPSolver
 ( module Folsolver.LP.Arithmetic
 , mkVarMap, mkLPBounds, solveS, solve
 , solveWithBounds
 ) where
 
import Codec.TPTP
import Folsolver.TPTP
import Numeric.LinearProgramming as LP
import Folsolver.LP.Arithmetic

import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Bimap as Bimap
import Data.Bimap (Bimap)

import Data.Maybe (fromMaybe, fromJust)
import Control.Arrow

type SparseBound = Bound [(Double, Int)]
type VarMap = Bimap V Int
type Error = String
type CoeffMap = (Map V Rational)
      
-- | create a map of all variables in a list of terms
-- | to an integer which identifies the variable (and visa versa).
mkVarMap :: (HasVar a) => a -> VarMap
mkVarMap a = 
  let
    vars = Set.toList $ variables a
  in 
    Bimap.fromList $ take (length vars) $ zip vars [1..]
    
-- | converts a list of formula to a lp-constraints
mkLPBounds :: [Formula] -> [Either Error SparseBound]
mkLPBounds formulas = 
  let
    varmap = mkVarMap formulas
  in map (formulaToBounds varmap) formulas

-- | splits a list of formulas into a list of lp-bounds which are
-- | the linear system interpretation of thus formulas and a list
-- | of formulas which can't be converted to a lp-bound.
splitLPBounds :: [Formula] -> ([Formula], [SparseBound])
splitLPBounds formulas = first concat $ second concat $ unzip $ map q $ zip formulas (mkLPBounds formulas) where
  q (f, Left _)  = ([f],[])
  q (_, Right b) = ([],[b])
  
-- | solves a lp of bounds
solveWithBounds :: VarMap -> [SparseBound] -> Solution
solveWithBounds varmap bound = simplex (Minimize $ replicate (Bimap.size varmap) 0) (Sparse bound) []

-- | solves a lp of formulas, give the solution to the problem
solveS :: [Formula] -> Solution
solveS formulas = 
  let 
    varmap = mkVarMap formulas
  in case (catchLeft $ mkLPBounds formulas) of
    Left err     -> error err
    Right bounds -> simplex (Minimize $ replicate (Bimap.size varmap) 0) (Sparse bounds) []
    
-- | whether the lp of formulas have a solution
solve :: [Formula] -> Bool
solve formulas = case solveS formulas of
  Undefined    -> error "LP solution is Undefined."
  Feasible _   -> True
  Infeasible _ -> False
  NoFeasible   -> False
  Optimal _    -> True
  Unbounded    -> True

-- | converts a formula to a lp bound
formulaToBounds :: VarMap -> Formula -> Either Error SparseBound
formulaToBounds varmap = formulaToBounds0 varmap False

formulaToBounds0 
  :: VarMap    -- varmap
  -> Bool      -- negate?
  -> Formula   -- formula to convert
  -> Either Error SparseBound
formulaToBounds0 varmap neg f = case unwrapF f of
  (:~:) f0              -> formulaToBounds0 varmap (not neg) f0
  InfixPred t1 op t2 -> case (buildTermCoeffMap t1, buildTermCoeffMap t2) of
    (Left err, _)          -> Left err
    (_, Left err)          -> Left err
    (Right t10, Right t20) -> case op of
      (:=:)   -> buildFormulaBound varmap (if neg then "/=" else "==") t10 t20
      (:!=:)  -> buildFormulaBound varmap (if neg then "==" else "/=") t10 t20
  PredApp op [t1,t2]    -> case (buildTermCoeffMap t1, buildTermCoeffMap t2) of
    (Left err, _)          -> Left err
    (_, Left err)          -> Left err
    (Right t10, Right t20) -> case () of 
      _ | op == nameLessEq     -> buildFormulaBound varmap (if neg then ">=" else "<=") t10 t20
        | op == nameGreaterEq  -> buildFormulaBound varmap (if neg then "<=" else ">=") t10 t20
        | otherwise            -> Left $ "formulaToBounds0: unsupported relation " ++ (show op)
  _                     -> Left "formulaToBounds0"

-- |
-- |
-- | building of coeffience maps and lp bounds
constTerm = V ""

-- | builds a sparse lp bound from two coeffient maps m1, m2 and a relation R
-- | connecting m1 and m2. R is "<=", ">=", "==" or "/="
-- | (helper method)
buildFormulaBound :: VarMap -> String -> CoeffMap -> CoeffMap -> Either Error SparseBound
buildFormulaBound varmap "==" c1 c2 =
  let 
    coeffMap = Map.unionWith (+) (c1) (Map.map negate $ c2)
    b   = fromRational $ fromMaybe 0 $ Map.lookup constTerm coeffMap
    as  = Map.toList $ Map.delete constTerm coeffMap
    as0 = map (first (\v -> fromJust $ Bimap.lookup v varmap)) as
    as1 = map (first fromRational) $ map (\(x,y) -> (y,x)) as0
  in
    Right $ as1 LP.:==: (negate b)  -- we have to negate b, since b is on the right side
                                    -- of the equation
buildFormulaBound varmap "<=" c1 c2 =
  let 
    coeffMap = Map.unionWith (+) (c1) (Map.map negate $ c2)
    b   = fromRational $ fromMaybe 0 $ Map.lookup constTerm coeffMap
    as  = Map.toList $ Map.delete constTerm coeffMap
    as0 = map (first (\v -> fromJust $ Bimap.lookup v varmap)) as
    as1 = map (first fromRational) $ map (\(x,y) -> (y,x)) as0
  in
    Right $ as1 LP.:<=: (negate b)  -- we have to negate b, since b is on the right side
                                    -- of the equation
buildFormulaBound varmap ">=" c1 c2 = buildFormulaBound varmap "<=" c2 c1
buildFormulaBound varmap "/=" c1 c2 = Left "buildFormulaBound: /= is unsupported."
buildFormulaBound _ _ _ _ = Left "buildFormulaBound"

-- | build a coefficient map where
-- | each variable is mapped to it's coefficant
buildTermCoeffMap :: Term -> Either Error CoeffMap
buildTermCoeffMap t = case unwrapT t of
  Var v             -> Right $ Map.singleton v 1
  NumberLitTerm r   -> Right $ Map.singleton constTerm r
  FunApp op [t1,t2] -> case (buildTermCoeffMap t1, buildTermCoeffMap t2) of
    (Left err, _)          -> Left err
    (_, Left err)          -> Left err
    (Right t10, Right t20) -> joinCoeffMaps op t10 t20

-- | join two coeffient maps with a operation
joinCoeffMaps :: AtomicWord -> CoeffMap -> CoeffMap -> Either Error CoeffMap
joinCoeffMaps name t1 t2
  | name == namePlus  = 
    Right $ Map.unionWith (+) t1 t2
  | name == nameMinus = 
    Right $ Map.unionWith (+) t1 (Map.map negate t2)
  | name == nameMult  = 
    if containsVar t1 && containsVar t2
    then Left "only linear constraints are supported"
    else Right $ Map.unionWith (*) t1 t2
  | name == nameDiv   = 
    if containsVar t1 && containsVar t2
    then Left "only linear constraints are supported"
    else Right $ Map.unionWith (*) t1 (Map.map (1.0 /) t2)
                        
-- | whether a variable coefficient map contains a variable
containsVar :: CoeffMap -> Bool
containsVar m = if (Map.member constTerm m) then Map.size m >= 2 else Map.size m >= 1

--
-- helpers
--

-- | maps to the Right component
-- | returns the first Left if one is found
catchLeft :: [Either b a] -> Either b [a]
catchLeft [] = Right []
catchLeft (Left err:_)   = Left err
catchLeft (Right e:xs) = case catchLeft xs of
  Left  err -> Left err
  Right es  -> Right $ e:es