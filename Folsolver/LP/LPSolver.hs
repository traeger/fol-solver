{-# OPTIONS_GHC -XOverloadedStrings #-}

module Folsolver.LP.LPSolver where
 
import Codec.TPTP
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

variables :: Term -> Set V
variables t = case unwrapT t of
  Var v              -> Set.singleton v
  FunApp fname terms -> Set.unions $ map variables terms
  _                  -> Set.empty
  
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

-- | create a map of all variables in a list of terms
-- | to an integer which identifies the variable (and visa versa).
buildVarMap :: [Term] -> VarMap
buildVarMap terms = 
  let
    varset = Set.unions $ map variables terms
    vars = Set.toList $ varset
  in 
    Bimap.fromList $ take (length vars) $ zip vars [1..]
    
-- | converts a list of formula to a lp-constraints
toLPBounds :: [Formula] -> [Either Error SparseBound]
toLPBounds formulas = 
  let
    terms = Set.unions $ map termsOfFormula formulas
    varmap = buildVarMap (Set.toList terms)
  in map (formulaToBounds varmap) formulas

-- | splits a list of formulas into a list of lp-bounds which are
-- | the linear system interpretation of thus formulas and a list
-- | of formulas which can't be converted to a lp-bound.
splitLPBounds :: [Formula] -> ([Formula], [SparseBound])
splitLPBounds formulas = first concat $ second concat $ unzip $ map q $ zip formulas (toLPBounds formulas) where
  q (f, Left _)  = ([f],[])
  q (_, Right b) = ([],[b])

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
    (Right t10, Right t20) -> case op of
      (nameLessEq)     -> buildFormulaBound varmap (if neg then ">=" else "<=") t10 t20
      (nameGreaterEq)  -> buildFormulaBound varmap (if neg then "<=" else ">=") t10 t20
      _                -> Left $ "formulaToBounds0: unsupported relation " ++ (show op)
      
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
    Right $ as1 LP.:==: b
buildFormulaBound varmap "<=" c1 c2 =
  let 
    coeffMap = Map.unionWith (+) (c1) (Map.map negate $ c2)
    b   = fromRational $ fromMaybe 0 $ Map.lookup constTerm coeffMap
    as  = Map.toList $ Map.delete constTerm coeffMap
    as0 = map (first (\v -> fromJust $ Bimap.lookup v varmap)) as
    as1 = map (first fromRational) $ map (\(x,y) -> (y,x)) as0
  in
    Right $ as1 LP.:<=: b
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
joinCoeffMaps namePlus t1 t2  = Right $ Map.unionWith (+) t1 t2
joinCoeffMaps nameMinus t1 t2 = Right $ Map.unionWith (+) t1 (Map.map negate t2)
joinCoeffMaps nameMult t1 t2  = if containsVar t1 && containsVar t2
  then Left "only linear constraints are supported"
  else Right $ Map.unionWith (*) t1 t2
joinCoeffMaps nameDiv t1 t2   = if containsVar t1 && containsVar t2
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