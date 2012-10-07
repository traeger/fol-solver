module Folsolver.LP.LPSolver
 (
 ) where
 
import Codec.TPTP
import Data.Set as Set
import Data.Map as Map
import Data.Bimap as Bimap

variables :: Term -> Set Var
variables t = case t of
  Var v              -> Set.singleton v
  FunApp fname terms -> Set.unions $ map variables terms
  _                  -> Set.empty
  
-- | get terms
termsOfFormula :: Formula -> Set Term
termsOfFormula formulas =
  let
    folder = foldF 
      id                                               -- handle negation
      (\_ _ f0 -> folder f0)                           -- handle quantification
      (\f0 _ f1 -> Set.union (folder f0) (folder f1))  -- handle bin op
      (\t0 _ t1 -> Set.fromList [t0, t1])              -- handle equality/inequality
      (\_ ts -> Set.fromList ts)                       -- handle predicates
  in folder formulas

type VarMap = BiMap Var Int
type Error = String

-- | create a map of all variables in a list of terms
-- | to an integer which identifies the variable (and visa versa).
buildVarMap :: [Term] -> VarMap
buildVarMap formulas = 
  let
    varset = Set.unions $ map variables term
    vars = Set.toList $ varset
  in 
    Map.fromList $ take (length vars) $ zip vars [1..]
    
-- | converts a list of formula to a lp-constraints
toLPConstraints :: [Formula] -> Either Error Constraints
toLPConstraints formulas = 
  let
    terms = Set.unions $ map termsOfFormula formulas
    varmap = buildVarMap terms
  in case catchLeft (map (formulaToBounds varmap) formulas) of
    Left err     -> Left err
    Right bounds -> Right $ Sparse bounds
    
-- maps to the Right component
-- returns the first Left if one is found
catchLeft :: [Either b a] -> Either b [a]
catchLeft [] = []
catchLeft (Left err:_)   = Left err
catchLeft (Right e:xs) = case catchLeft xs of
  Left  err -> Left err
  Right es  -> Right $ e:es

-- | converts a formula to a lp bound
formulaToBounds :: VarMap -> Formula -> Either Error Bound
formulaToBounds varmap f = case unwrap f of
  InfixPred t1 (:=:) t2 -> case (buildTermCoeffMap t1, buildTermCoeffMap t2) of
    (Left err, _)          -> Left err
    (_, Left err)          -> Left err
    (Right t10, Right t20) -> Right $ buildFormulaBound varmap "=" t10 t20
  PredApp op [t1,t2]    -> case (buildTermCoeffMap t1, buildTermCoeffMap t2) of
    (Left err, _)          -> Left err
    (_, Left err)          -> Left err
    (Right t10, Right t20) -> Right $ buildFormulaBound varmap op t10 t20
  _                     -> Left "formulaToBounds"

-- |
-- |
-- | building of coeffience maps and lp bounds
constTerm = V ""
type CoeffMap = (Map V Rational)

buildFormulaBound :: VarMap -> String -> CoeffMap -> CoeffMap -> Bound
buildFormulaBound varmap "=" c1 c2 =
  let 
    coeffMap = Map.unionWith (+) (c1) (Map.map (-1 *) $ c2)
    b   = fromMaybe 0 $ lookup constTerm coeffMap
    as  = Map.toList $ delete constTerm coeffMap
    as0 = map (first (\v -> fromJust $ Map.lookup v varmap)) as
    as1 = map (\(x,y) -> (y,x)) as0
  in
    as1 :==: b
buildFormulaBound varmap "<=" c1 c2 =
  let 
    coeffMap = Map.unionWith (+) (Map.map (-1 *) $ c1) (c2)
    b   = fromMaybe 0 $ lookup constTerm coeffMap
    as  = Map.toList $ delete constTerm coeffMap
    as0 = map (first (\v -> fromJust $ Map.lookup v varmap)) as
    as1 = map (\(x,y) -> (y,x)) as0
  in
    as1 :<=: b
buildFormulaBound varmap ">=" c1 c2 = buildFormulaBound varmap "<=" c2 c1
buildFormulaBound _ _ _ _ = error "buildFormulaBound"

-- build a coefficient map where
-- each variable is mapped to it's coefficant
buildTermCoeffMap :: Term -> Either Error CoeffMap
buildTermCoeffMap t = case unwrap t of
  Var v             -> Right $ Map.singleton v 1
  NumberLitTerm r   -> Right $ Map.singleton constTerm r
  FunApp op [t1,t2] -> case (buildTermCoeffMap t1, buildTermCoeffMap t2) of
    (Left err, _)          -> Left err
    (_, Left err)          -> Left err
    (Right t10, Right t20) -> joinTermCoeffMaps op t10 t20
    _                      -> Left $ show t ++ " not supported"

joinCoeffMaps :: AtomicWord -> CoeffMap -> CoeffMap -> Either Error CoeffMap
joinCoeffMaps "+" t1 t2 = Right $ Map.unionWith (+) t1 t2
joinCoeffMaps "-" t1 t2 = Right $ Map.unionWith (+) t1 (Map.map (-1 *) t2)
joinCoeffMaps "*" t1 t2 = if containsVar t1 && containsVar t2
  then Left "only linear constraints are supported"
  else Right $ Map.unionWith (*) t1 t2
joinCoeffMaps "/" t1 t2 = if containsVar t1 && containsVar t2
  then Left "only linear constraints are supported"
  else Right $ Map.unionWith (*) t1 (Map.map (1.0 /) t2)

-- whether a variable coefficient map contains a variable
containsVar :: CoeffMap
containsVar m = if (member constTerm) then size m >= 2 else size m >= 1