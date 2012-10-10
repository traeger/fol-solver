{-# OPTIONS_GHC -XTypeSynonymInstances -XMultiParamTypeClasses -XFlexibleInstances -XTypeFamilies #-}

module Folsolver.FOTableau
 ( tableauFO, checkFOTableau, proofSATFOTableau, Proofer(..), simplePickFO
 , checkFOT, proofFOT) where

import Codec.TPTP
import Folsolver.Normalform
import Folsolver.Data.FOTableau
import Folsolver.TPTP
import Folsolver.Proofer
import Folsolver.Data.TPTP_Gen

import Data.Set (Set) 
import qualified Data.Set as S
import Data.Map (Map)
import qualified Data.Map as M
import Data.Maybe (fromJust, fromMaybe)
import Data.List (nub)

import Data.Functor.Identity

import Text.PrettyPrint.HughesPJ as Pretty

type FOForm = (TPTP_Input,[V])

maxNodeLength :: Int
maxNodeLength = 20

fofformula :: FOForm -> TPTP_Input
fofformula (x,_)       = x

freeVariables :: FOForm -> [V]
freeVariables (_,v) = v

simplePickFO 
    :: [FOForm]                 -- Aufzulösende Formeln 
    -> [FOForm]                 -- Quantifizierte Formeln
    -> (FOForm, [FOForm], [FOForm])
simplePickFO [] (f:fs)  = (f,[],fs)
simplePickFO (f:fs) xs  = (f,fs,xs)

tableauFO
  :: ([FOForm] -> [FOForm] -> (FOForm, [FOForm], [FOForm]))  -- pick function fuer die naechste formula
  -> [TPTP_Input]  -- noch zu nutztende formulas
  -> FOTableau
tableauFO pick formulas = tableau0 (pick) emptyWalk 1 simple compl (leaf formulas)
    where
        (simple,compl) = initFormulas formulas
        initFormulas :: [TPTP_Input] -> ([FOForm],[FOForm])
        initFormulas xs = (map (\x -> (x,[])) $ filter (isAlphaFormula . formula) xs ++ filter (\x -> (isSimple . formula) x && (not (isAlphaFormula $ formula  x))) xs, map (\x -> (x,[])) $ filter (isQuant . formula) xs)

type WalkDir    = ([Bool],[Bool],Map TPTP_Input Bool)
changeDir :: TPTP_Input -> WalkDir -> WalkDir
changeDir f (x,y,m)
    | M.member f m  = let b = (fromJust $ M.lookup f m) in (x, b:y, M.insert f (not b) m)
    | otherwise     = (x, True:y, M.insert f True m)
getDir :: WalkDir -> (Bool, WalkDir)
getDir ([],[],m)        = (True,([],[],m))
getDir ([],ys,m)        = let (x:xs) = reverse ys in (x,(xs,[],m))
getDir ((x:xs),ys,m)    = (x,(xs,ys,m))
emptyWalk :: WalkDir
emptyWalk = ([],[],M.empty)

tableau0
  :: ([FOForm] -> [FOForm] -> (FOForm, [FOForm],[FOForm]))  -- pick function fuer die naechste formula
  -> WalkDir
  -> Integer        -- Position in the tree
  -> [FOForm]  -- noch nicht genutzten formulas
  -> [FOForm]  -- quantifizierte formulas
  -> FOTableau    -- kurzzeitiges Tableau (brauchen wir fuer mehrere alpha schritte)
  -> FOTableau
tableau0 pick w pos [] [] t           = t
tableau0 pick w pos formulas quans t    = 
  let
    nameFun p q = "genFunction_"++(show p)++"_"++(show q)
    ((f,v),fs,qs) = pick formulas quans
  in case reduction $ formula f of
    AlphaR a1 a2 
        -> 
            let
                at1 = mkTPTP (nameFun pos $ (length $ value t)) "plain" a1 [("alpha1",[show.name $ f])]
                at2 = mkTPTP (nameFun pos $ (length $ value t)+1) "plain" a2 [("alpha2",[show.name $ f])]
            in
                if (length $ value t) > maxNodeLength
                then
                    tableau0 pick w pos (fs++[(at1,v),(at2,v)]) qs (leaf $ value t ++ [at1, at2])
                else
                    value t <|> tableau0 pick w (2*pos) (fs++[(at1,v),(at2,v)]) qs (leaf [at1,at2]) 
    BetaR b1 b2  
        -> 
            let
                (dir,newWalk)   = getDir w
                bt1 = mkTPTP (nameFun (pos * 2) 1) "plain" b1 [("beta1",[show.name $ f])]
                bt2 = mkTPTP (nameFun ((2*pos)+1) 1) "plain" b2 [("beta2",[show.name $ f])]
                t1 = tableau0 pick newWalk (2*pos) (fs++[(bt1,v)]) qs (leaf [bt1])
                t2 = tableau0 pick newWalk (2*pos + 1) (fs++[(bt2,v)]) qs (leaf [bt2])
            in
                if dir then t1  <# value t #> t2 else t2 <# value t #> t1
    DNegate n   
        ->
            let
                f1 = mkTPTP (nameFun pos $ (length $ value t)) "plain" n [("negate",[show.name $ f])]
            in
                if (length $ value t) > maxNodeLength
                then
                    tableau0 pick w pos (fs++[(f1,v)]) qs (leaf $ value t ++ [f1])                    -- handle double negate
                else
                    value t <|> tableau0 pick w (2*pos) (fs++[(f1,v)]) qs (leaf [f1])
    AtomR _     
        -> tableau0 pick w pos fs qs t
    GammaR form var
        ->
            let
                newDir      = changeDir f w
                (AtomicWord oldName)    = name f
                newFunName  = "genFunction_"++show pos++"_"++(show $ length $ value t)
                varName     = V $ "FreeVar_"++show pos++"_"++(show $ length $ value t)
                rename      = variableRename var (T $ Identity $ Var varName) form
                next        = mkTPTP newFunName "plain" rename [("gamma",[oldName])]
            in 
                if (length $ value t) > maxNodeLength
                then
                    tableau0 pick newDir pos (fs++[(next,varName:v)]) (qs++[(f,v)]) t
                else
                    value t <|> tableau0 pick newDir (2*pos) (fs++[(next,varName:v)]) (qs++[(f,v)]) (leaf [next])
    DeltaR form var 
        -> 
            let
                (AtomicWord oldName)    = name f
                newFunName  = "genFunction_"++show pos++"_"++(show $ length $ value t)
                skolName    = AtomicWord $ "skolFun_"++show pos++"_"++(show $ length $ value t)
                skolFun     = T $ Identity $ FunApp skolName (map (\x -> (T $ Identity $ Var x)) v)
                rename      = variableRename var skolFun form
                next        = mkTPTP newFunName "plain" rename [("delta",[oldName])]
            in
                if (length $ value t) > maxNodeLength
                then
                    tableau0 pick w pos (fs++[(next,v)]) qs t
                else
                    value t <|> tableau0 pick w (2*pos) (fs++[(next,v)]) qs (leaf [next])
  --  _   -> tableau0 pick pos fs qs t

type Sub5t1tut0r = Map V Term

{-
 - | This function iterates over the tableau and checks
 - | whether the negate of a new formula already occured.
 - | If this is the case, it will step back with true.
 - | If we reach the bottom we will step back with false.
 -}
checkFOTableau 
    :: 
    FOTableau             -- Current branch of the tableau
    -> Set Formula      -- Formulas seen so far
    -> Sub5t1tut0r
    -> (Bool,Sub5t1tut0r)             
checkFOTableau (BinEmpty) _ m  = (False, m)
checkFOTableau (SNode t v) forms m =
    let
        (cond, nForms, m')  = isClosed (map formula v) m forms
    in
        if cond
        then
            (True, m')
        else
            (checkFOTableau t nForms m)
checkFOTableau t forms m       = 
    let
        (cond, nForms, m')      = isClosed (map formula $ value t) m forms
        (closed1, m1)           = checkFOTableau (left t) nForms m'
        (closed2, m2)           = checkFOTableau (right t) nForms m1
    in
        if cond
        then
            (True,m')
        else if closed1 && closed2
        then
            (True,m2)
        else
            (False, M.empty)

isClosed :: [Formula] -> Sub5t1tut0r -> Set Formula -> (Bool, Set Formula, Sub5t1tut0r)
isClosed [] m forms                             = (False, forms, m)
isClosed (x:xs) m forms
    | isTrue x                                  = isClosed xs m forms
    | isFalse x                                 = (True, forms, m)
    | S.member (noDoubleNeg ((.~.) x)) forms    = (True, forms, m)
    | not $ null $ filter fst ergs              = (True, forms, snd $ head $ ergs)
    | otherwise                                 = isClosed xs m (S.insert x forms)
    where
        ergs = map (unifyEquals m (noDoubleNeg ((.~.) x))) (S.toList forms)
            
proofSATFOTableau 
    :: 
    FOTableau             -- Current branch of the tableau
    -> Sub5t1tut0r
    -> Set TPTP_Input      -- Formulas seen so far
    -> (Proof FOTableau , Sub5t1tut0r)
proofSATFOTableau (BinEmpty) m forms = (mkSATProof $ nub $ filter isLiteral $ (map formula) $ S.toList $ forms , m)
proofSATFOTableau (SNode t v) m forms
    | closed                =
        let
            witTPTP     = fromJust witness
            tillWit     = takeWhile ((/=) $ fromJust witness) $ v
            (AtomicWord errName)   = name $ fromJust errCase
            (AtomicWord fName) = name witTPTP
            wName       = drop 12 fName
            contForm    = (formula witTPTP) .&. (formula $ fromJust errCase)
            contradict = mkTPTP ("contradict_"++wName) "plain" contForm [("contradiction_of",[fName, errName])]
        in
            (mkNSATProof $ leaf $ tillWit ++ [witTPTP,contradict], m')
    | isSATProof subTree    = (subTree, m'')
    | otherwise             = (mkNSATProof $ v <|> subPTree, m'')
    where
        (closed,nForms,witness, errCase, m')    = isClosedWithWitness v m forms
        (subTree,m'')                           = proofSATFOTableau t m nForms
        subPTree                                = fromNSATProofT subTree
proofSATFOTableau t m forms
    | closed                = 
        let
            witTPTP     = fromJust witness
            tillWit     = takeWhile ((/=) $ fromJust witness) $ value t
            (AtomicWord errName)   = name $ fromJust errCase
            (AtomicWord fName) = name witTPTP
            wName       = drop 12 fName
            contForm    = (formula witTPTP) .&. (formula $ fromJust errCase)
            contradict = mkTPTP ("contradict_"++wName) "plain" contForm [("contradiction_of",[fName, errName])]
        in
            (mkNSATProof $ leaf $ tillWit ++ [witTPTP,contradict],m')
    | isSATProof proofLeft  = (proofLeft,m'')
    | isSATProof proofRight = (proofRight,m''')
    | otherwise             = (mkNSATProof $ leftPTree <# value t #> rightPTree, m''')
    where
        (closed, nForms, witness, errCase, m')  = isClosedWithWitness (value t) m forms
        (proofLeft,m'')      = proofSATFOTableau (left t) m' nForms
        (proofRight, m''')   = proofSATFOTableau (right t) m'' nForms
        (leftPTree)  = fromNSATProofT proofLeft
        (rightPTree) = fromNSATProofT proofRight

isClosedWithWitness :: [TPTP_Input] -> Sub5t1tut0r -> Set TPTP_Input -> (Bool, Set TPTP_Input, Maybe TPTP_Input, Maybe TPTP_Input, Sub5t1tut0r)
isClosedWithWitness [] m forms             = (False, forms, Nothing, Nothing, m)
isClosedWithWitness (x:xs) m forms
    | isTrue (formula x)                            = isClosedWithWitness xs m forms
    | isFalse (formula x)                           = (True, forms, Just x, Just x, m)
    | not $ null directErgs                         = (True, forms, Just x, Just $ head directErgs, m)
    | not $ null $ unifyErgs                        = (True, forms, Just x, Just $ snd $ head unifyErgs, snd $ fst $ head $ unifyErgs)
    | otherwise                                     = isClosedWithWitness xs m (S.insert x forms)
    where
        negF        = noDoubleNeg ((.~.) (formula x))
        directErgs = filter (((==) negF ) . formula) (S.toList forms)
        unifyErgs = filter (fst . fst) $  map (\x -> (unifyEquals m negF (formula x), x)) (S.toList forms)
 
instance Proofer FOTableau where
  data NSATProof FOTableau = NSAT {fromNSATproofT :: FOTableau} deriving Show
  data Picker FOTableau = Picker {pick :: [FOForm] -> [FOForm] -> (FOForm, [FOForm],[FOForm])}
  mkProofer (Picker picker) formulas = tableauFO picker formulas
  
  isSAT tableau = not $ fst $ checkFOTableau tableau S.empty M.empty
  proofSAT t = fst $ proofSATFOTableau t M.empty S.empty

mkNSATProof = mkProof . NSAT
fromNSATProofT = fromNSATproofT . getNSATProof0

instance HasPretty (NSATProof FOTableau) where
  pretty (NSAT nsatproof) = Pretty.text "  [ tableau proof ]" $$ pretty nsatproof

-- | shorthands to use a tableau proofer
proofFOT = proof (Picker simplePickFO)
checkFOT = check (Picker simplePickFO)
