{-# OPTIONS_GHC -XTypeSynonymInstances -XMultiParamTypeClasses -XFlexibleInstances -XTypeFamilies #-}

module Folsolver.FOTableau
 ( tableauFO, checkFOTableau, proofSATFOTableau, Proofer(..), simplePickFO
 , checkFOT, proofFOT
 , module Folsolver.Data.FOTableau
 , Picker(..), fromNSATProofT) where

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
import Data.Maybe (fromJust, fromMaybe, isNothing)
import Data.List (nub)

import qualified Data.List as L ((\\))

import Control.Arrow(second)

import Data.Functor.Identity

import Text.PrettyPrint.HughesPJ as Pretty hiding (($+$))

type FOForm = (TPTP_Input,[V],Set V,Set V)

-- | map from the universal quantifier variable to its dequantified variables
type UniversalDequantMap = Map V [V]
noUniversal = M.empty

maxNodeLength :: Int
maxNodeLength = 20

fofformula :: FOForm -> TPTP_Input
fofformula (x,_,_,_)       = x

freeVariables :: FOForm -> [V]
freeVariables (_,v,_,_) = v

sAN :: AtomicWord -> String
sAN (AtomicWord s)  = s

simplePickFO 
    :: [FOForm]                 -- Aufzulösende Formeln 
    -> (FOForm, [FOForm])
simplePickFO (f:fs) = (f,fs)

tableauFO
  :: ([FOForm] -> (FOForm, [FOForm]))  -- pick function fuer die naechste formula
  -> [TPTP_Input]  -- noch zu nutztende formulas
  -> FOTableau
tableauFO pick formulas = inittree $ tableau0 (pick) (1,1) simple noUniversal (mkTC $ last formulas)
    where
        inittree = mkListTree $ init $ map mkTC formulas
        simple  = initFormulas formulas
        initFormulas :: [TPTP_Input] -> [FOForm]
        initFormulas xs = map (\x -> (x,[],S.empty,S.empty)) $ filter (isAlphaFormula . formula) xs ++ filter (\x -> (not (isAlphaFormula $ formula  x))) xs

tableau0
  :: ([FOForm] -> (FOForm, [FOForm]))  -- pick function fuer die naechste formula
  -> (Integer, Integer) -- Verzweigungs Position in the tree (spos), Tiefen Position (dpos) 
  -> [FOForm]  -- noch nicht genutzten formulas
  -> UniversalDequantMap       -- map from the universal quantifier variable to its dequantified variables introduced so far
  -> TC
  -> FOTableau
tableau0 pick (spos, dpos) [] udm tc        = leaf tc
tableau0 pick (spos, dpos) formulas udm tc  = 
  let
    nameFun sp dp = "genFunction_"++(show sp)++"_"++(show dp)
    ((f,v,uniFormVars,deuniFormVars),fs) = pick formulas
  in case reduction $ formula f of
    AlphaR a1 a2 
        -> 
            let
                at1 = mkTPTP (nameFun spos dpos) "plain" a1 [("alpha1",[sAN.name $ f])]
                at2 = mkTPTP (nameFun spos (dpos + 1)) "plain" a2 [("alpha2",[sAN.name $ f])]
            in
                tc <|> mkTC at1 <|> tableau0 pick (spos, dpos+2) (fs++[(at1,v,uniFormVars,deuniFormVars),(at2,v,uniFormVars,deuniFormVars)]) udm (mkTC at2)
    BetaR b1 b2  
        -> 
            let
                udm' = foldr (M.update (\x -> Just $ x L.\\ (S.toList deuniFormVars) ) ) udm (S.toList uniFormVars) -- foldr M.delete udm (S.toList uniFormVars)
                bt1 = mkTPTP (nameFun (spos*2) 1) "plain" b1 [("beta1",[sAN.name $ f])]
                bt2 = mkTPTP (nameFun ((2*spos)+1) 1) "plain" b2 [("beta2",[sAN.name $ f])]
                t1 = tableau0 pick (2*spos, 1) (fs++[(bt1,v, uniFormVars,S.empty)]) udm' (mkTC bt1)
                t2 = tableau0 pick (2*spos + 1, 1) (fs++[(bt2,v, uniFormVars,S.empty)]) udm'  (mkTC bt2)
                quantDequantTuplesToDelete = map (second fromJust) $ filter (not . isNothing . snd) $ map (\v -> (v, M.lookup v udm) ) $ S.toList uniFormVars
            in
                t1 <# foldr (flip ($*$)) (tc) quantDequantTuplesToDelete #> t2
    DNegate n   
        ->
            let
                f1 = mkTPTP (nameFun spos $ dpos) "plain" n [("negate",[sAN.name $ f])]
            in
                tc <|> tableau0 pick (spos,dpos+1) (fs++[(f1,v,uniFormVars,deuniFormVars)]) udm (mkTC f1)
    AtomR _     
        -> tableau0 pick (spos, dpos) fs udm tc
    GammaR form var
        ->
            let
                (AtomicWord oldName)    = name f
                varName = V $ "FreeVar_"++(show spos)++"_"++(show dpos)
                rename  = variableRename var (T $ Identity $ Var varName) form
                next    = mkTPTP (nameFun spos dpos) "plain" rename [("gamma",[oldName])]
            in 
                tc <|> tableau0 pick (spos, dpos+1) (fs++[(next,varName:v,S.insert var uniFormVars,S.insert varName deuniFormVars),(f,v,uniFormVars,deuniFormVars)]) (M.insertWith (++) var [varName] udm) (mkTC next)
    DeltaR form var 
        -> 
            let
                (AtomicWord oldName)    = name f
                skolName    = AtomicWord $ "skolFun_"++(show spos)++"_"++(show dpos)
                skolFun     = T $ Identity $ FunApp skolName (map (\x -> (T $ Identity $ Var x)) v)
                rename      = variableRename var skolFun form
                next        = mkTPTP (nameFun spos dpos) "plain" rename [("delta",[oldName])]
            in
                tc <|> tableau0 pick (spos, dpos+1) (fs++[(next,v,uniFormVars,deuniFormVars)]) udm (mkTC next)
  --  _   -> tableau0 pick (spos, dpos) fs qs udm t

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
        (cond, nForms, m')  = isClosed (formula $ formTC v) m forms
    in
        if cond
        then
            (True, m')
        else
            (checkFOTableau t nForms m)
checkFOTableau t forms m       = 
    let
        (cond, nForms, m')      = isClosed (formula $ formTCT t) m forms
        (closed1, m1)           = checkFOTableau (left t) nForms m
        (closed2, m2)           = checkFOTableau (right t) nForms (removeVarOccurance (dequantsTCT t) m1)
    in
        if cond
        then
            (True,m')
        else if closed1 && closed2
        then
            (True,m2)
        else
            (False, M.empty)

isClosed :: Formula -> Sub5t1tut0r -> Set Formula -> (Bool, Set Formula, Sub5t1tut0r)
isClosed x m forms
    | isTrue x                                  = (False, forms, m)
    | isFalse x                                 = (True, forms, m)
    | S.member (noDoubleNeg ((.~.) x)) forms    = (True, forms, m)
    | not $ null $ filter fst ergs              = (True, forms, snd $ head $ ergs)
    | otherwise                                 = (False, S.insert x forms, m)
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
            (AtomicWord errName)   = name $ fromJust errCase
            (AtomicWord fName) = name witTPTP
            wName       = drop 12 fName
            contForm    = (applySub m' $ formula witTPTP) .&. (applySub m' $ formula $ fromJust errCase)
            contradict = mkTPTP ("contradict_"++wName) "plain" contForm [("contradiction_of",[fName, errName])]
        in
            (mkNSATProof $ (formTC v) <|> leaf contradict, m' )
    | isSATProof subTree    = (subTree, m'')
    | otherwise             = (mkNSATProof $ (formTC v) <|> subPTree, m'')
    where
        (closed,nForms,witness, errCase, m')    = isClosedWithWitness (formTC v) m forms
        (subTree,m'')                           = proofSATFOTableau t m nForms
        subPTree                                = fromNSATProofT subTree
proofSATFOTableau t m forms
    | closed                = 
        let
            witTPTP     = fromJust witness
            (AtomicWord errName)   = name $ fromJust errCase
            (AtomicWord fName) = name witTPTP
            wName       = drop 12 fName
            contForm    = (applySub m' $ formula witTPTP) .&. (applySub m' $ formula $ fromJust errCase)
            contradict = mkTPTP ("contradict_"++wName) "plain" contForm [("contradiction_of",[fName, errName])]
        in
            (mkNSATProof $ (formTCT t) <|> leaf contradict,m')
    | isSATProof proofLeft  = (proofLeft, M.empty)
    | isSATProof proofRight = (proofRight, M.empty)
    | otherwise             = (mkNSATProof $ leftPTree <# formTCT t #> rightPTree, m''')
    where
        (closed, nForms, witness, errCase, m')  = isClosedWithWitness (formTCT t) m forms
        (proofLeft,m'')      = proofSATFOTableau (left t) m nForms
        (proofRight, m''')   = proofSATFOTableau (right t) (removeVarOccurance (dequantsTCT t) m'') nForms
        (leftPTree)  = fromNSATProofT proofLeft
        (rightPTree) = fromNSATProofT proofRight

isClosedWithWitness :: TPTP_Input -> Sub5t1tut0r -> Set TPTP_Input -> (Bool, Set TPTP_Input, Maybe TPTP_Input, Maybe TPTP_Input, Sub5t1tut0r)
--isClosedWithWitness [] m forms             = (False, forms, Nothing, Nothing, m)
isClosedWithWitness x m forms
    | isTrue (formula x)                            = (False, forms, Nothing, Nothing, m)
    | isFalse (formula x)                           = (True, forms, Just x, Just x, m)
    | not $ null directErgs                         = (True, forms, Just x, Just $ head directErgs, m)
    | not $ null $ unifyErgs                        = (True, forms, Just x, Just $ snd $ head unifyErgs, snd $ fst $ head $ unifyErgs)
    | otherwise                                     = (False, (S.insert x forms), Nothing, Nothing, m)
    where
        negF        = noDoubleNeg ((.~.) (formula x))
        directErgs = filter (((==) negF ) . formula) (S.toList forms)
        unifyErgs = filter (fst . fst) $  map (\x -> (unifyEquals m negF (formula x), x)) (S.toList forms)
 
instance Proofer FOTableau where
  data NSATProof FOTableau = NSAT {fromNSATproofT :: BinTreeS TPTP_Input} deriving Show
  data Picker FOTableau = Picker {pick :: [FOForm] -> (FOForm, [FOForm])}
  mkProofer (Picker picker) formulas = tableauFO picker formulas
  
  isSAT tableau = not $ fst $ checkFOTableau tableau S.empty M.empty
  proofSAT t = fst $ proofSATFOTableau t M.empty S.empty

mkNSATProof = mkProof . NSAT
fromNSATProofT = fromNSATproofT . getNSATProof0

instance HasPretty (NSATProof FOTableau) where
  pretty (NSAT nsatproof) = Pretty.text "  [ tableau proof ]" $$ pretty nsatproof
  
-- instance (HasPretty ([TPTP_Input_ Identity], [V])) where
--  pretty (a,b) = pretty a

-- | shorthands to use a tableau proofer
proofFOT = proof (Picker simplePickFO)
checkFOT = check (Picker simplePickFO)
