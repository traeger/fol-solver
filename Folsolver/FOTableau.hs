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
tableauFO pick formulas = tableau0 (pick) 1 simple compl (leaf formulas)
    where
        (simple,compl) = initFormulas formulas
        initFormulas :: [TPTP_Input] -> ([FOForm],[FOForm])
        initFormulas xs = (map (\x -> (x,[])) $ filter (isAlphaFormula . formula) xs ++ filter (\x -> (isSimple . formula) x && (not (isAlphaFormula $ formula  x))) xs, map (\x -> (x,[])) $ filter (isQuant . formula) xs)

tableau0
  :: ([FOForm] -> [FOForm] -> (FOForm, [FOForm],[FOForm]))  -- pick function fuer die naechste formula
  -> Integer
  -> [FOForm]  -- noch nicht genutzten formulas
  -> [FOForm]  -- quantifizierte formulas
  -> FOTableau    -- kurzzeitiges Tableau (brauchen wir fuer mehrere alpha schritte)
  -> FOTableau
tableau0 pick pos [] [] t           = t
tableau0 pick pos formulas quans t    = 
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
                    tableau0 pick pos (fs++[(at1,v),(at2,v)]) qs (leaf $ value t ++ [at1, at2])
                else
                    value t <|> tableau0 pick (2*pos) (fs++[(at1,v),(at2,v)]) qs (leaf [at1,at2]) 
    BetaR b1 b2  
        -> 
            let
                bt1 = mkTPTP (nameFun (pos * 2) 1) "plain" b1 [("beta1",[show.name $ f])]
                bt2 = mkTPTP (nameFun ((2*pos)+1) 1) "plain" b2 [("beta2",[show.name $ f])]
                t1 = tableau0 pick (2*pos) (fs++[(bt1,v)]) qs (leaf [bt1])
                t2 = tableau0 pick (2*pos + 1) (fs++[(bt2,v)]) qs (leaf [bt2])
            in
                t1  <# value t #> t2
    DNegate n   
        ->
            let
                f1 = mkTPTP (nameFun pos $ (length $ value t)) "plain" n [("negate",[show.name $ f])]
            in
                if (length $ value t) > maxNodeLength
                then
                    tableau0 pick pos (fs++[(f1,v)]) qs (leaf $ value t ++ [f1])                    -- handle double negate
                else
                    value t <|> tableau0 pick (2*pos) (fs++[(f1,v)]) qs (leaf [f1])
    AtomR _     
        -> tableau0 pick pos fs qs t
    GammaR form var
        ->
            let
                (AtomicWord oldName)    = name f
                newFunName  = "genFunction_"++show pos++"_"++(show $ length $ value t)
                varName = V $ "FreeVar_"++show pos++"_"++(show $ length $ value t)
                rename  = variableRename var (T $ Identity $ Var varName) form
                next    = mkTPTP newFunName "plain" rename [("gamma",[oldName])]
            in 
                if (length $ value t) > maxNodeLength
                then
                    tableau0 pick pos (fs++[(next,varName:v)]) (qs++[(f,v)]) t
                else
                    value t <|> tableau0 pick (2*pos) (fs++[(next,varName:v)]) (qs++[(f,v)]) (leaf [next])
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
                    tableau0 pick pos (fs++[(next,v)]) qs t
                else
                    value t <|> tableau0 pick (2*pos) (fs++[(next,v)]) qs (leaf [next])
  --  _   -> tableau0 pick pos fs qs t
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
    -> Bool             
checkFOTableau (BinEmpty) _   = False
checkFOTableau (SNode t v) forms =
    let
        (cond, nForms)  = isClosed (map formula v) forms
    in
        cond || (checkFOTableau t nForms)
checkFOTableau t forms        = 
    let
        (cond, nForms)      = isClosed (map formula $ value t) forms
    in
        cond || (checkFOTableau (left t) nForms && checkFOTableau (right t) nForms)

isClosed :: [Formula] -> Set Formula -> (Bool, Set Formula)
isClosed [] forms              = (False, forms)
isClosed (x:xs) forms
    | isTrue x                                  = isClosed xs forms
    | isFalse x                                 = (True, forms)
    | S.member (noDoubleNeg ((.~.) x)) forms    = (True, forms)
    | or $ map (unifyEquals (noDoubleNeg ((.~.) x))) (S.toList forms)  = (True, forms)
    | otherwise                                 = isClosed xs forms
            
proofSATFOTableau 
    :: 
    FOTableau             -- Current branch of the tableau
    -> Set TPTP_Input      -- Formulas seen so far
    -> Proof FOTableau 
proofSATFOTableau (BinEmpty) forms = mkSATProof $ nub $ filter isLiteral $ (map formula) $ S.toList $ forms
proofSATFOTableau (SNode t v) forms
    | closed                =
        let
            witTPTP     = head $ filter ((==) $ fromJust witness) $ v
            tillWit     = takeWhile ((/=) $ fromJust witness) $ v
            (AtomicWord fName) = name witTPTP
            wName       = drop 12 fName
            contradict  = mkTPTP ("contradict_"++wName) "plain" false [("contradiction_of",[fName])]
        in
            mkNSATProof $ leaf $ tillWit ++ [witTPTP,contradict]
    | isSATProof subTree    = subTree
    | otherwise             = mkNSATProof $ v <|> subPTree
    where
        (closed,nForms,witness) = isClosedWithWitness v forms
        subTree                 = proofSATFOTableau t nForms
        subPTree                = fromNSATProofT subTree
proofSATFOTableau t forms
    | closed                = 
        let
            witTPTP     = head $ filter ((==) $ fromJust witness) $ value t
            tillWit     = takeWhile ((/=) $ fromJust witness) $ value t
            (AtomicWord fName) = name witTPTP
            wName       = drop 12 fName
            -- cond        = head $ filter (((==) (noDoubleNeg ((.~.) $ formula witTPTP))).formula) ((S.toList forms)++(value t))
            contradict = mkTPTP ("contradict_"++wName) "plain" false [("contradiction_of",[fName])]
        in
            mkNSATProof $ leaf $ tillWit ++ [witTPTP,contradict]
    | isSATProof proofLeft  = proofLeft
    | isSATProof proofRight = proofRight
    | otherwise             = mkNSATProof $ leftPTree <# value t #> rightPTree
    where
        (closed, nForms, witness)  = isClosedWithWitness (value t) forms
        proofLeft       = proofSATFOTableau (left t) nForms
        proofRight      = proofSATFOTableau (right t) nForms
        (leftPTree)  = fromNSATProofT proofLeft
        (rightPTree) = fromNSATProofT proofRight

isClosedWithWitness :: [TPTP_Input] -> Set TPTP_Input -> (Bool, Set TPTP_Input, Maybe TPTP_Input)
isClosedWithWitness [] forms              = (False, forms, Nothing)
isClosedWithWitness (x:xs) forms
    | isTrue (formula x)        = isClosedWithWitness xs forms
    | isFalse (formula x)       = (True, forms, Just x)
    | S.member (noDoubleNeg ((.~.) (formula x))) (S.map formula forms)  
                                = (True, forms, Just x)
    | or $ map (unifyEquals (noDoubleNeg ((.~.) (formula x)))) (map formula $ S.toList forms)
                                = (True, forms, Just x)
    | otherwise                 = isClosedWithWitness xs (S.insert x forms)
 
instance Proofer FOTableau where
  data NSATProof FOTableau = NSAT {fromNSATproofT :: FOTableau} deriving Show
  data Picker FOTableau = Picker {pick :: [FOForm] -> [FOForm] -> (FOForm, [FOForm],[FOForm])}
  mkProofer (Picker picker) formulas = tableauFO picker formulas
  
  isSAT tableau = not $ checkFOTableau tableau S.empty
  proofSAT t = proofSATFOTableau t S.empty

mkNSATProof = mkProof . NSAT
fromNSATProofT = fromNSATproofT . getNSATProof0

instance HasPretty (NSATProof FOTableau) where
  pretty (NSAT nsatproof) = Pretty.text "  [ tableau proof ]" $$ pretty nsatproof

-- | shorthands to use a tableau proofer
proofFOT = proof (Picker simplePickFO)
checkFOT = check (Picker simplePickFO)
