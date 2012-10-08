{-# OPTIONS_GHC -XTypeSynonymInstances -XMultiParamTypeClasses -XFlexibleInstances -XTypeFamilies #-}

module Folsolver.FOTableau
 ( tableauFO, checkFOTableau, proofSATFOTableau, Proofer(..), simplePickFO
 , checkT, proofT, subProof, decToBin ) where

import Codec.TPTP
import Folsolver.Normalform
import Folsolver.Data.Tableau
import Folsolver.TPTP
import Folsolver.Proofer
import Folsolver.Data.TPTP_gen

import Data.Set (Set) 
import qualified Data.Set as S
import Data.Maybe (fromJust, fromMaybe)
import Data.List (nub)

import Text.PrettyPrint.HughesPJ as Pretty

type FOForm = (TPTP_Input,[V])

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
tableauFO pick formulas = tableau0 pick 1 simple compl (leaf formulas)
    where
        (simple,compl) = initFormulas formulas
        initFormulas :: [TPTP_Input] -> ([FOForm],[FOForm])
        initFormulas xs = (map (\x -> (x,[])) $ filter isAlpha xs ++ filter (\x -> isSimple x && (not (isAlpha x))) xs, map (\x -> (x,[])) $ filter isComplex xs)

tableau0
  :: ([FOForm] -> (FOForm, [FOForm],[FOForm]))  -- pick function fuer die naechste formula
  -> Integer
  -> [FOForm]  -- noch nicht genutzten formulas
  -> [FOForm]  -- quantifizierte formulas
  -> FOTableau    -- kurzzeitiges Tableau (brauchen wir fuer mehrere alpha schritte)
  -> FOTableau
tableau0 pick pos [] [] t           = t
tableau0 pick pos [] (x:xs) (FO t)  = case reduce x of
    (GammaR (form,vars) var)
        ->
            let
                newFunName  = "genFunction_"++pos++"_"++(length $ value t)
                varName = V $ "FreeVar_"++pos++"_"++(length $ value t)
                formul  = formula form
                rename  = variableRename var (Var varName) formul
                next    = mkTPTP newFunName "plain" rename [("gamma",[name form])]
            in 
                tableau0 pick pos [(next,varName:vars)] (xs++x) (FO t)
    (DelaR (form,vars) var) 
        -> 
            let
                newFunName  = "genFunction_"++pos++"_"++(length $ value t)
                skolName    = "skolFun_"++pos++"_"++(length $ value t)
                skolFun     = FunApp skolName (map (\x -> (Var x)) vars)
                rename      = variableRename var skolFun (formul form)
                next        = mkTPTP newFunName "plain" rename [("delta",[name form])]
            in
                tableau0 pick pos [(next,vars)] xs (FO t)

    _                   -> error "Should not occure"

tableau0 pick pos formulas quans (FO t)    = 
  let
    nameFun p q = "genFunction_"++(show p)++"_"++(show q)
    ((f,v),fs,qs) = pick formulas quans
  in case reduction . formula f of
    AlphaR a1 a2 -> 
        let
            at1 = mkTPTP (nameFun pos $ (length $ value t)) "plain" a1 [("alpha1",[show.name $ f])]
            at2 = mkTPTP (nameFun pos $ (length $ value t)+1) "plain" a2 [("alpha2",[show.name $ f])]
        in
            tableau0 pick pos (fs++[(at1,v),(at2,v)]) qs (FO $ leaf $ value t ++ [at1, at2])           -- handle alpha formulas
    BetaR b1 b2  -> 
        let
            bt1 = mkTPTP (nameFun (pos * 2) 1) "plain" b1 [("beta1",[show.name $ f])]
            bt2 = mkTPTP (nameFun ((2*pos)+1) 1) "plain" b2 [("beta2",[show.name $ f])]
        in
            FO $ tableau0 pick (2*pos) (fs++[(bt1,v)]) qs (leaf [bt1])  <# value t #> tableau0 pick (2*pos + 1) (fs++[(bt2,v)]) qs (leaf [bt2])  -- handle beta formulas
    DNegate n   ->
        let
            f1 = mkTPTP (nameFun pos $ (length $ value t)) "plain" n [("negate",[show.name $ f])]
        in
            tableau0 pick pos (fs++[(f1,v)]) (FO $ leaf $ value t ++ [f1])                    -- handle double negate
    AtomR _     -> tableau0 pick pos fs qs (FO t)
    _           -> tableau0 pick pos fs ((f,v):qs) (FO t)
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
checkFOTableau (FO BinEmpty) _     = False
checkFOTableau (FO t) forms        = 
    let
        (cond, nForms)      = isClosed (map formula $ value t) forms
    in
        cond || (checkFOTableau (left (FO t)) nForms && checkFOTableau (right (FO t)) nForms)

isClosed :: [Formula] -> Set Formula -> (Bool, Set Formula)
isClosed [] forms              = (False, forms)
isClosed (x:xs) forms
    | isTrue x                                  = isClosed xs forms
    | isFalse x                                 = (True, forms)
    | S.member (noDoubleNeg ((.~.) x)) forms    = (True, forms)
    | or $ map (unifyEqual (noDoubleNeg ((.~.) x))) (toList forms)  = (True, forms)
    | otherwise                                 = isClosed xs forms
            
proofSATFOTableau 
    :: 
    FOTableau             -- Current branch of the tableau
    -> Set TPTP_Input      -- Formulas seen so far
    -> Proof FOTableau 
proofSATFOTableau (FO BinEmpty) forms = mkSATProof $ nub $ filter isLiteral $ (map formula) $ S.toList $ forms
proofSATFOTableau (FO t) forms
    | closed                = 
        let
            witTPTP     = head $ filter ((==) $ fromJust witness) $ value t
            tillWit     = takeWhile ((/=) $ fromJust witness) $ value t
            wName       = let (AtomicWord x) = name witTPTP in drop 12 x
            -- cond        = head $ filter (((==) (noDoubleNeg ((.~.) $ formula witTPTP))).formula) ((S.toList forms)++(value t))
            contradict = mkTPTP ("contradict_"++wName) "plain" true [("contradiction_of",[show $ name witTPTP])]
        in
            mkNSATProof $ FO $leaf $ tillWit ++ [witTPTP,contradict]
    | isSATProof proofLeft  = proofLeft
    | isSATProof proofRight = proofRight
    | otherwise             = FO $ mkNSATProof $ fromNSATProofT proofLeft <# value t #> fromNSATProofT proofRight
    where
        (closed, nForms, witness)  = isClosedWithWitness (value t) forms
        proofLeft   = proofSATFOTableau (left t) nForms
        proofRight  = proofSATFOTableau (right t) nForms

isClosedWithWitness :: [TPTP_Input] -> Set TPTP_Input -> (Bool, Set TPTP_Input, Maybe TPTP_Input)
isClosedWithWitness [] forms              = (False, forms, Nothing)
isClosedWithWitness (x:xs) forms
    | isTrue (formula x)        = isClosedWithWitness xs forms
    | isFalse (formula x)       = (True, forms, Just x)
    | S.member (noDoubleNeg ((.~.) (formula x))) (S.map formula forms)  
                                = (True, forms, Just x)
    | or $ map (unifyEqual (NoDoubleNeg ((.~.) (formula x)))) (toList forms)
                                = (True, forms, Just x)
    | otherwise                 = isClosedWithWitness xs (S.insert x forms)
 
newtype FOTableau = FO Tableau
 
instance Proofer FOTableau where
  data NSATProof FOTableau = NSAT {fromNSATproofT :: FOTableau} deriving Show
  data Picker FOTableau = Picker {pick :: [FOForm] -> (FOForm, [FOForm],[FOForm])}
  mkProofer (Picker picker) formulas = tableau picker formulas
  
  isSAT tableau = not $ checkFOTableau tableau S.empty
  proofSAT t = proofSATFOTableau t S.empty

mkNSATProof = mkProof . NSAT
fromNSATProofT = fromNSATproofT . getNSATProof0

instance HasPretty (NSATProof FOTableau) where
  pretty (NSAT (FO nsatproof)) = Pretty.text "  [ tableau proof ]" $$ pretty nsatproof

-- | shorthands to use a tableau proofer
proofFOT = proof (Picker simplePickFO)
checkFOT = check (Picker simplePickFO)
