module Folsolver.Data.TPTP_gen where

import Codec.TPTP
import Folsolver.TPTP(false)

mkTPTP 
    :: String               -- formula name
    -> String               -- Role
    -> Formula              -- formula
    -> [(String,[String])]  -- Annotations
    -> TPTP_Input
mkTPTP name role form ann   = (((mkEmptyTPTP <+---> name) <-+--> role) <--+-> form) <---+> ann

mkTPTP' :: String -> String -> Formula -> (String,[String]) -> TPTP_Input
mkTPTP' a b c d = mkTPTP a b c [d]

mkEmptyTPTP :: TPTP_Input
mkEmptyTPTP = (AFormula (AtomicWord "") (Role "unkown") false NoAnnotations)

infixl 2 <+--->
infixl 2 <-+-->
infixl 2 <--+->
infixl 2 <---+>

(<+--->) ::  TPTP_Input -> String -> TPTP_Input
(<+--->) (AFormula _ r f a) name   = (AFormula (AtomicWord name) r f a)

(<-+-->) :: TPTP_Input -> String -> TPTP_Input
(<-+-->) (AFormula n _ f a) role   = (AFormula n (Role role) f a)

(<--+->) :: TPTP_Input -> Formula -> TPTP_Input
(<--+->) (AFormula n r _ a) form   = (AFormula n r form a)

(<---+>) :: TPTP_Input -> [(String,[String])] -> TPTP_Input
(<---+>) (AFormula n r f _) ann    = (AFormula n r f (parseAn ann))
    where
        parseAn :: [(String,[String])] -> Annotations
        parseAn xs  = Annotations (GList (map pGTerm xs)) NoUsefulInfo
        pGTerm :: (String,[String]) -> GTerm
        pGTerm (name, []) = GTerm $ GWord (AtomicWord x)
        pGTerm (name, args) = GTerm (GApp (AtomicWord name) (map (\x-> GTerm $ GWord $ AtomicWord x) args))
