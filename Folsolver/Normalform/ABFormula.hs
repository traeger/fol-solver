module Folsolver.Normalform.ABFormula
 ( abFormula, ABFormula(..)
 , isAlpha, isBeta, isLiteral
 ) where

import Codec.TPTP
import Data.Functor.Identity
import Folsolver.TPTP
import Data.Maybe(isNothing)

data ABFormula = Alpha {alpha1 :: Formula, alpha2 :: Formula} | Beta {beta1 :: Formula, beta2 :: Formula} | NoType Formula
        deriving (Eq,Ord,Read)

instance Show ABFormula where
    show (Alpha a b)    = "Alpha { "++ (show . pretty) a++" } { "++ (show . pretty) b++" }"
    show (Beta a b)     = "Beta { "++ (show . pretty) a++" } { "++ (show . pretty) b++" }"
    show (NoType a)     = "Atom { "++ (show . pretty) a++" }"

isAlpha, isBeta :: ABFormula -> Bool
isAlpha (Alpha _ _) = True
isAlpha _ = False
isBeta (Beta _ _) = True
isBeta _ = False

-- | Checks, if we have a literal in our formula
isLiteral :: Formula -> Bool
isLiteral x     =
    case reduction x of
        (Atom _)    -> True
        _           -> False


-- | Function will deliver a alpha - beta- connectivity formula, if
-- | it is binary connected. If it is not a binary connected formula,
-- | NoType is returned and both arguments hold the formula
abFormula :: Formula -> ABFormula
abFormula f =
    case unwrapF f of
        BinOp left (:<=>:) right    -> Beta (left .&. right) ((.~.) $ left .|. right)
        BinOp left (:<~>:) right    -> Alpha (left .|. right) ((.~.) $ left .&. right)
        BinOp left (:=>:) right     -> Beta ((.~.) left) right
        BinOp left (:<=:) right     -> Beta left ((.~.) right)
        BinOp left (:&:) right      -> Alpha left right
        BinOp left (:|:) right      -> Beta left right
        BinOp left (:~&:) right     -> Beta ((.~.) left) ((.~.) right)
        BinOp left (:~|:) right     -> Alpha ((.~.) left) ((.~.) right)

        (:~:) f'    ->  case unwrapF f' of
            BinOp left (:<=>:) right    -> Alpha (left .|. right) ((.~.) $ left .&. right)
            BinOp left (:<~>:) right    -> Beta (left .&. right) ((.~.) $ left .|. right)
            BinOp left (:=>:) right     -> Alpha left ((.~.) right)
            BinOp left (:<=:) right     -> Alpha ((.~.) left) right
            BinOp left (:&:) right      -> Beta ((.~.) left) ((.~.) right)
            BinOp left (:|:) right      -> Alpha ((.~.) left) ((.~.) right)
            BinOp left (:~&:) right     -> Alpha left right
            BinOp left (:~|:) right     -> Beta left right

            (:~:) form                  -> NoType $ (.~.) $ (.~.) $ form
            _                           -> NoType $ (.~.) f
        _                           -> NoType $  f

data DGFormula = Delta {deltaF :: Formula , dVar :: V} | Gamma {gammaF :: Formula, gVar :: Var} | NoQuant { nForm :: Formula }

instance Show DGFormula where
    show (Delta f v)    = "delta{ "++show v++" , "++show f++" }"
    show (Gamma f v)    = "gamma{ "++show v++" , "++show f++" }"
    show (NoQuant f)    = "noQuantifier{ "++show f++" }"


-- | This function will cut a formula if it is quantified.
-- | It will then return the formula (the quantifier is stripped)
-- | and the variable, that should be substituited.
dgFormula :: Formula -> DGFormula
dgFormula f =
    case unwrapF f of
        Quant All [x] f0            -> Gamma f0 x
        Quant All (x:xs) f0         -> Gamma (Quant All xs f0) x
        Quant Exists [x] f0         -> Delta f0 x
        Quant Exists (x:xs) f0      -> Delta (Quant All xs f0) x
        (:~:) f0    -> case unwrapF f0 of
            Quant All [x] f1        -> Delta ((.~.) f1) x
            Quant All (x:xs) f1     -> Delta ((.~.) (Quant All xs f1)) x
            Quant Exists [x] f1     -> Gamma ((.~.) f1) x
            Quant Exists (x:xs) f1  -> Gamma ((.~.) (Quant Exists xs f1)) x 
            _                       -> NoQuant f
        _                           -> NoQuant f

data RedFormula =
    AlphaR { alphaR1 :: Formula , alphaR2 :: Formula }
    BetaR { betaR1 :: Formula , betaR2 :: Formula }
    Gamma { gammaR :: Formula, gVarR :: Var }
    Delta { delaR :: Formula, dVarR :: Var }
    DNegate { negate :: Formula }
    Atom { atom :: Formula }

instance Show RedFormula =
    show (AlphaR a b)   = show (Alpha a b)
    show (BetaR a b)    = show (Beta a b)
    show (GammaR a b)   = show (Gamma a b)
    show (DeltaR a b)   = show (Delta a b)
    show (DNegate a)    = "double neg { "++show a++" }"
    show (Atom a)       = "atom { "++show a"++ }"

reduction :: Formula -> RedFormula
reduction f =
    case abFormula f of
        (Alpha a b)                     -> (AlphaR a b)
        (Beta a b)                      -> (BetaR a b)
        (NoType _)  -> case dgFormula f of
            (Delta f x)                 -> (DeltaR f x)
            (Gamma f x)                 -> (Gamma f x)
            (NoQuant _) -> case unwrapF f of
                ((:~:) f0)  -> case unwrap f0 of
                    ((:~:) f1)          -> (DNegate f1)
                    _                   -> (Atom f)
                _                       -> (Atom f)
