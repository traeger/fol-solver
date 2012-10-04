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
    case abFormula x of
        (NoType _)  -> isNothing $ stripDoubleNeg x
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
