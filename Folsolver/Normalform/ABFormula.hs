module Folsolver.Normalform.ABFormula
 ( abFormula, ABFormula(..)
 , isAlpha, isBeta
 ) where

import Codec.TPTP
import Data.Functor.Identity
import Folsolver.TPTP

data ABFormula = Alpha {alpha1 :: Formula, alpha2 :: Formula} | Beta {beta1 :: Formula, beta2 :: Formula} | NoType Formula
        deriving (Eq,Ord,Show,Read)

isAlpha, isBeta :: ABFormula -> Bool
isAlpha (Alpha _ _) = True
isAlpha _ = False
isBeta (Beta _ _) = True
isBeta _ = False

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
