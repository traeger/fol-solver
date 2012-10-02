module Folsolver.Normalform.OperatorNF where

import Codec.TPTP
import Data.Functor.Identity

import Folsolver.TPTP

-- |ReplaceOp takes a function, which replaces an operation with another formula,
-- | if specified correctly, it will remove a kind of Operators from the formula.
replaceOp :: (BinOp -> Formula -> Formula -> Formula) -> Formula -> Formula
replaceOp trans f = case unwrapF f of
    BinOp left op right -> trans op (replaceOp trans left) (replaceOp trans right)
    Quant q quants formula  -> wrapF $ Quant q quants (noEquivNF formula)
    _                       -> f
   
-- | Substituites equivalenz and xor with representations in all other operators.
noEquiv :: BinOp -> Formula -> Formula -> Formula
noEquiv (:<=>:) left right  = (left .=>. right) .&. (left .<=. right)
noEquiv (:<~>:) left right  = (left .&. ((.~.) right)) .|. (((.~.) left) .&. right)
noEquiv op  left right      = wrapF $ BinOp left op right

-- | Replaces all occurens of a operation with onyl Conjunction, Disjunction, Negation
onlyCDN :: BinOp -> Formula -> Formula -> Formula
onlyCDN (:<=>:) left right  = (left .&. right) .|. (((.~.) left) .&. ((.~.) right))
onlyCDN (:<~>:) left right  = (left .&. ((.~.) right)) .|. (((.~.) left) .&. right)
onlyCDN (:=>:) left right   = ((.~.) left) .|. right
onlyCDN (:<=:) left right   = left .|. ((.~.) right)
onlyCDN (:|:) left right    = left .|. right
onlyCDN (:&:) left right    = left .&. right
onlyCDN (:~&:) left right   = ((.~.) left) .|. ((.~.) right)
onlyCDN (:~|:) left right   = ((.~.) left) .&. ((.~.) right)

-- Shortcuts

noEquivNF :: Formula -> Formula
noEquivNF = replaceOp noEquiv

cdnNF :: Formula -> Formula
cdnNF = replaceOp onlyCDN
