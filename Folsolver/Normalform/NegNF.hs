module Folsolver.Normalform.NegNF
 ( mkNeg, negQ, negNormal, negNormalNeg
 ) where

import Codec.TPTP
import Data.Functor.Identity
import Folsolver.TPTP

mkNeg :: Formula -> Formula
mkNeg = (.~.)

-- | Negates of the quantifiers
negQ :: Quant -> Quant
negQ All       = Exists
negQ Exists    = All

-- | Negation Normal form, assumption, the formula is Positiv
negNormal :: Formula -> Formula
negNormal f =
    wrapF $ case unwrapF f of
        BinOp left op right     -> BinOp (negNormal left) op (negNormal right)
        Quant q quants formula  -> Quant q quants (negNormal formula)
        (:~:) f                 -> unwrapF $ negNormalNeg f
        s                       -> s

-- | Negation Normal form, we carry a negation with us
negNormalNeg :: Formula -> Formula
negNormalNeg f =
    case unwrapF f of
        BinOp left (:<=>:) right    -> (negNormal left) .<~>. (negNormal right)
        BinOp left (:<~>:) right    -> (negNormal left) .<=>. (negNormal right)
        BinOp left (:=>:) right     -> (negNormal left) .&. (negNormalNeg right)
        BinOp left (:<=:) right     -> (negNormalNeg left) .&. (negNormal right)
        BinOp left (:&:) right      -> (negNormalNeg left) .|. (negNormalNeg right)
        BinOp left (:|:) right      -> (negNormalNeg left) .&. (negNormalNeg right)
        BinOp left (:~&:) right     -> (negNormal left) .&. (negNormal right)
        BinOp left (:~|:) right     -> (negNormal left) .|. (negNormal right)

        Quant q quants formula      -> wrapF $ Quant (negQ q) quants (negNormalNeg formula)

        (:~:) f                     -> negNormal f
        _                           -> (.~.) f
