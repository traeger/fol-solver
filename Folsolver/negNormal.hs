import Codec.TPTP
import Data.Functor.Identity
import Folsolver.TPTP

transformOnInput :: (Formula -> Formula) -> TPTP_Input -> TPTP_Input
transformOnInput fun (AFormula name role form anno) = AFormula name role (fun form) anno

{-
 - Negation Normal Form of a FOF Term by the dual of
 - the operations.
 -}

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
        s                           -> (.~.) (wrapF $ s)

data ABFormula = Alpha Formula Formula | Beta Formula Formula | NoType Formula
        deriving (Eq,Ord,Show,Read)

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
                
        s                           -> NoType $ wrapF $ s
