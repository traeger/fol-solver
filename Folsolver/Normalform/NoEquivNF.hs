module Folsolver.Normalform.NoEquivNF where

import Codec.TPTP
import Data.Functor.Identity

stripFromInput :: TPTP_Input -> TPTP_Input
stripFromInput (AFormula name role form anno) = AFormula name role (stripEquiv form) anno 

stripEquiv :: Formula -> Formula
stripEquiv (F p) = let Identity f = p in F $ Identity $ case f of
    BinOp left (:<=>:) right -> 
      let 
        newLeft = F $ Identity $ BinOp (stripEquiv left) (:<=:) (stripEquiv right)
        newRight = F $ Identity $ BinOp (stripEquiv left) (:=>:) (stripEquiv right)
      in
        BinOp newLeft (:&:) newRight
    BinOp left op right -> BinOp (stripEquiv left) op (stripEquiv right)
    s@(InfixPred _ _ _) -> s
    s@(PredApp _ _) -> s
    Quant q quants formula -> Quant q quants (stripEquiv formula)
    (:~:) formula -> (:~:) (stripEquiv formula)
