module Folsolver.Resolution where

import Folsolver.TPTP
import Folsolver.Normalform

import Data.List

import Codec.TPTP

{-
 - Int the Resolution calculus we need to apply
 - the reduction rules to every formula we have
 - once.
 - Therefor we have to keep track, which formulas
 - we need to resolve furhter.
 - On the other hand we might have to resolve any
 - to formulas and we will not save all these options.
 -
 - Our approach is, to decide, whether to use resolution rule
 - or reduction and then check, if the disjuntion
 - is already in our set of formulas.
 -}

{- | In a ResFormula the inner lists are all connected
 - | by conjecture and the formulas in the inner lists
 - | are connected by disjuncture.
 -
 - | By Resolution term exists as it is in clause1 and negated in clause2
 -}
type ResFormula = [[Formula]]

data ResAction =    Reduction { reduce :: Formula , clause :: [Formula]}
                |   Resolution { clause1 :: [Formula] , clause2 :: [Formula] , term :: Formula}
                |   NoAction
                    

{-
 - | Takes the formulas from the input
 - | if it is a conjecture it will be negated
 -
 - | Is also defined in Tableau. Move to other package.
 -}
transformInput :: [TPTP_Input] -> [Formula]
transformInput []                                           = []
transformInput (AFormula _ (Role "conjecture") f _:xs)      = ((.~.) f) : transformInput xs
transformInput (AFormula _ (Role "axiom") f _:xs)           = f : transformInput xs
transformInput (_:xs)                                       = transformInput xs 

{-
 - | Takes a formula to pick the next step
 - | and a list of input
 - | and returns true iff the input is a tautology.
 -}
resolutionProof 
    :: 
    (ResFormula -> ResAction)                   -- This function will consider what to do next
    -> [TPTP_Input]                             -- A list of TPTP input formulas
    -> Bool
resolutionProof pick forms  = elem []  $ map (flip (:) []) forms' ++ resolution pick (map (flip (:) []) forms')
    where forms' = transformInput forms


{- | The resolution function creates lazy the complete resolution list.
 - | It will simply executes the actions given by the pick function.
 -}
resolution :: (ResFormula -> ResAction) -> ResFormula -> ResFormula
resolution pick res     = case pick res of
    (NoAction)                  -> []
    (Reduction toRed clause)    -> let c = delete toRed clause in 
        case abFormula toRed of
            Alpha a1 a2   -> 
                let new =  [a:c | a <- [a1,a2], notElem (a:c) res] in
                    new ++ resolution pick (new ++ res)
            Beta b1 b2    -> (b1 : b2 : c) : resolution pick ((b1 : b2 : c) : res)
            NoType f      -> case stripDoubleNeg f of
              Just f0       -> (f0 : c) : resolution pick ((f0:c):res)
              Nothing       -> resolution pick res
    (Resolution c1 c2 t)         -> 
            let
                cd1 = delete t c1
                cd2 = delete (noDoubleNeg ((.~.) t)) c2
            in
                (cd1 ++ cd2) : resolution pick (res ++ [cd1++cd2])



resSimplePick :: ResFormula -> ResAction
resSimplePick xs    = case rnd False True of
    True    -> 
        let
            c1 = xs !! rnd 0 (length xs)
            t1 = c1 !! rnd 0 (length c1)
        in
            Reduction t1 c1
    False   -> 
        let
            c1 = xs !! rnd 0 (length xs)
            c2 = xs !! rnd 0 (length xs)
            op = [ red | red <- c1, y <- c2, red == (noDoubleNeg ((.~.) y))] 
        in
            if null op
            then
                resSimplePick xs
            else
                Resolution c1 c2 (head op)               
            
