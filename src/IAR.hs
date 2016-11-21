{-|
Module      : IAR
Description : Translation of Rabin to parity automata using Index Appearance Records
Copyright   : Clara Waldmann, 2016

Translation of Rabin automata to parity automata using Index Appearance Records inspired by https://www.react.uni-saarland.de/teaching/automata-games-verification-11/downloads/ps9.pdf
-}

module IAR
where

import qualified Data.Set as S
import qualified Data.List as L

import OmegaAutomata.Automata as A
import AR



-- | Data structure for Index Appearance Record
data IAR q = IAR 
    { state :: q    -- ^ the current state
    , perm :: [Int] -- ^ permutation of indices of pairs
    }
  deriving (Show, Ord, Eq)
  
instance AR IAR where
    arstate = state
    arstart q n = IAR q [0.. n-1] 
    ardelta = deltaIAR
    arprio = prio
    arempty q = IAR q []
    
-- | transition function of the parity automaton
-- 
-- (q, perm) -> (q', perm') where: 
--
-- * q -> q' : sucessor as in Rabin automaton
-- * second component: sort all indices in perm where q is in the excluded set and move those to the front
deltaIAR :: (Ord q) => DRA q sigma l -> IAR q -> [(sigma, IAR q)]
deltaIAR r iar@(IAR q perm) = do
            let ps = accept r
            (q',s) <- succs r q
                
            let  es = map fst ps
                 perm' = let (ine, notine) = L.partition (\i -> S.member q (es !! i) )  perm
                         in (L.sort ine) ++ notine
            return (s, IAR { state = q', perm = perm'})

-- | priority to states in the parity automaton
--
-- prio (q,perm): 2*rpos oder 2*rpos + 1
prio :: Ord q => [Rabinpair q]  -> IAR q -> Int
prio ps iar@(IAR q perm) = 
    let permps = map (\i -> ps !! i) perm
        j = case L.findIndices (\(e,f) -> S.member q (S.union e f)) permps of
                [] -> -1
                xs -> last xs
        l = case j of
                -1 -> 1
                j -> let (e,f) = permps !! j
                        in 
                        if S.member q ( f S.\\ e )
                        then 2*(j+1)
                        else 2*(j+1) + 1
    in l                
