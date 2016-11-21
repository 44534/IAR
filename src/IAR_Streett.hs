{-|
Module      : IAR-Streett
Description : Translation of Streett to parity automata 
Copyright   : Clara Waldmann, 2016

Translation of Streett to parity automata. Implementation of the IAR-procedure found in "Methods for the Transformation of Omega-Automata: Complexity and Connection to Second Order Logic." Chapter 3.2.2 (C. Löding)
-}

module IAR_Streett
where

import qualified Data.Set as S
import qualified Data.List as L

import OmegaAutomata.Automata as A
import AR

-- | Data structure for Index Appearance Records
data SIAR q = SIAR { 
      state :: q    -- ^ current state
    , perm :: [Int] -- ^ permutation of indices of pairs
    , fPtr :: Int   -- ^ pointer f
    , ePtr :: Int   -- ^ pointer e
    }
  deriving (Show, Ord, Eq)
            
instance AR SIAR where
    arstate = state
    arstart q n = SIAR q [1..n] (n+1) (n+1)
    ardelta =  deltaIAR
    arprio = prio
    arempty q = SIAR q [] 0 0

-- | the transition function \delta ^ IAR
deltaIAR :: (Ord q) => DRA q sigma l -> SIAR q -> [(sigma, SIAR q)]
deltaIAR r siar@(SIAR q _ _ _) = do
            let omega = accept r
            (q',s) <- succs r q  
            return (s, phiIAR omega siar q')
    
-- | function phi ^ IAR
phiIAR :: Ord q => [Rabinpair q] -> SIAR q -> q -> SIAR q
phiIAR omega siar@(SIAR q perm _ _) q' =
    let r = length omega
        (es, fs) = unzip omega
        k = case L.find (\j -> S.member q' (es !! ((perm !! (j-1)) - 1)) ) [1.. r] of
                Nothing -> r + 1
                Just j -> j 
        l = case L.find (\j -> S.member q' (fs !! ((perm !! (j-1)) - 1)) ) [1.. r] of
                Nothing -> r + 1
                Just j -> j
        perm' = if k == r + 1 
                   then perm 
                   else let (front, _:back) = splitAt (k-1) perm
                        in front ++ back ++ [perm !! (k-1)]
    in SIAR q' perm' l k
               
-- | computes priorities for states as in Löding but adds 1 to complement the resulting parity automaton
prio :: Ord q => [Rabinpair q] -> SIAR q -> Int
prio ps iar@(SIAR _ _ fp ep) = 
    let r = length ps
        l = case L.find (\i -> ((ep > i-1) && (fp == i-1)) || ((fp >= i) && (ep == i)) ) [1..r+1] of
                Just i -> if (ep > i-1) && (fp == i-1)
                            then 2*(r+1) - 2*i + 2
                            else 2*(r+1) - 2*i + 1
                Nothing -> error "stop"
         
    in  l
                      
