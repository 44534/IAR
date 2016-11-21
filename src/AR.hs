{-|
Module      : AR
Description : Class for Appearance Records
Copyright   : Clara Waldmann, 2016

Class for Appearance Records
-}

module AR where

import qualified Data.Map as M
import qualified Data.Set as S

import OmegaAutomata.Automata as A

-- | class for Appearance Records
class AR ar where
    -- | access state component of the AR
    arstate :: ar q -> q 
    -- | initial state to start construction
    arstart :: q -> Int -> ar q 
    -- | transition function (labelled successors to an AR)
    ardelta :: Ord q => DRA q sigma l -> ar q -> [(sigma, ar q)] 
    -- | assign priorities to ARs
    arprio :: Ord q => [Rabinpair q] -> ar q -> Int 
    -- | default AR for states in edgeless SCCs or SCCs where no indices have to be tracked
    arempty :: q -> ar q 
    
-- | apply a function recursively until a fixpoint is reached
ufix :: Eq a => 
       (a -> a) -- ^ function
    -> a        -- ^ start 
    -> a        -- ^ fixpoint
ufix f s = let t = f s 
           in if t == s then s else ufix f t
            
-- | Computes from a set of elements the set of direct successors.
reachl :: Ord q => 
       (q -> S.Set q)  -- ^ successor function
    -> S.Set q         -- ^ set of elements 
    -> S.Set q         -- ^ direct successors of the elements
reachl  delta qs = S.unions $ do
    q <- S.toList qs
    return $ delta q
            
-- | Computes all reachable elements starting from a given element given a function that computes the direct successors of an element.      
reach :: (Eq q, Ord q) => 
    (q -> S.Set q) -- ^ successor function
    -> q           -- ^ starting element
    -> S.Set q     -- ^ reachable elements
reach delta q = ufix (\qs -> S.union qs $ reachl delta qs) $ S.singleton q

-- | compute priorities to given states and reduce them.
--
-- If only priorities 5,6,7 occur they are reduced to 1,2,3.
prios :: ( Ord (ar q), Ord q, AR ar)=> [Rabinpair q] -> [ar q] -> M.Map (ar q) Int
prios acc sts = 
    let m' = M.fromList $ (\s -> (s,arprio acc s)) <$> sts
        minpar = minimum $ M.elems m'
        shift = if even minpar then minpar else minpar - 1
    in M.map (\i-> i - shift) m'

-- | translate a Rabin automaton into a parity automaton
rabin2parity :: (Ord (rec q), Ord q, AR rec) => 
       DRA q sigma l         -- ^ the Rabin automaton
    -> DPA (rec q) sigma Int -- ^ the parity automaton having ARs as states
rabin2parity r = let n = length $ accept r 
                     [startstate] = S.toList $ A.start r
                     initialAR = AR.arstart startstate n
                     statesAR = S.toList $ 
                        reach (S.fromList . map snd . ardelta r) initialAR
                     priorities = prios (accept r) statesAR
                     transitions = do
                         q <- statesAR
                         (s,q') <- ardelta r q 
                         return (q,s, q')
                 in (makeAutomat 
                        (M.toList priorities) 
                        transitions 
                        [initialAR] 
                        (A.MaxEv priorities)
                    ) { A.aps = A.aps r }
                 
{- | example Rabin automaton (from Example 5.6 of the thesis)

@ exdra = makeAutomat
    [ (1,()),(2,()),(3,())
    , (4,()),(5,()),(6,())
    , (7,()),(8,())
    ]
    [ (1,'a',2), (1,'b',5)
    , (2,'a',3), (2,'b',4)
    , (3,'a',7), (3,'b',3)
    , (4,'a',5), (4,'b',6)
    , (5,'a',4), (5,'a',5)
    , (6,'a',6), (6,'b',5)
    , (7,'a',8), (7,'b',7)
    , (8,'a',7), (8,'b',8)
    ]
    [1]
    [ (S.fromList [6], S.fromList [5])
    , (S.fromList [4,5], S.fromList [6])
    , (S.fromList [1,7], S.fromList [2,3])
    , (S.fromList [8], S.fromList [2])
    ]
@
-}
exdra :: DRA Int Char ()
exdra = makeAutomat
    [ (1,()),(2,()),(3,())
    , (4,()),(5,()),(6,())
    , (7,()),(8,())
    ]
    [ (1,'a',2), (1,'b',5)
    , (2,'a',3), (2,'b',4)
    , (3,'a',7), (3,'b',3)
    , (4,'a',5), (4,'b',6)
    , (5,'a',4), (5,'a',5)
    , (6,'a',6), (6,'b',5)
    , (7,'a',8), (7,'b',7)
    , (8,'a',7), (8,'b',8)
    ]
    [1]
    [ (S.fromList [6], S.fromList [5])
    , (S.fromList [4,5], S.fromList [6])
    , (S.fromList [1,7], S.fromList [2,3])
    , (S.fromList [8], S.fromList [2])
    ]
