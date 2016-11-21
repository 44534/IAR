{-|
Module      : IAR_optimized
Description : improvements for IAR procedures 
Copyright   : Clara Waldmann, 2016

Improvements for IAR procedures: SCC decomposition, finding a good initial state.
-}

module IAR_optimized (
    rabin2parity,
    -- * Helper
    applytoboth, fromSubGraph, larWithState,
    sccNodes, sccs, interestingsccs, interestingfs, btwsccs,
    -- * SCC Decomposition
    components, connectcomponents, combineDPAs, parsuccs, toDPA,
    -- * Initial State
    reduceparitygraph
    ) where


import qualified Data.Graph.Inductive as G
import qualified Data.Set as S
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Bimap as B
import Control.Monad (guard)

import OmegaAutomata.Automata
import AR hiding (rabin2parity)

-- | translate a Rabin automaton into a parity automaton applying the improvements (SCC decomposition, finding a good initial state in each SCC) using the given basic translation
--
-- >>> IAR_optimized.rabin2parity AR.rabin2parity  exdra :: DPA (IAR Int) Char Int

rabin2parity :: (Eq sigma, Ord q, AR ar, Ord (ar q)) => 
       (DRA q sigma l -> DPA (ar q) sigma Int) -- ^ basic translation of Rabin automata to parity automata (e.g. 'AR.rabin2parity' from 'AR')
    -> DRA q sigma l        
    -> DPA (ar q) sigma Int
rabin2parity r2p dra =
    let (nonints, ints) = components dra
        intdpas = r2p <$> ints
        reddpas = zipWith reduceparitygraph ints intdpas
        nonintdpas = toDPA <$> nonints
        

    in connectcomponents dra (reddpas ++ nonintdpas)
    
{- | direct translation of Rabin automata with empty acceptance condition or no edges

Example: Let tdra be the Rabin automaton exdra restricted to its component [7,8]

>>> toDPA tdra :: DPA (IAR Int) Char Int 
Automat { states = fromList [ IAR {state = 7, perm = []}, IAR {state = 8, perm = []}]
        , bimap = fromList [(IAR {state = 7, perm = []},7),(IAR {state = 8, perm = []},8)]
        , graph = mkGraph [(7,1),(8,1)] [(7,7,'b'),(7,8,'a'),(8,7,'a'),(8,8,'b')]
        , start = fromList [IAR {state = 7, perm = []}]
        , accept = MaxEv {priomap = fromList [(IAR {state = 7, perm = []},1),(IAR {state = 8, perm = []},1)]}
        , aps = Nothing
        }

-}
toDPA :: (Ord q, AR ar, Ord (ar q)) => DRA q s l -> DPA (ar q) s Int
toDPA dra = 
    let larSts = AR.arempty <$> ( S.toList $ states dra)
        larBimap = B.map (\q -> AR.arempty q ) $ bimap dra
        drastartnodes = (toNode dra ) <$> (S.toList $ start dra)
        starts = (larBimap B.!> )<$> drastartnodes
        newGraph = G.nmap (\_ -> 1) $ graph dra
    in Automat
        { states = S.fromList larSts
        , bimap = larBimap
        , graph = newGraph
        , start = S.fromList starts
        , accept = MaxEv $ M.fromList $ zip larSts $ repeat 1
        , aps = aps dra
        }
            
-- | decompose and restrict a Rabin automaton to its strongly connected components
-- they are grouped as (edgeless SCC or SCC where no pair has to be tracked,  restriction of the Rabin automaton to a component)
components :: Ord q => DRA q s l -> ([DRA q s l], [DRA q s l])
components dra = 
    let pis = applytoboth ((toNode dra <$> ) . S.toList) <$> accept dra
        (nonintgs, ints) = interestingsccs (graph dra) pis
        (intgs, lpns) = unzip ints
        lps = (applytoboth (S.fromList . (toState dra <$>)) <$> ) <$> lpns
        ints' = zip intgs lps
        
        (nonintstarts, intstarts) = applytoboth (toState dra . head . G.nodes <$>) (nonintgs, intgs)
        nonintdras = zipWith (\g -> \q -> fromSubGraph dra g (S.singleton q) []) nonintgs nonintstarts
        intdras = zipWith (\(g,ps) -> \q -> fromSubGraph dra g (S.singleton q) ps) ints' intstarts
    in ( nonintdras , intdras)


{- | compute SCCs of a graph and the pairs that have to be tracked in this SCC
grouped as (SCCs where no pair has to be tracked, SCCs and pairs that have to be tracked)

>>> interestingsccs (graph exdra) [([6],[5]),([4,5],[6]),([1,7],[2,3]),([8],[2])]
([ mkGraph [(1,())] []
 , mkGraph [(2,())] []
 , mkGraph [(7,()),(8,())] [(7,7,'b'),(7,8,'a'),(8,7,'a'),(8,8,'b')]
 ]
,[ (mkGraph [(4,()),(5,()),(6,())] [(4,5,'a'),(4,6,'b'),(5,4,'a'),(5,5,'a'),(6,5,'b'),(6,6,'a')]
   ,[([6],[5]),([4,5],[6])]
   )
 , (mkGraph [(3,())] [(3,3,'b')]
   ,[([1,7],[2,3])]
   )
 ]
)
-}
interestingsccs :: G.Gr l s     -- ^ the graph 
    -> [([G.Node], [G.Node])]   -- ^ the Rabin pairs translated to nodes in the graph
    -> ([G.Gr l s], [(G.Gr l s, [([G.Node],[G.Node])])])
interestingsccs gr ps = 
    let (trivs, nontrivs) = sccs gr
        les = ((ps!!) <$>) <$> (interestingfs ps <$> nontrivs)
        (nonints' , ints) = L.partition (\(_, es) -> es == []) $ zip nontrivs les
    in (trivs ++ ( fst <$> nonints' ), ints)
    
{- | compute SCCs of a graph (as subgraphs) grouped as (edgeless, cyclic)

>>> sccs $ graph exdra 
( [mkGraph [(1,())] [],mkGraph [(2,())] []]
, [ mkGraph [(4,()),(5,()),(6,())] [(4,5,'a'),(4,6,'b'),(5,4,'a'),(5,5,'a'),(6,5,'b'),(6,6,'a')]
  , mkGraph [(7,()),(8,())] [(7,7,'b'),(7,8,'a'),(8,7,'a'),(8,8,'b')]
  , mkGraph [(3,())] [(3,3,'b')]
  ]
)
-}
sccs :: G.Gr l s -> ([G.Gr l s], [G.Gr l s])
sccs g = applytoboth (map (\ns -> G.subgraph ns g)) $ sccNodes g
    
-- | compute SCCs of a graph (as list of nodes) grouped as (edgeless, cyclic)
--
-- >>> sccNodes $ graph exdra 
-- ([[1],[2]],[[4,5,6],[7,8],[3]])
sccNodes :: G.Gr l s -> ([[G.Node]], [[G.Node]])
sccNodes g = 
    let (probtrivs, nontrivs) = L.partition (\ns -> 1 == length ns) $ G.scc g
        (ntrivs, trivs) =  L.partition (\[n] -> G.hasNeighbor g n n ) probtrivs
    in (trivs, nontrivs ++ ntrivs)
    
{- | compute indices of pairs that have to be tracked in the graph (the final set intersects the graph)

Example: Let g be the SCC [4,5,6] of the Rabin automaton exdra 

>>> interestingfs [([6],[5]),([4,5],[6]),([1,7],[2,3]),([8],[2])] g
[0,1]
-}
interestingfs :: [([G.Node],[G.Node])] -> G.Gr l s -> [Int]
interestingfs ps g = 
    let nodes = G.nodes g
    in L.findIndices (\(_,f) -> L.intersect f nodes /= [] ) ps
    
    
{- | compute a new automaton from a subgraph of an automaton

>>> fromSubGraph exdra 
        (G.mkGraph [(4,()),(5,()),(6,())] [(4,5,'a'),(4,6,'b'),(5,4,'a'),(5,5,'a'),(6,5,'b'),(6,6,'a')]) 
        (S.fromList [4]) 
        [(S.fromList [6], S.fromList [5]),(S.fromList [4,5], S.fromList [6])]
Automat { states = fromList [4,5,6]
        , bimap = fromList [(4,4),(5,5),(6,6)]
        , graph = mkGraph [(4,()),(5,()),(6,())] [(4,5,'a'),(4,6,'b'),(5,4,'a'),(5,5,'a'),(6,5,'b'),(6,6,'a')]
        , start = fromList [4]
        , accept = [(fromList [6],fromList [5]),(fromList [4,5],fromList [6])]
        , aps = Nothing
        }

-}
fromSubGraph :: Ord q => Automat q s l acc 
    -> G.Gr l s     -- ^ the graph of the new automaton (subgraph of the old automaton)
    -> S.Set q      -- ^ new intial states 
    -> acc          -- ^ new acceptance condition
    -> Automat q s l acc
fromSubGraph aut g ss acc = 
    let newBimap = B.filter (\q -> \n -> n `elem` (G.nodes g) ) $ bimap aut
    in Automat
        { states = S.fromList $ B.keys newBimap
        , bimap = newBimap
        , graph = g
        , start = ss
        , accept = acc
        , aps = aps aut
        }
    
{- | pick a good initial state by choosing the BSCC of the parity automaton

Example: let tdra be the Rabin automaton exdra restricted to its SCC [4,5,6]

>>> reduceparitygraph tdra $ AR.rabin2parity tdra :: DPA (IAR Int) Char Int
Automat { states = fromList [ IAR {state = 4, perm = [1,0]}
                            , IAR {state = 5, perm = [0,1]}
                            , IAR {state = 5, perm = [1,0]}
                            , IAR {state = 6, perm = [0,1]}
                            , IAR {state = 6, perm = [1,0]}
                            ]
        , bimap = fromList [ (IAR {state = 4, perm = [1,0]},2)
                           , (IAR {state = 5, perm = [0,1]},3)
                           , (IAR {state = 5, perm = [1,0]},4)
                           , (IAR {state = 6, perm = [0,1]},5)
                           , (IAR {state = 6, perm = [1,0]},6)
                           ]
        , graph = mkGraph [(2,1),(3,3),(4,2),(5,2),(6,3)] 
                          [(2,4,'a'),(2,6,'b')
                          ,(3,2,'a'),(3,4,'a')
                          ,(4,2,'a'),(4,4,'a')
                          ,(5,3,'b'),(5,5,'a')
                          ,(6,3,'b'),(6,5,'a')
                          ]
        , start = fromList [IAR {state = 4, perm = [0,1]}]
        , accept = MaxEv {priomap = fromList 
                [ (IAR {state = 4, perm = [0,1]},3)
                , (IAR {state = 4, perm = [1,0]},1)
                , (IAR {state = 5, perm = [0,1]},3)
                , (IAR {state = 5, perm = [1,0]},2)
                , (IAR {state = 6, perm = [0,1]},2)
                , (IAR {state = 6, perm = [1,0]},3)
                ]
                         }
        , aps = Nothing
        }
-}
reduceparitygraph :: (Ord q, AR ar, Ord (ar q)) => DRA q s ll -> DPA (ar q) s l -> DPA (ar q) s l
reduceparitygraph scc dpa =
    let sccStates = states scc
        parScc = do
            nodes <- snd $ sccNodes $ graph dpa
            let sts = (arstate . toState dpa) <$> nodes
            guard $ S.fromList sts == sccStates
            return nodes
        subg = G.subgraph (head parScc) $ graph dpa
        [dpastart] = S.toList $ start dpa
        st = S.singleton $ larWithState [dpa] (arstate dpastart)
        newDPA = fromSubGraph dpa subg st (MaxEv M.empty)
        MaxEv dpaparmap = accept dpa
        acc = M.filterWithKey (\lar -> \_ -> M.member lar dpaparmap) dpaparmap
    in newDPA{ accept = MaxEv acc }

-- | connect the parity automata of the components
--
-- Takes all automata and adds edges between them as in the Rabin automaton.
connectcomponents :: (Ord q, AR ar, Ord (ar q)) => DRA q s ll -> [DPA (ar q) s Int] -> DPA (ar q) s Int
connectcomponents dra dpas = 
    let [startdra] = S.toList $ start dra 
        larstart = larWithState dpas startdra
        newDPA' = combineDPAs larstart dpas
        
        newedges = concatMap (parsuccs dra dpas) $ S.toList $ states newDPA'
        newDPA = insertTrans newedges newDPA'
    in newDPA
    
-- | combine parity automata to one automaton having the automata as components (no new edges are added) and the union of the acceptance conditions
combineDPAs :: Ord q => q -> [DPA q s l] -> DPA q s l
combineDPAs start dpas =
    let qls = [(q,l) | dpa <- dpas, q <- S.toList $ states dpa, let l = label q dpa]
        pms = M.unions $ (\(MaxEv m) -> m) <$> accept <$> dpas
    in (makeAutomat qls (concatMap trans dpas) [start] (MaxEv pms)) {aps = aps $ head dpas}

{- | compute the successors of an Appearance Record in different SCCs

Example: Let dpas be the parity automata of the SCCs of the Rabin automaton exdra

>>> parsuccs exdra dpas (IAR 3 [0])
[(IAR {state = 3, perm = [0]},'a',IAR {state = 7, perm = []})]
-}
parsuccs :: (Eq q, Ord q, AR ar, Ord (ar q)) => DRA q s ll -> [DPA (ar q) s l] -> (ar q) -> [(ar q, s, ar q)]
parsuccs dra dpas larq =
    let q = arstate larq
    in do
        (q',a) <- succs dra q
        guard $ btwsccs dra (q', q)
        return (larq, a , larWithState dpas q')
    
{- | are the two states in different SCCs of the graph of the automaton

>>> btwsccs exdra (4,7)
True

>>> btwsccs exdra (8,7)
False

-}
btwsccs :: Ord q => DRA q s l -> (q, q) -> Bool
btwsccs dra (q,q') = not $ any (\is -> elem (toNode dra q) is && elem (toNode dra q') is) $ G.scc (graph dra)
    
{- | find an Appearance Record in the given automata with a given state component

>>> larWithState [IAR_optimized.rabin2parity AR.rabin2parity  exdra :: DPA (IAR Int) Char Int] 4
IAR {state = 4, perm = [1,0]}

-}
larWithState :: (Eq q, AR ar) => [DPA (ar q) s l] -> q -> ar q
larWithState dpas q = head $ filter (\lar ->  arstate lar == q) $ concatMap B.keys $ bimap <$> dpas
    
-- | apply a function to both components of a pair
--
-- >>> applytoboth (5+) (1,5)
-- (6,10)
applytoboth :: (a -> b) -> (a,a) -> (b,b)
applytoboth f (x,y) = (f x, f y)
