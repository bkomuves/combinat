
-- | Creates graphviz @.dot@ files from various structures, for example trees.

module Math.Combinat.Graphviz 
  ( Dot
  , treeDot
  , forestDot
  )
  where

--------------------------------------------------------------------------------

import Data.Tree

import Control.Applicative
import Control.Monad.State
import Data.Traversable (traverse)

import Math.Combinat.Trees.Binary (BinTree, BinTree')
import Math.Combinat.Trees.Nary (addUniqueLabelsTree, addUniqueLabelsForest)

--------------------------------------------------------------------------------

type Dot = String

digraphBracket :: String -> [String] -> String   
digraphBracket name lines = 
  "digraph " ++ name ++ " {\n" ++ 
  concatMap (\xs -> "  "++xs++"\n") lines    
  ++ "}\n"
    
-- | Generates graphviz @.dot@ file from a forest. The first argument tells whether
-- to make the individual trees clustered subgraphs; the second is the name of the
-- graph.
forestDot :: Show a => Bool -> String -> Forest a -> Dot
forestDot clustered graphname forest = digraphBracket graphname lines where
  lines = concat $ zipWith cluster [(1::Int)..] (addUniqueLabelsForest forest) 
  name unique = "node_"++show unique
  cluster j tree = let treelines = worker (0::Int) tree in case clustered of
    False -> treelines
    True  -> ("subgraph cluster_"++show j++" {") : map ("  "++) treelines ++ ["}"] 
  worker depth (Node (label,unique) subtrees) = vertex : edges ++ concatMap (worker (depth+1)) subtrees where
    vertex = name unique ++ "[label=\"" ++ show label ++ "\"" ++ "];"
    edges = map edge subtrees
    edge (Node (_,unique') _) = name unique ++ " -> " ++ name unique'   
  
-- | Generates graphviz @.dot@ file from a tree. The first argument is
-- the name of the graph.
treeDot :: Show a => String -> Tree a -> Dot
treeDot graphname tree = digraphBracket graphname $ worker (0::Int) (addUniqueLabelsTree tree) where
  name unique = "node_"++show unique
  worker depth (Node (label,unique) subtrees) = vertex : edges ++ concatMap (worker (depth+1)) subtrees where
    vertex = name unique ++ "[label=\"" ++ show label ++ "\"" ++ "];"
    edges = map edge subtrees
    edge (Node (_,unique') _) = name unique ++ " -> " ++ name unique'

--------------------------------------------------------------------------------
