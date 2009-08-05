
-- | Creates graphviz @.dot@ files from various structures, for example trees.

module Math.Combinat.Graphviz 
  ( Dot
  , binTreeDot
  , binTree'Dot
  , treeDot
  , forestDot
  )
  where

--------------------------------------------------------------------------------

import Data.Tree

import Control.Applicative
import Control.Monad.State
import Data.Traversable (traverse)

import Math.Combinat.Trees.Binary (BinTree(..), BinTree'(..))
import Math.Combinat.Trees.Nary (addUniqueLabelsTree, addUniqueLabelsForest)

--------------------------------------------------------------------------------

type Dot = String

digraphBracket :: String -> [String] -> String   
digraphBracket name lines = 
  "digraph " ++ name ++ " {\n" ++ 
  concatMap (\xs -> "  "++xs++"\n") lines    
  ++ "}\n"
  
--------------------------------------------------------------------------------

binTreeDot :: Show a => String -> BinTree a -> Dot
binTreeDot graphname tree = 
  digraphBracket graphname $ binTreeDot' tree

binTree'Dot :: (Show a, Show b) => String -> BinTree' a b -> Dot
binTree'Dot graphname tree = 
  digraphBracket graphname $ binTree'Dot' tree
  
binTreeDot' :: Show a => BinTree a -> [String]
binTreeDot' tree = lines where
  lines = worker (0::Int) "r" tree 
  name path = "node_"++path
  worker depth path (Leaf x) = 
    [ name path ++ "[shape=box,label=\"" ++ show x ++ "\"" ++ "];" ]
  worker depth path (Branch left right) 
    = [vertex,leftedge,rightedge] ++ 
      worker (depth+1) ('l':path) left ++ 
      worker (depth+1) ('r':path) right
    where 
      vertex = name path ++ "[shape=circle,style=filled,height=0.25,label=\"\"];"
      leftedge  = name path ++ " -> " ++ name ('l':path) ++ "[tailport=sw];"
      rightedge = name path ++ " -> " ++ name ('r':path) ++ "[tailport=se];"

binTree'Dot' :: (Show a, Show b) => BinTree' a b -> [String]
binTree'Dot' tree = lines where
  lines = worker (0::Int) "r" tree 
  name path = "node_"++path
  worker depth path (Leaf' x) = 
    [ name path ++ "[shape=box,label=\"" ++ show x ++ "\"" ++ "];" ]
  worker depth path (Branch' left y right) 
    = [vertex,leftedge,rightedge] ++ 
      worker (depth+1) ('l':path) left ++ 
      worker (depth+1) ('r':path) right
    where 
      vertex = name path ++ "[shape=ellipse,label=\"" ++ show y ++ "\"];"
      leftedge  = name path ++ " -> " ++ name ('l':path) ++ "[tailport=sw];"
      rightedge = name path ++ " -> " ++ name ('r':path) ++ "[tailport=se];"

--------------------------------------------------------------------------------
    
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
treeDot graphname tree = digraphBracket graphname lines where
  lines = worker (0::Int) (addUniqueLabelsTree tree) 
  name unique = "node_"++show unique
  worker depth (Node (label,unique) subtrees) = vertex : edges ++ concatMap (worker (depth+1)) subtrees where
    vertex = name unique ++ "[label=\"" ++ show label ++ "\"" ++ "];"
    edges = map edge subtrees
    edge (Node (_,unique') _) = name unique ++ " -> " ++ name unique'

--------------------------------------------------------------------------------
