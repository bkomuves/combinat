
-- | N-ary trees.

module Math.Combinat.Trees.Nary 
  ( 
    derivTrees
    -- * unique labels
  , addUniqueLabelsTree
  , addUniqueLabelsForest
  , addUniqueLabelsTree_
  , addUniqueLabelsForest_
    -- * labelling by depth
  , labelDepthTree
  , labelDepthForest
  , labelDepthTree_
  , labelDepthForest_
  ) where


--------------------------------------------------------------------------------

import Data.Tree

import Control.Applicative
import Control.Monad.State
import Data.Traversable (traverse)

import Math.Combinat.Sets (listTensor)
import Math.Combinat.Partitions (partitionMultiset)

--------------------------------------------------------------------------------

-- | Adds unique labels to a 'Tree'.
addUniqueLabelsTree :: Tree a -> Tree (a,Int) 
addUniqueLabelsTree tree = head (addUniqueLabelsForest [tree])

-- | Adds unique labels to a 'Forest'
addUniqueLabelsForest :: Forest a -> Forest (a,Int) 
addUniqueLabelsForest forest = evalState (mapM globalAction forest) 1 where
  globalAction tree = 
    unwrapMonad $ traverse localAction tree 
  localAction x = WrapMonad $ do
    i <- get
    put (i+1)
    return (x,i)

addUniqueLabelsTree_ :: Tree a -> Tree Int
addUniqueLabelsTree_ = fmap snd . addUniqueLabelsTree  

addUniqueLabelsForest_ :: Forest a -> Forest Int
addUniqueLabelsForest_ = map (fmap snd) . addUniqueLabelsForest
    
-- | Attaches the depth to each node. The depth of the root is 0. 
labelDepthTree :: Tree a -> Tree (a,Int) 
labelDepthTree tree = worker 0 tree where
  worker depth (Node label subtrees) = Node (label,depth) (map (worker (depth+1)) subtrees)

labelDepthForest :: Forest a -> Forest (a,Int) 
labelDepthForest forest = map labelDepthTree forest
    
labelDepthTree_ :: Tree a -> Tree Int
labelDepthTree_ = fmap snd . labelDepthTree

labelDepthForest_ :: Forest a -> Forest Int 
labelDepthForest_ = map (fmap snd) . labelDepthForest
    
--------------------------------------------------------------------------------

-- | Computes the set of equivalence classes of trees (in the 
-- sense that the leaves of a node are /unordered/) 
-- with @n = length ks@ leaves where the set of heights of 
-- the leaves matches the given set of numbers. 
-- The height is defined as the number of /edges/ from the leaf to the root. 
--
-- TODO: better name?
derivTrees :: [Int] -> [Tree ()]
derivTrees xs = derivTrees' (map (+1) xs)

derivTrees' :: [Int] -> [Tree ()]
derivTrees' [] = []
derivTrees' [n] = 
  if n>=1 
    then [unfoldTree f 1] 
    else [] 
  where 
    f k = if k<n then ((),[k+1]) else ((),[])
derivTrees' ks = 
  if and (map (>0) ks)
    then
      [ Node () sub 
      | part <- parts
      , let subtrees = map g part
      , sub <- listTensor subtrees 
      ] 
    else []
  where
    parts = partitionMultiset ks
    g xs = derivTrees' (map (\x->x-1) xs)

--------------------------------------------------------------------------------
    