
module Math.Combinat.Trees.Nary where

--------------------------------------------------------------------------------

import Data.Tree

--------------------------------------------------------------------------------

addUniqueLabelsTree   :: Tree   a -> Tree   (a,Int) 
addUniqueLabelsForest :: Forest a -> Forest (a,Int) 

addUniqueLabelsTree_   :: Tree   a -> Tree   Int
addUniqueLabelsForest_ :: Forest a -> Forest Int

--------------------------------------------------------------------------------
