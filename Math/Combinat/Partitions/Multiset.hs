
-- | Partitions of a multiset
module Math.Combinat.Partitions.Multiset where

--------------------------------------------------------------------------------

import Data.Array.Unboxed
import Data.List

import Math.Combinat.Partitions.Vector

--------------------------------------------------------------------------------
                              
-- | Partitions of a multiset. Internally, this uses the vector partition algorithm
partitionMultiset :: (Eq a, Ord a) => [a] -> [[[a]]]
partitionMultiset xs = parts where
  parts = (map . map) (f . elems) temp
  f ns = concat (zipWith replicate ns zs)
  temp = fasc3B_algorithm_M counts
  counts = map length ys
  ys = group (sort xs) 
  zs = map head ys

--------------------------------------------------------------------------------