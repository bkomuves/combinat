
-- | Set partitions.
--
-- See eg. <http://en.wikipedia.org/wiki/Partition_of_a_set>
-- 

module Math.Combinat.Partitions.Set where

--------------------------------------------------------------------------------

import Data.List
import Data.Ord

import System.Random

import Math.Combinat.Sets
import Math.Combinat.Numbers
import Math.Combinat.Helper

--------------------------------------------------------------------------------
-- * The type of set partitions

-- | A partition of the set @[1..n]@ (in standard order)
newtype SetPartition = SetPartition [[Int]] deriving (Eq,Ord,Show,Read)

_standardizeSetPartition :: [[Int]] -> [[Int]]
_standardizeSetPartition = sortBy (comparing myhead) . map sort where
  myhead xs = case xs of
    (x:xs) -> x
    []     -> error "_standardizeSetPartition: empty subset"

fromSetPartition :: SetPartition -> [[Int]]
fromSetPartition (SetPartition zzs) = zzs

toSetPartitionUnsafe :: [[Int]] -> SetPartition
toSetPartitionUnsafe = SetPartition

toSetPartition :: [[Int]] -> SetPartition
toSetPartition zzs = if _isSetPartition zzs
  then SetPartition (_standardizeSetPartition zzs)
  else error "toSetPartition: not a set partition"

_isSetPartition :: [[Int]] -> Bool
_isSetPartition zzs = sort (concat zzs) == [1..n] where 
  n = sum' (map length zzs)

--------------------------------------------------------------------------------
-- * Generating set partitions

-- | Synonym for 'setPartitionsNaive'
setPartitions :: Int -> [SetPartition]
setPartitions = setPartitionsNaive

-- | List all set partitions of @[1..n]@, naive algorithm
setPartitionsNaive :: Int -> [SetPartition]
setPartitionsNaive n = map (SetPartition . _standardizeSetPartition) $ go [1..n] where
  go :: [Int] -> [[[Int]]]
  go []     = [[]]
  go (z:zs) = [ s : rest | k <- [1..n] , s0 <- choose (k-1) zs , let s = z:s0 , rest <- go (zs \\ s) ]

-- | Set partitions are counted by the Bell numbers
countSetPartitions :: Int -> Integer
countSetPartitions = bellNumber 

--------------------------------------------------------------------------------
