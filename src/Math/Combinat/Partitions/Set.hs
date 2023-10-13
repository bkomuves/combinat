
-- | Set partitions.
--
-- See eg. <http://en.wikipedia.org/wiki/Partition_of_a_set>
-- 

{-# LANGUAGE BangPatterns #-}
module Math.Combinat.Partitions.Set where

--------------------------------------------------------------------------------

import Data.List
import Data.Ord

import System.Random

import Math.Combinat.Sets
import Math.Combinat.Numbers
import Math.Combinat.Helper
import Math.Combinat.Classes
import Math.Combinat.Partitions.Integer

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

instance HasNumberOfParts SetPartition where
  numberOfParts (SetPartition p) = length p

--------------------------------------------------------------------------------
-- * Forgetting the set structure

-- | The \"shape\" of a set partition is the partition we get when we forget the
-- set structure, keeping only the cardinalities.
--
setPartitionShape :: SetPartition -> Partition
setPartitionShape (SetPartition pps) = mkPartition (map length pps)

--------------------------------------------------------------------------------
-- * Generating set partitions

-- | Synonym for 'setPartitionsNaive'
setPartitions :: Int -> [SetPartition]
setPartitions = setPartitionsNaive

-- | Synonym for 'setPartitionsWithKPartsNaive'
--
-- > sort (setPartitionsWithKParts k n) == sort [ p | p <- setPartitions n , numberOfParts p == k ]
-- 
setPartitionsWithKParts   
  :: Int    -- ^ @k@ = number of parts
  -> Int    -- ^ @n@ = size of the set
  -> [SetPartition]
setPartitionsWithKParts = setPartitionsWithKPartsNaive

-- | List all set partitions of @[1..n]@, naive algorithm
setPartitionsNaive :: Int -> [SetPartition]
setPartitionsNaive n = map (SetPartition . _standardizeSetPartition) $ go [1..n] where
  go :: [Int] -> [[[Int]]]
  go []     = [[]]
  go (z:zs) = [ s : rest | k <- [1..n] , s0 <- choose (k-1) zs , let s = z:s0 , rest <- go (zs \\ s) ]

-- | Set partitions of the set @[1..n]@ into @k@ parts
setPartitionsWithKPartsNaive 
  :: Int    -- ^ @k@ = number of parts
  -> Int    -- ^ @n@ = size of the set
  -> [SetPartition]
setPartitionsWithKPartsNaive k n = map (SetPartition . _standardizeSetPartition) $ go k [1..n] where
  go :: Int -> [Int] -> [[[Int]]]
  go !k []     = if k==0 then [[]] else []
  go  1 zs     = [[zs]]
  go !k (z:zs) = [ s : rest | l <- [1..n] , s0 <- choose (l-1) zs , let s = z:s0 , rest <- go (k-1) (zs \\ s) ]


-- | Set partitions are counted by the Bell numbers
countSetPartitions :: Int -> Integer
countSetPartitions = bellNumber 

-- | Set partitions of size @k@ are counted by the Stirling numbers of second kind
countSetPartitionsWithKParts 
  :: Int    -- ^ @k@ = number of parts
  -> Int    -- ^ @n@ = size of the set
  -> Integer
countSetPartitionsWithKParts k n = stirling2nd n k

--------------------------------------------------------------------------------
