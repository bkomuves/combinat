
-- | Partitions. Partitions are nonincreasing sequences of positive integers.

module Math.Combinat.Partitions
  ( -- * Type and basic stuff
    Partition
  , toPartition
  , toPartitionUnsafe
  , mkPartition
  , isPartition
  , fromPartition
  , height
  , width
  , heightWidth
  , weight
  , _dualPartition
  , dualPartition
    -- * Generation
  , _partitions' 
  , partitions'  
  , countPartitions'
  , _partitions
  , partitions
  , countPartitions
  , allPartitions'  
  , allPartitions 
  , countAllPartitions'
  , countAllPartitions
  ) 
  where

import Data.List
import Math.Combinat.Helper

-------------------------------------------------------

-- | The additional invariant enforced here is that partitions 
--   are monotone decreasing sequences of positive integers.
newtype Partition = Partition [Int] deriving (Eq,Ord,Show,Read)

-- | Sorts the input.
mkPartition :: [Int] -> Partition
mkPartition xs = Partition $ sortBy (reverseCompare) $ filter (>0) xs

-- | Assumes that the input is decreasing.
toPartitionUnsafe :: [Int] -> Partition
toPartitionUnsafe = Partition

-- | Checks whether the input is a partition.
toPartition :: [Int] -> Partition
toPartition xs = if isPartition xs
  then toPartitionUnsafe xs
  else error "toPartition: not a partition"
  
isPartition :: [Int] -> Bool
isPartition []  = True
isPartition [_] = True
isPartition (x:xs@(y:_)) = (x >= y) && isPartition xs

fromPartition :: Partition -> [Int]
fromPartition (Partition part) = part

-- | The first element of the sequence.
height :: Partition -> Int
height (Partition part) = case part of
  (p:_) -> p
  [] -> 0
  
-- | The length of the sequence.
width :: Partition -> Int
width (Partition part) = length part

heightWidth :: Partition -> (Int,Int)
heightWidth part = (height part, width part)

-- | The weight of the partition 
--   (that is, the sum of the corresponding sequence).
weight :: Partition -> Int
weight (Partition part) = sum part

-- | The dual (or conjugate) partition.
dualPartition :: Partition -> Partition
dualPartition (Partition part) = Partition (_dualPartition part)

-- (we could be more efficient, but it hardly matters)
_dualPartition :: [Int] -> [Int]
_dualPartition [] = []
_dualPartition xs@(k:_) = [ length $ filter (>=i) xs | i <- [1..k] ]
  
-------------------------------------------------------

-- | Partitions of d, fitting into a given rectangle, as lists.
_partitions' 
  :: (Int,Int)     -- ^ (height,width)
  -> Int           -- ^ d
  -> [[Int]]        
_partitions' _ 0 = [[]] 
_partitions' (0,_) d = if d==0 then [[]] else []
_partitions' (_,0) d = if d==0 then [[]] else []
_partitions' (h,w) d = 
  [ i:xs | i <- [1..min d h] , xs <- _partitions' (i,w-1) (d-i) ]

-- | Partitions of d, fitting into a given rectangle. The order is again lexicographic.
partitions'  
  :: (Int,Int)     -- ^ (height,width)
  -> Int           -- ^ d
  -> [Partition]
partitions' hw d = map toPartitionUnsafe $ _partitions' hw d        

countPartitions' :: (Int,Int) -> Int -> Integer
countPartitions' _ 0 = 1
countPartitions' (0,_) d = if d==0 then 1 else 0
countPartitions' (_,0) d = if d==0 then 1 else 0
countPartitions' (h,w) d = sum
  [ countPartitions' (i,w-1) (d-i) | i <- [1..min d h] ] 

-- | Partitions of d, as lists
_partitions :: Int -> [[Int]]
_partitions d = _partitions' (d,d) d

-- | Partitions of d.
partitions :: Int -> [Partition]
partitions d = partitions' (d,d) d

countPartitions :: Int -> Integer
countPartitions d = countPartitions' (d,d) d

-- | All partitions fitting into a given rectangle.
allPartitions'  
  :: (Int,Int)        -- ^ (height,width)
  -> [[Partition]]
allPartitions' (h,w) = [ partitions' (h,w) i | i <- [0..d] ] where d = h*w

-- | All partitions up to a given degree.
allPartitions :: Int -> [[Partition]]
allPartitions d = [ partitions i | i <- [0..d] ]

-- | # = \\binom { h+w } { h }
countAllPartitions' :: (Int,Int) -> Integer
countAllPartitions' (h,w) = 
  binomial (h+w) (min h w)
  --sum [ countPartitions' (h,w) i | i <- [0..d] ] where d = h*w

countAllPartitions :: Int -> Integer
countAllPartitions d = sum [ countPartitions i | i <- [0..d] ]

-------------------------------------------------------

