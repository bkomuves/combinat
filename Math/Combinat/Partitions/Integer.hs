
-- | Partitions of integers.
-- Integer partitions are nonincreasing sequences of positive integers.
--
-- See:
--
--  * Donald E. Knuth: The Art of Computer Programming, vol 4, pre-fascicle 3B.
--
--  * <http://en.wikipedia.org/wiki/Partition_(number_theory)>
--

{-# LANGUAGE BangPatterns #-}
module Math.Combinat.Partitions.Integer where

--------------------------------------------------------------------------------

import Data.List

import Math.Combinat.Helper
import Math.Combinat.Numbers (factorial,binomial,multinomial)

--------------------------------------------------------------------------------
-- * Type and basic stuff

-- | A partition of an integer. The additional invariant enforced here is that partitions 
--   are monotone decreasing sequences of positive integers.
newtype Partition = Partition [Int] deriving (Eq,Ord,Show,Read)

---------------------------------------------------------------------------------

class HasNumberOfParts p where
  numberOfParts :: p -> Int

instance HasNumberOfParts Partition where
  numberOfParts (Partition p) = length p

---------------------------------------------------------------------------------
  
-- | Sorts the input, and cuts the nonpositive elements.
mkPartition :: [Int] -> Partition
mkPartition xs = Partition $ sortBy (reverseCompare) $ filter (>0) xs

-- | Assumes that the input is decreasing.
toPartitionUnsafe :: [Int] -> Partition
toPartitionUnsafe = Partition

-- | Checks whether the input is an integer partition. See the note at 'isPartition'!
toPartition :: [Int] -> Partition
toPartition xs = if isPartition xs
  then toPartitionUnsafe xs
  else error "toPartition: not a partition"
  
-- | Note: we only check that the sequence is ordered, but we /do not/ check for
-- negative elements. This can be useful when working with symmetric functions.
-- It may also change in the future...
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
weight (Partition part) = sum' part

-- | The dual (or conjugate) partition.
dualPartition :: Partition -> Partition
dualPartition (Partition part) = Partition (_dualPartition part)

-- (we could be more efficient, but it hardly matters)
_dualPartition :: [Int] -> [Int]
_dualPartition [] = []
_dualPartition xs@(k:_) = [ length $ filter (>=i) xs | i <- [1..k] ]

-- | Example:
--
-- > elements (toPartition [5,4,1]) ==
-- > [ (1,1), (1,2), (1,3), (1,4), (1,5)
-- > , (2,1), (2,2), (2,3), (2,4)
-- > , (3,1)
-- > ]
elements :: Partition -> [(Int,Int)]
elements (Partition part) = _elements part

_elements :: [Int] -> [(Int,Int)]
_elements shape = [ (i,j) | (i,l) <- zip [1..] shape, j<-[1..l] ] 

-- | Computes the number of \"automorphisms\" of a given integer partition.
countAutomorphisms :: Partition -> Integer  
countAutomorphisms = _countAutomorphisms . fromPartition

_countAutomorphisms :: [Int] -> Integer
_countAutomorphisms = multinomial . map length . group

---------------------------------------------------------------------------------
-- * Generating partitions

-- | Integer partitions of @d@, fitting into a given rectangle, as lists.
_partitions' 
  :: (Int,Int)     -- ^ (height,width)
  -> Int           -- ^ d
  -> [[Int]]        
_partitions' _ 0 = [[]] 
_partitions' ( 0 , _) d = if d==0 then [[]] else []
_partitions' ( _ , 0) d = if d==0 then [[]] else []
_partitions' (!h ,!w) d = 
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

-- | Partitions of @d@, as lists
_partitions :: Int -> [[Int]]
_partitions d = _partitions' (d,d) d

-- | Partitions of @d@.
partitions :: Int -> [Partition]
partitions d = partitions' (d,d) d

countPartitions :: Int -> Integer
countPartitions d = countPartitions' (d,d) d

-- | All integer partitions fitting into a given rectangle.
allPartitions'  
  :: (Int,Int)        -- ^ (height,width)
  -> [[Partition]]
allPartitions' (h,w) = [ partitions' (h,w) i | i <- [0..d] ] where d = h*w

-- | All integer partitions up to a given degree (that is, all integer partitions whose sum is less or equal to @d@)
allPartitions :: Int -> [[Partition]]
allPartitions d = [ partitions i | i <- [0..d] ]

-- | # = \\binom { h+w } { h }
countAllPartitions' :: (Int,Int) -> Integer
countAllPartitions' (h,w) = 
  binomial (h+w) (min h w)
  --sum [ countPartitions' (h,w) i | i <- [0..d] ] where d = h*w

countAllPartitions :: Int -> Integer
countAllPartitions d = sum' [ countPartitions i | i <- [0..d] ]

--------------------------------------------------------------------------------
-- partitions with given number of parts

-- | Lists partitions of @n@ into @k@ parts.
--
-- > sort (partitionsWithKParts k n) == sort [ p | p <- partitions n , numberOfParts p == k ]
--
-- Naive recursive algorithm.
--
partitionsWithKParts 
  :: Int    -- ^ @k@ = number of parts
  -> Int    -- ^ @n@ = the integer we partition
  -> [Partition]
partitionsWithKParts k n = map Partition $ go n k n where
{-
  h = max height
  k = number of parts
  n = integer
-}
  go !h !k !n 
    | k <  0     = []
    | k == 0     = if h>=0 && n==0 then [[] ] else []
    | k == 1     = if h>=n && n>=1 then [[n]] else []
    | otherwise  = [ a:p | a <- [1..(min h (n-k+1))] , p <- go a (k-1) (n-a) ]

countPartitionsWithKParts 
  :: Int    -- ^ @k@ = number of parts
  -> Int    -- ^ @n@ = the integer we partition
  -> Integer
countPartitionsWithKParts k n = go n k n where
  go !h !k !n 
    | k <  0     = 0
    | k == 0     = if h>=0 && n==0 then 1 else 0
    | k == 1     = if h>=n && n>=1 then 1 else 0
    | otherwise  = sum' [ go a (k-1) (n-a) | a<-[1..(min h (n-k+1))] ]


--------------------------------------------------------------------------------
-- * ASCII Ferrer diagrams

printFerrerDiagram :: Partition -> IO ()
printFerrerDiagram = putStrLn . ferrerDiagram

-- | Synonym for 'ferrerDiagramEnglishNotation'
ferrerDiagram :: Partition -> String
ferrerDiagram = ferrerDiagramEnglishNotation

ferrerDiagramEnglishNotation :: Partition -> String
ferrerDiagramEnglishNotation = ferrerDiagramEnglishNotation' '@'

ferrerDiagramFrenchNotation :: Partition -> String
ferrerDiagramFrenchNotation  = ferrerDiagramFrenchNotation'  '@'

ferrerDiagramEnglishNotation' :: Char -> Partition -> String
ferrerDiagramEnglishNotation' ch part = unlines (map f ys) where
  ys  = fromPartition part
  f n = replicate n ch 

ferrerDiagramFrenchNotation' :: Char -> Partition -> String
ferrerDiagramFrenchNotation' ch part = unlines (map f ys) where
  ys  = reverse $ fromPartition $ dualPartition part
  f n = replicate n ch 

--------------------------------------------------------------------------------
