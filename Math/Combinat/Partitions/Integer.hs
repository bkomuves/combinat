
-- | Partitions of integers.
-- Integer partitions are nonincreasing sequences of positive integers.
--
-- See:
--
--  * Donald E. Knuth: The Art of Computer Programming, vol 4, pre-fascicle 3B.
--
--  * <http://en.wikipedia.org/wiki/Partition_(number_theory)>
--
-- For example the partition
--
-- > Partition [8,6,3,3,1]
--
-- can be represented by the (English notation) Ferrers diagram:
--
-- <<svg/ferrers.svg>>
-- 

{-# LANGUAGE BangPatterns #-}
module Math.Combinat.Partitions.Integer where

--------------------------------------------------------------------------------

import Data.List

import Math.Combinat.Helper
import Math.Combinat.ASCII as ASCII
import Math.Combinat.Numbers (factorial,binomial,multinomial)

--------------------------------------------------------------------------------
-- * Type and basic stuff

-- | A partition of an integer. The additional invariant enforced here is that partitions 
-- are monotone decreasing sequences of positive integers. The @Ord@ instance is lexicographical.
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
-- >   [ (1,1), (1,2), (1,3), (1,4), (1,5)
-- >   , (2,1), (2,2), (2,3), (2,4)
-- >   , (3,1)
-- >   ]
--
elements :: Partition -> [(Int,Int)]
elements (Partition part) = _elements part

_elements :: [Int] -> [(Int,Int)]
_elements shape = [ (i,j) | (i,l) <- zip [1..] shape, j<-[1..l] ] 

---------------------------------------------------------------------------------
-- * Automorphisms 

-- | Computes the number of \"automorphisms\" of a given integer partition.
countAutomorphisms :: Partition -> Integer  
countAutomorphisms = _countAutomorphisms . fromPartition

_countAutomorphisms :: [Int] -> Integer
_countAutomorphisms = multinomial . map length . group

---------------------------------------------------------------------------------
-- * Dominance order 

-- | @q \`dominates\` p@ returns @True@ if @q >= p@ in the dominance order of partitions
-- (this is partial ordering on the set of partitions of @n@).
--
-- See <http://en.wikipedia.org/wiki/Dominance_order>
--
dominates :: Partition -> Partition -> Bool
dominates (Partition qs) (Partition ps) 
  = and $ zipWith (>=) (sums (qs ++ repeat 0)) (sums ps)
  where
    sums = scanl (+) 0

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
-- * Partitions with given number of parts

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
-- * Sub-partitions of a given partition

-- | Returns @True@ of the first partition is a subpartition (that is, fit inside) of the second.
-- This includes equality
isSubPartitionOf :: Partition -> Partition -> Bool
isSubPartitionOf (Partition ps) (Partition qs) = and $ zipWith (<=) ps (qs ++ repeat 0)

----------------------------------------

-- | Sub-partitions of a given partition with the given weight:
--
-- > sort (subPartitions d q) == sort [ p | p <- partitions d, isSubPartitionOf p q ]
--
subPartitions :: Int -> Partition -> [Partition]
subPartitions d (Partition ps) = map Partition (_subPartitions d ps)

_subPartitions :: Int -> [Int] -> [[Int]]
_subPartitions d big
  | null big       = if d==0 then [[]] else []
  | d > sum' big   = []
  | d < 0          = []
  | otherwise      = go d (head big) big
  where
    go :: Int -> Int -> [Int] -> [[Int]]
    go !k !h []      = if k==0 then [[]] else []
    go !k !h (b:bs) 
      | k<0 || h<0   = []
      | k==0         = [[]]
      | h==0         = []
      | otherwise    = [ this:rest | this <- [1..min h b] , rest <- go (k-this) this bs ]

----------------------------------------

-- | All sub-partitions of a given partition
allSubPartitions :: Partition -> [Partition]
allSubPartitions (Partition ps) = map Partition (_allSubPartitions ps)

_allSubPartitions :: [Int] -> [[Int]]
_allSubPartitions big 
  | null big   = [[]]
  | otherwise  = go (head big) big
  where
    go _  [] = [[]]
    go !h (b:bs) 
      | h==0         = []
      | otherwise    = [] : [ this:rest | this <- [1..min h b] , rest <- go this bs ]

--------------------------------------------------------------------------------
-- * ASCII Ferrers diagrams

-- | Which orientation to draw the Ferrers diagrams.
-- For example, the partition [5,4,1] corrsponds to:
--
-- In standard English notation:
-- 
-- >  @@@@@
-- >  @@@@
-- >  @
--
--
-- In English notation rotated by 90 degrees counter-clockwise:
--
-- > @  
-- > @@
-- > @@
-- > @@
-- > @@@
--
--
-- And in French notation:
--
-- 
-- >  @
-- >  @@@@
-- >  @@@@@
--
--
data PartitionConvention
  = EnglishNotation          -- ^ English notation
  | EnglishNotationCCW       -- ^ English notation rotated by 90 degrees counterclockwise
  | FrenchNotation           -- ^ French notation (mirror of English notation to the x axis)
  deriving (Eq,Show)

-- | Synonym for @asciiFerrersDiagram\' EnglishNotation \'\@\'@
--
-- Try for example:
--
-- > autoTabulate RowMajor (Right 8) (map asciiFerrersDiagram $ partitions 9)
--
asciiFerrersDiagram :: Partition -> ASCII
asciiFerrersDiagram = asciiFerrersDiagram' EnglishNotation '@'

asciiFerrersDiagram' :: PartitionConvention -> Char -> Partition -> ASCII
asciiFerrersDiagram' conv ch part = ASCII.asciiFromLines (map f ys) where
  f n = replicate n ch 
  ys  = case conv of
          EnglishNotation    -> fromPartition part
          EnglishNotationCCW -> reverse $ fromPartition $ dualPartition part
          FrenchNotation     -> reverse $ fromPartition $ part

--------------------------------------------------------------------------------
