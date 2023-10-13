
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

{-# LANGUAGE CPP, BangPatterns, ScopedTypeVariables #-}
module Math.Combinat.Partitions.Integer 
  ( -- module Math.Combinat.Partitions.Integer.Count
    module Math.Combinat.Partitions.Integer.Naive
    -- * Types and basic stuff
  , Partition
    -- * Conversion to\/from lists
  , fromPartition 
  , mkPartition 
  , toPartition 
  , toPartitionUnsafe 
  , isPartition 
    -- * Conversion to\/from exponent vectors
  , toExponentVector
  , fromExponentVector
  , dropTailingZeros
    -- * Union and sum
  , unionOfPartitions
  , sumOfPartitions
    -- * Generating partitions
  , partitions 
  , partitions'
  , allPartitions 
  , allPartitionsGrouped 
  , allPartitions'  
  , allPartitionsGrouped'  
    -- * Counting partitions
  , countPartitions
  , countPartitions'
  , countAllPartitions
  , countAllPartitions'
  , countPartitionsWithKParts 
    -- * Random partitions
  , randomPartition
  , randomPartitions
    -- * Dominating \/ dominated partitions
  , dominanceCompare
  , dominatedPartitions 
  , dominatingPartitions 
    -- * Conjugate lexicographic ordering
  , conjugateLexicographicCompare 
  , ConjLex (..) , fromConjLex 
    -- * Partitions with given number of parts
  , partitionsWithKParts
    -- * Partitions with only odd\/distinct parts
  , partitionsWithOddParts 
  , partitionsWithDistinctParts
    -- * Sub- and super-partitions of a given partition
  , subPartitions 
  , allSubPartitions 
  , superPartitions 
    -- * ASCII Ferrers diagrams
  , PartitionConvention(..)
  , asciiFerrersDiagram 
  , asciiFerrersDiagram'
  )
  where

--------------------------------------------------------------------------------

import Data.List
import Control.Monad ( liftM , replicateM )

-- import Data.Map (Map)
-- import qualified Data.Map as Map

import Math.Combinat.Classes
import Math.Combinat.ASCII as ASCII
import Math.Combinat.Numbers (factorial,binomial,multinomial)
import Math.Combinat.Helper

import Data.Array
import System.Random

import Math.Combinat.Partitions.Integer.Naive hiding ()    -- this is for haddock!
import Math.Combinat.Partitions.Integer.IntList
import Math.Combinat.Partitions.Integer.Count

---------------------------------------------------------------------------------
-- * Conversion to\/from lists

fromPartition :: Partition -> [Int]
fromPartition (Partition_ part) = part
  
-- | Sorts the input, and cuts the nonpositive elements.
mkPartition :: [Int] -> Partition
mkPartition xs = toPartitionUnsafe $ sortBy (reverseCompare) $ filter (>0) xs

-- | Checks whether the input is an integer partition. See the note at 'isPartition'!
toPartition :: [Int] -> Partition
toPartition xs = if isPartition xs
  then toPartitionUnsafe xs
  else error "toPartition: not a partition"

-- | Assumes that the input is decreasing.
toPartitionUnsafe :: [Int] -> Partition
toPartitionUnsafe = Partition_
  
-- | This returns @True@ if the input is non-increasing sequence of 
-- /positive/ integers (possibly empty); @False@ otherwise.
--
isPartition :: [Int] -> Bool
isPartition []  = True
isPartition [x] = x > 0
isPartition (x:xs@(y:_)) = (x >= y) && isPartition xs

--------------------------------------------------------------------------------
-- * Conversion to\/from exponent vectors
     
-- | Converts a partition to an exponent vector.
--
-- For example, 
--
-- > toExponentVector (Partition [4,4,2,2,2,1]) == [1,3,0,2]
--
-- meaning @(1^1,2^3,3^0,4^2)@.
--
toExponentVector :: Partition -> [Int]
toExponentVector part = fun 1 $ reverse $ group (fromPartition part) where
  fun _  [] = []
  fun !k gs@(this@(i:_):rest) 
    | k < i      = replicate (i-k) 0 ++ fun i gs
    | otherwise  = length this : fun (k+1) rest

fromExponentVector :: [Int] -> Partition
fromExponentVector expos = Partition $ concat $ reverse $ zipWith f [1..] expos where
  f !i !e = replicate e i

dropTailingZeros :: [Int] -> [Int]
dropTailingZeros = reverse . dropWhile (==0) . reverse

{-
-- alternative implementation
toExponentialVector2 :: Partition -> [Int]
toExponentialVector2 p = go 1 (toExponentialForm p) where
  go _  []              = []
  go !i ef@((j,e):rest) = if i<j 
    then 0 : go (i+1) ef
    else e : go (i+1) rest
-}

--------------------------------------------------------------------------------
-- * Union and sum

-- | This is simply the union of parts. For example 
--
-- > Partition [4,2,1] `unionOfPartitions` Partition [4,3,1] == Partition [4,4,3,2,1,1]
--
-- Note: This is the dual of pointwise sum, 'sumOfPartitions'
--
unionOfPartitions :: Partition -> Partition -> Partition 
unionOfPartitions (Partition_ xs) (Partition_ ys) = mkPartition (xs ++ ys)

-- | Pointwise sum of the parts. For example:
--
-- > Partition [3,2,1,1] `sumOfPartitions` Partition [4,3,1] == Partition [7,5,2,1]
--
-- Note: This is the dual of 'unionOfPartitions'
--
sumOfPartitions :: Partition -> Partition -> Partition 
sumOfPartitions (Partition_ xs) (Partition_ ys) = Partition_ (longZipWith 0 0 (+) xs ys)

--------------------------------------------------------------------------------
-- * Generating partitions

-- | Partitions of @d@.
partitions :: Int -> [Partition]
partitions = map toPartitionUnsafe . _partitions

-- | Partitions of d, fitting into a given rectangle. The order is again lexicographic.
partitions'  
  :: (Int,Int)     -- ^ (height,width)
  -> Int           -- ^ d
  -> [Partition]
partitions' hw d = map toPartitionUnsafe $ _partitions' hw d        

--------------------------------------------------------------------------------

-- | All integer partitions up to a given degree (that is, all integer partitions whose sum is less or equal to @d@)
allPartitions :: Int -> [Partition]
allPartitions d = concat [ partitions i | i <- [0..d] ]

-- | All integer partitions up to a given degree (that is, all integer partitions whose sum is less or equal to @d@),
-- grouped by weight
allPartitionsGrouped :: Int -> [[Partition]]
allPartitionsGrouped d = [ partitions i | i <- [0..d] ]

-- | All integer partitions fitting into a given rectangle.
allPartitions'  
  :: (Int,Int)        -- ^ (height,width)
  -> [Partition]
allPartitions' (h,w) = concat [ partitions' (h,w) i | i <- [0..d] ] where d = h*w

-- | All integer partitions fitting into a given rectangle, grouped by weight.
allPartitionsGrouped'  
  :: (Int,Int)        -- ^ (height,width)
  -> [[Partition]]
allPartitionsGrouped' (h,w) = [ partitions' (h,w) i | i <- [0..d] ] where d = h*w


---------------------------------------------------------------------------------
-- * Random partitions

-- | Uniformly random partition of the given weight. 
--
-- NOTE: This algorithm is effective for small @n@-s (say @n@ up to a few hundred \/ one thousand it should work nicely),
-- and the first time it is executed may be slower (as it needs to build the table of partitions counts first)
--
-- Algorithm of Nijenhuis and Wilf (1975); see
--
-- * Knuth Vol 4A, pre-fascicle 3B, exercise 47;
--
-- * Nijenhuis and Wilf: Combinatorial Algorithms for Computers and Calculators, chapter 10
--
randomPartition :: RandomGen g => Int -> g -> (Partition, g)
randomPartition n g = (p, g') where
  ([p], g') = randomPartitions 1 n g

-- | Generates several uniformly random partitions of @n@ at the same time.
-- Should be a little bit faster then generating them individually.
--
randomPartitions 
  :: forall g. RandomGen g 
  => Int   -- ^ number of partitions to generate
  -> Int   -- ^ the weight of the partitions
  -> g -> ([Partition], g)
randomPartitions howmany n = runRand $ replicateM howmany (worker n []) where

  cnt = countPartitions
 
  finish :: [(Int,Int)] -> Partition
  finish = mkPartition . concatMap f where f (j,d) = replicate j d

  fi :: Int -> Integer 
  fi = fromIntegral

  find_jd :: Int -> Integer -> (Int,Int)
  find_jd m capm = go 0 [ (j,d) | j<-[1..n], d<-[1..div m j] ] where
    go :: Integer -> [(Int,Int)] -> (Int,Int)
    go !s []   = (1,1)       -- ??
    go !s [jd] = jd          -- ??
    go !s (jd@(j,d):rest) = 
      if s' > capm 
        then jd 
        else go s' rest
      where
        s' = s + fi d * cnt (m - j*d)

  worker :: Int -> [(Int,Int)] -> Rand g Partition
  worker  0 acc = return $ finish acc
  worker !m acc = do
    capm <- randChoose (0, (fi m) * cnt m - 1)
    let jd@(!j,!d) = find_jd m capm
    worker (m - j*d) (jd:acc)

--------------------------------------------------------------------------------
-- * Dominating \/ dominated partitions

-- | Dominance partial ordering as a partial ordering.
dominanceCompare :: Partition -> Partition -> Maybe Ordering
dominanceCompare p q  
  | p==q             = Just EQ
  | p `dominates` q  = Just GT
  | q `dominates` p  = Just LT
  | otherwise        = Nothing

-- | Lists all partitions of the same weight as @lambda@ and also dominated by @lambda@
-- (that is, all partial sums are less or equal):
--
-- > dominatedPartitions lam == [ mu | mu <- partitions (weight lam), lam `dominates` mu ]
-- 
dominatedPartitions :: Partition -> [Partition]    
dominatedPartitions (Partition_ lambda) = map Partition_ (_dominatedPartitions lambda)

-- | Lists all partitions of the sime weight as @mu@ and also dominating @mu@
-- (that is, all partial sums are greater or equal):
--
-- > dominatingPartitions mu == [ lam | lam <- partitions (weight mu), lam `dominates` mu ]
-- 
dominatingPartitions :: Partition -> [Partition]    
dominatingPartitions (Partition_ mu) = map Partition_ (_dominatingPartitions mu)

--------------------------------------------------------------------------------
-- * Conjugate lexicographic ordering

conjugateLexicographicCompare :: Partition -> Partition -> Ordering
conjugateLexicographicCompare p q = compare (dualPartition q) (dualPartition p) 

newtype ConjLex = ConjLex Partition deriving (Eq,Show)

fromConjLex :: ConjLex -> Partition
fromConjLex (ConjLex p) = p

instance Ord ConjLex where
  compare (ConjLex p) (ConjLex q) = conjugateLexicographicCompare p q

-- {- CONJUGATE LEXICOGRAPHIC ordering is a refinement of dominance partial ordering -}
-- let test n = [ ConjLex p >= ConjLex q | p <- partitions n , q <-partitions n ,  p `dominates` q ]
-- and (test 20)

-- {- LEXICOGRAPHIC ordering is a refinement of dominance partial ordering -}
-- let test n = [ p >= q | p <- partitions n , q <-partitions n ,  p `dominates` q ]
-- and (test 20)

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
partitionsWithKParts k n = map Partition_ $ go n k n where
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

--------------------------------------------------------------------------------
-- * Partitions with only odd\/distinct parts

-- | Partitions of @n@ with only odd parts
partitionsWithOddParts :: Int -> [Partition]
partitionsWithOddParts d = map Partition_ (go d d) where
  go _  0  = [[]]
  go !h !n = [ a:as | a<-[1,3..min n h], as <- go a (n-a) ]

{-
-- | Partitions of @n@ with only even parts
--
-- Note: this is not very interesting, it's just @(map.map) (2*) $ _partitions (div n 2)@
--
partitionsWithEvenParts :: Int -> [Partition]
partitionsWithEvenParts d = map Partition (go d d) where
  go _  0  = [[]]
  go !h !n = [ a:as | a<-[2,4..min n h], as <- go a (n-a) ]
-}

-- | Partitions of @n@ with distinct parts.
-- 
-- Note:
--
-- > length (partitionsWithDistinctParts d) == length (partitionsWithOddParts d)
--
partitionsWithDistinctParts :: Int -> [Partition]
partitionsWithDistinctParts d = map Partition_ (go d d) where
  go _  0  = [[]]
  go !h !n = [ a:as | a<-[1..min n h], as <- go (a-1) (n-a) ]

--------------------------------------------------------------------------------
-- * Sub- and super-partitions of a given partition

-- | Sub-partitions of a given partition with the given weight:
--
-- > sort (subPartitions d q) == sort [ p | p <- partitions d, isSubPartitionOf p q ]
--
subPartitions :: Int -> Partition -> [Partition]
subPartitions d (Partition_ ps) = map Partition_ (_subPartitions d ps)

-- | All sub-partitions of a given partition
allSubPartitions :: Partition -> [Partition]
allSubPartitions (Partition_ ps) = map Partition_ (_allSubPartitions ps)

-- | Super-partitions of a given partition with the given weight:
--
-- > sort (superPartitions d p) == sort [ q | q <- partitions d, isSubPartitionOf p q ]
--
superPartitions :: Int -> Partition -> [Partition]
superPartitions d (Partition_ ps) = map toPartitionUnsafe (_superPartitions d ps)
    

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

instance DrawASCII Partition where
  ascii = asciiFerrersDiagram

--------------------------------------------------------------------------------

