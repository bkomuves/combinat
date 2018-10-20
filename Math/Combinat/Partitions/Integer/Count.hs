
-- | Counting partitions of integers.

{-# LANGUAGE CPP, BangPatterns, ScopedTypeVariables #-}
module Math.Combinat.Partitions.Integer.Count where

--------------------------------------------------------------------------------

import Data.List
import Control.Monad ( liftM , replicateM )

-- import Data.Map (Map)
-- import qualified Data.Map as Map

import Math.Combinat.Numbers ( factorial , binomial , multinomial )
import Math.Combinat.Numbers.Integers -- Primes
import Math.Combinat.Helper

import Data.Array
import System.Random

--------------------------------------------------------------------------------
-- * Infinite tables of integers

-- | A data structure which is essentially an infinite list of @Integer@-s,
-- but fast lookup (for reasonable small inputs)
newtype TableOfIntegers = TableOfIntegers [Array Int Integer]

lookupInteger :: TableOfIntegers -> Int -> Integer
lookupInteger (TableOfIntegers table) !n 
  | n >= 0  = (table !! k) ! r
  | n <  0  = 0
  where
    (k,r) = divMod n 1024

makeTableOfIntegers
  :: ((Int -> Integer) -> (Int -> Integer))
  -> TableOfIntegers
makeTableOfIntegers user = table where
  calc  = user lkp
  lkp   = lookupInteger table
  table = TableOfIntegers
    [ listArray (0,1023) (map calc [a..b]) 
    | k<-[0..] 
    , let a = 1024*k 
    , let b = 1024*(k+1) - 1 
    ]

--------------------------------------------------------------------------------
-- * Counting partitions

-- | Number of partitions of @n@ (looking up a table built using Euler's algorithm)
countPartitions :: Int -> Integer
countPartitions = lookupInteger partitionCountTable 

-- | This uses the power series expansion of the infinite product. It is slower than the above.
countPartitionsInfiniteProduct :: Int -> Integer
countPartitionsInfiniteProduct k = partitionCountListInfiniteProduct !! k

-- | This uses 'countPartitions'', and is (very) slow
countPartitionsNaive :: Int -> Integer
countPartitionsNaive d = countPartitions' (d,d) d

--------------------------------------------------------------------------------

-- | This uses Euler's algorithm to compute p(n)
--
-- See eg.:
-- NEIL CALKIN, JIMENA DAVIS, KEVIN JAMES, ELIZABETH PEREZ, AND CHARLES SWANNACK
-- COMPUTING THE INTEGER PARTITION FUNCTION
-- <http://www.math.clemson.edu/~kevja/PAPERS/ComputingPartitions-MathComp.pdf>
--
partitionCountTable :: TableOfIntegers
partitionCountTable = table where

  table = makeTableOfIntegers fun

  fun lkp !n 
    | n >  1 = foldl' (+) 0 
             [ (if even k then negate else id) 
                 ( lkp (n - div (k*(3*k+1)) 2)
                 + lkp (n - div (k*(3*k-1)) 2)
                 )
             | k <- [1..limit n]
             ]
    | n <  0 = 0
    | n == 0 = 1
    | n == 1 = 1

  limit :: Int -> Int
  limit !n = fromInteger $ ceilingSquareRoot (1 + div (nn+nn+1) 3) where
    nn = fromIntegral n :: Integer

-- | An infinite list containing all @p(n)@, starting from @p(0)@.
partitionCountList :: [Integer]
partitionCountList = map countPartitions [0..]

--------------------------------------------------------------------------------

-- | Infinite list of number of partitions of @0,1,2,...@
--
-- This uses the infinite product formula the generating function of partitions, 
-- recursively expanding it; it is reasonably fast for small numbers.
--
-- > partitionCountListInfiniteProduct == map countPartitions [0..]
--
partitionCountListInfiniteProduct :: [Integer]
partitionCountListInfiniteProduct = final where

  final = go 1 (1:repeat 0) 

  go !k (x:xs) = x : go (k+1) ys where
    ys = zipWith (+) xs (take k final ++ ys)
    -- explanation:
    --   xs == drop k $ f (k-1)
    --   ys == drop k $ f (k  )  

{-

Full explanation of 'partitionCountList':
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

let f k = productPSeries $ map (:[]) [1..k]

f 0 = [1,0,0,0,0,0,0,0...]
f 1 = [1,1,1,1,1,1,1,1...]
f 2 = [1,1,2,2,3,3,4,4...]
f 3 = [1,1,2,3,4,5,7,8...]

observe: 

* take (k+1) (f k) == take (k+1) partitionCountList
* f (k+1) == zipWith (+) (f k) (replicate (k+1) 0 ++ f (k+1))

now apply (drop (k+1)) to the second one : 

* drop (k+1) (f (k+1)) == zipWith (+) (drop (k+1) $ f k) (f (k+1))
* f (k+1) = take (k+1) final ++ drop (k+1) (f (k+1))

-}

--------------------------------------------------------------------------------

-- | Naive infinite list of number of partitions of @0,1,2,...@
--
-- > partitionCountListNaive == map countPartitionsNaive [0..]
--
-- This is very slow.
--
partitionCountListNaive :: [Integer]
partitionCountListNaive = map countPartitionsNaive [0..]

--------------------------------------------------------------------------------
-- * Counting all partitions

countAllPartitions :: Int -> Integer
countAllPartitions d = sum' [ countPartitions i | i <- [0..d] ]

-- | Count all partitions fitting into a rectangle.
-- # = \\binom { h+w } { h }
countAllPartitions' :: (Int,Int) -> Integer
countAllPartitions' (h,w) = 
  binomial (h+w) (min h w)
  --sum [ countPartitions' (h,w) i | i <- [0..d] ] where d = h*w

--------------------------------------------------------------------------------
-- * Counting fitting into a rectangle

-- | Number of of d, fitting into a given rectangle. Naive recursive algorithm.
countPartitions' :: (Int,Int) -> Int -> Integer
countPartitions' _ 0 = 1
countPartitions' (0,_) d = if d==0 then 1 else 0
countPartitions' (_,0) d = if d==0 then 1 else 0
countPartitions' (h,w) d = sum
  [ countPartitions' (i,w-1) (d-i) | i <- [1..min d h] ] 

--------------------------------------------------------------------------------
-- * Partitions with given number of parts

-- | Count partitions of @n@ into @k@ parts.
--
-- Naive recursive algorithm.
--
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
-- Partitions with only odd\/distinct parts

{-
-- | Partitions of @n@ with only odd parts
partitionsWithOddParts :: Int -> [Partition]
partitionsWithOddParts d = map Partition (go d d) where
  go _  0  = [[]]
  go !h !n = [ a:as | a<-[1,3..min n h], as <- go a (n-a) ]
-}

{-
-- > length (partitionsWithDistinctParts d) == length (partitionsWithOddParts d)
--
partitionsWithDistinctParts :: Int -> [Partition]
partitionsWithDistinctParts d = map Partition (go d d) where
  go _  0  = [[]]
  go !h !n = [ a:as | a<-[1..min n h], as <- go (a-1) (n-a) ]
-}

--------------------------------------------------------------------------------
