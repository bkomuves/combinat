
-- | Partition functions working on lists of integers.
-- 
-- It's not recommended to use this module directly.

{-# LANGUAGE CPP, BangPatterns, ScopedTypeVariables #-}
module Math.Combinat.Partitions.Integer.IntList where

--------------------------------------------------------------------------------

import Data.List
import Control.Monad ( liftM , replicateM )

import Math.Combinat.Numbers ( factorial , binomial , multinomial )
import Math.Combinat.Helper

import Data.Array
import System.Random

import Math.Combinat.Partitions.Integer.Count ( countPartitions )

--------------------------------------------------------------------------------
-- * Type and basic stuff

-- | Sorts the input, and cuts the nonpositive elements.
_mkPartition :: [Int] -> [Int]
_mkPartition xs = sortBy (reverseCompare) $ filter (>0) xs
 
-- | This returns @True@ if the input is non-increasing sequence of 
-- /positive/ integers (possibly empty); @False@ otherwise.
--
_isPartition :: [Int] -> Bool
_isPartition []  = True
_isPartition [x] = x > 0
_isPartition (x:xs@(y:_)) = (x >= y) && _isPartition xs


_dualPartition :: [Int] -> [Int]
_dualPartition [] = []
_dualPartition xs = go 0 (_diffSequence xs) [] where
  go !i (d:ds) acc = go (i+1) ds (d:acc)
  go n  []     acc = finish n acc 
  finish !j (k:ks) = replicate k j ++ finish (j-1) ks
  finish _  []     = []

--------------------------------------------------------------------------------

{-
-- more variations:

_dualPartition_b :: [Int] -> [Int]
_dualPartition_b [] = []
_dualPartition_b xs = go 1 (diffSequence xs) [] where
  go !i (d:ds) acc = go (i+1) ds ((d,i):acc)
  go _  []     acc = concatMap (\(d,i) -> replicate d i) acc

_dualPartition_c :: [Int] -> [Int]
_dualPartition_c [] = []
_dualPartition_c xs = reverse $ concat $ zipWith f [1..] (diffSequence xs) where
  f _ 0 = []
  f k d = replicate d k
-}

-- | A simpler, but bit slower (about twice?) implementation of dual partition
_dualPartitionNaive :: [Int] -> [Int]
_dualPartitionNaive [] = []
_dualPartitionNaive xs@(k:_) = [ length $ filter (>=i) xs | i <- [1..k] ]

-- | From a sequence @[a1,a2,..,an]@ computes the sequence of differences
-- @[a1-a2,a2-a3,...,an-0]@
_diffSequence :: [Int] -> [Int]
_diffSequence = go where
  go (x:ys@(y:_)) = (x-y) : go ys 
  go [x] = [x]
  go []  = []

-- | Example:
--
-- > _elements [5,4,1] ==
-- >   [ (1,1), (1,2), (1,3), (1,4), (1,5)
-- >   , (2,1), (2,2), (2,3), (2,4)
-- >   , (3,1)
-- >   ]
--

_elements :: [Int] -> [(Int,Int)]
_elements shape = [ (i,j) | (i,l) <- zip [1..] shape, j<-[1..l] ] 

---------------------------------------------------------------------------------
-- * Exponential form

-- | We convert a partition to exponential form.
-- @(i,e)@ mean @(i^e)@; for example @[(1,4),(2,3)]@ corresponds to @(1^4)(2^3) = [2,2,2,1,1,1,1]@. Another example:
--
-- > toExponentialForm (Partition [5,5,3,2,2,2,2,1,1]) == [(1,2),(2,4),(3,1),(5,2)]
--
_toExponentialForm :: [Int] -> [(Int,Int)]
_toExponentialForm = reverse . map (\xs -> (head xs,length xs)) . group

_fromExponentialForm :: [(Int,Int)] -> [Int]
_fromExponentialForm = sortBy reverseCompare . go where
  go ((j,e):rest) = replicate e j ++ go rest
  go []           = []   

---------------------------------------------------------------------------------
-- * Generating partitions

-- | Partitions of @d@, as lists
_partitions :: Int -> [[Int]]
_partitions d = go d d where
  go _  0  = [[]]
  go !h !n = [ a:as | a<-[1..min n h], as <- go a (n-a) ]

-- | All integer partitions up to a given degree (that is, all integer partitions whose sum is less or equal to @d@)
_allPartitions :: Int -> [[Int]]
_allPartitions d = concat [ _partitions i | i <- [0..d] ]

-- | All integer partitions up to a given degree (that is, all integer partitions whose sum is less or equal to @d@),
-- grouped by weight
_allPartitionsGrouped :: Int -> [[[Int]]]
_allPartitionsGrouped d = [ _partitions i | i <- [0..d] ]

---------------------------------------------------------------------------------

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

---------------------------------------------------------------------------------
-- * Random partitions

-- | Uniformly random partition of the given weight. 
--
-- NOTE: This algorithm is effective for small @n@-s (say @n@ up to a few hundred \/ one thousand it should work nicely),
-- and the first time it is executed may be slower (as it needs to build the table 'partitionCountList' first)
--
-- Algorithm of Nijenhuis and Wilf (1975); see
--
-- * Knuth Vol 4A, pre-fascicle 3B, exercise 47;
--
-- * Nijenhuis and Wilf: Combinatorial Algorithms for Computers and Calculators, chapter 10
--
_randomPartition :: RandomGen g => Int -> g -> ([Int], g)
_randomPartition n g = (p, g') where
  ([p], g') = _randomPartitions 1 n g

-- | Generates several uniformly random partitions of @n@ at the same time.
-- Should be a little bit faster then generating them individually.
--
_randomPartitions 
  :: forall g. RandomGen g 
  => Int   -- ^ number of partitions to generate
  -> Int   -- ^ the weight of the partitions
  -> g -> ([[Int]], g)
_randomPartitions howmany n = runRand $ replicateM howmany (worker n []) where

  cnt = countPartitions
 
  finish :: [(Int,Int)] -> [Int]
  finish = _mkPartition . concatMap f where f (j,d) = replicate j d

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

  worker :: Int -> [(Int,Int)] -> Rand g [Int]
  worker  0 acc = return $ finish acc
  worker !m acc = do
    capm <- randChoose (0, (fi m) * cnt m - 1)
    let jd@(!j,!d) = find_jd m capm
    worker (m - j*d) (jd:acc)


---------------------------------------------------------------------------------
-- * Dominance order 

-- | @q \`dominates\` p@ returns @True@ if @q >= p@ in the dominance order of partitions
-- (this is partial ordering on the set of partitions of @n@).
--
-- See <http://en.wikipedia.org/wiki/Dominance_order>
--
_dominates :: [Int] -> [Int] -> Bool
_dominates qs ps
  = and $ zipWith (>=) (sums (qs ++ repeat 0)) (sums ps)
  where
    sums = scanl (+) 0

-- | Lists all partitions of the same weight as @lambda@ and also dominated by @lambda@
-- (that is, all partial sums are less or equal):
--
-- > dominatedPartitions lam == [ mu | mu <- partitions (weight lam), lam `dominates` mu ]
-- 
_dominatedPartitions :: [Int] -> [[Int]]
_dominatedPartitions []     = [[]]
_dominatedPartitions lambda = go (head lambda) w dsums 0 where

  n = length lambda
  w = sum    lambda
  dsums = scanl1 (+) (lambda ++ repeat 0)

  go _   0 _       _  = [[]]
  go !h !w (!d:ds) !e  
    | w >  0  = [ (a:as) | a <- [1..min h (d-e)] , as <- go a (w-a) ds (e+a) ] 
    | w == 0  = [[]]
    | w <  0  = error "_dominatedPartitions: fatal error; shouldn't happen"

-- | Lists all partitions of the sime weight as @mu@ and also dominating @mu@
-- (that is, all partial sums are greater or equal):
--
-- > dominatingPartitions mu == [ lam | lam <- partitions (weight mu), lam `dominates` mu ]
-- 
_dominatingPartitions :: [Int] -> [[Int]]
_dominatingPartitions []     = [[]]
_dominatingPartitions mu     = go w w dsums 0 where

  n = length mu
  w = sum    mu
  dsums = scanl1 (+) (mu ++ repeat 0)

  go _   0 _       _  = [[]]
  go !h !w (!d:ds) !e  
    | w >  0  = [ (a:as) | a <- [max 0 (d-e)..min h w] , as <- go a (w-a) ds (e+a) ] 
    | w == 0  = [[]]
    | w <  0  = error "_dominatingPartitions: fatal error; shouldn't happen"

--------------------------------------------------------------------------------
-- * Partitions with given number of parts

-- | Lists partitions of @n@ into @k@ parts.
--
-- > sort (partitionsWithKParts k n) == sort [ p | p <- partitions n , numberOfParts p == k ]
--
-- Naive recursive algorithm.
--
_partitionsWithKParts 
  :: Int    -- ^ @k@ = number of parts
  -> Int    -- ^ @n@ = the integer we partition
  -> [[Int]]
_partitionsWithKParts k n = go n k n where
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
_partitionsWithOddParts :: Int -> [[Int]]
_partitionsWithOddParts d = (go d d) where
  go _  0  = [[]]
  go !h !n = [ a:as | a<-[1,3..min n h], as <- go a (n-a) ]

{-
-- | Partitions of @n@ with only even parts
--
-- Note: this is not very interesting, it's just @(map.map) (2*) $ _partitions (div n 2)@
--
_partitionsWithEvenParts :: Int -> [[Int]]
_partitionsWithEvenParts d = (go d d) where
  go _  0  = [[]]
  go !h !n = [ a:as | a<-[2,4..min n h], as <- go a (n-a) ]
-}

-- | Partitions of @n@ with distinct parts.
-- 
-- Note:
--
-- > length (partitionsWithDistinctParts d) == length (partitionsWithOddParts d)
--
_partitionsWithDistinctParts :: Int -> [[Int]]
_partitionsWithDistinctParts d = (go d d) where
  go _  0  = [[]]
  go !h !n = [ a:as | a<-[1..min n h], as <- go (a-1) (n-a) ]

--------------------------------------------------------------------------------
-- * Sub- and super-partitions of a given partition

-- | Returns @True@ of the first partition is a subpartition (that is, fit inside) of the second.
-- This includes equality
_isSubPartitionOf :: [Int] -> [Int] -> Bool
_isSubPartitionOf ps qs = and $ zipWith (<=) ps (qs ++ repeat 0)

-- | This is provided for convenience\/completeness only, as:
--
-- > isSuperPartitionOf q p == isSubPartitionOf p q
--
_isSuperPartitionOf :: [Int] -> [Int] -> Bool
_isSuperPartitionOf qs ps = and $ zipWith (<=) ps (qs ++ repeat 0)


-- | Sub-partitions of a given partition with the given weight:
--
-- > sort (subPartitions d q) == sort [ p | p <- partitions d, isSubPartitionOf p q ]
--
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
_allSubPartitions :: [Int] -> [[Int]]
_allSubPartitions big 
  | null big   = [[]]
  | otherwise  = go (head big) big
  where
    go _  [] = [[]]
    go !h (b:bs) 
      | h==0         = []
      | otherwise    = [] : [ this:rest | this <- [1..min h b] , rest <- go this bs ]

----------------------------------------

-- | Super-partitions of a given partition with the given weight:
--
-- > sort (superPartitions d p) == sort [ q | q <- partitions d, isSubPartitionOf p q ]
--
_superPartitions :: Int -> [Int] -> [[Int]]
_superPartitions dd small
  | dd < w0     = []
  | null small  = _partitions dd
  | otherwise   = go dd w1 dd (small ++ repeat 0)
  where
    w0 = sum' small
    w1 = w0 - head small
    -- d = remaining weight of the outer partition we are constructing
    -- w = remaining weight of the inner partition (we need to reserve at least this amount)
    -- h = max height (decreasing)
    go !d !w !h (!a:as@(b:_)) 
      | d < 0     = []
      | d == 0    = if a == 0 then [[]] else []
      | otherwise = [ this:rest | this <- [max 1 a .. min h (d-w)] , rest <- go (d-this) (w-b) this as ]
    
--------------------------------------------------------------------------------
-- * The Pieri rule

-- | The Pieri rule computes @s[lambda]*h[n]@ as a sum of @s[mu]@-s (each with coefficient 1).
--
-- See for example <http://en.wikipedia.org/wiki/Pieri's_formula>
--
-- | We assume here that @lambda@ is a partition (non-increasing sequence of /positive/ integers)! 
_pieriRule :: [Int] -> Int -> [[Int]] 
_pieriRule lambda n
    | n == 0     = [lambda]
    | n <  0     = [] 
    | otherwise  = go n diffs dsums (lambda++[0]) 
    where
      diffs = n : _diffSequence lambda                 -- maximum we can add to a given row
      dsums = reverse $ scanl1 (+) (reverse diffs)    -- partial sums of remaining total we can add
      go !k (d:ds) (p:ps@(q:_)) (l:ls) 
        | k > p     = []
        | otherwise = [ h:tl | a <- [ max 0 (k-q) .. min d k ] , let h = l+a , tl <- go (k-a) ds ps ls ]
      go !k [d]    _      [l]    = if k <= d 
                                     then if l+k>0 then [[l+k]] else [[]]
                                     else []
      go !k []     _      _      = if k==0 then [[]] else []

-- | The dual Pieri rule computes @s[lambda]*e[n]@ as a sum of @s[mu]@-s (each with coefficient 1)
_dualPieriRule :: [Int] -> Int -> [[Int]] 
_dualPieriRule lam n = map _dualPartition $ _pieriRule (_dualPartition lam) n

--------------------------------------------------------------------------------
