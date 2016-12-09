
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
module Math.Combinat.Partitions.Integer where

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

--------------------------------------------------------------------------------
-- * Type and basic stuff

-- | A partition of an integer. The additional invariant enforced here is that partitions 
-- are monotone decreasing sequences of /positive/ integers. The @Ord@ instance is lexicographical.
newtype Partition = Partition [Int] deriving (Eq,Ord,Show,Read)

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
  
-- | This returns @True@ if the input is non-increasing sequence of 
-- /positive/ integers (possibly empty); @False@ otherwise.
--
isPartition :: [Int] -> Bool
isPartition []  = True
isPartition [x] = x > 0
isPartition (x:xs@(y:_)) = (x >= y) && isPartition xs

isEmptyPartition :: Partition -> Bool
isEmptyPartition (Partition p) = null p

emptyPartition :: Partition
emptyPartition = Partition []

instance CanBeEmpty Partition where
  empty   = emptyPartition
  isEmpty = isEmptyPartition

fromPartition :: Partition -> [Int]
fromPartition (Partition part) = part

-- | The first element of the sequence.
partitionHeight :: Partition -> Int
partitionHeight (Partition part) = case part of
  (p:_) -> p
  []    -> 0
  
-- | The length of the sequence (that is, the number of parts).
partitionWidth :: Partition -> Int
partitionWidth (Partition part) = length part

instance HasHeight Partition where
  height = partitionHeight
 
instance HasWidth Partition where
  width = partitionWidth

heightWidth :: Partition -> (Int,Int)
heightWidth part = (height part, width part)

-- | The weight of the partition 
--   (that is, the sum of the corresponding sequence).
partitionWeight :: Partition -> Int
partitionWeight (Partition part) = sum' part

instance HasWeight Partition where 
  weight = partitionWeight

-- | The dual (or conjugate) partition.
dualPartition :: Partition -> Partition
dualPartition (Partition part) = Partition (_dualPartition part)

instance HasDuality Partition where 
  dual = dualPartition

data Pair = Pair !Int !Int

_dualPartition :: [Int] -> [Int]
_dualPartition [] = []
_dualPartition xs = go 0 (diffSequence xs) [] where
  go !i (d:ds) acc = go (i+1) ds (d:acc)
  go n  []     acc = finish n acc 
  finish !j (k:ks) = replicate k j ++ finish (j-1) ks
  finish _  []     = []

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
diffSequence :: [Int] -> [Int]
diffSequence = go where
  go (x:ys@(y:_)) = (x-y) : go ys 
  go [x] = [x]
  go []  = []

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
-- * Exponential form

-- | We convert a partition to exponential form.
-- @(i,e)@ mean @(i^e)@; for example @[(1,4),(2,3)]@ corresponds to @(1^4)(2^3) = [2,2,2,1,1,1,1]@. Another example:
--
-- > toExponentialForm (Partition [5,5,3,2,2,2,2,1,1]) == [(1,2),(2,4),(3,1),(5,2)]
--
toExponentialForm :: Partition -> [(Int,Int)]
toExponentialForm = _toExponentialForm . fromPartition

_toExponentialForm :: [Int] -> [(Int,Int)]
_toExponentialForm = reverse . map (\xs -> (head xs,length xs)) . group

fromExponentialForm :: [(Int,Int)] -> Partition
fromExponentialForm = Partition . sortBy reverseCompare . go where
  go ((j,e):rest) = replicate e j ++ go rest
  go []           = []   

---------------------------------------------------------------------------------
-- * Automorphisms 

-- | Computes the number of \"automorphisms\" of a given integer partition.
countAutomorphisms :: Partition -> Integer  
countAutomorphisms = _countAutomorphisms . fromPartition

_countAutomorphisms :: [Int] -> Integer
_countAutomorphisms = multinomial . map length . group

---------------------------------------------------------------------------------
-- * Generating partitions

-- | Partitions of @d@.
partitions :: Int -> [Partition]
partitions = map Partition . _partitions

-- | Partitions of @d@, as lists
_partitions :: Int -> [[Int]]
_partitions d = go d d where
  go _  0  = [[]]
  go !h !n = [ a:as | a<-[1..min n h], as <- go a (n-a) ]

-- | Number of partitions of @n@
countPartitions :: Int -> Integer
countPartitions n = partitionCountList !! n

-- | This uses 'countPartitions'', and thus is slow
countPartitionsNaive :: Int -> Integer
countPartitionsNaive d = countPartitions' (d,d) d

--------------------------------------------------------------------------------

-- | Infinite list of number of partitions of @0,1,2,...@
--
-- This uses the infinite product formula the generating function of partitions, recursively
-- expanding it; it is quite fast.
--
-- > partitionCountList == map countPartitions [0..]
--
partitionCountList :: [Integer]
partitionCountList = final where

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
-- This is much slower than the power series expansion above.
--
partitionCountListNaive :: [Integer]
partitionCountListNaive = map countPartitionsNaive [0..]

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

-- | # = \\binom { h+w } { h }
countAllPartitions' :: (Int,Int) -> Integer
countAllPartitions' (h,w) = 
  binomial (h+w) (min h w)
  --sum [ countPartitions' (h,w) i | i <- [0..d] ] where d = h*w

countAllPartitions :: Int -> Integer
countAllPartitions d = sum' [ countPartitions i | i <- [0..d] ]

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

  table = listArray (0,n) $ take (n+1) partitionCountList :: Array Int Integer
  cnt k = table ! k
 
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


-- | Lists all partitions of the same weight as @lambda@ and also dominated by @lambda@
-- (that is, all partial sums are less or equal):
--
-- > dominatedPartitions lam == [ mu | mu <- partitions (weight lam), lam `dominates` mu ]
-- 
dominatedPartitions :: Partition -> [Partition]    
dominatedPartitions (Partition lambda) = map Partition (_dominatedPartitions lambda)

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
dominatingPartitions :: Partition -> [Partition]    
dominatingPartitions (Partition mu) = map Partition (_dominatingPartitions mu)

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
-- * Partitions with only odd\/distinct parts

-- | Partitions of @n@ with only odd parts
partitionsWithOddParts :: Int -> [Partition]
partitionsWithOddParts d = map Partition (go d d) where
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
partitionsWithDistinctParts d = map Partition (go d d) where
  go _  0  = [[]]
  go !h !n = [ a:as | a<-[1..min n h], as <- go (a-1) (n-a) ]

--------------------------------------------------------------------------------
-- * Sub- and super-partitions of a given partition

-- | Returns @True@ of the first partition is a subpartition (that is, fit inside) of the second.
-- This includes equality
isSubPartitionOf :: Partition -> Partition -> Bool
isSubPartitionOf (Partition ps) (Partition qs) = and $ zipWith (<=) ps (qs ++ repeat 0)

-- | This is provided for convenience\/completeness only, as:
--
-- > isSuperPartitionOf q p == isSubPartitionOf p q
--
isSuperPartitionOf :: Partition -> Partition -> Bool
isSuperPartitionOf (Partition qs) (Partition ps) = and $ zipWith (<=) ps (qs ++ repeat 0)


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

----------------------------------------

-- | Super-partitions of a given partition with the given weight:
--
-- > sort (superPartitions d p) == sort [ q | q <- partitions d, isSubPartitionOf p q ]
--
superPartitions :: Int -> Partition -> [Partition]
superPartitions d (Partition ps) = map Partition (_superPartitions d ps)

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
pieriRule :: Partition -> Int -> [Partition] 
pieriRule (Partition lambda) n = map Partition (_pieriRule lambda n) where

  -- | We assume here that @lambda@ is a partition (non-increasing sequence of /positive/ integers)! 
  _pieriRule :: [Int] -> Int -> [[Int]] 
  _pieriRule lambda n
    | n == 0     = [lambda]
    | n <  0     = [] 
    | otherwise  = go n diffs dsums (lambda++[0]) 
    where
      diffs = n : diffSequence lambda                 -- maximum we can add to a given row
      dsums = reverse $ scanl1 (+) (reverse diffs)    -- partial sums of remaining total we can add
      go !k (d:ds) (p:ps@(q:_)) (l:ls) 
        | k > p     = []
        | otherwise = [ h:tl | a <- [ max 0 (k-q) .. min d k ] , let h = l+a , tl <- go (k-a) ds ps ls ]
      go !k [d]    _      [l]    = if k <= d 
                                     then if l+k>0 then [[l+k]] else [[]]
                                     else []
      go !k []     _      _      = if k==0 then [[]] else []

-- | The dual Pieri rule computes @s[lambda]*e[n]@ as a sum of @s[mu]@-s (each with coefficient 1)
dualPieriRule :: Partition -> Int -> [Partition] 
dualPieriRule lam n = map dualPartition $ pieriRule (dualPartition lam) n


{- 
-- moved to "Math.Combinat.Tableaux.GelfandTsetlin"

-- | Computes the Schur expansion of @h[n1]*h[n2]*h[n3]*...*h[nk]@ via iterating the Pieri rule
iteratedPieriRule :: Num coeff => [Int] -> Map Partition coeff
iteratedPieriRule = iteratedPieriRule' (Partition [])

-- | Iterating the Pieri rule, we can compute the Schur expansion of
-- @h[lambda]*h[n1]*h[n2]*h[n3]*...*h[nk]@
iteratedPieriRule' :: Num coeff => Partition -> [Int] -> Map Partition coeff
iteratedPieriRule' plambda ns = iteratedPieriRule'' (plambda,1) ns

{-# SPECIALIZE iteratedPieriRule'' :: (Partition,Int    ) -> [Int] -> Map Partition Int     #-}
{-# SPECIALIZE iteratedPieriRule'' :: (Partition,Integer) -> [Int] -> Map Partition Integer #-}
iteratedPieriRule'' :: Num coeff => (Partition,coeff) -> [Int] -> Map Partition coeff
iteratedPieriRule'' (plambda,coeff0) ns = worker (Map.singleton plambda coeff0) ns where
  worker old []     = old
  worker old (n:ns) = worker new ns where
    stuff = [ (coeff, pieriRule lam n) | (lam,coeff) <- Map.toList old ] 
    new   = foldl' f Map.empty stuff 
    f t0 (c,ps) = foldl' (\t p -> Map.insertWith (+) p c t) t0 ps  
-}

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

