
-- | Compositions. 
--
-- See eg. <http://en.wikipedia.org/wiki/Composition_%28combinatorics%29>
--

module Math.Combinat.Compositions where

--------------------------------------------------------------------------------

import System.Random

import Math.Combinat.Sets    ( randomChoice )
import Math.Combinat.Numbers ( factorial , binomial )
import Math.Combinat.Helper

--------------------------------------------------------------------------------
-- * generating all compositions

-- | A /composition/ of an integer @n@ into @k@ parts is an ordered @k@-tuple of nonnegative (sometimes positive) integers
-- whose sum is @n@.
type Composition = [Int]

-- | Compositions fitting into a given shape and having a given degree.
--   The order is lexicographic, that is, 
--
-- > sort cs == cs where cs = compositions' shape k
--
compositions'  
  :: [Int]         -- ^ shape
  -> Int           -- ^ sum
  -> [[Int]]
compositions' [] 0 = [[]]
compositions' [] _ = []
compositions' shape@(s:ss) n = 
  [ x:xs | x <- [0..min s n] , xs <- compositions' ss (n-x) ] 

countCompositions' :: [Int] -> Int -> Integer
countCompositions' [] 0 = 1
countCompositions' [] _ = 0
countCompositions' shape@(s:ss) n = sum 
  [ countCompositions' ss (n-x) | x <- [0..min s n] ] 

-- | All positive compositions of a given number (filtrated by the length). 
-- Total number of these is @2^(n-1)@
allCompositions1 :: Int -> [[Composition]]
allCompositions1 n = map (\d -> compositions1 d n) [1..n] 

-- | All compositions fitting into a given shape.
allCompositions' :: [Int] -> [[Composition]]
allCompositions' shape = map (compositions' shape) [0..d] where d = sum shape

-- | Nonnegative compositions of a given length.
compositions 
  :: Integral a 
  => a       -- ^ length
  -> a       -- ^ sum
  -> [[Int]]
compositions len' d' = compositions' (replicate len d) d where
  len = fromIntegral len'
  d   = fromIntegral d'

-- | # = \\binom { len+d-1 } { len-1 }
countCompositions :: Integral a => a -> a -> Integer
countCompositions len d = binomial (len+d-1) (len-1)

-- | Positive compositions of a given length.
compositions1  
  :: Integral a 
  => a       -- ^ length
  -> a       -- ^ sum
  -> [[Int]]
compositions1 len d 
  | len > d   = []
  | otherwise = map plus1 $ compositions len (d-len)
  where
    plus1 = map (+1)
    -- len = fromIntegral len'
    -- d   = fromIntegral d'

countCompositions1 :: Integral a => a -> a -> Integer
countCompositions1 len d = countCompositions len (d-len)

--------------------------------------------------------------------------------
-- * random compositions

-- | @randomComposition k n@ returns a uniformly random composition 
-- of the number @n@ as an (ordered) sum of @k@ /nonnegative/ numbers
randomComposition :: RandomGen g => Int -> Int -> g -> ([Int],g)
randomComposition k n g0 = 
  if k<1 || n<0 
    then error "randomComposition: k should be positive, and n should be nonnegative" 
    else (comp, g1) 
  where
    (cs,g1) = randomChoice (k-1) (n+k-1) g0
    comp = pairsWith (\x y -> y-x-1) (0 : cs ++ [n+k])
  
-- | @randomComposition1 k n@ returns a uniformly random composition 
-- of the number @n@ as an (ordered) sum of @k@ /positive/ numbers
randomComposition1 :: RandomGen g => Int -> Int -> g -> ([Int],g)
randomComposition1 k n g0 = 
  if k<1 || n<k 
    then error "randomComposition1: we require 0 < k <= n" 
    else (comp, g1) 
  where
    (cs,g1) = randomComposition k (n-k) g0 
    comp = map (+1) cs

--------------------------------------------------------------------------------
