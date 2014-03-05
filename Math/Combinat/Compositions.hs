
-- | Compositions. 
--
-- See eg. <http://en.wikipedia.org/wiki/Composition_%28combinatorics%29>
--

module Math.Combinat.Compositions where

import Math.Combinat.Numbers (factorial,binomial)

-------------------------------------------------------

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

-- | Compositions of a given length.
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
compositions1 len' d' 
  | len > d = []
  | otherwise = map plus1 $ compositions len (d-len)
  where
    plus1 = map (+1)
    len = fromIntegral len'
    d   = fromIntegral d'

countCompositions1 :: Integral a => a -> a -> Integer
countCompositions1 len d = countCompositions len (d-len)

-------------------------------------------------------
