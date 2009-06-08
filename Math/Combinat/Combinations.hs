
-- | Combinations

module Math.Combinat.Combinations where

import Math.Combinat.Numbers (factorial,binomial)

-------------------------------------------------------

-- | Combinations fitting into a given shape and having a given degree.
--   The order is lexicographic, that is, 
--
-- > sort cs == cs where cs = combinations' shape k
--
combinations'  
  :: [Int]         -- ^ shape
  -> Int           -- ^ sum
  -> [[Int]]
combinations' [] 0 = [[]]
combinations' [] _ = []
combinations' shape@(s:ss) n = 
  [ x:xs | x <- [0..min s n] , xs <- combinations' ss (n-x) ] 

countCombinations' :: [Int] -> Int -> Integer
countCombinations' [] 0 = 1
countCombinations' [] _ = 0
countCombinations' shape@(s:ss) n = sum 
  [ countCombinations' ss (n-x) | x <- [0..min s n] ] 

-- | All combinations fitting into a given shape.
allCombinations' :: [Int] -> [[[Int]]]
allCombinations' shape = map (combinations' shape) [0..d] where d = sum shape

-- | Combinations of a given length.
combinations 
  :: Int       -- ^ length
  -> Int       -- ^ sum
  -> [[Int]]
combinations len d = combinations' (replicate len d) d

-- | # = \\binom { len+d-1 } { len-1 }
countCombinations :: Int -> Int -> Integer
countCombinations len d = binomial (len+d-1) (len-1)

-- | Positive combinations of a given length.
combinations1  
  :: Int       -- ^ length
  -> Int       -- ^ sum
  -> [[Int]]
combinations1 len d 
  | len > d = []
  | otherwise = map plus1 $ combinations len (d-len)
  where
    plus1 = map (+1)

countCombinations1 :: Int -> Int -> Integer
countCombinations1 len d = countCombinations len (d-len)

-------------------------------------------------------
