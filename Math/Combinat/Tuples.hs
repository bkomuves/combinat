
-- | Tuples.

module Math.Combinat.Tuples where

import Math.Combinat.Helper

-------------------------------------------------------
-- Tuples

-- | \"Tuples\" fitting into a give shape. The order is lexicographic, that is,
--
-- > sort ts == ts where ts = tuples' shape
--
--   Example: 
--
-- > tuples' [2,3] = 
-- >   [[0,0],[0,1],[0,2],[0,3],[1,0],[1,1],[1,2],[1,3],[2,0],[2,1],[2,2],[2,3]]
--
tuples' :: [Int] -> [[Int]]
tuples' [] = [[]]
tuples' (s:ss) = [ x:xs | x <- [0..s] , xs <- tuples' ss ] 

-- | positive \"tuples\" fitting into a give shape.
tuples1' :: [Int] -> [[Int]]
tuples1' [] = [[]]
tuples1' (s:ss) = [ x:xs | x <- [1..s] , xs <- tuples1' ss ] 

-- | # = \\prod_i (m_i + 1)
countTuples' :: [Int] -> Integer
countTuples' shape = product $ map f shape where
  f k = 1 + fromIntegral k

-- | # = \\prod_i m_i
countTuples1' :: [Int] -> Integer
countTuples1' shape = product $ map fromIntegral shape

tuples 
  :: Int    -- ^ length (width)
  -> Int    -- ^ maximum (height)
  -> [[Int]]
tuples len k = tuples' (replicate len k)

tuples1 
  :: Int    -- ^ length (width)
  -> Int    -- ^ maximum (height)
  -> [[Int]]
tuples1 len k = tuples1' (replicate len k)

-- | # = (m+1) ^ len
countTuples :: Int -> Int -> Integer
countTuples len k = (1 + fromIntegral k) ^ len

-- | # = m ^ len
countTuples1 :: Int -> Int -> Integer
countTuples1 len k = fromIntegral k ^ len

binaryTuples :: Int -> [[Bool]]
binaryTuples len = map (map intToBool) (tuples len 1)

-------------------------------------------------------
