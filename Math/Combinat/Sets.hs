
-- | Subsets. 

module Math.Combinat.Sets 
  ( 
    choose
  , combine
  , tuplesFromList
  
  , kSublists
  , sublists
  , countKSublists
  , countSublists
  ) 
  where

import Math.Combinat.Numbers (binomial)

--------------------------------------------------------------------------------

-- | All possible ways to choose @k@ elements from a list, without
-- repetitions. \"Antisymmetric power\" for lists. Synonym for "kSublists".
choose :: Int -> [a] -> [[a]]
choose 0 _  = [[]]
choose k [] = []
choose k (x:xs) = map (x:) (choose (k-1) xs) ++ choose k xs  

-- | All possible ways to choose @k@ elements from a list, /with repetitions/. 
-- \"Symmetric power\" for lists. See also "Math.Combinat.Combinations".
-- TODO: better name?
combine :: Int -> [a] -> [[a]]
combine 0 _  = [[]]
combine k [] = []
combine k xxs@(x:xs) = map (x:) (combine (k-1) xxs) ++ combine k xs  

-- | \"Tensor power\" for lists.
-- See also "Math.Combinat.Tuples".
-- TODO: better name?
tuplesFromList :: Int -> [a] -> [[a]]
tuplesFromList 0 _  = [[]]
tuplesFromList k xs = [ (y:ys) | y <- xs, ys <- tuplesFromList (k-1) xs ]
 
--------------------------------------------------------------------------------

-- | Sublists of a list having given number of elements.
kSublists :: Int -> [a] -> [[a]]
kSublists = choose

-- | @# = \binom { n } { k }@.
countKSublists :: Int -> Int -> Integer
countKSublists k n = binomial n k 

-- | All sublists of a list.
sublists :: [a] -> [[a]]
sublists [] = [[]]
sublists (x:xs) = map (x:) (sublists xs) ++ sublists xs 

-- | @# = 2^n@.
countSublists :: Int -> Integer
countSublists n = 2 ^ n

--------------------------------------------------------------------------------
