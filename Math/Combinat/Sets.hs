
-- | Subsets. 

module Math.Combinat.Sets 
  ( choose
  , kSublists
  , sublists
  , countKSublists
  , countSublists
  ) 
  where

import Math.Combinat.Helper

-------------------------------------------------------

-- | synonym for "kSublists"
choose :: Int -> [a] -> [[a]]
choose = kSublists

-- | Sublists of a list having given number of elements.
kSublists :: Int -> [a] -> [[a]]
kSublists 0 _  = [[]]
kSublists k [] = []
kSublists k (x:xs) = map (x:) (kSublists (k-1) xs) ++ kSublists k xs  

-- | @# = \binom { n } { k }@.
countKSublists :: Int -> Int -> Integer
countKSublists k n = binomial (fromIntegral n) (fromIntegral k)

-- | All sublists of a list.
sublists :: [a] -> [[a]]
sublists [] = [[]]
sublists (x:xs) = map (x:) (sublists xs) ++ sublists xs 

-- | @# = 2^n@.
countSublists :: Int -> Integer
countSublists n = 2 ^ n

-------------------------------------------------------
