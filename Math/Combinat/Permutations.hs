
-- | Permutations. See:
--   Donald E. Knuth: The Art of Computer Programming, vol 4, pre-fascicle 2B.
--
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
module Math.Combinat.Permutations where

import Data.List
import Data.Array

import Math.Combinat.Helper

-------------------------------------------------------
{-
-- * Types

-- | Standard notation for permutations
newtype Permutation = Permutation (Array Int Int) deriving (Eq,Ord,Show,Read)

-- | Disjoint cycle notation for permutations
newtype DisjCycles  = DisjCycles [[Int]] deriving (Eq,Ord,Show,Read)
-}

-------------------------------------------------------
-- * Permutations of distinct elements

-- | Permutations of [1..n] in lexicographic order, naive algorithm.
_permutations :: Int -> [[Int]]  
_permutations 0 = [[]]
_permutations 1 = [[1]]
_permutations n = helper [1..n] where
  helper [] = [[]]
  helper xs = [ i : ys | i <- xs , ys <- helper (xs `minus` i) ]
  minus [] _ = []
  minus (x:xs) i = if x < i then x : minus xs i else xs

{-
permutations :: Int -> [Permutation]
permutations n = map toPermutationUnsafe $ _permutations n 
-}

-- | # = n!
countPermutations :: Int -> Integer
countPermutations = factorial

-------------------------------------------------------
-- * Permutations of a multiset

-- | Generates all permutations of a multiset. 
--   The order is lexicographic.  
permute :: (Eq a, Ord a) => [a] -> [[a]] 
permute = fasc2B_algorithm_L

-- | # = \\frac { (\sum_i n_i) ! } { \\prod_i (n_i !) }    
countPermute :: (Eq a, Ord a) => [a] -> Integer
countPermute xs = factorial n `div` product [ factorial (length z) | z <- group ys ] 
  where
    ys = sort xs
    n = length xs
  
-- | Generates all permutations of a multiset 
--   (based on \"algorithm L\" in Knuth; somewhat less efficient). 
--   The order is lexicographic.  
fasc2B_algorithm_L :: (Eq a, Ord a) => [a] -> [[a]] 
fasc2B_algorithm_L xs = unfold1 next (sort xs) where
  -- next :: [a] -> Maybe [a]
  next xs = case findj (reverse xs,[]) of 
    Nothing -> Nothing
    Just ( (l:ls) , rs) -> Just $ inc l ls (reverse rs,[]) 
    Just ( [] , _ ) -> error "permute: should not happen"

  -- we use simple list zippers: (left,right)
  -- findj :: ([a],[a]) -> Maybe ([a],[a])   
  findj ( xxs@(x:xs) , yys@(y:_) ) = if x >= y 
    then findj ( xs , x : yys )
    else Just ( xxs , yys )
  findj ( x:xs , [] ) = findj ( xs , [x] )  
  findj ( [] , _ ) = Nothing
  
  -- inc :: a -> [a] -> ([a],[a]) -> [a]
  inc u us ( (x:xs) , yys ) = if u >= x
    then inc u us ( xs , x : yys ) 
    else reverse (x:us)  ++ reverse (u:yys) ++ xs
  inc _ _ ( [] , _ ) = error "permute: should not happen"
      
-------------------------------------------------------
