
-- | Vector partitions. See:
--
--  * Donald E. Knuth: The Art of Computer Programming, vol 4, pre-fascicle 3B.
--

{-# LANGUAGE BangPatterns #-}
module Math.Combinat.Partitions.Vector where

--------------------------------------------------------------------------------

import Data.Array.Unboxed
import Data.List

--------------------------------------------------------------------------------

-- | Integer vectors. The indexing starts from 1.
type IntVector = UArray Int Int

-- | Vector partitions. Basically a synonym for 'fasc3B_algorithm_M'.
vectorPartitions :: IntVector -> [[IntVector]]
vectorPartitions = fasc3B_algorithm_M . elems

_vectorPartitions :: [Int] -> [[[Int]]]
_vectorPartitions = map (map elems) . fasc3B_algorithm_M

-- | Generates all vector partitions 
--   (\"algorithm M\" in Knuth). 
--   The order is decreasing lexicographic.  
fasc3B_algorithm_M :: [Int] -> [[IntVector]] 
{- note to self: Knuth's descriptions of algorithms are still totally unreadable -}
fasc3B_algorithm_M xs = worker [start] where

  -- n = sum xs
  m = length xs

  start = [ (j,x,x) | (j,x) <- zip [1..] xs ]  
  
  worker stack@(last:_) = 
    case decrease stack' of
      Nothing -> [visited]
      Just stack'' -> visited : worker stack''
    where
      stack'  = subtract_rec stack
      visited = map to_vector stack'
      
  decrease (last:rest) = 
    case span (\(_,_,v) -> v==0) (reverse last) of
      ( _ , [(_,_,1)] ) -> case rest of
        [] -> Nothing
        _  -> decrease rest
      ( second , (c,u,v):first ) -> Just (modified:rest) where 
        modified =   
          reverse first ++ 
          (c,u,v-1) :  
          [ (c,u,u) | (c,u,_) <- reverse second ] 
      _ -> error "fasc3B_algorithm_M: should not happen"
        
  to_vector cuvs = 
    accumArray (flip const) 0 (1,m)
      [ (c,v) | (c,_,v) <- cuvs ] 

  subtract_rec all@(last:_) = 
    case subtract last of 
      []  -> all
      new -> subtract_rec (new:all) 

  subtract [] = []
  subtract full@((c,u,v):rest) = 
    if w >= v 
      then (c,w,v) : subtract   rest
      else           subtract_b full
    where w = u - v
    
  subtract_b [] = []
  subtract_b ((c,u,v):rest) = 
    if w /= 0 
      then (c,w,w) : subtract_b rest
      else           subtract_b rest
    where w = u - v

--------------------------------------------------------------------------------
