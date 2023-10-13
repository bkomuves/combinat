
-- | Naive implementation of partitions of integers, encoded as list of @Int@-s.
--
-- Integer partitions are nonincreasing sequences of positive integers.
--
-- This is an internal module, you are not supposed to import it directly.
--
 

{-# LANGUAGE CPP, BangPatterns, ScopedTypeVariables, PatternSynonyms, ViewPatterns #-}
module Math.Combinat.Partitions.Integer.Naive where

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

import Math.Combinat.Partitions.Integer.IntList
import Math.Combinat.Partitions.Integer.Count ( countPartitions )

--------------------------------------------------------------------------------
-- * Type and basic stuff

-- | A partition of an integer. The additional invariant enforced here is that partitions 
-- are monotone decreasing sequences of /positive/ integers. The @Ord@ instance is lexicographical.
newtype Partition = Partition [Int] deriving (Eq,Ord,Show,Read)

instance HasNumberOfParts Partition where
  numberOfParts (Partition p) = length p

---------------------------------------------------------------------------------

toList :: Partition -> [Int]
toList (Partition xs) = xs

fromList :: [Int] -> Partition 
fromList = mkPartition where
  mkPartition xs = Partition $ sortBy (reverseCompare) $ filter (>0) xs

fromListUnsafe :: [Int] -> Partition
fromListUnsafe = Partition

---------------------------------------------------------------------------------

isEmptyPartition :: Partition -> Bool
isEmptyPartition (Partition p) = null p

emptyPartition :: Partition
emptyPartition = Partition []

instance CanBeEmpty Partition where
  empty   = emptyPartition
  isEmpty = isEmptyPartition

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

--------------------------------------------------------------------------------
-- * Pattern synonyms 

-- | Pattern sysnonyms allows us to use existing code with minimal modifications
pattern Nil :: Partition
pattern Nil <- (isEmpty -> True) where
        Nil =  empty

pattern Cons :: Int -> Partition -> Partition
pattern Cons x xs  <- (unconsPartition -> Just (x,xs)) where
        Cons x (Partition xs) = Partition (x:xs)

-- | Simulated newtype constructor 
pattern Partition_ :: [Int] -> Partition
pattern Partition_ xs = Partition xs

pattern Head :: Int -> Partition 
pattern Head h <- (head . toDescList -> h)

pattern Tail :: Partition -> Partition
pattern Tail xs <- (Partition . tail . toDescList -> xs)

pattern Length :: Int -> Partition 
pattern Length n <- (partitionWidth -> n)        
 
---------------------------------------------------------------------------------
-- * Exponential form

-- | We convert a partition to exponential form.
-- @(i,e)@ mean @(i^e)@; for example @[(1,4),(2,3)]@ corresponds to @(1^4)(2^3) = [2,2,2,1,1,1,1]@. Another example:
--
-- > toExponentialForm (Partition [5,5,3,2,2,2,2,1,1]) == [(1,2),(2,4),(3,1),(5,2)]
--
toExponentialForm :: Partition -> [(Int,Int)]
toExponentialForm = _toExponentialForm . toDescList

fromExponentialForm :: [(Int,Int)] -> Partition
fromExponentialForm = Partition . _fromExponentialForm where

--------------------------------------------------------------------------------
-- * List-like operations

-- | From a sequence @[a1,a2,..,an]@ computes the sequence of differences
-- @[a1-a2,a2-a3,...,an-0]@
diffSequence :: Partition -> [Int]
diffSequence = go . toDescList where
  go (x:ys@(y:_)) = (x-y) : go ys 
  go [x] = [x]
  go []  = []

unconsPartition :: Partition -> Maybe (Int,Partition)
unconsPartition (Partition xs) = case xs of
  (y:ys) -> Just (y, Partition ys)
  []     -> Nothing

toDescList :: Partition -> [Int]
toDescList (Partition xs) = xs

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

--------------------------------------------------------------------------------
-- * Containment partial ordering

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
    
--------------------------------------------------------------------------------
-- * The Pieri rule

-- | The Pieri rule computes @s[lambda]*h[n]@ as a sum of @s[mu]@-s (each with coefficient 1).
--
-- See for example <http://en.wikipedia.org/wiki/Pieri's_formula>
--
pieriRule :: Partition -> Int -> [Partition] 
pieriRule (Partition lambda) n = map Partition (_pieriRule lambda n) where

-- | The dual Pieri rule computes @s[lambda]*e[n]@ as a sum of @s[mu]@-s (each with coefficient 1)
dualPieriRule :: Partition -> Int -> [Partition] 
dualPieriRule lam n = map dualPartition $ pieriRule (dualPartition lam) n

--------------------------------------------------------------------------------


