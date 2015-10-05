
-- | Non-crossing partitions.
--
-- See eg. <http://en.wikipedia.org/wiki/Noncrossing_partition>
--
-- Non-crossing partitions of the set @[1..n]@ are encoded as lists of lists
-- in standard form: Entries decreasing in each block  and blocks listed in increasing order of their first entries.
-- For example the partition in the diagram
--
-- <<svg/noncrossing.svg>>
--
-- is represented as
--
-- > NonCrossing [[3],[5,4,2],[7,6,1],[9,8]]
--

{-# LANGUAGE BangPatterns #-}
module Math.Combinat.Partitions.NonCrossing where

--------------------------------------------------------------------------------

import Control.Applicative

import Data.List
import Data.Ord

import System.Random

import Math.Combinat.Numbers
import Math.Combinat.LatticePaths
import Math.Combinat.Helper
import Math.Combinat.Partitions.Set
import Math.Combinat.Classes

--------------------------------------------------------------------------------
-- * The type of non-crossing partitions

-- | A non-crossing partition of the set @[1..n]@ in standard form: 
-- entries decreasing in each block  and blocks listed in increasing order of their first entries.
newtype NonCrossing = NonCrossing [[Int]] deriving (Eq,Ord,Show,Read)

-- | Checks whether a set partition is noncrossing.
--
-- Implementation method: we convert to a Dyck path and then back again, and finally compare. 
-- Probably not very efficient, but should be better than a naive check for crosses...)
--
_isNonCrossing :: [[Int]] -> Bool
_isNonCrossing zzs0 = _isNonCrossingUnsafe (_standardizeNonCrossing zzs0)

-- | Warning: This function assumes the standard ordering!
_isNonCrossingUnsafe :: [[Int]] -> Bool
_isNonCrossingUnsafe zzs = 
  case _nonCrossingPartitionToDyckPathMaybe zzs of
    Nothing   -> False
    Just dyck -> case dyckPathToNonCrossingPartitionMaybe dyck of
      Nothing                -> False
      Just (NonCrossing yys) -> yys == zzs

-- | Convert to standard form: entries decreasing in each block 
-- and blocks listed in increasing order of their first entries.
_standardizeNonCrossing :: [[Int]] -> [[Int]]
_standardizeNonCrossing = sortBy (comparing myhead) . map reverseSort where
  myhead xs = case xs of
    (x:xs) -> x
    []     -> error "_standardizeNonCrossing: empty subset"

fromNonCrossing :: NonCrossing -> [[Int]]
fromNonCrossing (NonCrossing xs) = xs

toNonCrossingUnsafe :: [[Int]] -> NonCrossing
toNonCrossingUnsafe = NonCrossing

-- | Throws an error if the input is not a non-crossing partition
toNonCrossing :: [[Int]] -> NonCrossing
toNonCrossing xxs = case toNonCrossingMaybe xxs of
  Just nc -> nc
  Nothing -> error "toNonCrossing: not a non-crossing partition"

toNonCrossingMaybe :: [[Int]] -> Maybe NonCrossing
toNonCrossingMaybe xxs0 = 
  if _isNonCrossingUnsafe xxs
    then Just $ NonCrossing xxs
    else Nothing
  where 
    xxs = _standardizeNonCrossing xxs0

-- | If a set partition is actually non-crossing, then we can convert it
setPartitionToNonCrossing :: SetPartition -> Maybe NonCrossing
setPartitionToNonCrossing (SetPartition zzs0) =
  if _isNonCrossingUnsafe zzs
    then Just $ NonCrossing zzs
    else Nothing
  where
    zzs = _standardizeNonCrossing zzs0

instance HasNumberOfParts NonCrossing where
  numberOfParts (NonCrossing p) = length p

--------------------------------------------------------------------------------
-- * Bijection to Dyck paths

-- | Bijection between Dyck paths and noncrossing partitions
--
-- Based on: David Callan: /Sets, Lists and Noncrossing Partitions/
--
-- Fails if the input is not a Dyck path.
dyckPathToNonCrossingPartition :: LatticePath -> NonCrossing
dyckPathToNonCrossingPartition = NonCrossing . go 0 [] [] [] where
  go :: Int -> [Int] -> [Int] -> [[Int]] -> LatticePath -> [[Int]] 
  go !cnt stack small big path =
    case path of
      (x:xs) -> case x of 
        UpStep   -> let cnt' = cnt + 1 in case xs of
          (y:ys)   -> case y of
            UpStep   -> go cnt' (cnt':stack) small                  big  xs  
            DownStep -> go cnt' (cnt':stack) []    (reverse small : big) xs
          []       -> error "dyckPathToNonCrossingPartition: last step is an UpStep (thus input was not a Dyck path)"
        DownStep -> case stack of
          (k:ks)   -> go cnt ks (k:small) big xs
          []       -> error "dyckPathToNonCrossingPartition: empty stack, shouldn't happen (thus input was not a Dyck path)"
      [] -> tail $ reverse (reverse small : big)

-- | Safe version of 'dyckPathToNonCrossingPartition'
dyckPathToNonCrossingPartitionMaybe :: LatticePath -> Maybe NonCrossing
dyckPathToNonCrossingPartitionMaybe = fmap NonCrossing . go 0 [] [] [] where
  go :: Int -> [Int] -> [Int] -> [[Int]] -> LatticePath -> Maybe [[Int]] 
  go !cnt stack small big path =
    case path of
      (x:xs) -> case x of 
        UpStep   -> let cnt' = cnt + 1 in case xs of
          (y:ys)   -> case y of
            UpStep   -> go cnt' (cnt':stack) small                  big  xs  
            DownStep -> go cnt' (cnt':stack) []    (reverse small : big) xs
          []       -> Nothing
        DownStep -> case stack of
          (k:ks)   -> go cnt ks (k:small) big xs
          []       -> Nothing
      [] -> Just $ tail $ reverse (reverse small : big)

-- | The inverse bijection (should never fail proper 'NonCrossing'-s)
nonCrossingPartitionToDyckPath :: NonCrossing -> LatticePath
nonCrossingPartitionToDyckPath (NonCrossing zzs) = go 0 zzs where
  go !k (ys@(y:_):yys) = replicate (y-k) UpStep ++ replicate (length ys) DownStep ++ go y yys
  go !k []             = []
  go _  _              = error "nonCrossingPartitionToDyckPath: shouldnt't happen"

-- | Safe version 'nonCrossingPartitionToDyckPath'
_nonCrossingPartitionToDyckPathMaybe :: [[Int]] -> Maybe LatticePath
_nonCrossingPartitionToDyckPathMaybe = go 0 where
  go !k (ys@(y:_):yys) = fmap (\zs -> replicate (y-k) UpStep ++ replicate (length ys) DownStep ++ zs) (go y yys)
  go !k []             = Just []
  go _  _              = Nothing

--------------------------------------------------------------------------------

{- 
-- this should be mapped to NonCrossing [[3],[5,4,2],[7,6,1],[9,8]]
testpath = [u,u,u,d,u,u,d,d,d,u,u,d,d,d,u,u,d,d] where
  u = UpStep
  d = DownStep

testnc = NonCrossing [[3],[5,4,2],[7,6,1],[9,8]]
-}

--------------------------------------------------------------------------------
-- * Generating non-crossing partitions

-- | Lists all non-crossing partitions of @[1..n]@
--
-- Equivalent to (but orders of magnitude faster than) filtering out the non-crossing ones:
--
-- > (sort $ catMaybes $ map setPartitionToNonCrossing $ setPartitions n) == sort (nonCrossingPartitions n)
--
nonCrossingPartitions :: Int -> [NonCrossing]
nonCrossingPartitions = map dyckPathToNonCrossingPartition . dyckPaths

-- | Lists all non-crossing partitions of @[1..n]@ into @k@ parts.
--
-- > sort (nonCrossingPartitionsWithKParts k n) == sort [ p | p <- nonCrossingPartitions n , numberOfParts p == k ]
--
nonCrossingPartitionsWithKParts 
  :: Int   -- ^ @k@ = number of parts 
  -> Int   -- ^ @n@ = size of the set
  -> [NonCrossing]
nonCrossingPartitionsWithKParts k n = map dyckPathToNonCrossingPartition $ peakingDyckPaths k n

-- | Non-crossing partitions are counted by the Catalan numbers
countNonCrossingPartitions :: Int -> Integer
countNonCrossingPartitions = countDyckPaths

-- | Non-crossing partitions with @k@ parts are counted by the Naranaya numbers
countNonCrossingPartitionsWithKParts 
  :: Int   -- ^ @k@ = number of parts 
  -> Int   -- ^ @n@ = size of the set
  -> Integer
countNonCrossingPartitionsWithKParts = countPeakingDyckPaths

--------------------------------------------------------------------------------

-- | Uniformly random non-crossing partition
randomNonCrossingPartition :: RandomGen g => Int -> g -> (NonCrossing,g)
randomNonCrossingPartition n g0 = (dyckPathToNonCrossingPartition dyck, g1) where
  (dyck,g1) = randomDyckPath n g0

--------------------------------------------------------------------------------
