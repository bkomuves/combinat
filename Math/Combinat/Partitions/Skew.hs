
-- | Skew partitions.
--
-- Skew partitions are the difference of two integer partitions, denoted by @lambda/mu@.
--

{-# LANGUAGE BangPatterns #-}
module Math.Combinat.Partitions.Skew where

--------------------------------------------------------------------------------

import Data.List

import Math.Combinat.Partitions.Integer
import Math.Combinat.ASCII

--------------------------------------------------------------------------------

-- | A skew partition @lambda/mu@ is represented by the list @[ (mu_i , lambda_i-mu_i) | i<-[1..n] ]@
newtype SkewPartition = SkewPartition [(Int,Int)] deriving (Eq,Ord,Show)

-- | @mkSkewPartition (lambda,mu)@ creates the skew partition @lambda/mu@.
-- Throws an error if @mu@ is not a sub-partition of @lambda@.
mkSkewPartition :: (Partition,Partition) -> SkewPartition
mkSkewPartition ( lam@(Partition bs) , mu@(Partition as)) = if mu `isSubPartitionOf` lam 
  then SkewPartition $ zipWith (\b a -> (a,b-a)) bs (as ++ repeat 0)
  else error "mkSkewPartition: mu should be a subpartition of lambda!" 

-- | Returns 'Nothing' if @mu@ is not a sub-partition of @lambda@.
safeSkewPartition :: (Partition,Partition) -> Maybe SkewPartition
safeSkewPartition ( lam@(Partition bs) , mu@(Partition as)) = if mu `isSubPartitionOf` lam 
  then Just $ SkewPartition $ zipWith (\b a -> (a,b-a)) bs (as ++ repeat 0)
  else Nothing

skewPartitionWeight :: SkewPartition -> Int
skewPartitionWeight (SkewPartition abs) = foldl' (+) 0 (map snd abs)

-- | This function \"cuts off\" the \"uninteresting parts\" of a skew partition
normalizeSkewPartition :: SkewPartition -> SkewPartition
normalizeSkewPartition (SkewPartition abs) = SkewPartition abs' where
  (as,bs) = unzip abs
  a0 = minimum as
  k  = length (takeWhile (==0) bs)
  abs' = zip [ a-a0 | a <- drop k as ] (drop k bs)
   
-- | Returns the outer and inner partition of a skew partition, respectively
fromSkewPartition :: SkewPartition -> (Partition,Partition)
fromSkewPartition (SkewPartition list) = (toPartition (zipWith (+) as bs) , toPartition (filter (>0) as)) where
  (as,bs) = unzip list

outerPartition :: SkewPartition -> Partition  
outerPartition = fst . fromSkewPartition 

innerPartition :: SkewPartition -> Partition  
innerPartition = snd . fromSkewPartition 

dualSkewPartition :: SkewPartition -> SkewPartition
dualSkewPartition = mkSkewPartition . f . fromSkewPartition where
  f (lam,mu) = (dualPartition lam, dualPartition mu)

--------------------------------------------------------------------------------

asciiSkewFerrersDiagram :: SkewPartition -> ASCII
asciiSkewFerrersDiagram = asciiSkewFerrersDiagram' ('@','.') EnglishNotation

asciiSkewFerrersDiagram' 
  :: (Char,Char)       
  -> PartitionConvention -- Orientation
  -> SkewPartition 
  -> ASCII
asciiSkewFerrersDiagram' (outer,inner) orient (SkewPartition abs) = asciiFromLines stuff where
  stuff = case orient of
    EnglishNotation    -> ls
    EnglishNotationCCW -> reverse (transpose ls)
    FrenchNotation     -> reverse ls
  ls = [ replicate a inner ++ replicate b outer | (a,b) <- abs ]

instance DrawASCII SkewPartition where
  ascii = asciiSkewFerrersDiagram     

--------------------------------------------------------------------------------

