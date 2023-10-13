
-- | Skew partitions.
--
-- Skew partitions are the difference of two integer partitions, denoted by @lambda/mu@.
--
-- For example
--
-- > mkSkewPartition (Partition [9,7,3,2,2,1] , Partition [5,3,2,1])
--
-- creates the skew partition @(9,7,3,2,2,1) / (5,3,2,1)@, which looks like
--
-- <<svg/skew3.svg>>
--

{-# LANGUAGE CPP, BangPatterns #-}
module Math.Combinat.Partitions.Skew where

--------------------------------------------------------------------------------

import Data.List

import Math.Combinat.Classes
import Math.Combinat.Partitions.Integer
import Math.Combinat.ASCII

--------------------------------------------------------------------------------
-- * Basics

-- | A skew partition @lambda/mu@ is internally represented by the list @[ (mu_i , lambda_i-mu_i) | i<-[1..n] ]@
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

-- | The weight of a skew partition is the weight of the outer partition minus the
-- the weight of the inner partition (that is, the number of boxes present).
skewPartitionWeight :: SkewPartition -> Int
skewPartitionWeight (SkewPartition abs) = foldl' (+) 0 (map snd abs)

instance HasWeight SkewPartition where
  weight = skewPartitionWeight

-- | This function \"cuts off\" the \"uninteresting parts\" of a skew partition
normalizeSkewPartition :: SkewPartition -> SkewPartition
normalizeSkewPartition (SkewPartition abs) = SkewPartition abs' where
  (as,bs) = unzip abs
  a0 = minimum as
  k  = length (takeWhile (==0) bs)
  abs' = zip [ a-a0 | a <- drop k as ] (drop k bs)
   
-- | Returns the outer and inner partition of a skew partition, respectively:
--
-- > mkSkewPartition . fromSkewPartition == id
--
fromSkewPartition :: SkewPartition -> (Partition,Partition)
fromSkewPartition (SkewPartition list) = (toPartition (zipWith (+) as bs) , toPartition (filter (>0) as)) where
  (as,bs) = unzip list

-- | The @lambda@ part of @lambda/mu@
outerPartition :: SkewPartition -> Partition  
outerPartition = fst . fromSkewPartition 

-- | The @mu@ part of @lambda/mu@
innerPartition :: SkewPartition -> Partition  
innerPartition = snd . fromSkewPartition 

-- | The dual skew partition (that is, the mirror image to the main diagonal)
dualSkewPartition :: SkewPartition -> SkewPartition
dualSkewPartition = mkSkewPartition . f . fromSkewPartition where
  f (lam,mu) = (dualPartition lam, dualPartition mu)

instance HasDuality SkewPartition where
  dual = dualSkewPartition

-- | See "partitionElements"
skewPartitionElements :: SkewPartition -> [(Int, Int)]
skewPartitionElements (SkewPartition abs) = concat
  [ [ (i,j) | j <- [a+1 .. a+b] ]
  | (i,(a,b)) <- zip [1..] abs
  ]

--------------------------------------------------------------------------------
-- * Listing skew partitions

-- | Lists all skew partitions with the given outer shape and given (skew) weight
skewPartitionsWithOuterShape :: Partition -> Int -> [SkewPartition]
skewPartitionsWithOuterShape outer skewWeight 
  | innerWeight < 0 || innerWeight > outerWeight = []
  | otherwise = [ mkSkewPartition (outer,inner) | inner <- subPartitions innerWeight outer ]
  where
    outerWeight = weight outer
    innerWeight = outerWeight - skewWeight 

-- | Lists all skew partitions with the given outer shape and any (skew) weight
allSkewPartitionsWithOuterShape :: Partition -> [SkewPartition]
allSkewPartitionsWithOuterShape outer 
  = concat [ skewPartitionsWithOuterShape outer w | w<-[0..outerWeight] ]
  where
    outerWeight = weight outer

-- | Lists all skew partitions with the given inner shape and given (skew) weight
skewPartitionsWithInnerShape :: Partition -> Int -> [SkewPartition]
skewPartitionsWithInnerShape inner skewWeight 
  | innerWeight > outerWeight = []
  | otherwise = [ mkSkewPartition (outer,inner) | outer <- superPartitions outerWeight inner ]
  where
    outerWeight = innerWeight + skewWeight 
    innerWeight = weight inner 

--------------------------------------------------------------------------------
-- connected components

{-
connectedComponents :: SkewPartition -> [((Int,Int),SkewPartition)]
connectedComponents = error "connectedComponents: not implemented yet"

isConnectedSkewPartition :: SkewPartition -> Bool
isConnectedSkewPartition skewp = length (connectedComponents skewp) == 1
-}

--------------------------------------------------------------------------------
-- * ASCII

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

