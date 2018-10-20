
-- | Tests for skew tableaux

{-# LANGUAGE FlexibleInstances, TypeApplications, DataKinds #-}
module Tests.SkewTableaux where

--------------------------------------------------------------------------------

import Control.Monad

import Test.Framework
import Test.Framework.Providers.QuickCheck2
import Test.QuickCheck
import Test.QuickCheck.Gen

import Tests.Partitions.Integer ()
import Tests.Partitions.Skew ( Skew(..) , fromSkew20 , fromSkew30 )     -- Arbitrary instances

import Math.Combinat.Tableaux
import Math.Combinat.Tableaux.Skew
import Math.Combinat.Partitions.Integer
import Math.Combinat.Partitions.Skew

--------------------------------------------------------------------------------
-- * code

numberOfNonEmptyRows :: SkewPartition -> Int
numberOfNonEmptyRows (SkewPartition xys) = length [ True | (x,y) <- xys, y/=0 ]

-- | Breaks a skew partition into disjoint parts
disjointParts :: SkewPartition -> [SkewPartition]
disjointParts (SkewPartition xys) = map normalizeSkewPartition list where

  list = map SkewPartition $ filter (not . isEmpty) $ break xys

  isEmpty :: [(Int,Int)] -> Bool
  isEmpty xys = and [ y==0 | (x,y) <- xys ]

  break :: [(Int,Int)] -> [[(Int,Int)]]
  break []   = [[]]
  break [xy] = [[xy]]
  break ( xy@(x,y) : rest@((x',y'):_) ) = if x >= x'+y' 
    then [xy] : break rest
    else let (     xys  : rest' ) = break rest
         in  ( (xy:xys) : rest' )
  
  


--------------------------------------------------------------------------------
-- * instances 

instance Arbitrary (SkewTableau Int) where
  arbitrary = do
    pshape <- arbitrary
    let shape = fromSkew20 pshape      -- skew partition of size at most 20
    let w = skewPartitionWeight shape
    content <- replicateM w $ choose (1,1000)
    return $ fillSkewPartitionWithRowWord shape content

--------------------------------------------------------------------------------
-- * test group

testgroup_SkewTableaux :: Test
testgroup_SkewTableaux = testGroup "Skew tableaux"
  [ testProperty "dual^2 = identity"            prop_skew_dual_dual
  , testProperty "fill . rowWord = identity"    prop_rowWord
  , testProperty "fill . columnWord = identity" prop_columnWord
  , testProperty "fill respectes the shape"     prop_fill_shape 
  , testProperty "semistandard skew tableaux are indeed semistandard"   prop_semistandard 
  ]

--------------------------------------------------------------------------------
-- * properties

prop_skew_dual_dual :: SkewTableau Int -> Bool
prop_skew_dual_dual st = (dualSkewTableau (dualSkewTableau st) == st)

prop_rowWord :: SkewTableau Int -> Bool
prop_rowWord st = (fillSkewPartitionWithRowWord shape content == st) where
  shape   = skewTableauShape st
  content = skewTableauRowWord st

prop_columnWord :: SkewTableau Int -> Bool
prop_columnWord st = (fillSkewPartitionWithColumnWord shape content == st) where
  shape   = skewTableauShape st
  content = skewTableauColumnWord st

prop_fill_shape :: SkewPartition -> Bool
prop_fill_shape shape = (shape == shape') where
  tableau = fillSkewPartitionWithColumnWord shape [1..]
  shape'  = skewTableauShape tableau

prop_semistandard :: Skew 20 -> Bool
prop_semistandard (Skew shape) = and 
  [ isSemiStandardSkewTableau st 
  | n  <- [kk..nn] 
  , st <- take 500 (semiStandardSkewTableaux n shape)         -- we only take the first 500 because impossibly slow otherwise
  ]
  where
    nn = min (kk + 10) (skewPartitionWeight shape)
    kk = maximum $ 0 : (map numberOfNonEmptyRows $ disjointParts shape)

--------------------------------------------------------------------------------
