
-- | Tests for ribbons (border strip skew partitions).
--

{-# LANGUAGE CPP, BangPatterns #-}
module Tests.Partitions.Ribbon where

--------------------------------------------------------------------------------

import Test.Framework
import Test.Framework.Providers.QuickCheck2
import Test.QuickCheck

import Tests.Common
import Tests.Partitions.Integer ( Part(..) , fromPart20 , fromPart30 )     -- Arbitrary instances

import Math.Combinat.Partitions.Integer
import Math.Combinat.Partitions.Skew
import Math.Combinat.Partitions.Skew.Ribbon

import Data.List

import Math.Combinat.Classes

--------------------------------------------------------------------------------
-- * instances

data Inner = Inner Partition Int deriving (Eq,Show)

data Outer = Outer Partition Int deriving (Eq,Show)

instance Arbitrary Inner where
  arbitrary = do
    p <- arbitrary
    let (w,h) = (partitionWidth p, partitionHeight p)
        n = w+h-1
    d <- choose (1,n)
    return $ Inner p d

instance Arbitrary Outer where
  arbitrary = do
    pp <- arbitrary
    let p = fromPart30 pp    -- smaller partitions
    let (w,h) = (partitionWidth p, partitionHeight p)
        n = w+h+10   
    d <- choose (1,n)
    return $ Outer p d

--------------------------------------------------------------------------------
-- * test group

testgroup_Ribbon :: Test
testgroup_Ribbon = testGroup "Ribbons and Corners" 
  [ testGroup "Ribbons"  
      [ testProperty "all inner ribbons vs. naive"        prop_inner_all
      , testProperty "inner ribbons of length vs. naive"  prop_inner_length
      , testProperty "outer ribbons of length vs. naive"  prop_outer_length
      ]
  , testGroup "Corners"
      [ testProperty "inner corner boxes vs. naive" prop_innerCornerBoxes
      , testProperty "outer corner boxes vs. naive" prop_outerCornerBoxes 
      ]
  ]

--------------------------------------------------------------------------------
-- * ribbon properties

prop_inner_all :: Partition -> Bool
prop_inner_all p = sort (innerRibbons p) == sort (innerRibbonsNaive p)

prop_inner_length :: Inner -> Bool
prop_inner_length (Inner p n) = sort (innerRibbonsOfLength p n) == sort (innerRibbonsOfLengthNaive p n)

prop_outer_length :: Outer -> Bool
prop_outer_length (Outer p n) = sort (outerRibbonsOfLength p n) == sort (outerRibbonsOfLengthNaive p n)

--------------------------------------------------------------------------------
-- * corner properties

prop_innerCornerBoxes :: Partition -> Bool
prop_innerCornerBoxes p  =  (innerCornerBoxes p == innerCornerBoxesNaive p)

prop_outerCornerBoxes :: Partition -> Bool
prop_outerCornerBoxes p  =  (outerCornerBoxes p == outerCornerBoxesNaive p)

--------------------------------------------------------------------------------
