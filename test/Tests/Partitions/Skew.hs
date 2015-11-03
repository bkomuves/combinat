
-- | Tests for skew partitions.
--

{-# LANGUAGE CPP, BangPatterns #-}
module Tests.Partitions.Skew where

--------------------------------------------------------------------------------

import Test.Framework
import Test.Framework.Providers.QuickCheck2
import Test.QuickCheck

import Tests.Common
import Tests.Partitions.Integer ()     -- Arbitrary instances

import Math.Combinat.Partitions.Integer
import Math.Combinat.Partitions.Skew

import Data.List

import Math.Combinat.Classes

--------------------------------------------------------------------------------
-- * instances

instance Arbitrary SkewPartition where
  arbitrary = do
    p <- arbitrary
    let n = partitionWeight p
    d <- choose (0,n)
    let qs = subPartitions d p
        ln = length qs
    k <- choose (0,ln-1)
    let q = qs !! k
    return $ mkSkewPartition (p,q) 

--------------------------------------------------------------------------------
-- * test group

testgroup_SkewPartitions :: Test
testgroup_SkewPartitions = testGroup "Skew Partitions"  

  [ testProperty "dual^2 = identity"              prop_dual_dual
  , testProperty "dual vs. inner/outer dual"      prop_dual_from
  , testProperty "to . from = identity"           prop_from_to
  , testProperty "from . to = identity"           prop_to_from
  , testProperty "from . to . from = from"        prop_from_to_from
  , testProperty "weight vs. inner/outer weight"  prop_weight
  ]

--------------------------------------------------------------------------------
-- * properties

prop_dual_dual :: SkewPartition -> Bool
prop_dual_dual sp = (dualSkewPartition (dualSkewPartition sp) == sp)

prop_dual_from :: SkewPartition -> Bool
prop_dual_from sp = (p == dual p' && q == dual q') where
  (p,q)   = fromSkewPartition sp
  sp'     = dualSkewPartition sp
  (p',q') = fromSkewPartition sp'

prop_from_to :: SkewPartition -> Bool
prop_from_to sp = (mkSkewPartition (fromSkewPartition sp) == sp)

prop_to_from :: (Partition,Partition) -> Bool
prop_to_from (p,q) = 
  case mb of
    Nothing -> True
    Just sp -> fromSkewPartition sp == (p,q)
  where
    mb = safeSkewPartition (p,q)

prop_from_to_from :: SkewPartition -> Bool
prop_from_to_from sp = (pq == pq') where
  pq  = fromSkewPartition sp
  sp' = mkSkewPartition pq
  pq' = fromSkewPartition sp'

prop_weight :: SkewPartition -> Bool
prop_weight sp = (skewPartitionWeight sp == weight p - weight q) where
  (p,q) = fromSkewPartition sp

--------------------------------------------------------------------------------
