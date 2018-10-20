
-- | Tests for skew partitions.
--

{-# LANGUAGE CPP, BangPatterns, ScopedTypeVariables, DataKinds, KindSignatures #-}
module Tests.Partitions.Skew where

--------------------------------------------------------------------------------

import Test.Framework
import Test.Framework.Providers.QuickCheck2
import Test.QuickCheck

import Tests.Common
import Tests.Partitions.Integer ( Part(..) , fromPart20 , fromPart30 )     -- Arbitrary instances

import Math.Combinat.Partitions.Integer
import Math.Combinat.Partitions.Skew

import Data.List

import Math.Combinat.Classes

import Data.Proxy
import GHC.TypeLits

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

-- | Skew partitions of size at most n
newtype Skew (n :: Nat) = Skew (SkewPartition) deriving (Eq,Show)

-- | usage: fromSkew @20
fromSkew :: Skew n -> SkewPartition
fromSkew (Skew p) = p

fromSkew20 :: Skew 20 -> SkewPartition
fromSkew20 (Skew p) = p

fromSkew30 :: Skew 30 -> SkewPartition
fromSkew30 (Skew p) = p 

instance forall nn. KnownNat nn => Arbitrary (Skew nn) where
  arbitrary = do
    Part p <- arbitrary :: Gen (Part nn)
    let n = partitionWeight p
    d <- choose (0,n)
    let qs = subPartitions d p
        ln = length qs
    k <- choose (0,ln-1)
    let q = qs !! k
    return $ Skew $ mkSkewPartition (p,q) 

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
