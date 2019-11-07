
-- | Tests for integer partitions.

{-# LANGUAGE CPP, BangPatterns, DataKinds, KindSignatures, ScopedTypeVariables #-}
module Tests.Partitions.Integer where

--------------------------------------------------------------------------------

import Test.Framework
import Test.Framework.Providers.QuickCheck2
import Test.QuickCheck

import Tests.Common

import Math.Combinat.Partitions.Integer
import Math.Combinat.Partitions.Integer.Count

import Data.List
import Control.Monad

-- import Data.Map (Map)
-- import qualified Data.Map as Map

import Math.Combinat.Classes
import Math.Combinat.Numbers ( factorial , binomial , multinomial )
import Math.Combinat.Helper

import Data.Proxy
import GHC.TypeLits

--------------------------------------------------------------------------------

-- | Partitions of size at most n
newtype Part (n :: Nat) = Part (Partition) deriving (Eq,Show)

-- | usage: fromPart @20
fromPart :: Part n -> Partition
fromPart (Part p) = p

fromPart20 :: Part 20 -> Partition
fromPart20 (Part p) = p

fromPart30 :: Part 30 -> Partition
fromPart30 (Part p) = p 

instance forall n. KnownNat n => Arbitrary (Part n) where
  arbitrary = do
    n <- choose (0, fromInteger (natVal (Proxy :: Proxy n)))
    myMkGen' Part (randomPartition n)

newtype Expo = Expo [Int] deriving (Eq,Show)

instance Arbitrary Expo where
  arbitrary = do
    n  <- choose (0, 10)
    es <- replicateM n $ choose (0,4)
    return $ Expo es

--------------------------------------------------------------------------------
-- * Types and instances

newtype PartitionWeight     = PartitionWeight     Int              deriving (Eq,Show)
data    PartitionWeightPair = PartitionWeightPair Int Int          deriving (Eq,Show)
data    PartitionIntPair    = PartitionIntPair    Partition Int    deriving (Eq,Show)
maxPartitionSize :: Int
maxPartitionSize = 44

instance Arbitrary Partition where
  arbitrary = do
    n <- choose (0,maxPartitionSize)
    myMkGen (randomPartition n)

instance Arbitrary PartitionWeight where
  arbitrary = liftM PartitionWeight $ choose (0,maxPartitionSize)

instance Arbitrary PartitionWeightPair where
  arbitrary = do
    n <- choose (0,maxPartitionSize)
    k <- choose (0,n+2)
    return (PartitionWeightPair n k)

instance Arbitrary PartitionIntPair where
  arbitrary = do
    part <- arbitrary
    k <- choose (0,partitionWeight part + 2)
    return (PartitionIntPair part k)

--------------------------------------------------------------------------------

-- {- CONJUGATE LEXICOGRAPHIC ordering is a refinement of dominance partial ordering -}
-- let test n = [ ConjLex p >= ConjLex q | p <- partitions n , q <-partitions n ,  p `dominates` q ]
-- and (test 20)

-- {- LEXICOGRAPHIC ordering is a refinement of dominance partial ordering -}
-- let test n = [ p >= q | p <- partitions n , q <-partitions n ,  p `dominates` q ]
-- and (test 20)

--------------------------------------------------------------------------------
-- * test group

testgroup_IntegerPartitions :: Test
testgroup_IntegerPartitions = testGroup "Integer Partitions"  

  [ testProperty "partitions in a box"             prop_partitions_in_bigbox
  , testProperty "partitions with k parts"         prop_kparts
  , testProperty "odd partitions"                  prop_odd_partitions 
  , testProperty "partitions with distinct parts"  prop_distinct_partitions  
  , testProperty "subpartitions"                   prop_subparts
  , testProperty "dual^2 is identity"              prop_dual_dual
  , testProperty "dominated partitions"            prop_dominated_list
  , testProperty "dominating partitions"           prop_dominating_list
  , testProperty "counting partitions"             prop_countParts
  , testProperty "union/sum duality"               prop_union_sum_duality
    --
  , testProperty "to/from expo vector"             prop_to_from_expo_vector
  , testProperty "to/from expo form"               prop_to_from_expo_form
  , testProperty "from/to expo vector"             prop_from_to_expo_vector
  , testProperty "from/to expo form"               prop_from_to_expo_form
  ]

--------------------------------------------------------------------------------
-- * properties

prop_partitions_in_bigbox :: PartitionWeight -> Bool
prop_partitions_in_bigbox (PartitionWeight n) = (partitions n == partitions' (n,n) n)

prop_kparts :: PartitionWeightPair -> Bool
prop_kparts (PartitionWeightPair n k) = (partitionsWithKParts k n == [ mu | mu <- partitions n, numberOfParts mu == k ])

prop_odd_partitions :: PartitionWeight -> Bool
prop_odd_partitions (PartitionWeight n) = 
  (partitionsWithOddParts n == [ mu | mu <- partitions n, and (map odd (fromPartition mu)) ])

prop_distinct_partitions :: PartitionWeight -> Bool
prop_distinct_partitions (PartitionWeight n) = 
  (partitionsWithDistinctParts n == [ mu | mu <- partitions n, let xs = fromPartition mu, xs == nub xs ])

prop_subparts :: PartitionIntPair -> Bool
prop_subparts (PartitionIntPair lam d) = (subPartitions d lam) == sort [ p | p <- partitions d, isSubPartitionOf p lam ]

prop_dual_dual :: Partition -> Bool
prop_dual_dual lam = (lam == dualPartition (dualPartition lam))

prop_dominated_list :: Partition -> Bool
prop_dominated_list lam = (dominatedPartitions  lam == [ mu  | mu  <- partitions (weight lam), lam `dominates` mu ])

prop_dominating_list :: Partition -> Bool
prop_dominating_list mu  = (dominatingPartitions mu  == [ lam | lam <- partitions (weight mu ), lam `dominates` mu ])

prop_countParts :: Bool
prop_countParts = (take 50 partitionCountList == take 50 partitionCountListNaive)

prop_union_sum_duality :: Partition -> Partition -> Bool
prop_union_sum_duality p q = dualPartition (sumOfPartitions p q) == unionOfPartitions (dualPartition p) (dualPartition q)

--------------------------------------------------------------------------------

prop_to_from_expo_vector p  =  fromExponentVector  (toExponentVector  p) == p
prop_to_from_expo_form   p  =  fromExponentialForm (toExponentialForm p) == p

prop_from_to_expo_vector (Expo es) = toExponentVector (fromExponentVector es) == dropTailingZeros es

prop_from_to_expo_form   p  =  let ef = toExponentialForm p
                               in  toExponentialForm (fromExponentialForm ef) == ef

--------------------------------------------------------------------------------
