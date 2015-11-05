
-- | Tests for lattice paths 
--

{-# LANGUAGE CPP, ScopedTypeVariables, GeneralizedNewtypeDeriving, FlexibleContexts #-}
module Tests.LatticePaths where

--------------------------------------------------------------------------------

import Math.Combinat.LatticePaths

import Test.Framework
import Test.Framework.Providers.QuickCheck2
import Test.QuickCheck
import System.Random

import Control.Monad

import Data.List  

import Math.Combinat.Classes
import Math.Combinat.Helper
import Math.Combinat.Sign
import Math.Combinat.Numbers ( factorial , binomial )

--------------------------------------------------------------------------------
-- * instances

-- | Half-length of a Dyck path
newtype Half = Half Int deriving (Eq,Show)

-- | First number is (usually) less or equal than the second
data HalfPair = HalfPair Int Int deriving (Eq,Show)

maxHalfSize :: Int
maxHalfSize = 11     -- number of paths grow exponentially

instance Arbitrary Half where
  arbitrary = liftM Half $ choose (0,maxHalfSize)    

instance Arbitrary HalfPair where
  arbitrary = do
    n <- choose (0,maxHalfSize)     
    k <- choose (0,n+1)
    return (HalfPair k n)

fi :: Int -> Integer
fi = fromIntegral

--------------------------------------------------------------------------------
-- * test group

testgroup_LatticePaths :: Test
testgroup_LatticePaths = testGroup "Lattice paths"
  
  [ testProperty "dyck paths are in reverse lexicographic order"      prop_revlex
  , testProperty "naive Dyck path algorithm = less naive algorithm"   prop_dyck_naive
  , testProperty "counting Dyck paths"                                prop_count
  , testProperty "counting Lattice paths"                             prop_count_lattice

  , testProperty "bounded Dyck paths, def, v1"                        prop_bounded_1
  , testProperty "bounded Dyck paths, def, v2"                        prop_bounded_2
  , testProperty "bounded Dyck paths w/ high bound = all dyck paths"  prop_not_bounded

  , testProperty "zero-touching Dyck paths"              prop_touching
  , testProperty "Dyck paths w/ k peaks"                 prop_peaking

  ]

--------------------------------------------------------------------------------
-- * test properties         

prop_revlex :: Bool
prop_revlex = and [ sort (dyckPaths m) == reverse (dyckPaths m) | m <- [0..maxHalfSize] ]

prop_dyck_naive :: Bool
prop_dyck_naive = and [ sort (dyckPathsNaive m) == sort (dyckPaths m) | m <- [0..maxHalfSize] ]

prop_count :: Bool
prop_count = and [ fi (length (dyckPaths m)) == countDyckPaths m | m <- [0..maxHalfSize] ]

prop_count_lattice :: HalfPair -> Bool
prop_count_lattice (HalfPair y x) = fi (length (latticePaths (x,y))) == countLatticePaths (x,y)

prop_bounded_1 :: HalfPair -> Bool
prop_bounded_1 (HalfPair h m) = (one == two) where
  one = sort (boundedDyckPaths h m ) 
  two = sort [ p | p <- dyckPaths m  , pathHeight p <= h ]
  
prop_bounded_2 :: Half -> Half -> Bool
prop_bounded_2 (Half h) (Half m) = (one == two) where
  one = sort (boundedDyckPaths h  m ) 
  two = sort [ p | p <- dyckPaths m  , pathHeight p <= h  ]

prop_not_bounded :: Bool
prop_not_bounded = and [ sort (boundedDyckPaths m m) == sort (dyckPaths m) | m <- [0..maxHalfSize] ]

prop_touching :: HalfPair -> Bool
prop_touching (HalfPair k m) = (one == two && fi (length one) == cnt) where
  one = sort (touchingDyckPaths k m) 
  two = sort [ p | p <- dyckPaths m , pathNumberOfZeroTouches p == k ]
  cnt = countTouchingDyckPaths k m

prop_peaking :: HalfPair -> Bool
prop_peaking (HalfPair k m) = (one == two && fi (length one) == cnt) where
  one = sort (peakingDyckPaths k m) 
  two = sort [ p | p <- dyckPaths m , pathNumberOfPeaks p == k ]
  cnt = countPeakingDyckPaths k m

--------------------------------------------------------------------------------

