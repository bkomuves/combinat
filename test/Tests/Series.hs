
-- | Tests for power series
--

{-# LANGUAGE CPP, GeneralizedNewtypeDeriving #-}
module Tests.Series where

--------------------------------------------------------------------------------

import Math.Combinat.Numbers.Series

import Test.Framework
import Test.Framework.Providers.QuickCheck2
import Test.QuickCheck
import System.Random

import Data.List

import Math.Combinat.Sign
import Math.Combinat.Numbers
import Math.Combinat.Partitions.Integer
import Math.Combinat.Helper

--------------------------------------------------------------------------------
-- * code used only for tests

-- | Expansion of @1 / (1-x^k)@. Included for completeness only; 
-- it equals to @coinSeries [k]@, and for example
-- for @k=4@ it is simply
-- 
-- > [1,0,0,0,1,0,0,0,1,0,0,0,1,0,0,0,1,0,0...]
--
pseries1 :: Int -> [Integer]
pseries1 k1 = convolveWithPSeries1 k1 unitSeries 

-- | The expansion of @1 / (1-x^k_1-x^k_2)@
pseries2 :: Int -> Int -> [Integer]
pseries2 k1 k2 = convolveWithPSeries2 k1 k2 unitSeries 

-- | The expansion of @1 / (1-x^k_1-x^k_2-x^k_3)@
pseries3 :: Int -> Int -> Int -> [Integer]
pseries3 k1 k2 k3 = convolveWithPSeries3 k1 k2 k3 unitSeries

--------------------------------------------------------------------------------

-- | Convolve with (the expansion of) @1 / (1-x^k1)@
convolveWithPSeries1 :: Int -> [Integer] -> [Integer]
convolveWithPSeries1 k1 series1 = xs where
  series = series1 ++ repeat 0 
  xs = zipWith (+) series ( replicate k1 0 ++ xs )

-- | Convolve with (the expansion of) @1 / (1-x^k1-x^k2)@
convolveWithPSeries2 :: Int -> Int -> [Integer] -> [Integer]
convolveWithPSeries2 k1 k2 series1 = xs where
  series = series1 ++ repeat 0 
  xs = zipWith3 (\x y z -> x + y + z)
    series
    ( replicate k1 0 ++ xs )
    ( replicate k2 0 ++ xs )
    
-- | Convolve with (the expansion of) @1 / (1-x^k_1-x^k_2-x^k_3)@
convolveWithPSeries3 :: Int -> Int -> Int -> [Integer] -> [Integer]
convolveWithPSeries3 k1 k2 k3 series1 = xs where
  series = series1 ++ repeat 0 
  xs = zipWith4 (\x y z w -> x + y + z + w)
    series
    ( replicate k1 0 ++ xs )
    ( replicate k2 0 ++ xs )
    ( replicate k3 0 ++ xs )

--------------------------------------------------------------------------------

-- | @1 / (1 - a*x^k)@. 
-- For example, for @a=3@ and @k=2@ it is just
-- 
-- > [1,0,3,0,9,0,27,0,81,0,243,0,729,0,2187,0,6561,0,19683,0...]
--
pseries1' :: Num a => (a,Int) -> [a]
pseries1' ak1 = convolveWithPSeries1' ak1 unitSeries

-- | @1 / (1 - a_1*x^k_1 - a_2*x^k_2)@
pseries2' :: Num a => (a,Int) -> (a,Int) -> [a]
pseries2' ak1 ak2 = convolveWithPSeries2' ak1 ak2 unitSeries

-- | @1 / (1 - a_1*x^k_1 - a_2*x^k_2 - a_3*x^k_3)@
pseries3' :: Num a => (a,Int) -> (a,Int) -> (a,Int) -> [a]
pseries3' ak1 ak2 ak3 = convolveWithPSeries3' ak1 ak2 ak3 unitSeries

--------------------------------------------------------------------------------

-- | Convolve with @1 / (1 - a*x^k)@. 
convolveWithPSeries1' :: Num a => (a,Int) -> [a] -> [a]
convolveWithPSeries1' (a1,k1) series1 = xs where
  series = series1 ++ repeat 0 
  xs = zipWith (+)
    series
    ( replicate k1 0 ++ map (*a1) xs )

-- | Convolve with @1 / (1 - a_1*x^k_1 - a_2*x^k_2)@
convolveWithPSeries2' :: Num a => (a,Int) -> (a,Int) -> [a] -> [a]
convolveWithPSeries2' (a1,k1) (a2,k2) series1 = xs where
  series = series1 ++ repeat 0 
  xs = zipWith3 (\x y z -> x + y + z)
    series
    ( replicate k1 0 ++ map (*a1) xs )
    ( replicate k2 0 ++ map (*a2) xs )
    
-- | Convolve with @1 / (1 - a_1*x^k_1 - a_2*x^k_2 - a_3*x^k_3)@
convolveWithPSeries3' :: Num a => (a,Int) -> (a,Int) -> (a,Int) -> [a] -> [a]
convolveWithPSeries3' (a1,k1) (a2,k2) (a3,k3) series1 = xs where
  series = series1 ++ repeat 0 
  xs = zipWith4 (\x y z w -> x + y + z + w)
    series
    ( replicate k1 0 ++ map (*a1) xs )
    ( replicate k2 0 ++ map (*a2) xs )
    ( replicate k3 0 ++ map (*a3) xs )

--------------------------------------------------------------------------------
-- * Types and instances

{-
swap :: (a,b) -> (b,a)
swap (x,y) = (y,x)
-}

-- compare the first 500 elements of the infinite lists
(=!=) :: (Eq a, Num a) => [a] -> [a] -> Bool
(=!=) xs1 ys1 = (take m xs == take m ys) where 
  m = 500
  xs = xs1 ++ repeat 0
  ys = ys1 ++ repeat 0

infix 4 =!=

newtype Nat = Nat { fromNat :: Int } deriving (Eq,Ord,Show,Num,Random)
newtype Ser = Ser { fromSer :: [Integer] } deriving (Eq,Ord,Show)
newtype Exp  = Exp  { fromExp  ::  Int  } deriving (Eq,Ord,Show,Num,Random)
newtype Exps = Exps { fromExps :: [Int] } deriving (Eq,Ord,Show)
newtype CoeffExp  = CoeffExp  { fromCoeffExp  ::  (Integer,Int)  } deriving (Eq,Ord,Show)
newtype CoeffExps = CoeffExps { fromCoeffExps :: [(Integer,Int)] } deriving (Eq,Ord,Show)

minSerSize = 0    :: Int
maxSerSize = 1000 :: Int

minSerValue = -10000 :: Int
maxSerValue =  10000 :: Int

rndList :: (RandomGen g, Random a) => Int -> (a, a) -> g -> ([a], g)
rndList n minmax g = swap $ mapAccumL f g [1..n] where
  f g _ = swap $ randomR minmax g 

instance Arbitrary Nat where
  arbitrary = choose (Nat 0 , Nat 750)

instance Arbitrary Exp where
  arbitrary = choose (Exp 1 , Exp 32)

instance Arbitrary CoeffExp where
  arbitrary = do
    coeff <- choose (minSerValue, maxSerValue) :: Gen Int
    exp   <- arbitrary :: Gen Exp
    return $ CoeffExp (fromIntegral coeff, fromExp exp)
   
instance Random Ser where
  random g = (Ser $ map fi list, g2) where
    (size,g1) = randomR (minSerSize,maxSerSize) g
    (list,g2) = rndList size (minSerValue,maxSerValue) g1
    fi :: Int -> Integer
    fi = fromIntegral 
  randomR _ = random

instance Random Exps where
  random g = (Exps list, g2) where
    (size,g1) = randomR (0,10) g
    (list,g2) = rndList size (1,32) g1
  randomR _ = random

instance Random CoeffExps where
  random g = (CoeffExps (zip (map fromIntegral list2) list1), g3) where
    (size,g1) = randomR (0,10) g
    (list1,g2) = rndList size (1,32) g1
    (list2,g3) = rndList size (minSerValue,maxSerValue) g2
  randomR _ = random
  
instance Arbitrary Ser where
  arbitrary = choose undefined

instance Arbitrary Exps where
  arbitrary = choose undefined

instance Arbitrary CoeffExps where
  arbitrary = choose undefined

--------------------------------------------------------------------------------
-- * test group

testgroup_PowerSeries :: Test
testgroup_PowerSeries = testGroup "Power series"
  [ 
    testProperty "convPSeries1 vs generic"     prop_conv1_vs_gen
  , testProperty "convPSeries2 vs generic"     prop_conv2_vs_gen
  , testProperty "convPSeries3 vs generic"     prop_conv3_vs_gen
  , testProperty "convPSeries1' vs generic"    prop_conv1_vs_gen'
  , testProperty "convPSeries2' vs generic"    prop_conv2_vs_gen'
  , testProperty "convPSeries3' vs generic"    prop_conv3_vs_gen'
  , testProperty "convolve_pseries"            prop_convolve_pseries 
  , testProperty "convolve_pseries'"           prop_convolve_pseries' 
  , testProperty "coinSeries vs pseries"       prop_coin_vs_pseries
  , testProperty "coinSeries vs pseries'"      prop_coin_vs_pseries'

    -- these are very slow, because random is slow
  , testProperty "leftIdentity"    prop_leftIdentity
  , testProperty "rightIdentity"   prop_rightIdentity
  , testProperty "commutativity"   prop_commutativity
  , testProperty "associativity"   prop_associativity
  ]

--------------------------------------------------------------------------------
-- * properties
     
prop_leftIdentity ser = ( xs =!= unitSeries `convolve` xs ) where 
  xs = fromSer ser 

prop_rightIdentity ser = ( unitSeries `convolve` xs =!= xs ) where 
  xs = fromSer ser 

prop_commutativity ser1 ser2 = ( xs `convolve` ys =!= ys `convolve` xs ) where 
  xs = fromSer ser1
  ys = fromSer ser2

prop_associativity ser1 ser2 ser3 = ( one =!= two ) where
  one = (xs `convolve` ys) `convolve` zs
  two = xs `convolve` (ys `convolve` zs)
  xs = fromSer ser1
  ys = fromSer ser2
  zs = fromSer ser3
  
prop_conv1_vs_gen exp1 ser = ( one =!= two ) where
  one = convolveWithPSeries1 k1 xs 
  two = convolveWithPSeries [k1] xs
  k1 = fromExp exp1
  xs = fromSer ser  

prop_conv2_vs_gen exp1 exp2 ser = (one =!= two) where
  one = convolveWithPSeries2 k1 k2 xs 
  two = convolveWithPSeries [k2,k1] xs
  k1 = fromExp exp1
  k2 = fromExp exp2
  xs = fromSer ser  

prop_conv3_vs_gen exp1 exp2 exp3 ser = (one =!= two) where
  one = convolveWithPSeries3 k1 k2 k3 xs 
  two = convolveWithPSeries [k2,k3,k1] xs
  k1 = fromExp exp1
  k2 = fromExp exp2
  k3 = fromExp exp3
  xs = fromSer ser  

prop_conv1_vs_gen' exp1 ser = ( one =!= two ) where
  one = convolveWithPSeries1' ak1 xs 
  two = convolveWithPSeries' [ak1] xs
  ak1 = fromCoeffExp exp1
  xs = fromSer ser  

prop_conv2_vs_gen' exp1 exp2 ser = (one =!= two) where
  one = convolveWithPSeries2' ak1 ak2 xs 
  two = convolveWithPSeries' [ak2,ak1] xs
  ak1 = fromCoeffExp exp1
  ak2 = fromCoeffExp exp2
  xs = fromSer ser  

prop_conv3_vs_gen' exp1 exp2 exp3 ser = (one =!= two) where
  one = convolveWithPSeries3' ak1 ak2 ak3 xs 
  two = convolveWithPSeries' [ak2,ak3,ak1] xs
  ak1 = fromCoeffExp exp1
  ak2 = fromCoeffExp exp2
  ak3 = fromCoeffExp exp3
  xs = fromSer ser  

prop_convolve_pseries exps1 ser = (one =!= two) where
  one = convolveWithPSeries ks1 xs 
  two = xs `convolve` pseries ks1 
  ks1 = fromExps exps1
  xs = fromSer ser  

prop_convolve_pseries' cexps1 ser = (one =!= two) where
  one = convolveWithPSeries' aks1 xs 
  two = xs `convolve` pseries' aks1 
  aks1 = fromCoeffExps cexps1
  xs = fromSer ser  

prop_coin_vs_pseries exps1 = (one =!= two) where
  one = coinSeries ks1 
  two = convolveMany (map pseries1 ks1)
  ks1 = fromExps exps1

prop_coin_vs_pseries' cexps1 = (one =!= two) where
  one = coinSeries' aks1 
  two = convolveMany (map pseries1' aks1)
  aks1 = fromCoeffExps cexps1
    
--------------------------------------------------------------------------------

