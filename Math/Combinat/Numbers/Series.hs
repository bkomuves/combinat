
-- | Some basic power series expansions.
-- This module is not re-exported by "Math.Combinat".
--
-- Note: the \"@convolveWithXXX@\" functions are much faster than the equivalent
-- @(XXX \`convolve\`)@!
-- 
-- TODO: better names for these functions.
--

{-# LANGUAGE CPP, GeneralizedNewtypeDeriving #-}
module Math.Combinat.Numbers.Series where

--------------------------------------------------------------------------------

import Data.List

#ifdef QUICKCHECK
import System.Random
import Test.QuickCheck
#endif

--------------------------------------------------------------------------------

-- | The series [1,0,0,0,0,...], which is the neutral element for the convolution.
{-# SPECIALIZE unitSeries :: [Integer] #-}
unitSeries :: Num a => [a]
unitSeries = 1 : repeat 0

-- | Convolution of series. The result is always an infinite list. Warning: This is slow!
convolve :: Num a => [a] -> [a] -> [a]
convolve xs1 ys1 = res where
  res = [ foldl' (+) 0 (zipWith (*) xs (reverse (take n ys)))
        | n<-[1..] 
        ]
  xs = xs1 ++ repeat 0
  ys = ys1 ++ repeat 0

-- | Convolution of many series. Still slow!
convolveMany :: Num a => [[a]] -> [a]
convolveMany []  = 1 : repeat 0
convolveMany xss = foldl1 convolve xss

--------------------------------------------------------------------------------
-- * \"Coin\" series

-- | Power series expansion of 
-- 
-- > 1 / ( (1-x^k_1) * (1-x^k_2) * ... * (1-x^k_n) )
--
-- Example:
--
-- @(coinSeries [2,3,5])!!k@ is the number of ways 
-- to pay @k@ dollars with coins of two, three and five dollars.
--
-- TODO: better name?
coinSeries :: [Int] -> [Integer]
coinSeries [] = 1 : repeat 0
coinSeries (k:ks) = xs where
  xs = zipWith (+) (coinSeries ks) (replicate k 0 ++ xs) 

-- | Generalization of the above to include coefficients: expansion of 
--  
-- > 1 / ( (1-a_1*x^k_1) * (1-a_2*x^k_2) * ... * (1-a_n*x^k_n) ) 
-- 
coinSeries' :: Num a => [(a,Int)] -> [a]
coinSeries' [] = 1 : repeat 0
coinSeries' ((a,k):aks) = xs where
  xs = zipWith (+) (coinSeries' aks) (replicate k 0 ++ map (*a) xs) 

convolveWithCoinSeries :: [Int] -> [Integer] -> [Integer]
convolveWithCoinSeries ks series1 = worker ks where
  series = series1 ++ repeat 0
  worker [] = series
  worker (k:ks) = xs where
    xs = zipWith (+) (worker ks) (replicate k 0 ++ xs)

convolveWithCoinSeries' :: Num a => [(a,Int)] -> [a] -> [a]
convolveWithCoinSeries' ks series1 = worker ks where
  series = series1 ++ repeat 0
  worker [] = series
  worker ((a,k):aks) = xs where
    xs = zipWith (+) (worker aks) (replicate k 0 ++ map (*a) xs)

--------------------------------------------------------------------------------
-- * Reciprocals of products of polynomials

-- | Convolution of many 'pseries', that is, the expansion of the reciprocal
-- of a product of polynomials
productPSeries :: [[Int]] -> [Integer]
productPSeries = foldl (flip convolveWithPSeries) unitSeries

-- | The same, with coefficients.
productPSeries' :: Num a => [[(a,Int)]] -> [a]
productPSeries' = foldl (flip convolveWithPSeries') unitSeries

convolveWithProductPSeries :: [[Int]] -> [Integer] -> [Integer]
convolveWithProductPSeries kss ser = foldl (flip convolveWithPSeries) ser kss

-- | This is the most general function in this module; all the others
-- are special cases of this one.  
convolveWithProductPSeries' :: Num a => [[(a,Int)]] -> [a] -> [a] 
convolveWithProductPSeries' akss ser = foldl (flip convolveWithPSeries') ser akss
  
--------------------------------------------------------------------------------
-- * Reciprocals of polynomials

-- Reciprocals of polynomials, without coefficients

#ifdef QUICKCHECK
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
#endif

-- | The power series expansion of 
--
-- > 1 / (1 - x^k_1 - x^k_2 - x^k_3 - ... - x^k_n)
--
pseries :: [Int] -> [Integer]
pseries ks = convolveWithPSeries ks unitSeries

#ifdef QUICKCHECK
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
#endif

-- | Convolve with (the expansion of) 
--
-- > 1 / (1 - x^k_1 - x^k_2 - x^k_3 - ... - x^k_n)
--
convolveWithPSeries :: [Int] -> [Integer] -> [Integer]
convolveWithPSeries ks series1 = ys where 
  series = series1 ++ repeat 0 
  ys = worker ks ys 
  worker [] _ = series 
  worker (k:ks) ys = xs where
    xs = zipWith (+) (replicate k 0 ++ ys) (worker ks ys)

--------------------------------------------------------------------------------
--  Reciprocals of polynomials, with coefficients

#ifdef QUICKCHECK
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
#endif

-- | The expansion of 
--
-- > 1 / (1 - a_1*x^k_1 - a_2*x^k_2 - a_3*x^k_3 - ... - a_n*x^k_n)
--
pseries' :: Num a => [(a,Int)] -> [a]
pseries' aks = convolveWithPSeries' aks unitSeries

#ifdef QUICKCHECK
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
#endif

-- | Convolve with (the expansion of) 
--
-- > 1 / (1 - a_1*x^k_1 - a_2*x^k_2 - a_3*x^k_3 - ... - a_n*x^k_n)
--
convolveWithPSeries' :: Num a => [(a,Int)] -> [a] -> [a]
convolveWithPSeries' aks series1 = ys where 
  series = series1 ++ repeat 0 
  ys = worker aks ys 
  worker [] _ = series
  worker ((a,k):aks) ys = xs where
    xs = zipWith (+) (replicate k 0 ++ map (*a) ys) (worker aks ys)

data Sign = Plus | Minus deriving (Eq,Show)

signValue :: Num a => Sign -> a
signValue Plus  =  1
signValue Minus = -1

signedPSeries :: [(Sign,Int)] -> [Integer] 
signedPSeries aks = convolveWithSignedPSeries aks unitSeries

-- | Convolve with (the expansion of) 
--
-- > 1 / (1 +- x^k_1 +- x^k_2 +- x^k_3 +- ... +- x^k_n)
--
-- Should be faster than using `convolveWithPSeries'`.
-- Note: 'Plus' corresponds to the coefficient @-1@ in `pseries'` (since
-- there is a minus sign in the definition there)!
convolveWithSignedPSeries :: [(Sign,Int)] -> [Integer] -> [Integer]
convolveWithSignedPSeries aks series1 = ys where 
  series = series1 ++ repeat 0 
  ys = worker aks ys 
  worker [] _ = series
  worker ((a,k):aks) ys = xs where
    xs = case a of
      Minus -> zipWith (+) one two 
      Plus  -> zipWith (-) one two
    one = worker aks ys
    two = replicate k 0 ++ ys
     
--------------------------------------------------------------------------------

#ifdef QUICKCHECK

swap :: (a,b) -> (b,a)
swap (x,y) = (y,x)

-- compare the first 1000 elements of the infinite lists
(=!=) :: (Eq a, Num a) => [a] -> [a] -> Bool
(=!=) xs1 ys1 = (take m xs == take m ys) where 
  m = 1000
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

minSerValue = -10000 :: Integer
maxSerValue =  10000 :: Integer

rndList :: (RandomGen g, Random a) => Int -> (a, a) -> g -> ([a], g)
rndList n minmax g = swap $ mapAccumL f g [1..n] where
  f g _ = swap $ randomR minmax g 

instance Arbitrary Nat where
  arbitrary = choose (Nat 0 , Nat 750)

instance Arbitrary Exp where
  arbitrary = choose (Exp 1 , Exp 32)

instance Arbitrary CoeffExp where
  arbitrary = do
    coeff <- choose (minSerValue, maxSerValue) :: Gen Integer
    exp <- arbitrary :: Gen Exp
    return $ CoeffExp (coeff,fromExp exp)
   
instance Random Ser where
  random g = (Ser list, g2) where
    (size,g1) = randomR (minSerSize,maxSerSize) g
    (list,g2) = rndList size (minSerValue,maxSerValue) g1
  randomR _ = random

instance Random Exps where
  random g = (Exps list, g2) where
    (size,g1) = randomR (0,10) g
    (list,g2) = rndList size (1,32) g1
  randomR _ = random

instance Random CoeffExps where
  random g = (CoeffExps (zip list2 list1), g3) where
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
  
-- TODO: quickcheck test properties

checkAll :: IO ()
checkAll = do
  let f :: Testable a => a -> IO ()
      f = quickCheck
{- 
  -- these are very slow, because random is slow
  putStrLn "leftIdentity"  ; f prop_leftIdentity
  putStrLn "rightIdentity" ; f prop_rightIdentity
  putStrLn "commutativity" ; f prop_commutativity
  putStrLn "associativity" ; f prop_associativity
-}
  putStrLn "convPSeries1 vs generic" ; f prop_conv1_vs_gen
  putStrLn "convPSeries2 vs generic" ; f prop_conv2_vs_gen
  putStrLn "convPSeries3 vs generic" ; f prop_conv3_vs_gen
  putStrLn "convPSeries1' vs generic" ; f prop_conv1_vs_gen'
  putStrLn "convPSeries2' vs generic" ; f prop_conv2_vs_gen'
  putStrLn "convPSeries3' vs generic" ; f prop_conv3_vs_gen'
  putStrLn "convolve_pseries"  ; f prop_convolve_pseries 
  putStrLn "convolve_pseries'" ; f prop_convolve_pseries' 
  putStrLn "coinSeries vs pseries"  ; f prop_coin_vs_pseries
  putStrLn "coinSeries vs pseries'" ; f prop_coin_vs_pseries'
     
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
    
#endif 

--------------------------------------------------------------------------------

