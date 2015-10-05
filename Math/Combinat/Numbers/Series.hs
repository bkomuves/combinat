
-- | Some basic univariate power series expansions.
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

import Math.Combinat.Sign
import Math.Combinat.Numbers
import Math.Combinat.Partitions.Integer
import Math.Combinat.Helper

#ifdef QUICKCHECK
import System.Random
import Test.QuickCheck
#endif

--------------------------------------------------------------------------------
-- * Trivial series

-- | The series [1,0,0,0,0,...], which is the neutral element for the convolution.
{-# SPECIALIZE unitSeries :: [Integer] #-}
unitSeries :: Num a => [a]
unitSeries = 1 : repeat 0

-- | Constant zero series
zeroSeries :: Num a => [a]
zeroSeries = repeat 0

-- | Power series representing a constant function
constSeries :: Num a => a -> [a]
constSeries x = x : repeat 0

-- | The power series representation of the identity function @x@
idSeries :: Num a => [a]
idSeries = 0 : 1 : repeat 0

-- | The power series representation of @x^n@
powerTerm :: Num a => Int -> [a]
powerTerm n = replicate n 0 ++ (1 : repeat 0)

--------------------------------------------------------------------------------
-- * Basic operations on power series

addSeries :: Num a => [a] -> [a] -> [a]
addSeries xs ys = longZipWith 0 0 (+) xs ys

subSeries :: Num a => [a] -> [a] -> [a]
subSeries xs ys = longZipWith 0 0 (-) xs ys

negateSeries :: Num a => [a] -> [a]
negateSeries = map negate

scaleSeries :: Num a => a -> [a] -> [a]
scaleSeries s = map (*s)

mulSeries :: Num a => [a] -> [a] -> [a]
mulSeries = convolve

productOfSeries :: Num a => [[a]] -> [a]
productOfSeries = convolveMany

--------------------------------------------------------------------------------
-- * Convolution (product)

-- | Convolution of series (that is, multiplication of power series). 
-- The result is always an infinite list. Warning: This is slow!
convolve :: Num a => [a] -> [a] -> [a]
convolve xs1 ys1 = res where
  res = [ foldl' (+) 0 (zipWith (*) xs (reverse (take n ys)))
        | n<-[1..] 
        ]
  xs = xs1 ++ repeat 0
  ys = ys1 ++ repeat 0

-- | Convolution (= product) of many series. Still slow!
convolveMany :: Num a => [[a]] -> [a]
convolveMany []  = 1 : repeat 0
convolveMany xss = foldl1 convolve xss

--------------------------------------------------------------------------------
-- * Reciprocals of general power series

-- | Given a power series, we iteratively compute its multiplicative inverse
reciprocalSeries :: (Eq a, Fractional a) => [a] -> [a]
reciprocalSeries series = case series of
  [] -> error "reciprocalSeries: empty input series (const 0 function does not have an inverse)"
  (a:as) -> case a of
    0 -> error "reciprocalSeries: input series has constant term 0"
    _ -> map (/a) $ integralReciprocalSeries $ map (/a) series

-- | Given a power series starting with @1@, we can compute its multiplicative inverse
-- without divisions.
--
{-# SPECIALIZE integralReciprocalSeries :: [Int]     -> [Int]     #-}
{-# SPECIALIZE integralReciprocalSeries :: [Integer] -> [Integer] #-}
integralReciprocalSeries :: (Eq a, Num a) => [a] -> [a]
integralReciprocalSeries series = case series of 
  [] -> error "integralReciprocalSeries: empty input series (const 0 function does not have an inverse)"
  (a:as) -> case a of
    1 -> 1 : worker [1]
    _ -> error "integralReciprocalSeries: input series must start with 1"
  where
    worker bs = let b' = - sum (zipWith (*) (tail series) bs) 
                in  b' : worker (b':bs)

--------------------------------------------------------------------------------
-- * Composition of formal power series

-- | @g \`composeSeries\` f@ is the power series expansion of @g(f(x))@.
-- This is a synonym for @flip substitute@.
--
-- We require that the constant term of @f@ is zero.
composeSeries :: (Eq a, Num a) => [a] -> [a] -> [a]
composeSeries g f = substitute f g

-- | @substitute f g@ is the power series corresponding to @g(f(x))@. 
-- Equivalently, this is the composition of univariate functions (in the \"wrong\" order).
--
-- Note: for this to be meaningful in general (not depending on convergence properties),
-- we need that the constant term of @f@ is zero.
substitute :: (Eq a, Num a) => [a] -> [a] -> [a]
substitute as_ bs_ = 
  case head as of
    0 -> [ f n | n<-[0..] ]
    _ -> error "PowerSeries/substitute: we expect the the constant term of the inner series to be zero"
  where
    as = as_ ++ repeat 0
    bs = bs_ ++ repeat 0
    a i = as !! i
    b j = bs !! j
    f n = sum
            [ b m * product [ (a i)^j | (i,j)<-es ] * fromInteger (multinomial (map snd es))
            | p <- partitions n 
            , let es = toExponentialForm p
            , let m  = partitionWidth    p
            ]

--------------------------------------------------------------------------------
-- * Lagrange inversions

-- | Coefficients of the Lagrange inversion
lagrangeCoeff :: Partition -> Integer
lagrangeCoeff p = div numer denom where
  numer = (-1)^m * product (map fromIntegral [n+1..n+m])
  denom = fromIntegral (n+1) * product (map (factorial . snd) es)
  m  = partitionWidth    p
  n  = partitionWeight   p
  es = toExponentialForm p

-- | We expect the input series to match @(0:1:_)@. The following is true for the result (at least with exact arithmetic):
--
-- > substitute f (integralLagrangeInversion f) == (0 : 1 : repeat 0)
-- > substitute (integralLagrangeInversion f) f == (0 : 1 : repeat 0)
--
integralLagrangeInversion :: (Eq a, Num a) => [a] -> [a]
integralLagrangeInversion series_ = 
  case series of
    (0:1:rest) -> 0 : 1 : [ f n | n<-[1..] ]
    _ -> error "integralLagrangeInversion: the series should start with (0 + x + a2*x^2 + ...)"
  where
    series = series_ ++ repeat 0
    as  = tail series 
    a i = as !! i
    f n = sum [ fromInteger (lagrangeCoeff p) * product [ (a i)^j | (i,j) <- toExponentialForm p ]
              | p <- partitions n
              ] 

-- | We expect the input series to match @(0:a1:_)@. with a1 nonzero The following is true for the result (at least with exact arithmetic):
--
-- > substitute f (lagrangeInversion f) == (0 : 1 : repeat 0)
-- > substitute (lagrangeInversion f) f == (0 : 1 : repeat 0)
--
lagrangeInversion :: (Eq a, Fractional a) => [a] -> [a]
lagrangeInversion series_ = 
  case series of
    (0:a1:rest) -> if a1 ==0 
      then err 
      else 0 : (1/a1) : [ f n / a1^(n+1) | n<-[1..] ]
    _ -> err
  where
    err    = error "lagrangeInversion: the series should start with (0 + a1*x + a2*x^2 + ...) where a1 is non-zero"
    series = series_ ++ repeat 0
    a1  = series !! 1
    as  = map (/a1) (tail series)
    a i = as !! i
    f n = sum [ fromInteger (lagrangeCoeff p) * product [ (a i)^j | (i,j) <- toExponentialForm p ]
              | p <- partitions n
              ] 
  
--------------------------------------------------------------------------------
-- * Power series expansions of elementary functions

-- | Power series expansion of @exp(x)@
expSeries :: Fractional a => [a]
expSeries = go 0 1 where
  go i e = e : go (i+1) (e / (i+1))

-- | Power series expansion of @cos(x)@
cosSeries :: Fractional a => [a]
cosSeries = go 0 1 where
  go i e = e : 0 : go (i+2) (-e / ((i+1)*(i+2)))

-- | Power series expansion of @sin(x)@
sinSeries :: Fractional a => [a]
sinSeries = go 1 1 where
  go i e = 0 : e : go (i+2) (-e / ((i+1)*(i+2)))

-- | Power series expansion of @cosh(x)@
coshSeries :: Fractional a => [a]
coshSeries = go 0 1 where
  go i e = e : 0 : go (i+2) (e / ((i+1)*(i+2)))

-- | Power series expansion of @sinh(x)@
sinhSeries :: Fractional a => [a]
sinhSeries = go 1 1 where
  go i e = 0 : e : go (i+2) (e / ((i+1)*(i+2)))

-- | Power series expansion of @log(1+x)@
log1Series :: Fractional a => [a]
log1Series = 0 : go 1 1 where
  go i e = (e/i) : go (i+1) (-e)

-- | Power series expansion of @(1-Sqrt[1-4x])/(2x)@ (the coefficients are the Catalan numbers)
dyckSeries :: Num a => [a]
dyckSeries = [ fromInteger (catalan i) | i<-[(0::Int)..] ]

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

{-
data Sign = Plus | Minus deriving (Eq,Show)

signValue :: Num a => Sign -> a
signValue Plus  =  1
signValue Minus = -1
-}

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

-- * Tests

{-
swap :: (a,b) -> (b,a)
swap (x,y) = (y,x)
-}

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

