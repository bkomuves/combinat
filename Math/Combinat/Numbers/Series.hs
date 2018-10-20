
-- | Some basic univariate power series expansions.
-- This module is not re-exported by "Math.Combinat".
--
-- Note: the \"@convolveWithXXX@\" functions are much faster than the equivalent
-- @(XXX \`convolve\`)@!
-- 
-- TODO: better names for these functions.
--

{-# LANGUAGE CPP, BangPatterns, GeneralizedNewtypeDeriving #-}
module Math.Combinat.Numbers.Series where

--------------------------------------------------------------------------------

import Data.List

import Math.Combinat.Sign
import Math.Combinat.Numbers
import Math.Combinat.Partitions.Integer
import Math.Combinat.Helper

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

sumSeries :: Num a => [[a]] -> [a]
sumSeries [] = [0]
sumSeries xs = foldl1' addSeries xs

subSeries :: Num a => [a] -> [a] -> [a]
subSeries xs ys = longZipWith 0 0 (-) xs ys

negateSeries :: Num a => [a] -> [a]
negateSeries = map negate

scaleSeries :: Num a => a -> [a] -> [a]
scaleSeries s = map (*s)

-- | A different implementation, taken from:
--
-- M. Douglas McIlroy: Power Series, Power Serious 
mulSeries :: Num a => [a] -> [a] -> [a]
mulSeries xs ys = go (xs ++ repeat 0) (ys ++ repeat 0) where
  go (f:fs) ggs@(g:gs) = f*g : (scaleSeries f gs) `addSeries` go fs ggs

-- | Multiplication of power series. This implementation is a synonym for 'convolve'
mulSeriesNaive :: Num a => [a] -> [a] -> [a]
mulSeriesNaive = convolve

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

-- | Division of series.
--
-- Taken from: M. Douglas McIlroy: Power Series, Power Serious 
divSeries :: (Eq a, Fractional a) => [a] -> [a] -> [a]
divSeries xs ys = go (xs ++ repeat 0) (ys ++ repeat 0) where
  go (0:fs)     (0:gs) = go fs gs
  go (f:fs) ggs@(g:gs) = let q = f/g in q : go (fs `subSeries` scaleSeries q gs) ggs

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
-- This implementation is taken from
--
-- M. Douglas McIlroy: Power Series, Power Serious 
composeSeries :: (Eq a, Num a) => [a] -> [a] -> [a]
composeSeries xs ys = go (xs ++ repeat 0) (ys ++ repeat 0) where
  go (f:fs) (0:gs) = f : mulSeries gs (go fs (0:gs))
  go (f:fs) (_:gs) = error "PowerSeries/composeSeries: we expect the the constant term of the inner series to be zero"

-- | @substitute f g@ is the power series corresponding to @g(f(x))@. 
-- Equivalently, this is the composition of univariate functions (in the \"wrong\" order).
--
-- Note: for this to be meaningful in general (not depending on convergence properties),
-- we need that the constant term of @f@ is zero.
substitute :: (Eq a, Num a) => [a] -> [a] -> [a]
substitute f g = composeSeries g f

-- | Naive implementation of 'composeSeries' (via 'substituteNaive')
composeSeriesNaive :: (Eq a, Num a) => [a] -> [a] -> [a]
composeSeriesNaive g f = substituteNaive f g

-- | Naive implementation of 'substitute'
substituteNaive :: (Eq a, Num a) => [a] -> [a] -> [a]
substituteNaive as_ bs_ = 
  case head as of
    0 -> [ f n | n<-[0..] ]
    _ -> error "PowerSeries/substituteNaive: we expect the the constant term of the inner series to be zero"
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

-- | We expect the input series to match @(0:a1:_)@. with a1 nonzero The following is true for the result (at least with exact arithmetic):
--
-- > substitute f (lagrangeInversion f) == (0 : 1 : repeat 0)
-- > substitute (lagrangeInversion f) f == (0 : 1 : repeat 0)
--
-- This implementation is taken from:
--
-- M. Douglas McIlroy: Power Series, Power Serious 
lagrangeInversion :: (Eq a, Fractional a) => [a] -> [a]
lagrangeInversion xs = go (xs ++ repeat 0) where
  go (0:fs) = rs where rs = 0 : divSeries unitSeries (composeSeries fs rs)
  go (_:fs) = error "lagrangeInversion: the series should start with (0 + a1*x + a2*x^2 + ...) where a1 is non-zero"

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
integralLagrangeInversionNaive :: (Eq a, Num a) => [a] -> [a]
integralLagrangeInversionNaive series_ = 
  case series of
    (0:1:rest) -> 0 : 1 : [ f n | n<-[1..] ]
    _ -> error "integralLagrangeInversionNaive: the series should start with (0 + x + a2*x^2 + ...)"
  where
    series = series_ ++ repeat 0
    as  = tail series 
    a i = as !! i
    f n = sum [ fromInteger (lagrangeCoeff p) * product [ (a i)^j | (i,j) <- toExponentialForm p ]
              | p <- partitions n
              ] 

-- | Naive implementation of 'lagrangeInversion'
lagrangeInversionNaive :: (Eq a, Fractional a) => [a] -> [a]
lagrangeInversionNaive series_ = 
  case series of
    (0:a1:rest) -> if a1 ==0 
      then err 
      else 0 : (1/a1) : [ f n / a1^(n+1) | n<-[1..] ]
    _ -> err
  where
    err    = error "lagrangeInversionNaive: the series should start with (0 + a1*x + a2*x^2 + ...) where a1 is non-zero"
    series = series_ ++ repeat 0
    a1  = series !! 1
    as  = map (/a1) (tail series)
    a i = as !! i
    f n = sum [ fromInteger (lagrangeCoeff p) * product [ (a i)^j | (i,j) <- toExponentialForm p ]
              | p <- partitions n
              ] 


--------------------------------------------------------------------------------
-- * Differentiation and integration

differentiateSeries :: Num a => [a] -> [a]
differentiateSeries (y:ys) = go (1::Int) ys where
  go !n (x:xs) = fromIntegral n * x : go (n+1) xs
  go _  []     = []

integrateSeries :: Fractional a => [a] -> [a]
integrateSeries ys = 0 : go (1::Int) ys where
  go !n (x:xs) = x / (fromIntegral n) : go (n+1) xs
  go _  []     = []

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

-- | Alternative implementation using differential equations.
--
-- Taken from: M. Douglas McIlroy: Power Series, Power Serious
cosSeries2, sinSeries2 :: Fractional a => [a]
cosSeries2 = unitSeries `subSeries` integrateSeries sinSeries2
sinSeries2 =                        integrateSeries cosSeries2

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

-- | The power series expansion of 
--
-- > 1 / (1 - x^k_1 - x^k_2 - x^k_3 - ... - x^k_n)
--
pseries :: [Int] -> [Integer]
pseries ks = convolveWithPSeries ks unitSeries

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

-- | The expansion of 
--
-- > 1 / (1 - a_1*x^k_1 - a_2*x^k_2 - a_3*x^k_3 - ... - a_n*x^k_n)
--
pseries' :: Num a => [(a,Int)] -> [a]
pseries' aks = convolveWithPSeries' aks unitSeries

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


