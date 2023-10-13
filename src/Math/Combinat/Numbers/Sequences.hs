
-- | Some important number sequences. 
--  
-- See the \"On-Line Encyclopedia of Integer Sequences\",
-- <https://oeis.org> .

{-# LANGUAGE BangPatterns, ScopedTypeVariables #-}
module Math.Combinat.Numbers.Sequences where

--------------------------------------------------------------------------------

import Data.Array
import Data.Bits ( shiftL , shiftR , (.&.) )

import Math.Combinat.Helper 
import Math.Combinat.Sign

import Math.Combinat.Numbers.Primes ( primes , factorize , productOfFactors )

import qualified Data.Map.Strict as Map   -- used for factorialPrimeExponentsNaive

--------------------------------------------------------------------------------
-- * Factorial

-- | The factorial function (A000142).
factorial :: Integral a => a -> Integer
factorial = factorialSplit

-- | Faster implementation of the factorial function
factorialSplit :: Integral a => a -> Integer
factorialSplit n = productFromTo 1 n

-- | Naive implementation of factorial
factorialNaive :: Integral a => a -> Integer
factorialNaive n
  | n <  0    = error "factorialNaive: input should be nonnegative"
  | n == 0    = 1
  | otherwise = product [1..fromIntegral n]

-- | \"Swing factorial\" algorithm
factorialSwing :: Integral a => a -> Integer
factorialSwing n = productOfFactors (factorialPrimeExponents $ fromIntegral n) where

--------------------------------------------------------------------------------

-- | Prime factorization of the factorial (using the \"swing factorial\" algorithm)
factorialPrimeExponents :: Int -> [(Integer,Int)]
factorialPrimeExponents n = filter cond $ zip primes (factorialPrimeExponents_ n) where
  cond (_,!e) = e > 0

factorialPrimeExponentsNaive :: forall a. Integral a => a -> [(Integer,Int)]
factorialPrimeExponentsNaive n = result where
  fi = fromIntegral :: a -> Integer
  result = Map.toList 
         $ Map.unionsWith (+) 
         $ map Map.fromList 
         $ map factorize 
         $ map fi [1..n] 

factorialPrimeExponents_ :: Int -> [Int]
factorialPrimeExponents_ = go where
  go  0 = []
  go  1 = []
  go  2 = [1]
  go !n = longAdd half swing where
    half  = map (flip shiftL 1) $ go (shiftR n 1)
    swing = swingFactorialExponents_ n

  longAdd :: [Int] -> [Int] -> [Int]
  longAdd xs [] = xs
  longAdd [] ys = ys
  longAdd (!x:xs) (!y:ys) = (x+y) : longAdd xs ys

-- | Prime factorizaiton of the \"swing factorial\" function)
swingFactorialExponents_ :: Int -> [Int]
swingFactorialExponents_ = go where
  go 0 = []
  go 1 = []
  go 2 = [1]
  go n = expo2 : map expo (tail ps) where

    nn = fromIntegral n :: Integer

    ps :: [Integer]
    ps = takeWhile (<=nn) primes 

    expo2 :: Int
    expo2 = go 0 (shiftR n 1) where
      go :: Int -> Int -> Int
      go !acc !r  
        | r < 1     = acc
        | otherwise = go acc' r' 
        where
          acc' = acc + (r .&. 1)
          r'   = shiftR r 1

    expo :: Integer -> Int
    expo pp = go 0 (div n p) where
      p = fromInteger pp :: Int
      go :: Int -> Int -> Int
      go !acc !r  
        | r < 1     = acc
        | otherwise = go acc' r' 
        where
          acc' = acc + (r .&. 1)
          r'   = div r p

--------------------------------------------------------------------------------

-- | The double factorial
doubleFactorial :: Integral a => a -> Integer
doubleFactorial = doubleFactorialSplit

-- | Faster implementation of the double factorial function
doubleFactorialSplit :: Integral a => a -> Integer
doubleFactorialSplit n
  | n <  0    = error "doubleFactorialSplit: input should be nonnegative"
  | n == 0    = 1
  | odd n     = productFromToStride2 2 n
  | otherwise = let halfn = div n 2 
                in  shiftL (factorialSplit halfn) (fromIntegral halfn)

-- | Naive implementation of the double factorial (A006882).
doubleFactorialNaive :: Integral a => a -> Integer
doubleFactorialNaive n
  | n <  0    = error "doubleFactorialNaive: input should be nonnegative"
  | n == 0    = 1
  | odd n     = product [1,3..fromIntegral n]
  | otherwise = product [2,4..fromIntegral n]

--------------------------------------------------------------------------------
-- * Binomial and multinomial

-- | Binomial numbers (A007318). Note: This is zero for @n<0@ or @k<0@; see also 'signedBinomial' below.
binomial :: Integral a => a -> a -> Integer
binomial = binomialSplit

-- | Faster implementation of binomial
binomialSplit :: Integral a => a -> a -> Integer
binomialSplit n k 
  | k > n = 0
  | k < 0 = 0
  | k > (n `div` 2) = binomialSplit n (n-k)
  | otherwise = (productFromTo (n-k) n) `div` (productFromTo 1 k)

-- | A007318. Note: This is zero for @n<0@ or @k<0@; see also 'signedBinomial' below.
binomialNaive :: Integral a => a -> a -> Integer
binomialNaive n k 
  | k > n = 0
  | k < 0 = 0
  | k > (n `div` 2) = binomial n (n-k)
  | otherwise = (product [n'-k'+1 .. n']) `div` (product [1..k'])
  where 
    k' = fromIntegral k
    n' = fromIntegral n

-- | The extension of the binomial function to negative inputs. This should satisfy the following properties:
--
-- > for n,k >=0 : signedBinomial n k == binomial n k
-- > for any n,k : signedBinomial n k == signedBinomial n (n-k) 
-- > for k >= 0  : signedBinomial (-n) k == (-1)^k * signedBinomial (n+k-1) k
--
-- Note: This is compatible with Mathematica's @Binomial@ function.
--
signedBinomial :: Int -> Int -> Integer
signedBinomial n k
  | n >= 0     = binomial n k
  | k >= 0     = negateIfOdd    k  $ binomial (k-n-1)   k  
  | otherwise  = negateIfOdd (n+k) $ binomial (-k-1) (-n-1)

{-
test_signed_0 = [ signedBinomial ( n) k == signedBinomial ( n) ( n-k)                | n<-[-30..40] , k<-[-30..40] ]
test_signed_1 = [ signedBinomial (-n) k == signedBinomial (-n) (-n-k)                | n<-[-30..40] , k<-[-30..40] ]
test_signed_2 = [ signedBinomial (-n) k == negateIfOdd k $ signedBinomial (n+k-1) k  | n<-[-30..40] , k<-[0..30] ]
-}

-- | A given row of the Pascal triangle; equivalent to a sequence of binomial 
-- numbers, but much more efficient. You can also left-fold over it.
--
-- > pascalRow n == [ binomial n k | k<-[0..n] ]
pascalRow :: Integral a => a -> [Integer]
pascalRow n' = worker 0 1 where
  n = fromIntegral n'
  worker j x
    | j>n   = [] 
    | True  = let j'=j+1 in x : worker j' (div (x*(n-j)) j') 

multinomial :: Integral a => [a] -> Integer
multinomial xs = div
  (factorial (sum xs))
  (product [ factorial x | x<-xs ])  
  
--------------------------------------------------------------------------------
-- * Catalan numbers

-- | Catalan numbers. OEIS:A000108.
catalan :: Integral a => a -> Integer
catalan n 
  | n < 0     = 0
  | otherwise = binomial (n+n) n `div` fromIntegral (n+1)

-- | Catalan's triangle. OEIS:A009766.
-- Note:
--
-- > catalanTriangle n n == catalan n
-- > catalanTriangle n k == countStandardYoungTableaux (toPartition [n,k])
--
catalanTriangle :: Integral a => a -> a -> Integer
catalanTriangle n k
  | k > n     = 0
  | k < 0     = 0
  | otherwise = (binomial (n+k) n * fromIntegral (n-k+1)) `div` fromIntegral (n+1)

--------------------------------------------------------------------------------
-- * Stirling numbers

-- | Rows of (signed) Stirling numbers of the first kind. OEIS:A008275.
-- Coefficients of the polinomial @(x-1)*(x-2)*...*(x-n+1)@.
-- This function uses the recursion formula.
signedStirling1stArray :: Integral a => a -> Array Int Integer
signedStirling1stArray n
  | n <  1    = error "stirling1stArray: n should be at least 1"
  | n == 1    = listArray (1,1 ) [1]
  | otherwise = listArray (1,n') [ lkp (k-1) - fromIntegral (n-1) * lkp k | k<-[1..n'] ] 
  where
    prev = signedStirling1stArray (n-1)
    n' = fromIntegral n :: Int
    lkp j | j <  1    = 0
          | j >= n'   = 0
          | otherwise = prev ! j 
        
-- | (Signed) Stirling numbers of the first kind. OEIS:A008275.
-- This function uses 'signedStirling1stArray', so it shouldn't be used
-- to compute /many/ Stirling numbers.
--
-- Argument order: @signedStirling1st n k@
--
signedStirling1st :: Integral a => a -> a -> Integer
signedStirling1st n k 
  | k==0 && n==0 = 1
  | k < 1        = 0
  | k > n        = 0
  | otherwise    = signedStirling1stArray n ! (fromIntegral k)

-- | (Unsigned) Stirling numbers of the first kind. See 'signedStirling1st'.
unsignedStirling1st :: Integral a => a -> a -> Integer
unsignedStirling1st n k = abs (signedStirling1st n k)

-- | Stirling numbers of the second kind. OEIS:A008277.
-- This function uses an explicit formula.
-- 
-- Argument order: @stirling2nd n k@
--
stirling2nd :: Integral a => a -> a -> Integer
stirling2nd n k 
  | k==0 && n==0 = 1
  | k < 1        = 0
  | k > n        = 0
  | otherwise = sum xs `div` factorial k where
      xs = [ negateIfOdd (k-i) $ binomial k i * (fromIntegral i)^n | i<-[0..k] ]

--------------------------------------------------------------------------------
-- * Bernoulli numbers

-- | Bernoulli numbers. @bernoulli 1 == -1%2@ and @bernoulli k == 0@ for
-- k>2 and /odd/. This function uses the formula involving Stirling numbers
-- of the second kind. Numerators: A027641, denominators: A027642.
bernoulli :: Integral a => a -> Rational
bernoulli n 
  | n <  0    = error "bernoulli: n should be nonnegative"
  | n == 0    = 1
  | n == 1    = -1/2
  | otherwise = sum [ f k | k<-[1..n] ] 
  where
    f k = toRational (negateIfOdd (n+k) $ factorial k * stirling2nd n k) 
        / toRational (k+1)

--------------------------------------------------------------------------------
-- * Bell numbers

-- | Bell numbers (Sloane's A000110) from B(0) up to B(n). B(0)=B(1)=1, B(2)=2, etc. 
--
-- The Bell numbers count the number of /set partitions/ of a set of size @n@
-- 
-- See <http://en.wikipedia.org/wiki/Bell_number>
--
bellNumbersArray :: Integral a => a -> Array Int Integer
bellNumbersArray nn = arr where
  arr = array (0::Int,n) kvs 
  n = fromIntegral nn :: Int
  kvs = (0,1) : [ (k, f k) | k<-[1..n] ] 
  f n = sum' [ binomial (n-1) k * arr ! k | k<-[0..n-1] ]

-- | The n-th Bell number B(n), using the Stirling numbers of the second kind.
-- This may be slower than using 'bellNumbersArray'.
bellNumber :: Integral a => a -> Integer
bellNumber nn
  | n <  0     = error "bellNumber: expecting a nonnegative index"
  | n == 0     = 1
  | otherwise  = sum' [ stirling2nd n k | k<-[1..n] ] 
  where
    n = fromIntegral nn :: Int

--------------------------------------------------------------------------------


 