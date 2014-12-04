
-- | A few important number sequences. 
--  
-- See the \"On-Line Encyclopedia of Integer Sequences\",
-- <https://oeis.org> .

module Math.Combinat.Numbers where

--------------------------------------------------------------------------------

import Data.Array

import Math.Combinat.Helper ( sum' )

--------------------------------------------------------------------------------

-- | @(-1)^k@
paritySign :: Integral a => a -> Integer
paritySign k = if odd k then (-1) else 1

--------------------------------------------------------------------------------

-- | A000142.
factorial :: Integral a => a -> Integer
factorial n
  | n <  0    = error "factorial: input should be nonnegative"
  | n == 0    = 1
  | otherwise = product [1..fromIntegral n]

-- | A006882.
doubleFactorial :: Integral a => a -> Integer
doubleFactorial n
  | n <  0    = error "doubleFactorial: input should be nonnegative"
  | n == 0    = 1
  | odd n     = product [1,3..fromIntegral n]
  | otherwise = product [2,4..fromIntegral n]

-- | A007318.
binomial :: Integral a => a -> a -> Integer
binomial n k 
  | k > n = 0
  | k < 0 = 0
  | k > (n `div` 2) = binomial n (n-k)
  | otherwise = (product [n'-k'+1 .. n']) `div` (product [1..k'])
  where 
    k' = fromIntegral k
    n' = fromIntegral n

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
      xs = [ paritySign (k-i) * binomial k i * (fromIntegral i)^n | i<-[0..k] ]

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
    f k = toRational (paritySign (n+k) * factorial k * stirling2nd n k) 
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


 