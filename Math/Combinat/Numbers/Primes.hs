
-- | Prime numbers and related number theoretical stuff.

module Math.Combinat.Numbers.Primes 
  ( -- * List of prime numbers
    primes
  , primesSimple
  , primesTMWE
    -- * Prime factorization
  , groupIntegerFactors
  , integerFactorsTrialDivision
    -- * Integer logarithm
  , integerLog2
  , ceilingLog2
    -- * Integer square root
  , isSquare
  , integerSquareRoot
  , ceilingSquareRoot
  , integerSquareRoot' 
  , integerSquareRootNewton'
    -- * Modulo @m@ arithmetic
  , powerMod
    -- * Prime testing
  , millerRabinPrimalityTest
  )
  where

--------------------------------------------------------------------------------

-- import Math.Combinat.Numbers

import Data.List ( group , sort )
import Data.Bits

--------------------------------------------------------------------------------
-- List of prime numbers 

-- | Infinite list of primes, using the TMWE algorithm.
primes :: [Integer]
primes = primesTMWE

-- | A relatively simple but still quite fast implementation of list of primes.
-- By Will Ness <http://www.haskell.org/pipermail/haskell-cafe/2009-November/068441.html>
primesSimple :: [Integer]
primesSimple = 2 : 3 : sieve 0 primes' 5 where
  primes' = tail primesSimple
  sieve k (p:ps) x = noDivs k h ++ sieve (k+1) ps (t+2) where
    t = p*p 
    h = [x,x+2..t-2]
  noDivs k = filter (\x -> all (\y -> rem x y /= 0) (take k primes'))
  
-- | List of primes, using tree merge with wheel. Code by Will Ness.
primesTMWE :: [Integer]
primesTMWE = 2:3:5:7: gaps 11 wheel (fold3t $ roll 11 wheel primes') where                                                             

  primes' = 11: gaps 13 (tail wheel) (fold3t $ roll 11 wheel primes')
  fold3t ((x:xs): ~(ys:zs:t)) 
    = x : union xs (union ys zs) `union` fold3t (pairs t)            
  pairs ((x:xs):ys:t) = (x : union xs ys) : pairs t 
  wheel = 2:4:2:4:6:2:6:4:2:4:6:6:2:6:4:2:6:4:6:8:4:2:4:2:  
          4:8:6:4:6:2:4:6:2:6:6:4:2:4:6:2:6:4:2:4:2:10:2:10:wheel 
  gaps k ws@(w:t) cs@ ~(c:u) 
    | k==c  = gaps (k+w) t u              
    | True  = k : gaps (k+w) t cs  
  roll k ws@(w:t) ps@ ~(p:u) 
    | k==p  = scanl (\c d->c+p*d) (p*p) ws : roll (k+w) t u              
    | True  = roll (k+w) t ps   

  minus xxs@(x:xs) yys@(y:ys) = case compare x y of 
    LT -> x : minus xs  yys
    EQ ->     minus xs  ys 
    GT ->     minus xxs ys
  minus xs [] = xs
  minus [] _  = []
  
  union xxs@(x:xs) yys@(y:ys) = case compare x y of 
    LT -> x : union xs  yys
    EQ -> x : union xs  ys 
    GT -> y : union xxs ys
  union xs [] = xs
  union [] ys =ys

--------------------------------------------------------------------------------
-- Prime factorization

-- | Groups integer factors. Example: from [2,2,2,3,3,5] we produce [(2,3),(3,2),(5,1)]  
groupIntegerFactors :: [Integer] -> [(Integer,Int)]
groupIntegerFactors = map f . group . sort where
  f xs = (head xs, length xs)

-- | The naive trial division algorithm.
integerFactorsTrialDivision :: Integer -> [Integer]
integerFactorsTrialDivision n 
  | n<1 = error "integerFactorsTrialDivision: n should be at least 1"
  | otherwise = go primes n 
  where
    go _  1 = []
    go rs k = sub ps k where
      sub [] k = [k]
      sub qqs@(q:qs) k = case mod k q of
        0 -> q : go qqs (div k q)
        _ -> sub qs k
      ps = takeWhile (\p -> p*p <= k) rs  
{-
    go 1 = []
    go k = sub ps k where
      sub [] k = [k]
      sub (q:qs) k = case mod k q of
        0 -> q : go (div k q)
        _ -> sub qs k
      ps = takeWhile (\p -> p*p <= k) primes
-}

{-    
-- brute force testing of factors
ifactorsTest :: (Integer -> [Integer]) -> Integer -> Bool
ifactorsTest alg n = and [ product (alg k) == k | k<-[1..n] ]   
-}

--------------------------------------------------------------------------------
-- Integer logarithm

-- | Largest integer @k@ such that @2^k@ is smaller or equal to @n@
integerLog2 :: Integer -> Integer
integerLog2 n = go n where
  go 0 = -1
  go k = 1 + go (shiftR k 1)

-- | Smallest integer @k@ such that @2^k@ is larger or equal to @n@
ceilingLog2 :: Integer -> Integer
ceilingLog2 0 = 0
ceilingLog2 n = 1 + go (n-1) where
  go 0 = -1
  go k = 1 + go (shiftR k 1)
  
--------------------------------------------------------------------------------
-- Integer square root

isSquare :: Integer -> Bool
isSquare n = 
  if (fromIntegral $ mod n 32) `elem` rs 
    then snd (integerSquareRoot' n) == 0
    else False
  where
    rs = [0,1,4,9,16,17,25] :: [Int]
    
-- | Integer square root (largest integer whose square is smaller or equal to the input)
-- using Newton's method, with a faster (for large numbers) inital guess based on bit shifts.
integerSquareRoot :: Integer -> Integer
integerSquareRoot = fst . integerSquareRoot'

-- | Smallest integer whose square is larger or equal to the input
ceilingSquareRoot :: Integer -> Integer
ceilingSquareRoot n = (if r>0 then u+1 else u) where (u,r) = integerSquareRoot' n 

-- | We also return the excess residue; that is
--
-- > (a,r) = integerSquareRoot' n
-- 
-- means that
--
-- > a*a + r = n
-- > a*a <= n < (a+1)*(a+1)
integerSquareRoot' :: Integer -> (Integer,Integer)
integerSquareRoot' n
  | n<0 = error "integerSquareRoot: negative input"
  | n<2 = (n,0)
  | otherwise = go firstGuess 
  where
    k = integerLog2 n
    firstGuess = 2^(div (k+2) 2) -- !! note that (div (k+1) 2) is NOT enough !!
    go a = 
      if m < a
        then go a' 
        else (a, r + a*(m-a))
      where
        (m,r) = divMod n a
        a' = div (m + a) 2

-- | Newton's method without an initial guess. For very small numbers (<10^10) it
-- is somewhat faster than the above version.
integerSquareRootNewton' :: Integer -> (Integer,Integer)
integerSquareRootNewton' n
  | n<0 = error "integerSquareRootNewton: negative input"
  | n<2 = (n,0)
  | otherwise = go (div n 2) 
  where
    go a = 
      if m < a
        then go a' 
        else (a, r + a*(m-a))
      where
        (m,r) = divMod n a
        a' = div (m + a) 2

{-
-- brute force test of integer square root
isqrt_test n1 n2 = 
  [ k 
  | k<-[n1..n2] 
  , let (a,r) = integerSquareRoot' k
  , (a*a+r/=k) || (a*a>k) || (a+1)*(a+1)<=k 
  ]
-}

--------------------------------------------------------------------------------
-- Modulo @m@ arithmetic

-- | Efficient powers modulo m.
-- 
-- > powerMod a k m == (a^k) `mod` m
powerMod :: Integer -> Integer -> Integer -> Integer
powerMod a' k m = {- debug bs $ -} go a bs where

  bs = bin k

  bin 0 = []
  bin x = (x .&. 1 /= 0) : bin (shiftR x 1)

  a = mod a' m

  go _ [] = 1
  go x (b:bs) = -- debug (x,b) $ 
    if b 
      then mod (x*rest) m
      else rest
    where 
      rest = go (mod (x*x) m) bs 
      
--------------------------------------------------------------------------------
-- Prime testing
 
-- | Miller-Rabin Primality Test (taken from Haskell wiki). 
-- We test the primality of the first argument @n@ by using the second argument @a@ as a candidate witness.
-- If it returs @False@, then @n@ is composite. If it returns @True@, then @n@ is either prime or composite.
--
-- A random choice between @2@ and @(n-2)@ is a good choice for @a@.
millerRabinPrimalityTest :: Integer -> Integer -> Bool
millerRabinPrimalityTest n a
  | a <= 1 || a >= n-1 = 
      error $ "millerRabinPrimalityTest: a out of range (" ++ show a ++ " for "++ show n ++ ")" 
  | n < 2 = False
  | even n = False
  | b0 == 1 || b0 == n' = True
  | otherwise = iter (tail b)
  where
    n' = n-1
    (k,m) = find2km n'
    b0 = powMod n a m
    b = take (fromIntegral k) $ iterate (squareMod n) b0
    iter [] = False
    iter (x:xs)
      | x == 1 = False
      | x == n' = True
      | otherwise = iter xs


{-# SPECIALIZE find2km :: Integer -> (Integer,Integer) #-}
find2km :: Integral a => a -> (a,a)
find2km n = f 0 n where 
  f k m
    | r == 1 = (k,m)
    | otherwise = f (k+1) q
    where (q,r) = quotRem m 2        
 
{-# SPECIALIZE pow' :: (Integer -> Integer -> Integer) -> (Integer -> Integer) -> Integer -> Integer -> Integer #-}
pow' :: (Num a, Integral b) => (a -> a -> a) -> (a -> a) -> a -> b -> a
pow' _ _ _ 0 = 1
pow' mul sq x' n' = f x' n' 1 where 
  f x n y
    | n == 1 = x `mul` y
    | r == 0 = f x2 q y
    | otherwise = f x2 q (x `mul` y)
    where
      (q,r) = quotRem n 2
      x2 = sq x
 
{-# SPECIALIZE mulMod :: Integer -> Integer -> Integer -> Integer #-}
mulMod :: Integral a => a -> a -> a -> a
mulMod a b c = (b * c) `mod` a

{-# SPECIALIZE squareMod :: Integer -> Integer -> Integer #-}
squareMod :: Integral a => a -> a -> a
squareMod a b = (b * b) `rem` a

{-# SPECIALIZE powMod :: Integer -> Integer -> Integer -> Integer #-}
powMod :: Integral a => a -> a -> a -> a
powMod m = pow' (mulMod m) (squareMod m)

--------------------------------------------------------------------------------
