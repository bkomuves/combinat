
-- | Prime numbers and related number theoretical stuff.

module Math.Combinat.Numbers.Primes 
  ( -- * Elementary number theory
    divides
  , divisors, squareFreeDivisors, squareFreeDivisors_  
  , divisorSum , divisorSum'
  , moebiusMu , eulerTotient , liouvilleLambda
    -- * List of prime numbers
  , primes
  , primesSimple
  , primesTMWE
    -- * Prime factorization
  , factorize, factorizeNaive
  , productOfFactors
  , integerFactorsTrialDivision
  , groupIntegerFactors
    -- * Modulo @m@ arithmetic
  , powerMod
    -- * Prime testing
  , millerRabinPrimalityTest
  , isProbablyPrime
  , isVeryProbablyPrime
  )
  where

--------------------------------------------------------------------------------

import Data.List ( group , sort , foldl' )

import Math.Combinat.Sign
import Math.Combinat.Helper
import Math.Combinat.Numbers.Integers

-- import Math.Combinat.Sets   ( sublists )       -- cyclic dependency...
import Math.Combinat.Tuples ( tuples'  )

import Data.Bits

import System.Random

--------------------------------------------------------------------------------

-- | @d `divides` n@
divides :: Integer -> Integer -> Bool
divides d n = (mod n d == 0)

{-# SPECIALIZE moebiusMu :: Int     -> Int     #-}
{-# SPECIALIZE moebiusMu :: Integer -> Integer #-}
-- | The Moebius mu function
moebiusMu :: (Integral a, Num b) => a -> b
moebiusMu n 
  | any (>1) expos       =  0
  | even (length primes) =  1
  | otherwise            = -1
  where
    factors = groupIntegerFactors $ integerFactorsTrialDivision $ fromIntegral n
    (primes,expos) = unzip factors

{-# SPECIALIZE liouvilleLambda :: Int     -> Int     #-}
{-# SPECIALIZE liouvilleLambda :: Integer -> Integer #-}
-- | The Liouville lambda function
liouvilleLambda :: (Integral a, Num b) => a -> b
liouvilleLambda n = 
  if odd (foldl' (+) 0 $ map snd grps)
    then -1
    else  1
  where
    grps = groupIntegerFactors $ integerFactorsTrialDivision $ fromIntegral n

-- | Sum ofthe of the divisors
divisorSum :: Integer -> Integer
divisorSum n = foldl' (+) 0 [ d | d <- divisors n]

-- | Sum of @k@-th powers of the divisors
divisorSum' :: Int -> Integer -> Integer
divisorSum' k n = foldl' (+) 0 [ d^k | d <- divisors n]

-- | Euler's totient function
eulerTotient :: Integer -> Integer
eulerTotient n = div n prodp * prodp1 where
  grps   = groupIntegerFactors $ integerFactorsTrialDivision n
  ps     = map fst grps
  prodp  = foldl' (*) 1 [ p   | p <- ps ] 
  prodp1 = foldl' (*) 1 [ p-1 | p <- ps ] 

-- | Divisors of @n@ (note: the result is /not/ ordered!)
divisors :: Integer -> [Integer]
divisors n = [ f tup | tup <- tuples' expos ] where
  grps = groupIntegerFactors $ integerFactorsTrialDivision n
  (ps,expos) = unzip grps
  f es = foldl' (*) 1 $ zipWith (^) ps es

-- | List of square-free divisors together with their Mobius mu value
-- (note: the result is /not/ ordered!)
squareFreeDivisors :: Integer -> [(Integer,Sign)]
squareFreeDivisors n = map f (sublists primes) where
  grps = groupIntegerFactors $ integerFactorsTrialDivision n
  primes = map fst grps
  f ps = ( foldl' (*) 1 ps , if even (length ps) then Plus else Minus)

-- | List of square-free divisors 
-- (note: the result is /not/ ordered!)
squareFreeDivisors_ :: Integer -> [Integer]
squareFreeDivisors_ n = map f (sublists primes) where
  grps = groupIntegerFactors $ integerFactorsTrialDivision n
  primes = map fst grps
  f ps = foldl' (*) 1 ps

-- | To avoid cyclic dependencies, I made a local copy of this...
sublists :: [a] -> [[a]]
sublists [] = [[]]
sublists (x:xs) = sublists xs ++ map (x:) (sublists xs)  

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
  gaps k ws@(w:t) cs@(~(c:u))
    | k==c  = gaps (k+w) t u              
    | True  = k : gaps (k+w) t cs  
  roll k ws@(w:t) ps@(~(p:u)) 
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

factorize :: Integer -> [(Integer,Int)]
factorize = factorizeNaive

factorizeNaive :: Integer -> [(Integer,Int)]
factorizeNaive = groupIntegerFactors . integerFactorsTrialDivision

productOfFactors :: [(Integer,Int)] -> Integer
productOfFactors = productInterleaved . map (uncurry pow) where
  pow _ 0 = 1
  pow p 1 = p
  pow 2 n = shiftL 1 n
  pow p 2 = p*p
  pow p n = if even n
              then     (pow p (shiftR n 1))^2
              else p * (pow p (shiftR n 1))^2 

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

-- | For very small numbers, we use trial division, for larger numbers, we apply the 
-- Miller-Rabin primality test @log4(n)@ times, with candidate witnesses derived 
-- deterministically from @n@ using a pseudo-random sequence 
-- (which /should be/ based on a cryptographic hash function, but isn\'t, yet). 
--
-- Thus the candidate witnesses should behave essentially like random, but the 
-- resulting function is still a deterministic, pure function.
--
-- TODO: implement the hash sequence, at the moment we use 'System.Random' instead...
--
isProbablyPrime :: Integer -> Bool
isProbablyPrime n 
  | n < 2      = False
  | even n     = (n==2)
  | n < 1000   = length (integerFactorsTrialDivision n) == 1
  | otherwise  = and [ millerRabinPrimalityTest n a | a <- witnessList ]
  where
    log2n       = integerLog2 n 
    nchecks     = 1 + fromInteger (div log2n 2) :: Int
    witnessList = take nchecks pseudoRnds
    pseudoRnds  = 2 : [ a | a <- integerRndSequence n , a > 1 && a < (n-1) ]

-- | A more exhaustive version of 'isProbablyPrime', this one tests candidate
-- witnesses both the first log4(n) prime numbers and then log4(n) pseudo-random
-- numbers
isVeryProbablyPrime :: Integer -> Bool
isVeryProbablyPrime n
  | n < 2      = False
  | even n     = (n==2)
  | n < 1000   = length (integerFactorsTrialDivision n) == 1
  | otherwise  = and [ millerRabinPrimalityTest n a | a <- witnessList ]
  where
    log2n       = integerLog2 n 
    nchecks     = 1 + fromInteger (div log2n 2) :: Int
    witnessList = take nchecks primes ++ take nchecks pseudoRnds
    pseudoRnds  = [ a | a <- integerRndSequence (n+3) , a > 1 && a < (n-1) ]

--------------------------------------------------------------------------------

{-
-- | Given an integer @n@, we return an infinite sequence of pseudo-random integers 
-- between @0..n-1@, generated using a crypographic hash function.
--
integerHashSequence :: Integer -> [Integer]
integerHashSequence = error "integerHashSequence: not implemented yet"
-}

-- | Given an integer @n@, we initialize a system random generator with using a 
-- seed derived from @n@ (note that this uses at most 32 or 64 bits), and generate 
-- an infinite sequence of pseudo-random integers between @0..n-1@, generated by 
-- that random generator. 
--
-- Note that this is not really a preferred way of generating such sequences!
-- 
integerRndSequence :: Integer -> [Integer]
integerRndSequence n = randomRs (0,n-1) gen where
  gen = mkStdGen $ fromInteger (n + 17 * integerLog2 n)

--------------------------------------------------------------------------------
