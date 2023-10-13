
-- | Operations on integers

module Math.Combinat.Numbers.Integers 
  ( -- * Integer logarithm
    integerLog2
  , ceilingLog2
    -- * Integer square root
  , isSquare
  , integerSquareRoot
  , ceilingSquareRoot
  , integerSquareRoot' 
  , integerSquareRootNewton'
  )
  where

--------------------------------------------------------------------------------

-- import Math.Combinat.Numbers

import Data.List ( group , sort )
import Data.Bits

import System.Random

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

