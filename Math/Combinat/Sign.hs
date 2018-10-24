
-- | Signs

{-# LANGUAGE CPP, BangPatterns #-}
module Math.Combinat.Sign where

--------------------------------------------------------------------------------

import Data.Monoid

-- Semigroup became a superclass of Monoid
#if MIN_VERSION_base(4,11,0)     
import Data.Foldable
import Data.Semigroup
#endif

import System.Random

--------------------------------------------------------------------------------

data Sign
  = Plus                            -- hmm, this way @Plus < Minus@, not sure about that
  | Minus
  deriving (Eq,Ord,Show,Read)

--------------------------------------------------------------------------------

-- Semigroup became a superclass of Monoid
#if MIN_VERSION_base(4,11,0)        

instance Semigroup Sign where
  (<>)    = mulSign
  sconcat = foldl1 mulSign

instance Monoid Sign where
  mempty  = Plus
  mconcat = productOfSigns

#else

instance Monoid Sign where
  mempty  = Plus
  mappend = mulSign
  mconcat = productOfSigns

#endif

--------------------------------------------------------------------------------

instance Random Sign where
  random        g = let (b,g') = random g in (if b    then Plus else Minus, g')
  randomR (u,v) g = let (y,g') = random g in (if u==v then u    else y    , g') 

isPlus, isMinus :: Sign -> Bool
isPlus  s = case s of { Plus  -> True ; _ -> False }
isMinus s = case s of { Minus -> True ; _ -> False }

{-# SPECIALIZE signValue :: Sign -> Int     #-}
{-# SPECIALIZE signValue :: Sign -> Integer #-}

-- | @+1@ or @-1@
signValue :: Num a => Sign -> a
signValue s = case s of 
  Plus  ->  1 
  Minus -> -1 

{-# SPECIALIZE signed :: Sign -> Int     -> Int     #-}
{-# SPECIALIZE signed :: Sign -> Integer -> Integer #-}

-- | Negate the second argument if the first is 'Minus'
signed :: Num a => Sign -> a -> a
signed s y = case s of
  Plus  -> y
  Minus -> negate y

{-# SPECIALIZE paritySign :: Int     -> Sign #-}
{-# SPECIALIZE paritySign :: Integer -> Sign #-}

-- | 'Plus' if even, 'Minus' if odd
paritySign :: Integral a => a -> Sign
paritySign x = if even x then Plus else Minus 

{-# SPECIALIZE paritySignValue :: Int     -> Integer #-}
{-# SPECIALIZE paritySignValue :: Integer -> Integer #-}

-- | @(-1)^k@
paritySignValue :: Integral a => a -> Integer
paritySignValue k = if odd k then (-1) else 1

{-# SPECIALIZE negateIfOdd :: Int     -> Int     -> Int     #-}
{-# SPECIALIZE negateIfOdd :: Int     -> Integer -> Integer #-}

-- | Negate the second argument if the first is odd
negateIfOdd :: (Integral a, Num b) => a -> b -> b
negateIfOdd k y = if even k then y else negate y

oppositeSign :: Sign -> Sign
oppositeSign s = case s of
  Plus  -> Minus
  Minus -> Plus

mulSign :: Sign -> Sign -> Sign
mulSign s1 s2 = case s1 of
  Plus  -> s2
  Minus -> oppositeSign s2

productOfSigns :: [Sign] -> Sign
productOfSigns = go Plus where
  go !acc []     = acc
  go !acc (x:xs) = case x of
    Plus  -> go acc xs
    Minus -> go (oppositeSign acc) xs

--------------------------------------------------------------------------------
