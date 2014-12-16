
-- | Signs

{-# LANGUAGE BangPatterns #-}
module Math.Combinat.Sign where

--------------------------------------------------------------------------------

import Data.Monoid

--------------------------------------------------------------------------------

data Sign
  = Plus
  | Minus
  deriving (Eq,Ord,Show,Read)

instance Monoid Sign where
  mempty  = Plus
  mappend = mulSign
  mconcat = productOfSigns

signValue :: Num a => Sign -> a
signValue s = case s of 
  Plus  ->  1 
  Minus -> -1 

paritySign :: Integral a => a -> Sign
paritySign x = if even x then Plus else Minus 

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
