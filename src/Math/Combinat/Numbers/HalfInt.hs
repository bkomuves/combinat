{-# LANGUAGE FlexibleInstances #-}

-- | Half-integers
module Math.Combinat.Numbers.HalfInt where

import Math.Combinat.Helper (safeZip)


-- | The type of half-integers (internally represented by their double)
newtype HalfInt
  = HalfInt Int
  deriving (Eq,Ord)

half :: HalfInt
half = HalfInt 1

divByTwo :: Int -> HalfInt
divByTwo = HalfInt

mulByTwo :: HalfInt -> Int
mulByTwo (HalfInt n) = n

scaleBy :: Int -> HalfInt -> HalfInt
scaleBy k (HalfInt n) = HalfInt (k*n)

instance Show HalfInt where
  show (HalfInt n) = case divMod n 2 of
    (k,0) -> show k
    (_,1) -> show n ++ "/2"

{-# LANGUAGE FlexibleInstances #-}
instance Num HalfInt where
  fromInteger = HalfInt . (*2) . fromInteger
  a + b = divByTwo $ mulByTwo a + mulByTwo b
  a - b = divByTwo $ mulByTwo a - mulByTwo b
  a * b = case divMod (mulByTwo a * mulByTwo b) 2 of
            (k,0) -> HalfInt k
            _     -> error "the result of multiplication is not a half-integer"
  negate = divByTwo . negate . mulByTwo
  signum = divByTwo . signum . mulByTwo
  abs    = divByTwo . abs    . mulByTwo

--------------------------------------------------------------------------------
-- * Vectors of half-integers

type HalfVec = [HalfInt]

instance Num HalfVec where
  fromInteger = error "HalfVec/fromInteger"
  (+) = safeZip (+)
  (-) = safeZip (-)
  (*) = safeZip (*)
  negate = map negate
  abs    = map abs
  signum = map signum

scaleVec :: Int -> HalfVec -> HalfVec
scaleVec k = map (scaleBy k)

negateVec :: HalfVec -> HalfVec
negateVec = map negate

dotProd :: HalfVec -> HalfVec -> HalfInt
dotProd xs ys = let
  f a b = mulByTwo a * mulByTwo b
  in case divMod (sum $ safeZip f xs ys) 2 of
    (n, 0) -> divByTwo n
    _ -> error "the result of dot product is not a half-integer"
  



