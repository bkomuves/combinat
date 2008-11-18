
module Math.Combinat.Helper where

import Debug.Trace

debug :: Show a => a -> b -> b
debug x y = trace (show x) y

{-# SPECIALIZE swap :: (a,a) -> (a,a) #-}
{-# SPECIALIZE swap :: (Int,Int) -> (Int,Int) #-}
swap :: (a,b) -> (b,a)
swap (x,y) = (y,x)

-- helps testing the random rutines 
count :: Eq a => a -> [a] -> Int
count x xs = length $ filter (==x) xs

fromJust :: Maybe a -> a
fromJust (Just x) = x
fromJust Nothing = error "fromJust: Nothing"

-- iterated function application
nest :: Int -> (a -> a) -> a -> a
nest 0 _ x = x
nest n f x = nest (n-1) f (f x)

reverseOrdering :: Ordering -> Ordering
reverseOrdering LT = GT
reverseOrdering GT = LT
reverseOrdering EQ = EQ

reverseCompare :: Ord a => a -> a -> Ordering
reverseCompare x y = reverseOrdering $ compare x y

factorial :: Int -> Integer
factorial 0 = 1
factorial n = product [1..fromIntegral n]

binomial :: Int -> Int -> Integer
binomial n k 
  | k > n = 0
  | k < 0 = 0
  | k > (n `div` 2) = binomial n (n-k)
  | otherwise = (product [n'-k'+1 .. n']) `div` (product [1..k'])
  where 
    k' = fromIntegral k
    n' = fromIntegral n
    
intToBool :: Int -> Bool
intToBool 0 = False
intToBool 1 = True
intToBool _ = error "intToBool"

boolToInt :: Bool -> Int 
boolToInt False = 0
boolToInt True  = 1

unfold1 :: (a -> Maybe a) -> a -> [a]
unfold1 f x = case f x of 
  Nothing -> [x] 
  Just y  -> x : unfold1 f y 
  
unfold :: (b -> (a,Maybe b)) -> b -> [a]
unfold f y = let (x,m) = f y in case m of 
  Nothing -> [x]
  Just y' -> x : unfold f y'

unfoldEither :: (b -> Either c (b,a)) -> b -> (c,[a])
unfoldEither f y = case f y of
  Left z -> (z,[])
  Right (y,x) -> let (z,xs) = unfoldEither f y in (z,x:xs)
  