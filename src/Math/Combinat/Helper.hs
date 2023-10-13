
-- | Miscellaneous helper functions used internally

{-# LANGUAGE BangPatterns, PolyKinds, GeneralizedNewtypeDeriving #-}
module Math.Combinat.Helper where

--------------------------------------------------------------------------------

import Control.Monad
import Control.Applicative ( Applicative(..) )    -- required before AMP (before GHC 7.10)
import Data.Functor.Identity

import Data.List
import Data.Ord
import Data.Proxy

import Data.Set (Set) ; import qualified Data.Set as Set
import Data.Map (Map) ; import qualified Data.Map as Map

import Debug.Trace

import System.Random
import Control.Monad.Trans.State

--------------------------------------------------------------------------------
-- * debugging

debug :: Show a => a -> b -> b
debug x y = trace ("-- " ++ show x ++ "\n") y

--------------------------------------------------------------------------------
-- * pairs

swap :: (a,b) -> (b,a)
swap (x,y) = (y,x)

pairs :: [a] -> [(a,a)]
pairs = go where
  go (x:xs@(y:_)) = (x,y) : go xs
  go _            = []

pairsWith :: (a -> a -> b) -> [a] -> [b]
pairsWith f = go where
  go (x:xs@(y:_)) = f x y : go xs
  go _            = []

--------------------------------------------------------------------------------
-- * lists

{-# SPECIALIZE sum' :: [Int]     -> Int     #-}
{-# SPECIALIZE sum' :: [Integer] -> Integer #-}
sum' :: Num a => [a] -> a
sum' = foldl' (+) 0

interleave :: [a] -> [a] -> [a]
interleave (x:xs) (y:ys) = x : y : interleave xs ys
interleave [x]    []     = x : []
interleave []     []     = []
interleave _      _      = error "interleave: shouldn't happen"

evens, odds :: [a] -> [a] 
evens (x:xs) = x : odds xs
evens [] = []
odds (x:xs) = evens xs
odds [] = []

--------------------------------------------------------------------------------
-- * multiplication

-- | Product of list of integers, but in interleaved order (for a list of big numbers,
-- it should be faster than the linear order)
productInterleaved :: [Integer] -> Integer
productInterleaved = go where
  go []    = 1
  go [x]   = x
  go [x,y] = x*y
  go list  = go (evens list) * go (odds list)

-- | Faster implementation of @product [ i | i <- [a+1..b] ]@
productFromTo :: Integral a => a -> a -> Integer
productFromTo = go where
  go !a !b 
    | dif < 1     = 1
    | dif < 5     = product [ fromIntegral i | i<-[a+1..b] ]
    | otherwise   = go a half * go half b
    where
      dif  = b - a
      half = div (a+b+1) 2

-- | Faster implementation of product @[ i | i <- [a+1,a+3,..b] ]@
productFromToStride2 :: Integral a => a -> a -> Integer
productFromToStride2 = go where
  go !a !b 
    | dif < 1     = 1
    | dif < 9     = product [ fromIntegral i | i<-[a+1,a+3..b] ]
    | otherwise   = go a half * go half b
    where
      dif  = b - a
      half = a + 2*(div dif 4)

--------------------------------------------------------------------------------
-- * equality and ordering 

equating :: Eq b => (a -> b) -> a -> a -> Bool
equating f x y = (f x == f y)

reverseOrdering :: Ordering -> Ordering
reverseOrdering LT = GT
reverseOrdering GT = LT
reverseOrdering EQ = EQ

reverseComparing :: Ord b => (a -> b) -> a -> a -> Ordering
reverseComparing f x y = compare (f y) (f x)

reverseCompare :: Ord a => a -> a -> Ordering
reverseCompare x y = compare y x   -- reverseOrdering $ compare x y

reverseSort :: Ord a => [a] -> [a]
reverseSort = sortBy reverseCompare

groupSortBy :: (Eq b, Ord b) => (a -> b) -> [a] -> [[a]]
groupSortBy f = groupBy (equating f) . sortBy (comparing f) 

nubOrd :: Ord a => [a] -> [a]
nubOrd = worker Set.empty where
  worker _ [] = []
  worker s (x:xs) 
    | Set.member x s = worker s xs
    | otherwise      = x : worker (Set.insert x s) xs

--------------------------------------------------------------------------------
-- * increasing \/ decreasing sequences

{-# SPECIALIZE isWeaklyIncreasing :: [Int] -> Bool #-}
isWeaklyIncreasing :: Ord a => [a] -> Bool
isWeaklyIncreasing = go where
  go xs = case xs of 
    (a:rest@(b:_)) -> a <= b && go rest
    [_]            -> True
    []             -> True

{-# SPECIALIZE isStrictlyIncreasing :: [Int] -> Bool #-}
isStrictlyIncreasing :: Ord a => [a] -> Bool
isStrictlyIncreasing = go where
  go xs = case xs of 
    (a:rest@(b:_)) -> a < b && go rest
    [_]            -> True
    []             -> True

{-# SPECIALIZE isWeaklyDecreasing :: [Int] -> Bool #-}
isWeaklyDecreasing :: Ord a => [a] -> Bool
isWeaklyDecreasing = go where
  go xs = case xs of 
    (a:rest@(b:_)) -> a >= b && go rest
    [_]            -> True
    []             -> True

{-# SPECIALIZE isStrictlyDecreasing :: [Int] -> Bool #-}
isStrictlyDecreasing :: Ord a => [a] -> Bool
isStrictlyDecreasing = go where
  go xs = case xs of 
    (a:rest@(b:_)) -> a > b && go rest
    [_]            -> True
    []             -> True

--------------------------------------------------------------------------------
-- * first \/ last 

-- | The boolean argument will @True@ only for the last element
mapWithLast :: (Bool -> a -> b) -> [a] -> [b]
mapWithLast f = go where
  go (x : []) = f True  x : []
  go (x : xs) = f False x : go xs

mapWithFirst :: (Bool -> a -> b) -> [a] -> [b]
mapWithFirst f = go True where
  go b (x:xs) = f b x : go False xs 
  
mapWithFirstLast :: (Bool -> Bool -> a -> b) -> [a] -> [b]
mapWithFirstLast f = go True where
  go b (x : []) = f b True  x : []
  go b (x : xs) = f b False x : go False xs

--------------------------------------------------------------------------------
-- * older helpers for ASCII drawing

-- | extend lines with spaces so that they have the same line
mkLinesUniformWidth :: [String] -> [String]
mkLinesUniformWidth old = zipWith worker ls old where
  ls = map length old
  m  = maximum ls
  worker l s = s ++ replicate (m-l) ' '

mkBlocksUniformHeight :: [[String]] -> [[String]]
mkBlocksUniformHeight old = zipWith worker ls old where
  ls = map length old
  m  = maximum ls
  worker l s = s ++ replicate (m-l) ""
    
mkUniformBlocks :: [[String]] -> [[String]] 
mkUniformBlocks = map mkLinesUniformWidth . mkBlocksUniformHeight
    
hConcatLines :: [[String]] -> [String]
hConcatLines = map concat . transpose . mkUniformBlocks

vConcatLines :: [[String]] -> [String]  
vConcatLines = concat

--------------------------------------------------------------------------------
-- * counting

-- helps testing the random rutines 
count :: Eq a => a -> [a] -> Int
count x xs = length $ filter (==x) xs

histogram :: (Eq a, Ord a) => [a] -> [(a,Int)]
histogram xs = Map.toList table where
  table = Map.fromListWith (+) [ (x,1) | x<-xs ] 

--------------------------------------------------------------------------------
-- * maybe

fromJust :: Maybe a -> a
fromJust (Just x) = x
fromJust Nothing = error "fromJust: Nothing"

--------------------------------------------------------------------------------
-- * bool

intToBool :: Int -> Bool
intToBool 0 = False
intToBool 1 = True
intToBool _ = error "intToBool"

boolToInt :: Bool -> Int 
boolToInt False = 0
boolToInt True  = 1

--------------------------------------------------------------------------------
-- * iteration
    
-- iterated function application
nest :: Int -> (a -> a) -> a -> a
nest !0 _ x = x
nest !n f x = nest (n-1) f (f x)

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
  
unfoldM :: Monad m => (b -> m (a,Maybe b)) -> b -> m [a]
unfoldM f y = do
  (x,m) <- f y
  case m of
    Nothing -> return [x]
    Just y' -> do
      xs <- unfoldM f y'
      return (x:xs)

mapAccumM :: Monad m => (acc -> x -> m (acc, y)) -> acc -> [x] -> m (acc, [y])
mapAccumM _ s [] = return (s, [])
mapAccumM f s (x:xs) = do
  (s1,y) <- f s x
  (s2,ys) <- mapAccumM f s1 xs
  return (s2, y:ys)

--------------------------------------------------------------------------------
-- * long zipwith    

longZipWith :: a -> b -> (a -> b -> c) -> [a] -> [b] -> [c]
longZipWith a0 b0 f = go where
  go (x:xs) (y:ys)  =   f x  y : go xs ys
  go []     ys      = [ f a0 y | y<-ys ]
  go xs     []      = [ f x b0 | x<-xs ]

{-
longZipWithZero :: (Num a, Num b) => (a -> b -> c) -> [a] -> [b] -> [c]
longZipWithZero = longZipWith 0 0 
-}

--------------------------------------------------------------------------------
-- * random

-- | A simple random monad to make life suck less
type Rand g = RandT g Identity

runRand :: Rand g a -> g -> (a,g)
runRand action g = runIdentity (runRandT action g)

flipRunRand :: Rand s a -> s -> (s,a)
flipRunRand action g = runIdentity (flipRunRandT action g)


-- | The Rand monad transformer
newtype RandT g m a = RandT (StateT g m a) deriving (Functor,Applicative,Monad)

runRandT :: RandT g m a -> g -> m (a,g)
runRandT (RandT stuff) = runStateT stuff

-- | This may be occasionally useful
flipRunRandT :: Monad m => RandT s m a -> s -> m (s,a)
flipRunRandT action ini = liftM swap $ runRandT action ini


-- | Puts a standard-conforming random function into the monad
rand :: (g -> (a,g)) -> Rand g a
rand user = RandT (state user)

randRoll :: (RandomGen g, Random a) => Rand g a
randRoll = rand random

randChoose :: (RandomGen g, Random a) => (a,a) -> Rand g a
randChoose uv = rand (randomR uv)

randProxy1 :: Rand g (f n) -> Proxy n -> Rand g (f n)
randProxy1 action _ = action

--------------------------------------------------------------------------------
