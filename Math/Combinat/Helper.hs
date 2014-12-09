
-- | Miscellaneous helper functions

module Math.Combinat.Helper where

--------------------------------------------------------------------------------

import Control.Monad

import Data.List
import Data.Ord

import Data.Set (Set) ; import qualified Data.Set as Set
import Data.Map (Map) ; import qualified Data.Map as Map

import Debug.Trace

--------------------------------------------------------------------------------
-- * debugging

debug :: Show a => a -> b -> b
debug x y = trace ("-- " ++ show x ++ "\n") y

--------------------------------------------------------------------------------
-- * pairs

{-# SPECIALIZE swap :: (a  ,a  ) -> (a  ,a  ) #-}
{-# SPECIALIZE swap :: (Int,Int) -> (Int,Int) #-}
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

--------------------------------------------------------------------------------
-- * equality and ordering 

equating :: Eq b => (a -> b) -> a -> a -> Bool
equating f x y = (f x == f y)

reverseOrdering :: Ordering -> Ordering
reverseOrdering LT = GT
reverseOrdering GT = LT
reverseOrdering EQ = EQ

reverseCompare :: Ord a => a -> a -> Ordering
reverseCompare x y = reverseOrdering $ compare x y

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
nest 0 _ x = x
nest n f x = nest (n-1) f (f x)

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
    
  