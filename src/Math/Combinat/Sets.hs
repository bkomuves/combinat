
-- | Subsets. 

{-# LANGUAGE BangPatterns, Rank2Types #-}
module Math.Combinat.Sets 
  ( 
    -- * Choices
    choose_ , choose , choose' , choose'' , chooseTagged
    -- * Compositions
  , combine , compose
    -- * Tensor products
  , tuplesFromList
  , listTensor
    -- * Sublists
  , kSublists
  , sublists
  , countKSublists
  , countSublists
    -- * Random choice
  , randomChoice
  ) 
  where

--------------------------------------------------------------------------------

import Data.List ( sort , mapAccumL )
import System.Random

import Control.Monad
import Control.Monad.ST
import Data.Array.ST
import Data.Array.MArray

-- import Data.Map (Map)
-- import qualified Data.Map as Map

import Math.Combinat.Numbers ( binomial )
import Math.Combinat.Helper  ( swap )

--------------------------------------------------------------------------------
-- * choices


-- | @choose_ k n@ returns all possible ways of choosing @k@ disjoint elements from @[1..n]@
--
-- > choose_ k n == choose k [1..n]
--
choose_ :: Int -> Int -> [[Int]]
choose_ k n  = if n<0 || k<0
  then error "choose_: n and k should nonnegative"
  else if k>n || k<0 
    then []
    else choose k [1..n]

-- | All possible ways to choose @k@ elements from a list, without
-- repetitions. \"Antisymmetric power\" for lists. Synonym for 'kSublists'.
choose :: Int -> [a] -> [[a]]
choose 0 _  = [[]]
choose k [] = []
choose k (x:xs) = map (x:) (choose (k-1) xs) ++ choose k xs  

-- | A version of 'choose' which also returns the complementer sets.
--
-- > choose k = map fst . choose' k
--
choose' :: Int -> [a] -> [([a],[a])]
choose' 0 xs = [([],xs)]
choose' k [] = []
choose' k (x:xs) = map f (choose' (k-1) xs) ++ map g (choose' k xs) where
  f (as,bs) = (x:as ,   bs)
  g (as,bs) = (  as , x:bs)

-- | Another variation of 'choose''. This satisfies
--
-- > choose'' k == map (\(xs,ys) -> (map fst xs, map snd ys)) . choose' k
--
choose'' :: Int -> [(a,b)] -> [([a],[b])]
choose'' 0 xys = [([] , map snd xys)]
choose'' k []  = []
choose'' k ((x,y):xs) = map f (choose'' (k-1) xs) ++ map g (choose'' k xs) where
  f (as,bs) = (x:as ,   bs)
  g (as,bs) = (  as , y:bs)

-- | Another variation on 'choose' which tags the elements based on whether they are part of
-- the selected subset ('Right') or not ('Left'):
--
-- > choose k = map rights . chooseTagged k
--
chooseTagged :: Int -> [a] -> [[Either a a]]
chooseTagged 0 xs = [map Left xs]
chooseTagged k [] = []
chooseTagged k (x:xs) = map f (chooseTagged (k-1) xs) ++ map g (chooseTagged k xs) where
  f eis = Right x : eis
  g eis = Left  x : eis

-- | All possible ways to choose @k@ elements from a list, /with repetitions/. 
-- \"Symmetric power\" for lists. See also "Math.Combinat.Compositions".
-- TODO: better name?
combine :: Int -> [a] -> [[a]]
combine 0 _  = [[]]
combine k [] = []
combine k xxs@(x:xs) = map (x:) (combine (k-1) xxs) ++ combine k xs  

-- | A synonym for 'combine'.
compose :: Int -> [a] -> [[a]]
compose = combine

--------------------------------------------------------------------------------
-- * tensor products

-- | \"Tensor power\" for lists. Special case of 'listTensor':
--
-- > tuplesFromList k xs == listTensor (replicate k xs)
-- 
-- See also "Math.Combinat.Tuples".
-- TODO: better name?
tuplesFromList :: Int -> [a] -> [[a]]
tuplesFromList 0 _  = [[]]
tuplesFromList k xs = [ (y:ys) | ys <- tuplesFromList (k-1) xs , y <- xs ]
--the order seems to be very important, the wrong order causes a memory leak!
--tuplesFromList k xs = [ (y:ys) | y <- xs, ys <- tuplesFromList (k-1) xs ]
 
-- | \"Tensor product\" for lists.
listTensor :: [[a]] -> [[a]]
listTensor [] = [[]]
listTensor (xs:xss) = [ y:ys | ys <- listTensor xss , y <- xs ]
--the order seems to be very important, the wrong order causes a memory leak!
--listTensor (xs:xss) = [ y:ys | y <- xs, ys <- listTensor xss ]

--------------------------------------------------------------------------------
-- * sublists

-- | Sublists of a list having given number of elements. Synonym for 'choose'.
kSublists :: Int -> [a] -> [[a]]
kSublists = choose

-- | @# = \binom { n } { k }@.
countKSublists :: Int -> Int -> Integer
countKSublists k n = binomial n k 

-- | All sublists of a list.
sublists :: [a] -> [[a]]
sublists [] = [[]]
sublists (x:xs) = sublists xs ++ map (x:) (sublists xs)  
--the order seems to be very important, the wrong order causes a memory leak!
--sublists (x:xs) = map (x:) (sublists xs) ++ sublists xs 

-- | @# = 2^n@.
countSublists :: Int -> Integer
countSublists n = 2 ^ n

--------------------------------------------------------------------------------
-- * random choice

-- | @randomChoice k n@ returns a uniformly random choice of @k@ elements from the set @[1..n]@
--
-- Example:
--
-- > do
-- >   cs <- replicateM 10000 (getStdRandom (randomChoice 3 7))
-- >   mapM_ print $ histogram cs
-- 
randomChoice :: RandomGen g => Int -> Int -> g -> ([Int],g)
randomChoice k n g0 = 
  if k>n || k<0 
    then error "randomChoice: k out of range" 
    else (makeChoiceFromIndicesKnuth n as, g1) 
  where
    -- choose numbers from [1..n], [1..n-1], [1..n-2] etc
    (g1,as) = mapAccumL (\g m -> swap (randomR (1,m) g)) g0 [n,n-1..n-k+1]   

--------------------------------------------------------------------------------
   
-- | From a list of $k$ numbers, where the first is in the interval @[1..n]@, 
-- the second in @[1..n-1]@, the third in @[1..n-2]@, we create a size @k@ subset of @n@.
--
-- Knuth's method. The first argument is the number @n@.
--
makeChoiceFromIndicesKnuth :: Int -> [Int] -> [Int]
makeChoiceFromIndicesKnuth n xs = 
  runST $ do
    arr <- newArray_ (1,n) :: forall s. ST s (STUArray s Int Int)
    forM_ [1..n] $ \(!j) -> writeArray arr j j
    forM_ (zip [n,n-1..] xs) $ \(!j,!i) -> do
      a <- readArray arr j
      b <- readArray arr i
      writeArray arr j b
      writeArray arr i a
    sel <- forM (zip [n,n-1..] xs) $ \(!j,_) -> readArray arr j
    return (sort sel)

-- | From a list of $k$ numbers, where the first is in the interval @[1..n]@, 
-- the second in @[1..n-1]@, the third in @[1..n-2]@, we create a size @k@ subset of @n@.
makeChoiceFromIndicesNaive :: [Int] -> [Int]
makeChoiceFromIndicesNaive = sort . go [] where

  go :: [Int] -> [Int] -> [Int]
  go acc (b:bs) = b' : go (insert b' acc) bs where b' = skip b acc
  go _   [] = []

  -- skip over the already occupied positions. Second argument should be a sorted list
  skip :: Int -> [Int] -> Int
  skip x (y:ys) = if x>=y then skip (x+1) ys else x
  skip x [] = x

  -- insert into a sorted list
  insert :: Int -> [Int] -> [Int]
  insert x (y:ys) = if x<=y then x:y:ys else y : insert x ys
  insert x [] = [x]

--------------------------------------------------------------------------------

