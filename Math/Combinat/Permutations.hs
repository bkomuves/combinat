
-- | Permutations. See:
--   Donald E. Knuth: The Art of Computer Programming, vol 4, pre-fascicle 2B.
--
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Math.Combinat.Permutations 
  ( -- * Types
    Permutation
  , fromPermutation
  , permutationArray
  , toPermutationUnsafe
  , isPermutation
  , toPermutation
  , permutationSize
    -- * Disjoint cycles
  , fromDisjointCycles
  , disjointCyclesUnsafe
  , permutationToDisjointCycles
  , disjointCyclesToPermutation
  , isEvenPermutation
  , isOddPermutation
  , signOfPermutation
    -- * Permutation groups
  , permute
  , permuteList
  , multiply
  , inverse
    -- * Simple permutations
  , permutations
  , _permutations
  , permutationsNaive
  , _permutationsNaive
  , countPermutations
    -- * Random permutations
  , randomPermutation
  , _randomPermutation
  , randomCyclicPermutation
  , _randomCyclicPermutation
  , randomPermutationDurstenfeld
  , randomCyclicPermutationSattolo
    -- * Multisets
  , permuteMultiset
  , countPermuteMultiset
  , fasc2B_algorithm_L
  ) 
  where

import Control.Monad
import Control.Monad.ST

import Data.List hiding (permutations)
import Data.Array
import Data.Array.ST

import Math.Combinat.Helper

import System.Random

--------------------------------------------------------------------------------
-- * Types

-- | Standard notation for permutations. Internally it is an array of the integers @[1..n]@. 
newtype Permutation = Permutation (Array Int Int) deriving (Eq,Ord,Show,Read)

-- | Disjoint cycle notation for permutations
newtype DisjointCycles = DisjointCycles [[Int]] deriving (Eq,Ord,Show,Read)

fromPermutation :: Permutation -> [Int]
fromPermutation (Permutation ar) = elems ar

permutationArray :: Permutation -> Array Int Int
permutationArray (Permutation ar) = ar

-- | Assumes that the input is a permutation of the numbers @[1..n]@.
toPermutationUnsafe :: [Int] -> Permutation
toPermutationUnsafe xs = Permutation perm where
  n = length xs
  perm = listArray (1,n) xs

-- | Checks whether the input is a permutation of the numbers @[1..n]@.
isPermutation :: [Int] -> Bool
isPermutation xs = (ar!0 == 0) && and [ ar!j == 1 | j<-[1..n] ] where
  n = length xs
  -- the zero index is an unidiomatic hack
  ar = accumArray (+) 0 (0,n) $ map f xs 
  f :: Int -> (Int,Int)
  f j = if j<1 || j>n then (0,1) else (j,1)

-- | Checks the input.
toPermutation :: [Int] -> Permutation
toPermutation xs = if isPermutation xs 
  then toPermutationUnsafe xs
  else error "toPermutation: not a permutation"

-- | Returns @n@, where the input is a permutation of the numbers @[1..n]@
permutationSize :: Permutation -> Int
permutationSize (Permutation ar) = snd $ bounds ar

--------------------------------------------------------------------------------
-- * Disjoint cycles

fromDisjointCycles :: DisjointCycles -> [[Int]]
fromDisjointCycles (DisjointCycles cycles) = cycles

disjointCyclesUnsafe :: [[Int]] -> DisjointCycles 
disjointCyclesUnsafe = DisjointCycles

{-
testconv n m g = mapAccumL f g (replicate m 0) where
  f g _ = (g',p==q) where
    (p,g') = randomPermutation n g
    d = permutationToDisjointCycles p
    q = disjointCyclesToPermutation n d
-}
  
disjointCyclesToPermutation :: Int -> DisjointCycles -> Permutation
disjointCyclesToPermutation n (DisjointCycles cycles) = Permutation perm where
  pairs :: [Int] -> [(Int,Int)]
  pairs xs@(x:_) = worker (xs++[x]) where
    worker (x:xs@(y:_)) = (x,y):worker xs
    worker _ = [] 
  perm = runST $ do
    ar <- newArray_ (1,n) :: ST s (STUArray s Int Int)
    forM_ [1..n] $ \i -> writeArray ar i i 
    forM_ cycles $ \cyc -> forM_ (pairs cyc) $ \(i,j) -> writeArray ar i j
    freeze ar
  
permutationToDisjointCycles :: Permutation -> DisjointCycles
permutationToDisjointCycles (Permutation perm) = res where

  (1,n) = bounds perm

  -- we don't want trivial cycles
  f :: [Int] -> Bool
  f [_] = False
  f _ = True
  
  res = runST $ do
    tag <- newArray (1,n) False 
    cycles <- unfoldM (step tag) 1 
    return (DisjointCycles $ filter f cycles)
    
  step :: STUArray s Int Bool -> Int -> ST s ([Int],Maybe Int)
  step tag k = do
    cyc <- worker tag k k [k] 
    m <- next tag (k+1)
    return (reverse cyc,m)
    
  next :: STUArray s Int Bool -> Int -> ST s (Maybe Int)
  next tag k = if k > n
    then return Nothing
    else readArray tag k >>= \b -> if b 
      then next tag (k+1)  
      else return (Just k)
       
  worker :: STUArray s Int Bool -> Int -> Int -> [Int] -> ST s [Int]
  worker tag k l cyc = do
    writeArray tag l True
    let m = perm ! l
    if m == k 
      then return cyc
      else worker tag k m (m:cyc)      

{-
testmanyperm n m g = mapAccumL f g (replicate m 0) where
  f g _ = (g',(a,b)) where
    (p,g') = randomPermutation n g
    a = isEvenPermutation p
    b = testEvenPerm p 

testcount (_,xys) = if and (map (\(x,y) -> x==y) xys)
  then length $ filter (\(x,y) -> x) xys
  else error "baj van"

testEvenPerm p = even $ sum $ map (\x->x-1) $ map length $ fromDisjointCycles $ permutationToDisjointCycles p
-}

isEvenPermutation :: Permutation -> Bool
isEvenPermutation (Permutation perm) = res where

  (1,n) = bounds perm
  res = runST $ do
    tag <- newArray (1,n) False 
    cycles <- unfoldM (step tag) 1 
    return $ even (sum cycles)
    
  step :: STUArray s Int Bool -> Int -> ST s (Int,Maybe Int)
  step tag k = do
    cyclen <- worker tag k k 0
    m <- next tag (k+1)
    return (cyclen,m)
    
  next :: STUArray s Int Bool -> Int -> ST s (Maybe Int)
  next tag k = if k > n
    then return Nothing
    else readArray tag k >>= \b -> if b 
      then next tag (k+1)  
      else return (Just k)
      
  worker :: STUArray s Int Bool -> Int -> Int -> Int -> ST s Int
  worker tag k l cyclen = do
    writeArray tag l True
    let m = perm ! l
    if m == k 
      then return cyclen
      else worker tag k m (1+cyclen)      

isOddPermutation :: Permutation -> Bool
isOddPermutation = not . isEvenPermutation

-- | Plus 1 or minus 1.
signOfPermutation :: Num a => Permutation -> a
signOfPermutation perm = case isEvenPermutation perm of
  True  ->   1
  False -> (-1)
   
--------------------------------------------------------------------------------
-- * Permutation groups
    
-- | Action of a permutation on a set. If our permutation is 
-- encoded with the sequence @[p1,p2,...,pn]@, then in the
-- two-line notation we have
--
-- > ( 1  2  3  ... n  )
-- > ( p1 p2 p3 ... pn )
--
-- We adopt the convention that permutations act /on the left/ 
-- (as opposed to Knuth, where they act on the right).
-- Thus, 
-- 
-- > permute pi1 (permute pi2 set) == permute (pi1 `multiply` pi2) set
--   
-- The second argument should be an array with bounds @(1,n)@.
-- The function checks the array bounds.
permute :: Permutation -> Array Int a -> Array Int a    
permute pi@(Permutation perm) ar = 
  if (a==1) && (b==n) 
    then listArray (1,n) [ ar!(perm!i) | i <- [1..n] ] 
    else error "permute: array bounds do not match"
  where
    (_,n) = bounds perm  
    (a,b) = bounds ar   

-- | The list should be of length @n@.
permuteList :: Permutation -> [a] -> [a]    
permuteList perm xs = elems $ permute perm $ listArray (1,n) xs where
  n = permutationSize perm

-- | Multiplies two permutations together. See 'permute' for our
-- conventions.  
multiply :: Permutation -> Permutation -> Permutation
multiply pi1@(Permutation perm1) (Permutation perm2) = 
  if (n==m) 
    then Permutation result
    else error "multiply: permutations of different sets"  
  where
	  (_,n) = bounds perm1
	  (_,m) = bounds perm2    
	  result = permute pi1 perm2    
  
infixr 7 `multiply`  
    
-- | The inverse permutation
inverse :: Permutation -> Permutation    
inverse (Permutation perm1) = Permutation result
  where
    result = array (1,n) $ map swap $ assocs perm1
    (_,n) = bounds perm1

--------------------------------------------------------------------------------
-- * Permutations of distinct elements

-- | A synonym for 'permutationsNaive'
permutations :: Int -> [Permutation]
permutations = permutationsNaive

_permutations :: Int -> [[Int]]
_permutations = _permutationsNaive

-- | Permutations of @[1..n]@ in lexicographic order, naive algorithm.
permutationsNaive :: Int -> [Permutation]
permutationsNaive n = map toPermutationUnsafe $ _permutations n 

_permutationsNaive :: Int -> [[Int]]  
_permutationsNaive 0 = [[]]
_permutationsNaive 1 = [[1]]
_permutationsNaive n = helper [1..n] where
  helper [] = [[]]
  helper xs = [ i : ys | i <- xs , ys <- helper (xs `minus` i) ]
  minus [] _ = []
  minus (x:xs) i = if x < i then x : minus xs i else xs
          
-- | # = n!
countPermutations :: Int -> Integer
countPermutations = factorial

--------------------------------------------------------------------------------
-- * Random permutations

-- | A synonym for 'randomPermutationDurstenfeld'.
randomPermutation :: RandomGen g => Int -> g -> (Permutation,g)
randomPermutation = randomPermutationDurstenfeld

_randomPermutation :: RandomGen g => Int -> g -> ([Int],g)
_randomPermutation n rndgen = (fromPermutation perm, rndgen') where
  (perm, rndgen') = randomPermutationDurstenfeld n rndgen 

-- | A synonym for 'randomCyclicPermutationSattolo'.
randomCyclicPermutation :: RandomGen g => Int -> g -> (Permutation,g)
randomCyclicPermutation = randomCyclicPermutationSattolo

_randomCyclicPermutation :: RandomGen g => Int -> g -> ([Int],g)
_randomCyclicPermutation n rndgen = (fromPermutation perm, rndgen') where
  (perm, rndgen') = randomCyclicPermutationSattolo n rndgen 

-- | Generates a uniformly random permutation of @[1..n]@.
-- Durstenfeld's algorithm (see <http://en.wikipedia.org/wiki/Knuth_shuffle>).
randomPermutationDurstenfeld :: RandomGen g => Int -> g -> (Permutation,g)
randomPermutationDurstenfeld = randomPermutationDurstenfeldSattolo False

-- | Generates a uniformly random /cyclic/ permutation of @[1..n]@.
-- Sattolo's algorithm (see <http://en.wikipedia.org/wiki/Knuth_shuffle>).
randomCyclicPermutationSattolo :: RandomGen g => Int -> g -> (Permutation,g)
randomCyclicPermutationSattolo = randomPermutationDurstenfeldSattolo True

randomPermutationDurstenfeldSattolo :: RandomGen g => Bool -> Int -> g -> (Permutation,g)
randomPermutationDurstenfeldSattolo isSattolo n rnd = res where
  res = runST $ do
    ar <- newArray_ (1,n) 
    forM_ [1..n] $ \i -> writeArray ar i i
    rnd' <- worker n (if isSattolo then n-1 else n) rnd ar 
    perm <- unsafeFreeze ar
    return (Permutation perm, rnd')
  worker :: RandomGen g => Int -> Int -> g -> STUArray s Int Int -> ST s g 
  worker n m rnd ar = 
    if n==1 
      then return rnd 
      else do
        let (k,rnd') = randomR (1,m) rnd
        when (k /= n) $ do
          y <- readArray ar k 
          z <- readArray ar n
          writeArray ar n y
          writeArray ar k z
        worker (n-1) (m-1) rnd' ar 

--------------------------------------------------------------------------------
-- * Permutations of a multiset

-- | Generates all permutations of a multiset.  
--   The order is lexicographic. A synonym for 'fasc2B_algorithm_L'
permuteMultiset :: (Eq a, Ord a) => [a] -> [[a]] 
permuteMultiset = fasc2B_algorithm_L

-- | # = \\frac { (\sum_i n_i) ! } { \\prod_i (n_i !) }    
countPermuteMultiset :: (Eq a, Ord a) => [a] -> Integer
countPermuteMultiset xs = factorial n `div` product [ factorial (length z) | z <- group ys ] 
  where
    ys = sort xs
    n = length xs
  
-- | Generates all permutations of a multiset 
--   (based on \"algorithm L\" in Knuth; somewhat less efficient). 
--   The order is lexicographic.  
fasc2B_algorithm_L :: (Eq a, Ord a) => [a] -> [[a]] 
fasc2B_algorithm_L xs = unfold1 next (sort xs) where
  -- next :: [a] -> Maybe [a]
  next xs = case findj (reverse xs,[]) of 
    Nothing -> Nothing
    Just ( (l:ls) , rs) -> Just $ inc l ls (reverse rs,[]) 
    Just ( [] , _ ) -> error "permute: should not happen"

  -- we use simple list zippers: (left,right)
  -- findj :: ([a],[a]) -> Maybe ([a],[a])   
  findj ( xxs@(x:xs) , yys@(y:_) ) = if x >= y 
    then findj ( xs , x : yys )
    else Just ( xxs , yys )
  findj ( x:xs , [] ) = findj ( xs , [x] )  
  findj ( [] , _ ) = Nothing
  
  -- inc :: a -> [a] -> ([a],[a]) -> [a]
  inc u us ( (x:xs) , yys ) = if u >= x
    then inc u us ( xs , x : yys ) 
    else reverse (x:us)  ++ reverse (u:yys) ++ xs
  inc _ _ ( [] , _ ) = error "permute: should not happen"
      
--------------------------------------------------------------------------------

