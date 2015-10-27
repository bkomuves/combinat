
-- | Permutations. 
--
-- See eg.:
-- Donald E. Knuth: The Art of Computer Programming, vol 4, pre-fascicle 2B.
--
-- WARNING: As of version 0.2.7.3, I changed the convention of how permutations
-- are represented internally. Also now they act on the /right/ by default!
--

{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
{-# LANGUAGE CPP, ScopedTypeVariables, GeneralizedNewtypeDeriving #-}
module Math.Combinat.Permutations 
  ( -- * The Permutation type
    Permutation (..)
  , fromPermutation
  , permutationArray
  , permutationUArray
  , uarrayToPermutationUnsafe
  , isPermutation
  , maybePermutation
  , toPermutation
  , toPermutationUnsafe
  , permutationSize
    -- * Disjoint cycles
  , DisjointCycles (..)
  , fromDisjointCycles
  , disjointCyclesUnsafe
  , permutationToDisjointCycles
  , disjointCyclesToPermutation
  , numberOfCycles
    -- * Queries
  , isIdentityPermutation
  , isEvenPermutation
  , isOddPermutation
  , signOfPermutation  
  , signValueOfPermutation  
  , module Math.Combinat.Sign   --  , Sign(..)
  , isCyclicPermutation
    -- * Some concrete permutations
  , transposition
  , adjacentTransposition
  , swapPermutation
  , reversePermutation
  , cycleLeft
  , cycleRight
    -- * Permutation groups
  , multiply
  , inverse
  , identity
    -- * Action of the permutation group
  , permute 
  , permuteList
  , permuteLeft , permuteRight
  , permuteLeftList , permuteRightList
    -- * ASCII drawing
  , asciiPermutation
  , asciiDisjointCycles
  , twoLineNotation 
  , twoLineNotation'
    -- * List of permutations
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

#ifdef QUICKCHECK
    -- * QuickCheck 
  , checkAll
#endif 
  ) 
  where

--------------------------------------------------------------------------------

import Control.Monad
import Control.Monad.ST

import Data.List hiding (permutations)

import Data.Array (Array)
import Data.Array.ST
import Data.Array.Unboxed
import Data.Array.IArray
import Data.Array.MArray
import Data.Array.Unsafe

import Math.Combinat.ASCII
import Math.Combinat.Classes
import Math.Combinat.Helper
import Math.Combinat.Sign
import Math.Combinat.Numbers (factorial,binomial)

import System.Random

#ifdef QUICKCHECK
import Test.QuickCheck
#endif

--------------------------------------------------------------------------------
-- * Types

-- | A permutation. Internally it is an (unboxed) array of the integers @[1..n]@. 
--
-- If this array of integers is @[p1,p2,...,pn]@, then in two-line 
-- notations, that represents the permutation
--
-- > ( 1  2  3  ... n  )
-- > ( p1 p2 p3 ... pn )
--
-- That is, it is the permutation @sigma@ whose (right) action on the set @[1..n]@ is
--
-- > sigma(1) = p1
-- > sigma(2) = p2 
-- > ...
--
-- (NOTE: this changed at version 0.2.7.3!)
--
newtype Permutation = Permutation (UArray Int Int) deriving (Eq,Ord) -- ,Show,Read)

instance Show Permutation where
  showsPrec d (Permutation arr) 
    = showParen (d > 10)  
    $ showString "toPermutation " . showsPrec 11 (elems arr)       -- app_prec = 10

instance Read Permutation where
  readsPrec d r = readParen (d > 10) fun r where
    fun r = [ (toPermutation p,t) 
            | ("toPermutation",s) <- lex r
            , (p,t) <- readsPrec 11 s                              -- app_prec = 10
            ] 

instance DrawASCII Permutation where
  ascii = asciiPermutation

-- | Disjoint cycle notation for permutations. Internally it is @[[Int]]@.
--
-- The cycles are to be understood as follows: a cycle @[c1,c2,...,ck]@ means
-- the permutation
--
-- > ( c1 c2 c3 ... ck )
-- > ( c2 c3 c4 ... c1 )
--
newtype DisjointCycles = DisjointCycles [[Int]] deriving (Eq,Ord,Show,Read)

fromPermutation :: Permutation -> [Int]
fromPermutation (Permutation ar) = elems ar

permutationUArray :: Permutation -> UArray Int Int
permutationUArray (Permutation ar) = ar

-- | Note: this is slower than 'permutationUArray'
permutationArray :: Permutation -> Array Int Int
permutationArray (Permutation ar) = listArray (1,n) (elems ar) where
  (1,n) = bounds ar

-- | Assumes that the input is a permutation of the numbers @[1..n]@.
toPermutationUnsafe :: [Int] -> Permutation
toPermutationUnsafe xs = Permutation perm where
  n    = length xs
  perm = listArray (1,n) xs

-- | Note: Indexing starts from 1.
uarrayToPermutationUnsafe :: UArray Int Int -> Permutation
uarrayToPermutationUnsafe = Permutation

-- | Checks whether the input is a permutation of the numbers @[1..n]@.
isPermutation :: [Int] -> Bool
isPermutation xs = (ar!0 == 0) && and [ ar!j == 1 | j<-[1..n] ] where
  n = length xs
  -- the zero index is an unidiomatic hack
  ar = (accumArray (+) 0 (0,n) $ map f xs) :: UArray Int Int
  f :: Int -> (Int,Int)
  f j = if j<1 || j>n then (0,1) else (j,1)

-- | Checks whether the input is a permutation of the numbers @[1..n]@.
maybePermutation :: [Int] -> Maybe Permutation
maybePermutation input = runST action where
  n = length input
  action :: forall s. ST s (Maybe Permutation)
  action = do
    ar <- newArray (1,n) 0 :: ST s (STUArray s Int Int)
    let go []     = return $ Just (Permutation $ listArray (1,n) input)
        go (j:js) = if j<1 || j>n 
          then return Nothing
          else do
            z <- readArray ar j
            writeArray ar j (z+1)
            if z==0 then go js
                    else return Nothing               
    go input
    
-- | Checks the input.
toPermutation :: [Int] -> Permutation
toPermutation xs = case maybePermutation xs of
  Just p  -> p
  Nothing -> error "toPermutation: not a permutation"

-- | Returns @n@, where the input is a permutation of the numbers @[1..n]@
permutationSize :: Permutation -> Int
permutationSize (Permutation ar) = snd $ bounds ar

instance HasWidth Permutation where
  width = permutationSize

-- | Checks whether the permutation is the identity permutation
isIdentityPermutation :: Permutation -> Bool
isIdentityPermutation (Permutation ar) = (elems ar == [1..n]) where
  (1,n) = bounds ar

--------------------------------------------------------------------------------
-- * ASCII

-- | Synonym for 'twoLineNotation'
asciiPermutation :: Permutation -> ASCII
asciiPermutation = twoLineNotation 

asciiDisjointCycles :: DisjointCycles -> ASCII
asciiDisjointCycles (DisjointCycles cycles) = final where
  final = hCatWith VTop (HSepSpaces 1) boxes 
  boxes = [ twoLineNotation' (f cyc) | cyc <- cycles ]
  f cyc = pairs (cyc ++ [head cyc])

-- | The standard two-line notation, moving the element indexed by the top row into
-- the place indexed by the corresponding element in the bottom row.
twoLineNotation :: Permutation -> ASCII
twoLineNotation (Permutation arr) = twoLineNotation' $ zip [1..] (elems arr)

twoLineNotation' :: [(Int,Int)] -> ASCII
twoLineNotation' xys = asciiFromLines [ topLine, botLine ] where
  topLine = "( " ++ intercalate " " us ++ " )"
  botLine = "( " ++ intercalate " " vs ++ " )"
  pairs   = [ (show x, show y) | (x,y) <- xys ]
  (us,vs) = unzip (map f pairs) 
  f (s,t) = (s',t') where
    a = length s 
    b = length t
    c = max a b
    s' = replicate (c-a) ' ' ++ s
    t' = replicate (c-b) ' ' ++ t

--------------------------------------------------------------------------------
-- * Disjoint cycles

fromDisjointCycles :: DisjointCycles -> [[Int]]
fromDisjointCycles (DisjointCycles cycles) = cycles

disjointCyclesUnsafe :: [[Int]] -> DisjointCycles 
disjointCyclesUnsafe = DisjointCycles

instance DrawASCII DisjointCycles where
  ascii = asciiDisjointCycles

instance HasNumberOfCycles DisjointCycles where
  numberOfCycles (DisjointCycles cycles) = length cycles

instance HasNumberOfCycles Permutation where
  numberOfCycles = numberOfCycles . permutationToDisjointCycles
  
disjointCyclesToPermutation :: Int -> DisjointCycles -> Permutation
disjointCyclesToPermutation n (DisjointCycles cycles) = Permutation perm where

  pairs :: [Int] -> [(Int,Int)]
  pairs xs@(x:_) = worker (xs++[x]) where
    worker (x:xs@(y:_)) = (x,y):worker xs
    worker _ = [] 
  pairs [] = error "disjointCyclesToPermutation: empty cycle"

  perm = runSTUArray $ do
    ar <- newArray_ (1,n) :: ST s (STUArray s Int Int)
    forM_ [1..n] $ \i -> writeArray ar i i 
    forM_ cycles $ \cyc -> forM_ (pairs cyc) $ \(i,j) -> writeArray ar i j
    return ar -- freeze ar
  
-- | Convert to disjoint cycle notation.
--
-- This is compatible with Maple's @convert(perm,\'disjcyc\')@ 
-- and also with Mathematica's @PermutationCycles[perm]@
--
-- Note however, that for example Mathematica uses the 
-- /top row/ to represent a permutation, while we use the
-- /bottom row/ - thus even though this function looks
-- identical, the /meaning/ of both the input and output
-- is different!
-- 
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
    return (reverse cyc, m) 
    
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

signOfPermutation :: Permutation -> Sign
signOfPermutation perm = case isEvenPermutation perm of
  True  -> Plus
  False -> Minus

-- | Plus 1 or minus 1.
{-# SPECIALIZE signValueOfPermutation :: Permutation -> Int     #-}
{-# SPECIALIZE signValueOfPermutation :: Permutation -> Integer #-}
signValueOfPermutation :: Num a => Permutation -> a
signValueOfPermutation = signValue . signOfPermutation
  
isCyclicPermutation :: Permutation -> Bool
isCyclicPermutation perm = 
  case cycles of
    []    -> True
    [cyc] -> (length cyc == n)
    _     -> False
  where 
    n = permutationSize perm
    DisjointCycles cycles = permutationToDisjointCycles perm

--------------------------------------------------------------------------------
-- * Some concrete permutations

-- | The permutation @[n,n-1,n-2..2,1]@. Note that it is the inverse of itself.
reversePermutation :: Int -> Permutation
reversePermutation n = Permutation $ listArray (1,n) [n,n-1..1]

-- | A transposition (swapping two elements). Synonym for 'swapPermutation'.
transposition :: Int -> (Int,Int) -> Permutation
transposition = swapPermutation

-- | @adjacentTransposition n k@ swaps the elements @k@ and @(k+1)@.
adjacentTransposition :: Int -> Int -> Permutation
adjacentTransposition n k 
  | k>0 && k<n  = swapPermutation n (k,k+1)
  | otherwise   = error "adjacentTransposition: index out of range"

-- | @swapPermutation n (i,j)@ is the permutation of size @n@ which swaps @i@\'th and @j@'th elements.
swapPermutation :: Int -> (Int,Int) -> Permutation
swapPermutation n (i,j) = 
  if i>=1 && j>=1 && i<=n && j<=n 
    then Permutation $ listArray (1,n) [ f k | k<-[1..n] ]
    else error "swapPerm: index out of range"
  where
    f k | k == i    = j
        | k == j    = i
        | otherwise = k

-- | The permutation which cycles a list left by one step:
-- 
-- > permuteList (cycleLeft 5) "abcde" == "bcdea"
--
-- Or in two-line notation:
--
-- > ( 1 2 3 4 5 )
-- > ( 2 3 4 5 1 )
-- 
cycleLeft :: Int -> Permutation
cycleLeft n = Permutation $ listArray (1,n) $ [2..n] ++ [1]

-- | The permutation which cycles a list right by one step:
-- 
-- > permuteList (cycleRight 5) "abcde" == "eabcd"
--
-- Or in two-line notation:
--
-- > ( 1 2 3 4 5 )
-- > ( 5 1 2 3 4 )
-- 
cycleRight :: Int -> Permutation
cycleRight n = Permutation $ listArray (1,n) $ n : [1..n-1]
   
--------------------------------------------------------------------------------
-- * Permutation groups

-- | Multiplies two permutations together: @p `multiply` q@
-- means the permutation when we first apply @p@, and then @q@
-- (that is, the natural action is the /right/ action)
--
-- See also 'permute' for our conventions.  
--
multiply :: Permutation -> Permutation -> Permutation
multiply pi1@(Permutation perm1) pi2@(Permutation perm2) = 
  if (n==m) 
    then Permutation result
    else error "multiply: permutations of different sets"  
  where
    (_,n) = bounds perm1
    (_,m) = bounds perm2    
    result = permute pi2 perm1
  
infixr 7 `multiply`  
    
-- | The inverse permutation.
inverse :: Permutation -> Permutation    
inverse (Permutation perm1) = Permutation result
  where
    result = array (1,n) $ map swap $ assocs perm1
    (_,n) = bounds perm1
    
-- | The identity (or trivial) permutation.
identity :: Int -> Permutation 
identity n = Permutation $ listArray (1,n) [1..n]

--------------------------------------------------------------------------------
-- * Action of the permutation group

-- | /Right/ action of a permutation on a set. If our permutation is 
-- encoded with the sequence @[p1,p2,...,pn]@, then in the
-- two-line notation we have
--
-- > ( 1  2  3  ... n  )
-- > ( p1 p2 p3 ... pn )
--
-- We adopt the convention that permutations act /on the right/ 
-- (as in Knuth):
--
-- > permute pi2 (permute pi1 set) == permute (pi1 `multiply` pi2) set
--
-- Synonym to 'permuteRight'
--
{-# SPECIALIZE permute :: Permutation -> Array  Int b   -> Array  Int b   #-}
{-# SPECIALIZE permute :: Permutation -> UArray Int Int -> UArray Int Int #-}
permute :: IArray arr b => Permutation -> arr Int b -> arr Int b    
permute = permuteRight

-- | Right action on lists. Synonym to 'permuteListRight'
--
permuteList :: Permutation -> [a] -> [a]
permuteList = permuteRightList
    
-- | The right (standard) action of permutations on sets. 
-- 
-- > permuteRight pi2 (permuteRight pi1 set) == permuteRight (pi1 `multiply` pi2) set
--   
-- The second argument should be an array with bounds @(1,n)@.
-- The function checks the array bounds.
--
{-# SPECIALIZE permuteRight :: Permutation -> Array  Int b   -> Array  Int b   #-}
{-# SPECIALIZE permuteRight :: Permutation -> UArray Int Int -> UArray Int Int #-}
permuteRight :: IArray arr b => Permutation -> arr Int b -> arr Int b    
permuteRight pi@(Permutation perm) ar = 
  if (a==1) && (b==n) 
    then listArray (1,n) [ ar!(perm!i) | i <- [1..n] ] 
    else error "permuteRight: array bounds do not match"
  where
    (_,n) = bounds perm  
    (a,b) = bounds ar   

-- | The right (standard) action on a list. The list should be of length @n@.
--
-- > fromPermutation perm == permuteRightList perm [1..n]
-- 
permuteRightList :: forall a . Permutation -> [a] -> [a]    
permuteRightList perm xs = elems $ permuteRight perm $ arr where
  arr = listArray (1,n) xs :: Array Int a
  n   = permutationSize perm

-- | The left (opposite) action of the permutation group.
--
-- > permuteLeft pi2 (permuteLeft pi1 set) == permuteLeft (pi2 `multiply` pi1) set
--
-- It is related to 'permuteLeft' via:
--
-- > permuteLeft  pi arr == permuteRight (inverse pi) arr
-- > permuteRight pi arr == permuteLeft  (inverse pi) arr
--
{-# SPECIALIZE permuteLeft :: Permutation -> Array  Int b   -> Array  Int b   #-}
{-# SPECIALIZE permuteLeft :: Permutation -> UArray Int Int -> UArray Int Int #-}
permuteLeft :: IArray arr b => Permutation -> arr Int b -> arr Int b    
permuteLeft pi@(Permutation perm) ar =    
  -- permuteRight (inverse pi) ar
  if (a==1) && (b==n) 
    then array (1,n) [ ( perm!i , ar!i ) | i <- [1..n] ] 
    else error "permuteLeft: array bounds do not match"
  where
    (_,n) = bounds perm  
    (a,b) = bounds ar   

-- | The left (opposite) action on a list. The list should be of length @n@.
--
-- > permuteLeftList perm set == permuteList (inverse perm) set
-- > fromPermutation (inverse perm) == permuteLeftList perm [1..n]
--
permuteLeftList :: forall a. Permutation -> [a] -> [a]    
permuteLeftList perm xs = elems $ permuteLeft perm $ arr where
  arr = listArray (1,n) xs :: Array Int a
  n   = permutationSize perm

--------------------------------------------------------------------------------
-- * Permutations of distinct elements

-- | A synonym for 'permutationsNaive'
permutations :: Int -> [Permutation]
permutations = permutationsNaive

_permutations :: Int -> [[Int]]
_permutations = _permutationsNaive

-- | All permutations of @[1..n]@ in lexicographic order, naive algorithm.
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
    perm <- Data.Array.Unsafe.unsafeFreeze ar
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

#ifdef QUICKCHECK

minPermSize = 1
maxPermSize = 123

newtype Elem = Elem Int deriving Eq
newtype Nat  = Nat { fromNat :: Int } deriving (Eq,Ord,Show,Num,Random)

naturalSet :: Permutation -> Array Int Elem
naturalSet perm = listArray (1,n) [ Elem i | i<-[1..n] ] where
  n = permutationSize perm

permInternalSet :: Permutation -> Array Int Elem
permInternalSet perm@(Permutation arr) = listArray (1,n) [ Elem (arr!i) | i<-[1..n] ] where
  n = permutationSize perm

sameSize :: Permutation ->  Permutation -> Bool
sameSize perm1 perm2 = ( permutationSize perm1 == permutationSize perm2)

newtype CyclicPermutation = Cyclic { fromCyclic :: Permutation } deriving Show

data SameSize = SameSize Permutation Permutation deriving Show

instance Random Permutation where
  random g = randomPermutation size g1 where
    (size,g1) = randomR (minPermSize,maxPermSize) g
  randomR _ = random

instance Random CyclicPermutation where
  random g = (Cyclic cycl,g2) where
    (size,g1) = randomR (minPermSize,maxPermSize) g
    (cycl,g2) = randomCyclicPermutation size g1
  randomR _ = random

instance Random DisjointCycles where
  random g = (disjcyc,g2) where
    (size,g1) = randomR (minPermSize,maxPermSize) g
    (perm,g2) = randomPermutation size g1
    disjcyc   = permutationToDisjointCycles perm
  randomR _ = random

instance Random SameSize where
  random g = (SameSize prm1 prm2, g3) where
    (size,g1) = randomR (minPermSize,maxPermSize) g
    (prm1,g2) = randomPermutation size g1 
    (prm2,g3) = randomPermutation size g2
  randomR _ = random

instance Arbitrary Nat where
  arbitrary = choose (Nat 0 , Nat 50)
     
instance Arbitrary Permutation       where arbitrary = choose undefined
instance Arbitrary CyclicPermutation where arbitrary = choose undefined
instance Arbitrary DisjointCycles    where arbitrary = choose undefined
instance Arbitrary SameSize          where arbitrary = choose undefined

-- | Runs all quickCheck tests
checkAll :: IO ()
checkAll = do
  let f :: Testable a => a -> IO ()
      f = quickCheck

  f prop_disjcyc_1
  f prop_disjcyc_2 

  f prop_disjcyc_Mathematica

  f prop_randCyclic
  f prop_inverse

  f prop_mulPerm
  f prop_mulPermLeft
  f prop_mulPermRight

  f prop_perm
  f prop_permLeft
  f prop_permRight
  f prop_permLeftRight

  f prop_cycleLeft
  f prop_cycleRight

  f prop_mulSign      
  f prop_invMul
  f prop_cyclSign
  f prop_permIsPerm
  f prop_isEven
          
prop_disjcyc_1 perm = ( perm == disjointCyclesToPermutation n (permutationToDisjointCycles perm) )
  where n = permutationSize perm

prop_disjcyc_2 k dcyc = ( dcyc == permutationToDisjointCycles (disjointCyclesToPermutation n dcyc) )
  where 
    n = fromNat k + m 
    m = case fromDisjointCycles dcyc of
      []  -> 1
      xxs -> maximum (concat xxs)

-- PermutationCycles[ { 12, 15, 5, 6, 2, 7, 17, 9, 20, 3, 11, 18, 22, 21, 8, 10, 4, 19, 14, 16, 23, 1, 13 } ]
-- Cycles           [ {{1, 12, 18, 19, 14, 21, 23, 13, 22}, {2, 15, 8, 9, 20, 16, 10, 3, 5}, {4, 6, 7, 17}} ]
prop_disjcyc_Mathematica = (permutationToDisjointCycles   perm == disjcyc) 
                        && (disjointCyclesToPermutation n disjcyc == perm)
  where
    n       = permutationSize perm
    perm    = toPermutation  [ 12, 15, 5, 6, 2, 7, 17, 9, 20, 3, 11, 18, 22, 21, 8, 10, 4, 19, 14, 16, 23, 1, 13 ]
    disjcyc = DisjointCycles [ [1, 12, 18, 19, 14, 21, 23, 13, 22], [2, 15, 8, 9, 20, 16, 10, 3, 5], [4, 6, 7, 17] ]

xperm    = toPermutation  [ 12, 15, 5, 6, 2, 7, 17, 9, 20, 3, 11, 18, 22, 21, 8, 10, 4, 19, 14, 16, 23, 1, 13 ]
xdisjcyc = DisjointCycles [ [1, 12, 18, 19, 14, 21, 23, 13, 22], [2, 15, 8, 9, 20, 16, 10, 3, 5], [4, 6, 7, 17] ]

prop_randCyclic cycl = ( isCyclicPermutation (fromCyclic cycl) )

prop_inverse perm = ( perm == inverse (inverse perm) ) 

prop_mulPerm (SameSize perm1 perm2) = 
    ( permute perm2 (permute perm1 set) == permute (perm1 `multiply` perm2) set ) 
  where 
    set = naturalSet perm1

prop_mulPermRight (SameSize perm1 perm2) = 
    ( permuteRight perm2 (permuteRight perm1 set) == permuteRight (perm1 `multiply` perm2) set ) 
  where 
    set = naturalSet perm1

prop_mulPermLeft (SameSize perm1 perm2) = 
    ( permuteLeft perm2 (permuteLeft perm1 set) == permuteLeft (perm2 `multiply` perm1) set ) 
  where 
    set = naturalSet perm1

prop_perm          perm = permute perm (naturalSet perm) == permInternalSet perm
prop_permLeft      perm = permuteLeft  perm (permInternalSet perm) == naturalSet perm
prop_permRight     perm = permuteRight perm (naturalSet perm) == permInternalSet perm
prop_permLeftRight perm = permuteLeft (inverse perm) (naturalSet perm) == permuteRight (perm) (naturalSet perm) 

prop_cycleLeft  = permuteList (cycleLeft  5) "abcde" == "bcdea"
prop_cycleRight = permuteList (cycleRight 5) "abcde" == "eabcd"

prop_mulSign (SameSize perm1 perm2) = 
    ( sgn perm1 * sgn perm2 == sgn (perm1 `multiply` perm2) ) 
  where 
    sgn = signValue . signOfPermutation :: Permutation -> Int

prop_invMul (SameSize perm1 perm2) =   
  ( inverse perm2 `multiply` inverse perm1 == inverse (perm1 `multiply` perm2) ) 

prop_cyclSign cycl = ( isEvenPermutation perm == odd n ) where
  perm = fromCyclic cycl
  n = permutationSize perm
  
prop_permIsPerm perm = ( isPermutation (fromPermutation perm) ) 

prop_isEven perm = ( isEvenPermutation perm == isEvenAlternative perm ) where
  isEvenAlternative p = 
    even $ sum $ map (\x->x-1) $ map length $ fromDisjointCycles $ permutationToDisjointCycles p


#endif

--------------------------------------------------------------------------------

