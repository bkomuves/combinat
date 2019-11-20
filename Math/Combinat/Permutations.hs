
-- | Permutations. 
--
-- See eg.:
-- Donald E. Knuth: The Art of Computer Programming, vol 4, pre-fascicle 2B.
--
-- WARNING: As of version 0.2.8.0, I changed the convention of how permutations
-- are represented internally. Also now they act on the /right/ by default!
--

{-# LANGUAGE CPP, BangPatterns, ScopedTypeVariables, GeneralizedNewtypeDeriving, FlexibleContexts #-}
module Math.Combinat.Permutations 
  ( -- * The Permutation type
    Permutation (..)
  , fromPermutation
  , lookupPermutation , (!!!)
  , permutationArray
  , permutationUArray
  , uarrayToPermutationUnsafe
  , isPermutation
  , maybePermutation
  , toPermutation
  , toPermutationUnsafe
  , toPermutationUnsafeN
  , permutationSize
    -- * Disjoint cycles
  , DisjointCycles (..)
  , fromDisjointCycles
  , disjointCyclesUnsafe
  , permutationToDisjointCycles
  , disjointCyclesToPermutation
  , numberOfCycles
  , concatPermutations
    -- * Queries
  , isIdentityPermutation
  , isReversePermutation
  , isEvenPermutation
  , isOddPermutation
  , signOfPermutation  
  , signValueOfPermutation  
  , module Math.Combinat.Sign   --  , Sign(..)
  , isCyclicPermutation
    -- * Some concrete permutations
  , transposition
  , transpositions
  , adjacentTransposition
  , adjacentTranspositions
  , cycleLeft
  , cycleRight
  , reversePermutation
    -- * Inversions
  , inversions
  , numberOfInversions
  , numberOfInversionsNaive
  , numberOfInversionsMerge
  , bubbleSort2
  , bubbleSort
    -- * Permutation groups
  , identityPermutation
  , inversePermutation
  , multiplyPermutation
  , productOfPermutations
  , productOfPermutations'
    -- * Action of the permutation group
  , permuteArray 
  , permuteList
  , permuteArrayLeft , permuteArrayRight
  , permuteListLeft  , permuteListRight
    -- * Sorting
  , sortingPermutationAsc 
  , sortingPermutationDesc
    -- * ASCII drawing
  , asciiPermutation
  , asciiDisjointCycles
  , twoLineNotation 
  , inverseTwoLineNotation
  , genericTwoLineNotation
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
  ) 
  where

--------------------------------------------------------------------------------

import Control.Monad
import Control.Monad.ST

import Data.List hiding ( permutations )
import Data.Ord ( comparing )

import Data.Array (Array)
import Data.Array.ST
import Data.Array.Unboxed
import Data.Array.IArray
import Data.Array.MArray
import Data.Array.Unsafe

import Data.Vector.Compact.WordVec ( WordVec )
import qualified Data.Vector.Compact.WordVec as V

import Math.Combinat.ASCII
import Math.Combinat.Classes
import Math.Combinat.Helper
import Math.Combinat.Sign
import Math.Combinat.Numbers ( factorial , binomial )

import System.Random

--------------------------------------------------------------------------------
-- WordVec helpers

toUArray :: WordVec -> UArray Int Int
toUArray vec = listArray (1,n) (map fromIntegral $ V.toList vec) where n = V.vecLen vec

fromUArray :: UArray Int Int -> WordVec
fromUArray arr = fromPermListN n (map fromIntegral $ elems arr) where
  (1,n) = bounds arr

-- | maximum = length
fromPermListN :: Int -> [Int] -> WordVec
fromPermListN n perm = V.fromList' shape (map fromIntegral perm) where
  shape = V.Shape n bits
  bits  = V.bitsNeededFor (fromIntegral n :: Word)

fromPermList :: [Int] -> WordVec
fromPermList perm = V.fromList (map fromIntegral perm)

(.!) :: WordVec -> Int -> Int
(.!) vec idx = fromIntegral (V.unsafeIndex (idx-1) vec)

_elems :: WordVec -> [Int]
_elems = map fromIntegral . V.toList

_assocs :: WordVec -> [(Int,Int)]
_assocs vec = zip [1..] (_elems vec)

_bound :: WordVec -> Int
_bound = V.vecLen

{- 
-- the old internal representation (UArray Int Int)

_elems :: UArray Int Int -> [Int]
_elems = elems

_assocs :: UArray Int Int -> [(Int,Int)]
_assocs = elems

_bound :: UArray Int Int -> Int
_bound = snd . bounds
-}


toPermN :: Int -> [Int] -> Permutation
toPermN n xs = Permutation (fromPermListN n xs)

--------------------------------------------------------------------------------
-- * Types

-- | A permutation. Internally it is an (compact) vector 
-- of the integers @[1..n]@.
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
-- (NOTE: this changed at version 0.2.8.0!)
--
newtype Permutation = Permutation WordVec deriving (Eq,Ord) -- ,Show,Read)

instance Show Permutation where
  showsPrec d (Permutation arr) 
    = showParen (d > 10)  
    $ showString "toPermutation " . showsPrec 11 (_elems arr)       -- app_prec = 10

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
fromPermutation (Permutation ar) = _elems ar

permutationUArray :: Permutation -> UArray Int Int
permutationUArray (Permutation ar) = toUArray ar

permutationArray :: Permutation -> Array Int Int
permutationArray (Permutation ar) = listArray (1,n) (_elems ar) where
  n = _bound ar

-- | Assumes that the input is a permutation of the numbers @[1..n]@.
toPermutationUnsafe :: [Int] -> Permutation
toPermutationUnsafe xs = Permutation (fromPermList xs) 

-- | This is faster than 'toPermutationUnsafe', but you need to supply @n@.
toPermutationUnsafeN :: Int -> [Int] -> Permutation
toPermutationUnsafeN n xs = Permutation (fromPermListN n xs) 

-- | Note: Indexing starts from 1.
uarrayToPermutationUnsafe :: UArray Int Int -> Permutation
uarrayToPermutationUnsafe = Permutation . fromUArray

-- | Checks whether the input is a permutation of the numbers @[1..n]@.
isPermutation :: [Int] -> Bool
isPermutation xs = (ar!0 == 0) && and [ ar!j == 1 | j<-[1..n] ] where
  n = length xs
  -- the zero index is an unidiomatic hack
  ar = (accumArray (+) 0 (0,n) $ map f xs) :: UArray Int Int
  f :: Int -> (Int,Int)
  f !j = if j<1 || j>n then (0,1) else (j,1)

-- | Checks whether the input is a permutation of the numbers @[1..n]@.
maybePermutation :: [Int] -> Maybe Permutation
maybePermutation input = runST action where
  n = length input
  action :: forall s. ST s (Maybe Permutation)
  action = do
    ar <- newArray (1,n) 0 :: ST s (STUArray s Int Int)
    let go []     = return $ Just (toPermutationUnsafe input)
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
permutationSize (Permutation ar) = _bound ar

-- | Returns the image @sigma(k)@ of @k@ under the permutation @sigma@.
-- 
-- Note: we don't check the bounds! It may even crash if you index out of bounds!
lookupPermutation :: Permutation -> Int -> Int
lookupPermutation (Permutation ar) idx = ar .! idx

-- infix 8 !!!

-- | Infix version of 'lookupPermutation'
(!!!) :: Permutation -> Int -> Int
(!!!) (Permutation ar) idx = ar .! idx

instance HasWidth Permutation where
  width = permutationSize

-- | Checks whether the permutation is the identity permutation
isIdentityPermutation :: Permutation -> Bool
isIdentityPermutation (Permutation ar) = (_elems ar == [1..n]) where
  n = _bound ar

-- | Given a permutation of @n@ and a permutation of @m@, we return
-- a permutation of @n+m@ resulting by putting them next to each other.
-- This should satisfy
--
-- > permuteList p1 xs ++ permuteList p2 ys == permuteList (concatPermutations p1 p2) (xs++ys)
--
concatPermutations :: Permutation -> Permutation -> Permutation 
concatPermutations perm1 perm2 = toPermutationUnsafe list where
  n    = permutationSize perm1
  list = fromPermutation perm1 ++ map (+n) (fromPermutation perm2)

--------------------------------------------------------------------------------
-- * ASCII

-- | Synonym for 'twoLineNotation'
asciiPermutation :: Permutation -> ASCII
asciiPermutation = twoLineNotation 

asciiDisjointCycles :: DisjointCycles -> ASCII
asciiDisjointCycles (DisjointCycles cycles) = final where
  final = hCatWith VTop (HSepSpaces 1) boxes 
  boxes = [ genericTwoLineNotation (f cyc) | cyc <- cycles ]
  f cyc = pairs (cyc ++ [head cyc])

-- | The standard two-line notation, moving the element indexed by the top row into
-- the place indexed by the corresponding element in the bottom row.
twoLineNotation :: Permutation -> ASCII
twoLineNotation (Permutation arr) = genericTwoLineNotation $ zip [1..] (_elems arr)

-- | The inverse two-line notation, where the it\'s the bottom line 
-- which is in standard order. The columns of this are a permutation
-- of the columns 'twoLineNotation'.
--
-- Remark: the top row of @inverseTwoLineNotation perm@ is the same 
-- as the bottom row of @twoLineNotation (inversePermutation perm)@.
--
inverseTwoLineNotation :: Permutation -> ASCII
inverseTwoLineNotation (Permutation arr) =
  genericTwoLineNotation $ sortBy (comparing snd) $ zip [1..] (_elems arr) 

-- | Two-line notation for any set of numbers
genericTwoLineNotation :: [(Int,Int)] -> ASCII
genericTwoLineNotation xys = asciiFromLines [ topLine, botLine ] where
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
disjointCyclesToPermutation n (DisjointCycles cycles) = Permutation $ fromUArray perm where

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

  n = _bound perm

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
    let m = perm .! l
    if m == k 
      then return cyc
      else worker tag k m (m:cyc)      

isEvenPermutation :: Permutation -> Bool
isEvenPermutation (Permutation perm) = res where

  n = _bound perm
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
    let m = perm .! l
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
-- * Inversions

-- | An /inversion/ of a permutation @sigma@ is a pair @(i,j)@ such that
-- @i<j@ and @sigma(i) > sigma(j)@.
--
-- This functions returns the inversion of a permutation.
--
inversions :: Permutation -> [(Int,Int)]
inversions (Permutation arr) = list where
  n =  _bound arr
  list = [ (i,j) | i<-[1..n-1], j<-[i+1..n], arr.!i > arr.!j ]

-- | Returns the number of inversions:
--
-- > numberOfInversions perm = length (inversions perm)
--
-- Synonym for 'numberOfInversionsMerge'
--
numberOfInversions :: Permutation -> Int
numberOfInversions = numberOfInversionsMerge

-- | Returns the number of inversions, using the merge-sort algorithm.
-- This should be @O(n*log(n))@
--
numberOfInversionsMerge :: Permutation -> Int
numberOfInversionsMerge (Permutation arr) = fst (sortCnt n $ _elems arr) where
  n = _bound arr
                                        
  -- | First argument is length of the list.
  -- Returns also the inversion count.
  sortCnt :: Int -> [Int] -> (Int,[Int])
  sortCnt 0 _     = (0,[] )
  sortCnt 1 [x]   = (0,[x])
  sortCnt 2 [x,y] = if x>y then (1,[y,x]) else (0,[x,y])
  sortCnt n xs    = mergeCnt (sortCnt k us) (sortCnt l vs) where
    k = div n 2
    l = n - k 
    (us,vs) = splitAt k xs

  mergeCnt :: (Int,[Int]) -> (Int,[Int]) -> (Int,[Int])
  mergeCnt (!c,us) (!d,vs) = (c+d+e,ws) where

    (e,ws) = go 0 us vs 

    go !k xs [] = ( k*length xs , xs )
    go _  [] ys = ( 0 , ys)
    go !k xxs@(x:xs) yys@(y:ys) = if x < y
      then let (a,zs) = go  k     xs yys in (a+k, x:zs)
      else let (a,zs) = go (k+1) xxs  ys in (a  , y:zs)

-- | Returns the number of inversions, using the definition, thus it's @O(n^2)@.
--
numberOfInversionsNaive :: Permutation -> Int
numberOfInversionsNaive (Permutation arr) = length list where
  n    = _bound arr
  list = [ (0::Int) | i<-[1..n-1], j<-[i+1..n], arr.!i > arr.!j ]

-- | Bubble sorts breaks a permutation into the product of adjacent transpositions:
--
-- > multiplyMany' n (map (transposition n) $ bubbleSort2 perm) == perm
--
-- Note that while this is not unique, the number of transpositions 
-- equals the number of inversions.
--
bubbleSort2 :: Permutation -> [(Int,Int)]
bubbleSort2 = map f . bubbleSort where f i = (i,i+1)

-- | Another version of bubble sort. An entry @i@ in the return sequence means
-- the transposition @(i,i+1)@:
--
-- > multiplyMany' n (map (adjacentTransposition n) $ bubbleSort perm) == perm
--
bubbleSort :: Permutation -> [Int]
bubbleSort perm@(Permutation tgt) = runST action where
  n = _bound tgt

  action :: forall s. ST s [Int]
  action = do
    fwd <- newArray_ (1,n) :: ST s (STUArray s Int Int)
    inv <- newArray_ (1,n) :: ST s (STUArray s Int Int)
    forM_ [1..n] $ \i -> writeArray fwd i i
    forM_ [1..n] $ \i -> writeArray inv i i

    list <- forM [1..n] $ \x -> do

      let k = tgt .! x       -- we take the number which will be at the @x@-th position at the end
      i <- readArray inv k   -- number @k@ is at the moment at position @i@
      let j = x              -- but the final place is at @x@      

      let swaps = move i j
      forM_ swaps $ \y -> do

        a <- readArray fwd  y
        b <- readArray fwd (y+1)
        writeArray fwd (y+1) a
        writeArray fwd  y    b

        u <- readArray inv a
        v <- readArray inv b
        writeArray inv b u
        writeArray inv a v

      return swaps
  
    return (concat list)

  move :: Int -> Int -> [Int]
  move !i !j
    | j == i  = []
    | j >  i  = [i..j-1]
    | j <  i  = [i-1,i-2..j]

--------------------------------------------------------------------------------
-- * Some concrete permutations

-- | The permutation @[n,n-1,n-2,...,2,1]@. Note that it is the inverse of itself.
reversePermutation :: Int -> Permutation
reversePermutation n = Permutation $ fromPermListN n [n,n-1..1]

-- | Checks whether the permutation is the reverse permutation @[n,n-1,n-2,...,2,1].
isReversePermutation :: Permutation -> Bool
isReversePermutation (Permutation arr) = _elems arr == [n,n-1..1] where n = _bound arr

-- | A transposition (swapping two elements). 
--
-- @transposition n (i,j)@ is the permutation of size @n@ which swaps @i@\'th and @j@'th elements.
--
transposition :: Int -> (Int,Int) -> Permutation
transposition n (i,j) = 
  if i>=1 && j>=1 && i<=n && j<=n 
    then Permutation $ fromPermListN n [ f k | k<-[1..n] ]
    else error "transposition: index out of range"
  where
    f k | k == i    = j
        | k == j    = i
        | otherwise = k

-- | Product of transpositions.
--
-- > transpositions n list == multiplyMany [ transposition n pair | pair <- list ]
--
transpositions :: Int -> [(Int,Int)] -> Permutation
transpositions n list = Permutation (fromUArray $ runSTUArray action) where

  action :: ST s (STUArray s Int Int)
  action = do
    arr <- newArray_ (1,n) 
    forM_ [1..n] $ \i -> writeArray arr i i    
    let doSwap (i,j) = do
          u <- readArray arr i
          v <- readArray arr j
          writeArray arr i v
          writeArray arr j u          
    mapM_ doSwap list
    return arr

-- | @adjacentTransposition n k@ swaps the elements @k@ and @(k+1)@.
adjacentTransposition :: Int -> Int -> Permutation
adjacentTransposition n k 
  | k>0 && k<n  = transposition n (k,k+1)
  | otherwise   = error "adjacentTransposition: index out of range"

-- | Product of adjacent transpositions.
--
-- > adjacentTranspositions n list == multiplyMany [ adjacentTransposition n idx | idx <- list ]
--
adjacentTranspositions :: Int -> [Int] -> Permutation
adjacentTranspositions n list = Permutation (fromUArray $ runSTUArray action) where

  action :: ST s (STUArray s Int Int)
  action = do
    arr <- newArray_ (1,n) 
    forM_ [1..n] $ \i -> writeArray arr i i    
    let doSwap i
          | i<0 || i>=n  = error "adjacentTranspositions: index out of range"
          | otherwise    = do
              u <- readArray arr  i
              v <- readArray arr (i+1)
              writeArray arr  i    v
              writeArray arr (i+1) u          
    mapM_ doSwap list
    return arr

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
cycleLeft n = Permutation $ fromPermListN n ([2..n] ++ [1])

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
cycleRight n = Permutation $ fromPermListN n (n : [1..n-1])
   
--------------------------------------------------------------------------------
-- * Permutation groups

-- | Multiplies two permutations together: @p `multiplyPermutation` q@
-- means the permutation when we first apply @p@, and then @q@
-- (that is, the natural action is the /right/ action)
--
-- See also 'permuteArray' for our conventions.  
--
multiplyPermutation :: Permutation -> Permutation -> Permutation
multiplyPermutation pi1@(Permutation perm1) pi2@(Permutation perm2) = 
  if (n==m) 
    then Permutation $ fromUArray result
    else error "multiplyPermutation: permutations of different sets"  
  where
    n = _bound perm1
    m = _bound perm2    
    result = permuteArray pi2 (toUArray perm1)
  
infixr 7 `multiplyPermutation`  

-- | The inverse permutation.
inversePermutation :: Permutation -> Permutation    
inversePermutation (Permutation perm1) = Permutation $ fromUArray result
  where
    result = array (1,n) $ map swap $ _assocs perm1
    n = _bound perm1
    
-- | The identity (or trivial) permutation.
identityPermutation :: Int -> Permutation 
identityPermutation n = Permutation $ fromPermListN n [1..n]

-- | Multiply together a /non-empty/ list of permutations (the reason for requiring the list to
-- be non-empty is that we don\'t know the size of the result). See also 'multiplyMany''.
productOfPermutations :: [Permutation] -> Permutation 
productOfPermutations [] = error "productOfPermutations: empty list, we don't know size of the result"
productOfPermutations ps = foldl1' multiplyPermutation ps    

-- | Multiply together a (possibly empty) list of permutations, all of which has size @n@
productOfPermutations' :: Int -> [Permutation] -> Permutation 
productOfPermutations' n []       = identityPermutation n
productOfPermutations' n ps@(p:_) = if n == permutationSize p 
  then foldl1' multiplyPermutation ps    
  else error "productOfPermutations': incompatible permutation size(s)"

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
-- > permuteArray pi2 (permuteArray pi1 set) == permuteArray (pi1 `multiplyPermutation` pi2) set
--
-- Synonym to 'permuteArrayRight'
--
{-# SPECIALIZE permuteArray :: Permutation -> Array  Int b   -> Array  Int b   #-}
{-# SPECIALIZE permuteArray :: Permutation -> UArray Int Int -> UArray Int Int #-}
permuteArray :: IArray arr b => Permutation -> arr Int b -> arr Int b    
permuteArray = permuteArrayRight

-- | Right action on lists. Synonym to 'permuteListRight'
--
permuteList :: Permutation -> [a] -> [a]
permuteList = permuteListRight
    
-- | The right (standard) action of permutations on sets. 
-- 
-- > permuteArrayRight pi2 (permuteArrayRight pi1 set) == permuteArrayRight (pi1 `multiplyPermutation` pi2) set
--   
-- The second argument should be an array with bounds @(1,n)@.
-- The function checks the array bounds.
--
{-# SPECIALIZE permuteArrayRight :: Permutation -> Array  Int b   -> Array  Int b   #-}
{-# SPECIALIZE permuteArrayRight :: Permutation -> UArray Int Int -> UArray Int Int #-}
permuteArrayRight :: IArray arr b => Permutation -> arr Int b -> arr Int b    
permuteArrayRight pi@(Permutation perm) ar = 
  if (a==1) && (b==n) 
    then listArray (1,n) [ ar!(perm.!i) | i <- [1..n] ] 
    else error "permuteArrayRight: array bounds do not match"
  where
    n     = _bound perm
    (a,b) = bounds ar   

-- | The right (standard) action on a list. The list should be of length @n@.
--
-- > fromPermutation perm == permuteListRight perm [1..n]
-- 
permuteListRight :: forall a . Permutation -> [a] -> [a]    
permuteListRight perm xs = elems $ permuteArrayRight perm $ arr where
  arr = listArray (1,n) xs :: Array Int a
  n   = permutationSize perm

-- | The left (opposite) action of the permutation group.
--
-- > permuteArrayLeft pi2 (permuteArrayLeft pi1 set) == permuteArrayLeft (pi2 `multiplyPermutation` pi1) set
--
-- It is related to 'permuteLeftArray' via:
--
-- > permuteArrayLeft  pi arr == permuteArrayRight (inversePermutation pi) arr
-- > permuteArrayRight pi arr == permuteArrayLeft  (inversePermutation pi) arr
--
{-# SPECIALIZE permuteArrayLeft :: Permutation -> Array  Int b   -> Array  Int b   #-}
{-# SPECIALIZE permuteArrayLeft :: Permutation -> UArray Int Int -> UArray Int Int #-}
permuteArrayLeft :: IArray arr b => Permutation -> arr Int b -> arr Int b    
permuteArrayLeft pi@(Permutation perm) ar =    
  -- permuteRight (inverse pi) ar
  if (a==1) && (b==n) 
    then array (1,n) [ ( perm.!i , ar!i ) | i <- [1..n] ] 
    else error "permuteArrayLeft: array bounds do not match"
  where
    n     = _bound perm
    (a,b) = bounds ar   

-- | The left (opposite) action on a list. The list should be of length @n@.
--
-- > permuteListLeft perm set == permuteList (inversePermutation perm) set
-- > fromPermutation (inversePermutation perm) == permuteListLeft perm [1..n]
--
permuteListLeft :: forall a. Permutation -> [a] -> [a]    
permuteListLeft perm xs = elems $ permuteArrayLeft perm $ arr where
  arr = listArray (1,n) xs :: Array Int a
  n   = permutationSize perm

--------------------------------------------------------------------------------

-- | Given a list of things, we return a permutation which sorts them into
-- ascending order, that is:
--
-- > permuteList (sortingPermutationAsc xs) xs == sort xs
--
-- Note: if the things are not unique, then the sorting permutations is not
-- unique either; we just return one of them.
--
sortingPermutationAsc :: Ord a => [a] -> Permutation
sortingPermutationAsc xs = toPermutation (map fst sorted) where
  sorted = sortBy (comparing snd) $ zip [1..] xs

-- | Given a list of things, we return a permutation which sorts them into
-- descending order, that is:
--
-- > permuteList (sortingPermutationDesc xs) xs == reverse (sort xs)
--
-- Note: if the things are not unique, then the sorting permutations is not
-- unique either; we just return one of them.
--
sortingPermutationDesc :: Ord a => [a] -> Permutation
sortingPermutationDesc xs = toPermutation (map fst sorted) where
  sorted = sortBy (reverseComparing snd) $ zip [1..] xs

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
    return (Permutation (fromUArray perm), rnd')
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
  inc !u us ( (x:xs) , yys ) = if u >= x
    then inc u us ( xs , x : yys ) 
    else reverse (x:us)  ++ reverse (u:yys) ++ xs
  inc _ _ ( [] , _ ) = error "permute: should not happen"
      
--------------------------------------------------------------------------------


