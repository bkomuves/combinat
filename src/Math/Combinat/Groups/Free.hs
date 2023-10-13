
-- | Words in free groups (and free powers of cyclic groups).
--
-- This module is not re-exported by "Math.Combinat"
--
{-# LANGUAGE CPP, BangPatterns, PatternGuards #-}
module Math.Combinat.Groups.Free where

--------------------------------------------------------------------------------

-- new Base exports "Word" from Data.Word...
#ifdef MIN_VERSION_base
#if MIN_VERSION_base(4,7,1)
import Prelude hiding ( Word )
#endif
#elif __GLASGOW_HASKELL__ >= 709
import Prelude hiding ( Word )
#endif

import Data.Char     ( chr )
import Data.List     ( mapAccumL , groupBy )

import Control.Monad ( liftM )
import System.Random

import Math.Combinat.Numbers
import Math.Combinat.Sign
import Math.Combinat.Helper

--------------------------------------------------------------------------------
-- * Words

-- | A generator of a (free) group, indexed by which \"copy\" of the group we are dealing with.
data Generator idx
  = Gen !idx          -- @a@
  | Inv !idx          -- @a^(-1)@
  deriving (Eq,Ord,Show,Read)

-- | The index of a generator
genIdx :: Generator idx -> idx
genIdx g = case g of
  Gen x -> x
  Inv x -> x

-- | The sign of the (exponent of the) generator (that is, the generator is 'Plus', the inverse is 'Minus')
genSign :: Generator idx -> Sign
genSign g = case g of { Gen _ -> Plus ; Inv _ -> Minus }  

genSignValue :: Generator idx -> Int
genSignValue g = case g of { Gen _ -> (1::Int) ; Inv _ -> (-1::Int) } 

-- | keep the index, but return always the 'Gen' one.
absGen :: Generator idx -> Generator idx 
absGen g = case g of
  Gen x -> Gen x
  Inv x -> Gen x

-- | A /word/, describing (non-uniquely) an element of a group.
-- The identity element is represented (among others) by the empty word.
type Word idx = [Generator idx] 

--------------------------------------------------------------------------------

-- | Generators are shown as small letters: @a@, @b@, @c@, ...
-- and their inverses are shown as capital letters, so @A=a^-1@, @B=b^-1@, etc.
showGen :: Generator Int -> Char
showGen (Gen i) = chr (96+i)
showGen (Inv i) = chr (64+i)

showWord :: Word Int -> String
showWord = map showGen

--------------------------------------------------------------------------------
  
instance Functor Generator where
  fmap f g = case g of 
    Gen x -> Gen (f x) 
    Inv y -> Inv (f y)
    
--------------------------------------------------------------------------------

-- | The inverse of a generator
inverseGen :: Generator a -> Generator a
inverseGen g = case g of
  Gen x -> Inv x
  Inv x -> Gen x

-- | The inverse of a word
inverseWord :: Word a -> Word a
inverseWord = map inverseGen . reverse

-- | Lists all words of the given length (total number will be @(2g)^n@).
-- The numbering of the generators is @[1..g]@.
allWords 
  :: Int         -- ^ @g@ = number of generators 
  -> Int         -- ^ @n@ = length of the word
  -> [Word Int]
allWords g = go where
  go !0 = [[]]
  go !n = [ x:xs | xs <- go (n-1) , x <- elems ]
  elems =  [ Gen a | a<-[1..g] ]
        ++ [ Inv a | a<-[1..g] ]

-- | Lists all words of the given length which do not contain inverse generators
-- (total number will be @g^n@).
-- The numbering of the generators is @[1..g]@.
allWordsNoInv 
  :: Int         -- ^ @g@ = number of generators 
  -> Int         -- ^ @n@ = length of the word
  -> [Word Int]
allWordsNoInv g = go where
  go !0 = [[]]
  go !n = [ x:xs | xs <- go (n-1) , x <- elems ]
  elems = [ Gen a | a<-[1..g] ]

--------------------------------------------------------------------------------
-- * Random words

-- | A random group generator (or its inverse) between @1@ and @g@
randomGenerator
  :: RandomGen g
  => Int         -- ^ @g@ = number of generators 
  -> g -> (Generator Int, g)
randomGenerator !d !g0 = (gen, g2) where
  (b, !g1) = random        g0
  (k, !g2) = randomR (1,d) g1
  gen = if b then Gen k else Inv k

-- | A random group generator (but never its inverse) between @1@ and @g@
randomGeneratorNoInv
  :: RandomGen g
  => Int         -- ^ @g@ = number of generators 
  -> g -> (Generator Int, g)
randomGeneratorNoInv !d !g0 = (Gen k, g1) where
  (!k, !g1) = randomR (1,d) g0

-- | A random word of length @n@ using @g@ generators (or their inverses)
randomWord 
  :: RandomGen g
  => Int         -- ^ @g@ = number of generators 
  -> Int         -- ^ @n@ = length of the word
  -> g -> (Word Int, g)
randomWord !d !n !g0 = (word,g1) where
  (g1,word) = mapAccumL (\g _ -> swap (randomGenerator d g)) g0 [1..n]   

-- | A random word of length @n@ using @g@ generators (but not their inverses)
randomWordNoInv
  :: RandomGen g
  => Int         -- ^ @g@ = number of generators 
  -> Int         -- ^ @n@ = length of the word
  -> g -> (Word Int, g)
randomWordNoInv !d !n !g0 = (word,g1) where
  (g1,word) = mapAccumL (\g _ -> swap (randomGeneratorNoInv d g)) g0 [1..n]   
  
--------------------------------------------------------------------------------
-- * The free group on @g@ generators

{-# SPECIALIZE multiplyFree        :: Word Int -> Word Int -> Word Int #-}
{-# SPECIALIZE equivalentFree      :: Word Int -> Word Int -> Bool     #-}
{-# SPECIALIZE reduceWordFree      :: Word Int -> Word Int #-}
{-# SPECIALIZE reduceWordFreeNaive :: Word Int -> Word Int #-}

-- | Multiplication of the free group (returns the reduced result). It is true
-- for any two words w1 and w2 that
--
-- > multiplyFree (reduceWordFree w1) (reduceWord w2) = multiplyFree w1 w2
--
multiplyFree :: Eq idx => Word idx -> Word idx -> Word idx
multiplyFree w1 w2 = reduceWordFree (w1 ++ w2)

-- | Decides whether two words represent the same group element in the free group
equivalentFree :: Eq idx => Word idx -> Word idx -> Bool
equivalentFree w1 w2 = null $ reduceWordFree $ w1 ++ inverseWord w2

-- | Reduces a word in a free group by repeatedly removing @x*x^(-1)@ and
-- @x^(-1)*x@ pairs. The set of /reduced words/ forms the free group; the
-- multiplication is obtained by concatenation followed by reduction.
--
reduceWordFree :: Eq idx => Word idx -> Word idx
reduceWordFree = loop where

  loop w = case reduceStep w of
    Nothing -> w
    Just w' -> loop w'
  
  reduceStep :: Eq a => Word a -> Maybe (Word a)
  reduceStep = go False where    
    go !changed w = case w of
      (Gen x : Inv y : rest) | x==y   -> go True rest
      (Inv x : Gen y : rest) | x==y   -> go True rest
      (this : rest)                   -> liftM (this:) $ go changed rest
      _                               -> if changed then Just w else Nothing


-- | Naive (but canonical) reduction algorithm for the free groups
reduceWordFreeNaive :: Eq idx => Word idx -> Word idx
reduceWordFreeNaive = loop where
  loop w = let w' = step w in if w/=w' then loop w' else w
  step   = concatMap worker . groupBy (equating genIdx) where
  worker gs 
    | s>0       = replicate      s  (Gen i)
    | s<0       = replicate (abs s) (Inv i)
    | otherwise = []
    where 
      i = genIdx (head gs)
      s = sum' (map genSignValue gs)

--------------------------------------------------------------------------------

-- | Counts the number of words of length @n@ which reduce to the identity element.
--
-- Generating function is @Gf_g(u) = \\frac {2g-1} { g-1 + g \\sqrt{ 1 - (8g-4)u^2 } }@
--
countIdentityWordsFree
  :: Int   -- ^ g = number of generators in the free group
  -> Int   -- ^ n = length of the unreduced word
  -> Integer
countIdentityWordsFree g n = countWordReductionsFree g n 0
  
-- | Counts the number of words of length @n@ whose reduced form has length @k@
-- (clearly @n@ and @k@ must have the same parity for this to be nonzero):
--
-- > countWordReductionsFree g n k == sum [ 1 | w <- allWords g n, k == length (reduceWordFree w) ]
--
countWordReductionsFree 
  :: Int   -- ^ g = number of generators in the free group
  -> Int   -- ^ n = length of the unreduced word
  -> Int   -- ^ k = length of the reduced word
  -> Integer
countWordReductionsFree gens_ nn_ kk_
  | nn==0              = if k==0 then 1 else 0
  | even nn && kk == 0 = sum [ ( binomial (nn-i) (n  -i) * gg^(i  ) * (gg-1)^(n  -i  ) * (   i) ) `div` (nn-i) | i<-[0..n  ] ]
  | even nn && even kk = sum [ ( binomial (nn-i) (n-k-i) * gg^(i+1) * (gg-1)^(n+k-i-1) * (kk+i) ) `div` (nn-i) | i<-[0..n-k] ] 
  | odd  nn && odd  kk = sum [ ( binomial (nn-i) (n-k-i) * gg^(i+1) * (gg-1)^(n+k-i  ) * (kk+i) ) `div` (nn-i) | i<-[0..n-k] ]
  | otherwise          = 0  
  where
    g  = fromIntegral gens_ :: Integer
    nn = fromIntegral nn_   :: Integer
    kk = fromIntegral kk_   :: Integer
    
    gg = 2*g
    n = div nn 2
    k = div kk 2
    
--------------------------------------------------------------------------------
-- * Free powers of cyclic groups

{-# SPECIALIZE multiplyZ2 ::        Word Int -> Word Int -> Word Int #-}
{-# SPECIALIZE multiplyZ3 ::        Word Int -> Word Int -> Word Int #-}
{-# SPECIALIZE multiplyZm :: Int -> Word Int -> Word Int -> Word Int #-}

-- | Multiplication in free products of Z2's
multiplyZ2 :: Eq idx => Word idx -> Word idx -> Word idx
multiplyZ2 w1 w2 = reduceWordZ2 (w1 ++ w2)

-- | Multiplication in free products of Z3's
multiplyZ3 :: Eq idx => Word idx -> Word idx -> Word idx
multiplyZ3 w1 w2 = reduceWordZ3 (w1 ++ w2)

-- | Multiplication in free products of Zm's
multiplyZm :: Eq idx => Int -> Word idx -> Word idx -> Word idx
multiplyZm k w1 w2 = reduceWordZm k (w1 ++ w2)

--------------------------------------------------------------------------------

{-# SPECIALIZE equivalentZ2 ::        Word Int -> Word Int -> Bool #-}
{-# SPECIALIZE equivalentZ3 ::        Word Int -> Word Int -> Bool #-}
{-# SPECIALIZE equivalentZm :: Int -> Word Int -> Word Int -> Bool #-}

-- | Decides whether two words represent the same group element in free products of Z2
equivalentZ2 :: Eq idx => Word idx -> Word idx -> Bool
equivalentZ2 w1 w2 = null $ reduceWordZ2 $ w1 ++ inverseWord w2

-- | Decides whether two words represent the same group element in free products of Z3
equivalentZ3 :: Eq idx => Word idx -> Word idx -> Bool
equivalentZ3 w1 w2 = null $ reduceWordZ3 $ w1 ++ inverseWord w2

-- | Decides whether two words represent the same group element in free products of Zm
equivalentZm :: Eq idx => Int -> Word idx -> Word idx -> Bool
equivalentZm m w1 w2 = null $ reduceWordZm m $ w1 ++ inverseWord w2

--------------------------------------------------------------------------------

{-# SPECIALIZE reduceWordZ2 ::        Word Int -> Word Int #-}
{-# SPECIALIZE reduceWordZ3 ::        Word Int -> Word Int #-}
{-# SPECIALIZE reduceWordZm :: Int -> Word Int -> Word Int #-}

--------------------------------------------------------------------------------

-- | Reduces a word, where each generator @x@ satisfies the additional relation @x^2=1@
-- (that is, free products of Z2's)
reduceWordZ2 :: Eq idx => Word idx -> Word idx
reduceWordZ2 = loop where
  loop w = case reduceStep w of
    Nothing -> w
    Just w' -> loop w'
 
  reduceStep :: Eq a => Word a -> Maybe (Word a)
  reduceStep = go False where   
    go !changed w = case w of
      (Gen x : Gen y : rest) | x==y   -> go True rest
      (Gen x : Inv y : rest) | x==y   -> go True rest
      (Inv x : Gen y : rest) | x==y   -> go True rest
      (Inv x : Inv y : rest) | x==y   -> go True rest
      (this : rest)                   -> liftM (absGen this:) $ go changed rest
      _                               -> if changed then Just w else Nothing

-- | Reduces a word, where each generator @x@ satisfies the additional relation @x^3=1@
-- (that is, free products of Z3's)
reduceWordZ3 :: Eq idx => Word idx -> Word idx
reduceWordZ3 = loop where
  loop w = case reduceStep w of
    Nothing -> w
    Just w' -> loop w'
 
  reduceStep :: Eq a => Word a -> Maybe (Word a)
  reduceStep = go False where   
    go !changed w = case w of
      (Gen x : Inv y : rest)         | x==y           -> go True rest
      (Inv x : Gen y : rest)         | x==y           -> go True rest
      (Gen x : Gen y : Gen z : rest) | x==y && y==z   -> go True rest
      (Inv x : Inv y : Inv z : rest) | x==y && y==z   -> go True rest
      (Gen x : Gen y : rest)         | x==y           -> go True (Inv x : rest)       -- !!!
      (Inv x : Inv y : rest)         | x==y           -> go True (Gen x : rest)
      (this : rest)                                   -> liftM (this:) $ go changed rest
      _                                               -> if changed then Just w else Nothing
      
-- | Reduces a word, where each generator @x@ satisfies the additional relation @x^m=1@
-- (that is, free products of Zm's)
reduceWordZm :: Eq idx => Int -> Word idx -> Word idx
reduceWordZm m = loop where

  loop w = case reduceStep w of
    Nothing -> w
    Just w' -> loop w'

  halfm = div m 2  -- if we encounter strictly more than m/2 equal elements in a row, we replace them by the inverses
 
  -- reduceStep :: Eq a => Word a -> Maybe (Word a)
  reduceStep = go False where   
    go !changed w = case w of
      (Gen x : Inv y : rest) | x==y                        -> go True rest
      (Inv x : Gen y : rest) | x==y                        -> go True rest
      something | Just (k,rest) <- dropIfMoreThanHalf w    -> go True (replicate (m-k) (inverseGen (head w)) ++ rest)
      (this : rest)                                        -> liftM (this:) $ go changed rest
      _                                                    -> if changed then Just w else Nothing
  
  -- dropIfMoreThanHalf :: Eq a => Word a -> Maybe (Int, Word a)
  dropIfMoreThanHalf w = 
    let (!k,rest) = dropWhileEqual w 
    in  if k > halfm then Just (k,rest)
                     else Nothing
                     
  -- dropWhileEqual :: Eq a => Word a -> (Int, Word a) 
  dropWhileEqual []     = (0,[])
  dropWhileEqual (x0:rest) = go 1 rest where
    go !k []         = (k,[])
    go !k xxs@(x:xs) = if k==m then (m,xxs) 
                               else if x==x0 then go (k+1) xs 
                                             else (k,xxs)

{-  
  dropm :: Eq a => Word a -> Maybe (Word a)    
  dropm []     = Nothing
  dropm (x:xs) = go (m-1) xs where
    go 0 rest    = Just rest
    go j (y:ys)  = if y==x 
      then go (j-1) ys
      else Nothing 
    go j []      = Nothing
-}

--------------------------------------------------------------------------------

{-# SPECIALIZE reduceWordZ2Naive ::        Word Int -> Word Int #-}
{-# SPECIALIZE reduceWordZ3Naive ::        Word Int -> Word Int #-}
{-# SPECIALIZE reduceWordZmNaive :: Int -> Word Int -> Word Int #-}

-- | Reduces a word, where each generator @x@ satisfies the additional relation @x^2=1@
-- (that is, free products of Z2's). Naive (but canonical) algorithm.
reduceWordZ2Naive :: Eq idx => Word idx -> Word idx
reduceWordZ2Naive = loop where
  loop w = let w' = step w in if w/=w' then loop w' else w
  step   = concatMap worker . groupBy (equating genIdx) where
  worker gs = 
    case mod s 2 of
      1 -> [Gen i]
      0 -> []
      _ -> error "reduceWordZ2: fatal error, shouldn't happen"
    where 
      i = genIdx (head gs)
      s = sum' (map genSignValue gs)

-- | Reduces a word, where each generator @x@ satisfies the additional relation @x^3=1@
-- (that is, free products of Z3's). Naive (but canonical) algorithm.
reduceWordZ3Naive :: Eq idx => Word idx -> Word idx
reduceWordZ3Naive = loop where
  loop w = let w' = step w in if w/=w' then loop w' else w
  step   = concatMap worker . groupBy (equating genIdx) where
  worker gs = 
    case mod s 3 of
      0 -> []
      1 -> [Gen i]
      2 -> [Inv i]
      _ -> error "reduceWordZ3: fatal error, shouldn't happen"
    where 
      i = genIdx (head gs)
      s = sum' (map genSignValue gs)

-- | Reduces a word, where each generator @x@ satisfies the additional relation @x^m=1@
-- (that is, free products of Zm's). Naive (but canonical) algorithm.
reduceWordZmNaive :: Eq idx => Int -> Word idx -> Word idx
reduceWordZmNaive m = loop where
  loop w = let w' = step w in if w/=w' then loop w' else w
  step   = concatMap worker . groupBy (equating genIdx) where
  halfm1 = div (m+1) 2
  worker gs 
    | mods <= halfm1  = replicate    mods  (Gen i)
    | otherwise       = replicate (m-mods) (Inv i)
    where 
      i = genIdx (head gs)
      s = sum' (map genSignValue gs)
      mods = mod s m

--------------------------------------------------------------------------------

-- | Counts the number of words (without inverse generators) of length @n@ 
-- which reduce to the identity element, using the relations @x^2=1@.
--
-- Generating function is @Gf_g(u) = \\frac {2g-2} { g-2 + g \\sqrt{ 1 - (4g-4)u^2 } }@
--
-- The first few @g@ cases:
--
-- > A000984 = [ countIdentityWordsZ2 2 (2*n) | n<-[0..] ] = [1,2,6,20,70,252,924,3432,12870,48620,184756...]
-- > A089022 = [ countIdentityWordsZ2 3 (2*n) | n<-[0..] ] = [1,3,15,87,543,3543,23823,163719,1143999,8099511,57959535...]
-- > A035610 = [ countIdentityWordsZ2 4 (2*n) | n<-[0..] ] = [1,4,28,232,2092,19864,195352,1970896,20275660,211823800,2240795848...]
-- > A130976 = [ countIdentityWordsZ2 5 (2*n) | n<-[0..] ] = [1,5,45,485,5725,71445,925965,12335685,167817405,2321105525,32536755565...]
--
countIdentityWordsZ2
  :: Int   -- ^ g = number of generators in the free group
  -> Int   -- ^ n = length of the unreduced word
  -> Integer
countIdentityWordsZ2 g n = countWordReductionsZ2 g n 0

-- | Counts the number of words (without inverse generators) of length @n@ whose 
-- reduced form in the product of Z2-s (that is, for each generator @x@ we have @x^2=1@) 
-- has length @k@
-- (clearly @n@ and @k@ must have the same parity for this to be nonzero):
--
-- > countWordReductionsZ2 g n k == sum [ 1 | w <- allWordsNoInv g n, k == length (reduceWordZ2 w) ]
--
countWordReductionsZ2 
  :: Int   -- ^ g = number of generators in the free group
  -> Int   -- ^ n = length of the unreduced word
  -> Int   -- ^ k = length of the reduced word
  -> Integer
countWordReductionsZ2 gens_ nn_ kk_
  | nn==0              = if k==0 then 1 else 0
  | even nn && kk == 0 = sum [ ( binomial (nn-i) (n  -i) * g^(i  ) * (g-1)^(n  -i  ) * (   i) ) `div` (nn-i) | i<-[0..n  ] ]
  | even nn && even kk = sum [ ( binomial (nn-i) (n-k-i) * g^(i+1) * (g-1)^(n+k-i-1) * (kk+i) ) `div` (nn-i) | i<-[0..n-k] ] 
  | odd  nn && odd  kk = sum [ ( binomial (nn-i) (n-k-i) * g^(i+1) * (g-1)^(n+k-i  ) * (kk+i) ) `div` (nn-i) | i<-[0..n-k] ]
  | otherwise          = 0  
  where
    g  = fromIntegral gens_ :: Integer
    nn = fromIntegral nn_   :: Integer
    kk = fromIntegral kk_   :: Integer
    
    n = div nn 2
    k = div kk 2

-- | Counts the number of words (without inverse generators) of length @n@ 
-- which reduce to the identity element, using the relations @x^3=1@.
--
-- > countIdentityWordsZ3NoInv g n == sum [ 1 | w <- allWordsNoInv g n, 0 == length (reduceWordZ2 w) ]
--
-- In mathematica, the formula is: @Sum[ g^k * (g-1)^(n-k) * k/n * Binomial[3*n-k-1, n-k] , {k, 1,n} ]@
--
countIdentityWordsZ3NoInv
  :: Int   -- ^ g = number of generators in the free group
  -> Int   -- ^ n = length of the unreduced word
  -> Integer
countIdentityWordsZ3NoInv gens_ nn_ 
  | nn==0           = 1
  | mod nn 3 == 0   = sum [ ( binomial (3*n-i-1) (n-i) * g^i * (g-1)^(n-i) * i ) `div` n | i<-[1..n] ]
  | otherwise       = 0
  where
    g  = fromIntegral gens_ :: Integer
    nn = fromIntegral nn_   :: Integer
    
    n = div nn 3
  
--------------------------------------------------------------------------------
      
{-

-- some basic testing. TODO: real tests

import Math.Combinat.Helper
import Math.Combinat.Groups.Free

g    = 3 :: Int
maxn = 8 :: Int

bad_free = [ w | n<-[0..maxn] , w <- allWords g n , not (reduceWordFree w `equivalentFree` reduceWordFreeNaive w) ]
bad_z2   = [ w | n<-[0..maxn] , w <- allWords g n , not (reduceWordZ2   w `equivalentZ2`   reduceWordZ2Naive   w) ]
bad_z3   = [ w | n<-[0..maxn] , w <- allWords g n , not (reduceWordZ3   w `equivalentZ3`   reduceWordZ3Naive   w) ]
bad_zm m = [ w | n<-[0..maxn] , w <- allWords g n , not (equivalentZm m (reduceWordZm m w) (reduceWordZmNaive m w)) ]

speed_free = sum' [ length (reduceWordFree w) | n<-[0..maxn] , w <- allWords g n ]
speed_z2   = sum' [ length (reduceWordZ2   w) | n<-[0..maxn] , w <- allWords g n ]
speed_z3   = sum' [ length (reduceWordZ3   w) | n<-[0..maxn] , w <- allWords g n ]
speed_zm m = sum' [ length (reduceWordZm m w) | n<-[0..maxn] , w <- allWords g n ]

naive_speed_free = sum' [ length (reduceWordFreeNaive w) | n<-[0..maxn] , w <- allWords g n ]
naive_speed_z2   = sum' [ length (reduceWordZ2Naive   w) | n<-[0..maxn] , w <- allWords g n ]
naive_speed_z3   = sum' [ length (reduceWordZ3Naive   w) | n<-[0..maxn] , w <- allWords g n ]
naive_speed_zm m = sum' [ length (reduceWordZmNaive m w) | n<-[0..maxn] , w <- allWords g n ]

-}

--------------------------------------------------------------------------------


