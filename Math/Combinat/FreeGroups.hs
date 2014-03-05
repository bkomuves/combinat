
-- | Words in free groups (and free powers of cyclic groups) 
--
{-# LANGUAGE PatternGuards #-}
module Math.Combinat.FreeGroups where

--------------------------------------------------------------------------------

import Control.Monad (liftM)

import Math.Combinat.Numbers

--------------------------------------------------------------------------------

-- | A generator of a (free) group
data Generator a 
  = Gen a          -- @a@
  | Inv a          -- @a^{-1}@
  deriving (Eq,Ord,Show,Read)

-- | A /word/, describing (non-uniquely) an element of a group.
-- The identity element is represented (among others) by the empty word.
type Word a = [Generator a] 

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
  go 0 = [[]]
  go n = [ x:xs | xs <- go (n-1) , x <- elems ]
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
  go 0 = [[]]
  go n = [ x:xs | xs <- go (n-1) , x <- elems ]
  elems = [ Gen a | a<-[1..g] ]
  
--------------------------------------------------------------------------------
-- * The free group on @g@ generators

-- | Multiplication of the free group (returns the reduced result). It is true
-- for any two words w1 and w2 that
--
-- > multiplyFree (reduceWordFree w1) (reduceWord w2) = multiplyFree w1 w2
--
multiplyFree :: Eq a => Word a -> Word a -> Word a
multiplyFree w1 w2 = reduceWordFree (w1++w2)

-- | Reduces a word in a free group by repeatedly removing @x*x^{-1}@ and
-- @x^{-1}*x@ pairs. The set of /reduced words/ forms the free group; the
-- multiplication is obtained by concatenation followed by reduction.
--
reduceWordFree :: Eq a => Word a -> Word a
reduceWordFree = loop where

  loop w = case reduceStep w of
    Nothing -> w
    Just w' -> loop w'
  
  reduceStep :: Eq a => Word a -> Maybe (Word a)
  reduceStep = go False where    
    go changed w = case w of
      (Gen x : Inv y : rest) | x==y   -> go True rest
      (Inv x : Gen y : rest) | x==y   -> go True rest
      (this : rest)                   -> liftM (this:) $ go changed rest
      _                               -> if changed then Just w else Nothing

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

-- | Multiplication in free products of Z2's
multiplyZ2 :: Eq a => Word a -> Word a -> Word a
multiplyZ2 w1 w2 = reduceWordZ2 (w1++w2)

-- | Multiplication in free products of Z3's
multiplyZ3 :: Eq a => Word a -> Word a -> Word a
multiplyZ3 w1 w2 = reduceWordZ3 (w1++w2)

-- | Multiplication in free products of Zm's
multiplyZm :: Eq a => Int -> Word a -> Word a -> Word a
multiplyZm k w1 w2 = reduceWordZm k (w1++w2)

--------------------------------------------------------------------------------

-- | Reduces a word, where each generator @x@ satisfies the additional relation @x^2=1@
-- (that is, free products of Z2's)
reduceWordZ2 :: Eq a => Word a -> Word a
reduceWordZ2 = loop where
  loop w = case reduceStep w of
    Nothing -> w
    Just w' -> loop w'
 
  reduceStep :: Eq a => Word a -> Maybe (Word a)
  reduceStep = go False where   
    go changed w = case w of
      (Gen x : Gen y : rest) | x==y   -> go True rest
      (Gen x : Inv y : rest) | x==y   -> go True rest
      (Inv x : Gen y : rest) | x==y   -> go True rest
      (Inv x : Inv y : rest) | x==y   -> go True rest
      (this : rest)                   -> liftM (this:) $ go changed rest
      _                               -> if changed then Just w else Nothing

-- | Reduces a word, where each generator @x@ satisfies the additional relation @x^3=1@
-- (that is, free products of Z3's)
reduceWordZ3 :: Eq a => Word a -> Word a
reduceWordZ3 = loop where
  loop w = case reduceStep w of
    Nothing -> w
    Just w' -> loop w'
 
  reduceStep :: Eq a => Word a -> Maybe (Word a)
  reduceStep = go False where   
    go changed w = case w of
      (Gen x : Inv y : rest)         | x==y           -> go True rest
      (Inv x : Gen y : rest)         | x==y           -> go True rest
      (Gen x : Gen y : Gen z : rest) | x==y && y==z   -> go True rest
      (Inv x : Inv y : Inv z : rest) | x==y && y==z   -> go True rest
      (this : rest)                                   -> liftM (this:) $ go changed rest
      _                                               -> if changed then Just w else Nothing
      
-- | Reduces a word, where each generator @x@ satisfies the additional relation @x^m=1@
-- (that is, free products of Zm's)
reduceWordZm :: Eq a => Int -> Word a -> Word a
reduceWordZm k = loop where
  loop w = case reduceStep w of
    Nothing -> w
    Just w' -> loop w'
 
  reduceStep :: Eq a => Word a -> Maybe (Word a)
  reduceStep = go False where   
    go changed w = case w of
      (Gen x : Inv y : rest) | x==y                  -> go True rest
      (Inv x : Gen y : rest) | x==y                  -> go True rest
      something              | Just rest <- dropk w  -> go True rest
      (this : rest)                                  -> liftM (this:) $ go changed rest
      _                                              -> if changed then Just w else Nothing
  
  dropk :: Eq a => Word a -> Maybe (Word a)    
  dropk []     = Nothing
  dropk (x:xs) = go (k-1) xs where
    go 0 rest    = Just rest
    go j (y:ys)  = if y==x 
      then go (j-1) ys
      else Nothing 
    go j []      = Nothing

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
          
--------------------------------------------------------------------------------
      