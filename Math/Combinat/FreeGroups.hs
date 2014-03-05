
-- | Words in free groups (and free products of cyclic groups) 
--
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

-- | Counts the number of words of length @n@ whose free reduced form has length @k@
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
    