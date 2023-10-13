
-- | Skew tableaux are skew partitions filled with numbers.
--
-- For example:
--
-- <<svg/skew_tableau.svg>>
--

{-# LANGUAGE CPP, BangPatterns, ScopedTypeVariables, MultiParamTypeClasses #-}

module Math.Combinat.Tableaux.Skew where

--------------------------------------------------------------------------------

import Data.List

import Math.Combinat.Classes
import Math.Combinat.Partitions.Integer
import Math.Combinat.Partitions.Integer.IntList ( _diffSequence )
import Math.Combinat.Partitions.Skew
import Math.Combinat.Tableaux
import Math.Combinat.ASCII
import Math.Combinat.Helper

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

--------------------------------------------------------------------------------
-- * Basics
-- | A skew tableau is represented by a list of offsets and entries
newtype SkewTableau a = SkewTableau [(Int,[a])] deriving (Eq,Ord,Show)

-- unSkewTableau :: SkewTableau a -> [(Int,[a])]
-- unSkewTableau (SkewTableau a) = a

instance Functor SkewTableau where
  fmap f (SkewTableau t) = SkewTableau [ (a, map f xs) | (a,xs) <- t ]

-- | The shape of a skew tableau 
skewTableauShape :: SkewTableau a -> SkewPartition
skewTableauShape (SkewTableau list) = SkewPartition [ (o,length xs) | (o,xs) <- list ]

instance HasShape (SkewTableau a) SkewPartition where
  shape = skewTableauShape

-- | The weight of a tableau is the weight of its shape, or the number of entries
skewTableauWeight :: SkewTableau a -> Int
skewTableauWeight = skewPartitionWeight . skewTableauShape

instance HasWeight (SkewTableau a) where
  weight = skewTableauWeight

--------------------------------------------------------------------------------

-- | The dual of a skew tableau, that is, its mirror image to the main diagonal
dualSkewTableau :: forall a. SkewTableau a -> SkewTableau a
dualSkewTableau (SkewTableau axs) = SkewTableau (go axs) where

  go []  = []  
  go axs = case sub 0 axs of
    (0,[]) -> []
    this   -> this : go (strip axs)

  strip :: [(Int,[a])] -> [(Int,[a])]
  strip []            = []
  strip ((a,xs):rest) = if a>0 
    then (a-1,xs) : strip rest
    else case xs of
      []     -> []
      (z:zs) -> case zs of
        []      -> []
        _       -> (0,zs) : strip rest

  sub :: Int -> [(Int,[a])] -> (Int,[a])
  sub !b [] = (b,[])
  sub !b ((a,this):rest) = if a>0 
    then sub (b+1) rest  
    else (b,ys) where      
      ys = map head $ takeWhile (not . null) (this : map snd rest)

{-
test_dualSkewTableau :: [SkewTableau Int]
test_dualSkewTableau = bad where 
  ps = allPartitions 11
  bad = [ st 
        | p<-ps , q<-ps 
        , (q `isSubPartitionOf` p) 
        , let sp = mkSkewPartition (p,q) 
        , let st = fillSkewPartitionWithRowWord sp [1..] 
        , dualSkewTableau (dualSkewTableau st) /= st
        ]
-}

instance HasDuality (SkewTableau a) where
  dual = dualSkewTableau

--------------------------------------------------------------------------------
-- * Semistandard tableau

-- | A tableau is /semistandard/ if its entries are weekly increasing horizontally
-- and strictly increasing vertically
isSemiStandardSkewTableau :: SkewTableau Int -> Bool
isSemiStandardSkewTableau st@(SkewTableau axs) = weak && strict where
  weak   = and [ isWeaklyIncreasing   xs | (a,xs) <- axs ]
  strict = and [ isStrictlyIncreasing ys | (b,ys) <- bys ]
  SkewTableau bys = dualSkewTableau st

-- | A tableau is /standard/ if it is semistandard and its content is exactly @[1..n]@,
-- where @n@ is the weight.
isStandardSkewTableau :: SkewTableau Int -> Bool
isStandardSkewTableau st = isSemiStandardSkewTableau st && sort (skewTableauRowWord st) == [1..n] where
  n = skewTableauWeight st
  
--------------------------------------------------------------------------------

-- | All semi-standard skew tableaux filled with the numbers @[1..n]@
semiStandardSkewTableaux :: Int -> SkewPartition -> [SkewTableau Int]
semiStandardSkewTableaux n (SkewPartition abs) = map SkewTableau stuff where

  stuff = worker as bs ds (repeat 1) 
  (as,bs) = unzip abs
  ds = _diffSequence as
  
  -- | @worker inner outerMinusInner innerdiffs lowerbound
  worker :: [Int] -> [Int] -> [Int] -> [Int] -> [[(Int,[Int])]]
  worker (a:as) (b:bs) (d:ds) lb = [ (a,this):rest 
                                   | this <- row b 1 lb 
                                   , let lb' = (replicate d 1 ++ map (+1) this) 
                                   , rest <- worker as bs ds lb' ] 
  worker []     _      _      _  = [ [] ]

  -- @row length minimum lowerbound@
  row 0  _  _       = [[]]
  row _  _  []      = []
  row !k !m (!a:as) = [ x:xs | x <- [(max a m)..n] , xs <- row (k-1) x as ] 

{-
-- | from a sequence @[a1,a2,..,an]@ computes the sequence of differences
-- @[a1-a2,a2-a3,...,an-0]@
diffSequence :: [Int] -> [Int]
diffSequence = go where
  go (x:ys@(y:_)) = (x-y) : go ys 
  go [x] = [x]
  go []  = []
-}

--------------------------------------------------------------------------------
-- * ASCII

-- | ASCII drawing of a skew tableau (using the English notation)
asciiSkewTableau :: Show a => SkewTableau a -> ASCII
asciiSkewTableau = asciiSkewTableau' "." EnglishNotation

asciiSkewTableau' 
  :: Show a
  => String               -- ^ string representing the elements of the inner (unfilled) partition
  -> PartitionConvention  -- ^ orientation
  -> SkewTableau a 
  -> ASCII
asciiSkewTableau' innerstr orient (SkewTableau axs) = tabulate (HRight,VTop) (HSepSpaces 1, VSepEmpty) stuff where
  stuff = case orient of
    EnglishNotation    -> es
    EnglishNotationCCW -> reverse (transpose es)
    FrenchNotation     -> reverse es
  inner = asciiFromString innerstr
  es = [ replicate a inner ++ map asciiShow xs | (a,xs) <- axs ]

instance Show a => DrawASCII (SkewTableau a) where
  ascii = asciiSkewTableau

--------------------------------------------------------------------------------
-- * Row \/ column words

-- | The reversed (right-to-left) rows, concatenated
skewTableauRowWord :: SkewTableau a -> [a]
skewTableauRowWord (SkewTableau axs) = concatMap (reverse . snd) axs

-- | The reversed (bottom-to-top) columns, concatenated
skewTableauColumnWord :: SkewTableau a -> [a]
skewTableauColumnWord = skewTableauRowWord . dualSkewTableau

-- | Fills a skew partition with content, in row word order 
fillSkewPartitionWithRowWord :: SkewPartition -> [a] -> SkewTableau a
fillSkewPartitionWithRowWord (SkewPartition abs) xs = SkewTableau $ go abs xs where
  go ((b,a):rest) xs = let (ys,zs) = splitAt a xs in (b,reverse ys) : go rest zs
  go []           xs = []

-- | Fills a skew partition with content, in column word order 
fillSkewPartitionWithColumnWord :: SkewPartition -> [a] -> SkewTableau a
fillSkewPartitionWithColumnWord shape content 
  = dualSkewTableau 
  $ fillSkewPartitionWithRowWord (dualSkewPartition shape) content

--------------------------------------------------------------------------------

-- | If the skew tableau's row word is a lattice word, we can make a partition from its content
skewTableauRowContent :: SkewTableau Int -> Maybe Partition
skewTableauRowContent (SkewTableau axs) = go Map.empty rowword where

  rowword = concatMap (reverse . snd) axs

  finish table = Partition (f 1) where
    f !i = case lkp i of
      0 -> []
      y -> y : f (i+1) 
    lkp j = case Map.lookup j table of
      Just k  -> k
      Nothing -> 0

  go :: Map Int Int -> [Int] -> Maybe Partition
  go !table []     = Just (finish table)
  go !table (i:is) =
    if check i
      then go table' is
      else Nothing
    where
      table'  = Map.insertWith (+) i 1 table
      check j = j==1 || cnt (j-1) >= cnt j
      cnt j   = case Map.lookup j table' of
        Just k  -> k
        Nothing -> 0

--------------------------------------------------------------------------------

