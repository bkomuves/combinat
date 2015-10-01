
-- | Skew tableaux are skew partitions filled with numbers.

{-# LANGUAGE BangPatterns, ScopedTypeVariables #-}

module Math.Combinat.Tableaux.Skew where

--------------------------------------------------------------------------------

import Data.List

import Math.Combinat.Partitions.Integer
import Math.Combinat.Partitions.Skew
import Math.Combinat.Tableaux
import Math.Combinat.ASCII

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

--------------------------------------------------------------------------------

-- | A skew tableau is represented by a list of offsets and entries
newtype SkewTableau a = SkewTableau [(Int,[a])] deriving (Eq,Ord,Show)

-- unSkewTableau :: SkewTableau a -> [(Int,[a])]
-- unSkewTableau (SkewTableau a) = a

instance Functor SkewTableau where
  fmap f (SkewTableau t) = SkewTableau [ (a, map f xs) | (a,xs) <- t ]
 
skewShape :: SkewTableau a -> SkewPartition
skewShape (SkewTableau list) = SkewPartition [ (o,length xs) | (o,xs) <- list ]

--------------------------------------------------------------------------------

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

--------------------------------------------------------------------------------

-- | Semi-standard skew tableaux filled with numbers @[1..n]@
semiStandardSkewTableaux :: Int -> SkewPartition -> [SkewTableau Int]
semiStandardSkewTableaux n (SkewPartition abs) = map SkewTableau stuff where

  stuff = worker as bs ds (repeat 1) 
  (as,bs) = unzip abs
  ds = diffSequence as
  
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

asciiSkewTableau :: Show a => SkewTableau a -> ASCII
asciiSkewTableau = asciiSkewTableau' "." EnglishNotation

asciiSkewTableau' 
  :: Show a
  => String              -- ^ string representing the elements of the inner (unfilled) partition
  -> PartitionConvention -- Orientation
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

-- | The reversed rows, concatenated
skewTableauRowWord :: SkewTableau a -> [a]
skewTableauRowWord (SkewTableau axs) = concatMap (reverse . snd) axs

-- | The reversed rows, concatenated
skewTableauColumnWord :: SkewTableau a -> [a]
skewTableauColumnWord = skewTableauRowWord . dualSkewTableau

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
