
-- | Skew tableaux are skew partitions filled with numbers.

{-# LANGUAGE BangPatterns #-}

module Math.Combinat.Tableaux.Skew where

--------------------------------------------------------------------------------

import Data.List

import Math.Combinat.Partitions.Integer
import Math.Combinat.Partitions.Skew
import Math.Combinat.Tableaux
import Math.Combinat.ASCII

--------------------------------------------------------------------------------

-- | A skew tableau is represented by a list of offsets and entries
newtype SkewTableau a = SkewTableau [(Int,[a])] deriving (Eq,Ord,Show)

instance Functor SkewTableau where
  fmap f (SkewTableau t) = SkewTableau [ (a, map f xs) | (a,xs) <- t ]
 
skewShape :: SkewTableau a -> SkewPartition
skewShape (SkewTableau list) = SkewPartition [ (o,length xs) | (o,xs) <- list ]

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

--------------------------------------------------------------------------------
