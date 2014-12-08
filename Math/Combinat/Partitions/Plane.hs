
-- | Plane partitions. See eg. <http://en.wikipedia.org/wiki/Plane_partition>

{-# LANGUAGE BangPatterns #-}
module Math.Combinat.Partitions.Plane where

--------------------------------------------------------------------------------

import Data.List

import Math.Combinat.Partitions
import Math.Combinat.Tableaux as Tableaux
import Math.Combinat.Helper

--------------------------------------------------------------------------------
-- * the type of plane partitions

-- | A plane partition encoded as a tablaeu (the \"Z\" heights are the numbers)
newtype PlanePart = PlanePart [[Int]] deriving (Eq,Ord,Show)

fromPlanePart :: PlanePart -> [[Int]]
fromPlanePart (PlanePart xs) = xs

-- | The XY projected shape, as a partition
planePartShape :: PlanePart -> Partition
planePartShape = Tableaux.shape . fromPlanePart

planePartZHeight :: PlanePart -> Int
planePartZHeight (PlanePart xs) = 
  case xs of
    ((h:_):_) -> h
    _         -> 0

planePartWeight :: PlanePart -> Int
planePartWeight (PlanePart xs) = sum' (map sum' xs)

--------------------------------------------------------------------------------
-- * constructing plane partitions

singleLayer :: Partition -> PlanePart
singleLayer = PlanePart . map (\k -> replicate k 1) . fromPartition 

-- | Stacks layers of partitions into a plane partition.
-- This is unsafe in the sense that we don't check that the partitions fit on the top of each other.
unsafeStackLayers :: [Partition] -> PlanePart
unsafeStackLayers []            = PlanePart []
unsafeStackLayers (bottom:rest) = PlanePart $ foldl addLayer (fromPlanePart $ singleLayer bottom) rest where
  addLayer :: [[Int]] -> Partition -> [[Int]]
  addLayer xxs (Partition ps) = [ zipWith (+) xs (replicate p 1 ++ repeat 0) | (xs,p) <- zip xxs (ps ++ repeat 0) ] 


--------------------------------------------------------------------------------

subPartitions :: Int -> Partition -> [Partition]
subPartitions d (Partition ps) = map Partition (_subPartitions d ps)

-- | Sub-partitions of a given partition with the given weight
_subPartitions :: Int -> [Int] -> [[Int]]
_subPartitions d big
  | null big       = if d==0 then [[]] else []
  | d > sum' big   = []
  | d < 0          = []
  | otherwise      = go d (head big) big
  where
    go :: Int -> Int -> [Int] -> [[Int]]
    go !k !h []      = if k==0 then [[]] else []
    go !k !h (b:bs) 
      | k<0 || h<0   = []
      | k==0         = [[]]
      | h==0         = []
      | otherwise    = [ this:rest | this <- [1..min h b] , rest <- go (k-this) this bs ]

--------------------------------------------------------------------------------

allSubPartitions :: Partition -> [Partition]
allSubPartitions (Partition ps) = map Partition (_allSubPartitions ps)

-- | All sub-partitions of a given partition
_allSubPartitions :: [Int] -> [[Int]]
_allSubPartitions big 
  | null big   = [[]]
  | otherwise  = go (head big) big
  where
    go _  [] = [[]]
    go !h (b:bs) 
      | h==0         = []
      | otherwise    = [] : [ this:rest | this <- [1..min h b] , rest <- go this bs ]

--------------------------------------------------------------------------------
-- * generating plane partitions

-- | Plane partitions of a given weight
planePartitions :: Int -> [PlanePart]
planePartitions d 
  | d <  0     = []
  | d == 0     = [PlanePart []]
  | otherwise  = concat [ go (d-n) [p] | n<-[1..d] , p<-partitions n ]
  where
    go :: Int -> [Partition] -> [PlanePart]
    go  0   acc       = [unsafeStackLayers (reverse acc)]
    go !rem acc@(h:_) = concat [ go (rem-k) (this:acc) | k<-[1..rem] , this <- subPartitions k h ]


--------------------------------------------------------------------------------
