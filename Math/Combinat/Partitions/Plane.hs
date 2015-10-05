
-- | Plane partitions. See eg. <http://en.wikipedia.org/wiki/Plane_partition>
--
-- Plane partitions are encoded as lists of lists of Z heights. For example the plane 
-- partition in the picture
-- 
-- <<svg/plane_partition.svg>>
--
-- is encoded as
--
-- > PlanePart [ [5,4,3,3,1]
-- >           , [4,4,2,1]
-- >           , [3,2]
-- >           , [2,1]
-- >           , [1]
-- >           , [1]
-- >           ]
-- 
{-# LANGUAGE BangPatterns #-}
module Math.Combinat.Partitions.Plane where

--------------------------------------------------------------------------------

import Data.List
import Data.Array

import Math.Combinat.Classes
import Math.Combinat.Partitions
import Math.Combinat.Tableaux as Tableaux
import Math.Combinat.Helper

--------------------------------------------------------------------------------
-- * the type of plane partitions

-- | A plane partition encoded as a tablaeu (the \"Z\" heights are the numbers)
newtype PlanePart = PlanePart [[Int]] deriving (Eq,Ord,Show)

fromPlanePart :: PlanePart -> [[Int]]
fromPlanePart (PlanePart xs) = xs

isValidPlanePart :: [[Int]] -> Bool
isValidPlanePart pps = 
  and [ table!(i,j) >= table!(i  ,j+1) &&
        table!(i,j) >= table!(i+1,j  )
      | i<-[0..y-1] , j<-[0..x-1] 
      ]
  where
    table :: Array (Int,Int) Int
    table = accumArray const 0 ((0,0),(y,x)) [ ((i,j),k) | (i,ps) <- zip [0..] pps , (j,k) <- zip [0..] ps ]
    y = length pps
    x = maximum (map length pps)

instance CanBeEmpty PlanePart where
  isEmpty = null . fromPlanePart
  empty   = PlanePart []

-- | Throws an exception if the input is not a plane partition
toPlanePart :: [[Int]] -> PlanePart
toPlanePart pps = if isValidPlanePart pps
  then PlanePart $ filter (not . null) $ map (filter (>0)) $ pps
  else error "toPlanePart: not a plane partition"

-- | The XY projected shape of a plane partition, as an integer partition
planePartShape :: PlanePart -> Partition
planePartShape = Tableaux.tableauShape . fromPlanePart

-- | The Z height of a plane partition
planePartZHeight :: PlanePart -> Int
planePartZHeight (PlanePart xs) = 
  case xs of
    ((h:_):_) -> h
    _         -> 0

planePartWeight :: PlanePart -> Int
planePartWeight (PlanePart xs) = sum' (map sum' xs)

instance HasWeight PlanePart where
  weight = planePartWeight

--------------------------------------------------------------------------------
-- * constructing plane partitions

singleLayer :: Partition -> PlanePart
singleLayer = PlanePart . map (\k -> replicate k 1) . fromPartition 

-- |  Stacks layers of partitions into a plane partition.
-- Throws an exception if they do not form a plane partition.
stackLayers :: [Partition] -> PlanePart
stackLayers layers = if and [ isSubPartitionOf p q | (q,p) <- pairs layers ]
  then unsafeStackLayers layers
  else error "stackLayers: the layers do not form a plane partition"

-- | Stacks layers of partitions into a plane partition.
-- This is unsafe in the sense that we don't check that the partitions fit on the top of each other.
unsafeStackLayers :: [Partition] -> PlanePart
unsafeStackLayers []            = PlanePart []
unsafeStackLayers (bottom:rest) = PlanePart $ foldl addLayer (fromPlanePart $ singleLayer bottom) rest where
  addLayer :: [[Int]] -> Partition -> [[Int]]
  addLayer xxs (Partition ps) = [ zipWith (+) xs (replicate p 1 ++ repeat 0) | (xs,p) <- zip xxs (ps ++ repeat 0) ] 

-- | The \"layers\" of a plane partition (in direction @Z@). We should have
--
-- > unsafeStackLayers (planePartLayers pp) == pp
-- 
planePartLayers :: PlanePart -> [Partition]
planePartLayers pp@(PlanePart xs) = [ layer h | h<-[1..planePartZHeight pp] ] where
  layer h = Partition $ filter (>0) $ map sum' $ (map . map) (f h) xs
  f h = \k -> if k>=h then 1 else 0

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
