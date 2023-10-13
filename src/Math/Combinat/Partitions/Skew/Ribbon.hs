
-- | Ribbons (also called border strips, skew hooks, skew rim hooks, etc...).
--
-- Ribbons are skew partitions that are 1) connected, 2) do not contain
-- 2x2 blocks. Intuitively, they are 1-box wide continuous strips on
-- the boundary.
--
-- An alternative definition that they are skew partitions whose projection
-- to the diagonal line is a continuous segment of width 1.

{-# LANGUAGE BangPatterns, ScopedTypeVariables #-}
module Math.Combinat.Partitions.Skew.Ribbon where

--------------------------------------------------------------------------------

import Data.Array
import Data.List
import Data.Maybe

import qualified Data.Map as Map

import Math.Combinat.Sets
import Math.Combinat.Partitions.Integer
import Math.Combinat.Partitions.Integer.IntList ( _diffSequence )
import Math.Combinat.Partitions.Skew
import Math.Combinat.Tableaux
import Math.Combinat.Tableaux.LittlewoodRichardson
import Math.Combinat.Tableaux.GelfandTsetlin
import Math.Combinat.Helper

--------------------------------------------------------------------------------
-- * Corners (TODO: move to Partitions - but we also want to refactor that)

-- | The coordinates of the outer corners 
outerCorners :: Partition -> [(Int,Int)]
outerCorners = outerCornerBoxes

-- | The coordinates of the inner corners, including the two on the two coordinate
-- axes. For the partition @[5,4,1]@ the result should be @[(0,5),(1,4),(2,1),(3,0)]@
extendedInnerCorners:: Partition -> [(Int,Int)]
extendedInnerCorners (Partition_ ps) = (0, head ps') : catMaybes mbCorners where
  ps' = ps ++ [0]
  mbCorners = zipWith3 f [1..] (tail ps') (_diffSequence ps') 
  f !y !x !k = if k > 0 then Just (y,x) else Nothing

-- | Sequence of all the (extended) corners
extendedCornerSequence :: Partition -> [(Int,Int)]
extendedCornerSequence (Partition_ ps) = {- if null ps then [(0,0)] else -} interleave inner outer where
  inner = (0, head ps') : [ (y,x) | (y,x,k) <- zip3 [1..] (tail ps') diff , k>0 ]
  outer =                 [ (y,x) | (y,x,k) <- zip3 [1..] ps'        diff , k>0 ]
  diff = _diffSequence ps'
  ps' = ps ++ [0]

-- | The inner corner /boxes/ of the partition. Coordinates are counted from 1
-- (cf.the 'elements' function), and the first coordinate is the row, the second
-- the column (in English notation).
--
-- For the partition @[5,4,1]@ the result should be @[(1,4),(2,1)]@
--
-- > innerCornerBoxes lambda == (tail $ init $ extendedInnerCorners lambda)
--
innerCornerBoxes :: Partition -> [(Int,Int)]
innerCornerBoxes (Partition_ ps) = 
  case ps of
    []  -> []
    _   -> catMaybes mbCorners 
  where
    mbCorners = zipWith3 f [1..] (tail ps) (_diffSequence ps) 
    f !y !x !k = if k > 0 then Just (y,x) else Nothing

-- | The outer corner /boxes/ of the partition. Coordinates are counted from 1
-- (cf.the 'elements' function), and the first coordinate is the row, the second
-- the column (in English notation).
--
-- For the partition @[5,4,1]@ the result should be @[(1,5),(2,4),(3,1)]@
outerCornerBoxes :: Partition -> [(Int,Int)]
outerCornerBoxes (Partition_ ps) = catMaybes mbCorners where
  mbCorners = zipWith3 f [1..] ps (_diffSequence ps) 
  f !y !x !k = if k > 0 then Just (y,x) else Nothing

-- | The outer and inner corner boxes interleaved, so together they form 
-- the turning points of the full border strip
cornerBoxSequence :: Partition -> [(Int,Int)]
cornerBoxSequence (Partition_ ps) = if null ps then [] else interleave outer inner where
  inner = [ (y,x) | (y,x,k) <- zip3 [1..] tailps diff , k>0 ]
  outer = [ (y,x) | (y,x,k) <- zip3 [1..] ps     diff , k>0 ]
  diff = _diffSequence ps
  tailps = case ps of { [] -> [] ; _-> tail ps }

--------------------------------------------------------------------------------

-- | Naive (and very slow) implementation of @innerCornerBoxes@, for testing purposes
innerCornerBoxesNaive :: Partition -> [(Int,Int)]
innerCornerBoxesNaive part = filter f boxes where
  boxes = elements part
  f (y,x) =       elem (y+1,x  ) boxes
          &&      elem (y  ,x+1) boxes
          && not (elem (y+1,x+1) boxes)

-- | Naive (and very slow) implementation of @outerCornerBoxes@, for testing purposes
outerCornerBoxesNaive :: Partition -> [(Int,Int)]
outerCornerBoxesNaive part = filter f boxes where
  boxes = elements part
  f (y,x) =  not (elem (y+1,x  ) boxes)
          && not (elem (y  ,x+1) boxes)
          && not (elem (y+1,x+1) boxes)

--------------------------------------------------------------------------------
-- * Ribbon

-- | A skew partition is a a ribbon (or border strip) if and only if projected
-- to the diagonals the result is an interval.
isRibbon :: SkewPartition -> Bool
isRibbon skewp = go Nothing proj where
  proj = Map.toList 
       $ Map.fromListWith (+) [ (x-y , 1) | (y,x) <- skewPartitionElements skewp ]
  go Nothing   []            = False
  go (Just _)  []            = True
  go Nothing   ((a,h):rest)  = (h == 1) &&               go (Just a) rest  
  go (Just b)  ((a,h):rest)  = (h == 1) && (a == b+1) && go (Just a) rest

{-
-- | Naive (and slow) reference implementation of "isRibbon"
isRibbonNaive :: SkewPartition -> Bool
isRibbonNaive skewp = isConnectedSkewPartition skewp && no2x2 where
  boxes = skewPartitionElements skewp
  no2x2 = and 
    [ not ( elem (y+1,x  ) boxes &&             
            elem (y  ,x+1) boxes &&  
            elem (y+1,x+1) boxes )        -- no 2x2 blocks 
    | (y,x) <- boxes 
    ]
-}

toRibbon :: SkewPartition -> Maybe Ribbon
toRibbon skew = 
  if not (isRibbon skew)
    then Nothing
    else Just ribbon 
  where
    ribbon =  Ribbon
      { rbShape  = skew
      , rbLength = skewPartitionWeight skew
      , rbHeight = height
      , rbWidth  = width
      }
    elems  = skewPartitionElements skew
    height = (length $ group $ sort $ map fst elems) - 1    -- TODO: optimize these
    width  = (length $ group $ sort $ map snd elems) - 1

-- | Border strips (or ribbons) are defined to be skew partitions which are 
-- connected and do not contain 2x2 blocks.
-- 
-- The /length/ of a border strip is the number of boxes it contains,
-- and its /height/ is defined to be one less than the number of rows
-- (in English notation) it occupies. The /width/ is defined symmetrically to 
-- be one less than the number of columns it occupies.
--
data Ribbon = Ribbon
  { rbShape  :: SkewPartition
  , rbLength :: Int
  , rbHeight :: Int
  , rbWidth  :: Int
  }
  deriving (Eq,Ord,Show)

--------------------------------------------------------------------------------
-- * Inner border strips

-- | Ribbons (or border strips) are defined to be skew partitions which are 
-- connected and do not contain 2x2 blocks. This function returns the
-- border strips whose outer partition is the given one.
innerRibbons :: Partition -> [Ribbon]
innerRibbons part@(Partition ps) = if null ps then [] else strips where

  strips  = [ mkStrip i j 
            | i<-[1..n] , _canStartStrip (annArr!i)
            , j<-[i..n] , _canEndStrip   (annArr!j)
            ]

  n       = length annList
  annList = annotatedInnerBorderStrip part
  annArr  = listArray (1,n) annList

  mkStrip !i1 !i2 = Ribbon shape len height width where
    ps'   = ps ++ [0]
    shape = SkewPartition [ (p-k,k) | (i,p,q) <- zip3 [1..] ps (tail ps') , let k = indent i p q ] 
    indent !i !p !q 
      | i <  y1    = 0
      | i >  y2    = 0
      | i == y2    = p - x2 + 1     -- the order is important here !!!
      | otherwise  = p - q  + 1     -- because of the case y1 == y2 == i

    len    = i2 - i1 + 1
    height = y2 - y1
    width  = x1 - x2
    BorderBox _ _ y1 x1 = annArr ! i1
    BorderBox _ _ y2 x2 = annArr ! i2

-- | Inner border strips (or ribbons) of the given length
innerRibbonsOfLength :: Partition -> Int -> [Ribbon]
innerRibbonsOfLength part@(Partition ps) givenLength = if null ps then [] else strips where

  strips  = [ mkStrip i j 
            | i<-[1..n] , _canStartStrip (annArr!i)
            , j<-[i..n] , _canEndStrip   (annArr!j)
            , j-i+1 == givenLength
            ]

  n       = length annList
  annList = annotatedInnerBorderStrip part
  annArr  = listArray (1,n) annList

  mkStrip !i1 !i2 = Ribbon shape givenLength height width where
    ps'   = ps ++ [0]
    shape = SkewPartition [ (p-k,k) | (i,p,q) <- zip3 [1..] ps (tail ps') , let k = indent i p q ] 
    indent !i !p !q 
      | i <  y1    = 0
      | i >  y2    = 0
      | i == y2    = p - x2 + 1     -- the order is important here !!!
      | otherwise  = p - q  + 1     -- because of the case y1 == y2 == i

    height = y2 - y1
    width  = x1 - x2
    BorderBox _ _ y1 x1 = annArr ! i1
    BorderBox _ _ y2 x2 = annArr ! i2


--------------------------------------------------------------------------------
-- * Outer border strips

-- | Hooks of length @n@ (TODO: move to the partition module)
listHooks :: Int -> [Partition]
listHooks 0 = []
listHooks 1 = [ Partition [1] ]
listHooks n = [ Partition (k : replicate (n-k) 1) | k<-[1..n] ]

-- | Outer border strips (or ribbons) of the given length
outerRibbonsOfLength :: Partition -> Int -> [Ribbon]
outerRibbonsOfLength part@(Partition ps) givenLength = result where

  result = if null ps 
    then [ Ribbon shape givenLength ht wd
         | p <- listHooks givenLength
         , let shape = mkSkewPartition (p,part)
         , let ht = partitionWidth  p - 1        -- pretty inconsistent names here :(((
         , let wd = partitionHeight p - 1
         ]
    else strips 

  strips  = [ mkStrip i j 
            | i<-[1..n] , _canStartStrip (annArr!i)
            , j<-[i..n] , _canEndStrip   (annArr!j)
            , j-i+1 == givenLength
            ]
 
  ysize = partitionWidth  part
  xsize = partitionHeight part
 
  annList  =  [ BorderBox True False 1 x | x <- reverse [xsize+2 .. xsize+givenLength ] ]
           ++ annList0 
           ++ [ BorderBox False True y 1 | y <-         [ysize+2 .. ysize+givenLength ] ]
 
  n        = length annList
  annList0 = annotatedOuterBorderStrip part
  annArr   = listArray (1,n) annList

  mkStrip !i1 !i2 = Ribbon shape len height width where
    ps'   = (-666) : ps ++ replicate (givenLength) 0
    shape = SkewPartition [ (p,k) | (i,p,q) <- zip3 [1..max ysize y2] (tail ps') ps' , let k = indent i p q ] 
    indent !i !p !q 
      | i <  y1    = 0
      | i >  y2    = 0
      | i == y1    = x1 - p    -- the order is important here !!!
--      | i == y2    = x2 - p     
      | otherwise  = q - p  + 1   

    len    = i2 - i1 + 1
    height = y2 - y1
    width  = x1 - x2
    BorderBox _ _ y1 x1 = annArr ! i1
    BorderBox _ _ y2 x2 = annArr ! i2

--------------------------------------------------------------------------------
-- * Naive implementations (for testing)

-- | Naive (and slow) implementation listing all inner border strips
innerRibbonsNaive :: Partition -> [Ribbon]
innerRibbonsNaive outer = list where
  list = [ Ribbon skew (len skew) (ht skew) (wt skew)
         | skew <- allSkewPartitionsWithOuterShape outer
         , isRibbon skew
         ]
  len skew = length (skewPartitionElements skew)
  ht  skew = (length $ group $ sort $ map fst $ skewPartitionElements skew) - 1
  wt  skew = (length $ group $ sort $ map snd $ skewPartitionElements skew) - 1


-- | Naive (and slow) implementation listing all inner border strips of the given length
innerRibbonsOfLengthNaive :: Partition -> Int -> [Ribbon]
innerRibbonsOfLengthNaive outer givenLength = list where
  pweight = partitionWeight outer
  list = [ Ribbon skew (len skew) (ht skew) (wt skew)
         | skew <- skewPartitionsWithOuterShape outer givenLength
         , isRibbon skew
         ]
  len skew = length (skewPartitionElements skew)
  ht  skew = (length $ group $ sort $ map fst $ skewPartitionElements skew) - 1
  wt  skew = (length $ group $ sort $ map snd $ skewPartitionElements skew) - 1

-- | Naive (and slow) implementation listing all outer border strips of the given length
outerRibbonsOfLengthNaive :: Partition -> Int -> [Ribbon]
outerRibbonsOfLengthNaive inner givenLength = list where
  pweight = partitionWeight inner
  list = [ Ribbon skew (len skew) (ht skew) (wt skew)
         | skew <- skewPartitionsWithInnerShape inner givenLength
         , isRibbon skew
         ]
  len skew = length (skewPartitionElements skew)
  ht  skew = (length $ group $ sort $ map fst $ skewPartitionElements skew) - 1
  wt  skew = (length $ group $ sort $ map snd $ skewPartitionElements skew) - 1

--------------------------------------------------------------------------------
-- * Annotated borders

-- | A box on the border of a partition
data BorderBox = BorderBox
  { _canStartStrip :: !Bool
  , _canEndStrip   :: !Bool
  , _yCoord :: !Int
  , _xCoord :: !Int
  }
  deriving Show
 
-- | The boxes of the full inner border strip, annotated with whether a border strip 
-- can start or end there.
annotatedInnerBorderStrip :: Partition -> [BorderBox]
annotatedInnerBorderStrip partition = if isEmptyPartition partition then [] else list where
  list    = goVert (head corners) (tail corners) 
  corners = extendedCornerSequence partition  

  goVert  (y1,x ) ((y2,_ ):rest) = [ BorderBox True (y==y2) y x | y<-[y1+1..y2] ] ++ goHoriz (y2,x) rest
  goVert  _       []             = [] 

  goHoriz (y ,x1) ((_, x2):rest) = case rest of
    [] -> [ BorderBox False True    y x | x<-[x1-1,x1-2..x2+1] ]
    _  -> [ BorderBox False (x/=x2) y x | x<-[x1-1,x1-2..x2  ] ] ++ goVert (y,x2) rest

-- | The boxes of the full outer border strip, annotated with whether a border strip 
-- can start or end there.
annotatedOuterBorderStrip :: Partition -> [BorderBox]
annotatedOuterBorderStrip partition = if isEmptyPartition partition then [] else list where
  list    = goVert (head corners) (tail corners) 
  corners = extendedCornerSequence partition  

  goVert  (y1,x ) ((y2,_ ):rest) = [ BorderBox (y==y1) (y/=y2) (y+1) (x+1) | y<-[y1..y2] ] ++ goHoriz (y2,x) rest
  goVert  _       []             = [] 

  goHoriz (y ,x1) ((_, x2):rest) = case rest of
    [] -> [ BorderBox True (x==0) (y+1) (x+1) | x<-[x1-1,x1-2..x2  ] ]
    _  -> [ BorderBox True False  (y+1) (x+1) | x<-[x1-1,x1-2..x2+1] ] ++ goVert (y,x2) rest


--------------------------------------------------------------------------------
