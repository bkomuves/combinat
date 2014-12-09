
-- | Young tableaux and similar gadgets. 
--   See e.g. William Fulton: Young Tableaux, with Applications to 
--   Representation theory and Geometry (CUP 1997).
-- 
--   The convention is that we use 
--   the English notation, and we store the tableaux as lists of the rows.
-- 
--   That is, the following standard Young tableau of shape [5,4,1]
-- 
-- >  1  3  4  6  7
-- >  2  5  8 10
-- >  9
--
-- <<svg/young_tableau.svg>>
--
--   is encoded conveniently as
-- 
-- > [ [ 1 , 3 , 4 , 6 , 7 ]
-- > , [ 2 , 5 , 8 ,10 ]
-- > , [ 9 ]
-- > ]
--

module Math.Combinat.Tableaux where

import Data.List

import Math.Combinat.Helper
import Math.Combinat.Numbers (factorial,binomial)
import Math.Combinat.Partitions

--------------------------------------------------------------------------------
-- * Basic stuff

type Tableau a = [[a]]

_shape :: Tableau a -> [Int]
_shape t = map length t 

shape :: Tableau a -> Partition
shape t = toPartition (_shape t)

dualTableau :: Tableau a -> Tableau a
dualTableau = transpose

content :: Tableau a -> [a]
content = concat

-- | An element @(i,j)@ of the resulting tableau (which has shape of the
-- given partition) means that the vertical part of the hook has length @i@,
-- and the horizontal part @j@. The /hook length/ is thus @i+j-1@. 
--
-- Example:
--
-- > > mapM_ print $ hooks $ toPartition [5,4,1]
-- > [(3,5),(2,4),(2,3),(2,2),(1,1)]
-- > [(2,4),(1,3),(1,2),(1,1)]
-- > [(1,1)]
--
hooks :: Partition -> Tableau (Int,Int)
hooks part = zipWith f p [1..] where 
  p = fromPartition part
  q = _dualPartition p
  f l i = zipWith (\x y -> (x-i+1,y)) q [l,l-1..1] 

hookLengths :: Partition -> Tableau Int
hookLengths part = (map . map) (\(i,j) -> i+j-1) (hooks part) 

--------------------------------------------------------------------------------
-- * Row and column words

rowWord :: Tableau a -> [a]
rowWord = concat . reverse

rowWordToTableau :: Ord a => [a] -> Tableau a
rowWordToTableau xs = reverse rows where
  rows = break xs
  break [] = [[]]
  break [x] = [[x]]
  break (x:xs@(y:_)) = if x>y
    then [x] : break xs
    else let (h:t) = break xs in (x:h):t

columnWord :: Tableau a -> [a]
columnWord = rowWord . transpose

columnWordToTableau :: Ord a => [a] -> Tableau a
columnWordToTableau = transpose . rowWordToTableau
    
--------------------------------------------------------------------------------
-- * Standard Young tableaux

-- | Standard Young tableaux of a given shape.
--   Adapted from John Stembridge, 
--   <http://www.math.lsa.umich.edu/~jrs/software/SFexamples/tableaux>.
standardYoungTableaux :: Partition -> [Tableau Int]
standardYoungTableaux shape' = map rev $ tableaux shape where
  shape = fromPartition shape'
  rev = reverse . map reverse
  tableaux :: [Int] -> [Tableau Int]
  tableaux p = 
    case p of
      []  -> [[]]
      [n] -> [[[n,n-1..1]]]
      _   -> worker (n,k) 0 [] p
    where
      n = sum p
      k = length p
  worker :: (Int,Int) -> Int -> [Int] -> [Int] -> [Tableau Int]
  worker _ _ _ [] = []
  worker nk i ls (x:rs) = case rs of
    (y:_) -> if x==y 
      then worker nk (i+1) (x:ls) rs
      else worker2 nk i ls x rs
    [] ->  worker2 nk i ls x rs
  worker2 :: (Int,Int) -> Int -> [Int] -> Int -> [Int] -> [Tableau Int]
  worker2 nk@(n,k) i ls x rs = new ++ worker nk (i+1) (x:ls) rs where
    old = if x>1 
      then             tableaux $ reverse ls ++ (x-1) : rs
      else map ([]:) $ tableaux $ reverse ls ++ rs   
    a = k-1-i
    new = {- debug ( i , a , head old , f a (head old) ) $ -}
      map (f a) old
    f :: Int -> Tableau Int -> Tableau Int
    f _ [] = []
    f 0 (t:ts) = (n:t) : f (-1) ts
    f j (t:ts) = t : f (j-1) ts
  
-- | hook-length formula
countStandardYoungTableaux :: Partition -> Integer
countStandardYoungTableaux part = {- debug (hookLengths part) $ -}
  factorial n `div` h where
    h = product $ map fromIntegral $ concat $ hookLengths part 
    n = weight part
        
--------------------------------------------------------------------------------
-- * Semistandard Young tableaux
   
-- | Semistandard Young tableaux of given shape, \"naive\" algorithm    
semiStandardYoungTableaux :: Int -> Partition -> [Tableau Int]
semiStandardYoungTableaux n part = worker (repeat 0) shape where
  shape = fromPartition part
  worker _ [] = [[]] 
  worker prevRow (s:ss) 
    = [ (r:rs) | r <- row n s 1 prevRow, rs <- worker (map (+1) r) ss ]

  -- weekly increasing lists of length @len@, pointwise at least @xs@, 
  -- maximum value @n@, minimum value @prev@.
  row :: Int -> Int -> Int -> [Int] -> [[Int]]
  row _ 0   _    _      = [[]]
  row n len prev (x:xs) = [ (a:as) | a <- [max x prev..n] , as <- row n (len-1) a xs ]

-- | Stanley's hook formula (cf. Fulton page 55)
countSemiStandardYoungTableaux :: Int -> Partition -> Integer
countSemiStandardYoungTableaux n shape = k `div` h where
  h = product $ map fromIntegral $ concat $ hookLengths shape 
  k = product [ fromIntegral (n+j-i) | (i,j) <- elements shape ]
  
--------------------------------------------------------------------------------
    