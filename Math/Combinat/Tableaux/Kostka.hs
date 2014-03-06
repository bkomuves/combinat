
-- TODO: better name?

-- | This module contains a function to generate (equivalence classes of) 
-- triangular tableaux of size /k/, strictly increasing to the right and 
-- to the bottom. For example
-- 
-- >  1  
-- >  2  4  
-- >  3  5  8  
-- >  6  7  9  10 
--
-- is such a tableau of size 4.
-- The numbers filling a tableau always consist of an interval @[1..c]@;
-- @c@ is called the /content/ of the tableaux. There is a unique tableau
-- of minimal content @2k-1@:
--
-- >  1  
-- >  2  3  
-- >  3  4  5 
-- >  4  5  6  7 
-- 
-- Let us call the tableaux with maximal content (that is, @m = binomial (k+1) 2@)
-- /standard/. The number of standard tableaux are
--
-- > 1, 1, 2, 12, 286, 33592, 23178480, ...
--
-- OEIS:A003121, \"Strict sense ballot numbers\", 
-- <https://oeis.org/A003121>.
--
-- See 
-- R. M. Thrall, A combinatorial problem, Michigan Math. J. 1, (1952), 81-88.
-- 
-- The number of tableaux with content @c=m-d@ are
-- 
-- >  d=  |     0      1      2      3    ...
-- > -----+----------------------------------------------
-- >  k=2 |     1
-- >  k=3 |     2      1
-- >  k=4 |    12     18      8      1
-- >  k=5 |   286    858   1001    572    165     22     1
-- >  k=6 | 33592 167960 361114 436696 326196 155584 47320 8892 962 52 1 
--
-- We call these \"Kostka tableaux\" (in the lack of a better name), since
-- they are in bijection with the simplicial cones in a canonical simplicial 
-- decompositions of the Gelfand-Tsetlin cones (the content corresponds
-- to the dimension), which encode the combinatorics of Kostka numbers.
--

module Math.Combinat.Tableaux.Kostka 
  ( 
    Tableau
  , Tri(..)
  , TriangularArray
  , fromTriangularArray
  , triangularArrayUnsafe
  , kostkaTableaux
  , _kostkaTableaux
  , countKostkaTableaux
  , kostkaContent
  , _kostkaContent
  ) 
  where

--------------------------------------------------------------------------------

import Data.Ix
import Data.Ord
import Data.List

import Control.Monad
import Control.Monad.ST
import Data.Array.IArray
import Data.Array.Unboxed
import Data.Array.ST

import Math.Combinat.Tableaux (Tableau)
import Math.Combinat.Helper

--------------------------------------------------------------------------------

-- | Triangular arrays
type TriangularArray a = Array Tri a

-- | Set of @(i,j)@ pairs with @i>=j>=1@.
newtype Tri = Tri { unTri :: (Int,Int) } deriving (Eq,Ord,Show)

binom2 :: Int -> Int
binom2 n = (n*(n-1)) `div` 2

index' :: Tri -> Int
index' (Tri (i,j)) = binom2 i + j - 1

-- it should be (1+8*m), 
-- the 2 is a hack to be safe with the floating point stuff
deIndex' :: Int -> Tri 
deIndex' m = Tri ( i+1 , m - binom2 (i+1) + 1 ) where
  i = ( (floor.sqrt.(fromIntegral::Int->Double)) (2+8*m) - 1 ) `div` 2  

instance Ix Tri where
  index   (a,b) x = index' x - index' a 
  inRange (a,b) x = (u<=j && j<=v) where
    u = index' a 
    v = index' b
    j = index' x
  range     (a,b) = map deIndex' [ index' a .. index' b ] 
  rangeSize (a,b) = index' b - index' a + 1 

{-# SPECIALIZE triangularArrayUnsafe :: Tableau Int -> TriangularArray Int #-}
triangularArrayUnsafe :: Tableau a -> TriangularArray a
triangularArrayUnsafe tableau = listArray (Tri (1,1),Tri (k,k)) (concat tableau) 
  where k = length tableau

{-# SPECIALIZE fromTriangularArray :: TriangularArray Int -> Tableau Int #-}
fromTriangularArray :: TriangularArray a -> Tableau a
fromTriangularArray arr = (map.map) snd $ groupBy (equating f) $ assocs arr
  where f = fst . unTri . fst
  
--------------------------------------------------------------------------------

-- "fractional fillings"
data Hole = Hole Int Int deriving (Eq,Ord,Show)

type ReverseTableau      = [[Int ]] 
type ReverseHoleTableau  = [[Hole]]      

toHole :: Int -> Hole
toHole k = Hole k 0

nextHole :: Hole -> Hole
nextHole (Hole k l) = Hole k (l+1)

{-# SPECIALIZE reverseTableau :: [[Int]] -> [[Int]] #-}
reverseTableau :: [[a]] -> [[a]]
reverseTableau = reverse . map reverse

--------------------------------------------------------------------------------

kostkaContent :: TriangularArray Int -> Int
kostkaContent arr = arr ! (snd (bounds arr))

_kostkaContent :: Tableau Int -> Int
_kostkaContent = last . last
 
normalize :: ReverseHoleTableau -> TriangularArray Int 
normalize = snd . normalize'

-- returns ( content , tableau )
normalize' :: ReverseHoleTableau -> ( Int , TriangularArray Int )   
normalize' holes = ( c , array (Tri (1,1), Tri (k,k)) xys ) where
  k = length holes
  c = length sorted
  xys = concat $ zipWith hs [1..] sorted
  hs a xs     = map (h a) xs
  h  a (ij,_) = (Tri ij , a)  
  sorted = groupSortBy snd (concat withPos)
  withPos = zipWith f [1..] (reverseTableau holes) 
  f i xs = zipWith (g i) [1..] xs 
  g i j hole = ((i,j),hole) 

--------------------------------------------------------------------------------

startHole :: [Hole] -> [Int] -> Hole 
startHole (t:ts) (p:ps) = max t (toHole p)
startHole (t:ts) []     = t
startHole []     (p:ps) = toHole p
startHole []     []     = error "startHole"

-- c is the "content" of the small tableau
enumHoles :: Int -> Hole -> [Hole]
enumHoles c start@(Hole k l) 
  = nextHole start 
  : [ Hole i 0 | i <- [k+1..c] ] ++ [ Hole i 1 | i <- [k+1..c] ]

helper :: Int -> [Int] -> [Hole] -> [[Hole]]
helper c [] this = [[]] 
helper c prev@(p:ps) this = 
  [ t:rest | t <- enumHoles c (startHole this prev), rest <- helper c ps (t:this) ]

newLines' :: Int -> [Int] -> [[Hole]]
newLines' c lastReversed = helper c last []  
  where
    top  = head lastReversed
    last = reverse (top : lastReversed)

newLines :: [Int] -> [[Hole]]
newLines lastReversed = newLines' (head lastReversed) lastReversed

-- | Generates all tableaux of size @k@. Effective for @k<=6@.
kostkaTableaux :: Int -> [TriangularArray Int]
kostkaTableaux 0 = [ triangularArrayUnsafe [] ]
kostkaTableaux 1 = [ triangularArrayUnsafe [[1]] ]
kostkaTableaux k = map normalize $ concatMap f smalls where
  smalls :: [ [[Int]] ]
  smalls = map (reverseTableau . fromTriangularArray) $ kostkaTableaux (k-1)
  f :: [[Int]] -> [ [[Hole]] ]
  f small = map (:smallhole) $ map reverse $ newLines (head small) where
    smallhole = map (map toHole) small

_kostkaTableaux :: Int -> [Tableau Int]
_kostkaTableaux k = map fromTriangularArray $ kostkaTableaux k

--------------------------------------------------------------------------------

countKostkaTableaux :: Int -> [Int]
countKostkaTableaux = elems . sizes'

sizes' :: Int -> UArray Int Int
sizes' k = 
  runSTUArray $ do
    let (a,b) = ( 2*k-1 , binom2 (k+1) )
    ar <- newArray (a,b) 0 :: ST s (STUArray s Int Int)   
    mapM_ (worker ar) $ kostkaTableaux k 
    return ar
  where
    worker :: STUArray s Int Int -> TriangularArray Int -> ST s ()
    worker ar t = do
      let c = kostkaContent t 
      n <- readArray ar c  
      writeArray ar c (n+1)
     
--------------------------------------------------------------------------------
