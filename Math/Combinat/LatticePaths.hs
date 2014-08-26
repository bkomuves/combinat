
-- | Dyck paths, lattice paths, etc

{-# LANGUAGE BangPatterns #-}
module Math.Combinat.LatticePaths where

--------------------------------------------------------------------------------

import Math.Combinat.Numbers
import Math.Combinat.Trees.Binary

--------------------------------------------------------------------------------
-- * Types

-- | A step in a lattice path
data Step 
  = UpStep         -- ^ the step @(1,1)@
  | DownStep       -- ^ the step @(1,-1)@
  deriving (Eq,Ord,Show)

-- | A lattice path is a path using only the allowed steps. 
--
-- Note that if you rotate such a path by 45 degrees counterclockwise,
-- you get a path which uses only the steps @(1,0)@ and @(0,1)@, and stays
-- above the main diagonal (hence the name, we just use a different convention).
--
type LatticePath = [Step]

--------------------------------------------------------------------------------

-- | A lattice path is called \"valid\", if it never goes below the @y=0@ line.
isValidPath :: LatticePath -> Bool
isValidPath = go 0 where
  go !y []     = y>=0
  go !y (t:ts) = let y' = case t of { UpStep -> y+1 ; DownStep -> y-1 }
                 in  if y'<0 then False 
                             else go y' ts

-- | Maximal height of a lattice path
pathHeight :: LatticePath -> Int
pathHeight = go 0 0 where
  go !h !y []     = h
  go !h !y (t:ts) = case t of
    UpStep   -> go (max h (y+1)) (y+1) ts
    DownStep -> go      h        (y-1) ts

-- | Endpoint of a lattice path, which starts from @(0,0)@.
pathEndpoint :: LatticePath -> (Int,Int)
pathEndpoint = go 0 0 where
  go !x !y []     = (x,y)
  go !x !y (t:ts) = case t of                         
    UpStep   -> go (x+1) (y+1) ts
    DownStep -> go (x+1) (y-1) ts

-- | Returns the coordinates of the path (excluding the starting point @(0,0)@, but including
-- the endpoint
pathCoordinates :: LatticePath -> [(Int,Int)]
pathCoordinates = go 0 0 where
  go _  _  []     = []
  go !x !y (t:ts) = let x' = x + 1
                        y' = case t of { UpStep -> y+1 ; DownStep -> y-1 }
                    in  (x',y') : go x' y' ts

-- | Number of points on the path which touch the @y=0@ zero level line
-- (excluding the starting point @(0,0)@, but including the endpoint; that is, for Dyck paths it this is always positive!).
pathNumberOfZeroTouches :: LatticePath -> Int
pathNumberOfZeroTouches = pathNumberOfTouches' 0

-- | Number of points on the path which touch the level line at height @h@
-- (excluding the starting point @(0,0)@, but including the endpoint).
pathNumberOfTouches' 
  :: Int       -- ^ @h@ = the touch level
  -> LatticePath -> Int
pathNumberOfTouches' h = go 0 0 0 where
  go !cnt _  _  []     = cnt
  go !cnt !x !y (t:ts) = let y'   = case t of { UpStep -> y+1 ; DownStep -> y-1 }
                             cnt' = if y'==h then cnt+1 else cnt
                         in  go cnt' (x+1) y' ts


--------------------------------------------------------------------------------
-- * Dyck paths

-- | @dyckPaths m@ lists all Dyck paths from @(0,0)@ to @(2m,0)@. 
-- 
-- Remark: Dyck paths are obviously in bijection with nested parentheses, and thus
-- also with binary trees.
--
dyckPaths :: Int -> [LatticePath]
dyckPaths = map (map f) . nestedParentheses where
  f p = case p of { LeftParen -> UpStep ; RightParen -> DownStep }

-- | The number of Dyck paths from @(0,0)@ to @(2m,0)@ is simply the m\'th Catalan number.
countDyckPaths :: Int -> Integer
countDyckPaths m = catalan m

--------------------------------------------------------------------------------
-- * Bounded Dyck paths

-- | @boundedDyckPaths h m@ lists all Dyck paths from @(0,0)@ to @(2m,0)@ whose height is at most @h@.
-- Synonym for 'boundedDyckPathsNaive'.
--
boundedDyckPaths
  :: Int   -- ^ @h@ = maximum height
  -> Int   -- ^ @m@ = half-length
  -> [LatticePath]
boundedDyckPaths = boundedDyckPathsNaive 

-- | @boundedDyckPathsNaive h m@ lists all Dyck paths from @(0,0)@ to @(2m,0)@ whose height is at most @h@.
--
-- > sort (boundedDyckPaths h m) == sort [ p | p <- dyckPaths m , pathHeight p <= h ]
-- > sort (boundedDyckPaths m m) == sort (dyckPaths m) 
--
-- Naive recursive algorithm, resulting order is pretty ad-hoc.
--
boundedDyckPathsNaive
  :: Int   -- ^ @h@ = maximum height
  -> Int   -- ^ @m@ = half-length
  -> [LatticePath]
boundedDyckPathsNaive = worker where
  worker !h !m 
    | h<0        = []
    | m<0        = []
    | m==0       = [[]]
    | h<=0       = []
    | otherwise  = as ++ bs 
    where
      bracket p = UpStep : p ++ [DownStep]
      as = [ bracket p      |                 p <- boundedDyckPaths (h-1) (m-1)                                 ]
      bs = [ bracket p ++ q | k <- [1..m-1] , p <- boundedDyckPaths (h-1) (k-1) , q <- boundedDyckPaths h (m-k) ]

--------------------------------------------------------------------------------
-- * More general lattice paths

-- | All lattice paths from @(0,0)@ to @(x,y)@. Clearly empty unless @x-y@ is even.
-- Synonym for 'latticePathsNaive'
--
latticePaths :: (Int,Int) -> [LatticePath]
latticePaths = latticePathsNaive

-- | All lattice paths from @(0,0)@ to @(x,y)@. Clearly empty unless @x-y@ is even.
--
-- Note that
--
-- > sort (dyckPaths n) == sort (latticePaths (0,2*n))
--
-- Naive recursive algorithm, resulting order is pretty ad-hoc.
--
latticePathsNaive :: (Int,Int) -> [LatticePath]
latticePathsNaive (x,y) = worker x y where
  worker !x !y 
    | odd (x-y)     = []
    | x<0           = []
    | y<0           = []
    | y==0          = dyckPaths (div x 2)
    | x==1 && y==1  = [[UpStep]]
    | otherwise     = as ++ bs
    where
      bracket p = UpStep : p ++ [DownStep] 
      as = [ UpStep : p     | p <- worker (x-1) (y-1) ]
      bs = [ bracket p ++ q | k <- [1..(div x 2)] , p <- dyckPaths (k-1) , q <- worker (x-2*k) y ]

--------------------------------------------------------------------------------
-- * Zero-level touches

-- | @touchingDyckPathsNaive k m@ lists all Dyck paths from @(0,0)@ to @(2m,0)@ which touch the 
-- zero level line @y=0@ exactly @k@ times (excluding the starting point, but including the endpoint;
-- thus, @k@ should be positive). Synonym for 'touchingDyckPathsNaive'.
touchingDyckPaths
  :: Int   -- ^ @k@ = number of touches
  -> Int   -- ^ @m@ = half-length
  -> [LatticePath]
touchingDyckPaths = touchingDyckPathsNaive


-- | @touchingDyckPathsNaive k m@ lists all Dyck paths from @(0,0)@ to @(2m,0)@ which touch the 
-- zero level line @y=0@ exactly @k@ times (excluding the starting point, but including the endpoint;
-- thus, @k@ should be positive).
--
-- > sort (touchingDyckPathsNaive k m) == sort [ p | p <- dyckPaths m , pathNumberOfZeroTouches p == k ]
-- 
-- Naive recursive algorithm, resulting order is pretty ad-hoc.
--
touchingDyckPathsNaive
  :: Int   -- ^ @k@ = number of touches
  -> Int   -- ^ @m@ = half-length
  -> [LatticePath]
touchingDyckPathsNaive = worker where
  worker !k !m 
    | m == 0    = if k==0 then [[]] else []
    | k <= 0    = []
    | m <  0    = []
    | k == 1    = [ bracket p      |                 p <- dyckPaths (m-1)                           ]
    | otherwise = [ bracket p ++ q | l <- [1..m-1] , p <- dyckPaths (l-1) , q <- worker (k-1) (m-l) ]
    where
      bracket p = UpStep : p ++ [DownStep] 

--------------------------------------------------------------------------------

