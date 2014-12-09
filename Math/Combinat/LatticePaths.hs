
-- | Dyck paths, lattice paths, etc
--
-- For example, the following figure represents a Dyck path of height 5 with 3 zero-touches (not counting the starting point,
-- but counting the endpoint) and 7 peaks:
--
-- <<svg/dyck_path.svg>>
--

{-# LANGUAGE BangPatterns #-}
module Math.Combinat.LatticePaths where

--------------------------------------------------------------------------------

import Data.List
import System.Random

import Math.Combinat.Numbers
import Math.Combinat.Trees.Binary
import Math.Combinat.ASCII as ASCII

--------------------------------------------------------------------------------
-- * Types

-- | A step in a lattice path
data Step 
  = UpStep         -- ^ the step @(1,1)@
  | DownStep       -- ^ the step @(1,-1)@
  deriving (Eq,Ord,Show)

-- | A lattice path is a path using only the allowed steps, never going below the zero level line @y=0@. 
--
-- Note that if you rotate such a path by 45 degrees counterclockwise,
-- you get a path which uses only the steps @(1,0)@ and @(0,1)@, and stays
-- above the main diagonal (hence the name, we just use a different convention).
--
type LatticePath = [Step]

--------------------------------------------------------------------------------
-- * ascii drawing of paths

-- | Draws the path into a list of lines. For example try:
--
-- > autotabulate RowMajor (Right 5) (map asciiPath $ dyckPaths 4)
--
asciiPath :: LatticePath -> ASCII
asciiPath p = asciiFromLines $ transpose (go 0 p) where

  go !h [] = []
  go !h (x:xs) = case x of
    UpStep   -> ee  h    x : go (h+1) xs
    DownStep -> ee (h-1) x : go (h-1) xs

  maxh   = pathHeight p

  ee h x = replicate (maxh-h-1) ' ' ++ [ch x] ++ replicate h ' '
  ch x   = case x of 
    UpStep   -> '/' 
    DownStep -> '\\' 

--------------------------------------------------------------------------------
-- * elementary queries

-- | A lattice path is called \"valid\", if it never goes below the @y=0@ line.
isValidPath :: LatticePath -> Bool
isValidPath = go 0 where
  go !y []     = y>=0
  go !y (t:ts) = let y' = case t of { UpStep -> y+1 ; DownStep -> y-1 }
                 in  if y'<0 then False 
                             else go y' ts

-- | A Dyck path is a lattice path whose last point lies on the @y=0@ line
isDyckPath :: LatticePath -> Bool
isDyckPath = go 0 where
  go !y []     = y==0
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
-- the endpoint)
pathCoordinates :: LatticePath -> [(Int,Int)]
pathCoordinates = go 0 0 where
  go _  _  []     = []
  go !x !y (t:ts) = let x' = x + 1
                        y' = case t of { UpStep -> y+1 ; DownStep -> y-1 }
                    in  (x',y') : go x' y' ts

-- | Counts the up-steps
pathNumberOfUpSteps :: LatticePath -> Int
pathNumberOfUpSteps   = fst . pathNumberOfUpDownSteps

-- | Counts the down-steps
pathNumberOfDownSteps :: LatticePath -> Int
pathNumberOfDownSteps = snd . pathNumberOfUpDownSteps

-- | Counts both the up-steps and down-steps
pathNumberOfUpDownSteps :: LatticePath -> (Int,Int)
pathNumberOfUpDownSteps = go 0 0 where 
  go !u !d (p:ps) = case p of 
    UpStep   -> go (u+1)  d    ps  
    DownStep -> go  u    (d+1) ps    
  go !u !d []     = (u,d)

--------------------------------------------------------------------------------
-- * path-specific queries

-- | Number of peaks of a path (excluding the endpoint)
pathNumberOfPeaks :: LatticePath -> Int
pathNumberOfPeaks = go 0 where
  go !k (x:xs@(y:_)) = go (if x==UpStep && y==DownStep then k+1 else k) xs
  go !k [x] = k
  go !k [ ] = k

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
-- Order is reverse lexicographical:
--
-- > sort (dyckPaths m) == reverse (dyckPaths m)
-- 
dyckPaths :: Int -> [LatticePath]
dyckPaths = map nestedParensToDyckPath . nestedParentheses 

-- | @dyckPaths m@ lists all Dyck paths from @(0,0)@ to @(2m,0)@. 
--
-- > sort (dyckPathsNaive m) == sort (dyckPaths m) 
--  
-- Naive recursive algorithm, order is ad-hoc
--
dyckPathsNaive :: Int -> [LatticePath]
dyckPathsNaive = worker where
  worker  0 = [[]]
  worker  m = as ++ bs where
    as = [ bracket p      | p <- worker (m-1) ] 
    bs = [ bracket p ++ q | k <- [1..m-1] , p <- worker (k-1) , q <- worker (m-k) ]
  bracket p = UpStep : p ++ [DownStep]

-- | The number of Dyck paths from @(0,0)@ to @(2m,0)@ is simply the m\'th Catalan number.
countDyckPaths :: Int -> Integer
countDyckPaths m = catalan m

-- | The trivial bijection
nestedParensToDyckPath :: [Paren] -> LatticePath
nestedParensToDyckPath = map f where
  f p = case p of { LeftParen -> UpStep ; RightParen -> DownStep }

-- | The trivial bijection in the other direction
dyckPathToNestedParens :: LatticePath -> [Paren]
dyckPathToNestedParens = map g where
  g s = case s of { UpStep -> LeftParen ; DownStep -> RightParen }

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

-- | Lattice paths are counted by the numbers in the Catalan triangle.
countLatticePaths :: (Int,Int) -> Integer
countLatticePaths (x,y) 
  | even (x+y)  = catalanTriangle (div (x+y) 2) (div (x-y) 2)
  | otherwise   = 0

--------------------------------------------------------------------------------
-- * Zero-level touches

-- | @touchingDyckPaths k m@ lists all Dyck paths from @(0,0)@ to @(2m,0)@ which touch the 
-- zero level line @y=0@ exactly @k@ times (excluding the starting point, but including the endpoint;
-- thus, @k@ should be positive). Synonym for 'touchingDyckPathsNaive'.
touchingDyckPaths
  :: Int   -- ^ @k@ = number of zero-touches
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
  :: Int   -- ^ @k@ = number of zero-touches
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


-- | There is a bijection from the set of non-empty Dyck paths of length @2n@ which touch the zero lines @t@ times,
-- to lattice paths from @(0,0)@ to @(2n-t-1,t-1)@ (just remove all the down-steps just before touching
-- the zero line, and also the very first up-step). This gives us a counting formula.
countTouchingDyckPaths 
  :: Int   -- ^ @k@ = number of zero-touches
  -> Int   -- ^ @m@ = half-length
  -> Integer
countTouchingDyckPaths t n
  | t==0 && n==0   = 1
  | otherwise      = countLatticePaths (2*n-t-1,t-1)

--------------------------------------------------------------------------------
-- * Dyck paths with given number of peaks

-- | @peakingDyckPaths k m@ lists all Dyck paths from @(0,0)@ to @(2m,0)@ with exactly @k@ peaks.
--
-- Synonym for 'peakingDyckPathsNaive'
--
peakingDyckPaths
  :: Int      -- ^ @k@ = number of peaks
  -> Int      -- ^ @m@ = half-length
  -> [LatticePath]
peakingDyckPaths = peakingDyckPathsNaive 

-- | @peakingDyckPathsNaive k m@ lists all Dyck paths from @(0,0)@ to @(2m,0)@ with exactly @k@ peaks.
--
-- > sort (peakingDyckPathsNaive k m) = sort [ p | p <- dyckPaths m , pathNumberOfPeaks p == k ]
--  
-- Naive recursive algorithm, resulting order is pretty ad-hoc.
--
peakingDyckPathsNaive 
  :: Int      -- ^ @k@ = number of peaks
  -> Int      -- ^ @m@ = half-length
  -> [LatticePath]
peakingDyckPathsNaive = worker where
  worker !k !m
    | m == 0    = if k==0 then [[]] else []       
    | k <= 0    = []
    | m <  0    = []
    | k == 1    = [ singlePeak m ] 
    | otherwise = as ++ bs ++ cs
    where
      as = [ bracket p      |                                 p <- worker k (m-1)                           ]
      bs = [ smallHill ++ q |                                                       q <- worker (k-1) (m-1) ]
      cs = [ bracket p ++ q | l <- [2..m-1] , a <- [1..k-1] , p <- worker a (l-1) , q <- worker (k-a) (m-l) ]
      smallHill     = [ UpStep , DownStep ]
      singlePeak !m = replicate m UpStep ++ replicate m DownStep 
      bracket p = UpStep : p ++ [DownStep] 

-- | Dyck paths of length @2m@ with @k@ peaks are counted by the Narayana numbers @N(m,k) = \binom{m}{k} \binom{m}{k-1} / m@
countPeakingDyckPaths
  :: Int      -- ^ @k@ = number of peaks
  -> Int      -- ^ @m@ = half-length
  -> Integer
countPeakingDyckPaths k m 
  | m == 0    = if k==0 then 1 else 0
  | k <= 0    = 0
  | m <  0    = 0
  | k == 1    = 1
  | otherwise = div (binomial m k * binomial m (k-1)) (fromIntegral m)

--------------------------------------------------------------------------------
-- * Random lattice paths

-- | A uniformly random Dyck path of length @2m@
randomDyckPath :: RandomGen g => Int -> g -> (LatticePath,g)
randomDyckPath m g0 = (nestedParensToDyckPath parens, g1) where
  (parens,g1) = randomNestedParentheses m g0

--------------------------------------------------------------------------------

