
-- | Gelfand-Tsetlin patterns and Kostka numbers.
--
-- Gelfand-Tsetlin patterns (or tableaux) are triangular arrays like
--
-- > [ 3 ]
-- > [ 3 , 2 ]
-- > [ 3 , 1 , 0 ]
-- > [ 2 , 0 , 0 , 0 ]
--
-- with both rows and columns non-increasing non-negative integers.
-- Note: these are in bijection with the semi-standard Young tableaux.
--
-- If we add the further restriction that
-- the top diagonal reads @lambda@, 
-- and the diagonal sums are partial sums of @mu@, where @lambda@ and @mu@ are two
-- partitions (in this case @lambda=[3,2]@ and @mu=[2,1,1,1]@), 
-- then the number of the resulting patterns 
-- or tableaux is the Kostka number @K(lambda,mu)@.
-- Actually @mu@ doesn't even need to the be non-increasing.
--

{-# LANGUAGE BangPatterns, ScopedTypeVariables #-}
module Math.Combinat.Tableaux.GelfandTsetlin where

--------------------------------------------------------------------------------

import Data.List
import Data.Maybe
import Data.Monoid
import Data.Ord

import Control.Monad
import Control.Monad.Trans.State

import Data.Map (Map)
import qualified Data.Map as Map

import Math.Combinat.Partitions.Integer
import Math.Combinat.Tableaux
import Math.Combinat.Helper
import Math.Combinat.ASCII

--------------------------------------------------------------------------------
-- * Kostka numbers

-- | Kostka numbers (via counting Gelfand-Tsetlin patterns). See for example <http://en.wikipedia.org/wiki/Kostka_number>
--
-- @K(lambda,mu)==0@ unless @lambda@ dominates @mu@:
--
-- > [ mu | mu <- partitions (weight lam) , kostkaNumber lam mu > 0 ] == dominatedPartitions lam
--
kostkaNumber :: Partition -> Partition -> Int
kostkaNumber = countKostkaGelfandTsetlinPatterns

-- | Very naive (and slow) implementation of Kostka numbers, for reference.
kostkaNumberReferenceNaive :: Partition -> Partition -> Int
kostkaNumberReferenceNaive plambda pmu@(Partition mu) = length stuff where
  stuff  = [ (1::Int) | t <- semiStandardYoungTableaux k plambda , cond t ]
  k      = length mu
  cond t = [ (head xs, length xs) | xs <- group (sort $ concat t) ] == zip [1..] mu 

--------------------------------------------------------------------------------

-- | Lists all (positive) Kostka numbers @K(lambda,mu)@ with the given @lambda@:
--
-- > kostkaNumbersWithGivenLambda lambda == Map.fromList [ (mu , kostkaNumber lambda mu) | mu <- dominatedPartitions lambda ]
--
-- It's much faster than computing the individual Kostka numbers, but not as fast
-- as it could be.
--
{-# SPECIALIZE kostkaNumbersWithGivenLambda :: Partition -> Map Partition Int     #-}
{-# SPECIALIZE kostkaNumbersWithGivenLambda :: Partition -> Map Partition Integer #-}
kostkaNumbersWithGivenLambda :: forall coeff. Num coeff => Partition -> Map Partition coeff
kostkaNumbersWithGivenLambda plambda@(Partition lam) = evalState (worker lam) Map.empty where

  worker :: [Int] -> State (Map Partition (Map Partition coeff)) (Map Partition coeff)
  worker unlam = case unlam of
    [] -> return $ Map.singleton (Partition []) 1
    _  -> do
      cache <- get
      case Map.lookup (Partition unlam) cache of
        Just sol -> return sol
        Nothing  -> do
          let s = foldl' (+) 0 unlam
          subsols <- forM (prevLambdas0 unlam) $ \p -> do
            sub <- worker p 
            let t = s - foldl' (+) 0 p              
                f (Partition xs , c) = case xs of
                  (y:_) -> if t >= y then Just (Partition (t:xs) , c) else Nothing
                  []    -> if t >  0 then Just (Partition [t]    , c) else Nothing
            if t > 0
              then return $ Map.fromList $ mapMaybe f $ Map.toList sub
              else return $ Map.empty

          let sol = Map.unionsWith (+) subsols
          put $! (Map.insert (Partition unlam) sol cache)
          return sol

  -- needs decreasing sequence
  prevLambdas0 :: [Int] -> [[Int]]
  prevLambdas0 (l:ls) = go l ls where
    go b [a]    = [ [x]   | x <- [a..b] ] ++ [ [x,y] | x <- [a..b] , y<-[1..a] ]
    go b (a:as) = [ x:xs  | x <- [a..b] , xs <- go a as ]
    go b []     = [] : [ [j] | j <- [1..b] ]
  prevLambdas0 []  = []

-- | Lists all (positive) Kostka numbers @K(lambda,mu)@ with the given @mu@:
--
-- > kostkaNumbersWithGivenMu mu == Map.fromList [ (lambda , kostkaNumber lambda mu) | lambda <- dominatingPartitions mu ]
--
-- This function uses the iterated Pieri rule, and is relatively fast.
--
kostkaNumbersWithGivenMu :: Partition -> Map Partition Int
kostkaNumbersWithGivenMu (Partition mu) = iteratedPieriRule (reverse mu)

--------------------------------------------------------------------------------
-- * Gelfand-Tsetlin patterns

-- | A Gelfand-Tstetlin tableau
type GT = [[Int]]

asciiGT :: GT -> ASCII
asciiGT gt = tabulate (HRight,VTop) (HSepSpaces 1, VSepEmpty) 
           $ (map . map) asciiShow
           $ gt

kostkaGelfandTsetlinPatterns :: Partition -> Partition -> [GT]
kostkaGelfandTsetlinPatterns lambda (Partition mu) = kostkaGelfandTsetlinPatterns' lambda mu

-- | Generates all Kostka-Gelfand-Tsetlin tableau, that is, triangular arrays like
--
-- > [ 3 ]
-- > [ 3 , 2 ]
-- > [ 3 , 1 , 0 ]
-- > [ 2 , 0 , 0 , 0 ]
--
-- with both rows and column non-increasing such that
-- the top diagonal read lambda (in this case @lambda=[3,2]@) and the diagonal sums
-- are partial sums of mu (in this case @mu=[2,1,1,1]@)
--
-- The number of such GT tableaux is the Kostka
-- number K(lambda,mu).
--
kostkaGelfandTsetlinPatterns' :: Partition -> [Int] -> [GT]
kostkaGelfandTsetlinPatterns' plam@(Partition lambda0) mu0
  | minimum mu0 < 0                       = []
  | wlam == 0                             = if wmu == 0 then [ [] ] else []
  | wmu  == wlam && plam `dominates` pmu  = list
  | otherwise                             = []
  where

    pmu = mkPartition mu0

    nlam = length lambda0
    nmu  = length mu0

    n = max nlam nmu

    lambda = lambda0 ++ replicate (n - nlam) 0
    mu     = mu0     ++ replicate (n - nmu ) 0

    revlam = reverse lambda

    wmu  = sum' mu
    wlam = sum' lambda

    list = worker 
             revlam 
             (scanl1 (+) mu) 
             (replicate (n-1) 0) 
             (replicate (n  ) 0) 
             []

    worker
      :: [Int]       -- lambda_i in reverse order
      -> [Int]       -- partial sums of mu
      -> [Int]       -- sums of the tails of previous rows
      -> [Int]       -- last row
      -> [[Int]]     -- the lower part of GT tableau we accumulated so far (this is not needed if we only want to count)
      -> [GT]   

    worker (rl:rls) (smu:smus) (a:acc) (lastx0:lastrowt) table = stuff 
      where
        x0 = smu - a
        stuff = concat 
          [ worker rls smus (zipWith (+) acc (tail row)) (init row) (row:table)
          | row <- boundedNonIncrSeqs' x0 (map (max rl) (max lastx0 x0 : lastrowt)) lambda
          ]
    worker [rl] _ _ _ table = [ [rl]:table ] 
    worker []   _ _ _ _     = [ []         ]

    boundedNonIncrSeqs' :: Int -> [Int] -> [Int] -> [[Int]]
    boundedNonIncrSeqs' = go where
      go h0 (a:as) (b:bs) = [ h:hs | h <- [(max 0 a)..(min h0 b)] , hs <- go h as bs ]
      go _  []     _      = [[]]
      go _  _      []     = [[]]

--------------------------------------------------------------------------------

-- | This returns the corresponding Kostka number:
--
-- > countKostkaGelfandTsetlinPatterns lambda mu == length (kostkaGelfandTsetlinPatterns lambda mu)
-- 
countKostkaGelfandTsetlinPatterns :: Partition -> Partition -> Int
countKostkaGelfandTsetlinPatterns plam@(Partition lambda0) pmu@(Partition mu0) 
  | wlam == 0                             = if wmu == 0 then 1 else 0
  | wmu  == wlam && plam `dominates` pmu  = cnt
  | otherwise                             = 0
  where

    nlam = length lambda0
    nmu  = length mu0

    n = max nlam nmu

    lambda = lambda0 ++ replicate (n - nlam) 0
    mu     = mu0     ++ replicate (n - nmu ) 0

    revlam = reverse lambda

    wmu  = sum' mu
    wlam = sum' lambda

    cnt = worker 
            revlam 
            (scanl1 (+) mu) 
            (replicate (n-1) 0) 
            (replicate (n  ) 0) 

    worker
      :: [Int]       -- lambda_i in reverse order
      -> [Int]       -- partial sums of mu
      -> [Int]       -- sums of the tails of previous rows
      -> [Int]       -- last row
      -> Int

    worker (rl:rls) (smu:smus) (a:acc) (lastx0:lastrowt) = stuff 
      where
        x0 = smu - a
        stuff = sum'
          [ worker rls smus (zipWith (+) acc (tail row)) (init row) 
          | row <- boundedNonIncrSeqs' x0 (map (max rl) (max lastx0 x0 : lastrowt)) lambda
          ]
    worker [rl] _ _ _ = 1 
    worker []   _ _ _ = 1

    boundedNonIncrSeqs' :: Int -> [Int] -> [Int] -> [[Int]]
    boundedNonIncrSeqs' = go where
      go h0 (a:as) (b:bs) = [ h:hs | h <- [(max 0 a)..(min h0 b)] , hs <- go h as bs ]
      go _  []     _      = [[]]
      go _  _      []     = [[]]

--------------------------------------------------------------------------------

{-

-- | All non-increasing sentences between a lower and an upper bound
boundedNonIncrSeqs :: [Int] -> [Int] -> [[Int]]
boundedNonIncrSeqs as bs = case bs of  
  (h0:_) -> boundedNonIncrSeqs' h0 as bs
  []     -> [[]]

-- | All non-increasing sentences between a lower and an upper bound, and also less-or-equal than the given number
boundedNonIncrSeqs' :: Int -> [Int] -> [Int] -> [[Int]]
boundedNonIncrSeqs' = go where
  go h0 (a:as) (b:bs) = [ h:hs | h <- [(max 0 a)..(min h0 b)] , hs <- go h as bs ]
  go _  []     _      = [[]]
  go _  _      []     = [[]]

-- | All non-decreasing sentences between a lower and an upper bound
boundedNonDecrSeqs :: [Int] -> [Int] -> [[Int]]
boundedNonDecrSeqs = boundedNonDecrSeqs' 0

-- | All non-decreasing sentences between a lower and an upper bound, and also greator-or-equal then the given number
boundedNonDecrSeqs' :: Int -> [Int] -> [Int] -> [[Int]]
boundedNonDecrSeqs' h0 = go (max 0 h0) where
  go h0 (a:as) (b:bs) = [ h:hs | h <- [(max h0 a)..b] , hs <- go h as bs ]
  go _  []     _      = [[]]
  go _  _      []     = [[]]

-}

--------------------------------------------------------------------------------
-- * The iterated Pieri rule 

-- | Computes the Schur expansion of @h[n1]*h[n2]*h[n3]*...*h[nk]@ via iterating the Pieri rule.
-- Note: the coefficients are actually the Kostka numbers; the following is true:
--
-- > Map.toList (iteratedPieriRule (fromPartition mu))  ==  [ (lam, kostkaNumber lam mu) | lam <- dominatingPartitions mu ]
-- 
-- This should be faster than individually computing all these Kostka numbers.
--
iteratedPieriRule :: Num coeff => [Int] -> Map Partition coeff
iteratedPieriRule = iteratedPieriRule' (Partition [])

-- | Iterating the Pieri rule, we can compute the Schur expansion of
-- @h[lambda]*h[n1]*h[n2]*h[n3]*...*h[nk]@
iteratedPieriRule' :: Num coeff => Partition -> [Int] -> Map Partition coeff
iteratedPieriRule' plambda ns = iteratedPieriRule'' (plambda,1) ns

{-# SPECIALIZE iteratedPieriRule'' :: (Partition,Int    ) -> [Int] -> Map Partition Int     #-}
{-# SPECIALIZE iteratedPieriRule'' :: (Partition,Integer) -> [Int] -> Map Partition Integer #-}
iteratedPieriRule'' :: Num coeff => (Partition,coeff) -> [Int] -> Map Partition coeff
iteratedPieriRule'' (plambda,coeff0) ns = worker (Map.singleton plambda coeff0) ns where
  worker old []     = old
  worker old (n:ns) = worker new ns where
    stuff = [ (coeff, pieriRule lam n) | (lam,coeff) <- Map.toList old ] 
    new   = foldl' f Map.empty stuff 
    f t0 (c,ps) = foldl' (\t p -> Map.insertWith (+) p c t) t0 ps  

--------------------------------------------------------------------------------

-- | Computes the Schur expansion of @e[n1]*e[n2]*e[n3]*...*e[nk]@ via iterating the Pieri rule.
-- Note: the coefficients are actually the Kostka numbers; the following is true:
--
-- > Map.toList (iteratedDualPieriRule (fromPartition mu))  ==  
-- >   [ (dualPartition lam, kostkaNumber lam mu) | lam <- dominatingPartitions mu ]
-- 
-- This should be faster than individually computing all these Kostka numbers.
-- It is a tiny bit slower than 'iteratedPieriRule'.
--
iteratedDualPieriRule :: Num coeff => [Int] -> Map Partition coeff
iteratedDualPieriRule = iteratedDualPieriRule' (Partition [])

-- | Iterating the Pieri rule, we can compute the Schur expansion of
-- @e[lambda]*e[n1]*e[n2]*e[n3]*...*e[nk]@
iteratedDualPieriRule' :: Num coeff => Partition -> [Int] -> Map Partition coeff
iteratedDualPieriRule' plambda ns = iteratedDualPieriRule'' (plambda,1) ns

{-# SPECIALIZE iteratedDualPieriRule'' :: (Partition,Int    ) -> [Int] -> Map Partition Int     #-}
{-# SPECIALIZE iteratedDualPieriRule'' :: (Partition,Integer) -> [Int] -> Map Partition Integer #-}
iteratedDualPieriRule'' :: Num coeff => (Partition,coeff) -> [Int] -> Map Partition coeff
iteratedDualPieriRule'' (plambda,coeff0) ns = worker (Map.singleton plambda coeff0) ns where
  worker old []     = old
  worker old (n:ns) = worker new ns where
    stuff = [ (coeff, dualPieriRule lam n) | (lam,coeff) <- Map.toList old ] 
    new   = foldl' f Map.empty stuff 
    f t0 (c,ps) = foldl' (\t p -> Map.insertWith (+) p c t) t0 ps  

--------------------------------------------------------------------------------
