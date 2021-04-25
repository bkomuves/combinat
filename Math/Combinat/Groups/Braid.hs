
-- | Braids. See eg. <https://en.wikipedia.org/wiki/Braid_group>
--
--
-- Based on: 
--
--  * Joan S. Birman, Tara E. Brendle: BRAIDS - A SURVEY
--    <https://www.math.columbia.edu/~jb/Handbook-21.pdf>
--
--
-- Note: This module GHC 7.8, since we use type-level naturals
-- to parametrize the 'Braid' type.
--


{-# LANGUAGE 
      CPP, BangPatterns, 
      ScopedTypeVariables, ExistentialQuantification,
      DataKinds, KindSignatures, Rank2Types,
      TypeOperators, TypeFamilies,
      StandaloneDeriving #-}

module Math.Combinat.Groups.Braid where

--------------------------------------------------------------------------------

import Data.Proxy
import GHC.TypeLits

import Control.Monad

import Data.List ( mapAccumL , foldl' )

import Data.Array.Unboxed
import Data.Array.ST
import Data.Array.IArray
import Data.Array.MArray
import Data.Array.Unsafe
import Data.Array.Base

import Control.Monad.ST

import System.Random

import Math.Combinat.ASCII
import Math.Combinat.Sign
import Math.Combinat.Helper
import Math.Combinat.TypeLevel
import Math.Combinat.Numbers.Series

import Math.Combinat.Permutations ( Permutation(..) , (!!!) )
import qualified Math.Combinat.Permutations as P

--------------------------------------------------------------------------------
-- * Artin generators

-- | A standard Artin generator of a braid: @Sigma i@ represents twisting 
-- the neighbour strands @i@ and @(i+1)@, such that strand @i@ goes /under/ strand @(i+1)@.
--
-- Note: The strands are numbered @1..n@.
data BrGen
  = Sigma    !Int         -- ^ @i@ goes under @(i+1)@
  | SigmaInv !Int         -- ^ @i@ goes above @(i+1)@
  deriving (Eq,Ord,Show)
 
-- | The strand (more precisely, the first of the two strands) the generator twistes
brGenIdx :: BrGen -> Int
brGenIdx g = case g of
  Sigma    i -> i
  SigmaInv i -> i

brGenSign :: BrGen -> Sign
brGenSign g = case g of
  Sigma    _ -> Plus
  SigmaInv _ -> Minus

brGenSignIdx :: BrGen -> (Sign,Int)        
brGenSignIdx g = case g of
  Sigma    i -> (Plus ,i)
  SigmaInv i -> (Minus,i) 

-- | The inverse of a braid generator
invBrGen :: BrGen -> BrGen
invBrGen  g = case g of
  Sigma    i -> SigmaInv i
  SigmaInv i -> Sigma    i

--------------------------------------------------------------------------------
-- * The braid type
  
-- | The braid group @B_n@ on @n@ strands.
-- The number @n@ is encoded as a type level natural in the type parameter.
--
-- Braids are represented as words in the standard generators and their
-- inverses.
newtype Braid (n :: Nat) = Braid [BrGen] deriving (Show)

-- | The number of strands in the braid
numberOfStrands :: KnownNat n => Braid n -> Int
numberOfStrands = fromInteger . natVal . braidProxy where                                                         
  braidProxy :: Braid n -> Proxy n
  braidProxy _ = Proxy

-- | Sometimes we want to hide the type-level parameter @n@, for example when
-- dynamically creating braids whose size is known only at runtime.
data SomeBraid = forall n. KnownNat n => SomeBraid (Braid n)

someBraid :: Int -> (forall (n :: Nat). KnownNat n => Braid n) -> SomeBraid
someBraid n polyBraid = 
  case snat of    
    SomeNat pxy -> SomeBraid (asProxyTypeOf1 polyBraid pxy)
  where
    snat = case someNatVal (fromIntegral n :: Integer) of
      Just sn -> sn
      Nothing -> error "someBraid: input is not a natural number"

withSomeBraid :: SomeBraid -> (forall n. KnownNat n => Braid n -> a) -> a
withSomeBraid sbraid f = case sbraid of SomeBraid braid -> f braid

mkBraid :: (forall n. KnownNat n => Braid n -> a) -> Int -> [BrGen] -> a
mkBraid f n w = y where
  sb = someBraid n (Braid w)
  y  = withSomeBraid sb f

withBraid 
  :: Int
  -> (forall (n :: Nat). KnownNat n => Braid n)
  -> (forall (n :: Nat). KnownNat n => Braid n -> a) 
  -> a
withBraid n polyBraid f = 
  case snat of    
    SomeNat pxy -> f (asProxyTypeOf1 polyBraid pxy)
  where
    snat = case someNatVal (fromIntegral n :: Integer) of
      Just sn -> sn
      Nothing -> error "withBraid: input is not a natural number"

--------------------------------------------------------------------------------

braidWord :: Braid n -> [BrGen]
braidWord (Braid gs) = gs

braidWordLength :: Braid n -> Int
braidWordLength (Braid gs) = length gs

-- | Embeds a smaller braid group into a bigger braid group    
extend :: (n1 <= n2) => Braid n1 -> Braid n2
extend (Braid gs) = Braid gs

-- | Apply \"free reduction\" to the word, that is, iteratively remove @sigma_i sigma_i^-1@ pairs.
-- The resulting braid is clearly equivalent to the original.
freeReduceBraidWord :: Braid n -> Braid n
freeReduceBraidWord (Braid orig) = Braid (loop orig) where

  loop w = case reduceStep w of
    Nothing -> w
    Just w' -> loop w'
  
  reduceStep :: [BrGen] -> Maybe [BrGen]
  reduceStep = go False where    
    go !changed w = case w of
      (Sigma    x : SigmaInv y : rest) | x==y   -> go True rest
      (SigmaInv x : Sigma    y : rest) | x==y   -> go True rest
      (this : rest)                             -> liftM (this:) $ go changed rest
      _                                         -> if changed then Just w else Nothing

--------------------------------------------------------------------------------
-- * Some specific braids

-- | The braid generator @sigma_i@ as a braid
sigma :: KnownNat n => Int -> Braid (n :: Nat)
sigma k = braid where
  braid = if k > 0 && k < numberOfStrands braid
    then Braid [Sigma k]
    else error "sigma: braid generator index out of range"

-- | The braid generator @sigma_i^(-1)@ as a braid
sigmaInv :: KnownNat n => Int -> Braid (n :: Nat)
sigmaInv k = braid where
  braid = if k > 0 && k < numberOfStrands braid
    then Braid [SigmaInv k]
    else error "sigma: braid generator index out of range"

-- | @doubleSigma s t@ (for s<t)is the generator @sigma_{s,t}@ in Birman-Ko-Lee's
-- \"new presentation\". It twistes the strands @s@ and @t@ while going over all
-- other strands. For @t==s+1@ we get back @sigma s@
-- 
doubleSigma :: KnownNat n => Int -> Int -> Braid (n :: Nat)
doubleSigma s t = braid where
  n = numberOfStrands braid
  braid
    | s < 1 || s > n   = error "doubleSigma: s index out of range"
    | t < 1 || t > n   = error "doubleSigma: t index out of range"
    | s >= t           = error "doubleSigma: s >= t"
    | otherwise        = Braid $
       [ Sigma i | i<-[t-1,t-2..s] ] ++ [ SigmaInv i | i<-[s+1..t-1] ]

-- | @positiveWord [2,5,1]@ is shorthand for the word @sigma_2*sigma_5*sigma_1@.
positiveWord :: KnownNat n => [Int] -> Braid (n :: Nat)
positiveWord idxs = braid where
  braid = Braid (map gen idxs) 
  n     = numberOfStrands braid
  gen i = if i>0 && i<n then Sigma i else error "positiveWord: index out of range"
       
-- | The (positive) half-twist of all the braid strands, usually denoted by @Delta@.
halfTwist :: KnownNat n => Braid n
halfTwist = braid where
  braid = Braid $ map Sigma $ _halfTwist n 
  n     = numberOfStrands braid

-- | The untyped version of 'halfTwist'
_halfTwist :: Int -> [Int]
_halfTwist n = gens where
  gens  = concat [ sub k | k<-[1..n-1] ]
  sub k = [ j | j<-[n-1,n-2..k] ]
  
-- | Synonym for 'halfTwist'
theGarsideBraid :: KnownNat n => Braid n
theGarsideBraid = halfTwist 

-- | The inner automorphism defined by @tau(X) = Delta^-1 X Delta@, 
-- where @Delta@ is the positive half-twist.
-- 
-- This sends each generator @sigma_j@ to @sigma_(n-j)@.
--
tau :: KnownNat n => Braid n -> Braid n
tau braid@(Braid gens) = Braid (map f gens) where
  n = numberOfStrands braid
  f (Sigma    i) = Sigma    (n-i)
  f (SigmaInv i) = SigmaInv (n-i)


-- | The involution @tau@ on permutations (permutation braids)
--
tauPerm :: Permutation -> Permutation
tauPerm perm = P.toPermutationUnsafeN n [ (n+1) - perm !!! (n-i) | i<-[0..n-1] ] where
  n = P.permutationSize perm

--------------------------------------------------------------------------------
-- * Group operations

-- | The trivial braid
identity :: Braid n
identity = Braid []

-- | The inverse of a braid. Note: we do not perform reduction here,
-- as a word is reduced if and only if its inverse is reduced.
inverse :: Braid n -> Braid n
inverse = Braid . reverse . map invBrGen . braidWord

-- | Composes two braids, doing free reduction on the result 
-- (that is, removing @(sigma_k * sigma_k^-1)@ pairs@)
compose :: Braid n -> Braid n -> Braid n
compose (Braid gs) (Braid hs) = freeReduceBraidWord $ Braid (gs++hs)

composeMany :: [Braid n] -> Braid n
composeMany = freeReduceBraidWord . Braid . concat . map braidWord 

-- | Composes two braids without doing any reduction.
composeDontReduce :: Braid n -> Braid n -> Braid n
composeDontReduce (Braid gs) (Braid hs) = Braid (gs++hs)

--------------------------------------------------------------------------------
-- * Braid permutations

-- | A braid is pure if its permutation is trivial
isPureBraid :: KnownNat n => Braid n -> Bool
isPureBraid braid = (braidPermutation braid == P.identityPermutation n) where
  n = numberOfStrands braid

-- | Returns the left-to-right permutation associated to the braid. 
-- We follow the strands /from the left to the right/ (or from the top to the 
-- bottom), and return the permutation taking the left side to the right side.
--
-- This is compatible with /right/ (standard) action of the permutations:
-- @permuteRight (braidPermutationRight b1)@ corresponds to the left-to-right
-- permutation of the strands; also:
--
-- > (braidPermutation b1) `multiply` (braidPermutation b2) == braidPermutation (b1 `compose` b2)
--
-- Writing the right numbering of the strands below the left numbering,
-- we got the two-line notation of the permutation.
--
braidPermutation :: KnownNat n => Braid n -> Permutation
braidPermutation braid@(Braid gens) = perm where
  n    = numberOfStrands braid
  perm = _braidPermutation n (map brGenIdx gens)

-- | This is an untyped version of 'braidPermutation'
_braidPermutation :: Int -> [Int] -> Permutation
_braidPermutation n idxs = P.uarrayToPermutationUnsafe (runSTUArray action) where

  action :: forall s. ST s (STUArray s Int Int) 
  action = do 
    arr <- newArray_ (1,n) 
    forM_ [1..n] $ \i -> writeArray arr i i
    worker arr idxs
    return arr
    
  worker arr = go where
    go []     = return arr 
    go (i:is) = do
      a <- readArray arr  i
      b <- readArray arr (i+1)
      writeArray arr  i    b
      writeArray arr (i+1) a
      go is

--------------------------------------------------------------------------------
-- * Permutation braids

-- | A positive braid word contains only positive (@Sigma@) generators.
isPositiveBraidWord :: KnownNat n => Braid n -> Bool
isPositiveBraidWord (Braid gs) = all (isPlus . brGenSign) gs 

-- | A /permutation braid/ is a positive braid where any two strands cross
-- at most one, and /positively/. 
--
isPermutationBraid :: KnownNat n => Braid n -> Bool
isPermutationBraid braid = isPositiveBraidWord braid && crosses where
  crosses     = and [ check i j | i<-[1..n-1], j<-[i+1..n] ] 
  check i j   = zeroOrOne (lkMatrix ! (i,j)) 
  zeroOrOne a = (a==1 || a==0)
  lkMatrix    = linkingMatrix   braid
  n           = numberOfStrands braid

-- | Untyped version of 'isPermutationBraid' for positive words.
_isPermutationBraid :: Int -> [Int] -> Bool
_isPermutationBraid n gens = crosses where
  crosses     = and [ check i j | i<-[1..n-1], j<-[i+1..n] ] 
  check i j   = zeroOrOne (lkMatrix ! (i,j)) 
  zeroOrOne a = (a==1 || a==0)
  lkMatrix    = _linkingMatrix n $ map Sigma gens

-- | For any permutation this functions returns a /permutation braid/ realizing
-- that permutation. Note that this is not unique, so we make an arbitrary choice
-- (except for the permutation @[n,n-1..1]@ reversing the order, in which case 
-- the result must be the half-twist braid).
-- 
-- The resulting braid word will have a length at most @choose n 2@ (and will have
-- that length only for the permutation @[n,n-1..1]@)
--
-- > braidPermutationRight (permutationBraid perm) == perm
-- > isPermutationBraid    (permutationBraid perm) == True
--
permutationBraid :: KnownNat n => Permutation -> Braid n
permutationBraid perm = braid where
  n1 = numberOfStrands braid
  n2 = P.permutationSize perm
  braid = if n1 == n2
    then Braid (map Sigma $ _permutationBraid perm)
    else error $ "permutationBraid: incompatible n: " ++ show n1 ++ " vs. " ++ show n2

-- | Untyped version of 'permutationBraid'
_permutationBraid :: Permutation -> [Int]
_permutationBraid = concat . _permutationBraid'

-- | Returns the individual \"phases\" of the a permutation braid realizing the
-- given permutation.
_permutationBraid' :: Permutation -> [[Int]]
_permutationBraid' perm = runST action where
  n = P.permutationSize perm

  action :: forall s. ST s [[Int]]
  action = do

    -- cfwd = the current state of strands    : cfwd!j = where is strand #j now?
    -- cinv = the inverse of that permutation : cinv!i = which strand is on the #i position now?

    cfwd <- newArray_ (1,n) :: ST s (STUArray s Int Int)
    cinv <- newArray_ (1,n) :: ST s (STUArray s Int Int)
    forM_ [1..n] $ \j -> do
      writeArray cfwd j j
      writeArray cinv j j

    let doSwap i = do     
          a <- readArray cinv  i
          b <- readArray cinv (i+1)
          writeArray cinv  i    b
          writeArray cinv (i+1) a

          u <- readArray cfwd a
          v <- readArray cfwd b
          writeArray cfwd a v
          writeArray cfwd b u

    -- at the k-th phase, we move the (inv!k)-th strand, which is the k-th strand /on the RHS/, to correct position.
    let worker phase
          | phase >= n  = return []
          | otherwise   = do
              let tgt = P.lookupPermutation perm phase  -- (arr ! phase)
              src <- readArray cfwd tgt
              let this = [src-1,src-2..phase]
              mapM_ doSwap $ this 
              rest <- worker (phase+1)
              return (this:rest)

    worker 1
 

-- | We compute the linking numbers between all pairs of strands:
--
-- > linkingMatrix braid ! (i,j) == strandLinking braid i j 
--
linkingMatrix :: KnownNat n => Braid n -> UArray (Int,Int) Int
linkingMatrix braid@(Braid gens) = _linkingMatrix (numberOfStrands braid) gens where

-- | Untyped version of 'linkingMatrix'
_linkingMatrix :: Int -> [BrGen] -> UArray (Int,Int) Int
_linkingMatrix n gens = runSTUArray action where

  action :: forall s. ST s (STUArray s (Int,Int) Int)
  action = do
    perm <- newArray_ (1,n) :: ST s (STUArray s Int Int)
    forM_ [1..n] $ \i -> writeArray perm i i
    let doSwap :: Int -> ST s ()
        doSwap i = do
          a <- readArray perm  i
          b <- readArray perm (i+1)
          writeArray perm  i    b
          writeArray perm (i+1) a
               
    mat <- newArray ((1,1),(n,n)) 0 :: ST s (STUArray s (Int,Int) Int)
    let doAdd :: Int -> Int -> Int -> ST s ()
        doAdd i j pm1 = do
          x <- readArray mat (i,j)
          writeArray mat (i,j) (x+pm1) 
          writeArray mat (j,i) (x+pm1)
       
    forM_ gens $ \g -> do
      let (sgn,k) = brGenSignIdx g
      u <- readArray perm  k 
      v <- readArray perm (k+1)
      doAdd u v (signValue sgn)
      doSwap k 
        
    return mat
    
    
-- | The linking number between two strands numbered @i@ and @j@ 
-- (numbered such on the /left/ side).
strandLinking :: KnownNat n => Braid n -> Int -> Int -> Int
strandLinking braid@(Braid gens) i0 j0 
  | i0 < 1 || i0 > n  = error $ "strandLinkingNumber: invalid strand index i: " ++ show i0
  | j0 < 1 || j0 > n  = error $ "strandLinkingNumber: invalid strand index j: " ++ show j0
  | i0 == j0          = 0
  | otherwise         = go i0 j0 gens
  where
    n = numberOfStrands braid
    
    go !i !j []     = 0
    go !i !j (g:gs)  
      | i == k   && j == k+1  = s + go (i+1) (j-1) gs
      | j == k   && i == k+1  = s + go (i-1) (j+1) gs
      | i == k                =     go (i+1)  j    gs
      |             i == k+1  =     go (i-1)  j    gs
      | j == k                =     go  i    (j+1) gs
      |             j == k+1  =     go  i    (j-1) gs
      | otherwise             =     go  i     j    gs
      where
        (sgn,k) = brGenSignIdx g
        s = signValue sgn

--------------------------------------------------------------------------------
-- * Growth 

-- | Bronfman's recursive formula for the reciprocial of the growth function 
-- of /positive/ braids. It was already known (by Deligne) that these generating functions 
-- are reciprocials of polynomials; Bronfman [1] gave a recursive formula for them.
--
-- > let count n l = length $ nub $ [ braidNormalForm w | w <- allPositiveBraidWords n l ]
-- > let convertPoly (1:cs) = zip (map negate cs) [1..]
-- > pseries' (convertPoly $ bronfmanH n) == expandBronfmanH n == [ count n l | l <- [0..] ] 
--
-- * [1] Aaron Bronfman: Growth functions of a class of monoids. Preprint, 2001
--
bronfmanH :: Int -> [Int]
bronfmanH n = bronfmanHsList !! n

-- | An infinite list containing the Bronfman polynomials:
--
-- > bronfmanH n = bronfmanHsList !! n
--
bronfmanHsList :: [[Int]]
bronfmanHsList = list where
  list = map go [0..]
  go 0 = [1]
  go n = sumSeries [ sgn i $ replicate (choose2 i) 0 ++ list !! (n-i) | i<-[1..n] ]
  sgn i = if odd i then id else map negate
  choose2 k = div (k*(k-1)) 2

-- | Expands the reciprocial of @H(n)@ into an infinite power series,
-- giving the growth function of the positive braids on @n@ strands.
expandBronfmanH :: Int -> [Int]
expandBronfmanH n = pseries' (convertPoly $ bronfmanH n) where
  convertPoly (1:cs) = zip (map negate cs) [1..]
   
--------------------------------------------------------------------------------
-- * ASCII diagram

instance KnownNat n => DrawASCII (Braid n) where
  ascii = horizBraidASCII

-- | Horizontal braid diagram, drawn from left to right,
-- with strands numbered from the bottom to the top
horizBraidASCII :: KnownNat n => Braid n -> ASCII
horizBraidASCII = horizBraidASCII' True

-- | Horizontal braid diagram, drawn from left to right.
-- The boolean flag indicates whether to flip the strands
-- vertically ('True' means bottom-to-top, 'False' means top-to-bottom) 
horizBraidASCII' :: KnownNat n => Bool -> Braid n -> ASCII
horizBraidASCII' flipped braid@(Braid gens) = final where

  n = numberOfStrands braid
 
  final        = vExtendWith VTop 1 $ hCatTop allBlocks
  allBlocks    = prelude ++ middleBlocks ++ epilogue
  prelude      = [ numberBlock   , spaceBlock , beginEndBlock ] 
  epilogue     = [ beginEndBlock , spaceBlock , numberBlock'  ]
  middleBlocks = map block gens 
  
  block g = case g of
    Sigma    i -> block' i $ if flipped then over  else under
    SigmaInv i -> block' i $ if flipped then under else over

  block' i middle = asciiFromLines $ drop 2 $ concat 
                  $ replicate a horiz ++ [space3, middle] ++ replicate b horiz
    where 
      (a,b) = if flipped then (n-i-1,i-1) else (i-1,n-i-1)

  -- cycleN :: Int -> [a] -> [a]
  -- cycleN n = concat . replicate n

  spaceBlock    = transparentBox (1,n*3-2)
  beginEndBlock = asciiFromLines $ drop 2 $ concat $ replicate n horiz
  numberBlock   = mkNumbers [1..n]
  numberBlock'  = mkNumbers $ P.fromPermutation $ braidPermutation braid

  mkNumbers :: [Int] -> ASCII
  mkNumbers list = vCatWith HRight (VSepSpaces 2) $ map asciiShow 
                 $ (if flipped then reverse else id) $ list

  under  = [ "\\ /" , " / "  , "/ \\" ]
  over   = [ "\\ /" , " \\ " , "/ \\" ]
  horiz  = [ "   "  , "   "  , "___"  ]
  space3 = [ "   "  , "   "  , "   "  ]

--------------------------------------------------------------------------------

{- this is unusably ugly and vertically loooong

-- | Vertical braid diagram, drawn from the top to the bottom.
-- Strands are numbered from the left to the right.
--
-- Writing down the strand numbers from the top and and the bottom
-- gives the two-line notation of the permutation realized by the braid.
--
verticalBraidASCII :: KnownNat n => Braid n -> ASCII
verticalBraidASCII braid@(Braid gens) = final where

  n = numberOfStrands braid
 
  final        = hExtendWith HLeft 1 $ vCatLeft allBlocks
  allBlocks    = prelude ++ middleBlocks ++ epilogue
  prelude      = [ numberBlock   , spaceBlock , beginEndBlock ] 
  epilogue     = [ beginEndBlock , spaceBlock , numberBlock'  ]
  middleBlocks = map block gens 
  
  block g = case g of
    Sigma    i -> block' i under
    SigmaInv i -> block' i over

  block' i middle = asciiFromLines (map f middle) where
    f xs = drop 1 $ concat $ h (i-1) ++ ["   ",xs] ++ h (n-i-1)
    h k  = replicate k "  |"

  spaceBlock    = transparentBox (n*3-2,1)
  beginEndBlock = asciiFromLines $ replicate 3 $ drop 1 $ concat (replicate n "  |")
  numberBlock   = mkNumbers [1..n]
  numberBlock'  = mkNumbers $ P.fromPermutation $ braidPermutation braid

  mkNumbers :: [Int] -> ASCII
  mkNumbers list = asciiFromString (drop 1 $ concatMap show3 list)
  show3 k = let s = show k 
            in  replicate (3-length s) ' ' ++ s

  under  = [ "\\ /" , " / "  , "/ \\" ]
  over   = [ "\\ /" , " \\ " , "/ \\" ]

-}

--------------------------------------------------------------------------------
-- * List of all words

-- | All positive braid words of the given length
allPositiveBraidWords :: KnownNat n => Int -> [Braid n]
allPositiveBraidWords l = braids where
  n = numberOfStrands (head braids)
  braids = map Braid $ _allPositiveBraidWords n l 

-- | All braid words of the given length
allBraidWords :: KnownNat n => Int -> [Braid n]
allBraidWords l = braids where
  n = numberOfStrands (head braids)
  braids = map Braid $ _allBraidWords n l 

-- | Untyped version of 'allPositiveBraidWords'
_allPositiveBraidWords :: Int -> Int -> [[BrGen]]
_allPositiveBraidWords n = go where
  go 0 = [[]]
  go k = [ Sigma i : rest | i<-[1..n-1] , rest <- go (k-1) ]

-- | Untyped version of 'allBraidWords'
_allBraidWords :: Int -> Int -> [[BrGen]]
_allBraidWords n = go where
  go 0 = [[]]
  go k = [ gen : rest | gen <- gens , rest <- go (k-1) ]
  gens = concat [ [ Sigma i , SigmaInv i ] | i<-[1..n-1] ]

--------------------------------------------------------------------------------
-- * Random braids  

-- | Random braid word of the given length
randomBraidWord :: (RandomGen g, KnownNat n) => Int -> g -> (Braid n, g)
randomBraidWord len g = (braid, g') where
  braid  = Braid w
  n      = numberOfStrands braid
  (w,g') = _randomBraidWord n len g

-- | Random /positive/ braid word of the given length
randomPositiveBraidWord :: (RandomGen g, KnownNat n) => Int -> g -> (Braid n, g)
randomPositiveBraidWord len g = (braid, g') where
  braid  = Braid w
  n      = numberOfStrands braid
  (w,g') = _randomPositiveBraidWord n len g

--------------------------------------------------------------------------------

-- | Given a braid word, we perturb it randomly @m@ times using the braid relations,
-- so that the resulting new braid word is equivalent to the original.
--
-- Useful for testing.
--
randomPerturbBraidWord :: forall n g. (RandomGen g, KnownNat n) => Int -> Braid n -> g -> (Braid n, g)
randomPerturbBraidWord m braid@(Braid xs) g = (Braid word' , g') where

  (word',g') = go m (length xs) xs g 

  n = numberOfStrands braid

  -- | A random pair cancelling each other
  rndE :: g -> ([BrGen],g)
  rndE g = (e1,g'') where
    (i , g'  ) = randomR (1,n-1) g 
    (b , g'' ) = random          g'
    e0 = [SigmaInv i, Sigma i] 
    e1 = if b then reverse e0 else e0

  brg    s i = case s of { Plus -> Sigma    i ; Minus -> SigmaInv i }
  brginv s i = case s of { Plus -> SigmaInv i ; Minus -> Sigma    i }

  go :: Int -> Int -> [BrGen] -> g -> ([BrGen], g)
  go !cnt !len !word !g 

    | cnt <= 0   = (word, g)

    | len <  2   = let w' = if b1 then (e++word) else (word++e)        -- if it is short, we just add a trivial pair somewhere
                   in  continue g4 (len+2) w'

    | abs (i-j) >= 2            = continue g4  len    (as ++ v:u:bs)         -- they commute, so we just commute them

    | i == j && s/=t            = continue g4 (len-2) (as ++ bs    )         -- they are inverse of each other, so we kill them

    | abs (i-j) == 1 && s == t  = let mid = if b1 
                                        then [ brg s j , brg s i , brg s j , brginv s i ]   -- insert pair and
                                        else [ brginv s j , brg s i , brg s j , brg s i ]   -- apply ternary relation 
                                  in  continue g4 (len+2) (as ++ mid ++ bs)

    | otherwise                 = let mid = if b1
                                        then (u : e ++ [v])
                                        else if b2
                                          then [u,v] ++ e
                                          else e ++ [u,v]
                                  in continue g4 (len+2) (as++(u:e)++[v]++bs)          -- otherwise we just insert an trivial pair         

    where

      (pos         , g1 ) = randomR (0,len-2) g
      (b1 :: Bool  , g2 ) = random g1
      (b2 :: Bool  , g3 ) = random g2
      (e           , g4 ) = rndE   g3
      (as,u:v:bs) = splitAt pos word
      (s,i) = brGenSignIdx u
      (t,j) = brGenSignIdx v
  
      continue g' len' word' = go (cnt-1) len' word' g'

--------------------------------------------------------------------------------

-- | This version of 'randomBraidWord' may be convenient to avoid the type level stuff
withRandomBraidWord 
  :: RandomGen g 
  => (forall n. KnownNat n => Braid n -> a) 
  -> Int                -- ^ number of strands
  -> Int                -- ^ length of the random word
  -> g -> (a, g)
withRandomBraidWord f n len = runRand $ do
  withSelectedM f (rand $ randomBraidWord len) n

-- | This version of 'randomPositiveBraidWord' may be convenient to avoid the type level stuff
withRandomPositiveBraidWord 
  :: RandomGen g 
  => (forall n. KnownNat n => Braid n -> a) 
  -> Int                -- ^ number of strands
  -> Int                -- ^ length of the random word
  -> g -> (a, g)
withRandomPositiveBraidWord f n len = runRand $ do
  withSelectedM f (rand $ randomPositiveBraidWord len) n

-- | Untyped version of 'randomBraidWord'
_randomBraidWord 
  :: (RandomGen g) 
  => Int                -- ^ number of strands
  -> Int                -- ^ length of the random word
  -> g -> ([BrGen], g)
_randomBraidWord n len = runRand $ replicateM len $ do
  k <- randChoose (1,n-1)
  s <- randRoll
  return $ case s of
    Plus  -> Sigma k
    Minus -> SigmaInv k

-- | Untyped version of 'randomPositiveBraidWord'
_randomPositiveBraidWord 
  :: (RandomGen g) 
  => Int             -- ^ number of strands
  -> Int             -- ^ length of the random word
  -> g -> ([BrGen], g)
_randomPositiveBraidWord n len = runRand $ replicateM len $ do
  liftM Sigma $ randChoose (1,n-1)

--------------------------------------------------------------------------------

