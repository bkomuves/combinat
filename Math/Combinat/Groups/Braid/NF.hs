
-- | Normal form of braids, take 1.
--
-- We implement the Adyan-Thurston-ElRifai-Morton solution to the word problem in braid groups.
--
--
-- Based on:
--
-- * [1] Joan S. Birman, Tara E. Brendle: BRAIDS - A SURVEY
--   <https://www.math.columbia.edu/~jb/Handbook-21.pdf> (chapter 5.1)
--
-- * [2] Elsayed A. Elrifai, Hugh R. Morton: Algorithms for positive braids
--

{-# LANGUAGE 
      CPP, BangPatterns, 
      ScopedTypeVariables, ExistentialQuantification,
      DataKinds, KindSignatures, Rank2Types #-}

module Math.Combinat.Groups.Braid.NF  
  ( -- * Normal form
    BraidNF (..)
  , nfReprWord
  , braidNormalForm
  , braidNormalForm'
  , braidNormalFormNaive'
    -- * Starting and finishing sets
  , permWordStartingSet
  , permWordFinishingSet    
  , permutationStartingSet
  , permutationFinishingSet    
  )
  where

--------------------------------------------------------------------------------

import Data.Proxy
import GHC.TypeLits

import Control.Monad

import Data.List ( mapAccumL , foldl' , (\\) )

import Data.Array.Unboxed
import Data.Array.ST
import Data.Array.IArray
import Data.Array.MArray
import Data.Array.Unsafe
import Data.Array.Base

import Control.Monad.ST

import Math.Combinat.Helper
import Math.Combinat.Sign

import Math.Combinat.Permutations ( Permutation(..) , (!!!) , isIdentityPermutation , isReversePermutation )
import qualified Math.Combinat.Permutations as P

import Math.Combinat.Groups.Braid

--------------------------------------------------------------------------------

-- | A unique normal form for braids, called the /left-greedy normal form/.
-- It looks like @Delta^i*P@, where @Delta@ is the positive half-twist, @i@ is an integer,
-- and @P@ is a positive word, which can be further decomposed into non-@Delta@ /permutation words/; 
-- these words themselves are not unique, but the permutations they realize /are/ unique.
--
-- This will solve the word problem relatively fast, 
-- though it is not the fastest known algorithm.
--
data BraidNF (n :: Nat) = BraidNF
  { _nfDeltaExp :: !Int              -- ^ the exponent of @Delta@
  , _nfPerms    :: [Permutation]     -- ^ the permutations
  }
  deriving (Eq,Ord,Show)

-- | A braid word representing the given normal form
nfReprWord :: KnownNat n => BraidNF n -> Braid n
nfReprWord (BraidNF k perms) = freeReduceBraidWord $ composeMany (deltas ++ rest) where

  deltas 
    | k > 0     = replicate   k           halfTwist
    | k < 0     = replicate (-k) (inverse halfTwist)
    | otherwise = []

  rest = map permutationBraid perms

--------------------------------------------------------------------------------

-- | Computes the normal form of a braid. We apply free reduction first, it should be faster that way.
braidNormalForm :: KnownNat n => Braid n -> BraidNF n
braidNormalForm = braidNormalForm' . freeReduceBraidWord

-- | This function does not apply free reduction before computing the normal form
braidNormalForm' :: KnownNat n => Braid n -> BraidNF n
braidNormalForm' braid@(Braid gens) = BraidNF (dexp+pexp) perms where
  n = numberOfStrands braid
  invless = replaceInverses n gens
  (dexp,posxword) = moveDeltasLeft n invless
  factors = leftGreedyFactors n $ expandPosXWord n posxword
  (pexp,perms) = normalizePermFactors n $ map (_braidPermutation n) factors

-- | This one uses the naive inverse replacement method. Probably somewhat slower than 'braidNormalForm''.
braidNormalFormNaive' :: KnownNat n => Braid n -> BraidNF n
braidNormalFormNaive' braid@(Braid gens) = BraidNF (dexp+pexp) perms where
  n = numberOfStrands braid
  invless = replaceInversesNaive gens
  (dexp,posxword) = moveDeltasLeft n invless
  factors = leftGreedyFactors n $ expandPosXWord n posxword
  (pexp,perms) = normalizePermFactors n $ map (_braidPermutation n) factors

--------------------------------------------------------------------------------

-- | Replaces groups of @sigma_i^-1@ generators by @(Delta^-1 * P)@, 
-- where @P@ is a positive word.
--
-- This should be more clever (resulting in shorter words) than the naive version below
--
replaceInverses :: Int -> [BrGen] -> [XGen]
replaceInverses n gens = worker gens where

  worker [] = []
  worker xs = replaceNegs neg ++ map (XSigma . brGenIdx) pos ++ worker rest where 
    (neg,tmp ) = span (isMinus . brGenSign) xs
    (pos,rest) = span (isPlus  . brGenSign) tmp
  
  replaceNegs gs = concatMap replaceFac facs where
    facs = leftGreedyFactors n $ map brGenIdx gs
  
  replaceFac idxs = XDelta (-1) : map XSigma (_permutationBraid perm) where
    perm = (P.reversePermutation n) `P.multiplyPermutation` (P.adjacentTranspositions n idxs)


-- | Replaces @sigma_i^-1@ generators by @(Delta^-1 * L_i)@.
replaceInversesNaive :: [BrGen] -> [XGen]
replaceInversesNaive gens = concatMap f gens where 
  f (Sigma    i) = [ XSigma i ]
  f (SigmaInv i) = [ XDelta (-1) , XL i ]

--------------------------------------------------------------------------------

-- | Temporary data structure to be used during the normal form computation
data XGen
  = XDelta !Int   -- ^ @Delta^k@
  | XSigma !Int   -- ^ @Sigma_j@
  | XL     !Int   -- ^ @L_j = Delta * sigma_j^-1@
  | XTauL  !Int   -- ^ @tau(L_j)@
  deriving (Eq,Show)

isXDelta :: XGen -> Bool
isXDelta x = case x of { XDelta {} -> True ; _ -> False }

-- | We move the all @Delta@'s to the left
moveDeltasLeft :: Int -> [XGen] -> (Int,[XGen])
moveDeltasLeft n input = (finalExp, finalPosWord) where
  
  (XDelta finalExp : finalPosWord) =  reverse $ worker 0 (reverse input) 

  -- we start from the right end, and work towards the left end
  worker  dexp [] = [ XDelta dexp ]
  worker !dexp xs = this' ++ worker dexp' rest where 
    (delta,notdelta) = span isXDelta xs
    (this ,rest    ) = span (not . isXDelta) notdelta
    dexp' = dexp + sumDeltas delta
    this' = if even dexp' 
      then this
      else map xtau this

  sumDeltas :: [XGen] -> Int
  sumDeltas xs = foldl' (+) 0 [ k | XDelta k <- xs ]

  -- | The @X -> Delta^-1 * X * Delta@ inner automorphism
  xtau :: XGen -> XGen
  xtau (XSigma j) = XSigma (n-j)
  xtau (XDelta k) = XDelta k  
  xtau (XL     k) = XTauL  k  
  xtau (XTauL  k) = XL     k  

--------------------------------------------------------------------------------

-- | Expands a /positive/ \"X-word\" into a positive braid word
expandPosXWord :: Int -> [XGen] -> [Int]
expandPosXWord n = concatMap f where

  posHalfTwist = _halfTwist n

  jtau :: Int -> Int
  jtau j = n-j

  posLTable    = listArray (1,n-1) [ _permutationBraid (posLPerm n i) | i<-[1..n-1] ] :: Array Int [Int]
  posTauLTable = amap (map jtau) posLTable

  -- posRTable = listArray (1,n-1) [ _permutationBraid (posRPerm n i) | i<-[1..n-1] ] :: Array Int [Int]

  f x = case x of
    XSigma i -> [i]
    XL     i -> posLTable    ! i
    XTauL  i -> posTauLTable ! i
    XDelta i 
      | i > 0     -> concat (replicate i posHalfTwist)
      | i < 0     -> error "expandPosXWord: negative delta power"
      | otherwise -> []

  -- word :: Braid n -> [Int]
  -- word (Braid gens) = map brGenIdx gens


-- | Expands an \"X-word\" into a braid word. Useful for debugging.
expandAnyXWord :: forall n. KnownNat n => [XGen] -> Braid n
expandAnyXWord xgens = braid where
  n = numberOfStrands braid

  braid = composeMany (map f xgens)

  posHalfTwist = halfTwist            :: Braid n
  negHalfTwist = inverse posHalfTwist :: Braid n

  posLTable    = listArray (1,n-1) [ permutationBraid (posLPerm n i) | i<-[1..n-1] ] :: Array Int (Braid n)
  posTauLTable = amap tau posLTable

  -- posRTable = listArray (1,n-1) [ permutationBraid (posRPerm n i) | i<-[1..n-1] ] :: Array Int (Braid n)

  f :: XGen -> Braid n
  f x = case x of
    XSigma i -> sigma i
    XL     i -> posLTable    ! i
    XTauL  i -> posTauLTable ! i
    XDelta i 
      | i > 0     -> composeMany (replicate   i  posHalfTwist)
      | i < 0     -> composeMany (replicate (-i) negHalfTwist)
      | otherwise -> identity

--------------------------------------------------------------------------------

-- | @posL k@ (denoted as @L_k@) is a /positive word/ which 
-- satisfies @Delta = L_k * sigma_k@, or:
-- 
-- > (inverse halfTwist) `compose` (posL k) ~=~ sigmaInv k@
-- 
-- Thus we can replace any word with a positive word plus some @Delta^-1@\'s
--
posL :: KnownNat n => Int -> Braid n
posL k = braid where
  n = numberOfStrands braid
  braid = permutationBraid (posLPerm n k)

-- | @posR k n@ (denoted as @R_k@) is a /permutation braid/ which 
-- satisfies @Delta = sigma_k * R_k@
-- 
-- > (posR k) `compose` (inverse halfTwist) ~=~ sigmaInv k@
-- 
-- Thus we can replace any word with a positive word plus some @Delta^-1@'s
--
posR :: KnownNat n => Int -> Braid n
posR k = braid where
  n = numberOfStrands braid
  braid = permutationBraid (posRPerm n k)

-- | The permutation @posL k :: Braid n@ is realizing
posLPerm :: Int -> Int -> Permutation
posLPerm n k 
  | k>0 && k<n  = (P.reversePermutation n `P.multiplyPermutation` P.adjacentTransposition n k)
  | otherwise   = error "posLPerm: index out of range"

-- | The permutation @posR k :: Braid n@ is realizing
posRPerm :: Int -> Int -> Permutation
posRPerm n k 
  | k>0 && k<n  = (P.adjacentTransposition n k `P.multiplyPermutation` P.reversePermutation n )
  | otherwise   = error "posRPerm: index out of range"

--------------------------------------------------------------------------------

-- | We recognize left-greedy factors which are @Delta@-s (easy, since they are the only ones
-- with length @(n choose 2)@), and move them to the left, returning their summed exponent
-- and the filtered new factors. We also filter trivial permutations (which should only happen 
-- for the trivial braid, but it happens there?)
--
filterDeltaFactors :: Int -> [[Int]] -> (Int, [[Int]])
filterDeltaFactors n facs = (exp',facs'') where

  (exp',facs') = go 0 (reverse facs)

  jtau j = n-j
  facs'' = reverse facs'
  maxlen = div (n*(n-1)) 2

  go !e []       = (e,[])
  go !e (xs:xxs)  
    | null xs             = go e xxs
    | length xs == maxlen = go (e+1) xxs
    | otherwise           =  
        if even e
          then let (e',yys) = go e xxs in (e' ,          xs : yys) 
          else let (e',yys) = go e xxs in (e' , map jtau xs : yys)  

-------------------------------------------------------------------------------- 

-- | The /starting set/ of a positive braid P is the subset of @[1..n-1]@ defined by
-- 
-- > S(P) = [ i | P = sigma_i * Q , Q is positive ] = [ i | (sigma_i^-1 * P) is positive ] 
--
-- This function returns the starting set a positive word, assuming it 
-- is a /permutation braid/ (see Lemma 2.4 in [2])
--
permWordStartingSet :: Int -> [Int] -> [Int]
permWordStartingSet n xs = permWordFinishingSet n (reverse xs)

-- | The /finishing set/ of a positive braid P is the subset of @[1..n-1]@ defined by
-- 
-- > F(P) = [ i | P = Q * sigma_i , Q is positive ] = [ i | (P * sigma_i^-1) is positive ] 
--
-- This function returns the finishing set, assuming the input is a /permutation braid/
--
permWordFinishingSet :: Int -> [Int] -> [Int]
permWordFinishingSet n input = runST action where

  action :: forall s. ST s [Int]
  action = do
    perm <- newArray_ (1,n) :: ST s (STUArray s Int Int)
    forM_ [1..n] $ \i -> writeArray perm i i
    forM_ input $ \i -> do
      a <- readArray perm  i
      b <- readArray perm (i+1)
      writeArray perm  i    b
      writeArray perm (i+1) a
    flip filterM [1..n-1] $ \i -> do
      a <- readArray perm  i
      b <- readArray perm (i+1) 
      return (b<a)                    -- Lemma 2.4 in [2]

-- | This satisfies
-- 
-- > permutationStartingSet p == permWordStartingSet n (_permutationBraid p)
--
permutationStartingSet :: Permutation -> [Int]
permutationStartingSet = permutationFinishingSet . P.inversePermutation

-- | This satisfies
-- 
-- > permutationFinishingSet p == permWordFinishingSet n (_permutationBraid p)
--
permutationFinishingSet :: Permutation -> [Int]
permutationFinishingSet perm
  = [ i | i<-[1..n-1] , perm !!! i > perm !!! (i+1) ] where n = P.permutationSize perm

-- | Returns the list of permutations failing Lemma 2.5 in [2] 
-- (so an empty list means the implementaton is correct)
fails_lemmma_2_5 :: Int -> [Permutation]
fails_lemmma_2_5 n = [ p | p <- P.permutations n , not (test p) ] where
  test p = and [ check i | i<-[1..n-1] ] where
    w = _permutationBraid p
    s = permWordStartingSet n w
    check i = _isPermutationBraid n (i:w) == (not $ elem i s)

-------------------------------------------------------------------------------- 
                    
-- | Given factors defined as permutation braids, we normalize them
-- to /left-canonical form/ by ensuring that
--
-- * for each consecutive pair @(P,Q)@ the finishing set F(P) contains the starting set S(Q)
--
-- * all @Delta@-s (corresponding to the reverse permutation) are moved to the left
--
-- * all trivial factors are filtered out
--
-- Unfortunately, it seems that we may need multiple sweeps to do that...
--
normalizePermFactors :: Int -> [Permutation] -> (Int,[Permutation])
normalizePermFactors n = go 0 where
  go !acc input = 
    if (exp==0 && input == output) 
      then (acc,input) 
      else go (acc+exp) output 
    where 
      (exp,output) = normalizePermFactors1 n input

-- | Does 1 sweep of the above normalization process.
-- Unfortunately, it seems that we may need to do this multiple times...
--
normalizePermFactors1 :: Int -> [Permutation] -> (Int,[Permutation])
normalizePermFactors1 n input = (exp, reverse output) where
  (exp, output) = worker 0 (reverse input)

  -- Notes: We work in reverse order, from the right to the left.
  -- We maintain the number of Delta-s pushed through; the tau involutions
  -- are implicit in the parity of this number
  --
  worker :: Int -> [Permutation] -> (Int,[Permutation])
  worker = worker' 0 0
  
  -- We also maintain additional 0/1 flip flags for the first two permutations
  -- this is a little bit of hack but it should work nicely
  --
  worker' :: Int -> Int -> Int -> [Permutation] -> (Int,[Permutation])
  worker' !ep !eq !e (!p : rest@(!q : rest')) 

    -- check if the very first element is identity or Delta 
    -- (note: these are tau-invariants)

    | isIdentityPermutation p  = worker'  eq  0  e    rest
    | isReversePermutation  p  = worker'  eq  0 (e+1) rest

    -- check if the second element is identity or Delta 
    -- this is necessary since we "fatten" the second element and it can possibly
    -- become Delta after a while (?)

    | isIdentityPermutation q  = worker'  ep    0  e    (p : rest')
    | isReversePermutation  q  = worker' (ep-1) 0 (e+1) (p : rest')    

    -- ok so we have something like "... : Q : P"
    -- if F(Q) contains S(P) then we can move on; 
    -- otherwise there is an element j in S(P) \\ F(Q), so we can 
    -- replace it by "... : Qj : jP"

    | otherwise = 
        case permutationStartingSet preal \\ permutationFinishingSet qreal of  
          []    -> let (e',rs) = worker' eq 0 e rest in (e', preal : rs)
          (j:_) -> worker' (-e) (-e) e (p':q':rest') where 
                     s  = P.adjacentTransposition n j
                     p' = P.multiplyPermutation s preal
                     q' = P.multiplyPermutation qreal s
        where
          preal = oddTau (e+ep) p       -- the "real" p
          qreal = oddTau (e+eq) q       -- the "real" q

  worker' _   _  !e [ ] = (e,[])
  worker' !ep _  !e [p] 
    | isIdentityPermutation p  = (e   , [])
    | isReversePermutation  p  = (e+1 , [])
    | otherwise                = (e   , [oddTau (e+ep) p] )

  oddTau :: Int -> Permutation -> Permutation
  oddTau !e p = if even e then p else tauPerm p

{-
  checkDelta :: Int -> Permutation -> [Permutation] -> (Int,[Permutation])
  checkDelta !e !p !rest 
    | P.isIdentityPermutation p  = worker  e    rest
    | isReversePermutation    p  = worker (e+1) rest
    | otherwise                  = let (e',rs) = worker e rest in (e', oddTau e p : rs)
-}        

-------------------------------------------------------------------------------- 

-- | Given a /positive/ word, we apply left-greedy factorization of
-- that word into subwords representing /permutation braids/.
--
-- Example 5.1 from the above handbook:
--
-- > leftGreedyFactors 7 [1,3,2,2,1,3,3,2,3,2] == [[1,3,2],[2,1,3],[3,2,3],[2]]
--
leftGreedyFactors :: Int -> [Int] -> [[Int]]
leftGreedyFactors n input = filter (not . null) $ runST (action input) where

  action :: forall s. [Int] -> ST s [[Int]]
  action input = do

    perm <- newArray_ (1,n) :: ST s (STUArray s Int Int)
    forM_ [1..n] $ \i -> writeArray perm i i
    let doSwap :: Int -> ST s ()
        doSwap i = do
          a <- readArray perm  i
          b <- readArray perm (i+1)
          writeArray perm  i    b
          writeArray perm (i+1) a
               
    mat <- newArray ((1,1),(n,n)) 0 :: ST s (STUArray s (Int,Int) Int)
    let clearMat = forM_ [1..n] $ \i -> 
          forM_ [1..n] $ \j -> writeArray mat (i,j) 0
          
    let doAdd1 :: Int -> Int -> ST s Int
        doAdd1 i j = do
          x <- readArray mat (i,j)
          let y = x+1
          writeArray mat (i,j) y 
          writeArray mat (j,i) y
          return y
           
    let worker :: [Int] -> ST s [[Int]]
        worker []     = return [[]]
        worker (p:ps) = do
          u <- readArray perm  p 
          v <- readArray perm (p+1)
          c <- doAdd1 u v 
          doSwap p
          if c<=1
            then do
              (f:fs) <- worker ps
              return ((p:f):fs)
            else do
              clearMat
              fs <- worker (p:ps)
              return ([]:fs)
              
    worker input

--------------------------------------------------------------------------------

{-

-- | Finds ternary braid relations, and returns them as a list of indices, decorated
-- with a flag specifying which side of the relation we found, a sign specifying
-- whether it is a relation between positive or negative generators.
--
findTernaryBraidRelations :: Braid n -> [(Int,Bool,Sign)]
findTernaryBraidRelations (Braid gens) = go 0 gens where
  go !k (Sigma a : rest@(Sigma b : Sigma c : _))  
    | a==c && b==a+1 = (k,True ,Plus) : go (k+1) rest
    | a==c && b==a-1 = (k,False,Plus) : go (k+1) rest
    | otherwise      =                  go (k+1) rest
  go !k (SigmaInv a : rest@(SigmaInv b : SigmaInv c : _))  
    | a==c && b==a+1 = (k,True ,Minus) : go (k+1) rest
    | a==c && b==a-1 = (k,False,Minus) : go (k+1) rest
    | otherwise      =                   go (k+1) rest
  go !k (x:xs) = go (k+1) xs
  go _  []     = []

-- | Finds subsequences like @(i,i+1,i)@ and @(i+1,i,i+1)@, and returns them
-- and a list of indices, plus a flag specifying which one we found (the first 
-- one is 'True', second one is 'False')
--
_findTernaryBraidRelations :: [Int] -> [(Int,Bool)]
_findTernaryBraidRelations = go 0 where
  go !k (a:rest@(b:c:_))  
    | a==c && b==a+1 = (k,True ) : go (k+1) rest
    | a==c && b==a-1 = (k,False) : go (k+1) rest
    | otherwise      =             go (k+1) rest
  go !k (x:xs) = go (k+1) xs
  go _  []     = []

-}

--------------------------------------------------------------------------------

