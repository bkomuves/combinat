
-- | Tests for braids. 

{-# LANGUAGE 
      CPP, BangPatterns, 
      ScopedTypeVariables, ExistentialQuantification,
      DataKinds, KindSignatures, Rank2Types,
      TypeOperators, TypeFamilies,
      StandaloneDeriving #-}

module Tests.Braid where

--------------------------------------------------------------------------------

import Math.Combinat.Groups.Braid
import Math.Combinat.Groups.Braid.NF

import Tests.Permutations ()     -- arbitrary instance
import Tests.Common

import Test.Framework
import Test.Framework.Providers.QuickCheck2
import Test.QuickCheck
import Test.QuickCheck.Gen

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

import Math.Combinat.Sign
import Math.Combinat.Helper
import Math.Combinat.TypeLevel
import Math.Combinat.Numbers.Series

import Math.Combinat.Permutations ( Permutation(..) )
import qualified Math.Combinat.Permutations as P

--------------------------------------------------------------------------------
-- * Types and instances

maxBraidWordLen :: Int
maxBraidWordLen = 600

maxStrands :: Int
maxStrands = 18         -- normal forms are very slow for large ones

shrinkBraid :: KnownNat n => Braid n -> [Braid n]
shrinkBraid (Braid gens) = map Braid list where
  len  = length gens
  list = [ take i gens ++ drop (i+1) gens | i<-[0..len-1] ]

-- someRndBraid :: Int -> (forall (n :: Nat). KnownNat n => g -> (Braid n, g)) -> g -> (SomeBraid, g)
-- someRndBraid n f = \g -> let (x,g') = f g in (someBraid n x, g')

-- | equality as /braid words/
(=:=) :: Braid n -> Braid n -> Bool
(=:=) (Braid gens1) (Braid gens2) = (gens1 == gens2)

data UnreducedBraid   = forall n. KnownNat n => Unreduced (Braid n)              
data ReducedBraid     = forall n. KnownNat n => Reduced   (Braid n)              
data PositiveBraid    = forall n. KnownNat n => PositiveB (Braid n)              
data PerturbedBraid   = forall n. KnownNat n => Perturbed (Braid n)   (Braid n)  
data PermutationBraid = forall n. KnownNat n => PermBraid Permutation (Braid n)  
data TwoBraids        = forall n. KnownNat n => TwoBraids (Braid n)   (Braid n)  

deriving instance Show UnreducedBraid
deriving instance Show ReducedBraid
deriving instance Show PositiveBraid
deriving instance Show PerturbedBraid
deriving instance Show PermutationBraid
deriving instance Show TwoBraids

instance KnownNat n => Random (Braid n) where
  randomR _ = random
  random g0 = (b, g2) where
    n = numberOfStrands b
    (l,g1) = randomR (0,maxBraidWordLen) g0
    (b,g2) = randomBraidWord l g1

instance Random UnreducedBraid where
  randomR _ = random
  random = runRand $ do
    n <- randChoose (2,maxStrands)
    l <- randChoose (0,maxBraidWordLen)
    withSelectedM Unreduced (rand $ randomBraidWord l) n

instance Random PositiveBraid where
  randomR _ = random
  random  = runRand $ do
    n <- randChoose (2,maxStrands)
    l <- randChoose (0,maxBraidWordLen)
    withSelectedM PositiveB (rand $ randomPositiveBraidWord l) n

instance Random PerturbedBraid where
  randomR _ = random
  random  = runRand $ do
    Unreduced b <- rand random
    k <- randChoose (20,1000)
    c <- rand $ randomPerturbBraidWord k b 
    return (Perturbed b c)

instance KnownNat n => Arbitrary (Braid n) where
  arbitrary = choose_
  shrink    = shrinkBraid

instance Arbitrary UnreducedBraid where
  arbitrary = choose_
  shrink (Unreduced b) = map Unreduced (shrinkBraid b)

instance Arbitrary PositiveBraid where
  arbitrary = choose_
  shrink (PositiveB b) = map PositiveB (shrinkBraid b)

instance Arbitrary ReducedBraid where
  arbitrary = do
    Unreduced braid <- arbitrary
    return $ Reduced $ freeReduceBraidWord braid

instance Arbitrary PerturbedBraid where
  arbitrary = choose_
  shrink _  = []

instance Arbitrary TwoBraids where
  shrink _  = []
  arbitrary = do
    n <- choose (2::Int, maxStrands)
    let snat = case someNatVal (fromIntegral n :: Integer) of
          Just sn -> sn
          Nothing -> error "TwoBraids/arbitrary: shouldn't happen"
    case snat of 
      SomeNat pxy -> do
        (braid1,braid2) <- choosePair_
        return $ TwoBraids (asProxyTypeOf1 braid1 pxy) (asProxyTypeOf1 braid2 pxy)

mkPermBraid :: Permutation -> PermutationBraid
mkPermBraid perm = 
  case snat of    
    SomeNat pxy -> PermBraid perm (asProxyTypeOf1 (permutationBraid perm) pxy)
  where
    n = P.permutationSize perm
    Just snat = someNatVal (fromIntegral n :: Integer)

instance Arbitrary PermutationBraid where
  arbitrary = do
    perm <- arbitrary
    return $ mkPermBraid perm
  shrink (PermBraid x b) = [ PermBraid (braidPermutation s) s | s <- shrinkBraid b ]

--------------------------------------------------------------------------------
-- * test groups

testgroup_Braid :: Test
testgroup_Braid = testGroup "Braid"
  
  [ testProperty "linking matrix is invariant of reduction"    prop_link_reduce 
  , testProperty "linking matrix is invariant of perturbation" prop_link_perturb
  
  , testProperty "tau^2 = identity"                    prop_tau_square
  , testProperty "tau commutes with braidPermutation"  prop_permTau_1

  , testProperty "braidPermutation . permutationBraid = identity"  prop_permBraid_perm
  , testProperty "permutation braid is indeed a permutation braid" prop_permBraid_valid
  , testProperty "multiplication commutes with braidPermutation" prop_braidPerm_comp

  , testProperty "positive braids have positive links" prop_link_positive
  , testProperty "definition of linking"               prop_linking

  ] 

--------------------------------------------------------------------------------

testgroup_Braid_NF :: Test
testgroup_Braid_NF = testGroup "Braid/NF"
  
  [ testProperty "NF with naive inverse elimination == less naive inverse elimination"  prop_braidnf_naive
  , testProperty "NF with reduction == NF without reduction"                            prop_braidnf_reduce

  , testProperty "NF = NF of representative word of NF"   prop_braidnf_reprs
  , testProperty "NF = NF of perturbed word"              prop_braidnf_perturb

  , testProperty "linking of word == linking of representative of NF"   prop_braidnf_link

  , testProperty "NF of positive word is positive"   prop_braidnf_pos

  , testProperty "Lemma 2.5"   prop_lemma_2_5

  , testProperty "permutationBraid and tau commutes, up to NF"   prop_permTau_2
  ]

--------------------------------------------------------------------------------
-- * braid properties

prop_link_reduce :: UnreducedBraid -> Bool
prop_link_reduce (Unreduced braid) = linkingMatrix braid == linkingMatrix braid' where
  braid' = freeReduceBraidWord braid

prop_link_perturb :: PerturbedBraid -> Bool
prop_link_perturb (Perturbed braid1 braid2) = linkingMatrix braid1 == linkingMatrix braid2 

prop_tau_square :: ReducedBraid -> Bool
prop_tau_square (Reduced braid) = braidWord (tau (tau braid)) == braidWord braid

prop_permTau_1 :: PermutationBraid -> Bool
prop_permTau_1 (PermBraid perm braid) = tauPerm perm == braidPermutation (tau braid)

prop_permBraid_perm :: PermutationBraid -> Bool
prop_permBraid_perm (PermBraid perm braid) = (braidPermutation braid == perm)

prop_permBraid_valid :: PermutationBraid -> Bool
prop_permBraid_valid (PermBraid perm braid) = isPermutationBraid braid

prop_braidPerm_comp :: TwoBraids -> Bool
prop_braidPerm_comp (TwoBraids b1 b2) = (p == q) where
  p = braidPermutation (compose b1 b2) 
  q = braidPermutation b1 `P.multiplyPermutation` braidPermutation b2

prop_link_positive :: PositiveBraid -> Bool
prop_link_positive (PositiveB braid) = all (>=0) $ elems $ linkingMatrix braid

prop_linking :: UnreducedBraid -> Bool
prop_linking (Unreduced braid) = (linkingMatrix braid == matrix) where
  n = numberOfStrands braid
  matrix = array ((1,1),(n,n)) [ ((i,j),strandLinking braid i j) | i<-[1..n], j<-[1..n] ]

--------------------------------------------------------------------------------

prop_braidnf_naive :: UnreducedBraid -> Bool
prop_braidnf_naive (Unreduced braid) = (braidNormalFormNaive' braid == braidNormalForm' braid)

prop_braidnf_reduce :: UnreducedBraid -> Bool
prop_braidnf_reduce (Unreduced braid) = (braidNormalForm' braid == braidNormalForm braid)

prop_braidnf_reprs :: ReducedBraid -> Bool
prop_braidnf_reprs (Reduced braid) = (nf == nf') where
  nf  = braidNormalForm braid 
  nf' = braidNormalForm braid'
  braid' = nfReprWord nf

prop_braidnf_perturb :: PerturbedBraid -> Bool
prop_braidnf_perturb (Perturbed braid1 braid2) = (braidNormalForm braid1 == braidNormalForm braid2)

prop_braidnf_link :: UnreducedBraid -> Bool
prop_braidnf_link (Unreduced braid) = (linkingMatrix braid == linkingMatrix braid') where
  nf  = braidNormalForm braid 
  braid' = nfReprWord nf

prop_braidnf_pos :: PositiveBraid -> Bool
prop_braidnf_pos (PositiveB braid) = (_nfDeltaExp (braidNormalForm braid) >= 0)
 
prop_lemma_2_5 :: Permutation -> Bool
prop_lemma_2_5 p = and [ check i | i<-[1..n-1] ] where
  n = P.permutationSize p
  w = _permutationBraid p
  s = permWordStartingSet n w
  check i = _isPermutationBraid n (i:w) == (not $ elem i s)

prop_permTau_2 :: PermutationBraid -> Bool
prop_permTau_2 (PermBraid perm braid) = (nf1 == nf2) where
  nf1 = braidNormalForm $ permutationBraid (tauPerm perm)
  nf2 = braidNormalForm $ tau braid

--------------------------------------------------------------------------------


