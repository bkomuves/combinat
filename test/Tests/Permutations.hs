
-- | Tests for permutations. 
--

{-# LANGUAGE CPP, ScopedTypeVariables, GeneralizedNewtypeDeriving, FlexibleContexts #-}
module Tests.Permutations where

--------------------------------------------------------------------------------

import Math.Combinat.Permutations

import Test.Framework
import Test.Framework.Providers.QuickCheck2
import Test.QuickCheck
import System.Random

import Control.Monad
import Control.Monad.ST

import Data.List hiding (permutations)

import Data.Array (Array)
import Data.Array.ST
import Data.Array.Unboxed
import Data.Array.IArray
import Data.Array.MArray
import Data.Array.Unsafe

import Math.Combinat.ASCII
import Math.Combinat.Classes
import Math.Combinat.Helper
import Math.Combinat.Sign
import Math.Combinat.Numbers (factorial,binomial)

--------------------------------------------------------------------------------
-- * generating permutations (random & arbitrary instances, spec types etc)

minPermSize = 1
maxPermSize = 123

newtype Elem = Elem Int deriving Eq
newtype Nat  = Nat { fromNat :: Int } deriving (Eq,Ord,Show,Num,Random)

naturalSet :: Permutation -> Array Int Elem
naturalSet perm = listArray (1,n) [ Elem i | i<-[1..n] ] where
  n = permutationSize perm

permInternalSet :: Permutation -> Array Int Elem
permInternalSet perm@(Permutation arr) = listArray (1,n) [ Elem (arr!i) | i<-[1..n] ] where
  n = permutationSize perm

sameSize :: Permutation ->  Permutation -> Bool
sameSize perm1 perm2 = ( permutationSize perm1 == permutationSize perm2)

newtype CyclicPermutation = Cyclic { fromCyclic :: Permutation } deriving Show

data SameSize = SameSize Permutation Permutation deriving Show

instance Random Permutation where
  random g = randomPermutation size g1 where
    (size,g1) = randomR (minPermSize,maxPermSize) g
  randomR _ = random

instance Random CyclicPermutation where
  random g = (Cyclic cycl,g2) where
    (size,g1) = randomR (minPermSize,maxPermSize) g
    (cycl,g2) = randomCyclicPermutation size g1
  randomR _ = random

instance Random DisjointCycles where
  random g = (disjcyc,g2) where
    (size,g1) = randomR (minPermSize,maxPermSize) g
    (perm,g2) = randomPermutation size g1
    disjcyc   = permutationToDisjointCycles perm
  randomR _ = random

instance Random SameSize where
  random g = (SameSize prm1 prm2, g3) where
    (size,g1) = randomR (minPermSize,maxPermSize) g
    (prm1,g2) = randomPermutation size g1 
    (prm2,g3) = randomPermutation size g2
  randomR _ = random

instance Arbitrary Nat where
  arbitrary = choose (Nat 0 , Nat 50)
     
instance Arbitrary Permutation       where arbitrary = choose undefined
instance Arbitrary CyclicPermutation where arbitrary = choose undefined
instance Arbitrary DisjointCycles    where arbitrary = choose undefined
instance Arbitrary SameSize          where arbitrary = choose undefined

--------------------------------------------------------------------------------
-- * test group

testgroup_Permutations :: Test
testgroup_Permutations = testGroup "Permutations"
  
  [ testProperty "disjoint cycles /1" prop_disjcyc_1
  , testProperty "disjoint cycles /2" prop_disjcyc_2 

  , testProperty "disjoint cycles compatibility" prop_disjcyc_Mathematica

  , testProperty "random cyclic permutation is indeed cyclic" prop_randCyclic
  , testProperty "inverse^2 is identity"                      prop_inverse

  , testProperty "permutation action is group action"              prop_mulPerm
  , testProperty "left permutation action is left group action"    prop_mulPermLeft
  , testProperty "right permutation action is right group action"  prop_mulPermRight

  , testProperty "permutation action convetion"        prop_perm
  , testProperty "left permutation action convention"  prop_permLeft
  , testProperty "right permutation action convention" prop_permRight
  , testProperty "left/right permutation action convention" prop_permLeftRight

  , testProperty "cycle left"  prop_cycleLeft
  , testProperty "cycle right" prop_cycleRight

  , testProperty "sign of permutation is multiplicative"     prop_mulSign      
  , testProperty "inverse is compatible with multiplication" prop_invMul

  , testProperty "parity of cyclic permutaiton" prop_cyclSign
  , testProperty "random permutation is valid"  prop_permIsPerm
  , testProperty "definition of parity"         prop_isEven

  , testProperty "bubbleSort works"    prop_bubbleSort
  , testProperty "bubbleSort2 works"   prop_bubbleSort2
  , testProperty "number of inversions = steps in bubble sort"         prop_bubble_inversions
  , testProperty "number of inversions = actual number of inversions"  prop_number_inversions 
  , testProperty "number of inversions is the same for the inverse permutation"  prop_ninversions_inverse
  , testProperty "merge sort algorithm = naive inversion count"                  prop_merge_inversions

  ]

--------------------------------------------------------------------------------
-- * test properties
          
prop_disjcyc_1 perm = ( perm == disjointCyclesToPermutation n (permutationToDisjointCycles perm) )
  where n = permutationSize perm

prop_disjcyc_2 k dcyc = ( dcyc == permutationToDisjointCycles (disjointCyclesToPermutation n dcyc) )
  where 
    n = fromNat k + m 
    m = case fromDisjointCycles dcyc of
      []  -> 1
      xxs -> maximum (concat xxs)

-- PermutationCycles[ { 12, 15, 5, 6, 2, 7, 17, 9, 20, 3, 11, 18, 22, 21, 8, 10, 4, 19, 14, 16, 23, 1, 13 } ]
-- Cycles           [ {{1, 12, 18, 19, 14, 21, 23, 13, 22}, {2, 15, 8, 9, 20, 16, 10, 3, 5}, {4, 6, 7, 17}} ]
prop_disjcyc_Mathematica = (permutationToDisjointCycles   perm == disjcyc) 
                        && (disjointCyclesToPermutation n disjcyc == perm)
  where
    n       = permutationSize perm
    perm    = toPermutation  [ 12, 15, 5, 6, 2, 7, 17, 9, 20, 3, 11, 18, 22, 21, 8, 10, 4, 19, 14, 16, 23, 1, 13 ]
    disjcyc = DisjointCycles [ [1, 12, 18, 19, 14, 21, 23, 13, 22], [2, 15, 8, 9, 20, 16, 10, 3, 5], [4, 6, 7, 17] ]

xperm    = toPermutation  [ 12, 15, 5, 6, 2, 7, 17, 9, 20, 3, 11, 18, 22, 21, 8, 10, 4, 19, 14, 16, 23, 1, 13 ]
xdisjcyc = DisjointCycles [ [1, 12, 18, 19, 14, 21, 23, 13, 22], [2, 15, 8, 9, 20, 16, 10, 3, 5], [4, 6, 7, 17] ]

prop_randCyclic cycl = ( isCyclicPermutation (fromCyclic cycl) )

prop_inverse perm = ( perm == inverse (inverse perm) ) 

prop_mulPerm (SameSize perm1 perm2) = 
    ( permute perm2 (permute perm1 set) == permute (perm1 `multiply` perm2) set ) 
  where 
    set = naturalSet perm1

prop_mulPermRight (SameSize perm1 perm2) = 
    ( permuteRight perm2 (permuteRight perm1 set) == permuteRight (perm1 `multiply` perm2) set ) 
  where 
    set = naturalSet perm1

prop_mulPermLeft (SameSize perm1 perm2) = 
    ( permuteLeft perm2 (permuteLeft perm1 set) == permuteLeft (perm2 `multiply` perm1) set ) 
  where 
    set = naturalSet perm1

prop_perm          perm = permute perm (naturalSet perm) == permInternalSet perm
prop_permLeft      perm = permuteLeft  perm (permInternalSet perm) == naturalSet perm
prop_permRight     perm = permuteRight perm (naturalSet perm) == permInternalSet perm
prop_permLeftRight perm = permuteLeft (inverse perm) (naturalSet perm) == permuteRight (perm) (naturalSet perm) 

prop_cycleLeft  = permuteList (cycleLeft  5) "abcde" == "bcdea"
prop_cycleRight = permuteList (cycleRight 5) "abcde" == "eabcd"

prop_mulSign (SameSize perm1 perm2) = 
    ( sgn perm1 * sgn perm2 == sgn (perm1 `multiply` perm2) ) 
  where 
    sgn = signValue . signOfPermutation :: Permutation -> Int

prop_invMul (SameSize perm1 perm2) =   
  ( inverse perm2 `multiply` inverse perm1 == inverse (perm1 `multiply` perm2) ) 

prop_cyclSign cycl = ( isEvenPermutation perm == odd n ) where
  perm = fromCyclic cycl
  n = permutationSize perm
  
prop_permIsPerm perm = ( isPermutation (fromPermutation perm) ) 

prop_isEven perm = ( isEvenPermutation perm == isEvenAlternative perm ) where
  isEvenAlternative p = 
    even $ sum $ map (\x->x-1) $ map length $ fromDisjointCycles $ permutationToDisjointCycles p

prop_bubbleSort perm = multiplyMany' n (map (adjacentTransposition n) $ bubbleSort perm) == perm where
  n = permutationSize perm

prop_bubbleSort2 perm = multiplyMany' n (map (transposition n) $ bubbleSort2 perm) == perm where
  n = permutationSize perm

prop_bubble_inversions perm = length (bubbleSort perm) == numberOfInversions perm

prop_number_inversions perm = length (inversions perm) == numberOfInversions perm

prop_ninversions_inverse perm = numberOfInversions perm == numberOfInversions (inverse perm)

prop_merge_inversions perm = (numberOfInversionsMerge perm == numberOfInversionsNaive perm)

--------------------------------------------------------------------------------

