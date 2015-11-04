
-- | Tests for Thompson's group F
--

{-# LANGUAGE CPP, GeneralizedNewtypeDeriving, FlexibleInstances, TypeSynonymInstances #-}
module Tests.Thompson where

--------------------------------------------------------------------------------

import Prelude hiding ( (**) )
import Control.Monad
import Data.List

import Math.Combinat.Groups.Thompson.F
import qualified Math.Combinat.Trees.Binary as B

import Tests.Common

import Test.Framework
import Test.Framework.Providers.QuickCheck2
import Test.QuickCheck
import System.Random

import Math.Combinat.Helper


--------------------------------------------------------------------------------
-- * code

(**) :: TDiag -> TDiag -> TDiag
(**) x y = x `compose` y

(//) :: TDiag -> TDiag -> TDiag
(//) x y = x `compose` (inverse y)

growth_n_sphere     = [1,4,12,36,108,314,906,2576,7280,20352] :: [Int]
growth_pos_n_sphere = [1,2, 4, 9, 20, 45,101, 227, 510, 1146] :: [Int]

--------------------------------------------------------------------------------
-- * instances

-- | A pair of trees with the same size
data TPair = TPair !T !T deriving (Eq,Show)

newtype Unreduced = Unreduced TDiag deriving (Eq,Show)

instance Arbitrary T where
  arbitrary = liftM fromBinTree $ myMkSizedGen B.randomBinaryTree

instance Arbitrary TPair where
  arbitrary = myMkSizedGen $ \siz -> runRand $ do
    t1 <- rand (B.randomBinaryTree siz)
    t2 <- rand (B.randomBinaryTree siz)
    return $ TPair (fromBinTree t1) (fromBinTree t2)

instance Arbitrary TDiag where
  arbitrary = do 
    TPair t1 t2 <- arbitrary
    return $ mkTDiag t1 t2

instance Arbitrary Unreduced where
  arbitrary = do 
    TPair t1 t2 <- arbitrary
    return $ Unreduced $ mkTDiagDontReduce t1 t2

--------------------------------------------------------------------------------
-- * test group

testgroup_ThompsonF :: Test
testgroup_ThompsonF = testGroup "Thompson's group F"
  [ testProperty "identity element"                    prop_identity
  , testProperty "associativity"                       prop_assoc
  , testProperty "standard relations"                  prop_relations
  , testProperty "quotient of positives"               prop_quot_positive
  , testProperty "telescopic product"                  prop_telescope
  , testProperty "cyclic telescopic product (3)"       prop_cyclic_product_3
  , testProperty "cyclic telescopic product (4)"       prop_cyclic_product_4
  , testProperty "positive diagrams form a monoid"     prop_positive_product
  , testProperty "composition commutes with reduction" prop_reduce_composition
  , testProperty "inverse commutes with reduction"     prop_reduce_inverse
  ]

--------------------------------------------------------------------------------
-- * properties
    
prop_relations :: Bool
prop_relations = and [ rel k n | n<-[1..30] , k<-[0..n-1] ] where
  rel k n = (inverse $ xk k) `compose` (xk n) `compose` (xk k) == xk (n+1)

prop_quot_positive :: TPair -> Bool
prop_quot_positive (TPair t1 t2) = (mkTDiag t1 t2) == (positive t1 // positive t2)

prop_identity :: TDiag -> Bool
prop_identity x = (x ** identity) == x && (identity ** x) == x

prop_assoc :: TDiag -> TDiag -> TDiag -> Bool
prop_assoc a b c = (p == q) where
  p = compose (compose a b) c
  q = compose a (compose b c)

prop_telescope :: TDiag -> TDiag -> TDiag -> TDiag -> Bool
prop_telescope u v w z = (a `compose` b `compose` c) == (u // z) where
  a = u // v
  b = v // w
  c = w // z

prop_cyclic_product_3 :: TDiag -> TDiag -> TDiag -> Bool
prop_cyclic_product_3 u v w = (a `compose` b `compose` c) == identity where
  a = u // v
  b = v // w
  c = w // u

prop_cyclic_product_4 :: TDiag -> TDiag -> TDiag -> TDiag -> Bool
prop_cyclic_product_4 u v w z = (a `compose` b `compose` c `compose` d) == identity where
  a = u // v
  b = v // w
  c = w // z
  d = z // u

prop_positive_product :: T -> T -> Bool
prop_positive_product x y = isPositive (positive x `compose` positive y)

prop_reduce_composition :: Unreduced -> Unreduced -> Bool
prop_reduce_composition (Unreduced x) (Unreduced y) = lhs == rhs where
  lhs = reduce (x `composeDontReduce` y)
  rhs = compose (reduce x) (reduce y)

prop_reduce_inverse :: Unreduced -> Bool
prop_reduce_inverse (Unreduced x) = lhs == rhs where
  lhs = reduce (inverse x)
  rhs = inverse (reduce x)

--------------------------------------------------------------------------------

