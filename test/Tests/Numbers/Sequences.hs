

-- | Tests for integer sequences
--

{-# LANGUAGE CPP, GeneralizedNewtypeDeriving, DataKinds, KindSignatures #-}
module Tests.Numbers.Sequences where

--------------------------------------------------------------------------------

{-
import Test.Framework
import Test.Framework.Providers.QuickCheck2
import Test.QuickCheck
-}

import Test.Tasty
import Test.Tasty.HUnit      as U
import Test.Tasty.QuickCheck as Q 

import System.Random

import Data.List
import Data.Ratio

import GHC.TypeLits
import Data.Proxy

import Math.Combinat.Sign
import Math.Combinat.Numbers.Sequences
import Math.Combinat.Numbers.Primes
import Math.Combinat.Helper

--------------------------------------------------------------------------------

prop_factorial_naive_vs_split n = factorialNaive n == factorialSplit n
prop_factorial_split_vs_swing n = factorialSplit n == factorialSwing n

prop_fac_exponents_vs_naive n  = factorialPrimeExponents n == factorialPrimeExponentsNaive n
prop_factorial_vs_fac_expos n  = productOfFactors (factorialPrimeExponents n) == factorial n

prop_double_factorial_naive_vs_split n = doubleFactorialNaive n == doubleFactorialSplit n

prop_binomial_naive_vs_split n k = binomialNaive n k == binomialSplit n k

--------------------------------------------------------------------------------

main = defaultMain tests

tests :: TestTree
tests = testGroup "Tests" [{-properties,-} unitTests]

unitTests :: TestTree
unitTests = testGroup "Numbers.Sequences module"
  [ testCase "naive vs. split factorial"          $ allTrue [ prop_factorial_naive_vs_split n | n<-[1..1000] ]
  , testCase "split vs. swing factorial"          $ allTrue [ prop_factorial_split_vs_swing n | n<-[1..1000] ]
  , testCase "naive vs. fast factorial expos"     $ allTrue [ prop_fac_exponents_vs_naive   n | n<-[1..1000] ]
  , testCase "factorial vs. fac exponents"        $ allTrue [ prop_factorial_vs_fac_expos   n | n<-[1..1000] ]
  , testCase "naive vs. split double factorial"   $ allTrue [ prop_double_factorial_naive_vs_split n | n<-[1..1000]  ]
  , testCase "naive vs. split binomial"           $ allTrue [ prop_binomial_naive_vs_split n k | n<-[1..100] , k<-[-3..n+3] ]
  ]

allTrue :: [Bool] -> Assertion
allTrue bools = (and bools @=? True)

--------------------------------------------------------------------------------
