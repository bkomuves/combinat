

-- | Tests for number theory
--

{-# LANGUAGE CPP, GeneralizedNewtypeDeriving, DataKinds, KindSignatures #-}
module Tests.Numbers.Primes where

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
import Math.Combinat.Numbers
import Math.Combinat.Numbers.Primes
import Math.Combinat.Helper

--------------------------------------------------------------------------------

prop_primes_sum_100    =  sum (take    100 primes)  @=?       24133 
prop_primes_sum_1000   =  sum (take   1000 primes)  @=?     3682913
prop_primes_sum_10000  =  sum (take  10000 primes)  @=?   496165411
prop_primes_sum_100000 =  sum (take 100000 primes)  @=? 62260698721

prop_divisorsigma1_sum_1000   =  sum [ divisorSum    n | n <- [1..1000] ]  @=?  823081
prop_divisorsigma1_sum_1000_b =  sum [ divisorSum' 1 n | n <- [1..1000] ]  @=?  823081
prop_divisorsigma2_sum_1000   =  sum [ divisorSum' 2 n | n <- [1..1000] ]  @=?  401382971
prop_divisorsigma3_sum_1000   =  sum [ divisorSum' 3 n | n <- [1..1000] ]  @=?  271161435595

prop_divisors_def n  =  sort (divisors n) == [ d | d<-[1..n] , d `divides` n ]

prop_moebius_inversion n   =  sum [ moebiusMu d | d <- divisors n ] == (if n==1 then 1 else 0)

prop_totient_divisorsum n  =  n == sum [ eulerTotient d | d <- divisors n ]

prop_totient_mobius_inv n  =  eulerTotient n == sum [ moebiusMu d * div n d | d <- divisors n ]

prop_Liouville_squaredivs n =  liouvilleLambda n == rhs where
  rhs = sum [ moebiusMu (div n d2) 
            | d <- divisors n , let d2 = d*d , d2 <= n , d2 `divides` n
            ] 

prop_Liouville_sum n = sum [ liouvilleLambda d | d <- divisors n ] == (if isSquare n then 1 else 0) 

--------------------------------------------------------------------------------

prop_product_of_factors n  =  productOfFactors (factorize n) == n
prop_factorize_vs_naive n  =  factorize n == factorizeNaive n

--------------------------------------------------------------------------------

main = defaultMain tests

tests :: TestTree
tests = testGroup "Tests" [{-properties,-} unitTests]

unitTests :: TestTree
unitTests = testGroup "Primes module"
  [ unitTests1
  , unitTests2
  ]

unitTests1 :: TestTree
unitTests1 = testGroup "Elementary number theory unit tests "
  [ testCase "sum first 100 primes"         $ prop_primes_sum_100
  , testCase "sum first 1000 primes"        $ prop_primes_sum_1000
  , testCase "sum first 10000 primes"       $ prop_primes_sum_10000
  , testCase "sum first 100000 primes"      $ prop_primes_sum_100000
  , testCase "divisor set"                  $ allTrue [ prop_divisors_def n | n<-[1..1000] ]
  , testCase "sum 1000 divisor sigma_1"     $ prop_divisorsigma1_sum_1000
  , testCase "sum 1000 divisor sigma_1 /b"  $ prop_divisorsigma1_sum_1000_b
  , testCase "sum 1000 divisor sigma_2"     $ prop_divisorsigma2_sum_1000
  , testCase "sum 1000 divisor sigma_3"     $ prop_divisorsigma3_sum_1000
  , testCase "moebius inversion"            $ allTrue [ prop_moebius_inversion    n | n<-[1..1000] ]
  , testCase "totient divisor sum"          $ allTrue [ prop_totient_divisorsum   n | n<-[1..1000] ]
  , testCase "totient moebius inversion"    $ allTrue [ prop_totient_mobius_inv   n | n<-[1..1000] ]
  , testCase "Liouville square divs sumn"   $ allTrue [ prop_Liouville_squaredivs n | n<-[1..1000] ]
  , testCase "Liouville divisor sum"        $ allTrue [ prop_Liouville_sum        n | n<-[1..1000] ]
  ]

unitTests2 :: TestTree
unitTests2 = testGroup "Integer factorization"
  [ testCase "productOfFactors . factorize = id" $ allTrue [ prop_product_of_factors n | n<-[1..1000] ]
  , testCase "factorize vs. factorizeNaive"      $ allTrue [ prop_factorize_vs_naive n | n<-[1..1000] ]
  ]

allTrue :: [Bool] -> Assertion
allTrue bools = (and bools @=? True)

--------------------------------------------------------------------------------
