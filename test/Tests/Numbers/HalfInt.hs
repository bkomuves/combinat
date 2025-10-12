module Tests.Numbers.HalfInt where

import Test.Framework
import Test.Framework.Providers.HUnit
import Test.HUnit (assertEqual)

import Math.Combinat.Numbers.HalfInt


testgroup_HalfInt :: Test
testgroup_HalfInt = testGroup "HalfInt"
  [ testDotProduct ]

testDotProduct :: Test
testDotProduct = testCase "dotProd" $ do
  assertEqual "1/4 + 1/4 + 1/4 + 1/4" (dotProd [half, half, half, half] [half, half, half, half]) 1
  assertEqual "1 + 1 + 1 + 1" (dotProd [1, 1, 1, 1] [1, 1, 1, 1]) 4
  assertEqual "1/4 + 1/4" (dotProd [half, half] [half, half]) half
