
-- | Helper routines for tests

{-# LANGUAGE Rank2Types #-}
module Tests.Common where

--------------------------------------------------------------------------------

import Test.QuickCheck
import Test.QuickCheck.Gen

import System.Random

--------------------------------------------------------------------------------

-- | Generates a random element.
choose_ :: Random a => Gen a
choose_ = MkGen (\r _ -> let (x,_) = random r in x)

-- | Generates two random elements 
choosePair_ :: Random a => Gen (a,a)
choosePair_ = do
  x <- choose_
  y <- choose_
  return (x,y)

-- | Generates a random element.
myMkGen :: (forall g. RandomGen g => g -> (a,g)) -> Gen a
myMkGen fun = MkGen (\r _ -> let (x,_) = fun r in x)

-- | Generates a random element.
myMkGen' :: (a -> b) -> (forall g. RandomGen g => g -> (a,g)) -> Gen b
myMkGen' h fun = MkGen (\r _ -> let (x,_) = fun r in h x)

-- | Generates a random element.
myMkSizedGen :: (forall g. RandomGen g => Int -> g -> (a,g)) -> Gen a
myMkSizedGen fun = MkGen (\r siz -> let (x,_) = fun siz r in x)

--------------------------------------------------------------------------------