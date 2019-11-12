
module Main where

--------------------------------------------------------------------------------

import Test.Framework
import Test.Framework.Providers.QuickCheck2

import Tests.Permutations       ( testgroup_Permutations      )
import Tests.Partitions.Integer ( testgroup_IntegerPartitions )
import Tests.Partitions.Skew    ( testgroup_SkewPartitions    )
import Tests.Partitions.Ribbon  ( testgroup_Ribbon      )
import Tests.Braid              ( testgroup_Braid 
                                , testgroup_Braid_NF          )
import Tests.Series             ( testgroup_PowerSeries       )
import Tests.SkewTableaux       ( testgroup_SkewTableaux      )
import Tests.Thompson           ( testgroup_ThompsonF         )
import Tests.LatticePaths       ( testgroup_LatticePaths      )

--------------------------------------------------------------------------------

main :: IO ()
main = defaultMain tests

{- 

----- missing (because tasty, not test-framework): -----

Partitions.Compact
Numbers.Primes
Numbers.Sequences

-}


tests :: [Test]
tests = 
  [ testgroup_Permutations
  , testgroup_PowerSeries  
  , testGroup "Partitions" 
      [ testgroup_IntegerPartitions
      , testgroup_SkewPartitions
      , testgroup_Ribbon
      ]
  , testgroup_SkewTableaux
  , testgroup_ThompsonF
  , testgroup_LatticePaths
  , testGroup "Braids" 
      [ testgroup_Braid 
      , testgroup_Braid_NF 
      ]
  ]

--------------------------------------------------------------------------------
