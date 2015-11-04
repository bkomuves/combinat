
module Main where

--------------------------------------------------------------------------------

import Test.Framework
import Test.Framework.Providers.QuickCheck2

import Tests.Permutations       ( testgroup_Permutations      )
import Tests.Partitions.Integer ( testgroup_IntegerPartitions )
import Tests.Partitions.Skew    ( testgroup_SkewPartitions    )
import Tests.Braid              ( testgroup_Braid 
                                , testgroup_Braid_NF          )
import Tests.Series             ( testgroup_PowerSeries       )
import Tests.SkewTableaux       ( testgroup_SkewTableaux      )
import Tests.Thompson           ( testgroup_ThompsonF         )

--------------------------------------------------------------------------------

main :: IO ()
main = defaultMain tests

tests :: [Test]
tests = 
  [ testgroup_Permutations
  , testGroup "Partitions" 
      [ testgroup_IntegerPartitions
      , testgroup_SkewPartitions
      ]
  , testgroup_SkewTableaux
  , testgroup_ThompsonF
  , testGroup "Braids" 
      [ testgroup_Braid 
      , testgroup_Braid_NF 
      ]
  , testgroup_PowerSeries  
  ]

--------------------------------------------------------------------------------
