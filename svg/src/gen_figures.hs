
-- | A script to generate the SVG figures in the documentation.
-- We use the @combinat-diagrams@ library for that.

module Main where

--------------------------------------------------------------------------------

import Math.Combinat.Partitions.Integer
import Math.Combinat.Partitions.Plane
import Math.Combinat.Partitions.NonCrossing
import Math.Combinat.Tableaux
import Math.Combinat.LatticePaths

import Math.Combinat.Diagrams.Partitions.Integer
import Math.Combinat.Diagrams.Partitions.Plane
import Math.Combinat.Diagrams.Partitions.NonCrossing
import Math.Combinat.Diagrams.Tableaux
import Math.Combinat.Diagrams.LatticePaths

import Diagrams.Core
import Diagrams.Prelude
import Diagrams.Backend.SVG

--------------------------------------------------------------------------------

export fpath size what = renderSVG fpath size $ pad 1.10 what

main = do 
  export "plane_partition.svg" (Width 320) $ drawPlanePartition3D $
    PlanePart [[5,4,3,3,1],[4,4,2,1],[3,2],[2,1],[1],[1]] 

  export "noncrossing.svg" (Width 256) $ pad 1.10 $ drawNonCrossingCircleDiagram' orange True $
    NonCrossing [[3],[5,4,2],[7,6,1],[9,8]]

  export "young_tableau.svg" (Width 256) $ drawTableau $ 
    [ [ 1 , 3 , 4 , 6 , 7 ]
    , [ 2 , 5 , 8 ,10 ]
    , [ 9 ]
    ]

  let u = UpStep
      d = DownStep
      path = [ u,u,d,u,u,u,d,u,d,d,u,d,u,u,u,d,d,d,d,d,u,d,u,u,d,d ]     
  export "dyck_path.svg" (Width 500) $ drawLatticePath $ path
  -- print (pathHeight path, pathNumberOfZeroTouches path, pathNumberOfPeaks path)

  export "ferrers.svg" (Width 256) $ drawFerrersDiagram' EnglishNotation red True $
    Partition [8,6,3,3,1]
