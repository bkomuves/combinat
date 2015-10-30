
-- | A script to generate the SVG figures in the documentation.
-- We use the @combinat-diagrams@ library for that.

module Main where

--------------------------------------------------------------------------------

import Math.Combinat.Partitions.Integer
import Math.Combinat.Partitions.Plane
import Math.Combinat.Partitions.NonCrossing
import Math.Combinat.Partitions.Skew
import Math.Combinat.Tableaux
import Math.Combinat.Tableaux.Skew
import Math.Combinat.LatticePaths
import Math.Combinat.Trees.Binary

import Math.Combinat.Diagrams.Partitions.Integer
import Math.Combinat.Diagrams.Partitions.Plane
import Math.Combinat.Diagrams.Partitions.NonCrossing
import Math.Combinat.Diagrams.Partitions.Skew
import Math.Combinat.Diagrams.Tableaux
import Math.Combinat.Diagrams.Tableaux.Skew
import Math.Combinat.Diagrams.LatticePaths
import Math.Combinat.Diagrams.Trees.Binary

import Diagrams.Core
import Diagrams.Prelude
import Diagrams.Backend.SVG

--------------------------------------------------------------------------------

export fpath size what = renderSVG fpath size $ pad 1.10 what

vcatSep = vcat' (with & sep .~ 1) 
hcatSep = hcat' (with & sep .~ 1) 

boxSep m xs = pad 1.05 $ vcatSep $ map hcatSep $ yys where
  yys = go xs where
    go [] = []
    go zs = take m zs : go (drop m zs) 

padding fac diag = pad fac $ centerXY diag
margin  siz diag = hcat [ strutX siz , vcat [ strutY siz , centerXY diag , strutY siz ] , strutX siz ]

--------------------------------------------------------------------------------

main = do 

  export "plane_partition.svg" (mkWidth 320) $ margin 0.05 $ drawPlanePartition3D $
    PlanePart [[5,4,3,3,1],[4,4,2,1],[3,2],[2,1],[1],[1]] 

  export "noncrossing.svg" (mkWidth 256) $ padding 1.10 $ drawNonCrossingCircleDiagram' orange True $
    NonCrossing [[3],[5,4,2],[7,6,1],[9,8]]

  export "young_tableau.svg" (mkWidth 256) $ margin 0.05 $ drawTableau $ 
    [ [ 1 , 3 , 4 , 6 , 7 ]
    , [ 2 , 5 , 8 ,10 ]
    , [ 9 ]
    ]

  let u = UpStep
      d = DownStep
      path = [ u,u,d,u,u,u,d,u,d,d,u,d,u,u,u,d,d,d,d,d,u,d,u,u,d,d ]     
  export "dyck_path.svg" (mkWidth 500) $ margin 0.05 $ drawLatticePath $ path
  -- print (pathHeight path, pathNumberOfZeroTouches path, pathNumberOfPeaks path)

  export "ferrers.svg" (mkWidth 256) $ margin 0.05 $ drawFerrersDiagram' EnglishNotation red True $
    Partition [8,6,3,3,1]

  export "bintrees.svg" (mkWidth 750) $ boxSep 7 $ map drawBinTree_ (binaryTrees 4)

  let skew = mkSkewPartition (Partition [9,7,3,2,2,1] , Partition [5,3,2,1])
  -- export "skew.svg"  (mkWidth 256) $ margin 0.05 $ drawSkewFerrersDiagram  skew
  -- export "skew2.svg" (mkWidth 256) $ margin 0.05 $ drawSkewFerrersDiagram' EnglishNotation green True (True,True) skew
  export "skew3.svg" (mkWidth 256) $ margin 0.05 $ drawSkewPartitionBoxes  EnglishNotation skew

  let skewtableau  = (semiStandardSkewTableaux 7 skew) !! 123
  export "skew_tableau.svg" (mkWidth 320) $ margin 0.05 $ drawSkewTableau' EnglishNotation blue True skewtableau

--------------------------------------------------------------------------------
