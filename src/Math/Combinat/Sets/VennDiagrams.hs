
-- | Venn diagrams. See <https://en.wikipedia.org/wiki/Venn_diagram>
--
-- TODO: write a more efficient implementation (for example an array of size @2^n@)
--

{-# LANGUAGE BangPatterns #-}
module Math.Combinat.Sets.VennDiagrams where

--------------------------------------------------------------------------------

import Data.List

import GHC.TypeLits
import Data.Proxy

import qualified Data.Map as Map
import Data.Map (Map)

import Math.Combinat.Compositions
import Math.Combinat.ASCII

--------------------------------------------------------------------------------

-- | Venn diagrams of @n@ sets. Each possible zone is annotated with a value
-- of type @a@. A typical use case is to annotate with the cardinality of the
-- given zone.
--
-- Internally this is representated by a map from @[Bool]@, where @True@ means element 
-- of the set, @False@ means not.
--
-- TODO: write a more efficient implementation (for example an array of size 2^n)
newtype VennDiagram a = VennDiagram { vennTable :: Map [Bool] a } deriving (Eq,Ord,Show)

-- | How many sets are in the Venn diagram
vennDiagramNumberOfSets :: VennDiagram a -> Int
vennDiagramNumberOfSets (VennDiagram table) = length $ fst $ Map.findMin table

-- | How many zones are in the Venn diagram
--
-- > vennDiagramNumberOfZones v == 2 ^ (vennDiagramNumberOfSets v)
--
vennDiagramNumberOfZones :: VennDiagram a -> Int
vennDiagramNumberOfZones venn = 2 ^ (vennDiagramNumberOfSets venn)

-- | How many /nonempty/ zones are in the Venn diagram
vennDiagramNumberOfNonemptyZones :: VennDiagram Int -> Int
vennDiagramNumberOfNonemptyZones (VennDiagram table) = length $ filter (/=0) $ Map.elems table

unsafeMakeVennDiagram :: [([Bool],a)] -> VennDiagram a
unsafeMakeVennDiagram = VennDiagram . Map.fromList

-- | We call venn diagram trivial if all the intersection zones has zero cardinality
-- (that is, the original sets are all disjoint)
isTrivialVennDiagram :: VennDiagram Int -> Bool
isTrivialVennDiagram (VennDiagram table) = and [ c == 0 | (bs,c) <- Map.toList table , isIntersection bs ] where
  isIntersection bs = case filter id bs of
    []  -> False
    [_] -> False
    _   -> True

printVennDiagram :: Show a => VennDiagram a -> IO ()
printVennDiagram = putStrLn . prettyVennDiagram

prettyVennDiagram :: Show a => VennDiagram a -> String
prettyVennDiagram = unlines . asciiLines . asciiVennDiagram

asciiVennDiagram :: Show a => VennDiagram a -> ASCII
asciiVennDiagram (VennDiagram table) = asciiFromLines $ map f (Map.toList table) where
  f (bs,a) = "{" ++ extendTo (length bs) [ if b then z else ' ' | (b,z) <- zip bs abc ] ++ "} -> " ++ show a
  extendTo k str = str ++ replicate (k - length str) ' '
  abc = ['A'..'Z']

instance Show a => DrawASCII (VennDiagram a) where
  ascii = asciiVennDiagram

-- | Given a Venn diagram of cardinalities, we compute the cardinalities of the
-- original sets (note: this is slow!)
vennDiagramSetCardinalities :: VennDiagram Int -> [Int]
vennDiagramSetCardinalities (VennDiagram table) = go n list where
  list = Map.toList table
  n = length $ fst $ head list
  go :: Int -> [([Bool],Int)] -> [Int]
  go !0 _  = []
  go !k xs = this : go (k-1) (map xtail xs) where
    this = foldl' (+) 0 [ c | ((True:_) , c) <- xs ]
  xtail (bs,c) = (tail bs,c)

--------------------------------------------------------------------------------

-- | Given the cardinalities of some finite sets, we list all possible
-- Venn diagrams.
--
-- Note: we don't include the empty zone in the tables, because it's always empty.
--
-- Remark: if each sets is a singleton set, we get back set partitions:
--
-- > > [ length $ enumerateVennDiagrams $ replicate k 1 | k<-[1..8] ]
-- > [1,2,5,15,52,203,877,4140]
-- >
-- > > [ countSetPartitions k | k<-[1..8] ]
-- > [1,2,5,15,52,203,877,4140]
--
-- Maybe this could be called multiset-partitions?
--
-- Example:
--
-- > autoTabulate RowMajor (Right 6) $ map ascii $ enumerateVennDiagrams [2,3,3]
--
enumerateVennDiagrams :: [Int] -> [VennDiagram Int]
enumerateVennDiagrams dims = 
  case dims of
    []     -> []
    [d]    -> venns1 d
    (d:ds) -> concatMap (worker (length ds) d) $ enumerateVennDiagrams ds
  where

    worker !n !d (VennDiagram table) = result where

      list   = Map.toList table
      falses = replicate n False

      comps k = compositions' (map snd list) k
      result = 
        [ unsafeMakeVennDiagram $ 
            [ (False:tfs    , m-c) | ((tfs,m),c) <- zip list comp ] ++
            [ (True :tfs    ,   c) | ((tfs,m),c) <- zip list comp ] ++
            [ (True :falses , d-k) ]
        | k <- [0..d]
        , comp <- comps k
        ]

    venns1 :: Int -> [VennDiagram Int]
    venns1 p = [ theVenn ] where 
      theVenn = unsafeMakeVennDiagram [ ([True],p) ] 

--------------------------------------------------------------------------------

{-

-- | for testing only
venns2 :: Int -> Int -> [Venn Int]
venns2 p q = 
  [ mkVenn [ ([t,f],p-k) , ([f,t],q-k) , ([t,t],k) ]
  | k <- [0..min p q] 
  ]
  where
    t = True
    f = False
-}
