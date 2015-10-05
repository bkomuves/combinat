
-- | N-ary trees.

{-# LANGUAGE FlexibleInstances, TypeSynonymInstances #-}
module Math.Combinat.Trees.Nary 
  (      
    -- * Types
    module Data.Tree
  , Tree(..)
    -- * Regular trees  
  , ternaryTrees
  , regularNaryTrees
  , semiRegularTrees
  , countTernaryTrees
  , countRegularNaryTrees
    -- * \"derivation trees\"
  , derivTrees
    -- * ASCII drawings
  , asciiTreeVertical_
  , asciiTreeVertical
  , asciiTreeVerticalLeavesOnly
    -- * Graphviz drawing
  , Dot
  , graphvizDotTree  
  , graphvizDotForest
    -- * Classifying nodes
  , classifyTreeNode
  , isTreeLeaf  , isTreeNode
  , isTreeLeaf_ , isTreeNode_
  , treeNodeNumberOfChildren 
    -- * Counting nodes
  , countTreeNodes
  , countTreeLeaves
  , countTreeLabelsWith
  , countTreeNodesWith 
    -- * Left and right spines
  , leftSpine  , leftSpine_
  , rightSpine , rightSpine_
  , leftSpineLength , rightSpineLength
    -- * Unique labels
  , addUniqueLabelsTree
  , addUniqueLabelsForest
  , addUniqueLabelsTree_
  , addUniqueLabelsForest_
    -- * Labelling by depth
  , labelDepthTree
  , labelDepthForest
  , labelDepthTree_
  , labelDepthForest_
    -- * Labelling by number of children
  , labelNChildrenTree
  , labelNChildrenForest
  , labelNChildrenTree_
  , labelNChildrenForest_
    
  ) where


--------------------------------------------------------------------------------

import Data.Tree
import Data.List

import Control.Applicative

--import Control.Monad.State
import Control.Monad.Trans.State
import Data.Traversable (traverse)

import Math.Combinat.Sets                  ( listTensor )
import Math.Combinat.Partitions.Multiset   ( partitionMultiset )
import Math.Combinat.Compositions          ( compositions )
import Math.Combinat.Numbers               ( factorial, binomial )

import Math.Combinat.Trees.Graphviz ( Dot , graphvizDotForest , graphvizDotTree )

import Math.Combinat.Classes
import Math.Combinat.ASCII as ASCII
import Math.Combinat.Helper

--------------------------------------------------------------------------------

instance HasNumberOfNodes (Tree a) where
  numberOfNodes = go where
    go (Node label subforest) = if null subforest 
      then 0 
      else 1 + sum' (map go subforest)

instance HasNumberOfLeaves (Tree a) where
  numberOfLeaves = go where
    go (Node label subforest) = if null subforest 
      then 1
      else sum' (map go subforest)

--------------------------------------------------------------------------------

-- | @regularNaryTrees d n@ returns the list of (rooted) trees on @n@ nodes where each
-- node has exactly @d@ children. Note that the leaves do not count in @n@.
-- Naive algorithm.
regularNaryTrees 
  :: Int         -- ^ degree = number of children of each node
  -> Int         -- ^ number of nodes
  -> [Tree ()]
regularNaryTrees d = go where
  go 0 = [ Node () [] ]
  go n = [ Node () cs
         | is <- compositions d (n-1) 
         , cs <- listTensor [ go i | i<-is ] 
         ]
  
-- | Ternary trees on @n@ nodes (synonym for @regularNaryTrees 3@)
ternaryTrees :: Int -> [Tree ()]  
ternaryTrees = regularNaryTrees 3

-- | We have 
--
-- > length (regularNaryTrees d n) == countRegularNaryTrees d n == \frac {1} {(d-1)n+1} \binom {dn} {n} 
--
countRegularNaryTrees :: (Integral a, Integral b) => a -> b -> Integer
countRegularNaryTrees d n = binomial (dd*nn) nn `div` ((dd-1)*nn+1) where
  dd = fromIntegral d :: Integer
  nn = fromIntegral n :: Integer 

-- | @\# = \\frac {1} {(2n+1} \\binom {3n} {n}@
countTernaryTrees :: Integral a => a -> Integer  
countTernaryTrees = countRegularNaryTrees (3::Int)

--------------------------------------------------------------------------------

-- | All trees on @n@ nodes where the number of children of all nodes is
-- in element of the given set. Example:
--
-- > autoTabulate RowMajor (Right 5) $ map asciiTreeVertical 
-- >                                 $ map labelNChildrenTree_ 
-- >                                 $ semiRegularTrees [2,3] 2
-- >
-- > [ length $ semiRegularTrees [2,3] n | n<-[0..] ] == [1,2,10,66,498,4066,34970,312066,2862562,26824386,...]
--
-- The latter sequence is A027307 in OEIS: <https://oeis.org/A027307>
--
-- Remark: clearly, we have
--
-- > semiRegularTrees [d] n == regularNaryTrees d n
--
-- 
semiRegularTrees 
  :: [Int]         -- ^ set of allowed number of children
  -> Int           -- ^ number of nodes
  -> [Tree ()]
semiRegularTrees []    n = if n==0 then [Node () []] else []
semiRegularTrees dset_ n = 
  if head dset >=1 
    then go n
    else error "semiRegularTrees: expecting a list of positive integers"
  where
    dset = map head $ group $ sort $ dset_
    
    go 0 = [ Node () [] ]
    go n = [ Node () cs
           | d <- dset
           , is <- compositions d (n-1) 
           , cs <- listTensor [ go i | i<-is ]
           ]
           
{- 

NOTES:

A006318 = [ length $ semiRegularTrees [1,2] n | n<-[0..] ] == [1,2,6,22,90,394,1806,8558,41586,206098,1037718.. ]
??      = [ length $ semiRegularTrees [1,3] n | n<-[0..] ] == [1,2,8,44,280,1936,14128,107088,834912,6652608 .. ]
??      = [ length $ semiRegularTrees [1,4] n | n<-[0..] ] == [1,2,10,74,642,6082,60970,635818,6826690

A027307 = [ length $ semiRegularTrees [2,3] n | n<-[0..] ] == [1,2,10,66,498,4066,34970,312066,2862562,26824386,...]
A219534 = [ length $ semiRegularTrees [2,4] n | n<-[0..] ] == [1,2,12,100,968,10208,113792,1318832 ..]
??      = [ length $ semiRegularTrees [2,5] n | n<-[0..] ] == [1,2,14,142,1690,21994,303126,4348102 ..]

A144097 = [ length $ semiRegularTrees [3,4] n | n<-[0..] ] == [1,2,14,134,1482,17818,226214,2984206,40503890..]

A107708 = [ length $ semiRegularTrees [1,2,3]   n | n<-[0..] ] == [1,3,18,144,1323,13176,138348,1507977 .. ]
??      = [ length $ semiRegularTrees [1,2,3,4] n | n<-[0..] ] == [1,4,40,560,9120,161856,3036800,59242240 .. ] 

-}
             
--------------------------------------------------------------------------------

-- | Vertical ASCII drawing of a tree, without labels. Example:
--
-- > autoTabulate RowMajor (Right 5) $ map asciiTreeVertical_ $ regularNaryTrees 2 4 
--
-- Nodes are denoted by @\@@, leaves by @*@.
--
asciiTreeVertical_ :: Tree a -> ASCII
asciiTreeVertical_ tree = ASCII.asciiFromLines (go tree) where
  go :: Tree b -> [String]
  go (Node _ cs) = case cs of
    [] -> ["-*"]
    _  -> concat $ mapWithFirstLast f $ map go cs
    
  f :: Bool -> Bool -> [String] -> [String] 
  f bf bl (l:ls) = let indent = if bl           then "  "  else  "| "
                       gap    = if bl           then []    else ["| "]
                       branch = if bl && not bf 
                                  then "\\-" 
                                  else if bf then "@-"
                                             else "+-"
                   in  (branch++l) : map (indent++) ls ++ gap

instance DrawASCII (Tree ()) where
  ascii = asciiTreeVertical_

-- | Prints all labels. Example:
-- 
-- > asciiTreeVertical $ addUniqueLabelsTree_ $ (regularNaryTrees 3 9) !! 666
--
-- Nodes are denoted by @(label)@, leaves by @label@.
--
asciiTreeVertical :: Show a => Tree a -> ASCII
asciiTreeVertical tree = ASCII.asciiFromLines (go tree) where
  go :: Show b => Tree b -> [String]
  go (Node x cs) = case cs of
    [] -> ["-- " ++ show x]
    _  -> concat $ mapWithFirstLast (f (show x)) $ map go cs
    
  f :: String -> Bool -> Bool -> [String] -> [String] 
  f label bf bl (l:ls) =
        let spaces = (map (const ' ') label  ) 
            dashes = (map (const '-') spaces ) 
            indent = if bl then "  " ++spaces++"  " else  " |" ++ spaces ++ "  "
            gap    = if bl then []                  else [" |" ++ spaces ++ "  "]
            branch = if bl && not bf
                           then " \\"++dashes++"--" 
                           else if bf 
                             then "-(" ++ label  ++ ")-"
                             else " +" ++ dashes ++ "--"
        in  (branch++l) : map (indent++) ls ++ gap

-- | Prints the labels for the leaves, but not for the  nodes.
asciiTreeVerticalLeavesOnly :: Show a => Tree a -> ASCII
asciiTreeVerticalLeavesOnly tree = ASCII.asciiFromLines (go tree) where
  go :: Show b => Tree b -> [String]
  go (Node x cs) = case cs of
    [] -> ["- " ++ show x]
    _  -> concat $ mapWithFirstLast f $ map go cs
    
  f :: Bool -> Bool -> [String] -> [String] 
  f bf bl (l:ls) = let indent = if bl           then "  "  else  "| "
                       gap    = if bl           then []    else ["| "]
                       branch = if bl && not bf 
                                  then "\\-" 
                                  else if bf then "@-"
                                             else "+-"
                   in  (branch++l) : map (indent++) ls ++ gap
  
--------------------------------------------------------------------------------
  
-- | The leftmost spine (the second element of the pair is the leaf node)
leftSpine  :: Tree a -> ([a],a)
leftSpine = go where
  go (Node x cs) = case cs of
    [] -> ([],x)
    _  -> let (xs,y) = go (head cs) in (x:xs,y) 

rightSpine  :: Tree a -> ([a],a)
rightSpine = go where
  go (Node x cs) = case cs of
    [] -> ([],x)
    _  -> let (xs,y) = go (last cs) in (x:xs,y) 

-- | The leftmost spine without the leaf node
leftSpine_  :: Tree a -> [a]
leftSpine_ = go where
  go (Node x cs) = case cs of
    [] -> []
    _  -> x : go (head cs)

rightSpine_ :: Tree a -> [a] 
rightSpine_ = go where
  go (Node x cs) = case cs of
    [] -> []
    _  -> x : go (last cs) 

-- | The length (number of edges) on the left spine 
--
-- > leftSpineLength tree == length (leftSpine_ tree)
--
leftSpineLength  :: Tree a -> Int  
leftSpineLength = go 0 where
  go n (Node x cs) = case cs of
    [] -> n
    _  -> go (n+1) (head cs)
  
rightSpineLength :: Tree a -> Int  
rightSpineLength = go 0 where
  go n (Node x cs) = case cs of
    [] -> n
    _  -> go (n+1) (last cs)

--------------------------------------------------------------------------------

-- | 'Left' is leaf, 'Right' is node
classifyTreeNode :: Tree a -> Either a a
classifyTreeNode (Node x cs) = case cs of { [] -> Left x ; _ -> Right x }

isTreeLeaf :: Tree a -> Maybe a  
isTreeLeaf (Node x cs) = case cs of { [] -> Just x ; _ -> Nothing }  

isTreeNode :: Tree a -> Maybe a  
isTreeNode (Node x cs) = case cs of { [] -> Nothing ; _ -> Just x }  

isTreeLeaf_ :: Tree a -> Bool  
isTreeLeaf_ (Node x cs) = case cs of { [] -> True ; _ -> False }  
  
isTreeNode_ :: Tree a -> Bool  
isTreeNode_ (Node x cs) = case cs of { [] -> False ; _ -> True }  

treeNodeNumberOfChildren :: Tree a -> Int
treeNodeNumberOfChildren (Node _ cs) = length cs

--------------------------------------------------------------------------------
-- counting

countTreeNodes :: Tree a -> Int
countTreeNodes = go where
  go (Node x cs) = case cs of
    [] -> 0
    _  -> 1 + sum (map go cs)

countTreeLeaves :: Tree a -> Int
countTreeLeaves = go where
  go (Node x cs) = case cs of
    [] -> 1
    _  -> sum (map go cs)

countTreeLabelsWith :: (a -> Bool) -> Tree a -> Int
countTreeLabelsWith f = go where
  go (Node label cs) = (if f label then 1 else 0) + sum (map go cs)

countTreeNodesWith :: (Tree a -> Bool) -> Tree a -> Int
countTreeNodesWith f = go where
  go node@(Node _ cs) = (if f node then 1 else 0) + sum (map go cs)

--------------------------------------------------------------------------------

-- | Adds unique labels to the nodes (including leaves) of a 'Tree'.
addUniqueLabelsTree :: Tree a -> Tree (a,Int) 
addUniqueLabelsTree tree = head (addUniqueLabelsForest [tree])

-- | Adds unique labels to the nodes (including leaves) of a 'Forest'
addUniqueLabelsForest :: Forest a -> Forest (a,Int) 
addUniqueLabelsForest forest = evalState (mapM globalAction forest) 1 where
  globalAction tree = 
    unwrapMonad $ traverse localAction tree 
  localAction x = WrapMonad $ do
    i <- get
    put (i+1)
    return (x,i)

addUniqueLabelsTree_ :: Tree a -> Tree Int
addUniqueLabelsTree_ = fmap snd . addUniqueLabelsTree  

addUniqueLabelsForest_ :: Forest a -> Forest Int
addUniqueLabelsForest_ = map (fmap snd) . addUniqueLabelsForest

--------------------------------------------------------------------------------
    
-- | Attaches the depth to each node. The depth of the root is 0. 
labelDepthTree :: Tree a -> Tree (a,Int) 
labelDepthTree tree = worker 0 tree where
  worker depth (Node label subtrees) = Node (label,depth) (map (worker (depth+1)) subtrees)

labelDepthForest :: Forest a -> Forest (a,Int) 
labelDepthForest forest = map labelDepthTree forest
    
labelDepthTree_ :: Tree a -> Tree Int
labelDepthTree_ = fmap snd . labelDepthTree

labelDepthForest_ :: Forest a -> Forest Int 
labelDepthForest_ = map (fmap snd) . labelDepthForest

--------------------------------------------------------------------------------

-- | Attaches the number of children to each node. 
labelNChildrenTree :: Tree a -> Tree (a,Int)
labelNChildrenTree (Node x subforest) = 
  Node (x, length subforest) (map labelNChildrenTree subforest)
  
labelNChildrenForest :: Forest a -> Forest (a,Int) 
labelNChildrenForest forest = map labelNChildrenTree forest

labelNChildrenTree_ :: Tree a -> Tree Int
labelNChildrenTree_ = fmap snd . labelNChildrenTree

labelNChildrenForest_ :: Forest a -> Forest Int 
labelNChildrenForest_ = map (fmap snd) . labelNChildrenForest
    
--------------------------------------------------------------------------------

-- | Computes the set of equivalence classes of rooted trees (in the 
-- sense that the leaves of a node are /unordered/) 
-- with @n = length ks@ leaves where the set of heights of 
-- the leaves matches the given set of numbers. 
-- The height is defined as the number of /edges/ from the leaf to the root. 
--
-- TODO: better name?
derivTrees :: [Int] -> [Tree ()]
derivTrees xs = derivTrees' (map (+1) xs)

derivTrees' :: [Int] -> [Tree ()]
derivTrees' [] = []
derivTrees' [n] = 
  if n>=1 
    then [unfoldTree f 1] 
    else [] 
  where 
    f k = if k<n then ((),[k+1]) else ((),[])
derivTrees' ks = 
  if and (map (>0) ks)
    then
      [ Node () sub 
      | part <- parts
      , let subtrees = map g part
      , sub <- listTensor subtrees 
      ] 
    else []
  where
    parts = partitionMultiset ks
    g xs = derivTrees' (map (\x->x-1) xs)

--------------------------------------------------------------------------------
    