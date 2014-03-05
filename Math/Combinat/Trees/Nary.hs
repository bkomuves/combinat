
-- | N-ary trees.

module Math.Combinat.Trees.Nary 
  (
    -- * regular trees 
    ternaryTrees
  , regularNaryTrees
  , countTernaryTrees
  , countRegularNaryTrees
    -- * derivation trees
  , derivTrees
    -- * ASCII drawings
  , printTreeVertical_
  , printTreeVertical
  , printTreeVerticalLeavesOnly
  , drawTreeVertical_
  , drawTreeVertical
  , drawTreeVerticalLeavesOnly
    -- * classifying nodes
  , classifyTreeNode
  , isTreeLeaf  , isTreeNode
  , isTreeLeaf_ , isTreeNode_
    -- * spines
  , leftSpine  , leftSpine_
  , rightSpine , rightSpine_
  , leftSpineLength , rightSpineLength
    -- * unique labels
  , addUniqueLabelsTree
  , addUniqueLabelsForest
  , addUniqueLabelsTree_
  , addUniqueLabelsForest_
    -- * labelling by depth
  , labelDepthTree
  , labelDepthForest
  , labelDepthTree_
  , labelDepthForest_
    -- * labelling by number of children
  , labelNChildrenTree
  , labelNChildrenForest
  , labelNChildrenTree_
  , labelNChildrenForest_
    
  ) where


--------------------------------------------------------------------------------

import Data.Tree

import Control.Applicative

--import Control.Monad.State
import Control.Monad.Trans.State
import Data.Traversable (traverse)

import Math.Combinat.Sets         (listTensor)
import Math.Combinat.Partitions   (partitionMultiset)
import Math.Combinat.Compositions (compositions)
import Math.Combinat.Numbers      (factorial,binomial)

import Math.Combinat.Helper

--------------------------------------------------------------------------------

-- | @regularNaryTrees d n@ returns the list of (rooted) trees on @n@ nodes where each
-- node has exactly @d$ children. Note that the leaves do not count in @n@.
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
-- > length (regularNaryTrees d n) == countRegularNaryTrees == binomial (dn) n / (1+(d-1)n)
--
countRegularNaryTrees :: (Integral a, Integral b) => a -> b -> Integer
countRegularNaryTrees d n = binomial (dd*nn) nn `div` ((dd-1)*nn+1) where
  dd = fromIntegral d :: Integer
  nn = fromIntegral n :: Integer 

countTernaryTrees :: Integral a => a -> Integer  
countTernaryTrees = countRegularNaryTrees (3::Int)

--------------------------------------------------------------------------------

-- | Vertical ASCII drawing of a tree, without labels.
-- 
-- Example:
--
-- > mapM_ printTreeVertical_ $ regularNaryTrees 2 3 
--
printTreeVertical_ :: Tree a -> IO ()
printTreeVertical_ = putStrLn . drawTreeVertical_

-- | Prints all labels.
--
-- Example: 
--
-- > printTreeVertical $ addUniqueLabelsTree_ $ (regularNaryTrees 3 9) !! 666
--
printTreeVertical :: Show a => Tree a -> IO ()
printTreeVertical = putStrLn . drawTreeVertical

-- | Prints the labels for the leaves, but not for the nonempty nodes
printTreeVerticalLeavesOnly :: Show a => Tree a -> IO ()
printTreeVerticalLeavesOnly = putStrLn . drawTreeVerticalLeavesOnly


drawTreeVertical_ :: Tree a -> String
drawTreeVertical_ tree = unlines (go tree) where
  go :: Tree b -> [String]
  go (Node _ cs) = case cs of
    [] -> ["o"]
    _  -> concat $ mapWithLast f $ map go cs
    
  f :: Bool -> [String] -> [String] 
  f b (l:ls) = let indent = if b then "  "  else  "| "
                   branch = if b then "\\-" else  "+-"
                   gap    = if b then []    else ["| "]
               in  (branch++l) : map (indent++) ls ++ gap

drawTreeVertical :: Show a => Tree a -> String
drawTreeVertical tree = unlines (go tree) where
  go :: Show b => Tree b -> [String]
  go (Node x cs) = case cs of
    [] -> ["-- " ++ show x]
    _  -> concat $ mapWithFirstLast (f (show x)) $ map go cs
    
  f :: String -> Bool -> Bool -> [String] -> [String] 
  f label bf bl (l:ls) =
        let spaces = (map (const ' ') label  ) 
            dashes = (map (const '-') spaces ) 
            indent = if bl then "  " ++spaces++"  " else " |" ++ spaces ++ "  "
            branch = if bl then " \\"++dashes++"--" 
                           else if bf 
                             then "-(" ++ label  ++ ")-"
                             else " +" ++ dashes ++ "--"
            gap    = if bl then []                  else [" |" ++ spaces ++ "  "]
        in  (branch++l) : map (indent++) ls ++ gap

drawTreeVerticalLeavesOnly :: Show a => Tree a -> String
drawTreeVerticalLeavesOnly tree = unlines (go tree) where
  go :: Show b => Tree b -> [String]
  go (Node x cs) = case cs of
    [] -> [" " ++ show x]
    _  -> concat $ mapWithLast f $ map go cs
    
  f :: Bool -> [String] -> [String] 
  f b (l:ls) = let indent = if b then "  "  else  "| "
                   branch = if b then "\\-" else  "+-"
                   gap    = if b then []    else ["| "]
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
    