
-- | Binary trees, forests, etc. See:
--   Donald E. Knuth: The Art of Computer Programming, vol 4, pre-fascicle 4A.
--
-- For example, here are all the binary trees on 4 nodes:
--
-- <<svg/bintrees.svg>>
--

{-# LANGUAGE FlexibleInstances, TypeSynonymInstances #-}
module Math.Combinat.Trees.Binary 
  ( -- * Types
    BinTree(..)
  , leaf 
  , graft
  , BinTree'(..)
  , forgetNodeDecorations
  , Paren(..)
  , parenthesesToString
  , stringToParentheses  
  , numberOfNodes
  , numberOfLeaves
    -- * Conversion to rose trees (@Data.Tree@)
  , toRoseTree , toRoseTree'
  , module Data.Tree 
    -- * Enumerate leaves
  , enumerateLeaves_ 
  , enumerateLeaves 
  , enumerateLeaves'
    -- * Nested parentheses
  , nestedParentheses 
  , randomNestedParentheses
  , nthNestedParentheses
  , countNestedParentheses
  , fasc4A_algorithm_P
  , fasc4A_algorithm_W
  , fasc4A_algorithm_U
    -- * Generating binary trees
  , binaryTrees
  , countBinaryTrees
  , binaryTreesNaive
  , randomBinaryTree
  , fasc4A_algorithm_R
    -- * ASCII drawing
  , asciiBinaryTree_
    -- * Graphviz drawing
  , Dot
  , graphvizDotBinTree
  , graphvizDotBinTree'
  , graphvizDotForest
  , graphvizDotTree  
    -- * Bijections
  , forestToNestedParentheses
  , forestToBinaryTree
  , nestedParenthesesToForest
  , nestedParenthesesToForestUnsafe
  , nestedParenthesesToBinaryTree
  , nestedParenthesesToBinaryTreeUnsafe
  , binaryTreeToForest
  , binaryTreeToNestedParentheses
  ) 
  where

--------------------------------------------------------------------------------

import Control.Applicative
import Control.Monad
import Control.Monad.ST

import Data.Array
import Data.Array.ST
import Data.Array.Unsafe

import Data.List
import Data.Tree (Tree(..),Forest(..))

import Data.Monoid
import Data.Foldable (Foldable(foldMap))
import Data.Traversable (Traversable(traverse))

import System.Random

import Math.Combinat.Numbers (factorial,binomial)

import Math.Combinat.Trees.Graphviz 
  ( Dot 
  , graphvizDotBinTree , graphvizDotBinTree' 
  , graphvizDotForest  , graphvizDotTree 
  )
import Math.Combinat.Classes
import Math.Combinat.Helper
import Math.Combinat.ASCII as ASCII

--------------------------------------------------------------------------------
-- * Types

-- | A binary tree with leaves decorated with type @a@.
data BinTree a
  = Branch (BinTree a) (BinTree a)
  | Leaf a
  deriving (Eq,Ord,Show,Read)

leaf :: BinTree ()
leaf = Leaf ()

-- | The monadic join operation of binary trees
graft :: BinTree (BinTree a) -> BinTree a
graft = go where
  go (Branch l r) = Branch (go l) (go r)
  go (Leaf   t  ) = t 

--------------------------------------------------------------------------------

-- | A binary tree with leaves and internal nodes decorated 
-- with types @a@ and @b@, respectively.
data BinTree' a b
  = Branch' (BinTree' a b) b (BinTree' a b)
  | Leaf' a
  deriving (Eq,Ord,Show,Read)

forgetNodeDecorations :: BinTree' a b -> BinTree a
forgetNodeDecorations = go where
  go (Branch' left _ right) = Branch (go left) (go right)
  go (Leaf'   decor       ) = Leaf decor 

--------------------------------------------------------------------------------

instance HasNumberOfNodes (BinTree a) where
  numberOfNodes = go where
    go (Leaf   _  ) = 0
    go (Branch l r) = go l + go r + 1

instance HasNumberOfLeaves (BinTree a) where
  numberOfLeaves = go where
    go (Leaf   _  ) = 1
    go (Branch l r) = go l + go r 


instance HasNumberOfNodes (BinTree' a b) where
  numberOfNodes = go where
    go (Leaf'   _    ) = 0
    go (Branch' l _ r) = go l + go r + 1

instance HasNumberOfLeaves (BinTree' a b) where
  numberOfLeaves = go where
    go (Leaf'   _    ) = 1
    go (Branch' l _ r) = go l + go r 

--------------------------------------------------------------------------------
-- * Enumerate leaves

-- | Enumerates the leaves a tree, starting from 0, ignoring old labels
enumerateLeaves_ :: BinTree a -> BinTree Int
enumerateLeaves_ = snd . go 0 where
  go !k t = case t of
    Leaf   _   -> (k+1 , Leaf k)
    Branch l r -> (k'', Branch l' r')  where
                    (k' ,l') = go k  l
                    (k'',r') = go k' r

-- | Enumerates the leaves a tree, starting from zero, and also returns the number of leaves
enumerateLeaves' :: BinTree a -> (Int, BinTree (a,Int))
enumerateLeaves' = go 0 where
  go !k t = case t of
    Leaf   y   -> (k+1 , Leaf (y,k))
    Branch l r -> (k'', Branch l' r')  where
                    (k' ,l') = go k  l
                    (k'',r') = go k' r

-- | Enumerates the leaves a tree, starting from zero
enumerateLeaves :: BinTree a -> BinTree (a,Int)
enumerateLeaves = snd . enumerateLeaves'

--------------------------------------------------------------------------------
-- * conversion to 'Data.Tree'

-- | Convert a binary tree to a rose tree (from "Data.Tree")
toRoseTree :: BinTree a -> Tree (Maybe a)
toRoseTree = go where
  go (Branch t1 t2) = Node Nothing  [go t1, go t2]
  go (Leaf x)       = Node (Just x) [] 

toRoseTree' :: BinTree' a b -> Tree (Either b a)
toRoseTree' = go where
  go (Branch' t1 y t2) = Node (Left  y) [go t1, go t2]
  go (Leaf' x)         = Node (Right x) [] 
  
--------------------------------------------------------------------------------
-- instances
  
instance Functor BinTree where
  fmap f = go where
    go (Branch left right) = Branch (go left) (go right)
    go (Leaf x) = Leaf (f x)
  
instance Foldable BinTree where
  foldMap f = go where
    go (Leaf x) = f x
    go (Branch left right) = (go left) `mappend` (go right)  

instance Traversable BinTree where
  traverse f = go where 
    go (Leaf x) = Leaf <$> f x
    go (Branch left right) = Branch <$> go left <*> go right

instance Applicative BinTree where
  pure    = Leaf
  u <*> t = go u where
    go (Branch l r) = Branch (go l) (go r)
    go (Leaf   f  ) = fmap f t

instance Monad BinTree where
  return    = Leaf
  (>>=) t f = go t where
    go (Branch l r) = Branch (go l) (go r)
    go (Leaf   y  ) = f y 

--------------------------------------------------------------------------------
-- * Nested parentheses

data Paren 
  = LeftParen 
  | RightParen 
  deriving (Eq,Ord,Show,Read)

parenToChar :: Paren -> Char
parenToChar LeftParen = '('
parenToChar RightParen = ')'

parenthesesToString :: [Paren] -> String
parenthesesToString = map parenToChar

stringToParentheses :: String -> [Paren]
stringToParentheses [] = []
stringToParentheses (x:xs) = p : stringToParentheses xs where
  p = case x of
    '(' -> LeftParen
    ')' -> RightParen
    _ -> error "stringToParentheses: invalid character"

--------------------------------------------------------------------------------
-- * Bijections

forestToNestedParentheses :: Forest a -> [Paren]
forestToNestedParentheses = forest where
  -- forest :: Forest a -> [Paren]
  forest = concatMap tree 
  -- tree :: Tree a -> [Paren]
  tree (Node _ sf) = LeftParen : forest sf ++ [RightParen]

forestToBinaryTree :: Forest a -> BinTree ()
forestToBinaryTree = forest where
  -- forest :: Forest a -> BinTree ()
  forest = foldr Branch leaf . map tree 
  -- tree :: Tree a -> BinTree ()
  tree (Node _ sf) = case sf of
    [] -> leaf
    _  -> forest sf 
   
nestedParenthesesToForest :: [Paren] -> Maybe (Forest ())
nestedParenthesesToForest ps = 
  case parseForest ps of 
    (rest,forest) -> case rest of
      [] -> Just forest
      _  -> Nothing
  where  
    parseForest :: [Paren] -> ( [Paren] , Forest () )
    parseForest ps = unfoldEither parseTree ps
    parseTree :: [Paren] -> Either [Paren] ( [Paren] , Tree () )  
    parseTree orig@(LeftParen:ps) = let (rest,ts) = parseForest ps in case rest of
      (RightParen:qs) -> Right (qs, Node () ts)
      _ -> Left orig
    parseTree qs = Left qs

nestedParenthesesToForestUnsafe :: [Paren] -> Forest ()
nestedParenthesesToForestUnsafe = fromJust . nestedParenthesesToForest

nestedParenthesesToBinaryTree :: [Paren] -> Maybe (BinTree ())
nestedParenthesesToBinaryTree ps = 
  case parseForest ps of 
    (rest,forest) -> case rest of
      [] -> Just forest
      _  -> Nothing
  where  
    parseForest :: [Paren] -> ( [Paren] , BinTree () )
    parseForest ps = let (rest,ts) = unfoldEither parseTree ps in (rest , foldr Branch leaf ts)
    parseTree :: [Paren] -> Either [Paren] ( [Paren] , BinTree () )  
    parseTree orig@(LeftParen:ps) = let (rest,ts) = parseForest ps in case rest of
      (RightParen:qs) -> Right (qs, ts)
      _ -> Left orig
    parseTree qs = Left qs
    
nestedParenthesesToBinaryTreeUnsafe :: [Paren] -> BinTree ()
nestedParenthesesToBinaryTreeUnsafe = fromJust . nestedParenthesesToBinaryTree

binaryTreeToNestedParentheses :: BinTree a -> [Paren]
binaryTreeToNestedParentheses = worker where
  worker (Branch l r) = LeftParen : worker l ++ RightParen : worker r
  worker (Leaf _) = []

binaryTreeToForest :: BinTree a -> Forest ()
binaryTreeToForest = worker where
  worker (Branch l r) = Node () (worker l) : worker r
  worker (Leaf _) = []

--------------------------------------------------------------------------------
-- * Nested parentheses

-- | Generates all sequences of nested parentheses of length @2n@ in
-- lexigraphic order.
-- 
-- Synonym for 'fasc4A_algorithm_P'.
--
nestedParentheses :: Int -> [[Paren]]
nestedParentheses = fasc4A_algorithm_P

-- | Synonym for 'fasc4A_algorithm_W'.
randomNestedParentheses :: RandomGen g => Int -> g -> ([Paren],g)
randomNestedParentheses = fasc4A_algorithm_W

-- | Synonym for 'fasc4A_algorithm_U'.
nthNestedParentheses :: Int -> Integer -> [Paren]
nthNestedParentheses = fasc4A_algorithm_U

countNestedParentheses :: Int -> Integer
countNestedParentheses = countBinaryTrees

-- | Generates all sequences of nested parentheses of length 2n.
-- Order is lexicographical (when right parentheses are considered 
-- smaller then left ones).
-- Based on \"Algorithm P\" in Knuth, but less efficient because of
-- the \"idiomatic\" code.
fasc4A_algorithm_P :: Int -> [[Paren]]
fasc4A_algorithm_P 0 = [[]]
fasc4A_algorithm_P 1 = [[LeftParen,RightParen]]
fasc4A_algorithm_P n = unfold next ( start , [] ) where 
  start = concat $ replicate n [RightParen,LeftParen]  -- already reversed!
   
  next :: ([Paren],[Paren]) -> ( [Paren] , Maybe ([Paren],[Paren]) )
  next ( (a:b:ls) , [] ) = next ( ls , b:a:[] )
  next ( lls@(l:ls) , rrs@(r:rs) ) = ( visit , new ) where
    visit = reverse lls ++ rrs
    new = 
      {- debug (reverse ls,l,r,rs) $ -} 
      case l of 
        RightParen -> Just ( ls , LeftParen:RightParen:rs )
        LeftParen  -> 
          {- debug ("---",reverse ls,l,r,rs) $ -}
          findj ( lls , [] ) ( reverse (RightParen:rs) , [] ) 
  next _ = error "fasc4A_algorithm_P: fatal error shouldn't happen"

  findj :: ([Paren],[Paren]) -> ([Paren],[Paren]) -> Maybe ([Paren],[Paren])
  findj ( [] , _ ) _ = Nothing
  findj ( lls@(l:ls) , rs) ( xs , ys ) = 
    {- debug ((reverse ls,l,rs),(reverse xs,ys)) $ -}
    case l of
      LeftParen  -> case xs of
        (a:_:as) -> findj ( ls, RightParen:rs ) ( as , LeftParen:a:ys )
        _ -> findj ( lls, [] ) ( reverse rs ++ xs , ys) 
      RightParen -> Just ( reverse ys ++ xs ++ reverse (LeftParen:rs) ++ ls , [] )
  findj _ _ = error "fasc4A_algorithm_P: fatal error shouldn't happen"
    
-- | Generates a uniformly random sequence of nested parentheses of length 2n.    
-- Based on \"Algorithm W\" in Knuth.
fasc4A_algorithm_W :: RandomGen g => Int -> g -> ([Paren],g)
fasc4A_algorithm_W n' rnd = worker (rnd,n,n,[]) where
  n = fromIntegral n' :: Integer  
  -- the numbers we use are of order n^2, so for n >> 2^16 
  -- on a 32 bit machine, we need big integers.
  worker :: RandomGen g => (g,Integer,Integer,[Paren]) -> ([Paren],g)
  worker (rnd,_,0,parens) = (parens,rnd)
  worker (rnd,p,q,parens) = 
    if x<(q+1)*(q-p) 
      then worker (rnd' , p   , q-1 , LeftParen :parens)
      else worker (rnd' , p-1 , q   , RightParen:parens)
    where 
      (x,rnd') = randomR ( 0 , (q+p)*(q-p+1)-1 ) rnd

-- | Nth sequence of nested parentheses of length 2n. 
-- The order is the same as in 'fasc4A_algorithm_P'.
-- Based on \"Algorithm U\" in Knuth.
fasc4A_algorithm_U 
  :: Int               -- ^ n
  -> Integer           -- ^ N; should satisfy 1 <= N <= C(n) 
  -> [Paren]
fasc4A_algorithm_U n' bign0 = reverse $ worker (bign0,c0,n,n,[]) where
  n = fromIntegral n' :: Integer
  c0 = foldl f 1 [2..n]  
  f c p = ((4*p-2)*c) `div` (p+1) 
  worker :: (Integer,Integer,Integer,Integer,[Paren]) -> [Paren]
  worker (_   ,_,_,0,parens) = parens
  worker (bign,c,p,q,parens) = 
    if bign <= c' 
      then worker (bign    , c'   , p   , q-1 , RightParen:parens)
      else worker (bign-c' , c-c' , p-1 , q   , LeftParen :parens)
    where
      c' = ((q+1)*(q-p)*c) `div` ((q+p)*(q-p+1))
  
--------------------------------------------------------------------------------
-- * Generating binary trees

-- | Generates all binary trees with @n@ nodes. 
--   At the moment just a synonym for 'binaryTreesNaive'.
binaryTrees :: Int -> [BinTree ()]
binaryTrees = binaryTreesNaive

-- | # = Catalan(n) = \\frac { 1 } { n+1 } \\binom { 2n } { n }.
--
-- This is also the counting function for forests and nested parentheses.
countBinaryTrees :: Int -> Integer
countBinaryTrees n = binomial (2*n) n `div` (1 + fromIntegral n)
    
-- | Generates all binary trees with n nodes. The naive algorithm.
binaryTreesNaive :: Int -> [BinTree ()]
binaryTreesNaive 0 = [ leaf ]
binaryTreesNaive n = 
  [ Branch l r 
  | i <- [0..n-1] 
  , l <- binaryTreesNaive i 
  , r <- binaryTreesNaive (n-1-i) 
  ]

-- | Generates an uniformly random binary tree, using 'fasc4A_algorithm_R'.
randomBinaryTree :: RandomGen g => Int -> g -> (BinTree (), g)
randomBinaryTree n rnd = (tree,rnd') where
  (decorated,rnd') = fasc4A_algorithm_R n rnd      
  tree = fmap (const ()) $ forgetNodeDecorations decorated

-- | Grows a uniformly random binary tree. 
-- \"Algorithm R\" (Remy's procudere) in Knuth.
-- Nodes are decorated with odd numbers, leaves with even numbers (from the
-- set @[0..2n]@). Uses mutable arrays internally.
fasc4A_algorithm_R :: RandomGen g => Int -> g -> (BinTree' Int Int, g)
fasc4A_algorithm_R n0 rnd = res where
  res = runST $ do
    ar <- newArray (0,2*n0) 0
    rnd' <- worker rnd 1 ar
    links <- Data.Array.Unsafe.unsafeFreeze ar
    return (toTree links, rnd')
  toTree links = f (links!0) where
    f i = if odd i 
      then Branch' (f $ links!i) i (f $ links!(i+1)) 
      else Leaf' i  
  worker :: RandomGen g => g -> Int -> STUArray s Int Int -> ST s g
  worker rnd n ar = do 
    if n > n0
      then return rnd
      else do
        writeArray ar (n2-b)   n2
        lk <- readArray ar k
        writeArray ar (n2-1+b) lk
        writeArray ar k        (n2-1)
        worker rnd' (n+1) ar      
    where  
      n2 = n+n
      (x,rnd') = randomR (0,4*n-3) rnd
      (k,b) = x `divMod` 2
      
--------------------------------------------------------------------------------      
-- * ASCII drawing  

-- | Draws a binary tree in ASCII, ignoring node labels.
--
-- Example:
--
-- > autoTabulate RowMajor (Right 5) $ map asciiBinaryTree_ $ binaryTrees 4
--
asciiBinaryTree_ :: BinTree a -> ASCII
asciiBinaryTree_ = ASCII.asciiFromLines . fst . go where

  go :: BinTree a -> ([String],Int)
  go (Leaf x) = ([],0)
  go (Branch t1 t2) = ( new , j1+m ) where
    (ls1,j1) = go t1
    (ls2,j2) = go t2
    w1 = blockWidth ls1
    w2 = blockWidth ls2
    m = max 1 $ (w1-j1+j2+2) `div` 2
    s = 2*m - (w1-j1+j2)
    spaces = [replicate s ' ']
    ls = hConcatLines [ ls1 , spaces , ls2 ]
    top = [ replicate (j1+m-i) ' ' ++ "/" ++ replicate (2*(i-1)) ' ' ++ "\\" | i<-[1..m] ]
    new = mkLinesUniformWidth $ vConcatLines [ top , ls ] 
        
  blockWidth ls = case ls of
    (l:_) -> length l
    []    -> 0

instance DrawASCII (BinTree ()) where
  ascii = asciiBinaryTree_ 

--------------------------------------------------------------------------------      
