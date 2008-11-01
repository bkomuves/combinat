
-- | Trees, forests, etc. See:
--   Donald E. Knuth: The Art of Computer Programming, vol 4, pre-fascicle 4A.

module Math.Combinat.Trees 
  ( -- * Types
    BinTree(..)
  , leaf
  , module Data.Tree 
  , Paren(..)
  , parenthesesToString
  , stringToParentheses
    -- * Bijections
  , forestToNestedParentheses
  , forestToBinaryTree
  , nestedParenthesesToForest
  , nestedParenthesesToForestUnsafe
  , nestedParenthesesToBinaryTree
  , nestedParenthesesToBinaryTreeUnsafe
  , binaryTreeToForest
  , binaryTreeToNestedParentheses
    -- * Nested parentheses
  , nestedParentheses 
  , fasc4A_algorithm_P
    -- * Binary trees
  , binaryTrees
  , countBinaryTrees
  , binaryTreesNaive
  ) 
  where

import Data.List
import Data.Tree (Tree(..),Forest(..))

import Math.Combinat.Helper

-------------------------------------------------------
-- * Types

data BinTree a
  = Branch (BinTree a) (BinTree a)
  | Leaf a
  deriving (Eq,Ord,Show,Read)

leaf :: BinTree ()
leaf = Leaf ()

-------------------------------------------------------

data Paren = LeftParen | RightParen deriving (Eq,Ord,Show,Read)

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

-------------------------------------------------------
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

-------------------------------------------------------
-- * Nested parentheses

-- | Synonym for 'fasc4A_algorithm_P'.
nestedParentheses :: Int -> [[Paren]]
nestedParentheses = fasc4A_algorithm_P

-- | Generates all sequences of nested parentheses of length 2n.
-- Order is lexigraphic (when right parentheses are considered 
-- smaller then left ones).
-- Based on \"Algorithm P\" in Knuth, but less efficient because of
-- the \"idiomatic\" code.
fasc4A_algorithm_P :: Int -> [[Paren]]
fasc4A_algorithm_P 0 = []
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

  findj :: ([Paren],[Paren]) -> ([Paren],[Paren]) -> Maybe ([Paren],[Paren])
  findj ( [] , _ ) _ = Nothing
  findj ( lls@(l:ls) , rs) ( xs , ys ) = 
    {- debug ((reverse ls,l,rs),(reverse xs,ys)) $ -}
    case l of
	    LeftParen  -> case xs of
	      (a:_:as) -> findj ( ls, RightParen:rs ) ( as , LeftParen:a:ys )
	      _ -> findj ( lls, [] ) ( reverse rs ++ xs , ys) 
	    RightParen -> Just ( reverse ys ++ xs ++ reverse (LeftParen:rs) ++ ls , [] )
    

-------------------------------------------------------
-- * Binary trees

-- | Generates all binary trees with n nodes. 
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

----- binary tree zipper

data Ctx a
  = Top 
  | L (Ctx a) (BinTree a)
  | R (BinTree a) (Ctx a) 

type Loc a = (BinTree a, Ctx a)

left :: Loc a -> Loc a
left (Branch l r , c) = (l , L c r)
left (Leaf _ , _) = error "left: Leaf"

right :: Loc a -> Loc a
right (Branch l r , c) = (r , R l c)
right (Leaf _ , _) = error "right: Leaf"
 
top :: BinTree a -> Loc a
top t = (t, Top)
 
up :: Loc a -> Loc a
up (t, L c r) = (Branch t r, c)
up (t, R l c) = (Branch l t, c)
up (t, Top  ) = error "up: top"

upmost :: Loc a -> Loc a
upmost l@(t, Top) = l
upmost l = upmost (up l)
 
modify :: (BinTree a -> BinTree a) -> Loc a -> Loc a
modify f (t, c) = (f t, c)

-----

{-
-- | Generates all binary trees with n nodes.
-- Based on \"Algorithm B\" in Knuth, uses tree zippers.
fasc4A_algorithm_B	:: Int -> [BinTree ()]
fasc4A_algorithm_B 0 = [ leaf ]
fasc4A_algorithm_B n = unfold1 next start where
  start = nest n (\t -> Branch t leaf) leaf

  killLeft  (Branch _ r) = Branch leaf r
  killRight (Branch l _) = Branch l leaf
  
  next t = case findj (top t) of
    Nothing -> Nothing
    Just locj@(s,c) -> case findk (top s) of
      lock@(u,Top) -> Just $ promote (modify killLeft locj ) lock 
      lock@(u,_  ) -> Just $ promote locj (modify killRight lock)
      
  findj :: Loc () -> Maybe (Loc ())
  findj (Branch (Leaf _) t , c) = case t of
    Branch l r -> findj $ left (Branch t leaf , c) 
    Leaf _ -> Nothing
  findj loc@(Leaf _ , c) = Just loc

  findk :: Loc () -> Loc ()
  findk loc@( Branch l (Leaf _) , _) = loc
  findk loc@( Branch l r , _) = findk (right loc)
  
  promote :: Loc () -> Loc () -> BinTree ()
  promote locj lock = undefined
-}
