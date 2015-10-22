
-- | Thompson's group F.
--
-- See eg. <https://en.wikipedia.org/wiki/Thompson_groups>
--
-- Based mainly on James Michael Belk's PhD thesis \"THOMPSON'S GROUP F\";
-- see <http://www.math.u-psud.fr/~breuilla/Belk.pdf>
--

{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, BangPatterns, PatternSynonyms, DeriveFunctor #-}
module Math.Combinat.Groups.Thompson.F where

--------------------------------------------------------------------------------

import Data.List

import Math.Combinat.Classes
import Math.Combinat.ASCII

import Math.Combinat.Trees.Binary ( BinTree )
import qualified Math.Combinat.Trees.Binary as B

--------------------------------------------------------------------------------
-- * Tree diagrams

-- | A tree diagram, consisting of two binary trees with the same number of leaves, 
-- representing an element of the group F.
data TDiag = TDiag 
  { _width  :: !Int      -- ^ the width is the number of leaves, minus 1, of both diagrams
  , _domain :: !T        -- ^ the top diagram correspond to the /domain/
  , _range  :: !T        -- ^ the bottom diagram corresponds to the /range/
  }
  deriving (Eq,Ord,Show)

instance DrawASCII TDiag where
  ascii = asciiTDiag

instance HasWidth TDiag where
  width = _width

-- | Creates a tree diagram from two trees
mkTDiag :: T -> T -> TDiag 
mkTDiag d1 d2 = reduce $ mkTDiagDontReduce d1 d2

-- | Creates a tree diagram, but does not reduce it.
mkTDiagDontReduce :: T -> T -> TDiag 
mkTDiagDontReduce top bot = 
  if w1 == w2 
    then TDiag w1 top bot 
    else error "mkTDiag: widths do not match"
  where
    w1 = treeWidth top 
    w2 = treeWidth bot


isValidTDiag :: TDiag -> Bool
isValidTDiag (TDiag w top bot) = (treeWidth top == w && treeWidth bot == w)

isPositive :: TDiag -> Bool
isPositive (TDiag w top bot) = (bot == rightVine w)

isReduced :: TDiag -> Bool
isReduced diag = (reduce diag == diag)

-- | The generator x0
x0 :: TDiag
x0 = TDiag 2 top bot where
  top = branch caret leaf
  bot = branch leaf  caret

-- | The generator x1
x1 :: TDiag
x1 = xk 1

-- | The generators x0, x1, x2 ...
xk :: Int -> TDiag
xk = go where
  go k | k< 0      = error "xk: negative indexed generator"
       | k==0      = x0
       | otherwise = let TDiag _ t b = go (k-1) 
                     in  TDiag (k+2) (branch leaf t) (branch leaf b)

-- | The identity element in the group F                     
identity :: TDiag
identity = TDiag 0 Lf Lf

-- | A /positive diagram/ is a diagram whose bottom tree (the range) is a right vine.
positive :: T -> TDiag
positive t = TDiag w t (rightVine w) where w = treeWidth t

-- | Swaps the top and bottom of a tree diagram. This is the inverse in the group F.
-- (Note: we don't do reduction here, as this operation keeps the reducedness)
inverse :: TDiag -> TDiag
inverse (TDiag w top bot) = TDiag w bot top

-- | Decides whether two (possibly unreduced) tree diagrams represents the same group element in F.
equivalent :: TDiag -> TDiag -> Bool
equivalent diag1 diag2 = (identity == reduce (compose diag1 (inverse diag2)))

--------------------------------------------------------------------------------
-- * Reduction of tree diagrams

-- | Reduces a diagram. The result is a normal form of an element in the group F.
reduce :: TDiag -> TDiag
reduce = worker where

  worker :: TDiag -> TDiag
  worker diag = case step diag of
    Nothing    -> diag
    Just diag' -> worker diag'

  step :: TDiag -> Maybe TDiag
  step (TDiag w top bot) = 
    if null idxs 
      then Nothing
      else Just $ TDiag w' top' bot'
    where
      cs1  = treeCaretList top
      cs2  = treeCaretList bot
      idxs = sortedIntersect cs1 cs2
      w'   = w - length idxs
      top' = removeCarets idxs top
      bot' = removeCarets idxs bot

  -- | Intersects sorted lists      
  sortedIntersect :: [Int] -> [Int] -> [Int]
  sortedIntersect = go where
    go [] _  = []
    go _  [] = []
    go xxs@(x:xs) yys@(y:ys) = case compare x y of
      LT ->     go  xs yys
      EQ -> x : go  xs  ys
      GT ->     go xxs  ys

-- | List of carets at the bottom of the tree, indexed by their left edge position
treeCaretList :: T -> [Int]
treeCaretList = snd . go 0 where
  go !x t = case t of 
    Lf        ->  (x+1 , []  )
    Ct        ->  (x+2 , [x] )
    Br t1 t2  ->  (x2  , cs1++cs2) where
      (x1 , cs1) = go x  t1
      (x2 , cs2) = go x1 t2

-- | Remove the carets with the given indices 
-- (throws an error if there is no caret at the given index)
removeCarets :: [Int] -> T -> T
removeCarets idxs tree = if null rem then final else error ("removeCarets: some stuff remained: " ++ show rem) where

  (_,rem,final) =  go 0 idxs tree where

  go :: Int -> [Int] -> T -> (Int,[Int],T)
  go !x []         t  = (x + treeWidth t , [] , t)
  go !x iis@(i:is) t  = case t of
    Lf        ->  (x+1 , iis , t)
    Ct        ->  if x==i then (x+2 , is , Lf) else (x+2 , iis , Ct)
    Br t1 t2  ->  (x2  , iis2 , Br t1' t2') where
      (x1 , iis1 , t1') = go x  iis  t1
      (x2 , iis2 , t2') = go x1 iis1 t2
      
--------------------------------------------------------------------------------
-- * Composition of tree diagrams

-- | If @diag1@ corresponds to the PL function @f@, and @diag2@ to @g@, then @compose diag1 diag2@ 
-- will correspond to @(g.f)@ (note that the order is opposite than normal function composition!)
--
-- This is the multiplication in the group F.
--
compose :: TDiag -> TDiag -> TDiag
compose d1 d2 = reduce (composeDontReduce d1 d2)

-- | Compose two tree diagrams without reducing the result
composeDontReduce :: TDiag -> TDiag -> TDiag
composeDontReduce (TDiag w1 top1 bot1) (TDiag w2 top2 bot2) = new where
  new = mkTDiagDontReduce top' bot' 
  (list1,list2) = extensionToCommonTree bot1 top2
  top' = listGraft list1 top1
  bot' = listGraft list2 bot2

-- | Given two binary trees, we return a pair of list of subtrees which, grafted the to leaves of
-- the first (resp. the second) tree, results in the same extended tree.
extensionToCommonTree :: T -> T -> ([T],[T])
extensionToCommonTree t1 t2 = snd $ go (0,0) (t1,t2) where
  go (!x1,!x2) (!t1,!t2) = 
    case (t1,t2) of
      ( Lf       , Lf       ) -> ( (x1+n1 , x2+n2 ) , (             [Lf] ,             [Lf] ) )
      ( Lf       , Br _  _  ) -> ( (x1+n1 , x2+n2 ) , (             [t2] , replicate n2 Lf  ) )
      ( Br _  _  , Lf       ) -> ( (x1+n1 , x2+n2 ) , ( replicate n1 Lf  ,             [t1] ) )
      ( Br l1 r1 , Br l2 r2 ) 
        -> let ( (x1' ,x2' ) , (ps1,ps2) ) = go (x1 ,x2 ) (l1,l2)
               ( (x1'',x2'') , (qs1,qs2) ) = go (x1',x2') (r1,r2)
           in  ( (x1'',x2'') , (ps1++qs1, ps2++qs2) )
    where
      n1 = numberOfLeaves t1
      n2 = numberOfLeaves t2

--------------------------------------------------------------------------------
-- * Subdivions

-- | Returns the list of dyadic subdivision points
subdivision1 :: T -> [Rational]
subdivision1 = go 0 1 where
  go !a !b t = case t of
    Leaf   _   -> [a,b]
    Branch l r -> go a c l ++ tail (go c b r) where c = (a+b)/2

-- | Returns the list of dyadic intervals
subdivision2 :: T -> [(Rational,Rational)]
subdivision2 = go 0 1 where
  go !a !b t = case t of
    Leaf   _   -> [(a,b)]
    Branch l r -> go a c l ++ go c b r where c = (a+b)/2


--------------------------------------------------------------------------------
-- * Binary trees

-- | A (strict) binary tree with labelled leaves (but unlabelled nodes)
data Tree a
  = Branch !(Tree a) !(Tree a)
  | Leaf   !a
  deriving (Eq,Ord,Show,Functor)

-- | The monadic join operation of binary trees
graft :: Tree (Tree a) -> Tree a
graft = go where
  go (Branch l r) = Branch (go l) (go r)
  go (Leaf   t  ) = t 

-- | A list version of 'graft'
listGraft :: [Tree a] -> Tree b -> Tree a
listGraft subs big = snd $ go subs big where  
  go ggs@(g:gs) t = case t of
    Leaf   _   -> (gs,g)
    Branch l r -> (gs2, Branch l' r') where
                    (gs1,l') = go ggs l
                    (gs2,r') = go gs1 r

-- | A completely unlabelled binary tree
type T = Tree ()

instance DrawASCII T where
  ascii = asciiT 

instance HasNumberOfLeaves (Tree a) where
  numberOfLeaves = treeNumberOfLeaves

instance HasWidth (Tree a) where
  width = treeWidth

leaf :: T
leaf = Leaf ()

branch :: T -> T -> T
branch = Branch

caret :: T
caret = branch leaf leaf

treeNumberOfLeaves :: Tree a -> Int
treeNumberOfLeaves = go where
  go (Branch l r) = go l + go r
  go (Leaf   _  ) = 1  

-- | The width of the tree is the number of leaves minus 1.
treeWidth :: Tree a -> Int
treeWidth t = numberOfLeaves t - 1

-- | Enumerates the leaves a tree, starting from 0
enumerate_ :: Tree a -> Tree Int
enumerate_ = snd . enumerate

-- | Enumerates the leaves a tree, and also returns the number of leaves
enumerate :: Tree a -> (Int, Tree Int)
enumerate = go 0 where
  go !k t = case t of
    Leaf   _   -> (k+1 , Leaf k)
    Branch l r -> let (k' ,l') = go k  l
                      (k'',r') = go k' r
                  in (k'', Branch l' r') 

-- | \"Right vine\" of the given width 
rightVine :: Int -> T
rightVine k 
  | k< 0      = error "rightVine: negative width"
  | k==0      = leaf
  | otherwise = branch leaf (rightVine (k-1))

-- | \"Left vine\" of the given width 
leftVine :: Int -> T
leftVine k 
  | k< 0      = error "leftVine: negative width"
  | k==0      = leaf
  | otherwise = branch (leftVine (k-1)) leaf 

-- | Flips each node of a binary tree
flipTree :: Tree a -> Tree a
flipTree = go where
  go t = case t of
    Leaf   _   -> t
    Branch l r -> Branch (go r) (go l)

--------------------------------------------------------------------------------
-- * Conversion to\/from BinTree

-- | 'Tree' and 'BinTree' are the same type, except that 'Tree' is strict.
--
-- TODO: maybe unify these two types? Until that, you can convert between the two
-- with these functions if necessary.
--
toBinTree :: Tree a -> B.BinTree a
toBinTree = go where
  go (Branch l r) = B.Branch (go l) (go r)
  go (Leaf   y  ) = B.Leaf   y

fromBinTree :: B.BinTree a -> Tree a 
fromBinTree = go where
  go (B.Branch l r) = Branch (go l) (go r)
  go (B.Leaf   y  ) = Leaf   y
    
--------------------------------------------------------------------------------
-- * Pattern synonyms

pattern Lf     = Leaf ()
pattern Br l r = Branch l r
pattern Ct     = Br Lf Lf
pattern X0     = TDiag 2        (Br Ct Lf)         (Br Lf Ct)
pattern X1     = TDiag 3 (Br Lf (Br Ct Lf)) (Br Lf (Br Lf Ct))

--------------------------------------------------------------------------------
-- * ASCII

-- | Draws a binary tree, with all leaves at the same (bottom) row
asciiT :: T -> ASCII
asciiT = asciiT' False

-- | Draws a binary tree; when the boolean flag is @True@, we draw upside down
asciiT' :: Bool -> T -> ASCII
asciiT' inv = go where

  go t = case t of
    Leaf _                   -> emptyRect 
    Branch l r -> 
      if yl >= yr
        then pasteOnto (yl+yr+1,if inv then yr else 0) (rs $ yl+1) $ 
               vcat HCenter 
                 (bc $ yr+1) 
                 (hcat bot al ar)
        else pasteOnto (yl, if inv then yl else 0) (ls $ yr+1) $
               vcat HCenter 
                 (bc $ yl+1) 
                 (hcat bot al ar)
      where
        al = go l
        ar = go r
        yl = asciiYSize al 
        yr = asciiYSize ar 

  bot = if inv then VTop else VBottom
  hcat align p q = hCatWith align (HSepString "  ") [p,q]
  vcat align p q = vCatWith align VSepEmpty $ if inv then [q,p] else [p,q]
  bc = if inv then asciiBigInvCaret   else asciiBigCaret
  ls = if inv then asciiBigRightSlope else asciiBigLeftSlope
  rs = if inv then asciiBigLeftSlope  else asciiBigRightSlope

  asciiBigCaret :: Int -> ASCII
  asciiBigCaret k = hCatWith VTop HSepEmpty [ asciiBigLeftSlope k , asciiBigRightSlope k ]

  asciiBigInvCaret :: Int -> ASCII
  asciiBigInvCaret k = hCatWith VTop HSepEmpty [ asciiBigRightSlope k , asciiBigLeftSlope k ]

  asciiBigLeftSlope :: Int -> ASCII  
  asciiBigLeftSlope k = if k>0 
    then asciiFromLines [ replicate l ' ' ++ "/" | l<-[k-1,k-2..0] ]
    else emptyRect

  asciiBigRightSlope :: Int -> ASCII  
  asciiBigRightSlope k = if k>0 
    then asciiFromLines [ replicate l ' ' ++ "\\" | l<-[0..k-1] ]
    else emptyRect
  
-- | Draws a binary tree, with all leaves at the same (bottom) row, and labelling
-- the leaves starting with 0 (continuing with letters after 9)
asciiTLabels :: T -> ASCII
asciiTLabels = asciiTLabels' False

-- | When the flag is true, we draw upside down
asciiTLabels' :: Bool -> T -> ASCII
asciiTLabels' inv t = 
  if inv 
    then vCatWith HLeft VSepEmpty [ labels , asciiT' inv t ]
    else vCatWith HLeft VSepEmpty [ asciiT' inv t , labels ]
  where
    w = treeWidth t
    labels = asciiFromString $ intersperse ' ' $ take (w+1) allLabels
    allLabels = ['0'..'9'] ++ ['a'..'z']
    
-- | Draws a tree diagram
asciiTDiag :: TDiag -> ASCII
asciiTDiag (TDiag _ top bot) = vCatWith HLeft (VSepString " ") [asciiT' False top , asciiT' True bot]

--------------------------------------------------------------------------------


