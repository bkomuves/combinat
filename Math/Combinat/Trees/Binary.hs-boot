

module Math.Combinat.Trees.Binary where

--------------------------------------------------------------------------------

import Data.Tree ( Tree(..) , Forest(..) )

--------------------------------------------------------------------------------

-- | A binary tree with leaves decorated with type @a@.
data BinTree a
  = Branch (BinTree a) (BinTree a)
  | Leaf a

-- | A binary tree with leaves and internal nodes decorated 
-- with types @a@ and @b@, respectively.
data BinTree' a b
  = Branch' (BinTree' a b) b (BinTree' a b)
  | Leaf' a

--------------------------------------------------------------------------------