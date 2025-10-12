
-- | Type classes for some common properties shared by different objects

{-# LANGUAGE FunctionalDependencies #-}
module Math.Combinat.Classes where

--------------------------------------------------------------------------------

-- | Emptyness
class CanBeEmpty a where
  isEmpty :: a -> Bool
  empty   :: a

--------------------------------------------------------------------------------
-- * Partitions

-- | Number of parts
class HasNumberOfParts a where
  numberOfParts :: a -> Int

--------------------------------------------------------------------------------

class HasHeight a where
  height :: a -> Int

class HasWidth a where
  width :: a -> Int

heightWidth :: (HasHeight a, HasWidth a) => a -> (Int,Int)
heightWidth x = (height x, width x)

--------------------------------------------------------------------------------

-- | Weight (of partitions, tableaux, etc)
class HasWeight a where
  weight :: a -> Int

--------------------------------------------------------------------------------

-- | Duality (of partitions, tableaux, etc)
class HasDuality a where
  dual :: a -> a

--------------------------------------------------------------------------------
-- * Tableau

-- | Shape (of tableaux, skew tableaux)
class HasShape a s | a -> s where
  shape :: a -> s

--------------------------------------------------------------------------------
-- * Trees

-- | Number of nodes (of trees)
class HasNumberOfNodes t where
  numberOfNodes :: t -> Int

-- | Number of leaves (of trees)
class HasNumberOfLeaves t where
  numberOfLeaves :: t -> Int

--------------------------------------------------------------------------------
-- * Permutations

-- | Number of cycles (of partitions)
class HasNumberOfCycles p where
  numberOfCycles :: p -> Int

--------------------------------------------------------------------------------
