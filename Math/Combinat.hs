
-- | A collection of functions to generate combinatorial
-- objects like partitions, combinations, permutations,
-- Young tableaux, various trees, etc.
--
-- The long-term goals are 
--
--  (1) to be efficient; 
--
--  (2) to be able to enumerate the structures 
--      with constant memory usage. 
--
-- The short-term goal is to generate 
-- many interesting structures.
--
-- Naming conventions (subject to change): 
--
--  * prime suffix: additional constrains, typically more general;
--
--  * underscore prefix: use plain lists instead of other types with 
--    enforced invariants;
--
--  * \"count\" prefix: counting functions.

module Math.Combinat 
  ( module Math.Combinat.Tuples
  , module Math.Combinat.Combinations
  , module Math.Combinat.Partitions
  , module Math.Combinat.Permutations
  , module Math.Combinat.Tableaux
  , module Math.Combinat.Trees
  ) where

import Math.Combinat.Tuples
import Math.Combinat.Combinations
import Math.Combinat.Partitions
import Math.Combinat.Permutations
import Math.Combinat.Tableaux
import Math.Combinat.Trees

