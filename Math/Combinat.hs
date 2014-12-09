
-- | A collection of functions to generate combinatorial
-- objects like partitions, compositions, permutations,
-- Young tableaux, various trees, etc etc.
--
-- 
-- See also the @combinat-diagrams@ library for generating
-- graphical representations of these structure using 
-- the @diagrams@ library (<http://projects.haskell.org/diagrams>).
--
--
-- The long-term goals are 
--
--  (1) generate most of the standard structures;
-- 
--  (2) while being efficient; 
--
--  (3) to be able to enumerate the structures 
--      with constant memory usage;
--
--  (4) and to be able to randomly sample from them.
--
--  (5) finally, be a repository of algorithms
--
--
-- The short-term goal is simply to generate 
-- many interesting structures.
--
--
-- Naming conventions (subject to change): 
--
--  * prime suffix: additional constrains, typically more general;
--
--  * underscore prefix: use plain lists instead of other types with 
--    enforced invariants;
--
--  * \"random\" prefix: generates random objects 
--    (typically with uniform distribution); 
--
--  * \"count\" prefix: counting functions.
--
--
-- This module re-exports the most common modules.
--

module Math.Combinat 
  ( module Math.Combinat.Numbers
  , module Math.Combinat.Sets
  , module Math.Combinat.Tuples
  , module Math.Combinat.Compositions
  , module Math.Combinat.Partitions
  , module Math.Combinat.Permutations
  , module Math.Combinat.Tableaux
  , module Math.Combinat.Trees
  , module Math.Combinat.LatticePaths
  , module Math.Combinat.ASCII
  ) where

import Math.Combinat.Numbers
import Math.Combinat.Sets
import Math.Combinat.Tuples
import Math.Combinat.Compositions
import Math.Combinat.Partitions
import Math.Combinat.Permutations
import Math.Combinat.Tableaux
import Math.Combinat.Trees
import Math.Combinat.LatticePaths
import Math.Combinat.ASCII
