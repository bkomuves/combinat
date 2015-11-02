
-- | Type-level hackery.
--
-- This module is used for groups whose parameters are encoded as type-level natural numbers,
-- for example finite cyclic groups, free groups, symmetric groups and braid groups.
--

{-# LANGUAGE PolyKinds, DataKinds, KindSignatures, ScopedTypeVariables, 
             ExistentialQuantification, Rank2Types #-}

module Math.Combinat.TypeLevel 
  ( -- * Proxy
    Proxy(..)
  , proxyUndef
  , proxyOf
  , proxyOf1
  , proxyOf2
  , asProxyTypeOf   -- defined in Data.Proxy
  , asProxyTypeOf1
    -- * Type-level naturals as type arguments
  , typeArg 
  , iTypeArg
    -- * Hiding the type parameter
  , Some (..)
  , withSome , withSomeM
  , selectSome , selectSomeM
  , withSelected , withSelectedM
  )
  where

--------------------------------------------------------------------------------

import Data.Proxy ( Proxy(..) , asProxyTypeOf )
import GHC.TypeLits

import Math.Combinat.Numbers.Primes ( isProbablyPrime )

--------------------------------------------------------------------------------
-- * Proxy

proxyUndef :: Proxy a -> a
proxyUndef _ = error "proxyUndef"

proxyOf :: a -> Proxy a
proxyOf _ = Proxy

proxyOf1 :: f a -> Proxy a
proxyOf1 _ = Proxy

proxyOf2 :: g (f a) -> Proxy a
proxyOf2 _ = Proxy

asProxyTypeOf1 :: f a -> Proxy a -> f a 
asProxyTypeOf1 y _ = y

--------------------------------------------------------------------------------
-- * Type-level naturals as type arguments

typeArg :: KnownNat n => f (n :: Nat) -> Integer
typeArg = natVal . proxyOf1

iTypeArg :: KnownNat n => f (n :: Nat) -> Int
iTypeArg = fromIntegral . typeArg

--------------------------------------------------------------------------------
-- * Hiding the type parameter

-- | Hide the type parameter of a functor. Example: @Some Braid@
data Some f = forall n. KnownNat n => Some (f n)

-- | Uses the value inside a 'Some'
withSome :: Some f -> (forall n. KnownNat n => f n -> a) -> a
withSome some polyFun = case some of { Some stuff -> polyFun stuff }

-- | Monadic version of 'withSome'
withSomeM :: Monad m => Some f -> (forall n. KnownNat n => f n -> m a) -> m a
withSomeM some polyAct = case some of { Some stuff -> polyAct stuff }

-- | Given a polymorphic value, we select at run time the
-- one specified by the second argument
selectSome :: Integral int => (forall n. KnownNat n => f n) -> int -> Some f
selectSome poly n = case someNatVal (fromIntegral n :: Integer) of
  Nothing   -> error "selectSome: not a natural number"
  Just snat -> case snat of
    SomeNat pxy -> Some (asProxyTypeOf1 poly pxy)

-- | Monadic version of 'selectSome'
selectSomeM :: forall m f int. (Integral int, Monad m) => (forall n. KnownNat n => m (f n)) -> int -> m (Some f)
selectSomeM runPoly n = case someNatVal (fromIntegral n :: Integer) of
  Nothing   -> error "selectSomeM: not a natural number"
  Just snat -> case snat of
    SomeNat pxy -> do
      poly <- runPoly 
      return $ Some (asProxyTypeOf1 poly pxy)

-- | Combination of 'selectSome' and 'withSome': we make a temporary structure
-- of the given size, but we immediately consume it.
withSelected 
  :: Integral int 
  => (forall n. KnownNat n => f n -> a) 
  -> (forall n. KnownNat n => f n) 
  -> int 
  -> a
withSelected f x n = withSome (selectSome x n) f

-- | (Half-)monadic version of 'withSelected'
withSelectedM 
  :: forall m f int a. (Integral int, Monad m) 
  => (forall n. KnownNat n => f n -> a) 
  -> (forall n. KnownNat n => m (f n)) 
  -> int 
  -> m a
withSelectedM f mx n = do 
  s <- selectSomeM mx n
  return (withSome s f)

--------------------------------------------------------------------------------
