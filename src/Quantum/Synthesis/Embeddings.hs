{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ConstraintKinds #-}

{-|
Module      : Embeddings
Description : Tools for embedding one ring inside another
Maintainer  : matt.e.amy@gmail.com
Stability   : experimental
Portability : portable
-}

module Quantum.Synthesis.Embeddings(
  Embeddable(..),
  ComplexPart(..),
  Commuting(..)
  )where

import Data.Type.Equality
import Unsafe.Coerce

import Quantum.Synthesis.Ring
import Quantum.Synthesis.Matrix

{------------------------
 Coercions & utilities for type-level natural arithmetic
 ------------------------}

-- | Commutativity of Plus
plus_commutes :: (Nat n, Nat m) => NNat n -> NNat m -> Plus n m :~: Plus m n
plus_commutes _ _ = unsafeCoerce Refl

-- | Commutativity of Times
times_commutes :: (Nat n, Nat m) => NNat n -> NNat m -> Times n m :~: Times m n
times_commutes _ _ = unsafeCoerce Refl

-- | One is a unit with respect to Times
times_unit :: Nat n => NNat n -> Times n One :~: n
times_unit _ = unsafeCoerce Refl

-- | Plus n n is Times Two n
n_plus_n :: Nat n => NNat n -> Plus n n  :~: Times Two n
n_plus_n _ = unsafeCoerce Refl

-- | Powers of natural numbers
type family Power n m
type instance Power n Zero      = One
type instance Power n (Succ m') = Times n (Power n m')

-- | Propositional ordering
type family n :<: m :: Bool

type instance _ :<: Zero              = 'False
type instance Zero :<: (Succ n')      = 'True
type instance (Succ n') :<: (Succ m') = n' :<: m'

-- | Type constraint ordering
type n < m = (n :<: m) ~ 'True

{------------------------
 Embeddings
 ------------------------}

-- | Class of rings with an /a/-embedding
class (Nat a, Ring r, Ring r') => Embeddable a r r' where
  embed :: Nat n => Matrix n n r -> Matrix (Times a n) (Times a n) r' 
  embedElt :: r -> Matrix a a r'
  {- Default implementations -}
  embedElt e = case times_unit (nnat @ a) of
    Refl -> (embed @ a) . column_matrix . vector_singleton $ e

{------------------------
 Specific embeddings
 ------------------------}

instance Ring r => Embeddable Two (Cplx r) r where
  embed :: forall n. Nat n => Matrix n n (Cplx r) -> Matrix (Times Two n) (Times Two n) r
  embed mat = case n_plus_n (nnat @ n) of
    Refl -> stack_horizontal (stack_vertical a b) (stack_vertical a (-b)) where
      (a,b) = case commute mat of Cplx a' b' -> (a',b')

instance (Eq r, ComplexRing r) => Embeddable Two (RootTwo r) r where
  embed :: forall n. Nat n => Matrix n n (RootTwo r) -> Matrix (Times Two n) (Times Two n) r
  embed mat = case n_plus_n (nnat @ n) of
    Refl -> stack_horizontal (stack_vertical a b1) (stack_vertical a b2) where
      (a,b) = case commute mat of RootTwo a' b' -> (a',b')
      b1    = scalarmult (1 + i) b
      b2    = scalarmult (1 - i) b

{------------------------
 Utilities
 ------------------------}

-- | Things that have a "complex" part
class ComplexPart a b | a -> b where
  complex :: a -> b

instance ComplexPart (Cplx a) a where
  complex (Cplx _a b) = b

-- | Class for functors which commute
class Commuting f g where
  commute :: f (g a) -> g (f a)

instance Commuting Cplx RootTwo where
  commute (Cplx (RootTwo a b) (RootTwo c d)) = RootTwo (Cplx a c) (Cplx b d)

instance Nat n => Commuting (Matrix n n) Cplx where
  commute mat = Cplx (matrix_map real mat) (matrix_map complex mat)

instance Nat n => Commuting (Matrix n n) RootTwo where
  commute mat = RootTwo (matrix_map ipart mat) (matrix_map rpart mat) where
    ipart (RootTwo a _b) = a
    rpart (RootTwo _a b) = b
