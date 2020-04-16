{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternSynonyms #-}

{-|
Module      : TypeArith
Description : Extra type arithmetic
Maintainer  : matt.e.amy@gmail.com
Stability   : experimental
Portability : portable
-}

module Quantum.Synthesis.TypeArith where

import Data.Type.Equality
import Unsafe.Coerce
import GHC.Exts (Constraint)

import Quantum.Synthesis.Matrix

{------------------------
 Proof techniques
 ------------------------}

-- | The type of propositions (the "dict" trick). Instances
--   are proofs
data Lemma (c :: Constraint) where
  Qed :: forall c. c => Lemma c

-- | Type class generalizing the :~: type equality witness to
--   other constraints. Adapted from Edward Kmett's Constraint library
class Witness e (c :: Constraint) | e -> c where
  witness :: e -> Lemma c

instance Witness (a :~: b) (a ~ b) where
  witness Refl = Qed

-- | Uses a proof to bring a constraint into the type checking context
withProof :: forall (c :: Constraint) b. Lemma c -> (c => b) -> b
withProof Qed = id

{------------------------
 More type level arithmetic
 ------------------------}

-- | Powers of natural numbers
type family Power n m 
type instance Power n Zero     = One
type instance Power n (Succ m) = Times n (Power n m)

-- | Logarithms of natural numbers
type family Log n m 
type instance Log n One = Zero
type instance Log n (power n m) = m

-- | Propositional ordering
type family n :<: m :: Bool

type instance _ :<: Zero              = 'False
type instance Zero :<: (Succ n')      = 'True
type instance (Succ n') :<: (Succ m') = n' :<: m'

-- | Type constraint ordering
type n < m = (n :<: m) ~ 'True

-- | Term-level reflection of the Plus type family
plus :: forall n m. (Nat n, Nat m) => NNat n -> NNat m -> NNat (Plus n m)
plus Zero b     = b
plus (Succ a) b = withProof (plus_is_nat a b) $ Succ (plus a b)

-- | Term-level reflection of the Plus type family
times :: forall n m. (Nat n, Nat m) => NNat n -> NNat m -> NNat (Times n m)
times Zero _b    = Zero
times (Succ a) b = withProof (times_is_nat a b) $ plus b (times a b)

-- | Term-level reflection of the Power type family
power :: forall n m. (Nat n, Nat m) => NNat n -> NNat m -> NNat (Power n m)
power _a Zero    = Succ Zero
power a (Succ b) = withProof (power_is_nat a b) $ times a (power a b)

{------------------------
 Arithmetic identities
 ------------------------}

-- | Generate a witness for the commutativity of plus
plus_commutes :: (Nat n, Nat m) => NNat n -> NNat m -> Plus n m :~: Plus m n
plus_commutes _ _ = unsafeCoerce Refl

-- | Commutativity of Times
times_commutes :: (Nat n, Nat m) => NNat n -> NNat m -> Times n m :~: Times m n
times_commutes _ _ = unsafeCoerce Refl

-- | One is a unit with respect to Times
times_unit :: Nat n => NNat n -> Times n One :~: n
times_unit _ = unsafeCoerce Refl

-- | Plus n n is Times Two n
n_plus_n :: Nat n => NNat n ->  Plus n n :~: Times Two n
n_plus_n _ = unsafeCoerce Refl

-- | Times Four n is n + n + n + n
times_four :: Nat n => NNat n ->  Times Four n :~: Plus n (Plus n (Plus n (Plus n Zero)))
times_four _ = unsafeCoerce Refl

-- | Plus n m is a Nat
plus_is_nat :: forall n m. (Nat n, Nat m) => NNat n -> NNat m -> Lemma (Nat (Plus n m))
plus_is_nat a b = case a of
  Zero    -> Qed
  Succ a' -> withProof (plus_is_nat a' b) Qed

-- | Quantified proof that a plus is a Nat
plus_is_nat_quant :: forall n m. (Nat n, Nat m) => Lemma (Nat (Plus n m))
plus_is_nat_quant = case plus_is_nat (nnat @n) (nnat @m) of Qed -> Qed

-- | Times n m is a Nat
times_is_nat :: forall n m. (Nat n, Nat m) => NNat n -> NNat m -> Lemma (Nat (Times n m))
times_is_nat a b = case a of
  Zero                 -> Qed
  Succ (a' :: NNat n') -> withProof (times_is_nat a' b) $
                          withProof (plus_is_nat b (nnat @(Times n' m))) $
                          Qed

-- | Power n m is a Nat
power_is_nat :: forall n m. (Nat n, Nat m) => NNat n -> NNat m -> Lemma (Nat (Power n m))
power_is_nat a b = case b of
  Zero                 -> Qed
  Succ (b' :: NNat m') -> withProof (power_is_nat a b') $
                          withProof (times_is_nat a (nnat @(Power n m'))) $
                          Qed
