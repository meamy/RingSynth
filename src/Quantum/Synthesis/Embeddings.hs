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

module Quantum.Synthesis.Embeddings where

import Data.Type.Equality
import Unsafe.Coerce
import Data.Map (Map)
import qualified Data.Map as Map
import Data.List

import qualified Utils.Unicode as U
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
type family Power n m where
  Power n Zero      = One
  Power n (Succ m') = Times n (Power n m')

-- | Propositional ordering
type family n :<: m :: Bool

type instance _ :<: Zero              = 'False
type instance Zero :<: (Succ n')      = 'True
type instance (Succ n') :<: (Succ m') = n' :<: m'

-- | Type constraint ordering
type n < m = (n :<: m) ~ 'True

{-------------------------------
 Cyclotomics
 -------------------------------}
-- | The /k/th cyclotomic extension of /r/, \(R[\zeta_k]\)
data Cyclotomic k r = Cyclo !(Map Integer r)

instance (Nat k, Eq r, Num r, Show r) => Show (Cyclotomic k r) where
  show (Cyclo p)
    | Map.null p = "0"
    | otherwise  = intercalate " + " $ map showTerm (Map.assocs p)
    where showTerm (expt, a)
            | expt == 0  = show a
            | a == 1     = showExpt expt
            | a == -1    = show "-" ++ showExpt expt
            | otherwise  = show a ++ showExpt expt
          showExpt expt
            | expt == 1  = U.sub U.zeta (nat @k undefined)
            | otherwise  = U.sup (U.sub U.zeta (nat @k undefined)) expt

instance (Nat k, Num r) => Num (Cyclotomic k r) where
  (+)              = add
  (*)              = mult
  negate (Cyclo p) = Cyclo (Map.map negate p)
  abs              = id
  signum           = id
  fromInteger 0    = Cyclo Map.empty
  fromInteger i    = Cyclo $ Map.singleton 0 (fromInteger i)

-- | Retrieve the degree of the polynomial
degree :: Cyclotomic k r -> Integer
degree (Cyclo p) = maybe 0 (fromIntegral . fst) . Map.lookupMax $ p

-- | The cyclotomic polynomial \(\zeta_k\)
zeta :: (Nat k, Ring r) => Cyclotomic k r
zeta = Cyclo $ Map.singleton 1 1

-- | Constant polynomial
constant :: (Nat k, Ring r) => r -> Cyclotomic k r
constant = Cyclo . Map.singleton 0

-- | Multiply by a scalar
scale :: (Nat k, Ring r) => r -> Cyclotomic k r -> Cyclotomic k r
scale a (Cyclo p) = Cyclo $ Map.map (a*) p

-- | Add two univariate polynomials
add :: (Nat k, Num r) => Cyclotomic k r -> Cyclotomic k r -> Cyclotomic k r
add (Cyclo p) (Cyclo q) = Cyclo $ Map.unionWith (+) p q

-- | Multiply two univariate polynomials
mult :: forall k r. (Nat k, Num r) => Cyclotomic k r -> Cyclotomic k r -> Cyclotomic k r
mult (Cyclo p) (Cyclo q) = Map.foldrWithKey (\expt a -> add (mulTerm expt a)) 0 p where
  mulTerm expt a      = Cyclo . Map.mapKeys (plusModK expt) $ Map.map (* a) q
  plusModK expt expt' = (expt + expt') `mod` (nat @k undefined)

-- | Decomposes an element of \(R[\zeta_{2^k}]\) as \(R[\zeta_{2^{k-1}}]:R[\zeta_{2^k}]\)
decompose :: (Nat k, Eq r, Num r)
          => Cyclotomic (Power Two (Succ k)) r
          -> (Cyclotomic (Power Two k) r, Cyclotomic (Power Two k) r)
decompose (Cyclo p) = (Cyclo $ divTwo q, Cyclo $ divTwoMinus r) where
  (q, r)      = Map.partitionWithKey (\l _a -> l `mod` 2 == 0) p
  divTwo      = Map.mapKeysMonotonic (`div` 2)
  divTwoMinus = Map.mapKeysMonotonic (\l -> (l - 1) `div` 2)

{------------------------
 Embeddings
 ------------------------}

-- | Class of rings with an /a/-embedding
class (Nat a, Ring r, Ring r') => Embeddable a r r' where
  embed :: Nat n => Matrix n n r -> Matrix (Times a n) (Times a n) r' 
  embedElt :: r -> Matrix a a r'
  {- Default implementations -}
  embedElt e = case times_unit (nnat @a) of
    Refl -> (embed @a) . column_matrix . vector_singleton $ e

{------------------------
 Specific embeddings
 ------------------------}

instance Ring r => Embeddable Two (Cplx r) r where
  embed :: forall n. Nat n => Matrix n n (Cplx r) -> Matrix (Times Two n) (Times Two n) r
  embed mat = case n_plus_n (nnat @ n) of
    Refl -> stack_horizontal (stack_vertical a b) (stack_vertical (-b) a) where
      (a,b) = case commute mat of Cplx a' b' -> (a',b')

instance (Eq r, ComplexRing r) => Embeddable Two (RootTwo r) r where
  embed :: forall n. Nat n => Matrix n n (RootTwo r) -> Matrix (Times Two n) (Times Two n) r
  embed mat = case n_plus_n (nnat @ n) of
    Refl -> stack_horizontal (stack_vertical a b1) (stack_vertical b2 a) where
      (a,b) = case commute mat of RootTwo a' b' -> (a',b')
      b1    = scalarmult (1 + i) b
      b2    = scalarmult (1 - i) b

instance (Nat k, Nat k', Nat k'', Ring r, Eq r, k' ~ Power Two (Succ k), k'' ~ Power Two k)
      => Embeddable Two (Cyclotomic k' r) (Cyclotomic k'' r) where
  embed :: forall n. Nat n
                  => Matrix n n (Cyclotomic k' r)
                  -> Matrix (Times Two n) (Times Two n) (Cyclotomic k'' r)
  embed mat = case n_plus_n (nnat @ n) of
    Refl -> stack_horizontal (stack_vertical a b) (stack_vertical a c) where
      (a,b) = case decompose @k $ commute mat of (a',b') -> (commute a', commute b')
      c     = scalarmult zeta b
  embedElt :: Cyclotomic k' r -> Matrix Two Two (Cyclotomic k'' r)
  embedElt e = case decompose @k e of
    (a,b) -> matrix2x2 (a,zeta*b) (b,a)

{------------------------
 Utilities
 ------------------------}

-- | Things that have a "complex" part
class ComplexPart a b | a -> b where
  complex :: a -> b

instance ComplexPart (Cplx a) a where
  complex (Cplx _a b) = b

-- | Class for functors which commute
class Commuting f g a where
  commute :: f (g a) -> g (f a)

instance Commuting Cplx RootTwo r where
  commute (Cplx (RootTwo a b) (RootTwo c d)) = RootTwo (Cplx a c) (Cplx b d)

instance Nat n => Commuting (Matrix n n) Cplx r where
  commute mat = Cplx (matrix_map real mat) (matrix_map complex mat)

instance Nat n => Commuting (Matrix n n) RootTwo r where
  commute mat = RootTwo (matrix_map ipart mat) (matrix_map rpart mat) where
    ipart (RootTwo a _b) = a
    rpart (RootTwo _a b) = b

instance forall n k r. (Ring r, Nat n, Nat k) => Commuting (Matrix n n) (Cyclotomic k) r where
  commute mat = Cyclo $ Map.fromAscList [(i, collectExpt i) | i <- [0..(nat @k undefined)]] where
    collectExpt :: Integer -> Matrix n n r
    collectExpt y = matrix_map (\(Cyclo p) -> Map.findWithDefault 0 y p) mat

instance forall n k r. (Ring r, Nat n, Nat k) => Commuting (Cyclotomic k) (Matrix n n) r where
  commute (Cyclo p) = Map.foldr (+) 0 $ Map.mapWithKey go p where
    go expt = matrix_map (\a -> Cyclo $ Map.singleton expt a)

{--------------------------
 Testing & examples
 --------------------------}
i_in_D :: Matrix Two Two Dyadic
i_in_D = embedElt (i :: Cplx Dyadic)

rt2_in_Di :: Matrix Two Two (Cplx Dyadic)
rt2_in_Di = embedElt (roottwo :: RootTwo (Cplx Dyadic))

rt2_in_D :: Matrix Four Four Dyadic
rt2_in_D = embed @Two rt2_in_Di
  
omega_one_one :: Matrix One One (Cyclotomic Eight Dyadic)
omega_one_one = column_matrix $ vector_singleton $ zeta

--omega_in_i :: Matrix Two Two (Cyclotomic Four Dyadic)
--omega_in_i = embedElt (zeta :: Cyclotomic Eight Dyadic)
