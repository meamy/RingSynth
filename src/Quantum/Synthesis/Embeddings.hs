{-# LANGUAGE InstanceSigs #-}
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

{-|
Module      : Embeddings
Description : Tools for embedding one ring inside another
Maintainer  : matt.e.amy@gmail.com
Stability   : experimental
Portability : portable
-}

module Quantum.Synthesis.Embeddings where

import Data.Type.Equality
import qualified Data.Map as Map

import Quantum.Synthesis.Matrix
import Quantum.Synthesis.Ring
import Quantum.Synthesis.TypeArith
import Quantum.Synthesis.MoreRings
import Quantum.Synthesis.Exact



{------------------------
 Embeddings
 ------------------------}

-- | Class of rings with an /a/-embedding
class (Nat a, Ring r, Ring r') => Embeddable a r r' | r r' -> a where
  embed :: Nat n => Matrix n n r -> Matrix (Times a n) (Times a n) r' 
  embedElt :: r -> Matrix a a r'
  {- Default implementations -}
  embedElt e = case times_unit (nnat @a) of
    Refl -> (embed @a) . column_matrix . vector_singleton $ e

{------------------------
 Specific embeddings
 ------------------------}

instance Ring r => Embeddable Two (Cplx r) r where
  embed mat = case n_plus_n (nnatMat mat) of
    Refl -> stack_horizontal (stack_vertical a b) (stack_vertical (-b) a) where
      (a,b) = case commute mat of Cplx a' b' -> (a',b')

instance Ring r => Embeddable Two (Omega r) (Cplx r) where
  embed mat = case n_plus_n (nnatMat mat) of
    Refl -> stack_horizontal (stack_vertical a b) (stack_vertical b0 a) where
      b0    = scalarmult i b
      (a,b) = case commute mat of
        Omega a' b' c' d' -> (commute (Cplx d' b'), commute (Cplx c' a'))

instance (Eq r, ComplexRing r) => Embeddable Two (RootTwo r) r where
  embed mat = case n_plus_n (nnatMat mat) of
    Refl -> stack_horizontal (stack_vertical a b1) (stack_vertical b2 a) where
      (a,b) = case commute mat of RootTwo a' b' -> (a',b')
      b1    = scalarmult (1 + i) b
      b2    = scalarmult (1 - i) b

instance (Eq r, HalfRing r) => Embeddable Four (Eisenstein r) r where
  embed :: forall n. Nat n => Matrix n n (Eisenstein r) -> Matrix (Four `Times` n) (Four `Times` n) r
  embed mat = withProof (times_is_nat (nnat @Four) (nnatMat mat)) go mat where
    go :: Nat (Four `Times` n) => Matrix n n (Eisenstein r) -> Matrix (Four `Times` n) (Four `Times` n) r
    go mat = (tensor gamma (1 :: Matrix n n r))*(lift a) + lift b where
      (Eisen a b) = commute mat
      lift = tensor (1 :: Matrix Four Four r)
      gamma = matrix4x4 (-half,half,-half,-half)
                        (-half,-half,-half,half)
                        (half,half,-half,half)
                        (half,-half,-half,-half)

instance (Eq r, HalfRing r) => Embeddable Two (Eisenstein r) (Cplx r) where
  embed mat = case n_plus_n (nnatMat mat) of
    Refl -> stack_horizontal (stack_vertical a b) (stack_vertical c d) where
      (a0, b0) = case commute mat of Eisen a b -> (matrix_map iota a, matrix_map iota b)
      a        = scalarmult (half*(-1 + i)) a0 .+. b0
      b        = scalarmult (half*(-1 + i)) a0
      c        = scalarmult (half*( 1 + i)) a0
      d        = scalarmult (half*(-1 - i)) a0 .+. b0

-- | Specific embedding for cyclotomics to deal with some GHC constraints
embedCyclotomicMat :: forall n k r. (Nat n, Nat k, Eq r, Ring r, Nat (Power Two k), Nat (Power Two (Succ k)))
                => Matrix n n (Cyclotomic (Power Two (Succ k)) r)
                -> Matrix (Times Two n) (Times Two n) (Cyclotomic (Power Two k) r)
embedCyclotomicMat mat = case n_plus_n (nnatMat mat) of
    Refl -> stack_horizontal (stack_vertical a b) (stack_vertical a c) where
      (a,b) = case decompose @k $ commute mat of (a',b') -> (commute a', commute b')
      c     = scalarmult zeta b

-- | Specific embedding for cyclotomics to deal with some GHC constraints
embedCyclotomicPoly :: forall k r. (Nat k, Eq r, Ring r, Nat (Power Two k))
                => Cyclotomic (Power Two (Succ k)) r
                -> Matrix Two Two (Cyclotomic (Power Two k) r)
embedCyclotomicPoly e = case decompose @k e of
    (a,b) -> matrix2x2 (a,zeta*b) (b,a)

-- | Temporary, embed \(\sqrt{a^2 + b^2}\) in a complex ring containing a and b
embedRoot :: ComplexRing r => r -> r -> Matrix Two Two r
embedRoot a b = matrix2x2 (0, a - i*b) (a + i*b, 0)

{------------------------
 Utilities
 ------------------------}

-- | The dimension of a square matrix as an NNat
nnatMat :: forall n r. Nat n => Matrix n n r -> NNat n
nnatMat _mat = nnat @n

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

instance (Nat n, Ring r) => Commuting Cplx (Matrix n n) r where
  commute (Cplx mr mi) = mr' + mi' where
    mr' = matrix_map (\a -> Cplx a 0) mr
    mi' = matrix_map (\a -> Cplx 0 a) mi

instance Nat n => Commuting (Matrix n n) Omega r where
  commute mat = Omega w x y z where
    w = matrix_map (\(Omega a _b _c _d) -> a) mat
    x = matrix_map (\(Omega _a b _c _d) -> b) mat
    y = matrix_map (\(Omega _a _b c _d) -> c) mat
    z = matrix_map (\(Omega _a _b _c d) -> d) mat

instance Nat n => Commuting (Matrix n n) RootTwo r where
  commute mat = RootTwo (matrix_map ipart mat) (matrix_map rpart mat) where
    ipart (RootTwo a _b) = a
    rpart (RootTwo _a b) = b

instance forall n k r. (Ring r, Nat n, Nat k) => Commuting (Matrix n n) (Cyclotomic k) r where
  commute mat = Cyclo $ Map.fromAscList [(j, collectExpt j) | j <- [0..(nat @k undefined)]] where
    collectExpt :: Integer -> Matrix n n r
    collectExpt y = matrix_map (\(Cyclo p) -> Map.findWithDefault 0 y p) mat

instance forall n k r. (Ring r, Nat n, Nat k) => Commuting (Cyclotomic k) (Matrix n n) r where
  commute (Cyclo p) = Map.foldr (+) 0 $ Map.mapWithKey go p where
    go expt = matrix_map (\a -> Cyclo $ Map.singleton expt a)

instance Nat n => Commuting (Matrix n n) Eisenstein r where
  commute mat = Eisen amat bmat where
    amat = matrix_map (\(Eisen a _) -> a) mat
    bmat = matrix_map (\(Eisen _ b) -> b) mat

{--------------------------
 Testing & examples
 --------------------------}

i_in_D :: Matrix Two Two Dyadic
i_in_D = embedElt (i :: Cplx Dyadic)

rt2_in_Di :: Matrix Two Two (Cplx Dyadic)
rt2_in_Di = embedElt (roottwo :: RootTwo (Cplx Dyadic))

rt2_in_D :: Matrix Four Four Dyadic
rt2_in_D = embed rt2_in_Di

omega_in_Di :: Matrix Two Two (Cplx Dyadic)
omega_in_Di = embedElt (omega :: Omega Dyadic)

omega_in_D :: Matrix Four Four Dyadic
omega_in_D = embed omega_in_Di

omega_in_Di_alt :: Matrix Two Two (Cplx Dyadic)
omega_in_Di_alt = embedElt (roottwo * half * (1 + i) :: RootTwo (Cplx Dyadic))

omega_in_D_alt :: Matrix Four Four Dyadic
omega_in_D_alt = embed omega_in_Di_alt

eisen_in_D :: Matrix Four Four Dyadic
eisen_in_D = matrix4x4 (-half, half, -half, -half)
                       (-half, -half, -half, half)
                       (half, half, -half, half)
                       (half, -half, -half, -half)

eisen_in_Di :: Matrix Two Two (Cplx Dyadic)
eisen_in_Di = embedElt (eisen :: Eisenstein Dyadic)

controlled_t_in_DOmega :: Matrix Four Four DOmega
controlled_t_in_DOmega = matrix4x4 (1, 0, 0, 0) (0, 1, 0, 0) (0, 0, 1, 0) (0, 0, 0, omega)

controlled_t_in_Di :: Matrix Eight Eight (Cplx Dyadic)
controlled_t_in_Di = embed controlled_t_in_DOmega

controlled_t_in_D :: Matrix (Times Two Eight) (Times Two Eight) Dyadic
controlled_t_in_D = embed controlled_t_in_Di
