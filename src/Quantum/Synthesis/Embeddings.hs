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

import Data.Map (Map)
import qualified Data.Map as Map
import Data.List
import Data.Type.Equality

import qualified Utils.Unicode as U
import Quantum.Synthesis.Matrix
import Quantum.Synthesis.TypeArith
import Quantum.Synthesis.Ring

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
  fromInteger j    = Cyclo $ Map.singleton 0 (fromInteger j)

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

tmp :: Matrix Four Four Dyadic
tmp = matrix4x4 (-half, half, -half, -half)
                (-half, -half, -half, half)
                (half, half, -half, half)
                (half, -half, -half, -half)
