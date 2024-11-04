{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

{-|
Module      : MoreRings
Description : Additional rings
Maintainer  : matt.e.amy@gmail.com
Stability   : experimental
Portability : portable
-}

module Quantum.Synthesis.MoreRings(
  EisensteinRing(..),
  CplxRootTwoRing(..),
  Z4(..),
  DGaussian(..),
  Eisenstein(..),
  DEisen,
  ZEisen,
  CplxRootTwo(..),
  DCplxRootTwo,
  ZCplxRootTwo,
  residue2irt2,
  Residue(..),
  Cyclotomic(..),
  degree,
  zeta,
  constant,
  scale,
  decompose
  ) where

import Data.List
import Data.Bits
import Data.Map (Map)
import qualified Data.Map as Map

import Quantum.Synthesis.Matrix
import Quantum.Synthesis.Ring
import Quantum.Synthesis.EuclideanDomain
import Quantum.Synthesis.MultiQubitSynthesis (Residue(..))

import qualified Utils.Unicode as U
import Quantum.Synthesis.TypeArith

-- * Ring type classes
-- ---------------------------------------

-- ---------------------------------------
-- ** Rings with a cube root of unity

-- | A ring that has a cube root of unity
class Ring r => EisensteinRing r where
  eisen :: r

instance (EisensteinRing a, Nat n) => EisensteinRing (Matrix n n a) where
  eisen = scalarmult eisen 1

-- ---------------------------------------
-- ** Rings with a root of -2

-- | A ring that has a root of -2
class Ring a => CplxRootTwoRing a where
  iroottwo :: a
  fromZCplxRootTwo :: ZCplxRootTwo -> a
  -- defaults
  fromZCplxRootTwo (CplxRootTwo a b) = a' + b'*iroottwo where
    a' = fromInteger a
    b' = fromInteger b

instance (CplxRootTwoRing a, Nat n) => CplxRootTwoRing (Matrix n n a) where
  iroottwo = scalarmult iroottwo 1

-- * Rings and ring constructors
-- ---------------------------------------

-- ---------------------------------------
-- ** The ring \(\mathbb{Z}_4\) of integers mod 4
newtype Z4 = Z4 Integer deriving (Eq, Ord, Show)

instance Num Z4 where
  Z4 a + Z4 b   = Z4 $ (a + b) `mod` 4
  Z4 a * Z4 b   = Z4 $ (a * b) `mod` 4
  negate (Z4 a) = Z4 $ (-a) `mod` 4
  signum (Z4 a) = Z4 $ signum (a `mod` 4)
  abs (Z4 a)    = Z4 $ (a `mod` 4)
  fromInteger n = Z4 $ (n `mod` 4)

-- ---------------------------------------
-- ** Specialized instances for \(\mathbb{D}\)

-- | The 2-lde
instance DenomExp Dyadic where
  denomexp = snd . decompose_dyadic
  denomexp_factor a k = (fromInteger $ 1 `shiftL` (fromInteger k)) * a

-- ---------------------------------------
-- ** The ring \(\mathbb{D}[i]\)

-- | Wrapper for newsynth's DComplex to give a custom denominator exponent
newtype DGaussian = DGaussian DComplex
  deriving (Eq, Num, HalfRing, ComplexRing, Adjoint)

instance Show DGaussian where
  show (DGaussian d) = show d

instance WholePart DGaussian ZComplex where
  from_whole = DGaussian . from_whole
  to_whole (DGaussian d) = to_whole d

-- | The (1+i)-lde
instance DenomExp DGaussian where
  denomexp (DGaussian a) = if k > 0 && euclid_divides (1 + i) b then 2*k - 1 else 2*k
    where (b, k) = denomexp_decompose a
  denomexp_factor a k
    | k `mod` 2 == 0 = a * 2^(k `div` 2)
    | otherwise      = a * (1 + i) * 2^((k-1) `div` 2)

-- ---------------------------------------
-- ** The ring \(R[\omega]\)

-- | The ring \(R[\omega]\) where \(R\) is any ring and
--   \(\omega = e^{2\pi i /3}\) is a primitive 3rd root
--   of unity. The value 'Eisen' /a/ /b/ represents
--   the complex number \(\omega a + b\)
data Eisenstein r = Eisen !r !r deriving (Eq)

instance (Show r, Eq r, Ring r) => Show (Eisenstein r) where
  showsPrec _ (Eisen 0 0) = showString "0"
  showsPrec p (Eisen a b) = showParen (p >= 11) $ showString str where
    str = intercalate " + " $ showA ++ showB
    showA
      | a == 0    = []
      | a == 1    = [U.omega]
      | otherwise = [U.omega ++ "*" ++ showsPrec 11 a ""]
    showB
      | b == 0    = []
      | otherwise = [showsPrec 11 b ""]

instance Num r => Num (Eisenstein r) where
  (Eisen a b) + (Eisen c d) = Eisen (a + c) (b + d)
  (Eisen a b) * (Eisen c d) = Eisen a' b' where
    a' = a*d + b*c - a*c
    b' = b*d - a*c
  negate (Eisen a b)            = Eisen (-a) (-b)
  signum _                      = undefined
  abs _                         = undefined
  fromInteger j                 = Eisen 0 (fromInteger j)

instance (Ring r, Adjoint r) => Adjoint (Eisenstein r) where
  adj (Eisen a b) = Eisen (-a) (b - a)

instance HalfRing r => HalfRing (Eisenstein r) where
  half = Eisen 0 half

instance Ring r => EisensteinRing (Eisenstein r) where
  eisen = Eisen 1 0

instance (Eq r, EisensteinRing r) => EisensteinRing (CplxRootTwo r) where
  eisen = CplxRootTwo eisen 0

-- ---------------------------------------
-- ** The ring \(\mathbb{Z}[\omega]\) of Eisenstein integers
type ZEisen = Eisenstein Integer

-- ---------------------------------------
-- ** The ring \(\mathbb{D}[\omega]\)
type DEisen = Eisenstein Dyadic

-- ---------------------------------------
-- ** The ring \(R[i\sqrt{2}]\)

-- | The ring \(R[i\sqrt{2}]\) where \(R\) is any ring and
--   \(i\sqrt{2}\) is a root of negative 2.
--   The value 'CplxRootTwo' /a/ /b/ represents \(a + bi\sqrt{2}\)
data CplxRootTwo a = CplxRootTwo !a !a deriving (Eq)

instance (Eq a, Num a) => Num (CplxRootTwo a) where
  CplxRootTwo a b + CplxRootTwo a' b' = CplxRootTwo (a + a') (b + b')
  CplxRootTwo a b * CplxRootTwo a' b' = CplxRootTwo a'' b'' where
    a'' = a * a' - 2 * b * b'
    b'' = a * b' + a' * b
  negate (CplxRootTwo a b)            = CplxRootTwo (-a) (-b)
  abs x                               = x
  signum _                            = 1
  fromInteger n                       = CplxRootTwo (fromInteger n) 0

instance (Show a, Eq a, Ring a) => Show (CplxRootTwo a) where
  showsPrec d (CplxRootTwo a 0)    = showsPrec d a
  showsPrec _ (CplxRootTwo 0 1)    = showString "iroottwo"
  showsPrec d (CplxRootTwo 0 (-1)) = showParen (d >= 7) str where
    str = showString "-iroottwo"
  showsPrec d (CplxRootTwo 0 b)    = showParen (d >= 8) str where
    str = showsPrec 7 b . showString "*iroottwo"
  showsPrec d (CplxRootTwo a b)
    | signum b == 1 = showParen (d >= 7) str where
        str = showsPrec 6 a . showString " + " . showsPrec 6 (CplxRootTwo 0 b)
  showsPrec d (CplxRootTwo a b)
    | otherwise     = showParen (d >= 7) str where
        str = showsPrec 6 a . showString " - " . showsPrec 7 (CplxRootTwo 0 (-b))

instance (Eq a, Ring a) => CplxRootTwoRing (CplxRootTwo a) where
  iroottwo = CplxRootTwo 0 1

instance (Eq a, HalfRing a) => HalfRing (CplxRootTwo a) where
  half = CplxRootTwo half 0

instance (Adjoint a, Ring a) => Adjoint (CplxRootTwo a) where
  adj (CplxRootTwo a b) = CplxRootTwo (adj a) (-(adj b))

instance (Eq a, NormedRing a) => NormedRing (CplxRootTwo a) where
  norm (CplxRootTwo a b) = (norm a)*(norm a) + 2*(norm b)*(norm b)

instance Residue a b => Residue (CplxRootTwo a) (CplxRootTwo b) where
  residue (CplxRootTwo a b) = CplxRootTwo (residue a) (residue b)

-- ---------------------------------------
-- ** The ring \(\mathbb{Z}[i\sqrt{2}]\)
type ZCplxRootTwo = CplxRootTwo Integer

-- ---------------------------------------
-- ** The ring \(\mathbb{D}[i\sqrt{2}]\)
type DCplxRootTwo = CplxRootTwo Dyadic

instance WholePart DCplxRootTwo ZCplxRootTwo where
  from_whole                 = fromZCplxRootTwo
  to_whole (CplxRootTwo a b) = CplxRootTwo (to_whole a) (to_whole b)

instance EuclideanDomain ZCplxRootTwo where
  rank a = abs (norm a)
  divmod a b = (q, r) where
    (CplxRootTwo l m) = a * adj b
    k = norm b
    q1 = l `rounddiv` k
    q2 = m `rounddiv` k
    q = CplxRootTwo q1 q2
    r = a - b * q

-- | The \(i\sqrt{2}\) denominator exponent
instance DenomExp DCplxRootTwo where
  denomexp (CplxRootTwo a b) = maximum [2*k, 2*l-1] where
    (_,k) = decompose_dyadic a
    (_,l) = decompose_dyadic b
  denomexp_factor a k = a * iroottwo^k

-- | Take the residue of \(a\in\mathbb{Z}[i\sqrt{2}]\) mod \(2i\sqrt{2}\)
residue2irt2 :: ZCplxRootTwo -> (Z4, Z2)
residue2irt2 p = (fromInteger a, fromInteger b) where
  (_, CplxRootTwo a b) = divmod p (2*iroottwo)

-- ---------------------------------------
-- ** The ring \(R[\zeta_k]\)

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
degree (Cyclo p) = maybe 0 (fromIntegral . fst) . maxKey $ p where
  maxKey = fmap fst . Map.maxViewWithKey

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
