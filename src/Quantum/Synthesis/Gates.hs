{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PostfixOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

{-|
Module      : Gates
Description : Gates & gate hierarchies
Maintainer  : matt.e.amy@gmail.com
Stability   : experimental
Portability : portable
-}

module Quantum.Synthesis.Gates where

import Prelude hiding (Real, Integral)
import Data.Bits
import Data.List
import Control.Monad

import Quantum.Synthesis.Matrix
import Quantum.Synthesis.Ring


import Quantum.Synthesis.MoreRings

{-----------------------------
 (Polymorphic) Gates
 -----------------------------}

-- | Empty class
class Gate repr where
  identity :: repr

-- | The permutation group \(S_{2^n}\)
class Gate repr => Permutation repr where
  x   :: Int -> repr
  cx  :: Int -> Int -> repr
  ccx :: Int -> Int -> Int -> repr

-- | The 2-permutation group \(S_{2^n}(2)\)
class Permutation repr => TwoPermutation repr where
  z :: Int -> repr

-- | The 4-permutation group \(S_{2^n}(4)\)
class TwoPermutation repr => FourPermutation repr where
  s :: Int -> repr

-- | The 8-permutation group \(S_{2^n}(8)\)
class FourPermutation repr => EightPermutation repr where
  t :: Int -> repr

-- | The Integral Clifford + T operators \(U_n(\mathbb{D})\)
class Permutation repr => Integral repr where
  hh :: Int -> Int -> repr
  
-- | The Real Clifford + T operators \(U_n(\mathbb{D[\sqrt{2}]})\)
class TwoPermutation repr => Real repr where
  h :: Int -> repr
  ch :: Int -> Int -> repr

-- | The Unreal Clifford + T operators \(U_n(\mathbb{D}[i\sqrt{2}])\)
class TwoPermutation repr => Unreal repr where
  f :: Int -> repr

-- | The Gaussian Clifford + T operators \(U_n(\mathbb{D}[i])\)
class FourPermutation repr => Gaussian repr where
  wh :: Int -> repr

-- | The Clifford + T operators \(U_n(\mathbb{D}[i])\)
class (FourPermutation repr, Real repr) => CliffordT repr

{-----------------------------
 Circuits
 -----------------------------}

-- | Circuit concatenation
class Circuit repr where
  (@@) :: repr -> repr -> repr

infixr 6 @@

{-----------------------------
 Dagger
 -----------------------------}

-- | Syntactic dagger
class Dagger repr where
  dagger :: repr -> repr

-- | An implementation of "Dagger" over circuits
type Daggered = Bool
instance (Dagger repr, Circuit repr) => Circuit (Daggered -> repr) where
  (c @@ c') False = (c False) @@ (c' False)
  (c @@ c') True  = (c' True) @@ (c True)

instance (Dagger repr) => Dagger (Daggered -> repr) where
  dagger c b = c $ not b

instance Gate repr => Gate (Daggered -> repr) where
  identity _b = identity

instance Permutation repr => Permutation (Daggered -> repr) where
  x i _b       = x i
  cx i j _b    = cx i j
  ccx i j k _b = ccx i j k

instance TwoPermutation repr => TwoPermutation (Daggered -> repr) where
  z i _b = z i

instance (FourPermutation repr, Dagger repr) => FourPermutation (Daggered -> repr) where
  s i False = s i
  s i True  = dagger $ s i

instance (EightPermutation repr, Dagger repr) => EightPermutation (Daggered -> repr) where
  t i False = t i
  t i True  = dagger $ t i

instance Integral repr => Integral (Daggered -> repr) where
  hh i j _b = hh i j

instance Real repr => Real (Daggered -> repr) where
  h i _b    = h i
  ch i j _b = ch i j

instance (Gaussian repr, Dagger repr) => Gaussian (Daggered -> repr) where
  wh i False = wh i
  wh i True  = dagger $ wh i

instance (Unreal repr, Dagger repr) => Unreal (Daggered -> repr) where
  f i False = f i
  f i True  = dagger $ f i

-- | Pushes daggers onto gates
distDagger :: Dagger repr => (Daggered -> repr) -> repr
distDagger c = c False

-- | Non-syntactic dagger
inv :: Dagger repr => (Daggered -> repr) -> repr
inv c = c True

{-----------------------------
 Printing
 -----------------------------}

instance Gate String where
  identity = "\x03B5"

instance Permutation String where
  x i       = "X " ++ (show i)
  cx i j    = "CNOT " ++ (show i) ++ " " ++ (show j)
  ccx i j k = "Toffoli " ++ (show i) ++ " " ++ (show j) ++ " " ++ (show k)

instance TwoPermutation String where
  z i = "Z " ++ (show i)

instance FourPermutation String where
  s i = "S " ++ (show i)

instance EightPermutation String where
  t i = "T " ++ (show i)

instance Integral String where
  hh i j  = "H\x2297H " ++ (show i) ++ " " ++ (show j)

instance Real String where
  h i    = "H " ++ (show i)
  ch i j = "CH " ++ (show i) ++ " " ++ (show j)

instance Unreal String where
  f i    = "F " ++ (show i)

instance Gaussian String where
  wh i    = "\x03C9H " ++ (show i)

instance CliffordT String

instance Circuit String where
  a @@ b = a ++ "; " ++ b

instance Dagger String where
  dagger a = "(" ++ a ++ ")^*"

{-----------------------------
 Matrices
 -----------------------------}

-- | Convert a type-level power of 2 to a term-level exponent
natLog :: forall n. Nat n => Integer
natLog = case log2 (nat @n undefined) of
  Just x  -> x
  Nothing -> error "Not a power of 2"

-- | Convenience functions
make :: (Nat n, Nat m) => (Int -> Int -> r) -> Matrix n m r
make f = matrix_map (uncurry f) matrix_enum

-- | General kronecker product. Takes an integer specifying the number
--   of qubits, an ordered list of /m/ qubits that are being acted on
--   non-trivially, and a /2^m/ by /2^m/ matrix
kron :: (Nat n, Nat m, Num r) => Integer -> [Int] -> ((Int,Int) -> r) -> Matrix n m r
kron qubits indices mat = make (\i j -> maybe 0 id . liftM mat $ go i j) where
  go :: Int -> Int -> Maybe (Int, Int)
  go i j = foldM f (0,0) [0..(fromInteger qubits)-1] where
    f (a,b) q = case elemIndex q indices of
      Just q' -> Just (a .|. reduce q q' i, b .|. reduce q q' j)
      Nothing -> if valueAt q i == valueAt q j then Just (a,b) else Nothing
  reduce q q' i = if valueAt q i then 1 `shiftL` (qubits' - 1 - q') else 0
  valueAt q i = testBit i $ (fromInteger qubits)-1-q
  qubits' = length indices

instance (Nat n, Ring r) => Gate (Matrix n n r) where
  identity = 1

instance (Nat n, Ring r) => Permutation (Matrix n n r) where
  x i = kron (natLog @n) [i] f where
    f (a,b) = if a /= b then 1 else 0
  cx i j = kron (natLog @n) [i,j] f where
    f (a,b)
      | testBit a 1 /= testBit b 1 = 0
      | testBit a 1 && (testBit a 0 /= testBit b 0) = 1
      | not (testBit a 1) && (testBit a 0 == testBit b 0) = 1
      | otherwise = 0
  ccx i j k = kron (natLog @n) [i,j,k] f where
    f (a,b)
      | testBit a 2 /= testBit b 2 || testBit a 1 /= testBit b 1 = 0
      | testBit a 2 && testBit a 1 && (testBit a 0 /= testBit b 0) = 1
      | not (testBit a 2 && testBit a 1) && (testBit a 0 == testBit b 0) = 1
      | otherwise = 0

instance (Nat n, Ring r) => TwoPermutation (Matrix n n r) where
  z i = kron (natLog @n) [i] f where
    f (0,0) = 1
    f (1,1) = -1
    f _     = 0

instance (Nat n, ComplexRing r) => FourPermutation (Matrix n n r) where
  s j = kron (natLog @n) [j] f where
    f (0,0) = 1
    f (1,1) = i
    f _     = 0

instance (Nat n, ComplexRing r, RootHalfRing r, OmegaRing r) => EightPermutation (Matrix n n r) where
  t j = kron (natLog @n) [j] f where
    f (0,0) = 1
    f (1,1) = omega
    f _     = 0

instance (Nat n, HalfRing r) => Integral (Matrix n n r) where
  hh i j = kron (natLog @n) [i] f where
    f (a,b)
      | testBit a 0 && testBit b 0 && testBit a 1 && testBit b 1 = half
      | testBit a 0 && testBit b 0 = -half
      | testBit a 1 && testBit b 1 = -half
      | otherwise = half

instance (Nat n, RootHalfRing r) => Real (Matrix n n r) where
  h i = kron (natLog @n) [i] f where
    f (1,1) = -roothalf
    f _     = roothalf

instance (Nat n, HalfRing r, CplxRootTwoRing r) => Unreal (Matrix n n r) where
  f i = kron (natLog @n) [i] g where
    g (0,0) = half + half*iroottwo
    g (1,1) = -half + half*iroottwo
    g _     = half

instance (Nat n, HalfRing r, ComplexRing r) => Gaussian (Matrix n n r) where
  wh j = kron (natLog @n) [j] f where
    f (1,1) = -(1+i)*half
    f _     = (1+i)*half

instance (Nat n, ComplexRing r, RootHalfRing r) => CliffordT (Matrix n n r)

instance (Nat n, Ring r) => Circuit (Matrix n n r) where
  a @@ b = b .*. a

instance (Nat n, Adjoint r) => Dagger (Matrix n n r) where
  dagger a = adj a

{-------------------------------
 Examples
 -------------------------------}

examples :: () -> IO ()
examples () = do
  putStrLn $ ccx 1 2 3
  putStrLn $ x 1 @@ cx 1 2
  putStrLn $ x 1 @@ cx 1 2 @@ wh 1
  putStrLn $ dagger (z 1)
  putStrLn $ dagger (t 1)
  putStrLn $ dagger (z 1 @@ t 1)
  putStrLn $ distDagger $ dagger (z 1 @@ t 1)
  putStrLn $ inv (t 1)
  putStrLn $ inv (dagger $ t 1)
  putStrLn $ inv (z 1 @@ t 1)
  putStrLn $ inv (z 1 @@ (dagger $ t 1))
