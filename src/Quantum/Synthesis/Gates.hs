{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PostfixOperators #-}

{-|
Module      : Gates
Description : Gates & gate hierarchies
Maintainer  : matt.e.amy@gmail.com
Stability   : experimental
Portability : portable
-}

module Quantum.Synthesis.Gates where

import Prelude hiding (Real, Integral)

{-----------------------------
 (Polymorphic) Gates
 -----------------------------}

-- | Empty class
class Gate repr

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

instance Gate repr => Gate (Daggered -> repr)

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
  h i _b = h i

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

instance Gate String

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

instance Unreal String where
  f i    = "F " ++ (show i)

instance Gaussian String where
  wh i    = "\x03C9H " ++ (show i)

instance CliffordT String

instance Circuit String where
  a @@ b = a ++ "; " ++ b

instance Dagger String where
  dagger a = "(" ++ a ++ ")^*"

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
