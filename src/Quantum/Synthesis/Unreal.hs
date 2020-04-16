{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

{-|
Module      : Unreal
Description : Exact synthesis over \(\mathbb{D}[i\sqrt{2}]\)
Maintainer  : matt.e.amy@gmail.com
Stability   : experimental
Portability : portable
-}

module Quantum.Synthesis.Unreal where

import Data.List

import Control.Monad

import Quantum.Synthesis.Matrix
import Quantum.Synthesis.Ring
import Quantum.Synthesis.MultiQubitSynthesis
import Quantum.Synthesis.EuclideanDomain

import Test.QuickCheck

import Quantum.Synthesis.Exact

{---------------------------------
 Rings
 ---------------------------------}

-- | Class of rings with \(i\sqrt{2}\)
class Ring a => CplxRootTwoRing a where
  iroottwo :: a
  fromZCplxRootTwo :: ZCplxRootTwo -> a
  -- defaults
  fromZCplxRootTwo (CplxRootTwo a b) = a' + b'*iroottwo where
    a' = fromInteger a
    b' = fromInteger b

instance (CplxRootTwoRing a, Nat n) => CplxRootTwoRing (Matrix n n a) where
  iroottwo = scalarmult iroottwo 1

-- | The ring \(R[1/i\sqrt{2}]\), where \(R\) is any ring.
--   The value CplxRootTwo a b represents \(a + bi\sqrt{2}\)
data CplxRootTwo a = CplxRootTwo !a !a deriving (Eq)

instance (Eq a, Num a) => Num (CplxRootTwo a) where
  CplxRootTwo a b + CplxRootTwo a' b' = CplxRootTwo (a + a') (b + b')
  CplxRootTwo a b * CplxRootTwo a' b' = CplxRootTwo a'' b'' where
    a'' = a * a' - 2 * b * b'
    b'' = a * b' + a' * b
  negate (CplxRootTwo a b)            = CplxRootTwo (-a) (-b)
  abs x                               = x
  signum x                            = 1
  fromInteger n                       = CplxRootTwo (fromInteger n) 0

instance (Show a, Eq a, Ring a) => Show (CplxRootTwo a) where
  showsPrec d (CplxRootTwo a 0)    = showsPrec d a
  showsPrec d (CplxRootTwo 0 1)    = showString "iroottwo"
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
  norm (CplxRootTwo a b) = (norm a)^2 + 2 * (norm b)^2

instance Residue a b => Residue (CplxRootTwo a) (CplxRootTwo b) where
  residue (CplxRootTwo a b) = CplxRootTwo (residue a) (residue b)

-- | The ring \(\mathbb{Z}[i\sqrt{2}]\)
type ZCplxRootTwo = CplxRootTwo Integer

-- | The ring \(\mathbb{D}[i\sqrt{2}]\)
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

-- | Defined as \(i\sqrt{2}\) denominator exponents
instance DenomExp DCplxRootTwo where
  denomexp (CplxRootTwo a b) = maximum [2*k, 2*l-1] where
    (_,k) = decompose_dyadic a
    (_,l) = decompose_dyadic b
  denomexp_factor a k = a * iroottwo^k

-- | The ring of integers mod 4 \(\mathbb{Z}_4\)
newtype Z4 = Z4 Integer deriving (Eq, Ord, Show)

instance Num Z4 where
  Z4 a + Z4 b   = Z4 $ (a + b) `mod` 4
  Z4 a * Z4 b   = Z4 $ (a * b) `mod` 4
  negate (Z4 a) = Z4 $ (-a) `mod` 4
  signum (Z4 a) = Z4 $ signum (a `mod` 4)
  abs (Z4 a)    = Z4 $ (a `mod` 4)
  fromInteger n = Z4 $ (n `mod` 4)

-- | The type of residues \(\mathbb{Z}[i\sqrt{2}]/2\mathbb{Z}\)
type Z2CplxRootTwo = CplxRootTwo Z2

-- | Take the residue of \(a\in\mathbb{Z}[i\sqrt{2}]\) mod \(2i\sqrt{2}\)
residue2irt2 :: ZCplxRootTwo -> (Z4, Z2)
residue2irt2 p = (fromInteger a, fromInteger b) where
  (_, CplxRootTwo a b) = divmod p (2*iroottwo)

{---------------------------------
 Generators
 ---------------------------------}

-- | The generators of the integral circuit group
data UnrealGen =
    Z !Int
  | X !Int !Int
  | F !Int !Int !Int
  deriving (Eq, Show, Ord)

instance Adjoint UnrealGen where
  adj (F k i j) = F ((-k) `mod` 8) i j
  adj x         = x

instance ToMatrix UnrealGen DCplxRootTwo where
  toMatrix (Z a)     = onelevel_matrix (-1) a
  toMatrix (X a b)   = twolevel_matrix (0, 1) (1, 0) a b
  toMatrix (F k a b) = twolevel_matrix (w, x) (y, z) a b where
    [[w, x], [y, z]] = rows_of_matrix $ mat^k
    mat = matrix2x2 (half + half*iroottwo, half) (half, -half + half*iroottwo)

{---------------------------------
 Exact synthesis
 ---------------------------------}

instance Synthesizable DCplxRootTwo ZCplxRootTwo UnrealGen where
  initialize e xs = zCorr ++ xCorr where
      a     = case findIndex (/= 0) xs  of
        Just a -> a
        Nothing -> error $ "Not a unit vector: " ++ show xs
      zCorr = if xs!!a == -1 then [Z a] else []
      xCorr = if a == e then [] else [X a e]
  reduce xs = f $ findIndices (\v -> (residue $ (adj v)*v) == 1) xs where
    f []        = []
    f (a:b:xs') = corr ++ f xs' where
      corr = case residue (xs!!a) == residue (xs!!b) of
        True  -> [F 6 a b]
        False -> zCorr ++ xCorr ++ [F 7 a b] where
          zCorr = map Z $ filter (\j -> fst (residue2irt2 (xs!!j)) == 3) [a,b]
          xCorr = if snd (residue2irt2 (xs!!a)) == 0 then [X a b] else []
    f  _        = error $ "Not a unit vector: " ++ show xs
      
{---------------------------------
 Testing
 ---------------------------------}

-- | Random (-1) phase
genZ :: Int -> Gen UnrealGen
genZ n
  | n <= 0 = error $ "Invalid bound " ++ show n ++ " for random Z"
  | otherwise = do
    a <- choose (0,n-1)
    return $ Z a

-- | Random row swap
genX :: Int -> Gen UnrealGen
genX n
  | n <= 1 = error $ "Invalid bound " ++ show n ++ " for random X"
  | otherwise = do
    a <- choose (0,n-1)
    b <- choose (0,n-1) `suchThat` (/= a)
    return $ X a b

-- | Random F
genF :: Int -> Gen UnrealGen
genF n
  | n <= 1 = error $ "Invalid bound " ++ show n ++ " for random F"
  | otherwise = do
    k <- choose (0,7)
    a <- choose (0,n-1)
    b <- choose (0,n-1) `suchThat` (/= a)
    return $ F k a b

instance Arbitrary UnrealGen where
  arbitrary = sized go where
    go n
      | n < 1 = error $ "Can't generate a generator on " ++ show n ++ " dimensions"
      | 1 <= n && n < 2 = genZ n
      | otherwise       = oneof [genZ n, genX n, genF n]
    
instance Nat n => Arbitrary (Matrix n n DCplxRootTwo) where
  arbitrary = liftM toMatrix $ listOf (resize (getn nnat) gen) where
    gen  :: Gen UnrealGen
    gen  = arbitrary
    getn :: NNat n -> Int
    getn = fromInteger . fromNNat 

-- | Test suite
runTests :: () -> IO ()
runTests () = do
  quickCheck (prop_correct :: Matrix Two Two DCplxRootTwo -> Bool)
  quickCheck (prop_correct :: Matrix Four Four DCplxRootTwo -> Bool)
  quickCheck (prop_correct :: Matrix Eight Eight DCplxRootTwo -> Bool)
