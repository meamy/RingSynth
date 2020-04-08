{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

{-|
Module      : Gaussian
Description : Exact synthesis over \(\mathbb{D}[i]\)
Maintainer  : matt.e.amy@gmail.com
Stability   : experimental
Portability : portable
-}

module Quantum.Synthesis.Gaussian where

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

-- | Wrapper for newsynth's DComplex to give custom instances
--   for DenomExp and Residue
newtype DGaussian = DGaussian DComplex
  deriving (Eq, Num, HalfRing, ComplexRing, Adjoint)

instance Show DGaussian where
  show (DGaussian d) = show d

instance WholePart DGaussian ZComplex where
  from_whole = DGaussian . from_whole
  to_whole (DGaussian d) = to_whole d

-- | Copy from Integral -- needed to efficiently
instance DenomExp Dyadic where
  denomexp = snd . decompose_dyadic
  denomexp_factor a k = a * 2^k

-- | This instance recontextualizes DenomExp as the (1+i)-lde
instance DenomExp DGaussian where
  denomexp (DGaussian a) = if k > 0 && euclid_divides (1 + i) b then 2*k - 1 else 2*k
    where (b, k) = denomexp_decompose a
  denomexp_factor a k
    | k `mod` 2 == 0 = a * 2^(k `div` 2)
    | otherwise      = a * (1 + i) * 2^((k-1) `div` 2)

-- | The type of residues \(\mathbb{Z}[i]/2\mathbb{Z}\)
type Z2Complex = Cplx Z2
  
{---------------------------------
 Generators
 ---------------------------------}

-- | The generators of the integral circuit group
data GaussianGen =
    S !Int !Int
  | X !Int !Int
  | WH !Int !Int !Int
  deriving (Eq, Show, Ord)

instance Adjoint GaussianGen where
  adj (S k a)    = S ((-k) `mod` 4) a
  adj (WH k a b) = WH ((-k) `mod` 8) a b
  adj x          = x

instance ToMatrix GaussianGen DGaussian where
  toMatrix (S k a)    = onelevel_matrix (i^k) a
  toMatrix (X a b)    = twolevel_matrix (0, 1) (1, 0) a b
  toMatrix (WH k a b) = twolevel_matrix (w, x) (y, z) a b where
    [[w, x], [y, z]] = rows_of_matrix $ mat^k
    mat = matrix2x2 ((1+i)*half, (1+i)*half) ((1+i)*half, -(1+i)*half)

{---------------------------------
 Exact synthesis
 ---------------------------------}

instance Synthesizable DGaussian ZComplex GaussianGen where
  initialize e xs = sCorr ++ xCorr where
      a     = case findIndex (/= 0) xs  of
        Just a  -> a
        Nothing -> error $ "Not a unit vector: " ++ show xs
      sCorr = case (xs!!a) of
        v | v == 1 -> []
          | v == i -> [S 1 a]
          | v == -1 -> [S 2 a]
          | v == -i -> [S 3 a]
      xCorr = if a == e then [] else [X a e]
  reduce xs = f $ findIndices (\v -> residue (v*v) == 1) xs where
    f []        = []
    f (a:b:xs') = sCorr ++ [WH 7 a b] ++ f xs' where
      sCorr = map (S 3) . filter (\j -> residue (xs!!j) == i) $ [a,b]
    f _             = error $ "Not a unit vector: " ++ show xs

{---------------------------------
 Testing
 ---------------------------------}
-- | Random i phase
genS :: Int -> Gen GaussianGen
genS n
  | n <= 0 = error $ "Invalid bound " ++ show n ++ " for random S"
  | otherwise = do
    k <- choose (0,3)
    a <- choose (0,n-1)
    return $ S k a

-- | Random row swap
genX :: Int -> Gen GaussianGen
genX n
  | n <= 1 = error $ "Invalid bound " ++ show n ++ " for random X"
  | otherwise = do
    a <- choose (0,n-1)
    b <- choose (0,n-1) `suchThat` (/= a)
    return $ X a b

-- | Random \(\omega H\)
genWH :: Int -> Gen GaussianGen
genWH n
  | n <= 1 = error $ "Invalid bound " ++ show n ++ " for random WH"
  | otherwise = do
    k <- choose (0,7)
    a <- choose (0,n-1)
    b <- choose (0,n-1) `suchThat` (/= a)
    return $ WH k a b

instance Arbitrary GaussianGen where
  arbitrary = sized go where
    go n
      | n < 1 = error $ "Can't generate a generator on " ++ show n ++ " dimensions"
      | 1 <= n && n < 2 = genS n
      | otherwise       = oneof [genS n, genX n, genWH n]
    
instance Nat n => Arbitrary (Matrix n n DGaussian) where
  arbitrary = liftM toMatrix $ listOf (resize (getn nnat) gen) where
    gen  :: Gen GaussianGen
    gen  = arbitrary
    getn :: NNat n -> Int
    getn = fromInteger . fromNNat 

-- | Test suite
runTests :: () -> IO ()
runTests () = do
  quickCheck (prop_correct :: Matrix Two Two DGaussian -> Bool)
  quickCheck (prop_correct :: Matrix Four Four DGaussian -> Bool)
  quickCheck (prop_correct :: Matrix Eight Eight DGaussian -> Bool)