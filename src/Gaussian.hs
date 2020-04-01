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
import Data.Bits

import Control.Monad

import Quantum.Synthesis.Matrix
import Quantum.Synthesis.Ring
import Quantum.Synthesis.MultiQubitSynthesis
import Quantum.Synthesis.EuclideanDomain

import Test.QuickCheck

{---------------------------------
 Rings
 ---------------------------------}

-- | Wrapper for newsynth's DComplex to give custom instances
--   for DenomExp and Residue
newtype DGauss = DGauss DComplex deriving (Eq, Num, HalfRing, ComplexRing)

instance Show DGauss where
  show (DGauss d) = show d

instance WholePart DGauss ZComplex where
  from_whole = DGauss . from_whole
  to_whole (DGauss d) = to_whole d

-- | Copy from Integral -- needed to efficiently
instance DenomExp Dyadic where
  denomexp = snd . decompose_dyadic
  denomexp_factor a k = a * 2^k

-- | This instance recontextualizes DenomExp as the (1+i)-lde
instance DenomExp DGauss where
  denomexp (DGauss a) = if k > 0 && euclid_divides (1 + i) b then 2*k - 1 else 2*k
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
data Generator =
    S !Int !Int
  | X !Int !Int
  | WH !Int !Int !Int
  deriving (Eq, Show, Ord)

-- | Categories with a dagger operator
class Dagger c where
  dagger :: c -> c

instance Dagger c => Dagger [c] where
  dagger = reverse . map dagger

instance Dagger Generator where
  dagger (S k i)    = S ((-k) `mod` 4) i
  dagger (WH k i j) = WH ((-k) `mod` 8) i j
  dagger x          = x

-- | Type class for conversion to matrices
class Num r => Matrixable c r | c -> r where
  toMatrix :: Nat n => c -> Matrix n n r

instance Matrixable c r => Matrixable [c] r where
  toMatrix = foldl' (\acc -> (acc .*.) . toMatrix) (fromInteger 1)

instance Matrixable Generator DGauss where
  toMatrix (S k j)    = onelevel_matrix (i^k) j
  toMatrix (X h j)    = twolevel_matrix (0, 1) (1, 0) h j
  toMatrix (WH k h j) = twolevel_matrix r1 r2 h j where
    ipow     = i^(k `div` 2)
    e        = (1+i)*half*ipow
    (r1, r2) = case k `mod` 2 of
      0 -> ((ipow, 0), (0, ipow))
      1 -> ((e, e), (e, -e))

{---------------------------------
 Exact synthesis
 ---------------------------------}
-- | Column reduction / state preparation with initial state \(e_i\)
synthesizeState :: Nat n => Int -> Vector n DGauss -> [Generator]
synthesizeState b = go  . list_of_vector where
  go :: [DGauss] -> [Generator]
  go vec = case denomexp_decompose vec of
    (xs, 0) -> sCorr ++ xCorr where
      a     = case findIndex (/= 0) xs  of
        Just a -> a
        Nothing -> error $ "Not a unit vector: " ++ show vec
      sCorr = case (xs!!a) of
        v | v == 1 -> []
          | v == i -> [S 1 a]
          | v == -1 -> [S 2 a]
          | v == -i -> [S 3 a]
      xCorr = if a == b then [] else [X a b]
    (xs, k) -> s1 ++ s2 ++ hCorr ++ go vec' where
      (a,b) = case findIndices (\v -> (residue (v*v)) == 1) xs of
        (a:b:_) -> (a,b)
        _       -> error $ "Not a unit vector: " ++ show vec
      (s1,v) = if residue (xs!!a) == i then ([S 3 a], i*(vec!!a)) else ([], vec!!a)
      (s2,u) = if residue (xs!!b) == i then ([S 3 b], i*(vec!!b)) else ([], vec!!b)
      hCorr = [WH 7 a b]
      vec'  = map f (zip [0..] vec) where
        f (c, w)
          | c == a    = (v + u)*(1 + i)*half
          | c == b    = (v - u)*(1 + i)*half
          | otherwise = w

-- | The Gaussian synthesis algorithm
synthesize :: Nat n => Matrix n n DGauss -> [Generator]
synthesize m = go (unMatrix m) 0 where
  go :: (Nat n') => Vector n (Vector n' DGauss) -> Integer -> [Generator]
  go Nil i         = []
  go (Cons c cs) i = gates ++ go (unMatrix m') (i+1)
    where
      gates = synthesizeState (fromInteger i) c
      m'    = (toMatrix $ dagger gates) .*. (Matrix cs)

{---------------------------------
 Testing
 ---------------------------------}
-- | Random i phase
genS :: Int -> Gen Generator
genS n
  | n <= 0 = error $ "Invalid bound " ++ show n ++ " for random S"
  | otherwise = do
    k <- choose (0,3)
    j <- choose (0,n-1)
    return $ S k j

-- | Random row swap
genX :: Int -> Gen Generator
genX n
  | n <= 1 = error $ "Invalid bound " ++ show n ++ " for random X"
  | otherwise = do
    i <- choose (0,n-1)
    j <- choose (0,n-1) `suchThat` (/= i)
    return $ X i j

-- | Random \(\omega H\)
genWH :: Int -> Gen Generator
genWH n
  | n <= 1 = error $ "Invalid bound " ++ show n ++ " for random WH"
  | otherwise = do
    k <- choose (0,7)
    i <- choose (0,n-1)
    j <- choose (0,n-1) `suchThat` (/= i)
    return $ WH k i j

instance Arbitrary Generator where
  arbitrary = sized go where
    go n
      | n < 1 = error $ "Can't generate a generator on " ++ show n ++ " dimensions"
      | 1 <= n && n < 2 = genS n
      | otherwise       = oneof [genS n, genX n, genWH n]
    
instance Nat n => Arbitrary (Matrix n n DGauss) where
  arbitrary = liftM toMatrix $ listOf (resize (getn nnat) gen) where
    gen  :: Gen Generator
    gen  = arbitrary
    getn :: NNat n -> Int
    getn = fromInteger . fromNNat 

-- | Checks correctness of the synthesis algorithm
synthesisCorrect :: Nat n => Matrix n n DGauss -> Bool
synthesisCorrect m = m == (toMatrix $ synthesize m)

-- | Test suite
runTests _ = do
  quickCheck (synthesisCorrect :: Matrix Two Two DGauss -> Bool)
  quickCheck (synthesisCorrect :: Matrix Four Four DGauss -> Bool)
  quickCheck (synthesisCorrect :: Matrix Eight Eight DGauss -> Bool)

gen :: IO (Matrix Eight Eight DGauss)
gen = generate $ resize 50 arbitrary
