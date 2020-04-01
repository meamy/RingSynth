{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-|
Module      : Real
Description : Exact synthesis over \(\mathbb{D}[\sqrt{2}]\)
Maintainer  : matt.e.amy@gmail.com
Stability   : experimental
Portability : portable
-}

module Quantum.Synthesis.Real where

import Data.List
import Data.Bits

import Control.Monad

import Quantum.Synthesis.Matrix
import Quantum.Synthesis.Ring
import Quantum.Synthesis.MultiQubitSynthesis

import Test.QuickCheck

{---------------------------------
 Rings
 ---------------------------------}

-- | The type of residues \(\mathbb{Z}[\sqrt{2}]/\mathbb{Z}_2\)
type Z2RootTwo = RootTwo Z2
  
{---------------------------------
 Generators
 ---------------------------------}

-- | The generators of the integral circuit group
data Generator =
    Z !Int
  | X !Int !Int
  | H !Int !Int
  deriving (Eq, Show, Ord)

-- | Categories with a dagger operator
class Dagger c where
  dagger :: c -> c

instance Dagger c => Dagger [c] where
  dagger = reverse . map dagger

instance Dagger Generator where
  dagger = id

-- | Type class for conversion to matrices
class Num r => Matrixable c r | c -> r where
  toMatrix :: Nat n => c -> Matrix n n r

instance Matrixable c r => Matrixable [c] r where
  toMatrix = foldl' (\acc -> (acc .*.) . toMatrix) (fromInteger 1)

instance Matrixable Generator DRootTwo where
  toMatrix (Z i)   = onelevel_matrix (-1) i
  toMatrix (X i j) = twolevel_matrix (0, 1) (1, 0) i j
  toMatrix (H i j) =
    twolevel_matrix (roothalf, roothalf) (roothalf, -roothalf) i j

{---------------------------------
 Exact synthesis
 ---------------------------------}

-- | Column reduction / state preparation with initial state \(e_i\)
synthesizeState :: Nat n => Int -> Vector n DRootTwo -> [Generator]
synthesizeState i = go  . list_of_vector where
  go :: [DRootTwo] -> [Generator]
  go vec = case denomexp_decompose vec of
    (xs, 0) -> zCorr ++ xCorr where
      j     = case findIndex (/= 0) xs  of
        Just j -> j
        Nothing -> error $ "Not a unit vector: " ++ show vec
      zCorr = if xs!!j == -1 then [Z j] else []
      xCorr = if j == i then [] else [X i j]
    (xs, k) -> hCorr ++ go vec' where
      allPairs = [(i,j) | i <- [0..n-1], j <- [0..n-1], i /= j] where
        n = length xs
      (i,j) = case find (f . \(i,j) -> residue (xs!!i, xs!!j)) allPairs of
        Just (i,j) -> (i,j)
        Nothing    -> error $ "Not a unit vector: " ++ show xs
        where f (x,y) = x == y && (x == 1 || x == 1 + roottwo)
      hCorr = [H i j]
      vec'  = map f (zip [0..] vec) where
        f (h, w)
          | h == i    = roothalf*(w + vec!!j)
          | h == j    = roothalf*(vec!!i - w)
          | otherwise = w

-- | The Integral synthesis algorithm
synthesize :: Nat n => Matrix n n DRootTwo -> [Generator]
synthesize m = go (unMatrix m) 0 where
  go :: (Nat n') => Vector n (Vector n' DRootTwo) -> Integer -> [Generator]
  go Nil i         = []
  go (Cons c cs) i = gates ++ go (unMatrix m') (i+1)
    where
      gates = synthesizeState (fromInteger i) c
      m'    = (toMatrix $ dagger gates) .*. (Matrix cs)

{---------------------------------
 Testing
 ---------------------------------}
-- | Random (-1) phase
genZ :: Int -> Gen Generator
genZ n
  | n <= 0 = error $ "Invalid bound " ++ show n ++ " for random Z"
  | otherwise = choose (0,n-1) >>= \j -> return $ Z j

-- | Random row swap
genX :: Int -> Gen Generator
genX n
  | n <= 1 = error $ "Invalid bound " ++ show n ++ " for random X"
  | otherwise = do
    i <- choose (0,n-1)
    j <- choose (0,n-1) `suchThat` (/= i)
    return $ X i j

-- | Random row swap
genH :: Int -> Gen Generator
genH n
  | n <= 1 = error $ "Invalid bound " ++ show n ++ " for random HH"
  | otherwise = do
    i <- choose (0,n-1)
    j <- choose (0,n-1) `suchThat` (/= i)
    return $ H i j

instance Arbitrary Generator where
  arbitrary = sized go where
    go n
      | n < 1 = error $ "Can't generate a generator on " ++ show n ++ " dimensions"
      | 1 <= n && n < 2 = genZ n
      | otherwise       = oneof [genZ n, genX n, genH n]
    
instance Nat n => Arbitrary (Matrix n n DRootTwo) where
  arbitrary = liftM toMatrix $ listOf (resize (getn nnat) gen) where
    gen  :: Gen Generator
    gen  = arbitrary
    getn :: NNat n -> Int
    getn = fromInteger . fromNNat 

-- | Checks correctness of the synthesis algorithm
synthesisCorrect :: Nat n => Matrix n n DRootTwo -> Bool
synthesisCorrect m = m == (toMatrix $ synthesize m)

-- | Test suite
runTests _ = do
  quickCheck (synthesisCorrect :: Matrix Two Two DRootTwo -> Bool)
  quickCheck (synthesisCorrect :: Matrix Four Four DRootTwo -> Bool)
  quickCheck (synthesisCorrect :: Matrix Eight Eight DRootTwo -> Bool)

gen :: IO (Matrix Eight Eight DRootTwo)
gen = generate $ resize 50 arbitrary
