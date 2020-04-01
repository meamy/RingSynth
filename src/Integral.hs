{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-|
Module      : Integral
Description : Exact synthesis over \(\mathbb{D}\)
Maintainer  : matt.e.amy@gmail.com
Stability   : experimental
Portability : portable
-}

module Quantum.Synthesis.Integral where

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

-- | This instance recontextualizes DenomExp as the 2-lde
instance DenomExp Dyadic where
  denomexp = snd . decompose_dyadic
  denomexp_factor a k = (fromInteger $ 1 `shiftL` (fromInteger k)) * a

{---------------------------------
 Generators
 ---------------------------------}

-- | The generators of the integral circuit group
data Generator =
    Z !Int
  | X !Int !Int
  | HH !Int !Int !Int !Int
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

instance Matrixable Generator Dyadic where
  toMatrix (Z i)        = onelevel_matrix (-1) i
  toMatrix (X i j)      = twolevel_matrix (0, 1) (1, 0) i j
  toMatrix (HH a b c d) = matrix_of_function f where
    f x y
      | x == a && (y == a || y == b || y == c || y == d) = half
      | x == b && (y == a || y == c)                     = half
      | x == b && (y == b || y == d)                     = -half
      | x == c && (y == a || y == b)                     = half
      | x == c && (y == c || y == d)                     = -half
      | x == d && (y == a || y == d)                     = half
      | x == d && (y == c || y == b)                     = -half
      | x == y                                           = 1
      | otherwise                                        = 0

{---------------------------------
 Exact synthesis
 ---------------------------------}

-- | Column reduction / state preparation with initial state \(e_i\)
synthesizeState :: Nat n => Int -> Vector n Dyadic -> [Generator]
synthesizeState i = go . denomexp_decompose . list_of_vector where
  go :: ([Integer], Integer) -> [Generator]
  go (xs, 0) = zCorr ++ xCorr where
    (j, v) = case filter ((/= 0) . snd) (zip [0..] xs) of
      [x] -> x
      _   -> error $ "Not a unit vector: " ++ show xs
    zCorr = if v == -1 then [Z j] else []
    xCorr = if j == i then [] else [X i j]
  go (xs, k) = zCorr ++ hCorr ++ go (denomexp_decompose xs') where
    [a,b,c,d] = case filter (\(_, v) -> (v*v) `mod` 4 == 1) (zip [0..] xs) of
      (a:b:c:d:_) -> [a,b,c,d]
      _           -> error $ "Not a unit vector: " ++ show xs
    (zCorr, vs) = foldr f ([], []) [a,b,c,d] where
      f (j, v) (za, va) = if v `mod` 4 == 3 then ((Z j):za, (-v):va) else (za, v:va)
    hCorr    = [HH (fst a) (fst b) (fst c) (fst d)]
    xs'      = map f (zip [0..] xs) where
      f (j, v)
        | j == fst a = Dyadic ((vs!!0 + vs!!1 + vs!!2 + vs!!3) `div` 2) k
        | j == fst b = Dyadic ((vs!!0 - vs!!1 + vs!!2 - vs!!3) `div` 2) k
        | j == fst c = Dyadic ((vs!!0 + vs!!1 - vs!!2 - vs!!3) `div` 2) k
        | j == fst d = Dyadic ((vs!!0 - vs!!1 - vs!!2 + vs!!3) `div` 2) k
        | otherwise  = Dyadic v k

-- | The Integral synthesis algorithm
synthesize :: Nat n => Matrix n n Dyadic -> [Generator]
synthesize m = go (unMatrix m) 0 where
  go :: (Nat n') => Vector n (Vector n' Dyadic) -> Integer -> [Generator]
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
genHH :: Int -> Gen Generator
genHH n
  | n <= 3 = error $ "Invalid bound " ++ show n ++ " for random HH"
  | otherwise = do
    a <- choose (0,n-1)
    b <- choose (0,n-1) `suchThat` (/= a)
    c <- choose (0,n-1) `suchThat` (`notElem` [a,b])
    d <- choose (0,n-1) `suchThat` (`notElem` [a,b,c])
    return $ HH a b c d

instance Arbitrary Generator where
  arbitrary = sized go where
    go n
      | n < 1 = error $ "Can't generate a generator on " ++ show n ++ " dimensions"
      | 1 <= n && n < 2 = genZ n
      | 2 <= n && n < 4 = oneof [genZ n, genX n]
      | otherwise = oneof [genZ n, genX n, genHH n]
    
instance Nat n => Arbitrary (Matrix n n Dyadic) where
  arbitrary = liftM toMatrix $ listOf (resize (getn nnat) gen) where
    gen  :: Gen Generator
    gen  = arbitrary
    getn :: NNat n -> Int
    getn = fromInteger . fromNNat 

-- | Checks correctness of the synthesis algorithm
synthesisCorrect :: Nat n => Matrix n n Dyadic -> Bool
synthesisCorrect m = m == (toMatrix $ synthesize m)

-- | Test suite
runTests _ = do
  quickCheck (synthesisCorrect :: Matrix Two Two Dyadic -> Bool)
  quickCheck (synthesisCorrect :: Matrix Four Four Dyadic -> Bool)
  quickCheck (synthesisCorrect :: Matrix Eight Eight Dyadic -> Bool)
