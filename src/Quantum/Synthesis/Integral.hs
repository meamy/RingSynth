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

import Control.Monad

import Test.QuickCheck

import Quantum.Synthesis.Matrix
import Quantum.Synthesis.Ring
import Quantum.Synthesis.MultiQubitSynthesis

import Quantum.Synthesis.Exact
import Quantum.Synthesis.MoreRings

-- * Generators
-- ---------------------------------------

-- | The generators of the integral circuit group
data DyadicGen =
    Z !Int
  | X !Int !Int
  | HH !Int !Int !Int !Int
  deriving (Eq, Show, Ord)

instance Adjoint DyadicGen where
  adj = id

instance ToMatrix DyadicGen Dyadic where
  toMatrix (Z a)        = onelevel_matrix (-1) a
  toMatrix (X a b)      = twolevel_matrix (0, 1) (1, 0) a b
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

-- * Synthesis algorithm
-- ---------------------------------------

instance Synthesizable Dyadic Integer DyadicGen where
  initialize e xs = zCorr ++ xCorr where
    a = case findIndex (\v -> v /= 0) xs of
      Just b  -> b
      Nothing -> error $ "Not a unit vector: " ++ show xs
    zCorr = if (xs!!a) == -1 then [Z a] else []
    xCorr = if a == e then [] else [X e a]
  reduce xs = f $ findIndices (\v -> (v*v) `mod` 4 == 1) xs where
    f []            = []
    f (a:b:c:d:xs') = zCorr ++ [HH a b c d] ++ f xs' where
      zCorr = map Z . filter (\j -> (xs!!j) `mod` 4 == 3) $ [a,b,c,d]
    f _             = error $ "Not a unit vector: " ++ show xs

-- * Arbitrary instances
-- ---------------------------------------

-- | Random (-1) phase
genZ :: Int -> Gen DyadicGen
genZ n
  | n <= 0 = error $ "Invalid bound " ++ show n ++ " for random Z"
  | otherwise = choose (0,n-1) >>= \a -> return $ Z a

-- | Random row swap
genX :: Int -> Gen DyadicGen
genX n
  | n <= 1 = error $ "Invalid bound " ++ show n ++ " for random X"
  | otherwise = do
    a <- choose (0,n-1)
    b <- choose (0,n-1) `suchThat` (/= a)
    return $ X a b

-- | Random row swap
genHH :: Int -> Gen DyadicGen
genHH n
  | n <= 3 = error $ "Invalid bound " ++ show n ++ " for random HH"
  | otherwise = do
    a <- choose (0,n-1)
    b <- choose (0,n-1) `suchThat` (/= a)
    c <- choose (0,n-1) `suchThat` (`notElem` [a,b])
    d <- choose (0,n-1) `suchThat` (`notElem` [a,b,c])
    return $ HH a b c d

instance Arbitrary DyadicGen where
  arbitrary = sized go where
    go n
      | n < 1 = error $ "Can't generate a generator on " ++ show n ++ " dimensions"
      | 1 <= n && n < 2 = genZ n
      | 2 <= n && n < 4 = oneof [genZ n, genX n]
      | otherwise = oneof [genZ n, genX n, genHH n]
    
instance Nat n => Arbitrary (Matrix n n Dyadic) where
  arbitrary = liftM toMatrix $ listOf (resize (getn nnat) gen) where
    gen  :: Gen DyadicGen
    gen  = arbitrary
    getn :: NNat n -> Int
    getn = fromInteger . fromNNat 

-- | Test suite
--runTests :: () -> IO ()
--runTests () = do
--  quickCheck (prop_correct :: Matrix Two Two Dyadic -> Bool)
--  quickCheck (prop_correct :: Matrix Four Four Dyadic -> Bool)
--  quickCheck (prop_correct :: Matrix Eight Eight Dyadic -> Bool)
