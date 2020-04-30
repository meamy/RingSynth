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
import Control.Monad

import Test.QuickCheck

import Quantum.Synthesis.Matrix
import Quantum.Synthesis.Ring
import Quantum.Synthesis.MultiQubitSynthesis

import Quantum.Synthesis.Exact


-- * Generators
-- ---------------------------------------

-- | The generators of the real circuit group
data RealGen =
    Z !Int
  | X !Int !Int
  | H !Int !Int
  deriving (Eq, Show, Ord)

instance Adjoint RealGen where
  adj = id

instance ToMatrix RealGen DRootTwo where
  toMatrix (Z a)   = onelevel_matrix (-1) a
  toMatrix (X a b) = twolevel_matrix (0, 1) (1, 0) a b
  toMatrix (H a b) =
    twolevel_matrix (roothalf, roothalf) (roothalf, -roothalf) a b

-- * Synthesis algorithm
-- ---------------------------------------

instance Synthesizable DRootTwo ZRootTwo RealGen where
  initialize e xs = zCorr ++ xCorr where
    a = case findIndex (\v -> v /= 0) xs of
      Just b  -> b
      Nothing -> error $ "Not a unit vector: " ++ show xs
    zCorr = if (xs!!a) == -1 then [Z a] else []
    xCorr = if a == e then [] else [X e a]
  reduce xs = f . equalPairs . findIndices oddRes $ xs where
    oddRes v      = residue v == 1 || residue v == 1 + roottwo
    sameRes (a,b) = residue (xs!!a) == residue (xs!!b)
    equalPairs is = filter sameRes [(a,b) | a <- is, b <- is, a < b]
    f []          = []
    f ((a,b):xs') = (H a b):(f xs')

-- * Arbitrary instances
-- ---------------------------------------

-- | Random (-1) phase
genZ :: Int -> Gen RealGen
genZ n
  | n <= 0 = error $ "Invalid bound " ++ show n ++ " for random Z"
  | otherwise = choose (0,n-1) >>= \a -> return $ Z a

-- | Random row swap
genX :: Int -> Gen RealGen
genX n
  | n <= 1 = error $ "Invalid bound " ++ show n ++ " for random X"
  | otherwise = do
    a <- choose (0,n-1)
    b <- choose (0,n-1) `suchThat` (/= a)
    return $ X a b

-- | Random row swap
genH :: Int -> Gen RealGen
genH n
  | n <= 1 = error $ "Invalid bound " ++ show n ++ " for random HH"
  | otherwise = do
    a <- choose (0,n-1)
    b <- choose (0,n-1) `suchThat` (/= a)
    return $ H a b

instance Arbitrary RealGen where
  arbitrary = sized go where
    go n
      | n < 1 = error $ "Can't generate a generator on " ++ show n ++ " dimensions"
      | 1 <= n && n < 2 = genZ n
      | otherwise       = oneof [genZ n, genX n, genH n]
    
instance Nat n => Arbitrary (Matrix n n DRootTwo) where
  arbitrary = liftM toMatrix $ listOf (resize (getn nnat) gen) where
    gen  :: Gen RealGen
    gen  = arbitrary
    getn :: NNat n -> Int
    getn = fromInteger . fromNNat 

-- | Test suite
runTests :: () -> IO ()
runTests () = do
  quickCheck (prop_correct :: Matrix Two Two DRootTwo -> Bool)
  quickCheck (prop_correct :: Matrix Four Four DRootTwo -> Bool)
  quickCheck (prop_correct :: Matrix Eight Eight DRootTwo -> Bool)
