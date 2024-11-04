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

module Quantum.Synthesis.Unreal (UnrealGen(..)) where

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

-- | The generators of the unreal circuit group
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

-- * Synthesis algorithm
-- ---------------------------------------

instance Synthesizable DCplxRootTwo ZCplxRootTwo UnrealGen where
  initialize e xs = zCorr ++ xCorr where
      a     = case findIndex (/= 0) xs  of
        Just a' -> a'
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
      
-- * Arbitrary instances
-- ---------------------------------------

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
--runTests :: () -> IO ()
--runTests () = do
--  quickCheck (prop_correct :: Matrix Two Two DCplxRootTwo -> Bool)
--  quickCheck (prop_correct :: Matrix Four Four DCplxRootTwo -> Bool)
--  quickCheck (prop_correct :: Matrix Eight Eight DCplxRootTwo -> Bool)
