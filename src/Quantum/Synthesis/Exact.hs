{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-|
Module      : Exact
Description : Generic exact synthesis algorithm & tools
Maintainer  : matt.e.amy@gmail.com
Stability   : experimental
Portability : portable
-}

module Quantum.Synthesis.Exact(
  ToMatrix(..),
  Synthesizable(..),
  prop_correct)
where

import Data.List

import Quantum.Synthesis.Matrix
import Quantum.Synthesis.Ring

-- * Matrix-like data
-- ---------------------------------------

-- | Type of things that can be converted to a matrix
class Ring r => ToMatrix g r | g -> r where
  toMatrix :: Nat n => g -> Matrix n n r

instance ToMatrix g r => ToMatrix [g] r where
  toMatrix = foldl' (\acc -> (acc .*.) . toMatrix) (fromInteger 1)

-- * Generic exact synthesis algorithm
-- ---------------------------------------

-- | Class of unitaries over the ring /r/ synthesizable as a word
--   over the generators in /g/. Implements a generic exact synthesis algorithm
class (DenomExp r, ToMatrix g r, Adjoint r, WholePart r z) => Synthesizable r z g | g -> r, g -> z where
  initialize :: Int -> [z] -> [g]
  reduce :: [z] -> [g]
  synthesizeState :: forall n. Nat n => Int -> Vector n r -> [g]
  synthesize :: Nat n => Matrix n n r -> [g]

  -- default implementations
  -- | Exactly synthesize a length /n/ unit vector over r with
  --   initial state e/i/
  synthesizeState e = go where
    go :: Vector n r -> [g]
    go vec = case denomexp_decompose (list_of_vector vec) of
      (xs, 0) -> initialize e xs
      (xs, _) -> gates ++ go vec' where
        gates = reduce xs
        vec' = vector_head . unMatrix $ adj (toMatrix gates) .*. (column_matrix vec)
  -- | Exactly synthesize an /n/x/n/ unitary matrix over r
  synthesize m = go (unMatrix m) 0 where
    go :: (Nat n') => Vector n (Vector n' r) -> Integer -> [g]
    go Nil _j        = []
    go (Cons c cs) j = gates ++ go (unMatrix m') (j+1)
      where
        gates = synthesizeState (fromInteger j) c
        m'    = (adj $ toMatrix gates) .*. (Matrix cs)

-- | Checks correctness of synthesis
prop_correct :: (Nat n, Eq r, Adjoint r, Synthesizable r z g) => [g] -> Matrix n n r -> Bool
prop_correct proxy m = m == (toMatrix k) where
  k = proxy ++ synthesize m
