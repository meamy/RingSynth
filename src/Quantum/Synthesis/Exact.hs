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

{---------------------------------
 Auxiliary type classes
 ---------------------------------}

-- | Type of things that can be converted to a matrix
class Ring r => ToMatrix g r | g -> r where
  toMatrix :: Nat n => g -> Matrix n n r

instance ToMatrix g r => ToMatrix [g] r where
  toMatrix = foldl' (\acc -> (acc .*.) . toMatrix) (fromInteger 1)

{---------------------------------
 Exact synthesis
 ---------------------------------}

-- | Class of unitaries over the ring /r/ synthesizable as a word
--   over the generators in /g/
class ToMatrix g r => Synthesizable r g | r -> g where
  -- | Exactly synthesize a length /n/ unit vector over r with
  --   initial state e/i/
  synthesizeState :: (Nat n, Adjoint r) => Int -> Vector n r -> [g]
  -- | Exactly synthesize an /n/x/n/ unitary matrix over r
  synthesize :: (Nat n, Adjoint r) => Matrix n n r -> [g]
  -- default implementation
  synthesize m = go (unMatrix m) 0 where
    go :: (Nat n') => Vector n (Vector n' r) -> Integer -> [g]
    go Nil _j        = []
    go (Cons c cs) j = gates ++ go (unMatrix m') (j+1)
      where
        gates = synthesizeState (fromInteger j) c
        m'    = (adj $ toMatrix gates) .*. (Matrix cs)

{---------------------------------
 Testing
 ---------------------------------}

-- | Checks correctness of synthesis
prop_correct ::
  (Nat n, Eq r, Adjoint r, Synthesizable r g) => Matrix n n r -> Bool
prop_correct m = m == (toMatrix $ synthesize m)
