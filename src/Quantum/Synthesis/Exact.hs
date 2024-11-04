{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE TypeApplications #-}

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
import Quantum.Synthesis.TypeArith
import Data.Type.Equality

-- * Matrix-like data
-- ---------------------------------------

-- | Type of things that can be converted to a matrix
class Ring r => ToMatrix g r | g -> r where
  toMatrix :: Nat n => g -> Matrix n n r

instance ToMatrix g r => ToMatrix [g] r where
  toMatrix = foldl' (\acc -> (acc .*.) . toMatrix) (fromInteger 1)

instance Adjoint g => Adjoint [g] where
  adj = map adj . reverse

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

-- | Householder-based synthesis. Synthesizes |+><-|xU + |-><+|xU*
householderSynth :: forall r z g n. (Synthesizable r z g, HalfRing r, Adjoint g, Nat n) => Matrix n n r -> [g]
householderSynth m = concatMap synthRefl $ zip [0..] (columns_of_matrix m) where
  dim :: Int
  dim = fromInteger $ nat @n undefined

  plus :: Matrix Two One r
  plus = matrix_of_columns [[1,1]]

  minus :: Matrix Two One r
  minus = matrix_of_columns [[1,-1]]

  refZ :: Matrix (Times Two n) One r
  refZ = case n_plus_n (nnat @n) of
    Refl -> withProof (plus_is_nat (nnat @n) (nnat @n)) $
      matrix_of_columns [(-1:replicate (dim - 2) 0)]

  ket :: Int -> Matrix n One r
  ket j = matrix_of_function (\a b -> if a == j then 1 else 0)

  genWvec :: Int -> Matrix n One r -> Matrix (Times Two n) One r
  genWvec i ui = case n_plus_n (nnat @n) of
    Refl -> withProof (plus_is_nat (nnat @n) (nnat @n)) $
      scalarmult half (tensor minus (ket i) .-. tensor plus ui)

  toColumn :: forall n. Nat n => Matrix n One r -> Vector n r
  toColumn m = vector_index (unMatrix m) 0

  synthRefl :: (Int, [r]) -> [g]
  synthRefl (i, ui) =
    let cob = case n_plus_n (nnat @n) of
          Refl -> withProof (plus_is_nat (nnat @n) (nnat @n)) $
            synthesizeState 0 . toColumn $ genWvec i (matrix_of_columns [ui])
        ref = case n_plus_n (nnat @n) of
          Refl -> withProof (plus_is_nat (nnat @n) (nnat @n)) $
            synthesizeState 0 . toColumn $ refZ
    in
      adj cob ++ ref ++ cob

-- | Checks correctness of synthesis
prop_correct :: (Nat n, Eq r, Adjoint r, Synthesizable r z g) => [g] -> Matrix n n r -> Bool
prop_correct proxy m = m == (toMatrix k) where
  k = proxy ++ synthesize m

-- | Checks correctness of Householder synthesis
prop_correct_hh :: (Nat n, Eq r, Adjoint r, Synthesizable r z g, HalfRing r, Adjoint g) => [g] -> Matrix n n r -> Bool
prop_correct_hh proxy m = m == (toMatrix k) where
  k = proxy ++ householderSynth m
