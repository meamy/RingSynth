{-|
Module      : ChannelRep
Description : Channel representation of unitaries
Maintainer  : matt.e.amy@gmail.com
Stability   : experimental
Portability : portable
-}

module Quantum.Synthesis.ChannelRep where

import Data.List

import Control.Monad

import Test.QuickCheck

import Quantum.Synthesis.Matrix
import Quantum.Synthesis.Ring
import Quantum.Synthesis.MoreRings

-- * Pauli group
-- ---------------------------------------

-- | The generators of the Pauli group
data PauliGen =
    PauliX !Int
  | PauliY !Int
  | PauliZ !Int
  deriving (Eq, Show, Ord)

instance Adjoint PauliGen  where
  adj = id

instance (CplxRing r) => ToMatrix PauliGen r where
  toMatrix (PauliX a b) = twolevel_matrix (0, 1) (1, 0) a b
  toMatrix (PauliY a b) = twolevel_matrix (0, -i) (i, 0) a b
  toMatrix (PauliZ a)   = onelevel_matrix (-1) a

-- * Channel representation
-- ---------------------------------------
