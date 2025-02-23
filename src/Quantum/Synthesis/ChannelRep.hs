{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

{-|
Module      : ChannelRep
Description : Channel representation of unitaries
Maintainer  : matt.e.amy@gmail.com
Stability   : experimental
Portability : portable
-}

module Quantum.Synthesis.ChannelRep where

import Quantum.Synthesis.Ring
import Quantum.Synthesis.Exact
import Quantum.Synthesis.Gates

-- * Pauli group
-- ---------------------------------------

-- | The generators of the Pauli group
data PauliGen =
    PauliI !Int 
  | PauliX !Int 
  | PauliY !Int
  | PauliZ !Int
  deriving (Eq, Show, Ord)

instance Pauli PauliGen where
  pauliX a = PauliX a
  pauliY a = PauliY a
  pauliZ a = PauliZ a

instance Adjoint PauliGen  where
  adj = id

instance (ComplexRing r) => ToMatrix PauliGen r where
  toMatrix (PauliI _) = 1
  toMatrix (PauliX a) = pauliX a
  toMatrix (PauliY a) = pauliY a
  toMatrix (PauliZ a) = pauliZ a

-- | Interpret a PauliGen string
interpretPauli :: Pauli repr => PauliGen -> repr
interpretPauli (PauliI a) = pauliI a
interpretPauli (PauliX a) = pauliX a
interpretPauli (PauliY a) = pauliY a
interpretPauli (PauliZ a) = pauliZ a

-- | Convert an integer to an n-qubit Pauli
intToPauliN :: Int -> Integer -> [PauliGen]

-- * Channel representation
-- ---------------------------------------

type ChannelMatrix n r = Matrix (Power Four n) (Power Four n) r

-- | Send a matrix to its channel matrix representation
channelRep :: Complexring r => QubitMatrix n r -> ChannelMatrix n r
channelRep
