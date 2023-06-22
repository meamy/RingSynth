{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleContexts #-}

module Main where

import Prelude hiding (Integral, Real)

import Quantum.Synthesis.Matrix
import Quantum.Synthesis.Ring

import Quantum.Synthesis.Exact
import Quantum.Synthesis.Integral

import Quantum.Synthesis.Gates

-- ---------------------------------------
-- ** Generators of E8

s1, s2, s3, s4, s5, s6, s7, s8 :: Matrix Eight Eight Dyadic

s1 = toMatrix $ X 0 1
s2 = toMatrix $ X 1 2
s3 = toMatrix $ X 2 3
s4 = toMatrix $ X 3 4
s5 = toMatrix $ X 4 5
s6 = toMatrix $ X 5 6
s7 = toMatrix $ [X 5 6, Z 5, Z 6]
s8 = matrix_of_function go where
  go a b | a == b    = 3 * (half * half)
         | otherwise = -(half * half)

-- ----------------------------------------
-- ** Derived generators
x67 :: Matrix Eight Eight Dyadic
x67 = s7 * s8 * s6 * ph * s8 * ph * s6 * s8 * s7 where
  ph = toMatrix [Z 0, Z 1, Z 2, Z 3, Z 4, Z 5]

main = exec ()
