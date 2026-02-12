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

import Quantum.Synthesis.MoreRings
import Quantum.Synthesis.Exact
import Quantum.Synthesis.Gates
import Quantum.Synthesis.Gaussian
import Quantum.Synthesis.Embeddings

-- ---------------------------------------
-- ** Worked out example

type DiEisen = Eisenstein DGaussian

-- | \(\omega\) in \mathbb{D}
gamma :: Matrix Two Two DGaussian
gamma = embed . column_matrix . vector_singleton $ (eisen :: DiEisen)

-- *** Cube root of unity phase gate

-- | The gate diag(1, \(\omega\))
eGate :: Matrix Two Two DiEisen
eGate = matrix2x2 (1, 0) (0, eisen)

-- | The embedded E gate diag(1, \(\omega\))
eGate' :: Matrix Four Four DGaussian
eGate' = embed eGate

-- | The embedded E gate round-trip
eGate'' :: Matrix Four Four DiEisen
eGate'' = matrix_map iota eGate'

-- *** Two-level synthesis of \(E'\)
twolevel_circuit :: [GaussianGen]
twolevel_circuit = synthesize eGate'

-- *** Eigenvectors and eigenvalues
  
chi :: Matrix Two One DiEisen
chi = column_matrix $ vector [half*(-eisen + (iota (i :: DGaussian))*(adj eisen)), 1]

-- | Projectors
pChi :: Matrix Two Two DiEisen
pChi = chi .*. adjoint chi

-- | Identity matrix for convenience
i2 :: Matrix Two Two DiEisen
i2 = 1

-- *** Resource counts

-- | Clifford + T implementation of eGate'
eGate'_circuit :: (Circuit repr, CliffordT repr) => repr
eGate'_circuit =
  ccx 2 1 0 @@
  h 2 @@
  ccx 0 1 2 @@
  h 2 @@
  x 0 @@
  ch 0 1 @@
  ch 0 2 @@
  x 0 @@
  x 2 @@
  h 1 @@
  cx 2 1 @@
  h 1 @@
  x 2

main :: IO ()
main = do
  putStrLn $ "Embedding a third root of unity in Clifford+T"
  putStrLn $ ""
  putStrLn $ "This example constructs and checks an embedding of D[omega] in D[i]"
  putStrLn $ "along with a rotation by a third root of unity around Z."
  putStrLn $ ""
  putStrLn $ "First we construct and check the pseudo-companion matrix Gamma:"
  putStrLn $ "  Gamma = " ++ show gamma
  putStrLn $ "  Gamma^3 = I: " ++ show (gamma^3 == 1)
  putStrLn $ "  Gamma^2 + Gamma + I = 0: " ++ show (gamma^2 + gamma + 1 == 0)
  putStrLn $ "  Gamma^*Gamma = I: " ++ show ((adj gamma) * gamma == 1)
  putStrLn $ "  GammaGamma^* = I: " ++ show (gamma * (adj gamma) == 1)
  putStrLn $ ""
  putStrLn $ "Now we embed a third-order rotation gate over D:"
  putStrLn $ "  E = " ++ show eGate
  putStrLn $ "  phi(E) = " ++ show eGate'
  putStrLn $ "  phi(E)^3 = I: " ++ show (eGate'^3 == 1)
  putStrLn $ ""
  putStrLn $ "Next we synthesize a circuit for the embedded gate phi(E):"
  putStrLn $ "  Two level: " ++ show twolevel_circuit
  putStrLn $ "  Over Toffoli+Hadamard: " ++ show (eGate'_circuit :: String)
  putStrLn $ ""
  putStrLn $ "To apply E, we need catalysts, which we obtain via eigenvectors of Gamma:"
  putStrLn $ "  chi = " ++ show chi
  putStrLn $ ""
  putStrLn $ "Now we look at projector matrices for eigenspace:"
  putStrLn $ "  P = " ++ show pChi
  putStrLn $ ""
  putStrLn $ "Now verify the catalytic condition:"
  putStrLn $ "  phi(E)(I x P) = E x P: " ++ show ((eGate'' .*. (tensor pChi i2)) == tensor pChi eGate)
  putStrLn $ "  phi(E)(I x P) = E x P: " ++ show ((eGate'' .*. (tensor pChi i2)))
  putStrLn $ "  phi(E)(I x P) = E x P: " ++ show (tensor pChi eGate)
  


