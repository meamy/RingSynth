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

import Data.Type.Equality
import Data.List

import Quantum.Synthesis.Matrix
import Quantum.Synthesis.Ring hiding (omega)

import qualified Utils.Unicode as U

import Quantum.Synthesis.Exact
import Quantum.Synthesis.Gates
import Quantum.Synthesis.Integral
import Quantum.Synthesis.Unreal
import Quantum.Synthesis.Embeddings
import Quantum.Synthesis.TypeArith

-- ---------------------------------------
-- ** Rings with a cube root of unity

-- | A ring that has a cube root of unity
class Ring r => EisensteinRing r where
  omega :: r

-- ---------------------------------------
-- ** The ring \(R[\omega]\)

-- | The ring \(R[\omega]\) where \(R\) is any ring and
--   \(\omega = e^{2\pi i /3}\) is a primitive 3rd root
--   of unity. The value 'Eisen' /a/ /b/ represents
--   the complex number \(\omega a + b\)
data Eisenstein r = Eisen !r !r deriving (Eq)

instance (Show r, Eq r, Ring r) => Show (Eisenstein r) where
  showsPrec p (Eisen 0 0) = showString "0"
  showsPrec p (Eisen a b) = showParen (p >= 11) $ showString str where
    str = intercalate " + " $ showA ++ showB
    showA
      | a == 0    = []
      | a == 1    = [U.omega]
      | otherwise = [U.omega ++ "*" ++ showsPrec 11 a ""]
    showB
      | b == 0    = []
      | otherwise = [showsPrec 11 b ""]

instance Num r => Num (Eisenstein r) where
  (Eisen a b) + (Eisen c d) = Eisen (a + c) (b + d)
  (Eisen a b) * (Eisen c d) = Eisen a' b' where
    a' = a*d + b*c - a*c
    b' = b*d - a*c
  negate (Eisen a b)            = Eisen (-a) (-b)
  signum _                      = undefined
  abs _                         = undefined
  fromInteger j                 = Eisen 0 (fromInteger j)

instance (Ring r, Adjoint r) => Adjoint (Eisenstein r) where
  adj (Eisen a b) = Eisen (-a) (b - a)

instance HalfRing r => HalfRing (Eisenstein r) where
  half = Eisen 0 half

instance Ring r => EisensteinRing (Eisenstein r) where
  omega = Eisen 1 0

instance (Eq r, EisensteinRing r) => EisensteinRing (CplxRootTwo r) where
  omega = CplxRootTwo omega 0

instance Nat n => Commuting (Matrix n n) Eisenstein r where
  commute mat = Eisen amat bmat where
    amat = matrix_map (\(Eisen a _) -> a) mat
    bmat = matrix_map (\(Eisen _ b) -> b) mat

-- | The ring \(D[\omega]\)
type DEisen = Eisenstein Dyadic

-- ---------------------------------------
-- ** Embeddings

instance EisensteinRing (Matrix Four Four Dyadic) where
  omega = scalarmult half mat where
    mat = matrix4x4 (-1,1,-1,-1) (-1,-1,-1,1) (1,1,-1,1) (1,-1,-1,-1)

instance Embeddable Four DEisen Dyadic where
  embed :: forall n. Nat n => Matrix n n DEisen -> Matrix (Four `Times` n) (Four `Times` n) Dyadic
  embed = withProof (times_is_nat (nnat @Four) (nnat @n)) go where
    go :: Nat (Four `Times` n) => Matrix n n DEisen -> Matrix (Four `Times` n) (Four `Times` n) Dyadic
    go mat = o*(lift a) + lift b where
      lift = tensor (1 :: Matrix Four Four Dyadic)
      (Eisen a b) = commute mat
      o = tensor (omega :: Matrix Four Four Dyadic) (1 :: Matrix n n Dyadic)

-- ---------------------------------------
-- ** Worked out example

-- | \(\omega\) in \mathbb{D}
gamma :: Matrix Four Four Dyadic
gamma = omega

-- *** Cube root of unity phase gate

-- | The gate diag(1, \(\omega\))
eGate :: Matrix Two Two DEisen
eGate = matrix2x2 (1, 0) (0, omega)

-- | The embedded E gate diag(1, \(\omega\))
eGate' :: Matrix Eight Eight Dyadic
eGate' = embed eGate

-- *** Two-level synthesis of \(E'\)
twolevel_circuit :: [DyadicGen]
twolevel_circuit = synthesize eGate'

-- *** Eigenvectors and eigenvalues
  
l1,l2,l3,l4 :: DEisen
l1 = omega
l2 = omega
l3 = adj omega
l4 = adj omega

v1,v2,v3,v4 :: Matrix Four One DEisen
v1 = column_matrix $ vector [omega, adj omega, 0, 1]
v2 = column_matrix $ vector [-(adj omega), omega, 1, 0]
v3 = column_matrix $ vector [adj omega, omega, 0, 1]
v4 = column_matrix $ vector [-omega, adj omega, 1, 0]

-- | orthogonal eigenvectors
v1',v2',v3',v4' :: Matrix Four One (CplxRootTwo DEisen)
v1' = matrix_map (\a -> CplxRootTwo a 0) v1
v2' = scalarmult (half*iroottwo) $ column_matrix $ vector [1, 1, -(1 + 2*omega), 1]
v3' = matrix_map (\a -> CplxRootTwo a 0) v3
v4' = scalarmult (half*iroottwo) $ column_matrix $ vector [-1, -1, -(1 + 2*omega), -1]

lift :: Ring r => Matrix n m r -> Matrix n m (Eisenstein r)
lift = matrix_map (\a -> Eisen 0 a)


v :: Matrix Four Four DEisen
v = matrix_of_columns . concatMap columns_of_matrix $ [v1, v2, v3, v4]

l :: Matrix Four Four DEisen
l = matrix4x4 (l1, 0, 0, 0) (0, l2, 0, 0) (0, 0, l3, 0) (0, 0, 0, l4)

-- *** Measurement results

-- | Hadamard matrix in RootTwo DEisen
had :: Matrix Two Two (RootTwo DEisen)
had = matrix2x2 (roothalf, roothalf) (roothalf, -roothalf)

-- | A simple test vector
pl :: Matrix Two One (RootTwo DEisen)
pl = column_matrix $ vector [roothalf, roothalf]

-- | The state HEH|0>
test_state :: Matrix Two One (RootTwo DEisen)
test_state = had .*. (matrix_map (\a -> RootTwo a 0) eGate) .*. pl

-- | The state (I\otimes H)E'(I\otimes H)(|v1>\otimes|0>)
test_state' :: Matrix Eight One (RootTwo DEisen)
test_state' = had' .*. (matrix_map f eGate') .*. (tensor v1' pl) where
  had' = tensor (1 :: Matrix Four Four (RootTwo DEisen)) had
  f a  = RootTwo (Eisen 0 a) 0
  v1'  = matrix_map (\a -> RootTwo a 0) v1

-- *** Resource counts

-- Clifford + T implementation of eGate'
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
  putStrLn $ "Properties of Gamma:"
  putStrLn $ "  Gamma = " ++ show gamma
  putStrLn $ "  Gamma^3 = I: " ++ show (gamma^3 == 1)
  putStrLn $ "  Gamma^2 + Gamma + I = 0: " ++ show (gamma^2 + gamma + 1 == 0)
  putStrLn $ "  Gamma^*Gamma = I: " ++ show ((adj gamma) * gamma == 1)
  putStrLn $ "  GammaGamma^* = I: " ++ show (gamma * (adj gamma) == 1)
  putStrLn $ ""
  putStrLn $ "E gates:"
  putStrLn $ "  E = " ++ show eGate
  putStrLn $ "  E' = " ++ show eGate'
  putStrLn $ "  E'^3 = I: " ++ show (eGate'^3 == 1)
  putStrLn $ ""
  putStrLn $ "Circuits for E':"
  putStrLn $ "  two level: " ++ show twolevel_circuit
  putStrLn $ "  Over Cliffor+T: " ++ show (eGate'_circuit :: String)
  putStrLn $ ""
  putStrLn $ "Eigenvectors:"
  putStrLn $ "  l1 = " ++ show l1
  putStrLn $ "  l2 = " ++ show l2
  putStrLn $ "  l3 = " ++ show l3
  putStrLn $ "  l4 = " ++ show l4
  putStrLn $ "  Gamma v1 = omega v1: " ++ show ((lift gamma) .*. v1 == scalarmult l1 v1)
  putStrLn $ "  Gamma v2 = omega v2: " ++ show ((lift gamma) .*. v2 == scalarmult l2 v2)
  putStrLn $ "  Gamma v3 = omega^* v3: " ++ show ((lift gamma) .*. v3 == scalarmult l3 v3)
  putStrLn $ "  Gamma v4 = omega^* v4: " ++ show ((lift gamma) .*. v4 == scalarmult l4 v4)
  putStrLn $ ""
  putStrLn $ "SVD:"
  putStrLn $ "  U = " ++ show v
  putStrLn $ "  A = " ++ show l
  putStrLn $ "  Gamma = UAU^*: " ++ show (adjoint v .*. l .*. v == (lift gamma))
  putStrLn $ ""
  putStrLn $ "Evaluation:"
  putStrLn $ "  (I x H)E'(I x H)|v1> x |0> = HEH|0>: " ++ show (test_state' == tensor v1' test_state)
  where v1'  = matrix_map (\a -> RootTwo a 0) v1
  


