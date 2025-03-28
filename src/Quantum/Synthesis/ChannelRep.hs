{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}

{-|
Module      : ChannelRep
Description : Channel representation of unitaries
Maintainer  : matt.e.amy@gmail.com
Stability   : experimental
Portability : portable
-}

module Quantum.Synthesis.ChannelRep where

import Data.String
import Data.List
import Data.Bits

import Quantum.Synthesis.Matrix
import Quantum.Synthesis.Ring
import Quantum.Synthesis.MoreRings
import Quantum.Synthesis.TypeArith
import Quantum.Synthesis.Exact
import Quantum.Synthesis.Gates hiding (Integral)
import qualified Utils.Unicode as U

-- * Utilities
-- ---------------------------------------

class CompactShow a where
  compactShow :: a -> String

instance CompactShow DOmega where
  compactShow (Omega a b c d) = sgn1 a ++ show a ++ U.omega ++ U.supscript 3 ++
                                sgn b ++ show b ++ "i" ++
                                sgn c ++ show c ++ U.omega ++
                                sgn d ++ show d ++ " |"
    where sgn a = case a < 0 of
            True  -> ""
            False -> "+"
          sgn1 a = case a < 0 of
            True  -> ""
            False -> " "

instance CompactShow DRootTwo where
  compactShow (RootTwo a b) = if length str < 2 then " " ++ str else str where
    str = case (a, b) of
      (0,0) -> " 0"
      (0,b) -> showRt2 b
      (a,0) -> show a
      (a,b) | b < 0 -> show a ++ showRt2 b
      (a,b) | otherwise -> show a ++ "+" ++ showRt2 b
    showRt2 b = case b of
      1  -> U.rt2
      -1 -> "-" ++ U.rt2
      _  -> show b ++ U.rt2

instance CompactShow (RootTwo Z2) where
  compactShow (RootTwo a b) = case (a,b) of
    (0,0) -> show 0
    (1,0) -> show 1
    (0,1) -> show 2
    (1,1) -> show 3

-- * The n-qubit Pauli group
-- ---------------------------------------

data PauliGate = PauliI | PauliX | PauliZ | PauliY deriving (Eq, Ord)
data PauliPhase = I0 | I1 | I2 | I3 deriving (Eq, Ord)
newtype PauliGroup n = PauliOp (PauliPhase, Vector n PauliGate)

instance Show PauliGate where
  show PauliI = "I"
  show PauliX = "X"
  show PauliY = "Y"
  show PauliZ = "Z"

instance Show PauliPhase where
  show I0 = ""
  show I1 = "i"
  show I2 = "-"
  show I1 = "-i"

instance Show (PauliGroup n) where
  show (PauliOp (ph,pa)) = show ph ++ concatMap show (list_of_vector pa)

instance Nat n => IsString (PauliGroup n) where
  fromString s
    | s == []          = PauliOp (I0, vector []) 
    | head s   == 'i'  = PauliOp (I1, vector $ map toPauli (tail s))
    | head s   == '-'  = PauliOp (I2, vector $ map toPauli (tail s))
    | take 2 s == "-i" = PauliOp (I2, vector $ map toPauli (drop 2 s))
    | otherwise        = PauliOp (I0, vector $ map toPauli s)
    where toPauli 'I' = PauliI
          toPauli 'X' = PauliX
          toPauli 'Y' = PauliY
          toPauli 'Z' = PauliZ

instance Semigroup PauliPhase where
  a <> b =
    let fromInt a = case a of
          0 -> I0
          1 -> I1
          2 -> I2
          3 -> I3
        toInt a = case a of
          I0 -> 0
          I1 -> 1
          I2 -> 2
          I3 -> 3
    in
      fromInt ((toInt a + toInt b) `mod` 4)

instance Monoid PauliPhase where
  mempty = I0

instance Nat n => Semigroup (PauliGroup n) where
  (PauliOp (r, p)) <> (PauliOp (s, q)) = PauliOp (r <> s <> t, vector xs) where

    (t, xs) = foldr go (I0, []) $ zip (list_of_vector p) (list_of_vector q)

    go (p,q) (t, xs) = (t <> t', p':xs) where
      (t',p') = case (p,q) of
        (PauliI, p)      -> (I0, p)
        (p, PauliI)      -> (I0, p)
        (PauliX, PauliX) -> (I0, PauliI)
        (PauliX, PauliZ) -> (I3, PauliY)
        (PauliX, PauliY) -> (I1, PauliZ)
        (PauliZ, PauliX) -> (I1, PauliY)
        (PauliZ, PauliZ) -> (I0, PauliI)
        (PauliZ, PauliY) -> (I3, PauliX)
        (PauliY, PauliX) -> (I3, PauliZ)
        (PauliY, PauliZ) -> (I1, PauliX)
        (PauliY, PauliY) -> (I0, PauliI)

instance Nat n => Monoid (PauliGroup n) where
  mempty = PauliOp (I0, vector_repeat PauliI)

instance Nat n => Gate (PauliGroup n) where
  identity = mempty

instance Nat n => Pauli (PauliGroup n) where
  pauliX a = PauliOp (I0, vector_of_function (\i -> if i == a then PauliX else PauliI))
  pauliY a = PauliOp (I0, vector_of_function (\i -> if i == a then PauliY else PauliI))
  pauliZ a = PauliOp (I0, vector_of_function (\i -> if i == a then PauliZ else PauliI))

instance (ComplexRing r, Nat n) => ToMatrix (PauliGroup n) r where
  toMatrix = pauli

-- | Access the pauli vector of a pauli
proj :: PauliGroup n -> Vector n PauliGate
proj (PauliOp (_,p)) = p

-- | Inserts a Pauli at position "i"
insertI :: Nat n => Int -> PauliGate -> PauliGroup n -> PauliGroup (Succ n)
insertI i p (PauliOp (pp,pg)) = PauliOp (pp,pg') where
  pg' = vector_of_function f

  f j | j < i  = vector_index pg j
      | j == i = p
      | j > i  = vector_index pg (j-1)

-- | Interpret a member of the n-qubit Pauli group
pauli :: (Pauli repr, Circuit repr, Nat n) => PauliGroup n -> repr
pauli (PauliOp (t,p)) = foldl (@@) identity . map toRepr . zip [0..] $ list_of_vector p
  where toRepr (a, PauliI) = identity
        toRepr (a, PauliX) = pauliX a
        toRepr (a, PauliY) = pauliY a
        toRepr (a, PauliZ) = pauliZ a

-- | Basic Pauli commutation relations
pauliCommute :: PauliGate -> PauliGate -> Bool
pauliCommute p q = if p == q then True else False

-- | Checks whether two Paulis commute
commutes :: Nat n => PauliGroup n -> PauliGroup n -> Bool
commutes (PauliOp (_,p)) (PauliOp (_,q)) = foldr f True $ zip ps qs where
  ps      = list_of_vector p
  qs      = list_of_vector q
  f (p,q) = if pauliCommute p q then \x -> x else \x -> not x

-- | Convert an integer to an n-qubit Pauli
intToPauliGroup :: forall n. Nat n => Integer -> PauliGroup n
intToPauliGroup a = PauliOp (I0, vector . reverse $ go 0 a) where
  qubits = nat @n undefined

  go i a | i == qubits = []
         | otherwise   = (getPauli (a `mod` 4)):go (i+1) (a `div` 4)
  
  getPauli a = case a `mod` 4 of
          0 -> PauliI 
          1 -> PauliX
          2 -> PauliY
          3 -> PauliZ

-- | Convert an n-qubit Pauli to an integer
pauliGroupToInt :: forall n. Nat n => PauliGroup n -> Integer
pauliGroupToInt (PauliOp (_, vec)) = foldl go 0 $ list_of_vector vec where
  go acc p = (acc `shiftL` 2) + getInt p

  getInt p = case p of
    PauliI -> 0
    PauliX -> 1
    PauliY -> 2
    PauliZ -> 3

-- | Converts a plus or minus to a scalar
pauliPhaseToScalar :: ComplexRing r => PauliPhase -> r
pauliPhaseToScalar a = case a of
  I0 -> 1
  I1 -> i
  I2 -> -1
  I3 -> -i

-- | Checks whether a Pauli is the identity up to a phase
isIdentity :: Nat n => PauliGroup n -> Bool
isIdentity (PauliOp (_,p)) = all (== PauliI) $ list_of_vector p

-- | Checks whether a Pauli is in the linear span of a subset of Paulis
inSpan :: forall n. Nat n => PauliGroup n -> [PauliGroup n] -> Bool
inSpan p xs = isIdentity $ foldr reduce p [0..(nat @n undefined)-1] where
  reduce i p = case vector_index (proj p) i of
    PauliI -> p
    p'     -> reduceP i p' p
  reduceP i pauli p = case findP i pauli xs of
    Just q  -> p <> q
    Nothing ->
      let (x,z) = calculateProduct pauli in
        case (findP i x xs, findP i z xs) of
          (Just q, Just q') -> p <> q <> q'
          _                 -> p
  findP i p = find (\q -> vector_index (proj q) i == p)
  calculateProduct p = case p of
    PauliX -> (PauliY, PauliZ)
    PauliY -> (PauliX, PauliZ)
    PauliZ -> (PauliX, PauliY)
    PauliI -> error "Why are you trying to find a Pauli I?"

-- * pi/4 Pauli rotations
-- ---------------------------------------

newtype PauliExp n = Exp (PauliGroup n)

instance Show (PauliExp n) where
  show (Exp pauli) = "R(" ++ show pauli ++ ")" 

instance Nat n => Gate (PauliExp n) where
  identity = Exp identity

instance Nat n => Adjoint (PauliExp n) where
  adj (Exp (PauliOp (t,p))) = Exp (PauliOp (I2 <> t,p))

instance Nat n => ToMatrix (PauliExp n) DOmega where
  toMatrix (Exp p) = scalarmult a identity + scalarmult b (toMatrix p) where
    a = half*(1 + omega)
    b = half*(1 - omega)

-- * Concrete representation for Pauli & Pauli Rotation circuits
-- ---------------------------------------

data PauliGen =
    IGate !Int 
  | XGate !Int 
  | YGate !Int
  | ZGate !Int
  deriving (Eq, Show, Ord)

instance Gate PauliGen where
  identity = IGate 0

instance Pauli PauliGen where
  pauliX a = XGate a
  pauliY a = YGate a
  pauliZ a = ZGate a

instance Adjoint PauliGen  where
  adj = id

instance (ComplexRing r) => ToMatrix PauliGen r where
  toMatrix p = interpretPauli [p]

-- | Interpret a PauliGen string
interpretPauli :: (Pauli repr, Circuit repr) => [PauliGen] -> repr
interpretPauli = foldl (@@) identity . map toRepr
  where toRepr (IGate a) = identity
        toRepr (XGate a) = pauliX a
        toRepr (YGate a) = pauliY a
        toRepr (ZGate a) = pauliZ a

-- | Convert an integer to an n-qubit Pauli
intToPauliN :: Int -> Integer -> [PauliGen]
intToPauliN n a
  | n <= 0    = []
  | otherwise =
    let g = case a `mod` 4 of
          0 -> IGate $ n - 1 
          1 -> XGate $ n - 1
          2 -> YGate $ n - 1
          3 -> ZGate $ n - 1
    in
      g:(intToPauliN (n-1) $ a `div` 4)

-- * pi/4 Pauli rotations using Pauli generators
-- ---------------------------------------
data PM = Plus | Minus deriving (Eq, Show, Ord)

-- | Flips a plus or minus sign
pmFlip :: PM -> PM
pmFlip Plus = Minus
pmFlip Minus = Plus

-- | Converts a plus or minus to a scalar
pmToScalar :: Integral a => PM -> a
pmToScalar Plus  = fromInteger 1
pmToScalar Minus = fromInteger $ -1

data PauliRotation = R PM [PauliGen] deriving (Eq, Show, Ord)

instance Gate PauliRotation where
  identity = R Plus [identity]

instance Adjoint PauliRotation where
  adj (R pm p) = R (pmFlip pm) p

instance ToMatrix PauliRotation DOmega where
  toMatrix (R pm p) = scalarmult (half*(1 + omega)) ii + scalarmult (half*(1 - omega)) pp where
    ii = identity
    pp = toMatrix p

-- * Channel representation
-- ---------------------------------------

type ChannelMatrix n r = Matrix (Power Four n) (Power Four n) r

-- | Send a matrix to its channel matrix representation
channelRep :: forall n r. (Nat n, ComplexRing r, HalfRing r, Adjoint r) =>
                          QubitMatrix n r -> ChannelMatrix n r
channelRep u = mat where
  m :: Integer
  m = nat @n undefined

  mat :: ChannelMatrix n r
  mat = withProof (power_is_nat (nnat @Four) (nnat @n)) $
    withProof (power_is_nat (nnat @Two) (nnat @n)) $
    matrix_of_function f

  f :: (Nat (Power Two n)) => Integer -> Integer -> r
  f x y =
    let p = toMatrix $ intToPauliN (fromInteger m) x
        q = toMatrix $ intToPauliN (fromInteger m) y
        s = fromDyadic $ Dyadic 1 m
    in
      s * (tr $ u * p * (adj u) * q)
 

-- | Escapes type-checking
channelRep' :: forall n m r. (Nat n,Nat m,ComplexRing r,HalfRing r,Adjoint r) =>
                             Matrix n n r -> Matrix m m r
channelRep' u = mat where
  qubits :: Integer
  qubits = natLog @n 

  mat :: Matrix m m r
  mat = matrix_of_function f

  f :: Integer -> Integer -> r
  f x y =
    let p = toMatrix $ intToPauliN (fromInteger qubits) x
        q = toMatrix $ intToPauliN (fromInteger qubits) y
        s = fromDyadic $ Dyadic 1 qubits
    in
      s * (tr $ u * p * (adj u) * q)

-- | Generates the channel representation of a pi/4 rotation of a Pauli string
pauliExp :: forall n. Nat n => String -> ChannelMatrix n DRootTwo
pauliExp = coerceSubring . channelRep @n . toMat . fromStr where
  toMat :: PauliExp n -> QubitMatrix n DOmega
  toMat m = withProof (power_is_nat (nnat @Two) (nnat @n)) $ toMatrix m

  fromStr :: String -> PauliExp n
  fromStr = Exp . fromString

-- | Calculates the paulis which quasi-commute with the unitary
commutingPaulis :: forall n. Nat n => ChannelMatrix n DRootTwo -> [PauliGroup n]
commutingPaulis = foldr go [] . zip [0..] . list_of_vector . unMatrix where
  go (i, vec) acc = case denomexp vec of
    0 -> (intToPauliGroup @n i):acc
    _ -> acc

-- | Gets the residue mod 2 of the channel representation
residueChannel :: forall n. Nat n => ChannelMatrix n DRootTwo -> ChannelMatrix n (RootTwo Z2)
residueChannel m = residue m' where
  (m', sde) = denomexp_decompose m

-- | Given a channel matrix, calculates the Paulis which are not zero mod 2
reducibles :: forall n. Nat n => ChannelMatrix n DRootTwo -> [[(PauliGroup n, String)]]
reducibles = map go . list_of_vector . unMatrix . residueChannel @n where
  go = foldr f [] . zip [0..] . list_of_vector
  f (i,a) acc = case a of
    RootTwo 0 0 -> acc
    RootTwo 1 0 -> (intToPauliGroup @n i, "10"):acc
    RootTwo 0 1 -> (intToPauliGroup @n i, "01"):acc
    RootTwo 1 1 -> (intToPauliGroup @n i, "11"):acc

-- | Computes the channel matrix on the |0> (ancillary) subspace of the indicated qubit
setAncilla :: forall n r. (Nat n, HalfRing r) => Int -> ChannelMatrix (Succ n) r -> ChannelMatrix n r
setAncilla i mat = mat' where
  n' = (nat @n undefined) + 1

  mat' :: ChannelMatrix n r
  mat' = withProof (power_is_nat (nnat @Four) (nnat @n)) $
    withProof (power_is_nat (nnat @Two) (nnat @n)) $
    matrix_of_function f

  f x y = 
    let p  = intToPauliGroup @n x
        pi = pauliGroupToInt $ insertI i PauliI p
        pz = pauliGroupToInt $ insertI i PauliZ p
        q  = intToPauliGroup @n y
        qi = pauliGroupToInt $ insertI i PauliI q
        qz = pauliGroupToInt $ insertI i PauliZ q
    in
      half*(matrix_index mat pi qi + matrix_index mat pi qz +
            matrix_index mat pz qi + matrix_index mat pz qz)

-- | Prints a channel matrix compactly
printChannel :: forall n r z. (Nat n, Nat (Power Four n), CompactShow r, DenomExp r) =>
                              ChannelMatrix n r -> IO ()
printChannel m = go . zip [0..] $ rows_of_matrix m' where
  sde = denomexp m
  m' = denomexp_factor m sde

  go []         = putStrLn ("sde = " ++ show sde) >> return ()
  go ((i,x):xs) = do
    let p = intToPauliGroup @n i
    putStrLn (show p ++ " [" ++ intercalate " " (map compactShow x) ++ "]")
    go xs

-- | Prints a channel matrix compactly
printResidue :: forall n. (Nat n, Nat (Power Four n)) => ChannelMatrix n DRootTwo -> IO ()
printResidue m = go . zip [0..] $ rows_of_matrix m' where
  m' = residueChannel @n m

  go []         = return ()
  go ((i,x):xs) = do
    let p = intToPauliGroup @n i
    putStrLn (show p ++ " [" ++ concatMap showIt x ++ "]")
    go xs

  showIt 0 = " "
  showIt x = compactShow x

-- * Testing
-- ---------------------------------------

-- | Channel representation of Pauli rotations
allPauliRotations :: forall m. Nat m => Int -> [Matrix m m DOmega]
allPauliRotations n = map go [0..2^n - 1] where
  go :: Integer -> Matrix m m DOmega
  go i = toMatrix $ R Plus (intToPauliN n i)

tChannel :: ChannelMatrix One DOmega
tChannel = tgateChannel where
  tgate :: QubitMatrix One DOmega
  tgate = t 0
  
  tgateChannel :: ChannelMatrix One DOmega
  tgateChannel = channelRep' tgate

tChannel' :: ChannelMatrix One DRootTwo
tChannel' = coerceSubring tgateChannel where
  tgate :: QubitMatrix One DOmega
  tgate = t 0
  
  tgateChannel :: ChannelMatrix One DOmega
  tgateChannel = channelRep' tgate


setAncilla2 :: HalfRing r => Int -> ChannelMatrix Three r -> ChannelMatrix Two r
setAncilla2 = setAncilla @Two

pp_matrix :: (Nat n, Nat m, Show r) => Matrix n m r -> IO ()
pp_matrix = go . rows_of_matrix where
  go []     = return ()
  go (x:xs) = do
    putStrLn ("[" ++ intercalate " " (map show x) ++ "]")
    go xs
