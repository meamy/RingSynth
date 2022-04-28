{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-|
Module      : Integral
Description : Exact synthesis over \(\mathbb{D}\)
Maintainer  : matt.e.amy@gmail.com
Stability   : experimental
Portability : portable
-}

module Quantum.Synthesis.Integral where

import Data.List

import Control.Monad

import Test.QuickCheck

import Quantum.Synthesis.Matrix
import Quantum.Synthesis.Ring
import Quantum.Synthesis.MoreRings
import Quantum.Synthesis.MultiQubitSynthesis

import Quantum.Synthesis.Exact


-- * Generators
-- ---------------------------------------

-- | The generators of the integral circuit group
data DyadicGen =
    Z !Int
  | X !Int !Int
  | HH !Int !Int !Int !Int
  deriving (Eq, Show, Ord)

instance Adjoint DyadicGen where
  adj = id

instance ToMatrix DyadicGen Dyadic where
  toMatrix (Z a)        = onelevel_matrix (-1) a
  toMatrix (X a b)      = twolevel_matrix (0, 1) (1, 0) a b
  toMatrix (HH a b c d) = matrix_of_function f where
    f x y
      | x == a && (y == a || y == b || y == c || y == d) = half
      | x == b && (y == a || y == c)                     = half
      | x == b && (y == b || y == d)                     = -half
      | x == c && (y == a || y == b)                     = half
      | x == c && (y == c || y == d)                     = -half
      | x == d && (y == a || y == d)                     = half
      | x == d && (y == c || y == b)                     = -half
      | x == y                                           = 1
      | otherwise                                        = 0

-- | An alternate set of generators for the integral circuit group
data DyadicGenAlt =
    M !Int
  | S !Int !Int
  | R !Int !Int !Int !Int
  deriving (Eq, Show, Ord)

instance Adjoint DyadicGenAlt where
  adj = id

instance ToMatrix DyadicGenAlt Dyadic where
  toMatrix (M a)       = onelevel_matrix (-1) a
  toMatrix (S a b)     = twolevel_matrix (0, 1) (1, 0) a b
  toMatrix (R a b c d) = 1 - matrix_of_function f where
    f x y
      | [x,y] `intersect` [a,b,c,d] == [x,y] = half
      | otherwise                            = 0

dyadicToAlt :: [DyadicGen] -> [DyadicGenAlt]
dyadicToAlt xs = concatMap go xs where
  go (Z a)        = [M a]
  go (X a b)      = [S a b]
  go (HH a b c d) = [M a, R a b c d, M a, S b c]

altToDyadic :: [DyadicGenAlt] -> [DyadicGen]
altToDyadic xs = concatMap go xs where
  go (M a)       = [Z a]
  go (S a b)     = [X a b]
  go (R a b c d) = [Z a, HH a b c d, Z a, X b c]

-- * Relations
-- ---------------------------------------

-- | Relations for the Dyadic generators
rel1a a b             = [X a b, X a b]
rel1b a               = [Z a, Z a]
rel1c a b c d         = [HH a b c d, HH a b c d]

rel2a a b c d         = [X a b, X c d, X a b, X c d]
rel2b a b c           = [X a b, Z c, X a b, Z c]
rel2c a b c d e f     = [X a b, HH c d e f, X a b, HH c d e f]
rel2d a b             = [Z a, Z b, Z a, Z b]
rel2e a b c d e       = [Z a, HH b c d e, Z a, HH b c d e]
rel2f a b c d e f g h = [HH a b c d, HH e f g h, HH a b c d, HH e f g h]

rel3a a b c           = [X a b, X a c, X a b, X b c]
rel3b a b c           = [X a b, X c a, X a b, X c b]
rel3c a b             = [X a b, Z b, X a b, Z a]
rel3d a b c d e       = [X a b, HH a c d e, X a b, HH b c d e]
rel3e a b c d e       = [X a b, HH c a d e, X a b, HH c b d e]
rel3f a b c d e       = [X a b, HH c d a e, X a b, HH c d b e]
rel3g a b c d e       = [X a b, HH c d e a, X a b, HH c d e b]

rel4a a b c d         = [X a b, HH a b c d, Z d, Z b, X b d, HH a b c d]
rel4b a b c d         = [X b c, HH a b c d, Z a, HH a b c d, Z a, HH a b c d, Z a]
rel4c a b c d         = [X c d, HH a b c d, X b d, HH a b c d]

rel5a a b c d e f     = [HH a b c d, HH b d e f, HH a b c e, HH c d e f]

rel6a a b c d e f g h = [Z a, Z e, X a e, HH e f g h, HH a b c d, X d e, HH a b c d,
                         HH e f g h, X a e, Z a, Z e, HH e f g h, HH a b c d,
                         X d e, HH a b c d, HH e f g h]

-- * Synthesis algorithm
-- ---------------------------------------

instance Synthesizable Dyadic Integer DyadicGen where
  initialize e xs = zCorr ++ xCorr where
    a = case findIndex (\v -> v /= 0) xs of
      Just b  -> b
      Nothing -> error $ "Not a unit vector: " ++ show xs
    zCorr = if (xs!!a) == -1 then [Z a] else []
    xCorr = if a == e then [] else [X e a]
  reduce xs = f $ findIndices (\v -> (v*v) `mod` 4 == 1) xs where
    f []            = []
    f (a:b:c:d:xs') = zCorr ++ [HH a b c d] ++ f xs' where
      zCorr = map Z . filter (\j -> (xs!!j) `mod` 4 == 3) $ [a,b,c,d]
    f _             = error $ "Not a unit vector: " ++ show xs

instance Synthesizable Dyadic Integer DyadicGenAlt where
  initialize e xs = zCorr ++ xCorr where
    a = case findIndex (\v -> v /= 0) xs of
      Just b  -> b
      Nothing -> error $ "Not a unit vector: " ++ show xs
    zCorr = if (xs!!a) == -1 then [M a] else []
    xCorr = if a == e then [] else [S e a]
  reduce xs = f $ findIndices (\v -> (v*v) `mod` 4 == 1) xs where
    f []            = []
    f (a:b:c:d:xs') = zCorr ++ [R a b c d] ++ f xs' where
      zCorr   = aCorr ++ bcdCorr
      aCorr   = if (xs!!a) `mod` 4 == 3 then [M a] else []
      bcdCorr = map M . filter (\j -> (xs!!j) `mod` 4 == 1) $ [b,c,d]
    f _             = error $ "Not a unit vector: " ++ show xs

-- * Arbitrary instances
-- ---------------------------------------

-- | Random (-1) phase
genZ :: Int -> Gen DyadicGen
genZ n
  | n <= 0 = error $ "Invalid bound " ++ show n ++ " for random Z"
  | otherwise = choose (0,n-1) >>= \a -> return $ Z a

-- | Random row swap
genX :: Int -> Gen DyadicGen
genX n
  | n <= 1 = error $ "Invalid bound " ++ show n ++ " for random X"
  | otherwise = do
    a <- choose (0,n-1)
    b <- choose (0,n-1) `suchThat` (/= a)
    return $ X a b

-- | Random HH
genHH :: Int -> Gen DyadicGen
genHH n
  | n <= 3 = error $ "Invalid bound " ++ show n ++ " for random HH"
  | otherwise = do
    a <- choose (0,n-1)
    b <- choose (0,n-1) `suchThat` (/= a)
    c <- choose (0,n-1) `suchThat` (`notElem` [a,b])
    d <- choose (0,n-1) `suchThat` (`notElem` [a,b,c])
    return $ HH a b c d

instance Arbitrary DyadicGen where
  arbitrary = sized go where
    go n
      | n < 1 = error $ "Can't generate a generator on " ++ show n ++ " dimensions"
      | 1 <= n && n < 2 = genZ n
      | 2 <= n && n < 4 = oneof [genZ n, genX n]
      | otherwise = oneof [genZ n, genX n, genHH n]
    
instance Nat n => Arbitrary (Matrix n n Dyadic) where
  arbitrary = liftM toMatrix $ listOf (resize (getn nnat) gen) where
    gen  :: Gen DyadicGen
    gen  = arbitrary
    getn :: NNat n -> Int
    getn = fromInteger . fromNNat 

-- | Random (-1) phase
genM :: Int -> Gen DyadicGenAlt
genM n
  | n <= 0 = error $ "Invalid bound " ++ show n ++ " for random Z"
  | otherwise = choose (0,n-1) >>= \a -> return $ M a

-- | Random row swap
genS :: Int -> Gen DyadicGenAlt
genS n
  | n <= 1 = error $ "Invalid bound " ++ show n ++ " for random X"
  | otherwise = do
    a <- choose (0,n-1)
    b <- choose (0,n-1) `suchThat` (/= a)
    return $ S a b

-- | Random R gate
genR :: Int -> Gen DyadicGenAlt
genR n
  | n <= 3 = error $ "Invalid bound " ++ show n ++ " for random R"
  | otherwise = do
    a <- choose (0,n-1)
    b <- choose (0,n-1) `suchThat` (/= a)
    c <- choose (0,n-1) `suchThat` (`notElem` [a,b])
    d <- choose (0,n-1) `suchThat` (`notElem` [a,b,c])
    return $ R a b c d

instance Arbitrary DyadicGenAlt where
  arbitrary = sized go where
    go n
      | n < 1 = error $ "Can't generate a generator on " ++ show n ++ " dimensions"
      | 1 <= n && n < 2 = genM n
      | 2 <= n && n < 4 = oneof [genM n, genS n]
      | otherwise = oneof [genM n, genS n, genR n]

-- | Equality of generators
prop_iso_generators :: Nat n => Matrix n n Dyadic -> [DyadicGen] -> Bool
prop_iso_generators m xs = m * toMatrix xs == toMatrix (dyadicToAlt xs)
  
prop_iso_generators_alt :: Nat n => Matrix n n Dyadic -> [DyadicGenAlt] -> Bool
prop_iso_generators_alt m xs = m * toMatrix xs == toMatrix (altToDyadic xs)

    
-- | Test suite
runTests :: () -> IO ()
runTests () = do
  quickCheck (mapSize (\_ -> 8) (prop_iso_generators (1 :: Matrix Eight Eight Dyadic)))
  quickCheck (mapSize (\_ -> 8) (prop_iso_generators_alt (1 :: Matrix Eight Eight Dyadic)))
  --quickCheck (prop_correct ([] :: [DyadicGen]) :: Matrix Two Two Dyadic -> Bool)
  --quickCheck (prop_correct ([] :: [DyadicGen]) :: Matrix Four Four Dyadic -> Bool)
  --quickCheck (prop_correct ([] :: [DyadicGen]) :: Matrix Eight Eight Dyadic -> Bool)
