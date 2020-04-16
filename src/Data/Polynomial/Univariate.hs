{-|
Module      : Univariate
Description : Univariate polynomials (notably cyclotomics)
Maintainer  : matt.e.amy@gmail.com
Stability   : experimental
Portability : portable
-}

module Data.Polynomial.Univariate(
  Univariate,
  degree,
  var,
  constant,
  rmult,
  add,
  mult)
where

import Data.List
import Data.Map(Map)
import qualified Data.Map as Map

import qualified Utils.Unicode as Unicode

{-------------------------------
 Univariate polynomials
 -------------------------------}

-- | Univariate polynomials over the ring 'r'
data Univariate r = Univariate { getCoeffs :: !(Map Integer r) } deriving (Eq, Ord)

instance (Eq r, Num r, Show r) => Show (Univariate r) where
  show = showWithName "x"

-- | Retrieve the degree of the polynomial
degree :: Univariate r -> Integer
degree = maybe 0 (fromIntegral . fst) . Map.lookupMax . getCoeffs

-- | Print a univariate polynomial with a particular variable name
showWithName :: (Eq r, Num r, Show r) => String -> Univariate r -> String
showWithName x p
    | p == 0    = "0"
    | otherwise = intercalate " + " $ map showTerm (Map.assocs $ getCoeffs p)
    where showTerm (expt, a)
            | expt == 0  = show a
            | a    == 1  = showExpt expt
            | a    == -1 = "-" ++ showExpt expt
            | otherwise  = show a ++ showExpt expt
          showExpt expt
            | expt == 1  = x
            | otherwise  = Unicode.sup x expt

instance (Eq r, Num r) => Num (Univariate r) where
  (+)           = add
  (*)           = mult
  negate        = Univariate . Map.map negate . getCoeffs
  abs           = id
  signum        = id
  fromInteger 0 = Univariate Map.empty
  fromInteger i = Univariate $ Map.singleton 0 (fromInteger i)

-- | Normalize a univariate polynomial
normalize :: (Eq r, Num r) => Univariate r -> Univariate r
normalize = Univariate . Map.filter (/=0) . getCoeffs

-- | The unique univariate variable
var :: Num r => Univariate r
var = Univariate $ Map.singleton 1 1

-- | Constant polynomial
constant :: (Eq r, Num r) => r -> Univariate r
constant a
  | a == 0    = Univariate $ Map.empty
  | otherwise = Univariate $ Map.singleton 0 a

-- | Multiply by a scalar
rmult :: (Eq r, Num r) => r -> Univariate r -> Univariate r
rmult 0 = \_p -> 0
rmult a = Univariate . Map.map (a*) . getCoeffs

-- | Add two univariate polynomials
add :: (Eq r, Num r) => Univariate r -> Univariate r -> Univariate r
add p = normalize . Univariate . Map.unionWith (+) (getCoeffs p) . getCoeffs

-- | Multiply two univariate polynomials
mult :: (Eq r, Num r) => Univariate r -> Univariate r -> Univariate r
mult p = normalize . Map.foldrWithKey (\expt a -> add (mulTerm expt a)) 0 . getCoeffs
  where mulTerm expt a = Univariate . Map.mapKeysMonotonic (+ expt) . Map.map (* a) $ getCoeffs p

