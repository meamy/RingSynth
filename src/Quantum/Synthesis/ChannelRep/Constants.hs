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
Module      : Constants
Description : Compile-time constants in the channel representation
Maintainer  : matt.e.amy@gmail.com
Stability   : experimental
Portability : portable
-}

module Quantum.Synthesis.ChannelRep.Constants where

import Quantum.Synthesis.Matrix
import Quantum.Synthesis.Ring
import Quantum.Synthesis.MultiQubitSynthesis
import Quantum.Synthesis.MoreRings

import Quantum.Synthesis.Gates hiding (Integral)
import Quantum.Synthesis.ChannelRep
import Quantum.Synthesis.TypeArith

-- | Two-qubit Pauli rotations

ii = pauliExp @Two "II"
ix = pauliExp @Two "IX"
iy = pauliExp @Two "IY"
iz = pauliExp @Two "IZ"
xi = pauliExp @Two "XI"
xx = pauliExp @Two "XX"
xy = pauliExp @Two "XY"
xz = pauliExp @Two "XZ"
yi = pauliExp @Two "YI"
yx = pauliExp @Two "YX"
yy = pauliExp @Two "YY"
yz = pauliExp @Two "YZ"
zi = pauliExp @Two "ZI"
zx = pauliExp @Two "ZX"
zy = pauliExp @Two "ZY"
zz = pauliExp @Two "ZZ"

-- | Three-qubit Pauli rotations

iii = pauliExp @Three "III"
iix = pauliExp @Three "IIX"
iiy = pauliExp @Three "IIY"
iiz = pauliExp @Three "IIZ"
ixi = pauliExp @Three "IXI"
ixx = pauliExp @Three "IXX"
ixy = pauliExp @Three "IXY"
ixz = pauliExp @Three "IXZ"
iyi = pauliExp @Three "IYI"
iyx = pauliExp @Three "IYX"
iyy = pauliExp @Three "IYY"
iyz = pauliExp @Three "IYZ"
izi = pauliExp @Three "IZI"
izx = pauliExp @Three "IZX"
izy = pauliExp @Three "IZY"
izz = pauliExp @Three "IZZ"
xii = pauliExp @Three "XII"
xix = pauliExp @Three "XIX"
xiy = pauliExp @Three "XIY"
xiz = pauliExp @Three "XIZ"
xxi = pauliExp @Three "XXI"
xxx = pauliExp @Three "XXX"
xxy = pauliExp @Three "XXY"
xxz = pauliExp @Three "XXZ"
xyi = pauliExp @Three "XYI"
xyx = pauliExp @Three "XYX"
xyy = pauliExp @Three "XYY"
xyz = pauliExp @Three "XYZ"
xzi = pauliExp @Three "XZI"
xzx = pauliExp @Three "XZX"
xzy = pauliExp @Three "XZY"
xzz = pauliExp @Three "XZZ"
yii = pauliExp @Three "YII"
yix = pauliExp @Three "YIX"
yiy = pauliExp @Three "YIY"
yiz = pauliExp @Three "YIZ"
yxi = pauliExp @Three "YXI"
yxx = pauliExp @Three "YXX"
yxy = pauliExp @Three "YXY"
yxz = pauliExp @Three "YXZ"
yyi = pauliExp @Three "YYI"
yyx = pauliExp @Three "YYX"
yyy = pauliExp @Three "YYY"
yyz = pauliExp @Three "YYZ"
yzi = pauliExp @Three "YZI"
yzx = pauliExp @Three "YZX"
yzy = pauliExp @Three "YZY"
yzz = pauliExp @Three "YZZ"
zii = pauliExp @Three "ZII"
zix = pauliExp @Three "ZIX"
ziy = pauliExp @Three "ZIY"
ziz = pauliExp @Three "ZIZ"
zxi = pauliExp @Three "ZXI"
zxx = pauliExp @Three "ZXX"
zxy = pauliExp @Three "ZXY"
zxz = pauliExp @Three "ZXZ"
zyi = pauliExp @Three "ZYI"
zyx = pauliExp @Three "ZYX"
zyy = pauliExp @Three "ZYY"
zyz = pauliExp @Three "ZYZ"
zzi = pauliExp @Three "ZZI"
zzx = pauliExp @Three "ZZX"
zzy = pauliExp @Three "ZZY"
zzz = pauliExp @Three "ZZZ"

ccz :: ChannelMatrix Three DRootTwo
ccz = pauliExp @Three "IIZ" *
      pauliExp @Three "IZI" *
      pauliExp @Three "IZZ" *
      pauliExp @Three "ZII" *
      pauliExp @Three "ZIZ" *
      pauliExp @Three "ZZI" *
      pauliExp @Three "ZZZ"

ccxC :: ChannelMatrix Three DRootTwo
ccxC = coerceSubring $ channelRep @Three (ccx 0 1 2 :: QubitMatrix Three DOmega)

tlT :: QubitMatrix Two DOmega
tlT = matrix_of_twolevel $ TL_T 1 2 3

tlTC2 :: ChannelMatrix Two DRootTwo
tlTC2 = coerceSubring $ channelRep @Two tlT

tlW :: QubitMatrix Two DOmega
tlW = matrix_of_twolevels $ twolevels_of_twolevelalts $ [TL_W 1 2 3]

tlW3 :: QubitMatrix Three DOmega
tlW3 = matrix_of_twolevels $ [TL_T 1 0 3, TL_T 7 0 7]

tlWC :: ChannelMatrix Two DRootTwo
tlWC = coerceSubring $ channelRep @Two tlW

tlW3C :: ChannelMatrix Three DRootTwo
tlW3C = coerceSubring $ channelRep @Three tlW3

tlTT :: QubitMatrix Three DOmega
tlTT = tensor tlT (identity :: Matrix Two Two DOmega)

tlTC :: ChannelMatrix Three DRootTwo
tlTC = coerceSubring $ channelRep @Three tlTT

tlTCR :: ChannelMatrix Two DRootTwo
tlTCR = setAncilla @Two 2 tlTC

tmp = xx * xi * ix
tmpRed = residueChannel @Two tmp
xxRed = residueChannel @Two xx

twoLevelT :: forall n . Nat n => Int -> Int -> ChannelMatrix n DRootTwo
twoLevelT i j = coerceSubring $ channelRep @n mat where
  mat :: QubitMatrix n DOmega
  mat = withProof (power_is_nat (nnat @Two) (nnat @n)) $
    matrix_of_twolevels $ [TL_T 1 i j]

twoLevelH :: forall n . Nat n => Int -> Int -> ChannelMatrix n DRootTwo
twoLevelH i j = coerceSubring $ channelRep @n mat where
  mat :: QubitMatrix n DOmega
  mat = withProof (power_is_nat (nnat @Two) (nnat @n)) $
    matrix_of_twolevels $ [TL_H i j]
