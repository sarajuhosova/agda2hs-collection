module Lib.InfInt where

open import Haskell.Prelude

data InfInt : Set where
    NegInf : InfInt
    IInt : Int → InfInt
    PosInf : InfInt

{-# COMPILE AGDA2HS InfInt #-}

eqInfInt : InfInt → InfInt → Bool
eqInfInt NegInf NegInf = True
eqInfInt (IInt i) (IInt j) = i == j
eqInfInt PosInf PosInf = True
eqInfInt _ _ = False

ltInfInt : InfInt → InfInt → Bool
ltInfInt NegInf _ = True
ltInfInt (IInt i) (IInt j) = i < j
ltInfInt _ PosInf = True
ltInfInt _ _ = False

{-# COMPILE AGDA2HS eqInfInt #-}
{-# COMPILE AGDA2HS ltInfInt #-}

instance
    iEqInfInt : Eq InfInt
    iEqInfInt ._==_ = eqInfInt

    iOrdInfInt : Ord InfInt
    iOrdInfInt .compare x y = if (ltInfInt x y) then LT else if x == y then EQ else GT
    iOrdInfInt ._<_  x y = (ltInfInt x y)
    iOrdInfInt ._>_  x y = (ltInfInt y x)
    iOrdInfInt ._<=_ x y = (ltInfInt x y) || x == y
    iOrdInfInt ._>=_ x y = (ltInfInt y x) || x == y
    iOrdInfInt .max  x y = if (ltInfInt x y) then y else x
    iOrdInfInt .min  x y = if (ltInfInt y x) then y else x

{-# COMPILE AGDA2HS iEqInfInt #-}
{-# COMPILE AGDA2HS iOrdInfInt #-}
