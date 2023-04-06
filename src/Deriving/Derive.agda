module Deriving.Derive where

open import Haskell.Prelude

data Direction : Set where
  North : Direction
  South : Direction
  East  : Direction
  West  : Direction

{-# COMPILE AGDA2HS Direction #-}

instance
  iEqDirection : Eq Direction
  iEqDirection ._==_ North North = True
  iEqDirection ._==_ South South = True
  iEqDirection ._==_ East  East  = True
  iEqDirection ._==_ West  West  = True
  iEqDirection ._==_ _     _     = False

{-# COMPILE AGDA2HS iEqDirection derive #-}

record Clazz (a : Set) : Set where
  field
    foo : a → Int
    bar : a → Bool

open Clazz ⦃...⦄ public

{-# COMPILE AGDA2HS Clazz class #-}

postulate instance iDirectionClazz : Clazz Direction

{-# COMPILE AGDA2HS iDirectionClazz derive anyclass #-}
