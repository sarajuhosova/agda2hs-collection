module Deriving.New where

open import Haskell.Prelude

data Direction : Set where
  North : Direction
  South : Direction
  East  : Direction
  West  : Direction

postulate instance
  iEqDirection : Eq Direction
  iShowDirection : Show Direction

{-# COMPILE AGDA2HS Direction #-}
{-# COMPILE AGDA2HS iEqDirection #-}
{-# COMPILE AGDA2HS iShowDirection #-}
