module Deriving.Original where

open import Haskell.Prelude

data Direction : Set where
  North : Direction
  South : Direction
  East  : Direction
  West  : Direction

{-# COMPILE AGDA2HS Direction deriving (Eq, Show) #-}
 