module Lib.BoxedProof where

open import Haskell.Prelude

record ∃ (A : Set) (P : A → Set) : Set where
  constructor _[_]
  field
    el : A
    @0 pf : P el
open ∃ public

{-# COMPILE AGDA2HS ∃ unboxed #-}
