module FlowWitness.Witness where

open import Haskell.Prelude

record Witness (A : Set) (a : A) : Set where
  constructor _[_]
  field
    el : A
    @0 pf : _≡_ a el
open Witness public

{-# COMPILE AGDA2HS Witness unboxed #-}

toWitness : {A : Set} → (a : A) → Witness A a
toWitness a = a [ refl ]

{-# COMPILE AGDA2HS toWitness #-}
