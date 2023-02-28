module FlowWitness.Witness where

open import Haskell.Prelude

record Witness (A : Set) (a : A) : Set where
  constructor _[_]
  field
    el : A
    @0 pf : _≡_ a el
open Witness public

{-# COMPILE AGDA2HS Witness unboxed #-}

witness : {A : Set} → (a : A) → Witness A a
witness a = a [ refl ]

{-# COMPILE AGDA2HS witness #-}

-- record Unboxable (a b : Set) : Set where
--   field
--     unbox : b → a

-- open Unboxable ⦃ ... ⦄ public

-- {-# COMPILE AGDA2HS Unboxable class #-}

-- instance
--   iUnboxableWitness : Unboxable a (Witness a a)
--   iUnboxableWitness = ?
