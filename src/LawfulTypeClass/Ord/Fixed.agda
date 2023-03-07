module LawfulTypeClass.Ord.Fixed where

open import Haskell.Prelude using ( Bool; True; False; Ordering; a; LT; GT; EQ; if_then_else_ )

open import LawfulTypeClass.Eq.Fixed

import Relation.Binary.PropositionalEquality as PEq
open PEq using (_≡_; refl; sym; cong)

record Ord (a : Set) : Set where
  field
    compare : a → a → Ordering
    _<_  : a → a → Bool
    _>_  : a → a → Bool
    _>=_ : a → a → Bool
    _<=_ : a → a → Bool
    max  : a → a → a
    min  : a → a → a
    overlap ⦃ super ⦄ : Eq a

  infix 4 _<_ _>_ _<=_ _>=_

open Ord ⦃ ... ⦄ public

ordFromCompare : ⦃ Eq a ⦄ → (a → a → Ordering) → Ord a
ordFromCompare cmp .compare = cmp
ordFromCompare cmp ._<_  x y = cmp x y == LT
ordFromCompare cmp ._>_  x y = cmp x y == GT
ordFromCompare cmp ._<=_ x y = cmp x y /= GT
ordFromCompare cmp ._>=_ x y = cmp x y /= LT
ordFromCompare cmp .max  x y = if cmp x y == LT then y else x
ordFromCompare cmp .min  x y = if cmp x y == GT then y else x

instance
    iOrdBool : Ord Bool
    iOrdBool = ordFromCompare λ where
        False True  → LT
        True  False → GT
        _     _     → EQ
