module LawfulTypeClass.Eq.Composed where

open import Haskell.Prelude

import Relation.Binary.PropositionalEquality as PEq
open PEq using (_≡_; sym; cong)

record LawEq (e : Set) : Set₁ where
    field
        {{ iEqE }} : Eq e

        equality : ∀ (x y : e) → (x == y) ≡ True → x ≡ y
        equality' : ∀ (x y : e) → x ≡ y → (x == y) ≡ True

    -- https://hackage.haskell.org/package/base-4.17.0.0/docs/Data-Eq.html
    -- Reflexivity: x == x = True
    reflexivity : ∀ { x : e } → x ≡ x
    reflexivity = refl

    -- Symmetry: x == y = y == x
    symmetry : ∀ { x y : e } → x ≡ y → y ≡ x
    symmetry h = sym h

    -- Transitivity: if x == y && y == z = True, then x == z = True
    transitivity : ∀ { x y z : e } → x ≡ y → y ≡ z → x ≡ z
    transitivity refl refl = refl

    -- Extensionality: if x == y = True and f is a function whose return type is an instance of Eq, then f x == f y = True
    extensionality : { e' : Set } → {{ iLawEq : LawEq e' }} 
        → ∀ { x y : e } (f : e → e') → x ≡ y → f x ≡ f y
    extensionality f h = cong f h

    -- Negation: x /= y = not (x == y)
    negation : ∀ { x y : e } → (x /= y) ≡ not (x == y)
    negation = refl
        
open LawEq ⦃ ... ⦄ public
 