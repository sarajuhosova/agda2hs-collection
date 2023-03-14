module LawfulTypeClass.Eq.Composed where

open import Haskell.Prelude

import Relation.Binary.PropositionalEquality as PEq
open PEq using (_≡_; sym; cong)

record LawfulEq (e : Set) : Set₁ where
    field
        overlap {{ iEqE }} : Eq e

        equality : ∀ (x y : e) → (x == y) ≡ True → x ≡ y
        equality' : ∀ (x y : e) → x ≡ y → (x == y) ≡ True

    -- https://hackage.haskell.org/package/base-4.17.0.0/docs/Data-Eq.html
    -- Reflexivity: x == x = True
    eqReflexivity : ∀ { x : e } → x ≡ x
    eqReflexivity = refl

    -- Symmetry: x == y = y == x
    eqSymmetry : ∀ { x y : e } → x ≡ y → y ≡ x
    eqSymmetry h = sym h

    -- Transitivity: if x == y && y == z = True, then x == z = True
    eqTransitivity : ∀ { x y z : e } → x ≡ y → y ≡ z → x ≡ z
    eqTransitivity refl refl = refl

    -- Extensionality: if x == y = True and f is a function whose return type is an instance of Eq, then f x == f y = True
    eqExtensionality : { e' : Set } → {{ iLawEq : LawfulEq e' }} 
        → ∀ { x y : e } (f : e → e') → x ≡ y → f x ≡ f y
    eqExtensionality f h = cong f h

    -- Negation: x /= y = not (x == y)
    eqNegation : ∀ { x y : e } → (x /= y) ≡ not (x == y)
    eqNegation = refl
        
open LawfulEq ⦃ ... ⦄ public
 