module LawfulTypeClass.Eq.Complete where

open import Haskell.Prelude using ( Bool; True; False; not )

import Relation.Binary.PropositionalEquality as PEq
open PEq using (_≡_; refl; sym; cong)

record Eq (a : Set) : Set where
    infix 4 _==_ _/=_
    field
        _==_ : a → a → Bool

        equality  : ∀ (x y : a) → (x == y) ≡ True → x ≡ y
        equality' : ∀ (x y : a) → x ≡ y → (x == y) ≡ True
        -- equivalent to: ∀ (x y : a) → (x == y) ≡ False → (x ≡ y → ⊥)
    
    _/=_ : a → a → Bool
    x /= y = not (x == y)

    -- https://hackage.haskell.org/package/base-4.17.0.0/docs/Data-Eq.html
    -- Reflexivity: x == x = True
    reflexivity₂ : ∀ { x : a } → x ≡ x
    reflexivity₂ = refl

    -- Symmetry: x == y = y == x
    symmetry₂ : ∀ { x y : a } → x ≡ y → y ≡ x
    symmetry₂ h = sym h

    -- Transitivity: if x == y && y == z = True, then x == z = True
    transitivity₂ : ∀ { x y z : a } → { x ≡ y } → { y ≡ z } → z ≡ z
    transitivity₂ = refl

    -- Extensionality: if x == y = True and f is a function whose return type is an instance of Eq, then f x == f y = True
    extensionality₂ : { a' : Set } → {{ iEq : Eq a' }}
        → ∀ { x y : a } (f : a → a') → x ≡ y → f x ≡ f y
    extensionality₂ f h = cong f h

    -- Negation: x /= y = not (x == y)
    negation₂ : ∀ { x y : a } → (x /= y) ≡ not (x == y)
    negation₂ = refl
        
open Eq ⦃ ... ⦄ public
        

