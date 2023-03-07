module LawfulTypeClass.Eq.Extended1 where

open import Haskell.Prelude

import Relation.Binary.PropositionalEquality as PEq
open PEq using (_≡_; sym; cong)

record LawfulEq₁ (e : Set) {{iEq : Eq e}} : Set₁ where
    field
        equality  : ∀ (x y : e) → (x == y) ≡ True → x ≡ y
        equality' : ∀ (x y : e) → x ≡ y → (x == y) ≡ True

    -- https://hackage.haskell.org/package/base-4.17.0.0/docs/Data-Eq.html
    -- Reflexivity: x == x = True
    reflexivity₁ : ∀ (x : e) → x ≡ x
    reflexivity₁ _ = refl

    -- Symmetry: x == y = y == x
    symmetry₁ : ∀ (x y : e) → x ≡ y → y ≡ x
    symmetry₁ _ _ h = sym h

    -- Transitivity: if x == y && y == z = True, then x == z = True
    transitivity₁ : ∀ (x y z : e) → x ≡ y → y ≡ z → x ≡ z
    transitivity₁ _ _ _ refl refl = refl

    -- Extensionality: if x == y = True and f is a function whose return type is an instance of Eq, then f x == f y = True
    extensionality₁ : {e' : Set} → {{iEq : Eq e'}} → {{iLawfulEq : LawfulEq₁ e'}} 
        → ∀ (x y : e) (f : e → e') → x ≡ y → f x ≡ f y
    extensionality₁ _ _ f h = cong f h

    -- Negation: x /= y = not (x == y)
    negation₁ : ∀ (x y : e) → (x /= y) ≡ not (x == y)
    negation₁ _ _ = refl
        
open LawfulEq₁ ⦃ ... ⦄ public
