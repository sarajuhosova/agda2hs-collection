module LawfulTypeClass.Eq.Extended where

open import Haskell.Prelude hiding (IsLawfulEq; equality'; nequality)

import Relation.Binary.PropositionalEquality as PEq
open PEq using (_≡_; _≢_)

{-# NO_POSITIVITY_CHECK #-}
record LawfulEq₀ (e : Set) {{iEq : Eq e}} : Set₁ where
    field
        equality₀  : ∀ (x y : e) → (x == y) ≡ True → x ≡ y
        equality'₀ : ∀ (x y : e) → x ≡ y → (x == y) ≡ True

        -- https://hackage.haskell.org/package/base-4.17.0.0/docs/Data-Eq.html
        -- Reflexivity: x == x = True
        reflexivity₀ : ∀ (x : e) → x ≡ x

        -- Symmetry: x == y = y == x
        symmetry₀ : ∀ (x y : e) → x ≡ y → y ≡ x

        -- Transitivity: if x == y && y == z = True, then x == z = True
        transitivity₀ : ∀ (x y z : e) → x ≡ y → y ≡ z → x ≡ z

        -- Extensionality: if x == y = True and f is a function whose return type is an instance of Eq, then f x == f y = True
        extensionality₀ : {e' : Set} → {{iEq : Eq e'}} → {{iLawfulEq : LawfulEq₀ e'}} 
            → ∀ (x y : e) (f : e → e') → x ≡ y → f x ≡ f y

        -- Negation: x /= y = not (x == y)
        negation₀ : ∀ (x y : e) → (x /= y) ≡ not (x == y)
        
open LawfulEq₀ ⦃ ... ⦄ public

record LawfulEq₁ (e : Set) {{iEq : Eq e}} : Set₁ where
    field
        equality₁  : ∀ (x y : e) → (x == y) ≡ True → x ≡ y
        equality'₁ : ∀ (x y : e) → x ≡ y → (x == y) ≡ True

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

record IsLawfulEq (e : Set) {{iEq : Eq e}} : Set₁ where
    field
        equality  : ∀ (x y : e) → (x == y) ≡ True → x ≡ y
        equality' : ∀ (x y : e) → x ≡ y → (x == y) ≡ True

    postulate nequality : ∀ (x y : e) → (x == y) ≡ False → (x ≡ y → ⊥) -- x ≢ y
    -- nequality x y h = λ eq → case equality' x y eq of λ where r → {!   !}

    -- https://hackage.haskell.org/package/base-4.17.0.0/docs/Data-Eq.html
    -- Reflexivity: x == x = True
    reflexivity' : ∀ { x : e } → x ≡ x
    reflexivity' = refl

    -- Symmetry: x == y = y == x
    symmetry' : ∀ { x y : e } → x ≡ y → y ≡ x
    symmetry' h = sym h

    -- Transitivity: if x == y && y == z = True, then x == z = True
    transitivity' : ∀ { x y z : e } → x ≡ y → y ≡ z → x ≡ z
    transitivity' refl refl = refl

    -- Extensionality: if x == y = True and f is a function whose return type is an instance of Eq, then f x == f y = True
    extensionality' : { e' : Set } → {{ iEq : Eq e' }} → {{ iLawfulEq : IsLawfulEq e' }} 
        → ∀ { x y : e } (f : e → e') → x ≡ y → f x ≡ f y
    extensionality' f h = cong f h

    -- Negation: x /= y = not (x == y)
    negation' : ∀ { x y : e } → (x /= y) ≡ not (x == y)
    negation' = refl
        
open IsLawfulEq ⦃ ... ⦄ public
