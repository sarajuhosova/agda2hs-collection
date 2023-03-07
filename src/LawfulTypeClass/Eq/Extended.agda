module LawfulTypeClass.Eq.Extended where

open import Haskell.Prelude

{-# NO_POSITIVITY_CHECK #-}
record LawfulEq (e : Set) {{iEq : Eq e}} : Set₁ where
    field
        equality  : ∀ (x y : e) → (x == y) ≡ True → x ≡ y
        equality' : ∀ (x y : e) → x ≡ y → (x == y) ≡ True

        -- https://hackage.haskell.org/package/base-4.17.0.0/docs/Data-Eq.html
        -- Reflexivity: x == x = True
        reflexivity : ∀ (x : e) → x ≡ x

        -- Symmetry: x == y = y == x
        symmetry : ∀ (x y : e) → x ≡ y → y ≡ x

        -- Transitivity: if x == y && y == z = True, then x == z = True
        transitivity : ∀ (x y z : e) → x ≡ y → y ≡ z → x ≡ z

        -- Extensionality: if x == y = True and f is a function whose return type is an instance of Eq, then f x == f y = True
        extensionality : {e' : Set} → {{iEq : Eq e'}} → {{iLawfulEq : LawfulEq e'}} 
            → ∀ (x y : e) (f : e → e') → x ≡ y → f x ≡ f y

        -- Negation: x /= y = not (x == y)
        negation : ∀ (x y : e) → (x /= y) ≡ not (x == y)
        
open LawfulEq ⦃ ... ⦄ public
