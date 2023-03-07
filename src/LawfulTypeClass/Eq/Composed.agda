module LawfulTypeClass.Eq.Composed where

open import Haskell.Prelude

{-# NO_POSITIVITY_CHECK #-}
record LawEq (e : Set) : Set₁ where
    field
        iEqE : Eq e

        equality : {{ iEqE' : Eq e }} → {{ _ : iEqE ≡ iEqE' }}
            → ∀ (x y : e) → (x == y) ≡ True → x ≡ y
        equality' : {{ iEqE : Eq e }} → ∀ (x y : e) → x ≡ y → (x == y) ≡ True

        -- https://hackage.haskell.org/package/base-4.17.0.0/docs/Data-Eq.html
        -- Reflexivity: x == x = True
        reflexivity : ∀ (x : e) → x ≡ x

        -- Symmetry: x == y = y == x
        symmetry : ∀ (x y : e) → x ≡ y → y ≡ x

        -- Transitivity: if x == y && y == z = True, then x == z = True
        transitivity : ∀ (x y z : e) → x ≡ y → y ≡ z → z ≡ z

        -- Extensionality: if x == y = True and f is a function whose return type is an instance of Eq, then f x == f y = True
        extensionality : {e' : Set} → {{iLawEq : LawEq e'}} 
            → ∀ (x y : e) (f : e → e') → x ≡ y → f x ≡ f y

        -- Negation: x /= y = not (x == y)
        negation : {{ iEqE : Eq e }} → ∀ (x y : e) → (x /= y) ≡ not (x == y)
        
open LawEq ⦃ ... ⦄ public
 