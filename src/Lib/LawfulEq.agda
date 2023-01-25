module Lib.LawfulEq where

open import Haskell.Prelude

import Relation.Binary.PropositionalEquality as PEq
open PEq using (_≡_; cong)

record LawfulEq (e : Set) {{iEq : Eq e}} : Set₁ where
    field
        equality : ∀ (x y : e) → (x == y) ≡ True → x ≡ y
        equality' : ∀ (x y : e) → x ≡ y → (x == y) ≡ True

        -- https://hackage.haskell.org/package/base-4.17.0.0/docs/Data-Eq.html
        -- Reflexivity: x == x = True
        reflexivity : ∀ (x : e) 
                        → (x == x) ≡ True

        -- Symmetry: x == y = y == x
        symmetry : ∀ (x y : e) 
                     → (x == y) ≡ (y == x)

        -- Transitivity: if x == y && y == z = True, then x == z = True
        transitivity : ∀ (x y z : e) 
                         → ((x == y) && (y == z)) ≡ True 
                         → (x == z) ≡ True

        -- Extensionality: if x == y = True and f is a function whose return type is an instance of Eq, then f x == f y = True
        extensionality : {{iEq : Eq b}}
            → ∀ (x y : e) (f : e → b)
            → (x == y) ≡ True
            → (f x == f y) ≡ True

        -- Negation: x /= y = not (x == y)
        negation : ∀ (x y : e)
                     → (x /= y) ≡ not (x == y)

open LawfulEq ⦃ ... ⦄ public

equalityBool : ∀ (x y : Bool) → (x == y) ≡ True → x ≡ y
equalityBool False False _ = refl
equalityBool True True _ = refl

equalityBool' : ∀ (x y : Bool) → x ≡ y → (x == y) ≡ True
equalityBool' False False _ = refl
equalityBool' True True _ = refl

reflexivityBool : ∀ (x : Bool) → (x == x) ≡ True
reflexivityBool False = refl
reflexivityBool True = refl

symmetryBool : ∀ (x y : Bool) → (x == y) ≡ (y == x)
symmetryBool False False = refl
symmetryBool False True = refl
symmetryBool True False = refl
symmetryBool True True = refl

transitivityBool : ∀ (x y z : Bool) → ((x == y) && (y == z)) ≡ True → (x == z) ≡ True
transitivityBool x y z = {!   !}

extensionalityBool' : {{iEq : Eq b}} → ∀ (x y : Bool) (f : Bool → b)
            → x ≡ y → f x ≡ f y
extensionalityBool' x y f h = cong f h

extensionalityBool : {{iEq : Eq b}} -- → {{iLawfulEq : LawfulEq b}} 
            → ∀ (x y : Bool) (f : Bool → b)
            → (x == y) ≡ True
            → (f x == f y) ≡ True
extensionalityBool x y f h = {!   !}

instance
  _ : LawfulEq Bool
  _ = λ where
    .equality → equalityBool
    .equality' → equalityBool'
    .reflexivity → reflexivityBool
    .symmetry → symmetryBool
    .transitivity → λ x y z h → {!   !}
    .extensionality → extensionalityBool
    .negation → λ x y → refl

