module Lib.LawfulEq where

open import Haskell.Prelude

import Relation.Binary.PropositionalEquality as PEq
open PEq using (_≡_; cong)

{-# NO_POSITIVITY_CHECK #-}
record LawfulEq (e : Set) {{iEq : Eq e}} : Set₁ where
    inductive; field
        equality : ∀ (x y : e) → (x == y) ≡ True → x ≡ y
        equality' : ∀ (x y : e) → x ≡ y → (x == y) ≡ True

        -- https://hackage.haskell.org/package/base-4.17.0.0/docs/Data-Eq.html
        -- Reflexivity: x == x = True
        reflexivity : ∀ (x : e) → (x == x) ≡ True

        -- Symmetry: x == y = y == x
        symmetry : ∀ (x y : e) → (x == y) ≡ (y == x)

        -- Transitivity: if x == y && y == z = True, then x == z = True
        transitivity : ∀ (x y z : e) 
                         → (x == y) ≡ True → (y == z) ≡ True 
                         → (x == z) ≡ True

        -- Extensionality: if x == y = True and f is a function whose return type is an instance of Eq, then f x == f y = True
        extensionality : {{iEq : Eq b}} → {{iLawfulEq : LawfulEq b}} 
            → ∀ (x y : e) (f : e → b)
            → (x == y) ≡ True
            → (f x == f y) ≡ True

        -- Negation: x /= y = not (x == y)
        negation : ∀ (x y : e) → (x /= y) ≡ not (x == y)

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

transitivityBool' : ∀ (x y z : Bool) → (x ≡ y) → (y ≡ z) → (x ≡ z)
transitivityBool' x .x .x refl refl = refl

transitivityBoolVerbose : ∀ (x y z : Bool) 
            → (x == y) ≡ True → (y == z) ≡ True
            → (x == z) ≡ True
transitivityBoolVerbose False False False _ _ = refl
transitivityBoolVerbose True True True _ _ = refl

transitivityBool : ∀ (x y z : Bool) 
            → (x == y) ≡ True → (y == z) ≡ True
            → (x == z) ≡ True
transitivityBool x y z h1 h2 = 
  equalityBool' x z (transitivityBool' x y z (equalityBool x y h1) (equalityBool y z h2))

extensionalityBool' : {{iEq : Eq b}} → ∀ (x y : Bool) (f : Bool → b)
            → x ≡ y → f x ≡ f y
extensionalityBool' x .x f refl = refl

extensionalityBool : {{iEq : Eq b}} → {{iLawfulEq : LawfulEq b}} 
            → ∀ (x y : Bool) (f : Bool → b)
            → (x == y) ≡ True
            → (f x == f y) ≡ True
extensionalityBool x y f h = 
  equality' (f x) (f y) (extensionalityBool' x y f (equalityBool x y h))

instance
  _ : LawfulEq Bool
  _ = λ where
    .equality → equalityBool
    .equality' → equalityBool'
    .reflexivity → reflexivityBool
    .symmetry → symmetryBool
    .transitivity → transitivityBool
    .extensionality → extensionalityBool
    .negation → λ x y → refl

