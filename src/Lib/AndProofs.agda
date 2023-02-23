module Lib.AndProofs where

open import Haskell.Prelude

&&-left-assoc : ∀ (a b c : Bool) → (a && b && c) ≡ True → ((a && b) && c) ≡ True
&&-left-assoc True True True h = refl

&&-leftTrue : ∀ (a b : Bool) → (a && b) ≡ True → a ≡ True
&&-leftTrue True True h = refl

&&-rightTrue : ∀ (a b : Bool) → (a && b) ≡ True → b ≡ True
&&-rightTrue True True h = refl

&&-true : ∀ (a) → a ≡ (a && True)
&&-true False = refl
&&-true True = refl

&&-true' : ∀ (a) → (a && True) ≡ True → a ≡ True
&&-true' True _ = refl
