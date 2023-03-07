module LawfulTypeClass.Eq.IEqInt where

open import Haskell.Prelude

import Relation.Binary.PropositionalEquality as PEq
open PEq using (_≡_; sym; cong)

open import LawfulTypeClass.Eq.Extended
open import LawfulTypeClass.Eq.Extended1
open import LawfulTypeClass.Eq.Extended2
open import LawfulTypeClass.Eq.Composed

postulate equalityInt : ∀ (x y : Int) → (x == y) ≡ True → x ≡ y

postulate equalityInt' : ∀ (x y : Int) → x ≡ y → (x == y) ≡ True

instance
  iLawfulInt : LawfulEq Int
  iLawfulInt = λ where
    .equality → equalityInt
    .equality' → equalityInt'
    .reflexivity → λ _ → refl
    .symmetry → λ _ _ h → sym h
    .transitivity → λ _ _ _ hxy hyz → {!   !}
    .extensionality → λ _ _ f h → cong f h
    .negation → λ _ _ → refl
  
  iLawfulInt₁ : LawfulEq₁ Int
  iLawfulInt₁ = λ where
    .equality → equalityInt
    .equality' → equalityInt'
  
  iLawfulInt₂ : LawfulEq₂ Int
  iLawfulInt₂ = λ where
    .equality → equalityInt
    .equality' → equalityInt'

  iLawInt : LawEq Int
  iLawInt = λ where
    .iEqE → iEqInt
    .equality → {!   !}
    .equality' → {!   !}
    .reflexivity → λ _ → refl
    .symmetry → λ _ _ h → sym h
    .transitivity → λ _ _ _ hxy hyz → {!   !}
    .extensionality → λ _ _ f h → cong f h
    .negation → λ _ _ → refl
