module LawfulTypeClass.Eq.IEqBool where

open import Haskell.Prelude

import Relation.Binary.PropositionalEquality as PEq
open PEq using (_≡_; refl; sym; cong)

open import LawfulTypeClass.Eq.Extended
open import LawfulTypeClass.Eq.Extended1
open import LawfulTypeClass.Eq.Extended2
open import LawfulTypeClass.Eq.Composed

equalityBool : ∀ (x y : Bool) → (x == y) ≡ True → x ≡ y
equalityBool False False _ = refl
equalityBool True True _ = refl

equalityBool' : ∀ (x y : Bool) → x ≡ y → (x == y) ≡ True
equalityBool' False False _ = refl
equalityBool' True True _ = refl

instance
  iLawfulBool : LawfulEq Bool
  iLawfulBool = λ where
    .equality → equalityBool
    .equality' → equalityBool'
    .reflexivity → λ _ → refl
    .symmetry → λ _ _ h → sym h
    .transitivity → λ _ _ _ hxy hyx → {!  !}
    .extensionality → λ _ _ f h → cong f h
    .negation → λ _ _ → refl
  
  iLawfulBool₁ : LawfulEq₁ Bool
  iLawfulBool₁ = λ where
    .equality → equalityBool
    .equality' → equalityBool'
  
  iLawfulBool₂ : LawfulEq₂ Bool
  iLawfulBool₂ = λ where
    .equality → equalityBool
    .equality' → equalityBool'

  iLawBool : LawEq Bool
  iLawBool = λ where
    .iEqE → iEqBool
    .equality → {!   !}
    .equality' → {!   !}
    .reflexivity → λ _ → refl
    .symmetry → λ _ _ h → sym h
    .transitivity → λ _ _ _ hxy hyx → {!  !}
    .extensionality → λ _ _ f h → cong f h
    .negation → λ _ _ → refl
