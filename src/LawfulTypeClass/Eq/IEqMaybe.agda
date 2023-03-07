module LawfulTypeClass.Eq.IEqMaybe where

open import Haskell.Prelude

import Relation.Binary.PropositionalEquality as PEq
open PEq using (_≡_; sym; cong)

open import LawfulTypeClass.Eq.Extended
open import LawfulTypeClass.Eq.Extended1
open import LawfulTypeClass.Eq.Extended2
open import LawfulTypeClass.Eq.Composed

equalityMaybe : {{ iEqA : Eq a }} {{ iLawfulEqA : LawfulEq₂ a }}
  → ∀ (x y : Maybe a) → (x == y) ≡ True → x ≡ y
equalityMaybe Nothing Nothing _ = refl
equalityMaybe {{ _ }} {{ lEq }} (Just x) (Just y) h
  = cong Just (LawfulEq₂.equality lEq x y h)

equalityMaybe' : {{ iEqA : Eq a }} {{ iLawfulEqA : LawfulEq₂ a }}
  → ∀ (x y : Maybe a) → x ≡ y → (x == y) ≡ True
equalityMaybe' Nothing Nothing _ = refl
equalityMaybe' {{ _ }} {{ lEq }} (Just x) (Just y) refl
  = LawfulEq₂.equality' lEq x y refl

instance
  iLawfulMaybe₂ : {{ iEqA : Eq a }} → {{ iLawfulEqA : LawfulEq₂ a }} → LawfulEq₂ (Maybe a)
  iLawfulMaybe₂ = λ where
    .equality → equalityMaybe
    .equality' → equalityMaybe'
 