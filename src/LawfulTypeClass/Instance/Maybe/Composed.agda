module LawfulTypeClass.Instance.Maybe.Composed where

open import Haskell.Prelude

import Relation.Binary.PropositionalEquality as PEq
open PEq using ( refl; sym; cong )

open import LawfulTypeClass.Eq.Composed

equalityMaybe : {{ iLawfulEqA : LawfulEq a }}
  → ∀ (x y : Maybe a) → (x == y) ≡ True → x ≡ y
equalityMaybe Nothing Nothing _ = refl
equalityMaybe {{ lEq }} (Just x) (Just y) h
  = cong Just (LawfulEq.equality lEq x y h)

equalityMaybe' : {{ iLawfulEqA : LawfulEq a }}
  → ∀ (x y : Maybe a) → x ≡ y → (x == y) ≡ True
equalityMaybe' Nothing Nothing _ = refl
equalityMaybe' {{ lEq }} (Just x) (Just y) refl
  = LawfulEq.equality' lEq x y refl

instance
  iLawfulMaybe : {{ iLawfulEqA : LawfulEq a }} → LawfulEq (Maybe a)
  iLawfulMaybe = λ where
    .iEqE → iEqMaybe
    .equality → equalityMaybe
    .equality' → equalityMaybe'
