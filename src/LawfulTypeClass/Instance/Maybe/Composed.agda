module LawfulTypeClass.Instance.Maybe.Composed where

open import Haskell.Prelude

import Relation.Binary.PropositionalEquality as PEq
open PEq using ( refl; sym; cong )

open import LawfulTypeClass.Eq.Composed

equalityMaybe : {{ iLawEqA : LawEq a }}
  → ∀ (x y : Maybe a) → (x == y) ≡ True → x ≡ y
equalityMaybe Nothing Nothing _ = refl
equalityMaybe {{ lEq }} (Just x) (Just y) h
  = cong Just (LawEq.equality lEq x y h)

equalityMaybe' : {{ iLawEqA : LawEq a }}
  → ∀ (x y : Maybe a) → x ≡ y → (x == y) ≡ True
equalityMaybe' Nothing Nothing _ = refl
equalityMaybe' {{ lEq }} (Just x) (Just y) refl
  = LawEq.equality' lEq x y refl

instance
  iLawMaybe : {{ iLawEqA : LawEq a }} → LawEq (Maybe a)
  iLawMaybe = λ where
    .iEqE → iEqMaybe
    .equality → equalityMaybe
    .equality' → equalityMaybe'
