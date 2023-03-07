module LawfulTypeClass.Instance.Maybe.Util where

open import Haskell.Prelude using ( Maybe; Just; Nothing; _==_; True; Eq; a )

import Relation.Binary.PropositionalEquality as PEq
open PEq using ( _≡_; refl; sym; cong )

open import LawfulTypeClass.Eq.Extended

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
