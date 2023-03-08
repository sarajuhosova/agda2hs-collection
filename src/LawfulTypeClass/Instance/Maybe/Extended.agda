module LawfulTypeClass.Instance.Maybe.Extended where

open import Haskell.Prelude

import Relation.Binary.PropositionalEquality as PEq
open PEq using ( _≡_; refl; sym; cong )
open PEq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

open import LawfulTypeClass.Eq.Extended
open import LawfulTypeClass.Ord.Extended

open import LawfulTypeClass.Instance.Ordering.Extended

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

reflMaybe : {{ iOrdA : Ord a }} → {{ iLawfulOrdA : LawfulOrd a }}
    → ∀ (x : Maybe a) → (x <= x) ≡ True
reflMaybe Nothing = refl
reflMaybe {{ ord }} {{ lOrd }} (Just x) =
  begin
    (Just x) <= (Just x)
  ≡⟨⟩
    not ((iEqOrdering Eq.== Ord.compare ord x x) GT)
  ≡⟨⟩
    Ord.compare ord x x /= GT
  ≡⟨ {!   !} ⟩
    EQ /= GT
  ≡⟨⟩
    True
  ∎

instance
    iLawfulMaybe₂ : {{ iEqA : Eq a }} → {{ iLawfulEqA : LawfulEq₂ a }} → LawfulEq₂ (Maybe a)
    iLawfulMaybe₂ = λ where
        .equality → equalityMaybe
        .equality' → equalityMaybe'

    iLawfulOrdMaybe : {{ iOrdA : Ord a }} → {{ iLawfulOrdA : LawfulOrd a }} → LawfulOrd (Maybe a)
    iLawfulOrdMaybe = λ where
        .comparability → {!   !}
        .transitivity → {!   !}
        .reflexivity → reflMaybe
        .antisymmetry → {!   !}

