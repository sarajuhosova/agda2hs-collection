module LawfulTypeClass.Instance.Maybe.Extended where

open import Haskell.Prelude

import Relation.Binary.PropositionalEquality as PEq
open PEq using ( _≡_; refl; sym; cong )
open PEq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

open import LawfulTypeClass.Eq.Extended
open import LawfulTypeClass.Ord.Extended

open import LawfulTypeClass.Instance.Maybe.Util

instance
    iLawfulMaybe : {{ iEqA : Eq a }} → {{ iLawfulEqA : IsLawfulEq a }} → IsLawfulEq (Maybe a)
    iLawfulMaybe = λ where
        .equality → equalityMaybe
        .equality' → equalityMaybe'

    iLawfulOrdMaybe : {{ iOrdA : Ord a }} → {{ iLawfulOrdA : IsLawfulOrd a }} → IsLawfulOrd (Maybe a)
    iLawfulOrdMaybe = λ where
        .comparability → compMaybe
        .transitivity → transMaybe
        .reflexivity → reflMaybe
        .antisymmetry → antisymMaybe
        .lte2gte → lte2gteMaybe
        .lNotLteNeq → lNotLteNeqMaybe
        .lt2gt → lt2gtMaybe
        .compareLt → compareLtMaybe
        .compareLt' → compareLtMaybe'
        .compareGt → compareGtMaybe
        .compareGt' → compareGtMaybe'
        .compareEq → compareEqMaybe
        .compareEq' → compareEqMaybe'
        .min2if → min2ifMaybe
        .max2if → max2ifMaybe

