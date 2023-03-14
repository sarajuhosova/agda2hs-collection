module LawfulTypeClass.Instance.Int.Extended where

open import Haskell.Prelude

import Relation.Binary.PropositionalEquality as PEq
open PEq using ( refl; sym; cong )

open import LawfulTypeClass.Eq.Extended
open import LawfulTypeClass.Ord.Extended

open import LawfulTypeClass.Instance.Int.Util

instance
    iLawfulInt : LawfulEq Int
    iLawfulInt = λ where
        .equality → equalityInt
        .equality' → equalityInt'
        .reflexivity → λ _ → refl
        .symmetry → λ _ _ h → sym h
        .transitivity → λ _ _ _ hxy hyx → {!  !}
        .extensionality → λ _ _ f h → cong f h
        .negation → λ _ _ → refl

    iLawfulInt₁ : LawfulEq₁ Int
    iLawfulInt₁ = λ where
        .equality → equalityInt
        .equality' → equalityInt'

    iLawfulInt₂ : IsLawfulEq Int
    iLawfulInt₂ = λ where
        .equality → equalityInt
        .equality' → equalityInt'

    iLawfulOrdInt : IsLawfulOrd Int
    iLawfulOrdInt = λ where
        .comparability → compInt
        .transitivity → transInt
        .reflexivity → reflInt
        .antisymmetry → antisymInt
        .lte2gte → lte2gteInt
        .lNotLteNeq → lNotLteNeqInt
        .lt2gt → lt2gtInt
        .compareLt → compareLtInt
        .compareLt' → compareLtInt'
        .compareGt → compareGtInt
        .compareGt' → compareGtInt'
        .compareEq → compareEqInt
        .compareEq' → compareEqInt'
        .min2if → min2ifInt
        .max2if → max2ifInt
