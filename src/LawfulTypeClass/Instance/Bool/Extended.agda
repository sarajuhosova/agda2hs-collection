module LawfulTypeClass.Instance.Bool.Extended where

open import Haskell.Prelude

import Relation.Binary.PropositionalEquality as PEq
open PEq using ( refl; sym; cong )

open import LawfulTypeClass.Eq.Extended
open import LawfulTypeClass.Ord.Extended

open import LawfulTypeClass.Instance.Bool.Util

instance
    iLawfulBool : LawfulEq₀ Bool
    iLawfulBool = λ where
        .equality₀ → equalityBool
        .equality'₀ → equalityBool'
        .reflexivity₀ → λ _ → refl
        .symmetry₀ → λ _ _ h → sym h
        .transitivity₀ → λ _ _ _ hxy hyx → {!  !}
        .extensionality₀ → λ _ _ f h → cong f h
        .negation₀ → λ _ _ → refl

    iLawfulBool₁ : LawfulEq₁ Bool
    iLawfulBool₁ = λ where
        .equality₁ → equalityBool
        .equality'₁ → equalityBool'

    iLawfulBool₂ : IsLawfulEq Bool
    iLawfulBool₂ = λ where
        .equality → equalityBool
        .equality' → equalityBool'

    iLawfulOrdBool : IsLawfulOrd Bool
    iLawfulOrdBool = λ where
        .comparability → compBool
        .transitivity → transBool
        .reflexivity → reflBool
        .antisymmetry → antisymBool
        .lte2gte → lte2gteBool
        .lNotLteNeq → lNotLteNeqBool
        .lt2gt → lt2gtBool
        .compareLt → compareLtBool
        .compareLt' → compareLtBool'
        .compareGt → compareGtBool
        .compareGt' → compareGtBool'
        .compareEq → compareEqBool
        .compareEq' → compareEqBool'
        .min2if → min2ifBool
        .max2if → max2ifBool
        