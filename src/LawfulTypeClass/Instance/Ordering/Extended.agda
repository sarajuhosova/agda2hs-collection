module LawfulTypeClass.Instance.Ordering.Extended where

open import Haskell.Prelude

import Relation.Binary.PropositionalEquality as PEq
open PEq using ( refl; sym; cong )

open import LawfulTypeClass.Eq.Extended
open import LawfulTypeClass.Ord.Extended

open import LawfulTypeClass.Instance.Ordering.Util

instance
    iLawfulOrdering : IsLawfulEq Ordering
    iLawfulOrdering = λ where
        .equality → equalityOrdering
        .equality' → equalityOrdering'

    iLawfulOrdOrdering : IsLawfulOrd Ordering
    iLawfulOrdOrdering = λ where
        .comparability → compOrdering
        .transitivity → transOrdering
        .reflexivity → reflOrdering
        .antisymmetry → antisymOrdering
        .lte2gte → lte2gteOrdering
        .lNotLteNeq → lNotLteNeqOrdering
        .lt2gt → lt2gtOrdering
        .compareLt → compareLtOrdering
        .compareLt' → compareLtOrdering'
        .compareGt → compareGtOrdering
        .compareGt' → compareGtOrdering'
        .compareEq → compareEqOrdering
        .compareEq' → compareEqOrdering'
        .min2if → min2ifOrdering
        .max2if → max2ifOrdering
        