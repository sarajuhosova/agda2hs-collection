module LawfulTypeClass.Instance.Ordering.Extended where

open import Haskell.Prelude

import Relation.Binary.PropositionalEquality as PEq
open PEq using ( refl; sym; cong )

open import LawfulTypeClass.Eq.Extended
open import LawfulTypeClass.Ord.Extended

open import LawfulTypeClass.Instance.Ordering.Util

instance
    iLawfulOrdering : LawfulEq₂ Ordering
    iLawfulOrdering = λ where
        .equality → equalityOrdering
        .equality' → equalityOrdering'

    iLawfulOrdOrdering : LawfulOrd Ordering
    iLawfulOrdOrdering = λ where
        .comparability → compOrdering
        .transitivity → transOrdering
        .reflexivity → reflOrdering
        .antisymmetry → antisymOrdering
