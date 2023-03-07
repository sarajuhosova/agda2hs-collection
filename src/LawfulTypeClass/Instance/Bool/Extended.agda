module LawfulTypeClass.Instance.Bool.Extended where

open import Haskell.Prelude

import Relation.Binary.PropositionalEquality as PEq
open PEq using ( refl; sym; cong )

open import LawfulTypeClass.Eq.Extended

open import LawfulTypeClass.Instance.Bool.Util

instance
    iLawfulBool : LawfulEq Bool
    iLawfulBool = λ where
        .equality → equalityBool
        .equality' → equalityBool'
        .reflexivity → λ _ → refl
        .symmetry → λ _ _ h → sym h
        .transitivity → λ _ _ _ hxy hyx → {!  !}
        .extensionality → λ _ _ f h → cong f h
        .negation → λ _ _ → refl

    iLawfulBool₁ : LawfulEq₁ Bool
    iLawfulBool₁ = λ where
        .equality → equalityBool
        .equality' → equalityBool'

    iLawfulBool₂ : LawfulEq₂ Bool
    iLawfulBool₂ = λ where
        .equality → equalityBool
        .equality' → equalityBool'
