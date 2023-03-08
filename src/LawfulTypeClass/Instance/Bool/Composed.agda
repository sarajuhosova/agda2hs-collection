module LawfulTypeClass.Instance.Bool.Composed where

open import Haskell.Prelude

import Relation.Binary.PropositionalEquality as PEq
open PEq using ( refl; sym; cong )

open import LawfulTypeClass.Eq.Composed

open import LawfulTypeClass.Instance.Bool.Util

instance
  iLawBool : LawEq Bool
  iLawBool = λ where
    .iEqE → iEqBool
    .equality → equalityBool
    .equality' → equalityBool'
