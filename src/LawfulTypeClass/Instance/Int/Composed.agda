module LawfulTypeClass.Instance.Int.Composed where

open import Haskell.Prelude

import Relation.Binary.PropositionalEquality as PEq
open PEq using ( refl; sym; cong )

open import LawfulTypeClass.Eq.Composed

open import LawfulTypeClass.Instance.Int.Util

instance
  iLawfulInt : LawfulEq Int
  iLawfulInt = λ where
    .iEqE → iEqInt
    .equality → equalityInt
    .equality' → equalityInt'
