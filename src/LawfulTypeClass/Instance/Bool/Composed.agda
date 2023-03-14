module LawfulTypeClass.Instance.Bool.Composed where

open import Haskell.Prelude

import Relation.Binary.PropositionalEquality as PEq
open PEq using ( refl; sym; cong )

open import LawfulTypeClass.Eq.Composed
open import LawfulTypeClass.Ord.Composed

open import LawfulTypeClass.Instance.Bool.Util

instance
  iLawfulBool : LawfulEq Bool
  iLawfulBool = λ where
    .iEqE → iEqBool
    .equality → equalityBool
    .equality' → equalityBool'

  iLawfulOrdBool : LawfulOrd Bool
  iLawfulOrdBool = λ where
    .iLawfulEqE → iLawfulBool
    .iOrdE → iOrdBool
    .ordComparability → compBool  
    .ordTransitivity → transBool
    .ordReflexivity → reflBool
    .ordAntisymmetry → antisymBool
