module LawfulTypeClass.Instance.Maybe.Extended where

open import Haskell.Prelude

open import LawfulTypeClass.Eq.Extended

open import LawfulTypeClass.Instance.Maybe.Util

instance
  iLawfulMaybe₂ : {{ iEqA : Eq a }} → {{ iLawfulEqA : LawfulEq₂ a }} → LawfulEq₂ (Maybe a)
  iLawfulMaybe₂ = λ where
    .equality → equalityMaybe
    .equality' → equalityMaybe'

