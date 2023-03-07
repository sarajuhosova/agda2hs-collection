module LawfulTypeClass.Instance.Bool.Complete where

open import Haskell.Prelude using ( Bool; True; False
                                  ; Ordering; GT; LT; EQ
                                  )

import Relation.Binary.PropositionalEquality as PEq
open PEq using ( _≡_; refl )

open import LawfulTypeClass.Eq.Complete

eqBool : Bool → Bool → Bool
eqBool False False = True
eqBool True  True  = True
eqBool _     _     = False

equalityBool : ∀ (x y : Bool) → eqBool x y ≡ True → x ≡ y
equalityBool False False _ = refl
equalityBool True True _ = refl

equalityBool' : ∀ (x y : Bool) → x ≡ y → eqBool x y ≡ True
equalityBool' False False _ = refl
equalityBool' True True _ = refl

instance
    iEqBool : Eq Bool
    iEqBool = λ where
        ._==_ → eqBool
        .equality → equalityBool
        .equality' → equalityBool'
