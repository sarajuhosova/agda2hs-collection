module LawfulTypeClass.Example.Ordered.Composed where

open import Haskell.Prelude

open import LawfulTypeClass.Example.Ordered.Data

import Relation.Binary.PropositionalEquality as PEq
open PEq using ( _≡_; refl )
open PEq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

open import LawfulTypeClass.Eq.Composed
open import LawfulTypeClass.Ord.Composed

order : {{ iLawfulOrd : LawfulOrd a }} → (a' : a) → (a'' : a) → Ordered a
order {{ lOrd }} left right =
    if left < right then 
        Lt left right {{ {!   !} }}
    else (
        if left == right then
            (λ {{ h }} → E left right {{ {!   !} }} )
        else
            Gt left right {{ {!   !} }}
    )

{-# COMPILE AGDA2HS order #-}
