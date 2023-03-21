module LawfulTypeClass.Example.Ordered.Extended where

open import Haskell.Prelude hiding ( IsLawfulOrd )

open import LawfulTypeClass.Example.Ordered.Data

import Relation.Binary.PropositionalEquality as PEq
open PEq using ( _≡_; refl )
open PEq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

open import LawfulTypeClass.Eq.Extended
open import LawfulTypeClass.Ord.Extended

postulate sym' : { a : Set } → {{ iEq : Eq a }} → {{ iLawfulEq : IsLawfulEq a }} → ∀ (x y : a) → (x == y) ≡ (y == x)

neq : { a : Set } → {{ iEq : Eq a }} → {{ iLawfulEq : IsLawfulEq a }} → ∀ (x y : a) → (x == y) ≡ False → (y == x) ≡ False
neq x y h rewrite sym' y x | h = refl

postulate notLtIsGeq : { a : Set } → {{ iOrd : Ord a }} → {{ iLawfulOrd : IsLawfulOrd a }} → ∀ (x y : a) → (x < y) ≡ False → (x >= y) ≡ True

notLtOrEqIsGt : { a : Set } → {{ iOrd : Ord a }} → {{ iLawfulOrd : IsLawfulOrd a }} → ∀ (x y : a) → {{ (x < y) ≡ False }} → {{ (x == y) ≡ False }} → (x > y) ≡ True
notLtOrEqIsGt {{ _ }} {{ lOrd }} x y {{ hLt }} {{ hNEq }} =
    begin
        (x > y)
    ≡⟨ IsLawfulOrd.lt2gt lOrd x y ⟩
        y < x
    ≡⟨ IsLawfulOrd.lNotLteNeq lOrd y x ⟩
        (y <= x && y /= x)
    ≡⟨ cong (λ n → y <= x && n) (cong (λ b → not b) (neq x y hNEq)) ⟩
        (y <= x && True)
    ≡⟨ cong (λ leq → leq && True) (sym (IsLawfulOrd.lte2gte lOrd x y)) ⟩
        (x >= y && True)
    ≡⟨ cong (λ geq → geq && True) (notLtIsGeq x y hLt) ⟩
        True && True
    ≡⟨⟩
        True
    ∎

order : {{ iOrd : Ord a }} → {{ @0 iLawfulOrd : IsLawfulOrd a }} → (a' : a) → (a'' : a) → Ordered a
order {{ iLawfulOrd = lOrd }} left right =
    if left < right then 
        Lt left right
    else (
        if left == right then
            (λ {{ h }} → E left right {{ IsLawfulEq.equality (IsLawfulOrd.super lOrd) left right h }})
        else
            Gt left right {{ notLtOrEqIsGt left right }}
    )

{-# COMPILE AGDA2HS order #-}
