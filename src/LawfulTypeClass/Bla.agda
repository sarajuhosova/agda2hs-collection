module LawfulTypeClass.Bla where

open import Haskell.Prim
open import Haskell.Prim.Bool
open import Haskell.Prim.Eq
open import Haskell.Prim.Maybe
open import Haskell.Prim.Ord

open import Haskell.Law.Bool
open import Haskell.Law.Eq
open import Haskell.Law.Equality hiding ( begin_; _≡⟨⟩_; step-≡; _∎ )
open import Haskell.Law.Maybe
open import Haskell.Law.Ord.Def

import Relation.Binary.PropositionalEquality as PEq
open PEq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

bla : ⦃ iOrdA : Ord a ⦄ → ⦃ iLawfulOrd : IsLawfulOrd a ⦄
  → ∀ (x y : a) → ((compare x y) == GT) ≡ (x > y)
bla ⦃ iLawfulOrd = lOrd ⦄ x y with ((compare x y) == GT) in h
... | True  =
        begin
          ((compare x y) == GT)
        ≡⟨ {!   !} ⟩
          {!  True !}
        ≡⟨ {!   !} ⟩
          (x > y)
        ∎
... | False = {!   !}

lt2gtMaybeJust : ⦃ iOrdA : Ord a ⦄ → ⦃ iLawfulOrd : IsLawfulOrd a ⦄
  → ∀ (x y : a) → ((Just x) > (Just y)) ≡ ((Just y) < (Just x))
lt2gtMaybeJust ⦃ iLawfulOrd = lOrd ⦄ x y =
  begin
    ((Just x) > (Just y))
  ≡⟨⟩
    compare x y == GT
  ≡⟨ bla x y ⟩
    x > y
  ≡⟨ IsLawfulOrd.lt2gt lOrd x y ⟩
    y < x
  ≡⟨ {!   !} ⟩
    compare y x == LT
  ≡⟨⟩
    ((Just y) < (Just x))
  ∎