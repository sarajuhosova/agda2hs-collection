{-# OPTIONS --allow-unsolved-metas #-}

module FlowWitness.Playground where

open import Haskell.Prelude

import Relation.Binary.PropositionalEquality as PEq
open PEq using (_≡_; refl; cong; sym)
open PEq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

-- ABSOLUTE -----------------------------------

boolCase : Bool → Int → Int → Int
boolCase b tru fls = case b of λ where
    True → tru
    False → fls

{-# COMPILE AGDA2HS boolCase #-}

absolute : Int → Int
absolute i = boolCase (i < 0) (-1 * i) i

{-# COMPILE AGDA2HS absolute #-}

caseTakesTrueBranch : ∀ (i j : Int) → boolCase True i j ≡ i
caseTakesTrueBranch i j = refl

timesNeq1MakesPositive : ∀ (i : Int) → (i < 0) ≡ True → ((-1 * i) > 0) ≡ True
timesNeq1MakesPositive i h =
    begin
        (-1 * i) > 0
    ≡⟨⟩
        {!   !}
    ≡⟨ {!   !} ⟩
        True
    ∎

negativeTurnsPositive : ∀ (i : Int) → (i < 0) ≡ True → (absolute i > 0) ≡ True
negativeTurnsPositive i h =
    begin
        absolute i > 0
    ≡⟨⟩
        (boolCase (i < 0) (-1 * i) i) > 0
    ≡⟨ cong (λ b → (boolCase b (-1 * i) i) > 0) h ⟩
        (boolCase True (-1 * i) i) > 0
    ≡⟨ cong (λ b → b > 0) (caseTakesTrueBranch (-1 * i) i) ⟩
        (-1 * i) > 0
    ≡⟨ timesNeq1MakesPositive i h ⟩
        True
    ∎