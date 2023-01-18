module Interpreter.InterpEq where

open import Haskell.Prelude
open import Interpreter.Lang
open import Interpreter.Interp using (interp)
open import Interpreter.Safe using (safeInterp)

import Relation.Binary.PropositionalEquality as PEq
open PEq using (_≡_; refl; cong; sym)
open PEq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

interpEq : (e : Expr) → (interp e == safeInterp e) ≡ True
interpEq (EBool b) =
    begin
        interp (EBool b) == safeInterp (EBool b)
    ≡⟨⟩
        {!   !}
    ≡⟨ {!   !} ⟩
        {!   !}
    ≡⟨⟩
        True
    ∎
interpEq (EInt x) = {!   !}
interpEq (EAdd e e₁) = {!   !}
interpEq (EEq e e₁) = {!   !}
interpEq (ENot e) = {!   !}
interpEq (EAnd e e₁) = {!   !}
interpEq (EOr e e₁) = {!   !}

