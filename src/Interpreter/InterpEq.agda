module Interpreter.InterpEq where

open import Haskell.Prelude
open import Interpreter.Lang
open import Interpreter.Interp using (interp)
open import Interpreter.Safe using (safeInterp; simplify)

import Relation.Binary.PropositionalEquality as PEq
open PEq using (_≡_; refl)
open PEq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

≡-interp : ∀ e → interp e ≡ safeInterp e
≡-interp (EBool b) =
    begin
        Just (VBool b)
    ≡⟨ {!   !} ⟩
        safeInterp (EBool b)
    ∎
≡-interp (EInt x) = {!   !}
≡-interp (EAdd left right) = {!   !}
≡-interp (EEq left right) = {!   !}
≡-interp (ENot e) = {!   !}
≡-interp (EAnd left right) = {!   !}
≡-interp (EOr left right) = {!   !}

