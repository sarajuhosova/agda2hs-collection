module Interpreter.Interp where

open import Haskell.Prelude
open import Interpreter.Lang

import Relation.Binary.PropositionalEquality as PEq
open PEq using (_≡_; refl)
open PEq.≡-Reasoning using (begin_; _≡⟨⟩_;  _∎)

------------------------------------------------------------
-- DIRECT INTERPRETER                                     --
------------------------------------------------------------

interp : Expr → Maybe Val
interp (EBool b) = Just (VBool b)
interp (EInt i) = Just (VInt i)
interp (EAdd left right) =
    case (interp left , interp right) of λ where
        (Just (VInt i) , Just (VInt j)) → Just (VInt (i + j))
        _ → Nothing
interp (EEq left right) =
    case (interp left , interp right) of λ where
        (Just (VInt i) , Just (VInt j)) → Just (VBool (i == j))
        _ → Nothing
interp (ENot e) =
    case interp e of λ where
        (Just (VBool b)) → Just (VBool (not b))
        _ → Nothing
interp (EAnd left right) =
    case (interp left , interp right) of λ where
        (Just (VBool a) , Just (VBool b)) → Just (VBool (a && b))
        _ → Nothing
interp (EOr left right) =
    case (interp left , interp right) of λ where
        (Just (VBool a) , Just (VBool b)) → Just (VBool (a || b))
        _ → Nothing

{-# COMPILE AGDA2HS interp #-}

------------------------------------------------------------
-- SIMPLE TYPE CHECKER                                    --
------------------------------------------------------------

typeOf : Expr → Maybe Type
typeOf (EBool b) = Just TBool
typeOf (EInt i) = Just TInt
typeOf (EAdd left right) =
    case (typeOf left , typeOf right) of λ where
        (Just TInt , Just TInt) → Just TInt
        _ → Nothing
typeOf (EEq left right) =
    case (typeOf left , typeOf right) of λ where
        (Just TInt , Just TInt) → Just TBool
        _ → Nothing
typeOf (ENot e) =
    case typeOf e of λ where
        (Just TBool) → Just TBool
        _ → Nothing
typeOf (EAnd left right) =
    case (typeOf left , typeOf right) of λ where
        (Just TBool , Just TBool) → Just TBool
        _ → Nothing
typeOf (EOr left right) =
    case (typeOf left , typeOf right) of λ where
        (Just TBool , Just TBool) → Just TBool
        _ → Nothing

{-# COMPILE AGDA2HS typeOf #-}

------------------------------------------------------------
-- PROOFS                                                 --
------------------------------------------------------------

bogus : Maybe Val
bogus = interp (ENot (EInt 13))

_ : (bogus == Nothing) ≡ True
_ = refl

three : Maybe Val
three = Just (VInt 3)

three₁ : Maybe Val
three₁ = interp (EInt 3)

three₂ : Maybe Val
three₂ = interp (EAdd (EInt 1) (EAdd (EInt 1) (EInt 1)))

_ : (three == three₁) ≡ True
_ = refl

_ : (three == three₂) ≡ True
_ = refl

_ : (three₁ == three₂) ≡ True
_ = refl

-- sound : ∀ {e} → ((typeOf e) == Nothing) ≡ False → ((interp e) == Nothing) ≡ False
-- sound h = {!   !}


