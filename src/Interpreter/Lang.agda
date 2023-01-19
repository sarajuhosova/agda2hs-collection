module Interpreter.Lang where

open import Haskell.Prelude

import Relation.Binary.PropositionalEquality as PEq
open PEq using (_≡_; refl; cong; sym)
open PEq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

------------------------------------------------------------
-- TYPES                                                  --
------------------------------------------------------------

data Type : Set where
    TBool : Type
    TInt : Type

eqType : Type → Type → Bool
eqType TBool TBool = True
eqType TInt TInt = True
eqType _ _ = False

instance
  iEqType : Eq Type
  iEqType ._==_ = eqType

{-# COMPILE AGDA2HS Type #-}

------------------------------------------------------------
-- EXPRESSIONS                                            --
------------------------------------------------------------

data Expr : Set where
    EBool : Bool → Expr
    EInt  : Int  → Expr
    EAdd  : Expr → Expr → Expr
    EEq   : Expr → Expr → Expr
    ENot  : Expr → Expr
    EAnd  : Expr → Expr → Expr
    EOr   : Expr → Expr → Expr

eqExpr : Expr → Expr → Bool
eqExpr (EBool a) (EBool b) = a == b
eqExpr (EInt i) (EInt j) = i == j
eqExpr (EAdd left₁ right₁) (EAdd left₂ right₂) = eqExpr left₁ left₂ && eqExpr right₁ right₂
eqExpr (EEq left₁ right₁) (EEq left₂ right₂) = eqExpr left₁ left₂ && eqExpr right₁ right₂
eqExpr (ENot a) (ENot b) = eqExpr a b
eqExpr (EAnd left₁ right₁) (EAnd left₂ right₂) = eqExpr left₁ left₂ && eqExpr right₁ right₂
eqExpr (EOr left₁ right₁) (EOr left₂ right₂) = eqExpr left₁ left₂ && eqExpr right₁ right₂
eqExpr _ _ = False

instance
  iEqExpr : Eq Expr
  iEqExpr ._==_ = eqExpr

{-# COMPILE AGDA2HS Expr #-}

------------------------------------------------------------
-- VALUES                                                 --
------------------------------------------------------------

data Val : Set where
    VBool : Bool → Val
    VInt  : Int  → Val

eqVal : Val → Val → Bool
eqVal (VBool a) (VBool b) = a == b
eqVal (VInt i) (VInt j) = i == j
eqVal _ _ = False

instance
  iEqVal : Eq Val
  iEqVal ._==_ = eqVal

{-# COMPILE AGDA2HS Val #-}

≡-bool : ∀ (left right : Bool) → (left == right) ≡ True → left ≡ right
≡-bool False False _ = refl
≡-bool True True _ = refl

postulate ≡-int : ∀ (left right : Int) → (left == right) ≡ True → left ≡ right

≡-val : ∀ (left right : Val) → (left == right) ≡ True → left ≡ right
≡-val (VBool a) (VBool b) h rewrite ≡-bool a b h = refl
≡-val (VInt x) (VInt y) h rewrite ≡-int x y h = refl
