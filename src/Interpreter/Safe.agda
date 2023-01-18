module Interpreter.Safe where

open import Haskell.Prelude
open import Interpreter.Lang

open import Data.Product using (∃;∃-syntax) renaming (_,_ to ⟨_,_⟩)

------------------------------------------------------------
-- TYPED EXPRESSIONS                                      --
------------------------------------------------------------

data TExpr : @0 Type → Set where
    TEBool : Bool → TExpr TBool
    TEInt  : Int  → TExpr TInt
    TEAdd  : TExpr TInt → TExpr TInt → TExpr TInt
    TEEq   : TExpr TInt → TExpr TInt → TExpr TBool
    TENot  : TExpr TBool → TExpr TBool
    TEAnd  : TExpr TBool → TExpr TBool → TExpr TBool
    TEOr   : TExpr TBool → TExpr TBool → TExpr TBool

eqTExpr : ∀ {@0 t} → TExpr t → TExpr t → Bool
eqTExpr (TEBool a) (TEBool b) = a == b
eqTExpr (TEInt i) (TEInt j) = i == j
eqTExpr (TEAdd left₁ right₁) (TEAdd left₂ right₂) = eqTExpr left₁ left₂ && eqTExpr right₁ right₂
eqTExpr (TEEq left₁ right₁) (TEEq left₂ right₂) = eqTExpr left₁ left₂ && eqTExpr right₁ right₂
eqTExpr (TENot a) (TENot b) = eqTExpr a b
eqTExpr (TEAnd left₁ right₁) (TEAnd left₂ right₂) = eqTExpr left₁ left₂ && eqTExpr right₁ right₂
eqTExpr (TEOr left₁ right₁) (TEOr left₂ right₂) = eqTExpr left₁ left₂ && eqTExpr right₁ right₂
eqTExpr _ _ = False

instance
  iEqTExpr : ∀ {@0 t} → Eq (TExpr t)
  iEqTExpr ._==_ = eqTExpr

{-# COMPILE AGDA2HS TExpr #-}

------------------------------------------------------------
-- VALUES                                                 --
------------------------------------------------------------

data TVal : @0 Type → Set where
    VBool : Bool → TVal TBool
    VInt  : Int  → TVal TInt

eqTVal : ∀ {@0 t} → TVal t → TVal t → Bool
eqTVal (VBool a) (VBool b) = a == b
eqTVal (VInt i) (VInt j) = i == j

instance
  iEqTVal : ∀ {@0 t} → Eq (TVal t)
  iEqTVal ._==_ = eqTVal

{-# COMPILE AGDA2HS TVal #-}

simplify : ∀ {@0 t} → TVal t → Val
simplify (VBool b) = VBool b
simplify (VInt i) = VInt i

{-# COMPILE AGDA2HS simplify #-}

-- val : Type → Set
-- val TBool = Bool
-- val TInt = Int

------------------------------------------------------------
-- TYPING JUDGEMENT                                       --
------------------------------------------------------------

data HasType : Expr → Type → Set where
    TBool : ∀ {b} → HasType (EBool b) TBool
    TInt  : ∀ {i} → HasType (EInt  i) TInt
    TAdd  : ∀ {left right}
        → HasType left TInt → HasType right TInt
        → HasType (EAdd left right) TInt
    TEq   : ∀ {left right}
        → HasType left TInt → HasType right TInt
        → HasType (EEq left right) TBool
    TNot  : ∀ {e}
        → HasType e TBool
        → HasType (ENot e) TBool
    TAnd  : ∀ {left right}
        → HasType left TBool → HasType right TBool
        → HasType (EAnd left right) TBool
    TOr   : ∀ {left right}
        → HasType left TBool → HasType right TBool
        → HasType (EOr left right) TBool
        
------------------------------------------------------------
-- TYPE CHECK                                             --
------------------------------------------------------------

-- record Σ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
--   constructor _,_
--   field
--     fst : A
--     snd : B fst

-- record TypeProof {e : Expr} {t : Type} (T : Set t) (P : T → HasType e T) : Set where
--     field
--         type : T
--         proof : P type

typeProof : (e : Expr) → Maybe (∃[ t ](HasType e t))
typeProof (EBool _) = Just ⟨ TBool , TBool ⟩
typeProof (EInt _) = Just ⟨ TInt , TInt ⟩
typeProof (EAdd left right) =
    case (typeProof left , typeProof right) of λ where
        (Just ⟨ TInt , hₗ ⟩ , Just ⟨ TInt , hᵣ ⟩)
            → Just ⟨ TInt , TAdd hₗ hᵣ ⟩
        _   → Nothing
typeProof (EEq left right) = 
    case (typeProof left , typeProof right) of λ where
        (Just ⟨ TInt , hₗ ⟩ , Just ⟨ TInt , hᵣ ⟩)
            → Just ⟨ TBool , TEq hₗ hᵣ ⟩
        _   → Nothing
typeProof (ENot e) =
    case (typeProof e) of λ where
        (Just ⟨ TBool , h ⟩)
            → Just ⟨ TBool , TNot h ⟩
        _   → Nothing
typeProof (EAnd left right) = 
    case (typeProof left , typeProof right) of λ where
        (Just ⟨ TBool , hₗ ⟩ , Just ⟨ TBool , hᵣ ⟩)
            → Just ⟨ TBool , TAnd hₗ hᵣ ⟩
        _   → Nothing
typeProof (EOr left right) =
    case (typeProof left , typeProof right) of λ where
        (Just ⟨ TBool , hₗ ⟩ , Just ⟨ TBool , hᵣ ⟩)
            → Just ⟨ TBool , TOr hₗ hᵣ ⟩
        _   → Nothing

{-# COMPILE AGDA2HS typeProof #-}
        
------------------------------------------------------------
-- TYPED INTERPRETER                                      --
------------------------------------------------------------

convert : ∀ {@0 t} → (e : Expr) → @0 HasType e t → TExpr t
convert (EBool b) TBool = TEBool b
convert (EInt i) TInt = TEInt i
convert (EAdd left right) (TAdd hl hr) = TEAdd (convert left hl) (convert right hr)
convert (EEq left right) (TEq hl hr) = TEEq (convert left hl) (convert right hr)
convert (ENot e) (TNot h) = TENot (convert e h)
convert (EAnd left right) (TAnd hl hr) = TEAnd (convert left hl) (convert right hr)
convert (EOr left right) (TOr hl hr) = TEOr (convert left hl) (convert right hr)

typedInterp : ∀ {@0 t} → TExpr t → TVal t
typedInterp (TEBool b) = VBool b
typedInterp (TEInt i) = VInt i
typedInterp (TEAdd left right) =
    case (typedInterp left , typedInterp right) of λ where
        (VInt i , VInt j) → VInt (i + j)
typedInterp (TEEq left right) =
    case (typedInterp left , typedInterp right) of λ where
        (VInt i , VInt j) → VBool (i == j)
typedInterp (TENot e) =
    case (typedInterp e) of λ where
        (VBool b) → VBool (not b)
typedInterp (TEAnd left right) = 
    case (typedInterp left , typedInterp right) of λ where
        (VBool a , VBool b) → VBool (a && b)
typedInterp (TEOr left right) = 
    case (typedInterp left , typedInterp right) of λ where
        (VBool a , VBool b) → VBool (a || b)

{-# COMPILE AGDA2HS convert #-}
{-# COMPILE AGDA2HS typedInterp #-}
        
------------------------------------------------------------
-- SAFE INTERP                                            --
------------------------------------------------------------

combine' : Expr → Maybe (∃[ t ](TVal t))
combine' e with typeProof e
... | Just ⟨ t , h ⟩ = Just ⟨ t , typedInterp (convert e h) ⟩
... | _              = Nothing

safeInterp' : Expr → Maybe Val
safeInterp' e with combine' e
... | Just ⟨ _ , v ⟩ = Just (simplify v)
... | _ = Nothing

safeInterp : Expr → Maybe Val
safeInterp e =
    case (typeProof e) of λ where
        (Just ⟨ t , h ⟩) 
            → Just (simplify (typedInterp (convert e h)))
        _   → Nothing

{-# COMPILE AGDA2HS safeInterp #-}

------------------------------------------------------------
-- PROOFS                                                 --
------------------------------------------------------------

_ : HasType (EAdd (EInt 3) (EInt 5)) TInt
_ = TAdd TInt TInt
