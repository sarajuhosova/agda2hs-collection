module DeBruijn.Lang where

open import Haskell.Prelude

infixr 7 Func
infixl 5 Ctx

data Type : Set where
    Unit : Type
    Func  : Type → Type → Type

data Context : Set where
    Empty : Context
    Ctx   : Type → Context → Context

infix 4 In
infix 4 Judge

data In : Type → Context → Set where
    Zero : ∀ {c a} → In a (Ctx a c)
    Suc  : ∀ {c a b} → In a c → In a (Ctx b c)

data Judge : Context → Type → Set where
    Var : ∀ {c a} → In a c → Judge c a
    Lam : ∀ {c a b} → Judge (Ctx a c) b → Judge c (Func a b)
    App : ∀ {c a b} → Judge c (Func a b) → Judge c a → Judge c b
    Uni : ∀ {c} → Judge c Unit

