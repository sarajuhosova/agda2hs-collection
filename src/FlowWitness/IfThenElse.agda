{-# OPTIONS --allow-unsolved-metas #-}

module FlowWitness.IfThenElse where

open import Haskell.Prelude

open import FlowWitness.Witness
open import Lib.BoxedProof

flow : Int → Int → Int
flow i j = if i == j then {!   !} else {!   !}

-- by Dixit
-- case'_of_ : {A B : Set} → (a : A) → ((a' : A) → {eq : a ≡ a'} → B) → B
-- case' x of f = f x { refl }

if'_then_else_ : {A : Set} → (flg : Bool) → ({flg ≡ True} → A) → ({flg ≡ False} → A) → A
if' True then t else f = t {refl}
if' False then t else f = f {refl}

flow' : Int → Int → Int
flow' i j = if' i == j then {!   !} else {!   !}

-- with box
-- case''_of_ : {A B : Set} → (a : A) → (∃ A (_≡_ a) → B) → B
-- case'' x of f = f (x [ refl ])

if''_then_else_ : {A : Set} → (flg : Bool) → ({flg ≡ True} → A) → ({flg ≡ False} → A) → A
if'' c then t else f = {!   !}

flow'' : Int → Int → Int
flow'' i j = if'' i == j then {!   !} else {!   !}

-- with witness
-- case'''_of_ : {A B : Set} → (a : A) → (Witness A a → B) → B
-- case''' x of f = f (x [ refl ])

if'''_then_else_ : {A : Set} → (flg : Bool) → ({flg ≡ True} → A) → ({flg ≡ False} → A) → A
if''' c then t else f = {!   !}

flow''' : Int → Int → Int
flow''' i j = if'' i == j then {!   !} else {!   !}

