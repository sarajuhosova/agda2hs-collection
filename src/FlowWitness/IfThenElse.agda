{-# OPTIONS --allow-unsolved-metas #-}

module FlowWitness.IfThenElse where

open import Haskell.Prelude

open import FlowWitness.Witness
open import Lib.BoxedProof
open import Lib.InfInt

flow : Int → Int → Int
flow i j = if i == j then {!   !} else {!   !}

-- by Dixit
-- case'_of_ : {A B : Set} → (a : A) → ((a' : A) → {eq : a ≡ a'} → B) → B
-- case' x of f = f x { refl }

if''_then_else_ : {A : Set} → (flg : Bool) → ({flg ≡ True} → A) → ({flg ≡ False} → A) → A
if'' True then t else f = t {refl}
if'' False then t else f = f {refl}

flow'' : Int → Int → Int
flow'' i j = if'' i == j then (λ {h} → {!   !}) else (λ {h} → {!   !})

-- test

test : @0 True ≡ True → Int
test h = 0

{-# COMPILE AGDA2HS test #-}

-- floww : Int → Int → Bool
-- floww i j = if' (i == j) then (λ h → False) else (λ h → True)

-- {-# COMPILE AGDA2HS floww #-}

-- data ValueInRange (@0 low high : InfInt) : Set where
--     Value : (i : Int)
--             → {{ @0 hl : ((low <= (IInt i)) ≡ True) }}
--             → {{ @0 hr : (((IInt i) <= high) ≡ True) }}
--             → ValueInRange low high

data Range : Set where
    MkRange : (low high : Int)
            → {{ @0 h : ((low <= high) ≡ True) }}
            → Range

{-# COMPILE AGDA2HS Range #-}

-- createRange' : Int → Int → Maybe Range
-- createRange' low high = if low <= high then Just (MkRange low high) else Nothing

createRange : Int → Int → Maybe Range
createRange low high = if' low <= high then Just (MkRange low high) else Nothing

{-# COMPILE AGDA2HS createRange #-}
