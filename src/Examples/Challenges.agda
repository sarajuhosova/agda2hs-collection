{-# OPTIONS --allow-unsolved-metas #-}

module Examples.Challenges where

open import Haskell.Prelude

import Relation.Binary.PropositionalEquality as PEq
open PEq using (_≡_; refl; cong; sym)
open PEq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

-- Incomplete Standard Library --------------------------------

&&-leftAssoc : ∀ (a b c : Bool) → (a && b && c) ≡ True → ((a && b) && c) ≡ True
&&-leftAssoc True True True h = refl

&&-leftAssoc' : ∀ (a b c : Bool) → (a && b && c) ≡ ((a && b) && c)
&&-leftAssoc' False b c = refl
&&-leftAssoc' True b c = refl

&&-leftTrue : ∀ (a b : Bool) → (a && b) ≡ True → a ≡ True
&&-leftTrue True True h = refl

-- Guards -----------------------------------------------------

passed : Double → Either String Bool
passed grade =
    if grade >= 5.75 && grade <= 10 then
        Right True
    else
        if grade >= 1 && grade < 5.75 then
            Right False
        else
            Left "Not a valid grade!"

{-# COMPILE AGDA2HS passed #-}

-- Type Class Deriving ----------------------------------------

data Tree : Set where
    Leaf : Tree
    Branch : Int → Tree → Tree → Tree

eqTree : Tree → Tree → Bool
eqTree Leaf Leaf = True
eqTree (Branch x ll lr) (Branch y rl rr) 
    = x == y && eqTree ll rl && eqTree lr rr
eqTree _ _ = False

instance
  iEqTree : Eq Tree
  iEqTree ._==_ = eqTree

{-# COMPILE AGDA2HS Tree #-}
{-# COMPILE AGDA2HS eqTree #-}
{-# COMPILE AGDA2HS iEqTree #-}

-- Newtype ----------------------------------------------------

record Identity (a : Set) : Set where
    constructor Identityₙ
    field
        runIdentity : a
open Identity public

-- Witnesses in Flow Control ----------------------------------

flow : Int → Int → Int
flow i j = case (i == j) of λ where
    True → {!   !}
    False → {!   !}

-- Boolean vs Propositional Equality --------------------------

postulate ≡-Int : ∀ {i j : Int} → (i == j) ≡ True → i ≡ j
postulate ≡-Int' : ∀ {i j : Int} → i ≡ j → (i == j) ≡ True

≡-same : ∀ {i j : Int} → i ≡ j → i ∷ [] ≡ j ∷ []
≡-same h = cong (λ x → x ∷ []) h

≡-same' : ∀ {i j : Int} → (i == j) ≡ True → i ∷ [] ≡ j ∷ []
≡-same' h = ≡-same (≡-Int h)

&&-true : ∀ (a) → a ≡ (a && True)
&&-true False = refl
&&-true True = refl

-- ≡-refl : ⦃ Eq a ⦄ → ∀ (x : a) → (x == x) ≡ True 
-- ≡-refl x = {!   !}

≡-refl-int : ∀ (x : Int) → (x == x) ≡ True
≡-refl-int x = {!   !}

≡-refl-list : ∀ (xs : List Int) → (xs == xs) ≡ True
≡-refl-list [] = refl
≡-refl-list (x ∷ xs)
    rewrite ≡-refl-int x 
          | sym (&&-true (x == x))
          | ≡-refl-list xs
    = refl

same-[] : ∀ (i j : Int) → (i == j) ≡ (i ∷ [] == j ∷ [])
same-[] i j = &&-true (i == j)

same : ∀ (i j : Int) (xs : List Int) → (i == j) ≡ (i ∷ xs == j ∷ xs)
same i j xs =
    begin
        i == j
    ≡⟨ &&-true (i == j) ⟩
        i == j && True
    ≡⟨ cong (λ x → i == j && x) (sym (≡-refl-list xs)) ⟩
        i == j && xs == xs
    ≡⟨⟩
        (i ∷ xs) == (j ∷ xs)
    ∎

≡-sub : ∀ (i j : Int) 
            → i ≡ j
            → i ∷ j ∷ [] ≡ j ∷ j ∷ []
≡-sub i j h = cong (λ x → x ∷ j ∷ []) h

==-sub : ∀ (i j : Int) 
            → (i == j) ≡ True 
            → i ∷ j ∷ [] ≡ j ∷ i ∷ []
==-sub i j h =
    begin
        i ∷ j ∷ []
    ≡⟨ cong (λ x → i ∷ x ∷ []) (sym (≡-Int h)) ⟩
        i ∷ i ∷ []
    ≡⟨ cong (λ x → x ∷ i ∷ []) (≡-Int h) ⟩
        j ∷ i ∷ []
    ∎
 