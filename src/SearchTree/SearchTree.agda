{-# OPTIONS --allow-unsolved-metas #-}

module SearchTree.SearchTree where

open import Haskell.Prelude

import Relation.Binary.PropositionalEquality as PEq
open PEq using (_≡_; refl; cong; sym)
open PEq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

open import Agda.Builtin.Word
open import Agda.Builtin.Word.Properties

-- DATA DEFINITION ----------------------------------------

data SearchTree : Set where
    Nil : SearchTree
    Tree : Int → SearchTree → SearchTree → SearchTree

eqSearchTree : SearchTree → SearchTree → Bool
eqSearchTree Nil Nil = True
eqSearchTree (Tree e1 l1 r1) (Tree e2 l2 r2) = e1 == e2 && eqSearchTree l1 l2 && eqSearchTree r1 r2
eqSearchTree _ _ = False

instance
    iEqSearchTree : Eq SearchTree
    iEqSearchTree ._==_ = eqSearchTree


{-# COMPILE AGDA2HS SearchTree #-}
{-# COMPILE AGDA2HS eqSearchTree #-}
{-# COMPILE AGDA2HS iEqSearchTree #-}

-- METHODS ------------------------------------------------

add : Int → SearchTree → SearchTree
add i Nil = Tree i Nil Nil
add i (Tree e left right) = if i < e then Tree e (add i left) right else Tree e left (add i right)

{-# COMPILE AGDA2HS add #-}

addAll : List Int → SearchTree → SearchTree
addAll xs tree = foldl ((λ t x → add x t)) tree xs

{-# COMPILE AGDA2HS addAll #-}

flatten : SearchTree → List Int
flatten Nil = []
flatten (Tree e left right) = flatten left ++ (e ∷ []) ++ flatten right

{-# COMPILE AGDA2HS flatten #-}

sort : List Int → List Int
sort xs = {!   !}

-- PROOFS -------------------------------------------------

≡-eqNat : ∀ (left right : Nat) → (left == right) ≡ True → left ≡ right
≡-eqNat zero zero h = refl
≡-eqNat (suc left) (suc right) h
    rewrite ≡-eqNat left right h
    = refl

≡-Nat-≡-eqInt : ∀ (left right : Word64) 
                → (primWord64ToNat left == primWord64ToNat right) ≡ True 
                → (int64 left) ≡ (int64 right)
≡-Nat-≡-eqInt i j h = {!  !}

≡-eqInt : ∀ (left right : Int) → (left == right) ≡ True → left ≡ right
≡-eqInt (int64 i) (int64 j) h = ≡-Nat-≡-eqInt i j h

&&-left-assoc : ∀ (a b c : Bool) → (a && b && c) ≡ True → ((a && b) && c) ≡ True
&&-left-assoc True True True h = refl

&&-leftTrue : ∀ (a b : Bool) → (a && b) ≡ True → a ≡ True
&&-leftTrue True True h = refl

&&-rightTrue : ∀ (a b : Bool) → (a && b) ≡ True → b ≡ True
&&-rightTrue True True h = refl

-- eq : ∀ (left right : SearchTree) → (left == right) ≡ True → left ≡ right
-- eq Nil Nil h = refl
-- eq Nil (Tree x right right₁) ()
-- eq (Tree x₁ left₁ right₁) (Tree x₂ left₂ right₂) h
--     rewrite ≡-eqInt x₁ x₂ (&&-leftTrue
--                 (eqInt x₁ x₂)
--                 (eqSearchTree left₁ left₂)
--                 (&&-leftTrue
--                     (eqInt x₁ x₂ && eqSearchTree left₁ left₂)
--                     (eqSearchTree right₁ right₂)
--                     (&&-left-assoc
--                         (eqInt x₁ x₂)
--                         (eqSearchTree left₁ left₂)
--                         (eqSearchTree right₁ right₂)
--                         h
--                     )
--                 )
--             )
--             | eq left₁ left₂ (&&-rightTrue
--                 (eqInt x₁ x₂)
--                 (eqSearchTree left₁ left₂)
--                 (&&-leftTrue
--                     (eqInt x₁ x₂ && eqSearchTree left₁ left₂)
--                     (eqSearchTree right₁ right₂)
--                     (&&-left-assoc
--                         (eqInt x₁ x₂)
--                         (eqSearchTree left₁ left₂)
--                         (eqSearchTree right₁ right₂)
--                         h
--                     )
--                 )
--             )
--             | eq right₁ right₂ (&&-rightTrue 
--                 (eqInt x₁ x₂ && eqSearchTree left₁ left₂)
--                 (eqSearchTree right₁ right₂)
--                 (&&-left-assoc
--                     (eqInt x₁ x₂)
--                     (eqSearchTree left₁ left₂)
--                     (eqSearchTree right₁ right₂)
--                     h
--                 )
--             )
--     = refl

ifFlip : ⦃ Eq a ⦄ 
         → (b : Bool) → (i₁ t₁ i₂ t₂ : a)
         → i₁ ≡ t₂ → t₁ ≡ i₂
         → (if b then i₁ else t₁) ≡ (if (not b) then i₂ else t₂)
ifFlip False _ _ _ _ _ h rewrite h = refl
ifFlip True _ _ _ _ h _ rewrite h = refl

ifApply : (b : Bool) → (i t : a) → (f : a → c) → (f (if b then i else t)) ≡ (if b then (f i) else (f t))
ifApply False i t f = refl
ifApply True i t f = refl

addSingleElement : (e : Int) → flatten (add e Nil) ≡ e ∷ []
addSingleElement e = refl

flattenIndepentOfAddOrder : (i j : Int) → flatten (add i (add j Nil)) ≡ flatten (add j (add i Nil))
flattenIndepentOfAddOrder i j =
    begin
        flatten (add i (add j Nil))
    ≡⟨⟩
        flatten (add i (Tree j Nil Nil))
    ≡⟨⟩
        flatten (if ltInt i j then Tree j (Tree i Nil Nil) Nil else Tree j Nil (Tree i Nil Nil))
    ≡⟨ ifApply (ltInt i j) (Tree j (Tree i Nil Nil) Nil) (Tree j Nil (Tree i Nil Nil)) flatten ⟩
        (if ltInt i j then (flatten (Tree j (Tree i Nil Nil) Nil)) else (flatten (Tree j Nil (Tree i Nil Nil))))
    ≡⟨⟩
        (if ltInt i j then i ∷ j ∷ [] else j ∷ i ∷ [])
    ≡⟨ {!   !} ⟩
        (if not (ltInt j i) then i ∷ j ∷ [] else j ∷ i ∷ [])
    ≡⟨⟩
        (if not (ltInt j i) then (flatten (Tree i Nil (Tree j Nil Nil))) else (flatten (Tree i (Tree j Nil Nil) Nil)))
    ≡⟨ sym (ifApply (not (ltInt j i)) (Tree i Nil (Tree j Nil Nil)) (Tree i (Tree j Nil Nil) Nil) flatten) ⟩
        flatten (if not (ltInt j i) then Tree i Nil (Tree j Nil Nil) else Tree i (Tree j Nil Nil) Nil)
    ≡⟨ sym (cong flatten (ifFlip (ltInt j i) (Tree i (Tree j Nil Nil) Nil) (Tree i Nil (Tree j Nil Nil)) (Tree i Nil (Tree j Nil Nil)) (Tree i (Tree j Nil Nil) Nil) refl refl)) ⟩
        flatten (if ltInt j i then Tree i (Tree j Nil Nil) Nil else Tree i Nil (Tree j Nil Nil))
    ≡⟨⟩
        flatten (add j (Tree i Nil Nil))
    ≡⟨⟩
        flatten (add j (add i Nil))
    ∎

flattenIndepentOfAddOrder2 : (i j : Int) → flatten (add i (add j Nil)) ≡ flatten (add j (add i Nil))
flattenIndepentOfAddOrder2 i j =
    case i < j of λ where
        True → {!   !}
        False → {!   !}

addAllSorts : (xs : List Int) → flatten (addAll xs Nil) ≡ sort xs
addAllSorts xs = {!   !}
