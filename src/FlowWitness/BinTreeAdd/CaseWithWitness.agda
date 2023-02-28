module FlowWitness.BinTreeAdd.CaseWithWitness where

open import Haskell.Prelude

open import Lib.InfInt
open import Lib.Util
open import FlowWitness.BinTree
open import FlowWitness.Witness

import Relation.Binary.PropositionalEquality as PEq
open PEq using (_≡_; refl; cong; sym)
open PEq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

add : ∀ {@0 min max : InfInt} 
      → (i : Int) → BinTree min max 
      → @0 (min < (IInt i)) ≡ True → @0 ((IInt i) < max) ≡ True 
      → BinTree min max
add i Leaf h1 h2 = Branch i (Leaf {{ h1 }}) (Leaf {{ h2 }})
add i (Branch x left right) h1 h2 =
    case witness (i < x) of λ where
        (True < hlt >) → Branch x (add i left h1 hlt) right
        (False <>) → case witness (x < i) of λ where
            (True < hgt >) → Branch x left (add i right hgt h2)
            (False <>) → Branch x left right

{-# COMPILE AGDA2HS add #-}

addAll : ∀ (@0 min max : InfInt)
         → (is : List Int) → BinTree min max 
         → @0 allMatch (λ x → min < (IInt x)) is ≡ True
         → @0 allMatch (λ x → (IInt x) < max) is ≡ True 
         → BinTree min max
addAll _ _ [] tree h1 h2 = tree
addAll min max (i ∷ is) tree h1 h2 =
    addAll min max is 
        (add i tree 
            (allMatchHead i is (λ x → min < (IInt x)) h1)
            (allMatchHead i is (λ x → (IInt x) < max) h2)
        )
        (allMatchTail i is (λ x → min < (IInt x)) h1)
        (allMatchTail i is (λ x → (IInt x) < max) h2)

{-# COMPILE AGDA2HS addAll #-}

flatten : ∀ {@0 min max : InfInt} → BinTree min max → List Int
flatten Leaf = []
flatten (Branch x left right) = flatten left ++ (x ∷ []) ++ flatten right

{-# COMPILE AGDA2HS flatten #-}

-- propAlwaysSorted :: [Int] -> Bool
alwaysSorted : ∀ (is : List Int) 
               → isSorted (flatten (addAll NegInf PosInf is Leaf (allMatchTrue is) (allMatchTrue is))) ≡ True
alwaysSorted [] = refl
alwaysSorted (i ∷ is) =
    -- isSorted (flatten (addAll NegInf PosInf is (Branch i Leaf Leaf) (allMatchTail i is (λ x → True) (allMatchTrue is)) (allMatchTail i is (λ x → True) (allMatchTrue is))))
    begin
        isSorted (flatten (addAll NegInf PosInf (i ∷ is) Leaf (allMatchTrue (i ∷ is)) (allMatchTrue (i ∷ is))))
    ≡⟨⟩
        {!   !}
    ≡⟨ {!   !} ⟩
        True
    ∎ 

-- propNoDuplicates :: [Int] -> Bool
-- hasNoDuplicates : ∀ (is : List Int) 
--                   → noDuplicates (flatten (addAll is Leaf {!   !} {!   !})) ≡ True
-- hasNoDuplicates = {!   !}
