module FlowWitness.BinTreeAdd.Original where

open import Haskell.Prelude
open import Lib.InfInt
open import Lib.Util
open import FlowWitness.BinTree

-- add :: Int -> BinTree -> BinTree
add : ∀ {@0 min max : InfInt} 
      → (i : Int) → BinTree min max 
      → @0 (min < (IInt i)) ≡ True → @0 ((IInt i) < max) ≡ True 
      → BinTree min max
add i Leaf h1 h2 = Branch i (Leaf {{ h1 }}) (Leaf {{ h2 }})
add i (Branch x left right) h1 h2 =
    case i < x of λ where
        True → Branch x (add i left h1 {!   !}) right
        False → case x < i of λ where
            True → Branch x left (add i right {!   !} h2)
            False → Branch x left right

-- {-# COMPILE AGDA2HS add #-}

-- addAll :: [Int] -> BinTree -> BinTree
addAll : ∀ {@0 min max : InfInt} 
         → (is : List Int) → BinTree min max 
         → @0 allMatch (λ x → min < (IInt x)) is ≡ True
         → @0 allMatch (λ x → (IInt x) < max) is ≡ True 
         → BinTree min max
addAll [] tree h1 h2 = tree
addAll (i ∷ is) tree h1 h2 =
    addAll is 
        (add i tree 
            (allMatchHead i is {!   !} h1)
            (allMatchHead i is {!   !} h2)
        )
        (allMatchTail i is {!   !} h1)
        (allMatchTail i is {!   !} h2)

-- {-# COMPILE AGDA2HS addAll #-}

-- flatten :: BinTree -> [Int]
flatten : ∀ {@0 min max : InfInt} → BinTree min max → List Int
flatten Leaf = []
flatten (Branch x left right) = flatten left ++ (x ∷ []) ++ flatten right

{-# COMPILE AGDA2HS flatten #-}

-- propAlwaysSorted :: [Int] -> Bool
-- alwaysSorted : ∀ (is : List Int) 
--                → isSorted (flatten (addAll is Leaf {!   !} {!   !})) ≡ True
-- alwaysSorted = {!   !}

-- propNoDuplicates :: [Int] -> Bool
-- hasNoDuplicates : ∀ (is : List Int) 
--                   → noDuplicates (flatten (addAll is Leaf {!   !} {!   !})) ≡ True
-- hasNoDuplicates = {!   !}
