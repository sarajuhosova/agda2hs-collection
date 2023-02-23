{-# OPTIONS --allow-unsolved-metas #-}

module FlowWitness.BinTree where

open import Haskell.Prelude
open import Lib.Util

import Relation.Binary.PropositionalEquality as PEq
open PEq using (_≡_; refl; cong; sym)
open PEq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

data InfInt : Set where
    NegInf : InfInt
    IInt : Int → InfInt
    PosInf : InfInt

{-# COMPILE AGDA2HS InfInt #-}

eqInfInt : InfInt → InfInt → Bool
eqInfInt NegInf NegInf = True
eqInfInt (IInt i) (IInt j) = i == j
eqInfInt PosInf PosInf = True
eqInfInt _ _ = False

ltInfInt : InfInt → InfInt → Bool
ltInfInt NegInf _ = True
ltInfInt (IInt i) (IInt j) = i < j
ltInfInt _ PosInf = True
ltInfInt _ _ = False

{-# COMPILE AGDA2HS eqInfInt #-}
{-# COMPILE AGDA2HS ltInfInt #-}

instance
    iEqInfInt : Eq InfInt
    iEqInfInt ._==_ = eqInfInt

    iOrdInfInt : Ord InfInt
    iOrdInfInt .compare x y = if (ltInfInt x y) then LT else if x == y then EQ else GT
    iOrdInfInt ._<_  x y = (ltInfInt x y)
    iOrdInfInt ._>_  x y = (ltInfInt y x)
    iOrdInfInt ._<=_ x y = (ltInfInt x y) || x == y
    iOrdInfInt ._>=_ x y = (ltInfInt y x) || x == y
    iOrdInfInt .max  x y = if (ltInfInt x y) then y else x
    iOrdInfInt .min  x y = if (ltInfInt y x) then y else x

{-# COMPILE AGDA2HS iEqInfInt #-}
{-# COMPILE AGDA2HS iOrdInfInt #-}

data BinTree (@0 min max : InfInt) : Set where
    Leaf : {{ @0 h : ((min < max) ≡ True) }} → BinTree min max
    Branch : (i : Int) → BinTree min (IInt i) → BinTree (IInt i) max → BinTree min max

{-# COMPILE AGDA2HS BinTree #-}

emptyTree : BinTree NegInf PosInf
emptyTree = Leaf

singleElemTree : BinTree NegInf PosInf
singleElemTree = Branch 3 Leaf Leaf

rightTree : BinTree NegInf PosInf
rightTree = Branch 3 Leaf (Branch 4 Leaf Leaf)

leftTree : BinTree NegInf PosInf
leftTree = Branch 3 (Branch 2 Leaf Leaf) Leaf

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

-- isSorted :: [Int] -> Bool
isSorted : List Int → Bool
isSorted [] = True
isSorted (x ∷ []) = True
isSorted (x ∷ y ∷ xs) = x <= y && isSorted (y ∷ xs)

-- propAlwaysSorted :: [Int] -> Bool
-- alwaysSorted : ∀ (is : List Int) 
--                → isSorted (flatten (addAll is Leaf {!   !} {!   !})) ≡ True
-- alwaysSorted = {!   !}

-- noDuplicates :: [Int] -> Bool
noDuplicates : List Int → Bool
noDuplicates [] = True
noDuplicates (x ∷ []) = True
noDuplicates (x ∷ xs) = allMatch (λ i → i /= x) xs && noDuplicates xs

-- propNoDuplicates :: [Int] -> Bool
-- hasNoDuplicates : ∀ (is : List Int) 
--                   → noDuplicates (flatten (addAll is Leaf {!   !} {!   !})) ≡ True
-- hasNoDuplicates = {!   !}
