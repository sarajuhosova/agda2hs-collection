{-# OPTIONS --allow-unsolved-metas #-}

module FlowWitness.Case where

open import Haskell.Prelude

open import FlowWitness.Witness
open import FlowWitness.BinTree
open import Lib.InfInt
open import Lib.BoxedProof

flow : Int → Int → Int
flow i j =
  case ( i == j ) of λ where
    True → {!   !}
    False → {!   !}

-- by Dixit
case'_of_ : {A B : Set} → (a : A) → ((a' : A) → {eq : a ≡ a'} → B) → B
case' x of f = f x { refl }

flow' : Int → Int → Int
flow' i j =
  case' ( i == j ) of λ where
    True → {!   !}
    False → {!   !}

-- with box
case''_of_ : {A B : Set} → (a : A) → (∃ A (_≡_ a) → B) → B
case'' x of f = f (x [ refl ])

flow'' : Int → Int → Int
flow'' i j =
  case'' ( i == j ) of λ where
    (True [ h ]) → {!   !}
    (False [ h ]) → {!   !}

-- with witness
case'''_of_ : {A B : Set} → (a : A) → (Witness A a → B) → B
case''' x of f = -- f (x [ refl ])
  case (x <>) of f

-- {-# COMPILE AGDA2HS case'''_of_ transparent #-}

floww : Int → Int → Bool
floww i j =
  case''' ( i == j ) of λ where
    (True <>) → False
    (False <>) → True

-- {-# COMPILE AGDA2HS floww #-}

binTreeFlow : BinTree NegInf PosInf → Int
binTreeFlow t =
  case''' t of λ where
    (Leaf <>) → {!   !}
    ((Branch x left right) <>) → {!   !}

-- with witness WITHOUT NEW CASE

flowWithout : Int → Int → Int
flowWithout i j =
  case (i == j) of λ where
    True → 0
    False → 1

-- {-# COMPILE AGDA2HS flowWithout #-}

flowWithWitness : Int → Int → Bool
flowWithWitness i j =
  case (witness (i == j)) of λ where
    (True <>) → False
    (False <>) → True

{-# COMPILE AGDA2HS flowWithWitness #-}

-- flowWithWitnessInt : Int → Int → Int
-- flowWithWitnessInt i j =
--   case (witness (i == j)) of λ where
--     (True <>) → 0
--     (False <>) → 1

-- {-# COMPILE AGDA2HS flowWithWitnessInt #-}

binTreeWithWitness : BinTree NegInf PosInf → Bool
binTreeWithWitness t =
  case (witness t) of λ where
    (Leaf <>) → False
    ((Branch x left right) <>) → True

{-# COMPILE AGDA2HS binTreeWithWitness #-}
  