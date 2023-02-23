{-# OPTIONS --allow-unsolved-metas #-}

module FlowWitness.Case where

open import Haskell.Prelude

open import Lib.BoxedProof

record Witness (A : Set) (a : A) : Set where
  constructor _[_]
  field
    el : A
    @0 pf : _≡_ a el
open Witness public

{-# COMPILE AGDA2HS Witness unboxed #-}

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
case''' x of f = f (x [ refl ])

flow''' : Int → Int → Int
flow''' i j =
  case''' ( i == j ) of λ where
    (True [ h ]) → {!   !}
    (False [ h ]) → {!   !}
  