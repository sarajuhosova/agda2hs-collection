module Examples.Challenges where

open import Haskell.Prelude

import Relation.Binary.PropositionalEquality as PEq
open PEq using (_≡_; refl)

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

-- Incomplete Standard Library --------------------------------

&&-leftAssoc : ∀ (a b c : Bool) → (a && b && c) ≡ True → ((a && b) && c) ≡ True
&&-leftAssoc True True True h = refl

&&-leftTrue : ∀ (a b : Bool) → (a && b) ≡ True → a ≡ True
&&-leftTrue True True h = refl
