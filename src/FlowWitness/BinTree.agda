{-# OPTIONS --allow-unsolved-metas #-}

module FlowWitness.BinTree where

open import Haskell.Prelude
open import Lib.InfInt
open import Lib.Util

import Relation.Binary.PropositionalEquality as PEq
open PEq using (_≡_; refl; cong; sym)
open PEq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

--------------------------------------------------------------------------------------
--                                                                                  --

data BinTree (@0 min max : InfInt) : Set where
    Leaf : {{ @0 h : ((min < max) ≡ True) }} → BinTree min max
    Branch : (i : Int) → BinTree min (IInt i) → BinTree (IInt i) max → BinTree min max

{-# COMPILE AGDA2HS BinTree #-}

--                                                                                  --
--------------------------------------------------------------------------------------

emptyTree : BinTree NegInf PosInf
emptyTree = Leaf

singleElemTree : BinTree NegInf PosInf
singleElemTree = Branch 3 Leaf Leaf

rightTree : BinTree NegInf PosInf
rightTree = Branch 3 Leaf (Branch 4 Leaf Leaf)

leftTree : BinTree NegInf PosInf
leftTree = Branch 3 (Branch 2 Leaf Leaf) Leaf
