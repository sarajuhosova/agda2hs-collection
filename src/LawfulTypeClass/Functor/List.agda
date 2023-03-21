-- {-# OPTIONS --allow-unsolved-metas #-}

module LawfulTypeClass.Functor.List where

open import Haskell.Prim
open import Haskell.Prim.List

open import Haskell.Prim.Functor

open import Haskell.Law.Functor.Def

import Relation.Binary.PropositionalEquality as PEq
open PEq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

instance
  iLawfulFunctorList : IsLawfulFunctor List
  iLawfulFunctorList .identity [] = refl
  iLawfulFunctorList .identity (x ∷ xs) =
    begin
      (Functor.fmap iFunctorList id (x ∷ xs))
    ≡⟨⟩
      {!   !}
    ≡⟨ {!   !} ⟩ 
      (id (x ∷ xs))
    ∎

  iLawfulFunctorList .composition [] = refl
  iLawfulFunctorList .composition (x ∷ xs) = {!   !}
  