module Lib.Identity where

open import Haskell.Prelude

import Relation.Binary.PropositionalEquality as PEq
open PEq using (_≡_; refl)

------------------------------------------------------------
-- DEFINTION                                              --
------------------------------------------------------------

record Identity (a : Set) : Set where
    constructor Id_
    field
        runIdentity : a
open Identity public

{-# COMPILE AGDA2HS Identity #-}

instance
    iFunctorIdentity : Functor Identity
    iFunctorIdentity .fmap f record { runIdentity = a } = Id (f a)
    
    iApplicativeIdentity : Applicative Identity
    iApplicativeIdentity .pure = Id_
    iApplicativeIdentity ._<*>_ (Id f) (Id x) = Id (f x)
    
    iMonadIdentity : Monad Identity
    iMonadIdentity ._>>=_ (Id a) f = f a

{-# COMPILE AGDA2HS iFunctorIdentity #-}
{-# COMPILE AGDA2HS iApplicativeIdentity #-}
{-# COMPILE AGDA2HS iMonadIdentity #-}

------------------------------------------------------------
-- MONAD LAWS                                             --
------------------------------------------------------------

leftId : ∀ {a b} (x : a) (f : a → Identity b) → (return x >>= f) ≡ f x
leftId x f = refl
 
rightId : ∀ {a} (k : Identity a) → (k >>= return) ≡ k
rightId id = refl

assoc : ∀ {a b c} (k : Identity a) (f : a → Identity b) (g : b → Identity c)
             → ((k >>= f) >>= g) ≡ (k >>= (λ x → f x >>= g))
assoc id f g = refl
