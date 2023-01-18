module Lib.Identity where

open import Haskell.Prelude

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
  iApplicativeIdentity .pure a = Id a
  iApplicativeIdentity ._<*>_ (Id f) (Id x) = Id (f x)

{-# COMPILE AGDA2HS iFunctorIdentity #-}
{-# COMPILE AGDA2HS iApplicativeIdentity #-}

