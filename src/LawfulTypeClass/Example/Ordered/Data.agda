module LawfulTypeClass.Example.Ordered.Data where

open import Haskell.Prelude

data Ordered (a : Set) : Set where
    Gt : {{ @0 iOrd : Ord a }} → (a' : a) → (a'' : a) → {{ @0 pf : (a' > a'') ≡ True }} → Ordered a
    Lt : {{ @0 iOrd : Ord a }} → (a' : a) → (a'' : a) → {{ @0 pf : (a' < a'') ≡ True }} → Ordered a
    E :  {{ @0 iOrd : Ord a }} → (a' : a) → (a'' : a) → {{ @0 pf : a' ≡ a'' }}         → Ordered a

{-# COMPILE AGDA2HS Ordered #-}
