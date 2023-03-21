module LawfulTypeClass.Eq.Fixed where

open import Haskell.Prelude using ( Bool; True; not )

import Relation.Binary.PropositionalEquality as PEq
open PEq using (_≡_; refl)

record Eq (a : Set) : Set where
    infix 4 _==_ _/=_
    field
        _==_ : a → a → Bool

        equality  : ∀ (x y : a) → (x == y) ≡ True → x ≡ y
        equality' : ∀ (x y : a) → x ≡ y → (x == y) ≡ True
    
    _/=_ : a → a → Bool
    x /= y = not (x == y)
        
open Eq ⦃ ... ⦄ public
        