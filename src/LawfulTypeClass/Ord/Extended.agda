module LawfulTypeClass.Ord.Extended where

open import Haskell.Prelude

open import LawfulTypeClass.Eq.Extended

import Relation.Binary.PropositionalEquality as PEq
open PEq using (_≡_; refl; sym; cong)

record LawfulOrd (a : Set) {{iOrd : Ord a}} : Set₁ where
    field
        overlap ⦃ super ⦄ : LawfulEq₂ a

        -- Comparability: x <= y || y <= x = True
        comparability : ∀ (x y : a) → (x <= y || y <= x) ≡ True

        -- Transitivity: if x <= y && y <= z = True, then x <= z = True
        transitivity :  ∀ ( x y z : a ) → {{ (x <= y) ≡ True }} → {{ (y <= z) ≡ True }} → (x <= z) ≡ True

        -- Reflexivity: x <= x = True
        reflexivity : ∀ (x : a) → (x <= x) ≡ True

        -- Antisymmetry: if x <= y && y <= x = True, then x == y = True
        antisymmetry : ∀ (x y : a) → {{ (x <= y) ≡ True }} → {{ (y <= x) ≡ True }} → x ≡ y
        
open LawfulOrd ⦃ ... ⦄ public
