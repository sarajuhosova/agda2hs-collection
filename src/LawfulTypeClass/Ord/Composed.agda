module LawfulTypeClass.Ord.Composed where

open import Haskell.Prelude

import Relation.Binary.PropositionalEquality as PEq
open PEq using (_≡_; sym; cong)

open import LawfulTypeClass.Eq.Composed

record LawfulOrd (e : Set) : Set₁ where
    field
        overlap @0 {{ iLawfulEqE }} : LawfulEq e
        overlap {{ iOrdE }} : Ord e

        -- Comparability: x <= y || y <= x = True
        @0 ordComparability : ∀ (x y : e) → (x <= y || y <= x) ≡ True

        -- Transitivity: if x <= y && y <= z = True, then x <= z = True
        @0 ordTransitivity :  ∀ ( x y z : e ) → {{ (x <= y) ≡ True }} → {{ (y <= z) ≡ True }} → (x <= z) ≡ True

        -- Reflexivity: x <= x = True
        @0 ordReflexivity : ∀ (x : e) → (x <= x) ≡ True

        -- Antisymmetry: if x <= y && y <= x = True, then x == y = True
        @0 ordAntisymmetry : ∀ (x y : e) → {{ (x <= y) ≡ True }} → {{ (y <= x) ≡ True }} → x ≡ y
        
open LawfulOrd ⦃ ... ⦄ public
 