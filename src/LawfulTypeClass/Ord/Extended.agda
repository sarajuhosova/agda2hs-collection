module LawfulTypeClass.Ord.Extended where

open import Haskell.Prelude hiding ( IsLawfulEq; IsLawfulOrd )

open import LawfulTypeClass.Eq.Extended

import Relation.Binary.PropositionalEquality as PEq
open PEq using (_≡_; refl)

record IsLawfulOrd (a : Set) {{iOrd : Ord a}} : Set₁ where
    field
        overlap ⦃ super ⦄ : IsLawfulEq a

        -- Comparability: x <= y || y <= x = True
        comparability : ∀ (x y : a) → (x <= y || y <= x) ≡ True

        -- Transitivity: if x <= y && y <= z = True, then x <= z = True
        transitivity :  ∀ ( x y z : a ) → {{ (x <= y) ≡ True }} → {{ (y <= z) ≡ True }} → (x <= z) ≡ True

        -- Reflexivity: x <= x = True
        reflexivity : ∀ (x : a) → (x <= x) ≡ True

        -- Antisymmetry: if x <= y && y <= x = True, then x == y = True
        antisymmetry : ∀ (x y : a) → {{ (x <= y) ≡ True }} → {{ (y <= x) ≡ True }} → x ≡ y

        -- x >= y = y <= x
        lte2gte : ∀ (x y : a) → (x >= y) ≡ (y <= x)

        -- x < y = x <= y && x /= y
        lNotLteNeq : ∀ (x y : a) → (x < y) ≡ (x <= y && x /= y)

        -- x > y = y < x
        lt2gt : ∀ (x y : a) → (x > y) ≡ (y < x)

        -- x < y = compare x y == LT
        compareLt  : ∀ (x y : a) → (x < y) ≡ True → compare x y ≡ LT
        compareLt' : ∀ (x y : a) → compare x y ≡ LT → (x < y) ≡ True

        -- x > y = compare x y == GT
        compareGt  : ∀ (x y : a) → (x > y) ≡ True → compare x y ≡ GT
        compareGt' : ∀ (x y : a) → compare x y ≡ GT → (x > y) ≡ True

        -- x == y = compare x y == EQ
        compareEq  : ∀ (x y : a) → x ≡ y → compare x y ≡ EQ
        compareEq' : ∀ (x y : a) → compare x y ≡ EQ → x ≡ y

        -- min x y == if x <= y then x else y = True
        min2if : ∀ (x y : a) → (min x y) ≡ (if (x <= y) then x else y)

        -- max x y == if x >= y then x else y = True
        max2if : ∀ (x y : a) → (max x y) ≡ (if (x >= y) then x else y)
        
open IsLawfulOrd ⦃ ... ⦄ public
