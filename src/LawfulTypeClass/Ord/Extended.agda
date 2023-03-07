module LawfulTypeClass.Ord.Extended where

open import Haskell.Prelude using ( a; _||_; True; False; Bool )

open import LawfulTypeClass.Eq.Fixed
open import LawfulTypeClass.Ord.Fixed

import Relation.Binary.PropositionalEquality as PEq
open PEq using (_≡_; refl; sym; cong)

record LawfulOrd (a : Set) {{iOrd : Ord a}} : Set₁ where
    field
        -- Comparability: x <= y || y <= x = True
        comparability : ∀ (x y : a) → (x <= y || y <= x) ≡ True

        -- Transitivity: if x <= y && y <= z = True, then x <= z = True
        transitivity :  ∀ ( x y z : a ) → {{ (x <= y) ≡ True }} → {{ (y <= z) ≡ True }} → (x <= z) ≡ True

        -- Reflexivity: x <= x = True
        reflexivity : ∀ (x : a) → (x <= x) ≡ True

        -- Antisymmetry: if x <= y && y <= x = True, then x == y = True
        antisymmetry : ∀ (x y : a) → {{ (x <= y) ≡ True }} → {{ (y <= x) ≡ True }} → x ≡ y
        
open LawfulOrd ⦃ ... ⦄ public

compBool : ∀ (x y : Bool) → (x <= y || y <= x) ≡ True
compBool False False = refl
compBool False True = refl
compBool True False = refl
compBool True True = refl

transBool : ∀ ( x y z : Bool ) → {{ (x <= y) ≡ True }} → {{ (y <= z) ≡ True }} → (x <= z) ≡ True
transBool False False False = refl
transBool False False True = refl
transBool False True True = refl
transBool True True True = refl

reflBool : ∀ (x : Bool) → (x <= x) ≡ True
reflBool False = refl
reflBool True = refl

antisymBool : ∀ (x y : Bool) → {{ (x <= y) ≡ True }} → {{ (y <= x) ≡ True }} → x ≡ y
antisymBool False False = refl
antisymBool True True = refl

instance
    iLawfulOrdBool : LawfulOrd Bool
    iLawfulOrdBool = λ where
        .comparability → compBool
        .transitivity → transBool
        .reflexivity → reflBool
        .antisymmetry → antisymBool


record LawfulOrd₁ (a : Set) {{iOrd : Ord a}} : Set₁ where
    -- Comparability: x <= y || y <= x = True
    comparability₁ : ∀ (x y : a) → (x <= y || y <= x) ≡ True
    comparability₁ = {!   !}

    -- Transitivity: if x <= y && y <= z = True, then x <= z = True
    transitivity₁ :  ∀ ( x y z : a ) → (x <= y) ≡ True → (y <= z) ≡ True → (x <= z) ≡ True
    transitivity₁ = {!   !}

    -- Reflexivity: x <= x = True
    reflexivity₁ : ∀ (x : a) → (x <= x) ≡ True
    reflexivity₁ x = {!   !}

    -- Antisymmetry: if x <= y && y <= x = True, then x == y = True
    antisymmetry₁ : ∀ (x y : a) → (x <= y) ≡ True → (y <= x) ≡ True → x ≡ y
    antisymmetry₁ x y hxy hyx = {!   !}
        
open LawfulOrd₁ ⦃ ... ⦄ public
