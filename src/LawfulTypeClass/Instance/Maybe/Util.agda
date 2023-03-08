-- {-# OPTIONS --allow-unsolved-metas #-}

module LawfulTypeClass.Instance.Maybe.Util where

open import Haskell.Prelude

open import LawfulTypeClass.Eq.Extended
open import LawfulTypeClass.Ord.Extended

import Relation.Binary.PropositionalEquality as PEq
open PEq using ( _≡_; refl; cong )
open PEq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

equalityMaybe : {{ iEqA : Eq a }} {{ iLawfulEqA : LawfulEq₂ a }}
    → ∀ (x y : Maybe a) → (x == y) ≡ True → x ≡ y
equalityMaybe Nothing Nothing _ = refl
equalityMaybe {{ _ }} {{ lEq }} (Just x) (Just y) h
    = cong Just (LawfulEq₂.equality lEq x y h)

equalityMaybe' : {{ iEqA : Eq a }} {{ iLawfulEqA : LawfulEq₂ a }}
    → ∀ (x y : Maybe a) → x ≡ y → (x == y) ≡ True
equalityMaybe' Nothing Nothing _ = refl
equalityMaybe' {{ _ }} {{ lEq }} (Just x) (Just y) refl
    = LawfulEq₂.equality' lEq x y refl

compMaybe : {{ iOrdA : Ord a }} → {{ iLawfulOrdA : LawfulOrd a }}
    → ∀ (x y : Maybe a) → (x <= y || y <= x) ≡ True
compMaybe Nothing Nothing = refl
compMaybe Nothing (Just _) = refl
compMaybe (Just _) Nothing = refl
compMaybe (Just x) (Just y) = {!   !}

transMaybe : {{ iOrdA : Ord a }} → {{ iLawfulOrdA : LawfulOrd a }}
    → ∀ ( x y z : Maybe a ) → {{ (x <= y) ≡ True }} → {{ (y <= z) ≡ True }} → (x <= z) ≡ True
transMaybe Nothing Nothing Nothing = refl
transMaybe Nothing Nothing (Just _) = refl
transMaybe Nothing (Just _) (Just _) = refl
transMaybe {{ _ }} {{ lOrd }} (Just x) (Just y) (Just z)
    = cong (λ o → o /= GT) (LawfulOrd.compareLt lOrd x z {!   !})

reflMaybe : {{ iOrdA : Ord a }} → {{ iLawfulOrdA : LawfulOrd a }}
    → ∀ (x : Maybe a) → (x <= x) ≡ True
reflMaybe Nothing = refl
reflMaybe {{ _ }} {{ lOrd }} (Just x)
    = cong (λ o → o /= GT) (LawfulOrd.compareEq lOrd x x refl)

antisymMaybe : {{ iOrdA : Ord a }} → {{ iLawfulOrdA : LawfulOrd a }}
    → ∀ (x y : Maybe a) → {{ (x <= y) ≡ True }} → {{ (y <= x) ≡ True }} → x ≡ y
antisymMaybe Nothing Nothing = refl
antisymMaybe {{ _ }} {{ lOrd }} (Just x) (Just y) {{ h1 }} {{ h2 }}
    = -- ?
    cong Just {!   !}
    -- (LawfulOrd.antisymmetry lOrd x y ? ?)
    -- (LawfulEq₂.equality (LawfulOrd.super lOrd) x y {!   !})

lte2gteMaybe : {{ iOrdA : Ord a }} → {{ iLawfulOrdA : LawfulOrd a }}
    → ∀ (x y : Maybe a) → (x >= y) ≡ (y <= x)
lte2gteMaybe Nothing Nothing = refl
lte2gteMaybe Nothing (Just _) = refl
lte2gteMaybe (Just _) Nothing = refl
lte2gteMaybe {{ _ }} {{ lOrd }} (Just x) (Just y) = {!   !}

lNotLteNeqMaybe : {{ iOrdA : Ord a }} → {{ iLawfulOrdA : LawfulOrd a }}
    → ∀ (x y : Maybe a) → (x < y) ≡ (x <= y && x /= y)
lNotLteNeqMaybe Nothing Nothing = refl
lNotLteNeqMaybe Nothing (Just _) = refl
lNotLteNeqMaybe (Just _) Nothing = refl
lNotLteNeqMaybe (Just x) (Just y) = {!   !}

lt2gtMaybe : {{ iOrdA : Ord a }} → {{ iLawfulOrdA : LawfulOrd a }}
    → ∀ (x y : Maybe a) → (x > y) ≡ (y < x)
lt2gtMaybe Nothing Nothing = refl
lt2gtMaybe Nothing (Just _) = refl
lt2gtMaybe (Just _) Nothing = refl
lt2gtMaybe {{ _ }} {{ lOrd }} (Just x) (Just y) = {!   !}

compareLtMaybe : {{ iOrdA : Ord a }} → {{ iLawfulOrdA : LawfulOrd a }}
    → ∀ (x y : Maybe a) → (x < y) ≡ True → compare x y ≡ LT
compareLtMaybe Nothing (Just _) refl = refl
compareLtMaybe {{ _ }} {{ lOrd }} (Just x) (Just y) h
    = LawfulOrd.compareLt lOrd x y {!   !}

compareLtMaybe' : {{ iOrdA : Ord a }} → {{ iLawfulOrdA : LawfulOrd a }}
    → ∀ (x y : Maybe a) → compare x y ≡ LT → (x < y) ≡ True
compareLtMaybe' Nothing (Just _) refl = refl
compareLtMaybe' {{ _ }} {{ lOrd }} (Just x) (Just y) h
    = {!   !}

compareGtMaybe : {{ iOrdA : Ord a }} → {{ iLawfulOrdA : LawfulOrd a }}
    → ∀ (x y : Maybe a) → (x > y) ≡ True → compare x y ≡ GT
compareGtMaybe (Just x) Nothing refl = refl
compareGtMaybe {{ _ }} {{ lOrd }} (Just x) (Just y) h
    = LawfulOrd.compareGt lOrd x y {!   !}

compareGtMaybe' : {{ iOrdA : Ord a }} → {{ iLawfulOrdA : LawfulOrd a }}
    → ∀ (x y : Maybe a) → compare x y ≡ GT → (x > y) ≡ True
compareGtMaybe' (Just x) Nothing refl = refl
compareGtMaybe' {{ _ }} {{ lOrd }} (Just x) (Just y) h
    = {!   !}

compareEqMaybe : {{ iOrdA : Ord a }} → {{ iLawfulOrdA : LawfulOrd a }}
    → ∀ (x y : Maybe a) → x ≡ y → compare x y ≡ EQ
compareEqMaybe Nothing Nothing refl = refl
compareEqMaybe {{ _ }} {{ lOrd }} (Just x) (Just .x) refl
    = LawfulOrd.compareEq lOrd x x refl

compareEqMaybe' : {{ iOrdA : Ord a }} → {{ iLawfulOrdA : LawfulOrd a }}
    → ∀ (x y : Maybe a) → compare x y ≡ EQ → x ≡ y
compareEqMaybe' Nothing Nothing _ = refl
compareEqMaybe' {{ _ }} {{ lOrd }} (Just x) (Just y) h
    = {!   !}

min2ifMaybe : {{ iOrdA : Ord a }} → {{ iLawfulOrdA : LawfulOrd a }}
    → ∀ (x y : Maybe a) → (min x y) ≡ (if (x <= y) then x else y)
min2ifMaybe Nothing Nothing = refl
min2ifMaybe Nothing (Just _) = refl
min2ifMaybe (Just _) Nothing = refl
min2ifMaybe {{ _ }} {{ lOrd }} (Just x) (Just y) = {!   !}

max2ifMaybe : {{ iOrdA : Ord a }} → {{ iLawfulOrdA : LawfulOrd a }}
    → ∀ (x y : Maybe a) → (max x y) ≡ (if (x >= y) then x else y)
max2ifMaybe Nothing Nothing = refl
max2ifMaybe Nothing (Just _) = refl
max2ifMaybe (Just _) Nothing = refl
max2ifMaybe {{ _ }} {{ lOrd }} (Just x) (Just y) = {!   !}
