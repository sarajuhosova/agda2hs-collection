module Lib.Util where

open import Haskell.Prelude

open import Lib.AndProofs

-- ALL MATCH -----------------------------------------------

allMatch : (a → Bool) → List a → Bool
allMatch f [] = True
allMatch f (x ∷ is) = f x && allMatch f is

{-# COMPILE AGDA2HS allMatch #-}

allMatchTrue : ∀ {A : Set} (xs : List A) → (allMatch (λ x → True) xs) ≡ True
allMatchTrue [] = refl
allMatchTrue (x ∷ xs) = allMatchTrue xs

allMatchHead : ∀ (x : a) (xs : List a) (f : a → Bool) 
               → allMatch f (x ∷ xs) ≡ True
               → f x ≡ True
allMatchHead x [] f h = &&-true' (f x) h
allMatchHead x xs f h = &&-leftTrue (f x) (allMatch f xs) h

allMatchHead' : ∀ {x : a} {xs : List a} {f : a → Bool}
               → allMatch f (x ∷ xs) ≡ True
               → f x ≡ True
allMatchHead' h = &&-leftTrue' h

allMatchTail : ∀ (x : a) (xs : List a) (f : a → Bool) 
               → allMatch f (x ∷ xs) ≡ True
               → allMatch f xs ≡ True
allMatchTail x [] f h = refl
allMatchTail x xs f h = &&-rightTrue (f x) (allMatch f xs) h

-- SORTING -------------------------------------------------

isSorted : {{ Ord a }} → List a → Bool
isSorted [] = True
isSorted (x ∷ []) = True
isSorted (x ∷ y ∷ xs) = x <= y && isSorted (y ∷ xs)

{-# COMPILE AGDA2HS isSorted #-}

-- NO DUPLICATES -------------------------------------------

noDuplicates : {{ Eq a }} → List a → Bool
noDuplicates [] = True
noDuplicates (x ∷ []) = True
noDuplicates (x ∷ xs) = allMatch (λ i → i /= x) xs && noDuplicates xs

{-# COMPILE AGDA2HS noDuplicates #-}
