module Lib.Util where

open import Haskell.Prelude

open import Lib.AndProofs

-- ALL MATCH -----------------------------------------------

allMatch : (Int → Bool) → List Int → Bool
allMatch f [] = True
allMatch f (x ∷ is) = f x && allMatch f is

allMatchHead : ∀ (x : Int) (xs : List Int) (f : Int → Bool) 
               → allMatch f (x ∷ xs) ≡ True
               → f x ≡ True
allMatchHead x [] f h = &&-true' (f x) h
allMatchHead x xs f h = &&-leftTrue (f x) (allMatch f xs) h

allMatchTail : ∀ (x : Int) (xs : List Int) (f : Int → Bool) 
               → allMatch f (x ∷ xs) ≡ True
               → allMatch f xs ≡ True
allMatchTail x [] f h = refl
allMatchTail x xs f h = &&-rightTrue (f x) (allMatch f xs) h

-- NONE MATCH ----------------------------------------------
