module LawfulTypeClass.Instance.Int.Util where

open import Haskell.Prelude using ( Int; _==_; _<=_; _||_; True )

import Relation.Binary.PropositionalEquality as PEq
open PEq using ( _≡_ )

postulate equalityInt : ∀ (x y : Int) → (x == y) ≡ True → x ≡ y

postulate equalityInt' : ∀ (x y : Int) → x ≡ y → (x == y) ≡ True

postulate compInt : ∀ (x y : Int) → (x <= y || y <= x) ≡ True

postulate transInt : ∀ ( x y z : Int ) → {{ (x <= y) ≡ True }} → {{ (y <= z) ≡ True }} → (x <= z) ≡ True

postulate reflInt : ∀ (x : Int) → (x <= x) ≡ True

postulate antisymInt : ∀ (x y : Int) → {{ (x <= y) ≡ True }} → {{ (y <= x) ≡ True }} → x ≡ y
