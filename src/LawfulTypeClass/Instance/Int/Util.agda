module LawfulTypeClass.Instance.Int.Util where

open import Haskell.Prelude using ( Int; True
                                  ; _==_; _/=_; _<=_; _>=_; _<_; _>_; compare
                                  ; _&&_; _||_
                                  ; LT; GT; EQ
                                  ; min; max
                                  ; if_then_else_
                                  )

import Relation.Binary.PropositionalEquality as PEq
open PEq using ( _≡_ )

postulate equalityInt : ∀ (x y : Int) → (x == y) ≡ True → x ≡ y

postulate equalityInt' : ∀ (x y : Int) → x ≡ y → (x == y) ≡ True

postulate compInt : ∀ (x y : Int) → (x <= y || y <= x) ≡ True

postulate transInt : ∀ ( x y z : Int ) → {{ (x <= y) ≡ True }} → {{ (y <= z) ≡ True }} → (x <= z) ≡ True

postulate reflInt : ∀ (x : Int) → (x <= x) ≡ True

postulate antisymInt : ∀ (x y : Int) → {{ (x <= y) ≡ True }} → {{ (y <= x) ≡ True }} → x ≡ y

postulate lte2gteInt : ∀ (x y : Int) → (x >= y) ≡ (y <= x)

postulate lNotLteNeqInt : ∀ (x y : Int) → (x < y) ≡ (x <= y && x /= y)

postulate lt2gtInt : ∀ (x y : Int) → (x > y) ≡ (y < x)

postulate compareLtInt : ∀ (x y : Int) → (x < y) ≡ True → compare x y ≡ LT

postulate compareLtInt' : ∀ (x y : Int) → compare x y ≡ LT → (x < y) ≡ True

postulate compareGtInt : ∀ (x y : Int) → (x > y) ≡ True → compare x y ≡ GT

postulate compareGtInt' : ∀ (x y : Int) → compare x y ≡ GT → (x > y) ≡ True

postulate compareEqInt : ∀ (x y : Int) → x ≡ y → compare x y ≡ EQ

postulate compareEqInt' : ∀ (x y : Int) → compare x y ≡ EQ → x ≡ y

postulate min2ifInt : ∀ (x y : Int) → (min x y) ≡ (if (x <= y) then x else y)

postulate max2ifInt : ∀ (x y : Int) → (max x y) ≡ (if (x >= y) then x else y)
