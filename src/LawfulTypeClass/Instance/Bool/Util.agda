module LawfulTypeClass.Instance.Bool.Util where

open import Haskell.Prelude using ( Bool; True; False
                                  ; _==_; _/=_; _<=_; _>=_; _<_; _>_; compare
                                  ; _&&_; _||_
                                  ; LT; GT; EQ
                                  ; min; max
                                  ; if_then_else_
                                  )

import Relation.Binary.PropositionalEquality as PEq
open PEq using ( _≡_; refl )

equalityBool : ∀ (x y : Bool) → (x == y) ≡ True → x ≡ y
equalityBool False False _ = refl
equalityBool True True _ = refl

equalityBool' : ∀ (x y : Bool) → x ≡ y → (x == y) ≡ True
equalityBool' False False _ = refl
equalityBool' True True _ = refl

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

lte2gteBool : ∀ (x y : Bool) → (x >= y) ≡ (y <= x)
lte2gteBool False False = refl
lte2gteBool False True = refl
lte2gteBool True False = refl
lte2gteBool True True = refl

lNotLteNeqBool : ∀ (x y : Bool) → (x < y) ≡ (x <= y && x /= y)
lNotLteNeqBool False False = refl
lNotLteNeqBool False True = refl
lNotLteNeqBool True False = refl
lNotLteNeqBool True True = refl

lt2gtBool : ∀ (x y : Bool) → (x > y) ≡ (y < x)
lt2gtBool False False = refl
lt2gtBool False True = refl
lt2gtBool True False = refl
lt2gtBool True True = refl

compareLtBool : ∀ (x y : Bool) → (x < y) ≡ True → compare x y ≡ LT
compareLtBool False True refl = refl
compareLtBool True False ()
compareLtBool True True ()

compareGtBool : ∀ (x y : Bool) → (x > y) ≡ True → compare x y ≡ GT
compareGtBool False False ()
compareGtBool False True ()
compareGtBool True False refl = refl

compareEqBool : ∀ (x y : Bool) → x ≡ y → compare x y ≡ EQ
compareEqBool False .False refl = refl
compareEqBool True .True refl = refl

compareLtBool' : ∀ (x y : Bool) → compare x y ≡ LT → (x < y) ≡ True
compareLtBool' False True refl = refl
compareLtBool' True False ()
compareLtBool' True True ()

compareGtBool' : ∀ (x y : Bool) → compare x y ≡ GT → (x > y) ≡ True
compareGtBool' False False ()
compareGtBool' False True ()
compareGtBool' True False refl = refl

compareEqBool' : ∀ (x y : Bool) → compare x y ≡ EQ → x ≡ y
compareEqBool' False False _ = refl
compareEqBool' True True _ = refl

min2ifBool : ∀ (x y : Bool) → (min x y) ≡ (if (x <= y) then x else y)
min2ifBool False False = refl
min2ifBool False True = refl
min2ifBool True False = refl
min2ifBool True True = refl

max2ifBool : ∀ (x y : Bool) → (max x y) ≡ (if (x >= y) then x else y)
max2ifBool False False = refl
max2ifBool False True = refl
max2ifBool True False = refl
max2ifBool True True = refl
 