module LawfulTypeClass.Instance.Bool.Util where

open import Haskell.Prelude using ( Bool; True; False; _==_; _<=_; _||_ )

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
