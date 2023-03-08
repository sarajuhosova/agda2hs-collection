module LawfulTypeClass.Instance.Ordering.Util where

open import Haskell.Prelude

import Relation.Binary.PropositionalEquality as PEq
open PEq using ( _≡_; refl )

equalityOrdering : ∀ (x y : Ordering) → (x == y) ≡ True → x ≡ y
equalityOrdering LT LT _ = refl
equalityOrdering EQ EQ _ = refl
equalityOrdering GT GT _ = refl

equalityOrdering' : ∀ (x y : Ordering) → x ≡ y → (x == y) ≡ True
equalityOrdering' LT LT _ = refl
equalityOrdering' EQ EQ _ = refl
equalityOrdering' GT GT _ = refl

compOrdering : ∀ (x y : Ordering) → (x <= y || y <= x) ≡ True
compOrdering LT LT = refl
compOrdering LT EQ = refl
compOrdering LT GT = refl
compOrdering EQ LT = refl
compOrdering EQ EQ = refl
compOrdering EQ GT = refl
compOrdering GT LT = refl
compOrdering GT EQ = refl
compOrdering GT GT = refl

transOrdering : ∀ ( x y z : Ordering ) → {{ (x <= y) ≡ True }} → {{ (y <= z) ≡ True }} → (x <= z) ≡ True
transOrdering LT LT LT = refl
transOrdering LT LT EQ = refl
transOrdering LT LT GT = refl
transOrdering LT EQ EQ = refl
transOrdering LT EQ GT = refl
transOrdering LT GT GT = refl
transOrdering EQ EQ EQ = refl
transOrdering EQ EQ GT = refl
transOrdering EQ GT GT = refl
transOrdering GT GT GT = refl

reflOrdering : ∀ (x : Ordering) → (x <= x) ≡ True
reflOrdering LT = refl
reflOrdering EQ = refl
reflOrdering GT = refl

antisymOrdering : ∀ (x y : Ordering) → {{ (x <= y) ≡ True }} → {{ (y <= x) ≡ True }} → x ≡ y
antisymOrdering LT LT = refl
antisymOrdering EQ EQ = refl
antisymOrdering GT GT = refl
