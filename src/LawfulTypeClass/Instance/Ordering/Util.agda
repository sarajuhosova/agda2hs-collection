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

lte2gteOrdering : ∀ (x y : Ordering) → (x >= y) ≡ (y <= x)
lte2gteOrdering LT LT = refl
lte2gteOrdering LT EQ = refl
lte2gteOrdering LT GT = refl
lte2gteOrdering EQ LT = refl
lte2gteOrdering EQ EQ = refl
lte2gteOrdering EQ GT = refl
lte2gteOrdering GT LT = refl
lte2gteOrdering GT EQ = refl
lte2gteOrdering GT GT = refl

lNotLteNeqOrdering : ∀ (x y : Ordering) → (x < y) ≡ (x <= y && x /= y)
lNotLteNeqOrdering LT LT = refl
lNotLteNeqOrdering LT EQ = refl
lNotLteNeqOrdering LT GT = refl
lNotLteNeqOrdering EQ LT = refl
lNotLteNeqOrdering EQ EQ = refl
lNotLteNeqOrdering EQ GT = refl
lNotLteNeqOrdering GT LT = refl
lNotLteNeqOrdering GT EQ = refl
lNotLteNeqOrdering GT GT = refl

lt2gtOrdering : ∀ (x y : Ordering) → (x > y) ≡ (y < x)
lt2gtOrdering LT LT = refl
lt2gtOrdering LT EQ = refl
lt2gtOrdering LT GT = refl
lt2gtOrdering EQ LT = refl
lt2gtOrdering EQ EQ = refl
lt2gtOrdering EQ GT = refl
lt2gtOrdering GT LT = refl
lt2gtOrdering GT EQ = refl
lt2gtOrdering GT GT = refl

compareLtOrdering : ∀ (x y : Ordering) → (x < y) ≡ True → compare x y ≡ LT
compareLtOrdering LT EQ refl = refl
compareLtOrdering LT GT refl = refl
compareLtOrdering EQ GT refl = refl
compareLtOrdering GT LT ()
compareLtOrdering GT EQ ()
compareLtOrdering GT GT ()

compareGtOrdering : ∀ (x y : Ordering) → (x > y) ≡ True → compare x y ≡ GT
compareGtOrdering LT LT ()
compareGtOrdering LT EQ ()
compareGtOrdering LT GT ()
compareGtOrdering EQ LT refl = refl
compareGtOrdering GT LT refl = refl
compareGtOrdering GT EQ refl = refl

compareEqOrdering : ∀ (x y : Ordering) → x ≡ y → compare x y ≡ EQ
compareEqOrdering LT .LT refl = refl
compareEqOrdering EQ .EQ refl = refl
compareEqOrdering GT .GT refl = refl

compareLtOrdering' : ∀ (x y : Ordering) → compare x y ≡ LT → (x < y) ≡ True
compareLtOrdering' LT EQ refl = refl
compareLtOrdering' LT GT refl = refl
compareLtOrdering' EQ GT refl = refl
compareLtOrdering' GT LT ()
compareLtOrdering' GT EQ ()
compareLtOrdering' GT GT ()

compareGtOrdering' : ∀ (x y : Ordering) → compare x y ≡ GT → (x > y) ≡ True
compareGtOrdering' LT LT ()
compareGtOrdering' LT EQ ()
compareGtOrdering' LT GT ()
compareGtOrdering' EQ LT refl = refl
compareGtOrdering' GT LT refl = refl
compareGtOrdering' GT EQ refl = refl

compareEqOrdering' : ∀ (x y : Ordering) → compare x y ≡ EQ → x ≡ y
compareEqOrdering' LT LT _ = refl
compareEqOrdering' EQ EQ _ = refl
compareEqOrdering' GT GT _ = refl

min2ifOrdering : ∀ (x y : Ordering) → (min x y) ≡ (if (x <= y) then x else y)
min2ifOrdering LT LT = refl
min2ifOrdering LT EQ = refl
min2ifOrdering LT GT = refl
min2ifOrdering EQ LT = refl
min2ifOrdering EQ EQ = refl
min2ifOrdering EQ GT = refl
min2ifOrdering GT LT = refl
min2ifOrdering GT EQ = refl
min2ifOrdering GT GT = refl

max2ifOrdering : ∀ (x y : Ordering) → (max x y) ≡ (if (x >= y) then x else y)
max2ifOrdering LT LT = refl
max2ifOrdering LT EQ = refl
max2ifOrdering LT GT = refl
max2ifOrdering EQ LT = refl
max2ifOrdering EQ EQ = refl
max2ifOrdering EQ GT = refl
max2ifOrdering GT LT = refl
max2ifOrdering GT EQ = refl
max2ifOrdering GT GT = refl
