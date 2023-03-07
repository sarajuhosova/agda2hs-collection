module LawfulTypeClass.Instance.Int.Util where

open import Haskell.Prelude using ( Int; _==_; True )

import Relation.Binary.PropositionalEquality as PEq
open PEq using ( _≡_ )

postulate equalityInt : ∀ (x y : Int) → (x == y) ≡ True → x ≡ y

postulate equalityInt' : ∀ (x y : Int) → x ≡ y → (x == y) ≡ True
