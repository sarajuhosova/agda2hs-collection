module LawfulTypeClass.Eq.Fixed where

open import Haskell.Prelude using ( Bool; True; False; not
                                  ; Ordering; GT; LT; EQ
                                  )

import Relation.Binary.PropositionalEquality as PEq
open PEq using (_≡_; refl; sym; cong)

record Eq (a : Set) : Set where
    infix 4 _==_ _/=_
    field
        _==_ : a → a → Bool

        equality  : ∀ (x y : a) → (x == y) ≡ True → x ≡ y
        equality' : ∀ (x y : a) → x ≡ y → (x == y) ≡ True
    
    _/=_ : a → a → Bool
    x /= y = not (x == y)
        
open Eq ⦃ ... ⦄ public

eqBool : Bool → Bool → Bool
eqBool False False = True
eqBool True  True  = True
eqBool _     _     = False

equalityBool : ∀ (x y : Bool) → eqBool x y ≡ True → x ≡ y
equalityBool False False _ = refl
equalityBool True True _ = refl

equalityBool' : ∀ (x y : Bool) → x ≡ y → eqBool x y ≡ True
equalityBool' False False _ = refl
equalityBool' True True _ = refl

instance
    iEqBool : Eq Bool
    iEqBool = λ where
        ._==_ → eqBool
        .equality → equalityBool
        .equality' → equalityBool'

    iEqOrdering : Eq Ordering
    iEqOrdering ._==_ LT LT = True
    iEqOrdering ._==_ EQ EQ = True
    iEqOrdering ._==_ GT GT = True
    iEqOrdering ._==_ _  _  = False

    iEqOrdering .equality LT LT _ = refl
    iEqOrdering .equality EQ EQ _ = refl
    iEqOrdering .equality GT GT _ = refl

    iEqOrdering .equality' LT LT _ = refl
    iEqOrdering .equality' EQ EQ _ = refl
    iEqOrdering .equality' GT GT _ = refl
        

