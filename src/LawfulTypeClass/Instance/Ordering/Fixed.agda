module LawfulTypeClass.Instance.Ordering.Fixed where

open import Haskell.Prelude using ( Bool; True; False
                                  ; Ordering; GT; LT; EQ
                                  )

import Relation.Binary.PropositionalEquality as PEq
open PEq using ( refl )

open import LawfulTypeClass.Eq.Fixed

instance
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
