module FlowWitness.BinTreeAdd.WitnessCase where

open import Haskell.Prelude

open import Lib.BoxedProof
open import Lib.InfInt
open import Lib.Util
open import FlowWitness.BinTree
open import FlowWitness.Case

-- add :: Int -> BinTree -> BinTree
add : ∀ {@0 min max : InfInt} 
      → (i : Int) → BinTree min max 
      → @0 (min < (IInt i)) ≡ True → @0 ((IInt i) < max) ≡ True 
      → BinTree min max
add i Leaf h1 h2 = Branch i (Leaf {{ h1 }}) (Leaf {{ h2 }})
add i (Branch x left right) h1 h2 =
    case''' i < x of λ where
        (True [ hlt ]) → Branch x (add i left h1 hlt) right
        (False [ _ ]) → case''' x < i of λ where
            (True [ hgt ]) → Branch x left (add i right hgt h2)
            (False [ _ ]) → Branch x left right
