{-# OPTIONS --allow-unsolved-metas #-}

module NewType.Behaviour where

open import Haskell.Prelude

data DataFoo : Set where
    DFoo : String → DataFoo

{-# COMPILE AGDA2HS DataFoo #-}


