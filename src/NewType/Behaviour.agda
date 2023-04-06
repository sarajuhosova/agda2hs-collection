{-# OPTIONS --allow-unsolved-metas #-}

module NewType.Behaviour where

open import Haskell.Prelude

data DataFoo : Set where
    DFoo : String → DataFoo

{-# COMPILE AGDA2HS DataFoo newtype #-}

data Bla : Set where
    MkBla : String → Int → Bla

{-# COMPILE AGDA2HS Bla newtype #-}

-- data Blaa : Set where
--     BlaaOne : String → Blaa
--     BlaaTwo : String → Blaa

-- {-# COMPILE AGDA2HS Blaa newtype #-}


