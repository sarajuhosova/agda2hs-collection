{-# OPTIONS --allow-unsolved-metas #-}

module NewType.Test where

open import Haskell.Prelude

record Foo : Set where
    constructor NewFoo_
    field
        bar : Int
open Foo public

{-# COMPILE AGDA2HS Foo newtype #-}

record Foon : Set where
    constructor Fooₙ_
    field
        bar : Int
open Foon public

{-# COMPILE AGDA2HS Foon newtype #-}

foo : Foo
foo = NewFoo 3

record Fool (a : Set) : Set where
    constructor NewFool_
    field
        bar : a
open Fool public

{-# COMPILE AGDA2HS Fool newtype #-}

foolInt : Fool Int
foolInt = NewFool 3

foolString : Fool String
foolString = NewFool "Hello!"

foolPair : Fool (Int × String)
foolPair = NewFool (3 , "Hello!")

record Foop (a b : Set) : Set where
    constructor NewFoop_
    field
        bar : a × b
open Foop public

{-# COMPILE AGDA2HS Foop newtype #-}

foopIntString : Foop Int String
foopIntString = NewFoop (3 , "Hello!")
