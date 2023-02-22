module Documentation.Structures where

open import Haskell.Prelude using (Int ; List ; String ; a ; _×_)

-- type

Entry = Int × List String

{-# COMPILE AGDA2HS Entry #-}

-- newtype

record Indexed (a : Set) : Set where
    constructor MkIndexed_
    field
        fld : Int × a
open Indexed public

{-# COMPILE AGDA2HS Indexed newtype #-}

-- data

data Nat : Set where
    Zero : Nat 
    Suc : Nat → Nat
    
{-# COMPILE AGDA2HS Nat #-}

data Tree (a : Set) : Set where
    Leaf   : a → Tree a
    Branch : a → Tree a → Tree a → Tree a
    
{-# COMPILE AGDA2HS Tree #-}

-- record

record Citation : Set where
    field
        id     : Int
        author : String
        title  : String
        url    : String
        year   : Int
open Citation public

{-# COMPILE AGDA2HS Citation #-}
