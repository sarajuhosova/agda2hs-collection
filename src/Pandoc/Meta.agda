module Pandoc.Meta where

open import Haskell.Prelude
open import Pandoc.Definition

------------------------------------------------------------
-- IMPORTS                                                --
------------------------------------------------------------

{-# FOREIGN AGDA2HS import Data.Map (Map, union, empty) #-}
postulate Map : (A : Set) → (B : Set) → Set
postulate union : {A B : Set} → Map A B → Map A B → Map A B
postulate empty : {A B : Set} → Map A B

------------------------------------------------------------
-- DATA DEFINITIONS                                       --
------------------------------------------------------------

-- data MetaValue = MetaMap (M.Map Text MetaValue)
--                | MetaList [MetaValue]
--                | MetaBool Bool
--                | MetaString Text
--                | MetaInlines [Inline]
--                | MetaBlocks [Block]
--                deriving (Eq, Ord, Show, Read)

data MetaValue : Set where
    MetaMap : Text → MetaValue
    MetaList : List MetaValue → MetaValue
    MetaBool : Bool → MetaValue
    MetaString : Text → MetaValue
    MetaInlines : List Inline → MetaValue
    MetaBlocks : List Block → MetaValue

-- newtype Meta = Meta { unMeta :: M.Map Text MetaValue }
--                deriving (Eq, Ord, Show, Read)

record Meta : Set where
    pattern; constructor MkMeta_
    field
        unMeta : Map Text MetaValue
open Meta public

-- instance Semigroup Meta where
--   (Meta m1) <> (Meta m2) = Meta (M.union m2 m1)

instance
    iSemigroupMeta : Semigroup Meta
    iSemigroupMeta ._<>_ (MkMeta m1) (MkMeta m2) = MkMeta (union m2 m1)
  
-- instance Monoid Meta where
--   mempty = Meta M.empty
--   mappend = (<>)

    iMonoidMeta : Monoid Meta
    iMonoidMeta .mempty = MkMeta empty

{-# COMPILE AGDA2HS Meta #-}
{-# COMPILE AGDA2HS iSemigroupMeta #-}
{-# COMPILE AGDA2HS iMonoidMeta #-}
{-# COMPILE AGDA2HS MetaValue #-}
