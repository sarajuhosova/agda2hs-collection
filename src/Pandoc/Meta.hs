module Pandoc.Meta ( Meta(..) ) where

import qualified Data.Map as M
import Data.Text (Text)
import Pandoc.Definition ( Inline(..), Block(..) )

-- | Metadata for the document:  title, authors, date.
newtype Meta = Meta { unMeta :: M.Map Text MetaValue }
               deriving (Eq, Ord, Show, Read) --, Typeable, Data, Generic)

instance Semigroup Meta where
  (Meta m1) <> (Meta m2) = Meta (M.union m2 m1)
  -- note: M.union is left-biased, so if there are fields in both m2
  -- and m1, m2 wins.
instance Monoid Meta where
  mempty = Meta M.empty
  mappend = (<>)

data MetaValue = MetaMap (M.Map Text MetaValue)
               | MetaList [MetaValue]
               | MetaBool Bool
               | MetaString Text
               | MetaInlines [Inline]
               | MetaBlocks [Block]
               deriving (Eq, Ord, Show, Read) --, Typeable, Data, Generic)

nullMeta :: Meta
nullMeta = Meta M.empty

isNullMeta :: Meta -> Bool
isNullMeta (Meta m) = M.null m

-- Helper functions to extract metadata

-- | Retrieve the metadata value for a given @key@.
lookupMeta :: Text -> Meta -> Maybe MetaValue
lookupMeta key (Meta m) = M.lookup key m

-- | Extract document title from metadata; works just like the old @docTitle@.
-- docTitle :: Meta -> [Inline]
-- docTitle meta =
--   case lookupMeta "title" meta of
--          Just (MetaString s)           -> [Str s]
--          Just (MetaInlines ils)        -> ils
--          Just (MetaBlocks [Plain ils]) -> ils
--          Just (MetaBlocks [Para ils])  -> ils
--          _                             -> []

-- | Extract document authors from metadata; works just like the old
-- @docAuthors@.
-- docAuthors :: Meta -> [[Inline]]
-- docAuthors meta =
--   case lookupMeta "author" meta of
--         Just (MetaString s)    -> [[Str s]]
--         Just (MetaInlines ils) -> [ils]
--         Just (MetaList   ms)   -> [ils | MetaInlines ils <- ms] ++
--                                   [ils | MetaBlocks [Plain ils] <- ms] ++
--                                   [ils | MetaBlocks [Para ils]  <- ms] ++
--                                   [[Str x] | MetaString x <- ms]
--         _                      -> []

-- | Extract date from metadata; works just like the old @docDate@.
-- docDate :: Meta -> [Inline]
-- docDate meta =
--   case lookupMeta "date" meta of
--          Just (MetaString s)           -> [Str s]
--          Just (MetaInlines ils)        -> ils
--          Just (MetaBlocks [Plain ils]) -> ils
--          Just (MetaBlocks [Para ils])  -> ils
--          _                             -> []
