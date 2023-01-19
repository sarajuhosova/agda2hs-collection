module Pandoc.Definition where

open import Haskell.Prelude

------------------------------------------------------------
-- IMPORTS                                                --
------------------------------------------------------------

{-# FOREIGN AGDA2HS import Data.Text (Text) #-}
postulate Text : Set

------------------------------------------------------------
-- TYPE DEFINITIONS                                       --
------------------------------------------------------------

-- type Attr = (Text, [Text], [(Text, Text)])
Attr = Tuple (Text ∷ (List Text ∷ (List (Tuple (Text ∷ (Text ∷ []))) ∷ [])))
data Format : Set
data Block : Set
data QuoteType : Set
-- type Target = (Text, Text)
Target = Tuple (Text ∷ (Text ∷ []))
data MathType : Set
data Inline : Set
record Citation : Set
data CitationMode : Set

------------------------------------------------------------
-- DATA DEFINITIONS                                       --
------------------------------------------------------------

-- newtype Format = Format Text
--                deriving (Read, Show)

data Format where
    F : Text → Format

-- data Block
--     = Plain [Inline]
--     | Para [Inline]
--     | LineBlock [[Inline]]
--     | CodeBlock Attr Text
--     | RawBlock Format Text
--     | BlockQuote [Block]
--     | BulletList [[Block]]
--     | DefinitionList [([Inline],[[Block]])]
--     | Header Int Attr [Inline]
--     | HorizontalRule
--     | Div Attr [Block]
--     deriving (Eq, Ord, Read, Show)

data Block where
    Plain : List Inline → Block
    Para : List Inline → Block
    LineBlock : List (List Inline) → Block
    CodeBlock : Attr → Text → Block
    RawBlock : Format → Text → Block
    BlockQuote : List Block → Block
    BulletList : List (List Block) → Block
    DefinitionList : List (Tuple (List Inline ∷ (List (List Block) ∷ []))) → Block
    Header : Int → Attr → List Inline → Block
    HorizontalRule : Block
    Div : Attr → List Block → Block

-- data QuoteType = SingleQuote | DoubleQuote deriving (Show, Eq, Ord, Read) 

data QuoteType where
    SingleQuote : QuoteType
    DoubleQuote : QuoteType

-- data MathType = DisplayMath | InlineMath deriving (Show, Eq, Ord, Read)

data MathType where
    DisplayMath : MathType
    InlineMath : MathType

-- data Inline
--     = Str Text            -- ^ Text (string)
--     | Emph [Inline]         -- ^ Emphasized text (list of inlines)
--     | Underline [Inline]    -- ^  Underlined text (list of inlines)
--     | Strong [Inline]       -- ^ Strongly emphasized text (list of inlines)
--     | Strikeout [Inline]    -- ^ Strikeout text (list of inlines)
--     | Superscript [Inline]  -- ^ Superscripted text (list of inlines)
--     | Subscript [Inline]    -- ^ Subscripted text (list of inlines)
--     | SmallCaps [Inline]    -- ^ Small caps text (list of inlines)
--     | Quoted QuoteType [Inline] -- ^ Quoted text (list of inlines)
--     | Cite [Citation]  [Inline] -- ^ Citation (list of inlines)
--     | Code Attr Text      -- ^ Inline code (literal)
--     | Space                 -- ^ Inter-word space
--     | SoftBreak             -- ^ Soft line break
--     | LineBreak             -- ^ Hard line break
--     | Math MathType Text  -- ^ TeX math (literal)
--     | RawInline Format Text -- ^ Raw inline
--     | Link Attr [Inline] Target  -- ^ Hyperlink: alt text (list of inlines), target
--     | Image Attr [Inline] Target -- ^ Image:  alt text (list of inlines), target
--     | Note [Block]          -- ^ Footnote or endnote
--     | Span Attr [Inline]    -- ^ Generic inline container with attributes
--     deriving (Show, Eq, Ord, Read)

data Inline where
    Str : Text → Inline
    Emph : List Inline → Inline
    Underline : List Inline → Inline
    Strong : List Inline → Inline
    Strikeout : List Inline → Inline
    Superscript : List Inline → Inline
    Subscript : List Inline → Inline
    SmallCaps : List Inline → Inline
    Quoted : QuoteType → List Inline → Inline
    Cite : List Citation → List Inline → Inline
    Code : Attr → Text → Inline
    Space : Inline
    SoftBreak : Inline
    LineBreak : Inline
    Math : MathType → Text → Inline
    RawInline : Format → Text → Inline
    Link : Attr → List Inline → Target → Inline
    Image : Attr → List Inline → Target → Inline
    Note : List Block → Inline
    Span : Attr → List Inline → Inline

-- data Citation = Citation { citationId      :: Text
--                          , citationPrefix  :: [Inline]
--                          , citationSuffix  :: [Inline]
--                          , citationMode    :: CitationMode
--                          , citationNoteNum :: Int
--                          , citationHash    :: Int
--                          }
--                 deriving (Show, Eq, Read)

record Citation where
    inductive
    field
        citationId : Text
        citationPrefix : List Inline
        citationSuffix : List Inline
        citationMode : CitationMode
        citationNoteNum : Int
        citationHash : Int

open Citation public

-- data CitationMode = AuthorInText | SuppressAuthor | NormalCitation
--                     deriving (Show, Eq, Ord, Read)

data CitationMode where
    AuthorInText : CitationMode
    SuppressAuthor : CitationMode
    NormalCitation : CitationMode


{-# COMPILE AGDA2HS Attr #-}
{-# COMPILE AGDA2HS Format #-}
{-# COMPILE AGDA2HS Block #-}
{-# COMPILE AGDA2HS QuoteType #-}
{-# COMPILE AGDA2HS Target #-}
{-# COMPILE AGDA2HS MathType #-}
{-# COMPILE AGDA2HS Inline #-}
{-# COMPILE AGDA2HS Citation #-}
{-# COMPILE AGDA2HS CitationMode #-}
