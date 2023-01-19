{-# OPTIONS --allow-unsolved-metas #-}

module GitMediate.Conflict where

open import Haskell.Prelude
open import Lib.Identity

LineNo = Int

{-# COMPILE AGDA2HS LineNo #-}

-- data Sides a = Sides
--     { sideA :: a
--     , sideBase :: a
--     , sideB :: a
--     } deriving (Functor, Foldable, Traversable, Show, Eq, Ord, Generic1)
--     deriving Applicative via Generically1 Sides

record Sides (a : Set) : Set where
    field
        sideA : a
        sideBase : a
        sideB : a
open Sides public

instance
    iFunctorSides : Functor Sides
    iFunctorSides .fmap f record { sideA = a ; sideBase = base ; sideB = b } 
        = record { sideA = f a ; sideBase = f base ; sideB = f b }

    iApplicativeSides : Applicative Sides
    iApplicativeSides .pure x = record { sideA = x ; sideBase = x ; sideB = x }
    iApplicativeSides ._<*>_
        (record { sideA = fA ; sideBase = fBase ; sideB = fB })
        (record { sideA = xA ; sideBase = xBase ; sideB = xB })
        = (record { sideA = fA xA ; sideBase = fBase xBase ; sideB = fB xB })

    iFoldableSides : Foldable Sides
    iFoldableSides .foldMap f record { sideA = sideA ; sideBase = sideBase ; sideB = sideB } = {!   !}

{-# COMPILE AGDA2HS Sides #-}
{-# COMPILE AGDA2HS iFunctorSides #-}
{-# COMPILE AGDA2HS iApplicativeSides #-}
-- {-# COMPILE AGDA2HS iFoldableSides #-}

-- data Conflict = Conflict
--     { cMarkers   :: Sides (LineNo, String) -- The markers at the beginning of sections
--     , cMarkerEnd :: (LineNo, String)       -- The ">>>>>>>...." marker at the end of the conflict
--     , cBodies    :: Sides [String]
--     } deriving (Show)

record Conflict : Set where
    field
        cMarkers : Sides (Pair LineNo String)
        cMarkerEnd : Pair LineNo String
        cBodies : Sides (List String)
open Conflict public

{-# COMPILE AGDA2HS Conflict #-}

-- bodies :: Applicative f => (Sides [String] -> f (Sides [String])) -> Conflict -> f Conflict
-- bodies f c@Conflict{cBodies} = (\x -> c{cBodies = x}) <$> f cBodies

bodies : {{ Applicative f }} → (Sides (List String) → f (Sides (List String))) → Conflict → f Conflict
bodies f c = fmap
    (λ x → record { cMarkers = Conflict.cMarkers c; cMarkerEnd = Conflict.cMarkerEnd c; cBodies = x  })
    (f (Conflict.cBodies c))

{-# COMPILE AGDA2HS bodies #-}

-- setBodies :: (Sides [String] -> Sides [String]) -> Conflict -> Conflict
-- setBodies f = runIdentity . bodies (Identity . f)

setBodies : (Sides (List String) → Sides (List String)) → Conflict → Conflict
setBodies f = Identity.runIdentity ∘ bodies (λ x → Id (f x))

{-# COMPILE AGDA2HS setBodies #-}

-- setEachBody :: ([String] -> [String]) -> Conflict -> Conflict
-- setEachBody = setBodies . fmap

setEachBody : (List String -> List String) -> Conflict -> Conflict
setEachBody = setBodies ∘ fmap

{-# COMPILE AGDA2HS setEachBody #-}

-- setStrings :: (String -> String) -> Conflict -> Conflict
-- setStrings = setEachBody . map

setStrings : (String → String) → Conflict → Conflict
setStrings = setEachBody ∘ map

{-# COMPILE AGDA2HS setStrings #-}

-- prettyLines :: Conflict -> [String]
-- prettyLines Conflict{cMarkers, cMarkerEnd, cBodies} =
--     concat ((:) <$> (snd <$> cMarkers) <*> cBodies) <> [snd cMarkerEnd]

prettyLines : Conflict -> List String
prettyLines record { cMarkers = cMarkers ; cMarkerEnd = cMarkerEnd ; cBodies = cBodies } 
    = concat (((List._∷_) <$> (Pair.snd <$> cMarkers) <*> cBodies)) <> ((Pair.snd cMarkerEnd) ∷ [])

{-# COMPILE AGDA2HS prettyLines #-}

-- pretty :: Conflict -> String
-- pretty = unlines . prettyLines

pretty : Conflict → String
pretty = unlines ∘ prettyLines

{-# COMPILE AGDA2HS pretty #-}
