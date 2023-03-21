module FlowWitness.Playground ( main ) where

import Test.QuickCheck

-- ABS VALUE ----------------------------------

absolute :: Int -> Int
absolute i = case i < 0 of
    True  -> -i
    False -> i

propNegativeTurnsPositive :: Int -> Property
propNegativeTurnsPositive i = i < 0 ==> absolute i > 0

propAlwaysPositive :: Int -> Bool
propAlwaysPositive i = absolute i >= 0

propSameAsPrelude :: Int -> Bool
propSameAsPrelude i = absolute i == abs i

absoluteMain :: IO ()
absoluteMain = do
    quickCheck propNegativeTurnsPositive
    quickCheck propAlwaysPositive
    quickCheck propSameAsPrelude

-- TREE ---------------------------------------

-- data Tree a = Leaf | Branch a (Tree a) (Tree a)

-- size :: Tree a -> Int
-- size Leaf = 0
-- size (Branch _ left right) = 1 + size left + size right

-- height :: Tree a -> Int
-- height Leaf = 0
-- height (Branch _ left right) = 1 + max (height left) (height right)

-- propHeightSmallerThanSize :: Int -> Bool
-- propHeightSmallerThanSize i = True

-- treeMain :: IO ()
-- treeMain = do
--     quickCheck propHeightSmallerThanSize

-- MAIN ---------------------------------------

main :: IO ()
main = absoluteMain


