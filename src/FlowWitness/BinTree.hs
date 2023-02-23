module FlowWitness.BinTree ( main ) where

import Test.QuickCheck

data BinTree = Leaf | Branch Int BinTree BinTree

add :: Int -> BinTree -> BinTree
add i Leaf = Branch i Leaf Leaf
add i t@(Branch x left right) =
    case i < x of
        True -> Branch x (add i left) right
        False -> case i == x of
            True -> t
            False -> Branch x left (add i right)

addAll :: [Int] -> BinTree -> BinTree
addAll xs tree = foldl (\t x -> add x t) tree xs

flatten :: BinTree -> [Int]
flatten Leaf = []
flatten (Branch x left right) = flatten left ++ [x] ++ flatten right

isSorted :: [Int] -> Bool
isSorted [] = True
isSorted [x] = True
isSorted (x:y:xs) = x <= y && isSorted (y:xs)

propAlwaysSorted :: [Int] -> Bool
propAlwaysSorted is = isSorted (flatten (addAll is Leaf))

noneMatch :: (Int -> Bool) -> [Int] -> Bool
noneMatch _ [] = True
noneMatch f (x:xs) = if f x then False else noneMatch f xs

noDuplicates :: [Int] -> Bool
noDuplicates [] = True
noDuplicates [x] = True
noDuplicates (x:xs) = noneMatch (\i -> i == x) xs && noDuplicates xs

propNoDuplicates :: [Int] -> Bool
propNoDuplicates is = noDuplicates (flatten (addAll is Leaf))

main :: IO ()
main = do
    quickCheck propAlwaysSorted
    quickCheck propNoDuplicates