module SearchTree.SearchTree where

import Test.QuickCheck
import Data.List

-- DATA DEFINITION ----------------------------------------

data SearchTree = Nil | Tree Int (SearchTree) (SearchTree)
    deriving ( Eq, Show )

-- METHODS ------------------------------------------------

add :: Int -> SearchTree -> SearchTree
add i Nil = Tree i Nil Nil
add i (Tree e left right)
    | i < e = Tree e (add i left) right
    | otherwise = Tree e left (add i right)

addAll :: [Int] -> SearchTree -> SearchTree
addAll xs tree = foldl (\t x -> add x t) tree xs

flatten :: SearchTree -> [Int]
flatten Nil = []
flatten (Tree e left right) = flatten left ++ [e] ++ flatten right

-- TESTING ------------------------------------------------

propAddSingleElement :: Int -> Bool
propAddSingleElement i =
  flatten (add i Nil) == [i]

propFlattenIndepentOfAddOrder :: Int -> Int -> Bool
propFlattenIndepentOfAddOrder i j = flatten (add i (add j Nil)) == flatten (add j (add i Nil))

propAddAllSorts :: [Int] -> Bool
propAddAllSorts xs = flatten (addAll xs Nil) == sort xs

main :: IO ()
main = do
    putStrLn "Checking AddSingleElement property..."
    quickCheck propAddSingleElement
    putStrLn "Checking FlattenIndepentOfAddOrder property..."
    quickCheck propFlattenIndepentOfAddOrder
    putStrLn "Checking AddAllSorts property..."
    quickCheck propAddAllSorts
