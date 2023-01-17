module Examples.Challenges where

-- Guards -----------------------------------------------------

passed :: Double -> Either String Bool
passed grade
    | grade >= 5.75 && grade <= 10   = Right True
    | grade >= 1    && grade <  5.75 = Right False
    | otherwise                      = Left "Not a valid grade!"

-- Type Class Deriving ----------------------------------------

data Tree = Leaf | Branch Int Tree Tree
    deriving ( Eq )
