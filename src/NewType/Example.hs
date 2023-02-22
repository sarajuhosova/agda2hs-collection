module NewType.Example where

newtype Indexed a = MkIndexed (Int, a)
    deriving ( Eq )
    
index :: (Int, a) -> Indexed a
index = MkIndexed
