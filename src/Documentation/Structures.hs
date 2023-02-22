module Documentation.Structures where

-- type

type Entry = (Int, [String])

-- newtype

newtype Indexed a = MkIndexed (Int, a)

-- data

data Nat = Zero | Suc Nat

-- record

data Citation = Citation { id     :: Int
                         , author :: String
                         , title  :: String
                         , url    :: String
                         , year   :: Int
                         }
