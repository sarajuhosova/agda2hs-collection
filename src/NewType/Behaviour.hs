module NewType.Behaviour ( run ) where

newtype NewFoo = NewFoo String

data DataFoo = DataFoo String

data StrictFoo = StrictFoo !String

-- case Foo undefined of Foo _ ->   ()

newFooUndefined = case NewFoo undefined of NewFoo _ -> "new"
dataFooUndefined = case DataFoo undefined of DataFoo _ -> "data"
strictFooUndefined = case StrictFoo undefined of StrictFoo _ -> "strict"

runFooUndefined = do
    putStrLn "\n--------------------------------------"
    putStrLn $ "NewFoo:    " ++ newFooUndefined
    putStrLn $ "DataFoo:   " ++ dataFooUndefined
    putStrLn $ "StrictFoo: " ++ strictFooUndefined      -- undefined
    putStrLn "--------------------------------------\n"

-- case undefined of Foo _ ->   ()

newUndefined = case undefined of NewFoo _ -> "new"
dataUndefined = case undefined of DataFoo _ -> "data"
strictUndefined = case undefined of StrictFoo _ -> "strict"

runUndefined = do
    putStrLn "\n--------------------------------------"
    putStrLn $ "NewFoo:    " ++ newUndefined
    putStrLn $ "DataFoo:   " ++ dataUndefined           -- undefined
    putStrLn $ "StrictFoo: " ++ strictUndefined         -- undefined
    putStrLn "--------------------------------------\n"

-- Foo undefined         `seq` ()

newSeqFooUndefined = NewFoo undefined `seq` "new"
dataSeqFooUndefined = DataFoo undefined `seq` "data"
strictSeqFooUndefined = StrictFoo undefined `seq` "strict"

runSeqFooUndefined = do
    putStrLn "\n--------------------------------------"
    -- putStrLn $ "NewFoo:    " ++ newSeqFooUndefined      -- undefined
    putStrLn $ "DataFoo:   " ++ dataSeqFooUndefined
    putStrLn $ "StrictFoo: " ++ strictSeqFooUndefined   -- undefined
    putStrLn "--------------------------------------\n"

-- (undefined :: Foo) `seq` ()

newSeqUndefined = (undefined :: NewFoo) `seq` "new"
dataSeqUndefined = (undefined :: DataFoo) `seq` "data"
strictSeqUndefined = (undefined :: StrictFoo) `seq` "strict"

runSeqUndefined = do
    putStrLn "\n--------------------------------------"
    -- putStrLn $ "NewFoo:    " ++ newSeqUndefined         -- undefined
    -- putStrLn $ "DataFoo:   " ++ dataSeqUndefined        -- undefined
    putStrLn $ "StrictFoo: " ++ strictSeqUndefined      -- undefined
    putStrLn "--------------------------------------\n"

run = runSeqUndefined

-- deriving

newtype Bla = MkBla Int deriving ( Eq )


