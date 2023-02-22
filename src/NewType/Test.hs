module NewType.Test where

newtype Foo = NewFoo Int

newtype Fool a = NewFool a

newtype Foop a b = NewFoop (a, b)
