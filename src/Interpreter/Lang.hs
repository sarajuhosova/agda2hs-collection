module Interpreter.Lang
    ( Type(..)
    , Expr(..)
    , Val(..)
    ) where

------------------------------------------------------------
-- TYPES                                                  --
------------------------------------------------------------

data Type = TBool | TInt
    deriving ( Eq )

------------------------------------------------------------
-- EXPRESSIONS                                            --
------------------------------------------------------------

data Expr = EBool Bool
          | EInt Int
          | EAdd Expr Expr
          | EEq Expr Expr
          | ENot Expr
          | EAnd Expr Expr
          | EOr Expr Expr
    deriving ( Eq )

------------------------------------------------------------
-- VALUES                                                 --
------------------------------------------------------------

data Val = VBool Bool | VInt Int
    deriving ( Eq )
