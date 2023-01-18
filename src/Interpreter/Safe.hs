module Interpreter.Safe where

import Interpreter.Lang ( Type(..), Expr(..), Val(..) )

data TExpr = TEBool Bool
           | TEInt Int
           | TEAdd TExpr TExpr
           | TEEq TExpr TExpr
           | TENot TExpr
           | TEAnd TExpr TExpr
           | TEOr TExpr TExpr
    deriving ( Eq )

data TVal = TVBool Bool
          | TVInt Int
    deriving ( Eq )

convert :: Expr -> TExpr
convert (EBool b) = TEBool b
convert (EInt i) = TEInt i
convert (EAdd left right) = TEAdd (convert left) (convert right)
convert (EEq left right) = TEEq (convert left) (convert right)
convert (ENot e) = TENot (convert e)
convert (EAnd left right) = TEAnd (convert left) (convert right)
convert (EOr left right) = TEOr (convert left) (convert right)

typedInterp :: TExpr -> TVal
typedInterp (TEBool b) = TVBool b
typedInterp (TEInt i) = TVInt i
typedInterp (TEAdd left right)
  = case (typedInterp left, typedInterp right) of
        (TVInt i, TVInt j) -> TVInt (i + j)
typedInterp (TEEq left right)
  = case (typedInterp left, typedInterp right) of
        (TVInt i, TVInt j) -> TVBool (i == j)
typedInterp (TENot e)
  = case typedInterp e of
        TVBool b -> TVBool (not b)
typedInterp (TEAnd left right)
  = case (typedInterp left, typedInterp right) of
        (TVBool a, TVBool b) -> TVBool (a && b)
typedInterp (TEOr left right)
  = case (typedInterp left, typedInterp right) of
        (TVBool a, TVBool b) -> TVBool (a || b)

simplify :: TVal -> Val
simplify (TVBool b) = VBool b
simplify (TVInt i) = VInt i

-- safeInterp :: Expr -> Maybe Val
-- safeInterp e
--   = case typeProof e of
--         Just (t , h) -> Just (simplify (typedInterp (convert e)))
--         _ -> Nothing
