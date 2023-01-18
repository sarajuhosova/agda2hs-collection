module Interpreter.Interp ( interp, typeOf ) where

import Interpreter.Lang ( Type(..), Expr(..), Val(..) )

------------------------------------------------------------
-- DIRECT INTERPRETER                                     --
------------------------------------------------------------

interp :: Expr -> Maybe Val
interp (EBool b) = Just (VBool b)
interp (EInt i) = Just (VInt i)
interp (EAdd left right) =
    case (interp left, interp right) of
        (Just (VInt i), Just (VInt j)) -> Just (VInt (i + j))
        _ -> Nothing
interp (EEq left right) =
    case (interp left, interp right) of
        (Just (VInt i), Just (VInt j)) -> Just (VBool (i == j))
        _ -> Nothing
interp (ENot e) =
    case interp e of
        (Just (VBool b)) -> Just (VBool (not b))
        _ -> Nothing
interp (EAnd left right) =
    case (interp left, interp right) of
        (Just (VBool a), Just (VBool b)) -> Just (VBool (a && b))
        _ -> Nothing
interp (EOr left right) =
    case (interp left, interp right) of
        (Just (VBool a), Just (VBool b)) -> Just (VBool (a || b))
        _ -> Nothing

------------------------------------------------------------
-- SIMPLE TYPE CHECKER                                    --
------------------------------------------------------------

typeOf :: Expr -> Maybe Type
typeOf (EBool _) = Just TBool
typeOf (EInt _) = Just TInt
typeOf (EAdd left right) =
    case (typeOf left, typeOf right) of
        (Just TInt, Just TInt) -> Just TInt
        _ -> Nothing
typeOf (EEq left right) =
    case (typeOf left, typeOf right) of
        (Just TInt, Just TInt) -> Just TBool
        _ -> Nothing
typeOf (ENot e) =
    case typeOf e of
        (Just TBool) -> Just TBool
        _ -> Nothing
typeOf (EAnd left right) =
    case (typeOf left, typeOf right) of
        (Just TBool, Just TBool) -> Just TBool
        _ -> Nothing
typeOf (EOr left right) =
    case (typeOf left, typeOf right) of
        (Just TBool, Just TBool) -> Just TBool
        _ -> Nothing
