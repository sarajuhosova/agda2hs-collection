module Ledger.Operations where

import Control.Monad.State

data Transaction = Withdraw Double
                 | Deposit Double

type Log = [Transaction]

type AccountState = (Double, Log)

applyTransaction :: Transaction -> Double -> Double
applyTransaction (Withdraw amount) = \balance -> balance - amount
applyTransaction (Deposit amount) = \balance -> balance + amount

updateAccount :: Transaction -> State AccountState ()
updateAccount transaction = do
    account <- get
    put (applyTransaction transaction (fst account), transaction : snd account)

getBalance :: State AccountState Double
getBalance = do
    account <- get
    return $ fst account
