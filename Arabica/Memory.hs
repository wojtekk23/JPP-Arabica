module Arabica.Memory where

import qualified Arabica.Abs
import Arabica.Utils
import qualified Data.Map as M
import Control.Monad.State
import Control.Monad.Reader

import Control.Monad.Trans.Maybe
import Control.Monad.Trans.Except

-- Is new variable readonly?
newVariable :: Bool -> Arabica.Abs.Ident -> Arabica.Abs.LocVal -> Arabica.Abs.InterpretingMonadIO Arabica.Abs.VarEnv
newVariable readOnly x val = do
  varEnv <- ask
  (locEnv, loc) <- get
  put $ (M.insert loc val locEnv, loc+1)
  pure $ M.insert x (loc, readOnly) varEnv

updateVariable :: Arabica.Abs.BNFC'Position -> Arabica.Abs.Ident -> Arabica.Abs.LocVal -> Arabica.Abs.InterpretingMonadIO ()
updateVariable p x val = do
  varEnv <- ask
  (locEnv, lastLoc) <- get
  let addr = M.lookup x varEnv
  case addr of
    Nothing -> errorMessage $ Arabica.Abs.NoLocation p x
    Just (loc, readOnly) -> do
      if readOnly then do
        errorMessage $ Arabica.Abs.ReadOnlyVariable p x
      else do put $ (M.insert loc val locEnv, lastLoc)

updateForVariable :: Arabica.Abs.BNFC'Position -> Arabica.Abs.Ident -> Arabica.Abs.LocVal -> Arabica.Abs.InterpretingMonadIO ()
updateForVariable p x val = do
  varEnv <- ask
  (locEnv, lastLoc) <- get
  let addr = M.lookup x varEnv
  case addr of
    Nothing -> errorMessage $ Arabica.Abs.NoLocation p x
    Just (loc, readOnly) -> do
      if readOnly then do
        put $ (M.insert loc val locEnv, lastLoc)
      else do failure p "updateForVariable for NOT read-only variable"    

readVariable :: Arabica.Abs.BNFC'Position -> Arabica.Abs.Ident -> Arabica.Abs.InterpretingMonadIO Arabica.Abs.LocVal
readVariable p x = do
  varEnv <- ask
  (locEnv, _) <- get
  let addr = M.lookup x varEnv
  case addr of
    Nothing -> errorMessage $ Arabica.Abs.NoLocation p x
    Just (loc, _) -> do
      let maybeVal = M.lookup loc locEnv
      case maybeVal of
        Nothing -> errorMessage $ Arabica.Abs.IncorrectValue p x loc
        Just val -> pure val

changeByOne :: Integer -> Arabica.Abs.BNFC'Position -> Arabica.Abs.Ident -> Arabica.Abs.InterpretingMonadIO Arabica.Abs.StmtState
changeByOne n p ident = do
  val <- readVariable p ident
  case val of
    Arabica.Abs.IntegerVal m -> do
      updateVariable p ident $ Arabica.Abs.IntegerVal (m+n)
      normalPass
    _ -> errorMessage $ Arabica.Abs.StringError p $ unwords ["Tried to in/decrement variable", show ident, "but it is not an integer"]

getClosureFromCurrentEnvironment :: Arabica.Abs.BNFC'Position -> Arabica.Abs.VarEnv -> Arabica.Abs.InterpretingMonadIO Arabica.Abs.Closure
getClosureFromCurrentEnvironment p varEnv = do
  let varKeys = M.keys varEnv
  varVals <- mapM (readVariable p) varKeys
  pure $ M.fromList $ zip varKeys varVals

assignClosureToVals :: Arabica.Abs.Closure -> Arabica.Abs.InterpretingMonadIO Arabica.Abs.VarEnv
assignClosureToVals closure = do
  let keyValPairs = M.toList closure
  getUpdatedEnv keyValPairs
  where
    getUpdatedEnv [] = ask
    getUpdatedEnv ((key, val):pairs) = do
    newVarEnv <- newVariable False key val
    local (const newVarEnv) $ getUpdatedEnv pairs