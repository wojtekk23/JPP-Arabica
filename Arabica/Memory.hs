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
  -- TODO: Na razie chyba przyzwalamy na powtórzone deklaracje, chyba trzeba będzie zmienić
  varEnv <- ask
  (locEnv, loc) <- get
  -- debugMessage $ unwords [show x, show val]
  put $ (M.insert loc val locEnv, loc+1)
  pure $ M.insert x (loc, readOnly) varEnv

updateVariable :: Arabica.Abs.Ident -> Arabica.Abs.LocVal -> Arabica.Abs.InterpretingMonadIO ()
updateVariable x val = do
  varEnv <- ask
  (locEnv, lastLoc) <- get
  let addr = M.lookup x varEnv
  case addr of
    Nothing -> errorMessage $ Arabica.Abs.NoLocation x
    Just (loc, readOnly) -> do
      if readOnly then do
        errorMessage $ Arabica.Abs.ReadOnlyVariable x
      else do put $ (M.insert loc val locEnv, lastLoc)

updateForVariable :: Arabica.Abs.Ident -> Arabica.Abs.LocVal -> Arabica.Abs.InterpretingMonadIO ()
updateForVariable x val = do
  varEnv <- ask
  (locEnv, lastLoc) <- get
  let addr = M.lookup x varEnv
  case addr of
    Nothing -> errorMessage $ Arabica.Abs.NoLocation x
    Just (loc, readOnly) -> do
      if readOnly then do
        put $ (M.insert loc val locEnv, lastLoc)
      else do failure "updateForVariable for NOT read-only variable"    

readVariable :: Arabica.Abs.Ident -> Arabica.Abs.InterpretingMonadIO Arabica.Abs.LocVal
readVariable x = do
  varEnv <- ask
  (locEnv, _) <- get
  let addr = M.lookup x varEnv
  case addr of
    Nothing -> errorMessage $ Arabica.Abs.NoLocation x
    Just (loc, _) -> do
      let maybeVal = M.lookup loc locEnv
      case maybeVal of
        Nothing -> errorMessage $ Arabica.Abs.IncorrectValue x loc
        Just val -> pure val

getClosureFromCurrentEnvironment :: Arabica.Abs.VarEnv -> Arabica.Abs.InterpretingMonadIO Arabica.Abs.Closure
getClosureFromCurrentEnvironment varEnv = do
  let varKeys = M.keys varEnv
  varVals <- mapM readVariable varKeys
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