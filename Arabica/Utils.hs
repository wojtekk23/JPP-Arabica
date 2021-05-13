module Arabica.Utils where

import qualified Arabica.Abs
import Control.Monad.State
import Control.Monad.Reader

import Control.Monad.Trans.Maybe
import Control.Monad.Trans.Except
import qualified Data.Map as M
import Data.Array

if' :: Bool -> a -> a -> a
if' True  x _ = x
if' False _ y = y

errorExpM :: Arabica.Abs.InterpretingMonadIO a
errorExpM = errorInterpretingMonadIO

errorInterpretingMonadIO :: Arabica.Abs.InterpretingMonadIO a
errorInterpretingMonadIO = lift $ lift $ throwE $ Arabica.Abs.StringError "ERROR"

failure :: Show a => a -> Arabica.Abs.InterpretingMonadIO b
failure x = lift $ lift $ throwE $ Arabica.Abs.StringError $ show x

errorMessage :: Arabica.Abs.Exception -> Arabica.Abs.InterpretingMonadIO a
errorMessage e = lift $ lift $ throwE e

debugMessage :: String -> Arabica.Abs.InterpretingMonadIO ()
debugMessage s = lift $ lift $ lift $ putStrLn s

defaultVal :: Arabica.Abs.Type -> Arabica.Abs.InterpretingMonadIO Arabica.Abs.LocVal
defaultVal type_ = case type_ of
  Arabica.Abs.Int -> pure $ Arabica.Abs.IntegerVal 0
  Arabica.Abs.Str -> pure $ Arabica.Abs.StringVal ""
  Arabica.Abs.Bool -> pure $ Arabica.Abs.BoolVal False
  Arabica.Abs.Array arrType -> pure $ Arabica.Abs.ArrVal arrType (array (0,0) [])
  _ -> failure "Na razie domyślne wartości mają inty, stringi, boole i tablice"

conformValType :: Arabica.Abs.LocVal -> Arabica.Abs.Type -> Bool
conformValType (Arabica.Abs.IntegerVal _) Arabica.Abs.Int = True
conformValType (Arabica.Abs.BoolVal _) Arabica.Abs.Bool = True
conformValType (Arabica.Abs.StringVal _) Arabica.Abs.Str = True
conformValType Arabica.Abs.VoidVal Arabica.Abs.Void = True
conformValType (Arabica.Abs.FunVal valType args _ _) (Arabica.Abs.Fun funType argTypes) = 
  let leftTypes = map (\(Arabica.Abs.Arg type_ _) -> type_) args in 
    (valType == funType) && (all (uncurry $ (==)) (zip leftTypes argTypes))
conformValType (Arabica.Abs.ArrVal arrType _) (Arabica.Abs.Array type_) = arrType == type_
conformValType _ _ = False

normalPass :: Arabica.Abs.InterpretingMonadIO Arabica.Abs.StmtState
normalPass = do
  varEnv <- ask
  pure $ (varEnv, Nothing, Arabica.Abs.NoLoopState)