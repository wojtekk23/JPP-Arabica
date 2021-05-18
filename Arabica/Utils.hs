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

failure :: Show a => Arabica.Abs.BNFC'Position -> a -> Arabica.Abs.InterpretingMonadIO b
failure p x = lift $ lift $ throwE $ Arabica.Abs.StringError p $ show x

errorMessage :: Arabica.Abs.Exception -> Arabica.Abs.InterpretingMonadIO a
errorMessage e = lift $ lift $ throwE e

debugMessage :: String -> Arabica.Abs.InterpretingMonadIO ()
debugMessage s = lift $ lift $ lift $ putStrLn s

transType :: Show a => Arabica.Abs.Type' a -> Arabica.Abs.AbsType
transType x = case x of
  Arabica.Abs.IntType _ -> Arabica.Abs.Int
  Arabica.Abs.StrTpye _ -> Arabica.Abs.Str
  Arabica.Abs.BoolType _ -> Arabica.Abs.Bool
  Arabica.Abs.VoidType _ -> Arabica.Abs.Void
  Arabica.Abs.FunType _ type_ types -> Arabica.Abs.Fun (transType type_) $ map transType types
  Arabica.Abs.ArrayType _ type_ -> Arabica.Abs.Array (transType type_)

transArg :: Show a => Arabica.Abs.Arg' a -> Arabica.Abs.AbsArg
transArg x = case x of
  Arabica.Abs.Arg _ type_ ident -> Arabica.Abs.AbsArg (transType type_) ident

defaultVal :: Arabica.Abs.AbsType -> Arabica.Abs.InterpretingMonadIO Arabica.Abs.LocVal
defaultVal type_ = case type_ of
  Arabica.Abs.Int -> pure $ Arabica.Abs.IntegerVal 0
  Arabica.Abs.Str -> pure $ Arabica.Abs.StringVal ""
  Arabica.Abs.Bool -> pure $ Arabica.Abs.BoolVal False
  Arabica.Abs.Array arrType -> pure $ Arabica.Abs.ArrVal arrType (array (0,0) [])
  _ -> failure Nothing "Na razie domyślne wartości mają inty, stringi, boole i tablice"

conformValType :: Arabica.Abs.LocVal -> Arabica.Abs.AbsType -> Bool
conformValType (Arabica.Abs.IntegerVal _) Arabica.Abs.Int = True
conformValType (Arabica.Abs.BoolVal _) Arabica.Abs.Bool = True
conformValType (Arabica.Abs.StringVal _) Arabica.Abs.Str = True
conformValType Arabica.Abs.VoidVal Arabica.Abs.Void = True
conformValType (Arabica.Abs.FunVal valType args _ _) (Arabica.Abs.Fun funType argTypes) = 
  let leftTypes = map (\(Arabica.Abs.AbsArg type_ _) -> type_) args in 
    (valType == funType) && (all (uncurry $ (==)) (zip leftTypes argTypes))
conformValType (Arabica.Abs.ArrVal arrType _) (Arabica.Abs.Array type_) = arrType == type_
conformValType _ _ = False

getTypeFromVal :: Arabica.Abs.LocVal -> Arabica.Abs.AbsType
getTypeFromVal x = case x of
  Arabica.Abs.BoolVal _ -> Arabica.Abs.Bool
  Arabica.Abs.IntegerVal _ -> Arabica.Abs.Int
  Arabica.Abs.StringVal _ -> Arabica.Abs.Str
  Arabica.Abs.VoidVal -> Arabica.Abs.Void
  Arabica.Abs.FunVal retType absArgs _ _ -> Arabica.Abs.Fun retType $ map (\(Arabica.Abs.AbsArg argType _) -> argType) absArgs
  Arabica.Abs.ArrVal arrType _ -> Arabica.Abs.Array arrType

normalPass :: Arabica.Abs.InterpretingMonadIO Arabica.Abs.StmtState
normalPass = do
  varEnv <- ask
  pure $ (varEnv, Nothing, Arabica.Abs.NoLoopState)