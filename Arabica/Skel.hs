-- Haskell module generated by the BNF converter

{-# OPTIONS_GHC -fno-warn-unused-matches #-}

module Arabica.Skel where

-- import Prelude (($), Either(..), String, (++), Show, show)
import qualified Arabica.Abs
import qualified Data.Map as M
import Data.Array
import Control.Monad.State
import Control.Monad.Reader

import Control.Monad.Trans.Maybe
import Control.Monad.Trans.Except

-- Bool - czy zmienna jest read-only
-- type VarEnv = M.Map Arabica.Abs.Ident (Arabica.Abs.Location, Bool)
-- type LocEnv = M.Map Arabica.Abs.Location Arabica.Abs.LocVal
-- type LocMemory = (LocEnv, Arabica.Abs.Location)
-- type ExpM a = ReaderT VarEnv Maybe a
type InterpretingMonadIO = ReaderT Arabica.Abs.VarEnv (StateT Arabica.Abs.LocMemory (ExceptT Arabica.Abs.Exception IO))

type Err = Either String
type Result = InterpretingMonadIO Arabica.Abs.LocVal

type StmtState = (Arabica.Abs.VarEnv, Arabica.Abs.ReturnVal, Arabica.Abs.LoopState)

if' :: Bool -> a -> a -> a
if' True  x _ = x
if' False _ y = y

errorExpM :: InterpretingMonadIO a
errorExpM = errorInterpretingMonadIO

errorInterpretingMonadIO :: InterpretingMonadIO a
errorInterpretingMonadIO = lift $ lift $ throwE $ Arabica.Abs.StringError "ERROR"

failure :: Show a => a -> InterpretingMonadIO b
-- failure x = Left $ "Undefined case: " ++ show x
failure x = lift $ lift $ throwE $ Arabica.Abs.StringError $ show x

errorMessage :: Arabica.Abs.Exception -> InterpretingMonadIO a
errorMessage e = lift $ lift $ throwE e

debugMessage :: String -> InterpretingMonadIO ()
debugMessage s = lift $ lift $ lift $ putStrLn s

-- Is new variable readonly?
newVariable :: Bool -> Arabica.Abs.Ident -> Arabica.Abs.LocVal -> InterpretingMonadIO Arabica.Abs.VarEnv
newVariable readOnly x val = do
  -- TODO: Na razie chyba przyzwalamy na powtórzone deklaracje, chyba trzeba będzie zmienić
  varEnv <- ask
  (locEnv, loc) <- get
  -- debugMessage $ unwords [show x, show val]
  put $ (M.insert loc val locEnv, loc+1)
  pure $ M.insert x (loc, readOnly) varEnv

updateVariable :: Arabica.Abs.Ident -> Arabica.Abs.LocVal -> InterpretingMonadIO ()
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

updateForVariable :: Arabica.Abs.Ident -> Arabica.Abs.LocVal -> InterpretingMonadIO ()
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

readVariable :: Arabica.Abs.Ident -> InterpretingMonadIO Arabica.Abs.LocVal
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

transIdent :: Arabica.Abs.Ident -> InterpretingMonadIO ()
transIdent x = case x of
  Arabica.Abs.Ident string -> failure x

transProgram :: Arabica.Abs.Program -> InterpretingMonadIO ()
transProgram x = case x of
  Arabica.Abs.Program topdefs -> do
    runTopDefs topdefs
  where
    runTopDefs [] = pure ()
    runTopDefs (def:defs) = do
      -- Czy powinniśmy przejmować się zwracaną wartością?
      (varEnv, _) <- transTopDef def
      local (const varEnv) $ runTopDefs defs

transTopDef :: Arabica.Abs.TopDef -> InterpretingMonadIO (Arabica.Abs.VarEnv, Arabica.Abs.ReturnVal)
transTopDef x = case x of
  Arabica.Abs.FnDef type_ ident args block -> do
    -- Na razie tylko uruchamiaj main
    let Arabica.Abs.Ident str = ident
    newVarEnv <- newVariable False ident (Arabica.Abs.FunVal type_ args block M.empty)
    if str == "main" then  do
      (newestEnv, newestReturn, _) <- local (const newVarEnv) $ transBlock False block
      pure $ (newestEnv, newestReturn)
    else pure $ (newVarEnv, Nothing)

transArg :: Arabica.Abs.Arg -> InterpretingMonadIO ()
transArg x = case x of
  Arabica.Abs.Arg type_ ident -> failure x

noPass :: InterpretingMonadIO StmtState
noPass = do
  varEnv <- ask
  pure $ (varEnv, Nothing, Arabica.Abs.NoLoopState)

transBlock :: Bool -> Arabica.Abs.Block -> InterpretingMonadIO StmtState
transBlock inLoop x = case x of
  Arabica.Abs.Block stmts -> runStmts stmts
  where
    runStmts [] = noPass
    runStmts (stmt:stmts) = do
      -- env <- ask
      -- (locEnv, _) <- get
      -- debugMessage $ unwords ["VARS", show env]
      -- debugMessage $ unwords ["LOCS", show locEnv]
      -- debugMessage $ unwords ["STATEMENT", show stmt]
      (newVarEnv, retVal, loopState) <- transStmt inLoop stmt
      case retVal of
        Just x -> pure $ (newVarEnv, retVal, loopState)
        Nothing -> do
          if inLoop then do
            case loopState of
              Arabica.Abs.NoLoopState -> local (const newVarEnv) $ runStmts stmts
              _ -> pure $ (newVarEnv, retVal, loopState)
          else local (const newVarEnv) $ runStmts stmts

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

-- Bool - czy jesteśmy w pętli
transStmt :: Bool -> Arabica.Abs.Stmt -> InterpretingMonadIO StmtState
transStmt inLoop x = case x of
  Arabica.Abs.Empty -> noPass
  Arabica.Abs.BStmt block -> transBlock inLoop block
  Arabica.Abs.Decl type_ items -> do
    -- Na razie tylko int
    case items of
      [] -> noPass
      (x:xs) -> do
        -- debugMessage $ unwords ["DECL", show (x:xs)]
        newVarEnv <- transItem False x
        local (const newVarEnv) $ transStmt inLoop (Arabica.Abs.Decl type_ xs)
  Arabica.Abs.Ass ident expr -> do
    -- env <- get
    -- let locVal = runReaderT (transExpr expr) env
    -- case locVal of
    --   Nothing -> errorInterpretingMonadIO
    --   Just x -> updateVariable ident x
    val <- transExpr expr
    updateVariable ident val
    noPass
  Arabica.Abs.ArrAss ident posExpr valExpr -> do
    arrVal <- readVariable ident
    case arrVal of
      Arabica.Abs.ArrVal type_ arr -> do
        let (lowerBound, upperBound) = bounds arr
        position <- transExpr posExpr
        case position of
          Arabica.Abs.IntegerVal pos -> do
            if pos < lowerBound || pos > upperBound then do
              errorMessage $ Arabica.Abs.IndexOutOfBounds pos (lowerBound, upperBound) ident
            else do
              val <- transExpr valExpr
              if conformValType val type_ then do
                updateVariable ident $ Arabica.Abs.ArrVal type_ $ arr // [(pos, val)]
                noPass
              else errorMessage $ Arabica.Abs.ArrayAssignMismatch ident
          _ -> errorMessage $ Arabica.Abs.IndexNotInteger ident
      _ -> errorMessage $ Arabica.Abs.NotAnArray ident
  Arabica.Abs.Incr ident -> failure "Incr"
  Arabica.Abs.Decr ident -> failure "Decr"
  Arabica.Abs.Ret expr -> do
    retVal <- transExpr expr
    varEnv <- ask
    pure $ (varEnv, Just retVal, Arabica.Abs.NoLoopState)
  Arabica.Abs.VRet -> do
    varEnv <- ask
    pure $ (varEnv, Just Arabica.Abs.VoidVal, Arabica.Abs.NoLoopState)
  Arabica.Abs.Cond expr stmt -> transStmt inLoop $ Arabica.Abs.CondElse expr stmt Arabica.Abs.Empty
  Arabica.Abs.CondElse expr stmt1 stmt2 -> do
    val <- transExpr expr
    -- Akceptujemy tylko inty i boole
    case val of
      Arabica.Abs.BoolVal b -> transStmt inLoop $ if' b stmt1 stmt2
      Arabica.Abs.IntegerVal n -> transStmt inLoop $ if' (n /= 0) stmt1 stmt2
  Arabica.Abs.While expr stmt -> do
    val <- transExpr expr
    -- TODO: Napisz to bez powtórzeń
    case val of
      Arabica.Abs.BoolVal b -> do
        if b then do
          (newVarEnv, retVal, loopState) <- transStmt True stmt
          case retVal of
            Just x -> pure $ (newVarEnv, retVal, loopState)
            Nothing -> do
              case loopState of
                Arabica.Abs.BreakState -> noPass
                -- TODO: Czy tutaj inLoop czy może True? A może False xdd
                _ -> transStmt inLoop x
        else
          noPass
      Arabica.Abs.IntegerVal n -> do
        if n /= 0 then do
          (newVarEnv, retVal, loopState) <- transStmt True stmt
          case retVal of
            Just x -> pure $ (newVarEnv, retVal, loopState)
            Nothing -> do
              case loopState of
                Arabica.Abs.BreakState -> noPass
                -- TODO: Czy tutaj inLoop czy może True? A może False xdd
                _ -> transStmt inLoop x
        else
          noPass
      _ -> failure "while"
  Arabica.Abs.Break -> do
    varEnv <- ask
    pure $ (varEnv, Nothing, Arabica.Abs.BreakState)
  Arabica.Abs.Continue -> do
    varEnv <- ask
    pure $ (varEnv, Nothing, Arabica.Abs.ContState)
  Arabica.Abs.SExp expr -> do
    transExpr expr
    noPass
  Arabica.Abs.ForTo ident expr1 expr2 stmt -> do
    -- transItem True item
    -- val <- transExpr expr
    -- TODO: NIE DZIAŁA RETURN W PĘTLACH!!!!
    val1 <- transExpr expr1
    val2 <- transExpr expr2
    if (conformValType val1 Arabica.Abs.Int) && (conformValType val2 Arabica.Abs.Int) then do
      let Arabica.Abs.IntegerVal n1 = val1
      let Arabica.Abs.IntegerVal n2 = val2
      newVarEnv <- newVariable True ident val1
      local (const newVarEnv) $ runForLoop ident n1 n2 stmt
    else
      failure "ForTo"
    where
      runForLoop ident curr n2 stmt = do
        if curr == n2 then noPass
        else do
          updateForVariable ident $ Arabica.Abs.IntegerVal curr
          (newVarEnv, retVal, loopState) <- transStmt True stmt
          case retVal of
            Just x -> pure $ (newVarEnv, retVal, loopState)
            Nothing -> do
              case loopState of
                Arabica.Abs.BreakState -> noPass
                _ -> runForLoop ident (curr+1) n2 stmt
  Arabica.Abs.Print expr -> do
    -- Na razie tylko inty
    val <- transExpr expr
    case val of
      Arabica.Abs.IntegerVal n -> lift $ lift $ lift $ putStrLn $ show n
      Arabica.Abs.BoolVal b -> lift $ lift $ lift $ putStrLn $ show b
      Arabica.Abs.StringVal s -> lift $ lift $ lift $ putStrLn $ show s
      _ -> failure "Can only print integers, booleans and strings"
    noPass

-- Bool - readonly?
transItem :: Bool -> Arabica.Abs.Item -> InterpretingMonadIO Arabica.Abs.VarEnv
transItem readOnly x = case x of
  Arabica.Abs.NoInit ident -> failure "NoInit"
  Arabica.Abs.Init ident expr -> do
    val <- transExpr expr
    newVarEnv <- newVariable readOnly ident val
    -- debugMessage "INIT"
    pure $ newVarEnv

transType :: Arabica.Abs.Type -> InterpretingMonadIO ()
transType x = case x of
  Arabica.Abs.Int -> failure x
  Arabica.Abs.Str -> failure x
  Arabica.Abs.Bool -> failure x
  Arabica.Abs.Void -> failure x
  Arabica.Abs.Fun type_ types -> failure x
  Arabica.Abs.Array type_ -> failure x

assignArgsToVals :: Arabica.Abs.Ident -> [Arabica.Abs.Expr] -> [Arabica.Abs.Arg] -> Arabica.Abs.VarEnv -> InterpretingMonadIO Arabica.Abs.VarEnv
assignArgsToVals _ [] [] env = pure env
assignArgsToVals ident _ [] _ = errorMessage $ Arabica.Abs.TooManyArgs ident
assignArgsToVals ident [] _ _ = errorMessage $ Arabica.Abs.NotEnoughArgs ident
assignArgsToVals ident (e:es) ((Arabica.Abs.Arg type_ ident_):as) _ = do
  val <- transExpr e
  newVarEnv <- newVariable False ident_ val
  assignArgsToVals ident es as newVarEnv

defaultVal :: Arabica.Abs.Type -> InterpretingMonadIO Arabica.Abs.LocVal
defaultVal type_ = case type_ of
  Arabica.Abs.Int -> pure $ Arabica.Abs.IntegerVal 0
  Arabica.Abs.Str -> pure $ Arabica.Abs.StringVal ""
  Arabica.Abs.Bool -> pure $ Arabica.Abs.BoolVal False
  Arabica.Abs.Array arrType -> pure $ Arabica.Abs.ArrVal arrType (array (0,0) [])
  _ -> failure "Na razie domyślne wartości mają inty, stringi, boole i tablice"

transExpr :: Arabica.Abs.Expr -> InterpretingMonadIO Arabica.Abs.LocVal
transExpr x = case x of
  Arabica.Abs.EArray type_ integer -> do
    initVal <- defaultVal type_
    pure $ Arabica.Abs.ArrVal type_ (array (0, integer-1) [(ix, initVal) | ix <- [0..integer-1]])
  Arabica.Abs.EArrElem ident expr -> do
    val <- readVariable ident
    pos <- transExpr expr
    case val of
      Arabica.Abs.ArrVal type_ arr -> do
        let (lowerBound, upperBound) = bounds arr
        case pos of
          Arabica.Abs.IntegerVal n -> do
            if n < lowerBound || n > upperBound then do
              errorMessage $ Arabica.Abs.IndexOutOfBounds n (lowerBound, upperBound) ident
            else do
              pure $ arr ! n
      _ -> errorMessage $ Arabica.Abs.NotAnArray ident
  Arabica.Abs.ELambda type_ args block -> failure "Lambda"
  Arabica.Abs.EVar ident -> readVariable ident
  Arabica.Abs.ELitInt integer -> pure $ Arabica.Abs.IntegerVal $ integer
  Arabica.Abs.ELitTrue -> pure $ Arabica.Abs.BoolVal $ True
  Arabica.Abs.ELitFalse -> pure $ Arabica.Abs.BoolVal $ False
  Arabica.Abs.EApp ident exprs -> do
    varEnv <- ask
    maybeFun <- readVariable ident
    case maybeFun of
      -- TODO: closures
      Arabica.Abs.FunVal type_ args block closure -> do
        -- TODO: przyzwala na pozyskiwanie zmiennych z środowiska funkcji wywołującej, trzeba to zmienić
        -- i dodać rozróżnienie na funkcje i lambdy (ewentulanie dodać do FunVal środowisko)
        funVarEnv <- assignArgsToVals ident exprs args varEnv
        (_, retVal, _) <- local (const funVarEnv) $ transBlock False block
        case retVal of
          Just x -> pure x
          Nothing -> do
            case type_ of
              Arabica.Abs.Void -> pure Arabica.Abs.VoidVal
              _ -> errorMessage $ Arabica.Abs.NoValueReturned ident type_
      _ -> errorMessage $ Arabica.Abs.NotAFunction ident
  Arabica.Abs.EString string -> pure $ Arabica.Abs.StringVal $ string
  Arabica.Abs.Neg expr -> do
    Arabica.Abs.IntegerVal n <- transExpr expr
    pure $ Arabica.Abs.IntegerVal $ (-n)
  Arabica.Abs.Not expr -> do
    Arabica.Abs.BoolVal b <- transExpr expr
    pure $ Arabica.Abs.BoolVal $ not b
  Arabica.Abs.EMul expr1 mulop expr2 -> do
    Arabica.Abs.IntegerVal n1 <- transExpr expr1
    Arabica.Abs.IntegerVal n2 <- transExpr expr2
    transMulOp mulop n1 n2
  Arabica.Abs.EAdd expr1 addop expr2 -> do
    Arabica.Abs.IntegerVal n1 <- transExpr expr1
    Arabica.Abs.IntegerVal n2 <- transExpr expr2
    transAddOp addop n1 n2
  Arabica.Abs.ERel expr1 relop expr2 -> do
    Arabica.Abs.IntegerVal n1 <- transExpr expr1
    Arabica.Abs.IntegerVal n2 <- transExpr expr2
    transRelOp relop n1 n2
  Arabica.Abs.EAnd expr1 expr2 -> do
    Arabica.Abs.BoolVal b1 <- transExpr expr1
    Arabica.Abs.BoolVal b2 <- transExpr expr2
    pure $ Arabica.Abs.BoolVal $ b1 && b2
  Arabica.Abs.EOr expr1 expr2 -> do
    Arabica.Abs.BoolVal b1 <- transExpr expr1
    Arabica.Abs.BoolVal b2 <- transExpr expr2
    pure $ Arabica.Abs.BoolVal $ b1 || b2

transAddOp :: Arabica.Abs.AddOp -> Integer -> Integer -> Result
transAddOp x n1 n2 = case x of
  Arabica.Abs.Plus -> pure $ Arabica.Abs.IntegerVal $ n1 + n2
  Arabica.Abs.Minus -> pure $ Arabica.Abs.IntegerVal $ n1 - n2

transMulOp :: Arabica.Abs.MulOp -> Integer -> Integer -> Result
transMulOp x n1 n2 = case x of
  Arabica.Abs.Times -> pure $ Arabica.Abs.IntegerVal $ n1 * n2
  Arabica.Abs.Div -> do
    if n2 == 0 then
      errorMessage $ Arabica.Abs.DivisionByZero
    else
      pure $ Arabica.Abs.IntegerVal $ n1 `div` n2

transRelOp :: Arabica.Abs.RelOp -> Integer -> Integer -> Result
transRelOp x n1 n2 = case x of
  Arabica.Abs.LTH -> pure $ Arabica.Abs.BoolVal $ n1 < n2
  Arabica.Abs.LE -> pure $ Arabica.Abs.BoolVal $ n1 <= n2
  Arabica.Abs.GTH -> pure $ Arabica.Abs.BoolVal $ n1 > n2
  Arabica.Abs.GE -> pure $ Arabica.Abs.BoolVal $ n1 >= n2
  Arabica.Abs.EQU -> pure $ Arabica.Abs.BoolVal $ n1 == n2
  Arabica.Abs.NE -> pure $ Arabica.Abs.BoolVal $ n1 /= n2
