-- Haskell module generated by the BNF converter

{-# OPTIONS_GHC -fno-warn-unused-matches #-}

module Arabica.Skel where

-- import Prelude (($), Either(..), String, (++), Show, show)
import qualified Arabica.Abs
import qualified Data.Map as M
import Arabica.Utils
import Arabica.Memory
import Data.Array
import Control.Monad.State
import Control.Monad.Reader

import Control.Monad.Trans.Maybe
import Control.Monad.Trans.Except

-- Initialize function arguments with values caclulated from given expression 
assignArgsToVals :: Arabica.Abs.VarEnv -> Arabica.Abs.BNFC'Position -> Arabica.Abs.Ident -> [Arabica.Abs.Expr] -> [Arabica.Abs.AbsArg] -> Arabica.Abs.InterpretingMonadIO Arabica.Abs.VarEnv
assignArgsToVals _ _ _ [] [] = ask
assignArgsToVals _ p ident _ [] = errorMessage $ Arabica.Abs.TooManyArgs p ident
assignArgsToVals _ p ident [] _ = errorMessage $ Arabica.Abs.NotEnoughArgs p ident
assignArgsToVals oldEnv p ident (e:es) ((Arabica.Abs.AbsArg type_ ident_):as) = do
  val <- local (const oldEnv) $ transExpr e
  newVarEnv <- newVariable False ident_ val
  local (const newVarEnv) $ assignArgsToVals oldEnv p ident es as

-- Translate program
transProgram :: Arabica.Abs.Program -> Arabica.Abs.InterpretingMonadIO ()
transProgram x = case x of
  Arabica.Abs.Program _ topdefs -> do
    runTopDefs topdefs
  where
    runTopDefs [] = pure ()
    runTopDefs (def:defs) = do
      (varEnv, _) <- transTopDef def
      local (const varEnv) $ runTopDefs defs

-- Translate top definitions
transTopDef :: Arabica.Abs.TopDef -> Arabica.Abs.InterpretingMonadIO (Arabica.Abs.VarEnv, Arabica.Abs.ReturnVal)
transTopDef x = case x of
  Arabica.Abs.FnDef p type_ ident args block -> do
    let Arabica.Abs.Ident str = ident
    let absType = transType type_
    let absArgs = map transArg args
    currEnv <- ask
    closure <- getClosureFromCurrentEnvironment p currEnv
    newVarEnv <- newVariable False ident (Arabica.Abs.FunVal absType absArgs block closure)
    if str == "main" then do
      (newestEnv, newestReturn, _) <- local (const newVarEnv) $ transBlock False block

      case newestReturn of
        Just y -> case y of
          Arabica.Abs.IntegerVal _ -> pure $ (newestEnv, newestReturn)
          z -> errorMessage $ Arabica.Abs.WrongValueReturned p ident absType $ getTypeFromVal z
        Nothing -> errorMessage $ Arabica.Abs.NoValueReturned p ident absType
    else pure $ (newVarEnv, Nothing)

-- translate Block
-- inLoop: whether the block is a part of any loop
transBlock :: Bool -> Arabica.Abs.Block -> Arabica.Abs.InterpretingMonadIO Arabica.Abs.StmtState
transBlock inLoop x = case x of
  Arabica.Abs.Block _ stmts -> do
    varEnv <- ask
    local (const varEnv) $ runStmts varEnv stmts
  where
    runStmts varEnv [] = pure $ (varEnv, Nothing, Arabica.Abs.NoLoopState)
    runStmts varEnv (stmt:stmts) = do
      (newVarEnv, retVal, loopState) <- transStmt inLoop stmt
      case retVal of
        Just x -> pure $ (newVarEnv, retVal, loopState)
        Nothing -> do
          if inLoop then do
            case loopState of
              Arabica.Abs.NoLoopState -> local (const newVarEnv) $ runStmts varEnv stmts
              _ -> pure $ (varEnv, retVal, loopState)
          else local (const newVarEnv) $ runStmts varEnv stmts

-- Translate statement
-- inLoop: whether statement is inside of any loop
transStmt :: Bool -> Arabica.Abs.Stmt -> Arabica.Abs.InterpretingMonadIO Arabica.Abs.StmtState
transStmt inLoop x = case x of
  Arabica.Abs.Empty _ -> normalPass
  Arabica.Abs.BStmt _ block -> transBlock inLoop block
  Arabica.Abs.Decl p type_ items -> do
    case items of
      [] -> normalPass
      (x:xs) -> do
        let absType = transType type_
        newVarEnv <- transItem absType False x
        local (const newVarEnv) $ transStmt inLoop (Arabica.Abs.Decl p type_ xs)
  Arabica.Abs.Ass p ident expr ->  do
    val <- transExpr expr
    updateVariable p ident val
    normalPass
  Arabica.Abs.ArrAss p ident posExpr valExpr -> do
    arrVal <- readVariable p ident
    case arrVal of
      Arabica.Abs.ArrVal type_ arr -> do
        let (lowerBound, upperBound) = bounds arr
        position <- transExpr posExpr
        case position of
          Arabica.Abs.IntegerVal pos -> do
            if pos < lowerBound || pos > upperBound then do
              errorMessage $ Arabica.Abs.IndexOutOfBounds p pos (lowerBound, upperBound) ident
            else do
              val <- transExpr valExpr
              if conformValType val type_ then do
                updateVariable p ident $ Arabica.Abs.ArrVal type_ $ arr // [(pos, val)]
                normalPass
              else errorMessage $ Arabica.Abs.ArrayAssignMismatch p ident
          _ -> errorMessage $ Arabica.Abs.IndexNotInteger p ident
      _ -> errorMessage $ Arabica.Abs.NotAnArray p ident
  Arabica.Abs.Incr p ident -> changeByOne 1 p ident
  Arabica.Abs.Decr p ident -> changeByOne (-1) p ident
  Arabica.Abs.Ret _ expr -> do
    retVal <- transExpr expr
    varEnv <- ask
    pure $ (varEnv, Just retVal, Arabica.Abs.NoLoopState)
  Arabica.Abs.VRet _ -> do
    varEnv <- ask
    pure $ (varEnv, Just Arabica.Abs.VoidVal, Arabica.Abs.NoLoopState)
  Arabica.Abs.Cond p expr stmt -> transStmt inLoop $ Arabica.Abs.CondElse p expr stmt (Arabica.Abs.Empty p)
  Arabica.Abs.CondElse _ expr stmt1 stmt2 -> do
    val <- transExpr expr
    case val of
      Arabica.Abs.BoolVal b -> transStmt inLoop $ if' b stmt1 stmt2
      Arabica.Abs.IntegerVal n -> transStmt inLoop $ if' (n /= 0) stmt1 stmt2
  Arabica.Abs.While _ expr stmt -> do
    val <- transExpr expr
    case val of
      Arabica.Abs.BoolVal b -> do
        if b then do
          (newVarEnv, retVal, loopState) <- transStmt True stmt
          case retVal of
            Just x -> pure $ (newVarEnv, retVal, loopState)
            Nothing -> do
              case loopState of
                Arabica.Abs.BreakState -> normalPass
                _ -> transStmt inLoop x
        else
          normalPass
  Arabica.Abs.Break _ -> do
    varEnv <- ask
    pure $ (varEnv, Nothing, Arabica.Abs.BreakState)
  Arabica.Abs.Continue _ -> do
    varEnv <- ask
    pure $ (varEnv, Nothing, Arabica.Abs.ContState)
  Arabica.Abs.SExp _ expr -> do
    transExpr expr
    normalPass
  Arabica.Abs.ForTo p ident expr1 expr2 stmt -> do
    val1 <- transExpr expr1
    val2 <- transExpr expr2
    if (conformValType val1 Arabica.Abs.Int) && (conformValType val2 Arabica.Abs.Int) then do
      let Arabica.Abs.IntegerVal n1 = val1
      let Arabica.Abs.IntegerVal n2 = val2
      newVarEnv <- newVariable True ident val1
      local (const newVarEnv) $ runForLoop p ident n1 n2 stmt
    else
      if not (conformValType val1 Arabica.Abs.Int) then errorMessage $ Arabica.Abs.StringError p $ unwords ["Typ pierwszej wartości w for-to się nie zgadza"]
      else errorMessage $ Arabica.Abs.StringError p $ unwords ["Typ drugiej wartości w for-to się nie zgadza"]
    where
      runForLoop p ident curr n2 stmt = do
        if curr == n2 then normalPass
        else do
          updateForVariable p ident $ Arabica.Abs.IntegerVal curr
          (newVarEnv, retVal, loopState) <- transStmt True stmt
          case retVal of
            Just x -> pure $ (newVarEnv, retVal, loopState)
            Nothing -> do
              case loopState of
                Arabica.Abs.BreakState -> normalPass
                _ -> runForLoop p ident (curr+1) n2 stmt
  Arabica.Abs.Print p expr -> do
    val <- transExpr expr
    case val of
      Arabica.Abs.IntegerVal n -> lift $ lift $ lift $ putStrLn $ show n
      Arabica.Abs.BoolVal b -> lift $ lift $ lift $ putStrLn $ show b
      Arabica.Abs.StringVal s -> lift $ lift $ lift $ putStrLn $ s
      _ -> failure p "Can only print integers, booleans and strings"
    normalPass

-- Translate item declaration
-- valType: type of the initialized variable
-- readOnly: whether the new variable is read-only or not
transItem :: Arabica.Abs.AbsType -> Bool -> Arabica.Abs.Item -> Arabica.Abs.InterpretingMonadIO Arabica.Abs.VarEnv
transItem valType readOnly x = case x of
  Arabica.Abs.NoInit p ident -> do
    val <- defaultVal valType
    newVarEnv <- newVariable readOnly ident val
    pure $ newVarEnv
  Arabica.Abs.Init _ ident expr -> do
    val <- transExpr expr
    newVarEnv <- newVariable readOnly ident val
    pure $ newVarEnv

-- translate expression
transExpr :: Arabica.Abs.Expr -> Arabica.Abs.InterpretingMonadIO Arabica.Abs.LocVal
transExpr x = case x of
  Arabica.Abs.EArray _ type_ integer -> do
    let absType = transType type_
    initVal <- defaultVal absType
    pure $ Arabica.Abs.ArrVal absType (array (0, integer-1) [(ix, initVal) | ix <- [0..integer-1]])
  Arabica.Abs.EArrElem p ident expr -> do
    val <- readVariable p ident
    pos <- transExpr expr
    case val of
      Arabica.Abs.ArrVal type_ arr -> do
        let (lowerBound, upperBound) = bounds arr
        case pos of
          Arabica.Abs.IntegerVal n -> do
            if n < lowerBound || n > upperBound then do
              errorMessage $ Arabica.Abs.IndexOutOfBounds p n (lowerBound, upperBound) ident
            else do
              pure $ arr ! n
      _ -> errorMessage $ Arabica.Abs.NotAnArray p ident
  Arabica.Abs.ELambda p type_ args block -> do
    let absType = transType type_
    let absArgs = map transArg args
    varEnv <- ask
    closure <- getClosureFromCurrentEnvironment p varEnv
    pure $ Arabica.Abs.FunVal absType absArgs block closure
  Arabica.Abs.EVar p ident -> readVariable p ident
  Arabica.Abs.ELitInt _ integer -> pure $ Arabica.Abs.IntegerVal $ integer
  Arabica.Abs.ELitTrue _ -> pure $ Arabica.Abs.BoolVal $ True
  Arabica.Abs.ELitFalse _ -> pure $ Arabica.Abs.BoolVal $ False
  Arabica.Abs.EApp p ident exprs -> do
    varEnv <- ask
    maybeFun <- readVariable p ident
    case maybeFun of
      Arabica.Abs.FunVal type_ args block closure -> do
        oldFunVarEnv <- local (const M.empty) $ assignClosureToVals closure
        funVarEnv <- local (const oldFunVarEnv) $ assignArgsToVals varEnv p ident exprs args
        newFunVarEnv <- local (const funVarEnv) $ newVariable True ident (Arabica.Abs.FunVal type_ args block closure)
        (_, retVal, _) <- local (const newFunVarEnv) $ transBlock False block
        case retVal of
          Just x -> pure x
          Nothing -> do
            case type_ of
              Arabica.Abs.Void -> pure Arabica.Abs.VoidVal
              _ -> errorMessage $ Arabica.Abs.NoValueReturned p ident type_
      _ -> errorMessage $ Arabica.Abs.NotAFunction p ident
  Arabica.Abs.EString _ string -> pure $ Arabica.Abs.StringVal $ string
  Arabica.Abs.Neg _ expr -> do
    Arabica.Abs.IntegerVal n <- transExpr expr
    pure $ Arabica.Abs.IntegerVal $ (-n)
  Arabica.Abs.Not _ expr -> do
    Arabica.Abs.BoolVal b <- transExpr expr
    pure $ Arabica.Abs.BoolVal $ not b
  Arabica.Abs.EMul _ expr1 mulop expr2 -> do
    Arabica.Abs.IntegerVal n1 <- transExpr expr1
    Arabica.Abs.IntegerVal n2 <- transExpr expr2
    transMulOp mulop n1 n2
  Arabica.Abs.EAdd _ expr1 addop expr2 -> do
    Arabica.Abs.IntegerVal n1 <- transExpr expr1
    Arabica.Abs.IntegerVal n2 <- transExpr expr2
    transAddOp addop n1 n2
  Arabica.Abs.ERel _ expr1 relop expr2 -> do
    Arabica.Abs.IntegerVal n1 <- transExpr expr1
    Arabica.Abs.IntegerVal n2 <- transExpr expr2
    transRelOp relop n1 n2
  Arabica.Abs.EAnd _ expr1 expr2 -> do
    Arabica.Abs.BoolVal b1 <- transExpr expr1
    if not b1 then pure $ Arabica.Abs.BoolVal b1
    else do
      b2 <- transExpr expr2
      pure $ b2
  Arabica.Abs.EOr _ expr1 expr2 -> do
    Arabica.Abs.BoolVal b1 <- transExpr expr1
    if b1 then pure $ Arabica.Abs.BoolVal b1
    else do
      b2 <- transExpr expr2
      pure $ b2

-- Translate add/subtract operations
-- n1, n2: two operands
transAddOp :: Arabica.Abs.AddOp -> Integer -> Integer -> Arabica.Abs.Result
transAddOp x n1 n2 = case x of
  Arabica.Abs.Plus _ -> pure $ Arabica.Abs.IntegerVal $ n1 + n2
  Arabica.Abs.Minus _ -> pure $ Arabica.Abs.IntegerVal $ n1 - n2

-- Translate multiply/divide operations
-- n1, n2: two operands
transMulOp :: Arabica.Abs.MulOp -> Integer -> Integer -> Arabica.Abs.Result
transMulOp x n1 n2 = case x of
  Arabica.Abs.Times _ -> pure $ Arabica.Abs.IntegerVal $ n1 * n2
  Arabica.Abs.Div p -> do
    if n2 == 0 then
      errorMessage $ Arabica.Abs.DivisionByZero p
    else
      pure $ Arabica.Abs.IntegerVal $ n1 `div` n2

-- Translate relations
-- n1, n2: two operands
transRelOp :: Arabica.Abs.RelOp -> Integer -> Integer -> Arabica.Abs.Result
transRelOp x n1 n2 = case x of
  Arabica.Abs.LTH _ -> pure $ Arabica.Abs.BoolVal $ n1 < n2
  Arabica.Abs.LE _ -> pure $ Arabica.Abs.BoolVal $ n1 <= n2
  Arabica.Abs.GTH _ -> pure $ Arabica.Abs.BoolVal $ n1 > n2
  Arabica.Abs.GE _ -> pure $ Arabica.Abs.BoolVal $ n1 >= n2
  Arabica.Abs.EQU _ -> pure $ Arabica.Abs.BoolVal $ n1 == n2
  Arabica.Abs.NE _ -> pure $ Arabica.Abs.BoolVal $ n1 /= n2
