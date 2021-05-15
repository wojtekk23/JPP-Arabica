module Arabica.TypeCheck where

import qualified Arabica.Abs
import qualified Data.Map as M
import Control.Monad.Reader
import Control.Monad.Trans.Except

getArgType (Arabica.Abs.Arg type_ ident) = pure $ type_
getTopDefType (Arabica.Abs.FnDef type_ ident args block) = do
  argTypes <- mapM getArgType args
  pure $ Arabica.Abs.Fun type_ argTypes
getLambdaType (Arabica.Abs.ELambda type_ args block) = do
  argTypes <- mapM getArgType args
  pure $ Arabica.Abs.Fun type_ argTypes

typeError :: Show a => a -> Arabica.Abs.TypeCheckingMonadIO b
typeError x = lift $ throwE $ Arabica.Abs.CustomTypeError $ show x

typeCheckProgram :: Arabica.Abs.Program -> Arabica.Abs.TypeCheckingMonadIO ()
typeCheckProgram x = case x of
  Arabica.Abs.Program topdefs -> do
    checkTopDefs topdefs
  where
    checkTopDefs [] = pure ()
    checkTopDefs (topdef:topdefs) = do
      let Arabica.Abs.FnDef _ ident _ _ = topdef
      typeTopDef topdef
      fnType <- getTopDefType topdef
      -- lift $ lift $ putStrLn $ unwords ["fnType", show fnType]
      local (M.insert ident fnType) $ checkTopDefs topdefs

typeTopDef :: Arabica.Abs.TopDef -> Arabica.Abs.TypeCheckingMonadIO ()
typeTopDef x = case x of
  Arabica.Abs.FnDef type_ ident args block -> do
    let Arabica.Abs.Ident name = ident
    if name == "main" && (type_ /= Arabica.Abs.Int || length args /= 0) then do
      typeError $ unwords ["Main function should have a return type int and take no arguments"]
    else do
      typeEnv <- ask
      topDefType <- getTopDefType x
      let argsTypeEnv = foldl (\env (argType, argIdent) -> M.insert argIdent argType env) typeEnv $ map (\(Arabica.Abs.Arg argType argIdent) -> (argType, argIdent)) args
      let newTypeEnv = M.insert ident topDefType argsTypeEnv
      local (const newTypeEnv) $ typeBlock type_ block

typeBlock :: Arabica.Abs.Type -> Arabica.Abs.Block -> Arabica.Abs.TypeCheckingMonadIO ()
typeBlock retType x = case x of
  Arabica.Abs.Block stmts -> runTypeStmts retType stmts
  where
    runTypeStmts :: Arabica.Abs.Type -> [Arabica.Abs.Stmt] -> Arabica.Abs.TypeCheckingMonadIO ()
    runTypeStmts type_ [] = pure ()
    runTypeStmts type_ (stmt:stmts) = do
      newEnv <- typeStmts type_ stmt
      local (const newEnv) $ runTypeStmts type_ stmts

typeItem :: Arabica.Abs.Type -> Arabica.Abs.Item -> Arabica.Abs.TypeCheckingMonadIO Arabica.Abs.Ident
typeItem itemType x = case x of
  Arabica.Abs.NoInit ident -> pure ident
  Arabica.Abs.Init ident expr -> do
    exprType <- typeExpr expr
    if exprType == itemType then pure ident
    else typeError $ unwords ["Variable", show ident, "is of type", show itemType, "but was initialized with type", show exprType]

typeStmts :: Arabica.Abs.Type -> Arabica.Abs.Stmt -> Arabica.Abs.TypeCheckingMonadIO Arabica.Abs.TypeEnv
typeStmts fnType x = case x of
  Arabica.Abs.Empty -> ask
  Arabica.Abs.BStmt block -> do
    typeBlock fnType block
    ask
  Arabica.Abs.Decl type_ items -> do
    varIdents <- mapM (typeItem type_) items
    typeEnv <- ask
    let newTypeEnv = foldl (\env ident -> M.insert ident type_ env) typeEnv varIdents
    pure newTypeEnv
  Arabica.Abs.Ass ident expr -> do
    typeEnv <- ask
    let maybeVar = M.lookup ident typeEnv
    case maybeVar of
      Nothing -> typeError $ unwords ["No identifier", "\"" ++ show ident ++ "\"", "was found"]
      Just varType -> do
        exprType <- typeExpr expr
        if exprType == varType then ask
        else typeError $ unwords ["Type of an expression", show expr, "and type of variable", show ident, "do not match"]
  Arabica.Abs.ArrAss ident indexExpr valExpr -> do
    typeEnv <- ask
    let maybeArr = M.lookup ident typeEnv
    case maybeArr of
      Nothing -> typeError $ unwords ["No identifier", "\"" ++ show ident ++ "\"", "was found"]
      Just arrType -> case arrType of
        Arabica.Abs.Array arrType -> do
          indexType <- typeExpr indexExpr
          case indexType of
            Arabica.Abs.Int -> do
              valType <- typeExpr valExpr
              if valType == arrType then ask
              else typeError $ unwords ["Type of an expression", show valExpr, "and type of array", show ident, "do not match"]
            _ -> typeError $ unwords ["Array", "\"" ++ show ident ++ "\"", "can only be accessed with an integer"]
        _ -> typeError $ unwords ["Variable", "\"" ++ show ident ++ "\"", "is not an array"]
  Arabica.Abs.Incr ident -> do
    valType <- typeExpr $ Arabica.Abs.EVar ident
    case valType of
      Arabica.Abs.Int -> ask
      _ -> typeError $ unwords ["Variable", show x, "cannot be incremented because it is not an integer"]
  Arabica.Abs.Decr ident -> do
    valType <- typeExpr $ Arabica.Abs.EVar ident
    case valType of
      Arabica.Abs.Int -> ask
      _ -> typeError $ unwords ["Variable", show x, "cannot be decremented because it is not an integer"]
  Arabica.Abs.Ret expr -> do
    exprType <- typeExpr expr
    if exprType == fnType then ask
    else typeError $ unwords ["Function is of type", show fnType, "but it contains a statement returning type", show exprType]
  Arabica.Abs.VRet -> do
    if fnType == Arabica.Abs.Void then ask
    else typeError $ unwords ["Function is of type", show fnType, "but it contains a void return statement"]
  Arabica.Abs.Cond expr stmt -> typeStmts fnType $ Arabica.Abs.CondElse expr stmt $ Arabica.Abs.Empty
  Arabica.Abs.CondElse expr stmt1 stmt2 -> do
    condType <- typeExpr expr
    if condType /= Arabica.Abs.Bool && condType /= Arabica.Abs.Int then
      typeError $ unwords ["Condition is of type", show condType, "but it has to either a boolean or integer value"]
    else do
      typeStmts fnType stmt1
      typeStmts fnType stmt2
      ask
  Arabica.Abs.While expr stmt -> do
    condType <- typeExpr expr
    if condType /= Arabica.Abs.Bool && condType /= Arabica.Abs.Int then
      typeError $ unwords ["Condition is of type", show condType, "but it has to either a boolean or integer value"]
    else do
      typeStmts fnType stmt
      ask
  Arabica.Abs.Break -> ask
  Arabica.Abs.Continue -> ask
  Arabica.Abs.SExp expr -> do
    typeExpr expr
    ask
  Arabica.Abs.ForTo ident expr1 expr2 stmt -> do
    beginType <- typeExpr expr1
    case beginType of
      Arabica.Abs.Int -> do
        endType <- typeExpr expr2
        case endType of
          Arabica.Abs.Int -> do
            local (M.insert ident Arabica.Abs.Int) $ typeStmts fnType stmt
            ask
          _ -> typeError $ unwords ["End expression in for loop should be of type Int"]
      _ -> typeError $ unwords ["Begin expression in for loop should be of type Int"]
  Arabica.Abs.Print expr -> do
    typeExpr expr
    ask

confirmTypes :: Arabica.Abs.Ident -> Integer -> [Arabica.Abs.Type] -> [Arabica.Abs.Type] -> Arabica.Abs.TypeCheckingMonadIO ()
confirmTypes _ _ [] [] = pure ()
confirmTypes ident _ _ [] = typeError $ unwords ["Too many arguments given to a function", show ident]
confirmTypes ident _ [] _ = typeError $ unwords ["Not enough arguments given to a function", show ident]
confirmTypes ident num (exprType:exprs) (argType:args) = do
  if exprType /= argType then typeError $ unwords ["Argument", show num, "given to a function", show ident, "is of type", show exprType, "but should be of type", show argType]
  else confirmTypes ident (num+1) exprs args

typeExpr :: Arabica.Abs.Expr -> Arabica.Abs.TypeCheckingMonadIO Arabica.Abs.Type
typeExpr x = case x of
  Arabica.Abs.EArray type_ _ -> pure $ Arabica.Abs.Array type_
  Arabica.Abs.EArrElem ident expr -> do
    typeEnv <- ask
    let maybeArrType = M.lookup ident typeEnv
    case maybeArrType of
      Nothing -> typeError $ unwords ["No identifier", show ident, "was found"]
      Just arrType -> do
        case arrType of
          Arabica.Abs.Array elemType -> do
            ixType <- typeExpr expr
            case ixType of
              Arabica.Abs.Int -> pure elemType
              _ -> typeError $ unwords ["Arrays must be indexed with an integer"]
          _ -> typeError $ unwords ["Variable", show ident, "is not an array"]
  Arabica.Abs.ELambda type_ args block -> do
    typeEnv <- ask
    let newTypeEnv = foldl (\env (argType, argIdent) -> M.insert argIdent argType env) typeEnv $ map (\(Arabica.Abs.Arg argType argIdent) -> (argType, argIdent)) args
    local (const newTypeEnv) $ typeBlock type_ block
    getLambdaType x
  Arabica.Abs.EVar ident -> do
    typeEnv <- ask
    let maybeType = M.lookup ident typeEnv
    case maybeType of
      Nothing -> typeError $ unwords ["No identifier", "\"" ++ show ident ++ "\"", "was found"]
      Just type_ -> pure type_
  Arabica.Abs.ELitInt integer -> pure $ Arabica.Abs.Int
  Arabica.Abs.ELitTrue -> pure $ Arabica.Abs.Bool
  Arabica.Abs.ELitFalse -> pure $ Arabica.Abs.Bool
  Arabica.Abs.EApp ident exprs -> do
    typeEnv <- ask
    -- lift $ lift $ putStrLn $ show typeEnv
    let maybeVarType = M.lookup ident typeEnv
    case maybeVarType of
      Nothing -> typeError $ unwords ["No identifier", "\"" ++ show ident ++ "\"", "was found"]
      Just varType -> do
        case varType of
          Arabica.Abs.Fun funType argTypes -> do
            exprTypes <- mapM typeExpr exprs
            confirmTypes ident 1 exprTypes argTypes
            pure funType
          _ -> typeError $ unwords ["Variable", show ident, "is not a function"]
  Arabica.Abs.EString string -> pure $ Arabica.Abs.Str
  Arabica.Abs.Neg expr -> do
    exprType <- typeExpr expr
    if exprType == Arabica.Abs.Int then pure $ Arabica.Abs.Int
    else typeError $ unwords ["Only integers can be negated"]
  Arabica.Abs.Not expr -> do
    exprType <- typeExpr expr
    if exprType == Arabica.Abs.Bool then pure $ Arabica.Abs.Bool
    else typeError $ unwords ["Only booleans can be used in logical negation"]
  Arabica.Abs.EMul expr1 op expr2 -> do
    exprType1 <- typeExpr expr1
    case exprType1 of
      Arabica.Abs.Int -> do
        exprType2 <- typeExpr expr2
        case exprType2 of
          Arabica.Abs.Int -> pure $ Arabica.Abs.Int
          _ -> typeError $ unwords ["Second operand of", show x, "is not an integer"]
      _ -> typeError $ unwords ["First operand of", show x, "is not an integer"]
  Arabica.Abs.EAdd expr1 _ expr2 -> do
    exprType1 <- typeExpr expr1
    case exprType1 of
      Arabica.Abs.Int -> do
        exprType2 <- typeExpr expr2
        case exprType2 of
          Arabica.Abs.Int -> pure $ Arabica.Abs.Int
          _ -> typeError $ unwords ["Second operand of", show x, "is not an integer"]
      _ -> typeError $ unwords ["First operand of", show x, "is not an integer"]
  Arabica.Abs.ERel expr1 _ expr2 -> do
    exprType1 <- typeExpr expr1
    case exprType1 of
      Arabica.Abs.Int -> do
        exprType2 <- typeExpr expr2
        case exprType2 of
          Arabica.Abs.Int -> pure $ Arabica.Abs.Bool
          _ -> typeError $ unwords ["Second operand of", show x, "is not an integer"]
      _ -> typeError $ unwords ["First operand of", show x, "is not an integer"]
  Arabica.Abs.EAnd expr1 expr2 -> typeExpr $ Arabica.Abs.EOr expr1 expr2
  Arabica.Abs.EOr expr1 expr2 -> do
    exprType1 <- typeExpr expr1
    case exprType1 of
      Arabica.Abs.Bool -> do
        exprType2 <- typeExpr expr2
        case exprType2 of
          Arabica.Abs.Bool -> pure $ Arabica.Abs.Bool
          _ -> typeError $ unwords ["Second operand of", show x, "is not a boolean"]
      _ -> typeError $ unwords ["First operand of", show x, "is not a boolean"]