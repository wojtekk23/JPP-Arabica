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
      local (M.insert ident fnType) $ checkTopDefs topdefs

typeTopDef :: Arabica.Abs.TopDef -> Arabica.Abs.TypeCheckingMonadIO ()
typeTopDef x = case x of
  Arabica.Abs.FnDef type_ ident args block -> do
    typeEnv <- ask
    let argsTypeEnv = foldl (\env (argType, argIdent) -> M.insert argIdent argType env) typeEnv $ map (\(Arabica.Abs.Arg argType argIdent) -> (argType, argIdent)) args
    let newTypeEnv = M.insert ident type_ argsTypeEnv
    local (const newTypeEnv) $ typeBlock type_ block

typeBlock :: Arabica.Abs.Type -> Arabica.Abs.Block -> Arabica.Abs.TypeCheckingMonadIO ()
typeBlock type_ x = case x of
  Arabica.Abs.Block stmts -> typeError "type block"

typeStmts :: Arabica.Abs.Type -> Arabica.Abs.Stmt -> Arabica.Abs.TypeCheckingMonadIO Arabica.Abs.TypeEnv
typeStmts fnType x = case x of
  Arabica.Abs.Empty -> ask
  Arabica.Abs.BStmt block -> do
    typeBlock fnType block
    ask
  Arabica.Abs.Decl type_ items -> typeError "type decl"
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
  Arabica.Abs.Ret expr -> typeError "type Ret"
  Arabica.Abs.VRet -> typeError "type VRet"
  Arabica.Abs.Cond expr stmt -> typeError "type Cond"
  Arabica.Abs.CondElse expr stmt1 stmt2 -> typeError "type CondElse"
  Arabica.Abs.While expr stmt -> typeError "type While"
  Arabica.Abs.Break -> ask
  Arabica.Abs.Continue -> ask
  Arabica.Abs.SExp expr -> do
    typeExpr expr
    ask
  Arabica.Abs.ForTo ident expr1 expr2 stmt -> typeError "type ForTo"
  Arabica.Abs.Print expr -> do
    typeExpr expr
    ask

typeExpr :: Arabica.Abs.Expr -> Arabica.Abs.TypeCheckingMonadIO Arabica.Abs.Type
typeExpr x = case x of
  Arabica.Abs.EArray type_ _ -> pure $ Arabica.Abs.Array type_
  Arabica.Abs.EArrElem ident expr -> typeError "typeExpr EArrElem"
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
  Arabica.Abs.EApp ident exprs -> typeError "typeExpr EApp"
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