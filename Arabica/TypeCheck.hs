module Arabica.TypeCheck where

import qualified Arabica.Abs
import Arabica.Utils
import qualified Data.Map as M
import Control.Monad.Reader
import Control.Monad.Trans.Except

getArgType (Arabica.Abs.Arg _ type_ ident) = pure $ transType type_
getTopDefType (Arabica.Abs.FnDef _ type_ ident args block) = do
  let absType = transType type_
  argTypes <- mapM getArgType args
  pure $ Arabica.Abs.Fun absType argTypes
getLambdaType (Arabica.Abs.ELambda _ type_ args block) = do
  let absType = transType type_
  argTypes <- mapM getArgType args
  pure $ Arabica.Abs.Fun absType argTypes

typeError :: Show a => Arabica.Abs.BNFC'Position -> a -> Arabica.Abs.TypeCheckingMonadIO b
typeError p x = lift $ throwE $ Arabica.Abs.CustomTypeError p $ show x

throwTypeError :: Arabica.Abs.TypeCheckingError -> Arabica.Abs.TypeCheckingMonadIO b
throwTypeError x = lift $ throwE $ x

-- Type-check program
typeCheckProgram :: Arabica.Abs.Program -> Arabica.Abs.TypeCheckingMonadIO ()
typeCheckProgram x = case x of
  Arabica.Abs.Program _ topdefs -> do
    checkTopDefs topdefs
  where
    checkTopDefs [] = pure ()
    checkTopDefs (topdef:topdefs) = do
      let Arabica.Abs.FnDef _ _ ident _ _ = topdef
      typeTopDef topdef
      fnType <- getTopDefType topdef
      local (M.insert ident fnType) $ checkTopDefs topdefs

-- Type-check top definitions (top functions including main)
typeTopDef :: Arabica.Abs.TopDef -> Arabica.Abs.TypeCheckingMonadIO ()
typeTopDef x = case x of
  Arabica.Abs.FnDef p type_ ident args block -> do
    let Arabica.Abs.Ident name = ident
    let absType = transType type_
    let absArgs = map transArg args
    if name == "main" && (absType /= Arabica.Abs.Int || length absArgs /= 0) then do
      throwTypeError $ Arabica.Abs.WrongMainTypeError p
    else do
      typeEnv <- ask
      topDefType <- getTopDefType x
      let argsTypeEnv = foldl (\env (argType, argIdent) -> M.insert argIdent argType env) typeEnv $ map (\(Arabica.Abs.AbsArg argType argIdent) -> (argType, argIdent)) absArgs
      let newTypeEnv = M.insert ident topDefType argsTypeEnv
      local (const newTypeEnv) $ typeBlock absType block

-- Type-check block
-- retType: type of a function the block is a part of
typeBlock :: Arabica.Abs.AbsType -> Arabica.Abs.Block -> Arabica.Abs.TypeCheckingMonadIO ()
typeBlock retType x = case x of
  Arabica.Abs.Block _ stmts -> runTypeStmts retType stmts
  where
    runTypeStmts :: Arabica.Abs.AbsType -> [Arabica.Abs.Stmt] -> Arabica.Abs.TypeCheckingMonadIO ()
    runTypeStmts type_ [] = pure ()
    runTypeStmts type_ (stmt:stmts) = do
      newEnv <- typeStmts type_ stmt
      local (const newEnv) $ runTypeStmts type_ stmts

-- Type-check item declarations
-- itemType: type of the new variable
typeItem :: Arabica.Abs.AbsType -> Arabica.Abs.Item -> Arabica.Abs.TypeCheckingMonadIO Arabica.Abs.Ident
typeItem itemType x = case x of
  Arabica.Abs.NoInit _ ident -> pure ident
  Arabica.Abs.Init p ident expr -> do
    exprType <- typeExpr expr
    if exprType == itemType then pure ident
    else throwTypeError $ Arabica.Abs.WrongInitType p ident itemType exprType

-- Type-check statement
-- fnType: AbsType of the function statement is a part of
typeStmts :: Arabica.Abs.AbsType -> Arabica.Abs.Stmt -> Arabica.Abs.TypeCheckingMonadIO Arabica.Abs.TypeEnv
typeStmts fnType x = case x of
  Arabica.Abs.Empty _ -> ask
  Arabica.Abs.BStmt _ block -> do
    typeBlock fnType block
    ask
  Arabica.Abs.Decl _ type_ items -> do
    let itemType = transType type_
    varIdents <- mapM (typeItem itemType) items
    typeEnv <- ask
    let newTypeEnv = foldl (\env ident -> M.insert ident itemType env) typeEnv varIdents
    pure newTypeEnv
  Arabica.Abs.Ass p ident expr -> do
    typeEnv <- ask
    let maybeVar = M.lookup ident typeEnv
    case maybeVar of
      Nothing -> throwTypeError $ Arabica.Abs.NoIdentifierFound p ident
      Just varType -> do
        exprType <- typeExpr expr
        if exprType == varType then ask
        else throwTypeError $ Arabica.Abs.ExpressionVariableMismatch p ident
  Arabica.Abs.ArrAss p ident indexExpr valExpr -> do
    typeEnv <- ask
    let maybeArr = M.lookup ident typeEnv
    case maybeArr of
      Nothing -> throwTypeError $ Arabica.Abs.NoIdentifierFound p ident
      Just arrType -> case arrType of
        Arabica.Abs.Array arrType -> do
          indexType <- typeExpr indexExpr
          case indexType of
            Arabica.Abs.Int -> do
              valType <- typeExpr valExpr
              if valType == arrType then ask
              else throwTypeError $ Arabica.Abs.ExpressionArrayMismatch p ident
            _ -> throwTypeError $ Arabica.Abs.NonIntegerIndex p ident
        _ -> throwTypeError $ Arabica.Abs.NotAnArrayType p ident
  Arabica.Abs.Incr p ident -> do
    valType <- typeExpr $ Arabica.Abs.EVar p ident
    case valType of
      Arabica.Abs.Int -> ask
      _ -> throwTypeError $ Arabica.Abs.IncrementNonInteger p ident
  Arabica.Abs.Decr p ident -> do
    valType <- typeExpr $ Arabica.Abs.EVar p ident
    case valType of
      Arabica.Abs.Int -> ask
      _ -> throwTypeError $ Arabica.Abs.DecrementNonInteger p ident
  Arabica.Abs.Ret p expr -> do
    exprType <- typeExpr expr
    if exprType == fnType then ask
    else throwTypeError $ Arabica.Abs.WrongReturnType p fnType exprType
  Arabica.Abs.VRet p -> do
    if fnType == Arabica.Abs.Void then ask
    else throwTypeError $ Arabica.Abs.WrongVoidReturn p fnType
  Arabica.Abs.Cond p expr stmt -> typeStmts fnType $ Arabica.Abs.CondElse p expr stmt $ Arabica.Abs.Empty p
  Arabica.Abs.CondElse p expr stmt1 stmt2 -> do
    condType <- typeExpr expr
    if condType /= Arabica.Abs.Bool && condType /= Arabica.Abs.Int then
      throwTypeError $ Arabica.Abs.WrongConditionType p condType
    else do
      typeStmts fnType stmt1
      typeStmts fnType stmt2
      ask
  Arabica.Abs.While p expr stmt -> do
    condType <- typeExpr expr
    if condType /= Arabica.Abs.Bool && condType /= Arabica.Abs.Int then
      throwTypeError $ Arabica.Abs.WrongConditionType p condType
    else do
      typeStmts fnType stmt
      ask
  Arabica.Abs.Break _ -> ask
  Arabica.Abs.Continue _ -> ask
  Arabica.Abs.SExp _ expr -> do
    typeExpr expr
    ask
  Arabica.Abs.ForTo p ident expr1 expr2 stmt -> do
    beginType <- typeExpr expr1
    case beginType of
      Arabica.Abs.Int -> do
        endType <- typeExpr expr2
        case endType of
          Arabica.Abs.Int -> do
            local (M.insert ident Arabica.Abs.Int) $ typeStmts fnType stmt
            ask
          _ -> throwTypeError $ Arabica.Abs.WrongForEndType p
      _ -> throwTypeError $ Arabica.Abs.WrongForBeginType p
  Arabica.Abs.Print _ expr -> do
    typeExpr expr
    ask

-- Check if the AbsTypes in two lists are the same
confirmTypes :: Arabica.Abs.BNFC'Position -> Arabica.Abs.Ident -> Integer -> [Arabica.Abs.AbsType] -> [Arabica.Abs.AbsType] -> Arabica.Abs.TypeCheckingMonadIO ()
confirmTypes _ _ _ [] [] = pure ()
confirmTypes p ident _ _ [] = throwTypeError $ Arabica.Abs.TooManyArgsType p ident
confirmTypes p ident _ [] _ = throwTypeError $ Arabica.Abs.NotEnoughArgsType p ident
confirmTypes p ident num (exprType:exprs) (argType:args) = do
  if exprType /= argType then throwTypeError $ Arabica.Abs.FunArgumentTypeMismatch p num ident exprType argType
  else confirmTypes p ident (num+1) exprs args

-- Type-check expression
typeExpr :: Arabica.Abs.Expr -> Arabica.Abs.TypeCheckingMonadIO Arabica.Abs.AbsType
typeExpr x = case x of
  Arabica.Abs.EArray _ type_ _ -> pure $ Arabica.Abs.Array $ transType type_
  Arabica.Abs.EArrElem p ident expr -> do
    typeEnv <- ask
    let maybeArrType = M.lookup ident typeEnv
    case maybeArrType of
      Nothing -> throwTypeError $ Arabica.Abs.NoIdentifierFound p ident
      Just arrType -> do
        case arrType of
          Arabica.Abs.Array elemType -> do
            ixType <- typeExpr expr
            case ixType of
              Arabica.Abs.Int -> pure elemType
              _ -> throwTypeError $ Arabica.Abs.NonIntegerIndex p ident
          _ -> throwTypeError $ Arabica.Abs.NotAnArrayType p ident
  Arabica.Abs.ELambda _ type_ args block -> do
    typeEnv <- ask
    let absType = transType type_
    let newTypeEnv = foldl (\env (argType, argIdent) -> M.insert argIdent argType env) typeEnv $ map (\(Arabica.Abs.AbsArg argType argIdent) -> (argType, argIdent)) $ map transArg args
    local (const newTypeEnv) $ typeBlock absType block
    getLambdaType x
  Arabica.Abs.EVar p ident -> do
    typeEnv <- ask
    let maybeType = M.lookup ident typeEnv
    case maybeType of
      Nothing -> throwTypeError $ Arabica.Abs.NoIdentifierFound p ident
      Just type_ -> pure type_
  Arabica.Abs.ELitInt _ integer -> pure $ Arabica.Abs.Int
  Arabica.Abs.ELitTrue _ -> pure $ Arabica.Abs.Bool
  Arabica.Abs.ELitFalse _ -> pure $ Arabica.Abs.Bool
  Arabica.Abs.EApp p ident exprs -> do
    typeEnv <- ask
    let maybeVarType = M.lookup ident typeEnv
    case maybeVarType of
      Nothing -> throwTypeError $ Arabica.Abs.NoIdentifierFound p ident
      Just varType -> do
        case varType of
          Arabica.Abs.Fun funType argTypes -> do
            exprTypes <- mapM typeExpr exprs
            confirmTypes p ident 1 exprTypes argTypes
            pure funType
          _ -> throwTypeError $ Arabica.Abs.NotAFunctionType p ident
  Arabica.Abs.EString _ string -> pure $ Arabica.Abs.Str
  Arabica.Abs.Neg p expr -> do
    exprType <- typeExpr expr
    if exprType == Arabica.Abs.Int then pure $ Arabica.Abs.Int
    else throwTypeError $ Arabica.Abs.ArithNegationType p exprType
  Arabica.Abs.Not p expr -> do
    exprType <- typeExpr expr
    if exprType == Arabica.Abs.Bool then pure $ Arabica.Abs.Bool
    else throwTypeError $ Arabica.Abs.LogicNegationType p exprType
  Arabica.Abs.EMul p expr1 op expr2 -> do
    exprType1 <- typeExpr expr1
    case exprType1 of
      Arabica.Abs.Int -> do
        exprType2 <- typeExpr expr2
        case exprType2 of
          Arabica.Abs.Int -> pure $ Arabica.Abs.Int
          otherType2 -> throwTypeError $ Arabica.Abs.SecondOperandShouldBeType p Arabica.Abs.Int otherType2
      otherType1 -> throwTypeError $ Arabica.Abs.FirstOperandShouldBeType p Arabica.Abs.Int otherType1
  Arabica.Abs.EAdd p expr1 _ expr2 -> do
    exprType1 <- typeExpr expr1
    case exprType1 of
      Arabica.Abs.Int -> do
        exprType2 <- typeExpr expr2
        case exprType2 of
          Arabica.Abs.Int -> pure $ Arabica.Abs.Int
          otherType2 -> throwTypeError $ Arabica.Abs.SecondOperandShouldBeType p Arabica.Abs.Int otherType2
      otherType1 -> throwTypeError $ Arabica.Abs.FirstOperandShouldBeType p Arabica.Abs.Int otherType1
  Arabica.Abs.ERel p expr1 _ expr2 -> do
    exprType1 <- typeExpr expr1
    case exprType1 of
      Arabica.Abs.Int -> do
        exprType2 <- typeExpr expr2
        case exprType2 of
          Arabica.Abs.Int -> pure $ Arabica.Abs.Bool
          otherType2 -> throwTypeError $ Arabica.Abs.SecondOperandShouldBeType p Arabica.Abs.Int otherType2
      otherType1 -> throwTypeError $ Arabica.Abs.FirstOperandShouldBeType p Arabica.Abs.Int otherType1
  Arabica.Abs.EAnd p expr1 expr2 -> typeExpr $ Arabica.Abs.EOr p expr1 expr2
  Arabica.Abs.EOr p expr1 expr2 -> do
    exprType1 <- typeExpr expr1
    case exprType1 of
      Arabica.Abs.Bool -> do
        exprType2 <- typeExpr expr2
        case exprType2 of
          Arabica.Abs.Bool -> pure $ Arabica.Abs.Bool
          otherType2 -> throwTypeError $ Arabica.Abs.SecondOperandShouldBeType p Arabica.Abs.Bool otherType2
      otherType1 -> throwTypeError $ Arabica.Abs.FirstOperandShouldBeType p Arabica.Abs.Int otherType1