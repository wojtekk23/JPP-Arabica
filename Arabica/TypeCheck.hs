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
      -- lift $ lift $ putStrLn $ unwords ["fnType", show fnType]
      local (M.insert ident fnType) $ checkTopDefs topdefs

typeTopDef :: Arabica.Abs.TopDef -> Arabica.Abs.TypeCheckingMonadIO ()
typeTopDef x = case x of
  Arabica.Abs.FnDef p type_ ident args block -> do
    let Arabica.Abs.Ident name = ident
    let absType = transType type_
    let absArgs = map transArg args
    if name == "main" && (absType /= Arabica.Abs.Int || length absArgs /= 0) then do
      typeError p $ unwords ["Main function should have a return type int and take no arguments"]
    else do
      typeEnv <- ask
      topDefType <- getTopDefType x
      let argsTypeEnv = foldl (\env (argType, argIdent) -> M.insert argIdent argType env) typeEnv $ map (\(Arabica.Abs.AbsArg argType argIdent) -> (argType, argIdent)) absArgs
      let newTypeEnv = M.insert ident topDefType argsTypeEnv
      local (const newTypeEnv) $ typeBlock absType block

typeBlock :: Arabica.Abs.AbsType -> Arabica.Abs.Block -> Arabica.Abs.TypeCheckingMonadIO ()
typeBlock retType x = case x of
  Arabica.Abs.Block _ stmts -> runTypeStmts retType stmts
  where
    runTypeStmts :: Arabica.Abs.AbsType -> [Arabica.Abs.Stmt] -> Arabica.Abs.TypeCheckingMonadIO ()
    runTypeStmts type_ [] = pure ()
    runTypeStmts type_ (stmt:stmts) = do
      newEnv <- typeStmts type_ stmt
      local (const newEnv) $ runTypeStmts type_ stmts

typeItem :: Arabica.Abs.AbsType -> Arabica.Abs.Item -> Arabica.Abs.TypeCheckingMonadIO Arabica.Abs.Ident
typeItem itemType x = case x of
  Arabica.Abs.NoInit _ ident -> pure ident
  Arabica.Abs.Init p ident expr -> do
    exprType <- typeExpr expr
    if exprType == itemType then pure ident
    else typeError p $ unwords ["Variable", show ident, "is of type", show itemType, "but was initialized with type", show exprType]

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
      Nothing -> typeError p $ unwords ["No identifier", "\"" ++ show ident ++ "\"", "was found"]
      Just varType -> do
        exprType <- typeExpr expr
        if exprType == varType then ask
        else typeError p $ unwords ["Type of an expression", show expr, "and type of variable", show ident, "do not match"]
  Arabica.Abs.ArrAss p ident indexExpr valExpr -> do
    typeEnv <- ask
    let maybeArr = M.lookup ident typeEnv
    case maybeArr of
      Nothing -> typeError p $ unwords ["No identifier", "\"" ++ show ident ++ "\"", "was found"]
      Just arrType -> case arrType of
        Arabica.Abs.Array arrType -> do
          indexType <- typeExpr indexExpr
          case indexType of
            Arabica.Abs.Int -> do
              valType <- typeExpr valExpr
              if valType == arrType then ask
              else typeError p $ unwords ["Type of an expression", show valExpr, "and type of array", show ident, "do not match"]
            _ -> typeError p $ unwords ["Array", "\"" ++ show ident ++ "\"", "can only be accessed with an integer"]
        _ -> typeError p $ unwords ["Variable", "\"" ++ show ident ++ "\"", "is not an array"]
  Arabica.Abs.Incr p ident -> do
    valType <- typeExpr $ Arabica.Abs.EVar p ident
    case valType of
      Arabica.Abs.Int -> ask
      _ -> typeError p $ unwords ["Variable", show x, "cannot be incremented because it is not an integer"]
  Arabica.Abs.Decr p ident -> do
    valType <- typeExpr $ Arabica.Abs.EVar p ident
    case valType of
      Arabica.Abs.Int -> ask
      _ -> typeError p $ unwords ["Variable", show x, "cannot be decremented because it is not an integer"]
  Arabica.Abs.Ret p expr -> do
    exprType <- typeExpr expr
    if exprType == fnType then ask
    else typeError p $ unwords ["Function is of type", show fnType, "but it contains a statement returning type", show exprType]
  Arabica.Abs.VRet p -> do
    if fnType == Arabica.Abs.Void then ask
    else typeError p $ unwords ["Function is of type", show fnType, "but it contains a void return statement"]
  -- Chyba nie powinniśmy przypisywać Arabica.Abs.Empty takiej pozycji :/
  Arabica.Abs.Cond p expr stmt -> typeStmts fnType $ Arabica.Abs.CondElse p expr stmt $ Arabica.Abs.Empty p
  Arabica.Abs.CondElse p expr stmt1 stmt2 -> do
    condType <- typeExpr expr
    if condType /= Arabica.Abs.Bool && condType /= Arabica.Abs.Int then
      typeError p $ unwords ["Condition is of type", show condType, "but it has to either a boolean or integer value"]
    else do
      typeStmts fnType stmt1
      typeStmts fnType stmt2
      ask
  Arabica.Abs.While p expr stmt -> do
    condType <- typeExpr expr
    if condType /= Arabica.Abs.Bool && condType /= Arabica.Abs.Int then
      typeError p $ unwords ["Condition is of type", show condType, "but it has to either a boolean or integer value"]
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
          _ -> typeError p $ unwords ["End expression in for loop should be of type Int"]
      _ -> typeError p $ unwords ["Begin expression in for loop should be of type Int"]
  Arabica.Abs.Print _ expr -> do
    typeExpr expr
    ask

confirmTypes :: Arabica.Abs.BNFC'Position -> Arabica.Abs.Ident -> Integer -> [Arabica.Abs.AbsType] -> [Arabica.Abs.AbsType] -> Arabica.Abs.TypeCheckingMonadIO ()
confirmTypes _ _ _ [] [] = pure ()
confirmTypes p ident _ _ [] = typeError p $ unwords ["Too many arguments given to a function", show ident]
confirmTypes p ident _ [] _ = typeError p $ unwords ["Not enough arguments given to a function", show ident]
confirmTypes p ident num (exprType:exprs) (argType:args) = do
  if exprType /= argType then typeError p $ unwords ["Argument", show num, "given to a function", show ident, "is of type", show exprType, "but should be of type", show argType]
  else confirmTypes p ident (num+1) exprs args

typeExpr :: Arabica.Abs.Expr -> Arabica.Abs.TypeCheckingMonadIO Arabica.Abs.AbsType
typeExpr x = case x of
  Arabica.Abs.EArray _ type_ _ -> pure $ Arabica.Abs.Array $ transType type_
  Arabica.Abs.EArrElem p ident expr -> do
    typeEnv <- ask
    let maybeArrType = M.lookup ident typeEnv
    case maybeArrType of
      Nothing -> typeError p $ unwords ["No identifier", show ident, "was found"]
      Just arrType -> do
        case arrType of
          Arabica.Abs.Array elemType -> do
            ixType <- typeExpr expr
            case ixType of
              Arabica.Abs.Int -> pure elemType
              _ -> typeError p $ unwords ["Arrays must be indexed with an integer"]
          _ -> typeError p $ unwords ["Variable", show ident, "is not an array"]
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
      Nothing -> typeError p $ unwords ["No identifier", "\"" ++ show ident ++ "\"", "was found"]
      Just type_ -> pure type_
  Arabica.Abs.ELitInt _ integer -> pure $ Arabica.Abs.Int
  Arabica.Abs.ELitTrue _ -> pure $ Arabica.Abs.Bool
  Arabica.Abs.ELitFalse _ -> pure $ Arabica.Abs.Bool
  Arabica.Abs.EApp p ident exprs -> do
    typeEnv <- ask
    -- lift $ lift $ putStrLn $ show typeEnv
    let maybeVarType = M.lookup ident typeEnv
    case maybeVarType of
      Nothing -> typeError p $ unwords ["No identifier", "\"" ++ show ident ++ "\"", "was found"]
      Just varType -> do
        case varType of
          Arabica.Abs.Fun funType argTypes -> do
            exprTypes <- mapM typeExpr exprs
            confirmTypes p ident 1 exprTypes argTypes
            pure funType
          _ -> typeError p $ unwords ["Variable", show ident, "is not a function"]
  Arabica.Abs.EString _ string -> pure $ Arabica.Abs.Str
  Arabica.Abs.Neg p expr -> do
    exprType <- typeExpr expr
    if exprType == Arabica.Abs.Int then pure $ Arabica.Abs.Int
    else typeError p $ unwords ["Only integers can be negated"]
  Arabica.Abs.Not p expr -> do
    exprType <- typeExpr expr
    if exprType == Arabica.Abs.Bool then pure $ Arabica.Abs.Bool
    else typeError p $ unwords ["Only booleans can be used in logical negation"]
  Arabica.Abs.EMul p expr1 op expr2 -> do
    exprType1 <- typeExpr expr1
    case exprType1 of
      Arabica.Abs.Int -> do
        exprType2 <- typeExpr expr2
        case exprType2 of
          Arabica.Abs.Int -> pure $ Arabica.Abs.Int
          _ -> typeError p $ unwords ["Second operand of", show x, "is not an integer"]
      _ -> typeError p $ unwords ["First operand of", show x, "is not an integer"]
  Arabica.Abs.EAdd p expr1 _ expr2 -> do
    exprType1 <- typeExpr expr1
    case exprType1 of
      Arabica.Abs.Int -> do
        exprType2 <- typeExpr expr2
        case exprType2 of
          Arabica.Abs.Int -> pure $ Arabica.Abs.Int
          _ -> typeError p $ unwords ["Second operand of", show x, "is not an integer"]
      _ -> typeError p $ unwords ["First operand of", show x, "is not an integer"]
  Arabica.Abs.ERel p expr1 _ expr2 -> do
    exprType1 <- typeExpr expr1
    case exprType1 of
      Arabica.Abs.Int -> do
        exprType2 <- typeExpr expr2
        case exprType2 of
          Arabica.Abs.Int -> pure $ Arabica.Abs.Bool
          _ -> typeError p $ unwords ["Second operand of", show x, "is not an integer"]
      _ -> typeError p $ unwords ["First operand of", show x, "is not an integer"]
  Arabica.Abs.EAnd p expr1 expr2 -> typeExpr $ Arabica.Abs.EOr p expr1 expr2
  Arabica.Abs.EOr p expr1 expr2 -> do
    exprType1 <- typeExpr expr1
    case exprType1 of
      Arabica.Abs.Bool -> do
        exprType2 <- typeExpr expr2
        case exprType2 of
          Arabica.Abs.Bool -> pure $ Arabica.Abs.Bool
          _ -> typeError p $ unwords ["Second operand of", show x, "is not a boolean"]
      _ -> typeError p $ unwords ["First operand of", show x, "is not a boolean"]