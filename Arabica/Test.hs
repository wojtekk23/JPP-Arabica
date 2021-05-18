-- Program to test parser, automatically generated by BNF Converter.

module Main where

import Prelude
  ( ($)
  , Either(..)
  , Int, (>)
  , String, (++), unlines, unwords
  , Show, show
  , (>>), (>>=), mapM_, putStrLn
  , FilePath
  , getContents, readFile
  , Maybe(..)
  )
import System.Environment ( getArgs )
import System.Exit        ( exitFailure, exitSuccess )
import Control.Monad      ( when )
import System.IO

import Arabica.Abs 
import Arabica.Lex   ( Token )
import Arabica.Par   ( pProgram, myLexer )
import Arabica.Print ( Print, printTree )
import Arabica.Skel  ( transProgram )
import Arabica.TypeCheck
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.Except
import qualified Data.Map as M
import Control.Monad.State
import Control.Monad.Reader

type Err        = Either String
type ParseFun a = [Token] -> Err a
type Verbosity  = Int

putStrV :: Verbosity -> String -> IO ()
putStrV v s = when (v > 1) $ putStrLn s

runFile :: (Print a, Show a) => Verbosity -> ParseFun a -> FilePath -> IO ()
runFile v p f = putStrLn f >> readFile f >>= run v p

run :: (Print a, Show a) => Verbosity -> ParseFun a -> String -> IO ()
run v p s =
  case p ts of
    Left err -> do
      putStrLn "\nParse              Failed...\n"
      putStrV v "Tokens:"
      putStrV v $ show ts
      putStrLn err
      exitFailure
    Right tree -> do
      putStrLn "\nParse Successful!"
      showTree v tree
      exitSuccess
  where
  ts = myLexer s

addPositionToExceptionMessage :: Arabica.Abs.BNFC'Position -> String -> String
addPositionToExceptionMessage p s = 
  case p of
    Just (line, col) -> unwords [show line ++ ":" ++ show col ++ ":", s]
    Nothing -> unwords ["Position unavailable:", s]

getExceptionMessage :: Arabica.Abs.Exception -> String
getExceptionMessage exception = 
  case exception of
    Arabica.Abs.NoLocation p ident -> addPositionToExceptionMessage p $ unwords ["No location for variable", show ident]
    Arabica.Abs.IncorrectValue p ident integer -> addPositionToExceptionMessage p $ unwords ["Incorrect value for address", show integer, "and variable", show ident]
    Arabica.Abs.IndexOutOfBounds p n (lower, upper) ident -> addPositionToExceptionMessage p $ unwords ["Position", show n, "out of bounds", show (lower, upper), "for array", show ident]
    Arabica.Abs.ArrayAssignMismatch p ident -> addPositionToExceptionMessage p $ unwords ["Types of array", show ident, "and assigned expression do not match"]
    Arabica.Abs.IndexNotInteger p ident -> addPositionToExceptionMessage p $ unwords ["Array", show ident, "should be indexed with an integer"]
    Arabica.Abs.NotAnArray p ident -> addPositionToExceptionMessage p $ unwords ["Variable", show ident, "cannot be indexed because it is not an array"]
    Arabica.Abs.TooManyArgs p ident -> addPositionToExceptionMessage p $ unwords ["Too many values passed to a function", show ident]
    Arabica.Abs.NotEnoughArgs p ident -> addPositionToExceptionMessage p $ unwords ["Not enough values passed to a function", show ident]
    Arabica.Abs.NoValueReturned p ident type_ -> addPositionToExceptionMessage p $ unwords ["Function", show ident, "should return", show type_, "but returns nothing"]
    Arabica.Abs.NotAFunction p ident -> addPositionToExceptionMessage p $ unwords ["Identifier", show ident, "is not a function"]
    Arabica.Abs.DivisionByZero p -> addPositionToExceptionMessage p $ "Division by 0"
    Arabica.Abs.WrongValueReturned p ident type1 type2 -> addPositionToExceptionMessage p $ unwords ["Function", show ident, "should return", show type1, "but returns", show type2]
    Arabica.Abs.StringError s -> s

runProgram :: Verbosity -> ParseFun Arabica.Abs.Program -> String -> IO ()
runProgram v p s =
  case p ts of
    Left err -> do
      putStrLn "\nParse              Failed...\n"
      putStrV v "Tokens:"
      putStrV v $ show ts
      putStrLn err
      exitFailure
    Right tree -> do
      putStrLn "\nParse Successful!"
      -- showTree v tree
      expEnv <- runExceptT $ execStateT (runReaderT (transProgram tree) M.empty) (M.empty, 0)
      case expEnv of
        Left e -> hPutStrLn stderr $ getExceptionMessage e
        -- Right newEnv -> putStrLn $ unwords ["Środowisko", show newEnv]
        Right _ -> putStrLn "The end"
      exitSuccess
  where
  ts = myLexer s

getTypeErrorMessage :: Arabica.Abs.TypeCheckingError -> String
getTypeErrorMessage typeError = addPositionToExceptionMessage (Arabica.Abs.hasPosition typeError) s
  where
    s = case typeError of
      Arabica.Abs.CustomTypeError _ s -> s
      Arabica.Abs.WrongMainTypeError _ -> "Main function should have a return type int and take no arguments"
      Arabica.Abs.WrongInitType p ident type1 type2 -> unwords ["Variable", show ident, "is of type", show type1, "but was initialized with type", show type2]
      Arabica.Abs.NoIdentifierFound p ident -> unwords ["No identifier", show ident, "was found"]
      Arabica.Abs.ExpressionVariableMismatch p ident -> unwords ["Type of an expression and type of variable", show ident, "mismatch"]
      Arabica.Abs.ExpressionArrayMismatch p ident -> unwords ["Type of an expression and type of an array", show ident, "mismatch"]
      Arabica.Abs.NonIntegerIndex p ident -> unwords ["Array", show ident, "can only be accessed with an integer"]
      Arabica.Abs.NotAnArrayType p ident -> unwords ["Variable", show ident, "is not an array and cannot be indexed"]
      Arabica.Abs.IncrementNonInteger p ident -> unwords ["Variable", show ident, "cannot be incremented because it is not an integer"]
      Arabica.Abs.DecrementNonInteger p ident -> unwords ["Variable", show ident, "cannot be decremented because it is not an integer"]
      Arabica.Abs.WrongReturnType p type1 type2 -> unwords ["Function is of type", show type1, "but it contains a statement returning type", show type2]
      Arabica.Abs.WrongVoidReturn p type_ -> unwords ["Function is of type", show type_, "but it contains a void return statement"]
      Arabica.Abs.WrongConditionType p condType -> unwords ["Condition is of type", show condType, "but it has to be either a boolean or integer value"]
      Arabica.Abs.WrongForBeginType p -> unwords ["Begin expression in for loop should be of type int"]
      Arabica.Abs.WrongForEndType p -> unwords ["End expression in for loop should be of type int"]
      Arabica.Abs.TooManyArgsType p ident -> unwords ["Too many arguments given to a function", show ident]
      Arabica.Abs.NotEnoughArgsType p ident -> unwords ["Not enough arguments given to a function", show ident]
      Arabica.Abs.FunArgumentTypeMismatch p num ident exprType argType -> unwords ["Argument", show num, "given to a function", show ident, "is of type", show exprType, "but should be of type", show argType]
      Arabica.Abs.NotAFunctionType p ident -> unwords ["Variable", show ident, "is not a function"]
      Arabica.Abs.ArithNegationType p type_ -> unwords ["Tried to negate expression of type", show type_, "but it should be an integer"]
      Arabica.Abs.LogicNegationType p type_ -> unwords ["Tried to apply logical not to an expression of type", show type_, "but it should be a boolean"]
      Arabica.Abs.FirstOperandShouldBeType p type1 type2 -> unwords ["First operand of expression should be of type", show type1, "but is of type", show type2]
      Arabica.Abs.SecondOperandShouldBeType p type1 type2 -> unwords ["Second operand of expression should be of type", show type1, "but is of type", show type2]

runTypeCheck :: Verbosity -> ParseFun Arabica.Abs.Program -> String -> IO ()
runTypeCheck v p s = 
  case p ts of
    Left err -> do
      putStrLn "\nParse              Failed...\n"
      putStrV v "Tokens:"
      putStrV v $ show ts
      putStrLn err
      exitFailure
    Right tree -> do
      putStrLn "\nParse Successful!"
      -- showTree v tree
      typeState <- runExceptT $ runReaderT (typeCheckProgram tree) M.empty
      case typeState of
        Left e -> hPutStrLn stderr $ getTypeErrorMessage e
        Right _ -> putStrLn $ show "Typ ok"
      exitSuccess
  where
  ts = myLexer s

showTree :: (Show a, Print a) => Int -> a -> IO ()
showTree v tree = do
  putStrV v $ "\n[Abstract Syntax]\n\n" ++ show tree
  putStrV v $ "\n[Linearized tree]\n\n" ++ printTree tree

usage :: IO ()
usage = do
  putStrLn $ unlines
    [ "usage: Call with one of the following argument combinations:"
    , "  --help          Display this help message."
    , "  (no arguments)  Parse stdin verbosely."
    , "  (files)         Parse content of files verbosely."
    , "  -s (files)      Silent mode. Parse content of files silently."
    ]
  exitFailure

main :: IO ()
main = do
  args <- getArgs
  case args of
    ["--help"] -> usage
    ["--tree"] -> getContents >>= run 2 pProgram
    ["--type"] -> getContents >>= runTypeCheck 2 pProgram
    []         -> getContents >>= runProgram 2 pProgram
    "-s":fs    -> mapM_ (runFile 0 pProgram) fs
    fs         -> mapM_ (runFile 2 pProgram) fs

