-- Program to test parser, automatically generated by BNF Converter.

module Main where

import Prelude
  ( ($)
  , Either(..)
  , Int, (>)
  , String, (++), unlines, unwords
  , Show, show
  , IO, (>>), (>>=), mapM_, putStrLn
  , FilePath
  , getContents, readFile
  , Maybe(..)
  )
import System.Environment ( getArgs )
import System.Exit        ( exitFailure, exitSuccess )
import Control.Monad      ( when )

import Arabica.Abs 
import Arabica.Lex   ( Token )
import Arabica.Par   ( pProgram, myLexer )
import Arabica.Print ( Print, printTree )
import Arabica.Skel  ( transProgram )
-- import Arabica.TypeCheck
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

getExceptionMessage :: Arabica.Abs.Exception -> String
getExceptionMessage exception = 
  case exception of
    Arabica.Abs.NoLocation ident -> unwords ["No location for variable", show ident]
    Arabica.Abs.IncorrectValue ident integer -> unwords ["Incorrect value for address", show integer, "and variable", show ident]
    Arabica.Abs.IndexOutOfBounds n (lower, upper) ident -> unwords ["Position", show n, "out of bounds", show (lower, upper), "for array", show ident]
    Arabica.Abs.ArrayAssignMismatch ident -> unwords ["Types of array", show ident, "and assigned expression do not match"]
    Arabica.Abs.IndexNotInteger ident -> unwords ["Array", show ident, "should be indexed with an integer"]
    Arabica.Abs.NotAnArray ident -> unwords ["Variable", show ident, "cannot be indexed because it is not an array"]
    Arabica.Abs.TooManyArgs ident -> unwords ["Too many values passed to a function", show ident]
    Arabica.Abs.NotEnoughArgs ident -> unwords ["Not enough values passed to a function", show ident]
    Arabica.Abs.NoValueReturned ident type_ -> unwords ["Function", show ident, "should return", show type_, "but returns nothing"]
    Arabica.Abs.NotAFunction ident -> unwords ["Identifier", show ident, "is not a function"]
    Arabica.Abs.DivisionByZero -> "Division by 0"
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
        Left e -> putStrLn $ getExceptionMessage e
        -- Right newEnv -> putStrLn $ unwords ["Środowisko", show newEnv]
        Right _ -> putStrLn "The end"
      exitSuccess
  where
  ts = myLexer s

-- runTypeCheck :: Verbosity -> ParseFun Arabica.Abs.Program -> String -> IO ()
-- runTypeCheck v p s = 
--   case p ts of
--     Left err -> do
--       putStrLn "\nParse              Failed...\n"
--       putStrV v "Tokens:"
--       putStrV v $ show ts
--       putStrLn err
--       exitFailure
--     Right tree -> do
--       putStrLn "\nParse Successful!"
--       -- showTree v tree
--       typeState <- runExceptT $ runReaderT (typeCheckProgram tree) M.empty
--       case typeState of
--         Left e -> putStrLn $ show e
--         Right _ -> putStrLn $ show "Typ ok"
--       exitSuccess
--   where
--   ts = myLexer s

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
    -- ["--type"] -> getContents >>= runTypeCheck 2 pProgram
    []         -> getContents >>= runProgram 2 pProgram
    "-s":fs    -> mapM_ (runFile 0 pProgram) fs
    fs         -> mapM_ (runFile 2 pProgram) fs

