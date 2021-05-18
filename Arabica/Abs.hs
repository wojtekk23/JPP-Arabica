-- Haskell data types for the abstract syntax.
-- Generated by the BNF converter.

{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}

-- | The abstract syntax of language arabica.

module Arabica.Abs where

import Prelude (Integer, String, Bool, Maybe, IO)
import qualified Prelude as C
  ( Eq, Ord, Show(..), Read
  , Functor, Foldable, Traversable
  , Int, Maybe(..)
  )
import qualified Data.String
import qualified Data.Map as M
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.Except
import Data.Array

type Program = Program' BNFC'Position
data Program' a = Program a [TopDef' a]
  deriving (C.Eq, C.Ord, C.Show, C.Read, C.Functor, C.Foldable, C.Traversable)

type TopDef = TopDef' BNFC'Position
data TopDef' a = FnDef a (Type' a) Ident [Arg' a] (Block' a)
  deriving (C.Eq, C.Ord, C.Show, C.Read, C.Functor, C.Foldable, C.Traversable)

type Arg = Arg' BNFC'Position
data Arg' a = Arg a (Type' a) Ident
  deriving (C.Eq, C.Ord, C.Show, C.Read, C.Functor, C.Foldable, C.Traversable)

data AbsArg = AbsArg AbsType Ident
  deriving (C.Eq, C.Ord, C.Show, C.Read)

type Block = Block' BNFC'Position
data Block' a = Block a [Stmt' a]
  deriving (C.Eq, C.Ord, C.Show, C.Read, C.Functor, C.Foldable, C.Traversable)

type Stmt = Stmt' BNFC'Position
data Stmt' a
    = Empty a
    | BStmt a (Block' a)
    | Decl a (Type' a) [Item' a]
    | Ass a Ident (Expr' a)
    | ArrAss a Ident (Expr' a) (Expr' a)
    | Incr a Ident
    | Decr a Ident
    | Ret a (Expr' a)
    | VRet a
    | Cond a (Expr' a) (Stmt' a)
    | CondElse a (Expr' a) (Stmt' a) (Stmt' a)
    | While a (Expr' a) (Stmt' a)
    | Break a
    | Continue a
    | SExp a (Expr' a)
    | ForTo a Ident (Expr' a) (Expr' a) (Stmt' a)
    | Print a (Expr' a)
  deriving (C.Eq, C.Ord, C.Show, C.Read, C.Functor, C.Foldable, C.Traversable)

type Item = Item' BNFC'Position
data Item' a = NoInit a Ident | Init a Ident (Expr' a)
  deriving (C.Eq, C.Ord, C.Show, C.Read, C.Functor, C.Foldable, C.Traversable)

type Type = Type' BNFC'Position
data Type' a
    = IntType a
    | StrTpye a
    | BoolType a
    | VoidType a
    | FunType a (Type' a) [Type' a]
    | ArrayType a (Type' a)
  deriving (C.Eq, C.Ord, C.Show, C.Read, C.Functor, C.Foldable, C.Traversable)

data AbsType
    = Int
    | Str
    | Bool
    | Void
    | Fun AbsType [AbsType]
    | Array AbsType
  deriving (C.Eq, C.Ord, C.Show, C.Read)

type Expr = Expr' BNFC'Position
data Expr' a
    = EArray a (Type' a) Integer
    | EArrElem a Ident (Expr' a)
    | ELambda a (Type' a) [Arg' a] (Block' a)
    | EVar a Ident
    | ELitInt a Integer
    | ELitTrue a
    | ELitFalse a
    | EApp a Ident [Expr' a]
    | EString a String
    | Neg a (Expr' a)
    | Not a (Expr' a)
    | EMul a (Expr' a) (MulOp' a) (Expr' a)
    | EAdd a (Expr' a) (AddOp' a) (Expr' a)
    | ERel a (Expr' a) (RelOp' a) (Expr' a)
    | EAnd a (Expr' a) (Expr' a)
    | EOr a (Expr' a) (Expr' a)
  deriving (C.Eq, C.Ord, C.Show, C.Read, C.Functor, C.Foldable, C.Traversable)

type AddOp = AddOp' BNFC'Position
data AddOp' a = Plus a | Minus a
  deriving (C.Eq, C.Ord, C.Show, C.Read, C.Functor, C.Foldable, C.Traversable)

type MulOp = MulOp' BNFC'Position
data MulOp' a = Times a | Div a
  deriving (C.Eq, C.Ord, C.Show, C.Read, C.Functor, C.Foldable, C.Traversable)

type RelOp = RelOp' BNFC'Position
data RelOp' a = LTH a | LE a | GTH a | GE a | EQU a | NE a
  deriving (C.Eq, C.Ord, C.Show, C.Read, C.Functor, C.Foldable, C.Traversable)

newtype Ident = Ident String
  deriving (C.Eq, C.Ord, C.Read, Data.String.IsString)

instance C.Show Ident where
  show (Ident str) = C.show str

type VarEnv = M.Map Ident (Location, Bool)
type LocEnv = M.Map Location LocVal
type TypeEnv = M.Map Ident AbsType
type LocMemory = (LocEnv, Location)
type ExpM a = ReaderT VarEnv Maybe a

type Closure = M.Map Ident LocVal

data LocVal = BoolVal Bool | IntegerVal Integer | StringVal String | VoidVal | FunVal AbsType [AbsArg] Block Closure | ArrVal AbsType (Array Integer LocVal)
  deriving (C.Show)

type Location = Integer

data Exception 
    = StringError BNFC'Position String
    | DivisionByZero BNFC'Position
    | NoLocation BNFC'Position Ident
    | IncorrectValue BNFC'Position Ident Integer
    | IndexOutOfBounds BNFC'Position Integer (Integer, Integer) Ident
    | ArrayAssignMismatch BNFC'Position Ident
    | IndexNotInteger BNFC'Position Ident
    | NotAnArray BNFC'Position Ident
    | TooManyArgs BNFC'Position Ident
    | NotEnoughArgs BNFC'Position Ident
    | NoValueReturned BNFC'Position Ident AbsType
    | WrongValueReturned BNFC'Position Ident AbsType AbsType
    | NotAFunction BNFC'Position Ident
    | ReadOnlyVariable BNFC'Position Ident
  deriving (C.Eq, C.Show)

data TypeCheckingError
    = CustomTypeError BNFC'Position String
    | WrongMainTypeError BNFC'Position
    | WrongInitType BNFC'Position Ident AbsType AbsType
    | NoIdentifierFound BNFC'Position Ident
    | ExpressionVariableMismatch BNFC'Position Ident
    | ExpressionArrayMismatch BNFC'Position Ident
    | NonIntegerIndex BNFC'Position Ident
    | NotAnArrayType BNFC'Position Ident
    | IncrementNonInteger BNFC'Position Ident
    | DecrementNonInteger BNFC'Position Ident
    | WrongReturnType BNFC'Position AbsType AbsType
    | WrongVoidReturn BNFC'Position AbsType
    | WrongConditionType BNFC'Position AbsType
    | WrongForBeginType BNFC'Position
    | WrongForEndType BNFC'Position
    | TooManyArgsType BNFC'Position Ident
    | NotEnoughArgsType BNFC'Position Ident
    | FunArgumentTypeMismatch BNFC'Position Integer Ident AbsType AbsType
    | NotAFunctionType BNFC'Position Ident
    | ArithNegationType BNFC'Position AbsType
    | LogicNegationType BNFC'Position AbsType
    | FirstOperandShouldBeType BNFC'Position AbsType AbsType
    | SecondOperandShouldBeType BNFC'Position AbsType AbsType
  deriving (C.Eq, C.Show)

type ReturnVal = Maybe LocVal

type InterpretingMonadIO = ReaderT Arabica.Abs.VarEnv (StateT Arabica.Abs.LocMemory (ExceptT Arabica.Abs.Exception IO))
type TypeCheckingMonadIO = ReaderT Arabica.Abs.TypeEnv (ExceptT Arabica.Abs.TypeCheckingError IO)
type Result = InterpretingMonadIO LocVal
type StmtState = (Arabica.Abs.VarEnv, Arabica.Abs.ReturnVal, Arabica.Abs.LoopState)

data LoopState = BreakState | ContState | NoLoopState
  deriving (C.Show, C.Eq)

-- | Start position (line, column) of something.

type BNFC'Position = C.Maybe (C.Int, C.Int)

pattern BNFC'NoPosition :: BNFC'Position
pattern BNFC'NoPosition = C.Nothing

pattern BNFC'Position :: C.Int -> C.Int -> BNFC'Position
pattern BNFC'Position line col = C.Just (line, col)

-- | Get the start position of something.

class HasPosition a where
  hasPosition :: a -> BNFC'Position

instance HasPosition Program where
  hasPosition = \case
    Program p _ -> p

instance HasPosition TopDef where
  hasPosition = \case
    FnDef p _ _ _ _ -> p

instance HasPosition Arg where
  hasPosition = \case
    Arg p _ _ -> p

instance HasPosition Block where
  hasPosition = \case
    Block p _ -> p

instance HasPosition Stmt where
  hasPosition = \case
    Empty p -> p
    BStmt p _ -> p
    Decl p _ _ -> p
    Ass p _ _ -> p
    ArrAss p _ _ _ -> p
    Incr p _ -> p
    Decr p _ -> p
    Ret p _ -> p
    VRet p -> p
    Cond p _ _ -> p
    CondElse p _ _ _ -> p
    While p _ _ -> p
    Break p -> p
    Continue p -> p
    SExp p _ -> p
    ForTo p _ _ _ _ -> p
    Print p _ -> p

instance HasPosition Item where
  hasPosition = \case
    NoInit p _ -> p
    Init p _ _ -> p

instance HasPosition Type where
  hasPosition = \case
    IntType p -> p
    StrTpye p -> p
    BoolType p -> p
    VoidType p -> p
    FunType p _ _ -> p
    ArrayType p _ -> p

instance HasPosition Expr where
  hasPosition = \case
    EArray p _ _ -> p
    EArrElem p _ _ -> p
    ELambda p _ _ _ -> p
    EVar p _ -> p
    ELitInt p _ -> p
    ELitTrue p -> p
    ELitFalse p -> p
    EApp p _ _ -> p
    EString p _ -> p
    Neg p _ -> p
    Not p _ -> p
    EMul p _ _ _ -> p
    EAdd p _ _ _ -> p
    ERel p _ _ _ -> p
    EAnd p _ _ -> p
    EOr p _ _ -> p

instance HasPosition AddOp where
  hasPosition = \case
    Plus p -> p
    Minus p -> p

instance HasPosition MulOp where
  hasPosition = \case
    Times p -> p
    Div p -> p

instance HasPosition RelOp where
  hasPosition = \case
    LTH p -> p
    LE p -> p
    GTH p -> p
    GE p -> p
    EQU p -> p
    NE p -> p

instance HasPosition TypeCheckingError where
  hasPosition = \case
    CustomTypeError p _ -> p
    WrongMainTypeError p -> p
    WrongInitType p _ _ _ -> p
    NoIdentifierFound p _ -> p
    ExpressionVariableMismatch p _ -> p
    ExpressionArrayMismatch p _ -> p
    NonIntegerIndex p _ -> p
    NotAnArrayType p _ -> p
    IncrementNonInteger p _ -> p
    DecrementNonInteger p _ -> p
    WrongReturnType p _ _ -> p
    WrongVoidReturn p _ -> p
    WrongConditionType p _ -> p
    WrongForBeginType p -> p
    WrongForEndType p -> p
    TooManyArgsType p _ -> p
    NotEnoughArgsType p _ -> p
    FunArgumentTypeMismatch p _ _ _ _ -> p
    NotAFunctionType p _ -> p
    ArithNegationType p _ -> p
    LogicNegationType p _ -> p
    FirstOperandShouldBeType p _ _ -> p
    SecondOperandShouldBeType p _ _ -> p

