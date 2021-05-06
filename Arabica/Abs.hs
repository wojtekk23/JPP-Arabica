-- Haskell data types for the abstract syntax.
-- Generated by the BNF converter.

{-# LANGUAGE GeneralizedNewtypeDeriving #-}

-- | The abstract syntax of language arabica.

module Arabica.Abs where

import Prelude (Integer, String, Bool)
import qualified Prelude as C (Eq, Ord, Show, Read)
import qualified Data.String

data Program = Program [TopDef]
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data TopDef = FnDef Type Ident [Arg] Block
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data Arg = Arg Type Ident
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data Block = Block [Stmt]
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data Stmt
    = Empty
    | BStmt Block
    | Decl Type [Item]
    | Ass Ident Expr
    | ArrAss Ident Expr Expr
    | Incr Ident
    | Decr Ident
    | Ret Expr
    | VRet
    | Cond Expr Stmt
    | CondElse Expr Stmt Stmt
    | While Expr Stmt
    | Break
    | Continue
    | SExp Expr
    | ForTo Item Expr Stmt
    | Print Expr
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data Item = NoInit Ident | Init Ident Expr
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data Type = Int | Str | Bool | Void | Fun Type [Type] | Array Type
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data Expr
    = EArray Type Integer
    | EArrElem Ident Expr
    | ELambda Type [Arg] Block
    | EVar Ident
    | ELitInt Integer
    | ELitTrue
    | ELitFalse
    | EApp Ident [Expr]
    | EString String
    | Neg Expr
    | Not Expr
    | EMul Expr MulOp Expr
    | EAdd Expr AddOp Expr
    | ERel Expr RelOp Expr
    | EAnd Expr Expr
    | EOr Expr Expr
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data AddOp = Plus | Minus
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data MulOp = Times | Div
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data RelOp = LTH | LE | GTH | GE | EQU | NE
  deriving (C.Eq, C.Ord, C.Show, C.Read)

newtype Ident = Ident String
  deriving (C.Eq, C.Ord, C.Show, C.Read, Data.String.IsString)

data LocVal = BoolVal Bool | IntegerVal Integer | StringVal String | VoidVal

