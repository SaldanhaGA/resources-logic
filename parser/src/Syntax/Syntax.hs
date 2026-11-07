module Syntax.Syntax where

data Program
    = Program { 
        progSpec :: Spec,
        progBory :: Stmt
    } deriving (Eq, Show)

data Spec
    = Spec {
        progName   :: String,
        sizeParam  :: Var,
        inputGens  :: [InputGen],
        complexity :: Growth
    } deriving (Eq, Show)

type Var = String

data InputGen
    = GenAssign Var AExp
    deriving (Eq, Show)

data Growth
    = Const
    | Log
    | Lin
    | NLogN
    | Poly Int
    | Exp
    deriving (Eq, Ord, Show)

data AExp
    = Num Int
    | Var Var
    | ArrAccess Var AExp
    | Add AExp AExp
    | Sub AExp AExp
    | Mul AExp AExp
    | Div AExp AExp
    | Pow AExp AExp
    | Sum Var AExp AExp AExp
    deriving (Eq, Show)

data BExp
    = BTrue
    | BFalse
    | Eq  AExp AExp
    | Ne  AExp AExp
    | Lt  AExp AExp
    | Gt  AExp AExp
    | Le  AExp AExp
    | Ge  AExp AExp
    | And BExp BExp
    | Or  BExp BExp
    | Not BExp
    deriving (Eq, Show)

data Stmt
    = Skip
    | Assign Var AExp
    | ArrAssign Var AExp AExp
    | Seq Stmt Stmt
    | If BExp Stmt Stmt
    | While BExp Stmt
    deriving (Eq, Show)
