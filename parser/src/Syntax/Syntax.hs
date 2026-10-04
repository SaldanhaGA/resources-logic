module Syntax.Syntax where

newtype Ident = Ident { unIdent :: String } deriving (Eq, Ord, Show)

data Program
  = Program BExp Stmt BExp AExp
    deriving (Eq, Ord, Show)

data Stmt
    = Skip
    | Assign Ident AExp
    | ArrAssign Ident AExp AExp
    | Seq Stmt Stmt
    | Ite BExp Stmt Stmt
    | While BExp Stmt
    deriving (Eq, Ord, Show)

data AExp
    = Num Int
    | Var Ident
    | Arr Ident AExp
    | Add AExp AExp
    | Sub AExp AExp
    | Mul AExp AExp
    | Div AExp AExp
    | Pow AExp AExp
    | Sum Ident AExp AExp AExp
    deriving (Eq, Ord, Show)

data BExp
    = BTrue
    | BFalse
    | Eq AExp AExp
    | Ne AExp AExp
    | Lt AExp AExp
    | Gt AExp AExp
    | Le AExp AExp
    | Ge AExp AExp
    | Neg BExp
    | And BExp BExp
    | Or BExp BExp
    deriving (Eq, Ord, Show)

mkFor :: Ident -> AExp -> AExp -> Stmt -> Stmt
mkFor i a b s = Seq (Assign i a) 
                    (While (Lt (Var i) b) 
                           (Seq s (Assign i (Add (Var i) (Num 1)))))

class Idents a where 
  idents :: a -> [Ident]

instance Idents Stmt where 
    idents Skip = []
    idents (Assign i _) = [i]
    idents (ArrAssign i _ _) = [i]
    idents (Seq s1 s2) = idents s1 ++ idents s2
    idents (Ite _ bt be) = idents bt ++ idents be
    idents (While _ bw) = idents bw 
