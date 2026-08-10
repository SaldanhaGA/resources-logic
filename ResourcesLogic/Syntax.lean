import ResourcesLogic.State

namespace ResourcesLogic

inductive AExp where
  | num : Int → AExp
  | var : Ident → AExp

  | arr : Ident → AExp → AExp
  | add : AExp → AExp → AExp
  | sub : AExp → AExp → AExp
  | mul : AExp → AExp → AExp
  | div : AExp → AExp → AExp
  | pow : AExp → AExp → AExp

  | sum : Ident → AExp → AExp → AExp → AExp
  deriving Repr

inductive BExp where
  | tt : BExp
  | ff : BExp
  | eq : AExp → AExp → BExp
  | ne : AExp → AExp → BExp
  | lt : AExp → AExp → BExp
  | gt : AExp → AExp → BExp
  | le : AExp → AExp → BExp
  | ge : AExp → AExp → BExp
  | neg : BExp → BExp
  | and : BExp → BExp → BExp
  | or : BExp → BExp → BExp
  deriving Repr

inductive Stmt where
  | skip : Stmt

  | assign : Ident → AExp → Stmt

  | arrAssign : Ident → AExp → AExp → Stmt
  | seq : Stmt → Stmt → Stmt
  | ite : BExp → Stmt → Stmt → Stmt
  | while : BExp → Stmt → Stmt
  deriving Repr

namespace Stmt

def «for» (i : Ident) (a b : AExp) (S : Stmt) : Stmt :=
  .seq (.assign i a)
    (.while (.lt (.var i) b)
      (.seq S (.assign i (.add (.var i) (.num 1)))))

end Stmt

end ResourcesLogic
