import ResourcesLogic.State

namespace ResourcesLogic

structure CostModel where

  cst : Nat

  var : Nat

  array : Nat
  add : Nat
  sub : Nat
  mul : Nat
  div : Nat
  pow : Nat

  bool : Nat
  eq : Nat
  ne : Nat
  lt : Nat
  gt : Nat
  le : Nat
  ge : Nat

  neg : Nat

  and : Nat

  or : Nat

  skip : Nat

  assignV : Nat

  assignA : Nat

def unitModel : CostModel where
  cst := 1; var := 1; array := 1
  add := 1; sub := 1; mul := 1; div := 1; pow := 1
  bool := 1; eq := 1; ne := 1; lt := 1; gt := 1; le := 1; ge := 1
  neg := 1; and := 1; or := 1
  skip := 1; assignV := 1; assignA := 1

end ResourcesLogic
