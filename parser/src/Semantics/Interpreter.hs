module Semantics.Interpreter where

import Syntax.Syntax
import Semantics.State

data ExecResult
  = Terminated Int State
  | BudgetExceeded Int
  | RuntimeError String
  deriving (Eq, Show)

evalAExp :: CostModel -> State -> AExp -> Either String (Int, Int)
evalAExp cm _  (Num n) = Right (n, costNum cm)
evalAExp cm st (Var v) = Right (lookupVar v st, costVar cm)
evalAExp cm st (ArrAccess v idxExp) = do
  (idx, cIdx) <- evalAExp cm st idxExp
  Right (lookupArr v idx st, cIdx + costArr cm)
evalAExp cm st (Add lExp rExp) = do
  (l, cL) <- evalAExp cm st lExp
  (r, cR) <- evalAExp cm st rExp
  Right (l + r, cL + cR + costAdd cm)
evalAExp cm st (Sub lExp rExp) = do
  (l, cL) <- evalAExp cm st lExp
  (r, cR) <- evalAExp cm st rExp
  Right (l - r, cL + cR + costSub cm)
evalAExp cm st (Mul lExp rExp) = do
  (l, cL) <- evalAExp cm st lExp
  (r, cR) <- evalAExp cm st rExp
  Right (l * r, cL + cR + costMul cm)
evalAExp cm st (Div lExp rExp) = do
  (l, cL) <- evalAExp cm st lExp
  (r, cR) <- evalAExp cm st rExp
  if r == 0
    then Left "Division by zero"
    else Right (l `div` r, cL + cR + costDiv cm)
evalAExp cm st (Pow lExp rExp) = do
  (l, cL) <- evalAExp cm st lExp
  (r, cR) <- evalAExp cm st rExp
  if r < 0
    then Left "Negative exponent"
    else Right (l ^ r, cL + cR + costExp cm)
evalAExp cm st (Sum v startExp endExp bodyExp) = do
  (start, cStart) <- evalAExp cm st startExp
  (end, cEnd)     <- evalAExp cm st endExp
  let go idx acc costAcc
        | idx > end = Right (acc, costAcc)
        | otherwise = do
            let st' = updateVar v idx st
            (vBody, cBody) <- evalAExp cm st' bodyExp
            go (idx + 1) (acc + vBody) (costAcc + cBody)
  go start 0 (cStart + cEnd)

evalBExp :: CostModel -> State -> BExp -> Either String (Bool, Int)
evalBExp cm _  BTrue  = Right (True, costTrue cm)
evalBExp cm _  BFalse = Right (False, costFalse cm)
evalBExp cm st (Eq lExp rExp) = do
  (l, cL) <- evalAExp cm st lExp
  (r, cR) <- evalAExp cm st rExp
  Right (l == r, cL + cR + costEq cm)
evalBExp cm st (Ne lExp rExp) = do
  (l, cL) <- evalAExp cm st lExp
  (r, cR) <- evalAExp cm st rExp
  Right (l /= r, cL + cR + costNe cm)
evalBExp cm st (Lt lExp rExp) = do
  (l, cL) <- evalAExp cm st lExp
  (r, cR) <- evalAExp cm st rExp
  Right (l < r, cL + cR + costLt cm)
evalBExp cm st (Gt lExp rExp) = do
  (l, cL) <- evalAExp cm st lExp
  (r, cR) <- evalAExp cm st rExp
  Right (l > r, cL + cR + costGt cm)
evalBExp cm st (Le lExp rExp) = do
  (l, cL) <- evalAExp cm st lExp
  (r, cR) <- evalAExp cm st rExp
  Right (l <= r, cL + cR + costLe cm)
evalBExp cm st (Ge lExp rExp) = do
  (l, cL) <- evalAExp cm st lExp
  (r, cR) <- evalAExp cm st rExp
  Right (l >= r, cL + cR + costGe cm)
evalBExp cm st (And lExp rExp) = do
  (l, cL) <- evalBExp cm st lExp
  (r, cR) <- evalBExp cm st rExp
  Right (l && r, cL + cR + costAnd cm)
evalBExp cm st (Or lExp rExp) = do
  (l, cL) <- evalBExp cm st lExp
  (r, cR) <- evalBExp cm st rExp
  Right (l || r, cL + cR + costOr cm)
evalBExp cm st (Not bExp) = do
  (b, cB) <- evalBExp cm st bExp
  Right (not b, cB + costNeg cm)

evalStmt :: CostModel -> Int -> Int -> State -> Stmt -> ExecResult
evalStmt cm cap costAcc st stmt
  | costAcc > cap = BudgetExceeded costAcc
  | otherwise = case stmt of
      Skip ->
        checkCap cap (costAcc + costSkip cm) st

      Assign v valExp ->
        case evalAExp cm st valExp of
          Left err          -> RuntimeError err
          Right (val, cVal) ->
            checkCap cap (costAcc + cVal + costAssV cm) (updateVar v val st)

      ArrAssign v idxExp valExp ->
        case do
          (idx, cIdx) <- evalAExp cm st idxExp
          (val, cVal) <- evalAExp cm st valExp
          Right (idx, val, cIdx + cVal)
        of
          Left err            -> RuntimeError err
          Right (idx, val, c) ->
            checkCap cap (costAcc + c + costAssA cm) (updateArr v idx val st)

      Seq s1 s2 ->
        case evalStmt cm cap costAcc st s1 of
          Terminated c1 st' -> evalStmt cm cap c1 st' s2
          BudgetExceeded c1 -> BudgetExceeded c1
          RuntimeError err  -> RuntimeError err

      If condExp s1 s2 ->
        case evalBExp cm st condExp of
          Left err -> RuntimeError err
          Right (cond, cCond) ->
            let c = costAcc + cCond
            in if c > cap
                 then BudgetExceeded c
                 else if cond
                   then evalStmt cm cap c st s1
                   else evalStmt cm cap c st s2

      While condExp body ->
        case evalBExp cm st condExp of
          Left err -> RuntimeError err
          Right (cond, cCond) ->
            let c = costAcc + cCond
            in if c > cap
                 then BudgetExceeded c
                 else if not cond
                   then Terminated c st
                   else case evalStmt cm cap c st body of
                     Terminated cBody stBody -> evalStmt cm cap cBody stBody (While condExp body)
                     other                   -> other

checkCap :: Int -> Int -> State -> ExecResult
checkCap cap newCap st
  | cap >= newCap = Terminated newCap st
  | otherwise     = BudgetExceeded newCap

runProgram :: CostModel -> Int -> State -> Program -> ExecResult
runProgram cm cap initSt (Program _ body) = evalStmt cm cap 0 initSt body