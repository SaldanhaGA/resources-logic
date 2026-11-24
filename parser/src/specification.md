# Syntax Tree Definition (AST)

This documentation describes the abstract syntax tree (AST) defined in `Syntax.Syntax`. The language structure is organized into: **Programs (`Program`)**, **Specifications (`Spec`)**, **Input Generators (`InputGen`)**, **Complexity Classes (`Growth`)**, **Statements (`Stmt`)**, **Arithmetic Expressions (`AExp`)**, and **Boolean Expressions (`BExp`)**.

## Grammar Overview

Below is the formal grammar definition in BNF format corresponding to the Haskell AST:

```bnf
Program   -> 'program' Ident 'size' Var 'inputs' '{' InputGen* '}' 'complexity' Growth Stmt

InputGen  -> Var ':=' AExp

Growth    -> 'O(1)'
          |  'O(log n)'
          |  'O(n)'
          |  'O(n log n)'
          |  'O(n^' Int ')'
          |  'O(2^n)'

Stmt      -> 'skip'
          |  Var ':=' AExp
          |  Var '[' AExp ']' ':=' AExp
          |  Stmt ';' Stmt
          |  'if' BExp 'then' Stmt 'else' Stmt
          |  'while' BExp 'do' Stmt

AExp      -> Int
          |  Var
          |  Var '[' AExp ']'
          |  AExp '+' AExp
          |  AExp '-' AExp
          |  AExp '*' AExp
          |  AExp '/' AExp
          |  AExp '^' AExp
          |  'sum' Var AExp AExp AExp

BExp      -> 'true'
          |  'false'
          |  AExp '==' AExp
          |  AExp '!=' AExp
          |  AExp '<' AExp
          |  AExp '>' AExp
          |  AExp '<=' AExp
          |  AExp '>=' AExp
          |  BExp '&&' BExp
          |  BExp '||' BExp
          |  '!' BExp

```

---

## Rule Breakdown

### 1. Programs & Specifications (`Program`, `Spec`)

A program is composed of a metadata specification (`progSpec`) and an executable statement body (`progBory`).

| AST Constructor / Field | Syntax Example | Description |
| --- | --- | --- |
| `Program` | `program <name> ... <body>` | Wraps a `Spec` alongside the program body statement `Stmt`. |
| `progName :: String` | `program division` | Name identifier of the program. |
| `sizeParam :: Var` | `size n` | Declares the variable name representing input size. |
| `inputGens :: [InputGen]` | `inputs { ... }` | List of input initializers/generators. |
| `complexity :: Growth` | `complexity O(n)` | Target asymptotic complexity bound. |

### 2. Input Generators (`InputGen`)

Used within the `inputs { ... }` block to initialize program variables before execution.

| AST Constructor | Syntax Example | Description |
| --- | --- | --- |
| `GenAssign Var AExp` | `x := n + 1` | Assigns an arithmetic expression to an initial state variable. |

### 3. Asymptotic Growth (`Growth`)

Target complexity class declared in the specification header.

| AST Constructor | Concrete Syntax | Description |
| --- | --- | --- |
| `Const` | `O(1)` | Constant complexity. |
| `Log` | `O(log n)` | Logarithmic complexity. |
| `Lin` | `O(n)` | Linear complexity. |
| `NLogN` | `O(n log n)` | Linearithmic complexity. |
| `Poly Int` | `O(n^k)` | Polynomial complexity of degree $k$ ($k \ge 2$). |
| `Exp` | `O(2^n)` | Exponential complexity. |

### 4. Statements (`Stmt`)

Imperative statements defining control flow and memory mutations.

| AST Constructor | Concrete Syntax | Description |
| --- | --- | --- |
| `Skip` | `skip` | Null statement (no-op). |
| `Assign Var AExp` | `x := AExp` | Variable assignment. |
| `ArrAssign Var AExp AExp` | `a[AExp] := AExp` | Array element update at specified index. |
| `Seq Stmt Stmt` | `Stmt ; Stmt` | Sequential composition. |
| `If BExp Stmt Stmt` | `if BExp then Stmt else Stmt` | Conditional branching (both `then` and `else` branches required). |
| `While BExp Stmt` | `while BExp do Stmt` | While-loop iteration. |

### 5. Arithmetic Expressions (`AExp`)

Integer-valued expressions, variable reads, array lookups, and arithmetic operations.

| AST Constructor | Concrete Syntax | Description |
| --- | --- | --- |
| `Num Int` | `Int` | Integer literal. |
| `Var Var` | `x` | Variable lookup. |
| `ArrAccess Var AExp` | `a[AExp]` | Array element lookup. |
| `Add AExp AExp` | `AExp + AExp` | Addition. |
| `Sub AExp AExp` | `AExp - AExp` | Subtraction. |
| `Mul AExp AExp` | `AExp * AExp` | Multiplication. |
| `Div AExp AExp` | `AExp / AExp` | Integer division. |
| `Pow AExp AExp` | `AExp ^ AExp` | Exponentiation. |
| `Sum Var AExp AExp AExp` | `sum x a b body` | Summation over variable `x` from `a` to `b` evaluating `body`. |

### 6. Boolean Expressions (`BExp`)

Truth-valued predicates, comparison operations, and logical connectives.

| AST Constructor | Concrete Syntax | Description |
| --- | --- | --- |
| `BTrue` | `true` | Boolean constant true. |
| `BFalse` | `false` | Boolean constant false. |
| `Eq AExp AExp` | `AExp == AExp` | Relational equality. |
| `Ne AExp AExp` | `AExp != AExp` | Relational inequality. |
| `Lt AExp AExp` | `AExp < AExp` | Strictly less than. |
| `Gt AExp AExp` | `AExp > AExp` | Strictly greater than. |
| `Le AExp AExp` | `AExp <= AExp` | Less than or equal to. |
| `Ge AExp AExp` | `AExp >= AExp` | Greater than or equal to. |
| `And BExp BExp` | `BExp && BExp` | Logical conjunction (AND). |
| `Or BExp BExp` | `BExp || BExp` | Logical disjunction (OR). |
| `Not BExp` | `! BExp` | Logical negation (NOT). |