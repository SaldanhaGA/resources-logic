# Syntax Tree Definition (AST)

This documentation describes the grammar of the programming language, divided into four main categories: **Programs (Prog)**, **Statements (Stmt)**, **Arithmetic Expressions (AExp)**, and **Boolean Expressions (BExp)**.

## Grammar Overview

Below is the formal grammar definition in BNF (Backus-Naur Form) format:

```
Prog    -> '{' BExp '}' Stmt '{' BExp '|' AExp '}'

Stmt    -> '{' Stmt '}'
        |  'skip' ';'
        |  Ident '=' AExp ';'
        |  Ident '[' AExp ']' '=' AExp ';'
        |  Stmt ';' Stmt
        |  'if' '(' BExp ')' Stmt
        |  'if' '(' BExp ')' Stmt 'else' Stmt
        |  'while' '(' BExp ')' Stmt
        |  'for' '(' Ident '=' AExp 'to' AExp ')' Stmt

AExp    -> Int
        |  Ident
        |  Ident '[' AExp ']'
        |  AExp '+' AExp
        |  AExp '-' AExp
        |  AExp '*+*' AExp
        |  AExp '/' AExp
        |  AExp '^' AExp
        |  'sum' Ident 'from' AExp 'to' AExp 'in' AExp

BExp    -> 'true'
        |  'false'
        |  AExp '==' AExp
        |  AExp '!=' AExp
        |  AExp '<' AExp
        |  AExp '>' AExp
        |  AExp '<=' AExp
        |  AExp '>=' AExp
        |  '!' BExp
        |  BExp '&&' BExp
        |  BExp '||' BExp
```

## Rule Breakdown

### 1. Programs (`Prog`)

Programs represent a complete execution block annotated with Hoare Logic specifications, used for formal verification and resource analysis.

| Syntax | Description | 
| ----- | ----- | 
| `{ BExp } Stmt { BExp \| AExp }` | A Hoare Logic triple where the first `BExp` is the **precondition**, `Stmt` is the program to be executed, the second `BExp` is the **postcondition**, and `AExp` represents an additional quantitative measure (such as cost, resource bound, or a variant). | 

### 2. Statements (`Stmt`)

Statements define the execution flow and state-altering operations of the language.

| Syntax | Description | 
| ----- | ----- | 
| `{ Stmt }` | Block of statements (groups multiple statements within a scope). | 
| `skip ;` | Null operation (no-op). Does nothing. | 
| `Ident = AExp ;` | Assignment of an expression to a variable. | 
| `Ident[AExp] = AExp ;` | Assignment of a value to a specific position in an array/vector. | 
| `Stmt ; Stmt` | Statement sequencing. | 
| `if (BExp) Stmt` | Simple conditional structure. | 
| `if (BExp) Stmt else Stmt` | Complete conditional structure (with an alternative branch). | 
| `while (BExp) Stmt` | Condition-based loop (executes while the condition is true). | 
| `for (Ident = AExp to AExp) Stmt` | Loop with a delimited counter. | 

### 3. Arithmetic Expressions (`AExp`)

Represent numeric values, variables, and mathematical operations.

| Syntax | Description | 
| ----- | ----- | 
| `Int` | Literal integer value (e.g., `1`, `42`). | 
| `Ident` | Identifier / Variable name. | 
| `Ident[AExp]` | Access to an array/vector element at the specified index. | 
| `AExp + AExp` | Addition. | 
| `AExp - AExp` | Subtraction. | 
| `AExp *+* AExp` | Multiplication (or custom operator). | 
| `AExp / AExp` | Division. | 
| `AExp ^ AExp` | Exponentiation. | 
| `sum Ident from AExp to AExp in AExp` | Summation operation (Mathematical sum loop). | 

### 4. Boolean Expressions (`BExp`)

Represent logical evaluations that result in `true` or `false`.

| Syntax | Description | 
| ----- | ----- | 
| `true` / `false` | Literal boolean values. | 
| `AExp == AExp` | Mathematical equality. | 
| `AExp != AExp` | Inequality (not equal). | 
| `AExp < AExp` | Less than. | 
| `AExp > AExp` | Greater than. | 
| `AExp <= AExp` | Less than or equal to. | 
| `AExp >= AExp` | Greater than or equal to. | 
| `! BExp` | Logical negation (NOT). | 
| `BExp && BExp` | Logical conjunction (AND). | 
| `BExp \|\| BExp` | Logical disjunction (OR). |