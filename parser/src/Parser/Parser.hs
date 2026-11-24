module Parser.Parser where

import Data.Void
import Text.Megaparsec hiding (Token)
import Control.Monad.Combinators.Expr

import Lexer.Lexer
import Syntax.Syntax

type Parser = Parsec Void [Token]

matchLex :: Lexeme -> Parser ()
matchLex lx = satisfy (\(Token _ l) -> l == lx) *> pure ()

pVar :: Parser Var
pVar = do
  Token _ lexeme <- satisfy isIdent
  case lexeme of
    TIdent s -> return s
    _        -> empty
  where
    isIdent (Token _ (TIdent _)) = True
    isIdent _                    = False

pNum :: Parser Int
pNum = do
  Token _ lexeme <- satisfy isNum
  case lexeme of
    TNumber n -> return n
    _         -> empty
  where
    isNum (Token _ (TNumber _)) = True
    isNum _                     = False

-------------------------------------------------------------------------------

pGrowth :: Parser Growth
pGrowth = do
  matchLex TO
  matchLex TLParen
  g <- choice
    [ Const <$ matchLex (TNumber 1)
    , try pNLogN
    , try pExp
    , try pPoly
    , Log   <$ (matchLex TLog *> pVar)
    , Lin   <$ pVar
    ]
  matchLex TRParen
  return g
  where
    pNLogN = do
      _ <- pVar
      matchLex TLog
      _ <- pVar
      return NLogN

    pExp = do
      n <- pNum
      if n == 2
        then matchLex TPow *> pVar *> pure Exp
        else empty

    pPoly = do
      _ <- pVar
      matchLex TPow
      k <- pNum
      return (Poly k)

-------------------------------------------------------------------------------

pInputGen :: Parser InputGen
pInputGen = do
  v <- pVar
  matchLex TAssign
  e <- aexp
  optional (matchLex TSemi)
  return (GenAssign v e)

pSpec :: Parser Spec
pSpec = do
  matchLex TProgram
  name <- pVar
  matchLex TSize
  size <- pVar
  matchLex TInputs
  matchLex TLBrace
  gens <- many pInputGen
  matchLex TRBrace
  matchLex TComplexity
  growth <- pGrowth
  return (Spec name size gens growth)

-------------------------------------------------------------------------------

stmt :: Parser Stmt
stmt = do
  stmts <- sepBy1 stmtSingle (matchLex TSemi)
  return (foldr1 Seq stmts)

stmtSingle :: Parser Stmt
stmtSingle = choice
  [ pSkip
  , try pArrAssign
  , pAssign
  , pIf
  , pWhile
  , between (matchLex TLBrace) (matchLex TRBrace) stmt
  ]

pSkip :: Parser Stmt
pSkip = Skip <$ matchLex TSkip

pAssign :: Parser Stmt
pAssign = do
  i <- pVar
  matchLex TAssign
  e <- aexp
  return (Assign i e)

pArrAssign :: Parser Stmt
pArrAssign = do
  i <- pVar
  matchLex TLBracket
  idx <- aexp
  matchLex TRBracket
  matchLex TAssign
  val <- aexp
  return (ArrAssign i idx val)

pIf :: Parser Stmt
pIf = do
  matchLex TIf
  cond <- bexp
  matchLex TThen
  thn <- stmtSingle
  matchLex TElse
  els <- stmtSingle
  return (If cond thn els)

pWhile :: Parser Stmt
pWhile = do
  matchLex TWhile
  cond <- bexp
  matchLex TDo
  body <- stmtSingle
  return (While cond body)

-------------------------------------------------------------------------------

aexp :: Parser AExp
aexp = makeExprParser aTerm aTable

aTerm :: Parser AExp
aTerm = choice
  [ Num <$> pNum
  , pSum
  , try pArrAccess
  , Var <$> pVar
  , between (matchLex TLParen) (matchLex TRParen) aexp
  ]

pArrAccess :: Parser AExp
pArrAccess = do
  i <- pVar
  matchLex TLBracket
  idx <- aexp
  matchLex TRBracket
  return (ArrAccess i idx)

pSum :: Parser AExp
pSum = do
  matchLex TSum
  v <- pVar
  start <- aTerm
  end <- aTerm
  body <- aTerm
  return (Sum v start end body)

aTable :: [[Operator Parser AExp]]
aTable =
  [ [ InfixR (Pow <$ matchLex TPow) ]
  , [ InfixL (Mul <$ matchLex TTimes)
    , InfixL (Div <$ matchLex TDiv) ]
  , [ InfixL (Add <$ matchLex TPlus)
    , InfixL (Sub <$ matchLex TMinus) ]
  ]

-------------------------------------------------------------------------------

bexp :: Parser BExp
bexp = makeExprParser bTerm bTable

bTerm :: Parser BExp
bTerm = choice
  [ BTrue  <$ matchLex TTrue
  , BFalse <$ matchLex TFalse
  , try pComparison
  , between (matchLex TLParen) (matchLex TRParen) bexp
  ]

pComparison :: Parser BExp
pComparison = do
  a1 <- aexp
  op <- choice
    [ Eq <$ matchLex TEq
    , Ne <$ matchLex TNe
    , Le <$ matchLex TLe
    , Ge <$ matchLex TGe
    , Lt <$ matchLex TLt
    , Gt <$ matchLex TGt
    ]
  a2 <- aexp
  return (op a1 a2)

bTable :: [[Operator Parser BExp]]
bTable =
  [ [ Prefix (Not <$ matchLex TNot) ]
  , [ InfixL (And <$ matchLex TAnd) ]
  , [ InfixL (Or  <$ matchLex TOr) ]
  ]

-------------------------------------------------------------------------------

pProg :: Parser Program
pProg = do
  spec <- pSpec
  body <- stmt
  return (Program spec body)

parseProgram :: String -> [Token] -> Either (ParseErrorBundle [Token] Void) Program
parseProgram fileName tokens = runParser (pProg <* matchLex TEOF) fileName tokens