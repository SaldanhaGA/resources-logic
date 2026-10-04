module Parser.Parser where

import Data.Void
import Text.Megaparsec hiding (Token)
import Control.Monad.Combinators.Expr

import Lexer.Lexer
import Syntax.Syntax

type Parser = Parsec Void [Token]

matchLex :: Lexeme -> Parser ()
matchLex lx = satisfy (\(Token _ l) -> l == lx) *> pure ()

pIdent :: Parser Ident
pIdent = do
  Token _ lexeme <- satisfy isIdent
  case lexeme of
    TIdent s -> return (Ident s)
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

stmt :: Parser Stmt
stmt = do
  stmts <- some stmtSingle
  return (foldr1 Seq stmts)

stmtSingle :: Parser Stmt
stmtSingle = choice
  [ pBlock
  , pSkip
  , try pArrAssign
  , pAssign
  , pIf
  , pWhile
  , pFor
  ]

pBlock :: Parser Stmt
pBlock = do
  matchLex TLBrace
  stmts <- many stmtSingle
  matchLex TRBrace
  case stmts of
    [] -> return Skip
    _  -> return (foldr1 Seq stmts)

pSkip :: Parser Stmt
pSkip = Skip <$ (matchLex TSkip *> matchLex TSemi)

pAssign :: Parser Stmt
pAssign = do
  i <- pIdent
  matchLex TAssign
  e <- aexp
  matchLex TSemi
  return (Assign i e)

pArrAssign :: Parser Stmt
pArrAssign = do
  i <- pIdent
  matchLex TLBracket
  idx <- aexp
  matchLex TRBracket
  matchLex TAssign
  val <- aexp
  matchLex TSemi
  return (ArrAssign i idx val)

pIf :: Parser Stmt
pIf = do
  matchLex TIf
  matchLex TLParen
  cond <- bexp
  matchLex TRParen
  thn <- stmtSingle
  optEls <- optional (matchLex TElse *> stmtSingle)
  case optEls of
    Nothing  -> return (Ite cond thn Skip)
    Just els -> return (Ite cond thn els)

pWhile :: Parser Stmt
pWhile = do
  matchLex TWhile
  matchLex TLParen
  cond <- bexp
  matchLex TRParen
  body <- stmtSingle
  return (While cond body)

pFor :: Parser Stmt
pFor = do
  matchLex TFor
  matchLex TLParen
  i <- pIdent
  matchLex TAssign
  start <- aexp
  matchLex TTo
  end <- aexp
  matchLex TRParen
  body <- stmtSingle
  return (mkFor i start end body)

-------------------------------------------------------------------------------

aexp :: Parser AExp
aexp = makeExprParser aTerm aTable

aTerm :: Parser AExp
aTerm = choice
  [ Num <$> pNum
  , pSumLoop
  , try pArrAccess
  , Var <$> pIdent
  , between (matchLex TLParen) (matchLex TRParen) aexp
  ]

pArrAccess :: Parser AExp
pArrAccess = do
  i <- pIdent
  matchLex TLBracket
  idx <- aexp
  matchLex TRBracket
  return (Arr i idx)

pSumLoop :: Parser AExp
pSumLoop = do
  matchLex TSum
  i <- pIdent
  matchLex TFrom
  start <- aexp
  matchLex TTo
  end <- aexp
  matchLex TIn
  body <- aexp
  return (Sum i start end body)

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
    , Lt <$ matchLex TLt
    , Gt <$ matchLex TGt
    , Le <$ matchLex TLe
    , Ge <$ matchLex TGe
    ]
  a2 <- aexp
  return (op a1 a2)

bTable :: [[Operator Parser BExp]]
bTable =
  [ [ Prefix (Neg <$ matchLex TNot) ]
  , [ InfixL (And <$ matchLex TAnd) ]
  , [ InfixL (Or <$ matchLex TOr) ]
  ]


-------------------------------------------------------------------------------

parseProgram :: String -> [Token] -> Either (ParseErrorBundle [Token] Void) Program
parseProgram fileName tokens = runParser p fileName tokens
  where
    p = Program <$> stmt <* matchLex TEOF