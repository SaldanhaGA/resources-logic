{
{-# OPTIONS_GHC -Wno-name-shadowing #-}
module Lexer.Lexer where
}

%wrapper "monad"

$digit = 0-9
$alpha = [a-zA-Z]

@identifier = $alpha [$alpha $digit]*
@number     = $digit+

tokens :-
      <0> $white+       ;
      
      <0> @number       {mkNumber}
      <0> "skip"        {simpleToken TSkip}
      <0> "="           {simpleToken TAssign}
      <0> "if"          {simpleToken TIf}
      <0> "else"        {simpleToken TElse}
      <0> "while"       {simpleToken TWhile}
      <0> "for"         {simpleToken TFor}
      <0> ";"           {simpleToken TSemi}
      <0> "("           {simpleToken TLParen}
      <0> ")"           {simpleToken TRParen}
      <0> "{"           {simpleToken TLBrace}
      <0> "}"           {simpleToken TRBrace}
      <0> "["           {simpleToken TLBracket}
      <0> "]"           {simpleToken TRBracket}
      <0> "+"           {simpleToken TPlus}
      <0> "-"           {simpleToken TMinus}
      <0> "*"           {simpleToken TTimes}
      <0> "/"           {simpleToken TDiv}
      <0> "^"           {simpleToken TPow}
      <0> "sum"         {simpleToken TSum}
      <0> "from"        {simpleToken TFrom}
      <0> "to"          {simpleToken TTo}
      <0> "in"          {simpleToken TIn}
      <0> "true"        {simpleToken TTrue}
      <0> "false"       {simpleToken TFalse}
      <0> "=="          {simpleToken TEq}
      <0> "!="          {simpleToken TNe}
      <0> "<"           {simpleToken TLt}
      <0> ">"           {simpleToken TGt}
      <0> "<="          {simpleToken TLe}
      <0> ">="          {simpleToken TGe}
      <0> "!"           {simpleToken TNot}
      <0> "&&"          {simpleToken TAnd}
      <0> "||"          {simpleToken TOr}
      <0> @identifier   {mkIdent}

{
alexEOF :: Alex Token
alexEOF = do
  (pos, _, _, _) <- alexGetInput
  pure $ Token (position pos) TEOF

data Token
  = Token {
      pos :: (Int, Int)
    , lexeme :: Lexeme 
    } deriving (Eq, Ord, Show)

data Lexeme    
  = TIdent String
  | TNumber Int
  | TAssign 
  | TIf 
  | TElse 
  | TWhile 
  | TFor
  | TSemi 
  | TLParen 
  | TRParen 
  | TLBrace 
  | TRBrace 
  | TLBracket 
  | TRBracket 
  | TPlus 
  | TTimes 
  | TMinus 
  | TDiv 
  | TPow
  | TSum
  | TFrom
  | TTo
  | TIn
  | TEq 
  | TNe
  | TLt 
  | TGt
  | TLe
  | TGe
  | TNot 
  | TAnd 
  | TOr
  | TTrue 
  | TFalse 
  | TSkip
  | TEOF
  deriving (Eq, Ord, Show)

position :: AlexPosn -> (Int, Int)
position (AlexPn _ line col) = (line, col)

mkIdent :: AlexAction Token 
mkIdent (st, _, _, str) len 
  = pure $ Token (position st) (TIdent (take len str))

mkNumber :: AlexAction Token
mkNumber (st, _, _, str) len 
  = pure $ Token (position st) (TNumber $ read $ take len str)

simpleToken :: Lexeme -> AlexAction Token
simpleToken lx (st, _, _, _) _
  = return $ Token (position st) lx

lexer :: String -> Either String [Token]
lexer s = runAlex s go 
  where 
    go = do 
      output <- alexMonadScan 
      if lexeme output == TEOF then 
        pure [output]
      else (output :) <$> go
}