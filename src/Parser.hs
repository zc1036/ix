
{-# LANGUAGE NamedFieldPuns #-}

module Parser where

import Text.ParserCombinators.Parsec
import System.Environment
import Control.Monad
import Data.Maybe
import Data.List (intercalate)
import Text.Printf

-- AST types

data SExpr a = IntLiteral a Integer
             | FloatLiteral a Float
             | SymbolLiteral a String
             | StringLiteral a String
             | Nil a
             | Cons a (SExpr a) (SExpr a)

sexprdata :: SExpr a -> a
sexprdata (IntLiteral x _) = x
sexprdata (FloatLiteral x _) = x
sexprdata (SymbolLiteral x _) = x
sexprdata (StringLiteral x _) = x    
sexprdata (Nil x) = x
sexprdata (Cons x _ _) = x

instance (Show a) => Show (SExpr a) where
    show (IntLiteral _ x) = show x
    show (FloatLiteral _ x) = show x
    show (SymbolLiteral _ x) = show x
    show (StringLiteral _ x) = show x
    show (Nil _) = "()"
    show (Cons _ l r) = "(" ++ (show l) ++ " . " ++ (show r) ++ ")"

-- Parser functions

symbolChars :: String
symbolChars = ".!$%&|*+-/:<=>?@^_~" ++ ['a'..'z'] ++ ['A'..'Z'] ++ ['0'..'9']

lispsymbol :: Parser (SExpr ())
lispsymbol = liftM (SymbolLiteral ()) (many1 (oneOf symbolChars))

integer :: Parser (SExpr ())
integer = liftM ((IntLiteral ()) . Prelude.read) (many1 digit)

float :: Parser (SExpr ())
float = do
  whole <- many1 digit
  char '.'
  fraction <- many1 digit
  return (FloatLiteral () (Prelude.read $ whole ++ "." ++ fraction))

number :: Parser (SExpr ())
number = do
  n <- try float <|> integer
  notFollowedBy (oneOf symbolChars)
  return n

listEnd :: Parser [SExpr ()]
listEnd = return []

listBody :: Parser [SExpr ()]
listBody = do
  car <- expr
  spaces
  cdr <- try listBody <|> listEnd
  return (car:cdr)

tocons (x:xs) rest = tocons xs (Cons () rest x)
tocons [] rest = rest

list :: Parser (SExpr ())
list = do
  whitespace
  char '('
  whitespace
  body <- try listBody <|> listEnd
  whitespace
  char ')'
  return $ tocons body (Nil ())

{-|
structLiteral :: Parser SExpr
structLiteral = do
  whitespace
  char '{'
  whitespace
  body <- try listBody <|> listEnd
  whitespace
  char '}'
  return (StructLiteral body)
|-}

escapedChar :: Parser Char
escapedChar = (char '\\') >> (oneOf "rtn\\\"")

stringlit :: Parser (SExpr ())
stringlit = do
  char '"'
  contents <- manyTill ((try escapedChar) <|> (noneOf "\"\\")) (char '"')
  return (StringLiteral () contents)

comment :: Parser ()
comment = do
  string "--"
  manyTill anyChar ((eof >> return '\n') <|> (char '\n'))
  return ()

comments :: Parser ()
comments = skipMany (comment >> whitespace)

expr :: Parser (SExpr ())
expr = number
       <|> stringlit
       <|> lispsymbol
       <|> list
--       <|> structLiteral

whitespace :: Parser ()
whitespace = skipMany space

readAll :: Parser (SExpr ())
readAll = do
  whitespace
  comments
  result <- many $ do
              e <- expr
              whitespace
              comments
              return e
  eof
  return $ tocons result (Nil ())

parseToplevel :: String -> Either ParseError (SExpr ())
parseToplevel input = parse readAll "lisp" input
