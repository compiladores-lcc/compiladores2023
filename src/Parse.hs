{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use <$>" #-}
{-|
Module      : Parse
Description : Define un parser de términos FD40 a términos fully named.
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar
Stability   : experimental

-}

module Parse (tm, Parse.parse, SDecl, runP, P, program, declOrTm) where

import Prelude hiding ( const )
import Lang hiding (getPos)
import Common
import Text.Parsec hiding (runP,parse)
--import Data.Char ( isNumber, ord )
import qualified Text.Parsec.Token as Tok
import Text.ParserCombinators.Parsec.Language --( GenLanguageDef(..), emptyDef )
import qualified Text.Parsec.Expr as Ex
import Text.Parsec.Expr (Operator, Assoc)
import Control.Monad.Identity (Identity)

type P = Parsec String ()

-----------------------
-- Lexer
-----------------------
-- | Analizador de Tokens
lexer :: Tok.TokenParser u
lexer = Tok.makeTokenParser langDef

langDef :: LanguageDef u
langDef = emptyDef {
         commentLine    = "#",
         reservedNames = ["let", "rec","fun", "fix", "then", "else","in", "end",
                           "ifz", "if", "print","Nat","type"],
         reservedOpNames = ["->",":",";","=","+","-","!"]
        }

whiteSpace :: P ()
whiteSpace = Tok.whiteSpace lexer

natural :: P Integer 
natural = Tok.natural lexer

stringLiteral :: P String
stringLiteral = Tok.stringLiteral lexer

parens :: P a -> P a
parens = Tok.parens lexer

identifier :: P String
identifier = Tok.identifier lexer

reserved :: String -> P ()
reserved = Tok.reserved lexer

reservedOp :: String -> P ()
reservedOp = Tok.reservedOp lexer

tyIdentifier :: P String
tyIdentifier = Tok.lexeme lexer $ do
  c  <- upper
  cs <- many (identLetter langDef)
  return (c:cs)

-----------------------
-- Parsers
-----------------------

num :: P Int
num = fromInteger <$> natural

var :: P Name
var = identifier

getPos :: P Pos
getPos = do pos <- getPosition
            return $ Pos (sourceLine pos) (sourceColumn pos)

tyatom :: P STy
tyatom = (reserved "Nat" >> return SNatTy)
         <|> parens typeP

typeP :: P STy
typeP = try (do 
          x <- tyatom
          reservedOp "->"
          y <- typeP
          return (SFunTy x y))
      <|> tyatom -- TODO: Acomodar para que parsee synonyms también
          
const :: P Const
const = CNat <$> num

printOp :: P STerm
printOp = do
  i <- getPos
  reserved "print"
  str <- option "" stringLiteral
  a <- atom
  return (SPrint i str a)

unary :: String -> UnaryOp -> Operator String () Identity STerm
unary s f = Ex.Prefix (reservedOp s >> return (SUnaryOp NoPos f))

binary :: String -> BinaryOp -> Assoc -> Operator String () Identity STerm
binary s f = Ex.Infix (reservedOp s >> return (SBinaryOp NoPos f))

table :: [ [Operator String () Identity STerm] ]
table = [ [ unary "!" Bang],
          [ binary "+" Add Ex.AssocLeft,
            binary "-" Sub Ex.AssocLeft] ]

expr :: P STerm
expr = Ex.buildExpressionParser table tm

atom :: P STerm
atom =     (flip SConst <$> const <*> getPos)
       <|> flip SV <$> var <*> getPos
       <|> parens expr
       <|> printOp

-- parsea un par (variable : tipo)
binding :: P (Name, STy)
binding = do v <- var
             reservedOp ":"
             ty <- typeP
             return (v, ty)

bindings :: P [(Name, STy)]
bindings = do many1 $ parens binding


lam :: P STerm
lam = do i <- getPos
         reserved "fun"
         mb <- bindings
         reservedOp "->"
         t <- expr
         return (SLam i mb t)

-- Nota el parser app también parsea un solo atom.
app :: P STerm
app = do i <- getPos
         f <- atom
         args <- many atom
         return (foldl (SApp i) f args)

ifz :: P STerm
ifz = do i <- getPos
         reserved "ifz"
         c <- expr
         reserved "then"
         t <- expr
         reserved "else"
         e <- expr
         return (SIfZ i c t e)

if_ :: P STerm
if_ = do return (abort "TODO")

fix :: P STerm
fix = do i <- getPos
         reserved "fix"
         (f, fty) <- parens binding
         bs <- bindings
         reservedOp "->"
         t <- expr
         return (SFix i (f,fty) bs  t)

-- fixSugar :: P STerm
-- fixSugar = do i <- getPos


letfun :: P STerm
letfun = do
  i <- getPos
  reserved "let"
  f <- var 
  bs <- bindings
  reservedOp ":"
  ty <- typeP -- tau
  reservedOp "="  
  def <- expr
  reserved "in"
  body <- expr
  return (SLetFun i (f,ty) bs def body)

letexp :: P STerm
letexp = do
  i <- getPos
  reserved "let"
  b <- binding <|> parens binding
  reservedOp "="  
  def <- expr
  reserved "in"
  body <- expr
  return (SLet i b def body)

letrec :: P STerm
letrec = do
  i <- getPos
  reserved "let"
  reserved "rec"
  f <- var 
  (b:bs) <- bindings
  reservedOp ":"
  ty <- typeP 
  reservedOp "="  
  def <- expr
  reserved "in"
  body <- expr
  return (SLetRec i (f,ty) (b:bs) def body)

-- | Parser de términos
tm :: P STerm
tm = app <|> lam <|> ifz <|> printOp <|> fix <|> try letexp <|> try letrec <|> letfun 

-- | Parser de declaraciones
termDecl :: P SDeclaration
termDecl = do 
     i <- getPos
     reserved "let"
     v <- var
     reservedOp "="
     t <- expr
     return $ SDecl i v $ STermDecl t

typeDecl :: P SDeclaration
typeDecl = do 
  i <- getPos
  reserved "type"
  synonym <- var
  reservedOp "="
  realType <- typeP
  return $ SDecl i synonym $ STypeDecl realType
  
decl :: P SDeclaration
decl = termDecl <|> typeDecl

-- | Parser de programas (listas de declaraciones) 
program :: P [SDeclaration]
program = many decl

-- | Parsea una declaración a un término
-- Útil para las sesiones interactivas
declOrTm :: P (Either SDeclaration STerm)
declOrTm =  try (Left <$> decl) <|> (Right <$> expr)

-- Corre un parser, chequeando que se pueda consumir toda la entrada
runP :: P a -> String -> String -> Either ParseError a
runP p s filename = runParser (whiteSpace *> p <* eof) () filename s

--para debugging en uso interactivo (ghci)
parse :: String -> STerm
parse s = case runP expr s "" of
            Right t -> t
            Left e -> error ("no parse: " ++ show s)
