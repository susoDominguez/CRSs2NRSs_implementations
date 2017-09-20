module ParserExp where

import Text.ParserCombinators.Parsec

import qualified Data.Char as R
import qualified Data.Set as S

import Exp

----------------------------------------------------------------------------

-- CRS exps

--vars: string starting with one lower case then an index number if necessary
parseVar :: Parser Cvar
parseVar =  do   
               x <- lower
               r <- many  (alphaNum <|> char '\'')
               return (x:r) <?> "CRS variable"

--metavars: string starting with one upper case then an index number if necessary
parseMVar :: Parser Mvar
parseMVar =  do  
                x <- upper
                r <- many (upper <|> char '\'' <|> digit)
                return (x:r) <?> "metavariable"

--function symbol: string starting with lowercase letter then any letter/digit
parseFun :: Parser Fun
parseFun = do  
              x <- char '\''
              r <- many1 alphaNum 
              return (x:r) <?> " CRS function symbol"

          
--parsing CRS terms
parseExp :: Parser Exp
parseExp = parseAbsExp <|> parseFunExp   <|> parseMappExp    <|> parseVarExp   <|>  parseTuplExp  <?> "CRS expression"

parseAbsExp , parseMappExp , parseFunExp, parseTuplExp :: Parser Exp

parseVarExp = do x <-parseVar
                 return (VarExp x)

parseAbsExp = do x <- between ( char '[' >> spaces) (spaces >> char ']') parseVar
                 spaces
                 t <- parseExp
                 return (AbsExp x t)

parseMappExp = do x <-  parseMVar
                  spaces
                  t <-   parseTuplExp <|> return (TuplExp [])
                  return (Mapp x t)
                  
parseFunExp = do f <- parseFun
                 t <- parseTuplExp <|> (space >> parseExp)
                 return (FunExp f t)
                 


parseTuplExp = fmap TuplExp (between ( char '('>> spaces) ( spaces >> char ')') (sepBy (spaces>>parseExp)  (spaces >> char ',') ))

--------------------------------------------------------------

parseCRule :: Parser CRule --define CRule
parseCRule = do l <- (spaces >>  parseExp)
                spaces >> string "->"
                r <- (spaces >> parseExp)
                return (l,r) <?> "CRS rule"
