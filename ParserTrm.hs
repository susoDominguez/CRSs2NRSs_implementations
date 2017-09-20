module ParserTrm where

import Text.ParserCombinators.Parsec

import qualified Data.Char as R
import qualified Data.Set as S
import qualified Data.Map as M
import Constraints
import Trm

type PErr = String

-- TRM

--atoms: string starting w lower case letter
parseAtm :: Parser Atm
parseAtm = do
  x <- lower
  r <- many (lower <|> char '\'' <|> digit)
  return (x:r) <?> "Atom"


--variables: string starting w upper case letter
parseVar :: Parser Var
parseVar = do
  x <- upper
  r <- many (upper <|> char '\'' <|> digit)
  return (x:r) <?> "Variable"


--function name: string starting with '
parseFun :: Parser Fun
parseFun = do
  x <- char '\''
  r <- many1 alphaNum
  return (x:r)  <?> "Function symbol"
                 
--swapping : 2 atoms separated by a space in between brackets
parseTrans:: Parser (Atm,Atm)
parseTrans = between (char '(') (char ')') p  <?> "Swapping"
            where p = do
                    a <- parseAtm
                    space
                    b <- parseAtm
                    return (a,b)

--permutation : must be reversed
parsePrm :: Parser Prm
parsePrm = fmap reverse (many1 parseTrans) <?> "permutation"
                 

--parse freshness context
parseaCtx :: Parser Ctx
parseaCtx = fmap S.fromList (between (char '{' >> spaces) (spaces >> char '}') (sepBy p (char ','))) <?> "freshness context"
    where p = do a <- (spaces >> parseAtm)
                 char '#'
                 x <- parseVar
                 spaces
                 return (a, x)
                 
parseTrm :: Parser Trm
parseTrm = parseAbsTrm <|> parseAppTrm <|> (fmap AtmTrm parseAtm) <|> (try parseTplTrm <|> parseVarTrm) <?> "nominal term"


parseAbsTrm, parseTplTrm, parseVarTrm, parseAppTrm :: Parser Trm
parseAbsTrm = do
              char '['
              a <- spaces >> parseAtm
              spaces 
              char ']'
              t <- spaces >> parseTrm
              return (AbsTrm a t)
parseTplTrm = fmap TplTrm (between (char '(') (char ')')( p `sepBy1`  (char ',')))
   where p = do  t <- spaces >> parseTrm
                 spaces
                 return t
parseVarTrm = try p1 <|> p2
   where p1 = do p <- parsePrm
                 char '+'
                 v <- parseVar
                 return (VarTrm p v)
         p2 = do 
                 v <- parseVar
                 return (VarTrm [] v)
parseAppTrm = do
                 f <- parseFun
                 spaces
                 t <- do try parseTrm <|>
                            try (eof >> return (TplTrm [])) <|>
                              (lookAhead (oneOf ",])=") >> return (TplTrm []))
                 return (AppTrm f t)             
                 
parseCtx:: Parser Ctx
parseCtx = do ctx <- parseaCtx
              spaces
              string "|-"
              return ctx

parseTrmCtx:: Parser TrmCtx
parseTrmCtx = do
              ctx <- try (parseCtx)  <|> (return S.empty) 
              spaces
              t <- parseTrm
              return (ctx, t) <?> "term-in-context"

parseConstr :: Parser (Constr Trm)
parseConstr = try eq <|> frsh
      where eq = do a <- spaces >> parseAtm
                    char '#'
                    t <- parseTrm
                    spaces
                    return (F (AtmTrm a) t)
            frsh = do t1 <- spaces >>  parseTrm
                      spaces
                      char '='
                      t2 <- spaces >> parseTrm
                      spaces
                      return (E t1 t2) <?> "#|= Constrain"

parseProb :: Parser Prob
parseProb = do xs <- sepBy parseConstr (char ',')
               spaces >> eof
               return xs <?> "List of #|= Constraints"

parseProbCtx :: Parser ProbCtx
parseProbCtx = do   ctx <- try (parseCtx) <|> (return S.empty)
                    spaces
                    prob <- parseProb
                    return (ctx,prob) <?> "ctx and problem"
                           
inputL :: Parser a -> String -> Either PErr a
inputL p s = case parse p ""  s of
                 Left e -> Left (show e)
                 Right x -> Right x

--parse a nominal vsubs
parseSubs :: Parser VSub
parseSubs = fmap  M.fromList  (between (char '[') (char ']') ( sepBy p (char ',')))
   where p = do x <- parseVar
                string "->"
                t <- parseTrm
                return (x, t) <?> "substitution"

--parseCtx :: Parser Ctx
-------------------------------------------------------------------------------
-- REWRITING

parseRule :: Parser Rule
parseRule = do fc <- try parseCtx <|> (return S.empty)
               spaces
               l <- parseTrm
               spaces
               string "-->"
               spaces
               r <- parseTrm
               return (fc, l, r) <?> "rule"
