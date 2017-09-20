module Main (main) where

import Trm
import Defs
import System.IO
import Exp
import Control.Monad (when, liftM)
import ParserQuery
import ParserTrm
--import Data.Char (isDigit, ord)
import Data.List as L (map)
import Data.Map as M (singleton, null, unionsWith, fromList, union)
import Data.Set as S (empty, union)
import Data.Maybe (fromMaybe)
import Text.ParserCombinators.Parsec
import System.Exit
import CommonFn
import Crs2Nrs

main :: IO ()
main = do 
        hSetBuffering stdout NoBuffering
        hSetBuffering stdin LineBuffering
        putStrLn ""
        putStrLn  "Choose a definition to run:\n 1 - Translates a closed nominal rule or term in context,\n 2 - translates a set of nominal rules from a script \n 3 - Translates both a nominal term in context and a ground substitution.\n 4 - Similar to (3) but substitution is applied to term .\n 5 - Translates a set of CRS rules from a  script. \n 0 - Exit\n Definition number: "
        num <- getChar
        exprt <- getLine
        when (num == '0')   exitSuccess
        def num       
        main
     
def :: Char -> IO ()
def num = do
          putStrLn "write nominal term-in-context/file path: "
          hFlush stdout
          str <- liftM trim getLine
          case num of
                      '1'   -> do putStrLn "" 
                                  print $  readRules str
                      '2'   -> do withFile str ReadMode (\handle -> do
                                                            contents <- hGetContents handle
                                                            (putStr . unlines) $ map  readRules (lines contents))
                                  
                      '3'   -> do putStrLn "write a nominal assignment in the form [Var->Trm(,Var->Trm)] :"
                                  sub <- getLine
                                  let term = readRuleSub str
                                  putStrLn ""
                                  print $ either  ("error: " ++) term (readSub sub)
                                  
                      '4'   -> do putStrLn "write a nominal assignment in the form [Var->Trm(,Var->Trm)] :"
                                  sub <- getLine
                                  let term = readAndApply str
                                  putStrLn ""
                                  print $ either  ("error: " ++) term (readSub sub)       
                      '5'   -> do withFile str ReadMode (\handle -> do
                                                            contents <- hGetContents handle
                                                            (putStr . unlines) $ map  readInput (lines contents))
                      otherwise    -> print ("Error: a number must be chosen between 1 and 4.")
     
                                
                                
{- reads and ouputs type TrmCxt ((atm,Var),Trm)         -}  

          
readRules :: String -> String
readRules s = case (inputL parseCQ s) of
          Left err -> "Error: " ++ err
          Right (fc , tt ) -> let fc1  = fromMaybe empty fc
                                  absT =  M.unionsWith (S.union) (L.map (absTotal []) tt)
                                  m    = L.map ( translate4 absT fc1) tt
                                in (show . head) m ++ if (length m > 1) then " -> " ++ (show . last) m else ""  


readRuleSub :: String -> VSub -> String
readRuleSub t sb = case (inputL parseT t) of
          Left err -> "Error: " ++ err
          Right (fc , t) ->  let absT =  absTotal [] t
                                 trans = translate6 absT fc sb t
                                 expr  = fst trans
                                 subs  = snd trans
                             in "( " ++ show expr ++ ", " ++    showSubs subs ++ " )"

readAndApply :: String -> VSub -> String
readAndApply t sb = case (inputL parseT t) of
          Left err -> "Error: " ++ err
          Right (fc , t) ->  let absT = absTotal [] t
                                 trans = translate6 absT fc sb t
                                 expr  = fst trans
                                 subs  = snd trans
                             in "( "++ show (applySub subs expr) ++ " )"


--how to build a dictionary and map to more than one assignment
readSub :: String ->Either PErr VSub
readSub s= inputL parseSubs s 
               
                
                            
                            

--parse a nominal subs
parseSubs :: Parser VSub
parseSubs = fmap  M.fromList  (between (char '[') (char ']') ( sepBy p (char ',')))
   where p = do x <- parseVar
                string "->"
                t <- parseTrm
                return (x, t) <?> "substitution"
             
