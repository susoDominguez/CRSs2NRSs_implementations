module Exp where 

--import System.Environment
--import Control.Monad
import qualified Data.List as L
import qualified Data.Set as S
import qualified Data.Map as M
import Data.Char

-- data structures --

type Cvar = String --variable
type Mvar = String --metavariable
type Fun = String --function constructor

data Exp = VarExp Cvar
           | Mapp Mvar Exp
           | FunExp Fun Exp
           | AbsExp Cvar Exp
           | TuplExp [Exp] deriving (Eq)

-- CRS substitution
type Subs = ([Cvar], Exp) --substitute, pair of binders and exp
type CSubs = M.Map Mvar Subs --CRS sub

--to display errors
type TErr = String                    
----------------------------------------------------------------------------------------
{- Pretty-printing -}

showExp :: Exp -> String
showExp (VarExp a)     = a
showExp (FunExp fn e)  = fn ++ " " ++ showExp e                      
showExp (AbsExp a e)   = "[" ++ a ++ "]" ++ showExp e
showExp (TuplExp [])  = ""
showExp (TuplExp xs)   = "("++ L.intercalate ", " (map showExp xs) ++ ")"
showExp (Mapp x e)     = x ++ showExp e --parser only accepts tuplExp

--show CRS substs
showSubs    =  concat . (map aSubs) .  M.toList 

aSubs :: (Mvar,Subs) -> String
aSubs (v, (xs,exp)) 
               | null xs = "[" ++ v ++ " -> " ++ showExp exp ++ "]"
               | otherwise = "[" ++ v ++ " -> \\\&"  ++ 
                            L.intercalate ".\\\&" xs ++  "." ++
                            showExp exp ++ "]"

instance Show Exp where show = showExp

----------------------------------
type CRule = (Exp , Exp)--CRS RUle

showRule (l,r) = showExp l ++  " => " ++ showExp r

-----------------------------------

--Sets of variables and metavariables

--Cvars
cvarsExp :: Exp -> S.Set Cvar
cvarsExp (VarExp a)   = S.singleton a
cvarsExp (FunExp _ t) = cvarsExp t
cvarsExp (TuplExp ts)  = S.unions (map cvarsExp ts)
cvarsExp (AbsExp a t) = S.insert a (cvarsExp t)
cvarsExp (Mapp x t) = cvarsExp t

--Mvars
mvarsExp :: Exp -> S.Set Mvar
mvarsExp (VarExp _)   = S.empty
mvarsExp (FunExp _ t) = mvarsExp t
mvarsExp (TuplExp ts)  = S.unions (map mvarsExp ts)
mvarsExp (AbsExp _ t) = mvarsExp t
mvarsExp (Mapp x t) = S.insert x (mvarsExp t)

------------------------
--sets of free and bound variables

--free
freeVars :: Exp -> S.Set Cvar
freeVars (VarExp a)   = S.singleton a
freeVars (FunExp _ t) = freeVars t
freeVars (TuplExp ts)  = S.unions (map freeVars ts)
freeVars (AbsExp a t) = (freeVars t) S.\\ S.singleton a
freeVars (Mapp x t) = freeVars t

--one CRS substitute
freeVarsSb :: Subs -> S.Set Cvar
freeVarsSb (vrs,exp) = freeVars exp S.\\ S.fromList vrs

--free vrs of substitutes 
freeVarsSbs :: CSubs -> S.Set Cvar
freeVarsSbs  = S.unions . (map freeVarsSb) . M.elems
