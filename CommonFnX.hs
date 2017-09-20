module CommonFnX where

import Exp
import TrmX
import Data.List as L
import Data.Set as S 
import Data.Map as M
import Data.Maybe (fromJust, isJust)
--import Data.Char (isSpace)

--Lamba_t type
type AbsT = M.Map Var (Set Atm)--contains a dictionary with variables and a set  with all Atms abst over them.
              

--extended version --needs editing
absTotalX :: S.Set Atm ->  Trm -> AbsT 
absTotalX    xs (AtmTrm _)       = M.empty 
absTotalX    xs (VarTrm sb _ x) = M.unionsWith S.union
                                  (M.singleton x (xs `S.union` aSbDom sb) :
                                  L.map (absTotalX xs) (M.elems sb))
absTotalX    xs (AbsTrm a  t)    = absTotalX (S.singleton a `S.union` xs) t
absTotalX    xs (AppTrm f t)     = absTotalX xs t
absTotalX    xs (TplTrm t)       = M.unionsWith S.union (L.map (absTotalX xs) t)


----lambda_t function

lambdaOfX = absTotalX S.empty

---------------------------------------------

--given a context, and a Var X from the term, produce a set of atoms which are fresh for that particular X. 
frshList ::  Ctx -> Var -> Set Atm
frshList fc x = S.map fst $ S.filter (\(a,y) -> x==y) fc


------------------------------------------------------------------------------
--converts a metavar and a list of variables into a set of assumptions
crs2ctx :: Mvar -> [Cvar] -> Ctx
crs2ctx _ [] = S.empty
crs2ctx x vars = S.fromList $ L.map (\a -> (a, x)) vars


-----------aux funs for crs2eNrs


--remove type VarExp to list of vars in metaApp. AuxFun for leftmostZ
listedVars :: [Exp]  -> [Cvar]
listedVars [] = []
listedVars (VarExp x : xs) = x : (listedVars xs)
listedVars ( _ : xs) =  listedVars xs


--filters prms from Atm subs( here denoted as Atm->Exp, translate back in main fn
rightSub ::  [Cvar] -> [Exp] -> (Prm, M.Map Atm Exp)
rightSub m  ts = (tuple m ts, tuple' m ts)


--this tuple fun constructs prms and filters out trms            
tuple :: [Cvar] -> [Exp] -> Prm
tuple   [] _ = []
tuple    _ []=[]
tuple  (a:vars) (VarExp b: xs) | a == b =   tuple vars xs --discard id prms
tuple  (a:vars) (VarExp b: xs) =  (a, b) : tuple vars xs
tuple   (a:vars)  (x:xs) = tuple vars xs --case where rhs in not a varExp
-------
--this tuple' fun types trms and filters out prm.
--Exp must be translated to TrmX in main fn
tuple' :: [Cvar] -> [Exp] -> M.Map Atm Exp
tuple'   [] _ = M.empty
tuple'    _ []= M.empty
tuple' (a:vars)  (VarExp b: xs) = tuple' vars xs --checks 1st for Cvars to skip
tuple' (a:vars)  (b:xs) = tuple' vars xs `M.union` M.singleton a b


-- works for both mappings rightwards and leftwards. Psi fn helper
applyMaps:: Map Atm Atm -> Atm -> Atm -> [Atm]
applyMaps  f a b = if isJust maybeNext  && next /= a
                    then next : applyMaps f a next 
                       else []
    where maybeNext = M.lookup b f
          next = fromJust maybeNext


--function to build prm from cycle notation. [a,b,c,...,n] -> (a b)(a c)...(a n)
cycle2Prm :: [Atm] -> Prm
cycle2Prm (x:[]) = []
cycle2Prm (x:y:xs) = prmComp [(x,y)] (cycle2Prm (x:xs))
