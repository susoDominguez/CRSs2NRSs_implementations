module CommonFn where
--28/10 changes to function:
--pre: traverse the term to list all abs in term.This is now XS in main function.

import Exp
import Trm
import Data.List as L ((\\), union, map,null)
import Data.Set as S 
import Data.Map as M
import Data.Char (isSpace)

--Lamba_t type
type AbsT = M.Map Var (Set Atm)--contains a dictionary with variables and a set  with all Atms abst over them.
              
--reads abstractions on term (Mapping Lambda_t)
absTotal :: [Atm] ->  Trm -> AbsT 
absTotal    xs (AtmTrm _)       = M.empty 
absTotal    xs (VarTrm _ x)     = M.singleton x (S.fromList xs)
absTotal    xs (AbsTrm a  t)    = absTotal (a:xs) t
absTotal    xs (AppTrm f t)     = absTotal xs t
absTotal    xs (TplTrm t)       = M.unionsWith S.union  (L.map (absTotal xs)  t)


----lambda_t function
lambdaOf = absTotal []

---------------------------------------------

--given a context, and a Var X from the term, produce a set of atoms which are fresh for that particular X. 
frshList ::  Ctx -> Var -> Set Atm
frshList fc x = S.map fst $ S.filter (\(a,y) -> x==y) fc


------------------------------------------------------------------------------
--converts a metavar and a list of variables into a set of assumptions
crs2ctx :: Mvar -> [Cvar] -> Ctx
crs2ctx _ [] = S.empty
crs2ctx x vars = S.fromList $ L.map (\a -> (a, x)) vars

                   
-- application of CRS substitution to term
applySub :: CSubs -> Exp -> Exp
applySub sub t @(Mapp x (TuplExp e))
    = case M.lookup x sub of
             Nothing      -> t
             Just (xs, s) -> tMapping (zip xs (toCvar e)) s
applySub  sub (AbsExp a t) = AbsExp a (applySub sub t)
applySub  sub (FunExp f t) = FunExp f (applySub sub t)               
applySub  sub (TuplExp  t) = TuplExp (L.map (applySub sub) t)               
applySub  _    t           = t
               


--swaps variables s.t (a,b) indicates a as a bound variable in term and b as new variable to be substituted in the term.
varMapping :: [(Cvar, Cvar)] -> Cvar -> Cvar
varMapping [] a = a
varMapping ((a, b) : p) c
    | c == a    = b
    | otherwise = varMapping p c
                  
--map bound variables to sub variables in the substitution term
tMapping :: [(Cvar,Cvar)] -> Exp -> Exp
tMapping  sub (VarExp t)    = VarExp (varMapping sub t)
tMapping  sub (AbsExp a t) = AbsExp a (tMapping sub t)
tMapping  sub (FunExp f t) = FunExp f (tMapping sub t)               
tMapping  sub (TuplExp  t) = TuplExp (L.map (tMapping sub) t)               
tMapping  _    t           = t




--convert a list of expressions into a list of CRS object vars
toCvar :: [Exp] -> [Cvar]
toCvar []   = []
toCvar (VarExp x:xs) = x : toCvar xs 

--converts a list of atoms into a list of lambda variables for vsubs
toCvar' :: [Atm] -> [Cvar]
toCvar' xs =L.map (\ x -> x) xs 

---trim whitespace from String
trim :: String -> String
trim = f . f
      where f = reverse . dropWhile isSpace
