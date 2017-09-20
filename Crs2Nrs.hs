module Crs2Nrs(crs2NrsRl) where

--import ParserExp
import Exp
--import System.Exit
--import System.Environment
--import Text.ParserCombinators.Parsec
import Trm
import Data.Set as S
import Data.Map as M
import Data.List as L
import Data.Maybe as N
import CommonFn (crs2ctx)

       
{-readInput ::  String -> String
readInput input = case parse  parseCRule "CRS" input of
                   Left err -> "No match: " ++ (show err)
                   Right exp -> let l = fst exp
                                    r = snd exp                      
                                    zs =leftmostZ  l
                                    lr = leftRule zs l
                                    rr = rightRule zs  r
                                    ctx = S.union (fst lr) (fst rr)
                                in  showTrmCtx (ctx, (snd lr)) ++ " --> " ++ (showTrm (snd rr))-}
-------------------------------------------------------------------------------------
--Definition from leftmost MetaVar return list of variables                    
leftmostZ :: Exp -> Map Mvar  [Cvar]
leftmostZ  (VarExp x) = M.empty
leftmostZ  (Mapp x (TuplExp xs)) = M.singleton x (listedVars xs) --  xs for list in metaapp
leftmostZ  (AbsExp a t) = leftmostZ  t
leftmostZ  (FunExp f t) = leftmostZ  t
leftmostZ  (TuplExp t) = M.unions   (L.map leftmostZ  t)--map union is left-biased

--remove type VarExp to list of vars in metaApp. AuxFun for leftmostZ
listedVars :: [Exp]  -> [Cvar]
listedVars [] = []
listedVars (VarExp x : xs) = x : (listedVars xs)
listedVars ( _ : xs) =  listedVars xs
----------------------------------------------------------------------------------------------------

--main fun. filter thru validations first
crs2NrsRl (l,r) = let lftmstZ = leftmostZ l
                      (fc,l') = leftRule lftmstZ l
                      (fc',r')= rightRule lftmstZ r
                  in (fc `S.union` fc', l' ,r')


--translates LHS of CRS rules
leftRule  = leftRule' []
          
--left rule algorithm:
leftRule' ::  [Cvar] -> Map Mvar [Cvar] ->  Exp -> TrmCtx
leftRule'  v _ (VarExp a)   = (S.empty , AtmTrm a)
leftRule'  v m (Mapp x (TuplExp t)) = let lst = findWithDefault [] x m --list of vars in lambda for x
                                          context = crs2ctx x (v L.\\ lst)--if leftmost then lst=v
                                      in (context , VarTrm (psi lst (listedVars t))  x) 
leftRule'  v  m (AbsExp a t) = let lr = leftRule' (a:v) m t
                               in (fst lr, AbsTrm a (snd lr))
leftRule'  v  m (FunExp f t) = let lr = leftRule' v m  t
                               in (fst lr, AppTrm f (snd lr))
leftRule'  v  m (TuplExp tt) = ( S.unions c', TplTrm tt') 
  where (c', tt')= unzip $ L.map (leftRule' v m) tt


--translates RHS of Crs rules
rightRule  = rightRule' []

--Right rule algorithm
rightRule' :: [Cvar] -> Map Mvar [Cvar] -> Exp -> TrmCtx
rightRule' v m (VarExp a)   = (S.empty,  AtmTrm a)
rightRule'  v m (Mapp x (TuplExp t)) = let lst = findWithDefault [] x m
                                           (prm, tpl) = rightSub lst t --filters prms from explicit asubs
                                           tpl'= M.map (snd . rightRule m) tpl
                                       in (crs2ctx x v, VarTrm' prm  x tpl')
rightRule'  v m (AbsExp a t) = let trm=(rightRule' (a:v) m t) 
                               in (fst trm,  AbsTrm a (snd trm))  
rightRule'  v m (FunExp f t) = let trm=(rightRule' v m t) 
                               in (fst trm,  AppTrm f (snd trm))
rightRule'  v m (TuplExp tt) = (S.unions ctxs, TplTrm  tt') 
  where (ctxs, tt') = unzip $ L.map (rightRule' v m) tt                             
                                 
--function to construct subs on right-hand side and also permutations
rightSub ::  [Cvar] -> [Exp] -> (Prm, M.Map Atm Exp)--must b trans to Trm
rightSub m  ts = (tuple m ts, tuple' m ts)

--this tuple fun constructs prms and filters out trms            
tuple :: [Cvar] -> [Exp] -> Prm
tuple   [] _ = []
tuple    _ []=[]
tuple  (a:vars) (VarExp b: xs) | a == b =   tuple vars xs --discard identity permutations
tuple  (a:vars) (VarExp b: xs) =  (a, b) : tuple vars xs
tuple   (a:vars)  (x:xs) = tuple vars xs --for the case where on rhs rule is an Exp but not a var
-------
--this tuple' fun types trms and filters out prm
tuple' :: [Cvar] -> [Exp] -> M.Map Atm Exp
tuple'   [] _ = M.empty
tuple'    _ []= M.empty
tuple' (a:vars)  (VarExp b: xs) = tuple' vars xs --checks 1st for Cvars to skip
tuple' (a:vars)  (b:xs) = tuple' vars xs `M.union` M.singleton a b

--Definition of Psi
psi :: [Cvar] -> [Cvar] -> Prm
psi [] _ = []
psi phi@(a:xs)  ys = prmComp perm  (psi  (delElems phi) (delElems ys) )
             where lftMapp = M.fromList $ L.zip phi ys
                   rghtMapp= M.fromList $ L.zip ys phi
                   fun   = applyMaps lftMapp
                   fun_1 a = reverse . applyMaps rghtMapp a
                   cycle = if S.fromList (fun a a) == S.fromList (fun_1 a a)
                             then (a:fun a a) else fun_1 a a ++ (a:fun a a)
                   delElems = L.filter (\a -> notElem a  cycle) 
                   perm = cycle2Prm  cycle

-- works for both mappings rightwards and leftwards
applyMaps:: Map Atm Atm -> Atm -> Atm -> [Atm]
applyMaps  f a b = if N.isJust maybeNext  && next /= a
                    then next : applyMaps f a next 
                       else []
    where maybeNext = M.lookup b f
          next = N.fromJust maybeNext


--function to build prm from cycle notation. [a,b,c,...,n] -> (a b)(a c)...(a n)
cycle2Prm :: [Atm] -> Prm
cycle2Prm (x:[]) = []
cycle2Prm (x:y:xs) = prmComp [(x,y)] (cycle2Prm (x:xs))
