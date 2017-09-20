module Crs2eNrs(crs2eNrsRl) where

--import ParserExp
import Exp
import TrmX
import Data.Set as S
import Data.Map as M
import Data.List as L
import CommonFnX (crs2ctx,cycle2Prm,rightSub,listedVars,applyMaps)



--main function. filter thru validation funs before passing it here
crs2eNrsRl (l,r) = let lftmstZ = leftmostZ l
                       (fc,l') = leftRuleX lftmstZ l
                       (fc',r')= rightRuleX lftmstZ r
                   in (fc `S.union` fc', l' ,r')

--translates LHS of CRS rules
leftRuleX  = leftRuleX' []

--translates RHS of Crs rules to eNom
rightRuleX  = rightRuleX' []

---------------------------------------------------------------------------------

--Definition from leftmost MetaVar returns list of variables                    
leftmostZ :: Exp -> Map Mvar  [Cvar]
leftmostZ  (VarExp x) = M.empty
leftmostZ  (Mapp x (TuplExp xs)) = M.singleton x (listedVars xs) --list in metaapp
leftmostZ  (AbsExp a t) = leftmostZ  t
leftmostZ  (FunExp f t) = leftmostZ  t
leftmostZ  (TuplExp t) = M.unions   (L.map leftmostZ  t)--map union is left-biased


-----------------------------------------------------

--left rule algorithm for the extended case:
leftRuleX' ::  [Cvar] -> Map Mvar [Cvar] ->  Exp -> TrmCtx
leftRuleX'  v _ (VarExp a)   = (S.empty , AtmTrm a)
leftRuleX'  v m (Mapp x (TuplExp t)) =
  let lst = findWithDefault [] x m 
      context = crs2ctx x (v L.\\ lst)
  in (context , VarTrm M.empty (psi lst (listedVars t))  x) 
leftRuleX'  v  m (AbsExp a t) = let lr = leftRuleX' (a:v) m t
                                in (fst lr, AbsTrm a (snd lr))
leftRuleX'  v  m (FunExp f t) = let lr = leftRuleX' v m  t
                                in (fst lr, AppTrm f (snd lr))
leftRuleX'  v  m (TuplExp tt) = ( S.unions c', TplTrm tt') 
  where (c', tt')= unzip $ L.map (leftRuleX' v m) tt
                            


--Right rule algorithm
rightRuleX' :: [Cvar] -> Map Mvar [Cvar] -> Exp -> TrmCtx
rightRuleX' v m (VarExp a)   = (S.empty,  AtmTrm a)
rightRuleX'  v m (Mapp x (TuplExp t)) =
  let lst = findWithDefault [] x m
      (prm, asb) = rightSub lst t
      asb' = M.map (snd . rightRuleX m) asb
  in (crs2ctx x v, VarTrm asb' prm  x)
rightRuleX'  v m (AbsExp a t) = let trm=(rightRuleX' (a:v) m t) 
                                in (fst trm,  AbsTrm a (snd trm))  
rightRuleX'  v m (FunExp f t) = let trm=(rightRuleX' v m t) 
                                in (fst trm,  AppTrm f (snd trm))
rightRuleX'  v m (TuplExp tt) = (S.unions ctxs, TplTrm  tt') 
  where (ctxs, tt') = unzip $ L.map (rightRuleX' v m) tt                                 
                                 

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


