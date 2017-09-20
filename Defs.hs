module Defs where

import qualified Data.List as L
import qualified Data.Map as M
import Trm
import qualified Data.Set as S
import Exp
import Data.Maybe (fromJust, isNothing)
import CommonFn (AbsT, lambdaOf, frshList)



--should be checked for validity first
nrs2crsRule (fc,l,r) = (nom2crsTrm (fc,l),nom2crsTrm (fc,r)) 

nom2crsTrm tc = tranTrm (lambdaOf $ snd tc) tc

--Nominal Substitution translation--check whether is ground sigma(t)
nom2crsVSub fc t sub = tranSb (lambdaOf t) sub (fc,t)
-----------------------------------------------------------------------------
-- translates a TRMCTX into an CRS exp
tranTrm :: AbsT ->  TrmCtx -> Exp
tranTrm     _   (_,AtmTrm a)    = VarExp a --atom to var
tranTrm    lam  (fc,VarTrm p x)  = Mapp x  (TuplExp xs') where
  lambdaT     = lam M.! x --no error thrown bc empty by default
  frshness    = frshList fc x --set of atms fresh for x frshness
  xs          = S.toAscList $ (S.map (prmAtmApp (prmInv p)) lambdaT) S.\\ frshness
  xs'         = map (\a-> VarExp (prmAtmApp p a)) xs
tranTrm    lam  (fc,AbsTrm a  t) = AbsExp a (tranTrm lam (fc,t)) --abstraction
tranTrm    lam  (fc,AppTrm f t) = FunExp f (tranTrm lam (fc,t)) --function
tranTrm    lam  (fc,TplTrm t)  = TuplExp (L.map (\ti-> tranTrm lam (fc,ti)) t)--tuple





--leftmost occurrence of prm for each nom X --auxFun for tranSb
leftmostPrm:: Trm -> M.Map Var Prm
leftmostPrm (AtmTrm _) = M.empty
leftmostPrm (VarTrm p v) = M.singleton v p
leftmostPrm (AbsTrm a t) = leftmostPrm t
leftmostPrm (AppTrm f t) = leftmostPrm t
leftmostPrm (TplTrm t) = M.unions (L.map leftmostPrm t)


-- translates substitution
tranSb :: AbsT -> VSub -> TrmCtx -> CSubs
tranSb lam sub (fc,t) = let lftPrm = leftmostPrm t --leftmost Prm for each X
                            keys = M.keys sub --dom(sub)
                            prm  = (lftPrm M.!) --find  prm of x
                            lamOf = (lam M.!) --find  set of abst of x
                            frshnss  = frshList fc --set of assumptions for x
                            exp x = nom2crsTrm (fc, prmTrmApp (prm x) (sub M.! x))--CRs subst
                            convert x = M.singleton x (binders (prm x) (lamOf x) (frshnss x), exp x)--main fun
                         in M.unions $ map convert keys --maps to each NRS subs


--returns list of variable binders to add to substitute
binders setPrm setLam setFc = L.map (prmAtmApp setPrm) xsi
                              where xsi = S.toAscList $  
                                          S.map (prmAtmApp  (prmInv setPrm))  (setLam S.\\ setFc)
                           
