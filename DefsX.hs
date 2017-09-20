module DefsX where

import qualified Data.List as L
import qualified Data.Map as M
import TrmX
import qualified Data.Set as S
import Exp
import Data.Maybe (fromJust, isNothing)
import CommonFnX (AbsT, frshList,lambdaOfX)



--should be checked for validity first
eNrs2CrsRl (fc,l,r) = (eNom2CrsTrm (fc,l),eNom2CrsTrm (fc,r)) 

eNom2CrsTrm tc = tranTrmX (lambdaOfX $ snd tc) tc

--Nominal Substitution translation--check whether is ground sigma(t)
eNom2CrsVSub fc t sub = tranSb (lambdaOfX t) sub (fc,t)
-----------------------------------------------------------------------------
-- translates a TrmXCtx into an CRS exp
tranTrmX :: AbsT -> TrmCtx -> Exp
tranTrmX     _   (_,AtmTrm a)    = VarExp a --atom to var
tranTrmX    lam  (fc,VarTrm sb p x)  = Mapp x  (TuplExp xs') where
  lambdaT     = lam M.! x --no error thrown bc empty by default
  frshness    = frshList fc x --set of atms fresh for x frshness
  xs          = S.toAscList $ (S.map (prmAtmApp (prmInv p)) lambdaT) S.\\ frshness
  xs1         = map (prmAtmApp p) xs
  xs'         = map (\a-> tranTrmX lam (fc, M.findWithDefault (anAtmTrm a) a sb)) xs1
tranTrmX    lam  (fc,AbsTrm a  t) = AbsExp a (tranTrmX lam (fc,t)) --abstraction
tranTrmX    lam  (fc,AppTrm f t) = FunExp f (tranTrmX lam (fc,t)) --function
tranTrmX    lam  (fc,TplTrm t)  = TuplExp (L.map (\ti-> tranTrmX lam (fc,ti)) t)--tuple





--leftmost occurrence of prm for each nom X --auxFun for tranSb
--it is translated w lhs rule hence no asb allowed
leftmostPrm:: Trm -> M.Map Var Prm
leftmostPrm (AtmTrm _) = M.empty
leftmostPrm (VarTrm sb p v) =  M.singleton v p
leftmostPrm (AbsTrm a t) = leftmostPrm t
leftmostPrm (AppTrm f t) = leftmostPrm t
leftmostPrm (TplTrm t) = M.unions (L.map leftmostPrm t)


-- translates substitution. needs LHS term
tranSb :: AbsT -> VSub -> TrmCtx -> CSubs
tranSb lam sub (fc,t) = let lftPrm = leftmostPrm t --leftmost Prm for each X
                            keys = M.keys sub --dom(sub)
                            prm  = (lftPrm M.!) --find  prm of x
                            lamOf = (lam M.!) --find  set of abst of x
                            frshnss  = frshList fc --set of assumptions for x
                            exp x = eNom2CrsTrm (fc, prmTrmApp (prm x) (sub M.! x))--CRS subst
                            convert x = M.singleton x (binders (prm x) (lamOf x) (frshnss x), exp x)--main fun
                         in M.unions $ map convert keys --maps to each NRS subs


--returns list of variable binders to add to substitute
binders setPrm setLam setFc = L.map (prmAtmApp setPrm) xsi
                              where xsi = S.toAscList $  
                                          S.map (prmAtmApp  (prmInv setPrm))  (setLam S.\\ setFc)
                           

