module CRSstep(crsStep) where

import Exp
import RenameCrs
import CRSvalidations
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S



--check arity is respected in substitute binders w.respect to MetaApp
arity:: CRule -> CSubs -> Bool
arity rl sb = let m =  (uncurry zip) $ tplSizes rl
              in and $ map (\(k,a) -> check (fst $ sb M.! k) a ) m

--by this point we know arities are respected among occ in rules
--Check that the number in the set is equal to the length of the binders
check c s =  length c `S.member` s


--steps should be done only after succesfully passing all
-- validations
crsStep:: Either TErr CRule-> Either TErr CSubs -> Either TErr CRule
crsStep (Left s)   (Left s') = Left (s ++ s')
crsStep (Left s) _ = Left s 
crsStep _ (Left s') = Left s' 
crsStep (Right (l,r)) (Right sub)
  | not $ mvarsExp l `S.isSubsetOf` M.keysSet sub =
    Left "Error: some MetaVars have no substitute specified in the valuation. \n"
  | not $ arity (l,r) sub =
    Left "Binders length in valuation must match arity of respective meta-application. \n"
  | otherwise  =
    let (s,l') = rnmCvars (freeVarsSbs sub) l
        (s',r') = rnmCvars s r
    in Right (oneStepRl  (safeSubs sub) (l' , r'))

--rewrite one step in CRS
oneStepRl:: CSubs -> CRule ->  CRule
oneStepRl sb (l,r)  = (applyVal sb l, applyVal  sb r)

--valuation action
applyVal ::  CSubs -> Exp  -> Exp
applyVal _ v@(VarExp a) = v
applyVal sb (Mapp x (TuplExp t)) = reduce (sb  M.! x) (map (applyVal sb) t)
applyVal sb (FunExp f t) = FunExp f (applyVal sb t)
applyVal sb (AbsExp a t) = AbsExp a (applyVal sb t)
applyVal sb (TuplExp t) = TuplExp (map (applyVal sb) t)

--perform developments
reduce :: Subs -> [Exp] -> Exp
reduce (xs, e) [] = e
reduce (xs, e) e' = renameCvrExp  (M.fromList $ zip xs e') e

--it works after alpha-converting both rules and valuations.No metavars should exist
renameCvrExp :: M.Map Cvar Exp -> Exp -> Exp
renameCvrExp as c@(VarExp a)   = M.findWithDefault c a as 
renameCvrExp as (AbsExp a t) = AbsExp a (renameCvrExp as t)
renameCvrExp as (FunExp f t) = FunExp f (renameCvrExp as t)
renameCvrExp as (TuplExp ts)  = TuplExp (map (renameCvrExp as) ts)
