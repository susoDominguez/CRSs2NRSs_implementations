-- Syntax of Nominal terms and operations on them
module Trm where

import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S

--------------------------  DATA STRUCTURES

--Convenient aliases for term symbols
type Atm = String --atom symbol
type Var = String -- var symbol
type Fun = String --term former (function) symbol

--type aliases for permutations and freshnesses
type Prm = [(Atm, Atm)] --permuation is a list of atom swappings
--Freshness context is a set of primitive constraints of form  a#X: (a,X)
type Ctx = S.Set (Atm, Var)

--Term t in freshness context \Delta (aka term in context)
type TrmCtx = (Ctx, Trm)

--type alias for a set of variable mappings
type VSub = M.Map Var Trm

{-type alias for explicit  substitution of atoms by terms.
  To be applied when reducing NRSs to CRSs since atom substitution is
  not primitive. -}
type ASb = M.Map Atm Trm

--alias for errors when parsing terms
type TErr = String

{-| Syntax of nominal terms. It consists of Atom terms, Abstraction terms,
  Function application terms, tuple terms, moderated variables and, additionally,
  moderated variables with an explicit atom substitution.-} 
data Trm = AtmTrm Atm
         | AbsTrm Atm Trm
         | AppTrm Fun Trm
         | TplTrm [Trm]
         | VarTrm Prm Var 
         | VarTrm' Prm Var ASb deriving (Show, Eq) --additional moderated Var term


----------------------------- PERMUTATION actions

{-| Returns the composition of a pair of permutations, that is, given
  permutations p = (a b) and p = (a c)(d e), prmComp p p' = (a b)(a c)(d e). -}
prmComp :: Prm -> Prm -> Prm
prmComp = (++)

{-| Returns the inverse of a permutation p, that is, p^{ -1}. -}
prmInv :: Prm -> Prm
prmInv = reverse

--returns all the names in a given permutation
atmsPrm :: Prm -> S.Set Atm
atmsPrm = S.unions . (map (\(a, b) -> S.fromList [a, b]))

{-| Returns the support of a permutation p. Observe that if p = (a b)(c d)(b a),
  then atoms a,b are not in the support of p since p(a)=a and p(b)=b. -}
prmSupp :: Prm -> S.Set Atm
prmSupp p = S.filter (\a -> (prmAtmApp p a) /= a) (atmsPrm p)

--Application of a permutation to an atom symbol
prmAtmApp :: Prm -> Atm -> Atm
prmAtmApp [] a = a
prmAtmApp ((a, b) : p) c
    | c == a    = prmAtmApp p b
    | c == b    = prmAtmApp p a
    | otherwise = prmAtmApp p c

{-| Applies a permutation to a Nominal term, resulting in the permuted Nominal
   term. -}
prmTrmApp :: Prm -> Trm -> Trm
prmTrmApp [] t = t
prmTrmApp p (AtmTrm a)   = AtmTrm (prmAtmApp p a)
prmTrmApp p (AbsTrm a t) = AbsTrm (prmAtmApp p a) (prmTrmApp p t)
prmTrmApp p (AppTrm f t) = AppTrm f (prmTrmApp p t)
prmTrmApp p (TplTrm ts)  = TplTrm (map (prmTrmApp p) ts)
prmTrmApp p (VarTrm q v) = VarTrm (prmComp q p) v

{-| Returns the Difference Set between a pair of permutations, that is,
  for permutations p,p' and atom a, if p(a)=b and p'(a)=c, for any two distinct
  atoms b,c, then atom a is in their Difference set.-}
prmDs :: Prm -> Prm -> S.Set Atm
prmDs p1 p2 = S.filter diff $ S.union (atmsPrm p1) (atmsPrm p2)
    where diff a = prmAtmApp p1 a /= prmAtmApp p2 a



-----------------------SETS of ATOMs and VARS in a term ----

{-| Set of atom symbols in a freshness context \Delta, that is,
  {a | a#X\in\Delta}. -}
atmsCtx :: Ctx -> S.Set Atm
atmsCtx = S.map fst

{-| Set of variable symbols in a freshness context \Delta, that is,
  {X | a#X\in\Delta}. -}
varsCtx :: Ctx -> S.Set Var
varsCtx = S.map snd

{-| Returns the set of atom symbols from a given Nominal term. -}
atmsTrm :: Trm -> S.Set Atm
atmsTrm (AtmTrm a)   = S.singleton a
atmsTrm (AppTrm _ t) = atmsTrm t
atmsTrm (TplTrm ts)  = S.unions (map atmsTrm ts)
atmsTrm (AbsTrm a t) = S.insert a (atmsTrm t)
atmsTrm (VarTrm p _) = prmSupp p --support of a permutation p

{-| Returns the set of variable symbols from a given Nominal term. -}
varsTrm :: Trm -> S.Set Var
varsTrm (AtmTrm _)   = S.empty
varsTrm (AppTrm _ t) = varsTrm t
varsTrm (TplTrm ts)  = S.unions (map varsTrm ts)
varsTrm (AbsTrm _ t) = varsTrm t
varsTrm (VarTrm _ v) = S.singleton v

{-| Returns the set of atom symbols from a given Nominal term-in-Context. -}
atmsTrmCtx :: TrmCtx -> S.Set Atm
atmsTrmCtx (fc, t) = S.union (atmsCtx fc) (atmsTrm t)

{-| Returns the set of variable  symbols from a given Nominal term-in-Context. -}
varsTrmCtx :: TrmCtx -> S.Set Var
varsTrmCtx (fc, t) = S.union (varsCtx fc) (varsTrm t)



-------------------------- PRETTY-PRINTING of Nominal terms

--printing permutations
showPrm :: Prm -> String
showPrm [] = ""
showPrm ((a, b) : ts)| a==b = showPrm ts --discard Id swaps
showPrm ((a, b) : ts) = showPrm ts ++ "(" ++ a ++ " " ++ b ++ ")"

--printing a freshness context
showCtx :: Ctx -> String
showCtx ctx =
  if S.null ctx
   then "{}" 
    else "{" ++ L.intercalate ", " (map (\(a,v) ->  a ++ "#" ++ v) (S.toList ctx)) ++ "}"

--printing a nominal term
showTrm :: Trm -> String
showTrm (AtmTrm a)    = a
showTrm (AbsTrm a t)  = "[" ++ a ++ "]" ++ showTrm t
showTrm (AppTrm n (TplTrm [])) = n
showTrm (AppTrm n t)  = n ++ " " ++ showTrm t
showTrm (TplTrm ts)   = "(" ++ L.intercalate ", " (map showTrm ts) ++ ")"
showTrm (VarTrm [] v) = v
showTrm (VarTrm p v)  = showPrm p ++ "+" ++ v
--explicit substitution printing
showTrm (VarTrm' p v ts) = showPrm p ++ 
              (if null p then "" else "+") ++ v  ++ showASb ts 

showASb :: M.Map Atm Trm -> String
showASb m 
   | M.null m = ""
   | otherwise = concat $ map (\(k,a) -> "[" ++ k ++ " -> " ++ showTrm a ++ "]"  ) (M.assocs m)
--endOf explicit substittuion printing

--prints a term-in-context
showTrmCtx :: TrmCtx -> String
showTrmCtx (fc, t) = showCtx fc ++ " |-  " ++ showTrm t

--prints a set of variable substitutions
showVSub :: VSub -> String
showVSub sb = M.foldrWithKey (\v t acc -> acc ++ (fn v t)) "" sb
    where fn v t = "[" ++ v ++ " -> " ++ showTrm t ++ "]"

--prints a nominal rewrite rule
showRule :: Rule -> String
showRule (fc,l,r) = showCtx fc ++ " |- " ++ showTrm l ++ " --> " ++ showTrm r

--prints a sequence of nominal rewrite steps
showSteps :: Ctx -> [Trm] -> String
showSteps fc ts = showCtx fc ++ " |- " ++ L.intercalate "-->" (map showTrm ts) ++ "."
-------------------------------------------------------------------------
--Context

-- context fc2 satisfies fc1
derives :: Ctx -> Ctx -> Bool
derives fc1 fc2 = fc2 `S.isSubsetOf` fc1
-----------------
--groundTrm?
isGround  = S.null . varsTrm 
------------------------------------------------------------------------------
-- Vsubstitutions

vsubApp :: VSub -> Trm -> Trm
vsubApp  sb t@(VarTrm p x) = case M.lookup x sb of
                                     Nothing -> t
                                     Just s  -> prmTrmApp p s
vsubApp sb (AppTrm f ts) = AppTrm f (vsubApp sb ts)
vsubApp sb (TplTrm ts) = TplTrm (map (vsubApp sb) ts)
vsubApp sb (AbsTrm a t) = AbsTrm a (vsubApp sb t)
vsubApp _ t = t


vsubSearch :: Var -> VSub -> Maybe Trm
vsubSearch = M.lookup

-- idempotent substitution composition: see baader & snyder
vsubComp :: VSub -> VSub -> VSub
vsubComp sb1 sb2 = M.union ((step3 . step1) sb1) (step2 sb2)
    where step1 = M.map (\t -> vsubApp sb2 t)
          step2 = M.filterWithKey (\v _ -> M.notMember v sb1)
          step3 = M.filterWithKey (\v t -> (VarTrm [] v) /= t)

{-
-- apply a variable substitution (sub) to a freshness context (cxt)
vsubCtxApp :: VSub -> Cxt -> Maybe Cxt
vsubCtxApp sub cxt = fmap S.unions (sequence (map fn (S.elems cxt)))
    where fn cst @ (a, v) = case vsubApp v sub of
                                 Just t -> fresh a t
                                 Nothing -> Just (S.singleton cst)
-}
-------------------------------------------------------------------------------
renameAtm :: (Atm, Atm) -> Atm -> Atm
renameAtm (a, b) c = if c == a then b else c

renameVar :: (Var, Var) -> Var -> Var
renameVar (x, y) z = if z == x then y else z

renameAtmPrm :: (Atm, Atm) -> Prm -> Prm
renameAtmPrm as = map (\(a, b) -> (renameAtm as a, renameAtm as b))

renameAtmCtx :: (Atm, Atm) -> Ctx -> Ctx
renameAtmCtx as = S.map (\(a, v) -> (renameAtm as a, v))

renameVarCtx :: (Var, Var) -> Ctx -> Ctx
renameVarCtx vs = S.map (\(a, v) -> (a, renameVar vs v))

renameAtmTrm :: (Atm, Atm) -> Trm -> Trm
renameAtmTrm as (AtmTrm a)   = AtmTrm (renameAtm as a)
renameAtmTrm as (AbsTrm a t) = AbsTrm (renameAtm as a) (renameAtmTrm as t)
renameAtmTrm as (AppTrm f t) = AppTrm f (renameAtmTrm as t)
renameAtmTrm as (TplTrm ts)  = TplTrm (map (renameAtmTrm as) ts)
renameAtmTrm as (VarTrm p v) = VarTrm (renameAtmPrm as p) v

renameUAtmTrm :: (Atm, Atm) -> Trm -> Trm
renameUAtmTrm
    = let f ab as (AbsTrm b t) = AbsTrm b (f (b : ab) as t)
          f ab as @ (a, _) t = if a `elem` ab then t else renameAtmTrm as t
      in f []

renameVarTrm :: (Var, Var) -> Trm -> Trm
renameVarTrm vs (AbsTrm a t) = AbsTrm a (renameVarTrm vs t)
renameVarTrm vs (AppTrm f t) = AppTrm f (renameVarTrm vs t)
renameVarTrm vs (VarTrm p v) = VarTrm p (renameVar vs v)
renameVarTrm vs (TplTrm ts)  = TplTrm (map (renameVarTrm vs) ts)
renameVarTrm _ t             = t

renameAtmTrmCtx :: (Atm, Atm) -> TrmCtx -> TrmCtx
renameAtmTrmCtx ns (fc, t) = (fc', t')
    where fc' = renameAtmCtx ns fc
          t' = renameAtmTrm ns t

renameVarTrmCtx :: (Var, Var) -> TrmCtx -> TrmCtx
renameVarTrmCtx ns (fc, t) = (fc', t')
    where fc' = renameVarCtx ns fc
          t' = renameVarTrm ns t

-------------------------------------------------------------------------------
{-RULES-}

--data structure
type Rule = (Ctx, Trm, Trm)

