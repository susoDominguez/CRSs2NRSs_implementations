module CRSvalidations(validateRls,validateCsubs,tplSizes) where

import Exp
import qualified Data.List as L
import qualified Data.Set as S
import qualified Data.Map as M
import RenameCrs


--Mvars on RHS are a subset of LHS
isValidRl :: CRule -> Bool
isValidRl (l , r) = mvarsExp r `S.isSubsetOf` mvarsExp l

--rules must be closed
isClosedRl :: CRule -> Bool
isClosedRl  = S.null . (uncurry set)
  where set l r = freeVars l `S.union` freeVars r

--Rules must have a fun exp on the LHS
isFunExp :: Exp -> Bool
isFunExp (FunExp _ _) = True
isFunExp _ = False

--test for validity. If returns [] then start computations 
validity ::  CRule -> String
validity rl
  | not . isFunExp $ fst rl =
    "LHS not a Function app: " ++ showRule rl ++ "."
  |  not (isValidRl rl) =
     "Invalid Rule (RHS Mvars not a subset of LHS): " ++ showRule rl ++ "."
  |  not $ isClosedRl rl =
     "Rule Not Closed: "++ showRule rl++ "."
  |  not $ arityP rl = "Arity is not preserved among Mvars occurrences in : " ++
                      showRule rl ++ "."
  |  otherwise = []

--arity must be preserved across metaVars, must be checked after checking isValidRl
--size must be 1 for all otherwise there's at least 1 occ w diff arity.
arityP:: CRule  -> Bool
arityP  = all  (\x-> S.size x ==1) .  snd . tplSizes

--returns [(metavar X, set containing arities across occurrences of X)]
tplSizes (l,r) = let mvrs = S.toList $ mvarsExp l
                 in ( mvrs, (map (\m ->  tplSize m (TuplExp [l,r])) mvrs))

tplSize :: Mvar ->  Exp -> S.Set Int
tplSize y (Mapp x (TuplExp t)) | x==y = S.singleton (length t)
tplSize y (FunExp _ t)  = tplSize  y t
tplSize y (TuplExp t)  = S.unions $ map (tplSize y) t 
tplSize y (AbsExp _ t)  = tplSize y t 
tplSize _ _ = S.empty


------

--CRS substitutes must be ground
ground t
  | S.null (cvarsExp t) = []
  | otherwise = "Substitute " ++ showExp t++ " must be ground." ++ "\n"

validateRls::[CRule] -> Either String [CRule]
validateRls rl = case unlines $ map  validity rl of
                  [] -> Right rl
                  p -> Left p

validateCsubs:: CSubs -> Either String CSubs
validateCsubs m = let (cvars, exps) = L.unzip $ M.elems m
                        in case unlines $ map ground exps of
                            [] -> Right m
                            p -> Left p
