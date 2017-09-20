module RenameCrs(rnmCvars,safeSubs) where

import Exp
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Char as C



{-
The notion is that fun map passes the original book-keeping to a tuple
and it is only updated below but not returned back so no clashing.
However, set of vars free/used must be global, then we return it as part
of the solution and
apply a mapping with accumulator for the tuple
-}

--Barendregt's renaming convention function
rnmCvars = renameBinders M.empty

--safe substitutes
safeSubs m = let freeV = freeVarsSbs m 
             in M.fromList $ map (\ (k, a) -> (k, rnmCvarSbs freeV a))  (M.assocs m)  

--must add free cvars
renameBinders :: M.Map Cvar Cvar -> S.Set Cvar -> Exp -> (S.Set Cvar, Exp)
renameBinders  m s (VarExp a) =
  (s, VarExp (M.findWithDefault a a m))--if free no changes
renameBinders m s (Mapp x t) = let (s',exp) = renameBinders m s t
                               in (s', Mapp x exp)
renameBinders m s (FunExp f t) = let (s',exp) = renameBinders m s t
                                 in  (s', FunExp f exp)
renameBinders m s (TuplExp t) = let (s', exp) = L.mapAccumL (renameBinders m) s t
                               in (s', TuplExp exp) 
renameBinders m s (AbsExp a t) = let m' = renameAbs m s a
                                     a' = (m' M.! a)
                                     s' = S.unions [s,S.singleton a,S.singleton a']
                                     (s'',exp)=renameBinders m' s' t
                                 in  (s'', AbsExp a' exp)


renameAbs :: M.Map Cvar Cvar -> S.Set Cvar -> Cvar -> M.Map Cvar Cvar
renameAbs m s a
  | a `S.member` s =  M.insert a (aNewNameUp s (head a:[]) ) m --scope of previous[a] ends
  | otherwise = M.insert a a m --never seen before, stick to it




--recursively builds a new cvar, it stops when it's not in set of current ones
aNewNameUp :: S.Set Cvar -> String -> String
aNewNameUp s a
  | a `S.member` s = aNewNameUp s (if C.isDigit l then d ++ fun l else a ++ "0" )
  | otherwise = a --base case
  where  l = last a
         d = init a
         fun = show .  (1 +) . C.digitToInt

--rename one CRS sub, list of cvars(binders) converts into an Id map of binders
rnmCvarSbs::  S.Set Cvar -> Subs -> Subs
rnmCvarSbs s (vrs,exp) = (vrs, snd $ renameBinders (M.fromList $ L.zip vrs vrs) s exp)

--------------------------------------------------------------------------

