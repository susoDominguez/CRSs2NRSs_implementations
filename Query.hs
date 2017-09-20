module Query where

import qualified Data.Map as M
import qualified Data.Set as S

import Alpha
import Rewriting
import Trm

-------------------------------------------------------------------------------
-- DATA STRUCTURES

-- constraint problem
type AQ = (Equ, Maybe Ctx, CPrb)

-- closedness
type CQ = (Maybe Ctx, [Trm])

-- rewriting
type RQ = ([Rule], Ctx, Trm)

-------------------------------------------------------------------------------

fn :: (VSub, Ctx) -> String
fn (sb, fc)
    | M.null sb && S.null fc = ""
    | M.null sb = ", if " ++ showCtx fc
    | S.null fc = ", if " ++ showVSub sb
    | otherwise = ", if " ++ showVSub sb ++ " and " ++ showCtx fc

runAQ :: AQ -> String
runAQ (eq, mfc, cp)
    = case (solveCPrb eq cp, mfc) of
          (Nothing, _) -> "False"
          (Just sol, Nothing) -> "True" ++ (fn sol)
          (Just (sb, fc2), Just fc1) -> if not (derives fc1 fc2)
                                        then "False"
                                        else "True" ++ (fn (sb, S.empty))

runCQ :: CQ -> String
runCQ (Nothing, (t1 : []))
    = case closedTrm (0, 0) t1 of
          Nothing -> "False"
          Just fc -> "True" ++ (fn (M.empty, fc))
runCQ (Nothing, (t1 : (t2 : [])))
    = case closedTrm (0, 0) (TplTrm [t1, t2]) of
          Nothing -> "False"
          Just fc -> "True" ++ (fn (M.empty, fc))
runCQ (Just fc1, (t1 : []))
    = show (closedTrmCtx (0, 0) (fc1, t1))
runCQ (Just fc1, (t1 : (t2 : [])))
    = if not (validRule (fc1, t1, t2))
      then "Invalid rule: meta-variables not contained in the LHS"
      else show (closedTrmCtx (0, 0) (fc1, TplTrm [t1, t2]))
runCQ (_, _) = "Invalid input" -- should not arise

runRQ :: RQ -> String
runRQ (rls, fc, t)
  | not (and (map snd bs1))
        = "Invalid rule (meta-variables not contained in the LHS): " ++ showRule (fn2 bs1)
  | not (all snd bs2)
        = "Invalid rule (not closed): " ++ showRule (fn2 bs2)
  | otherwise
        = showTrmCtx (snd (closedRewritesStar 1024 (0, 0) (fc, t) rls))
    where bs1 = map (\rl -> (rl, validRule rl)) rls
          bs2 = map (\rl -> (rl, closedRule (0, 0) rl)) rls
          fn2 xs = (fst . head) (dropWhile snd xs)
