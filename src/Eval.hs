-- |
-- Module      : Eval
-- Description : Evalúa un término siguiendo la semántica big-step
-- Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
-- License     : GPL-3
-- Maintainer  : mauro@fceia.unr.edu.ar
-- Stability   : experimental
--
-- Este módulo evalúa términos siguiendo la semántica big-step (estrategia CBV)
module Eval where

import Common (abort)
import Core
import MonadFD4 (MonadFD4, failFD4, lookupDecl, printFD4)
import PPrint (ppTTerm, ppName)
import Subst (subst, subst2)

-- | Semántica de operadores binarios
semOp :: BinaryOp -> Int -> Int -> Int
semOp Add x y = x + y
semOp Sub x y = max 0 (x - y)

-- | Evaluador de términos CBV
eval :: (MonadFD4 m) => TTerm -> m TTerm
eval (Var _ (Global nm)) = do
  -- unfold and keep going
  mtm <- lookupDecl nm
  case mtm of
    Nothing ->
      failFD4 $ "Error de ejecución: variable no declarada: " ++ ppName nm
    Just t -> eval t
eval (App p l r) = do
  le <- eval l
  re <- eval r
  case (le, re) of
    (Lam _ y _ m, n) -> eval (subst n m)
    (ff@(Fix _ f _ _ _ t), n) -> eval (subst2 ff n t)
    _ -> abort ("Error de tipo en runtime " ++ show (le, re))
eval (Pnt p lit t) = do
  te <- eval t
  case te of
    Lit _ (N n) -> do
      printFD4 (unS lit ++ show n)
      return te
    _ -> abort "Error de tipo en runtime!: Print"
eval (BOp p op t u) = do
  te <- eval t
  ue <- eval u
  case (te, ue) of
    (Lit _ (N n), Lit _ (N m)) ->
      return $
        Lit p (N (semOp op n m))
    _ -> do
      pt <- ppTTerm te
      abort $ "Error de tipo en runtime!: BinaryOp " ++ pt
eval (IfZ p c t e) = do
  ce <- eval c
  case ce of
    Lit _ (N 0) -> eval t
    Lit _ (N _) -> eval e
    c' -> abort "Error de tipo en runtime!: IfZ"
eval (Let _ _ _ m n) = do
  v <- eval m
  eval (subst v n)
-- nada más para reducir
eval t = return t
