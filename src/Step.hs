module Step where

import qualified Prelude

type EqDec v =
  v -> v -> Prelude.Bool
  -- singleton inductive, whose constructor was Build_EqDec
  
eq_decide :: (EqDec a1) -> a1 -> a1 -> Prelude.Bool
eq_decide eqDec =
  eqDec

data Lambda t =
   Build_Lambda (t -> t -> t) ((t -> t) -> t)

lam :: (Lambda a1) -> (a1 -> a1) -> a1
lam lambda =
  case lambda of {
   Build_Lambda _ lam0 -> lam0}

data Ast v =
   Ast_var v
 | Ast_app (Ast v) (Ast v)
 | Ast_lam (v -> Ast v)

ast_lambda :: Lambda (Ast a1)
ast_lambda =
  Build_Lambda (\x x0 -> Ast_app x x0) (\f -> Ast_lam (\x -> f (Ast_var x)))

data Font v =
   Build_font v (Font v) (Font v)

head :: (Font a1) -> a1
head f =
  case f of {
   Build_font head0 _ _ -> head0}

data Stack v =
   Hole
 | Lpass (Stack v) (Ast v)

type Heap v = [] ((,) v (Ast v))

arbitrary :: Ast a1
arbitrary =
  lam ast_lambda (\x -> x)

lookup :: (EqDec a1) -> (Heap a1) -> a1 -> Ast a1
lookup h hp =
  case hp of {
   [] -> (\_ -> arbitrary);
   (:) p t ->
    case p of {
     (,) x' h0 ->
      let {t' = lookup h t} in
      (\x ->
      case eq_decide h x x' of {
       Prelude.True -> h0;
       Prelude.False -> t' x})}}

type State v = (,) ((,) (Heap v) (Stack v)) (Ast v)

go :: (EqDec a1) -> (Font a1) -> (Heap a1) -> (Stack a1) -> (Ast a1) ->
      Prelude.Maybe (State a1)
go h fnt s k e =
  case e of {
   Ast_var x -> Prelude.Just ((,) ((,) s k) (lookup h s x));
   Ast_app e0 e1 -> Prelude.Just ((,) ((,) s (Lpass k e1)) e0);
   Ast_lam f ->
    case k of {
     Hole -> Prelude.Nothing;
     Lpass k' e0 ->
      let {x = head fnt} in
      Prelude.Just ((,) ((,) ((:) ((,) x e0) s) k') (f x))}}

