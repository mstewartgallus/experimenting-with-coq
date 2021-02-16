module Step where

import qualified Prelude

type EqDec v =
  v -> v -> Prelude.Bool
  -- singleton inductive, whose constructor was Build_EqDec
  
eq_decide :: (EqDec a1) -> a1 -> a1 -> Prelude.Bool
eq_decide eqDec =
  eqDec

data Term v =
   Var v
 | Pass (Term v) (Term v)
 | Lam (v -> Term v)

data Term' v =
   Hole
 | Lpass (Term' v) (Term v)

data Ck v =
   Build_ck (Term v) (Term' v)

type Environ v = v -> Term v

data State v =
   Build_state (Environ v) (Ck v)

put :: (EqDec a1) -> (a1 -> Term a1) -> a1 -> (Term a1) -> Environ a1
put h old x e x' =
  case eq_decide h x x' of {
   Prelude.True -> e;
   Prelude.False -> old x'}

data Font v =
   Build_font v (Font v) (Font v)

head :: (Font a1) -> a1
head f =
  case f of {
   Build_font head0 _ _ -> head0}

right :: (Font a1) -> Font a1
right f =
  case f of {
   Build_font _ _ right0 -> right0}

go :: (EqDec a1) -> (Font a1) -> (Environ a1) -> (Term' a1) -> (Term 
      a1) -> Prelude.Maybe (State a1)
go h fnt g k e =
  case e of {
   Var x -> Prelude.Just (Build_state g (Build_ck (g x) k));
   Pass e0 e1 -> Prelude.Just (Build_state g (Build_ck e0 (Lpass k e1)));
   Lam f ->
    case k of {
     Hole -> Prelude.Nothing;
     Lpass k' e0 ->
      let {x = head fnt} in go h (right fnt) (put h g x e0) k' (f x)}}

