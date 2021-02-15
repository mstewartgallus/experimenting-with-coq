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
 | App (Term v) (Term v)
 | Lam_ (v -> Term v)

type Store v = v -> Term v

data Font v =
   Build_font v (Font v) (Font v)

head :: (Font a1) -> a1
head f =
  case f of {
   Build_font head0 _ _ -> head0}

left :: (Font a1) -> Font a1
left f =
  case f of {
   Build_font _ left0 _ -> left0}

insert :: (EqDec a1) -> a1 -> (Term a1) -> (a1 -> Term a1) -> Store a1
insert h x e s x' =
  case eq_decide h x x' of {
   Prelude.True -> e;
   Prelude.False -> s x'}

cbn :: (EqDec a1) -> (Font a1) -> (Term a1) -> (Store a1) -> Prelude.Maybe
       ((,) (Store a1) (Term a1))
cbn h xs e s0 =
  case e of {
   Var x -> Prelude.Just ((,) s0 (s0 x));
   App e0 e1 ->
    case e0 of {
     Lam_ f ->
      let {v = head xs} in
      let {y = f v} in Prelude.Just ((,) (insert h v e1 s0) y);
     _ ->
      case cbn h (left xs) e0 s0 of {
       Prelude.Just p ->
        case p of {
         (,) s1 e'0 -> Prelude.Just ((,) s1 (App e'0 e1))};
       Prelude.Nothing -> Prelude.Nothing}};
   Lam_ _ -> Prelude.Nothing}

