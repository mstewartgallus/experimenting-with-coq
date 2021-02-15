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
 | Lam (v -> Term v)

type Heap v = v -> Term v

data State v =
   Build_state (Term v) (Heap v)

control :: (State a1) -> Term a1
control s =
  case s of {
   Build_state control0 _ -> control0}

store :: (State a1) -> Heap a1
store s =
  case s of {
   Build_state _ store0 -> store0}

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

insert :: (EqDec a1) -> a1 -> (Term a1) -> (a1 -> Term a1) -> Heap a1
insert h x e s x' =
  case eq_decide h x x' of {
   Prelude.True -> e;
   Prelude.False -> s x'}

cbn :: (EqDec a1) -> (Font a1) -> (Term a1) -> (Heap a1) -> Prelude.Maybe
       (State a1)
cbn h xs e s0 =
  case e of {
   Var x -> Prelude.Just (Build_state (s0 x) s0);
   App e0 e1 ->
    case e0 of {
     Lam f ->
      let {v = head xs} in
      let {y = f v} in Prelude.Just (Build_state y (insert h v e1 s0));
     _ ->
      case cbn h (left xs) e0 s0 of {
       Prelude.Just st ->
        let {e'0 = control st} in
        let {s1 = store st} in Prelude.Just (Build_state (App e'0 e1) s1);
       Prelude.Nothing -> Prelude.Nothing}};
   Lam _ -> Prelude.Nothing}

