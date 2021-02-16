Import IfNotations.
Require Import Coq.Lists.List.

Class EqDec {v : Set} := {
  eq_decide (x y : v) : {x = y} + {x <> y}
}.

Section term.
Variable v : Set.

Inductive term :=
| var (_ : v)
| pass (_ : term) (_ : term)
| lam (_ : v -> term)
.

Inductive term' :=
| hole
| lpass (_ : term') (_ : term).

Section applyk.
Variable repl : term.
Fixpoint applyk k :=
match k with
| hole => repl
| lpass k e => pass (applyk k) e
end.
End applyk.

Record ck := { control : term ; kont : term' }. 
Notation " 'E' [ h | e ]" := {| control := e ; kont := h |}.

Definition environ := v -> term.

Context `{EqDec v}.


Record state := { assumption : environ ; consequence : ck }.

Notation "g |- ck" := {| assumption := g ; consequence := ck |} (at level 70).

Definition put old x e : environ:=
fun x' => if eq_decide x x' then e else old x'.

Reserved Notation "e0 ~> e1 " (at level 80).

Variant step : state -> state -> Prop := 
| step_var env x k :
   env |- E[k|var x] ~> env |- E[k|env x]

| step_pass env k e0 e1 :
   env |- E[k|pass e0 e1] ~> env |- E[lpass k e1|e0]

| step_lam env k f x e:
   env |- E[lpass k e |lam f] ~> put env x e |- E[k|f x]
where "e ~> e'" := (step e e').

Definition valid (f : state -> option state) := forall c e k,
exists c' e' k',
(f (e |- E[k|c]) = Some (e |- E[k|c])) -> (e |- E[k|c]) ~> (e' |- E[k'|c']).

(* FIXMEe rule out infinite loops *)

CoInductive font : Set := { head : v ; left : font ; right : font }.

Fixpoint go (fnt : font) g k e :=
match e with
| var x => Some (g |- E[k | g x])

| pass e0 e1 => Some (g |- E[lpass k e1 | e0])
| lam f =>
   if k is lpass k' e0
   then
     let x := head fnt in
     go (right fnt) (put g x e0) k' (f x)
   else None
end.

Definition go_valid `{EqDec v} fnt : valid (fun st => go fnt (assumption st) (kont (consequence st)) (control (consequence st))).
intros c e k.
cbn.
induction c.
+ cbn.
  eexists (e v0).
  eexists e.
  eexists k.
  intro.
  apply (step_var e v0 k).
+ cbn.
  eexists c1.
  eexists e.
  eexists (lpass k c2).
  intro.
  apply (step_pass e k c1 c2).
+ cbn.
  induction k.
  * eexists (lam (fun x => var x)).
    eexists e.
    eexists hole.
    discriminate.
  * eexists (t (head fnt)).
    eexists (put e (head fnt) t0).
    eexists k.
    intro.
    eapply (step_lam e k t (head fnt) t0).
Qed.

End term.

Set Primitive Projections.

Require Extraction.

Extraction Language Haskell.
Extract Inductive bool => "Prelude.Bool" ["Prelude.True" "Prelude.False"].
Extract Inductive sumbool => "Prelude.Bool" ["Prelude.True" "Prelude.False"].
Extract Inductive sumor => "Prelude.Maybe" ["Prelude.Just" "Prelude.Nothing"].
Extract Inductive option => "Prelude.Maybe" ["Prelude.Just" "Prelude.Nothing"].
Extract Inductive prod => "(,)" ["(,)"].
Extract Inductive unit => "()" ["()"].
Extract Inductive list => "[]" ["[]" "(:)"].
Extraction "./Step.hs" go.