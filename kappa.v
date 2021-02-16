Import IfNotations.

Class EqDec {v : Set} := {
  eq_decide (x y : v) : {x = y} + {x <> y}
}.

Section term.
(* I define terms in a parameteric higher order abstract style.
   As we go along variables become a sort of address/pointer.
 *)
Variable v : Set.

Inductive term :=
| var (_ : v)
| pass (_ : term) (_ : term)
| lam (_ : v -> term)
.

Declare Custom Entry lam.
Notation "_{ e }" := e (e custom lam at level 99).
Notation "x" := x (in custom lam at level 0, x constr at level 0).
Notation "f x" := (pass f x) (in custom lam at level 1, left associativity).
Notation "'fun' x => y" :=
  (lam (fun x => y)) (in custom lam at level 90,
                     x ident,
                     y custom lam at level 99,
                     left associativity).
Notation "( x )" := x (in custom lam, x at level 99).
Notation "${ x }" := x (in custom lam, x constr at level 0).

Coercion var : v >-> term.

(* My intuition is that a stack is kind of like a one hole context/evaluation context.
   An alternate representation might be:

   Definition term' := term -> term.
   Definition hole : term' := fun x => x.
   Definition lpass (k : term') (e : term) : term' := fun x =>
     pass (k x) e.

   I'm not totally sure which is better.
 *)
Inductive term' :=
| hole
| lpass (_ : term') (_ : term).

Record ck := { control : term ; kont : term' }. 
Notation " 'E' [ h | e ]" := {| control := e ; kont := h |} (e custom lam).

(* We use a very simple model of the heap as a function.
   Note that this very simple model leaks memory.
*)
Definition heap := v -> term.

Record state := { store : heap ; local : ck }.
(*
I used the turnstile before while figuring things out but really this is a store not an environment.
I need to think up better notation/denotation.

fun store => E[kont|control] ?
*)
Notation "s |- ck" := {| store := s ; local := ck |} (at level 70).

Definition put `{EqDec v} old x e : heap:=
fun x' => if eq_decide x x' then e else old x'.

Reserved Notation "s0 ~> s1 " (at level 80).

Variant step: state -> state -> Prop := 
| step_var s (x: v) k :
   s |- E[k| x] ~> s |- E[k| ${s x}]

| step_pass s k e0 e1 :
   s |- E[k| e0 e1] ~> s |- E[lpass k e1| e0]

| step_lam `{EqDec v} s k f x e:
   s |- E[lpass k e| ${lam f}] ~> put s x e |- E[k|${f x}]
where "st ~> st'" := (step st st').

(* FIXME I need to think of a less misleading name, the spec is very weak currently *)
(*
  If an interpreter takes a step (and succeeds!) then that implies that must have been a valid state transition.
*)
Definition valid (tick : state -> option state) := forall c s k,
exists c' s' k',
(tick (s |- E[k|c]) = Some (s |- E[k|c])) -> (s |- E[k|c]) ~> (s' |- E[k'|c']).

(* We use an old trick of lazily threading through new variables *)
CoInductive font : Set := { head : v ; left : font ; right : font }.

Fixpoint go `{EqDec v} (fnt : font) s k c :=
match c with
| var x => Some (s |- E[k |${s x}])

| _{ c0 c1 } => Some (s |- E[lpass k c1 | c0])
| lam f =>
   if k is lpass k' e0
   then
     let x := head fnt in
     go (right fnt) (put s x e0) k' (f x)
   else None
end.

Definition go_valid `{EqDec v} fnt : valid (fun st => go fnt (store st) (kont (local st)) (control (local st))).
intros c s k.
cbn.
(* Perform induction over all possible cases of control, then all cases of the stack *)
induction c.
+ cbn.
  eexists (s v0).
  eexists s.
  eexists k.
  intro.
  apply (step_var s v0 k).
+ cbn.
  eexists c1.
  eexists s.
  eexists (lpass k c2).
  intro.
  apply (step_pass s k c1 c2).
+ cbn.
  induction k.
  * (* I'm not precisely sure why we have to introduce an arbitrary term here but identity works well enough. *)
    eexists _{ fun x => x }.
    eexists s.
    eexists hole.
    discriminate.
  * eexists (t (head fnt)).
    eexists (put s (head fnt) t0).
    eexists k.
    intro.
    eapply (step_lam s k t (head fnt) t0).
Qed.

End term.

(* My language of choice is Haskell but a runtime of Ocaml or Scheme might be preferable. Not sure. *)
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