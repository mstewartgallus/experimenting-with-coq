Import IfNotations.

Class EqDec {v : Set} := {
  eq_decide (x y : v) : {x = y} + {x <> y}
}.


Class Lambda {t : Set} := {
  app : t -> t -> t ;
  lam : (t -> t) -> t
}.

Declare Custom Entry lam.
Notation "_{ e }" := e (e custom lam at level 99).
Notation "x" := x (in custom lam at level 0, x constr at level 0).
Notation "f x" := (app f x) (in custom lam at level 1, left associativity).
Notation "'fun' x => y" :=
  (lam (fun x => y)) (in custom lam at level 90,
                     x ident,
                     y custom lam at level 99,
                     left associativity).
Notation "( x )" := x (in custom lam, x at level 99).
Notation "${ x }" := x (in custom lam, x constr at level 0).

Section model.

Variable v : Set.

Inductive term :=
| var (_ : v)
| pass (_ : term) (_ : term)
| lam_ (_ : v -> term)
.

Coercion var : v >-> term.
Instance term_lambda : @Lambda term := {
  app := pass ;
  lam f := lam_ (fun x => f x)
}.

(* My intuition is that a stack is kind of like a one hole context/evaluation context.
   An alternate representation might be:
 *)
Definition term' := term -> term.

Record ck := { control : term ; kont : term' }. 
Notation " 'E' [ h | e ]" := (h (e : term)) (e custom lam).

(* We use a very simple model of the heap as a function. *)
Definition store := v -> term.

Record model := { model_store : store ; expr : term }.
(*
I used the turnstile before while figuring things out but really this is a store not an environment.
I need to think up better notation/denotation.

fun store => E[kont|control] ?
*)
Notation "s |- ck" := {| model_store := s ; expr := ck |} (at level 70).

Definition put `{EqDec v} old x e : store :=
fun x' => if eq_decide x x' then e else old x'.

Reserved Notation "s0 ~> s1 " (at level 80).

Variant step: model -> model -> Prop := 
| step_var s (x: v) k :
   s |- E[k| x] ~> s |- E[k| ${s x}]

| step_pass s k e0 e1 :
   s |- E[k| e0 e1] ~> s |- E[fun x => _{ ${k x} e1 }| e0]

| step_lam `{EqDec v} s k f x e:
   s |- E[fun x => _{ ${k x} e } | ${lam_ f}] ~> put s x e |- E[k|${f x}]
where "st ~> st'" := (step st st').


(* FIXME I need to think of a less misleading name, the spec is very weak currently *)
(*
  If an interpreter takes a step (and succeeds!) then that implies that must have been a valid state transition.
*)
Definition valid state to (tick : state -> option state) :=
forall a,
exists b,
tick a = Some b ->
to a ~> to b.

Inductive ast :=
| ast_var (_ : v)
| ast_app (_ : ast) (_ : ast)
| ast_lam (_ : v -> ast)
.

Coercion ast_var : v >-> ast.
Instance ast_lambda : @Lambda ast := {
  app := ast_app ;
  lam f := ast_lam (fun x => f x)
}.


(* We use an old trick of lazily threading through new variables *)
CoInductive font : Set := { head : v ; left : font ; right : font }.

Inductive stack : Set :=
| hole
| lpass (_ : stack) (_ : ast).

(* We currently leak memory *)
Definition heap := list (v * ast).

Definition arbitrary : ast := _{ fun x => x }.

Section lookup.
Context `{EqDec v}.
Fixpoint lookup (hp : heap) : v -> ast :=
match hp with
| cons (x', h) t =>
   let t' := lookup t in
   fun x => if eq_decide x x' then h else t' x
| nil => fun _ => arbitrary
end.
End lookup.

Definition state := (heap * stack * ast) %type.

Definition go `{EqDec v} (fnt : font) s k e : option state :=
match e with
| ast_var x => Some (s, k, lookup s x)

| ast_app e0 e1 => Some (s, lpass k e1, e0)
| ast_lam f =>
   if k is lpass k' e0
   then
     let x := head fnt in
     Some (cons (x, e0) s, k', f x)
   else None
end.

Definition go' `{EqDec v} fnt st :=
match st with
| (s, k, e) => go fnt s k e
end.
Fixpoint to_term e :=
match e with
| ast_var x => var x
| ast_app e0 e1 => app (to_term e0) (to_term e1)
| ast_lam f => lam_ (fun x => to_term (f x))
end.

Section applyk.
Variable h : term.
Fixpoint applyk k :=
match k with
| hole => h
| lpass k e => pass (applyk k) (to_term e)
end.
End applyk.

Definition to_term' k : term' := fun x => applyk x k.

Fixpoint to_store `{EqDec v} (s : heap) : store :=
match s with
| cons (x, h) t =>
  let t' := to_store t in
  let h' := to_term h in
  put t' x h'
| nil => fun _ => _{ fun x => x }
end.

Definition models_put `{EqDec v} (h : heap) x (e : ast):
put (to_store h) x (to_term e) = to_store (cons (x, e) h).
induction h.
- cbn.
  trivial.
- cbn.
  trivial.
Qed.

Definition tautological `{EqDec v} x : if eq_decide x x then True else False.
case (eq_decide x x).
trivial.
intro.
contradiction.
Qed.

(* really messy *)
Definition models_store `{EqDec v} h : forall x, to_store h x = to_term (lookup h x).
induction h.
- cbn.
  trivial.
- destruct a.
  intro.
  cbv.
  rewrite -> IHh.
  rewrite <- IHh.
  rewrite -> IHh.
  destruct H.
  case (eq_decide0 v0 x).
  +
    intro.
    rewrite -> e.
    cbv.
    case (eq_decide0 x x).
    * intro.
      trivial.
    * intro.
      contradiction.
  + intro.
    case (eq_decide0 x v0).
    * intro.
      symmetry in e.
      contradiction.
    * intro.
      trivial.
      Qed.

Definition go_to_model `{EqDec v} (st : state) : model :=
match st with
| (s, k , e) => to_store s |- E[to_term' k| ${to_term e} ]
end.

Definition go_valid `{EqDec v} fnt : valid _ go_to_model (go' fnt).
intro a.
destruct a, p.
cbn.
(* Perform induction over all possible cases of control, then all cases of the stack *)
induction a.
+ cbn.
  eexists (h, s, lookup h v0).
  intro.
  cbn.
  rewrite <- (models_store _ _).
  eapply (step_var (to_store h) v0 (to_term' s)).
+ cbn.
  eexists (h, lpass s a2, a1).
  intro.
  apply (step_pass (to_store h) (to_term' s) (to_term a1) (to_term a2)).
+ cbn.
  induction s.
  - eexists (h, hole, arbitrary).
    intros.
    discriminate.
  - pose (x := head fnt).
    pose (h' := cons (x, a0) h).
    eexists (h', s, a x).
    intros.
    pose (str := to_store h).
    pose (str' := to_store h').
    cbn.
    eapply (step_lam str (to_term' s) (fun y => to_term (a y)) x (to_term a0)).
Qed.

End model.

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