Import IfNotations.
Require Import Coq.Program.Basics.


Class EqDec {v : Set} := {
  eq_decide (x y : v) : {x = y} + {x <> y}
}.

Section term.

Context { v : Set }.

Inductive term : Set :=
| var ( _ : v)
| app (_ : term) (_ : term)
| lam (_ : v -> term)
.


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
Coercion var : v >-> term.

Definition heap := v -> term.

Record state := {
  control:term ;
  store:heap
}.

CoInductive font : Set := { head : v ; left : font ; right : font }.

Definition insert `{EqDec v} x e s : heap := fun x' =>
  if eq_decide x x' then e else s x'.

Fixpoint cbn `{EqDec v} (xs : font) (e : term) (s0 : heap) : option state :=
match e with
| var x => Some {| control := s0 x ; store := s0 |}
| _{ ${lam f} e1 } =>
  let v := head xs in
  let y := f v in
  Some {| control := y ; store := insert v e1 s0 |}
| _{ e0 e1 } =>
  if cbn (left xs) e0 s0 is Some st
  then
    let e'0 := control st in
    let s1 := store st in
    Some {| control := _{ e'0 e1 } ; store := s1 |}
  else None
| _ => None
end.

(* Define a one-hole context type *)
Inductive term' : Set :=
| hole : term'
| lapp' : term' -> term -> term'
| rapp' : term -> term' -> term'
| lam' : (v -> term') -> term'.

Section substitution.
Variable h : term.
Fixpoint subst i :=
match i with
| hole => h
| lapp' i0 e1 => _{ ${subst i0 } e1 }
| rapp' e0 i1 => _{ e0 ${ subst i1 } }
| lam' i0 => lam (fun x => subst (i0 x))
end.
End substitution.

Notation "'E' [ h | e ]" := (subst e h) (e custom lam).

Reserved Notation "e ~> e'" (at level 50).
Inductive step `{EqDec v} : state -> state -> Prop :=
| step_load h s (x:v) :
    {| control := E[h|x] ; store := s |} ~> {| control := E[h|${s x}] ; store := s |}
| step_beta h s f x e1 :
    {| control := E[h| _{ ${lam f} e1 }] ; store := s |} ~> {| control := E[h| ${f x}] ; store := insert x e1 s |}
where "e ~> e'" := (step e e').

Reserved Notation "e ~> e'" (at level 50).

Definition valid `{EqDec v} f := forall x y, f x = Some y -> x ~> y.

Definition strategy `{EqDec v} := { f | valid f }.

Definition fail `{EqDec v} : strategy.
eexists.
Unshelve.
2: {
  intro.
  apply None.
}
easy.
Defined.

Definition cbn' `{EqDec v} xs s0 := cbn xs (control s0) (store s0).
Definition cbn_valid `{EqDec v} xs : valid (cbn' xs).
intro.
intro.
case y.
destruct x.
cbn.
intros.
induction control0.
1: {
  inversion H0.
  apply (step_load hole).
}
2: {
     discriminate.
   }

Admitted.

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
Extraction "./Step.hs" cbn.
