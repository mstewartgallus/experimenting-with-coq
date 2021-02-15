Import IfNotations.
Require Import Coq.Program.Basics.


Class EqDec {v : Set} := {
  eq_decide (x y : v) : {x = y} + {x <> y}
}.

Definition id (s : Set) := s.

(* Fix me put in laws *)
Class Functor (f : Set -> Set) := {
  map {a b : Set} : (a -> b) -> f a -> f b
}.

Class Monad (m : Set -> Set) `(Functor m) := {
  pure {a : Set} : a -> m a ;
  join {a : Set} : m (m a) -> m a
}.

Module MonadNotation.

Notation "'do' X <- A ; B" := (join (map (fun X => B) A)) (at level 200, X pattern, A at level 100, B at level 200).

End MonadNotation.

Section state.

Context {s : Set}.

Definition state (a : Set) : Set := s -> (s * a).

Definition get : state s := fun x => (x, x).
Definition put (x : s) : state unit := fun _ => (x, tt).

Instance state_Functor : Functor state := {
  map {A B} f (x : state A) := fun s0 =>
    let (s1, y) := x s0 in
    (s1, f y)
}.

Instance state_Monad : Monad state state_Functor := {
  pure (A : Set) (x : A) := fun s0 => (s0, x);
  join {A: Set} (a : state (state A)) := fun s0 => let (s1, b) := a s0 in b s1
}.
End state.

Definition injective {a b : Set} (f : a -> b) : Prop := forall x y, f x = f y -> x = y.
Definition inj (a b : Set) := { f : a -> b | injective f }.

Definition inj_id {a : Set} : inj a a.
eapply (exist _ (fun x => x)).
easy.
Defined.

Definition fanout {a b c : Set} (f : inj a b) (g : inj a c) : inj a (b * c).
destruct f, g.
eexists.
Unshelve.
2: {
 intro.
 apply (x H, x0 H).
}
intro.
intros.
inversion H.
elim (i0 x1 y).
easy.
apply H2.
Defined.

Definition inl {a b c : Set} (f : inj a b) : inj a (b + c).
destruct f.
eexists.
Unshelve.
2: {
 left.
 apply (x H).
}
intro.
intros.
inversion H.
elim (i x0 y).
easy.
apply H1.
Defined.

Definition inr {a b c : Set} (f : inj a b) : inj a (c + b).
destruct f.
eexists.
Unshelve.
2: {
 right.
 apply (x H).
}
intro.
intros.
inversion H.
elim (i x0 y).
easy.
apply H1.
Defined.

(* Fix me put in laws *)
Class InjectiveFunctor (f : Set -> Set) := {
  injmap {a b : Set}: inj a b -> f a -> f b
}.

(* Two functors of variables are the same if for some injective renaming they are the same. *)
Definition alpha {f : Set -> Set} `{InjectiveFunctor f} {a b : Set} x y : Prop :=
  exists (c : Set) (xf : inj a c) (yf : inj b c), injmap xf x = injmap yf y.

Definition identical {f : Set -> Set} `{InjectiveFunctor f} {a : Set} (x : f a) y (ident : x = y) : alpha x y.
rewrite <- ident.
eexists a.
eexists inj_id.
eexists inj_id.
eexists.
Qed.

Definition refl {f : Set -> Set} `{InjectiveFunctor f} {a : Set} (x : f a) : alpha x x.
eexists a.
eexists inj_id.
eexists inj_id.
easy.
Qed.

Definition symmetry {f : Set -> Set} `{InjectiveFunctor f} {a b : Set} (x : f a) (y : f b) (alph : alpha x y) : alpha y x.
destruct alph.
eexists x0.
destruct H0.
destruct H0.
eexists x2.
eexists x1.
easy.
Qed.

Section term.

Context { v : Set }.

Inductive term : Set :=
| var ( _ : v)
| app (_ : term) (_ : term)
| lam_ (_ : v -> term)
.

Definition lam f := lam_ (fun x => f (var x)).
End term.

Module TermNotation.

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

End TermNotation.

Import TermNotation.

Section cbn.
Context {v : Set}.

Definition store := v -> term (v := v).

Definition st := (store * term (v := v))%type.

CoInductive font : Set := { head : v ; left : font ; right : font }.

Definition insert `{EqDec v} x e s : store := fun x' =>
  if eq_decide x x' then e else s x'.

Fixpoint cbn `{EqDec v} (xs : font) (e : term (v := v)) (s0 : store) :=
match e with
| var x => Some (s0, s0 x)
| _{ ${lam_ f} e1 } =>
  let v := head xs in
  let y := f v in
  Some (insert v e1 s0, y)
| _{ e0 e1 } =>
  if cbn (left xs) e0 s0 is Some (s1, e'0) then Some (s1, _{ e'0 e1 }) else None
| _ => None
end.

End cbn.

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
Extraction "./step.hs" cbn.

Section spec.

Context {v : Set}.

(* Define a one-hole context type *)
Inductive term' : Set :=
| hole : term'
| lapp' : term' -> term (v := v) -> term'
| rapp' : term (v := v) -> term' -> term'
| lam' : (v -> term') -> term'.

Section substitution.
Variable h : term (v := v).
Fixpoint subst i :=
match i with
| hole => h
| lapp' i0 e1 => _{ ${subst i0 } e1 }
| rapp' e0 i1 => _{ e0 ${ subst i1 } }
| lam' i0 => lam_ (fun x => subst (i0 x))
end.
End substitution.

Notation "'E' [ h | e ]" := (subst e h) (e custom lam).
Reserved Notation "e ~> e'" (at level 50).

Inductive reduce : st -> st -> Prop :=
| reduce_store gamma x : (gamma, var x) ~> (gamma, gamma x)
| reduce_beta gamma h e0 e1 : (gamma, E[h | (fun x => ${e0 x}) e1 ]) ~> (gamma, E[h | ${e0 e1}])
where "e ~> e'" := (reduce e e').

Definition valid f := forall (x : st), if f x is Some y then x ~> y else True.

Definition strategy := { f | valid f }.

Definition fail : strategy.
eexists.
Unshelve.
2: {
  intro.
  apply None.
}
easy.
Defined.

Definition cbn' `{EqDec v} xs x := cbn xs (snd x) (fst x).

Definition cbn_valid `{EqDec v} xs : valid (cbn' xs).
intro.
destruct x.
induction t.
1: {
  cbv.
  apply reduce_store.
}
2: {
  cbv.
  trivial.
}
1: {
  admit.
}
Admitted.