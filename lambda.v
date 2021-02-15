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
| lam (_ : v) (_ : term)
.

End term.

Module TermNotation.

Declare Custom Entry lam.
Notation "_{ e }" := e (e custom lam at level 99).
Notation "x" := x (in custom lam at level 0, x constr at level 0).
Notation "f x" := (app f x) (in custom lam at level 1, left associativity).
Notation "'fun' x => y" :=
  (lam x y) (in custom lam at level 90,
                     x constr at level 99,
                     y custom lam at level 99,
                     left associativity).
Notation "( x )" := x (in custom lam, x at level 99).
Notation "${ x }" := x (in custom lam, x constr at level 0).

End TermNotation.

Section termf.
Variables (a b : Set) (f : a -> b).

Fixpoint m (e : @term a) : @term b :=
match e with
| var x => var (f x)
| app e0 e1 => app (m e0) (m e1)
| lam x e0 => lam (f x) (m e0)
end.

End termf.

Instance term_Functor : Functor (@term) := { map := m }.


(* Find one possible one-hole context of a lambda term on the free variable "x". *)

Section term'.

Import TermNotation.

Context {v : Set}.

Definition term' := term (v := v) -> term (v := v).

Variable x : v.

Reserved Notation "∈ e" (at level 10).
Reserved Notation "∉ e" (at level 10).

Inductive occurs : term -> Prop :=
| in_var : ∈ (var x)
| in_lapp {e0 e1} : ∈ e0 -> ∈ _{ e0 e1 }
| in_rapp {e0 e1} : ∈ e1 -> ∈ _{ e0 e1 }
| in_lam {y e0} : ∈ e0 -> ∈ _{ fun y => e0 }
where "∈ e" := (occurs e).

Inductive not_occurs : term -> Prop :=
| not_var {y} : x <> y -> ∉ (var y)
| not_app {e0 e1} : ∉ e0 -> ∉ e1 -> ∉ _{ e0 e1 }
| not_lam {y e0} : ∉ e0 -> ∉ _{ fun y => e0 }
where "∉ e" := (not_occurs e).

Inductive D : term -> Set :=
| var' : D (var x)
| lapp' {e0 e1} : D e0 -> D _{ e0 e1 }
| rapp' {e0 e1} : D e1 -> D _{ e0 e1 }
| lam' {y e0} : D e0 -> D _{ fun y => e0 }
.

Section atpoint.
Variable h : term (v := v).

Reserved Notation "∂ y | ∂ x" (at level 0).

Fixpoint diff e (i : D e) :=
match i with
| var' => h
| @lapp' e0 e1 i0 => _{ ${∂e0|∂i0} e1 }
| @rapp' e0 e1 i1 => _{ e0 ${ ∂e1 | ∂i1 } }
| @lam' y e0 i0 => _{ fun y => ${ ∂e0|∂i0 } }
end where "∂ e | ∂ i" := (diff e i).

End atpoint.

Definition var_helper {y} : x = y -> D (var y).
intro.
rewrite <- H.
apply var'.
Defined.

Fixpoint lookup `{EqDec v} e : D e + { ∉ e } :=
match e with
| var y =>
   match eq_decide x y with
    | left _ eq => inleft (var_helper eq)
    | right _ neq => inright (not_var neq)
   end
| app e0 e1 =>
   match (lookup e0, lookup e1) with
   | (inleft e'0, _) => inleft (lapp' e'0)
   | (_, inleft e'1) => inleft (rapp' e'1)
   | (inright n0, inright n1) => inright (not_app n0 n1)
   end
| lam y e0 =>
   match lookup e0 with
     | inleft e'0 => inleft (lam' e'0)
     | inright n0 => inright (not_lam n0)
   end
end .

End term'.

Section variables.

Context { v : Set }.

(* Provide a utility monad *)

(* I think I need to change things to use a partial order not equality *)
CoInductive stream : Set := { head : v ; tail : stream }.

Definition vars := @state stream.
Instance vars_Functor : Functor vars := state_Functor.
Instance vars_Monad : Monad vars vars_Functor := state_Monad.

Import MonadNotation.
Import TermNotation.

Definition alloc : vars v := do
  s <- get ; do
  _ <- put (tail s) ;
  pure (head s).


Definition free (x : v) : vars unit := do
  s <- get ; do
  _ <- put {| head := x ; tail := s |} ;
  pure tt.


Section s3.
Variable x : v.
Fixpoint replace `{EqDec v} (xs : list (v * v)) :=
match xs with
| nil => x
| cons (y, subst) t => if eq_decide x y is left _ _ then subst else replace t
end.
End s3.

Fixpoint rename `{EqDec v} (xs : list (v * v)) (e : term) : vars term :=
match e with
| var x => pure (var (replace x xs))
| _{ f x } => do
   f' <- rename xs f ; do
   x' <- rename xs x ;
   pure _{ f' x' }
| _{ fun x => e } => do
   x' <- alloc ; do
   e' <- rename ((x, x') :: xs) e ;
   pure _{ fun x' => e' }
end.

(* Only recycle bound variables *)
Fixpoint destroy_term (e : term) : vars unit :=
match e with
| var x => pure tt
| _{ e0 e1 } => do
  _ <- destroy_term e0 ;
  destroy_term e1
| _{ fun x => e0 } => do
   _ <- destroy_term e0 ;
   free x
end
.

Definition identity: vars term := do
  x0 <- alloc ; do
  x1 <- alloc ; 
  pure _{ (fun x0 => ${var x0}) (fun x1 => ${var x1}) }. 

(*
Renaming at every substitution should avoid capture AND sharing,
not sure if that's good or bad.
Not sure how to double check/formally prove capture is actually avoided.
*)

Fixpoint step `{EqDec v} e : vars (option term):=
match e with
| _{ (fun x => e0) e1 } =>
  if lookup x e0 is inleft ix then do
    e'1 <- rename nil e1 ; do
    e''1 <- rename nil e1 ;
    pure (Some (let e' := diff x e'1 e0 ix in _{ (fun x => e')  e''1 }))
  else do
  _ <- destroy_term e1 ; do
  _ <- free x ;
  pure (Some e0)
| _{ e0 e1 }  => do
  e'0 <- step e0 ;
  pure (if e'0 is Some e''0 then Some _{ e''0 e1 } else None)
| _ => pure None
end .

End variables.

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
Extraction "./step.hs" step.


(* I think I need to change things to use a partial order not equality *)
CoInductive font (a : Set) : Set := { head : a ; left : font a ; right : font a }.

Definition decide_font v (x y : font v) : {x = y} + {x <> y}.


Instance font_eq {a} : @EqDec (font a).


Fixpoint approx (fuel : nat) (e : term) : term :=
if fuel is S n then
  if step e is Some e' then approx n e' else
  e else
e.

Eval cbv in (fun v => approx 5 (identity v)).

End s1.
