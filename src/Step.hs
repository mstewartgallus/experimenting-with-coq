{-# OPTIONS_GHC -cpp -XMagicHash #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module Step where

import qualified Prelude

#ifdef __GLASGOW_HASKELL__
import qualified GHC.Base
#else
-- HUGS
import qualified IOExts
#endif

#ifdef __GLASGOW_HASKELL__
unsafeCoerce :: a -> b
unsafeCoerce = GHC.Base.unsafeCoerce#
#else
-- HUGS
unsafeCoerce :: a -> b
unsafeCoerce = IOExts.unsafeCoerce
#endif

#ifdef __GLASGOW_HASKELL__
type Any = GHC.Base.Any
#else
-- HUGS
type Any = ()
#endif

__ :: any
__ = Prelude.error "Logical or arity value used"

eq_rect :: a1 -> a2 -> a1 -> a2
eq_rect _ f _ =
  f

type EqDec v =
  v -> v -> Prelude.Bool
  -- singleton inductive, whose constructor was Build_EqDec
  
eq_decide :: (EqDec a1) -> a1 -> a1 -> Prelude.Bool
eq_decide eqDec =
  eqDec

type Functor f =
  () -> () -> (Any -> Any) -> f -> f
  -- singleton inductive, whose constructor was Build_Functor
  
map :: (Functor a1) -> (a2 -> a3) -> a1 -> a1
map functor x x0 =
  unsafeCoerce functor __ __ x x0

data Monad m =
   Build_Monad (() -> Any -> m) (() -> m -> m)

pure :: (Functor a1) -> (Monad a1) -> a2 -> a1
pure _ monad x =
  case monad of {
   Build_Monad pure0 _ -> unsafeCoerce pure0 __ x}

join :: (Functor a1) -> (Monad a1) -> a1 -> a1
join _ monad x =
  case monad of {
   Build_Monad _ join0 -> join0 __ x}

type State s a = s -> (,) s a

get :: State a1 a1
get x =
  (,) x x

put :: a1 -> State a1 ()
put x _ =
  (,) x ()

state_Functor :: Functor (State a1 Any)
state_Functor _ _ f x s0 =
  case x s0 of {
   (,) s1 y -> (,) s1 (f y)}

state_Monad :: Monad (State a1 Any)
state_Monad =
  Build_Monad (\_ x s0 -> (,) s0 x) (\_ a s0 ->
    case a s0 of {
     (,) s1 b -> unsafeCoerce b s1})

data Term v =
   Var v
 | App (Term v) (Term v)
 | Lam v (Term v)

data D v =
   Var'
 | Lapp' (Term v) (Term v) (D v)
 | Rapp' (Term v) (Term v) (D v)
 | Lam' v (Term v) (D v)

diff :: a1 -> (Term a1) -> (Term a1) -> (D a1) -> Term a1
diff x h _ i =
  case i of {
   Var' -> h;
   Lapp' e0 e1 i0 -> App (diff x h e0 i0) e1;
   Rapp' e0 e1 i1 -> App e0 (diff x h e1 i1);
   Lam' y e0 i0 -> Lam y (diff x h e0 i0)}

var_helper :: a1 -> a1 -> D a1
var_helper x y =
  eq_rect x Var' y

lookup :: a1 -> (EqDec a1) -> (Term a1) -> Prelude.Maybe (D a1)
lookup x h e =
  case e of {
   Var y ->
    case eq_decide h x y of {
     Prelude.True -> Prelude.Just (var_helper x y);
     Prelude.False -> Prelude.Nothing};
   App e0 e1 ->
    let {s = lookup x h e0} in
    let {s0 = lookup x h e1} in
    case s of {
     Prelude.Just e'0 -> Prelude.Just (Lapp' e0 e1 e'0);
     Prelude.Nothing ->
      case s0 of {
       Prelude.Just e'1 -> Prelude.Just (Rapp' e0 e1 e'1);
       Prelude.Nothing -> Prelude.Nothing}};
   Lam y e0 ->
    case lookup x h e0 of {
     Prelude.Just e'0 -> Prelude.Just (Lam' y e0 e'0);
     Prelude.Nothing -> Prelude.Nothing}}

data Stream v =
   Build_stream v (Stream v)

head :: (Stream a1) -> a1
head s =
  case s of {
   Build_stream head0 _ -> head0}

tail :: (Stream a1) -> Stream a1
tail s =
  case s of {
   Build_stream _ tail0 -> tail0}

type Vars v a = State (Stream v) a

vars_Functor :: Functor (Vars a1 Any)
vars_Functor =
  state_Functor

vars_Monad :: Monad (Vars a1 Any)
vars_Monad =
  state_Monad

alloc :: Vars a1 a1
alloc =
  join (unsafeCoerce vars_Functor) (unsafeCoerce vars_Monad)
    (map (unsafeCoerce vars_Functor) (\s ->
      join (unsafeCoerce vars_Functor) (unsafeCoerce vars_Monad)
        (map (unsafeCoerce vars_Functor) (\_ ->
          pure vars_Functor vars_Monad (head s)) (put (tail s))))
      (unsafeCoerce get))

free :: a1 -> Vars a1 ()
free x =
  join (unsafeCoerce vars_Functor) (unsafeCoerce vars_Monad)
    (map (unsafeCoerce vars_Functor) (\s ->
      join (unsafeCoerce vars_Functor) (unsafeCoerce vars_Monad)
        (map (unsafeCoerce vars_Functor) (\_ ->
          pure vars_Functor vars_Monad ()) (put (Build_stream x s))))
      (unsafeCoerce get))

replace :: a1 -> (EqDec a1) -> ([] ((,) a1 a1)) -> a1
replace x h xs =
  case xs of {
   [] -> x;
   (:) p t ->
    case p of {
     (,) y subst ->
      case eq_decide h x y of {
       Prelude.True -> subst;
       Prelude.False -> replace x h t}}}

rename :: (EqDec a1) -> ([] ((,) a1 a1)) -> (Term a1) -> Vars a1 (Term a1)
rename h xs e =
  case e of {
   Var x ->
    pure (unsafeCoerce vars_Functor) (unsafeCoerce vars_Monad) (Var
      (replace x h xs));
   App f x ->
    join (unsafeCoerce vars_Functor) (unsafeCoerce vars_Monad)
      (map (unsafeCoerce vars_Functor) (\f' ->
        join (unsafeCoerce vars_Functor) (unsafeCoerce vars_Monad)
          (map (unsafeCoerce vars_Functor) (\x' ->
            pure vars_Functor vars_Monad (App f' x')) (rename h xs x)))
        (rename h xs f));
   Lam x e0 ->
    join (unsafeCoerce vars_Functor) (unsafeCoerce vars_Monad)
      (map (unsafeCoerce vars_Functor) (\x' ->
        join (unsafeCoerce vars_Functor) (unsafeCoerce vars_Monad)
          (map (unsafeCoerce vars_Functor) (\e' ->
            pure vars_Functor vars_Monad (Lam x' e'))
            (rename h ((:) ((,) x x') xs) e0))) (unsafeCoerce alloc))}

destroy_term :: (Term a1) -> Vars a1 ()
destroy_term e =
  case e of {
   Var _ -> pure (unsafeCoerce vars_Functor) (unsafeCoerce vars_Monad) ();
   App e0 e1 ->
    join (unsafeCoerce vars_Functor) (unsafeCoerce vars_Monad)
      (map (unsafeCoerce vars_Functor) (\_ -> destroy_term e1)
        (destroy_term e0));
   Lam x e0 ->
    join (unsafeCoerce vars_Functor) (unsafeCoerce vars_Monad)
      (map (unsafeCoerce vars_Functor) (\_ -> free x) (destroy_term e0))}

step :: (EqDec a1) -> (Term a1) -> Vars a1 (Prelude.Maybe (Term a1))
step h e =
  case e of {
   Var _ ->
    pure (unsafeCoerce vars_Functor) (unsafeCoerce vars_Monad)
      Prelude.Nothing;
   App e0 e1 ->
    case e0 of {
     Var _ ->
      join (unsafeCoerce vars_Functor) (unsafeCoerce vars_Monad)
        (map (unsafeCoerce vars_Functor) (\e'0 ->
          pure vars_Functor vars_Monad
            (case e'0 of {
              Prelude.Just e''0 -> Prelude.Just (App e''0 e1);
              Prelude.Nothing -> Prelude.Nothing})) (step h e0));
     App _ _ ->
      join (unsafeCoerce vars_Functor) (unsafeCoerce vars_Monad)
        (map (unsafeCoerce vars_Functor) (\e'0 ->
          pure vars_Functor vars_Monad
            (case e'0 of {
              Prelude.Just e''0 -> Prelude.Just (App e''0 e1);
              Prelude.Nothing -> Prelude.Nothing})) (step h e0));
     Lam x e2 ->
      case lookup x h e2 of {
       Prelude.Just ix ->
        join (unsafeCoerce vars_Functor) (unsafeCoerce vars_Monad)
          (map (unsafeCoerce vars_Functor) (\e'1 ->
            join (unsafeCoerce vars_Functor) (unsafeCoerce vars_Monad)
              (map (unsafeCoerce vars_Functor) (\e''1 ->
                pure vars_Functor vars_Monad (Prelude.Just
                  (let {e' = diff x e'1 e2 ix} in App (Lam x e') e''1)))
                (rename h [] e1))) (unsafeCoerce rename h [] e1));
       Prelude.Nothing ->
        join (unsafeCoerce vars_Functor) (unsafeCoerce vars_Monad)
          (map (unsafeCoerce vars_Functor) (\_ ->
            join (unsafeCoerce vars_Functor) (unsafeCoerce vars_Monad)
              (map (unsafeCoerce vars_Functor) (\_ ->
                pure vars_Functor vars_Monad (Prelude.Just e2)) (free x)))
            (unsafeCoerce destroy_term e1))}};
   Lam _ _ ->
    pure (unsafeCoerce vars_Functor) (unsafeCoerce vars_Monad)
      Prelude.Nothing}

