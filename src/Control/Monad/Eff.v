(*
Lightweight effect system sketch: Effect := (Type -> Type) -> Type;
Effects m [e1;…] is a heterogeneous list of effect handlers for base m.
TFree / Eff xs m a := Effects m xs -> m a.
Handles typeclass projects one effect from the list; liftF / interpret.
Examples: Abortive + Reader over Maybe. Not in default _CoqProject.
(EffPlain.v is a variant fixed to an axiomatic IO base.)

--------
轻量效应系统草图：Effect := (Type → Type) → Type；
Effects m [e1;…] 是基单子 m 上的效应处理器异构列表。
TFree / Eff xs m a := Effects m xs → m a。
Handles 从列表投影某一效应；liftF / interpret。
示例：Maybe 上的 Abortive + Reader。默认不进 _CoqProject。
（EffPlain.v 是固定到公理 IO 基的变体。）
*)

Require Import
  Hask.Control.Monad
  Hask.Data.Maybe
  Coq.Lists.List.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Import ListNotations.

(* Effect descriptor parameterized by base monad. / 由基单子参数化的效应描述符。 *)
Definition Effect := (Type -> Type) -> Type.

Inductive Effects (m : Type -> Type) : list Effect -> Type :=
  | NilE : Effects m []
  | ConsE effects : forall effect : Effect,
      effect m -> Effects m effects -> Effects m (effect :: effects).

Arguments ConsE : default implicits.

Definition combine `(e : effect m) `(xs : Effects m effects) :
  Effects m (effect :: effects) := ConsE _ e xs.

Infix ".:" := combine (at level 48, right associativity).

Class Handles (fs : list Effect) (effect : Effect) := {
  getEffect : forall m, Effects m fs -> effect m
}.

#[export]
Instance Handles_hd {fs : list Effect}  {f : Effect} :
  Handles (f :: fs) f.
Proof.
  constructor; intros.
  inversion X.
  exact X0.
Defined.

#[export]
Instance Handles_tl `{_ : Handles fs f} : Handles (x :: fs) f.
Proof.
  constructor; intros.
  inversion H.
  apply getEffect0.
  inversion X.
  exact X1.
Defined.

(* Program given a bundle of handlers. / 给定处理器束的程序。 *)
Definition TFree `(xs : list Effect) m a :=
  Effects m xs -> m a.

Definition Eff := TFree.

Definition liftF `{Handles effects effect} `{Monad m}
  `(getOp : effect m -> m a) : Eff effects m a :=
  fun effects => getOp (getEffect m effects).

Definition interpret `{H : Monad m} `(interpreter : Effects m effects)
  `(program : Eff effects m a) : m a := program interpreter.

#[export]
Instance TFree_Functor `(xs : list Effect) `{Monad m} : Functor (TFree xs m) := {
  fmap := fun A B f run => fun xs => fmap f (run xs)
}.

#[export]
Instance TFree_Applicative `(xs : list Effect) `{Monad m} : Applicative (TFree xs m) := {
  pure := fun _ x => fun xs => pure x;
  ap   := fun A B runf runx => fun xs => runf xs <*> runx xs
}.

#[export]
Instance TFree_Monad `(xs : list Effect) `{Monad m} : Monad (TFree xs m) := {
  join := fun A run => fun xs => run xs >>= fun f => f xs
}.

Record Abortive (m : Type -> Type) := {
  abortE : m unit
}.

Definition abort `{Handles r Abortive} : Eff r unit :=
  liftF abortE.

Record Reader (e : Type) (m : Type -> Type) := {
  askE : m e
}.

Definition ask `{Handles r (Reader e)} : Eff r e :=
  liftF (askE e).

Require Import Arith.

Set Printing Universes.

Definition example1 `{Handles r (Reader nat)} `{Handles r Abortive} :
  Eff r nat :=
  (fun x y => y + 15) <$> abort <*> ask.

Definition maybeInterpreter : Effects Maybe [Reader nat; Abortive] :=
  combine {| askE   := Just 10 |} (combine {| abortE := Nothing |} (NilE _)).

Definition run {a} : Eff [Reader nat; Abortive] a -> Maybe a :=
  interpret maybeInterpreter.

Example run_example1 : run example1 = Nothing.
Proof. reflexivity. Qed.

Definition example2 `{Handles r (Reader nat)} : Eff r nat :=
  fmap (plus 15) ask.

Example run_example2 : run example2 = Just 25.
Proof. reflexivity. Qed.

(*
Definition example3 `{Handles r (Reader nat)} `{Handles r Abortive} :
  Eff r nat :=
  v <- ask;
  if leb v 15
  then abort ;; pure 0
  else pure (v+1).

Example run_example3 : run example3 = None.
Proof. reflexivity. Qed.
*)
