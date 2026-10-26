(*
Traversable: sequence flips t (f a) → f (t a) for Applicative f
(laws sketched in comments; not proven here).
Tupersable is a tuple-specialized variant that does not need
Applicative on the "state" component.

--------
Traversable：sequence 把 t (f a) 翻成 f (t a)（f 为应用子；
定律仅注释，本文件未证）。
Tupersable 是面向元组的特化，不要求“状态”分量是应用子。
*)

Require Import
  Hask.Control.Monad
  Hask.Data.Maybe.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

(* Class: effectful traversal via sequence. / 类：经 sequence 做带效应遍历。 *)
Class Traversable `{Functor t} := {
  sequence : forall `{Applicative f} a, t (f a) -> f (t a)

  (* naturality
       t . sequence = sequence . fmap t for every applicative transformation t
     identity
       sequence . fmap Identity = Identity
     composition
       sequence . fmap Compose = Compose . fmap sequence . sequence
  *)
}.

Arguments sequence {t H _ f _ a} _.

Arguments Traversable t [H].

(* Tupersable: Traversable specialized to tuples — no Applicative on rep.
   --------
   Tupersable：Traversable 对元组的特化——rep 不必是应用子。 *)

Class Tupersable {rep} `{Functor t} := {
  sequenceT : forall a, rep -> t (rep * a)%type -> rep * t a
}.

Arguments sequenceT {rep t H _ a} _ _.

Arguments Tupersable rep t [H].

#[export]
(* Maybe: Nothing → pure Nothing; Just effect → fmap Just. / Maybe 遍历。 *)
Instance Maybe_Traversable : Traversable Maybe := {
  sequence := fun _ _ A x =>
    match x with
    | Nothing => pure Nothing
    | Just x  => fmap Just x
    end
}.

#[export]
(* Thread rep through Maybe of pairs. / 经 Maybe 的配对线程化 rep。 *)
Instance Maybe_Tupersable {rep} : Tupersable rep Maybe := {
  sequenceT := fun A (s : rep) x =>
    match x with
    | Nothing => (s, Nothing)
    | Just (s', x)  => (s', Just x)
    end
}.
