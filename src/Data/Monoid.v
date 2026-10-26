(*
Monoid: Semigroup plus unit mempty with left/right identity laws.
option inherits Monoid when the payload does (None = mempty).

--------
幺半群：半群加上单位元 mempty，及左右单位律。
载荷有 Monoid 时，option 继承（None = mempty）。
*)

Require Export Hask.Data.Semigroup.
Require Import Hask.Prelude.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

(* Class: Semigroup + mempty. / 类：半群 + 单位元。 *)
Class Monoid (m : Type) := {
  is_semigroup :> Semigroup m;

  mempty : m;

  mempty_left  : forall a, mappend mempty a = a;
  mempty_right : forall a, mappend a mempty = a;
}.

#[export]
(* None is the unit; Just uses underlying mappend. / None 为单位元。 *)
Program Instance Monoid_option `{Monoid a} : Monoid (option a) := {
  mempty := None
}.
Next Obligation. destruct a0; reflexivity. Qed.
