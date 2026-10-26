(*
Semigroup: associative binary mappend (⨂).
Laws sit in the class. Maybe lifts Semigroup a by
appending Just payloads and absorbing Nothing.

--------
半群：结合的二元 mappend（⨂）。
定律写在类内。Maybe 在 Just 上合并、Nothing 作吸收元，
把 Semigroup a 抬到 Maybe a。
*)

Require Import Hask.Prelude.
Require Import Hask.Data.Maybe.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

(* Class: associative append. / 类：结合的拼接。 *)
Class Semigroup (m : Type) := {
  mappend : m -> m -> m;

  mappend_assoc : forall a b c, mappend a (mappend b c) = mappend (mappend a b) c;
}.

Arguments mappend {m _} _ _.

Infix "⨂" := mappend (at level 41, right associativity).

(* Lift Semigroup through Maybe. / 经 Maybe 抬升半群。 *)
Definition Maybe_append `{Semigroup a} (x y : Maybe a) : Maybe a :=
  match x, y with
  | Nothing, x     => x
  | x, Nothing     => x
  | Just x, Just y => Just (x ⨂ y)
  end.

#[export]
Program Instance Semigroup_Maybe `{Semigroup a} : Semigroup (Maybe a) := {
  mappend := Maybe_append
}.
Next Obligation.
  destruct a0, b, c; simpl; try reflexivity.
  now rewrite mappend_assoc.
Qed.
