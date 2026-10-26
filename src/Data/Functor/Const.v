(*
Const c a ignores a and just stores c.
Both Functor and Contravariant act as id on the phantom parameter
(phantom type; useful in Lens getters / Fold).

--------
Const c a 忽略 a，只存 c。
Functor 与 Contravariant 对幻影参数的作用皆为 id
（幻影类型；常用于 Lens 的 getter / Fold）。
*)

Require Import Hask.Data.Functor.
Require Import Hask.Data.Functor.Contravariant.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

(* Phantom: Const c a ≡ c. / 幻影：Const c a ≡ c。 *)
Definition Const (c a : Type) := c.

#[export]
(* fmap = id (cannot touch c). / fmap = id（碰不到 c）。 *)
Program Instance Const_Functor (c : Type) : Functor (Const c) := {
  fmap := fun _ _ _ => id
}.

#[export]
(* contramap = id as well. / contramap 同样是 id。 *)
Program Instance Const_Contravariant (c : Type) : Contravariant (Const c) := {
  contramap := fun _ _ _ => id
}.
