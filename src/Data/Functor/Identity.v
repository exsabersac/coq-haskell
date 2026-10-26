(*
Identity functor/monad in two flavors:
  - Identity a := a          (type synonym; fmap/pure/join = id)
  - IdentityF                (inductive wrapper Id)
Both sit at the bottom of the F/A/M tower as the "no effect" case.

--------
恒等函子/单子的两种写法：
  - Identity a := a          （类型同义词；fmap/pure/join = id）
  - IdentityF                （归纳包装 Id）
二者都是 F/A/M 塔底端的「无效应」情形。
*)

Require Import Hask.Prelude.
Require Import Hask.Control.Monad.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.
Set Asymmetric Patterns.

(* Type-synonym Identity. / 类型同义词版 Identity。 *)

Definition Identity (a : Type) := a.

#[export]
Program Instance Identity_Functor : Functor Identity := {
  fmap := fun _ _ => id
}.

#[export]
Program Instance Identity_Applicative : Applicative Identity := {
  pure := fun _ => id;
  ap := fun _ _ => id
}.

#[export]
Program Instance Identity_Monad : Monad Identity := {
  join := fun _ => id
}.

(* Inductive wrapper IdentityF. / 归纳包装版 IdentityF。 *)
Inductive IdentityF (a : Type) := Id : a -> IdentityF a.

Definition runIdentityF `(x : IdentityF a) : a :=
  match x with Id y => y end.

#[export]
Program Instance IdentityF_Functor : Functor IdentityF := {
  fmap := fun _ _ f x => Id _ (f (runIdentityF x))
}.

#[export]
Program Instance IdentityF_Applicative : Applicative IdentityF := {
  pure := fun _ => Id _;
  ap := fun _ _ f x => Id _ (runIdentityF f (runIdentityF x))
}.

#[export]
Program Instance IdentityF_Monad : Monad IdentityF := {
  join := fun _ => runIdentityF
}.
