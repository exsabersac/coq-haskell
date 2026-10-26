(*
MonadBase (mtl-style): lift an action from a distinguished base monad b
into a stack m that sits on b. FunDep encodes the functional dependency
m -> b (which base a stack uses).
Only StateT instance is active here; Identity versions are commented out.

--------
MonadBase（mtl 风格）：把基单子 b 上的动作抬到「坐在 b 上」的栈 m。
FunDep 表示函数依赖 m → b（栈用哪一个基）。
此处仅激活 StateT 实例；Identity 版本被注释掉。
*)

(* Require Import Data.Functor.Identity. *)
Require Import Hask.Control.Monad.
Require Import Hask.Control.Monad.Trans.State.

Generalizable All Variables.
Unset Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

(* Functional dependency witness m1 ~> m2. / 函数依赖见证。 *)
Class FunDep {T : Type} (m1 m2 : T).

(* liftBase : b a -> m a. / 从基单子抬入栈。 *)
Class MonadBase (b : Type -> Type) `{Monad b} (m : Type -> Type) `{Monad m}
      `{FunDep (Type -> Type) m b} := {
  liftBase : forall a, b a -> m a
}.
Arguments liftBase {b _ m _ _ _ a} _.

(* #[export] *)
(* Instance FunDep_Id_Id : FunDep Identity Identity. *)

(* #[export] *)
(* Instance MonadBase_Id_Id : MonadBase Identity Identity := { *)
(*   liftBase := @id *)
(* }. *)

#[export]
Program Instance StateT_m_b {s : Type} {m b : Type -> Type}
         `{FunDep (Type -> Type) m b} :
  FunDep (StateT s m) b.

#[export]
Instance MonadBase_StateT {s : Type} {m b : Type -> Type}
         `{B : MonadBase b m} : MonadBase b (StateT s m) := {
  liftBase := fun A x st =>
                res <- liftBase x;
                @pure m _ (A * s) (res, st)
}.
