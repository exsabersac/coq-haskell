(*
Impl: the reader / function monad (fun B => A -> B) — Haskell's ((->) r).
Functor / Applicative / Monad instances, plus Monad_Distributes over an
inner N so Compose can stack (A -> _) over other monads.

--------
Impl：读 / 函数单子（fun B => A → B）— 即 Haskell 的 ((->) r)。
含 Functor / Applicative / Monad，以及相对内层 N 的 Monad_Distributes，
以便 Compose 把 (A → _) 叠在其他单子上。
*)

Require Import Hask.Data.Functor.
Require Import Hask.Control.Applicative.
Require Import Hask.Control.Monad.
Require Import Hask.Control.Compose.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

(* fmap = post-compose / fmap：后复合 *)
#[export]
Instance Impl_Functor {A} : Functor (fun B => A -> B) := {
  fmap := fun A B f run => fun xs => f (run xs)
}.

(* pure = const; ap = S combinator / pure：常值；ap：S 组合子 *)
#[export]
Instance Impl_Applicative {A} : Applicative (fun B => A -> B) := {
  pure := fun _ x => fun _ => x;
  ap   := fun _ _ runf runx => fun xs => runf xs (runx xs)
}.

(* join f x = f x x  (diagonal) / join：对角应用 *)
#[export]
Instance Impl_Monad {A} : Monad (fun B => A -> B) := {
  join := fun A run => fun xs => run xs xs
}.

(* distribute: sequence reader over N / 把 reader 与内层 N 交换 *)
#[export]
Program Instance Impl_Monad_Distributes {A} `{Monad N} :
  @Monad_Distributes (fun B => A -> B) Impl_Monad N is_applicative.
Obligation 1.
  exact (X >>= fun f => f X0).
Defined.

Require Import FunctionalExtensionality.

Module ImplMonadLaws.

Import MonadLaws.

#[export]
Program Instance Impl_FunctorLaws {A} : FunctorLaws (fun B => A -> B).
#[export]
Program Instance Impl_ApplicativeLaws {A} : ApplicativeLaws (fun B => A -> B).
#[export]
Program Instance Impl_MonadLaws {A} : MonadLaws (fun B => A -> B).

#[export]
Program Instance Impl_Monad_DistributesLaws {A} `{MonadLaws N} :
  @Monad_DistributesLaws (fun B => A -> B) N _ Impl_Monad is_applicative
                         Impl_Monad_Distributes.
Obligation 1.
  unfold Impl_Monad_Distributes_obligation_1, comp, bind, id.
  extensionality x.
  extensionality x0.
  simpl.
  rewrite <- join_fmap_fmap_x, !fmap_comp_x.
  reflexivity.
Qed.
Obligation 2.
  unfold Impl_Monad_Distributes_obligation_1, comp, bind, id.
  extensionality x.
  extensionality x0.
  simpl.
  rewrite fmap_pure_x, join_pure_x.
  reflexivity.
Qed.
Obligation 3.
  unfold Impl_Monad_Distributes_obligation_1, comp, bind, id.
  extensionality x.
  extensionality x0.
  simpl.
  rewrite fmap_comp_x, join_fmap_pure_x.
  reflexivity.
Qed.
Obligation 4.
  unfold Impl_Monad_Distributes_obligation_1, comp, bind, id.
  extensionality x.
  extensionality x0.
  simpl.
  rewrite <- join_fmap_fmap_x, <- join_fmap_join_x, !fmap_comp_x.
  reflexivity.
Qed.

End ImplMonadLaws.
