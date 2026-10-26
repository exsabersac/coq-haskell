(*
van Laarhoven Lens: Lens s t a b = ∀ f. Functor f → (a → f b) → s → f t.
Lens' is monomorphic. Getter / Getting specialize for reads (Const / Contravariant).
set / over / view plus product lenses _1 _2; StateT helpers (+= .= %=).
LensLaws: get-set / set-get / set-set.

--------
van Laarhoven 透镜：Lens s t a b = ∀ f. Functor f → (a → f b) → s → f t。
Lens' 为单态。Getter / Getting 专用于读（Const / Contravariant）。
set / over / view 与积透镜 _1 _2；StateT 辅助（+= .= %=）。
LensLaws：get-set / set-get / set-set。
*)

Require Import Hask.Prelude.
Require Import Hask.Control.Monad.
Require Import Hask.Data.Functor.Contravariant.
Require Import Hask.Data.Functor.Identity.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Generalizable All Variables.
Set Primitive Projections.
Unset Transparent Obligations.

(* Polymorphic VL lens / 多态 VL 透镜 *)
Definition Lens s t a b := forall f, Functor f -> (a -> f b) -> s -> f t.
Definition Lens' s a := Lens s s a a.

(* Read-only optic (needs Contravariant) / 只读 optic（需 Contravariant） *)
Definition Getter s a :=
  forall f, Functor f -> Contravariant f -> (a -> f a) -> s -> f s.

(* Concrete getting via Const / 用 Const 具体化的 Getting *)
Definition Getting r s a := (a -> Const r a) -> s -> Const r s.

Notation "x &+ f" := (f x) (at level 41, only parsing).

(* set / over via Identity; view via Const id
   --------
   set / over 走 Identity；view 走 Const id *)
Definition set `(l : Lens s t a b) (x : b) : s -> t :=
  runIdentityF \o l _ _ (fun _ => Id _ x).
Notation "l .~ x" := (set l x) (at level 40).

Definition over `(l : Lens s t a b) (f : a -> b) : s -> t :=
  runIdentityF \o l _ _ (fun x => Id _ (f x)).
Notation "l %~ f" := (over l f) (at level 40).

Definition view `(f : Getting a s a) : s -> a := f id.
Notation "x ^_ l" := (view l x) (at level 40).

(* Coerce Lens'/Getter down to Getting / 把 Lens'/Getter 降为 Getting *)
Definition stepdownl' `(l : Lens' s a) : Getting a s a := l _ _.
Coercion stepdownl' : Lens' >-> Getting.

Definition stepdowng `(l : Getter s a) : Getting a s a := l _ _ _.
Coercion stepdowng : Getter >-> Getting.

Notation "f \o+ g" := (fun x y => f x y \o g x y) (at level 41, only parsing).

(* Product lenses / 积的左右分量透镜 *)
Definition _1 {a b : Type} : Lens' (a * b) a :=
  fun _ _ f s => match s with (x, y) => fmap (fun z => (z, y)) (f x) end.
Definition _2 {a b : Type} : Lens' (a * b) b :=
  fun _ _ f s => match s with (x, y) => fmap (fun z => (x, z)) (f y) end.

(* Sigma projection as Getter / Σ 投影做成 Getter *)
Definition _ex1 {a : Type} {P : a -> Prop} : Getter { x : a | P x } a :=
  fun _ _ _ f s => fmap (const s) (f (proj1_sig s)).

Require Import Hask.Control.Monad.Trans.State.

(* StateT: view / mutate through a lens / 经透镜在 StateT 中读 / 改 *)
Definition use `(l : Getting a s a) `{Monad m} : StateT s m a :=
  view l <$> getT.

Definition plusStateT `(l : Lens' s nat) (n : nat) `{Monad m} :
  StateT s m unit := modifyT (l %~ plus n).

Notation "l += n" := (plusStateT l n) (at level 41).

Definition modifyStateT `(l : Lens' s a) (x : a) `{Monad m} :
  StateT s m unit := modifyT (l .~ x).

Notation "l .= x" := (modifyStateT l x) (at level 41).

Definition applyStateT `(l : Lens' s a) (f : a -> a) `{Monad m} :
  StateT s m unit := modifyT (l %~ f).

Notation "l %= f" := (applyStateT l f) (at level 41).

Module LensLaws.

(* Classic three lens laws / 经典三条透镜律 *)
Class LensLaws `(l : Lens' s a) := {
  lens_view_set : forall (x : s) (y : a), view l (set l y x) = y;
  lens_set_view : forall (x : s), set l (view l x) x = x;
  lens_set_set  : forall (x : s) (y z : a), set l z (set l y x) = set l z x
}.

#[export]
Program Instance Lens__1 {a b} : LensLaws (s:=a * b) _1.
#[export]
Program Instance Lens__2 {a b} : LensLaws (s:=a * b) _2.

Example lens_ex1 : view _1 (10, 20) = 10.
Proof. reflexivity. Qed.

Example lens_ex2 : view _2 (10, 20) = 20.
Proof. reflexivity. Qed.

Example lens_ex3 : (10, 20) ^_ _2 = 20.
Proof. reflexivity. Qed.

Example lens_ex4 : (1, (2, (3, 4))) ^_ stepdownl' (_2 \o+ _2 \o+ _2) = 4.
Proof. reflexivity. Qed.

Example lens_ex5 : ((10, 20) &+ _1 .~ 500) = (500, 20).
Proof. reflexivity. Qed.

Example lens_ex6 : ((10, 20) &+ _1 %~ plus 1) = (11, 20).
Proof. reflexivity. Qed.

End LensLaws.
