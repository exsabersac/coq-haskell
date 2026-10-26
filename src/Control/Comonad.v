(*
Comonad: dual of Monad — extract : w a -> a and duplicate : w a -> w (w a).
extend f := fmap f \o duplicate (Haskell =>>). ComonadLaws is sketched but
commented out; only the class + extend are active.

--------
Comonad：Monad 的对偶 — extract : w a → a，duplicate : w a → w (w a)。
extend f := fmap f \o duplicate（Haskell 的 =>>）。ComonadLaws 有草图但整段注释；
当前生效的只有类与 extend。
*)

Require Import Hask.Prelude.
Require Import Hask.Data.List.
Require Import Hask.Control.Applicative.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

(* extract = counit; duplicate = comultiplication / extract：余单位；duplicate：余乘法 *)
Class Comonad (w : Type -> Type) := {
  is_functor :> Functor w;

  extract : forall {a : Type}, w a -> a;
  duplicate : forall {a : Type}, w a -> w (w a)
}.

Arguments extract {w _ _} _.
Arguments duplicate {w _ _} _.

(* extend = co-Kleisli / cobind / extend：余 Kleisli（cobind） *)
Definition extend `{Comonad w} {X Y : Type} (f : (w X -> Y)) : w X -> w Y :=
  fmap f \o duplicate.

Notation "m =>> f" := (extend f m) (at level 25, left associativity).

Module ComonadLaws.

Include ApplicativeLaws.

(*
Intended laws (commented): coassociativity of duplicate, counit left/right,
and naturality of duplicate. Left inactive — treat as documentation only.

--------
拟定律（已注释）：duplicate 的余结合、左右余单位、以及 duplicate 的自然性。
未启用 — 仅作文档参考。
*)
(* Class ComonadLaws (w : Type -> Type) `{Comonad w} := { *)
(*   has_applicative_laws :> ApplicativeLaws w; *)

(*   duplicate_fmap_duplicate : forall a : Type, *)
(*     duplicate \o fmap (@duplicate w _ a) =1 duplicate \o duplicate; *)
(*   duplicate_fmap_extract : forall a : Type, *)
(*     duplicate \o fmap (extract (a:=a)) =1 id; *)
(*   duplicate_extract      : forall a : Type, duplicate \o extract =1 @id (w a); *)
(*   duplicate_fmap_fmap : forall (a b : Type) (f : a -> b), *)
(*     duplicate \o fmap (fmap f) =1 fmap f \o duplicate *)
(* }. *)

(* Corollary duplicate_fmap_duplicate_x `{ComonadLaws w} : forall a x, *)
(*   duplicate (fmap (duplicate (a:=a)) x) = duplicate (duplicate x). *)
(* Proof. exact: duplicate_fmap_duplicate. Qed. *)

(* Corollary duplicate_fmap_extract_x `{ComonadLaws w} : forall a x, *)
(*   duplicate (fmap (extract (a:=a)) x) = x. *)
(* Proof. exact: duplicate_fmap_extract. Qed. *)

(* Corollary duplicate_extract_x `{ComonadLaws w} : forall a x, *)
(*   duplicate (extract x) = @id (w a) x. *)
(* Proof. exact: duplicate_extract. Qed. *)

(* Corollary duplicate_fmap_fmap_x `{ComonadLaws w} : *)
(*   forall (a b : Type) (f : a -> b) x, *)
(*   duplicate (fmap (fmap f) x) = fmap f (duplicate x). *)
(* Proof. exact: duplicate_fmap_fmap. Qed. *)

End ComonadLaws.
