(*
Left / Right Kan extensions along functors f, g (on Type → Type):
  Lan f g a  ≅ ∃ e. (f e → a) × g e     (existential / initial)
  Ran f g a  ≅ ∀ r. (a → f r) → g r     (universal / final)
Lan_final is the final encoding of Lan; parametricity axioms support rewriting.

--------
沿函子 f、g 的左/右 Kan 扩张（在 Type → Type 上）：
  Lan f g a  ≅ ∃ e. (f e → a) × g e     （存在 / 始）
  Ran f g a  ≅ ∀ r. (a → f r) → g r     （全称 / 终）
Lan_final 是 Lan 的终编码；参数性公理用于改写。
*)

Require Import Hask.Ltac.
Require Import Hask.Data.Functor.
Require Import Hask.Data.Functor.Contravariant.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

(* Left and Right Kan extensions / 左、右 Kan 扩张 *)

(* Existential (coend-style) Lan. / 存在式（余端风格）Lan。 *)
Definition Lan (f g : Type -> Type) (a : Type) :=
  { e : Type & ((f e -> a) * g e)%type }.

(* Final encoding of the same data. / 同一数据的终编码。 *)
Definition Lan_final (f g : Type -> Type) (a : Type) :=
  forall r, (forall x : Type, (f x -> a) -> g x -> r) -> r.

Axiom Lan_final_parametricity :
  forall a b c f g
         (k : Lan_final f g a)
         (h : forall x : Type, (f x -> a) -> g x -> b)
         (x : b -> c),
    x (k b h) = k c (fun e n z => x (h e n z)).

(* Universal (end-style) Ran. / 全称式（端风格）Ran。 *)
Definition Ran (f g : Type -> Type) (a : Type) :=
  forall r, (a -> f r) -> g r.

Axiom Ran_parametricity :
  forall a b c `{Functor f} `{Functor g}
         (k : Ran f g a) (g : b -> c) (h : a -> f b),
    fmap g (k _ h) = k _ (fmap g \o h).
