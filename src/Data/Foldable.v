(*
Foldable: right fold over a type constructor t.
An axiom of foldr parametricity yields fmap-fusion:
foldr f z (fmap g xs) = foldr (f \o g) z xs.

--------
Foldable：在类型构造子 t 上的右折叠。
foldr 参数性公理推出 fmap 融合：
foldr f z (fmap g xs) = foldr (f \o g) z xs。
*)

Require Import Hask.Ltac.
Require Import Hask.Data.Functor.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

(* Class: foldr only. / 类：仅 foldr。 *)
Class Foldable (t : Type -> Type) := {
  foldr : forall a b, (a -> b -> b) -> b -> t a -> b
}.

Arguments foldr {t _ a b} _ _ _.

(*
Parametricity of foldr w.r.t. fmap (free theorem style).
--------
foldr 相对 fmap 的参数性（自由定理风格）。
*)
Axiom foldr_parametricity :
  forall `{Foldable t} `{Functor t}
         A B (f : A -> B -> B) (u : B)
         A' B' (g : A' -> B' -> B') (u' : B')
         (a : A -> A') (b : B -> B'),
    b u = u'
      -> (forall x y, b (f x y) = g (a x) (b y))
      -> b \o @foldr t _ A B f u = @foldr t _ A' B' g u' \o fmap a.

Import FunctorLaws.

(* Fusion: push fmap into the combining function. / 融合：把 fmap 推进合并函数。 *)
Theorem foldr_fmap_fusion `{Foldable t} `{FunctorLaws t} :
  forall A B (f : A -> B -> B) C (g : C -> A) (z : B) (xs : t C),
    foldr f z (fmap g xs) = foldr (f \o g) z xs.
Proof.
  intros.
  pose proof (foldr_parametricity C B (f \o g) z A B f z g id
                                  eq_refl (fun _ _ => eq_refl)).
  replace (foldr f z (fmap[ t] g xs))
     with ((foldr f z \o fmap[ t] g) xs) by trivial.
  rewrite <- H2.
  reflexivity.
Qed.
