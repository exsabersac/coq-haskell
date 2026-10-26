(*
Boolean equality typeclass (Haskell Eq): eqb / neqb with
reflexivity, symmetry, transitivity, and soundness (eqb true → =).
Laws live in the class itself (unlike FunctorLaws).

--------
布尔相等类型类（对应 Haskell Eq）：eqb / neqb，
含自反、对称、传递，以及健全性（eqb 为真 ⇒ 命题相等）。
定律写在类内（与 FunctorLaws 拆开的风格不同）。
*)

Generalizable All Variables.
Set Primitive Projections.

(* Class: decidable equality as bool. / 类：用 bool 表达可判定相等。 *)
Class Eq (A : Type) := {
  eqb  : A -> A -> bool;
  neqb : A -> A -> bool;

  eqb_refl x : eqb x x = true;
  eqb_sym x y : eqb x y = eqb y x;
  eqb_trans {x y z} : eqb x y = true -> eqb y z = true -> eqb x z = true;

  eqb_eq {x y} : eqb x y = true -> x = y;
}.

Infix "==" := eqb (at level 70).
Infix "/=" := neqb (at level 70).

(* Soundness of false: unequal. / false 的健全性：不相等。 *)
Lemma eqb_neq `{Eq A} {x y} : eqb x y = false -> x <> y.
Proof.
  repeat intro; subst.
  pose proof (eqb_refl y).
  rewrite H0 in H1.
  inversion H1.
Qed.
