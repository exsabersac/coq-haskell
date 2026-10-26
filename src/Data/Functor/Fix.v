(*
Church / final encoding of the fixed point of an endofunctor f:
Fix f ≅ ∀ r. (∀ x. (x → r) → f x → r) → r
(the catamorphism / fold algebra form).

--------
自函子 f 不动点的 Church / 终编码：
Fix f ≅ ∀ r. (∀ x. (x → r) → f x → r) → r
（catamorphism / 折叠代数形式）。
*)

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

(* Final encoding of μ f. / μ f 的终编码。 *)
Definition Fix (f : Type -> Type) :=
  forall r, (forall x, (x -> r) -> f x -> r) -> r.
