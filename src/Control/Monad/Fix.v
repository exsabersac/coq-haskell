Require Import Hask.Prelude.
Require Import Hask.Control.Monad.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*
MonadFix: value-recursion in a monad.
mfix : ((T -> m U) -> T -> m U) -> T -> m U
Differs from Haskell's (a -> m a) -> m a because Coq is call-by-value;
see "Axioms for Recursion in Call-by-Val"
(http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.27.2580&rep=rep1&type=pdf).
MonadFixLaws module only documents purity / left-shrinking / sliding / nesting
(no proved instances here).

--------
MonadFix：单子中的值递归。
mfix : ((T → m U) → T → m U) → T → m U
因 Coq 传值求值，类型不同于 Haskell 的 (a → m a) → m a；
见上文论文。MonadFixLaws 只记录 purity / left-shrinking / sliding / nesting
（此处无已证实例）。
*)

Class MonadFix (m : Type -> Type) : Type := {
  mfix : forall {T U}, ((T -> m U) -> T -> m U) -> T -> m U
}.

Module MonadFixLaws.

Include MonadLaws.

(**
MonadFix laws (documented; not proved here).
purity: mfix (return . h) = return (fix h) — no extra monadic action.
left shrinking: actions independent of the recursive var factor out of mfix.
sliding (h strict): mfix (liftM h . f) = liftM h (mfix (f . h)).
nesting: nested mfix merges — like pure fix.

--------
MonadFix 定律（仅文档，此处未证）。
purity：纯递归上的 mfix 不引入额外单子动作。
left shrinking：与递归变量无关的左侧动作可提出 mfix。
sliding（h 严格）：与 liftM 交换。
nesting：嵌套 mfix 可合并——类比纯 fix。
*)

End MonadFixLaws.
