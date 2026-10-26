(*
  EN: Thin re-export of ssreflect / ssrfun / ssrbool, plus tiny helpers
  (decide, prop). This is the library's SSR entrypoint — tactic style,
  not the full MathComp stack.
  --------
  中文：统一导出 ssreflect / ssrfun / ssrbool，并附带小工具（decide、prop）。
  本仓 SSR 入口：主要用战术风格，不是整套 MathComp。
  说明见 docs/SSR.zh-CN.md。
*)

From Coq Require Export
  ssreflect
  ssrfun
  ssrbool.

Lemma and_swap : forall x y z, [&& x, y & z] = [&& y, x & z].
Proof. by case; case; case. Qed.

Definition decide {T : Type} (H : bool)
  (kt : (H = true)  -> T)
  (kf : (H = false) -> T) : T :=
  (fun (if_true  : (fun b : bool => protect_term (H = b) -> T) true)
       (if_false : (fun b : bool => protect_term (H = b) -> T) false) =>
    if H as b return ((fun b0 : bool => protect_term (H = b0) -> T) b)
    then if_true
    else if_false)
  (fun (E : H = true)  => kt E)
  (fun (E : H = false) => kf E)
  (erefl H).

Arguments decide {T} H kt kf.

Definition prop (b : bool) : option (is_true b) :=
  if b then Some is_true_true else None.
