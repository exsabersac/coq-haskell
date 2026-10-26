(*
Either as a thin alias of Coq sum (Left/Right = inl/inr),
with Functor / Applicative / Monad on the Right-biased Either E.
Left carries the fixed error (or left) type E; join flattens nested Right.

--------
Either 是 Coq sum 的薄别名（Left/Right = inl/inr），
在右偏的 Either E 上给出 Functor / Applicative / Monad。
Left 承载固定的错误（左）类型 E；join 压平嵌套的 Right。
*)

Require Import Hask.Control.Monad.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

(* Haskell names for sum. / 用 Haskell 名指称 sum。 *)
Notation Either := sum (only parsing).
Notation Left   := inl (only parsing).
Notation Right  := inr (only parsing).

(* Predicates on the tag. / 按构造子判别。 *)
Definition isLeft  `(x : a + b) : bool := if x then true else false.
Definition isRight `(x : a + b) : bool := if x then false else true.

(* Case analysis: fold both sides. / 双侧消去（类似 either）。 *)
Definition either `(f : a -> c) `(g : b -> c) (x : a + b) : c :=
  match x with
  | inl a => f a
  | inr b => g b
  end.

(* Map only the Left payload. / 只映射 Left。 *)
Definition mapLeft `(f : a -> c) `(x : a + b) : c + b :=
  match x with
  | inl l => inl (f l)
  | inr r => inr r
  end.

(* fmap on Right; Left untouched. / 函子作用在 Right。 *)
Definition Either_map {E X Y} (f : X -> Y) (x : Either E X) : Either E Y :=
  match x with
  | Left e   => Left e
  | Right x' => Right (f x')
  end.

(* Applicative: Left short-circuits. / 应用子：遇 Left 短路。 *)
Definition Either_apply {E X Y} (f : Either E (X -> Y)) (x : Either E X)
  : Either E Y :=
  match f with
  | Left e   => Left e
  | Right f' => match x with
    | Left e   => Left e
    | Right x' => Right (f' x')
    end
  end.

(* Monad join: flatten Either E (Either E X). / join：压平嵌套 Either。 *)
Definition Either_join {E X} (x : Either E (Either E X)) : Either E X :=
  match x with
  | Left e           => Left e
  | Right (Left e)   => Left e
  | Right (Right x') => Right x'
  end.

#[export]
(* fmap = Either_map / 函子实例 *)
Instance Either_Functor {E} : Functor (Either E) :=
{ fmap := @Either_map E
}.
(* jww (2015-06-17): NYI
Proof.
  - (* fun_identity *)
    intros. extensionality x. compute. destruct x; reflexivity.
  - (* fun_composition *)
    intros. extensionality x. compute. destruct x; reflexivity.
Defined.
*)

#[export]
(* pure = Right ; ap = Either_apply / 应用子实例 *)
Instance Either_Applicative {E} : Applicative (Either E) :=
{ is_functor := Either_Functor
; pure := @Right E
; ap := @Either_apply E
}.
(* jww (2015-06-17): NYI
Proof.
  - (* app_identity *)
    intros. extensionality x. compute. destruct x; reflexivity.
  - (* app_composition *)
    intros. compute.
    destruct u.
      destruct v; reflexivity.
      destruct v. reflexivity. destruct w; reflexivity.
  - (* app_homomorphism *)
    intros. compute. reflexivity.
  - (* app_interchange *)
    intros. compute. destruct u; reflexivity.
  - (* app_fmap_unit *)
    intros. extensionality x. compute. destruct x; reflexivity.
Defined.
*)

#[export]
(* join = Either_join / 单子实例（join 原语） *)
Instance Either_Monad {E} : Monad (Either E) :=
{ is_applicative := Either_Applicative
; join := @Either_join E
}.
(* jww (2015-06-17): NYI
Proof.
  - (* monad_law_1 *)
    intros. extensionality x. compute.
    destruct x.
      reflexivity.
      destruct e.
        reflexivity.
        destruct e; reflexivity.
  - (* monad_law_2 *)
    intros. extensionality x. compute.
    destruct x; reflexivity.
  - (* monad_law_3 *)
    intros. extensionality x. compute.
    destruct x; reflexivity.
  - (* monad_law_4 *)
    intros. extensionality x. compute.
    destruct x.
      reflexivity.
      destruct e; reflexivity.
Defined.
*)
