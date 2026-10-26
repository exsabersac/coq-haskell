(*
Maybe as a thin alias of Coq option (Just/Nothing = Some/None),
with Functor / Applicative / Monad / Alternative instances —
a worked example of how data types plug into the Hask typeclass tower.
join is the primitive for Monad (flatten nested option).

--------
Maybe 是 Coq option 的薄别名（Just/Nothing = Some/None），
并给出 Functor / Applicative / Monad / Alternative 实例——
数据型如何挂上 Hask 类型类塔的样板。
Monad 仍以 join 为原语（压平嵌套 option）。
*)

Require Import Hask.Control.Monad.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

(* Haskell names for option. / 用 Haskell 名指称 option。 *)
Notation Maybe   := option.
Notation Nothing := None.
Notation Just    := Some.

Definition fromMaybe `(x : a) (my : Maybe a) : a :=
  match my with
  | Just z  => z
  | Nothing => x
  end.

Definition maybe `(x : b) `(f : a -> b) (my : Maybe a) : b :=
  match my with
  | Just z  => f z
  | Nothing => x
  end.

Definition Maybe_map `(f : X -> Y) (x : Maybe X) : Maybe Y :=
  match x with
  | Nothing => Nothing
  | Just x' => Just (f x')
  end.

#[export]
(* fmap = Maybe_map / 函子实例 *)
Instance Maybe_Functor : Functor Maybe := {
  fmap := @Maybe_map
}.

Definition Maybe_apply {X Y} (f : Maybe (X -> Y)) (x : Maybe X) : Maybe Y :=
  match f with
  | Nothing => Nothing
  | Just f' => match x with
    | Nothing => Nothing
    | Just x' => Just (f' x')
    end
  end.

#[export]
(* pure = Just ; ap = Maybe_apply / 应用子实例 *)
Instance Maybe_Applicative : Applicative Maybe := {
  is_functor := Maybe_Functor;

  pure := @Just;
  ap := @Maybe_apply
}.

Definition Maybe_join {X} (x : Maybe (Maybe X)) : Maybe X :=
  match x with
  | Nothing => Nothing
  | Just Nothing => Nothing
  | Just (Just x') => Just x'
  end.

#[export]
(* join = Maybe_join (flatten) / 单子实例：join 压平 *)
Instance Maybe_Monad : Monad Maybe := {
  is_applicative := Maybe_Applicative;
  join := @Maybe_join
}.

Definition isJust {a} (x : Maybe a) := if x then true else false.

Definition Maybe_choose {a} (x y : Maybe a) : Maybe a :=
  match x with
  | Nothing => y
  | Just _  => x
  end.

#[export]
(* empty = Nothing ; choose prefers left Just / 选择：偏左 Just *)
Instance Maybe_Alternative : Alternative Maybe := {
  empty  := @Nothing;
  choose := @Maybe_choose
}.

Lemma Maybe_choose_spec : forall a (x y : Maybe a),
  isJust (x <|> y) = (isJust x || isJust y)%bool.
Proof.
  intros a x y.
  destruct x; auto.
Qed.

Lemma fmap_endo_just {c} (f : c -> c) (m : Maybe c) (x : c) :
  f <$> m = Just x <-> exists y, x = f y /\ m = Just y.
Proof.
  induction m; simpl; split; intros.
  - inversion_clear H.
    eexists; eauto.
  - destruct H, H; subst.
    now inversion_clear H0.
  - discriminate.
  - destruct H, H; discriminate.
Qed.

Lemma fmap_endo_nothing {c} (f : c -> c) (m : Maybe c) :
  f <$> m = Nothing <-> m = Nothing.
Proof. induction m; simpl; intuition auto; discriminate. Qed.

Lemma ap_endo_just {c} (f : c -> c -> c) (m n : Maybe c) (x : c) :
  f <$> m <*> n = Just x
    <-> exists y z, x = f y z /\ m = Just y /\ n = Just z.
Proof.
  induction m, n; simpl; split; intros.
  - inversion_clear H.
    eexists; eauto.
  - destruct H, H, H, H0; subst.
    inversion_clear H0.
    now inversion_clear H1.
  - discriminate.
  - destruct H, H, H, H0; discriminate.
  - discriminate.
  - destruct H, H, H, H0; discriminate.
  - discriminate.
  - destruct H, H, H, H0; discriminate.
Qed.

Lemma ap_endo_nothing {c} (f : c -> c -> c) (m n : Maybe c) :
  f <$> m <*> n = Nothing <-> m = Nothing \/ n = Nothing.
Proof. induction m, n; simpl; intuition auto; discriminate. Qed.

Lemma bind_endo_just {c} (f : c -> Maybe c) (m : Maybe c) (x : c) :
  m >>= f = Just x <-> exists y, f y = Just x /\ m = Just y.
Proof.
  induction m; simpl; split; intros.
  - destruct (f a) eqn:?.
      inversion H; subst.
      now eexists; eauto.
    discriminate.
  - destruct H, H.
    inversion H0; subst.
    now rewrite H.
  - discriminate.
  - destruct H, H.
    discriminate.
Qed.

Lemma bind_endo_nothing {c} (f : c -> Maybe c) (m : Maybe c) :
  m >>= f = Nothing <-> m = Nothing \/ exists y, f y = Nothing /\ m = Just y.
Proof.
  induction m; simpl; split; intros.
  - destruct (f a) eqn:?.
      now inversion H; subst.
    right.
    now eexists; eauto.
  - destruct H.
      discriminate.
    firstorder eauto.
    inversion_clear H0.
    now rewrite H.
  - now left.
  - reflexivity.
Qed.

Lemma alt_endo_just {c} (m n : Maybe c) (x : c) :
  m <|> n = Just x <-> m = Just x \/ (m = Nothing /\ n = Just x).
Proof. induction m; simpl; intuition auto; discriminate. Qed.

Lemma alt_endo_nothing {c} (m n : Maybe c) :
  m <|> n = Nothing <-> m = Nothing /\ n = Nothing.
Proof. induction m, n; simpl; intuition auto; discriminate. Qed.
