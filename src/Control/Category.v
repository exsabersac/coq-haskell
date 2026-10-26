Set Warnings "-notation-overridden".

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Set Transparent Obligations.

(* Copyright (c) 2014, John Wiegley
 *
 * This work is licensed under a
 * Creative Commons Attribution-Noncommercial-No Derivative Works 3.0
 * Unported License.
 * The license text is available at:
 *   http://creativecommons.org/licenses/by-nc-nd/3.0/
 *)

(*
Tutorial-style Category on Type: objects, hom (~>), id, compose with laws.
Defines sections/retractions, epic/monic, Isomorphism, Groupoid, Sets,
and Opposite (C^op). Pedagogical CT sketch — day-to-day F/A/M instances
do NOT hang on this Category. Uses axioms propositional_extensionality
and proof_irrelevance.

--------
教程风 Category（对象在 Type）：对象、hom（~>）、id、复合及定律。
含 section/retraction、epic/monic、Isomorphism、Groupoid、Sets、
以及对偶范畴 C^op。偏教学的 CT 草图 — 日常 F/A/M 实例不挂在此 Category 上。
使用公理 propositional_extensionality 与 proof_irrelevance。
*)

(** %\chapter{Category}% *)

Require Import Hask.Prelude.
Require Import Hask.Crush.
Require Import Coq.Unicode.Utf8.
Require Import FunctionalExtensionality.

Axiom propositional_extensionality : forall P : Prop, P -> P = True.
Axiom proof_irrelevance : forall (P : Prop) (u v : P), u = v.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
(* Unset Transparent Obligations. *)

(*
* Category — "the algebra of abstract functions" (Awodey): objects + morphisms.

--------
* 范畴 — 「抽象函数的代数」（Awodey）：对象 + 态射。
*)

(* begin hide *)
Reserved Notation "a ~> b" (at level 70, right associativity).
Reserved Notation "f ∘ g" (at level 40, left associativity).
Reserved Notation "C ^op" (at level 90).
(* end hide *)

Class Category := {
    ob   : Type;
    (* These require Coq 8.5 and universe polymorphism. *)
    (* uhom := Type : Type; *)
    (* hom  : ob → ob → uhom where "a ~> b" := (hom a b); *)
    hom  : ob → ob → Type where "a ~> b" := (hom a b);
(*
Objects/arrows carry no inherent meaning — they only distinguish morphisms;
morphisms characterize objects. [hom] = Hom-set; [uhom] (commented) for
universe polymorphism when categories are objects.

--------
对象/箭头本身无固有含义 — 仅区分态射；态射刻画对象。
[hom] 即 Hom-集；[uhom]（已注释）用于范畴作对象时的宇宙多态。
*)

(* * Morphisms / * 态射 *)

    c_id : ∀ {A}, A ~> A;
    c_comp : ∀ {A B C}, (B ~> C) → (A ~> B) → (A ~> C)
      where "f ∘ g" := (c_comp f g);
(*
[id] / [compose] are the verbs; three laws: left/right identity, associativity.

--------
[id] / [compose] 是动词；三定律：左/右单位、结合律。
*)

    c_right_id : ∀ A B (f : A ~> B), f ∘ c_id = f;
    c_left_id : ∀ A B (f : A ~> B), c_id ∘ f = f;
    c_comp_assoc : ∀ A B C D (f : C ~> D) (g : B ~> C) (h : A ~> B),
        f ∘ (g ∘ h) = (f ∘ g) ∘ h
}.

(* Coq function arrow A → B vs categorical A ~> B (or A ~{C}~> B)
   --------
   Coq 函数箭头 A → B 与范畴态射 A ~> B（或 A ~{C}~> B） *)

(* begin hide *)
(* Using a [Category] in a context requiring a [Type] will do what is expected
   using this coercion. *)
Coercion ob : Category >-> Sortclass.
(* Coercion hom : Category >-> Funclass. *)

Declare Scope category_scope.

Infix "~>"       := hom : category_scope.
Infix "~{ C }~>" := (@hom C) (at level 100) : category_scope.
Infix "∘"        := c_comp (at level 40, left associativity) : category_scope.

Notation "ob/ C" := (@ob C) (at level 1) : category_scope.
Notation "id/ X" := (@c_id _ X) (at level 1) : category_scope.

Open Scope category_scope.

Lemma cat_irrelevance `(C : Category) `(D : Category)
  : ∀ (m n : ∀ {A}, A ~> A)
      (p q : ∀ {A B C}, (B ~> C) → (A ~> B) → (A ~> C))
      l l' r r' c c',
  @m = @n →
  @p = @q →
  {| ob           := C
   ; hom          := @hom C
   ; c_id         := @m
   ; c_comp       := @p
   ; c_left_id    := l
   ; c_right_id   := r
   ; c_comp_assoc := c
 |} =
  {| ob           := C
   ; hom          := @hom C
   ; c_id         := @n
   ; c_comp       := @q
   ; c_left_id    := l'
   ; c_right_id   := r'
   ; c_comp_assoc := c'
 |}.
Proof.
  intros. subst. f_equal.
  apply proof_irrelevance.
  apply proof_irrelevance.
  apply proof_irrelevance.
Qed.

#[export] Hint Extern 1 => apply c_left_id : core.
#[export] Hint Extern 1 => apply c_right_id : core.

#[export] Hint Extern 4 (?A = ?A) => reflexivity : core.
#[export] Hint Extern 7 (?X = ?Z) =>
  match goal with
    [H : ?X = ?Y, H' : ?Y = ?Z |- ?X = ?Z] => transitivity Y
  end : core.

(* end hide *)

(* Morphisms derived from id/compose / 由 id/compose 导出的态射性质 *)

(* begin hide *)
Section Morphisms.
Context `{C : Category}.
(* end hide *)

Definition Idempotent `(f : X ~> X) := f ∘ f = f.
Definition Involutive `(f : X ~> X) := f ∘ f = c_id.

(* Section' / Retraction / SplitIdempotent / Section'、Retraction、分裂幂等 *)

Definition Section'   `(f : X ~> Y) := { g : Y ~> X & g ∘ f = c_id }.
Definition Retraction `(f : X ~> Y) := { g : Y ~> X & f ∘ g = c_id }.

Class SplitIdempotent {X Y : C} := {
    split_idem_retract := Y;

    split_idem       : X ~> X;
    split_idem_r     : X ~> split_idem_retract;
    split_idem_s     : split_idem_retract ~> X;
    split_idem_law_1 : split_idem_s ∘ split_idem_r = split_idem;
    split_idem_law_2 : split_idem_r ∘ split_idem_s = id/Y
}.

(* Σ-type keeps the witness g (∃ would hide it)
   --------
   用 Σ 保留见证 g（∃ 会藏掉） *)

Definition Epic  `(f : X ~> Y) := ∀ Z (g1 g2 : Y ~> Z), g1 ∘ f = g2 ∘ f → g1 = g2.
Definition Monic `(f : X ~> Y) := ∀ Z (g1 g2 : Z ~> X), f ∘ g1 = f ∘ g2 → g1 = g2.

Definition Bimorphic `(f : X ~> Y) := Epic f ∧ Monic f.
Definition SplitEpi  `(f : X ~> Y) := Retraction f.
Definition SplitMono `(f : X ~> Y) := Section' f.

(* id is Idempotent and Involutive / id 既幂等又对合 *)

(* begin hide *)
Hint Unfold Idempotent : core.
Hint Unfold Involutive : core.
Hint Unfold Section' : core.
Hint Unfold Retraction : core.
Hint Unfold Epic : core.
Hint Unfold Monic : core.
Hint Unfold Bimorphic : core.
Hint Unfold SplitEpi : core.
Hint Unfold SplitMono : core.
(* end hide *)

Lemma id_idempotent : ∀ X, Idempotent (c_id (A := X)).
Proof. auto. Qed.

Lemma id_involutive : ∀ X, Involutive (c_id (A := X)).
Proof. auto. Qed.

(* Retraction ⇒ Epic; Section' ⇒ Monic / 收缩⇒满；截影⇒单 *)

(* begin hide *)
Section Lemmas.
Variables X Y : C.
Variable f : X ~> Y.
(* end hide *)

Lemma retractions_are_epic : Retraction f → Epic f.
Proof.
  autounfold.
  intros.
  destruct X0.
  rewrite <- c_right_id.
  symmetry.
  rewrite <- c_right_id.
  rewrite <- e.
  repeat (rewrite c_comp_assoc); try f_equal; auto.
Qed.

Lemma sections_are_monic : Section' f → Monic f.
Proof.
  autounfold.
  intros.
  destruct X0.
  rewrite <- c_left_id.
  symmetry.
  rewrite <- c_left_id.
  rewrite <- e.
  repeat (rewrite <- c_comp_assoc); try f_equal; auto.
Qed.

(* begin hide *)
End Lemmas.
End Morphisms.
(* end hide *)

Definition epi_compose `{C : Category} {X Y Z : C}
  `(ef : @Epic C Y Z f) `(eg : @Epic C X Y g) : Epic (f ∘ g).
Proof.
  unfold Epic in *. intros.
  apply ef.
  apply eg.
  repeat (rewrite <- c_comp_assoc); auto.
Qed.

Definition monic_compose `{C : Category} {X Y Z : C}
  `(ef : @Monic C Y Z f) `(eg : @Monic C X Y g) : Monic (f ∘ g).
Proof.
  unfold Monic in *. intros.
  apply eg.
  apply ef.
  repeat (rewrite c_comp_assoc); auto.
Qed.

(*
* Isomorphism — to / from with to∘from = id and from∘to = id

--------
* 同构 — to / from，双向复合为 id
*)

Class Isomorphism `{C : Category} (X Y : C) := {
  to       : X ~> Y;
  from     : Y ~> X;
  iso_to   : to ∘ from = id/Y;
  iso_from : from ∘ to = id/X
}.

(* begin hide *)
Lemma iso_irrelevance `(C : Category) {X Y : C}
  : ∀ (f g : X ~> Y) (k h : Y ~> X) tl tl' fl fl',
  @f = @g →
  @k = @h →
  {| to       := f
   ; from     := k
   ; iso_to   := tl
   ; iso_from := fl
  |} =
  {| to       := g
   ; from     := h
   ; iso_to   := tl'
   ; iso_from := fl'
  |}.
Proof.
  intros. subst. f_equal.
  apply proof_irrelevance.
  apply proof_irrelevance.
Qed.
(* end hide *)

(* Object iso X {≅} Y; value-level x {≡} y
   --------
   对象同构 X {≅} Y；值级 x {≡} y *)

Notation "X {≅} Y" :=
  (Isomorphism X Y) (at level 70, right associativity) : category_scope.
Notation "x {≡} y" :=
  (to x = y ∧ from y = x) (at level 70, right associativity).

(* Iso: identity, symmetry, transitivity (parametric relation)
   --------
   同构：恒等、对称、传递（参数关系，可改写） *)

Program Definition iso_identity `{C : Category} (X : C) : X {≅} X := {|
    to   := id/X;
    from := id/X
|}.

Program Definition iso_symmetry `{C : Category} `(iso : X {≅} Y) : Y {≅} X := {|
    to   := @from C X Y iso;
    from := @to C X Y iso
|}.
(* begin hide *)
Obligation 1. apply iso_from. Qed.
Obligation 2. apply iso_to. Qed.
(* end hide *)

Program Definition iso_compose `{C : Category} {X Y Z : C}
    (iso_a : Y {≅} Z) (iso_b : X {≅} Y) : X {≅} Z := {|
    to   := (@to C Y Z iso_a) ∘ (@to C X Y iso_b);
    from := (@from C X Y iso_b) ∘ (@from C Y Z iso_a)
|}.
(* begin hide *)
Obligation 1.
  destruct iso_a.
  destruct iso_b. simpl.
  rewrite <- c_comp_assoc.
  rewrite (c_comp_assoc _ _ _ _ to1).
  rewrite iso_to1.
  rewrite c_left_id.
  assumption.
Qed.
Obligation 2.
  destruct iso_a.
  destruct iso_b. simpl.
  rewrite <- c_comp_assoc.
  rewrite (c_comp_assoc _ _ _ _ from0).
  rewrite iso_from0.
  rewrite c_left_id.
  assumption.
Qed.
(* end hide *)

(*
Definition iso_equiv `{C : Category} {a b : C} (x y : a ≅ b) : Prop :=
  match x with
  | Build_Isomorphism to0 from0 _ _ => match y with
    | Build_Isomorphism to1 from1 _ _ =>
      to0 = to1 ∧ from0 = from1
    end
  end.

Program Definition iso_equivalence `{C : Category} (a b : C)
  : Equivalence (@iso_equiv C a b).
Obligation 1.
  unfold Reflexive, iso_equiv. intros.
  destruct x. auto.
Defined.
Obligation 2.
  unfold Symmetric, iso_equiv. intros.
  destruct x. destruct y.
  inversion H.
  split; symmetry; assumption.
Defined.
Obligation 3.
  unfold Transitive, iso_equiv. intros.
  destruct x. destruct y. destruct z.
  inversion H. inversion H0.
  split. transitivity to1; auto.
  transitivity from1; auto.
Defined.

Add Parametric Relation `(C : Category) (a b : C) : (a ≅ b) (@iso_equiv C a b)
  reflexivity proved by  (@Equivalence_Reflexive  _ _ (iso_equivalence a b))
  symmetry proved by     (@Equivalence_Symmetric  _ _ (iso_equivalence a b))
  transitivity proved by (@Equivalence_Transitive _ _ (iso_equivalence a b))
    as parametric_relation_iso_eqv.

  Add Parametric Morphism `(C : Category) (a b c : C) : (@iso_compose C a b c)
    with signature (iso_equiv ==> iso_equiv ==> iso_equiv)
      as parametric_morphism_iso_comp.
    intros. unfold iso_equiv, iso_compose.
    destruct x. destruct y. destruct x0. destruct y0.
    simpl in *.
    inversion H. inversion H0.
    split; crush.
Defined.
*)

(* Groupoid: every morphism is an iso / Groupoid：每个态射皆同构 *)

Program Definition Groupoid `(C : Category) : Category := {|
    ob      := @ob C;
    hom     := @Isomorphism C;
    c_id    := @iso_identity C
|}.
(* begin hide *)
Next Obligation.
  unfold iso_compose, iso_identity.
  eapply iso_compose; eauto.
Defined.
Next Obligation.
  unfold Groupoid_obligation_1.
  unfold iso_compose, iso_identity.
  destruct f. simpl in *.
  apply iso_irrelevance.
  apply c_right_id.
  apply c_left_id.
Qed.
Next Obligation.
  unfold Groupoid_obligation_1.
  unfold iso_compose, iso_identity.
  destruct f. simpl in *.
  apply iso_irrelevance.
  apply c_left_id.
  apply c_right_id.
Qed.
Next Obligation.
  unfold Groupoid_obligation_1.
  unfold iso_compose.
  destruct f. destruct g. destruct h.
  simpl; apply iso_irrelevance;
  rewrite c_comp_assoc; reflexivity.
Qed.
(* end hide *)

(* Monic+Retraction or Epic+Section' ⇒ Isomorphism
   --------
   单+收缩 或 满+截影 ⇒ 同构 *)

Program Definition Monic_Retraction_Iso `{C : Category}
  `(f : X ~{C}~> Y) (r : Retraction f) (m : Monic f) : X {≅} Y := {|
  to   := f;
  from := projT1 r
|}.
(* begin hide *)
Obligation 1.
  autounfold in *.
  destruct r.
  auto.
Qed.
Obligation 2.
  autounfold in *.
  destruct r.
  simpl.
  specialize (m X (x ∘ f) c_id).
  apply m.
  rewrite c_comp_assoc.
  rewrite e.
  auto.
  rewrite c_left_id.
  rewrite c_right_id.
  reflexivity.
Qed.
(* end hide *)

Program Definition Epic_Section_Iso
    `{C : Category} {X Y} `(s : Section' f) `(e : Epic f) : X {≅} Y := {|
    to   := f;
    from := projT1 s
|}.
(* begin hide *)
Obligation 1.
  autounfold in *.
  destruct s.
  simpl.
  specialize (e Y (f ∘ x) c_id).
  apply e.
  rewrite <- c_comp_assoc.
  rewrite e0.
  rewrite c_left_id.
  rewrite c_right_id.
  reflexivity.
Qed.
Obligation 2.
  autounfold in *.
  destruct s.
  specialize (e Y (f ∘ x) c_id).
  auto.
Qed.

#[export] Hint Unfold Idempotent : core.
#[export] Hint Unfold Involutive : core.
#[export] Hint Unfold Section' : core.
#[export] Hint Unfold Retraction : core.
#[export] Hint Unfold Epic : core.
#[export] Hint Unfold Monic : core.
#[export] Hint Unfold Bimorphic : core.
#[export] Hint Unfold SplitEpi : core.
#[export] Hint Unfold SplitMono : core.
(* end hide *)

(* flip Section' ↔ Retraction / 截影与收缩互翻 *)

Definition flip_section `{Category} `(f : X ~> Y)
  (s : @Section' _ X Y f) : @Retraction _ Y X (projT1 s).
Proof.
  autounfold.
  destruct s.
  exists f.
  crush.
Qed.

Definition flip_retraction `{Category} `(f : X ~> Y)
  (s : @Retraction _ X Y f) : @Section' _ Y X (projT1 s).
Proof.
  autounfold.
  destruct s.
  exists f.
  crush.
Qed.

(*
* Sets — objects = Type; morphisms = functions. Named Sets (not Set) to avoid clash.

--------
* Sets（集合范畴）— 对象 = Type；态射 = 函数。称 Sets（非 Set）以免与 Coq 冲突。
*)

Program Definition Sets : Category := {|
    ob     := Type;
    hom    := fun X Y => X → Y;
    c_id   := fun _ x => x;
    c_comp := fun _ _ _ f g x => f (g x)
|}.
(* In Sets: Monic ↔ Injective, Epic ↔ Surjective
   --------
   在 Sets 中：单 ↔ 单射，满 ↔ 满射（他范畴未必） *)

Notation "X ≅Sets Y" :=
  (@Isomorphism Sets X Y) (at level 70, right associativity) : category_scope.

Definition Injective `(f : X → Y) := ∀ x y, f x = f y → x = y.

Lemma injectivity_is_monic `(f : X → Y) : Injective f ↔ @Monic Sets _ _ f.
Proof.
  unfold Monic, Injective.
  split; intros; simpl in *.
  - extensionality z.
    apply H. apply (equal_f H0).
  - pose (fun (_ : unit) => x) as const_x.
    pose (fun (_ : unit) => y) as const_y.
    specialize (H unit const_x const_y).
    unfold const_x in H.
    unfold const_y in H.
    apply equal_f in H.
    + assumption.
    + extensionality tt. assumption.
    + constructor.
Qed.

Definition Surjective `(f : X → Y) := ∀ y, ∃ x, f x = y.

Lemma surjectivity_is_epic `(f : X → Y) : Surjective f ↔ @Epic Sets _ _ f.
Proof.
  unfold Epic, Surjective.
  split; intros; simpl in *.
  - extensionality y.
    specialize (H y).
    destruct H.
    rewrite <- H.
    apply (equal_f H0).
  - specialize H with (Z := Prop).
    specialize H with (g1 := fun y0 => ∃ x0, f x0 = y0).
    specialize H with (g2 := fun y  => True).
    eapply equal_f in H.
    erewrite H. constructor.
    extensionality x.
    apply propositional_extensionality.
    exists x. reflexivity.
Qed.

(*
* Dual Category — C^op flips morphisms; (C^op)^op = C (involutive)

--------
* 对偶范畴 — C^op 翻转态射方向；(C^op)^op = C（对合）
*)

Program Definition Opposite `(C : Category) : Category := {|
    ob     := @ob C;
    hom    := fun x y => @hom C y x;
    c_id   := @c_id C;
    c_comp := fun _ _ _ f g => g ∘ f
|}.
Obligation 3. rewrite c_comp_assoc. auto. Defined.

(* begin hide *)
Notation "C ^op" := (Opposite C) (at level 90) : category_scope.
(* end hide *)

Lemma op_involutive (C : Category) : (C^op)^op = C.
Proof.
  unfold Opposite.
  unfold Opposite_obligation_1.
  unfold Opposite_obligation_2.
  unfold Opposite_obligation_3.
  simpl. destruct C. simpl.
  apply f_equal3; repeat (extensionality e; simpl; crush).
  extensionality b.
  extensionality c.
  extensionality d.
  extensionality f.
  extensionality g.
  extensionality h. crush.
Qed.

(* op / unop flip a single morphism / op、unop：翻转单个态射 *)

Definition op `{C : Category} : ∀ {X Y}, (X ~{C^op}~> Y) → (Y ~{C}~> X).
Proof. auto. Defined.

Definition unop `{C : Category} : ∀ {X Y}, (Y ~{C}~> X) → (X ~{C^op}~> Y).
Proof. auto. Defined.
