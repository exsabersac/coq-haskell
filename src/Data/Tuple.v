(*
Tuple helpers: reassociation, first/second, curry/uncurry,
and prod_map (fmap on the second component) with identity/composition laws.
Isomorphism instances for unit×A ≅ A are commented out (need Iso).

--------
元组工具：重结合、first/second、curry/uncurry，
以及 prod_map（在第二分量上 fmap）及其恒等/复合律。
unit×A ≅ A 的同构实例已注释（依赖 Iso）。
*)

Require Import Hask.Ltac.
(* Require Import Hask.Control.Iso. *)

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

(*
#[export]
Instance LTuple_Isomorphism {A} : (unit * A) ≅ A :=
{ iso_to   := @snd unit A
; iso_from := pair tt
}.
(* jww (2015-06-17): NYI
Obligation 1. (* iso_to *)
  intros. extensionality x. destruct x. compute. destruct u. reflexivity.
Defined.
*)

#[export]
Instance RTuple_Isomorphism {A} : (A * unit) ≅ A :=
{ iso_to   := @fst A unit
; iso_from := fun x => (x, tt)
}.
(* jww (2015-06-17): NYI
Obligation 1. (* iso_to *)
  intros. extensionality x. destruct x. compute. destruct u. reflexivity.
Defined.
*)
*)

(* Reassociate nested products. / 重结合嵌套积。 *)
Definition tuple_swap_a_bc_to_ab_c {A B C} (x : A * (B * C)) : A * B * C :=
  match x with (a, (b, c)) => ((a, b), c) end.

Definition tuple_swap_ab_c_to_a_bc {A B C} (x : A * B * C) : A * (B * C) :=
  match x with ((a, b), c) => (a, (b, c)) end.

Definition left_triple {A B C} (x : A) (y : B) (z : C) : A * B * C :=
  ((x, y), z).

Definition right_triple {A B C} (x : A) (y : B) (z : C) : A * (B * C) :=
  (x, (y, z)).

(*
#[export]
Instance Tuple_Assoc {A B C} : (A * B * C) ≅ (A * (B * C)) :=
{ iso_to   := tuple_swap_ab_c_to_a_bc
; iso_from := tuple_swap_a_bc_to_ab_c
}.
(* jww (2015-06-17): NYI
Obligation 1. (* iso_to *)
  intros.
  extensionality x.
  unfold compose.
  destruct x.
  destruct p.
  unfold id.
  unfold tuple_swap_a_bc_to_ab_c, tuple_swap_ab_c_to_a_bc.
  reflexivity.
Defined.
Obligation 2. (* iso_from *)
  intros.
  extensionality x.
  unfold compose.
  destruct x.
  destruct p.
  unfold id.
  unfold tuple_swap_a_bc_to_ab_c, tuple_swap_ab_c_to_a_bc.
  reflexivity.
Defined.
*)
*)

(* Map left / right of a pair. / 映射对的左/右分量。 *)
Definition first `(f : a -> b) `(x : a * z) : b * z :=
  match x with (a, z) => (f a, z) end.

Definition second `(f : a -> b) `(x : z * a) : z * b :=
  match x with (z, b) => (z, f b) end.

(* Curry / uncurry between Hom(A×B,C) and Hom(A, Hom(B,C)).
   --------
   柯里化 / 反柯里化。 *)
Definition curry `(f : a -> b -> c) (x : (a * b)) : c :=
  match x with (a, b) => f a b end.

Definition uncurry {X Y Z} (f : X -> Y -> Z) (xy : X * Y) : Z :=
  match xy with (x, y) => f x y end.

Theorem uncurry_works : forall {X Y Z} (x : X) (y : Y) (f : X -> Y -> Z),
  uncurry f (x, y) = f x y.
Proof. reflexivity. Qed.

Lemma fst_snd : forall a b (z : a * b),
  (let '(x, y) := z in (x, y)) = (fst z, snd z).
Proof. intros ? ? [?]; auto. Qed.

Require Import Coq.Lists.List.

Lemma unsplit : forall a b (xs : list (a * b)),
  map (fun x => (fst x, snd x)) xs = xs.
Proof.
  intros.
  induction xs as [|x xs IHxs]; auto; simpl.
  rewrite IHxs.
  destruct x; auto.
Qed.

(* fmap on the second component (fixed first). / 固定第一分量，映射第二分量。 *)
Definition prod_map {A B C : Type} (f : A -> B) (x : C * A) : C * B :=
  match x with (a, b) => (a, f b) end.

Require Import FunctionalExtensionality.

Module TupleLaws.

(* Functor laws for prod_map. / prod_map 的函子律。 *)
Theorem prod_map_id {E A} : @prod_map A A E id = id.
Proof.
  extensionality x.
  destruct x; auto.
Qed.

Theorem prod_map_comp {E A B C} (f : B -> C) (g : A -> B) :
  @prod_map B C E f \o @prod_map A B E g = @prod_map A C E (f \o g).
Proof.
  extensionality x.
  destruct x; auto.
Qed.

Corollary prod_map_comp_x {E A B C} (f : B -> C) (g : A -> B) (x : E * A) :
  prod_map f (prod_map g x) = prod_map (fun x => f (g x)) x.
Proof. destruct x; auto. Qed.

End TupleLaws.
