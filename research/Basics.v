(*
[research] Axioms (prop extensionality, proof irrelevance) and a tiny
simple_solver Ltac. Experimental — not in _CoqProject.
--------
【research / 实验草稿，未入 _CoqProject】
命题外延、proof irrelevance 公理，以及简单的 simple_solver Ltac。
*)

Require Export FunctionalExtensionality.

Set Primitive Projection.

Axiom propositional_extensionality : forall P : Prop, P -> P = True.
Axiom propositional_extensionality_rev : forall P : Prop, P = True -> P.
Axiom proof_irrelevance : forall (P : Prop) (u v : P), u = v.

(* Patterns solvable by auto. / 常见可被 auto 解决的模式。 *)
#[export] Hint Extern 4 (?A = ?A) => reflexivity : core.
#[export] Hint Extern 7 (?X = ?Z) =>
  match goal with
  | [H : ?X = ?Y, H' : ?Y = ?Z |- ?X = ?Z] => transitivity Y
  end : core.

Ltac simple_solver :=
  intros;
  try extensionality e;
  compute;
  repeat (
    match goal with
    | [ |- context f [match ?X with _ => _ end] ] =>
      is_var X; destruct X; auto
    end);
  auto.
