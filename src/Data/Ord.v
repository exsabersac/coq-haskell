(*
Total order typeclass (Haskell Ord), requiring Eq:
compare → Ordering, plus bool relations and max/min.
No laws are stated in the class yet.

--------
全序类型类（对应 Haskell Ord），依赖 Eq：
compare 得到 Ordering，并提供布尔比较与 max/min。
类内尚未写定律。
*)

Require Export Hask.Data.Eq.

Generalizable All Variables.

(* Three-way comparison result. / 三向比较结果。 *)
Inductive Ordering := LT | EQ | GT.

(* Class: order on top of Eq. / 类：在 Eq 之上的序。 *)
Class Ord (A : Type) `{Eq A} := {
  compare : A -> A -> Ordering;
  ltb : A -> A -> bool;
  lteb : A -> A -> bool;
  gtb : A -> A -> bool;
  gteb : A -> A -> bool;
  max : A -> A -> A;
  min : A -> A -> A
}.

Infix "<" := ltb (at level 70).
Infix "<=" := lteb (at level 70).
Infix ">" := gtb (at level 70).
Infix ">=" := gteb (at level 70).
