(* Copyright (c) 2008-2012, Adam Chlipala
 * 
 * This work is licensed under a
 * Creative Commons Attribution-Noncommercial-No Derivative Works 3.0
 * Unported License.
 * The license text is available at:
 *   http://creativecommons.org/licenses/by-nc-nd/3.0/
 *)

(*
CPDT-style automation (Adam Chlipala): inject / simplHyp / inster / crush'
and the thin wrapper [crush]. Used by early research / Category drafts;
not the main ssreflect path of src/*.

--------
来自 CPDT 的自动化战术包（Adam Chlipala）：inject / simplHyp / inster / crush'
及薄封装 [crush]。早期 research / Category 草稿会用到；
不是本仓 src 主路径上的 ssreflect 风格。
*)

Require Import Coq.Logic.Eqdep Coq.Lists.List.

Require Import Coq.micromega.Lia.

Set Implicit Arguments.
Generalizable All Variables.

(*
inject H: injection + clear H + intros + try subst.
--------
inject H：injection 后清假设、引入新事实并尝试 subst。
*)
Ltac inject H := injection H; clear H; intros; try subst.

(*
appHyps f: try f on each hypothesis; keep first success.
--------
appHyps f：对每个假设试 f，保留首次成功。
*)
Ltac appHyps f :=
  match goal with
    | [ H : _ |- _ ] => f H
  end.

(*
inList x ls: succeed iff x appears in left-nested tuple-list ls.
--------
inList x ls：x 是否出现在左结合嵌套元组列表 ls 中。
*)
Ltac inList x ls :=
  match ls with
    | x => idtac
    | (_, x) => idtac
    | (?LS, _) => inList x LS
  end.

(*
app f ls: try f on each element of tupled list; first success wins.
--------
app f ls：对元组列表各元素试 f，首次成功即停。
*)
Ltac app f ls :=
  match ls with
    | (?LS, ?X) => f X || app f LS || fail 1
    | _ => f ls
  end.

(*
all f ls: run f on every element of ls (must all succeed).
--------
all f ls：对 ls 每个元素都跑 f（全部须成功）。
*)
Ltac all f ls :=
  match ls with
    | (?LS, ?X) => f X; all f LS
    | (_, _) => fail 1
    | _ => f ls
  end.

(*
simplHyp invOne: simplify hyps; auto-invert predicates listed in invOne.
--------
simplHyp invOne：化简假设；对 invOne 中列出的谓词自动 inversion。
*)
Ltac simplHyp invOne :=
  (** Helper function to do inversion on certain hypotheses, where [H] is the hypothesis and [F] its head symbol *)
  let invert H F :=
    (** We only proceed for those predicates in [invOne]. *)
    inList F invOne;
    (** This case covers an inversion that succeeds immediately, meaning no constructors of [F] applied. *)
      (inversion H; fail)
    (** Otherwise, we only proceed if inversion eliminates all but one constructor case. *)
      || (inversion H; [idtac]; clear H; try subst) in

  match goal with
    (** Eliminate all existential hypotheses. *)
    | [ H : ex _ |- _ ] => destruct H

    (** Find opportunities to take advantage of injectivity of data constructors, for several different arities. *)
    | [ H : ?F ?X = ?F ?Y |- ?G ] =>
      (** This first branch of the [||] fails the whole attempt iff the arguments of the constructor applications are already easy to prove equal. *)
      (assert (X = Y); [ assumption | fail 1 ])
      (** If we pass that filter, then we use injection on [H] and do some simplification as in [inject].
         * The odd-looking check of the goal form is to avoid cases where [injection] gives a more complex result because of dependent typing, which we aren't equipped to handle here. *)
      || (injection H;
        match goal with
          | [ |- X = Y -> G ] =>
            try clear H; intros; try subst
        end)
    | [ H : ?F ?X ?U = ?F ?Y ?V |- ?G ] =>
      (assert (X = Y); [ assumption
        | assert (U = V); [ assumption | fail 1 ] ])
      || (injection H;
        match goal with
          | [ |- U = V -> X = Y -> G ] =>
            try clear H; intros; try subst
        end)

    (** Consider some different arities of a predicate [F] in a hypothesis that we might want to invert. *)
    | [ H : ?F _ |- _ ] => invert H F
    | [ H : ?F _ _ |- _ ] => invert H F
    | [ H : ?F _ _ _ |- _ ] => invert H F
    | [ H : ?F _ _ _ _ |- _ ] => invert H F
    | [ H : ?F _ _ _ _ _ |- _ ] => invert H F

    (** Use an (axiom-dependent!) inversion principle for dependent pairs, from the standard library. *)
    | [ H : existT _ ?T _ = existT _ ?T _ |- _ ] => generalize (inj_pair2 _ _ _ _ _ H); clear H

    (** If we're not ready to use that principle yet, try the standard inversion, which often enables the previous rule. *)
    | [ H : existT _ _ _ = existT _ _ _ |- _ ] => inversion H; clear H

    (** Similar logic to the cases for constructor injectivity above, but specialized to [Some], since the above cases won't deal with polymorphic constructors. *)
    | [ H : Some _ = Some _ |- _ ] => injection H; clear H
  end.

(*
rewriteHyp: rewrite with some hyp; auto must close rewrite side goals.
--------
rewriteHyp：用某条假设改写；副目标须能被 auto 关掉。
*)
Ltac rewriteHyp :=
  match goal with
    | [ H : _ |- _ ] => rewrite H by solve [ auto ]
  end.

(*
rewriterP / rewriter: autorewrite + rewriteHyp loop.
--------
rewriterP / rewriter：autorewrite 与假设改写的组合循环。
*)
Ltac rewriterP := repeat (rewriteHyp; autorewrite with core in *).
Ltac rewriter := autorewrite with core in *; rewriterP.

(* app_ass as rewrite hint / 把 app_ass 放进 rewrite hint *)
#[export] Hint Rewrite app_ass : core.

(*
done: marker Prop to encode inster's instantiation trace in the goal.
--------
done：在目标上下文里编码 inster 实例化轨迹的标记谓词。
*)
Definition done (T : Type) (x : T) := True.

(*
inster e trace: instantiate foralls in e; trace avoids repeating choices.
--------
inster e trace：对 e 中全称量词做实例化；trace 避免重复同一选择。
*)
Ltac inster e trace :=
  (** Does [e] have any quantifiers left? *)
  match type of e with
    | forall x : _, _ =>
      (** Yes, so let's pick the first context variable of the right type. *)
      match goal with
        | [ H : _ |- _ ] =>
          inster (e H) (trace, H)
        | _ => fail 2
      end
    | _ =>
      (** No more quantifiers, so now we check if the trace we computed was already used. *)
      match trace with
        | (_, _) =>
          (** We only reach this case if the trace is nonempty, ensuring that [inster] fails if no progress can be made. *)
          match goal with
            | [ H : done (trace, _) |- _ ] =>
              (** Uh oh, found a record of this trace in the context!  Backtrack to try another trace. *)
              fail 1
            | _ =>
              (** What is the type of the proof [e] now? *)
              let T := type of e in
                match type of T with
                  | Prop =>
                    (** [e] should be thought of as a proof, so let's add it to the context, and also add a new marker hypothesis recording our choice of trace. *)
                    generalize e; intro;
                      assert (done (trace, tt)) by constructor
                  | _ =>
                    (** [e] is something beside a proof.  Better make sure no element of our current trace was generated by a previous call to [inster], or we might get stuck in an infinite loop!  (We store previous [inster] terms in second positions of tuples used as arguments to [done] in hypotheses.  Proofs instantiated by [inster] merely use [tt] in such positions.) *)
                    all ltac:(fun X =>
                      match goal with
                        | [ H : done (_, X) |- _ ] => fail 1
                        | _ => idtac
                      end) trace;
                    (** Pick a new name for our new instantiation. *)
                    let i := fresh "i" in (pose (i := e);
                      assert (done (trace, i)) by constructor)
                end
          end
      end
  end.

(*
un_done: clear leftover [done _] marker hypotheses.
--------
un_done：清掉残留的 [done _] 标记假设。
*)
Ltac un_done :=
  repeat match goal with
           | [ H : done _ |- _ ] => clear H
         end.

Require Import JMeq.

(*
crush' lemmas invOne: parameterized crush — inster lemmas + invert invOne.
--------
crush' lemmas invOne：参数化 crush——对 lemmas 做 inster、对 invOne 做 inversion。
*)
Ltac crush' lemmas invOne :=
  (** A useful combination of standard automation *)
  let sintuition := simpl in *; intuition; try subst;
    repeat (simplHyp invOne; intuition; try subst); try congruence in

  (** A fancier version of [rewriter] from above, which uses [crush'] to discharge side conditions *)
  let rewriter := autorewrite with core in *;
    repeat (match goal with
              | [ H : ?P |- _ ] =>
                match P with
                  | context[JMeq] => fail 1 (** JMeq is too fancy to deal with here. *)
                  | _ => rewrite H by crush' lemmas invOne
                end
            end; autorewrite with core in *) in

  (** Now the main sequence of heuristics: *)
    (sintuition; rewriter;
      match lemmas with
        | false => idtac (** No lemmas?  Nothing to do here *)
        | _ =>
          (** Try a loop of instantiating lemmas... *)
          repeat ((app ltac:(fun L => inster L L) lemmas
          (** ...or instantiating hypotheses... *)
            || appHyps ltac:(fun L => inster L L));
          (** ...and then simplifying hypotheses. *)
          repeat (simplHyp invOne; intuition)); un_done
      end;
      sintuition; rewriter; sintuition;
      (** End with a last attempt to prove an arithmetic fact with [lia], or prove any sort of fact in a context that is contradictory by reasoning that [lia] can do. *)
      try lia; try (elimtype False; lia)).

(*
crush: crush' false fail — default no lemmas / no auto-invert list.
--------
crush：crush' false fail——默认无引理列表、无自动 inversion 谓词。
*)
Ltac crush := crush' false fail.

(*
dep_destruct E: remember + dependent destruction + try rewrite back.
Wraps Program.Equality for friendlier use inside Ltac matches.
--------
dep_destruct E：remember + dependent destruction，并尝试写回。
对 Program.Equality 的薄封装，便于在 Ltac match 里使用。
*)
Require Import Program.Equality.

Ltac dep_destruct E :=
  let x := fresh "x" in
    remember E as x; simpl in x; dependent destruction x;
      try match goal with
            | [ H : _ = E |- _ ] => try rewrite <- H in *; clear H
          end.

(*
clear_all: clear every hypothesis that can be cleared without breaking the goal.
--------
clear_all：在不破坏目标的前提下尽量清掉所有假设。
*)
Ltac clear_all :=
  repeat match goal with
           | [ H : _ |- _ ] => clear H
         end.

(*
guess v H: specialize H with v (or evar); auto-prove Prop premises.
--------
guess v H：用 v（或 evar）特化 H；Prop 前提尽量 eauto 消掉。
*)
Ltac guess v H :=
  repeat match type of H with
           | forall x : ?T, _ =>
             match type of T with
               | Prop =>
                 (let H' := fresh "H'" in
                   assert (H' : T); [
                     solve [ eauto 6 ]
                     | specialize (H H'); clear H' ])
                 || fail 1
               | _ =>
                 specialize (H v)
                 || let x := fresh "x" in
                   evar (x : T);
                   let x' := eval unfold x in x in
                     clear x; specialize (H x')
             end
         end.

(*
guessKeep v H: like guess, but keep original H (work on a copy).
--------
guessKeep v H：同 guess，但保留原假设 H（在副本上操作）。
*)
Ltac guessKeep v H :=
  let H' := fresh "H'" in
    generalize H; intro H'; guess v H'.
