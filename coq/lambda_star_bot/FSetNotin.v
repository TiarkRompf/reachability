(** Lemmas and tactics for working with and solving goals related to
    non-membership in finite sets.  The main tactic of interest here
    is [notin_solve].

    Authors: Arthur Charguéraud and Brian Aydemir. *)

Set Implicit Arguments.
Require Import FSetInterface.


(* *********************************************************************** *)
(** * Implementation *)

Module Notin (X : FSetInterface.S).

Import X.


(* *********************************************************************** *)
(** ** Facts about set (non-)membership *)

Lemma in_singleton : forall x,
  In x (singleton x).
Proof.
  auto using singleton_2 with *.
Qed.

Lemma notin_empty : forall x,
  ~ In x empty.
Proof.
  auto using empty_1.
Qed.

Lemma notin_union : forall x E F,
  ~ In x E -> ~ In x F -> ~ In x (union E F).
Proof.
  intros x E F H J K.
  destruct (union_1 K); intuition.
Qed.

Lemma elim_notin_union : forall x E F,
  ~ In x (union E F) -> (~ In x E) /\ (~ In x F).
Proof.
  intros x E F H. split; intros J; contradiction H.
  auto using union_2.
  auto using union_3.
Qed.

Lemma notin_singleton : forall x y,
  ~ E.eq x y -> ~ In x (singleton y).
Proof.
  intros x y H J. assert (K := singleton_1 J). intuition.
Qed.

Lemma elim_notin_singleton : forall x y,
  ~ In x (singleton y) -> ~ E.eq x y.
Proof.
  intros x y H J. contradiction H. auto using singleton_2 with *.
Qed.

Lemma elim_notin_singleton' : forall x y,
  ~ In x (singleton y) -> x <> y.
Proof.
  intros. assert (~ E.eq x y). auto using singleton_2 with *.
  intros J. subst. intuition.
Qed.

Lemma notin_singleton_swap : forall x y,
  ~ In x (singleton y) -> ~ In y (singleton x).
Proof.
  intros.
  assert (Q := elim_notin_singleton H).
  auto using singleton_1.
Qed.


(* *********************************************************************** *)
(** ** Rewriting non-membership facts *)

Lemma notin_singleton_rw : forall x y,
  ~ In x (singleton y) <-> ~ E.eq x y.
Proof.
  intros. split.
    auto using elim_notin_singleton.
    auto using notin_singleton.
Qed.


(* *********************************************************************** *)
(** ** Tactics *)

(** The tactic [notin_simpl_hyps] destructs all hypotheses of the form
    [(~ In x E)], where [E] is built using only [empty], [union], and
    [singleton]. *)

Ltac notin_simpl_hyps :=
  try match goal with
        | H: In ?x ?E -> False |- _ =>
          change (~ In x E) in H;
          notin_simpl_hyps
        | H: ~ In _ empty |- _ =>
          clear H;
          notin_simpl_hyps
        | H: ~ In ?x (singleton ?y) |- _ =>
          let F1 := fresh in
          let F2 := fresh in
          assert (F1 := @elim_notin_singleton x y H);
          assert (F2 := @elim_notin_singleton' x y H);
          clear H;
          notin_simpl_hyps
        | H: ~ In ?x (union ?E ?F) |- _ =>
          destruct (@elim_notin_union x E F H);
          clear H;
          notin_simpl_hyps
      end.

(** The tactic [notin_solve] solves goals of them form [(x <> y)] and
    [(~ In x E)] that are provable from hypotheses of the form
    destructed by [notin_simpl_hyps]. *)

Ltac notin_solve :=
  notin_simpl_hyps;
  repeat (progress (  apply notin_empty
                   || apply notin_union
                   || apply notin_singleton));
  solve [ trivial | congruence | intuition auto with * ].


(* *********************************************************************** *)
(** ** Examples and test cases *)

Lemma test_notin_solve_1 : forall x E F G,
  ~ In x (union E F) -> ~ In x G -> ~ In x (union E G).
Proof.
  intros. notin_solve.
Qed.

Lemma test_notin_solve_2 : forall x y E F G,
  ~ In x (union E (union (singleton y) F)) -> ~ In x G ->
  ~ In x (singleton y) /\ ~ In y (singleton x).
Proof.
  intros. split. notin_solve. notin_solve.
Qed.

Lemma test_notin_solve_3 : forall x y,
  ~ E.eq x y -> ~ In x (singleton y) /\ ~ In y (singleton x).
Proof.
  intros. split. notin_solve. notin_solve.
Qed.

Lemma test_notin_solve_4 : forall x y E F G,
  ~ In x (union E (union (singleton x) F)) -> ~ In y G.
Proof.
  intros. notin_solve.
Qed.

Lemma test_notin_solve_5 : forall x y E F,
  ~ In x (union E (union (singleton y) F)) -> ~ In y E ->
  ~ E.eq y x /\ ~ E.eq x y.
Proof.
  intros. split. notin_solve. notin_solve.
Qed.

End Notin.
