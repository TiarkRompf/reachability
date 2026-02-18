Require Export Arith.EqNat.
Require Export PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.

(* The bdestruct tactic is borrowed from https://softwarefoundations.cis.upenn.edu/vfa-current/Perm.html *)

Lemma beq_reflect : forall x y, reflect (x = y) (x =? y).
Proof.
  intros x y.
  apply iff_reflect. symmetry. apply Nat.eqb_eq.
Qed.

Lemma blt_reflect : forall x y, reflect (x < y) (x <? y).
Proof.
  intros x y.
  apply iff_reflect. symmetry. apply Nat.ltb_lt.
Qed.

Lemma ble_reflect : forall x y, reflect (x <= y) (x <=? y).
Proof.
  intros x y.
  apply iff_reflect. symmetry. apply Nat.leb_le.
Qed.
#[global] Hint Resolve blt_reflect ble_reflect beq_reflect : bdestruct.

Ltac bdestruct X :=
  let H := fresh in let e := fresh "e" in
                    evar (e: Prop);
                    assert (H: reflect e X); subst e;
                    [eauto with bdestruct
                    | destruct H as [H|H];
                      [ | try first [apply not_lt in H | apply not_le in H] ] ].

Ltac ndestruct X :=
  let H := fresh in let e := fresh "e" in
                    evar (e: Prop);
                    assert (H: reflect e X); subst e;
                    [eauto with ndestruct |
                        destruct H as [H|H]].

Ltac Tauto.intuition_solver ::= auto with *.

Ltac Ex :=
  repeat match goal with
         | H : exists _, _ |- _ => destruct H; intuition
         end.
