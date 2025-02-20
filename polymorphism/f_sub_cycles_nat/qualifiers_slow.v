Require Export Arith.EqNat.
Require Export Arith.Le.
Require Import Coq.Program.Equality.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import Psatz.
Require Import Coq.Arith.Compare_dec.
Import ListNotations.

Require Import FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.

Require Import vars.
Require Import nats.
Require Import boolean.
Require Import qualifiers_base.
Require Import tactics.

(**********
*  open  *
**********)
Import QualNotations.
Local Open Scope qualifiers.

Lemma closed_Qual_open' : forall {d b f l},
    closed_Qual (S b) f l (Q_lift d) ->
    forall {x}, x <= f ->
    forall {d'}, closed_Qual 0 x l d' -> closed_Qual b f l (open_Qual b d' (Q_lift d)).
Proof.
  intros. qual_destruct d. qual_destruct d'.
  unfold_Q. unfold_N. ndestruct (bvs b); intuition; eauto 3 with arith. eapply closed_Nats_tighten; eauto.
Qed.
Lemma closed_qual_open' : forall {d b f l},
    closed_qual (S b) f l d ->
    forall {x}, x <= f ->
    forall {d'}, closed_qual 0 x l d' -> closed_qual b f l (open_qual b d' d).
Proof.
  intros. apply Q_lift_closed. apply Q_lift_closed' in H,H1. rewrite Q_lift_open_qual. eapply closed_Qual_open'; eauto.
Qed.

Lemma open_subst1_qual_comm : forall {q : qual} {k g fr df ff lf},
    closed_Qual 0 ff lf df↑ ->
    open_qual k ${fr} g (subst_qual q 0 df) = subst_qual (open_qual k ${fr}(S g) q) 0 df.
Proof.
  intros. qual_destruct df. qual_destruct q. unfold_q. 
  ndestruct (bvs0 k); simpl;
  ndestruct (fvs0 0); simpl; 
  ndestruct (bvs k); simpl; 
  ndestruct (n_one (S g) 0);
  apply Q_lift_eq; clift; Qcrush; exfalso; eauto.
Qed.

Lemma open_subst1_qual_comm' : forall {q q' : qual} {k df ff lf},
    closed_Qual 0 ff lf df↑ ->
    open_qual k q' (subst_qual q 0 df) = subst_qual (open_qual k (splice_qual 0 q') q) 0 df.
Proof.
  intros. qual_destruct df. qual_destruct q. qual_destruct q'. unfold_q. 
  ndestruct (fvs0 0); simpl;
  ndestruct (bvs0 k); simpl;
  ndestruct (bvs k); simpl;
  ndestruct ((n_splice 0 fvs1) 0);
  apply Q_lift_eq; clift; Qcrush; exfalso; eauto.
Qed.

Lemma open_qual_commute : forall d frx fry i j x y, i <> j ->
    open_qual i ${frx} x (open_qual j ${fry} y d)
  = open_qual j ${fry} y (open_qual i ${frx} x d).
intros. qual_destruct d. unfold_q. ndestruct (bvs i); ndestruct (bvs j); simpl.
- ndestruct (n_or (n_diff bvs (n_one j)) n_empty i); ndestruct ((n_or (n_diff bvs (n_one i)) n_empty j)); apply Q_lift_eq; Qcrush.
- ndestruct (bvs i); ndestruct (n_or (n_diff bvs (n_one i)) n_empty j); apply Q_lift_eq; Qcrush.
- ndestruct (bvs j); ndestruct (n_or (n_diff bvs (n_one j)) n_empty i); apply Q_lift_eq; Qcrush.
- ndestruct (bvs i); ndestruct (bvs j); apply Q_lift_eq; Qcrush.
Qed.

Lemma open_qual_commute' : forall d i j fr x d' f l, i <> j -> 
  closed_Qual 0 f l d' ↑ ->
  open_qual i ${fr}x (open_qual j d' d)
  = open_qual j d' (open_qual i ${fr}x d).
qual_destruct d; qual_destruct d'. intros. 
unfold_q.
ndestruct (bvs i); ndestruct (bvs j); ndestruct (bvs0 i); ndestruct (bvs0 j); simpl; apply Q_lift_eq; Qcrush; exfalso; eauto. 
Qed.

Lemma open_qual_commute'' : forall d i j d' d'' f l, i <> j -> closed_Qual 0 f l d' ↑ -> closed_Qual 0 f l d'' ↑ ->
  open_qual i d'' (open_qual j d' d)
  = open_qual j d' (open_qual i d'' d).
qual_destruct d. qual_destruct d'. qual_destruct d''. intros. 
unfold_q.
ndestruct (bvs i); ndestruct (bvs j); ndestruct (bvs0 i); ndestruct (bvs0 j); ndestruct (bvs1 i); ndestruct (bvs1 j); simpl; apply Q_lift_eq; Qcrush; exfalso; eauto.
Qed.

Lemma closed_qual_open2 : forall {f l d1 d2 d}, closed_qual 2 f l d -> closed_qual 0 f l d1 -> closed_qual 0 f l d2 -> closed_qual 0 f l (open_qual 1 d1 (open_qual 0 d2 d)).
  intros. erewrite open_qual_commute''; eauto using closed_qual_open'. 
Qed.

Lemma subst1_open_qual_comm : forall {k l d1 d2 q1},
    closed_Qual 0 0 l (Q_lift q1) ->
    subst_qual (open_qual k d1 d2) 0 q1 = open_qual k (subst_qual d1 0 q1) (subst_qual d2 0 q1).
Proof.
  intros. qual_destruct d1. qual_destruct d2. qual_destruct q1. unfold_q.
  ndestruct (bvs0 k); simpl;
  ndestruct (fvs0 0); simpl;
  ndestruct (fvs 0); simpl;
  ndestruct (bvs1 k); simpl;
  apply Q_lift_eq; clift; Qcrush; exfalso; eauto.
Qed.

