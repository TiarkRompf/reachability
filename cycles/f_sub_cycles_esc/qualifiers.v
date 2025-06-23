Require Export Arith.EqNat.
Require Export Arith.Le.
Require Import Coq.Program.Equality.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import Psatz.
Require Import Coq.Arith.Compare_dec.
Require Import FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.
Import ListNotations.

Require Import vars.
Require Export nats.
Require Export boolean.
Require Export qualifiers_base.
Require Export qualifiers_slow.
Require Export tactics.

Export QualNotations.
Local Open Scope qualifiers.

(*************
*  boolean  *
*************)

Lemma not_fresh_fresh_false : forall {d}, (♦∉ (d ⊔ {♦})) -> False.
Qcrush.
Qed.

Lemma subst1_fresh_id : forall {x dx'}, subst_qual {♦} x dx' = {♦}.
  intros. apply Q_lift_eq. Qcrush.
Qed.

Lemma subst1_non_fresh : forall {x qx q}, ♦∉ q -> ♦∉ qx -> ♦∉ (subst_qual q x qx).
  intros. unfold subst_qual. destruct (qfvs q x). Qcrush. Qcrush.
Qed.
#[global] Hint Resolve subst1_non_fresh : core.

Lemma subst1_fresh : forall {x qx q}, ♦∈ q -> ♦∈ (subst_qual q x qx).
  intros. unfold subst_qual. destruct (qfvs q x). Qcrush. Qcrush.
Qed.
#[global] Hint Resolve subst1_fresh : core.

Lemma un_subst1_fresh : forall {x qx q}, ♦∉ qx -> ♦∈ (subst_qual q x qx) -> ♦∈ q.
intros. qual_destruct q. qual_destruct qx. Qcrush. unfold_q. destruct (fvs x); auto. simpl in *. blift. destruct H0; eauto.
Qed.
#[global] Hint Resolve un_subst1_fresh : core.

(**********
*  subq  *
**********)

Lemma Subq_refl : forall {d1}, d1 ⊑↑ d1.
  intros. unfold_Q. unfold_N. intuition.
Qed.
#[global] Hint Resolve Subq_refl : core.

Lemma subq_refl : forall {d1}, d1 ⊑ d1.
  intros. apply Q_lift_subq. apply Subq_refl.
Qed.
#[global] Hint Resolve subq_refl : core.

Lemma Subq_trans : forall {d1 d2 d3}, d1 ⊑↑ d2 -> d2 ⊑↑ d3 -> d1 ⊑↑ d3.
  intros. unfold_Q. unfold_N. intuition.
Qed.

Lemma subq_trans : forall {d1 d2 d3}, d1 ⊑ d2 -> d2 ⊑ d3 -> d1 ⊑ d3.
  intros. apply Q_lift_subq. apply Q_lift_subq' in H,H0. eapply Subq_trans; eauto.
Qed.

Lemma subq_empty : forall {φ}, q_empty ⊑ φ.
intros. unfold_q. unfold_n. intuition.
Qed.
#[global] Hint Resolve subq_empty : core.

Lemma Subq_empty : forall {φ}, q_empty ⊑↑ φ.
intros. unfold_Q. unfold_N. intuition.
Qed.
#[global] Hint Resolve Subq_empty : core.

Lemma Subq_qor_gt: forall {q1 q2 : qual}, q1 ⊑↑ q1 ⊔ q2.
intros. unfold_Q. nlift. unfold_N. intuition.
Qed.
#[global] Hint Resolve Subq_qor_gt : core.

Lemma subq_qor_gt: forall {q1 q2 : qual}, q1 ⊑ q1 ⊔ q2.
intros. apply Q_lift_subq. apply Subq_qor_gt.
Qed.

Lemma Subq_qor_gt': forall {q1 q2 : qual}, q1 ⊑↑ q2 ⊔ q1.
intros. unfold_Q. nlift. unfold_N. intuition.
Qed.
#[global] Hint Resolve Subq_qor_gt' : core.

Lemma subq_qor_gt': forall {q1 q2 : qual}, q1 ⊑ q2 ⊔ q1.
intros. apply Q_lift_subq. apply Subq_qor_gt'.
Qed.

Lemma Subq_qor_elim : forall a b, b ⊑↑ a -> (a ⊔ b) = a.
intros. apply Q_lift_eq. Qcrush.
Qed.

Lemma open_qual_subqual : forall {d1 d2 φ}, d1 ⊑↑ φ -> forall {k}, (open_qual k ∅ d2) ⊑↑ φ -> (open_qual k d1 d2) ⊑↑ φ.
  intros. qual_destruct d2.
unfold_q. ndestruct (bvs k); simpl; auto. Qcrush.
Qed.

(**********
*  qand  *
**********)

Lemma qand_commute : forall {d1 d2}, d1 ⊓ d2 = d2 ⊓ d1.
intros. apply Q_lift_eq. repeat rewrite Q_lift_and. Qcrush.
Qed.

Lemma qand_Sub_l : forall {q1 q2}, q2 ⊓ q1 ⊑↑ q2.
intros. Qcrush.
Qed.

Lemma qand_sub_l : forall {q1 q2}, q2 ⊓ q1 ⊑ q2.
intros. apply Q_lift_subq. apply qand_Sub_l.
Qed.

Lemma qand_Sub_r : forall {q1 q2}, q2 ⊓ q1 ⊑↑ q1.
intros. Qcrush.
Qed.

Lemma qand_sub_r : forall {q1 q2}, q2 ⊓ q1 ⊑ q1.
intros. apply Q_lift_subq. apply qand_Sub_r.
Qed.

Lemma Subq_qand_split : forall a b c d,
  a ⊑↑ c ->
  b ⊑↑ d ->
  a ⊓ b ⊑↑ c ⊓ d.
intros. Qcrush.
Qed.

(*********
*  qor  *
*********)

Lemma qand_qor_dist_l : forall {d1 d2 d3 : qual}, (d1 ⊓ (d2 ⊔ d3)) = ((d1 ⊓ d2) ⊔ (d1 ⊓ d3)).
intros. apply Q_lift_eq. Qcrush.
Qed.

Lemma qand_qor_dist_r : forall {d1 d2 d3 : qual}, ((d1 ⊔ d2) ⊓ d3) = ((d1 ⊓ d3) ⊔ (d2 ⊓ d3)).
intros. apply Q_lift_eq. Qcrush.
Qed.

Lemma qor_qand_dist_l : forall {d1 d2 d3 : qual}, (d1 ⊔ (d2 ⊓ d3)) = ((d1 ⊔ d2) ⊓ (d1 ⊔ d3)).
intros. apply Q_lift_eq. Qcrush.
Qed.

Lemma qor_qand_dist_r : forall {d1 d2 d3 : qual}, ((d1 ⊓ d2) ⊔ d3) = ((d1 ⊔ d3) ⊓ (d2 ⊔ d3)).
intros. apply Q_lift_eq. Qcrush.
Qed.

Lemma qor_empty_left : forall {d}, (q_empty ⊔ d) = d.
intros. apply Q_lift_eq. rewrite Q_lift_or. Qcrush.
Qed.

Lemma qor_empty_right : forall {d}, (d ⊔ q_empty) = d.
intros. apply Q_lift_eq. rewrite Q_lift_or. Qcrush.
Qed.

Lemma Qor_bound : forall q1 q2 q3 : qual, q1 ⊑↑ q3 -> q2 ⊑↑ q3 -> q1 ⊔ q2 ⊑↑ q3.
intros. Qcrush.
Qed.
Lemma qor_bound : forall q1 q2 q3 : qual, q1 ⊑ q3 -> q2 ⊑ q3 -> q1 ⊔ q2 ⊑ q3.
intros. apply Q_lift_subq. apply Qor_bound; apply Q_lift_subq'; auto.
Qed.

Lemma Subq_qor : forall {d1 d2}, d1 ⊑↑ d2 -> forall {d}, d1 ⊔ d ⊑↑ d2 ⊔ d.
intros. Qcrush.
Qed.
#[global] Hint Resolve Subq_qor : core.

Lemma subq_qor : forall {d1 d2}, d1 ⊑ d2 -> forall {d}, d1 ⊔ d ⊑ d2 ⊔ d.
intros. apply Q_lift_subq. apply Subq_qor. apply Q_lift_subq'. auto.
Qed.

Lemma Subq_qor' : forall {d1 d2}, d1 ⊑↑ d2 -> forall {d}, d ⊔ d1 ⊑↑ d ⊔ d2.
intros. Qcrush.
Qed.
#[global] Hint Resolve Subq_qor' : core.
Lemma subq_qor' : forall {d1 d2}, d1 ⊑ d2 -> forall {d}, d ⊔ d1 ⊑ d ⊔ d2.
intros. apply Q_lift_subq. apply Subq_qor'. apply Q_lift_subq'. auto.
Qed.

Lemma qor_idem : forall {q}, (q ⊔ q) = q.
intros. apply Q_lift_eq; Qcrush.
Qed.

Lemma qor_assoc : forall {q1 q2 q3}, (q1 ⊔ (q2 ⊔ q3)) = ((q1 ⊔ q2) ⊔ q3).
intros. apply Q_lift_eq. Qcrush.
Qed.

Lemma qor_commute : forall q1 q2, (q1 ⊔ q2) = (q2 ⊔ q1).
intros. apply Q_lift_eq. Qcrush.
Qed.

Lemma Subq_qor_l : forall d1 d2 d3,
  d1 ⊑↑ d3 -> 
  d2 ⊑↑ d3 -> 
  d1 ⊔ d2 ⊑↑ d3.
intros. Qcrush.
Qed.

(*****************
*  closed_qual  *
*****************)

Lemma closed_Qual_sub : forall {b f l d}, closed_Qual b f l d↑ -> forall {d'}, d' ⊑↑ d -> closed_Qual b f l d'↑.
Proof.
  intros. Qcrush.
Qed.
#[global] Hint Resolve closed_Qual_sub : core.
Lemma closed_qual_sub : forall {b f l d}, closed_qual b f l d -> forall {d'}, d' ⊑ d -> closed_qual b f l d'.
Proof.
  intros. apply Q_lift_closed. apply Q_lift_closed' in H. apply Q_lift_subq' in H0. eauto.
Qed.
#[global] Hint Resolve closed_qual_sub : core.

Lemma closed_Qual_empty : forall {b f l}, closed_Qual b f l ∅↑.
  intros. Qcrush.
Qed.
#[global] Hint Resolve closed_Qual_empty : core.
Lemma closed_qual_empty : forall {b f l}, closed_qual b f l ∅.
  intros. apply Q_lift_closed. auto.
Qed.
#[global] Hint Resolve closed_qual_empty : core.

Lemma closed_Qual_fresh : forall {b f l}, closed_Qual b f l {♦}↑.
  intros. Qcrush.
Qed.
#[global] Hint Resolve closed_Qual_fresh : core.
Lemma closed_qual_fresh : forall {b f l}, closed_qual b f l {♦}.
  intros. apply Q_lift_closed. auto.
Qed.
#[global] Hint Resolve closed_qual_fresh : core.

Lemma closed_Qual_monotone : forall {f b l d},
    closed_Qual b f l d↑ ->
    forall {b' f' l'},
      b <= b' ->
      f <= f' ->
      l <= l' ->
      closed_Qual b' f' l' d↑.
Proof.
  intros. repeat split; eapply closed_Nats_mono; eauto; eapply H.
Qed.

Lemma closed_qual_monotone : forall {f b l d},
    closed_qual b f l d ->
    forall {b' f' l'},
      b <= b' ->
      f <= f' ->
      l <= l' ->
      closed_qual b' f' l' d.
Proof.
  intros. apply Q_lift_closed. eapply closed_Qual_monotone; eauto.
Qed.

Lemma closed_Qual_open_id : forall {d b f l},
    closed_Qual b f l (Q_lift d) -> forall {n}, b <= n -> forall {x}, (open_qual n x d) = d.
Proof.
  intros. qual_destruct d. qual_destruct x. unfold_q.
  ndestruct (bvs n); auto.
  apply Q_lift_eq. unfold_Q. nlift. unfold_N. repeat f_equal; intuition.
  all: exfalso; eauto.
Qed.
#[global] Hint Resolve closed_Qual_open_id : core.
Lemma closed_qual_open_id : forall {d b f l},
    closed_qual b f l d -> forall {n}, b <= n -> forall {x}, (open_qual n x d) = d.
Proof.
  intros. apply Q_lift_closed' in H. eauto.
Qed.
#[global] Hint Resolve closed_qual_open_id : core.

Lemma closed_Qual_open_succ : forall {d b fr f l},
    closed_Qual b f l d↑ ->
    forall {j}, closed_Qual b (S f) l (open_Qual j ${fr}f↑ d↑).
Proof.
  intros. qual_destruct d.
  ndestruct (bvs j); Qcrush.
Qed.
Lemma closed_qual_open_succ : forall {d b fr f l},
    closed_qual b f l d ->
    forall {j}, closed_qual b (S f) l (open_qual j ${fr}f d).
Proof.
  intros. apply Q_lift_closed. apply Q_lift_closed' in H. rewrite Q_lift_open_qual. eapply closed_Qual_open_succ; eauto.
Qed.

Lemma closed_Qual_qor: forall {b f l d1 d2}, closed_Qual b f l (Q_lift d1) -> closed_Qual b f l (Q_lift d2) -> closed_Qual b f l (Q_lift (d1 ⊔ d2)).
intros. Qcrush.
Qed.
Lemma closed_qual_qor: forall {b f l d1 d2}, closed_qual b f l d1 -> closed_qual b f l d2 -> closed_qual b f l (d1 ⊔ d2).
  intros. apply Q_lift_closed. apply Q_lift_closed' in H,H0. apply closed_Qual_qor; auto.
Qed.
Lemma closed_Qual_qand: forall {b f l d1 d2}, closed_Qual b f l (Q_lift d1) -> closed_Qual b f l (Q_lift d2) -> closed_Qual b f l (Q_lift (d1 ⊓ d2)).
intros. Qcrush.
Qed.
Lemma closed_qual_qand: forall {b f l d1 d2}, closed_qual b f l d1 -> closed_qual b f l d2 -> closed_qual b f l (d1 ⊓ d2).
  intros. apply Q_lift_closed. apply Q_lift_closed' in H,H0. apply closed_Qual_qand; auto.
Qed.

Lemma closed_Qual_qand_l : forall q1 q2 b f l,
  closed_Qual b f l q2 ↑ ->
  closed_Qual b f l (q1 ⊓ q2) ↑.
intros. Qcrush.
Qed.

Lemma closed_Qual_qand_r : forall q1 q2 b f l,
  closed_Qual b f l q1 ↑ ->
  closed_Qual b f l (q1 ⊓ q2) ↑.
intros. Qcrush.
Qed.

Lemma qand_subq_l : forall q1 q2, q1 ⊓ q2 ⊑↑ q2.
intros. Qcrush.
Qed.

Lemma qand_subq_r : forall q1 q2, q1 ⊓ q2 ⊑↑ q1.
intros. Qcrush.
Qed.

Lemma closed_Qual_qqplus: forall {b f l d1 d2}, closed_Qual b f l d1 ↑ -> closed_Qual b f l d2 ↑ -> closed_Qual b f l (d1 ⋓ d2) ↑.
  intros. qual_destruct d1. qual_destruct d2. rewrite Q_lift_qplus. destruct fr; Qcrush.
Qed.
Lemma closed_qual_qqplus: forall {b f l d1 d2}, closed_qual b f l d1 -> closed_qual b f l d2 -> closed_qual b f l (d1 ⋓ d2).
  intros. apply Q_lift_closed. eauto using closed_Qual_qqplus.
Qed.

Lemma closed_Qual_subq_and : forall {b f l d1 d1' d2 d2'}, d1 ⊑↑ d1' -> d2 ⊑↑ d2' -> closed_Qual b f l (Q_lift (d1' ⊓ d2')) -> closed_Qual b f l (Q_lift (d1 ⊓ d2)).
intros. Qcrush.
Qed.

(************
*  splice  *
************)

Lemma splice_qual_empty : forall {k}, splice_qual k ∅ = ∅.
  intros. apply Q_lift_eq. Qcrush.
Qed.
#[global] Hint Resolve splice_qual_empty : core.

Lemma splice_qual_fresh : forall {k}, splice_qual k {♦} = {♦}.
  intros. apply Q_lift_eq. Qcrush.
Qed.
#[global] Hint Resolve splice_qual_fresh : core.

Lemma splice_qual_id : forall {d b f l},
  closed_Qual b f l (Q_lift d) ->
  (splice_qual f d) = d.
Proof.
  Qcrush. qual_destruct d. unfold_Q. unfold_q. intuition. repeat f_equal; eauto using n_splice_id.
Qed.

Lemma splice_qual_open : forall {d j fr n m}, 
  splice_qual n (open_qual j ${fr}(m + n) d) = 
  open_qual j ${fr}(S (m + n)) (splice_qual n d).
Proof.
  intros. qual_destruct d. apply Q_lift_eq. repeat rewrite Q_lift_open_qual, Q_lift_splice_qual. Qcrush.
  bdestruct (x <=? n); intuition.
Qed.

Lemma splice_qual_qand_dist : forall {d1 d2 k}, splice_qual k (d1 ⊓ d2) = (splice_qual k d1) ⊓ (splice_qual k d2).
  intros. qual_destruct d1; qual_destruct d2; intuition.
  unfold_q. unfold_n. repeat f_equal. apply functional_extensionality. intros.
  bdestruct (x =? k); bdestruct (x <? k); intuition.
Qed.

Lemma splice_qual_mem_lt : forall {x k d1}, x < k -> $x ∈ᵥ splice_qual k d1 -> $x ∈ᵥ d1.
  intros. qual_destruct d1. simpl in *.
  unfold_q. rewrite N_lift_splice in H0. unfold_N. intuition.
Qed.

Lemma splice_qual_one_S : forall {i k}, i >= k -> splice_qual k ($! i) = $! (S i).
intros. unfold_q. rewrite n_splice_one_S; auto.
Qed.

Lemma splice_qual_one_inv : forall {i k}, i < k -> splice_qual k ($! i) = $! i.
intros. unfold_q. rewrite n_splice_one_inv; auto.
Qed.

Lemma splice_qual_glb_dist : forall {d1 d2 k}, splice_qual k (d1 ⊓ d2) = (splice_qual k d1) ⊓ (splice_qual k d2).
  intros. apply Q_lift_eq. Qcrush.
Qed.

Lemma splice_qual_glb_dist' : forall {d1 d2 k}, splice_qual k (d1 ⋒ d2) = ((splice_qual k d1) ⋒ (splice_qual k d2)).
  intros. apply Q_lift_eq. Qcrush.
Qed.

Lemma splice_qual_lub_dist : forall {d1 d2 k}, splice_qual k (d1 ⊔ d2) = ((splice_qual k d1) ⊔ (splice_qual k d2)).
  intros. apply Q_lift_eq. Qcrush. bdestruct (x <? k); intuition. bdestruct (x =? k); intuition. assert (x > k) by lia. Qcrush.
Qed.

Lemma splice_qual_mem_ge : forall {x k d1}, x >= k -> $(S x) ∈ᵥ (splice_qual k d1) -> $x ∈ᵥ d1.
  intros. Qcrush.
Qed.

Lemma splice_qual_mem_loc : forall {l k d1}, l ∈ₗ (splice_qual k d1) <-> l ∈ₗ d1.
  intros. Qcrush.
Qed.

Lemma splice_qual_not_mem : forall {k d1}, $k ∈ᵥ (splice_qual k d1) -> False.
  intros. Qcrush.
Qed.

Lemma splice_qual_just_fv_ge : forall {k j fr}, k <= j -> splice_qual k (${fr} j) = ${fr}(S j).
  intros. apply Q_lift_eq. Qcrush.
Qed.

Lemma splice_qual_just_fv_lt : forall {k j fr}, k > j -> splice_qual k (${fr} j) = ${fr}j.
  intros. apply Q_lift_eq. Qcrush.
Qed.

Lemma not_fresh_splice_iff : forall {df n}, ♦∉ df <-> ♦∉ (splice_qual n df).
  intros. Qcrush.
Qed.

Lemma fresh_splice_iff : forall {df n}, ♦∈ df <-> ♦∈ (splice_qual n df).
  intros. Qcrush.
Qed.


(***********
*  subst  *
***********)

Lemma subst1_qual_empty : forall {dx}, subst_qual q_empty 0 dx = q_empty.
  intros. qual_destruct dx. unfold_q. repeat f_equal; nlift; intros.
Qed.
#[global] Hint Resolve subst1_qual_empty : core.

Lemma subst1_qual_id : forall {b l q}, closed_Qual b 0 l (Q_lift q) -> forall {q1}, subst_qual q 0 q1 = q.
Proof.
  intros. qual_destruct q. qual_destruct q1. apply Q_lift_eq. rewrite Q_lift_subst_qual. Qcrush.
  - eauto.
  - exfalso. intuition eauto 3 with arith.
  - intuition eauto 3 with arith.
  - intuition eauto 3 with arith.
Qed.

Lemma subst_qual_id : forall b l n q q1,
  closed_Qual b 0 l q ↑ -> subst_qual q n q1 = q.
intros. qual_destruct q. qual_destruct q1. apply Q_lift_eq. rewrite Q_lift_subst_qual. Qcrush.
- eauto.
- exfalso. intuition eauto 3 with arith.
- exfalso. intuition eauto.
- exfalso. intuition eauto.
- intuition eauto 3 with arith.
- intuition eauto 3 with arith.
Qed.

Lemma closed_qual_subst1 : forall {q b f l},
    closed_Qual b (S f) l q ↑ ->
    forall {d1 l1}, closed_Qual 0 0 l1 d1 ↑ ->
    forall{l2},
      l <= l2 -> l1 <= l2 ->
      closed_Qual b f l2 (subst_qual q 0 d1) ↑.
Proof.
  intros. qual_destruct q. unfold_q. 
  ndestruct (fvs 0); Qcrush; try solve [eauto using Arith_prebase.lt_S_n, Nat.lt_le_trans]; try solve [exfalso; eauto 3].
Qed.

Lemma closed_Qual_subst1 : forall {q b f l},
  closed_Qual b (S f) l q ↑ ->
  forall {d1 l1}, closed_Qual b f l1 d1 ↑ ->
  forall{l2},
  l <= l2 -> l1 <= l2 ->
  closed_Qual b f l2 (subst_qual q 0 d1) ↑.
Proof.
  intros. qual_destruct q. unfold_q. 
ndestruct (fvs 0); Qcrush; try solve [eauto using Arith_prebase.lt_S_n, Nat.lt_le_trans]; try solve [exfalso; eauto 3].
Qed.

Lemma subst1_qor_dist : forall {q1 q2 df},
  subst_qual (q1 ⊔ q2) 0 df = ((subst_qual q1 0 df) ⊔ (subst_qual q2 0 df)).
Proof.
  intros. qual_destruct q1. qual_destruct q2. qual_destruct df. unfold_q.
  ndestruct (fvs 0); simpl;
  ndestruct (fvs0 0); simpl; apply Q_lift_eq; Qcrush. 
Qed.

Lemma subst_qual_subqual_monotone : forall {d1 d2}, d1 ⊑↑ d2 -> forall {df}, (subst_qual d1 0 df) ⊑↑ (subst_qual d2 0 df).
Proof.
  intros. qual_destruct d1; qual_destruct d2; qual_destruct df; unfold_q.
  ndestruct (fvs0 0); simpl;
  ndestruct (fvs 0); simpl; Qcrush.
Qed.

Lemma subst_filter0 : forall {d φ l fr}, closed_Qual 0 0 l (Q_lift d) -> Subq (Q_lift ${fr}0) (Q_lift φ) -> Subq (Q_lift d) (Q_lift (subst_qual φ 0 d)).
  intros. qual_destruct φ. unfold_q. 
  ndestruct (fvs 0); Qcrush. 
Qed.

(***********
*  qplus  *
***********)

Lemma Qqplus_upper_l : forall {d1 d2}, d1 ⊑↑ (d1 ⋓ d2).
  intros. qual_destruct d1. unfold_q. destruct fr; auto. Qcrush.
Qed.
#[global] Hint Resolve Qqplus_upper_l : core.

Lemma qqplus_upper_l : forall {d1 d2}, d1 ⊑ (d1 ⋓ d2).
  intros. apply Q_lift_subq. intuition.
Qed.
#[global] Hint Resolve Qqplus_upper_l : core.

Lemma qqplus_qbot_right_neutral : forall {d}, (d ⋓ ∅) = d.
intros. qual_destruct d. unfold_q. destruct fr; auto. apply Q_lift_eq. Qcrush.
Qed.
#[global] Hint Resolve qqplus_qbot_right_neutral : core.

Lemma qqplus_qbot_left_cancel : forall {d}, (∅ ⋓ d) = ∅.
intros. unfold_q. auto.
Qed.
#[global] Hint Resolve qqplus_qbot_left_cancel : core.

Lemma Subqual_qqplus : forall {d1 d2 d}, d1 ⊑↑ d2 -> d1 ⋓ d ⊑↑ d2 ⋓ d.
  intros. qual_destruct d1. qual_destruct d2. qual_destruct d. unfold_q. destruct fr; destruct fr0; Qcrush.
Qed.
#[global] Hint Resolve Subqual_qqplus : core.

Lemma subqual_qqplus : forall {d1 d2 d}, d1 ⊑ d2 -> d1 ⋓ d ⊑ d2 ⋓ d.
  intros. apply Q_lift_subq. apply Q_lift_subq' in H. intuition.
Qed.
#[global] Hint Resolve subqual_qqplus : core.

Lemma Subqual_qqplus_l : forall {d1 d2 d}, d1 ⊑↑ d2 -> d ⋓ d1 ⊑↑ d ⋓ d2.
  intros. qual_destruct d. qual_destruct d1. qual_destruct d2. unfold_q. destruct fr; destruct fr0; Qcrush.
Qed.
#[global] Hint Resolve Subqual_qqplus_l : core.

Lemma subqual_qqplus_l : forall {d1 d2 d}, d1 ⊑ d2 -> d ⋓ d1 ⊑ d ⋓ d2.
  intros. apply Q_lift_subq. apply Q_lift_subq' in H. intuition.
Qed.
#[global] Hint Resolve subqual_qqplus_l : core.

Lemma Qqplus_bound : forall {q1 q2 q3}, q1 ⊑↑ q3 -> q2 ⊑↑ q3 -> q1 ⋓ q2 ⊑↑ q3.
  intros. qual_destruct q1. unfold_q. destruct fr; Qcrush.
Qed.

Lemma qqplus_bound : forall {q1 q2 q3}, q1 ⊑ q3 -> q2 ⊑ q3 -> q1 ⋓ q2 ⊑ q3.
  intros. apply Q_lift_subq. apply Q_lift_subq' in H,H0. apply Qqplus_bound; auto. 
Qed.

Lemma not_fresh_qqplus : forall {d1 d'}, ♦∉ d1 -> (d1 ⋓ d') = d1.
  intros. qual_destruct d1. unfold_q. destruct fr; Qcrush.
Qed.
#[global] Hint Resolve not_fresh_qqplus : core.

Lemma qqplus_fresh : forall {d d'}, ♦∈ d -> (d ⋓ d') = (d ⊔ d').
  intros. qual_destruct d. unfold_q. destruct fr; Qcrush.
Qed.

(***********
*  qdiff  *
***********)

Lemma qdiff_subq : forall a b, 
  a ⊖ b ⊑↑ a.
intros. rewrite Q_lift_diff. Qcrush. 
Qed.
#[global] Hint Resolve qdiff_subq : core.

Lemma Subq_qdiff_monotone: forall q1 q2 r,
   q1 ⊑↑ q2 ->
   q1 ⊖ r ⊑↑ q2 ⊖ r.
intros. repeat rewrite Q_lift_diff. Qcrush.
Qed.
#[global] Hint Resolve Subq_qdiff_monotone : core.

Lemma Subq_qdiff_monotone': forall q1 q2 q,
   q1 ⊑↑ q2 ->
   q ⊖ q2 ⊑↑ q ⊖ q1.
intros. repeat rewrite Q_lift_diff. Qcrush.
Qed.
#[global] Hint Resolve Subq_qdiff_monotone' : core.

Lemma closed_Qual_qdiff: forall b f l q1 q2,
  closed_Qual b f l q1 ↑ ->
  closed_Qual b f l (q1 ⊖ q2) ↑.
intros. rewrite Q_lift_diff. Qcrush.
Qed.

Lemma closed_Qual_qdiff_qlub: forall b f l q1 q2 q3,
  closed_Qual b f l (q1 ⊔ q3) ↑ ->
  closed_Qual b f l (q1 ⊖ q2 ⊔ q3) ↑.
intros. apply closed_Qual_qor. rewrite Q_lift_diff. all: Qcrush.
Qed.

Lemma qdiff_splice: forall {d r : qual} {n:nat},
  splice_qual n (d ⊖ r) = (splice_qual n d) ⊖ (splice_qual n r).
intros. apply Q_lift_eq. repeat rewrite Q_lift_diff. repeat rewrite Q_lift_splice_qual. repeat rewrite Q_lift_diff. Qcrush. bdestruct (x <? n); intuition. assert (x > n). lia. intuition.
Qed.

Lemma Subq_qdiff_qlub : forall d1 d2 r, d1 ⊖ r ⊑↑ d2 -> d1 ⊑↑ d2 ⊔ r.
intros. rewrite Q_lift_or. rewrite Q_lift_diff in H. Qcrush. 
#[local] Hint Resolve is_true_reflect : bdestruct.
bdestruct (fst (fst (fst r))); intuition.
#[local] Remove Hints is_true_reflect : bdestruct.
ndestruct ((snd (fst (fst r))) x); intuition.
ndestruct ((snd (fst r)) x); intuition.
ndestruct ((snd r) x); intuition.
Qed.

Lemma Subq_qdiff_qlub' : forall d1 d2 r, d1 ⊑↑ d2 ⊔ r -> d1 ⊖ r ⊑↑ d2.
intros. rewrite Q_lift_diff. rewrite Q_lift_or in H. Qcrush. 
apply H in H4. intuition.
apply H1 in H4. intuition.
apply H3 in H4. intuition.
Qed.

Lemma n_sub_qbvs_qdiff_qlub_open : forall d1 d2 r,
  n_sub (qbvs (d1 ⊖ r ⊔ #! 0)) (qbvs d2) ->
  n_sub (qbvs (d1 ⊔ #! 0)) (qbvs (d2 ⊔ r)).
intros. apply N_lift_sub. apply N_lift_sub' in H. Qcrush.
ndestruct ((snd (fst r)) x); intuition. 
Qed.

Lemma qdiff_qdiff_dist : forall a b c, 
  a ⊖ (b ⊖ c) = ((a ⊖ b) ⊔ (a ⊓ c)).
intros. apply Q_lift_eq. rewrite Q_lift_or. repeat rewrite Q_lift_and. repeat rewrite Q_lift_diff. Qcrush.
- destruct (fst (fst (fst b))); intuition. right. unfold Is_true in H. intuition. destruct (fst (fst (fst c))); intuition. 
- ndestruct (snd (fst (fst b)) x); intuition. ndestruct ((snd (fst (fst c))) x); intuition. 
- ndestruct (snd (fst b) x); intuition. ndestruct ((snd (fst c)) x); intuition. 
- ndestruct (snd b x); intuition. ndestruct ((snd c) x); intuition. 
Qed.

Lemma qdiff_qdiff_dist' : forall a b c, 
  a ⊖ (b ⊖ c) = ((a ⊖ b) ⊔ (a ⊓ b ⊓ c)).
intros. apply Q_lift_eq. rewrite Q_lift_or. repeat rewrite Q_lift_and. repeat rewrite Q_lift_diff. Qcrush.
- destruct (fst (fst (fst b))); intuition. right. unfold Is_true in H. intuition. destruct (fst (fst (fst c))); intuition. 
- ndestruct (snd (fst (fst b)) x); intuition. ndestruct ((snd (fst (fst c))) x); intuition. 
- ndestruct (snd (fst b) x); intuition. ndestruct ((snd (fst c)) x); intuition. 
- ndestruct (snd b x); intuition. ndestruct ((snd c) x); intuition. 
Qed.

Lemma qdiff_qand : forall a b, 
  a ⊖ b = a ⊖ (a ⊓ b).
intros. apply Q_lift_eq. repeat rewrite Q_lift_diff. rewrite Q_lift_and. Qcrush.
Qed.

Lemma qdiff_empty : forall a, 
  a ⊖ ∅ = a.
intros. apply Q_lift_eq. rewrite Q_lift_diff. Qcrush.
Qed.

Lemma qor_qdiff_dist_l : forall a b c,
  (a ⊔ b) ⊖ c = ((a ⊖ c) ⊔ (b ⊖ c)).
intros. apply Q_lift_eq. rewrite Q_lift_or. repeat rewrite Q_lift_diff. Qcrush.
Qed.

Lemma qor_qdiff_dist_r : forall a b c,
  a ⊖ (b ⊔ c) = ((a ⊖ b) ⊓ (a ⊖ c)).
intros. apply Q_lift_eq. repeat rewrite Q_lift_and. repeat rewrite Q_lift_diff. rewrite Q_lift_or. Qcrush.
Qed.

Lemma qdiff_subq_notin : forall a b c, 
  a ⊑↑ b ⊖ c -> a ⊓ c = ∅.
intros. rewrite Q_lift_diff in H. apply Q_lift_eq. rewrite Q_lift_and. Qcrush.
apply H in H4. intuition.
apply H1 in H4. intuition.
apply H3 in H4. intuition.
Qed.

Lemma qor_qdiff_dist_disj_l: forall d1 d2 r,
  d2 ⊓ r ⊑↑ ∅ ->
  ((d1 ⊔ d2) ⊖ r) = ((d1 ⊖ r) ⊔ d2).
intros. apply Q_lift_eq. rewrite Q_lift_diff. repeat rewrite Q_lift_or. rewrite Q_lift_diff. Qcrush; eauto.
Qed.

Lemma qdiff_disj_id : forall d r, d ⊓ r ⊑↑ ∅ -> (d ⊖ r) = d.
intros. apply Q_lift_eq. rewrite Q_lift_diff. rewrite Q_lift_and in H. Qcrush; eauto.
Qed.

Lemma qdiff_qor_dist : forall a b c,
  (a ⊔ c) ⊖ (b ⊔ c) = a ⊖ (b ⊔ c).
intros. apply Q_lift_eq. repeat rewrite Q_lift_diff. repeat rewrite Q_lift_or. Qcrush; eauto.
Qed.

(***********
*  qn/Qn  *
***********)

(* simulate a qn *)
Definition qfr : qual -> nats := (fun q _ => qfresh q).
#[global] Hint Unfold qfr : core.
(* simulate a Qn *)
Definition Qfr : Qual -> Nats := (fun q _ => qfresh q).
#[global] Hint Unfold Qfr : core.

Definition Q_lift_qn' (f : qual -> nats) (F : Qual -> Nats) :=
  forall (q : qual), N_lift (f q) = F (Q_lift q).
#[global] Hint Unfold Q_lift_qn' : core.

Lemma Q_lift_qn_qfr : Q_lift_qn' qfr Qfr.
autounfold. intros. Qcrush. unfold N_lift. unfold Is_true in *. destruct (fst (fst (fst q))); auto.
Qed.

Lemma Q_lift_qn_qfvs : Q_lift_qn' qfvs qfvs.
autounfold. intuition.
Qed.

Lemma Q_lift_qn_qbvs : Q_lift_qn' qbvs qbvs.
autounfold. intuition.
Qed.

Lemma Q_lift_qn_qlocs : Q_lift_qn' qlocs qlocs.
autounfold. intuition.
Qed.

Lemma Q_lift_qn_mix_false : Q_lift_qn' qbvs qfvs -> False.
autounfold. intuition. specialize (H (false, n_empty, n_one 1, n_empty)). unfold_q. nlift. assert (N_one 1 1). intuition. rewrite H in H0. unfold_N. auto. 
Qed.

Definition Qn_or_dist' (qenv_Qn : Qual -> Nats) := forall q1 q2, qenv_Qn (Qor q1 q2) = N_or (qenv_Qn q1) (qenv_Qn q2).
#[global] Hint Unfold Qn_or_dist' : core.

Lemma Qn_or_dist_qfr : Qn_or_dist' Qfr.
autounfold. intuition.
Qed.

Lemma Qn_or_dist_qfvs : Qn_or_dist' qfvs.
autounfold. intuition.
Qed.

Lemma Qn_or_dist_qbvs : Qn_or_dist' qbvs.
autounfold. intuition.
Qed.

Lemma Qn_or_dist_qlocs : Qn_or_dist' qlocs.
autounfold. intuition.
Qed.

Definition qn_or_dist' (qn : qual -> nats) := forall q1 q2, qn (qor q1 q2) = n_or (qn q1) (qn q2).
#[global] Hint Unfold qn_or_dist' : core.

Lemma qn_or_dist_qfr : qn_or_dist' qfr.
autounfold. intuition.
Qed.

Lemma qn_or_dist_qfvs : qn_or_dist' qfvs.
autounfold. intuition.
Qed.

Lemma qn_or_dist_qbvs : qn_or_dist' qbvs.
autounfold. intuition.
Qed.

Lemma qn_or_dist_qlocs : qn_or_dist' qlocs.
autounfold. intuition.
Qed.

Definition Qn_and_dist' (qenv_Qn : Qual -> Nats) := forall q1 q2, qenv_Qn (Qand q1 q2) = N_and (qenv_Qn q1) (qenv_Qn q2).
#[global] Hint Unfold Qn_and_dist' : cande.

Lemma Qn_and_dist_qfr : Qn_and_dist' Qfr.
autounfold. intuition.
Qed.

Lemma Qn_and_dist_qfvs : Qn_and_dist' qfvs.
autounfold. intuition.
Qed.

Lemma Qn_and_dist_qbvs : Qn_and_dist' qbvs.
autounfold. intuition.
Qed.

Lemma Qn_and_dist_qlocs : Qn_and_dist' qlocs.
autounfold. intuition.
Qed.

Definition qn_and_dist' (qn : qual -> nats) := forall q1 q2, qn (qand q1 q2) = n_and (qn q1) (qn q2).
#[global] Hint Unfold qn_and_dist' : cande.

Lemma qn_and_dist_qfr : qn_and_dist' qfr.
autounfold. intuition.
Qed.

Lemma qn_and_dist_qfvs : qn_and_dist' qfvs.
autounfold. intuition.
Qed.

Lemma qn_and_dist_qbvs : qn_and_dist' qbvs.
autounfold. intuition.
Qed.

Lemma qn_and_dist_qlocs : qn_and_dist' qlocs.
autounfold. intuition.
Qed.

Definition Qn_sub' (Qn : Qual -> Nats) := forall q1 q2 : Qual, Subq q1 q2 -> N_sub (Qn q1) (Qn q2).
#[global] Hint Unfold Qn_sub' : core.

Lemma Qn_sub_qfr : Qn_sub' Qfr.
autounfold. intuition. unfold N_sub. intuition.
Qed.

Lemma Qn_sub_qfvs : Qn_sub' qfvs.
autounfold. intuition.
Qed.

Lemma Qn_sub_qbvs : Qn_sub' qbvs.
autounfold. intuition.
Qed.

Lemma Qn_sub_qlocs : Qn_sub' qlocs.
autounfold. intuition.
Qed.

Definition qn_sub' (qn : qual -> nats) := forall q1 q2 : qual, q1 ⊑ q2 -> n_sub (qn q1) (qn q2).
#[global] Hint Unfold qn_sub' : core.

Lemma qn_sub_qfr : qn_sub' qfr.
autounfold. intuition. unfold n_sub. blift. intuition.
Qed.

Lemma qn_sub_qfvs : qn_sub' qfvs.
autounfold. intuition.
Qed.

Lemma qn_sub_qbvs : qn_sub' qbvs.
autounfold. intuition.
Qed.

Lemma qn_sub_qlocs : qn_sub' qlocs.
autounfold. intuition.
Qed.

Definition Qn_splice_dist' (qenv_Qn : Qual -> Nats) := forall n q, qenv_Qn (splice_Qual n q) = N_splice n (qenv_Qn q).
#[global] Hint Unfold Qn_splice_dist' : core.

Definition Qn_splice_inv' (qenv_Qn : Qual -> Nats) := forall n q, qenv_Qn (splice_Qual n q) = (qenv_Qn q).
#[global] Hint Unfold Qn_splice_inv' : core.

Lemma Qn_splice_inv_qfr : Qn_splice_inv' Qfr.
autounfold. intuition.
Qed.

Lemma Qn_splice_dist_qfvs : Qn_splice_dist' qfvs.
autounfold. intuition.
Qed.

Lemma Qn_splice_inv_qbvs : Qn_splice_inv' qbvs.
autounfold. intuition.
Qed.

Lemma Qn_splice_inv_qlocs : Qn_splice_inv' qlocs.
autounfold. intuition.
Qed.

Definition qn_splice_dist' (qenv_qn : qual -> nats) := forall n q, qenv_qn (splice_qual n q) = n_splice n (qenv_qn q).
#[global] Hint Unfold qn_splice_dist' : core.

Definition qn_splice_inv' (qenv_qn : qual -> nats) := forall n q, qenv_qn (splice_qual n q) = (qenv_qn q).
#[global] Hint Unfold qn_splice_inv' : core.

Lemma qn_splice_inv_qfr : qn_splice_inv' qfr.
autounfold. intuition.
Qed.

Lemma qn_splice_dist_qfvs : qn_splice_dist' qfvs.
autounfold. intuition.
Qed.

Lemma qn_splice_inv_qbvs : qn_splice_inv' qbvs.
autounfold. intuition.
Qed.

Lemma qn_splice_inv_qlocs : qn_splice_inv' qlocs.
autounfold. intuition.
Qed.

Class qnmap (qn : qual -> nats) (Qn : Qual -> Nats) : Type := {
  qn_sub : qn_sub' qn;
  Qn_sub : Qn_sub' Qn;
  qn_or_dist : qn_or_dist' qn;
  Qn_or_dist : Qn_or_dist' Qn;
  qn_and_dist : qn_and_dist' qn;
  Qn_and_dist : Qn_and_dist' Qn;
  Q_lift_qn : Q_lift_qn' qn Qn;
}.

#[export] Instance qnmap_qfr : qnmap qfr Qfr : Type := {
  qn_sub := qn_sub_qfr;
  Qn_sub := Qn_sub_qfr;
  qn_or_dist := qn_or_dist_qfr;
  Qn_or_dist := Qn_or_dist_qfr;
  qn_and_dist := qn_and_dist_qfr;
  Qn_and_dist := Qn_and_dist_qfr;
  Q_lift_qn := Q_lift_qn_qfr;
}.

#[export] Instance qnmap_qfvs : qnmap qfvs qfvs : Type := {
  qn_sub := qn_sub_qfvs;
  Qn_sub := Qn_sub_qfvs;
  qn_or_dist := qn_or_dist_qfvs;
  Qn_or_dist := Qn_or_dist_qfvs;
  qn_and_dist := qn_and_dist_qfvs;
  Qn_and_dist := Qn_and_dist_qfvs;
  Q_lift_qn := Q_lift_qn_qfvs;
}.

#[export] Instance qnmap_qbvs : qnmap qbvs qbvs : Type := {
  qn_sub := qn_sub_qbvs;
  Qn_sub := Qn_sub_qbvs;
  qn_or_dist := qn_or_dist_qbvs;
  Qn_or_dist := Qn_or_dist_qbvs;
  qn_and_dist := qn_and_dist_qbvs;
  Qn_and_dist := Qn_and_dist_qbvs;
  Q_lift_qn := Q_lift_qn_qbvs;
}.

#[export] Instance qnmap_qlocs : qnmap qlocs qlocs : Type := {
  qn_sub := qn_sub_qlocs;
  Qn_sub := Qn_sub_qlocs;
  qn_or_dist := qn_or_dist_qlocs;
  Qn_or_dist := Qn_or_dist_qlocs;
  qn_and_dist := qn_and_dist_qlocs;
  Qn_and_dist := Qn_and_dist_qlocs;
  Q_lift_qn := Q_lift_qn_qlocs;
}.

#[global] Hint Resolve qnmap_qfr qnmap_qfvs qnmap_qbvs qnmap_qlocs : core.
