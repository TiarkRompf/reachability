Require Export PeanoNat.
Require Import Coq.Program.Equality.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import Psatz.
Require Import Coq.Arith.Compare_dec.
Import ListNotations.

Require Import Coq.Logic.ProofIrrelevance.

Require Import vars.
Require Import env.
Require Import tactics.
Require Import NatSets.
Require Import setfacts.

Import NatSet.F.

(* Type qualifiers. *)

Inductive qual : Type :=
| qset : bool(*fresh?*) -> nats(*fv*) -> nats(*bv*) -> nats(*locs*) -> qual
.

Definition qfvs (q: qual) : nats :=
  match q with
  | qset _ fvs _ _ => fvs
  end.

Definition qbvs (q: qual) : nats :=
  match q with
  | qset _ _ bvs _ => bvs
  end.

Definition qlocs (q: qual) : nats :=
  match q with
  | qset _ _ _ ls => ls
  end.

Definition qfresh (q: qual): bool :=
  match q with
  | qset b _ _ _ => b
  end.

Definition qmemb (v : var + loc) (d : qual) : bool  :=
  match d with
  | qset _ vs bs ls => match v with
                    | inl (varF v) => mem v vs
                    | inl (varB v) => mem v bs
                    | inr l        => mem l ls
                    end
  end.

Definition qmem (v : var + loc) (d : qual) : Prop :=
  match d with
  | qset _ vs bs ls => match v with
                    | inl (varF v) => In v vs
                    | inl (varB v) => In v bs
                    | inr l        => In l ls
                    end
  end.

Definition subqual (d1 d2 : qual) : Prop :=
  match d1 , d2 with
  | qset fresh1 fs1 bs1 ls1 , qset fresh2 fs2 bs2 ls2 => (implb fresh1 fresh2 = true) /\ (Subset fs1 fs2) /\ (Subset bs1 bs2) /\ (Subset ls1 ls2)
  end.

Definition subqualb (d1 d2 : qual) : bool :=
  match d1, d2 with
  | qset fresh1 vs1 bs1 ls1, qset fresh2 vs2 bs2 ls2 =>
    fold_right andb true [(implb fresh1 fresh2); (subset vs1 vs2); (subset bs1 bs2); (subset ls1 ls2)]
  end.

Definition eqqual (d1 d2 : qual) : Prop :=
  match d1 , d2 with
  | qset fresh1 fs1 bs1 ls1 , qset fresh2 fs2 bs2 ls2 => (fresh1 = fresh2) /\ (Equal fs1 fs2) /\ (Equal bs1 bs2) /\ (Equal ls1 ls2)
  end.

Definition eqqualb (d1 d2 : qual): bool :=
match d1 , d2 with
  | qset fresh1 fs1 bs1 ls1 , qset fresh2 fs2 bs2 ls2 => (eqb fresh1 fresh2) && (equal fs1 fs2) && (equal bs1 bs2) && (equal ls1 ls2)
end.


(* Semilattice ops on qualifiers *)
Definition qlub (d1 d2 : qual) : qual :=
  match d1, d2 with
  | qset fresh1 vs1 bs1 ls1, qset fresh2 vs2 bs2 ls2 => qset (orb fresh1 fresh2) (union vs1 vs2) (union bs1 bs2) (union ls1 ls2)
  end.


Definition qglb (d1 d2 : qual) : qual :=
  match d1, d2 with
  | qset fresh1 vs1 bs1 ls1, qset fresh2 vs2 bs2 ls2 => qset (andb fresh1 fresh2) (inter vs1 vs2) (inter bs1 bs2) (inter ls1 ls2)
  end.

(* The cancelling union generalized to qualifiers as second arg *)
Definition qqplus (q1 q2 : qual) : qual :=
  match (qfresh q1) with
  | true => (qlub q1 q2)
  | false => q1
  end.
Arguments qqplus _ / _. (* most often we can simplify with the first argument known *)

Definition ldom {A} (Σ : list A) := qset true {}N {}N (dom Σ).
#[global] Hint Unfold ldom : core.

Module QualNotations.
  Declare Scope qualifiers.
  Notation "∅"        := (qset false {}N {}N {}N) (at level 9) : qualifiers.
  Notation "{♦}"      := (qset true {}N {}N {}N) (at level 9) : qualifiers. (* \vardiamondsuit *)
  Notation "∅{ f }"   := (qset f {}N {}N {}N)  (at level 9) : qualifiers.

  Notation "l ∈ₗ d"   := (qmem (inr l) d) (at level 75) : qualifiers.
  Notation "v ∈ᵥ d"   := (qmem (inl v) d) (at level 75) : qualifiers.
  Notation "l ∈?ₗ d"  := (qmemb (inr l) d) (at level 75) : qualifiers.
  Notation "v ∈?ᵥ d"  := (qmemb (inl v) d) (at level 75) : qualifiers.
  Notation "♦∈ d"     := ((qfresh d) = true) (at level 75) : qualifiers.
  Notation "♦∉ d"     := ((qfresh d) = false) (at level 75) : qualifiers.
  Notation "♦∈? d"    := (qfresh d) (at level 75) : qualifiers.

  (* untracked singletons *)
  Notation "$! x "    := (qset false (singleton x) {}N {}N) (at level 0, right associativity) : qualifiers.
  Notation "#! x "    := (qset false {}N (singleton x) {}N) (at level 0, right associativity) : qualifiers.
  Notation "&! l "    := (qset false {}N {}N (singleton l)) (at level 0, right associativity) : qualifiers.

  (* fresh singletons *)
  Notation "$♦ x"     := (qset true (singleton x) {}N {}N) (at level 0, right associativity) : qualifiers.
  Notation "#♦ x "    := (qset true {}N (singleton x) {}N) (at level 0, right associativity) : qualifiers.
  Notation "&♦ l "    := (qset true {}N {}N (singleton l)) (at level 0, right associativity) : qualifiers.

  (* freshness-parametric singletons *)
  Notation "${ f } x" := (qset f (singleton x) {}N {}N) (at level 0, right associativity) : qualifiers.
  Notation "#{ f } x" := (qset f {}N (singleton x) {}N) (at level 0, right associativity) : qualifiers.
  Notation "&{ f } l" := (qset f {}N {}N (singleton l)) (at level 0, right associativity) : qualifiers.

  Notation "d1 ⊑ d2"  := (subqual d1 d2) (at level 75) : qualifiers.
  Notation "d1 ⊑? d2" := (subqualb d1 d2) (at level 75) : qualifiers.

  Notation "d1 ≡ d2"  := (eqqual d1 d2) (at level 75) : qualifiers.
  Notation "d1 ≡? d2" := (eqqualb d1 d2) (at level 75) : qualifiers.

  Notation "d1 ⊔ d2"  := (qlub d1 d2) (at level 70, right associativity) : qualifiers.
  Notation "d1 ⊓ d2"  := (qglb d1 d2) (at level 65, right associativity) : qualifiers.

  (* qualifier growth *)
  Notation "q1 ⋓ q2"  := (qqplus q1 q2) (at level 70, right associativity) : qualifiers.

  (* overlap (modulo saturation) *)
  Notation "q1 ⋒ q2"  := (qlub (qglb q1 q2) (qset true {}N {}N {}N)) (at level 70, right associativity) : qualifiers.
End QualNotations.
Import QualNotations.
Local Open Scope qualifiers.

Require Import Coq.Bool.Bool.

Lemma qfresh_true : forall {s1 s2 s3}, qfresh (qset true s1 s2 s3) = true.
  auto.
Qed.

Lemma qfresh_false : forall {s1 s2 s3}, qfresh (qset false s1 s2 s3) = false.
  auto.
Qed.

Lemma qmem_reflect : forall {v d}, reflect (qmem v d) (qmemb v d).
  intros. destruct d. simpl. destruct v.
  destruct v.
  destruct (mem i t0) eqn:Hmem; try constructor; intuition.
  rewrite <- NatSetFacts.not_mem_iff in Hmem. auto.
  destruct (mem i t1) eqn:Hmem; try constructor; intuition.
  rewrite <- NatSetFacts.not_mem_iff in Hmem. auto.
  destruct (mem l t2) eqn:Hmem; try constructor; intuition.
  rewrite <- NatSetFacts.not_mem_iff in Hmem. auto.
Qed.

Lemma qmem_decidable : forall v d, {qmem v d} + {~ qmem v d}.
  intros. eapply reflect_dec. apply qmem_reflect.
Qed.

Lemma subqual_reflect : forall {d1 d2}, reflect (subqual d1 d2) (subqualb d1 d2).
  intros. destruct (d1 ⊑? d2) eqn:Hsub; try constructor;
  unfold subqual; unfold subqualb in Hsub; destruct d1; destruct d2;
    simpl in Hsub. repeat rewrite andb_true_iff in Hsub.
  intuition; fnsetdec.
  repeat rewrite andb_false_iff in Hsub. intuition.
  rewrite H0 in H2. discriminate.
  apply subset_1 in H. rewrite H in H4. discriminate.
  apply subset_1 in H1. rewrite H1 in H2. discriminate.
  apply subset_1 in H3. rewrite H3 in H4. discriminate.
Qed.

Lemma subqual_decidable : forall d1 d2, {d1 ⊑ d2} + {~ d1 ⊑ d2}.
  intros. eapply reflect_dec. apply subqual_reflect.
Qed.

Lemma subqualb_true_iff : forall {d1 d2}, (d1 ⊑? d2) = true <-> d1 ⊑ d2.
  intuition. erewrite reflect_iff. eauto. apply subqual_reflect.
  erewrite <- reflect_iff; eauto. apply subqual_reflect.
Qed.

Lemma subqualb_false_iff : forall {d1 d2}, (d1 ⊑? d2) = false <-> ~ d1 ⊑ d2.
  intuition. rewrite <- subqualb_true_iff in H0. rewrite H in H0.
  discriminate. destruct (d1 ⊑? d2) eqn:Heq.
  rewrite subqualb_true_iff in Heq. contradiction.
  auto.
Qed.

Lemma eqqual_reflect : forall {d1 d2}, reflect (eqqual d1 d2) (eqqualb d1 d2).
  intros. destruct d1. destruct d2.
  destruct (qset b t0 t1 t2 ≡? qset b0 t3 t4 t5) eqn:Heq; unfold eqqual; unfold eqqualb in *; constructor.
  repeat rewrite andb_true_iff in Heq. intuition. apply eqb_prop. auto.
  repeat rewrite andb_false_iff in Heq. intuition. subst. rewrite eqb_reflx in H2. discriminate.
  apply equal_1 in H. rewrite H in H2. discriminate.
  apply equal_1 in H1. rewrite H1 in H4. discriminate.
  apply equal_1 in H3. rewrite H3 in H2. discriminate.
Qed.

Lemma eqqual_decidable : forall d1 d2, {d1 ≡ d2} + {~ d1 ≡ d2}.
  intros. eapply reflect_dec. apply eqqual_reflect.
Qed.

(* Lifts the extensional equality of the underlying set impl to qualifiers *)
Lemma eq_if_eqqual : forall {d1 d2}, d1 ≡ d2 -> d1 = d2.
  intros. destruct d1. destruct d2. unfold eqqual in H. intuition.
  f_equal; try apply NatSet.eq_if_Equal; auto.
Qed.

Lemma subqual_refl : forall {d1}, d1 ⊑ d1.
  intros. unfold subqual.
  destruct d1; intuition. apply implb_same.
Qed.
#[global] Hint Resolve subqual_refl : core.

Lemma subqual_trans : forall {d1 d2 d3}, d1 ⊑ d2 -> d2 ⊑ d3 -> d1 ⊑ d3.
  intros. unfold subqual in *. destruct d1. destruct d2. destruct d3. intuition; try fnsetdec.
  destr_bool.
Qed.

Lemma subqual_antisymm : forall {d1 d2}, d1 ⊑ d2 -> d2 ⊑ d1 -> d1 ≡ d2.
  intros. unfold eqqual in *. unfold subqual in *. destruct d1. destruct d2. intuition. destr_bool.
Qed.

Lemma eqqual_refl : forall {d}, d ≡ d.
  intros. unfold eqqual. destruct d. intuition.
Qed.
#[global] Hint Resolve eqqual_refl : core.

Lemma eqqual_sym : forall {d1 d2}, d1 ≡ d2 -> d2 ≡ d1.
  unfold eqqual. destruct d1. destruct d2. intuition.
Qed.

Lemma eqqual_trans : forall {d1 d2 d3}, d1 ≡ d2 -> d2 ≡ d3 -> d1 ≡ d3.
  unfold eqqual. destruct d1. destruct d2. destruct d3. intuition; try fnsetdec.
Qed.

Ltac qdec :=
  try apply eq_if_eqqual;
  try unfold qglb in *;
  try unfold qlub in *;
  try unfold eqqual in *;
  try unfold subqual in *;
  intuition;
  try destr_bool;
  try apply NatSet.eq_if_Equal; NatSetDecide.fsetdec.

Lemma qmem_lub_or_commute: forall {vl d1 d2}, qmem vl (d1 ⊔ d2) <-> qmem vl d1 \/ qmem vl d2.
  destruct d1. destruct d2. simpl.
  destruct vl. destruct v; fnsetdec. fnsetdec.
Qed.

Lemma qmem_glb_and_commute: forall {vl d1 d2}, qmem vl (d1 ⊓ d2) <-> qmem vl d1 /\ qmem vl d2.
  destruct d1. destruct d2. simpl.
  destruct vl. destruct v; fnsetdec. fnsetdec.
Qed.

Lemma qlub_upper_l : forall {d1 d2}, d1 ⊑ (d1 ⊔ d2).
  intros. destruct d1. destruct d2. qdec.
Qed.
#[global] Hint Resolve qlub_upper_l : core.

Lemma qqplus_upper_l : forall {d1 d2}, d1 ⊑ (d1 ⋓ d2).
  intros. destruct d1. destruct d2. destruct b; simpl; qdec.
Qed.
#[global] Hint Resolve qqplus_upper_l : core.

Lemma qlub_upper_r : forall {d1 d2}, d1 ⊑ (d2 ⊔ d1).
  intros. destruct d1. destruct d2. qdec.
Qed.
#[global] Hint Resolve qlub_upper_r : core.

Lemma qlub_is_lub : forall {d1 d2 d3}, d1 ⊑ d3 -> d2 ⊑ d3 -> (d1 ⊔ d2) ⊑ d3.
  destruct d1. destruct d2. destruct d3. qdec.
Qed.

Lemma qlub_is_lub_2 : forall {d1 d2 d3}, (d1 ⊔ d2) ⊑ d3 -> d1 ⊑ d3 /\ d2 ⊑ d3.
  intros. destruct d1. destruct d2. destruct d3. qdec.
Qed.

Lemma qglb_lower_l : forall {d1 d2}, (d1 ⊓ d2) ⊑ d1.
  intros. destruct d1. destruct d2. qdec.
Qed.
#[global] Hint Resolve qglb_lower_l : core.

Lemma qglb_lower_r : forall {d1 d2}, (d1 ⊓ d2) ⊑ d2.
  intros. destruct d1. destruct d2. qdec.
Qed.
#[global] Hint Resolve qglb_lower_r : core.

Lemma qglb_is_glb : forall {d1 d2 d3}, d3 ⊑ d1 -> d3 ⊑ d2 -> d3 ⊑ (d1 ⊓ d2).
  destruct d1. destruct d2. destruct d3. qdec.
Qed.

Lemma qglb_is_glb_2 : forall {d1 d2 d3}, d3 ⊑ (d1 ⊓ d2) -> d3 ⊑ d1 /\ d3 ⊑ d2.
  destruct d1. destruct d2. destruct d3. qdec.
Qed.

Lemma qlub_empty_right : forall {d}, (d ⊔ ∅) = d.
  intros. destruct d. qdec.
Qed.
#[global] Hint Resolve qlub_empty_right : core.

Lemma qglb_empty_right : forall {d}, (d ⊓ ∅) = ∅.
  intros. destruct d. qdec.
Qed.
#[global] Hint Resolve qglb_empty_right : core.

Lemma qglb_empty_left : forall {d}, (∅ ⊓ d) = ∅.
  intros. destruct d. qdec.
Qed.
#[global] Hint Resolve qglb_empty_left : core.

Lemma qlub_idem : forall {q}, (q ⊔ q) = q.
  intros. destruct q. qdec.
Qed.

Lemma qlub_assoc : forall {q1 q2 q3},
    (q1 ⊔ (q2 ⊔ q3)) = ((q1 ⊔ q2) ⊔ q3).
Proof.
  intros. destruct q1, q2, q3. simpl. qdec.
Qed.

Lemma qglb_qlub_dist : forall {d1 d2 d3}, (d1 ⊓ (d2 ⊔ d3)) = ((d1 ⊓ d2) ⊔ (d1 ⊓ d3)).
  destruct d1; destruct d2; destruct d3. qdec.
Qed.

Lemma qglb_commute : forall {d1 d2}, d1 ⊓ d2 = d2 ⊓ d1.
  intros. destruct d1; destruct d2. qdec.
Qed.

Lemma qlub_commute : forall {d1 d2}, (d1 ⊔ d2) = (d2 ⊔ d1).
  intros. destruct d1; destruct d2. qdec.
Qed.

Lemma qlub_empty_left : forall {d}, (∅ ⊔ d) = d.
  intros. rewrite qlub_commute. auto.
Qed.
#[global] Hint Resolve qlub_empty_left : core.

Lemma qqplus_qbot_right_neutral : forall {d}, (d ⋓ ∅) = d.
  destruct d. simpl. destruct b; qdec.
Qed.
#[global] Hint Resolve qqplus_qbot_right_neutral : core.

Lemma qqplus_qbot_left_cancel : forall {d}, (∅ ⋓ d) = ∅.
  destruct d. simpl. destruct b; qdec.
Qed.
#[global] Hint Resolve qqplus_qbot_left_cancel : core.

Lemma qqplus_gt : forall {q1 q2}, q1 ⊑ (q1 ⋓ q2).
  intros. destruct q1. simpl. destruct q2. destruct b; qdec.
Qed.
#[global] Hint Resolve qqplus_gt : core.

Lemma subqual_qlub : forall {d1 d2 d}, d1 ⊑ d2 -> d1 ⊔ d ⊑ d2 ⊔ d.
  destruct d1. destruct d2. destruct d. qdec.
Qed.
#[global] Hint Resolve subqual_qlub : core.

Lemma subqual_qglb : forall {d1 d2 d}, d1 ⊑ d2 -> d ⊓ d1 ⊑ d ⊓ d2.
  destruct d1. destruct d2. destruct d. qdec.
Qed.
#[global] Hint Resolve subqual_qglb : core.

Lemma subqual_qglb_r : forall {d1 d2 d}, d1 ⊑ d2 -> d1 ⊓ d ⊑ d2 ⊓ d.
  destruct d1. destruct d2. destruct d. qdec.
Qed.
#[global] Hint Resolve subqual_qglb_r : core.

Lemma qglb_mono_lr : forall {d1 d1' d2 d2'}, d1 ⊑ d1' -> d2 ⊑ d2' -> d1 ⊓ d2 ⊑ d1' ⊓ d2'.
  intros. destruct d1. destruct d1'. destruct d2. destruct d2'. qdec.
Qed.
#[global] Hint Resolve qglb_mono_lr : core.

Lemma empty_smallest : forall {d}, ∅ ⊑ d.
  destruct d. qdec.
Qed.
#[global] Hint Resolve empty_smallest : core.

Lemma subqual_qqplus : forall {d1 d2 d}, d1 ⊑ d2 -> d1 ⋓ d ⊑ d2 ⋓ d.
  intros. destruct d1. destruct d2. destruct d. simpl. destr_bool; qdec.
Qed.
#[global] Hint Resolve subqual_qqplus : core.

Lemma subqual_qlub_l : forall {d1 d2 d}, d1 ⊑ d2 -> d ⊔ d1 ⊑ d ⊔ d2.
  destruct d1. destruct d2. destruct d. qdec.
Qed.
#[global] Hint Resolve subqual_qlub_l : core.

Lemma subqual_qqplus_l : forall {d1 d2 d}, d1 ⊑ d2 -> d ⋓ d1 ⊑ d ⋓ d2.
  intros. destruct d1. destruct d2. destruct d. simpl. destr_bool; qdec.
Qed.
#[global] Hint Resolve subqual_qqplus_l : core.

Lemma empty_superqual : forall {df}, df ⊑ ∅ -> df = ∅.
  intros. destruct df. simpl in *. intuition. qdec.
Qed.

Lemma qlub_qglb_dist_r:
  forall {d1 d2 d3 : qual}, ((d2 ⊓ d3) ⊔ d1) = ((d2 ⊔ d1) ⊓ (d3 ⊔ d1)).
  destruct d1. destruct d2. destruct d3. qdec.
Qed.

Lemma qlub_qglb_dist_l:
  forall {d1 d2 d3 : qual}, (d1 ⊔ (d2 ⊓ d3)) = ((d1 ⊔ d2) ⊓ (d1 ⊔ d3)).
  destruct d1. destruct d2. destruct d3. qdec.
Qed.

Lemma qglb_qlub_dist_r:
  forall {d1 d2 d3 : qual}, ((d2 ⊔ d3) ⊓ d1) = ((d2 ⊓ d1) ⊔ (d3 ⊓ d1)).
  destruct d1. destruct d2. destruct d3. qdec.
Qed.

Lemma qglb_qlub_dist_l:
  forall {d1 d2 d3 : qual}, (d1 ⊓ (d2 ⊔ d3)) = ((d1 ⊓ d2) ⊔ (d1 ⊓ d3)).
  destruct d1. destruct d2. destruct d3. qdec.
Qed.

Lemma qglb_qqplus_dist_l : forall {d1 d2 d3}, d1 ⊓ d3 ⊑ ∅ -> (d1 ⊓ (d2 ⋓ d3)) = ((d1 ⊓ d2) ⋓ (d1 ⊓ d3)).
  intros. destruct d1 as [f1 fvs1 bvs1 ls1]; destruct d2 as [f2 fvs2 bvs2 ls2]; destruct d3 as [f3 fvs3 bvs3 ls3].
  destr_bool; qdec.
Qed.

Lemma qglb_qqplus_dist_r : forall {d1 d2 d3}, d3 ⊓ d1 ⊑ ∅ -> ((d2 ⋓ d3) ⊓ d1) = ((d2 ⊓ d1) ⋓ (d3 ⊓ d1)).
  intros. destruct d1 as [f1 fvs1 bvs1 ls1]; destruct d2 as [f2 fvs2 bvs2 ls2]; destruct d3 as [f3 fvs3 bvs3 ls3].
  destr_bool; qdec.
Qed.

Lemma empty_neutral_set : forall {fr a b c}, ((qset fr a b c) ⊔ ∅) = (qset fr a b c).
Proof. intros. simpl. repeat rewrite empty_union_right. auto. destr_bool. Qed.

Lemma qlub_swallow_l : forall {q1 q2}, q1 ⊑ q2 -> (q1 ⊔ q2) = q2.
  intros. destruct q1. destruct q2. qdec.
Qed.

Lemma qlub_swallow_r : forall {q1 q2}, q1 ⊑ q2 -> (q2 ⊔ q1) = q2.
  intros. destruct q1. destruct q2. qdec.
Qed.

Lemma qlub_bound : forall {q1 q2 q3}, q1 ⊑ q3 -> q2 ⊑ q3 -> q1 ⊔ q2 ⊑ q3.
  intros. destruct q1. destruct q2. destruct q3. qdec.
Qed.

Lemma qqplus_bound : forall {q1 q2 q3}, q1 ⊑ q3 -> q2 ⊑ q3 -> q1 ⋓ q2 ⊑ q3.
  intros. destruct q1. destruct q2. destruct q3. simpl. destruct b; qdec.
Qed.

Lemma qglb_bound : forall {q1 q2 q3}, q3 ⊑ q1 -> q3 ⊑ q2 -> q3 ⊑ q1 ⊓ q2.
  intros. destruct q1. destruct q2. destruct q3. qdec.
Qed.

Lemma subqual_bound : forall {q1 q2},
    q1 ⊑ q2 ->
    (bound (qfvs q1)) <= (bound (qfvs q2))
    /\ (bound (qbvs q1)) <= (bound (qbvs q2))
    /\ (bound (qlocs q1)) <= (bound (qlocs q2)).
  intros. destruct q1. destruct q2. simpl in *. intuition; apply subset_bound'; auto.
Qed.

Lemma subqual_just_loc_bound : forall {l q},
    &! l ⊑ q -> l < bound (qlocs q).
  intros. apply subqual_bound in H. intuition. simpl in *.
  rewrite bound_singleton in H2. lia.
Qed.

Lemma subqual_just_fv_bound : forall {x q},
    $! x ⊑ q -> x < bound (qfvs q).
  intros. apply subqual_bound in H. intuition. simpl in *.
  rewrite bound_singleton in H0. lia.
Qed.

Lemma qset_empty_inv : forall {fr a b c}, qset fr a b c = ∅ <-> fr = false /\ a [=] {}N /\ b [=] {}N /\ c [=] {}N.
  intros. split. intros.
  inversion H. intuition.
  intros. intuition. f_equal; try fnsetdec.
Qed.

Lemma just_fv_mem_iff : forall {x y fr}, $x ∈ᵥ ${ fr } y <-> x = y.
  intros. simpl. rewrite NatSetFacts.singleton_iff. intuition.
Qed.

Lemma not_fresh_sub : forall {q2}, ♦∉ q2 -> forall {q1}, q1 ⊑ q2 -> ♦∉ q1.
  intros. destruct q1. destruct q2. qdec.
Qed.

Lemma not_fresh_qqplus : forall {d1 d'}, ♦∉ d1 -> (d1 ⋓ d') = d1.
  intros. destruct d1. destruct b. simpl in H. discriminate.
  simpl. auto.
Qed.
#[global] Hint Resolve not_fresh_qqplus : core.

Lemma fresh_qlub_r : forall {d}, ♦∈ d ⊔ {♦}.
  intros. destruct d. simpl. destr_bool.
Qed.
#[global] Hint Resolve fresh_qlub_r : core.

Lemma fresh_qlub_l : forall {d}, ♦∈ {♦} ⊔ d.
  intros. destruct d. simpl. destr_bool.
Qed.
#[global] Hint Resolve fresh_qlub_l : core.

Lemma not_fresh_fresh_false : forall {d}, (♦∉ (d ⊔ {♦})) -> False.
  intros. destruct d. destruct b; simpl in H; discriminate.
Qed.

Lemma qlub_empty_fresh : forall {fr}, (∅{ fr} ⊔ {♦}) = {♦}.
  intros. qdec.
Qed.
#[global] Hint Resolve qlub_empty_fresh : core.

Lemma qlub_set_not_fresh : forall {d1}, (qset false (qfvs d1) (qbvs d1) (qlocs d1)) ⊑ d1.
  intros. destruct d1. qdec.
Qed.
#[global] Hint Resolve qlub_set_not_fresh : core.

Lemma qqplus_fresh : forall {d d'}, ♦∈ d -> (d ⋓ d') = (d ⊔ d').
  intros. destruct d. destruct d'. simpl in H. subst. qdec.
Qed.

Lemma qfresh_subset : forall {q}, ♦∈ q <-> {♦} ⊑ q.
  intros. destruct q. simpl. intuition.
Qed.

Lemma not_fresh_qlub : forall {q1 q2}, ♦∉ q1 -> ♦∉ q2 -> ♦∉ (q1 ⊔ q2).
  intros. destruct q1. destruct q2. qdec.
Qed.
#[global] Hint Resolve not_fresh_qlub : core.

Lemma not_fresh_qlub' : forall {q1 q2}, ♦∉ (q1 ⊔ q2) -> ♦∉ q1 /\ ♦∉ q2.
  intros. destruct q1. destruct q2. qdec.
Qed.

Lemma not_fresh_qglb : forall {q1 q2}, ♦∉ q1 -> ♦∉ q2 -> ♦∉ (q1 ⊓ q2).
  intros. destruct q1. destruct q2. qdec.
Qed.
#[global] Hint Resolve not_fresh_qglb : core.

Lemma not_fresh_qglb' : forall {q1 q2}, ♦∉ (q1 ⊓ q2) -> ♦∉ q1 \/ ♦∉ q2.
  intros. destruct q1. destruct q2. qdec.
Qed.