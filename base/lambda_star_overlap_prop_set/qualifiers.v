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
Require Import tactics.

Definition qual : Type := (nats(*fv*) * nats(*bv*) * nats(*locs*)).
Definition Qual : Type := (Nats * Nats * Nats).

Definition qfvs   {A B C} (q : A * B * C): A := fst (fst q).
Definition qbvs   {A B C} (q : A * B * C): B := snd (fst q).
Definition qlocs  {A B C} (q : A * B * C): C := snd q.

Definition qmemb (v : var + loc) (d : qual) : bool  :=
  match v with
  | inl (varF v) => qfvs d v
  | inl (varB v) => qbvs d v
  | inr l        => qlocs d l
  end.

Definition qmem (v : var + loc) (d : qual) : Prop :=
  match v with
  | inl (varF v) => N_lift (qfvs d) v
  | inl (varB v) => N_lift (qbvs d) v
  | inr l        => N_lift (qlocs d) l
  end.

Ltac qual_destruct a := destruct a as [[?fvs ?bvs] ?lcs].

Definition qdom {A} (Σ : list A): qual := (n_empty, n_empty, (n_dom Σ)).

Definition subq (d1 d2 : qual) : Prop :=
  (n_sub (qfvs d1) (qfvs d2)) /\ (n_sub (qbvs d1) (qbvs d2)) /\ (n_sub (qlocs d1) (qlocs d2)).
Definition qor (d1 d2 : qual) : qual := (n_or  (qfvs d1) (qfvs d2), n_or  (qbvs d1) (qbvs d2), n_or  (qlocs d1) (qlocs d2)).
Definition qand (d1 d2 : qual) : qual := (n_and (qfvs d1) (qfvs d2), n_and (qbvs d1) (qbvs d2), n_and (qlocs d1) (qlocs d2)).
Definition qdiff (d1 d2 : qual) : qual := (n_diff (qfvs d1) (qfvs d2), n_diff (qbvs d1) (qbvs d2), n_diff (qlocs d1) (qlocs d2)).

(* The cancelling union generalized to qualifiers as second arg *)
Definition qqplus (q1 q2 : qual) : qual := qor q1 q2.
Arguments qqplus _ / _. (* most often we can simplify with the first argument known *)

(* Propositional versions *)
Definition Subq (d1 d2 : Qual) : Prop :=
  (N_sub (qfvs d1) (qfvs d2)) /\ (N_sub (qbvs d1) (qbvs d2)) /\ (N_sub (qlocs d1) (qlocs d2)).
Definition Qor (d1 d2 : Qual) : Qual := (N_or  (qfvs d1) (qfvs d2), N_or  (qbvs d1) (qbvs d2), N_or  (qlocs d1) (qlocs d2)).
Definition Qand (d1 d2 : Qual) : Qual := (N_and (qfvs d1) (qfvs d2), N_and (qbvs d1) (qbvs d2), N_and (qlocs d1) (qlocs d2)).
Definition Qqplus (d1 d2 : Qual) : Qual := Qor d1 d2.
Definition Qdiff (d1 d2 : Qual) : Qual := (N_diff (qfvs d1) (qfvs d2), N_diff (qbvs d1) (qbvs d2), N_diff (qlocs d1) (qlocs d2)).
Definition Qdom {A} (Σ : list A): Qual := (N_empty, N_empty, (N_dom Σ)).

Definition q_empty: qual := (n_empty, n_empty, n_empty).
Definition Q_empty: Qual := (N_empty, N_empty, N_empty).

Definition Q_lift (q: qual): Qual := (N_lift (qfvs q), N_lift (qbvs q), N_lift (qlocs q)).

Definition just_fv (x : id) : qual := (n_one x, n_empty, n_empty).
Definition just_bv (x : id) : qual := (n_empty, n_one x, n_empty).
Definition just_loc (x : id) : qual := (n_empty, n_empty, n_one x).

Definition open_qual (k : nat) (d' : qual) (d : qual) : qual :=
  if (qbvs d k) then
  qor (qfvs d, n_diff (qbvs d) (n_one k), qlocs d) d'
  else d
.

Definition open_Qual (k : nat) (d' : Qual) (d : Qual) : Qual :=
  (
  fun x => (qbvs d k -> (N_or (qfvs d) (qfvs d') x)) /\ (~(qbvs d k) -> qfvs d x),
  fun x => (qbvs d k -> (N_or (N_diff (qbvs d) (N_one k)) (qbvs d') x)) /\ (~(qbvs d k) -> qbvs d x),
  fun x => (qbvs d k -> (N_or (qlocs d) (qlocs d') x)) /\ (~(qbvs d k) -> qlocs d x)
  )
.

Definition splice_qual (n : nat) (d : qual) : qual :=
  match d with
  | (vs,bs,ls) => ((n_splice n vs),bs,ls)
  end.

Definition splice_Qual (n : nat) (d : Qual) : Qual :=
  match d with
  | (vs,bs,ls) => ((N_splice n vs),bs,ls)
  end.

Definition unsplice_qual (n : nat) (d : qual) : qual :=
  match d with
  | (vs,bs,ls) => ((n_unsplice n vs),bs,ls)
  end.

Definition unsplice_Qual (n : nat) (d : Qual) : Qual :=
  match d with
  | (vs,bs,ls) => ((N_unsplice n vs),bs,ls)
  end.

Definition subst_qual (q : qual) (v : nat) (q' : qual) : qual :=
  if qfvs q v
  then qor (n_unsplice 0 (n_diff (qfvs q) (n_one v)), qbvs q, qlocs q) q'
  else (n_unsplice 0 (qfvs q), qbvs q, qlocs q)
.

Definition subst_Qual (q : Qual) (v : nat) (q' : Qual) : Qual :=
  (
  fun x => (qfvs q v -> (N_or (N_unsplice 0 (N_diff (qfvs q) (N_one v))) (qfvs q') x)) /\ (~(qfvs q v) -> N_unsplice 0 (qfvs q) x),
  fun x => (qfvs q v -> (N_or (qbvs q) (qbvs q') x)) /\ (~(qfvs q v) -> qbvs q x),
  fun x => (qfvs q v -> (N_or (qlocs q) (qlocs q') x)) /\ (~(qfvs q v) -> qlocs q x)
  )
.

Definition closed_qual b f l q :=
  closed_nats f (qfvs q) /\ closed_nats b (qbvs q) /\ closed_nats l (qlocs q).

Definition closed_Qual b f l q :=
  closed_Nats f (qfvs q) /\ closed_Nats b (qbvs q) /\ closed_Nats l (qlocs q).

Definition qstp (tl sl : nat)  (d1 : qual) (d2 : qual) :=
    Subq (Q_lift d1) (Q_lift d2) /\
    closed_Qual 0 tl sl (Q_lift d2).

Definition Qstp (tl sl : nat) (d1 : Qual) (d2 : Qual) :=
    Subq d1 d2 /\
    closed_Qual 0 tl sl d2.

Ltac unfold_q := repeat (unfold qstp, open_qual, closed_qual, splice_qual, subst_qual, subq, qdom, q_empty, qqplus, qand, qor, qdiff, qfvs, qbvs, qlocs in *; simpl in *).
Ltac unfold_Q := repeat (unfold Q_lift, Qstp, open_Qual, closed_Qual, splice_Qual, subst_Qual, Subq, Qdom, Q_empty, Qqplus, Qand, Qor, Qdiff, qfvs, qbvs, qlocs in *; simpl in *).
Ltac Qcrush := unfold_Q; nlift; unfold_N; repeat f_equal; try apply functional_extensionality; intros; try apply propositional_extensionality; intuition.

#[global] Hint Unfold qdom : core.
#[global] Hint Unfold qfvs : core.
#[global] Hint Unfold qbvs : core.
#[global] Hint Unfold qlocs : core.
#[global] Hint Unfold subq : core.
#[global] Hint Unfold just_fv : core.
#[global] Hint Unfold just_bv : core.
#[global] Hint Unfold just_loc : core.
#[global] Hint Unfold Qdom : core.
#[global] Hint Unfold Subq : core.
#[global] Hint Unfold q_empty : core.
#[global] Hint Unfold Q_empty : core.

Module QualNotations.
  Declare Scope qualifiers.
  Notation "∅"        := q_empty (at level 9) : qualifiers.

  Notation "l ∈ₗ d"   := (qmem (inr l) d) (at level 75) : qualifiers.
  Notation "v ∈ᵥ d"   := (qmem (inl v) d) (at level 75) : qualifiers.
  Notation "l ∈?ₗ d"  := (qmemb (inr l) d) (at level 75) : qualifiers.
  Notation "v ∈?ᵥ d"  := (qmemb (inl v) d) (at level 75) : qualifiers.

  (* Notation "♦∈ d"     := ((qfresh d) = true) (at level 75) : qualifiers. *)
  (* Notation "♦∉ d"     := ((qfresh d) = false) (at level 75) : qualifiers. *)
  (* Notation "♦∈? d"    := (qfresh d) (at level 75) : qualifiers. *)

  (* untracked n_ones *)
  Notation "$$ x "    := (just_fv x) (at level 0, right associativity) : qualifiers.
  Notation "## x "    := (just_bv x) (at level 0, right associativity) : qualifiers.
  Notation "&& l "    := (just_loc l) (at level 0, right associativity) : qualifiers.

  Notation "d1 ⊑ d2"  := (subq d1 d2) (at level 75) : qualifiers.
  (* Notation "d1 ⊑? d2" := (subqb d1 d2) (at level 75) : qualifiers. *)
  (* TODO: Should this accept lifted qualifiers or unlifted? <2023-05-23, David Deng> *)
  Notation "d1 ⊑↑ d2" := (Subq (Q_lift d1) (Q_lift d2)) (at level 75) : qualifiers.

  (* Notation "d1 ≡ d2"  := (eqqual d1 d2) (at level 75) : qualifiers. *)
  (* Notation "d1 ≡? d2" := (eqqualb d1 d2) (at level 75) : qualifiers. *)

  Notation "d1 ⊔ d2"  := (qor d1 d2) (at level 70, right associativity) : qualifiers.
  Notation "d1 ⊓ d2"  := (qand d1 d2) (at level 65, right associativity) : qualifiers.

  (* qualifier growth *)
  Notation "q1 ⋓ q2"  := (qqplus q1 q2) (at level 70, right associativity) : qualifiers.
  Notation "q1 ⊕ q2"  := (qqplus q1 (just_fv q2)) (at level 70, right associativity) : qualifiers.

  (* overlap (modulo saturation) *)
  (* Notation "q1 ⋒ q2"  := (qor (qand q1 q2) (n_empty, n_empty, n_empty)) (at level 70, right associativity) : qualifiers. *)
End QualNotations.
Import QualNotations.
Local Open Scope qualifiers.

Require Import Coq.Bool.Bool.

Lemma qmem_reflect : forall {v d}, reflect (qmem v d) (qmemb v d).
  intros. destruct d. simpl. destruct v;
  try destruct v; unfold N_lift; apply iff_reflect; intuition.
Qed.

Lemma qmem_decidable : forall v d, {qmem v d} + {~ qmem v d}.
  intros. eapply reflect_dec. apply qmem_reflect.
Qed.

Lemma Q_lift_empty:
    Q_lift (q_empty) = Q_empty.
Proof.
  intros. unfold Q_lift. unfold_Q. unfold N_lift. repeat f_equal; simpl.
  all : eapply functional_extensionality; intros;
  eapply propositional_extensionality; intuition.
Qed.

Lemma Q_lift_and: forall a b,
    Q_lift (a ⊓ b) = Qand (Q_lift a) (Q_lift b).
Proof.
  intros. unfold Q_lift. unfold Qand. repeat f_equal. simpl. simpl.
  all : unfold_Q; simpl; eapply functional_extensionality; intros;
  rewrite N_lift_and; intuition.
Qed.

Lemma Q_lift_or: forall a b,
    Q_lift (a ⊔ b) = Qor (Q_lift a) (Q_lift b).
Proof.
  intros. unfold Q_lift. unfold Qor. repeat f_equal. simpl.
  all : unfold_Q; simpl; eapply functional_extensionality; intros;
  rewrite N_lift_or; intuition.
Qed.

Lemma Q_lift_diff: forall a b,
    Q_lift (qdiff a b) = Qdiff (Q_lift a) (Q_lift b).
Proof.
  intros. unfold Q_lift. unfold Qdiff. repeat f_equal.
  all : unfold_Q; simpl; eapply functional_extensionality; intros; rewrite N_lift_diff; intuition.
Qed.

Lemma Q_lift_dist : forall fvs bvs locs, Q_lift (fvs, bvs, locs) = (N_lift fvs, N_lift bvs, N_lift locs).
  intros. unfold Q_lift. intuition.
Qed.

Lemma Q_lift_qdom : forall {A} (H : list A), Q_lift (qdom H) = Qdom H.
  intros. unfold qdom. unfold Qdom. rewrite Q_lift_dist. repeat rewrite N_lift_empty.
  rewrite N_lift_dom. repeat f_equal; intuition.
Qed.

Lemma Q_lift_open_qual: forall a b k,
    Q_lift (open_qual k a b) = open_Qual k (Q_lift a) (Q_lift b).
Proof.
  intros. qual_destruct a. qual_destruct b. unfold Q_lift, open_Qual, open_qual. destruct (qbvs (fvs0, bvs0, lcs0) k) eqn:Eq.
  - assert (N_lift bvs0 k). { unfold N_lift. auto. } unfold_Q. nlift. repeat f_equal; eapply functional_extensionality; intros; apply propositional_extensionality; intuition.
  - assert (~N_lift bvs0 k). { unfold_q. unfold N_lift. rewrite Eq. auto. } repeat f_equal; eapply functional_extensionality; intros; apply propositional_extensionality; intuition.
Qed.

Lemma Q_lift_splice_qual: forall q k,
    Q_lift (splice_qual k q) = splice_Qual k (Q_lift q).
Proof.
  intros. qual_destruct q. unfold Q_lift. unfold_Q. unfold N_lift. unfold_N. unfold_n. repeat f_equal; eapply functional_extensionality; intros. apply propositional_extensionality; bdestruct (x =? k); bdestruct (x <? k); intuition.
Qed.

Lemma Q_lift_unsplice_qual: forall q k,
    Q_lift (unsplice_qual k q) = unsplice_Qual k (Q_lift q).
Proof.
  intros. qual_destruct q. unfold Q_lift. unfold_Q. unfold N_lift. unfold_N. unfold_n. repeat f_equal; eapply functional_extensionality; intros. apply propositional_extensionality; bdestruct (x =? k); bdestruct (x <? k); intuition.
Qed.

Lemma Q_lift_subst_qual: forall q v q',
    Q_lift (subst_qual q v q') = subst_Qual (Q_lift q) v (Q_lift q').
Proof.
  intros. qual_destruct q. qual_destruct q'. unfold Q_lift, subst_Qual, subst_qual. destruct (qfvs (fvs, bvs, lcs) v) eqn:Eq.
  - assert (N_lift fvs v). { unfold N_lift. auto. } unfold_Q. nlift. repeat f_equal; eapply functional_extensionality; intros; apply propositional_extensionality; intuition.
  - assert (~N_lift fvs v). { unfold_q. unfold N_lift. rewrite Eq. auto. } unfold_Q. nlift. repeat f_equal; eapply functional_extensionality; intros; apply propositional_extensionality; intuition.
Qed.

Lemma Q_lift_qstp: forall a b tl sl,
  Qstp tl sl (Q_lift a) (Q_lift b) -> qstp tl sl a b. intuition.
Qed.
Lemma Q_lift_qstp': forall a b tl sl,
  qstp tl sl a b -> Qstp tl sl (Q_lift a) (Q_lift b). intuition.
Qed.

Lemma Q_lift_closed : forall b f l q,
  closed_Qual b f l (Q_lift q) -> closed_qual b f l q. intuition.
Qed.
Lemma Q_lift_closed' : forall b f l q,
  closed_qual b f l q -> closed_Qual b f l (Q_lift q). intuition.
Qed.

Lemma Q_lift_subq : forall a b,
  Subq (Q_lift a) (Q_lift b) -> subq a b.
  intros. unfold_Q. unfold_q. intuition.
Qed.
Lemma Q_lift_subq' : forall a b,
  subq a b -> Subq (Q_lift a) (Q_lift b).
  intros. unfold_Q. unfold_q. intuition.
Qed.

Lemma Q_lift_eq : forall (p q : qual),
  (Q_lift p = Q_lift q) -> (p = q).
Proof.
  intros. qual_destruct q. qual_destruct p. unfold Q_lift in *. unfold_Q. inversion H. repeat f_equal; apply N_lift_eq; try rewrite H1; try rewrite H2; try rewrite H3; intuition.
Qed.
Lemma Q_lift_eq' : forall (p q : qual),
  (p = q) -> (Q_lift p = Q_lift q).
Proof.
  intros. unfold Q_lift. rewrite H. intuition.
Qed.

(**********
*  subq  *
**********)


Lemma subq_refl : forall {d1}, d1 ⊑ d1.
  intros. unfold_q. unfold_n. intuition.
Qed.
#[global] Hint Resolve subq_refl : core.

Lemma Subq_refl : forall {d1}, d1 ⊑↑ d1.
  intros. unfold_Q. unfold_N. intuition.
Qed.
#[global] Hint Resolve Subq_refl : core.

Lemma subq_trans : forall {d1 d2 d3}, d1 ⊑ d2 -> d2 ⊑ d3 -> d1 ⊑ d3.
  intros. unfold_q. unfold_n. intuition.
Qed.
#[global] Hint Resolve subq_trans : core.

Lemma Subq_trans : forall {d1 d2 d3}, d1 ⊑↑ d2 -> d2 ⊑↑ d3 -> d1 ⊑↑ d3.
  intros. unfold_Q. unfold_N. intuition.
Qed.
#[global] Hint Resolve Subq_trans : core.

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
Lemma subq_qor_gt: forall {q1 q2 : qual}, q1 ⊑ q1 ⊔ q2.
intros. apply Q_lift_subq. apply Subq_qor_gt.
Qed.

Lemma Subq_qor_bound: forall {q1 q2 q3}, q1 ⊑↑ q3 -> q2 ⊑↑ q3 -> q1 ⊔ q2 ⊑↑ q3.
intros. Qcrush.
Qed.

Lemma subq_qor_bound: forall {q1 q2 q3}, q1 ⊑ q3 -> q2 ⊑ q3 -> q1 ⊔ q2 ⊑ q3.
intros. apply Q_lift_subq. apply Q_lift_subq' in H, H0. apply Subq_qor_bound; auto.
Qed.

Lemma Subq_splice_dist : forall {i du df},
    Subq (splice_Qual i (Q_lift du)) (splice_Qual i (Q_lift df)) <-> Subq (Q_lift du) (Q_lift df).
Proof.
  intros. intuition.
  - qual_destruct du. qual_destruct df. Qcrush. 
    bdestruct (x =? i); bdestruct (x <? i); intuition.
    + specialize (H0 (S x)). intuition.
    + specialize (H0 x). intuition.
    + specialize (H0 (S x)). intuition.
  - qual_destruct du. qual_destruct df. Qcrush. 
Qed.

Lemma subq_splice_dist : forall {i du df},
    splice_qual i du ⊑ splice_qual i df <-> du ⊑ df.
Proof.
  intros. intuition.
  - apply Q_lift_subq. apply Q_lift_subq' in H. repeat rewrite Q_lift_splice_qual in H. eapply Subq_splice_dist; eauto. 
  - apply Q_lift_subq. apply Q_lift_subq' in H. repeat rewrite Q_lift_splice_qual. eapply Subq_splice_dist; eauto.
Qed.

(**********
*  qand  *
**********)

Lemma qand_commute : forall {d1 d2}, d1 ⊓ d2 = d2 ⊓ d1.
intros. apply Q_lift_eq. unfold_q. unfold_Q. nlift. unfold_N. repeat f_equal; apply functional_extensionality; intros; apply propositional_extensionality; intuition.
Qed.

Lemma qand_qlub_dist_r:
  forall {d1 d2 d3 : qual}, ((d2 ⊔ d3) ⊓ d1) = ((d2 ⊓ d1) ⊔ (d3 ⊓ d1)).
intros. unfold_q. apply Q_lift_eq. unfold_Q. nlift. unfold_N. repeat f_equal; apply functional_extensionality; intros; apply propositional_extensionality; intuition.
Qed.

Lemma qand_qlub_dist_l:
  forall {d1 d2 d3 : qual}, (d1 ⊓ (d2 ⊔ d3)) = ((d1 ⊓ d2) ⊔ (d1 ⊓ d3)).
intros. unfold_q. apply Q_lift_eq. unfold_Q. nlift. unfold_N. repeat f_equal; apply functional_extensionality; intros; apply propositional_extensionality; intuition.
Qed.

Lemma qand_fresh_r : forall {d1 df f l},
    closed_Qual 0 f l (Q_lift d1) -> closed_Qual 0 f l (Q_lift df) -> forall {l'}, l <= l' -> d1 ⊓ df = d1 ⊓ (df ⊔ (just_loc l')).
intros. qual_destruct df. qual_destruct d1. apply Q_lift_eq. unfold_q. unfold_Q; nlift; unfold_N; repeat f_equal; apply functional_extensionality; intros; apply propositional_extensionality; intuition. subst; exfalso; eauto.
Qed.

Lemma qand_fresh_l : forall {d1 df f l},
    closed_qual 0 f l d1 -> closed_qual 0 f l df -> forall {l'}, l <= l' -> d1 ⊓ df = (d1 ⊔ just_loc l') ⊓ df.
  intros. rewrite qand_commute. erewrite qand_fresh_r; eauto.
  rewrite qand_commute. auto.
Qed.

Lemma qand_Sub_l : forall {q1 q2}, q2 ⊓ q1 ⊑↑ q2.
intros. unfold_Q. nlift. unfold_N. intuition.
Qed.

Lemma qand_sub_l : forall {q1 q2}, q2 ⊓ q1 ⊑ q2.
intros. apply Q_lift_subq. apply qand_Sub_l.
Qed.

Lemma qand_Sub_r : forall {q1 q2}, q2 ⊓ q1 ⊑↑ q1.
intros. unfold_Q. nlift. unfold_N. intuition.
Qed.

Lemma qand_sub_r : forall {q1 q2}, q2 ⊓ q1 ⊑ q1.
intros. apply Q_lift_subq. apply qand_Sub_r.
Qed.

(*********
*  qor  *
*********)

Lemma qand_qor_dist_l : forall {d1 d2 d3 : qual}, (d1 ⊓ (d2 ⊔ d3)) = ((d1 ⊓ d2) ⊔ (d1 ⊓ d3)).
intros. apply Q_lift_eq. unfold_q. unfold_Q. nlift. unfold_N. repeat f_equal; apply functional_extensionality; intros; apply propositional_extensionality; intuition.
Qed.

Lemma qand_qor_dist_r : forall {d1 d2 d3 : qual}, ((d1 ⊔ d2) ⊓ d3) = ((d1 ⊓ d3) ⊔ (d2 ⊓ d3)).
intros. apply Q_lift_eq. unfold_q. unfold_Q. nlift. unfold_N. repeat f_equal; apply functional_extensionality; intros; apply propositional_extensionality; intuition.
Qed.

Lemma qor_empty_right : forall {d}, (d ⊔ q_empty) = d.
intros. apply Q_lift_eq. rewrite Q_lift_or. unfold_Q. repeat f_equal; nlift; unfold_N; apply functional_extensionality; intros; apply propositional_extensionality; intuition.
Qed.

Lemma Qor_bound : forall q1 q2 q3 : qual, q1 ⊑↑ q3 -> q2 ⊑↑ q3 -> q1 ⊔ q2 ⊑↑ q3.
intros. unfold_Q; nlift; unfold_N; intuition.
Qed.
Lemma qor_bound : forall q1 q2 q3 : qual, q1 ⊑ q3 -> q2 ⊑ q3 -> q1 ⊔ q2 ⊑ q3.
intros. apply Q_lift_subq. apply Qor_bound; apply Q_lift_subq'; auto.
Qed.

Lemma Subq_qor : forall {d1 d2}, d1 ⊑↑ d2 -> forall {d}, d1 ⊔ d ⊑↑ d2 ⊔ d.
intros. unfold_Q. nlift. unfold_N. intuition.
Qed.
Lemma subq_qor : forall {d1 d2}, d1 ⊑ d2 -> forall {d}, d1 ⊔ d ⊑ d2 ⊔ d.
intros. apply Q_lift_subq. apply Subq_qor. apply Q_lift_subq'. auto.
Qed.

(*****************
*  closed_qual  *
*****************)

Lemma closed_Qual_monotone : forall {f b l d},
    closed_Qual b f l d ->
    forall {b' f' l'},
      b <= b' ->
      f <= f' ->
      l <= l' ->
      closed_Qual b' f' l' d.
Proof.
  intros. repeat split; eapply closed_Nats_mono; eauto; eapply H.
Qed.
#[global] Hint Resolve closed_Qual_monotone : core.

Lemma closed_qual_open_id : forall {d b f l},
    closed_Qual b f l (Q_lift d) -> forall {n}, b <= n -> forall {x}, (open_qual n x d) = d.
Proof.
  intros. qual_destruct d. qual_destruct x. unfold_q.
  ndestruct (bvs n); auto.
  apply Q_lift_eq. unfold_Q. nlift. unfold_N. repeat f_equal; intuition.
  all: exfalso; eauto.
Qed.

Lemma closed_qual_open' : forall {d b f l},
    closed_Qual (S b) f l (Q_lift d) ->
    forall {x}, x <= f ->
    forall {d'}, closed_Qual 0 x l d' -> closed_Qual b f l (open_Qual b d' (Q_lift d)).
Proof.
  intros. qual_destruct d. qual_destruct d'.
  unfold_Q. unfold_N. ndestruct (bvs b); intuition; eauto 3 with arith. eapply closed_Nats_tighten; eauto.
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

Lemma closed_Qual_sub : forall {b f l d}, closed_Qual b f l (Q_lift d) -> forall {d'}, Subq (Q_lift d') (Q_lift d) -> closed_Qual b f l (Q_lift d').
Proof.
  intros. Qcrush.
Qed.

Lemma closed_Qual_empty : forall {b f l}, closed_Qual b f l (Q_lift ∅).
  intros. unfold_Q; unfold_N; intuition.
Qed.
#[global] Hint Resolve closed_Qual_empty : core.

(**********
*  qstp  *
**********)

Lemma Qstp_trans : forall tl sl {d1 d2}, Qstp tl sl (Q_lift d1) (Q_lift d2) -> forall {d3}, Qstp tl sl (Q_lift d2) (Q_lift d3) -> Qstp tl sl (Q_lift d1) (Q_lift d3).
  intros. unfold_Q. unfold_N. intuition.
Qed.
Lemma qstp_trans : forall {tl sl d1 d2}, qstp tl sl d1 d2 -> forall {d3}, qstp tl sl d2 d3 -> qstp tl sl d1 d3.
intros. apply Q_lift_qstp. eapply Qstp_trans; eauto.
Qed.

Lemma qstp_closed : forall {tl sl d1 d2},
  Qstp (tl) (sl) (Q_lift d1) (Q_lift d2) ->
  closed_Qual 0 (tl) (sl) (Q_lift d1) /\
  closed_Qual 0 (tl) (sl) (Q_lift d2).
  intros Γ Σ d1 d2 HSQ. induction HSQ; intuition.
  eapply closed_Qual_sub; eauto.
Qed.

Lemma Qstp_refl : forall {d tl sl}, closed_Qual 0 tl sl (Q_lift d) -> Qstp tl sl (Q_lift d) (Q_lift d).
  intros. constructor; subst; auto.
Qed.
Lemma qstp_refl : forall {d tl sl}, closed_Qual 0 tl sl (Q_lift d) -> qstp tl sl d d.
  intros. constructor; subst; auto.
Qed.

(************
*  splice  *
************)

Lemma splice_qual_id : forall {d b f l},
  closed_Qual b f l (Q_lift d) ->
  (splice_qual f d) = d.
Proof.
  qual_destruct d. unfold_Q. intuition. repeat f_equal; eauto using n_splice_id.
Qed.

Lemma splice_qual_open : forall {d j n m},
  splice_qual n (open_qual j (just_fv (m + n)) d) =
  open_qual j (just_fv (S (m + n))) (splice_qual n d).
Proof.
  intros. qual_destruct d. apply Q_lift_eq. repeat rewrite Q_lift_open_qual, Q_lift_splice_qual. unfold_Q. nlift. unfold_N.
  repeat f_equal. apply functional_extensionality. intros. apply propositional_extensionality. intuition.
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

(***********
*  subst  *
***********)

Lemma subst1_qual_empty : forall {dx}, subst_qual q_empty 0 dx = q_empty.
  intros. qual_destruct dx. unfold_q. repeat f_equal; nlift; intros.
Qed.
#[global] Hint Resolve subst1_qual_empty : core.

Lemma subst1_qual_id : forall {b l q}, closed_Qual b 0 l (Q_lift q) -> forall {q1}, subst_qual q 0 q1 = q.
Proof.
  intros. qual_destruct q. qual_destruct q1. apply Q_lift_eq. rewrite Q_lift_subst_qual. unfold_Q. unfold_N. repeat f_equal; apply functional_extensionality; intuition; apply propositional_extensionality; intuition; eauto 4 with arith. exfalso. intuition eauto 3 with arith.
Qed.

Lemma subst1_Qual_plus : forall {du du' l},
    du' ⊑↑ du -> closed_Qual 0 0 l (Q_lift du) -> subst_Qual (Q_lift (du' ⊕ 0)) 0 (Q_lift du) = (Q_lift du).
Proof.
  intros. qual_destruct du'. qual_destruct du. unfold_Q. nlift. unfold_N. repeat f_equal; apply functional_extensionality; intros; apply propositional_extensionality; intuition. exfalso; eauto.
Qed.

Lemma subst1_qual_plus : forall {du du' l},
    du' ⊑↑ du -> closed_Qual 0 0 l (Q_lift du) -> subst_qual (du' ⊕ 0) 0 du = du.
Proof.
  intros. apply Q_lift_eq. rewrite Q_lift_subst_qual. eapply subst1_Qual_plus; eauto.
Qed.

Lemma subst_Qual_subqual_monotone : forall {d1 d2}, Subq (Q_lift d1) (Q_lift d2) -> forall {df}, Subq (subst_Qual (Q_lift d1) 0 (Q_lift df)) (subst_Qual (Q_lift d2) 0 (Q_lift df)).
Proof.
  intros. qual_destruct d1. qual_destruct d2. qual_destruct df. unfold_Q. unfold_N. intuition.
  all: nlem; intuition.
Qed.

Lemma subst_qual_subqual_monotone : forall {d1 d2}, d1 ⊑ d2 -> forall {df}, subst_qual d1 0 df ⊑ subst_qual d2 0 df.
Proof.
  intros. apply Q_lift_subq. repeat rewrite Q_lift_subst_qual. apply subst_Qual_subqual_monotone. apply Q_lift_subq'. auto.
Qed.

Lemma subst1_Qual_subq : forall {du dv du'},
  du ⊑↑ dv -> subst_qual du 0 du' ⊑↑ subst_qual dv 0 du'.
Proof.
  intros.
  qual_destruct du. qual_destruct dv. unfold subst_qual. unfold_q.
  ndestruct (fvs 0); ndestruct (fvs0 0); Qcrush.
Qed.

Lemma subst1_open_qual_comm : forall {k l d1 d2 q1},
    closed_Qual 0 0 l (Q_lift q1) ->
    subst_qual (open_qual k d1 d2) 0 q1 = open_qual k (subst_qual d1 0 q1) (subst_qual d2 0 q1).
Proof.
  intros. qual_destruct d1. qual_destruct d2. qual_destruct q1. unfold_q.
  ndestruct (fvs 0);
  ndestruct (bvs0 k);
  ndestruct (fvs0 0); simpl.
  1,2,5,6: ndestruct (n_or fvs0 fvs 0); nlift.
  1,2,5,6,9,11: ndestruct (n_or bvs0 bvs1 k); nlift.
  9-12,17,18: ndestruct (fvs0 0).
  17-24: ndestruct (bvs0 k).
  (* NOTE: takes quite a long time <2023-05-30, David Deng> *)
  all: apply Q_lift_eq; unfold_Q; nlift; unfold_N; repeat f_equal; apply functional_extensionality; intros; apply propositional_extensionality; intuition.
  all: exfalso; eauto.
Qed.
