Set Warnings "-intuition-auto-with-star".
Require Export PeanoNat.
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
Require Import tactics.

Definition qual : Type := (bool(*fresh?*) * nats(*fv*) * nats(*bv*) * nats(*locs*)).
Definition Qual : Type := (Prop * Nats * Nats * Nats).

Definition qfresh {A B C D} (q : A * B * C * D): A := fst (fst (fst q)).
Definition qfvs   {A B C D} (q : A * B * C * D): B := snd (fst (fst q)).
Definition qbvs   {A B C D} (q : A * B * C * D): C := snd (fst q).
Definition qlocs  {A B C D} (q : A * B * C * D): D := snd q.

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

Ltac qual_destruct a := destruct a as [[[?fr ?fvs] ?bvs] ?lcs].

Definition qdom {A} (Σ : list A): qual := (true, n_empty, n_empty, (n_dom Σ)).

Definition subq (d1 d2 : qual) : Prop :=
  Is_true (implb (qfresh d1) (qfresh d2)) /\ (n_sub (qfvs d1) (qfvs d2)) /\ (n_sub (qbvs d1) (qbvs d2)) /\ (n_sub (qlocs d1) (qlocs d2)).
Definition qor (d1 d2 : qual) : qual := (orb  (qfresh d1) (qfresh d2), n_or  (qfvs d1) (qfvs d2), n_or  (qbvs d1) (qbvs d2), n_or  (qlocs d1) (qlocs d2)).
Definition qand (d1 d2 : qual) : qual := (andb (qfresh d1) (qfresh d2), n_and (qfvs d1) (qfvs d2), n_and (qbvs d1) (qbvs d2), n_and (qlocs d1) (qlocs d2)).
Definition qdiff (d1 d2 : qual) : qual := (andb (qfresh d1) (negb (qfresh d2)), n_diff (qfvs d1) (qfvs d2), n_diff (qbvs d1) (qbvs d2), n_diff (qlocs d1) (qlocs d2)).

(* The cancelling union generalized to qualifiers as second arg *)
Definition qqplus (q1 q2 : qual) : qual := if (qfresh q1) then (qor q1 q2) else q1.
Arguments qqplus _ / _. (* most often we can simplify with the first argument known *)

(* Propositional versions *)
Definition Subq (d1 d2 : Qual) : Prop :=
  ((qfresh d1) -> (qfresh d2)) /\ (N_sub (qfvs d1) (qfvs d2)) /\ (N_sub (qbvs d1) (qbvs d2)) /\ (N_sub (qlocs d1) (qlocs d2)).
Definition Qor (d1 d2 : Qual) : Qual := ((qfresh d1) \/ (qfresh d2), N_or  (qfvs d1) (qfvs d2), N_or  (qbvs d1) (qbvs d2), N_or  (qlocs d1) (qlocs d2)).
Definition Qand (d1 d2 : Qual) : Qual := ((qfresh d1) /\ (qfresh d2), N_and (qfvs d1) (qfvs d2), N_and (qbvs d1) (qbvs d2), N_and (qlocs d1) (qlocs d2)).
Definition Qqplus (d1 d2 : Qual) : Qual := (qfresh d1, (fun x => (qfresh d1 -> N_or (qfvs d1) (qfvs d2) x)   /\ (~ (qfresh d1) -> qfvs d1 x)),
                                                       (fun x => (qfresh d1 -> N_or (qbvs d1) (qbvs d2) x)   /\ (~ (qfresh d1) -> qbvs d1 x)),
                                                       (fun x => (qfresh d1 -> N_or (qlocs d1) (qlocs d2) x) /\ (~ (qfresh d1) -> qlocs d1 x))).
Definition Qdiff (d1 d2 : Qual) : Qual := (qfresh d1 /\ ((qfresh d2) -> False), N_diff (qfvs d1) (qfvs d2), N_diff (qbvs d1) (qbvs d2), N_diff (qlocs d1) (qlocs d2)).
Definition Qdom {A} (Σ : list A): Qual := (True, N_empty, N_empty, (N_dom Σ)).

Definition q_empty: qual := (false, n_empty, n_empty, n_empty).
Definition Q_empty: Qual := (False, N_empty, N_empty, N_empty).

Definition Q_lift (q: qual): Qual := (Is_true (qfresh q), N_lift (qfvs q), N_lift (qbvs q), N_lift (qlocs q)).

Definition open_qual (k : nat) (d' : qual) (d : qual) : qual :=
  if (qbvs d k) then
  qor (qfresh d, qfvs d, n_diff (qbvs d) (n_one k), qlocs d) d'
  else d
.

Definition open_Qual (k : nat) (d' : Qual) (d : Qual) : Qual :=
  (
  (qbvs d k -> qfresh d \/ qfresh d') /\ (~(qbvs d k) -> qfresh d),
  fun x => (qbvs d k -> (N_or (qfvs d) (qfvs d') x)) /\ (~(qbvs d k) -> qfvs d x),
  fun x => (qbvs d k -> (N_or (N_diff (qbvs d) (N_one k)) (qbvs d') x)) /\ (~(qbvs d k) -> qbvs d x),
  fun x => (qbvs d k -> (N_or (qlocs d) (qlocs d') x)) /\ (~(qbvs d k) -> qlocs d x)
  )
.

Definition splice_qual (n : nat) (d : qual) : qual :=
  (qfresh d,(n_splice n (qfvs d)),qbvs d,qlocs d)
.

Definition splice_Qual (n : nat) (d : Qual) : Qual :=
  (qfresh d,(N_splice n (qfvs d)),qbvs d,qlocs d)
.

Definition unsplice_qual (n : nat) (d : qual) : qual :=
  (qfresh d,(n_unsplice n (qfvs d)),qbvs d,qlocs d)
.

Definition unsplice_Qual (n : nat) (d : Qual) : Qual :=
  (qfresh d,(N_unsplice n (qfvs d)),qbvs d,qlocs d)
.

Definition subst_qual (q : qual) (v : nat) (q' : qual) : qual :=
  if qfvs q v
  then qor (qfresh q, n_unsplice 0 (n_diff (qfvs q) (n_one v)), qbvs q, qlocs q) q'
  else (qfresh q, n_unsplice 0 (qfvs q), qbvs q, qlocs q)
.

Definition subst_Qual (q : Qual) (v : nat) (q' : Qual) : Qual :=
  (
  (qfvs q v -> qfresh q \/ qfresh q') /\ (~(qfvs q v) -> qfresh q),
  fun x => (qfvs q v -> (N_or (N_unsplice 0 (N_diff (qfvs q) (N_one v))) (qfvs q') x)) /\ (~(qfvs q v) -> N_unsplice 0 (qfvs q) x),
  fun x => (qfvs q v -> (N_or (qbvs q) (qbvs q') x)) /\ (~(qfvs q v) -> qbvs q x),
  fun x => (qfvs q v -> (N_or (qlocs q) (qlocs q') x)) /\ (~(qfvs q v) -> qlocs q x)
  )
.

Definition closed_qual b f l (q : qual) :=
  closed_nats f (qfvs q) /\ closed_nats b (qbvs q) /\ closed_nats l (qlocs q).

Definition closed_Qual b f l (q : Qual) :=
  closed_Nats f (qfvs q) /\ closed_Nats b (qbvs q) /\ closed_Nats l (qlocs q).

Ltac unfold_q := repeat (unfold open_qual, closed_qual, splice_qual, subst_qual, subq, qdom, q_empty, qqplus, qand, qor, qdiff, qfresh, qfvs, qbvs, qlocs in *; simpl in *).
Ltac unfold_Q := repeat (unfold Q_lift, open_Qual, closed_Qual, splice_Qual, subst_Qual, Subq, Qdom, Q_empty, Qqplus, Qand, Qor, Qdiff, qfresh, qfvs, qbvs, qlocs in *; simpl in *).
Ltac Qcrush := clift; unfold_Q; nlift; blift; unfold_N;
  repeat match goal with
    [ _ : _ |- (_,_) = (_,_) ] => f_equal
         end; try apply functional_extensionality; intros; try apply propositional_extensionality; intuition.

#[global] Hint Unfold qdom : core.
#[global] Hint Unfold qfvs : core.
#[global] Hint Unfold qbvs : core.
#[global] Hint Unfold qlocs : core.
#[global] Hint Unfold qfresh : core.
#[global] Hint Unfold subq : core.
#[global] Hint Unfold Qdom : core.
#[global] Hint Unfold Subq : core.
#[global] Hint Unfold Q_empty: core.

Module QualNotations.
  Declare Scope qualifiers.
  Notation "∅"        := (q_empty) (at level 9) : qualifiers.
  Notation "{♦}"      := (true, n_empty, n_empty, n_empty) (at level 9) : qualifiers. (* \vardiamondsuit *)
  Notation "∅{ f }"   := (f, n_empty, n_empty, n_empty)  (at level 9) : qualifiers.

  Notation "l ∈ₗ d"   := (qmem (inr l) d) (at level 75) : qualifiers.
  Notation "v ∈ᵥ d"   := (qmem (inl v) d) (at level 75) : qualifiers.
  Notation "l ∈?ₗ d"  := (qmemb (inr l) d) (at level 75) : qualifiers.
  Notation "v ∈?ᵥ d"  := (qmemb (inl v) d) (at level 75) : qualifiers.
  Notation "♦∈ d"     := (Is_true (qfresh d)) (at level 75) : qualifiers.
  Notation "♦∉ d"     := (~Is_true (qfresh d)) (at level 75) : qualifiers.
  Notation "♦∈? d"    := (qfresh d) (at level 75) : qualifiers.

  (* untracked n_ones *)
  Notation "$! x "    := (false, (n_one x), n_empty, n_empty) (at level 0, right associativity) : qualifiers.
  Notation "#! x "    := (false, n_empty, (n_one x), n_empty) (at level 0, right associativity) : qualifiers.
  Notation "&! l "    := (false, n_empty, n_empty, (n_one l)) (at level 0, right associativity) : qualifiers.

  (* fresh n_ones *)
  Notation "$♦ x"     := (true, (n_one x), n_empty, n_empty) (at level 0, right associativity) : qualifiers.
  Notation "#♦ x "    := (true, n_empty, (n_one x), n_empty) (at level 0, right associativity) : qualifiers.
  Notation "&♦ l "    := (true, n_empty, n_empty, (n_one l)) (at level 0, right associativity) : qualifiers.

  (* freshness-parametric n_ones *)
  Notation "${ f } x" := (f, (n_one x), n_empty, n_empty) (at level 0, right associativity) : qualifiers.
  Notation "#{ f } x" := (f, n_empty, (n_one x), n_empty) (at level 0, right associativity) : qualifiers.
  Notation "&{ f } l" := (f, n_empty, n_empty, (n_one l)) (at level 0, right associativity) : qualifiers.

  Notation "d ↑" := (Q_lift d) (at level 9) : qualifiers.

  Notation "d1 ⊑ d2"  := (subq d1 d2) (at level 75) : qualifiers.
  Notation "d1 ⊑↑ d2"  := (Subq (Q_lift d1) (Q_lift d2)) (at level 75) : qualifiers.
  (* Notation "d1 ⊑? d2" := (subqb d1 d2) (at level 75) : qualifiers. *)

  (* Notation "d1 ≡ d2"  := (eqqual d1 d2) (at level 75) : qualifiers. *)
  (* Notation "d1 ≡? d2" := (eqqualb d1 d2) (at level 75) : qualifiers. *)

  Notation "d1 ⊔ d2"  := (qor d1 d2) (at level 70, right associativity) : qualifiers.
  Notation "d1 ⊓ d2"  := (qand d1 d2) (at level 65, right associativity) : qualifiers.

  (* qualifier growth *)
  Notation "q1 ⋓ q2"  := (qqplus q1 q2) (at level 70, right associativity) : qualifiers.

  (* overlap (modulo saturation) *)
  Notation "q1 ⋒ q2"  := (qor (qand q1 q2) (true, n_empty, n_empty, n_empty)) (at level 70, right associativity) : qualifiers.
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

(*************
*  boolean  *
*************)

Lemma not_fresh_fresh_false : forall {d}, (♦∉ (d ⊔ {♦})) -> False.
Qcrush.
Qed.

(************
*  Q_lift  *
************)

Lemma Q_lift_empty:
    Q_lift (q_empty) = Q_empty.
Proof.
  intros. Qcrush.
Qed.

Lemma Q_lift_and: forall a b,
    Q_lift (a ⊓ b) = Qand (Q_lift a) (Q_lift b).
Proof.
  intros. unfold Q_lift, Qand. Qcrush; eauto.
Qed.

Lemma Q_lift_or: forall a b,
    Q_lift (a ⊔ b) = Qor (Q_lift a) (Q_lift b).
Proof.
  intros. unfold Q_lift, Qor. Qcrush.
Qed.

Lemma Q_lift_qplus: forall a b,
    Q_lift (a ⋓ b) = Qqplus (Q_lift a) (Q_lift b).
Proof.
  intros. qual_destruct a. qual_destruct b. unfold Q_lift, Qqplus, qqplus, "♦∈?". simpl. destruct (fr); Qcrush.
Qed.

Lemma Q_lift_diff: forall a b,
    Q_lift (qdiff a b) = Qdiff (Q_lift a) (Q_lift b).
Proof.
  intros. unfold Q_lift, Qdiff. Qcrush; eauto.
Qed.

Lemma Q_lift_dist : forall fresh fvs bvs locs, Q_lift (fresh, fvs, bvs, locs) = (Is_true fresh, N_lift fvs, N_lift bvs, N_lift locs).
  intros. unfold Q_lift. intuition.
Qed.

Lemma Q_lift_qdom : forall {A} (H : list A), Q_lift (qdom H) = Qdom H.
intros. unfold qdom. unfold Qdom. rewrite Q_lift_dist. repeat rewrite N_lift_empty. rewrite N_lift_dom. Qcrush.
Qed.

Lemma Q_lift_open_qual: forall a b k,
    Q_lift (open_qual k a b) = open_Qual k (Q_lift a) (Q_lift b).
Proof.
  intros. qual_destruct a. qual_destruct b. unfold Q_lift, open_Qual, open_qual. destruct (qbvs (fr0, fvs0, bvs0, lcs0) k) eqn:Eq.
  - assert (N_lift bvs0 k). { unfold N_lift. auto. } Qcrush.
  - assert (~N_lift bvs0 k). { unfold_q. unfold N_lift. rewrite Eq. auto. } Qcrush.
Qed.

Lemma Q_lift_splice_qual: forall q k,
    Q_lift (splice_qual k q) = splice_Qual k (Q_lift q).
Proof.
  intros. Qcrush.
Qed.

Lemma Q_lift_unsplice_qual: forall q k,
    Q_lift (unsplice_qual k q) = unsplice_Qual k (Q_lift q).
Proof.
  intros. Qcrush.
Qed.

Lemma Q_lift_subst_qual: forall q v q',
    Q_lift (subst_qual q v q') = subst_Qual (Q_lift q) v (Q_lift q').
Proof.
  intros. qual_destruct q. qual_destruct q'. unfold Q_lift, subst_Qual, subst_qual. destruct (qfvs (fr, fvs, bvs, lcs) v) eqn:Eq.
  - assert (N_lift fvs v). { unfold N_lift. auto. } Qcrush.
  - assert (~N_lift fvs v). { unfold_q. unfold N_lift. rewrite Eq. auto. } Qcrush.
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
  intros. unfold_Q. unfold_q. intuition eauto.
Qed.

Lemma Q_lift_eq : forall (p q : qual),
  (Q_lift p = Q_lift q) -> (p = q).
Proof.
  intros. qual_destruct q. qual_destruct p. unfold Q_lift in *. unfold_Q. inversion H. repeat f_equal.
  - apply is_true_lift. auto.
  - apply N_lift_eq. rewrite H2. intuition.
  - apply N_lift_eq. rewrite H3. intuition.
  - apply N_lift_eq. rewrite H4. intuition.
Qed.

Lemma Q_lift_eq' : forall (p q : qual),
  (p = q) -> (Q_lift p = Q_lift q).
Proof.
  intros. unfold Q_lift. rewrite H. intuition.
Qed.

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
#[global] Hint Resolve Subq_trans : core.

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
Lemma subq_qor_gt: forall {q1 q2 : qual}, q1 ⊑ q1 ⊔ q2.
intros. apply Q_lift_subq. apply Subq_qor_gt.
Qed.

(**********
*  qand  *
**********)

Lemma qand_commute : forall {d1 d2}, d1 ⊓ d2 = d2 ⊓ d1.
intros. apply Q_lift_eq. repeat rewrite Q_lift_and. Qcrush.
Qed.

(* Lemma qand_fresh_r : forall {d1 df f l}, *)
(*     closed_Qual 0 f l (Q_lift d1) -> closed_Qual 0 f l (Q_lift df) -> forall {l'}, l <= l' -> d1 ⊓ df = d1 ⊓ (df ⊔ (just_loc l')). *)
(* intros. qual_destruct df. qual_destruct d1. apply Q_lift_eq. unfold_q. unfold_Q; nlift; unfold_N; repeat f_equal; apply functional_extensionality; intros; apply propositional_extensionality; intuition. subst; exfalso; eauto. *)
(* Qed. *)

(* Lemma qand_fresh_l : forall {d1 df f l}, *)
(*     closed_qual 0 f l d1 -> closed_qual 0 f l df -> forall {l'}, l <= l' -> d1 ⊓ df = (d1 ⊔ just_loc l') ⊓ df. *)
(*   intros. rewrite qand_commute. erewrite qand_fresh_r; eauto. *)
(*   rewrite qand_commute. auto. *)
(* Qed. *)

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
Lemma subq_qor : forall {d1 d2}, d1 ⊑ d2 -> forall {d}, d1 ⊔ d ⊑ d2 ⊔ d.
intros. apply Q_lift_subq. apply Subq_qor. apply Q_lift_subq'. auto.
Qed.

Lemma qor_idem : forall {q}, (q ⊔ q) = q.
intros. apply Q_lift_eq; Qcrush.
Qed.

Lemma qor_assoc : forall {q1 q2 q3}, (q1 ⊔ (q2 ⊔ q3)) = ((q1 ⊔ q2) ⊔ q3).
intros. apply Q_lift_eq. Qcrush.
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
#[global] Hint Resolve closed_Qual_monotone : core.
Lemma closed_qual_monotone : forall {f b l d},
    closed_qual b f l d ->
    forall {b' f' l'},
      b <= b' ->
      f <= f' ->
      l <= l' ->
      closed_qual b' f' l' d.
Proof.
  intros. apply Q_lift_closed. eauto.
Qed.
#[global] Hint Resolve closed_qual_monotone : core.

Lemma closed_Qual_open_id : forall {d b f l},
    closed_Qual b f l (Q_lift d) -> forall {n}, b <= n -> forall {x}, (open_qual n x d) = d.
Proof.
  intros. qual_destruct d. qual_destruct x. unfold_q.
  #[local] Hint Resolve n_reflect_true : bdestruct.
  bdestruct (bvs n); auto.
  #[local] Remove Hints n_reflect_true : bdestruct.
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

Lemma closed_Qual_open' : forall {d b f l},
    closed_Qual (S b) f l (Q_lift d) ->
    forall {x}, x <= f ->
    forall {d'}, closed_Qual 0 x l d' -> closed_Qual b f l (open_Qual b d' (Q_lift d)).
Proof.
  intros. qual_destruct d. qual_destruct d'.
  #[local] Hint Resolve n_reflect_true : bdestruct.
  unfold_Q. unfold_N. bdestruct (bvs b); intuition; eauto 3 with arith. eapply closed_Nats_tighten; eauto.
  #[local] Remove Hints n_reflect_true : bdestruct.
Qed.
#[global] Hint Resolve closed_Qual_open' : core.
Lemma closed_qual_open' : forall {d b f l},
    closed_qual (S b) f l d ->
    forall {x}, x <= f ->
    forall {d'}, closed_qual 0 x l d' -> closed_qual b f l (open_qual b d' d).
Proof.
  intros. apply Q_lift_closed. apply Q_lift_closed' in H,H1. rewrite Q_lift_open_qual. eauto.
Qed.
#[global] Hint Resolve closed_qual_open' : core.

Lemma closed_Qual_open_succ : forall {d b fr f l},
    closed_Qual b f l d↑ ->
    forall {j}, closed_Qual b (S f) l (open_Qual j ${fr}f↑ d↑).
Proof.
  intros. qual_destruct d.
  #[local] Hint Resolve n_reflect_true : bdestruct.
  bdestruct (bvs j); Qcrush.
  #[local] Remove Hints n_reflect_true : bdestruct.
Qed.
#[global] Hint Resolve closed_Qual_open_succ : core.
Lemma closed_qual_open_succ : forall {d b fr f l},
    closed_qual b f l d ->
    forall {j}, closed_qual b (S f) l (open_qual j ${fr}f d).
Proof.
  intros. apply Q_lift_closed. apply Q_lift_closed' in H. rewrite Q_lift_open_qual. eauto.
Qed.
#[global] Hint Resolve closed_qual_open_succ : core.

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

Lemma closed_Qual_qqplus: forall {b f l d1 d2}, closed_Qual b f l d1 ↑ -> closed_Qual b f l d2 ↑ -> closed_Qual b f l (d1 ⋓ d2) ↑.
  intros. qual_destruct d1. qual_destruct d2. rewrite Q_lift_qplus. destruct fr; Qcrush.
Qed.
Lemma closed_qual_qqplus: forall {b f l d1 d2}, closed_qual b f l d1 -> closed_qual b f l d2 -> closed_qual b f l (d1 ⋓ d2).
  intros. apply Q_lift_closed. eauto using closed_Qual_qqplus.
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

(**********
*  open  *
**********)

Lemma open_qual_commute : forall d frx fry i j x y, i <> j ->
    open_qual i ${frx} x (open_qual j ${fry} y d)
  = open_qual j ${fry} y (open_qual i ${frx} x d).
#[local] Hint Resolve n_reflect_true : bdestruct.
intros. qual_destruct d. unfold_q. bdestruct (bvs i); bdestruct (bvs j); simpl.
- bdestruct (n_or (n_diff bvs (n_one j)) n_empty i); bdestruct ((n_or (n_diff bvs (n_one i)) n_empty j)); apply Q_lift_eq; Qcrush.
- bdestruct (bvs i); bdestruct (n_or (n_diff bvs (n_one i)) n_empty j); apply Q_lift_eq; Qcrush.
- bdestruct (bvs j); bdestruct (n_or (n_diff bvs (n_one j)) n_empty i); apply Q_lift_eq; Qcrush.
- bdestruct (bvs i); bdestruct (bvs j); apply Q_lift_eq; Qcrush.
#[local] Remove Hints n_reflect_true : bdestruct.
Qed.

Lemma open_qual_commute' : forall d i j fr x d' f l, i <> j ->
  closed_Qual 0 f l d' ↑ ->
  open_qual i ${fr}x (open_qual j d' d)
  = open_qual j d' (open_qual i ${fr}x d).
qual_destruct d; qual_destruct d'. intros.
unfold_q.
#[local] Hint Resolve n_reflect_true : bdestruct.
bdestruct (bvs i); bdestruct (bvs j); bdestruct (bvs0 i); bdestruct (bvs0 j); simpl; apply Q_lift_eq; Qcrush; exfalso; eauto.
#[local] Remove Hints n_reflect_true : bdestruct.
Qed.

Lemma open_qual_commute'' : forall d i j d' d'' f l, i <> j -> closed_Qual 0 f l d' ↑ -> closed_Qual 0 f l d'' ↑ ->
  open_qual i d'' (open_qual j d' d)
  = open_qual j d' (open_qual i d'' d).
qual_destruct d. qual_destruct d'. qual_destruct d''. intros.
unfold_q.
#[local] Hint Resolve n_reflect_true : bdestruct.
bdestruct (bvs i); bdestruct (bvs j); bdestruct (bvs0 i); bdestruct (bvs0 j); bdestruct (bvs1 i); bdestruct (bvs1 j); simpl; apply Q_lift_eq; Qcrush; exfalso; eauto.
#[local] Remove Hints n_reflect_true : bdestruct.
Qed.

Lemma closed_qual_open2 : forall {f l d1 d2 d}, closed_qual 2 f l d -> closed_qual 0 f l d1 -> closed_qual 0 f l d2 -> closed_qual 0 f l (open_qual 1 d1 (open_qual 0 d2 d)).
  intros. erewrite open_qual_commute''; eauto.
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

Lemma subst1_open_qual_comm : forall {k l d1 d2 q1},
    closed_Qual 0 0 l (Q_lift q1) ->
    subst_qual (open_qual k d1 d2) 0 q1 = open_qual k (subst_qual d1 0 q1) (subst_qual d2 0 q1).
Proof.
  intros. qual_destruct d1. qual_destruct d2. qual_destruct q1. unfold_q.
  #[local] Hint Resolve n_reflect_true : bdestruct.
  bdestruct (bvs0 k); simpl;
  bdestruct (fvs0 0); simpl;
  bdestruct (fvs 0); simpl;
  bdestruct (bvs1 k); simpl;
  apply Q_lift_eq; clift; Qcrush; exfalso; eauto.
  #[local] Remove Hints n_reflect_true : bdestruct.
Qed.

Lemma open_subst1_qual_comm : forall {q : qual} {k g fr df ff lf},
    closed_Qual 0 ff lf df↑ ->
    open_qual k ${fr}g (subst_qual q 0 df) = subst_qual (open_qual k ${fr}(S g) q) 0 df.
Proof.
  intros. qual_destruct df. qual_destruct q. unfold_q.
  #[local] Hint Resolve n_reflect_true : bdestruct.
  bdestruct (bvs0 k); simpl;
  bdestruct (fvs0 0); simpl;
  bdestruct (bvs k); simpl;
  bdestruct (n_one (S g) 0);
  apply Q_lift_eq; clift; Qcrush; exfalso; eauto.
  #[local] Remove Hints n_reflect_true : bdestruct.
Qed.

Lemma closed_qual_subst1 : forall {q b f l},
    closed_Qual b (S f) l q ↑ ->
    forall {d1 l1}, closed_Qual 0 0 l1 d1 ↑ ->
    forall{l2},
      l <= l2 -> l1 <= l2 ->
      closed_Qual b f l2 (subst_qual q 0 d1) ↑.
Proof.
  intros. qual_destruct q. unfold_q.
  #[local] Hint Resolve n_reflect_true : bdestruct.
  bdestruct (fvs 0); Qcrush; try solve [eauto using PeanoNat.lt_S_n, Nat.lt_le_trans]; try solve [exfalso; eauto 3].
  #[local] Remove Hints n_reflect_true : bdestruct.
Qed.

Lemma subst1_qor_dist : forall {q1 q2 df},
  subst_qual (q1 ⊔ q2) 0 df = ((subst_qual q1 0 df) ⊔ (subst_qual q2 0 df)).
Proof.
  intros. qual_destruct q1. qual_destruct q2. qual_destruct df. unfold_q.
  #[local] Hint Resolve n_reflect_true : bdestruct.
  bdestruct (fvs 0); simpl;
  bdestruct (fvs0 0); simpl; apply Q_lift_eq; Qcrush.
  #[local] Remove Hints n_reflect_true : bdestruct.
Qed.

Lemma subst_qual_subqual_monotone : forall {d1 d2}, d1 ⊑↑ d2 -> forall {df}, (subst_qual d1 0 df) ⊑↑ (subst_qual d2 0 df).
Proof.
  intros. qual_destruct d1; qual_destruct d2; qual_destruct df; unfold_q.
  #[local] Hint Resolve n_reflect_true : bdestruct.
  bdestruct (fvs0 0); simpl;
  bdestruct (fvs 0); simpl; Qcrush.
  #[local] Remove Hints n_reflect_true : bdestruct.
Qed.

Lemma subst_filter0 : forall {d φ l fr}, closed_Qual 0 0 l (Q_lift d) -> Subq (Q_lift ${fr}0) (Q_lift φ) -> Subq (Q_lift d) (Q_lift (subst_qual φ 0 d)).
  intros. qual_destruct φ. unfold_q.
  #[local] Hint Resolve n_reflect_true : bdestruct.
  bdestruct (fvs 0); Qcrush.
  #[local] Remove Hints n_reflect_true : bdestruct.
Qed.