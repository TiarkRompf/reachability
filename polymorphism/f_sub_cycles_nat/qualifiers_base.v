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
Definition qdom' {A} (Σ : list (option A)): qual := (true, n_empty, n_empty, (n_dom' Σ)).

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
  then qor (qfresh q, n_unsplice v (n_diff (qfvs q) (n_one v)), qbvs q, qlocs q) q'
  else (qfresh q, n_unsplice v (qfvs q), qbvs q, qlocs q)
.

Definition subst_Qual (q : Qual) (v : nat) (q' : Qual) : Qual :=
  (
  (qfvs q v -> qfresh q \/ qfresh q') /\ (~(qfvs q v) -> qfresh q),
  fun x => (qfvs q v -> (N_or (N_unsplice v (N_diff (qfvs q) (N_one v))) (qfvs q') x)) /\ (~(qfvs q v) -> N_unsplice v (qfvs q) x),
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

  Notation "d1 ⊔ d2"  := (qor d1 d2) (at level 70, right associativity) : qualifiers.
  Notation "d1 ⊓ d2"  := (qand d1 d2) (at level 65, right associativity) : qualifiers.

  (* qualifier growth *)
  Notation "q1 ⋓ q2"  := (qqplus q1 q2) (at level 70, right associativity) : qualifiers.

  (* overlap (modulo saturation) *)
  Notation "q1 ⋒ q2"  := (qor (qand q1 q2) (true, n_empty, n_empty, n_empty)) (at level 70, right associativity) : qualifiers.
End QualNotations.
Export QualNotations.
Local Open Scope qualifiers.

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
