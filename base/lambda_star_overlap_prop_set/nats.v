Require Import Coq.Lists.List.
Require Import Psatz.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.
Import ListNotations.

Require Import tactics.
Require Import env.

Definition nats := nat -> bool.

Definition n_empty: nats := fun x => false.    (* no body can reach *)

Definition n_one (x:nat): nats := fun x' => x' =? x.  (* x can reach x *)

Definition n_and q1 q2 (x:nat) := (q1 x) && q2 x. (* q1 and q2 can reach x *)

Definition n_or q1 q2 (x:nat) := (q1 x) || q2 x.

Definition n_diff q1 q2 (x: nat) := (q1 x) && (negb (q2 x)).

Definition n_dom {X} (H: list X) := fun x' =>  x' <? (length H).

Definition n_sub (q1 q2: nats): Prop := forall x:nat, q1 x = true -> q2 x = true.

Definition n_splice (n: nat) (q: nats) : nats := fun x =>
         if x =? n then false else if x <? n then q x else q (pred x).

Definition n_unsplice (n: nat) (q: nats) : nats := fun x =>
         if x <? n then q x else q (S x).

Definition Nats := nat -> Prop.

Definition N_empty: Nats := fun x => False.                            (* empty set *)

Definition N_one (x:nat): Nats := fun x' => x' = x.                    (* singleton set *)

Definition N_and p1 p2 (x:nat) := p1 x /\ p2 x.                        (* intersection *)

Definition N_or p1 p2 (x:nat) := p1 x \/ p2 x.                         (* union *)

Definition N_diff p1 p2 (x:nat) := p1 x /\ (p2 x -> False).            (* difference *)

Definition N_dom {X} (H: list X) := fun x' =>  x' < (length H).        (* domain of a list *)

Definition N_sub (p1 p2: Nats): Prop := forall x:nat, p1 x -> p2 x.    (* subset inclusion *)

Definition N_lift (b: nats): Nats := fun x => b x = true.              (* reflect nat->bool set *)

Definition N_splice (n: nat) (q: Nats) : Nats := fun x =>
    (x = n -> False) /\ (x < n -> q x) /\ (x > n -> q (pred x)).

Definition N_unsplice (n: nat) (q: Nats) : Nats := fun x =>
    (x < n -> q x) /\ (~ x < n -> q (S x)).

Definition closed_nats m q := (forall x, q x = true -> x < m).

Definition closed_Nats m (p: nat -> Prop) := (forall x, p x -> x < m).

(* reflect  *)

Lemma n_reflect_true: forall (n : nats) x,
  reflect (N_lift n x)(n x).
Proof.
    intros. apply iff_reflect. intuition.
Qed.
#[global] Hint Resolve n_reflect_true : ndestruct.

Lemma n_reflect_false: forall (n : nats) x,
  reflect (~ N_lift n x)(negb (n x)).
Proof.
    intros. apply iff_reflect. unfold N_lift,not,negb. split; intros; destruct (n x); auto; discriminate.
Qed.
#[global] Hint Resolve n_reflect_false : ndestruct.

Lemma n_one_reflect: forall m x,
  reflect (m = x)(n_one m x).
Proof.
    intros. apply iff_reflect. symmetry.
    unfold n_one; split; intros.
    apply Nat.eqb_eq in H. auto.
    apply Nat.eqb_eq. auto.
Qed.
#[global] Hint Resolve n_one_reflect : ndestruct.

Lemma n_and_reflect_true: forall q1 q2 x,
    reflect (q1 x = true /\ q2 x = true)(n_and q1 q2 x).
Proof.
    intros. apply iff_reflect. symmetry.
    unfold n_and. apply andb_true_iff.
Qed.
#[global] Hint Resolve n_and_reflect_true : ndestruct.

Lemma n_and_reflect_false: forall q1 q2 x,
    reflect (q1 x = false \/ q2 x = false) (negb (n_and q1 q2 x)).
Proof.
    intros. apply iff_reflect. symmetry.
    unfold n_and. split; intros.
    apply andb_false_iff.  apply negb_true_iff in H. auto.
    apply negb_true_iff; apply andb_false_iff.  auto.
Qed.
#[global] Hint Resolve n_and_reflect_false : ndestruct.

Lemma n_or_reflect_true: forall q1 q2 x,
    reflect (q1 x = true \/ q2 x = true)(n_or q1 q2 x).
Proof.
    intros. apply iff_reflect. symmetry.
    unfold n_or. apply orb_true_iff.
Qed.
#[global] Hint Resolve n_or_reflect_true : ndestruct.

Lemma n_diff_reflect_true: forall q1 q2 x,
    reflect (n_diff q1 q2 x = true)((q1 x) && (negb (q2 x))).
Proof.
    intros. apply iff_reflect. symmetry.
    unfold n_diff. intuition.
Qed.
#[global] Hint Resolve n_diff_reflect_true : ndestruct.

Lemma n_or_reflect_false: forall q1 q2 x,
    reflect (q1 x = false /\ q2 x = false)(negb(n_or q1 q2 x)) .
Proof.
    intros. apply iff_reflect. symmetry.
    unfold n_or. split; intro.
    apply negb_true_iff in H. apply orb_false_iff in H. auto.
    apply negb_true_iff. apply orb_false_iff.  auto.
Qed.
#[global] Hint Resolve n_or_reflect_false : ndestruct.

Lemma n_dom_reflect {X}: forall (H: list X) n,
  reflect (n < length H)(n_dom H n).
Proof.
    intros. apply iff_reflect. symmetry.
    unfold n_dom. apply Nat.ltb_lt; auto.
Qed.
#[global] Hint Resolve n_dom_reflect : ndestruct.

Ltac unfold_N := unfold N_sub, N_dom, N_and, N_or, N_empty, N_one, N_diff, N_splice, N_unsplice, closed_Nats in *.
Ltac unfold_n := unfold n_sub, n_dom, n_and, n_or, n_empty, n_one, n_diff, n_splice, n_unsplice, closed_nats in *.


(************************
*  rewritable lifting  *
************************)

Lemma N_lift_empty:
    N_lift (n_empty) = N_empty.
Proof.
  intros. unfold_N. unfold N_lift.
  eapply functional_extensionality. intros.
  eapply propositional_extensionality.
  destruct (n_empty x) eqn:Eq; intuition.
Qed.

Lemma N_lift_one: forall x,
    N_lift (n_one x) = N_one x.
Proof.
  intros. unfold_N. unfold N_lift.
  eapply functional_extensionality. intros.
  eapply propositional_extensionality.
  unfold N_one. apply Nat.eqb_eq.
Qed.

Lemma N_lift_and: forall a b,
    N_lift (n_and a b) = N_and (N_lift a) (N_lift b).
Proof.
  intros. unfold_N. unfold N_lift.
  eapply functional_extensionality. intros.
  eapply propositional_extensionality.
  ndestruct (n_and a b x); intuition.
Qed.

Lemma N_lift_or: forall a b,
    N_lift (n_or a b) = N_or (N_lift a) (N_lift b).
Proof.
  intros. unfold_N. unfold N_lift.
  eapply functional_extensionality. intros.
  eapply propositional_extensionality.
  ndestruct (n_or a b x); intuition.
Qed.

Lemma N_lift_dom : forall {A} (H: list A), N_lift (n_dom H) = N_dom H.
  intros. unfold_n. unfold_N. unfold N_lift. eapply functional_extensionality. intros.
  eapply propositional_extensionality. rewrite Nat.ltb_lt. intuition.
Qed.

Lemma N_lift_diff : forall a b,
    N_lift (n_diff a b) = N_diff (N_lift a) (N_lift b).
    intros. unfold_N. unfold N_lift. unfold n_diff.
    eapply functional_extensionality. intros.
    eapply propositional_extensionality.
    destruct (b x) eqn:Hbx; destruct (a x) eqn:Hax; intuition.
Qed.

Lemma N_lift_splice : forall n s,
     N_lift (n_splice n s) = N_splice n (N_lift s).
     intros. unfold_N. unfold n_splice. unfold N_lift.
     eapply functional_extensionality. intros.
     eapply propositional_extensionality. bdestruct (x <? n); bdestruct (x =? n); intuition.
Qed.

Lemma N_lift_unsplice : forall n s,
     N_lift (n_unsplice n s) = N_unsplice n (N_lift s).
     intros. unfold_N. unfold n_unsplice. unfold N_lift.
     eapply functional_extensionality. intros.
     eapply propositional_extensionality. bdestruct (x <? n); intuition.
Qed.


(************************
*  applicable lifting  *
************************)

Lemma N_lift_eq : forall (n m : nats),
  (forall x : nat, N_lift n x <-> N_lift m x) -> (n = m).
Proof.
  intros. unfold N_lift in *. apply functional_extensionality. intros. specialize (H x). destruct (n x) eqn:Eq; destruct (m x) eqn:Eq2; intuition.
Qed.
Lemma N_lift_eq' : forall (n m : nats),
  (n = m) -> (forall x : nat, N_lift n x <-> N_lift m x).
Proof.
  intros. unfold N_lift. rewrite H. intuition.
Qed.

Lemma N_lift_sub : forall n1 n2,
  N_sub (N_lift n1) (N_lift n2) -> n_sub n1 n2.
  intros. unfold_N. unfold n_sub. unfold N_lift in *. auto.
Qed.
Lemma N_lift_sub' : forall n1 n2,
  n_sub n1 n2 -> N_sub (N_lift n1) (N_lift n2).
  intros. unfold_N. unfold n_sub. unfold N_lift. intros; intuition.
Qed.

Lemma N_lift_closed : forall (m : nat) (q : nats),
  closed_Nats m (N_lift q) -> closed_nats m q.
Proof.
  intros. intros; unfold_N; unfold_n; unfold N_lift in *; auto.
Qed.
Lemma N_lift_closed' : forall (m : nat) (q : nats),
  closed_nats m q -> closed_Nats m (N_lift q).
Proof.
  intros. intros; unfold_N; unfold_n; unfold N_lift in *; auto.
Qed.

#[global] Hint Rewrite N_lift_empty N_lift_one N_lift_and N_lift_or N_lift_diff N_lift_splice N_lift_unsplice : nlift_rewrite.

Ltac nlift := autorewrite with nlift_rewrite in *.

(**********************
*  basic properties  *
**********************)

Lemma closed_nats_mono : forall n s, closed_nats n s -> forall {m}, n <= m -> closed_nats m s.
    unfold closed_nats. intros. apply H in H1. lia.
Qed.
#[global] Hint Resolve closed_nats_mono : core.

Lemma closed_Nats_mono : forall n s, closed_Nats n s -> forall {m}, n <= m -> closed_Nats m s.
    unfold closed_Nats. intros. apply H in H1. lia.
Qed.
#[global] Hint Resolve closed_Nats_mono : core.

Lemma closed_nats_tighten : forall n s, closed_nats (S n) s -> (s n = false) -> closed_nats n s.
    intros. unfold closed_nats in *. intros. destruct (x =? n) eqn:Eq.
    - apply Nat.eqb_eq in Eq. rewrite Eq in H1. rewrite H1 in H0. discriminate H0.
    - apply H in H1. apply Nat.eqb_neq in Eq. lia.
Qed.

Lemma closed_Nats_tighten : forall n s, closed_Nats (S n) s -> (~ s n) -> closed_Nats n s.
    intros. unfold closed_Nats in *. intros. destruct (x =? n) eqn:Eq.
    - apply Nat.eqb_eq in Eq. rewrite Eq in H1. contradiction.
    - apply H in H1. apply Nat.eqb_neq in Eq. lia.
Qed.

Lemma n_splice_id : forall n s, closed_nats n s -> (n_splice n s) = s.
    intros. unfold_n. apply functional_extensionality. intros.
bdestruct (x =? n); bdestruct (x <? n); intuition.
  - specialize (H n). rewrite <- H0 in H. unfold N_lift in H. destruct (s x); intuition.
  - destruct (s x) eqn:Hin. specialize (H x). unfold N_lift in H. intuition.
    destruct (s (Init.Nat.pred x)) eqn:Hin2; auto. assert (Hge: (Init.Nat.pred x) >= n) by lia. specialize (H (Init.Nat.pred x)). unfold N_lift in H. intuition.
Qed.

Lemma N_splice_id : forall n s, closed_Nats n s -> (N_splice n s) = s.
    intros. unfold_N. apply functional_extensionality. intros.
bdestruct (x =? n); bdestruct (x <? n); apply propositional_extensionality; intuition.
  - specialize (H n). rewrite <- H0 in H. intuition.
  - exfalso. assert (x > n) by lia. apply H5 in H4. apply H in H4. lia.
  - apply H in H2. lia.
Qed.

Lemma N_sub_splice : forall n a b, N_sub a b -> N_sub (N_splice n a) (N_splice n b).
Proof.
  unfold_N. intros. intuition.
Qed.
#[global] Hint Resolve N_sub_splice : core.

Lemma N_splice_closed : forall {i d n},
    closed_Nats n d ->
    closed_Nats (S n) (N_splice i d).
Proof.
  unfold_N. intros. bdestruct (x <=? i); intuition. apply H in H3. lia.
Qed.
#[global] Hint Resolve N_splice_closed : core.

Lemma N_sub_closed : forall n a b, closed_Nats n b -> N_sub a b -> closed_Nats n a.
Proof.
  unfold_N. intros. intuition.
Qed.
#[global] Hint Resolve N_sub_closed : core.

Lemma N_closed_0_not_in : forall n m, closed_Nats 0 n -> ~(n m).
Proof.
  unfold_N. intuition. apply H in H0. lia.
Qed.
#[global] Hint Resolve N_closed_0_not_in : core.

Lemma N_closed_not_in : forall n m m', closed_Nats m n -> m <= m' -> ~(n m').
Proof.
  unfold_N. intuition. apply H in H1. lia.
Qed.
#[global] Hint Resolve N_closed_not_in : core.

Lemma N_neq : forall n m m', N_lift n m -> (N_lift n m' -> False) -> (m = m' -> False).
intros. intuition. rewrite H1 in H. contradiction.
Qed.
#[global] Hint Resolve N_neq : core.

(*********
*  lem  *
*********)

Lemma N_mem_absurd : forall m n, (N_lift m n) -> ~(N_lift m n) -> False.
Proof.
  intuition.
Qed.
#[global] Hint Resolve N_mem_absurd : core.

Lemma N_mem_lem : forall m n (P Q : Prop), (N_lift m n -> P) -> (~(N_lift m n) -> Q) -> (N_lift m n /\ P) \/ (~N_lift m n /\ Q).
Proof.
  intros. unfold N_lift in *. destruct (m n); intuition.
Qed.
(* #[global] Hint Resolve N_mem_lem : core. *)

Ltac nlem :=
  repeat match goal with
         | [ H1 : (?a -> _), H2 : ((?a -> False) -> _) |- _ ]  => (pose proof N_mem_lem _ _ _ _ H1 H2); clear H1 H2
         end.

(*********
*  nat  *
*********)

Lemma lt_S_ne_lt : forall {n m}, n < S m -> n <> m -> n < m.
intros. lia.
Qed.
#[global] Hint Resolve lt_S_ne_lt : core.

Lemma lt_0_absurd: forall n : nat, n < 0 -> False.
intros. lia.
Qed.
#[global] Hint Resolve lt_0_absurd : core.

Lemma or_False_cancel : forall P, (P \/ False) = P.
intros. apply propositional_extensionality. split; intros; intuition.
Qed.
#[global] Hint Rewrite or_False_cancel : core.
