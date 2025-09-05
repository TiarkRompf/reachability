Require Import Coq.Lists.List.
Require Import Psatz.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import FunctionalExtensionality.
Import ListNotations.

Require Import tactics.
Require Import env.

Definition ql := nat -> bool.

Definition qempty: ql := fun x => false.    (* no body can reach *)

Definition qone (x:nat): ql := fun x' => x' =? x.  (* x can reach x *)

Definition qand q1 q2 (x:nat) := (q1 x) && q2 x. (* q1 and q2 can reach x *)

Definition qor q1 q2 (x:nat) := (q1 x) || q2 x.

Definition qdiff q1 q2 (x: nat) := (q1 x) && (negb (q2 x)).

Definition qdom {X} (H: list X) := fun x' =>  x' <? (length H).

Definition qsub (q1 q2:ql): Prop := forall x:nat, q1 x = true -> q2 x = true.

(* reflect  *)

Lemma qone_reflect: forall m x,
  reflect (m = x)(qone m x).
Proof. 
    intros. apply iff_reflect. symmetry.
    unfold qone; split; intros. 
    apply Nat.eqb_eq in H. auto.
    apply Nat.eqb_eq. auto.
Qed.
#[global] Hint Resolve qone_reflect : bdestruct.

Lemma qand_reflect_true: forall q1 q2 x,
    reflect (q1 x = true /\ q2 x = true)(qand q1 q2 x). 
Proof.
    intros. apply iff_reflect. symmetry.
    unfold qand. apply andb_true_iff.
Qed.
#[global] Hint Resolve qand_reflect_true : bdestruct.

Lemma qand_reflect_false: forall q1 q2 x,
    reflect (q1 x = false \/ q2 x = false) (negb (qand q1 q2 x)).
Proof. 
    intros. apply iff_reflect. symmetry. 
    unfold qand. split; intros. 
    apply andb_false_iff.  apply negb_true_iff in H. auto. 
    apply negb_true_iff; apply andb_false_iff.  auto.
Qed.
#[global] Hint Resolve qand_reflect_false : bdestruct.

Lemma qor_reflect_true: forall q1 q2 x,
    reflect (q1 x = true \/ q2 x = true)(qor q1 q2 x).
Proof.
    intros. apply iff_reflect. symmetry.
    unfold qor. apply orb_true_iff. 
Qed.
#[global] Hint Resolve qor_reflect_true : bdestruct.

Lemma qdiff_reflect_true: forall q1 q2 x,
    reflect (qdiff q1 q2 x = true)((q1 x) && (negb (q2 x))).
Proof.
    intros. apply iff_reflect. symmetry.
    unfold qdiff. intuition.
Qed.
#[global] Hint Resolve qdiff_reflect_true : bdestruct.

Lemma qor_reflect_false: forall q1 q2 x,
    reflect (q1 x = false /\ q2 x = false)(negb(qor q1 q2 x)) .
Proof. 
    intros. apply iff_reflect. symmetry.
    unfold qor. split; intro. 
    apply negb_true_iff in H. apply orb_false_iff in H. auto.
    apply negb_true_iff. apply orb_false_iff.  auto.
Qed.
#[global] Hint Resolve qor_reflect_false : bdestruct.

Lemma qdom_reflect {X}: forall (H: list X) n,
  reflect (n < length H)(qdom H n).
Proof. 
    intros. apply iff_reflect. symmetry. 
    unfold qdom. apply Nat.ltb_lt; auto.
Qed.    
#[global] Hint Resolve qdom_reflect : bdestruct.


Lemma qempty_false: forall x,
  qempty x = false.
Proof.
    intros. unfold qempty. auto.
Qed.


Lemma qand_empty_l: forall q,
    qand qempty q = qempty.
Proof. 
    intros. unfold qand. auto.
Qed.
#[global] Hint Resolve qand_empty_l : core.

Lemma qand_empty_r: forall q,
    qand q qempty = qempty.
Proof.
    intros. apply functional_extensionality. intros.
    bdestruct (qand q qempty x); intuition.
Qed.
#[global] Hint Resolve qand_empty_r : core.

Lemma qand_qone_empty: forall q m,
    q m = false ->
    qand (qone m ) q = qempty.
Proof. 
    intros. apply functional_extensionality. intros.
    rewrite qempty_false.
    bdestruct (qand (qone m)  q x); bdestruct (qone m x); intuition.
    subst. rewrite H in H3. discriminate. 
Qed.
#[global] Hint Resolve qand_qone_empty : core.

Lemma qsub_empty_l: forall q,
    qsub qempty q.
Proof.
    intros. unfold qsub. intros. inversion H.
Qed.
#[global] Hint Resolve qsub_empty_l : core.

Lemma qsub_empty: forall q,
    qsub q qempty <-> q = qempty.
Proof.
    intros. split;  intros.
    + apply functional_extensionality. intros.
    rewrite  qempty_false.
    unfold qsub in H. specialize H with x.
    destruct (q x) eqn: Heqn; intuition.
    + rewrite H. auto.
Qed.
#[global] Hint Resolve qsub_empty : core.

Lemma qor_empty_id_l: forall q,
    q = qor qempty q.
Proof. 
    intros. apply functional_extensionality.
    intros. unfold qor. auto.
Qed.
#[global] Hint Rewrite <- qor_empty_id_l : core. 

Lemma qor_empty_id_r: forall q,
    q = qor q qempty.
Proof. 
    intros. apply functional_extensionality.
    intros. unfold qor. unfold qempty. intuition.
Qed.
#[global] Hint Rewrite <- qor_empty_id_r : core.

(* qand *)
Lemma qand_idempetic: forall p,
  qand p p = p.
Proof. 
    intros. unfold qand. apply functional_extensionality.
    intros. intuition.
    destruct (p x) eqn: Heq. auto. auto.
Qed.
#[global] Hint Resolve qand_idempetic : core.  

Lemma qand_commutative: forall p q,
    qand p q = qand q p.
Proof.
    intros. unfold qand. apply functional_extensionality.
    intros. intuition.
Qed.

Lemma qand_associative: forall p q s,
  qand (qand p q) s = 
  qand p (qand q s).
Proof.
    intros. unfold qand. apply functional_extensionality.
    intros. erewrite andb_assoc. auto.
Qed.

Lemma qand_true_iff: forall p q x,
    qand p q x = true <->
    (p x = true /\ q x = true).
Proof.
    intros. split. 
    +  bdestruct (qand p q x); intuition.
    +  intros. intuition. 
       bdestruct (qand p q x); intuition.
Qed.
#[global] Hint Resolve qand_true_iff : core.  

Lemma qand_sub_l : forall p q,
  qsub p q -> qand q p = p.
Proof.
    intros. apply functional_extensionality. intros.
    bdestruct (qand q p x); intuition.
    unfold qsub in H. specialize (H x).
    destruct (p x) eqn: Heqn; intuition.
Qed.
#[global] Hint Resolve qand_sub_l : core.  

Lemma qand_sub_r : forall p q,
  qsub p q -> qand p q = p.
Proof.
    intros. apply functional_extensionality. intros.
    bdestruct (qand p q x); intuition.
    unfold qsub in H. specialize (H x).
    destruct (p x) eqn: Heqn; intuition.
Qed.
#[global] Hint Resolve qand_sub_r : core. 


(* qor *)

Lemma qor_idempetic: forall p,
  qor p p = p.
Proof.
    intros. unfold qor. apply functional_extensionality.
    intros. intuition.
    destruct (p x) eqn: Heq. auto. auto.
Qed.
#[global] Hint Resolve qor_idempetic : core. 


 Lemma qor_true_iff: forall q1 q2 x, 
  (qor q1 q2) x = true <-> (q1 x = true \/ q2 x = true).
Proof.
    intros. split.
    + intros. bdestruct (qor q1 q2 x); intuition.
    + intros. bdestruct (qor q1 q2 x); intuition.
Qed.
#[global] Hint Resolve qor_true_iff : core.  

Lemma qor_sub_id: forall q1 q2,
    qsub q1 q2 ->
    qor q1 q2 = q2.
Proof.
    intros. unfold qsub in H.  apply functional_extensionality.
    intros. specialize (H x). bdestruct (qor q1 q2 x); intuition.
    destruct (q1 x) eqn: Heq. intuition. 
    destruct (q2 x) eqn: Heq1. intuition. auto. 
Qed.
#[global] Hint Resolve qor_sub_id : core.  

Lemma qor_commutative: forall p q,
    qor p q = qor q p.
Proof.
    intros. unfold qor. apply functional_extensionality.
    intros. intuition.
Qed.

Lemma qor_associative: forall p q s,
  qor (qor p q) s = 
  qor p (qor q s).
Proof.
    intros. unfold qor. apply functional_extensionality.
    intros. erewrite orb_assoc. auto.
Qed.

(* qsub *)
Lemma qsub_refl: forall q,
    qsub q q.
Proof. 
    intros. unfold qsub. intros. auto.
Qed.
#[global] Hint Resolve qsub_refl : core.

Lemma qsub_trans: forall q1 q2 q3,
    qsub q1 q2 ->
    qsub q2 q3 ->
    qsub q1 q3.
Proof. 
    intros. unfold qsub in *. intros.
    specialize H with x. intuition.
Qed.

Lemma qsub_one: forall q x,
    q x = true <->
    qsub (qone x) q.
Proof.
    intros. split; intros.
    + unfold qsub. intros.
    bdestruct (qone x x0); intuition. subst. auto.
    +  unfold qsub in H. specialize (H x).
    bdestruct (qone x x); intuition.
Qed.
#[global] Hint Resolve qsub_one : core.

(* qand; qsub *)

Lemma qand_sub_mono_l: forall q1 q2 q3,
    qsub q1 q2 ->
    qsub (qand q1 q3) (qand q2 q3).
Proof.
    unfold qsub in *. intros. 
    bdestruct (qand q2 q3 x); bdestruct (qand q1 q3 x); intuition. 
Qed.
#[global] Hint Resolve qand_sub_mono_l : core.

Lemma qand_sub_mono_bi: forall q1 q2 q3 q4,
    qsub q1 q2 ->
    qsub q3 q4 ->
    qsub (qand q1 q3) (qand q2 q4).
Proof.
    unfold qsub in *. intros.
    specialize (H x).  specialize (H0 x). 
    bdestruct (qand q1 q3 x). intuition.
    apply qand_true_iff. intuition.
    discriminate.
Qed.
#[global] Hint Resolve qand_sub_mono_bi : core.

Lemma qand_sub_empty: forall q1 q2 q3,
    qand q2 q3 = qempty ->
    qsub q1 q2 ->
    qand q1 q3 = qempty.
Proof.
  intros.
  assert (qsub (qand q1 q3) (qand q2 q3)). eapply qand_sub_mono_l; eauto.
  rewrite H in H1. apply qsub_empty. auto.
Qed.
#[global] Hint Resolve qand_sub_empty : core.


Lemma qand_sub_empty_bi: forall q1 q2 q3 q4,
    qand q1 q2 = qempty ->
    qsub q3 q1 ->
    qsub q4 q2 ->
    qand q3 q4 = qempty.
Proof.
    intros. 
    assert (qsub (qand q3 q4)(qand q1 q2)). {
        eapply qand_sub_mono_bi; auto.
    }
    rewrite H in H2.
    eapply qsub_empty. auto.
Qed.
#[global] Hint Resolve qand_sub_empty_bi : core.
    
Lemma qdisj: forall q1 q2 x1 x2,
    qsub (qand q1 q2) qempty ->
    q1 x1 = true ->
    q2 x2 = true ->
    x1 <> x2.
Proof.  
    intros.  unfold qsub in H.
    specialize (H x1) as H2.
    specialize (H x2).
    bdestruct (qand q1 q2 x1); intuition.
    subst.  intuition.
Qed.

Lemma qsub_sub_and_r: forall q q1 q2,
    qsub q1 q2 ->
    qsub (qand q q1) (qand q q2).
Proof. 
    intros. unfold qsub in  *; intros. specialize (H x).
    bdestruct (qand q q1 x); intuition; bdestruct (qand q q2 x); intuition.
Qed.
#[global] Hint Resolve qsub_sub_and_r : core.

(* qor; qsub *)

Lemma qsub_or_l: forall q1 q2,
    qsub q1 (qor q1 q2).
Proof.
    intros. unfold qsub, qor. intros. intuition.
Qed.
#[global] Hint Resolve qsub_or_l : core.


Lemma qsub_or_r: forall q1 q2,
    qsub q2 (qor q1 q2).
Proof.
    intros. unfold qsub, qor. intros. intuition.
Qed.
#[global] Hint Resolve qsub_or_r : core.

Lemma qsub_sub_or_l: forall q1 q2 q3,
    qsub q1 q3 ->
    qsub q2 q3 ->
    qsub (qor q1 q2) q3.
Proof.
    intros. unfold qsub in *. intros.
    specialize H with x. specialize H0 with x.
    bdestruct (qor q1 q2 x); intuition.
Qed.
#[global] Hint Resolve qsub_sub_or_l : core.

Lemma qsub_sub_or: forall q1 q2 q3,
    qsub q1 q2 ->
    qsub (qor q1 q3) (qor q2 q3).
Proof. 
    intros. unfold qsub in *. intros.
    bdestruct (qor q1 q3 x); bdestruct (qor q2 q3 x); intuition.
Qed.    
#[global] Hint Resolve qsub_sub_or : core.

Lemma qsub_or_upb: forall q1 q2 q3,
    qsub (qor q1 q2) q3 ->
    (qsub q1 q3 /\ qsub q2 q3).
Proof. 
    intros. intuition; unfold qsub in *; intros;
    specialize (H x);
    bdestruct (qor q1 q2 x); intuition.
Qed.

Lemma qsub_sub_and: forall q1 q2 q,
  qsub q1 q2 ->
  qsub (qand q1 q) (qand q2 q).
Proof.
    intros. unfold qsub in *. intros.
    bdestruct (qand q1 q x); bdestruct (qand q2 q x); intuition.
Qed.
#[global] Hint Resolve qsub_sub_and : core.

Lemma qsub_and_l1: forall q1 q2,
    qsub (qand q1 q2) q1.
Proof.
    intros. unfold qsub. intros.
    bdestruct (qand q1 q2 x); intuition.
Qed.
#[global] Hint Resolve qsub_and_l1 : core.

Lemma qsub_and_l2: forall q1 q2,
    qsub (qand q1 q2) q2.
Proof. 
    intros. unfold qsub. intros.
    bdestruct (qand q1 q2 x); intuition.
Qed.
#[global] Hint Resolve qsub_and_l2 : core.

Lemma qsub_and_lb_l : forall q1 q2 q,
    qsub q1 q ->
    qsub (qand q1 q2) q.
Proof. 
    intros. unfold qsub. intros.
    bdestruct (qand q1 q2 x); intuition.
Qed.
#[global] Hint Resolve qsub_and_lb_l : core.

Lemma qsub_and_lb_r : forall q1 q2 q,
    qsub q2 q ->
    qsub (qand q1 q2) q.
Proof. 
    intros. unfold qsub. intros.
    bdestruct (qand q1 q2 x); intuition.
Qed.
#[global] Hint Resolve qsub_and_lb_r : core.

(*
Lemma qand_or_distribute: forall p q s, 
  qor (qand p q) s = (qand (qor p s) (qor q s)).
Proof.
  intros. unfold qor, qand.
  apply functional_extensionality. intros.
  destruct (p x) eqn:Heqn; destruct (q x) eqn: Heqn1; intuition;
  simpl. eauto with bool. erewrite andb_true_r; auto. erewrite andb_diag. auto.
Qed.*)

Lemma qand_or_distribute2: forall p q s, 
  qand (qor p q) s = (qor (qand p s) (qand q s)).
Proof.
  intros. unfold qor, qand.
  apply functional_extensionality. intros.
  destruct (p x) eqn:Heqn; destruct (q x) eqn: Heqn1; intuition;
  simpl. destruct (s x); intuition.
Qed.

Lemma qsub_cons {X}: forall (H H': list X),
    qsub (qdom H) (qdom (H'++H)).
Proof.
    intros. induction H'. simpl. apply qsub_refl. 
    simpl in *. unfold qsub in *. intros.
    specialize IHH' with x. intuition.
    bdestruct (qdom(H' ++ H) x); bdestruct (qdom(a :: H' ++ H) x); intuition.
    simpl in *. lia.
Qed.
#[global] Hint Resolve qsub_cons : core.
    
Lemma qsub_cons1 {X}: forall q (H H' : list X),
    qsub q (qdom H) ->
    qsub q (qdom (H'++H)).
Proof. 
    intros. unfold qsub in *. intros.
    specialize H0 with x. intuition.
    bdestruct (qdom H x); bdestruct (qdom (H' ++ H) x); intuition. 
    assert ((length H)  <= length (H' ++ H)). { auto. }
    lia.
Qed.
#[global] Hint Resolve qsub_cons1 : core.

Lemma qsub_cons2 {X}: forall q (H: list X) v,
    qsub q (qdom H) ->
    qsub q (qdom (v::H)).
Proof.
    intros. replace (qdom (v:: H)) with (qdom ([v] ++  H)); auto.
Qed.
#[global] Hint Resolve qsub_cons2 : core.



Lemma qsub_one_dom {X}: forall (H: list X) x,
    x < length H <->
    qsub (qone x) (qdom H).
Proof.
    intros. split.
    + intros. unfold qsub. intros. 
    bdestruct (qone x x0); bdestruct (qdom H x0); intuition.
    + intros. unfold qsub in H0. specialize (H0 x).
      bdestruct (qone x x); intuition.
      unfold qdom in H2.
      bdestruct (x <? length H); intuition. 
Qed.
#[global] Hint Resolve qsub_one_dom : core.


Lemma qsub_equiv_l: forall q1 q2,
    qsub q1 q2 ->
    qsub q2 q1 ->
    q1 = q2.
Proof. 
    intros. apply functional_extensionality.
    unfold qsub in *. intros.
    specialize (H x). specialize (H0 x).
    destruct (q1 x) eqn: Henq; destruct (q2 x) eqn: Heqn1; intuition.   
Qed.

Lemma qsub_equiv_r: forall q1 q2,
    q1 = q2 ->
    (qsub q1 q2 /\ qsub q2 q1).
Proof. 
    intros. intuition; rewrite H; auto. 
Qed.
