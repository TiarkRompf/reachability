Require Export Arith.EqNat.
Require Export Arith.Le.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Program.Equality.
Require Import Coq.Lists.List.
Require Import Psatz.
Require Import ZArith.
Require Import Coq.Arith.Compare_dec.
Import ListNotations.

Require Import vars.
Require Import env.
Require Import tactics.
Require Import NatSets.
Require Import setfacts.
Require Import qualifiers.

Import QualNotations.
Local Open Scope qualifiers.

Require Import lambda_star.

Import OpeningNotations.
Local Open Scope opening.
Import SubstitutionNotations.
Local Open Scope substitutions.

Import NatSet.F.

Lemma qglb_increase_fresh_equal : forall {dx dx' φ' l X},
  dx' ⊓ φ' = dx ->
  closed_qual 0 0 l dx' ->
  dx' ⊓ (φ' ⊔ qset X {}N {}N) = dx.
Proof.
  intros. inversion H0. subst. apply bound_0_empty in H1, H2.
  subst. destruct φ'. simpl in *. do 4 rewrite inter_empty_left. rewrite empty_union_right. reflexivity.
Qed.


Lemma subst1_preserves_separation_equal : forall {df d1 Tx dx dx' Γ Σ φ},
    dx' ⊓ φ = dx ->
    closed_qual 0 0 (length Σ) dx' ->
    df ⊑ φ -> d1 ⊑ φ ->
    saturated (Γ ++ [(Tx, dx)]) Σ d1 ->
    saturated (Γ ++ [(Tx, dx)]) Σ df ->
    {0 |-> dx' }ᵈ df ⊓ {0 |-> dx' }ᵈ d1 = {0 |-> dx' }ᵈ (df ⊓ d1).
  intros. destruct df as [ff bf lf]. destruct d1 as [f1 b1 l1]. destruct dx' as [fx' bx' lx'].
  destruct φ as [fp bp lp]. inversion H0. subst. apply bound_0_empty in H11, H12.
  subst. simpl.
  destruct (mem 0 ff) eqn:Hmem0ff; destruct (mem 0 f1) eqn:Hmem0f1; simpl; rewrite NatSetFacts.inter_b;
    rewrite Hmem0ff; rewrite Hmem0f1; simpl.
  - (*0 ∈ df, 0 ∈ d1 : this is trivial since we substitute the first variable for a closed value. The case for general
      substitution would require more careful reasoning. *)
    f_equal; try fnsetdec. repeat rewrite empty_union_right.
    apply NatSet.eq_if_Equal. apply inter_unsplice_0.
  - (* 0 ∈ df, 0 ∉ d1 *) f_equal; try fnsetdec. repeat rewrite empty_union_right.
    apply NatSet.eq_if_Equal. apply inter_unsplice_0.
    (* the interesting bit is reasoning about the overlap, this requires the extra assumptions about
       saturation of the sets and the boundedness of the context. *)
    apply NatSet.eq_if_Equal.
    setoid_rewrite NatSetProperties.union_inter_1.    
    specialize (saturated0 Hmem0ff H4) as Hlx.
    assert (Hl1 : inter lx' l1 [<=] lf). { simpl in H2. intuition. fnsetdec. }
    fnsetdec. 
  - (* 0 ∉ df, 0 ∈ d1, analogous to the previous case *)
    f_equal; try fnsetdec. repeat rewrite empty_union_right.
    apply NatSet.eq_if_Equal. apply inter_unsplice_0.
    apply NatSet.eq_if_Equal. rewrite NatSetProperties.inter_sym.
    setoid_rewrite NatSetProperties.union_inter_1.
    specialize (saturated0 Hmem0f1 H3) as Hlx.
    assert (Hl1 : inter lx' lf [<=] l1). { simpl in H1. intuition. fnsetdec. }
    fnsetdec.
  - (* 0 ∉ df, 0 ∉ d1 : trivial, since the substitution has no effect (other than unsplicing the sets) *)
    f_equal; try fnsetdec. apply NatSet.eq_if_Equal. apply inter_unsplice_0.
Qed.


Lemma subqual_qmem : forall v d d', 
  qmem v d ->
  d ⊑ d' ->
  qmem v d'.
Proof.
  intros. unfold qmem in *. destruct d. destruct d'. inversion H0; destruct H2. destruct v.
  - destruct v. fnsetdec. fnsetdec.
  - fnsetdec.
Qed.


Lemma qstp_saturated : forall {Γ Σ d d'},
  saturated Γ Σ d' ->
  qstp Γ Σ d d'   ->
  saturated Γ Σ d.
Proof.
  intros. unfold saturated in *. inversion H0; subst. intros.
  eapply subqual_qmem in H3; eauto. specialize (H x H3). inversion H; subst. econstructor; eauto. 
Abort.


Lemma closed_qual_qlub_inv : forall {b f l d1 d2}, closed_qual b f l (d1 ⊔ d2) ->
  closed_qual b f l d1 /\ closed_qual b f l d2.
Proof.
  intros. destruct d1, d2. inversion H; subst. apply bound_union in H6, H7, H8.
  split; constructor; intuition.
Qed.


Lemma qlub_empty_inversion : forall {d1 d2}, 
  (d1 ⊔ d2) = ∅ ->
  d1 = ∅ /\ (d2 = ∅).
Proof.
  intros. destruct d1, d2. simpl in H. inversion H.
  rewrite H1 in H2. rewrite H2 in H3.
  symmetry in H1, H2, H3; apply union_empty_inv in H1, H2, H3.
  intuition; subst; rewrite empty_union_left; auto.
Qed.

Lemma qlub_just_fv_inversion : forall {d1 d2 i},
  (d1 ⊔ d2) = just_fv i ->
  (d1 = ∅ \/ d1 = just_fv i) /\ (d2 = ∅ \/ d2 = just_fv i).
Proof.
  intros. destruct d1, d2; unfold just_fv in H; simpl in H. 
  inversion H. rewrite H2 in H3. symmetry in H2, H3. apply union_empty_inv in H2, H3. destruct H2, H3; subst. 
  rewrite setfacts.empty_union_left in *.
  symmetry in H1. 
  (* true but not necessary anymore *)  
Abort.


Lemma singleton_subset_in_inv : forall x s, In x s -> singleton x [<=] s.
Proof. intros. fnsetdec. Qed.

Lemma singleton_in_union_inversion: forall i s1 s2,
  singleton i [<=] (union s1 s2) ->
  singleton i [<=] s1 \/ singleton i [<=] s2.
Proof.
  intros. apply setfacts.singleton_subset_in in H. apply union_1 in H. destruct H.
  left. apply singleton_subset_in_inv; auto. right. apply singleton_subset_in_inv; auto.
Qed.

Lemma just_fv_subqual_qlub_inversion : forall i q1 q2,
  (just_fv i) ⊑ (q1 ⊔ q2) ->
  (just_fv i) ⊑ q1 \/ (just_fv i) ⊑ q2.
Proof.
  intros. unfold just_fv in *. destruct q1, q2. simpl in *.
  intuition. apply singleton_in_union_inversion in H0. destruct H0.
  left. intuition. right. intuition.
Qed.

Lemma just_bv_subqual_qlub_inversion : forall i q1 q2,
  (just_bv i) ⊑ (q1 ⊔ q2) ->
  (just_bv i) ⊑ q1 \/ (just_bv i) ⊑ q2.
Proof.
  intros. unfold just_bv in *. destruct q1, q2. simpl in *.
  intuition. apply singleton_in_union_inversion in H. destruct H.
  left. intuition. right. intuition.
Qed.


Lemma just_loc_subqual_qlub_inversion : forall i q1 q2,
  (just_loc i) ⊑ (q1 ⊔ q2) ->
  (just_loc i) ⊑ q1 \/ (just_loc i) ⊑ q2.
Proof.
  intros. unfold just_loc in *. destruct q1, q2. simpl in *.
  intuition. apply singleton_in_union_inversion in H2. destruct H2.
  left. intuition. right. intuition.
Qed.

Lemma subqual_qglb_lr : forall d1 d1' d2 d2',
  d1 ⊑ d1' ->
  d2 ⊑ d2' ->
  (d1 ⊓ d2) ⊑ (d1' ⊓ d2').
Proof.
  intros. destruct d1, d2, d1', d2'. simpl in *. qdec.
Qed.