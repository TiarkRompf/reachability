Require Export Arith.EqNat.
Require Export PeanoNat.
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
Require Import nats.
Require Import qualifiers.
Require Import boolean.
Require Import lang.
Require Import qenv.
Require Import ops.
Require Import lemmas.
Require Import killsep.
Require Import rules.

Import QualNotations.
Local Open Scope qualifiers.
Import OpeningNotations.
Local Open Scope opening.

Import SplicingNotations.
Local Open Scope splicing.
Import SubstitutionNotations.
Local Open Scope substitutions.




Lemma weaken_qstp_gen : forall {Γ1 Γ2 Σ d1 d2},
    qstp (Γ1 ++ Γ2) Σ d1 d2 ->
    forall T', qstp ((Γ1 ↑ᴳ ‖Γ2‖) ++ T' :: Γ2) Σ (d1 ↑ᵈ ‖Γ2‖) (d2 ↑ᵈ ‖Γ2‖).
Proof.
  intros Γ1 Γ2 Σ d1 d2 HSTP. remember (Γ1 ++ Γ2) as Γ. generalize dependent Γ1. induction HSTP; intros Γ1 HeqG T'; subst.
  - constructor. apply subqual_splice_lr'. auto. apply splice_qual_closed'.
    rewrite app_length in *. unfold splice_tenv. erewrite splice_env_length; eauto.
  - rewrite splice_qual_qor_dist. bdestruct (f <? ‖Γ2‖).
    * rewrite splice_qual_just_fv_lt; auto. erewrite @splice_qual_id with (d:=df).
      eapply qs_self; eauto. rewrite indexr_skips. rewrite indexr_skips in H. rewrite indexr_skip. eauto.
      1-3: simpl; lia. eapply closed_qual_monotone; eauto; lia.
    * rewrite splice_qual_just_fv_ge; auto.
      eapply qs_self; eauto. rewrite <- indexr_insert_ge; auto.
      eapply @indexr_splice_tenv with (k:=‖Γ2‖) in H; auto. simpl in H. eauto.
      eapply splice_qual_closed''; eauto.
  - rewrite splice_qual_qor_dist. bdestruct (f <? ‖Γ2‖).
    * rewrite splice_qual_just_fv_lt; auto. erewrite @splice_qual_id with (d:=df).
      eapply qs_self_all; eauto. rewrite indexr_skips. rewrite indexr_skips in H. rewrite indexr_skip. eauto.
      1-3: simpl; lia.  eapply closed_qual_monotone; eauto; lia.
    * rewrite splice_qual_just_fv_ge; auto.
      eapply qs_self_all; eauto. rewrite <- indexr_insert_ge; auto.
      eapply @indexr_splice_tenv with (k:=‖Γ2‖) in H; auto. simpl in H. eauto.
      eapply splice_qual_closed''; eauto.
  - bdestruct (x <? ‖Γ2‖).
    * rewrite splice_qual_just_fv_lt; auto. erewrite @splice_qual_id with (d:=q1).
      eapply qs_qvar; eauto. rewrite indexr_skips. rewrite indexr_skips in H. rewrite indexr_skip. eauto.
      1-3: simpl; lia.  eapply closed_qual_monotone; eauto; lia.
    * rewrite splice_qual_just_fv_ge; auto.
      eapply qs_qvar. rewrite <- indexr_insert_ge; auto.
      eapply @indexr_splice_tenv with (k:=‖Γ2‖) in H; auto. simpl in H. eauto.
      eapply splice_ty_closed''; eauto. eapply splice_qual_closed''; eauto.
      rewrite <- not_fresh_splice_iff. auto.
  - bdestruct (x <? ‖Γ2‖).
    * rewrite splice_qual_just_fv_lt; auto. erewrite @splice_qual_id with (d:=q1).
      eapply qs_qvar_ty; eauto. rewrite indexr_skips. rewrite indexr_skips in H. rewrite indexr_skip. eauto.
      1-3: simpl; lia.  eapply closed_qual_monotone; eauto; lia.
    * rewrite splice_qual_just_fv_ge; auto.
      eapply qs_qvar_ty. rewrite <- indexr_insert_ge; auto.
      eapply @indexr_splice_ty_tenv with (k:=‖Γ2‖) in H; auto. simpl in H. eauto.
      eapply splice_ty_closed''; eauto. eapply splice_qual_closed''; eauto.
      rewrite <- not_fresh_splice_iff. auto.
  - repeat rewrite splice_qual_qor_dist. eapply qs_cong.
    eapply IHHSTP. auto. apply splice_qual_closed'. rewrite app_length in *. unfold splice_tenv. erewrite splice_env_length; eauto.
  - eapply qs_trans; eauto.
Qed.

Lemma weaken_qstp : forall {Γ Σ d1 d2}, qstp Γ Σ d1 d2 -> forall T', qstp (T' :: Γ) Σ d1 d2.
  intros Γ Σ d1 d2 HST. specialize (@weaken_qstp_gen [] Γ Σ d1 d2) as Hsp. simpl in *.
  specialize (Hsp HST). intros. specialize (Hsp T'). apply qstp_closed in HST. intuition.
  replace (d1 ↑ᵈ ‖Γ‖) with d1 in Hsp. replace (d2 ↑ᵈ ‖Γ‖) with d2 in Hsp. intuition.
  1,2 : erewrite  splice_qual_id; eauto.
Qed.

Lemma weaken_qstp' : forall {Γ Σ d1 d2}, qstp Γ Σ d1 d2 -> forall Γ', qstp (Γ' ++ Γ) Σ d1 d2.
  intros. induction Γ'.
  - simpl. auto.
  - replace ((a :: Γ') ++ Γ) with (a :: (Γ' ++ Γ)).
    apply weaken_qstp. auto. simpl. auto.
Qed.

Lemma weaken_qstp_store : forall {Γ Σ d1 d2}, qstp Γ Σ d1 d2 -> forall {Σ'}, qstp Γ (Σ' ++ Σ) d1 d2.
  intros. induction H.
  - apply qs_sq; auto. rewrite app_length. eapply closed_qual_monotone; eauto. lia.
  - eapply qs_self; eauto. erewrite app_length. eapply closed_qual_monotone; eauto. lia.
  - eapply qs_self_all; eauto. erewrite app_length. eapply closed_qual_monotone; eauto. lia.
  - eapply qs_qvar; eauto. all : erewrite app_length. eapply closed_ty_monotone; eauto. lia. eapply closed_qual_monotone; eauto. lia.
  - eapply qs_qvar_ty; eauto. all : erewrite app_length. eapply closed_ty_monotone; eauto. lia. eapply closed_qual_monotone; eauto. lia.
  - eapply qs_cong; eauto. rewrite app_length. eapply closed_qual_monotone; eauto. lia.
  - eapply qs_trans; eauto.
Qed.

Lemma weaken_2D_qstp_store : forall {Γ Σ d1 d2}, qstp Γ Σ d1 d2 -> forall {Σ'}, ‖Σ'‖ >= ‖Σ‖ -> qstp Γ (Σ') d1 d2.
Proof.
  intros Γ Σ d1 d2 H. induction H; intros.
  - apply qs_sq; auto. eapply closed_qual_monotone; eauto.
  - eapply qs_self; eauto. eapply closed_qual_monotone; eauto.
  - eapply qs_self_all; eauto. eapply closed_qual_monotone; eauto.
  - eapply qs_qvar; eauto. eapply closed_ty_monotone; eauto. eapply closed_qual_monotone; eauto.
  - eapply qs_qvar_ty; eauto. eapply closed_ty_monotone; eauto. eapply closed_qual_monotone; eauto.
  - eapply qs_cong; eauto. eapply closed_qual_monotone; eauto.
  - eapply qs_trans; eauto.
Qed.



(* the splice ϰ version is also provable, but it looks unnecessary *)
Lemma weaken_stp_gen : forall {Γ1 Γ2 Σ T1 d1 T2 d2}, stp (Γ1 ++ Γ2) Σ T1 d1 T2 d2 ->
    forall T', stp ((Γ1 ↑ᴳ ‖Γ2‖) ++ T' :: Γ2) Σ (T1 ↑ᵀ ‖Γ2‖) (d1 ↑ᵈ ‖Γ2‖) (T2 ↑ᵀ ‖Γ2‖) (d2 ↑ᵈ ‖Γ2‖).
Proof. intros Γ1 Γ2 Σ T1 d1 T2 d2 Hstp T'. remember (Γ1 ++ Γ2)  as Γ. generalize dependent Γ1.  induction Hstp. intros Γ1.
  - (* TTop *) intros. subst. constructor.  rewrite app_length in *. rewrite splice_env_length in *; auto. simpl.
    replace (‖ Γ1 ‖ + S (‖ Γ2 ‖)) with (S ((‖ Γ1 ‖) +  (‖ Γ2 ‖))). eapply splice_ty_closed; eauto. lia.
    eapply weaken_qstp_gen; auto.
  - (* TVarF x *)  intros; subst. simpl. qual_destruct v.
    destruct (le_lt_dec (‖ Γ2 ‖) x ); destruct fr; econstructor; auto.
      rewrite <- indexr_insert_ge; eauto. eapply indexr_splice_tenv; eauto. eapply weaken_qstp_gen; eauto.
      rewrite <- indexr_insert_ge; eauto. eapply indexr_splice_ty_tenv; eauto. eapply weaken_qstp_gen; eauto.
      1,3: rewrite indexr_skips in H; auto; rewrite indexr_skips. 1,3: rewrite indexr_skip; eauto. 1-2: lia. 1-2: simpl; lia. 1-2: eapply weaken_qstp_gen; eauto.
  - (* TVarF x trans *) intros; subst. simpl.  intuition. specialize (IHHstp Γ1 eq_refl).
     destruct (le_lt_dec (‖ Γ2 ‖)  x) eqn:Heq.
    * (* |Γ2| <= x < |Γ1|+|Γ2| *)
      econstructor; eauto.
      rewrite <- indexr_insert_ge; eauto.
      apply @indexr_splice_ty_tenv with(Γ1 := Γ1)(i := x)(Γ2 := Γ2)(k := ‖ Γ2 ‖)(du := d0) in H; eauto.
      erewrite splice_ty_id  in H; eauto. eapply closed_ty_monotone; eauto. lia.
      erewrite splice_ty_id in IHHstp.  auto. eapply closed_ty_monotone; eauto. lia.
    * (* |Γ2| > x *)  econstructor; eauto.
      erewrite indexr_skips in H. erewrite indexr_skips;  auto. erewrite  indexr_skip.
      apply H. lia. simpl. lia. lia.
      erewrite splice_ty_id in IHHstp; eauto.  eapply closed_ty_monotone; eauto.  lia.
  - (* TAll *) intros; subst.  assert (stp (Γ1 ++ Γ2) Σ (TAll d1 d2 T1 T2) d5 (TAll d3 d4 T3 T4) d6). { econstructor; eauto. }
    intuition.
    specialize (IHHstp1 Γ1).  specialize (IHHstp2 ((bind_ty, false, T3, d3) :: (bind_tm, true,(TAll d1 d2 T1 T2), {♦}) :: Γ1)). intuition.
    inversion H0. inversion H. subst. apply qstp_closed in H1 as H1'; intuition. econstructor; eauto; fold splice_ty.
    constructor. 5: constructor.
    1,2,5,6: apply splice_qual_closed'; auto; eapply closed_qual_monotone; eauto; rewrite app_length in*.
    5-8: apply splice_ty_closed'; auto; eapply closed_ty_monotone; eauto; rewrite app_length in*.

    1-8: rewrite app_length; erewrite splice_env_length; eauto; lia.

    eapply weaken_qstp_gen; eauto.
    erewrite app_length in *; eauto.
    repeat rewrite <- splice_ty_open'. repeat rewrite <- splice_qual_open'. simpl in H3.
    repeat rewrite idfun_inv in H3.
    repeat rewrite @open_ty'_len with (Γ:=(Γ1 ↑ᴳ ‖Γ2‖) ++ Γ2) (Γ':=Γ1++Γ2).
    repeat rewrite @openq'_len with (Γ:=(Γ1 ↑ᴳ ‖Γ2‖) ++ Γ2) (Γ':=Γ1++Γ2).
    replace ({♦} ↑ᵈ (‖ Γ2 ‖)) with ({♦}) in H3; auto.
    all: repeat rewrite app_length; rewrite splice_env_length; auto.
  - constructor. eapply weaken_qstp_gen. subst; auto.
  - intros. assert (stp Γ Σ (TRef q1 T1) d1 (TRef q2 T2) d2). { constructor; intuition. } subst.
    apply stp_closed in H2 as Hcl. intuition.
    inversion H3. inversion H4. subst. simpl.
    specialize (IHHstp1 Γ1). intuition.
    specialize (IHHstp2 Γ1). intuition.
    constructor. apply weaken_qstp_gen. subst; auto. auto.
    1,2 : rewrite splice_qual_empty in H6, H8; auto.
    1, 2: eapply weaken_qstp_gen; intuition.
  - assert (stp Γ Σ (TFun d1 d2 T1 T2) d5 (TFun d3 d4 T3 T4) d6). { constructor; intuition. } intros.
    subst. intuition. inversion H0; inversion H; subst. apply qstp_closed in H1 as Hcl. intuition.
    constructor; try fold splice_ty. 1-2: constructor.
    1,2,5,6 : apply splice_qual_closed'. 5-8 : apply splice_ty_closed'.
    1-8: rewrite app_length in *; rewrite splice_env_length in *; auto.
    apply weaken_qstp_gen. auto. auto.
    specialize (IHHstp1 Γ1). auto.
    specialize (IHHstp2 ((bind_tm, false,T3, d3) :: (bind_tm, true,(TFun d1 d2 T1 T2), {♦}) :: Γ1)). intuition.
    repeat rewrite <- splice_ty_open'. repeat rewrite <- splice_qual_open'. simpl in H5.
    repeat rewrite @open_ty'_len with (Γ:=(Γ1 ↑ᴳ ‖Γ2‖) ++ Γ2) (Γ':=Γ1++Γ2).
    repeat rewrite @openq'_len with (Γ:=(Γ1 ↑ᴳ ‖Γ2‖) ++ Γ2) (Γ':=Γ1++Γ2).
    replace ({♦} ↑ᵈ (‖ Γ2 ‖)) with ({♦}) in H5; auto.
    all: repeat rewrite app_length; rewrite splice_env_length; auto.
  - intros. specialize (IHHstp1 Γ1). specialize (IHHstp2 Γ1). intuition.
    eapply s_trans; eauto.
    Unshelve. all: apply 0.
Qed.


Lemma weaken_stp : forall {Γ Σ T1 d1 T2 d2}, stp Γ Σ T1 d1 T2 d2 -> forall T', stp (T' :: Γ) Σ T1 d1 T2 d2.
  intros Γ Σ T1 d1 T2 d2 HST. specialize (@weaken_stp_gen [] Γ Σ T1 d1 T2 d2) as Hsp. simpl in *.
  specialize (Hsp HST). intros. specialize (Hsp T'). apply stp_closed in HST. intuition.
  replace (T1 ↑ᵀ ‖Γ‖) with T1 in Hsp. replace (T2 ↑ᵀ ‖Γ‖) with T2 in Hsp.
  replace (d1 ↑ᵈ ‖Γ‖) with d1 in Hsp. replace (d2 ↑ᵈ ‖Γ‖) with d2 in Hsp. intuition.
  1,2 : erewrite  splice_qual_id; eauto.
  1,2 : erewrite splice_ty_id; eauto.
Qed.

Lemma weaken_stp' : forall {Γ Σ T1 d1 T2 d2}, stp Γ Σ T1 d1 T2 d2 -> forall Γ', stp (Γ' ++ Γ) Σ T1 d1 T2 d2.
  intros. induction Γ'.
  - simpl. auto.
  - replace ((a :: Γ') ++ Γ) with (a :: (Γ' ++ Γ)).
    apply weaken_stp. auto. simpl. auto.
Qed.



Lemma narrowing_qstp_gen : forall{Γ1 bd b U du Γ2 Σ d1 d2},
    qstp (Γ1 ++ (bd, b,U,du) :: Γ2) Σ d1 d2 -> (b = true -> (♦∈ du)) ->
    forall {V dv}, stp Γ2 Σ V dv U du ->
              qstp (Γ1 ++ (bd, b,V,dv) :: Γ2) Σ d1 d2.
  intros Γ1 bd b U du Γ2 Σ d1 d2 HST Hb. remember (Γ1 ++ (bd, b,U,du) :: Γ2) as Γ.
  generalize dependent Γ1; induction HST; intros; subst; intuition.
  - constructor. auto. rewrite app_length in *. simpl in *. auto.
  - eapply qs_self; eauto. destruct (PeanoNat.Nat.lt_trichotomy f (‖Γ2‖)) as [Hlen | [Hlen | Hlen] ].
    * rewrite indexr_skips. rewrite indexr_skips in H.
      rewrite indexr_skip.  rewrite indexr_skip in H. eauto. all: simpl; lia.
    * subst. rewrite indexr_skips in H; auto. rewrite indexr_head in H. inversion H. subst. intuition.
    * rewrite indexr_skips'; auto. rewrite indexr_skips' in H; auto.
  - eapply qs_self_all; eauto. destruct (PeanoNat.Nat.lt_trichotomy f (‖Γ2‖)) as [Hlen | [Hlen | Hlen] ].
    * rewrite indexr_skips. rewrite indexr_skips in H.
      rewrite indexr_skip.  rewrite indexr_skip in H. eauto. all: simpl; lia.
    * subst. rewrite indexr_skips in H; auto. rewrite indexr_head in H. inversion H. subst. intuition.
    * rewrite indexr_skips'; auto. rewrite indexr_skips' in H; auto.
  - destruct (PeanoNat.Nat.lt_trichotomy x (‖Γ2‖)) as [Hlen | [Hlen | Hlen] ].
    * eapply qs_qvar; eauto. rewrite indexr_skips. rewrite indexr_skips in H.
      rewrite indexr_skip.  rewrite indexr_skip in H. eauto. 1-4: simpl; lia.
    * subst.  pose (H':=H). rewrite indexr_skips in H'. rewrite indexr_head in H'. inversion H'. subst.
      eapply qs_trans. eapply qs_qvar. rewrite indexr_skips; auto. apply indexr_head.
      1,2 : apply stp_closed in H3; intuition.
      apply stp_qstp_inv in H3. eapply qstp_non_fresh; eauto.
      apply stp_qstp_inv in H3. eapply weaken_qstp'; auto. eapply weaken_qstp. auto. auto.
    * eapply qs_qvar; eauto. rewrite indexr_skips'; auto. rewrite indexr_skips' in H. eauto.
      simpl. lia.
  - destruct (PeanoNat.Nat.lt_trichotomy x (‖Γ2‖)) as [Hlen | [Hlen | Hlen] ].
    * eapply qs_qvar_ty; eauto. rewrite indexr_skips. rewrite indexr_skips in H.
      rewrite indexr_skip.  rewrite indexr_skip in H. eauto. 1-4: simpl; lia.
    * subst.  pose (H':=H). rewrite indexr_skips in H'. rewrite indexr_head in H'. inversion H'. subst.
      eapply qs_trans. eapply qs_qvar_ty. rewrite indexr_skips; auto. apply indexr_head.
      1,2 : apply stp_closed in H3; intuition.
      apply stp_qstp_inv in H3. eapply qstp_non_fresh; eauto.
      apply stp_qstp_inv in H3. eapply weaken_qstp'. auto. eapply weaken_qstp; auto. auto.
    * eapply qs_qvar_ty; eauto. rewrite indexr_skips'; auto. rewrite indexr_skips' in H. eauto.
      simpl. lia.
  - eapply qs_cong; eauto. rewrite app_length in *. simpl in *. auto.
  - eapply qs_trans; eauto.
Qed.

Lemma narrowing_stp_gen : forall{Γ1 b U du Γ2 Σ T1 d1 T2 d2},
  stp (Γ1 ++ (bind_tm, b,U,du) :: Γ2) Σ T1 d1 T2 d2 -> (b = true -> (♦∈ du)) ->
  forall {V dv}, (stp Γ2 Σ V dv U du) -> stp (Γ1 ++ (bind_tm, b,V,dv) :: Γ2) Σ T1 d1 T2 d2.
Proof. intros Γ1 b U du Γ2 Σ T1 d1 T2 d2 HST Hb. remember (Γ1 ++ (bind_tm, b,U,du) :: Γ2) as Γ.
  generalize dependent Γ1; induction HST; intros; auto.
  - (* TTop *) subst. constructor. rewrite app_length in *.  simpl in *. intuition. eapply narrowing_qstp_gen; eauto.
  - (* TVarF x refl *) subst. destruct (Nat.eqb x (length Γ2)) eqn: Heqn.
     + eapply s_tvar_refl; eauto. apply Nat.eqb_eq in Heqn. subst. eapply indexr_insert.
       eapply narrowing_qstp_gen; eauto.
     + eapply s_tvar_refl; eauto.
      eapply indexr_var_same. assumption. eassumption. eapply narrowing_qstp_gen; eauto.
  - (* TVarF x trans *) subst. destruct (Nat.eqb x (length Γ2)) eqn: Heqn.
       specialize (IHHST Γ1).  intuition.  specialize (H2 V dv).  intuition.
    +  eapply s_tvar_trans. apply Nat.eqb_eq in  Heqn; subst.
       erewrite  indexr_skips in  H; eauto. erewrite indexr_head in H.  inversion H. subst. apply H0.
       auto.
    +  eapply s_tvar_trans.  eapply indexr_var_same.  assumption. eassumption. apply H0. auto.
  - (* TAll *) rewrite HeqΓ in *. econstructor.
    subst. rewrite app_length in *. simpl in *. auto.
    subst. rewrite app_length in *. simpl in *. auto.
    eapply narrowing_qstp_gen; subst; eauto. eapply IHHST1; eauto.
    unfold open_ty' in *. unfold open_ty in *. unfold openq' in *. unfold openq in *.
    rewrite app_length in *. simpl in *.
    repeat rewrite app_comm_cons.
    specialize (IHHST2 ((bind_ty, false, T3, d3) :: (bind_tm, true, TAll d1 d2 T1 T2, {♦}) :: Γ1)). intuition.
  - subst. constructor. eapply narrowing_qstp_gen; eauto.
  - (* TRef *) subst. constructor. eapply narrowing_qstp_gen; eauto. auto. auto.
    1, 2: eapply narrowing_qstp_gen; subst; eauto.
  - rewrite HeqΓ in *. constructor.
    subst. rewrite app_length in *. simpl in *. auto.
    subst. rewrite app_length in *. simpl in *. auto.
    eapply narrowing_qstp_gen; subst; eauto. eapply IHHST1; eauto.
    unfold open_ty' in *. unfold openq' in *.
    rewrite app_length in *. simpl in *.
    repeat rewrite app_comm_cons.
    eapply IHHST2; eauto.
  - subst. specialize (IHHST1 Γ1).  specialize (IHHST2 Γ1). intuition.
    specialize (H0 V dv).  specialize (H1 V dv). intuition.  eapply s_trans; eauto.
  Unshelve. auto.
Qed.

Lemma narrowing_stp : forall{b U du Γ Σ T1 d1 T2 d2}, stp ((bind_tm, b,U,du) :: Γ) Σ T1 d1 T2 d2 -> (b = true -> (♦∈ du)) ->
    forall {V dv}, stp Γ Σ V dv U du -> stp ((bind_tm, b,V,dv) :: Γ) Σ T1 d1 T2 d2.
  intros. specialize (@narrowing_stp_gen [] b U du Γ Σ T1 d1 T2 d2) as narrow. simpl in *. eapply narrow; eauto.
Qed.

Lemma narrowing_qstp_ty_gen : forall{Γ1 bd U du Γ2 Σ d1 d2},
    qstp (Γ1 ++ (bind_ty, bd,U,du) :: Γ2) Σ d1 d2 ->
    forall {V dv}, stp Γ2 Σ V dv U du ->
            qstp (Γ1 ++ (bind_ty, bd,V,dv) :: Γ2) Σ d1 d2.
  intros Γ1 bd U du Γ2 Σ d1 d2 HST Hb. remember (Γ1 ++ (bind_ty, bd,U,du) :: Γ2) as Γ.
  generalize dependent Γ1; induction HST; intros; subst; auto.
  - constructor. auto. rewrite app_length in *. simpl in *. auto.
  - eapply qs_self; eauto. destruct (PeanoNat.Nat.lt_trichotomy f (‖Γ2‖)) as [Hlen | [Hlen | Hlen] ].
    * rewrite indexr_skips. rewrite indexr_skips in H.
      rewrite indexr_skip.  rewrite indexr_skip in H. eauto. all: simpl; lia.
    * subst. rewrite indexr_skips in H; auto. rewrite indexr_head in H. inversion H.
    * rewrite indexr_skips'; auto. rewrite indexr_skips' in H; auto.
  - eapply qs_self_all; eauto. destruct (PeanoNat.Nat.lt_trichotomy f (‖Γ2‖)) as [Hlen | [Hlen | Hlen] ].
    * rewrite indexr_skips. rewrite indexr_skips in H.
      rewrite indexr_skip.  rewrite indexr_skip in H. eauto. all: simpl; lia.
    * subst. rewrite indexr_skips in H; auto. rewrite indexr_head in H. inversion H.
    * rewrite indexr_skips'; auto. rewrite indexr_skips' in H; auto.
  - destruct (PeanoNat.Nat.lt_trichotomy x (‖Γ2‖)) as [Hlen | [Hlen | Hlen] ].
    * eapply qs_qvar; eauto. rewrite indexr_skips. rewrite indexr_skips in H.
      rewrite indexr_skip.  rewrite indexr_skip in H. eauto. 1-4: simpl; lia.
    * subst.  pose (H':=H). rewrite indexr_skips in H'. rewrite indexr_head in H'. inversion H'.
      simpl. lia.
    * eapply qs_qvar; eauto. rewrite indexr_skips'; auto. rewrite indexr_skips' in H. eauto.
      simpl. lia.
  - destruct (PeanoNat.Nat.lt_trichotomy x (‖Γ2‖)) as [Hlen | [Hlen | Hlen] ].
    * eapply qs_qvar_ty; eauto. rewrite indexr_skips. rewrite indexr_skips in H.
      rewrite indexr_skip.  rewrite indexr_skip in H. apply H. eauto. 1-4: simpl; lia.
    * subst. pose (H':=H). rewrite indexr_skips in H'. rewrite indexr_head in H'. inversion H'.
      subst.  eapply qs_trans. eapply qs_qvar_ty.
      rewrite indexr_skips; auto. apply indexr_head.
      1,2 : apply stp_closed in H3; intuition.
      apply stp_qstp_inv in H3. eapply qstp_non_fresh; eauto.
      apply stp_qstp_inv in H3. eapply weaken_qstp'; auto. eapply weaken_qstp; auto. auto.
    * eapply qs_qvar_ty; eauto. rewrite indexr_skips'; auto. rewrite indexr_skips' in H. eauto.
      simpl. lia.
  - eapply qs_cong; eauto. rewrite app_length in *. simpl in *. auto.
  - specialize (IHHST1 Γ1). intuition. specialize (H0 dv). intuition.
    specialize (IHHST2 Γ1). intuition. specialize (H0 dv). intuition.
    eapply qs_trans; eauto.
Qed.



Lemma weaken_stp_store : forall {Σ Γ T1 d1 T2 d2}, stp Γ Σ T1 d1 T2 d2 -> forall Σ', stp Γ (Σ' ++ Σ) T1 d1 T2 d2.
Proof. intros Σ Γ T1 d1 T2 d2 HSTP. induction HSTP; intros.
  + constructor; auto. eapply closed_ty_monotone; eauto. rewrite app_length. lia. apply weaken_qstp_store. auto.
  + econstructor; eauto. apply weaken_qstp_store. auto.
  + econstructor; eauto. eapply closed_ty_monotone; eauto. rewrite app_length. lia.
  + econstructor; eauto. eapply closed_ty_monotone in H; eauto. rewrite app_length. lia.
    eapply closed_ty_monotone in H0; eauto. rewrite app_length. lia.
    eapply weaken_qstp_store. intuition.
  + constructor. apply weaken_qstp_store. auto.
  + constructor; auto. apply weaken_qstp_store. auto.
    1, 2: eapply weaken_qstp_store; intuition.
  + constructor; auto. 1,2 : rewrite app_length; eapply closed_ty_monotone; eauto; lia.
    apply weaken_qstp_store. auto.
  + specialize (IHHSTP1 Σ'). specialize (IHHSTP2 Σ'). eapply s_trans in IHHSTP2; eauto.
Qed.

Lemma weaken_2D_stp_store_ext : forall {Σ Γ T1 d1 T2 d2}, stp Γ Σ T1 d1 T2 d2 -> forall {Σ'}, ‖Σ'‖ >= ‖Σ‖ ->  stp Γ Σ' T1 d1 T2 d2.
Proof.
  intros Σ Γ T1 d1 T2 d2 HSTP. induction HSTP; intros.
  - constructor; auto. eapply closed_ty_monotone; eauto. eapply weaken_2D_qstp_store; eauto.
  - econstructor; eauto. eapply weaken_2D_qstp_store; eauto.
  - econstructor; eauto. eapply closed_ty_monotone; eauto.
  - econstructor; eauto. eapply closed_ty_monotone in H; eauto. eapply closed_ty_monotone in H0; eauto. eapply weaken_2D_qstp_store; eauto.
  - constructor. eapply weaken_2D_qstp_store; eauto.
  - constructor; auto. eapply weaken_2D_qstp_store; eauto.
    1, 2: eapply weaken_2D_qstp_store; eauto.
  - constructor; auto. 1,2 : eapply closed_ty_monotone; eauto. eapply weaken_2D_qstp_store; eauto.
  - specialize (IHHSTP1 Σ' H). specialize (IHHSTP2 Σ' H). eapply s_trans; eauto.
Qed.


Lemma weaken_stp_store_ext : forall {Σ Γ T1 d1 T2 d2}, stp Γ Σ T1 d1 T2 d2 -> forall {Σ'}, Σ' ⊇ Σ ->  stp Γ Σ' T1 d1 T2 d2.
  intros. unfold extends in H0. destruct H0. subst. apply weaken_stp_store. auto.
Qed.

Lemma stp_shrink_var : forall {Γ Σ T1 d1 T2 d2}, stp Γ Σ T1 d1 T2 d2 -> forall {fr x}, x < ‖Γ‖ -> stp Γ Σ T1 ${fr}x T2 ${fr}x.
  intros. eapply stp_qual_irrelevance; eauto. apply qs_sq; auto. apply just_fv_closed. auto.
Qed.

Lemma narrowing_stp_ty_gen : forall{Γ1 b U du Γ2 Σ T1 d1 T2 d2},
      stp (Γ1 ++ ((bind_ty, b, U, du)) :: Γ2) Σ T1 d1 T2 d2 ->
      forall {V dv }, closed_ty  0 0 (‖ Σ ‖) V -> closed_qual  0 0 (‖ Σ ‖) dv ->
      (stp Γ2 Σ V dv U du) ->
      stp (Γ1 ++ ((bind_ty, b, V, dv)) :: Γ2) Σ T1 d1 T2 d2.
Proof. intros Γ1 b U du Γ2 Σ T1 d1 T2 d2 HST. remember (Γ1 ++ ((bind_ty, b, U, du)) :: Γ2) as Γ.
  generalize dependent Γ1; induction HST; intros; auto.
  - (* TTop *) subst. constructor. rewrite app_length in *.  simpl in *. intuition.
    eapply  narrowing_qstp_ty_gen; eauto.
  - (* TVarF x refl *) subst. destruct (Nat.eqb x  (‖ Γ2 ‖)) eqn: Heqn.
     + eapply s_tvar_refl; eauto. simpl in Heqn. apply Nat.eqb_eq in Heqn. subst. eapply indexr_insert.
       eapply narrowing_qstp_ty_gen; eauto.
     + eapply s_tvar_refl; eauto.  eapply indexr_var_same. assumption. eassumption. eapply narrowing_qstp_ty_gen; eauto.

  - (* TVarF x trans *) assert (stp Γ Σ $x d1 T2 d2). {
         econstructor; eauto.
       }
      subst. destruct (Nat.eqb x  (‖ Γ2 ‖)) eqn: Heqn.
     + apply Nat.eqb_eq  in  Heqn. subst.

       erewrite indexr_skips in H. erewrite indexr_head in H. inversion H. subst.
     econstructor; eauto.
     assert (indexr (‖ Γ2 ‖) (Γ1 ++ (bind_ty, false, V, dv) :: Γ2) = Some ((bind_ty, false, V, dv))). {
       erewrite indexr_skips. erewrite indexr_head. auto. simpl. lia.
     }
     apply H5.
     specialize (IHHST Γ1); intuition. specialize(H5 V dv); intuition.
     assert (stp (Γ1 ++ (bind_ty, false, V, dv) :: Γ2) Σ V dv T1 d0). {
       eapply weaken_stp'; eauto. eapply weaken_stp; eauto.
     }

     apply stp_qstp_inv in H6 as H6'.
     assert (stp (Γ1 ++ (bind_ty, false, V, dv) :: Γ2) Σ V d1 T1 d1). {
       assert (qstp (Γ1 ++ (bind_ty, false, V, dv) :: Γ2) Σ d1 d1). {
         apply qstp_refl; auto. apply qstp_closed in H6'; intuition.
       }
       eapply stp_qual_irrelevance; eauto.
     }
     eapply s_trans; eauto.  simpl. lia.
    +  specialize (IHHST Γ1). intuition.  specialize (H5 V dv). intuition.
       eapply s_tvar_trans.
       eapply indexr_var_same; eauto. auto. auto.

  - (* TAll *) rewrite HeqΓ in *. econstructor.
    subst. rewrite app_length in *. simpl in *. auto.
    subst. rewrite app_length in *. simpl in *. auto.
    eapply narrowing_qstp_ty_gen; subst; eauto. eapply IHHST1; eauto.
    specialize (IHHST2 ((bind_ty, false, T3, d3) :: (bind_tm, true, TAll d1 d2 T1 T2, {♦}) :: Γ1 )). intuition.
    specialize (H5 V dv). intuition.
    unfold open_ty' in *. unfold openq' in *.
    rewrite app_length in *. simpl in *.
    repeat rewrite app_comm_cons. auto.
  - (* TUnit *) subst. constructor. eapply narrowing_qstp_ty_gen; eauto.
  - (* TRef *) subst. constructor. eapply narrowing_qstp_ty_gen; eauto. auto. auto.
    1,2: eapply narrowing_qstp_ty_gen; subst; eauto.
  - (* TFUN *)  rewrite HeqΓ in *. constructor.
    subst. rewrite app_length in *. simpl in *. auto.
    subst. rewrite app_length in *. simpl in *. auto.
    eapply narrowing_qstp_ty_gen; subst; eauto. eapply IHHST1; eauto.
    unfold open_ty' in *. unfold openq' in *.
    rewrite app_length in *. simpl in *.
    repeat rewrite app_comm_cons.
    eapply IHHST2; eauto.
  - subst. specialize (IHHST1 Γ1).  specialize (IHHST2 Γ1). intuition.
    specialize (H2 V dv). specialize (H3 V dv). intuition.  eapply s_trans; eauto.
Qed.

Lemma narrowing_stp_ty : forall{bd U du Γ Σ T1 d1 T2 d2}, stp (((bind_ty, bd, U, du)) :: Γ) Σ T1 d1 T2 d2 ->
  forall {V dv}, closed_ty 0 0 (length Σ) V -> closed_Qual 0 0 (length Σ) dv↑ ->  stp Γ Σ V dv U du ->
    stp (((bind_ty, bd, V, dv)) :: Γ) Σ T1 d1 T2 d2.
   intros. specialize (@narrowing_stp_ty_gen [] bd U du Γ Σ T1 d1 T2 d2) as narrow. simpl in narrow. apply narrow; auto.
Qed.

Lemma stp_scale_qor : forall {Γ Σ T1 d1 T2 d2}, stp Γ Σ T1 d1 T2 d2 -> forall {q}, closed_Qual 0 (‖Γ‖) (‖Σ‖) q↑ -> stp Γ Σ T1 (d1 ⊔ q) T2 (d2 ⊔ q).
  intros. eapply stp_qual_irrelevance; auto. eauto. apply stp_qstp_inv in H. replace (d1 ⊔ q) with (q ⊔ d1). replace (d2 ⊔ q) with (q ⊔ d2). eauto.
all: apply Q_lift_eq; Qcrush.
Qed.

Lemma stp_scale_qqplus : forall {Γ Σ T1 d1 T2 d2}, stp Γ Σ T1 d1 T2 d2 -> forall {d}, closed_Qual 0 (‖Γ‖) (‖Σ‖) d↑ -> stp Γ Σ T1 (d1 ⋓ d) T2 (d2 ⋓ d).
#[local] Hint Resolve is_true_reflect : bdestruct.
  intros. bdestruct (♦∈? d1); bdestruct (♦∈? d2).
#[local] Remove Hints is_true_reflect : bdestruct.
  - repeat rewrite qqplus_fresh; auto. apply stp_scale_qor; auto.
  - apply stp_qstp_inv in H. specialize (qstp_non_fresh H H2) as Hc. unfold_q. contradiction.
  - rewrite @qqplus_fresh with (d:=d2); auto. unfold qqplus. apply Is_true_eq_false in H1. rewrite H1.
    eapply s_trans; eauto. apply stp_refl. apply stp_closed in H. intuition.
    apply qs_sq. Qcrush. apply stp_closed in H. apply closed_Qual_qor; intuition.
  - unfold qqplus. apply Is_true_eq_false in H1,H2. rewrite H1,H2. auto.
Qed.


Fixpoint has_type_closed  {Γ φ Σ t T d} (ht : has_type Γ φ Σ t T d) :
  closed_Qual 0 (‖Γ‖) (‖Σ‖) φ↑ /\
  closed_tm 0 (‖Γ‖) (‖Σ‖) t /\
  closed_ty 0 (‖Γ‖) (‖Σ‖) T /\
  closed_Qual 0 (‖Γ‖) (‖Σ‖) d↑.
Proof.
  destruct ht; intuition; try apply has_type_closed in ht; try apply has_type_closed in ht1;
  try apply has_type_closed in ht2; intuition; eauto;
    try match goal with
    | [ H : closed_ty _ _ _ (_ _ _ _ ?T)  |- closed_ty _ _ _ (?T <~ᵀ _ ~ _; _ ~ _) ] =>
       inversion H; subst; unfold open_ty; eapply closed_ty_open2; eauto
    | [ H : closed_ty _ _ _ (_ _ ?q _ _)  |- closed_Qual _ _ _ (?q <~ᵈ _ ; _ )↑ ] =>
       inversion H; subst; unfold openq; eapply closed_qual_open2; eauto
    end.
  - constructor. apply indexr_var_some' in H. auto.
  - apply indexr_var_some' in H. eapply closed_ty_monotone; eauto. lia.
  - constructor. apply sindexr_var_some' in H0; destruct H0. auto.
  - econstructor. eapply closed_ty_monotone; eauto; lia.
    eapply closed_qual_monotone; eauto; lia.
  - inversion H3. intuition.
  - apply stp_closed in H. intuition.
  - apply stp_closed in H. intuition.
Qed.


Lemma qstp_empty : forall {Σ q1 q2}, qstp [] Σ q1 q2 -> q1 ⊑↑ q2.
  intros. remember [] as Γ. induction H; subst; auto; try solve [simpl in H; discriminate]. auto.
  intuition. Qcrush.
Qed.



Fixpoint has_type_filter {Γ φ Σ t T d} (ht : has_type Γ φ Σ t T d) {struct ht} : d ⊑↑ φ ⊔ {♦}.
Proof.
  destruct ht; intuition.
  - Qcrush.
  - specialize (has_type_closed ht) as Hc. specialize (has_type_filter _ _ _ _ _ _ ht). intuition.
    assert (d1 ⊑↑ φ ⊔ {♦}). Qcrush.
    assert (d2 <~ᵈ ∅; ∅ ⊑↑ φ ⊔ {♦}). Qcrush.
    assert (closed_Qual 0 (‖ Γ ‖) (‖ Σ ‖) (φ ⊔ {♦}) ↑). Qcrush.
    eapply openq_subqual; eauto.
  - specialize (has_type_closed ht) as Hc. specialize (has_type_filter _ _ _ _ _ _ ht). intuition.
    assert (d1 ⊑↑ φ ⊔ {♦}). Qcrush.
    assert (d2 <~ᵈ ∅; ∅ ⊑↑ φ ⊔ {♦}). Qcrush.
    assert (closed_Qual 0 (‖ Γ ‖) (‖ Σ ‖) (φ ⊔ {♦}) ↑). Qcrush.
    eapply openq_subqual; eauto.
  - Qcrush.
  - Qcrush.
  - specialize (has_type_closed ht1) as Hc1. specialize (has_type_closed ht2) as Hc2. intuition. apply (qdiff_local_loc_prop) in H2. destruct H2.
    inversion H7; subst. specialize (has_type_filter _ _ _ _ _ _ ht1) as Hfl1.
    specialize (has_type_filter _ _ _ _ _ _ ht2) as Hfl2.
    assert (d2 <~ᵈ ∅; ∅ ⊑↑ φ ⊔ {♦}). Qcrush.
    assert (closed_Qual 0 (‖ Γ ‖) (‖ Σ ‖) (φ ⊔ {♦}) ↑). Qcrush.
    assert (d1 ⊑↑ φ ⊔ {♦}). eapply Subq_trans; eauto.
    eapply openq_subqual; eauto.
  - specialize (has_type_closed ht1) as Hc1. specialize (has_type_closed ht2) as Hc2. intuition. apply (qdiff_local_loc_prop) in H3. destruct H3.
    inversion H10. subst. specialize (has_type_filter _ _ _ _ _ _ ht1) as Hfl1.
    specialize (has_type_filter _ _ _ _ _ _ ht2) as Hfl2.
    assert (d2 <~ᵈ ∅; ∅ ⊑↑ (φ) ⊔ {♦}). Qcrush.
    assert (closed_Qual 0 (‖ Γ ‖) (‖ Σ ‖) ((φ) ⊔ {♦}) ↑). Qcrush.
    assert (d1 ⊑↑ (φ) ⊔ {♦}). eapply Subq_trans; eauto. eapply openq_subqual; eauto.
  - Qcrush.
  - specialize (has_type_filter _ _ _ _ _ _ ht2). auto.
  - specialize (has_type_filter _ _ _ _ _ _ ht). Qcrush.
  - specialize (has_type_filter _ _ _ _ _ _ ht2). clear - H1 H3 has_type_filter. rename H1 into Hcld2.
    rewrite <- qor_assoc_23 in has_type_filter. apply subqual_qor_drop_var in has_type_filter; auto. eapply Subq_trans; eauto.
    clear - Hcld2. Qcrush; auto. specialize (H0 (S (‖ Γ ‖)) H). lia.
  - specialize (has_type_filter _ _ _ _ _ _ ht); auto.
Qed.

Lemma bound_vars_untypable : forall {Γ φ Σ T d i}, has_type Γ φ Σ #i T d -> False.
  intros Γ φ Σ T d i HT. remember (tvar #i) as t. induction HT; try discriminate; intuition.
Qed.



Lemma not_free_splice_ty_iff : forall {v k T}, not_free v T <-> not_free v (T ↑ᵀ k).
  intros v k. unfold not_free. intros. intuition.
  - replace (∅) with (∅ ↑ᵈ k); auto. replace (TUnit) with (TUnit ↑ᵀ k); auto. rewrite <- splice_ty_open_rec_ty. rewrite H. auto.
  - replace (∅) with (∅ ↑ᵈ k) in H; auto. replace (TUnit) with (TUnit ↑ᵀ k) in H; auto. rewrite <- splice_ty_open_rec_ty in H.
    eapply splice_ty_injective; eauto.
Qed.



Lemma has_type_local_loc_sep : forall Γ φ Σ t T d,
  has_type Γ φ Σ t T d ->
  kill_sep (local_locs t) d.
Proof.
  intros. induction H; simpl; auto.
  - apply has_type_closed in H as Ht. intuition. eapply kill_sep_sub with (q := (df ⊔ d1 ⊔ d2 <~ᵈ ∅; ∅)).  inversion H9; subst. eapply openq_subqual. 2-4: clear; Qcrush. eapply closed_Qual_qor. eauto. eapply closed_Qual_qor; auto. apply closed_qual_open2; auto.
    eapply kill_sep_qor; auto. eapply kill_sep_qor; auto.
      unfold openq. eapply kill_sep_open_empty'. 2: eauto. eapply local_locs_closed; eauto.
  - apply has_type_closed in H as Ht. intuition. eapply kill_sep_sub with (q := (df ⊔ d1 ⊔ d2 <~ᵈ ∅; ∅)).  inversion H11; subst. eapply openq_subqual. 2-4: clear; Qcrush. eapply closed_Qual_qor. eauto. eapply closed_Qual_qor; auto. apply closed_qual_open2; auto.
    eapply kill_sep_qor; auto. eapply kill_sep_qor; auto.
      unfold openq. eapply kill_sep_open_empty'. 2: eauto. eapply local_locs_closed; eauto.
  - unfold kill_sep; Qcrush.
  - unfold kill_sep; Qcrush.
  - apply has_type_closed in H as Ht1. apply has_type_closed in H0 as Ht2. intuition. eapply kill_sep_sub with (q := (df ⊔ d1 ⊔ d2 <~ᵈ ∅; ∅)).  inversion H10; subst. eapply openq_subqual. 2-4: clear; Qcrush. eapply closed_Qual_qor. eauto. eapply closed_Qual_qor; auto. apply closed_qual_open2; auto.
    eapply kill_sep_qor; auto. apply kill_sep_kill_qor; auto. eapply kill_sep_qor; auto. apply kill_sep_kill_qor; auto. apply qdiff_local_loc_prop in H4. destruct H4. apply has_type_filter in H0. eapply kill_sep_sub_fresh; eauto.
      unfold openq. eapply kill_sep_open_empty'. 2: eauto. apply closed_Qual_qor. 1-2: eapply local_locs_closed; eauto.
  - apply has_type_closed in H as Ht1. apply has_type_closed in H0 as Ht2. intuition. eapply kill_sep_sub with (q := (df ⊔ d1 ⊔ d2 <~ᵈ ∅; ∅)).  inversion H12; subst. eapply openq_subqual. 2-4: clear; Qcrush. eapply closed_Qual_qor. eauto. eapply closed_Qual_qor; auto. apply closed_qual_open2; auto.
    eapply kill_sep_qor; auto. apply kill_sep_kill_qor; auto. eapply kill_sep_qor; auto. apply kill_sep_kill_qor; auto. apply qdiff_local_loc_prop in H5. destruct H5. apply has_type_filter in H0. eapply kill_sep_sub_fresh; eauto.
      unfold openq. eapply kill_sep_open_empty'. 2: eauto. apply closed_Qual_qor. 1-2: eapply local_locs_closed; eauto.
  - unfold kill_sep; Qcrush.
  - apply kill_sep_fresh.
  - apply kill_sep_kill_qor; auto.
  - apply kill_sep_empty.
  - apply has_type_closed in H as Ht1. intuition. apply kill_sep_kill_qor; auto. eapply kill_sep_sub_fresh with (φd ⊔ $! (S (‖ Γ ‖))). eapply has_type_filter; eauto. apply kill_sep_qor. auto. eapply kill_sep_var. eapply local_locs_closed; eauto.
    unfold open_tm' in IHhas_type2. rewrite local_locs_open' in IHhas_type2; auto. rewrite local_locs_open' in IHhas_type2; auto.
  - apply kill_sep_kill_qor; auto.
Qed.





Lemma weaken_gen : forall {t Γ1 Γ2 φ Σ T d},
  wf_tenv Γ2 Σ ->
  wf_senv Σ ->
  has_type (Γ1 ++ Γ2) φ Σ t T d ->
  forall X, has_type ((Γ1 ↑ᴳ ‖Γ2‖) ++ X :: Γ2) (φ ↑ᵈ ‖Γ2‖) Σ (t ↑ᵗ ‖Γ2‖) (T ↑ᵀ ‖Γ2‖) (d ↑ᵈ ‖Γ2‖).
  intros t Γ1 Γ2 φ Σ T d wft wfs HT. remember (Γ1 ++ Γ2) as Γ. generalize dependent Γ1. generalize dependent Γ2.
  induction HT; intros; subst.
  - (* t_tabs *) rewrite app_length in *. simpl.  constructor.
    apply splice_closed'.
    1-3: rewrite app_length; rewrite splice_env_length; simpl;
      replace (‖Γ1‖ + S (‖Γ2‖)) with (S (‖Γ1‖ + ‖Γ2‖)); eauto.
    inversion H0. subst. constructor. 1,2,5: apply splice_qual_closed; auto. 1,2 : apply splice_ty_closed; auto.
    erewrite <- splice_qual_fresh. rewrite <- splice_qual_qor_dist. rewrite subqual_splice_lr'. auto.
    rewrite subqual_splice_lr'. auto.
    rewrite <- not_fresh_splice_iff. auto.
    eauto.
    eapply kill_sep_local_locs_splice; eauto.
    rewrite app_comm_cons.
    replace ((bind_ty, false, T1 ↑ᵀ ‖Γ2‖, d1 ↑ᵈ ‖Γ2‖)
         :: ((bind_tm, true, TAll (d1 ↑ᵈ ‖Γ2‖) (d2 ↑ᵈ ‖Γ2‖) (T1 ↑ᵀ ‖Γ2‖) (T2 ↑ᵀ ‖Γ2‖), df ↑ᵈ ‖Γ2‖)
                      :: (Γ1 ↑ᴳ ‖Γ2‖)) ++ X :: Γ2)
       with ((((bind_ty, false,T1, d1) :: (bind_tm, true, TAll d1 d2 T1 T2, df) :: Γ1) ↑ᴳ ‖Γ2‖) ++ X :: Γ2).
    specialize (IHHT wfs Γ2 wft ((bind_ty, false, T1, d1) :: (bind_tm, true, TAll d1 d2 T1 T2, df) :: Γ1)). intuition. rename H6 into IHHT. remember (a, b1, b0, b) as X.
    specialize (IHHT X). intuition.
    replace ((df ↑ᵈ ‖Γ2‖) ⊔ $!(‖(Γ1 ↑ᴳ ‖Γ2‖) ++ X :: Γ2‖) ⊔ $!(S (‖(Γ1 ↑ᴳ ‖Γ2‖) ++ X :: Γ2‖)))
      with  ((df ⊔ $!(‖Γ1‖ + ‖Γ2‖) ⊔ $!(S (‖Γ1‖ + ‖Γ2‖))) ↑ᵈ ‖Γ2‖).
    rewrite <- splice_open'. rewrite <- splice_ty_open'. rewrite <- splice_qual_open'.
    rewrite @open_tm'_len with (Γ':=(Γ1 ++ Γ2)). rewrite @open_ty'_len with (Γ':=(Γ1 ++ Γ2)).
    rewrite @openq'_len with (Γ':=(Γ1 ++ Γ2)). auto.
    1-4 : repeat rewrite app_length; rewrite splice_env_length; auto.
    repeat rewrite splice_qual_lub_dist. simpl.
    repeat rewrite <- plus_n_Sm. repeat f_equal; unfold_q; rewrite n_splice_one_S; try lia; repeat f_equal; lia.
    simpl. auto.
  - (* t_tapp *) simpl. rewrite splice_qual_open''. rewrite splice_ty_open''. rewrite splice_qual_empty.
    apply t_tapp; eauto.
    1-2: erewrite app_length in *; erewrite splice_env_length; eauto; simpl in *;
    replace (‖ Γ1 ‖ + S (‖ Γ2 ‖)) with (S (‖ Γ1 ‖ + ‖ Γ2 ‖)); try lia.
    apply splice_ty_closed; eauto. apply splice_qual_closed; eauto.
    rewrite <- @splice_qual_empty with (k := ‖Γ2‖); rewrite <- splice_qual_open''.
    specialize (@splice_qual_lub_dist φ ({♦}) (‖ Γ2 ‖)) as Hdist. rewrite splice_qual_fresh in Hdist.
    rewrite <- Hdist. rewrite subqual_splice_lr'; auto. rewrite subqual_splice_lr'; auto.
    rewrite <- not_free_splice_ty_iff. auto.
    eapply kill_sep_local_locs_splice; eauto. apply has_type_closed in HT; intuition. eauto.
    eapply kill_sep_local_locs_splice; eauto. apply has_type_closed in HT; intuition. eauto.

  - (* t_tapp_fresh *) simpl. rewrite splice_qual_open''. rewrite splice_ty_open''. rewrite splice_qual_empty.
    apply t_tapp_fresh with (T1:=T1 ↑ᵀ ‖Γ2‖) (d1:=d1 ↑ᵈ ‖Γ2‖) (df:=df ↑ᵈ ‖Γ2‖); auto.
    replace (TAll
     (q_trans_tenv (Γ1 ↑ᴳ (‖ Γ2 ‖) ++ X :: Γ2) (df ↑ᵈ (‖ Γ2 ‖))
      ⋒ q_trans_tenv (Γ1 ↑ᴳ (‖ Γ2 ‖) ++ X :: Γ2) (d1 ↑ᵈ (‖ Γ2 ‖)))
     (d2 ↑ᵈ (‖ Γ2 ‖)) (T1 ↑ᵀ (‖ Γ2 ‖)) (T2 ↑ᵀ (‖ Γ2 ‖)))
     with ((TAll (q_trans_tenv (Γ1 ++ Γ2) df ⋒ q_trans_tenv (Γ1 ++ Γ2) d1) d2 T1 T2) ↑ᵀ (‖ Γ2 ‖)). auto.
    simpl. rewrite splice_qual_qor_dist. rewrite splice_qual_fresh. rewrite splice_qual_glb_dist. f_equal.
    erewrite <- wf_tenv_splice_lower_id' with (Γ1:=(Γ1 ↑ᴳ (‖ Γ2 ‖))) (n:=(‖ Γ2 ‖)) (d:=(df ↑ᵈ (‖ Γ2 ‖))); eauto. erewrite <- wf_tenv_splice_lower_id' with (Γ1:=(Γ1 ↑ᴳ (‖ Γ2 ‖))) (n:=(‖ Γ2 ‖)) (d:=(d1 ↑ᵈ (‖ Γ2 ‖))); eauto.
    repeat rewrite splice_q_trans_tenv_comm. auto.
    rewrite app_length. simpl. rewrite <- plus_n_Sm. apply splice_ty_closed; auto. eapply closed_ty_monotone; eauto. erewrite splice_env_length; eauto. rewrite app_length. lia.
    rewrite app_length. simpl. rewrite <- plus_n_Sm. apply splice_Qual_closed; auto. eapply closed_Qual_monotone; eauto. erewrite splice_env_length; eauto. rewrite app_length. lia.
    erewrite <- splice_qual_fresh. rewrite <- splice_qual_qor_dist. rewrite subqual_splice_lr'; auto.
    intros Hfresh. rewrite <- fresh_splice_iff in Hfresh. rewrite <- not_free_splice_ty_iff. auto.
    rewrite <- not_free_splice_ty_iff. auto.
    rewrite <- @splice_qual_empty with (k := ‖Γ2‖); rewrite <- splice_qual_open''.
    erewrite <- splice_qual_fresh. rewrite <- splice_qual_qor_dist. rewrite subqual_splice_lr'; auto.
    erewrite <- wf_tenv_splice_lower_id' with (Γ1:=(Γ1 ↑ᴳ (‖ Γ2 ‖))) (n:=(‖ Γ2 ‖)) (d:=(df ↑ᵈ (‖ Γ2 ‖))); eauto. erewrite <- wf_tenv_splice_lower_id' with (Γ1:=(Γ1 ↑ᴳ (‖ Γ2 ‖))) (n:=(‖ Γ2 ‖)) (d:=(d1 ↑ᵈ (‖ Γ2 ‖))); eauto. repeat rewrite splice_q_trans_tenv_comm. rewrite <- splice_qual_qand_dist. erewrite <- splice_qual_fresh. rewrite <- splice_qual_qor_dist. rewrite <- splice_qual_qor_dist. rewrite subqual_splice_lr'; auto.
    eapply kill_sep_local_locs_splice; eauto. apply has_type_closed in HT; intuition. eauto.
    eapply kill_sep_local_locs_splice; eauto. apply has_type_closed in HT; intuition. eauto.
    replace ( (q_trans_tenv (Γ1 ↑ᴳ (‖ Γ2 ‖) ++ X :: Γ2) (d1 ↑ᵈ (‖ Γ2 ‖))
    ⋒ q_trans_tenv (Γ1 ↑ᴳ (‖ Γ2 ‖) ++ X :: Γ2) (df ↑ᵈ (‖ Γ2 ‖)))) with ((q_trans_tenv (Γ1 ++ Γ2) d1 ⋒ q_trans_tenv (Γ1 ++ Γ2) df) ↑ᵈ (‖ Γ2 ‖)). eapply kill_sep_local_locs_splice; eauto. apply has_type_closed in HT; intuition. eauto.
      simpl. rewrite splice_qual_qor_dist. rewrite splice_qual_fresh. rewrite splice_qual_glb_dist. f_equal.
      erewrite <- wf_tenv_splice_lower_id' with (Γ1:=(Γ1 ↑ᴳ (‖ Γ2 ‖))) (n:=(‖ Γ2 ‖)) (d:=(df ↑ᵈ (‖ Γ2 ‖))); eauto. erewrite <- wf_tenv_splice_lower_id' with (Γ1:=(Γ1 ↑ᴳ (‖ Γ2 ‖))) (n:=(‖ Γ2 ‖)) (d:=(d1 ↑ᵈ (‖ Γ2 ‖))); eauto.
      repeat rewrite splice_q_trans_tenv_comm. auto.

  - (* tunit *) simpl. rewrite splice_qual_empty.
    constructor. eapply splice_qual_closed'.
    rewrite app_length in *. unfold splice_tenv. erewrite splice_env_length; eauto.
  - (* t_var *) simpl.
    destruct (le_lt_dec (‖Γ2‖) x) eqn:Heq.
    * (* |Γ2| <= x < |Γ1|+|Γ2|*)
      rewrite splice_qual_one_S; auto.
      apply t_var with (b:=b) (d:=d ↑ᵈ ‖Γ2‖).
      rewrite <- indexr_insert_ge. apply indexr_splice_tenv; eauto. lia.
      erewrite <- splice_qual_just_fv_ge; eauto.
      rewrite subqual_splice_lr'. auto.
      eapply splice_qual_closed'.
      rewrite app_length in *. unfold splice_tenv. erewrite splice_env_length; eauto. auto.
      eapply splice_ty_closed''; eauto. eapply splice_qual_closed''; eauto.
    * (* |Γ2| > x *)
      rewrite indexr_skips in H; auto. rewrite splice_qual_one_inv; auto.
      apply t_var with (b:=b) (d:=d).
      rewrite <- indexr_insert_lt; auto. rewrite indexr_skips; auto.
      erewrite splice_ty_id. auto.
      eapply closed_ty_monotone; eauto. lia.
      erewrite <- splice_qual_just_fv_lt; eauto.
      rewrite subqual_splice_lr'. auto.
      eapply splice_qual_closed'.
      rewrite app_length in *. unfold splice_tenv. erewrite splice_env_length; eauto. auto.
      erewrite splice_ty_id; eauto. eapply closed_ty_monotone; eauto. lia. auto.
  - (* t_abs *) rewrite app_length in *. simpl. constructor; auto.
    apply splice_closed'.
    1-3: rewrite app_length; rewrite splice_env_length; simpl;
      replace (‖Γ1‖ + S (‖Γ2‖)) with (S (‖Γ1‖ + ‖Γ2‖)); eauto.
    inversion H0. subst. constructor. 1,2,5: apply splice_qual_closed; auto. 1,2 : apply splice_ty_closed; auto.
    erewrite <- splice_qual_fresh. rewrite <- splice_qual_qor_dist. rewrite subqual_splice_lr'. auto.
    rewrite subqual_splice_lr'; auto.
    eapply kill_sep_local_locs_splice; eauto.
    rewrite app_comm_cons.
    replace ((bind_tm, false, T1 ↑ᵀ ‖Γ2‖, d1 ↑ᵈ ‖Γ2‖)
                :: ((bind_tm, true, TFun (d1 ↑ᵈ ‖Γ2‖) (d2 ↑ᵈ ‖Γ2‖) (T1 ↑ᵀ ‖Γ2‖) (T2 ↑ᵀ ‖Γ2‖), df ↑ᵈ ‖Γ2‖)
                      :: (Γ1 ↑ᴳ ‖Γ2‖)) ++ X :: Γ2)
            with ((((bind_tm, false,T1, d1) :: (bind_tm, true, TFun d1 d2 T1 T2, df) :: Γ1) ↑ᴳ ‖Γ2‖) ++ X :: Γ2).
    replace ((df ↑ᵈ ‖Γ2‖) ⊔ $!(‖(Γ1 ↑ᴳ ‖Γ2‖) ++ X :: Γ2‖) ⊔ $!(S (‖(Γ1 ↑ᴳ ‖Γ2‖) ++ X :: Γ2‖)))
      with  ((df ⊔ $!(‖Γ1‖ + ‖Γ2‖) ⊔ $!(S (‖Γ1‖ + ‖Γ2‖))) ↑ᵈ ‖Γ2‖).
    rewrite <- splice_open'. rewrite <- splice_ty_open'. rewrite <- splice_qual_open'.
    rewrite @open_tm'_len with (Γ':=(Γ1 ++ Γ2)). rewrite @open_ty'_len with (Γ':=(Γ1 ++ Γ2)).
    rewrite @openq'_len with (Γ':=(Γ1 ++ Γ2)).
    apply IHHT; intuition. 1-4 : repeat rewrite app_length; rewrite splice_env_length; auto.
    repeat rewrite splice_qual_lub_dist. simpl.
    repeat rewrite <- plus_n_Sm. repeat f_equal; unfold_q; rewrite n_splice_one_S; try lia; repeat f_equal; lia.
    simpl. auto.
  - (* t_app *) simpl. rewrite splice_qual_open''. rewrite splice_ty_open''. rewrite splice_qual_empty. remember ((qdiff φ (local_locs t1))) as φd. symmetry in Heqφd. apply (qdiff_local_loc_prop) in Heqφd as Heqφd'. destruct Heqφd'. apply t_app with (T1:=T1 ↑ᵀ ‖Γ2‖) (df:=df ↑ᵈ ‖Γ2‖) (φd:=φd ↑ᵈ ‖Γ2‖).
    apply IHHT1; auto. apply IHHT2; auto.
    specialize (@splice_qual_lub_dist φ ({♦}) (‖ Γ2 ‖)) as Hdist. rewrite splice_qual_fresh in Hdist.
    rewrite <- Hdist. rewrite <- @splice_qual_empty with (k := ‖Γ2‖); rewrite <- splice_qual_open''.
    rewrite subqual_splice_lr'; auto. rewrite <- not_fresh_splice_iff. auto.
    rewrite <- not_free_splice_ty_iff. auto.
    (* rewrite subqual_splice_lr'; auto. *) subst. rewrite qdiff_splice_dist; auto. rewrite <- local_locs_splice; auto. f_equal. erewrite splice_qual_id; auto. apply has_type_closed in HT1; intuition. apply local_locs_closed in H8. eapply closed_Qual_monotone; eauto. lia.
    eapply kill_sep_local_locs_splice; eauto. apply has_type_closed in HT2; intuition. eauto.
    apply kill_sep_kill_qor_rev in H4; destruct H4. eapply kill_sep_kill_qor. 1-2: eapply kill_sep_local_locs_splice; eauto. apply has_type_closed in HT1; intuition. eauto. apply has_type_closed in HT2; intuition. eauto.
  - (* t_app_fresh *) simpl. rewrite splice_qual_open''. rewrite splice_ty_open''. rewrite splice_qual_empty.  remember ((qdiff φ (local_locs t1))) as φd. symmetry in Heqφd. apply (qdiff_local_loc_prop) in Heqφd as Heqφd'. destruct Heqφd'.
    apply t_app_fresh with (T1:=T1 ↑ᵀ ‖Γ2‖) (d1:=d1 ↑ᵈ ‖Γ2‖) (df:=df ↑ᵈ ‖Γ2‖) (φd:=φd ↑ᵈ ‖Γ2‖); auto.
    replace (TFun
     (q_trans_tenv (Γ1 ↑ᴳ (‖ Γ2 ‖) ++ X :: Γ2) (df ↑ᵈ (‖ Γ2 ‖))
      ⋒ q_trans_tenv (Γ1 ↑ᴳ (‖ Γ2 ‖) ++ X :: Γ2) (d1 ↑ᵈ (‖ Γ2 ‖)))
     (d2 ↑ᵈ (‖ Γ2 ‖)) (T1 ↑ᵀ (‖ Γ2 ‖)) (T2 ↑ᵀ (‖ Γ2 ‖)))
     with ((TFun (q_trans_tenv (Γ1 ++ Γ2) df ⋒ q_trans_tenv (Γ1 ++ Γ2) d1) d2 T1 T2) ↑ᵀ (‖ Γ2 ‖)). auto.
    simpl. rewrite splice_qual_qor_dist. rewrite splice_qual_fresh. rewrite splice_qual_glb_dist. f_equal.
    erewrite <- wf_tenv_splice_lower_id' with (Γ1:=(Γ1 ↑ᴳ (‖ Γ2 ‖))) (n:=(‖ Γ2 ‖)) (d:=(df ↑ᵈ (‖ Γ2 ‖))); eauto. erewrite <- wf_tenv_splice_lower_id' with (Γ1:=(Γ1 ↑ᴳ (‖ Γ2 ‖))) (n:=(‖ Γ2 ‖)) (d:=(d1 ↑ᵈ (‖ Γ2 ‖))); eauto.
    repeat rewrite splice_q_trans_tenv_comm. auto.
    intros Hfresh. rewrite <- fresh_splice_iff in Hfresh. rewrite <- not_free_splice_ty_iff. auto.
    rewrite <- not_free_splice_ty_iff. auto.
    rewrite <- @splice_qual_empty with (k := ‖Γ2‖); rewrite <- splice_qual_open''.
    erewrite <- splice_qual_fresh. rewrite <- splice_qual_qor_dist. rewrite subqual_splice_lr'; auto.
    erewrite <- wf_tenv_splice_lower_id' with (Γ1:=(Γ1 ↑ᴳ (‖ Γ2 ‖))) (n:=(‖ Γ2 ‖)) (d:=(df ↑ᵈ (‖ Γ2 ‖))); eauto. erewrite <- wf_tenv_splice_lower_id' with (Γ1:=(Γ1 ↑ᴳ (‖ Γ2 ‖))) (n:=(‖ Γ2 ‖)) (d:=(d1 ↑ᵈ (‖ Γ2 ‖))); eauto. repeat rewrite splice_q_trans_tenv_comm. rewrite <- splice_qual_qand_dist. erewrite <- splice_qual_fresh. rewrite <- splice_qual_qor_dist. rewrite <- splice_qual_qor_dist. apply subqual_splice_lr'. auto.
    subst. rewrite qdiff_splice_dist; auto. rewrite <- local_locs_splice; auto. f_equal. erewrite splice_qual_id; auto. apply has_type_closed in HT1; intuition. apply local_locs_closed in H10. eapply closed_Qual_monotone; eauto. lia.
    eapply kill_sep_local_locs_splice; eauto. apply has_type_closed in HT2; intuition. eauto.
    apply kill_sep_kill_qor_rev in H5; destruct H5. eapply kill_sep_kill_qor. 1-2: eapply kill_sep_local_locs_splice; eauto. apply has_type_closed in HT1; intuition. eauto. apply has_type_closed in HT2; intuition. eauto.
    replace ( (q_trans_tenv (Γ1 ↑ᴳ (‖ Γ2 ‖) ++ X :: Γ2) (d1 ↑ᵈ (‖ Γ2 ‖))
      ⋒ q_trans_tenv (Γ1 ↑ᴳ (‖ Γ2 ‖) ++ X :: Γ2) (df ↑ᵈ (‖ Γ2 ‖)))) with ((q_trans_tenv (Γ1 ++ Γ2) d1 ⋒ q_trans_tenv (Γ1 ++ Γ2) df) ↑ᵈ (‖ Γ2 ‖)). eapply kill_sep_local_locs_splice; eauto. apply has_type_closed in HT1; intuition. eauto.
      simpl. rewrite splice_qual_qor_dist. rewrite splice_qual_fresh. rewrite splice_qual_glb_dist. f_equal.
      erewrite <- wf_tenv_splice_lower_id' with (Γ1:=(Γ1 ↑ᴳ (‖ Γ2 ‖))) (n:=(‖ Γ2 ‖)) (d:=(df ↑ᵈ (‖ Γ2 ‖))); eauto. erewrite <- wf_tenv_splice_lower_id' with (Γ1:=(Γ1 ↑ᴳ (‖ Γ2 ‖))) (n:=(‖ Γ2 ‖)) (d:=(d1 ↑ᵈ (‖ Γ2 ‖))); eauto.
      repeat rewrite splice_q_trans_tenv_comm. auto.

  - (* t_loc *) simpl. replace (&! l ↑ᵈ (‖ Γ2 ‖)) with (&! l). apply t_loc. eapply splice_qual_closed'.
    rewrite app_length in *. unfold splice_tenv. erewrite splice_env_length; eauto. auto.
    erewrite splice_ty_id; eauto. erewrite splice_qual_id; eauto. eapply closed_qual_monotone; eauto. lia. eapply closed_ty_monotone; eauto. lia.
    erewrite splice_ty_id; eauto. eapply closed_ty_monotone; eauto. lia.
    erewrite splice_qual_id; eauto. eapply closed_qual_monotone; eauto. lia.
    Qcrush.
    1-2: Qcrush.
    replace (&! l) with (&! l ↑ᵈ (‖ Γ2 ‖)).
    1-2: apply Q_lift_eq; Qcrush.
  - (* t_ref *) simpl in *. specialize (IHHT wfs Γ2 wft Γ1). intuition. remember (a, b1, b0, b) as X.
    specialize (H1 X).
    rewrite splice_qual_fresh. apply t_ref; auto.
    apply has_type_closed in H1. intuition.
  - (* t_refat *) simpl in *. specialize (IHHT1 wfs Γ2 wft Γ1 eq_refl X). specialize (IHHT2 wfs Γ2 wft Γ1 eq_refl X).
    eapply t_refat; eauto.
    subst. rewrite qdiff_splice_dist; auto. rewrite <- local_locs_splice; auto. f_equal. erewrite splice_qual_id; auto. apply has_type_closed in HT2; intuition. apply local_locs_closed in H3. eapply closed_Qual_monotone; eauto. lia.
    eapply kill_sep_local_locs_splice; eauto. apply has_type_closed in HT1; intuition. eauto.
  - (* t_deref *) simpl. econstructor; eauto. apply subqual_splice_lr'. auto.
    eapply kill_sep_local_locs_splice; eauto. apply has_type_closed in HT; intuition. eauto.
  - (* t_assign *) simpl. specialize (IHHT1 wfs Γ2 wft Γ1). specialize (IHHT2 wfs Γ2 wft Γ1). intuition.
    remember (a, b1, b0, b) as X.
    specialize (H2 X). specialize (H0 X). simpl in *. rewrite splice_qual_empty. eapply t_assign; eauto.
    subst. rewrite qdiff_splice_dist; auto. rewrite <- local_locs_splice; auto. f_equal. erewrite splice_qual_id; auto. apply has_type_closed in HT1; intuition. apply local_locs_closed in H5. eapply closed_Qual_monotone; eauto. lia.
    eapply kill_sep_local_locs_splice; eauto. apply has_type_closed in HT2; intuition. eauto.
  - (* t_sub *) eapply t_sub. eapply IHHT; auto.
    apply @weaken_stp_gen; eauto; lia.
    specialize (@splice_qual_lub_dist φ ({♦}) (‖ Γ2 ‖)) as Hdist. rewrite splice_qual_fresh in Hdist.
    rewrite <- Hdist. apply subqual_splice_lr'. auto.
    eapply kill_sep_local_locs_splice; eauto. apply has_type_closed in HT; intuition. eauto.
  - (* t_withr *) simpl. eapply t_withr with (φd := φd ↑ᵈ (‖ Γ2 ‖)); eauto. 1-3: rewrite app_length in *; unfold splice_tenv; erewrite splice_env_length; eauto; simpl; replace (‖ Γ1 ‖ + S (‖ Γ2 ‖)) with (S ((‖ Γ1 ‖ + ‖ Γ2 ‖))) by lia.
    eapply splice_ty_closed; auto. eapply splice_qual_closed; auto. eapply splice_closed; auto.
    specialize (IHHT2 wfs Γ2 wft ((bind_tm, false, TRef d1 T1, {♦}) :: (bind_tm, true, TUnit, {♦}) :: Γ1) eq_refl X). rewrite <- splice_open'. simpl in IHHT2.
    erewrite splice_qual_fresh in IHHT2.
    rewrite @open_tm'_len with (Γ':=(Γ1 ++ Γ2)).
    rewrite splice_qual_lub_dist in IHHT2. rewrite app_length in *; simpl in *. rewrite splice_qual_just_fv_ge in IHHT2. rewrite splice_env_length.
    repeat rewrite <- plus_n_Sm. apply IHHT2. eauto. lia.
    repeat rewrite app_length. rewrite splice_env_length; auto.
    rewrite subqual_splice_lr'; auto.
    eapply kill_sep_local_locs_splice; eauto. apply has_type_closed in HT1; intuition. eauto.
  - (* t_withc *)
    specialize (IHHT wfs Γ2 wft Γ1 eq_refl X). simpl. eapply t_withc; eauto.
    erewrite splice_ty_id; eauto. eapply closed_ty_monotone; eauto; lia.
    erewrite splice_qual_id; eauto. eapply closed_Qual_monotone; eauto; lia.
    erewrite splice_qual_id; eauto. eapply closed_Qual_monotone; eauto; lia.
    Unshelve.
Qed.


(*
  it's not sensical that filter can be arbitrarily grow, because we have the invariance: whatever inside the filter, it's separate from the already killed things
  Therefore, by exiting the scope (twithc l t), the filter should never contain l, so adding it by weaken_flt should be forbidden.
  We know how the environment changes: normally never change, adding one location when step from ref to loc, which we have the value witness.
  Therefore, we can make the filter monotonically grow, and only vtp_weaken_flt is necessary in this case
*)
Lemma weaken_flt : forall {Γ φ Σ t T d},
    has_type Γ φ Σ t T d ->
    forall {φ'}, φ ⊑↑ φ' -> closed_Qual 0 (‖Γ‖) (‖Σ‖) φ'↑ ->
    has_type Γ φ' Σ t T d.
  intros Γ φ Σ t T d HT.
  induction HT; intros.
  1,4-6,9-10,12-13: try solve [econstructor; eauto using Subq_trans].
  - assert (φ ⊔ {♦} ⊑↑ φ' ⊔ {♦}). eapply Subq_qor; eauto. specialize (qdiff_subqual_monotone φ φ' (local_locs t1) H2); intros.
    econstructor; auto. subst. eapply IHHT2; auto. eapply closed_Qual_sub; eauto. Qcrush.
  - assert (φ ⊔ {♦} ⊑↑ φ' ⊔ {♦}). eapply Subq_qor; eauto.
    econstructor; eauto. eapply Subq_trans; eauto. eauto using Subq_trans.
  - assert (φ ⊔ {♦} ⊑↑ φ' ⊔ {♦}). eapply Subq_qor; eauto.
    eapply t_tapp_fresh; eauto. eapply Subq_trans; eauto.
    Qcrush. Qcrush.
  - assert (φ ⊔ {♦} ⊑↑ φ' ⊔ {♦}). eapply Subq_qor; eauto. specialize (qdiff_subqual_monotone φ φ' (local_locs t1) H5); intros.
    econstructor; auto. subst. eapply IHHT2; auto. eapply closed_Qual_sub; eauto. Qcrush.
    eapply Subq_trans; eauto.
  - assert (φ ⊔ {♦} ⊑↑ φ' ⊔ {♦}). eapply Subq_qor; eauto. specialize (qdiff_subqual_monotone φ φ' (local_locs t1) H7); intros.
    eapply t_app_fresh; auto. subst. eapply IHHT2; auto. eapply closed_Qual_sub; eauto. Qcrush.
    eapply Subq_trans; eauto.
    eapply Subq_trans; eauto.
  - assert (φ ⊔ {♦} ⊑↑ φ' ⊔ {♦}). eapply Subq_qor; eauto. specialize (qdiff_subqual_monotone φ φ' (local_locs t2) H2); intros.
    eapply t_refat; auto. subst. eapply IHHT1; eauto. eapply closed_Qual_sub; eauto. Qcrush.
  - econstructor; eauto. assert (φ ⊔ {♦} ⊑↑ φ' ⊔ {♦}). eapply Subq_qor; eauto.
    eapply Subq_trans; eauto.
  - eapply t_withr; eauto. eapply Subq_trans; eauto.
  - subst. eapply t_withc; eauto.
Qed.


Lemma weaken : forall {φ Σ t T d},
    wf_senv Σ ->
    has_type [] φ Σ t T d -> forall {Γ},
    wf_tenv Γ Σ ->
    has_type Γ φ Σ t T d.
  intros φ Σ t T d wfs HT Γ wft. induction Γ; auto.
  specialize (@weaken_gen t [] Γ φ Σ T d) as Hsp. simpl in *.
  apply wf_tenv_shrink in wft as wft'. intuition. rename H0 into Hsp.
  apply has_type_closed in HT. intuition. simpl in *.
  replace (splice (‖Γ‖) t) with t in Hsp.
  replace (splice_ty (‖Γ‖) T) with T in Hsp.
  replace (splice_qual (‖Γ‖) d) with d in Hsp.
  replace (splice_qual (‖Γ‖) φ) with φ in Hsp. auto.
  all : symmetry.
  eapply splice_qual_id; eauto. eapply closed_qual_monotone; eauto; lia.
  eapply splice_qual_id; eauto. eapply closed_qual_monotone; eauto; lia.
  eapply splice_ty_id; eauto.   eapply closed_ty_monotone; eauto; lia.
  eapply splice_id; eauto.      eapply closed_tm_monotone; eauto; lia.
Qed.

Lemma weaken' : forall {φ Σ t T d},
  wf_senv Σ -> has_type [] φ Σ t T d -> forall {φ'}, φ ⊑↑ φ' -> forall {Γ}, wf_tenv Γ Σ ->
  closed_Qual 0 (‖Γ‖) (‖Σ‖) φ'↑ -> has_type Γ φ' Σ t T d.
  intros. eapply weaken_flt; eauto. apply weaken; auto.
Qed.

Lemma closed_Qual_qor_fresh_inv : forall {f l q}, closed_Qual 0 f l (q ⊔ {♦})↑ -> closed_Qual 0 f l q↑.
Proof. intros. Qcrush. Qed.


Lemma weaken_2D_store : forall {Γ φ Σ t T d}, has_type Γ φ Σ t T d -> forall {Σ'}, Σ' ⊇₂ Σ -> closed_qenv 0 (‖ Γ ‖) (‖ Σ ‖) Γ -> closed_qenv_qn (‖ Σ ‖) (squish Σ) -> has_type Γ φ Σ' t T d.
Proof.  intros Γ φ Σ t T d HT. induction HT; intros; intuition.
  - econstructor; eauto using closed_tm_monotone, closed_ty_monotone, closed_Qual_monotone, extends_length. apply IHHT; auto. simpl. apply closed_qenv_extend; auto. apply closed_qenv_extend; auto. eapply closed_qenv_monotone; eauto. Qcrush. inversion H0. Qcrush.
  - apply has_type_closed in HT as Hcl. eapply t_tapp; eauto using closed_tm_monotone, closed_ty_monotone, closed_Qual_monotone, extends_length; eapply weaken_store_senv_saturated; eauto; intuition; eapply closed_Qual_monotone; eauto.
  - eapply t_tapp_fresh; eauto using closed_tm_monotone, closed_ty_monotone, closed_Qual_monotone, extends_length.
  - econstructor; eauto using closed_Qual_monotone.
  - econstructor; eauto using closed_ty_monotone, closed_Qual_monotone.
  - econstructor; eauto using closed_tm_monotone, closed_ty_monotone, closed_Qual_monotone, extends_length. apply IHHT; auto. simpl. apply closed_qenv_extend; auto. apply closed_qenv_extend; auto. eapply closed_qenv_monotone; eauto. Qcrush. inversion H0. Qcrush.
  - econstructor; eauto.
  - eapply t_app_fresh; eauto.
  - econstructor; eauto using closed_Qual_monotone.
    eapply extends_2D_sindexr; eauto.
    apply extends_2D_length in H5. eapply closed_ty_monotone; eauto.
  - econstructor; eauto. eapply closed_ty_monotone; eauto.
  - econstructor; eauto.
  - apply has_type_closed in HT as Hcl. econstructor; eauto.
  - econstructor; eauto.
  - econstructor; eauto. eapply weaken_2D_stp_store_ext; eauto.
  - eapply t_withr; eauto using closed_tm_monotone, closed_ty_monotone, closed_Qual_monotone, extends_length. eapply IHHT2; eauto.
    apply closed_qenv_extend; auto. apply closed_qenv_extend; auto. eapply closed_qenv_monotone; eauto.
  - apply extends_2D_length in H3 as Hlen. eapply t_withc; eauto. lia.
    eapply closed_ty_monotone; eauto. eapply closed_Qual_monotone; eauto.
Qed.


Lemma narrowing_gen : forall {t Γ1 bd b U du Γ2 φ Σ T d},
    has_type (Γ1 ++ (bd, b,U,du) :: Γ2) φ Σ t T d -> (b = true -> (♦∈ du)) ->
    forall {V dv}, stp [] Σ V dv U du -> dv ⊑↑ du -> wf_senv Σ -> has_type (Γ1 ++ (bd, b,V,dv) :: Γ2) φ Σ t T d.
Proof. intros t Γ1 bd b U du Γ2 φ Σ T d HT Hb. remember (Γ1 ++ (bd, b, U, du) :: Γ2) as Γ.
  generalize dependent Γ1. generalize dependent U. generalize dependent du. generalize dependent Γ2.
  induction HT; intros; subst.
  - repeat rewrite app_length in *; simpl in *; auto.
    constructor; auto. 1-3 : rewrite app_length in *; simpl in *; auto.
    rewrite @open_tm'_len with (Γ' := (Γ1 ++ (bd, b,U, du) :: Γ2)).
    rewrite @open_ty'_len with (Γ' := (Γ1 ++ (bd, b,U, du) :: Γ2)).
    rewrite @openq'_len with (Γ' := (Γ1 ++ (bd, b,U, du) :: Γ2)).
    2-4 : repeat rewrite app_length; simpl; auto.
    rewrite app_length. simpl.
    rewrite app_comm_cons. rewrite app_comm_cons.
    eapply IHHT; eauto. simpl. auto.
  - econstructor; eauto. all : rewrite app_length in *; simpl in *; auto.
  - eapply t_tapp_fresh; eauto.
    apply has_type_filter in HT as Hft.
    apply t_sub with (T1:=(TAll
     (q_trans_tenv (Γ1 ++ (bd, b, U, du) :: Γ2) df
      ⋒ q_trans_tenv (Γ1 ++ (bd, b, U, du) :: Γ2) d1) d2 T1 T2)) (d1:=df); auto.
    eapply IHHT; eauto.
    apply has_type_closed in HT as HT'. intuition. inversion H13. subst. constructor. 1,2,3: constructor; auto. 1-9: repeat rewrite app_length in *; simpl in *; auto; intuition. apply closed_Qual_qor; auto. assert (closed_Qual 0 (‖ Γ1 ‖ + S (‖ Γ2 ‖)) (‖ Σ ‖) (q_trans_tenv (Γ1 ++ (bd, b, U, du) :: Γ2) df ⊓ q_trans_tenv (Γ1 ++ (bd, b, U, du) :: Γ2) d1) ↑). Qcrush. eapply @closed_Qual_subq_and with (d1':=q_trans_tenv (Γ1 ++ (bd, b, U, du) :: Γ2) df) (d2':=q_trans_tenv (Γ1 ++ (bd, b, U, du) :: Γ2) d1); eauto using q_trans_tenv_narrowing_subq'.
    1-2: eauto.
    {
      destruct bd.
      + apply @narrowing_stp_gen with (U:=U) (du:=du); eauto 2.
        apply stp_refl; auto. constructor; auto. apply Subq_qor. apply Subq_qand_split. 1,2: apply q_trans_tenv_narrowing_subq'; auto.
        replace (Γ2) with (Γ2 ++ []) by intuition. apply weaken_stp'; eauto.
      + apply @narrowing_stp_ty_gen with (U:=U) (du:=du); eauto 2.
        apply stp_refl; auto. auto.
        constructor; auto. apply Subq_qor. apply Subq_qand_split. 1,2: apply q_trans_tenv_narrowing_subq'; auto.
        1-2: apply stp_closed in H9; intuition.
        replace (Γ2) with (Γ2 ++ []) by intuition. apply weaken_stp'; eauto.
    }
    eapply stp_refl. auto. simpl.
    apply closed_ty_open2; simpl; repeat rewrite app_length; simpl; auto.
    eapply closed_ty_monotone; eauto. repeat rewrite app_length. simpl. lia.
    1,2: apply Q_lift_closed; Qcrush.
    apply qstp_refl. simpl.
    apply closed_Qual_open2; simpl; repeat rewrite app_length; simpl; auto.
    eapply closed_Qual_monotone; eauto. repeat rewrite app_length. simpl. lia.
    1-2: Qcrush.
    apply has_type_local_loc_sep in HT; auto.
    eapply closed_ty_monotone; eauto. repeat rewrite app_length. simpl. lia.
    eapply closed_Qual_monotone; eauto. repeat rewrite app_length. simpl. lia.
    eapply @Subq_trans with (d2:=(q_trans_tenv (Γ1 ++ (bd, b, U, du) :: Γ2) d1 ⋒ q_trans_tenv (Γ1 ++ (bd, b, U, du) :: Γ2) df)); auto. apply Subq_qor. apply Subq_qand_split.
    1,2: apply q_trans_tenv_narrowing_subq'; eauto using has_type_filter.
    eapply kill_sep_sub. 2: eauto. apply Subq_qor. apply Subq_qand_split. 1,2: apply q_trans_tenv_narrowing_subq'; auto.

  - econstructor; eauto.
    repeat rewrite app_length in *; simpl in *; auto.
  - repeat rewrite app_length in *; simpl in *; auto.
    destruct (PeanoNat.Nat.lt_trichotomy x (‖Γ2‖)) as [Hlen | [Hlen | Hlen] ].
    * apply t_var with (b:=b0) (d:=d); auto. rewrite <- indexr_insert_lt; auto. rewrite <- indexr_insert_lt in H; auto.
      repeat rewrite app_length in *; simpl in *; auto.
    * subst. rewrite indexr_insert in H. inversion H. subst.
      apply t_sub with (T1:=V) (d1:=$!‖Γ2‖); auto. apply t_var with (b:=b0) (d:=dv).
      rewrite indexr_insert. auto. destruct φ. simpl. auto.
      repeat rewrite app_length in *; simpl in *; auto.
      1,2 : apply stp_closed in H4; intuition. eapply closed_ty_monotone; eauto. eapply closed_qual_monotone; eauto.
      eapply stp_shrink_var; eauto. eapply weaken_stp'; eauto. eapply weaken_stp; eauto.
      replace Γ2 with (Γ2 ++ []). eapply weaken_stp'; eauto. rewrite app_nil_r. auto. rewrite app_length. simpl. lia.
      Qcrush.
      simpl. unfold kill_sep; Qcrush.
    * apply t_var with (b:=b0) (d:=d); auto. destruct x. lia. rewrite <- indexr_insert_ge; try lia.
      rewrite <- indexr_insert_ge in H; try lia. auto.
      repeat rewrite app_length in *; simpl in *; auto.
  - repeat rewrite app_length in *; simpl in *; auto.
    constructor; auto. 1-3 : rewrite app_length in *; simpl in *; auto.
    rewrite @open_tm'_len with (Γ' := (Γ1 ++ (bd, b,U, du) :: Γ2)).
    rewrite @open_ty'_len with (Γ' := (Γ1 ++ (bd, b,U, du) :: Γ2)).
    rewrite @openq'_len with (Γ' := (Γ1 ++ (bd, b,U, du) :: Γ2)).
    2-4 : repeat rewrite app_length; simpl; auto.
    rewrite app_length. simpl.
    rewrite app_comm_cons. rewrite app_comm_cons.
    eapply IHHT; eauto. simpl. auto.
  - econstructor; eauto.
  - eapply t_app_fresh; eauto.
    apply has_type_filter in HT1 as Hft.
    apply t_sub with (T1:=(TFun
     (q_trans_tenv (Γ1 ++ (bd, b, U, du) :: Γ2) df
      ⋒ q_trans_tenv (Γ1 ++ (bd, b, U, du) :: Γ2) d1) d2 T1 T2)) (d1:=df); auto.
    eapply IHHT1; eauto.
    apply has_type_closed in HT1, HT2. intuition. inversion H14. subst. constructor. 1,2,3: constructor; auto. 1-9: repeat rewrite app_length in *; simpl in *; auto; intuition. apply closed_Qual_qor; auto. assert (closed_Qual 0 (‖ Γ1 ‖ + S (‖ Γ2 ‖)) (‖ Σ ‖) (q_trans_tenv (Γ1 ++ (bd, b, U, du) :: Γ2) df ⊓ q_trans_tenv (Γ1 ++ (bd, b, U, du) :: Γ2) d1) ↑). Qcrush. eapply @closed_Qual_subq_and with (d1':=q_trans_tenv (Γ1 ++ (bd, b, U, du) :: Γ2) df) (d2':=q_trans_tenv (Γ1 ++ (bd, b, U, du) :: Γ2) d1); eauto using q_trans_tenv_narrowing_subq'.
    {
      destruct bd.
      + apply @narrowing_stp_gen with (U:=U) (du:=du). auto. 2: auto.
        apply stp_refl; auto. constructor; auto. apply Subq_qor. apply Subq_qand_split. 1,2: apply q_trans_tenv_narrowing_subq'; auto.
        replace (Γ2) with (Γ2 ++ []) by intuition. apply weaken_stp'; eauto.
      + apply @narrowing_stp_ty_gen with (U:=U) (du:=du); auto.
        apply stp_refl; auto. constructor; auto. apply Subq_qor. apply Subq_qand_split. 1,2: apply q_trans_tenv_narrowing_subq'; auto.
        1,2: eapply stp_closed in H7; intuition.
        replace (Γ2) with (Γ2 ++ []) by intuition. apply weaken_stp'; eauto.
    }
    eapply stp_refl; auto. simpl.
    apply closed_ty_open2; simpl; repeat rewrite app_length; simpl; auto.
    eapply closed_ty_monotone; eauto. repeat rewrite app_length. simpl. lia.
    1,2: apply Q_lift_closed; Qcrush.
    apply qstp_refl. simpl.
    apply closed_Qual_open2; simpl; repeat rewrite app_length; simpl; auto.
    eapply closed_Qual_monotone; eauto. repeat rewrite app_length. simpl. lia.
    1,2: Qcrush.
    apply has_type_local_loc_sep in HT1; auto.
    eapply @Subq_trans with (d2:=(q_trans_tenv (Γ1 ++ (bd, b, U, du) :: Γ2) d1 ⋒ q_trans_tenv (Γ1 ++ (bd, b, U, du) :: Γ2) df)); auto. apply Subq_qor. apply Subq_qand_split.
    1,2: apply q_trans_tenv_narrowing_subq'; eauto using has_type_filter.
    eapply kill_sep_sub. 2: eauto. apply Subq_qor. apply Subq_qand_split. 1,2: apply q_trans_tenv_narrowing_subq'; auto.
  - econstructor; eauto. repeat rewrite app_length in *; simpl in *; auto.
  - econstructor; eauto. repeat rewrite app_length in *; simpl in *; auto.
  - econstructor; eauto.
  - econstructor; eauto.
  - econstructor; eauto.
  - eapply t_sub; eauto.
    {
      destruct bd.
      + eapply narrowing_stp_gen; eauto. replace (Γ2) with (Γ2 ++ []). eapply weaken_stp'; eauto. rewrite app_nil_r. auto.
      + eapply narrowing_stp_ty_gen; eauto. 1,2: eapply stp_closed in H2; intuition.
        replace (Γ2) with (Γ2 ++ []). eapply weaken_stp'; eauto. rewrite app_nil_r. auto.
    }
  - eapply t_withr; eauto. eapply closed_ty_monotone; eauto. 2: eapply closed_Qual_monotone; eauto. 3: eapply closed_tm_monotone; eauto. 1-3: do 2 rewrite app_length; simpl; lia.
    rewrite @open_tm'_len with (Γ' := (Γ1 ++ (bd, b,U, du) :: Γ2)). replace ($! (S (‖ Γ1 ++ (bd, b, V, dv) :: Γ2 ‖))) with ($! (S (‖ Γ1 ++ (bd, b, U, du) :: Γ2 ‖))).
    specialize (IHHT2 Γ2 du Hb U ((bind_tm, false, TRef d1 T1, {♦}) :: (bind_tm, true, TUnit, {♦}) :: Γ1) eq_refl). eapply IHHT2; eauto. 1-2: do 2 rewrite app_length; simpl; auto.
  - eapply t_withc; eauto.
Qed.

Lemma narrowing : forall {Γ bd b U du φ Σ t T d}, has_type ((bd, b,U,du) :: Γ) φ Σ t T d -> (b = true -> (♦∈ du)) -> forall {V dv}, stp [] Σ V dv U du -> dv ⊑↑ du -> wf_senv Σ -> has_type ((bd, b,V,dv) :: Γ) φ Σ t T d.
  intros. specialize (@narrowing_gen t [] bd b U du Γ φ Σ T d) as narrow. simpl in *. eapply narrow; eauto.
Qed.

Lemma values_stuck : forall {v}, value v -> forall {t σ σ'}, step v σ t σ' -> False.
  intros. inversion H0; subst; inversion H.
Qed.