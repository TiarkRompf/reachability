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
Require Import weaken_narrow.

Import QualNotations.
Local Open Scope qualifiers.
Import OpeningNotations.
Local Open Scope opening.

Import SplicingNotations.
Local Open Scope splicing.
Import SubstitutionNotations.
Local Open Scope substitutions.



Lemma loc_in_qor : forall l q1 q2,
  l ∈ₗ (q1 ⊔ q2) -> l ∈ₗ q1 \/ l ∈ₗ q2.
Proof.
  intros. Qcrush.
Qed.

Lemma qstp_loc_in : forall Σ l d1 d2,
  qstp [] Σ d1 d2 ->
  l ∈ₗ d1 -> l ∈ₗ d2.
Proof.
  intros. remember [] as Γ. induction H; subst; auto.
  Qcrush. inversion H. inversion H. inversion H. inversion H.
  apply loc_in_qor in H0. destruct H0. Qcrush. specialize (IHqstp eq_refl H0). Qcrush.
Qed.


(* Value typing, the typing for values in empty context
  Vtp has s_trans built-in, so it's invertible
*)
Inductive vtp: senv -> qual -> qual -> tm -> ty -> qual -> Prop :=
| vtp_tabs: forall Σ ϰ φ t T1 T2 T3 T4 d1 d2 d3 d4 df1 df2,
  closed_tm 2 0 (‖Σ‖) t ->
  closed_ty 0 0 (‖Σ‖) (TAll d3 d4 T3 T4) -> (* supertype *)
  closed_ty 0 0 (‖Σ‖) (TAll d1 d2 T1 T2) -> (* subtype *)
  has_type [(bind_ty, false, T1, d1); (bind_tm, true, (TAll d1 d2 T1 T2), df1)] (df1 ⊔ $!0 ⊔ $!1) Σ
           (t <~²ᵗ ([] : tenv)) (T2 <~²ᵀ ([] : tenv)) (d2 <~²ᵈ ([] : tenv)) ->
  stp [] Σ T3 d3 T1 d1 ->
  qstp [] Σ df1 df2 ->
  stp [(bind_ty, false, T3, d3); (bind_tm, true, (TAll d1 d2 T1 T2), {♦})] Σ
      (T2 <~²ᵀ ([] : tenv)) (d2 <~²ᵈ ([] : tenv))
      (T4 <~²ᵀ ([] : tenv)) (d4 <~²ᵈ ([] : tenv)) ->
  d1 ⊑↑ df1 ⊔ {♦} ->
  ♦∉ df1 ->
  kill_sep ϰ df2 ->
  kill_sep (local_locs t) df2 ->
  vtp Σ ϰ φ (ttabs t) (TAll d3 d4 T3 T4) df2

| vtp_base: forall Σ ϰ φ d,
  closed_Qual 0 0 (‖Σ‖) d↑ ->
  kill_sep ϰ d ->
  vtp Σ ϰ φ tunit TUnit d

| vtp_loc:  forall Σ ϰ φ l o T U q1 q2 d,
  closed_Qual 0 0 (‖Σ‖) d↑ ->
  closed_ty 0 0 (‖Σ‖) T ->
  closed_Qual 0 0 (‖Σ‖) q1↑ ->
  closed_Qual 0 0 (‖Σ‖) q2↑ ->
  l ∈ₗ φ ->
  sindexr l o Σ = Some (T,q1) ->
  stp [] Σ T ∅ U ∅ ->
  stp [] Σ U ∅ T ∅ ->
  qstp [] Σ (&!l) d ->
  ♦∉ q1 ->
  qstp [] Σ q1 q2 ->
  qstp [] Σ q2 q1 ->
  kill_sep ϰ d ->
  vtp Σ ϰ φ &(l, o) (TRef q2 U) d

| vtp_abs: forall Σ ϰ φ T1 d1 T2 d2 T3 d3 T4 d4 df1 df2 t,
  closed_tm 2 0 (‖Σ‖) t ->
  closed_Qual 0 0 (‖Σ‖) df2↑ ->
  closed_ty 0 0 (‖Σ‖) (TFun d3 d4 T3 T4) -> (* supertype *)
  closed_ty 0 0 (‖Σ‖) (TFun d1 d2 T1 T2) -> (* subtype *)
  has_type [(bind_tm, false,T1,d1) ; (bind_tm, true, (TFun d1 d2 T1 T2), df1)]
            (df1 ⊔ $!0 ⊔ $!1) Σ (t <~²ᵗ ([] : tenv)) (T2 <~²ᵀ ([] : tenv)) (d2 <~²ᵈ ([] : tenv)) ->
  stp [] Σ T3 d3 T1 d1 ->
  qstp [] Σ df1 df2 ->
  stp [(bind_tm, false,T3, d3) ; (bind_tm, true, (TFun d1 d2 T1 T2), {♦})] Σ
      (T2 <~²ᵀ ([] : tenv)) (d2 <~²ᵈ ([] : tenv))
      (T4 <~²ᵀ ([] : tenv)) (d4 <~²ᵈ ([] : tenv)) ->
  d1 ⊑↑ df1 ⊔ {♦} ->
  ♦∉ df1 ->
  kill_sep ϰ df2 ->
  kill_sep (local_locs t) df2 ->
  vtp Σ ϰ φ (tabs t) (TFun d3 d4 T3 T4) df2

| vtp_top: forall Σ ϰ φ t T d,
   vtp Σ ϰ φ t T d ->
  vtp Σ ϰ φ t TTop d
.
#[global] Hint Constructors vtp : core.



Lemma vtp_closed:
  forall {Σ ϰ φ t T d}, vtp Σ ϰ φ t T d ->
    closed_tm 0 0 (‖Σ‖) t /\
    closed_ty 0 0 (‖Σ‖) T /\
    closed_Qual 0 0 (‖Σ‖) d↑.
Proof.
  intros. induction H; intuition.
  - apply qstp_closed in H4. subst. intuition.
  - constructor. apply sindexr_var_some' in H4; intuition.
  - constructor. apply stp_closed in H6. intuition.  simpl in *. auto.
Qed.

Lemma vtp_kill_sep : forall {Σ ϰ φ t T d},
  vtp Σ ϰ φ t T d ->
  kill_sep ϰ d.
Proof.
  intros. induction H; auto.
Qed.


Lemma vtp_qual_widening : forall {Σ ϰ φ t T1 d1 d2},
  closed_Qual 0 0 (‖Σ‖) ϰ↑ ->
  vtp Σ ϰ φ t T1 d1 -> qstp [] Σ d1 d2 ->
  kill_sep ϰ d2 -> kill_sep (local_locs t) d2 ->
  vtp Σ ϰ φ t T1 d2.
Proof.
  intros. induction H0.
  - econstructor; eauto.
  - econstructor; eauto.
    eapply qstp_closed in H1. intuition.
  - eapply qstp_empty in H13. eapply qstp_empty in H14.
    assert (q1 = q2). eapply subQual_eq; eauto. subst.
    econstructor. 7: eauto. all: eauto.
    eapply qstp_closed in H1. intuition.
  - econstructor; eauto.
    eapply qstp_closed in H1. intuition.
  - econstructor; eauto.
Qed.

Lemma vtp_type_widening: forall {Σ ϰ φ T1 T2 d1 d2 d3 t},
  closed_Qual 0 0 (‖Σ‖) ϰ↑ ->
  vtp Σ ϰ φ t T1 d1 -> stp [] Σ T1 d2 T2 d3 ->
  vtp Σ ϰ φ t T2 d1.
Proof.
  intros Σ ϰ φ T1 T2 d1 d2 d3 t Hclϰ HVtp HStp. remember t as tt. remember [] as Γ.
  induction HStp; subst.
  - apply qstp_closed in H0 as HC. intuition.
    inversion HVtp; subst; econstructor; eauto.
  - inversion HVtp.
  - inversion HVtp.
  - eapply vtp_closed in HVtp as HC. intuition.
    eapply stp_closed in HStp1 as HC. intuition.
    inversion HVtp; subst; econstructor; eauto.
    assert (narrow: stp [(bind_ty, false,T3, d3); (bind_tm, true,TAll d7 d8 T0 T5, {♦})] Σ (open_ty' ([]: tenv) T5)(openq' ([]:tenv) d8) (open_ty' ([]:tenv) T2) (openq' ([]: tenv) d2)). {
      eapply narrowing_stp_ty; eauto.
      apply weaken_stp. auto.
    }
    simpl in *. eapply s_trans; eauto.
    specialize (@narrowing_stp_gen [(bind_ty, false, T3, d3)] true (TAll d0 d2 T1 T2) {♦} [] Σ (T2 <~²ᵀ ([]:tenv)) (d2 <~²ᵈ ([]:tenv)) (T4 <~²ᵀ ([]:tenv)) (d4 <~²ᵈ ([]:tenv))) as narrowing.
    simpl in narrowing. intuition.
  - auto.
  - inversion HVtp; subst. intros. eapply vtp_loc. 6: eapply H9. all: eauto.
    apply qstp_closed in H0; destruct H0; auto.
  - inversion HVtp; subst; econstructor; eauto.
    assert (narrow: stp [(bind_tm, false,T3, d3); (bind_tm, true,TFun d7 d8 T0 T5, {♦})] Σ (open_ty' ([]: tenv) T5)(openq' ([]:tenv) d8) (open_ty' ([]:tenv) T2) (openq' ([]: tenv) d2)). {
      eapply narrowing_stp; eauto. intros. inversion H2.
      apply weaken_stp. auto.
    }
    simpl in *. eapply s_trans; eauto.
    assert (forall T (a:T) (b:T), [a;b] = [a]++[b]) as R. eauto.
    rewrite R in HStp2. rewrite R.
    eapply @narrowing_stp_gen with (U := (TFun d0 d2 T1 T2))(du:={♦})(Γ2 := []: tenv)  in HStp2; auto. eapply HStp2.
    constructor; auto.
  - intuition.
Qed.

Lemma vtp_widening: forall {Σ ϰ φ T1 d1 T2 d2 t},
  closed_Qual 0 0 (‖Σ‖) ϰ↑ ->  kill_sep ϰ d2 -> kill_sep (local_locs t) d2 ->
  vtp Σ ϰ φ t T1 d1 -> stp [] Σ T1 d1 T2 d2 -> vtp Σ ϰ φ t T2 d2.
Proof.
  intros Σ ϰ φ T1 d1 T2 d2 t Hclϰ Hsep HsepLL HVtp HStp.
  eapply vtp_closed in HVtp as HC. intuition.
  assert (stp [] Σ T1 d1 T2 d1). { eapply stp_qual_irrelevance; auto. eapply HStp.  }
  eapply vtp_type_widening in HVtp; auto. 2: eapply H0.
  eapply vtp_qual_widening; eauto. eapply stp_qstp_inv in HStp. eauto.
Qed.

Lemma has_type_vtp: forall {Σ ϰ φ t T d},
  closed_Qual 0 0 (‖Σ‖) ϰ↑ ->
  value t ->
  has_type [] φ Σ t T d ->
  kill_sep ϰ φ ->
  vtp Σ ϰ φ t T d.
Proof.
  intros Σ ϰ φ t T d Hclϰ HV Ht HWFK. remember [] as Γ. induction Ht; eauto; subst; try inversion HV; subst; intuition;
    try solve [simpl in H1; discriminate].
  - (* ttabs *) subst. apply has_type_closed in Ht as Hcl. intuition.
    inversion H0. subst.  eapply vtp_tabs. 4: eauto. all: auto.
    + eapply stp_refl; auto.
    + apply qstp_refl; auto. eapply closed_Qual_sub. 2: eauto. auto.
    + apply stp_refl; intuition.
    + eapply kill_sep_sub; eauto.
  - apply vtp_base; auto. apply kill_sep_empty.
  - (* tabs *) subst.  subst. apply has_type_closed in Ht as Hcl. intuition.
    inversion H0. subst.  eapply vtp_abs. 5: eauto. all: auto.   eapply closed_Qual_sub. 2: eauto. auto.
    + eapply stp_refl; auto.
    + apply qstp_refl; auto. eapply closed_Qual_sub. 2: eauto. auto.
    + apply stp_refl; auto.
    + eapply kill_sep_sub; eauto.
  - (* tloc *) intros.  eapply vtp_loc. 6: eauto. 1-4: eauto. 4,6,7: apply qstp_refl; eauto. 4,5: eauto. 4:{ apply Q_lift_closed. eauto. }
    + Qcrush.
    + apply stp_refl; auto.
    + apply stp_refl; auto.
    + eapply kill_sep_sub; eauto.
  - intuition. eapply vtp_widening; eauto. eapply kill_sep_sub_fresh; eauto.
  - intuition. eapply vtp_widening; eauto. eapply kill_sep_sub_fresh; eauto.
  - intuition. eapply vtp_widening; eauto. eapply kill_sep_sub_fresh; eauto.
  - intuition. eapply vtp_widening; eauto. eapply kill_sep_sub_fresh; eauto.
Qed.



Lemma kill_sep_qstp : forall Σ l d1 d2,
  kill_sep &! l d2 -> qstp [] Σ d1 d2 -> kill_sep &! l d1.
Proof.
  intros. remember [] as Γ. induction H0; subst; auto.
  - eapply kill_sep_sub; eauto.
  - inversion H0.
  - inversion H0.
  - inversion H0.
  - inversion H0.
  - apply kill_sep_qor_rev in H; destruct H. apply kill_sep_qor; auto.
Qed.


Lemma qstp_delete_fresh : forall {Σ q1 q2}, qstp [] Σ q1 q2 -> ♦∉ q1 -> qstp [] Σ q1 (false, (qfvs q2), (qbvs q2), (qlocs q2)).
  intros. specialize (qstp_closed H) as Hcl. intuition. apply qstp_empty in H. apply qs_sq. Qcrush. Qcrush.
Qed.

Lemma vtp_non_fresh : forall {Σ ϰ φ v T q},
  vtp Σ ϰ φ v T q -> wf_senv Σ -> vtp Σ ϰ φ v T (false, (qfvs q), (qbvs q), (qlocs q)).
Proof. intros. induction H.
  + apply qstp_closed in H5 as Hcl_qstp. intuition. eapply vtp_tabs; eauto.
    apply qstp_empty in H5. econstructor; eauto. Qcrush. eapply kill_sep_fresh_irrlevance; auto. eapply kill_sep_fresh_irrlevance; auto.
  + inversion H. subst. econstructor; auto. clear - H1. eapply kill_sep_fresh_irrlevance; auto.
  + inversion H2. inversion H3. intuition.
    assert (♦∉ q2). eapply qstp_non_fresh; eauto.
    econstructor. 6: eapply H5. all: eauto.
    apply qstp_delete_fresh; auto. (*Qcrush. *) eapply kill_sep_fresh_irrlevance; auto.
  + inversion H2. subst. econstructor; eauto.
    apply qstp_delete_fresh; auto. eapply kill_sep_fresh_irrlevance; auto. eapply kill_sep_fresh_irrlevance; auto.
  + apply vtp_closed in IHvtp as Hcl_vtp; intuition. eapply vtp_top; eauto.
Qed.


Lemma vtp_kill_retype : forall {Σ ϰ φ t T d l},
  kill_sep ϰ φ ->
  vtp Σ ϰ φ t T d ->
  kill_sep &!l d ->
  vtp Σ (ϰ ⊔ &!l) (q_remove Σ l φ) t T d.
Proof.
  intros. induction H0.
  - eapply vtp_tabs; eauto. apply kill_sep_newkill; auto.
  - eapply vtp_base; auto. apply kill_sep_newkill; auto.
  - eapply vtp_loc. 6: eauto. all: eauto. eapply kill_sep_qstp in H9; eauto. apply q_remove_in; auto. apply sindexr_var_some' in H6; intuition. apply kill_sep_newkill; auto.
  - eapply vtp_abs; eauto. apply kill_sep_newkill; auto.
  - eapply vtp_top; eauto.
Qed.

(* alternative form of weaken_flt *)
Lemma vtp_weaken_flt: forall {Σ ϰ φ t T d},
  vtp Σ ϰ φ t T d ->
  forall {φ'}, φ ⊑↑ φ' -> closed_Qual 0 0 (‖Σ‖) φ'↑ ->
  vtp Σ ϰ φ' t T d.
Proof.
  intros. induction H; simpl.
  - eapply vtp_tabs; eauto.
  - eapply vtp_base; auto.
  - eapply vtp_loc. 6: eauto. all: eauto. clear - H0 H5. Qcrush.
  - eapply vtp_abs; eauto.
  - eapply vtp_top; eauto.
Qed.


Lemma weaken_flt_value : forall {Γ φ Σ t T d},
  value t ->
  has_type Γ φ Σ t T d ->
  forall {φ'}, φ ⊑↑ φ' -> closed_Qual 0 (‖Γ‖) (‖Σ‖) φ'↑ ->
  has_type Γ φ' Σ t T d.
Proof.
  intros Γ φ Σ t T d Hv HT.
  induction HT; intros; inversion Hv; subst.
  - eapply t_tabs; eauto. eapply Subq_trans; eauto.
  - eapply t_base; eauto.
  - eapply t_abs; eauto. eapply Subq_trans; eauto.
  - eapply t_loc; eauto. eapply Subq_trans; eauto.
  - eapply t_sub; eauto. assert (φ ⊔ {♦} ⊑↑ φ' ⊔ {♦}). eapply Subq_qor; eauto. eapply Subq_trans; eauto.
  - eapply t_sub; eauto. assert (φ ⊔ {♦} ⊑↑ φ' ⊔ {♦}). eapply Subq_qor; eauto. eapply Subq_trans; eauto.
  - eapply t_sub. 2: eauto. eauto. assert (φ ⊔ {♦} ⊑↑ φ' ⊔ {♦}). eapply Subq_qor; eauto. eapply Subq_trans; eauto. simpl. unfold kill_sep; Qcrush.
  - eapply t_sub; eauto. assert (φ ⊔ {♦} ⊑↑ φ' ⊔ {♦}). eapply Subq_qor; eauto. eapply Subq_trans; eauto.
Qed.



Lemma vtp_has_type: forall {Σ ϰ t T d φ},
  vtp Σ ϰ φ t T d -> has_type [] d Σ t T d.
  intros. induction H.
  + (* ttabs *) assert (has_type [] df1 Σ (ttabs t) (TAll d1 d2 T1 T2) df1). {
    constructor; eauto. apply qstp_closed in H4 as Hcl; intuition. apply qstp_empty in H4. eapply kill_sep_sub; eauto. }
    assert (has_type [] df2 Σ (ttabs t) (TAll d1 d2 T1 T2) df1). {
    inversion H1. subst. eapply weaken_flt with  (φ' := df2) in H10; intuition.
    eapply qstp_empty; eauto. eapply qstp_closed; eauto. }
    eapply t_sub. eauto. constructor; auto. auto.
    simpl. auto.
  + (* tunit *) econstructor; auto. simpl; unfold kill_sep; Qcrush.
  + (* tloc *) eapply qstp_empty in H9 as H10'.
    eapply t_sub; auto. eapply t_loc; eauto.
    apply qstp_empty in H7; auto.
    eapply s_ref; auto.
    simpl. unfold kill_sep; Qcrush.
  + (* tabs *) assert (has_type [] df1 Σ (tabs t) (TFun d1 d2 T1 T2) df1). {
    constructor; eauto. apply qstp_closed in H5 as Hcl; intuition.
    apply qstp_empty in H5. eapply kill_sep_sub; eauto.  }
    assert (has_type [] df2 Σ (tabs t) (TFun d1 d2 T1 T2) df1). {
    inversion H2. subst. eapply weaken_flt with  (φ' := df2) in H11; intuition.
    eapply qstp_empty; eauto. }
    eapply t_sub. eauto. constructor; auto. intuition.
    simpl. auto.
  + (* ttop *)
    apply has_type_closed in IHvtp as Hcl. intuition.
      econstructor; eauto.
    apply has_type_local_loc_sep in IHvtp; auto.
Qed.


Lemma vtp_weaken_store : forall {Σ ϰ φ v T q},
  vtp Σ ϰ φ v T q -> wf_senv Σ -> forall {T' q'},
  closed_Qual 0 0 (‖Σ‖) q'↑ ->
  vtp ([(T', q')] :: Σ) ϰ (φ) v T q.
Proof.
  intros. induction H; auto.
  - inversion H2; inversion H3; subst. eapply vtp_tabs. 4:{ eapply weaken_2D_store. 2: eauto. eapply H4; eauto. auto. simpl. unfold extends.
    apply closed_qenv_extend. apply closed_qenv_extend. apply closed_qenv_empty. apply []. simpl. apply qstp_closed in H6; destruct H6. eapply closed_Qual_monotone; eauto. simpl. eapply closed_Qual_monotone; eauto. clear - H0. Qcrush. }
    eapply closed_tm_monotone; eauto. eapply closed_ty_monotone; eauto. eapply closed_ty_monotone; eauto.
    eapply weaken_stp_store_ext; eauto. replace ([(T', q')] :: Σ) with ([ [(T', q')] ] ++ Σ) by auto. eapply weaken_qstp_store; eauto. eapply weaken_stp_store_ext; eauto.
    auto. auto. auto. auto.
  - apply vtp_base; auto. eapply closed_Qual_monotone; eauto.
  - apply sindexr_var_some' in H6 as H6'. eapply vtp_loc. 6: rewrite sindexr_skip; eauto. 1,3,4: eapply closed_Qual_monotone; eauto. eapply closed_ty_monotone; eauto. clear - H5. Qcrush. lia.
    1-2: eapply weaken_stp_store_ext; eauto. 1,3,4: replace ([(T', q')] :: Σ) with ([ [(T', q')] ] ++ Σ) by auto; eapply weaken_qstp_store; eauto. Qcrush. auto.
  - inversion H3; inversion H4; subst. eapply vtp_abs. 5:{ eapply weaken_2D_store. 1: eapply H5; eauto. auto.
    apply closed_qenv_extend. apply closed_qenv_extend. apply closed_qenv_empty. apply []. simpl. apply qstp_closed in H7; destruct H7. eapply closed_Qual_monotone; eauto. simpl. eapply closed_Qual_monotone; eauto. clear - H0. Qcrush. }
    eapply closed_tm_monotone; eauto. eapply closed_Qual_monotone; eauto. eapply closed_ty_monotone; eauto. eapply closed_ty_monotone; eauto.
    eapply weaken_stp_store_ext; eauto. replace ([(T', q')] :: Σ) with ([ [(T', q')] ] ++ Σ) by auto. eapply weaken_qstp_store; eauto. eapply weaken_stp_store_ext; eauto.
    auto. auto. apply qstp_closed in H7; destruct H7. auto. auto.
  - eapply vtp_top; eauto.
Qed.

Lemma vtp_weaken_2D_store : forall {Σ ϰ φ v T q},
  vtp Σ ϰ φ v T q -> wf_senv Σ -> forall {Σ'},
  Σ' ⊇₂ Σ ->
  vtp (Σ') ϰ (φ) v T q.
Proof.
  intros. induction H; auto.
  - inversion H2; inversion H3; subst. eapply vtp_tabs. 4:{ eapply weaken_2D_store. 2: eauto. eapply H4; eauto. auto. simpl. unfold extends.
    apply closed_qenv_extend. apply closed_qenv_extend. apply closed_qenv_empty. apply []. simpl. apply qstp_closed in H6; destruct H6. eapply closed_Qual_monotone; eauto. simpl. eapply closed_Qual_monotone; eauto. clear - H0. Qcrush. }
    eapply closed_tm_monotone; eauto. eapply closed_ty_monotone; eauto. eapply closed_ty_monotone; eauto.
    eapply weaken_2D_stp_store_ext; eauto. eapply weaken_2D_qstp_store; eauto. eapply weaken_2D_stp_store_ext; eauto.
    auto. auto. auto. auto.
  - apply vtp_base; auto. eapply closed_Qual_monotone; eauto.
  - apply sindexr_var_some' in H6 as H6'. eapply vtp_loc. 6: eapply extends_2D_sindexr; eauto. 1,3,4: eapply closed_Qual_monotone; eauto. eapply closed_ty_monotone; eauto. auto.
    1-2: eapply weaken_2D_stp_store_ext; eauto. 1,3,4: eapply weaken_2D_qstp_store; eauto. Qcrush. auto.
  - inversion H3; inversion H4; subst. eapply vtp_abs. 5:{ eapply weaken_2D_store. 2: eauto. 1: eapply H5; eauto. auto.
    apply closed_qenv_extend. apply closed_qenv_extend. apply closed_qenv_empty. apply []. simpl. apply qstp_closed in H7; destruct H7. eapply closed_Qual_monotone; eauto. simpl. eapply closed_Qual_monotone; eauto. clear - H0. Qcrush. }
    eapply closed_tm_monotone; eauto. eapply closed_Qual_monotone; eauto. eapply closed_ty_monotone; eauto. eapply closed_ty_monotone; eauto.
    eapply weaken_2D_stp_store_ext; eauto. eapply weaken_2D_qstp_store; eauto. eapply weaken_2D_stp_store_ext; eauto.
    auto. auto. apply qstp_closed in H7; destruct H7. auto. auto.
  - eapply vtp_top; eauto.
Qed.


Lemma vtp_weaken : forall {Σ ϰ φ v T q},
  vtp Σ ϰ φ v T q -> wf_senv Σ -> forall {T' q'},
  closed_Qual 0 0 (‖Σ‖) q'↑ ->
  vtp ([(T', q')] :: Σ) ϰ (φ ⊔ &!(‖Σ‖)) v T q.
Proof.
  intros. induction H; auto.
  - inversion H2; inversion H3; subst. eapply vtp_tabs. 4:{ eapply weaken_2D_store. 2: eauto. 1: eapply H4; eauto. auto. simpl. unfold extends.
    apply closed_qenv_extend. apply closed_qenv_extend. apply closed_qenv_empty. apply []. simpl. apply qstp_closed in H6; destruct H6. eapply closed_Qual_monotone; eauto. simpl. eapply closed_Qual_monotone; eauto. clear - H0. Qcrush. }
    eapply closed_tm_monotone; eauto. eapply closed_ty_monotone; eauto. eapply closed_ty_monotone; eauto.
    eapply weaken_stp_store_ext; eauto. replace ([(T', q')] :: Σ) with ([ [(T', q')] ] ++ Σ) by auto. eapply weaken_qstp_store; eauto. eapply weaken_stp_store_ext; eauto.
    auto. auto. apply qstp_closed in H6; destruct H6. auto. auto.
  - apply vtp_base; auto. eapply closed_Qual_monotone; eauto.
  - apply sindexr_var_some' in H6 as H6'. eapply vtp_loc. 6: eapply extends_2D_sindexr; eauto. 1,3,4: eapply closed_Qual_monotone; eauto. eapply closed_ty_monotone; eauto. auto. Qcrush.
    1-2: eapply weaken_2D_stp_store_ext; eauto. 1,3,4: eapply weaken_2D_qstp_store; eauto. Qcrush. auto.
  - inversion H3; inversion H4; subst. eapply vtp_abs. 5:{ eapply weaken_2D_store. 2: eauto. eauto.
    apply closed_qenv_extend. apply closed_qenv_extend. apply closed_qenv_empty. apply []. simpl. apply qstp_closed in H7; destruct H7. eapply closed_Qual_monotone; eauto. simpl. eapply closed_Qual_monotone; eauto. clear - H0. Qcrush. }
    eapply closed_tm_monotone; eauto. eapply closed_Qual_monotone; eauto. eapply closed_ty_monotone; eauto. eapply closed_ty_monotone; eauto.
    eapply weaken_stp_store_ext; eauto. replace ([(T', q')] :: Σ) with ([ [(T', q')] ] ++ Σ) by auto. eapply weaken_qstp_store; eauto. eapply weaken_stp_store_ext; eauto.
    auto. auto. apply qstp_closed in H7; destruct H7. auto. auto.
  - eapply vtp_top; eauto.
Qed.



Lemma subst_qstp :  forall {Γ bd b Tf df df' Σ d1 d2},
    qstp (Γ ++ [(bd, b, Tf, df)]) Σ d1 d2 ->
    closed_ty 0 0 (‖Σ‖) Tf ->
    closed_Qual 0 0 (‖Σ‖) df'↑ ->
    Substq (Γ ++ [(bd, b, Tf, df)]) Σ df df' ->
    qstp ({0 |-> Tf ~ df' }ᴳ Γ) Σ ({0 |-> df' }ᵈ d1) ({0 |-> df' }ᵈ d2).
  intros Γ bd b Tf df df' Σ d1 d2 H. remember (Γ ++ [(bd, b, Tf, df)]) as Γ'.
  generalize dependent Γ. generalize dependent df.  generalize dependent Tf.
  induction H; intros; subst.
  - apply qs_sq. apply subst_qual_subqual_monotone. auto. eapply closed_qual_subst1'; eauto.
  -  bdestruct (f =? 0).
    * pose (H' := H). subst. rewrite indexr_skips in H'; auto. simpl in H'. inversion H'. subst.
      rewrite subst1_qor_dist. rewrite subst1_just_fv0. erewrite subst1_qual_id; auto. 2: eauto. inversion H4; subst.
      + rewrite qor_idem. apply qs_sq; auto. rewrite subst1_env_length. eapply closed_qual_monotone; eauto. lia.
      + rewrite <- H9 in H1. apply not_fresh_fresh_false in H1. contradiction.
    * rewrite subst1_qor_dist. destruct f. lia. rewrite <- subst1_just_fv.
      eapply qs_self; eauto. eapply @indexr_subst1 with (dx:=df') in H; try lia. eauto.
      eapply closed_qual_subst1; eauto.
  -  bdestruct (f =? 0).
    * pose (H' := H). subst. rewrite indexr_skips in H'; auto. simpl in H'. inversion H'. subst.
      rewrite subst1_qor_dist. rewrite subst1_just_fv0. erewrite subst1_qual_id; auto. 2: eauto. inversion H4; subst.
      + rewrite qor_idem. apply qs_sq; auto. rewrite subst1_env_length. eapply closed_qual_monotone; eauto. lia.
      + rewrite <- H9 in H1. apply not_fresh_fresh_false in H1. contradiction.
    * rewrite subst1_qor_dist. destruct f. lia. rewrite <- subst1_just_fv.
      eapply qs_self_all; eauto. eapply @indexr_subst1 with (dx:=df') in H; try lia. eauto.
      eapply closed_qual_subst1; eauto.
  - bdestruct (x =? 0).
    * subst. pose (H' := H). subst. rewrite indexr_skips in H'; auto. simpl in H'. inversion H'. subst.
      rewrite subst1_just_fv0. erewrite subst1_qual_id; auto. 2: eauto. inversion H5; subst.
      + apply qs_sq; auto. rewrite subst1_env_length. eapply closed_qual_monotone; eauto. lia.
      + rewrite <- H10 in H2. apply not_fresh_fresh_false in H2. contradiction.
    * destruct x. lia. rewrite <- subst1_just_fv. eapply qs_qvar. apply @indexr_subst1 with (Tx := Tf)(dx:=df') in H; try lia.
      eauto. eapply closed_ty_subst1; eauto. eapply closed_qual_subst1; eauto. eauto.
  - bdestruct (x =? 0).
    * subst. pose (H' := H). subst. rewrite indexr_skips in H'; auto. simpl in H'. inversion H'; destruct bd; subst; try discriminate.
      rewrite subst1_just_fv0. erewrite subst1_qual_id; auto. 2: eauto. inversion H5; subst.
      + apply qs_sq; auto. erewrite subst1_env_length. eapply closed_qual_monotone; eauto. lia.
      + rewrite <- H11 in H2. apply not_fresh_fresh_false in H2. contradiction.
    * destruct x. lia. rewrite <- subst1_just_fv. eapply qs_qvar_ty. apply @indexr_subst1 with (Tx := Tf)(dx:=df') in H; try lia.
      eauto. eapply closed_ty_subst1; eauto. eapply closed_qual_subst1; eauto. eauto.
  - repeat rewrite subst1_qor_dist. eapply qs_cong; auto. eauto. eapply closed_qual_subst1'; eauto.
  - eapply qs_trans. eapply IHqstp1; eauto. eauto.
    Unshelve. all : auto.
Qed.

Lemma subst_ty_qstp :  forall {Γ T d d' Σ d1 d2},
    qstp (Γ ++ [(bind_ty, false, T, d)]) Σ d1 d2 ->
    closed_ty 0 0 (length Σ) T ->
    closed_Qual 0 0 (length Σ) d'↑ ->
    Substq (Γ ++ [(bind_ty, false, T, d)]) Σ d d' ->
    qstp ({0 |-> T ~ d' }ᴳ Γ) Σ ({0 |-> d' }ᵈ d1) ({0 |-> d' }ᵈ d2).
Proof. intros Γ T d d' Σ d1 d2 H. remember (Γ ++ [(bind_ty, false, T, d)]) as Γ'.
  generalize dependent Γ. generalize dependent d.  generalize dependent T.
  induction H; intros; subst.
  - apply qs_sq. apply subst_qual_subqual_monotone. auto. eapply closed_qual_subst1'; eauto.
  -  bdestruct (f =? 0).
    * pose (H' := H). subst. rewrite indexr_skips in H'; auto. simpl in H'. inversion H'.
    * rewrite subst1_qor_dist. destruct f. lia. rewrite <- subst1_just_fv.
      eapply qs_self; eauto. eapply @indexr_subst1 with (dx:=d') in H; try lia. eauto.
      eapply closed_qual_subst1; eauto.
  -  bdestruct (f =? 0).
    * pose (H' := H). subst. rewrite indexr_skips in H'; auto. simpl in H'. inversion H'.
    * rewrite subst1_qor_dist. destruct f. lia. rewrite <- subst1_just_fv.
      eapply qs_self_all; eauto. eapply @indexr_subst1 with (dx:=d') in H; try lia. eauto.
      eapply closed_qual_subst1; eauto.
  - bdestruct (x =? 0).
    * subst. pose (H' := H). subst. rewrite indexr_skips in H'; auto. simpl in H'. inversion H'.
    * destruct x. lia. rewrite <- subst1_just_fv. eapply qs_qvar.
      apply @indexr_subst1 with (Tx := T)(dx:=d') in H; try lia.
      simpl in H. eauto. eapply closed_ty_subst1; eauto. eapply closed_qual_subst1; eauto. eauto.
  - bdestruct (x =? 0).
    * subst. pose (H' := H). erewrite indexr_skips in H'; auto. simpl in H'. inversion H'. subst.
      rewrite subst1_just_fv0. erewrite subst1_qual_id; auto. 2: eauto. inversion H5; subst.
      + apply qs_sq; auto. erewrite subst1_env_length. eapply closed_qual_monotone; eauto. lia.
      + rewrite <- H10 in H2. apply not_fresh_fresh_false in H2. contradiction.
    * destruct x. lia. rewrite <- subst1_just_fv. eapply qs_qvar_ty.
      apply @indexr_subst1 with (Tx := T)(dx:=d') in H; try lia. simpl in H. eauto.
      eapply closed_ty_subst1; eauto. eapply closed_qual_subst1; eauto. eauto.
  - repeat rewrite subst1_qor_dist. eapply qs_cong. eapply IHqstp; eauto. eapply closed_qual_subst1'; eauto.
  - eapply qs_trans. eapply IHqstp1; eauto. eapply IHqstp2; eauto.
  Unshelve. all : auto.
Qed.

Lemma Substq_weaken : forall Γ Σ a df df',
  closed_Qual 0 (‖Γ‖) (‖Σ‖) df'↑ ->
  closed_qenv_qn (‖Γ‖) Γ ->
  Substq Γ Σ df df' ->
  Substq (a :: Γ) Σ df df'.
intros. induction H1; subst. constructor; auto. replace (q_trans_tenv Γ df ⋒ q_trans_tenv Γ dx) with (q_trans_tenv (a::Γ) df ⋒ q_trans_tenv (a::Γ) dx). constructor; auto. simpl. eapply closed_Qual_monotone; eauto. unfold q_trans_tenv. repeat rewrite q_trans''_extend_closed_id'; auto. repeat rewrite q_trans''_fuel_max with (E:=Γ) (fuel:=(‖ a :: Γ ‖)); auto. all: simpl; Qcrush; exfalso; eauto.
Qed.



Lemma subst_stp : forall{T1 T2},
    forall {Γ bd b Tf df df' Σ d1 d2},
      stp (Γ ++ [(bd, b,Tf,df)]) Σ T1 d1 T2 d2 ->
      wf_tenv (Γ ++ [(bd, b,Tf,df)]) Σ ->
      closed_ty 0 0  (‖Σ‖) Tf ->
      closed_Qual 0 0 (‖Σ‖) df'↑ ->
      Substq (Γ ++ [(bd, b,Tf,df)]) Σ df df' ->
      stp ({ 0 |-> Tf ~ df' }ᴳ Γ) Σ
          ({ 0 |-> Tf ~ df' }ᵀ T1) ({ 0 |-> df' }ᵈ d1)
          ({ 0 |-> Tf ~ df' }ᵀ T2) ({ 0 |-> df' }ᵈ d2).
  intros T1 T2 Γ bd b Tf df df' Σ d1 d2 HS.
  remember (Γ ++ [(bd, b, Tf, df)]) as Γ'.
  generalize dependent Γ. generalize dependent df.  generalize dependent Tf. induction HS; intros; subst.
  - (* TTop *) simpl. constructor. eapply closed_ty_subst1'; eauto. eapply subst_qstp; eauto.
  - (* TVarF x *) simpl.  (bdestruct (x =? 0)).
    * (*x is 0 *) rewrite indexr_skips in H; simpl; auto; try lia. simpl in H. subst. simpl in H.
      inversion H. subst. eapply subst_qstp in H0; eauto. eapply stp_refl; eauto.
      eapply closed_ty_monotone; eauto. lia.

    * (*x is in Γ0*) assert (Hx: 1 <= x); try lia. destruct x; try lia.
      destruct v. destruct p. specialize (@subst_qstp _ _  _ _ _ df' _ _ _  H0); intuition.
      eapply stp_refl; eauto. constructor. erewrite subst1_env_length.
      erewrite <-  indexr_insert_ge in  H.  replace (Γ0 ++  [])  with Γ0 in H.
      apply indexr_var_some' in  H. intuition. intuition.
      intuition.
  - (* TVarF x  trans *)
    destruct bd; simpl; bdestruct (x =? 0).
    (* bind_tm *)
    * (*x is 0 *) subst. rewrite indexr_skips in H. simpl in H. inversion H. simpl. lia.
    * (*x is in Γ0*) intuition. apply @indexr_subst1 with (Tx := Tf)(dx :=df') in H; try lia.
    econstructor; eauto.
    erewrite subst1_ty_id; auto. apply H0.
    (* bind_ty *)
    * (*x is 0 *) subst. eapply @indexr_subst1' in H.
    specialize (IHHS Tf df Γ0). intuition. subst. erewrite subst1_ty_id in H7; eauto.
    * (*x is in Γ0*) intuition. apply @indexr_subst1 with (Tx := Tf)(dx :=df') in H; try lia.
    econstructor. eauto.
    erewrite subst1_ty_id; eauto. eapply IHHS; eauto.
  - (* TAll *) simpl. inversion H. inversion H0. subst.  econstructor; auto.
    1,2: constructor; try eapply closed_ty_subst1'; eauto; eapply closed_qual_subst1'; eauto.
    eapply subst_qstp; eauto.
    eapply IHHS1; eauto.
    specialize (IHHS2 Tf df ((bind_ty, false, T3, d3) :: (bind_tm, true, TAll d1 d2 T1 T2, {♦}) :: Γ0)). intuition.
    unfold open_ty' in *. unfold open_ty in *.
    unfold openq' in *. unfold openq in *.
    rewrite app_length in *. rewrite subst1_env_length. simpl in *.
    replace (‖Γ0‖ + 1) with (S (‖Γ0‖)) in *; try lia.
    rename H6 into HH.
    erewrite <- open_subst1_ty_comm in HH; eauto. erewrite <- open_subst1_ty_comm in HH; eauto.
    erewrite <- open_subst1_ty_comm in HH; eauto. erewrite <- open_subst1_ty_comm in HH; eauto.
    erewrite <- open_subst1_qual_comm in HH; eauto. erewrite <- open_subst1_qual_comm in HH; eauto.
    erewrite <- open_subst1_qual_comm in HH; eauto. erewrite <- open_subst1_qual_comm in HH; eauto.
    apply HH; auto.
    inversion H0. inversion H. subst. constructor; eauto. constructor; eauto. 1-3: simpl; rewrite app_length; simpl; rewrite Nat.add_1_r. auto. eapply closed_ty_monotone; eauto. eapply closed_Qual_monotone; eauto.
    apply Substq_weaken. simpl; rewrite app_length; simpl. eapply closed_Qual_monotone; eauto. lia. eapply wf_tenv_closed_qenv_qn. econstructor; eauto. simpl; rewrite app_length; simpl. eapply closed_ty_monotone; eauto. lia.
    apply Substq_weaken; eauto. simpl; rewrite app_length; simpl. eapply closed_Qual_monotone; eauto. lia.
  - simpl. constructor. eapply subst_qstp; eauto.
  - specialize (stp_closed HS1). specialize (stp_closed HS2). intuition.
    simpl. constructor. eapply subst_qstp; eauto.
    eapply IHHS1; eauto. eapply IHHS2; eauto.
    1, 2: eapply subst_qstp; eauto.
  - simpl. constructor. inversion H. subst. 2 : inversion H0. subst.
    1,2: constructor; try eapply closed_ty_subst1'; eauto; eapply closed_qual_subst1'; eauto.
    eapply subst_qstp; eauto. eapply IHHS1; eauto.
    unfold open_ty' in *. unfold open_ty in *.
    unfold openq' in *. unfold openq in *.
    rewrite app_length in *. rewrite subst1_env_length. simpl in *.
    replace (‖Γ0‖ + 1) with (S (‖Γ0‖)) in *; try lia.
    specialize (IHHS2 Tf df ((bind_tm, false, T3, d3) :: (bind_tm, true, TFun d1 d2 T1 T2, {♦}) :: Γ0)). intuition. rename H6 into IHHS2. simpl in IHHS2.
    erewrite <- open_subst1_ty_comm in IHHS2; eauto. erewrite <- open_subst1_ty_comm in IHHS2; eauto.
    erewrite <- open_subst1_ty_comm in IHHS2; eauto. erewrite <- open_subst1_ty_comm in IHHS2; eauto.
    erewrite <- open_subst1_qual_comm in IHHS2; eauto. erewrite <- open_subst1_qual_comm in IHHS2; eauto.
    erewrite <- open_subst1_qual_comm in IHHS2; eauto. erewrite <- open_subst1_qual_comm in IHHS2; eauto.
    apply IHHS2; auto.
    inversion H0. inversion H. subst. constructor; eauto. constructor; eauto. 1-3: simpl; rewrite app_length; simpl; rewrite Nat.add_1_r. auto. eapply closed_ty_monotone; eauto. eapply closed_Qual_monotone; eauto.
    apply Substq_weaken. simpl; rewrite app_length; simpl. eapply closed_Qual_monotone; eauto. lia. eapply wf_tenv_closed_qenv_qn. econstructor; eauto. simpl; rewrite app_length; simpl. eapply closed_ty_monotone; eauto. lia.
    apply Substq_weaken; eauto. simpl; rewrite app_length; simpl. eapply closed_Qual_monotone; eauto. lia.
  - eapply s_trans. eapply IHHS1; eauto. eapply IHHS2; eauto.
Qed.


Lemma not_free_subst1_ty_iff : forall {v Tx dx T l}, closed_ty 0 0 l Tx -> closed_Qual 0 0 l dx ↑ -> not_free v T <-> not_free v ({0 |-> Tx ~ dx }ᵀ T).
  intros. unfold not_free. intuition.
  - replace (∅) with ({0 |-> dx }ᵈ ∅); auto. replace (TUnit) with ({0 |-> Tx ~ dx }ᵀ TUnit); auto.
    erewrite <- subst1_open_ty_comm; eauto. rewrite H1. auto.
  - replace (∅) with ({0 |-> dx }ᵈ ∅) in H1; auto. replace (TUnit) with ({0 |-> Tx ~ dx }ᵀ TUnit) in H1; auto.
    erewrite <- subst1_open_ty_comm in H1; eauto.
    generalize dependent v. induction T; intros; simpl; intuition;
    simpl in H1; inversion H1; f_equal; intuition; try solve [eapply un_subst1_qual_open; eauto].
    destruct v; auto.
    destruct (v0 =? i) eqn:Heqvi; intuition.
Qed.

Lemma q_trans''_subst1_tenv_subq' : forall Γ0 Σ bd Tx dx' dx df bx,
  wf_senv Σ ->
  wf_tenv (Γ0 ++ [(bd, bx, Tx, dx)]) Σ ->
  closed_Qual 0 0 (‖ Σ ‖) dx' ↑ ->
  Substq (Γ0 ++ [(bd, bx, Tx, dx)]) Σ dx dx' ->
  (q_trans'' ({0 |-> Tx ~ dx' }ᴳ Γ0) ({0 |-> dx' }ᵈ df) (‖ Γ0 ‖)) ⊑↑
  ({0 |-> dx' }ᵈ (q_trans'' (Γ0 ++ [(bd, bx, Tx, dx)]) df (S (‖ Γ0 ‖)))).
  intros. inversion H2; subst.
  - erewrite <- q_trans''_subst1_tenv_comm; eauto. apply subst_qual_subqual_monotone. apply q_trans''_incr_subq.
  - eapply @Subq_trans with (d2:=
    ({0 |-> dx' }ᵈ (q_trans'' (Γ0 ++ [(bd, bx, Tx, q_trans_tenv (Γ0 ++ [(bd, bx, Tx, dx)]) df0 ⋒ dx')]) df (S (‖ Γ0 ‖))))); eauto.
    eapply q_trans''_subst1_tenv_subq''; eauto. eapply wf_tenv_weaken'; eauto.
    apply subst_qual_subqual_monotone. apply q_trans_tenv_narrowing_subq; auto. apply Subq_qor; auto. apply Subq_qand_split; auto. unfold q_trans_tenv. apply q_trans''_subq'.
Qed.

Lemma has_type_vtp': forall {Σ ϰ φ t T d},
  closed_Qual 0 0 (‖Σ‖) ϰ↑ ->
  value t ->
  has_type [] φ Σ t T d ->
  kill_sep ϰ φ ->
  vtp Σ ϰ d t T d.
Proof.
  intros Σ ϰ φ t T d Hclϰ HV Ht HWFK. remember [] as Γ. induction Ht; eauto; subst; try inversion HV; subst; intuition;
    try solve [simpl in H1; discriminate].
  - (* ttabs *) subst. apply has_type_closed in Ht as Hcl. intuition.
    inversion H0. subst.  eapply vtp_tabs. 4: eauto. all: auto.
    + eapply stp_refl; auto.
    + apply qstp_refl; auto. eapply closed_Qual_sub. 2: eauto. auto.
    + apply stp_refl; intuition.
    + eapply kill_sep_sub; eauto.
  - apply vtp_base; auto. apply kill_sep_empty.
  - (* tabs *) subst.  subst. apply has_type_closed in Ht as Hcl. intuition.
    inversion H0. subst.  eapply vtp_abs. 5: eauto. all: auto.   eapply closed_Qual_sub. 2: eauto. auto.
    + eapply stp_refl; auto.
    + apply qstp_refl; auto. eapply closed_Qual_sub. 2: eauto. auto.
    + apply stp_refl; auto.
    + eapply kill_sep_sub; eauto.
  - (* tloc *) intros.  eapply vtp_loc. 6: eauto. 1-4: eauto. 4,6,7: apply qstp_refl; eauto. 4,5: eauto. 4:{ apply Q_lift_closed. eauto. }
    + Qcrush.
    + apply stp_refl; auto.
    + apply stp_refl; auto.
    + eapply kill_sep_sub; eauto.
  - intuition. eapply vtp_widening; eauto. eapply kill_sep_sub_fresh; eauto. apply stp_qstp_inv in H as H'. apply qstp_empty in H'. eapply vtp_weaken_flt; eauto. apply stp_closed in H; intuition.
  - intuition. eapply vtp_widening; eauto. eapply kill_sep_sub_fresh; eauto. apply stp_qstp_inv in H as H'. apply qstp_empty in H'. eapply vtp_weaken_flt; eauto. apply stp_closed in H; intuition.
  - intuition. eapply vtp_widening; auto. eapply kill_sep_sub_fresh; eauto. apply stp_qstp_inv in H as H'. apply qstp_empty in H'. eapply vtp_weaken_flt; eauto. apply stp_closed in H; intuition. auto.
  - intuition. eapply vtp_widening; auto. eapply kill_sep_sub_fresh; eauto. apply stp_qstp_inv in H as H'. apply qstp_empty in H'. eapply vtp_weaken_flt; eauto. apply stp_closed in H; intuition. auto.
Qed.

Lemma qdiff_substitution : forall dx q t b f l,
  kill_sep (local_locs t) dx ->
  closed_tm b f l t ->
  qdiff ({0 |-> dx }ᵈ q) (local_locs (t)) = {0 |-> dx }ᵈ (qdiff q (local_locs t)).
Proof.
  intros. erewrite qdiff_subst1_dist. f_equal. erewrite subst1_qual_id; eauto. 1-2: eapply local_locs_closed; eauto.
  eapply local_locs_kill_sep_empty; eauto.
Qed.


(* ================= Main Substitution Lemma ============== *)

Lemma substitution_gen :
  forall {t Γ φ φ' bd bx Tx dx dx' Σ ϰ T d},
  (q_trans_tenv (Γ ++ [(bd, bx,Tx,dx)]) dx') ⊓ (q_trans_tenv (Γ ++ [(bd, bx,Tx,dx)]) φ) ⊑↑ dx ->
  has_type (Γ ++ [(bd, bx,Tx,dx)]) φ Σ t T d ->
  wf_tenv (Γ ++ [(bd, bx,Tx,dx)]) Σ ->
  wf_senv Σ ->
  Substq (Γ ++ [(bd, bx,Tx,dx)]) Σ dx dx' ->
        forall {tx}, vtp Σ ϰ φ' tx Tx dx' ->
            kill_sep (local_locs t) dx' ->
            local_locs tx = ∅ ->
                        has_type ({ 0 |-> Tx ~ dx' }ᴳ Γ) ({ 0 |-> dx' }ᵈ φ) Σ
                                 ({ 0 |-> tx  }ᵗ t)
                                 ({ 0 |-> Tx ~ dx' }ᵀ T)
                                 ({ 0 |-> dx' }ᵈ d).
  intros t Γ φ φ' bd bx Tx dx dx' Σ ϰ T d Hsep HT HwfΓ HwfΣ HSubst tx HTx Hwfdx' Hwftx. specialize (vtp_closed HTx) as Hclx.
  simpl in Hclx. intuition. remember (Γ ++ [(bd, bx,Tx, dx)]) as Γ'.
  generalize dependent Γ.
  induction HT; intros; subst Γ; pose (φs := {0 |-> dx' }ᵈ φ); replace ({0 |-> dx' }ᵈ φ) with φs in *; auto.

  - (* t_tabs *) simpl. apply t_tabs; auto. eapply closed_tm_subst1'; eauto.
    inversion H3. subst. constructor; try eapply closed_ty_subst1'; eauto; eapply closed_qual_subst1'; eauto.
    eapply closed_qual_subst1'; eauto. erewrite <- subst1_fresh_id. rewrite <- subst1_qor_dist. apply subst_qual_subqual_monotone; auto. apply subst_qual_subqual_monotone; auto.
    eapply subst1_non_fresh; auto. eauto.
    eapply local_locs_substitution; eauto.
    (* 1. instantiate the IH *)
    replace (length (Γ0 ++ [(bd, bx, Tx, dx)])) with (S (‖Γ0‖)) in IHHT.
    rewrite subst1_env_length. rewrite app_comm_cons in IHHT. rewrite app_comm_cons in IHHT.
    remember (df ⊔ $!(S (‖Γ0‖)) ⊔ $!(S (S (‖Γ0‖))) ⊔ {♦}) as DF.
    replace ({0 |-> dx' }ᵈ df ⊔ $!(‖Γ0‖) ⊔ $!(S (‖Γ0‖)) ⊔ {♦}) with ({0 |-> dx' }ᵈ DF).
    intuition. specialize IHHT with (Γ := (((bind_ty, false,T1, d1) :: (bind_tm, true, (TAll d1 d2 T1 T2), df) :: Γ0))).
    (* 2. reason about opening and subst, apply IH *)
    unfold open_tm' in *. unfold open_ty' in *. unfold open_ty in *.
    unfold openq' in *. unfold openq in *.
    rewrite app_length in IHHT. rewrite subst1_env_length. simpl in *.
    replace (‖Γ0‖ + 1) with (S (‖Γ0‖)) in IHHT; try lia.
    erewrite <- open_subst1_tm_comm in IHHT; eauto. erewrite <- open_subst1_tm_comm in IHHT; eauto.
    erewrite <- open_subst1_ty_comm in IHHT; eauto. erewrite <- open_subst1_ty_comm in IHHT; eauto.
    erewrite <- open_subst1_qual_comm in IHHT; eauto. erewrite <- open_subst1_qual_comm in IHHT; eauto. repeat erewrite subst1_qor_dist in IHHT. apply IHHT; auto.
    apply has_type_filter in HT as Hft.
    subst.
    inversion H3. subst. rewrite app_length in *. simpl in *. rewrite Nat.add_1_r in *.
    unfold q_trans_tenv. repeat rewrite <- q_trans''_or_dist. repeat rewrite qand_qor_dist_l. assert (Hqn: closed_qenv_qn (S (‖ Γ0 ‖)) ((bind_ty, false, T1, d1) :: (bind_tm, true, TAll d1 d2 T1 T2, df) :: Γ0 ++ [(bd, bx, Tx, dx)])). {
      unfold closed_qenv_qn. intros.
      bdestruct (x =? (S (S (‖ Γ0 ‖)))). replace x with (‖ (bind_tm, true, TAll d1 d2 T1 T2, df) :: Γ0 ++ [(bd, bx, Tx, dx)] ‖) in *. rewrite indexr_head in H9. inversion H9. subst. simpl. clear - H16. Qcrush. subst. simpl. rewrite app_length. simpl. lia.
      bdestruct (x =? (S (‖ Γ0 ‖))). replace x with (‖ Γ0 ++ [(bd, bx, Tx, dx)] ‖) in *. rewrite indexr_skip in H9; auto. rewrite indexr_head in H9. inversion H9. subst. simpl. clear - H6 H4. Qcrush. subst. simpl. rewrite app_length. simpl. lia.
      rewrite indexr_skip in H9; auto. rewrite indexr_skip in H9; auto. destruct a as [ [ [ b fr ] T' ] q']. eapply wf_tenv_prop in HwfΓ; eauto. simpl. apply indexr_var_some' in H9. rewrite app_length in *. simpl in *. rewrite Nat.add_1_r in *. eapply closed_Nats_mono; eauto. clear - HwfΓ. Qcrush. 1,2: subst; simpl; rewrite app_length; simpl; lia.
    }
    repeat apply Subq_qor_l. unfold q_trans_tenv. repeat erewrite q_trans''_extend_closed_id'. rewrite q_trans''_fuel_max. eapply @Subq_trans with (d2:=(q_trans_tenv (Γ0 ++ [(bd, bx, Tx, dx)]) dx' ⊓ q_trans_tenv (Γ0 ++ [(bd, bx, Tx, dx)]) φ)); eauto. unfold q_trans_tenv. eapply Subq_qand_split; eauto.
    rewrite q_trans''_fuel_max. apply q_trans''_subq; auto. 1,2: simpl; lia.
    eapply closed_qenv_qn_monotone; eauto.
    1-3: simpl; rewrite app_length; simpl; rewrite Nat.add_1_r.
    clear - H4 H6. Qcrush.
    eapply closed_qenv_qn_shrink in Hqn; eauto.
    clear - H4 H6. Qcrush.
    eapply closed_qenv_qn_shrink in Hqn; eauto.
    eapply closed_Nats_mono with (n:=0). clear - H2. Qcrush. lia.
    eapply closed_qenv_qn_shrink in Hqn; eauto. simpl. eapply closed_qenv_qn_monotone; eauto. rewrite app_length. lia.
    eapply closed_Nats_mono with (n:=0). clear - H2. Qcrush. lia.
    erewrite q_trans''_extend_closed_id' with (q:=$! (S (‖ Γ0 ‖))). replace (S (‖ Γ0 ‖)) with (‖ Γ0 ++ [(bd, bx, Tx, dx)] ‖). remember (Γ0 ++ [(bd, bx, Tx, dx)]) as l. pose proof q_trans_tenv_fv as Hfv. unfold q_trans_tenv in Hfv. erewrite q_trans''_fuel_max with (E:=((bind_tm, true, TAll d1 d2 T1 T2, df) :: l)); auto. rewrite Hfv. rewrite qand_qor_dist_l. erewrite qglb_disjoint_freshv; eauto. rewrite qor_empty_right. repeat erewrite q_trans''_extend_closed_id'. erewrite q_trans''_fuel_max with (E:=(l)); simpl; auto. subst l. eapply @Subq_trans with (d2:=(q_trans_tenv (Γ0 ++ [(bd, bx, Tx, dx)]) dx' ⊓ q_trans_tenv (Γ0 ++ [(bd, bx, Tx, dx)]) φ)); eauto. apply Subq_qand_split; unfold q_trans_tenv; eapply q_trans''_subq; eauto.
    eapply closed_qenv_qn_shrink in Hqn; eauto.
    eapply closed_Nats_mono with (n:=0). clear - H2. Qcrush. lia.
    eapply closed_qenv_qn_shrink in Hqn; eauto.
    simpl. eapply closed_qenv_qn_monotone; eauto.
    subst. rewrite app_length. simpl. lia.
    eapply closed_Nats_mono with (n:=0). clear - H2. Qcrush. lia.
    rewrite q_trans''_closed_id; eauto 3. clear - H2. Qcrush.
    simpl; rewrite app_length; simpl; lia.
    1,2: simpl; rewrite app_length; simpl; rewrite Nat.add_1_r.
    eapply closed_qenv_qn_shrink in Hqn; eauto.
    clear. Qcrush.
    replace (S (S (‖ Γ0 ‖))) with (‖ (bind_tm, true, TAll d1 d2 T1 T2, df) :: Γ0 ++ [(bd, bx, Tx, dx)] ‖). pose proof q_trans_tenv_fv as Hfv. unfold q_trans_tenv in Hfv. rewrite Hfv. rewrite qand_qor_dist_l. erewrite qglb_disjoint_freshv; eauto. rewrite qor_empty_right. rewrite q_trans''_extend_closed_id'. eapply @Subq_trans with (d2:=(q_trans_tenv (Γ0 ++ [(bd, bx, Tx, dx)]) dx' ⊓ q_trans_tenv (Γ0 ++ [(bd, bx, Tx, dx)]) (φ ⊔ {♦}))); eauto. apply Subq_qand_split; auto.
    rewrite q_trans''_extend_closed_id'; eauto. rewrite q_trans''_fuel_max; eauto.
    eapply closed_qenv_qn_shrink in Hqn; eauto.
    eapply closed_Nats_mono with (n:=0). clear - H2. Qcrush. lia.
    rewrite q_trans''_extend_closed_id'. rewrite q_trans''_fuel_max; eauto. apply q_trans''_subq. eapply Subq_trans; eauto.
    eapply closed_qenv_qn_shrink in Hqn; eauto.
    simpl; rewrite app_length; simpl; rewrite Nat.add_1_r. clear - H16. Qcrush.
    eapply closed_qenv_qn_shrink in Hqn; eauto.
    unfold q_trans_tenv. rewrite <- q_trans''_or_dist. erewrite q_trans''_tenv_freshv_id; eauto. rewrite qand_qor_dist_l. rewrite qand_diamond_r_non_fresh. rewrite qor_empty_right; auto.
    unfold q_trans_tenv. rewrite q_trans''_closed_id; eauto. clear - H2. Qcrush.
    eapply closed_qenv_qn_shrink in Hqn; eauto.
    simpl. eapply closed_qenv_qn_monotone; eauto.
    rewrite app_length. simpl. lia.
    eapply closed_Nats_mono with (n:=0). clear - H2. Qcrush. lia.
    rewrite q_trans''_closed_id; eauto 3. clear - H2. Qcrush.
    simpl. rewrite app_length. simpl. lia.
    inversion H3. subst. constructor. constructor; auto. eapply closed_Qual_monotone; eauto. eapply closed_ty_monotone; eauto. eapply closed_Qual_monotone; eauto.
    apply Substq_weaken. simpl; rewrite app_length; simpl. eapply closed_Qual_monotone; eauto. lia. eapply wf_tenv_closed_qenv_qn. econstructor; eauto.
    apply Substq_weaken; eauto. simpl; rewrite app_length; simpl. eapply closed_Qual_monotone; eauto. lia.
    rewrite local_locs_open'; auto. rewrite local_locs_open'; auto.
    subst DF. repeat rewrite subst1_qor_dist.
    erewrite <- @subst1_just_fv with (x:=(‖ Γ0 ‖)). erewrite <- @subst1_just_fv with (x:=(S (‖ Γ0 ‖))). rewrite subst1_fresh_id. auto. rewrite app_length. simpl. lia.

  - (* t_tapp *) intuition. rename H8 into IHHT. simpl.
    replace ({ 0 |-> dx' }ᵈ (openq df d1 d2)) with
               (openq ({ 0 |-> dx' }ᵈ df) ({ 0 |-> dx' }ᵈ d1) ({ 0 |-> dx' }ᵈ d2)).
    replace ({0 |-> Tx ~ dx' }ᵀ (T2 <~ᵀ TUnit ~ ∅; T1 ~ d1)) with
               (({0 |-> Tx ~ dx' }ᵀ T2) <~ᵀ TUnit ~ ∅; ({0 |-> Tx ~ dx' }ᵀ T1) ~ ({0 |-> dx' }ᵈ d1)).
    apply t_tapp with (T1:= { 0 |-> Tx ~ dx' }ᵀ T1) (df:=({0 |-> dx' }ᵈ df)).
    replace (TAll ({0 |-> dx' }ᵈ d1) ({0 |-> dx' }ᵈ d2) ({0 |-> Tx ~ dx' }ᵀ T1) ({0 |-> Tx ~ dx' }ᵀ T2))
            with ({ 0 |-> Tx ~ dx' }ᵀ (TAll d1 d2 T1 T2)); auto.
    * eapply closed_ty_subst1; eauto; eapply closed_ty_monotone; eauto. rewrite subst1_env_length,app_length. simpl. lia.
    * eapply closed_qual_subst1; eauto; eapply closed_Qual_monotone; eauto. rewrite subst1_env_length,app_length. simpl. lia.
    * replace (∅) with ({0 |-> dx' }ᵈ ∅) by auto; unfold openq. repeat erewrite <- subst1_open_qual_comm; eauto. erewrite <- subst1_fresh_id. subst φs. rewrite <- subst1_qor_dist. apply subst_qual_subqual_monotone; auto.
    * apply subst1_non_fresh; eauto.
    * apply subst_qual_subqual_monotone. auto.
    * erewrite <- not_free_subst1_ty_iff; eauto.
    * eapply local_locs_substitution; eauto. apply has_type_closed in HT; intuition; eauto.
    * eapply local_locs_substitution; eauto. apply has_type_closed in HT; intuition; eauto.
    * replace (∅) with ({0 |-> dx' }ᵈ ∅) at 1; auto. unfold open_ty. repeat erewrite subst1_open_ty_comm; eauto.
    * replace (∅) with ({0 |-> dx' }ᵈ ∅) by auto; unfold openq. repeat erewrite <- subst1_open_qual_comm; eauto.

  - (* t_tapp_fresh *) intuition. rename H12 into IHHT. simpl.
    replace ({ 0 |-> dx' }ᵈ (openq df d1 d2)) with
               (openq ({ 0 |-> dx' }ᵈ df) ({ 0 |-> dx' }ᵈ d1) ({ 0 |-> dx' }ᵈ d2)).
    replace ({0 |-> Tx ~ dx' }ᵀ (T2 <~ᵀ TUnit ~ ∅; T1 ~ d1)) with
               (({0 |-> Tx ~ dx' }ᵀ T2) <~ᵀ TUnit ~ ∅; ({0 |-> Tx ~ dx' }ᵀ T1) ~ ({0 |-> dx' }ᵈ d1)).
    (*separation/overap is preserved after substitution*)
    assert (Hoverlap: {0 |-> dx' }ᵈ (q_trans_tenv (Γ0 ++ [(bd, bx, Tx, dx)]) df ⊓ q_trans_tenv (Γ0 ++ [(bd, bx, Tx, dx)]) d1) = ({0 |-> dx' }ᵈ (q_trans_tenv (Γ0 ++ [(bd, bx, Tx, dx)]) df) ⊓ {0 |-> dx' }ᵈ (q_trans_tenv (Γ0 ++ [(bd, bx, Tx, dx)]) d1))). {
      erewrite @subst1_qand_saturated' with (dx:=dx) (φ:=q_trans_tenv (Γ0 ++ [(bd, bx, Tx, dx)]) φ). auto.
      eapply @Subq_trans with (d2:=q_trans_tenv (Γ0 ++ [(bd, bx, Tx, dx)]) dx' ⊓ q_trans_tenv (Γ0 ++ [(bd, bx, Tx, dx)]) φ ); eauto. apply Subq_qand_split; eauto. unfold q_trans_tenv; eapply q_trans''_subq'.
      eauto. eauto.
      1,2: eapply q_trans_tenv_subq_fresh; eauto. eapply has_type_filter; eauto.
      1,2: unfold q_trans_tenv; eapply q_trans''_tenv_saturated; eauto.
    }
    eapply t_tapp_fresh with (T1:= { 0 |-> Tx ~ dx' }ᵀ T1) (df:=({0 |-> dx' }ᵈ df)) (d1:=({0 |-> dx' }ᵈ d1)); eauto.
    apply t_sub with (T1:=({0 |-> Tx ~ dx' }ᵀ (TAll (q_trans_tenv (Γ0 ++ [(bd, bx, Tx, dx)]) df ⋒ q_trans_tenv (Γ0 ++ [(bd, bx, Tx, dx)]) d1) d2 T1 T2))) (d1:=({0 |-> dx' }ᵈ df)). apply IHHT; auto.
    simpl. rewrite subst1_qor_dist. rewrite Hoverlap. rewrite subst1_fresh_id. auto. unfold q_trans_tenv.
    apply has_type_closed in HT as Hcl. intuition. inversion H13. subst. rewrite subst1_env_length,app_length in *. simpl in *. try rewrite Nat.add_1_r in *. constructor; repeat rewrite subst1_env_length.
    + constructor. apply closed_Qual_qor; auto. apply closed_Qual_qand.
      eapply closed_qual_subst1; eauto. apply closed_Qual_q_trans''_monotone; eauto. apply wf_tenv_closed_qenv in HwfΓ. eapply closed_qenv_monotone; eauto. rewrite app_length. simpl. lia.
      eapply closed_qual_subst1; eauto. apply closed_Qual_q_trans''_monotone; eauto. apply wf_tenv_closed_qenv in HwfΓ. eapply closed_qenv_monotone; eauto. rewrite app_length. simpl. lia.
      eapply closed_qual_subst1; eauto.
      eapply closed_ty_subst1; eauto.
      eapply closed_ty_subst1; eauto.
    + constructor. apply closed_Qual_qor; auto. apply closed_Qual_qand.
      apply closed_Qual_q_trans''_monotone. eapply closed_qual_subst1; eauto. apply wf_tenv_closed_qenv in HwfΓ. eapply closed_qenv_subst1; eauto. rewrite app_length in HwfΓ. simpl in HwfΓ. rewrite Nat.add_1_r in HwfΓ. eapply closed_qenv_shrink'; eauto. eapply closed_Qual_monotone; eauto. lia.
      apply closed_Qual_q_trans''_monotone. eapply closed_qual_subst1; eauto. apply wf_tenv_closed_qenv in HwfΓ. eapply closed_qenv_subst1; eauto. rewrite app_length in HwfΓ. simpl in HwfΓ. rewrite Nat.add_1_r in HwfΓ. eapply closed_qenv_shrink'; eauto. eapply closed_Qual_monotone; eauto. lia.
      eapply closed_qual_subst1; eauto.
      eapply closed_ty_subst1; eauto.
      eapply closed_ty_subst1; eauto.
    + constructor; auto. eapply closed_qual_subst1; eauto. eapply closed_Qual_monotone; eauto. rewrite subst1_env_length. lia.
    + eapply stp_refl'; eauto 3. eapply closed_ty_subst1; eauto. eapply closed_ty_monotone; eauto. rewrite subst1_env_length. lia. constructor.
      apply Subq_qor. apply Subq_qand_split; eauto.
      1,2: eapply q_trans''_subst1_tenv_subq'; eauto.
      rewrite subst1_env_length. apply closed_Qual_qor; auto. apply closed_Qual_qand.
      eapply closed_qual_subst1; eauto 3. eapply closed_Qual_q_trans''_monotone; eauto. replace (S (‖ Γ0 ‖)) with (‖ Γ0 ++ [(bd, bx, Tx, dx)] ‖). apply wf_tenv_closed_qenv; auto. rewrite app_length. simpl. lia.
      eapply closed_qual_subst1; eauto 3. eapply closed_Qual_q_trans''_monotone; eauto. replace (S (‖ Γ0 ‖)) with (‖ Γ0 ++ [(bd, bx, Tx, dx)] ‖). apply wf_tenv_closed_qenv; auto. rewrite app_length. simpl. lia.
    + apply stp_refl. simpl. rewrite subst1_env_length. apply closed_ty_open2; try rewrite subst1_env_length; auto. eapply closed_ty_subst1; eauto. eapply closed_ty_monotone; eauto. 1,2: clear; apply Q_lift_closed; Qcrush. apply qstp_refl. simpl. apply closed_Qual_open2; try rewrite subst1_env_length. eapply closed_qual_subst1; eauto. eapply closed_Qual_monotone; eauto. 1,2: clear; Qcrush.
    + apply has_type_filter in HT. subst φs. erewrite <- subst1_fresh_id. rewrite <- subst1_qor_dist. apply subst_qual_subqual_monotone; auto.
    + eapply local_locs_substitution; eauto. apply has_type_closed in HT; intuition; eauto. apply has_type_local_loc_sep in HT; auto.
    + rewrite subst1_env_length. eapply closed_ty_subst1; eauto. eapply closed_ty_monotone; eauto. rewrite app_length. simpl. lia.
    + eapply closed_qual_subst1; eauto. eapply closed_Qual_monotone; eauto. rewrite app_length. simpl. rewrite subst1_env_length. lia.
    + apply has_type_filter in HT. subst φs. erewrite <- subst1_fresh_id. rewrite <- subst1_qor_dist. apply subst_qual_subqual_monotone; auto.
    + erewrite <- not_free_subst1_ty_iff; eauto; apply Substq_non_fresh in HSubst.
    + erewrite <- not_free_subst1_ty_iff; eauto; apply Substq_non_fresh in HSubst.
    + unfold openq; replace (∅) with ({0 |-> dx' }ᵈ ∅) by solve [apply subst1_qual_empty]; repeat erewrite <- subst1_open_qual_comm; eauto. subst φs. erewrite <- subst1_fresh_id. rewrite <- subst1_qor_dist. apply subst_qual_subqual_monotone; auto.
    + apply Subq_qor_l; eauto.
      eapply @Subq_trans with (d2:={0 |-> dx'}ᵈ (q_trans_tenv (Γ0 ++ [(bd, bx, Tx, dx)]) df ⊓ q_trans_tenv (Γ0 ++ [(bd, bx, Tx, dx)]) d1)); eauto. rewrite qand_commute. rewrite Hoverlap. unfold q_trans_tenv. rewrite app_length, subst1_env_length. simpl. rewrite Nat.add_1_r. apply Subq_qand_split; eapply q_trans''_subst1_tenv_subq'; eauto.
        erewrite <- subst1_fresh_id. subst φs. rewrite <- subst1_qor_dist. apply subst_qual_subqual_monotone. Qcrush.
    + eapply local_locs_substitution; eauto. apply has_type_closed in HT; intuition; eauto.
    + eapply local_locs_substitution; eauto. apply has_type_closed in HT; intuition; eauto.
    + eapply kill_sep_sub. 2: eapply local_locs_substitution. 5: eapply H11. 2,4: eauto. 2: apply has_type_closed in HT; intuition; eauto.
      eapply @Subq_trans with (d2:={0 |-> dx'}ᵈ (q_trans_tenv (Γ0 ++ [(bd, bx, Tx, dx)]) df ⊓ q_trans_tenv (Γ0 ++ [(bd, bx, Tx, dx)]) d1) ⊔ {♦}); eauto. apply Subq_qor.
      rewrite qand_commute. rewrite Hoverlap. unfold q_trans_tenv. rewrite app_length, subst1_env_length. simpl. rewrite Nat.add_1_r. apply Subq_qand_split; eapply q_trans''_subst1_tenv_subq'; eauto.
      rewrite subst1_qor_dist. replace ({0 |-> dx' }ᵈ {♦}) with ({♦}). apply Subq_qor. rewrite qand_commute. clear; Qcrush. symmetry. rewrite subst1_fresh_id; auto.
    + replace (∅) with ({0 |-> dx' }ᵈ ∅) at 1; auto. unfold open_ty. repeat erewrite subst1_open_ty_comm; eauto.
    + unfold openq. repeat erewrite <- subst1_open_qual_comm; eauto.
  - (* t_base *) subst. simpl. replace ({0 |-> dx' }ᵈ ∅) with (∅) by solve [symmetry; apply subst1_qual_empty].
    apply t_base; auto. eapply closed_qual_subst1'; eauto.
  - (* t_var *) subst. simpl. (bdestruct (x =? 0)).
    * (*x is 0 *) rewrite indexr_skips in H0; simpl; auto; try lia. simpl in H0. subst. simpl in H0.
      qual_destruct dx'.
      inversion H0. subst. erewrite subst1_ty_id; eauto. inversion HSubst; subst.
      + (*subst fun, dx = dx' *)
        apply vtp_has_type in HTx.
        eapply weaken'; eauto. subst φs. eapply subst_filter0; eauto.
        eapply wf_tenv_subst; eauto.
        subst φs. (* tx φ, tx dx', and subst preserve *)
        eapply closed_qual_subst1'; eauto.
      + (*subst arg, dx = df ⋒ dx = dx' ⋒ φ *)
        apply vtp_has_type in HTx.
        eapply weaken'; eauto.
        eapply @subst_qual_subqual_monotone with (df:=(fr, fvs, bvs, lcs)) in H3.
        subst φs. erewrite subst1_just_fv0 in H3. auto.
        eapply wf_tenv_subst; eauto. eapply wf_tenv_closed_subst; eauto.
        eapply closed_qual_subst1'; eauto.
    * (*x is in Γ0*) assert (Hx: 1 <= x); try lia. destruct x; try lia.
      apply t_var with (b:=b) (d:={0 |-> dx' }ᵈ d). change x with (pred (S x)).
      eapply indexr_subst1; eauto. erewrite subst1_just_fv.
      repeat eapply subst_qual_subqual_monotone. auto.
      eapply closed_qual_subst1'; eauto. simpl. eapply closed_ty_subst1; eauto.
      simpl. eapply closed_qual_subst1; eauto.

  - (* t_abs *) simpl. apply t_abs; auto. eapply closed_tm_subst1'; eauto.
    inversion H3. subst. constructor; try eapply closed_ty_subst1'; eauto; eapply closed_qual_subst1'; eauto.
    eapply closed_qual_subst1'; eauto. apply subst_qual_subqual_monotone_fresh; auto. apply subst_qual_subqual_monotone; auto. eauto.
    eapply local_locs_substitution; eauto.
    (* 1. instantiate the IH *)
    replace (length (Γ0 ++ [(bd, bx, Tx, dx)])) with (S (‖Γ0‖)) in IHHT.
    rewrite subst1_env_length. rewrite app_comm_cons in IHHT. rewrite app_comm_cons in IHHT.
    remember (df ⊔ $!(S (‖Γ0‖)) ⊔ $!(S (S (‖Γ0‖))) ⊔ {♦}) as DF.
    replace ({0 |-> dx' }ᵈ df ⊔ $!(‖Γ0‖) ⊔ $!(S (‖Γ0‖)) ⊔ {♦}) with ({0 |-> dx' }ᵈ DF).
    intuition. specialize IHHT with (Γ := (((bind_tm, false,T1, d1) :: (bind_tm, true, (TFun d1 d2 T1 T2), df) :: Γ0))).
    (* 2. reason about opening and subst, apply IH *)
    unfold open_tm' in *. unfold open_ty' in *. unfold open_ty in *.
    unfold openq' in *. unfold openq in *.
    rewrite app_length in IHHT. rewrite subst1_env_length. simpl in *.
    replace (‖Γ0‖ + 1) with (S (‖Γ0‖)) in IHHT; try lia.
    erewrite <- open_subst1_tm_comm in IHHT; eauto. erewrite <- open_subst1_tm_comm in IHHT; eauto.
    erewrite <- open_subst1_ty_comm in IHHT; eauto. erewrite <- open_subst1_ty_comm in IHHT; eauto.
    erewrite <- open_subst1_qual_comm in IHHT; eauto. erewrite <- open_subst1_qual_comm in IHHT; eauto. repeat erewrite subst1_qor_dist in IHHT. apply IHHT; auto.
    apply has_type_filter in HT as Hft.
    subst.
    inversion H3. subst. rewrite app_length in *. simpl in *. rewrite Nat.add_1_r in *.
    unfold q_trans_tenv. repeat rewrite <- q_trans''_or_dist. repeat rewrite qand_qor_dist_l. assert (Hqn: closed_qenv_qn (S (‖ Γ0 ‖)) ((bind_tm, false, T1, d1) :: (bind_tm, true, TFun d1 d2 T1 T2, df) :: Γ0 ++ [(bd, bx, Tx, dx)])). {
      unfold closed_qenv_qn. intros.
      bdestruct (x =? (S (S (‖ Γ0 ‖)))). replace x with (‖ (bind_tm, true, TFun d1 d2 T1 T2, df) :: Γ0 ++ [(bd, bx, Tx, dx)] ‖) in *. rewrite indexr_head in H9. inversion H9. subst. simpl. clear - H16. Qcrush. subst. simpl. rewrite app_length. simpl. lia.
      bdestruct (x =? (S (‖ Γ0 ‖))). replace x with (‖ Γ0 ++ [(bd, bx, Tx, dx)] ‖) in *. rewrite indexr_skip in H9; auto. rewrite indexr_head in H9. inversion H9. subst. simpl. clear - H6 H4. Qcrush. subst. simpl. rewrite app_length. simpl. lia.
      rewrite indexr_skip in H9; auto. rewrite indexr_skip in H9; auto. destruct a as [ [ [ b fr ] T' ] q']. eapply wf_tenv_prop in HwfΓ; eauto. simpl. apply indexr_var_some' in H9. rewrite app_length in *. simpl in *. rewrite Nat.add_1_r in *. eapply closed_Nats_mono; eauto. clear - HwfΓ. Qcrush. 1,2: subst; simpl; rewrite app_length; simpl; lia.
    }
    repeat apply Subq_qor_l. unfold q_trans_tenv. repeat erewrite q_trans''_extend_closed_id'. rewrite q_trans''_fuel_max. eapply @Subq_trans with (d2:=(q_trans_tenv (Γ0 ++ [(bd, bx, Tx, dx)]) dx' ⊓ q_trans_tenv (Γ0 ++ [(bd, bx, Tx, dx)]) φ)); eauto. unfold q_trans_tenv. eapply Subq_qand_split; eauto.
    rewrite q_trans''_fuel_max. apply q_trans''_subq; auto. 1,2: simpl; lia.
    eapply closed_qenv_qn_monotone; eauto.
    1-3: simpl; rewrite app_length; simpl; rewrite Nat.add_1_r.
    clear - H4 H6. Qcrush.
    eapply closed_qenv_qn_shrink in Hqn; eauto.
    clear - H4 H6. Qcrush.
    eapply closed_qenv_qn_shrink in Hqn; eauto.
    eapply closed_Nats_mono with (n:=0). clear - H2. Qcrush. lia.
    eapply closed_qenv_qn_shrink in Hqn; eauto. simpl. eapply closed_qenv_qn_monotone; eauto. rewrite app_length. lia.
    eapply closed_Nats_mono with (n:=0). clear - H2. Qcrush. lia.
    erewrite q_trans''_extend_closed_id' with (q:=$! (S (‖ Γ0 ‖))). replace (S (‖ Γ0 ‖)) with (‖ Γ0 ++ [(bd, bx, Tx, dx)] ‖). remember (Γ0 ++ [(bd, bx, Tx, dx)]) as l. pose proof q_trans_tenv_fv as Hfv. unfold q_trans_tenv in Hfv. erewrite q_trans''_fuel_max with (E:=((bind_tm, true, TFun d1 d2 T1 T2, df) :: l)); auto. rewrite Hfv. rewrite qand_qor_dist_l. erewrite qglb_disjoint_freshv; eauto. rewrite qor_empty_right. repeat erewrite q_trans''_extend_closed_id'. erewrite q_trans''_fuel_max with (E:=(l)); simpl; auto. subst l. eapply @Subq_trans with (d2:=(q_trans_tenv (Γ0 ++ [(bd, bx, Tx, dx)]) dx' ⊓ q_trans_tenv (Γ0 ++ [(bd, bx, Tx, dx)]) φ)); eauto. apply Subq_qand_split; unfold q_trans_tenv; eapply q_trans''_subq; eauto.
    eapply closed_qenv_qn_shrink in Hqn; eauto.
    eapply closed_Nats_mono with (n:=0). clear - H2. Qcrush. lia.
    eapply closed_qenv_qn_shrink in Hqn; eauto.
    simpl. eapply closed_qenv_qn_monotone; eauto.
    subst. rewrite app_length. simpl. lia.
    eapply closed_Nats_mono with (n:=0). clear - H2. Qcrush. lia.
    rewrite q_trans''_closed_id; eauto 3. clear - H2. Qcrush.
    simpl; rewrite app_length; simpl; lia.
    1,2: simpl; rewrite app_length; simpl; rewrite Nat.add_1_r.
    eapply closed_qenv_qn_shrink in Hqn; eauto.
    clear. Qcrush.
    replace (S (S (‖ Γ0 ‖))) with (‖ (bind_tm, true, TFun d1 d2 T1 T2, df) :: Γ0 ++ [(bd, bx, Tx, dx)] ‖). pose proof q_trans_tenv_fv as Hfv. unfold q_trans_tenv in Hfv. rewrite Hfv. rewrite qand_qor_dist_l. erewrite qglb_disjoint_freshv; eauto. rewrite qor_empty_right. rewrite q_trans''_extend_closed_id'. eapply @Subq_trans with (d2:=(q_trans_tenv (Γ0 ++ [(bd, bx, Tx, dx)]) dx' ⊓ q_trans_tenv (Γ0 ++ [(bd, bx, Tx, dx)]) (φ ⊔ {♦}))); eauto. apply Subq_qand_split; auto.
    rewrite q_trans''_extend_closed_id'; eauto. rewrite q_trans''_fuel_max; eauto.
    eapply closed_qenv_qn_shrink in Hqn; eauto.
    eapply closed_Nats_mono with (n:=0). clear - H2. Qcrush. lia.
    rewrite q_trans''_extend_closed_id'. rewrite q_trans''_fuel_max; eauto. apply q_trans''_subq. eapply Subq_trans; eauto.
    eapply closed_qenv_qn_shrink in Hqn; eauto.
    simpl; rewrite app_length; simpl; rewrite Nat.add_1_r. clear - H16. Qcrush.
    eapply closed_qenv_qn_shrink in Hqn; eauto.
    unfold q_trans_tenv. rewrite <- q_trans''_or_dist. erewrite q_trans''_tenv_freshv_id; eauto. rewrite qand_qor_dist_l. rewrite qand_diamond_r_non_fresh. rewrite qor_empty_right; auto.
    unfold q_trans_tenv. rewrite q_trans''_closed_id; eauto. clear - H2. Qcrush.
    eapply closed_qenv_qn_shrink in Hqn; eauto.
    simpl. eapply closed_qenv_qn_monotone; eauto.
    rewrite app_length. simpl. lia.
    eapply closed_Nats_mono with (n:=0). clear - H2. Qcrush. lia.
    rewrite q_trans''_closed_id; eauto 3. clear - H2. Qcrush.
    simpl. rewrite app_length. simpl. lia.
    inversion H3. subst. constructor. constructor; auto. eapply closed_Qual_monotone; eauto. eapply closed_ty_monotone; eauto. eapply closed_Qual_monotone; eauto.
    apply Substq_weaken. simpl; rewrite app_length; simpl. eapply closed_Qual_monotone; eauto. lia. eapply wf_tenv_closed_qenv_qn. econstructor; eauto.
    apply Substq_weaken; eauto. simpl; rewrite app_length; simpl. eapply closed_Qual_monotone; eauto. lia.
    rewrite local_locs_open'; auto. rewrite local_locs_open'; auto.
    subst DF. repeat rewrite subst1_qor_dist.
    erewrite <- @subst1_just_fv with (x:=(‖ Γ0 ‖)). erewrite <- @subst1_just_fv with (x:=(S (‖ Γ0 ‖))). rewrite subst1_fresh_id. auto. rewrite app_length. simpl. lia.

  - (* t_app *) intuition. rename H8 into IHHT1. simpl. simpl in Hwfdx'. apply kill_sep_kill_qor_rev in Hwfdx'; destruct Hwfdx' as [Hwfdx'1 Hwfdx'2]. apply (qdiff_local_loc_prop) in H5 as H5'; destruct H5'. auto.
    replace ({ 0 |-> dx' }ᵈ (openq df d1 d2)) with
               (openq ({ 0 |-> dx' }ᵈ df) ({ 0 |-> dx' }ᵈ d1) ({ 0 |-> dx' }ᵈ d2)).
    replace ({0 |-> Tx ~ dx' }ᵀ (T2 <~ᵀ TUnit ~ ∅; T1 ~ d1)) with
               (({0 |-> Tx ~ dx' }ᵀ T2) <~ᵀ TUnit ~ ∅; ({0 |-> Tx ~ dx' }ᵀ T1) ~ ({0 |-> dx' }ᵈ d1)).
    apply t_app with (T1:= { 0 |-> Tx ~ dx' }ᵀ T1) (df:=({0 |-> dx' }ᵈ df)) (φd:={0 |-> dx' }ᵈ φd).
    replace (TFun ({0 |-> dx' }ᵈ d1) ({0 |-> dx' }ᵈ d2) ({0  |-> Tx ~ dx' }ᵀ T1) ({0 |-> Tx ~ dx' }ᵀ T2))
            with ({ 0 |->Tx ~ dx' }ᵀ (TFun d1 d2 T1 T2)); auto.
    eapply IHHT2; eauto. { clear - Hsep H9. eapply Qand_bound_sub. eauto. auto. unfold q_trans_tenv. apply q_trans''_subq; auto. }
    unfold openq; replace (∅) with ({0 |-> dx' }ᵈ ∅) by solve [apply subst1_qual_empty];
        erewrite <- subst1_open_qual_comm; eauto; erewrite <- subst1_open_qual_comm; eauto.
    * replace (∅) with ({0 |-> dx' }ᵈ ∅) by auto; unfold openq. repeat erewrite <- subst1_open_qual_comm; eauto. erewrite <- subst1_fresh_id. subst φs. rewrite <- subst1_qor_dist. apply subst_qual_subqual_monotone; auto.
    * replace (∅) with ({0 |-> dx' }ᵈ ∅) by auto; unfold openq. repeat erewrite <- subst1_open_qual_comm; eauto.
    * erewrite <- not_free_subst1_ty_iff; eauto.
    * subst φs. subst. rewrite local_locs_subst'; auto. eapply qdiff_substitution; eauto. apply has_type_closed in HT1; intuition; eauto.
    * (* (tapp t1 t2) {vx}, so t1 is at the inner level of vx, we can require local locs of t1 is separate from local locs of vx/dx'
      goal: LC(tx) + LC(t1) sep (dx'+φd),
        premise: LC(t1) sep φd ,
        need: LC(t1) sep dx' : t1 is at inner level, so require wf premise: local loc term disjoint: and vtp can retype, so in the case here:
          tapp (tapp t1 t2) vx: vx is typed in a context φd' separate from local locs of (tapp t1 t2), which includes t1
        need: LC(tx) sep dx' : vtp should not contain any local loc
        need: LC(tx) sep φd : vtp should not contain any local loc
      *)
      eapply local_locs_substitution; eauto. apply has_type_closed in HT2; intuition; eauto.
    * apply kill_sep_kill_qor_rev in H7; destruct H7. apply kill_sep_kill_qor.
      1-2: eapply local_locs_substitution; eauto. apply has_type_closed in HT1; intuition; eauto. apply has_type_closed in HT2; intuition; eauto.
    * replace (∅) with ({0 |-> dx' }ᵈ ∅) at 1; auto. unfold open_ty. repeat erewrite subst1_open_ty_comm; eauto.
    * unfold openq. repeat erewrite <- subst1_open_qual_comm; eauto.

  - (* t_app_fresh *) intuition. rename H10 into IHHT1. simpl. simpl in Hwfdx'. apply kill_sep_kill_qor_rev in Hwfdx'; destruct Hwfdx' as [Hwfdx'1 Hwfdx'2]. auto. apply (qdiff_local_loc_prop) in H6 as H5'; destruct H5'.
    replace ({ 0 |-> dx' }ᵈ (openq df d1 d2)) with
               (openq ({ 0 |-> dx' }ᵈ df) ({ 0 |-> dx' }ᵈ d1) ({ 0 |-> dx' }ᵈ d2)).
    replace ({0 |-> Tx ~ dx' }ᵀ (T2 <~ᵀ TUnit ~ ∅; T1 ~ d1)) with
               (({0 |-> Tx ~ dx' }ᵀ T2) <~ᵀ TUnit ~ ∅; ({0 |-> Tx ~ dx' }ᵀ T1) ~ ({0 |-> dx' }ᵈ d1)).
    (*separation/overap is preserved after substitution*)
    assert (Hoverlap: {0 |-> dx' }ᵈ (q_trans_tenv (Γ0 ++ [(bd, bx, Tx, dx)]) df ⊓ q_trans_tenv (Γ0 ++ [(bd, bx, Tx, dx)]) d1) = {0 |-> dx' }ᵈ (q_trans_tenv (Γ0 ++ [(bd, bx, Tx, dx)]) df) ⊓ {0 |-> dx' }ᵈ (q_trans_tenv (Γ0 ++ [(bd, bx, Tx, dx)]) d1)). {
      erewrite @subst1_qand_saturated' with (dx:=dx) (φ:=q_trans_tenv (Γ0 ++ [(bd, bx, Tx, dx)]) φ). auto.
      eapply @Subq_trans with (d2:=q_trans_tenv (Γ0 ++ [(bd, bx, Tx, dx)]) dx' ⊓ q_trans_tenv (Γ0 ++ [(bd, bx, Tx, dx)]) φ); eauto.
      apply Subq_qand_split; auto; unfold q_trans_tenv; eapply q_trans''_subq'; eauto.
            eauto. eauto. 1,2: eapply q_trans_tenv_subq_fresh. eapply has_type_filter; eauto. apply has_type_filter in HT2. eapply Subq_trans; eauto.
      1,2: unfold q_trans_tenv; eapply q_trans''_tenv_saturated; eauto.
    }
    eapply t_app_fresh with (T1:= { 0 |-> Tx ~ dx' }ᵀ T1) (df:=({0 |-> dx' }ᵈ df)) (d1:=({0 |-> dx' }ᵈ d1)) (φd := {0 |-> dx' }ᵈ φd); eauto.
    apply t_sub with (T1:=({0 |-> Tx ~ dx' }ᵀ (TFun (q_trans_tenv (Γ0 ++ [(bd, bx, Tx, dx)]) df ⋒ q_trans_tenv (Γ0 ++ [(bd, bx, Tx, dx)]) d1) d2 T1 T2))) (d1:=({0 |-> dx' }ᵈ df)). apply IHHT1; auto.
    simpl. rewrite subst1_qor_dist. rewrite Hoverlap. rewrite subst1_fresh_id. auto. unfold q_trans_tenv.
    apply has_type_closed in HT1 as Hcl,HT2 as Hcl2. intuition. inversion H15. subst. rewrite subst1_env_length,app_length in *. simpl in *. try rewrite Nat.add_1_r in *. constructor; repeat rewrite subst1_env_length.
    + constructor. apply closed_Qual_qor; auto. apply closed_Qual_qand.
      eapply closed_qual_subst1; eauto. apply closed_Qual_q_trans''_monotone; eauto. apply wf_tenv_closed_qenv in HwfΓ. eapply closed_qenv_monotone; eauto. rewrite app_length. simpl. lia.
      eapply closed_qual_subst1; eauto. apply closed_Qual_q_trans''_monotone; eauto. apply wf_tenv_closed_qenv in HwfΓ. eapply closed_qenv_monotone; eauto. rewrite app_length. simpl. lia.
      eapply closed_qual_subst1; eauto.
      eapply closed_ty_subst1; eauto.
      eapply closed_ty_subst1; eauto.
    + constructor. apply closed_Qual_qor; auto. apply closed_Qual_qand.
      apply closed_Qual_q_trans''_monotone. eapply closed_qual_subst1; eauto. apply wf_tenv_closed_qenv in HwfΓ. eapply closed_qenv_subst1; eauto. rewrite app_length in HwfΓ. simpl in HwfΓ. rewrite Nat.add_1_r in HwfΓ. eapply closed_qenv_shrink'; eauto. eapply closed_Qual_monotone; eauto. lia.
      apply closed_Qual_q_trans''_monotone. eapply closed_qual_subst1; eauto. apply wf_tenv_closed_qenv in HwfΓ. eapply closed_qenv_subst1; eauto. rewrite app_length in HwfΓ. simpl in HwfΓ. rewrite Nat.add_1_r in HwfΓ. eapply closed_qenv_shrink'; eauto. eapply closed_Qual_monotone; eauto. lia.
      eapply closed_qual_subst1; eauto.
      eapply closed_ty_subst1; eauto.
      eapply closed_ty_subst1; eauto.
    + constructor; auto. eapply closed_qual_subst1; eauto. eapply closed_Qual_monotone; eauto. rewrite subst1_env_length. lia.
    + eapply stp_refl'; eauto 3. eapply closed_ty_subst1; eauto. eapply closed_ty_monotone; eauto. rewrite subst1_env_length. lia. constructor.
      apply Subq_qor. apply Subq_qand_split; eauto.
      1,2: eapply q_trans''_subst1_tenv_subq'; eauto.
      rewrite subst1_env_length. apply closed_Qual_qor; auto. apply closed_Qual_qand.
      eapply closed_qual_subst1; eauto 3. eapply closed_Qual_q_trans''_monotone; eauto. replace (S (‖ Γ0 ‖)) with (‖ Γ0 ++ [(bd, bx, Tx, dx)] ‖). apply wf_tenv_closed_qenv; auto. rewrite app_length. simpl. lia.
      eapply closed_qual_subst1; eauto 3. eapply closed_Qual_q_trans''_monotone; eauto. replace (S (‖ Γ0 ‖)) with (‖ Γ0 ++ [(bd, bx, Tx, dx)] ‖). apply wf_tenv_closed_qenv; auto. rewrite app_length. simpl. lia.
    + apply stp_refl. simpl. rewrite subst1_env_length. apply closed_ty_open2; try rewrite subst1_env_length; auto. eapply closed_ty_subst1; eauto. eapply closed_ty_monotone; eauto. 1,2: clear; apply Q_lift_closed; Qcrush. apply qstp_refl. simpl. apply closed_Qual_open2; try rewrite subst1_env_length. eapply closed_qual_subst1; eauto. eapply closed_Qual_monotone; eauto. 1,2: clear; Qcrush.
    + apply has_type_filter in HT1. subst φs. erewrite <- subst1_fresh_id. rewrite <- subst1_qor_dist. apply subst_qual_subqual_monotone; auto.
    + eapply local_locs_substitution; eauto. apply has_type_closed in HT1; intuition; eauto. apply has_type_local_loc_sep in HT1; auto.
  + (*has_type*) apply IHHT2; auto. clear - Hsep H11. eapply Qand_bound_sub; eauto. unfold q_trans_tenv. eapply q_trans''_subq; auto.
    + erewrite <- not_free_subst1_ty_iff; eauto; apply Substq_non_fresh in HSubst.
    + erewrite <- not_free_subst1_ty_iff; eauto; apply Substq_non_fresh in HSubst.
    + unfold openq; replace (∅) with ({0 |-> dx' }ᵈ ∅) by solve [apply subst1_qual_empty]; repeat erewrite <- subst1_open_qual_comm; eauto. subst φs. erewrite <- subst1_fresh_id. rewrite <- subst1_qor_dist. apply subst_qual_subqual_monotone; auto.
    + apply Subq_qor_l; eauto.
      eapply @Subq_trans with (d2:={0 |-> dx'}ᵈ (q_trans_tenv (Γ0 ++ [(bd, bx, Tx, dx)]) df ⊓ q_trans_tenv (Γ0 ++ [(bd, bx, Tx, dx)]) d1)); eauto. rewrite qand_commute. rewrite Hoverlap. unfold q_trans_tenv. rewrite app_length, subst1_env_length. simpl. rewrite Nat.add_1_r. apply Subq_qand_split; eapply q_trans''_subst1_tenv_subq'; eauto.
      erewrite <- subst1_fresh_id. subst φs. rewrite <- subst1_qor_dist. apply subst_qual_subqual_monotone. Qcrush. (*slow*)
    + subst φs. rewrite local_locs_subst'; auto. subst. eapply qdiff_substitution; eauto. eapply has_type_closed in HT1; intuition; eauto.
    + eapply local_locs_substitution; eauto. apply has_type_closed in HT2; intuition; eauto.
    + apply kill_sep_kill_qor_rev in H8; destruct H8. apply kill_sep_kill_qor.
      1-2: eapply local_locs_substitution; eauto. apply has_type_closed in HT1; intuition; eauto. apply has_type_closed in HT2; intuition; eauto.
    + eapply kill_sep_sub. 2: eapply local_locs_substitution. 5: eapply H9. 4: eapply Hwfdx'1. 2: eauto. 2: apply has_type_closed in HT1; intuition; eauto.
      eapply @Subq_trans with (d2:={0 |-> dx'}ᵈ (q_trans_tenv (Γ0 ++ [(bd, bx, Tx, dx)]) df ⊓ q_trans_tenv (Γ0 ++ [(bd, bx, Tx, dx)]) d1) ⊔ {♦}); eauto. apply Subq_qor.
      rewrite qand_commute. rewrite Hoverlap. unfold q_trans_tenv. rewrite app_length, subst1_env_length. simpl. rewrite Nat.add_1_r. apply Subq_qand_split; eapply q_trans''_subst1_tenv_subq'; eauto.
      rewrite subst1_qor_dist.  apply Subq_qor. rewrite qand_commute. clear; Qcrush.
    + replace (∅) with ({0 |-> dx' }ᵈ ∅) at 1; auto. unfold open_ty. repeat erewrite subst1_open_ty_comm; eauto.
    + unfold openq. repeat erewrite <- subst1_open_qual_comm; eauto.

  - (* t_loc *) erewrite @subst1_qual_id with (q:=(&!l)); eauto. simpl. erewrite subst1_ty_id; eauto.
    erewrite subst1_qual_id; eauto. apply t_loc; auto. eapply closed_qual_subst1'; eauto.
    erewrite <- @subst1_qual_id with (q:=(&!l)); eauto. eapply subst_qual_subqual_monotone; eauto.
    all : apply sindexr_var_some' in H3; eapply just_loc_closed; eauto.
  - (* t_ref *) rewrite subst1_fresh_id. simpl. apply t_ref; auto.
    eapply closed_ty_subst1'; eauto. apply subst1_non_fresh; eauto.
  - (* t_refat *) simpl. simpl in Hwfdx'. apply kill_sep_kill_qor_rev in Hwfdx'; destruct Hwfdx' as [Hwfdx'1 Hwfdx'2]. apply (qdiff_local_loc_prop) in H3 as H5'; destruct H5'.
    eapply t_refat with (φd:={ 0 |-> dx' }ᵈ φd); auto. 2: apply subst1_non_fresh; eauto.
    eapply IHHT1; eauto. eapply Qand_bound_sub; eauto. unfold q_trans_tenv; apply q_trans''_subq; auto.
    eapply IHHT2; eauto.
    subst φs. rewrite local_locs_subst'; auto. subst. eapply qdiff_substitution; eauto. apply has_type_closed in HT2; intuition; eauto.
    eapply local_locs_substitution; eauto. apply has_type_closed in HT1; intuition; eauto.
  - (* t_deref *) simpl. apply t_deref with (d := { 0 |-> dx' }ᵈ d); auto.
    apply subst1_non_fresh; eauto. apply subst_qual_subqual_monotone. auto.
    simpl in Hwfdx'. eapply local_locs_substitution; eauto. apply has_type_closed in HT; intuition; eauto.
  - (* t_assign *) rewrite subst1_qual_empty in *. simpl. simpl in IHHT1. simpl in Hwfdx'. apply kill_sep_kill_qor_rev in Hwfdx'; destruct Hwfdx' as [Hwfdx'1 Hwfdx'2]. apply (qdiff_local_loc_prop) in H3 as H5'; destruct H5'.
    apply t_assign with (T:={0 |-> Tx ~ dx' }ᵀ T) (d:=({0 |-> dx' }ᵈ d)) (d1:=({0 |-> dx' }ᵈ d1)) (φd := {0 |-> dx' }ᵈ φd); auto.
    eapply IHHT2; auto. eapply Qand_bound_sub; eauto. unfold q_trans_tenv; apply q_trans''_subq; auto.
    apply subst1_non_fresh; eauto.
    subst φs. rewrite local_locs_subst'; auto. subst. eapply qdiff_substitution; eauto. apply has_type_closed in HT1; intuition; eauto.
    eapply local_locs_substitution; eauto. apply has_type_closed in HT2; intuition; eauto.
  - (* t_sub *) apply t_sub with (T1:={ 0 |-> Tx ~ dx' }ᵀ T1) (d1:={ 0 |-> dx' }ᵈ d1).
    eapply IHHT; eauto. eapply subst_stp; eauto. erewrite <- subst1_fresh_id. subst φs. rewrite <- subst1_qor_dist. apply subst_qual_subqual_monotone; auto.
    eapply local_locs_substitution; eauto. eapply has_type_closed in HT; intuition; eauto.
  Unshelve. apply bind_tm. all : auto.
  - (* t_withr *) simpl. simpl in Hwfdx'. apply kill_sep_kill_qor_rev in Hwfdx'; destruct Hwfdx' as [Hwfdx'1 Hwfdx'2].
    eapply t_withr with (φd := { 0 |-> dx' }ᵈ φd).
    eapply IHHT1; auto. apply subst1_non_fresh; eauto.
    eauto. eapply closed_ty_subst1'; eauto.
    eapply closed_qual_subst1'; eauto. eapply closed_tm_subst1'; eauto.
    specialize (IHHT1 Hsep HwfΓ HwfΣ HSubst HTx).
    (* 1. instantiate the IH *)
    replace (length (Γ0 ++ [(bd, bx, Tx, dx)])) with (S (‖Γ0‖)) in IHHT2.
    rewrite subst1_env_length. rewrite app_comm_cons in IHHT2. rewrite app_comm_cons in IHHT2.
    intuition. specialize IHHT2 with (Γ :=  ((bind_tm, false, TRef d1 T1, {♦}) :: (bind_tm, true, TUnit, {♦}) :: Γ0)).
    (* 2. reason about opening and subst, apply IH *)
    unfold open_tm' in *.
    rewrite app_length in IHHT2. rewrite subst1_env_length. simpl in *.
    replace (‖Γ0‖ + 1) with (S (‖Γ0‖)) in IHHT2; try lia.
    erewrite <- open_subst1_tm_comm in IHHT2; eauto. erewrite <- open_subst1_tm_comm in IHHT2; eauto.
    repeat erewrite subst1_qor_dist in IHHT2. apply IHHT2; auto.
    apply has_type_filter in HT2 as Hft.
    subst.
    rewrite app_length in *. simpl in *. rewrite Nat.add_1_r in *.
    unfold q_trans_tenv. repeat rewrite <- q_trans''_or_dist. repeat rewrite qand_qor_dist_l. assert (Hqn: closed_qenv_qn (S (‖ Γ0 ‖)) ((bind_tm, false, TRef d1 T1, {♦}) :: (bind_tm, true, TUnit, {♦}) :: Γ0 ++ [(bd, bx, Tx, dx)])). {
      unfold closed_qenv_qn. intros.
      bdestruct (x =? (S (S (‖ Γ0 ‖)))). replace x with (‖ (bind_tm, true, TUnit, {♦}) :: Γ0 ++ [(bd, bx, Tx, dx)] ‖) in *. rewrite indexr_head in H8. inversion H8. subst. simpl. clear. Qcrush. subst. simpl. rewrite app_length. simpl. lia.
      bdestruct (x =? (S (‖ Γ0 ‖))). replace x with (‖ Γ0 ++ [(bd, bx, Tx, dx)] ‖) in *. rewrite indexr_skip in H8; auto. rewrite indexr_head in H8. inversion H8. subst. simpl. clear. Qcrush. subst. simpl. rewrite app_length. simpl. lia.
      rewrite indexr_skip in H8; auto. rewrite indexr_skip in H8; auto. destruct a as [ [ [ b fr ] T' ] q']. eapply wf_tenv_prop in HwfΓ; eauto. simpl. apply indexr_var_some' in H8. rewrite app_length in *. simpl in *. rewrite Nat.add_1_r in *. eapply closed_Nats_mono; eauto. clear - HwfΓ. Qcrush. 1,2: subst; simpl; rewrite app_length; simpl; lia.
    }
    repeat apply Subq_qor_l. unfold q_trans_tenv. repeat erewrite q_trans''_extend_closed_id'. rewrite q_trans''_fuel_max. eapply @Subq_trans with (d2:=(q_trans_tenv (Γ0 ++ [(bd, bx, Tx, dx)]) dx' ⊓ q_trans_tenv (Γ0 ++ [(bd, bx, Tx, dx)]) φ)); eauto. unfold q_trans_tenv. eapply Subq_qand_split; eauto.
    rewrite q_trans''_fuel_max. apply q_trans''_subq; auto. 1,2: simpl; lia.
    eapply closed_qenv_qn_monotone; eauto.
    1-3: apply has_type_closed in HT1; intuition. 1-3: simpl; rewrite app_length in *; simpl in *;  rewrite Nat.add_1_r in *.
    apply closed_Qual_sub with (d':=φd) in H8; auto. clear - H8. Qcrush.
    eapply closed_qenv_qn_shrink in Hqn; eauto. apply closed_Qual_sub with (d':=φd) in H8; auto. clear - H8; Qcrush.
    eapply closed_qenv_qn_shrink in Hqn; eauto.
    eapply closed_Nats_mono with (n:=0). clear - H2. Qcrush. lia.
    eapply closed_qenv_qn_shrink in Hqn; eauto.
    eapply closed_Nats_mono with (n:=0). clear - H2. Qcrush. lia.
    replace (S (S (‖ Γ0 ‖))) with (‖ (bind_tm, true, TUnit, {♦}) :: Γ0 ++ [(bd, bx, Tx, dx)] ‖). pose proof q_trans_tenv_fv as Hfv. unfold q_trans_tenv in Hfv. rewrite Hfv. rewrite qand_qor_dist_l. erewrite qglb_disjoint_freshv; eauto. rewrite qor_empty_right. rewrite q_trans''_extend_closed_id'. eapply @Subq_trans with (d2:=(q_trans_tenv (Γ0 ++ [(bd, bx, Tx, dx)]) dx' ⊓ q_trans_tenv (Γ0 ++ [(bd, bx, Tx, dx)]) (φ ⊔ {♦}))); eauto. apply Subq_qand_split; auto.
    rewrite q_trans''_extend_closed_id'; eauto. rewrite q_trans''_fuel_max; eauto.
    eapply closed_qenv_qn_shrink in Hqn; eauto.
    eapply closed_Nats_mono with (n:=0). clear - H2. Qcrush. lia.
    rewrite q_trans''_extend_closed_id'. rewrite q_trans''_fuel_max; eauto. apply q_trans''_subq. clear; Qcrush.
    eapply closed_qenv_qn_shrink in Hqn; eauto.
    simpl; rewrite app_length; simpl; rewrite Nat.add_1_r. clear; Qcrush.
    eapply closed_qenv_qn_shrink in Hqn; eauto.
    unfold q_trans_tenv. rewrite <- q_trans''_or_dist. erewrite q_trans''_tenv_freshv_id; eauto. rewrite qand_qor_dist_l. rewrite qand_diamond_r_non_fresh. rewrite qor_empty_right; auto.
    unfold q_trans_tenv. rewrite q_trans''_closed_id; eauto. clear - H2; Qcrush.
    eapply closed_qenv_qn_shrink in Hqn; eauto.
    eapply closed_Nats_mono with (n:=0).  clear - H2; Qcrush. lia.
    rewrite q_trans''_closed_id; eauto 3.  clear - H2; Qcrush.
    simpl. rewrite app_length. simpl. lia.
    apply has_type_closed in HT1; intuition. constructor. constructor; auto. constructor. eapply closed_ty_monotone; eauto. eapply closed_Qual_monotone; eauto. eapply closed_Qual_monotone; eauto.
    apply Substq_weaken. simpl; rewrite app_length; simpl. eapply closed_Qual_monotone; eauto. lia. eapply wf_tenv_closed_qenv_qn. econstructor; eauto.
    apply Substq_weaken; eauto. simpl; rewrite app_length; simpl. eapply closed_Qual_monotone; eauto. lia.
    rewrite local_locs_open'; auto. rewrite local_locs_open'; auto.
    rewrite app_length. simpl. lia.
    subst φs. apply subst_qual_subqual_monotone; auto.
    eapply local_locs_substitution; eauto. apply has_type_closed in HT1; intuition; eauto.

  - (* t_withc *) specialize (IHHT) with (Γ := Γ0). simpl. simpl in Hwfdx'. apply kill_sep_kill_qor_rev in Hwfdx'; destruct Hwfdx' as [Hwfdx'1 Hwfdx'2].
    eapply t_withc.
    2: eapply IHHT; auto. auto.
    erewrite subst1_ty_id; eauto. erewrite subst1_qual_id; eauto.
    erewrite subst1_qual_id; eauto.
    Unshelve. all: auto.
Qed.


(* Aulixary lemma for one substitution *)

Lemma substitution1 : forall {t bdx bdf bf Tf df bx Tx dx Σ ϰ T d},
    has_type [(bdx, bx,Tx,dx) ; (bdf, bf,Tf,df)] (df ⊔ $!0 ⊔ $!1) Σ t T d ->
    wf_senv Σ ->
    forall {vf φ}, vtp Σ ϰ φ vf Tf df -> ♦∉ df ->
        forall {vx φ'}, vtp Σ ϰ φ' vx Tx dx -> ♦∉ dx ->
          local_locs vx = ∅ ->
          local_locs vf = ∅ ->
          kill_sep (local_locs t) dx ->
          kill_sep (local_locs t) df ->
          local_locs t ⊓ local_locs vf ⊑↑ ∅ ->
                    has_type [] (df ⊔ dx) Σ
                             ({ 0 |-> vf ; vx }ᵗ t)
                             ({ 0 |-> Tf ~ df ; Tx ~ dx }ᵀ T)
                             ({ 0 |-> df ; dx }ᵈ d).
  intros. specialize (vtp_closed H1) as Hclf. specialize (vtp_closed H3) as Hclx.
  intuition. replace ([(bdx, bx,Tx, dx); (bdf, bf,Tf, df)]) with ([(bdx, bx,Tx,dx)] ++ [(bdf, bf,Tf, df)]) in H; auto.
  (* substitute the first free variable df *)
  assert (Hsepf : (q_trans_tenv ([(bdx, bx, Tx, dx)] ++ [(bdf, bf, Tf, df)]) df) ⊓ (q_trans_tenv ([(bdx, bx, Tx, dx)] ++ [(bdf, bf, Tf, df)]) (df ⊔ $!0 ⊔ $!1)) ⊑↑ df). { unfold q_trans_tenv. rewrite q_trans''_closed_id; eauto. apply qand_Sub_l. Qcrush. }
  eapply (substitution_gen Hsepf) in H; eauto.
  (* substitute the second free variable dx *)
  replace ({0 |-> Tf ~ df }ᴳ [(bdx, bx, Tx, dx)]) with ([] ++ [(bdx, bx, Tx, dx)]) in H.
  replace ({0 |-> df }ᵈ (df ⊔ $! 0 ⊔ $! 1)) with (df ⊔ $!0) in H.
  assert (Hsepf' : (q_trans_tenv ([] ++ [(bdx, bx, Tx, dx)]) dx) ⊓ (q_trans_tenv ([] ++ [(bdx, bx, Tx, dx)]) (df ⊔ $!0)) ⊑↑ dx). { unfold q_trans_tenv. rewrite q_trans''_closed_id; auto. apply qand_Sub_l. clear - H16. Qcrush. }
  eapply (substitution_gen Hsepf') in H; eauto.
  replace ({0 |-> dx }ᵈ (df ⊔ $!0)) with (df ⊔ dx) in H. simpl in H. apply H.
  repeat rewrite subst1_qor_dist. rewrite subst1_just_fv0. erewrite subst1_qual_id; eauto.
  constructor; auto.
  (* need t dx, vf dx, vx df, vx dx, t and vx separate, vf and vx separate, actually vf is just t itself *) rewrite local_locs_subst'; auto.
  subst. repeat rewrite subst1_qor_dist. rewrite subst1_just_fv0. rewrite <- subst1_just_fv.
  erewrite subst1_qual_id; eauto.
  rewrite (@qor_assoc df df).
  rewrite qor_idem. auto.
  simpl. erewrite subst1_qual_id; eauto. erewrite subst1_ty_id; eauto.
  constructor; auto; simpl. eapply closed_ty_monotone; eauto. eapply closed_Qual_monotone; eauto.
  (* need t df, vf df, t and vf separate *)
Qed.


(* F-sub type substitution, following directly as term substitution *)

Lemma substitution_ty_gen :
  forall {t Γ φ bx Tx dx dx' Σ T d}, (q_trans_tenv (Γ ++ [(bind_ty, bx,Tx,dx)]) dx') ⊓ (q_trans_tenv (Γ ++ [(bind_ty, bx,Tx,dx)]) φ) ⊑↑ dx ->
  has_type (Γ ++ [(bind_ty, bx,Tx,dx)]) φ Σ t T d ->
  wf_tenv (Γ ++ [(bind_ty, bx,Tx,dx)]) Σ ->
  wf_senv Σ ->
  Substq (Γ ++ [(bind_ty, bx,Tx,dx)]) Σ dx dx' ->
  closed_ty 0 0 (length Σ) Tx ->
  closed_Qual 0 0 (length Σ) dx↑ ->
  closed_Qual 0 0 (length Σ) dx'↑ ->
  kill_sep (local_locs t) dx' ->
  has_type ({ 0 |-> Tx ~ dx' }ᴳ Γ) ({ 0 |-> dx' }ᵈ φ) Σ
                                   ({ 0 |-> tunit  }ᵗ t)
                                   ({ 0 |-> Tx ~  dx' }ᵀ T)
                                   ({ 0 |-> dx' }ᵈ d).

  intros t Γ φ bx Tx dx dx' Σ T d Hsep HT HwfΓ HwfΣ HSubst Hcl Hcl' Hcl'' Hwfdx'.
  remember (Γ ++ [(bind_ty, bx,Tx, dx)]) as Γ'.
  generalize dependent Γ.
  induction HT; intros; subst; pose (φs := {0 |-> dx' }ᵈ φ); replace ({0 |-> dx' }ᵈ φ) with φs in *; auto.

  - (* t_tabs *) simpl. apply t_tabs; auto. eapply closed_tm_subst1'; eauto.
    inversion H0. subst. constructor; try eapply closed_ty_subst1'; eauto; eapply closed_qual_subst1'; eauto.
    eapply closed_qual_subst1'; eauto.
    erewrite <- subst1_fresh_id. rewrite <- subst1_qor_dist. apply subst_qual_subqual_monotone; auto.
    apply subst_qual_subqual_monotone; auto. eauto.
    eapply local_locs_substitution; eauto.
    (* 1. instantiate the IH *)
    replace (length (Γ0 ++ [(bind_ty, bx, Tx, dx)])) with (S (‖Γ0‖)) in IHHT.
    rewrite subst1_env_length. rewrite app_comm_cons in IHHT. rewrite app_comm_cons in IHHT.
    remember (df ⊔ $!(S (‖Γ0‖)) ⊔ $!(S (S (‖Γ0‖))) ⊔ {♦}) as DF.
    replace ({0 |-> dx' }ᵈ df ⊔ $!(‖Γ0‖) ⊔ $!(S (‖Γ0‖)) ⊔ {♦}) with ({0 |-> dx' }ᵈ DF).
    intuition. specialize IHHT with (Γ := (((bind_ty, false,T1, d1) :: (bind_tm, true, (TAll d1 d2 T1 T2), df) :: Γ0))).
    (* 2. reason about opening and subst, apply IH *)
    unfold open_tm' in *. unfold open_ty' in *. unfold open_ty in *.
    unfold openq' in *. unfold openq in *.
    rewrite app_length in IHHT. rewrite subst1_env_length. simpl in *.
    replace (‖Γ0‖ + 1) with (S (‖Γ0‖)) in IHHT; try lia.
    erewrite <- open_subst1_tm_comm in IHHT; eauto. erewrite <- open_subst1_tm_comm in IHHT; eauto.
    erewrite <- open_subst1_ty_comm in IHHT; eauto. erewrite <- open_subst1_ty_comm in IHHT; eauto.
    erewrite <- open_subst1_qual_comm in IHHT; eauto. erewrite <- open_subst1_qual_comm in IHHT; eauto. repeat erewrite subst1_qor_dist in IHHT. apply IHHT; auto.
    apply has_type_filter in HT as Hft.
    subst.
    inversion H0. subst. rewrite app_length in *. simpl in *. rewrite Nat.add_1_r in *.
    unfold q_trans_tenv. repeat rewrite <- q_trans''_or_dist. repeat rewrite qand_qor_dist_l. assert (Hqn: closed_qenv_qn (S (‖ Γ0 ‖)) ((bind_ty, false, T1, d1) :: (bind_tm, true, TAll d1 d2 T1 T2, df) :: Γ0 ++ [(bind_ty, bx, Tx, dx)])). {
      unfold closed_qenv_qn. intros.
      bdestruct (x =? (S (S (‖ Γ0 ‖)))). replace x with (‖ (bind_tm, true, TAll d1 d2 T1 T2, df) :: Γ0 ++ [(bind_ty, bx, Tx, dx)] ‖) in *. rewrite indexr_head in H6. inversion H6. subst. simpl. clear - H13. Qcrush. subst. simpl. rewrite app_length. simpl. lia.
      bdestruct (x =? (S (‖ Γ0 ‖))). replace x with (‖ Γ0 ++ [(bind_ty, bx, Tx, dx)] ‖) in *. rewrite indexr_skip in H6; auto. rewrite indexr_head in H6. inversion H6. subst. simpl. clear - H3 H1. Qcrush. subst. simpl. rewrite app_length. simpl. lia.
      rewrite indexr_skip in H6; auto. rewrite indexr_skip in H6; auto. destruct a as [ [ [ b fr ] T' ] q']. eapply wf_tenv_prop in HwfΓ; eauto. simpl. apply indexr_var_some' in H6. rewrite app_length in *. simpl in *. rewrite Nat.add_1_r in *. eapply closed_Nats_mono; eauto. clear - HwfΓ. Qcrush. 1,2: subst; simpl; rewrite app_length; simpl; lia.
    }
    repeat apply Subq_qor_l. unfold q_trans_tenv. repeat erewrite q_trans''_extend_closed_id'. rewrite q_trans''_fuel_max. eapply @Subq_trans with (d2:=(q_trans_tenv (Γ0 ++ [(bind_ty, bx, Tx, dx)]) dx' ⊓ q_trans_tenv (Γ0 ++ [(bind_ty, bx, Tx, dx)]) φ)); eauto. unfold q_trans_tenv. eapply Subq_qand_split; eauto.
    repeat eapply q_trans''_subq; eauto. rewrite q_trans''_fuel_max. apply q_trans''_subq; auto.
    1-2: clear; simpl; lia.
    eapply closed_qenv_qn_monotone; eauto.
    1-3: simpl; rewrite app_length; simpl; rewrite Nat.add_1_r.
    clear - H1 H3. Qcrush.
    eapply closed_qenv_qn_shrink in Hqn; eauto.
    clear - H1 H3. Qcrush.
    eapply closed_qenv_qn_shrink in Hqn; eauto.
    eapply closed_Nats_mono with (n:=0). clear - Hcl''. Qcrush. lia.
    eapply closed_qenv_qn_shrink in Hqn; eauto. simpl. eapply closed_qenv_qn_monotone; eauto. rewrite app_length. lia.
    eapply closed_Nats_mono with (n:=0). clear - Hcl''. Qcrush. lia.
    erewrite q_trans''_extend_closed_id' with (q:=$! (S (‖ Γ0 ‖))). replace (S (‖ Γ0 ‖)) with (‖ Γ0 ++ [(bind_ty, bx, Tx, dx)] ‖). remember (Γ0 ++ [(bind_ty, bx, Tx, dx)]) as l. pose proof q_trans_tenv_fv as Hfv. unfold q_trans_tenv in Hfv. erewrite q_trans''_fuel_max with (E:=((bind_tm, true, TAll d1 d2 T1 T2, df) :: l)); auto. rewrite Hfv. rewrite qand_qor_dist_l. erewrite qglb_disjoint_freshv; eauto. rewrite qor_empty_right. repeat erewrite q_trans''_extend_closed_id'. erewrite q_trans''_fuel_max with (E:=(l)); simpl; auto. subst l. eapply @Subq_trans with (d2:=(q_trans_tenv (Γ0 ++ [(bind_ty, bx, Tx, dx)]) dx' ⊓ q_trans_tenv (Γ0 ++ [(bind_ty, bx, Tx, dx)]) φ)); eauto. apply Subq_qand_split; unfold q_trans_tenv; eapply q_trans''_subq; eauto.
    eapply closed_qenv_qn_shrink in Hqn; eauto.
    eapply closed_Nats_mono with (n:=0). clear - Hcl''. Qcrush. lia.
    eapply closed_qenv_qn_shrink in Hqn; eauto.
    simpl. eapply closed_qenv_qn_monotone; eauto.
    subst. rewrite app_length. simpl. lia.
    eapply closed_Nats_mono with (n:=0). clear - Hcl''. Qcrush. lia.
    rewrite q_trans''_closed_id; eauto 3. clear - Hcl''. Qcrush.
    simpl; rewrite app_length; simpl; lia.
    1,2: simpl; rewrite app_length; simpl; rewrite Nat.add_1_r.
    eapply closed_qenv_qn_shrink in Hqn; eauto.
    clear. Qcrush.
    replace (S (S (‖ Γ0 ‖))) with (‖ (bind_tm, true, TAll d1 d2 T1 T2, df) :: Γ0 ++ [(bind_ty, bx, Tx, dx)] ‖). pose proof q_trans_tenv_fv as Hfv. unfold q_trans_tenv in Hfv. rewrite Hfv. rewrite qand_qor_dist_l. erewrite qglb_disjoint_freshv; eauto. rewrite qor_empty_right. rewrite q_trans''_extend_closed_id'. eapply @Subq_trans with (d2:=(q_trans_tenv (Γ0 ++ [(bind_ty, bx, Tx, dx)]) dx' ⊓ q_trans_tenv (Γ0 ++ [(bind_ty, bx, Tx, dx)]) (φ ⊔ {♦}))); eauto. apply Subq_qand_split; auto.
    rewrite q_trans''_extend_closed_id'; eauto. rewrite q_trans''_fuel_max; eauto.
    eapply closed_qenv_qn_shrink in Hqn; eauto.
    eapply closed_Nats_mono with (n:=0). clear - Hcl''. Qcrush. lia.
    rewrite q_trans''_extend_closed_id'. rewrite q_trans''_fuel_max; eauto. apply q_trans''_subq. eapply Subq_trans; eauto.
    eapply closed_qenv_qn_shrink in Hqn; eauto.
    simpl; rewrite app_length; simpl; rewrite Nat.add_1_r. clear - H13. Qcrush.
    eapply closed_qenv_qn_shrink in Hqn; eauto.
    unfold q_trans_tenv. rewrite <- q_trans''_or_dist. erewrite q_trans''_tenv_freshv_id; eauto. rewrite qand_qor_dist_l. rewrite qand_diamond_r_non_fresh. rewrite qor_empty_right; auto.
    unfold q_trans_tenv. rewrite q_trans''_closed_id; eauto. clear - Hcl''. Qcrush.
    eapply closed_qenv_qn_shrink in Hqn; eauto.
    simpl. eapply closed_qenv_qn_monotone; eauto.
    rewrite app_length. simpl. lia.
    eapply closed_Nats_mono with (n:=0). clear - Hcl''. Qcrush. lia.
    rewrite q_trans''_closed_id; eauto 3. clear - Hcl''. Qcrush.
    simpl. rewrite app_length. simpl. lia.
    inversion H0. subst. constructor. constructor; auto. eapply closed_Qual_monotone; eauto. eapply closed_ty_monotone; eauto. eapply closed_Qual_monotone; eauto.
    apply Substq_weaken. simpl; rewrite app_length; simpl. eapply closed_Qual_monotone; eauto. lia. eapply wf_tenv_closed_qenv_qn. econstructor; eauto.
    apply Substq_weaken; eauto. simpl; rewrite app_length; simpl. eapply closed_Qual_monotone; eauto. lia.
    rewrite local_locs_open'; auto. rewrite local_locs_open'; auto.
    subst DF. repeat rewrite subst1_qor_dist.
    erewrite <- @subst1_just_fv with (x:=(‖ Γ0 ‖)). erewrite <- @subst1_just_fv with (x:=(S (‖ Γ0 ‖))). rewrite subst1_fresh_id. auto. rewrite app_length. simpl. lia.
  - (* t_tapp *) intuition. rename H6 into IHHT. simpl.
    replace ({ 0 |-> dx' }ᵈ (openq df d1 d2)) with
               (openq ({ 0 |-> dx' }ᵈ df) ({ 0 |-> dx' }ᵈ d1) ({ 0 |-> dx' }ᵈ d2)).
    replace ({0 |-> Tx ~ dx' }ᵀ (T2 <~ᵀ TUnit ~ ∅; T1 ~ d1)) with
               (({0 |-> Tx ~ dx' }ᵀ T2) <~ᵀ TUnit ~ ∅; ({0 |-> Tx ~ dx' }ᵀ T1) ~ ({0 |-> dx' }ᵈ d1)).
    apply t_tapp with (T1:= { 0 |-> Tx ~ dx' }ᵀ T1) (df:=({0 |-> dx' }ᵈ df)).
    replace (TAll ({0 |-> dx' }ᵈ d1) ({0 |-> dx' }ᵈ d2) ({0 |-> Tx ~ dx' }ᵀ T1) ({0 |-> Tx ~ dx' }ᵀ T2))
            with ({ 0 |-> Tx ~ dx' }ᵀ (TAll d1 d2 T1 T2)); auto.
    * eapply closed_ty_subst1; eauto; eapply closed_ty_monotone; eauto. rewrite subst1_env_length,app_length. simpl. lia.
    * eapply closed_qual_subst1; eauto; eapply closed_Qual_monotone; eauto. rewrite subst1_env_length,app_length. simpl. lia.
    * replace (∅) with ({0 |-> dx' }ᵈ ∅) by auto; unfold openq. repeat erewrite <- subst1_open_qual_comm; eauto. erewrite <- subst1_fresh_id. subst φs. rewrite <- subst1_qor_dist. apply subst_qual_subqual_monotone; auto.
    * apply subst1_non_fresh; eauto.
    * apply subst_qual_subqual_monotone. auto.
    * erewrite <- not_free_subst1_ty_iff; eauto.
    * eapply local_locs_substitution; eauto. apply has_type_closed in HT; intuition; eauto.
    * eapply local_locs_substitution; eauto. apply has_type_closed in HT; intuition; eauto.
    * replace (∅) with ({0 |-> dx' }ᵈ ∅) at 1; auto. unfold open_ty. repeat erewrite subst1_open_ty_comm; eauto.
    * replace (∅) with ({0 |-> dx' }ᵈ ∅) by auto; unfold openq. repeat erewrite <- subst1_open_qual_comm; eauto.

  - (* t_tapp_fresh *) intuition. rename H10 into IHHT. simpl.
    replace ({ 0 |-> dx' }ᵈ (openq df d1 d2)) with
               (openq ({ 0 |-> dx' }ᵈ df) ({ 0 |-> dx' }ᵈ d1) ({ 0 |-> dx' }ᵈ d2)).
    replace ({0 |-> Tx ~ dx' }ᵀ (T2 <~ᵀ TUnit ~ ∅; T1 ~ d1)) with
               (({0 |-> Tx ~ dx' }ᵀ T2) <~ᵀ TUnit ~ ∅; ({0 |-> Tx ~ dx' }ᵀ T1) ~ ({0 |-> dx' }ᵈ d1)).
    (*separation/overap is preserved after substitution*)
    assert (Hoverlap: {0 |-> dx' }ᵈ (q_trans_tenv (Γ0 ++ [(bind_ty, bx, Tx, dx)]) df ⊓ q_trans_tenv (Γ0 ++ [(bind_ty, bx, Tx, dx)]) d1) = ({0 |-> dx' }ᵈ (q_trans_tenv (Γ0 ++ [(bind_ty, bx, Tx, dx)]) df) ⊓ {0 |-> dx' }ᵈ (q_trans_tenv (Γ0 ++ [(bind_ty, bx, Tx, dx)]) d1))). {
      erewrite @subst1_qand_saturated' with (dx:=dx) (φ:=q_trans_tenv (Γ0 ++ [(bind_ty, bx, Tx, dx)]) φ). auto.
      eapply @Subq_trans with (d2:=q_trans_tenv (Γ0 ++ [(bind_ty, bx, Tx, dx)]) dx' ⊓ q_trans_tenv (Γ0 ++ [(bind_ty, bx, Tx, dx)]) φ ); eauto. apply Subq_qand_split; eauto. unfold q_trans_tenv; eapply q_trans''_subq'.
      eauto. eauto.
      1,2: eapply q_trans_tenv_subq_fresh; eauto. eapply has_type_filter; eauto.
      1,2: unfold q_trans_tenv; eapply q_trans''_tenv_saturated; eauto.
    }
    eapply t_tapp_fresh with (T1:= { 0 |-> Tx ~ dx' }ᵀ T1) (df:=({0 |-> dx' }ᵈ df)) (d1:=({0 |-> dx' }ᵈ d1)); eauto.
    apply t_sub with (T1:=({0 |-> Tx ~ dx' }ᵀ (TAll (q_trans_tenv (Γ0 ++ [(bind_ty, bx, Tx, dx)]) df
                  ⋒ q_trans_tenv (Γ0 ++ [(bind_ty, bx, Tx, dx)]) d1) d2 T1 T2))) (d1:=({0 |-> dx' }ᵈ df)). auto.
    simpl. rewrite subst1_qor_dist. rewrite Hoverlap. rewrite subst1_fresh_id. auto. unfold q_trans_tenv.
    apply has_type_closed in HT as Hcl'''. intuition. inversion H10. subst. rewrite subst1_env_length,app_length in *. simpl in *. try rewrite Nat.add_1_r in *. constructor; repeat rewrite subst1_env_length.
    + constructor. apply closed_Qual_qor; auto. apply closed_Qual_qand.
      eapply closed_qual_subst1; eauto. apply closed_Qual_q_trans''_monotone; eauto. apply wf_tenv_closed_qenv in HwfΓ. eapply closed_qenv_monotone; eauto. rewrite app_length. simpl. lia.
      eapply closed_qual_subst1; eauto. apply closed_Qual_q_trans''_monotone; eauto. apply wf_tenv_closed_qenv in HwfΓ. eapply closed_qenv_monotone; eauto. rewrite app_length. simpl. lia.
      eapply closed_qual_subst1; eauto.
      eapply closed_ty_subst1; eauto.
      eapply closed_ty_subst1; eauto.
    + constructor. apply closed_Qual_qor; auto. apply closed_Qual_qand.
      apply closed_Qual_q_trans''_monotone. eapply closed_qual_subst1; eauto. apply wf_tenv_closed_qenv in HwfΓ. eapply closed_qenv_subst1; eauto. rewrite app_length in HwfΓ. simpl in HwfΓ. rewrite Nat.add_1_r in HwfΓ. eapply closed_qenv_shrink'; eauto. eapply closed_Qual_monotone; eauto. lia.
      apply closed_Qual_q_trans''_monotone. eapply closed_qual_subst1; eauto. apply wf_tenv_closed_qenv in HwfΓ. eapply closed_qenv_subst1; eauto. rewrite app_length in HwfΓ. simpl in HwfΓ. rewrite Nat.add_1_r in HwfΓ. eapply closed_qenv_shrink'; eauto. eapply closed_Qual_monotone; eauto. lia.
      eapply closed_qual_subst1; eauto.
      eapply closed_ty_subst1; eauto.
      eapply closed_ty_subst1; eauto.
    + constructor; auto. eapply closed_qual_subst1; eauto. eapply closed_Qual_monotone; eauto. rewrite subst1_env_length. lia.
    + eapply stp_refl'; eauto 3. eapply closed_ty_subst1; eauto. eapply closed_ty_monotone; eauto. rewrite subst1_env_length. lia. constructor.
      apply Subq_qor. apply Subq_qand_split; eauto.
      1,2: eapply q_trans''_subst1_tenv_subq'; eauto.
      rewrite subst1_env_length. apply closed_Qual_qor; auto. apply closed_Qual_qand.
      eapply closed_qual_subst1; eauto 3. eapply closed_Qual_q_trans''_monotone; eauto. replace (S (‖ Γ0 ‖)) with (‖ Γ0 ++ [(bind_ty, bx, Tx, dx)] ‖). apply wf_tenv_closed_qenv; auto. rewrite app_length. simpl. lia.
      eapply closed_qual_subst1; eauto 3. eapply closed_Qual_q_trans''_monotone; eauto. replace (S (‖ Γ0 ‖)) with (‖ Γ0 ++ [(bind_ty, bx, Tx, dx)] ‖). apply wf_tenv_closed_qenv; auto. rewrite app_length. simpl. lia.
    + apply stp_refl. simpl. rewrite subst1_env_length. apply closed_ty_open2; try rewrite subst1_env_length; auto. eapply closed_ty_subst1; eauto. eapply closed_ty_monotone; eauto. 1,2: clear; apply Q_lift_closed; Qcrush. apply qstp_refl. simpl. apply closed_Qual_open2; try rewrite subst1_env_length. eapply closed_qual_subst1; eauto. eapply closed_Qual_monotone; eauto. 1,2: clear; Qcrush.
    + apply has_type_filter in HT. subst φs. erewrite <- subst1_fresh_id. rewrite <- subst1_qor_dist. apply subst_qual_subqual_monotone; auto.
    + eapply local_locs_substitution; eauto. apply has_type_closed in HT; intuition; eauto. apply has_type_local_loc_sep in HT; auto.
    + rewrite subst1_env_length. eapply closed_ty_subst1; eauto. eapply closed_ty_monotone; eauto. rewrite app_length. simpl. lia.
    + eapply closed_qual_subst1; eauto. eapply closed_Qual_monotone; eauto. rewrite app_length. simpl. rewrite subst1_env_length. lia.
    + apply has_type_filter in HT. subst φs. erewrite <- subst1_fresh_id. rewrite <- subst1_qor_dist. apply subst_qual_subqual_monotone; auto.
    + erewrite <- not_free_subst1_ty_iff; eauto; apply Substq_non_fresh in HSubst.
    + erewrite <- not_free_subst1_ty_iff; eauto; apply Substq_non_fresh in HSubst.
    + unfold openq; replace (∅) with ({0 |-> dx' }ᵈ ∅) by solve [apply subst1_qual_empty]; repeat erewrite <- subst1_open_qual_comm; eauto. subst φs. erewrite <- subst1_fresh_id. rewrite <- subst1_qor_dist. apply subst_qual_subqual_monotone; auto.
    + apply Subq_qor_l; eauto.
      eapply @Subq_trans with (d2:={0 |-> dx'}ᵈ (q_trans_tenv (Γ0 ++ [(bind_ty, bx, Tx, dx)]) df ⊓ q_trans_tenv (Γ0 ++ [(bind_ty, bx, Tx, dx)]) d1)); eauto. rewrite qand_commute. rewrite Hoverlap. unfold q_trans_tenv. rewrite app_length, subst1_env_length. simpl. rewrite Nat.add_1_r. apply Subq_qand_split; eapply q_trans''_subst1_tenv_subq'; eauto.
      erewrite <- subst1_fresh_id. subst φs. rewrite <- subst1_qor_dist. apply subst_qual_subqual_monotone. Qcrush. (*slow*)
    + eapply local_locs_substitution; eauto. apply has_type_closed in HT; intuition; eauto.
    + eapply local_locs_substitution; eauto. apply has_type_closed in HT; intuition; eauto.
    + eapply kill_sep_sub. 2: eapply local_locs_substitution. 5: eapply H8. 2,4: eauto. 2: apply has_type_closed in HT; intuition; eauto.
      eapply @Subq_trans with (d2:={0 |-> dx'}ᵈ (q_trans_tenv (Γ0 ++ [(bind_ty, bx, Tx, dx)]) df ⊓ q_trans_tenv (Γ0 ++ [(bind_ty, bx, Tx, dx)]) d1) ⊔ {♦}); eauto. apply Subq_qor.
      rewrite qand_commute. rewrite Hoverlap. unfold q_trans_tenv. rewrite app_length, subst1_env_length. simpl. rewrite Nat.add_1_r. apply Subq_qand_split; eapply q_trans''_subst1_tenv_subq'; eauto.
      rewrite subst1_qor_dist. apply Subq_qor. rewrite qand_commute. clear; Qcrush.
    + replace (∅) with ({0 |-> dx' }ᵈ ∅) at 1; auto. unfold open_ty. repeat erewrite subst1_open_ty_comm; eauto.
    + unfold openq. repeat erewrite <- subst1_open_qual_comm; eauto.
  - (* t_base *) simpl. replace ({0 |-> dx' }ᵈ ∅) with (∅) by solve [symmetry; apply subst1_qual_empty].
    apply t_base; auto. eapply closed_qual_subst1'; eauto.
  - (* t_var *) simpl. (bdestruct (x =? 0)).
    + (*  x is 0 *)
      rewrite indexr_skips in H; simpl; auto; try lia. simpl in H. subst. simpl in H. inversion H.
    + (* x is in Γ0 *)
      assert (Hx: 1 <= x); try lia. destruct x; try lia.
      apply @indexr_subst1 with (Tx := Tx)(dx := dx') in H; auto.
      apply t_var with (b:=b) (d:={0 |-> dx' }ᵈ d)(φ  := ({0 |-> dx' }ᵈ φ)). change x with (pred (S x)). auto.
      erewrite subst1_just_fv.
      repeat eapply subst_qual_subqual_monotone. auto.
      eapply closed_qual_subst1'; eauto. simpl. eapply closed_ty_subst1; eauto.
      simpl. eapply closed_qual_subst1; eauto.

  - (* t_abs *) simpl. apply t_abs; auto. eapply closed_tm_subst1'; eauto.
    inversion H0. subst. constructor; try eapply closed_ty_subst1'; eauto; eapply closed_qual_subst1'; eauto.
    eapply closed_qual_subst1'; eauto. apply subst_qual_subqual_monotone_fresh; auto. apply subst_qual_subqual_monotone; auto. eauto.
    eapply local_locs_substitution; eauto.
    (* 1. instantiate the IH *)
    replace (length (Γ0 ++ [(bind_ty, bx, Tx, dx)])) with (S (‖Γ0‖)) in IHHT.
    rewrite subst1_env_length. rewrite app_comm_cons in IHHT. rewrite app_comm_cons in IHHT.
    remember (df ⊔ $!(S (‖Γ0‖)) ⊔ $!(S (S (‖Γ0‖))) ⊔ {♦}) as DF.
    replace ({0 |-> dx' }ᵈ df ⊔ $!(‖Γ0‖) ⊔ $!(S (‖Γ0‖)) ⊔ {♦}) with ({0 |-> dx' }ᵈ DF).
    intuition. specialize IHHT with (Γ := (((bind_tm, false,T1, d1) :: (bind_tm, true, (TFun d1 d2 T1 T2), df) :: Γ0))).
    (* 2. reason about opening and subst, apply IH *)
    unfold open_tm' in *. unfold open_ty' in *. unfold open_ty in *.
    unfold openq' in *. unfold openq in *.
    rewrite app_length in IHHT. rewrite subst1_env_length. simpl in *.
    replace (‖Γ0‖ + 1) with (S (‖Γ0‖)) in IHHT; try lia.
    erewrite <- open_subst1_tm_comm in IHHT; eauto. erewrite <- open_subst1_tm_comm in IHHT; eauto.
    erewrite <- open_subst1_ty_comm in IHHT; eauto. erewrite <- open_subst1_ty_comm in IHHT; eauto.
    erewrite <- open_subst1_qual_comm in IHHT; eauto. erewrite <- open_subst1_qual_comm in IHHT; eauto. repeat erewrite subst1_qor_dist in IHHT. apply IHHT; auto.
    apply has_type_filter in HT as Hft.
    subst.
    inversion H0. subst. rewrite app_length in *. simpl in *. rewrite Nat.add_1_r in *.
    unfold q_trans_tenv. repeat rewrite <- q_trans''_or_dist. repeat rewrite qand_qor_dist_l. assert (Hqn: closed_qenv_qn (S (‖ Γ0 ‖)) ((bind_tm, false, T1, d1) :: (bind_tm, true, TFun d1 d2 T1 T2, df) :: Γ0 ++ [(bind_ty, bx, Tx, dx)])). {
      unfold closed_qenv_qn. intros.
      bdestruct (x =? (S (S (‖ Γ0 ‖)))). replace x with (‖ (bind_tm, true, TFun d1 d2 T1 T2, df) :: Γ0 ++ [(bind_ty, bx, Tx, dx)] ‖) in *. rewrite indexr_head in H6. inversion H6. subst. simpl. clear - H13. Qcrush. subst. simpl. rewrite app_length. simpl. lia.
      bdestruct (x =? (S (‖ Γ0 ‖))). replace x with (‖ Γ0 ++ [(bind_ty, bx, Tx, dx)] ‖) in *. rewrite indexr_skip in H6; auto. rewrite indexr_head in H6. inversion H6. subst. simpl. clear - H3 H1. Qcrush. subst. simpl. rewrite app_length. simpl. lia.
      rewrite indexr_skip in H6; auto. rewrite indexr_skip in H6; auto. destruct a as [ [ [ b fr ] T' ] q']. eapply wf_tenv_prop in HwfΓ; eauto. simpl. apply indexr_var_some' in H6. rewrite app_length in *. simpl in *. rewrite Nat.add_1_r in *. eapply closed_Nats_mono; eauto. clear - HwfΓ. Qcrush. 1,2: subst; simpl; rewrite app_length; simpl; lia.
    }
    repeat apply Subq_qor_l. unfold q_trans_tenv. repeat erewrite q_trans''_extend_closed_id'. rewrite q_trans''_fuel_max. eapply @Subq_trans with (d2:=(q_trans_tenv (Γ0 ++ [(bind_ty, bx, Tx, dx)]) dx' ⊓ q_trans_tenv (Γ0 ++ [(bind_ty, bx, Tx, dx)]) φ)); eauto. unfold q_trans_tenv. eapply Subq_qand_split; eauto.
    rewrite q_trans''_fuel_max. apply q_trans''_subq; auto. 1,2: simpl; lia.
    eapply closed_qenv_qn_monotone; eauto.
    1-3: simpl; rewrite app_length; simpl; rewrite Nat.add_1_r.
    clear - H3 H1. Qcrush.
    eapply closed_qenv_qn_shrink in Hqn; eauto.
    clear - H3 H1. Qcrush.
    eapply closed_qenv_qn_shrink in Hqn; eauto.
    eapply closed_Nats_mono with (n:=0). clear - Hcl''. Qcrush. lia.
    eapply closed_qenv_qn_shrink in Hqn; eauto. simpl. eapply closed_qenv_qn_monotone; eauto. rewrite app_length. lia.
    eapply closed_Nats_mono with (n:=0). clear - Hcl''. Qcrush. lia.
    erewrite q_trans''_extend_closed_id' with (q:=$! (S (‖ Γ0 ‖))). replace (S (‖ Γ0 ‖)) with (‖ Γ0 ++ [(bind_ty, bx, Tx, dx)] ‖). remember (Γ0 ++ [(bind_ty, bx, Tx, dx)]) as l. pose proof q_trans_tenv_fv as Hfv. unfold q_trans_tenv in Hfv. erewrite q_trans''_fuel_max with (E:=((bind_tm, true, TFun d1 d2 T1 T2, df) :: l)); auto. rewrite Hfv. rewrite qand_qor_dist_l. erewrite qglb_disjoint_freshv; eauto. rewrite qor_empty_right. repeat erewrite q_trans''_extend_closed_id'. erewrite q_trans''_fuel_max with (E:=(l)); simpl; auto. subst l. eapply @Subq_trans with (d2:=(q_trans_tenv (Γ0 ++ [(bind_ty, bx, Tx, dx)]) dx' ⊓ q_trans_tenv (Γ0 ++ [(bind_ty, bx, Tx, dx)]) φ)); eauto. apply Subq_qand_split; unfold q_trans_tenv; eapply q_trans''_subq; eauto.
    eapply closed_qenv_qn_shrink in Hqn; eauto.
    eapply closed_Nats_mono with (n:=0). clear - Hcl''. Qcrush. lia.
    eapply closed_qenv_qn_shrink in Hqn; eauto.
    simpl. eapply closed_qenv_qn_monotone; eauto.
    subst. rewrite app_length. simpl. lia.
    eapply closed_Nats_mono with (n:=0). clear - Hcl''. Qcrush. lia.
    rewrite q_trans''_closed_id; eauto 3. clear - Hcl''. Qcrush.
    simpl; rewrite app_length; simpl; lia.
    1,2: simpl; rewrite app_length; simpl; rewrite Nat.add_1_r.
    eapply closed_qenv_qn_shrink in Hqn; eauto.
    clear; Qcrush.
    replace (S (S (‖ Γ0 ‖))) with (‖ (bind_tm, true, TFun d1 d2 T1 T2, df) :: Γ0 ++ [(bind_ty, bx, Tx, dx)] ‖). pose proof q_trans_tenv_fv as Hfv. unfold q_trans_tenv in Hfv. rewrite Hfv. rewrite qand_qor_dist_l. erewrite qglb_disjoint_freshv; eauto. rewrite qor_empty_right. rewrite q_trans''_extend_closed_id'. eapply @Subq_trans with (d2:=(q_trans_tenv (Γ0 ++ [(bind_ty, bx, Tx, dx)]) dx' ⊓ q_trans_tenv (Γ0 ++ [(bind_ty, bx, Tx, dx)]) (φ ⊔ {♦}))); eauto. apply Subq_qand_split; auto.
    rewrite q_trans''_extend_closed_id'; eauto. rewrite q_trans''_fuel_max; eauto.
    eapply closed_qenv_qn_shrink in Hqn; eauto.
    eapply closed_Nats_mono with (n:=0). clear - Hcl''. Qcrush. lia.
    rewrite q_trans''_extend_closed_id'. rewrite q_trans''_fuel_max; eauto. apply q_trans''_subq. eapply Subq_trans; eauto.
    eapply closed_qenv_qn_shrink in Hqn; eauto.
    simpl; rewrite app_length; simpl; rewrite Nat.add_1_r. clear - H13. Qcrush.
    eapply closed_qenv_qn_shrink in Hqn; eauto.
    unfold q_trans_tenv. rewrite <- q_trans''_or_dist. erewrite q_trans''_tenv_freshv_id; eauto. rewrite qand_qor_dist_l. rewrite qand_diamond_r_non_fresh. rewrite qor_empty_right; auto.
    unfold q_trans_tenv. rewrite q_trans''_closed_id; eauto. clear - Hcl''. Qcrush.
    eapply closed_qenv_qn_shrink in Hqn; eauto.
    simpl. eapply closed_qenv_qn_monotone; eauto.
    rewrite app_length. simpl. lia.
    eapply closed_Nats_mono with (n:=0). clear - Hcl''. Qcrush. lia.
    rewrite q_trans''_closed_id; eauto 3. clear - Hcl''. Qcrush.
    simpl. rewrite app_length. simpl. lia.
    inversion H0. subst. constructor. constructor; auto. eapply closed_Qual_monotone; eauto. eapply closed_ty_monotone; eauto. eapply closed_Qual_monotone; eauto.
    apply Substq_weaken. simpl; rewrite app_length; simpl. eapply closed_Qual_monotone; eauto. lia. eapply wf_tenv_closed_qenv_qn. econstructor; eauto.
    apply Substq_weaken; eauto. simpl; rewrite app_length; simpl. eapply closed_Qual_monotone; eauto. lia.
    rewrite local_locs_open'; auto. rewrite local_locs_open'; auto.
    subst DF. repeat rewrite subst1_qor_dist.
    erewrite <- @subst1_just_fv with (x:=(‖ Γ0 ‖)). erewrite <- @subst1_just_fv with (x:=(S (‖ Γ0 ‖))). rewrite subst1_fresh_id. auto. rewrite app_length. simpl. lia.

  - (* t_app *) intuition. rename H2 into IHHT1. simpl. simpl in Hwfdx'. apply kill_sep_kill_qor_rev in Hwfdx'; destruct Hwfdx' as [Hwfdx'1 Hwfdx'2]. remember (qdiff φ (local_locs t1)) as φd. symmetry in Heqφd. apply (qdiff_local_loc_prop) in Heqφd as Heqφd'; destruct Heqφd'.
    replace ({ 0 |-> dx' }ᵈ (openq df d1 d2)) with
               (openq ({ 0 |-> dx' }ᵈ df) ({ 0 |-> dx' }ᵈ d1) ({ 0 |-> dx' }ᵈ d2)).
    replace ({0 |-> Tx ~ dx' }ᵀ (T2 <~ᵀ TUnit ~ ∅; T1 ~ d1)) with
               (({0 |-> Tx ~ dx' }ᵀ T2) <~ᵀ TUnit ~ ∅; ({0 |-> Tx ~ dx' }ᵀ T1) ~ ({0 |-> dx' }ᵈ d1)).
    apply t_app with (T1:= { 0 |-> Tx ~ dx' }ᵀ T1) (df:=({0 |-> dx' }ᵈ df)) (φd:={0 |-> dx' }ᵈ φd).
    replace (TFun ({0 |-> dx' }ᵈ d1) ({0 |-> dx' }ᵈ d2) ({0 |-> Tx ~ dx' }ᵀ T1) ({0 |-> Tx ~ dx' }ᵀ T2))
            with ({ 0 |->Tx ~ dx' }ᵀ (TFun d1 d2 T1 T2)); auto.
    eapply IHHT2; eauto. { clear - Hsep H5. eapply Qand_bound_sub. eauto. auto. unfold q_trans_tenv. apply q_trans''_subq; auto. }
    unfold openq; replace (∅) with ({0 |-> dx' }ᵈ ∅) by solve [apply subst1_qual_empty];
        erewrite <- subst1_open_qual_comm; eauto; erewrite <- subst1_open_qual_comm; eauto.
    * replace (∅) with ({0 |-> dx' }ᵈ ∅) by auto; unfold openq. repeat erewrite <- subst1_open_qual_comm; eauto. erewrite <- subst1_fresh_id. subst φs. rewrite <- subst1_qor_dist. apply subst_qual_subqual_monotone; auto.
    * replace (∅) with ({0 |-> dx' }ᵈ ∅) by auto; unfold openq. repeat erewrite <- subst1_open_qual_comm; eauto.
    * erewrite <- not_free_subst1_ty_iff; eauto.
    * subst. rewrite local_locs_subst'; auto. eapply qdiff_substitution; eauto. apply has_type_closed in HT1; intuition; eauto.
    * eapply local_locs_substitution; eauto. apply has_type_closed in HT2; intuition; eauto.
    * apply kill_sep_kill_qor_rev in H4; destruct H4. apply kill_sep_kill_qor.
      1-2: eapply local_locs_substitution; eauto. apply has_type_closed in HT1; intuition; eauto. apply has_type_closed in HT2; intuition; eauto.
    * replace (∅) with ({0 |-> dx' }ᵈ ∅) at 1; auto. unfold open_ty. repeat erewrite subst1_open_ty_comm; eauto.
    * unfold openq. repeat erewrite <- subst1_open_qual_comm; eauto.
  - (* t_app_fresh *) intuition. rename H3 into IHHT1. simpl. simpl in Hwfdx'. apply kill_sep_kill_qor_rev in Hwfdx'; destruct Hwfdx' as [Hwfdx'1 Hwfdx'2]. remember (qdiff φ (local_locs t1)) as φd. symmetry in Heqφd. apply (qdiff_local_loc_prop) in Heqφd as Heqφd'; destruct Heqφd'.
    replace ({ 0 |-> dx' }ᵈ (openq df d1 d2)) with
               (openq ({ 0 |-> dx' }ᵈ df) ({ 0 |-> dx' }ᵈ d1) ({ 0 |-> dx' }ᵈ d2)).
    replace ({0 |-> Tx ~ dx' }ᵀ (T2 <~ᵀ TUnit ~ ∅; T1 ~ d1)) with
               (({0 |-> Tx ~ dx' }ᵀ T2) <~ᵀ TUnit ~ ∅; ({0 |-> Tx ~ dx' }ᵀ T1) ~ ({0 |-> dx' }ᵈ d1)).
    (*separation/overap is preserved after substitution*)
    assert (Hoverlap: {0 |-> dx' }ᵈ (q_trans_tenv (Γ0 ++ [(bind_ty, bx, Tx, dx)]) df ⊓ q_trans_tenv (Γ0 ++ [(bind_ty, bx, Tx, dx)]) d1) = {0 |-> dx' }ᵈ (q_trans_tenv (Γ0 ++ [(bind_ty, bx, Tx, dx)]) df) ⊓ {0 |-> dx' }ᵈ (q_trans_tenv (Γ0 ++ [(bind_ty, bx, Tx, dx)]) d1)). {
      erewrite @subst1_qand_saturated' with (dx:=dx) (φ:=q_trans_tenv (Γ0 ++ [(bind_ty, bx, Tx, dx)]) φ). auto.
      eapply @Subq_trans with (d2:=q_trans_tenv (Γ0 ++ [(bind_ty, bx, Tx, dx)]) dx' ⊓ q_trans_tenv (Γ0 ++ [(bind_ty, bx, Tx, dx)]) φ); eauto.
        apply Subq_qand_split; auto; unfold q_trans_tenv; eapply q_trans''_subq'; eauto.
              eauto. eauto. 1,2: eapply q_trans_tenv_subq_fresh. eapply has_type_filter; eauto. apply has_type_filter in HT2. eapply Subq_trans; eauto.
        1,2: unfold q_trans_tenv; eapply q_trans''_tenv_saturated; eauto.
    }
    eapply t_app_fresh with (T1:= { 0 |-> Tx ~ dx' }ᵀ T1) (df:=({0 |-> dx' }ᵈ df)) (d1:=({0 |-> dx' }ᵈ d1)) (φd:={0|->dx'}ᵈ φd); eauto.
    apply t_sub with (T1:=({0 |-> Tx ~ dx' }ᵀ (TFun (q_trans_tenv (Γ0 ++ [(bind_ty, bx, Tx, dx)]) df
                  ⋒ q_trans_tenv (Γ0 ++ [(bind_ty, bx, Tx, dx)]) d1) d2 T1 T2))) (d1:=({0 |-> dx' }ᵈ df)). auto.
    simpl. rewrite subst1_qor_dist. rewrite Hoverlap. rewrite subst1_fresh_id. auto. unfold q_trans_tenv.
    apply has_type_closed in HT1 as Hcl''',HT2 as Hcl2. intuition. inversion H11. subst. rewrite subst1_env_length,app_length in *. simpl in *. try rewrite Nat.add_1_r in *. constructor; repeat rewrite subst1_env_length.
    + constructor. apply closed_Qual_qor; auto. apply closed_Qual_qand.
      eapply closed_qual_subst1; eauto. apply closed_Qual_q_trans''_monotone; eauto. apply wf_tenv_closed_qenv in HwfΓ. eapply closed_qenv_monotone; eauto. rewrite app_length. simpl. lia.
      eapply closed_qual_subst1; eauto. apply closed_Qual_q_trans''_monotone; eauto. apply wf_tenv_closed_qenv in HwfΓ. eapply closed_qenv_monotone; eauto. rewrite app_length. simpl. lia.
      eapply closed_qual_subst1; eauto.
      eapply closed_ty_subst1; eauto.
      eapply closed_ty_subst1; eauto.
    + constructor. apply closed_Qual_qor; auto. apply closed_Qual_qand.
      apply closed_Qual_q_trans''_monotone. eapply closed_qual_subst1; eauto. apply wf_tenv_closed_qenv in HwfΓ. eapply closed_qenv_subst1; eauto. rewrite app_length in HwfΓ. simpl in HwfΓ. rewrite Nat.add_1_r in HwfΓ. eapply closed_qenv_shrink'; eauto. eapply closed_Qual_monotone; eauto. lia.
      apply closed_Qual_q_trans''_monotone. eapply closed_qual_subst1; eauto. apply wf_tenv_closed_qenv in HwfΓ. eapply closed_qenv_subst1; eauto. rewrite app_length in HwfΓ. simpl in HwfΓ. rewrite Nat.add_1_r in HwfΓ. eapply closed_qenv_shrink'; eauto. eapply closed_Qual_monotone; eauto. lia.
      eapply closed_qual_subst1; eauto.
      eapply closed_ty_subst1; eauto.
      eapply closed_ty_subst1; eauto.
    + constructor; auto. eapply closed_qual_subst1; eauto. eapply closed_Qual_monotone; eauto. rewrite subst1_env_length. lia.
    + eapply stp_refl'; eauto 3. eapply closed_ty_subst1; eauto. eapply closed_ty_monotone; eauto. rewrite subst1_env_length. lia. constructor.
      apply Subq_qor. apply Subq_qand_split; eauto.
      1,2: eapply q_trans''_subst1_tenv_subq'; eauto.
      rewrite subst1_env_length. apply closed_Qual_qor; auto. apply closed_Qual_qand.
      eapply closed_qual_subst1; eauto 3. eapply closed_Qual_q_trans''_monotone; eauto. replace (S (‖ Γ0 ‖)) with (‖ Γ0 ++ [(bind_ty, bx, Tx, dx)] ‖). apply wf_tenv_closed_qenv; auto. rewrite app_length. simpl. lia.
      eapply closed_qual_subst1; eauto 3. eapply closed_Qual_q_trans''_monotone; eauto. replace (S (‖ Γ0 ‖)) with (‖ Γ0 ++ [(bind_ty, bx, Tx, dx)] ‖). apply wf_tenv_closed_qenv; auto. rewrite app_length. simpl. lia.
    + apply stp_refl. simpl. rewrite subst1_env_length. apply closed_ty_open2; try rewrite subst1_env_length; auto. eapply closed_ty_subst1; eauto. eapply closed_ty_monotone; eauto. 1,2: clear; apply Q_lift_closed; Qcrush. apply qstp_refl. simpl. apply closed_Qual_open2; try rewrite subst1_env_length. eapply closed_qual_subst1; eauto. eapply closed_Qual_monotone; eauto. 1,2: clear; Qcrush.
    + apply has_type_filter in HT1. subst φs. erewrite <- subst1_fresh_id. rewrite <- subst1_qor_dist. apply subst_qual_subqual_monotone; auto.
    + eapply local_locs_substitution; eauto. eapply has_type_closed in HT1; intuition; eauto. apply has_type_local_loc_sep in HT1; auto.
    + eapply IHHT2; eauto. clear - Hsep H7. eapply Qand_bound_sub. eauto. Qcrush. unfold q_trans_tenv. apply q_trans''_subq; auto.
    + erewrite <- not_free_subst1_ty_iff; eauto; apply Substq_non_fresh in HSubst.
    + erewrite <- not_free_subst1_ty_iff; eauto; apply Substq_non_fresh in HSubst.
    + unfold openq; replace (∅) with ({0 |-> dx' }ᵈ ∅) by solve [apply subst1_qual_empty]; repeat erewrite <- subst1_open_qual_comm; eauto. subst φs. erewrite <- subst1_fresh_id. rewrite <- subst1_qor_dist. apply subst_qual_subqual_monotone; auto.
    + apply Subq_qor_l; eauto.
      eapply @Subq_trans with (d2:={0 |-> dx'}ᵈ (q_trans_tenv (Γ0 ++ [(bind_ty, bx, Tx, dx)]) df ⊓ q_trans_tenv (Γ0 ++ [(bind_ty, bx, Tx, dx)]) d1)); eauto. rewrite qand_commute. rewrite Hoverlap. unfold q_trans_tenv. rewrite app_length, subst1_env_length. simpl. rewrite Nat.add_1_r. apply Subq_qand_split; eapply q_trans''_subst1_tenv_subq'; eauto.
      erewrite <- subst1_fresh_id. subst φs. rewrite <- subst1_qor_dist. apply subst_qual_subqual_monotone. Qcrush. (*slow*)
    + subst. rewrite local_locs_subst'; auto. eapply qdiff_substitution; eauto. apply has_type_closed in HT1; intuition; eauto.
    + eapply local_locs_substitution; eauto. apply has_type_closed in HT2; intuition; eauto.
    + apply kill_sep_kill_qor_rev in H5; destruct H5. apply kill_sep_kill_qor.
      1-2: eapply local_locs_substitution; eauto. apply has_type_closed in HT1; intuition; eauto. apply has_type_closed in HT2; intuition; eauto.
    + eapply kill_sep_sub. 2: eapply local_locs_substitution. 5: eapply H6. 4: eapply Hwfdx'1.  2: eauto. 2: apply has_type_closed in HT1; intuition; eauto.
      eapply @Subq_trans with (d2:={0 |-> dx'}ᵈ (q_trans_tenv (Γ0 ++ [(bind_ty, bx, Tx, dx)]) df ⊓ q_trans_tenv (Γ0 ++ [(bind_ty, bx, Tx, dx)]) d1) ⊔ {♦}); eauto. apply Subq_qor.
      rewrite qand_commute. rewrite Hoverlap. unfold q_trans_tenv. rewrite app_length, subst1_env_length. simpl. rewrite Nat.add_1_r. apply Subq_qand_split; eapply q_trans''_subst1_tenv_subq'; eauto.
      rewrite subst1_qor_dist. apply Subq_qor. rewrite qand_commute. clear; Qcrush.
    + replace (∅) with ({0 |-> dx' }ᵈ ∅) at 1; auto. unfold open_ty. repeat erewrite subst1_open_ty_comm; eauto.
    + unfold openq. repeat erewrite <- subst1_open_qual_comm; eauto.

  - (* t_loc *) erewrite @subst1_qual_id with (q:=(&!l)); eauto. simpl. erewrite subst1_ty_id; eauto.
    erewrite subst1_qual_id; eauto. apply t_loc; auto. eapply closed_qual_subst1'; eauto.
    erewrite <- @subst1_qual_id with (q:=(&!l)); eauto. eapply subst_qual_subqual_monotone; eauto.
    all : apply sindexr_var_some' in H0; eapply just_loc_closed; eauto.
  - (* t_ref *) rewrite subst1_fresh_id. simpl. apply t_ref; auto.
    eapply closed_ty_subst1'; eauto. apply subst1_non_fresh; eauto.
  - (* t_refat *) simpl. simpl in Hwfdx'. apply kill_sep_kill_qor_rev in Hwfdx'; destruct Hwfdx' as [Hwfdx'1 Hwfdx'2]. remember (qdiff φ (local_locs t2)) as φd. symmetry in Heqφd. apply (qdiff_local_loc_prop) in Heqφd as Heqφd'; destruct Heqφd'.
    eapply t_refat with (φd:={ 0 |-> dx' }ᵈ φd); auto. 2: apply subst1_non_fresh; eauto.
    eapply IHHT1; eauto. eapply Qand_bound_sub; eauto. unfold q_trans_tenv; apply q_trans''_subq; auto.
    eapply IHHT2; eauto.
    subst φs. rewrite local_locs_subst'; auto. subst. eapply qdiff_substitution; eauto. apply has_type_closed in HT2; intuition; eauto.
    eapply local_locs_substitution; eauto. apply has_type_closed in HT1; intuition; eauto.
  - (* t_deref *) simpl. apply t_deref with (d := { 0 |-> dx' }ᵈ d); auto.
    apply subst1_non_fresh; eauto. apply subst_qual_subqual_monotone. auto.
    eapply local_locs_substitution; eauto. apply has_type_closed in HT; intuition; eauto.
  - (* t_assign *) rewrite subst1_qual_empty in *. simpl. simpl in IHHT1. simpl in Hwfdx'. apply kill_sep_kill_qor_rev in Hwfdx'; destruct Hwfdx' as [Hwfdx'1 Hwfdx'2]. remember (qdiff φ (local_locs t1)) as φd. symmetry in Heqφd. apply (qdiff_local_loc_prop) in Heqφd as Heqφd'; destruct Heqφd'.
    apply t_assign with (T:={0 |-> Tx ~ dx' }ᵀ T) (d:=({0 |-> dx' }ᵈ d)) (d1:=({0 |-> dx' }ᵈ d1)) (φd := {0 |-> dx' }ᵈ φd); auto.
    eapply IHHT2; auto. eapply Qand_bound_sub; eauto. unfold q_trans_tenv; apply q_trans''_subq; auto.
    apply subst1_non_fresh; eauto.
    subst. rewrite local_locs_subst'; auto. eapply qdiff_substitution; eauto. apply has_type_closed in HT1; intuition; eauto.
    eapply local_locs_substitution; eauto. apply has_type_closed in HT2; intuition; eauto.
  - (* t_sub *) apply t_sub with (T1:={ 0 |-> Tx ~ dx' }ᵀ T1) (d1:={ 0 |-> dx' }ᵈ d1).
    eapply IHHT; eauto. eapply subst_stp; eauto. erewrite <- subst1_fresh_id. subst φs. rewrite <- subst1_qor_dist. apply subst_qual_subqual_monotone; auto.
    eapply local_locs_substitution; eauto. apply has_type_closed in HT; intuition; eauto.
  Unshelve. all : apply 0.
  - (* t_withr *) simpl. simpl in Hwfdx'. apply kill_sep_kill_qor_rev in Hwfdx'; destruct Hwfdx' as [Hwfdx'1 Hwfdx'2].
    eapply t_withr with (φd := { 0 |-> dx' }ᵈ φd); auto. eauto. eapply closed_ty_subst1'; eauto.
    eapply closed_qual_subst1'; eauto. eapply closed_tm_subst1'; eauto.
    specialize (IHHT1 Hsep HwfΓ HwfΣ HSubst).
    (* 1. instantiate the IH *)
    replace (length (Γ0 ++ [(bind_tm, bx, Tx, dx)])) with (S (‖Γ0‖)) in IHHT2.
    rewrite subst1_env_length. rewrite app_comm_cons in IHHT2. rewrite app_comm_cons in IHHT2.
    intuition. specialize IHHT2 with (Γ :=  ((bind_tm, false, TRef d1 T1, {♦}) :: (bind_tm, true, TUnit, {♦}) :: Γ0)).
    (* 2. reason about opening and subst, apply IH *)
    unfold open_tm' in *.
    rewrite app_length in IHHT2. rewrite subst1_env_length. simpl in *.
    replace (‖Γ0‖ + 1) with (S (‖Γ0‖)) in IHHT2; try lia.
    erewrite <- open_subst1_tm_comm in IHHT2; eauto. erewrite <- open_subst1_tm_comm in IHHT2; eauto.
    repeat erewrite subst1_qor_dist in IHHT2. apply IHHT2; auto.
    apply has_type_filter in HT2 as Hft.
    subst.
    rewrite app_length in *. simpl in *. rewrite Nat.add_1_r in *.
    unfold q_trans_tenv. repeat rewrite <- q_trans''_or_dist. repeat rewrite qand_qor_dist_l. assert (Hqn: closed_qenv_qn (S (‖ Γ0 ‖)) ((bind_tm, false, TRef d1 T1, {♦}) :: (bind_tm, true, TUnit, {♦}) :: Γ0 ++ [(bind_ty, bx, Tx, dx)])). {
      unfold closed_qenv_qn. intros.
      bdestruct (x =? (S (S (‖ Γ0 ‖)))). replace x with (‖ (bind_tm, true, TUnit, {♦}) :: Γ0 ++ [(bind_ty, bx, Tx, dx)] ‖) in *. rewrite indexr_head in H5. inversion H5. subst. simpl. clear; Qcrush. subst. simpl. rewrite app_length. simpl. lia.
      bdestruct (x =? (S (‖ Γ0 ‖))). replace x with (‖ Γ0 ++ [(bind_ty, bx, Tx, dx)] ‖) in *. rewrite indexr_skip in H5; auto. rewrite indexr_head in H5. inversion H5. subst. simpl. clear; Qcrush. subst. simpl. rewrite app_length. simpl. lia.
      rewrite indexr_skip in H5; auto. rewrite indexr_skip in H5; auto. destruct a as [ [ [ b fr ] T' ] q']. eapply wf_tenv_prop in HwfΓ; eauto. simpl. apply indexr_var_some' in H5. rewrite app_length in *. simpl in *. rewrite Nat.add_1_r in *. eapply closed_Nats_mono; eauto. clear - HwfΓ. Qcrush. 1,2: subst; simpl; rewrite app_length; simpl; lia.
    }
    repeat apply Subq_qor_l. unfold q_trans_tenv. repeat erewrite q_trans''_extend_closed_id'. rewrite q_trans''_fuel_max. eapply @Subq_trans with (d2:=(q_trans_tenv (Γ0 ++ [(bind_ty, bx, Tx, dx)]) dx' ⊓ q_trans_tenv (Γ0 ++ [(bind_ty, bx, Tx, dx)]) φ)); eauto. unfold q_trans_tenv. eapply Subq_qand_split; eauto.
    rewrite q_trans''_fuel_max. apply q_trans''_subq; auto. 1,2: simpl; lia.
    eapply closed_qenv_qn_monotone; eauto.
    1-3: apply has_type_closed in HT1; intuition. 1-3: simpl; rewrite app_length in *; simpl in *;  rewrite Nat.add_1_r in *.
    clear - H3 H5. eapply closed_Qual_sub with (d':=φd) in H5; auto. Qcrush.
    eapply closed_qenv_qn_shrink in Hqn; eauto. clear - H3 H5. eapply closed_Qual_sub with (d':=φd) in H5; auto. Qcrush.
    eapply closed_qenv_qn_shrink in Hqn; eauto.
    eapply closed_Nats_mono with (n:=0). clear - Hcl''. Qcrush. lia.
    eapply closed_qenv_qn_shrink in Hqn; eauto.
    eapply closed_Nats_mono with (n:=0). clear - Hcl''. Qcrush. lia.
    replace (S (S (‖ Γ0 ‖))) with (‖ (bind_tm, true, TUnit, {♦}) :: Γ0 ++ [(bind_ty, bx, Tx, dx)] ‖). pose proof q_trans_tenv_fv as Hfv. unfold q_trans_tenv in Hfv. rewrite Hfv. rewrite qand_qor_dist_l. erewrite qglb_disjoint_freshv; eauto. rewrite qor_empty_right. rewrite q_trans''_extend_closed_id'. eapply @Subq_trans with (d2:=(q_trans_tenv (Γ0 ++ [(bind_ty, bx, Tx, dx)]) dx' ⊓ q_trans_tenv (Γ0 ++ [(bind_ty, bx, Tx, dx)]) (φ ⊔ {♦}))); eauto. apply Subq_qand_split; auto.
    rewrite q_trans''_extend_closed_id'; eauto. rewrite q_trans''_fuel_max; eauto.
    eapply closed_qenv_qn_shrink in Hqn; eauto.
    eapply closed_Nats_mono with (n:=0). clear - Hcl''. Qcrush. lia.
    rewrite q_trans''_extend_closed_id'. rewrite q_trans''_fuel_max; eauto. apply q_trans''_subq. clear; Qcrush.
    eapply closed_qenv_qn_shrink in Hqn; eauto.
    simpl; rewrite app_length; simpl; rewrite Nat.add_1_r. clear; Qcrush.
    eapply closed_qenv_qn_shrink in Hqn; eauto.
    unfold q_trans_tenv. rewrite <- q_trans''_or_dist. erewrite q_trans''_tenv_freshv_id; eauto. rewrite qand_qor_dist_l. rewrite qand_diamond_r_non_fresh. rewrite qor_empty_right; auto.
    unfold q_trans_tenv. rewrite q_trans''_closed_id; eauto. clear - Hcl''; Qcrush.
    eapply closed_qenv_qn_shrink in Hqn; eauto.
    eapply closed_Nats_mono with (n:=0).  clear - Hcl''; Qcrush. lia.
    rewrite q_trans''_closed_id; eauto 3.  clear - Hcl''; Qcrush.
    simpl. rewrite app_length. simpl. lia.
    apply has_type_closed in HT1; intuition. constructor. constructor; auto. constructor. eapply closed_ty_monotone; eauto. eapply closed_Qual_monotone; eauto. eapply closed_Qual_monotone; eauto.
    apply Substq_weaken. simpl; rewrite app_length; simpl. eapply closed_Qual_monotone; eauto. lia. eapply wf_tenv_closed_qenv_qn. econstructor; eauto.
    apply Substq_weaken; eauto. simpl; rewrite app_length; simpl. eapply closed_Qual_monotone; eauto. lia.
    rewrite local_locs_open'; auto. rewrite local_locs_open'; auto.
    rewrite app_length. simpl. lia.
    subst φs. apply subst_qual_subqual_monotone; auto.
    eapply local_locs_substitution; eauto. apply has_type_closed in HT1; intuition; eauto.
  - (* t_withc *) specialize (IHHT) with (Γ := Γ0). simpl. simpl in Hwfdx'. apply kill_sep_kill_qor_rev in Hwfdx'; destruct Hwfdx' as [Hwfdx'1 Hwfdx'2].
    eapply t_withc.
    2: eapply IHHT; auto. auto.
    erewrite subst1_ty_id; eauto. erewrite subst1_qual_id; eauto.
    erewrite subst1_qual_id; eauto.
    Unshelve. all: auto. 1-4: apply 0. 1-2: apply bind_tm.
Qed.


(* case for t_tapp *)
Lemma substitution1_ty : forall {t bx bf Tx Tf dx df Σ ϰ T d},
     has_type [(bind_ty, bx, Tx, dx) ; (bind_tm, bf,Tf,df)] (df ⊔ $!0 ⊔ $!1) Σ t T d ->
     closed_ty 0 0 (length Σ) Tx ->
     closed_Qual 0 0 (length Σ) dx↑ -> ♦∉ dx ->
     wf_senv Σ ->
     forall {vt φ}, vtp Σ ϰ φ vt Tf df -> ♦∉ df ->
        local_locs vt = ∅ ->
        kill_sep (local_locs t) dx ->
        kill_sep (local_locs t) df ->
     has_type [] (df ⊔ dx) Σ  ( { 0 |-> vt; tunit  }ᵗ t)  ( { 0 |-> Tf ~ df; Tx ~ dx }ᵀ T) ({ 0 |-> df; dx }ᵈ d).
Proof.
  intros. subst. specialize (vtp_closed  H4) as HV_cl. specialize (has_type_closed H) as Hcl. intuition.
       intuition. replace ([(bind_ty, bx,Tx, dx); (bind_tm, bf,Tf, df)]) with ([(bind_ty, bx,Tx,dx)] ++ [(bind_tm, bf,Tf, df)]) in H; auto.
  assert (Hsepf : (q_trans_tenv ([(bind_ty, bx, Tx, dx)] ++ [(bind_tm, bf, Tf, df)]) df) ⊓ (q_trans_tenv ([(bind_ty, bx, Tx, dx)] ++ [(bind_tm, bf, Tf, df)]) (df ⊔ $!0 ⊔ $!1)) ⊑↑ df). { unfold q_trans_tenv. rewrite q_trans''_closed_id. apply qand_Sub_l. Qcrush. }
  eapply (substitution_gen Hsepf) in H; eauto.
  (* substitute the second free variable dx *)
  replace ({0 |-> Tf ~ df }ᴳ [(bind_ty, bx, Tx, dx)]) with ([] ++ [(bind_ty, bx, Tx, dx)]) in H.
  replace ({0 |-> df }ᵈ (df ⊔ $! 0 ⊔ $! 1)) with (df ⊔ $!0) in H.
  assert (Hsepf' : (q_trans_tenv ([] ++ [(bind_ty, bx, Tx, dx)]) dx) ⊓ (q_trans_tenv ([] ++ [(bind_ty, bx, Tx, dx)]) (df ⊔ $!0)) ⊑↑ dx). { unfold q_trans_tenv. rewrite q_trans''_closed_id. apply qand_Sub_l. clear - H1. Qcrush. }
  eapply (substitution_ty_gen Hsepf') in H; eauto.
  replace ({0 |-> dx }ᵈ (df ⊔ $!0)) with (df ⊔ dx) in H. simpl in H. apply H.
  repeat rewrite subst1_qor_dist. rewrite subst1_just_fv0. erewrite subst1_qual_id; eauto.
  constructor; auto.
  rewrite local_locs_subst'; auto.
  subst. repeat rewrite subst1_qor_dist. rewrite subst1_just_fv0. rewrite <- subst1_just_fv.
  erewrite subst1_qual_id; eauto.
  rewrite (@qor_assoc df df).
  rewrite qor_idem. auto.
  simpl. erewrite subst1_qual_id; eauto. erewrite subst1_ty_id; eauto.
  constructor; auto; simpl. eapply closed_ty_monotone; eauto. eapply closed_Qual_monotone; eauto.
Qed.

(* t_app case *)
Lemma substitution_stp1 : forall{T1 T2},
    forall {bdx bdf bx Tx bf Tf df dx Σ d1 d2},
      stp ([(bdx, bx,Tx,dx); (bdf, bf,Tf,{♦})]) Σ T1 d1 T2 d2 ->
      wf_senv Σ ->
      closed_ty 0 0 (‖Σ‖) Tx ->
      closed_ty 0 0 (‖Σ‖) Tf ->
      closed_Qual 0 0 (‖Σ‖) df↑ -> closed_Qual 0 0 (‖Σ‖) dx↑ -> ♦∉ df -> ♦∉ dx ->
      stp [] Σ ({ 0 |-> Tf ~ df; Tx ~ dx }ᵀ T1) ({ 0 |-> df ; dx }ᵈ d1) ({ 0 |-> Tf ~ df ; Tx ~ dx }ᵀ T2) ({ 0 |-> df ; dx }ᵈ d2).
  intros. replace [(bdx, bx, Tx, dx); (bdf, bf, Tf,{♦})] with ([(bdx, bx, Tx, dx)] ++ [(bdf, bf, Tf,{♦})]) in H; auto.
  eapply @subst_stp with (df':=df) in H; auto.
  replace ({0 |-> Tf ~ df }ᴳ [(bdx, bx, Tx, dx)]) with ([(bdx, bx, Tx, dx)]) in H.
  replace ([(bdx, bx, Tx, dx)]) with ([] ++ [(bdx, bx, Tx, dx)]) in H; auto.
  eapply @subst_stp with (df':=dx) in H; auto.
  constructor; auto.
  simpl. erewrite subst1_ty_id; eauto. erewrite subst1_qual_id; eauto.
  simpl. constructor; auto; simpl; auto. eapply closed_ty_monotone; eauto. eapply closed_Qual_monotone; eauto.
  apply Substq_weaken; simpl; auto. eapply closed_Qual_monotone; eauto. eauto.
  apply Substq_weaken; simpl; eauto. replace ({♦}) with (q_trans_tenv [] ∅ ⋒ q_trans_tenv [] df); auto.
Qed.

(* case for t_app_fresh *)
Lemma substitution2 : forall {bdx bdf t bf Tf df df1 Tx dx Σ ϰ T d},
  has_type [(bdx, false, Tx, q_trans_tenv [] df ⋒ q_trans_tenv [] dx);
    (bdf, bf, Tf, df1)] (df1 ⊔ $! 0 ⊔ $! 1) Σ t T d ->
    df1 ⊑↑ df ->
    wf_senv Σ ->
    forall {vf φ}, vtp Σ ϰ φ vf Tf df -> ♦∉ df -> closed_Qual 0 0 (‖Σ‖) df↑ ->
                  vtp Σ ϰ φ vf Tf df1 -> ♦∉ df1 -> closed_Qual 0 0 (‖Σ‖) df1↑ ->
    forall {vx φ'}, vtp Σ ϰ φ' vx Tx dx -> ♦∉ dx -> closed_Qual 0 0 (‖Σ‖) dx↑ ->
      local_locs vx = ∅ -> local_locs vf = ∅ ->
      kill_sep (local_locs t) dx -> kill_sep (local_locs t) df1 ->
    has_type [] (df1 ⊔ dx) Σ
        ({ 0 |-> vf ; vx }ᵗ t)
        ({ 0 |-> Tf ~ df1 ; Tx ~ dx }ᵀ T)
        ({ 0 |-> df1 ; dx }ᵈ d).
  intros. rename H2 into Hvf. rename H5 into Hvf1. rename H8 into Hvx.
  pose proof (vtp_closed Hvf). pose proof (vtp_closed Hvf1). pose proof (vtp_closed Hvx).
  assert (Hcl : closed_Qual 0 0 (‖ Σ ‖) (q_trans_tenv [] df ⋒ q_trans_tenv [] dx)↑). { apply closed_Qual_qor; auto. apply closed_Qual_qand; repeat apply closed_Qual_q_trans''_monotone; auto. all: apply closed_qenv_empty; apply []. }
  intuition. replace ([(bdx, false,Tx, q_trans_tenv [] df ⋒ q_trans_tenv [] dx); (bdf, bf,Tf, df)]) with ([(bdx, false,Tx, q_trans_tenv [] df ⋒ q_trans_tenv [] dx)] ++ [(bdf, bf,Tf, df)]) in H; auto.
  remember (q_trans_tenv ([(bdx, false, Tx, q_trans_tenv [] df ⋒ q_trans_tenv [] dx)] ++ [(bdf, bf, Tf, df1)]) df1) as DF. remember (q_trans_tenv ([(bdx, false, Tx, q_trans_tenv [] df ⋒ q_trans_tenv [] dx)] ++ [(bdf, bf, Tf, df1)]) (df1 ⊔ $!0 ⊔ $!1)) as Φ.
  assert (Hsepf : DF ⊓ Φ ⊑↑ df1). {
    subst. unfold q_trans_tenv. repeat rewrite qenv_saturated_trans''_id with (q:=df1); auto. apply qand_Sub_l. unfold qenv_saturated_q''. rewrite q_trans_one_closed_id; auto. clear - H20. Qcrush.
  }
  subst. eapply (substitution_gen Hsepf) in H; eauto.
  replace ({0 |-> df1 }ᵈ (df1 ⊔ $!0 ⊔ $!1)) with (df1 ⊔ $!0) in H.
  remember (q_trans_tenv ([] ++ [(bdx, false, Tx, q_trans_tenv [] df ⋒ q_trans_tenv [] dx)]) (df1 ⊔ $! 0)) as DF. remember (q_trans_tenv ([] ++ [(bdx, false, Tx, q_trans_tenv [] df ⋒ q_trans_tenv [] dx)]) dx) as DX.
  assert (Hsepf' : DX ⊓ DF ⊑↑ q_trans_tenv [] df ⋒ q_trans_tenv [] dx). {
    subst. unfold q_trans_tenv. simpl. ndestruct (qfvs dx 0). exfalso. Qcrush. eauto. repeat rewrite <- qor_assoc. assert (Hin: N_lift (qfvs (df1 ⊔ $! 0)) 0). { Qcrush. } unfold N_lift in Hin. rewrite Hin. repeat rewrite qand_qor_dist_l. replace (dx ⊓ $! 0) with (∅). Qcrush. apply Q_lift_eq. Qcrush. eauto.
  }
  remember (q_trans_tenv [] df ⋒ q_trans_tenv [] dx) as q.
  replace ([(bdx, false, Tx, q_trans_tenv [] df ⋒ q_trans_tenv [] dx)]) with ([] ++ [(bdx, false, Tx, q_trans_tenv [] df ⋒ q_trans_tenv [] dx)]) in H; auto.
  replace ({0 |-> Tf ~ df1 }ᴳ [(bdx, false, Tx, q)]) with ([] ++ [(bdx, false, Tx, q)]) in H.
  subst. eapply (substitution_gen Hsepf') in H; eauto; auto.
  replace ({0 |-> dx }ᵈ (df1 ⊔ $!0)) with (df1 ⊔ dx) in H. simpl in H. apply H.
  (*done, prove earlier replacements *)
  repeat rewrite subst1_qor_dist. rewrite subst1_just_fv0. erewrite subst1_qual_id; eauto.
  constructor; auto.
  apply Substq_weaken; auto. simpl. apply closed_qenv_qn_empty. apply [].
  rewrite local_locs_subst'; auto.
  simpl. erewrite subst1_qual_id; eauto. erewrite subst1_ty_id; eauto.
  repeat rewrite subst1_qor_dist. rewrite subst1_just_fv0. rewrite <- subst1_just_fv.
  erewrite subst1_qual_id; eauto. rewrite (@qor_assoc df1 df1). rewrite qor_idem. auto.
  constructor; auto; simpl. eapply closed_ty_monotone; eauto. eapply closed_Qual_monotone; eauto.
Qed.

Lemma substitution_stp2 : forall{T1 T2},
    forall {bdx bdf Tx bf Tf df0 dx0 df dx Σ d1 d2},
      stp ([(bdx, false,Tx,q_trans_tenv [] df0 ⋒ q_trans_tenv [] dx0); (bdf, bf,Tf,{♦})]) Σ T1 d1 T2 d2 ->
      wf_senv Σ ->
      closed_ty 0 0 (‖Σ‖) Tx ->
      closed_ty 0 0 (‖Σ‖) Tf ->
      df ⊑↑ df0 -> dx ⊑↑ dx0 ->
      closed_Qual 0 0 (‖Σ‖) df0↑ -> closed_Qual 0 0 (‖Σ‖) dx0↑ -> ♦∉ df -> ♦∉ dx ->
      stp [] Σ
          ({ 0 |-> Tf ~ df; Tx ~ dx }ᵀ T1)
          ({ 0 |-> df ; dx }ᵈ d1)
          ({ 0 |-> Tf ~ df ; Tx ~ dx }ᵀ T2)
          ({ 0 |-> df ; dx }ᵈ d2).
  intros.  assert (Hcl : closed_Qual 0 0 (‖ Σ ‖) (q_trans_tenv [] df0 ⋒ q_trans_tenv [] dx0)↑). { apply closed_Qual_qor; auto. apply closed_Qual_qand; auto. all: apply closed_Qual_q_trans''_monotone; eauto; apply wf_senv_closed_qenv; auto. }
  remember ([(bdx, false, Tx, q_trans_tenv [] df0 ⋒ q_trans_tenv [] dx0); (bdf, bf, Tf, {♦})]) as Γ.
  replace Γ with ([(bdx, false, Tx, q_trans_tenv [] df0 ⋒ q_trans_tenv [] dx0)] ++ [(bdf, bf, Tf, q_trans_tenv Γ ∅ ⋒ q_trans_tenv Γ df)]) in H; auto.
  eapply @subst_stp with (df':=df) in H; eauto.
  (* constructor. *)
  replace ({0 |-> Tf ~ df }ᴳ [(bdx, false, Tx, q_trans_tenv [] df0 ⋒ q_trans_tenv [] dx0 )]) with ([(bdx, false, Tx, q_trans_tenv [] df0 ⋒ q_trans_tenv [] dx0 )]) in H.
  assert (H' : stp [(bdx, false, Tx, q_trans_tenv [] df ⋒ q_trans_tenv [] dx)] Σ ({0 |-> Tf ~ df }ᵀ T1) ({0 |-> df }ᵈ d1) ({0 |-> Tf ~ df }ᵀ T2) ({0 |-> df }ᵈ d2)). {
    destruct bdx.
    + eapply narrowing_stp; eauto 3. intros. discriminate. apply stp_refl; auto. constructor; auto. apply Subq_qor. apply Subq_qand_split; unfold q_trans_tenv; apply q_trans''_subq; auto.
    + eapply narrowing_stp_ty; eauto 3. eapply closed_Qual_sub; eauto. apply Subq_qor; eauto. apply Subq_qand_split; unfold q_trans_tenv; apply q_trans''_subq; auto. apply stp_refl; auto. constructor; auto. apply Subq_qor. apply Subq_qand_split; unfold q_trans_tenv; apply q_trans''_subq; auto.
  }
  replace ([(bdx, false, Tx, df ⋒ dx )]) with ([] ++ [(bdx, false, Tx, df ⋒ dx)]) in H'; auto.
  replace ([]:tenv) with ({0 |-> Tx ~ dx}ᴳ ([]:tenv)); auto.
  eapply subst_stp ; eauto.
    simpl. constructor; auto.
  eapply closed_Qual_sub; eauto. apply Subq_qor. apply Subq_qand_split; unfold q_trans_tenv; apply q_trans''_subq; auto.
  apply Substq_weaken; auto. eapply @closed_Qual_sub with (d:=dx0); eauto. constructor; auto. eapply @closed_Qual_sub with (d:=df0); eauto.
    simpl. erewrite subst1_ty_id; eauto. erewrite subst1_qual_id; eauto.
  constructor. constructor; auto. apply closed_Qual_qor; auto. apply closed_Qual_qand_r; auto. unfold q_trans_tenv,q_trans_tenv. repeat rewrite q_trans''_empty_id; Qcrush.
  simpl. eapply closed_ty_monotone; eauto. simpl. eapply closed_Qual_monotone; eauto.
  replace ([(bdf, bf, Tf, q_trans_tenv Γ ∅ ⋒ q_trans_tenv Γ df)]) with ([(bdf, bf, Tf, {♦})]).
  subst. constructor; auto. unfold q_trans_tenv. rewrite q_trans''_empty_id; auto. Qcrush.
  replace ([(bdf, bf, Tf, q_trans_tenv Γ ∅ ⋒ q_trans_tenv Γ df)]) with ([(bdf, bf, Tf, {♦})]). auto.
  unfold q_trans_tenv. rewrite q_trans''_empty_id; auto. Qcrush.
Qed.

(* case for t_tapp_fresh *)
Lemma substitution2_ty : forall {t df1 df Tf Tx dx Σ ϰ T d},
    has_type [(bind_ty, false,Tx, q_trans_tenv [] df ⋒ q_trans_tenv [] dx); (bind_tm, true,Tf,df1)] (df1 ⊔ $!0 ⊔ $!1) Σ t T d ->
    ♦∉ dx ->
    wf_senv Σ ->
    closed_ty 0 0 (‖ Σ ‖) Tx ->
    closed_Qual 0 0 (‖Σ‖) dx↑ ->
    df1 ⊑↑ df ->
    ♦∉ df ->
    closed_Qual 0 0 (‖Σ‖) df ↑ ->
    forall {vt φ},
    vtp Σ ϰ φ vt Tf df1 ->
      local_locs vt = ∅ ->
      kill_sep (local_locs t) dx -> kill_sep (local_locs t) df1 ->
    has_type [] (df1 ⊔ dx) Σ
                ({ 0 |-> vt; tunit }ᵗ t)
                ({ 0 |-> Tf ~ df1; Tx ~ dx}ᵀ T)
                ({ 0 |-> df1 ; dx }ᵈ d).
Proof.
  intros.
  assert (Hcl : closed_Qual 0 0 (‖ Σ ‖) (q_trans_tenv [] df ⋒ q_trans_tenv [] dx)↑). { apply closed_Qual_qor; auto. apply closed_Qual_qand; repeat apply closed_Qual_q_trans''_monotone; auto. all: apply closed_qenv_empty; apply []. }
  intuition. replace ([(bind_ty, false,Tx, q_trans_tenv [] df ⋒ q_trans_tenv [] dx); (bind_tm, true,Tf, df)]) with ([(bind_ty, false,Tx, q_trans_tenv [] df ⋒ q_trans_tenv [] dx)] ++ [(bind_tm, true,Tf, df)]) in H; auto.
  remember (q_trans_tenv ([(bind_ty, false, Tx, q_trans_tenv [] df ⋒ q_trans_tenv [] dx)] ++ [(bind_tm, true, Tf, df1)]) df1) as DF. remember (q_trans_tenv ([(bind_ty, false, Tx, q_trans_tenv [] df ⋒ q_trans_tenv [] dx)] ++ [(bind_tm, true, Tf, df1)]) (df1 ⊔ $!0 ⊔ $!1)) as Φ.
  assert (Hsepf : DF ⊓ Φ ⊑↑ df1). {
    subst. unfold q_trans_tenv,q_trans_tenv. repeat rewrite qenv_saturated_trans''_id with (q:=df1); auto. apply qand_Sub_l. unfold qenv_saturated_q''. rewrite q_trans_one_closed_id; auto. Qcrush.
  }
  subst. eapply (substitution_gen Hsepf) in H; eauto.
  replace ({0 |-> df1 }ᵈ (df1 ⊔ $!0 ⊔ $!1)) with (df1 ⊔ $!0) in H.
  remember (q_trans_tenv ([] ++ [(bind_ty, false, Tx, q_trans_tenv [] df ⋒ q_trans_tenv [] dx)]) (df1 ⊔ $! 0)) as DF. remember (q_trans_tenv ([] ++ [(bind_ty, false, Tx, q_trans_tenv [] df ⋒ q_trans_tenv [] dx)]) dx) as DX.
  assert (Hsepf' : DX ⊓ DF ⊑↑ q_trans_tenv [] df ⋒ q_trans_tenv [] dx). {
    subst. unfold q_trans_tenv. simpl. ndestruct (qfvs dx 0). exfalso. Qcrush. eauto. repeat rewrite <- qor_assoc. assert (Hin: N_lift (qfvs (df1 ⊔ $! 0)) 0). { Qcrush. } unfold N_lift in Hin. rewrite Hin. repeat rewrite qand_qor_dist_l. replace (dx ⊓ $! 0) with (∅). Qcrush. apply Q_lift_eq. Qcrush. eauto.
  }
  remember (q_trans_tenv [] df ⋒ q_trans_tenv [] dx) as q.
  replace ([(bind_ty, false, Tx, q_trans_tenv [] df ⋒ q_trans_tenv [] dx)]) with ([] ++ [(bind_ty, false, Tx, q_trans_tenv [] df ⋒ q_trans_tenv [] dx)]) in H; auto.
  replace ({0 |-> Tf ~ df1 }ᴳ [(bind_ty, false, Tx, q)]) with ([] ++ [(bind_ty, false, Tx, q)]) in H.
  subst. eapply (substitution_ty_gen Hsepf') in H; eauto; auto.
  replace ({0 |-> dx }ᵈ (df1 ⊔ $!0)) with (df1 ⊔ dx) in H. simpl in H. apply H.
  (*done, prove earlier replacements *)
  repeat rewrite subst1_qor_dist. rewrite subst1_just_fv0. erewrite subst1_qual_id; eauto.
  constructor; auto.
  apply Substq_weaken; auto. simpl. apply closed_qenv_qn_empty. apply [].
  rewrite local_locs_subst'; auto.
  simpl. erewrite subst1_qual_id; eauto. erewrite subst1_ty_id; eauto.
  repeat rewrite subst1_qor_dist. rewrite subst1_just_fv0. rewrite <- subst1_just_fv.
  erewrite subst1_qual_id; eauto. rewrite (@qor_assoc df1 df1). rewrite qor_idem. auto.
  constructor; auto; simpl. constructor; auto; simpl. 1,2: apply vtp_closed in H7; intuition. eapply closed_ty_monotone; eauto. eapply closed_Qual_monotone; eauto. constructor. Qcrush.
Qed.


(* case of twithr *)
Lemma substitution2_withr : forall {bdx bdf t bf φ qr Tr Σ ϰ T d},
  has_type [(bdx, false, (TRef qr Tr), {♦});
    (bdf, bf, TUnit, {♦})] (φ ⊔ $! 1) Σ t T d ->
    closed_ty 0 0 (‖Σ‖) T -> closed_Qual 0 0 (‖Σ‖) d↑ -> closed_Qual 0 0 (‖Σ‖) φ↑ ->
    wf_senv (Σ) -> wf_senv ([(Tr, qr)] :: Σ) ->
    forall {vx φ'}, vtp ([(Tr, qr)] :: Σ) ϰ φ' vx (TRef qr Tr) (&!(‖Σ‖)) ->
      kill_sep (local_locs t) (&!(‖Σ‖)) ->
      local_locs vx = ∅ ->
    has_type [] (φ ⊔ &!(‖Σ‖)) ([(Tr, qr)] :: Σ)
        ({ 0 |-> tunit ; vx }ᵗ t)
        (T)
        (d).
Proof.
  intros. remember (TRef qr Tr) as Tx. remember (&!(‖Σ‖)) as dx. remember ([(Tr, qr)] :: Σ) as Σ'. eapply weaken_2D_store with (Σ':=Σ') in H; eauto. 2: { subst. eauto. } 2: { eapply closed_qenv_extend; auto. apply closed_qenv_extend; auto. apply closed_qenv_empty. apply []. }
  assert (Hvf: vtp Σ' ϰ φ' tunit TUnit ∅). { apply vtp_base. clear. Qcrush. apply kill_sep_empty. } rename H5 into Hvx.
  pose proof (vtp_closed Hvf). pose proof (vtp_closed Hvx).
  intuition. replace ([(bdx, false, Tx, {♦}); (bdf, bf, TUnit, {♦})]) with ([(bdx, false, Tx, {♦})] ++ [(bdf, bf,TUnit, {♦})]) in H; auto.
  remember (q_trans_tenv ([(bdx, false, Tx, {♦})] ++ [(bdf, bf, TUnit, {♦})]) ∅) as DF. remember (q_trans_tenv ([(bdx, false, Tx, {♦})] ++ [(bdf, bf, TUnit, {♦})]) (φ ⊔ $! 1)) as Φ.
  assert (Hsepf : DF ⊓ Φ ⊑↑ {♦}). {
    subst. unfold q_trans_tenv. repeat rewrite qenv_saturated_trans''_id with (q:=df1); auto. }
  subst DF. subst Φ. eapply (substitution_gen Hsepf) in H; eauto.
  replace ({0 |-> ∅ }ᵈ (φ ⊔ $! 1)) with (φ ⊔ $!0) in H. simpl in H. rewrite subst1_fresh_id in H. erewrite subst1_ty_id in H; eauto. erewrite subst1_ty_id in H; eauto. erewrite subst1_qual_id in H; eauto.
  remember (q_trans_tenv ([] ++ [(bdx, false, Tx, {♦})]) (φ ⊔ $! 0)) as DF. remember (q_trans_tenv ([] ++ [(bdx, false, Tx, {♦})]) dx) as DX.
  assert (Hsepf' : DX ⊓ DF ⊑↑ {♦}). {
    subst. unfold q_trans_tenv. simpl. ndestruct (qfvs &! (‖ Σ ‖) 0). exfalso. Qcrush. eauto. repeat rewrite <- qor_assoc. assert (Hin: N_lift (qfvs (φ ⊔ $! 0)) 0). { clear. Qcrush. } unfold N_lift in Hin. rewrite Hin. repeat rewrite qand_qor_dist_l. replace (&! (‖ Σ ‖) ⊓ $! 0) with (∅). 2: apply Q_lift_eq; Qcrush; eauto.
    apply Qor_bound. 2: apply Qor_bound; auto. 2: clear; Qcrush. clear - H2. Qcrush. subst. specialize (H2 (‖ Σ ‖) H4); lia.
  }
  subst DF DX.
  replace ([(bdx, false, Tx, {♦})]) with ([] ++ [(bdx, false, Tx, {♦})]) in H; auto.
  eapply (substitution_gen Hsepf') in H; eauto; auto.
  replace ({0 |-> dx }ᵈ (φ ⊔ $!0)) with (φ ⊔ dx) in H. simpl in H. erewrite subst1_ty_id in H; eauto. erewrite subst1_qual_id in H; eauto.
  (*done, prove earlier replacements *)
  repeat rewrite subst1_qor_dist. rewrite subst1_just_fv0. erewrite subst1_qual_id; eauto.
  constructor; auto. rewrite app_nil_l. replace ({♦}) with (q_trans_tenv [(bdx, false, Tx, {♦})] {♦} ⋒ q_trans_tenv [(bdx, false, Tx, {♦})] dx) at 2. constructor; auto. subst; clear; Qcrush. subst; unfold q_trans_tenv; auto. 1-3: subst.
  (* need t dx, vx φ, vx dx, t and vx separate *) rewrite local_locs_subst'; auto.
  rewrite subst1_qor_dist. erewrite subst1_qual_id; eauto.
  constructor; auto. eapply closed_ty_monotone; eauto. lia.
  replace ({♦}) with (q_trans_tenv ([(bdx, false, Tx, {♦})] ++ [(bdf, bf, TUnit, {♦})]) {♦} ⋒ q_trans_tenv ([(bdx, false, Tx, {♦})] ++ [(bdf, bf, TUnit, {♦})]) ∅) at 3. constructor; auto. subst; clear; Qcrush.
Qed.