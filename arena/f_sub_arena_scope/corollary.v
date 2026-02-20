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
Require Import vtp_subst.
Require Import type_safety.

Import QualNotations.
Local Open Scope qualifiers.
Import OpeningNotations.
Local Open Scope opening.

Import SplicingNotations.
Local Open Scope splicing.
Import SubstitutionNotations.
Local Open Scope substitutions.



(* To show preservation_of_separation, we derive progress & preservation from type safety: *)

(* This requires proving that the reduction relation is deterministic. *)
Lemma step_deterministic:  deterministic step.
  unfold deterministic. intros t t1 t2 σ σ1 σ2 Hstep1 Hstep2. generalize dependent σ2. generalize dependent t2.
  induction Hstep1; intros; inversion Hstep2; subst; auto; try solve [match goal with
  | [ H : step _ _ _ _  |- _ ] => eapply values_stuck in H; eauto; contradiction (* stuck cases, contradiction *)
  | [ H1 : step ?t ?s ?t' ?s', (* congruence cases, use IH *)
      IH : forall _ _, step ?t ?s _ _ -> _ |- _ = _ /\ _ = ?s' ] => specialize (IH t' s'); intuition; f_equal; auto
  end].
  rewrite H8 in H0. inversion H0. subst. intuition.
  rewrite H3 in H. inversion H. subst. rewrite H7 in H0. inversion H0. subst. intuition.
Qed.

Lemma progress : forall {Σ t T d φ ϰ},
    has_type [] φ Σ t T d -> wf_senv Σ ->  wf_step t ->
    value t \/ forall {σ}, wf_store σ -> CtxOK [] φ Σ ϰ σ -> exists t' σ', step t σ t' σ'.
Proof.
  intros Σ t T d φ ϰ HT Hwf Hwfstep.
  specialize (@type_safety Σ ϰ). intros HTS. apply (HTS) in HT; auto. intuition. right. intros σ Hwfstore HCtxOK.
  specialize (H σ). intuition. destruct H as [t' [σ' [Hstep  HPreserve]]].
  exists t'. exists σ'. intuition.
Qed.

Lemma preservation : forall {Σ t T d φ ϰ},
    has_type [] φ Σ t T d -> wf_senv Σ -> wf_step t ->
    forall{σ}, wf_store σ -> CtxOK [] φ Σ ϰ σ ->
    forall {t' σ'}, step t σ t' σ' ->
    preserve [] Σ ϰ φ (local_locs t) t' T d σ'.
Proof.
  intros Σ t T d φ ϰ HT Hwf Hwfstep σ Hwfstore HCtxOK t' σ' HStep. specialize (@type_safety Σ ϰ). intros HTS. apply HTS in HT; auto. intuition.
  - inversion HStep; subst; inversion H.
  - specialize (H σ HCtxOK Hwfstore). destruct H as [t'' [σ'' [HStep2 HPreserve]]].
    assert (t'' = t' /\ σ' = σ''). { intuition. 1,2: eapply step_deterministic; eauto.  }
    intuition. subst. intuition.
Qed.


(* ============ Empty Store Corollary ============ *)

Lemma empty_store_no_local_loc : forall Γ φ t T q,
  has_type Γ φ [] t T q ->
  local_locs t = ∅.
Proof.
  intros. remember [] as Σ. induction H; subst; simpl; auto.
  unfold open_tm' in IHhas_type. do 2 rewrite local_locs_open' in IHhas_type; auto.
  unfold open_tm' in IHhas_type. do 2 rewrite local_locs_open' in IHhas_type; auto.
  rewrite IHhas_type1; auto. rewrite IHhas_type2; auto.
  rewrite IHhas_type1; auto. rewrite IHhas_type2; auto.
  rewrite IHhas_type1; auto. rewrite IHhas_type2; auto.
  rewrite IHhas_type1; auto. rewrite IHhas_type2; auto.
  rewrite IHhas_type1; auto. unfold open_tm' in IHhas_type2. do 2 rewrite local_locs_open' in IHhas_type2; auto. rewrite IHhas_type2; auto.
  simpl in H; lia.
Qed.


Inductive has_type_static : tenv -> qual -> tm -> ty -> qual -> Prop :=
| ts_tabs: forall Γ φ t T1 T2 df d1 d2,
    closed_tm 2 (‖Γ‖) (0) t ->
    closed_ty 0 (‖Γ‖) (0) (TAll d1 d2 T1 T2) ->
    closed_Qual 0 (‖Γ‖) (0) φ↑ ->
    d1 ⊑↑ df ⊔ {♦} ->
    df ⊑↑ φ ->
    ♦∉ df ->
    has_type_static ((bind_ty, false, T1, d1)  :: (bind_tm, true, (TAll d1 d2 T1 T2), df) :: Γ)
             (df ⊔ ($!‖Γ‖) ⊔ $!(S (‖Γ‖))) (t <~²ᵗ Γ) (T2 <~²ᵀ Γ) (d2 <~²ᵈ Γ) ->
    has_type_static Γ φ (ttabs t) (TAll d1 d2 T1 T2) df

| ts_tapp: forall Γ φ t T1 T2 d1 d2 df,
    has_type_static Γ φ t (TAll d1 d2 T1 T2) df ->
    closed_ty 0 (‖Γ‖) (0) T1 ->
    closed_Qual 0 (‖Γ‖) (0) d1↑ ->
    (d2 <~ᵈ ∅ ; ∅) ⊑↑ (φ ⊔ {♦}) ->
    ♦∉ d1 ->
    d1 ⊑↑ φ ->
    not_free 0 T2 ->
    has_type_static Γ φ (ttapp t) (T2 <~ᵀ TUnit ~ ∅ ; T1 ~ d1) (d2 <~ᵈ df ; d1)

| ts_tapp_fresh : forall Γ φ t d1 d2 df T1 T2,
    has_type_static Γ φ t (TAll (q_trans_tenv Γ df ⋒ q_trans_tenv Γ d1) d2 T1 T2) df ->
    closed_ty 0 (‖Γ‖) (0) T1 ->
    closed_Qual 0 (‖Γ‖) (0) d1↑ ->
    d1 ⊑↑ (φ ⊔ {♦}) ->
    (♦∈ d1 -> not_free 1 T2) ->
    not_free 0 T2 ->
    (d2 <~ᵈ ∅ ; ∅) ⊑↑ (φ ⊔ {♦}) ->
    (q_trans_tenv Γ d1) ⋒ (q_trans_tenv Γ df) ⊑↑ (φ ⊔ {♦}) ->
    has_type_static Γ φ (ttapp t) (T2 <~ᵀ TUnit ~ ∅ ; T1 ~ d1) (d2 <~ᵈ df ; d1)

| ts_base : forall Γ φ,
    closed_Qual 0 (‖Γ‖) (0) φ↑ ->
    has_type_static Γ φ tunit TUnit ∅

| ts_var : forall Γ φ x b T d,
    indexr x Γ = Some ((bind_tm, b,T,d)) ->
    $!x ⊑↑ φ ->
    closed_Qual 0 (‖Γ‖) (0) φ↑ ->
    closed_ty   0 x (0) T ->
    closed_Qual 0 x (0) d↑ ->
    has_type_static Γ φ $x T $!x

| ts_abs: forall Γ φ T1 d1 T2 d2 df t,
    closed_tm   2 (‖Γ‖) (0) t ->
    closed_ty   0 (‖Γ‖) (0) (TFun d1 d2 T1 T2) ->
    closed_Qual 0 (‖Γ‖) (0) φ↑ ->
    d1 ⊑↑ df ⊔ {♦} ->
    df ⊑↑ φ ->
    ♦∉ df ->
    has_type_static ((bind_tm, false, T1, d1) :: (bind_tm, true, (TFun d1 d2 T1 T2), df) :: Γ)
             (df ⊔ ($!‖Γ‖) ⊔ $!(S (‖Γ‖))) (t <~²ᵗ Γ) (T2 <~²ᵀ Γ) (d2 <~²ᵈ Γ) ->
    has_type_static Γ φ (tabs t) (TFun d1 d2 T1 T2) df

| ts_app : forall Γ φ t1 d1 t2 d2 df T1 T2,
    has_type_static Γ φ t1 (TFun d1 d2 T1 T2) df ->
    has_type_static Γ φ t2 T1 d1 ->
    (d2 <~ᵈ ∅ ; ∅) ⊑↑ (φ ⊔ {♦}) ->
    ♦∉ d1 ->
    not_free 0 T2 ->
    has_type_static Γ φ (tapp t1 t2) (T2 <~ᵀ TUnit ~ ∅ ; T1 ~ d1) (d2 <~ᵈ df ; d1)

| ts_app_fresh : forall Γ φ t1 d1 t2 d2 df T1 T2,
    has_type_static Γ φ t1 (TFun (q_trans_tenv Γ df ⋒ q_trans_tenv Γ d1) d2 T1 T2) df ->
    has_type_static Γ φ t2 T1 d1 ->
    (♦∈ d1 -> not_free 1 T2) ->
    not_free 0 T2 ->
    (d2 <~ᵈ ∅ ; ∅) ⊑↑ (φ ⊔ {♦}) ->
    (q_trans_tenv Γ d1) ⋒ (q_trans_tenv Γ df) ⊑↑ (φ ⊔ {♦}) ->
    has_type_static Γ φ (tapp t1 t2) (T2 <~ᵀ TUnit ~ ∅ ; T1 ~ d1) (d2 <~ᵈ df ; d1)

| ts_ref: forall Γ φ T t d1,
    has_type_static Γ φ t T d1 ->
    closed_ty 0 (‖Γ‖) (0) T ->
    ♦∉ d1 ->
    has_type_static Γ φ (tref t) (TRef d1 T) ({♦})

| ts_refat : forall Γ φ t1 t2 T d T1 d1 d2,
    has_type_static Γ φ t1 T d ->
    ♦∉ d ->
    has_type_static Γ φ (t2) (TRef d1 T1) (d2) ->
    has_type_static Γ φ (trefat t1 t2) (TRef (d) T) (d2)

| ts_deref: forall Γ φ T d d1 t,
    has_type_static Γ φ t (TRef d1 T) d ->
    ♦∉ d1 ->
    d1 ⊑↑ φ ->
    has_type_static Γ φ !t T d1

| ts_assign: forall Γ φ T t1 d d1 t2,
    has_type_static Γ φ t1 (TRef d1 T) d ->
    has_type_static Γ φ t2 T d1 ->
    ♦∉ d1 ->
    has_type_static Γ φ (tassign t1 t2) TUnit ∅

| ts_sub: forall Γ φ e T1 d1 T2 d2,
    has_type_static Γ φ e T1 d1 ->
    stp Γ [] T1 d1 T2 d2 ->
    d2 ⊑↑ (φ ⊔ {♦}) ->
    has_type_static Γ φ e T2 d2

| ts_withr : forall Γ φ t1 t2 T1 d1 T2 d2,
    has_type_static Γ φ t1 T1 d1 ->
    ♦∉ d1 ->
    closed_ty 0 (‖Γ‖) (0) T2 ->   (* alternative of not_free 0 1*)
    closed_Qual 0 (‖Γ‖) (0) d2↑ ->  (*alternative of not_free 0 1*)
    closed_tm 2 (‖Γ‖) (0) t2 ->
    has_type_static ((bind_tm, false, TRef d1 T1, {♦}) :: (bind_tm, true, TUnit, {♦}) :: Γ)
      (φ ⊔ $!(S (‖Γ‖))) (t2 <~²ᵗ Γ) (T2) (d2) ->
    has_type_static Γ φ (twithr t1 t2) T2 d2
.
#[global] Hint Constructors has_type_static : core.


Lemma static_typing : forall Γ φ t T q,
  has_type_static Γ φ t T q ->
  has_type Γ φ [] t T q.
Proof.
  intros. induction H; auto.
  - eapply t_tabs; eauto. apply empty_store_no_local_loc in IHhas_type_static. unfold open_tm' in IHhas_type_static. do 2 rewrite local_locs_open' in IHhas_type_static; auto. rewrite IHhas_type_static. apply kill_sep_empty_kill.
  - apply empty_store_no_local_loc in IHhas_type_static as HL.
    eapply t_tapp; eauto. rewrite HL. apply kill_sep_empty_kill. rewrite HL. apply kill_sep_empty_kill.
  - apply empty_store_no_local_loc in IHhas_type_static as HL.
    eapply t_tapp_fresh; eauto. rewrite HL. apply kill_sep_empty_kill. rewrite HL. apply kill_sep_empty_kill. rewrite HL. apply kill_sep_empty_kill.
  - eapply t_var; eauto.
  - eapply t_abs; eauto. apply empty_store_no_local_loc in IHhas_type_static. unfold open_tm' in IHhas_type_static. do 2 rewrite local_locs_open' in IHhas_type_static; auto. rewrite IHhas_type_static. apply kill_sep_empty_kill.
  - apply empty_store_no_local_loc in IHhas_type_static1 as HL1. apply empty_store_no_local_loc in IHhas_type_static2 as HL2.
    eapply t_app; eauto. rewrite HL1. apply qdiff_empty.
    rewrite HL2; apply kill_sep_empty_kill. rewrite HL1; rewrite HL2; simpl. apply kill_sep_empty_kill.
  - apply empty_store_no_local_loc in IHhas_type_static1 as HL1. apply empty_store_no_local_loc in IHhas_type_static2 as HL2.
    eapply t_app_fresh; eauto. rewrite HL1. apply qdiff_empty.
    rewrite HL2; apply kill_sep_empty_kill. rewrite HL1; rewrite HL2; simpl. apply kill_sep_empty_kill. rewrite HL1; apply kill_sep_empty_kill.
  - apply empty_store_no_local_loc in IHhas_type_static1 as HL1. apply empty_store_no_local_loc in IHhas_type_static2 as HL2.
    eapply t_refat; eauto. rewrite HL2. apply qdiff_empty.
    rewrite HL1. apply kill_sep_empty_kill.
  - apply empty_store_no_local_loc in IHhas_type_static as HL.
    eapply t_deref; eauto. rewrite HL. apply kill_sep_empty_kill.
  - apply empty_store_no_local_loc in IHhas_type_static1 as HL1. apply empty_store_no_local_loc in IHhas_type_static2 as HL2.
    eapply t_assign; eauto. rewrite HL1. apply qdiff_empty.
    rewrite HL2; apply kill_sep_empty_kill.
  - apply empty_store_no_local_loc in IHhas_type_static as HL.
    eapply t_sub; eauto. rewrite HL. apply kill_sep_empty_kill.
  - apply empty_store_no_local_loc in IHhas_type_static1 as HL1. apply empty_store_no_local_loc in IHhas_type_static2 as HL2.
    eapply t_withr; eauto. rewrite HL1. apply kill_sep_empty_kill.
Qed.
