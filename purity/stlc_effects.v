Require Import Coq.Lists.List.
Require Import Psatz.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import FunctionalExtensionality.
Require Import PropExtensionality.

Import ListNotations.

Require Import tactics.
Require Import env.
Require Import qualifiers.
Require Import stlc_tae.
Require Import stlc_tae_ctx.

Import STLC.

Inductive ty_E : Type :=
| TBool_E  : ty_E
| TRef_E   : ty_E
| TFun_E   : ty_E -> ty_E -> bool -> ty_E  (* T1 -> T2 e *)
.

Definition tenv_E := list ty_E.


Inductive stp_E: ty_E -> ty_E -> Prop := 
| s_bool_E : 
  stp_E TBool_E TBool_E 
| s_ref_E: 
  stp_E TRef_E TRef_E
| s_fun_E: forall T1 T2 e2 T3 T4 e4, 
  stp_E T3 T1 ->
  stp_E T2 T4 ->
  bsub e2 e4 ->
  stp_E (TFun_E T1 T2 e2) (TFun_E T3 T4 e4)
.


Inductive has_type_E: tenv_E -> tm -> ty_E -> ql -> bool -> Prop := 
| t_true_E: forall env,
    has_type_E env ttrue TBool_E qempty false
| t_false_E: forall env,
    has_type_E env tfalse TBool_E qempty false
| t_var_E: forall x env T,
    indexr x env = Some T ->
    has_type_E env (tvar x) T (qone x) false
| t_ref_E: forall t env p e,
    has_type_E env t TBool_E p e ->
    has_type_E env (tref t) TRef_E p true
| t_get_E: forall t env p e,
    has_type_E env t TRef_E p e ->
    has_type_E env (tget t) TBool_E p true
| t_put_E: forall t1 t2 env p1 p2 e1 e2,
    has_type_E env t1 TRef_E p1 e1 ->
    has_type_E env t2 TBool_E p2 e2 ->
    has_type_E env (tput t1 t2) TBool_E (qor p1 p2) true
| t_app_E: forall env f t T1 T2 pf p1 e1 e2 ef,
    has_type_E env f (TFun_E T1 T2 e2) pf ef ->
    has_type_E env t T1 p1 e1 ->
    has_type_E env (tapp f t) T2 (qor pf p1) (e1||ef||e2)
| t_abs_E: forall env t T1 T2 p2 pf e2,
    has_type_E (T1::env) t T2 p2 e2 ->
    pf = (qdiff p2 (qone (length env))) -> 
    has_type_E env (tabs t) (TFun_E T1 T2 e2) pf false
| t_not_E: forall env t p e,
    has_type_E env t TBool_E p e ->
    has_type_E env (tnot t) TBool_E p e 
| t_bin_E: forall env t1 t2 p1 p2 e1 e2,
    has_type_E env t1 TBool_E p1 e1 ->
    has_type_E env t2 TBool_E p2 e2 ->
    has_type_E env (tbin t1 t2) TBool_E (qor p1 p2) (e1||e2)
| t_sub_eff_E: forall env t T p e,
    has_type_E env t T p e ->
    has_type_E env t T p true
| t_sub_stp_E: forall env t T1 p e1 T2 e2,
    has_type_E env t T1 p e1 ->
    stp_E T1 T2 ->
    bsub e1 e2 ->
    has_type_E env t T2 p e2 
.

Lemma ty_abs_app_E: forall G T1 T2 t1 t2 p1 p2 e1 e2,
  has_type_E G t1 T1 p1 e1 ->
  has_type_E (T1::G) t2 T2 p2 e2 ->
  has_type_E G (tapp (tabs t2) t1) T2  (qor (qdiff p2 (qone (length G))) p1) (e1||e2).
Proof.
  intros.
  eapply t_app_E with (f := tabs t2) (t := t1) (p1 := p1) in H as A.
  2:{ eapply t_abs_E. eauto. eauto.  }
  rewrite qor_idempetic in A. destruct e1, false; simpl in *; auto.
Qed.

Lemma hast_E_fv: forall G t T p e,
    has_type_E G t T p e -> p = fv (length G) t.
Proof.
  intros. induction H; simpl; eauto.
  - rewrite IHhas_type_E1, IHhas_type_E2. eauto.
  - rewrite IHhas_type_E1, IHhas_type_E2. eauto.
  - rewrite H0, IHhas_type_E. simpl. eauto.
  - rewrite IHhas_type_E1, IHhas_type_E2. eauto. 
Qed.

(* ---------- encoding 1: pure effect system  ---------- *)

Fixpoint tty_E T :=
    match T with 
    | TBool_E => TBool
    | TRef_E => TRef 
    | TFun_E T1 T2 e => TFun (tty_E T1) true true (tty_E T2) e true e 
end.

Definition ttenv_E (G: tenv_E): tenv := map (fun p => (tty_E p, true, true)) G.

Lemma translate_SE: forall T1 T2,
  stp_E T1 T2 ->
  stp (tty_E T1) (tty_E T2).
Proof.
  intros. induction H.
  - simpl. eapply s_bool.
  - simpl. eapply s_ref.
  - simpl. eapply s_fun; eauto. all: unfold bsub; auto.
Qed.

Lemma translate_E: forall G t T p e,
    has_type_E G t T p e ->
    has_type (ttenv_E G) t (tty_E T) p e true e.
Proof.
  intros. induction H.
  - eapply t_sub_cap. eapply t_true.
  - eapply t_sub_cap. eapply t_false.
  - assert (indexr x (ttenv_E env) = Some (tty_E T, true, true)). {
      unfold ttenv_E. erewrite indexr_map. 2: eauto. eauto. }
    eapply t_var in H0 as H2. simpl in H2. auto.
  - eapply t_sub_cap. eapply t_ref. eauto. 
  - eapply t_sub_fresh. eapply t_sub_cap.
    replace true with (e||true). 2: { destruct e; auto. }
    eapply t_get; eauto. 
  - eapply t_sub_fresh. eapply t_sub_cap. 
    replace true with (e1||e2||true). 2: { destruct e1, e2; auto. }
    eapply t_put; eauto. 
  - simpl in *.
    eapply t_sub_cap.
    eapply t_app with (frf := ef)(fr2 := e2)(fr1 := e1)(ef := ef)(e2 := e2) in IHhas_type_E2 as HA.
    2: { eapply t_sub_stp. eapply IHhas_type_E1. eapply s_fun. eapply stp_id. eapply stp_id. all: unfold bsub;auto. }
    simpl in *.
    replace (((ef || e1) && true || e2)) with (e1||ef||e2) in HA. 2: { destruct e1, ef; simpl; auto. }
    eauto.
  - simpl in *. eapply t_abs with (af := true) in IHhas_type_E as HA.
    2: eauto. 
    replace ((qor (qdiff p2 (qone (length (ttenv_E env))))(qdiff p2 (qone (length (ttenv_E env))))))
      with  pf in HA. 
    2: { unfold ttenv_E. rewrite map_length. rewrite qor_idempetic. auto.  }
    eapply t_sub_cap. eauto.
    intros ? ? ? ? ? ?. unfold bsub in *. auto.
  - eapply t_sub_cap with (a := false). eapply t_not in IHhas_type_E; eauto.
    eapply t_sub_stp. eauto. eapply stp_id. all: unfold bsub; auto. intuition.
  - eapply t_bin in IHhas_type_E2. 2: eapply IHhas_type_E1.
    eapply t_sub_stp. eauto. eapply stp_id. all: unfold bsub; auto. intuition.
  - eapply t_sub_stp. eauto. eapply stp_id. all: unfold bsub; auto.
  - eapply t_sub_stp. eauto. eapply translate_SE. auto. all: auto. unfold bsub. auto.
Qed.

Corollary translate_E_pure: forall G t T p,
    has_type_E G t T p false -> (* syntactic purity in E: e = false *)
    has_type (ttenv_E G) t (tty_E T) p false true false. (* pure in AE (fr = false, a is arbitrary, e = false) *)
Proof.
  intros. eapply translate_E in H; eauto.
Qed.

Theorem fundamental_E: forall G t T p e,
    has_type_E G t T p e ->
    sem_type (ttenv_E G)  t t (tty_E T) (plift p) e true e.
Proof.
  intros.
  eapply translate_E in H as H1.
  eapply fundamental in H1 as H2. 
  auto.
Qed.


(* syntactic typing of contexts *)
Inductive ctx_type_E : ctx -> tenv_E -> ty_E -> bool -> tenv_E -> ty_E -> ql -> bool -> Prop :=
| c_hole_e: forall G T e,
    ctx_type_E chole G T e G T qempty e
| c_ref_e: forall Gh Th eh G t p e,
    ctx_type_E t Gh Th eh G TBool_E p e ->
    ctx_type_E (cref t) Gh Th eh G TRef_E p true 
| c_get_e: forall Gh Th eh G t p e,
    ctx_type_E t Gh Th eh G TRef_E p e ->
    ctx_type_E (cget t) Gh Th eh G TBool_E p true
| c_put1_e: forall Gh Th eh G t1 p1 e1 t2 p2 e2,
    ctx_type_E t1 Gh Th eh G TRef_E p1 e1 ->
    has_type_E G t2 TBool_E p2 e2 ->
    ctx_type_E (cput1 t1 t2) Gh Th eh G TBool_E (qor p1 p2) true
| c_put2_e: forall Gh Th eh G t1 p1 e1 t2 p2 e2,
    has_type_E G t1 TRef_E p1 e1 ->
    ctx_type_E t2 Gh Th eh G TBool_E p2 e2 ->
    ctx_type_E (cput2 t1 t2) Gh Th eh G TBool_E (qor p1 p2) true
| c_app1_e: forall Gh Th eh G f t T1 T2 p1 p2 e1 ef e2,
    ctx_type_E f Gh Th eh G (TFun_E T1 T2 e2) p1 ef ->
    has_type_E G t T1 p2 e1 ->
    ctx_type_E (capp1 f t) Gh Th eh G T2 (qor p1 p2) (e1 || ef || e2)
| c_app2_e: forall Gh Th eh G f t T1 T2 p1 p2 e1 ef e2,
    has_type_E G f (TFun_E T1 T2 e2) p1 ef ->
    ctx_type_E t Gh Th eh G T1 p2 e1 ->
    ctx_type_E (capp2 f t) Gh Th eh G T2 (qor p1 p2) (e1 || ef || e2)
| c_abs_e: forall Gh Th eh G t T1 T2 p2 pf e2,
    ctx_type_E t Gh Th eh (T1::G) T2 p2 e2 ->
    pf = (qdiff p2 (qone (length G))) ->
    env_cap (ttenv_E G) pf true ->
    ctx_type_E (cabs t) Gh Th eh G (TFun_E T1 T2 e2) pf false 
| c_not_e: forall Gh Th eh G t p e,
    ctx_type_E t Gh Th eh G TBool_E p e -> 
    ctx_type_E (cnot t) Gh Th eh G TBool_E p e
| c_bin1_e: forall Gh Th eh G t1 p1 e1 t2 p2 e2,
    ctx_type_E t1 Gh Th eh G TBool_E p1 e1 ->
    has_type_E G t2 TBool_E p2 e2 ->
    ctx_type_E (cbin1 t1 t2) Gh Th eh G TBool_E (qor p1 p2) (e1||e2)
| c_bin2_e: forall Gh Th eh G t1 p1 e1 t2 p2 e2,
    has_type_E G t1 TBool_E p1 e1 ->
    ctx_type_E t2 Gh Th eh G TBool_E p2 e2 ->
    ctx_type_E (cbin2 t1 t2) Gh Th eh G TBool_E (qor p1 p2) (e1||e2)
| c_sub_eff_e: forall Gh Th eh G t T p e,
    ctx_type_E t Gh Th eh G T p e ->
    ctx_type_E t Gh Th eh G T p true
| c_sub_stp_e: forall Gh Th eh G t T1 p e1 T2 e2,
    ctx_type_E t Gh Th eh G T1 p e1 ->
    stp_E T1 T2 ->
    bsub e1 e2 ->
    ctx_type_E t Gh Th eh G T2 p e2
.

Check ctx_type. 

Lemma translate_ctx_E: forall (C:ctx) Gh Th eh G T p e,
  ctx_type_E C Gh Th eh G T p e ->
  ctx_type C (ttenv_E Gh) (tty_E Th) true eh true eh (ttenv_E G) (tty_E T) p e true e.
Proof.
  intros. induction H.
  + eapply c_sub_cap. eapply c_hole.
  + eapply c_sub_cap. eapply c_sub_eff. eapply c_ref; eauto.
  + replace true with (e||true) at 5.
    eapply c_sub_cap. eapply c_sub_fresh. eapply c_get. eauto.
    destruct e; auto.
  + replace true with (e1||e2||true) at 5.
    eapply c_sub_cap. eapply c_sub_fresh. eapply c_put1. eauto.
    eapply translate_E in H0. eauto.
    destruct e1, e2; auto.
  + replace true with (e1||e2||true) at 5.
    eapply c_sub_cap. eapply c_sub_fresh. eapply c_put2.
    eapply translate_E in H. eauto. eauto.
    destruct e1, e2; auto.
  + eapply c_sub_cap. 
    eapply translate_E in H0.
    eapply c_app1 with (frf := ef)(fr2 := e2)(fr1 := e1)(ef := ef)(e2 := e2) in H0.
    2: { eapply c_sub_cap. eapply c_sub_stp. eapply IHctx_type_E. 
        eapply s_fun. eapply stp_id. eapply stp_id. all: unfold bsub; auto. }
    simpl in *. replace ((ef||e1)&&true||e2) with (e1||ef||e2) in H0.
    2: { destruct ef, e1; auto. }
    eapply H0.
  + replace (e1 || ef || e2)  with (e1||ef || (true||true)&&e2) at 2.
    replace (e1||ef||e2) with ((ef||e1)&&true||e2). 2: { destruct ef, e1; auto. }
    replace true with ((true||true)&&true) at 4. 2: { simpl; auto. }
    eapply c_app2. eapply translate_E in H. 
    eapply t_sub_stp. eauto. eapply s_fun. eapply stp_id. eapply stp_id.
    all: unfold bsub in *; auto.
  + replace true with ((e2||true)&&(true||true)) at 3.
    eapply c_abs. eauto. unfold ttenv_E. rewrite map_length. auto.
    auto. destruct e2; auto.
  + eapply c_sub_stp. eapply c_not. eauto. eapply stp_id.
    all: unfold bsub; auto. intuition.
  + eapply c_sub_stp. eapply c_bin1; eauto.
    eapply translate_E in H0. eauto. eapply stp_id; auto.
    all: unfold bsub; auto. intuition.
  + eapply c_sub_stp. eapply c_bin2; eauto.
    eapply translate_E in H. eauto. eapply stp_id; auto.
    all: unfold bsub; auto. intuition.
  + eapply c_sub_eff. eapply c_sub_fresh. eauto.
  + eapply c_sub_stp. eauto. eapply translate_SE. auto.
    all: unfold bsub; auto.
Qed.


(* ---------- contextual equivalence ---------- *)


(* contextual equivalence: no boolean context can detect a difference *)
Definition contextual_equiv_E G t1 t2 T1 e1 :=
  forall C,
    ctx_type_E C G T1 e1 [] TBool_E qempty true ->
    exists S1 S2 v,
      tevaln [] [] (plug C t1) S1 v /\
      tevaln [] [] (plug C t2) S2 v.

(* congruence: syntactic context typing implies semantic context typing *)
Theorem congr_E:
  forall C G1 T1 e1 G2 T2 p2 e2,
    ctx_type_E C G1 T1 e1 G2 T2 p2 e2 ->
    sem_ctx_type C C (ttenv_E G1) (tty_E T1) true e1 true e1 (ttenv_E G2) (tty_E T2) p2 e2 true e2.
Proof.
  intros ? ? ? ? ? ? ? ? CX.
  eapply translate_ctx_E in CX. 
  eapply congr. eauto.
Qed.

Theorem soundness_E': forall G t1 t2 T p e,
  p = (fv (length G) t1) ->
  p = (fv (length G) t2) ->
  env_cap (ttenv_E G) p true ->
  sem_type (ttenv_E G) t1 t2 (tty_E T) (plift p) e true e ->
  contextual_equiv_E G t1 t2 T e.
Proof.
  intros. intros ? ?.
  eapply adequacy.
  eapply congr_E in H3. 
  eapply H3; eauto.
  unfold ttenv_E. rewrite map_length. rewrite <-H. rewrite <-H0. unfoldq; intuition.
  unfold ttenv_E. rewrite map_length. rewrite <-H. rewrite plift_or. rewrite por_same. auto.
  unfold ttenv_E. rewrite map_length. rewrite <-H. rewrite qor_idempetic. auto.
Qed.

(* soundness of binary logical relation: implies contextual equivalence *)
Theorem soundness_E: forall G t1 t2 T p e,
  has_type_E G t1 T p e ->
  has_type_E G t2 T p e ->
  (sem_type (ttenv_E G) t1 t2 (tty_E T) (plift p) e true e ->
  contextual_equiv_E G t1 t2 T e).
Proof.
  intros.
  eapply soundness_E'. 
  eapply translate_E in H as H'. eapply hast_fv in H'. unfold ttenv_E in H'. rewrite map_length in H'. eapply H'.
  eapply translate_E in H0 as H''. eapply hast_fv in H''. unfold ttenv_E in H''. rewrite map_length in H''. eapply H''.
  intros ????? ?. unfold bsub in *.  auto. eauto.
Qed.  


(* soudness of purity: a syntactically pure term is semantically pure *)
Theorem soundness_of_purity_E: forall t1 G T1 pt1,
    has_type_E G t1 T1 pt1 false -> (* fr1 = false and e1 = false: syntactic purity! *)    
    contextual_purity (ttenv_E G) t1 (tty_E T1) true. 
Proof.
  intros. 
  eapply translate_E in H.
  eapply soundness_of_purity. eauto.
Qed.

Theorem reorder_tbin_E: forall G t1 t2 p1 p2
  (W1: has_type_E G t1 TBool_E p1 false)
  (W2: has_type_E G t2 TBool_E p2 false),
  sem_type (ttenv_E G) (tbin t1 t2) (tbin t2 t1) TBool (por (plift p1) (plift p2)) false false false.
Proof.
  intros.
  eapply translate_E in W1.
  eapply translate_E in W2.
  eapply reorder_tbin_mention; eauto.
Qed.

Lemma tbin_inversion1: forall env t T p e
  (W: has_type_E env t T p e),
  forall t1 t2,
    t = tbin t1 t2 ->
    T = TBool_E ->
  exists p1 e1, 
    psub (plift p1) (plift p) /\ 
    bsub e1 e /\ 
    has_type_E env t1 TBool_E p1 e1.
Proof.
  intros env t T p e W. 
  induction W; intros.
  - inversion H.
  - inversion H.
  - inversion H0.
  - inversion H.
  - inversion H.
  - inversion H.
  - inversion H.
  - inversion H0.
  - inversion H.
  - inversion H. subst t0 t3.
    exists p1, e1.
    split. 2: split. 
    -- rewrite plift_or. unfoldq; intuition.
    -- unfold bsub. intros. subst e1. simpl. auto.
    -- auto.
  - eapply IHW in H; auto.
    destruct H as (p1 & e1 & ? & ? & ?).
    exists p1, e1. 
    split. auto.  
    split. unfold bsub. auto.
    auto.
  - eapply IHW in H1; auto.
    destruct H1 as (p1' & e1' & ? & ? & ?).
    exists p1', e1'. 
    split. auto.  
    split. unfold bsub. auto.
    auto.
    subst T2. inversion H. auto.
Qed. 

Lemma tbin_inversion2: forall env t T p e
  (W: has_type_E env t T p e),
  forall t1 t2,
    t = tbin t1 t2 ->
    T = TBool_E ->
  exists p2 e2, 
    psub (plift p2) (plift p) /\ 
    bsub e2 e /\ 
    has_type_E env t2 TBool_E p2 e2.
Proof.
  intros env t T p e W. 
  induction W; intros.
  - inversion H.
  - inversion H.
  - inversion H0.
  - inversion H.
  - inversion H.
  - inversion H.
  - inversion H.
  - inversion H0.
  - inversion H.
  - inversion H. subst t0 t3.
    exists p2, e2.
    split. 2: split. 
    -- rewrite plift_or. unfoldq; intuition.
    -- unfold bsub. intros. subst e2. destruct e1; simpl; auto.
    -- auto.
  - eapply IHW in H; auto.
    destruct H as (p2 & e2 & ? & ? & ?).
    exists p2, e2. 
    split. auto.  
    split. unfold bsub. auto.
    auto.
  - eapply IHW in H1; auto.
    destruct H1 as (p2' & e2' & ? & ? & ?).
    exists p2', e2'. 
    split. auto.  
    split. unfold bsub. auto.
    auto.
    subst T2. inversion H. auto.
Qed. 


