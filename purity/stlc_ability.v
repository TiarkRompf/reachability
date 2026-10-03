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

Inductive ty_A : Type :=
  | TBool_A  : ty_A
  | TRef_A   : ty_A
  | TFun_A   : ty_A -> bool -> ty_A -> bool -> ty_A (* T1^a1 -> T2^a2 *)
.

Definition tenv_A := list (ty_A * bool).

Definition env_cap_A (G: tenv_A) p a := forall x T1 a1,
  indexr x G = Some (T1, a1) -> p x = true -> bsub a1 a.

Fixpoint tty_A T :=
  match T with
  | TBool_A => TBool
  | TRef_A => TRef
  | TFun_A T1 a1 T2 a2 => TFun (tty_A T1) a1 a1 (tty_A T2) a2 a2 true
  end.

Definition ttenv_A (G: tenv_A): tenv := map (fun p => (tty_A (fst p), snd p, snd p)) G. 

Inductive stp_A: ty_A -> ty_A -> Prop := 
| s_bool_A : 
  stp_A TBool_A TBool_A 
| s_ref_A: 
  stp_A TRef_A TRef_A
| s_fun_A: forall T1 a1 T2 a2 T3 a3 T4 a4, 
  stp_A T3 T1 ->
  stp_A T2 T4 ->
  bsub a3 a1 ->
  bsub a2 a4 ->
  stp_A (TFun_A T1 a1 T2 a2) (TFun_A T3 a3 T4 a4)
.


Inductive has_type_A : tenv_A -> tm -> ty_A -> ql -> bool -> Prop :=
| t_true_A: forall env,
    has_type_A env ttrue TBool_A qempty false
| t_false_A: forall env,
    has_type_A env tfalse TBool_A qempty false
| t_var_A: forall x env T a,
    indexr x env = Some (T, a) ->
    has_type_A env (tvar x) T (qone x) a
| t_ref_A: forall t env p a,
    has_type_A env t TBool_A p a ->
    has_type_A env (tref t) TRef_A p true
| t_get_A: forall t env p a,
    has_type_A env t TRef_A p a ->
    has_type_A env (tget t) TBool_A p false
| t_put_A: forall t1 t2 env p1 p2 a1 a2,
    has_type_A env t1 TRef_A p1 a1 ->
    has_type_A env t2 TBool_A p2 a2 ->
    has_type_A env (tput t1 t2) TBool_A (qor p1 p2) false
| t_app_A: forall env f t T1 T2 pf p1 a1 a2 af,
    has_type_A env f (TFun_A T1 a1 T2 a2) pf af ->
    has_type_A env t T1 p1 a1 ->
    has_type_A env (tapp f t) T2 (qor pf p1) a2
| t_abs_A: forall env t T1 T2 p2 pf a1 a2 af,
    has_type_A ((T1, a1)::env) t T2 p2 a2 ->
    pf = (qdiff p2 (qone (length env))) ->
    env_cap_A env pf af ->
    has_type_A env (tabs t) (TFun_A T1 a1 T2 a2) pf af
| t_not_A: forall env t p a,
    has_type_A env t TBool_A p a ->
    has_type_A env (tnot t) TBool_A p a
| t_bin_A: forall env t1 t2 p1 p2 a1 a2,
    has_type_A env t1 TBool_A p1 a1 ->
    has_type_A env t2 TBool_A p2 a2 ->
    has_type_A env (tbin t1 t2) TBool_A (qor p1 p2) false
| t_sub_eff_A: forall env t T p a,
    has_type_A env t T p a ->
    has_type_A env t T p true
| t_sub_stp_A: forall env t T1 p a1 T2 a2,
    has_type_A env t T1 p a1 ->
    stp_A T1 T2 ->
    bsub a1 a2 ->
    has_type_A env t T2 p a2
.

Lemma ty_abs_app_A: forall G T1 T2 t1 t2 p1 p2 af a1 a2,
  has_type_A G t1 T1 p1 a1 ->
  has_type_A ((T1, a1)::G) t2 T2 p2 a2 ->
  env_cap_A G (qdiff p2 (qone (length G))) af -> 
  has_type_A G (tapp (tabs t2) t1) T2  (qor (qdiff p2 (qone (length G))) p1) a2.
Proof.
  intros.
  eapply t_app_A with (f := tabs t2) (t := t1) (p1 := p1) in H as A.
  2:{ eapply t_abs_A. eauto. eauto. rewrite qor_idempetic. eauto. }
  rewrite qor_idempetic in A. eauto.
Qed.

Lemma hast_A_fv: forall G t T p a,
    has_type_A G t T p a -> p = fv (length G) t.
Proof.
  intros. induction H; simpl; eauto.
  - rewrite IHhas_type_A1, IHhas_type_A2. eauto.
  - rewrite IHhas_type_A1, IHhas_type_A2. eauto.
  - rewrite H0, IHhas_type_A. simpl. eauto.
  - rewrite IHhas_type_A1, IHhas_type_A2. eauto.
Qed.

Lemma translate_envc: forall env pf af,
  env_cap_A env pf af ->
  env_cap (ttenv_A env) pf af.
Proof.
  intros. unfold env_cap_A in H. unfold env_cap.
  intros. assert (x < length env). { apply indexr_var_some' in H0. unfold ttenv_A in H0. rewrite map_length in H0. lia. }
  apply indexr_var_some in H2. destruct H2 as ((? & ?) & ?). 
  eapply indexr_map in H2 as H2'. unfold ttenv_A in H0. erewrite H0 in H2'. inversion H2'.
  subst. eapply H in H2; auto. destruct b; simpl; auto. 
Qed.

Lemma translate_SA: forall T1 T2,
  stp_A T1 T2 ->
  stp (tty_A T1) (tty_A T2).
Proof.
  intros. induction H.
  - simpl. eapply s_bool.
  - simpl. eapply s_ref.
  - simpl. eapply s_fun; eauto. unfold bsub; auto.
Qed.


Lemma translate_A': forall G t T p a,
    has_type_A G t T p a ->
    has_type (ttenv_A G) t (tty_A T) p a a true.
Proof.
  intros. induction H.
  - eauto. 
  - eauto.
  - assert (indexr x (ttenv_A env) = Some (tty_A T, a, a)). {
      unfold ttenv_A. erewrite indexr_map. 2: eauto. eauto. }
    eapply t_var in H0 as H2.
    destruct a; eauto.
  - eauto. 
  - eauto. 
  - eauto.
  - simpl in *.
    eapply t_app with (fr2 := a2)(frf := af)(ef := true)(e2 := true)(a2 := a2)(af := af)(fr1 := a1) in IHhas_type_A2 as HA.
    2: { eapply t_sub_stp. eapply IHhas_type_A1. eapply s_fun. eapply stp_id. eapply stp_id. all: unfold bsub; auto. }
    simpl in *.
    destruct a1,af,a2; simpl in *; eauto. 
  - simpl in *. eapply t_abs in IHhas_type_A as HA.
    3: eapply translate_envc; eauto. 2: { unfold ttenv_A. rewrite map_length. eauto. }
    destruct af; eauto.
  - eapply t_not in IHhas_type_A. 
    destruct a; auto. eapply t_sub_cap; eauto.
  - eauto.
  - eauto. 
  - eapply t_sub_stp. eauto. eapply translate_SA. auto. auto. auto. unfold bsub. auto.
Qed.


Lemma translate_A: forall G t T p a af,
    has_type_A G t T p a ->
    env_cap (ttenv_A G) p af ->
    has_type (ttenv_A G) t (tty_A T) p a (a&&af) af.
Proof.
  intros. eapply translate_A' in H. 
  eapply hast_strengthen in H; eauto.
Qed.

Corollary translate_A_pure: forall G t T p,
    has_type_A G t T p false -> (* syntactic purity in A: a = false, af = false *)
    env_cap (ttenv_A G) p false ->
    has_type (ttenv_A G) t (tty_A T) p false false false. (* pure in AE *)
Proof.
  intros. eapply translate_A in H; eauto.
Qed.

(* better semantic equivalence: e = locs(p) *)
Theorem fundamental_A: forall G t T p a,
    has_type_A G t T p a ->
    forall af,
      env_cap (ttenv_A G) p af ->
      sem_type (ttenv_A G) t t (tty_A T) (plift p) a (a&&af) af.
Proof.
  intros.
  eapply translate_A in H as H1; eauto.
  eapply fundamental in H1 as H2. eauto. 
Qed.


(* ---------- aux definitions and lemmas ---------- *)

(* syntactic typing of contexts *)
Inductive ctx_type_A : ctx -> tenv_A -> ty_A -> bool ->  bool -> tenv_A -> ty_A -> ql -> bool -> Prop :=
| c_hole_a: forall G T af a,
    ctx_type_A chole G T af a G T qempty a
| c_ref_a: forall Gh Th afh ah G t p a,
    ctx_type_A t Gh Th afh ah G TBool_A p a ->
    ctx_type_A (cref t) Gh Th afh ah G TRef_A p true  
| c_get_a: forall Gh Th afh ah G t p a,
    ctx_type_A t Gh Th afh ah G TRef_A p a ->
    ctx_type_A (cget t) Gh Th afh ah G TBool_A p false
| c_put1_a: forall Gh Th afh ah G t1 p1 a1 t2 p2 a2,
    ctx_type_A t1 Gh Th afh ah G TRef_A p1 a1  ->
    has_type_A G t2 TBool_A p2 a2  ->
    ctx_type_A (cput1 t1 t2) Gh Th afh ah G TBool_A (qor p1 p2) false 
| c_put2_a: forall Gh Th afh ah G t1 p1 a1 t2 p2 a2,
    has_type_A G t1 TRef_A p1 a1 ->
    ctx_type_A t2 Gh Th afh ah G TBool_A p2 a2  ->
    ctx_type_A (cput2 t1 t2) Gh Th afh ah G TBool_A (qor p1 p2) false 
| c_app1_a: forall Gh Th afh ah  G f t T1 T2 p1 p2 a1 af a2,
    ctx_type_A f Gh Th afh ah G (TFun_A T1 a1 T2 a2) p1 af ->
    has_type_A G t T1 p2 a1 ->
    ctx_type_A (capp1 f t) Gh Th afh ah G T2 (qor p1 p2) ((af||a1)|| a2)
| c_app2_a: forall Gh Th afh ah G f t T1 T2 p1 p2 a1 af a2,
    has_type_A G f (TFun_A T1 a1 T2 a2) p1 af ->
    ctx_type_A t Gh Th afh ah G T1 p2 a1 ->
    ctx_type_A (capp2 f t) Gh Th afh ah G T2 (qor p1 p2) ((af||a1)|| a2)
| c_abs_a: forall Gh Th afh ah G t T1 T2 p2 pf af a1 a2,
    ctx_type_A t Gh Th afh ah ((T1,a1)::G) T2 p2 a2  ->
    pf = (qdiff p2 (qone (length G))) ->
    env_cap (ttenv_A G) pf af ->
    ctx_type_A (cabs t) Gh Th afh ah G (TFun_A T1 a1 T2 a2) pf (af||afh)
| c_not_a: forall Gh Th afh ah G t p a,
    ctx_type_A t Gh Th afh ah G TBool_A p a -> 
    ctx_type_A (cnot t) Gh Th afh ah G TBool_A p a
| c_bin1_a: forall Gh Th afh ah G t1 p1 a1 t2 p2 a2,
    ctx_type_A t1 Gh Th afh ah G TBool_A p1 a1 ->
    has_type_A G t2 TBool_A p2 a2 ->
    ctx_type_A (cbin1 t1 t2) Gh Th afh ah G TBool_A (qor p1 p2) false 
| c_bin2_a: forall Gh Th afh ah G t1 p1 a1 t2 p2 a2,
    has_type_A G t1 TBool_A p1 a1 ->
    ctx_type_A t2 Gh Th afh ah G TBool_A p2 a2 ->
    ctx_type_A (cbin2 t1 t2) Gh Th afh ah G TBool_A (qor p1 p2) false
| c_sub_cap_a: forall Gh Th afh ah G t T p a,
    ctx_type_A t Gh Th afh ah G T p a ->
    ctx_type_A t Gh Th afh ah G T p true
| c_sub_stp_a: forall Gh Th afh ah G t T1 p a1 T2 a2,
    ctx_type_A t Gh Th afh ah G T1 p a1  ->
    stp_A T1 T2 ->
    bsub a1 a2 ->
    ctx_type_A t Gh Th afh ah G T2 p a2
.


Lemma translate_ctx_A: forall C Gh Th afh ah G T p a, 
  ctx_type_A C Gh Th afh ah G T p a ->
  ctx_type C (ttenv_A Gh) (tty_A Th) afh ah ah true (ttenv_A G) (tty_A T) p a a true.
Proof.
  intros. induction H.
  + eapply c_sub_eff. eapply c_hole.
  + eapply c_sub_cap. eapply c_sub_eff. eapply c_ref. eauto.
  + replace true with (true||true||a) at 2.
    eapply c_get. eauto. simpl. auto.
  + replace true with (true||true||a1) at 2.
    eapply c_put1. eauto. eapply translate_A in H0. eauto. 
    intros ? ? ? ? ? ?. unfold bsub. auto. auto.
  + replace true with (true||true||a1) at 2.
    eapply c_put2. eapply translate_A with (af := true) in H. destruct a1; eauto.
    intros ? ? ? ?. unfold bsub. auto.
    eapply IHctx_type_A. auto.
  + eapply c_app1 with (fr2 := a2)(frf := af)(ef := true)(e2 := true)(a2 := a2)(af := af)(fr1 := a1) in IHctx_type_A as HA.
    2: { eapply translate_A with (af := true) in H0. destruct a1; eauto. intros ? ? ? ?. unfold bsub; auto. }
    eapply c_sub_stp. eauto. eapply stp_id.
    all: unfold bsub. destruct af, a1, a2; simpl; auto. destruct af, a1, a2; simpl; auto. auto.
  + eapply c_app2 with (fr2 := a2)(frf := af)(ef := true)(e2 := true)(a2 := a2)(af := af)(fr1 := a1) in IHctx_type_A as HA.
    2: { eapply translate_A with (af := true) in H. destruct af; eauto. intros ? ? ? ?. unfold bsub; auto. }
    eapply c_sub_stp. eauto. eapply stp_id.
    all: unfold bsub. destruct af, a1, a2; simpl; auto. destruct af, a1, a2; simpl; auto. auto.
  + eapply c_sub_stp with (e1 := false)(fr1 := false). 
    eapply c_abs. eapply IHctx_type_A. unfold ttenv_A. rewrite map_length. auto. eauto.
    eapply s_fun. eapply stp_id. eapply stp_id.
    all: unfold bsub; simpl; auto. intuition.
  + eapply c_sub_stp. eapply c_not. eauto. eapply stp_id. all: unfold bsub; intuition.
  + replace true with (true||true) at 2. 2: auto.
    eapply c_bin1. eauto. eapply translate_A with (af := true) in H0. destruct a1; eauto.
    intros ? ? ? ?. unfold bsub; auto. 
  + replace true with (true||true) at 2. 2: auto.
    eapply c_bin2. eapply translate_A with (af := true) in H. destruct a1; eauto. 
    intros ? ? ? ?. unfold bsub; auto. eauto. 
  + eapply c_sub_fresh in IHctx_type_A. eapply c_sub_cap; eauto.
  + eapply c_sub_stp; eauto. eapply translate_SA. auto. unfold bsub. auto.
Qed.





(* ---------- contextual equivalence ---------- *)

(* contextual equivalence: no boolean context can detect a difference *)
Definition contextual_equiv_A G t1 t2 T1 (*p1*) af1 a1 :=
  forall C,
    ctx_type_A C G T1 (*p1*) af1 a1 [] TBool_A qempty false ->
    exists S1 S2 v,
      tevaln [] [] (plug C t1) S1 v /\
      tevaln [] [] (plug C t2) S2 v.

(* congruence: syntactic context typing implies semantic context typing *)
Theorem congr_A:
  forall C G1 T1 af1 a1 G2 T2 p2 a2,
    ctx_type_A C G1 T1 af1 a1 G2 T2 p2 a2 ->
    sem_ctx_type C C (ttenv_A G1) (tty_A T1) af1 a1 a1 true (ttenv_A G2) (tty_A T2) p2 a2 a2 true.
Proof.
  intros ? ? ? ? ? ? ? ? ? CX.
  eapply translate_ctx_A in CX. 
  eapply congr. eauto.
Qed.

Theorem soundness_A': forall G t1 t2 T p af a,
  p = (fv (length G) t1) ->
  p = (fv (length G) t2) ->
  env_cap (ttenv_A G) p af ->
  sem_type (ttenv_A G) t1 t2 (tty_A T) (plift p) a a true ->
  contextual_equiv_A G t1 t2 T af a.
Proof.
  intros. intros ? ?.
  eapply adequacy.
  eapply congr_A in H3. eapply H3;eauto.
  unfold ttenv_A. rewrite map_length. rewrite <-H. rewrite <-H0. unfoldq; intuition.
  unfold ttenv_A. rewrite map_length. rewrite <-H. rewrite plift_or. rewrite por_same. auto.
  unfold ttenv_A. rewrite map_length. rewrite <-H. rewrite qor_idempetic. auto.
Qed.

(* soundness of binary logical relation: implies contextual equivalence *)
Theorem soundness_A: forall G t1 t2 T p af a,
  has_type_A G t1 T p a ->
  has_type_A G t2 T p a ->
  env_cap (ttenv_A G) p af ->
  sem_type (ttenv_A G) t1 t2 (tty_A T) (plift p) a a true ->
  contextual_equiv_A G t1 t2 T af a.
Proof.
  intros.
  eapply soundness_A'.  3: eauto. 
  eapply translate_A in H as H'. eapply hast_fv in H'. unfold ttenv_A in H'. rewrite map_length in H'. eapply H'.
  eauto.
  eapply translate_A in H0 as H''. eapply hast_fv in H''. unfold ttenv_A in H''. rewrite map_length in H''. eapply H''.
  eauto.
  eauto.
Qed.  


(* soudness of purity: a syntactically pure term is semantically pure *)
Theorem soundness_of_purity_A: forall t1 G T1 pt1,
    has_type_A G t1 T1 pt1 false -> (* fr1 = false and e1 = false: syntactic purity! *)    
    env_cap (ttenv_A G) pt1 false ->
    contextual_purity (ttenv_A G) t1 (tty_A T1) false. 
Proof.
  intros.
  eapply translate_A in H; eauto. 
  eapply soundness_of_purity. simpl in *. eauto.
Qed.

Theorem reorder_tbin_A: forall G t1 p1 t2 p2,
  has_type_A G t1 TBool_A p1 false ->
  has_type_A G t2 TBool_A p2 false ->
  env_cap (ttenv_A G) p1 false ->
  env_cap (ttenv_A G) p2 false ->
  sem_type (ttenv_A G) (tbin t1 t2) (tbin t2 t1) TBool (por (plift p1) (plift p2)) false false false.
Proof.
  intros.
  eapply translate_A in H; eauto. 
  eapply translate_A in H0; eauto.
  simpl in *.
  eapply reorder_tbin_mention; eauto.
Qed. 

Lemma tbin_inversion1: forall env t T p
  (W: has_type_A env t T p false),
  forall t1 t2,
    t = tbin t1 t2 ->
    T = TBool_A ->
  exists p1 a1, 
    psub (plift p1) (plift p) /\ 
    has_type_A env t1 TBool_A p1 a1.
Proof.
  intros env t T p W. 
  induction W; intros.
  - inversion H.
  - inversion H.
  - inversion H0.
  - inversion H.
  - inversion H.
  - inversion H.
  - inversion H.
  - inversion H1.
  - inversion H.
  - inversion H. subst t0 t3.
    exists p1. exists a1.
    split. 
    -- rewrite plift_or. unfoldq; intuition.
    -- auto.
  - eapply IHW in H; auto.
  - eapply IHW in H1; auto.
    subst T2. inversion H. auto.
Qed. 

Lemma tbin_inversion2: forall env t T p
  (W: has_type_A env t T p false),
  forall t1 t2,
    t = tbin t1 t2 ->
    T = TBool_A ->
  exists p2 a2, 
    psub (plift p2) (plift p) /\ 
    has_type_A env t2 TBool_A p2 a2.
Proof.
  intros env t T p W. 
  induction W; intros.
  - inversion H.
  - inversion H.
  - inversion H0.
  - inversion H.
  - inversion H.
  - inversion H.
  - inversion H.
  - inversion H1.
  - inversion H.
  - inversion H. subst t0 t3.
    exists p2, a2.
    split. 
    -- rewrite plift_or. unfoldq; intuition.
    -- auto.
  - eapply IHW in H; auto.
  - eapply IHW in H1; auto.
    subst T2. inversion H. auto.
Qed. 

