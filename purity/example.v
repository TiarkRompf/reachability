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

Import STLC.

(* utils from stp file *)
Lemma qif_false: forall q,
    qif false q = qempty.
Proof.
  unfold qif. eauto with bool.
Qed.

Lemma qif_true: forall q,
    qif true q = q.
Proof.
  unfold qif. eauto with bool.
Qed.

Lemma qor_empty: forall q,
    qor q qempty = q.
Proof.
  unfold qor, qempty.
  intros. eapply functional_extensionality.
  intros. eauto with bool.
Qed.

Lemma qor_emptyl: forall q,
    qor qempty q = q.
Proof.
  unfold qor, qempty.
  intros. eapply functional_extensionality.
  intros. eauto with bool.
Qed.

Lemma qor_comm: forall q q',
    qor q q' = qor q' q.
Proof.
  unfold qor, qempty.
  intros. eapply functional_extensionality.
  intros. eauto with bool.
Qed.

Lemma qand_same: forall q,
    qand q q = q.
Proof.
  unfold qand.
  intros. eapply functional_extensionality.
  intros. destruct (q x); eauto.
Qed.

Lemma qand_sub: forall a p,
    psub (plift a) (plift p) ->
    qand p a = a.
Proof.
  unfold qand.
  intros. eapply functional_extensionality.
  intros. remember (a x) as A. destruct A.
  unfoldq. rewrite H. eauto. unfold plift. eauto.
  eauto with bool.
Qed.

Lemma qand_or_dist: forall a b c,
    qand (qor a b) c = (qor (qand a c) (qand b c)).
Proof.
  unfold qand, qor.
  intros. eapply functional_extensionality.
  intros. destruct (a x), (b x), (c ); eauto with bool.
Qed.

Ltac qsimpl :=
  repeat (try rewrite qif_false;
          try rewrite qif_true;
          try rewrite qor_empty;
          try rewrite qor_emptyl;
          try rewrite qand_same;
          try rewrite qand_or_dist;
          try (rewrite qand_sub; [|assumption])).

Ltac plift_any :=
  repeat (
          try rewrite plift_or in *;
          try rewrite plift_and in *;
          try rewrite plift_if in *;
          try rewrite plift_diff in *;
          try rewrite plift_one in *;
          try rewrite plift_empty in *).

Ltac crush :=
  qsimpl; plift_any; unfoldq; intuition.

(* general reflection proof principle *)
Lemma plift_qual_eq: forall q1 q2,
    (q1 = q2) = (plift q1 = plift q2).
  intros. eapply propositional_extensionality.
  remember (plift q1) as p1.
  remember (plift q2) as p2. 
  unfold plift in *. intuition.
  - subst. eauto.
  - eapply functional_extensionality. intros.
    remember (q1 x) as qx1. symmetry in Heqqx1.
    remember (q2 x) as qx2. symmetry in Heqqx2.
    destruct qx1; destruct qx2; try reflexivity.
    + replace (q1 x = true) with (p1 x) in *.
      rewrite H in Heqqx1. subst p2. eauto. subst p1. eauto. 
    + replace (q2 x = true) with (p2 x) in *. 
      rewrite <-H in Heqqx2. subst p1. eauto. subst p2. eauto.
Qed.

(* pure term; pure function; pure ability *)
Definition TFun_id := TFun TBool false false TBool false false false.

Lemma ty_id: forall G,
  has_type G (tabs (tvar (length G))) TFun_id qempty false false false.
Proof. 
  intros.
  replace false with ((false||false)&&false) at 2.  
  eapply t_abs. 
  replace false with (false||false) at 4. eapply t_var.
  rewrite indexr_head. auto. 
  all: crush.
  rewrite plift_qual_eq. rewrite plift_diff, plift_one. 
  eapply functional_extensionality; intros. eapply propositional_extensionality. unfoldq; intuition.
  intros ?. intros. unfoldq; intuition.
Qed.



(* (\lambda x. x)(true) *)
Lemma ty_idapp: forall G,
  has_type G (tapp (tabs (tvar (length G))) (ttrue)) TBool qempty false false false.
Proof.
  intros.
   
  replace (qempty) with (qor qempty qempty).
  replace false with (false || false || (false || false)&&false) at 3.
  replace false with ((false||false)&&false) at 2.
  replace false with (((false||false)&&false)||false) at 1.
  eapply t_app with (f := (tabs (tvar (length G)))) (t := ttrue)(p1 := qempty)
                    (p2 := qempty).
  all: crush. eapply ty_id. 
Qed.

Lemma sem_idapp: forall G,
  sem_type G (tabs (tvar (length G))) (tabs (tvar (length G)))  TFun_id pempty false false false ->
  sem_type G (tapp (tabs (tvar (length G)))(ttrue)) (tapp (tabs (tvar (length G)))(ttrue)) TBool pempty false false false.
Proof.
  intros.
  intros u E. unfold bsub in *.
  intros M H1 H2 V1 V2 WFE STW ? ? ? ? ST P1 P2.

  replace false with (false || false || (false || false)&&false) at 3.
  replace false with ((false||false)&&false) at 2.
  replace false with (((false||false)&&false)||false) at 1.
 
  destruct u. { 
    (* use *)
    
    edestruct H as (S1' & S2' & M' & HEF); eauto.
    unfold TFun_id in HEF.
    assert (exp_type S1' S2' M' H1 H2 V1 V2 (ttrue) (ttrue) TBool
          true 
          (por p1 (pdiff (pdom S1') (pdom S1)))
          (por p2 (pdiff (pdom S2') (pdom S2))) 
          false false false). {
        destruct HEF as (? & ? & ? & ? & ? & ? & ? & ?). 
        intuition.  
        eapply exp_true. auto. auto.
   }
   eapply exp_app with (f1 := (tabs (tvar (length G)))) (t1 := ttrue)
                       (f2 := (tabs (tvar (length G)))) (t2 := ttrue).
  all: auto. eapply HEF. auto.
    
  } {
    (* mention *)
    edestruct H as (S1' & S2' & M' & HEF); eauto.
    unfold TFun_id in HEF.
    assert (exp_type S1' S2' M' H1 H2 V1 V2 (ttrue) (ttrue) TBool
          true 
          (por p1 (pdiff (pdom S1') (pdom S1)))
          (por p2 (pdiff (pdom S2') (pdom S2))) 
          false false false). {
        destruct HEF as (? & ? & ? & ? & ? & ? & ? & ?). 
        intuition.  
        eapply exp_true. auto. auto.
    }
    eapply exp_app with (f1 := (tabs (tvar (length G)))) (t1 := ttrue)
                       (f2 := (tabs (tvar (length G)))) (t2 := ttrue).
    all: auto. eapply HEF. auto.
    
  }
  all: crush.
Qed. 

(* upcast the effect to true *)
(* u is forced to be true *)
Lemma sem_idapp_upcast_eff: forall G,
  sem_type G (tabs (tvar (length G))) (tabs (tvar (length G))) TFun_id pempty false false false ->
  sem_type G (tapp (tabs (tvar (length G)))(ttrue)) 
             (tapp (tabs (tvar (length G)))(ttrue)) TBool pempty false false true.
Proof.
  intros. intros u E M H1 H2 ? ? WFE STW ? ? ? ? ST P1 P2.
  unfold bsub in E.
  rewrite E in *; auto.
  eapply H in WFE as A. 2: { unfold bsub. intuition. } 

  replace true with (true || false || (false || false)&&false) at 2.
  replace false with ((false||false)&&false) at 2.
  replace false with (((false||false)&&false)||false) at 1.

  edestruct (H true) as (S1' & S2' & M' & HEF). 
  unfold bsub. auto.

  eauto. eauto. eauto.
  unfoldq; intuition.
  unfoldq; intuition.
  unfold TFun_id in HEF.

  
  assert (exp_type S1' S2' M' H1 H2 V1 V2 (ttrue) (ttrue) TBool
          false 
          (por p1 (pdiff (pdom S1') (pdom S1)))
          (por p2 (pdiff (pdom S2') (pdom S2))) 
          false false true). {
        destruct HEF as (? & ? & ? & ? & ? & ? & ? & ?). 
        intuition.
        eapply exp_sub_eff; eauto.  
        eapply exp_true. auto. auto.
   }
  
  eapply exp_app with (f1 := (tabs (tvar (length G)))) (t1 := ttrue)
                      (f2 := (tabs (tvar (length G)))) (t2 := ttrue).
  all: auto. eapply HEF. auto.
  unfold bsub. intuition.
Qed.

Definition TFun_id_ref := TFun TRef true false TRef false true false.
(* (lambda x. x) (new ref ttrue) *)
Lemma ty_idapp_ref: forall G,
  has_type ((TRef, true, false):: G) (tapp (tabs (tvar (length G+1))) (tref ttrue)) TRef qempty true false false.
Proof.
  intros. 
  assert (has_type ((TRef, true, false):: G) (tabs (tvar (length G+1))) TFun_id_ref qempty false false false ). {
    replace false with ((false||true)&&false) at 3.
    eapply t_abs.
    replace true with (true || false) at 3.
    eapply t_var. replace (length G + 1) with (length ((TRef, true, false)::G)). rewrite indexr_head. auto.
    all: crush. simpl. lia.
    rewrite plift_qual_eq. rewrite plift_diff, plift_one. rewrite plift_one. simpl. 
    replace (length G+1) with (S (length G)). rewrite pdiff_same. rewrite plift_empty. auto.
    lia.
    intros ? ? ? ? ?. unfoldq; intuition.
  } 
  replace (qempty) with (qor qempty qempty).
  replace false with (false || false || (false || false)&&false) at 3. (* effs*)
  replace false with ((false||false)&&true) at 2.
  replace true with (((false||true)&&true)||false) at 2.
  eapply t_app. eauto.
  all: crush. simpl. eauto.
Qed.

Lemma sem_idapp_ref: forall G,
  sem_type ((TRef, true, false):: G) (tabs (tvar (length G))) (tabs (tvar (length G))) TFun_id_ref pempty false false false ->
  sem_type ((TRef, true, false):: G) (tapp (tabs (tvar (length G)))(tref ttrue)) 
                            (tapp (tabs (tvar (length G)))(tref ttrue)) 
                            TRef pempty true false false.
Proof.
  intros. intros u E. unfold bsub in E. 
  intros M H1 H2 ? ? WFE STW ? ? ? ? ST P1 P2.
  replace false with (false || false || (false || false)&&false) at 2.
  replace false with ((false||false)&&true) at 1.
  replace true with (((false||true)&&true)||false) at 1.
  destruct u. {
    (* use *)
    edestruct H as (S1' & S2' & M' & HEF).  
    unfold bsub. eapply E.
    eapply WFE. auto. eauto.
    unfoldq; intuition.
    unfoldq; intuition.

    assert (exp_type S1' S2' M' H1 H2 V1 V2 (tref ttrue) (tref ttrue) TRef
            true 
            (por p1 (pdiff (pdom S1') (pdom S1)))
            (por p2 (pdiff (pdom S2') (pdom S2))) 
            true false false). {
          destruct HEF as (? & ? & ? & ? & ? & ? & ? & ?). 
          intuition.  
          eapply exp_ref. eapply exp_true. auto. auto.
     }


    eapply exp_app with (f1 := (tabs (tvar (length G)))) (t1 := tref ttrue)
                        (f2 := (tabs (tvar (length G)))) (t2 := tref ttrue).
    all: auto. eapply HEF. auto.
  }{
    (* mention *)
    edestruct H as (S1' & S2' & M' & HEF).  
    unfold bsub. eapply E.
    eapply WFE. auto. eauto.
    unfoldq; intuition.
    unfoldq; intuition.

    assert (exp_type S1' S2' M' H1 H2 V1 V2 (tref ttrue) (tref ttrue) TRef
            true 
            (por p1 (pdiff (pdom S1') (pdom S1)))
            (por p2 (pdiff (pdom S2') (pdom S2))) 
            true false false). {
          destruct HEF as (? & ? & ? & ? & ? & ? & ? & ?). 
          intuition.  
          eapply exp_ref. eapply exp_true. auto. auto.
     }


    eapply exp_app with (f1 := (tabs (tvar (length G)))) (t1 := tref ttrue)
                        (f2 := (tabs (tvar (length G)))) (t2 := tref ttrue).
    all: auto. eapply HEF. auto.
  }
  all: crush.
Qed.

(* (lambda x. x) (a) *)
Lemma ty_idapp_ref_test: forall G,
  has_type ((TRef, true, false):: G) (tapp (tabs (tvar (length G+1))) (tvar (length G))) TRef (qone (length G)) false true false.
Proof.
  intros.
  replace (qone (length G)) with (qor (qempty) (qone (length G))).
  replace false with (false||false|| (false||true)&&false) at 3. (* effs *)
  replace true with ((false||true)&&true) at 2. (* ability *)
  replace false with ((false||false)&&true || false) at 2. (* fresh*)
  eapply t_app. replace false with ((false||true)&&false) at 6.
  eapply t_abs. replace true with (false||true) at 3.
  eapply t_var. replace (length G+1) with (length ((TRef, true,false) :: G)).
  rewrite indexr_head. eauto.
  simpl. lia. all: crush.
  simpl. replace (length G+1) with (S(length G)). rewrite plift_qual_eq. rewrite plift_empty, plift_diff. rewrite pdiff_same. auto.
  lia.

  intros ?. intros. unfoldq; intuition.

  replace true with (true || false) at 2. 
  eapply t_var. rewrite indexr_head. auto. crush.
Qed.


Definition TFun_Alloc := TFun TBool false false TRef true false false.
(* (lambda x. ref x)  *)
Lemma ty_TFun_Alloc: forall G,
  has_type ((TRef, true, false) ::G) (tabs (tref (tvar (length G + 1))))  TFun_Alloc qempty false false false.
Proof.
  intros.
  replace false with ((false||false)&&false) at 3.
  eapply t_abs. 
  eapply t_ref with (a := false). 
  replace false with (false||false) at 4.
  eapply t_var. replace (length G+1) with (length ((TRef, true, false) :: G)).
  rewrite indexr_head. auto. 
  all: crush.
  simpl. lia.
  rewrite plift_qual_eq. rewrite plift_empty, plift_diff, plift_one, plift_one.
  replace (length G+1) with (length ((TRef, true, false) :: G)).
  rewrite pdiff_same. auto. simpl. lia.
  intros ? ? ? ? ? ?. unfoldq; intuition.
Qed. 

Definition TFun_Leak := TFun TBool false false TRef false true false.

(* \lambda x. a *)
Lemma ty_TFun_Leak: forall G,
  has_type ((TRef, true, false) ::G) (tabs (tvar (length G)))  TFun_Leak (qone (length G)) false true false.
Proof.
  intros.
  replace true with ((false||true)&& true) at 2.
  eapply t_abs. replace true with (true||false) at 2.
  eapply t_var. rewrite indexr_skip. rewrite indexr_head. auto. simpl. lia.
  all: crush.
  rewrite plift_qual_eq. rewrite plift_diff, plift_one, plift_one. simpl.
  eapply functional_extensionality. intros. eapply propositional_extensionality. split; unfoldq; intuition.

  intros ??????. assert (x = length G). { unfold qone in H0. bdestruct (x =? length G); intuition. }
  subst x. rewrite indexr_head in H. inversion H. unfold bsub. auto.
Qed.

Definition TFun_NotUseArg := TFun TRef false false TBool false false true. (* cannot make a call on it *)
(* def use (z: Ref Bool)= { !y } in the context  y: (TRef, true, false) *)
Lemma ty_fun_notusearg: forall G,
  has_type ((TRef, true, false):: G) (tabs (tget (tvar (length G)))) TFun_NotUseArg (qone (length G)) false true false.
Proof.
  intros.
  replace true with ((true||false)&& true) at 2.
  eapply t_abs. replace true with (false||true) at 2.
  eapply t_get. replace true with (true||false) at 2.
  eapply t_var. rewrite indexr_skip. rewrite indexr_head. auto. simpl. lia.
  all: crush.
  rewrite plift_qual_eq. rewrite plift_diff, plift_one, plift_one. simpl.
  eapply functional_extensionality. intros. eapply propositional_extensionality. split; unfoldq; intuition.

  intros ??????. assert (x = length G). { unfold qone in H0. bdestruct (x =? length G); intuition. }
  subst x. rewrite indexr_head in H. inversion H. unfold bsub. auto.
Qed.

Definition TFun_Use := TFun TRef true false TBool false false true. 
(* def use (z: Ref Bool)= { !y } in the context  y: (TRef, true, false) *)
Lemma ty_fun_use: forall G,
  has_type ((TRef, true, false):: G) (tabs (tget (tvar (length G)))) TFun_Use (qone (length G)) false true false.
Proof.
  intros.
  replace true with ((true||false)&& true) at 2.
  eapply t_abs. replace true with (false||true) at 3.
  eapply t_get. replace true with (true||false) at 3.
  eapply t_var. rewrite indexr_skip. rewrite indexr_head. auto. simpl. lia.
  all: crush.
  rewrite plift_qual_eq. rewrite plift_diff, plift_one, plift_one. simpl.
  eapply functional_extensionality. intros. eapply propositional_extensionality. split; unfoldq; intuition.

  intros ??????. assert (x = length G). { unfold qone in H0. bdestruct (x =? length G); intuition. }
  subst x. rewrite indexr_head in H. inversion H. unfold bsub. auto.
Qed.

Definition TFun_UseArg := TFun TRef false true TBool false false true.

(* def use (z: Ref Bool)= { !z } in the context  y: (TRef, true, false) *)
Lemma ty_fun_usearg: forall G,
  has_type ((TRef, true, false):: G) (tabs (tget (tvar (length G+1)))) TFun_UseArg qempty false false false.
Proof. 
  intros.
  replace false with ((true||false)&&false) at 3.  
  eapply t_abs.
  replace true with (false || true) at 3.
  eapply t_get.
  replace true with (false||true) at 3.
  
  eapply t_var. replace (length G+1) with (length ((TRef, true,  false) :: G)). rewrite indexr_head. auto.
  all: crush. simpl in *. lia. 
  rewrite plift_qual_eq. rewrite plift_diff, plift_one. rewrite plift_one. simpl. 
  replace (length G+1) with (S (length G)). rewrite pdiff_same. rewrite plift_empty. auto.
  lia.
  
  intros ? ? ? ? ?. unfoldq; intuition.
Qed.



(* def use (z: Ref Bool)= { !z } in the context  y: (TRef, true, false) 
   z (y)
*)
Lemma ty_fun_usearg_app: forall G,
  has_type ((TRef, true, false)::G) (tapp (tabs (tget (tvar (length G+1)))) (tvar (length G))) TBool (qone (length G)) false false true.
Proof.
  intros.
  (*
  a1: true
  *)
 
  replace (qone (length G)) with (qor (qempty) (qone (length G))).
  replace true with (false || false || (false || true)&&true) at 2. (* effs *)
  replace false with ((false||true)&&false) at 3. (* ability *)
  replace false with (((false||false)&&false)||false) at 2. (* freshness *)
  eapply t_app. 
  all: crush. fold TFun_UseArg. eapply ty_fun_usearg.
  replace true with (true||false) at 2.
  eapply t_var. rewrite indexr_head. auto. auto.
Qed.

Lemma sem_fun_usearg_app: forall G,
  sem_type ((TRef, true, false):: G) (tabs (tget (tvar (length G+1)))) 
                                     (tabs (tget (tvar (length G+1)))) TFun_UseArg pempty false false false ->
  sem_type ((TRef, true, false):: G) (tapp (tabs (tget (tvar (length G+1)))) (tvar (length G)))
                                     (tapp (tabs (tget (tvar (length G+1)))) (tvar (length G))) 
                            TBool (pone (length G)) false false true.
Proof.
  intros. intros u E. unfold bsub in E. rewrite E in *; auto. 
  intros M H1 H2 ? ? WFE STW ? ? ? ? ST P1 P2.
  replace true with (false || false || (false || true)&&true) at 2.
  replace false with ((false||true)&&false) at 2.
  replace false with (((false||true)&&false)||false) at 1.

  (* mention mode for function *)
  edestruct (H false) as (S1' & S2' & M' & HEF). unfold sem_type_genericV in H. 
  unfold bsub. auto.
  eapply envt_tighten. eapply envt_strengthenW1. rewrite <-plift_one in WFE. eauto. unfoldq; intuition.
  auto. eauto.
  unfoldq; intuition.
  unfoldq; intuition.

  assert (exp_type1 S1 S2 M H1 H2 V1 V2 
            (tabs (tget (tvar (length G + 1))))
            (tabs (tget (tvar (length G + 1))))
             S1' S2' M' TFun_UseArg true p1 p2 false false false) as HEF'. {
    eapply exp_mentionable with (uv := true). eauto.
    intuition. intuition.
  }
  
  (* making it usalbe *)
  assert (exp_type S1' S2' M' H1 H2 V1 V2 (tvar (length G)) (tvar (length G)) TRef
            true 
            (por p1 (pdiff (pdom S1') (pdom S1)))
            (por p2 (pdiff (pdom S2') (pdom S2))) 
            false (true||false) false). {
          destruct WFE as (LH1 & LH2 & LV1 & LV2 & ? & W).
          edestruct (W (length G)) as (v1 & v2 & ux & ls1 & ls2 & ?).
          rewrite indexr_head. eauto. intuition.
          destruct HEF as (? & ? & ? & ? & ? & ? & ? & ?). 
          intuition.  
          eapply exp_var; eauto. simpl in H8, H25. subst ux x1. 
          eapply valt_store_change. eapply H9. unfoldq; intuition.
          intros ??????. rewrite H33. auto.
          destruct ST. destruct H23. lia.
          destruct ST. destruct H23. lia.
          intuition. intuition.
     }


    eapply exp_app with (f1 := (tabs (tget (tvar (length G+1))))) (t1 := (tvar (length G)))
                        (f2 := (tabs (tget (tvar (length G+1))))) (t2 := (tvar (length G))).
    all: auto. eapply HEF'. simpl in H0. eapply exp_sub_fresh; eauto.
    destruct HEF' as (v1  & v2 & uv & ls1 & ls2 & ? & ? & ?). auto.
    destruct HEF' as (v1  & v2 & uv & ls1 & ls2 & ? & ? & ? & ? & ? & ? & ? & ?). auto.
    unfold bsub. intuition. 
Qed.

Definition TFun_Mention := TFun TRef false true TBool false false false.

(* \lambda x. true *)
Lemma ty_fun_mention_inner1: forall G,
  has_type ((TRef, false, true) :: (TRef, false, true):: G) (tabs ttrue) TFun_Mention qempty false false false.
Proof. 
  intros. replace false with ((false||false)&&false) at 4.
  eapply t_abs. eapply t_true. 
  simpl. rewrite plift_qual_eq. rewrite plift_diff, plift_one, plift_empty. 
  eapply functional_extensionality; intros. eapply propositional_extensionality. unfoldq; intuition.

  intros ?. intros. unfoldq; intuition.
  crush.
Qed.

(* (\lambda x. true ) a *)
Lemma ty_fun_mention_inner2: forall G,
  has_type ((TRef, false, true):: (TRef, false, true):: G) (tapp (tabs ttrue) (tvar (length G))) TBool (qone (length G)) false false false.
Proof.
  intros.
  replace (qone (length G)) with (qor qempty (qone (length G))).
  replace false with (false||false|| (false ||true)&&false) at 5. (* effs *)
  replace false with ((false||true)&&false) at 4.  (* ability *)
  replace false with ((false||false)&&false || false) at 3.

  eapply t_app. eapply ty_fun_mention_inner1.
  replace true with (false||true) at 3. eapply t_var. rewrite indexr_skip. rewrite indexr_head. auto.
  all: crush. simpl in *. lia.
Qed.

(* (lambda y. ((\lambda x. true ) a) *)
Lemma ty_fun_mention: forall G,
  has_type ((TRef, false, true):: G) (tabs (tapp (tabs ttrue) (tvar (length G)))) TFun_Mention (qone (length G)) false false false.
Proof.
  intros. 
  replace false with ((false||false)&&true) at 3.
  eapply t_abs. eapply ty_fun_mention_inner2. 
  simpl. rewrite plift_qual_eq. rewrite plift_diff, plift_one, plift_one. 
  eapply functional_extensionality; intros. eapply propositional_extensionality. unfoldq; intuition.

  intros ?. intros. assert (x = length G). { unfold qone in H0. bdestruct (x =? length G); intuition. } 
  subst x. rewrite indexr_head in H. inversion H. subst. unfold bsub. auto. 
  crush.
Qed.

Definition TFun_MentionX := TFun TRef false false TBool false false false.

(* \lambda x. true *)
Lemma ty_fun_mention_inner1X: forall G,
  has_type ((TRef, false, false) :: (TRef, false, false):: G) (tabs ttrue) TFun_MentionX qempty false false false.
Proof. 
  intros. replace false with ((false||false)&&false) at 6.
  eapply t_abs. eapply t_true. 
  simpl. rewrite plift_qual_eq. rewrite plift_diff, plift_one, plift_empty. 
  eapply functional_extensionality; intros. eapply propositional_extensionality. unfoldq; intuition.

  intros ?. intros. unfoldq; intuition.
  crush.
Qed.

(* (\lambda x. true ) a *)
Lemma ty_fun_mention_inner2X: forall G,
  has_type ((TRef, false, false):: (TRef, false, false):: G) (tapp (tabs ttrue) (tvar (length G))) TBool (qone (length G)) false false false.
Proof.
  intros.
  replace (qone (length G)) with (qor qempty (qone (length G))).
  replace false with (false||false|| (false ||false)&&false) at 7. (* effs *)
  replace false with ((false||false)&&false) at 6.  (* ability *)
  replace false with ((false||false)&&false || false) at 5.

  eapply t_app. eapply ty_fun_mention_inner1X.
  replace false with (false||false) at 6. eapply t_var. rewrite indexr_skip. rewrite indexr_head. auto.
  all: crush. simpl in *. lia.
Qed.

(* (lambda y. ((\lambda x. true ) a) *)
Lemma ty_fun_mentionX: forall G,
  has_type ((TRef, false, false):: G) (tabs (tapp (tabs ttrue) (tvar (length G)))) TFun_MentionX (qone (length G)) false false false.
Proof.
  intros. 
  replace false with ((false||false)&&false) at 4.
  eapply t_abs. eapply ty_fun_mention_inner2X. 
  simpl. rewrite plift_qual_eq. rewrite plift_diff, plift_one, plift_one. 
  eapply functional_extensionality; intros. eapply propositional_extensionality. unfoldq; intuition.

  intros ?. intros. assert (x = length G). { unfold qone in H0. bdestruct (x =? length G); intuition. } 
  subst x. rewrite indexr_head in H. inversion H. subst. unfold bsub. auto. 
  crush.
Qed.


Definition TFun_Use_Arg_Mask := TFun TRef true false TBool false false true.

Lemma ty_fun_mask: forall G,
  has_type ((TRef, true, false):: G) (tabs (tget (tvar (length G+1)))) TFun_Use_Arg_Mask qempty false false false.
Proof.
  intros.  replace false with ((true||false)&&false) at 3.
  eapply t_abs.  replace (true) with (false||true) at 3.
  eapply t_get. replace true with (true||false) at 3.
  eapply t_var. replace (length G+1) with (length ((TRef, true, false) :: G)). rewrite indexr_head. auto.
  all: crush. simpl. lia.
  rewrite plift_qual_eq. rewrite plift_diff, plift_one. rewrite plift_one. 
  eapply functional_extensionality; intros. eapply propositional_extensionality. unfoldq; intuition.
  simpl in *. lia.

  intros ?. intros. unfoldq; intuition.
Qed.

Lemma ty_fun_mask_app: forall G,
  has_type ((TRef, true, false)::G) (tapp (tabs (tget (tvar (length G+1)))) (tref ttrue)) TBool qempty false false false.
Proof.
  intros.
  (*
  a1: true
  *)
 
  replace qempty with (qor qempty qempty).
  replace false with (false || false || (false || false)&&true) at 4. (* effs *)
  replace false with ((false||false)&&false) at 3. (* ability *)
  replace false with (((false||true)&&false)||false) at 2. (* freshness *)
  eapply t_app. 
  all: crush. eapply ty_fun_mask.
  eapply t_ref. eauto.
Qed.

Definition TFun_CAPTURE := TFun TRef true false TFun_NotUseArg false true false.

(* \lambda x. \lambda y. !a *)
Lemma ty_fun_capture: forall G,
  has_type ((TRef, true, false)::G) (tabs (tabs (tget (tvar (length G))))) (TFun TRef true false TFun_Use false true false) (qone (length G)) false true false.
Proof.
  intros.
  replace true with ((false||true) && true) at 4.
  eapply t_abs. replace true with ((true||false)&& true) at 3.
  eapply t_abs. replace true with (false||true) at 4.
  eapply t_get. replace true with (true||false) at 4.
  eapply t_var. rewrite indexr_skip. rewrite indexr_skip. rewrite indexr_head. auto.
  all: crush. simpl in *. lia. simpl in *. lia.

  intros ?. intros. unfold qdiff, qone in H0. simpl in H0. bdestruct (x =? length G); intuition. 
  bdestruct (x =? (S (S (length G)))); intuition. subst x.
  rewrite indexr_skip in H. rewrite indexr_head in H. inversion H. 
  unfold bsub. auto. simpl. lia.
  
  rewrite plift_qual_eq. rewrite plift_one, plift_diff, plift_diff, plift_one, plift_one, plift_one.
  eapply functional_extensionality. intros. eapply propositional_extensionality. split; intros; unfoldq; intuition.
  simpl in H0. lia. simpl in H0. lia.

  intros ?. intros. assert (x = length G). { unfold qone in H0. bdestruct (x =? length G); intuition. }
  subst x. rewrite indexr_head in H. inversion H. unfold bsub. intuition.
Qed.
 
(* lambda f. \lambda x. f x *)
Lemma ty_fun_poly: forall G,
  has_type ((TRef, true, false)::G) (tabs (tabs (tapp (tvar (length G+1))(tvar (length G+2))))) (TFun TFun_id false false TFun_id false false false) qempty false false false.
Proof.
  intros.
  replace false with ((false||false)&&false) at 8.
  eapply t_abs with (p2 := qone (length G+1)). replace false with ((false||false)&&false) at 5.
  eapply t_abs with (p2 := (qor (qone (length G+1))(qone (length G+2)))).
  replace false with (false||false||(false||false)&&false) at 8. (* effs *)
  replace false with ((false||false)&&false) at 7.
  replace false with ((false||false)&&false || false) at 6.
  eapply t_app. replace false with (false||false) at 12.
  eapply t_var. replace (length G+1) with (length ((TRef, true, false) :: G)).
  rewrite indexr_skip. rewrite indexr_head. unfold TFun_id. eauto.
  simpl. lia. simpl. lia.
  all: crush.
  
  replace false with (false||false) at 7.
  eapply t_var. replace (length G+2) with (length ((TFun_id, false, false) :: (TRef, true, false) :: G)).
  rewrite indexr_head. auto. simpl. lia. auto.
  
  rewrite plift_qual_eq. rewrite plift_diff, plift_or. rewrite plift_one, plift_one, plift_one.
  eapply functional_extensionality. intros. eapply propositional_extensionality. split; intros; unfoldq; intuition.
  simpl in *. lia. simpl in *. lia.

  intros ?. intros. assert (x = length ((TRef, true, false) :: G)). { unfold qone in H0. bdestruct (x =? length G+1); intuition. simpl. lia. }
  subst x. rewrite indexr_head in H. inversion H. unfold bsub. intuition.
  simpl. replace (length G+1) with (S (length G)).
  rewrite plift_qual_eq. rewrite plift_empty, plift_diff. rewrite pdiff_same. auto. lia.
  
  intros ?. intros. unfoldq; intuition.
Qed.
