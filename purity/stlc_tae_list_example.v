(*******************************************************************************
* Coq mechanization of the simply typed calculus with first-order mutable store (the λ$_{ae}$-calculus).
* - Syntactic definitions
* - Semantic definitions
* - Metatheory
*******************************************************************************)


(* Full safety for STLC *)


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
Require Import stlc_tae_list.

Import STLC.


(* fold (x0,a1 => x0 && a1) false [true; false; true] *)
Definition ex_fold_or (n:nat): tm :=
  tfold
    (tbin (tvar (n)) (tvar (S (n))))
    tfalse
    (tcons ttrue
      (tcons tfalse
        (tcons ttrue tnil))).
    
Lemma test: forall M n env M' v,
    teval n M env (ex_fold_or (length env)) = (M', Some (Some (v))) ->
    v = (vbool false).
Proof.
    intros. destruct n. simpl in *. inversion H. 
    simpl in H. 
    remember (teval n M env tfalse) as Ht. 
    symmetry in HeqHt. destruct Ht as [nt [rt|]]. 2: { inversion H. }
    destruct rt. 2: { inversion H. }
    remember (teval n nt env (tcons ttrue (tcons tfalse (tcons ttrue tnil)))) as Htcons. 
    symmetry in HeqHtcons. destruct Htcons as [ntcons [rtcons|]]. 2: { inversion H. }
    destruct rtcons. 2: { inversion H. }
    destruct v1. inversion H. inversion H. 2: { inversion H. }
    destruct n. simpl in *. inversion HeqHt. simpl in HeqHt. inversion HeqHt. subst v0 nt.   
    simpl in HeqHtcons. 
    remember (teval n M env ttrue) as Ht2. 
    symmetry in HeqHt2. destruct Ht2 as [nt2 [rt2|]]. 2: { inversion HeqHtcons. }
    destruct rt2. 2: { inversion HeqHtcons. }
    destruct n. simpl in *. inversion HeqHt2. simpl in HeqHt2. inversion HeqHt2. subst v0 nt2. 
    simpl in HeqHtcons. 
    remember (teval n M env tfalse) as Ht3. symmetry in HeqHt3. destruct Ht3 as [nt3 [rt3|]]. 2: { inversion HeqHtcons. }
    destruct n. simpl in HeqHt3. inversion HeqHt3. simpl in HeqHt3. inversion HeqHt3. subst rt3 nt3.
    simpl in HeqHtcons. 
    remember (teval n M env ttrue) as Ht4. symmetry in HeqHt4. destruct Ht4 as [nt4 [rt4|]]. 2: { inversion HeqHtcons. }
    destruct n. simpl in HeqHt4. inversion HeqHt4. simpl in HeqHt4. inversion HeqHt4. subst rt4 nt4. 
    simpl in HeqHtcons. inversion HeqHtcons. subst ntcons l.
    cbn [fold_right] in H.
    simpl in H.
    bdestruct (length env =? S (length env)). lia. 
    bdestruct (length env =? length env). 2: { lia. } 
    simpl in H. congruence.
Qed.
    

(* fun f0,xs1 => fold (x2,a3 => (f0 x2)::a3) [] xs1 *)
Definition ex_map (n: nat): tm :=
    tabs (tabs
      (tfold
         (tcons (tapp (tvar n) (tvar (S (S n))))
                (tvar (S (S (S n)))))
         tnil
         (tvar (S n)))).
  
(* Sample use at top level (n = 0): map (fun b => not b) [true; false; true]. *)
Definition ex_map_test (n: nat): tm :=
  tapp
    (tapp (ex_map n) (tabs (tnot (tvar n))))
    (tcons ttrue (tcons tfalse (tcons ttrue tnil))).

Lemma eval_ex_map_test: forall n E M M' v,
  teval n M E (ex_map_test (length E)) = (M', Some (Some v)) ->
  v = vlist [vbool false; vbool true; vbool false].
Proof.
  intros. destruct n. simpl in *. inversion H. 
  simpl in H. 
  remember (teval n M E (tapp (ex_map (length E)) (tabs (tnot (tvar (length E)))))) as Ht.
  unfold ex_map in *.
  symmetry in HeqHt. destruct Ht as [nt [rt|]]. 2: { inversion H. }
  destruct rt. 2: { inversion H. }

  destruct v0; try inversion H. 

  remember (teval n nt E (tcons ttrue (tcons tfalse (tcons ttrue tnil)))) as Ht1.
  symmetry in HeqHt1. destruct Ht1 as [nt1 [rt1|]]. 2: { inversion H. }
  destruct rt1. 2: { inversion H. }

  simpl in *.

  destruct n. simpl in *. inversion H.
  simpl in *.


  remember (teval n nt E ttrue) as HT.
  symmetry in HeqHT. destruct HT as [nT [rT|]]. 2: { inversion  HeqHt1. }
  destruct rT. 2: { inversion HeqHt1. }

  remember (teval n nT E (tcons tfalse (tcons ttrue tnil))) as HL.
  symmetry in HeqHL. destruct HL as [nL [rL|]]. 2: { inversion  HeqHt1. }
  destruct rL. 2: { inversion HeqHt1. }

  destruct v2; try inversion HeqHt1.
  subst nt1 v0. clear HeqHt1.



  remember  (teval n M E
  (tabs
     (tabs
        (tfold
           (tcons (tapp (tvar (length E)) (tvar (S (S (length E)))))
              (tvar (S (S (S (length E)))))) tnil
           (tvar (S (length E))))))) as Ht2.
  symmetry in HeqHt2. destruct Ht2 as [nt2 [rt2|]]. 2: { inversion HeqHt. }
  destruct rt2. 2: { inversion HeqHt. }

  destruct v0; try inversion HeqHt.

  remember (teval n nt2 E (tabs (tnot (tvar (length E))))) as HN.
  symmetry in HeqHN. destruct HN as [nN [rN|]]. 2: { inversion HeqHt. }
  destruct rN. 2: { inversion H2. }
  
  destruct n. simpl in *. inversion H2.
  simpl in *. inversion HeqHt2. subst nt2 l1 t0.
  inversion H2. subst nN l t. clear H2.
  inversion HeqHN. subst nt v0.

  inversion HeqHT. subst nT v1.
  clear HeqHt. clear HeqHN. clear HeqHT.

  simpl in *. bdestruct (length E =? length E); intuition.
  clear HeqHt2.

  remember (teval n M E tfalse) as HF.
  symmetry in HeqHF. destruct HF as [nF [rF|]]. 2: { inversion HeqHL. }
  destruct rF. 2: { inversion HeqHL. }

  remember (teval n nF E (tcons ttrue tnil)) as HLT.
  symmetry in HeqHLT. destruct HLT as [nLT [rLT|]]. 2: { inversion HeqHL. }
  destruct rLT. 2: { inversion HeqHL. }
  destruct v1; try inversion HeqHL.
  subst nLT l0. clear HeqHL.
  
  destruct n. simpl in *. inversion HeqHLT.
  simpl in *.

  remember (teval n nF E ttrue) as HT.
  symmetry in HeqHT. destruct HT as [nT [rT|]]. 2: { inversion HeqHLT. }
  destruct rT. 2: { inversion HeqHLT. }

  inversion HeqHF. subst nF v0. clear HeqHF.

  remember (teval n nT E tnil) as HTA.
  symmetry in HeqHTA. destruct HTA as [nTA [rTA|]]. 2: { inversion HeqHLT. }
  destruct rTA. 2: { inversion HeqHLT. }
  destruct v0; try inversion HeqHLT.
  subst nTA l. clear HeqHLT.
  
  destruct n. simpl in *. inversion HeqHT.

  simpl in *. inversion HeqHT. inversion HeqHTA. subst nT. subst v1 nL l0.


  cbn [fold_right] in H1.
  bdestruct (length E =? (S (S (S (length E))))); intuition.
  bdestruct (length E =? (S (S (length E)))); intuition.
  bdestruct (length E =? (S (length E))); intuition.
  bdestruct (length E =? length E); intuition.
  simpl in *.
  
  remember (teval n M (vbool true :: E) (tvar (length E))) as TE1.
  symmetry in HeqTE1. destruct TE1 as [nE1 [rE1|]]. 2: { inversion H. }
  destruct rE1. 2: { inversion H. }
  
  destruct n. simpl in *. inversion HeqTE1.
  simpl in *. bdestruct (length E =? length E); intuition.
  inversion HeqTE1. subst nE1 v0.
  inversion H1. auto.
Qed.


Lemma envc_empty: forall G a,
  env_cap G qempty a.
Proof.
  intros. unfold env_cap. intros. unfoldq; intuition.
Qed.

(*
Definition ex_map (n: nat): tm :=
    tabs (tabs
      (tfold
         (tcons (tapp (tvar n) (tvar (S (S n))))
                (tvar (S (S (S n)))))
         tnil
         (tvar (S n)))).
  
*)

(*
Definition ex_map_test (n: nat): tm :=
  tapp
    (tapp (ex_map n) (tabs (tnot (tvar n))))
    (tcons ttrue (tcons tfalse (tcons ttrue tnil))).
*)

Lemma ty0: forall G f T1  T2 al a2 F n ay ef af
  (X: F = TFun T1 false al T2 false ay ef)
  (N: n = length G)
  (Y: f = (tcons (tapp (tvar n) (tvar (S (S n)))) (tvar (S (S (S n)))))), 
  has_type ((TList T2, false, a2) :: (T1, false, al) :: (TList T1, false, al) :: (F, af, af) :: G)
           (tapp (tvar n) (tvar (S (S n))))  T2  (qor (qone n) (qone (S (S n))))  false
           ((af || al) && ay)
           ((af || al) && ef).
Proof.
  intros. replace false with ((false||false)&& ay ||false) at 4.
  replace ((af || al) && ef) with (false || false || ((af || al) && ef)).
  eapply t_app. subst n. replace af with (af || af) at 3. 
  eapply t_var. rewrite indexr_skip. rewrite indexr_skip. rewrite indexr_skip. subst F. rewrite indexr_head. eauto. simpl. lia. simpl. lia. simpl. lia.
  simpl. destruct af; eauto.
  replace al with (false||al) at 3.
  eapply t_var. replace (S (S n)) with (length ((TList T1, false, al) :: (F, af, af) :: G)). 2: { subst n. simpl. lia. }
  rewrite indexr_skip. rewrite indexr_head. auto. simpl. lia. simpl. auto. simpl. auto. simpl. auto.
Qed.

Lemma ty1: forall G f T1  T2 al a2 F n ay ef af
  (X: F = TFun T1 false al T2 false ay ef)
  (N: n = length G)
  (Y: f = (tcons (tapp (tvar n) (tvar (S (S n)))) (tvar (S (S (S n)))))),
  has_type ((TList T2, false, a2) :: (T1, false, al) :: (TList T1, false, al) :: (F, af, af) :: G) 
            f  (TList T2)  (qor (qor (qone n) (qone (S (S n)))) (qone (S (S (S n)))))
            false   (((af || al) && ay) || a2)  ((af || al) && ef).
Proof.
  intros. subst f. replace false with (false ||false) at 4.
  replace ((af || al) && ef) with (((af || al) && ef) || false).
  eapply t_cons with (t1 := (tapp (tvar n) (tvar (S (S n)))))(t2 := (tvar (S (S (S n))))) (p1 := (qor (qone n) (qone (S (S n))))).
  eapply ty0; eauto. 
  replace a2 with (false||a2) at 2.
  eapply t_var. replace (S (S (S n ))) with (length ((T1, false, al) :: (TList T1, false, al) :: (F, af, af) :: G)).
  2: { simpl. lia. }
  rewrite indexr_head. auto. simpl. auto. destruct af, al, ef; simpl; auto. simpl. auto.
Qed.


Lemma ty2: forall G f T1  T2 al a2 F n ay ef af p p2
  (X: F = TFun T1 false al T2 false ay ef)
  (N: n = length G)
  (Y: f = (tcons (tapp (tvar n) (tvar (S (S n)))) (tvar (S (S (S n))))))
  (Z: (((af || al) && ay) || a2) = a2),
  p2 =  (qor (qor (qone n) (qone (S (S n)))) (qone (S (S (S n))))) ->
  p = (qdiff p2 (qor (qone (S (S (S n)))) (qone (S (S n))))) ->
  has_type ((TList T1, false, al) ::(F, af, af) :: G)
           (tfold f tnil (tvar (S n)))
           (TList T2)
           (qor (qone n) (qone (S n)))
           false
          a2
          ((af||al) &&ef).
Proof.
  intros. 
  assert (has_type ((TList T2, false, a2) :: (T1, false, al) :: (TList T1, false, al) :: (F, af, af) :: G) 
            f  (TList T2)  p2
            false   (((af || al) && ay) || a2)  ((af || al) && ef)) as HH. {
          subst p2. eapply ty1; eauto.
  }
  assert (qor qempty (qor (qone (S n)) p) = qor (qone n) (qone (S n))) as D. {
    rewrite <-qor_empty_id_l. subst p. subst p2. rewrite plift_qual_eq. repeat rewrite plift_or.
    repeat rewrite plift_diff. repeat rewrite plift_or. repeat rewrite plift_one.
    eapply functional_extensionality. intros. eapply propositional_extensionality. split; intros.
    unfoldq; intuition. unfoldq; intuition. 
  }
  replace (qor (qone n) (qone (S n))) with (qor qempty (qor (qone (S n)) p)).
  eapply t_sub_stp.
  eapply t_fold with (al := al)(e2 := (af||al)&&ef)(a2 := a2)(ez := false). 
  2: {
     eapply t_sub_stp. eapply t_nil. eapply stp_id. all: unfold bsub; auto. intuition.  
   }
   2: { replace al with (false||al) at 2. eapply t_var. 
        replace (S n) with (length ((F, af, af)::G)). rewrite indexr_head. auto. simpl. lia. simpl. auto.  }
   2: { simpl. subst n. eapply H0. }
   2: { eapply stp_id. }
   2: { unfold bsub. auto. }
   2: { unfold bsub. intros. auto. }
   simpl in *.

   rewrite <- Z at 2. eauto.
   unfold bsub. simpl. auto.
Qed.


Lemma ty3: forall G f T1  T2 al a2 F n ay ef af pf p2
  (X: F = TFun T1 false al T2 false ay ef)
  (N: n = length G)
  (Y: f = (tcons (tapp (tvar n) (tvar (S (S n)))) (tvar (S (S (S n))))))
  (Z: (((af || al) && ay) || a2) = a2),
  p2 = (qor (qone n) (qone (S n))) ->
  pf = (qdiff p2 (qone (S n))) ->
  env_cap ((F, af, af) :: G) pf af ->
  has_type ((F, af, af) :: G)
           (tabs ((tfold f tnil (tvar (S n)))))
           (TFun (TList T1) false al (TList T2) false a2 ((af||al) &&ef)) pf false ((((af||al) &&ef)||a2)&&af) false.

Proof.
  intros.
  assert (has_type ((TList T1, false, al) ::(F, af, af) :: G)
           (tfold f tnil (tvar (S n)))
           (TList T2)
           p2
           false
           a2 
           ((af||al) &&ef) ) as HH. {
    subst p2. 
    eapply ty2; eauto.
  }
  
  eapply t_abs. eauto. simpl. subst n. auto. auto. 
Qed.

Lemma ty4: forall G f T1  T2 al a2 F n ay ef af 
  (X: F = TFun T1 false al T2 false ay ef)
  (N: n = length G)
  (Y: f = (tcons (tapp (tvar n) (tvar (S (S n)))) (tvar (S (S (S n))))))
  (Z: (((af || al) && ay) || a2) = a2),
  has_type G (ex_map n)
             (TFun F af af  (TFun (TList T1) false al (TList T2) false a2 ((af||al) &&ef)) false ((((af||al) &&ef)||a2)&&af) false)
             qempty false false false.    

Proof.
  intros. unfold ex_map.

  assert (has_type ((F, af, af) :: G)
           (tabs ((tfold f tnil (tvar (S n)))))
           (TFun (TList T1) false al (TList T2) false a2 ((af||al) &&ef)) (qone n) false ((((af||al) &&ef)||a2)&&af) false ) as HH. {
    eapply ty3;eauto. 
    rewrite plift_qual_eq. rewrite plift_diff. repeat rewrite plift_or. repeat rewrite plift_one.
    eapply functional_extensionality. intros. eapply propositional_extensionality. split; intros.
    unfoldq; intuition. unfoldq; intuition.
    replace (qone n) with (qor qempty (qone (length G))).
    eapply envc_extend. eapply envc_empty. unfold bsub. auto.
    destruct af; eauto. rewrite qor_empty_id_l. subst n. auto. 
  }

  assert (qor (qdiff (qone n) (qone (length G))) (qdiff (qone n) (qone (length G))) = qempty) as D. {
    rewrite qor_idempetic. replace (qdiff (qone n) (qone (length G))) with qempty. eauto.
    rewrite plift_qual_eq. subst n.  rewrite plift_diff. rewrite pdiff_same. rewrite plift_empty. auto.
  }
  
  eapply t_abs with (af := false) in HH as HH'. 
  2: { eauto. }
  2: { rewrite D. eapply envc_empty. }
  simpl in *.
  rewrite D in HH'.
  replace (((af || al) && ef || a2) && af && false)  with  false in HH'.
  subst f. eauto.
  destruct af, al, ef, a2; simpl; auto.  
Qed.


(* map itself is closed *)
(* map: ((f: (T1 ∐ =>⊤ T2 ∐) Π ) =>⊥  (List T1 ∐ =>⊤ List T2 ∐) ⟨⊥, ⊤⟩ *)

Lemma ty5: forall G f T1  T2  F n 
  (X: F = TFun T1 false false T2 false false true)
  (N: n = length G)
  (Y: f = (tcons (tapp (tvar n) (tvar (S (S n)))) (tvar (S (S (S n)))))),
  has_type G (ex_map n)
             (TFun F true true  (TFun (TList T1) false false (TList T2) false false true) false true false)
             qempty false false false.    
Proof.
  intros.
  specialize ty4 with (al := false)(ay := false)(a2 := false)(af := true)(ef := true).
  intros. simpl in *. eapply H; eauto.
Qed. 

(* [true; false; true] *)
Definition mylist := (tcons ttrue (tcons tfalse (tcons ttrue tnil))). 

Lemma ty_mylist: forall G a fr,
  has_type G mylist (TList TBool) qempty a fr false.
Proof.
  intros. unfold mylist. 
  replace qempty with (qor qempty qempty).
  replace false with (false||false).
  replace fr with (false||fr).
  replace a with (false ||a).
  eapply t_cons. eapply t_true.
  replace qempty with (qor qempty qempty).
  replace false with (false||false).
  replace fr with (false||fr).
  replace a with (false ||a).
  eapply t_cons. eapply t_false.
  replace qempty with (qor qempty qempty).
  replace false with (false||false).
  replace fr with (false||fr).
  replace a with (false ||a).
  eapply t_cons. eapply t_true.
  eapply t_sub_stp.
  eapply t_nil.
  eapply stp_id.
  1-3: unfold bsub; intuition.
  all: simpl; auto.
Qed.  


Lemma ty_myfun_noeff: forall G F f_neg n
  (N: n = length G)
  (X: F = TFun TBool false false TBool false false false)
  (PF: f_neg = tabs (tnot (tvar n))),
  has_type G f_neg F qempty false false false.
Proof.
  intros. subst F f_neg.
  replace false with ((false||false)&&false) at 7.
  eapply t_abs with (p2 := qone n).
  eapply t_not with (a := false)(fr := false). 
  replace false with (false||false) at 4. subst n.
  eapply t_var. rewrite indexr_head. auto. simpl. auto.
  rewrite plift_qual_eq. rewrite plift_diff. repeat rewrite plift_one. subst n. rewrite pdiff_same. rewrite plift_empty. auto.
  intros ??????. unfoldq; intuition. simpl; auto.
Qed.

(* pass a function without effects to map *)
Lemma ty5_noeff: forall G f F n f_neg T_fneg
  (X: F = TFun TBool false false TBool false false true)
  (N: n = length G)
  (Y: f = (tcons (tapp (tvar n) (tvar (S (S n)))) (tvar (S (S (S n))))))
  (PF: f_neg = tabs (tnot (tvar n)))
  (Z: T_fneg =  TFun TBool false false TBool false false false),
  has_type G (tapp (tapp (ex_map n) f_neg) mylist) (TList TBool) qempty false false false.
Proof.
  intros. 
  assert (has_type G (ex_map n)
            (TFun F true true  (TFun (TList TBool) false false (TList TBool) false false true) false true false)
             qempty false false false ) as HH. {
    eapply ty5; eauto.
  } 
  assert  (has_type G (ex_map n)
            (TFun T_fneg false false  (TFun (TList TBool) false false (TList TBool) false false true) false true false)
             qempty false false false ) as HH'. {
    eapply t_sub_stp. eapply HH.
    eapply s_fun. {
      subst T_fneg. subst F. eapply s_fun.
      1,2: eapply stp_id. all: unfold bsub; auto.
    }
    eapply stp_id; eauto. all: unfold bsub; auto. 
  } 
  eapply ty_myfun_noeff in PF as HA; eauto. 
  eapply t_app with (f := (ex_map n))(t := f_neg)(p2 := qempty)(ef := false)(e1 := false) in HH' as HB.
  2: { eapply HA.  }
  simpl in *. rewrite qor_idempetic in HB. 
  eapply t_app with (f := tapp (ex_map n) f_neg)(t := mylist)(p2 :=qempty)(e1 := false) in HB as HC.
  2: eapply ty_mylist.
  simpl in *. rewrite qor_idempetic in HC. auto. 
Qed.

Lemma ty_myfun_eff: forall G F f_neg n
  (N: n = length G)
  (X: F = TFun TBool false false TBool false false true)
  (PF: f_neg = tabs (tnot (tvar n))),
  has_type G f_neg F qempty false false false.
Proof.
  intros. subst F f_neg.
  replace false with ((true||false)&&false) at 6.
  eapply t_abs with (p2 := qone n).
  eapply t_not with (a := false)(fr := false). 
  replace false with (false||false) at 4. subst n.
  eapply t_sub_eff with (e := false).
  eapply t_var. rewrite indexr_head. auto. simpl. auto.
  rewrite plift_qual_eq. rewrite plift_diff. repeat rewrite plift_one. subst n. rewrite pdiff_same. rewrite plift_empty. auto.
  intros ??????. unfoldq; intuition. simpl; auto.
Qed.
    

(* pass an effectful function to map by upcasting the effect of f_neg *)
Lemma ty5_eff: forall G f F n f_neg
  (X: F = TFun TBool false false TBool false false true)
  (N: n = length G)
  (Y: f = (tcons (tapp (tvar n) (tvar (S (S n)))) (tvar (S (S (S n))))))
  (PF: f_neg = tabs (tnot (tvar n))),
  env_cap G qempty true ->
  has_type G (tapp (tapp(ex_map n) f_neg) mylist) (TList TBool) qempty false false true.
Proof.
  intros.
  assert (has_type G (ex_map n)
      (TFun F true true  (TFun (TList TBool) false false (TList TBool) false false true) false true false)
             qempty false false false ) as HH. {
    eapply ty5; eauto.
  } 
  eapply t_app with (f := (ex_map n))(t := f_neg)(p2 := qempty)(ef := false) in HH as HA.
  2: { eapply t_sub_cap. eapply t_sub_fresh. eapply ty_myfun_eff; eauto. }
  simpl in *. 
  eapply t_app with (f := tapp (ex_map n) f_neg)(t := mylist)(p2 :=qempty)(e1 := false) in HA as HB.
  2: eapply ty_mylist.
  simpl in *. rewrite qor_idempetic in HB.
  auto.
Qed.


(* variants that factor out the 'map' term (this is to demonstrate that the use site
   cannot inspect the 'map' term (e.g. to re-type it), only the given type) *)



(* pass a function without effects to map *)
Lemma ty5_noeff': forall G F LF n f_neg T_fneg q t_map T_map
  (X: F = TFun TBool false false TBool false false true)
  (Y: LF = (TFun (TList TBool) false false (TList TBool) false false true))
  (U: T_map = (TFun F false true LF false true false))
  (N: n = length G)
  (PF: f_neg = tabs (tnot (tvar n)))
  (Z: T_fneg = TFun TBool false false TBool false false false),
  has_type G t_map T_map q false false false ->
  has_type G (tapp (tapp t_map f_neg) mylist) (TList TBool) q false false false.
Proof.
  intros. subst T_map LF. rename H into HH. 
  assert  (has_type G t_map
            (TFun T_fneg false false (TFun (TList TBool) false false (TList TBool) false false true) false true false)
             q false false false ) as HH'. {
    eapply t_sub_stp. eapply HH.
    eapply s_fun. {
      subst T_fneg. subst F. eapply s_fun.
      1,2: eapply stp_id. all: unfold bsub; auto.
    }
    eapply stp_id; eauto. all: unfold bsub; auto. 
  } 
  eapply ty_myfun_noeff in PF as HA; eauto. 
  eapply t_app with (f := t_map)(t := f_neg)(p2 := qempty)(ef := false)(e1 := false) in HH' as HB.
  2: { eapply HA.  }  
  assert (forall q, (qor q qempty) = q) as QE. {
    unfold qor, qempty. intros. extensionality x. eauto with bool. }
  simpl in *. rewrite QE in HB. 
  eapply t_app with (f := tapp t_map f_neg)(t := mylist)(p2 :=qempty)(e1 := false) in HB as HC.
  2: eapply ty_mylist.
  simpl in *. rewrite QE in HC. auto. 
Qed.


(* alternative proof using hast_strengthen *) 
Lemma ty5_noeff'': forall G F LF n f_neg q t_map T_map
  (X: F = TFun TBool false false TBool false false true)
  (Y: LF = (TFun (TList TBool) false false (TList TBool) false false true))
  (U: T_map = (TFun F true true LF false true false))
  (N: n = length G)
  (PF: f_neg = tabs (tnot (tvar n))),
  env_cap G q false -> 
  has_type G t_map T_map q false false false ->
  has_type G (tapp (tapp t_map f_neg) mylist) (TList TBool) q false false false.
Proof.
  intros. subst T_map LF. rename H0 into HH. 
  eapply ty_myfun_eff in PF as HA; eauto. 
  eapply t_app with (f := t_map)(t := f_neg)(p2 := qempty)(ef := false)(e1 := false) in HH as HB.
  2: { subst F. eapply t_sub_cap. eapply t_sub_fresh. eapply ty_myfun_eff; eauto. }
  assert (forall q, (qor q qempty) = q) as QE. {
    unfold qor, qempty. intros. extensionality x. eauto with bool. }
  simpl in *. rewrite QE in HB. 
  eapply t_app with (f := tapp t_map f_neg)(t := mylist)(p2 :=qempty)(e1 := false) in HB as HC.
  2: eapply ty_mylist.
  simpl in *. rewrite QE in HC.
  eapply hast_strengthen in HC. 2: eauto. simpl in HC. eapply HC.
Qed.


(* pass an effectful function to map (e.g. by upcasting the effect of f_neg) *)
Lemma ty5_eff': forall G F LF n f_neg q qf t_map T_map
  (X: F = TFun TBool false false TBool false false true)
  (Y: LF = (TFun (TList TBool) false false (TList TBool) false false true))
  (U: T_map = (TFun F false true LF false true false))
  (N: n = length G),
  has_type G t_map T_map q false false false ->
  has_type G f_neg F qf false true false ->
  has_type G (tapp (tapp t_map f_neg) mylist) (TList TBool) (qor q qf) false false true.
Proof.
  intros. rename H0 into HH. subst T_map LF.
  eapply t_app with (f := t_map)(t := f_neg)(p2 := qf)(ef := false) in HH as HA.
  2: { eapply t_sub_cap. eauto. }
  simpl in *. 
  eapply t_app with (f := tapp t_map f_neg)(t := mylist)(p2 :=qempty)(e1 := false) in HA as HB.
  2: eapply ty_mylist.
  assert (forall q, (qor q qempty) = q) as QE. {
    unfold qor, qempty. intros. extensionality x. eauto with bool. }
  simpl in *. rewrite QE in HB.
  auto.
Qed.

