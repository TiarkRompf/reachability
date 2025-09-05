(*******************************************************************************
* Coq mechanization of the re-ordering rule without effect qualifier in the λ^♦-caluclus.

*******************************************************************************)

(* based on sec6_reach_binary.v *)
(* based on sec7_store_invariants.v *)

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

Require Import sec4_reach_binary.
Require Import sec5_store_invariants.


Import STLC.

Lemma separation1: forall M H1 H2 G p p1 p2 
   (WFE: env_type M H1 H2 G p) 
   (SEP: psub (pand (vars_trans' G p1)(vars_trans' G p2)) pempty)
   (SUB1: psub (plift p1) p)
   (SUB2: psub (plift p2) p),
   psub (pand (locs_locs_stty (st1 M) (vars_locs H1 (plift p1)))(locs_locs_stty (st1 M) (vars_locs H1 (plift p2) ))) pempty.
Proof.
  intros. remember WFE as WFE'. clear HeqWFE'. destruct WFE as [L1 [L2 [P1 [P2 [W1 [W2 W3]]]]]].
  unfold vars_trans' in SEP. rewrite plift_vt in SEP. rewrite plift_vt in SEP. 
  assert (psub (pand (vars_trans G (plift p1))(vars_trans G (plift p2))) p). {
    intros ? ?. eapply SEP in H. unfoldq; intuition.
  }
  eapply vars_locs_mono with (H := H1) in SEP. eapply lls_mono with (M := (st1 M)) in SEP.
  rewrite <- lls_empty with (M := (st1 M)). rewrite <- vars_locs_empty with (H := H1). 
  intros ? ?.  eapply W2 in H0; eauto. 
  eapply envt_telescope; eauto. eapply envt_telescope; eauto.
Qed.

Lemma separation2: forall M H1 H2 G p p1 p2 
   (WFE: env_type M H1 H2 G p) 
   (SEP: psub (pand (vars_trans' G p1)(vars_trans' G p2)) pempty)
   (SUB1: psub (plift p1) p)
   (SUB2: psub (plift p2) p),
   psub (pand (locs_locs_stty (st2 M) (vars_locs H2 (plift p1)))(locs_locs_stty (st2 M) (vars_locs H2 (plift p2) ))) pempty.
Proof.
  intros. remember WFE as WFE'. clear HeqWFE'. destruct WFE as [L1 [L2 [P1 [P2 [W1 [W2 W3]]]]]].
  unfold vars_trans' in SEP. rewrite plift_vt in SEP. rewrite plift_vt in SEP. 
  assert (psub (pand (vars_trans G (plift p1))(vars_trans G (plift p2))) p). {
    intros ? ?. eapply SEP in H. unfoldq; intuition.
  }
  eapply vars_locs_mono with (H := H2) in SEP. eapply lls_mono with (M := (st2 M)) in SEP.
  rewrite <- lls_empty with (M := (st2 M)). rewrite <- vars_locs_empty with (H := H2). 
  intros ? ?.  eapply W3 in H0; eauto. 
  eapply envt_telescope; eauto. eapply envt_telescope; eauto.
Qed.

Theorem reorder_seq : forall G t1 t2 p1 p2  q1 q2 p
  (W1: has_type G t1 TBool p1 false q1)
  (W2: has_type G t2 TBool p2 false q2)
  (SEP: psub (pand (vars_trans' G p1)(vars_trans' G p2)) pempty) (* observations are separate *)
  (SUB1: psub (plift p1) (plift p))
  (SUB2: psub (plift p2) (plift p)),
  sem_type G (tseq t1 t2) (tseq t2 t1) TBool (plift p) false pempty.
Proof.
  intros. intros ? ? ? WFE STF S1 S2 ST.
  assert (env_type M H1 H2 G (plift p1)) as WFE1. eapply envt_tighten; eauto.
  assert (env_type M H1 H2 G (plift p2)) as WFE2. eapply envt_tighten. eapply WFE. eauto.

  (* E1 *)
  eapply fundamental_property in W1 as SEM1.
  destruct (SEM1 M H1 H2 WFE1 STF S1 S2 ST) as [S1' [S1x' [M' [v1 [v1x IE1]]]]].
  destruct IE1 as (E1 & E1x & STC' & SFM' & ST' & SE1 & SE1x & VT' & VQ1 & VQ2). 

  assert (length S1 = length1 M) as L1. { destruct ST as [[L ?] ?]. eauto. }
  assert (length S2 = length2 M) as L2. { destruct ST as [? [[L ?] ?]]. eauto. }
  assert (length S1' = length1 M') as L1'. { destruct ST' as [[L ?] ?]. eauto. }
  assert (length S1 <= length S1') as LEQ1. { eapply st_mono1 in STC'. lia. }   
  assert (length2 M <= length2 M') as LEQ2. { eapply st_mono2 in STC'. lia. }

  remember ST' as ST'x. clear HeqST'x.
  destruct ST'x as [SST1' [SST2' [STREL' [STR' STL']]]].

  (* E2 *)
  eapply store_invariance2' in W2 as W2'. 
  2: eapply WFE2. 2: eauto. 2: eauto. 2: lia. 3: eapply ST'. 2: eapply STC'; eauto.
  2: { eapply separation1. eapply WFE. intros ? [? ?].  eapply SEP. split; auto.
       auto. auto. }

  destruct W2' as (S1'' & S2' & M'' & v2 & v2x & E2' & E2 & STC'' & STF'' & ST'' & SE2' & SE2 & VT'' & VQ3 & VQ4).

  assert (length S2 <= length S2') as LEQ3. {
    eapply st_mono2 in STC''. unfold length2, st2 in STC''. simpl in STC''.  destruct ST'' as (? & (L& ?) & ?).  unfold st2  in L. 
    destruct ST as [? [[L' ?] ?]]. unfold st2 in L'. lia.
  }
  assert (length2 M <= length2 M'') as LEQ4. {
    eapply st_mono2 in STC''. unfold length2, st2 in STC''. simpl in STC''. unfold length2, st2. lia.
  }
  
  (* E1 *)
  eapply store_invariance3' in W1 as W1'. 
  2: eapply WFE1. 2: eauto. 2: eauto. 2: eauto. 2: eapply STC''; eauto. 
  2: { destruct ST'' as [? [X ?]]. auto. }
  2: { unfold st2, st1. simpl. eapply separation2. eapply WFE. intros ? ?.  eapply SEP. auto. 
       eauto. auto. }

  destruct W1' as (S1y' & S2'' & M''' & v1y & v1z & E1y & E2'' & STC''' &  SFT''' & ST''' & SE1y & SE2'' & VT''' & VQ5 & VQ6).    
  
  assert (S1' = S1y' /\ v1 = v1y) as A. {
    destruct E1 as [n1 E1].
    destruct E1y as [n1x E1y].
    assert (1+n1+n1x > n1) as A1. lia.
    assert (1+n1+n1x > n1x) as A1x. lia. 
    specialize (E1 _ A1).
    specialize (E1y _ A1x).
    split; congruence.
  }
  destruct A. subst v1y S1y'.
  clear WFE1. clear WFE2.

  destruct v1; destruct v1x; destruct v1z; simpl in VT'; simpl in VT'''; intuition. subst b0 b1.
  destruct v2; destruct v2x; simpl in VT''; intuition. subst b0.

  assert (tevaln S1 H1 (tseq t1 t2) S1'' (vbool (b && b1))). {
      destruct E1 as [n1 E1].
      destruct E2' as [n1' E1'].
      exists (1+n1+n1'). intros.
      destruct n. lia. simpl.
      rewrite E1, E1'. eauto. lia. lia. 
    }

    assert (tevaln S2 H2 (tseq t2 t1) S2'' (vbool (b1 && b))). {
      destruct E2 as [n1 E2].
      destruct E2'' as [n1' E1'].
      exists (1+n1+n1'). intros.
      destruct n. lia. simpl.
      rewrite E2, E1'. eauto. lia. lia. 
    }

    assert (b && b1 = b1 && b). eauto with bool.
    rewrite H3 in *. 

  unfold st2, st1 in *. simpl in *.

  
  (* separation *)
  assert (forall l, locs_locs_stty (st1 M) (vars_locs H1 (plift p1)) l -> locs_locs_stty (st1 M)  (vars_locs H1 (plift p2) ) l -> False) as SEP1. {
    intros. eapply separation1 with (p1 := p1). eauto. intros ? ?. eapply SEP; eauto. auto. auto.
    split; eauto.
  }

  assert (forall l, locs_locs_stty (st2 M) (vars_locs H2 (plift p1)) l -> locs_locs_stty (st2 M) (vars_locs H2 (plift p2) ) l -> False) as SEP1X. {
    intros. eapply separation2 with (p1 := p1). eauto. intros ? [? ?]. eapply SEP. split. eapply H6. eapply H7.
    auto. auto. split; eauto.
  }

  assert (forall l1 l2, strel M l1 l2 -> locs_locs_stty (st1 M) (vars_locs H1 (plift p1)) l1 -> ~ locs_locs_stty (st2 M) (vars_locs H2 (plift p1)) l2 -> False) as SEP2. {
    intros. eapply H6. edestruct envt_same_locs with (p1:=plift p1). 2: eapply WFE. eauto. eauto. eauto. eauto. 
  }

  assert (forall l1 l2, strel M l1 l2 -> locs_locs_stty (st1 M) (vars_locs H1 (plift p2)) l1 -> ~ locs_locs_stty (st2 M) (vars_locs H2 (plift p2)) l2 -> False) as SEP3. {
    intros. eapply H6. edestruct envt_same_locs with (p1:=plift p2). 2: eapply WFE. eauto. eauto. eauto. eauto.
  }    
  

  assert (forall l1 l2, strel M l1 l2 -> locs_locs_stty (st2 M) (vars_locs H2 (plift p1)) l2 -> ~ locs_locs_stty (st1 M) (vars_locs H1 (plift p1)) l1 -> False) as SEP4. {
    intros. eapply H6. edestruct envt_same_locs with (p1:=plift p1). 2: eapply WFE. eauto. eauto. eauto. eauto.
  }
  

  assert (forall l1 l2, strel M l1 l2 -> locs_locs_stty (st2 M) (vars_locs H2 (plift p2)) l2 -> ~ locs_locs_stty (st1 M) (vars_locs H1 (plift p2)) l1 -> False) as SEP5. {
    intros. eapply H6. edestruct envt_same_locs with (p1:=plift p2). 2: eapply WFE. eauto. eauto. eauto. eauto.
  }


  assert (st_chain_partial M M''' (locs_locs_stty (st1 M) (vars_locs H1 (plift p1))) (locs_locs_stty (st2 M) (vars_locs H2 (plift p1)))) as SXMP2. {
     eapply stchain_tighten with (p1' := (locs_locs_stty (st1 M) (vars_locs H1 (plift p1))))(p2':= (locs_locs_stty (st2 M) (vars_locs H2 (plift p1)))) in STC''' as R.
     2: {
         unfold st_filter. split. 2: split.
       + unfold st_locs1, pnat, length1, st1. simpl. eapply envt_store_deep_wf; eauto. 
       + unfold st_locs2, pnat, length2, st2. simpl. intros ? ?. eapply envt_store_deep_wf in H4; eauto. unfold pnat, length2, st2 in *. lia. 
       + intros. unfold strel in H4. simpl in H4. destruct H4 as [? [? ?]].
         split. intros. eapply envt_filter_deep in H7; eauto.
         intros ?. eapply envt_filter_deep in H7; eauto.
     }
     2: { unfold st_locs1, pnat, length1, st1. simpl. eapply envt_store_deep_wf; eauto. }
     2: {
       unfold st_locs2, pnat, length2, st2. simpl. intros ? ?. eapply envt_store_deep_wf in H4; eauto. unfold pnat, length2, st2 in *. lia. 
     }
     destruct R as [A [B [C [D [E F]]]]].
     unfold st_chain_partial. split. 2: split. 3: split. 4: split. 5: split.
     + eapply envt_filter_deep; eauto.
     + auto.
     + unfold st1 in C. simpl in C. unfold st1. auto.
     + unfold st2 in D. simpl in D. unfold st2. eapply sst_trans'' with (M2 := (st2 M'')).
       eapply sstchain_tighten. eapply STC''; eauto. eapply envt_store_deep_wf; eauto. 
       destruct STC''' as [? [? [? [XX ?]]]]. eapply sstchain_tighten. eapply XX.
       unfold st_locs1, st_locs2, pnat, length1, length2, st1, st2 in *. simpl in *.
       intros ? ?. eapply envt_store_deep_wf in H8; eauto. unfold pnat, length2, st2 in H8. lia. 
       eapply envt_store_deep_wf; eauto. 
     + intros. simpl in E. specialize (E l1 l2); intuition. unfold strel in H8. simpl in H8. rewrite <- H8. 
       eapply functional_extensionality. intros. eapply functional_extensionality. intros.
       eapply propositional_extensionality. split; intros; intuition.
       ++ eapply SEP1X; eauto. 
       ++ intros ? ?. destruct H8 as [[? | ?] ?]. 
          assert (l2 < length (st2 M)) as X. {  eapply envt_store_deep_wf in H5; eauto. }
          destruct H8.
          assert (x1 < length (st2 M)). {  
            inversion H10; subst. unfold pone in H12. subst x1. eapply envt_store_deep_wf. eapply WFE. 2: eapply H5. eauto.  
            unfold pone in H12. subst x3. eapply lls_indexr_closed'' in H13. eapply H13 in H14. unfold pnat in H14. lia. eapply ST; eauto.
          }
          unfold pnat, length2 in H11. lia.
          eapply envt_same_locs in H4; eauto.
          assert (locs_locs_stty (st2 M) (pone x1) x1). left. unfold pone. auto.
          eapply lls_filter in H10. eapply H10 in H11. eapply lls_filter in H4. eapply H4 in H11. contradiction.
        ++ split. 2: split. intros. 
           eapply SEP1X; eauto. 
       
          intros ? ?. unfold pdiff, pnat in H7. destruct H7 as [[[? ?] | ?] ?]. 
          eapply lls_filter in H10. 
          assert (locs_locs_stty (st2 M) (pone x) x). left. unfold pone. auto.
          eapply H10 in H11. eapply lls_filter in H5. eapply H5 in H11. eapply envt_store_deep_wf in H11; eauto. unfold pnat in H11. contradiction.
       
          assert (locs_locs_stty (st2 M) (pone x) x). left. unfold pone. auto.
          eapply lls_filter in H9. eapply H9 in H10. eapply lls_filter in H5. eapply H5 in H10. contradiction.
          auto.

     + intros. unfold strel in F. simpl in F. specialize (F l1 l2); intuition. eapply H4; auto.
       intros ?. eapply SEP1X; eauto. 
       split.
       intros ? ?. destruct H9 as [[? | ?] ?].
       unfold pdiff, pnat in H9.
       eapply lls_filter in H6 as H6'. eapply H6' in H10. eapply envt_store_deep_wf in H10; eauto. unfold pnat, st2 in H10. lia.

       assert (locs_locs_stty (st2 M) (pone x) x). left. unfold pone. auto.
       eapply lls_filter in H6. eapply H6 in H10. eapply lls_filter in H10. eapply H10 in H11. contradiction.       
       auto.
  }

  assert (st_chain_partial M M'' (locs_locs_stty (st1 M) (vars_locs H1 (plift p2))) (locs_locs_stty (st2 M) (vars_locs H2 (plift p2)))) as SXMP3. {
     eapply stchain_tighten with (p1' := (locs_locs_stty (st1 M) (vars_locs H1 (plift p2))))(p2':= (locs_locs_stty (st2 M) (vars_locs H2 (plift p2)))) in STC'' as R.
     2: {
       unfold st_filter. split. 2: split.
       + unfold st_locs1, pnat, length1, st1. simpl. intros ? ?. eapply envt_store_deep_wf in H4; eauto. unfold pnat, length1, st1 in *. lia. 
       + unfold st_locs2, pnat, length2, st2. simpl. intros ? ?. eapply envt_store_deep_wf in H4; eauto.
       + intros. unfold strel in H4. simpl in H4. destruct H4 as [? [? ?]].
         split. intros. eapply envt_filter_deep; eauto.
         intros. eapply envt_filter_deep; eauto.
     }
     2: {
      unfold st_locs1, pnat, length1, st1. simpl. intros ? ?. eapply envt_store_deep_wf in H4; eauto.  unfold pnat, length1, st1 in *. lia. 
     }
     2: {
       unfold st_locs2, pnat, length2, st2. simpl. intros ? ?. eapply envt_store_deep_wf in H4; eauto. 
     }
     destruct R as [A [B [C [D [E F]]]]].
     unfold st_chain_partial. split. 2: split. 3: split. 4: split. 5: split.
     + eapply envt_filter_deep; eauto.
     + auto.
     + unfold st1 in C. simpl in C. unfold st1. eapply sst_trans''; eauto. eapply sstchain_tighten; eauto. eapply STC'; eauto. eapply envt_store_deep_wf; eauto. eapply envt_store_deep_wf; eauto. 
     + unfold st2 in D. simpl in D. unfold st2. auto. 
     + intros ? ?. simpl in E. specialize (E l1 l2); intuition. rewrite <- H8. 
       eapply functional_extensionality. intros. eapply functional_extensionality. intros.
       eapply propositional_extensionality. split; intros; intuition. eapply SEP1; eauto. 
       intros ? ?. destruct H9 as [[? | ?] ?]. 
       unfold pdiff, pnat in H9. eapply lls_filter in H4. eapply H4 in H10. eapply envt_store_deep_wf in H10; eauto.  unfold pnat, st1 in H10. lia.

       assert (locs_locs_stty (st1 M) (pone x1) x1). left. unfold pone. auto.
       eapply lls_filter in H10. eapply H10 in H11. eapply lls_filter in H4. eapply H4 in H11. contradiction.

       unfold strel in *. simpl in *.  split. intros ?. eapply SEP1; eauto. 
       split.
       intros ? ?. destruct H7 as [[? | ?] ?]. 
       unfold pdiff, pnat in H7. eapply lls_filter in H4. eapply H4 in H9. eapply envt_store_deep_wf in H9; eauto. unfold pnat, st1 in H9. lia.

       assert (locs_locs_stty (st1 M) (pone x) x). left. unfold pone. auto.
       eapply lls_filter in H9. eapply H9 in H10. eapply lls_filter in H4. eapply H4 in H10. contradiction.
       auto.
       
     + intros. unfold strel in F. simpl in F. specialize (F l1 l2); intuition. eapply H4; auto.
       intros ?. eapply SEP1; eauto. 
       split.
       intros ? ?. destruct H9 as [[? | ?] ?].
       
       unfold pdiff, pnat in H9. eapply lls_filter in H5. eapply H5 in H10. 
       eapply envt_store_deep_wf in H10; eauto. unfold pnat, st1 in H10. lia.
       
       assert (locs_locs_stty (st1 M) (pone x) x). left. unfold pone. auto.
       eapply lls_filter in H10. eapply H10 in H11. eapply lls_filter in H5. eapply H5 in H11. contradiction.

       auto.
  }

  remember ST''' as ST'''x. clear HeqST'''x.
  destruct ST'''x  as [SST1''' [SST2''' [STREL''' [M'''R M'''L]]]].

  remember ST'' as ST''x. clear HeqST''x.
  destruct ST''x as [SST1''x [SST2''x [STX'' [STR'' STL'']]]].
  
  
  assert (length S1' = length1 M''') as L3. { destruct SST1''' as [X ?]. unfold length1. lia.  }
  assert (length S2' = length2 M'') as L4. { destruct ST'' as [? [ [X ?] ? ]]. unfold st2 in *. unfold length2, st2. lia. }
  assert (length S2 <= length S2') as L5. auto.
  assert (length S1' <= length S1'') as L6. { eapply st_mono1 in STC''.  unfold length1, st1 in *. simpl in *.  
    destruct ST'' as [[A ?] B]. unfold st1, length1 in *. lia.
  }
  assert (length S2'' = length2 M''') as L7. { destruct ST''' as [? [[X ?] ?]].   unfold length2. lia. }
  assert (length S2' <= length S2'') as L8. { eapply st_mono2 in STC'''. unfold length2, st2 in *. simpl in *. lia. }
  assert (length S1'' = length1 M'') as L9. { destruct ST'' as [[X ?] ?]. unfold length1, st1 in *. simpl in *. lia. }
  assert (length1 M <= length1 M'') as L10. { eapply st_mono1 in STC''. unfold length1, st1 in *. simpl in *. lia. }


  assert (forall l1 l2,
               l1 < length S1 /\ l2 < length S2' ->
               strel M''' l1 l2 ->
               ~ (locs_locs_stty (st2 M) (vars_locs H2 (plift p2) ) l2) /\ 
               psub(pand (por (pdiff (pnat (length2 M'')) (pnat (length2 M))) (pnot (locs_locs_stty (st2 M) (vars_locs H2 (plift p1)))))(locs_locs_stty (st2 M) (pone l2))) pempty /\    
               strel M l1 l2
      ) as CES'''. {
    intros.  eapply STC'''. unfold st_locs1, st_locs2, length1, length2, st_empty, pnat, st1, st2. simpl.
    destruct H4. split. unfold length1, st1 in *.  lia. unfold length2, st2 in *. lia. auto.
  }

  assert (forall l1 l2,
               l1 < length S1' /\ l2 < length S2 ->
               strel M'' l1 l2 ->
               ~ (locs_locs_stty (st1 M) (vars_locs H1 (plift p1)) l1) /\ 
               psub(pand (por (pdiff (pnat (length1 M')) (pnat (length1 M))) (pnot (locs_locs_stty (st1 M) (vars_locs H1 (plift p2)))))(locs_locs_stty (st1 M) (pone l1))) pempty /\    
               strel M l1 l2) as CES''. {
      intros. eapply STC''. unfold st_locs1, st_locs2, length1, length2, st_empty, pnat, st1, st2. simpl. 
      split. unfold length1, length2, st1, st2 in *. lia.  unfold length2, st2 in *. lia.   auto.
  }

  remember ((st1 M''), (st2 M'''),
  fun l1 l2 =>
    strel M l1 l2 /\
      ~ (locs_locs_stty (st1 M) (vars_locs H1 (plift p1))) l1 /\
      ~ (locs_locs_stty (st2 M) (vars_locs H2 (plift p1))) l2 /\
      ~ (locs_locs_stty (st1 M) (vars_locs H1 (plift p2))) l1 /\
      ~ (locs_locs_stty (st2 M) (vars_locs H2 (plift p2))) l2 \/
    strel M''' l1 l2 /\
       ((locs_locs_stty (st1 M) (vars_locs H1 (plift p1))) l1 /\
       (locs_locs_stty (st2 M) (vars_locs H2 (plift p1))) l2 \/
       ~ l1 < length1 M /\ l1 < length1 M' /\ l1 < length1 M''' /\ 
       (psub(pand (por (pdiff (pnat (length1 M')) (pnat (length1 M))) (pnot (locs_locs_stty (st1 M) (vars_locs H1 (plift p2)))))(locs_locs_stty (st1 M) (pone l1)))) pempty /\
       ~ l2 < length2 M /\ ~ l2 < length2 M'' /\ l2 < length2 M''' ) \/
     (* ~ vars_locs H2 (plift p2) l1 /\
      ~ vars_locs H3 (plift p2) l2 \/ *)
    strel M'' l1 l2 /\
     (* ~ vars_locs H2 (plift p1) l1 /\
      ~ vars_locs H3 (plift p1) l2  *)
       ((locs_locs_stty (st1 M) (vars_locs H1 (plift p2))) l1 /\
        (locs_locs_stty (st2 M) (vars_locs H2 (plift p2))) l2 \/
       ~ l1 < length1 M /\  ~ l1 < length1 M' /\ l1 < length1 M'' /\ 
       ~ l2 < length2 M /\ l2 < length2 M'' /\ 
       psub(pand (por (pdiff (pnat (length2 M'')) (pnat (length2 M))) (pnot (locs_locs_stty (st2 M) (vars_locs H2 (plift p1)))))(locs_locs_stty (st2 M) (pone l2))) pempty     
       ),
   fun l1 l2 v1 v2 =>
       st_valtype M l1 l2 v1 v2 /\
         ~ (locs_locs_stty (st1 M) (vars_locs H1 (plift p1))) l1 /\
         ~ (locs_locs_stty (st2 M) (vars_locs H2 (plift p1))) l2 /\
         ~ (locs_locs_stty (st1 M) (vars_locs H1 (plift p2))) l1 /\
         ~ (locs_locs_stty (st2 M) (vars_locs H2 (plift p2))) l2 \/
       st_valtype M''' l1 l2 v1 v2 /\
         ((locs_locs_stty (st1 M) (vars_locs H1 (plift p1))) l1 /\
         (locs_locs_stty (st2 M) (vars_locs H2 (plift p1))) l2 \/
         ~ l1 < length1 M /\ l1 < length1 M' /\ l1 < length1 M''' /\ 
         (psub(pand (por (pdiff (pnat (length1 M')) (pnat (length1 M))) (pnot (locs_locs_stty (st1 M) (vars_locs H1 (plift p2)))))(locs_locs_stty (st1 M) (pone l1)))) pempty /\
         ~ l2 < length2 M /\ ~ l2 < length2 M'' /\ l2 < length2 M''')     
       \/ 
       st_valtype M'' l1 l2 v1 v2 /\
         ((locs_locs_stty (st1 M) (vars_locs H1 (plift p2))) l1 /\
           (locs_locs_stty (st2 M) (vars_locs H2 (plift p2))) l2 \/
           ~ l1 < length1 M /\  ~ l1 < length1 M' /\ l1 < length1 M'' /\
           ~ l2 < length2 M /\ l2 < length2 M'' /\ 
           psub(pand (por (pdiff (pnat (length2 M'')) (pnat (length2 M))) (pnot (locs_locs_stty (st2 M) (vars_locs H2 (plift p1)))))(locs_locs_stty (st2 M) (pone l2))) pempty     
         )
  ) as MM.

  assert (forall a b, a || b = b || a) as RS. { intros. eauto with bool. }

  assert (sst_chain_partial (fst (fst (fst M))) (fst (fst (fst M''))) (st_locs1 M)) as STCMM''1. {
    unfold st1, st_locs1, pnat, length1, st1 in *. 
    eapply sst_trans''' with (M2 := (st1 M')). 
    destruct STC' as [? [? ?]]. intuition. eapply STC''; eauto. 
    intros ? ?. auto. intros ? ?. simpl. 
    unfold st1, st_locs1, pnat, length1, st1, pdom in *. simpl. lia.
  }

  assert (sst_chain_partial (snd (fst (fst M))) (snd (fst (fst M'''))) (st_locs2 M)) as STCMM'''2. {
    destruct STC''' as [Ax [Bx [Cx [Dx Ex]]]]. unfold st2, st_locs2, pnat, length2, st2 in Dx. 
    destruct STC'' as [A [B [C [D E]]]].  unfold st2, st_locs2, pnat, length2, st2 in D. 
    eapply sst_trans'''; eauto. intros ? ?. auto. intros ? ?. simpl. unfold st_locs2, pnat, length2, st2 in *. lia.
  } 



  assert (st_chain M MM). {
    subst MM. unfold st_chain. unfold st_chain_partial. split. 2: split. 3: split. 4: split. 5: split.
    - auto. 
    - repeat split.
      * unfold st_locs1, pnat, length1, st1 in *. intros ? ?. simpl in *. lia.
      * unfold st_locs2, pnat, length2, st2 in *. intros ? ?. simpl in *. lia. 
      * intros X. unfold strel in H4. simpl in H4. unfold st_locs2, pnat, length2, st2. 
        destruct H4. destruct H4 as [? [? [? [? ?]]]]. eapply STF; eauto.
        destruct H4. destruct H4 as [? [[? ?] | [? [? [? ?]]]]].  
        eapply envt_store_deep_wf in H6; eauto. 
        unfold st_locs1, pnat, length1, st1 in *. contradiction.  
        destruct H4 as [? [[? ?] | [? [? ?]]]].  
        eapply envt_store_deep_wf in H6; eauto. 
        unfold st_locs1, pnat, length1, st1 in *. contradiction.  
      * intros X. unfold strel in H4. simpl in H4. unfold st_locs1, pnat, length1, st1. 
        destruct H4. destruct H4 as [? [? [? [? ?]]]]. eapply STF; eauto.
        destruct H4. destruct H4 as [? [[? ?] | [? [? [? [? [? ?]]]]]]].  
        eapply envt_store_deep_wf in H5; eauto. 
        unfold st_locs2, pnat, length2, st2 in *. contradiction.  
        destruct H4 as [? [[? ?] | [? [? [? [? ?]]]]]].  
        eapply envt_store_deep_wf in H5; eauto. 
        unfold st_locs2, pnat, length2, st2 in *. contradiction.  
        
    - (* sst_chain_partial 1 *)
        unfold st1, st_locs1, pnat, length1, st1. simpl in *. eauto.
        
    - (* sst_chain_partial 2 *)
        unfold st2, st_locs2, pnat, length2, st2. simpl in *. eauto.
        
    - (* st_valtype *)    
      intros. simpl. eapply functional_extensionality. intros. eapply functional_extensionality. intros.
      eapply propositional_extensionality. 
      split; intros. 
      * assert (locs_locs_stty (st1 M) (vars_locs H1 (plift p1)) l1 \/ ~ locs_locs_stty (st1 M) (vars_locs H1 (plift p1)) l1). { rewrite plift_vars_locs.  eapply val_locs_stty_decide. eapply ST; eauto. }
        assert (locs_locs_stty (st2 M) (vars_locs H2 (plift p1)) l2 \/ ~locs_locs_stty (st2 M) (vars_locs H2 (plift p1)) l2). { rewrite plift_vars_locs.  eapply val_locs_stty_decide. eapply ST; eauto. }
        assert (locs_locs_stty (st1 M) (vars_locs H1 (plift p2)) l1 \/ ~locs_locs_stty (st1 M) (vars_locs H1 (plift p2)) l1). { rewrite plift_vars_locs.  eapply val_locs_stty_decide. eapply ST; eauto. }
        assert (locs_locs_stty (st2 M) (vars_locs H2 (plift p2)) l2 \/ ~locs_locs_stty (st2 M) (vars_locs H2 (plift p2)) l2). { rewrite plift_vars_locs.  eapply val_locs_stty_decide. eapply ST; eauto. }
        destruct H8; destruct H9; destruct H10; destruct H11.
        ** (*   p1 l1,   p1 l2,   p2 l1,   p2 l2 *)
           edestruct (SEP1 l1); eauto. 
        ** (*   p1 l1,   p1 l2,   p2 l1, ~ p2 l2 *)
           edestruct (SEP1 l1); eauto. 
        ** (*   p1 l1,   p1 l2, ~ p2 l1,   p2 l2 *)
           edestruct (SEP1X l2); eauto.
        ** (*   p1 l1,   p1 l2, ~ p2 l1, ~ p2 l2 *)
           right. left. 
           repeat split; auto. 
           destruct STC''' as [? [? [? [? [STY ?]]]]]. 
           unfold st_locs1, st_locs2, pnat, length1, length2, st1, st2 in STY. simpl in STY.
           rewrite <- STY. split. intros. eapply H11. eapply lls_mono; eauto. eapply vars_locs_mono; eauto. unfoldq; intuition. 
           split. intros ? ?. destruct H17 as [[? | ?] ?].
           unfold pdiff, pnat in H17. destruct H17. eapply lls_filter in H9. eapply H9 in H18.  eapply envt_store_deep_wf in H18; eauto. unfold pnat, length2, st2 in *. lia.
           assert (locs_locs_stty (st2 M) (pone x1) x1). left. unfold pone. auto.
           eapply lls_filter in H18. eapply H18 in H19. eapply lls_filter in H9. eapply H9 in H19. contradiction. 
           auto.
           eapply envt_store_deep_wf in H8; eauto. 
           eapply envt_store_deep_wf in H9; eauto. unfold st_locs2, pnat, length2, st2 in *. lia.
           unfold strel. simpl. split. intros. 
           eapply H11. eapply lls_mono; eauto. eapply vars_locs_mono; eauto. unfoldq; intuition.
           split.
           intros ? ?. destruct H17. unfold pdiff in H17. destruct H17. 
           eapply lls_filter in H9; eauto. eapply H9 in H18; eauto.  
           eapply envt_store_deep_wf in H18; eauto. unfold pdiff, pnat, length2, st2 in *. lia.
           
           assert (locs_locs_stty (st2 M) (pone x1) x1). left. unfold pone. auto.
           eapply lls_filter in H18. eapply H18 in H19. eapply lls_filter in H9. eapply H9 in H19. contradiction.
           auto. 
        ** (*   p1 l1, ~ p1 l2,   p2 l1,   p2 l2 *)
           edestruct (SEP1 l1); eauto.
        ** (*   p1 l1, ~ p1 l2,   p2 l1, ~ p2 l2 *)
           edestruct (SEP1 l1); eauto.
        ** (*   p1 l1, ~ p1 l2, ~ p2 l1,   p2 l2 *)
           edestruct (SEP2 l1 l2); eauto.
        ** (*   p1 l1, ~ p1 l2, ~ p2 l1, ~ p2 l2 *)
           edestruct (SEP2); eauto.
          
        ** (* ~ p1 l1,   p1 l2,   p2 l1,   p2 l2 *)
           edestruct (SEP1X l2); eauto.
        ** (* ~ p1 l1,   p1 l2,   p2 l1, ~ p2 l2 *)
           edestruct (SEP3); eauto.
        ** (* ~ p1 l1,   p1 l2, ~ p2 l1,   p2 l2 *)
           edestruct (SEP1X l2); eauto.
        ** (* ~ p1 l1,   p1 l2, ~ p2 l1, ~ p2 l2 *)
           edestruct (SEP4); eauto. 
        ** (* ~ p1 l1, ~ p1 l2,   p2 l1,   p2 l2 *)
           right. right. repeat split; auto.
           destruct STC'' as [? [? [? [? [STY ?]]]]]. 
           unfold st_locs1, st_locs2, pnat, length1, length2, st1, st2 in STY. simpl in STY.
           rewrite <- STY. split. intros. eapply H8. eapply lls_mono; eauto. eapply vars_locs_mono; eauto. unfoldq; intuition.
           split; auto.
           intros ? ?. destruct H17 as [[? | ?] ?].
           
           unfold pdiff in H17. destruct H17. eapply lls_filter in H10; eauto. eapply H10 in H18; eauto. 
           eapply envt_store_deep_wf in H18; eauto. unfold pnat, length1, st1 in *. lia.
           
           assert (locs_locs_stty (st1 M) (pone x1) x1). left. unfold pone. auto.
           eapply lls_filter in H18. eapply H18 in H19. eapply lls_filter in H10. eapply H10 in H19. contradiction. 
           
           eapply envt_store_deep_wf in H10; eauto. unfold pnat, length1, st1 in *. lia.
           eapply envt_store_deep_wf in H11; eauto.
           unfold strel. simpl. split. intros. eapply H8. eapply lls_mono; eauto. eapply vars_locs_mono; eauto. unfoldq; intuition. 
           split; auto.
           intros ? ?. destruct H17. unfold pdiff in H17. destruct H17. eapply lls_filter in H10; eauto. eapply H10 in H18; eauto.  
           eapply envt_store_deep_wf in H18; eauto. unfold pnat, length1, st1 in *. lia.
           
           assert (locs_locs_stty (st1 M) (pone x1) x1). left. unfold pone. auto.
           eapply lls_filter in H18. eapply H18 in H19. eapply lls_filter in H10. eapply H10 in H19. contradiction. 
           
        ** (* ~ p1 l1, ~ p1 l2,   p2 l1, ~ p2 l2 *)
            edestruct (SEP3); eauto. 
        ** (* ~ p1 l1, ~ p1 l2, ~ p2 l1,   p2 l2 *)
            edestruct (SEP5); eauto. 
        ** (* ~ p1 l1, ~ p1 l2, ~ p2 l1, ~ p2 l2 *)
            intuition. (* M *)
      * destruct H7 as [[? [? [? [? ?]]]] | [[? ?] | [? ?]]]. 
        ** auto. 
        ** destruct STC''' as [? [? [? [? [STY ?]]]]]. 
           destruct H8 as [[? ?] | [? [? [? [? ?]]]]].
           unfold st_locs1, st_locs2, pnat, length1, length2, st1, st2, strel in *. simpl in *.
           assert (l2 < length (snd (fst (fst M'')))). lia.
           erewrite <- STY in H7; eauto. destruct H7 as [? [? ?]]. auto.
           split. intros ?. eapply SEP1X; eauto. 
           split.
           intros ? ?. destruct H16 as [[? | ?] ?].
           unfold pdiff in H16. destruct H16. 
           eapply lls_filter in H14; eauto. eapply H14 in H17; eauto. eapply envt_store_deep_wf in H17; eauto. unfold pnat, length2, st2 in *. lia.
           assert (locs_locs_stty (st2 M) (pone x1) x1). left. unfold pone. auto.
           eapply lls_filter in H17. eapply H17 in H18. eapply lls_filter in H14. eapply H14 in H18. contradiction.  
            
           erewrite <- STY in H7; eauto; simpl in H7. split. 
           intros. eapply SEP1X; eauto. 
           split. intros ? ?. destruct H16 as [[? | ?] ?].
           unfold pdiff in H16. destruct H16. eapply lls_filter in H14; eauto. eapply H14 in H17; eauto. eapply envt_store_deep_wf in H17; eauto. unfold pnat, length2, st2 in *. lia.
           eapply lls_filter in H14. eapply H14 in H17. contradiction.
           auto.   
           unfold st_locs1, st_locs2, pnat, length1, length2, st1, st2 in *. simpl in *. contradiction.
        ** destruct STC'' as [? [? [? [? [STY ?]]]]]. 
           unfold st_locs1, st_locs2, pnat, length1, length2, st1, st2 in *. simpl in *.
           assert (l1 < length (fst (fst (fst M')))). lia.
           rewrite <- STY in H7. destruct H7 as [? [? ?]]. auto. auto. auto.
           destruct H8 as [[? ?] | [? [? [? [? ?]]]]];  
           unfold strel in *; simpl in *; split. 
           intros ?.  eapply SEP1; eauto. 
           split. 
           intros ? ?. destruct H16 as [[? | ?] ?].
           unfold pdiff in H16. destruct H16. eapply lls_filter in H8; eauto. eapply H8 in H17; eauto.  
           eapply envt_store_deep_wf in H17; eauto. unfold pnat, length1, st1 in *. lia.
           
           assert (locs_locs_stty (st1 M) (pone x1) x1). left. unfold pone. auto.
           eapply lls_filter in H17. eapply H17 in H18. eapply lls_filter in H8. eapply H8 in H18. contradiction.
           auto.
           intros ?. eapply envt_store_deep_wf in H19; eauto. 
           split.
           contradiction. contradiction.
    - (* strel *)
      intros. unfold strel. simpl. split; intros.
      + assert (locs_locs_stty (st1 M) (vars_locs H1 (plift p1)) l1 \/ ~ locs_locs_stty (st1 M) (vars_locs H1 (plift p1)) l1). { rewrite plift_vars_locs.  eapply val_locs_stty_decide. eapply ST; eauto. }
        assert (locs_locs_stty (st2 M) (vars_locs H2 (plift p1)) l2 \/ ~locs_locs_stty (st2 M) (vars_locs H2 (plift p1)) l2). { rewrite plift_vars_locs.  eapply val_locs_stty_decide. eapply ST; eauto. }
        assert (locs_locs_stty (st1 M) (vars_locs H1 (plift p2)) l1 \/ ~locs_locs_stty (st1 M) (vars_locs H1 (plift p2)) l1). { rewrite plift_vars_locs.  eapply val_locs_stty_decide. eapply ST; eauto. }
        assert (locs_locs_stty (st2 M) (vars_locs H2 (plift p2)) l2 \/ ~locs_locs_stty (st2 M) (vars_locs H2 (plift p2)) l2). { rewrite plift_vars_locs.  eapply val_locs_stty_decide. eapply ST; eauto. }
                
        destruct H6; destruct H7; destruct H8; destruct H9.
        * (*   p1 l1,   p1 l2,   p2 l1,   p2 l2 *)
          edestruct (SEP1 l1); eauto. 
        * (*   p1 l1,   p1 l2,   p2 l1, ~ p2 l2 *)
          edestruct (SEP1 l1); eauto. 
        * (*   p1 l1,   p1 l2, ~ p2 l1,   p2 l2 *)
          edestruct (SEP1X l2); eauto.
        * (*   p1 l1,   p1 l2, ~ p2 l1, ~ p2 l2 *)
          right. left. split. eapply STC'''; eauto.
          unfold st_locs1, st_locs2, pnat, length1, length2, st1, st2 . simpl.
          split. unfold st_locs1, pnat, length1, st1 in *. lia.
          unfold st_locs2, pnat, length2, st2 in *. lia.
          unfold strel. simpl. split. intros ?. eapply H9. eapply lls_mono; eauto. eapply vars_locs_mono; eauto. unfoldq; intuition. 
          split; auto.
          intros ? ?. destruct H10 as [[? | ?] ?].
          
          unfold pdiff in H10. destruct H10. eapply lls_filter in H7. eapply H7 in H11; eauto.  
          eapply envt_store_deep_wf in H11; eauto. unfold pnat, length2, st2 in *. lia. 
          assert (locs_locs_stty (st2 M) (pone x) x). left. unfold pone. auto.
          eapply lls_filter in H11. eapply H11 in H12. eapply lls_filter in H7. eapply H7 in H12. contradiction. 
          
          left. split. auto. auto.
        * (*   p1 l1, ~ p1 l2,   p2 l1,   p2 l2 *)
          edestruct (SEP1 l1); eauto.
        * (*   p1 l1, ~ p1 l2,   p2 l1, ~ p2 l2 *)
          edestruct (SEP1 l1); eauto.
        * (*   p1 l1, ~ p1 l2, ~ p2 l1,   p2 l2 *)
          right. left. 
          edestruct (SEP2); eauto. 
        * (*   p1 l1, ~ p1 l2, ~ p2 l1, ~ p2 l2 *)
          right. left. 
          edestruct (SEP2); eauto.
          
        * (* ~ p1 l1,   p1 l2,   p2 l1,   p2 l2 *)
          edestruct (SEP1X l2); eauto.
        * (* ~ p1 l1,   p1 l2,   p2 l1, ~ p2 l2 *)
          right. right. edestruct (SEP3); eauto.
        * (* ~ p1 l1,   p1 l2, ~ p2 l1,   p2 l2 *)
          edestruct (SEP1X l2); eauto.
        * (* ~ p1 l1,   p1 l2, ~ p2 l1, ~ p2 l2 *)
          edestruct (SEP4); eauto.
          
        * (* ~ p1 l1, ~ p1 l2,   p2 l1,   p2 l2 *)
          right. right. split.  (* M'' *)
          eapply STC''. unfold st_locs1, st_locs2, pnat, length1, length2, st1, st2. simpl.
          split. unfold st_locs1, pnat, length1, st1 in *. lia.
          unfold st_locs2, pnat, length2, st2 in *. lia.
          unfold strel. simpl. split. intros ?. eapply H6. eapply lls_mono; eauto. eapply vars_locs_mono; eauto. unfoldq; intuition.
          split; auto.
          intros ? ?. destruct H10 as [[? | ?] ?].
          
          unfold pdiff in H10. destruct H10. eapply lls_filter in H8; eauto. eapply H8 in H11; eauto.  
          eapply envt_store_deep_wf in H11; eauto. unfold pnat, length1, st1 in *. lia.
          assert (locs_locs_stty (st1 M) (pone x) x). left. unfold pone. auto.
          eapply lls_filter in H11. eapply H11 in H12. eapply lls_filter in H8. eapply H8 in H12. contradiction. 
          
          left; auto. 
          
        * (* ~ p1 l1, ~ p1 l2,   p2 l1, ~ p2 l2 *)
          edestruct (SEP3); eauto.
        * (* ~ p1 l1, ~ p1 l2, ~ p2 l1,   p2 l2 *)
          edestruct (SEP5); eauto.
        * (* ~ p1 l1, ~ p1 l2, ~ p2 l1, ~ p2 l2 *)
          left. intuition. (* M *)
      + destruct H5. destruct H5. auto.
        destruct H5. destruct H5 as [? [? | ?]]. destruct H6 as [? ?].
        eapply CES'''; auto. split.
        unfold st_locs1, pnat, length1, st1 in *. lia.
        unfold st_locs2, pnat, length2, st2 in *. lia.
        eapply STC'''; eauto.
        unfold st_locs1, pnat, length1, st1 in *. lia.
        destruct H5 as [? ?]. eapply CES''; auto. split. 
        unfold st_locs1, pnat, length1, st1 in *. lia.
        unfold st_locs2, pnat, length2, st2 in *. lia.
  } 
  
  assert (st_chain_partial M MM (locs_locs_stty (st1 M) (vars_locs H1 (plift p1))) (locs_locs_stty (st2 M) (vars_locs H2 (plift p1)))) as SRMP1. {
     eapply stchain_tighten; eauto. eapply envt_filter_deep; eauto. 
     1,2: eapply envt_store_deep_wf; eauto. 
  } 

  assert (store_effect S1 S1'' (locs_locs_stty (st1 M) (vars_locs H1 (por (plift p1) (plift p2))))) as SSE1.  {
    eapply se_trans. eapply se_sub. eauto. unfold st1. simpl. eapply lls_mono. eapply vars_locs_mono; eauto. unfoldq; intuition.
    eapply se_sub. eauto. unfold st1. simpl. erewrite <- lls_change with (M := (st1 M)). eapply lls_mono; eauto. eapply vars_locs_mono; eauto. unfoldq; intuition.
    eapply sstchain_tighten; eauto. eapply STC'; eauto. eapply envt_store_deep_wf; eauto. 
  }

  assert (store_effect S2 S2'' (locs_locs_stty (st2 M) (vars_locs H2 (por (plift p1)(plift p2) )))) as SSE2. {
    eapply se_trans. eapply se_sub. eauto. unfold st2. simpl. eapply lls_mono. eapply vars_locs_mono; eauto. unfoldq; intuition.
    eapply se_sub. eauto. unfold st2. simpl. erewrite <- lls_change with (M := (st2 M)). eapply lls_mono; eauto. eapply vars_locs_mono; eauto. unfoldq; intuition.
    eapply sstchain_tighten; eauto. eapply STC''; eauto. intros ? ?. unfold st_locs2, pnat, length2, st2. simpl.
    eapply envt_store_deep_wf with (q := (plift p1)). eapply WFE. auto. eapply lls_mono; eauto. eapply vars_locs_mono; eauto. unfoldq; intuition.
  }

  assert (st_filter MM (st_locs1 MM)(st_locs2 MM)) as SRF. {
    subst MM. simpl. split. 2: split.
    + intros ? ?. auto.
    + intros ? ?. auto.
    + intros. unfold strel in H5. simpl in H5. unfold st_locs1, st_locs2, pnat, length1, length2, st1, st2. simpl.
      destruct H5 as [A | [B | C]].
      - destruct A as [A A']. eapply strel_wf in A; eauto. unfold length1, length2, st1, st2 in *. destruct A. split; intros; lia.
      - destruct B as [? [B1 | B2]]. destruct B1. eapply envt_store_deep_wf in H6, H7; eauto.
        unfold pnat, length1, length2, st1, st2 in *. split; intros; lia.
        destruct B2 as [? [? [? [? [? [? ?]]]]]]. split; intros. auto.  eapply st_mono1 in STC''; eauto. unfold length1, st1 in *. lia.
      - destruct C as [? [C1 | C2]]. destruct C1. eapply envt_store_deep_wf in H6, H7; eauto.
        unfold pnat, length1, length2, st1, st2 in *. split; intros; lia.
        destruct C2 as [? [? [? [? ?]]]]. split; intros. eapply st_mono2 in STC'''. unfold length2, st2 in *. lia.   
        eapply st_mono1 in STC''; eauto. 
  }

  assert (sst_chain_partial (st1 M')(st1 M'')(locs_locs_stty (st1 M')(vars_locs H1 (plift p1)))) as XXYY. {
    repeat split.
    + intros ? ?. erewrite <- lls_change with (M := (st1 M)) in H5.  eapply envt_store_deep_wf in H5; eauto. unfold pnat, length1, st1, pdom in *. lia.
      eapply sstchain_tighten. eapply STC'; eauto. eapply envt_store_deep_wf; eauto.
    + intros ? ?. erewrite <- lls_change with (M := (st1 M)) in H5.  eapply envt_store_deep_wf in H5; eauto. unfold pnat, length1, st1, pdom in *. lia.
      eapply sstchain_tighten. eapply STC'; eauto. eapply envt_store_deep_wf; eauto.
    + intros.  erewrite <- lls_change with (M := st1 M) in H5. 
      2: { eapply sstchain_tighten. eapply STC'; eauto. eapply envt_store_deep_wf; eauto. }
      assert (indexr l (st1 M) = indexr l (st1 M')). { eapply STC'; eauto. eapply envt_store_deep_wf in H5; eauto. }
      assert (indexr l (st1 M) = indexr l (st1 M'')). { eapply sstchain_tighten. eapply STCMM''1. 2: eauto.  eapply envt_store_deep_wf; eauto. }
      congruence.
  }

  assert (sst_chain_partial (st1 M'') (st1 M''') (locs_locs_stty (st1 M) (vars_locs H1 (plift p1)))) as X1Y1. {
    repeat split.
    + intros ? ?. eapply envt_store_deep_wf in H5; eauto. unfold pnat, length1, st1, pdom in *. lia.
    + intros ? ?. eapply envt_store_deep_wf in H5; eauto. unfold pnat, length1, st1, pdom in *. lia.
    + intros ? ?. 
      assert (indexr l (st1 M) = indexr l (st1 M'')). { 
        eapply sstchain_tighten. eapply sst_trans'''. eapply sstchain_tighten. eapply STC'. 6: eauto. 2: eauto. 
        3: { intros ? ?. eauto. } 
        erewrite <- lls_change. 2: { eapply sstchain_tighten. eapply STC'. eapply envt_store_deep_wf; eauto. } eapply envt_store_deep_wf; eauto. 
        erewrite <- lls_change. 2: { eapply sstchain_tighten. eapply STC'. eapply envt_store_deep_wf; eauto. } eapply envt_store_deep_wf; eauto.
        intros ? ?. erewrite <- lls_change; eauto. eapply sstchain_tighten. eapply STC'. eapply envt_store_deep_wf; eauto.  }
      assert (indexr l (st1 M) = indexr l (st1 M''')). { eapply SXMP2; eauto. }
      congruence.
  }
 
   (* invariants in exp_type:
       1. store_preserve: store outside of vars_locs p is unchanged
       2: st_chain: M1 is a conservative extension of M, i.e., only adds entries larger than size of M *)
  assert (store_type S1'' S2'' MM). {
    subst MM. remember ST as STT. clear HeqSTT. 
    destruct ST as (SST1 & SST2 & STREL & STR & STL). split. 2: split. 3: split. 4: split. 
    - unfold st1. simpl. eapply ST''; eauto.
    - intuition.
    - intros. destruct H5 as [A | [B | C]].
      + (* strel M l1 l2 but not in p1 or p2 *)
        destruct A as (? & ? & ? & ? & ?).
        unfold st1 at 1. simpl. unfold st2 at 1. simpl.
        
        destruct (STREL l1 l2) as (vtx & qt1x & qt2x & v1'x & v2'x & ? & ? & ? & ? & ? & ? & ?). eauto.
        exists vtx, qt1x, qt2x, v1'x, v2'x. split. 2: split. 3: split. 4: split. 5: split. 6: split.
        * assert (sst_chain (st1 M)(st1 M'')). { eapply sst_trans. eapply STC'; eauto.  eapply STC''; eauto. }
          destruct H17 as [HA [HB HC]]. assert (l1 < length (st1 M)). apply indexr_var_some' in H10. lia.
          unfold pdom, st1 in *.  eapply HC in H17. congruence.

        * assert (sst_chain (st2 M'') (st2 M''')). { destruct STC''' as [H17A [H17B [H17C [H17D H17E]]]]; eauto. }
          assert (sst_chain (st2 M)(st2 M''')). { eapply sst_trans. 2: eapply H17. destruct STC'' as [? [? [? [X ?]]]]; eauto. }
          destruct H18 as [HA [HB HC]]. apply indexr_var_some' in H11 as H11'.
          eapply HC in H11'. congruence.

        * rewrite SSE1; eauto. intros ?. rewrite lls_vars_or in H17. destruct H17. 
          eapply H6. eapply lls_mono; eauto. eapply vars_locs_mono; eauto. unfoldq; intuition.
          eapply H8. eapply lls_mono; eauto. eapply vars_locs_mono; eauto. unfoldq; intuition.
        * rewrite SSE2; eauto. intros ?. rewrite lls_vars_or in H17. destruct H17. 
          eapply H7. eapply lls_mono; eauto. eapply vars_locs_mono; eauto. unfoldq; intuition.
          eapply H9. eapply lls_mono; eauto. eapply vars_locs_mono; eauto. unfoldq; intuition.
        * (* vt_valtype *)
          subst vtx. eapply functional_extensionality. intros. eapply functional_extensionality. intros.
          eapply propositional_extensionality. split; intro.
          **  destruct H14. destruct H14 as [? ?]. auto. 
              destruct H14. destruct H14 as [? [? | ]]. destruct H17. contradiction. 
              destruct H17 as [? [? [? ?]]]. apply indexr_var_some' in H10. unfold length1 in *. contradiction.
              destruct H14 as [? [? | ]]. destruct H17. contradiction.
              destruct H17 as [? [? [? ?]]]. apply indexr_var_some' in H10. unfold length1 in *. contradiction.         
         ** left. split; auto. 
       * (* vt *) 
         auto.
       * (* st_filter *)
         remember H16 as H16'. clear HeqH16'.
         destruct H16 as [SFF1 [SFF2 SFF3]]. repeat split.
         ** unfold st1 at 1. simpl. unfold st_locs1, pnat, length1, st1. simpl.
            intros ? ?. erewrite <- lls_change with (M := (fst(fst(fst M)))) in H16.
            unfold st1 in SFF1. eapply SFF1 in H16. unfold st_locs1, pnat, length1, st1 in *. lia. 
            eapply sstchain_tighten with (p := st_locs1 M); eauto.
         ** unfold st2 at 1. simpl. unfold st_locs2, pnat, length2, st2. simpl.
            intros ? ?. erewrite <- lls_change with (M := (snd(fst(fst M)))) in H16.
            unfold st2 in SFF2. eapply SFF2 in H16. unfold st_locs2, pnat, length2, st2 in *. lia. 
            eapply sstchain_tighten. { destruct STC''' as [? [? [? [X ?]]]]; eauto. } eauto.
         ** unfold strel in H16. simpl in H16.
            intros. unfold st1 at 1 in H16. simpl in H16.
            unfold st2 at 1. simpl.
            destruct H16 as [SX | [SY | SZ]]. destruct SX as [SXA [SXB [SXC [SXD SXE]]]].
            *** erewrite <- lls_change with (M := ((fst (fst(fst M))))) in H17. unfold st1, st2 in SFF3.
                eapply SFF3 in H17 as H17'; eauto. erewrite <- lls_change. eapply H17'.
                eapply sstchain_tighten; eauto. eapply sstchain_tighten with (p := st_locs1 M); eauto.
            *** destruct SY as [SYA [SYB | SYC]].
                assert (strel M l0 l3). { eapply SXMP2; eauto. }
                erewrite <- lls_change with (M := ((fst (fst(fst M))))) in H17. unfold st1, st2 in SFF3.
                eapply SFF3 in H17 as H17'; eauto. erewrite <- lls_change. eapply H17'.
                eapply sstchain_tighten; eauto. eapply sstchain_tighten with (p := st_locs1 M); eauto.
                destruct SYC. apply indexr_var_some' in H10 as H10'. 
                unfold st_locs1, st_locs2, pnat, length1, length2, st1, st2 in *. simpl in H17. 
                erewrite <- lls_change with (M := (st1 M)) in H17.
                2: { eapply sstchain_tighten; eauto. }
                eapply SFF1 in H17. contradiction.
            *** destruct SZ as [SZA [SZB | SZC]]. 
                assert (strel M l0 l3). { eapply SXMP3; eauto. }
                destruct SZB.
                erewrite <- lls_change with (M := ((fst (fst(fst M))))) in H17. 
                eapply SFF3 in H17; eauto. 
                erewrite <- lls_change; eauto. 
                eapply sstchain_tighten; eauto. eapply sstchain_tighten with (p := st_locs1 M); eauto.
                destruct SZC.
                unfold st_locs1, st_locs2, pnat, length1, length2, st1, st2 in *. simpl in H17.
                erewrite <- lls_change  with (M := (st1 M)) in H17; eauto.
                eapply SFF1 in H17. contradiction.
                eapply sstchain_tighten; eauto. 
                
         ** unfold strel in H16. simpl in H16.
            intros. unfold st2 at 1 in H16. simpl in H16.
            unfold st1 at 1. simpl.
            destruct H16 as [SX | [SY | SZ]]. destruct SX as [SXA [SXB [SXC [SXD SXE]]]].
            *** erewrite <- lls_change with (M := ((snd (fst(fst M))))) in H17. 
                eapply SFF3 in H17; eauto. 
                2: eapply sstchain_tighten; eauto.
                erewrite <- lls_change; eauto.
                eapply sstchain_tighten with (p := st_locs1 M); eauto. 
            *** destruct SY as [SYA [SYB | SYC]].
                assert (strel M l0 l3). { eapply SXMP2; eauto. }
                erewrite <- lls_change with (M := ((snd (fst(fst M))))) in H17. 
                eapply SFF3 in H17; eauto.
                erewrite <- lls_change; eauto.
                eapply sstchain_tighten with (p := st_locs1 M); eauto. 
                eapply sstchain_tighten; eauto.
                destruct SYC as [SYC1 [SYC2 [SYC3 [SYC4 [SYC5 SYC6]]]]]. 
                unfold st_locs1, st_locs2, pnat, length1, length2, st1, st2 in *. simpl in *. 
                erewrite <- lls_change  with (M := (st2 M)) in H17; eauto.
                2: { eapply sstchain_tighten; eauto. }
                eapply SFF2 in H17. contradiction.
            *** destruct SZ as [SZA [SZB | SZC]]. destruct SZB as [SZB1 SZB2].
                assert (strel M l0 l3). { eapply SXMP3; eauto. }
                erewrite <- lls_change with (M := ((snd (fst(fst M))))) in H17. 
                eapply SFF3 in H17; eauto.
                erewrite <- lls_change; eauto.
                eapply sstchain_tighten with (p := st_locs1 M); eauto. 
                eapply sstchain_tighten; eauto.
                destruct SZC as [SZC1 [SZC2 [SZC3 [SZC4 [SZC5 SZC6 ]]]]].
                erewrite <- lls_change with (M := ((snd (fst(fst M))))) in H17.
                eapply SFF2 in H17. unfold st_locs2, pnat in H17. contradiction.
                eapply sstchain_tighten; eauto. 
     + (* strel M''' l1 l2 and l1 l2 are in p1 *)
       destruct B as [? [? | ?]]. destruct H6 as [HA HB].
       destruct (STREL''' l1 l2) as (vtx & qt1x & qt2x & v1'x & v2'x & ? & ? & ? & ? & ? & ? & ?). eauto.
       exists vtx, qt1x, qt2x, v1'x, v2'x. split. 2: split. 3: split. 4: split. 5: split. 6: split.
       * unfold st1. simpl. assert (snd (fst M) l1 l2). { eapply SXMP2; eauto. }
         destruct SRMP1 as [A [B [[C1 [C2 C3] ][D [E F]]]]]. unfold st_locs1, pnat, length1, st1 in C3. simpl in C3. 
         destruct STC''' as [Ax [Bx [[C1x [C2x C3x] ][Dx [Ex Fx]]]]]. unfold st_locs1, pnat, length1, st1 in C3x. simpl in C3x.
         eapply C3 in HA as HA'; eauto.
         assert (l1 < length (fst(fst(fst M)))) as X. { eapply envt_store_deep_wf in HA; eauto.  }
         eapply C3x in X; eauto.  unfold st1 in *. congruence.
       * unfold st2. simpl. auto.
       * erewrite SE2'; eauto. unfold st1. simpl. intros ?. erewrite <- lls_change with (M := (fst (fst (fst M)))) in H13.
         eapply SEP1; eauto. 
         eapply stchain_tighten. 2: eapply STC'; eauto. eapply envt_filter_deep; eauto. 
         eapply envt_store_deep_wf; eauto. eapply envt_store_deep_wf; eauto. 
       * auto.
       * (* st_valtype *)
         simpl. subst vtx. eapply functional_extensionality. intros. eapply functional_extensionality. intros.
         eapply propositional_extensionality. split; intros.
         ** destruct H10. destruct H10 as [? [? ?]]. contradiction. 
            destruct H10. destruct H10 as [? [? | ?]]. destruct H13. congruence. 
            destruct H13 as [? [? [? ?]]]. eapply envt_store_deep_wf in HA; eauto. 
            destruct H10 as [? [? | ?]]. destruct H13. assert False. eapply SEP1; eauto. contradiction.
            destruct H13 as [? [? [? ?]]]. eapply envt_store_deep_wf in HA; eauto. unfold pnat in HA. contradiction.
         ** right. left. split. congruence. left. split; auto.
       * (* vt *) 
         auto.
       * (* st_filter *)
         unfold st1, st2. simpl. destruct H12 as [A [B C ]]. 
         assert (indexr l1 S1'' = Some v1'x) as ISV0. { 
          erewrite SE2'; eauto. intros ?. eapply SEP1; eauto. erewrite lls_change. eapply lls_mono; eauto. eapply vars_locs_mono; eauto. unfoldq; intuition. 
          eapply sstchain_tighten. eapply STC'. eapply envt_filter_deep; eauto. 
         }
         assert (indexr l1 (st1 M) = Some qt1x) as IM1x. { rewrite <- H6. eapply SXMP2; eauto.  }
         assert (indexr l1 (st1 M') =  Some qt1x) as IM2x. { rewrite <- IM1x. symmetry.  eapply STC'. unfold st_locs1. unfoldq. eapply envt_store_deep_wf in HA; eauto. }
         assert (indexr l1 (st1 M') = indexr l1 (st1 M'')) as IM3x. { eapply XXYY. erewrite <- lls_change; eauto. eapply sstchain_tighten. eapply STC'; eauto. eapply  envt_store_deep_wf; eauto.  }
         assert (indexr l1 (st1 M'') = Some qt1x) as IM4x. congruence.
         
         repeat split. 
         ** unfold st_locs1, pnat, length1, st1. simpl. intros ? ?. unfold st1 in SE2'. simpl in SE2'.
            eapply lls_qt in IM4x as IM4x'; eauto. eapply lls_indexr_closed'' in IM4x as IM4x''; eauto. eapply IM4x' in H12. 
            eapply IM4x'' in H12. unfoldq. apply indexr_var_some' in IM4x. unfold st1 in IM4x. lia. 
         ** unfold st_locs2, pnat, length2, st2. simpl. unfold st2, st_locs2, pnat, length2 in B. auto. 
         ** unfold strel in H12. simpl in H12. destruct H12 as [XX | [YY | ZZ]]. 
            *** destruct XX as [Ax [Bx [Cx [Dx Ex]]]].  
                intros. unfold st2 in SE2, SE2''. simpl in SE2, SE2''.
                eapply val_reach_p in ISV0 as ISV0'. 3: eapply IM4x. 
                2: { erewrite <- lls_change; eauto. eapply sstchain_tighten; eauto.  eapply envt_store_deep_wf; eauto.  } 2: eauto.
                eapply ISV0' in H12. erewrite <- lls_change with (M := st1 M') in H12. erewrite lls_change with (M' := (st1 M')) in Bx.
                specialize (SEP1 l0); intuition. eapply sstchain_tighten. eapply STC'. eapply envt_store_deep_wf; eauto. eauto.
            *** destruct YY as [Ax [Bx | Cx]]. destruct Bx. intros.  
               eapply C. eauto.
            (* (S1, M1) ->p1 (S1', M1''') ->p2 (S1'', M1'') *)
               erewrite <- lls_change; eauto.     
               eapply sstchain_tighten with (p := (locs_locs_stty (st1 M) (vars_locs H1 (plift p1)))). 
               eapply sstchain_tighten; eauto. intros ? ?. auto.
               intros ? ?.  erewrite lls_change with (M' := (st1 M'')); eauto.
               eapply val_reach_p; eauto. erewrite <- lls_change; eauto. eapply sstchain_tighten; eauto. eapply envt_store_deep_wf; eauto.
               eapply sstchain_tighten; eauto. eapply envt_store_deep_wf; eauto.
               destruct Cx as [Cx1 [Cx2 [Cx3 [Cx4 Cx5]]]]. intros.
               eapply C; eauto.
               erewrite <- lls_change; eauto.     
               eapply sstchain_tighten with (p := (locs_locs_stty (st1 M) (vars_locs H1 (plift p1)))); eauto. 
               intros ? ?. erewrite lls_change with (M' := (st1 M'')); eauto.
               eapply val_reach_p; eauto. erewrite <- lls_change; eauto.  
               eapply sstchain_tighten; eauto. eapply envt_store_deep_wf; eauto.
               eapply sstchain_tighten; eauto. eapply envt_store_deep_wf; eauto.

           *** destruct ZZ as [ZA [ZB | ZC]]. destruct ZB as [ZB1 ZB2]. intros.
               assert (psub (locs_locs_stty (st1 M'') (val_locs v1'x)) (locs_locs_stty (st1 M'')(vars_locs H1 (plift p1)))).  {
                 eapply val_reach_p; eauto. erewrite lls_change; eauto. eapply sst_chain_partial_symmetry. 
                 rewrite <- lls_change with (M := st1 M); eauto. 
                 eapply sstchain_tighten; eauto. eapply envt_store_deep_wf; eauto.
                 eapply sstchain_tighten; eauto. eapply envt_store_deep_wf; eauto.
               } 
               eapply H13 in H12. rewrite <- lls_change with (M := st1 M) in H12; eauto. 
               specialize (SEP1 l0); intuition.
               eapply sstchain_tighten; eauto. eapply envt_store_deep_wf; eauto.

               destruct ZC as [SZC1 [SZC2 [SZC3 [SZC4 [SZC5 SZC6]]]]]. intros.
               assert False.
               eapply SZC6. split.
               2: { left. unfold pone. eauto. }
               left. unfold pdiff. split; auto.
               contradiction.
         ** intros. unfold strel in H12. simpl in H12. destruct H12 as [XX | [YY | ZZ]].
            *** destruct XX as [Ax [Bx [Cx [Dx Ex]]]].  intros. unfold st2 in SE2, SE2''. simpl in SE2, SE2''.
                eapply val_reach_p in H13 as H13'. 3: eapply H9. 3: eauto. 3: eauto. 2: {  erewrite <- lls_change; eauto. eapply SXMP2; eauto. }
                erewrite <- lls_change with (M := st2 M) in H13'. 2: eapply SXMP2; eauto. specialize (SEP1X l3); intuition.
            *** destruct YY as [Ax [Bx | Cx]]. destruct Bx as [Bx1 Bx2].
                eapply C in H13; eauto.
                erewrite lls_change; eauto. eapply sstchain_tighten with (p := (locs_locs_stty (st1 M) (vars_locs H1 (plift p1)))); eauto.
                intros ? ?. erewrite lls_change with (M' := (st1 M'')); eauto. eapply val_reach_p; eauto.
                erewrite <- lls_change; eauto. 1,2: eapply sstchain_tighten; eauto;  eapply envt_store_deep_wf; eauto.
                
                destruct Cx as [Cx1 [Cx2 [Cx3 [Cx4 Cx5]]]].
                eapply C in H13; eauto.
                erewrite lls_change; eauto. eapply sstchain_tighten with (p := (locs_locs_stty (st1 M) (vars_locs H1 (plift p1)))); eauto.
                intros ? ?. erewrite lls_change with (M' := (st1 M'')); eauto. eapply val_reach_p; eauto.
                erewrite <- lls_change; eauto. 1,2: eapply sstchain_tighten; eauto; eapply envt_store_deep_wf; eauto. 
           *** destruct ZZ as [ZA [[ZB1 ZB2 ] | ZC]]. 
               assert (psub (locs_locs_stty (st2 M''') (val_locs v2'x)) (locs_locs_stty (st2 M''')(vars_locs H2 (plift p1)))).  {
                 eapply val_reach_p; eauto. erewrite <- lls_change with (M := st2 M); eauto. eapply SXMP2; eauto.
               } 
               eapply H12 in H13. rewrite <- lls_change with (M := st2 M) in H13; eauto. specialize (SEP1X l3); intuition.
               eapply SXMP2; eauto.
               
               destruct ZC as [SZC1 [SZC2 [SZC3 [SZC4 [SZC5 SZC6 ]]]]].
               assert False. eapply SZC6. split.
               2: { left. unfold pone. eauto. }
               left. unfold pdiff. split; auto.
               contradiction.
               
       * (* strel M''' l1 l2 and l1 or l2 are not in M *)
         destruct H6 as [HA [HB [HC [HD [HE [HF HG]]]]]].
         assert False. eapply HD. split.
         2: { left. unfold pone. eauto. }
         left. unfold pdiff. split; auto. contradiction.
                    
                
     + (* strel M'' l1 l2 and l1 l2 are in p2 *) 
       destruct C as [? [? | ?]]. destruct H6 as [HA HB].
       destruct (STX'' l1 l2) as (vtx & qt1x & qt2x & v1'x & v2'x & ? & ? & ? & ? & ? & ? & ?). eauto.
       exists vtx, qt1x, qt2x, v1'x, v2'x. split. 2: split. 3: split. 4: split. 5: split. 6: split.
       * unfold st1. simpl. unfold st1 in *. auto.
       * unfold st2. simpl. assert (snd (fst M) l1 l2). { eapply SXMP3; eauto. }
         destruct STC'' as [A [B [C [[D1 [D2 D3] ] [E F]]]]]. unfold st_locs2, pnat, length2, st2 in D3. simpl in D3. 
         destruct STC''' as [Ax [Bx [Cx [[D1x [D2x D3x]][Ex Fx]]]]]. unfold st_locs2, pnat, length2, st2 in D3x. simpl in D3x.
         assert (l2 < length (snd(fst(fst M)))) as X. { eapply envt_store_deep_wf in HB; eauto.  }
         assert (l2 < length (snd (fst (fst M'')))) as Y. { eapply indexr_var_some' in H7. unfold st2 in *. lia.  }
         eapply D3x in Y. eapply D3 in X. unfold st2 in *. congruence.
       * auto.
       * erewrite SE2''; eauto. unfold st2. simpl. intros ?. erewrite <- lls_change with (M := (snd (fst (fst M)))) in H13.
         eapply SEP1X; eauto. 
         eapply sstchain_tighten. eapply STC''; eauto.  eapply envt_store_deep_wf; eauto. 
       * (* st_valtype *)
         simpl. subst vtx. eapply functional_extensionality. intros. eapply functional_extensionality. intros.
         eapply propositional_extensionality. split; intros.
         ** destruct H10. destruct H10 as [? [? [? [? ?]]]]. contradiction. 
            destruct H10. destruct H10 as [? [? | ?]]. destruct H13. assert False. eapply SEP1; eauto. contradiction.
            destruct H13 as [? [? [? [? [? [? ?]]]]]]. eapply envt_store_deep_wf in HA; eauto. unfold pnat in HA. contradiction.
            destruct H10 as [? [? | ?]]. destruct H13. congruence.
            destruct H13 as [? [? [? ?]]]. eapply envt_store_deep_wf in HA; eauto. 
         ** right. right. split. congruence. left. split; auto.
       * (* vt *)
         auto.
       *(* st_filter *)
        (* (S2, M2) ->p2 (S2', M2'') ->p1 (S2'', M2''') *)
        (* (S2, M2) ->p1 (S1x', M2' )*)
        (* (S2, M2) ->p2 (S2'', M2''')*)
        (* (S1, M1) ->p1 (S1', M1''') ->p2 (S1'', M1'') *)
         unfold st1, st2 in *. simpl in *.  destruct H12 as [A [B C]].
         assert (indexr l2 S2'' = Some v2'x) as ISV0. { erewrite SE2''; eauto. intros ?.  eapply SEP1X; eauto. erewrite lls_change. eapply lls_mono; eauto. eapply vars_locs_mono; eauto. unfoldq; intuition. eapply sstchain_tighten. eapply STC''. eapply envt_store_deep_wf; eauto. }
         assert (indexr l2 (st2 M) = Some qt2x) as IM1x. { rewrite <- H7. eapply SXMP3; eauto.   }
         assert (indexr l2 (st2 M') =  Some qt2x) as IM2x. { rewrite <- IM1x. symmetry. eapply STC'; eauto. unfold st_locs2. unfold pnat. eapply envt_store_deep_wf in HB; eauto. }
         assert (indexr l2 (st2 M) = indexr l2 (st2 M''')) as IM3x. { eapply sstchain_tighten; eauto. eapply envt_store_deep_wf; eauto.  }
         assert (indexr l2 (st2 M''') =  Some qt2x) as IM4x. { congruence. } 
         repeat split.
         ** unfold st_locs1, pnat, length1, st1. simpl. intros ? ?. unfold st2 in SE2'. simpl in SE2'. 
            eapply val_reach_wf_store. eapply H8. eauto. eauto.
         ** unfold st_locs2, pnat, length2, st2. simpl. intros ? ?. eapply val_reach_wf in ISV0 as ISV0'; eauto. 
         ** intros. unfold strel in H12. simpl in H12. destruct H12 as [XX | [YY | ZZ]].
           *** destruct XX as [Ax [Bx [Cx [Dx Ex]]]]. 
               eapply val_reach_p in H13 as H13'. 3: eapply H8. 3: eauto. 2: { erewrite <- lls_change; eauto. eapply SXMP3; eauto. }
               erewrite <- lls_change with (M := (st1 M)) in H13'; eauto. 2: eapply SXMP3; eauto. specialize (SEP1X l0); intuition. eauto.
           *** destruct YY as [Ax [Bx | Cx]].
               destruct Bx.
               assert (psub (locs_locs_stty (st1 M'') (val_locs v1'x)) (locs_locs_stty (st1 M'')(vars_locs H1 (plift p2)))).  {
                 eapply val_reach_p; eauto. erewrite <- lls_change with (M := (st1 M)); auto.  eapply SXMP3; eauto. 
               }
               eapply H15 in H13. erewrite <- lls_change with (M := st1 M) in H13. specialize (SEP1 l0); intuition. eapply SXMP3; eauto.
               destruct Cx as [Cx1 [Cx2 [Cx3 [Cx4 [Cx5 [Cx6 Cx7]]]]]]. 
               assert False. 
               eapply Cx4. split. 2: { left. unfold pone. eauto. }
               left. unfold pdiff. split; auto. 
               contradiction.
           *** destruct ZZ as [Ax [Bx | Cx]]. destruct Bx as [Bx1 Bx2].
               eapply C in H13; eauto.  erewrite <- lls_change; eauto.
               assert (sst_chain_partial (st2 M) (st2 M'') (locs_locs_stty (st2 M) (vars_locs H2 (plift p2)))). { eapply SXMP3. }
               assert (sst_chain_partial (st2 M) (st2 M''') (locs_locs_stty (st2 M) (vars_locs H2 (plift p2)))). { eapply sstchain_tighten. eauto. eapply envt_store_deep_wf; eauto. }
               assert (sst_chain_partial (snd (fst (fst M''))) (snd (fst (fst M''')))(locs_locs_stty (snd (fst (fst M''))) (vars_locs H2 (plift p2)))). {
                 remember H12. remember H14. clear Heqs. clear Heqs0.
                 destruct H12 as [? [? ?]].  destruct H14 as [? [? ?]].
                 repeat split. intros ? ?. erewrite <- lls_change with (M := (st2 M)) in H19. eapply envt_store_deep_wf in H19; eauto. unfold pnat, length2, st2 in *. unfold pdom. lia.
                 eauto.
                 intros ? ?. erewrite <- lls_change with (M := (st2 M)) in H19. eapply envt_store_deep_wf in H19; eauto. unfold pnat, length2, st2 in *. unfold pdom. lia.
                 eauto.
                 intros ? ?. erewrite <- lls_change with (M := (st2 M)) in H19; eauto. eapply H18 in H19 as H19'. eapply H16 in H19. unfold st2 in *. congruence.
               }
               eapply sstchain_tighten; eauto.  eapply val_reach_p in H9; eauto. erewrite <- lls_change; eauto.
               destruct Cx as [Cx1 [Cx2 [Cx3 [Cx4 [Cx5 Cx6]]]]]. 
               assert False. 
               eapply Cx6. split. 2: { left. unfold pone. eauto. }
               left. unfold pdiff. split; auto. 
               contradiction.
       ** intros.  unfold strel in H12. simpl in H12. destruct H12 as [XX | [YY | ZZ]].
         *** destruct XX as [Ax [Bx [Cx [Dx Ex]]]].
             eapply val_reach_p in ISV0 as ISV0'. 3: eapply IM4x. 3: auto. 
             2: { erewrite lls_change; eauto. eapply sst_chain_partial_symmetry. erewrite <- lls_change with (M := st2 M). eapply sstchain_tighten; eauto. eapply envt_store_deep_wf; eauto. eapply sstchain_tighten; eauto. eapply envt_store_deep_wf; eauto. }
             eapply ISV0' in H13. erewrite <- lls_change with (M := st2 M) in H13. 2: auto. specialize (SEP1X l3); intuition.
             eapply sstchain_tighten; eauto. eapply envt_store_deep_wf; eauto. 
         *** destruct YY as [Ax [Bx | Cx]].
             eapply val_reach_p in ISV0 as ISV0'. 3: eapply IM4x. 3: eauto. 2: { erewrite <- lls_change; eauto. eapply sstchain_tighten; eauto. eapply envt_store_deep_wf; eauto.  }
             eapply ISV0' in H13. erewrite <- lls_change with (M := (st2 M)) in H13; eauto.
             specialize (SEP1X l3); intuition.
             eapply sstchain_tighten; eauto. eapply envt_store_deep_wf; eauto.
             destruct Cx as [Cx1 [Cx2 [Cx3 [Cx4 [Cx5 [Cx6 Cx7]]]]]].
             assert False. eapply Cx4. split.
             2: { left. unfold pone. eauto. }
             left. unfold pdiff. split; auto.
             contradiction.
         *** destruct ZZ as [Ax [Bx | Cx]]. destruct Bx as [Bx1 Bx2].
             erewrite <- lls_change with (M := st2 M'') in H13; eauto. eapply C; eauto.
             assert (sst_chain_partial (st2 M) (st2 M'') (locs_locs_stty (st2 M) (vars_locs H2 (plift p2)))). { eapply SXMP3. }
             assert (sst_chain_partial (st2 M) (st2 M''') (locs_locs_stty (st2 M) (vars_locs H2 (plift p2)))). { eapply sstchain_tighten; eauto. eapply envt_store_deep_wf; eauto. }
             assert (sst_chain_partial (snd (fst (fst M''))) (snd (fst (fst M''')))(locs_locs_stty (snd (fst (fst M''))) (vars_locs H2 (plift p2)))). {
               remember H12. remember H14. clear Heqs. clear Heqs0.
               destruct H12 as [? [? ?]].  destruct H14 as [? [? ?]].
               repeat split. 
               intros ? ?. erewrite <- lls_change with (M := (st2 M)) in H19. eapply envt_store_deep_wf in H19; eauto. unfold pnat, length2, st2 in *. unfold pdom. lia.
               eauto.
               intros ? ?. erewrite <- lls_change with (M := (st2 M)) in H19. eapply envt_store_deep_wf in H19; eauto. unfold pnat, length2, st2 in *. unfold pdom. lia.
               eauto.
               intros ? ?. erewrite <- lls_change with (M := (st2 M)) in H19; eauto. eapply H16 in H19 as H19'. eapply H18 in H19. unfold st2 in *. congruence.
             }
             eapply sstchain_tighten; eauto.  eapply val_reach_p in H9; eauto. erewrite <- lls_change; eauto.
         
             destruct Cx as [Cx1 [Cx2 [Cx3 [Cx4 [Cx5 Cx6]]]]].
             assert False.
             eapply Cx6. split.
             2: { left. unfold pone. eauto. }
             left. unfold pdiff. split; auto.
             contradiction.
     *  (* strel M'' l1 l2 and l1 or l2 are not in M *)
       destruct H6 as [HA [HB [HC [HD [HE HF]]]]].    
       assert False. eapply HF. split.
       2: { left. unfold pone. eauto. }
       left. unfold pdiff. split; auto. contradiction.
      
   - unfold strel. simpl. intros.
     destruct H5 as [(A&?) | [(B&?) | (C&?)]]; destruct H6 as [(U&?) | [(V&?) | (W&?)]].
     + eauto.
     + destruct H6. specialize (SEP1 l1); intuition. 
       destruct (STREL l1 l2) as [? [? [? [? [? [IM ?]]]]]]; auto. apply indexr_var_some' in IM. unfold st1 in IM. intuition.
     + destruct H6. specialize (SEP1 l1); intuition.
       destruct (STREL l1 l2) as [? [? [? [? [? [IM ?]]]]]]; auto. apply indexr_var_some' in IM. unfold st1 in IM. intuition.
     + destruct H5. specialize (SEP1 l1); intuition. 
       destruct (STREL l1 l2') as [? [? [? [? [? [IM ?]]]]]]; auto. apply indexr_var_some' in IM. unfold st1 in IM. intuition.
     + eauto.
     + destruct H5; destruct H6. 
       specialize (SEP1 l1); intuition. 
       destruct H5. eapply envt_store_deep_wf in H5; eauto. unfold pnat in H5. intuition.
       destruct H6. eapply envt_store_deep_wf in H6; eauto. unfold pnat in H6. intuition.
       intuition.
     + destruct H5. specialize (SEP1 l1); intuition. 
       destruct (STREL l1 l2') as [? [? [? [? [? [IM ?]]]]]]; auto. apply indexr_var_some' in IM. unfold st1 in IM. intuition.
     + destruct H5; destruct H6.
       specialize (SEP1 l1); intuition. 
       destruct H5. eapply envt_store_deep_wf in H5; eauto. unfold pnat in H5. intuition.
       destruct H6. eapply envt_store_deep_wf in H6; eauto. unfold pnat in H6. intuition.
       intuition.
     + destruct H5; destruct H6. 
       eauto.
       destruct H5. eapply envt_store_deep_wf in H5; eauto. 
       destruct H6. eapply envt_store_deep_wf in H6; eauto.
       eauto.
       
   - unfold strel. simpl. intros.
     destruct H5 as [(A&?) | [(B&?) | (C&?)]]; destruct H6 as [(U&?) | [(V&?) | (W&?)]].
     + eauto.
     + destruct H6. specialize (SEP1 l1); intuition. 
       destruct (STREL l1 l2) as [? [? [? [? [? [? [IM ?]]]]]]]; auto. apply indexr_var_some' in IM. unfold st2 in IM. intuition.
     + destruct H6. specialize (SEP1 l1); intuition.
       destruct (STREL l1 l2) as [? [? [? [? [? [? [IM ?]]]]]]]; auto. apply indexr_var_some' in IM. unfold st2 in IM. intuition.
     + destruct H5. specialize (SEP1 l1); intuition. 
       destruct (STREL l1' l2) as [? [? [? [? [? [? [IM ?]]]]]]]; auto. apply indexr_var_some' in IM. unfold st2 in IM. intuition.
     + eauto.
     + destruct H5; destruct H6. 
       specialize (SEP1X l2); intuition. 
       destruct H5. eapply envt_store_deep_wf in H7; eauto. unfold pnat in H7. intuition.
       destruct H6. eapply envt_store_deep_wf in H7; eauto. unfold pnat in H7. intuition.
       intuition.
     + destruct H5. specialize (SEP1X l2); intuition. 
       destruct (STREL l1' l2) as [? [? [? [? [? [? [IM ?]]]]]]]; auto. apply indexr_var_some' in IM. unfold st2 in IM. intuition.
     + destruct H5; destruct H6.
       specialize (SEP1X l2); intuition. 
       destruct H5. eapply envt_store_deep_wf in H7; eauto. unfold pnat in H7. intuition.
       destruct H6. eapply envt_store_deep_wf in H7; eauto. unfold pnat in H7. intuition.
       intuition.
     + destruct H5; destruct H6. 
       eauto.
       destruct H5. eapply envt_store_deep_wf in H7; eauto. 
       destruct H6. eapply envt_store_deep_wf in H6; eauto.
       eauto.
  }

  exists S1'', S2''. exists MM. eexists. eexists.
  split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 8: split. 9: split.
  + eauto.
  + eauto.
  + eauto. 
  + eauto.
  + eauto.
  + eapply se_sub. eauto. eapply lls_mono; eauto. eapply vars_locs_mono; eauto. intros ? ?. unfoldq; intuition.
  + eapply se_sub. eauto. eapply lls_mono; eauto. eapply vars_locs_mono; eauto. intros ? ?. unfoldq; intuition.
  + simpl. eauto.
  + eapply valq_bool.
  + eapply valq_bool. 
      
Qed.  