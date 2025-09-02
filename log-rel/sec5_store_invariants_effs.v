(***************************************************************************************************************
* Store invariants used for the proof of re-ordering  with effect qualifiers in the λ^♦_{\varepsilon}-caluclus.
****************************************************************************************************************)

(* based on sec6_reach_binary_effs.v *)



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
Require Import sec4_reach_binary_effs.

Import STLC.

(* ---------- store invariance / localization ---------- *)


Definition st_empty (MS1 MS2: st): stty := (MS1, MS2, fun l1 l2 => False, fun l1 l2 v1 v2 => False).

Lemma stchain_empty: forall S1 S2 M,
    st_chain_partial M (st_empty S1 S2) pempty pempty.
Proof.
  intros. unfold st_chain_partial, st_filter, st_empty, sst_chain_partial, st_locs1, length1 in *; simpl. intuition.
  all: intros ? ?; unfoldq; intuition.
Qed.

Lemma stchain_empty': forall M M1,
    st_chain_partial M M1 pempty pempty.
Proof.
  intros. 
  unfold st_chain_partial, st_filter, st_empty, sst_chain_partial, st_locs1, length1, length2 in *.  simpl. intuition.
  all: intros ? ?;  unfoldq; intuition.
Qed.


Lemma storet_empty: forall S1 S2 MS1 MS2,
    sstore_type S1 MS1 ->
    sstore_type S2 MS2 ->
    store_type S1 S2 (st_empty MS1 MS2).
Proof.
  intros. destruct H as [L1 ?]. destruct H0 as [L2 ?]. unfold store_type, sstore_type, st_empty. simpl in *. intuition.
Qed.

Definition st_tight (MS1 MS2: st): stty := (MS1, MS2, fun l1 l2 => False, fun l1 l2 v1 v2 => False).


Lemma stfilter_empty: forall MS1 MS2 P1 P2,
   st_filter (MS1, MS2, P1, P2) pempty pempty.
Proof.
  intros. unfold st_filter; intuition.
  + intros ? ?. unfoldq; intuition.
  + intros ? ?. unfoldq; intuition.
Qed.  

Lemma stfilter_empty': forall MS1 MS2,
    st_filter (st_empty MS1 MS2)(st_locs1 (st_empty MS1 MS2))(st_locs2 (st_empty MS1 MS2)).
Proof.
  intros. unfold st_filter, st_empty, st_locs1, st_locs2, pnat, length1, length2, st1, st2; intuition; simpl.
  unfoldq; intuition.
  unfoldq; intuition.
Qed.

Lemma valq_val_empty: forall M1 M2 H v,
  val_qual M1 M2 H v false pempty ->
  val_locs v = pempty.
Proof.
  intros. eapply functional_extensionality.
  intros. eapply propositional_extensionality.
  split; intros.
  destruct (H0 x); auto. left. auto. rewrite vars_locs_empty in H2. rewrite lls_empty in H2.
  unfoldq; intuition. unfoldq; intuition. 
Qed.

Lemma val_locs_empty:  forall t G T  p 
  (W: has_type G t T p false qempty qempty),
  forall  S1 S2 H1 H2 M, 
     env_type M H1 H2 G (plift p) ->
     st_filter M (st_locs1 M)(st_locs2 M) ->
     store_type S1 S2 M ->
  exists S1' S2'  v1 v2,
    tevaln S1 H1 t S1' v1 /\
    tevaln S2 H2 t S2' v2 /\
    val_locs v1 = pempty /\
    val_locs v2 = pempty.
Proof.
  intros. eapply fundamental_property in W.  rewrite plift_empty in W.
  unfold sem_type in W.
  destruct (W M H1 H2 H H0 S1 S2 H3) as [S1' [S2' [M' [v1 [v2 [E1 [E2 [SC [SF [ST [EF1 [Ef2 [VT [VQ1 VQ2]]]]]]]]]]]]]].
  rewrite pand_empty_r in *.
  exists S1', S2', v1, v2; intuition.
  eapply valq_val_empty; eauto. eapply valq_val_empty; eauto.
Qed.

(* Theorem: if an expression typechecks with p = empty,
            we can evaluate it in ANY two stores S1, S2
            to equivalent values v1, v2. *)

Theorem store_invariance : forall t G T q fr e
  (W: has_type G t T qempty fr q e),
  forall P1 P2 S1 S2 MS1 MS2 H1 H2,
       env_type (MS1, MS2, P1, P2) H1 H2 G (plift qempty) ->
       store_type S1 S2 (MS1, MS2, P1, P2) ->
  exists S1' S2' M' v1 v2,
  exp_type S1 S2 (st_empty MS1 MS2) H1 H2 t t S1' S2' M' v1 v2 T (plift qempty) fr (plift q) (plift e).
Proof.
    intros.
    eapply fundamental_property; eauto.
    eapply envt_store_change. eauto. eauto.
    eapply stchain_tighten. rewrite plift_empty, vars_locs_empty, vars_locs_empty, lls_empty, lls_empty. 
    eapply stfilter_empty. 
    eapply stchain_empty.
    rewrite plift_empty, vars_locs_empty, lls_empty. unfoldq; intuition.
    rewrite plift_empty, vars_locs_empty, lls_empty. unfoldq; intuition.
    eapply stfilter_empty'; eauto. 
    destruct H0 as [? [? ?]]. eapply storet_empty; eauto.
Qed.

 (* term equivalence preservation for the first program *)

Theorem store_invariance2 : forall t G T p p' fr q e
(W: has_type G t T p fr q e),
forall M H1 H2, env_type M H1 H2 G (plift p) ->
forall S1 S2, store_type S1 S2 M ->
              (forall l1 l2, strel M l1 l2 -> ~ p' l1) ->
forall S1' MS1', store_effect S1 S1' p' ->
               length S1 <= length S1' ->
               sst_chain (st1 M) MS1' ->
               sstore_type S1' MS1' ->
exists S1'' S2' M' v1 v2,
exp_type S1' S2 (MS1', st2 M, strel M, st_valtype M) H1 H2 t t S1'' S2' M' v1 v2 T (plift p) fr (plift q) (plift e).
Proof.
intros. 
assert (length S1' = length MS1') as L1. { destruct H7; intuition. }
assert (length S1 = length (st1 M)) as L2. { destruct H0 as [[? ?] ?]; intuition. }
assert (length S2 = length (st2 M)) as L3. { destruct H0 as [? [[? ?] ?]]; intuition. }
assert (st_filter M (locs_locs_stty (st1 M) (vars_locs H1 (plift p))) (locs_locs_stty (st2 M) (vars_locs H2 (plift p)))) as STF. {
  eapply envt_filter_deep; eauto. intros ? ?. auto.
}

eapply fundamental_property; eauto.
- eapply envt_store_change; eauto.
  assert (psub (locs_locs_stty (st1 M) (vars_locs H1 (plift p))) (st_locs1 M)). {
    eapply envt_store_deep_wf; eauto. intros ? ?. eauto. }
  assert (psub (locs_locs_stty (st2 M) (vars_locs H2 (plift p))) (st_locs2 M)). {
    eapply envt_store_deep_wf; eauto. intros ? ?. eauto. }
  unfold st_chain_partial. simpl. intuition.
  + unfold st_filter; intuition.
    * intros ? ?. unfold st_locs1, pnat, length1, st1. simpl.
      eapply H8 in H10. unfold st_locs1, pnat, length1 in H10. lia.
    * destruct STF as [? [? ?]]. eapply H14; eauto.
    * destruct STF as [? [? ?]]. eapply H14; eauto.
  + unfold sst_chain_partial; intuition.
    * intros ? ?. eapply H8 in H10. unfoldq; intuition. unfold st1. simpl. eapply sst_mono in H6.  unfold st_locs1, pnat, length1 in H10.  lia.
    * destruct H6 as [A [B C]]. eapply H8 in H10. eapply C in H10. unfold st1 at 2. simpl. auto.
  + unfold sst_chain_partial; intuition.
- unfold st_filter, st_locs1, st_locs2, pnat, length1, length2; intuition.
  + intros ? ?. auto.
  + intros ? ?. auto.
  + unfold strel at 1 in H8. simpl in H8. unfold st2 at 1. simpl. 
    destruct H0 as [? [? [? [? ?]]]]. destruct (H11 l1 l2) as [? [? [? [? [? [? [? ?]]]]]]]; auto.
    apply indexr_var_some' in H15. auto.
  + unfold strel at 1 in H8. simpl in H8. unfold st1 at 1. simpl. 
    destruct H0 as [? [? [? [? ?]]]]. destruct (H11 l1 l2) as [? [? [? [? [? [? [? ?]]]]]]]; auto.
    apply indexr_var_some' in H14. lia.
-  (* store type *)
  destruct H0 as (? & ? & P1 & P2 & P3).
  split. 2: split. 3: split. 4: split.
  + repeat split.
    * unfold st1. simpl. lia.
    * intros. unfold st1. simpl. destruct H7 as [A B] .
      destruct (B l) as [qt [v [IM [IS [Q1 Q2]]]]]; auto.
  + repeat split.
    * unfold st2 at 1. simpl. lia.
    * intros. unfold st2. simpl. destruct H8 as [A B] .
      destruct (B l) as [qt [v [IM [IS [Q1 Q2]]]]]; auto.
  + intros ? ? STR. unfold strel at 1 in STR. simpl in STR. 
    destruct (P1 l1 l2) as (vt & qt1 & qt2 & b1 & b2 & IM1 & IM2 & IS1 & IS2 & SVT & VT & STF'). eauto.
    exists vt, qt1, qt2, b1, b2; intuition.
    * unfold st1 at 1. simpl. destruct H6 as [D [E F]].
      assert (pdom (st1 M) l1). unfoldq; intuition. apply indexr_var_some' in IM1. auto.
      eapply F in H6. congruence.
    * eapply H4. intros ?. eapply H3; eauto. auto. 
    * destruct STF' as [SFA [SFB SFC]].
      repeat split. 
      -- destruct H0 as [? ?]. 
         unfold st1 at 1. unfold st_locs1. simpl.
         eapply lls_closed'. eauto. intros ? ?.  eapply val_lls with (M := st1 M) in H10; eauto.
         eapply SFA in H10. unfold st_locs1, pnat, length1 in H10. unfold pnat. lia.
      -- eapply lls_closed'; eauto.
         intros ? ?.  unfold st2 at 1. unfold pnat, length2, st2. simpl. 
         eapply val_lls with (M := st2 M) in H9; eauto. eapply SFB in H9.
         unfold st_locs2, pnat, length2, st2 in H9. lia.
      -- unfold strel at 1 in H9. simpl in H9.  intros.
         erewrite <- lls_change with (M := st1 M) in H10; eauto.
         eapply SFC in H9; intuition.
         unfold st1 at 2. simpl. eapply sstchain_tighten; eauto. 
      -- unfold strel at 1 in H9. simpl in H9.  intros.
         unfold st2 at 1 in H10. simpl in H10.
         eapply SFC in H9; intuition.
         unfold st1. simpl. erewrite <- lls_change with (M := st1 M); eauto.
         eapply sstchain_tighten; eauto. 
  + intros. unfold strel at 1 in H9. simpl in H9. unfold strel at 1 in H10. simpl in H10.
    eapply P2; eauto.
  + intros. unfold strel at 1 in H9. simpl in H9. unfold strel at 1 in H10. simpl in H10.
    eapply P3; eauto.
Qed.

(* term equivalence preservation for the second program *)

Theorem store_invariance3 : forall t G T p p' fr q e
  (W: has_type G t T p fr q e),
  forall M H1 H2, env_type M H1 H2 G (plift p) ->
  forall S1 S2, store_type S1 S2 M ->
                (forall l1 l2, strel M l1 l2 -> ~ p' l2) ->
  forall S2' MS2', store_effect S2 S2' p' ->
                 length S2 <= length S2' ->
                 sst_chain (st2 M) MS2' ->
                 sstore_type S2' MS2' ->
  exists S1' S2'' M' v1 v2,
  exp_type S1 S2' (st1 M, MS2', strel M, st_valtype M) H1 H2 t t S1' S2'' M' v1 v2 T (plift p) fr (plift q) (plift e).
Proof. 
  intros. 
  assert (length S2' = length MS2') as L1. { destruct H7; intuition. }
  assert (length S1 = length (st1 M)) as L2. { destruct H0 as [[? ?] ?]; intuition. }
  assert (length S2 = length (st2 M)) as L3. { destruct H0 as [? [[? ?] ?]]; intuition. }
  assert (st_filter M (locs_locs_stty (st1 M) (vars_locs H1 (plift p))) (locs_locs_stty (st2 M) (vars_locs H2 (plift p)))) as STF. {
    eapply envt_filter_deep; eauto. intros ? ?. auto.
  }
  eapply fundamental_property; eauto.
  - eapply envt_store_change; eauto.
    assert (psub (locs_locs_stty (st1 M) (vars_locs H1 (plift p))) (st_locs1 M)). {
      eapply envt_store_deep_wf; eauto. intros ? ?. eauto. }
    assert (psub (locs_locs_stty (st2 M) (vars_locs H2 (plift p))) (st_locs2 M)). {
      eapply envt_store_deep_wf; eauto. intros ? ?. eauto. }
    unfold st_chain_partial. simpl. intuition.
    + unfold st_filter; intuition.
      * intros ? ?. unfold st_locs2, pnat, length2, st2. simpl.
        eapply H9 in H10. unfold st_locs2, pnat, length2 in H10. lia.
      * destruct STF as [? [? ?]]. eapply H14; eauto.
      * destruct STF as [? [? ?]]. eapply H14; eauto.
    + unfold sst_chain_partial; intuition.
    + unfold sst_chain_partial; intuition.
      * intros ? ?. eapply H9 in H10. unfoldq; intuition. unfold st2. simpl. eapply sst_mono in H6.  unfold st_locs2, pnat, length2 in H10. lia.
      * destruct H6 as [A [B C]]. eapply H9 in H10. eapply C in H10. unfold st2 at 2. simpl. auto.
  - unfold st_filter, st_locs1, st_locs2, pnat, length1, length2; intuition.
    + intros ? ?. auto.
    + intros ? ?. auto.
    + unfold strel at 1 in H8. simpl in H8. unfold st2 at 1. simpl. 
      destruct H0 as [? [? [? [? ?]]]]. destruct (H11 l1 l2) as [? [? [? [? [? [? [? ?]]]]]]]; auto.
      apply indexr_var_some' in H15. lia.
    + unfold strel at 1 in H8. simpl in H8. unfold st1 at 1. simpl. 
      destruct H0 as [? [? [? [? ?]]]]. destruct (H11 l1 l2) as [? [? [? [? [? [? [? ?]]]]]]]; auto.
      apply indexr_var_some' in H14. lia.
  -  (* store type *)
    destruct H0 as (? & ? & P1 & P2 & P3).
    split. 2: split. 3: split. 4: split.
    + repeat split.
      * unfold st1. simpl. auto.
      * intros. unfold st1. simpl. destruct H0 as [A B] .
        destruct (B l) as [qt [v [IM [IS [Q1 Q2]]]]]; auto.
    + repeat split.
      * unfold st2 at 1. simpl. lia.
      * intros. unfold st2. simpl. destruct H7 as [A B] .
        destruct (B l) as [qt [v [IM [IS [Q1 Q2]]]]]; auto.
    + intros ? ? STR. unfold strel at 1 in STR. simpl in STR. 
      destruct (P1 l1 l2) as (vt & qt1 & qt2 & b1 & b2 & IM1 & IM2 & IS1 & IS2 & SVT & VT & STF'). eauto.
      exists vt, qt1, qt2, b1, b2; intuition.
      * unfold st2 at 1. simpl. destruct H6 as [D [E F]].
        assert (pdom (st2 M) l2). unfoldq; intuition. apply indexr_var_some' in IM2. auto.
        eapply F in H6. congruence.
      * eapply H4. intros ?. eapply H3; eauto. auto. 
      * destruct STF' as [SFA [SFB SFC]].
        repeat split. 
        -- remember H0 as H0'. clear HeqH0'. destruct H0 as [? ?]. 
           unfold st1 at 1. unfold st_locs1, pnat, length1 at 1. simpl. 
           eapply lls_closed'. eauto. intros ? ?.  eapply val_lls with (M := st1 M) in H10; eauto.
           eapply SFA in H10. unfold st_locs1, pnat, length1 in H10. unfold pnat. lia.
        -- eapply lls_closed'; eauto.
           intros ? ?.  unfold st2 at 1. unfold pnat, length2, st2. simpl. 
           eapply val_lls with (M := st2 M) in H9; eauto. eapply SFB in H9.
           unfold st_locs2, pnat, length2 in H9. lia.
        -- unfold strel at 1 in H9. simpl in H9.  intros.
           unfold st1 in H10. simpl in H10. unfold st2. simpl.
           eapply SFC in H10; eauto.
           erewrite <- lls_change with (M := st2 M); eauto.
           eapply sstchain_tighten; eauto. 
        -- unfold strel at 1 in H9. simpl in H9.  intros.
           unfold st2 at 1 in H10. simpl in H10.
           erewrite <- lls_change with (M := st2 M) in H10.
           eapply SFC in H9; intuition.
           eapply sstchain_tighten; eauto. 
    + intros. unfold strel at 1 in H9. simpl in H9. unfold strel at 1 in H10. simpl in H10.
      eapply P2; eauto.
    + intros. unfold strel at 1 in H9. simpl in H9. unfold strel at 1 in H10. simpl in H10.
      eapply P3; eauto.
Qed.


Definition st_tighten H1 (H2: venv) p M :=
(length1 M, length2 M, fun l1 l2 => vars_locs H1 p l1 /\ vars_locs H2 p l2 /\ strel M l1 l2).


Definition st_tighten1 H1 (H2: venv) p M :=
(length1 M, length2 M, fun l1 l2 => vars_locs H1 p l1 /\ vars_locs H2 p l2 /\ strel M l1 l2).


(* term equivalence preservation & reachability for the first program *)

Theorem store_invariance2' : forall t G T p fr q e 
  (W: has_type G t T p fr q e),
  forall M H1 H2, env_type M H1 H2 G (plift p) ->
  forall S1 S2, store_type S1 S2 M ->
  forall S1' MS1' p', store_effect S1 S1' p' ->  
                 length S1 <= length S1' ->
                 sst_chain (st1 M) MS1' ->
                 sstore_type S1' MS1' ->
                 psub (pand (locs_locs_stty (st1 M) (vars_locs H1 (plift p))) p') pempty ->
  exists S1'' S2' M' v1 v2,
  exp_type S1' S2 (MS1', st2 M, fun l1 l2 => 
                    ~ p' l1 /\ 
                    psub(pand (por (pdiff (pnat (length MS1')) (pnat (length1 M))) (pnot (locs_locs_stty (st1 M) (vars_locs H1 (plift p)))))(locs_locs_stty (st1 M) (pone l1))) pempty /\ 
                    strel M l1 l2, 
                  fun l1 l2 v1 v2 => ~ p' l1  /\ psub(pand (por (pdiff (pnat (length MS1')) (pnat (length1 M))) (pnot (locs_locs_stty (st1 M) (vars_locs H1 (plift p))))) (locs_locs_stty (st1 M) (pone l1))) pempty /\ st_valtype M l1 l2 v1 v2) 
                  H1 H2 t t S1'' S2' M' v1 v2 T (plift p) fr (plift q) (plift e).
Proof.
  intros.
  remember (st1 M, st2 M, 
            fun l1 l2 => ~ p' l1  /\ psub(pand (por (pdiff (pnat (length MS1')) (pnat (length1 M))) (pnot (locs_locs_stty (st1 M) (vars_locs H1 (plift p))))) (locs_locs_stty (st1 M) (pone l1))) pempty /\ strel M l1 l2, 
            fun l1 l2 v1 v2  => ~ p' l1 /\ psub(pand (por (pdiff (pnat (length MS1')) (pnat (length1 M))) (pnot (locs_locs_stty (st1 M) (vars_locs H1 (plift p))))) (locs_locs_stty (st1 M) (pone l1))) pempty /\ st_valtype M l1 l2 v1 v2 ) as Q.
  assert (st_chain_partial M Q (locs_locs_stty (st1 M) (vars_locs H1 (plift p))) (locs_locs_stty (st2 M) (vars_locs H2 (plift p)))). {
    assert (psub (locs_locs_stty (st1 M) (vars_locs H1 (plift p))) (st_locs1 M)). {
      eapply envt_store_deep_wf in H; eauto. destruct H. eauto. intros ? ?. eauto. }
    assert (psub (locs_locs_stty (st2 M) (vars_locs H2 (plift p))) (st_locs2 M)). {
      eapply envt_store_deep_wf in H; eauto. destruct H. eauto. intros ? ?. eauto. }
    assert (st_locs1 Q = st_locs1 M). {
     subst Q. unfold st_locs1, pnat, length1, st1. simpl. auto.
    }
    assert (st_locs2 Q = st_locs2 M). { 
      subst Q. unfold st_locs2, pnat, length2, st2. simpl. auto.
    }
    unfold st_chain_partial. intuition.
    + eapply envt_filter_deep; eauto. intros ? ?. auto.
    + subst Q. repeat split.
      - unfold st_locs1, pnat, length1, st1 in *. simpl. auto.
      - unfold st_locs2, pnat, length2, st2 in *. simpl. auto.
      - unfold strel at 1 in H12. simpl in H12. intuition. eapply envt_filter_deep; eauto. intros ? ?. auto.
      - unfold strel at 1 in H12. simpl in H12. intuition. eapply envt_filter_deep; eauto. intros ? ?. auto.
    + subst Q. repeat split.
      - unfold st_locs1, pnat, length1 in H8. unfold pdom. auto.
      - unfold st_locs1, pnat, length2 in H8. unfold pdom. auto.
    + subst Q. unfold sst_chain_partial. simpl. intuition.
    + subst Q. simpl. eapply functional_extensionality. intros. eapply functional_extensionality. intros. 
      eapply propositional_extensionality. split; intros. repeat split; auto. intuition. eapply H7; eauto. split. eauto. eauto.
      intros ? ?. destruct H16. unfold pdiff, pnat in *. destruct H16.  eapply lls_filter in H17. eapply lls_filter in H12 as H12'.
      assert (psub (locs_locs_stty (st1 M) (pone x1)) (pnat (length1 M))). {
        intros ? ?. eapply H17 in H18. eapply H12' in H18. eapply envt_store_deep_wf in H18; eauto. intros ? ?. auto. 
      }
      assert (locs_locs_stty (st1 M) (pone x1) x1). left. unfold pone. auto. eapply H18 in H19. unfold pnat, st1 in H19. lia.
      eapply lls_filter in H17.
      eapply lls_reach_trans in H12; eauto. eapply H16.
      assert (locs_locs_stty (st1 M) (pone x1) x1). { left. unfold pone. auto. }
      eapply H12 in H18. auto.
      destruct H15 as [? [?  ?]]. auto.  
    + subst Q. unfold strel. simpl. split. intros. eapply H7. split. eauto. eauto. intuition.
      intros ? ?. destruct H15. unfold pdiff, pnat in H15.
      assert (psub (locs_locs_stty (st1 M) (pone x)) (pnat (length1 M))). {
        intros ? ?. eapply lls_filter in H16. eapply H16 in H17. eapply lls_filter in H13 as H13'. eapply H13' in H17. 
        eapply envt_store_deep_wf in H17; eauto. intros ? ?. auto.
      }
      assert (locs_locs_stty (st1 M) (pone x) x). left. unfold pone. auto. destruct H15. 
      eapply H17 in H18. unfold pnat, st1 in H18. lia.
      eapply lls_filter in H16. eapply lls_reach_trans in H13. 2: { intros ? ?. eauto. } eapply H16 in H18. eapply H13 in H18. contradiction. 

    + subst Q. unfold strel in H12. simpl in H12. intuition.
  }

  eapply store_invariance2 with (M:=Q) (S1:=S1) (S2:=S2) (S1':=S1') (p':=p') in W.
  2: { eapply envt_store_change; eauto. }
  2: { subst Q. destruct H0 as [[S1A S1B][[S2A S2B] [P [U2 U1]]]].
       unfold store_type, sstore_type. repeat split. 
       - unfold st1. simpl. auto.
       - eapply S1B.
       - unfold st2. simpl. auto.
       - eapply S2B.
       - simpl. intros. unfold strel at 1 in H0. simpl in H0. destruct H0 as [? [? ?]].
         destruct (P l1 l2) as [vt [qt1 [qt2 [v1 [v2 [IM1 [IM2 [IS1 [IS2 [SVT [VTT SF]]]]]]]]]]]; auto.
         exists vt, qt1, qt2, v1, v2; intuition.
         (* st_valtype *)
         eapply functional_extensionality. intros. eapply functional_extensionality. intros. 
         eapply propositional_extensionality. split; intros. destruct H11 as [? [? ?]]. subst. auto.
         split. intros ?. contradiction.
         repeat split; auto. subst. auto.
         (* st_filter *)
         destruct SF as [SF1 [SF2 SF3]].
         unfold st_filter. repeat split.
         + intros ? ?. unfold st1 at 1 in H11. simpl in H11.
           unfold st_locs1, pnat, length1, st1. simpl. eapply SF1; auto.
         + intros ? ?. unfold st2 at 1 in H11. simpl in H11.
           unfold st_locs2, pnat, length2, st2. simpl. eapply SF2; auto.
         + intros. unfold strel in H11. simpl in H11. destruct H11 as [? [? ?]].
           unfold st1, pnat, length1, st1 in H13. simpl in H13.
           unfold st2, pnat, length2, st2. simpl. eapply SF3; eauto.
         + intros. unfold strel in H11. simpl in H11. destruct H11 as [? [? ?]].
           unfold st2, pnat, length2, st2 in H12. simpl in H12.
           unfold st1, pnat, length1, st1. simpl. eapply SF3; eauto.
        - intros. unfold strel in H0, H9. simpl in H0, H9. destruct H0 as [? [? ?]]. destruct H9 as [? [? ?]].
          eapply U2; eauto.
        - intros. unfold strel in H0, H9. simpl in H0, H9. destruct H0 as [? [? ?]]. destruct H9 as [? [? ?]].
          eapply U1; eauto.
  }
  2: { intros. subst Q. unfold strel in H9. simpl in *. destruct H9 as [? [? ?]]. auto.  }
  2: eauto.
  2: eauto.
  2: { subst Q. eapply H5. }
  2: { eauto.   }

  subst Q. simpl. destruct W as (S1'' & S2'' & M'' & v1'' & v2'' & ?).
  destruct H9 as [? [? [? [? [? [? [? [? [? ?]]]]]]]]].
  exists S1'', S2'', M'', v1'', v2''.
  split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 8: split. 9: split.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
Qed. 

(* term equivalence preservation & reachability for the second program *)

Theorem store_invariance3' : forall t G T p fr q e 
  (W: has_type G t T p fr q e),
  forall M H1 H2, env_type M H1 H2 G (plift p) ->
  forall S1 S2, store_type S1 S2 M ->
  forall S2' MS2' p', store_effect S2 S2' p' ->  
                 length S2 <= length S2' ->
                 sst_chain (st2 M) MS2' ->
                 sstore_type S2' MS2' ->
                 psub (pand (locs_locs_stty (st2 M) (vars_locs H2 (plift p))) p') pempty ->
  exists S1' S2'' M' v1 v2,
  exp_type S1 S2' (st1 M, MS2', 
                  fun l1 l2 => ~ p' l2 /\ psub(pand (por (pdiff (pnat (length MS2')) (pnat (length2 M))) (pnot (locs_locs_stty (st2 M) (vars_locs H2 (plift p))))) (locs_locs_stty (st2 M) (pone l2))) pempty /\ 
                                strel M l1 l2, 
                  fun l1 l2 v1 v2 => ~p' l2 /\ psub(pand (por (pdiff (pnat (length MS2')) (pnat (length2 M))) (pnot (locs_locs_stty (st2 M) (vars_locs H2 (plift p))))) (locs_locs_stty (st2 M) (pone l2))) pempty /\ 
                                 st_valtype M l1 l2 v1 v2) 
           H1 H2 t t S1' S2'' M' v1 v2 T (plift p) fr (plift q) (plift e).
Proof.
  intros.
  remember (st1 M, st2 M, fun l1 l2 => ~p' l2  /\ psub(pand (por (pdiff (pnat (length MS2')) (pnat (length2 M))) (pnot (locs_locs_stty (st2 M) (vars_locs H2 (plift p))))) (locs_locs_stty (st2 M) (pone l2))) pempty /\ strel M l1 l2, 
            fun l1 l2 v1 v2 => ~p' l2 /\ psub(pand (por (pdiff (pnat (length MS2')) (pnat (length2 M))) (pnot (locs_locs_stty (st2 M) (vars_locs H2 (plift p))))) (locs_locs_stty (st2 M) (pone l2))) pempty /\ st_valtype M l1 l2 v1 v2) as Q.
  assert (st_chain_partial M Q (locs_locs_stty (st1 M) (vars_locs H1 (plift p))) (locs_locs_stty (st2 M) (vars_locs H2 (plift p)))). {
    assert (psub (locs_locs_stty (st1 M) (vars_locs H1 (plift p))) (st_locs1 M)). {
      eapply envt_store_deep_wf in H; eauto. destruct H. eauto. intros ? ?. eauto. }
    assert (psub (locs_locs_stty (st2 M) (vars_locs H2 (plift p))) (st_locs2 M)). {
      eapply envt_store_deep_wf in H; eauto. destruct H. eauto. intros ? ?. eauto. }
    assert (st_locs1 Q = st_locs1 M). {
     subst Q. unfold st_locs1, pnat, length1, st1. simpl. auto.
    }
    assert (st_locs2 Q = st_locs2 M). { 
      subst Q. unfold st_locs2, pnat, length2, st2. simpl. auto.
    }
    unfold st_chain_partial. intuition.
    + eapply envt_filter_deep; eauto. intros ? ?. auto.
    + subst Q. repeat split.
      - unfold st_locs1, pnat, length1, st1 in *. simpl. auto.
      - unfold st_locs2, pnat, length2, st2 in *. simpl. auto.
      - unfold strel at 1 in H12. simpl in H12. intuition. eapply envt_filter_deep; eauto. intros ? ?. auto.
      - unfold strel at 1 in H12. simpl in H12. intuition. eapply envt_filter_deep; eauto. intros ? ?. auto.
    + subst Q. repeat split.
      - unfold st_locs1, pnat, length1 in H8. unfold pdom. auto.
      - unfold st_locs1, pnat, length2 in H8. unfold pdom. auto.
    + subst Q. unfold sst_chain_partial. simpl. intuition.
    + subst Q. simpl. eapply functional_extensionality. intros. eapply functional_extensionality. intros. 
      eapply propositional_extensionality. split; intros. split; auto. intros.  eapply H7. split. eauto. auto.
      split. 
      intros ? ?. destruct H16. unfold pdiff in H16. destruct H16.
      assert (psub (locs_locs_stty (st2 M) (pone x1)) (pnat (length2 M))). {
        intros ? ?. eapply lls_filter in H17. eapply H17 in H18. eapply lls_filter in H13 as H13'. eapply H13' in H18. 
        eapply envt_store_deep_wf in H18; eauto. intros ? ?. auto.
      }
      assert (locs_locs_stty (st2 M) (pone x1) x1). left. unfold pone. auto. eapply H18 in H19. unfold pnat, st2 in *. lia.
      eapply lls_filter in H17. eapply lls_reach_trans in H13. 2: { intros ? ?.  eauto. } 
      assert (locs_locs_stty (st2 M) (pone x1) x1). { left. unfold pone. auto. }
      eapply H17 in H18. eapply H13 in H18. contradiction.
      auto.
      destruct H15 as [? [? ?]]. auto.
    + subst Q. unfold strel. simpl. intuition. eapply H7. split. eauto. auto.
      intros ? ?. destruct H15. unfold pdiff in H15. destruct H15.
      assert (psub (locs_locs_stty (st2 M) (pone x)) (pnat (length2 M))). {
        intros ? ?. eapply lls_filter in H16. eapply H16 in H17. eapply lls_filter in H14 as H14'. eapply H14' in H17. 
        eapply envt_store_deep_wf in H17; eauto. intros ? ?. auto.
      }
      assert (locs_locs_stty (st2 M) (pone x) x). left. unfold pone. auto. eapply H17 in H18. unfold pnat, st2 in *. lia.
      eapply lls_filter in H16. eapply lls_reach_trans in H14. 2: { intros ? ?. eauto. }
      assert (locs_locs_stty (st2 M) (pone x) x). left. unfold pone. auto. eapply H16 in H17. eapply H14 in H17. contradiction.

    + subst Q. unfold strel in H12. simpl in H12. intuition.
  }

  eapply store_invariance3 with (M:=Q) (S1:=S1) (S2:=S2) (S2':=S2') (p':=p') in W.
  2: { eapply envt_store_change; eauto. }
  2: { subst Q. destruct H0 as [[S1A S1B][[S2A S2B] [P [U2 U1]]]].
       unfold store_type, sstore_type. repeat split. 
       - unfold st1. simpl. auto.
       - eapply S1B.
       - unfold st2. simpl. auto.
       - eapply S2B.
       - simpl. intros. unfold strel at 1 in H0. simpl in H0. destruct H0 as [? [? ?]].
         destruct (P l1 l2) as [vt [qt1 [qt2 [v1 [v2 [IM1 [IM2 [IS1 [IS2 [SVT [VTT SF]]]]]]]]]]]; auto.
         exists vt, qt1, qt2, v1, v2; intuition.
         (* st_valtype *)
         eapply functional_extensionality. intros. eapply functional_extensionality. intros. 
         eapply propositional_extensionality. split; intros. destruct H11 as [? [? ?]]. subst. auto.
         repeat split; auto. subst. auto.
         (* st_filter *)
         destruct SF as [SF1 [SF2 SF3]].
         unfold st_filter. repeat split.
         + intros ? ?. unfold st1 at 1 in H11. simpl in H11.
           unfold st_locs1, pnat, length1, st1. simpl. eapply SF1; auto.
         + intros ? ?. unfold st2 at 1 in H11. simpl in H11.
           unfold st_locs2, pnat, length2, st2. simpl. eapply SF2; auto.
         + intros. unfold strel in H11. simpl in H11. destruct H11 as [? [? ?]].
           unfold st1, pnat, length1, st1 in H12. simpl in H12.
           unfold st2, pnat, length2, st2. simpl. eapply SF3; eauto.
         + intros. unfold strel in H11. simpl in H11. destruct H11 as [? [? ?]].
           unfold st2, pnat, length2, st2 in H12. simpl in H12.
           unfold st1, pnat, length1, st1. simpl. eapply SF3; eauto.
        - intros. unfold strel in H0, H9. simpl in H0, H9. destruct H0 as [? [? ?]]. destruct H9 as [? [? ?]].
          eapply U2; eauto.
        - intros. unfold strel in H0, H9. simpl in H0, H9. destruct H0 as [? [? ?]]. destruct H9 as [? [? ?]].
          eapply U1; eauto.
  }
  2: { intros. subst Q. simpl in *. intros ?.
       unfold strel in H9. simpl in H9. destruct H9 as [? [? ?]]. 
       eapply H7. unfoldq. intuition.  }
  2: eauto.
  2: eauto.
  2: { subst Q. eapply H5. }
  2: { eauto. }

  subst Q. simpl. destruct W as (S1'' & S2'' & M'' & v1'' & v2'' & ?).
  destruct H9 as [? [? [? [? [? [? [? [? [? ?]]]]]]]]].
  exists S1'', S2'', M'', v1'', v2''.
  split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 8: split. 9: split.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  Unshelve. auto.
Qed.         

