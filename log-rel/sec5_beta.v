(**********************************************************************************************
* Coq mechanization of the beta rule in the λ^♦_{\varepsilon}-caluclus.
***********************************************************************************************)

(* based on sec6_reach_binary_effs.v *)

(* 

Simply-typed lambda calculus with higher-order mutable store and reachability types, 
proof of beta-inilining rule using binary logical relations


THIS FILE:
- types and qualifiers
  - overlap (explicit transitive closure)
  - self refs
  - fresh flag
  - no parametric polymorphism

- references
  - higher-order refs
  - mutation with put/get

- effects
  - observable write effets

Internals:
  - Semantic weakening lemma
  - Semantic substitution lemma
  - The beta-inlining theorem

*)

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
Require Import sec5_store_invariants_effs.

Import STLC.

(*******************************************************************************
* Syntactic Definitions
* - qualifier splicing 'splice_ql' (splice_pl)
* - type splicing 'splice_ty'
* - term splicing 'splice_tm'
* - qualifier substitution 'subst_ql' (subst_pl)
* - type substitution 'subst_ty'  
* - term substitution 'subst_tm'
*
* Semantic Definitions
* - term interpretation for semantic weakening and semantic substitution 'exp_type1'
* - semantic context interpretation for semantic weakening 'env_type1'
* - semantic typing for semantic weakening 'sem_type1'
* - semantic context interpretation for semantic substitution 'env_type_subst2'
*******************************************************************************)


Definition splice_nat x i n :=
  if x <? i then x else x + n.

Definition splice_ql (b: ql)(i: nat)(n: nat): ql := 
  fun x => if x <? i then b x else (i + n <=? x) && b (x - n).

Definition splice_pl (b: pl)(i: nat)(n: nat): pl := 
  fun x => (x < i) /\ b x \/ (i + n <= x) /\ b (x - n).

Lemma plift_splice: forall q i n,
    plift (splice_ql q i n) = splice_pl (plift q) i n.
Proof.
    intros. unfold plift. eapply functional_extensionality.
    intros. eapply propositional_extensionality.
    split; intros. unfold splice_ql in H.
    destruct (x <? i) eqn: Heqn; intuition. 
    unfold splice_pl. left. intuition. apply Nat.ltb_lt; auto.
    unfold splice_pl. right. apply andb_true_iff in H. intuition.
    apply Nat.leb_le in H0; auto.
    unfold splice_ql. unfold splice_pl in H. 
    destruct (x <? i) eqn: Heqn. intuition. apply Nat.ltb_lt in Heqn. intuition.
    destruct H. destruct H. apply Nat.ltb_lt in H. rewrite H in Heqn. intuition.
    apply andb_true_iff. intuition.
    apply Nat.leb_le. auto.
Qed.

Fixpoint splice_tm (t: tm) (i: nat) (n:nat) : tm := 
  match t with 
  | ttrue         => ttrue
  | tfalse        => tfalse
  | tref t        => tref (splice_tm t i n)
  | tget t        => tget (splice_tm t i n)
  | tput t1 t2    => tput (splice_tm t1 i n)(splice_tm t2 i n)
  | tvar x        => tvar (if x <? i then x else x + n)
  | tapp t1 t2    => tapp (splice_tm t1 i n) (splice_tm t2 i n)
  | tabs q t      => tabs (splice_ql q i n) (splice_tm t i n)
  | tseq t1 t2    => tseq (splice_tm t1 i n)(splice_tm t2 i n)
end.

Fixpoint splice_ty (T : ty) (i: nat) (n: nat) : ty :=
  match T with 
  | TBool                       => TBool
  | TRef T fr q                 => TRef (splice_ty T i n) fr (splice_ql q i n)
  | TFun T1 fn1 fr1 q1 T2 fn2 ar2 fr2 q2 e2f e2x e2            
                                => TFun (splice_ty T1 i n) fn1 fr1 (splice_ql q1 i n) 
                                        (splice_ty T2 i n) fn2 ar2 fr2 (splice_ql q2 i n) 
                                        e2f e2x (splice_ql e2 i n) 
end.

Definition subst_pl (q: pl)(i: nat)(u: pl) : pl :=
  fun x => 
    let q' := 
      fun y => i <= y /\ q(y+1) \/ (i > y) /\ q y
    in
    q i /\ (por q' u) x \/ q' x.

Definition subst_ql (q: ql) (i: nat) (u:ql): ql :=
  fun x => 
  let q' x := if i <=? x then q(x+1) else q x 
  in 
    if q i then (qor q' u) x else q' x.

Lemma plift_subst: forall q i u,
  plift (subst_ql q i u) = subst_pl (plift q) i (plift u).
Proof.
  intros. unfold plift. eapply functional_extensionality.
  intros. eapply propositional_extensionality.
  split; intros. 
  + unfold subst_ql in H. unfold subst_pl. 
    destruct (q i) eqn: Heqn; simpl in *.
    unfoldq; intuition.
    left; intuition. rewrite qor_true_iff in H.
    destruct H. 
    bdestruct (i <=? x); intuition. right. auto.
    bdestruct (i <=? x); intuition.
  + unfold subst_pl in H. unfold subst_ql.
    destruct (q i) eqn: Heqn.
    unfoldq; intuition. 
    rewrite qor_true_iff. bdestruct (i <=? x); intuition.
    rewrite qor_true_iff. bdestruct (i <=? x); intuition.
    rewrite qor_true_iff. bdestruct (i <=? x); intuition.
    rewrite qor_true_iff. bdestruct (i <=? x); intuition.
    rewrite qor_true_iff. bdestruct (i <=? x); intuition.
    bdestruct (i <=? x); intuition.
Qed.



Fixpoint subst_ty (t: ty )(i: nat) (p:ql) : ty := 
  match t with
  | TBool                           => TBool
  | TRef T fr q                     => TRef (subst_ty T i p) fr (subst_ql q i p)
  | TFun T1 fn1 fr1 q1 T2 fn2 ar2 fr2 q2 e2f e2x e2                            
                                    => TFun (subst_ty T1 i p) fn1 fr1 (subst_ql q1 i p)
                                            (subst_ty T2 i p) fn2 ar2 fr2 (subst_ql q2 i p) 
                                            e2f e2x (subst_ql e2 i p) 
end.


Fixpoint subst_tm (t: tm) (i: nat) (u:tm) (p:ql) : tm := 
  match t with 
  | ttrue         => ttrue
  | tfalse        => tfalse
  | tref t        => tref (subst_tm t i u p)
  | tget t        => tget (subst_tm t i u p)
  | tput t1 t2    => tput (subst_tm t1 i u p) (subst_tm t2 i u p)
  | tvar x        => if i =? x then u else if i <?  x then (tvar (pred x)) else (tvar x)   
  | tapp t1 t2    => tapp (subst_tm t1 i u p) (subst_tm t2 i u p)
  | tabs q t      => tabs (subst_ql q i p) (subst_tm t i (splice_tm u i 1) p)
  | tseq t1 t2    => tseq (subst_tm t1 i u p) (subst_tm t2 i u p)
end.



#[global] Hint Unfold splice_ql.
#[global] Hint Unfold subst_ql.
#[global] Hint Unfold subst_tm.

(*******************************************************************************

splice lemmas 

*******************************************************************************)


Lemma splice_pl_acc: forall q a b c,
  splice_pl (splice_pl q a b) a c =
  splice_pl q a (c + b).
Proof.
  intros. apply functional_extensionality.
  intros. apply propositional_extensionality.
  bdestruct (x <? a). 
  - unfold splice_pl. intuition.
  - bdestruct (x <? a+c+b).
    + unfold splice_pl. intuition.
    + unfold splice_pl.
      assert (x - c - b = x - (c + b)). lia. split.
      * right. intuition. congruence.
      * right. intuition. right. intuition. congruence.
Qed.

Lemma splice_ql_acc: forall q a b c,
  splice_ql (splice_ql q a b) a c =
  splice_ql q a (c + b).
Proof.
  intros. rewrite plift_qual_eq.
  repeat rewrite plift_splice.
  eapply splice_pl_acc.
Qed.

Lemma splicep_aux: forall p x i n,
    (splice_pl p i n) (splice_nat x i n) = p x.
Proof.
  intros. eapply propositional_extensionality.
  unfold splice_pl, splice_nat. simpl. 
  bdestruct (x <? i).
  - intuition. 
  - bdestruct (x + n <? i). lia.
    replace (x + n - n) with x. intuition. lia. 
Qed.

Lemma splicep_aux1: forall p x i n,
    (splice_pl p i n) x ->
    exists x', x = (splice_nat x' i n) /\ p x'.
Proof.
  intros. destruct H.
  - exists x. intuition. unfold splice_nat.
    bdestruct (x <? i); lia.
  - exists (x - n). intuition. unfold splice_nat.
    bdestruct (x - n <? i); lia.
Qed.

Lemma splice_acc: forall e1 a b c,
  splice_tm (splice_tm e1 a b) a c =
  splice_tm e1 a (c+b).
Proof. 
  induction e1; intros; simpl; intuition.
  + bdestruct (i <? a); intuition.  
    bdestruct (i <? a); intuition.
    bdestruct (i + b <? a); intuition.   
  + specialize (IHe1 a b c). rewrite IHe1. auto.
  + specialize (IHe1 a b c). rewrite IHe1. auto.
  + specialize (IHe1_1 a b c). specialize (IHe1_2 a b c). 
    rewrite IHe1_1. rewrite IHe1_2. auto.
  + specialize (IHe1_1 a b c). specialize (IHe1_2 a b c). 
    rewrite IHe1_1. rewrite IHe1_2. auto.
  + specialize (IHe1 a b c). rewrite splice_ql_acc.
    rewrite IHe1. auto.
  + specialize (IHe1_1 a b c). specialize (IHe1_2 a b c). 
    rewrite IHe1_1. rewrite IHe1_2. auto.
Qed.

Lemma splicep_zero: forall q a,
  (splice_pl q a 0) = q.
Proof. 
  intros. apply functional_extensionality.
  intros. apply propositional_extensionality. 
  unfold splice_pl. intuition.
  replace x with (x - 0). eauto. lia.
  bdestruct (x <? a). intuition.
  replace (x - 0) with x. intuition. lia. 
Qed.

Lemma spliceq_zero: forall q a,
  (splice_ql q a 0) = q.
Proof. 
  intros. rewrite plift_qual_eq. repeat rewrite plift_splice. eapply splicep_zero.
Qed.

Lemma splicety_zero: forall T a,
  (splice_ty T a 0) = T.
Proof.
  intros T. induction T; intuition.
  simpl. rewrite IHT. auto.
  simpl. rewrite spliceq_zero. auto.
  simpl. rewrite IHT1. rewrite IHT2. repeat rewrite spliceq_zero. auto.
Qed.

Lemma splice_zero: forall e1 a,
  (splice_tm e1 a 0) = e1.
Proof. 
  intros. induction e1; simpl; intuition.
  + bdestruct (i <? a); intuition.
  + rewrite IHe1. auto.
  + rewrite IHe1. auto.
  + rewrite IHe1_1. rewrite IHe1_2. auto.
  + rewrite IHe1_1. rewrite IHe1_2. auto.
  + rewrite spliceq_zero. rewrite IHe1. auto.
  + rewrite IHe1_1. rewrite IHe1_2. auto.
Qed.

Lemma indexr_splice': forall{X} x (G1 G3: list X) T,
  indexr x (G3 ++ G1) = Some T ->
  x >= length G1 ->
  forall G2, 
  indexr (x + (length G2))(G3 ++ G2 ++ G1) = Some T.
Proof. 
  intros.
  induction G3; intros; simpl in *.
  + apply indexr_var_some' in H as H'. intuition.
  + bdestruct (x =? length (G3 ++ G1)); intuition.
    - subst. inversion H. subst.
      bdestruct (length (G3 ++ G1) + length G2 =? length (G3 ++ G2 ++ G1)); intuition.
      repeat rewrite app_length in H1.
      intuition.
    - bdestruct (x + length G2 =? length (G3 ++ G2 ++ G1)); intuition.
      apply indexr_var_some' in H2. intuition.
Qed.
     

Lemma indexr_splice: forall{X} (H2' H2 HX: list X) x,
  indexr (splice_nat x (length H2) (length HX)) (H2' ++ HX ++ H2) =
  indexr x (H2' ++ H2).
Proof.
  intros. unfold splice_nat. 
  bdestruct (x <? length H2); intuition.
  - repeat rewrite indexr_skips; auto. rewrite app_length. lia.
  - bdestruct (x <? length (H2' ++ H2)).
    + apply indexr_var_some in H0 as H0'.
      destruct H0' as [T H0']; intuition.
      rewrite H0'. apply indexr_splice'; auto.
    + apply indexr_var_none in H0 as H0'. rewrite H0'.
      rewrite indexr_var_none. 
      repeat rewrite app_length in *. lia.
Qed.

Lemma indexr_splice1: forall{X} (H2' H2: list X) x y,
  indexr (splice_nat x (length H2) 1) (H2' ++ y :: H2) =
  indexr x (H2' ++ H2).
Proof.
  intros. eapply (indexr_splice H2' H2 [y] x).
Qed.


Lemma indexr_shift : forall{X} (H H': list X) x vx v,
  x > length H  ->
  indexr x (H' ++ vx :: H) = Some v <->
  indexr (pred x) (H' ++ H) = Some v.
Proof. 
  intros. split; intros.
  + destruct x; intuition.  simpl.
  rewrite <- indexr_insert_ge  in  H1; auto. lia.
  + destruct x; intuition. simpl in *.
    assert (x >= length H). lia.
    specialize (indexr_splice' x H H' v); intuition.
    specialize (H3  [vx]); intuition. simpl in H3.
    replace (x + 1) with (S x) in H3. auto. lia.
Qed.

Lemma var_locs_splice: forall H H' HX x,
    var_locs (H'++HX++H) (splice_nat x (length H) (length HX)) =
    var_locs (H'++H) x.
Proof.
  intros. eapply functional_extensionality.
  intros. eapply propositional_extensionality.
  unfoldq. intuition.
  - destruct H0. exists x1. rewrite indexr_splice in H0. eauto.
  - destruct H0. exists x1. rewrite indexr_splice. eauto.
Qed.
  
Lemma vars_locs_splice: forall H H' HX q,
    vars_locs (H'++HX++H) (splice_pl q (length H) (length HX)) =
      vars_locs (H'++H) q.
Proof.
  intros. eapply functional_extensionality.
  intros. eapply propositional_extensionality.
  unfoldq. intuition.
  - destruct H0 as [? [? ?]].
    eapply splicep_aux1 in H0 as H2. 
    destruct H2. exists x1.
    intuition. subst x0. rewrite var_locs_splice in H1. eauto. 
  - destruct H0. exists (splice_nat x0 (length H) (length HX)).
    intuition. rewrite splicep_aux. eauto.
    rewrite var_locs_splice. eauto.
Qed.

Lemma splice_or: forall ef e1 m n,
  plift (splice_ql (qor ef e1) m n) =
  plift (qor (splice_ql ef m n) (splice_ql e1 m n)).
Proof.
  intros. rewrite plift_splice. repeat rewrite plift_or.
  eapply functional_extensionality.
  intros. eapply propositional_extensionality.
  repeat rewrite plift_splice; unfold splice_pl in *; unfoldq; intuition.
Qed. 

Lemma splice_qor: forall ef e1 m n,
  (splice_ql (qor ef e1) m n) =
  (qor (splice_ql ef m n) (splice_ql e1 m n)).
Proof.
  intros. rewrite plift_qual_eq. eapply splice_or.
Qed.

Lemma splice_and: forall ef e1 m n,
  plift (splice_ql (qand ef e1) m n) =
  plift (qand (splice_ql ef m n) (splice_ql e1 m n)).
Proof.
  intros. rewrite plift_splice. repeat rewrite plift_and.
  eapply functional_extensionality.
  intros. eapply propositional_extensionality.
  repeat rewrite plift_splice; unfold splice_pl in *; unfoldq; intuition.
Qed. 


Lemma splice_qand: forall ef e1 m n,
  (splice_ql (qand ef e1) m n) =
  (qand (splice_ql ef m n) (splice_ql e1 m n)).
Proof.
  intros. rewrite plift_qual_eq. eapply splice_and.
Qed.

Lemma splice_pand: forall ef e1 m n,
  (splice_pl (pand ef e1) m n) =
  (pand (splice_pl ef m n) (splice_pl e1 m n)).
Proof.
  intros.
  eapply functional_extensionality.
  intros. eapply propositional_extensionality.
  repeat rewrite plift_splice; unfold splice_pl in *; unfoldq; intuition.
Qed.

Lemma splice_por: forall ef e1 m n,
  (splice_pl (por ef e1) m n) =
  (por (splice_pl ef m n) (splice_pl e1 m n)).
Proof.
  intros.
  eapply functional_extensionality.
  intros. eapply propositional_extensionality.
  repeat rewrite plift_splice; unfold splice_pl in *; unfoldq; intuition.
Qed.

Lemma splice_pdiff: forall ef e1 m n,
  (splice_pl (pdiff ef e1) m n) =
  (pdiff (splice_pl ef m n) (splice_pl e1 m n)).
Proof.
  intros.
  eapply functional_extensionality.
  intros. eapply propositional_extensionality.
  unfold splice_pl in *; unfoldq; intuition.
Qed.

Lemma splicep_empty: forall m n,
    splice_pl pempty m n = pempty.
Proof.
  intros. apply functional_extensionality.
  intros. unfold splice_pl.
  eapply propositional_extensionality. 
  unfoldq; intuition.
Qed.


Lemma spliceq_empty: forall m n,
    splice_ql qempty m n = qempty.
Proof.
  intros. apply functional_extensionality.
  intros. unfold splice_ql.
  bdestruct (x <? m); intuition.
Qed.

Lemma splice_sep: forall qf q1 m n,
  psub (plift (qand  qf q1)) pempty ->
  psub (plift (qand (splice_ql qf m n) 
             (splice_ql q1 m n))) pempty.
Proof.
  intros. rewrite <- splice_and.
  assert (qand qf q1 = qempty).
  unfoldq.
  eapply functional_extensionality. intros.
  specialize (H x); intuition.
  destruct (qempty x) eqn: Heqn. 
  inversion Heqn. 
  destruct (qand qf q1 x) eqn: Heqn1.
  assert (plift qf x). intuition.
  assert (plift q1 x). intuition.
  intuition. auto.
  rewrite H0. rewrite spliceq_empty. 
  unfoldq; intuition.
Qed. 

Lemma splice_sub: forall q2 p m n,
   qsub q2 p ->
   qsub (splice_ql q2 m n)
        (splice_ql p  m n).
Proof.
  intros. unfoldq1. intros.
  unfold splice_ql in *.
  bdestruct (x <? m); intuition.
  bdestruct (m+n <=? x); intuition.
Qed.

Lemma splice_psub: forall q2 p m n,
   psub  q2 p ->
   psub (splice_pl q2 m n)
        (splice_pl p m n).
Proof.
  intros. unfoldq; intuition.
  unfold splice_pl in *. intuition.
Qed.

Lemma splicep_id: forall q i n,
  closed_ql i q ->
  splice_pl (plift q) i n = (plift q).
Proof.
  intros. unfold closed_ql in H.
  unfold splice_pl.
  eapply functional_extensionality.
  intros.  eapply propositional_extensionality.
  intuition. eapply H in H2. intuition. 
Qed.

Lemma spliceq_id: forall q i n,
  closed_ql i q ->
  splice_ql q i n = q.
Proof.
  intros. eapply splicep_id with (n := n) in H.
  rewrite <- plift_splice in H. 
  rewrite plift_qual_eq. auto.
Qed. 

Lemma splicety_id: forall T i n,
  closed_ty i T ->
  splice_ty T i n = T.
Proof.
  intros T. induction T; intros; intuition.
  + simpl. inversion H. subst. specialize (IHT i n H3). rewrite IHT. erewrite spliceq_id; eauto.
  + simpl. inversion H. subst. 
    specialize (IHT1 i n H6). specialize (IHT2 i n H14).
    rewrite IHT1. rewrite IHT2.
    erewrite spliceq_id; eauto. erewrite spliceq_id; eauto. erewrite spliceq_id; eauto.
Qed.

Lemma closedql_splice: forall{X} (H1 H HX: list X) q, 
  closed_ql (length (H1++H)) q  ->
  closed_ql (length (H1++HX++H))(splice_ql q (length H)(length HX)).
Proof.
  intros. unfold closed_ql in *.  intros.
  unfold splice_ql, splice_nat in H2. 
  bdestruct(x <? length H). 
  specialize (H0 x).  intuition. repeat rewrite app_length. lia.
  specialize (H0 (x- (length HX))).
  apply andb_true_iff in H2. destruct H2. 
  intuition. 
  repeat rewrite app_length in *.  lia.
Qed.

Lemma closedty_splice: forall{X} (H1 H HX: list X) T, 
  closed_ty (length (H1++H)) T ->
  closed_ty (length (H1++HX++H))(splice_ty T (length H)(length HX)).
Proof. 
  intros. induction T; intros; simpl; intuition.
  + inversion H0. subst. intuition. constructor; auto.
    eapply closedql_splice; eauto.
  + inversion H0. subst. intuition. constructor; auto.
    eapply closedql_splice; eauto. 
    eapply closedql_splice; eauto.
    eapply closedql_splice; eauto.
Qed.


Lemma qdom_slice: forall{X} (H2' H2 HX: list X) q1,
  qsub q1 (qdom (H2' ++ H2)) ->
  qsub (splice_ql q1 (length H2) (length HX))(qdom (H2' ++ HX ++ H2)).
Proof.
  intros. unfoldq1; intuition.
  unfold splice_ql, splice_nat in H0. 
  bdestruct (x <? length H2); intuition. 
  specialize (H x) as H'. intuition.
  repeat rewrite app_length in *. 
  bdestruct (x <? (length H2' + length H2)); intuition.
  bdestruct (x <? (length H2' + (length HX + length H2))). auto.
  lia.
  rewrite andb_true_iff in H0. intuition.
  eapply H in H4.
  repeat rewrite app_length in *.
  bdestruct (x - length HX <? length H2' + length H2); intuition.
  bdestruct (x <? length H2' + (length HX  + length H2)); intuition.
Qed. 

Lemma pdom_slice: forall{X} (H2' H2 HX: list X) q1,
  psub (plift q1) (pdom (H2' ++ H2)) ->
  psub (plift (splice_ql q1 (length H2) (length HX)))(pdom (H2' ++ HX ++ H2)).
Proof.
  intros. rewrite plift_splice.
  unfoldq; intuition. unfold splice_pl in H0.
  destruct H0. destruct H0.  repeat rewrite app_length. lia.
  destruct H0. eapply H in H1. repeat rewrite app_length in *. lia.
Qed.

Lemma pdom_slice': forall{X} (H2' H2 HX: list X) q1,
  psub q1 (pdom (H2' ++ H2)) ->
  psub (splice_pl q1 (length H2) (length HX))(pdom (H2' ++ HX ++ H2)).
Proof.
  intros. 
  unfoldq; intuition. unfold splice_pl in H0.
  destruct H0. destruct H0.  repeat rewrite app_length. lia.
  destruct H0. eapply H in H1. repeat rewrite app_length in *. lia.
Qed.

Lemma psub_splice: forall{X} p (H21 H22 HX : list X),
  psub (plift p) (pdom (H21++H22)) ->
  psub (plift (splice_ql p (length H22)(length HX))) (pdom (H21++HX++H22)).
Proof.
 intros. rewrite plift_splice.
 unfold splice_pl. unfoldq; intuition.
 repeat rewrite  app_length. lia.
 eapply H in H2. repeat rewrite app_length in *. lia.
Qed.

Lemma psub_splice': forall{X} p (H21 H22 HX : list X),
  psub p (pdom (H21++H22)) ->
  psub (splice_pl p (length H22)(length HX)) (pdom (H21++HX++H22)).
Proof.
 intros. 
 unfold splice_pl. unfoldq; intuition.
 repeat rewrite  app_length. lia.
 eapply H in H2. repeat rewrite app_length in *. lia.
Qed.

Lemma qsub_splice: forall{X} p (H H' HX : list X),
  qsub p (qdom (H'++H)) ->
  qsub (splice_ql p (length H)(length HX)) (qdom (H'++HX++H)).
Proof.
  intros. 
  assert (psub (plift p)(pdom (H'++H))).
  unfoldq1; intuition. unfoldq; intuition.
  specialize (H0 x); intuition.
  bdestruct (x <? length (H'++H)); intuition.
  eapply psub_splice with (HX := HX)  in H1.
  unfoldq; unfoldq1; intuition. specialize (H1 x); intuition.
  bdestruct (x <? length (H'++HX++H)); intuition.
Qed. 

Lemma splicep_one: forall{X}{Y} (H2' HX H2: list Y) (G:list X),
   length (H2' ++ HX ++ H2) = length G + length HX -> 
   splice_pl (pone (length G)) (length H2) (length HX) = pone(length (H2' ++ HX ++ H2)).
Proof.  
  intros. repeat rewrite app_length in *.
  unfold splice_pl, pone. eapply functional_extensionality. intros.
  eapply propositional_extensionality. intuition. 
Qed.

Lemma spliceq_one: forall{X}{Y} (H2' HX H2: list Y) (G:list X),
   length (H2' ++ HX ++ H2) = length G + length HX -> 
   splice_ql (qone (length G)) (length H2) (length HX) = qone(length (H2' ++ HX ++ H2)).
Proof.  
  intros. repeat rewrite app_length in *.
  rewrite plift_qual_eq. repeat rewrite plift_splice. repeat rewrite plift_one.
  unfold splice_pl, pone. eapply functional_extensionality. intros.
  eapply propositional_extensionality. intuition. 
Qed.

(*******************************************************************************

substitution lemmas 

*******************************************************************************)

Lemma substp_empty: forall m p,
  subst_pl pempty m p = pempty.
Proof.
  intros. eapply functional_extensionality.
  intros. eapply propositional_extensionality.
  unfoldq; intuition. unfold subst_pl in H. intuition.
Qed.

Lemma substq_empty: forall m p,
  (subst_ql qempty m p) = qempty.
Proof.
  intros. unfold subst_ql.
  eapply functional_extensionality.
  intros.  destruct (qempty m) eqn: Heqn.
  unfold qempty in Heqn. intuition.
  bdestruct (m <=? x); intuition.
Qed.

Lemma substp_id: forall q m p,
  closed_ql m p ->
  subst_pl (plift p) m q = (plift p).
Proof.
  intros. unfold closed_ql in H.
  eapply functional_extensionality.
  intros. eapply propositional_extensionality.
  split; intros.
  + unfold subst_pl in H0. intuition.
    specialize (H m H0). intuition.
    eapply H in H2. intuition.
  + unfold subst_pl; intuition.
Qed.  

Lemma substp_id': forall q m (p: pl),
  (forall x, p x -> x < m) ->
  subst_pl p m q = p.
Proof.
  intros. 
  eapply functional_extensionality.
  intros. eapply propositional_extensionality.
  split; intros.
  + unfold subst_pl in H0. intuition.
    unfoldq; intuition.
    specialize (H m H0). intuition.
    eapply H in H0. intuition. eapply H in H2. lia.
  + unfold subst_pl; intuition.
Qed.  


Lemma substq_id: forall q m p,
  closed_ql m p ->
  subst_ql p m q = p.
Proof.
  intros. eapply substp_id in H.
  rewrite plift_qual_eq. rewrite plift_subst. eauto.
Qed.  


Lemma substy_id: forall T m q,
  closed_ty m T ->
  subst_ty T m q = T.
Proof.
  intros T. induction T; intros; simpl. auto.
  - inversion H. subst. rewrite IHT; auto. rewrite substq_id; auto. 
  - inversion H. subst. rewrite IHT1; auto. rewrite IHT2; auto. 
    rewrite substq_id; auto. rewrite substq_id; auto. rewrite substq_id; auto.
Qed.  

Lemma plift_mem: forall m p,
  plift p m <-> p m = true.
Proof. 
  intros m. destruct m; intros; intuition.
Qed.

Lemma subst_ql_pl: forall m p q x,
  subst_ql p m q x = true <-> subst_pl (plift p) m (plift q) x.
Proof.
  intros. unfold subst_ql, subst_pl.
  split; intros.
  + destruct (p m) eqn: Heqn; intuition. 
    rewrite qor_true_iff in H.
    bdestruct (m <=? x); intuition.
    left. intuition. unfoldq; intuition.
    left. intuition. unfoldq; intuition.
    bdestruct (m <=? x); intuition.
  + unfoldq; intuition; 
    destruct (p m) eqn: Heqn; intuition. 
    1,3,5,7,9: rewrite qor_true_iff.
    all: bdestruct (m <=? x); intuition.
    1,2: rewrite plift_mem in H; rewrite H in Heqn; intuition.
Qed.

Lemma substp_closed: forall m n  p q,
  closed_ql (m +  S n) p ->
  closed_ql n q ->
  closed_ql (m + n) (subst_ql p n q).
Proof.
  intros. unfold closed_ql in *.
  intros.
  rewrite subst_ql_pl in H1.  
  unfold subst_pl in H1. unfoldq; intuition.
  eapply H in H4. lia.
  eapply H0 in H2. lia.
  eapply H in H3. lia.
Qed.

Lemma substp_closed': forall m n  (p q: pl),
  (forall x, p x -> x < (m+S n)) ->
  (forall x, q x -> x < n) ->
  (forall x, subst_pl p n q x -> x < m + n).
Proof.
  intros. unfold subst_pl in H1. unfoldq; intuition.
  eapply H in H4. lia.
  eapply H0 in H2. lia.
  eapply H in H3. lia.
Qed.

Lemma substy_closed_gen: forall T m n q1,
  closed_ty (m + S n) T ->
  closed_ql n q1 ->
  closed_ty (m+n) (subst_ty T n q1).
Proof.
  intros T. induction T; intros; simpl in *.
  + constructor.
  + inversion H. auto. constructor. eapply IHT; auto. eapply substp_closed; eauto. 
  + inversion H. subst. constructor. eapply IHT1; auto. eapply IHT2; auto. 
    eapply substp_closed; eauto. eapply substp_closed; eauto. eapply substp_closed; eauto. 
Qed.  

Lemma substp_and: forall q1 q2 m q3,
  psub (subst_pl (pand q1 q2) m q3) (pand (subst_pl q1 m q3) (subst_pl q2 m q3)).
Proof.
  intros. unfold subst_pl. unfoldq; intuition.
Qed.

Lemma substp_or: forall m q1 q2 q3,
  subst_pl (por q1 q2) m q3 = (por (subst_pl q1 m q3) (subst_pl q2 m q3)).
Proof.
  intros. apply functional_extensionality.
  intros. unfold subst_pl. eapply propositional_extensionality.
  unfoldq; intuition. 
Qed.

Lemma substq_or: forall m q1 q2 q3,
  subst_ql (qor q1 q2) m q3 = (qor (subst_ql q1 m q3) (subst_ql q2 m q3)).
Proof.
  intros. rewrite plift_qual_eq.  
  rewrite plift_or. repeat rewrite plift_subst. 
  rewrite plift_or. eapply substp_or.
Qed.

Lemma substp_empty_and: forall m q1 q2,
  subst_pl (pand q1 q2) m pempty = (pand (subst_pl q1 m pempty) (subst_pl q2 m pempty)).
Proof.
  intros. apply functional_extensionality.
  intros. unfold subst_pl. eapply propositional_extensionality.
  unfoldq; intuition. 
Qed.


Lemma substq_empty_and: forall m q1 q2,
  subst_ql (qand q1 q2) m qempty = (qand (subst_ql q1 m qempty) (subst_ql q2 m qempty)).
Proof.
  intros. rewrite plift_qual_eq.  
  rewrite plift_and. repeat rewrite plift_subst. 
  rewrite plift_and, plift_empty. eapply substp_empty_and.
Qed.

Lemma substp_hit: forall x q,
 subst_pl (pone x) x q = q.
Proof.
  intros. apply functional_extensionality.
  intros. eapply propositional_extensionality.
  unfold subst_pl. unfoldq; intuition.
Qed.

Lemma substq_hit: forall x q,
  subst_ql (qone x) x q = q.
Proof.
  intros. rewrite plift_qual_eq.
  rewrite plift_subst, plift_one. eapply substp_hit.
Qed.

Lemma subst_empty_and: forall q1 q2 m,
  psub (subst_pl (pand q1 q2) m pempty) (pand (subst_pl q1 m pempty) (subst_pl q2 m pempty)).
Proof.
  intros. unfold subst_pl. unfoldq; intuition.
Qed.

Lemma dsubst_sub: forall p q2 q1 p1 m,
  psub q2 p ->
  q1 = qempty -> 
  psub (subst_pl q2 m (plift q1)) 
       (subst_pl p m (plift p1)).
Proof.
  intros. subst q1.
  unfold subst_pl in *. unfoldq; intuition.
Qed.

Lemma Q2: forall{X}{Y} q2 (H2' H2 : list X) (G G':list Y) T,
  psub (plift q2)(pdom (G'++T::G)) ->
  length H2' = length G' ->
  length H2 = length G ->
  psub (subst_pl (plift q2)(length H2) pempty)(pdom (H2'++H2)).
Proof.
  intros. unfoldq; intuition.
  unfold subst_pl in H3.  rewrite app_length in *.
  destruct H3. destruct H3. unfoldq; intuition.
  eapply H in H6. simpl in *. lia.
  destruct H3. destruct H3. eapply H in H4. simpl in *. lia.
  destruct H3. destruct H3. eapply H in H4. simpl in *. lia.
  eapply H in H4. simpl in *. lia.
Qed.

Lemma Q2': forall{X}{Y} q2 (H2' H2 : list X) (G G':list Y) T,
  closed_ql (length (G'++T::G)) q2 ->
  length H2' = length G' ->
  length H2 = length G ->
  psub (plift (subst_ql q2 (length H2) qempty))(pdom (H2'++H2)).
Proof.
  intros. rewrite plift_subst. rewrite plift_empty. eapply Q2; eauto.
Qed.

Lemma splice_subst_pdom{X}: forall (H H': list X) p p1 v1 vx1,
  psub (plift (splice_ql (subst_ql p (length H) p1) (length H) 1)) (pdom (H' ++ v1 :: H)) -> 
  psub (plift (splice_ql (subst_ql p (length H) p1) (length H) 1)) (pdom ((vx1 :: H') ++ v1 :: H)).
Proof.
  intros. unfoldq; intuition. rewrite app_length. simpl. 
  eapply H0 in H1. rewrite app_length in H1. simpl in H1.  auto. 
Qed.

Lemma splice_subst_pdom_sub{X}: forall (H H': list X) p p1 v1 p',
  psub (plift (splice_ql (subst_ql p (length H) p1) (length H) 1)) (pdom (H' ++ v1 :: H)) -> 
  psub (plift (subst_ql p' (length H) p1))  (plift (subst_ql p (length H) p1))  ->
  psub (plift (splice_ql (subst_ql p' (length H) p1) (length H) 1)) (pdom (H' ++ v1 :: H)).
Proof.
  intros. eapply splice_psub with (m := length H)(n :=1) in H1 .
  unfoldq; intuition.
  rewrite plift_splice in H2.
  eapply H1 in H2. rewrite <- plift_splice in H2. eapply H0 in H2. auto.
Qed.

Lemma substp_sub: forall p p' q1 m,
  psub (plift p')(plift p) ->
  psub (plift (subst_ql p' m q1))  (plift (subst_ql p m q1)).
Proof.
  intros. repeat rewrite plift_subst.
  unfold subst_pl. unfoldq; intuition.
Qed.

Lemma substp_sub': forall p p' q1 m,
  psub  p' p ->
  psub (subst_pl p' m q1) (subst_pl p m q1).
Proof.
  intros. 
  unfold subst_pl. unfoldq; intuition.
Qed.


Lemma substq_mem{X}: forall p x (G G':list X) p1,
  closed_ql (length G'+ S (length G)) p ->
  plift p x -> 
  x > length G ->
  plift  (subst_ql p (length G) p1)(x -1).
Proof.
  intros. rewrite plift_subst. unfold closed_ql in H.
  unfold subst_pl. unfoldq; intuition. 
  apply H in H0 as H0'.
  right. left. intuition. replace (x -1 +1) with x.  auto. lia.
Qed.

Lemma substq_mem'{X}: forall p x (G G':list X) p1,
  closed_ql (length G) p1 ->
  plift  (subst_ql p (length G) p1) x ->
  x > length G ->
  plift p (x+1).
Proof.
  intros. rewrite plift_subst in H0. unfold closed_ql in H.
  unfold subst_pl in H0.  destruct H0. destruct H0.
  destruct H2. destruct H2; intuition.
  specialize (H x); intuition.
  destruct H0. destruct H0. auto. intuition.
Qed.

Lemma substq_mem''{X}: forall p (G:list X) q1 x,
  plift  (subst_ql p (length G) q1) x ->
  exists y, plift p y.
Proof.
  intros. rewrite plift_subst in H. 
  unfold subst_pl in H. destruct H. exists (length G). intuition.
  destruct H.  exists (x+1); intuition.
  exists x; intuition.
Qed.

Lemma substp_mem''{X}: forall p (G:list X) q1 x,
  subst_pl p (length G) q1 x ->
  exists y, p y.
Proof.
  intros.  unfold subst_pl in H. destruct H. exists (length G). intuition.
  destruct H.  exists (x+1); intuition.
  exists x; intuition.
Qed.



Lemma substq_mem2{X}: forall p x (G:list X) p1,
  plift p x -> 
  x < length G ->
  plift  (subst_ql p (length G) p1) x.
Proof.
  intros. rewrite plift_subst. 
  unfold subst_pl. unfoldq; intuition. 
Qed.

Lemma substp_mem2{X}: forall (p:pl) x (G:list X) p1,
  p x -> 
  x < length G ->
  (subst_pl p (length G) p1) x.
Proof.
  intros. 
  unfold subst_pl. unfoldq; intuition. 
Qed.

Lemma substq_mem3{X}: forall p (G:list X) q1 x,
  plift p (length G) -> 
  (plift q1) x ->
  plift  (subst_ql p (length G) q1) x.
Proof.
  intros. rewrite plift_subst. 
  unfold subst_pl. left. intuition.
  unfoldq; intuition. 
Qed.

Lemma substp_mem3{X}: forall (p:pl) (G:list X) (q1:pl) x,
  p (length G) -> 
  q1 x ->
  (subst_pl p (length G) q1) x.
Proof.
  intros. unfold subst_pl. left. intuition.
  unfoldq; intuition. 
Qed.

Lemma pif_psub: forall b p x m,
  pif b p x ->
  (forall x, p x -> x < m) ->
  (forall x, pif b p x -> x < m).
Proof. 
  intros. destruct b; unfoldq; intuition.
Qed. 


(* term interpretation for semantic weakening *)

Definition exp_type1 S1 S2 M H1 H2 t1 t2 S1' S2' M' v1 v2 T1 T2 p1 p2 fr1 fr2 q1 q2 (e1 e2: pl)  :=
  tevaln S1 H1 t1 S1' v1 /\
  tevaln S2 H2 t2 S2' v2 /\
  st_chain M M'  /\
  st_filter M' (st_locs1 M') (st_locs2 M') /\
  store_type S1' S2' M' /\
  store_effect S1 S1' (locs_locs_stty (st1 M) (vars_locs H1 (pand p1 e1))) /\
  store_effect S2 S2' (locs_locs_stty (st2 M) (vars_locs H2 (pand p2 e2))) /\
  val_type M' H1 H2 v1 v2 T1 T2 /\
  val_qual (st1 M)(st1 M') H1 v1 fr1 (pand p1 q1) /\
  val_qual (st2 M)(st2 M') H2 v2 fr2 (pand p2 q2) 
.

(* semantic context interpretation for semantic weakening *)

Definition env_type1 M H1 H2 H2' HX G p :=
  length H1 = length G /\
  length (H2'++HX++H2) = length G + length HX /\
    psub (plift p) (pdom H1) /\
    psub (splice_pl (plift p) (length H2) (length HX))(pdom (H2'++HX++H2)) /\
    (forall x T fr (q: ql),
        indexr x G = Some (T, fr, q) ->
        exists v1 v2 : vl,
        closed_ql x q /\
        indexr x H1 = Some v1 /\
        indexr (if x <? length H2 then x else x + length HX) (H2' ++ HX ++ H2) = Some v2 /\
        ((plift p) x -> val_type M H1 (H2'++HX++H2) v1 v2 T (splice_ty T (length H2) (length HX))) /\
        (fr = false -> (plift p) x -> psub (plift q) (plift p) -> psub (locs_locs_stty (st1 M) (val_locs v1)) (locs_locs_stty (st1 M) (vars_locs H1 (plift q)))) /\
        (fr = false -> (plift p) x -> psub (plift q) (plift p) -> psub (locs_locs_stty (st2 M) (val_locs v2)) (locs_locs_stty (st2 M) (vars_locs (H2'++HX++H2) (plift (splice_ql q (length H2) (length HX)))))))
    /\
    (forall q q',
       psub q (plift p) ->
       psub q' (plift p) ->
       psub (pand (vars_trans G q) (vars_trans G q')) (plift p) ->
       psub (pand (locs_locs_stty (st1 M) (vars_locs H1 q)) (locs_locs_stty (st1 M) (vars_locs H1 q')))
         (locs_locs_stty (st1 M) (vars_locs H1 (pand (vars_trans G q) (vars_trans G q')))))
    /\    
    (forall q q',
      psub q (plift p) ->
      psub q' (plift p) ->
      psub (pand (vars_trans G q) (vars_trans G q')) (plift p) ->
      psub (pand (locs_locs_stty (st2 M) (vars_locs (H2'++HX++H2) (splice_pl q (length H2)(length HX)))) (locs_locs_stty (st2 M) (vars_locs (H2'++HX++H2) (splice_pl q' (length H2)(length HX)))))
        (locs_locs_stty (st2 M) (vars_locs  (H2'++HX++H2) (pand (splice_pl (vars_trans G q) (length H2)(length HX)) (splice_pl (vars_trans G q') (length H2)(length HX))))))
.

(* semantic types for semantic weakening *)

Definition sem_type1 G t1 t2 T T' p fr fr' q q' e e' :=
  forall M H1 H2 H2' HX,
    env_type1 M H1 H2 H2' HX G p ->
    st_filter M (st_locs1 M)(st_locs2 M) ->
    forall S1 S2,
    store_type S1 S2 M ->
    exists S1' S2' M' v1 v2,
    exp_type1 S1 S2 M H1 H2 t1 t2 S1' S2' M' v1 v2 T T' (plift p) (plift p) fr fr' q q' e e'
.

Lemma valt_splice: forall T1 T2 M H1 H2 H2' HX v1 v2
  (CLT1: closed_ty (length (H2'++H2)) T1)
  (CLT2: closed_ty (length (H2'++H2)) T2), 
  val_type M H1 (H2'++H2) v1 v2 T1 T2 <->
  val_type M H1 (H2'++HX++H2) v1 v2 T1 (splice_ty T2 (length H2) (length HX)).
Proof.
  intros T1. induction T1; intros; destruct T2; destruct v1; destruct v2; simpl in *; intuition.
  + eapply closedty_splice; eauto.
  + eapply pdom_slice; eauto. 
  + destruct H10  as [vt [qt1 [qt2 [IM1 [IM2 [STVALT [HVT [P1 [P2 [P3 P4]]]]]]]]]].
    exists vt, qt1, qt2. intuition.
    - eapply HVT in H11; eauto. eapply H11 in H14.
      eapply IHT1 in H14; eauto. inversion CLT1. subst. auto. 
    - eapply HVT; eauto. eapply IHT1 in H14; eauto. inversion CLT1. subst. auto. 
    - rewrite plift_splice. rewrite vars_locs_splice. auto.
  + inversion CLT2. subst. auto.
  + inversion CLT2. subst. auto. 
  + destruct H10  as [vt [qt1 [qt2 [IM1 [IM2 [STVALT [HVT [P1 [P2 [P3 P4]]]]]]]]]].
    exists vt, qt1, qt2. intuition.
    - eapply HVT in H11; eauto. eapply H11 in H14.
      eapply IHT1 in H14; eauto. inversion CLT1. subst. auto. inversion CLT2. subst. auto. 
    - eapply HVT; eauto. eapply IHT1 in H14; eauto. inversion CLT1. subst. auto. inversion CLT2. subst. auto. 
    - rewrite plift_splice in P2. rewrite vars_locs_splice in P2. auto.
  + eapply closedty_splice; eauto.
  + eapply pdom_slice; eauto.
  + eapply closedty_splice; eauto.
  + eapply pdom_slice; eauto.
  + eapply pdom_slice; eauto.
  + eapply H13 in H12; eauto. 
    2: { eapply IHT1_1; eauto. inversion CLT1. subst. auto. }
    2: { rewrite plift_splice in H18. rewrite vars_locs_splice in H18. auto. }
    destruct H12 as [S1'' [S2'' [M'' [vy1 [vy2 ?]]]]].
    exists S1'', S2'', M'', vy1, vy2. intuition.
    rewrite plift_splice. rewrite vars_locs_splice. auto.
    eapply IHT1_2 in H25; eauto. inversion CLT1; auto.
    rewrite plift_splice. rewrite vars_locs_splice. auto.
  + inversion CLT2. subst. auto.
  + inversion CLT2. subst. auto.
  + inversion CLT2. subst. auto.
  + inversion CLT2. subst. auto.
  + inversion CLT2. subst. auto.
  + eapply H13 in H12; eauto.
    2: { eapply IHT1_1 in H16; eauto. inversion CLT1. subst. auto. inversion CLT2. subst. auto. }
    2: { rewrite plift_splice. rewrite vars_locs_splice. auto. }
    destruct H12 as [S1'' [S2'' [M'' [vy1 [vy2 ?]]]]].
    exists S1'', S2'', M'', vy1, vy2. intuition.
    rewrite plift_splice in H24. rewrite vars_locs_splice in H24. auto.
    eapply IHT1_2; eauto. inversion CLT1; auto. inversion CLT2; auto.
    rewrite plift_splice in H28. rewrite vars_locs_splice in H28. auto.
Qed.

Lemma wf_envt1: forall M H1 H2 H2' HX G p, 
  env_type1 M H1 H2 H2' HX G p -> 
  (length H1 = length G /\
   length (H2'++H2) = length G /\
   pdom H1 = pdom G /\
   pdom (H2'++H2) = pdom G /\  
   psub (plift p) (pdom H1) /\
   psub (splice_pl (plift p) (length H2)(length HX)) (pdom (H2'++HX++H2))
   ).
Proof.
    intros. unfold env_type1 in H. 
    unfoldq; intuition. repeat rewrite app_length in *. intuition. 
    unfoldq; intuition. rewrite H0. auto.
    unfoldq; intuition. 
    assert ((length (H2'++H2) = length G)). unfoldq; intuition.
    repeat rewrite app_length in *. intuition.
    rewrite H7. auto.
Qed.

(* convert from semantic context interpretation to semantic context interpretation for semantic weakening *)

Lemma envt_convert: forall M H1 H2 H2' HX G p, 
  env_type M H1 (H2' ++ H2) G (plift p) ->
  env_type1 M H1 H2 H2' HX G p.
Proof.
  intros. destruct H as [L1 [L2 [PD1 [PD2 [P1 [P2 P3]]]]]].
  repeat rewrite app_length in *. intuition.
  unfold env_type1; intuition.
  repeat rewrite app_length. intuition. 
  eapply psub_splice in PD2. rewrite plift_splice in PD2. eauto.

  destruct (P1 x T fr q H) as [v1 [v2 [? [IX1 [IX2 [VT [? ?]]]]]]].

  bdestruct (x <? length H2); intuition.
  - rewrite indexr_skips. 2: { rewrite app_length. lia. } rewrite indexr_skips; auto.
    exists v1, v2; intuition. 
    + rewrite indexr_skips in IX2. auto. auto.
    + rewrite valt_splice in H7. eapply H7. 1,2: eapply valt_closed in H7; intuition.
    + intros ? ?. eapply H10 in H9. eapply lls_mono; eauto. rewrite plift_splice. rewrite vars_locs_splice. intros ? ?. auto.
  - (* x >= length H2 *)
    exists v1, v2; intuition.
    + eapply indexr_splice' in IX2. eapply IX2. auto.
    + rewrite valt_splice in H7. eapply H7. 1,2: eapply valt_closed in H7; intuition.
    + intros ? ?. eapply H10 in H9. eapply lls_mono; eauto. rewrite plift_splice. rewrite vars_locs_splice. intros ? ?. auto.
  - eapply P3 in H3; eauto.
    rewrite vars_locs_splice. rewrite vars_locs_splice. 
    intros ? ?. eapply H3 in H4.  eapply lls_mono; eauto. intros ? ?.  
    erewrite <- vars_locs_splice with (HX := HX) in H5. eapply vars_locs_mono; eauto.
    intros ? ?. rewrite splice_pand in H6. destruct H6. split; auto.
Qed.    

(* convert from semantic context interpretation for semantic weakening to semantic context interpretation *)

Lemma envt_convert': forall M H1 H2 H2' HX G p,
  env_type1 M H1 H2 H2' HX G p ->
  env_type M H1 (H2' ++ H2) G (plift p).
Proof.
  intros. 
  apply wf_envt1 in H as WFE'. 
  destruct WFE' as [L1' [L2' [P1' [P2' [P3' P4']]]]].
  destruct H as [L1 [L2 [P1 [P2 [W1 [W2 W3]]]]]]; intuition.
  assert (length (H2'++H2 ) = length G) as L.
  repeat rewrite app_length in *. lia.
  unfold env_type; repeat rewrite app_length in *; intuition.  
  - rewrite P2'. rewrite <- P1'. auto.
  
  - destruct (W1 x T fr q H) as [v1 [v2 [? [IX1 [IX2 VT]]]]]; intuition.
    bdestruct (x <? length H2); intuition.
    + rewrite indexr_skips in IX2. 2: rewrite app_length; lia. rewrite indexr_skips in IX2; auto.
      rewrite indexr_skips; auto. exists v1, v2; intuition.
      * rewrite valt_splice; eauto. 1,2: apply valt_closed in H8; intuition;
        rewrite L1' in H3; rewrite app_length; rewrite L; auto.  
      * rewrite plift_splice in H3. rewrite vars_locs_splice in H3; eauto.
    + exists v1, v2; intuition.
      * assert (indexr (if x <? length H2 then x else x + length HX) (H2' ++ HX ++ H2) =
              indexr x (H2' ++ H2)). { eapply indexr_splice. }
        bdestruct (x <? length H2); intuition. rewrite <- H7. auto. 
      *  rewrite valt_splice. eapply H8.
        1,2: apply valt_closed in H8; intuition;
        rewrite L1 in H3; rewrite app_length; rewrite L; auto.  
      * rewrite plift_splice in H3. rewrite vars_locs_splice in H3; eauto.
  - eapply W3 in H3; eauto. rewrite vars_locs_splice in H3. rewrite vars_locs_splice in H3.
    rewrite <- splice_pand in H3.  rewrite vars_locs_splice in H3. auto.
Qed.

Lemma envt1_store_wf1: forall M H1 H2 H2' HX G p q,
    env_type1 M H1 H2 H2' HX G p ->
    psub q (plift p) -> 
    psub (vars_locs H1 q) (pnat (length1 M)). 
Proof.
  unfoldq; intuition;
  intros; destruct H as [L1 [L2 [P1 [P2 [W1 [W2 W3]]]]]]; intuition;
  unfoldq; intuition.

  destruct H3 as [? [? ?]].
  assert (plift p x0). eapply H0. eauto.
  rewrite <- splicep_aux with (i := length H2)(n:= length HX)in H4.
  assert ((splice_nat x0 (length H2)(length HX)) < length (H2'++HX++H2)). eapply P2. auto. 

  assert (exists T, indexr x0 G = Some T) as TY. 
  eapply indexr_var_some. rewrite <-L1. eauto.
  destruct TY as [T ?]. destruct T as [[T fr] q'].
  destruct H3 as [? [? ?]].
  destruct (W1 x0 T fr q') as [vx1 [vx2 [? [IX1 [IX2 [? [? ?]]]]]]]. auto. 
  rewrite H3 in IX1. inversion IX1. subst x1.

  eapply valt_wf in H9.  intuition. 
  eapply H12; eauto. intuition.
Qed.


Lemma envt1_store_wf2: forall M H1 H2 H2' HX G p q,
    env_type1 M H1 H2 H2' HX G p ->
    psub q (plift p) -> 
    psub (vars_locs (H2'++HX++H2) (splice_pl q (length H2) (length HX))) (pnat (length2 M)). 
Proof.
  intros.
  assert ((vars_locs (H2'++HX++H2)(splice_pl q (length H2) (length HX))) =
          (vars_locs (H2'++H2) q)).
  eapply vars_locs_splice. rewrite H3.
  
  unfoldq; intuition;
  intros; destruct H as [L1 [L2 [P1 [P2 [W1 [W2 W3]]]]]]; intuition;
  unfoldq; intuition.
  
  destruct H4 as [? [? ?]].
  assert (plift p x0). eapply H0. auto.
  
  rewrite <- splicep_aux with (i := length H2)(n:= length HX)in H5.
  assert ((splice_nat x0 (length H2)(length HX)) < length (H2'++HX++H2)). eapply P2. auto.
  
  assert (exists T, indexr x0 G = Some T) as TY. 
  eapply indexr_var_some. rewrite <-L1. eauto.
  destruct TY as [T ?]. destruct T as [[T fr] q'].
  destruct H4 as [? [? ?]].
  destruct (W1 x0 T fr q') as [vx1 [vx2 [? [IX1 [IX2 [? [? ?]]]]]]]. auto.
  rewrite <- indexr_splice with (HX := HX) in H4.
  unfold splice_nat in H4.
  
  bdestruct (x0 <? length H2); intuition.
  rewrite H4 in IX2. inversion IX2. subst x1.
  eapply valt_wf in H10.  intuition. eapply H15; eauto. intuition.
  rewrite H4 in IX2. inversion IX2. subst x1.
  eapply valt_wf in H10. intuition. eapply H15. auto. intuition. 
Qed.

Lemma envt1_store_deep_wf1: forall M H1 H2 H2' HX G p q,
    env_type1 M H1 H2 H2' HX G p ->
    psub q (plift p) -> 
    psub (locs_locs_stty (st1 M) (vars_locs H1 q)) (pnat (length1 M)). 
Proof.
  intros. eapply envt1_store_wf1 with (q := q) in H as H'; auto.
  eapply lls_mono with (M := (st1 M)) in H'.
  intros ? ?. eapply lls_vars in H3.
  destruct H3 as [? [? ?]]. eapply lls_var in H4. destruct H4 as [v [IH R]].
  destruct H as [L1 [L2 [P1 [P2 [W1 [W2 W3]]]]]]; intuition.
  assert (x0 < length G). { apply indexr_var_some' in IH. lia. }
  apply indexr_var_some in H. destruct H as [[[T fr] q'] ?].
  destruct (W1 x0 T fr q') as [vx1 [vx2 [CLQ [IX1 [IX2 [VT [? ?]]]]]]]; eauto.
  rewrite IH in IX1. inversion IX1. subst v. 
  assert ((plift p) x0). { eapply H0 in H3. auto. }
  eapply VT in H6. eapply valt_deep_wf in H6. destruct H6. eapply H6 in R. unfold st_locs1 in R. auto.
Qed.

Lemma envt1_store_deep_wf2: forall M H1 H2 H2' HX G p q,
    env_type1 M H1 H2 H2' HX G p ->
    psub q (plift p) -> 
    psub (locs_locs_stty (st2 M) (vars_locs (H2'++HX++H2) (splice_pl q (length H2) (length HX)))) (pnat (length2 M)). 
Proof.
  intros.
  assert ((vars_locs (H2'++HX++H2)(splice_pl q (length H2) (length HX))) =
          (vars_locs (H2'++H2) q)).
  eapply vars_locs_splice. rewrite H3.
  unfoldq; intuition;
  intros; destruct H as [L1 [L2 [P1 [P2 [W1 [W2 W3]]]]]]; intuition;
  unfoldq; intuition.

  eapply lls_vars in H4. destruct H4 as [? [? ?]]. eapply lls_var in H4. 
  destruct H4 as [vx [IX ?]].
  assert (plift p x0) as P. eapply H0. auto.

  assert (exists T, indexr x0 G = Some T) as TY. 
  eapply indexr_var_some. rewrite <-L1. eauto.
  destruct TY as [T ?]. destruct T as [[T fr] q'].
  destruct (W1 x0 T fr q') as [vx1 [vx2 [? [IX1 [IX2 [? [? ?]]]]]]]. auto.
  erewrite <- indexr_splice with (HX := HX) in IX. unfold splice_nat in IX. 
  rewrite IX in IX2. inversion IX2. subst vx. eapply H7 in P. eapply valt_deep_wf in P.
  destruct P. eapply H11 in H4. unfold st_locs2, pnat in H4. auto.
Qed.


Lemma envt1_filter_deep: forall S1 S2 M H1 H2 H2' HX G p q,
    env_type1 M H1 H2 H2' HX G p ->
    store_type S1 S2 M ->
    psub q (plift p) ->
    st_filter M (locs_locs_stty (st1 M) (vars_locs H1 q)) (locs_locs_stty (st2 M) (vars_locs (H2'++HX++H2) (splice_pl q (length H2)(length HX)))).
Proof. 
  intros. eapply envt1_store_deep_wf1 with (q := q) in H as W4; auto.
  eapply envt1_store_deep_wf2 with (q := q) in H as W5; auto.
  remember H as WFE. clear HeqWFE.
  destruct H as [L1 [L2 [P1 [P2 [W1 [W2 W3]]]]]].
  remember H0 as ST'. clear HeqST'.
  destruct H0 as [SST1 [SST2 [ST [R L]]]].
  repeat split; auto. 
  + intros. eapply lls_vars in H0. destruct H0 as [? [? ?]].
    eapply lls_var in H4. destruct H4 as [? [? ?]].
    eapply H3 in H0 as H0'.
    assert (x < length G).  eapply P1 in H0'. unfold pdom in H0'. rewrite <- L1. lia.
    eapply indexr_var_some in H6. destruct H6 as [[[T frt] qt] ?].
    destruct (W1 x T frt qt) as [v1 [v2 [? [IX1 [IX2 [VT [? ?]]]]]]]; auto.
    rewrite IX1 in H4. inversion H4. subst x0. 
    eapply valt_same_locs_deep in H5; eauto.
    eapply lls_var' in H5; eauto. unfold splice_pl.
    apply indexr_var_some' in H6.
    eapply lls_vars'; eauto. 
    bdestruct (x <? length H2); intuition. right. split. lia. 
    replace (x + length HX - length HX) with x. auto. lia.
  + intros. eapply lls_vars in H0. destruct H0 as [? [? ?]].
    eapply lls_var in H4. destruct H4 as [? [? ?]].
    destruct H0 as [[? ?] | [? ?]].
    - assert (x < length G). { repeat rewrite app_length in *. lia.  }
      eapply indexr_var_some in H7. destruct H7 as [[[T frt] qt] ?].
      destruct (W1 x T frt qt) as [v1 [v2 [? [IX1 [IX2 [VT [? ?]]]]]]]; auto.
      bdestruct (x <? length H2); intuition.
      rewrite IX2 in H4. inversion H4. subst x0. 
      eapply valt_same_locs_deep in H5; eauto.
      eapply lls_var' in H5; eauto.
      eapply lls_vars'; eauto.

    - eapply H3 in H6 as H6'. eapply P1 in H6' as P1'. unfold pdom in P1'. rewrite L1 in P1'.
      remember (x - length HX) as y.
      eapply indexr_var_some in P1'. destruct P1' as [[[T frt] qt] ?].
      destruct (W1 y T frt qt) as [v1 [v2 [? [IX1 [IX2 [VT [? ?]]]]]]]; auto.
      bdestruct (y <? length H2); intuition.
      subst y. replace (x - length HX + length HX) with x in IX2. 2: lia.
      rewrite IX2 in H4. inversion H4. subst x0. 
      eapply valt_same_locs_deep in H5; eauto.
      eapply lls_var' in H5; eauto.
      eapply lls_vars'; eauto.
Qed.
  
Lemma envt1_same_locs: forall S1 S2 M H1 H2 H2' HX G p p1 l1 l2,
    store_type S1 S2 M ->
    env_type1 M H1 H2 H2' HX G p ->
    strel M l1 l2 ->
    psub (plift p1) (plift p) ->
    locs_locs_stty (st1 M) (vars_locs H1 (plift p1)) l1 <-> (locs_locs_stty (st2 M) (vars_locs (H2'++HX++H2) (splice_pl (plift p1) (length H2)(length HX)))) l2.
Proof. 
  intros.
  remember (locs_locs_stty (st1 M) (vars_locs H1 (plift p1))) as A.
  remember (locs_locs_stty (st2 M) (vars_locs (H2'++HX++H2) (splice_pl (plift p1) (length H2)(length HX)))) as B.
  assert (st_filter M A B). {
    subst A B. eapply envt1_filter_deep; eauto.
  }
  subst A B. eapply H5. auto.
Qed.

Lemma envt1_store_change: forall M M' S1 S2 H1 H2 H2' HX G p
    (WFE: env_type1 M H1 H2 H2' HX G p)
    (ST: store_type S1 S2 M)
    (SCP: st_chain_partial M M' (locs_locs_stty (st1 M) (vars_locs H1 (plift p)))(locs_locs_stty (st2 M) (vars_locs (H2'++HX++H2) (splice_pl (plift p) (length H2)(length HX))))),
    env_type1 M' H1 H2 H2' HX G p.
Proof. 
  intros. remember WFE as WFE'. clear HeqWFE'.
  destruct WFE as [L1 [L2 [P1 [P2 [W1 [W2 W3]]]]]]. 
  repeat split; auto. intros.
  - destruct (W1 _ _  _  _ H) as [vx1 [vx2 [? [IH1 [IH2 [HVX ?]]]]]]; intuition.
    exists vx1, vx2; intuition.
    eapply valt_deep_wf in H6 as H6'. destruct H6'. 
    + eapply valt_store_change in H6; eauto. eapply stchain_tighten; eauto. eapply valt_filter; eauto.
      intros ? Q. eapply lls_vars'; eauto. eapply lls_var'; eauto.
      intros ? Q. eapply lls_vars'; eauto. eapply lls_var'; eauto. 
      unfold splice_pl. bdestruct (x <? length H2); intuition. right. replace (x + length HX - length HX) with x; auto.
      split; auto. lia. lia.
    + intros ? ?. erewrite <- lls_change with (M := (st1 M)) in H8. eapply H4 in H8. erewrite <- lls_change; eauto.
      eapply stchain_tighten; eauto. eapply envt1_filter_deep; eauto. eapply lls_mono; eauto. eapply vars_locs_mono; eauto.
      eapply lls_mono; eauto. eapply vars_locs_mono; eauto. eapply splice_psub in H7. eauto.
      eapply stchain_tighten. eapply valt_filter; eauto. eauto. 
      intros ? ?. eapply H4 in H10. eapply lls_mono; eauto. eapply vars_locs_mono; eauto.
      intros ? ?. eapply H9 in H10. eapply lls_mono; eauto. eapply vars_locs_mono; eauto. rewrite plift_splice. eapply splice_psub in H7; eauto. 
    + intros ? ?. erewrite <- lls_change with (M := (st2 M)) in H8. eapply H9 in H8. erewrite <- lls_change; eauto.
      eapply stchain_tighten; eauto. rewrite plift_splice. eapply envt1_filter_deep; eauto. eapply lls_mono; eauto. eapply vars_locs_mono; eauto.
      eapply lls_mono; eauto. eapply vars_locs_mono; eauto. rewrite plift_splice. eapply splice_psub in H7. eauto.
      eapply stchain_tighten. eapply valt_filter; eauto. eauto. 
      intros ? ?. eapply H4 in H10. eapply lls_mono; eauto. eapply vars_locs_mono; eauto.
      intros ? ?. eapply H9 in H10. eapply lls_mono; eauto. eapply vars_locs_mono; eauto. rewrite plift_splice. eapply splice_psub in H7; eauto. 
  - intros. eapply W2 in H3 as H3'; auto.
    intros ? ?. 
    erewrite <- lls_change with (M := (st1 M))(M' := (st1 M')) in H4.
    erewrite <- lls_change with (M := (st1 M))(M' := (st1 M')) in H4.
    eapply H3' in H4. 
    erewrite <- lls_change; eauto.
    eapply stchain_tighten. eapply envt1_filter_deep; eauto. eauto.
    eapply lls_mono. eapply vars_locs_mono; eauto.
    eapply lls_mono. eapply vars_locs_mono; eauto. eapply splice_psub in H3; eauto.
    eapply stchain_tighten. eapply envt1_filter_deep; eauto. eauto.
    eapply lls_mono. eapply vars_locs_mono; eauto.
    eapply lls_mono. eapply vars_locs_mono; eauto. eapply splice_psub in H0; eauto.
    eapply stchain_tighten. eapply envt1_filter_deep; eauto. eauto.
    eapply lls_mono. eapply vars_locs_mono; eauto.
    eapply lls_mono. eapply vars_locs_mono; eauto. eapply splice_psub in H; eauto.
  - intros. eapply W3 in H3 as H3'; auto.
    intros ? ?. 
    erewrite <- lls_change with (M := (st2 M))(M' := (st2 M')) in H4.
    erewrite <- lls_change with (M := (st2 M))(M' := (st2 M')) in H4.
    eapply H3' in H4. 
    erewrite <- lls_change; eauto. 
    eapply stchain_tighten. rewrite <- splice_pand. eapply envt1_filter_deep; eauto. eauto.
    eapply lls_mono. eapply vars_locs_mono; eauto.
    eapply lls_mono. eapply vars_locs_mono; eauto. eapply splice_psub in H3. rewrite splice_pand in H3. eauto.
    eapply stchain_tighten. eapply envt1_filter_deep; eauto. eauto.
    eapply lls_mono. eapply vars_locs_mono; eauto.
    eapply lls_mono. eapply vars_locs_mono; eauto. eapply splice_psub in H0; eauto.
    eapply stchain_tighten. eapply envt1_filter_deep; eauto. eauto.
    eapply lls_mono. eapply vars_locs_mono; eauto.
    eapply lls_mono. eapply vars_locs_mono; eauto. eapply splice_psub in H; eauto.
Qed.  

Lemma envt1_store_extend: forall M M' S1 S2 H1 H2 H2' HX G p,
    env_type1 M H1 H2 H2' HX G p ->
    store_type S1 S2 M ->
    st_chain M M' ->
    env_type1 M' H1 H2 H2' HX G p.
Proof.
  intros.   
  remember H as WFE. clear HeqWFE. destruct H as [L1 [L2 [P1 [P2 [W1 [W2 W3]]]]]]. 
  repeat split; auto. intros. 
  destruct (W1 _ _ _  _ H) as [vx1 [vx2 [? [IH1 [IH2 [HVX ?]]]]]]; intuition. rewrite plift_splice in *.
  - exists vx1, vx2; intuition. eapply valt_store_extend in H8; eauto.
    rewrite <- lls_change with (M := st1 (M))(M' := (st1 M')). rewrite <- lls_change with (M := st1 (M))(M' := (st1 M')). auto.
    eapply stchain_tighten; eauto. eapply envt1_filter_deep; eauto. eapply envt1_store_deep_wf1; eauto. eapply envt1_store_deep_wf2; eauto.
    eapply stchain_tighten; eauto. eapply valt_filter; eauto. eapply valt_deep_wf; eauto. eapply valt_deep_wf; eauto.
    rewrite <- lls_change with (M := st2 (M))(M' := (st2 M')). rewrite <- lls_change with (M := st2 (M))(M' := (st2 M')). auto.
    eapply stchain_tighten; eauto. eapply envt1_filter_deep; eauto. eapply envt1_store_deep_wf1; eauto. eapply envt1_store_deep_wf2; eauto.
    eapply stchain_tighten; eauto. eapply valt_filter; eauto. eapply valt_deep_wf; eauto. eapply valt_deep_wf; eauto.
  - intros. eapply W2 in H5 as H5'; auto.
    intros ? ?. 
    erewrite <- lls_change with (M := (st1 M))(M' := (st1 M')) in H6.
    erewrite <- lls_change with (M := (st1 M))(M' := (st1 M')) in H6.
    eapply H5' in H6. 
    erewrite <- lls_change; eauto.
    eapply stchain_tighten. eapply envt1_filter_deep; eauto. eauto. eapply envt1_store_deep_wf1; eauto. eapply envt1_store_deep_wf2; eauto.
    eapply stchain_tighten. eapply envt1_filter_deep; eauto. eauto. eapply envt1_store_deep_wf1; eauto. eapply envt1_store_deep_wf2; eauto.
    eapply stchain_tighten. eapply envt1_filter_deep; eauto. eauto. eapply envt1_store_deep_wf1; eauto. eapply envt1_store_deep_wf2; eauto.
  - intros. eapply W3 in H5 as H5'; auto.
    intros ? ?. 
    erewrite <- lls_change with (M := (st2 M))(M' := (st2 M')) in H6.
    erewrite <- lls_change with (M := (st2 M))(M' := (st2 M')) in H6.
    eapply H5' in H6. 
    erewrite <- lls_change; eauto. 
    eapply stchain_tighten. rewrite <- splice_pand. eapply envt1_filter_deep; eauto. eauto. eapply envt1_store_deep_wf1; eauto. rewrite <- splice_pand in *.  eapply envt1_store_deep_wf2; eauto.
    eapply stchain_tighten. eapply envt1_filter_deep; eauto. eauto. eapply envt1_store_deep_wf1; eauto. rewrite <- splice_pand in *.  eapply envt1_store_deep_wf2; eauto.
    eapply stchain_tighten. eapply envt1_filter_deep; eauto. eauto. eapply envt1_store_deep_wf1; eauto. rewrite <- splice_pand in *.  eapply envt1_store_deep_wf2; eauto.
Qed.

Lemma envt1_valq_store_change1: forall M M' M'' S1 S2 G H1 H2 H2' HX v1 v2 T T' fr p q
    (WFE: env_type1 M' H1 H2 H2' HX G p)
    (ST: store_type S1 S2 M')
    (VT: val_type M' H1 (H2'++HX++H2) v1 v2 T T')
    (VQ: val_qual (st1 M) (st1 M') H1 v1 fr (pand (plift p) q)), 
    st_chain M' M'' ->
    val_qual (st1 M) (st1 M'') H1 v1 fr (pand (plift p) q).
Proof.
  intros. intros ? ?.
  assert (locs_locs_stty (st1 M') (val_locs v1) x). {
    erewrite lls_change. eauto.
    eapply stchain_tighten; eauto. eapply valt_filter; eauto.
    1,2: eapply valt_deep_wf in VT; intuition.
  }
  destruct (VQ x H3). {
    left. erewrite <-lls_change. eauto.
    eapply stchain_tighten; eauto. eapply envt1_filter_deep; eauto.
    intros ? ?. unfoldq; intuition.
    eapply envt1_store_deep_wf1; eauto; unfoldq; intuition.
    eapply envt1_store_deep_wf2; eauto; unfoldq; intuition. 
  } {
    right. destruct fr; try contradiction. 
    simpl in *. unfold pnot , pdom in *. intuition.
  }
Qed.

Lemma envt1_valq_store_change2: forall M M' M'' S1 S2 G H1 H2 H2' HX v1 v2 T T' fr p q
    (WFE: env_type1 M' H1 H2 H2' HX G p)
    (ST: store_type S1 S2 M')
    (VT: val_type M' H1 (H2'++HX++H2) v1 v2 T T')
    (VQ: val_qual (st2 M) (st2 M') (H2'++HX++H2) v2 fr (splice_pl (pand (plift p) q) (length H2)(length HX))), 
    st_chain M' M'' ->
    val_qual (st2 M) (st2 M'') (H2'++HX++H2) v2 fr (splice_pl (pand (plift p) q) (length H2)(length HX)).
Proof. 
  intros. intros ? ?.
  assert (locs_locs_stty (st2 M') (val_locs v2) x). {
    erewrite lls_change. eauto.
    eapply stchain_tighten; eauto. eapply valt_filter; eauto.
    1,2: eapply valt_deep_wf in VT; intuition.
  }
  destruct (VQ x H3). {
    left. erewrite <-lls_change. eauto.
    eapply stchain_tighten; eauto. eapply envt1_filter_deep; eauto. 
    unfoldq; intuition.
    eapply envt1_store_deep_wf1; eauto. unfoldq; intuition.
    eapply envt1_store_deep_wf2; eauto. unfoldq; intuition.
  } {
    right. destruct fr; try contradiction. 
    simpl in *. unfold pdiff , pnat in *. intuition.
  }
Qed.

Lemma envt1_telescope: forall M H1 H2 H2' HX G p,
  env_type1 M H1 H2 H2' HX G p -> telescope G.
Proof.
  intros. destruct H as (? & ? & ? & ? & ? & ? & ?).
  intros ? ? ? ? ?. edestruct H5 as (? & ? & ? & ? & ? & ?); eauto.
Qed.

Lemma envt1_extend_full: forall M M1 H1 H2 H2' HX G S1 S2 vx1 vx2 T1 p fr1 q1 qf
  (WFE: env_type1 M H1 H2 H2' HX G p)
  (SC: st_chain_partial M M1 (locs_locs_stty (st1 M) (vars_locs H1 (pand (plift p) (plift qf)))) (locs_locs_stty (st2 M) (vars_locs (H2'++HX++H2) (splice_pl (pand (plift p) (plift qf)) (length H2)(length HX)))))
  (ST: store_type S1 S2 M)
  (VT: val_type M1 H1 (H2' ++ HX ++H2) vx1 vx2 T1 (splice_ty T1 (length H2) (length HX)))
  (VQ1: psub (pand (locs_locs_stty (st1 M1) (vars_locs H1 (plift qf))) (locs_locs_stty (st1 M1) (val_locs vx1)))
    (locs_locs_stty (st1 M1) (vars_locs H1 (plift q1))))
  (VQ2: psub (pand (locs_locs_stty (st2 M1) (vars_locs (H2'++HX++H2) (splice_pl (plift qf) (length H2)(length HX)))) (locs_locs_stty (st2 M1) (val_locs vx2)))
    (locs_locs_stty (st2 M1) (vars_locs (H2'++HX++H2) (splice_pl (plift q1) (length H2)(length HX)))))  
  (A1: (fr1 = false -> psub (locs_locs_stty (st1 M1) (val_locs vx1)) (locs_locs_stty (st1 M1) (vars_locs H1 (plift q1)))))
  (A2: (fr1 = false -> psub (locs_locs_stty (st2 M1) (val_locs vx2)) (locs_locs_stty (st2 M1) (vars_locs (H2'++HX++H2) (splice_pl (plift q1) (length H2)(length HX))))))
  (SUB1: psub (plift qf) (plift p))
  (SUB2: psub (plift q1) (plift qf)) ,
  closed_ty (length G) T1 ->
  closed_ql (length G) q1 ->
  env_type1 M1 (vx1 :: H1) H2 (vx2 :: H2') HX ((T1, fr1, q1) :: G) (qor qf (qone (length G))).
Proof.  
  intros.  
  remember WFE as WFE1. clear HeqWFE1.
  destruct WFE as [L1 [L2 [PD1 [PD2 [W1 [W2 W3]]]]]].
  assert (psub (plift p) (pdom G)). { intros ? ?. unfold pdom. rewrite <- L1. eapply PD1. auto.  }
  repeat rewrite app_length in *. simpl in *.

  repeat split; eauto.
  - simpl. eauto.
  - simpl. repeat rewrite app_length. eauto.
  - rewrite plift_or, plift_one. unfoldq. simpl. intuition. 
  - eapply psub_splice'; eauto. rewrite plift_or, plift_one. intros ? [? | ?]. unfoldq. rewrite app_length. simpl.
    eapply SUB1 in H4. eapply H3 in H4. lia. unfoldq. rewrite app_length. simpl. lia.
  - intros.
  bdestruct (x =? length G).
  + subst. rewrite indexr_head in H4. inversion H4. subst.
    exists vx1, vx2. repeat split.
    auto.
    rewrite <-L1. rewrite indexr_head. auto. 
    rewrite <-L2. simpl. bdestruct (length G <? length H2); intuition. 
    repeat rewrite app_length. 
    bdestruct (length H2' + (length HX + length H2) =? length H2' + (length HX + length H2)); intuition.
    
    intros. eapply valt_extend1; auto. rewrite L1. auto. 
    eapply closedty_splice; eauto. eapply closedty_extend; eauto. rewrite app_length. lia.
    intros. intros ? ?. eapply A1 in H8. eapply lls_mono; eauto. intros ? ?. eapply vars_locs_extend1; eauto. auto.
    intros. intros ? ?. eapply A2 in H8. eapply lls_mono; eauto. intros ? ?. rewrite plift_splice. eapply vars_locs_extend1. eauto. auto.
  + rewrite indexr_skip in H4. 2: lia. 
    assert (x < length G). { apply indexr_var_some' in H4. auto. }
    destruct (W1 _ _ _ _ H4) as [v1' [v2' [CL2 [IH1 [IH2 [VALT [FR1 FR2]]]]]]]; intuition.
    exists v1', v2'. intuition.
    rewrite indexr_skip. auto. lia.
    bdestruct (x<? length H2); intuition. replace ((vx2::H2') ++ HX ++H2) with (vx2::H2'++HX ++H2). rewrite indexr_skip. auto.
    repeat rewrite app_length. lia. simpl. auto.
    replace ((vx2::H2') ++ HX ++H2) with (vx2::H2'++HX ++H2). rewrite indexr_skip. auto. repeat rewrite app_length. lia. simpl. auto.
    assert ((plift p) x). { rewrite plift_or, plift_one in H7. unfoldq; intuition.  }
    eapply valt_extend1; eauto. 1,2: eapply valt_closed in VALT; intuition. eapply VALT in H8. 
    (* XXX store extend/tighten XXX *) {
      eapply valt_store_change. eapply ST. auto.
      rewrite plift_or, plift_one in H7. 
      eapply stchain_tighten; eauto. eapply valt_filter; eauto. 
      intros ? ?. eapply lls_mono; eauto. exists x. intuition. unfoldq; intuition.  eexists. eauto.
      intros ? ?. eapply lls_mono; eauto. intros ? ?.
      bdestruct (x <? length H2); intuition.  eexists. split. 
      2: { eexists. eauto. } left. intuition. unfoldq; intuition.
      eexists. split. 2: { eexists. eauto. }
      right. replace (x + length HX - length HX) with x. unfoldq; intuition. lia.
    } {
      intros. intros ? ?.
      assert (psub (plift q) (plift qf)). {
        rewrite plift_or, plift_one in H8, H9.
        intros ? A. eapply CL2 in A as B. 
        eapply H9 in A. unfoldq; intuition.
      }
      assert ((plift p) x). {
        rewrite plift_or, plift_one in H8, H9.
        destruct H8. unfoldq; intuition. unfoldq; intuition.  
      }
      assert (psub (plift q) (plift p)). {
        rewrite plift_or, plift_one in H8, H9.
        destruct H8. unfoldq; intuition. unfoldq; intuition.
      }
      erewrite lls_change with (M' := (st1 M1)) in H10. eapply H10 in H12. rewrite <- vars_locs_extend with (H' := [vx1]) in H12. simpl in H12. 
      erewrite <- lls_change; eauto.
      rewrite lls_vars_shrink; auto. rewrite lls_vars_shrink in H12; auto. 
      eapply stchain_tighten; eauto. eapply envt1_filter_deep; eauto. 
      eapply lls_mono; eauto. intros ? ?. eapply vars_locs_mono; eauto. unfoldq; intuition.
      eapply lls_mono; eauto. eapply vars_locs_mono; eauto. eapply splice_psub; eauto. unfoldq; intuition.
      unfoldq; intuition.
      auto.
      unfoldq; intuition. unfoldq; intuition. auto. auto.
      eapply sstchain_tighten. eapply SC.
      intuition. intros ? ?. eapply H11 in H10. 
      eapply lls_mono; eauto. eapply vars_locs_mono; eauto. unfoldq; intuition.
    }{
      intros. intros ? ?. rewrite plift_splice. simpl.
      rewrite lls_vars_shrink; eauto.
      assert (psub (plift q) (plift qf)). {
        rewrite plift_or, plift_one in H8, H9.
        intros ? A. eapply CL2 in A as B.
        eapply H9 in A. unfoldq; intuition.
      }
      assert ((plift p) x). {
        rewrite plift_or, plift_one in H8, H9.
        destruct H8. unfoldq; intuition. unfoldq; intuition.  
      }
      assert (psub (plift q) (plift p)). {
        rewrite plift_or, plift_one in H8, H9.
        destruct H8. unfoldq; intuition. unfoldq; intuition.
      }
      intuition. erewrite <- lls_change with (M := (st2 M)) in H12. eapply H17 in H12.
      rewrite plift_splice in *. 
      erewrite <- lls_change; eauto.
      eapply sstchain_tighten. eapply SC. 
      eapply lls_mono; eauto. intros ? ?. eapply vars_locs_mono; eauto. eapply splice_psub; eauto. unfoldq; intuition.
      eapply sstchain_tighten. eapply SC. intros ? ?.
      eapply H17 in H10.
      eapply lls_mono; eauto. intros ? ?. eapply vars_locs_mono; eauto. rewrite plift_splice. eapply splice_psub; eauto.
      unfoldq; intuition.
      eapply pdom_slice'; eauto. intros ? ?. unfold pdom. rewrite app_length.
      eapply CL2 in H13. apply indexr_var_some' in H4. lia.
    }  

  - (* 2nd invariant *)

  clear W1. (* distraction*)
  eapply envt1_telescope in WFE1 as TL1.

  intros q q' QSUB QSUB' QSUBTR x (QQ & QQ').
  eapply lls_vars in QQ.
  eapply lls_vars in QQ'. 

  destruct QQ as (? & VTQ & VLQ).
  destruct QQ' as (? & VTQ' & VLQ').
  rewrite plift_or, plift_one in *.

  destruct (QSUB x0); intuition; destruct (QSUB' x1); intuition.

  + (* qf, qf *)

    assert (psub (pand (vars_trans G (pand (pdom H1) q)) (vars_trans G (pand (pdom H1) q'))) (plift qf)) as QSUBTR1. {
      intros ? [? ?]. destruct (QSUBTR x2) as [? | ?].
      split. (* extend *)
      eapply vt_extend. eapply vt_mono. 2: eapply H6. unfoldq. intuition.
      eapply vt_extend. eapply vt_mono. 2: eapply H7. unfoldq. intuition.
      eauto.
      eapply vt_closed in H6 as CL; eauto. unfoldq. intuition. unfoldq. intuition. (* contra *)
    }

    eassert _ as W4. {
      eapply (W2 (pand (pdom H1) q) (pand (pdom H1) q')) with (x:=x).

      intros ? ?. destruct (QSUB x2) as [? | ?]. unfoldq. intuition. 
      eauto. eauto. unfoldq. lia.

      intros ? ?. destruct (QSUB' x2) as [? | ?]. unfoldq. intuition. 
      eauto. eauto. unfoldq. lia. 

      intros ? ?.  eapply QSUBTR1 in H6. eapply SUB1. auto.

      split.

      erewrite lls_change. 
      eapply lls_vars'. eapply lls_mono. 2: eapply VLQ. intros ? ?. eapply var_locs_shrink. eauto. unfoldq. intuition. unfoldq. intuition.
      eapply stchain_tighten. eapply envt1_filter_deep; eauto. 
      intros ? ?. destruct H6. unfoldq. eapply QSUB in H7. unfoldq; intuition. 
      eapply SC; eauto. eapply lls_mono. eapply vars_locs_mono. unfoldq. intuition. destruct (QSUB x2); eauto. lia. 
      eapply QSUB in H8. unfoldq; intuition.

      eapply lls_mono; eauto. eapply vars_locs_mono; eauto. eapply splice_psub; eauto. unfoldq; intuition.
      eapply QSUB in H8. unfoldq; intuition. 
      eapply QSUB in H8. unfoldq; intuition. 

      erewrite lls_change. 
      eapply lls_vars'. eapply lls_mono. 2: eapply VLQ'. intros ? ?. eapply var_locs_shrink. eauto. unfoldq. intuition. unfoldq. intuition.

      eapply stchain_tighten. eapply envt1_filter_deep; eauto. 
      intros ? ?. destruct H6. unfoldq. eapply QSUB' in H7. unfoldq; intuition. 
      eapply SC; eauto. eapply lls_mono. eapply vars_locs_mono. unfoldq. intuition. destruct (QSUB' x2); eauto. lia. 
      eapply QSUB' in H8. unfoldq; intuition.

      eapply lls_mono; eauto. eapply vars_locs_mono; eauto. eapply splice_psub; eauto. unfoldq; intuition.
      eapply QSUB' in H8. unfoldq; intuition.
      eapply QSUB' in H8. unfoldq; intuition.

    }

    erewrite lls_change in W4.

    eapply lls_vars in W4. destruct W4 as (? & (? & ?) & ?). 

    eapply lls_vars'. eapply lls_mono. 2: eauto. intros ? ?. eapply var_locs_extend. eauto. split.
    eapply vt_extend. eapply vt_mono. 2: eapply H6. unfoldq. intuition.
    eapply vt_extend. eapply vt_mono. 2: eapply H7. unfoldq. intuition.

    eapply stchain_tighten. eapply envt1_filter_deep; eauto. 
    intros ? ?. eapply QSUBTR1 in H6. auto. eauto. 

    eapply lls_mono. eapply vars_locs_mono. 
    intros ? ?. eapply QSUBTR1 in H6. unfoldq; intuition. auto. 

    eapply lls_mono; eauto. eapply vars_locs_mono; eauto. eapply splice_psub; eauto. 
    intros ? ?. eapply QSUBTR1 in H6. unfoldq; intuition.  

  + (* qf, x *)
    unfold pone in H5. subst x1. 

    assert (psub (pand (vars_trans G (pand (pdom H1) q)) (vars_trans G (plift q1))) (plift qf)) as QSUBTR1. {
      intros ? [? ?]. destruct (QSUBTR x1) as [? | ?].
      split. {
        eapply vt_extend. eapply vt_mono. 2: eapply H5. unfoldq. intuition. (* extend q *)
      }{
        eapply vt_head. eauto. unfoldq; intuition.  eauto. eauto.  (* pick q1 *)
      }
      eauto.
      eapply vt_closed in H6; eauto. unfoldq. intuition.  (* contra *)
    }

    eassert _ as W4. {
      eapply (W2 (pand (pdom H1) q) (plift q1)) with (x:=x).

      intros ? ?. destruct (QSUB x1) as [? | ?]. unfoldq. intuition. 
      eauto. eauto. unfoldq. lia.

      unfoldq. intuition.

      intros ? ?. eapply QSUBTR1 in H5. eauto.

      split. 

      erewrite lls_change. 
      eapply lls_vars'. eapply lls_mono. 2: eapply VLQ. intros ? ?. eapply var_locs_shrink. eauto. unfoldq. intuition. unfoldq. intuition.
      eapply stchain_tighten. eapply envt1_filter_deep; eauto. unfoldq; intuition. eapply QSUB in H7. unfoldq; intuition.
      eauto. eapply lls_mono. eapply vars_locs_mono. unfoldq. intuition. destruct (QSUB x1); eauto. lia. eapply QSUB in H7. unfoldq; intuition.
      eapply lls_mono. eapply vars_locs_mono. eapply splice_psub; eauto.
      unfoldq. intuition. destruct (QSUB x1); eauto. lia. eapply QSUB in H7. unfoldq; intuition.

      erewrite lls_change.
      eapply VQ1. split.
      eapply lls_vars'. eapply lls_mono. 2: eapply VLQ. intros ? ?. eapply var_locs_shrink. eauto. unfoldq. intuition. auto. 

      eapply lls_var in VLQ'. destruct VLQ' as (? & IX & ?). rewrite <- L1 in IX.
      rewrite indexr_head in IX. inversion IX. eauto.
      eapply stchain_tighten. eapply envt1_filter_deep; eauto. unfoldq; intuition. eauto.
      eapply lls_mono. eapply vars_locs_mono. unfoldq. intuition.
      eapply lls_mono. eapply vars_locs_mono. eapply splice_psub; eauto. unfoldq. intuition.
    }


    erewrite lls_change in W4.

    eapply lls_vars in W4. destruct W4 as (? & (? & ?) & ?). 

    eapply lls_vars'. eapply lls_mono. 2: eauto. intros ? ?. eapply var_locs_extend. eauto. split.
    eapply vt_extend. eapply vt_mono. 2: eapply H5. unfoldq. intuition.
    eapply vt_head. eauto. eauto. eauto. eauto. 

    eapply stchain_tighten. eapply envt1_filter_deep; eauto.
    intros ? ?. eapply QSUBTR1 in H5. auto. eauto. 
    eapply lls_mono. eapply vars_locs_mono. intros ? ?. eapply QSUBTR1 in H5. unfoldq; intuition.
    eapply lls_mono. eapply vars_locs_mono. eapply splice_psub; eauto. intros ? ?. eapply QSUBTR1 in H5. unfoldq; intuition.


  + (* x, qf *)
    unfold pone in H4. subst x0. 

    assert (psub (pand (vars_trans G (plift q1)) (vars_trans G (pand (pdom H1) q'))) (plift qf)) as QSUBTR1. {
      intros ? [? ?]. destruct (QSUBTR x0) as [? | ?].
      split. {
        eapply vt_head. eauto. auto. auto. auto.  (* pick q1 *)
      }{
        eapply vt_extend. eapply vt_mono. 2: eapply H6. unfoldq. intuition. (* extend q' *)
      }
      eauto.
      eapply vt_closed in H6; eauto. unfoldq. intuition. unfoldq. intuition. (* contra *)
    }

    eassert _ as W4. {
      eapply (W2 (plift q1) (pand (pdom H1) q')) with (x:=x).

      unfoldq. intuition.

      intros ? ?. destruct (QSUB' x0) as [? | ?]. unfoldq. intuition. 
      eauto. eauto. unfoldq. lia.

      intros ? ?. eapply QSUBTR1 in H4. eauto.

      split. 
      erewrite lls_change.
      eapply VQ1. split.
      eapply lls_vars'. eapply lls_mono. 2: eapply VLQ'. intros ? ?. eapply var_locs_shrink. eauto. unfoldq. intuition. eauto. 

      eapply lls_var in VLQ. destruct VLQ as (? & IX & ?). rewrite <- L1 in IX.
      rewrite indexr_head in IX. inversion IX. eauto.
      eapply stchain_tighten. eapply envt1_filter_deep; eauto. unfoldq; intuition. eauto.
      eapply lls_mono. eapply vars_locs_mono. unfoldq. intuition.
      eapply lls_mono. eapply vars_locs_mono. eapply splice_psub; eauto. unfoldq. intuition.

      erewrite lls_change. 
      eapply lls_vars'. eapply lls_mono. 2: eapply VLQ'. intros ? ?. eapply var_locs_shrink. eauto. unfoldq. intuition. unfoldq. intuition.
      eapply stchain_tighten. eapply envt1_filter_deep; eauto. unfoldq; intuition. eapply QSUB' in H7. unfoldq; intuition.
      eauto.
      eapply lls_mono. eapply vars_locs_mono. unfoldq. intuition. eapply QSUB' in H7. unfoldq; intuition. eapply QSUB' in H7. unfoldq; intuition.
      eapply lls_mono. eapply vars_locs_mono. eapply splice_psub; eauto. unfoldq. intuition. eapply QSUB' in H7. unfoldq; intuition. eapply QSUB' in H7. unfoldq; intuition.
    }

    erewrite lls_change in W4.

    eapply lls_vars in W4. destruct W4 as (? & (? & ?) & ?). 

    eapply lls_vars'. eapply lls_mono. 2: eauto. intros ? ?. eapply var_locs_extend. eauto. split.
    eapply vt_head. eauto. auto. auto. auto. 
    eapply vt_extend. eapply vt_mono. 2: eapply H6. unfoldq. intuition.

    eapply stchain_tighten. eapply envt1_filter_deep; eauto. 
    intros ? ?. eapply QSUBTR1 in H4. auto. eauto. 
    eapply lls_mono. eapply vars_locs_mono. intros ? ?.  eapply QSUBTR1 in H4. unfoldq; intuition.
    eapply lls_mono. eapply vars_locs_mono. eapply splice_psub; eauto. intros ? ?.  eapply QSUBTR1 in H4. unfoldq; intuition.

  + (* x, x *)
    unfold pone in H4, H5.
    subst x0 x1.

    eapply lls_vars'. eauto. split.
    left. eauto. left. eauto.
  - (* 3rd invariant *)
   clear W1. (* distraction*)
  eapply envt1_telescope in WFE1 as TL1.

  intros q q' QSUB QSUB' QSUBTR x (QQ & QQ').

  eapply splice_psub with (m := (length H2)) (n := (length HX)) in QSUB as QSUB_splice.
  eapply splice_psub with (m := (length H2)) (n := (length HX)) in QSUB' as QSUB_splice'.

  eapply lls_vars in QQ.
  eapply lls_vars in QQ'. 

  destruct QQ as (? & VTQ & VLQ).
  destruct QQ' as (? & VTQ' & VLQ').

  rewrite plift_or, plift_one in *.
  rewrite splice_por in *.

  destruct (QSUB_splice x0); intuition; destruct (QSUB_splice' x1); intuition.

  + (* qf, qf *)

  assert (psub (pand (vars_trans G (pand (pdom H1) q)) (vars_trans G (pand (pdom H1) q'))) (plift qf)) as QSUBTR1. {
    intros ? [? ?]. destruct (QSUBTR x2) as [? | ?].
    split. (* extend *)
    eapply vt_extend. eapply vt_mono. 2: eapply H6. unfoldq. intuition.
    eapply vt_extend. eapply vt_mono. 2: eapply H7. unfoldq. intuition.
    eauto.
    eapply vt_closed in H6 as CL; eauto. unfoldq. intuition. unfoldq. intuition. (* contra *)
  }

  eassert _ as W4. {
    eapply (W3 (pand (pdom H1) q) (pand (pdom H1) q')) with (x:=x).

    intros ? ?. destruct (QSUB x2) as [? | ?]. unfoldq. intuition. 
    eauto. unfoldq; intuition. 

    intros ? ?. destruct (QSUB' x2) as [? | ?]. unfoldq. intuition. 
    eauto. unfoldq; intuition.

    intros ? ?.  eapply QSUBTR1 in H6. eapply SUB1. auto.

    split.

    erewrite lls_change. 
    eapply lls_vars'. eapply lls_mono. 2: eapply VLQ. intros ? ?. eapply var_locs_shrink. eauto. eapply pdom_slice' in H4. unfoldq. eauto. 
    unfoldq. intuition. eapply SUB1 in H7. eapply H3 in H7. rewrite app_length. lia.
    assert (splice_pl (pand (plift qf) q) (length H2) (length HX) x0). { rewrite splice_pand. unfoldq; intuition. }
    eapply splice_psub. 2: eapply H6. unfoldq; intuition.
    
    eapply stchain_tighten. eapply envt1_filter_deep; eauto. 
    intros ? ?. destruct H6. unfoldq. eapply QSUB in H7. unfoldq; intuition. 
    eapply SC; eauto. eapply lls_mono. eapply vars_locs_mono. unfoldq. intuition. destruct (QSUB x2); eauto. lia. 
    eapply QSUB in H8. unfoldq; intuition.

    eapply lls_mono; eauto. eapply vars_locs_mono; eauto. 
    eapply splice_psub; eauto.
    intros ? [? ?].
    eapply QSUB in H7. unfoldq; intuition. 

    erewrite lls_change. 
    eapply lls_vars'. eapply lls_mono. 2: eapply VLQ'. intros ? ?. eapply var_locs_shrink. eauto. 
    eapply pdom_slice' in H5. unfoldq. eauto. 
    unfoldq. intuition. eapply SUB1 in H7. eapply H3 in H7. rewrite app_length. lia.

    assert (splice_pl (pand (plift qf) q') (length H2) (length HX) x1). { rewrite splice_pand. unfoldq; intuition. }
    eapply splice_psub. 2: eapply H6. unfoldq; intuition.

    eapply stchain_tighten. eapply envt1_filter_deep; eauto. 
    intros ? ?. destruct H6. unfoldq. eapply QSUB' in H7. unfoldq; intuition. 
    eapply SC; eauto. eapply lls_mono. eapply vars_locs_mono. unfoldq. intuition. destruct (QSUB' x2); eauto. lia. 
    eapply QSUB' in H8. unfoldq; intuition.

    eapply lls_mono; eauto. eapply vars_locs_mono; eauto.
    eapply splice_psub; eauto.
    intros ? [? ?].
    eapply QSUB' in H7. unfoldq; intuition. 

  }

  erewrite lls_change in W4.

  eapply lls_vars in W4. destruct W4 as (? & (? & ?) & ?). 

  eapply lls_vars'. eapply lls_mono. 2: eauto. intros ? ?. eapply var_locs_extend. eauto. 
  split.
  eapply splice_psub. 2: eapply H6. intros ? ?. eapply vt_extend. eapply vt_mono. 2: eapply H9. unfoldq. intuition.
  eapply splice_psub. 2: eapply H7. intros ? ?. eapply vt_extend. eapply vt_mono. 2: eapply H9. unfoldq. intuition.

  eapply stchain_tighten. rewrite <- splice_pand. eapply envt1_filter_deep; eauto. 
  intros ? ?. eapply QSUBTR1 in H6. auto. eauto. 

  eapply lls_mono. eapply vars_locs_mono. 
  intros ? ?. eapply QSUBTR1 in H6. unfoldq; intuition. 

  eapply lls_mono; eauto. eapply vars_locs_mono; eauto. 
  intros ? ?.  rewrite <- splice_pand in H6. eapply splice_psub; eauto.
  intros ? ?. eapply QSUBTR1 in H7. unfoldq; intuition.  

  + (* qf, x *)
  remember H5 as A. clear HeqA.
  destruct H5 as [[? ?] | [? ?]]. 
  * unfold pone in H6. lia.
  * unfold pone in H6. assert (x1 = length G + length HX). { lia. }
    remember VTQ' as B. clear HeqB. destruct VTQ' as [[? ?] | [? ?]].
    ** lia.
    ** assert (q' (length G)). { subst x1. replace (length G + length HX - length HX) with (length G) in H9. auto. }
    assert (psub (pand (vars_trans G (pand (plift qf) q)) (vars_trans G (plift q1))) (plift qf)) as QSUBTR1. {
    intros ? [? ?]. destruct (QSUBTR x2) as [? | ?].
    split. {
      eapply vt_extend. eapply vt_mono. 2: eapply H11. unfoldq. intuition. (* extend q *)
    }{
      eapply vt_head. eauto. unfoldq; intuition.  eauto. eauto.  (* pick q1 *)
    }
    eauto.
    eapply vt_closed in H12; eauto. unfoldq. intuition.  (* contra *)
  }

  eassert _ as W4. {
    eapply (W3 (pand (plift qf) q) (plift q1)) with (x:=x).

    unfoldq; intuition.
    unfoldq; intuition.

    intros ? ?. eapply QSUBTR1 in H11. eauto.
    split.

    erewrite lls_change. 
    eapply lls_vars'. eapply lls_mono. 2: eapply VLQ. intros ? ?. eapply var_locs_shrink. eauto. 
    eapply pdom_slice' in H4. unfoldq. eauto. 
    unfoldq. intuition. eapply SUB1 in H12. eapply H3 in H12. rewrite app_length. lia.

    assert (splice_pl (pand (plift qf) q) (length H2) (length HX) x0). { rewrite splice_pand. unfoldq; intuition. }
    eapply splice_psub. 2: eapply H11. unfoldq; intuition.

    eapply stchain_tighten. eapply envt1_filter_deep; eauto. unfoldq; intuition. 
    eauto. eapply lls_mono. eapply vars_locs_mono. unfoldq. intuition. 
    eapply lls_mono. eapply vars_locs_mono. 
    eapply splice_psub; eauto. unfoldq; intuition.

    erewrite lls_change.
    eapply VQ2. split.
    eapply lls_vars'. eapply lls_mono. 2: eapply VLQ. intros ? ?. eapply var_locs_shrink. eauto. 
    eapply pdom_slice' in H4. unfoldq. eauto. 
    unfoldq. intuition. eapply SUB1 in H12. eapply H3 in H12. rewrite app_length. lia.

    assert (splice_pl (pand (plift qf) q) (length H2) (length HX) x0). { rewrite splice_pand. unfoldq; intuition. }
    eapply splice_psub. 2: eapply H11. unfoldq; intuition.
    
    eapply lls_var in VLQ'. destruct VLQ' as (? & IX & ?). 
    subst x1. replace (length G + length HX) with (length (H2'++HX++H2)) in IX. 2:{ repeat rewrite app_length. lia. }
    replace ((vx2::H2')++HX++H2) with (vx2::H2'++HX++H2) in IX. 2: { simpl. auto. }
    rewrite indexr_head in IX. inversion IX. eauto.

    eapply stchain_tighten. eapply envt1_filter_deep; eauto. unfoldq; intuition. eauto.
    eapply lls_mono. eapply vars_locs_mono. unfoldq. intuition.
    eapply lls_mono. eapply vars_locs_mono. eapply splice_psub; eauto. unfoldq. intuition.
  }

  erewrite lls_change in W4.

  eapply lls_vars in W4. destruct W4 as (? & (? & ?) & ?). 

  eapply lls_vars'. eapply lls_mono. 2: eauto. intros ? ?. eapply var_locs_extend. eauto. 
  split.
  eapply splice_psub. 2: eapply H11. intros ? ?. eapply vt_extend. eapply vt_mono. 2: eapply H14. unfoldq. intuition.
  eapply splice_psub. 2: eapply H12. intros ? ?. eapply vt_head. eauto. eauto. eauto. eauto. 

  eapply stchain_tighten. rewrite <- splice_pand. eapply envt1_filter_deep; eauto.
  intros ? ?. eapply QSUBTR1 in H11. auto. eauto. 
  eapply lls_mono. eapply vars_locs_mono. intros ? ?. eapply QSUBTR1 in H11. unfoldq; intuition.
  eapply lls_mono. eapply vars_locs_mono. rewrite <- splice_pand. eapply splice_psub. intros ? ?. eapply QSUBTR1 in H11. unfoldq; intuition.
  + (* x, qf *)
  remember H4 as A. clear HeqA.
  destruct H4 as [[? ?] | [? ?]]. 
  * unfold pone in H6. lia.
  * unfold pone in H6. assert (x0 = length G + length HX). { lia. }
    remember VTQ as B. clear HeqB. destruct VTQ as [[? ?] | [? ?]].
    ** lia.
    ** assert (q (length G)). { subst x0. replace (length G + length HX - length HX) with (length G) in H9. auto. }
    assert (psub (pand (vars_trans G (plift q1)) (vars_trans G (pand (plift qf) q')) ) (plift qf)) as QSUBTR1. {
    intros ? [? ?]. destruct (QSUBTR x2) as [? | ?].
    split. {
      eapply vt_head. eauto. unfoldq; intuition.  eauto. eauto.  (* pick q1 *)
    }{
      eapply vt_extend. eapply vt_mono. 2: eapply H12. unfoldq. intuition. (* extend q *)
    }
    eauto.
    eapply vt_closed in H12; eauto. unfoldq. intuition. unfoldq; intuition.  (* contra *)
  }

  eassert _ as W4. {
    eapply (W3 (plift q1) (pand (plift qf) q') ) with (x:=x).

    unfoldq; intuition.
    unfoldq; intuition.

    intros ? ?. eapply QSUBTR1 in H11. eauto.
    split.

    erewrite lls_change.
    eapply VQ2. split.
    eapply lls_vars'. eapply lls_mono. 2: eapply VLQ'. intros ? ?. eapply var_locs_shrink. eauto. 
    eapply pdom_slice' in H5. unfoldq. eauto. 
    unfoldq. intuition. eapply SUB1 in H12. eapply H3 in H12. rewrite app_length. lia.

    assert (splice_pl (pand (plift qf) q') (length H2) (length HX) x1). { rewrite splice_pand. unfoldq; intuition. }
    eapply splice_psub. 2: eapply H11. unfoldq; intuition.

    eapply lls_var in VLQ. destruct VLQ as (? & IX & ?). 
    subst x0. replace (length G + length HX) with (length (H2'++HX++H2)) in IX. 2:{ repeat rewrite app_length. lia. }
    replace ((vx2::H2')++HX++H2) with (vx2::H2'++HX++H2) in IX. 2: { simpl. auto. }
    rewrite indexr_head in IX. inversion IX. eauto.

    eapply stchain_tighten. eapply envt1_filter_deep; eauto. unfoldq; intuition. eauto.
    eapply lls_mono. eapply vars_locs_mono. unfoldq. intuition.
    eapply lls_mono. eapply vars_locs_mono. eapply splice_psub; eauto. unfoldq. intuition.

    erewrite lls_change. 
    eapply lls_vars'. eapply lls_mono. 2: eapply VLQ'. intros ? ?. eapply var_locs_shrink. eauto. 
    eapply pdom_slice' in H5. unfoldq. eauto. 
    unfoldq. intuition. eapply SUB1 in H12. eapply H3 in H12. rewrite app_length. lia.

    assert (splice_pl (pand (plift qf) q') (length H2) (length HX) x1). { rewrite splice_pand. unfoldq; intuition. }
    eapply splice_psub. 2: eapply H11. unfoldq; intuition.
    
    eapply stchain_tighten. eapply envt1_filter_deep; eauto. unfoldq; intuition. 
    eauto. eapply lls_mono. eapply vars_locs_mono. unfoldq. intuition. 
    eapply lls_mono. eapply vars_locs_mono. 
    eapply splice_psub; eauto. unfoldq; intuition.
  }

  erewrite lls_change in W4.

  eapply lls_vars in W4. destruct W4 as (? & (? & ?) & ?). 

  eapply lls_vars'. eapply lls_mono. 2: eauto. intros ? ?. eapply var_locs_extend. eauto. 
  split.
  eapply splice_psub. 2: eapply H11. intros ? ?. eapply vt_head. eauto. eauto. eauto. eauto. 
  eapply splice_psub. 2: eapply H12. intros ? ?. eapply vt_extend. eapply vt_mono. 2: eapply H14. unfoldq. intuition.
  
  eapply stchain_tighten. rewrite <- splice_pand. eapply envt1_filter_deep; eauto.
  intros ? ?. eapply QSUBTR1 in H11. auto. eauto. 
  eapply lls_mono. eapply vars_locs_mono. intros ? ?. eapply QSUBTR1 in H11. unfoldq; intuition.
  eapply lls_mono. eapply vars_locs_mono. rewrite <- splice_pand. eapply splice_psub. intros ? ?. eapply QSUBTR1 in H11. unfoldq; intuition.

  + (* x, x *)
  destruct H4 as [[? ?] | [? ?]]; destruct H5 as [[? ?] | [? ?]].
  * unfold pone in H6. lia.
  * unfold pone in H6. lia.
  * unfold pone in H7. lia.
  * remember VTQ as B. clear HeqB. remember VTQ' as C. clear HeqC.  
    destruct VTQ as [[? ?] |?]; destruct VTQ' as [[? ?] | ?].
    ** unfold pone in H6, H7. 
       assert (x0 = length HX + length G). { lia. }
       assert (x1 = length HX + length G). { lia. }
       subst x0 x1. 
       eapply lls_vars'. eauto. split.
       left. intuition.
       left. intuition.
    ** unfold pone in H6, H7. 
       assert (x0 = length HX + length G). { lia. }
       assert (x1 = length HX + length G). { lia. }
       subst x0 x1.
       eapply lls_vars'. eauto. split.
       left. intuition.
       left. intuition.
    ** unfold pone in H6, H7. 
       assert (x0 = length HX + length G). { lia. }
       assert (x1 = length HX + length G). { lia. }
       subst x0 x1.
       eapply lls_vars'. eauto. split.
       left. intuition.
       left. intuition.
    ** unfold pone in H6, H7. 
       assert (x0 = length HX + length G). { lia. }
       assert (x1 = length HX + length G). { lia. }
       subst x0 x1. 
       eapply lls_vars'. eauto. split.
       right. intuition. left. auto.
       right. intuition. left. auto.
Qed.

Lemma overlapping_splice: forall S1 S2 M S1' S2' M' M'' H1 H2 H2' HX G p vf1 vf2 vx1 vx2 frf qf frx qx q1 TF1 TF2
    (WFE: env_type1 M H1 H2 H2' HX G p)
    (ST : store_type S1 S2 M)
    (ST1 : store_type S1' S2' M')
    (STC1: st_chain M M')
    (STC2: st_chain M' M'')
    (VTF: val_type M' H1 (H2'++HX++H2) vf1 vf2 TF1 TF2) 
    (HQF1: val_qual (st1 M) (st1 M') H1 vf1 frf (pand (plift p) qf))
    (HQF2: val_qual (st2 M) (st2 M') (H2'++HX++H2) vf2 frf (pand (splice_pl (plift p)(length H2)(length HX))(splice_pl qf (length H2)(length HX))))
    (HQX1: val_qual (st1 M') (st1 M'') H1 vx1 frx (pand (plift p) qx))
    (HQX2: val_qual (st2 M') (st2 M'') (H2'++HX++H2) vx2 frx (pand (splice_pl (plift p)(length H2)(length HX))(splice_pl qx (length H2)(length HX))))
    (WFF1: psub (val_locs vf1) (st_locs1 M'))
    (WFF2: psub (val_locs vf2) (st_locs2 M'))
    (SUB: psub (plift q1) (plift p))
    (OVERLAP: psub (pand (vars_trans G (pand (plift p) qf)) (vars_trans G (pand (plift p) qx))) (plift q1))
    (A: psub (locs_locs_stty (st1 M') (val_locs vf1))  (st_locs1 M'))
    (B: psub (locs_locs_stty (st2 M') (val_locs vf2))  (st_locs2 M')), 
    psub (pand (locs_locs_stty (st1 M'') (val_locs vf1)) (locs_locs_stty (st1 M'') (val_locs vx1))) (locs_locs_stty (st1 M'') (vars_locs H1 (plift q1))) /\
    psub (pand (locs_locs_stty (st2 M'') (val_locs vf2)) (locs_locs_stty (st2 M'') (val_locs vx2))) (locs_locs_stty (st2 M'') (vars_locs (H2'++HX++H2) (splice_pl (plift q1)(length H2)(length HX)))).
Proof. 
  intros. 
  remember WFE as WFE1. clear HeqWFE1.
  eapply envt1_store_extend in WFE as WFE'; eauto.
  eapply envt1_store_extend in WFE' as WFE''; eauto.  
  destruct WFE'' as [L1 [L2 [P1 [P2 [W [O1 O2]]]]]].

  split.
  + (* 1st *)
    intros ? [LLSF LLSX]. destruct (HQF1 x) as [Hf_q | Hf_fr]; destruct (HQX1 x) as [Hx_q | Hx_fr]; auto.
    - erewrite <- lls_change with (M := (st1 M')) in LLSF; eauto.
      eapply stchain_tighten. eapply valt_filter; eauto. eapply STC2.  
      1,2: eapply valt_deep_wf; eauto.
    - erewrite lls_change; eauto. eapply stchain_tighten. eapply valt_filter; eauto. eapply STC2.
      1,2: eapply valt_deep_wf; eauto.
    - assert ((pand (locs_locs_stty (st1 M'') (vars_locs H1 (pand (plift p) qf)))
                   (locs_locs_stty (st1 M'') (vars_locs H1 (pand (plift p) qx)))) x).
        erewrite lls_change in Hf_q. 2: { 
        eapply stchain_tighten. eapply envt1_filter_deep; eauto.  unfoldq; intuition.
        eauto.
        eapply envt1_store_deep_wf1; eauto. unfoldq; intuition. 
        eapply envt1_store_deep_wf2; eauto. unfoldq; intuition. }

        split; eauto.
        eapply O1 with (q := (pand (plift p) qf)) (q' := (pand (plift p) qx)) in H.
        eapply lls_mono. eapply vars_locs_mono. 2: eauto.
        unfoldq. intuition.
        unfoldq. intuition.
        unfoldq. intuition.
        unfoldq. intuition. 
    - destruct frx. 2: contradiction. 
      eapply envt1_store_deep_wf1 in Hf_q.
        2: {  eauto. } 2: { unfoldq. intuition. }
        assert False. eapply Hx_fr. eauto. contradiction.
    - destruct frf. 2: contradiction. simpl in Hf_fr. unfold pnot in Hf_fr.
      rewrite <- lls_change with (M := (st1 M)) in Hx_q. eapply envt1_store_deep_wf1 in Hx_q; eauto. 
      destruct Hf_fr. unfold length1 in Hx_q. auto. unfoldq; intuition.
      eapply stchain_tighten. eapply envt1_filter_deep; eauto. unfoldq; intuition. 
      eapply st_trans; eauto. 
      eapply envt1_store_deep_wf1; eauto. unfoldq; intuition. 
      eapply envt1_store_deep_wf2; eauto. unfoldq; intuition. 
    - destruct frx. 2: contradiction. simpl in *.  
      assert False. eapply Hx_fr. eapply A. erewrite lls_change; eauto. eapply sstchain_tighten; eauto.
      eapply STC2. contradiction.  

  +  (* 2nd *)
    intros ? [LLSF LLSX]. destruct (HQF2 x) as [Hf_q | Hf_fr]; destruct (HQX2 x) as [Hx_q | Hx_fr]; auto.
    - erewrite <- lls_change with (M := (st2 M')) in LLSF; eauto.
      eapply stchain_tighten. eapply valt_filter; eauto. eapply STC2.  
      1,2: eapply valt_deep_wf; eauto.
    - erewrite lls_change; eauto. eapply stchain_tighten. eapply valt_filter; eauto. eapply STC2.
      1,2: eapply valt_deep_wf; eauto.
    - assert ((pand (locs_locs_stty (st2 M'') (vars_locs (H2'++HX++H2) (pand (splice_pl (plift p)(length H2)(length HX))(splice_pl qf (length H2)(length HX)))))
                   (locs_locs_stty (st2 M'') (vars_locs (H2'++HX++H2) (pand (splice_pl (plift p)(length H2)(length HX))(splice_pl qx (length H2)(length HX)))))) x).
        erewrite lls_change in Hf_q. 2: { 
        eapply stchain_tighten. rewrite <- splice_pand. eapply envt1_filter_deep; eauto.  unfoldq; intuition.
        eauto.
        eapply envt1_store_deep_wf1; eauto. unfoldq; intuition. 
        rewrite <- splice_pand. eapply envt1_store_deep_wf2; eauto. unfoldq; intuition. }

        split; eauto.
        repeat rewrite <- splice_pand in H.
        eapply O2 with (q := (pand (plift p) qf)) (q' := (pand (plift p) qx)) in H.
        eapply splice_psub with (m := length H2)(n := length HX) in SUB as B'.
        eapply lls_mono. eapply vars_locs_mono. 2: eauto.
        rewrite <- splice_pand. eapply splice_psub. unfoldq; intuition.
        unfoldq. intuition.
        unfoldq. intuition.
        unfoldq. intuition. 
    - destruct frx. 2: contradiction.
      rewrite <- splice_pand in Hf_q. 
      eapply envt1_store_deep_wf2 in Hf_q.
        2: {  eauto. } 2: { unfoldq. intuition. }
        assert False. eapply Hx_fr. eauto. contradiction.
    - destruct frf. 2: contradiction. simpl in Hf_fr. unfold pnot in Hf_fr.
      rewrite <- lls_change with (M := (st2 M)) in Hx_q. rewrite <- splice_pand in Hx_q. eapply envt1_store_deep_wf2 in Hx_q; eauto. 
      destruct Hf_fr. unfold length2 in Hx_q. auto. unfoldq; intuition.
      rewrite <- splice_pand. eapply stchain_tighten. eapply envt1_filter_deep; eauto. unfoldq; intuition. 
      eapply st_trans; eauto. 
      eapply envt1_store_deep_wf1; eauto. unfoldq; intuition. 
      eapply envt1_store_deep_wf2; eauto. unfoldq; intuition. 
    - destruct frx. 2: contradiction. simpl in *.  
      assert False. eapply Hx_fr. eapply B. erewrite lls_change; eauto. eapply sstchain_tighten; eauto.
      eapply STC2. contradiction.  
Qed.

Lemma envt1_tighten: forall M H1 H2 H2' HX G p p',
    env_type1 M H1 H2 H2' HX G p ->
    psub (plift p') (plift p) ->
    env_type1 M H1 H2 H2' HX G p'.
Proof.
  intros. apply wf_envt1 in H as H'.
  destruct H' as [L1' [L2' [PD1 [PD2 [PD3 PD4]]]]].
  destruct H as [L1 [L2 [P1 [P2 [W [W1 W2]]]]]].
  repeat split; auto.
  - unfoldq. intuition.
  - eapply psub_splice'; eauto. rewrite PD2. rewrite <- PD1. unfoldq; intuition.
  - intros.
    destruct (W x T fr q) as [v1 [v2 [? [? [? [? [? ?]]]]]]]; eauto.
    exists v1, v2; intuition.
    eapply H12. intuition. unfoldq; intuition.
    eapply H7. intuition. unfoldq; intuition.
  - intros. eapply W1; eauto. all: unfoldq; intuition.
  - intros. eapply W2; eauto. all: unfoldq; intuition.
Qed.


(*******************************************************************************
 compatability lemmas for semantic weakening
*******************************************************************************)

Lemma bi_true_splice: forall S1 S2 M H1 H2 p1 p2 q1 q2,
  st_filter M (st_locs1 M) (st_locs2 M) ->
  store_type S1 S2 M ->  
  exp_type1 S1 S2 M H1 H2 ttrue ttrue S1 S2 M (vbool true) (vbool true) TBool TBool p1 p2 false false q1 q2 pempty pempty.
Proof.
  intros. 
  split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 8: split. 9: split.  
  exists 1. intros. destruct n. lia. simpl. eauto.
  exists 1. intros. destruct n. lia. simpl. eauto.
  eapply st_refl; auto. 
  eauto.
  auto.
  intros ? ?. intuition.
  intros ? ?. intuition.
  simpl. eauto. 
  eapply valq_bool.
  eapply valq_bool.
Qed.

Lemma bi_false_splice: forall S1 S2 M H1 H2 p1 p2 q1 q2,
  st_filter M (st_locs1 M) (st_locs2 M) ->
  store_type S1 S2 M ->  
  exp_type1 S1 S2 M H1 H2 tfalse tfalse S1 S2 M (vbool false) (vbool false) TBool TBool p1 p2 false false q1 q2 pempty pempty.
Proof.  
  intros. 
  split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 8: split. 9: split.  
  exists 1. intros. destruct n. lia. simpl. eauto.
  exists 1. intros. destruct n. lia. simpl. eauto.
  eapply st_refl; auto. 
  eauto.
  auto.
  intros ? ?. intuition.
  intros ? ?. intuition.
  simpl. eauto. 
  eapply valq_bool.
  eapply valq_bool.
Qed.


Lemma bi_var_splice: forall G M H1 H2 H2' S1 S2 HX p x T1 fr1 q1
  (WFE: env_type M H1 (H2'++H2) G p)
  (ST: store_type S1 S2 M)
  (SF: st_filter M (st_locs1 M) (st_locs2 M)),
  indexr x G = Some (T1, fr1, q1) ->
  p x ->
  store_type S1 S2 M ->
  exists S1' S2' M' v1 v2,
    exp_type1 S1 S2 M
      H1 (H2'++HX++H2)
      (tvar x) (splice_tm (tvar x) (length H2) (length HX))
      S1' S2' M'
      v1 v2 
      T1 (splice_ty T1 (length H2) (length HX))
      p  (splice_pl p (length H2) (length HX))
      false false
      (plift (qone x)) (splice_pl (plift (qone x)) (length H2) (length HX))
      pempty pempty. 
Proof.
  intros. rewrite plift_one. 
  destruct WFE as [L1 [L2 [P1 [P2 [W [W1 W2]]]]]].
  eapply W in H; auto. 
  destruct H as [v1 [v2 [HCL [IX1 [IX2 [VT ?]]]]]].
  exists S1, S2, M, v1, v2. 
  split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 8: split. 9: split.  
  + (* teval 1 *)
    exists 1. intros. destruct n. lia. simpl. rewrite IX1. eauto.
  + (* teval 2 *)
    exists 1. intros. destruct n. lia. simpl.
    assert ((1, S2, Some (indexr (splice_nat x (length H2) (length HX))(H2' ++ HX ++ H2))) = (1, S2, Some (Some v2))) as R. {
      rewrite indexr_splice. rewrite IX2. eauto.  } 
    eapply R. 
  + eapply st_refl. auto.
  + eauto.
  + auto.
  + intros ? ? ? ?. auto.
  + intros ? ? ? ?. auto. 
  + (* valt *)
    eapply valt_splice in VT; eauto. 1,2: eapply valt_closed in VT; intuition.
  + (* first qual *)
    unfoldq. unfoldq. intuition.  inversion H6; subst. 
    left. left. exists x; intuition. exists v1. intuition.
    left. eapply lls_s; eauto. exists x; intuition. exists v1. intuition.
  
  + (* 2nd qual *)
    unfoldq. unfoldq. intuition. inversion H6; subst. 
    left. left. exists (splice_nat x (length H2) (length HX)).
    repeat rewrite plift_splice. repeat rewrite splicep_aux. rewrite indexr_splice. 
    intuition.  exists v2. eauto.
    left. eapply lls_s; eauto. exists (splice_nat x (length H2) (length HX)).
    repeat rewrite plift_splice. repeat rewrite splicep_aux. rewrite indexr_splice. 
    intuition. exists v2. eauto.
Qed.


Lemma storet_extend_splice: forall M H1 H2 H2' HX G p S1 S2 S1' S2' M' q vt v1 v2 qt1 qt2 T
    (WFE: env_type1 M H1 H2 H2' HX G p)
    (ST: store_type S1 S2 M)
    (ST1: store_type S1' S2' M')
    (QP: psub (plift q) (plift p))
    (SC1: st_chain M M')
    (QT1: qt1 = vars_locs_fix H1 q)
    (QT2: qt2 = (vars_locs_fix (H2'++HX++H2) (splice_ql q (length H2)(length HX))))
    (SC2: st_chain M' (st_extend M' vt qt1 qt2))
    (HVX: val_type M' H1 (H2'++HX++H2) v1 v2 T (splice_ty T (length H2) (length HX)))
    (HQX1: val_qual (st1 M) (st1 M') H1 v1 false (pand (plift p) (plift q)))
    (HQX2: val_qual (st2 M) (st2 M') (H2'++HX++H2) v2 false (pand (splice_pl (plift p) (length H2) (length HX))
                                                                  (splice_pl (plift q) (length H2) (length HX))))
    (VT: vt v1 v2),
    store_type (v1::S1')(v2::S2')(st_extend M' vt qt1 qt2).
Proof. 
  intros. 
  assert (env_type1 M H1 H2 H2' HX G (qand p q)) as WFET. eapply envt1_tighten; eauto. rewrite plift_and. intros ? ?. unfoldq; intuition.
  eapply envt1_store_deep_wf1 with (q := (pand (plift p) (plift q))) in WFET as WFET1. 2: { rewrite plift_and. intros ? ?; unfoldq; intuition. } 
  eapply envt1_store_deep_wf2 with (q := (pand (plift p) (plift q))) in WFET as WFET2. 2: { rewrite plift_and. intros ? ?; unfoldq; intuition. } 
  
  eapply envt1_store_wf1 with (q := (plift q)) in WFE as WFE1; auto.
  eapply envt1_store_wf2 with (q := (plift q)) in WFE as WFE2; auto.
  assert (st_filter M' (locs_locs_stty (st1 M') (val_locs v1)) (locs_locs_stty (st2 M') (val_locs v2))) as SFV. {
    eapply valt_filter; eauto.
  }
  remember ST as ST'. clear HeqST'. remember ST1 as ST1'. clear HeqST1'.
  destruct ST as [SST1 [SST2 ST]]. destruct ST1 as [? [? ?]].
  remember H as SST1'. remember H0 as SST2'. clear HeqSST1'. clear HeqSST2'.
  remember SC2 as SC2'. clear HeqSC2'. 
  destruct SC2' as [SC2A SC2B].
  assert (length (st1 M) <= length (st1 M')) as L1. eapply st_mono1 in SC1. unfold length1 in *. auto.
  assert (length (st2 M) <= length (st2 M')) as L2. eapply st_mono2 in SC1. unfold length2 in *. auto.
  assert (sstore_type (v1 :: S1') (st1 (st_extend M' vt qt1 qt2))) as SSTA. {
    unfold sstore_type in H, H0, SST1, SST2.  unfold sstore_type. intuition. 
    + unfold length1. simpl. eauto.
    + bdestruct (l <? length S1').
      unfold st_extend. simpl.
      destruct (H11 l) as [qt [v [? [? [? ?]]]]]. auto.
      exists qt, v; intuition.
       bdestruct (l =? length (st1 M')); intuition.
       bdestruct (l =? length S1'); intuition.
       unfold st1. simpl. 
       intros ? ?. auto.
       eapply lls_shrink' in H26; eauto. 
       eapply H24 in H26. eapply lls_extend. auto.
       eapply val_locs_wf; eauto. 

       unfold st_extend. simpl. rewrite <- H10. simpl in H19.
       bdestruct (l =? length S1'); intuition.
       exists qt1, v1; intuition.
       simpl. intros ? ?.
       eapply lls_shrink' in H23. 2: eauto. 2: eapply valt_wf; eauto.
       destruct (HQX1 x) as [H_q | H_fr]. eauto.
        (* q *) subst qt1. rewrite <-plift_vars_locs. erewrite <-lls_change1 with (q2 := (plift qt2)).  eapply lls_mono. 2: eauto. intros ? ?. eapply vars_locs_mono; eauto. unfoldq. intuition. 
        subst qt2. eapply stchain_tighten with (p1 := st_locs1 M') (p2 := st_locs2 M'); eauto.
        assert (env_type1 M' H1 H2 H2' HX G p) as WFE'. eapply envt1_store_extend; eauto.
        rewrite <- plift_vars_locs.
        eapply envt1_filter_deep in WFE'; eauto. rewrite plift_splice. auto.
        eapply envt1_store_deep_wf1. eapply envt1_store_extend. eauto. eauto. eauto. rewrite plift_and. unfoldq; intuition.
        rewrite <-plift_vars_locs. rewrite plift_splice. eapply envt1_store_deep_wf2. eapply envt1_store_extend. eauto. eauto. eauto. rewrite plift_and. unfoldq; intuition.
        (* fr *) destruct H_fr.
        subst qt1. intros ? ?. erewrite <- plift_vars_locs in H23.
        unfoldq. eapply WFE1 in H23. subst l. eapply st_mono1 in SC1. unfold length1 in *. simpl in H19. lia.
    }
  assert (sstore_type (v2 :: S2') (st2 (st_extend M' vt qt1 qt2))) as SSTB. {
    unfold sstore_type in H, H0, SST1, SST2.  unfold sstore_type. intuition.
    + simpl. lia. 
    + bdestruct (l <? length S2').
      unfold st_extend. simpl.
      destruct (H12 l) as [qt [v [? [? [? ?]]]]]. auto.
      exists qt, v; intuition.
       bdestruct (l =? length (st2 M')); intuition.
       bdestruct (l =? length S2'); intuition.
       unfold st2. simpl. 
       intros ? ?.
       eapply lls_shrink' in H26; eauto.
       eapply H24 in H26. eapply lls_extend. auto.
       eapply val_locs_wf; eauto. 

       unfold st_extend. simpl.
       rewrite <- H. simpl in H19.  bdestruct (l =? length S2'); intuition.
       exists qt2, v2; intuition.
       simpl. intros ? ?.
       eapply lls_shrink' in H23. 2: eauto. 2: eapply valt_wf; eauto.
       destruct (HQX2 x) as [H_q | H_fr]. eauto.
        (* q *) subst qt2. rewrite <-plift_vars_locs. erewrite <-lls_change2 with (q1 := (plift qt1)).  eapply lls_mono. 2: eauto. intros ? ?. rewrite plift_splice. eapply vars_locs_mono; eauto. unfoldq. intuition. 
        subst qt1. eapply stchain_tighten with (p1 := st_locs1 M') (p2 := st_locs2 M'); eauto.
        rewrite <- plift_vars_locs. rewrite plift_splice.
        eapply envt1_filter_deep. eapply envt1_store_extend; eauto. eauto. rewrite plift_and. unfoldq; intuition.
        rewrite <- plift_vars_locs. eapply envt1_store_deep_wf1; eauto. eapply envt1_store_extend; eauto.
        rewrite plift_splice. eapply envt1_store_deep_wf2; eauto. eapply envt1_store_extend; eauto.
        
        (* fr *) destruct H_fr.
        subst qt2. rewrite <- plift_vars_locs. rewrite plift_splice. intros ? ?. 
        unfoldq. eapply WFE2 in H23. subst l. eapply st_mono2 in SC1. unfold length2 in *. lia.
  }
  unfold store_type. intuition.
  - unfold st_extend in *. simpl in *.
    unfold strel in H13. simpl in H13. destruct H13.
    destruct H13 as [? ?].
    exists vt, qt1, qt2, v1, v2. repeat split.
    + subst l1. unfold length1. 
      bdestruct (length (st1 M') =? length (st1 M')); intuition.
    + subst l2. unfold length2. 
      bdestruct (length (st2 M') =? length (st2 M')); intuition.
    + subst l1. assert (length1 M' = length S1'). { unfold length1. destruct SST1'; intuition. }
      rewrite H13. bdestruct (length S1' =? length S1'); intuition.
    + subst l2. assert (length2 M' = length S2'). { unfold length2. destruct SST2'; intuition. }
      rewrite H15. bdestruct (length S2' =? length S2'); intuition.
    + eapply functional_extensionality. intros. eapply functional_extensionality. intros.
      eapply propositional_extensionality. split; intros.
      * destruct H16; intuition. destruct H16 as [? [? [? ?]]]. lia.
      * left. intuition.  
    + auto.
    + unfold st1. simpl. unfold st_locs1. eapply lls_closed'; eauto.
      intros ? ?. eapply valt_wf in HVX. destruct HVX as [A B].
      eapply A in H16. unfold pnat in *. unfold length1, st1 in H16. simpl. lia.
    + unfold st2. simpl. unfold st_locs2. eapply lls_closed'; eauto.
      intros ? ?. eapply valt_wf in HVX. destruct HVX as [A B].
      eapply B in H16. unfold pnat in *. unfold length2, st2 in H16. simpl. lia.
    + unfold strel in H16. simpl in H16.
      destruct H16.
      * destruct H16 as [A B]. rewrite <- H13 in A. inversion A. subst l0.
        rewrite <- H15 in B. inversion B. subst l3.
        unfold st1, st2. simpl. intros.
        eapply valt_deep_wf in HVX as HVX'. destruct HVX' as [A B].
        eapply lls_shrink in H18; eauto. eapply A in H18.
        unfold st_locs1, pnat in H18. lia.
        intros ? ?. eapply valt_wf; eauto.
      * unfold st1, st2. simpl. intros.
        eapply lls_shrink in H17; eauto. 
        destruct H3 as [C [D E]]. unfold strel in E. simpl in E.
        assert (st_locs1 M' l0). {
          eapply lls_closed' in H17; eauto. eapply valt_wf; eauto.
        }
        specialize (E l0 l3); intuition. clear H21.
        eapply SFV in H16; intuition. eapply lls_extend; eauto.
        eapply valt_wf; eauto.
    + unfold strel in H16. simpl in H16.
      destruct H16.
      * destruct H16 as [A B]. rewrite <- H13 in A. inversion A. subst l0.
        rewrite <- H15 in B. inversion B. subst l3.
        unfold st1, st2. simpl. intros.
        eapply valt_deep_wf in HVX as HVX'. destruct HVX' as [A B].
        eapply lls_shrink in H18; eauto. eapply B in H18.
        unfold st_locs2, pnat in H18. lia.
        intros ? ?. eapply valt_wf; eauto.
      * unfold st1, st2. simpl. intros.
        eapply lls_shrink in H17; eauto. 
        destruct H3 as [C [D E]]. unfold strel in E. simpl in E.
        assert (st_locs2 M' l3). {
          eapply lls_closed' in H17; eauto. eapply valt_wf; eauto.
        }
        specialize (E l0 l3); intuition. clear H19.
        eapply SFV in H16; intuition. eapply lls_extend; eauto.
        eapply valt_wf; eauto.
    + eapply H6 in H13 as H13'.  destruct H13' as [vt' [qt1' [qt2' [v1' [v2' ?]]]]]; intuition.
      exists vt', qt1', qt2', v1', v2'; intuition.
      * apply indexr_var_some' in H16 as H16'. bdestruct (l1 =? length (st1 M')); intuition.
      * apply indexr_var_some' in H15 as H15'. bdestruct (l2 =? length (st2 M')); intuition.
      * apply indexr_var_some' in H17 as H17'. bdestruct (l1 =? length S1'); intuition.
      * apply indexr_var_some' in H18 as H18'. bdestruct (l2 =? length S2'); intuition.
      * eapply functional_extensionality. intros. eapply functional_extensionality. intros.
        eapply propositional_extensionality. split; intros.
        ** destruct H21.
           *** destruct H21 as [? [? ?]]. apply indexr_var_some' in H16. unfold length1 in H21. lia.
           *** destruct H21 as [? [? [? [? ?]]]]. rewrite H19 in H24. subst x1. auto.
        ** right. exists vt'. intuition. apply indexr_var_some' in H16. unfold length1. lia.
           apply indexr_var_some' in H15. unfold length2. lia. 
      * (* st_filter *)
        destruct H22 as [STF1 [STF2 STF3]].
        repeat split.
        ** unfold st1, st_locs1, pnat, length1. simpl. intros ? ?.
           eapply lls_shrink in H21; eauto. eapply STF1 in H21. unfold st_locs1, pnat, length1, st1 in H21. lia.
           intros ? ?.  eapply lls_z with (M :=  (st1 M')) in H22; eauto. eapply STF1. auto.
        ** unfold st2, st_locs2, pnat, length2. simpl. intros ? ?.
           eapply lls_shrink in H21; eauto. eapply STF2 in H21. unfold st_locs2, pnat, length2, st2 in H21. lia.
           intros ? ?.  eapply lls_z with (M :=  (st2 M')) in H22; eauto. eapply STF2. auto.
        ** unfold strel in H21. simpl in H21. destruct H21 as [[? ?] | ?].
           *** unfold st1, st2. simpl. intros. subst l0 l3. eapply lls_shrink in H23; eauto.
               eapply STF1 in H23.  unfold st_locs1 in H23. unfoldq; intuition.
               intros ? ?.  eapply lls_z with (M := st1 M') in H21.  eapply STF1 in H21. unfold st_locs1 in H21. unfold pnat, length1, st1 in *. lia. 
           *** unfold st1, st2. simpl. intros ?. eapply lls_shrink in H22; eauto.
               specialize (STF3 l0 l3); intuition. eapply lls_extend; eauto.
               intros ? ?.  eapply lls_z with (M :=  (st1 M')) in H23; eauto. eapply STF1. auto.
        ** unfold strel in H21. simpl in H21. unfold st1, st2. simpl. intros. destruct H21 as [[? ?] | ?].
           *** subst l0 l3. eapply lls_shrink in H22; eauto. eapply STF2 in H22. unfold st_locs2 in H22. unfoldq; intuition.
               intros ? ?.  eapply lls_z with (M := st2 M') in H21.  eapply STF2 in H21. unfold st_locs2 in H21. unfold pnat, length2, st2 in *. lia.
           *** eapply lls_shrink in H22; eauto.
               specialize (STF3 l0 l3); intuition. eapply lls_extend; eauto.
               intros ? ?.  eapply lls_z with (M :=  (st2 M')) in H23; eauto. eapply STF2. auto.
  -  (* right unique *)
    unfold strel in H13, H15. simpl in H13, H15.
    destruct H13; destruct H15.
    + destruct H13 as [? ?]. destruct H15 as [? ?]. congruence.
    + destruct H13 as [? ?]. 
      edestruct H6 as [vt' [qt1' [qt2' [v1' [v2' [IM1 [IM2 [IS1 [IS2 [STVT [VT' STF']]]]]]]]]]]; eauto.
      subst l1. apply indexr_var_some' in IM1. unfold length1 in IM1. lia.
    + destruct H15 as [? ?].  
      edestruct H6 as [vt' [qt1' [qt2' [v1' [v2' [IM1 [IM2 [IS1 [IS2 [STVT [VT' STF']]]]]]]]]]]; eauto.
      subst l1. apply indexr_var_some' in IM1. unfold length1 in IM1. lia. 
    + eapply H5; eauto.
  - (* left unique *)
    unfold strel in H13, H15. simpl in H13, H15.
    destruct H13; destruct H15.
    + destruct H13 as [? ?]. destruct H15 as [? ?]. congruence.
    + destruct H13 as [? ?]. 
      edestruct H6 as [vt' [qt1' [qt2' [v1' [v2' [IM1 [IM2 [IS1 [IS2 [STVT [VT' STF']]]]]]]]]]]; eauto.
      apply indexr_var_some' in IM2. unfold length2 in H16. lia.
    + destruct H15 as [? ?].  
      edestruct H6 as [vt' [qt1' [qt2' [v1' [v2' [IM1 [IM2 [IS1 [IS2 [STVT [VT' STF']]]]]]]]]]]; eauto.
      apply indexr_var_some' in IM2. unfold length2 in H16. lia. 
    + eapply H11; eauto.
Qed.

Lemma bi_tref_splice: forall t M M' S1 S2 S1' S2' H1 H2 H2' (HX:list vl) G v1 v2 T p q e 
  (WFE: env_type M H1 (H2'++H2) G (plift p))
  (SUB: psub (plift q) (plift p)),
  store_type S1 S2 M ->
  exp_type1 S1 S2 M H1 (H2' ++ HX ++ H2) t (splice_tm t (length H2) (length HX)) S1' S2' M' v1 v2 
    T (splice_ty T (length H2) (length HX)) 
    (plift p) (splice_pl (plift p) (length H2) (length HX))
    false false 
    (plift q) (splice_pl (plift q) (length H2) (length HX)) 
    (plift e) (splice_pl (plift e) (length H2) (length HX)) ->
  exists S1'' S2'' M'' v3 v4,
  exp_type1 S1 S2 M H1 (H2' ++ HX ++ H2) (tref t) (tref (splice_tm t (length H2) (length HX))) S1'' S2'' M'' v3 v4 
    (TRef T false q) (TRef (splice_ty T (length H2) (length HX)) false (splice_ql q (length H2) (length HX))) 
    (plift p) (splice_pl (plift p) (length H2) (length HX)) 
    true true 
    (plift q) (splice_pl (plift q) (length H2) (length HX))
    (plift e) (splice_pl (plift e) (length H2) (length HX)).
Proof.
  intros. 
  destruct H0 as [IE1 [IE2 [STC [STF [ST [EFF1 [EFF2 [HV [HQ1 HQ2]]]]]]]]].
  remember ST as ST'. clear HeqST'.
  destruct ST as [[SL1 STT1] [[SL2 STT2] [SP [R L]]]].
  remember HV as  HV'. clear HeqHV'.
  remember (length S1) as x.
  remember (fun v1 v2  => val_type M' H1 (H2'++HX++H2) v1 v2 T (splice_ty T (length H2) (length HX))) as vt.

  remember (vars_locs_fix H1 q) as qt1.
  remember (vars_locs_fix (H2'++HX++H2) (splice_ql q (length H2)(length HX))) as qt2.

  assert (st_chain M' (st_extend M' vt qt1 qt2)). {
    assert (st_chain_partial M' (st_extend M' vt qt1 qt2)
                (st_locs1 M') (st_locs2 M')). {
      unfold st_chain_partial. split. auto. split. 
      {
        repeat split. 
        intros ? ?. unfold st_extend, st_locs1, pnat, length1 in *. simpl. lia.
        intros ? ?. unfold st_extend, st_locs2, pnat, length2 in *. simpl. lia.
        intros. simpl in H0. destruct H0. destruct H0 as [? ?].
        subst l1. unfold st_locs1, pnat in H3. lia. eapply STF; eauto.
        intros. simpl in H0. destruct H0. destruct H0 as [? ?].
        subst l2. unfold st_locs2, pnat in H3. lia. eapply STF; eauto.
      }
      repeat split.
      unfoldq; intuition.
      intros ? ?. unfold st_extend, pdom. simpl. unfold st_locs1, pnat, length1 in *. lia.
      intros ? ?. unfold st_extend. simpl. unfold st_locs1, pnat, length1 in *.
      bdestruct (l =? length (st1 M')); intuition.
      unfoldq; intuition.
      intros ? ?. unfold st_extend, pdom. simpl. unfold st_locs2, pnat, length2 in *. lia.
      intros ? ?. unfold st_extend. simpl. unfold st_locs2, pnat, length2 in *.
      bdestruct (l =? length (st2 M')); intuition.
      intros. simpl. 
      eapply functional_extensionality. intros. eapply functional_extensionality. intros.
      unfold st_locs1, pnat in H. unfold st_locs2, pnat in *. 
      eapply propositional_extensionality. split. intros. right. 

      exists (st_valtype M' l1 l2). intuition.
      intros.  destruct H5. 
      destruct H5 as [? [? ?]]. lia.
      destruct H5 as [? [? [? [? ?]]]]. subst x2. auto. 
      intros. unfold st_extend. unfold strel. simpl. right. auto.
      unfold st_extend, strel. simpl. intros. destruct H3 as [[? ?] | ?].
      destruct H0 as [? ?]. unfold st_locs1, pnat in *. lia.
      auto.
    }

    unfold st_chain. intuition.
  }
  
  exists (v1::S1'), (v2::S2'), (st_extend M' vt qt1 qt2).
  exists (vref (length S1')), (vref (length S2')).

  assert (store_type (v1 :: S1') (v2 :: S2') (st_extend M' vt qt1 qt2)) as RST. {
    subst vt. eapply storet_extend_splice; eauto. eapply envt_convert. eapply envt_store_extend; eauto.
    eapply st_refl. eauto.

  }

  split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 8: split. 9: split.

  + (* 1st term *)
    destruct IE1 as [n1 IE1].
    exists (S n1). intros. destruct n. lia. simpl. rewrite IE1.  auto. lia.

  + (* 2nd term *)
    destruct IE2 as [n2 IE2].
    exists (S n2). intros. destruct n. lia. simpl. rewrite IE2. auto. lia.
  
  + eapply st_trans. eauto. eapply stchain_extend. auto.

  + repeat split.
    - intros ? ?. auto.
    - intros ? ?. auto.
    - unfold st_locs1, st_locs2, pnat, length1, length2. simpl. unfold st_extend in H3. simpl in H3.
      intros. destruct H3. destruct H3 as [? ?]. subst l2. unfold length2. lia. 
      destruct (SP l1 l2) as [vt' [frt1 [frt2 [qt1' [qt2' [v1' [v2' [IM1 [IM2 ?]]]]]]]]]; auto.
      apply indexr_var_some' in IM2. lia.
    - simpl in H3. destruct H3. destruct H3. intros. unfold st_locs1, pnat, length1. simpl. unfold length1 in H3. lia.
      unfold st_locs1, st_locs2, pnat, length1, length2. simpl. intros.
      destruct (SP l1 l2) as [vt' [frt1 [frt2 [qt1' [qt2' [v1' [v2' [IM1 [IM2 ?]]]]]]]]]; auto.
      apply indexr_var_some' in IM1. lia.

  + (* store_typing *)
    eapply RST.

  + eapply se_trans. eauto. intros ? ?. intros. eapply indexr_extend1 in H4. eapply H4.
  
  + eapply se_trans. eauto. intros ? ?. intros. eapply indexr_extend1 in H4. eapply H4.
  
  + (* result type *)
    remember ((st_extend M' vt qt1 qt2)) as M2.
    assert (store_type (v1::S1')(v2::S2') (M2)) as ST2. {
      subst M2. eapply storet_extend_splice. 2: eapply H. all: eauto.
      eapply envt_convert; eauto.
      subst vt. auto. 
    }
    assert (psub (plift qt1) (st_locs1 M')) as KM1. {
      subst qt1. rewrite <-plift_vars_locs. eapply envt_store_wf; eauto.
      eapply envt_store_extend; eauto.
    }

  assert (psub (plift qt2) (st_locs2 M')) as KM2. {
    subst qt2. rewrite <-plift_vars_locs. rewrite plift_splice. eapply envt1_store_wf2; eauto. 
    eapply envt_convert.  eapply envt_store_extend; eauto. 
  }
    remember WFE as WFE'. clear HeqWFE'. destruct WFE as [? [? [? [? ?]]]].
    simpl. split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 8: split. 
    - eapply valt_closed in HV'; intuition.
    - eapply valt_closed in HV'; intuition.
    - unfoldq. intuition.
    - auto.
    - unfoldq; intuition.
    - rewrite plift_splice. intros ? ?. eapply pdom_slice; eauto. rewrite plift_splice. 
      eapply splice_psub in SUB; eauto.
    - subst M2. unfold st_extend, strel in *. simpl in *; intuition.
    - split. 2: split.
      -- rewrite val_locs_ref. intros ? ?. rewrite SL1 in H8. inversion H8; subst.
         unfold st1, st_extend, st_locs1, length1, pnat. simpl. unfold pone in H9. lia.
         unfold st1, st_extend, st_locs1, length1, pnat. simpl.
         eapply lls_indexr_closed''' in H11; eauto. destruct RST as [? [? ?]]; eauto.
      -- rewrite val_locs_ref. intros ? ?. rewrite SL2 in H8. inversion H8; subst.
         unfold st1, st_extend, st_locs2, length2, pnat. simpl. unfold pone in H9. lia.
         eapply lls_indexr_closed''' in H11; eauto. destruct RST as [? [? ?]]; eauto.
      -- intros. repeat rewrite val_locs_ref. subst M2. unfold st1, st2, st_extend in *. simpl in *.
         unfold strel in H8. simpl in H8. destruct H8 as [[? ?] | ?].
         --- split. intros. left. subst l2. unfoldq; intuition.
             intros. left. subst l1. unfoldq; intuition.
         --- destruct ST2 as [ST2A [ST2B ST2C]].
         split; intros. 
         * edestruct (SP l1 l2) as [vt' [frt1 [frt2 [qt1' [qt2' [v1'' [v2'' [IM1 [IM2 [IS1 [IS2 VT]]]]]]]]]]]; auto.
           inversion H9; subst. unfold pone in H10. apply indexr_var_some' in IM1. lia.
           eapply lls_shrink in H12 as H12'; eauto.       
           eapply lls_s in H12. 3: eauto. 2: eauto.
           eapply lls_s with (x1 := (length S2')); eauto.
           unfoldq; intuition. rewrite SL2. rewrite indexr_head. eauto.
           eapply lls_extend; eauto. unfold pone in H10. subst x1.
           rewrite SL1 in H11. rewrite indexr_head in H11. inversion H11.
           subst qt. rewrite <- plift_vars_locs in *. rewrite plift_splice.
           eapply envt1_same_locs; eauto.          
           eapply envt1_store_extend. eapply envt_convert; eauto. eauto. eauto. 
           unfold pone in H10. subst x1.
           rewrite SL1 in H11. unfold st1 in H11. rewrite indexr_head in H11.
           inversion H11. subst. rewrite <- plift_vars_locs.
           eapply envt_store_wf with (q := (plift q)). eapply envt_store_extend. eauto. eauto. auto. auto.
         * edestruct (SP l1 l2) as [vt' [frt1 [frt2 [qt1' [qt2' [v1'' [v2'' [IM1 [IM2 [IS1 [IS2 VT]]]]]]]]]]]; auto.
           inversion H9; subst. unfold pone in H10. apply indexr_var_some' in IM2. lia.
           eapply lls_shrink in H12 as H12'; eauto.       
           eapply lls_s in H12. 3: eauto. 2: eauto.
           eapply lls_s with (x1 := (length S1')); eauto.
           unfoldq; intuition. rewrite SL1. rewrite indexr_head. eauto.
           eapply lls_extend; eauto.
           unfold pone in H10. subst x1.
           rewrite SL2 in H11. rewrite indexr_head in H11. inversion H11.
           subst qt. rewrite  <- plift_vars_locs in *. rewrite plift_splice in *.
           eapply envt1_same_locs. eauto. 2: eauto. 2: eauto. 
           eapply envt1_store_extend. eapply envt_convert; eauto. eauto. eauto. eauto.
           unfold pone in H10. subst x1.
           rewrite SL2 in H11. unfold st2 in H11. rewrite indexr_head in H11.
           inversion H11. subst. rewrite <- plift_vars_locs in *. rewrite plift_splice. 
           eapply envt1_store_wf2; eauto. eapply envt1_store_extend. eapply envt_convert; eauto. eauto. eauto.
    - exists vt, qt1, qt2.
      split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split.
      -- subst M2. rewrite SL1. unfold st1 at 2, st_extend. simpl.
         bdestruct (length (st1 M') =? length (st1 M')); intuition.

      -- subst M2. rewrite SL2. unfold st2 at 2, st_extend. simpl.
         bdestruct (length (st2 M') =? length (st2 M')); intuition.

      -- subst vt. subst M2. unfold st_extend. 
         eapply functional_extensionality. intros. eapply functional_extensionality. intros. simpl.
         eapply propositional_extensionality. split. intros.
         intuition. destruct H10 as [? [? [? [? ?]]]]. unfold length1 in H8. lia.  intros. intuition.
      -- intros M3.  intros.
         remember H3 as STC'. clear HeqSTC'. 
         destruct H3 as [STC1' STC2'].
         
         remember (plift qt1) as qt1'. remember (plift qt2) as qt2'.

           assert (psub (locs_locs_stty (st1 M') qt1') (st_locs1 M')). {
             subst qt1' qt1. rewrite <-plift_vars_locs. eapply envt_store_deep_wf.
             eapply envt_store_extend. eauto. eauto. eauto. auto.
           }

           assert (psub (locs_locs_stty (st2 M') qt2') (st_locs2 M')). {
             subst qt2' qt2.  rewrite <-plift_vars_locs. rewrite plift_splice. 
             eapply envt1_store_deep_wf2; eauto. eapply envt1_store_extend.
             eapply envt_convert; eauto. eauto. eauto.
           }

           assert (st_chain_partial M' M2 (locs_locs_stty (st1 M') qt1') (locs_locs_stty (st2 M') qt2')). {
             eapply stchain_tighten; eauto. 
             split. 2: split.
             * auto.
             * auto.
             * intros. destruct H8 as [SFA [SFB SFC]].
               destruct SFA as [? [? X]].
               assert (strel M2 l1 l2). {
                 subst M2. simpl. right. auto.
               }
               eapply X in H16. split.
               intros. subst M2. unfold st1, st2, st_extend in H16. simpl in H16.
               eapply lls_extend with (a := qt1) in H17. intuition.
               eapply lls_shrink in H16; eauto. destruct ST2 as [? [? ?]]; eauto.
               intros. subst M2. unfold st1, st2, st_extend in H16. simpl in H16.
               eapply lls_extend with (a := qt2) in H17. intuition.
               eapply lls_shrink in H16; eauto. destruct ST2 as [? [? ?]]; eauto.
           }

           assert (locs_locs_stty (st1 M3) qt1' = locs_locs_stty (st1 M2) qt1') as L321. {
             erewrite <- lls_change1. eauto. eauto. 
           }
           assert (locs_locs_stty (st2 M3) qt2' = locs_locs_stty (st2 M2) qt2') as L322. {
             erewrite <-lls_change2. eauto. eauto.  
           }

           assert (locs_locs_stty (st1 M2) qt1' = locs_locs_stty (st1 M') qt1') as L211. {
             erewrite <- lls_change1 with (q2 := qt2'). eauto. eapply stchain_tighten; eauto. 
             eapply H14.
             intros ? ?. auto. intros ? ?. auto.
           }

           assert (locs_locs_stty (st2 M2) qt2' = locs_locs_stty (st2 M') qt2') as L212. {
             erewrite <- lls_change2 with (q1 := qt1'). eauto. eapply stchain_tighten; eauto.
             eapply H14.
             intros ? ?. auto. intros ? ?. auto.
           }

           assert (st_chain_partial M' M3 (locs_locs_stty (st1 M') qt1')(locs_locs_stty (st2 M') qt2')). {
             eapply st_trans''. eapply stchain_tighten. eauto.
             eapply H14. eauto.
             intros ? ?. auto. intros ? ?. auto.
             rewrite <- L211. rewrite <- L212. auto.
             auto. auto. 
           }


           assert (st_chain_partial M' M3 (locs_locs_stty (st1 M3) qt1') (locs_locs_stty (st2 M3) qt2')). {
             rewrite L321, L211. rewrite L322, L212. auto.
           }


           assert (st_chain_partial M3 M' (locs_locs_stty (st1 M3) qt1') (locs_locs_stty (st2 M3) qt2')). {
             eapply stchain_symmetry. auto. 
           }


          assert (st_chain_partial M3 M' (locs_locs_stty (st1 M3) (val_locs v1')) (locs_locs_stty (st2 M3) (val_locs v2'))). {
             eapply stchain_tighten.  auto. 
             eauto. eauto. eauto. 
           }



           assert (psub (locs_locs_stty (st1 M3) (val_locs v1')) (locs_locs_stty (st1 M') qt1')). {
             rewrite <-L211, <-L321. eauto. 
           }

           assert (psub (locs_locs_stty (st2 M3) (val_locs v2')) (locs_locs_stty (st2 M') qt2')). {
             rewrite <-L212, <-L322. eauto. 
           }

           assert (st_chain_partial M3 M' (locs_locs_stty (st1 M') (val_locs v1')) (locs_locs_stty (st2 M') (val_locs v2'))). {
             erewrite <-lls_change1.  erewrite <- lls_change2. eauto. eauto. eauto. 
           }

           assert (st_chain_partial M' M3 (locs_locs_stty (st1 M3) (val_locs v1')) (locs_locs_stty (st2 M3) (val_locs v2'))). {
             eapply stchain_symmetry. auto.
           }


           assert (st_chain_partial M' M3 (locs_locs_stty (st1 M') (val_locs v1')) (locs_locs_stty (st2 M') (val_locs v2'))). {
             erewrite <- lls_change1. erewrite <- lls_change2. eauto. eauto. eauto.  
           }


          subst vt. split; intros.
          eapply valt_store_change. 2: eapply H24. eauto. eauto. 
          eapply valt_store_change. 2: eapply H24. eauto. eauto. 
      -- intros. subst qt1. rewrite plift_vars_locs. auto.
      -- intros. subst qt2. rewrite <- plift_vars_locs. repeat rewrite plift_splice. auto.
         
      -- intros ? ?. subst x M2. eapply lls_s. unfoldq. eauto. 
           unfold st_extend. simpl. bdestruct (length S1' =? length (st1 M')); intuition.
           auto.
      -- intros ? ?. subst x M2. eapply lls_s. unfoldq. eauto. 
           unfold st_extend. simpl. bdestruct (length S2' =? length (st2 M')); intuition.
           auto.
  + (* valq 1 *)
    intros ? ?. inversion H3.
    * right. simpl. subst x1 q0 M0. rewrite val_locs_ref in *.
      unfold pone in H4. subst x x0. unfold pdiff, pnat. unfoldq.
      simpl. rewrite SL1. eapply st_mono1 in STC.  unfold length1 in STC. lia.
    * left. simpl. subst x1 q0 M0. rewrite val_locs_ref in *.
      unfold pone in H4. subst x x2. unfold st_extend in *.
      unfold st1 in *. simpl in *. rewrite SL1 in H5.
      bdestruct (length (fst (fst (fst M'))) =? length (fst (fst (fst M')))); intuition.
      inversion H5. subst qt. 
      eapply lls_mono. 2: eapply H6. subst qt1. rewrite <-plift_vars_locs. 
      intros ? ?. eapply vars_locs_mono; eauto. unfoldq; intuition.
  + (* valq 2 *)
    intros ? ?. inversion H3.
    * right. simpl. subst x1 q0 M0. rewrite val_locs_ref in *.
      unfold pone in H4. subst x x0. unfold pdiff, pnat. unfoldq.
      simpl. rewrite SL2. eapply st_mono2 in STC.  unfold length2 in STC. lia.
    * left. simpl. subst x1 q0 M0. rewrite val_locs_ref in *.
      unfold pone in H4. subst x x2. unfold st_extend in *.
      unfold st2 in *. simpl in *. rewrite SL2 in H5.
      bdestruct (length (snd (fst (fst M'))) =? length (snd (fst (fst M')))); intuition.
      inversion H5.  subst qt. 
      eapply lls_mono. 2: eapply H6. subst qt2. rewrite <-plift_vars_locs. 
      intros ? ?. eapply vars_locs_mono; eauto. rewrite plift_splice. unfoldq; intuition. 
      eapply splice_psub in SUB; eauto.
Qed.
    

Lemma bi_tget1_splice: forall t S1 S2 S1' S2' M M' G H1 H2 HX H2' p q e v1 v2 T q1 fr
  (WFE: env_type1 M H1 H2 H2' HX G p)
  (ST: store_type S1 S2 M)
  (SUB: psub (plift q1) (plift p)),
  exp_type1 S1 S2 M H1 (H2'++HX++H2) t (splice_tm t (length H2)(length HX)) 
    S1' S2' M' v1 v2 (TRef T false q1)  (TRef (splice_ty T (length H2)(length HX)) false (splice_ql q1 (length H2)(length HX))) 
    (plift p) (splice_pl (plift p) (length H2)(length HX))
    fr fr
    (plift q) (splice_pl (plift q) (length H2)(length HX)) 
    (plift e) (splice_pl (plift e) (length H2)(length HX)) ->
  exists S1'' S2'' M'' v3 v4,
  exp_type1 S1 S2 M H1 (H2'++HX++H2) (tget t) (tget (splice_tm t (length H2)(length HX)))  S1'' S2''  M'' v3 v4 
      T (splice_ty T (length H2)(length HX)) 
     (plift p) (splice_pl (plift p) (length H2)(length HX))
     false false 
     (plift q1) (splice_pl (plift q1) (length H2)(length HX))
     (plift e) (splice_pl (plift e) (length H2)(length HX)).
Proof.  
  intros.  
  destruct H as [IE1 [IE2 [SC [SF1 [ST1 [SE1 [SE2 [HV [HQ1 HQ2]]]]]]]]].
  remember HV as HV'. clear HeqHV'.
  destruct v1; destruct v2; try solve [inversion HV]. simpl in HV.
  
  destruct HV as [HT [HT' [F1 [F2 [SUB1 [SUB2 [STREL [STF HV]]]]]]]].
  remember ST1 as ST1'. clear HeqST1'.
  destruct ST1 as [SST1 [SST2 [SP1 [R L]]]].

  assert (strel M' i i0) as A. eauto.

  destruct (SP1 i i0 A) as [vt [qt1 [qt2 [v1 [v2 [IM1 [IM2 [IS1 [IS2 [STVT [VT STFV]]]]]]]]]]]. 

  destruct HV as  [vt' [qt1' [qt2' [IM1' [IM2' [STVALT [VT1 ?]]]]]]]; intuition.
  rewrite IM1 in IM1'. inversion IM1'. subst qt1'.
  rewrite IM2 in IM2'. inversion IM2'. subst qt2'.

  exists S1', S2', M', v1, v2. 
  split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 8: split. 9: split.
  + destruct IE1 as [n1 IW1].
    exists (S n1). intros. destruct n. lia. simpl.
    rewrite IW1. rewrite IS1. eauto. lia.
  + destruct IE2 as [n1 IW2].
    exists (S n1). intros. destruct n. lia. simpl.
    rewrite IW2. rewrite IS2. eauto. lia.
  + (* st_chain *)
    auto.
    
  + (* st_filter  *)
    auto.
  + (* store_type *)
    auto.
  + (* effect 1 *)
    auto.
  + (* effect  *)
    auto.
  + (* val_type *)  
    assert (st_chain M' M'). eapply st_refl; eauto.
    eapply valt_store_extend.  2: eapply VT1. eapply ST1'. 2: eapply ST1'.
    eapply stchain_tighten; eauto. eapply indexr_filter; eauto.
    eapply valt_filter in HV' as B. repeat rewrite val_locs_ref in B. auto.
    eapply lls_indexr_closed'''; eauto. eapply lls_indexr_closed'''; eauto.
    auto.
    destruct SST1 as (X & Y). destruct (Y i) as [qt1' [v' [IM1'' [IS1' [? ?]]]]].
    apply indexr_var_some' in IS1. lia.   
    rewrite IM1 in IM1''.  inversion IM1''. subst qt1'.
    rewrite IS1 in IS1'. inversion IS1'. subst v'. eapply H6. 
    destruct SST2 as (X & Y). destruct (Y i0) as [qt2' [v2' [IM2'' [IS2' [? ?]]]]].
    apply indexr_var_some' in IS2. lia. rewrite IM2 in IM2''.  inversion IM2''. subst qt2'.
    rewrite IS2 in IS2'. inversion IS2'. subst v2'. eapply H6. 
    rewrite STVALT in STVT. subst. 
    auto. auto.
    
  + intros ? ?.  left. 
    destruct SST1 as (X & Y). destruct (Y i) as [qt1' [v' [IM1'' [IS1' [? ?]]]]].
    apply indexr_var_some' in IS1. lia. rewrite IM1 in IM1''.  inversion IM1''. subst qt1'.
    rewrite IS1 in IS1'. inversion IS1'. subst v'.
    eapply H6 in H4; eauto. rewrite H0 in H4. eapply lls_mono; eauto. eapply vars_locs_mono. unfoldq; intuition. 

  + intros ? ?.  left. 
    destruct SST2 as (X & Y). destruct (Y i0) as [qt2' [v' [IM2'' [IS2' [? ?]]]]].
    apply indexr_var_some' in IS2. lia. rewrite IM2 in IM2''.  inversion IM2''. subst qt2'.
    rewrite IS2 in IS2'. inversion IS2'. subst v'.
    eapply H6 in H4; eauto. rewrite H in H4. eapply lls_mono; eauto. eapply vars_locs_mono. unfoldq; intuition.
    eapply splice_psub in SUB. rewrite plift_splice in H8. eapply SUB; eauto.
    rewrite plift_splice in H8. auto.
Qed.

Lemma bi_tget2_splice: forall t S1 S2 S1' S2' M M' G H1 H2 HX H2' p q e v1 v2 T q1 fr
  (WFE: env_type M H1(H2' ++ H2) G (plift p))
  (ST: store_type S1 S2 M)
  (E: exp_type1 S1 S2 M H1 (H2'++HX++H2) t (splice_tm t (length H2)(length HX)) 
    S1' S2' M' v1 v2 (TRef T false q1)  (splice_ty (TRef T false q1) (length H2)(length HX)) 
    (plift p) (splice_pl (plift p) (length H2)(length HX))
    fr fr
    (plift q) (splice_pl (plift q) (length H2)(length HX)) 
    (plift e) (splice_pl (plift e) (length H2)(length HX))), 
  exists S1'' S2'' M'' v3 v4,
  exp_type1 S1 S2 M H1 (H2'++HX++H2) (tget t) (splice_tm (tget t) (length H2)(length HX))  S1'' S2''  M'' v3 v4 
      T (splice_ty T (length H2)(length HX)) 
     (plift p) (splice_pl (plift p) (length H2)(length HX))
     fr fr 
     (plift q) (splice_pl (plift q) (length H2)(length HX))
     (plift e) (splice_pl (plift e) (length H2)(length HX)).
Proof.   
  intros.  
  destruct E as [IE1 [IE2 [STC [STF' [ST' [SE1 [SE2 [HV [HQ1 HQ2]]]]]]]]]. 
  remember HV as HV'. clear HeqHV'.
  destruct v1; destruct v2; try solve [inversion HV]. simpl in HV.
  
  destruct HV as [HT [HT' [F1 [F2 [SUB1 [SUB2 [STREL [STF HV]]]]]]]].
  remember ST' as ST''. clear HeqST''.
  destruct ST' as [STL1 [STL2 [SP1 [SP2 SP3]]]].

  assert (strel M' i i0) as A. eauto.
 
  destruct (SP1 i i0 A) as [vt [qt1 [qt2 [v1 [v2 [IM1 [IM2 [IS1 [IS2 [SVT [VT STFV]]]]]]]]]]]. 

  destruct HV as [vt' [qt1' [qt2' [IM1' [IM2'[SVT' [VT' ?]]]]]]]; intuition.
  rewrite IM1 in IM1'. inversion IM1'. subst qt1'.
  rewrite IM2 in IM2'. inversion IM2'. subst qt2'.
  
  exists S1', S2', M', v1, v2. 
  split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 8: split. 9: split.
  + destruct IE1 as [n1 IW1].
    exists (S n1). intros. destruct n. lia. simpl.
    rewrite IW1. rewrite IS1. eauto. lia.
  + destruct IE2 as [n1 IW2].
    exists (S n1). intros. destruct n. lia. simpl.
    rewrite IW2. rewrite IS2. eauto. lia.
  + eauto.
  + eauto.
  + eauto.
  + eauto.
  + eauto. 
  + assert (st_chain M' M'). eapply st_refl; eauto.
    eapply valt_store_extend.  2: eapply VT'. eapply ST''. 2: eapply ST''.
    eapply stchain_tighten; eauto. eapply indexr_filter; eauto.
    eapply valt_filter in HV' as B. repeat rewrite val_locs_ref in B. auto.
    eapply lls_indexr_closed'''; eauto. eapply lls_indexr_closed'''; eauto.
    auto.
    destruct STL1 as (X & Y). destruct (Y i) as [qt1' [v' [IM1'' [IS1' [? ?]]]]].
    apply indexr_var_some' in IS1. lia. rewrite IM1 in IM1''.  inversion IM1''. subst qt1'.
    rewrite IS1 in IS1'. inversion IS1'. subst v'. eapply H6. auto.
    destruct STL2 as (X & Y). destruct (Y i0) as [qt2' [v2' [IM2'' [IS2' [? ?]]]]].
    apply indexr_var_some' in IS2. lia. rewrite IM2 in IM2''.  inversion IM2''. subst qt2'.
    rewrite IS2 in IS2'. inversion IS2'. subst v2'. eapply H6. auto.
    rewrite SVT in SVT'. subst. auto.
    auto.
    
  + intros ? ?. eapply HQ1. rewrite val_locs_ref. 
    eapply lls_s; eauto. unfoldq; intuition.
    destruct STL1 as (X & Y). destruct (Y i) as [qt1' [v' [IM1'' [IS1' [? ?]]]]].
    apply indexr_var_some' in IS1. lia. rewrite IM1 in IM1''.  inversion IM1''. subst qt1'.
    rewrite IS1 in IS1'. inversion IS1'. subst v'. intuition. 
    
  + intros ? ?. eapply HQ2. rewrite val_locs_ref. 
    eapply lls_s; eauto. unfoldq; intuition.
    destruct STL2 as (X & Y). destruct (Y i0) as [qt2' [v' [IM2'' [IS2' [? ?]]]]].
    apply indexr_var_some' in IS2. lia. rewrite IM2 in IM2''.  inversion IM2''. subst qt2'.
    rewrite IS2 in IS2'. inversion IS2'. subst v'. intuition. 
Qed.

Lemma bi_tget_splice: forall t S1 S2 S1' S2' M M' G H1 H2 HX H2' p q e v1 v2 T q1 rf1 fr
  (WFE: env_type M H1(H2' ++ H2) G (plift p))
  (ST: store_type S1 S2 M)
  (E: exp_type1 S1 S2 M H1 (H2'++HX++H2) t (splice_tm t (length H2)(length HX)) 
    S1' S2' M' v1 v2 (TRef T rf1 q1)  (splice_ty (TRef T rf1 q1) (length H2)(length HX)) 
    (plift p) (splice_pl (plift p) (length H2)(length HX))
    fr fr
    (plift q) (splice_pl (plift q) (length H2)(length HX)) 
    (plift e) (splice_pl (plift e) (length H2)(length HX)))
  (SUB: psub (plift q1) (plift p)), 
  exists S1'' S2'' M'' v3 v4,
  exp_type1 S1 S2 M H1 (H2'++HX++H2) (tget t) (splice_tm (tget t) (length H2)(length HX))  S1'' S2''  M'' v3 v4 
      T (splice_ty T (length H2)(length HX)) 
     (plift p) (splice_pl (plift p) (length H2)(length HX))
     (if rf1 then fr else false) (if rf1 then fr else false) 
     (por (plift q1) (pif rf1 (plift q))) (splice_pl (por (plift q1) (pif rf1 (plift q))) (length H2)(length HX))
     (plift e) (splice_pl (plift e) (length H2)(length HX)).
Proof.
  intros. 
  destruct E as [IE1 [IE2 [STC [STF' [ST' [SE1 [SE2 [HV [HQ1 HQ2]]]]]]]]]. 
  remember HV as HV'. clear HeqHV'.
  destruct v1; destruct v2; try solve [inversion HV]. simpl in HV.
  
  destruct HV as [HT [HT' [F1 [F2 [SUB1 [SUB2 [STREL [STF HV]]]]]]]].
  remember ST' as ST''. clear HeqST''.
  destruct ST' as [STL1 [STL2 [SP1 [SP2 SP3]]]].

  assert (strel M' i i0) as A. eauto.
 
  destruct (SP1 i i0 A) as [vt [qt1 [qt2 [v1 [v2 [IM1 [IM2 [IS1 [IS2 [SVT [VT SFT]]]]]]]]]]]. 

  destruct HV as [vt' [qt1' [qt2' [IM1' [IM2'[SVT' [VT' ?]]]]]]]; intuition.
  rewrite IM1 in IM1'. inversion IM1'. subst qt1'.
  rewrite IM2 in IM2'. inversion IM2'. subst qt2'.

  exists S1', S2', M', v1, v2. 
  split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 8: split. 9: split.
  + destruct IE1 as [n1 IW1].
    exists (S n1). intros. destruct n. lia. simpl.
    rewrite IW1. rewrite IS1. eauto. lia.
  + destruct IE2 as [n1 IW2].
    exists (S n1). intros. destruct n. lia. simpl.
    rewrite IW2. rewrite IS2. eauto. lia.
  + eauto.
  + eauto.
  + eauto.
  + eauto.
  + eauto. 
  + assert (st_chain M' M'). eapply st_refl; eauto.
    eapply valt_store_extend.  2: eapply VT'. eapply ST''. 2: eapply ST''.
    eapply stchain_tighten; eauto. eapply indexr_filter; eauto.
    eapply valt_filter in HV' as B. repeat rewrite val_locs_ref in B. auto.
    eapply lls_indexr_closed'''; eauto. eapply lls_indexr_closed'''; eauto.
    auto.
    destruct STL1 as (X & Y). destruct (Y i) as [qt1' [v' [IM1'' [IS1' [? ?]]]]].
    apply indexr_var_some' in IS1. lia. rewrite IM1 in IM1''.  inversion IM1''. subst qt1'.
    rewrite IS1 in IS1'. inversion IS1'. subst v'. eapply H6. auto.
    destruct STL2 as (X & Y). destruct (Y i0) as [qt2' [v2' [IM2'' [IS2' [? ?]]]]].
    apply indexr_var_some' in IS2. lia. rewrite IM2 in IM2''.  inversion IM2''. subst qt2'.
    rewrite IS2 in IS2'. inversion IS2'. subst v2'. eapply H6. auto.
    rewrite SVT in SVT'. subst. auto.
    auto.

  + destruct STL1 as (X & Y). destruct (Y i) as [qt1' [v' [IM1'' [IS1' [? ?]]]]].
    apply indexr_var_some' in IS1. lia. rewrite IM1 in IM1''.  inversion IM1''. subst qt1'.
    rewrite IS1 in IS1'. inversion IS1'. subst v'. 

    destruct rf1. 
    * assert (val_qual (st1 M) (st1 M') H1 v1 fr (pand (plift p) (plift q))). {
        intros ? ?. eapply HQ1. rewrite val_locs_ref.
        eapply lls_s. unfold pone. intuition. eauto. eapply H4; eauto.
     }
      intros ? ?. destruct (H7 x). 
      -- eauto.
      -- left. eapply lls_mono. 2: eauto. eapply vars_locs_mono. unfoldq. intuition.
      -- right. eauto. 
    * assert (val_qual (st1 M) (st1 M') H1 v1 false (pand (plift p) (plift q1))). { 
        intros ? ?. left. eapply H4 in H7; auto. rewrite H0 in H7; auto. eapply lls_mono; eauto.
        eapply vars_locs_mono; eauto. unfoldq; intuition.
      }
      intros ? ?. destruct (H7 x). 
      -- auto.
      -- left. eapply lls_mono; eauto. eapply vars_locs_mono. 
         intros ? ?. unfoldq; intuition.
      -- right. auto.
    
  + destruct STL2 as (X & Y). destruct (Y i0) as [qt2' [v' [IM2'' [IS2' [? ?]]]]].
    apply indexr_var_some' in IS2. lia. rewrite IM2 in IM2''.  inversion IM2''. subst qt2'.
    rewrite IS2 in IS2'. inversion IS2'. subst v'. 

    destruct rf1. 
    * assert (val_qual (st2 M) (st2 M') (H2'++HX++H2) v2 fr 
                (pand (splice_pl (plift p)(length H2) (length HX))(splice_pl (por (plift q1)(pif true (plift q)))(length H2) (length HX)))). {
        intros ? ?. rewrite splice_por. destruct (HQ2 x). rewrite val_locs_ref. 
        eapply lls_s. unfold pone. intuition. eauto. eauto.
        left. eapply lls_mono; eauto. eapply vars_locs_mono; eauto. unfoldq; intuition.
        right. auto.
     }
      intros ? ?. destruct (H7 x). 
      -- eauto.
      -- left. eapply lls_mono. 2: eauto. eapply vars_locs_mono. unfoldq. intuition.
      -- right. eauto. 
    * assert (val_qual (st2 M) (st2 M') (H2'++HX++H2) v2 false (splice_pl (pand (plift p) (plift q1)) (length H2)(length HX))). { 
        intros ? ?. left. eapply H4 in H7; auto. rewrite H in H7; auto. eapply lls_mono; eauto.
        eapply vars_locs_mono; eauto. rewrite plift_splice. unfoldq; intuition.
        eapply splice_psub; eauto. unfoldq; intuition.
      }
      intros ? ?. destruct (H7 x). 
      -- auto.
      -- left. eapply lls_mono; eauto. eapply vars_locs_mono. 
         intros ? ?. rewrite splice_por. unfoldq; intuition.
         eapply splice_psub. 2: eapply H10. unfoldq; intuition.
         left. eapply splice_psub. 2: eapply H10. unfoldq; intuition.
      -- right. auto.    
Qed.

Lemma bi_tput_splice: forall S1 S2 M H1 H2 H2' HX t1 t2 S1' S2' M' M'' S1'' S2'' v1 v2 v3 v4 p q1  e1 e2 T fr2 q2 fr1 G
 (WFE: env_type1 M H1 H2 H2' HX G p )
 (ST: store_type S1 S2 M)
 (E1: exp_type1 S1 S2 M H1 (H2'++HX++H2) t1 (splice_tm t1 (length H2) (length HX)) S1' S2' M' v1 v2 
        (TRef T fr2 q2) (TRef (splice_ty T (length H2) (length HX)) fr2 (splice_ql q2 (length H2)(length HX)))
        (plift p) (splice_pl (plift p) (length H2) (length HX)) fr1 fr1
        (plift q1) (splice_pl (plift q1) (length H2) (length HX)) 
        (plift e1) (splice_pl (plift e1) (length H2) (length HX)))
 (E2: exp_type1 S1' S2' M' H1 (H2'++HX++H2) t2 (splice_tm t2 (length H2) (length HX)) S1'' S2'' M'' v3 v4 
        T (splice_ty T (length H2) (length HX)) 
        (plift p) (splice_pl (plift p) (length H2) (length HX)) 
        false false  
        (plift q2) (splice_pl (plift q2) (length H2) (length HX)) 
        (plift e2) (splice_pl (plift e2) (length H2) (length HX))),
 exists S1''' S2''' M''' v5 v6,
  exp_type1 S1 S2 M H1 (H2'++HX++H2) (tput t1 t2) (tput (splice_tm t1 (length H2) (length HX)) (splice_tm t2 (length H2) (length HX))) 
    S1''' S2'''  M''' v5 v6 TBool TBool 
    (plift p) (splice_pl (plift p) (length H2) (length HX))
    false false pempty pempty 
    (por (plift e1) (por (plift e2) (plift q1))) (splice_pl (por (plift e1) (por (plift e2) (plift q1))) (length H2) (length HX)).
Proof.  
  intros. 
  destruct E1 as [IE1 [IE2 [STC [STF1 [ST1 [SE1 [SE2 [HV1 [HQ1 HQ2]]]]]]]]]. 
  destruct E2 as [IE3 [IE4 [SC2 [STF2 [ST2 [SE3 [SE4 [HV2 [HQ3 HQ4]]]]]]]]].

  remember ST as ST'. clear HeqST'.
  destruct ST as [SST1 [SST2 [SP1 [SP2 SP3]]]].
  destruct SST1 as [LS1 PS1]. destruct SST2 as [LS2 PS2].

  remember HV1 as HV1'. clear HeqHV1'.

  destruct v1; destruct v2; try solve [inversion HV1]. simpl in HV1.
  destruct HV1 as (CLT1 & CLT2 & F1 & F2 & SUB1 & SUB2 & STR & STF & vt & qt1 & qt2 & IM1 & IM2 & ? & SVT & QT1 & QT2 & ? & ?).

  remember ST2 as ST2'. clear HeqST2'.
  destruct ST2 as [SST3 [SST4 [SP4 [SP5 SP6]]]].
  destruct SST3 as [LS3 PS3]. destruct SST4 as [LS4 PS4].

  assert (st_locs1 M' i) as A. { apply indexr_var_some' in IM1. unfold st_locs1, pnat, length1. lia. }
  assert (st_locs2 M' i0) as B. { apply indexr_var_some' in IM2. unfold st_locs2, pnat, length2. lia. }
  assert (indexr i (st1 M') = indexr i (st1 M'')) as R1. { eapply SC2; auto. }
  assert (indexr i0 (st2 M') = indexr i0 (st2 M'')) as R2. { eapply SC2; auto. }

  exists (update S1'' i v3), (update S2'' i0 v4).
  exists M'', (vbool true), (vbool true).
  split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 8: split. 9: split. 
  * (* first one *)
    destruct IE1 as [n1 IE1].
    destruct IE3 as [n3 IE3].
    exists (S(n1 + n3)). intros. destruct n. intuition.
    simpl. rewrite IE1. rewrite IE3.
    assert (i < length S1''). 
    rewrite LS3. eapply st_mono1'; eauto.
    apply indexr_var_some in H5. destruct H5. rewrite H5. auto. lia. lia.

  
  * (* 2nd  one *) 
    destruct IE2 as [n2 IE2].
    destruct IE4 as [n4 IE4].
    exists (S(n2 + n4)). intros. destruct n. intuition.
    simpl. rewrite IE2. rewrite IE4. 
    assert (i0 < length S2''). 
    rewrite LS4. eapply st_mono2'; eauto. 
    apply indexr_var_some in H5. destruct H5. rewrite H5. auto. lia. lia.

  * eapply st_trans; eauto.  

  * auto.
  
  * (* store typing *)
    repeat split. 
    + (* length *)
      rewrite <-update_length. eauto.
    + rewrite <-update_length.  
      intros. destruct (PS3 l) as [qt1' [v1' [IM1' [IS1' [P1' P2']]]]]; auto.
      bdestruct (l =? i).
      - exists qt1', v3; intuition. 
        -- subst l. rewrite update_indexr_hit. auto. auto.
        -- subst l. rewrite <- R1 in IM1'. rewrite IM1 in IM1'. inversion IM1'. subst qt1.
           intros ? ?. eapply HQ3 in H5. destruct H5.
           rewrite QT1. eapply lls_mono; eauto. eapply vars_locs_mono; eauto.
           intros ? ?. unfoldq; intuition. 
           simpl in H5. intuition.
      - exists qt1', v1'; intuition. rewrite update_indexr_miss. auto. auto.
    + (* length *)
      rewrite <-update_length. eauto.
    + rewrite <-update_length.  
      intros. destruct (PS4 l) as [qt2' [v2' [IM2' [IS2' [P1' P2']]]]]; auto.
      bdestruct (l =? i0).
      - exists qt2', v4; intuition. 
        -- subst l. rewrite update_indexr_hit. auto. auto.
        -- subst l. rewrite <- R2 in IM2'. rewrite IM2 in IM2'. inversion IM2'. subst qt2.
           intros ? ?. eapply HQ4 in H5. destruct H5.
           rewrite QT2. rewrite plift_splice. eapply lls_mono; eauto. eapply vars_locs_mono; eauto.
           intros ? ?. unfoldq; intuition. 
           simpl in H5. intuition.
      - exists qt2', v2'; intuition. rewrite update_indexr_miss. auto. auto.
    + intros. destruct (SP4 l1 l2) as [vt' [qt1' [qt2' [v1' [v2' [IM1' [IM2' [IS1' [IS2' [SVT' [VTT STF']]]]]]]]]]]; auto.
      bdestruct (l1 =? i). 
      assert (l2 = i0).  {
        destruct HV1'. subst.
        destruct SC2 as [? [? [? [? [? ?]]]]]. specialize (H11 i i0); intuition.
        eapply SP5; eauto.
      }
      - subst l1 l2. remember ST2' as ST2''. clear HeqST2''. 
        destruct ST' as [SST1' [SST2' ST' ]].
        exists vt, qt1', qt2', v3, v4; intuition.
        rewrite update_indexr_hit. auto. apply indexr_var_some' in IS1'. lia.
        rewrite update_indexr_hit. auto. apply indexr_var_some' in IS2'. lia.
        
        destruct SC2 as [? [? [? [? [? ?]]]]]. specialize (H12 i i0); intuition.
        congruence.

        eapply SVT. 6: eapply HV2. 2: eapply ST2'. eapply stchain_tighten; eauto. eapply indexr_filter; eauto.
        repeat rewrite <- val_locs_ref.
        eapply valt_filter. eauto. eapply lls_indexr_closed'''; eauto. destruct ST1 as [? [? ?]]; eauto. 
        eapply lls_indexr_closed'''; eauto. destruct ST1 as [? [? ?]]; eauto.   
        eapply valt_filter. eauto. 
        intros ? ?. destruct (HQ3 x); auto.  
        rewrite QT1. eapply lls_mono; eauto. eapply vars_locs_mono. unfoldq; intuition.
        simpl in H9. contradiction.

        intros ? ?. destruct (HQ4 x); auto.
        rewrite QT2. rewrite plift_splice. eapply lls_mono; eauto. eapply vars_locs_mono. unfoldq; intuition.
        simpl in H9. contradiction.
        
        eapply valt_filter; eauto.

      - assert (l2 = i0 -> False). {
        intros. subst. 
        assert (strel M'' i i0). {
          destruct SC2 as [? [? [? [? [? ?]]]]]. eapply H10. intuition. auto.
        }
        assert (l1 = i). eapply SP6; eauto. contradiction.
      }
        exists vt', qt1', qt2', v1', v2'; intuition.
        rewrite update_indexr_miss. auto. auto. 
        rewrite update_indexr_miss. auto. auto. 
    + eauto.
    + eauto.
  
  * (* store preservation 1 *)
    assert (length S1 = length1 M). destruct ST1 as ((? & ?) & ? & ?). eauto.
    assert (length S2 = length2 M). destruct ST1 as (? & (? & ?) & ?). eauto.
    intros ? ?. intros.
    bdestruct (i =? l). { subst. destruct (HQ1 l).
      left. rewrite val_locs_ref. unfoldq; intuition.
      destruct H6. erewrite lls_change1. eapply lls_mono; eauto.
      eapply vars_locs_mono. unfoldq; intuition.
      eapply stchain_tighten. eapply envt1_filter_deep. eauto. eauto. unfoldq; intuition. eauto.
      eapply envt1_store_deep_wf1; eauto. unfoldq; intuition. eapply envt1_store_deep_wf2; eauto. unfoldq; intuition.
            
      destruct fr1; simpl in *. destruct H. apply indexr_var_some' in H7.  unfoldq; intuition.
      contradiction.
      
    }{ rewrite update_indexr_miss.
       assert ((locs_locs_stty (st1 M) (vars_locs H1 (pand (plift p) (plift e2))) l) =
               locs_locs_stty (st1 M') (vars_locs H1 (pand (plift p) (plift e2))) l) as LLS1. {
          erewrite lls_change; eauto. eapply sstchain_tighten. destruct STC as [? [? [? ?]]]. eauto.
          eapply envt1_store_deep_wf1; eauto. unfoldq; intuition.
        }

        assert ( ~ locs_locs_stty (st1 M) (vars_locs H1 (pand (plift p) (plift e1))) l) as X. { 
          intros ?. eapply H6. eapply lls_mono; eauto. eapply vars_locs_mono; eauto. unfoldq; intuition.
        }
        
        unfold store_effect in *.
        eapply SE1 in X as C; eauto. 
        eapply SE3 in C; eauto.
        rewrite <- LLS1. 
        intros ?. eapply H6. eapply lls_mono; eauto. eapply vars_locs_mono; eauto. unfoldq; intuition.
        lia.
     }
  * (* store preservation 2 *)
    assert (length S1 = length1 M). destruct ST1 as ((? & ?) & ? & ?). eauto.
    assert (length S2 = length2 M). destruct ST1 as (? & (? & ?) & ?). eauto.
    intros ? ?. intros.
    bdestruct (i0 =? l). { subst. destruct (HQ2 l).
      left. rewrite val_locs_ref. unfoldq; intuition.
      destruct H6. erewrite lls_change. eapply lls_mono; eauto. 
      eapply vars_locs_mono. rewrite splice_por. rewrite splice_por. unfoldq; intuition.
      eapply sstchain_tighten; eauto. destruct STC as [? [? [? [? ?]]]]. eauto.
      rewrite <- splice_pand. eapply envt1_store_deep_wf2; eauto. unfoldq; intuition.
      
      destruct fr1; simpl in *. destruct H. apply indexr_var_some' in H7. unfoldq; intuition.
      contradiction.
      
    }{ rewrite update_indexr_miss.
       assert ((locs_locs_stty (st2 M) (vars_locs (H2'++HX++H2) (splice_pl (pand (plift p) (plift e2))(length H2)(length HX))) l) =
               (locs_locs_stty (st2 M') (vars_locs (H2'++HX++H2) (splice_pl (pand (plift p) (plift e2))(length H2)(length HX))) l)) as LLS2. {
          erewrite lls_change; eauto.
          eapply sstchain_tighten. destruct STC as [? [? [? [? ?]]]]. eauto.
          eapply envt1_store_deep_wf2; eauto. unfoldq; intuition.
        }

        assert (~ locs_locs_stty (st2 M) (vars_locs (H2'++HX++H2) (splice_pl (pand (plift p) (plift e1))(length H2)(length HX))) l) as X. { 
          intros ?. eapply H6. eapply lls_mono. 2: eapply H9. eapply vars_locs_mono; eauto. 
          rewrite splice_por. rewrite splice_pand. unfoldq; intuition.
        }
        rewrite splice_pand in X.
        unfold store_effect in *.
        eapply SE2 in X as C; eauto. 
        eapply SE4 in C. eauto. 
        rewrite <- splice_pand. rewrite <- LLS2.
        intros ?. eapply H6. eapply lls_mono. 2: eapply H9.  eauto. eapply vars_locs_mono; eauto. 
        repeat rewrite splice_por. rewrite splice_pand. unfoldq; intuition.
        lia.
     }
  
  * (* val_type *)
  simpl. auto.
  * constructor. rewrite val_locs_bool in H4. eapply lls_mono; eauto. intros ? ?. unfoldq; intuition.
  * constructor. rewrite val_locs_bool in H4. eapply lls_mono; eauto. intros ? ?. unfoldq; intuition.
Qed.


Lemma bi_tapp_splice: forall M M' M'' S1 S2 S1' S2' S1'' S2'' vf1 vf2 vx1 vx2 G H1 H2 H2' HX f x T1 fn1 fr1 T2 fn2 ar2 fr2 p qf ef q1 q2 ex e2 e2f e2x frx frf qx
   (WFE: env_type1 M H1 H2 H2' HX G p)
   (ST: store_type S1 S2 M)
   (IEF: exp_type1 S1 S2 M H1 (H2'++HX++H2) f (splice_tm f (length H2)(length HX)) S1' S2' M' vf1 vf2
        (TFun T1 fn1 fr1 q1 T2 fn2 ar2 fr2 q2 e2f e2x e2) 
        (splice_ty (TFun T1 fn1 fr1 q1 T2 fn2 ar2 fr2 q2 e2f e2x e2) (length H2)(length HX)) 
        (plift p) (splice_pl (plift p) (length H2)(length HX)) 
        frf frf 
        (plift qf) (splice_pl (plift qf) (length H2)(length HX)) 
        (plift ef) (splice_pl (plift ef) (length H2)(length HX)))  
   (IEX: exp_type1 S1' S2' M' H1 (H2'++HX++H2) x (splice_tm x (length H2)(length HX)) S1'' S2'' M'' vx1 vx2 
          T1 (splice_ty T1 (length H2)(length HX)) 
          (plift p ) (splice_pl (plift p) (length H2)(length HX)) 
          frx frx
          (plift qx) (splice_pl (plift qx) (length H2)(length HX)) 
          (plift ex) (splice_pl (plift ex) (length H2)(length HX)))
  (HSEP: if fn1 then
          if fr1 then
            True
          else
            (frx = false /\ (exists x0, f = tvar x0 /\ psub (plift qx) (pone x0))) \/
            (frx = false /\ (exists p0 t, f = tabs p0 t /\ psub (plift qx) (plift p0))) \/
            (frx = false /\ psub (plift qx) (plift q1))
        else
          if fr1 then
            psub (pand 
                    (plift (vars_trans_fix G qf))
                    (plift (vars_trans_fix G qx)))
              (plift q1)
          else
            frx = false /\ psub (plift qx) (plift q1))         
   (Q1: psub (plift q1) (plift p))
   (Q2: psub (plift q2) (plift p))
   (E2: psub (plift e2) (plift p)),
   exists S1''' S2''' M''' v5 v6,
    exp_type1 S1 S2 M H1 (H2'++HX++H2) (tapp f x)(splice_tm (tapp f x) (length H2)(length HX)) S1''' S2''' M''' v5 v6 
        T2 (splice_ty T2 (length H2)(length HX)) 
        (plift p) (splice_pl (plift p) (length H2)(length HX)) 
        (fn2 && frf || ar2 && frx || fr2) (fn2 && frf || ar2 && frx || fr2)
        (por (pif fn2 (plift qf))(por (pif ar2 (plift qx))(plift q2))) 
            (splice_pl (por (pif fn2 (plift qf)) (por (pif ar2 (plift qx)) (plift q2)))(length H2) (length HX))
        (por (plift ef) (por (plift ex) (por (plift e2) (por (pif e2f (plift qf)) (pif e2x (plift qx))))))
            (splice_pl (por (plift ef) (por (plift ex)(por (plift e2) (por (pif e2f (plift qf)) (pif e2x (plift qx))))))(length H2) (length HX))
       .
Proof.  
  intros. 
  destruct IEF as [IEF1 [IEF2 [SC1 [STF1 [ST1 [SEF1 [SEF2 [HVF [HQF1 HQF2]]]]]]]]].
  destruct IEX as [IEX1 [IEX2 [SC2 [STF2 [ST2 [SEF3 [SEF4 [HVX [HQX1 HQX2]]]]]]]]].

  assert (telescope G). eapply envt_telescope. eapply envt_convert'; eauto. 

  remember HVF as HVF'. clear HeqHVF'.
  destruct vf1; destruct vf2; try solve [inversion HVF]; simpl in HVF; intuition.
  apply valt_wf in HVF' as WFQF. apply valt_wf in HVX as WFQX.
  rename H14 into HVF.
  
  destruct (HVF S1'' S2'' M'' vx1 vx2) as [S1''' [S2''' [M''' [vy1 [vy2 [IEY1 [IEY2 [SC3 [STF3 [ST3 [SEF5 [SEF6 [HVY [HQY1 HQY2]]]]]]]]]]]]]]; eauto.
   
  eapply stchain_tighten. eapply valt_filter; eauto. eauto. eapply H12. eapply H12.
  
  (* SEPARATION / OVERLAP *)
  (* 1st *)
  intros ? ?.

  destruct fn1. { (* arg may overlap with function? *)
    destruct fr1. { (* arg may be fresh? *)
      (* fn, fr: anything goes *)
      edestruct val_locs_stty_decide. destruct ST2; eauto. left. simpl.  eauto. 
      right. left. eauto.
    } {
      (* fn, not fr *) 
      destruct HSEP as [SEP | [SEP | SEP]]. { (* fn *)
        destruct SEP as (? & ? & ? & A). subst f frx.
        destruct IEF1 as [? IEF1]. assert (S x2 > x2) as P. lia. specialize (IEF1 (S x2) P).
        simpl in IEF1. inversion IEF1.
        destruct (HQX1 x0) as [Hq | Hfr]. eauto. 2: { unfoldq. intuition. }
        left. simpl. eapply lls_vars in Hq. destruct Hq as (? & (? & B) & ?).
        eapply lls_var in H18. destruct H18 as (? & ? & ?).
        eapply A in B. unfoldq. congruence. 
      } { (* fn 2, value *)
        destruct SEP as (? & ? & ? & ? & A). subst f frx.
        destruct IEF1 as [? IEF1]. assert (S x3 > x3) as P. lia. specialize (IEF1 (S x3) P).
        simpl in IEF1. inversion IEF1. 
        destruct (HQX1 x0) as [Hq | Hfr]. eauto. 2: { unfoldq. intuition. }
        subst. left. simpl. eapply lls_vars in Hq. destruct Hq as (? & (? & B) & ?).
        rewrite val_locs_abs. 
        eapply A in B. eapply lls_vars'. eauto. eauto. 
      } { (* q1 *)
        destruct SEP. subst frx.
        right. right. 
        eapply valq_sub with (q':=plift q1) (fr':=false) in HQX1.
        destruct (HQX1 x0) as [Hq | Hfr]. eauto. 2: contradiction.
        eapply lls_vars in Hq. destruct Hq as (? & ? & ?). eapply lls_vars'. eauto. unfoldq. intuition. 
        unfoldq; intuition. eauto.
      }
    }
  } {
    right. destruct fr1. {
      (* not fn, fr *) 
      edestruct val_locs_stty_decide. destruct ST2; eauto. { (* check to see if we're aliasing function *)
        right. eapply overlapping_splice. 6: eapply HVF'. 3: eauto. 3: eauto. 3: eauto. 2: eauto. eapply WFE. eauto. eauto. eauto. eauto.
        eapply valt_wf; eauto. eapply valt_wf; eauto. auto.
        
        intros ? [? ?]. eapply HSEP. split.
        rewrite plift_vt. eapply vt_mono. 2: eapply H15. unfoldq. intuition. eauto. 
        rewrite plift_vt. eapply vt_mono. 2: eapply H16. unfoldq. intuition. eauto.
        eapply valt_deep_wf; eauto. eapply valt_deep_wf; eauto.
        unfoldq. intuition eauto.
      }{ 
        left. eauto.
      }
    } {
      (* not fn, not fr *)
      right. destruct HSEP as [? HSEP]. subst frx.
      eapply valq_sub with (q':=plift q1) (fr':=false) in HQX1.
      destruct (HQX1 x0) as [Hq | Hfr]. eauto. 2: contradiction.
      eapply lls_vars in Hq. destruct Hq as (? & ? & ?). eapply lls_vars'. eauto. unfoldq. intuition.
      unfoldq; intuition. eauto. 
    }
  }

  (* 2nd *)
  intros ? ?.

  destruct fn1. { (* arg may overlap with function? *)
    destruct fr1. { (* arg may be fresh? *)
      (* fn, fr: anything goes *)
      edestruct val_locs_stty_decide. destruct ST2 as [? [A ?]]. eapply A. left. simpl.  eauto. 
      right. left. eauto.
    } {
      (* fn, not fr *) 
      destruct HSEP as [SEP | [SEP | SEP]]. { (* fn *)
        destruct SEP as (? & ? & ? & A). subst f frx.
        destruct IEF2 as [? IEF2]. assert (S x2 > x2) as P. lia. specialize (IEF2 (S x2) P).
        simpl in IEF2. inversion IEF2.
        destruct (HQX2 x0) as [Hq | Hfr]. eauto. 2: { unfoldq. intuition. }
        left. simpl. eapply lls_vars in Hq. destruct Hq as (? & (? & B) & ?).
        eapply lls_var in H18. destruct H18 as (? & ? & ?).
        eapply splice_psub in A.
        eapply A in B. unfold splice_pl in *. bdestruct (x1 <? length H2); intuition.  unfoldq.  congruence.
        unfoldq; intuition. unfoldq; intuition. unfoldq. assert (x3 = x1 + length HX). { lia. } subst x3.
        congruence.
      } { (* fn 2, value *)
        destruct SEP as (? & ? & ? & ? & A). subst f frx.
        destruct IEF2 as [? IEF2]. assert (S x3 > x3) as P. lia. specialize (IEF2 (S x3) P).
        simpl in IEF2. inversion IEF2. 
        destruct (HQX2 x0) as [Hq | Hfr]. eauto. 2: { unfoldq. intuition. }
        subst. left. simpl. eapply lls_vars in Hq. destruct Hq as (? & (? & B) & ?).
        rewrite val_locs_abs.
        eapply splice_psub in A. 
        eapply A in B.  eapply lls_vars'. eauto. rewrite plift_splice. auto.
      } { (* q1 *)
        destruct SEP. subst frx.
        right. right. 
        eapply valq_sub with (q':=plift q1) (fr':=false) in HQX1.
        destruct (HQX2 x0) as [Hq | Hfr]. eauto. 2: contradiction. rewrite plift_splice.
        eapply lls_vars in Hq. destruct Hq as (? & ? & ?). eapply lls_vars'. eauto. 
        eapply splice_psub with (m := (length H2))(n := (length HX)) in H15 as H15'.   unfoldq. intuition.
        unfoldq; intuition.  eauto. 
      }
    }
  } {
    right. destruct fr1. {
      (* not fn, fr *) 
      edestruct val_locs_stty_decide. destruct ST2 as [? [X ?]]. eapply X.  { (* check to see if we're aliasing function *)
        right. rewrite plift_splice. eapply overlapping_splice. 6: eapply HVF'. 3: eauto. 3: eauto. 3: eauto. 2: eauto. eapply WFE. eauto. eauto. eauto. eauto.
        eapply valt_wf; eauto. eapply valt_wf; eauto. auto.
        
        intros ? [? ?]. eapply HSEP. split.
        rewrite plift_vt. eapply vt_mono. 2: eapply H15. unfoldq. intuition. eauto. 
        rewrite plift_vt. eapply vt_mono. 2: eapply H16. unfoldq. intuition. eauto.
        eapply valt_deep_wf; eauto. eapply valt_deep_wf; eauto.
        unfoldq. intuition eauto.
      }{ 
        left. eauto.
      }
    } {
      (* not fn, not fr *)
      right. destruct HSEP as [? HSEP]. subst frx.
      eapply valq_sub with (q':=(splice_pl (plift q1)(length H2)(length HX))) (fr':=false) in HQX2.
      destruct (HQX2 x0) as [Hq | Hfr]. eauto. 2: contradiction.
      eapply lls_vars in Hq. destruct Hq as (? & ? & ?). eapply lls_vars'. eauto. rewrite plift_splice. eauto. 
      eapply splice_psub with (m:= length H2) (n := length HX) in HSEP. unfoldq. intuition.
      rewrite plift_splice in *; auto.
    }
  }

  (* EVALUATION *)
  exists S1''', S2''', M''', vy1, vy2. 
  split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 8: split. 9: split.
  + (* expression evaluates *)
    (* - initial fuel value *)
    destruct IEF1 as [n1 IEF1].
    destruct IEX1 as [n2 IEX1].
    destruct IEY1 as [n3 IEY1].
    exists (S (n1+n2+n3)).
    (* - forall greater fuel *)
    intros. destruct n. lia.
    (* - result computes *)
    simpl. rewrite IEF1. rewrite IEX1. rewrite IEY1.
    repeat rewrite app_assoc. repeat rewrite app_nil_r. eauto.
    all: lia.

  + (* expression evaluates *)
    (* - initial fuel value *)
    destruct IEF2 as [n1 IEF2].
    destruct IEX2 as [n2 IEX2].
    destruct IEY2 as [n3 IEY2].
    exists (S (n1+n2+n3)).
    (* - forall greater fuel *)
    intros. destruct n. lia.
    (* - result computes *)
    simpl. rewrite IEF2. rewrite IEX2. rewrite IEY2.
    repeat rewrite app_assoc. repeat rewrite app_nil_r. eauto.
    all: lia.

  + eapply st_trans. eapply st_trans. eauto. eauto. eauto. 

  + eauto.
      
  (* STORE_TYPE *)
  + eauto.
  
  + (* store preservation 1 *)  

    assert (length1 M <= length1 M') as L1. eapply st_mono1 in SC1. auto.
    assert (st_chain M M'') as SCC. eapply st_trans. eauto. eauto.

    assert (length1 M' <= length1 M'') as L2. eapply st_mono1 in SC2. auto.
    intros ? ? PV. intros IS. rewrite SEF5; eauto. intros ?. eapply PV.
    assert (l1 < length1 M). apply indexr_var_some' in IS. destruct ST as ((L & ?) & ?). unfold length1. lia.
    destruct H13 as [EE2 | [E2X | E2F]]. {
      erewrite lls_change. 
      eapply lls_mono; eauto. eapply vars_locs_mono; eauto. unfoldq; intuition.

      eapply stchain_tighten. eapply envt1_filter_deep; eauto. unfoldq; intuition.
      eauto.
      eapply envt1_store_deep_wf1; eauto. unfoldq; intuition.
      eapply envt1_store_deep_wf2; eauto. unfoldq; intuition.

    } {
      destruct e2x; simpl in E2X.
      destruct (HQX1 l1). auto.
      erewrite lls_change. 
      eapply lls_mono; eauto. eapply vars_locs_mono; eauto. unfoldq; intuition.

      eapply stchain_tighten. eapply envt1_filter_deep; eauto. unfoldq; intuition.
      eauto. 
      eapply envt1_store_deep_wf1; eauto. unfoldq; intuition.
      eapply envt1_store_deep_wf2; eauto. unfoldq; intuition.

      destruct frx; unfold pnot, pdom in H13. destruct H13. 
      eapply st_mono1 in SC1. unfold length1, pnat in *. lia.
      contradiction. contradiction.
    } {
      destruct e2f; simpl in E2F.
      destruct (HQF1 l1). erewrite lls_change; eauto. eapply stchain_tighten. eapply valt_filter. eauto. eauto.
      eapply valt_deep_wf; eauto. eapply valt_deep_wf; eauto.
      erewrite lls_change; eauto.
      eapply lls_mono; eauto. eapply vars_locs_mono; eauto. unfoldq; intuition.
      eapply stchain_tighten. eapply envt1_filter_deep; eauto. unfoldq; intuition. eauto.
      eapply envt1_store_deep_wf1; eauto. unfoldq; intuition.
      eapply envt1_store_deep_wf2; eauto. unfoldq; intuition.
      destruct frf; simpl in H13. unfold pnot, pdom in H13. destruct H13. unfold length1, pnat in *. lia.
      contradiction. contradiction.
    }
    rewrite SEF3; eauto. intros ?. eapply PV.
    erewrite lls_change. eapply lls_mono; eauto. eapply vars_locs_mono; eauto. unfoldq; intuition.
    eapply stchain_tighten; eauto. eapply envt1_filter_deep; eauto. unfoldq; intuition.
    eapply envt1_store_deep_wf1; eauto. unfoldq; intuition.
    eapply envt1_store_deep_wf2; eauto. unfoldq; intuition.

    rewrite SEF1; eauto. intros ?. eapply PV.
    eapply lls_mono; eauto. eapply vars_locs_mono; eauto. unfoldq; intuition.

  + (* store preservation 2 *)  
  assert (length2 M <= length2 M') as L1. eapply st_mono2 in SC1. auto.
  assert (st_chain M M'') as SCC. eapply st_trans. eauto. eauto.
    
  assert (length2 M' <= length2 M'') as L2. eapply st_mono2 in SC2. auto.
  intros ? ? PV. intros IS. rewrite SEF6; eauto. intros ?. eapply PV.
  assert (l1 < length2 M). apply indexr_var_some' in IS. destruct ST as (? & (L & ?) & ?). unfold length2. lia.
  destruct H13 as [EE2 | [E2X | E2F]]. {
    rewrite plift_splice in EE2.
    erewrite lls_change. 
    eapply lls_mono; eauto. eapply vars_locs_mono; eauto. repeat rewrite splice_por. unfoldq; intuition.
    eapply splice_psub in E2; eauto.
    
    eapply stchain_tighten. rewrite <- splice_pand. eapply envt1_filter_deep; eauto. unfoldq; intuition.
    eauto.
    eapply envt1_store_deep_wf1; eauto. unfoldq; intuition.
    rewrite <- splice_pand. eapply envt1_store_deep_wf2; eauto. unfoldq; intuition.
    
  } {
    destruct e2x; simpl in E2X.
    destruct (HQX2 l1). auto.
    erewrite lls_change. 
    eapply lls_mono; eauto. eapply vars_locs_mono; eauto. repeat rewrite splice_por. unfoldq; intuition.
    
    eapply stchain_tighten. rewrite <- splice_pand.  eapply envt1_filter_deep; eauto. unfoldq; intuition.
    eauto. 
    eapply envt1_store_deep_wf1; eauto. unfoldq; intuition.
    rewrite <- splice_pand. eapply envt1_store_deep_wf2; eauto. unfoldq; intuition.
    
    destruct frx; unfold pnot, pdom in H13. destruct H13. 
    eapply st_mono2 in SC2. unfold length2, pnat in *. lia.
    contradiction. contradiction.
  } {
    destruct e2f; simpl in E2F.
    destruct (HQF2 l1). erewrite lls_change; eauto. eapply stchain_tighten. eapply valt_filter. eauto. eauto.
    eapply valt_deep_wf; eauto. eapply valt_deep_wf; eauto.
    erewrite lls_change; eauto.
    eapply lls_mono; eauto.  eapply vars_locs_mono; eauto.
    {
    intros ? [? ?]. split; auto. repeat rewrite splice_por. right. right. right. left. auto. 
    } 
    eapply stchain_tighten. rewrite <- splice_pand.  eapply envt1_filter_deep; eauto. unfoldq; intuition. eauto.
    eapply envt1_store_deep_wf1; eauto. unfoldq; intuition.
    rewrite <- splice_pand. eapply envt1_store_deep_wf2; eauto. unfoldq; intuition.
    destruct frf; simpl in H13. unfold pnot, pdom in H13. destruct H13. unfold length2, pnat in *. lia.
    contradiction. contradiction.
  }
  rewrite SEF4; eauto. intros ?. eapply PV.
  erewrite lls_change. eapply lls_mono; eauto. eapply vars_locs_mono; eauto. 
  { 
    intros ? [? ?]. split; auto. repeat rewrite splice_por. right. left. auto.
  }  
  
  eapply stchain_tighten; eauto. rewrite <- splice_pand. eapply envt1_filter_deep; eauto. unfoldq; intuition.
  eapply envt1_store_deep_wf1; eauto. unfoldq; intuition.
  rewrite <- splice_pand.
  eapply envt1_store_deep_wf2; eauto. unfoldq; intuition.
  
  rewrite SEF2; eauto. intros ?. eapply PV.
  eapply lls_mono; eauto. eapply vars_locs_mono; eauto. 
  {
    intros ? [? ?]. split; auto. repeat rewrite splice_por. left. auto.
  }
  

  (* VAL_TYPE *)
  + eapply HVY.

  (* VAL_QUAL 1 *)
  + remember (vabs l q t) as vf.
    assert (val_qual (st1 M) (st1 M''') H1 vf frf (pand (plift p) (plift qf))) as HQF'. {
      eapply envt1_valq_store_change1. 3: eauto. eapply envt1_store_extend. eauto. eauto. eauto. eauto. eauto. eapply st_trans; eauto.  }
    assert (val_qual (st1 M') (st1 M''') H1 vx1 frx (pand (plift p) (plift qx))) as HQX'. {
      eapply envt1_valq_store_change1. 3: eauto. eapply envt1_store_extend. eauto. eauto. eapply st_trans; eauto. eauto. eauto. eauto. }
    
    intros ? ?. unfoldq.
    destruct (HQY1 x0) as [HY_q | [HY_f | [HY_x | HY_fr]]].
    repeat rewrite app_length. intuition.
    * (* q2, and part of function *)
      destruct HY_q as [? ?].
      left. eapply lls_mono. eapply vars_locs_mono. 2: eauto.
      intros ? ?. intuition. 
    * (* part of function *)
      destruct fn2. 2: contradiction.
      destruct (HQF' x0) as [HF_q | HF_fr]. eauto. 
      -- (* q *) left. eapply lls_mono. 2: eauto. eapply vars_locs_mono. unfoldq. intuition.
      -- (* fr *) 
         destruct frf. 2: contradiction.
         right. simpl. auto.  
    * (* part of arg *)
      destruct ar2. 2: contradiction.
      destruct (HQX' x0) as [HX_q | HX_fr]. eauto.
      -- (* q *) left. eapply lls_mono. 2: eauto. eapply vars_locs_mono. unfoldq. intuition. 
      -- (* fr *)
         destruct frx. 2: contradiction.
         right. simpl.  destruct (fn2 && frf); simpl. 
         intros ?. eapply HX_fr. eapply SC1. eauto. 
         intros ?. eapply HX_fr. eapply SC1. eauto. 
    * (* fresh *)
      destruct fr2. 2: contradiction.
      right. simpl. 
      destruct (fn2 && frf || ar2 && frx); simpl.
      intros ?. eapply HY_fr. eapply SC2. eapply SC1. eauto.   
      intros ?. eapply HY_fr. eapply SC2. eapply SC1. eauto.

  (* VAL_QUAL 2 *)
  + remember (vabs l0 q0 t0) as vf.
    assert (val_qual (st2 M) (st2 M''') (H2'++HX++H2) vf frf (splice_pl (pand (plift p) (plift qf)) (length H2)(length HX))) as HQF'. {
      eapply envt1_valq_store_change2. 3: eapply HVF'. eapply envt1_store_extend; eauto. eauto. rewrite splice_pand. eauto. eapply st_trans; eauto.  }
    assert (val_qual (st2 M') (st2 M''') (H2'++HX++H2) vx2 frx (splice_pl (pand (plift p) (plift qx)) (length H2)(length HX))) as HQX'. {
      eapply envt1_valq_store_change2. 3: eauto. eapply envt1_store_extend; eauto. eapply st_trans; eauto. eauto. rewrite splice_pand. eauto. eauto. }
    
    intros ? ?. repeat rewrite splice_por.   
    destruct (HQY2 x0) as [HY_q | [HY_f | [HY_x | HY_fr]]].
    repeat rewrite app_length. intuition.
    * (* q2, and part of function *)
      destruct HY_q as [? ?].
      left. eapply lls_mono. eapply vars_locs_mono. 2: eauto.
      rewrite plift_splice  in *. 
      intros ? ?; split. eapply splice_psub in Q3. eapply Q3 in H16. eauto.
      right. right. auto.
      
    * (* part of function *)
      destruct fn2. 2: contradiction.
      destruct (HQF' x0) as [HF_q | HF_fr]. eauto. 
      -- (* q *) left. eapply lls_mono. 2: eauto. eapply vars_locs_mono. rewrite splice_pand.
         intros ? [? ?]; split; auto. left. auto.
      -- (* fr *) 
         destruct frf. 2: contradiction.
         right. simpl. auto. 
    * (* part of arg *)
      destruct ar2. 2: contradiction.
      destruct (HQX' x0) as [HX_q | HX_fr]. eauto.
      -- (* q *) left. eapply lls_mono. 2: eauto. eapply vars_locs_mono. 
      rewrite splice_pand. intros ? [? ?]. split; auto. right. left. auto.
      -- (* fr *)
         destruct frx. 2: contradiction.
         right. simpl. destruct (fn2 && frf); simpl. 
         intros ?. eapply HX_fr. eapply SC1. eauto. 
         intros ?. eapply HX_fr. eapply SC1. eauto. 
    * (* fresh *)
      destruct fr2. 2: contradiction.
      right. simpl.
      destruct (fn2 && frf || ar2 && frx); simpl.
      intros ?. eapply HY_fr. eapply SC2. eapply SC1. eauto.   
      intros ?. eapply HY_fr. eapply SC2. eapply SC1. eauto.   
Qed.  

Lemma pif_true: forall p,
  pif true p = p.
Proof.
  intros. eapply functional_extensionality. intros. simpl. auto.
Qed.

Lemma pif_false: forall p,
  pif false p = pempty.
Proof.
  intros. eapply functional_extensionality. intros. simpl. auto.
Qed.

Lemma pand_empty_r: forall p,
  pand p pempty = pempty.
Proof.
  intros. eapply functional_extensionality. intros. eapply propositional_extensionality. split; intros; unfoldq; intuition. 
Qed.

Lemma lls_empty: forall M,
  locs_locs_stty M pempty = pempty.
Proof.
  intros. eapply functional_extensionality. intros.
  eapply propositional_extensionality. 
  bdestruct (qempty x); intuition.  lia.
  inversion H0. unfoldq; intuition. subst. unfoldq; intuition. 
  Unshelve. apply 0. 
Qed.

Lemma bi_tabs_splice: forall H1 H2 H2' HX S1 S2 M G t1 T1 T2 p q2 qf e2 fr2 ar2 e2x e2f fr1 q1 fn1 fn2
  (WFE: env_type1 M H1 H2 H2' HX G p)
  (ST: store_type S1 S2 M)
  (SF: st_filter M (st_locs1 M)(st_locs2 M))
  (EXP:  forall S1' S2' M' vx1 vx2,
      val_type M' H1 (H2'++HX++H2) vx1 vx2 T1 (splice_ty T1 (length H2)(length HX)) ->
      env_type  M' (vx1::H1) (vx2::H2' ++ H2) ((T1, fr1, (qand p (qor q1 (qif fn1 qf))))::G) (por (pand (plift p) (plift qf))(pone (length G))) ->
      st_filter M' (st_locs1 M')(st_locs2 M') ->
      store_type S1' S2'  M' ->
      exists S1'' S2'' M'' v1 v2,
        exp_type1 S1' S2' M' (vx1:: H1) ((vx2:: H2')++HX++H2)  t1 (splice_tm t1 (length H2)(length HX)) S1'' S2'' M'' v1 v2 
        T2  (splice_ty T2 (length H2)(length HX))
        (por (pand (plift p) (plift qf)) (pone (length G))) (splice_pl (por (pand (plift p) (plift qf)) (pone (length G))) (length H2) (length HX)) 
        fr2 fr2
        (por (plift q2) (por (pif ar2 (pone (length G))) (pif fn2 (pand (plift p) (plift qf)))))
          (splice_pl (por (plift q2) (por (pif ar2 (pone (length G))) (pif fn2 (pand (plift p) (plift qf))))) (length H2) (length HX))
        (por (plift e2)(por (pif e2x (pone (length G))) (pif e2f (pand (plift p) (plift qf))))) 
        (splice_pl (por (plift e2) (por (pif e2x (pone (length G))) (pif e2f (pand (plift p) (plift qf)))))(length H2) (length HX))
         
  )
  (T1CL: closed_ty (length G) T1)
  (T2CL: closed_ty (length G) T2)
  (HQ2: (psub (plift q2) (pdom G)))
  (HE2: (psub (plift e2) (pdom G)))
  (HCLQF: closed_ql (length G) qf)
  (SUB: psub (plift q1) (pand (plift p) (plift qf))), 
  exists S1'' S2'' M'' v1'' v2'',
  exp_type1 S1 S2 M H1 (H2'++HX++H2) 
      (tabs (qand p qf) t1) (splice_tm (tabs (qand p qf) t1) (length H2) (length HX))
      S1'' S2'' M''  v1'' v2'' 
      (TFun T1 fn1 fr1 q1 T2 fn2 ar2 fr2 q2 e2f e2x e2) (splice_ty (TFun T1 fn1 fr1 q1 T2 fn2 ar2 fr2 q2 e2f e2x e2) (length H2)(length HX))
      (plift p) (splice_pl (plift p) (length H2) (length HX)) 
      false false
      (plift qf) (splice_pl (plift qf) (length H2)(length HX)) 
      pempty pempty.
Proof.  
  intros. 
  apply wf_envt1 in WFE as WFE'. 
  destruct WFE' as [L1 [L2 [P1 [P2 [P3 P4]]]]].
  remember ST as ST'. clear HeqST'.
  destruct ST as [SL1 [SL2 [SP1 [SP2 SP3]]]].

  exists S1, S2, M.
  exists (vabs H1 (qand p qf) t1). 
  exists (vabs (H2' ++ HX ++ H2) (splice_ql (qand p qf) (length H2) (length HX)) (splice_tm t1 (length H2) (length HX))).
  split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 8: split. 9: split.
  
  - (* 1st *)
    exists 1.  intros. destruct n. lia. simpl. eauto.
  
  - (* 2nd *)
    exists 1.  intros. destruct n. lia. simpl. auto.
  
  - eapply st_refl. auto.
  - auto.
  - auto.
  - intros ? ? ? ?. eauto.
  - intros ? ? ? ?. eauto.
  
  - (* results *)
   repeat split.
   rewrite L1. auto.
   unfoldq; intuition. eapply SUB in H. unfoldq; intuition.
   rewrite L1. auto.
   unfoldq; intuition. eapply HQ2 in H. lia.
   unfoldq; intuition. eapply HE2 in H. lia.
   eapply closedty_splice; eauto. rewrite L2. auto.
   rewrite plift_splice. eapply pdom_slice'; eauto. unfoldq; intuition. eapply SUB in H. destruct H. eapply P3 in H. lia.
   eapply closedty_splice; eauto. rewrite L2. auto.
   rewrite plift_splice. eapply pdom_slice'; eauto. unfoldq; intuition. eapply HQ2 in H. lia. 
   rewrite plift_splice. eapply pdom_slice'; eauto. unfoldq; intuition. eapply HE2 in H. lia. 
   
   rewrite val_locs_abs. 
   eapply envt1_store_deep_wf1. eapply WFE. rewrite plift_and. unfoldq; intuition.
   rewrite val_locs_abs. rewrite plift_splice. 
   eapply envt1_store_deep_wf2. eauto. rewrite plift_and. unfoldq; intuition.

   
   (* strel same locs *)
   
   rewrite val_locs_abs, val_locs_abs. rewrite plift_splice. edestruct envt1_same_locs; eauto. rewrite plift_and. 
   unfoldq; intuition.
   
   rewrite val_locs_abs, val_locs_abs. rewrite plift_splice. edestruct envt1_same_locs; eauto.
   rewrite plift_and. unfoldq; intuition. 
   
   intros.
      
   repeat rewrite val_locs_abs in H. 
   rewrite plift_splice, plift_and in H.
   rewrite val_locs_abs in H5, H6.
   rewrite plift_splice in H6. 
   rewrite plift_and in H5, H6. 
   assert (env_type1  M'
            (vx1 :: H1) H2 (vx2 :: H2') HX ((T1, fr1, (qand p (qor q1 (qif fn1 qf)))) :: G)
            (qor (qand p qf) (qone (length G)))) as WFE'. {
 
   eapply envt1_extend_full in WFE; eauto.
   - eapply stchain_tighten; eauto. eapply envt1_filter_deep; eauto. unfoldq; intuition.
     rewrite plift_and. eapply lls_mono. eapply vars_locs_mono; eauto. unfoldq; intuition.
     rewrite plift_and. eapply lls_mono. eapply vars_locs_mono; eauto. rewrite splice_pand. unfoldq; intuition.
   - intros ? [? ?]. rewrite plift_and. destruct (H5 x) as [F | [L | Q]]. auto. {
       destruct fn1. 2: contradiction.
       rewrite plift_or, plift_if. eapply lls_mono. 2: eapply F. eapply vars_locs_mono; eauto. unfoldq; intuition.
      }{
        destruct fr1. 2: contradiction. destruct L. rewrite plift_and in H7. eauto.
      }{
        rewrite plift_and in H7. rewrite plift_or, plift_if. 
        eapply lls_mono. 2: eapply Q. eapply vars_locs_mono; eauto. unfoldq; intuition. eapply SUB; eauto.
      }
   - repeat rewrite plift_and. rewrite plift_or, plift_if. 
     intros ? [? ?]. destruct (H6 x) as [F | [L | Q]]. auto. {
      destruct fn1. 2: contradiction.
      eapply lls_mono. 2: eapply F. eapply vars_locs_mono; eauto. rewrite pand_or_distribute. rewrite splice_por.
      unfoldq; intuition.
     }{
       destruct fr1. 2: contradiction. destruct L. eauto.
     }{
       rewrite plift_splice in Q. 
       eapply lls_mono. 2: eapply Q. eapply vars_locs_mono; eauto. intros ? ?. 
       eapply splice_psub in SUB. eapply SUB in H9 as H9'. rewrite pand_or_distribute. rewrite splice_por. rewrite splice_pand in *.
       left.  unfoldq; intuition. 
     }
   - intros. rewrite plift_and, plift_or in *. 
     subst fr1. intros ? ?. eapply H5 in H7.
     destruct H7 as [ A | [B | C]]. {
     destruct fn1. 2: contradiction.
     simpl in A. eapply lls_mono. 2: eauto. eapply vars_locs_mono. 
     unfoldq. intuition.
     } {
       contradiction.
     } {
       eapply lls_mono. 2: eauto. eapply vars_locs_mono. 
       unfoldq. intuition. eapply SUB; eauto.
     }
   - intros. rewrite plift_and in *. rewrite plift_or in *. 
     subst fr1. intros ? ?. eapply H6 in H7.
     destruct H7 as [ A | [B | C]]. {
       destruct fn1. 2: contradiction.
       simpl in A. eapply lls_mono. 2: eauto. eapply vars_locs_mono.
       repeat rewrite splice_pand. rewrite splice_por. unfoldq; intuition.
     } {
       contradiction.
     } {
       eapply lls_mono. 2: eauto. eapply vars_locs_mono. rewrite plift_splice.
       intros ? ?. 
       eapply splice_psub in SUB. eapply SUB in H7 as H7'. rewrite pand_or_distribute. rewrite splice_por. rewrite splice_pand in *.
       left.  unfoldq; intuition.
     }
   - rewrite plift_and. unfoldq; intuition.
   - repeat rewrite plift_and. rewrite plift_or. unfoldq; intuition. eapply SUB; eauto. rewrite plift_if in H7. destruct fn1; try contradiction. intuition.
   - eapply closedq_and. left. rewrite <- L1. eapply P3.
   
  }
      
   
   destruct (EXP S1' S2' M' vx1 vx2 H4) as [S1'' [S2'' [M'' [vy1 [vy2 IEY]]]]]; intuition. 
   eapply envt_convert' in WFE'. rewrite plift_or, plift_one, plift_and in WFE'. auto.
   
      
   destruct IEY as [IEY1 [IEY2 [STC2 [STF2 [ST2 [SEFY1 [SEFY2 [IVY [IYQ1 IYQ2 ]]]]]]]]].
   
   
   exists S1'', S2'', M'', vy1, vy2. intuition.

   (* store preserve *)
   rewrite val_locs_abs. rewrite plift_and in *.
   intros ? ? PV ?. eapply SEFY1. intros VL. eapply PV.
   repeat rewrite pand_or_distribute in VL. repeat  rewrite lls_vars_or in VL.
   destruct VL as [? | [? | ?]].
   left. replace (vx1::H1) with ([vx1]++H1) in H8. 2: { auto. }
   rewrite vars_locs_extend in H8. eapply lls_mono. 2: eapply H8. eapply vars_locs_mono. unfoldq; intuition.
   unfoldq; intuition. eapply HE2 in H14. lia. 
   destruct e2x; simpl in H8. right. left. eapply lls_mono. 2: eapply H8. intros ? ?.
   destruct H9 as [? [[? ?] ?]]. simpl in H10. unfold pone in H10. subst x0. destruct H11 as [? [? ?]]. 
   rewrite <- L1 in H10. rewrite indexr_head in H10. inversion H10. subst. auto. 
   rewrite pif_false in H8. rewrite pand_empty_r in H8. rewrite vars_locs_empty in H8. rewrite lls_empty in H8. unfoldq; intuition.
   right. right. replace (vx1::H1) with ([vx1]++H1) in H8. 2: { auto. } rewrite vars_locs_extend in H8.
   destruct e2f; simpl in H8. eapply lls_mono. 2: eapply H8. eapply vars_locs_mono; eauto. unfoldq; intuition.
   rewrite pif_false in H8. rewrite pand_empty_r in H8. rewrite vars_locs_empty in H8. rewrite lls_empty in H8. unfoldq; intuition.
   unfoldq; intuition. destruct e2f; simpl in *; intuition.
   auto.

   (* store preserve *)
  
   rewrite val_locs_abs. repeat rewrite plift_splice in *. repeat rewrite plift_and in *.
   intros ? ? PV ?. eapply SEFY2. intros VL. eapply PV.
   repeat rewrite splice_por in VL. 
   repeat rewrite pand_or_distribute in VL. repeat  rewrite lls_vars_or in VL.
   destruct VL as [? | [? | ?]]. simpl in H8.
   left. replace (vx2::H2'++HX++H2) with ([vx2]++H2'++HX++H2) in H8. 2: { auto. }
   rewrite vars_locs_extend in H8. eapply lls_mono. 2: eapply H8. eapply vars_locs_mono. unfoldq; intuition.
   rewrite <- splice_por. rewrite <- splice_pand.
   eapply pdom_slice'; eauto. unfoldq; intuition. eapply P3 in H13. lia.
   eapply HE2 in H14. lia.
   
   destruct e2x; simpl in H8. right. left. eapply lls_mono. 2: eapply H8. intros ? ?.
   destruct H9 as [? [[? ?] ?]]. simpl in H10. destruct H11 as [? [? ?]].
   destruct H10 as [[? ?] | ?]. simpl in H13. unfold pone in H13. rewrite app_length in *. lia.
   destruct H10. simpl in H13. unfold pone in H13. assert (x0 = length (H2' ++ HX ++H2)). { repeat rewrite app_length in *. lia. }
   subst x0. rewrite indexr_head in H11. inversion H11. subst. auto. 
   rewrite pif_false in H8. rewrite splicep_empty in H8. rewrite pand_empty_r in H8. rewrite vars_locs_empty in H8. rewrite lls_empty in H8. unfoldq; intuition.
   right. right. simpl in H8. replace (vx2::H2'++HX++H2) with ([vx2]++H2'++HX++H2) in H8. 2: { auto. } rewrite vars_locs_extend in H8.
   destruct e2f; simpl in H8. eapply lls_mono. 2: eapply H8. eapply vars_locs_mono; eauto. unfoldq; intuition.
   rewrite pif_false in H8. rewrite splicep_empty in H8. rewrite pand_empty_r in H8. rewrite vars_locs_empty in H8. rewrite lls_empty in H8. unfoldq; intuition.
   rewrite <- splice_por. rewrite <- splice_pand.
   eapply pdom_slice'; eauto. unfoldq; intuition. eapply P3 in H13. lia.
   destruct e2f; simpl in H14; try contradiction. destruct H14. eapply P3 in H13. lia.
   auto.
   
   rewrite <- P2 in HE2.
   eapply pdom_slice with (HX := HX) in HE2 . rewrite plift_splice in HE2. auto.
   
   eapply valt_extend1; eauto.
   rewrite L1. auto. 
   
   eapply closedty_splice. rewrite L2. auto.
   
  rewrite val_locs_abs in *. rename H4 into HVX;
  apply valt_wf in HVX; apply valt_wf in IVY.
   
   
  intros ? ?.
  destruct (IYQ1 x). eauto. 

  repeat rewrite pand_or_distribute in H7. repeat rewrite lls_vars_or in H7.
  replace (vx1::H1) with ([vx1]++H1) in H7. 2: { auto. }
  destruct H7 as [? | [?|  ?]].
  left. erewrite vars_locs_extend in H7. 2: { unfoldq; intuition. eapply HQ2 in H14. lia. }
  split. eapply lls_mono. 2: eapply H7. eapply vars_locs_mono; eauto. unfoldq; intuition.
  eapply lls_mono. 2: eapply H7. eapply vars_locs_mono; eauto. unfoldq; intuition. 1,2: rewrite plift_and; split; intuition.
  eapply HQ2 in H14. lia. eapply HQ2 in H14. lia.

  (* from arg *)
  right. right. left. destruct ar2; simpl in *.  eapply lls_mono. 2: eapply H7.
  intros ? ?. destruct H8 as [? [? ?]]. destruct H8 as [? ?]. simpl in H10. unfold pone in H10. 
  destruct H9 as [? [? ?]]. subst x1. rewrite <- L1 in H9. rewrite indexr_head in H9. inversion H9. subst. auto.
  rewrite pif_false in H7. rewrite pand_empty_r in H7. rewrite vars_locs_empty in H7. rewrite lls_empty in H7. unfoldq; intuition.

  (* from func *)
  right. left. 
  destruct fn2; simpl in *. replace (vx1::H1) with ([vx1]++H1) in H7. 2: { auto. }
  rewrite vars_locs_extend in H7. 2: { unfoldq; intuition. }
  eapply lls_mono. 2: eapply H7. eapply vars_locs_mono; eauto. rewrite plift_and. simpl. unfoldq; intuition.
  rewrite pif_false in H7. rewrite pand_empty_r in H7. rewrite vars_locs_empty in H7. rewrite lls_empty in H7. unfoldq; intuition.
  
  (* fr *)
  right. right. right.
  unfold length1. auto.

  (* 2nd *)
  rewrite val_locs_abs in *. rename H4 into HVX;
  apply valt_wf in HVX; apply valt_wf in IVY. 
  repeat rewrite plift_splice. repeat rewrite plift_and.
  intros ? ?.  
  destruct (IYQ2 x). intuition. simpl in H7. replace (vx2::H2'++HX++H2) with ([vx2]++H2'++HX++H2) in H7. 2: { simpl. auto. }
  repeat rewrite splice_por in H7. repeat rewrite splice_pand in *. 
  repeat rewrite pand_or_distribute in H7. repeat rewrite lls_vars_or in H7.
  destruct H7 as [? | [?| ?]].
  left. erewrite vars_locs_extend in H7. 
  2: { unfoldq; intuition. rewrite app_length in *. destruct H14 as [[? ?] | [? ?]]; destruct H12 as [[? ?] | [? ?]]; try lia. 
       eapply HQ2 in H14. lia. }
  split. eapply lls_mono. 2: eapply H7. eapply vars_locs_mono; eauto. unfoldq; intuition.
  eapply lls_mono. 2: eapply H7. eapply vars_locs_mono; eauto. eapply splice_psub in HQ2 as HQ2'. 
  unfoldq; intuition.  eapply HQ2' in H14. rewrite app_length in *.  destruct H14 as [[? ?] | ?]; destruct H12 as [[? ?] | ?]; try lia.
  rewrite app_length in *. destruct H14 as [[? ?] | ?]; destruct H12 as [[? ?] | ?]; try lia. destruct H13. eapply HQ2 in H14. lia.

  (* from arg *)
  right. right. left. destruct ar2; simpl in *. eapply lls_mono. 2: eapply H7. rewrite app_length in *.
  intros ? ?. destruct H8 as [? [? ?]]. destruct H8 as [? ?]. destruct H10 as [[? ?] | [? ?]]; simpl in H11; unfold pone in H11. lia.
  assert (x1 = length (H2'++HX++H2)). { repeat rewrite app_length. lia. } subst x1.    
  destruct H9 as [? [? ?]]. rewrite indexr_head in H9. inversion H9. subst. auto.
  rewrite pif_false in H7. rewrite splicep_empty in H7. rewrite pand_empty_r in H7. rewrite vars_locs_empty in H7. rewrite lls_empty in H7. unfoldq; intuition.
    
    
  (* from func *)
  right. left. 
  assert ((splice_pl (pone (length G))(length H2)(length HX)) = pone(length (H2'++HX++H2))) as N.
  eapply splicep_one; eauto. repeat rewrite app_length. rewrite <- L2. rewrite app_length. lia.
  repeat rewrite plift_splice in *. repeat rewrite plift_and, plift_one in *.
  rewrite N in *. replace (vx2::H2'++HX++H2) with ([vx2]++H2'++HX++H2) in H7. 2: { simpl. auto. }
  erewrite vars_locs_extend in H7. 
  2: { unfoldq; intuition. repeat rewrite app_length in *. destruct H14 as [[? ?] | [? ?]]. lia. 
      destruct fn2. 2: contradiction.  destruct H14. eapply P3 in H14. lia. }
  destruct fn2; simpl in *.
  eapply lls_mono. 2: eapply H7. eapply vars_locs_mono; eauto. intros ? [? ?]. unfold pif in H9. rewrite splice_pand in H9. auto.
  rewrite pif_false in H7. rewrite splicep_empty in H7. rewrite pand_empty_r in H7. rewrite vars_locs_empty in H7. rewrite lls_empty in H7. unfoldq; intuition.
    
  (* fresh *)
  right. right. right.
  destruct fr2; simpl in *. unfold length2. auto. contradiction.
   
 - eapply valq_abs; eauto.
 - rewrite splice_qand. 
    intros ? ?. rewrite val_locs_abs, plift_and, plift_splice, plift_splice in H. left. auto. 
Qed.

Lemma bi_tseq_splice: forall S1 S2 M H1 H2 H2' HX t1 t2 S1' S2' M' M'' S1'' S2'' v1 v2 v3 v4 p p1 p2 q1 q2 e1 e2 G 
 (WFE: env_type M H1 (H2' ++ H2) G (plift p))
 (ST: store_type S1 S2 M)
 (E1: exp_type1 S1 S2 M H1 (H2' ++ HX ++ H2) t1 (splice_tm t1 (length H2) (length HX)) S1' S2' M' v1 v2 
        TBool TBool 
        (plift p1) (splice_pl (plift p1) (length H2) (length HX))
        false false
        (plift q1) (splice_pl (plift q1) (length H2) (length HX))
        (plift e1) (splice_pl (plift e1) (length H2)(length HX)))
 (E2: exp_type1 S1' S2' M' H1 (H2' ++ HX ++ H2) t2 (splice_tm t2 (length H2) (length HX)) S1'' S2'' M'' v3 v4
        TBool TBool 
        (plift p2) (splice_pl (plift p2) (length H2) (length HX))
        false false
        (plift q2) (splice_pl (plift q2) (length H2) (length HX))
        (plift e2) (splice_pl (plift e2) (length H2) (length HX)))
 (SUB1: psub (plift p1) (plift p))
 (SUB2: psub (plift p2) (plift p)),
 exists S1'' S2'' M'' v5 v6,
  exp_type1 S1 S2 M H1 (H2' ++ HX ++ H2) (tseq t1 t2)
    (splice_tm (tseq t1 t2) (length H2) (length HX)) S1'' S2'' M'' v5 v6 
    TBool TBool 
    (plift p) (splice_pl (plift p) (length H2) (length HX)) 
    false false 
    pempty pempty
    (por (plift e1) (plift e2)) (splice_pl (por (plift e1) (plift e2)) (length H2) (length HX)).
Proof. 
  intros.
  assert (env_type M H1 (H2'++H2) G (plift p1)) as WFE1. { eapply envt_tighten; eauto. }
  
  destruct E1 as [IE1 [IE2 [SC1 [STF1 [ST1 [SE1 [SE2 [HV1 [HQ1 HQ2]]]]]]]]].
  destruct v1; destruct v2; try solve [inversion HV1]. simpl in HV1.
  destruct HV1 as [HT [LS1 [LS2 VT]]].
  remember ST1 as ST1'. clear HeqST1'.
  destruct ST1 as [STL1 [STL2 [SP1 [SP2 SP3]]]].

  eapply envt_store_extend in WFE as WFE'. 2: eapply ST. 2: eauto.
  assert (env_type M' H1 (H2'++H2) G (plift p2)) as WFE2. { eapply envt_tighten; eauto. }
  assert (env_type1 M H1 H2 H2' HX G p2) as WFE2'. { eapply envt_convert; eauto. eapply envt_tighten. eapply WFE. auto. }

  destruct E2 as [IE3 [IE4 [SC2 [STF2 [ST2 [SE3 [SE4 [HV2 [HQ3 HQ4]]]]]]]]].
  destruct v3; destruct v4; try solve [inversion HV2]. simpl in HV2.
  subst b0.
  remember ST2 as ST2'. clear HeqST2'.
  destruct ST2 as [STL3 [STL4 [SP4 [SP5 SP6]]]].
  
  exists S1'', S2''.
  exists M'', (vbool (b && b1)), (vbool (b && b1)).
  split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 8: split. 9: split.
  + (* first one *)
  destruct IE1 as [n1 IE1].
  destruct IE3 as [n3 IE3].
  exists (S(n1 + n3)). intros. destruct n. intuition.
  simpl. rewrite IE1. rewrite IE3. eauto. lia. lia.
  +
  destruct IE2 as [n2 IE2].
  destruct IE4 as [n4 IE4].
  exists (S(n2 + n4)). intros. destruct n. intuition.
  simpl. rewrite IE2. rewrite IE4. eauto. lia. lia. 

  + eapply st_trans; eauto.
  + eauto.
  + eauto.  
  + eapply se_trans; eapply se_sub; eauto. eapply lls_mono; eapply vars_locs_mono; eauto. unfoldq; intuition. 
  erewrite <- lls_change with (M := (st1 M)). eapply lls_mono; eapply vars_locs_mono; eauto. unfoldq; intuition.
  eapply stchain_tighten. eapply envt_filter_deep. eapply WFE. eauto. unfoldq; intuition. eauto.
  eapply envt_store_deep_wf. eapply WFE. unfoldq; intuition.
  eapply envt_store_deep_wf. eapply WFE. unfoldq; intuition.
  
  + eapply se_trans; eapply se_sub; eauto. eapply lls_mono; eapply vars_locs_mono; eauto. 
  rewrite splice_por. unfoldq; intuition. eapply splice_psub. 2: eapply H0. auto.
  erewrite <- lls_change with (M := (st2 M)). eapply lls_mono; eapply vars_locs_mono; eauto. 
  rewrite splice_por. unfoldq; intuition. eapply splice_psub. 2: eapply H0. auto.
  eapply stchain_tighten.  
  
  rewrite <- splice_pand.
  eapply envt1_filter_deep. eapply WFE2'. eauto. unfoldq; intuition. eauto.
  eapply envt_store_deep_wf. eapply WFE. unfoldq; intuition.
  rewrite <- splice_pand.
  eapply envt1_store_deep_wf2. eapply WFE2'. unfoldq; intuition. 
  
  + constructor.

  + eapply valq_bool. 
  + eapply valq_bool.
Qed.

Lemma bi_qsub_splice: forall S1 S2 S1' S2' M H1 H2 H2' HX t M' T p q1  q2 e1 e2  v1 v2 fr1 fr2 G
  (WFE: env_type M H1 (H2' ++ H2) G (plift p))
  (E: exp_type1 S1 S2 M H1 (H2'++HX++H2) t (splice_tm t (length H2)(length HX)) S1' S2' M' v1 v2 
      T (splice_ty T (length H2)(length HX)) 
      (plift p) (splice_pl (plift p)(length H2)(length HX)) 
      fr1 fr1 
      (plift q1) (splice_pl (plift q1) (length H2)(length HX)) 
      (plift e1) (splice_pl (plift e1) (length H2)(length HX))), 
  psub (plift q1) (plift q2) ->
  psub (plift q2) (pdom G) ->
  psub (plift e1) (plift e2) ->
  psub (plift e2) (pdom G) ->
  exists S1'' S2'' M'' v1' v2',
    exp_type1 S1 S2 M H1 (H2'++HX++H2) t (splice_tm t (length H2)(length HX)) S1'' S2'' M'' v1' v2' 
      T (splice_ty T (length H2)(length HX)) 
      (plift p) (splice_pl (plift p)(length H2)(length HX)) 
      (fr1 || fr2) (fr1 || fr2) 
      (plift q2) (splice_pl (plift q2) (length H2)(length HX)) 
      (plift e2) (splice_pl (plift e2) (length H2)(length HX)).
Proof.   
  intros.
  destruct E as [IE1 [IE2 [SC1 [STF1 [ST1 [SE1 [SE2 [HVX [HQX1 HQX2]]]]]]]]].
  assert (psub (plift q2) (pdom H1)). {
    unfoldq. destruct WFE. rewrite H5. intuition. } 
  assert (psub (plift q2) (pdom (H2'++H2))). {
    unfoldq. destruct WFE as [? [? ?]]. rewrite H7. intuition. }   
  exists S1', S2', M'. exists v1, v2. 
  split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 8: split. 9: split.
  eauto. eauto. eauto. eauto. eauto. 
  eapply se_sub; eauto. eapply lls_mono. eapply vars_locs_mono. unfoldq; intuition.
  eapply se_sub; eauto. eapply lls_mono. eapply vars_locs_mono. unfoldq; intuition. eapply splice_psub; eauto.
  eauto.
  eapply valq_sub; eauto. unfoldq; intuition. unfoldq; intuition.
  eapply valq_sub; eauto. unfoldq; intuition. eapply splice_psub; eauto. 
  intros ? [? ?]. eapply pdom_slice'; eauto.
Qed.

Lemma bi_sub_var_splice: forall S1 S2 S1' S2' M H1 H2 H2' HX t M' T p q1 e1 v1 v2 G fr1 x Tx qx
  (WFE: env_type M H1 (H2' ++ H2) G (plift p))
  (ST: store_type S1 S2 M)
  (E: exp_type1 S1 S2 M H1 (H2' ++ HX ++ H2) t (splice_tm t (length H2) (length HX)) 
    S1' S2' M' v1 v2 
    T (splice_ty T (length H2) (length HX)) 
    (plift p) (splice_pl (plift p) (length H2) (length HX)) 
    fr1 fr1
    (plift q1) (splice_pl (plift q1) (length H2)(length HX)) 
    (plift e1) (splice_pl (plift e1) (length H2)(length HX)))
  (L1: length H1 =length G)
  (L2: length (H2'++H2) = length G),
  plift q1 x ->
  indexr x G = Some (Tx, false, qx) ->
  psub (plift qx) (plift p) ->  
  exists S1'' S2'' M'' v1' v2',
  exp_type1 S1 S2 M H1 (H2'++HX++H2) t (splice_tm t (length H2) (length HX)) 
  S1'' S2'' M'' v1' v2' 
  T (splice_ty T (length H2) (length HX)) 
  (plift p) (splice_pl (plift p) (length H2) (length HX)) 
  fr1 fr1
  (por (pdiff (plift q1) (pone x)) (plift qx)) (splice_pl (por (pdiff (plift q1) (pone x)) (plift qx)) (length H2)(length HX)) 
  (plift e1) (splice_pl (plift e1) (length H2)(length HX)).
Proof.    
  intros. rename x into z.
  destruct E as [IE1 [IE2 [SC1 [STF1 [ST1 [SE1 [SE2 [HVX [HQX1 HQX2]]]]]]]]].
  exists S1', S2', M', v1, v2.
  split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 8: split. 9: split.
  - eauto. 
  - eauto. 
  - eauto. 
  - eauto. 
  - eauto. 
  - eapply se_sub; eauto. eapply lls_mono. eapply vars_locs_mono. unfoldq; intuition.
  - eapply se_sub; eauto. eapply lls_mono. eapply vars_locs_mono. unfoldq; intuition.
  - eauto.
  - eapply WFE in H0 as HZ.
    intros ? ?. destruct (HQX1 x). eauto.
    * eapply lls_vars in H5. destruct H5. bdestruct (x0 =? z).
      + subst. destruct HZ as [vz1 [vz2 ?]]. intuition.      
        eapply lls_var in H9. destruct H9 as (? & ? & ?). rewrite H9 in H5.
        inversion H5. subst x0. destruct H6. intuition. 
        left.
        erewrite lls_change with (M':=(st1 M')) in H12.
        erewrite lls_change with (M:=(st1 M)) (M':=(st1 M')) in H12.
        eapply lls_mono. 2: eapply H12. eapply vars_locs_mono.
        unfoldq. intuition.
        eauto.
        eapply stchain_tighten. eapply envt_filter_deep; eauto. eauto. eapply envt_store_deep_wf. eauto. eauto. eapply envt_store_deep_wf. eauto. eauto.
        eapply stchain_tighten. eapply valt_filter; eauto. eauto. eapply valt_deep_wf; eauto. eapply valt_deep_wf; eauto.
      + left. eapply lls_vars'. eapply H5. unfoldq. intuition.
    * right. intuition.
  - assert (env_type1 M H1 H2 H2' HX G p) as WFE1. {
    eapply envt_convert; eauto.
    }
    eapply WFE1 in H0 as HZ.
    intros ? ?. destruct (HQX2 x). eauto.
    * eapply lls_vars in H5. destruct H5. destruct H5 as [[? ?] ?].
      left. remember H5 as H5'. clear HeqH5'. destruct H5 as [[A1 A2] | [B1 B2]].    
      (* x0 < length H2 /\ p x0 *)
      bdestruct (x0 =? z).
      + (* x0 < length H2 /\ p x0 /\ x0 = z *)
        subst. destruct HZ as [vz1 [vz2 ?]]. intuition. bdestruct (z <? length H2); intuition.
        ++ eapply lls_var in H7. destruct H7 as (? & ? & ?). rewrite H7 in H9.
        inversion H9. subst x0.  
        erewrite lls_change with (M':=(st2 M')) in H11.
        erewrite lls_change with (M:=(st2 M)) (M':=(st2 M')) in H11.
        eapply lls_mono. 2: eapply H11. eapply vars_locs_mono.
        rewrite plift_splice. rewrite splice_por, splice_pdiff. unfoldq. intuition. eapply splice_psub; eauto.
        eauto.
        rewrite plift_splice. eapply stchain_tighten. eapply envt1_filter_deep; eauto. eauto. eapply envt_store_deep_wf. eauto. eauto. eapply envt1_store_deep_wf2. eauto. eauto.
        eapply stchain_tighten. eapply valt_filter; eauto. eauto. eapply valt_deep_wf; eauto. eapply valt_deep_wf; eauto.
      + (* x0 < length H2 /\ p x0 /\ x0 <> z *)
        eapply lls_vars'; eauto. split; auto. rewrite splice_por, splice_pdiff.
        left. split; auto. intros ?. destruct H8 as [? | ?]. intuition. intuition.
      + (* legth H2 + length HX <= x0 /\ p (x0 - length HX) *)
        bdestruct (z <? length H2); bdestruct (z =? x0); intuition.
        ++ (* z < length H2 /\ z <> x0 *)
          eapply lls_vars'; eauto.  split; auto. rewrite splice_por, splice_pdiff.
          left. split; auto. intros ?. destruct H9 as [? | ?]. intuition. unfoldq; intuition. 
        ++ (* z >= length H2 /\ z = x0 *)
           bdestruct (z =? x0 - length HX); intuition.
           {
            rewrite <- H9 in B2.
            destruct HZ as [vz1 [vz2 ?]]. intuition.
            eapply lls_var in H7. destruct H7 as [? [? ?]]. 
            assert (x0 = z + length HX). lia. rewrite H17 in H7.
            rewrite H7 in H12. inversion H12. subst x1.
            erewrite lls_change with (M':=(st2 M')) in H14.
            erewrite lls_change with (M:=(st2 M)) (M':=(st2 M')) in H14.
            eapply lls_mono. 2: eapply H14. eapply vars_locs_mono.
            rewrite plift_splice. rewrite splice_por, splice_pdiff. unfoldq. intuition. eapply splice_psub; eauto.
            eauto.
            rewrite plift_splice. eapply stchain_tighten. eapply envt1_filter_deep; eauto. eauto. eapply envt_store_deep_wf. eauto. eauto. eapply envt1_store_deep_wf2. eauto. eauto.
            eapply stchain_tighten. eapply valt_filter; eauto. eauto. eapply valt_deep_wf; eauto. eapply valt_deep_wf; eauto.
           }{
            eapply lls_vars'; eauto.  split; auto. rewrite splice_por, splice_pdiff.
            left. split; auto. intros ?. destruct H10 as [? | ?]. intuition. unfoldq; intuition. 
           }
        ++ (* z >= length H2 /\ z <> x0 *)
           bdestruct (z =? x0 - length HX); intuition. 
           {
            rewrite <- H9 in B2.
            destruct HZ as [vz1 [vz2 ?]]. intuition.
            eapply lls_var in H7. destruct H7 as [? [? ?]]. 
            assert (x0 = z + length HX). lia. rewrite H17 in H7.
            rewrite H7 in H12. inversion H12. subst x1.
            erewrite lls_change with (M':=(st2 M')) in H14.
            erewrite lls_change with (M:=(st2 M)) (M':=(st2 M')) in H14.
            eapply lls_mono. 2: eapply H14. eapply vars_locs_mono.
            rewrite plift_splice. rewrite splice_por, splice_pdiff. unfoldq. intuition. eapply splice_psub; eauto.
            eauto.
            rewrite plift_splice. eapply stchain_tighten. eapply envt1_filter_deep; eauto. eauto. eapply envt_store_deep_wf. eauto. eauto. eapply envt1_store_deep_wf2. eauto. eauto.
            eapply stchain_tighten. eapply valt_filter; eauto. eauto. eapply valt_deep_wf; eauto. eapply valt_deep_wf; eauto.
           }{
           eapply lls_vars'; eauto.  split; auto. rewrite splice_por, splice_pdiff.
           left. split; auto. intros ?. destruct H10 as [? | ?]. intuition. unfoldq; intuition.
           }
    * right. intuition.
Qed.

(*******************************************************************************

  general semantic weakening 

*******************************************************************************)

Lemma st_weaken: forall t1 T1 G p fr q e  
  (W: has_type G t1 T1 p fr q e)
  (CLT: closed_ty (length G) T1)
  (CLQ: closed_ql (length G) q)
  (CLE: closed_ql (length G) e),
  forall H1 H2 H2' HX M
    (WFE: env_type M H1 (H2'++H2) G (plift p)) 
    (SF: st_filter M (st_locs1 M)(st_locs2 M)),
    forall S1 S2,
    store_type S1 S2 M ->
    exists S1' S2' M' v1 v2,
      exp_type1 S1 S2 M
        H1 (H2'++HX++H2)
        t1 (splice_tm t1 (length H2) (length HX))
        S1' S2' M'
        v1 v2
        T1 (splice_ty T1 (length H2)(length HX))
        (plift p) (splice_pl (plift p) (length H2)(length HX))
        fr fr 
        (plift q) (splice_pl (plift q) (length H2)(length HX))
        (plift e) (splice_pl (plift e) (length H2)(length HX))
        .
Proof. 
  intros ? ? ? ? ? ?  ? W. 
  induction W; intros; intuition.
  - (* ttrue *)
    exists S1. exists S2. exists M. 
    exists (vbool true), (vbool true).
    rewrite plift_empty. rewrite splicep_empty. simpl. 
    eapply bi_true_splice; auto.

  - (* tfalse *)
    exists S1. exists S2. exists M.
    exists (vbool false), (vbool false).
    rewrite plift_empty. rewrite splicep_empty. simpl.
    eapply bi_false_splice; auto.

  - (* tvar *)
    rewrite plift_empty. rewrite splicep_empty. 
    eapply bi_var_splice; eauto; intuition.

  - (* tref *)
    simpl. intuition.
    assert (closed_ty (length env) T). inversion CLT. auto. intuition.
    destruct (H4 H1 H2 H2' HX M WFE SF S1 S2 H0) as [S1' [S2' [M' [ v1 [v2 IE]]]]].
    eapply bi_tref_splice; eauto.

  - (* tget1 *)
    assert (closed_ty (length env) (TRef T false q1)). constructor; auto. 
    assert (closed_ql (length env) e /\ closed_ql (length env) q).
    intuition. eapply has_type_closed in W; eauto. intuition.
    intuition.
    destruct (H4 H1 H2 H2' HX M WFE SF S1 S2 H0) as [S1' [S2' [M' [ v1 [v2 IE]]]]]. 
    simpl in *.
    eapply bi_tget1_splice; eauto.
    eapply envt_convert; eauto.

  - (* tget 2 *)
    eapply has_type_closed in W; eauto. intuition.
    destruct (H5 H1 H2 H2' HX M WFE SF S1 S2 H) as [S1' [S2' [M' [ v1 [v2 IE]]]]].
    eapply bi_tget2_splice; eauto. 

  - (* tget *)
    eapply has_type_closed in W; eauto. intuition.
    destruct (H6 H1 H2 H2' HX M WFE SF S1 S2 H0) as [S1' [S2' [M' [ v1 [v2 IE]]]]].
    rewrite plift_or in *. rewrite plift_if in *.
    eapply bi_tget_splice; eauto.

  - (* tput *)
    eapply has_type_closed in W1; eauto.
    eapply has_type_closed in W2; eauto.
    intuition.
    destruct (H8 H1 H2 H2' HX M WFE SF S1 S2 H) as [S1' [S2' [M' [ v1 [v2 IE]]]]].
    assert (env_type M' H1 (H2'++H2) env (plift p)) as WFE1. 
    eapply envt_store_extend; eauto. apply IE. 
    assert (st_filter M' (st_locs1 M')(st_locs2 M')) as SF1. apply IE.
    assert (store_type S1' S2' M' ) as ST'.
    apply IE.
    destruct (H11 H1 H2 H2' HX M' WFE1 SF1 S1' S2' ST') as [S1'' [S2'' [M'' [v3 [v4 IE2]]]]].
    simpl. rewrite plift_empty. rewrite  splicep_empty in *. 
    repeat rewrite plift_or. simpl in *.
    eapply bi_tput_splice; eauto. eapply envt_convert; eauto.

  - (* tapp *)
    eapply has_type_closed in W1; eauto.
    eapply has_type_closed in W2; eauto.
    intuition.
    destruct (H12 H3 H4 H2' HX M WFE SF S1 S2 H5) as [S1' [S2' [M' [v1 [v2 IEF]]]]].
    assert (env_type  M' H3 (H2'++H4) env (plift p)) as WFE1. 
    eapply envt_store_extend;  eauto. apply IEF. 
    assert (st_filter M' (st_locs1 M')(st_locs2 M')) as SF1. apply IEF.
    assert (store_type S1' S2' M') as ST'. apply IEF. 
    specialize (H15 H3 H4 H2' HX M' WFE1 SF1 S1' S2' ST') as [S1'' [S2'' [M'' [v3 [v4 IEX]]]]].
    repeat rewrite plift_or in *. repeat rewrite plift_if in *.
    eapply bi_tapp_splice; eauto.
    eapply envt_convert in WFE. eapply WFE. 
    

  - (* tabs *)
    rewrite plift_empty. rewrite splicep_empty. repeat rewrite plift_or in *.
    repeat rewrite plift_if in *. repeat rewrite plift_one in *. repeat rewrite plift_and in *.

    eapply bi_tabs_splice; eauto.
    eapply envt_convert in WFE. eapply WFE. 
       
    intros.
    replace (vx2 :: H2' ++ H7) with ((vx2 :: H2') ++ H7) in H10. 
    eapply has_type_closed in W.
    2: { rewrite plift_or, plift_and, plift_one. eauto. }   
    intuition. auto.
        
  
  - (* tseq *)
    eapply has_type_closed in W1. 2: { eapply envt_tighten; eauto. }
    eapply has_type_closed in W2. 2: { eapply envt_tighten. eapply WFE. eauto. }
    intuition.
    rename H4 into IH1. rename H5 into IH2. rename H3 into ST.
      
    assert (env_type M H1 (H2'++H2) env (plift p1)) as WFE1.
    eapply envt_tighten; eauto.
    destruct (IH1 H1 H2 H2' HX M WFE1 SF S1 S2 ST) as [S1' [S2' [M' [v1 [v2 IE1]]]]].

    assert (env_type M' H1 (H2'++H2) env (plift p2)) as WFE2.
    eapply envt_tighten.  eapply envt_store_extend. eapply WFE. eauto.
    apply IE1. auto.

    assert (store_type S1' S2' M') as ST'. eapply IE1.
    assert (st_filter M' (st_locs1 M')(st_locs2 M')) as SF2. apply IE1. 

    destruct (IH2 H1 H2 H2' HX M' WFE2 SF2 S1' S2' ST') as [S1'' [S2'' [M'' [v3 [v4 IE2]]]]].

    rewrite splicety_id in *. 2-4: constructor.
    repeat rewrite plift_or in *. rewrite plift_empty in *.  
    rewrite splicep_empty in *. 

    eapply bi_tseq_splice; eauto.

  - (* qsub *)
    eapply has_type_closed in W as Hcl. 2: eauto.
    intuition. rename H6 into IHW.
    destruct (IHW H3 H4 H2' HX M WFE SF S1 S2 H5) as [S1' [S2' [M' [v1 [v2 IE]]]]].
    eapply bi_qsub_splice; eauto. 
  
  - (* t_sub_var *)
    apply wf_env_type in WFE as WFE'. 
    destruct WFE' as [L1 [L2 [P1 [P2 [P3 P4]]]]].
    eapply has_type_closed in W as Hcl; eauto.
    
    intuition. rename H5 into IHW.
    destruct (IHW H2 H3 H2' HX M WFE SF S1 S2 H4) as [S1' [S2' [M' [v1 [v2 IE]]]]].
    rewrite plift_or, plift_diff, plift_one.
    eapply bi_sub_var_splice; eauto.
Qed.


(*******************************************************************************

 top-level semantic weakening 

********************************************************************************)
Lemma st_weaken1: forall t1 T1 G
  (W: has_type G t1 T1 qempty false qempty qempty ),
  forall H1 H2 M MF S1F S2 H2',
   env_type (st_empty (st1 MF) (st2 M)) H1 (H2'++H2) G pempty ->
   sstore_type S1F (st1 MF)  -> 
   sstore_type S2 (st2 M) ->
    exists v1 S1' M1', tevaln S1F H1 t1 S1' v1 /\ 
    sstore_type S1' M1' /\
    sst_chain (st1 MF) M1' /\
    forall HX S2' M2' P, 
    sst_chain_partial (st2 M)(st2 M2') P ->
    sstore_type S2' (st2 M2') ->
    exists v2 M' S2'',
    tevaln S2' (H2'++HX++H2) (splice_tm t1 (length H2) (length HX)) S2'' v2 /\ 
    store_type S1' S2'' (st_empty M1' (st2 M')) /\
    sst_chain (st2 M2') (st2 M') /\
    store_effect S2' S2'' pempty /\
    val_type (st_empty M1' (st2 M'))  H1 (H2'++HX++H2) v1 v2 T1 (splice_ty T1  (length H2)  (length HX)) /\
    val_qual (st1 MF) M1' H1 v1 false pempty  /\
    val_qual (st2 M) (st2 M') (H2'++HX++H2) v2 false pempty.
Proof. 
  intros. eapply has_type_closed in W as HCL. 2: { rewrite plift_empty. eauto.  } 
  destruct HCL as [HCL1 [HCL2 [HCL3 HCL4]]].
  eapply store_invariance with (S1 := S1F) (S2 := S2) in W as W'; eauto.
  3: { eapply storet_empty; eauto. }
  2: { rewrite plift_empty.  eauto. }
  
  destruct W' as [S1' [S2' [M'  [v1 [v2 ?]]]]].
  destruct H4 as [E1 [E2 [STC [SF [STE [EFF1 [EFF2 [VT [VQ1 VQ2]]]]]]]]].
  rewrite plift_empty in *. rewrite pand_empty_r in *. rewrite vars_locs_empty in EFF1, EFF2. rewrite lls_empty in EFF1, EFF2.
  exists v1, S1', (st1 M'). split. 2: split. 3: split.  
  auto. eapply STE; eauto. eapply STC; eauto.
  intros.
  eapply st_weaken with (H1 := H1)(H2 := H2)(H2' := H2')(HX := HX)(S1 := S1F)(S2 := S2'0)(M := (st_empty (st1 MF) (st2 M2'))) in W; eauto.
  2: { eapply envt_store_change. rewrite plift_empty. eapply H. eapply storet_empty; eauto. rewrite plift_empty.
       repeat rewrite vars_locs_empty. repeat rewrite lls_empty. eapply stchain_empty'; eauto. }
  2: { eapply stfilter_empty'.  }
  2: { eapply storet_empty; eauto. }
  
  repeat rewrite plift_empty in *. 
  repeat rewrite splicep_empty in *. 
  destruct W as [S1'' [S2'' [M''  [v1' [v2' ?]]]]].
  destruct H6 as [E1' [E2' [STC' [SF' [STE' [EFF3 [EFF4 [VT' [VQ1' VQ2']]]]]]]]].
  rewrite pand_empty_r in *.
  rewrite vars_locs_empty in EFF3, EFF4.
  rewrite lls_empty in EFF3, EFF4.
  assert  (v1' = v1 /\ S1'' = S1'). eapply tevaln_unique; eauto.
  destruct H6. subst v1'. subst S1''.
  exists v2', M'', S2''; eauto; intuition.
  eapply storet_empty; eauto. eapply STE; eauto. eapply STE'; eauto. eapply STC'; eauto.
  eapply valt_store_change. 2: eapply VT'; eauto. eauto.
  eapply valq_val_empty in VQ1, VQ2'. rewrite VQ1, VQ2'. repeat rewrite lls_empty. eapply stchain_empty'; eauto.
Qed. 

(**** substitution ****)

Definition env_type_subst2 M H1 H2 G p xx vx qx:=
  length H1  = length G /\
  (length H2 + 1 = length G) /\
  psub (plift p) (pdom H1) /\
  psub (subst_pl (plift p) xx (plift qx)) (pdom H2) /\
  (forall x T fr (q:ql),
      indexr x G = Some (T, fr, q) ->
      exists v1 v2 : vl,
      closed_ql x q /\
      indexr x H1 = Some v1 /\ 
      (x < xx -> indexr x H2 = Some v2) /\
      (x = xx -> vx = v2) /\ 
      (x > xx -> indexr (x-1) H2 = Some v2) /\
      (plift p x -> val_type M H1 H2 v1 v2 T (subst_ty T xx qx)) /\
      (fr = false -> (plift p) x -> psub (plift q) (plift p) -> psub (locs_locs_stty (st1 M) (val_locs v1)) (locs_locs_stty (st1 M) (vars_locs H1 (plift q)))) /\
      (fr = false -> (plift p) x -> psub (plift q) (plift p) -> 
              psub (locs_locs_stty (st2 M) (val_locs v2)) (locs_locs_stty (st2 M) (vars_locs H2 (subst_pl (plift q) xx (plift qx)))))
  )
  /\
  (forall q q',
    psub q (plift p) ->
    psub q' (plift p) ->
    psub (pand (vars_trans G q) (vars_trans G q')) (plift p) ->
    psub (pand (locs_locs_stty (st1 M) (vars_locs H1 q)) (locs_locs_stty (st1 M) (vars_locs H1 q')))
      (locs_locs_stty (st1 M) (vars_locs H1 (pand (vars_trans G q) (vars_trans G q')))))
  /\    
   (forall q q',
    psub q (plift p) ->
    psub q' (plift p) ->
    psub (pand (vars_trans G q) (vars_trans G q')) (plift p) ->
    psub (pand (locs_locs_stty (st2 M) (vars_locs H2 (subst_pl q xx (plift qx)))) (locs_locs_stty (st2 M) (vars_locs H2 (subst_pl q' xx (plift qx)))))
      (locs_locs_stty (st2 M) (vars_locs H2 (subst_pl (pand (vars_trans G q) (vars_trans G q')) xx (plift qx)))))    
.


Lemma filter_closed_subst: forall M H1 H2 G p m v q,
  env_type_subst2 M H1 H2 G p m v q ->
  closed_ql (length G) p.
Proof.
  intros. destruct H as [L1 [L2 [P1 [P2 P3]]]].
  unfold closed_ql. intros.
  unfoldq; intuition. eapply P1 in H.  rewrite L1 in H. auto.
Qed.  

Lemma envt_to_envt_subst2: forall M H1 H2 G p qf q1 v1 v2 T1 fr1 fn1 M' S1 S2
  (ST: store_type S1 S2 M') ,
  env_type M H1 H2 G (plift p) ->
  val_type M' H1 H2 v1 v2 T1 T1 ->
  closed_ty (length G) T1 ->
  closed_ql (length G) q1 ->
  closed_ql (length G) qf ->
  val_locs v1 = pempty ->
  val_locs v2 = pempty ->
  env_type_subst2 M (v1::H1) H2 ((T1, fr1, (qand p (qor q1 (qif fn1 qf))))::G) (qor (qand p qf) (qone (length G))) (length G) v2 qempty.
Proof. 
  intros. remember H as H'. clear HeqH'.
  eapply filter_closed in H' as FC.
  destruct H as [L1 [L2 [PD1 [PD2 [P1 [P2 P3]]]]]].
  split. 2: split. 3: split. 4: split. 5: split. 6: split.
  + simpl. lia.
  + simpl. lia.
  + rewrite plift_or, plift_and, plift_one. unfoldq; intuition. eapply FC in H. simpl. lia. simpl. lia.
  + rewrite plift_or,  plift_one, substp_or, plift_empty.
    assert (closed_ql (length G) (qand p qf)). { eapply closedq_and. left. auto.  }
    rewrite substp_id; auto. 
    rewrite substp_hit. rewrite plift_and. unfoldq; intuition. 
   
  + intros.
    bdestruct (x =? length G); intuition. subst x. rewrite indexr_head in H.
    inversion H. subst T1 fr1 q.
    exists v1, v2; intuition.
    eapply closedq_and. left. auto.
    rewrite <- L1. rewrite indexr_head. auto.
    eapply valt_extend with (H2' := [])(H1' := [v1]) in H0.
    rewrite substy_id. simpl in H0. eapply valt_store_change. eauto. eauto. 
    rewrite H6. rewrite H7. repeat rewrite lls_empty. eapply stchain_empty'; eauto.
    auto. rewrite L1. auto. rewrite L2. auto.
    rewrite H6. rewrite lls_empty. unfoldq; intuition.
    rewrite H7. rewrite lls_empty. unfoldq; intuition. 
   
    rewrite indexr_skip in H. 2: { lia. }
    destruct (P1 x T fr q) as [vx1 [vx2 [CL [IX1 [IX2 [IVT [? ?]]]]]]].  auto.
    exists vx1, vx2; intuition. 
    rewrite indexr_skip. auto. lia.
    apply indexr_var_some' in H. lia.
    assert ((plift p) x). { rewrite plift_or, plift_and, plift_one in H11. destruct H11. unfoldq; intuition. unfoldq; intuition. }
    assert (closed_ty (length G) T). { eapply valt_closed in IVT. intuition.  rewrite <- L1. auto. auto.   }
    
    eapply valt_extend with (H1' :=[v1])(H2':=[]). rewrite L1. auto.
    rewrite substy_id. rewrite L2. auto. auto. 
    rewrite substy_id. eapply IVT; eauto. auto.
    
    assert ((plift p) x). { rewrite plift_or, plift_and, plift_one in H12. destruct H12. unfoldq; intuition. unfoldq; intuition. }
    assert (psub (plift q) (plift p)). { rewrite plift_or, plift_and, plift_one in H13. intros ? ?. eapply H13 in H15 as H15'. destruct H15'. intuition. unfoldq; intuition. unfoldq. subst x0. eapply CL in H15. apply indexr_var_some' in H. lia. }
    intuition.
    intros ? ?. eapply H9 in H14. replace (v1 :: H1) with ([v1]++H1). 2: simpl; auto. rewrite vars_locs_extend. auto. unfoldq; intuition.
    
    assert ((plift p) x). { rewrite plift_or, plift_and, plift_one in H12. destruct H12. unfoldq; intuition. unfoldq; intuition. }
    assert (psub (plift q) (plift p)). { rewrite plift_or, plift_and, plift_one in H13. intros ? ?. eapply H13 in H15 as H15'. destruct H15'. intuition. unfoldq; intuition. unfoldq. subst x0. eapply CL in H15. apply indexr_var_some' in H. lia. }
    intuition. rewrite plift_empty. rewrite substp_id. auto.
    intros ? ?. eapply H15 in H14. unfoldq; intuition.

  + rewrite plift_or, plift_and, plift_one in *.
    eapply envt_telescope in H' as TL1.
    intros q q' QSUB QSUB' QSUBTR x (QQ & QQ'). 
    eapply lls_vars in QQ. eapply lls_vars in QQ'.
    destruct QQ as (? & VTQ & VLQ).
    destruct QQ' as (? & VTQ' & VLQ').

    destruct (QSUB x0); intuition; destruct (QSUB' x1); intuition.
    
    - (* qf, qf *)
      assert (psub (pand (vars_trans G (pand (pdom H1) q)) (vars_trans G (pand (pdom H1) q'))) (pand (plift p) (plift qf))) as QSUBTR1. {
        intros ? [? ?]. destruct (QSUBTR x2) as [? | ?].
        split. (* extend *)
        eapply vt_extend. eapply vt_mono. 2: eapply H9. unfoldq; intuition.
        eapply vt_extend. eapply vt_mono. 2: eapply H10. unfoldq; intuition.
        unfoldq; intuition.
        eapply vt_closed in H9; eauto. unfoldq; intuition. unfoldq; intuition.
      } 
      
      eassert _ as W4. {
        eapply (P2 (pand (pdom H1) q)(pand (pdom H1) q')) with (x := x). 

        intros ? ?. destruct (QSUB x2) as [? | ?]. unfoldq; intuition.
        unfoldq; intuition. unfoldq; intuition.

        intros ? ?. destruct (QSUB' x2) as [? | ?]. unfoldq; intuition.
        unfoldq; intuition. unfoldq; intuition.

        intros ? ?. eapply QSUBTR1 in H9. unfoldq; intuition.

        split.

        eapply lls_vars'. eapply lls_mono. 2: eapply VLQ. intros ? ?. eapply var_locs_shrink. eauto. unfoldq. intuition. unfoldq. intuition.
        
        eapply lls_vars'. eapply lls_mono. 2: eapply VLQ'. intros ? ?. eapply var_locs_shrink. eauto. unfoldq; intuition.
        unfoldq; intuition.
      }

      eapply lls_vars in W4. destruct W4 as (? & (? & ?) & ?). 
      
      eapply lls_vars'. eapply lls_mono. 2: eauto. intros ? ?. eapply var_locs_extend. eauto. split.
      eapply vt_extend. eapply vt_mono. 2: eapply H9. unfoldq. intuition.
      eapply vt_extend. eapply vt_mono. 2: eapply H10. unfoldq. intuition.

    - (* qf, x *)
      unfold pone in H8. subst x1. 
      assert (psub (pand (vars_trans G (pand (pdom H1) q)) (vars_trans G (pand (plift p)(por (plift q1) (pif fn1 (plift qf)))))) (pand (plift p) (plift qf))) as QSUBTR1. {
        intros ? [? ?]. destruct (QSUBTR x1) as [? | ?].
        split. {
          eapply vt_extend. eapply vt_mono. 2: eapply H8. unfoldq. intuition. (* extend q *)
        }{
          eapply vt_head. eauto. rewrite plift_and, plift_or, plift_if. unfoldq; intuition.  eauto. 
          rewrite plift_and, plift_or, plift_if. eauto.  (* pick q1 *)
        }
        eauto.
        eapply vt_closed in H9; eauto. unfoldq. intuition. unfoldq; intuition.  (* contra *)
      }

      eassert _ as W4. {
        eapply (P2 (pand (pdom H1) q) (pand (plift p)(por (plift q1) (pif fn1 (plift qf))))) with (x:=x).

        intros ? ?. destruct (QSUB x1) as [? | ?]. unfoldq. intuition. 
        unfoldq; intuition. unfoldq; intuition. unfoldq; intuition.

        intros ? ?. eapply QSUBTR1 in H8. unfoldq; intuition.

        split. 

        eapply lls_vars'. eapply lls_mono. 2: eapply VLQ. intros ? ?. eapply var_locs_shrink. eauto. unfoldq. intuition. unfoldq. intuition.
        
        
        eapply lls_var in VLQ'. destruct VLQ' as (? & IX & ?). rewrite <- L1 in IX.
        rewrite indexr_head in IX. inversion IX. eauto. subst x1.
        rewrite H6 in H8. rewrite lls_empty in H8. unfoldq; intuition.
      }


      eapply lls_vars in W4. destruct W4 as (? & (? & ?) & ?). 

      eapply lls_vars'. eapply lls_mono. 2: eauto. intros ? ?. eapply var_locs_extend. eauto. split.
      eapply vt_extend. eapply vt_mono. 2: eapply H8. unfoldq. intuition.
      eapply vt_head. eauto. rewrite plift_and, plift_or, plift_if. unfoldq; intuition. eauto. 
      rewrite plift_and, plift_or, plift_if. auto.
    - (* x, qf *)
      unfold pone in H. subst x0.
      
      assert (psub (pand (vars_trans G (pand (plift p)(por (plift q1) (pif fn1 (plift qf))))) (vars_trans G (pand (pdom H1) q'))) (pand (plift p) (plift qf))) as QSUBTR1. {
        intros ? [? ?]. destruct (QSUBTR x0) as [? | ?].
        split. {
          eapply vt_head. eauto.  rewrite plift_and, plift_or, plift_if. unfoldq; intuition. auto. 
          rewrite plift_and, plift_or, plift_if. auto.  (* pick q1 *)
        }{
          eapply vt_extend. eapply vt_mono. 2: eapply H9. unfoldq. intuition. (* extend q' *)
        }
        eauto.
        eapply vt_closed in H; eauto. unfoldq. intuition. unfoldq. intuition. (* contra *)
      }

      eassert _ as W4. {
        eapply (P2 (pand (plift p)(por (plift q1) (pif fn1 (plift qf)))) (pand (pdom H1) q')) with (x:=x).

        unfoldq. intuition.

        intros ? ?. destruct (QSUB' x0) as [? | ?]. unfoldq. intuition. 
        unfoldq; intuition. unfoldq; intuition.

        intros ? ?. eapply QSUBTR1 in H. unfoldq; intuition.

        split. 
        eapply lls_vars'. eapply lls_mono. 2: eapply VLQ'. intros ? ?. eapply var_locs_shrink. eauto. unfoldq. intuition. 
        

        eapply lls_var in VLQ. destruct VLQ as (? & IX & ?). rewrite <- L1 in IX.
        rewrite indexr_head in IX. inversion IX. eauto. inversion IX. subst x0. rewrite H6 in H. rewrite lls_empty in H. unfoldq; intuition.
        
        
        eapply lls_vars'. eapply lls_mono. 2: eapply VLQ'. intros ? ?. eapply var_locs_shrink. eauto. unfoldq. intuition. unfoldq. intuition.
      }

      eapply lls_vars in W4. destruct W4 as (? & (? & ?) & ?). 

      eapply lls_vars'. eapply lls_mono. 2: eauto. intros ? ?. eapply var_locs_extend. eauto. split.
      eapply vt_head. eauto. rewrite plift_and, plift_or, plift_if. unfoldq; intuition. auto. 
      rewrite plift_and, plift_or, plift_if. auto. 
      eapply vt_extend. eapply vt_mono. 2: eapply H9. unfoldq. intuition.

    -  (* x x *)
      unfold pone in H, H8. 
      subst x0 x1.
      eapply lls_vars'. eauto. split.
      left. eauto. left. eauto.
  + rewrite plift_or, plift_and, plift_one, plift_empty in *.
    clear P2. (* distraction*)
    eapply envt_telescope in H' as TL1.
    
    intros q q' QSUB QSUB' QSUBTR x (QQ & QQ').
    eapply lls_vars in QQ. eapply lls_vars in QQ'.

    destruct QQ as (? & VTQ & VLQ).
    destruct QQ' as (? & VTQ' & VLQ').

    eapply substp_sub' with (m := (length G))(q1 := pempty) in QSUB as QSUB_subst.
    eapply substp_sub' with (m := (length G))(q1 := pempty) in QSUB' as QSUB'_subst.
    eapply substp_sub' with (m := (length G))(q1 := pempty) in QSUBTR as QSUBTR_subst. 
    rewrite substp_or in *. 

    destruct (QSUB_subst x0); intuition; destruct (QSUB'_subst x1); intuition.
    - (* qf, qf *)
      assert (psub (pand (vars_trans  G (pand (pdom H1) q)) (vars_trans G (pand (pdom H1) q' ))) (pand (plift p) (plift qf))) as QSUBTR1. {
        intros ? [? ?]. destruct (QSUBTR x2) as [? | ?]. 
        split. (* extend *)
        eapply vt_extend. eapply vt_mono. 2: eapply H9. unfoldq. intuition.
        eapply vt_extend. eapply vt_mono. 2: eapply H10. unfoldq. intuition.
        eauto.
        eapply vt_closed in H10. unfoldq; intuition. eauto. unfoldq; intuition.  (* contra *)
      }

    eassert _ as W4. {
      eapply (P3 (pand (pdom H1) q) (pand (pdom H1) q')) with (x:=x). 
       
      - intros ? ?. destruct (QSUB x2) as [? | ?]. unfoldq; intuition.
        unfoldq; intuition. unfoldq; intuition.

      - intros ? ?. destruct (QSUB' x2) as [? | ?]. unfoldq; intuition.
        unfoldq; intuition. unfoldq; intuition.
      
      - intros ? ?.  eapply QSUBTR1 in H9. unfoldq; intuition.
        
      - split.
        {
          eapply lls_vars'. eapply lls_mono. 2: eapply VLQ. intros ? ?. eauto. 
          split. unfold pdom.
          destruct H as [[? ?] | [[? ?] |[? ?]]].
          destruct H. eapply PD1 in H. unfoldq; intuition.
          destruct H9. eapply PD1 in H9. unfoldq; intuition.
          lia.

          eapply QSUB_subst in VTQ as A. destruct A. rewrite substp_id' in H9. 
          destruct H9. eapply PD1 in H9.
          destruct VTQ as [[? ?] | [[? ?] |[? ?]]].
          destruct H12; intuition. unfoldq; intuition. unfoldq; intuition. auto.
          intros ? ?. unfoldq; intuition.
          rewrite substp_hit in H9. unfoldq; intuition.
        }

        {
          eapply lls_vars'. eapply lls_mono. 2: eapply VLQ'. intros ? ?. eauto. 
          split. unfold pdom.
          destruct H8 as [[? ?] | [[? ?] |[? ?]]].
          destruct H8. eapply PD1 in H8. unfoldq; intuition.
          destruct H9. eapply PD1 in H9. unfoldq; intuition.
          lia.

          eapply QSUB'_subst in VTQ' as A. destruct A. rewrite substp_id' in H9. 
          destruct H9. eapply PD1 in H9.
          destruct VTQ' as [[? ?] | [[? ?] |[? ?]]].
          destruct H12; intuition. unfoldq; intuition. unfoldq; intuition. auto.
          intros ? ?. unfoldq; intuition.
          rewrite substp_hit in H9. unfoldq; intuition.

        }
    }
    
    eapply lls_mono; eauto. eapply vars_locs_mono; eauto. intros ? [? ?]. 
    rewrite substp_empty_and.
    split. 
    {
      assert ((subst_pl (vars_trans G (pand (pdom H1) q)) (length G) pempty) = (vars_trans G (pand (pdom H1) q))). 
      eapply substp_id'; eauto. intros ? ?. eapply vt_closed; eauto. unfoldq; intuition.
      rewrite <- H11 in H9. 
      
      eapply substp_sub'. 2: eapply H9. intros ? ?. eapply vt_extend. eapply vt_mono; eauto. unfoldq; intuition.
    }

    {
      assert ((subst_pl (vars_trans G (pand (pdom H1) q')) (length G) pempty) = (vars_trans G (pand (pdom H1) q'))). 
      eapply substp_id'; eauto. intros ? ?. eapply vt_closed; eauto. unfoldq; intuition.
      rewrite <- H11 in H10. 
      
      eapply substp_sub'. 2: eapply H10. intros ? ?. eapply vt_extend. eapply vt_mono; eauto. unfoldq; intuition.
    }
  - rewrite substp_hit in H8. unfoldq; intuition.
  - rewrite substp_hit in H. unfoldq; intuition.
  - rewrite substp_hit in H. unfoldq; intuition.
 Qed.  

Lemma wf_envt_subst2: forall M H1' H1 v1 H2' H2 G G' p q1  T0 v2 
  (WFE: env_type_subst2 M (H1'++v1::H1) (H2'++ H2) (G'++T0::G) p (length G) v2 q1)
  (L1: length H1 = length G)
  (L2: length H2 = length G)
  (L3: length H1' = length G')
  (L4: length H2' = length G'),
  (
   pdom H1 = pdom G /\ 
   pdom H2 = pdom G /\ 
   pdom H1' = pdom G' /\
   pdom H2' = pdom G' /\
   psub (plift p) (pdom (H1'++v1::H1)) 
   ).
Proof.
    intros. unfold pdom in *. unfold env_type_subst2 in WFE.
    rewrite L1, L2, L3, L4; intuition. 
Qed.

Lemma envt_subst_store_wf1: forall M H1 H1' v1 H2 H2' G G' p q q1 v2'0 T0 fr0 q0
    (WFE: env_type_subst2 M (H1' ++ v1 :: H1) (H2' ++ H2) (G' ++  ((T0, fr0, q0) :: G)) p  (length G) v2'0 q1),
    psub q (plift p) -> 
    psub (vars_locs (H1'++v1::H1) q) (pnat (length1 M)). 
Proof. 
  intros. unfoldq; intuition.
  intros; destruct WFE as [L1 [L2 [P1 [P2 [W1 [W2 W3]]]]]]; intuition.
  unfoldq; intuition.
  destruct H0 as [? [? [? [? ?]]]].
  eapply H in H0.

  assert (exists T, indexr x0 (G'++ (T0,fr0,q0)::G) = Some T) as TY. 
  eapply indexr_var_some. eapply P1 in H0.
  rewrite <- L1. rewrite app_length in *. simpl in *.  lia.
  destruct TY as [[[T' fr'] q'] ?].
  destruct (W1 x0 T' fr' q') as [vx1 [vx2 [CLQ [IX1 [IX21 [IX22 [IX23 [IV [? ?]]]]]]]]]. eauto. 

  rewrite H3 in IX1. inversion IX1. subst.
  eapply valt_wf in IV. intuition.
  eapply H8. auto. auto.
Qed.

Lemma envt_subst_store_wf2: forall M H1 H1' v1 H2 H2' G G' p q q1 v2'0 T0 fr0 q0
    (WFE: env_type_subst2 M (H1' ++ v1 :: H1) (H2' ++ H2) (G' ++  (T0, fr0, q0) :: G) p  (length G) v2'0 q1)
    (EMP: q1 = qempty)
    (LL2: length H2 = length G), 
    psub (subst_pl q (length H2) (plift q1)) (subst_pl (plift p) (length H2) (plift q1)) -> 
    psub (vars_locs (H2'++H2) (subst_pl q (length H2) (plift q1))) (pnat (length2 M)).  
Proof. 
  intros. destruct WFE as [L1 [L2 [P1 [P2 [W1 [W2 W3]]]]]]; intuition.
  intros ? ?. 
  destruct H0 as [? [? ?]].
  eapply H in H0.

  assert (plift p (length G) /\ plift q1 x0 \/
            length G > x0    /\ plift p x0  \/
            length G <= x0   /\ plift p (x0 + 1)) as CASES. {
  rewrite <- LL2. unfold subst_pl in H0. destruct H0 as [[? A]|B].
  - (* p (len G) *)
    destruct A as [[AA | AB] | AC].
    + (* len G <= x0 /\ p (x0 + 1) *) eauto. 
    + (* len G > x0 /\ p x0 *) eauto. 
    + (* q1 x0 *) eauto. 
  - destruct B as [BA | BB].
    + (* len G <= x0 /\ p (x0+1) *) eauto. 
    + (* len G > x0 /\ p x0 *) eauto. }

  destruct CASES as [[EQ1 EQ2] | [[LT1 LT2] | [GT1 GT2]]].
  - subst q1. rewrite plift_empty in *. contradiction.
  - assert (exists TF, indexr x0 (G'++(T0, fr0, q0)::G) = Some TF) as TY.
    rewrite indexr_var_some. rewrite app_length. simpl. lia.
    destruct TY as [[[T' fr'] q'] ?].
    destruct (W1 x0 T' fr' q') as [vx1 [vx2 [CLQ [IX1 [IX21 [IX22 [IX23 [IV [? ?]]]]]]]]]. eauto. 
    eapply valt_wf in IV. eapply IV. eauto. 
    destruct H3 as (? & ? & ?). rewrite IX21 in H3. inversion H3.
    subst x1. eauto. eauto. eauto.
  - assert (exists TF, indexr (x0+1) (G'++(T0, fr0, q0)::G) = Some TF) as TY.
    rewrite indexr_var_some. rewrite app_length. simpl. eapply P1 in GT2. unfoldq; intuition.
    repeat rewrite app_length in * . simpl in *. lia.
    destruct TY as [[[T' fr'] q'] ?].
    destruct (W1 (x0+1) T' fr' q') as [vx1 [vx2 [CLQ [IX1 [IX21 [IX22 [IX23 [IV [? ?]]]]]]]]]. eauto. 
    eapply valt_wf in IV. eapply IV.
    destruct H3 as (? & ? & ?).
    bdestruct (x0+1 =? length G); intuition.
    bdestruct (length G <? x0+1); intuition.
    replace (x0+1-1) with x0 in H12. rewrite H3 in H12.
    inversion H12. subst. auto. lia. auto.
Qed.

Lemma envt_subst_store_deep_wf1: forall M H1 H1' v1 H2 H2' G G' p q q1 v2'0 T0 fr0 q0
    (WFE: env_type_subst2 M (H1' ++ v1 :: H1) (H2' ++ H2) (G' ++  ((T0, fr0, q0) :: G)) p  (length G) v2'0 q1),
    psub q (plift p) -> 
    psub (locs_locs_stty (st1 M) (vars_locs (H1'++v1::H1) q)) (pnat (length1 M)). 
Proof. 
  intros. eapply envt_subst_store_wf1 with (q := q) in H as H'; eauto.
  destruct WFE as [L1 [L2 [P1 [P2 [W1 [W2 W3]]]]]]; intuition.
  intros ? ?. inversion H0; subst. eapply H' in H3. auto.
  destruct H3 as [? [? [? [? ?]]]].
  assert (x0 < length (H1' ++ v1::H1)). apply indexr_var_some' in H6. auto.
  assert (exists xtq, indexr x0 (G'++((T0, fr0, q0) :: G)) = Some xtq) as TY. 
  eapply indexr_var_some. rewrite <-L1. eauto.
  destruct TY as [[[Tx frx] qx] ?].
  destruct (W1 x0 Tx frx qx) as [vx1 [vx2 [CLQ [IX1 [IX21 [IX22 [IX23 [VT [? ?]]]]]]]]]; eauto. 
  rewrite H6 in IX1. inversion IX1. subst x2. 
  assert ((plift p) x0). unfoldq. intuition. intuition.
  eapply valt_deep_wf in H13; eauto.  destruct H13.
  eapply H13. eapply lls_s; eauto.
Qed.


Lemma envt_subst_store_deep_wf2: forall M H1 H1' v1 H2 H2' G G' p q q1 v2'0 T0 fr0 q0
    (WFE: env_type_subst2 M (H1' ++ v1 :: H1) (H2' ++ H2) (G' ++  ((T0, fr0, q0) :: G)) p  (length G) v2'0 q1)
    (EMP: q1 = qempty)
    (LL2: length H2 = length G),
    psub  q (plift p) -> 
    psub (locs_locs_stty (st2 M) (vars_locs (H2'++H2) (subst_pl q (length H2) (plift q1)))) (pnat (length2 M)). 
Proof. 
  intros. eapply dsubst_sub with (m := length H2)(q1 := q1)(p1 := q1) in H as H'; eauto.
  eapply envt_subst_store_wf2 with (q := q) in H' as H''; eauto.
  destruct WFE as [L1 [L2 [P1 [P2 [W1 [W2 W3]]]]]]; intuition.  
  intros ? ?. repeat rewrite plift_subst in *.
  eapply lls_vars in H0. destruct H0 as [? [? ?]]. 
  
  assert (plift p (length G) /\ plift q1 x0 \/
            length G > x0    /\ plift p x0  \/
            length G <= x0   /\ plift p (x0 + 1)) as CASES. {
  destruct H0 as [[A1 A2] | B].            
  - (* p (len G) *)
    destruct A2 as [[[AA1 AA2] | [AB1 AB2 ]] | AC].
    + (* len G <= x0 /\ p (x0 + 1) *) right. right. split; auto. lia.
    + (* len G > x0 /\ p x0 *) right. left. split; auto. lia.
    + (* q1 x0 *) left. split; auto. rewrite <- LL2. auto.
  - destruct B as [BA | BB].
    + (* len G <= x0 /\ p (x0+1) *)right. right. intuition.
    + (* len G > x0 /\ p x0 *) right. left. intuition. }

   destruct CASES as [[EQ1 EQ2] | [[LT1 LT2] | [GT1 GT2]]].
  - subst q1. rewrite plift_empty in *. contradiction.
  - assert (exists TF, indexr x0 (G'++(T0, fr0, q0)::G) = Some TF) as TY.
    rewrite indexr_var_some. rewrite app_length. simpl. lia.
    destruct TY as [[[T' fr'] q'] ?].
    destruct (W1 x0 T' fr' q') as [vx1 [vx2 [CLQ [IX1 [IX21 [IX22 [IX23 [IV [? ?]]]]]]]]]. eauto. 
    eapply valt_deep_wf in IV. eapply IV. 
    eapply IX21 in LT1 as A. eapply lls_var in H3. 
    destruct H3 as (? & ? & ?). rewrite IX21 in H3. inversion H3.
    subst x1. eauto. eauto. eauto.
  - assert (exists TF, indexr (x0+1) (G'++(T0, fr0, q0)::G) = Some TF) as TY.
    rewrite indexr_var_some. rewrite app_length. simpl. eapply P1 in GT2. unfoldq; intuition.
    repeat rewrite app_length in * . simpl in *. lia.
    destruct TY as [[[T' fr'] q'] ?].
    destruct (W1 (x0+1) T' fr' q') as [vx1 [vx2 [CLQ [IX1 [IX21 [IX22 [IX23 [IV [? ?]]]]]]]]]. eauto. 
    eapply valt_deep_wf in IV. eapply IV.
    eapply lls_var in H3. destruct H3 as [? [? ?]].
    bdestruct (x0+1 =? length G); intuition.
    bdestruct (length G <? x0+1); intuition.
    replace (x0+1-1) with x0 in H12. rewrite H3 in H12.
    inversion H12. subst. auto. lia. auto.
Qed.

Lemma envt_subst_filter_deep: forall M H1 H2 H1' H2' S1 S2 G G' p q q1 v1 v2'0 T0 fr0 q0
  (LL1: length H1 = length G)
  (LL2: length H2 = length G)
  (LL3: length H1' = length G')
  (LL4: length H2' = length G')
  (EMP: q1 = qempty)
  (V1: val_locs v1 = pempty)
  (V2: val_locs v2'0 = pempty),
  store_type S1 S2 M ->
  env_type_subst2 M (H1' ++ v1 :: H1) (H2' ++ H2) (G' ++ (T0, fr0, q0) :: G) p (length G) v2'0 q1 ->
  psub q (plift p) ->
  st_filter M (locs_locs_stty (st1 M) (vars_locs (H1' ++ v1 :: H1) q)) (locs_locs_stty (st2 M) (vars_locs (H2'++H2) (subst_pl q (length H2) (plift q1)))).
Proof. 
  intros. eapply envt_subst_store_deep_wf1 with (q := q) in H0 as H0'; auto.
  eapply envt_subst_store_deep_wf2 with (q := q) in H0 as H0''; auto.
  remember H as ST'. clear HeqST'. destruct H as [SST1 [SST2 [ST [R L]]]].
  destruct H0 as [? [? [? [? [W1 [W2 W3]]]]]].
  repeat split; auto. 
  + intros. eapply lls_vars in H7. destruct H7 as [? [? ?]].
    eapply lls_var in H8. destruct H8 as [? [? ?]].    
    assert (x < length (G' ++ (T0, fr0, q0) :: G)). { apply indexr_var_some' in H8. repeat rewrite app_length in *. lia. }
    eapply indexr_var_some in H10. destruct H10 as [[[T frt] qt] ?].
    destruct (W1 x T frt qt) as [v1' [v2' [? [IX1 [IX21 [IX22 [IX23 [VT [? ?]]]]]]]]]; auto.
    rewrite IX1 in H8. inversion H8. subst x0. 
    eapply valt_same_locs_deep in VT; eauto. eapply VT in H9. 
    bdestruct (x <? length G); intuition.
    eapply lls_var'  in H18; eauto.
    eapply lls_vars'; eauto. unfold subst_pl. right. right. split; auto. lia.
    bdestruct (x =? length G); intuition. subst v2'0. rewrite V2 in *. rewrite lls_empty in H9. unfoldq; intuition.
    assert (x > length G); intuition.
    eapply lls_var'  in H16; eauto.
    eapply lls_vars'; eauto. unfold subst_pl. right. left. split; eauto. lia. replace (x -1+1) with x. auto. lia.
  + eapply substp_sub' with (m := (length H2)) (q1 := (plift q1)) in H3 as H3'.
    intros.  
    eapply lls_vars in H7. destruct H7 as [? [? ?]]. eapply H3' in H7 as H7'.
    eapply lls_var in H8. destruct H8 as [? [? ?]].
    assert (q (length G) /\ plift q1 x \/
            length G > x    /\ q x  \/
            length G <= x   /\ q (x + 1)) as CASES. {
      rewrite LL2 in H7. destruct H7 as [[? A]|B].        
    - (* p (len G) *)
      destruct A as [[AA | AB] | AC].
      + (* len G <= x0 /\ p (x0 + 1) *) eauto. 
      + (* len G > x0 /\ p x0 *) eauto. 
      + (* q1 x0 *) eauto. 
    - destruct B as [BA | BB].
      + (* len G <= x0 /\ p (x0+1) *) eauto. 
      + (* len G > x0 /\ p x0 *) eauto. 
    }
    
  destruct CASES as [[EQ1 EQ2] | [[LT1 LT2] | [GT1 GT2]]].
  - subst q1. rewrite plift_empty in *. contradiction.
  - assert (exists TF, indexr x (G'++(T0, fr0, q0)::G) = Some TF) as TY.
    rewrite indexr_var_some. rewrite app_length. simpl. lia.
    destruct TY as [[[T' fr'] q'] ?].
    destruct (W1 x T' fr' q') as [vx1 [vx2 [CLQ [IX1 [IX21 [IX22 [IX23 [VT [? ?]]]]]]]]]. eauto.
    intuition.
    assert ((plift p) x). { eapply H3. auto. } 
    rewrite H8 in H13. inversion H13. subst x0.
    eapply VT in H14 as H14'. eapply valt_same_locs_deep in H14'; eauto.
    eapply H14' in H9.  eapply lls_var' in H9; eauto. eapply lls_vars'; eauto.   
  - assert (exists TF, indexr (x+1) (G'++(T0, fr0, q0)::G) = Some TF) as TY.
    rewrite indexr_var_some. rewrite app_length. simpl. eapply H3 in GT2. eapply H4 in GT2. unfoldq; intuition.
    repeat rewrite app_length in * . simpl in *. lia.
    destruct TY as [[[T' fr'] q'] ?].
    destruct (W1 (x+1) T' fr' q') as [vx1 [vx2 [CLQ [IX1 [IX21 [IX22 [IX23 [VT [? ?]]]]]]]]]. eauto. 
    assert (x + 1 > length G). { lia. } replace (x+1-1) with x in IX23. 
    rewrite H8 in IX23. intuition. inversion H14. subst x0.
    eapply valt_same_locs_deep in VT; eauto.
    eapply VT in H9. eapply lls_var' in H9; eauto. eapply lls_vars'; eauto.
    lia.
Qed.

Lemma envt_subst_same_locs: forall S1 S2 M H1 H2 G p p1 l1 l2 H1' H2' v1 G' T0 v2'0 q1 fr0 q0
    (LL1: length H1 = length G)
    (LL2: length H2 = length G)
    (LL3: length H1' = length G')
    (LL4: length H2' = length G')
    (EMP: q1 = qempty)
    (V1: val_locs v1 = pempty)
    (V2: val_locs v2'0 = pempty),
    store_type S1 S2 M ->
    env_type_subst2 M (H1' ++ v1 :: H1) (H2' ++ H2) (G' ++ (T0, fr0, q0) :: G) p (length G) v2'0 q1 ->
    strel M l1 l2 ->
    psub (plift p1) (plift p) ->
    locs_locs_stty (st1 M) (vars_locs (H1' ++ v1 :: H1) (plift p1)) l1 <-> (locs_locs_stty (st2 M) (vars_locs (H2' ++ H2) (subst_pl (plift p1) (length H2) (plift q1)))) l2.
Proof. 
  intros.
  remember (locs_locs_stty (st1 M) (vars_locs (H1' ++ v1 :: H1) (plift p1))) as A.
  remember (locs_locs_stty (st2 M) (vars_locs (H2' ++ H2) (subst_pl (plift p1) (length H2) (plift q1)))) as B. 
  assert (st_filter M A B). {
    subst A B. eapply envt_subst_filter_deep; eauto.
  }
  subst A B. eapply H5. auto.
Qed.
  
Lemma envt_subst_tighten: forall M H1 H2 G m v p q p',
  env_type_subst2 M H1 H2 G p m v q ->
  psub (plift p')(plift p)  ->
  env_type_subst2 M H1 H2 G p' m v q.
Proof.
  intros. 
  destruct H as [L1 [L2 [PD1 [PD2 [P1 [P2 P3]]]]]].
  unfold env_type_subst2; intuition.
  + simpl. unfoldq; intuition.
  + simpl. eapply substp_sub with (m := m) (q1 := q) in H0 as H0'.
  rewrite plift_subst in *. unfoldq; intuition.
  eapply H0' in  H.  eapply PD2. rewrite plift_subst in H. auto.
  + destruct (P1 x T fr q0) as [v1 [v2 [? [? [? [? [? ?]]]]]]]; eauto.
    exists v1, v2; intuition.
    eapply H14. intuition. unfoldq; intuition.
    eapply H8. intuition. unfoldq; intuition.
    
  + eapply P2. unfoldq; intuition. unfoldq; intuition. unfoldq; intuition.
  + eapply P3. 1-3: eapply substp_sub with (m := m) (q1 := q) in H0 as H0'; repeat rewrite plift_subst in *. 
    unfoldq; intuition. unfoldq; intuition. unfoldq; intuition.
Qed.


Lemma has_type_closed_subst: forall M H1 H2 G p m v fr q q0 T e t,
  env_type_subst2 M H1 H2 G p m v q0 ->
  has_type G t T p fr q e ->
  (
    closed_ty (length G) T /\
    closed_ql (length G) p /\
    closed_ql (length G) q /\
    closed_ql (length G) e
  ).
Proof.
  intros. eapply filter_closed_subst in H as H'.  induction H0; intuition.
  + destruct H as [? [? [? [? [? [? ?]]]]]]. destruct (H7 x T fr q) as [? [? [? [? ?]]]]; auto.
    bdestruct (x <? m); intuition.  eapply valt_closed in H18. rewrite <- H.  intuition.
    eapply valt_closed in H18. rewrite <- H.  intuition.
  + unfold closed_ql. intros. unfold qone in H4. bdestruct (x0 =? x); intuition.
    apply indexr_var_some' in H0. lia.
  + inversion H4. subst. auto.
  + inversion H4. subst. auto.
  + inversion H3. subst. auto.
  + inversion H4. subst. auto.
  + eapply closedq_or; intuition. eapply closedq_sub. 2: eapply H3. auto.
    intros ? ?. destruct rf1; simpl in H7. eapply H6 in H7. lia. intuition.
  + eapply closedq_or; intuition. eapply closedq_or; intuition.
  + inversion H6. subst. auto. 
  + inversion H6. subst. eapply closedq_or; intuition. 
    intros ? ?. destruct fn2; simpl in H13. eapply H9. auto. intuition.
    eapply closedq_or; intuition.
    intros ? ?. destruct ar2; simpl in H13. eapply H12. auto. intuition.
  + inversion H6. subst. eapply closedq_or; intuition. eapply closedq_or; intuition.
    eapply closedq_or; intuition. eapply closedq_or; intuition. 
    intros ? ?. destruct e2f; simpl in H13. eapply H9. auto. intuition.
    intros ? ?. destruct e2x; simpl in H13. eapply H12. auto. intuition.
  + constructor; intuition. 
  + assert (env_type_subst2 M H1 H2 env p1 m v q0). eapply envt_subst_tighten; eauto. 
    assert (env_type_subst2 M H1 H2 env p2 m v q0). eapply envt_subst_tighten. 2: eauto. auto.
    assert (closed_ql (length env) p1). eapply closedq_sub; eauto. 
    assert (closed_ql (length env) p2). eapply closedq_sub. 2: eauto. auto.
    intuition. eapply closedq_or; intuition. 
  + eapply closedq_or; intuition. 
    intros ? ?. eapply H8. unfold qdiff in H9. apply andb_true_iff in H9. intuition.
    intros ? ?. eapply H5 in H9. eapply H7. intuition. 
Qed.
    
Lemma envt_subst_store_change: forall M M' S1 S2 H1 H1' v1 H2 H2' G G' T0 fr0 q0 p v2'0 q1
    (WFE: env_type_subst2 M (H1' ++ v1 :: H1) (H2' ++ H2) (G' ++  (T0, fr0, q0) :: G) p (length G) v2'0 q1)
    (ST: store_type S1 S2 M)
    (LL1: length H1 = length G)
    (LL2: length H2 = length G)
    (LL3: length H1' = length G')
    (LL4: length H2' = length G')
    (V1: val_locs v1 = pempty)
    (V2: val_locs v2'0 = pempty)
    (Q1: q1 = qempty),
    st_chain_partial M M' (locs_locs_stty (st1 M) (vars_locs (H1' ++ v1 :: H1)  (plift p))) (locs_locs_stty (st2 M) (vars_locs (H2' ++ H2) (subst_pl (plift p) (length H2) (plift q1)))) ->
    env_type_subst2 M' (H1' ++ v1 :: H1) (H2' ++ H2) (G' ++  (T0, fr0, q0) :: G) p (length G) v2'0 q1.
Proof.
  intros. remember WFE as WFE'. clear HeqWFE'. destruct WFE' as [L1 [L2 [P1 [P2 [W1 [W2 W3]]]]]]. 
  repeat split; auto. intros.
  destruct (W1 _ _ _ _ H0) as [vx1 [vx2 [CLQ [IH1 [IH2A [IH2B [IH2C [HVX ?]]]]]]]]; intuition.
  exists vx1, vx2; intuition.
  - eapply valt_store_change in H6; eauto.
    eapply stchain_tighten. eapply valt_filter; eauto. eauto. 
    intros ? Q. eapply lls_vars'; eauto. eapply lls_var'; eauto.
    intros ? Q.
    bdestruct (x =? length G). 
    intuition. subst v2'0. subst x.
    rewrite V2 in Q. rewrite lls_empty in Q. unfoldq; intuition.

    bdestruct (x <? length G). eapply IH2A in H8 as H8'. eauto.
    eapply lls_vars'; eauto. eapply lls_var'; eauto.
    unfold subst_pl. right. right. intuition.

    bdestruct (length G <? x); intuition. 
    eapply lls_vars'; eauto. eapply lls_var'; eauto.
    unfold subst_pl. right. left. intuition. replace (x -1 +1) with x. auto. intuition.
  - intros ? ?. erewrite <- lls_change with (M := (st1 M)) in H8. eapply H4 in H8.
    erewrite <- lls_change; eauto. 
    eapply stchain_tighten; eauto. eapply envt_subst_filter_deep; eauto.
    eapply lls_mono. eapply vars_locs_mono; eauto.
    eapply lls_mono. eapply vars_locs_mono; eauto. eapply substp_sub'; eauto.
    eapply stchain_tighten; eauto. eapply valt_filter; eauto. 
    intros ? ?. eapply H4 in H10. eapply lls_mono; eauto. eapply vars_locs_mono; eauto.
    intros ? ?. eapply H9 in H10. eapply lls_mono; eauto. eapply vars_locs_mono; eauto.
    rewrite <- LL2. eapply substp_sub'; eauto. 
  
  - intros ? ?. erewrite <- lls_change with (M := (st2 M)) in H8. eapply H9 in H8.
    erewrite <- lls_change; eauto. 
    eapply stchain_tighten; eauto. rewrite <- LL2. eapply envt_subst_filter_deep. 9: eauto. all: eauto.
    eapply lls_mono. eapply vars_locs_mono; eauto.
    eapply lls_mono. eapply vars_locs_mono; eauto. rewrite <- LL2. eapply substp_sub'; eauto.
    eapply stchain_tighten; eauto. eapply valt_filter; eauto. 
    intros ? ?. eapply H4 in H10. eapply lls_mono; eauto. eapply vars_locs_mono; eauto. 
    intros ? ?. eapply H9 in H10. eapply lls_mono; eauto. eapply vars_locs_mono; eauto.
    rewrite <- LL2. eapply substp_sub'; eauto. 

  - intros. eapply W2 in H4 as H4'; eauto. intros ? ?.
    erewrite <- lls_change with (M := (st1 M))(M' := (st1 M')) in H5.
    erewrite <- lls_change with (M := (st1 M))(M' := (st1 M')) in H5.
    eapply H4' in H5.
    erewrite <- lls_change; eauto.
    eapply stchain_tighten.  eapply envt_subst_filter_deep; eauto. eauto. 
    eapply lls_mono. eapply vars_locs_mono; eauto.
    eapply lls_mono. eapply vars_locs_mono; eauto. 
    eapply substp_sub'; eauto. 
    eapply stchain_tighten. eapply envt_subst_filter_deep; eauto. eauto.
    eapply lls_mono. eapply vars_locs_mono; eauto.
    eapply lls_mono. eapply vars_locs_mono; eauto. eapply substp_sub'; eauto.
    eapply stchain_tighten. eapply envt_subst_filter_deep; eauto. eauto.
    eapply lls_mono. eapply vars_locs_mono; eauto.
    eapply lls_mono. eapply vars_locs_mono; eauto. 
    eapply substp_sub'; eauto.

  - intros. eapply W3 in H4 as H4'; eauto. intros ? ?.
    erewrite <- lls_change with (M := (st2 M))(M' := (st2 M')) in H5.
    erewrite <- lls_change with (M := (st2 M))(M' := (st2 M')) in H5.
    eapply H4' in H5.
    erewrite <- lls_change; eauto. 
    eapply stchain_tighten. rewrite <- LL2. eapply envt_subst_filter_deep. 9: eapply WFE. all: eauto.
    eapply lls_mono. eapply vars_locs_mono; eauto. 
    eapply lls_mono. eapply vars_locs_mono; eauto. 
    rewrite <- LL2. eapply substp_sub'; eauto.
    rewrite <- LL2. eapply stchain_tighten. eapply envt_subst_filter_deep. 9: eapply WFE. all: eauto.
    eapply lls_mono. eapply vars_locs_mono; eauto. 
    eapply lls_mono. eapply vars_locs_mono; eauto. eapply substp_sub'; eauto.
    rewrite <- LL2. eapply stchain_tighten. eapply envt_subst_filter_deep. 9: eapply WFE. all: eauto. 
    eapply lls_mono. eapply vars_locs_mono; eauto.
    eapply lls_mono. eapply vars_locs_mono; eauto. 
    eapply substp_sub'; eauto.
Qed.


Lemma envt_subst_store_extend: forall M M' S1 S2 H1 H1' v1 H2 H2' G G' T0 fr0 q0 p v2'0 q1
    (LL1: length H1 = length G)
    (LL2: length H2 = length G)
    (LL3: length H1' = length G')
    (LL4: length H2' = length G')
    (EMP: q1 = qempty)
    (V1: val_locs v1 = pempty)
    (V2: val_locs v2'0 = pempty),
    env_type_subst2 M (H1' ++ v1 :: H1) (H2' ++ H2) (G' ++ (T0, fr0, q0) :: G) p (length G) v2'0 q1 ->
    store_type S1 S2 M ->
    st_chain M M' ->
    env_type_subst2 M' (H1' ++ v1 :: H1) (H2' ++ H2) (G' ++ (T0, fr0, q0) :: G) p (length G) v2'0 q1.
Proof.
  intros. remember H as H'. clear HeqH'. destruct H' as [L1 [L2 [P1 [P2 [W1 [W2 W3]]]]]]. 
  repeat split; auto. intros.
  destruct (W1 _ _ _  _ H4) as [vx1 [vx2 [IH1 [IH2 [? [? HVX]]]]]]; intuition.
  assert (st_chain_partial M M' (locs_locs_stty (st1 M) (vars_locs (H1' ++ v1 :: H1) (plift p)))  (locs_locs_stty (st2 M) (vars_locs (H2' ++ H2) (subst_pl (plift p) (length H2) (plift q1))))). {
    eapply stchain_tighten; eauto. eapply envt_subst_filter_deep; eauto. unfoldq; intuition. 
    eapply envt_subst_store_deep_wf1; eauto. unfoldq; intuition.
    eapply envt_subst_store_deep_wf2; eauto. unfoldq; intuition.
  }
  assert (fr = false -> psub (plift q) (plift p) -> st_chain_partial M M' (locs_locs_stty (st1 M) (vars_locs (H1' ++ v1 :: H1) (plift q)))  (locs_locs_stty (st2 M) (vars_locs (H2' ++ H2) (subst_pl (plift q) (length H2) (plift q1))))). {
    intros ?. intuition.
    eapply stchain_tighten; eauto. eapply envt_subst_filter_deep; eauto. 
    eapply lls_mono; auto. eapply vars_locs_mono; eauto.
    eapply lls_mono; auto. eapply vars_locs_mono; eauto. eapply substp_sub'; eauto.
  }

  assert ((plift p) x -> fr = false -> psub (plift q) (plift p) -> st_chain_partial M M' (locs_locs_stty (st1 M) (val_locs vx1))  (locs_locs_stty (st2 M) (val_locs vx2))). {
    intros ? ?. intuition.
    eapply stchain_tighten; eauto. eapply valt_filter; eauto. rewrite LL2. auto.
  }

  exists vx1, vx2; intuition.
  + eapply valt_store_extend in H15; eauto. 
  + erewrite <- lls_change1. intros ? ?. erewrite <- lls_change1. eauto. eauto. eauto.
  + erewrite <- lls_change2. intros ? ?. erewrite <- lls_change2. eauto. rewrite <- LL2. eauto. eauto.
  + intros. erewrite <- lls_change1. 
    2: { eapply stchain_tighten. eapply envt_subst_filter_deep. all: eauto. 
         eapply lls_closed'; eauto. destruct H0; eauto. eapply envt_subst_store_wf1; eauto.
         eapply lls_closed'; eauto. destruct H0 as [? [? ?]]; eauto. eapply envt_subst_store_wf2; eauto.
         eapply substp_sub'; eauto.
    }
    replace (locs_locs_stty (st1 M') (vars_locs (H1' ++ v1 :: H1) q')) with (locs_locs_stty (st1 M) (vars_locs (H1' ++ v1 :: H1) q')).
    2:{ eapply lls_change. eapply stchain_tighten. eapply envt_subst_filter_deep; eauto. eauto. 
        eapply lls_closed'; eauto. destruct H0; eauto. eapply envt_subst_store_wf1; eauto.
        eapply lls_closed'; eauto. destruct H0 as [? [? ?]]; eauto. eapply envt_subst_store_wf2; eauto.
        eapply substp_sub'; eauto. }
    replace (locs_locs_stty (st1 M') (vars_locs (H1' ++ v1 :: H1) (pand (vars_trans (G' ++ (T0, fr0, q0) :: G) q) (vars_trans (G' ++ (T0, fr0, q0) :: G) q')))) with 
            (locs_locs_stty (st1 M) (vars_locs (H1' ++ v1 :: H1) (pand (vars_trans (G' ++ (T0, fr0, q0) :: G) q) (vars_trans (G' ++ (T0, fr0, q0) :: G) q')))).
    2: { eapply lls_change. eapply stchain_tighten. eapply envt_subst_filter_deep; eauto. eauto. 
         eapply lls_closed'; eauto. destruct H0; eauto. eapply envt_subst_store_wf1; eauto.
         eapply lls_closed'; eauto. destruct H0 as [? [? ?]]; eauto. eapply envt_subst_store_wf2; eauto.
         eapply substp_sub'; eauto. }        
    eapply W2; eauto.     
    
  + intros. erewrite <- lls_change2. 
    2: { rewrite <- LL2. eapply stchain_tighten. eapply envt_subst_filter_deep. 9: eapply H. all: eauto.
         eapply lls_closed'; eauto. destruct H0; eauto. eapply envt_subst_store_wf1; eauto.
         eapply lls_closed'; eauto. destruct H0 as [? [? ?]]; eauto. eapply envt_subst_store_wf2; eauto.
         eapply substp_sub'; eauto.
      }
    replace (locs_locs_stty (st2 M') (vars_locs (H2'++H2) (subst_pl q' (length G) (plift q1)))) with (locs_locs_stty (st2 M) (vars_locs (H2'++H2) (subst_pl q' (length G) (plift q1)))).
    2:{ rewrite <- LL2. eapply lls_change2. eapply stchain_tighten. eapply envt_subst_filter_deep. 9: eapply H. all: eauto. 
        eapply lls_closed'; eauto. destruct H0; eauto. eapply envt_subst_store_wf1; eauto.
        eapply lls_closed'; eauto. destruct H0 as [? [? ?]]; eauto. eapply envt_subst_store_wf2; eauto.
        eapply substp_sub'; eauto. }
    replace (locs_locs_stty (st2 M') (vars_locs (H2'++H2) (subst_pl (pand (vars_trans (G' ++ (T0, fr0, q0) :: G) q) (vars_trans (G' ++ (T0, fr0, q0) :: G) q')) (length G) (plift q1)))) with 
            (locs_locs_stty (st2 M) (vars_locs (H2'++H2) (subst_pl (pand (vars_trans (G' ++ (T0, fr0, q0) :: G) q) (vars_trans (G' ++ (T0, fr0, q0) :: G) q')) (length G) (plift q1)))).
    2: { rewrite <- LL2. eapply lls_change. eapply stchain_tighten. eapply envt_subst_filter_deep. 9: eapply H. all: eauto.
         eapply lls_closed'; eauto. destruct H0; eauto. eapply envt_subst_store_wf1; eauto.
         eapply lls_closed'; eauto. destruct H0 as [? [? ?]]; eauto. eapply envt_subst_store_wf2; eauto.
         eapply substp_sub'; eauto. }        
  eapply W3; eauto.   
Qed.

Lemma valt_filter_subst: forall T T' v1' v2' M H1 v1 H1' H2 H2',
  val_type M (H1' ++ v1 :: H1) (H2' ++ H2)  v1' v2' T T' ->
  st_filter M (locs_locs_stty (st1 M) (val_locs v1')) (locs_locs_stty (st2 M) (val_locs v2')).
Proof. 
  intros T. induction T; intros; destruct T'; destruct v1'; destruct v2'; unfold st_filter; simpl in *; intuition.
  + repeat rewrite val_locs_bool. rewrite lls_empty. unfoldq; intuition.
  + repeat rewrite val_locs_bool. rewrite lls_empty. unfoldq; intuition.
  + repeat rewrite val_locs_bool in *. rewrite lls_empty in  *. unfoldq; intuition.
  + repeat rewrite val_locs_bool in *. rewrite lls_empty in  *. unfoldq; intuition.
  + eapply H8.
  + eapply H8.
  + eapply H8; eauto.
  + eapply H8; eauto.
  + eapply H11; eauto.
  + eapply H11; eauto.
  + eapply H11; eauto.
  + eapply H11; eauto.
Qed.

Lemma envt_subst_valq_store_change1: forall M M' M'' S1 S2 G H1 H1' v1 H2' H2 G' T0 fr0 q0 v2'0 q1 v1' v2' T T' fr p q
    (WFE: env_type_subst2 M' (H1' ++ v1 :: H1)  (H2' ++ H2) (G' ++ (T0, fr0, q0) :: G) p (length G) v2'0 q1)
    (ST: store_type S1 S2 M')
    (VT: val_type M' (H1' ++ v1 :: H1) (H2' ++ H2) v1' v2' T T')
    (VQ: val_qual (st1 M) (st1 M') (H1' ++ v1 :: H1) v1' fr (pand (plift p) q))
    (LL1: length H1 = length G)
    (LL2: length H2 = length G)
    (LL3: length H1' = length G')
    (LL4: length H2' = length G')
    (EMP: q1  = qempty)
    (V1: val_locs v1 = pempty)
    (V2: val_locs v2'0 = pempty), 
    st_chain M' M'' ->
    val_qual (st1 M) (st1 M'') (H1' ++ v1 :: H1) v1' fr (pand (plift p) q).
Proof.
  intros. intros ? ?.
  assert (locs_locs_stty (st1 M') (val_locs v1') x). {
    erewrite lls_change. eauto.
    eapply stchain_tighten; eauto. eapply valt_filter_subst; eauto.
    1,2: eapply valt_deep_wf in VT; intuition.
  }
  destruct (VQ x H3). {
    left. erewrite <-lls_change. eauto.
    eapply stchain_tighten; eauto. eapply envt_subst_filter_deep; eauto.
    intros ? ?. unfoldq; intuition.
    eapply envt_subst_store_deep_wf1; eauto; unfoldq; intuition.
    eapply envt_subst_store_deep_wf2; eauto; unfoldq; intuition. 
  } {
    right. destruct fr; try contradiction. 
    simpl in *. auto.
  }
Qed.


Lemma envt_subst_valq_store_change2: forall M M' M'' S1 S2 G H1 H1' v1 H2' H2 G' T0 fr0 q0 v2'0 q1 v1' v2' T T' fr p q
    (WFE: env_type_subst2 M' (H1' ++ v1 :: H1)  (H2' ++ H2) (G' ++ (T0, fr0, q0) :: G) p (length G) v2'0 q1)
    (ST: store_type S1 S2 M')
    (VT: val_type M' (H1' ++ v1 :: H1) (H2' ++ H2) v1' v2' T T')
    (VQ: val_qual (st2 M) (st2 M') (H2' ++ H2) v2' fr (subst_pl (pand (plift p) q) (length H2) (plift q1)))
    (LL1: length H1 = length G)
    (LL2: length H2 = length G)
    (LL3: length H1' = length G')
    (LL4: length H2' = length G')
    (EMP: q1  = qempty)
    (V1: val_locs v1 = pempty)
    (V2: val_locs v2'0 = pempty), 
    st_chain M' M'' ->
    val_qual (st2 M) (st2 M'') (H2' ++ H2) v2' fr (subst_pl (pand (plift p) q) (length H2) (plift q1)).
Proof.
  intros. intros ? ?.
  assert (locs_locs_stty (st2 M') (val_locs v2') x). {
    erewrite lls_change. eauto.
    eapply stchain_tighten; eauto. eapply valt_filter_subst; eauto.
    1,2: eapply valt_deep_wf in VT; intuition.
  }
  destruct (VQ x H3). {
    left. erewrite <-lls_change. eauto.
    eapply stchain_tighten; eauto. eapply envt_subst_filter_deep. 9: eauto. all: eauto. 
    intros ? ?. unfoldq; intuition.
    eapply envt_subst_store_deep_wf1; eauto; unfoldq; intuition.
    eapply envt_subst_store_deep_wf2; eauto; unfoldq; intuition. 
  } {
    right. destruct fr; try contradiction. 
    simpl in *. unfold pdiff , pnat in *. intuition.
  }
Qed.


Lemma envt_subst_telescope: forall M H1' v1 H1 H2' H2 G' T0' fr0' q0' G p v2'0 q0,
  env_type_subst2 M (H1'++v1::H1) (H2'++ H2) (G'++(T0', fr0', q0')::G) p (length G) v2'0 q0 -> 
  telescope (G'++(T0', fr0', q0')::G).
Proof.
  intros. destruct H as (? & ? & ? & ? & ? & ? & ?).
  intros ? ? ? ? ?. edestruct H5 as (? & ? & ? & ? & ? & ?); eauto.
Qed.

Lemma envt_subst_extend_all: forall M M' S1 S2 H1 H1' v1 H2 H2' G G' p vx1 vx2 T1 q1 qf v2'0 T0' fr0' q0' q0 fr1
    (WFE: env_type_subst2  M (H1' ++ v1 :: H1)  (H2' ++ H2) (G' ++ (T0', fr0', q0') :: G) p (length G) v2'0 q0) 
    (ST: store_type S1 S2 M)
    (SC: st_chain_partial M M' (locs_locs_stty (st1 M) (vars_locs (H1' ++ v1 :: H1) (pand (plift p) (plift qf) ))) (locs_locs_stty (st2 M) (vars_locs (H2' ++ H2) (subst_pl (pand (plift p) (plift qf)) (length H2) (plift q0))))) 
    (VT: val_type M' (H1'++v1::H1) (H2'++H2) vx1 vx2 T1 (subst_ty T1 (length G) q0))
    (VQ1: psub (pand (locs_locs_stty (st1 M') (vars_locs (H1' ++ v1 :: H1) (plift qf))) (locs_locs_stty (st1 M') (val_locs vx1)))
      (locs_locs_stty (st1 M') (vars_locs (H1' ++ v1 :: H1) (plift q1))))
    (VQ2: psub (pand (locs_locs_stty (st2 M') (vars_locs (H2' ++ H2) (subst_pl (plift qf) (length H2) (plift q0)))) (locs_locs_stty (st2 M') (val_locs vx2)))
      (locs_locs_stty (st2 M') (vars_locs (H2' ++ H2) (subst_pl (plift q1) (length H2)(plift q0)))))  
    (A1: (fr1 = false -> psub (locs_locs_stty (st1 M') (val_locs vx1)) (locs_locs_stty (st1 M') (vars_locs (H1' ++ v1 :: H1) (plift q1)))))
    (A2: (fr1 = false -> psub (locs_locs_stty (st2 M') (val_locs vx2)) (locs_locs_stty (st2 M') (vars_locs (H2' ++ H2) (subst_pl (plift q1) (length H2)(plift q0))))))
    (LL1: length H1 = length G)
    (LL2: length H2 = length G)
    (LL3: length H1' = length G')
    (LL4: length H2' = length G')
    (EMP: q0  = qempty)
    (V1: val_locs v1 = pempty)
    (V2: val_locs v2'0 = pempty)
    (SUB1: psub (plift qf) (plift p))
    (SUB2: psub (plift q1) (plift qf)),
    closed_ty (length G'+ S (length G)) T1 ->
    closed_ql (length G'+ S (length G)) q1 ->
    env_type_subst2 M' (vx1 :: H1' ++ v1 :: H1) (vx2 :: H2' ++ H2) ((T1, fr1, q1) :: G' ++ (T0', fr0', q0') :: G) (qor qf (qone (length (G' ++ (T0', fr0', q0') :: G)))) (length G) v2'0 q0.
Proof.  
  intros.  
  remember WFE as WFE1. clear HeqWFE1.
  destruct WFE as [L1 [L2 [PD1 [PD2 [W1 [W2 W3]]]]]].
  assert (psub (plift p) (pdom (G' ++ (T0', fr0', q0') :: G))). { intros ? ?. unfold pdom in *. rewrite app_length in *. simpl in *. eapply PD1 in H3. lia.  }

  repeat split; eauto.
  - simpl. eauto.
  - simpl. eauto.
  - rewrite plift_or, plift_one. unfoldq. simpl. intuition. 
  - subst q0. rewrite plift_empty. rewrite app_length. simpl.
    rewrite <- LL4. rewrite <- LL2. replace (vx2::H2'++H2) with (([vx2]++H2')++H2).
    eapply Q2; eauto. rewrite plift_or, plift_one. intros ? ?. unfoldq; intuition. rewrite app_length in *. simpl in *. 
    eapply SUB1 in H5. eapply H3 in H5. lia. rewrite app_length. simpl. lia. simpl. auto.
  - intros.
    bdestruct (x =? length (G' ++ (T0', fr0', q0') :: G)); intuition. 
    + subst. rewrite indexr_head in H4. inversion H4. subst T1 fr1 q1.
      exists vx1, vx2. repeat split.
      intros. rewrite app_length. simpl. auto.
      rewrite app_length in *. simpl in *. rewrite app_length. simpl. bdestruct (length G' + S(length G) =? (length H1' + S(length H1))); intuition. 
      intros. rewrite app_length in *. simpl in *. rewrite app_length. simpl. bdestruct (length G' + S(length G) =? (length H2' + length H2)); intuition. 
      intros ?. rewrite app_length in *. simpl in *. lia.
      intros ?. simpl. repeat rewrite app_length in *. simpl in *.  bdestruct (length G' + S(length G) -1 =? (length H2' + length H2)); intuition. 
      intros. eapply valt_extend1; auto. rewrite app_length. simpl. rewrite LL1, LL3. auto. 
      rewrite <- LL2. rewrite app_length. eapply substy_closed_gen; eauto. rewrite LL2, LL4. auto.

      intros. intros ? ?. eapply A1 in H8. eapply lls_mono; eauto. intros ? ?. eapply vars_locs_extend1; eauto. auto.
      intros. intros ? ?. eapply A2 in H8. rewrite <- LL2. eapply lls_mono; eauto. intros ? ?. eapply vars_locs_extend1; eauto. auto.
    + rewrite indexr_skip in H4. 2: lia.
      assert (x < length (G' ++ (T0', fr0', q0') :: G)). { apply indexr_var_some' in H4. auto. }
      destruct (W1 _ _ _ _ H4) as [v1' [v2' [CL2 [IH1 [IH2A [IH2B [IH2C [VALT [FR1 FR2]]]]]]]]]; intuition.
      rewrite plift_or, plift_one.
      exists v1', v2'. intuition.
      rewrite indexr_skip. auto. lia.
      rewrite indexr_skip. auto. 
      rewrite app_length. lia. 
      rewrite indexr_skip. auto. apply indexr_var_some' in H8. lia. 
      assert (plift p x). { unfoldq; intuition. }
      eapply valt_extend1; eauto. 1,2: eapply valt_closed in VALT; intuition. eapply VALT in H8. 
      (* XXX store extend/tighten XXX *) {
        eapply valt_store_change. eapply ST. auto. 
        eapply stchain_tighten; eauto. eapply valt_filter; eauto.
        intros ? ?. eapply lls_mono; eauto. intros ? ?. exists x. intuition. unfoldq; intuition. eexists. eauto.
        { 
          intros ? ?. eapply lls_mono; eauto. intros ? ?.
          bdestruct (x <? length G). exists x. split. 2: { exists v2'. intuition. } 
          unfoldq. rewrite app_length in H7. simpl in H7. intuition.
          unfold subst_pl. right. right. intuition.

          bdestruct (x =? length G). intuition. subst v2'0. rewrite V2 in H9. rewrite lls_empty in H9. unfoldq; intuition.

          intuition. exists (x-1). split. 2: { exists v2'; intuition. }
          unfoldq. intuition. 
          unfold subst_pl. right. left. replace (x-1+1) with x. intuition. lia.
        }

      } {
        intros. intros ? ?.
        assert (psub (plift q) (plift qf)). {
          intros ? A. eapply CL2 in A as B. 
          eapply H9 in A. unfoldq; intuition.
        }
        assert ( plift p x). {
          destruct H8. unfoldq; intuition. unfoldq; intuition.  
        }
        assert (psub (plift q) (plift p)). {
          destruct H8. unfoldq; intuition. unfoldq; intuition.
        }
        erewrite lls_change with (M' := (st1 M')) in H10. eapply H10 in H12. rewrite <- vars_locs_extend with (H' := [vx1]) in H12. simpl in H12. 
        erewrite <- lls_change; eauto.
        rewrite lls_vars_shrink; auto. rewrite lls_vars_shrink in H12; auto. 
        eapply stchain_tighten; eauto. eapply envt_subst_filter_deep; eauto. 
        eapply lls_mono; eauto. intros ? ?. eapply vars_locs_mono; eauto. unfoldq; intuition.

        eapply lls_mono; eauto. eapply vars_locs_mono; eauto. eapply substp_sub'; eauto. unfoldq; intuition.
        unfoldq; intuition.
        auto.
        unfoldq; intuition.
        unfoldq; intuition.
        auto.
        auto.
        eapply sstchain_tighten. eapply SC.
        intuition. intros ? ?. eapply H11 in H10. 
        eapply lls_mono; eauto. eapply vars_locs_mono; eauto. unfoldq; intuition.
      }{
        intros. intros ? ?.
        rewrite lls_vars_shrink; eauto.
        assert (psub (plift q) (plift qf)). {
          intros ? A. eapply H9 in A as A'. destruct A'. auto. 
          unfold pone in H13. subst x1. eapply CL2 in A. unfoldq; intuition.
        }
        assert (plift p x). {
          destruct H8. unfoldq; intuition. unfoldq; intuition.  
        }
        assert (psub (plift q) (plift p)). {
          destruct H8. unfoldq; intuition. unfoldq; intuition.
        }
        intuition. erewrite <- lls_change with (M := (st2 M)) in H12. eapply H17 in H12. 
        erewrite <- lls_change; eauto.
        eapply sstchain_tighten. eapply SC. 
        eapply lls_mono; eauto. intros ? ?. eapply vars_locs_mono; eauto. rewrite LL2. eapply substp_sub'; eauto. unfoldq; intuition.
        eapply sstchain_tighten. eapply SC. intros ? ?.
        eapply H17 in H10.
        eapply lls_mono; eauto. intros ? ?. eapply vars_locs_mono; eauto. rewrite LL2. eapply substp_sub'; eauto. unfoldq; intuition.
        intros ? ?. unfold pdom. rewrite app_length.
        rewrite <- LL2 in H13. eapply substp_closed'; eauto.
        intros ? ?. eapply CL2 in H14. unfoldq; intuition. eapply SUB1 in H15. eapply H3 in H15.
        rewrite app_length in H15. simpl in H15. lia.
        subst. rewrite plift_empty. unfoldq; intuition.
        
      }  

  - (* 2nd invariant *)

    clear W1. (* distraction*)
    eapply envt_subst_telescope in WFE1 as TL1. 

    intros q q' QSUB QSUB' QSUBTR x (QQ & QQ').
    rewrite plift_or, plift_one in *.
    eapply lls_vars in QQ.
    eapply lls_vars in QQ'. 

    destruct QQ as (? & VTQ & VLQ).
    destruct QQ' as (? & VTQ' & VLQ').

    destruct (QSUB x0); intuition; destruct (QSUB' x1); intuition.

    + (* qf, qf *)

      assert (psub (pand (vars_trans (G' ++ (T0', fr0', q0') :: G) (pand (pdom (H1' ++ v1 :: H1)) q)) (vars_trans (G' ++ (T0', fr0', q0') :: G) (pand (pdom (H1' ++ v1 :: H1)) q'))) (plift qf)) as QSUBTR1. {
        intros ? [? ?]. destruct (QSUBTR x2) as [? | ?].
        split. (* extend *)
        eapply vt_extend. eapply vt_mono. 2: eapply H6. unfoldq. intuition.
        eapply vt_extend. eapply vt_mono. 2: eapply H7. unfoldq. intuition.
        eauto.
        eapply vt_closed in H6 as CL; eauto. unfoldq. intuition. unfoldq. intuition. (* contra *)
      }

      eassert _ as W4. {
        eapply (W2 (pand (pdom (H1' ++ v1 :: H1)) q) (pand (pdom (H1' ++ v1 :: H1)) q')) with (x:=x).

        intros ? ?. destruct (QSUB x2) as [? | ?]. unfoldq. intuition. 
        eauto. eauto. unfoldq. lia.

        intros ? ?. destruct (QSUB' x2) as [? | ?]. unfoldq. intuition. 
        eauto. eauto. unfoldq. lia. 

        intros ? ?.  eapply QSUBTR1 in H6. eapply SUB1. auto.

        split.

        erewrite lls_change. 
        eapply lls_vars'. eapply lls_mono. 2: eapply VLQ. intros ? ?. eapply var_locs_shrink. eauto. unfoldq. intuition. unfoldq. intuition.
        eapply stchain_tighten. eapply envt_subst_filter_deep; eauto. 
        intros ? ?. destruct H6. unfoldq. eapply QSUB in H7. unfoldq; intuition. 
        eapply SC; eauto. eapply lls_mono. eapply vars_locs_mono. unfoldq. intuition. destruct (QSUB x2); eauto. lia. 
        eapply QSUB in H8. unfoldq; intuition.

        eapply lls_mono; eauto. eapply vars_locs_mono; eauto. eapply substp_sub'; eauto. 
        intros ? [? ?]. eapply QSUB in H7.  unfoldq; intuition.

        erewrite lls_change. 
        eapply lls_vars'. eapply lls_mono. 2: eapply VLQ'. intros ? ?. eapply var_locs_shrink. eauto. unfoldq. intuition. unfoldq. intuition.

        eapply stchain_tighten. eapply envt_subst_filter_deep; eauto. 
        intros ? ?. destruct H6. unfoldq. eapply QSUB' in H7. unfoldq; intuition. 
        eapply SC; eauto. eapply lls_mono. eapply vars_locs_mono. unfoldq. intuition. destruct (QSUB' x2); eauto. lia. 
        eapply QSUB' in H8. unfoldq; intuition.

        eapply lls_mono; eauto. eapply vars_locs_mono; eauto. eapply substp_sub'; eauto. unfoldq; intuition.
        eapply QSUB' in H8. unfoldq; intuition.
        eapply QSUB' in H8. unfoldq; intuition.

      }

      erewrite lls_change in W4.

      eapply lls_vars in W4. destruct W4 as (? & (? & ?) & ?). 

      eapply lls_vars'. eapply lls_mono. 2: eauto. intros ? ?. eapply var_locs_extend. eauto. split.
      eapply vt_extend. eapply vt_mono. 2: eapply H6. unfoldq. intuition.
      eapply vt_extend. eapply vt_mono. 2: eapply H7. unfoldq. intuition.

      eapply stchain_tighten. eapply envt_subst_filter_deep; eauto.  
      intros ? ?. eapply QSUBTR1 in H6. auto. eauto. 

      eapply lls_mono. eapply vars_locs_mono. 
      intros ? ?. eapply QSUBTR1 in H6. unfoldq; intuition. auto. 

      eapply lls_mono; eauto. eapply vars_locs_mono; eauto. 
      intros ? ?. eapply substp_sub' in QSUBTR1. eapply QSUBTR1 in H6. eapply substp_sub'; eauto. unfoldq; intuition.

    + (* qf, x *)
      unfold pone in H5. subst x1. 

      assert (psub (pand (vars_trans (G' ++ (T0', fr0', q0') :: G) (pand (pdom  (H1' ++ v1 :: H1)) q)) (vars_trans (G' ++ (T0', fr0', q0') :: G) (plift q1))) (plift qf)) as QSUBTR1. {
        intros ? [? ?]. destruct (QSUBTR x1) as [? | ?].
        split. {
          eapply vt_extend. eapply vt_mono. 2: eapply H5. unfoldq. intuition. (* extend q *)
        }{
          eapply vt_head. eauto. unfoldq; intuition.  eauto. eauto.  (* pick q1 *)
        }
        eauto.
        eapply vt_closed in H6; eauto. unfoldq. intuition.  unfoldq; intuition. (* contra *)
      }

      eassert _ as W4. {
        eapply (W2 (pand (pdom  (H1' ++ v1 :: H1)) q) (plift q1)) with (x:=x).

        intros ? ?. destruct (QSUB x1) as [? | ?]. unfoldq. intuition. 
        eauto. eauto. unfoldq. lia.

        unfoldq. intuition.

        intros ? ?. eapply QSUBTR1 in H5. eauto.

        split. 

        erewrite lls_change. 
        eapply lls_vars'. eapply lls_mono. 2: eapply VLQ. intros ? ?. eapply var_locs_shrink. eauto. unfoldq. intuition. unfoldq. intuition.
        eapply stchain_tighten. eapply envt_subst_filter_deep; eauto. unfoldq; intuition. eapply QSUB in H7. unfoldq; intuition.
        eauto. eapply lls_mono. eapply vars_locs_mono. unfoldq. intuition. destruct (QSUB x1); eauto. lia. eapply QSUB in H7. unfoldq; intuition.
        eapply lls_mono. eapply vars_locs_mono. eapply substp_sub'; eauto. unfoldq. intuition. destruct (QSUB x1); eauto. lia. eapply QSUB in H7. unfoldq; intuition.

        erewrite lls_change.
        eapply VQ1. split.
        eapply lls_vars'. eapply lls_mono. 2: eapply VLQ. intros ? ?. eapply var_locs_shrink. eauto. unfoldq. intuition. auto. 

        eapply lls_var in VLQ'. destruct VLQ' as (? & IX & ?). rewrite <- L1 in IX.
        rewrite indexr_head in IX. inversion IX. eauto.
        eapply stchain_tighten. eapply envt_subst_filter_deep; eauto. unfoldq; intuition. eauto.
        eapply lls_mono. eapply vars_locs_mono. unfoldq. intuition.
        eapply lls_mono. eapply vars_locs_mono. eapply substp_sub'; eauto. unfoldq. intuition.
      }


      erewrite lls_change in W4.

      eapply lls_vars in W4. destruct W4 as (? & (? & ?) & ?). 

      eapply lls_vars'. eapply lls_mono. 2: eauto. intros ? ?. eapply var_locs_extend. eauto. split.
      eapply vt_extend. eapply vt_mono. 2: eapply H5. unfoldq. intuition.
      eapply vt_head. eauto. 
      intros ? ?. eapply SUB2 in H8. eapply SUB1 in H8. eapply H3 in H8. auto.
      eauto. eauto. 

      eapply stchain_tighten. eapply envt_subst_filter_deep; eauto.
      intros ? ?. eapply QSUBTR1 in H5. auto. eauto. 
      eapply lls_mono. eapply vars_locs_mono. intros ? ?. eapply QSUBTR1 in H5. unfoldq; intuition.
      eapply lls_mono. eapply vars_locs_mono. intros ? ?. eapply substp_sub' in QSUBTR1. eapply QSUBTR1 in H5. 
      eapply substp_sub'; eauto. unfoldq; intuition.


    + (* x, qf *)
      unfold pone in H4. subst x0. 

      assert (psub (pand (vars_trans (G' ++ (T0', fr0', q0') :: G) (plift q1)) (vars_trans (G' ++ (T0', fr0', q0') :: G) (pand (pdom ( H1' ++ v1 :: H1)) q'))) (plift qf)) as QSUBTR1. {
        intros ? [? ?]. destruct (QSUBTR x0) as [? | ?].
        split. {
          eapply vt_head. eauto. 
          intros ? ?. eapply SUB2 in H7. eapply SUB1 in H7. eapply H3 in H7. auto.
          auto. auto.  (* pick q1 *)
        }{
          eapply vt_extend. eapply vt_mono. 2: eapply H6. unfoldq. intuition. (* extend q' *)
        }
        eauto.
        eapply vt_closed in H6; eauto. unfoldq. intuition. unfoldq. intuition. (* contra *)
      }

      eassert _ as W4. {
        eapply (W2 (plift q1) (pand (pdom (H1' ++ v1 :: H1)) q')) with (x:=x).

        unfoldq. intuition.

        intros ? ?. destruct (QSUB' x0) as [? | ?]. unfoldq. intuition. 
        eauto. eauto. unfoldq. lia.

        intros ? ?. eapply QSUBTR1 in H4. eauto.

        split. 
        erewrite lls_change.
        eapply VQ1. split.
        eapply lls_vars'. eapply lls_mono. 2: eapply VLQ'. intros ? ?. eapply var_locs_shrink. eauto. unfoldq. intuition. eauto. 

        eapply lls_var in VLQ. destruct VLQ as (? & IX & ?). rewrite <- L1 in IX.
        rewrite indexr_head in IX. inversion IX. eauto.
        eapply stchain_tighten. eapply envt_subst_filter_deep; eauto. unfoldq; intuition. eauto.
        eapply lls_mono. eapply vars_locs_mono. unfoldq. intuition.
        eapply lls_mono. eapply vars_locs_mono. eapply substp_sub'; eauto. unfoldq. intuition.

        erewrite lls_change. 
        eapply lls_vars'. eapply lls_mono. 2: eapply VLQ'. intros ? ?. eapply var_locs_shrink. eauto. unfoldq. intuition. unfoldq. intuition.
        eapply stchain_tighten. eapply envt_subst_filter_deep; eauto. unfoldq; intuition. eapply QSUB' in H7. unfoldq; intuition.
        eauto.
        eapply lls_mono. eapply vars_locs_mono. unfoldq. intuition. eapply QSUB' in H7. unfoldq; intuition. eapply QSUB' in H7. unfoldq; intuition.
        eapply lls_mono. eapply vars_locs_mono. eapply substp_sub'; eauto. unfoldq. intuition. eapply QSUB' in H7. unfoldq; intuition. eapply QSUB' in H7. unfoldq; intuition.
      }

      erewrite lls_change in W4.

      eapply lls_vars in W4. destruct W4 as (? & (? & ?) & ?). 

      eapply lls_vars'. eapply lls_mono. 2: eauto. intros ? ?. eapply var_locs_extend. eauto. split.
      eapply vt_head. eauto. unfoldq; intuition. eauto. eauto.

      eapply vt_extend. eapply vt_mono. 2: eapply H6. unfoldq. intuition.

      eapply stchain_tighten. eapply envt_subst_filter_deep; eauto. 
      intros ? ?. eapply QSUBTR1 in H4. auto. eauto. 
      eapply lls_mono. eapply vars_locs_mono. intros ? ?.  eapply QSUBTR1 in H4. unfoldq; intuition.
      eapply lls_mono. eapply vars_locs_mono. eapply substp_sub'; eauto. intros ? ?.  eapply QSUBTR1 in H4. unfoldq; intuition.

    + (* x, x *)
      unfold pone in H4, H5.
      subst x0 x1.

      eapply lls_vars'. eauto. split.
      left. eauto. left. eauto.
  - (* 3rd invariant *)
    clear W1. (* distraction*)
    eapply envt_subst_telescope in WFE1 as TL1. 
    rewrite plift_or, plift_one in *.
    intros q q' QSUB QSUB' QSUBTR x (QQ & QQ').


    eapply substp_sub' with (m := (length G))(q1 := (plift q0)) in QSUB as QSUB_subst.
    eapply substp_sub' with (m := (length G))(q1 := (plift q0)) in QSUB' as QSUB_subst'.


    eapply lls_vars in QQ.
    eapply lls_vars in QQ'. 

    destruct QQ as (? & VTQ & VLQ).
    destruct QQ' as (? & VTQ' & VLQ').

    assert (psub (subst_pl (plift qf) (length G) (plift q0)) (pdom (H2'++H2))) as CLQF. {
      intros ? ?. eapply substp_sub' in SUB1. eapply SUB1 in H4. unfoldq; intuition.
    }

  rewrite substp_or in *.

  destruct (QSUB_subst x0); intuition; destruct (QSUB_subst' x1); intuition.

  + (* qf, qf *)
    assert (psub (pand (vars_trans (G' ++ (T0', fr0', q0') :: G) (pand (pdom (H1' ++ v1 ::H1)) q)) 
                       (vars_trans (G' ++ (T0', fr0', q0') :: G) (pand (pdom (H1' ++ v1 ::H1)) q' ))) (pand (plift p) (plift qf))) as QSUBTR1. {
      intros ? [? ?]. destruct (QSUBTR x2) as [? | ?].
      split. (* extend *)
      eapply vt_extend. eapply vt_mono. 2: eapply H6. unfoldq. intuition.
      eapply vt_extend. eapply vt_mono. 2: eapply H7. unfoldq. intuition.
      unfoldq; intuition.
      eapply vt_closed in H6 as CL; eauto. unfoldq. lia. intuition. unfoldq. intuition. (* contra *)
    }

    eassert _ as W4. { 
      eapply (W3 (pand (pdom (H1'++v1::H1)) q) (pand (pdom (H1'++v1::H1)) q')) with (x:=x).

      intros ? ?. destruct (QSUB x2) as [? | ?]. unfoldq. intuition. unfoldq; intuition. 
      unfoldq; intuition. 

      intros ? ?. destruct (QSUB' x2) as [? | ?]. unfoldq. intuition. 
      eauto. unfoldq. intuition.

      intros ? ?.  eapply QSUBTR1 in H6. unfoldq; intuition.

      split.

      erewrite lls_change. 
      eapply lls_vars'. eapply lls_mono. 2: eapply VLQ. intros ? ?. eapply var_locs_shrink. eauto. unfoldq. intuition.
      subst q0. rewrite plift_empty in *. rewrite substp_empty_and. split; auto.  
      eapply substp_sub'. 2: eapply H4. unfoldq; intuition.
      
      eapply stchain_tighten. rewrite <- LL2. eapply envt_subst_filter_deep. 9: eauto. all: eauto.
      intros ? ?. destruct H6. unfoldq. eapply QSUB in H7. unfoldq; intuition.

      eapply lls_mono. eapply vars_locs_mono. unfoldq. intuition. destruct (QSUB x2); eauto. lia. 
      eapply QSUB in H8. unfoldq; intuition.

      eapply lls_mono; eauto. eapply vars_locs_mono; eauto. 
      rewrite LL2. eapply substp_sub'. unfoldq; intuition. destruct (QSUB x2); eauto. lia.
      eapply QSUB in H8. unfoldq; intuition. 
      
      erewrite lls_change. 
      eapply lls_vars'. eapply lls_mono. 2: eapply VLQ'. intros ? ?. eapply var_locs_shrink. eauto. unfoldq. intuition.
      subst q0. rewrite plift_empty in *. rewrite substp_empty_and. split; auto.  
      eapply substp_sub'. 2: eapply H5. unfoldq; intuition.

      eapply stchain_tighten. rewrite <- LL2. eapply envt_subst_filter_deep. 9: eauto. all: eauto.
      intros ? ?. destruct H6. unfoldq. eapply QSUB' in H7. unfoldq; intuition.

      eapply lls_mono. eapply vars_locs_mono. unfoldq. intuition. destruct (QSUB' x2); eauto. lia. 
      eapply QSUB' in H8. unfoldq; intuition.

      eapply lls_mono; eauto. eapply vars_locs_mono; eauto. 
      rewrite LL2. eapply substp_sub'; eauto. unfoldq; intuition. destruct (QSUB' x2); eauto. lia. 
      eapply QSUB' in H8. unfoldq; intuition.

    }

    subst q0. rewrite plift_empty in *. rewrite substp_empty_and in *.
    erewrite lls_change in W4.

    eapply lls_vars in W4. destruct W4 as (? & (? & ?) & ?). 

    eapply lls_vars'. eapply lls_mono. 2: eauto. intros ? ?. eapply var_locs_extend. eauto. split.

    eapply substp_sub'. 2: eapply H6. intros ? ?.
    eapply vt_extend. eapply vt_mono. 2: eapply H9. unfoldq. intuition.
    eapply substp_sub'. 2: eapply H7. intros ? ?.
    eapply vt_extend. eapply vt_mono. 2: eapply H9. unfoldq. intuition.

    eapply stchain_tighten.  rewrite <-substp_empty_and. rewrite <- plift_empty. rewrite <- LL2. eapply envt_subst_filter_deep. 9: eauto. all: eauto.
    intros ? ?. eapply QSUBTR1 in H6. unfoldq; intuition.

    eapply lls_mono. eapply vars_locs_mono. 
    intros ? ?. eapply QSUBTR1 in H6. unfoldq; intuition. 

    eapply lls_mono; eauto. eapply vars_locs_mono; eauto. 
    intros ? ?. eapply substp_sub' in QSUBTR1. rewrite <- substp_empty_and in H6. eapply QSUBTR1 in H6. 
    rewrite substp_empty_and in H6. rewrite LL2. auto.

  + (* qf, x *)
    remember H5 as A. clear HeqA.
    destruct H5 as [[? ?] | ?]. 
    * unfold pone in H5. rewrite app_length in H5. simpl in H5. lia.

    * destruct H5 as [[? ?] | [? ?]].
      ** unfold pone in H6. rewrite app_length in H6. simpl in H6.
         remember VTQ' as B. clear HeqB. destruct VTQ' as [[? ?] | ?].
          *** destruct H8 as [[[C1 C2] | [C3 C4]] | D]. 
              **** assert (psub (pand (vars_trans (G' ++ (T0', fr0', q0') :: G) (pand (plift qf) q)) 
                             (vars_trans (G' ++ (T0', fr0', q0') :: G) (plift q1) )) (plift qf)) as QSUBTR1. {
                    intros ? [? ?]. destruct (QSUBTR x2) as [? | ?].
                    split. (* extend *)
                    { eapply vt_extend. eapply vt_mono. 2: eapply H8. unfoldq. intuition. }
                    { eapply vt_head. eauto. unfoldq; intuition. 
                      rewrite app_length. simpl. 
                      assert (x1 = length G' + length G). { lia. } subst x1.
                      assert (length G' + length G +1 = length G' + S(length G)). { lia. }
                      rewrite <- H10. auto.
                      auto. }
                      auto.  
                    unfold pone in H10. rewrite app_length in H10. simpl in H10. 
                    eapply vt_closed in H9. unfoldq. rewrite app_length in H9. simpl in H9. lia. 
                    eauto. unfoldq; intuition.
                  }
                  eassert _ as W4. {
                    eapply (W3 (pand (plift qf) q) (plift q1)) with (x := x). 
                    unfoldq; intuition. 
                    unfoldq; intuition.

                    intros ? ?. eapply QSUBTR1 in H8. auto.
                    split.

                    erewrite lls_change.
                    eapply lls_vars'. eapply lls_mono. 2: eapply VLQ. intros ??. eapply var_locs_shrink. eauto. unfoldq; intuition.
                    assert (pand (subst_pl (plift qf) (length G)(plift q0))(subst_pl q (length G)(plift q0)) x0). { unfoldq; intuition. }
                    subst q0. rewrite plift_empty in *. rewrite <- substp_empty_and in H8.
                    eapply substp_sub'. 2: eapply H8.  unfoldq; intuition.

                    eapply stchain_tighten. rewrite <- LL2. eapply envt_subst_filter_deep. 9: eauto. all: eauto. unfoldq; intuition. 
                    eapply lls_mono. eapply vars_locs_mono. unfoldq. intuition. 
                    eapply lls_mono. eapply vars_locs_mono. rewrite LL2. 
                    assert (psub (pand (plift qf ) q) (pand (plift p) (plift qf))). { unfoldq; intuition. }
                    eapply substp_sub'; eauto.

                    erewrite lls_change.
                    rewrite <- LL2. eapply VQ2. split.
                    eapply lls_vars'. eapply lls_mono. 2: eapply VLQ. intros ? ?. eapply var_locs_shrink; eauto. unfoldq; intuition.
                    rewrite LL2. auto.

                    eapply lls_var in VLQ'. destruct VLQ' as (? & IX & ?). 
                    assert (x1 = (length (H2' ++ H2))). { rewrite app_length. lia. }
                    subst x1. rewrite indexr_head in IX. inversion IX. eauto.

                    eapply stchain_tighten. rewrite <- LL2. eapply envt_subst_filter_deep. 9: eauto. all: eauto. unfoldq; intuition. 
                    eapply lls_mono. eapply vars_locs_mono. unfoldq. intuition. 
                    eapply lls_mono. eapply vars_locs_mono. rewrite LL2. 
                    rewrite <- plift_and. eapply substp_sub'; eauto. rewrite plift_and. unfoldq; intuition.
                  }

                  erewrite lls_change in W4.

                  subst q0. rewrite plift_empty in *. rewrite substp_empty_and in *.  
                  eapply lls_vars in W4. destruct W4 as (? & (? & ?) & ?).

                  eapply lls_vars'. eapply lls_mono. 2: eapply H10. intros ? ?. eapply var_locs_extend. eauto. split.
                  eapply substp_sub'. 2: eapply H8. intros ? ?. eapply vt_extend. eapply vt_mono; eauto. unfoldq; intuition.
                  eapply substp_sub'. 2: eapply H9. intros ? ?. eapply vt_head. eauto. unfoldq; intuition. 
                  assert (x1 = length (G' ++ G)). { rewrite app_length. lia. }
                  subst x1. rewrite app_length. simpl. replace (length (G' ++ G) + 1) with (length G' + S (length G)) in C2. auto.
                  auto.

                  eapply stchain_tighten. rewrite <- LL2. eapply envt_subst_filter_deep. 9: eauto. all: eauto.
                  intros ? ?. eapply QSUBTR1 in H8. auto. 
                  eapply lls_mono. eapply vars_locs_mono. intros ? ?. eapply QSUBTR1 in H8. unfoldq; intuition.
                  eapply lls_mono. eapply vars_locs_mono. intros ? ?. 
                  eapply substp_sub' in QSUBTR1. eapply QSUBTR1 in H8. 
                  rewrite LL2. eapply substp_sub'; eauto. unfoldq; intuition.
              **** lia.
              **** subst q0. rewrite plift_empty in D. unfoldq; intuition.
          *** destruct H7; intuition.
              assert (psub (pand (vars_trans (G' ++ (T0', fr0', q0') :: G) (pand (plift qf) q)) 
                        (vars_trans (G' ++ (T0', fr0', q0') :: G) (plift q1) )) (plift qf)) as QSUBTR1. {
               intros ? [? ?]. destruct (QSUBTR x2) as [? | ?].
               split. (* extend *)
               { eapply vt_extend. eapply vt_mono. 2: eapply H7. unfoldq. intuition. }
               { eapply vt_head. eauto. unfoldq; intuition. 
                 rewrite app_length. simpl. 
                 assert (x1 = length G' + length G). { lia. } subst x1.
                 assert (length G' + length G +1 = length G' + S(length G)). { lia. }
                 rewrite <- H11. auto.
                 auto. }
                 auto.  
                 unfold pone in H11. rewrite app_length in H11. simpl in H11. 
                 eapply vt_closed in H10. unfoldq. rewrite app_length in H10. simpl in H10. lia. 
                 eauto. unfoldq; intuition.
               }
              eassert _ as W4. {
                eapply (W3 (pand (plift qf) q) (plift q1)) with (x := x). 
                unfoldq; intuition. 
                unfoldq; intuition. 
                intros ? ?. eapply QSUBTR1 in H7. auto.
                split. 
                erewrite lls_change.
                eapply lls_vars'. eapply lls_mono. 2: eapply VLQ. intros ??. eapply var_locs_shrink. eauto. unfoldq; intuition.
                assert (pand (subst_pl (plift qf) (length G)(plift q0))(subst_pl q (length G)(plift q0)) x0). { unfoldq; intuition. }
                subst q0. rewrite plift_empty in *. rewrite substp_empty_and. intuition.

                eapply stchain_tighten. rewrite <- LL2. eapply envt_subst_filter_deep. 9: eauto. all: eauto. unfoldq; intuition. 
                eapply lls_mono. eapply vars_locs_mono. unfoldq. intuition. 
                eapply lls_mono. eapply vars_locs_mono. rewrite LL2.
                eapply substp_sub'; eauto. unfoldq; intuition.

                erewrite lls_change.
                rewrite <- LL2. eapply VQ2. split.
                eapply lls_vars'. eapply lls_mono. 2: eapply VLQ. intros ? ?. eapply var_locs_shrink; eauto. unfoldq; intuition.
                rewrite LL2. auto.
                eapply lls_var in VLQ'. destruct VLQ' as (? & IX & ?). 
                assert (x1 = (length (H2' ++ H2))). { rewrite app_length. lia. }
                subst x1. rewrite indexr_head in IX. inversion IX. eauto.

                eapply stchain_tighten. rewrite <- LL2. eapply envt_subst_filter_deep. 9: eauto. all: eauto. unfoldq; intuition. 
                eapply lls_mono. eapply vars_locs_mono. unfoldq. intuition. 
                eapply lls_mono. eapply vars_locs_mono. rewrite LL2. 
                eapply substp_sub'; eauto. unfoldq; intuition.
              }

              erewrite lls_change in W4.

              subst q0. rewrite plift_empty in *. rewrite substp_empty_and in *.  
              eapply lls_vars in W4. destruct W4 as (? & (? & ?) & ?).

              eapply lls_vars'. eapply lls_mono. 2: eauto. intros ? ?. eapply var_locs_extend. eauto. split.
              eapply substp_sub'. 2: eapply H7. intros ? ?. eapply vt_extend. eapply vt_mono; eauto. unfoldq; intuition.
              eapply substp_sub'. 2: eapply H10. intros ? ?. eapply vt_head. eauto. unfoldq; intuition.
              assert(x1 = (length (G' ++ G))). { rewrite app_length. lia. } subst x1.
              rewrite app_length. simpl. replace (length (G'++G) + 1) with (length G'+S (length G)) in H9. auto.
              auto.

              eapply stchain_tighten. rewrite <- LL2. eapply envt_subst_filter_deep. 9: eauto. all: eauto.
              intros ? ?. eapply QSUBTR1 in H7. auto. 
              eapply lls_mono. eapply vars_locs_mono. intros ? ?. eapply QSUBTR1 in H7. unfoldq; intuition.
              eapply lls_mono. eapply vars_locs_mono. intros ? ?. 
              eapply substp_sub' in QSUBTR1. eapply QSUBTR1 in H7. 
              rewrite LL2. eapply substp_sub'; eauto. unfoldq; intuition.   
      ** unfold pone in H6. rewrite app_length in H6. simpl in H6. lia.

  + (* x, qf *)
    remember H4 as A. clear HeqA.
    destruct H4 as [[? ?] | ?].
    * unfold pone in H4. rewrite app_length in H4. simpl in H4. lia.
    * destruct H4 as [[? ?] | [? ?]].
      ** unfold pone in H6. rewrite app_length in H6. simpl in H6.
        remember VTQ as B. clear HeqB. destruct VTQ as [[? ?] | ?].
        *** destruct H8 as [[[C1 C2] | [C3 C4]] | D]. 
            **** assert (psub (pand (vars_trans (G' ++ (T0', fr0', q0') :: G) (plift q1)) 
                           (vars_trans (G' ++ (T0', fr0', q0') :: G) (pand (plift qf) q'))) (plift qf)) as QSUBTR1. {
                  intros ? [? ?]. destruct (QSUBTR x2) as [? | ?].
                  split. (* extend *)
                  { eapply vt_head. eauto. unfoldq; intuition. 
                    rewrite app_length. simpl. 
                    assert (x0 = length G' + length G). { lia. } subst x0.
                    assert (length G' + length G +1 = length G' + S(length G)). { lia. }
                    rewrite <- H10. auto.
                    auto. }
                  { eapply vt_extend. eapply vt_mono. 2: eapply H9. unfoldq. intuition. }  
                  auto.  
                  unfold pone in H10. rewrite app_length in H10. simpl in H10. 
                  eapply vt_closed in H9. unfoldq. rewrite app_length in H9. simpl in H9. lia. 
                  eauto. unfoldq; intuition.
                }

                eassert _ as W4. {
                  eapply (W3 (plift q1) (pand (plift qf) q')) with (x := x).
                  unfoldq; intuition. 
                  unfoldq; intuition.

                  intros ? ?. eapply QSUBTR1 in H8. eauto.
                  split.

                  {
                    erewrite lls_change.
                    rewrite <- LL2. eapply VQ2. split.
                    
                    eapply lls_vars'. eapply lls_mono. 2: eapply VLQ'. intros ??. eapply var_locs_shrink. eauto. unfoldq; intuition.
                    rewrite LL2. auto.

                    eapply lls_var in VLQ. destruct VLQ as (? & IX & ?). 
                    assert (x0 = length (H2'++H2)). { rewrite app_length. lia. }
                    subst x0. rewrite indexr_head in IX. inversion IX. subst x2. eauto.

                    eapply stchain_tighten. rewrite <- LL2. eapply envt_subst_filter_deep. 9: eauto. all: eauto. unfoldq; intuition. 

                    eapply lls_mono. eapply vars_locs_mono. unfoldq. intuition. 

                    eapply lls_mono. eapply vars_locs_mono. rewrite LL2. 
                    assert (psub (plift q1) (pand (plift p) (plift qf))). { unfoldq; intuition. }
                    eapply substp_sub'; eauto.
                  }

                  {
                    erewrite lls_change.
                    eapply lls_vars'. eapply lls_mono. 2: eapply VLQ'. intros ? ?. eapply var_locs_shrink. eauto. unfoldq; intuition.
                    subst q0. rewrite plift_empty in *. rewrite substp_empty_and. split; intuition.

                    eapply sstchain_tighten; eauto. eapply SC; eauto.
                    eapply lls_mono; eauto. rewrite LL2. eapply vars_locs_mono; eauto. eapply substp_sub'; eauto.
                    unfoldq; intuition.
                  }
                }

                erewrite lls_change in W4.

                subst q0. rewrite plift_empty in *. rewrite substp_empty_and in *.
                eapply lls_vars in W4. destruct W4 as (? & (? & ?) & ?).
                eapply lls_vars'. eapply lls_mono. 2: eauto. intros ? ?. eapply var_locs_extend. eauto.
                split. 

                eapply substp_sub'. 2: eapply H8. intros ? ?. eapply vt_head. eauto. unfoldq; intuition.
                rewrite app_length. simpl. assert (x0 = length (G'++G)). { rewrite app_length. lia. }
                subst x0. replace (length (G' ++ G) + 1) with (length G' + S (length G)) in C2. auto.
                auto.

                eapply substp_sub'. 2: eapply H9. intros ? ?. eapply vt_extend. eapply vt_mono; eauto. unfoldq; intuition.
                
                eapply stchain_tighten. rewrite <- LL2. eapply envt_subst_filter_deep. 9: eauto. all: eauto.
                intros ? ?. eapply QSUBTR1 in H8. auto. 
                eapply lls_mono. eapply vars_locs_mono. intros ? ?. eapply QSUBTR1 in H8. unfoldq; intuition.
                eapply lls_mono. eapply vars_locs_mono. intros ? ?. 
                eapply substp_sub' in QSUBTR1. eapply QSUBTR1 in H8. 
                rewrite LL2. eapply substp_sub'; eauto. unfoldq; intuition.
            **** lia.
            **** subst q0. rewrite plift_empty in D. unfoldq; intuition.
        *** destruct H7 as [[? ?] | [? ?]]; intuition.
            
        assert (psub (pand (vars_trans (G' ++ (T0', fr0', q0') :: G) (plift q1)) 
                  (vars_trans (G' ++ (T0', fr0', q0') :: G) (pand (plift qf) q'))) (plift qf)) as QSUBTR1. {
          intros ? [? ?]. destruct (QSUBTR x2) as [? | ?].
          split. (* extend *)
          { eapply vt_head. eauto. unfoldq; intuition. 
           rewrite app_length. simpl. 
           assert (x0 = length G' + length G). { lia. } subst x0.
           assert (length G' + length G +1 = length G' + S(length G)). { lia. }
           rewrite <- H11. auto.
           auto. }
          { eapply vt_extend. eapply vt_mono. 2: eapply H10. unfoldq. intuition. }  
          auto.  
          unfold pone in H11. rewrite app_length in H11. simpl in H11. 
          eapply vt_closed in H10. unfoldq. rewrite app_length in H10. simpl in H10. lia. 
          eauto. unfoldq; intuition.
          }

          eassert _ as W4. {
          eapply (W3 (plift q1) (pand (plift qf) q')) with (x := x).
          unfoldq; intuition. 
          unfoldq; intuition.

          intros ? ?. eapply QSUBTR1 in H9. eauto.
          split.

          {
          erewrite lls_change.
          rewrite <- LL2. eapply VQ2. split.
          
          eapply lls_vars'. eapply lls_mono. 2: eapply VLQ'. intros ??. eapply var_locs_shrink. eauto. unfoldq; intuition.
          rewrite LL2. auto.
          eapply lls_var in VLQ. destruct VLQ as (? & IX & ?). 
          assert (x0 = length (H2'++H2)). { rewrite app_length. lia. }
          subst x0. rewrite indexr_head in IX. inversion IX. subst x2. eauto.

          eapply stchain_tighten. rewrite <- LL2. eapply envt_subst_filter_deep. 9: eauto. all: eauto. unfoldq; intuition.
          eapply lls_mono. eapply vars_locs_mono. unfoldq. intuition.
          eapply lls_mono. eapply vars_locs_mono. rewrite LL2. 
          assert (psub (plift q1) (pand (plift p) (plift qf))). { unfoldq; intuition. }
          eapply substp_sub'; eauto.
          }

          {
            erewrite lls_change.
            eapply lls_vars'. eapply lls_mono. 2: eapply VLQ'. intros ? ?. eapply var_locs_shrink. eauto. unfoldq; intuition.
            subst q0. rewrite plift_empty in *. rewrite substp_empty_and. split; intuition.
            eapply sstchain_tighten; eauto. eapply SC; eauto.
            eapply lls_mono; eauto. rewrite LL2. eapply vars_locs_mono; eauto. eapply substp_sub'; eauto.
            unfoldq; intuition.
          }

          
        }

          erewrite lls_change in W4.

          subst q0. rewrite plift_empty in *. rewrite substp_empty_and in *.
          eapply lls_vars in W4. destruct W4 as (? & (? & ?) & ?).
          eapply lls_vars'. eapply lls_mono. 2: eauto. intros ? ?. eapply var_locs_extend. eauto.
          split. 

          eapply substp_sub'. 2: eapply H9. eapply vt_head. eauto. unfoldq; intuition.
          rewrite app_length. simpl. assert (x0 = length (G'++G)). { rewrite app_length. lia. }
          subst x0. replace (length (G' ++ G) + 1) with (length G' + S (length G)) in H8. auto.
          
          eapply substp_sub'. 2: eapply H10. intros ? ?. eapply vt_extend. eapply vt_mono; eauto. unfoldq; intuition.


          eapply stchain_tighten. rewrite <- LL2. eapply envt_subst_filter_deep. 9: eauto. all: eauto.
          intros ? ?. eapply QSUBTR1 in H9. auto. 
          eapply lls_mono. eapply vars_locs_mono. intros ? ?. eapply QSUBTR1 in H9. unfoldq; intuition.
          eapply lls_mono. eapply vars_locs_mono. intros ? ?. 
          eapply substp_sub' in QSUBTR1. eapply QSUBTR1 in H9. 
          rewrite LL2. eapply substp_sub'; eauto. unfoldq; intuition.
      ** unfold pone in H6. rewrite app_length in H6. simpl in H6. lia.

  + (* x, x *)
    destruct H4 as [[? ?] | ?]; destruct H5 as [[? ?] |?].
    * unfold pone in H4. rewrite app_length in H4. simpl in H4. lia.
    * unfold pone in H4. rewrite app_length in H4. simpl in H4. lia.
    * unfold pone in H5. rewrite app_length in H5. simpl in H5. lia.
    * destruct H4 as [[? ?] | [? ?]]; destruct H5 as [[? ?] | [? ?]]; intuition.
      ** unfold pone in H6, H7. rewrite app_length in H6, H7. simpl in H6, H7.
         remember VTQ as B. clear HeqB. remember VTQ' as C. clear HeqC.  
         destruct VTQ as [[? ?] |?]; destruct VTQ' as [[? ?] | ?].
         *** assert (x0 = length G' + length G). { lia. }
             assert (x1 = length G' + length G). { lia. }
             subst x0 x1.
             subst q0. rewrite plift_empty in *. rewrite substp_empty_and in *.
             eapply lls_vars'. eauto. split. 
             right. left. split. eauto. left. destruct H9; destruct H11; intuition.
             right. left. split. lia.  left. destruct H9; destruct H11; intuition.
          *** assert (x0 = length G' + length G). { lia. }
              assert (x1 = length G' + length G). { lia. }
              subst x0 x1.
              subst q0. rewrite plift_empty in *. rewrite substp_empty_and in *.
              eapply lls_vars'. eauto. split. 
              right. left. split. eauto. left. destruct H9; destruct H10; intuition.
              right. left. split. lia.  left. destruct H9; destruct H10; intuition.
          *** assert (x0 = length G' + length G). { lia. }
              assert (x1 = length G' + length G). { lia. }
              subst x0 x1.
              subst q0. rewrite plift_empty in *. rewrite substp_empty_and in *.
              eapply lls_vars'. eauto. split. 
              right. left. split. eauto. left. destruct H8; destruct H10; intuition.
              right. left. split. lia.  left. destruct H8; destruct H10; intuition.
          *** assert (x0 = length G' + length G). { lia. }
              assert (x1 = length G' + length G). { lia. }
              subst x0 x1.
              subst q0. rewrite plift_empty in *. rewrite substp_empty_and in *.
              eapply lls_vars'. eauto. split. 
              right. left. split. eauto. left. destruct H8; destruct H9; intuition.
              right. left. split. lia.  left. destruct H8; destruct H9; intuition.
      ** unfold pone in H6, H7. rewrite app_length in H6, H7. simpl in H6, H7. lia.
      ** unfold pone in H6, H7. rewrite app_length in H6, H7. simpl in H6, H7. lia.
      ** unfold pone in H6, H7. rewrite app_length in H6, H7. simpl in H6, H7. lia.
Unshelve. eauto. 
Qed.

(*******************************************************************************

  compatibility lemmas for semantic substitution 

********************************************************************************)

Lemma bi_var_subst2: forall G G' M M' S1 S2 S2'' H1 H1' H2 H2' x T0 fr0 q0 q1 p t1 T v1 v2x v2 p1 fr q MR
  (WFE: env_type_subst2 M (H1'++v1::H1) (H2'++H2) (G' ++ (T0, fr0, q0) :: G) p (length G) v2x q1)
  (SF: st_filter M (st_locs1 M)(st_locs2 M))
  (W: has_type G t1 T0 p1 false q1 qempty )
  (CLT1: closed_ty (length G) T0)
  (CLQ1: closed_ql (length G) q1)
  (CLP1: closed_ql (length G) p1)
  (CLP: closed_ql (length G'+ S(length G)) p)
  (CLT: closed_ty (length G'+ S(length G)) T)
  (L1: length H1 = length G)
  (L2: length H2 = length G)
  (L3: length H1' = length G')
  (L4: length H2' = length G')
  (ST: store_type S1 S2 M)
  (E2: tevaln S2 (H2'++H2) (splice_tm t1 (length H2) (length H2')) S2'' v2)
  (EFF2: store_effect S2 S2'' pempty)
  (SST2: sstore_type S2'' M')
  (SC2: sst_chain (st2 M) M')
  (X: MR = (st1 M, M', 
  fun l1 l2 : nat =>  strel M l1 l2,
  fun (l1 l2 : nat) (v1 v2 : vl) =>  st_valtype M l1 l2 v1 v2 /\ l1 < length (st1 M) /\ l2 < length (st2 M)))
  (VT:  val_type MR H1 (H2'++H2) v1 v2 T0 (splice_ty T0 (length H2)(length H2')))
  (VQ1: val_qual (st1 M) (st1 MR) H1 v1 false pempty)
  (VQ2: val_qual (st2 M) (st2 MR) (H2'++H2) v2 false pempty)
  (Y: q1 = qempty)
  (VL: val_locs v2x = pempty),  
  indexr x (G'++(T0, fr0, q0)::G) = Some (T, fr, q) ->
  plift p x ->
  exists S1'' S2'' M'' v1'' v2'',
  exp_type1 S1 S2 M (H1' ++ v1 :: H1) (H2' ++ H2) 
    (tvar x) (subst_tm (tvar x) (length H2) (splice_tm t1 (length H2) (length H2')) q1) 
    S1'' S2'' M'' v1'' v2'' 
    T  (subst_ty T (length H2) q1)
    (plift p) (subst_pl (plift p) (length H2) (plift q1))
    false false 
    (pone x) (subst_pl (pone x) (length H2) (plift q1))
    pempty pempty.
Proof.  
  intros. 
  bdestruct (x =? length H2); bdestruct (x <? length H2); intuition.
  - exists S1, S2'', MR, v1, v2.
    simpl. 
    subst x. rewrite L2 in H.
    assert (T = T0).
    rewrite indexr_skips in H.  rewrite indexr_head in H. inversion H.  simpl. auto.  simpl. lia. subst T. 
    bdestruct (length H2 =? length H2); intuition.

    assert (length S2 <= length S2'') as XL. {
        eapply sst_mono in SC2. destruct SST2 as [? ?]. destruct ST as [? [[? ?] ?]] .
        lia. }
    assert (length (st2 M) <= length M'). {
      destruct SST2 as [? ?]. destruct ST as [? [[? ?] ?]]. lia.
    }   
    assert (length (st1 M) = length (st1 MR)) as LM1. {
      subst MR. unfold st1, pnat, length1. simpl. auto.
    }

    assert (st_chain M MR) as SCR. {
      subst MR. split. 2: split. 3: split. 4: split. 5: split.
      - auto.
      - repeat split. 
        -- unfold st_locs1, pnat, length1, st1. simpl. intros ? ?. auto.
        -- unfold st_locs2, pnat, length2, st2 in *. simpl in *. intros ? ?. lia.
        -- unfold strel in H6. simpl in H6. eapply SF; eauto.
        -- unfold strel in H6. simpl in H6. eapply SF; eauto.
      - unfold st1. simpl. eapply st_refl; eauto.
      - eauto. 
      - intros. eapply functional_extensionality; intros. eapply functional_extensionality; intros. eapply propositional_extensionality. 
        unfold st1. simpl. intuition.
      - intros. unfold strel; intuition.
    }

    assert (st_filter MR (st_locs1 MR) (st_locs2 MR)) as STFR. {
      subst MR. unfold st_locs1, st_locs2, pnat, length1, length2, st1, st2. simpl. repeat split. 
      - unfold st_locs1, pnat, length1, st1. simpl. intros ? ?. auto.
      - unfold st_locs2, pnat, length2, st2. simpl. intros ? ?. auto.
      - intros. unfold strel in H6. simpl in H6. eapply strel_wf in H6; eauto. destruct H6. unfold length2 in *. lia.
      - intros. unfold strel in H6. simpl in H6. eapply strel_wf in H6; eauto. destruct H6. unfold length1, st1 in *. lia.
    }

    assert (store_type S1 S2'' MR). {
      subst MR. split. 2: split. 3: split. 4: split. 
      - unfold st1. simpl. eapply ST; eauto.
      - eauto.
      - intros. unfold strel, st1 in H6. simpl in H6.  destruct ST as [? [? [X ?]]].
        destruct (X l1 l2) as [vt [qt1 [qt2 [v1' [v2' ?]]]]]. auto.
        exists vt, qt1, qt2, v1', v2'. intuition.
        -- unfold st2, st1. simpl. destruct SC2 as [? [? Z]]. apply indexr_var_some' in H10 as H10'. 
           unfold st2 in H10'. unfoldq. specialize (Z l2); intuition. congruence.
        -- subst vt. eapply functional_extensionality; intros. eapply functional_extensionality; intros. eapply propositional_extensionality. 
        unfold st1. simpl. intuition. apply indexr_var_some' in H13. destruct H7 as [Z ?]. unfold st1, pnat, length1 in *. lia.
        apply indexr_var_some' in H14. destruct H8 as [Z ?]. unfold st2, pnat, length2 in *. lia.
        -- unfold st1, st2. simpl. destruct H18 as [? [? ?]]. repeat split.
           unfold st_locs1, pnat, length1, st1. simpl. intros ? ?. eapply H17 in H20. eauto.
           intros ? ?. unfold st_locs2, pnat, length2, st2. simpl. 
           assert (indexr l2 S2'' = Some v2'). { erewrite EFF2; eauto.  } 
           assert (indexr l2 M' = Some qt2). { destruct SC2 as [? [? Z]]. apply indexr_var_some' in H10 as H10'. 
           unfold st2 in H10'. unfoldq. specialize (Z l2); intuition. congruence. }
           eapply val_reach_wf_store in H21; eauto. eapply H21 in H20. unfoldq; intuition. 
           unfold strel in H20. simpl in H20. intro. eapply H19 in H21; eauto. erewrite <- lls_change; eauto. eapply sstchain_tighten; eauto. 
           unfold strel in H20. simpl in H20. intro. erewrite <- lls_change with (M := (st2 M)) in H21. eapply H19; eauto. eapply sstchain_tighten; eauto.  
      - eapply ST; eauto.  
      - eapply ST; eauto.
    }

    split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 8: split. 9: split.
    + eexists. intros. destruct n. lia. simpl.
      rewrite L2. rewrite <- L1. rewrite indexr_skips. rewrite indexr_head. auto. simpl. lia.
    + auto.
    + auto.
    + auto. 
    + auto. 
    + rewrite pand_empty_r. rewrite vars_locs_empty, lls_empty. intros ? ? ? ?. auto. 
    + rewrite pand_empty_r. rewrite vars_locs_empty, lls_empty. intros ? ? ? ?. auto. 
    + rewrite substy_id. rewrite splicety_id in VT.
      apply valt_closed in VT as CL.  
      rewrite <- valt_extend  with (H1':= (H1'++[v1]))(H2':=[]) in VT; eauto.
      simpl in VT. replace ((H1'++[v1])++H1) with (H1'++v1::H1) in VT. auto.
      rewrite <- app_assoc. simpl. auto. intuition. intuition.
      1-2: rewrite L2; auto. 
    + (* valq1 *)
      intros ? ?. eapply valq_val_empty in VQ1. rewrite VQ1 in H7. rewrite lls_empty in H7. unfoldq; intuition.
    
    + (* valq2 *)
      rewrite L2 in *.
      rewrite substp_hit. intros ? ?.  destruct (VQ2 x); auto. 
      eapply valq_val_empty in VQ2. rewrite VQ2 in H7. rewrite lls_empty in H7. unfoldq; intuition.
      simpl in H8. contradiction.

  - (* length G > x*)
      exists S1, S2, M.
      simpl. rewrite L2 in *.
      destruct WFE as [WL1 [WL2 [DP1 [DP2 [P1 [P2 P3]]]]]].
      destruct (P1 x T fr q H) as [vx1 [vx2 [CL [IX1 [IX2A [IX2B [IX2C [IVT [Q1 Q2]]]]]]]]].
      bdestruct (length G =? x); intuition. bdestruct (length G <? x); intuition.
      exists vx1, vx2; intuition. 
      split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 8: split.  9: split.
      
      -- eexists. intros. destruct n. lia. simpl. rewrite IX1. auto.  
      -- eexists. intros. destruct n. lia. simpl. replace (Init.Nat.pred x) with (x - 1) . rewrite <- H7. auto. lia. 
      -- eapply st_refl. auto.
      -- auto.
      -- auto.
      -- rewrite pand_empty_r, vars_locs_empty, lls_empty. intros ? ? ? ?. auto.
      -- rewrite pand_empty_r, vars_locs_empty, lls_empty. intros ? ? ? ?. auto.
      -- (* valt *) auto.
      -- (* valq1 *)  
         intros ? ?. left. eapply lls_mono; eauto.
         intros ? ?. unfoldq. unfoldq. exists x; intuition. exists vx1; intuition.
      -- (* valq2 *)
         intros ? ?. left. eapply lls_mono; eauto.
         intros ? ?. unfoldq. unfoldq. exists x; intuition. right. right. intuition.
         right. right. intuition. exists vx2; intuition.
         
  - (* length G < x*)
    exists S1, S2, M.
    simpl.
    destruct WFE as [WL1 [WL2 [DP1 [DP2 [P1 [P2 P3]]]]]].
    destruct (P1 x T fr q H) as [vx1 [vx2 [CL [IX1 [IX2A [IX2B [IX2C [IVT [Q1 Q2]]]]]]]]].
    exists vx1, vx2; intuition. 
    split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 8: split.  9: split.
    + eexists. intros. destruct n. lia. simpl. rewrite IX1. auto.  
    + destruct E2 as [n1 E1]. exists 1. intros. destruct n. lia.
      simpl.  bdestruct (length H2 =? x); intuition. bdestruct (length H2 <? x); intuition. 
      replace (Init.Nat.pred x) with (x - 1). rewrite IX2C. auto. lia. lia.
    + eapply st_refl. auto.
    + auto.
    + auto.
    + rewrite pand_empty_r, vars_locs_empty, lls_empty. intros ? ? ? ?. auto.
    + rewrite pand_empty_r, vars_locs_empty, lls_empty. intros ? ? ? ?. auto.
    + (* valt *) rewrite L2. auto.
    + (* valq1 *) 
      intros ? ?. left. eapply lls_mono; eauto. intros ? ?.
      unfoldq. unfoldq. exists x; intuition. exists vx1; intuition.
    +(* valq2 *)
      intros ? ?. left. eapply lls_mono; eauto. intros ? ?. 
      unfoldq. unfoldq. exists (x -1). intuition.
      right. left. intuition. replace (x-1+1) with x. auto. lia.
      right. left. intuition. exists vx2; intuition.    
Qed.


Lemma storet_extend_subst: forall M H1 H1' H2 H2' G' G p S1 S2 S1' S2' M' q vt v1 v2'0 qt1 qt2 T q1 T0 fr0 q0 v1' v2'
  (WFE: env_type_subst2 M (H1' ++ v1 :: H1) (H2' ++ H2) (G' ++ (T0, fr0, q0) :: G) p (length G) v2'0 q1)    
  (ST: store_type S1 S2 M)
  (ST1: store_type S1' S2' M')
  (QP: psub (plift q) (plift p))
  (SC1: st_chain M M')
  (QT1: qt1 = vars_locs_fix (H1' ++ v1 :: H1) q)
  (QT2: qt2 = vars_locs_fix (H2' ++ H2) (subst_ql q (length H2) q1))
  (SC2: st_chain M' (st_extend M' vt qt1 qt2))
  (HVX: val_type M' (H1' ++ v1 :: H1) (H2' ++ H2) v1' v2' T (subst_ty T (length H2) q1))
  (HQX1: val_qual (st1 M) (st1 M') (H1' ++ v1 :: H1) v1' false (pand (plift p) (plift q)))
  (HQX2: val_qual (st2 M) (st2 M') (H2' ++ H2) v2' false (pand (subst_pl (plift p) (length H2) (plift q1))
            (subst_pl (plift q) (length H2) (plift q1))))
  (VT: vt v1' v2')
  (LL1: length H1 = length G)
  (LL2: length H2 = length G)
  (LL3: length H1' = length G')
  (LL4: length H2' = length G')
  (EMP: q1 = qempty)
  (V1: val_locs v1 = pempty)
  (V2: val_locs v2'0 = pempty),
  store_type (v1'::S1')(v2'::S2')(st_extend M' vt qt1 qt2).
Proof.
  intros. 
  assert (env_type_subst2 M (H1' ++ v1 :: H1) (H2' ++ H2) (G' ++ (T0, fr0, q0) :: G) (qand p q) (length G) v2'0 q1) as WFET. eapply envt_subst_tighten; eauto. rewrite plift_and. intros ? ?. unfoldq; intuition.
  eapply envt_subst_store_deep_wf1 with (q := (pand (plift p) (plift q))) in WFET as WFET1; eauto.
  2: { rewrite plift_and. intros ? ?; unfoldq; intuition. } 
  eapply envt_subst_store_deep_wf2 with (q := (pand (plift p) (plift q))) in WFET as WFET2; eauto. 
  2: { rewrite plift_and. intros ? ?; unfoldq; intuition. }

  eapply envt_subst_store_wf1 with (q := (plift q)) in WFE as WFE1; auto.
  eapply envt_subst_store_wf2 with (q := (plift q)) in WFE as WFE2; auto.
  2: { eapply substp_sub'; eauto. }
  assert (st_filter M' (locs_locs_stty (st1 M') (val_locs v1')) (locs_locs_stty (st2 M') (val_locs v2'))) as SFV. {
    eapply valt_filter; eauto.
  }
  remember ST as ST'. clear HeqST'. remember ST1 as ST1'. clear HeqST1'.
  destruct ST as [SST1 [SST2 ST]]. destruct ST1 as [? [? ?]].
  remember H as SST1'. remember H0 as SST2'. clear HeqSST1'. clear HeqSST2'.
  remember SC2 as SC2'. clear HeqSC2'. 
  destruct SC2' as [SC2A SC2B].
  assert (length (st1 M) <= length (st1 M')) as L1. eapply st_mono1 in SC1. unfold length1 in *. auto.
  assert (length (st2 M) <= length (st2 M')) as L2. eapply st_mono2 in SC1. unfold length2 in *. auto.
  assert (sstore_type (v1' :: S1') (st1 (st_extend M' vt qt1 qt2))) as SSTA. {
    unfold sstore_type in H, H0, SST1, SST2.  unfold sstore_type. intuition. 
    + unfold length1. simpl. eauto.
    + bdestruct (l <? length S1').
      unfold st_extend. simpl.
      destruct (H11 l) as [qt [v [? [? [? ?]]]]]. auto.
      exists qt, v; intuition.
       bdestruct (l =? length (st1 M')); intuition.
       bdestruct (l =? length S1'); intuition.
       unfold st1. simpl. 
       intros ? ?. auto.
       eapply lls_shrink' in H26; eauto. 
       eapply H24 in H26. eapply lls_extend. auto.
       eapply val_locs_wf; eauto. 

       unfold st_extend. simpl. rewrite <- H10. simpl in H19.
       bdestruct (l =? length S1'); intuition.
       exists qt1, v1'; intuition.
       simpl. intros ? ?.
       eapply lls_shrink' in H23. 2: eauto. 2: eapply valt_wf; eauto.
       destruct (HQX1 x) as [H_q | H_fr]. eauto.
        (* q *) subst qt1. rewrite <-plift_vars_locs. erewrite <-lls_change1 with (q2 := (plift qt2)).  eapply lls_mono. 2: eauto. intros ? ?. eapply vars_locs_mono; eauto. unfoldq. intuition. 
        subst qt2. eapply stchain_tighten with (p1 := st_locs1 M') (p2 := st_locs2 M'); eauto.
        assert (env_type_subst2 M' (H1' ++ v1 :: H1) (H2' ++ H2) (G' ++ (T0, fr0, q0) :: G) p (length G) v2'0 q1) as WFE'. eapply envt_subst_store_extend; eauto.
        eapply envt_subst_filter_deep in WFE'; eauto. rewrite <- plift_vars_locs. rewrite plift_subst. auto.
        eapply envt_subst_store_deep_wf1. eapply envt_subst_store_extend; eauto.
        rewrite plift_and. unfoldq; intuition.
        rewrite <-plift_vars_locs, plift_subst. eapply envt_subst_store_deep_wf2; eauto. eapply envt_subst_store_extend. 8: eauto. all: eauto. 
        (* fr *) destruct H_fr.
        subst qt1. intros ? ?. erewrite <- plift_vars_locs in H23.
        unfoldq. eapply WFE1 in H23. subst l. eapply st_mono1 in SC1. unfold length1 in *. simpl in H19. lia.
    }
  assert (sstore_type (v2' :: S2') (st2 (st_extend M' vt qt1 qt2))) as SSTB. {
    unfold sstore_type in H, H0, SST1, SST2.  unfold sstore_type. intuition.
    + simpl. lia. 
    + bdestruct (l <? length S2').
      unfold st_extend. simpl.
      destruct (H12 l) as [qt [v [? [? [? ?]]]]]. auto.
      exists qt, v; intuition.
       bdestruct (l =? length (st2 M')); intuition.
       bdestruct (l =? length S2'); intuition.
       unfold st2. simpl. 
       intros ? ?.
       eapply lls_shrink' in H26; eauto.
       eapply H24 in H26. eapply lls_extend. auto.
       eapply val_locs_wf; eauto. 

       unfold st_extend. simpl.
       rewrite <- H. simpl in H19.  bdestruct (l =? length S2'); intuition.
       exists qt2, v2'; intuition.
       simpl. intros ? ?.
       eapply lls_shrink' in H23. 2: eauto. 2: eapply valt_wf; eauto.
       destruct (HQX2 x) as [H_q | H_fr]. eauto.
        (* q *) subst qt2. rewrite <-plift_vars_locs, plift_subst. erewrite <-lls_change2 with (q1 := (plift qt1)).  eapply lls_mono. 2: eauto. intros ? ?. eapply vars_locs_mono; eauto. unfoldq. intuition. 
        subst qt1. eapply stchain_tighten with (p1 := st_locs1 M') (p2 := st_locs2 M'); eauto. 
        assert (env_type_subst2 M' (H1' ++ v1 :: H1) (H2' ++ H2) (G' ++ (T0, fr0, q0) :: G) p (length G) v2'0 q1) as WFE'. eapply envt_subst_store_extend; eauto.
        eapply envt_subst_filter_deep in WFE'; eauto. rewrite <- plift_vars_locs. auto.
        intros ? ?. eapply envt_subst_store_deep_wf1. eapply envt_subst_store_extend. 8: eauto. all: eauto.
        2: { rewrite plift_vars_locs. eauto. }
        rewrite plift_and. unfoldq; intuition. 
        intros ? ?. eapply envt_subst_store_deep_wf2. eapply envt_subst_store_extend. 8: eauto. all: eauto. 
        rewrite plift_and. unfoldq; intuition.
        (* fr *) destruct H_fr.
        subst qt2. intros ? ?. erewrite <- plift_vars_locs, plift_subst in H23.
        unfoldq. eapply WFE2 in H23. subst l. eapply st_mono2 in SC1. unfold length2 in *. lia.
  }
  unfold store_type. intuition.
  - unfold st_extend in *. simpl in *.
    unfold strel in H13. simpl in H13. destruct H13.
    destruct H13 as [? ?].
    exists vt, qt1, qt2, v1', v2'. repeat split.
    + subst l1. unfold length1. 
      bdestruct (length (st1 M') =? length (st1 M')); intuition.
    + subst l2. unfold length2. 
      bdestruct (length (st2 M') =? length (st2 M')); intuition.
    + subst l1. assert (length1 M' = length S1'). { unfold length1. destruct SST1'; intuition. }
      rewrite H13. bdestruct (length S1' =? length S1'); intuition.
    + subst l2. assert (length2 M' = length S2'). { unfold length2. destruct SST2'; intuition. }
      rewrite H15. bdestruct (length S2' =? length S2'); intuition.
    + eapply functional_extensionality. intros. eapply functional_extensionality. intros.
      eapply propositional_extensionality. split; intros.
      * destruct H16; intuition. destruct H16 as [? [? [? ?]]]. lia.
      * left. intuition.  
    + auto.
    + unfold st1. simpl. unfold st_locs1. eapply lls_closed'; eauto.
      intros ? ?. eapply valt_wf in HVX. destruct HVX as [A B].
      eapply A in H16. unfold pnat in *. unfold length1, st1 in H16. simpl. lia.
    + unfold st2. simpl. unfold st_locs2. eapply lls_closed'; eauto.
      intros ? ?. eapply valt_wf in HVX. destruct HVX as [A B].
      eapply B in H16. unfold pnat in *. unfold length2, st2 in H16. simpl. lia.
    + unfold strel in H16. simpl in H16.
      destruct H16.
      * destruct H16 as [A B]. rewrite <- H13 in A. inversion A. subst l0.
        rewrite <- H15 in B. inversion B. subst l3.
        unfold st1, st2. simpl. intros.
        eapply valt_deep_wf in HVX as HVX'. destruct HVX' as [A B].
        eapply lls_shrink in H18; eauto. eapply A in H18.
        unfold st_locs1, pnat in H18. lia.
        intros ? ?. eapply valt_wf; eauto.
      * unfold st1, st2. simpl. intros.
        eapply lls_shrink in H17; eauto. 
        destruct H3 as [C [D E]]. unfold strel in E. simpl in E.
        assert (st_locs1 M' l0). {
          eapply lls_closed' in H17; eauto. eapply valt_wf; eauto.
        }
        specialize (E l0 l3); intuition. clear H21.
        eapply SFV in H16; intuition. eapply lls_extend; eauto.
        eapply valt_wf; eauto.
    + unfold strel in H16. simpl in H16.
      destruct H16.
      * destruct H16 as [A B]. rewrite <- H13 in A. inversion A. subst l0.
        rewrite <- H15 in B. inversion B. subst l3.
        unfold st1, st2. simpl. intros.
        eapply valt_deep_wf in HVX as HVX'. destruct HVX' as [A B].
        eapply lls_shrink in H18; eauto. eapply B in H18.
        unfold st_locs2, pnat in H18. lia.
        intros ? ?. eapply valt_wf; eauto.
      * unfold st1, st2. simpl. intros.
        eapply lls_shrink in H17; eauto. 
        destruct H3 as [C [D E]]. unfold strel in E. simpl in E.
        assert (st_locs2 M' l3). {
          eapply lls_closed' in H17; eauto. eapply valt_wf; eauto.
        }
        specialize (E l0 l3); intuition. clear H19.
        eapply SFV in H16; intuition. eapply lls_extend; eauto.
        eapply valt_wf; eauto.
    + eapply H6 in H13 as H13'.  destruct H13' as [vt' [qt1' [qt2' [v1'' [v2'' ?]]]]]; intuition.
      exists vt', qt1', qt2', v1'', v2''; intuition.
      * apply indexr_var_some' in H16 as H16'. bdestruct (l1 =? length (st1 M')); intuition.
      * apply indexr_var_some' in H15 as H15'. bdestruct (l2 =? length (st2 M')); intuition.
      * apply indexr_var_some' in H17 as H17'. bdestruct (l1 =? length S1'); intuition.
      * apply indexr_var_some' in H18 as H18'. bdestruct (l2 =? length S2'); intuition.
      * eapply functional_extensionality. intros. eapply functional_extensionality. intros.
        eapply propositional_extensionality. split; intros.
        ** destruct H21.
           *** destruct H21 as [? [? ?]]. apply indexr_var_some' in H16. unfold length1 in H21. lia.
           *** destruct H21 as [? [? [? [? ?]]]]. rewrite H19 in H24. subst x1. auto.
        ** right. exists vt'. intuition. apply indexr_var_some' in H16. unfold length1. lia.
           apply indexr_var_some' in H15. unfold length2. lia. 
      * (* st_filter *)
        destruct H22 as [STF1 [STF2 STF3]].
        repeat split.
        ** unfold st1, st_locs1, pnat, length1. simpl. intros ? ?.
           eapply lls_shrink in H21; eauto. eapply STF1 in H21. unfold st_locs1, pnat, length1, st1 in H21. lia.
           intros ? ?.  eapply lls_z with (M :=  (st1 M')) in H22; eauto. eapply STF1. auto.
        ** unfold st2, st_locs2, pnat, length2. simpl. intros ? ?.
           eapply lls_shrink in H21; eauto. eapply STF2 in H21. unfold st_locs2, pnat, length2, st2 in H21. lia.
           intros ? ?.  eapply lls_z with (M :=  (st2 M')) in H22; eauto. eapply STF2. auto.
        ** unfold strel in H21. simpl in H21. destruct H21 as [[? ?] | ?].
           *** unfold st1, st2. simpl. intros. subst l0 l3. eapply lls_shrink in H23; eauto.
               eapply STF1 in H23.  unfold st_locs1 in H23. unfoldq; intuition.
               intros ? ?.  eapply lls_z with (M := st1 M') in H21.  eapply STF1 in H21. unfold st_locs1 in H21. unfold pnat, length1, st1 in *. lia. 
           *** unfold st1, st2. simpl. intros ?. eapply lls_shrink in H22; eauto.
               specialize (STF3 l0 l3); intuition. eapply lls_extend; eauto.
               intros ? ?.  eapply lls_z with (M :=  (st1 M')) in H23; eauto. eapply STF1. auto.
        ** unfold strel in H21. simpl in H21. unfold st1, st2. simpl. intros. destruct H21 as [[? ?] | ?].
           *** subst l0 l3. eapply lls_shrink in H22; eauto. eapply STF2 in H22. unfold st_locs2 in H22. unfoldq; intuition.
               intros ? ?.  eapply lls_z with (M := st2 M') in H21.  eapply STF2 in H21. unfold st_locs2 in H21. unfold pnat, length2, st2 in *. lia.
           *** eapply lls_shrink in H22; eauto.
               specialize (STF3 l0 l3); intuition. eapply lls_extend; eauto.
               intros ? ?.  eapply lls_z with (M :=  (st2 M')) in H23; eauto. eapply STF2. auto.
  -  (* right unique *)
    unfold strel in H13, H15. simpl in H13, H15.
    destruct H13; destruct H15.
    + destruct H13 as [? ?]. destruct H15 as [? ?]. congruence.
    + destruct H13 as [? ?]. 
      edestruct H6 as [vt' [qt1' [qt2' [v1'' [v2'' [IM1 [IM2 [IS1 [IS2 [STVT [VT' STF']]]]]]]]]]]; eauto.
      subst l1. apply indexr_var_some' in IM1. unfold length1 in IM1. lia.
    + destruct H15 as [? ?].  
      edestruct H6 as [vt' [qt1' [qt2' [v1'' [v2'' [IM1 [IM2 [IS1 [IS2 [STVT [VT' STF']]]]]]]]]]]; eauto.
      subst l1. apply indexr_var_some' in IM1. unfold length1 in IM1. lia. 
    + eapply H5; eauto.
  - (* left unique *)
    unfold strel in H13, H15. simpl in H13, H15.
    destruct H13; destruct H15.
    + destruct H13 as [? ?]. destruct H15 as [? ?]. congruence.
    + destruct H13 as [? ?]. 
      edestruct H6 as [vt' [qt1' [qt2' [v1'' [v2'' [IM1 [IM2 [IS1 [IS2 [STVT [VT' STF']]]]]]]]]]]; eauto.
      apply indexr_var_some' in IM2. unfold length2 in H16. lia.
    + destruct H15 as [? ?].  
      edestruct H6 as [vt' [qt1' [qt2' [v1'' [v2'' [IM1 [IM2 [IS1 [IS2 [STVT [VT' STF']]]]]]]]]]]; eauto.
      apply indexr_var_some' in IM2. unfold length2 in H16. lia. 
    + eapply H11; eauto.
Qed.

Lemma bi_tref_subst: forall S1 S2 M H1' H2' H1 H2 v1 t t1 q e q1 S1' S2' M' v1' v2' p T G' T0 fr0 q0 G v2'0
  (WFE: env_type_subst2 M (H1' ++ v1 :: H1) (H2' ++ H2) (G' ++ (T0, fr0, q0) :: G) p (length G) v2'0 q1)
  (ST: store_type S1 S2 M)
  (SF: st_filter M (st_locs1 M)(st_locs2 M))
  (SUB: psub (plift q) (plift p))
  (LL1: length H1 = length G)
  (LL2: length H2 = length G)
  (LL3: length H1' = length G')
  (LL4: length H2' = length G')
  (EMP: q1 = qempty)
  (V1: val_locs v1 = pempty)
  (V2: val_locs v2'0 = pempty),
  exp_type1 S1 S2 M (H1' ++ v1 :: H1) (H2' ++ H2) 
	  t (subst_tm t (length H2) (splice_tm t1 (length H2) (length H2')) q1)
    S1' S2' M' v1' v2' 
    T (subst_ty T (length H2) q1) 
    (plift p) (subst_pl (plift p) (length H2) (plift q1))
    false false
    (plift q) (subst_pl (plift q) (length H2) (plift q1))
    (plift e) (subst_pl (plift e) (length H2) (plift q1)) 
  ->
exists (S1'' S2'' : stor) (M'' : stty) (v1'' v2'' : vl),
  exp_type1 S1 S2 M (H1' ++ v1 :: H1) (H2' ++ H2)
    (tref t) (subst_tm (tref t) (length H2) (splice_tm t1 (length H2) (length H2')) q1) 
    S1'' S2'' M'' v1'' v2''
    (TRef T false q) (subst_ty (TRef T false q) (length H2) q1)
    (plift p) (subst_pl (plift p) (length H2) (plift q1))
    true true
    (plift q) (subst_pl (plift q) (length H2) (plift q1))
    (plift e) (subst_pl (plift e) (length H2) (plift q1)) .
Proof. 
  intros.
  destruct H as [IE1 [IE2 [STC1 [STF1 [ST1 [EFF1 [EFF2 [HV [HQ1 HQ2]]]]]]]]].

  remember ST1 as ST1'. clear HeqST1'.
  destruct ST1 as [[SL1 SSP1] [[SL2 SSP2][SP3 [U L]]]].
  remember HV as  HV'. clear HeqHV'.

  remember (length S1) as x.
  remember (fun v1' v2'  => val_type M' (H1' ++ v1 :: H1) (H2' ++ H2) v1' v2' T (subst_ty T (length H2) q1)) as vt.

  remember (vars_locs_fix (H1' ++ v1 :: H1) q) as qt1.
  remember (vars_locs_fix (H2' ++ H2) (subst_ql q (length H2) q1)) as qt2.

  assert (st_chain M' (st_extend M' vt qt1 qt2)). {
    assert (st_chain_partial M' (st_extend M' vt qt1 qt2)
                (st_locs1 M') (st_locs2 M')). {
      unfold st_chain_partial. split. auto. split.
      {
        repeat split. 
        intros ? ?. unfold st_extend, st_locs1, pnat, length1 in *. simpl. lia.
        intros ? ?. unfold st_extend, st_locs2, pnat, length2 in *. simpl. lia.
        intros. unfold st_extend, strel in H. simpl in H. destruct H. destruct H as [? ?].
        subst l1. unfold st_locs1, pnat in H0. lia. eapply STF1; eauto.
        intros.  unfold st_extend, strel in H. simpl in H. destruct H. destruct H as [? ?].
        subst l1. unfold st_locs2, pnat in H0. lia. eapply STF1; eauto.
      }
      repeat split.
      unfoldq; intuition.
      intros ? ?. unfold st_extend, pdom. simpl. unfold st_locs1, pnat, length1 in *. lia.
      intros ? ?. unfold st_extend. simpl. unfold st_locs1, pnat, length1 in *.
      bdestruct (l =? length (st1 M')); intuition.
      unfoldq; intuition.
      intros ? ?. unfold st_extend, pdom. simpl. unfold st_locs2, pnat, length2 in *. lia.
      intros ? ?. unfold st_extend. simpl. unfold st_locs2, pnat, length2 in *.
      bdestruct (l =? length (st2 M')); intuition.
      intros. simpl. 
      eapply functional_extensionality. intros. eapply functional_extensionality. intros.
      unfold st_locs1, pnat in H. unfold st_locs2, pnat in *. 
      eapply propositional_extensionality. split. intros. right. 

      exists (st_valtype M' l1 l2). intuition.
      intros.  destruct H4. 
      destruct H4 as [? [? ?]]. lia.
      destruct H4 as [? [? [? [? ?]]]]. subst x2. auto. 
      intros. unfold st_extend. unfold strel. simpl. right. auto.
      unfold st_extend, strel. simpl. intros. destruct H0 as [[? ?] | ?].
      destruct H as [? ?]. unfold st_locs1, pnat in *. lia.
      auto.
    }

    unfold st_chain. intuition.
  }
  
  exists (v1'::S1'), (v2'::S2'), (st_extend M' vt qt1 qt2).
  exists (vref (length S1')), (vref (length S2')).

  assert (store_type (v1' :: S1') (v2' :: S2') (st_extend M' vt qt1 qt2)) as RST. {
    subst vt. eapply storet_extend_subst; eauto.

  }

  split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 8: split. 9: split.

  + (* 1st term *)
    destruct IE1 as [n1 IE1].
    exists (S n1). intros. destruct n. lia. simpl. rewrite IE1.  auto. lia.

  + (* 2nd term *)
    destruct IE2 as [n2 IE2].
    exists (S n2). intros. destruct n. lia. simpl. rewrite IE2. auto. lia.

  + (* store_typing *)
    eapply st_trans. eauto. eapply stchain_extend. auto.

  + repeat split.
    - intros ? ?. auto.
    - intros ? ?. auto.
    - unfold st_locs1, st_locs2, pnat, length1, length2. simpl. unfold st_extend, strel in H0. simpl in H0.
      intros. destruct H0. destruct H0 as [? ?]. subst l2. unfold length2. lia. 
      destruct (SP3 l1 l2) as [vt' [qt1' [qt2' [v1'' [v2'' [IM1 [IM2 ?]]]]]]]; auto.
      apply indexr_var_some' in IM2. lia.
    - unfold strel, st_extend in H0. simpl in H0. destruct H0. destruct H0. intros. unfold st_locs1, pnat, length1. simpl. unfold length1 in H0. lia.
      unfold st_locs1, st_locs2, pnat, length1, length2. simpl. intros.
      destruct (SP3 l1 l2) as [vt' [qt1' [qt2' [v1'' [v2'' [IM1 [IM2 ?]]]]]]]; auto.
      apply indexr_var_some' in IM1. lia.
  + eapply RST; eauto.
  
  + (* effects 1 *)
  eapply se_trans. eauto. intros ? ?. intros. eapply indexr_extend1 in H3. eapply H3.
  
  + (* effects 2 *)
  eapply se_trans. eauto. intros ? ?. intros. eapply indexr_extend1 in H3. eapply H3.

  + (* result type *)
  remember ((st_extend M' vt qt1 qt2)) as M2.
  assert (store_type (v1'::S1')(v2'::S2') (M2)) as ST2. {
    subst M2. eapply storet_extend_subst; eauto.
    subst vt. auto. 
  }
  assert (psub (plift qt1) (st_locs1 M')) as KM1. {
    subst qt1. rewrite <-plift_vars_locs. eapply envt_subst_store_wf1; eauto.
    eapply envt_subst_store_extend; eauto.
  }

  assert (psub (plift qt2) (st_locs2 M')) as KM2. {
    subst qt2. rewrite <-plift_vars_locs. rewrite plift_subst. eapply envt_subst_store_wf2; eauto. 
    eapply envt_subst_store_extend. 8: eauto. all: eauto.
    eapply substp_sub'; eauto.
  }
  remember WFE as WFE'. clear HeqWFE'. destruct WFE as [? [? [? [? [? [? ?]]]]]].
  simpl. split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 8: split. 
  - eapply valt_closed in HV'; intuition.
  - eapply valt_closed in HV'; intuition.
  - auto.
  - auto.
  - unfoldq. intuition.
  - rewrite plift_subst. intros ? ?. eapply substp_sub' in SUB. eapply SUB in H9.  eapply H5; eauto. rewrite <- LL2. auto.
  - subst M2. unfold st_extend, strel in *. simpl in *; intuition.
  - split. 2: split.
    -- rewrite val_locs_ref. intros ? ?. rewrite SL1 in H9. inversion H9; subst.
    unfold st1, st_extend, st_locs1, length1, pnat. simpl. unfold pone in H10. lia.
    unfold st1, st_extend, st_locs1, length1, pnat. simpl. 
    eapply lls_indexr_closed''' in H12; eauto. destruct RST; eauto.
    -- rewrite val_locs_ref. intros ? ?. rewrite SL2 in H9. inversion H9; subst.
    unfold st1, st_extend, st_locs2, length2, pnat. simpl. unfold pone in H10. lia.
    eapply lls_indexr_closed''' in H12; eauto. destruct RST as [? [? ?]]; eauto.
    -- intros. repeat rewrite val_locs_ref. subst M2. unfold st1, st2, st_extend in *. simpl in *.
    unfold strel in H9. simpl in H9. destruct H9 as [[? ?] | ?].
    --- split. intros. left. subst l2. unfoldq; intuition.
        intros. left. subst l1. unfoldq; intuition.
    --- destruct ST2 as [ST2A [ST2B ST2C]].
       split; intros. 
       * edestruct (SP3 l1 l2) as [vt' [frt1 [frt2 [qt1' [qt2' [v1'' [v2'' [IM1 [IM2 [IS1 [IS2 VT]]]]]]]]]]]; auto.
         inversion H10; subst. unfold pone in H11. apply indexr_var_some' in IM1. lia.
         eapply lls_shrink in H13 as H13'; eauto.       
         eapply lls_s in H13. 3: eauto. 2: eauto.
         eapply lls_s with (x1 := (length S2')); eauto.
         unfoldq; intuition. rewrite SL2. rewrite indexr_head. eauto.
         eapply lls_extend; eauto. unfold pone in H11. subst x1.
         rewrite SL1 in H12. rewrite indexr_head in H12. inversion H12.
         subst qt. rewrite <- plift_vars_locs in *. rewrite plift_subst.
         eapply envt_subst_same_locs. 2: eauto. 3: eauto. 
         7: { eapply envt_subst_store_extend. 8: eauto. all: eauto. }
         all: eauto.
         unfold pone in H11. subst x1.
         rewrite SL1 in H12. unfold st1 in H12. rewrite indexr_head in H12.
         inversion H12. subst. rewrite <- plift_vars_locs.
         eapply envt_subst_store_wf1 with (q := (plift q)). eapply envt_subst_store_extend. 
         8: eauto. all: eauto. 
       * edestruct (SP3 l1 l2) as [vt' [frt1 [frt2 [qt1' [qt2' [v1'' [v2'' [IM1 [IM2 [IS1 [IS2 VT]]]]]]]]]]]; auto.
         inversion H10; subst. unfold pone in H11. apply indexr_var_some' in IM2. lia.
         eapply lls_shrink in H13 as H13'; eauto.       
         eapply lls_s in H13. 3: eauto. 2: eauto.
         eapply lls_s with (x1 := (length S1')); eauto.
         unfoldq; intuition. rewrite SL1. rewrite indexr_head. eauto.
         eapply lls_extend; eauto.
         unfold pone in H11. subst x1.
         rewrite SL2 in H12. rewrite indexr_head in H12. inversion H12.
         subst qt. rewrite  <- plift_vars_locs in *. rewrite plift_subst in H13'. 
         eapply envt_subst_same_locs. 9: eapply envt_subst_store_extend. 16: eauto. all: eauto.
         unfold pone in H11. subst x1.
         rewrite SL2 in H12. unfold st2 in H12. rewrite indexr_head in H12.
         inversion H12. subst. rewrite <- plift_vars_locs in *. rewrite plift_subst. 
         eapply envt_subst_store_wf2; eauto. eapply envt_subst_store_extend. 8: eauto. all: eauto.
         rewrite plift_empty. eapply substp_sub'; eauto.
  - exists vt, qt1, qt2.
    split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 
    -- subst M2. rewrite SL1. unfold st1 at 2, st_extend. simpl.
       bdestruct (length (st1 M') =? length (st1 M')); intuition.

    -- subst M2. rewrite SL2. unfold st2 at 2, st_extend. simpl.
       bdestruct (length (st2 M') =? length (st2 M')); intuition.

    -- subst vt. subst M2. unfold st_extend. 
       eapply functional_extensionality. intros. eapply functional_extensionality. intros. simpl.
       eapply propositional_extensionality. split. intros.
       intuition. destruct H10 as [? [? [? [? ?]]]]. unfold length1 in H9. lia.  intros. intuition.
    -- intros M3.  intros.
       remember H9 as STC'. clear HeqSTC'. 
       destruct H9 as [STC1' STC2'].
       (* XXX refactor this! *)
       remember (plift qt1) as qt1'. remember (plift qt2) as qt2'.

       assert (psub (locs_locs_stty (st1 M') qt1') (st_locs1 M')). {
         subst qt1' qt1. rewrite <-plift_vars_locs. eapply envt_subst_store_deep_wf1.
         eapply envt_subst_store_extend. 8: eauto. all: eauto. 
       }

       assert (psub (locs_locs_stty (st2 M') qt2') (st_locs2 M')). {
         subst qt2' qt2.  rewrite <-plift_vars_locs. rewrite plift_subst. 
         eapply envt_subst_store_deep_wf2; eauto. eapply envt_subst_store_extend. 8: eauto.
         all: eauto.
       }
       
       assert (st_chain_partial M' M2 (locs_locs_stty (st1 M') qt1') (locs_locs_stty (st2 M') qt2')). {
         eapply stchain_tighten; eauto. 
         split. 2: split.
         * auto.
         * auto.
         * intros. destruct STC' as [SFA [SFB SFC]].
           destruct SFA as [? [? X]].
           assert (strel M2 l1 l2). {
             subst M2. unfold st_extend, strel. simpl. right. auto.
           }
           eapply X in H18. split.
           intros. subst M2. unfold st1, st2, st_extend in H18. simpl in H18.
           eapply lls_extend with (a := qt1) in H19. intuition.
           eapply lls_shrink in H18; eauto. destruct ST2 as [? [? ?]]; eauto.
           intros. subst M2. unfold st1, st2, st_extend in H18. simpl in H18.
           eapply lls_extend with (a := qt2) in H19. intuition.
           eapply lls_shrink in H18; eauto. destruct ST2 as [? [? ?]]; eauto.
       }

       assert (locs_locs_stty (st1 M3) qt1' = locs_locs_stty (st1 M2) qt1') as L321. {
         erewrite <- lls_change1. eauto. eauto. 
       }

       assert (locs_locs_stty (st2 M3) qt2' = locs_locs_stty (st2 M2) qt2') as L322. {
         erewrite <-lls_change2. eauto. eauto.
       }

       assert (locs_locs_stty (st1 M2) qt1' = locs_locs_stty (st1 M') qt1') as L211. {
         erewrite <- lls_change1 with (q2 := qt2'). eauto. eapply stchain_tighten; eauto. 
         eapply H15.
         intros ? ?. auto. intros ? ?. auto.
       }

       assert (locs_locs_stty (st2 M2) qt2' = locs_locs_stty (st2 M') qt2') as L212. {
         erewrite <- lls_change2 with (q1 := qt1'). eauto. eapply stchain_tighten; eauto.
         eapply H15.
         intros ? ?. auto. intros ? ?. auto.
       }
       
       assert (st_chain_partial M' M3 (locs_locs_stty (st1 M') qt1')(locs_locs_stty (st2 M') qt2')). {
         eapply st_trans''. eapply stchain_tighten. eauto.
         eapply H15. eauto.
         intros ? ?. auto. intros ? ?. auto.
         rewrite <- L211. rewrite <- L212. auto.
         auto. auto.
       } 
       
       assert (st_chain_partial M' M3 (locs_locs_stty (st1 M3) qt1') (locs_locs_stty (st2 M3) qt2')). {
         rewrite L321, L211. rewrite L322, L212. auto.
       }
       
       assert (st_chain_partial M3 M' (locs_locs_stty (st1 M3) qt1') (locs_locs_stty (st2 M3) qt2')). {
         eapply stchain_symmetry. auto.
       } 
       
      assert (st_chain_partial M3 M' (locs_locs_stty (st1 M3) (val_locs v1'0)) (locs_locs_stty (st2 M3) (val_locs v2'1))). {
         eapply stchain_tighten.  auto. 
         eauto. eauto. eauto.
      }

      assert (psub (locs_locs_stty (st1 M3) (val_locs v1'0)) (locs_locs_stty (st1 M') qt1')). {
        rewrite <-L211, <-L321. eauto. 
      }

      assert (psub (locs_locs_stty (st2 M3) (val_locs v2'1)) (locs_locs_stty (st2 M') qt2')). {
        rewrite <-L212, <-L322. eauto. 
      }      
      
      assert (st_chain_partial M3 M' (locs_locs_stty (st1 M') (val_locs v1'0)) (locs_locs_stty (st2 M') (val_locs v2'1))). {
        erewrite <-lls_change1.  erewrite <- lls_change2. eauto. eauto. eauto. 
      }

      assert (st_chain_partial M' M3 (locs_locs_stty (st1 M3) (val_locs v1'0)) (locs_locs_stty (st2 M3) (val_locs v2'1))). {
        eapply stchain_symmetry. auto.
      }

      assert (st_chain_partial M' M3 (locs_locs_stty (st1 M') (val_locs v1'0)) (locs_locs_stty (st2 M') (val_locs v2'1))). {
        erewrite <- lls_change1. erewrite <- lls_change2. eauto. eauto. eauto.  
      }

      subst vt. split; intros.
      eapply valt_store_change. 2: eapply H25. eauto. eauto. 
      eapply valt_store_change. 2: eapply H25. eauto. eauto. 
    -- intros. subst qt1. rewrite plift_vars_locs. auto.
    -- intros. subst qt2. rewrite <- plift_vars_locs. repeat rewrite plift_subst. auto.
       
    -- intros ? ?. subst x M2. eapply lls_s. unfoldq. eauto. 
         unfold st_extend. simpl. bdestruct (length S1' =? length (st1 M')); intuition.
         auto.
    -- intros ? ?. subst x M2. eapply lls_s. unfoldq. eauto. 
         unfold st_extend. simpl. bdestruct (length S2' =? length (st2 M')); intuition.
         auto.

  + (* valq 1 *)
    intros ? ?. inversion H0.
    * right. simpl. subst x1 q2 M0. rewrite val_locs_ref in *.
      unfold pone in H3. subst x x0. unfold pnot, pdom. unfoldq.
      simpl. rewrite SL1. eapply st_mono1 in STC1.  unfold length1 in STC1. lia.
    * left. simpl. subst x1 q2 M0. rewrite val_locs_ref in *.
      unfold pone in H3. subst x x2. unfold st_extend in *.
      unfold st1 in *. simpl in *. rewrite SL1 in H4.
      bdestruct (length (fst (fst (fst M'))) =? length (fst (fst (fst M')))); intuition.
      inversion H4.  subst qt. 
      eapply lls_mono. 2: eapply H5. subst qt1. rewrite <-plift_vars_locs. 
      intros ? ?. eapply vars_locs_mono; eauto. unfoldq; intuition.

  + (* valq 2 *)
    intros ? ?. inversion H0.
    * right. simpl. subst x1 q2 M0. rewrite val_locs_ref in *.
      unfold pone in H3. subst x x0. unfold pnot, pdom. unfoldq.
      simpl. rewrite SL2. eapply st_mono2 in STC1.  unfold length2 in STC1. lia.
    * left. simpl. subst x1 q2 M0. rewrite val_locs_ref in *.
      unfold pone in H3. subst x x2. unfold st_extend in *.
      unfold st2 in *. simpl in *. rewrite SL2 in H4.
      bdestruct (length (snd (fst (fst M'))) =? length (snd (fst (fst M')))); intuition.
      inversion H4.  subst qt. 
      eapply lls_mono. 2: eapply H5. subst qt2. rewrite <-plift_vars_locs. 
      intros ? ?. rewrite plift_subst in H6. eapply vars_locs_mono; eauto. unfoldq; intuition.
      eapply substp_sub'; eauto.
Qed.


Lemma bi_tget1_subst: forall S1 S2 M H1' v1 H11 H2' H12 t t1 q e q1 S1' S2' M' v1' v2' p T q2 fr
  (SUB: psub (plift q1) (plift p))
  (Q2: q2 = qempty),
  exp_type1 S1 S2 M (H1' ++ v1 :: H11)  (H2' ++ H12) 
     t (subst_tm t (length H12) (splice_tm t1 (length H12) (length H2')) q2) 
     S1' S2' M' v1' v2' 
     (TRef T false q1) (subst_ty (TRef T false q1) (length H12) q2) 
     (plift p) (subst_pl (plift p) (length H12) (plift q2))
     fr fr
     (plift q) (subst_pl (plift q) (length H12) (plift q2))
     (plift e) (subst_pl (plift e) (length H12) (plift q2))
  ->
  exists (S1'0 S2'0 : stor) (M'0 : stty) (v1'0 v2'0 : vl),
    exp_type1 S1 S2 M (H1' ++ v1 :: H11) (H2' ++ H12) 
      (tget t) (subst_tm (tget t) (length H12) (splice_tm t1 (length H12) (length H2')) q2)
      S1'0 S2'0 M'0 v1'0 v2'0 
      T (subst_ty T (length H12) q2)
      (plift p) (subst_pl (plift p) (length H12) (plift q2))
      false false
      (plift q1) (subst_pl (plift q1) (length H12) (plift q2))
      (plift e) (subst_pl (plift e) (length H12) (plift q2)).
Proof.  
  intros.

  destruct H as [EV1 [EV2 [STC [STF [STH [SPP1 [SPP2 [HV [HQ1 HQ2]]]]]]]]].
  remember HV as HV'. clear HeqHV'.
  destruct v1'; destruct v2'; try solve [inversion HV]. simpl in HV.
  
  destruct HV as [HT [HT' [F1 [F2 [SUB1 [SUB2 [STREL [HSTF HV]]]]]]]].
  remember STH as STH'. clear HeqSTH'.
  destruct STH as [SST1 [SST2 [SP1 [SP2 SP3]]]].

  assert (strel M' i i0) as A. eauto.
 
  destruct (SP1 i i0 A) as [vt [qt1 [qt2 [v1'' [v2'' [IM1 [IM2 [IS1 [IS2 [STVT [VT STFV]]]]]]]]]]]. 

  destruct HV as [vt' [qt1' [qt2' [IM1' [IM2' [STVALT [VT1 ?]]]]]]]; intuition.
  rewrite IM1 in IM1'. inversion IM1'. subst qt1'.
  rewrite IM2 in IM2'. inversion IM2'. subst qt2'.

  exists S1', S2', M', v1'', v2''. 
  split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 8: split. 9: split.
  + destruct EV1 as [n1 IW1].
    exists (S n1). intros. destruct n. lia. simpl.
    rewrite IW1. rewrite IS1. eauto. lia.
  + destruct EV2 as [n1 IW2].
    exists (S n1). intros. destruct n. lia. simpl.
    rewrite IW2. rewrite IS2. eauto. lia.
  + auto.  
  + auto. 
  + auto.
  + auto.
  + auto.
  + (* valt *)
  assert (st_chain M' M'). eapply st_refl; eauto.
  eapply valt_store_extend.  2: eapply VT1. eapply STH'. 2: eapply STH'.
  eapply stchain_tighten; eauto. eapply indexr_filter; eauto.
  eapply valt_filter in HV' as B. repeat rewrite val_locs_ref in B. auto.
  eapply lls_indexr_closed'''; eauto. eapply lls_indexr_closed'''; eauto.
  auto.
  destruct SST1 as (X & Y). destruct (Y i) as [qt1' [v' [IM1'' [IS1' [? ?]]]]].
  apply indexr_var_some' in IS1. lia.   
  rewrite IM1 in IM1''.  inversion IM1''. subst qt1'.
  rewrite IS1 in IS1'. inversion IS1'. subst v'. eapply H4. 
  destruct SST2 as (X & Y). destruct (Y i0) as [qt2' [v2' [IM2'' [IS2' [? ?]]]]].
  apply indexr_var_some' in IS2. lia. rewrite IM2 in IM2''.  inversion IM2''. subst qt2'.
  rewrite IS2 in IS2'. inversion IS2'. subst v2'. eapply H4. 
  rewrite STVALT in STVT. subst. 
  auto. auto.
  + intros ? ?.  left. 
  destruct SST1 as (X & Y). destruct (Y i) as [qt1' [v' [IM1'' [IS1' [? ?]]]]].
  apply indexr_var_some' in IS1. lia. rewrite IM1 in IM1''.  inversion IM1''. subst qt1'.
  rewrite IS1 in IS1'. inversion IS1'. subst v'.
  eapply H4 in H2. rewrite H0 in H2. eapply lls_mono; eauto. eapply vars_locs_mono. unfoldq; intuition. 

  + intros ? ?.  left. 
  destruct SST2 as (X & Y). destruct (Y i0) as [qt2' [v' [IM2'' [IS2' [? ?]]]]].
  apply indexr_var_some' in IS2. lia. rewrite IM2 in IM2''.  inversion IM2''. subst qt2'.
  rewrite IS2 in IS2'. inversion IS2'. subst v'.
  eapply H4 in H2; eauto. rewrite H in H2. eapply lls_mono; eauto. eapply vars_locs_mono. 
  rewrite plift_subst. subst q2. rewrite plift_empty.
  intros ? ?. split. eapply substp_sub'; eauto. auto.
Qed.

Lemma bi_tget2_subst: forall S1 S2 M H1' v1 H11 H2' H12 t t1 q e q1 S1' S2' M' v1' v2' p T q2 fr
  (Q2: q2 = qempty),
  exp_type1 S1 S2 M (H1' ++ v1 :: H11)  (H2' ++ H12) 
     t (subst_tm t (length H12) (splice_tm t1 (length H12) (length H2')) q2) 
     S1' S2' M' v1' v2' 
     (TRef T false q1) (subst_ty (TRef T false q1) (length H12) q2) 
     (plift p) (subst_pl (plift p) (length H12) (plift q2))
     fr fr
     (plift q) (subst_pl (plift q) (length H12) (plift q2))
     (plift e) (subst_pl (plift e) (length H12) (plift q2))
  ->
  exists (S1'0 S2'0 : stor) (M'0 : stty) (v1'0 v2'0 : vl),
    exp_type1 S1 S2 M (H1' ++ v1 :: H11) (H2' ++ H12) 
      (tget t) (subst_tm (tget t) (length H12) (splice_tm t1 (length H12) (length H2')) q2)
      S1'0 S2'0 M'0 v1'0 v2'0 
      T (subst_ty T (length H12) q2)
      (plift p) (subst_pl (plift p) (length H12) (plift q2))
      fr fr
      (plift q) (subst_pl (plift q) (length H12) (plift q2))
      (plift e) (subst_pl (plift e) (length H12) (plift q2)).
Proof.  
  intros.

  destruct H as [EV1 [EV2 [STC [STF [STH [SPP1 [SPP2 [HV [HQ1 HQ2]]]]]]]]].
  remember HV as HV'. clear HeqHV'.
  destruct v1'; destruct v2'; try solve [inversion HV]. simpl in HV.
  
  destruct HV as [HT [HT' [F1 [F2 [SUB1 [SUB2 [STREL [STF' HV]]]]]]]].
  remember STH as STH'. clear HeqSTH'.
  destruct STH as [SST1 [SST2 [SP1 [SP2 SP3]]]].

  assert (strel M' i i0) as A. eauto.
 
  destruct (SP1 i i0 A) as [vt [qt1 [qt2 [v1'' [v2'' [IM1 [IM2 [IS1 [IS2 [STVT [VT STFV]]]]]]]]]]]. 

  destruct HV as [vt' [qt1' [qt2' [IM1' [IM2' [STVALT [VT1 ?]]]]]]]; intuition.
  rewrite IM1 in IM1'. inversion IM1'. subst qt1'.
  rewrite IM2 in IM2'. inversion IM2'. subst qt2'.

  exists S1', S2', M', v1'', v2''. 
  split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 8: split. 9: split.
  + destruct EV1 as [n1 IW1].
    exists (S n1). intros. destruct n. lia. simpl.
    rewrite IW1. rewrite IS1. eauto. lia.
  + destruct EV2 as [n1 IW2].
    exists (S n1). intros. destruct n. lia. simpl.
    rewrite IW2. rewrite IS2. eauto. lia.
  + auto.  
  + auto. 
  + auto.
  + auto.
  + auto.
  + (* valt *)
  assert (st_chain M' M'). eapply st_refl; eauto.
  eapply valt_store_extend.  2: eapply VT1. eapply STH'. 2: eapply STH'.
  eapply stchain_tighten; eauto. eapply indexr_filter; eauto.
  eapply valt_filter in HV' as B. repeat rewrite val_locs_ref in B. auto.
  eapply lls_indexr_closed'''; eauto. eapply lls_indexr_closed'''; eauto.
  auto.
  destruct SST1 as (X & Y). destruct (Y i) as [qt1' [v' [IM1'' [IS1' [? ?]]]]].
  apply indexr_var_some' in IS1. lia.   
  rewrite IM1 in IM1''.  inversion IM1''. subst qt1'.
  rewrite IS1 in IS1'. inversion IS1'. subst v'. eapply H4. 
  destruct SST2 as (X & Y). destruct (Y i0) as [qt2' [v2' [IM2'' [IS2' [? ?]]]]].
  apply indexr_var_some' in IS2. lia. rewrite IM2 in IM2''.  inversion IM2''. subst qt2'.
  rewrite IS2 in IS2'. inversion IS2'. subst v2'. eapply H4. 
  rewrite STVALT in STVT. subst. 
  auto. auto.
  + intros ? ?.  eapply HQ1. 
  rewrite val_locs_ref. 
  eapply lls_s; eauto. unfoldq; intuition.
  destruct SST1 as (X & Y). destruct (Y i) as [qt1' [v' [IM1'' [IS1' [? ?]]]]].
  apply indexr_var_some' in IS1. lia. rewrite IM1 in IM1''.  inversion IM1''. subst qt1'.
  rewrite IS1 in IS1'. inversion IS1'. subst v'. intuition.
  + intros ? ?.  eapply HQ2. rewrite val_locs_ref. 
  eapply lls_s; eauto. unfoldq; intuition.
  destruct SST2 as (X & Y). destruct (Y i0) as [qt2' [v' [IM2'' [IS2' [? ?]]]]].
  apply indexr_var_some' in IS2. lia. rewrite IM2 in IM2''.  inversion IM2''. subst qt2'.
  rewrite IS2 in IS2'. inversion IS2'. subst v'. intuition. 
Qed.

Lemma bi_tget_subst: forall S1 S2 M H1' v1 H11 H2' H12 t t1 q e q1 S1' S2' M' v1' v2' p T q2 fr rf1
  (SUB: psub (plift q1) (plift p))
  (Q2: q2 = qempty),
  exp_type1 S1 S2 M (H1' ++ v1 :: H11)  (H2' ++ H12) 
     t (subst_tm t (length H12) (splice_tm t1 (length H12) (length H2')) q2) 
     S1' S2' M' v1' v2' 
     (TRef T rf1 q1) (subst_ty (TRef T rf1 q1) (length H12) q2) 
     (plift p) (subst_pl (plift p) (length H12) (plift q2))
     fr fr
     (plift q) (subst_pl (plift q) (length H12) (plift q2))
     (plift e) (subst_pl (plift e) (length H12) (plift q2))
  ->
  exists (S1'0 S2'0 : stor) (M'0 : stty) (v1'0 v2'0 : vl),
    exp_type1 S1 S2 M (H1' ++ v1 :: H11) (H2' ++ H12) 
      (tget t) (subst_tm (tget t) (length H12) (splice_tm t1 (length H12) (length H2')) q2)
      S1'0 S2'0 M'0 v1'0 v2'0 
      T (subst_ty T (length H12) q2)
      (plift p) (subst_pl (plift p) (length H12) (plift q2))
      (if rf1 then fr else false)  (if rf1 then fr else false)
      (plift (qor q1 (qif rf1 q))) (subst_pl (plift (qor q1 (qif rf1 q))) (length H12) (plift q2))
      (plift e) (subst_pl (plift e) (length H12) (plift q2)).
Proof.  
  intros.

  destruct H as [EV1 [EV2 [STC [STF [STH [SPP1 [SPP2 [HV [HQ1 HQ2]]]]]]]]].
  remember HV as HV'. clear HeqHV'.
  destruct v1'; destruct v2'; try solve [inversion HV]. simpl in HV.
  
  destruct HV as [HT [HT' [F1 [F2 [SUB1 [SUB2 [STREL [HTF' HV]]]]]]]].
  remember STH as STH'. clear HeqSTH'.
  destruct STH as [SST1 [SST2 [SP1 [SP2 SP3]]]].

  assert (strel M' i i0) as A. eauto.
 
  destruct (SP1 i i0 A) as [vt [qt1 [qt2 [v1'' [v2'' [IM1 [IM2 [IS1 [IS2 [STVT [VT STFV]]]]]]]]]]]. 

  destruct HV as [vt' [qt1' [qt2' [IM1' [IM2' [STVALT [VT1 ?]]]]]]]; intuition.
  rewrite IM1 in IM1'. inversion IM1'. subst qt1'.
  rewrite IM2 in IM2'. inversion IM2'. subst qt2'.

  rewrite plift_or, plift_if in *.

  exists S1', S2', M', v1'', v2''. 
  split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 8: split. 9: split.
  + destruct EV1 as [n1 IW1].
    exists (S n1). intros. destruct n. lia. simpl.
    rewrite IW1. rewrite IS1. eauto. lia.
  + destruct EV2 as [n1 IW2].
    exists (S n1). intros. destruct n. lia. simpl.
    rewrite IW2. rewrite IS2. eauto. lia.
  + auto.  
  + auto. 
  + auto.
  + auto.
  + auto.
  + (* valt *)
  assert (st_chain M' M'). eapply st_refl; eauto.
  eapply valt_store_extend.  2: eapply VT1. eapply STH'. 2: eapply STH'.
  eapply stchain_tighten; eauto. eapply indexr_filter; eauto.
  eapply valt_filter in HV' as B. repeat rewrite val_locs_ref in B. auto.
  eapply lls_indexr_closed'''; eauto. eapply lls_indexr_closed'''; eauto.
  auto.
  destruct SST1 as (X & Y). destruct (Y i) as [qt1' [v' [IM1'' [IS1' [? ?]]]]].
  apply indexr_var_some' in IS1. lia.   
  rewrite IM1 in IM1''.  inversion IM1''. subst qt1'.
  rewrite IS1 in IS1'. inversion IS1'. subst v'. eapply H4. 
  destruct SST2 as (X & Y). destruct (Y i0) as [qt2' [v2' [IM2'' [IS2' [? ?]]]]].
  apply indexr_var_some' in IS2. lia. rewrite IM2 in IM2''.  inversion IM2''. subst qt2'.
  rewrite IS2 in IS2'. inversion IS2'. subst v2'. eapply H4. 
  rewrite STVALT in STVT. subst. 
  auto. auto.
  + destruct SST1 as (X & Y). destruct (Y i) as [qt1' [v' [IM1'' [IS1' [? ?]]]]].
  apply indexr_var_some' in IS1. lia. rewrite IM1 in IM1''.  inversion IM1''. subst qt1'.
  rewrite IS1 in IS1'. inversion IS1'. subst v'. 

  destruct rf1. 
  * assert (val_qual (st1 M) (st1 M') (H1'++v1::H11) v1'' fr (pand (plift p) (plift q))). {
      intros ? ?. eapply HQ1. rewrite val_locs_ref.
      eapply lls_s. unfold pone. intuition. eauto. eapply H2; eauto.
   }
    intros ? ?. destruct (H5 x). 
    -- eauto.
    -- left. eapply lls_mono. 2: eauto. eapply vars_locs_mono. unfoldq. intuition.
    -- right. eauto. 
  * assert (val_qual (st1 M) (st1 M') (H1'++v1::H11) v1'' false (pand (plift p) (plift q1))). { 
      intros ? ?. left. eapply H2 in H5; auto. rewrite H0 in H5; auto. eapply lls_mono; eauto.
      eapply vars_locs_mono; eauto. unfoldq; intuition.
    }
    intros ? ?. destruct (H5 x). 
    -- auto.
    -- left. eapply lls_mono; eauto. eapply vars_locs_mono. 
       intros ? ?. unfoldq; intuition.
    -- right. auto.
  + destruct SST2 as (X & Y). destruct (Y i0) as [qt2' [v' [IM2'' [IS2' [? ?]]]]].
  apply indexr_var_some' in IS2. lia. rewrite IM2 in IM2''.  inversion IM2''. subst qt2'.
  rewrite IS2 in IS2'. inversion IS2'. subst v'. 

  destruct rf1. 
  * assert (val_qual (st2 M) (st2 M') (H2'++H12) v2'' fr (pand (subst_pl (plift p)(length H12)(plift q2))(subst_pl (plift q)(length H12)(plift q2)))). {
      intros ? ?. eapply HQ2. rewrite val_locs_ref.
      eapply lls_s. unfold pone. intuition. eauto. eauto.
   }
    intros ? ?. destruct (H5 x). 
    -- eauto.
    -- left. eapply lls_mono. 2: eauto. eapply vars_locs_mono. rewrite substp_or. unfoldq. intuition.
    -- right. eauto. 
  * assert (val_qual (st2 M) (st2 M') (H2'++H12) v2'' false (pand (subst_pl (plift p)(length H12)(plift q2))(subst_pl (plift q1)(length H12)(plift q2)))). { 
      intros ? ?. left. eapply H2 in H5; auto. rewrite H in H5; auto. eapply lls_mono; eauto.
      rewrite plift_subst.
      eapply vars_locs_mono; eauto. unfoldq; intuition. eapply substp_sub'; eauto.
    }
    intros ? ?. destruct (H5 x). 
    -- auto.
    -- left. eapply lls_mono; eauto. eapply vars_locs_mono.
       rewrite substp_or. 
       intros ? ?. unfoldq; intuition.
    -- right. auto.
Qed.


Lemma bi_tput_subst: forall S1 S2 M H1' v1 H11 H2' H12 t1 t2 t0 q1 q0 S1' S2' M' v1' v2' S1'' S2'' M'' v3 v4 q2 e1 e2 p rf2 T fr1 T0' fr0' q0' G' G v2'0
  (WFE: env_type_subst2 M (H1' ++ v1 :: H11)  (H2' ++ H12) (G' ++ (T0', fr0', q0') :: G) p (length G) v2'0 q0)
  (LL1: length H11 = length G)
  (LL2: length H12 = length G)
  (LL3: length H1' = length G')
  (LL4: length H2' = length G')
  (V1: val_locs v1 = pempty)
  (V2: val_locs v2'0 = pempty)
  (ST: store_type S1 S2 M)
  (E1: exp_type1 S1 S2 M (H1' ++ v1 :: H11) (H2' ++ H12) 
          t1 (subst_tm t1 (length H12) (splice_tm t0 (length H12) (length H2')) q0)
          S1' S2' M' v1' v2'
          (TRef T rf2 q2)  (subst_ty (TRef T rf2 q2) (length H12) q0)
          (plift p) (subst_pl (plift p) (length H12) (plift q0))
          fr1 fr1
          (plift q1) (subst_pl (plift q1) (length H12) (plift q0))
          (plift e1) (subst_pl (plift e1) (length H12) (plift q0)))
  (E2: exp_type1 S1' S2' M' (H1' ++ v1 :: H11) (H2' ++ H12) 
          t2 (subst_tm t2 (length H12) (splice_tm t0 (length H12) (length H2')) q0)
          S1'' S2'' M'' v3 v4 
          T (subst_ty T (length H12) q0)
          (plift p) (subst_pl (plift p) (length H12) (plift q0))
          false false
          (plift q2) (subst_pl (plift q2) (length H12) (plift q0))
          (plift e2) (subst_pl (plift e2) (length H12) (plift q0)))
  (EMP: q0 = qempty), 
  exists (S1'0 S2'0 : stor) (M'0 : stty) (v1'0 v2'0 : vl),
    exp_type1 S1 S2 M (H1' ++ v1 :: H11) (H2' ++ H12)
      (tput t1 t2) (subst_tm (tput t1 t2) (length H12) (splice_tm t0 (length H12) (length H2')) q0) 
      S1'0 S2'0 M'0 v1'0 v2'0 
      TBool (subst_ty TBool (length H12) q0)
      (plift p) (subst_pl (plift p) (length H12) (plift q0))
      false false
      (plift qempty) (subst_pl (plift qempty) (length H12) (plift q0))
      (plift (qor e1 (qor e2 q1))) (subst_pl (plift (qor e1 (qor e2 q1))) (length H12) (plift q0)). 
Proof. 
  intros. 
  repeat rewrite plift_or in *. rewrite plift_empty in *.
  destruct E1 as [IE1 [IE2 [STC [STF1 [ST1 [SE1 [SE2 [HV1 [HQ1 HQ2]]]]]]]]].
  eapply envt_subst_store_extend in WFE as WFE1. all: eauto. 

  destruct E2 as [IE3 [IE4 [SC2 [STF2 [ST2 [SE3 [SE4 [HV2 [HQ3 HQ4]]]]]]]]].

  remember ST as ST'. clear HeqST'.
  destruct ST as [SST1 [SST2 [SP1 [SP2 SP3]]]].
  destruct SST1 as [LS1 PS1]. destruct SST2 as [LS2 PS2].

  remember HV1 as HV1'. clear HeqHV1'.

  destruct v1'; destruct v2'; try solve [inversion HV1]. simpl in HV1.
  destruct HV1 as (CLT1 & CLT2 & F1 & F2 & SUB1 & SUB2 & STREL & STF' & vt & qt1' & qt2' & IM1 & IM2  & SVT & VT & QT1 & QT2 & ? & ? ).

  remember ST2 as ST2'. clear HeqST2'.
  destruct ST2 as [SST3 [SST4 [SP4 [SP5 SP6]]]].
  destruct SST3 as [LS3 PS3]. destruct SST4 as [LS4 PS4].

  assert (st_locs1 M' i) as A. { apply indexr_var_some' in IM1. unfold st_locs1, pnat, length1. lia.  }
  assert (st_locs2 M' i0) as B. { apply indexr_var_some' in IM2. unfold st_locs2, pnat, length2. lia. }

  assert (indexr i (st1 M') = indexr i (st1 M'')) as R1. { eapply SC2; auto. }
  assert (indexr i0 (st2 M') = indexr i0 (st2 M'')) as R2. { eapply SC2; auto. }


  exists (update S1'' i v3), (update S2'' i0 v4).
  exists M'', (vbool true), (vbool true).

  split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 8: split. 9: split.
  * (* first one *)
  destruct IE1 as [n1 IE1].
  destruct IE3 as [n3 IE3].
  exists (S(n1 + n3)). intros. destruct n. intuition.
  simpl. rewrite IE1. rewrite IE3.
  assert (i < length S1''). 
  rewrite LS3. eapply st_mono1'; eauto.
  apply indexr_var_some in H2. destruct H2. rewrite H2. auto. lia. lia.
  
  * destruct IE2 as [n2 IE2].
  destruct IE4 as [n4 IE4].
  exists (S(n2 + n4)). intros. destruct n. intuition.
  simpl. rewrite IE2. rewrite IE4. 
  assert (i0 < length S2''). 
  rewrite LS4. eapply st_mono2'; eauto.
  apply indexr_var_some in H2. destruct H2. rewrite H2. auto. lia. lia.

  * eapply st_trans; eauto.
  * auto.
  *  (* store typing *)
    repeat split. 
    + (* length *)
      rewrite <-update_length. eauto.
    + rewrite <-update_length.  
      intros. destruct (PS3 l) as [qt1'' [v1' [IM1' [IS1' [P1' P2']]]]]; auto.
      bdestruct (l =? i).
      - exists qt1'', v3; intuition. 
        -- subst l. rewrite update_indexr_hit. auto. auto.
        -- subst l. rewrite <- R1 in IM1'. rewrite IM1 in IM1'. inversion IM1'. subst qt1'.
           intros ? ?. eapply HQ3 in H2. destruct H2.
           rewrite QT1.
           eapply lls_mono; eauto. eapply vars_locs_mono; eauto.
           intros ? ?. unfoldq; intuition. 
           simpl in H2. intuition.
      - exists qt1'', v1'; intuition. rewrite update_indexr_miss. auto. auto.
    + (* length *)
      rewrite <-update_length. eauto.
    + rewrite <-update_length.  
      intros. destruct (PS4 l) as [qt2'' [v2' [IM2' [IS2' [P1' P2']]]]]; auto.
      bdestruct (l =? i0).
      - exists qt2'', v4; intuition. 
        -- subst l. rewrite update_indexr_hit. auto. auto.
        -- subst l. rewrite <- R2 in IM2'. rewrite IM2 in IM2'. inversion IM2'. subst qt2'.
           intros ? ?. eapply HQ4 in H2. destruct H2.
           rewrite QT2. rewrite plift_subst. eapply lls_mono; eauto.
           eapply vars_locs_mono; eauto.
           intros ? ?. unfoldq; intuition. 
           simpl in H2. intuition.
      - exists qt2'', v2'; intuition. rewrite update_indexr_miss. auto. auto.
    + intros. destruct (SP4 l1 l2) as [vt' [qt1'' [qt2'' [v1' [v2' [IM1' [IM2' [IS1' [IS2' [SVT' [VTT STF'']]]]]]]]]]]; auto.
      bdestruct (l1 =? i). 
      assert (l2 = i0).  {
        destruct HV1'. subst.
        destruct SC2 as [? [? [? [? [? ?]]]]]. specialize (H9 i i0); intuition.
        eapply SP5; eauto.
      }
      - subst l1 l2. remember ST2' as ST2''. clear HeqST2''. 
        destruct ST' as [SST1' [SST2' ST' ]].
        exists vt, qt1'', qt2'', v3, v4; intuition.
        rewrite update_indexr_hit. auto. apply indexr_var_some' in IS1'. lia.
        rewrite update_indexr_hit. auto. apply indexr_var_some' in IS2'. lia.

        destruct SC2 as [? [? [? [? [? ?]]]]]. specialize (H9 i i0); intuition.
        congruence.

        eapply VT. 6: eapply HV2. 2: eapply ST2'. eapply stchain_tighten; eauto. eapply indexr_filter; eauto.
        repeat rewrite <- val_locs_ref.
        eapply valt_filter. eauto. eapply lls_indexr_closed'''; eauto. destruct ST1 as [? [? ?]]; eauto. 
        eapply lls_indexr_closed'''; eauto. destruct ST1 as [? [? ?]]; eauto.   
        eapply valt_filter. eauto. 
        intros ? ?. destruct (HQ3 x); auto.
        rewrite QT1. eapply lls_mono; eauto. eapply vars_locs_mono. unfoldq; intuition.
        simpl in H6. contradiction.

        intros ? ?. destruct (HQ4 x); auto.
        rewrite QT2. rewrite plift_subst. eapply lls_mono; eauto. eapply vars_locs_mono. unfoldq; intuition.
        simpl in H6. contradiction.

        eapply valt_filter; eauto.

      - assert (l2 = i0 -> False). {
        intros. subst. 
        assert (strel M'' i i0). {
          destruct SC2 as [? [? [? [? [? ?]]]]]. eapply H8. intuition. auto.
        }
        assert (l1 = i). eapply SP6; eauto. contradiction.
      }
        exists vt', qt1'', qt2'', v1', v2'; intuition.
        rewrite update_indexr_miss. auto. auto. 
        rewrite update_indexr_miss. auto. auto. 
    + eauto.
    + eauto.
  * (* effects 1 *)
  assert (length S1 = length1 M). destruct ST1 as ((? & ?) & ? & ?). eauto.
  assert (length S2 = length2 M). destruct ST1 as (? & (? & ?) & ?). eauto.
  eapply envt_subst_store_deep_wf1 with (q := (plift p)) in WFE as WFEA. 2: { intros ? ?. auto. } 
  eapply envt_subst_store_deep_wf2 with (q := (plift p)) in WFE as WFEB. 2: eauto. 2: eauto. 2: { intros ? ?. auto. } 
  intros ? ?. intros.
  bdestruct (i =? l). { subst. destruct (HQ1 l).
    left. rewrite val_locs_ref. unfoldq; intuition.
    destruct H3. erewrite lls_change1. eapply lls_mono; eauto.
    eapply vars_locs_mono. unfoldq; intuition.
    eapply stchain_tighten. eapply envt_subst_filter_deep. all: eauto. unfoldq; intuition. 
    eapply envt_subst_store_deep_wf1; eauto. unfoldq; intuition. eapply envt_subst_store_deep_wf2; eauto. unfoldq; intuition.
          
    destruct fr1. simpl in *. unfold pnot, pdom in H5. apply indexr_var_some' in H4.
    rewrite LS1 in H4. destruct H5. auto.
    simpl in H5. contradiction.
    
  }{ rewrite update_indexr_miss. 
     assert ((locs_locs_stty (st1 M) (vars_locs (H1'++v1::H11) (pand (plift p) (plift e2))) l) =
             locs_locs_stty (st1 M') (vars_locs (H1'++v1::H11) (pand (plift p) (plift e2))) l) as LLS1. {
        assert (st_chain_partial M M' (locs_locs_stty (st1 M) (vars_locs (H1'++v1::H11) (pand (plift p) (plift e2)))) (locs_locs_stty (st2 M) (vars_locs (H2'++H12) (subst_pl (pand (plift p) (plift e2)) (length H12)(plift q0))))).
        eapply stchain_tighten; eauto. eapply envt_subst_filter_deep; eauto. unfoldq; intuition.
        eapply envt_subst_store_deep_wf1; eauto. unfoldq; intuition. eapply envt_subst_store_deep_wf2; eauto. unfoldq; intuition.
        eapply lls_change1 in H6. rewrite H6. auto.
      }

      assert ( ~ locs_locs_stty (st1 M) (vars_locs (H1'++v1::H11) (pand (plift p) (plift e1))) l) as X. { 
        intros ?. eapply H3. eapply lls_mono; eauto. eapply vars_locs_mono; eauto. unfoldq; intuition.
      }
      
      unfold store_effect in *.
      eapply SE1 in X as C; eauto. 
      eapply SE3 in C; eauto.
      rewrite <- LLS1. 
      intros ?. eapply H3. eapply lls_mono; eauto. eapply vars_locs_mono; eauto. unfoldq; intuition.
      lia.
   }
  * (* effects 1 *)
  assert (length S1 = length1 M). destruct ST1 as ((? & ?) & ? & ?). eauto.
  assert (length S2 = length2 M). destruct ST1 as (? & (? & ?) & ?). eauto.
  intros ? ?. intros.
  bdestruct (i0 =? l). { subst. destruct (HQ2 l).
    left. rewrite val_locs_ref. unfoldq; intuition.
    destruct H3. erewrite lls_change2. eapply lls_mono; eauto. 
    eapply vars_locs_mono. rewrite plift_empty. repeat rewrite substp_or. unfoldq; intuition.
    eapply stchain_tighten. rewrite plift_empty. rewrite <- substp_empty_and.
    rewrite <- plift_empty. 
    eapply envt_subst_filter_deep. 9: eapply WFE. all: eauto. unfoldq; intuition. eauto.
    eapply envt_subst_store_deep_wf1; eauto. unfoldq; intuition.
    rewrite plift_empty. rewrite <- substp_empty_and. rewrite <- plift_empty.
    eapply envt_subst_store_deep_wf2; eauto. unfoldq; intuition.
    
    destruct fr1. simpl in *. unfold pnot, pdom in H5. apply indexr_var_some' in H4.
    rewrite LS2 in H4. destruct H5.  auto.
    simpl in H5. contradiction.
    
  }{ rewrite update_indexr_miss.
     assert ((locs_locs_stty (st2 M) (vars_locs (H2'++H12) (subst_pl (pand (plift p) (plift e2)) (length H12)(plift q0))) l) =
             (locs_locs_stty (st2 M') (vars_locs (H2'++H12) (subst_pl (pand (plift p) (plift e2)) (length H12) (plift q0))) l)) as LLS2. {
        assert (st_chain_partial M M' (locs_locs_stty (st1 M) (vars_locs (H1'++v1::H11) (pand (plift p) (plift e2)))) (locs_locs_stty (st2 M) (vars_locs (H2'++H12) (subst_pl (pand (plift p) (plift e2)) (length H12)(plift q0))))).
        eapply stchain_tighten. eapply envt_subst_filter_deep; eauto. unfoldq; intuition. eauto.
        eapply envt_subst_store_deep_wf1; eauto. unfoldq; intuition.
        eapply envt_subst_store_deep_wf2; eauto. unfoldq; intuition.
        eapply lls_change2 in H6. rewrite H6. auto.
      }

      assert ( ~ locs_locs_stty (st2 M) (vars_locs (H2'++H12) (subst_pl (pand (plift p) (plift e1)) (length H12)(plift q0))) l) as X. { 
        intros ?. eapply H3. eapply lls_mono; eauto. eapply vars_locs_mono; eauto. 
        subst q0. rewrite plift_empty. rewrite substp_empty_and. rewrite substp_or. unfoldq; intuition.
      }

      unfold store_effect in *.
      subst q0. rewrite plift_empty in *. rewrite substp_empty_and in *.
      eapply SE2 in X as C; eauto. 
      eapply SE4 in C; eauto.
      rewrite <- LLS2. 
      intros ?. eapply H3. eapply lls_mono; eauto. eapply vars_locs_mono; eauto. 
      rewrite substp_or. rewrite substp_or. 
      unfoldq; intuition.
      lia.
   }
  
  
  * (* valt *)
  constructor.

  * (* valq *)
  eapply valq_bool. 
 * eapply valq_bool.
Qed.

Lemma overlapping_subst: forall S1 S2 M S1' S2' M' M'' H1 v1 H1' H2 H2' G T0' fr0' q0' G' p v2'0 vf1 vf2 vx1 vx2 frf qf frx qx q1 TF1 TF2 q0
    (WFE: env_type_subst2 M (H1'++v1::H1) (H2'++ H2) (G'++(T0', fr0', q0')::G) p (length G) v2'0 q0)
    (ST : store_type S1 S2 M)
    (ST1 : store_type S1' S2' M')
    (STC1: st_chain M M')
    (STC2: st_chain M' M'')
    (VTF: val_type M' (H1'++v1::H1) (H2'++ H2) vf1 vf2 TF1 TF2) 
    (HQF1: val_qual (st1 M) (st1 M') (H1'++v1::H1) vf1 frf (pand (plift p) (plift qf)))
    (HQF2: val_qual (st2 M) (st2 M') (H2'++ H2) vf2 frf (pand (subst_pl (plift p) (length H2) (plift q0)) (subst_pl (plift qf) (length H2) (plift q0))))
    (HQX1: val_qual (st1 M') (st1 M'') (H1'++v1::H1) vx1 frx (pand (plift p) (plift qx)))
    (HQX2: val_qual (st2 M') (st2 M'') (H2'++ H2) vx2 frx  (pand (subst_pl (plift p) (length H2) (plift q0)) (subst_pl (plift qx) (length H2) (plift q0))))
    (WFF1: psub (val_locs vf1) (st_locs1 M'))
    (WFF2: psub (val_locs vf2) (st_locs2 M'))
    (SUB: psub (plift q1) (plift p))
    (OVERLAP: psub (pand (vars_trans (G'++(T0', fr0', q0')::G) (pand (plift p) (plift qf))) (vars_trans (G'++(T0', fr0', q0')::G) (pand (plift p) (plift qx)))) (plift q1))
    (LL1: length H1 = length G)
    (LL2: length H2 = length G)
    (LL3: length H1' = length G')
    (LL4: length H2' = length G')
    (EMP: q0 = qempty)
    (V1: val_locs v1 = pempty)
    (V2: val_locs v2'0 = pempty)
    (A: psub (locs_locs_stty (st1 M') (val_locs vf1))  (st_locs1 M'))
    (B: psub (locs_locs_stty (st2 M') (val_locs vf2))  (st_locs2 M')), 
    psub (pand (locs_locs_stty (st1 M'') (val_locs vf1)) (locs_locs_stty (st1 M'') (val_locs vx1))) (locs_locs_stty (st1 M'') (vars_locs (H1'++v1::H1) (plift q1))) /\
    psub (pand (locs_locs_stty (st2 M'') (val_locs vf2)) (locs_locs_stty (st2 M'') (val_locs vx2))) (locs_locs_stty (st2 M'') (vars_locs (H2'++H2) (subst_pl (plift q1)(length H2)(plift q0)))).
Proof. 
  intros. 
  remember WFE as WFE1. clear HeqWFE1.
  eapply envt_subst_store_extend in WFE as WFE'; eauto.
  eapply envt_subst_store_extend in WFE' as WFE''; eauto. 
  destruct WFE'' as [L1 [L2 [P1 [P2 [W [O1 O2]]]]]].

  split.
  + (* 1st *)
    intros ? [LLSF LLSX]. destruct (HQF1 x) as [Hf_q | Hf_fr]; destruct (HQX1 x) as [Hx_q | Hx_fr]; auto.
    - erewrite <- lls_change with (M := (st1 M')) in LLSF; eauto.
      eapply stchain_tighten. eapply valt_filter; eauto. eapply STC2.  
      1,2: eapply valt_deep_wf; eauto.
    - erewrite lls_change; eauto. eapply stchain_tighten. eapply valt_filter; eauto. eapply STC2.
      1,2: eapply valt_deep_wf; eauto.
    - assert ((pand (locs_locs_stty (st1 M'') (vars_locs (H1' ++ v1 :: H1) (pand (plift p) (plift qf))))
                   (locs_locs_stty (st1 M'') (vars_locs (H1' ++ v1 :: H1) (pand (plift p) (plift qx))))) x).
        erewrite lls_change in Hf_q. 2: { 
        eapply stchain_tighten. eapply envt_subst_filter_deep; eauto.  unfoldq; intuition.
        eauto.
        eapply envt_subst_store_deep_wf1; eauto. unfoldq; intuition. 
        eapply envt_subst_store_deep_wf2; eauto. unfoldq; intuition. }

        split; eauto.
        eapply O1 with (q := (pand (plift p) (plift qf))) (q' := (pand (plift p) (plift qx))) in H.
        eapply lls_mono. eapply vars_locs_mono. 2: eauto.
        unfoldq. intuition.
        unfoldq. intuition.
        unfoldq. intuition.
        unfoldq. intuition. 
    - destruct frx. 2: contradiction. 
      eapply envt_subst_store_deep_wf1 in Hf_q.
        2: {  eauto. } 2: { unfoldq. intuition. }
        assert False. eapply Hx_fr. eauto. contradiction.
    - destruct frf. 2: contradiction. simpl in Hf_fr. unfold pdiff in Hf_fr.
      rewrite <- lls_change with (M := (st1 M)) in Hx_q. eapply envt_subst_store_deep_wf1 in Hx_q; eauto. 
      destruct Hf_fr. unfoldq; intuition.  unfoldq; intuition. 
      eapply stchain_tighten. eapply envt_subst_filter_deep; eauto. unfoldq; intuition. 
      eapply st_trans; eauto. 
      eapply envt_subst_store_deep_wf1; eauto. unfoldq; intuition. 
      eapply envt_subst_store_deep_wf2; eauto. unfoldq; intuition. 
    - destruct frx. 2: contradiction. simpl in *.
      assert False. eapply Hx_fr. eapply A. erewrite lls_change; eauto. eapply sstchain_tighten; eauto.
      eapply STC2. contradiction. 

  +  (* 2nd *)
    intros ? [LLSF LLSX]. destruct (HQF2 x) as [Hf_q | Hf_fr]; destruct (HQX2 x) as [Hx_q | Hx_fr]; auto.
    - erewrite <- lls_change with (M := (st2 M')) in LLSF; eauto.
      eapply stchain_tighten. eapply valt_filter; eauto. eapply STC2.  
      1,2: eapply valt_deep_wf; eauto.
    - erewrite lls_change; eauto. eapply stchain_tighten. eapply valt_filter; eauto. eapply STC2.
      1,2: eapply valt_deep_wf; eauto.
    - assert ((pand (locs_locs_stty (st2 M'') (vars_locs (H2'++H2) (pand (subst_pl (plift p)(length H2)(plift q0))(subst_pl (plift qf) (length H2)(plift q0)))))
                   (locs_locs_stty (st2 M'') (vars_locs (H2'++H2) (pand (subst_pl (plift p)(length H2)(plift q0))(subst_pl (plift qx) (length H2)(plift q0)))))) x).
        erewrite lls_change in Hf_q. 2: { 
        eapply stchain_tighten. subst q0. rewrite plift_empty. rewrite <- substp_empty_and. rewrite <- plift_empty. eapply envt_subst_filter_deep. 9: eauto.
        all: eauto. unfoldq; intuition.
        eapply envt_subst_store_deep_wf1; eauto. unfoldq; intuition. 
        subst q0. rewrite plift_empty. rewrite <- substp_empty_and. rewrite <- plift_empty. eapply envt_subst_store_deep_wf2; eauto. unfoldq; intuition. }

        split; eauto.
        assert (psub (pand (plift p)(plift qf))(plift p)) as C. { unfoldq; intuition. }
        assert (psub (pand (plift p)(plift qx))(plift p)) as D. { unfoldq; intuition. }
        assert (psub (pand (vars_trans (G' ++ (T0', fr0', q0') :: G) (pand (plift p) (plift qf)))(vars_trans (G' ++ (T0', fr0', q0') :: G) (pand (plift p) (plift qx))))(plift p)) as C'. {
          unfoldq; intuition.
        }
        specialize O2 with (q := (pand (plift p) (plift qf))) (q' := (pand (plift p) (plift qx))); intuition.
        subst q0. rewrite plift_empty in *. repeat rewrite <- substp_empty_and in *. rewrite LL2 in H. 
        eapply H0 in H.  
        eapply lls_mono. eapply vars_locs_mono. 2: eapply H.
        unfoldq. intuition. rewrite LL2. eapply substp_sub'; eauto. unfoldq; intuition.
    - destruct frx. 2: contradiction.
    subst q0. rewrite plift_empty in *. rewrite <- substp_empty_and in *. rewrite <- plift_empty in Hf_q.
      eapply envt_subst_store_deep_wf2 in Hf_q.
        2: {  eauto. } 2: { unfoldq. intuition. }
        assert False. eapply Hx_fr. eauto. contradiction. auto. unfoldq; intuition.
    - destruct frf. 2: contradiction. simpl in Hf_fr. unfold pnot in Hf_fr.
      rewrite <- lls_change with (M := (st2 M)) in Hx_q. 
      subst q0. rewrite plift_empty in *. rewrite <- substp_empty_and in *. rewrite <- plift_empty in Hx_q.
      eapply envt_subst_store_deep_wf2 in Hx_q; eauto. 
      destruct Hf_fr. unfold length2 in Hx_q. unfoldq; intuition. unfoldq; intuition.
      subst q0. rewrite plift_empty. rewrite <- substp_empty_and. rewrite <- plift_empty.
      eapply stchain_tighten. eapply envt_subst_filter_deep. 9: eauto. all: eauto.
      unfoldq; intuition. 
      eapply st_trans; eauto. 
      eapply envt_subst_store_deep_wf1; eauto. unfoldq; intuition. 
      eapply envt_subst_store_deep_wf2; eauto. unfoldq; intuition. 
    - destruct frx. 2: contradiction. simpl in *.
      assert False. eapply Hx_fr. eapply B. erewrite lls_change; eauto. eapply sstchain_tighten; eauto.
      eapply STC2. contradiction. 
Qed.


Lemma bi_tapp_subst: forall M M' M'' S1 S2 S1' S2' S1'' S2'' vf1 vf2 vx1 vx2 G G' H1 H2 H2' H1' f T1 fn1 fr1 T2 fn2 ar2 fr2 p qf ef q1 q2 ex e2 e2f e2x frx frf qx v1 v2'0 T0' fr0' q0' t1 t q0
  (WFE: env_type_subst2 M (H1'++v1::H1) (H2'++ H2) (G'++(T0', fr0', q0')::G) p (length G) v2'0 q0)
  (ST: store_type S1 S2 M)
  (STF: st_filter M (st_locs1 M)(st_locs2 M))
  (IEF: exp_type1 S1 S2 M (H1' ++ v1 :: H1) (H2' ++ H2)
           f (subst_tm f (length H2)(splice_tm t1 (length H2) (length H2')) q0) 
           S1' S2' M' vf1 vf2
           (TFun T1 fn1 fr1 q1 T2 fn2 ar2 fr2 q2 e2f e2x e2) (subst_ty (TFun T1 fn1 fr1 q1 T2 fn2 ar2 fr2 q2 e2f e2x e2) (length H2) q0)
           (plift p) (subst_pl (plift p) (length H2) (plift q0))
           frf frf
           (plift qf) (subst_pl (plift qf) (length H2) (plift q0))
           (plift ef) (subst_pl (plift ef) (length H2) (plift q0)))
  (IEX: exp_type1 S1' S2' M' (H1' ++ v1 :: H1) (H2' ++ H2)
          t (subst_tm t (length H2)(splice_tm t1 (length H2) (length H2')) q0) 
          S1'' S2'' M'' vx1 vx2 
          T1 (subst_ty T1 (length H2) q0)
          (plift p) (subst_pl (plift p) (length H2) (plift q0))
          frx frx
          (plift qx) (subst_pl (plift qx) (length H2) (plift q0))
          (plift ex) (subst_pl (plift ex) (length H2) (plift q0)))
  (HSEP: if fn1 then
          if fr1 then
            True
          else
            (frx = false /\ (exists x0, f = tvar x0 /\ psub (plift qx) (pone x0))) \/
            (frx = false /\ (exists p0 t, f = tabs p0 t /\ psub (plift qx) (plift p0))) \/
            (frx = false /\ psub (plift qx) (plift q1))
        else
          if fr1 then
            psub (pand 
                    (plift (vars_trans_fix (G' ++ (T0', fr0', q0') :: G) qf))
                    (plift (vars_trans_fix (G' ++ (T0', fr0', q0') :: G) qx)))
              (plift q1)
          else
            frx = false /\ psub (plift qx) (plift q1))
  (Q1: psub (plift q1) (plift p))            
  (Q2:   psub (plift q2) (plift p))
  (E2:   psub (plift e2) (plift p))
  (LL1: length H1 = length G)
  (LL2: length H2 = length G)
  (LL3: length H1' = length G')
  (LL4: length H2' = length G')
  (EMP: q0 = qempty)
  (V1: val_locs v1 = pempty)
  (V2: val_locs v2'0 = pempty), 
exists (S1'0 S2'0 : stor) (M'0 : stty) (v1' v2' : vl),
  exp_type1 S1 S2 M (H1' ++ v1 :: H1) (H2' ++ H2)
    (tapp f t) (subst_tm (tapp f t) (length H2) (splice_tm t1 (length H2)(length H2')) q0) 
    S1'0 S2'0  M'0 v1' v2' 
    T2 (subst_ty T2 (length H2) q0)
    (plift p) (subst_pl (plift p) (length H2) (plift q0))
    (fn2 && frf || ar2 && frx || fr2) (fn2 && frf || ar2 && frx || fr2)
    (plift (qor (qif fn2 qf) (qor (qif ar2 qx) q2))) (subst_pl (plift (qor (qif fn2 qf) (qor (qif ar2 qx) q2))) (length H2) (plift q0))
    (plift (qor ef (qor ex (qor e2 (qor (qif e2f qf) (qif e2x qx)))))) (subst_pl (plift (qor ef (qor ex (qor e2 (qor (qif e2f qf) (qif e2x qx))))))(length H2) (plift q0)).
Proof.    
  intros.
  repeat rewrite plift_subst in *. repeat rewrite plift_or in *. repeat rewrite plift_if in *. 
  destruct IEF as [IEF1 [IEF2 [SC1 [STF1 [ST1 [SEF1 [SEF2 [HVF [HQF1 HQF2]]]]]]]]].
  destruct IEX as [IEX1 [IEX2 [SC2 [STF2 [ST2 [SEF3 [SEF4 [HVX [HQX1 HQX2]]]]]]]]].

  assert (telescope (G'++(T0', fr0', q0')::G)). eapply envt_subst_telescope; eauto.

  remember HVF as HVF'. clear HeqHVF'.
  destruct vf1; destruct vf2; try solve [inversion HVF]; simpl in HVF; intuition.
  apply valt_wf in HVF' as WFQF. apply valt_wf in HVX as WFQX.
  rename H14 into HVF.

  destruct (HVF S1'' S2'' M'' vx1 vx2) as [S1''' [S2''' [M''' [vy1 [vy2 [IEY1 [IEY2 [SC3 [STF3 [ST3 [SEF5 [SEF6 [HVY [HQY1 HQY2]]]]]]]]]]]]]]; eauto.
  
  eapply stchain_tighten. eapply valt_filter; eauto. eauto. eapply H12. eapply H12. 

  (* SEPARATION / OVERLAP *)
  (* 1st *)
  intros ? ?.

  destruct fn1. { (* arg may overlap with function? *)
    destruct fr1. { (* arg may be fresh? *)
      (* fn, fr: anything goes *)
      edestruct val_locs_stty_decide. destruct ST2; eauto. left. simpl.  eauto. 
      right. left. eauto.
    } {
      (* fn, not fr *) 
      destruct HSEP as [SEP | [SEP | SEP]]. { (* fn *)
        destruct SEP as (? & ? & ? & A). subst f frx.
        destruct IEF1 as [? IEF1]. assert (S x1 > x1) as P. lia. specialize (IEF1 (S x1) P).
        simpl in IEF1. inversion IEF1.
        destruct (HQX1 x) as [Hq | Hfr]. eauto. 2: { unfoldq. intuition. }
        left. simpl. eapply lls_vars in Hq. destruct Hq as (? & (? & B) & ?).
        eapply lls_var in H18. destruct H18 as (? & ? & ?).
        eapply A in B. unfoldq. congruence. 
      } { (* fn 2, value *)
        destruct SEP as (? & ? & ? & ? & A). subst f frx.
        destruct IEF1 as [? IEF1]. assert (S x2 > x2) as P. lia. specialize (IEF1 (S x2) P).
        simpl in IEF1. inversion IEF1. subst.
        destruct (HQX1 x) as [Hq | Hfr]. eauto. 2: { unfoldq. intuition. }
        subst. left. simpl. eapply lls_vars in Hq. destruct Hq as (? & (? & B) & ?).
        rewrite val_locs_abs. 
        eapply A in B. eapply lls_vars'. eauto. eauto. 
      } { (* q1 *)
        destruct SEP. subst frx.
        right. right. 
        eapply valq_sub with (q':=plift q1) (fr':=false) in HQX1.
        destruct (HQX1 x) as [Hq | Hfr]. eauto. 2: contradiction.
        eapply lls_vars in Hq. destruct Hq as (? & ? & ?). eapply lls_vars'. eauto. unfoldq. intuition. 
        unfoldq; intuition. eauto.
      }
    }
  } {
    right. destruct fr1. {
      (* not fn, fr *) 
      edestruct val_locs_stty_decide. destruct ST2; eauto. { (* check to see if we're aliasing function *)
        right. eapply overlapping_subst. 6: eapply HVF'. eapply WFE. eauto. eauto. all: eauto.
        eapply valt_wf; eauto. eapply valt_wf; eauto. 

        intros ? [? ?]. eapply HSEP. split.
        rewrite plift_vt. eapply vt_mono. 2: eapply H15. unfoldq. intuition. eauto. 
        rewrite plift_vt. eapply vt_mono. 2: eapply H16. unfoldq. intuition. eauto.
        eapply valt_deep_wf; eauto. eapply valt_deep_wf; eauto.
        unfoldq. intuition eauto.

      }{ 
        left.  eauto.
      }
    } {
      (* not fn, not fr *)
      right. destruct HSEP as [? HSEP]. subst frx.
      eapply valq_sub with (q':=plift q1) (fr':=false) in HQX1.
      destruct (HQX1 x) as [Hq | Hfr]. eauto. 2: contradiction.
      eapply lls_vars in Hq. destruct Hq as (? & ? & ?). eapply lls_vars'. eauto. unfoldq. intuition.
      unfoldq; intuition. eauto. 
    }
  }

  (* 2nd *)
  intros ? ?.
  
  destruct fn1. { (* arg may overlap with function? *)
    destruct fr1. { (* arg may be fresh? *)
      (* fn, fr: anything goes *)
      edestruct val_locs_stty_decide. destruct ST2 as [? [A ?]]. eapply A. left. simpl.  eauto. 
      right. left. eauto.
    } { 
      (* fn, not fr *) 
      destruct HSEP as [SEP | [SEP | SEP]]. { (* fn *)
        destruct SEP as (? & ? & ? & A). subst f frx.
        destruct IEF2 as [? IEF2]. assert (S x1 > x1) as P. lia. specialize (IEF2 (S x1) P).
        simpl in IEF2.
        bdestruct (length H2 =? x0); intuition.
        - destruct (HQX2 x) as [Hq | Hfr]. eauto. 2: { unfoldq. intuition. }
        left. simpl. eapply lls_vars in Hq. destruct Hq as (? & (? & B) & ?).
        eapply lls_var in H20. destruct H20 as (? & ? & ?). 
        eapply substp_sub' in A.
        eapply A in B. destruct B as [? | ?]. destruct H22 as [? [? | ?]]. destruct H23; intuition.
        unfoldq; intuition.  unfoldq; intuition. subst q0. rewrite plift_empty in H23. unfoldq; intuition.
        destruct H22; intuition. unfold pone in H24. subst x0. intuition.
        unfold pone in H24. intuition.
        - bdestruct (length H2 <? x0); intuition. inversion IEF2.
        destruct (HQX2 x) as [Hq | Hfr]. eauto. 2: { unfoldq. intuition. }
        left. simpl. eapply lls_vars in Hq. destruct Hq as (? & (? & B) & ?).
        eapply lls_var in H24. destruct H24 as (? & ? & ?). 
        eapply substp_sub' in A.
        eapply A in B. destruct B as [? | ?]. destruct H26 as [? [? | ?]]. destruct H27; intuition.
        unfoldq; intuition. 
        destruct H26; intuition. unfold pone in H28. subst x0.  
        replace (Init.Nat.pred (x2+1)) with x2 in H23. 2: { intuition. }
        rewrite H23 in H24. inversion H24. subst x3. congruence.
        unfold pone in H28. subst x0. unfoldq; intuition.


        inversion IEF2.
        destruct (HQX2 x) as [Hq | Hfr]. eauto. 2: { unfoldq. intuition. }
        left. simpl. eapply lls_vars in Hq. destruct Hq as (? & (? & B) & ?).
        eapply lls_var in H24. destruct H24 as (? & ? & ?). 
        eapply substp_sub' in A.
        eapply A in B. destruct B as [? | ?]. destruct H26 as [? [? | ?]]. destruct H27; intuition.
        unfoldq; intuition. 
        destruct H26; intuition. unfold pone in H28. subst x0.  
        replace (Init.Nat.pred (x2+1)) with x2 in H23. 2: { intuition. }
        unfoldq; intuition.
        unfold pone in H28. subst x0. rewrite H23 in H24. inversion H24. congruence.
        
        
      } { (* fn 2, value *)
        destruct SEP as (? & ? & ? & ? & A). subst f frx. 
        destruct IEF2 as [? IEF2]. assert (S x2 > x2) as P. lia. specialize (IEF2 (S x2) P).
        simpl in IEF2. inversion IEF2. 
        destruct (HQX2 x) as [Hq | Hfr]. eauto. 2: { unfoldq. intuition. }
        subst. left. simpl. eapply lls_vars in Hq. destruct Hq as (? & (? & B) & ?).
        rewrite val_locs_abs.
        eapply substp_sub' in A. 
        eapply A in B.  eapply lls_vars'. eauto. rewrite plift_subst. auto. 

      } { (* q1 *)
        destruct SEP. subst frx. repeat rewrite plift_subst.
        right. right. 
        eapply valq_sub with (q':=plift q1) (fr':=false) in HQX1.
        destruct (HQX2 x) as [Hq | Hfr]. eauto. 2: contradiction. 
        eapply lls_vars in Hq. destruct Hq as (? & ? & ?). eapply lls_vars'. eauto. 
        eapply substp_sub'; eauto. destruct H14. auto. 
        unfoldq; intuition.  eauto. 
      }
    }
  } {
    right. destruct fr1. {
      (* not fn, fr *) 
      edestruct val_locs_stty_decide. destruct ST2 as [? [X ?]]. eapply X.  { (* check to see if we're aliasing function *)
        right. rewrite plift_subst. eapply overlapping_subst. 6: eapply HVF'. 3: eauto. 3: eauto. 3: eauto. 2: eauto. eapply WFE. all: eauto. 
        eapply valt_wf; eauto. eapply valt_wf; eauto.

        intros ? [? ?]. eapply HSEP. split.
        rewrite plift_vt. eapply vt_mono. 2: eapply H15. unfoldq. intuition. eauto. 
        rewrite plift_vt. eapply vt_mono. 2: eapply H16. unfoldq. intuition. eauto.
        eapply valt_deep_wf; eauto. eapply valt_deep_wf; eauto.
        unfoldq. intuition eauto. 
      }{ 
        left. eauto.
      }
    } {
      (* not fn, not fr *)
      right. destruct HSEP as [? HSEP]. subst frx. rewrite plift_subst in *.
      eapply valq_sub with (q':=(subst_pl (plift q1)(length H2)(plift q0))) (fr':=false) in HQX2.
      destruct (HQX2 x) as [Hq | Hfr]. eauto. 2: contradiction.
      eapply lls_vars in Hq. destruct Hq as (? & ? & ?). eapply lls_vars'. eauto. auto.
      subst q0. rewrite plift_empty. rewrite <- substp_empty_and. 
      eapply substp_sub'; eauto. unfoldq; intuition. auto.
    }
  }
  

  (* EVALUATION *)
  exists S1''', S2''', M''', vy1, vy2. 
  split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 8: split. 9: split.
  + (* expression evaluates *)
    (* - initial fuel value *)
    destruct IEF1 as [n1 IEF1].
    destruct IEX1 as [n2 IEX1].
    destruct IEY1 as [n3 IEY1].
    exists (S (n1+n2+n3)).
    (* - forall greater fuel *)
    intros. destruct n. lia.
    (* - result computes *)
    simpl. rewrite IEF1. rewrite IEX1. rewrite IEY1.
    repeat rewrite app_assoc. repeat rewrite app_nil_r. eauto.
    all: lia.

  + (* expression evaluates *)
    (* - initial fuel value *)
    destruct IEF2 as [n1 IEF2].
    destruct IEX2 as [n2 IEX2].
    destruct IEY2 as [n3 IEY2].
    exists (S (n1+n2+n3)).
    (* - forall greater fuel *)
    intros. destruct n. lia.
    (* - result computes *)
    simpl. rewrite IEF2. rewrite IEX2. rewrite IEY2.
    repeat rewrite app_assoc. repeat rewrite app_nil_r. eauto.
    all: lia.

  + eapply st_trans. eapply st_trans. eauto. eauto. eauto. 

  + eauto.

  (* STORE_TYPE *)
  + eauto.

  + (* store preservation 1 *)  

    assert (length1 M <= length1 M') as L1. eapply st_mono1 in SC1. auto.
    assert (st_chain M M'') as SCC. eapply st_trans. eauto. eauto.

    assert (length1 M' <= length1 M'') as L2. eapply st_mono1 in SC2. auto.
    intros ? ? PV. intros IS. rewrite SEF5; eauto. intros ?. eapply PV.
    assert (l1 < length1 M). apply indexr_var_some' in IS. destruct ST as ((L' & ?) & ?). unfold length1. lia.
    destruct H13 as [EE2 | [E2X | E2F]]. {
      erewrite lls_change. 
      eapply lls_mono; eauto. eapply vars_locs_mono; eauto. unfoldq; intuition.
      repeat rewrite plift_or.  repeat rewrite plift_if. unfoldq; intuition. 

      eapply stchain_tighten. repeat rewrite plift_or.  repeat rewrite plift_if. 
      eapply envt_subst_filter_deep; eauto. unfoldq; intuition. 
      eauto.
      repeat rewrite plift_or. repeat rewrite plift_if.
      eapply envt_subst_store_deep_wf1; eauto. unfoldq; intuition.
      eapply envt_subst_store_deep_wf2; eauto. unfoldq; intuition.

    } {
      destruct e2x; simpl in E2X.
      destruct (HQX1 l1). auto.
      erewrite lls_change. 
      eapply lls_mono; eauto. eapply vars_locs_mono; eauto. unfoldq; intuition.
      repeat rewrite plift_or. repeat rewrite plift_if. unfoldq; intuition.

      eapply stchain_tighten. eapply envt_subst_filter_deep; eauto. unfoldq; intuition.
      eauto. 
      eapply envt_subst_store_deep_wf1; eauto. unfoldq; intuition.
      eapply envt_subst_store_deep_wf2; eauto. unfoldq; intuition.

      destruct frx; unfold not, pdom in H13. destruct H13. 
      eapply st_mono1 in SC1. unfold length1, pnat in *. lia.
      contradiction. contradiction.
    } {
      destruct e2f; simpl in E2F.
      destruct (HQF1 l1). erewrite lls_change; eauto. eapply stchain_tighten. eapply valt_filter. eauto. eauto.
      eapply valt_deep_wf; eauto. eapply valt_deep_wf; eauto.
      erewrite lls_change; eauto.
      eapply lls_mono; eauto. eapply vars_locs_mono; eauto.
      repeat rewrite plift_or. repeat rewrite plift_if.
      unfoldq; intuition.
      eapply stchain_tighten. eapply envt_subst_filter_deep; eauto. unfoldq; intuition. eauto.
      eapply envt_subst_store_deep_wf1; eauto. unfoldq; intuition.
      eapply envt_subst_store_deep_wf2; eauto. unfoldq; intuition.
      destruct frf; simpl in H13. unfold pnot, pdom in H13. destruct H13. unfold length1, pnat in *. lia.
      contradiction. contradiction.
    }
    rewrite SEF3; eauto. intros ?. eapply PV.
    erewrite lls_change. eapply lls_mono; eauto. eapply vars_locs_mono; eauto. 
    repeat rewrite plift_or. repeat rewrite plift_if.
    unfoldq; intuition.
    eapply stchain_tighten; eauto. eapply envt_subst_filter_deep; eauto. unfoldq; intuition.
    eapply envt_subst_store_deep_wf1; eauto. unfoldq; intuition.
    eapply envt_subst_store_deep_wf2; eauto. unfoldq; intuition.

    rewrite SEF1; eauto. intros ?. eapply PV.
    eapply lls_mono; eauto. eapply vars_locs_mono; eauto. 
    repeat rewrite plift_or. repeat rewrite plift_if.
    unfoldq; intuition.

  + (* store preservation 2 *)  
  assert (length2 M <= length2 M') as L1. eapply st_mono2 in SC1. auto.
  assert (st_chain M M'') as SCC. eapply st_trans. eauto. eauto.
  
  assert (length2 M' <= length2 M'') as L2. eapply st_mono2 in SC2. auto.
  intros ? ? PV. intros IS. rewrite SEF6; eauto. intros ?. eapply PV.
  assert (l1 < length2 M). apply indexr_var_some' in IS. destruct ST as (? & (L & ?) & ?). unfold length2. lia.
  rewrite plift_subst in *. repeat rewrite plift_or in *. repeat rewrite plift_if in *.
  destruct H13 as [EE2 | [E2X | E2F]]. {
    erewrite lls_change. 
    eapply lls_mono; eauto. eapply vars_locs_mono; eauto. 
    unfoldq; intuition. eapply substp_sub'; eauto. eapply substp_sub'; eauto. unfoldq; intuition.
    subst q0. rewrite plift_empty.  rewrite <- substp_empty_and.
    eapply stchain_tighten. rewrite <- plift_empty. eapply envt_subst_filter_deep. 9: eauto. all: eauto. 
    unfoldq; intuition. 
    eapply envt_subst_store_deep_wf1; eauto. unfoldq; intuition.
    rewrite <- plift_empty. eapply envt_subst_store_deep_wf2; eauto. unfoldq; intuition.

  } {
    destruct e2x; simpl in E2X. 
    destruct (HQX2 l1). auto.
    erewrite lls_change. 
    eapply lls_mono; eauto. eapply vars_locs_mono; eauto.  unfoldq; intuition.
    eapply substp_sub'; eauto. unfoldq; intuition.
    subst q0. rewrite plift_empty.  rewrite <- substp_empty_and.
    eapply stchain_tighten. rewrite <- plift_empty. eapply envt_subst_filter_deep. 9: eauto. all: eauto.
    unfoldq; intuition. 

    eapply envt_subst_store_deep_wf1; eauto. unfoldq; intuition.
    rewrite <- plift_empty. eapply envt_subst_store_deep_wf2; eauto. unfoldq; intuition.

    destruct frx; unfold pnot, pdom in H13. destruct H13. 
    eapply st_mono2 in SC2. unfold length2, pnat in *. lia.
    contradiction. contradiction.
  } {
    destruct e2f; simpl in E2F.
    destruct (HQF2 l1). erewrite lls_change; eauto. eapply stchain_tighten. eapply valt_filter. eauto. eauto.
    eapply valt_deep_wf; eauto. eapply valt_deep_wf; eauto.
    erewrite lls_change; eauto.
    eapply lls_mono; eauto.  eapply vars_locs_mono; eauto.
    unfoldq; intuition. eapply substp_sub'; eauto. unfoldq; intuition.
    subst q0. rewrite plift_empty.  rewrite <- substp_empty_and.
    eapply stchain_tighten. rewrite <- plift_empty. eapply envt_subst_filter_deep. 9: eauto. all: eauto.
    unfoldq; intuition.
    eapply envt_subst_store_deep_wf1; eauto. unfoldq; intuition.
    rewrite <- plift_empty. eapply envt_subst_store_deep_wf2; eauto. unfoldq; intuition.
    destruct frf; simpl in H13. unfold pnot, pdom in H13. destruct H13. unfold length2, pnat in *. lia.
    contradiction. contradiction.
  }
  rewrite SEF4; eauto. intros ?. eapply PV. repeat rewrite plift_or in *. repeat rewrite plift_if in *.
  erewrite lls_change. eapply lls_mono; eauto. eapply vars_locs_mono; eauto.
  unfoldq; intuition. eapply substp_sub'; eauto. unfoldq; intuition.
  subst q0. rewrite plift_empty.  rewrite <- substp_empty_and.
  eapply stchain_tighten. rewrite <- plift_empty. eapply envt_subst_filter_deep. 9: eauto. all: eauto.
  unfoldq; intuition.
  eapply envt_subst_store_deep_wf1; eauto. unfoldq; intuition.
  rewrite <- plift_empty. eapply envt_subst_store_deep_wf2; eauto. unfoldq; intuition.
  
  rewrite SEF2; eauto. intros ?. eapply PV. repeat rewrite plift_or in *. repeat rewrite plift_if in *.
  eapply lls_mono; eauto. eapply vars_locs_mono; eauto.
  unfoldq; intuition. eapply substp_sub'; eauto. unfoldq; intuition.

  (* VAL_TYPE *)
  + eapply HVY.

  (* VAL_QUAL 1 *)
  + remember (vabs l q t0) as vf.
    assert (val_qual (st1 M) (st1 M''') (H1' ++ v1 :: H1)  vf frf (pand (plift p) (plift qf))) as HQF'. {
      eapply envt_subst_valq_store_change1. eapply envt_subst_store_extend. 8: eauto. all: eauto.
      eapply st_trans; eauto. }
    assert (val_qual (st1 M') (st1 M''') (H1' ++ v1 :: H1) vx1 frx (pand (plift p) (plift qx))) as HQX'. {
      eapply envt_subst_valq_store_change1. 3: eauto. eapply envt_subst_store_extend; eauto. eapply st_trans; eauto. 
      all: eauto.  }

    intros ? ?. unfoldq. repeat rewrite plift_or. repeat rewrite plift_if.
    destruct (HQY1 x) as [HY_q | [HY_f | [HY_x | HY_fr]]].
    repeat rewrite app_length. intuition.
    * (* q2, and part of function *)
      destruct HY_q as [? ?].
      left. eapply lls_mono. eapply vars_locs_mono. 2: eauto.
      unfoldq; intuition.
    * (* part of function *)
      destruct fn2. 2: contradiction.
      destruct (HQF' x) as [HF_q | HF_fr]. eauto. 
      -- (* q *) left. eapply lls_mono. 2: eauto. eapply vars_locs_mono. unfoldq; intuition.
      -- (* fr *) 
         destruct frf. 2: contradiction.
         right. simpl. auto.  
    * (* part of arg *)
      destruct ar2. 2: contradiction.
      destruct (HQX' x) as [HX_q | HX_fr]. eauto.
      -- (* q *) left. eapply lls_mono. 2: eauto. eapply vars_locs_mono. unfoldq. intuition. 
      -- (* fr *)
         destruct frx. 2: contradiction.
         right.  simpl.
         destruct (fn2 && frf); simpl. 
         intros ?. eapply HX_fr. eapply SC1. eauto. 
         intros ?. eapply HX_fr. eapply SC1. eauto. 
    * (* fresh *)
      destruct fr2. 2: contradiction.
      right. simpl. 
      destruct (fn2 && frf || ar2 && frx); simpl.
      intros ?. eapply HY_fr. eapply SC2. eapply SC1. eauto.   
      intros ?. eapply HY_fr. eapply SC2. eapply SC1. eauto.   

  (* VAL_QUAL 2 *)
  + remember (vabs l0 q3 t2) as vf.
    assert (val_qual (st2 M) (st2 M''') (H2'++H2) vf frf (subst_pl (pand (plift p) (plift qf)) (length H2)(plift q0))) as HQF'. {
      eapply envt_subst_valq_store_change2. eapply envt_subst_store_extend. 8: eauto. 
      all: eauto. subst q0. rewrite plift_empty in *. rewrite <- substp_empty_and in HQF2. auto. eapply st_trans; eauto.  }
    assert (val_qual (st2 M') (st2 M''') (H2'++H2) vx2 frx (subst_pl (pand (plift p) (plift qx)) (length H2)(plift q0))) as HQX'. {
      eapply envt_subst_valq_store_change2. 3: eauto. eapply envt_subst_store_extend; eauto. eapply st_trans; eauto. eauto. all: eauto.
      subst q0. rewrite plift_empty in *. rewrite <- substp_empty_and in HQX2. auto. }

    intros ? ?. repeat rewrite plift_subst in *.  repeat rewrite plift_or in *. repeat rewrite plift_if in *.
    destruct (HQY2 x) as [HY_q | [HY_f | [HY_x | HY_fr]]].
    repeat rewrite app_length. intuition.
    * (* q2, and part of function *)
      destruct HY_q as [? ?].
      left. eapply lls_mono. eapply vars_locs_mono. 2: eauto.
      unfoldq; intuition. eapply substp_sub' in Q3. eapply Q3 in H20; eauto. 
      eapply substp_sub'; eauto. unfoldq; intuition.
      
    * (* part of function *)
      destruct fn2. 2: contradiction.
      destruct (HQF' x) as [HF_q | HF_fr]. eauto. 
      -- (* q *) left. eapply lls_mono. 2: eauto. eapply vars_locs_mono. 
         unfoldq; intuition. eapply substp_sub' with (p' := (pand (plift p)(plift qf))). 
         unfoldq; intuition. auto.
         eapply substp_sub'; eauto. unfoldq; intuition.
      -- (* fr *) 
         destruct frf. 2: contradiction.
         right. simpl. auto. 
    * (* part of arg *)
      destruct ar2. 2: contradiction.
      destruct (HQX' x) as [HX_q | HX_fr]. eauto.
      -- (* q *) left. eapply lls_mono. 2: eauto. eapply vars_locs_mono.
      unfoldq; intuition. eapply substp_sub' with (p' := (pand (plift p)(plift qx))).
      unfoldq; intuition. auto.
      eapply substp_sub'; eauto. unfoldq; intuition. 
      -- (* fr *)
         destruct frx. 2: contradiction.
         right. simpl.
         destruct (fn2 && frf); simpl. 
         intros ?. eapply HX_fr. eapply SC1. eauto. 
         intros ?. eapply HX_fr. eapply SC1. eauto. 
    * (* fresh *)
      destruct fr2. 2: contradiction.
      right. simpl.
      destruct (fn2 && frf || ar2 && frx); simpl.
      intros ?. eapply HY_fr. eapply SC2. eapply SC1. eauto.   
      intros ?. eapply HY_fr. eapply SC2. eapply SC1. eauto.   
Qed.


Lemma bi_tabs_subst: forall H1 H1' H2 H2' G G' p S1 S2 M T0' fr0' q0' T1 q1 T2 q2 e2 qf t1 t v1 v2'0 q0 T0 fr1 fn1 fr2 fn2 ar2 e2f e2x
  (WFE: env_type_subst2 M (H1'++ v1::H1) (H2'++ H2) (G'++(T0', fr0', q0')::G) p (length G) v2'0 q0)
  (STF: st_filter M (st_locs1 M) (st_locs2 M))
  (L1: length H1 = length G)
  (L2: length H2 = length G)
  (L3: length H1' = length G')
  (L4: length H2' = length G')
  (ST: store_type S1 S2 M)
  (EXP: forall M H1 H1' H2 H2' v1 v2'0,
   val_type (st1 M, st2 M, fun l1 l2 => False, fun l1 l2 v1 v2 => False) H1 H2 v1 v2'0 T0 T0 ->
   val_locs v1 = pempty ->
   val_locs v2'0 = pempty ->
   env_type_subst2 M (H1' ++ v1 :: H1) (H2' ++ H2) ((T1, fr1, qand p (qor q1 (qif fn1 qf)))  :: G' ++ (T0', fr0', q0') :: G) (qor (qand p qf) (qone (length (G' ++ (T0', fr0', q0') :: G)))) (length G) v2'0 q0 ->
   st_filter M (st_locs1 M)(st_locs2 M) ->
      forall S1 S2,
      length H1 = length G ->
      length H2 = length G ->
      length H1' = length ((T1, fr1, qand p (qor q1 (qif fn1 qf))) :: G') ->
      length H2' = length ((T1, fr1, qand p (qor q1 (qif fn1 qf))) :: G') ->
      store_type S1 S2 M ->
      (forall H2'' S2' M' P1,
       sst_chain_partial (st2 M) (st2 M') P1 ->
       sstore_type S2' (st2 M') ->
       True ->
       exists v2 M'' S2'',
         tevaln S2' (H2'' ++ H2) (splice_tm t1 (length H2) (length H2'')) S2'' v2 /\
         store_type S1 S2'' (st_empty (st1 M) (st2 M'')) /\
         sst_chain (st2 M') (st2 M'') /\
         store_effect S2' S2'' pempty /\
         val_type (st_empty (st1 M)(st2 M'')) H1 (H2'' ++ H2) v1 v2 T0 T0  /\
         val_qual (st1 M) (st1 M'') H1 v1 false pempty /\
         val_qual (st2 M) (st2 M'') (H2'' ++ H2) v2  false pempty 
      ) 
       ->
      exists (S1' S2' : stor) (M' : stty) (v1' v2' : vl),
        exp_type1 S1 S2 M (H1' ++ v1 :: H1) (H2' ++ H2) 
        	t (subst_tm t (length H2) (splice_tm t1 (length H2) (length H2')) q0) 
        	S1' S2' M'  v1' v2'
          T2 (subst_ty T2 (length H2) q0)
          (plift (qor (qand p qf)(qone (length (G' ++ (T0', fr0', q0')::G)))))
          (subst_pl (plift (qor (qand p qf)(qone (length (G' ++ (T0', fr0', q0')::G))))) (length H2) (plift q0))
          fr2 fr2
          (plift (qor q2 (qor (qif ar2 (qone (length (G' ++ (T0', fr0', q0') :: G)))) (qif fn2 (qand p qf)))))
          	(subst_pl (plift (qor q2 (qor (qif ar2 (qone (length (G' ++ (T0', fr0', q0') :: G)))) (qif fn2 (qand p qf)))))(length H2) (plift q0))
          (plift (qor e2 (qor (qif e2x (qone (length (G' ++ (T0', fr0', q0') :: G)))) (qif e2f (qand p qf)))))
          	(subst_pl (plift (qor e2 (qor (qif e2x (qone (length (G' ++ (T0', fr0', q0') :: G)))) (qif e2f (qand p qf))))) (length H2) (plift q0))
  )
  (CLF:  closed_ty ((length G'+ S (length G))) (TFun T1 fn1 fr1 q1 T2 fn2 ar2 fr2 q2 e2f e2x e2))
  (VALT: val_type (st1 M, st2 M, fun l1 l2 => False, fun l1 l2 v1 v2 => False) H1 H2 v1 v2'0  T0 T0)
  (V1: val_locs v1 = pempty)
  (V2: val_locs v2'0 = pempty)
  (EMP: q0 = qempty)
  (SUB: psub (plift q1) (pand (plift p) (plift qf)))
  (STW: forall H2'' S2' M' P',
      sst_chain_partial (st2 M)(st2 M') P' ->
      sstore_type S2' (st2 M') ->
      True ->
      exists  (v2 : vl) (M'' : stty) (S2'' : stor),
        tevaln S2' (H2'' ++ H2) (splice_tm t1 (length H2) (length H2'')) S2'' v2 /\
        store_type S1 S2'' (st_empty (st1 M)(st2 M'')) /\
        sst_chain (st2 M')(st2 M'') /\
        store_effect S2' S2'' pempty /\
        val_type (st_empty (st1 M) (st2 M'')) H1 (H2'' ++ H2) v1 v2 T0 T0 /\
        val_qual (st1 M) (st1 M'') H1 v1 false pempty /\
        val_qual (st2 M) (st2 M'') (H2'' ++ H2) v2 false pempty)
  ,
exists (S1' S2' : stor) (M' : stty) (v1' v2' : vl),
  exp_type1 S1 S2 M (H1' ++ v1 :: H1) (H2' ++ H2)
    (tabs (qand p qf) t) (subst_tm (tabs (qand p qf) t) (length H2) (splice_tm t1 (length H2) (length H2')) q0) 
    S1' S2' M' v1' v2'
    (TFun T1 fn1 fr1 q1 T2 fn2 ar2 fr2 q2 e2f e2x e2)
    (subst_ty (TFun T1 fn1 fr1 q1 T2 fn2 ar2 fr2 q2 e2f e2x e2) (length H2) q0)
    (plift p) (subst_pl (plift p) (length H2) (plift q0))
    false false
    (plift qf) (subst_pl (plift qf) (length H2) (plift q0))
    (plift qempty) (subst_pl (plift qempty) (length H2) (plift q0)).
Proof.  
  intros. 
  repeat rewrite plift_or in *. repeat rewrite plift_if in *.  repeat rewrite plift_and in *.  repeat rewrite plift_one in *.
  repeat rewrite plift_empty in *. 
  apply wf_envt_subst2 in WFE as WFE'. all: eauto. 
  destruct WFE' as [P1 [P2 [P3 [P4 P5]]]].
  remember ST as ST'. clear HeqST'.
  destruct ST as [SST1 [SST2 [ST [R L]]]].

  exists S1, S2, M.
  exists (vabs (H1' ++ v1 :: H1)  (qand p qf) t). 
  exists (vabs (H2' ++ H2) (subst_ql (qand p qf) (length H2) q0)(subst_tm t (length H2)(splice_tm (splice_tm t1 (length H2) (length H2')) (length H2) 1) q0)).
  split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 8: split. 9: split.
  
  - (* 1st *)
    exists 1.  intros. destruct n. lia. simpl. eauto.
  
  - (* 2nd *)
    exists 1.  intros. destruct n. lia. simpl. auto.
  
  - eapply st_refl. auto.
  - auto.
  - auto.
  - intros ? ? ? ?. eauto.
  - intros ? ? ? ?. eauto.
  
  - (* results *)
   simpl. 

   repeat split.
   inversion CLF. subst. rewrite app_length. simpl. rewrite L1. rewrite L3. auto.
   inversion CLF. subst. unfoldq; intuition. rewrite app_length. simpl. rewrite L1. rewrite L3. eapply H16 in H. auto.
   inversion CLF. subst. rewrite app_length. simpl. rewrite L1. rewrite L3. auto.
   inversion CLF. subst. unfoldq; intuition. rewrite app_length. simpl. rewrite L1. rewrite L3. eapply H17 in H. auto.
   inversion CLF. subst. unfoldq; intuition. rewrite app_length. simpl. rewrite L1. rewrite L3. eapply H18 in H. auto.
   inversion CLF. subst. rewrite app_length in *. simpl in *. rewrite L2. rewrite L4. eapply substy_closed_gen; eauto.
   subst q0. eapply Q2'; eauto. inversion CLF. subst. rewrite app_length. simpl. auto.
   inversion CLF. subst. rewrite app_length in *. simpl in *. rewrite L2. rewrite L4. eapply substy_closed_gen; eauto.
   subst q0. eapply Q2'; eauto. inversion CLF. subst. rewrite app_length. simpl. auto.
   subst q0. eapply Q2'; eauto. inversion CLF. subst. rewrite app_length. simpl. auto.
   
   rewrite val_locs_abs. 
   eapply envt_subst_store_deep_wf1. eapply WFE. rewrite plift_and. unfoldq; intuition.
   rewrite val_locs_abs. rewrite plift_subst. 
   eapply envt_subst_store_deep_wf2; eauto. rewrite plift_and. unfoldq; intuition.

   
   (* strel same locs *)
   
   rewrite val_locs_abs, val_locs_abs in *. rewrite plift_subst in *. 
   edestruct envt_subst_same_locs. 9: eapply WFE. all: eauto. rewrite plift_and. unfoldq; intuition.
   
   rewrite val_locs_abs, val_locs_abs in *. rewrite plift_subst in *. 
   edestruct envt_subst_same_locs. 9: eapply WFE. all: eauto. rewrite plift_and. unfoldq; intuition.
   
   intros.
      
   repeat rewrite val_locs_abs in H. 
   rewrite plift_subst, plift_and in H.
   rewrite val_locs_abs in H5, H6.
   rewrite plift_subst in H6. 
   rewrite plift_and in H5, H6. 
   assert (env_type_subst2  M'
            (vx1 :: H1' ++ v1 :: H1) (vx2 :: H2' ++ H2) ((T1, fr1, (qand p (qor q1 (qif fn1 qf)))) :: G' ++ (T0', fr0', q0') :: G)
            (qor (qand p qf) (qone (length (G' ++ (T0', fr0', q0') :: G)))) (length G) v2'0 q0) as WFE'. {
 
   eapply envt_subst_extend_all in WFE; eauto.
   - eapply stchain_tighten; eauto. rewrite plift_and. eapply envt_subst_filter_deep; eauto. unfoldq; intuition.
     rewrite plift_and. eapply lls_mono. eapply vars_locs_mono; eauto. unfoldq; intuition.
     rewrite plift_and. eapply lls_mono. eapply vars_locs_mono; eauto. eapply substp_sub'; eauto. unfoldq; intuition.
   - rewrite <- L2. auto.
   - intros ? [? ?]. rewrite plift_and, plift_or. destruct (H5 x) as [F | [L' | Q]]. auto. {
       destruct fn1. 2: contradiction.
       rewrite plift_if. eapply lls_mono. 2: eapply F. eapply vars_locs_mono; eauto. unfoldq; intuition.
      }{
        destruct fr1. 2: contradiction. destruct L'. rewrite plift_and in H7. eauto.
      }{
        rewrite plift_and in H7. rewrite plift_if. 
        eapply lls_mono. 2: eapply Q. eapply vars_locs_mono; eauto. unfoldq; intuition. eapply SUB; eauto.
      }
   - repeat rewrite plift_and. rewrite plift_or, plift_if. 
     intros ? [? ?]. destruct (H6 x) as [F | [L' | Q]]. auto. {
      destruct fn1. 2: contradiction.
      eapply lls_mono. 2: eapply F. eapply vars_locs_mono; eauto. eapply substp_sub'; eauto.
      unfoldq; intuition.
     }{
       destruct fr1. 2: contradiction. destruct L'. eauto.
     }{
       rewrite plift_subst in Q. 
       eapply lls_mono. 2: eapply Q. eapply vars_locs_mono; eauto. 
       eapply substp_sub'; eauto. unfoldq; intuition. eapply SUB; eauto.
     }
   - intros. rewrite plift_subst, plift_and, plift_or in *. 
     subst fr1. intros ? ?. eapply H5 in H7.
     destruct H7 as [ A | [B | C]]. {
     destruct fn1. 2: contradiction.
     simpl in A. eapply lls_mono. 2: eauto. eapply vars_locs_mono. 
     unfoldq. intuition.
     } {
       contradiction.
     } {
       eapply lls_mono. 2: eauto. eapply vars_locs_mono. 
       unfoldq. intuition. eapply SUB; eauto.
     }
   - intros. rewrite plift_subst in *. rewrite plift_and in *. rewrite plift_or in *. 
     subst fr1. intros ? ?. eapply H6 in H7.
     destruct H7 as [ A | [B | C]]. {
       destruct fn1. 2: contradiction.
       simpl in A. eapply lls_mono. 2: eauto. eapply vars_locs_mono.
       eapply substp_sub'; eauto. unfoldq; intuition.
     } {
       contradiction.
     } {
       eapply lls_mono. 2: eauto. eapply vars_locs_mono. 
       eapply substp_sub'; eauto. unfoldq; intuition. eapply SUB; eauto.
     }
   - rewrite plift_and. unfoldq; intuition.
   - repeat rewrite plift_and. rewrite plift_or. unfoldq; intuition. eapply SUB; eauto. rewrite plift_if in H7. destruct fn1; try contradiction. intuition.
   - inversion CLF; subst. auto.
   - eapply closedq_and. left. intros ? ?. eapply P5 in H7. unfold pdom in H7. rewrite app_length in H7. simpl in H7. lia.
   
  }
  
  assert (val_type (st1 M', st2 M', fun l1 l2 => False, fun l1 l2 v1 v2 => False) H1 H2 v1 v2'0 T0 T0) as VT'. {
    eapply valt_store_change. 2: eapply VALT. 
    eapply storet_empty; eauto.
    rewrite V1, V2. repeat rewrite lls_empty. eapply stchain_empty'; eauto.
  }
   
   destruct (EXP M' H1 (vx1::H1') H2 (vx2::H2') v1 v2'0  VT' V1 V2 WFE' H0 S1' S2') as [S1'' [S2'' [M'' [vy1 [vy2 [IEY1 [IEY2 [STC2 [STF2 [ST2 [SEFY1 [SEFY2 [IVY [IYQ1 IYQ2 ]]]]]]]]]]]]]]; intuition. 
   simpl. auto.
   simpl. auto.
     
   destruct (STW H2'' S2'0 M'0  
      (pand (locs_locs_stty (st2 M) (vars_locs (H2' ++ H2)(subst_pl (pand (plift p) (plift qf)) (length H2) (plift q0)))) P0)) as [v2''' [M''' [S2''' ?]]]; intuition.
   eapply sst_trans''; eauto. eapply sstchain_tighten. eapply H; eauto. unfoldq; intuition.
   eapply sstchain_tighten; eauto. unfoldq; intuition.
   intros ? [? ?]. eapply envt_subst_store_deep_wf2 in H10; eauto. unfoldq; intuition.
   exists v2''', M''', S2'''; intuition.
   eapply storet_empty; eauto.
   eapply H3; eauto.
   eapply H10; eauto.
   eapply valt_store_change. 2: eapply H14. eauto.
   rewrite V1. eapply valq_val_empty in H17. rewrite H17. 
   repeat rewrite lls_empty. eapply stchain_empty'; eauto.

   exists S1'', S2'', M'', vy1, vy2. intuition.

   rewrite splice_acc. auto.
   
   (* store preserve *)
   rewrite val_locs_abs. rewrite plift_and in *.
   intros ? ? PV ?. eapply SEFY1. intros VL. eapply PV.
   repeat rewrite plift_or in *. repeat rewrite plift_if in *. repeat rewrite plift_one in *. 
   repeat rewrite pand_or_distribute in VL. repeat  rewrite lls_vars_or in VL.
   destruct VL as [? | [? | ?]].
   left. simpl in H8. replace (vx1::H1' ++ v1::H1) with ([vx1]++H1'++v1::H1) in H8. 2: { auto. }
   rewrite vars_locs_extend in H8. eapply lls_mono. 2: eapply H8. eapply vars_locs_mono. unfoldq; intuition.
   unfoldq; intuition. inversion CLF; subst. eapply H31 in H14. repeat rewrite app_length in H14. simpl in H14. lia. 
   destruct e2x; simpl in H8. right. left. eapply lls_mono. 2: eapply H8. intros ? ?.
   destruct H9 as [? [[? ?] ?]]. simpl in H10. unfold pone in H10. subst x0. destruct H11 as [? [? ?]].
   replace (length (G' ++ (T0', fr0', q0') :: G)) with  (length (H1' ++ v1 :: H1)) in H10.
   2: { repeat rewrite app_length. simpl. lia.  }
   rewrite indexr_head in H10. inversion H10. subst. auto. 
   rewrite pif_false in H8. rewrite pand_empty_r in H8. rewrite vars_locs_empty in H8. rewrite lls_empty in H8. unfoldq; intuition.
   right. right. simpl in H8. replace (vx1::H1' ++ v1::H1) with ([vx1]++H1'++v1::H1) in H8. 2: { auto. } rewrite vars_locs_extend in H8.
   destruct e2f; simpl in H8. eapply lls_mono. 2: eapply H8. eapply vars_locs_mono; eauto. unfoldq; intuition.
   rewrite pif_false in H8. rewrite pand_empty_r in H8. rewrite vars_locs_empty in H8. rewrite lls_empty in H8. unfoldq; intuition.
   unfoldq; intuition. destruct e2f; simpl in *; intuition.
   auto.

   (* store preserve *)
  
   rewrite val_locs_abs. repeat rewrite plift_and in *.
   intros ? ? PV ?. eapply SEFY2. intros VL. eapply PV.
   repeat rewrite plift_subst in *. repeat rewrite plift_or in *. repeat rewrite plift_if in *. rewrite plift_and in *. repeat rewrite plift_one in *. 
   repeat rewrite substp_or in *. repeat rewrite pand_or_distribute in VL. repeat  rewrite lls_vars_or in VL.
   destruct VL as [? | [? | ?]]. simpl in H8.
   left. replace (vx2::H2'++H2) with ([vx2]++H2'++H2) in H8. 2: { auto. }
   rewrite vars_locs_extend in H8. eapply lls_mono. 2: eapply H8. eapply vars_locs_mono. unfoldq; intuition.
   subst q0. rewrite plift_empty. intros ? [? ?]. eapply substp_closed' in H10. unfoldq; intuition.
   rewrite app_length. eauto. rewrite app_length. eauto. intros. inversion CLF; subst. eapply H29 in H11. lia.
   intros. unfoldq; intuition.

   destruct e2x; simpl in H8. right. left. simpl.  eapply lls_mono. 2: eapply H8. intros ? ?.
   destruct H9 as [? [[? ?] ?]]. simpl in H10. destruct H11 as [? [? ?]].
   destruct H10 as [[? ?] | ?]. simpl in *. unfold pone in H10. repeat rewrite app_length in *. simpl in H10. lia.
   destruct H10. simpl in H10. destruct H10. unfold pone in H13. assert (x0 = length (H2' ++H2)). { rewrite app_length in *. simpl in H13. lia. }
   subst x0. rewrite indexr_head in H11. inversion H11. subst. auto. 
   destruct H10. simpl in H13. unfold pone in H13. rewrite app_length in H13. simpl in H13. lia.
   rewrite pif_false in H8. rewrite substp_empty in H8. rewrite pand_empty_r in H8. rewrite vars_locs_empty in H8. rewrite lls_empty in H8. unfoldq; intuition.

   right. right. simpl in H8. replace (vx2::H2'++H2) with ([vx2]++H2'++H2) in H8. 2: { auto. } rewrite vars_locs_extend in H8.
   destruct e2f; simpl in H8. eapply lls_mono. 2: eapply H8. eapply vars_locs_mono; eauto. unfoldq; intuition.
   rewrite pif_false in H8. rewrite substp_empty in H8. rewrite pand_empty_r in H8. rewrite vars_locs_empty in H8. rewrite lls_empty in H8. unfoldq; intuition.
   intros ? [? ?]. eapply substp_closed' in H10. unfoldq. rewrite app_length. eauto.
   intros. eapply pif_psub in H11; eauto. intros ? ?. destruct H12. eapply P5 in H12. unfoldq. rewrite app_length in H12. simpl in H12. lia.
   intros ? ?. subst q0. rewrite plift_empty in H11. unfoldq; intuition.

   auto.
     
   eapply valt_extend1; eauto.
   inversion CLF; subst. rewrite app_length. simpl. rewrite L1. rewrite L3. auto.
   inversion CLF; subst. rewrite app_length. simpl. eapply substy_closed_gen; eauto. rewrite L2. rewrite L4. auto.
   
   rewrite val_locs_abs in *. rename H4 into HVX;
   apply valt_wf in HVX; apply valt_wf in IVY.
   
   
  intros ? ?.
  destruct (IYQ1 x). eauto. 

  repeat rewrite plift_or in *. repeat rewrite plift_and in *. repeat rewrite plift_one in *.
  repeat rewrite pand_or_distribute in H7. repeat rewrite lls_vars_or in H7.
  replace ((vx1::H1')++v1::H1) with ([vx1]++H1'++v1::H1) in H7. 2: { simpl. auto. }
  destruct H7 as [? | [?|  ?]].
  left. erewrite vars_locs_extend in H7. 2: { unfoldq; intuition.  inversion CLF; subst. eapply H30 in H14. rewrite app_length in H14. simpl in H14. lia. }
  split. eapply lls_mono. 2: eapply H7. eapply vars_locs_mono; eauto. unfoldq; intuition.
  eapply lls_mono. 2: eapply H7. eapply vars_locs_mono; eauto. unfoldq; intuition. 
  1,2: inversion CLF; subst; eapply H30 in H14; rewrite app_length in H14; simpl in H14; lia.
  
  (* from arg *)
  right. right. left. destruct ar2; simpl in *.  eapply lls_mono. 2: eapply H7.
  intros ? ?. destruct H8 as [? [? ?]]. destruct H8 as [? ?]. simpl in H10. unfold pone in H10. 
  destruct H9 as [? [? ?]]. subst x1. replace (length (G' ++ (T0', fr0', q0') ::G)) with (length (H1' ++ v1::H1)) in H9. 2:{ repeat rewrite app_length. simpl. lia. } 
  rewrite indexr_head in H9. inversion H9. subst. auto.
  rewrite pif_false in H7. rewrite pand_empty_r in H7. rewrite vars_locs_empty in H7. rewrite lls_empty in H7. unfoldq; intuition.

  (* from func *)
  right. left. 
  destruct fn2; simpl in *. replace (vx1::H1'++v1::H1) with ([vx1]++H1'++v1::H1) in H7. 2: { simpl. auto. }
  rewrite vars_locs_extend in H7. 2: { unfoldq; intuition. }
  eapply lls_mono. 2: eapply H7. eapply vars_locs_mono; eauto. simpl. unfoldq; intuition.
  rewrite pif_false in H7. rewrite pand_empty_r in H7. rewrite vars_locs_empty in H7. rewrite lls_empty in H7. unfoldq; intuition.
  
  (* fr *)
  right. right. right.
  unfold length1. auto.

   (* 2nd *)
  rewrite val_locs_abs in *. rename H4 into HVX;
  apply valt_wf in HVX; apply valt_wf in IVY. 
  repeat rewrite plift_subst in *. repeat rewrite plift_and in *. 
  intros ? ?.  
  destruct (IYQ2 x). intuition. simpl in H7. replace (vx2::H2'++H2) with ([vx2]++H2'++H2) in H7. 2: { simpl. auto. }
  repeat rewrite substp_or in H7. repeat rewrite pand_or_distribute in H7. repeat rewrite lls_vars_or in H7.
  destruct H7 as [? | [?| ?]].
  left. erewrite vars_locs_extend in H7. 
  split. eapply lls_mono. 2: eapply H7. eapply vars_locs_mono; eauto. unfoldq; intuition.
  eapply lls_mono. 2: eapply H7. eapply vars_locs_mono; eauto.
  unfoldq; intuition.  destruct H12 as [[? ?] | ?]. rewrite app_length in H12. simpl in H12. lia.
  destruct H14 as [[? ?] | ?]. destruct H14; destruct H12; intuition.
  assert (x0 = length G' + length G). { rewrite app_length in H16. simpl in H16. lia. }
  subst x0. inversion CLF. subst.  assert (q2 (length G' + length G + 1) =  true). { intuition.  } eapply H33 in H12. lia.
  subst x0. inversion CLF. subst.  assert (q2 (length G' + length G + 1) =  true). { rewrite app_length in H17. simpl in H17. replace (length G' + S(length G)) with (length G' + length G  +1) in H17. intuition. lia. } eapply H32 in H12. lia.
  subst q0. rewrite plift_empty. unfoldq;intuition.
  subst q0. rewrite plift_empty. unfoldq;intuition.
  
  destruct H13; destruct H12; intuition.
  inversion CLF. subst.  
  assert (x0 = (length G' + length G)). { rewrite app_length in H16. simpl in H16. lia.  }
  assert (q2 (length G' + length G + 1) =  true). { subst x0.  intuition.  } eapply H32 in H17. lia.

  inversion CLF. subst. assert (q2 (length G' + length G + 1) =  true). { rewrite app_length in *. simpl in *.  intuition.  } 
  eapply H32 in H12. lia.

  intros ? [? ?]. eapply substp_closed' in H9. unfoldq. rewrite app_length. eauto.
  intros ? ?. inversion CLF. subst. eapply H27 in H10. lia.
  intros ? ?. subst q0. rewrite plift_empty in H10. unfoldq; intuition.
  
    (* from arg *)
  right. right. left. destruct ar2; simpl in *. eapply lls_mono. 2: eapply H7. rewrite app_length in *.
  intros ? ?. destruct H8 as [? [? ?]]. destruct H8 as [? ?]. destruct H10 as [[? ?]|  ?]. simpl in H10; unfold pone in H10. lia.
  destruct H10 as [[? ?] | [? ?]]. simpl in H11. unfold pone in H11.
  assert (x1 = length (H2'++H2)). { repeat rewrite app_length. lia. } subst x1.    
  destruct H9 as [? [? ?]]. rewrite indexr_head in H9. inversion H9. subst. auto.
  destruct H9 as [? [? ?]].
  simpl in H11. unfold pone in H11. assert (x1 = length H2'+ length H2). { repeat rewrite app_length. lia. } lia.
  rewrite pif_false in H7. rewrite substp_empty in H7. rewrite pand_empty_r in H7. rewrite vars_locs_empty in H7. rewrite lls_empty in H7. unfoldq; intuition.
    
    
  (* from func *)
  right. left.
  replace (vx2::H2'++H2) with ([vx2]++H2'++H2) in H7. 2: { simpl. auto. }
  rewrite vars_locs_extend in H7. 
  destruct fn2; simpl in *.
  eapply lls_mono; eauto. eapply vars_locs_mono; eauto. simpl. unfoldq; intuition.
  rewrite pif_false in H7. rewrite substp_empty in H7. rewrite pand_empty_r in H7. rewrite vars_locs_empty in H7. rewrite lls_empty in H7. unfoldq; intuition.
  
  intros ? [? ?]. eapply substp_closed' in H9. unfoldq. rewrite app_length. eauto.
  intros. eapply pif_psub in H10. eauto. eauto. intros ? ?. destruct H11. eapply P5 in H11. unfoldq. rewrite app_length in H11. simpl in H11. lia.
  intros ? ?. subst q0. rewrite plift_empty in H10. unfoldq; intuition.
    
  (* fresh *)
  right. right. right.
  destruct fr2; simpl in *. unfold length2. auto. contradiction.
   
 - eapply valq_abs; eauto.
 - subst q0. repeat rewrite plift_empty in *. rewrite substq_empty_and. 
    intros ? ?. rewrite val_locs_abs, plift_and in H. repeat rewrite plift_subst in H. repeat rewrite plift_empty in H. rewrite pif_false. left. auto.
Unshelve. all: eauto. 
Qed.


Lemma bi_qsub_subst: forall S1 S2 M H1 H1' v1 H2 H2' G' T0 fr0 q0 G S1' S2' M' t t1 T p q1 q2 e1 e2  v1' v2' v2'0 fr1 fr2
  (WFE: env_type_subst2 M (H1'++ v1::H1) (H2'++ H2) (G'++(T0, fr0, q0)::G) p (length G) v2'0 qempty)
  (ST: store_type S1 S2 M)
  (IE: exp_type1 S1 S2 M (H1' ++ v1 :: H1) (H2' ++ H2) 
       t (subst_tm t (length H2) (splice_tm t1 (length H2) (length H2')) qempty) 
       S1' S2' M' v1' v2' 
       T  (subst_ty T (length H2) qempty)
       (plift p) (subst_pl (plift p) (length H2) pempty)
       fr1 fr1
       (plift q1) (subst_pl (plift q1) (length H2) pempty)
       (plift e1) (subst_pl (plift e1) (length H2) pempty)
  )
  (L1: length H1 = length G)
  (L2: length H2 = length G)
  (L3: length H1' = length G')
  (L4: length H2' = length G'),
  psub (plift q1) (plift q2) ->
  psub (plift q2) (pdom (G' ++ (T0, fr0, q0) :: G)) ->
  psub (plift e1) (plift e2) ->
  psub (plift e2) (pdom (G' ++ (T0, fr0, q0) :: G))  ->
  exists S1'' S2'' M'' v1' v2',
  exp_type1 S1 S2 M (H1'++v1::H1) (H2'++H2) 
  t (subst_tm t (length H2) (splice_tm t1 (length H2) (length H2')) qempty) 
  S1'' S2'' M'' v1' v2' 
  T (subst_ty T (length H2) qempty) 
  (plift p) (subst_pl (plift p) (length H2) pempty) 
  (fr1 || fr2) (fr1 || fr2)
  (plift q2) (subst_pl (plift q2) (length H2) pempty)
  (plift e2) (subst_pl (plift e2) (length H2) pempty).
Proof.    
  intros.  
  destruct IE as [IE1 [IE2 [SC1 [STF1 [ST1 [SE1 [SE2 [HVX [HQX1 HQX2]]]]]]]]].
  assert (psub (plift q2) (pdom (H1'++v1::H1))). {
    unfoldq. rewrite app_length in *. simpl in *. rewrite L1, L3. auto. } 
  exists S1', S2', M'. exists v1', v2'. 
  split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 8: split. 9: split.
  eauto. eauto. eauto. eauto. eauto. 
  eapply se_sub; eauto. eapply lls_mono. eapply vars_locs_mono. unfoldq; intuition.
  eapply se_sub; eauto. eapply lls_mono. eapply vars_locs_mono. unfoldq; intuition. eapply substp_sub'; eauto.
  eauto.
  eapply valq_sub; eauto. unfoldq; intuition. unfoldq; intuition.
  eapply valq_sub; eauto. unfoldq; intuition. eapply substp_sub'; eauto. 
  unfoldq; intuition. rewrite app_length. eapply substp_closed'; eauto.
  rewrite app_length in *. simpl in *. rewrite L1, L3 in H5. rewrite L2, L4. auto.
  intuition.
Qed.

Lemma bi_sub_var_subst: forall S1 S2 M H1 H1' v1 H2 H2' G' T0 fr0 q0 G S1' S2' M' t t1 T p q1 e1 v1' v2' v2'0 Tx qx fr1 x
  (WFE: env_type_subst2 M (H1'++ v1::H1) (H2'++ H2) (G'++(T0, fr0, q0)::G) p (length G) v2'0 qempty)
  (ST: store_type S1 S2 M)
  (IE: exp_type1 S1 S2 M (H1' ++ v1 :: H1) (H2' ++ H2) 
       t (subst_tm t (length H2) (splice_tm t1 (length H2) (length H2')) qempty) 
       S1' S2' M' v1' v2' 
       T  (subst_ty T (length H2) qempty)
       (plift p) (subst_pl (plift p) (length H2) pempty)
       fr1 fr1
       (plift q1) (subst_pl (plift q1) (length H2) pempty)
       (plift e1) (subst_pl (plift e1) (length H2) pempty)
  )
  (L1: length H1 = length G)
  (L2: length H2 = length G)
  (L3: length H1' = length G')
  (L4: length H2' = length G')
  (V1: val_locs v1 = pempty)
  (V2: val_locs v2'0 = pempty)
  (Hcl: closed_ql (length G' + S (length G)) q1),
  plift q1 x ->
  indexr x (G' ++ (T0, fr0, q0) :: G) = Some (Tx, false, qx) ->
  psub (plift qx) (plift p) ->
  exists S1'' S2'' M'' v1' v2',
  exp_type1 S1 S2 M (H1'++v1::H1) (H2'++H2) 
  t (subst_tm t (length H2) (splice_tm t1 (length H2) (length H2')) qempty) 
  S1'' S2'' M'' v1' v2' 
  T (subst_ty T (length H2) qempty) 
  (plift p) (subst_pl (plift p) (length H2) pempty) 
  fr1 fr1
  (por (pdiff (plift q1)(pone x)) (plift qx))(subst_pl (por (pdiff (plift q1) (pone x)) (plift qx)) (length H2) pempty)
  (plift e1) (subst_pl (plift e1) (length H2) pempty).
Proof. 
intros. rename x into z. 
destruct IE as [IE1 [IE2 [SC1 [STF1 [ST1 [SE1 [SE2 [HVX [HQX1 HQX2]]]]]]]]].

exists S1', S2', M'. exists v1', v2'. 
split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 8: split. 9: split.
- eauto. 
- eauto. 
- eauto. 
- eauto. 
- eauto. 
- eapply se_sub; eauto. eapply lls_mono. eapply vars_locs_mono. unfoldq; intuition.
- eapply se_sub; eauto. eapply lls_mono. eapply vars_locs_mono. unfoldq; intuition.
- eauto.

- eapply WFE in H0 as HZ.
  intros ? ?. destruct (HQX1 x). eauto.
  * eapply lls_vars in H5. destruct H5. bdestruct (x0 =? z).
    + subst. destruct HZ as [vz1 [vz2 ?]]. intuition.      
      eapply lls_var in H9. destruct H9 as (? & ? & ?). rewrite H9 in H5.
      inversion H5. subst x0. destruct H6. intuition. 
      left.
      erewrite lls_change with (M':=(st1 M')) in H14.
      erewrite lls_change with (M:= (st1 M)) (M':=(st1 M')) in H14.
      eapply lls_mono. 2: eapply H14. eapply vars_locs_mono.
      unfoldq. intuition. 
      eauto. 
      eapply stchain_tighten. eapply envt_subst_filter_deep; eauto. eauto. eapply envt_subst_store_deep_wf1. eauto. eauto. 
      eapply envt_subst_store_deep_wf2. eauto. eauto. eauto. eauto.
      eapply stchain_tighten. eapply valt_filter; eauto. eauto. eapply valt_deep_wf; eauto. eapply valt_deep_wf; eauto.
    + left. eapply lls_vars'. eapply H5. unfoldq. intuition.
  * right. intuition.
 - intros ? ?. destruct (HQX2 x). auto.
   eapply lls_vars in H5. destruct H5.  destruct H5 as [[? ?] ?].
   bdestruct (z =? length G); bdestruct (x0 =? z); intuition.
   -- (* z = length G /\ x0 = z *)
      left. subst x0. subst z. rewrite L2 in *.
      eapply lls_vars'. eauto. split. auto.
      rewrite substp_or. left. unfold subst_pl. right.
      left. split. lia. unfold pdiff. split. 
      --- destruct H6 as [[A1 A2] | B].
          ---- destruct A2 as [[[AA1 AA2] | [AB1 AB2 ]] | AC].
               auto.
               lia.
               unfoldq; intuition.
          ---- destruct B as [BA | BB]; intuition.
      --- intros ?. unfoldq; intuition.
    -- (* z = length G /\ x0 <> z *)
       left. eapply lls_vars'. eauto. split. auto.
       unfold subst_pl. destruct H6 as [[A1 A2] | B].
       --- destruct A2 as [[[AA1 AA2] | [AB1 AB2 ]] | AC].
           right. left. split. auto. left. split; auto. intros ?. unfoldq; intuition.
           right. right. split. auto. left. split. auto. intros ?. unfoldq; intuition.
           unfoldq; intuition.
       --- destruct B as [[BA1 BA2] | [BB1 BB2]].
           right. left. split. auto. left. split; auto. intros ?. unfoldq; intuition.
           right. right. split. auto. left. split. auto. intros ?. unfoldq; intuition.
    -- (* z <> length G /\ x0 = z *)
       bdestruct (z <? length G).
       --- (* z < length G /\ x0 = z *)
           assert ((plift p) z). {
           destruct H5 as [[A1 A2] | B]. 
           ---- (* p (len G) *)
                destruct A2 as [[[AA1 AA2] | [AB1 AB2 ]] | AC].
                lia.
                subst x0. auto.
                unfoldq; intuition.
           ---- destruct B as [[BA1 BA2] | [BB1 BB2]].
                lia.
                subst x0. auto.
          }
          subst x0. eapply WFE in H0 as HZ. destruct HZ as [vz1 [vz2 ?]]. intuition.
          left. eapply lls_var in H7. destruct H7 as [? [? ?]]. 
          rewrite H7 in H18. inversion H18. subst x0. rewrite plift_empty in *.
          erewrite lls_change with (M':=(st2 M')) in H17.
          erewrite lls_change with (M:= (st2 M)) (M':=(st2 M')) in H17.
          eapply lls_mono. 2: eapply H17. eapply vars_locs_mono.
          rewrite substp_or. unfoldq; intuition. eapply substp_sub'; eauto. rewrite L2. auto.
          right. rewrite L2. auto. eauto.
          eapply stchain_tighten. rewrite <- L2. rewrite <- plift_empty. eapply envt_subst_filter_deep. 9: eapply WFE. all: eauto.
          eapply envt_subst_store_deep_wf1; eauto. 
          rewrite <- L2. rewrite <- plift_empty. eapply envt_subst_store_deep_wf2; eauto.
          eapply stchain_tighten. eapply valt_filter; eauto. eauto. eapply valt_deep_wf; eauto. eapply valt_deep_wf; eauto.
       --- (* z > length G /\ x0 = z *)
          left. eapply lls_vars'. eauto. split; auto.
          unfold subst_pl. right. left. split; auto. lia.
          left. split.
          { 
          destruct H6 as [[A1 A2] | B]. 
           ---- (* q1 (len G) *)
                destruct A2 as [[[AA1 AA2] | [AB1 AB2 ]] | AC].
                auto.
                lia.
                unfoldq; intuition.
           ---- destruct B as [[BA1 BA2] | [BB1 BB2]].
                auto.
                lia.
          }
          unfoldq; intuition.
  -- (* z <> length G /\ x0 <> z *)
     left. bdestruct (x0 <? length G); bdestruct (z <? length G); intuition.
     --- (* x0 < length G /\ z < length G /\ x0 <> z *)
         eapply lls_vars'. eauto. split; auto.
         unfold subst_pl. right. right. split; auto. lia.
         left. split. 
         { 
          destruct H6 as [[A1 A2] | B]. 
           ---- (* q1 (len G) *)
                destruct A2 as [[[AA1 AA2] | [AB1 AB2 ]] | AC].
                lia.
                auto.
                unfoldq; intuition.
           ---- destruct B as [[BA1 BA2] | [BB1 BB2]].
                lia.
                auto.
          }
          unfoldq; intuition.
     --- (* z > length G /\ x0 < length G *)
         eapply lls_vars'. eauto. split; auto.
         unfold subst_pl. right. right. split; auto. lia.
         left. split. 
         { 
          destruct H6 as [[A1 A2] | B]. 
           ---- (* q1 (len G) *)
                destruct A2 as [[[AA1 AA2] | [AB1 AB2 ]] | AC].
                lia.
                auto.
                unfoldq; intuition.
           ---- destruct B as [[BA1 BA2] | [BB1 BB2]].
                lia.
                auto.
          }
          unfoldq; intuition.
     --- (* z < length G /\ x0 > length G *)
          eapply lls_vars'. eauto. split; auto.
         unfold subst_pl. right. left. split; auto. lia.
         left. split. 
         { 
          destruct H6 as [[A1 A2] | B]. 
           ---- (* q1 (len G) *)
                destruct A2 as [[[AA1 AA2] | [AB1 AB2 ]] | AC].
                auto.
                lia.
                unfoldq; intuition.
           ---- destruct B as [[BA1 BA2] | [BB1 BB2]].
                auto.
                lia.
          }
          unfoldq; intuition.
     --- (* x0 <> z /\ x0 >= length G /\ z > length G *)
         assert (plift (p) (x0 + 1)). {
         destruct H5 as [[A1 A2] | B]. 
         ---- (* q1 (len G) *)
              destruct A2 as [[[AA1 AA2] | [AB1 AB2 ]] | AC].
              auto.
              lia.
              unfoldq; intuition.
         ---- destruct B as [[BA1 BA2] | [BB1 BB2]].
              auto.
              lia.
         }
         bdestruct (x0 + 1 =? z); intuition.
         {
         rewrite H13 in H12. assert (z > length G). lia.
         eapply WFE in H0 as HZ. destruct HZ as [vz1 [vz2 ?]]. intuition.
         eapply lls_var in H7. destruct H7 as [? [? ?]].
          subst z. replace (x0 + 1 -1) with x0 in H20. 2:{ lia. } 
          rewrite H7 in H20. inversion H20. subst x1. rewrite plift_empty in *.
          erewrite lls_change with (M':=(st2 M')) in H21.
          erewrite lls_change with (M:= (st2 M)) (M':=(st2 M')) in H21.
          eapply lls_mono. 2: eapply H21. eapply vars_locs_mono.
          rewrite substp_or. unfoldq; intuition. eapply substp_sub'; eauto. rewrite L2. auto.
          right. rewrite L2. auto. eauto.
          eapply stchain_tighten. rewrite <- L2. rewrite <- plift_empty. eapply envt_subst_filter_deep. 9: eapply WFE. all: eauto.
          eapply envt_subst_store_deep_wf1; eauto. 
          rewrite <- L2. rewrite <- plift_empty. eapply envt_subst_store_deep_wf2; eauto.
          eapply stchain_tighten. eapply valt_filter; eauto. eauto. eapply valt_deep_wf; eauto. eapply valt_deep_wf; eauto.
         }{
         eapply lls_vars'. eauto. split; auto. 
     unfold subst_pl. right. left. intuition. left. split.

     { 
      destruct H6 as [[A1 A2] | B]. 
       ---- (* q1 (len G) *)
            destruct A2 as [[[AA1 AA2] | [AB1 AB2 ]] | AC].
            auto.
            lia.
            unfoldq; intuition.
       ---- destruct B as [[BA1 BA2] | [BB1 BB2]].
            auto.
            lia.
      }
      intros ?. unfoldq; intuition.
         }

  -- right. intuition.
Qed.      
    

Lemma bi_tseq_subst: forall S1 S2 M H1' v1 H11 H2' H12 t1 t2 t0 q1 S1' S2' M' v1' v2' S1'' S2'' M'' v3 v4 q2 e1 e2 p1 p2 p G' G T0 fr0 q0 v2'0
  (WFE: env_type_subst2 M (H1'++ v1::H11) (H2'++ H12) (G'++(T0, fr0, q0)::G) p (length G) v2'0 qempty)
  (L1: length H11 = length G)
  (L2: length H12 = length G)
  (L3: length H1' = length G')
  (L4: length H2' = length G')
  (V1: val_locs v1 = pempty)
  (V2: val_locs v2'0 = pempty)
  (ST: store_type S1 S2 M)
  (E1: exp_type1 S1 S2 M (H1' ++ v1 :: H11) (H2' ++ H12) 
          t1 (subst_tm t1 (length H12) (splice_tm t0 (length H12) (length H2')) qempty)
          S1' S2' M' v1' v2'
          TBool  (subst_ty  TBool (length H12) qempty)
          (plift p1) (subst_pl (plift p1) (length H12) pempty)
          false false
          (plift q1) (subst_pl (plift q1) (length H12) pempty)
          (plift e1) (subst_pl (plift e1) (length H12) pempty))
  (E2: exp_type1 S1' S2' M' (H1' ++ v1 :: H11) (H2' ++ H12) 
          t2 (subst_tm t2 (length H12) (splice_tm t0 (length H12) (length H2')) qempty)
          S1'' S2'' M'' v3 v4 
          TBool (subst_ty TBool (length H12) qempty)
          (plift p2) (subst_pl (plift p2) (length H12) pempty)
          false false 
          (plift q2) (subst_pl (plift q2) (length H12) pempty)
          (plift e2) (subst_pl (plift e2) (length H12) pempty))
  (SUB1: psub (plift p1)(plift p))
  (SUB2: psub (plift p2)(plift p)), 
  exists (S1'0 S2'0 : stor) (M'0 : stty) (v1'0 v2'0 : vl),
    exp_type1 S1 S2 M (H1' ++ v1 :: H11) (H2' ++ H12)
      (tseq t1 t2) (subst_tm (tseq t1 t2) (length H12) (splice_tm t0 (length H12) (length H2')) qempty) 
      S1'0 S2'0 M'0 v1'0 v2'0 
      TBool (subst_ty TBool (length H12) qempty)
      (plift p) (subst_pl (plift p) (length H12) pempty)
      false false
      pempty (subst_pl pempty (length H12) pempty)
      (por (plift e1) (plift e2)) (subst_pl (por (plift e1) (plift e2)) (length H12) pempty). 
Proof.  
  intros. 
  destruct E1 as [IE1 [IE2 [SC1 [STF1 [ST1 [SE1 [SE2 [HV1 [HQ1 HQ2]]]]]]]]].
  destruct v1'; destruct v2'; try solve [inversion HV1]. simpl in HV1.
  destruct HV1 as [HT [LS1 [LS2 VT]]].
  remember ST1 as ST1'. clear HeqST1'.
  destruct ST1 as [STL1 [STL2 [SP1 [SP2 SP3]]]].

  eapply envt_subst_store_extend in WFE as WFE'. all: eauto.
  assert (env_type_subst2 M' (H1'++ v1::H11) (H2'++ H12) (G'++(T0, fr0, q0)::G) p2 (length G) v2'0 qempty) as WFE2. { 
    eapply envt_subst_tighten; eauto. }

  destruct E2 as [IE3 [IE4 [SC2 [STF2 [ST2 [SE3 [SE4 [HV2 [HQ3 HQ4]]]]]]]]].
  destruct v3; destruct v4; try solve [inversion HV2]. simpl in HV2.
  subst b0.
  remember ST2 as ST2'. clear HeqST2'.
  destruct ST2 as [STL3 [STL4 [SP4 [SP5 SP6]]]].

  exists S1'', S2''.
  exists M''.
  exists (vbool (b && b1)), (vbool (b && b1)).

  split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 8: split. 9: split.
  + (* first one *)
  destruct IE1 as [n1 IE1].
  destruct IE3 as [n3 IE3].
  exists (S(n1 + n3)). intros. destruct n. intuition.
  simpl. rewrite IE1. rewrite IE3.
  auto. lia. lia.
  
  + destruct IE2 as [n2 IE2].
  destruct IE4 as [n4 IE4].
  exists (S(n2 + n4)). intros. destruct n. intuition.
  simpl. rewrite IE2. rewrite IE4. 
  auto. lia. lia.

  + eapply st_trans; eauto. 
  
  + eauto.
  
  + (* store typing *)
    eauto.

  + (* effects 1  *)
  eapply se_trans; eapply se_sub; eauto. eapply lls_mono; eapply vars_locs_mono; eauto. unfoldq; intuition. 
  erewrite <- lls_change with (M := (st1 M)). eapply lls_mono; eapply vars_locs_mono; eauto. unfoldq; intuition.
  eapply stchain_tighten. eapply envt_subst_filter_deep. all: eauto.  unfoldq; intuition.
  eapply envt_subst_store_deep_wf1. eapply WFE. unfoldq; intuition.
  eapply envt_subst_store_deep_wf2; eauto. unfoldq; intuition. 
 
  + (* effects 2 *)
  eapply se_trans; eapply se_sub; eauto. eapply lls_mono; eapply vars_locs_mono; eauto. repeat rewrite substp_or. unfoldq; intuition. eapply substp_sub'. intros ? ?. eapply SUB1; eauto. auto. 
  erewrite <- lls_change with (M := (st2 M)). eapply lls_mono; eapply vars_locs_mono; eauto. 
  repeat rewrite substp_or. unfoldq; intuition. eapply substp_sub'. intros ? ?. eapply SUB2; eauto. auto. 
  eapply stchain_tighten. rewrite <- substp_empty_and. rewrite <- plift_empty. eapply envt_subst_filter_deep. 9: eapply WFE; eauto. all: eauto. unfoldq; intuition. 
  eapply envt_subst_store_deep_wf1. eapply WFE. unfoldq; intuition.
  rewrite <- substp_empty_and. rewrite <- plift_empty.
  eapply envt_subst_store_deep_wf2. eapply WFE. all: eauto. unfoldq; intuition.
  
  + (* valt *)
  constructor.

  + (* valq 1 *)
  eapply valq_bool. 
  
  + (* valq 2 *)
  eapply valq_bool.
Qed.

(*******************************************************************************
  
  general semantic substitution

********************************************************************************)

Lemma st_subst: forall G0 t2 T0 fr0 q0 T2 p2 fr2 q2 e2
  (W: has_type G0 t2 T2 p2 fr2 q2 e2), 
  forall G' G, G0 = G'++(T0, fr0, q0) ::G ->
    closed_ty (length G) T0 ->
    closed_ql (length G) q0 ->
    closed_ty (length G' +  S (length G)) T2 ->
    closed_ql (length G' + S (length G)) p2 ->
    closed_ql (length G' + S (length G)) q2 ->
    closed_ql (length G' + S (length G)) e2 ->
  forall t1 p1 q1,
  closed_ql (length G) q1 ->
  closed_ql (length G) p1 -> 
  q1 = qempty  -> 
  has_type G t1 T0 p1 false q1 qempty  -> 
  forall MW H1 H1' H2 H2' v1 v2'0,
    val_type (st1 MW, st2 MW, fun l1 l2 => False, fun l1 l2 v1 v2 => False) H1 H2 v1 v2'0 T0 T0 ->     
    val_locs v1 = pempty ->
    val_locs v2'0 = pempty ->
    env_type_subst2 MW (H1'++v1::H1) (H2'++H2) G0 p2 (length G) v2'0 q1   ->
    st_filter MW (st_locs1 MW)(st_locs2 MW) ->
    forall S1 S2 (* S1' *),
    length H1 = length G ->
    length H2 = length G ->
    length H1' = length G' ->
    length H2' = length G' ->
    store_type S1 S2 MW ->
    (forall H2'' S2' M' P1,
     sst_chain_partial (st2 MW) (st2 M') P1 ->
     sstore_type S2' (st2 M') ->
     True ->
     exists v2 M'' S2'', 
     tevaln S2' (H2''++H2) (splice_tm t1 (length H2) (length H2'')) S2'' v2 /\
     store_type S1 S2'' (st_empty (st1 MW) (st2 M''))  /\
     sst_chain (st2 M') (st2 M'') /\
     store_effect S2' S2'' pempty /\
     val_type (st_empty (st1 MW) (st2 M'')) H1 (H2''++H2) v1 v2 T0 T0 /\
     val_qual (st1 MW) (st1 M'') H1 v1 false pempty  /\
     val_qual (st2 MW) (st2 M'') (H2''++H2) v2  false pempty 
     )  -> (* via st_weaken + store_invariance *)
    exists  S1'' S2'' M'' v1'' v2'',
      exp_type1 S1 S2 MW (H1'++v1::H1) (H2'++H2) 
        t2 (subst_tm t2 (length H2) (splice_tm t1 (length H2) (length H2')) q1)
        S1'' S2'' M'' v1'' v2''
        T2  (subst_ty T2 (length H2) q1)
        (plift p2) (subst_pl (plift p2) (length H2) (plift q1))
        fr2 fr2
        (plift q2) (subst_pl (plift q2) (length H2) (plift q1))
        (plift e2) (subst_pl (plift e2) (length H2) (plift q1)).
Proof.  
  intros ? ? ? ? ? ? ? ? ? ? W.
  induction W; intros.
  - (* ttrue *)
    simpl. rewrite plift_empty. repeat rewrite substp_empty.
    exists S1, S2, MW, (vbool true), (vbool true).
    eapply bi_true_splice; auto. 

  - simpl. rewrite plift_empty. repeat rewrite substp_empty.
    exists S1, S2, MW, (vbool false), (vbool false).
    eapply bi_false_splice; auto. 
  
  - (* tvar *)
    subst env.
    assert (sst_chain_partial (st2 MW) (st2 MW) (st_locs2 MW)) as SSC2. { eapply st_refl; eauto. }
    assert (sstore_type S2 (st2 MW)) as SST2. { eapply H23; eauto. }
    assert (store_effect S2 S2 pempty) as SE2. { intros ? ? ? ?. auto. }
    destruct (H24 H2' S2 MW (st_locs2 MW) SSC2 SST2 ) as [v2' [M'' [S2'' [IE2 [SST2' [SSC2' [EFF2 [IVAT [IVAQ1 IVAQ2]]]]]]]]]; auto.
    rewrite plift_empty. rewrite substp_empty. repeat rewrite plift_empty. rewrite plift_one.  
    eapply bi_var_subst2. 3: eauto. eauto. eauto.  1-11: eauto. eauto. 3: eauto.
    eapply SST2'; eauto. eapply SSC2'; eauto. 
    rewrite splicety_id. eapply valt_store_change. 2: eapply IVAT. eapply storet_empty; eauto. eapply SST2'; eauto. eapply SST2'; eauto.
    {
      unfold st1, st2.  simpl. rewrite H15. eapply valq_val_empty in IVAQ2; eauto. rewrite IVAQ2. repeat rewrite lls_empty.
      eapply stchain_empty'; eauto.
    }

    rewrite H20. auto.

    unfold st1, st2. simpl. intros ? ?. rewrite H15 in H1. rewrite lls_empty in H1. unfoldq; intuition.
    unfold st1, st2. simpl. intros ? ?. eapply valq_val_empty in IVAQ2; eauto. rewrite IVAQ2 in H1. rewrite lls_empty in H1. unfoldq; intuition.
    auto. auto. eauto. auto.
    
  - (* tref *)
    subst env.
    assert (closed_ty (length G'+ S(length G)) T). {
      inversion H3. auto.
    }
    specialize (IHW G' G). intuition. 
    rename H24 into IHW.
    specialize (IHW t1 p1 q1). intuition.
    rename H25 into IHW.
    destruct (IHW MW H11 H1' H12 H2' v1 v2'0 H13 H14 H15 H16 H17 S1 S2) as [S1'' [S2'' [M'' [v1'' [v2'' ?]]]]]; intuition.
    eapply bi_tref_subst; eauto. 

  - (* tget 1*)
    subst env.
    eapply has_type_closed_subst in W as Hcl; eauto.
    rewrite app_length in *.  simpl in Hcl.
        
    specialize (IHW G' G); intuition.
    rename H26 into IHW.
    specialize (IHW t1 p1 q2); intuition.
    rename H28 into IHW.
    destruct (IHW MW H11 H1' H12 H2' v1 v2'0 H13 H14 H15 H16 H17 S1 S2) as [S1'' [S2'' [M'' [v1'' [v2'' ?]]]]]; auto.

    eapply bi_tget1_subst; eauto. 

  - (* tget 2 *)
    subst env.
    eapply has_type_closed_subst in W as Hcl; eauto.
    rewrite app_length in *.  simpl in Hcl.
        
    specialize (IHW G' G); intuition.
    rename H25 into IHW.
    specialize (IHW t1 p1 q2); intuition.
    rename H27 into IHW.
    destruct (IHW MW H10 H1' H11 H2' v1 v2'0 H12 H13 H14 H15 H16 S1 S2) as [S1'' [S2'' [M'' [v1'' [v2'' ?]]]]]; auto.
    eapply bi_tget2_subst; eauto. 

  - (* tget *)  
    subst env.
    eapply has_type_closed_subst in W as Hcl; eauto.
    rewrite app_length in *.  simpl in Hcl.

    specialize (IHW G' G); intuition.
    rename H26 into IHW.
    specialize (IHW t1 p1 q2); intuition.
    rename H28 into IHW.
    destruct (IHW MW H11 H1' H12 H2' v1 v2'0 H13 H14 H15 H16 H17 S1 S2) as [S1'' [S2'' [M'' [v1'' [v2'' ?]]]]]; auto.
    eapply bi_tget_subst; eauto. 

  - (* tput *) 
    subst env.
    (* 1st IH *)
    eapply has_type_closed_subst in W1; eauto. rewrite app_length in W1. simpl in W1.
    eapply has_type_closed_subst in W2; eauto. rewrite app_length in W2. simpl in W2.
    
    specialize(IHW1 G' G); intuition.
    rename H28 into IHW1.
    specialize(IHW1 t0 p1 q3); intuition. 
    rename H31 into IHW1.
    destruct (IHW1 MW H10 H1' H11 H2' v1 v2'0 H12 H13 H14 H15 H16 S1 S2) as [S1'' [S2'' [M'' [v1'' [v2'' IE1]]]]]; eauto.

    (* 2nd IH*)
    assert (env_type_subst2 M'' (H1'++v1::H10) (H2'++H11) (G'++(T0, fr0, q0)::G) p (length G) v2'0  q3)  as WFE1.
    eapply envt_subst_store_extend; eauto. apply IE1.
    assert (store_type S1'' S2'' M'' ) as ST'.
    apply IE1.
    assert (st_filter M'' (st_locs1 M'')(st_locs2 M'')) as SF'. apply IE1.
    
    specialize(IHW2 G' G); intuition.
    rename H28 into IHW2.
  
   assert (st_chain MW M'') as SC0. apply IE1.

    assert (val_type ((st1 M''), (st2 M''), fun l1 l2 => False, fun l1 l2 v1 v2 => False)  H10 H11 v1 v2'0 T0 T0) as VT.
    eapply valt_store_change. eauto. eapply valt_store_change. 2: eauto. 
    eapply storet_empty. eapply H21. eapply H21.
    rewrite H13, H14. repeat rewrite lls_empty. eapply stchain_empty'; eauto.
    rewrite H13, H14. repeat rewrite lls_empty. eapply stchain_empty'; eauto.

    specialize(IHW2 t0 p1 q3); intuition. 
    rename H31 into IHW2.

    destruct (IHW2 M''  H10 H1' H11 H2' v1 v2'0 VT H13 H14 WFE1 SF' S1'' S2'') as [S1'''' [S2'''' [M'''' [v3 [v4 IE2]]]]]; auto.

    intros.
    destruct (H22 H2'' S2' M' (pand (st_locs2 MW) P1)) as [v2''' [M'''0 [S2'''0 [? [? [? [? [? [? ?]]]]]]]]].
    eapply sst_trans'. eapply SC0. unfoldq; intuition. eapply sstchain_tighten. eapply H28. 
    unfoldq; intuition. eauto. eauto.
    
    exists v2''', M'''0, S2'''0; intuition. 
    eapply storet_empty; eauto. eapply ST'; eauto. eapply H34; eauto.    
    {
      eapply valt_store_change; eauto.
      eapply valq_val_empty in H38, H39. rewrite H38, H39. repeat rewrite lls_empty; eauto. eapply stchain_empty'; eauto.
     }
    
    eapply bi_tput_subst; eauto. 
   
  - (* tapp *)
    subst env.

    (* 1st IH *)
    eapply has_type_closed_subst in W1; eauto. rewrite app_length in W1. simpl in W1.
    eapply has_type_closed_subst in W2; eauto. rewrite app_length in W2. simpl in W2.

    specialize (IHW1 G' G); intuition.
    rename H32 into IHW1.
    specialize (IHW1 t1 p1 q3); intuition.
    rename H35 into IHW1.
    specialize (IHW1 MW H14 H1' H15 H2' v1 v2'0 H16 H17 H18 H19 H20 S1 S2) as [S1' [S2' [M' [vf1 [vf2 IEF]]]]]; auto.

    (* 2nd IH *)
    specialize (IHW2 G' G); intuition.
    rename H32 into IHW2.
    specialize (IHW2 t1 p1 q3); intuition.
    rename H35 into IHW2.

    assert (env_type_subst2 M' (H1'++ v1::H14) (H2'++ H15) (G'++(T0, fr0, q0)::G) p (length G) v2'0 q3) as WFE1.
    eapply envt_subst_store_extend; eauto. eapply IEF.
    assert (store_type S1' S2'  M' ) as ST'.
    eapply IEF.

    assert (st_chain MW M') as SC0. apply IEF.
    assert (st_filter M' (st_locs1 M')(st_locs2 M')) as SF'. apply IEF.

    assert (val_type (st1 M', st2 M', fun l1 l2 => False, fun l1 l2 v1 v2 => False) H14 H15 v1 v2'0 T0 T0) as VT.
    eapply valt_store_extend. 2: eapply H16. eapply storet_empty. 
    eapply H25. eapply H25.
    unfold st_locs1.
    {
      split. 2: split. 3: split. 4: split. 5: split.
      - eapply stfilter_empty'; eauto.
      - unfold st_locs1, st_locs2, pnat, length1, length2, st1, st2. simpl.
        split. 2: split.
        intros ? ?. unfold st_locs1, pnat, length1, st1. simpl. eapply SC0; eauto.
        intros ? ?. unfold st_locs2, pnat, length2, st2. simpl. eapply SC0; eauto.
        intros. unfold strel in H32. simpl in H32. contradiction.
      - unfold st_locs1, pnat, length1, st1. simpl.
        eapply SC0; eauto.
      - eapply SC0; eauto.
      - eauto. 
      - intros. unfold strel. simpl. intuition.
        
    }

    
    destruct (IHW2 M' H14 H1' H15 H2' v1 v2'0 VT H17 H18 WFE1 SF' S1' S2') as [S1'' [S2'' [M'' [vx1 [vx2 IEX]]]]]; auto.

    intros. destruct (H26 H2'' S2'0 M'0 (pand (st_locs2 MW) P1)) as [v2x [MX [S2X [? [? [? ?]]]]]]; eauto.
    eapply sst_trans'. eapply SC0; eauto. unfoldq; intuition. eapply sstchain_tighten; eauto. unfoldq; intuition.
    exists v2x, MX, S2X; intuition.
    eapply storet_empty; eauto. eapply ST'; eauto. eapply H38; eauto.
    eapply valt_store_change. 2: eapply H40. eapply storet_empty; eauto.
    eapply H25; eauto. eapply H38; eauto.
    rewrite H17. eapply valq_val_empty in H44. rewrite H44. repeat rewrite lls_empty; eauto. eapply stchain_empty'; eauto.

    eapply bi_tapp_subst; eauto. 
    
  - (* tabs *)  

    subst env.
    assert (closed_ty (length ((T1, fr1, qand p (qor q1 (qif fn1 qf))) :: G') + S (length G)) T2). 
    eapply closedty_extend; eauto. simpl. repeat rewrite app_length. simpl. intuition.
    
    assert (closed_ql (length ((T1, fr1, qand p (qor q1 (qif fn1 qf))) :: G') + S (length G))
        (qor (qand p qf) (qone (length (G' ++ (T0, fr0, q0) :: G))))). 
    eapply closedq_or; eauto. repeat rewrite app_length. simpl. split. eapply closedq_and. left. eapply closedq_extend; eauto.
    eapply closedq_one; eauto.    
        
    assert (closed_ql (length ((T1, fr1, qand p (qor q1 (qif fn1 qf))) :: G') + S (length G))
         (qor q2 (qor (qif ar2 (qone (length (G' ++ (T0, fr0, q0) :: G)))) (qif fn2 (qand p qf))))). 
    eapply closedq_or; eauto. split. eapply closedq_extend; eauto. repeat rewrite app_length. simpl. intuition.
    eapply closedq_or; eauto. split. destruct ar2; eapply closedq_extend; eauto; intuition. eapply closedq_one; eauto. repeat rewrite app_length. simpl. intuition.
    destruct fn2; eapply closedq_extend; eauto; intuition. eapply closedq_and; eauto. left. eapply closedq_extend; eauto. repeat rewrite app_length. simpl. intuition.
         
    assert(closed_ql (length ((T1, fr1, qand p (qor q1 (qif fn1 qf))) :: G') + S (length G)) 
            (qor e2 (qor (qif e2x (qone (length (G' ++ (T0, fr0, q0) :: G)))) (qif e2f (qand p qf))))).
    eapply closedq_or; eauto. split. eapply closedq_extend; eauto. repeat rewrite app_length. simpl. intuition.
    eapply closedq_or; eauto. split. destruct e2x; eapply closedq_extend; eauto; intuition. eapply closedq_one; eauto. repeat rewrite app_length. simpl. intuition.
    destruct e2f; eapply closedq_extend; eauto; intuition. eapply closedq_and; eauto. left. eapply closedq_extend; eauto. repeat rewrite app_length. simpl. intuition.


    specialize (IHW ((T1, fr1, (qand p (qor q1 (qif fn1 qf))))::G') G). intuition.      
    specialize (H33 t1 p1 q3); intuition.
    rename H33 into IHW.
    
    eapply bi_tabs_subst; eauto. 
    
  - (* tseq *) 
    subst env. 
    eapply has_type_closed_subst in W1 as Hcl1. 2: { eapply envt_subst_tighten; eauto. }
    eapply has_type_closed_subst in W2 as Hcl2. 2: { eapply envt_subst_tighten. eapply H17. eauto. }
    rewrite app_length in Hcl1, Hcl2. simpl in Hcl1, Hcl2.
    intuition.
    (* 1st IH *)
    assert (closed_ql (length G) qempty). unfold closed_ql. unfoldq; intuition.

    assert (psub (pand (pand (pdom (G'++G))(plift p1))(plift qempty)) pempty).
    rewrite plift_empty. intros ? ?. unfoldq; intuition. 

    assert (psub (pand (pand (pdom (G'++G))(plift p2))(plift qempty)) pempty).
    rewrite plift_empty. intros ? ?. unfoldq; intuition. 

    specialize(IHW1 G' G); intuition.
    rename H35 into IHW1.
    specialize(IHW1 t0 p0 q3); intuition. 
    rename H36 into IHW1.

    assert(env_type_subst2 MW (H1' ++ v1 :: H12) (H2' ++ H13) (G' ++ (T0, fr0, q0) :: G) p1 (length G) v2'0 q3) as WFE1.
    eapply envt_subst_tighten; eauto. 

    destruct (IHW1 MW H12 H1' H13 H2' v1 v2'0  H14 H15 H16 WFE1 H18 S1 S2) as [S1'' [S2'' [M'' [v1'' [v2'' IE1]]]]]; eauto.

    
    (* 2nd IH*)
    specialize(IHW2 G' G); intuition.
    rename H35 into IHW2.

    assert (env_type_subst2 M'' (H1'++v1::H12) (H2'++H13) (G'++(T0, fr0, q0)::G) p2 (length G) v2'0  q3)  as WFE2.
    eapply envt_subst_tighten. eapply envt_subst_store_extend. 11: eauto. all: eauto. eapply IE1. 

    assert (st_chain MW M'') as SC'. apply IE1.

    assert (store_type S1'' S2'' M'') as ST'. eapply IE1.
    
    assert (val_type (st1 M'', st2 M'', fun l1 l2 => False, fun l1 l2 v1 v2 => False)  H12 H13 v1 v2'0 T0 T0) as VT.
    eapply valt_store_change. 2: eapply H14. eapply storet_empty; eauto. 1,2: eapply H23; eauto. 
    rewrite H15, H16. repeat rewrite lls_empty. eapply stchain_empty'; eauto.

    assert (st_filter M'' (st_locs1 M'')(st_locs2 M'')) as SF''. apply IE1.

    specialize(IHW2 t0 p0 q3); intuition. 
    rename H36 into IHW2.
    destruct (IHW2 M''  H12 H1' H13 H2' v1 v2'0  VT H15 H16 WFE2 SF'' S1'' S2'') as [S1'''' [S2'''' [M'''' [v3 [v4 IE2]]]]]; auto.

    intros. destruct (H24 H2'' S2' M' (pand (st_locs2 MW) P1)) as [v2x [MX [S2X [? [? [? ?]]]]]].
    eapply sst_trans'. eapply SC'. unfoldq; intuition. eapply sstchain_tighten. eapply H35. unfoldq; intuition. eauto. eauto.
    exists v2x, MX, S2X; intuition.
    eapply storet_empty; eauto. eapply ST'. eapply H39; eauto.
    eapply valt_store_change;eauto. 
    eapply valq_val_empty in H43, H45. rewrite H43, H45. repeat rewrite lls_empty.
    eapply stchain_empty'; eauto.

    subst q3.
    repeat rewrite plift_or in *. rewrite plift_empty in *.
    eapply bi_tseq_subst; eauto.

  - (* qsub *)
    subst; intuition.
    eapply has_type_closed_subst in W; eauto.
    rewrite app_length in W. simpl in W.
    specialize (IHW G' G); intuition.
    rename H28 into IHW.
    specialize (IHW t1 p1 qempty); intuition.
    rename H30 into IHW.
    specialize (IHW MW H14 H1' H15 H2' v1 v2'0); intuition.
    rename H28 into IHW.
    specialize (IHW S1 S2); intuition.
    destruct H30 as (S1' & S2' & M' & v1' & v2' & ?).
    repeat rewrite plift_subst in *. repeat rewrite plift_empty in *.
    eapply bi_qsub_subst; eauto. 
  - (* t_sub_var *)
    subst env. 
    eapply has_type_closed_subst in W as Hcl; eauto.
    rewrite app_length in Hcl. simpl in Hcl.
    assert (closed_ql (length G) qempty). { eauto. }
    specialize (IHW G' G); intuition.
    rename H29 into IHW.
    specialize (IHW t1 p1 q2); intuition.
    rename H31 into IHW.
    specialize (IHW MW H13 H1' H14 H2' v1 v2'0); intuition.
    rename H29 into IHW.
    specialize (IHW S1 S2); intuition.
    destruct H31 as (S1' & S2' & M' & v1' & v2' & ?).
    subst q2.
    repeat rewrite plift_subst in *. 
    repeat rewrite plift_or in *. 
    rewrite plift_diff, plift_one.
    repeat rewrite plift_empty in *.

    eapply bi_sub_var_subst; eauto.
    
Qed.


Lemma vars_locs_empty_head: forall v H p,
  val_locs v = pempty ->
  vars_locs (v :: H) p = vars_locs (v :: H) (por p (pone (length H))). 
Proof.
  intros. eapply functional_extensionality.
  intros. eapply propositional_extensionality.
  split; intros. destruct H1 as [? [? ?]].
  destruct H2 as [? [? ?]].
  bdestruct (x0 =? length H) . subst x0. rewrite indexr_head in H2. inversion H2. subst x1.
  rewrite H0 in H3. unfoldq; intuition.
  assert (x0 < length H). {
    apply indexr_var_some' in H2. simpl in H2. lia.
  }
  rewrite indexr_skip in H2. unfoldq; intuition.
  exists x0; intuition. unfoldq; intuition. exists x1; intuition.
  rewrite indexr_skip. auto. lia. lia.
  unfoldq; intuition. destruct H1 as [? [? ?]]. 
  destruct H1. exists x0; intuition.
  unfoldq; intuition. destruct H2 as [? [? ?]]. subst x0.
  rewrite indexr_head in H2. inversion H2. subst x1. rewrite H0 in H3. contradiction.
Qed.  


(*******************************************************************************
  
  top-level semantic substitution
  
********************************************************************************)

Lemma st_subst1 : forall t1 t2 G T1 T2 p qf fr2 q2 e2 H1 H2 v1 S1 S2 S1' S2' v2 fn2 ar2 e2x fr1 q1 fn1 e2f MW M MF MX qx
    (W: has_type ((T1, fr1, (qand p (qor q1 (qif fn1 qf))))::G) t2 T2 
          (qor  (qand p qf) (qone (length G))) 
          fr2 
          (qor q2 (qor (qif ar2 (qone (length G))) (qif fn2 (qand p qf)))) 
          (qor e2 (qor (qif e2x (qone (length G))) (qif e2f (qand p qf))))) 
    (X: has_type G t1 T1 qempty false qempty qempty)
    (WFEF: env_type (st_empty (st1 MF) (st2 M)) H1 H2 G pempty)  (* for semantic weakening *)
    (WFE: env_type MW H1 H2 G (plift p))                         (* for semantic substitution *)
    (SF: st_filter MW (st_locs1 MW) (st_locs2 MW))
    (SF1: st_filter M (st_locs1 M) (st_locs2 M))
    (Q1: qx = qempty),
    length H1 = length G ->
    length H2 = length G ->
    closed_ty (length G) T1 ->
    closed_ty (length G) T2 ->
    closed_ql (length G) q1 ->
    closed_ql (length G) q2 ->
    closed_ql (length G) e2 ->
    closed_ql (length G) qf -> 
    MW = (st1 MX, st2 M, fun l1 l2 : nat => strel M l1 l2, fun (l1 l2 : nat) (v1 v2 : vl) => st_valtype M l1 l2 v1 v2 ) ->
    sstore_type S1 (st1 MF) ->
    store_type S1' S2 MW ->
    tevaln S1 H1 t1 S1' v1 ->   
    tevaln S2 H2 t1 S2' v2 ->   
    store_effect S1 S1' pempty ->
    store_effect S2 S2' pempty ->
    store_type S1' S2' MX ->
    val_locs v1 = pempty ->
    val_locs v2 = pempty ->
    length S1 <= length S1' ->
    length S2 <= length S2' ->
    val_type (st1 MX, st2 MX, fun l1 l2: nat => False, fun (l1 l2 : nat) (v1 v2 : vl) => False ) H1 H2 v1 v2 T1 T1 ->
    (forall H2'' S2'' M2'' P,
     sst_chain_partial (st2 M)(st2 M2'') P -> 
     sstore_type S2'' (st2 M2'') ->
     exists v2 M''' S2''', 
     tevaln S2'' (H2''++H2) (splice_tm t1 (length H2) (length H2'')) S2''' v2 /\ 
     store_type S1' S2''' (st_empty (st1 MW) (st2 M''')) /\ 
     sst_chain (st2 M2'') (st2 M''') /\
     store_effect S2'' S2''' pempty /\
     val_type M''' H1 (H2''++H2) v1 v2 T1 T1 /\
     val_qual (st1 MW) (st1 M''') H1 v1 false pempty /\
     val_qual (st2 MW) (st2 M''') (H2''++H2) v2  false pempty 
     ) -> (* via st_weaken *)
    exists S1'' S2'' M'' v1'' v2'',
      exp_type S1' S2 MW
        (v1::H1) H2
        t2 (subst_tm t2 (length H2) t1 qempty)
        S1'' S2'' M'' v1'' v2'' T2  
        (plift p)
        fr2
        (por (plift q2) (por (pif ar2 (pone (length G))) (pif fn2 (pand (plift p)(plift qf)))))
        (por (plift e2) (por (pif e2x (pone (length G))) (pif e2f (pand (plift p)(plift qf))))).  
Proof.  
  intros. eapply filter_closed in WFE as CLP. 
  remember WFE as WFE'. clear HeqWFE'.
  destruct WFE as [L1 [L2 [? [? ?]]]].

  eapply st_subst with (G':=[]) (H1':=[]) (H2':=[])(H2 := H2)(H1 := H1) in W.
  12: eapply X. 21: eapply H11. 
  2: { simpl. eauto. }
  2: { auto. }
  2: { eapply closedq_and; eauto. }
  2: { simpl. eapply closedty_extend; eauto. }
  2: { simpl. eapply closedq_or. split. eapply closedq_and. left. eapply closedq_extend; eauto. eapply closedq_one; eauto. }
  2: { simpl. eapply closedq_or. split. eapply closedq_extend; eauto. 
       eapply closedq_or. split. 
       destruct ar2; simpl; unfoldq; intuition. intros ? ?. simpl in H27. unfold qone in H27. bdestruct (x =? length G); intuition. 
       destruct fn2; simpl; unfoldq; intuition. intros ? ?. simpl in H27. rewrite qand_true_iff in H27. unfoldq; intuition. }

  2: { simpl. eapply closedq_or. split. eapply closedq_extend; eauto. 
       eapply closedq_or. split. 
       destruct e2x; simpl; unfoldq; intuition. intros ? ?. simpl in H27. unfold qone in H27. bdestruct (x =? length G); intuition. 
       destruct e2f; simpl; unfoldq; intuition. intros ? ?. simpl in H27. rewrite qand_true_iff in H27. unfoldq; intuition. }
  2: { eauto. }
  2: { eauto. }
  2: { eauto. } 
  2: { eapply valt_store_change. 2: eauto. eapply storet_empty; eauto. eapply H16. eapply H16. 
       rewrite H17, H18. repeat rewrite lls_empty. eapply stchain_empty'; eauto. }
  2: { eauto. }
  2: { eauto. } 
  2: { simpl. eapply envt_to_envt_subst2. 3: eapply H21.  eapply storet_empty; eauto. eapply H16. eapply H16. 
       eauto. eauto. all: eauto. }
  2: { eauto. }
  2: { eauto. }
  2: { eauto. }
  2: { eauto. }
  2: { eauto. }
  2: { intros. 
                   
       eapply st_weaken1 with (S1F := S1)(S2 := S2)(H1 := H1)(H2:= H2)(H2' := [])(M := M) in X.
       3: { eapply H10. }
       2: { simpl. eapply envt_store_change. eauto. eapply storet_empty; eauto. rewrite H9 in H11. unfold st2 in H11. simpl in H11. eapply H11; eauto. 
            repeat rewrite vars_locs_empty. repeat rewrite lls_empty; eauto. eapply stchain_empty'; eauto. }
       2: {  rewrite H9 in H11. unfold st2 in H11. simpl in H11. eapply H11.  }
       
       destruct X as [v1' [SX [MSX [? ?]]]].
       assert (v1' = v1 /\ SX = S1').
       eapply tevaln_unique; eauto.
       destruct H31. subst v1'. subst SX.
       destruct H30 as [? [? ?]].
       destruct (H32 H2'' S2'0 M' (pand (st_locs2 MW) P1)) as [v2X [MX' [S2X [? [? [? [? ?]]]]]]]; eauto.
       eapply sstchain_tighten. unfold st2 in H26. subst MW. simpl. eapply H26.
       unfoldq; intuition.

       exists v2X, MX', S2X; intuition; simpl in *.
       eapply storet_empty; eauto. eapply H11; eauto. eapply H34; eauto.
       rewrite splicety_id in H25. eapply valt_store_change. 2: eapply H25. 
       eapply storet_empty; eauto. 
       eapply H34; eauto.
       rewrite H17. eapply valq_val_empty in H42. rewrite H42. repeat rewrite lls_empty; eauto. eapply stchain_empty'; eauto.
       rewrite H0. auto.
       intros ? ?. rewrite H17 in H40. rewrite lls_empty in H40. unfoldq; intuition.
  }

  destruct W as (SW1'' & SW2'' & M'' & v1'' & v2'' & ?).
  simpl in H26.
  destruct H26 as (TE1 & TE2 & STC' & STF' & ST' & SE1 & SE2 &  VT & VQ1 & VQ2). 
  
  repeat rewrite plift_or in *. repeat rewrite plift_and in *. repeat rewrite plift_if in *. 
  repeat rewrite plift_and in *. repeat rewrite plift_one in *. repeat rewrite plift_empty in *.

  exists SW1'', SW2'', M'', v1'', v2''.
  split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 8: split. 9: split.
  - eauto. 
  - rewrite splice_zero in TE2. eauto.
  - eauto. 
  - auto.
  - auto.
  - intros ? ? PV ?. eapply SE1; auto. intros VL. eapply PV.
    eapply lls_mono; eauto. repeat rewrite pand_or_distribute. repeat rewrite vars_or. 
    intros ? [ ? | [? | ?]].
    left. destruct H27 as [? [? ?]]. exists x0; intuition. unfoldq; intuition. eapply H7 in H32. lia.
    destruct H27 as [? [[? ?] ?]]. destruct H27 as [[? ?] | ?]; destruct e2x; simpl in H28; try contradiction; unfold pone in H28. eapply H8 in H30. lia.
    subst x0. rewrite <- H in H29.  unfoldq. destruct H29 as [? [? ?]]. rewrite indexr_head in H28. inversion H28. subst x0. rewrite H17 in H29. contradiction.
    destruct H27 as [? [[? ?] ?]]. right. right. exists x0; intuition. split; auto. 
    destruct H27. unfoldq; intuition. 
    unfold pone in H27. destruct e2f; simpl in H28; try contradiction. destruct H28. eapply H8 in H31. lia.
    
  - rewrite L2 in SE2. repeat rewrite substp_or in SE2. rewrite substp_hit in  SE2.
    rewrite <- plift_and in SE2. rewrite substp_id in SE2. rewrite substp_id in SE2.     
    eapply se_sub; eauto.
    rewrite plift_and. eapply lls_mono; eauto. eapply vars_locs_mono; eauto. 
    intros ? [? ?]. destruct H26 as [[? ?]| ?]; destruct H27 as [? | [? | ?]].
    split; auto. left. auto.
    split; auto. destruct e2x; simpl in H27; try contradiction. rewrite pif_true in H27. rewrite substp_hit in H27. unfoldq; intuition.
    rewrite pif_false in H27. rewrite substp_empty in H27. unfoldq; intuition.
    destruct e2f. rewrite pif_true in H27. rewrite <- plift_and, substp_id in H27. 
    split; auto. right. right. simpl. unfoldq; intuition.
    eapply closedq_and; eauto. 
    rewrite pif_false, substp_empty in H27. unfoldq; intuition. unfoldq; intuition. unfoldq; intuition.
    unfoldq; intuition. auto. eapply closedq_and; eauto. 

  - rewrite substy_id in VT. auto. rewrite L2. auto.
  - subst MW. unfold val_qual. intros ? ?. rewrite vars_locs_empty_head; auto.
    destruct (VQ1 x). auto. 
    left. eapply lls_mono; eauto. eapply vars_locs_mono; eauto. 
    destruct ar2; destruct fn2; simpl in *; unfoldq; intuition.
    right. auto.

  - repeat rewrite substp_or in VQ2. rewrite <- plift_and in VQ2. rewrite substp_id in VQ2.
    rewrite <- H0 in VQ2. rewrite substp_hit in VQ2. rewrite substp_id in VQ2.
    rewrite plift_and in VQ2. repeat rewrite pand_or_distribute in VQ2. 
    repeat rewrite pand_or_distribute. 
    intros ? ?. destruct (VQ2 x); auto; repeat rewrite lls_vars_or in H27; repeat rewrite lls_vars_or.
    destruct H27 as [? | [? | ?]].
    left. left. eapply lls_mono; eauto. eapply vars_locs_mono; eauto. unfoldq; intuition.
    destruct ar2. rewrite pif_true in *. rewrite substp_hit in H27. rewrite pand_empty_r, vars_locs_empty, lls_empty in H27. unfoldq. intuition.
    rewrite pif_false, substp_empty in H27. rewrite pand_empty_r, vars_locs_empty, lls_empty in H27. unfoldq. intuition.
    destruct fn2. rewrite pif_true in *. rewrite <- plift_and, substp_id in H27. rewrite plift_and in H27. 
    left. right. right. eapply lls_mono; eauto. eapply vars_locs_mono; eauto. unfoldq; intuition.
    eapply closedq_and; auto.
    rewrite pif_false, substp_empty in H27. rewrite pand_empty_r, vars_locs_empty, lls_empty in H27. unfoldq. intuition.
    right. auto. rewrite L2. auto. eapply closedq_and; auto.
Qed.

(*******************************************************************************
  
  beta rule
  
********************************************************************************)

Theorem beta_equivalence: forall t1 t2 G T1 q1 fr1 fn1 T2 p qf ar2 fn2 q2 e2x e2f e2 fr2
  (F: has_type ((T1, fr1, (qand p (qor q1 (qif fn1 qf))))::G) t2 T2 
        (qor (qand p qf) (qone (length G))) 
        fr2
        (qor q2 (qor (qif ar2 (qone (length G))) (qif fn2 (qand p qf))))
        (qor e2 (qor (qif e2x (qone (length G))) (qif e2f (qand p qf)))))
  (X: has_type G t1 T1 qempty false qempty qempty)    (* t1's observation is the empty set, does not have effects, and its reduction result reaches the empty set of locations *)
  (QSUB0: psub (plift q1) (pand (plift p) (plift qf)))
  (CLT2: closed_ty (length G) T1)
  (CLT2: closed_ty (length G) T2)
  (CLQ1: closed_ql (length G) q1) 
  (CLQ2: closed_ql (length G) q2) 
  (CLQF: closed_ql (length G) qf)
  (CLQE: closed_ql (length G) e2),
  sem_type G (tapp (tabs (qand p qf) t2) t1) (subst_tm t2 (length G) t1 qempty)  T2 (plift p) 
    fr2
    (por (pif fn2 (plift qf)) (plift q2))
    (por (plift e2) (pif e2f (plift qf))).
Proof.
  intros. 
  intros M H1 H2 WFE SF. intros S1 S2 ST.
  apply wf_env_type in WFE as WFE'.
  destruct WFE' as [L1 [L2 [PD1 [PD2 [PD3 PD4]]]]].

  assert (has_type G (tabs (qand p qf) t2) (TFun T1 fn1 fr1 q1 T2 fn2 ar2  fr2 q2 e2f e2x e2) p false qf qempty) as TF.
  econstructor; eauto. 

  eapply fundamental_property in TF as TF'; eauto.
  destruct (TF' M H1 H2 WFE SF S1 S2 ST) as  [FS1 [FS2 [MF [vf [vf' [IEF1 [IEF2 [SCF [SFF [STF [FEFF1 [FEFF2 [VTF [VQF1 VQF2]]]]]]]]]]]]]].

 
  assert (length S1 = length1 M) as LA. destruct ST as [[? ?] ?]. eauto.
  assert (length FS1 = length1 MF) as LB. destruct STF as [[? ?] ?]. eauto.
  assert (length S1 <= length FS1) as LC. eapply st_mono1 in SCF. lia.
  rewrite plift_empty in *. rewrite pand_empty_r in *. rewrite vars_locs_empty in *. 
  rewrite lls_empty in *.
  
  (* to get the first program's argument's value for weakending *)
  eapply st_weaken1 with (H2':=[])(S1F := FS1)(H1 := H1)(H2 := H2)(S2 := S2)(M := M) in X as A. 
  2: { simpl. eapply envt_store_change.  eapply envt_tighten. eapply WFE. unfoldq; intuition. eauto. repeat rewrite vars_locs_empty. repeat rewrite lls_empty; eauto. eapply stchain_empty'; eauto.    }
  2: { eapply STF; eauto. }
  2: { eapply ST; eauto. }
    
  destruct A as [v1 [S1' [M1' [IE1 [SST1A [STC1A A]]]]]].  
    
  assert (env_type MF H1 H2 G (plift qempty)) as WFEF. { eapply envt_tighten.  eapply envt_store_extend; eauto. unfoldq; intuition. }
  
  eapply store_invariance with (S1 := FS1)(S2 := S2) in X as X' . 
  3: { eapply storet_empty. eapply STF. eapply ST.   }
  2: { eapply envt_tighten. eapply envt_store_change. eapply WFEF. eauto. 
       rewrite plift_empty in *. repeat rewrite vars_locs_empty. repeat rewrite lls_empty.
       eapply stchain_empty'; eauto. unfoldq; intuition.  }
  
  destruct X' as [S1X [S2X [MX [v1'0 [v2'0 ?]]]]].
  destruct H as [IEX1' [IEX2' [SCX [STFX [STX [EFFX1 [EFFX2 [VTX [VQX1 VQX2]]]]]]]]].
  assert (v1'0 = v1 /\ S1X = S1').
  eapply tevaln_unique; eauto.
  destruct H. subst v1'0. subst S1X.
  
  assert (st_filter M (locs_locs_stty (st1 M) (vars_locs H1 (plift p))) (locs_locs_stty (st2 M) (vars_locs H2 (plift p)))) as SFV. {
    eapply envt_filter_deep; eauto. unfoldq; intuition.
  }

  eapply envt_store_deep_wf with (q := (plift p)) in WFE as WFE'.
  2: { intros ? ?.  auto. }
  destruct WFE' as [W1 W2].

  rewrite plift_empty in *. rewrite pand_empty_r in *. rewrite vars_locs_empty in *. rewrite lls_empty in *.
  assert (store_effect S2 S2X pempty) as EFFX2'. {
    intros ? ? ? ?. erewrite EFFX2; eauto. 
  }

  assert (length S2 = length2 M) as LS2. destruct ST as [? [[? ?] ?]]; intuition.
  assert (length1 M <= length1 MF) as LM1. eapply st_mono1 in SCF; auto.
  assert (length2 M <= length2 MF) as LM2. eapply st_mono2 in SCF; auto.
  assert (length FS2 = length2 MF) as LS4. destruct STF as [? [[? ?]?]]; intuition.
   
  assert (length1 MF <= length1 MX) as LM3. eapply st_mono1 in SCX; auto.
  assert (length2 M <= length2 MX) as LM4. { eapply st_mono2 in SCX; eauto. } 
  assert (length S1' = length1 MX) as LS5. destruct STX as [[? ?] [? ?]]; auto. 
  assert (length S2X = length2 MX) as LS6. destruct STX as [[? ?] [[? ?] ?]]; auto. 
    
  assert (val_locs v1 = pempty) as VXE. { eapply valq_val_empty; eauto. }
  assert (val_locs v2'0 = pempty) as VX'E. { eapply valq_val_empty; eauto. }
              
  remember ST as ST'. clear HeqST'.
  destruct ST as [SST1 [SST2 [ST [U2 U1]]]].
     
  assert (val_type (st_empty (st1 MF) (st2 M)) H1 H2 v1 v2'0 T1 T1) as VTXX. {
    eapply valt_store_change. 2: eapply VTX; eauto. eauto.
    rewrite VXE, VX'E.
    repeat rewrite vars_locs_empty. repeat rewrite lls_empty. eapply stchain_empty'; eauto.
  }

  
  remember ((st1 MX), (st2 M), 
    fun l1 l2 : nat => 
      strel M l1 l2 ,
    fun (l1 l2 : nat) (v1 v2 : vl) =>  
      st_valtype M l1 l2 v1 v2 
  ) as M1.

  assert (length1 M <= length1 M1) as LS9. {
    subst M1. unfold length1, st1 in *. simpl.  lia.
  }
  assert (length2 M <= length2 M1) as LS10. {
    subst M1. unfold length2, st2 in *. simpl. lia. 
  }  
  

  assert (sst_chain_partial (fst (fst (fst M))) (fst (fst (fst MX))) (locs_locs_stty (fst (fst (fst M))) (vars_locs H1 (plift p)))) as SSTCMMX1. {
    eapply sst_trans'. eapply SCF; eauto. auto. eapply sstchain_tighten. eapply SCX; eauto.
    intros ? ?. eapply W1 in H.  unfold st_locs1, pnat, length1, st1 in *. simpl in *. lia.
  }

  assert (st_chain_partial M M1 (st_locs1 M) (st_locs2 M)) as SCM1. {
     subst M1. split. 2: split. 3: split. 4: split. 5: split.
     + eauto.
     + repeat split.
       - unfold st_locs1. intros ? ?. unfold pnat in *. lia.
       - unfold st_locs2. intros ? ?. unfold pnat in *. lia.
       - unfold strel, st1 in H. simpl in H. intros. eapply strel_wf in H; eauto. unfold st_locs2. intuition.
       - unfold strel in H. simpl in H. eapply strel_wf in H; eauto. unfold st_locs2. intuition.
     + unfold st1. simpl.  eapply sst_trans. eapply SCF; eauto. eapply SCX; eauto.
     + unfold st2. simpl.  assert (st_chain M M). eapply st_refl. auto. eapply H; eauto.
     + intros. simpl. auto. 
     + intros. unfold strel. simpl. intuition.
  }

  assert (st_chain_partial M M1 (locs_locs_stty (st1 M) (vars_locs H1 (plift p))) (locs_locs_stty (st2 M) (vars_locs H2 (plift p)))) as SCP. {
    eapply stchain_tighten. eauto. eapply SCM1. auto. auto.
  }

  assert (store_type S1' S2 M1) as ST1. {
    subst M1. split. 2: split. 3: split. 4: split.
    + unfold st1. simpl. eapply STX; eauto.
    + unfold st2. simpl. eauto.
    + unfold strel, st1, st2. simpl. intros ? ? ?.
      destruct (ST l1 l2) as [vt [qt1 [qt2 [v1x [v2x [IM1 [IM2 [IS1 [IS2 [SVT [VT SFT]]]]]]]]]]]. auto.
      exists vt, qt1, qt2, v1x, v2x; intuition.
      - destruct SCX as [? [? [Y ?]]]. destruct Y as [Y1 [Y2 Y]]. rewrite <- Y; eauto.
        unfold st1. simpl. destruct SCF as [? [? [Z ?]]]. destruct Z as [Z1 [Z2 Z]]. rewrite <- Z; eauto.
        eapply strel_wf in H; eauto. unfold st_locs1; intuition.
        unfold st_locs1, pnat, length1, st1. simpl. eapply strel_wf in H; eauto. unfold length1, st1 in *. destruct H. lia.
      - repeat split. 
        -- unfold st_locs1, pnat, length1, st1. simpl. assert (indexr l1 S1' = Some v1x). { erewrite EFFX1; eauto. }
           eapply val_reach_wf_store; eauto. eapply STX; eauto.
        -- unfold st_locs2, pnat, length2, st2. simpl. eapply SFT; eauto.
        -- unfold strel in H0. simpl in H0. intros ?. erewrite <- lls_change with (M := (st1 M)) in H3. eapply SFT; eauto. 
           eapply sstchain_tighten. eapply SCM1; eauto. eapply SFT; eauto. 
        -- unfold strel in H0. simpl in H0. intros ?. erewrite <- lls_change. eapply SFT; eauto.
           eapply sstchain_tighten. eapply SCM1; eauto. eapply SFT; eauto.
    + unfold strel. simpl. intros. eapply U2; intuition. eauto. eauto.
    + unfold strel. simpl. intros. eapply U1; intuition. eauto. eauto.
  }
                    
  assert (env_type M1 H1 H2 G (plift p)) as WFEM1. {
    eapply envt_store_change. eapply WFE. eauto. eauto.
  }

  assert (st_filter M1 (st_locs1 M1)(st_locs2 M1)) as SFM1. {
    repeat split.
    intros ? ?. auto.
    intros ? ?. auto.
    subst M1. unfold st_locs1, st_locs2, pnat, length1, length2, st1, st2. simpl.
    unfold strel, st1 in H. simpl in H.  intuition.  
    eapply strel_wf in H; eauto. destruct H. unfold length2, st2 in *. lia.
    intros ?. subst M1. unfold st_locs1, st_locs2, pnat, length1, length2, st1, st2. simpl.
    unfold strel, st1 in H. simpl in H. intuition. 
    eapply strel_wf in H; eauto. unfold length1, st1 in *. intuition. 
  }

 
  (*---------------- substitution --------------*)

  assert (exists S1'' S2'' M'' v1'' v2'',
    exp_type S1' S2 M1 (v1::H1) H2 
        t2 (subst_tm t2 (length H2) t1 qempty)
        S1'' S2'' M'' v1'' v2'' T2   
        (plift p) fr2 
        (por (plift q2) (por (pif ar2 (pone (length G))) (pif fn2 (pand (plift p)(plift qf)))))
        (por (plift e2) (por (pif e2x (pone (length G))) (pif e2f (pand (plift p)(plift qf)))))) as SUBST. {
    eapply st_subst1. eapply F. eapply X. 14: eauto. 14: eapply STF; eauto. 
    eapply envt_store_change. eapply WFEF. eauto.
    repeat rewrite vars_locs_empty. repeat rewrite lls_empty. eapply stchain_empty'; eauto. eauto. eauto.
    1-18: eauto. lia. lia.
    eapply valt_store_change. 2: eauto. eapply storet_empty; eauto. eapply STF; eauto.
    rewrite VXE, VX'E. repeat rewrite lls_empty. eapply stchain_empty'; eauto.
    assert (sst_chain_partial (st2 M)(st2 M) (st_locs2 M)) as C. eapply st_refl; eauto.
    assert (sstore_type S2 (st2 M)) as  D. eauto.
    assert (store_effect FS2 FS2 pempty) as E. { intros ? ? ? ?. auto. }
    intros.  specialize (A H2'' S2'' M2'' P H H0 ). rewrite splicety_id in A. intuition. simpl in A. 
    destruct A as [v2A [M'A [S2'A ?]]].
    exists v2A, M'A, S2'A; intuition.
    eapply storet_empty; eauto. eapply ST1; eauto. eapply H3; eauto.
        
    eapply valt_store_change. 2: eapply H7. eapply storet_empty; eauto. eapply H3; eauto.
    eapply valq_val_empty in H8, H10. rewrite H8, H10. repeat rewrite lls_empty. eapply stchain_empty'; eauto.
    intros ? ?. rewrite VXE in H9. rewrite lls_empty in H9. unfoldq; intuition.
    rewrite L2. auto.
  }

  destruct SUBST as [S1'' [S2'' [M'' [v1'' [v2'' [YE1 [YE2 [YSC [YSF [YST [YEFF1 [YEFF2 [VY [QY1 QY2]]]]]]]]]]]]]].

  assert (length1 M <= length1 M1) as LA1. { subst M1. unfold length1, st1 in *. simpl in *. lia. }
  assert (length2 M <= length2 M1) as LB1. { subst M1. unfold length2, st2 in *. simpl in *. lia. }
  assert (length1 M1 <= length1 M'') as LC1. eapply st_mono1 in YSC. lia.
  assert (length2 M1 <= length2 M'') as LD. eapply st_mono2 in YSC. lia.
  assert (length S1' = length1 M1 ) as LE. { subst M1. unfold length1. simpl. auto. }
  assert (length S1'' = length1 M'') as LF. destruct YST as [[? ?] ?]; intuition.
  assert (length S2'' = length2 M'') as LG. destruct YST as [? [[? ?] ?]]; intuition.
  assert (length1 M <= length1 MX) as LMX. { eapply st_mono1 in SCX; eauto. unfold length1, st1 in SCX. simpl in SCX. lia.  }


  remember ((st1 M''), (st2 M''), 
    fun l1 l2 : nat =>
    strel M l1 l2 /\
      ~ (locs_locs_stty (st1 M) (vars_locs H1 (plift p))) l1 /\
      ~ (locs_locs_stty (st2 M) (vars_locs H2 (plift p))) l2 \/
      strel M1 l1 l2 /\
      ((locs_locs_stty (st1 M) (vars_locs H1 (plift p))) l1 /\
      (locs_locs_stty (st2 M) (vars_locs H2 (plift p))) l2 \/
      ~ l1 < length1 M /\ l1 < length1 M1 /\ 
      (psub(pand (por (pdiff (pnat (length1 M1)) (pnat (length1 M))) (pnot (locs_locs_stty (st1 M) (vars_locs H1 (plift p)))))(locs_locs_stty (st1 M) (pone l1)))) pempty /\
      ~ l2 < length2 M /\ l2 < length2 M1 ) \/
      strel M'' l1 l2 /\ ~l1 < length1 M1 /\ l1 < length1 M'' /\ ~l2 < length2 M1 /\ l2 < length2 M'' 
      ,  
    fun (l1 l2 : nat) (v1 v2 : vl) =>
    st_valtype M l1 l2 v1 v2 /\ l1 < length1 M /\ l2 < length2 M /\
    ~ (locs_locs_stty (st1 M) (vars_locs H1 (plift p))) l1 /\
    ~ (locs_locs_stty (st2 M) (vars_locs H2 (plift p))) l2 \/
    st_valtype M1 l1 l2 v1 v2 /\
      ((locs_locs_stty (st1 M) (vars_locs H1 (plift p))) l1 /\
      (locs_locs_stty (st2 M) (vars_locs H2 (plift p))) l2 \/
      ~ l1 < length1 M /\ l1 < length1 M1 /\ 
      (psub(pand (por (pdiff (pnat (length1 M1)) (pnat (length1 M))) (pnot (locs_locs_stty (st1 M) (vars_locs H1 (plift p)))))(locs_locs_stty (st1 M) (pone l1)))) pempty /\
      ~ l2 < length2 M /\ l2 < length2 M1) \/
     st_valtype M'' l1 l2 v1 v2 /\ ~l1 < length1 M1 /\ l1 < length1 M'' /\ ~l2 < length2 M1 /\ l2 < length2 M''  
    ) as MR.  
  
  assert (st_filter MR (st_locs1 MR)(st_locs2 MR)) as SFR'. { 
    subst MR. simpl. split. 2: split. 
    + intros ? ?. auto.
    + intros ? ?. auto.
    + intros. unfold strel in H. simpl in H. unfold st_locs1, st_locs2, st1, st2, pnat, length1, length2, st1, st2. simpl. 
      destruct H as [HA | [HB | HC ]].
      - destruct HA as [HA HA']. eapply strel_wf in HA; eauto. unfold length1, length2, st1, st2 in *. destruct HA. split; intros; lia.
      - destruct HB as [HB [HB1 | HB2]]. destruct HB1. eapply envt_store_deep_wf in H0, H; eauto.
        2,3: unfoldq; intuition.
        unfold pnat, length1, length2, st1, st2 in *. split; intros; lia.
        destruct HB2 as [? [? [? [? ?]]]]. unfold length1, length2, st1, st2 in *.
        split; intros; lia.
      - destruct HC as [? [? [? [? ?]]]]. split; intros. unfold length1, length2, st1, st2 in *. lia. unfold length1, length2, st1, st2 in *. lia.
  }

  
  assert (sst_chain_partial (fst (fst (fst M))) (fst (fst (fst M''))) (st_locs1 M)) as SSTA. {
    unfold st1, st_locs1, pnat, length1, st1 in *. 
    repeat split. 
    unfoldq; intuition.
    unfoldq; intuition. 
    intros. destruct YSC as [? [? [Y ?]]]. destruct Y as [Y1 [Y2 Y3]]. erewrite <- Y3.
    subst M1. unfold st1. simpl. 
    assert (indexr l (st1 MF)  = indexr l (st1 MX)). {  eapply SCX; eauto.  unfold st_locs1, pnat, length1, st1. simpl. lia. }
    assert (indexr l (st1 M)  = indexr l (st1 MF)). { eapply SCF; eauto.  }
    unfold st1 in *. congruence.
    unfold st_locs1, pnat, length1, st1 in *. lia.
  }

  assert (sst_chain_partial (snd (fst (fst M))) (snd (fst (fst M''))) (st_locs2 M)) as SSTB. {
    unfold st2, st_locs2, pnat, length2, st2 in *. 
    repeat split. 
    unfoldq; intuition.
    unfoldq; intuition. 
    intros. destruct YSC as [? [? [? [Y ?]]]]. destruct Y as [Y1 [Y2 Y3]]. erewrite <- Y3.
    rewrite HeqM1. unfold st2. simpl. auto. 
    unfold st_locs2. auto. unfold st_locs2, pnat, length2, st2 in *. lia.
  }
 
  assert (st_chain M MR) as SCR. {     
    subst MR. unfold st_chain. unfold st_chain_partial. split. 2: split. 3: split. 4: split. 5: split.
    - auto.
    - repeat split.
      * unfold st_locs1, pnat, length1, st1 in *. intros ? ?. simpl in *. lia.
      * unfold st_locs2, pnat, length2, st2 in *. intros ? ?. simpl in *. lia.
      * intros Y. unfold strel in H. simpl in H.
        destruct H as [HA | [HB | HC]].
        ** destruct HA as [HA HA']. eapply SF; eauto.
        ** destruct HB as [HB [HB1 | HB2]]. destruct HB1. unfold st_locs2; auto. 
           destruct HB2 as [? [? [? [? ? ]]]]. unfold st_locs1, pnat, length1, st1 in *. contradiction.
        ** destruct HC as [? [? [? [? ?]]]]. unfold st_locs1, pnat in Y. intuition. 
      * intros Y. unfold strel in H. simpl in H.
        destruct H as [HA | [HB | HC]]. 
        ** destruct HA as [HA HA']. eapply SF; eauto.
        ** destruct HB as [HB [HB1 | HB2]]. destruct HB1. unfold st_locs1. auto.
           destruct HB2 as [? [? [? [? ?]]]]. unfold st_locs2, pnat, length2, st2 in *. contradiction.
        ** destruct HC as [? [? [? [? ?]]]]. unfold st_locs2, pnat in Y. assert False. eapply H4. lia. contradiction.
    - (* sst_chain_partial 1 *)
      unfold st1, st_locs1, pnat, length1, st1. simpl in *. eapply SSTA.
    - (* sst_chain_partial 2 *)
      unfold st2, st_locs2, pnat, length1, st2. simpl in *. eapply SSTB; eauto.
    - (* st_valtype *)    
      intros. simpl. eapply functional_extensionality. intros. eapply functional_extensionality. intros.
      eapply propositional_extensionality. 
      split; intros. 
      * assert (locs_locs_stty (st1 M) (vars_locs H1 (plift p)) l1 \/ ~ locs_locs_stty (st1 M) (vars_locs H1 (plift p)) l1). { rewrite plift_vars_locs.  eapply val_locs_stty_decide. eauto.  }
        destruct H5. right. left. repeat split; auto. destruct SCP as [? [? [? [? [STY' ?]]]]]. erewrite <- STY'. auto. auto. eapply envt_same_locs; eauto. unfoldq; intuition. auto.
        left. split. auto. eapply envt_same_locs; eauto. unfoldq; intuition. 
        left. repeat split; auto. intros ?. eapply H5. eapply envt_same_locs; eauto. unfoldq; intuition. 
      * destruct H4 as [HA | [HB | HC]]; intuition.
        destruct SCP as [? [? [? [? [STY' ?]]]]]. erewrite STY'; eauto. unfold st_locs1, pnat, length1, st1 in *. lia.
    - (* strel *)
      intros. unfold strel. simpl. 
      assert (locs_locs_stty (st1 M) (vars_locs H1 (plift p)) l1 \/ ~ locs_locs_stty (st1 M) (vars_locs H1 (plift p)) l1). { rewrite plift_vars_locs.  eapply val_locs_stty_decide. eauto.  }
      split; intros.
      * destruct H. destruct H0.
        right. repeat split; auto. left. repeat split. eapply SCP; eauto. split; auto. eapply envt_same_locs; eauto. unfoldq; intuition.
        left. repeat split; auto. eapply envt_same_locs; eauto. unfoldq; intuition. 
        left. repeat split; auto. intros ?. eapply H0. eapply envt_same_locs; eauto. unfoldq; intuition.
      * destruct H. destruct H0; destruct H3 as [H5A | [H5B | H5C]].
        ** intuition.
        ** destruct H5B. destruct H5 as [? | ?].
           eapply SCP; eauto. intuition.
        ** destruct H5C as [? [? [? [? ?]]]]. unfold st_locs1, pnat, length1 in *. lia.
        ** intuition.
        ** destruct H5B. destruct H5 as [? | ?].
           intuition. intuition.
        ** intuition. unfold st_locs1, pnat, length1 in *. lia.
  }

  assert (env_type M'' H1 H2 G (plift p)) as WFE''. {
    eapply envt_store_change. eapply WFEM1. eauto.
    eapply stchain_tighten. 2: eapply YSC; eauto. eapply envt_filter_deep; eauto. unfoldq; intuition.
    eapply envt_store_deep_wf; eauto. unfoldq; intuition.
    eapply envt_store_deep_wf; eauto. unfoldq; intuition.
  }
  

  assert (env_type MR H1 H2 G (plift p)) as WFER. {
    eapply envt_store_change. eapply WFE. eauto.
    eapply stchain_tighten; eauto.
  }
 
  
  assert (st_chain_partial M1 M'' (locs_locs_stty (st1 M) (vars_locs H1 (plift p))) (locs_locs_stty (st2 M) (vars_locs H2 (plift p)))) as SCPR. { 
    eapply st_trans'; eauto. 
    + intros ? ?. eapply W1 in H. unfold st_locs1, pnat, length1 in *. lia.
    + intros ? ?. eapply W2 in H. unfold st_locs2, pnat, length1 in *. lia.
    + assert (st_chain M'' M''). { eapply st_refl. eauto.  }
      eapply stchain_tighten. 2: eapply H.
      rewrite lls_change with (M' := (st1 M'')). rewrite lls_change with (M := st2 M) (M' := (st2 M'')).
      eapply envt_filter_deep; eauto. unfoldq; intuition.
      eapply sstchain_tighten; eauto. eapply sstchain_tighten; eauto.
      intros ? ?. eapply W1 in H0. unfold st_locs1, pnat, length1 in *. lia.
      intros ? ?. eapply W2 in H0. unfold st_locs2, pnat, length1 in *. lia.
  }
  
  assert (sst_chain_partial (st1 MR) (st1 M'') (locs_locs_stty (st1 MR) (vars_locs H1 (plift p)))) as SSTMRM''1. {
    subst MR. repeat split.
    - unfold st1. simpl. eapply envt_store_deep_wf; eauto. unfoldq; intuition.
    - unfold st2. simpl. eapply envt_store_deep_wf; eauto. unfoldq; intuition.
  }

  assert (sst_chain_partial (st2 MR) (st2 M'') (locs_locs_stty (st2 MR) (vars_locs H2 (plift p)))) as SSTMRM''2. {
    subst MR. repeat split.
    - unfold st2. simpl. eapply envt_store_deep_wf; eauto. unfoldq; intuition.
    - unfold st2. simpl. eapply envt_store_deep_wf; eauto. unfoldq; intuition.
  }  

  assert (st_chain_partial M M'' (locs_locs_stty (st1 M) (vars_locs H1 (plift p))) (locs_locs_stty (st2 M) (vars_locs H2 (plift p)))) as SCPMM''. {
    eapply st_trans''; eauto.  
  }
  
  assert (store_effect S1 S1'' (locs_locs_stty (st1 M1) 
    (vars_locs (v1 :: H1)(pand (plift p) (por (plift e2) (por (pif e2x (pone (length G))) (pif e2f (pand (plift p) (plift qf))))))))) as SE11. {
    eapply se_trans.
    eapply se_sub; eauto. intros ? ?. unfoldq; intuition. 
    { intros ? ? ? ?. rewrite YEFF1; eauto. }
  }

 assert (store_effect S2 S2'' (locs_locs_stty (st2 M1)(vars_locs H2 (pand (plift p) (por (plift e2) (por (pif e2x (pone (length G))) (pif e2f (pand (plift p) (plift qf))))))))) as SE22. {
    eapply se_trans.
    eapply se_sub; eauto. intros ? ?. unfoldq; intuition.
    { intros ? ? ? ?. auto. }
 }
 
 assert (store_type S1'' S2'' MR) as STR. { 
    subst MR. remember YST as YST'. clear HeqYST'. 
    destruct YST' as (SSTY1 & SSTY2 & STRELY & STYR & STYL). split. 2: split. 3: split. 4: split. 
    - intuition.
    - intuition.
    - intros. unfold strel in H. simpl in H. destruct H as [NP | [[P [PM | PM'']] | PM'']].
      + destruct NP as [NP1 [NP2 NP3]].
        destruct (ST l1 l2) as (vtx & qt1x & qt2x & v1'x & v2'x & ? & ? & ? & ? & ? & ? & ?). eauto.
        destruct SCR as [SCR1 [SCR2 [SCR3 [SCR4 [SCR5 SCR6]]]]].
        exists vtx, qt1x, qt2x, v1'x, v2'x. split. 2: split. 3: split. 4: split. 5: split. 6: split.
        * unfold st1. simpl. destruct SCR3 as [Y1 [Y2 Y3]]. rewrite <- Y3. auto. apply indexr_var_some' in H. unfold st_locs1. auto.
        * unfold st2. simpl. destruct SCR4 as [Y1 [Y2 Y3]]. rewrite <- Y3. auto. apply indexr_var_some' in H0. unfold st_locs2. auto.
        * erewrite SE11; eauto. intros ?. eapply NP2.
          replace (v1:: H1) with ([v1]++H1) in H8. rewrite vars_locs_extend in H8.
          erewrite lls_change.  eapply lls_mono. 2: eapply H8. eapply vars_locs_mono; eauto. 
          destruct e2x; unfoldq; intuition. eapply SCP; eauto. 
          destruct e2x; destruct e2f; unfoldq; intuition. simpl. auto.
        * erewrite SE22; eauto. intros ?. eapply NP3. 
          erewrite lls_change.  eapply lls_mono. 2: eapply H8. eapply vars_locs_mono; eauto. 
          destruct e2x; unfoldq; intuition. eapply SCP; eauto. 
        * (* vt_valtype *)
          subst vtx. simpl. rewrite SCR5; eauto. unfold st1, st2. simpl.  eapply functional_extensionality. intros. eapply functional_extensionality. intros.
          eapply propositional_extensionality. split; intros. destruct H5 as [? | [? | ?]].
          destruct H5. intuition. right. intuition. right. right. intuition.
          destruct H5. intuition. right. intuition. 
          1,2: eapply strel_wf in NP1; eauto; destruct NP1. unfold st_locs1. auto. unfold st_locs2. auto.
        * auto.
        * (* st_filter *)
          remember H7 as H7'. clear HeqH7'. destruct H7' as [SFF1 [SFF2 SFF3]]. repeat split.
          ** unfold st1 at 1. simpl. unfold st_locs1, pnat, length1, st1. simpl.
             intros ? ?. erewrite <- lls_change with (M  := (fst (fst (fst M)))) in H8.
             unfold st1 in SFF1. eapply SFF1 in H8. unfold st_locs1, pnat, length1, st1 in *. lia.
             eapply sstchain_tighten with (p := st_locs1 M); eauto.
          ** unfold st2 at 1. simpl. unfold st_locs2, pnat, length2, st2. simpl.
             intros ? ?. erewrite <- lls_change with (M := (snd(fst(fst M)))) in H8.
             unfold st2 in SFF2. eapply SFF2 in H8. unfold st_locs2, pnat, length2, st2 in *. lia. 
             eapply sstchain_tighten; eauto. 
          ** unfold strel in H8. simpl in H8. destruct H8 as [[? [? ?]]| [[? [? | ?]] | [? ?]]]. 
             *** unfold st1, st2. simpl. intros. erewrite <- lls_change with (M := ((fst (fst(fst M))))) in H11. unfold st1, st2 in SFF3.
                 eapply SFF3 in H11 as H11'; eauto. erewrite <- lls_change. eapply H11'.
                 eapply sstchain_tighten; eauto. eapply sstchain_tighten with (p := st_locs1 M); eauto.
             *** unfold st1, st2. simpl. intros.
                 assert (strel M l0 l3). {  eapply SCP. intuition. intuition. }
                 erewrite <- lls_change with (M := (fst (fst (fst M)))) in H10.
                 unfold st1, st2 in SFF3. eapply SFF3 in H10 as H10'; eauto. erewrite <- lls_change. eapply H10'.
                 eapply sstchain_tighten; eauto. eapply sstchain_tighten with (p := st_locs1 M); eauto.
             *** intuition. unfold st2, st1 in *. simpl in *. 
                 assert False. eapply H12. split. left. unfold pdiff. split; eauto. left. unfoldq; intuition.
                 contradiction.
             *** unfold st1, st2. simpl. intuition.  rewrite <- lls_change with (M := (st1 M)) in H10. eapply SFF1 in H10.
                 unfold st_locs1, pnat in H10. assert False. eapply H12. lia. contradiction.
                 eapply sstchain_tighten; eauto.
          ** unfold strel in H8. simpl in H8.  destruct H8 as [[? [? ?]]| [[? [? | ?]] | [? ?]]].
            *** unfold st2, st1. simpl. intros. erewrite <- lls_change with (M := ((snd (fst(fst M))))) in H11. unfold st1, st2 in SFF3. 
                eapply SFF3 in H11 as H11'; eauto. erewrite <- lls_change. eapply H11'.
                eapply sstchain_tighten; eauto. eapply sstchain_tighten with (p := st_locs2 M); eauto.
            *** unfold st1, st2. simpl. intros.
                assert (strel M l0 l3). {  eapply SCP. intuition. intuition. }
                erewrite <- lls_change with (M := (snd (fst (fst M)))) in H10.
                unfold st1, st2 in SFF3. eapply SFF3 in H11 as H11'; eauto. erewrite <- lls_change. eapply H11' in H10. eauto.
                eapply sstchain_tighten; eauto. eapply sstchain_tighten with (p := st_locs2 M); eauto.
            *** intuition. unfold st2, st1 in *. simpl in *. 
                assert False. eapply H12. split. left. unfold pdiff. split; eauto. left. unfoldq; intuition.
                contradiction.
            *** unfold st1, st2. simpl. intuition.  rewrite <- lls_change with (M := (st2 M)) in H10. eapply SFF2 in H10.
                unfold st_locs2, pnat in H10. assert False. eapply H12. lia. contradiction.
                eapply sstchain_tighten; eauto.
      +  destruct YST as [YSST1 [YSST2 [YST [YSTR YSTL]]]]. destruct PM as [PM1 PM2].
         destruct (YST l1 l2) as (vtx & qt1x & qt2x & v1'x & v2'x & ? & ? & ? & ? & ? & ? & ?). eapply YSC; eauto.
         eapply W1 in PM1. eapply W2 in PM2. unfold st_locs1, st_locs2, pnat, length1, length2 in *. intuition. 
         exists vtx, qt1x, qt2x, v1'x, v2'x. split. 2: split. 3: split. 4: split. 5: split. 6: split.
         ++ unfold st1 in *. simpl. auto.
         ++ unfold st2 in *. simpl. auto.
         ++ auto.
         ++ auto.
         ++ unfold st1, st2. simpl. subst vtx. destruct YSC as [? [? [? [? [B ?]]]]].
            eapply functional_extensionality. intros. eapply functional_extensionality. intros. eapply propositional_extensionality. split; intros.
            destruct H12 as [? | [? | ?]]. intuition. destruct H12. destruct H13 as [[? ?] | [? [? ?]]]. 
            erewrite <- B; auto. eapply W1 in PM1. unfold st_locs1, pnat, length1 in *. lia.
            eapply W2 in PM2. unfold st_locs2, pnat, length2 in *. lia. 
            eapply W1 in PM1. unfold pnat, length1 in *. intuition.
            eapply W2 in PM2. unfold pnat, length2 in *. intuition.
            right. left. split; auto. erewrite B; auto. 
            eapply W1 in PM1. unfold st_locs1, pnat, length1 in *. intuition.
            eapply W2 in PM2. unfold st_locs2, pnat, length2 in *. intuition.
          ++ auto.
          ++ unfold st1, st2. simpl. repeat split.
             +++ unfold st_locs1, pnat, length1, st1. simpl. eapply H7; eauto.
             +++ unfold st_locs2, pnat, length2, st2. simpl. eapply H7; eauto.
             +++ unfold strel in H8. simpl in H8. destruct H8 as [[?[? ?]] | [[? ?] | [? [? [? [? ?]]]]]].
                 * intros ?. eapply val_reach_p in H11; eauto. 2: { erewrite <- lls_change; eauto. eapply SCPMM''; eauto.  }
                   rewrite <- lls_change with (M := (st1 M)) in H11. contradiction.
                   eapply SCPMM''; eauto.
                 * destruct H9 as [[? ?]| [? [? ?]]]. 
                   ** intros ?. eapply H7; eauto. eapply YSC; eauto.
                      eapply W1 in H9. eapply W2 in H10. unfold st_locs1, st_locs2, pnat, length1 in *. intuition.
                   ** destruct H11 as [? [? ?]]. assert False. eapply H11. split. left. unfold pdiff; eauto. left. unfoldq; intuition.
                      contradiction.
                 * intros ?. eapply H7; eauto.
             +++ unfold strel in H8. simpl in H8. destruct H8 as [[?[? ?]] | [[? ?] | [? [? [? [? ?]]]]]].
                 * intros ?. eapply val_reach_p in H11; eauto. 2: { erewrite <- lls_change; eauto. eapply SCPMM''; eauto.  }
                   rewrite <- lls_change with (M := (st2 M)) in H11. contradiction.
                   eapply SCPMM''; eauto.
                 * destruct H9 as [[? ?]| [? [? ?]]]. 
                   ** intros ?. eapply H7; eauto. eapply YSC; eauto.
                      eapply W1 in H9. eapply W2 in H10. unfold st_locs1, st_locs2, pnat, length1 in *. intuition.
                   ** destruct H11 as [? [? ?]]. assert False. eapply H11. split. left. unfold pdiff; eauto. left. unfoldq; intuition.
                      contradiction.
                 * intros ?. eapply H7; eauto.
      + (* strel M1 l1 l2 and l1 l2 are fresh *)
        destruct PM'' as [? [? [? [? ?]]]].  
        assert False. eapply H3. split. left. unfold pdiff; eauto. left. unfoldq; intuition. contradiction.    
      + (* strel M'' l1 l2 *) 
        destruct PM'' as [AP [BP [CP [DP EP]]]]. 
        destruct (STRELY l1 l2) as (vtx & qt1x & qt2x & v1'x & v2'x & ? & ? & ? & ? & ? & ? & ?). eauto.
        exists vtx, qt1x, qt2x, v1'x, v2'x. split. 2: split. 3: split. 4: split. 5: split. 6: split.
        * unfold st1. simpl. unfold length1 in DP. auto.
        * unfold st2. simpl. unfold length2 in EP. auto.
        * auto.
        * auto.
        * (* st_valtype *)
          simpl. subst vtx. eapply functional_extensionality. intros. eapply functional_extensionality. intros.
          eapply propositional_extensionality. split; intros.
          ** destruct H5 as [[? [? ?] ]| [? | ?]]; intuition.  destruct YSC as [? [? [? [? [B C]]]]]. erewrite <- B; eauto.
             eapply W1 in H9. unfold st_locs1, pnat, length1, st1 in *. lia.
             eapply W2 in H10. unfold st_locs2, pnat, length2, st2 in *. lia.
             eapply C; eauto. 
             eapply W1 in H9. unfold st_locs1, pnat, length1, st1 in *. 
             eapply W2 in H10. unfold st_locs2, pnat, length2, st2 in *. intuition. 
          ** right. right. intuition.
        * auto.
        * unfold st1, st2. simpl. repeat split.
          ** unfold st_locs1, pnat, length1, st1. simpl. eapply H7.
          ** eapply H7; eauto.
          ** unfold strel in H8. simpl in H8. destruct H8 as [[? [? ?]]| [[? ?]|[? [? [? [? ?]]]]]].
             *** intros ?.  assert (strel M'' l0 l3). { destruct YSC as [? [? [? [? [? B]]]]]. eapply B; eauto. eapply strel_wf in H8.
                 unfold st_locs1, st_locs2. unfold pnat, length1, length2, st1, st2 in *. intuition. eauto.
                 rewrite HeqM1. unfold strel. simpl. auto. }
                 eapply H7; eauto.
             *** destruct H9 as [[? ?] |[? [? [? [? ?]]]]].
                 intros. assert (strel M'' l0 l3). eapply YSC; eauto. eapply strel_wf in H8; eauto.
                 erewrite lls_change with (M' := (st1 M'')) in H9. 2: { eapply sstchain_tighten; eauto. }  
                 eapply H7; eauto.
                 assert False. eapply H11. split. left. unfold pdiff; eauto. left. unfoldq; intuition. contradiction.
             *** intros ?. eapply H7; eauto.
          ** unfold strel in H8. simpl in H8. destruct H8 as [[? [? ?]]| [[? ?]|[? [? [? [? ?]]]]]].
             *** intros ?. assert (strel M'' l0 l3). { destruct YSC as [? [? [? [? [? B]]]]]. eapply B; eauto. eapply strel_wf in H8.
                 unfold st_locs1, st_locs2. unfold pnat, length1, length2, st1, st2 in *. intuition. eauto.
                 rewrite HeqM1. unfold strel. simpl. auto. }
                 eapply H7; eauto.
             *** destruct H9 as [[? ?] |[? [? [? [? ?]]]]].
                 intros. assert (strel M'' l0 l3). eapply YSC; eauto. eapply strel_wf in H8; eauto.
                 erewrite lls_change with (M' := (st2 M'')) in H10. 2: { eapply sstchain_tighten; eauto. }  
                 eapply H7; eauto.
                 assert False. eapply H11. split. left. unfold pdiff; eauto. left. unfoldq; intuition. contradiction.
             *** intros ?. eapply H7; eauto.
    - intros. unfold strel in H0, H. simpl in H0, H.  
      destruct H0 as [(B&?) | [(C&?) | (D&?)]]; destruct H as [(U&?) | [(V&?) | (W&?)]].
      + eauto.
      + eapply strel_wf in B; eauto. intuition.
      + intuition. eapply strel_wf in B; eauto. intuition.
      + intuition. eapply strel_wf in U; eauto. intuition.
      + destruct ST1 as [? [? [? [R L]]]]. eapply R; eauto.
      + eapply strel_wf in C; eauto. intuition.
      + eapply strel_wf in U; eauto. intuition.
      + eapply strel_wf in V; eauto. intuition.
      + eauto.        
    - intros. unfold strel in H0, H. simpl in H0, H. 
      destruct H0 as [(B&?) | [(C&?) | (D&?)]]; destruct H as [(U&?) | [(V&?) | (W&?)]].
      + eauto.
      + eapply strel_wf in B; eauto. intuition.
      + eapply strel_wf in B; eauto. intuition.
      + eapply strel_wf in U; eauto. intuition.
      + destruct ST1 as [? [? [? [R L]]]]. eapply L; eauto.
      + eapply strel_wf in C; eauto. intuition.
      + eapply strel_wf in U; eauto. intuition.
      + eapply strel_wf in V; eauto. intuition.
      + eauto. 
  }

  assert (sst_chain_partial (st1 M'') (st1 MR) (locs_locs_stty (st1 M'') (vars_locs H1 (plift p)))) as SSTM''MR1. {
    subst MR. repeat split.
    - eapply envt_store_deep_wf; eauto. unfoldq; intuition.
    - unfold st1. simpl. eapply envt_store_deep_wf; eauto. unfoldq; intuition.
  }

  assert (sst_chain_partial (st2 M'') (st2 MR) (locs_locs_stty (st2 M'') (vars_locs H2 (plift p)))) as SSTM''MR2. {
    subst MR. repeat split.
    - eapply envt_store_deep_wf; eauto. unfoldq; intuition.
    - unfold st2. simpl. eapply envt_store_deep_wf; eauto. unfoldq; intuition.
  }

   
  assert(st_chain_partial M'' MR (locs_locs_stty (st1 M'') (val_locs v1'')) (locs_locs_stty (st2 M'') (val_locs v2''))) as STCV. { 
    repeat split. 
    - eapply valt_deep_wf; eauto.
    - eapply valt_deep_wf; eauto.
    - intros. eapply valt_same_locs_deep; eauto.
    - intros. eapply valt_same_locs_deep; eauto.
    - intros ? ?. destruct (QY1 x); auto. subst MR. unfold st_locs1, pnat, length1, st1. simpl. eapply valt_deep_wf ; eauto.
      subst MR. unfold st_locs1, pnat, length1, st1. simpl. eapply valt_deep_wf ; eauto.
    - intros ? ?. destruct (QY2 x); auto. subst MR. unfold st_locs2, pnat, length2, st2. simpl. eapply valt_deep_wf ; eauto.
      subst MR. unfold st_locs2, pnat, length2, st2. simpl. eapply valt_deep_wf ; eauto.
    - intros ?. eapply valt_same_locs_deep; eauto. subst MR. simpl in H. 
      destruct H as [[? [? ?]] | [? | ?]].
      -- destruct (QY1 l1). auto. assert False. 
         replace (v1::H1) with ([v1]++H1) in H5. 2: simpl; auto. rewrite vars_locs_extend in H5.
         eapply H3. erewrite lls_change. eapply lls_mono. 2: eapply H5. eapply vars_locs_mono; eauto.
         destruct ar2; destruct fn2; unfoldq; intuition. 
         eapply sstchain_tighten. eapply SCR; eauto. eauto. 
         destruct ar2; destruct fn2; unfoldq; intuition. contradiction. 
         destruct fr2; simpl in H5. destruct H5. eapply strel_wf in H. destruct H. unfold pdom. unfold pnat, length1, st1 in *. lia. eauto. contradiction.
      -- destruct H. destruct H3 as [? | ?].
         eapply SCPR; eauto. intuition. assert False. eapply H5. split. left. unfold pdiff. split. eauto. eauto. left. unfoldq; intuition.
         contradiction.
      -- intuition.
    - intros ?. eapply valt_same_locs_deep; eauto. subst MR. simpl in H. 
      destruct H as [[? [? ?]] | [? | ?]].
      -- destruct (QY2 l2). auto. assert False.
         eapply H4. erewrite lls_change. eapply lls_mono. 2: eapply H5.
         intros ? ?. destruct H6 as [? [? ?]]. destruct H6. exists x0; intuition.
         eapply sst_trans''. eapply SCP; eauto. eapply SCPR; eauto. eapply envt_store_deep_wf; eauto. unfoldq; intuition. contradiction.
         destruct fr2; simpl in H5. destruct H5. eapply strel_wf in H. destruct H. unfold pdom. unfold pnat, length2, st2 in *. lia. eauto. contradiction.
      -- destruct H. destruct H3 as [? | ?].
         eapply SCPR; eauto. intuition. assert False. eapply H5. split. left. unfold pdiff. split; eauto. left. unfoldq; intuition.
         contradiction.
      -- intuition.
    - eapply valt_deep_wf; eauto.
    - intros ? ?. destruct (QY1 x); auto. subst MR. unfold st_locs1, pnat, length1, st1. simpl. eapply valt_deep_wf ; eauto.
      subst MR. unfold st_locs1, pnat, length1, st1. simpl. eapply valt_deep_wf ; eauto.
    - intros. subst MR. unfold st1. simpl. auto.
    - eapply valt_deep_wf; eauto.
    - intros ? ?. destruct (QY2 x); auto. subst MR. unfold st_locs2, pnat, length2, st2. simpl. eapply valt_deep_wf ; eauto.
      subst MR. unfold st_locs2, pnat, length2, st2. simpl. eapply valt_deep_wf ; eauto.
    - intros. subst MR. unfold st2. simpl. auto.
    - intros. subst MR. unfold st1. simpl. 
      destruct (QY1 l1); destruct (QY2 l2); auto;  
      eapply functional_extensionality; intros; eapply functional_extensionality; intros;
      eapply propositional_extensionality; split; intros.
      -- replace (v1::H1) with ([v1] ++ H1) in H4. rewrite vars_locs_extend in H4. 3: simpl; auto. 2: unfoldq; intuition.
         right. left. rewrite <- lls_change with (M := (st1 M)) in H4. rewrite <- lls_change with (M := (st2 M)) in H5.  
         assert (strel M1 l1 l2). { eapply SCPR; eauto. split. eapply lls_mono. 2: eapply H4. eapply vars_locs_mono; eauto. unfoldq; intuition. 
           eapply lls_mono; eauto. eapply vars_locs_mono; eauto. unfoldq; intuition.  }
         split. destruct SCPR as [? [? [? [? [XX ?]]]]]. erewrite XX; eauto. eapply lls_mono. 2: eapply H4. eapply vars_locs_mono; eauto. unfoldq; intuition. 
         eapply lls_mono; eauto. eapply vars_locs_mono; eauto. unfoldq; intuition. 
         left. split. eapply lls_mono. 2: eapply H4. eapply vars_locs_mono; eauto. unfoldq; intuition. 
         eapply lls_mono; eauto. eapply vars_locs_mono; eauto. unfoldq; intuition.
         eapply sst_trans''. eapply sstchain_tighten. eapply SCP; eauto. eapply lls_mono; eauto. eapply vars_locs_mono; eauto. unfoldq; intuition.
         eapply sstchain_tighten. eapply SCPR; eauto. eapply lls_mono; eauto. eapply vars_locs_mono; eauto. unfoldq; intuition.
         eapply envt_store_deep_wf; eauto. unfoldq; intuition. 
         eapply sst_trans''. eapply sstchain_tighten. eapply SCP; eauto. eapply lls_mono; eauto. eapply vars_locs_mono; eauto. unfoldq; intuition.
         eapply sstchain_tighten. eapply SCPR; eauto. eapply lls_mono; eauto. eapply vars_locs_mono; eauto. unfoldq; intuition.
         eapply envt_store_deep_wf; eauto. unfoldq; intuition. 
      -- replace (v1::H1) with ([v1] ++ H1) in H4. rewrite vars_locs_extend in H4. 3: simpl; auto. 2: unfoldq; intuition.
         destruct H6 as [[? [? ?]] | [[? ?] | [? ?]]]. 
         * destruct H8 as [? [? ?]]. rewrite <- lls_change with (M := (st1 M)) in H4. 
           assert False. { eapply H9. eapply lls_mono. 2: eapply H4. eapply vars_locs_mono; eauto. unfoldq; intuition. }
           contradiction. 
           eapply sst_trans''. eapply sstchain_tighten. eapply SCP; eauto. eapply lls_mono; eauto. eapply vars_locs_mono; eauto. unfoldq; intuition.
           eapply sstchain_tighten. eapply SCPR; eauto. eapply lls_mono; eauto. eapply vars_locs_mono; eauto. unfoldq; intuition. 
           eapply envt_store_deep_wf; eauto. unfoldq; intuition. 
         * rewrite <- lls_change with (M := (st1 M)) in H4. rewrite <- lls_change with (M := (st2 M)) in H5.
           assert (strel M1 l1 l2). { eapply SCPR; eauto. split. eapply lls_mono. 2: eapply H4. eapply vars_locs_mono; eauto. unfoldq; intuition. 
           eapply lls_mono; eauto. eapply vars_locs_mono; eauto. unfoldq; intuition.  } 
           destruct SCPR as [? [? [? [? [XX ?]]]]]. erewrite <- XX; eauto. eapply lls_mono. 2: eapply H4. eapply vars_locs_mono; eauto. unfoldq; intuition. 
           eapply lls_mono; eauto. eapply vars_locs_mono; eauto. unfoldq; intuition. auto.

           eapply sst_trans''. eapply sstchain_tighten. eapply SCP; eauto. eapply lls_mono; eauto. eapply vars_locs_mono; eauto. unfoldq; intuition.
           eapply sstchain_tighten. eapply SCPR; eauto. eapply lls_mono; eauto. eapply vars_locs_mono; eauto. unfoldq; intuition. 
           eapply envt_store_deep_wf; eauto. unfoldq; intuition. 
           eapply sst_trans''. eapply sstchain_tighten. eapply SCP; eauto. eapply lls_mono; eauto. eapply vars_locs_mono; eauto. unfoldq; intuition.
           eapply sstchain_tighten. eapply SCPR; eauto. eapply lls_mono; eauto. eapply vars_locs_mono; eauto. unfoldq; intuition.
           eapply envt_store_deep_wf; eauto. unfoldq; intuition. 
         * intuition.
      --  replace (v1::H1) with ([v1] ++ H1) in H4. rewrite vars_locs_extend in H4. 3: simpl; auto. 2: unfoldq; intuition.
          eapply envt_same_locs in H3 as H3'. eapply H3' in H4. 2: eauto. 2: eauto. 2: unfoldq; intuition.
          destruct fr2; simpl in H5; try contradiction. destruct H5. 
          erewrite <- lls_change with (M := (st2 M1)) in H4. eapply envt_store_deep_wf in H4; eauto. 
          unfoldq; intuition. 
          
          erewrite <- lls_change with (M := (st2 M)).
          eapply sstchain_tighten. eapply SCPR; eauto. eapply lls_mono; eauto. eapply vars_locs_mono; eauto. unfoldq; intuition.
          eapply sstchain_tighten. eapply SCP; eauto. eapply lls_mono; eauto. eapply vars_locs_mono; eauto. unfoldq; intuition.
      -- replace (v1::H1) with ([v1] ++ H1) in H4. rewrite vars_locs_extend in H4. 3: simpl; auto. 2: unfoldq; intuition.
         eapply envt_same_locs in H3 as H3'. eapply H3' in H4. 2: eauto. 2: eauto. 2: unfoldq; intuition.
         destruct fr2; simpl in H5; try contradiction. destruct H5. 
         erewrite <- lls_change with (M := (st2 M1)) in H4. eapply envt_store_deep_wf in H4; eauto. 
         unfoldq; intuition. 
         
         erewrite <- lls_change with (M := (st2 M)).
         eapply sstchain_tighten. eapply SCPR; eauto. eapply lls_mono; eauto. eapply vars_locs_mono; eauto. unfoldq; intuition.
         eapply sstchain_tighten. eapply SCP; eauto. eapply lls_mono; eauto. eapply vars_locs_mono; eauto. unfoldq; intuition.
      -- destruct fr2; simpl in H4; try contradiction. destruct H4.
         eapply envt_same_locs in H3 as H3'. eapply H3' in H5. 2: eauto. 2: eauto. 2: unfoldq; intuition.
         erewrite <- lls_change with (M := (st1 M1)) in H5. eapply envt_store_deep_wf in H5; eauto. 
         unfoldq; intuition. 
         
         erewrite <- lls_change with (M := (st1 M)).
         eapply sstchain_tighten. eapply SCPR; eauto. eapply lls_mono; eauto. eapply vars_locs_mono; eauto. unfoldq; intuition.
         eapply sstchain_tighten. eapply SCP; eauto. eapply lls_mono; eauto. eapply vars_locs_mono; eauto. unfoldq; intuition.
      -- destruct fr2; simpl in H4; try contradiction. destruct H4.
         eapply envt_same_locs in H3 as H3'. eapply H3' in H5. 2: eauto. 2: eauto. 2: unfoldq; intuition.
         erewrite <- lls_change with (M := (st1 M1)) in H5. eapply envt_store_deep_wf in H5; eauto. 
         unfoldq; intuition. 
         
         erewrite <- lls_change with (M := (st1 M)).
         eapply sstchain_tighten. eapply SCPR; eauto. eapply lls_mono; eauto. eapply vars_locs_mono; eauto. unfoldq; intuition.
         eapply sstchain_tighten. eapply SCP; eauto. eapply lls_mono; eauto. eapply vars_locs_mono; eauto. unfoldq; intuition.
      -- destruct fr2; simpl in H4, H5; try contradiction.  unfold pnot, pdom in H4, H5.
         right. right. intuition. eapply valt_deep_wf in H; eauto. eapply valt_deep_wf in H0; eauto.
      -- destruct fr2; simpl in H4, H5; try contradiction. unfold pnot, pdom in H4, H5.
         destruct H6 as [[? [? [? [? ?]]]] | [[? [? | ?]] | ?]]. 
         * assert False.  eapply H4. unfold pnat, length1, st1 in *. lia. contradiction. 
         * destruct H7. eapply W1 in H7. 
           assert False. eapply H4. unfold pnat, length1, st1 in *. lia. contradiction.
         * destruct H7 as [? [? [? [? ?]]]]. intuition.
         * intuition.
    - intros. destruct H. subst MR. unfold strel. simpl.
      destruct (QY1 l1); destruct (QY2 l2); auto. 
      replace (v1::H1) with ([v1] ++ H1) in H4. rewrite vars_locs_extend in H4. 3: simpl; auto. 2: unfoldq; intuition.
      -- right. left. split; auto. eapply SCPR; eauto. split. erewrite lls_change. eapply lls_mono. 2: eapply H4. eapply vars_locs_mono; eauto.
         unfoldq; intuition. eapply sstchain_tighten; eauto. erewrite lls_change. eapply lls_mono. 2: eapply H5. eapply vars_locs_mono; eauto.
         unfoldq; intuition. eapply sstchain_tighten; eauto. 
         left. split. erewrite lls_change. eapply lls_mono. 2: eapply H4. eapply vars_locs_mono; eauto.
         unfoldq; intuition. eapply sstchain_tighten; eauto. erewrite lls_change. eapply lls_mono. 2: eapply H5. eapply vars_locs_mono; eauto.
         unfoldq; intuition. eapply sstchain_tighten; eauto. 
      -- destruct fr2; simpl in H5; try contradiction. destruct H5. 
         replace (v1::H1) with ([v1] ++ H1) in H4. rewrite vars_locs_extend in H4. 3: simpl; auto. 2: unfoldq; intuition.
         eapply envt_same_locs with (H2 := H2) in H0. eapply H0 in H4. 2: eauto. 2: eauto. 2: unfoldq; intuition.
         erewrite <- lls_change with (M := st2 M1) in H4. eapply envt_store_deep_wf in H4; eauto. 
         unfoldq; intuition. rewrite <- lls_change with (M := (st2 M)). eapply sstchain_tighten. eapply SCPR; eauto.
         eapply lls_mono; eauto. eapply vars_locs_mono; eauto. destruct ar2; destruct fn2; unfoldq; intuition.
         eapply sstchain_tighten. eapply SCP; eauto. eapply lls_mono; eauto. eapply vars_locs_mono; eauto. destruct ar2; destruct fn2; unfoldq; intuition.
      -- destruct fr2; simpl in H4; try contradiction. unfold pnot, pdom in H4.
         eapply envt_same_locs with (H2 := H2) in H0. eapply H0 in H5. 2: eauto. 2: eauto. 2: unfoldq; intuition.
         erewrite <- lls_change with (M := st1 M1) in H5. eapply envt_store_deep_wf in H5. 2: eapply WFEM1. unfold length1 in H5. contradiction.
         unfoldq; intuition. rewrite <- lls_change with (M := (st1 M)). eapply sstchain_tighten. eapply SCPR; eauto.
         eapply lls_mono; eauto. eapply vars_locs_mono; eauto. unfoldq; intuition.
         eapply sstchain_tighten. eapply SCP; eauto. eapply lls_mono; eauto. eapply vars_locs_mono; eauto. unfoldq; intuition.
      -- destruct fr2; simpl in H4, H5; try contradiction. unfold pnot, pdom in H4, H5.
         right. right. intuition. eapply valt_deep_wf in H; eauto. eapply valt_deep_wf in H3; eauto.
    - intros. destruct H. subst MR. unfold strel in H0. simpl in H0.
      destruct H0 as [[? [? ?]]| [[? ?] | [? [? ?]] ]].
      -- destruct (QY1 l1); destruct (QY2 l2); auto.
         replace (v1::H1) with ([v1] ++ H1) in H6. rewrite vars_locs_extend in H6. 3: simpl; auto. 2: unfoldq; intuition. 
         rewrite <- lls_change with (M := st1 M) in H6. 2: { eapply sstchain_tighten; eauto. eapply envt_store_deep_wf; eauto. unfoldq; intuition. }
         assert False. eapply H4. eapply lls_mono; eauto. eapply vars_locs_mono; eauto. unfoldq; intuition. contradiction.
         destruct fr2; simpl in H7; try contradiction. unfold pnot, pdom in H7. eapply strel_wf in H0; eauto. 
         unfold pnat, length2, st2 in *. intuition.
         destruct fr2; simpl  in H6; try contradiction. unfold pnot, pdom in H6. eapply strel_wf in H0; eauto. 
         unfold pnat, length1, st1 in *. intuition. 
         destruct fr2; simpl in H6; simpl in H7; try contradiction.
         unfold pnot, pdom in H6, H7.
         eapply strel_wf in H0; eauto. 
         unfold pnat, length1, st1 in *. intuition. 
      -- destruct H4 as [[? ?]| [? [? [? ?]]]].
         eapply SCPR; eauto.
         assert False. eapply H6. split. left. unfold pdiff; split; eauto. left. unfoldq; intuition. contradiction.
      -- intuition. 
  }
  

  assert (val_type MR H1 H2 v1'' v2'' T2 T2) as VTMR. {
    eapply valt_extend with(H1' := [v1]) (H2' := []); eauto.
    rewrite L1. auto. rewrite L2. auto. simpl. eapply valt_store_change. 2: eapply VY. eauto. 
    eapply STCV.  
  }
          
  exists S1'', S2'', MR, v1'', v2''. split.

  (* first term *)
  destruct IE1 as [n1 IE1].
  destruct IEF1 as [n2 IEF1].  
  destruct YE1 as [n3 YE1].  
  exists ((S (n1+n2+n3))). intros.
  destruct n. lia. simpl. 
  rewrite IEF1; try lia.
  destruct vf; destruct vf'; try solve [inversion VTF]; simpl in VTF; intuition.
  rewrite IE1; try lia.
  assert  (l = H1 /\ t = t2). assert (S n2 > n2) as N1. lia.
  specialize (IEF1 (S n2) N1). simpl in IEF1. inversion IEF1.
  intuition. destruct H13. subst l. subst t.
  rewrite YE1. f_equal. f_equal.  lia. lia. 
  
  (* second term *) 
  split.
  replace (length G) with (length H2). auto.
  

  split. auto.
  split. auto.
  split. auto.
  split.  replace (v1 :: H1) with ([v1]++H1) in YEFF1. rewrite vars_locs_extend in YEFF1.
  eapply se_trans.  eapply se_trans.  
  eapply se_sub. eapply se_trans. eapply FEFF1. eauto. intros ? ?. unfoldq; intuition. 
  eapply se_sub with (p := pempty). intros ? ? ?. unfoldq; intuition. eauto. unfoldq; intuition.
  erewrite lls_change with (M' := (st1 M1)).
  eapply se_sub. eapply YEFF1. eapply lls_mono; eauto. eapply vars_locs_mono; eauto.
  unfoldq; intuition. destruct e2x; simpl in H3; try contradiction. 
  eapply PD3 in H0. replace (length H1) with (length G) in H0. lia. 
  right. destruct e2f; unfoldq; intuition.
  eapply sstchain_tighten. eapply SCP. eapply lls_mono; eauto. eapply vars_locs_mono; eauto. unfoldq; intuition.
  unfoldq; intuition. simpl. auto.

  split. 
  erewrite lls_change with (M' := (st2 M1)).
  eapply se_sub; eauto. eapply lls_mono; eauto. eapply vars_locs_mono; eauto. unfoldq; intuition.
  destruct e2x; simpl in H3; try contradiction. eapply PD3 in H0. replace (length H1) with (length G) in H0. lia.
  right. destruct e2f; unfoldq; intuition.
  eapply sstchain_tighten. eapply SCP. eapply lls_mono; eauto. eapply vars_locs_mono; eauto. unfoldq; intuition.

  (*  valt *)
  split. eapply VTMR.
  
  (* valq 1*)
  split. 
  {
    intros ? ?.
    rewrite HeqMR in H.  unfold st1 in H. simpl in H.
    destruct (QY1 x). auto. 
    left. rewrite HeqMR. unfold st1. simpl. replace (v1::H1) with ([v1]++H1) in H0. 2: simpl; auto. rewrite vars_locs_extend in H0.
    2: unfoldq; intuition. eapply lls_mono; eauto. eapply vars_locs_mono; eauto. destruct ar2; destruct fn2; try contradiction; unfoldq; intuition.
    eapply PD3 in H4. replace (length H1) with (length G) in H4. lia.
    eapply PD3 in H4. replace (length H1) with (length G) in H4. lia.
    right. destruct fr2; simpl in *; try contradiction. unfold pnot, pdom in *. 
    intros ?. eapply H0.  unfold length1, st1 in *. lia.
  }
  
  (* valq 2*)
  {
    intros ? ?.
    rewrite HeqMR in H. unfold st1 in H. simpl in H.
    destruct (QY2 x). auto. 
    left. rewrite HeqMR. unfold st2. simpl. eapply lls_mono; eauto. eapply vars_locs_mono; eauto. destruct ar2; destruct fn2; try contradiction; unfoldq; intuition.
    eapply PD3 in H4. replace (length H1) with (length G) in H4. lia.
    eapply PD3 in H4. replace (length H1) with (length G) in H4. lia.
    right. destruct fr2; simpl in *; try contradiction. unfold pnot, pdom in *.
    intros ?. eapply H0. 
    subst M1. simpl in *. eapply st_mono2 in SCX. unfold length2, st2 in *. lia.
  }
Qed.
