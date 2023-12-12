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
Require Import stlc_reach_ref_effects_reorder_beta1.

Import STLC.

(* splice and substitution *)

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
(*  | tvar (varB x) => tvar (varB x) *)
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
  | TBool                    => TBool
  | TRef T                   => TRef (splice_ty T i n)
  | TFun T1 T2 q2 e2         => TFun (splice_ty T1 i n) (splice_ty T2 i n) (splice_ql q2 i n) (splice_ql e2 i n) 
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
  | TBool                   => TBool
  | TRef T                  => TRef (subst_ty T i p)
  | TFun T1 T2 q2 e2        => TFun (subst_ty T1 i p) (subst_ty T2 i p) (subst_ql q2 i p) (subst_ql e2 i p) 
end.


Fixpoint subst_tm (t: tm) (i: nat) (u:tm) (p:ql) : tm := 
  match t with 
  | ttrue         => ttrue
  | tfalse        => tfalse
(*  | tvar (varB x) => tvar (varB x) *)
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
  (* bdestruct (m+n <=? x); intuition. *)
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
  + simpl. inversion H. subst. specialize (IHT i n H2). rewrite IHT. auto.
  + simpl. inversion H. subst. 
    specialize (IHT1 i n H5). specialize (IHT2 i n H6).
    rewrite IHT1. rewrite IHT2.
    erewrite spliceq_id; eauto.
    erewrite spliceq_id; eauto.
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
  + constructor. inversion H0. subst.  intuition.
  + inversion H0. subst. intuition. constructor; auto.
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

Lemma psub_splice: forall{X} p (H21 H22 HX : list X),
  psub (plift p) (pdom (H21++H22)) ->
  psub (plift (splice_ql p (length H22)(length HX))) (pdom (H21++HX++H22)).
Proof.
 intros. rewrite plift_splice.
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


(* substitution lemmas *)

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
  rewrite IHT; auto. inversion H. subst. auto.
  rewrite IHT1. rewrite IHT2. 
  rewrite substq_id. rewrite substq_id.
  auto. 1-4: inversion H; subst; auto.
Qed.  
(*
Lemma substp_closed: forall m n p q,
  (forall x, p x = true -> x < m + S n) ->
  (forall x, q x = true -> x < n) ->
  forall x, subst_pl (plift p) n (plift q) x -> x < m + n.
Proof.
  intros. unfold subst_pl in H1.
  unfoldq; intuition.
  eapply H in H4. lia.
  eapply H0 in H2. lia.
  eapply H in H3. lia.
Qed.
*)

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

Lemma substy_closed_gen: forall T m n q1,
  closed_ty (m + S n) T ->
  closed_ql n q1 ->
  closed_ty (m+n) (subst_ty T n q1).
Proof.
  intros T. induction T; intros; simpl in *.
  constructor.
  constructor. eapply IHT. inversion H. auto.  auto.
  inversion H. subst.  constructor. eapply IHT1. auto. auto.
  eapply IHT2. auto. auto.
  eapply substp_closed; eauto. 
  eapply substp_closed; eauto. 
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
  psub (plift q2) (plift p) ->
  q1 = qempty -> 
  psub (subst_pl (plift q2) m (plift q1)) 
       (subst_pl (plift p) m (plift p1)).
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



(*----------env_type1; exp_type1---------------*)

Definition exp_type1 S1 S2 M H1 H2 t1 t2 S1' S2' M' v1 v2 T1 T2 p1 p2 q1 q2 (e1 e2: pl)  :=
  tevaln S1 H1 t1 S1' v1 /\
  tevaln S2 H2 t2 S2' v2 /\
  store_effect S1 S1' (vars_locs H1 p1) /\
  store_effect S2 S2' (vars_locs H2 p2) /\
  st_chain M M'   /\
  store_type S1' S2'  M' /\
  val_type M' H1 H2 v1 v2 T1 T2 /\
  val_qual (length1 M) H1 v1 p1 q1 /\
  val_qual (length2 M) H2 v2 p2 q2 
.

Definition env_type1 M H1 H2 H2' HX G p :=
  length H1 = length G /\
  length (H2'++HX++H2) = length G + length HX /\
    psub (plift p) (pdom H1) /\
    psub (plift (splice_ql p (length H2) (length HX)))(pdom (H2'++HX++H2)) /\
    (forall x T,
        indexr x G = Some T ->
        plift p x ->
        exists v1 v2 : vl,
        indexr x H1 = Some v1 /\
        indexr (if x <? length H2 then x else x + length HX) (H2' ++ HX ++ H2) = Some v2 /\
        val_type M H1 (H2'++HX++H2) v1 v2 T (splice_ty T (length H2) (length HX))) /\
    (forall l x0 x1,
        plift p x0 ->
        var_locs H1 x0 l ->
        plift p x1 ->
        var_locs H1 x1 l ->
        x0 = x1) /\
    (forall l x0 x1, 
        (plift (splice_ql p (length H2) (length HX))) x0 ->
        var_locs (H2'++HX++H2) x0 l ->
        (plift (splice_ql p (length H2) (length HX))) x1 ->
        var_locs (H2'++HX++H2) x1 l ->
        x0 = x1)  
.




Lemma vars_locs_dist_and11: forall M H1 H2 H2' HX G p q q'
    (WFE: env_type1 M H1 H2 H2' HX G  p),
    psub q (plift p) ->
    psub q' (plift p) ->
    pand (vars_locs H1 q) (vars_locs H1 q') = vars_locs H1 (pand q q').    
Proof.
  intros. 
  eapply functional_extensionality.
  intros. eapply propositional_extensionality.
  destruct WFE as [L1 [L2 [P1 [P2 [W [SEP1 SEP2]]]]]].
  intuition.
  - destruct H3 as [[? [? ?]]  [? [? ?]]].
    assert (x0 = x1). eapply SEP1; eauto. subst x1.
    exists x0. unfoldq. intuition.
  - destruct H3 as [? [? [? [? ?]]]].
    unfoldq. intuition.
    exists x0. intuition. exists x1. intuition.
      
    exists x0. intuition. exists x1. intuition.
Qed.

Lemma vars_locs_dist_and22: forall M H1 H2 H2' HX G p q q'
    (WFE: env_type1 M H1 H2 H2' HX G p),
    psub (plift (splice_ql q (length H2) (length HX))) (plift (splice_ql p (length H2) (length HX))) ->
    psub (plift (splice_ql q' (length H2) (length HX))) (plift (splice_ql p (length H2) (length HX))) ->
    pand (vars_locs (H2'++HX++H2) (plift (splice_ql q (length H2) (length HX)))) (vars_locs (H2'++HX++H2) (plift (splice_ql q' (length H2) (length HX)))) = 
          vars_locs (H2'++HX++H2) (pand (plift (splice_ql q (length H2) (length HX))) (plift (splice_ql q' (length H2) (length HX)))). 
Proof. 
  intros. eapply functional_extensionality.
  intros. eapply propositional_extensionality.
  destruct WFE as [L1 [L2 [P1 [P2 [W [SEP1 SEP2]]]]]].
  intuition.
  - destruct H3 as [[? [? ?]]  [? [? ?]]].
    assert (x0 = x1). eapply SEP2; eauto. subst x1.
    exists x0. unfoldq. intuition.
  - destruct H3 as [? [? [? [? ?]]]].
    unfoldq. intuition.
    exists x0. intuition. exists x1. intuition.
      
    exists x0. intuition. exists x1. intuition.  
Qed.



Lemma valt_splice: forall T1 T2 M H1 H2 H2' HX v1 v2
  (CLT1: closed_ty (length (H2'++H2)) T1)
  (CLT2: closed_ty (length (H2'++H2)) T2), 
  val_type M H1 (H2'++H2) v1 v2 T1 T2 <->
  val_type M H1 (H2'++HX++H2) v1 v2 T1 (splice_ty T2 (length H2) (length HX)).
Proof.
  intros T1. induction T1; intros; destruct T2; destruct v1; destruct v2; simpl in *; intuition.
  + subst. simpl. eauto.
  + destruct T2; simpl in H; congruence.
  + eapply  closedty_splice; eauto.
  + eapply closedty_splice; eauto.
  + eapply pdom_slice; eauto. 
  + eapply pdom_slice; eauto. 
  + destruct (H13 S1' S2' M' vx1 vx2 H12) as [S1'' [S2'' [M'' [vy1 [vy2 [IE1 [IE2 [STC' [ST'[EFF1 [EFF2  [HEY [HYQ1 HYQ2]]]]]]]]]]]]]; auto.
    eapply IHT1_1; eauto.
    inversion CLT1. subst. auto.
    exists S1'', S2'', M'', vy1, vy2.
    split. auto. split. auto. split.
    auto. split. auto. split. auto. split. auto.
    
    split. eapply IHT1_2 in HEY; eauto.
    inversion CLT1. subst. auto.
    split.  auto. rewrite plift_splice. rewrite vars_locs_splice. auto.
  + inversion CLT2. subst. auto.
  + inversion CLT2. subst. auto.
  + inversion CLT2. subst. auto.
  + inversion CLT2. subst. auto.
  + destruct (H13 S1' S2' M' vx1 vx2 H12) as [S1'' [S2'' [M'' [vy1 [vy2 [IE1 [IE2 [STC' [ST' [EFF1 [EFF2 [HEY [HYQ1 HYQ2]]]]]]]]]]]]]; auto.
    rewrite <- IHT1_1; eauto.
    inversion CLT1. subst. auto.
    inversion CLT2. subst. auto.
    exists S1'', S2'', M'', vy1, vy2. 
    split. auto. split. auto. split. auto.
    split. auto. split. auto. split. auto.
    split. rewrite IHT1_2. eauto. inversion CLT1. subst. auto. inversion CLT2. subst. auto.
    split. auto. 
    erewrite <- vars_locs_splice. rewrite <- plift_splice. eapply HYQ2.
Qed.

Lemma wf_env_type1: forall M H1 H2 H2' HX G p, 
  env_type1 M H1 H2 H2' HX G p -> 
  (length H1 = length G /\
   length (H2'++H2) = length G /\
   pdom H1 = pdom G /\
   pdom (H2'++H2) = pdom G /\  
   psub (plift p) (pdom H1) /\
   psub (plift (splice_ql p (length H2)(length HX))) (pdom (H2'++HX++H2))
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

Lemma env_type_store_wf1: forall M H1 H2 H2' HX G p q,
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
  assert ((splice_nat x0 (length H2)(length HX)) < length (H2'++HX++H2)). eapply P2. rewrite plift_splice. auto.

  assert (exists T, indexr x0 G = Some T) as TY. 
  eapply indexr_var_some. rewrite <-L1. eauto.
  destruct TY as [T ?].
  destruct H3 as [? [? ?]].
  destruct (W1 x0 T) as [vx1 [vx2 [IX1 [IX2 IV ]]]]. eauto. eauto. 
  rewrite H3 in IX1. inversion IX1. subst x1.

  eapply valt_wf in IV.  intuition. 
  eapply H8; eauto.
Qed.


Lemma env_type_store_wf2: forall M H1 H2 H2' HX G p q,
    env_type1 M H1 H2 H2' HX G p ->
    psub (plift q) (plift p) -> 
    psub (vars_locs (H2'++HX++H2) (plift (splice_ql q (length H2) (length HX)))) (pnat (length2 M)). 
Proof.
  intros.
  assert ((vars_locs (H2'++HX++H2)(splice_pl (plift q) (length H2) (length HX))) =
          (vars_locs (H2'++H2) (plift q))).
  eapply vars_locs_splice. rewrite plift_splice. rewrite H3.
  
  unfoldq; intuition;
  intros; destruct H as [L1 [L2 [P1 [P2 [W1 [W2 W3]]]]]]; intuition;
  unfoldq; intuition.
  
  destruct H4 as [? [? ?]].
  assert (plift p x0). eapply H0. auto.
  
  rewrite <- splicep_aux with (i := length H2)(n:= length HX)in H5.
  assert ((splice_nat x0 (length H2)(length HX)) < length (H2'++HX++H2)). eapply P2. rewrite plift_splice. auto.
  
  assert (x0 < length H1). eauto.
  assert (exists T, indexr x0 G = Some T) as TY. 
  eapply indexr_var_some. rewrite <-L1. eauto.
  destruct TY as [T ?].
  destruct H4 as [? [? ?]].
  destruct (W1 x0 T) as [vx1 [vx2 [IX1 [IX2 IV ]]]]. eauto. eauto.
  rewrite <- indexr_splice with (HX := HX) in H4.
  unfold splice_nat in H4.
  bdestruct (x0 <? length H2); intuition.
  rewrite H4 in IX2. inversion IX2. subst x1.
  eapply valt_wf in IV.  intuition. eapply H12; eauto.
  rewrite H4 in IX2. inversion IX2. subst x1.
  eapply valt_wf in IV. intuition. eapply  H12. auto. 
Qed.

Lemma envt_convert: forall M H1 H2 H2' HX G p, 
  env_type M H1 (H2' ++ H2) G (plift p) ->
  env_type1 M H1 H2 H2' HX G p.
Proof.
  intros. destruct H as [L1 [L2 [PD1 [PD2 [P1 [P2 P3]]]]]].
  repeat rewrite app_length in *. intuition.
  unfold env_type1; intuition.
  repeat rewrite app_length. intuition.
  eapply psub_splice. auto.

  destruct (P1 x T H H0) as [v1 [v2 [IX1 [IX2  VT]]]].

  bdestruct (x <? length H2); intuition.
  rewrite indexr_skips. rewrite indexr_skips.
  exists v1, v2; intuition. rewrite indexr_skips in IX2. auto. auto.
  rewrite valt_splice in VT. eapply VT.
  1,2: eapply valt_closed in VT; intuition.
  auto. rewrite app_length. lia.

  (* x >= length H2 *)
  exists v1, v2; intuition.
  eapply indexr_splice' in IX2. eapply IX2. auto.
  rewrite valt_splice in VT. eapply VT.
  1,2: eapply valt_closed in VT; intuition.
  
  rewrite plift_splice in H, H3.
  eapply splicep_aux1 in H as H5.
  eapply splicep_aux1 in H3 as H6.
  destruct H5,H6. destruct H5,H6.
  
  destruct (P3 l x x2).
  auto. subst x0. rewrite var_locs_splice in H0. eauto.
  auto. subst x1. rewrite var_locs_splice in H4. eauto.
  congruence.
Qed.

Lemma envt_convert': forall M H1 H2 H2' HX G p,
  env_type1 M H1 H2 H2' HX G p ->
  env_type M H1 (H2' ++ H2) G (plift p).
Proof.
  intros. 
  apply wf_env_type1 in H as WFE'. 
  destruct WFE' as [L1' [L2' [P1' [P2' [P3' P4']]]]].
  destruct H as [L1 [L2 [P1 [P2 [W1 [W2 W3]]]]]]; intuition.
  assert (length (H2'++H2 ) = length G) as L.
  repeat rewrite app_length in *. lia.
  unfold env_type; repeat rewrite app_length in *; intuition.  
  rewrite P2'. rewrite <- P1'. auto.
  
  destruct (W1 x T H) as [v1 [v2 [IX1 [IX2 VT]]]]; intuition.
  bdestruct (x <? length H2); intuition.
  rewrite indexr_skips in IX2; auto. rewrite indexr_skips in IX2.
  rewrite indexr_skips; auto. exists v1, v2; intuition.
  rewrite valt_splice; eauto.
  1,2: apply valt_closed in VT; intuition;
  rewrite L1 in H4; rewrite app_length; rewrite L; auto.  
  auto. rewrite app_length. lia. 

  exists v1, v2; intuition.
  assert (indexr (if x <? length H2 then x else x + length HX) (H2' ++ HX ++ H2) =
  indexr x (H2' ++ H2)). eapply indexr_splice.
  bdestruct (x <? length H2); intuition. rewrite <- H4. auto. 
  rewrite valt_splice. eapply VT.
  1,2: apply valt_closed in VT; intuition;
  rewrite L1 in H4; rewrite app_length; rewrite L; auto.  
  
  assert (splice_nat x0 (length H2) (length HX) = splice_nat x1 (length H2) (length HX)).
  eapply (W3 l (splice_nat x0 (length H2) (length HX)) (splice_nat x1 (length H2) (length HX))).

  rewrite plift_splice. rewrite splicep_aux. eauto.
  rewrite var_locs_splice. eauto.
  rewrite plift_splice. rewrite splicep_aux. eauto.
  rewrite var_locs_splice. eauto.

  unfold splice_nat in H5.
  bdestruct (x0 <? length H2); bdestruct (x1 <? length H2); lia.
Qed.   


Lemma envt_same_locs1: forall S1 S2 M H1 H2 H2' HX G p p1 l1 l2,
    store_type S1 S2 M ->
    env_type1 M H1 H2 H2' HX G p ->
    strel M l1 l2 ->
    psub (plift p1) (plift p) ->
    vars_locs H1 (plift p1) l1 <-> vars_locs (H2'++HX++H2) (splice_pl (plift p1) (length H2)(length HX)) l2.
Proof. 
  intros. eapply splice_psub with (m := length H2) (n :=length HX) in H4 as H4'.
  destruct H0 as (? & ? & ? & ? & WFX & ? & ?).
  split; intros V.
  - destruct V as (? & ? & v1 & ? & V).
    assert (exists T, indexr x G = Some T) as TT. {
      eapply indexr_var_some. rewrite <-H0. eapply indexr_var_some'. eauto. }
    destruct TT as (T & ?).
    destruct (WFX x T) as (v1' & v2 & ? & ? & ?). eauto. eauto.
    rewrite H11 in H13. inversion H13. subst v1'.
    remember H10 as H10'. clear HeqH10'. rewrite <- splicep_aux with (i := length H2)(n := length HX) in H10.
    unfold splice_nat in H10. unfoldq; intuition.  
    bdestruct (x <? length H2).
    exists x. split. auto. unfoldq; intuition. exists v2; intuition. 
    edestruct valt_same_locs; eauto. 
    exists (x+length HX). intuition. unfoldq; intuition. exists v2; intuition.
    edestruct valt_same_locs; eauto. 
    
  - destruct V as (? & ? & v2 & ? & V).
    eapply splicep_aux1 in H10. destruct H10 as [? [? ?]].
    subst x. unfold splice_nat in H11.
    assert (exists T, indexr x0 G = Some T) as TT. {
      eapply indexr_var_some. specialize (H4 x0); intuition. specialize (H6 x0); intuition. unfoldq; intuition. }
    destruct TT as (T & ?).
    destruct (WFX x0 T) as (v1 & v2' & ? & ? & ?). eauto. eauto.
    rewrite H11 in H14. inversion H14. subst v2'.
    unfoldq; intuition. exists x0; intuition. unfoldq; intuition. exists v1; intuition.
    edestruct valt_same_locs; eauto.
Qed.


Lemma separation1: forall M M' H1 H2 H2' HX G p vf1 vx1 qf q1 
    (WFE: env_type1 M H1 H2 H2' HX G p )
    (HQF1: val_qual (length1 M) H1 vf1 (plift p) qf)
    (STC: st_chain M M')
    (HQX1: val_qual (length1 M') H1 vx1 (plift p) q1)
    (PVF1: psub (val_locs vf1) (pnat (length1 M' )))
    (QSEP: psub (pand qf q1) pempty),
    psub (pand (val_locs vf1) (val_locs vx1)) pempty 
    .
Proof. 
  intros. unfoldq. intuition.
  remember WFE as WFE1; clear HeqWFE1;
  destruct WFE as [L1 [L2 [P1 [P2 [W [SEP1 SEP2]]]]]].
  + bdestruct (x <? length1 M).
  - destruct (HQF1 x). intuition.
    destruct (HQX1 x). eauto. 
    assert (x0 = x1). eapply SEP1; intuition; eauto.
    eapply QSEP. subst x0. intuition; eauto.
  - bdestruct (x <? length1 M').
    -- destruct (HQX1 x). intuition.
      (* fresh loc in vf, also occurs in vx --> can't happen *)
      assert (psub (vars_locs H1 (pone x0)) (pnat (length1 M))) as L. {
        eapply env_type_store_wf1 with (H2 := H2). eauto. eauto. unfoldq. intuition. subst x1. eauto.
      }
      assert (x < length1 M). {
        eapply L. unfoldq. exists x0. intuition.
      }
      lia.
    -- (* fresh loc in vx, bigger than vf *)
      eapply PVF1 in H0. lia.
Qed.

Lemma separation2: forall M M' H1 H2 H2' HX G p vf2 vx2 qf' q1' 
    (WFE: env_type1 M H1 H2 H2' HX G  p)
    (HQF: val_qual (length2 M) (H2'++HX++H2) vf2 (plift (splice_ql p (length H2) (length HX))) (plift (splice_ql qf' (length H2)(length HX))))
    (STC: st_chain M M')
    (HQX: val_qual (length2  M') (H2'++HX++H2) vx2 (plift (splice_ql p (length H2) (length HX))) (plift (splice_ql q1' (length H2)(length HX))))
    (PVF: psub (val_locs vf2) (pnat (length2 M')))
    (QSEP: psub (pand (plift (splice_ql qf' (length H2) (length HX)))  (plift (splice_ql q1' (length H2)(length HX)))) pempty),
    psub (pand (val_locs vf2) (val_locs vx2)) pempty 
    .
Proof. 
  intros. unfoldq. intuition.
  remember WFE as WFE1; clear HeqWFE1;
  destruct WFE as [L1 [L2 [P1 [P2 [W [SEP1 SEP2]]]]]].
  
  + bdestruct (x <? length2 M).
  - destruct (HQF x). intuition. 
    destruct (HQX x). eauto. 
    assert (x0 = x1). eapply SEP2; intuition; eauto.
    subst.  intuition.  eapply QSEP; eauto.
    
  - bdestruct (x  <? length2 M' ).
    -- destruct (HQX x). intuition.
      (* fresh loc in vf, also occurs in vx --> can't happen *)
      destruct H5. destruct H5.
      rewrite plift_splice in H5.
      eapply splicep_aux1 in H5 as H5'.
      destruct H5' as [x' [? ?]].
      rewrite H8 in H6. 
      unfold splice_nat in H6.
      bdestruct (x' <? length H2); intuition.
      assert (psub (vars_locs (H2'++HX++H2) (plift (splice_ql (qone x') (length H2)(length HX))))(pnat (length2 M))) as L. {
        eapply env_type_store_wf2. eauto.
        rewrite plift_one. unfoldq; intuition. subst. auto. 
      }
      assert (x < length2 M). {
        eapply L. unfoldq. exists x0. subst x0. 
        unfold splice_nat.
        rewrite plift_splice, plift_one. 
        unfold splice_pl.
        bdestruct (x' <? length H2); intuition.
      }
      lia.
      (* x' >= length H2*)
      unfoldq; intuition. 
      unfold splice_nat in H8.
      bdestruct (x' <? length H2); intuition.
      subst x0.
      rewrite plift_splice in P2.
      assert (psub (vars_locs (H2'++HX++H2) (plift (splice_ql p
       (length H2) (length HX))))(pnat (length2 M))) as L. {
        eapply env_type_store_wf2. eauto. intros ? ?. auto.
      }
      rewrite plift_splice in L.
      unfoldq; intuition. destruct(L x); intuition.
      destruct H6 as [? [? ?]]. unfoldq; intuition. 
      exists (x'+length HX); intuition.
      exists x0; intuition.
    -- (* fresh loc in vx, bigger than vf *)
      eapply PVF in H0. lia.
Qed.

Lemma envt_extend1: forall M H1 H2 H2' HX G v1 v2 T q p,
    env_type1 M H1 H2 H2' HX G p ->
    closed_ty (length G) T ->
    closed_ql (length G) q ->
    val_type M H1 (H2'++HX++H2) v1 v2 T (splice_ty T (length H2)(length HX)) -> (*??? H2 or G*)
    (* separation *)
    (forall x l, val_locs v1 l -> plift p x -> var_locs H1 x l -> False) ->
    (forall x l, val_locs v2 l -> (plift (splice_ql p (length H2)(length HX)) x) -> var_locs (H2'++HX++H2) x l -> False) ->
    env_type1 M (v1::H1) H2 (v2::H2') HX (T::G)(qor p (qone (length G))).
Proof. 
  intros. 
  apply wf_env_type1 in H as WFE'. 
  destruct WFE' as [L1' [L2' [P1' [P2' [P3' P4']]]]].
  destruct H as [L1 [L2 [P1 [P2 [W [SEP1 SEP2]]]]]].
  repeat split; auto.
  - simpl. eauto.
  - simpl. auto.
  - rewrite plift_or, plift_one. unfoldq. simpl. intuition.
  - rewrite <- L1'. unfoldq; intuition.
    rewrite splice_or in H. rewrite plift_or in H.
    unfoldq; intuition. eapply P4' in H7. rewrite app_length in *. simpl. auto.
    rewrite L1' in H7. rewrite <- L2' in H7.
    rewrite plift_splice in H7. rewrite plift_one in H7.
    unfold splice_pl in H7. destruct H7. destruct H. repeat rewrite app_length. lia.
    destruct H. unfoldq; intuition. repeat rewrite app_length in *. 
    assert (x = length HX + length H2' +  length H2). lia.
    subst x. simpl. lia.
    
  - intros. simpl in *.  rewrite app_length in *.   
    bdestruct (x =? (length G)); intuition; subst. inversion H. subst.
    + bdestruct (length G =? length H1); intuition.
      bdestruct (length G <? length H2); intuition.
      bdestruct (length G + length HX =? length H2' + length (HX ++ H2)); intuition.
      exists v1, v2; intuition. eapply valt_extend1; eauto. rewrite L1'. auto.
      eapply closedty_splice.  rewrite app_length. rewrite  L2'. auto.
  
   + apply indexr_var_some' in H as H'. rewrite <- L2' in H'.
     intuition. rewrite plift_or in *. unfoldq; intuition.
     destruct (W _ _ H) as [v1' [v2' ?]]; eauto.
     bdestruct (x <? length H2); bdestruct (x =? length H1); bdestruct (x =? length H2' + length (HX++H2)); intuition.
     
     exists v1', v2'. intuition.  
     eapply valt_closed in H15 as H15'.
     eapply valt_extend1 in H15. eauto.
     intuition.  intuition.
     
     bdestruct ( x + length HX =? length H2' + length (HX ++ H2)); intuition.
     exists v1', v2'. intuition. 
     eapply valt_closed in H15 as H15'.
     eapply valt_extend1; eauto.  intuition. intuition.

     rewrite plift_one in H9. unfoldq. rewrite <- L2' in H9. intuition.
  
  - intros. rewrite plift_or in *. rewrite plift_one in *. 
    inversion H; inversion H8.
    + eapply SEP1; eauto.
      eapply var_locs_shrink. eauto. eapply P1; eauto.
      eapply var_locs_shrink. eauto. eapply P1; eauto.
    + destruct (H5 x0 l); eauto.
      assert (x1 = length H1). unfoldq; intuition.
      subst x1. eapply var_locs_head; eauto.
      eapply var_locs_shrink. eauto. eapply P1; eauto.
    + destruct (H5 x1 l); eauto.
      assert (x0 = length H1). unfoldq. intuition.
      subst x0. eapply var_locs_head; eauto.
      eapply var_locs_shrink. eauto. eapply P1; eauto.
    + unfoldq. lia.
  - intros. rewrite splice_or in *. rewrite plift_or in *.
    assert ((splice_ql (qone (length G))(length H2)(length HX))
      = (qone (length (H2'++HX++H2)))) as A.
    eapply spliceq_one; eauto. rewrite A in *. rewrite plift_one in *.
    inversion H; inversion H8.
    + eapply SEP2; eauto.
      eapply var_locs_shrink. eauto. eapply P2; eauto.
      eapply var_locs_shrink. eauto. eapply P2; eauto.
    + destruct (H6 x0 l); eauto.
      assert (x1 = length (H2'++HX++H2)). 
      unfoldq; intuition.
      subst x1. eapply var_locs_head; eauto.
      eapply var_locs_shrink. eauto. eapply P2; eauto.
    + destruct (H6 x1 l); eauto.
      assert (x0 = length (H2'++HX++H2)). unfoldq. intuition.
      subst x0. eapply var_locs_head; eauto.
      eapply var_locs_shrink. eauto. eapply P2; eauto.
    + unfoldq. lia.
Qed.

Lemma envt_tighten1: forall M H1 H2 H2' HX G p p',
    env_type1 M H1 H2 H2' HX G p ->
    psub (plift p') (plift p) ->
    env_type1 M H1 H2 H2' HX G p'.
Proof.
  intros. apply wf_env_type1 in H as H'.
  destruct H' as [L1' [L2' [PD1 [PD2 [PD3 PD4]]]]].
  destruct H as [L1 [L2 [P1 [P2 W]]]].
  repeat split; auto.
  - unfoldq. intuition.
  - eapply psub_splice; eauto. rewrite PD2. rewrite <- PD1. unfoldq; intuition.
  - intros.
    destruct W as [W ?].
    destruct (W x T); eauto. 
  - intros.
    destruct W as [? [W1 W2]].
    eauto.
  - intros.
    destruct W as [? [W1 W2]].
    eapply splice_psub  with (m := (length H2))(n:= length HX) in H0; eauto.
    eapply W2; eauto.
    rewrite plift_splice in *.
    unfoldq; intuition.
    rewrite plift_splice in *.
    unfoldq; intuition.
Qed.

Lemma envt_store_change1: forall M M' H1 H2 H2' HX G p,
    env_type1 M H1 H2 H2' HX G p ->
    st_chain_partial M M' (vars_locs H1 (plift p)) (vars_locs (H2'++HX++H2) (splice_pl (plift p) (length H2)(length HX))) ->
    st_chain_partial2 M' M (vars_locs H1 (plift p)) (vars_locs (H2'++HX++H2) (splice_pl (plift p) (length H2)(length HX))) ->
    length2 M <= length2 M' ->
    env_type1 M' H1 H2 H2' HX G p.
Proof. 
  intros. destruct H as [L1 [L2 [P1 [P2 [W1 [W2 W3]]]]]]. 
  repeat split; auto. intros.
  destruct (W1 _ _  H H5) as [vx1 [vx2 [IH1 [IH2 HVX]]]]; intuition.
  exists vx1, vx2; intuition.
  eapply valt_store_change in HVX; eauto.
  eapply stchain_tighten. eauto.
  intros ? ?. exists x. intuition. exists vx1. intuition.
  intros ? ?. remember H5 as H5'. clear HeqH5'. rewrite <- splicep_aux with (i := length H2)(n := length HX) in H5.
  unfold splice_nat in H5. unfoldq; intuition.  
  bdestruct (x <? length H2).
  exists x. split. auto. unfoldq; intuition. exists vx2; intuition.
  exists (x+length HX). intuition. unfoldq; intuition. exists vx2; intuition.
  
  eapply stchain_tighten'. eauto.
  intros ? ?. exists x. intuition. exists vx1. intuition.
  intros ? ?. remember H5 as H5'. clear HeqH5'. rewrite <- splicep_aux with (i := length H2)(n := length HX) in H5.
  unfold splice_nat in H5. unfoldq; intuition.  
  bdestruct (x <? length H2).
  exists x. split. auto. unfoldq; intuition. exists vx2; intuition.
  exists (x+length HX). intuition. unfoldq; intuition. exists vx2; intuition.
Qed.


Lemma envt_store_extend1: forall M M' H1 H2 H2' HX G p,
    env_type1 M H1 H2 H2' HX G p ->
    st_chain M M' ->
    env_type1 M' H1 H2 H2' HX G p.
Proof.
  intros. destruct H as [L1 [L2 [P1 [P2 [W1 [W2 W3]]]]]]. 
  repeat split; auto. intros.
  destruct (W1 _ _  H H3) as [vx1 [vx2 [IH1 [IH2 HVX]]]]; intuition.
  exists vx1, vx2; intuition.
  eapply valt_store_extend in HVX; eauto.
  eapply st_mono2 in H0. auto.
Qed.


Lemma envt_extend_all1: forall M M1 H1 H2 H2' HX G p qf vx1 vx2 T1 q1,
    env_type1 M H1 H2 H2' HX G p ->
    st_chain_partial M M1 (vars_locs H1 (pand (plift p) (plift qf))) (vars_locs (H2'++HX++H2) (splice_pl (pand (plift p) (plift qf)) (length H2)(length HX))) ->
    st_chain_partial2 M1 M (vars_locs H1 (pand (plift p) (plift qf))) (vars_locs (H2'++HX++H2) (splice_pl (pand (plift p) (plift qf)) (length H2)(length HX))) ->
    length2 M <= length2 M1 ->
    val_type M1 H1 (H2'++HX++H2) vx1 vx2 T1 (splice_ty T1 (length H2)(length HX)) ->
    psub (pand (vars_locs H1 (pand (plift p) (plift qf))) (val_locs vx1)) pempty ->
    psub (pand (vars_locs (H2'++HX++H2) (splice_pl (pand (plift p)(plift qf)) (length H2)(length HX))) (val_locs vx2)) pempty ->
    closed_ty (length G) T1 ->
    closed_ql (length G) q1 ->
    env_type1 M1 (vx1 :: H1) H2 (vx2 :: H2') HX (T1 :: G) 
          (qor (qand p qf) (qone (length G))).
Proof. 
  intros. 

  eapply envt_extend1; eauto.
  eapply envt_store_change1.
  eapply envt_tighten1.
  eauto.
  rewrite plift_and. intros ? ?. unfoldq. intuition.
  rewrite plift_and. auto. 
  rewrite plift_and. auto.
  auto.
  
  (* now prove separation on the first *) 
  intros.

  unfoldq. unfoldq.
  eapply H6. intuition.
  exists x. intuition. rewrite plift_and in H11. unfoldq; intuition.
  rewrite plift_and in H11. unfoldq; intuition.
  eauto. auto.

  (* now prove separation on the second *) 
  intros.

  assert (psub (pand (plift p) (plift qf)) (plift p) /\
          psub (pand (plift p) (plift qf))(plift qf)).
  unfoldq; intuition.
  destruct H13.
  eapply splice_psub with (m := length H2) (n:= length HX) in H13.
  eapply splice_psub with (m := length H2) (n:= length HX) in H14.
  
  unfoldq. unfoldq.
  eapply H7. intuition.
  exists x. intuition.
  1,2: repeat rewrite plift_splice in *.
  1,2: rewrite plift_and in *; 
  unfoldq; intuition.
  eapply H12. auto. 
Qed.

(* compatability lemmas for splice *)

Lemma bi_vtrue3: forall S1 S2 M H1 H2 p1 p2 q1 q2,
  store_type S1 S2 M ->  
  exp_type1 S1 S2 M H1 H2 ttrue ttrue S1 S2 M (vbool true) (vbool true) TBool TBool p1 p2 q1 q2 pempty pempty.
Proof.
  intros.
  split.
  exists 0. intros. destruct n. lia. simpl. eauto.
  split.
  exists 0. intros. destruct n. lia. simpl. eauto.
  split.
  intros ? ?. intros. auto.
  split.
  intros ? ?. intros. auto.
  split.
  eapply st_refl.
  (* store_typing*)
  split. auto.
  simpl. repeat split. 
  apply valq_bool. apply valq_bool.
Qed.

Lemma bi_vfalse3: forall S1 S2 M H1 H2 p1 p2 q1 q2,
  store_type S1 S2 M -> 
  exp_type1 S1 S2 M H1 H2 tfalse tfalse S1 S2 M (vbool false) (vbool false) TBool TBool p1 p2 q1 q2 pempty pempty.
Proof.  
  intros.  remember H as H''. clear HeqH''.
  destruct H as [SL1 [SL2  [SP1 SP2]]]. 
  split.
  exists 0. intros. destruct n. lia. simpl. eauto.
  split.
  exists 0. intros. destruct n. lia. simpl. eauto.
  split.
  intros ? ? ? ?. auto. 
  split.
  intros ? ? ? ?. auto. 
  split.
  eapply st_refl.
  (* store_typing*)
  split. auto.

  simpl. repeat split.
  apply valq_bool. apply valq_bool.
Qed.


Lemma bi_var_splice: forall G M H1 H2 H2' S1 S2 HX p x T1
  (WFE: env_type M H1 (H2'++H2) G p),
  indexr x G = Some T1 ->
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
      (plift (qone x)) (plift (splice_ql (qone x) (length H2) (length HX)))
      (plift qempty) (plift qempty). (* should work for any e ? *)
Proof.
  intros. rewrite plift_one. rewrite plift_empty. 
  destruct WFE as [L1 [L2 [P1 [P2 [W [SEP1 SEP2]]]]]].
  eapply W in H; auto. 
  destruct H as [v1 [v2 [IX1 [IX2 VT]]]].
  exists S1, S2, M, v1, v2. 
  split. (* teval 1 *)
  exists 0. intros. destruct n. lia. simpl. rewrite IX1. eauto.
  split. (* teval 2 *)
  exists 0. intros. destruct n. lia. simpl.
  assert ((S2, Some (indexr (splice_nat x (length H2) (length HX))
        (H2' ++ HX ++ H2))) = (S2, Some (Some v2))) as R. 
  rewrite indexr_splice. rewrite IX2. eauto. eapply R.
  split. intros ? ? ? ?. auto.
  split. intros ? ? ? ?. auto. 
  split. eapply st_refl.
  split. auto.
  split. (* valt *)
  eapply valt_splice in VT. eauto.
  1,2: eapply valt_closed in VT; intuition.
  split.
  
  (* first qual *)
  unfoldq. unfoldq. intuition.  exists x. intuition.
  exists v1; intuition.
  
  (* 2nd qual *)
  unfoldq. unfoldq. intuition. exists (splice_nat x (length H2) (length HX)).
  repeat rewrite plift_splice. rewrite plift_one.
  repeat rewrite splicep_aux. rewrite indexr_splice. 
  intuition. 
  exists v2. eauto.
  
Qed.



Lemma bi_tref3: forall e1 e2 M M' S1 S2 S1' S2' H1 H2 v1 v2 p q e p' q' e',
  store_type S1 S2 M ->
  exp_type1 S1 S2 M H1 H2 e1 e2 S1' S2' M' v1 v2 TBool TBool p p' q q' e e'->
  exists S1'' S2'' M''  v1 v2,
  exp_type1 S1 S2 M H1 H2 (tref e1) (tref e2) S1'' S2''  M'' v1 v2 (TRef TBool) (TRef TBool) p p' q q' e e'.
Proof. 
  intros. 
  destruct H0 as [IE1 [IE2 [EFF1 [EFF2 [STC [ST [HV [HQ1 HQ2]]]]]]]].
  remember ST as ST'. clear HeqST'.
  destruct ST as [SL1 [SL2 [SP3 [SP4 SP5]]]].
  remember HV as  HV'. clear HeqHV'.
  remember ((1, 1, fun l1 l2 => l1 = length S1' /\ l2 = length S2')) as vt.
  destruct v1; destruct v2; try solve [inversion HV].
  exists ((vbool b)::S1'), ((vbool b0)::S2'),  (st_extend M').
  exists (vref (length S1')), (vref (length S2')).

  split.

  (* 1st term *)
  destruct IE1 as [n1 IE1].
  exists (S n1). intros. destruct n. lia. simpl. rewrite IE1.  auto. lia.

  split.
  (* 2nd term *)
  destruct IE2 as [n2 IE2].
  exists (S n2). intros. destruct n. lia. simpl. rewrite IE2. auto. lia.
  
  split.
  eapply se_trans. eauto. intros ? ?. intros. eapply indexr_extend1 in H3. eapply H3.
  
  split.
  eapply se_trans. eauto. intros ? ?. intros. eapply indexr_extend1 in H3. eapply H3.
  
  split. eapply st_trans. eauto. eapply stchain_extend.

  (* store_typing *)
  split.
  subst vt. eapply storet_extend; eauto.
   
  split.
  (* result type *)
  simpl. intuition.
  unfold length1, st_extend. simpl. lia.
  unfold length2, st_extend. simpl. lia.
  split.
  rewrite SL1. eapply valq_fresh1; eauto.
  
  rewrite SL2. eapply valq_fresh2; eauto.
  
Qed.


Lemma bi_tget3: forall t S1 S2 S1' S2' M M' G H1 H2 HX H2' p q e v1 v2
  (WFE: env_type1 M H1 H2 H2' HX G p),
  exp_type1 S1 S2 M H1 (H2'++HX++H2) t (splice_tm t (length H2)(length HX)) 
    S1' S2' M' v1 v2 (TRef (TBool)) (TRef (TBool)) 
    (plift p) (plift (splice_ql p (length H2)(length HX))) 
    (plift q) (plift (splice_ql q (length H2)(length HX))) 
    (plift e) (plift (splice_ql e (length H2)(length HX))) ->
  exists S1'' S2'' M'' v3 v4,
  exp_type1 S1 S2 M H1 (H2'++HX++H2) (tget t) (tget (splice_tm t (length H2)(length HX)))  S1'' S2''  M'' v3 v4 TBool TBool 
     (plift p) (splice_pl (plift p) (length H2)(length HX)) 
     pempty pempty 
    (plift (qor e q)) (plift (splice_ql (qor e q)(length H2)(length HX))).
Proof. 
  intros.  
  destruct H as [EV1 [EV2 [EFF1 [EFF2 [HSTC [HST [HV [HQ1 HQ2]]]]]]]].
  destruct v1; destruct v2; try solve [inversion HV]. simpl in HV.
  
  destruct HV as [HT [? [LS1 [LS2 VT]]]].
  remember HST as HST'. clear HeqHST'.
  destruct HST as [STL1 [STL2 [SP1 [SP2 SP3]]]].

  destruct (SP1 i i0 VT) as [b1 [b2 [IY1 [IY2 EQ]]]]. 

  exists S1', S2', M', (vbool b1), (vbool b2). 
  split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 8: split. 
  + destruct EV1 as [n1 IW1].
    exists (S n1). intros. destruct n. lia. simpl.
    rewrite IW1. rewrite IY1. eauto. lia.
  + destruct EV2 as [n1 IW2].
    exists (S n1). intros. destruct n. lia. simpl.
    rewrite IW2. rewrite IY2. eauto. lia.
  + (* effects 1 *)
    auto.
    
  + (* effects 2 *)
    rewrite plift_splice in EFF2. auto.
  + eauto. 
  + auto.
  + subst b2.
    constructor; eauto.
    
  + eapply valq_bool.
  + eapply valq_bool.   
Qed.

Lemma bi_tput3: forall S1 S2 M H1 H2 H2' HX t1 t2 S1' S2' M' M'' S1'' S2'' v1 v2 v3 v4 p q1 q2 e1 e2  
 (ST: store_type S1 S2 M)
 (E1: exp_type1 S1 S2 M H1  (H2'++HX++H2) t1 (splice_tm t1 (length H2) (length HX)) S1' S2' M' v1 v2 (TRef TBool) (TRef TBool) (plift p) (plift (splice_ql p (length H2) (length HX)))  (plift q1) (plift (splice_ql q1 (length H2) (length HX))) (plift e1) (plift (splice_ql e1 (length H2) (length HX))))
 (E2: exp_type1 S1' S2' M' H1 (H2'++HX++H2) t2 (splice_tm t2 (length H2) (length HX)) S1'' S2'' M'' v3 v4 TBool TBool (plift p) (plift (splice_ql p (length H2) (length HX))) (plift q2) (plift (splice_ql q2 (length H2) (length HX))) (plift e2) (plift (splice_ql e2 (length H2) (length HX)))),
 exists S1''' S2''' M''' v5 v6,
 exp_type1 S1 S2 M H1 (H2'++HX++H2) (tput t1 t2) (tput (splice_tm t1 (length H2) (length HX)) (splice_tm t2 (length H2) (length HX))) 
  S1''' S2'''  M''' v5 v6 TBool TBool 
  (plift p) (splice_pl (plift p) (length H2) (length HX))
  pempty pempty 
  (plift (qor e1 (qor e2 q1))) (plift (splice_ql (qor e1 (qor e2 q1)) (length H2) (length HX))).
Proof. 
  intros. 
  destruct E1 as [IE1 [IE2 [EFF1 [EFF2 [STC1 [ST1 [HV [HQ1 HQ2]]]]]]]].
  destruct v1; destruct v2; try solve [inversion HV]. simpl in HV.
  destruct HV as [HT [LS1 [LS2 VT]]].
  remember ST1 as ST1'. clear HeqST1'.
  destruct ST1 as [STL1 [STL2 [SP1 [SP2 SP3]]]].

  destruct E2 as [IE3 [IE4 [EFF3 [EFF4 [STC2 [ST2 [HV1 [HQ3 HQ4 ]]]]]]]].
  destruct v3; destruct v4; try solve [inversion HV1]. simpl in HV1.
  subst b0.
  remember ST2 as ST2'. clear HeqST2'.
  destruct ST2 as [STL3 [STL4 [SP4 [SP5 SP6]]]].

  exists (update S1'' i (vbool b)), (update S2'' i0 (vbool b)).
  exists M''.
  exists (vbool true), (vbool true).

  split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 8: split.
  (* first one *)
  destruct IE1 as [n1 IE1].
  destruct IE3 as [n3 IE3].
  exists (S(n1 + n3)). intros. destruct n. intuition.
  simpl. rewrite IE1. rewrite IE3.
  assert (i < length S1''). 
  rewrite STL3. eapply st_mono1'; eauto.
  apply indexr_var_some in H0. destruct H0. rewrite H0. auto. lia. lia.

  
  destruct IE2 as [n2 IE2].
  destruct IE4 as [n4 IE4].
  exists (S(n2 + n4)). intros. destruct n. intuition.
  simpl. rewrite IE2. rewrite IE4. 
  assert (i0 < length S2''). 
  rewrite STL4. eapply st_mono2'; eauto. lia.
  apply indexr_var_some in H0. destruct H0. rewrite H0. auto. lia. lia.

  (* effects  *)
  assert (length S1 = length1 M). destruct ST as (? & ? & ?). eauto.
  assert (length S2 = length2 M). destruct ST as (? & ? & ?). eauto.
  intros ? ? ? ?.
   bdestruct (i =? l). { subst. destruct (HQ1 l).
  rewrite val_locs_ref. eapply indexr_var_some' in H4. unfoldq. intuition.
  destruct H3. unfoldq; intuition. exists x; intuition.
  }{ rewrite update_indexr_miss. eauto. eauto. 
  }


  (* effects  *)
  assert (length S1 = length1 M). destruct ST as (? & ? & ?). eauto.
  assert (length S2 = length2 M). destruct ST as (? & ? & ?). eauto.
  intros ? ? ? ?.
   bdestruct (i0 =? l). { subst. destruct (HQ2 l).
  rewrite val_locs_ref. eapply indexr_var_some' in H4. unfoldq. intuition.
  destruct H3. unfoldq; intuition. exists x; intuition. rewrite plift_splice in H5. auto.
  }{ rewrite update_indexr_miss. rewrite plift_splice in *. eauto. eauto. 
  }

  eapply st_trans; eauto. 

  (* store typing *)
  eapply storet_update; eauto. eapply valt_store_extend; eauto. 
  simpl. intuition.
  eapply st_mono2 in STC2. auto.
  simpl. eauto. 
  
  constructor; intuition.
  

    (* valq *)
  eapply valq_bool. eapply valq_bool.
Unshelve. all: auto.
Qed.


Lemma bi_tapp3: forall M M' M'' S1 S2 S1' S2' S1'' S2'' vf1 vf2 vx1 vx2 G H1 H2 H2' HX ef1 ex1 T1 T2 p qf ef q1 q2 e1 e2 
   (WFE: env_type1 M H1 H2 H2' HX G p)
   (ST: store_type S1 S2 M)
   (IEF: exp_type1 S1 S2 M H1 (H2'++HX++H2) ef1 (splice_tm ef1 (length H2)(length HX)) S1' S2' M' vf1 vf2
        (TFun T1 T2 q2 e2) 
        (splice_ty (TFun T1 T2 q2 e2)(length H2)(length HX)) 
        (plift p) (plift (splice_ql p (length H2)(length HX))) 
        (plift qf) (plift (splice_ql qf (length H2)(length HX))) 
        (plift ef) (plift (splice_ql ef (length H2)(length HX))))  
   (IEX: exp_type1 S1' S2' M' H1 (H2'++HX++H2) ex1 (splice_tm ex1 (length H2)(length HX)) S1'' S2'' M'' vx1 vx2 T1 (splice_ty T1 (length H2)(length HX)) (plift p ) (plift (splice_ql p (length H2)(length HX))) (plift q1) (plift (splice_ql q1 (length H2)(length HX))) (plift e1) (plift (splice_ql e1 (length H2)(length HX))))  
   (QSEP: psub (pand (plift qf) (plift q1)) pempty)
   (QSEP': psub (pand (plift (splice_ql qf (length H2)(length HX))) (plift (splice_ql q1 (length H2)(length HX)))) pempty)
   (Q2: psub (plift q2) (plift p))
   (Q2': psub (plift (splice_ql q2 (length H2)(length HX))) (plift (splice_ql p (length H2)(length HX))))
   (E2: psub (plift e2) (plift p))
   (E2': psub (plift (splice_ql e2 (length H2)(length HX))) (plift (splice_ql p (length H2)(length HX)))),
   exists S1''' S2''' M''' v5 v6,
   exp_type1 S1 S2 M H1 (H2'++HX++H2) (tapp ef1 ex1)(splice_tm (tapp ef1 ex1) (length H2)(length HX)) 
        S1''' S2''' M''' v5 v6 T2 (splice_ty T2 (length H2)(length HX)) 
        (plift p) (plift (splice_ql p (length H2)(length HX))) 
        (por (plift q2) (plift q1)) (por (plift (splice_ql q2 (length H2)(length HX))) (plift (splice_ql q1 (length H2)(length HX)))) 
        (por (plift ef) (por (plift e1) (por (plift q1) (plift e2)))) 
        (por (plift (splice_ql ef (length H2)(length HX))) 
             (por (plift (splice_ql e1 (length H2)(length HX))) (por (plift (splice_ql q1 (length H2)(length HX))) (plift (splice_ql e2 (length H2)(length HX))))))
       .
Proof.  
  intros. 
  destruct IEF as [IEF1 [IEF2 [EFF1 [EFF2 [SC1 [ST1 [HVF [HQF1 HQF2]]]]]]]].
  destruct IEX as [IEX1 [IEX2 [EFF3 [EFF4 [SC2 [ST2 [HV2 [HQX1 HQX2 ]]]]]]]].

  destruct vf1; destruct vf2; try solve [inversion HVF]; simpl in HVF; intuition.
  rename H13 into HVF.
  
   
  assert ( psub (pand (val_locs (vabs l q t)) (val_locs vx1)) pempty). { 
    eapply separation1; eauto. 
  }
  assert ( psub (pand (val_locs (vabs l0 q0 t0)) (val_locs vx2)) pempty). { 
    eapply separation2; eauto.
  }
  
  intuition.

  destruct (HVF S1'' S2'' M'' vx1 vx2) as [S1'''[S2''' [M''' [r1 [r2 [IAPP1 [IAPP2 [STCY  [STY [EFF5 [EFF6  [IVALY [HQY1 HQY2]]]]]]]]]]]]]; auto.

  eapply stchain_tighten; eauto. eapply SC2.
  eapply stchain_tighten'; eauto. eapply SC2.
  eapply st_mono2 in SC2. auto.
  
  exists S1''', S2'''.
  exists M'''.

  exists r1. exists r2.

  split.
  (* 1st function *)
  destruct IEF1 as [n1 IEF1].
  destruct IEX1 as [n2 IEX1].
  destruct IAPP1 as [n3 IAPP1].
  exists (S (n1+n2+n3)). 
  (* - forall greater fuel *)
  intros. destruct n. lia.
  (* - result computes *)
  simpl. rewrite IEF1. rewrite IEX1. rewrite IAPP1. auto. lia. lia. lia.
  
  split.
  (* 2nd function *)
  destruct IEF2 as [n1 IEF2].
  destruct IEX2 as [n2 IEX2].
  destruct IAPP2 as [n3 IAPP2].
  exists (S (n1+n2+n3)). 
  (* - forall greater fuel *)
  intros. destruct n. lia.
  (* - result computes *)
  simpl. rewrite IEF2. rewrite IEX2. rewrite IAPP2. auto. lia. lia. lia.
  
  split.
  (* effect1 *)
  intros ? ? ? ?. rewrite EFF5. eauto. 2: eauto.
  assert (l1 < length1 M). { eapply indexr_var_some' in H15. destruct ST as (L & ?). lia. }
  intros ?. eapply H14. destruct H17. {
    destruct (HQF1 l1). unfoldq. intuition.
    exists x. unfoldq. intuition.
  } {
    destruct (HQX1 l1). unfoldq. intuition. eapply st_mono1'; eauto.
    exists x. unfoldq. intuition.
  }

  split.
  (* effect2*)
  intros ? ? ? ?. rewrite EFF6. eauto. 2: eauto.
  assert (l1 < length2 M). { eapply indexr_var_some' in H15. destruct ST as (L & ?). lia. }
  intros ?. eapply H14. destruct H17. {
    destruct (HQF2 l1). unfoldq. intuition.
    exists x. unfoldq. intuition.
  } {
    destruct (HQX2 l1). unfoldq. intuition. eapply st_mono2'; eauto.
    exists x. unfoldq. intuition.
  }

  split.
   eapply st_trans. eapply st_trans. eauto. eauto. eauto. 
  
  (* store typing *)
  split. auto.
 
  (* result type *)
  split. auto.
  
  split.
  (* 1st qual *)
  assert (val_qual (length1 M) H1 r1 (plift p) (pand (plift p) (por (plift q2) (plift q1)))) as A. {
    remember (vabs l q t) as vf1.
    unfold val_qual.
    rewrite <-(vars_locs_dist_and11 M H1 H2 H2' HX G p); eauto. 
    2: { intros ? ?. auto. }
    2: { intros ? ?. unfoldq. intuition. }
     
    unfoldq. intros.
    destruct (HQY1 x). intuition. eapply st_mono1'; eauto. eapply st_mono1'; eauto. (* XXX *)
    - (* part of function *)
      destruct (HQF1 x). intuition.
      destruct H15. destruct H15.
      split.
      exists x0. intuition. unfoldq. intuition.
      exists x1. intuition. 
  - (* part of argument *)
    destruct (HQX1 x). intuition. eapply st_mono1'; eauto. (* XXX *) split.
    exists x0. intuition.
    exists x0. intuition.
  }
  unfoldq. intuition.
  destruct (A x). intuition.
  exists x0. intuition.

  
  (* 2nd qual *)
  
  assert (val_qual (length2 M) (H2'++HX++H2) r2 (plift (splice_ql p (length H2)(length HX))) (plift (splice_ql (qand p (qor  q2 q1)) (length H2)(length HX)))) as B. {
    remember (vabs l0 q0 t0) as vf2.
    unfold val_qual. 
    rewrite <-(vars_locs_dist_and22 M H1 H2 H2' HX G p); eauto. 
  2: {unfoldq. intuition. }
  2: { rewrite splice_and. rewrite splice_qor.
      unfoldq. intuition. rewrite plift_and, plift_or in H14. unfoldq; intuition. }
 
  unfoldq. intros.
  destruct (HQY2 x). intuition. eapply st_mono2'; eauto. eapply st_mono2'; eauto. (* XXX *)
  - (* part of function *)
    destruct (HQF2 x). intuition.
    destruct H15. destruct H15.
    split.
    exists x0. intuition. unfoldq. intuition.
    exists x1. intuition.  rewrite splice_and. rewrite splice_qor. rewrite plift_and, plift_or.
      unfoldq. intuition.  
  - (* part of argument *)
    destruct (HQX2 x). intuition. eapply st_mono2'; eauto. (* XXX *) split.
    exists x0. intuition.
    exists x0. intuition. rewrite splice_and, splice_qor, plift_and, plift_or. unfoldq; intuition.
  } 
  unfoldq. intuition.
  destruct (B x). intuition.
  exists x0. intuition. 
  repeat rewrite plift_splice in *. 
  rewrite plift_and in H19. rewrite plift_or in H19.
  rewrite splice_pand in H19. rewrite splice_por in H19.
  unfoldq; intuition.
Qed.  

Lemma bi_tabs3: forall H1 H2 H2' HX S1 S2 M G t1 T1 T2 p q2 qf e2
  (WFE: env_type1 M H1 H2 H2' HX G p)
  (ST: store_type S1 S2 M)
  (EXP:  forall S1' S2' M' vx1 vx2,
      val_type M' H1 (H2'++HX++H2) vx1 vx2 T1 (splice_ty T1 (length H2)(length HX)) ->
      psub (pand (vars_locs H1 (pand (plift p)(plift qf))) (val_locs vx1)) pempty ->
      psub (pand (vars_locs (H2'++HX++H2) (plift (splice_ql (qand p qf) (length H2)(length HX)))) (val_locs vx2)) pempty  -> 
      env_type  M' (vx1::H1) (vx2::H2' ++ H2)(T1::G) (por (pand (plift p) (plift qf))(pone (length G))) ->
      store_type S1' S2'  M' ->
      exists S1'' S2'' M'' v1 v2,
        exp_type1 S1' S2' M' (vx1:: H1) ((vx2:: H2')++HX++H2) t1 (splice_tm t1 (length H2)(length HX)) S1'' S2'' M'' v1 v2 T2  (splice_ty T2 (length H2)(length HX))
        (plift (qor (qand p qf)(qone  (length G)))) 
        (plift (qor (splice_ql (qand p qf) (length H2) (length HX)) (splice_ql (qone  (length G)) (length H2)(length HX)) )) 
        (plift (qor q2 (qone (length G))))
        (plift (qor (splice_ql q2 (length H2)(length HX)) 
                (splice_ql (qone (length G)) (length H2)(length HX)))) 
        (plift (qor e2 (qone (length G)))) 
        (plift (qor (splice_ql e2 (length H2)(length HX)) 
                (splice_ql (qone (length G)) (length H2)(length HX))))
  )
  (T1CL: closed_ty (length G) T1)
  (T2CL: closed_ty (length G) T2)
  (HQ2: (psub (plift q2) (pdom G)))
  (HE2: (psub (plift e2) (pdom G)))
  (HCLQF: closed_ql (length G) qf), 
  exists S1'' S2'' M'' v1'' v2'',
  exp_type1 S1 S2 M H1 (H2'++HX++H2) 
      (tabs (qand p qf) t1) (splice_tm (tabs (qand p qf) t1) (length H2) (length HX))
      S1'' S2'' M''  v1'' v2'' 
      (TFun T1 T2 q2 e2 ) (splice_ty (TFun T1 T2 q2 e2) (length H2)(length HX))
      (plift p) 
      (plift (splice_ql p (length H2) (length HX))) 
      (plift qf) (plift (splice_ql qf (length H2)(length HX))) 
      pempty pempty.
Proof.  
  intros. 
  apply wf_env_type1 in WFE as WFE'. 
  destruct WFE' as [L1 [L2 [P1 [P2 [P3 P4]]]]].
  remember ST as ST'. clear HeqST'.
  destruct ST as [SL1 [SL2 [SP1 [SP2 SP3]]]].
  rewrite plift_or in *. 
  exists S1, S2, M.
  exists (vabs H1 (qand p qf) t1). 
  exists (vabs (H2' ++ HX ++ H2) (splice_ql (qand p qf) (length H2) (length HX)) (splice_tm t1 (length H2) (length HX))).
  split.
  
  (* 1st *)
    exists 0.  intros. destruct n. lia. simpl. eauto.
  split.
   (* 2nd *)
    exists 0.  intros. destruct n. lia. simpl. auto.
  split.
  intros ? ? ? ?. eauto.
  split.
  intros ? ? ? ?. eauto.
  split. eapply st_refl.
  split.
   (* store typing *)  
   auto.

   assert (length (H2'++HX ++ H2) = length G + length HX) as LL.
   repeat rewrite app_length in *. lia.
   
   (* results *)
   repeat split.
   rewrite L1. auto.
   rewrite L1. auto.
   eapply closedty_splice; eauto. rewrite L2. auto.
   eapply closedty_splice; eauto. rewrite L2. auto.
   rewrite P1. unfoldq; intuition.
   eapply psub_splice. rewrite P2. auto.
   rewrite P1. auto.
   eapply psub_splice. rewrite P2. auto.
   
   rewrite val_locs_abs. 
   eapply env_type_store_wf1. eapply WFE. auto.
   intros ? ?. rewrite plift_and in H. unfoldq; intuition.
   rewrite val_locs_abs.
   eapply env_type_store_wf2. eauto. auto.
   intros ? ?. rewrite plift_and in H. unfoldq; intuition.

   
   (* strel same locs *)
   
   rewrite val_locs_abs, val_locs_abs. rewrite plift_splice. edestruct envt_same_locs1; eauto. rewrite plift_and. 
   unfoldq; intuition.
   
   rewrite val_locs_abs, val_locs_abs. rewrite plift_splice. edestruct envt_same_locs1; eauto.
   rewrite plift_and. unfoldq; intuition. 
   
   intros.
      
   repeat rewrite val_locs_abs in H, H0. 
   rewrite plift_splice, plift_and in H, H0.
   rewrite val_locs_abs in H6, H7.
   rewrite plift_splice in H7. 
   rewrite plift_and in H6, H7.
   assert (env_type1  M'
            (vx1 :: H1) H2 (vx2 :: H2') HX (T1 :: G)
            (qor (qand p qf) (qone (length G)))) as WFE'.
 
   eapply envt_extend_all1 in WFE; eauto. 
      
   
   destruct (EXP S1' S2' M' vx1 vx2 H5) as [S1'' [S2'' [M'' [vy1 [vy2 IEY]]]]]; intuition.
   rewrite plift_splice, plift_and. auto.
   
   eapply envt_convert' in WFE'. 
   replace (vx2::H2'++H2) with ((vx2::H2')++H2). rewrite plift_or, plift_and, plift_one in WFE'. auto. simpl. auto.
      
   destruct IEY as [IEY1 [IEY2 [YEFF1 [YEFF2 [YSTC [YST [IVY [IYQ1 IYQ2 ]]]]]]]].
   
   rewrite plift_splice, plift_or, plift_one in *.
   exists S1'', S2'', M'', vy1, vy2. intuition.

   (* store preserve *)
   intros ? ? PV ?. eapply YEFF1. intros VL. eapply PV.
   destruct VL as (? & VL & ?).
   destruct VL. {
     left. rewrite val_locs_abs, plift_and. exists x. split. rewrite plift_and in H10. eauto. eapply var_locs_shrink. eauto. eapply (wf_env_type1 _ _ _ _ _ _ _ WFE). rewrite plift_and in H10. unfoldq. intuition.     
   } {
     right. destruct H9. replace x with (length H1) in H9.
     rewrite indexr_head in H9. intuition. congruence.
     unfoldq. intuition.
   }
   eauto.
  
   
   intros ? ? PV ?. eapply YEFF2. intros VL. eapply PV.
   repeat rewrite plift_splice, plift_and, plift_one in VL.
   destruct VL as (? & VL & ?).
   destruct VL. {
     left. rewrite val_locs_abs, plift_splice, plift_and. exists x. split. rewrite plift_splice, plift_and in H10. eauto. eapply var_locs_shrink. eauto. eapply (wf_env_type1 _ _ _ _ _  _ _ WFE). rewrite splice_and in H10. rewrite plift_and in H10. unfoldq. intuition.     
   } {
     right. destruct H9.  
     replace ((vx2 :: H2') ++ HX ++ H2) with (vx2:: H2' ++ HX ++ H2) in H9.
     replace x with (length (H2'++HX++H2)) in H9.
     rewrite indexr_head in H9. intuition. congruence.
     rewrite plift_splice, plift_one in H10. 
     eapply splicep_aux1 in H10. destruct H10 as [? [? ?]].
     subst x. unfold splice_nat. unfoldq; intuition.
     subst x1. bdestruct (length G <? length H2).
     rewrite <- L2 in H11. rewrite app_length in H11. lia.
     auto. simpl. auto.
   }
   eauto.
   
   
   rewrite <- P2 in HE2.
   eapply pdom_slice with (HX := HX) in HE2 . rewrite plift_splice in HE2. auto.
   
   eapply valt_extend1; eauto.
   rewrite L1. auto. 
   
   eapply closedty_splice. rewrite L2. auto.
  
   (* qual *)
     
  rewrite val_locs_abs in *. rename H5 into HVX;
  apply valt_wf in HVX; apply valt_wf in IVY.
     
  unfoldq. intuition.
  destruct (IYQ1 x). eauto. 
  unfoldq. 
  destruct H11.  destruct H11. 
  bdestruct (x0 =? length H1).
  (* from arg *)
    right. destruct H14 as [? [? ?]]. subst x0. 
    rewrite indexr_head in H14. inversion H14. eauto.
  (* from func *)
    unfoldq. left. split. 
    exists x0. intuition. 
    destruct H14 as [? [? ?]]. 
    rewrite indexr_skip in H14. 
    exists x1. split; eauto. lia.
    exists x0. split. rewrite plift_and in *.
    destruct H11. auto. lia.
    destruct H14 as [? [? ?]]. rewrite indexr_skip in H14; eauto.
    

   (* 2nd *)
  
  rewrite val_locs_abs in *. rename H5 into HVX;
  apply valt_wf in HVX; apply valt_wf in IVY.
    
  unfoldq. intuition.
  destruct (IYQ2 x). intuition.
  unfoldq.
  destruct H11. destruct H11. 
  rewrite plift_or in *. 
  
  bdestruct (x0 =? length (H2'++HX++H2)).
  (* from arg *)
    right. destruct H14 as [? [? ?]]. subst.
    replace ((vx2::H2')  ++ HX++H2) with (vx2::H2' ++ HX++H2) in H14.
    rewrite indexr_head in H14. inversion H14. subst. auto. auto.

    
  (* from func *)
    left. 
    assert ((splice_pl (pone (length G))(length H2)(length HX)) = pone(length (H2'++HX++H2))) as N.
    eapply splicep_one; eauto. 
    repeat rewrite plift_splice in *. repeat rewrite plift_and, plift_one in *.
    rewrite N in *.
    split.
    exists x0; intuition.
    destruct H14. auto. unfoldq; intuition.
    destruct H14 as [? [? ?]].
    replace ((vx2::H2')  ++ HX++H2) with (vx2::H2' ++ HX++H2) in H11. 
    rewrite indexr_skip in H11. exists x1. split; eauto. lia. auto.
    
    exists x0; intuition.
    destruct H14 as [? [? ?]]. 
    replace ((vx2::H2')  ++ HX++H2) with (vx2::H2' ++ HX++H2) in H11. 
    rewrite indexr_skip in H11; eauto. intuition.


  
  eapply valq_abs; eauto.
  rewrite splice_qand.
  eapply valq_abs; eauto.
Qed.


Lemma bi_tseq3: forall S1 S2 M H1 H2 H2' HX t1 t2 S1' S2' M' M'' S1'' S2'' v1 v2 v3 v4 p p1 p2 q1 q2 e1 e2  
 (ST: store_type S1 S2 M)
 (E1: exp_type1 S1 S2 M H1  (H2' ++ HX ++ H2) t1 (splice_tm t1 (length H2) (length HX)) S1' S2' M' v1 v2 
        TBool TBool 
        (plift p1) (splice_pl (plift p1) (length H2) (length HX))
        (plift q1) (splice_pl (plift q1) (length H2) (length HX))
        (plift e1) (splice_pl (plift e1) (length H2)(length HX)))
 (E2: exp_type1 S1' S2' M' H1 (H2' ++ HX ++ H2) t2 (splice_tm t2 (length H2) (length HX)) S1'' S2'' M'' v3 v4
        TBool TBool 
        (plift p2) (splice_pl (plift p2) (length H2) (length HX))
        (plift q2) (splice_pl (plift q2) (length H2) (length HX))
        (plift e2) (splice_pl (plift e2) (length H2) (length HX)))
 (SUB1: psub (plift p1) (plift p))
 (SUB2: psub (plift p2) (plift p)),
 exists S1'' S2'' M'' v5 v6,
  exp_type1 S1 S2 M H1 (H2' ++ HX ++ H2) (tseq t1 t2)
    (splice_tm (tseq t1 t2) (length H2) (length HX)) S1'' S2'' M'' v5 v6 
    TBool TBool 
    (plift p) (splice_pl (plift p) (length H2) (length HX)) 
    pempty pempty
    (por (plift e1) (por (plift e2) (plift q1))) 
        (splice_pl (por (plift e1) (por (plift e2) (plift q1)))
          (length H2) (length HX)).
Proof.
  intros.
  destruct E1 as [IE1 [IE2 [EFF1 [EFF2 [STC1 [ST1 [HV1 [HQ1 HQ2 ]]]]]]]].
  destruct v1; destruct v2; try solve [inversion HV1]. simpl in HV1. subst b0.
  
  remember ST1 as ST1'. clear HeqST1'.
  destruct ST1 as [STL1 [STL2 [SP1 [SP2 SP3]]]].

  destruct E2 as [IE3 [IE4 [EFF3 [EFF4 [STC2 [ST2 [HV2 [HQ3 HQ4 ]]]]]]]].
  destruct v3; destruct v4; try solve [inversion HV2]. simpl in HV2.
  subst b0.
  
  exists S1'', S2''.
  exists M'', (vbool (b && b1)), (vbool (b && b1)).
  split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 8: split.
  (* first one *)
  destruct IE1 as [n1 IE1].
  destruct IE3 as [n3 IE3].
  exists (S(n1 + n3)). intros. destruct n. intuition.
  simpl. rewrite IE1. rewrite IE3. eauto. lia. lia.
  destruct IE2 as [n2 IE2].
  destruct IE4 as [n4 IE4].
  exists (S(n2 + n4)). intros. destruct n. intuition.
  simpl. rewrite IE2. rewrite IE4. eauto. lia. lia. 

  eapply se_trans; eapply se_sub; eauto; eapply vl_mono; eauto.

  eapply se_trans; eapply se_sub; eauto; eapply vl_mono; eauto.
  eapply splice_psub. auto. eapply splice_psub. auto. 

  eapply st_trans; eauto.  
  
  (* store typing *)
  eauto.

  simpl. eauto. 
  eapply valq_bool. 
  eapply valq_bool.
Qed.



Lemma bi_qsub3: forall S1 S2 S1' S2' M H1 H2 t1 t2 M' T T' p p' q1 q1' q2 q2' e1 e1' e2 e2' v1 v2,  
  exp_type1 S1 S2 M H1 H2 t1 t2 S1' S2' M' v1 v2 T T' p p' q1 q2 e1 e2 ->
  psub q1 q1' ->
  psub q2 q2' ->
  psub e1 e1' ->
  psub e2 e2' ->
  psub q1' (pdom H1)  ->
  psub q2' (pdom H2)  ->
  psub e1' (pdom H1)  ->
  psub e2' (pdom H2)  ->
  exists S1'' S2'' M'' v1' v2',
  exp_type1 S1 S2 M H1 H2 t1 t2 S1'' S2'' M'' v1' v2' T T' p p' q1' q2' e1' e2'.
Proof.  
  intros.
  exists S1', S2', M', v1, v2.
  destruct H as [IE1 [IE2 [IEFF1 [IEFF2 [ISTC [IST [IVAL [IQ1 IQ2]]]]]]]]. 
  split. eauto. split. eauto.
  split. eapply se_sub; eauto. intros ? ?. auto.
  split. eapply se_sub; eauto. intros ? ?. auto. 
  split. eauto.
  split. auto.
  split. auto.
  unfold val_qual in IQ1; intuition.
  eapply valq_sub; eauto.
  unfold val_qual in IQ2; intuition.
  eapply valq_sub; eauto.
Qed.

Lemma st_weaken: forall t1 T1 G p q e  
  (W: has_type G t1 T1 p q e)
  (CLT: closed_ty (length G) T1)
  (CLQ: closed_ql (length G) q)
  (CLE: closed_ql (length G) e),
  forall H1 H2 H2' HX M
    (WFE: env_type M H1 (H2'++H2) G (plift p)), 
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
        (plift q) (plift (splice_ql q (length H2)(length HX)))
        (plift e) (plift (splice_ql e (length H2)(length HX)))
        .
Proof. 
  intros ? ? ? ? ? ?  W. 
  induction W; intros; intuition.
  - (* ttrue *)
    exists S1. exists S2. exists M. 
    exists (vbool true), (vbool true).
    rewrite spliceq_empty. rewrite plift_empty. simpl. 
    eapply bi_vtrue3; auto.

  - (* tfalse *)
    exists S1. exists S2. exists M.
    exists (vbool false), (vbool false).
    rewrite spliceq_empty. rewrite plift_empty. simpl.
    eapply bi_vfalse3; auto.

  - (* tvar *)
    rewrite spliceq_empty.
    eapply bi_var_splice; eauto; intuition.

  - (* tref *)
    simpl. intuition.
    assert (closed_ty (length env) TBool). constructor. intuition. 
    destruct (H3 H1 H2 H2' HX M WFE S1 S2 H) as [S1' [S2' [M' [ v1 [v2 IE]]]]]. 
    eapply bi_tref3; eauto.

  - (* tget *)
    assert (closed_ty (length env) (TRef TBool)). constructor. constructor.
    assert (closed_ql (length env) e /\ closed_ql (length env) q).
    eapply closedq_or. auto. intuition.
    destruct (H3 H1 H2 H2' HX M WFE S1 S2 H) as [S1' [S2' [M' [ v1 [v2 IE]]]]]. 
    simpl. rewrite spliceq_empty. rewrite plift_empty.
    rewrite splicety_id in IE. 2: constructor; constructor.
    eapply bi_tget3; eauto.
    eapply envt_convert; eauto.
    rewrite plift_splice. eauto.
    
    
  - (* tput *)
    eapply has_type_closed in W1; eauto.
    eapply has_type_closed in W2; eauto.
    intuition.
    destruct (H9 H1 H2 H2' HX M WFE S1 S2 H) as [S1' [S2' [M' [ v1 [v2 IE]]]]].
    assert (env_type M' H1 (H2'++H2) env (plift p)) as WFE1. 
    eapply envt_store_extend; eauto. apply IE. 
    
    assert (store_type S1' S2' M' ) as ST'.
    apply IE.
    destruct (H0 H1 H2 H2' HX M'  WFE1 S1' S2' ST') as [S1'' [S2'' [M'' [v3 [v4 IE2]]]]].
    simpl. rewrite spliceq_empty in *. repeat rewrite plift_empty.
    rewrite splicety_id in *.
    rewrite <- plift_splice in IE. 
    rewrite <- plift_splice in IE2. 
    eapply bi_tput3; eauto.
    constructor. all: constructor.

  - (* tapp *)
    eapply has_type_closed in W1; eauto.
    eapply has_type_closed in W2; eauto.
    intuition.
    destruct (H11 H2 H3 H2' HX M WFE S1 S2 H4) as [S1' [S2' [M' [v1 [v2 IE]]]]].
    assert (env_type  M' H2 (H2'++H3) env (plift p)) as WFE1. 
    eapply envt_store_extend;  eauto. apply IE. 
    
    assert (store_type S1' S2' M') as ST'. 
    apply IE. 
    specialize (H14 H2 H3 H2' HX M' WFE1 S1' S2' ST') as [S1'' [S2'' [M'' [v3 [v4 IE2]]]]].
    repeat rewrite splice_or.
    repeat rewrite splice_qor.
    repeat rewrite plift_or.
    rewrite <- plift_splice in *.
    eapply bi_tapp3; eauto.
    eapply envt_convert in WFE. eapply WFE. 
    rewrite <- plift_and.
    eapply splice_sep. rewrite plift_and. auto.
    eapply splice_sub. auto.
    eapply splice_sub. auto.
    

  - (* tabs *)
    rewrite spliceq_empty. rewrite plift_empty.
    rewrite <- plift_splice in *.
    eapply bi_tabs3; eauto.
    eapply envt_convert in WFE. eapply WFE. auto.
       
    intros.
    replace (vx2 :: H2' ++ H5) with ((vx2 :: H2') ++ H5) in H10. 
    eapply has_type_closed in W.
    2: { rewrite plift_or, plift_and, plift_one. eauto. }   
    intuition.
    repeat rewrite plift_or in *. rewrite plift_and in *. rewrite plift_one in *.
    
    destruct (H15 (vx1::H4) H5 (vx2::H2') HX M' H10 S1' S2' H11) as [S1'' [S2'' [M''  [vy1 [vy2 EY ]]]]].
    unfold exp_type1 in EY.
    destruct EY as [EY1 [EY2 [EFF1 [EFF2 [STC [ST [VTY [VQY1 VQY2]]]]]]]].
    exists S1'', S2'', M'', vy1, vy2.
    split. 2: split. 3: split. 4: split. 5: split. 6: split. 7:split. 8: split.  

    auto. auto. auto. 

    rewrite splice_por in EFF2.
    repeat rewrite plift_splice. rewrite plift_and, plift_one.
    auto.

    auto.  auto. auto. auto. 
   
    rewrite splice_por in VQY2. 
    repeat rewrite plift_splice. 
    repeat rewrite plift_or in *.
    repeat rewrite plift_splice in *.
    repeat rewrite plift_or in *.
    rewrite plift_one in *. 
    rewrite plift_and. rewrite splice_por in VQY2. auto.

    auto.
  
  - (* tseq *)
    eapply has_type_closed in W1. 2: { eapply envt_tighten; eauto. }
    eapply has_type_closed in W2. 2: { eapply envt_tighten. eapply WFE. eauto. }
    intuition.
    rename H5 into IH1. rename H6 into IH2. rename H4 into ST.
      
    assert (env_type M H2 (H2'++H3) env (plift p1)) as WFE1.
    eapply envt_tighten; eauto.
    destruct (IH1 H2 H3 H2' HX M WFE1 S1 S2 ST) as [S1' [S2' [M' [v1 [v2 IE1]]]]].

    assert (env_type M' H2 (H2'++H3) env (plift p2)) as WFE2.
    eapply envt_tighten.  eapply envt_store_extend. eapply WFE.
    apply IE1. auto.

    assert (store_type S1' S2' M') as ST'. eapply IE1. 

    destruct (IH2 H2 H3 H2' HX M' WFE2 S1' S2' ST') as [S1'' [S2'' [M'' [v3 [v4 IE2]]]]].

    rewrite splicety_id in *. 2-4: constructor.
    repeat rewrite plift_splice in *. rewrite plift_empty in *.  
    rewrite splicep_empty in *. repeat rewrite plift_or in *.

    eapply bi_tseq3; eauto.


  - (* qsub *)
    apply wf_env_type in WFE as WFE'. 
    destruct WFE' as [L1 [L2 [P1 [P2 [P3 P4]]]]].
    assert (closed_ql (length env) q1). eapply closedq_sub in H; eauto.
    assert (closed_ql (length env) e1). eapply closedq_sub in H2; eauto.
    
    intuition. rename H6 into IHW.
    destruct (IHW H3 H4 H2' HX M WFE S1 S2 H5) as [S1' [S2' [M' [v1 [v2 IE]]]]].
    eapply bi_qsub3; eauto. 
    1,2: eapply splice_sub; eauto. 
    rewrite P1. auto.
    rewrite <- P2 in H0. eapply pdom_slice; eauto. 
    rewrite P1. auto.
    rewrite <- P2 in H0. eapply pdom_slice; eauto. unfold closed_ql in CLE. unfoldq; intuition. eapply H2 in H6. lia.
Qed.


Lemma st_weaken1: forall t1 T1 G  
  (W: has_type G t1 T1 qempty qempty qempty ),
  forall H1 H2 S1 S2 H2',
   env_type (st_empty S1 S2) H1 (H2'++H2) G pempty ->
    exists v1 S1', tevaln S1 H1 t1 S1' v1 /\ 
    forall HX, exists v2 M' S2', 
    tevaln S2 (H2'++HX++H2) (splice_tm t1 (length H2) (length HX)) S2' v2 /\ 
    store_effect S2 S2' pempty /\
    length S2 <= length S2'   /\ 
    val_type M' H1 (H2'++HX++H2) v1 v2 T1 (splice_ty T1  (length H2)  (length HX))  /\
    val_qual (length S1) H1 v1 pempty pempty /\
    val_qual (length S2) (H2'++HX++H2) v2 pempty pempty.
Proof. 
  intros. eapply has_type_closed in W as HCL. 2: { rewrite plift_empty. eauto. } 
  destruct HCL as [HCL1 [HCL2 [HCL3 HCL4]]].
  eapply store_invariance with (S1 := S1) (S2 := S2) in W as W'. 2: rewrite plift_empty; eauto. 
  destruct W' as [S1' [S2' [M'  [v1 [v2 ?]]]]].
  destruct H0 as [E1 [E2 [STC [STE [EFF1 [EFF2 [VT [VQ1 VQ2]]]]]]]].
  rewrite plift_empty in *. rewrite vars_locs_empty in EFF1.
  exists v1, S1'. split.  auto. 
  intros.
  eapply st_weaken with (H1 := H1)(H2 := H2)(H2' := H2')(HX := HX)(S1 := S1)(S2 := S2) in W; eauto.
  2: { rewrite plift_empty. eauto. }
  2: { unfold store_type. repeat split.
       + intros. unfold st_empty, strel in H0. simpl in H0. intuition.  
       + intros. unfold st_empty, strel in H0. simpl in H0. intuition.
       + intros. unfold st_empty, strel in H0. simpl in H0. intuition.     
     }
  rewrite plift_splice in *. rewrite plift_empty in *. 
  rewrite splicep_empty in *. 
  destruct W as [S1'' [S2'' [M''  [v1' [v2' ?]]]]].
  destruct H0 as [E1' [E2' [EFF3 [EFF4 [STC' [STE' [VT' [VQ1' VQ2']]]]]]]].
  rewrite vars_locs_empty in EFF3.
  rewrite vars_locs_empty in EFF4.
  assert  (v1' = v1 /\ S1'' = S1'). eapply tevaln_unique; eauto.
  destruct H0. subst v1'. subst S1''.
  exists v2', M'', S2''; eauto; intuition.
  assert (length S2'' = length2 M''). destruct STE'; intuition.
  assert (length S2 <= length2 M'').
  eapply st_mono2 in STC'.  unfold st_empty, length2 in STC'. unfold length2. simpl in STC'. auto.  
  lia.
Qed. 

(**** substitution ****)

Definition env_type_subst2 M H1 H2 G p xx vx qx:=
  length H1  = length G /\
  (length H2 + 1 = length G) /\
  psub (plift p) (pdom H1) /\
  psub (plift (subst_ql p xx qx)) (pdom H2) /\
  (forall x T,
      indexr x G = Some T ->
      plift p x ->
      exists v1 v2 : vl,
      indexr x H1 = Some v1 /\ 
      (x < xx -> indexr x H2 = Some v2) /\
      (x = xx -> vx = v2) /\ 
      (x > xx -> indexr (x-1) H2 = Some v2) /\
      val_type M H1 H2 v1 v2 T (subst_ty T xx qx)) /\
  (forall l x0 x1,
       plift p x0 ->
       var_locs H1 x0  l ->   
       plift p x1 ->
       var_locs H1 x1 l ->  
       x0 = x1) /\
  (forall l x0 x1, 
       plift (subst_ql p xx qx) x0 ->
       var_locs H2 x0 l ->
       plift (subst_ql p xx qx) x1 ->
       var_locs H2 x1 l ->
       x0 = x1)  
.

Lemma filter_closed_subst: forall M H1 H2 G p m v q,
  env_type_subst2 M H1 H2 G p m v q ->
  closed_ql (length G) p.
Proof.
  intros. destruct H as [L1 [L2 [P1 [P2 P3]]]].
  unfold closed_ql. intros.
  unfoldq; intuition. eapply P1 in H.  rewrite L1 in H. auto.
Qed.  

Lemma envt_to_envt_subst2: forall M H1 H2 G p qf q1 v1 v2 T1
  (EMP: q1 = qempty)
  (QF: psub (plift qf) (plift p)),
  env_type M H1 H2 G (plift p) ->
  val_type M H1 H2 v1 v2 T1 T1 ->
  closed_ty (length G) T1 ->
  closed_ql (length G) q1 ->
  closed_ql (length G) qf ->
  (* separation *)
  (forall x l, val_locs v1 l -> plift p x -> var_locs H1 x l -> False) ->
  (forall x l, val_locs v2 l -> plift p x -> var_locs H2 x l -> False) ->
  env_type_subst2 M (v1::H1) H2 (T1::G) (qor qf (qone (length G))) (length G) v2 q1.
Proof.
  intros. remember H as H'. clear HeqH'.
  eapply filter_closed in H'.
  destruct H as [L1 [L2 [PD1 [PD2 [P1 [P2 P3]]]]]].
  unfold env_type_subst2; intuition; simpl in *.
  + lia.
  + lia.
  + rewrite plift_or, plift_one. unfoldq; intuition.
    eapply H5 in H8. simpl. lia. simpl. lia.
  + rewrite plift_subst, plift_or, plift_one, substp_or. rewrite substp_id; auto.
    rewrite substp_hit. intros ? ?. unfoldq; intuition. subst q1. unfoldq; intuition.
   
  + bdestruct (x =? length G); intuition.
    bdestruct (x =? length H1); intuition.
    inversion H. subst T1.
    exists v1, v2; intuition. rewrite substy_id; auto.
    eapply valt_extend with (H2' := [])(H1' := [v1]) in H0.
    simpl in H0. auto. rewrite L1. auto. rewrite L2. auto.

    bdestruct (x =? length H1); intuition.
    destruct (P1 x T) as [vx1 [vx2 [IX1 [IX2 IVT]]]].
    bdestruct (x =? length G); intuition.
    rewrite plift_or, plift_one  in *. unfoldq; intuition.
    unfoldq; intuition.
    exists vx1, vx2; intuition. apply indexr_var_some' in H. intuition.
    apply valt_closed in IVT as HCL.
    eapply valt_extend with (H1' :=[v1])(H2':=[]). intuition.
    rewrite substy_id. intuition. rewrite <-L1. intuition.
    rewrite substy_id. auto. rewrite <- L1. intuition.

  + rewrite plift_or, plift_one in *.
    assert (por (plift p)(pone (length G)) x0).
    unfoldq; intuition.
    assert (por (plift p)(pone (length G)) x1).
    unfoldq; intuition.
    inversion H11; inversion H12.
    eapply P2; eauto. 1,2: eapply var_locs_shrink; eauto.
    1,2: eapply PD1; eauto.
     
    destruct (H6 x0 l); eauto.
    assert (x1 = length H1). unfoldq; intuition.
    subst x1. eapply var_locs_head. eauto.
    eapply var_locs_shrink. eauto. 
    eapply PD1 in H13; eauto.

    destruct (H6 x1 l); eauto.
    assert (x0 = length H1). unfoldq; intuition.
    subst x0. eapply var_locs_head; eauto.
    eapply var_locs_shrink. eauto. eapply PD1 in H14; eauto.

    unfoldq; intuition.

  + rewrite plift_subst, plift_or, plift_one in H, H9. 
    rewrite substp_or in H, H9.
    rewrite substp_id in H, H9. 
    rewrite substp_hit in H, H9.
    inversion H; inversion H9; unfoldq; intuition; subst q1; unfoldq; intuition.
    eapply QF in H11, H12; eapply P3; eauto.
    auto. auto.
Qed.

Lemma wf_env_type_subst2: forall M H1' H1 v1 H2' H2 G G' p q1  T0 v2 
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


Lemma stc_X: forall S1 S2 M,
 store_type S1 S2 M ->
 forall S1' S2', 
  store_effect S1 S1' pempty -> 
  store_effect S2 S2' pempty ->
  length S1 <= length S1' ->
  length S2 <= length S2' ->           
 st_chain M (length S1', length S2', strel M).
Proof. 
  intros. 
  assert (st_chain_partial M (length S1', length S2', strel M) (st_locs1 M)(st_locs2 M)). {
      unfold st_chain_partial. repeat split.
      + intros ? ?. auto.
      + intros ? ?. unfold st_locs1, pnat in *. unfold length1. simpl. destruct H; intuition. 
      + intros ? ?. auto.
      + intros ? ?. unfold st_locs2, pnat in *. unfold length2. simpl. destruct H; intuition.
      + intros. simpl. auto.
    }
    assert (st_chain_partial2 (length S1', length S2', strel M) M (st_locs1 M)(st_locs2 M)). {
      unfold st_chain_partial2. repeat split.
      + intros ? ?. unfold st_locs1, pnat in *. unfold length1. simpl. destruct H; intuition.
      + intros ? ?. auto.
      + intros ? ?. unfold st_locs2, pnat in *. unfold length2. simpl. destruct H; intuition.
      + intros ? ?. auto.
      + intros. simpl in H4. auto.
    }
    unfold st_chain. intuition.
Qed.

Lemma envt_subst_store_wf1: forall M H1 H1' v1 H2 H2' G G' p q q1 v2'0 T0
    (WFE: env_type_subst2 M (H1' ++ v1 :: H1) (H2' ++ H2) (G' ++  T0 :: G) p  (length G) v2'0 q1),
    psub (plift q) (plift p) -> 
    psub (vars_locs (H1'++v1::H1) (plift q)) (pnat (length1 M)). 
Proof. 
  intros. unfoldq; intuition.
  intros; destruct WFE as [L1 [L2 [P1 [P2 [W1 [W2 W3]]]]]]; intuition.
  unfoldq; intuition.
  destruct H0 as [? [? ?]].
  specialize (H x0). intuition.
  
  assert (exists T, indexr x0 (G'++T0::G) = Some T) as TY. 
  eapply indexr_var_some. eapply P1 in H4.
  rewrite <- L1. rewrite app_length in *. simpl in *.  lia.
  destruct TY as [T ?].
  destruct H3 as [? [? ?]].
  destruct (W1 x0 T) as [vx1 [vx2 [IX1 [IX2 [? [? IV]]]]]]. eauto. eauto. 
  
  rewrite H3 in IX1. inversion IX1. subst.
  eapply valt_wf in IV. intuition.
  eapply H8. auto.
Qed.

Lemma envt_subst_store_wf2: forall M H1 H1' v1 H2 H2' G G' p q q1 v2'0 T0
    (WFE: env_type_subst2 M (H1' ++ v1 :: H1) (H2' ++ H2) (G' ++  T0 :: G) p  (length G) v2'0 q1)
    (EMP: q1 = qempty)
    (LL2: length H2 = length G), 
    psub (plift (subst_ql q (length G) q1)) (plift (subst_ql p (length G) q1)) -> 
    psub (vars_locs (H2'++H2) (plift (subst_ql q (length H2) q1))) (pnat (length2 M)).  
Proof. 
  intros. destruct WFE as [L1 [L2 [P1 [P2 [W1 [W2 W3]]]]]]; intuition.
  intros ? ?. 
  destruct H0 as [? [? ?]].
  rewrite LL2 in H0. eapply H in H0.

  assert (plift p (length G) /\ plift q1 x0 \/
            length G > x0    /\ plift p x0  \/
            length G <= x0   /\ plift p (x0 + 1)) as CASES. {
  rewrite plift_subst in H0. unfold subst_pl in H0. destruct H0 as [[? A]|B].
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
    (* assert (indexr (length G) (G'++T0::G) = Some T0) as TY.
    rewrite indexr_skips. rewrite indexr_head. eauto. simpl. lia.
    destruct (W1 (length G) T0) as [vx1 [vx2 [IX1 [IX2 [? [? IV]]]]]]; eauto.    
    eapply valt_wf in IV. eapply IV. rewrite <-H4 in *; eauto. intuition. *)
    (* <--- PROBLEM *)
  - assert (exists T, indexr x0 (G'++T0::G) = Some T) as TY.
    rewrite indexr_var_some. rewrite app_length. simpl. lia.
    destruct TY as [T TY].
    destruct (W1 x0 T) as [vx1 [vx2 [IX1 [IX2 [? [? IV]]]]]]; eauto.
    eapply valt_wf in IV. eapply IV. eauto. 
    destruct H3 as (? & ? & ?). rewrite IX2 in H3. inversion H3.
    subst x1. eauto. eauto.
  - assert (exists T, indexr (x0+1) (G'++T0::G) = Some T) as TY.
    rewrite indexr_var_some. rewrite app_length. simpl. eapply P1 in GT2. unfoldq; intuition.
    repeat rewrite app_length in * . simpl in *. lia.
    destruct TY as [T TY].
    destruct (W1 (x0+1) T) as [vx1 [vx2 [IX1 [IX2 [? [? IV]]]]]]; eauto.
    eapply valt_wf in IV. eapply IV.
    destruct H3 as (? & ? & ?).
    bdestruct (x0+1 =? length G); intuition.
    bdestruct (length G <? x0+1); intuition.
    replace (x0+1-1) with x0 in H11. rewrite H3 in H11.
    inversion H11. subst. auto. lia.
Qed.




Lemma envt_subst_extend: forall M H1 H1' v1 H2 H2' G G' p q1 T vx1 vx2 T0  v2'0 
  (WFE: env_type_subst2 M (H1' ++ v1 :: H1) (H2' ++ H2) (G' ++ T0 :: G) p (length G) v2'0 q1) 
  (LL1: length H1 = length G)
  (LL2: length H2 = length G)
  (LL3: length H1' = length G')
  (LL4: length H2' = length G')
  (CLQ1: closed_ql (length G) q1),
  val_type M (H1'++v1::H1)(H2'++H2) vx1 vx2 T (subst_ty T (length H2) q1)   ->
  (* separation *)
    (forall x l, val_locs vx1 l -> (plift p x) -> var_locs (H1'++v1::H1) x l -> False) ->
    (forall x l, val_locs vx2 l -> (plift (subst_ql p (length G) q1) x) -> var_locs (H2'++H2) x l -> False) ->
  env_type_subst2 M (vx1 :: H1' ++ v1 :: H1) (vx2::H2'++H2) (T::G'++T0::G) (qor p (qone (length (G'++T0::G))))(length G) v2'0 q1.
Proof. 
  intros. eapply filter_closed_subst in WFE as HFCL.
  apply wf_env_type_subst2 in  WFE as WFE'; auto.
  destruct WFE' as [D1 [D2 [D3 D4]]].
  destruct WFE as [L1 [L2 [PD1 [PD2 [P1 [P2 P3]]]]]].
   
  unfold env_type_subst2; intuition; simpl.
  + rewrite L1. auto.
  + rewrite L2. auto.
  + rewrite plift_or, plift_one. rewrite  <- L1. unfoldq; intuition. eapply PD1 in H7. simpl. repeat rewrite app_length in *. simpl in *.  lia. rewrite app_length in *. simpl in *.  rewrite app_length. simpl. lia.
  + rewrite plift_subst, plift_or, plift_one.
    rewrite <- L2. rewrite <- LL2. unfoldq; intuition. unfold subst_pl in H6.
    unfoldq; intuition. 
    1,3: simpl; eapply PD1 in H8; repeat rewrite app_length in *;  lia.
    1,2: simpl; repeat rewrite app_length in *;  lia.
    simpl. eapply CLQ1 in H6. rewrite app_length; simpl;  lia.
    1-3: rewrite app_length in H7; lia.
    1,3: eapply HFCL in H6;  simpl; repeat rewrite app_length in *;  lia.
    1,2: simpl; repeat rewrite app_length in *;  lia.
    
  + simpl in *. rewrite app_length in *. simpl in *. rewrite app_length in *.
    bdestruct (x =? length G'+S (length G)); intuition.
    - inversion H6. subst T1.
      assert (length H1'+S(length H1) = length G'+S(length G)).
      rewrite L1. simpl. auto.
      bdestruct (x =? length H1'+S(length H1)); intuition.
      exists vx1, vx2; intuition.
      bdestruct (x-1=? length H2'+length H2); intuition. 
      eapply valt_closed in H as HCL. destruct HCL.
      eapply valt_extend1; eauto; intuition.
      rewrite <- LL2. auto. rewrite <- LL2. auto.
    
    - apply indexr_var_some' in H6 as H6'. rewrite app_length in *.  simpl in *.
      destruct (P1 x T1) as [v1' [v2' [? [? [? VT]]]]]; auto.
      bdestruct (x =? length G'+S(length G)); intuition.
      rewrite plift_or, plift_one in H7.
      unfoldq; intuition.
      exists v1', v2'; intuition.
      bdestruct (x =? length H1'  + S(length H1)); intuition.
      bdestruct (x =? length H2'  + length H2); intuition.
      bdestruct (x-1=? length H2'  + length H2); intuition.
      eapply valt_closed in H13 as HCL.
      eapply valt_extend1; intuition.
      
  + rewrite plift_or, plift_one in H6, H8.
    inversion H6; inversion H8.
    - eapply P2; eauto.
      eapply var_locs_shrink. eauto. eapply PD1; eauto.
      eapply var_locs_shrink. eauto. eapply PD1; eauto.
    - destruct (H0 x0 l); eauto.
      assert (x1 = (length (G'++ T0::G))).
      unfold pone in H11. auto.   rewrite <- L1 in H12. 
      subst x1. eapply var_locs_head; eauto.
      eapply var_locs_shrink. eauto . eapply PD1; eauto.
    
    - destruct (H0 x1 l); eauto.
      assert (x0 = (length (G'++ T0::G))).
      unfold pone in H10. auto.   rewrite <- L1 in H12. 
      subst x0. eapply var_locs_head; eauto.
      eapply var_locs_shrink. eauto . eapply PD1; eauto.
    
    - unfoldq; intuition.
  
  + rewrite plift_subst, plift_or, substp_or in H6, H8.
    remember (subst_pl(plift p) (length G) (plift q1)) as PP.
    inversion H6; inversion  H8.
    - subst PP. eapply P3; eauto. rewrite plift_subst. auto. 
      eapply var_locs_shrink; eauto. eapply PD2; eauto. rewrite plift_subst. auto.
      rewrite plift_subst.  auto. eapply var_locs_shrink; eauto. eapply PD2; eauto. rewrite plift_subst. auto.
    - destruct (H3 x0 l); eauto.
      assert (x1 = (length (G'++ G))).
      rewrite plift_one in H11.  unfold subst_pl in H11.
      unfoldq; intuition. 
      1,4: rewrite app_length in H11; simpl in H11; lia.
      1,3,6-7:  rewrite app_length in *; simpl in H13; lia.
      1,3: subst PP; rewrite plift_subst in PD2; eapply PD2 in H10; rewrite app_length in *;  simpl in *; lia.
      subst x1. rewrite app_length in H8.  simpl in H8. lia.
      rewrite app_length in H11.  simpl in H11. lia.
      repeat rewrite app_length in *. simpl  in H13. lia.
      subst x1. rewrite app_length in H8.  simpl in H8. lia.
      replace (length (G'++G))  with (length (H2'++H2))  in H12. 
      subst x1. eapply var_locs_head; eauto. repeat rewrite app_length in *. simpl  in *. lia.
      subst PP. rewrite plift_subst.  auto.
      eapply var_locs_shrink. eauto . eapply PD2; eauto. subst PP.  rewrite plift_subst. auto.

    - destruct (H3 x1 l); eauto.
      assert (x0 = (length (G'++ G))).
      rewrite plift_one in H10.  unfold subst_pl in H10.
      unfoldq; intuition. 
      1,4: rewrite app_length in  H10; simpl in H10; lia.
      1,3,6-7:  rewrite app_length in *; simpl in H13; lia.
      1,3: subst PP; rewrite plift_subst in PD2; eapply PD2 in H11; rewrite app_length in *;  simpl in *; lia.
      1,4: subst x0; rewrite app_length  in H8; simpl in H8; lia.
      rewrite app_length in *; simpl in H10; lia.
      rewrite app_length in *. simpl in H13. lia.

      replace (length (G'++G))  with (length (H2'++H2))  in H12. 
      subst x0. eapply var_locs_head; eauto. repeat rewrite app_length in *. simpl  in *. lia.
      subst PP. rewrite plift_subst.  auto.
      eapply var_locs_shrink. eauto . eapply PD2; eauto. subst PP.  rewrite plift_subst. auto.
    - assert (x1  =  length G'+  length G).  
      rewrite plift_one in H11.  unfold  subst_pl in H11.
      unfoldq; intuition.
      1,4: rewrite app_length in H11; simpl in H11; lia.
      1,2,4,6,9: rewrite app_length in H13; simpl in H13; lia.
      1,3: rewrite app_length in H13; simpl in H13; lia.
      1,2: rewrite app_length in H11; simpl in H11; lia.
      rewrite app_length in H13; simpl in H13; lia.
     
      assert (x0 = length G' + length G).
      rewrite plift_one in H10.  unfold  subst_pl in  H10.
      unfoldq; intuition.
      1,4: rewrite app_length in H10; simpl in H10; lia.
      1,2,4,6,9: rewrite app_length in H14; simpl in H14; lia.
      1,3: rewrite app_length in H14; simpl in H14; lia.
      1,2: rewrite app_length in H10; simpl in H10; lia.
      rewrite app_length in H14; simpl in H14; lia.
      lia.
Qed.

Lemma envt_same_locs_subst: forall S1 S2 M H1 H2 G p p1 l1 l2 H1' H2' v1 G' T0 v2'0 q1 b
    (LL1: length H1 = length G)
    (LL2: length H2 = length G)
    (LL3: length H1' = length G')
    (LL4: length H2' = length G')
    (EMP: q1 = qempty)
    (V1: v1 = vbool b)
    (V2: v2'0 = vbool b),
    store_type S1 S2 M ->
    env_type_subst2 M (H1' ++ v1 :: H1) (H2' ++ H2) (G' ++ T0 :: G) p (length G) v2'0 q1 ->
    strel M l1 l2 ->
    psub p1 (plift p) ->
    vars_locs (H1' ++ v1 :: H1) p1 l1 <-> vars_locs (H2' ++ H2) (subst_pl p1 (length G) (plift q1)) l2.
Proof. 
  intros.
  destruct H0 as (? & ? & ? & ? & WFX & ? & ?).
  split; intros V.
  - destruct V as (? & ? & v1' & ? & V).
    assert (exists T, indexr x (G' ++ T0 :: G) = Some T) as TT. {
      eapply indexr_var_some.  eapply indexr_var_some' in H11. rewrite app_length in *. simpl in *. lia. } 
    destruct TT as (T & ?).
    destruct (WFX x T) as (v1'' & v2 & ? & ? & ?). eauto. eapply H4 in H10. auto.
    bdestruct (x <? length G). intuition.
    rewrite indexr_skips in H11, H13. rewrite indexr_skip in H11,H13.
    rewrite indexr_skips in H18. 
    exists x. split. eapply substp_mem2; eauto.
    unfoldq; intuition. rewrite indexr_skips. exists v2; intuition.
    rewrite H11 in H13. inversion H13. subst v1''.
    edestruct valt_same_locs; eauto. lia. lia. lia. lia. simpl. lia. simpl. lia.
  
    bdestruct (x =?  length G). rewrite H13 in H11. inversion H11. subst v1'.
    subst x. subst v1. rewrite <- LL1 in H13. rewrite indexr_skips in H13. rewrite indexr_head in H13.
    inversion H13. subst v1''. rewrite val_locs_bool in V. unfoldq; intuition.
    simpl. lia.
    intuition. 
    assert (x > length G). lia. intuition.
    exists (x-1). unfoldq; intuition.
    unfold subst_pl. right. left. intuition. replace (x-1+1) with x. auto. lia.
    exists v2. intuition. rewrite H11 in H13. inversion H13. subst.
    edestruct valt_same_locs; eauto. 
  - destruct V as (? & ? & v2 & ? & V).

  assert (p1 (length G) /\ plift q1 x \/
            length G > x    /\ p1 x  \/
            length G <= x   /\ p1 (x + 1)) as CASES. {
  unfold subst_pl in H10. destruct H10 as [[? A]|B].
  - (* p (len G) *)
    destruct A as [[AA | AB] | AC].
    + (* len G <= x0 /\ p (x0 + 1) *) eauto. 
    + (* len G > x0 /\ p x0 *) eauto. 
    + (* q1 x0 *) eauto. 
  - destruct B as [BA | BB].
    + (* len G <= x0 /\ p (x0+1) *) eauto. 
    + (* len G > x0 /\ p x0 *) eauto. }

  destruct CASES as [[EQ1 EQ2] | [[LT1 LT2] | [GT1 GT2]]].
    + subst q1. rewrite plift_empty in *. contradiction.
    + assert (exists T, indexr x (G'++T0::G) = Some T) as TY.
      rewrite indexr_var_some. rewrite app_length. simpl. lia.
      destruct TY as [T TY].
      destruct (WFX x T) as [vx1 [vx2 [IX1 [IX2 [? [? IV]]]]]]; eauto.
      eexists. split. eauto. eexists. split. eauto. 
      eapply valt_same_locs. eauto. eauto. eauto.
      rewrite IX2 in H11; eauto. inversion H11. subst. eauto.
    + assert (exists T, indexr (x+1) (G'++T0::G) = Some T) as TY.
      eapply indexr_var_some' in H11. 
      rewrite indexr_var_some. rewrite app_length in *. simpl. lia.
      destruct TY as [T TY].
      destruct (WFX (x+1) T) as [vx1 [vx2 [IX1 [IX2 [? [? IV]]]]]]; eauto.
      eexists. split. eauto. eexists. split. eauto. 
      eapply valt_same_locs. eauto. eauto. eauto.
      replace x with (x + 1 - 1) in H11. 2: lia.
      rewrite H13 in H11; eauto. inversion H11. subst. eauto. lia. 
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
  + unfoldq; intuition. 
    eapply H0 in H.
    destruct (P2 l x0 x1); auto.
  + unfoldq; intuition. 
    eapply substp_sub with (m := m) (q1 := q) in H0.
    eapply H0 in H. eapply H0 in H4. 
    destruct (P3 l x0 x1); auto. 
Qed.


Lemma has_type_closed_subst: forall M H1 H2 G p m v q q0 T e t,
  env_type_subst2 M H1 H2 G p m v q0 ->
  has_type G t T p q e ->
  (
    closed_ty (length G) T /\
    closed_ql (length G) p /\
    closed_ql (length G) q /\
    closed_ql (length G) e
  ).
Proof.
  intros. eapply filter_closed_subst in H as H'.  induction H0; intuition.
  + destruct H as [? [? [? [? [? [? ?]]]]]]. destruct (H7 x T) as [? [? [? [? ?]]]]; auto.
    bdestruct (x <? m); intuition.  eapply valt_closed in H16. rewrite <- H.  intuition.
    eapply valt_closed in H16. rewrite <- H.  intuition.
  + unfold closed_ql. intros. unfold qone in H4. bdestruct (x0 =? x); intuition.
    apply indexr_var_some' in H0. lia.
  + eapply closedq_or; intuition.
  + eapply closedq_or; intuition. eapply closedq_or; intuition.
  + inversion H5. subst. auto.
  + eapply closedq_or; intuition. eapply closedq_sub. 2: eapply H3. auto.
  + eapply closedq_or; intuition. eapply closedq_or; intuition. eapply closedq_sub. 2: eapply H4. auto.
  + constructor; intuition.
  + assert (env_type_subst2 M H1 H2 env p1 m v q0). eapply envt_subst_tighten; eauto. 
    assert (env_type_subst2 M H1 H2 env p2 m v q0). eapply envt_subst_tighten. 2: eauto. auto.
    assert (closed_ql (length env) p1). eapply closedq_sub; eauto.
    assert (closed_ql (length env) p2). eapply closedq_sub. 2: eauto. auto.
    intuition. eapply closedq_or; intuition. eapply closedq_or; intuition.
Qed.


Lemma envt_subst_store_change: forall M M' H1 H1' v1 H2 H2' G G' T0 p v2'0 q1 b
    (WFE: env_type_subst2 M (H1' ++ v1 :: H1) (H2' ++ H2) (G' ++ T0 :: G) p (length G) v2'0 q1)
    (LL1: length H1 = length G)
    (LL2: length H2 = length G)
    (LL3: length H1' = length G')
    (LL4: length H2' = length G')
    (LM: length2 M <= length2 M')
    (V1: v1 = vbool b)
    (V2: v2'0 = vbool b),
    st_chain_partial M M' (vars_locs (H1' ++ v1 :: H1)  (plift p)) (vars_locs (H2' ++ H2) (plift (subst_ql p (length H2) q1))) ->
    st_chain_partial2 M' M (vars_locs (H1' ++ v1 :: H1) (plift p)) (vars_locs (H2' ++ H2) (plift (subst_ql p (length H2) q1))) ->
    env_type_subst2 M' (H1' ++ v1 :: H1) (H2' ++ H2) (G' ++ T0 :: G) p (length G) v2'0 q1.
Proof.
  intros. destruct WFE as [L1 [L2 [P1 [P2 [W1 [W2 W3]]]]]]. 
  repeat split; auto. intros.
  destruct (W1 _ _  H3 H4) as [vx1 [vx2 [IH1 [IH2A [IH2B [IH2C HVX]]]]]]; intuition.
  exists vx1, vx2; intuition.
  eapply valt_store_change in HVX; eauto.
  eapply stchain_tighten. eauto.
  intros ? ?. exists x. intuition. exists vx1. intuition.
  intros ? ?. unfoldq; intuition. 
  bdestruct (x =? length G). 
  intuition. subst v2'0. subst x.
  subst vx2. rewrite val_locs_bool in H5. unfoldq; intuition. 
  
  bdestruct (x <? length G). 
  exists x. split. 
  eapply substq_mem2; eauto. lia.
  unfoldq; intuition. exists vx2; intuition.
  bdestruct (length G <? x); intuition. 
  exists (x-1). split. 
  assert (closed_ql (length H2'+S(length H2)) p). {
    intros ? ?. eapply P1 in H10. rewrite app_length in *. simpl in *. lia.
  }
  eapply substq_mem; eauto; eauto. lia.
  unfoldq; intuition. exists vx2; intuition.

  eapply stchain_tighten'. eauto.
  intros ? ?. exists x. intuition. exists vx1. intuition.
  intros ? ?. unfoldq; intuition.
  bdestruct (x =? length G). 
  intuition. subst v2'0. subst x.
  subst vx2. rewrite val_locs_bool in H5. unfoldq; intuition. 
  
  bdestruct (x <? length G). 
  exists x. split. 
  eapply substq_mem2; eauto. lia.
  unfoldq; intuition. exists vx2; intuition.
  bdestruct (length G <? x); intuition. 
  exists (x-1). split. 
  assert (closed_ql (length H2'+S (length H2)) p). {
    intros ? ?. eapply P1 in H10. rewrite app_length in *. simpl in *. lia.
  }
  eapply substq_mem; eauto; eauto. lia.
  unfoldq; intuition. exists vx2; intuition.
Qed.


Lemma envt_subst_store_extend: forall M M' H1 H1' v1 H2 H2' G G' T0 p v2'0 q1,
    env_type_subst2 M (H1' ++ v1 :: H1) (H2' ++ H2) (G' ++ T0 :: G) p (length G) v2'0 q1 ->
    st_chain M M' ->
    env_type_subst2 M' (H1' ++ v1 :: H1) (H2' ++ H2) (G' ++ T0 :: G) p (length G) v2'0 q1.
Proof.
  intros. destruct H as [L1 [L2 [P1 [P2 [W1 [W2 W3]]]]]]. 
  repeat split; auto. intros.
  destruct (W1 _ _  H H3) as [vx1 [vx2 [IH1 [IH2 HVX]]]]; intuition.
  bdestruct (x <? length G); intuition.
  rename H7 into HVX.
  exists vx1, vx2; intuition.
  eapply valt_store_extend in HVX; eauto.
  eapply st_mono2 in H0. auto.
  rename H7 into HVX.
  exists vx1, vx2; intuition.
  eapply valt_store_extend in HVX; eauto.
  eapply st_mono2 in H0. auto.
Qed.



Lemma envt_subst_extend_all: forall M M' H1 H1' v1 H2 H2' G G' p vx1 vx2 T1 q1 qf v2'0 T0 b
    (LL1: length H1 = length G)
    (LL2: length H2 = length G)
    (LL3: length H1' = length G')
    (LL4: length H2' = length G')
    (CLQ1: closed_ql  (length G) q1)
    (EMP: q1  = qempty)
    (LM: length2 M <= length2 M')
    (V1: v1 = vbool b)
    (V2: v2'0 = vbool b),
    env_type_subst2  M (H1' ++ v1 :: H1)  (H2' ++ H2) (G' ++ T0 :: G) p (length G) v2'0 q1 ->
    st_chain_partial M M' (vars_locs (H1' ++ v1 :: H1) (plift (qand p qf ))) (vars_locs (H2' ++ H2) (plift (subst_ql (qand p qf) (length H2) q1))) ->
    st_chain_partial2 M' M (vars_locs (H1' ++ v1 :: H1) (plift (qand p qf))) (vars_locs (H2' ++ H2) (plift (subst_ql (qand p qf) (length H2) q1))) ->
    val_type M' (H1'++v1::H1) (H2'++H2) vx1 vx2 T1 (subst_ty T1 (length H2) q1) ->
    psub (pand (vars_locs (H1' ++ v1 :: H1) (plift (qand p qf))) (val_locs vx1)) pempty ->
    psub (pand (vars_locs (H2' ++ H2) (plift (subst_ql (qand p qf) (length H2) q1))) (val_locs vx2))  pempty ->
    closed_ty (length G'+ S (length G)) T1 ->
    env_type_subst2 M' (vx1 :: H1' ++ v1 :: H1) (vx2 :: H2' ++ H2) (T1 :: G' ++ T0 :: G) (qor (qand p qf) (qone (length (G' ++ T0 :: G)))) (length G) v2'0 q1.
Proof. 
  intros. 
  eapply envt_subst_extend.
  eapply envt_subst_store_change.
  eapply envt_subst_tighten.
  eauto. rewrite plift_and. intros ? ?. unfoldq; intuition.
  auto. auto. auto. auto. auto. eauto. eauto. auto. auto. auto. auto. auto. auto. auto. auto.
    
  (* now prove separation on the first *) 
  intros.

  unfoldq. unfoldq.
  eapply H5. intuition.
  exists x. intuition.  
  destruct H10.
  exists x0. intuition. eauto. auto.
   
  (* now prove separation on the second *) 
  intros.

  unfoldq; intuition.
  destruct H10.
  subst q1.
   
  unfoldq; intuition.
  eapply H6. intuition.
  exists x; intuition. rewrite LL2. auto.  eauto. auto.
Qed.

Lemma separation_subst1: forall M M' H1 H1' H2 H2' G G' p vf1 vx1 qf q1 v1 T0 v2'0 q0
    (WFE:  env_type_subst2 M (H1'++v1::H1) (H2'++ H2) (G'++T0::G) p (length G) v2'0 q0)
    (HQF1: val_qual (length1 M) (H1'++v1::H1) vf1 (plift p) qf)
    (HQX1: val_qual (length1 M') (H1'++v1::H1) vx1 (plift p) (plift q1))
    (STC: st_chain M M')
    (PVF1: psub (val_locs vf1) (pnat (length1 M')))
    (QSEP: psub (pand qf (plift q1)) pempty),
    psub (pand (val_locs vf1) (val_locs vx1)) pempty 
    .
Proof. 
  intros. unfoldq. intuition.
  remember WFE as WFE1; clear HeqWFE1;
  destruct WFE as [L1 [L2 [P1 [P2 [W [SEP1 SEP2]]]]]].
  + bdestruct (x <? length1 M).
  - destruct (HQF1 x). intuition.
    destruct (HQX1 x). intuition. 
    assert (x0 = x1). eapply SEP1; intuition; eauto.
    eapply QSEP. subst x0. intuition; eauto.
  - bdestruct (x <? length1 M').
    -- destruct (HQX1 x). intuition.
      (* fresh loc in vf, also occurs in vx --> can't happen *)
      assert (psub (vars_locs (H1'++v1::H1) (plift (qone x0))) (pnat (length1 M))) as L. {
        eapply envt_subst_store_wf1. eauto. unfoldq. intuition. rewrite plift_one in H6. unfoldq; intuition. subst x1. eauto.
      }
      assert (x < length1 M). {
        eapply L. unfoldq. exists x0. intuition.
        rewrite plift_one.  unfoldq; intuition.
      }
      lia.
    -- (* fresh loc in vx, bigger than vf *)
      eapply PVF1 in H0. lia.
Qed.
(*
  qf : inner function 
  q1 : inner argument's qualifier 
  q0 : outter argument's qualifier 
  p0 : outter filter
*)
Lemma argq_subst: forall qf q1 m n q0 p0,
  closed_ql m p0 ->
  closed_ql n qf ->
  closed_ql n q1 ->
  n > m  ->
  q0  = qempty ->
  psub (pand  (plift qf) (plift q1)) pempty ->
  psub (pand  (plift qf) (plift p0)) pempty ->
  psub (pand (plift (subst_ql qf m q0)) (plift (subst_ql q1 m p0)))  pempty.
Proof.
  intros. subst q0.
  repeat rewrite plift_subst. unfold subst_pl.
  unfoldq; intuition.
  1-4: destruct (H4 m); intuition.
  1,3: destruct (H4 (x+1)); intuition.
  destruct (H4 x); intuition.
  eapply H in H6. intuition.
  destruct (H4 x); intuition.
  destruct (H5 x); intuition.
  destruct (H4 (x+1)); intuition.
  destruct (H4 x); intuition.
Qed.

(*
  qf : inner function 
  q1 : inner argument's qualifier 
  q0 : outter argument's qualifier 
*)
Lemma argq_subst': forall qf q1 m q0,
  q0  = qempty ->
  psub (pand  (plift qf) (plift q1)) pempty ->
  psub (pand (plift (subst_ql qf m q0)) (plift (subst_ql q1 m q0)))  pempty.
Proof.
  intros. subst q0.
  repeat rewrite plift_subst. unfold subst_pl.
  unfoldq; intuition.
  1-2: destruct (H0 m); intuition.
  1,3: destruct (H0 (x+1)); intuition.
  1,2,4: destruct (H0 x); intuition.
  destruct (H0 (x+1)); intuition.
Qed.


Lemma separation_subst2: forall M M' H1 H1' H2 H2' G G' p vf2 vx2 qf q0 v1 T0 v2'0 q1 
    (WFE: env_type_subst2 M (H1'++v1::H1) (H2'++ H2) (G'++T0::G) p (length G) v2'0 q0)
    (L: length G = length H2)
    (HQF: val_qual (length2 M) (H2'++H2) vf2  (plift (subst_ql p (length H2) q0)) (plift (subst_ql qf (length H2) q0)))
    (HQX: val_qual (length2 M') (H2'++H2) vx2 (plift (subst_ql p (length H2) q0)) (plift (subst_ql q1 (length H2) q0)))
    (STC: st_chain M M')
    (PVF: psub (val_locs vf2) (pnat (length2 M')))
    (QSEP: psub (pand (plift qf) (plift q1)) pempty)
    (EMP: q0 = qempty),
    psub (pand (val_locs vf2) (val_locs vx2)) pempty 
    .
Proof. 
  intros. rewrite <- plift_empty in QSEP.
  rewrite <- plift_and in  QSEP.
  assert (psub (pand (plift (subst_ql qf (length H2) q0)) (plift (subst_ql q1 (length H2) q0))) pempty) as QSEP'.
  eapply argq_subst'. auto. rewrite plift_and, plift_empty in QSEP; auto.

  subst q0.
  unfoldq. intuition.
  remember WFE as WFE1; clear HeqWFE1;
  destruct WFE as [L1 [L2 [P1 [P2 [W [SEP1 SEP2]]]]]].
  repeat rewrite plift_subst in *. rewrite plift_empty in *.
  
  + bdestruct (x <? length2 M).
  - destruct (HQF x). intuition. destruct H4. 
    destruct (HQX x). intuition. 
    destruct H6. 
    assert (x0 = x1). rewrite L in SEP2.
    eapply SEP2; intuition. eauto. eauto.
    eapply QSEP'; eauto. eauto. intuition. eauto. subst x0. eauto.
   
  - bdestruct (x  <? length2 M').
    -- destruct (HQX x). intuition.
      (* fresh loc in vf, also occurs in vx --> can't happen *)
      eapply envt_subst_store_wf2 with (q :=p) in WFE1 ; eauto.
      2: { intros ? ?. auto. }
      assert (x < length2 M). {
        destruct (HQX x); intuition.
        destruct (WFE1 x). unfold vars_locs. exists x0. rewrite plift_subst, plift_empty. intuition. lia. lia.
      }
       
      lia.
    -- (* fresh loc in vx, bigger than vf *)
      eapply PVF in H0. lia.

Qed.

Lemma result_reach2: forall M M' M'' H1 H1' v1 H2 H2' G G' p q0 v2'0 T0  r2 q2 q1 vf2 vx2
    (WFE: env_type_subst2 M (H1' ++ v1 :: H1) (H2' ++ H2) (G' ++ T0 :: G) p (length G) v2'0 q0)
    (HQX2: val_qual (length2 M') (H2' ++ H2) vx2 (plift (subst_ql p (length H2) q0)) (plift (subst_ql q1 (length H2) q0))) 
    (HQY2: psub (pand (pnat (length2 M'')) (val_locs r2)) (por (pand (vars_locs (H2' ++ H2) (plift (subst_ql q2 (length H2) q0)))  (val_locs vf2)) (val_locs vx2)))
    (Q2SUB: psub (plift q2) (plift p))
    (EMP: q0 = qempty)
    (ST1: st_chain M M') 
    (ST2: st_chain M' M''),
    val_qual (length2 M) (H2' ++ H2) r2 (plift (subst_ql p (length H2) q0))  (plift(subst_ql (qor q2 q1) (length H2) q0)).    
Proof. 
  intros. 
  unfoldq; intuition. 
  destruct WFE as [L1 [L2 [P1 [P2 [W [SEP1 SEP2]]]]]].
  repeat rewrite plift_subst in *. rewrite plift_or. rewrite substp_or.
  eapply substp_sub  with (m := (length H2)) (q1 := q0) in Q2SUB as Q2'.
  repeat rewrite plift_subst in Q2'.
  destruct (HQY2 x). intuition. eapply st_mono2'; eauto. eapply st_mono2'; eauto.
  - destruct H.  destruct H.  destruct H.
    exists x0; intuition.
    unfoldq; intuition. 
  - destruct (HQX2 x). intuition. eapply st_mono2'; eauto.
    destruct H4 as [? [? ?]]. 
    unfoldq; intuition.
    exists x0. intuition.
    exists  x1. intuition.
Qed.  



Lemma bi_var_subst2: forall G G' M S1 S2 S2'' H1 H1' H2 H2' x T1 q1 p t1 T v1 v2x v2 p1
  (WFE: env_type_subst2 M (H1'++v1::H1) (H2'++H2) (G'++T1::G) p (length G) v2x q1)
  (W: has_type G t1 T1 p1 q1 qempty )
  (CLT1: closed_ty (length G) T1)
  (CLQ1: closed_ql (length G) q1)
  (CLP1: closed_ql (length G) p1)
  (CLQONE: closed_ql (length G'+ S (length G)) (qone x))
  (CLP: closed_ql (length G'+ S(length G)) p)
  (CLT:  closed_ty (length G'+ S(length G)) T)
  (L1: length H1 = length G)
  (L2: length H2 = length G)
  (L3: length H1' = length G')
  (L4: length H2' = length G')
  (ST2: store_type S1 S2 M)
  (E2: tevaln S2 (H2'++H2) (splice_tm t1 (length H2) (length H2')) S2'' v2)
  (EFF2: store_effect S2 S2'' pempty)
  (LS2: length S2 <= length S2'') 
  (VALT:  val_type M H1 (H2'++H2) v1 v2 T1 (splice_ty T1 (length H2)(length H2')))
  (VALQ2: val_qual (length2 (st_empty S1 S2)) (H2' ++ H2) v2 pempty pempty)
  (Y: q1 = qempty),  
  indexr x (G'++T1::G) = Some T ->
  plift p x ->
  exists S1'' S2'' M'' v1'' v2'',
  exp_type1 S1 S2 M (H1' ++ v1 :: H1) (H2' ++ H2) 
    (tvar x) (subst_tm (tvar x) (length H2) (splice_tm t1 (length H2) (length H2')) q1) 
    S1'' S2'' M'' v1'' v2'' 
     T  (subst_ty T (length H2) q1)
     (plift p) (plift (subst_ql p (length H2) q1))
    (pone x) (plift (subst_ql (qone x) (length H2) q1))
    pempty pempty.
Proof.  
  intros. 
  bdestruct (x =? length H2); bdestruct (x <? length H2); intuition.
  - exists S1, S2'', (length S1, length S2'', strel M).
    simpl. 
    subst x. rewrite L2 in H.
    exists v1, v2.
    assert (T = T1).
    rewrite indexr_skips in H.  rewrite indexr_head in H. inversion H.  simpl. auto.  simpl. lia. subst T. 
    bdestruct (length H2 =? length H2); intuition.
    assert (st_chain M (length S1, length S2'', strel M)) as STC3. {
      unfold st_chain.
      assert (st_chain_partial M (length S1, length S2'', strel M) (st_locs1 M) (st_locs2 M)). {
        unfold st_chain_partial. repeat split.
        intros ? ?. auto.
        intros ? ?. unfold st_locs1, pnat in *. unfold length1. simpl in *. destruct ST2; intuition.
        intros ? ?. auto.
        intros ? ?. unfold st_locs2, pnat in *. unfold length2. simpl in *. destruct ST2; intuition.
        intros. unfold strel in *. simpl in *. auto.
      } 
      assert (st_chain_partial2 (length S1, length S2'', strel M) M (st_locs1  M) (st_locs2 M)). {
        unfold st_chain_partial2. repeat split.
        intros ? ?. unfold st_locs1, pnat in *. unfold length1. simpl in *. destruct ST2; intuition.
        intros ? ?. auto.
        intros ? ?. unfold st_locs2, pnat in *. unfold length2. simpl in *. destruct ST2; intuition.
        intros ? ?. auto.
        intros. unfold strel in *. simpl in *. auto.
      }
      intuition.
    }

    split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 8: split. 
    + eexists. intros. destruct n. lia. simpl.
    rewrite L2. rewrite <- L1. rewrite indexr_skips. rewrite indexr_head. auto. simpl. lia.
    + auto.
    + intros ? ?. intros. auto.
    + intros ? ? ? ?. auto.
    + auto.
    + destruct ST2 as [? [? [? ?]]].  unfold store_type; intuition. 
      specialize (H7 l1 l2); intuition. destruct H11 as [? [? [? [? ?]]]].
      specialize (EFF2 l2 (vbool x0)); intuition. exists x, x0; intuition.
    + rewrite substy_id. rewrite splicety_id in VALT.
      apply valt_closed in VALT as CL.  
      rewrite <- valt_extend  with (H1':= (H1'++[v1]))(H2':=[]) in VALT; eauto.
      simpl in VALT. replace ((H1'++[v1])++H1) with (H1'++v1::H1) in VALT.
      eapply valt_store_extend; eauto. eapply st_mono2 in STC3. auto.
      rewrite <- app_assoc. simpl. auto. intuition. intuition.
      1-2: rewrite L2; auto. 
    + (* valq1 *)
      intros ? ?. exists (length H2). unfoldq. intuition.
      exists v1. intuition.
      eapply WFE in H. 
      destruct H as [v1' [v2' [? ?]]].
      rewrite <- L1 in H. rewrite indexr_skips. rewrite L2. rewrite <-L1.  rewrite indexr_head. auto.
      simpl. lia. rewrite <- L2. auto.
    + (* valq2 *)
      rewrite L2 in *.
      rewrite substq_hit. unfoldq; intuition.
      destruct (VALQ2 x) as [? [? [? ?]]]; intuition.
      unfold length2, st_empty. simpl. destruct ST2; intuition.

  - (* length G > x*)
      exists S1, S2, M.
      simpl. rewrite L2 in *.
      destruct WFE as [WL1 [WL2 [DP1 [DP2 [P1 [P2 P3]]]]]].
      destruct (P1 x T H H0) as [vx1 [vx2 [IX1 [IX2 IVT]]]].
      destruct IVT as [IVT1 [IVT2 IVT3]].
      bdestruct (length G <? x); intuition. 
      bdestruct (length G =? x); intuition.
      rename H6 into IX2.
      exists vx1, vx2; intuition. 
      split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 8: split. 
      
      -- eexists. intros. destruct n. lia. simpl. rewrite IX1. auto.  
      -- eexists. intros. destruct n. lia. simpl. rewrite IX2. auto. 
      -- intros ? ?. intros. auto.
      -- intros ? ?. intros. auto.
      -- eapply st_refl.
      -- auto.
      -- auto. 
      -- (* valq1 *)  
         unfoldq; intuition.
         exists x. unfoldq; intuition.
         exists vx1; intuition.
      -- (* valq2 *)
         unfoldq; intuition. unfoldq; intuition.
         exists x. intuition.
         eapply substq_mem2; eauto.
         rewrite plift_subst, plift_one. 
         unfold subst_pl. right. right.
         unfoldq; intuition.
         exists vx2; intuition.
  - exists S1, S2, M.
    simpl.
    destruct WFE as [WL1 [WL2 [DP1 [DP2 [P1 [P2 P3]]]]]].
    destruct (P1 x T H H0) as [vx1 [vx2 [IX1 [IX2 IVT]]]].
    destruct IVT as [IVT1 [IVT2 IVT3]].
    bdestruct (length G <? x); intuition.
    bdestruct (length H2 =? x); intuition.
    bdestruct (length H2 <? x); intuition.
    exists vx1, vx2; intuition. 
    split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 8: split. 
    + eexists. intros. destruct n. lia. simpl. rewrite IX1. auto.  
    + eexists. intros. destruct n. lia. simpl. replace (Init.Nat.pred x) with (x - 1). rewrite H6. auto. lia.
    + intros ? ? ? ?. auto.
    + intros ? ? ? ?. auto.
    + eapply st_refl.
    + auto.
    + rewrite L2. auto. 
    + (* valq1 *) 
      unfoldq; intuition. unfoldq; intuition.
      exists x; intuition. 
      exists vx1; intuition.
    + unfoldq; intuition. exists (x-1). unfoldq; intuition. 
      1,2: rewrite L2 in *. eapply substq_mem; eauto.
      rewrite plift_subst, plift_one. unfold subst_pl.
      right. left. intuition. unfoldq; intuition. 
      exists vx2. intuition. 
    
Unshelve. all: eauto. apply 0.
Qed. 

Lemma bi_tref_subst: forall S1 S2 M H1' H2' H1 H2 v1 t t1 q e q1 S1' S2' M' v1' v2' p
  (ST: store_type S1 S2 M),
  exp_type1 S1 S2 M (H1' ++ v1 :: H1) (H2' ++ H2) 
	  t (subst_tm t (length H2) (splice_tm t1 (length H2) (length H2')) q1)
    S1' S2' M' v1' v2' TBool TBool
    (plift p) (plift (subst_ql p (length H2) q1))
    (plift q) (plift (subst_ql q (length H2) q1))
    (plift e) (plift (subst_ql e (length H2) q1)) 
  ->
exists (S1'' S2'' : stor) (M'' : stty) (v1'' v2'' : vl),
  exp_type1 S1 S2 M (H1' ++ v1 :: H1) (H2' ++ H2)
    (tref t) (subst_tm (tref t) (length H2) (splice_tm t1 (length H2) (length H2')) q1) 
    S1'' S2'' M'' v1'' v2''
    (TRef TBool) (TRef TBool)
    (plift p) (plift (subst_ql p (length H2) q1))
    (plift q) (plift (subst_ql q (length H2) q1))
    (plift e) (plift (subst_ql e (length H2) q1)).
Proof. 
  intros.
  destruct H as [IE1 [IE2 [EFF1 [EFF2 [STC1 [ST1 [HV [HQ1 HQ2]]]]]]]].

  remember ST1 as ST1'. clear HeqST1'.
  destruct ST1 as [SL1 [SL2 [SP3 [SP4 SP5]]]].
  remember HV as  HV'. clear HeqHV'.
  
  destruct v1'; destruct v2'; try solve [inversion HV].
  exists ((vbool b)::S1'), ((vbool b0)::S2'), (st_extend M').
  exists (vref (length S1')), (vref (length S2')).

  split.

  (* 1st term *)
  destruct IE1 as [n1 IE1].
  exists (S n1). intros. destruct n. lia. simpl. rewrite IE1.  auto. lia.

  split.
  (* 2nd term *)
  destruct IE2 as [n2 IE2].
  exists (S n2). intros. destruct n. lia. simpl. rewrite IE2. auto. lia.
  
  split.
  (* effects 1 *)
  eapply se_trans. eauto. intros ? ?. intros. eapply indexr_extend1 in H0. eapply H0.
  
  split.
  (* effects 2 *)
  eapply se_trans. eauto. intros ? ?. intros. eapply indexr_extend1 in H0. eapply H0.

  split.
  eapply st_trans. eauto. eapply stchain_extend.
  
  (* store_typing *)
  split.
  eapply storet_extend; eauto.
  
  split.
  (* result type *)
  simpl. intuition.
  unfold length1, st_extend. simpl. lia.
  unfold length2, st_extend. simpl. lia.

  split.
  rewrite SL1. eapply valq_fresh1; eauto.
  
  rewrite SL2. eapply valq_fresh2; eauto.
  
Qed.

Lemma bi_tget_subst: forall S1 S2 M H1' v1 H11 H2' H12 t t1 q e q1 S1' S2' M' v1' v2' p,
  exp_type1 S1 S2 M (H1' ++ v1 :: H11)  (H2' ++ H12) 
     t (subst_tm t (length H12) (splice_tm t1 (length H12) (length H2')) q1) 
     S1' S2' M' v1' v2' 
     (splice_ty (subst_ty (TRef TBool) (length H12) q1)  (length H12) 1) (subst_ty (TRef TBool) (length H12) q1)
     (plift p) (plift (subst_ql p (length H12) q1))
     (plift q) (plift (subst_ql q (length H12) q1))
     (plift e) (plift (subst_ql e (length H12) q1))
  ->
  exists (S1'0 S2'0 : stor) (M'0 : stty) (v1'0 v2'0 : vl),
    exp_type1 S1 S2 M (H1' ++ v1 :: H11) (H2' ++ H12) 
      (tget t) (subst_tm (tget t) (length H12) (splice_tm t1 (length H12) (length H2')) q1)
      S1'0 S2'0 M'0 v1'0 v2'0 
      TBool (subst_ty TBool (length H12) q1)
      (plift p) (plift (subst_ql p (length H12) q1))
      (plift qempty) (plift (subst_ql qempty (length H12) q1))
      (plift (qor e q)) (plift(subst_ql (qor e q) (length H12) q1)).
Proof.  
  intros.

  destruct H as [EV1 [EV2 [EFF1 [EFF2 [HSTC [HST [HV [HQ1 HQ2]]]]]]]].
  destruct v1'; destruct v2'; try solve [inversion HV]. simpl in HV.
  
  destruct HV as [HT [? [LS1 [LS2 VT]]]].
  remember HST as HST'. clear HeqHST'.
  destruct HST as [STL1 [STL2 [SP1 [SP2 SP3]]]].

  destruct (SP1 i i0 VT) as [b1 [b2 [IY1 [IY2 EQ]]]]. 

  exists S1', S2', M', (vbool b1), (vbool b2). 
  split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 8: split. 
  + destruct EV1 as [n1 IW1].
    exists (S n1). intros. destruct n. lia. simpl.
    rewrite IW1. rewrite IY1. eauto. lia.
  + destruct EV2 as [n1 IW2].
    exists (S n1). intros. destruct n. lia. simpl.
    rewrite IW2. rewrite IY2. eauto. lia.
  + (* effects 1 *)
    eapply se_sub; eauto. intros ? ?.  auto.
  + (* effects 2 *)
    eapply se_sub; eauto. intros ? ?. auto.
    
  + auto.
  + auto.
  + subst b2.
    constructor; eauto.
  + eapply valq_bool.
  + eapply valq_bool. 
Qed.


Lemma bi_tput_subst: forall S1 S2 M H1' v1 H11 H2' H12 t1 t2 t0 q1 q0 S1' S2' M' v1' v2' S1'' S2'' M'' v3 v4 q2 e1 e2 p
  (ST: store_type S1 S2 M)
  (E1: exp_type1 S1 S2 M (H1' ++ v1 :: H11) (H2' ++ H12) 
          t1 (subst_tm t1 (length H12) (splice_tm t0 (length H12) (length H2')) q0)
          S1' S2' M' v1' v2'
          (TRef TBool)  (subst_ty (TRef TBool) (length H12) q0)
          (plift p) (plift (subst_ql p (length H12) q0))
          (plift q1) (plift (subst_ql q1 (length H12) q0))
          (plift e1) (plift (subst_ql e1 (length H12) q0)))
  (E2: exp_type1 S1' S2' M' (H1' ++ v1 :: H11) (H2' ++ H12) 
          t2 (subst_tm t2 (length H12) (splice_tm t0 (length H12) (length H2')) q0)
          S1'' S2'' M'' v3 v4 
          TBool (subst_ty TBool (length H12) q0)
          (plift p) (plift (subst_ql p (length H12) q0))
          (plift q2) (plift (subst_ql q2 (length H12) q0))
          (plift e2) (plift (subst_ql e2 (length H12) q0)))
  (EMP: q0 = qempty), 
  exists (S1'0 S2'0 : stor) (M'0 : stty) (v1'0 v2'0 : vl),
    exp_type1 S1 S2 M (H1' ++ v1 :: H11) (H2' ++ H12)
      (tput t1 t2) (subst_tm (tput t1 t2) (length H12) (splice_tm t0 (length H12) (length H2')) q0) 
      S1'0 S2'0 M'0 v1'0 v2'0 
      TBool (subst_ty TBool (length H12) q0)
      (plift p) (plift (subst_ql p (length H12) q0))
      (plift qempty) (plift (subst_ql qempty (length H12) q0))
      (plift (qor e1 (qor e2 q1))) (plift (subst_ql (qor e1 (qor e2 q1)) (length H12) q0)). 
Proof.
  intros. 
  destruct E1 as [IE1 [IE2 [EFF1 [EFF2 [STC1 [ST1 [HV [HQ1 HQ2]]]]]]]].
  destruct v1'; destruct v2'; try solve [inversion HV]. simpl in HV.
  destruct HV as [HT [LS1 [LS2 VT]]].
  remember ST1 as ST1'. clear HeqST1'.
  destruct ST1 as [STL1 [STL2 [SP1 [SP2 SP3]]]].

  destruct E2 as [IE3 [IE4 [EFF3 [EFF4 [STC2 [ST2 [HV1 [HQ3 HQ4]]]]]]]].
  destruct v3; destruct v4; try solve [inversion HV1]. simpl in HV1.
  subst b0.
  remember ST2 as ST2'. clear HeqST2'.
  destruct ST2 as [STL3 [STL4 [SP4 [SP5 SP6]]]].

  exists (update S1'' i (vbool b)), (update S2'' i0 (vbool b)).
  exists M''.
  exists (vbool true), (vbool true).

  split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 8: split.
  (* first one *)
  destruct IE1 as [n1 IE1].
  destruct IE3 as [n3 IE3].
  exists (S(n1 + n3)). intros. destruct n. intuition.
  simpl. rewrite IE1. rewrite IE3.
  assert (i < length S1''). rewrite STL3. eapply st_mono1'; eauto.
  apply indexr_var_some in H0. destruct H0. rewrite H0. auto. lia. lia.
  
  destruct IE2 as [n2 IE2].
  destruct IE4 as [n4 IE4].
  exists (S(n2 + n4)). intros. destruct n. intuition.
  simpl. rewrite IE2. rewrite IE4. 
  assert (i0 < length S2''). rewrite STL4. eapply st_mono2'; eauto. lia.
  apply indexr_var_some in H0. destruct H0. rewrite H0. auto. lia. lia.

  (* effects  *)
  intros ? ? ? ?.  
  assert (length S1 = length1 M). destruct ST as (? & ? & ?). eauto.
  bdestruct (i =? l). { subst. destruct (HQ1 l).
  rewrite val_locs_ref. eapply indexr_var_some' in H0. unfoldq; intuition.
  destruct H. exists x. unfoldq; intuition.  
  }{ rewrite update_indexr_miss. eauto. eauto. }

  intros ? ?. intros.
  assert (length S2 = length2 M). destruct ST as (? & ? & ?). eauto.
  bdestruct (i0 =? l). { subst. destruct (HQ2 l).
  rewrite val_locs_ref. eapply indexr_var_some' in H0. unfoldq. intuition.
  destruct H. exists x. unfoldq. intuition. 
  }{ rewrite update_indexr_miss. eauto. eauto. }  

  eapply st_trans; eauto.
  
  (* store typing *)
  eapply storet_update; eauto. eapply valt_store_extend; eauto. 
  simpl. intuition. eapply st_mono2 in STC2; auto.
  simpl. eauto. 

  (* valt *)
  constructor.

  (* valq *)
  eapply valq_bool. eapply valq_bool.
Unshelve. all: auto.
Qed.


Lemma bi_tapp_subst: forall M H1 H1' H2 H2' G' G q0 p q1 S1 S2 v1 f S1' S2' M' vf1 vf2 T1 T2 q2 e2 qf ef t S1'' S2'' M'' vx1 vx2 t1 e1 T0 v2'0 
  (WFE: env_type_subst2 M (H1'++v1::H1) (H2'++ H2) (G'++T0::G) p (length G) v2'0 q0)
  (ST: store_type S1 S2 M)
  (IEF: exp_type1 S1 S2 M (H1' ++ v1 :: H1) (H2' ++ H2)
           f (subst_tm f (length H2)(splice_tm t1 (length H2) (length H2')) q0) 
           S1' S2' M' vf1 vf2
           (TFun T1 T2 q2 e2) (subst_ty (TFun T1 T2 q2 e2) (length H2) q0)
           (plift p) (plift (subst_ql p (length H2) q0))
           (plift qf) (plift (subst_ql qf (length H2) q0))
           (plift ef) (plift (subst_ql ef (length H2) q0)))
  (IEX: exp_type1 S1' S2' M' (H1' ++ v1 :: H1) (H2' ++ H2)
          t (subst_tm t (length H2)(splice_tm t1 (length H2) (length H2')) q0) 
          S1'' S2'' M'' vx1 vx2 
          T1 (subst_ty T1 (length H2) q0)
          (plift p) (plift (subst_ql p (length H2) q0))
          (plift q1) (plift (subst_ql q1 (length H2) q0))
          (plift e1)  (plift (subst_ql e1 (length H2) q0)))
  (QSEP: psub (pand (plift qf) (plift q1)) pempty)
  (Q2:   psub (plift q2) (plift p))
  (E2:   psub (plift e2) (plift p))
  (A:    psub (pand (pand (pdom (G'++G))(plift p))(plift q0)) pempty)
  (L:    length G = length H2)
  (EMP:  q0 = qempty), 
exists (S1'0 S2'0 : stor) (M'0 : stty) (v1' v2' : vl),
  exp_type1 S1 S2 M (H1' ++ v1 :: H1) (H2' ++ H2)
    (tapp f t) (subst_tm (tapp f t) (length H2) (splice_tm t1 (length H2)(length H2')) q0) 
    S1'0 S2'0  M'0 v1' v2' 
    T2 (subst_ty T2 (length H2) q0)
    (plift p) (plift (subst_ql p (length H2) q0))
    (plift (qor q2 q1)) (plift (subst_ql (qor q2 q1) (length H2) q0))
    (plift (qor ef (qor e1 (qor q1 e2)))) (plift (subst_ql (qor ef (qor e1 (qor q1 e2))) (length H2) q0)).
Proof.   
  intros. 
  remember WFE as WFE'.
  clear HeqWFE'.
  destruct WFE as [L1 [L2 [PD1 [PD2 [P1 [P2 P3]]]]]].
  destruct IEF as [IEF1 [IEF2 [EFF1 [EFF2 [STC1 [ST1 [HVF [HQF1 HQF2]]]]]]]].
  destruct IEX as [IEX1 [IEX2 [EFF3 [EFF4 [STC2 [ST2 [HV2 [HQX1 HQX2]]]]]]]].

  destruct vf1; destruct vf2; try solve [inversion HVF]; simpl in HVF; intuition.
  rename H13 into HVF.

   assert ( psub (pand (val_locs (vabs l q t0)) (val_locs vx1)) pempty). { 
    eapply separation_subst1; eauto.
  }
  assert ( psub (pand (val_locs (vabs l0 q3 t2)) (val_locs vx2)) pempty). { 
    eapply separation_subst2; eauto.
  }
  
  destruct (HVF S1'' S2'' M'' vx1 vx2) as [S1'''[S2''' [M''' [r1 [r2 [IAPP1 [IAPP2 [STCY [STY [EFF5 [EFF6  [IVALY [HQY1 HQY2]]]]]]]]]]]]]; auto.
  eapply stchain_tighten; eauto. eapply STC2.
  eapply stchain_tighten'; eauto. eapply STC2.
  eapply st_mono2 in STC2. auto.
  
  exists S1''', S2''', M'''.
  exists r1. exists r2.

  split.
  (* 1st function *)
  destruct IEF1 as [n1 IEF1].
  destruct IEX1 as [n2 IEX1].
  destruct IAPP1 as [n3 IAPP1].
  exists (S (n1+n2+n3)). 
  (* - forall greater fuel *)
  intros. destruct n. lia.
  (* - result computes *)
  simpl. rewrite IEF1. rewrite IEX1. rewrite IAPP1. auto. lia. lia. lia.
  
  split.
  (* 2nd function *)
  destruct IEF2 as [n1 IEF2].
  destruct IEX2 as [n2 IEX2].
  destruct IAPP2 as [n3 IAPP2].
  exists (S (n1+n2+n3)). 
  (* - forall greater fuel *)
  intros. destruct n. lia.
  (* - result computes *)
  simpl. rewrite IEF2. rewrite IEX2. rewrite IAPP2. auto. lia. lia. lia.
  
  split.
  (* effect1 *)
  intros ? ? ? ?. rewrite EFF5. eauto. 2: eauto.
  assert (l1 < length1 M). { eapply indexr_var_some' in H15. destruct ST as (L' & ?). lia. }
  intros ?. eapply H14. destruct H17. {
    destruct (HQF1 l1). unfoldq. intuition.
    exists x. unfoldq. intuition.
  } {
    destruct (HQX1 l1). unfoldq. intuition. eapply st_mono1'; eauto.
    exists x. unfoldq. intuition.
  }
  
  
  split.
  (* effect2*)
  intros ? ? ? ?. rewrite EFF6. eauto. 2: eauto.
  assert (l1 < length2 M). { eapply indexr_var_some' in H15. destruct ST as (L' & ?). lia. }
  intros ?. eapply H14. destruct H17. {
    destruct (HQF2 l1). unfoldq. intuition.
    exists x. unfoldq. intuition.
  } {
    destruct (HQX2 l1). unfoldq. intuition. eapply st_mono2'; eauto.
    exists x. unfoldq. intuition.
  }

  split.
  eapply st_trans. eapply st_trans. eauto. eauto. eauto. 

  (* store typing *)
  split. auto.
  split. auto.
  
  split.
  (* 1st qual *)
  remember (vabs l q t0) as vf1.
  unfoldq. intros.
  destruct (HQY1 x). intuition. eapply st_mono1'; eauto. eapply st_mono1'; eauto. 

  (* part of function *)
  destruct (HQF1 x). intuition.       
  destruct H15. destruct H15.
  exists x1. intuition. rewrite plift_or. unfoldq; intuition. 
  (* part of argument *)
  destruct (HQX1 x). intuition. eapply st_mono1'; eauto.
  
  exists x0. intuition.   
  rewrite plift_or.
  unfoldq; intuition.
    
  (* 2nd qual *)
  remember (vabs l0 q3 t2) as vf2. 
  eapply result_reach2; eauto.
Qed.

Lemma bi_tabs_subst: forall H1 H1' H2 H2' G G' q1 p S1 S2 M T1 T2 q2 e2 qf t1 t v1 v2'0 
  (WFE: env_type_subst2 M (H1'++ v1::H1) (H2'++ H2) (G'++TBool::G) p (length G) v2'0 q1)
  (L1: length H1 = length G)
  (L2: length H2 = length G)
  (L3: length H1' = length G')
  (L4: length H2' = length G')
  (ST: store_type S1 S2 M)
  (EXP: forall M H1 H1' H2 H2' v1 v2'0,
   val_type M H1 H2 v1 v2'0 TBool TBool ->
   env_type_subst2 M (H1' ++ v1 :: H1) (H2' ++ H2) (T1 :: G' ++ TBool :: G) (qor (qand p qf) (qone (length (G' ++ TBool :: G)))) (length G) v2'0 q1 ->
      forall S1 S2,
      length H1 = length G ->
      length H2 = length G ->
      length H1' = length (T1 :: G') ->
      length H2' = length (T1 :: G') ->
      store_type S1 S2 M ->
      (forall H2'' S2',
        length S2 <= length S2' ->
       exists v2 M'' S2'',
         tevaln S2' (H2'' ++ H2) (splice_tm t1 (length H2) (length H2'')) S2'' v2 /\
         store_effect S2' S2'' pempty /\
         length S2' <= length S2'' /\
         val_type M'' H1 (H2'' ++ H2) v1 v2 TBool TBool  /\
         val_qual (length1 (st_empty S1 S2)) H1 v1 pempty pempty /\
         val_qual (length2 (st_empty S1 S2)) (H2'' ++ H2) v2 pempty pempty 
      ) 
       ->
      exists
        (S1' S2' : stor) (M' : stty) (v1' v2' : vl),
        exp_type1 S1 S2 M (H1' ++ v1 :: H1) (H2' ++ H2) 
        	t (subst_tm t (length H2) (splice_tm t1 (length H2) (length H2')) q1) 
        	S1' S2' M'  v1' v2'
          T2 (subst_ty T2 (length H2) q1)
          (plift (qor (qand p qf)(qone (length (G' ++ TBool::G)))))
          (plift (subst_ql (qor (qand p qf)(qone (length (G' ++ TBool::G)))) (length H2) q1))
          (plift (qor q2 (qone (length (G' ++ TBool :: G)))))
          	(plift (subst_ql (qor q2 (qone (length (G' ++ TBool :: G)))) (length H2) q1))
          (plift (qor e2 (qone (length (G' ++ TBool :: G)))))
          	(plift (subst_ql (qor e2 (qone (length  (G' ++  TBool :: G)))) (length H2)  q1)) 
  )
  (CLF:  closed_ty ((length G'+ S (length G))) (TFun T1 T2 q2 e2))
  (CLQ1: closed_ql (length G) q1)
  (SEP: psub (pand (pand (pdom ((T1 :: G') ++ G)) (plift (qor (qand p qf) (qone (length (G' ++ TBool :: G)))))) (plift q1)) pempty)
  (VALT: val_type M H1 H2 v1 v2'0  TBool TBool)
  (EMP: q1 = qempty)
  (STW: forall H2'' S2' : list vl,
      length S2 <= length S2' ->
      exists  (v2 : vl) (M'' : stty)  (S2'' : stor),
        tevaln S2' (H2'' ++ H2) (splice_tm t1 (length H2) (length H2'')) S2'' v2 /\
        store_effect S2' S2'' pempty /\
        length S2' <= length S2'' /\
        val_type M'' H1 (H2'' ++ H2) v1 v2   TBool TBool /\
        val_qual (length1 (st_empty S1 S2)) H1 v1 pempty pempty /\
        val_qual (length2 (st_empty S1 S2)) (H2'' ++ H2) v2 pempty pempty)
  ,
exists (S1' S2' : stor) (M' : stty) (v1' v2' : vl),
  exp_type1 S1 S2 M (H1' ++ v1 :: H1) (H2' ++ H2)
    (tabs (qand p qf) t) (subst_tm (tabs (qand p qf) t) (length H2) (splice_tm t1 (length H2) (length H2')) q1) 
    S1' S2' M' v1' v2'
    (TFun T1 T2 q2 e2) (subst_ty (TFun T1 T2 q2 e2) (length H2) q1)
    (plift p) (plift (subst_ql p (length H2) q1))
    (plift qf) (plift (subst_ql qf (length H2) q1))
    (plift qempty) (plift (subst_ql qempty (length H2) q1)).
Proof.    
  intros. 
  apply wf_env_type_subst2 in WFE as WFE'. 
  destruct WFE' as [PD1 [PD2 [PD3 PD4]]].
  remember WFE as WFE'. clear HeqWFE'.
  destruct WFE' as [L1' [L2' [P1 [P2 P3]]]].

  remember ST as ST'. clear HeqST'.
  destruct ST as [SL1 [SL2 [SP1 [SP2 SP3]]]].
  
  exists S1, S2, M.
  exists (vabs (H1'++v1::H1) (qand p qf) t). 
  exists (vabs (H2'++ H2) (subst_ql (qand p qf) (length H2) q1) (subst_tm t (length H2) (splice_tm t1 (length H2)(1+length H2')) q1)).
  split.
  
  (* 1st *)
    exists 0.  intros. destruct n. lia. simpl. eauto.
  split.
   (* 2nd *)
    exists 0.  intros. destruct n. lia. simpl. rewrite splice_acc. auto.
  split.

  intros ? ? ? ?. auto. 
  split.
  intros ? ? ? ?. auto. 
  split. apply st_refl.
   (* store typing *)  
  split. auto.
   
  
  inversion CLF. subst.
  (* results *)
  repeat split; intuition; rewrite app_length in *. 
  

  1,2: rewrite L1'; rewrite app_length;  simpl; auto. 
  1,2: rewrite L2, L4; eapply substy_closed_gen;  eauto.   
  unfoldq; intuition.
  eapply H8 in H4. rewrite app_length in *.  simpl. lia.
  
  rewrite plift_subst, plift_empty.
  eapply Q2. intros ? ?. eapply H8 in H4. 
  unfoldq; intuition.  rewrite app_length in *. simpl. eauto.
  
  auto. auto.

  intros ? ?. eapply H9 in H4. unfoldq; intuition.  rewrite app_length in *. simpl. lia. 
  
  rewrite plift_subst, plift_empty.
  eapply Q2. intros ? ?. eapply H9 in H4. unfoldq; intuition.  rewrite app_length in *. eauto. 
  
  auto. auto.
   
  rewrite val_locs_abs.
  eapply envt_subst_store_wf1; eauto. intros ? ?. rewrite plift_and in H4. unfoldq; intuition.
  
  rewrite val_locs_abs.  
  eapply envt_subst_store_wf2; eauto.
  eapply substp_sub. intros ? ?. rewrite plift_and in H4. unfoldq; intuition.

  assert (exists b, v1 = (vbool b) /\ v2'0 = (vbool b)) as X. {
    destruct v1; destruct v2'0; try inversion VALT. 
    subst b. exists b0; intuition.
  }
  destruct X as [b [X1 X2]].

  (* strel same locs *)
  rewrite val_locs_abs in *. rewrite plift_subst.
  edestruct envt_same_locs_subst with (p1 := (plift (qand p qf))). 9: eapply WFE. 
  1-4: auto. eauto. eauto. eauto. eauto. eauto. 
  rewrite plift_and. intros ? ?. unfoldq. intuition. rewrite L2. auto. 

  assert (exists b, v1 = (vbool b) /\ v2'0 = (vbool b)) as X. {
    destruct v1; destruct v2'0; try inversion VALT. 
    subst b. exists b0; intuition.
  }
  destruct X as [b [X1 X2]].

   

  rewrite val_locs_abs in *. rewrite plift_subst in H0.
  edestruct envt_same_locs_subst with (p1 := (plift (qand p qf))). 
  9: eapply WFE. 1-4: auto. eauto. eauto. eauto. eauto. eauto.
  rewrite plift_and. intros ? ?. unfoldq. intuition. eapply H13. rewrite <- L2. auto. 
    
  rewrite val_locs_abs in *.  
  rewrite plift_subst in H16. 
  assert (exists b, v1 = (vbool b) /\ v2'0 = vbool b) as X. {
    destruct v1; destruct v2'0; try inversion VALT.
    subst b0. exists b. intuition.
  }
  destruct X as [b [X1 X2]].
  assert (env_type_subst2 M' 
            (vx1::H1'++v1::H1)  (vx2 :: H2'++H2) (T1:: G'++TBool::G)  
            (qor (qand p qf) (qone (length (G' ++ TBool :: G)))) (length G) v2'0 qempty) as WFE'.
 
  eapply envt_subst_extend_all in WFE; eauto.
  rewrite val_locs_abs in H4. eapply H4.
  rewrite val_locs_abs in H11. eapply H11. 
     
  intros ? ?. rewrite plift_subst in H17. unfoldq; intuition.
  eapply H16; eauto.
  
  assert (st_chain_partial M M' (val_locs v1) (val_locs v2'0)). {
    destruct v1; destruct v2'0; try inversion VALT.
    rewrite val_locs_bool. 
    unfold st_chain_partial. repeat split.
    intros ? ?. unfoldq; intuition.
    intros ? ?. unfoldq; intuition.
    intros ? ?. unfoldq; intuition.
    intros ? ?. unfoldq; intuition.
    intros. unfoldq; intuition.
  }

  assert (st_chain_partial2 M' M (val_locs v1) (val_locs v2'0)). {
    destruct v1; destruct v2'0; try inversion VALT.
    rewrite val_locs_bool. 
    unfold st_chain_partial2. repeat split.
    intros ? ?. unfoldq; intuition.
    intros ? ?. unfoldq; intuition.
    intros ? ?. unfoldq; intuition.
    intros ? ?. unfoldq; intuition.
    intros. unfoldq; intuition.
  }
  

  assert (val_type M' H1 H2 v1 v2'0 TBool TBool) as VT.
  eapply valt_store_change; eauto.
  

  rewrite app_length in WFE'. simpl in WFE'.
        
  specialize (EXP M' H1 (vx1::H1') H2 (vx2::H2') v1 v2'0 VT WFE' S1' S2') as [S1'' [S2'' [M'' [vy1 [vy2 IEY]]]]].
  auto.  auto. simpl. auto. simpl. auto. auto. 
  
  intros. 
  assert (length S2 <= length S2') as LS1. {
    destruct H13; intuition.
  }

  assert (length S2 <= length S2'0) as LS2. {
     lia.
  }
  destruct (STW H2'' S2'0) as [v2X [MX [S2X [? [? [? [? [? ?]]]]]]]]; auto.
  exists v2X, MX, S2X; intuition.
  1,2: destruct v1; destruct v2X; try inversion H23; unfoldq; intuition.

  
  destruct IEY as [IEY1 [IEY2 [YEFF1 [YEFF2 [YSTC [YST [IVY [IYQ1 IYQ2]]]]]]]].
   
  rewrite plift_subst, plift_or, plift_one in *.
  exists S1'', S2'', M'', vy1, vy2. intuition.
  
  (* effects 1 *)
  
  intros ? ? PV ?. eapply YEFF1. intros VL. eapply PV.
   destruct VL as (? & VL & ?).
   destruct VL. {
     left. exists x. split. eauto. eapply var_locs_shrink. eauto. 
     assert (plift p x). rewrite plift_and in H21. unfoldq; intuition.
     eapply H0 in H22. unfoldq; intuition.
   } {
     right. destruct H20. replace x with (length (H1'++v1::H1)) in H20.
     replace ((vx1 :: H1') ++ v1 :: H1) with (vx1::(H1'++v1::H1)) in H20. 
     rewrite indexr_head in H20. intuition. congruence. simpl. auto.
     unfoldq. rewrite app_length. simpl in*. intuition. 
   }
   eauto.

   (* effects 2 *)
   intros ? ? PV ?. eapply YEFF2. intros VL. eapply PV.
   rewrite val_locs_abs in*. rewrite substp_or in VL. rewrite substq_empty_and. 
   repeat rewrite  plift_and, plift_subst, plift_empty in *. 
   destruct VL as (? & VL & ?).
   destruct VL. {
     left. exists x. rewrite substp_empty_and in H21. intuition.
     destruct H21. eapply Q2 in H21. simpl in H20. eapply var_locs_shrink in H20. auto.
     unfold pdom in H21. eauto. 
     intros ? ?. unfold pdom. eapply P1 in H23. unfold pdom in H23. rewrite app_length in *. simpl in *. 
     2: eauto. 2: eauto. lia.
   } {
     right. destruct H18. 
     unfoldq; intuition. destruct H20 as [? [? ?]].
     eapply indexr_var_some' in H20 as H20'. rewrite app_length in H20'.
     unfold subst_pl in H21.  simpl in *; intuition.
     assert (x = length G' + length G). lia.
     bdestruct (x =? length (H2'++H2)); intuition. inversion H20. congruence.
     rewrite app_length in H31; intuition.
   }
   eauto.
 
  
  (* valt *)
  eapply valt_extend1; eauto.
  rewrite app_length in *.  rewrite  L1'. auto.
  
  replace (length (H2'++H2)) with (length G'+ length G).
  rewrite L2. 
  eapply substy_closed_gen; eauto.
  rewrite app_length.  lia.
  
  (* qual 1 *) 
  rewrite val_locs_abs in *. rename H14 into HVX;
  apply valt_wf in HVX; apply valt_wf in IVY.
   
  unfoldq. intuition.
  destruct (IYQ1 x). eauto. 
  unfoldq. 
  destruct H22. destruct H22. 
  bdestruct (x0 =? length G'+S(length G)).
  (* from arg *)
    right. destruct H25 as [? [? ?]]. 
    replace (length G'+S(length G)) with (length (H1'++v1::H1)) in H27.
    subst x0.
    replace ((vx1::H1')++v1::H1) with (vx1::(H1'++v1::H1)) in H25.
    rewrite indexr_head in H25. inversion H25. eauto.
    simpl. auto. repeat rewrite app_length. simpl. lia.
  (* from func *)
    unfoldq. left. split. 
    exists x0. intuition. rewrite plift_or in H26.
    destruct H26. auto. rewrite plift_one in H22. unfoldq; intuition. 
    destruct H25 as [? [? ?]]. 
    replace ((vx1::H1')++v1::H1) with (vx1::(H1'++v1::H1)) in H22.
    rewrite indexr_skip in H22. 
    exists x1. split; eauto. 
    repeat rewrite app_length in *. simpl. lia.  simpl. auto.
       
    destruct H25 as [? [? ?]]. rewrite <- L1 in H27. rewrite <- L3 in H27. 
    replace ((vx1::H1')++v1::H1) with (vx1::(H1'++v1::H1)) in H25.
    rewrite indexr_skip in H25; eauto.
    exists x0. intuition. exists x1. auto. 
    rewrite app_length in *. simpl in *. lia. 

    exists x1; intuition. rewrite app_length. simpl. lia. simpl. auto.

   (* 2nd *)
  rewrite substp_or, plift_and, plift_empty in IYQ2. rewrite substp_empty_and in IYQ2.
  rewrite plift_subst, plift_or, plift_one, plift_empty, substp_or in IYQ2. 
  rewrite val_locs_abs in *. rewrite plift_subst in *. 
  intros ? ?.
  destruct (IYQ2 x). eauto.
  unfoldq. rewrite plift_empty, plift_and, substp_empty_and.
  destruct H20.  destruct H20.
  bdestruct (x0 =? length (H2'++H2)).
  (* from arg *)
    right.
    replace ((vx2::H2') ++H2) with (vx2::H2'++H2) in H21.
    subst x0. destruct H21. rewrite indexr_head in H21. destruct H21.
    inversion H21. subst. auto. simpl. auto.  
  (* from func *)
    left. split.
    exists x0.  
    destruct H22. split. auto. eapply Q2 in H22. 3: eauto. 3: eauto.
    destruct H21 as [? [? ?]]. 
    unfold pdom in H22. replace ((vx2::H2') ++H2) with (vx2::H2'++H2) in H21.
    rewrite indexr_skip in H21; auto. unfold var_locs. exists x1; intuition. simpl. auto.
    intros ? ?. eapply H8 in H24. unfold pdom. rewrite app_length. simpl. lia.
    unfold subst_pl in H22. rewrite app_length in H23.
    unfoldq; intuition; simpl in *; lia.
    
    exists x0.     
    destruct H20. unfoldq; intuition. 
    eapply Q2 in H19. 3: eauto. 3: eauto. unfold pdom in H19.
    replace ((vx2::H2') ++H2) with (vx2::H2'++H2) in H21.
    rewrite indexr_skip in H21. intuition. lia. auto. 
    intros ? ?. unfold pdom. eapply P1 in H22. rewrite app_length in *. simpl in *. lia.
    eapply Q2 in H19. 3: eauto. 3: eauto. unfold pdom in H19.
    destruct H20; simpl in *; rewrite app_length in *; simpl in *; lia.
    intros ? ?. unfold pdom. eapply P1 in H22. rewrite app_length in *. simpl in *. lia.
    destruct H20; simpl in *; rewrite app_length in *; simpl in *; lia.
    
    eapply valq_abs.
    rewrite substq_empty_and.
    eapply valq_abs.

    auto. auto. auto. auto.
Unshelve. all: eauto.
Qed.


Lemma bi_qsub_subst: forall S1 S2 M H1 H1' v1 H2 H2' G' T0 G S1' S2' M' t t1 T p q1 q2 e1 e2  v1' v2' v2'0 
  (WFE: env_type_subst2 M (H1'++ v1::H1) (H2'++ H2) (G'++T0::G) p (length G) v2'0 qempty)
  (ST: store_type S1 S2 M)
  (IE: exp_type1 S1 S2 M (H1' ++ v1 :: H1) (H2' ++ H2) 
       t (subst_tm t (length H2) (splice_tm t1 (length H2) (length H2')) qempty) 
       S1' S2' M' v1' v2' 
       T  (subst_ty T (length H2) qempty)
       (plift p) (plift (subst_ql p (length H2) qempty))
       (plift q1) (plift (subst_ql q1 (length H2) qempty))
       (plift e1) (plift (subst_ql e1 (length H2) qempty))
  )
  (L1: length H1 = length G)
  (L2: length H2 = length G)
  (L3: length H1' = length G')
  (L4: length H2' = length G'),
  psub (plift q1) (plift q2) ->
  psub (plift q2) (pdom (G' ++ T0 :: G)) ->
  psub (plift e1) (plift e2) ->
  psub (plift e2) (pdom (G'++T0::G))  ->
  exists S1'' S2'' M'' v1' v2',
  exp_type1 S1 S2 M (H1'++v1::H1) (H2'++H2) 
  t (subst_tm t (length H2) (splice_tm t1 (length H2) (length H2')) qempty) 
  S1'' S2'' M'' v1' v2' 
  T (subst_ty T (length H2) qempty) 
  (plift p) (subst_pl (plift p) (length H2) pempty) 
  (plift q2) (subst_pl (plift q2) (length H2) pempty)
  (plift e2) (subst_pl (plift e2) (length H2) pempty).
Proof.    
  intros.  
  destruct IE as [IE1 [IE2 [IEFF1 [IEFF2 [ISTC [IST [IVAL [IQ1 IQ2]]]]]]]]. 
  exists S1', S2', M', v1', v2'.
  split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 8: split. 
  eauto. eauto.
  eapply se_sub; eauto. unfoldq; intuition. 
  eapply se_sub; eauto. rewrite plift_subst, plift_empty. intros ? ?. auto.
  auto. auto.
  auto. 
  
  unfold val_qual in IQ1; intuition.
  eapply valq_sub; eauto. unfoldq; intuition. rewrite app_length in *. simpl in *. eapply H0 in H5. lia. 
  unfold val_qual in IQ2; intuition.
  eapply substp_sub with (m := length H2) (q1 := qempty) in H. 
  eapply valq_sub; eauto. 
  repeat rewrite plift_subst, plift_empty in *. eauto. 
  repeat rewrite plift_subst in H. repeat rewrite plift_empty in H. eauto.

  eapply Q2; eauto. 
Qed.

Lemma bi_tseq_subst: forall S1 S2 M H1' v1 H11 H2' H12 t1 t2 t0 q1 S1' S2' M' v1' v2' S1'' S2'' M'' v3 v4 q2 e1 e2 p1 p2 p
  (ST: store_type S1 S2 M)
  (E1: exp_type1 S1 S2 M (H1' ++ v1 :: H11) (H2' ++ H12) 
          t1 (subst_tm t1 (length H12) (splice_tm t0 (length H12) (length H2')) qempty)
          S1' S2' M' v1' v2'
          TBool  (subst_ty  TBool (length H12) qempty)
          (plift p1) (plift (subst_ql p1 (length H12) qempty))
          (plift q1) (plift (subst_ql q1 (length H12) qempty))
          (plift e1) (plift (subst_ql e1 (length H12) qempty)))
  (E2: exp_type1 S1' S2' M' (H1' ++ v1 :: H11) (H2' ++ H12) 
          t2 (subst_tm t2 (length H12) (splice_tm t0 (length H12) (length H2')) qempty)
          S1'' S2'' M'' v3 v4 
          TBool (subst_ty TBool (length H12) qempty)
          (plift p2) (plift (subst_ql p2 (length H12) qempty))
          (plift q2) (plift (subst_ql q2 (length H12) qempty))
          (plift e2) (plift (subst_ql e2 (length H12) qempty)))
  (SUB1: psub (plift p1)(plift p))
  (SUB2: psub (plift p2)(plift p)), 
  exists (S1'0 S2'0 : stor) (M'0 : stty) (v1'0 v2'0 : vl),
    exp_type1 S1 S2 M (H1' ++ v1 :: H11) (H2' ++ H12)
      (tseq t1 t2) (subst_tm (tseq t1 t2) (length H12) (splice_tm t0 (length H12) (length H2')) qempty) 
      S1'0 S2'0 M'0 v1'0 v2'0 
      TBool (subst_ty TBool (length H12) qempty)
      (plift p) (plift (subst_ql p (length H12) qempty))
      (plift qempty) (plift (subst_ql qempty (length H12) qempty))
      (plift (qor e1 (qor e2 q1))) (plift (subst_ql (qor e1 (qor e2 q1)) (length H12) qempty)). 
Proof. 
  intros. 
  destruct E1 as [IE1 [IE2 [EFF1 [EFF2 [STC1 [ST1 [HV [HQ1 HQ2]]]]]]]].
  destruct v1'; destruct v2'; try solve [inversion HV]. simpl in HV.
  subst b0.
  remember ST1 as ST1'. clear HeqST1'.
  destruct ST1 as [STL1 [STL2 [SP1 [SP2 SP3]]]].

  destruct E2 as [IE3 [IE4 [EFF3 [EFF4 [STC2 [ST2 [HV1 [HQ3 HQ4]]]]]]]].
  destruct v3; destruct v4; try solve [inversion HV1]. simpl in HV1.
  subst b0.
  remember ST2 as ST2'. clear HeqST2'.
  destruct ST2 as [STL3 [STL4 [SP4 [SP5 SP6]]]].

  exists S1'', S2''.
  exists M''.
  exists (vbool (b && b1)), (vbool (b && b1)).

  split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 8: split.
  (* first one *)
  destruct IE1 as [n1 IE1].
  destruct IE3 as [n3 IE3].
  exists (S(n1 + n3)). intros. destruct n. intuition.
  simpl. rewrite IE1. rewrite IE3.
  auto. lia. lia.
  
  destruct IE2 as [n2 IE2].
  destruct IE4 as [n4 IE4].
  exists (S(n2 + n4)). intros. destruct n. intuition.
  simpl. rewrite IE2. rewrite IE4. 
  auto. lia. lia.

  (* effects  *)
    
  eapply se_trans; eapply se_sub; eauto; eapply vl_mono; eauto.
  eapply dsubst_sub with (p1 := qempty)(q1 := qempty)(m := length H12) in SUB2, SUB1.
  rewrite plift_empty in SUB1, SUB2.
  eapply se_trans; eapply se_sub; eauto; eapply vl_mono; eauto.
  1,2: repeat rewrite plift_subst, plift_empty; eauto. auto. auto. 
  
  eapply st_trans; eauto.

  auto.
  
  
  (* valt *)
  constructor.

  (* valq *)
  eapply valq_bool. eapply valq_bool.

Qed.

Lemma st_subst: forall G0 t2 T2 p2 q2 e2 
  (W: has_type G0 t2 T2 p2 q2 e2), (* p2 is p and qf + one*) 
  forall G' G, G0 = G'++TBool::G ->
    closed_ty (length G' +  S (length G)) T2 ->
    closed_ql (length G' + S (length G)) p2 ->
    closed_ql (length G' + S (length G)) q2 ->
    closed_ql (length G' + S (length G)) e2 ->
  forall t1 p1 q1,
  closed_ql (length G) q1 ->
  closed_ql (length G) p1 -> 
  q1 = qempty  -> (*****)
  p1 = qempty -> 
  psub (pand (pand (pdom (G'++G)) (plift p2))(plift q1)) pempty -> (* separation *)
  (* psub (pand (plift p2) (pdom G)) (plift p1) -> (* not sure about this one ... *)  *)
 (* psub (pone (length (G'++G)))(plift p2) -> *)
  has_type G t1 TBool p1 q1 qempty  -> 
  forall M H1 H1' H2 H2' v1 v2'0,
    val_type M H1 H2 v1 v2'0 TBool TBool -> 
    env_type_subst2 M (H1'++v1::H1) (H2'++H2) G0 p2 (length G) v2'0 q1   ->
    forall S1 S2 (* S1' *),
    length H1 = length G ->
    length H2 = length G ->
    length H1' = length G' ->
    length H2' = length G' ->
    store_type S1 S2 M ->
    (forall H2'' S2',
     length S2 <= length S2' ->   
     exists v2 M'' S2'', 
     tevaln S2' (H2''++H2) (splice_tm t1 (length H2) (length H2'')) S2'' v2 /\
     store_effect S2' S2'' pempty /\
     length S2' <= length S2'' /\  
     val_type M'' H1 (H2''++H2) v1 v2 TBool TBool /\
     val_qual (length S1) H1 v1 pempty pempty /\
     val_qual (length S2) (H2''++H2) v2  pempty pempty 
     )  -> (* via st_weaken + store_invariance *)
    exists  S1'' S2'' M'' v1'' v2'',
      exp_type1 S1 S2 M (H1'++v1::H1) (H2'++H2) 
        t2 (subst_tm t2 (length H2) (splice_tm t1 (length H2) (length H2')) q1)
        S1'' S2'' M'' v1'' v2''
        T2  (subst_ty T2 (length H2) q1)
        (plift p2) (plift (subst_ql p2 (length H2) q1))
        (plift q2) (plift (subst_ql q2 (length H2) q1))
        (plift e2) (plift (subst_ql e2 (length H2) q1)).
Proof.
  intros ? ? ? ? ? ?  W.
  induction W; intros.
  - (* ttrue *)
    simpl. repeat rewrite substq_empty. 
    rewrite plift_empty.
    exists S1, S2, M, (vbool true), (vbool true).
    eapply bi_vtrue3; auto. 
  - simpl. repeat rewrite substq_empty.  repeat rewrite spliceq_empty.
    rewrite plift_empty.
    exists S1, S2, M, (vbool false), (vbool false).
    eapply bi_vfalse3; auto. 
  
  - (* tvar *)
    subst env.
    destruct (H21 H2' S2) as [v2' [M'' [S2'' [IE2 [EFF2 [LS2 [IVAT [IVAQ1 IVAQ2]]]]]]]]; auto. 
    repeat rewrite substq_empty.
    rewrite plift_one.  rewrite plift_empty.
    eapply bi_var_subst2; eauto.
    
  - (* tref *)
    subst env.
    assert (closed_ty (length G'+ S(length G)) TBool).
    constructor.

    specialize (IHW G' G). intuition. 
    rename H20 into IHW.
    specialize (IHW t1 p1 q1). intuition.
    rename H21 into IHW.
    destruct (IHW M H10 H1' H11 H2' v1 v2'0 H12 H13 S1 S2) as [S1'' [S2'' [M'' [v1'' [v2'' ?]]]]]; intuition.
    eapply bi_tref_subst; eauto.

  - (* tget *)
    subst env.
    eapply has_type_closed_subst in W; eauto.
    rewrite app_length in *.  simpl in W. 
    
    specialize (IHW G' G); intuition.
    rename H22 into IHW.
    specialize (IHW t1 p1 q1); intuition.
    rename H24 into IHW.
    destruct (IHW M H10 H1' H11 H2' v1 v2'0 H12 H13 S1 S2) as [S1'' [S2'' [M'' [v1'' [v2'' ?]]]]]; auto.

    eapply bi_tget_subst; eauto.

  - (* tput *) 
    subst env.
    (* 1st IH *)
    eapply has_type_closed_subst in W1; eauto. rewrite app_length in W1. simpl in W1.
    eapply has_type_closed_subst in W2; eauto. rewrite app_length in W2. simpl in W2.

    
    specialize(IHW1 G' G); intuition.
    rename H25 into IHW1.
    specialize(IHW1 t0 p1 q0); intuition. 
    rename H28 into IHW1.
    destruct (IHW1 M H10 H1' H11 H2' v1 v2'0  H12 H13 S1 S2) as [S1'' [S2'' [M'' [v1'' [v2'' IE1]]]]]; eauto.

    (* 2nd IH*)
    assert (env_type_subst2 M'' (H1'++v1::H10) (H2'++H11) (G'++TBool::G) p (length G) v2'0  q0)  as WFE1.
    eapply envt_subst_store_extend; eauto. apply IE1.
    assert (store_type S1'' S2'' M'' ) as ST'.
    apply IE1.
    
    specialize(IHW2 G' G); intuition.
    rename H25 into IHW2.
  
   assert (st_chain M M'') as SC0. apply IE1.

    assert (val_type M'' H10 H11 v1 v2'0 TBool TBool) as VT.
    eapply valt_store_extend; eauto.  eapply st_mono2 in SC0. auto.


    specialize(IHW2 t0 p1 q0); intuition. 
    rename H28 into IHW2.
    destruct (IHW2 M''  H10 H1' H11 H2' v1 v2'0  VT WFE1 S1'' S2'') as [S1'''' [S2'''' [M'''' [v3 [v4 IE2]]]]]; auto.

    
    intros. 
    assert (length S2 <= length S2''). {
      eapply st_mono2 in SC0.
      destruct H18; destruct ST'; intuition.
    }
  
    destruct (H19 H2'' S2') as [v2' [MX [S2''' [? [? [? [? [? ?]]]]]]]].
    lia.
    exists v2', MX, S2'''; intuition.
    destruct v1; destruct v2'; try inversion H32.
    unfoldq; intuition.
    destruct v1; destruct v2'; try inversion H32.
    unfoldq; intuition. 
    
    
    eapply bi_tput_subst; eauto.

  - (* tapp *)
    subst env.

    (* 1st IH *)
    eapply has_type_closed_subst in W1; eauto. rewrite app_length in W1. simpl in W1.
    eapply has_type_closed_subst in W2; eauto. rewrite app_length in W2. simpl in W2.

    specialize (IHW1 G' G); intuition.
    rename H28 into IHW1.
    specialize (IHW1 t1 p1 q0); intuition.
    rename H31 into IHW1.
    specialize (IHW1 M H13 H1' H14 H2' v1 v2'0 H15 H16 S1 S2) as [S1' [S2' [M' [vf1 [vf2 IEF]]]]]; auto.

    (* 2nd IH *)
    specialize (IHW2 G' G); intuition.
    rename H28 into IHW2.
    specialize (IHW2 t1 p1 q0); intuition.
    rename H31 into IHW2.

    assert (env_type_subst2 M' (H1'++ v1::H13) (H2'++ H14) (G'++TBool::G) p (length G) v2'0 q0) as WFE1.
    eapply envt_subst_store_extend; eauto. eapply IEF.
    assert (store_type S1' S2'  M' ) as ST'.
    eapply IEF.

    assert (st_chain M M') as SC0. apply IEF.

    assert (val_type M' H13 H14 v1 v2'0 TBool TBool) as VT.
    eapply valt_store_extend; eauto. eapply st_mono2 in SC0. auto.

    destruct (IHW2 M' H13 H1' H14 H2' v1 v2'0 VT WFE1 S1' S2') as [S1'' [S2'' [M'' [vx1 [vx2 IEX]]]]]; auto.

    intros ? ? ?.
    assert (length S2 <= length S2'0). {
      eapply st_mono2 in SC0.
      destruct H21; destruct ST'; intuition.
    }
    destruct (H22 H2'' S2'0) as [v2' [MX [S2'' [? [? [? [? [? ?]]]]]]]].
    lia.
    exists v2', MX, S2''; intuition.
    1,2: destruct v1; destruct v2'; try inversion H35;
    unfoldq; intuition.

    eapply bi_tapp_subst; eauto.

  - (* tabs *)  
    subst env.
    assert (closed_ty (length (T1::G') + S(length G)) (TFun T1 T2 q2 e2)).
    eapply closedty_extend; eauto. simpl. lia.
    inversion H4. subst m T0 T3 q0 e0.
    simpl in H4, H30, H31, H32, H33.


    assert (closed_ql (length (T1::G') + S(length G)) (qor (qand p qf)(qone (length (G'++TBool :: G))))).
    rewrite closedq_or; intuition. eapply closedq_and. left. simpl. eapply closedq_extend; eauto.
    unfold closed_ql. intros ? ?. unfold qone in H25. bdestruct (x =? length (G'++TBool::G)); intuition. rewrite app_length in H26. simpl in *. lia.

    assert (closed_ql (length (T1::G') + S(length G)) (qor q2 (qone (length (G'++TBool :: G))))).
    rewrite closedq_or; intuition. 
    unfold closed_ql. intros ? ?. unfold qone in H26. bdestruct (x =? length (G'++TBool::G)); intuition. rewrite app_length in H27. simpl in *. lia.

    assert (closed_ql (length (T1::G') + S(length G)) (qor e2 (qone (length (G'++TBool :: G))))).
    rewrite closedq_or; intuition. 
    unfold closed_ql. intros ? ?. unfold qone in H27. bdestruct (x =? length (G'++TBool::G)); intuition. rewrite app_length in H28. simpl in *. lia.



    (* separation *)
    assert (psub (pand (pand (pdom ((T1::G')++G)) (plift (qor (qand p qf) (qone (length (G' ++ TBool :: G)))))) (plift q1)) pempty).
    rewrite plift_or, plift_one.
    unfoldq; intuition. subst q1. unfoldq; intuition.
    subst q1. unfoldq; intuition.

    specialize (IHW (T1::G') G). intuition.      
    specialize (H29 t1 p1 q1); intuition.
    rename H29 into IHW.

    eapply bi_tabs_subst; eauto. 
  
  - (* tseq *)
    subst env. subst q0 p0.
    eapply has_type_closed_subst in W1. 2: { eapply envt_subst_tighten; eauto. }
    eapply has_type_closed_subst in W2. 2: { eapply envt_subst_tighten. eapply H16. eauto. }
    rewrite app_length in W1, W2. simpl in W1, W2.
    intuition.
    (* 1st IH *)
    assert (closed_ql (length G) qempty). unfold closed_ql. unfoldq; intuition.

    assert (psub (pand (pand (pdom (G'++G))(plift p1))(plift qempty)) pempty).
    rewrite plift_empty. intros ? ?. unfoldq; intuition. 

    assert (psub (pand (pand (pdom (G'++G))(plift p2))(plift qempty)) pempty).
    rewrite plift_empty. intros ? ?. unfoldq; intuition. 

    specialize(IHW1 G' G); intuition.
    rename H31 into IHW1.
    specialize(IHW1 t0 qempty qempty); intuition. 
    rename H32 into IHW1.

    assert(env_type_subst2 M (H1' ++ v1 :: H13) (H2' ++ H14) (G' ++ TBool :: G) p1 (length G) v2'0 qempty) as WFE1.
    eapply envt_subst_tighten; eauto. 

    destruct (IHW1 M H13 H1' H14 H2' v1 v2'0  H15 WFE1 S1 S2) as [S1'' [S2'' [M'' [v1'' [v2'' IE1]]]]]; eauto.

    
    (* 2nd IH*)
    specialize(IHW2 G' G); intuition.
    rename H31 into IHW2.

    assert (env_type_subst2 M'' (H1'++v1::H13) (H2'++H14) (G'++TBool::G) p2 (length G) v2'0  qempty)  as WFE2.
    eapply envt_subst_tighten. eapply envt_subst_store_extend. eapply H16. eapply IE1. auto. 

    assert (st_chain M M'') as SC'. apply IE1.

    assert (store_type S1'' S2'' M'') as ST'. eapply IE1.
    
    assert (val_type M'' H13 H14 v1 v2'0 TBool TBool) as VT.
    eapply valt_store_extend; eauto. eapply st_mono2 in SC'. auto.


    specialize(IHW2 t0 qempty qempty); intuition. 
    rename H32 into IHW2.
    destruct (IHW2 M''  H13 H1' H14 H2' v1 v2'0  VT WFE2 S1'' S2'') as [S1'''' [S2'''' [M'''' [v3 [v4 IE2]]]]]; auto.
    
    intros. 
    assert (length S2 <= length S2''). {
      eapply st_mono2 in SC'.
      destruct H21; destruct ST'; intuition.
    }
  
    destruct (H22 H2'' S2') as [v2' [MX [S2''' [? [? [? [? [? ?]]]]]]]].
    lia.
    exists v2', MX, S2'''; intuition.
    destruct v1; destruct v2'; try inversion H36.
    unfoldq; intuition.
    destruct v1; destruct v2'; try inversion H36.
    unfoldq; intuition. 
    
    eapply bi_tseq_subst; eauto.
  
  - (* qsub *)

    subst; intuition.
    eapply has_type_closed_subst in W; eauto.
    rewrite app_length in W. simpl in W.
    specialize (IHW G' G); intuition.
    rename H24 into IHW.
    specialize (IHW t1 qempty qempty); intuition.
    rename H26 into IHW.
    specialize (IHW M H14 H1' H15 H2' v1 v2'0); intuition.
    rename H26 into IHW.
    specialize (IHW S1 S2); intuition.
    destruct H26 as (S1' & S2' & M' & v1' & v2' & ?).
    repeat rewrite plift_subst, plift_empty.
    eapply bi_qsub_subst; eauto. 
Qed.

Lemma vars_locs_bool_head: forall b H p,
  vars_locs ((vbool b) :: H) p = vars_locs ((vbool b) :: H) (por p (pone (length H))). 
Proof.
  intros. eapply functional_extensionality.
  intros. eapply propositional_extensionality.
  unfoldq; intuition. destruct H0 as [? [? ?]].
  exists x0; intuition.
  destruct H0. destruct H0. destruct H0.
  exists x0; intuition. subst x0. 
  unfoldq; intuition. destruct H1 as [? [? ?]]. rewrite indexr_head in H0.
  inversion H0. subst x0. rewrite val_locs_bool in H1. unfoldq; intuition.
Qed.  

Lemma st_subst1 : forall t1 t2 G M T2 p qf q2 e2 H1 H2 v1 S1 S2 S1' S2' v2
    (W: has_type (TBool::G) t2 T2 (qor  (qand p qf) (qone (length G))) (qor q2 (qone (length G))) (qor e2 (qone (length G)))) 
    (X: has_type G t1 TBool qempty qempty qempty)
    (WFE: env_type (length S1', length S2, strel M) H1 H2 G (plift p))
    (SUB: psub (plift q2) (plift p)),
    length H1 = length G ->
    length H2 = length G ->
    closed_ty (length G) T2 ->
    closed_ql (length G) q2 ->
    closed_ql (length G) e2 ->
    closed_ql (length G) qf -> 
    store_type S1 S2 M ->
    store_type S1' S2 (length S1', length S2, strel M) ->    
    tevaln S1 H1 t1 S1' v1 ->  (* S1 is SF *)
    tevaln S2 H2 t1 S2' v2 ->
    store_effect S1 S1' pempty ->
    store_effect S2 S2' pempty ->
    length S1 <= length S1' ->
    length S2 <= length S2' ->
    val_type (length S1', length S2, strel M) H1 H2 v1 v2 TBool TBool ->
    (forall H2'', 
     exists v2 M' S2'', 
     tevaln S2 (H2''++H2) (splice_tm t1 (length H2) (length H2'')) S2'' v2 /\ 
     store_effect S2 S2'' pempty /\
     length S2 <= length S2'' /\
     val_type M' H1 (H2''++H2) v1 v2 TBool TBool /\
     val_qual (length S1) H1 v1 pempty pempty /\
     val_qual (length S2) (H2''++H2) v2  pempty pempty 
     ) -> (* via st_weaken *)
    exists S1'' S2'' M'' v1'' v2'',
      exp_type S1' S2 M
        (v1::H1) H2
        t2 (subst_tm t2 (length H2) t1 qempty)
        S1'' S2'' M'' v1'' v2'' T2  
        (plift p)
        (plift q2)
        (plift e2).  
Proof.  
  intros. eapply filter_closed in WFE as CLP. 
  remember WFE as WFE'. clear HeqWFE'.
  destruct WFE as [L1 [L2 [? [? ?]]]].
  eapply st_subst with (G':=[]) (H1':=[]) (H2':=[])(H2 := H2)(H1 := H1) in W.
  12: eapply X. 18: eapply H8.
  2: { simpl. eauto. }
  2: { simpl. eapply closedty_extend; eauto. }
  2: { simpl. eapply closedq_or. split. eapply closedq_and. left. eapply closedq_extend; eauto. eapply closedq_one; eauto. }
  2: { simpl. eapply closedq_or. split. eapply closedq_extend; eauto.  eapply closedq_one; eauto. }
  2: { simpl. eapply closedq_or. split. eapply closedq_extend; eauto. eapply closedq_one; eauto. }
  2: { unfold closed_ql. intros. unfoldq; intuition.  }
  2: { unfold closed_ql. intros. unfoldq; intuition. }
  2: { eauto. } 
  2: { eauto. } 
  2: { rewrite plift_or, plift_one, plift_and, plift_empty. simpl. unfoldq. intuition. }
  2: { eauto. }
  2: { simpl.  eapply envt_to_envt_subst2; eauto.
       intros ? ?. rewrite plift_and in H20. unfoldq; intuition. eauto.
      eapply closedq_and. left. auto. 
      destruct v1; destruct v2; try inversion H15. intros. rewrite val_locs_bool in H21. unfoldq; intuition.
      destruct v1; destruct v2; try inversion H15. intros. rewrite val_locs_bool in H21. unfoldq; intuition. 
      }
  2: { eauto. }
  2: { eauto. }
  2: { eauto. }
  2: { eauto. }
  2: { intros. 
       remember (st_empty S1 S2'0) as ME.
       assert (store_type S1 S2'0 ME). subst ME. eapply storet_empty.
       assert (env_type ME H1 H2 G pempty). {
         eapply envt_store_change. eapply envt_tighten. eauto. intros ? ?. unfoldq; intuition.
         subst ME. repeat rewrite vars_locs_empty. unfold st_chain_partial. repeat split. 
         intros ? ?. unfoldq; intuition.
         intros ? ?. unfoldq; intuition.
         intros ? ?. unfoldq; intuition.
         intros ? ?. unfoldq; intuition.
         intros ? ? ? ?. unfoldq; intuition.

         subst ME. repeat rewrite vars_locs_empty. unfold st_chain_partial2. repeat split. 
         intros ? ?. unfoldq; intuition.
         intros ? ?. unfoldq; intuition.
         intros ? ?. unfoldq; intuition.
         intros ? ?. unfoldq; intuition.
         intros ? ? ? ?. unfoldq; intuition.
         subst ME. unfold length2. simpl. auto.
       }
       
       eapply st_weaken1 with (S1 := S1)(S2 := S2'0)(H1 := H1)(H2:= H2)(H2' := []) in X.
       2: { simpl. subst ME. auto. }
       destruct X as [v1' [S1'' [? ?]]].
       assert (v1' = v1 /\ S1'' = S1').
       eapply tevaln_unique; eauto.
       destruct H25. subst v1'. subst S1''.
       destruct (H24 H2'') as [v2X [MX [S2X [? [? [? [? [? ?]]]]]]]].
       exists v2X, MX, S2X; intuition.
       1,2: destruct v1; destruct v2X; try inversion H28; unfoldq; intuition.
  }

  destruct W as (S1'' & S2'' & M'' & v1'' & v2'' & ?).
  simpl in H20.
  destruct H20 as (TE1 & TE2 & SE1 & SE2 & STC' & ST' & VT & VQ1 & VQ2).

  exists S1'', S2'', M'', v1'', v2''.
  split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 8: split. 
  - eauto.
  - rewrite splice_zero in TE2. eauto.
  - eapply st_trans; eauto. eapply stc_X; eauto. intros ? ?. unfoldq; intuition.
  - auto.
  - rewrite plift_or, plift_one, plift_and in SE1.
    destruct v1; destruct v2; try inversion H15. subst b.
    rewrite vars_locs_bool_head. eapply se_sub; eauto.
    intros ? ?. rewrite <- L1 in H20. eapply vars_locs_sub; eauto. 
    intros ? ?. unfoldq; intuition.

  - rewrite plift_subst, plift_or, plift_one in SE2.
    rewrite substp_or in  SE2. rewrite L2 in SE2. rewrite substp_hit in  SE2.
    rewrite  substp_id in  SE2. eapply se_sub; eauto. 
    intros ? ?. unfold vars_locs in H20. unfold vars_locs. destruct H20 as [? [? ?]].
    exists x0; intuition. rewrite plift_and in H20. unfoldq; intuition.
    eapply closedq_and. left. auto.
  - rewrite substy_id in VT. auto. rewrite L2. auto.
  - unfold length1 in VQ1. simpl in VQ1. unfoldq; intuition. 
    destruct (VQ1 x). intuition. destruct H7; intuition. 
    rewrite plift_or, plift_and, plift_one in H21. 
    destruct H21. destruct H21. 
    rewrite plift_or, plift_one in H26. 
    destruct H21. destruct H21. destruct H26. 
    exists x0; intuition. unfold pone in H26. subst x0. eapply H6 in H27. lia.
    unfoldq; intuition. subst x0. eapply SUB in H27. eapply H17 in H27. lia.
    subst x0. destruct H25 as [? [? ?]]. rewrite <- L1 in H21. rewrite indexr_head in H21.
    inversion H21. subst x0. destruct v1; destruct v2; try inversion H15. rewrite val_locs_bool in H25. unfoldq; intuition.
  - repeat rewrite plift_subst, plift_or, substp_or, plift_empty, plift_one in VQ2.
    rewrite substp_id in VQ2. rewrite <- L2 in VQ2. 
    rewrite substp_hit in VQ2. rewrite substp_id in VQ2.
    repeat rewrite por_empty_r in VQ2. unfoldq; intuition.
    destruct (VQ2 x) as [? [? ?]]; intuition. 
    unfold length2. simpl. destruct H7; intuition. 
    exists x0; intuition.
    rewrite L2. auto. rewrite L2. eapply closedq_and. intuition.   
Qed.


(*---- beta rules ---------------*)

Lemma beta_equivalence: forall t1 t2 G T2 p qf q2 e2 
  (F: has_type (TBool::G) t2 T2 (qor (qand p qf) (qone (length G))) (qor q2 (qone (length G))) (qor e2 (qone (length G))))
  (X: has_type G t1 TBool qempty qempty qempty)
  (QSUB: psub (plift q2) (plift p))
  (ESUB: psub (plift e2) (plift p))
  (CLT2: closed_ty (length G) T2)
  (CLQ2: closed_ql (length G) q2) 
  (CLE2: closed_ql (length G) e2)
  (CLQF: closed_ql (length G) qf)
  (P: p = qempty),
  sem_type G (tapp (tabs (qand p qf) t2) t1) (subst_tm t2 (length G) t1 qempty) 
    T2 (plift p) (plift q2) (plift e2).
Proof.
  intros. 
  intros M H1 H2 WFE. intros S1 S2 ST.
  apply wf_env_type in WFE as WFE'.
  destruct WFE' as [L1 [L2 [PD1 [PD2 [PD3 PD4]]]]].

  assert (has_type G (tabs (qand p qf) t2) (TFun TBool T2 q2 e2) p qf qempty) as TFun.
  econstructor; eauto. 

  eapply fundamental_property in TFun; eauto. 
  destruct TFun as [FS1 [FS2 [MF [vf [vf' [IEF1 [IEF2 [SCF [STF [FEFF1 [FEFF2 [VTF [VQF1 VQF2]]]]]]]]]]]]]. 

   
  eapply st_weaken1 with (H2':=[])(S1 := FS1)(H1 := H1)(H2 := H2)(S2 := S2) in X as A; eauto.
  destruct A as [v1 [S1' [IE1 A]]].  
  2: { simpl in *. eapply envt_store_change. eapply envt_tighten. eauto.  intros ? ?. unfoldq; intuition. 
       1,2: repeat rewrite vars_locs_empty. 
       assert (st_chain_partial M (st_empty FS1 S2) pempty pempty). {
        unfold st_chain_partial; intuition.
        intros ? ?. unfoldq; intuition. 
        intros ? ?. unfoldq; intuition.
        intros ? ?. unfoldq; intuition.
        intros ? ?. unfoldq; intuition.
      }
      auto.
      assert (st_chain_partial2 (st_empty FS1 S2) M pempty pempty). {
        unfold st_chain_partial2. intuition.
        intros ? ?. unfoldq; intuition. 
        intros ? ?. unfoldq; intuition.
        intros ? ?. unfoldq; intuition.
        intros ? ?. unfoldq; intuition.
      }
      auto.
      assert (length2 M = length S2). destruct ST; intuition.
      rewrite H.  unfold st_empty, length2. simpl. lia.
    }

  assert (env_type MF H1 H2 G (plift qempty)) as WFE1.
  eapply envt_store_extend. eapply envt_tighten; eauto. intros ? ?. rewrite plift_empty in H. unfoldq; intuition. auto.

  destruct (fundamental_property _ _ _ _ _ _ X MF H1 H2 WFE1 FS1 FS2 STF) as [S1'0 [S2'0 [M'0 [v1'0 [v2'0 ?]]]]].
  destruct H as [IEF1' [IEF2' [STCMF [STMF [SEFFM1 [SEFFM2 [VTM [VQM1 VQM2]]]]]]]].
  assert (v1'0 = v1 /\ S1'0 = S1').
  eapply tevaln_unique; eauto.
  destruct H. subst v1'0. subst S1'0.


  (* store_typing *)
  assert (length S1 = length1 M) as LS1. destruct ST; intuition.
  assert (length S2 = length2 M) as LS2. destruct ST; intuition.
  assert (length1 M <= length1 MF) as LM1. eapply st_mono1 in SCF; auto.
  assert (length2 M <= length2 MF) as LM2. eapply st_mono2 in SCF; auto.
  assert (length FS1 = length1 MF) as LS3. destruct STF; intuition.
  assert (length FS2 = length2 MF) as LS4. destruct STF; intuition.
  
  assert (length1 MF <= length1 M'0) as LM3. eapply st_mono1 in STCMF; auto.
  assert (length2 MF <= length2 M'0) as LM4. eapply st_mono2 in STCMF; auto.
  assert (length S1' = length1 M'0) as LS5. destruct STMF; auto.
  assert (length S2'0 = length2 M'0) as LS6. destruct STMF; intuition.
  
  remember (length FS1, length S2, strel M) as M1.
  assert (st_chain M M1) as STM1. {
    subst p. rewrite plift_empty in *. rewrite vars_locs_empty in *.
    subst M1. eapply stc_X; eauto.
    intros ? ?. unfoldq; intuition. lia.
  }

  assert (store_type FS1 S2 M1) as STF1. {
    eapply store_invariance2 in X; eauto.
    2: { intros. unfoldq; intuition. destruct H0; intuition. }
    2: { lia.  }
    subst M1. subst p.
    unfold store_type. destruct ST as [? [? [? [? ?]]]].
    destruct X as [SY1 [SY2 [MY [vy1 [vy2 [? [? [? [? ?]]]]]]]]].
    unfold store_type; intuition.
    rewrite plift_empty in *. rewrite vars_locs_empty in *.
    
    destruct (H3 l1 l2) as [? [? [? ?]]]; auto.
    specialize (FEFF1 l1 (vbool x)). intuition.
    exists x, x0; intuition. 
  }
  
  
  eapply store_invariance with (S1 := FS1)(S2 := S2)(P := (strel M)) in X as XX.
  2: { eapply envt_tighten. eapply envt_store_extend. eapply WFE. rewrite <- HeqM1. auto.  intros ? ?.  unfoldq; intuition. }
  destruct XX as [SX1 [SX2 [MX [vx1 [vx2 [IEX1 [IEX2 [SCX [STX [SEFX1 [SEFX2 [VTX [VQX1 VQX2]]]]]]]]]]]]].
  assert (vx1 = v1 /\ SX1 = S1'). eapply tevaln_unique; eauto.
  destruct H as [? ?]. subst vx1. subst SX1.
  
  assert (length S2 <= length2 MX) as LM5. eapply st_mono2 in SCX. unfold length2 in SCX. simpl in SCX. unfold length2. auto.
  assert (length SX2 = length2 MX) as LS7. destruct STX; intuition.
  
  
  remember (length S1', length S2, strel M) as M2.
  assert (st_chain M M2) as STM2. {
    subst p. rewrite plift_empty in *. rewrite vars_locs_empty in *.
    subst M2. eapply stc_X; eauto.
    intros ? ?. unfoldq; intuition. intros ? ?. unfoldq; intuition.
    lia.
  }
  
  assert (store_type S1' S2 M2). {
    eapply store_invariance2 in X; eauto.
    2: { intros. rewrite plift_empty. unfoldq; intuition. destruct H0; intuition. }
    2: { lia. }
    subst M2. subst p.
    unfold store_type. destruct ST as [? [? [? [? ?]]]].
    destruct X as [SY1 [SY2 [MY [vy1 [vy2 [? [? [? [? ?]]]]]]]]].
    unfold store_type; intuition.
    rewrite plift_empty in *. rewrite vars_locs_empty in *.
    assert (store_effect S1 S1' pempty). eapply se_trans; eauto.
    
    destruct (H3 l1 l2) as [? [? [? ?]]]; auto.
    specialize (H16 l1 (vbool x)). intuition.
    exists x, x0; intuition. 
  }

  assert (strel M = strel M1) as STREL0. {
    subst M1. simpl. auto.
  }

  assert (strel M1 = strel M2) as STREL. {
    subst M1. subst M2. simpl. auto.
  }

  (*---------------- substitution --------------*)
  rewrite plift_empty in *.  repeat rewrite vars_locs_empty in *.
  assert (env_type M1 H1 H2 G (plift p)).
  eapply envt_store_extend; eauto. 
  specialize (st_subst1 t1 t2 G M1 T2 p qf q2 e2 H1 H2 v1); intuition.
  rename H3 into SUBST.
  destruct (SUBST FS1 S2 S1' SX2 vx2) as [S1'' [S2'' [M'' [v1'' [v2'' [IE1' [IE2 [STC' [ST' [EFF1 [EFF2  [VT [VQ1 VQ2]]]]]]]]]]]]]; eauto. 
  eapply envt_store_extend. eapply WFE. rewrite <- STREL0. eapply stc_X; eauto. eapply se_trans; eauto. subst p. rewrite plift_empty in FEFF1. rewrite vars_locs_empty in *. auto.
  intros ? ?. unfoldq; intuition. lia.
  rewrite STREL. subst M2. auto.
  lia. lia. 

        
  exists S1'', S2'', M'', v1'', v2''. split.

  (* first term *)
  destruct IE1 as [n1 IE1].
  destruct IEF1 as [n2 IEF1].  (* from subst *)
  destruct IE1' as [n3 IE1'].  (* from subst *)
  exists ((S (n1+n2+n3))). intros.
  destruct n. lia. simpl. 
  rewrite IEF1; try lia.
  destruct vf; destruct vf'; try solve [inversion VTF]; simpl in VTF; intuition.
  rewrite IE1; try lia.
  assert  (l = H1 /\ t = t2). assert (S n2 > n2) as N1. lia.
  specialize (IEF1 (S n2) N1). simpl in IEF1. inversion IEF1.
  intuition. destruct H15. subst l. subst t.
  rewrite IE1'. auto. lia. 
  
  (* second term *) 
  split.
  
  rewrite <- L2. auto.

  split.
  eapply st_trans. eapply STM1. eauto. 
  split.
  auto.
  split.
  replace (v1 :: H1) with ([v1]++H1) in EFF1. (* from subst *)
  eapply se_trans. eauto.
  erewrite <- vars_locs_extend with (H' := [v1]). eapply se_trans. 2: eapply EFF1. 
  eapply se_sub; eauto. intros ? ?. unfoldq; intuition. auto. auto.
  split. auto.
  
  (*  valt *)
  split. eapply valt_extend with(H1' := [v1]) (H2' := []); eauto.
  rewrite L1. auto. rewrite L2. auto.
  
  (* valq 1*)
  split. 
  unfoldq. intros. destruct H3 as [C D].
  destruct (VQ1 x) as [x0 [? [? ?]]]. intuition.
  eapply st_mono1 in STM1. lia.
  exists x0; intuition. 
  unfoldq. bdestruct (x0 <? length H1); intuition.
  rewrite indexr_skip in H3. exists x1; intuition. lia.
  eapply CLQ2 in H6. rewrite <- L1 in H6. lia.
  
  (* valq 2*)
   unfoldq. intros. destruct H3 as [C D].
  destruct (VQ2 x) as [x0 [? [? ?]]]. intuition.
  eapply st_mono2 in STM1. lia.
  exists x0; intuition. 
  unfoldq. bdestruct (x0 <? length H2); intuition.
  exists x1; intuition. 
  eapply CLQ2 in H6. rewrite <- L2 in H6. lia.
Qed.
