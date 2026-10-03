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

(* ---------- aux definitions and lemmas ---------- *)

Definition splice_ql (p: ql) (i: nat) (n: nat): ql :=
  fun x => (if x <? i then p x else if x <? i + n then false else p (x - n)). 

Lemma splice_empty: forall i n,
    splice_ql qempty i n = qempty.
Proof.
  intros. unfold splice_ql, qempty.
  eapply functional_extensionality. intros.
  bdestruct (x <? i); eauto.
  bdestruct (x <? i+n); eauto. 
Qed.


Lemma splice_one: forall x i n,
    splice_ql (qone x) i n = qone (if x <? i then x else x + n).
Proof.
  intros. unfold splice_ql, qone.
  bdestruct (x <? i). 
  eapply functional_extensionality. intros.
  bdestruct (x0 <? i). eauto.
  bdestruct (x0 <? i+n).
  bdestruct (x0 =? x). lia. eauto. 
  bdestruct (x0 =? x). lia. 
  bdestruct (x0 - n =? x). lia. eauto. 
  eapply functional_extensionality. intros.
  bdestruct (x0 <? i). 
  bdestruct (x0 =? x). lia. 
  bdestruct (x0 =? x+n). lia. eauto.
  bdestruct (x0 <? i+n). 
  bdestruct (x0 =? x+n). lia. eauto.
  bdestruct (x0 -n =? x). 
  bdestruct (x0 =? x+n). eauto. lia.
  bdestruct (x0 =? x+n). lia. eauto.
Qed.

Lemma splice_or: forall q1 q2 i n,
    splice_ql (qor q1 q2) i n = qor (splice_ql q1 i n) (splice_ql q2 i n).
Proof.
  intros. unfold splice_ql, qor.
  eapply functional_extensionality. intros.
  bdestruct (x <? i). eauto. 
  bdestruct (x <? i+n); eauto. 
Qed.

Lemma splice_diff: forall q1 q2 i n,
    splice_ql (qdiff q1 q2) i n = qdiff (splice_ql q1 i n) (splice_ql q2 i n).
Proof.
  intros. unfold splice_ql, qdiff.
  eapply functional_extensionality. intros.
  bdestruct (x <? i). eauto. 
  bdestruct (x <? i+n); eauto. 
Qed.

Lemma splice_miss: forall q1 (G:tenv) n,
    psub (plift q1) (pdom G) ->
    splice_ql q1 (length G) n = q1.
Proof.
  intros. unfold splice_ql. 
  eapply functional_extensionality. intros.
  bdestruct (x <? length G). eauto. 
  bdestruct (x <? length G + n). eauto. 
  remember (q1 x). destruct b. symmetry in Heqb. eapply H in Heqb. unfoldq. lia. eauto.
  remember (q1 x). destruct b. symmetry in Heqb. eapply H in Heqb. unfoldq. lia. eauto.
  remember (q1 (x-n)). destruct b. symmetry in Heqb0. eapply H in Heqb0. unfoldq. lia. eauto.  
Qed.



(* ---------- syntactic notion of context ---------- *)

(* definition of single-hole term contexts *)
Inductive ctx : Type :=
  | chole  : ctx
  | cref   : ctx -> ctx
  | cget   : ctx -> ctx
  | cput1  : ctx -> tm -> ctx
  | cput2  : tm -> ctx -> ctx
  | capp1  : ctx -> tm -> ctx
  | capp2  : tm -> ctx -> ctx
  | cabs   : ctx -> ctx
  | cnot   : ctx -> ctx
  | cbin1  : ctx -> tm -> ctx
  | cbin2  : tm -> ctx -> ctx
.

(* free variables of a context *)
Fixpoint cfv n t: ql :=
  match t with
  | chole => qempty
  | cref t => cfv n t
  | cget t => cfv n t
  | cput1 t1 t2 => qor (cfv n t1) (fv n t2)
  | cput2 t1 t2 => qor (fv n t1) (cfv n t2)
  | capp1 t1 t2 => qor (cfv n t1) (fv n t2)
  | capp2 t1 t2 => qor (fv n t1) (cfv n t2)
  | cabs t => qdiff (cfv (S n) t) (qone n)
  | cnot t => cfv n t
  | cbin1 t1 t2 => qor (cfv n t1) (fv n t2)
  | cbin2 t1 t2 => qor (fv n t1) (cfv n t2)
end.

(* splicing of a context's variable indexes *)
Fixpoint splice_ctx (t: ctx) (i: nat) (n:nat) : ctx := 
  match t with 
  | chole         => chole
  | cref t        => cref (splice_ctx t i n)
  | cget t        => cget (splice_ctx t i n)
  | cput1 t1 t2   => cput1 (splice_ctx t1 i n) (splice_tm t2 i n)
  | cput2 t1 t2   => cput2 (splice_tm t1 i n) (splice_ctx t2 i n)
  | capp1 t1 t2   => capp1 (splice_ctx t1 i n) (splice_tm t2 i n)
  | capp2 t1 t2   => capp2 (splice_tm t1 i n) (splice_ctx t2 i n)
  | cabs t        => cabs (splice_ctx t i n)
  | cnot t        => cnot (splice_ctx t i n)
  | cbin1 t1 t2   => cbin1 (splice_ctx t1 i n) (splice_tm t2 i n)
  | cbin2 t1 t2   => cbin2 (splice_tm t1 i n) (splice_ctx t2 i n)
end.

(* plugging a context with a term *)
Fixpoint plug (t1: ctx) (t2: tm): tm :=
  match t1 with
  | chole        => t2
  | cref t1      => tref (plug t1 t2)
  | cget t1      => tget (plug t1 t2)
  | cput1 t1 t1' => tput (plug t1 t2) t1'
  | cput2 t1 t1' => tput t1 (plug t1' t2)
  | capp1 t1 t1' => tapp (plug t1 t2) t1'
  | capp2 t1 t1' => tapp t1 (plug t1' t2)
  | cabs t1      => tabs (plug t1 t2)
  | cnot t1      => tnot (plug t1 t2)
  | cbin1 t1 t1' => tbin (plug t1 t2) t1'
  | cbin2 t1 t1' => tbin t1 (plug t1' t2)
  end.

(* syntactic typing of contexts *)
Inductive ctx_type : ctx -> tenv -> ty -> bool -> bool -> bool -> bool -> tenv -> ty -> ql -> bool -> bool -> bool -> Prop :=
| c_hole: forall G T af fr a e,
    ctx_type chole G T af fr a e G T qempty fr a e
| c_ref: forall Gh Th afh frh ah eh G t p fr a e,
    ctx_type t Gh Th afh frh ah eh G TBool p fr a e ->
    ctx_type (cref t) Gh Th afh frh ah eh G TRef p true false e 
| c_get: forall Gh Th afh frh ah eh G t p fr a e,
    ctx_type t Gh Th afh frh ah eh G TRef p fr a e ->
    ctx_type (cget t) Gh Th afh frh ah eh G TBool p false false (e||a)
| c_put1: forall Gh Th afh frh ah eh G t1 p1 fr1 a1 e1 t2 p2 fr2 a2 e2,
    ctx_type t1 Gh Th afh frh ah eh G TRef p1 fr1 a1 e1 ->
    has_type G t2 TBool p2 fr2 a2 e2 ->
    ctx_type (cput1 t1 t2) Gh Th afh frh ah eh G TBool (qor p1 p2) false false (e1||e2||a1)
| c_put2: forall Gh Th afh frh ah eh G t1 p1 fr1 a1 e1 t2 p2 fr2 a2 e2,
    has_type G t1 TRef p1 fr1 a1 e1 ->
    ctx_type t2 Gh Th afh frh ah eh G TBool p2 fr2 a2 e2 ->
    ctx_type (cput2 t1 t2) Gh Th afh frh ah eh G TBool (qor p1 p2) false false (e1||e2||a1)
| c_app1: forall Gh Th afh frh ah eh G f t T1 T2 p1 p2 fr1 frf fr2 a1 af a2 e1 ef e2,
    ctx_type f Gh Th afh frh ah eh G (TFun T1 fr1 a1 T2 fr2 a2 e2) p1 frf af ef ->
    has_type G t T1 p2 fr1 a1 e1 ->
    ctx_type (capp1 f t) Gh Th afh frh ah eh G T2 (qor p1 p2) ((frf||fr1)&&a2 || fr2) ((af||a1)&&a2) (e1 || ef || (af||a1)&&e2)
| c_app2: forall Gh Th afh frh ah eh G f t T1 T2 p1 p2 fr1 frf fr2 a1 af a2 e1 ef e2,
    has_type G f (TFun T1 fr1 a1 T2 fr2 a2 e2) p1 frf af ef ->
    ctx_type t Gh Th afh frh ah eh G T1 p2 fr1 a1 e1 ->
    ctx_type (capp2 f t) Gh Th afh frh ah eh G T2 (qor p1 p2) ((frf||fr1)&&a2 || fr2) ((af||a1)&&a2) (e1 || ef || (af||a1)&&e2)
| c_abs: forall Gh Th afh frh ah eh G t T1 T2 p2 pf fr1 fr2 af a1 a2 e2,
    ctx_type t Gh Th afh frh ah eh ((T1,fr1,a1)::G) T2 p2 fr2 a2 e2 ->
    pf = (qdiff p2 (qone (length G))) ->
    env_cap G pf af ->
    ctx_type (cabs t) Gh Th afh frh ah eh G (TFun T1 fr1 a1 T2 fr2 a2 e2) pf false ((e2||a2)&&(af||afh)) false 
| c_not: forall Gh Th afh frh ah eh G t p fr a e,
    ctx_type t Gh Th afh frh ah eh G TBool p fr a e -> 
    ctx_type (cnot t) Gh Th afh frh ah eh G TBool p false false e
| c_bin1: forall Gh Th afh frh ah eh G t1 p1 fr1 a1 e1 t2 p2 fr2 a2 e2,
    ctx_type t1 Gh Th afh frh ah eh G TBool p1 fr1 a1 e1 ->
    has_type G t2 TBool p2 fr2 a2 e2 ->
    ctx_type (cbin1 t1 t2) Gh Th afh frh ah eh G TBool (qor p1 p2) false false (e1||e2)
| c_bin2: forall Gh Th afh frh ah eh G t1 p1 fr1 a1 e1 t2 p2 fr2 a2 e2,
    has_type G t1 TBool p1 fr1 a1 e1 ->
    ctx_type t2 Gh Th afh frh ah eh G TBool p2 fr2 a2 e2 ->
    ctx_type (cbin2 t1 t2) Gh Th afh frh ah eh G TBool (qor p1 p2) false false (e1||e2)
| c_sub_fresh: forall Gh Th afh frh ah eh G t T p fr a e,
    ctx_type t Gh Th afh frh ah eh G T p fr a e ->
    ctx_type t Gh Th afh frh ah eh G T p true a e
| c_sub_cap: forall Gh Th afh frh ah eh G t T p fr a e,
    ctx_type t Gh Th afh frh ah eh G T p fr a e ->
    ctx_type t Gh Th afh frh ah eh G T p fr true e
| c_sub_eff: forall Gh Th afh frh ah eh G t T p fr a e,
    ctx_type t Gh Th afh frh ah eh G T p fr a e ->
    ctx_type t Gh Th afh frh ah eh G T p fr a true
| c_sub_stp: forall Gh Th afh frh ah eh G t T1 p fr1 a1 e1 T2 fr2 a2 e2,
    ctx_type t Gh Th afh frh ah eh G T1 p fr1 a1 e1 ->
    stp T1 T2 ->
    bsub fr1 fr2 ->
    bsub a1 a2 ->
    bsub e1 e2 ->
    ctx_type t Gh Th afh frh ah eh G T2 p fr2 a2 e2
.



(* ---------- contextual equivalence ---------- *)


(* semantic equivalence between contexts *)
Definition sem_ctx_type C C' G1 T1 af1 fr1 a1 e1 G2 T2 p2 fr2 a2 e2 :=
  forall t t' p1 p1',
    p1 = (fv (length G1) t) ->
    p1 = (fv (length G1) t') ->
    sem_type G1 t t' T1 (plift p1) fr1 a1 e1 ->
    p1' = qdiff p1 (qdiff (qdom G1) (qdom G2)) ->
    env_cap G1 p1 af1 ->
    qor p2 p1' = (fv (length G2) (plug C t)) /\
    qor p2 p1' = (fv (length G2) (plug C' t')) /\
    sem_type G2 (plug C t) (plug C' t') T2 (por (plift p2) (plift p1')) fr2 a2 e2.


(* contextual equivalence: no boolean context can detect a difference *)
Definition contextual_equiv G t1 t2 T1 (*p1*) af1 fr1 a1 e1 :=
  forall C,
    ctx_type C G T1 (*p1*) af1 fr1 a1 e1 [] TBool qempty false true true ->
    exists S1 S2 v,
      tevaln [] [] (plug C t1) S1 v /\
      tevaln [] [] (plug C t2) S2 v.


(* helper lemmas *)

Lemma aux0: forall t2 t0 n,
    (subst_tm (splice_tm t2 n 1) n t0) = t2.
Proof.
  intros t2. induction t2; intros; simpl.
  - eauto.
  - eauto.
  - bdestruct (i <? n).
    bdestruct (n =? i). lia.
    bdestruct (n <? i). lia. eauto.
    bdestruct (n <? i+1). 2: lia.
    bdestruct (n =? i+1). lia.
    replace (pred (i+1)) with i. eauto. lia.
  - rewrite IHt2. eauto.
  - rewrite IHt2. eauto.
  - rewrite IHt2_1, IHt2_2; eauto.
  - rewrite IHt2_1, IHt2_2; eauto.
  - rewrite IHt2. eauto.
  - rewrite IHt2. eauto. 
  - rewrite IHt2_1, IHt2_2; eauto.
Qed.


Lemma aux1: forall C Gh T1 G T2 af1 fr1 a1 e1 pt2 fr a e,
    ctx_type C Gh T1 af1 fr1 a1 e1 G T2 pt2 fr a e ->
    length G <= length Gh.
Proof. 
  intros ????????????? CX. induction CX; intros; subst; simpl in *; try lia.
Qed.

Lemma aux1b: forall C Gh T1 G T2 af1 fr1 a1 e1 pt2 fr a e,
    ctx_type C Gh T1 af1 fr1 a1 e1 G T2 pt2 fr a e ->
    exists G', Gh = G'++G.
Proof. 
  intros ????????????? CX. induction CX; intros; subst; simpl in *; try eauto.
  eexists []. eauto.
  destruct IHCX. eexists (x ++ [(T1, fr1, a1)]).
  rewrite <-app_assoc. simpl. eauto.
Qed.


Lemma ctxt_fv: forall Gh Th afh frh ah eh G t T p fr a e,
    ctx_type t Gh Th afh frh ah eh G T p fr a e ->
    p = cfv (length G) t.
Proof.
  intros. induction H; simpl; eauto.
  - eapply hast_fv in H0. congruence.
  - eapply hast_fv in H. congruence. 
  - eapply hast_fv in H0. congruence.
  - eapply hast_fv in H. congruence.
  - simpl in *. congruence. 
  - eapply hast_fv in H0. congruence.
  - eapply hast_fv in H. congruence. 
Qed.


Lemma ctxt_plug_fv: forall Gh Th afh frh ah eh G t T p fr a e,
    ctx_type t Gh Th afh frh ah eh G T p fr a e ->
    forall th ph ph',
    ph = fv (length Gh) th ->  
    ph' = qdiff ph (qdiff (qdom Gh) (qdom G)) -> (* substract bound vars *)
    qor p ph' = fv (length G) (plug t th).
Proof.
  intros ??????????????. induction H; intros; simpl in *; eauto.
  - subst. eapply functional_extensionality. intros.
    unfold qor, qempty, qdiff, qdom. simpl.
    bdestruct (x <? length G); simpl; eauto with bool. 
  - eapply hast_fv in H0. erewrite <-H0, <-IHctx_type; eauto.
    unfold qor. eapply functional_extensionality. intros.
    destruct (p1 x), (p2 x), (ph' x); eauto.
  - eapply hast_fv in H. erewrite <-H, <-IHctx_type; eauto.
    unfold qor. eapply functional_extensionality. intros.
    destruct (p1 x), (p2 x), (ph' x); eauto.
  - eapply hast_fv in H0. erewrite <-H0, <-IHctx_type; eauto.
    unfold qor. eapply functional_extensionality. intros.
    destruct (p1 x), (p2 x), (ph' x); eauto.
  - eapply hast_fv in H. erewrite <-H, <-IHctx_type; eauto. 
    unfold qor. eapply functional_extensionality. intros.
    destruct (p1 x), (p2 x), (ph' x); eauto.
  - erewrite <-IHctx_type. subst pf. 2: eauto. 2: eauto.
    subst ph' ph. 
    unfold qor, qdiff, qone, qdom. eapply functional_extensionality. intros.
    bdestruct (x =? length G). {
      subst x. simpl.
      bdestruct (length G <? length Gh). simpl. 
      bdestruct (length G <? length G). lia. simpl.
      bdestruct (length G <? S (length G)). lia. lia. 
      eapply aux1 in H. simpl in H. lia.
    } {
      destruct (p2 x); simpl. eauto.
      bdestruct (x <? length Gh); simpl. 
      bdestruct (x <? length G); simpl. 
      bdestruct (x <? S (length G)); simpl. 2: lia. 
      destruct (fv (length Gh) th x); eauto. 
      bdestruct (x <? S (length G)); simpl. lia. lia.
      destruct (fv (length Gh) th x); eauto. 
    }
  - eapply hast_fv in H0. erewrite <-H0, <-IHctx_type; eauto.
    unfold qor. eapply functional_extensionality. intros.
    destruct (p1 x), (p2 x), (ph' x); eauto.
  - eapply hast_fv in H. erewrite <-H, <-IHctx_type; eauto.
    unfold qor. eapply functional_extensionality. intros.
    destruct (p1 x), (p2 x), (ph' x); eauto.
Qed.


(* congruence: syntactic context typing implies semantic context typing *)
Theorem congr:
  forall C G1 T1 af1 fr1 a1 e1 G2 T2 p2 fr2 a2 e2,
    ctx_type C G1 T1 af1 fr1 a1 e1 G2 T2 p2 fr2 a2 e2 ->
    sem_ctx_type C C G1 T1 af1 fr1 a1 e1 G2 T2 p2 fr2 a2 e2.
Proof.
  intros ? ? ? ? ? ? ? ? ? ? ? ? ? CX.
  induction CX; intros ? ? ? ? PX1 PX2 ? PX1' EC1; simpl. 
  - (* hole *)
    split. 2: split.
    rewrite PX1', PX1. eapply functional_extensionality. intros.
    unfold qor, qempty, qdiff, qdom. simpl.
    bdestruct (x <? length G); eauto with bool.
    rewrite PX1', PX2. eapply functional_extensionality. intros.
    unfold qor, qempty, qdiff, qdom. simpl.
    bdestruct (x <? length G); eauto with bool.
    replace (por (plift qempty) (plift p1')) with (plift p1).
    eauto.
    subst p1'. rewrite plift_empty, por_empty_l, plift_diff, plift_diff, pdiff_same, pdiff_empty_r. eauto. 
  - (* ref *)
    split. 2: split.
    eapply ctxt_plug_fv; eauto.
    eapply ctxt_plug_fv; eauto. 
    intros u E ? ? ? ? ? WFE. 
    intros STWF S1 S2 q1 q2 ST LS1 LS2.
    eapply exp_ref; eauto. eapply IHCX; eauto.
  - (* get *)
    split. 2: split.
    eapply ctxt_plug_fv; eauto.
    eapply ctxt_plug_fv; eauto. 
    intros u E ? ? ? ? ? WFE. 
    intros STWF S1 S2 q1 q2 ST LS1 LS2.
    eapply exp_get; eauto. eapply IHCX; eauto.
    unfold bsub in *. intros ?. eapply E. destruct e; intuition. 
    rewrite exp_locs_get in LS1. intros ? ?. eapply LS1. destruct e; destruct a; intuition.
    rewrite exp_locs_get in LS2. intros ? ?. eapply LS2. destruct e; destruct a; intuition.
  - (* put1 *)
    split. 2: split.
    + replace (qor (qor p1 p2) p1') with (qor (qor p1 p1') p2).
      simpl. eapply hast_fv in H. eapply ctxt_plug_fv in CX. rewrite CX, H. eauto. eauto. eauto.
      rewrite plift_qual_eq, plift_or, plift_or, plift_or, plift_or, por_assoc, por_assoc.
      rewrite por_comm with (p1:=plift p2). eauto.
    + replace (qor (qor p1 p2) p1') with (qor (qor p1 p1') p2).
      simpl. eapply hast_fv in H. eapply ctxt_plug_fv in CX. rewrite CX, H. eauto. eauto. eauto.
      rewrite plift_qual_eq, plift_or, plift_or, plift_or, plift_or, por_assoc, por_assoc.
      rewrite por_comm with (p1:=plift p2). eauto.
    + rewrite plift_or. intros u E ? ? ? ? ? WFE. intros STWF S1 S2 q1 q2 ST LS1 LS2.
      assert (env_type M H1 H2 V1 V2 G u (por (plift p1) (plift p1'))) as WFE'. { eapply envt_tighten; eauto. unfoldq; intuition. }
      eapply IHCX in WFE' as A.
      2: eapply PX1. 2: eapply PX2. 2: eapply H0. 2: eapply PX1'. 2: eauto. 
      2: { unfold bsub in *. intros Q. eapply E. destruct e1; intuition. }
      edestruct A as (S1' & S2' & M' & v1 & v2 & ?). auto. eapply ST.
      intros ? ?. rewrite exp_locs_put in LS1. eapply LS1. destruct e1; try contradiction; simpl; left; auto. 
      intros ? ?. rewrite exp_locs_put in LS2. eapply LS2. destruct e1; try contradiction; simpl; left; auto. 
      eapply exp_put; eauto.
      exists v1, v2. eapply H3. destruct H3 as (? & ? & ? & ? & ?). intuition.
      eapply fundamental in H. eapply H.
      unfold bsub in *. intros Q. eapply E. destruct e1, e2, a1;intuition. 
      eapply envt_store_change. eapply envt_tighten. eapply WFE. unfoldq; intuition.
      { intros ? ? ? ? ?. eapply s. auto.  }
      destruct ST. destruct H8. lia. destruct ST. destruct H8. lia. auto.
      auto.
      intros ? ?. left. eapply LS1. rewrite exp_locs_put. destruct e2; try contradiction; destruct e1, a1; simpl; right; auto.
      intros ? ?. left. eapply LS2. rewrite exp_locs_put. destruct e2; try contradiction; destruct e1, a1; simpl; right; auto.
  - (* put2 *)
    split. 2: split.
    + replace (qor (qor p1 p2) p1') with (qor p1 (qor p2 p1')).
      simpl. eapply hast_fv in H. eapply ctxt_plug_fv in CX. rewrite CX, H. eauto. eauto. eauto.
      rewrite plift_qual_eq, plift_or, plift_or, plift_or, plift_or, por_assoc. eauto.
    + replace (qor (qor p1 p2) p1') with (qor p1 (qor p2 p1')).
      simpl. eapply hast_fv in H. eapply ctxt_plug_fv in CX. rewrite CX, H. eauto. eauto. eauto.
      rewrite plift_qual_eq, plift_or, plift_or, plift_or, plift_or, por_assoc. eauto.
    + rewrite plift_or. intros u E ? ? ? ? ? WFE. intros STWF S1 S2 q1 q2 ST LS1 LS2.
      eapply fundamental in H. 
      assert (env_type M H1 H2 V1 V2 G u (plift p1)) as WFE'. { eapply envt_tighten;eauto. unfoldq; intuition. }
      eapply H in WFE' as A.
      2: { unfold bsub in *. intros Q. eapply E. destruct e1; intuition. }
      edestruct A as (S1' & S2' & M' & v1 & v2 & ?). auto. eapply ST.
      intros ? ?. rewrite exp_locs_put in LS1. eapply LS1. destruct e1; try contradiction; simpl; left; auto. 
      intros ? ?. rewrite exp_locs_put in LS2. eapply LS2. destruct e1; try contradiction; simpl; left; auto. 
      eapply exp_put; eauto.
      exists v1, v2. eapply H3. destruct H3 as (? & ? & ? & ? & ?). intuition.
      eapply IHCX. eapply PX1. eapply PX2. eapply H0. eapply PX1'. eauto.
      unfold bsub in *. intros Q. eapply E. destruct e1, e2, a1;intuition. 
      eapply envt_store_change. eapply envt_tighten. eapply WFE. unfoldq; intuition.
      { intros ? ? ? ? ?. eapply s. auto.  }
      destruct ST. destruct H8. lia. destruct ST. destruct H8. lia. auto.
      auto.
      intros ? ?. left. eapply LS1. rewrite exp_locs_put. destruct e2; try contradiction; destruct e1, a1; simpl; right; auto.
      intros ? ?. left. eapply LS2. rewrite exp_locs_put. destruct e2; try contradiction; destruct e1, a1; simpl; right; auto.
  - (* app1 *)
    split. 2: split.
    + replace (qor (qor p1 p2) p1') with (qor (qor p1 p1') p2).
      simpl. eapply hast_fv in H. eapply ctxt_plug_fv in CX. rewrite CX, H. eauto. eauto. eauto.
      rewrite plift_qual_eq, plift_or, plift_or, plift_or, plift_or, por_assoc, por_assoc.
      rewrite por_comm with (p1:=plift p2). eauto.
    + replace (qor (qor p1 p2) p1') with (qor (qor p1 p1') p2).
      simpl. eapply hast_fv in H. eapply ctxt_plug_fv in CX. rewrite CX, H. eauto. eauto. eauto.
      rewrite plift_qual_eq, plift_or, plift_or, plift_or, plift_or, por_assoc, por_assoc.
      rewrite por_comm with (p1:=plift p2). eauto.
    + rewrite plift_or. 
      intros u E ? ? ? ? ? WFE. intros STWF S1 S2 q1 q2 ST LS1 LS2.
      assert (env_type M H1 H2 V1 V2 G u (por (plift p1) (plift p1'))) as WFE'. { eapply envt_tighten;eauto. unfoldq; intuition. }
      eapply IHCX in WFE' as A.
      2: eapply PX1. 2: eapply PX2. 2: eapply H0. 2: eapply PX1'. 2: eauto.
      2: { unfold bsub in *. intros Q. eapply E. destruct e1; intuition. }
      edestruct A as (S1' & S2' & M' & v1 & v2 & ?). auto. eapply ST.
      intros ? ?. rewrite exp_locs_app in LS1. eapply LS1. destruct ef; try contradiction; destruct e1; simpl; left; auto. 
      intros ? ?. rewrite exp_locs_app in LS2. eapply LS2. destruct ef; try contradiction; destruct e1; simpl; left; auto. 
      eapply exp_app; eauto.
      exists v1, v2. eapply H3. destruct H3 as (? & ? & ? & ? & ?). intuition.
      eapply fundamental in H. eapply H.
      unfold bsub in *. intros Q. eapply E. destruct e1, e2, a1;intuition. 
      eapply envt_store_change. eapply envt_tighten. eapply WFE. unfoldq; intuition.
      { intros ? ? ? ? ?.  eapply H3. auto. }
      destruct ST. destruct H9. lia. destruct ST. destruct H9. lia. auto.
      auto.
      intros ? ?. left. eapply LS1. rewrite exp_locs_app. destruct e1; try contradiction; simpl; right; auto.
      intros ? ?. left. eapply LS2. rewrite exp_locs_app. destruct e1; try contradiction; simpl; right; auto.
      unfold bsub in *. destruct e2, u, af, a1, a2; simpl in *; intuition.
      unfold bsub in *. destruct e2, u, af, a1, a2; simpl in *; intuition.
      unfold bsub in *. destruct e2, u, af, a1, a2; simpl in *; intuition.
      unfold bsub in *. destruct e2, u, af, a1, a2; simpl in *; intuition. 
  - (* app2 *)
    split. 2: split.
    + replace (qor (qor p1 p2) p1') with (qor p1 (qor p2 p1')).
      simpl. eapply hast_fv in H. eapply ctxt_plug_fv in CX. rewrite CX, H. eauto. eauto. eauto.
      rewrite plift_qual_eq, plift_or, plift_or, plift_or, plift_or, por_assoc. eauto.
    + replace (qor (qor p1 p2) p1') with (qor p1 (qor p2 p1')).
      simpl. eapply hast_fv in H. eapply ctxt_plug_fv in CX. rewrite CX, H. eauto. eauto. eauto.
      rewrite plift_qual_eq, plift_or, plift_or, plift_or, plift_or, por_assoc. eauto.
    + rewrite plift_or. 
      intros u E ? ? ? ? ? WFE. intros STWF S1 S2 q1 q2 ST LS1 LS2.
      eapply fundamental in H. 
      assert (env_type M H1 H2 V1 V2 G u (plift p1)) as WFE'. { eapply envt_tighten;eauto. unfoldq; intuition. }
      eapply H in WFE' as A.
      2: { unfold bsub in *. intros Q. eapply E. destruct e1; intuition. }
      edestruct A as (S1' & S2' & M' & v1 & v2 & ?). auto. eapply ST.
      intros ? ?. rewrite exp_locs_app in LS1. eapply LS1. destruct ef; try contradiction; destruct e1; simpl; left; auto. 
      intros ? ?. rewrite exp_locs_app in LS2. eapply LS2. destruct ef; try contradiction; destruct e1; simpl; left; auto. 
      eapply exp_app; eauto.
      exists v1, v2. eapply H3. destruct H3 as (? & ? & ? & ? & ?). intuition.
      eapply IHCX. eapply PX1. eapply PX2. eapply H0. eapply PX1'. eauto.
      unfold bsub in *. intros Q. eapply E. destruct e1, e2, a1;intuition. 
      eapply envt_store_change. eapply envt_tighten. eapply WFE. unfoldq; intuition.
      { intros ? ? ? ? ?. eapply H3. auto.  }
      destruct ST. destruct H9. lia. destruct ST. destruct H9. lia. auto.
      auto.
      intros ? ?. left. eapply LS1. rewrite exp_locs_app. destruct e1; try contradiction; simpl; right; auto.
      intros ? ?. left. eapply LS2. rewrite exp_locs_app. destruct e1; try contradiction; simpl; right; auto.
      unfold bsub in *. destruct e2, u, af, a1, a2; simpl in *; intuition.
      unfold bsub in *. destruct e2, u, af, a1, a2; simpl in *; intuition.
      unfold bsub in *. destruct e2, u, af, a1, a2; simpl in *; intuition.
      unfold bsub in *. destruct e2, u, af, a1, a2; simpl in *; intuition.
  - (* abs *)
    split. 2: split.
    + eapply ctxt_plug_fv in CX as C1. 2: eapply PX1. 2: eauto.
      rewrite H. simpl in C1. rewrite <-C1. rewrite PX1'. 
      rewrite plift_qual_eq. rewrite plift_or, plift_diff, plift_one.
      rewrite plift_diff, plift_diff, plift_diff, plift_or, plift_or.
      rewrite plift_diff, plift_diff, plift_dom.
      rewrite plift_dom, plift_dom, plift_one.
      rewrite por_same. 
      eapply functional_extensionality. intros.
      eapply propositional_extensionality. split.
      unfoldq. intuition. right. split. eauto.
      intros. destruct H4. eapply H3 in H4 as XX. eauto.
      intros. eapply H5. unfoldq. intuition. simpl. lia. 
      eapply aux1 in CX. simpl in CX.
      eapply H3. lia. lia.
      unfoldq. intuition. right. split. eauto.
      intros. destruct H5. eapply H2. eauto. simpl. lia.

    + eapply ctxt_plug_fv in CX as C1. 2: eapply PX2. 2: eauto.
      rewrite H. simpl in C1. rewrite <-C1. rewrite PX1'. 
      rewrite plift_qual_eq. rewrite plift_or, plift_diff, plift_one.
      rewrite plift_diff, plift_diff, plift_diff, plift_or, plift_or.
      rewrite plift_diff, plift_diff, plift_dom.
      rewrite plift_dom, plift_dom, plift_one.
      rewrite por_same. 
      eapply functional_extensionality. intros.
      eapply propositional_extensionality. split.
      unfoldq. intuition. right. split. eauto.
      intros. destruct H4. eapply H3 in H4 as XX. eauto.
      intros. eapply H5. unfoldq. intuition. simpl. lia. 
      eapply aux1 in CX. simpl in CX.
      eapply H3. lia. lia.
      unfoldq. intuition. right. split. eauto.
      intros. destruct H5. eapply H2. eauto. simpl. lia.

    + rewrite <-plift_or. eapply sem_abs. eauto. rewrite plift_or. 

      eapply IHCX. eapply PX1. eapply PX2. eauto. eauto. eauto.

      subst p1' pf.
      rewrite plift_qual_eq. rewrite plift_or, plift_diff, plift_one.
      rewrite plift_diff, plift_diff, plift_dom, plift_diff, plift_dom.
      rewrite plift_or, plift_or, plift_diff, plift_one, plift_diff.
      rewrite plift_dom, plift_dom.
      rewrite por_same.
      eapply functional_extensionality. intros.
      eapply propositional_extensionality. split.
      unfoldq. intuition. right. split. eauto.
      intros. destruct H3. eapply H2 in H3 as XX. eauto.
      intros. eapply H4. simpl. eauto.
      eapply aux1 in CX. simpl in CX.
      eapply H2. lia. lia.
      unfoldq. intuition. right. split. eauto.
      intros. destruct H4. eapply H. eauto. simpl. lia.

      eapply ctxt_plug_fv in CX. 2: eapply PX1. 2: eauto. eapply CX.
      
      eapply ctxt_plug_fv in CX as C1. 2: eapply PX1. 2: eauto. 
      eapply ctxt_plug_fv in CX as C2. 2: eapply PX2. 2: eauto. 
      simpl in *. congruence.

      intros ??????. assert (por (plift pf) (plift p1') x) as C.
      rewrite <-plift_or. eauto. destruct C as [C|C].
      eapply H0 in C. unfold bsub. 2: eauto. intuition.
      subst p1'. rewrite plift_diff in C. destruct C as (C & ?).
      assert (indexr x Gh = Some (T0, fr0, a0)). {
        eapply aux1b in CX. destruct CX. subst Gh.
        eapply indexr_var_some' in H2 as L. 
        rewrite indexr_skips. rewrite indexr_skip. eauto. lia. simpl. lia. }
      eapply EC1 in C. 2: eauto. unfold bsub. intuition.

  - (* not *)
    split. 2: split.
    eapply ctxt_plug_fv; eauto.
    eapply ctxt_plug_fv; eauto.
    intros u E ? ? ? ? ? WFE.
    intros STWF S1 S2 q1 q2 ST LS1 LS2.
    eapply exp_tnot; eauto. eapply IHCX; eauto.
  - (* bin1 *)
    split. 2: split.
    + replace (qor (qor p1 p2) p1') with (qor (qor p1 p1') p2).
      simpl. eapply hast_fv in H. eapply ctxt_plug_fv in CX. rewrite CX, H. eauto. eauto. eauto.
      rewrite plift_qual_eq, plift_or, plift_or, plift_or, plift_or, por_assoc, por_assoc.
      rewrite por_comm with (p1:=plift p2). eauto.
    + replace (qor (qor p1 p2) p1') with (qor (qor p1 p1') p2).
      simpl. eapply hast_fv in H. eapply ctxt_plug_fv in CX. rewrite CX, H. eauto. eauto. eauto.
      rewrite plift_qual_eq, plift_or, plift_or, plift_or, plift_or, por_assoc, por_assoc.
      rewrite por_comm with (p1:=plift p2). eauto.
    + rewrite plift_or. 
      intros u E ? ? ? ? ? WFE. intros STWF S1 S2 q1 q2 ST LS1 LS2.
      assert (env_type M H1 H2 V1 V2 G u (por (plift p1) (plift p1'))) as WFE'. { eapply envt_tighten;eauto. unfoldq; intuition. }
      eapply IHCX in WFE' as A.
      2: eapply PX1. 2: eapply PX2. 2: eapply H0. 2: eapply PX1'. 2: eauto.
      2: { unfold bsub in *. intros Q. eapply E. destruct e1; intuition. }
      edestruct A as (S1' & S2' & M' & v1 & v2 & ?). auto. eapply ST.
      intros ? ?. rewrite exp_locs_tbin in LS1. eapply LS1. destruct e1; try contradiction; simpl; left; auto. 
      intros ? ?. rewrite exp_locs_tbin in LS2. eapply LS2. destruct e1; try contradiction; simpl; left; auto. 
      eapply exp_tbin; eauto.
      exists v1, v2. eapply H3. destruct H3 as (? & ? & ? & ? & ?). intuition.
      eapply fundamental in H. eapply H.
      unfold bsub in *. intros Q. eapply E. destruct e1, e2, a1;intuition. 
      eapply envt_store_change. eapply envt_tighten. eapply WFE. unfoldq; intuition.
      { intros ? ? ? ? ?. eapply s. auto.  }
      destruct ST. destruct H8. lia. destruct ST. destruct H8. lia. auto.
      auto.
      intros ? ?. left. eapply LS1. rewrite exp_locs_tbin. destruct e2; try contradiction; destruct e1; simpl; right; auto.
      intros ? ?. left. eapply LS2. rewrite exp_locs_tbin. destruct e2; try contradiction; destruct e1; simpl; right; auto.
  - (* bin2 *)
    split. 2: split.
    + replace (qor (qor p1 p2) p1') with (qor p1 (qor p2 p1')).
      simpl. eapply hast_fv in H. eapply ctxt_plug_fv in CX. rewrite CX, H. eauto. eauto. eauto.
      rewrite plift_qual_eq, plift_or, plift_or, plift_or, plift_or, por_assoc. eauto.
    + replace (qor (qor p1 p2) p1') with (qor p1 (qor p2 p1')).
      simpl. eapply hast_fv in H. eapply ctxt_plug_fv in CX. rewrite CX, H. eauto. eauto. eauto.
      rewrite plift_qual_eq, plift_or, plift_or, plift_or, plift_or, por_assoc. eauto.
    + rewrite plift_or. 
      intros u E ? ? ? ? ? WFE. intros STWF S1 S2 q1 q2 ST LS1 LS2.
      eapply fundamental in H. 
      assert (env_type M H1 H2 V1 V2 G u (plift p1)) as WFE'. { eapply envt_tighten;eauto. unfoldq; intuition. }
      eapply H in WFE' as A.
      2: { unfold bsub in *. intros Q. eapply E. destruct e1; intuition. }
      edestruct A as (S1' & S2' & M' & v1 & v2 & ?). auto. eapply ST.
      intros ? ?. rewrite exp_locs_tbin in LS1. eapply LS1. destruct e1; try contradiction; simpl; left; auto. 
      intros ? ?. rewrite exp_locs_tbin in LS2. eapply LS2. destruct e1; try contradiction; simpl; left; auto. 
      eapply exp_tbin; eauto.
      exists v1, v2. eapply H3. destruct H3 as (? & ? & ? & ? & ?). intuition.
      eapply IHCX. eapply PX1. eapply PX2. eapply H0. eapply PX1'. eauto.
      unfold bsub in *. intros Q. eapply E. destruct e1, e2, a1;intuition. 
      eapply envt_store_change. eapply envt_tighten. eapply WFE. unfoldq; intuition.
      { intros ? ? ? ? ?.  eapply s. auto.  }
      destruct ST. destruct H8. lia. destruct ST. destruct H8. lia. auto.
      auto.
      intros ? ?. left. eapply LS1. rewrite exp_locs_tbin. destruct e2; try contradiction; destruct e1; simpl; right; auto.
      intros ? ?. left. eapply LS2. rewrite exp_locs_tbin. destruct e2; try contradiction; destruct e1; simpl; right; auto.
  - (* sub fresh *)
    split. 2: split.
    simpl. eapply ctxt_plug_fv in CX. eauto. eauto. eauto. 
    simpl. eapply ctxt_plug_fv in CX. eauto. eauto. eauto. 
    intros u E ? ? ? ? ? WFE. intros STWF S1 S2 q1 q2 ST LS1 LS2.
    eapply exp_sub_fresh; eauto.
    eapply IHCX; eauto. 
  - (* sub cap *)
    split. 2: split.
    simpl. eapply ctxt_plug_fv in CX. eauto. eauto. eauto.
    simpl. eapply ctxt_plug_fv in CX. eauto. eauto. eauto.
    intros u E ? ? ? ? ? WFE. intros STWF S1 S2 q1 q2 ST LS1 LS2.
    eapply exp_sub_cap; eauto.
    eapply IHCX; eauto. 
  - (* sub eff *)
    split. 2: split.
    simpl. eapply ctxt_plug_fv in CX. eauto. eauto. eauto.
    simpl. eapply ctxt_plug_fv in CX. eauto. eauto. eauto.
    intros u E ? ? ? ? ? WFE. intros STWF S1 S2 q1 q2 ST LS1 LS2.
    eapply exp_sub_eff; eauto.
    eapply IHCX; eauto. 
    unfold bsub in *. intros. eapply E. auto.
    intros ? ?. destruct e; try contradiction. eapply LS1. auto.
    intros ? ?. destruct e; try contradiction. eapply LS2. auto.
  - (* sub stp *)
    split. 2: split.
    simpl. eapply ctxt_plug_fv in CX. eauto. eauto. eauto.
    simpl. eapply ctxt_plug_fv in CX. eauto. eauto. eauto.
    unfold bsub in *.
    intros u E ? ? ? ? ? WFE. intros STWF S1 S2 q1 q2 ST LS1 LS2.
    eapply IHCX in WFE as A. 2: eapply PX1. 2: eapply PX2.
    edestruct A as  (S1'&S2'&M'&?&?&?&?&?&?). all: eauto.
    intros ? ?. eapply LS1. destruct e1, e2; simpl in *; intuition.
    intros ? ?. eapply LS2. destruct e1, e2; simpl in *; intuition.
    exists S1', S2', M', x, x0,  (negb a2 || u), (if (negb a2 || u) then x2 else qempty), (if (negb a2 || u) then x3 else qempty).
    eapply exp_sub_stp2; eauto. 
    eapply stp_fundamental. eauto. 
    unfold bsub in *. destruct e1, e2, u; simpl in *; intuition.
Qed.


(* soundness of binary logical relation: implies contextual equivalence *)
Theorem soundness': forall G t1 t2 T p af fr a e,
  p = (fv (length G) t1) ->
  p = (fv (length G) t2) ->
  env_cap G p af ->
  sem_type G t1 t2 T (plift p) fr a e ->
  contextual_equiv G t1 t2 T af fr a e.
Proof.
  intros. intros ? ?.
  eapply adequacy.
  eapply congr; eauto.
Qed.

Theorem soundness: forall G t1 t2 T p af fr a e,
  has_type G t1 T p fr a e ->
  has_type G t2 T p fr a e ->
  env_cap G p af ->
  sem_type G t1 t2 T (plift p) fr a e ->
  contextual_equiv G t1 t2 T af fr a e.
Proof.
  intros. intros ? ?.
  eapply soundness'.
  eapply hast_fv in H. eauto.
  eapply hast_fv in H0. eauto.
  eauto. eauto. eauto.
Qed.



(* ---------- contextual purity ---------- *)

(* convenience *)
Definition tlet t1 t2 := tapp (tabs t2) t1.

(* contextual purity: can't observe difference between term and term bound to a var *)
Definition contextual_purity G t1 T1 a1 := forall Gh afh C T2 pt2 af fr a e, 
    ctx_type C Gh T1 afh false a1 false G T2 pt2 fr a e -> 
    env_cap G pt2 af ->
    bsub a1 afh ->
    psub (plift pt2) (pdom G) -> 
    sem_type G
      (tlet t1 (plug (splice_ctx C (length G) 1) (tvar (length G))))
      (plug C (splice_tm t1 (length G) (length Gh - length G)))
      T2 (por (plift pt2) (plift (fv (length G) t1))) fr a e.



Lemma auxB: forall C Gh T1 G T2 af1 fr1 a1 e1 pt2 fr a e,
    ctx_type C Gh T1 af1 fr1 a1 e1 G T2 pt2 fr a e ->
    forall C' t1 t1' t2 n,
    C' = splice_ctx C n 1 ->
    t1' = splice_tm t1 n (length Gh - length G) ->
    t2 = plug C' (tvar n) ->
    subst_tm t2 n t1 = plug C t1'.
Proof.
  intros ????????????? CX. induction CX; intros; subst; simpl.
  - bdestruct (n =? n). 2: contradiction.
    replace (length G - length G) with 0.  rewrite splice_zero. eauto. lia.
  - erewrite IHCX; eauto.
  - erewrite IHCX; eauto.
  - erewrite IHCX; eauto.
    rewrite aux0; eauto. 
  - rewrite aux0; eauto.
    erewrite IHCX; eauto.
  - erewrite IHCX; eauto.
    rewrite aux0; eauto. 
  - rewrite aux0; eauto.
    erewrite IHCX; eauto.
  - erewrite IHCX; eauto. simpl. rewrite splice_acc.
    replace (length Gh - S (length G) + 1) with (length Gh - length G). eauto.
    eapply aux1 in CX. simpl in CX. lia. 
  - erewrite IHCX; eauto.
  - erewrite IHCX; eauto.
    rewrite aux0; eauto. 
  - rewrite aux0; eauto.
    erewrite IHCX; eauto.
  - erewrite IHCX; eauto.
  - erewrite IHCX; eauto.
  - erewrite IHCX; eauto.
  - erewrite IHCX; eauto.
Qed.

Lemma env_cap_weaken: forall G G' pt2 af,
    env_cap (G'++G) pt2 af -> forall GX,
    env_cap (G'++GX++G) (splice_ql pt2 (length G) (length GX)) af.
Proof.
  intros. intros ??????.

  unfold splice_ql in H1. 
  bdestruct (x <? length G).
  eapply H. rewrite indexr_skips, indexr_skips in H0. rewrite indexr_skips.
  eauto. eauto. eauto. rewrite app_length. lia. eauto. 
  bdestruct (x <? length G + length GX). inversion H1.
  eapply (H (x - length GX)). 2: eauto.
  erewrite <-indexr_splice.
  bdestruct (x - length GX <? length G). lia.
  rewrite <-H0. replace x with (x - length GX + length GX) at 2.
  eauto. lia. 
Qed.

Lemma hast_weaken: forall G G' t2 T2 pt2 fr a e,
    has_type (G'++G) t2 T2 pt2 fr a e -> forall GX,
    has_type (G'++GX++G) (splice_tm t2 (length G) (length GX)) T2 (splice_ql pt2 (length G) (length GX)) fr a e.
Proof.
  intros. remember (G'++G) as GY. revert GX. revert HeqGY. revert G G'. 
  induction H; intros; simpl; try solve [econstructor; eauto].
  - rewrite splice_empty. eauto.
  - rewrite splice_empty. eauto.
  - rewrite splice_one. eapply t_var.
    rewrite indexr_splice. subst. eauto. 
  - rewrite splice_or. eapply t_put; eauto.
  - rewrite splice_or. eapply t_app; eauto. 
  - simpl. specialize (IHhas_type G ((T1, fr1, a1) :: G')).
    simpl in IHhas_type. eapply t_abs. eapply IHhas_type. subst. eauto.
    subst. rewrite splice_diff, splice_one.
    bdestruct (length (G' ++ G) <? length G). rewrite app_length in *. lia.
    rewrite app_length, app_length, app_length.
    replace (length G' + length G + length GX) with (length G' + (length GX + length G)).
    eauto. lia.
    eapply env_cap_weaken. subst. eauto.
  - rewrite splice_or. eapply t_bin; eauto.
Qed.


Lemma hast_weaken1: forall G t2 T2 pt2 fr a e T1 fr1 a1,
    has_type G t2 T2 pt2 fr a e ->
    has_type ((T1, fr1, a1) :: G) (splice_tm t2 (length G) 1) T2 (splice_ql pt2 (length G) 1) fr a e.
Proof.
  intros. eapply hast_weaken with (G':=[]) (GX:=[(T1,fr1,a1)]) in H. simpl in H. eapply H. 
Qed.


Lemma ctxt_weaken: forall C Gh T1 G' G T2 af1 fr1 a1 e1 pt2 fr a e,
    ctx_type C (Gh++G'++G) T1 af1 fr1 a1 e1 (G'++G) T2 pt2 fr a e -> forall GX,
    ctx_type (splice_ctx C (length G) (length GX)) (Gh++G'++GX++G) T1 af1 fr1 a1 e1 (G'++GX++G) T2 (splice_ql pt2 (length G) (length GX)) fr a e.
Proof.
  intros. 
  remember (G'++G) as GY. remember (Gh++GY) as GYh. revert GX HeqGY HeqGYh. revert G G' Gh.
  induction H; intros; simpl; try solve [econstructor; eauto].
  - rewrite splice_empty. replace G with ([]++G) in HeqGYh at 1.
    eapply app_inv_tail in HeqGYh. 2: eauto. subst Gh. simpl. eapply c_hole. 
  - rewrite splice_or. eapply c_put1. eauto. eapply hast_weaken. subst. eauto.
  - rewrite splice_or. eapply c_put2. eapply hast_weaken. subst. eauto. eauto.
  - rewrite splice_or. eapply c_app1. eauto. eapply hast_weaken. subst. eauto.
  - rewrite splice_or. eapply c_app2. eapply hast_weaken. subst. eauto. eauto.
  - subst G. subst Gh. specialize (IHctx_type G0 ((T1, fr1, a1) :: G')).
    eapply aux1b in H as H'. destruct H' as (Gh1 & ?).
    replace (Gh1 ++ (T1, fr1, a1) :: G' ++ G0) with (Gh1 ++ [(T1, fr1, a1)] ++ G' ++ G0) in H2.
    2: simpl; eauto. assert (Gh0 = Gh1 ++ [(T1, fr1, a1)]).
    rewrite app_assoc, app_assoc, app_assoc in H2. eapply app_inv_tail, app_inv_tail in H2. eauto.
    subst Gh0. repeat rewrite <-app_assoc. simpl. 
    simpl in IHctx_type. eapply c_abs. eapply IHctx_type. eauto. eauto.
    subst pf. rewrite splice_diff, splice_one.
    bdestruct (length (G' ++ G0) <? length G0). rewrite app_length in *. lia.
    rewrite app_length, app_length, app_length.
    replace (length G' + length G0 + length GX) with (length G' + (length GX + length G0)).
    eauto. lia.
    eapply env_cap_weaken. subst. eauto.
  - rewrite splice_or. eapply c_bin1. eauto. eapply hast_weaken. subst. eauto.
  - rewrite splice_or. eapply c_bin2. eapply hast_weaken. subst. eauto. eauto.
Qed.

Lemma ctxt_weaken1: forall C Gh T1 G T2 af1 fr1 a1 e1 pt2 fr a e Tx frx ax,
    ctx_type C (Gh++G) T1 af1 fr1 a1 e1 G T2 pt2 fr a e ->
    ctx_type (splice_ctx C (length G) 1) (Gh++(Tx,frx,ax)::G) T1 af1 fr1 a1 e1 ((Tx,frx,ax)::G) T2 (splice_ql pt2 (length G) 1) fr a e.
Proof.
  intros. eapply ctxt_weaken with (G':=[]) (GX:=[(Tx,frx,ax)]) in H. simpl in H. eapply H. 
Qed.
  

Lemma plug_hast: forall C Gh T1 G T2 t1 af1 fr1 a1 e1 pt2 fr a e,
    ctx_type C Gh T1 af1 fr1 a1 e1 G T2 pt2 fr a e -> forall pt1,
    has_type Gh t1 T1 pt1 fr1 a1 e1 ->
    env_cap Gh pt1 af1 -> 
    has_type G (plug C t1) T2 (qor pt2 (qand pt1 (qdom G))) fr a e.
Proof.
  intros. revert pt1 H0 H1. induction H; intros; simpl.
  - simpl. eapply hast_closed in H0 as H0'.
    replace (qor qempty (qand pt1 (qdom G))) with pt1. eauto.
    rewrite plift_qual_eq. rewrite plift_or, plift_and, plift_empty, plift_dom, por_empty_l.
    eapply functional_extensionality. intros.
    eapply propositional_extensionality. unfoldq. intuition. 
  - eapply t_ref. eauto.
  - eapply t_get. eauto.
  - replace (qor (qor p1 p2) (qand pt1 (qdom G))) with (qor (qor p1 (qand pt1 (qdom G))) p2).
    eapply t_put. eapply IHctx_type. eauto. eauto. eauto.
    rewrite plift_qual_eq. rewrite plift_or, plift_or, plift_or, plift_or.
    eapply functional_extensionality. intros.
    eapply propositional_extensionality. unfoldq. intuition. 
  - replace (qor (qor p1 p2) (qand pt1 (qdom G))) with (qor p1 (qor p2 (qand pt1 (qdom G)))).
    eapply t_put. eauto. eapply IHctx_type. eauto. eauto.
    rewrite plift_qual_eq. rewrite plift_or, plift_or, plift_or, plift_or.
    eapply functional_extensionality. intros.
    eapply propositional_extensionality. unfoldq. intuition. 
  - replace (qor (qor p1 p2) (qand pt1 (qdom G))) with (qor (qor p1 (qand pt1 (qdom G))) p2).
    eapply t_app. eapply IHctx_type. eauto. eauto. eauto.
    rewrite plift_qual_eq. rewrite plift_or, plift_or, plift_or, plift_or.
    eapply functional_extensionality. intros.
    eapply propositional_extensionality. unfoldq. intuition. 
  - replace (qor (qor p1 p2) (qand pt1 (qdom G))) with (qor p1 (qor p2 (qand pt1 (qdom G)))).
    eapply t_app. eauto. eapply IHctx_type. eauto. eauto.
    rewrite plift_qual_eq. rewrite plift_or, plift_or, plift_or, plift_or.
    eapply functional_extensionality. intros.
    eapply propositional_extensionality. unfoldq. intuition. 
  - eapply t_abs. eauto. subst pf.
    rewrite plift_qual_eq. rewrite plift_or, plift_diff, plift_diff, plift_or.
    rewrite plift_and, plift_one, plift_and, plift_dom, plift_dom. 
    eapply functional_extensionality. intros.
    eapply propositional_extensionality. unfoldq. simpl. intuition. 
    intros ??????. assert (plift (qor pf (qand pt1 (qdom G))) x). eauto.
    rewrite plift_or, plift_and, plift_dom in H6.
    destruct H6. eapply H1 in H6. 2: eauto. unfold bsub in *. intuition.
    destruct H6. eapply H3 in H6.
    2: {
      eapply aux1b in H. destruct H as (G' & ?). subst Gh.
      rewrite indexr_skips. rewrite indexr_skip. eauto. unfoldq. lia. simpl. unfoldq. lia.
    }
    unfold bsub in *. intuition. 
  - eapply t_not. eauto.
  - replace (qor (qor p1 p2) (qand pt1 (qdom G))) with (qor (qor p1 (qand pt1 (qdom G))) p2).
    eapply t_bin. eapply IHctx_type. eauto. eauto. eauto.
    rewrite plift_qual_eq. rewrite plift_or, plift_or, plift_or, plift_or.
    eapply functional_extensionality. intros.
    eapply propositional_extensionality. unfoldq. intuition. 
  - replace (qor (qor p1 p2) (qand pt1 (qdom G))) with (qor p1 (qor p2 (qand pt1 (qdom G)))).
    eapply t_bin. eauto. eapply IHctx_type. eauto. eauto. 
    rewrite plift_qual_eq. rewrite plift_or, plift_or, plift_or, plift_or.
    eapply functional_extensionality. intros.
    eapply propositional_extensionality. unfoldq. intuition.
  - econstructor. eauto.
  - econstructor. eauto.
  - econstructor. eauto.
  - econstructor. 2-5: eauto. eapply IHctx_type; eauto.
Qed.


Lemma auxA: forall C Gh T1 G T2 af1 fr1 a1 e1 pt2 fr a e,
    ctx_type C Gh T1 af1 fr1 a1 e1 G T2 pt2 fr a e ->
    fr1 = false ->
    e1 = false ->
    forall C' t2,
    C' = splice_ctx C (length G) 1 ->
    t2 = plug C' (tvar (length G)) ->
    bsub a1 af1 ->
    has_type ((T1, fr1, a1) :: G) t2 T2 (qor (splice_ql pt2 (length G) 1) (qone (length G))) fr a e.
Proof.
  intros ????????????? CX.
  eapply aux1b in CX as CX'. destruct CX' as (Gh' & ?). subst Gh. 
  eapply ctxt_weaken1 with (Tx:=T1) (frx:=fr1) (ax:=a1) in CX. intros.
  eapply plug_hast with (t1:=tvar (length G)) (pt1:=qone (length G)) in CX. subst t2 C'. 
  replace (qand (qone (length G)) (qdom ((T1, fr1, a1) :: G))) with (qone (length G)) in CX.
  eapply CX.
  rewrite plift_qual_eq. rewrite plift_one, plift_and, plift_dom, plift_one.
  unfoldq. intuition. simpl.
  eapply functional_extensionality. intros.
  eapply propositional_extensionality. intuition.   
  specialize t_var. intros. specialize (H4 (length G) (Gh'++(T1,false,a1)::G) T1 a1 false).
  rewrite indexr_skips in H4. 
  rewrite indexr_head in H4. simpl in H4. subst. eauto. simpl. eauto.
  intros ??????. unfold qone in H5. bdestruct (x =? length G). 2: inversion H5.
  rewrite indexr_skips in H4. subst x. rewrite indexr_head in H4. inversion H4. subst.
  2: { simpl; lia. } simpl. eauto. 
Qed.


(* soudness of purity: a syntactically pure term is semantically pure *)
Theorem soundness_of_purity: forall t1 G T1 pt1 a1,
    has_type G t1 T1 pt1 false a1 false -> (* fr1 = false and e1 = false: syntactic purity! *)    
    contextual_purity G t1 T1 a1. 
Proof.
  intros. intros ?????????????.
  eapply hast_fv in H as H''.
  eapply fundamental in H as H'.
  eapply congr in H0 as H0'.
  
  unfold tlet.
  remember (splice_ctx C (length G) 1) as C'.
  remember (splice_tm t1 (length G) (length Gh - length G)) as t1'.
  remember (plug C' (tvar (length G))) as t2.
  replace (plug C t1') with (subst_tm t2 (length G) t1).
  
  eapply beta_equivalence.
  eapply auxA in H0; eauto. rewrite splice_miss in H0; eauto. 
  subst pt1. eauto. eauto. eauto. eapply hast_closed in H. subst pt1. eauto.
  eapply auxB; eauto. 
Qed.