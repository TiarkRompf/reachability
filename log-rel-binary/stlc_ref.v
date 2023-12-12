(* Full safety for STLC *)

(* based on stlc.v *)

(* 

Simply-typed lambda calculus, combined proof of termination and type 
soundness (using logical relations).

This version adds immutable references. The proof relies on a 
monotonically growing store. Since values in the store don't change, 
a separate store typing is not necessary (adding an assignment 
operator would require store typings).

There are no reachability qualifiers yet.

*)


Require Export Arith.EqNat.
Require Export Arith.Le.
Require Import Coq.Lists.List.
Require Import Psatz.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.Peano_dec.
Import ListNotations.

Require Import env.
Require Import tactics.

Module STLC.

Definition id := nat.  

Inductive ty : Type :=
  | TBool  : ty
  | TRef   : ty -> ty    
  | TFun   : ty -> ty -> ty
.

Inductive tm : Type :=
  | ttrue : tm
  | tfalse : tm
  | tvar : id -> tm
  | tref : tm -> tm
  | tget : tm -> tm
  (*| tput : tm -> tm -> tm  *)
  | tapp : tm -> tm -> tm (* f(x) *)
  | tabs : tm -> tm (* \f x.y *)
.

Inductive vl : Type :=
  | vbool : bool -> vl
  | vref  : id -> vl
  | vabs  : list vl -> tm -> vl
.

Definition venv := list vl.
Definition tenv := list ty.
Definition stor := list vl.
Definition stpe := list (vl -> Type).

#[global] Hint Unfold venv.
#[global] Hint Unfold tenv.
#[global] Hint Unfold stor.
#[global] Hint Unfold stpe.

Inductive has_type : tenv -> tm -> ty -> Prop :=
| t_true: forall env,
    has_type env ttrue TBool
| t_false: forall env,
    has_type env tfalse TBool
| t_var: forall x env T1,
    indexr x env = Some T1 ->
    has_type env (tvar x) T1
| t_ref: forall x env T1,
    has_type env x T1 ->
    has_type env (tref x) (TRef T1)
| t_app: forall env f x T1 T2,
    has_type env f (TFun T1 T2) ->
    has_type env x T1 ->
    has_type env (tapp f x) T2
| t_abs: forall env y T1 T2,
    has_type (T1::env) y T2 -> 
    has_type env (tabs y) (TFun T1 T2)
.


(*
None             means timeout
Some None        means stuck
Some (Some v))   means result v
*)

Fixpoint teval(n: nat)(M:stor)(env: venv)(t: tm){struct n}: stor * option (option vl) :=
  match n with
    | 0 => (M, None)
    | S n =>
      match t with
        | ttrue      => (M, Some (Some (vbool true)))
        | tfalse     => (M, Some (Some (vbool false)))
        | tvar x     => (M, Some (indexr x env))
        | tref ex    =>
          match teval n M env ex with
            | (M', None)           => (M', None)
            | (M', Some None)      => (M', Some None)
            | (M', Some (Some vx)) => (vx::M', Some (Some (vref (length M'))))
          end
        | tget ex    =>
          match teval n M env ex with
            | (M, None) => (M, None)
            | (M, Some None) => (M, Some None)
            | (M, Some (Some vx)) => (M, Some (Some vx))
          end
        | tabs y     => (M, Some (Some (vabs env y)))
        | tapp ef ex =>
          match teval n M env ef with
            | (M', None) => (M', None)
            | (M', Some None) => (M', Some None)
            | (M', Some (Some (vbool _))) => (M', Some None)
            | (M', Some (Some (vref _))) => (M', Some None)
            | (M', Some (Some (vabs env2 ey))) =>
              match teval n M' env ex with
                | (M'', None) => (M'', None)
                | (M'', Some None) => (M'', Some None)
                | (M'', Some (Some vx)) =>
                  teval n M'' (vx::env2) ey
              end
          end
      end
  end.


Definition tevaln M env e M' v :=
  exists nm,
  forall n,
    n > nm ->
    teval n M env e = (M', Some (Some v)).


Fixpoint val_type M1 M2 v1 v2 T : Prop :=
  match v1, v2, T with
  | vbool b1, vbool b2, TBool => 
      b1 = b2
  | vref l1, vref l2, TRef T =>
      exists vx1 vx2,
      indexr l1 M1 = Some vx1 /\
      indexr l2 M2 = Some vx2 /\
      val_type M1 M2 vx1 vx2 T
  | vabs G1 ty1, vabs G2 ty2, TFun T1 T2 => 
      (forall M1' M2' vx1 vx2,
            val_type (M1'++M1) (M2'++M2) vx1 vx2 T1
          -> 
            exists M1'' M2'' vy1 vy2,
              tevaln (M1'++M1) (vx1::G1) ty1 (M1''++M1'++M1) vy1 /\
              tevaln (M2'++M2) (vx2::G2) ty2 (M2''++M2'++M2) vy2 /\
              val_type (M1''++M1'++M1) (M2''++M2'++M2) vy1 vy2 T2) 
  | _,_,_ =>
      False
end.

Definition exp_type M1 M2 H1 H2 t1 t2 M1' M2' T :=
  exists v1 v2,
    tevaln M1 H1 t1 (M1'++M1) v1 /\
    tevaln M2 H2 t2 (M2'++M2) v2 /\
    val_type (M1'++M1) (M2'++M2) v1 v2 T.

Definition env_type M1 M2 H1 H2 G :=
  length H1 = length G /\
  length H2 = length G /\
    forall x T,
      indexr x G = Some T ->
      exists v1 v2 : vl,
        indexr x H1 = Some v1 /\
        indexr x H2 = Some v2 /\
        val_type M1 M2 v1 v2 T.


Hint Constructors ty.
Hint Constructors tm.
Hint Constructors vl.


Hint Constructors has_type.

Hint Constructors option.
Hint Constructors list.

Import Coq.Arith.PeanoNat.

Lemma valt_store_extend: forall T M1' M1 M2' M2 v1 v2,
  val_type M1 M2 v1 v2 T ->
  val_type (M1'++M1) (M2'++M2) v1 v2 T.
Proof.
  intros T. induction T; intros; simpl; destruct v1; destruct v2; simpl in H; eauto.
  - (* Ref*)
    destruct H as [v1  [v2 [HI1 [HI2 HV]]]].
    apply indexr_extend with (H' := M1') in HI1; intuition.
    apply indexr_extend with (H' := M2') in HI2; intuition.
    eexists. eauto.
  - (* Abs *)
    intros. specialize (H (M1'0++M1') (M2'0++M2')).
    assert ((M1'0 ++ M1') ++ M1 = M1'0 ++ M1' ++ M1). rewrite app_assoc. eauto.
    assert ((M2'0 ++ M2') ++ M2 = M2'0 ++ M2' ++ M2). rewrite app_assoc. eauto.
    rewrite H1 in H. rewrite H2 in H.
    eapply H. eauto.
Qed.

Lemma valt_store_extend1: forall T M1 M2 v1 v2,
  val_type M1 M2 v1 v2 T ->
  val_type (v1 :: M1) (v2 :: M2) v1 v2 T.
Proof.
  intros.
  replace (v1 :: M1) with ([v1] ++ M1); auto.
  replace (v2 :: M2) with ([v2] ++ M2); auto.
  eapply valt_store_extend. auto.
Qed.

Lemma envt_extend: forall M1 M2 H1 H2 G v1 v2 T,
    env_type M1 M2 H1 H2 G ->
    val_type M1 M2 v1 v2 T ->
    env_type M1 M2 (v1::H1)(v2::H2) (T::G).
Proof.
  intros. destruct H as [L1 [L2 W]].
  
  repeat split. simpl. eauto. simpl. auto.
  intros. 
  bdestruct (x =? (length G)); intuition; subst.
  - (* last *)
    rewrite indexr_head in H. 
    exists v1. exists v2.
    repeat split. 
    rewrite <-L1. rewrite indexr_head. eauto.
    rewrite <-L2. rewrite indexr_head. eauto.
    congruence.
   - (* not last *)
    rewrite indexr_skip in H; try lia.
    destruct (W x T0) as [v3 [v4 IEXP]].  auto.
    exists v3, v4.
    repeat (rewrite indexr_skip; try lia).
    eauto.
Qed.

Lemma envt_store_extend: forall M1 M2 M1' M2' H1 H2 G,
    env_type M1 M2 H1 H2 G ->
    env_type (M1'++M1) (M2'++M2) H1 H2 G.
Proof.
  intros. destruct H as [L1 [L2 W]].
  repeat split; auto.
  intros. simpl in *. 
  specialize (W x T H); intuition.
  destruct W as [v1 [v2 [IX VX]]]; intuition.
  exists v1. exists v2. intuition. eapply valt_store_extend; eauto.
Qed.

(* compatibility lemmas *)

Lemma bi_vtrue: forall M1 M2 H1 H2,
  exp_type M1 M2 H1 H2 ttrue ttrue [] []  TBool.
Proof.   
  intros. exists (vbool true). exists (vbool true). repeat split.  
  exists 0. intros. destruct n. lia. simpl. eauto.
  exists 0. intros. destruct n. lia. simpl. eauto.
Qed.

Lemma bi_vfalse: forall M1 M2 H1 H2,
  exp_type M1 M2 H1 H2 tfalse tfalse [] []  TBool.
Proof.   
  intros. exists (vbool false). exists (vbool false). repeat split.  
  exists 0. intros. destruct n. lia. simpl. eauto.
  exists 0. intros. destruct n. lia. simpl. eauto.
Qed.

Lemma bi_tref: forall e1 e2 M1 M2 M1' M2' H1 H2 T,
  exp_type M1 M2 H1 H2 e1 e2 M1' M2' T ->
  exists M1'' M2'',
   exp_type M1 M2 H1 H2 (tref e1) (tref e2) M1'' M2'' (TRef T).
Proof.   
  intros. 
  destruct H as [v1 [v2 [IEX1 [IEX2 HVALX]]]].
  exists (v1 :: M1'). exists (v2::M2').
  exists (vref (length (M1'++M1))).
  exists (vref (length (M2'++M2))).
  repeat split. 

  (* 1st term *)
  destruct IEX1 as [n1 IEX1].
  exists (S n1). intros. destruct n. lia. simpl. rewrite IEX1. eauto. lia.

  (* 2nd term *)
  destruct IEX2 as [n2 IEX2].
  exists (S n2). intros. destruct n. lia. simpl. rewrite IEX2. eauto. lia.

  simpl.
  bdestruct (length (M1' ++ M1) =? length (M1' ++ M1)); 
  bdestruct (length (M2' ++ M2) =? length (M2' ++ M2)); intuition.
  exists v1. exists v2; intuition.
  eapply valt_store_extend1; auto. 
Qed.



Lemma bi_tabs: forall H1 H2 M1 M2 e1 e2 T1 T2
  (EXP:  forall M1' M2' vx1 vx2,
      val_type (M1'++M1) (M2'++M2) vx1 vx2 T1 ->
      exists M1''  M2'',
        exp_type (M1'++M1) (M2'++M2) (vx1:: H1) (vx2:: H2) e1 e2 M1'' M2'' T2),   
  exp_type M1 M2 H1 H2 (tabs e1) (tabs e2) [] [] (TFun T1 T2).
Proof. 
  intros. 
  exists (vabs H1 e1). exists (vabs H2 e2).
  repeat split.
  (* first abs *)
  exists 0. intros. destruct n. lia. simpl. auto.
  (* second abs *)
  exists 0. intros. destruct n. lia. simpl. auto.
  simpl in *. eauto.
Qed.

Lemma bi_app: forall M1 M2 M1' M2' M1'' M2'' H1 H2 e1 e2 ex1 ex2 T1 T2,
  exp_type M1 M2 H1 H2 e1 e2 M1' M2' (TFun T1 T2) ->
  exp_type (M1'++M1) (M2'++M2) H1 H2 ex1 ex2 M1'' M2'' T1  ->
  exists M1''' M2''',
  exp_type M1 M2 H1 H2 (tapp e1 ex1) (tapp e2 ex2) M1''' M2''' T2.
Proof. 
  intros. 
  
  destruct H as [vf1 [vf2 [IEF1 [IEF2 HVALF]]]].
  destruct H0 as [vx1 [vx2 [IEX1 [IEX2 HVALX]]]].
  
  destruct vf1; destruct vf2; try solve [inversion HVAF]; simpl in HVALF; intuition.
  specialize (HVALF M1'' M2'' vx1 vx2); intuition.
  
  destruct H as [M1'''[M2'''[r1 [r2 [IAPP1 [IAPP2 IVALY]]]]]]. 
  exists (M1'''++M1''++M1'). exists (M2'''++M2''++M2'). exists r1. exists r2.

  repeat split; auto.
  (* 1st function *)
  destruct IEF1 as [n1 IEF1].
  destruct IEX1 as [n2 IEX1].
  destruct IAPP1 as [n3 IAPP1].
  exists (S (n1+n2+n3)). 
  (* - forall greater fuel *)
  intros. destruct n. lia.
  (* - result computes *)
  simpl. rewrite IEF1. rewrite IEX1. rewrite IAPP1. 
  replace ((M1''' ++  M1'' ++ M1') ++ M1)
    with  (M1''' ++  M1'' ++ M1' ++ M1). auto.
  repeat rewrite app_assoc; auto.
  lia. lia. lia.

  (* 2nd function *)
  destruct IEF2 as [n1 IEF2].
  destruct IEX2 as [n2 IEX2].
  destruct IAPP2 as [n3 IAPP2].
  exists (S (n1+n2+n3)). 
  (* - forall greater fuel *)
  intros. destruct n. lia.
  (* - result computes *)
  simpl. rewrite IEF2. rewrite IEX2. rewrite IAPP2. 
  replace ((M2''' ++  M2'' ++ M2') ++ M2)
    with  (M2''' ++  M2'' ++ M2' ++ M2). auto.
  repeat rewrite app_assoc; auto.
  lia. lia. lia.
  replace ((M1''' ++  M1'' ++ M1') ++ M1)
    with  (M1''' ++  M1'' ++ M1' ++ M1). 
  replace ((M2''' ++  M2'' ++ M2') ++ M2)
    with  (M2''' ++  M2'' ++ M2' ++ M2). auto.
  1,2: repeat rewrite app_assoc; auto.    
Qed.

Lemma bi_var: forall G M1 M2 H1 H2 x T1
  (WFE: env_type M1 M2 H1 H2 G),
  indexr x G = Some T1 ->
  exp_type M1 M2 H1 H2 (tvar x) (tvar x) [] [] T1.
Proof.
  intros. 
  eapply WFE in H. destruct H as [v1 [v2 [IX1 [IX2 VT]]]].
  exists v1, v2. repeat split.
  exists 0. intros. destruct n. lia. simpl. congruence.
  exists 0. intros. destruct n. lia. simpl. congruence.
  eauto.
Qed.


(* if well-typed, then result is an actual value (not stuck and not a timeout),
   for large enough n *)

Theorem fundamental_property : forall e G T,
  has_type G e T -> 
  forall M1 M2 H1 H2, env_type M1 M2 H1 H2 G ->
  exists M1'  M2',
  exp_type M1 M2 H1 H2 e e M1' M2' T.

Proof.
  intros ? ? ? W. 
  induction W; intros ? ? ? ? WFE.
  - (* Case "True". *)
    exists []. exists [].
    eapply bi_vtrue.
  - (* Case "False". *)
    exists []. exists [].
    eapply bi_vfalse.
  - (* Case "Var". *)
    exists []. exists [].
    eapply bi_var; eauto.
  - (* Case "Ref". *)
    specialize (IHW M1 M2 H1 H2); intuition.
    destruct H as [M1' [M2' IEX]].
    eapply bi_tref; eauto.
  - (* Case "App". *)
    specialize (IHW1 M1 M2 H1 H2); intuition.
    destruct H as [M1' [M2' IEF]].
    assert (env_type (M1'++M1) (M2'++M2) H1 H2  env) as WFE1. { eapply envt_store_extend. eauto. }
    specialize (IHW2 (M1'++M1) (M2'++M2) H1 H2); intuition.
    destruct H as [M1'' [M2'' IEX]].
    eapply bi_app. eauto. eauto. 
    
  - (* Case "Abs". *)
    exists []. exists[].
    eapply bi_tabs. intros. eapply IHW; eauto. eapply envt_extend; eauto.
    eapply envt_store_extend. auto.
Qed.

(* If we want to, we can package up the types a bit, and then we have an
   alternative version which I think should corresponds quite closely
   to what's in the paper: *)

Definition sem_type G e1 e2 T:=
  forall M1 M2 H1 H2,
    env_type M1 M2 H1 H2 G ->
    exists M1' M2',
    exp_type M1 M2 H1 H2 e1 e2 M1' M2' T.

Lemma bi_vtrue2: forall G,
  sem_type G ttrue ttrue TBool.
Proof.
  intros G M1 M2 H1 H2 WFE. 
  exists []. exists [].
  eapply bi_vtrue.
Qed.

Lemma bi_vfalse2: forall G,
  sem_type G tfalse tfalse TBool.
Proof.
  intros G M1 M2 H1 H2 WFE. 
  exists []. exists [].
  eapply bi_vfalse.
Qed.

Lemma bi_tref2: forall G T e1 e2,
  sem_type G e1 e2 T ->
  sem_type G (tref e1) (tref e2) (TRef T).
Proof.
  intros.
  intros M1 M2 H1 H2 WFE.
  unfold sem_type in H.
  specialize (H M1 M2 H1 H2 WFE) as [M1' [M2' IE]].
  eapply bi_tref; eauto.
Qed.

Lemma bi_tabs2: forall G e1 e2 T1 T2,
  sem_type (T1 :: G) e1 e2 T2 ->
  sem_type G (tabs e1) (tabs e2) (TFun T1 T2).
Proof. 
  intros. intros M1 M2 H1 H2 WFE.
  exists []. exists []. 
  eapply bi_tabs. intros.
  eapply H. eapply envt_extend; eauto.
  eapply envt_store_extend; eauto. 
Qed.

Lemma bi_app2: forall G e1 e2 ex1 ex2 T1 T2,
  sem_type G e1 e2 (TFun T1 T2) ->
  sem_type G ex1 ex2 T1  ->
  sem_type G (tapp e1 ex1) (tapp e2 ex2) T2.
Proof.
  intros. intros M1 M2 H1 H2 WFE.
  unfold sem_type in H.
  destruct (H M1 M2 H1 H2 WFE) as [M1' [M2' IEF]].
  assert (env_type (M1'++M1) (M2'++M2) H1 H2 G) as WFE1. { eapply envt_store_extend. eauto. }
  unfold sem_type in H0.
  destruct (H0 (M1'++M1) (M2'++M2) H1 H2 WFE1) as [M1'' [M2'' IEX]].
   
  eapply bi_app; eauto.
Qed.

Lemma bi_var2: forall G x T1,
  indexr x G = Some T1 ->
  sem_type G (tvar x) (tvar x) T1.
Proof.
  intros. intros M1 M2 H1 H2 WFE.
  exists []. exists [].
  eapply bi_var; eauto.
Qed.    

Theorem fundamental_property2 : forall e G T,
  has_type G e T -> 
  sem_type G e e T.
Proof.
  intros. induction H. 
  - (* Case "True". *)
    eapply bi_vtrue2.
  - (* Case "False". *)
    eapply bi_vfalse2.
  - (* Case "Var". *)
    eapply bi_var2; eauto.
  - (* Case "tref" *)
    eapply bi_tref2; eauto.
  - (* Case "App". *)
    eapply bi_app2; eauto.
  - (* Case "Abs". *)
    eapply bi_tabs2; eauto.
Qed.

(* Define typed contexts and prove that the binary logical
   relation implies contextual equivalence (congruency wrt
   putting expressions in context *)

(* Q: Do we need to prove a theorem that these are all
   possible contexts? Do we need to consider only one-hole
   contexts are also (fun x => tapp x x)? *)


Inductive ctx_type : (tm -> tm) -> tenv -> ty -> tenv -> ty -> Prop :=
| c_top: forall G T,
    ctx_type (fun x => x) G T G T
| c_ref: forall G T,
    ctx_type (fun x => tref x) G T G (TRef T)
| c_app1: forall e2 G T1 T2,
    has_type G e2 T1 ->
    ctx_type (fun x => tapp x e2) G (TFun T1 T2) G T2
| c_app2: forall e1 G T1 T2,
    has_type G e1 (TFun T1 T2) ->
    ctx_type (fun x => tapp e1 x) G T1 G T2
| c_abs: forall G T1 T2,
    ctx_type (fun x => tabs x) (T1::G) T2 G (TFun T1 T2).

Theorem congr:
  forall C G1 T1 G2 T2,
    ctx_type C G1 T1 G2 T2 ->
  forall e e',
    sem_type G1 e e' T1 ->
    sem_type G2 (C e) (C e') T2.
Proof.
  intros ? ? ? ? ? CX.
  induction CX; intros.
  - eauto.
  - eapply bi_tref2. eauto.
  - eapply bi_app2. eauto. eapply fundamental_property2. eauto.
  - eapply bi_app2. eapply fundamental_property2. eauto. eauto.
  - eapply bi_tabs2. eauto.
Qed.


End STLC.
