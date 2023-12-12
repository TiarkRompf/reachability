(* Full safety for STLC *)

(*

Simply-typed lambda calculus, combined proof of termination and type
soundness (using logical relations).

*)

Require Export Arith.EqNat.
Require Export Arith.Le.
Require Import Coq.Lists.List.
Require Import Psatz.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Arith.PeanoNat.

Import ListNotations.


Require Import tactics.
Require Import env.


Module STLC.

Definition id := nat.

Inductive ty : Type :=
  | TBool  : ty
  | TFun   : ty -> ty -> ty
.

Inductive tm : Type :=
  | ttrue : tm
  | tfalse : tm
  | tvar : id -> tm
  | tapp : tm -> tm -> tm (* f(x) *)
  | tabs : tm -> tm (* \f x.y *)
.

Inductive vl : Type :=
| vbool : bool -> vl
| vabs  : list vl -> tm -> vl
.

Definition venv := list vl.
Definition tenv := list ty.

#[global] Hint Unfold venv.
#[global] Hint Unfold tenv.


Inductive has_type : tenv -> tm -> ty -> Prop :=
| t_true: forall env,
           has_type env ttrue TBool
| t_false: forall env,
           has_type env tfalse TBool
| t_var: forall x env T1,
           indexr x env = Some T1 ->
           has_type env (tvar x) T1
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

Fixpoint teval(n: nat)(env: venv)(t: tm){struct n}: option (option vl) :=
  match n with
    | 0 => None
    | S n =>
      match t with
        | ttrue      => Some (Some (vbool true))
        | tfalse     => Some (Some (vbool false))
        | tvar x     => Some (indexr x env)
        | tabs y     => Some (Some (vabs env y))
        | tapp ef ex   =>
          match teval n env ef with
            | None => None
            | Some None => Some None
            | Some (Some (vbool _)) => Some None
            | Some (Some (vabs env2 ey)) =>
              match teval n env ex with
                | None => None
                | Some None => Some None
                | Some (Some vx) =>
                  teval n (vx::env2) ey
              end
          end
      end
  end.


Definition tevaln env e v := exists nm, forall n, n > nm -> teval n env e = Some (Some v).


(* need to use Fixpoint because of positivity restriction *)
Fixpoint val_type v1 v2 T : Prop := match v1, v2, T with
| vbool b1, vbool b2, TBool => b1 = b2
| vabs G1 ty1, vabs G2 ty2, TFun T1 T2 => 
  (forall vx1 vx2, 
     val_type vx1 vx2 T1 ->  
     exists vy1 vy2, 
       tevaln (vx1::G1) ty1 vy1 /\
       tevaln (vx2::G2) ty2 vy2 /\
       val_type vy1 vy2 T2) 
| _,_,_ => False
end.

(* terms  *)
Definition exp_type H1 H2 t1 t2 T :=
  exists v1 v2,
    tevaln H1 t1 v1 /\  
    tevaln H2 t2 v2 /\ 
    val_type v1 v2 T.

(* context  *)
Definition env_type H1 H2 G := 
  length H1 = length G /\
  length H2 = length G /\
  forall x T,
    indexr x G = Some T ->
    exists v1 v2,
      indexr x H1 = Some v1 /\
      indexr x H2 = Some v2 /\
      val_type v1 v2 T.      


Hint Constructors ty.
Hint Constructors tm.
Hint Constructors vl.


Hint Constructors has_type.
(* Hint Constructors val_type. *)

Hint Constructors option.
Hint Constructors list.



Fixpoint splice_tm (t: tm)(i: nat) (n:nat) : tm := 
  match t with 
  | ttrue         => ttrue
  | tfalse        => tfalse
(*  | tvar (varB x) => tvar (varB x) *)
  | tvar x        => tvar (if x <? i then x else x + n)
  | tapp t1 t2    => tapp (splice_tm t1 i n) (splice_tm t2 i n)
  | tabs t        => tabs (splice_tm t i n)
end.

Fixpoint subst_tm (t: tm)(i: nat) (u:tm) : tm := 
  match t with 
  | ttrue         => ttrue
  | tfalse        => tfalse
(*  | tvar (varB x) => tvar (varB x) *)
  | tvar x => if i =? x then u else if i <?  x then (tvar (pred x)) else (tvar x)   
  | tapp t1 t2    => tapp (subst_tm t1 i u) (subst_tm t2 i u)
  | tabs t        => tabs (subst_tm t i (splice_tm u i 1)) 
end.

(*

Substitution needs to use splice internally to avoid conflicts. Consider:

  G = [0, 1, 2]

  e2 = ( \x3: x1(x0) )

  e1 = ( \x3: x3+x2) )

  subst e2 [x1 -> e1]

  ( \x3: (( \x3: x3+x2) ))(x0) )  <--- wrong! inner lambda can't be x3

  need this istead:

  ( \x3: (( \x4: x4+x2) ))(x0) )


*)

Lemma splice_acc: forall e1 a b c,
  splice_tm (splice_tm e1 a b) a c =
  splice_tm e1 a (c+b).
Proof. induction e1; intros; simpl; intuition.
  + bdestruct (i <? a); intuition.  
    bdestruct (i <? a); intuition.
    bdestruct (i + b <? a); intuition.   
  + specialize (IHe1_1 a b c). specialize (IHe1_2 a b c).
    rewrite IHe1_1. rewrite IHe1_2. auto.
  + specialize (IHe1 a b c).
    rewrite IHe1. auto. 
Qed.
  
Lemma splice_zero: forall e1 a,
  (splice_tm e1 a 0) = e1.
Proof. intros. induction e1; simpl; intuition.
  + bdestruct (i <? a); intuition.
  + rewrite IHe1_1. rewrite IHe1_2. auto.
  + rewrite IHe1. auto.
Qed.

Lemma indexr_splice': forall{X} x (G1 G3: list X) T ,
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
  indexr (if x <? length H2 then x else x + length HX) (H2' ++ HX ++ H2) =
  indexr x (H2' ++ H2).
Proof.
  intros.
  bdestruct (x <? length H2); intuition.
  repeat rewrite indexr_skips; auto. rewrite app_length. lia.
  bdestruct (x <? length (H2' ++ H2)).
  apply indexr_var_some in H0 as H0'.
  destruct H0' as [T H0']; intuition.
  rewrite H0'. apply indexr_splice'; auto.
  apply indexr_var_none in H0 as H0'. rewrite H0'.
  assert (x + length HX >= (length (H2' ++ HX ++ H2))). {
    repeat rewrite app_length in *. lia.
  }
  rewrite indexr_var_none. auto.
Qed.

Lemma indexr_splice1: forall{X} (H2' H2: list X) x y,
  indexr (if x <? length H2 then x else (S x)) (H2' ++ y :: H2) =
  indexr x (H2' ++ H2).
Proof.
  intros.
  specialize (indexr_splice H2' H2 [y] x); intuition.
  simpl in *. replace (x +1) with (S x) in H. auto. lia.
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
    
Lemma envt_extend: forall H1 H2 G T v1 v2,
    env_type H1 H2 G ->
    val_type v1 v2 T -> 
    env_type (v1::H1) (v2:: H2) (T::G).
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

Lemma envt_insert: forall H1 H1' H2 H2' G G' T v1 v2,
    env_type (H1'++H1) (H2'++H2) (G' ++  G) ->
    length H1 = length G ->
    length H2 = length G ->
    val_type v1 v2 T -> 
    env_type (H1' ++ v1::H1) (H2' ++ v2:: H2) (G' ++ T::G).
Proof.
  intros. destruct H as [L1  [L2 W]]; intros; subst.
  repeat rewrite app_length in *.
  repeat split.  
  1,2: repeat rewrite app_length; simpl; intuition.
  intros. bdestruct (x <? length G).
  + rewrite indexr_skips in H. rewrite indexr_skip in H.
    rewrite indexr_extend with (H' := G') in H. intuition.
    specialize (W x T0 H6 ); intuition.
    destruct W as [v1' [v2' [IV1 [IV2  IVAL]]]].
    exists v1', v2'.  repeat split; auto.
    1,2: rewrite <-  indexr_insert_lt;  auto;  lia.
    lia.  simpl. lia.
  + bdestruct (x =? length G);  intuition.  
    exists v1, v2. repeat split.
    rewrite <- H0 in  H6. rewrite indexr_skips. subst.  rewrite indexr_head. auto.  simpl. lia.
    rewrite <- H3 in H6. rewrite indexr_skips. subst.  rewrite indexr_head. auto.  simpl. lia.
    rewrite indexr_skips in H.  subst. rewrite indexr_head in H. inversion H. subst. auto.
    simpl. lia.
    apply indexr_shift in H.
    specialize (W (Init.Nat.pred x) T0 H).
    destruct W as [v1' [v2'[ IV1 [IV2 IVAL]]]].
    exists v1', v2'. repeat split.
    rewrite <- H0 in H5.
    erewrite indexr_insert_ge in IV1. 
    assert ((S (Init.Nat.pred x)) = x). lia.
    rewrite H7 in IV1. eapply IV1. lia.
    rewrite <- H3 in H5.
    erewrite indexr_insert_ge in IV2. 
    assert ((S (Init.Nat.pred x)) = x). lia.
    rewrite H7 in IV2. eapply IV2. lia.
    auto. lia.
Qed.    
    
  
(* compatibility lemmas *)

Lemma bi_vtrue: forall  H1 H2,
  exp_type H1 H2 ttrue ttrue TBool.
Proof.   
  intros. exists (vbool true). exists (vbool true). repeat split.  
  exists 0. intros. destruct n. lia. simpl. eauto.
  exists 0. intros. destruct n. lia. simpl. eauto.
Qed.

Lemma bi_vfalse: forall  H1 H2,
  exp_type H1 H2 tfalse tfalse TBool.
Proof.   
  intros. exists (vbool false). exists (vbool false). repeat split.
  exists 0. intros. destruct n. lia. simpl. eauto.
  exists 0. intros. destruct n. lia. simpl. eauto.
Qed.

Lemma bi_tabs: forall H1 H2 e1 e2 T1 T2
  (EXP:  forall vx1 vx2,
      val_type vx1 vx2 T1 ->
      exp_type (vx1:: H1) (vx2:: H2) e1 e2 T2),   
  exp_type H1 H2 (tabs e1) (tabs e2) (TFun T1 T2).
Proof. 
  intros. 
  exists (vabs H1 e1). exists (vabs H2 e2).
  repeat split.
  (* first abs *)
  exists 0. intros. destruct n. lia. simpl. auto.
  (* second abs *)
  exists 0. intros. destruct n. lia. simpl. auto.
  simpl. eauto.
Qed.

Lemma bi_app: forall H1 H2 e1 e2 ex1 ex2 T1 T2,
  exp_type H1 H2 e1 e2 (TFun T1 T2) ->
  exp_type H1 H2 ex1 ex2 T1  ->
  exp_type H1 H2 (tapp e1 ex1) (tapp e2 ex2) T2.
Proof.
  intros. 
  
  destruct H as [vf1 [vf2 [IEF1 [IEF2 HVALF]]]].
  destruct H0 as [vx1 [vx2 [IEX1 [IEX2 HVALX]]]].
  
  destruct vf1; destruct vf2; try solve [inversion HVAF]; simpl in HVALF; intuition.
  specialize (HVALF vx1 vx2); intuition.
  destruct H as [r1 [r2 [IAPP1 [IAPP2 IVALY]]]]. 
  exists r1. exists r2.

  repeat split; auto.
  (* 1st function *)
  destruct IEF1 as [n1 IEF1].
  destruct IEX1 as [n2 IEX1].
  destruct IAPP1 as [n3 IAPP1].
  exists (S (n1+n2+n3)). 
  (* - forall greater fuel *)
  intros. destruct n. lia.
  (* - result computes *)
  simpl. rewrite IEF1. rewrite IEX1. rewrite IAPP1. eauto.
  lia. lia. lia.

  (* 2nd function *)
  destruct IEF2 as [n1 IEF2].
  destruct IEX2 as [n2 IEX2].
  destruct IAPP2 as [n3 IAPP2].
  exists (S (n1+n2+n3)). 
  (* - forall greater fuel *)
  intros. destruct n. lia.
  (* - result computes *)
  simpl. rewrite IEF2. rewrite IEX2. rewrite IAPP2. eauto.
  lia. lia. lia.
Qed.

Lemma bi_var: forall G H1 H2 x T1
  (WFE: env_type H1 H2 G),
  indexr x G = Some T1 ->
  exp_type H1 H2 (tvar x) (tvar x) T1.
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
  forall H1 H2, env_type H1 H2 G ->
  exp_type H1 H2 e e T.

Proof.
  intros ? ? ? W. 
  induction W; intros ? ? WFE.
  - (* Case "True". *)
    eapply bi_vtrue.
  - (* Case "False". *)
    eapply bi_vfalse.
  - (* Case "Var". *)
    eapply bi_var; eauto.
  - (* Case "App". *)
    eapply bi_app. eapply IHW1; eauto. eapply IHW2; eauto.
  - (* Case "Abs". *)
    eapply bi_tabs. intros. eapply IHW; eauto. eapply envt_extend; eauto.
Qed.


(* If we want to, we can package up the types a bit, and then we have an
   alternative version which I think should corresponds quite closely
   to what's in the paper: *)

Definition sem_type G e1 e2 T:=
  forall H1 H2,
    env_type H1 H2 G ->
    exp_type H1 H2 e1 e2 T.

Lemma bi_vtrue2: forall G,
  sem_type G ttrue ttrue TBool.
Proof.
  intros G H1 H2 WFE. eapply bi_vtrue.
Qed.

Lemma bi_vfalse2: forall G,
  sem_type G tfalse tfalse TBool.
Proof.
  intros G H1 H2 WFE. eapply bi_vfalse.
Qed.

Lemma bi_tabs2: forall G e1 e2 T1 T2,
  sem_type (T1 :: G) e1 e2 T2 ->
  sem_type G (tabs e1) (tabs e2) (TFun T1 T2).
Proof. 
  intros. intros H1 H2 WFE. eapply bi_tabs. intros.
  eapply H. eapply envt_extend; eauto. 
Qed.

Lemma bi_app2: forall G e1 e2 ex1 ex2 T1 T2,
  sem_type G e1 e2 (TFun T1 T2) ->
  sem_type G ex1 ex2 T1  ->
  sem_type G (tapp e1 ex1) (tapp e2 ex2) T2.
Proof.
  intros. intros H1 H2 WFE.
  eapply bi_app; eauto. 
Qed.

Lemma bi_var2: forall G x T1,
  indexr x G = Some T1 ->
  sem_type G (tvar x) (tvar x) T1.
Proof.
  intros. intros H1 H2 WFE.
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
   contexts or also (fun x => tapp x x)? *)


Inductive ctx_type : (tm -> tm) -> tenv -> ty -> tenv -> ty -> Prop :=
| c_top: forall G T,
    ctx_type (fun x => x) G T G T
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
  - eapply bi_app2. eauto. eapply fundamental_property2. eauto.
  - eapply bi_app2. eapply fundamental_property2. eauto. eauto.
  - eapply bi_tabs2. eauto.
Qed.

Lemma adequacy: forall e e' T,
  sem_type [] e e' T ->
  (exists v, tevaln [] e v) <-> 
  (exists v', tevaln [] e' v').
Proof. 
  intros. 
  assert (env_type [] [] []) as WFE. { unfold env_type; intuition. inversion H0. }
  unfold sem_type in H. specialize (H [] [] WFE). 
  destruct H as [? [? [? [? ?]]]].
  split. 
  + intros. exists x0. intuition.
  + intros. exists x. intuition.
Qed.

Definition context_equiv G t1 t2 T1 :=
  has_type G t1 T1 ->
  has_type G t2 T1 ->
  forall C,
    ctx_type C G T1 [] TBool ->
    (exists v1, tevaln [] (C t1) v1) <->
    (exists v2, tevaln [] (C t2) v2).


(* soundness of binary logical relations *)
Theorem soundess: forall G t1 t2 T,
  has_type G t1 T ->
  has_type G t2 T ->
    (sem_type G t1 t2 T -> context_equiv G t1 t2 T).    
Proof. 
  intros. unfold context_equiv. intros.
  assert (sem_type [] (C t1)(C t2) TBool). {
   specialize (congr C G  T [] TBool); intuition.
   }

  eapply adequacy; eauto. 
Qed.   
  

Lemma has_type_weaken: forall G3 G1 t T,
  has_type (G3++G1) t T -> forall G2,
  has_type (G3 ++ G2 ++ G1) (splice_tm t (length G1)(length G2)) T.
Proof.
  intros G3 G1 t T W. remember (G3 ++ G1) as GG'. 
  generalize dependent G3. generalize dependent G1.
  induction W; intros; simpl; subst.
  + constructor.
  + constructor.
  + apply indexr_var_some' in H as H''.
    bdestruct (x <? length G1); intuition. 
    rewrite indexr_skips in H.
    constructor. eapply indexr_extend with (H' := G3 ++ G2) in H; intuition.
    rewrite app_assoc. auto. auto.
    constructor. eapply indexr_splice'; eauto.
  + econstructor. eapply IHW1; auto.
    eapply IHW2; auto.
  + econstructor. specialize (IHW G1 (T1:: G3)); intuition.
    eapply H.
Qed. 





(* -------------------------------------- *)

(* What if we make weakening explicit? *)



Lemma bi_var_splice: forall G H1 H2 H2' HX x T1
  (WFE: env_type H1 (H2'++H2) G),
  indexr x G = Some T1 ->
  exp_type H1 (H2'++HX++H2) (tvar x) (splice_tm (tvar x) (length H2) (length HX)) T1.
Proof.
  intros. 
  destruct WFE as [? [? W]].
  eapply W in H. destruct H as [v1 [v2 [IX1 [IX2 VT]]]].
  exists v1, v2. intuition.
  exists 0. intros. destruct n. lia. simpl. rewrite IX1. eauto.
  exists 0. intros. destruct n. lia. simpl. rewrite indexr_splice. rewrite IX2. eauto.
Qed.

Lemma bi_var_splice1: forall G H1' H1 H2  HX x T1
  (WFE: env_type (H1' ++H1) H2 G),
  indexr x G = Some T1 ->
  exp_type (H1' ++ HX ++ H1) H2 (splice_tm (tvar x) (length H1) (length HX)) (tvar x) T1.
Proof.
  intros. 
  destruct WFE as [? [? W]].
  eapply W in H. destruct H as [v1 [v2 [IX1 [IX2 VT]]]].
  exists v1, v2. intuition.
  exists 0. intros. destruct n. lia. simpl. rewrite indexr_splice. rewrite IX1. eauto.
  apply indexr_var_some' in IX1. auto.
  exists 0. intros. destruct n. lia. simpl. rewrite IX2. eauto.
Qed.


Lemma st_weaken: forall e1 T1 G
  (W: has_type G e1 T1),
  forall H1 H2 H2' HX,
    env_type H1 (H2'++H2) G ->
    exp_type H1 (H2'++HX++H2) e1 (splice_tm e1 (length H2) (length HX)) T1.
Proof.
  intros ? ? ? W. induction W; intros.
  - eapply bi_vtrue.
  - eapply bi_vfalse.
  - eapply bi_var_splice; eauto.
  - eapply bi_app; eauto.
  - eapply bi_tabs. intros.
    eapply envt_extend in H; eauto.
    replace (vx2 :: H2' ++ H2) with ((vx2 :: H2') ++ H2) in H. 2: simpl; eauto.
    eapply IHW in H; eauto.
Qed.


(* Need to tweak the signature? To use st_subst from the main beta lemma,
   we need weakning results of the form:

   exists v1, tevaln e1 v1 ->
   forall HX,
   exists v2, tevaln (splice .. e1) v2 /\ val_type v1 v2 T
*)

Lemma tevaln_unique: forall H1 e1 v1 v1',
    tevaln H1 e1 v1 ->
    tevaln H1 e1 v1' ->
    v1 = v1'.
Proof.
  intros.
  destruct H as [n1 ?].
  destruct H0 as [n2 ?].
  assert (1+n1+n2 > n1) as A1. lia.
  assert (1+n1+n2 > n2) as A2. lia.
  specialize (H _ A1).
  specialize (H0 _ A2).
  congruence.
Qed.

Lemma st_weaken1: forall e1 T1 G
  (W: has_type G e1 T1),
  forall H1 H2 H2',
    env_type H1 (H2'++H2) G ->
    exists v1, tevaln H1 e1 v1 /\ forall HX, exists v2, tevaln (H2'++HX++H2) (splice_tm e1 (length H2) (length HX)) v2 /\ val_type v1 v2 T1.
Proof.
  intros.
  assert (exp_type H1 (H2'++H2) e1 e1 T1). eapply fundamental_property; eauto.
  destruct H0 as [v1 [v2 [? ?]]].
  exists v1. split. eapply H0.
  intros. 
  eapply st_weaken in W; eauto.
  destruct W as [v1' [v2' [? [? ?]]]].
  exists v2'. split. eauto.
  assert (v1 = v1'). eapply tevaln_unique; eauto.
  subst v1. eauto.
Qed.

Lemma bi_var_subst: forall G G' H1 H1' H2' H2 x v1 v2 e1 T1 T0
  (WFE: env_type (H1'++H1) (H2'++H2) (G' ++ G)),
  indexr x (G' ++ T1 :: G) = Some T0 ->
  length H1 = length G ->
  length H2 = length G ->
  tevaln H1 e1 v1 ->
  tevaln (H2'++H2) (splice_tm e1 (length H2) (length H2')) v2 ->
  val_type v1 v2 T1 ->
  exp_type (H1'++v1::H1) (H2'++H2) (tvar x) (subst_tm (tvar x) (length H2) (splice_tm e1 (length H2) (length H2'))) T0.
Proof.
  intros.
  bdestruct (x =? length G).
  - subst x. exists v1, v2. 
    assert (T0 = T1).
    rewrite indexr_skips in H.  rewrite indexr_head in H. inversion H. auto. simpl. lia.
    intuition.
    exists 0. intros. destruct n. lia. simpl.
    rewrite <- H0. 
    rewrite indexr_skips. rewrite indexr_head. auto. simpl. lia.
    simpl. bdestruct (length H2 =? length G). eauto. lia. subst T0. eauto. 
  - assert (env_type (H1' ++v1::H1) (H2'++ v2::H2) (G' ++ T1 :: G)) as WFE'. {
      eapply envt_insert; eauto.
    }
    simpl. 
    bdestruct (length H2 <? x).
    
    eapply WFE' in H.
     
    destruct H as [v3 [v4 [IX3 [IX4 VT]]]].
    exists v3, v4. repeat split.
    exists 0. intros. destruct n. lia. simpl. congruence.
  
    destruct H4 as [n1 H4].
    assert (S n1 > n1). { lia. }
    specialize (H4 (S n1)). intuition.
    exists 0. intros. destruct n. simpl. lia.
    bdestruct (length H2 =? x); intuition.
    simpl. eapply indexr_shift in IX4.
    rewrite IX4. auto. auto. auto.

    eapply WFE' in H. destruct H as [v3 [v4 [IX3 [IX4 VT]]]].
    exists v3, v4. repeat split.
    exists 0. intros. destruct n. lia. simpl. congruence.
    rewrite indexr_skips in IX3. 2: simpl; lia.
    rewrite indexr_skip in IX3. 2: rewrite  H0. 2: auto.
    rewrite indexr_extend with (H' := H2') in IX3. intuition.
    exists 0. intros. destruct n. lia.
    bdestruct (length H2 =? x); intuition.
    replace (length H1) with (length H2) in H8. 
    simpl.    
    assert (indexr (if x <? length H2 then x else x + 1) (H2' ++ [v2] ++ H2) =
            indexr x (H2' ++ H2)). {
            eapply indexr_splice with (HX := [v2]).            
    }
    bdestruct (x <? length H2); intuition.
    replace (H2' ++ [v2] ++ H2) with (H2' ++ v2 :: H2) in H12; auto.
    rewrite H12 in IX4. rewrite IX4. auto. congruence.
    eauto.
Qed.



Lemma st_subst : forall e2 T2 G0
                        (W: has_type G0 e2 T2),
  forall G' G T1, G0 = G'++T1::G ->
  forall H1 H1' H2 H2' e1 v1,
    env_type (H1'++H1) (H2'++H2) (G'++G) ->
    length H1 = length G ->
    length H2 = length G ->
    tevaln H1 e1 v1 ->
    (forall H2', exists v2, tevaln (H2'++H2) (splice_tm e1 (length H2) (length H2')) v2 /\ val_type v1 v2 T1) -> (* via st_weaken *)
    exp_type (H1'++v1::H1) (H2'++H2) e2 (subst_tm e2 (length H2) (splice_tm e1 (length H2) (length H2'))) T2.
Proof.
  intros ? ? ? W. induction W; simpl; intros.
  - eapply bi_vtrue.
  - eapply bi_vfalse.
  - destruct (H7 H2') as [v2 [? ?]]. subst env.
    eapply bi_var_subst; eauto. 
  - eapply bi_app; eauto.
  - eapply bi_tabs. intros. subst env.
    eapply envt_extend in H0; eauto.
    replace (vx1 :: H1' ++ H1) with ((vx1 :: H1') ++ H1) in H0. 2: simpl; eauto.
    replace (vx2 :: H2' ++ H2) with ((vx2 :: H2') ++ H2) in H0. 2: simpl; eauto.
    rewrite splice_acc. 
    eapply IHW with (H1':=(vx1::H1')) (H2':=(vx2::H2')).
    replace (T1 :: G' ++ T0 :: G) with ((T1 :: G') ++ T0 :: G). 2: simpl; eauto.
    eauto. eauto. eauto. eauto. eauto. eauto. 
Qed.

Lemma st_subst1 : forall e1 e2 G T1 T2 H1 H2 v1,
    has_type (T1::G) e2 T2 ->
    env_type H1 H2 G ->
    length H1 = length G ->
    length H2 = length G ->
    tevaln H1 e1 v1 ->
    (forall H2', exists v2, tevaln (H2'++H2) (splice_tm e1 (length H2) (length H2')) v2 /\ val_type v1 v2 T1) -> (* via st_weaken *)
    exp_type (v1::H1) H2 e2 (subst_tm e2 (length H2) (splice_tm e1 (length H2) 0)) T2.
Proof.
  intros. eapply st_subst with (G':=[]) (H1':=[]) (H2':=[]); eauto. eauto. 
Qed.


Lemma beta_equivalence: forall e1 e2 G T1 T2,
  has_type (T1::G) e2 T2 ->
  has_type G e1 T1 ->
  sem_type G (tapp (tabs e2) e1) (subst_tm e2 (length G) e1) T2.
Proof. 
  intros. intros H1 H2 WFE.
  assert (length G = length H2) as L. symmetry. eapply WFE. 
  eapply st_weaken1 with (H2':=[]) in H0 as A; eauto.
  destruct A as [v1 [? ?]].
  
  specialize (st_subst1 e1 e2 G T1 T2 H1 H2 v1) as ST; eauto.
  destruct ST as [v1' [v2' [? [? ?]]]]; eauto. eapply WFE. 

  assert (exp_type H1 H2 (tabs e2) (tabs e2) (TFun T1 T2)) as C.
  eapply fundamental_property. econstructor. eauto. eauto.
  destruct C as [vf [vf' [? [? ?]]]].
  
  exists v1', v2'. rewrite L. intuition.
  destruct H3 as [n1 ?].
  destruct H8 as [n2 ?].
  destruct H5 as [n3 ?].
  exists ((S (n1+n2+n3))). intros.
  destruct n. lia. simpl. 
  rewrite H3; try lia.
  destruct vf; destruct vf'; simpl in H11; try contradiction.
  rewrite H8; try lia.
  assert (S n2 > n2) as D. eauto. 
  specialize (H8 (S n2) D). simpl in H8. inversion H8. subst.
  rewrite H5. eauto. lia. 

  rewrite splice_zero in H6. eauto.  
Qed.


(* DCE *)
Lemma st_weaken_h1_gen: forall e1 T1 G
  (W: has_type G e1 T1),
  forall H1 H1' H2 HX,
    env_type (H1'++H1) H2 G ->
    exp_type (H1'++HX++H1) H2  (splice_tm e1 (length H1) (length HX)) e1 T1.
Proof.
  intros ? ? ? W. induction W; intros.
  - eapply bi_vtrue.
  - eapply bi_vfalse.
  - eapply bi_var_splice1; eauto.
  - eapply bi_app; eauto.
  - eapply bi_tabs. intros.
    eapply envt_extend in H; eauto.
    replace (vx1 :: H1' ++ H1) with ((vx1 :: H1') ++ H1) in H. 2: simpl; eauto.
    eapply IHW in H; eauto.
Qed.


Lemma st_weaken_h1: forall e1 T1 G
  (W: has_type G e1 T1),
  forall H1 H1' H2,
    env_type (H1'++H1) H2 G ->
    exists v2, tevaln H2 e1 v2 /\ 
    forall HX, exists v1, tevaln (H1'++HX++H1) (splice_tm e1 (length H1) (length HX)) v1 /\ val_type v1 v2 T1.
Proof.
  intros.
  assert (exp_type (H1' ++ H1) H2 e1 e1 T1). eapply fundamental_property; eauto.
  destruct H0 as [v2 [v1 [? [? ?]]]].
  exists v1. split. auto.
  intros. 
  eapply st_weaken_h1_gen in W; eauto.
  destruct W as [v2' [v1' [? [? ?]]]].
  exists v2'. split. eauto.
  assert (v1 = v1'). eapply tevaln_unique; eauto.
  subst v1. eauto.
Qed.


Lemma dce: forall G T1 T2 e ex
  (HE: has_type G e T2) 
  (HX: has_type G ex T1),
  sem_type G (tapp (tabs (splice_tm e (length G) 1)) ex) e T2.
Proof.
  intros. unfold sem_type.
  intros H1 H2 WFE.

  apply has_type_weaken with (G3 := [])(G2 := [T1]) in HE as WHE. simpl in WHE. 

  eapply fundamental_property in HX; eauto.
  destruct HX as [vx1 [vx2 [? [? ?]]]].

  assert (length G = length H1) as L. symmetry. eapply WFE.

  eapply st_weaken_h1 with (H1' := []) in HE as HE'; eauto.
  destruct HE' as [v2 [? ?]]. simpl in H5.
  specialize (H5 [vx1]).
  destruct H5 as [v1 [? ?]]; intuition.

  exists v1, v2. repeat split. rewrite L.
  
  assert (exp_type H1 H2 (tabs (splice_tm e (length G) 1)) (tabs (splice_tm e (length G) 1)) (TFun T1 T2)) as F. {
    eapply fundamental_property. econstructor; eauto. eauto. 
  }
  destruct F as [vf [vf' [? [? ?]]]].

  destruct H as [n1 H].
  destruct H7 as [n2 H7].
  destruct H5 as [n3 H5].
  exists (S (n1 + n2 + n3)). 
  intros. destruct n. simpl. lia.
  simpl. rewrite <- L. rewrite H7.
  destruct vf; destruct vf'; simpl in H7; try contradiction.
  rewrite H.
  assert (S n2 > n2) as N. eauto.
  specialize (H7 (S n2) N). simpl in H7.
  inversion H7. subst.
  assert (n > n3) as NN. lia. 
  specialize (H5 n NN); intuition.
  replace (vx1::l) with ([vx1] ++ l); auto.
  rewrite <- H5. rewrite L. auto.
  lia. lia. auto. auto.
Qed.

(* CSE *)

Lemma has_type_subst_var: forall T1 G e2 T2 G'
  (W: has_type (G' ++  T1::T1::G) e2 T2), 
  has_type (G'++ T1 :: G) (subst_tm e2 (S (length G)) (tvar (length G))) T2.
Proof. 
  intros ? ? ? ? ? W. remember (G'++T1 :: T1 :: G) as GG. generalize dependent G'.
  induction W; intros; simpl; subst.
  + constructor.
  + constructor.
  + apply indexr_var_some' in H as H'. rewrite app_length in H'. simpl in H'. 
    destruct x.  
    - bdestruct (S (length G) <? 0); intuition.
      constructor. rewrite indexr_skips in H. rewrite indexr_skip in H.
      rewrite indexr_skips.  auto.  all: simpl; lia.
    - bdestruct (length G =? x); intuition. subst.
      constructor. 
      -- assert ((S (length G)) > (length G)). lia.
         replace (G' ++ T1 :: T1 :: G) with ((G'++[T1]) ++ T1 :: G) in H. 
         rewrite indexr_shift with (H := G) in H; auto.
         simpl in H.  
         replace ((G' ++ [T1])++G) with (G'++T1 ::G) in H; auto.
         rewrite <- app_assoc. simpl. auto. 
         rewrite <- app_assoc. simpl. auto. 
      -- bdestruct (S(length G) <? (S x)); intuition.  simpl.
         constructor.  assert (length G < (S x)). lia.
         replace (G' ++ T1 :: T1 :: G) with ((G'++[T1]) ++ T1 :: G) in H. 
         rewrite indexr_shift with (H := G) in H; auto.
         simpl in H. 
         replace ((G' ++ [T1])++G) with (G'++T1 ::G) in H; auto.
         rewrite <- app_assoc. simpl. auto. 
         rewrite <- app_assoc. simpl. auto. 
         constructor.  
         rewrite indexr_skips. 2:  simpl; lia.
         rewrite indexr_skips in H. 2: simpl; lia.
         rewrite indexr_skip in H. 2: simpl; lia. auto.
  + intuition. econstructor; eauto.
  + econstructor. bdestruct (length G <? (S (length G))); intuition.
    replace (T0 :: G' ++ T1 :: G) with ((T0 :: G') ++ T1 :: G); auto.
Qed.    

Lemma has_type_subst_var1: forall T1 G e2 T2
  (W: has_type (T1::T1::G) e2 T2), 
  has_type (T1 :: G) (subst_tm e2 (S (length G)) (tvar (length G))) T2.
Proof.
  intros. specialize (has_type_subst_var T1 G e2 T2 []); intuition.
Qed.


Lemma bi_var_subst': forall G G' H1 H1'  H2' H2 x v1 v1' v2 e1 T1 T0
  (WFE: env_type (H1'++H1) (H2'++H2) (G' ++ G)),
  indexr x (G' ++ T1 :: G) = Some T0 ->
  length H1 = length G ->
  length H2 = length G ->
  tevaln H1 e1 v1 ->
  tevaln (H1'++H1) (splice_tm e1 (length H1) (length H1')) v1 ->
  tevaln (H2'++H2) (splice_tm e1 (length H2) (length H2')) v2 ->
  val_type v1 v2 T1 ->
  val_type v1' v2 T1 ->
  exp_type (H1'++v1'::H1) (H2'++H2) (tvar x) (subst_tm (tvar x) (length H2) (splice_tm e1 (length H2) (length H2'))) T0.
Proof. 
  intros. simpl. 
  bdestruct (length H2 =? x).
  - subst x. 
    assert (T0 = T1).
    rewrite indexr_skips in H. replace (length H2) with (length G) in H; auto.  rewrite indexr_head in H. inversion H. auto. simpl. lia.
    exists v1', v2. repeat split.
    exists 0. intros. destruct n. lia. simpl. replace (length H2) with (length H1).
    f_equal. 
    rewrite indexr_skips. rewrite indexr_head. auto. simpl. lia. congruence.
    subst.
    simpl. bdestruct (length H2 =? length G). eauto. lia. subst T0. eauto. 
  - assert (env_type (H1' ++v1::H1) (H2'++ v2::H2) (G' ++ T1 :: G)) as WFE'. {
      eapply envt_insert; eauto.
    }
    simpl. 
    bdestruct (length H2 <? x).
    
    eapply WFE' in H.
     
    destruct H as [v3 [v4 [IX3 [IX4 VT]]]].
    exists v3, v4. repeat split. 
    exists 0. intros. destruct n. simpl. lia. simpl.
    assert(x > length H1). lia.
    rewrite indexr_shift in IX3; auto.
    f_equal. rewrite indexr_shift; auto.

    exists 0. intros. destruct n. simpl. lia.
    simpl. eapply indexr_shift in IX4. rewrite IX4. auto. auto.
    auto.

    
    eapply WFE' in H. destruct H as [v3 [v4 [IX3 [IX4 VT]]]].
    exists v3, v4. repeat split.
    exists 0. intros. destruct n. lia. simpl.
    rewrite indexr_skips in IX3. 2: simpl; lia.
    rewrite indexr_skip in IX3. 
    rewrite indexr_extend with (H' := (H1'++[v1'])) in IX3. intuition.
    replace (H1'++v1'::H1) with ((H1'++[v1']) ++ H1). congruence.
    rewrite <- app_assoc. simpl. auto.
    replace (length  H1) with (length H2). auto. congruence.
    exists 0. intros. destruct n. lia. simpl.
    bdestruct (length H2 =? x); intuition.
    bdestruct (x <? length H2); intuition.
    rewrite indexr_skips in IX4. 2: simpl; auto.
    rewrite indexr_skip in IX4. 2: lia.
    f_equal. rewrite indexr_skips; eauto. auto.
Qed.


Lemma st_subst' : forall e2 T2 G0
                        (W: has_type G0 e2 T2),
  forall G' G T1, G0 = G'++T1::G ->
  forall H1 H1'  H2 H2' e1 v1 v1',
    env_type (H1'++H1) (H2'++H2) (G'++G) ->
    length H1 = length G ->
    length H2 = length G ->
    tevaln H1 e1 v1 ->
    (forall H1'',
       tevaln (H1''++ H1) (splice_tm e1 (length H1) (length H1'')) v1 /\
       (forall H2', exists v2, tevaln (H2'++H2) (splice_tm e1 (length H2) (length H2')) v2 /\ val_type v1 v2 T1 /\ val_type v1' v2 T1)) -> (* via st_weaken *)
    
    exp_type (H1' ++ v1':: H1) (H2'++H2) e2 (subst_tm e2 (length H2) (splice_tm e1 (length H2) (length H2'))) T2.
Proof.  
  intros ? ? ? W. induction W; simpl; intros.
  - eapply bi_vtrue.
  - eapply bi_vfalse.
  - destruct (H7 H1').  destruct (H9 H2') as [v2 [? ?]]. subst env.
    eapply bi_var_subst'; eauto. all: intuition. 
  - eapply bi_app; eauto.
  - eapply bi_tabs. intros. subst env.
    eapply envt_extend in H0; eauto.
    replace (vx1 :: H1' ++ H1) with ((vx1 :: H1') ++ H1) in H0. 2: simpl; eauto.
    replace (vx2 :: H2' ++ H2) with ((vx2 :: H2') ++ H2) in H0. 2: simpl; eauto.
    rewrite splice_acc. 
    eapply IHW with (H1':=(vx1::H1')) (H2':=(vx2::H2')).
    replace (T1 :: G' ++ T0 :: G) with ((T1 :: G') ++ T0 :: G). 2: simpl; eauto.
    eauto. eauto. eauto. eauto. eauto.  eauto.
Qed.

Lemma st_subst1' : forall e1 e2 G T1 T2 H1 H2 v1 v1',
    has_type (T1::G) e2 T2 ->
    env_type H1 H2 G ->
    length H1 = length G ->
    length H2 = length G ->
    tevaln H1 e1 v1 ->  
    (forall H1'',
       tevaln (H1''++ H1) (splice_tm e1 (length H1) (length H1'')) v1 /\
       (forall H2', exists v2, tevaln (H2'++H2) (splice_tm e1 (length H2) (length H2')) v2 /\ val_type v1 v2 T1 /\ val_type v1' v2 T1)) -> (* via st_weaken *)
    exp_type (v1'::H1) H2 e2 (subst_tm e2 (length H2) (splice_tm e1 (length H2) 0)) T2.
Proof. 
  intros. eapply st_subst' with (G':=[]) (H1':=[]) (H2':=[]); eauto. eauto.
Qed.

Lemma cse: forall G T1 T2 e1 e2
  (HE: has_type (T1::T1::G) e2 T2) 
  (HX: has_type G e1 T1),
  sem_type G (tapp (tabs (tapp (tabs e2) (splice_tm e1 (length G) 1))) e1) 
             (tapp (tabs (subst_tm e2 (S (length G)) (tvar (length G)))) e1) T2.
Proof.
  intros. intros H1 H2 WFE.

  assert (has_type (T1 :: G) (subst_tm e2 (S(length G)) (tvar (length G))) T2) as X. {
    eapply has_type_subst_var1; eauto.
  }

  assert (has_type (T1 :: G) (tvar (length G)) T1) as XX. {
    constructor. rewrite indexr_head. auto.
  }

  eapply has_type_weaken with (G3 := [])(G2 := [T1]) in HX as WHX. auto.

  assert (length G = length H1) as L1. symmetry. eapply WFE.  
  assert (length G = length H2) as L2. symmetry. eapply WFE. 
  eapply st_weaken1 with (H2':=[]) in HX as A; eauto.
  eapply st_weaken_h1 with (H1' := []) in HX as B; eauto.
  destruct A as [v1 [? ?]].
  destruct B as [v2 [? ?]].
  specialize (H0 ([v2])).
  specialize (H4 ([v1])).
  destruct H0 as [v2' [? ?]].
  destruct H4 as [v1' [? ?]].
  simpl in *.
  assert (val_type v1 v2 T1)  as VX1. {
    assert (exp_type H1 H2 e1 e1 T1). {
     eapply fundamental_property; eauto.
    }
    destruct H7 as [v1'' [v2'' [? [? ?]]]].
    assert (v1'' = v1). eapply tevaln_unique; eauto.
    assert (v2'' = v2). eapply tevaln_unique; eauto.
    subst. auto.
  }

  assert (env_type (v1:: H1) (v2::H2)  (T1::G)). eapply envt_extend in VX1; eauto.
  assert (val_type v1' v2' T1) as VX2. {
     assert (exp_type (v1:: H1) (v2::H2) 
        (splice_tm e1 (length G) 1) 
        (splice_tm e1 (length G) 1)  T1). {
     eapply fundamental_property; eauto.
    }
    destruct H8 as [v1'' [v2'' [? [? ?]]]].
    assert (v1'' = v1'). eapply tevaln_unique; eauto. rewrite L1. auto.
    assert (v2'' = v2'). eapply tevaln_unique; eauto. rewrite L2. auto.
    subst. auto.
  }
  (*   F1  *)
  assert (exp_type H1 H2 (tabs (tapp (tabs e2) (splice_tm e1 (length G) 1)))(tabs
        (tapp (tabs e2) (splice_tm e1 (length G) 1))) (TFun T1 T2)) as F1. {
            eapply fundamental_property; eauto.
  }
  destruct F1 as [vf11 [vf22 [? [? VF1]]]].
  destruct vf11; destruct vf22; simpl in VF1; try contradiction.
  specialize (VF1 v1 v2); intuition.
  assert (l = H1 /\ t = (tapp (tabs e2) (splice_tm e1 (length G) 1))). { 
    destruct H8 as [n H8]. assert (S n > n) as N. lia.
    specialize (H8 (S n) N). simpl in H8. inversion H8. intuition.
  } 
  assert (l0 = H2 /\ t0 = (tapp (tabs e2) (splice_tm e1 (length G) 1))). {
    destruct H9 as [n H9]. assert (S n > n) as N. lia.
    specialize (H9 (S n) N). simpl in H9. inversion H9. intuition.
  }
  intuition. subst t0. subst t.
  subst.

  destruct H10 as [vy1 [vy2 [? [? ?]]]]; intuition.


  
  (* F2 *)
  assert (exp_type (v1::H1)(v2::H2)(tabs e2)(tabs e2)(TFun T1 T2)) as F. {
    eapply fundamental_property; eauto.
  }
  
  destruct F as [vf1 [vf2 [? [? VF]]]].
  destruct vf1; destruct vf2; simpl in VF; try contradiction.

  assert (l = (v1::H1) /\ t = e2). { 
    destruct H13 as [n H13]. assert (S n > n) as N. lia.
    specialize (H13 (S n) N). simpl in H13. inversion H13. intuition.
  }
  assert (l0 = (v2::H2) /\ t0 = e2). { 
    destruct H14 as [n H14]. assert (S n > n) as N. lia.
    specialize (H14 (S n) N). simpl in H14. inversion H14. intuition.
  }
  intuition. subst t0. subst t.
  subst. 
  
  
  assert (env_type (v1::v1::H1)(v2'::v2::H2)(T1::T1::G)). eapply envt_extend in H5; eauto.
  
  specialize (st_subst1' (tvar (length G)) e2 (T1::G) T1 T2 (v1::H1) (v2::H2) v1 v1') as ST; eauto.
  destruct ST as [vy3 [vy4 [? [? ?]]]]; eauto. 
  assert (length H1 = length G) as L'. eapply WFE.
  simpl. lia. simpl. lia.
  exists 0. intros. destruct n. intuition. simpl.
  rewrite L1. bdestruct (length H1 =? length H1); intuition.
  repeat split.
  exists 0. intros. destruct n. intuition. simpl.
  rewrite L1. bdestruct (length H1 <? (S(length H1))); intuition.
  rewrite indexr_skips. rewrite indexr_head. auto. simpl. auto.
  
  intros.  exists v2; intuition.  simpl.
  exists 0. intros. destruct n. intuition.
  bdestruct (length  G <? (S (length H2))); intuition.
  simpl.  replace (length G) with (length H2); intuition.
  f_equal. rewrite indexr_skips. rewrite indexr_head. auto. simpl. auto.

  assert (exp_type H1 H2  (tabs
        (subst_tm e2 (S (length G))
           (tvar (length G))))(tabs
        (subst_tm e2 (S (length G))
           (tvar (length G)))) (TFun T1 T2) ). {
           eapply fundamental_property; eauto. 
           }
  destruct H19 as [vf3 [vf3'[? [? ?]]]]; intuition.
  destruct vf3; destruct vf3'; simpl in H21; try contradiction.
  specialize (H21 v1 v2 VX1); intuition.
  destruct H21 as [vy5 [vy6 [? [? ?]]]].
  assert (l0 = H2 /\ t0 = (subst_tm e2 (S (length G))(tvar (length G))) ). {
    destruct H20 as [n H20]. assert (S n > n) as N. lia.
    specialize (H20 (S n) N). simpl in H20. inversion H20. intuition.
  }
  assert (l = H1 /\ t = (subst_tm e2 (S (length G)) (tvar (length G)))). {
    destruct H19 as [n H19]. assert (S n > n) as N. lia.
    specialize (H19 (S n) N). simpl in H19.  inversion H19. intuition.
  }
  intuition.                 
  subst l0. subst t0. subst l. subst t.

  assert (vy4 = vy6). { rewrite splice_zero in H17.  simpl in H17. replace (length H2)  with (length G)  in H17.
  eapply tevaln_unique; eauto.
  }
  subst vy4.

  exists vy1, vy6.  intuition.
  destruct H as [n1 H].
  destruct H4 as [n2 H4].
  destruct H8 as [n3 H8].
  destruct H10 as [n4 H10].
  exists (S (n1+n2+n3+n4)).
  intros. destruct n. intuition.
  simpl. rewrite H8. 
  replace (length G) with (length H1).
  rewrite H. replace (length G) with (length H1) in H10. 
  rewrite H10. auto. lia. lia. lia.

  destruct H3 as [n1 H3]. 
  destruct H20 as [n3 H20].
  destruct H22 as [n4 H22].
  exists (S (n1+n3+n4)).
  intros. destruct n. intuition.
  simpl. rewrite H20. rewrite H3. rewrite H22. auto.
  lia. lia. lia.

  assert (tevaln (v1 :: H1)
        (tapp (tabs e2)
           (splice_tm e1 (length G) 1)) vy3). {
    destruct H4 as [n1 H4].
    destruct H16 as [n2 H16].
    destruct H13 as [n3 H13].
    exists (S (n1 + n2 +n3)). 
    intros. destruct n; intuition.
    simpl. rewrite H13.
    replace (length G) with (length H1).
    rewrite H4. rewrite H16. auto. lia. lia.  
    lia.
    
  }
  assert (vy1 = vy3). eapply tevaln_unique; eauto.
  subst vy1. auto.
    
Qed.

End STLC.



