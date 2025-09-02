(*******************************************************************************
* Coq mechanization of the simply typed calculus with first-order mutable store (the λ$_b$-calculus).
* - Syntactic definitions
* - Semantic definitions
* - Metatheory
*******************************************************************************)

(* Full safety for STLC *)

(* 
Simply-typed lambda calculus with first-order mutable store, proof of semantic type soundness and termination using logical relations.

THIS FILE:

- types 
- references
  - boolean values
  - mutation with put/get
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

Module STLC.

(*******************************************************************************
* Syntactic Definitions
* - Typing `has_type`
*******************************************************************************)

(* ---------- qualifier sets ---------- *)

Definition qif (b:bool) q (x:nat) := if b then q x else false.


Definition pl := nat -> Prop.

Definition pempty: pl := fun x => False.                            (* empty set *)

Definition pone (x:nat): pl := fun x' => x' = x.                    (* singleton set *)

Definition pand p1 p2 (x:nat) := p1 x /\ p2 x.                      (* intersection *)

Definition por p1 p2 (x:nat) := p1 x \/ p2 x.                       (* union *)

Definition pnot p1 (x:nat) := ~ p1 x.                               (* complement *)

Definition pdiff p1 p2 (x:nat) := p1 x /\ ~ p2 x.                   (* difference *)

Definition pnat n := fun x' =>  x' < n.                             (* numeric bound *)

Definition pdom {X} (H: list X) := fun x' =>  x' < (length H).      (* domain of a list *)

Definition pif (b:bool) p (x:nat) := if b then p x else False.      (* conditional *)

Definition psub (p1 p2: pl): Prop := forall x:nat, p1 x -> p2 x.    (* subset inclusion *)

Definition plift (b: ql): pl := fun x => b x = true.                (* reflect nat->bool set *)


(* ---------- language syntax ---------- *)

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
  | tput : tm -> tm -> tm  
  | tapp : tm -> tm -> tm 
  | tabs : tm -> tm 
  | tseq : tm -> tm -> tm
.


Inductive vl : Type :=
  | vbool : bool -> vl
  | vref  : id -> vl
  | vabs  : list vl -> tm -> vl    (* closure record  *)
                                   
.

Definition venv := list vl.
Definition tenv := list ty.

Definition stor := list vl.


#[global] Hint Unfold venv.
#[global] Hint Unfold tenv.
#[global] Hint Unfold stor.


Definition closed_ql m q := (forall x, q x = true -> x < m).

Inductive closed_ty: nat -> ty -> Prop :=
| c_bool: forall m,
    closed_ty m TBool
| c_ref: forall m T, 
    closed_ty m T ->
    closed_ty m (TRef T)
| c_fun: forall m T1 T2,
    closed_ty m T1 ->
    closed_ty m T2 ->   
    closed_ty m (TFun T1 T2)
.


(* ---------- syntactic typing rules ---------- *)

Inductive has_type : tenv -> tm -> ty -> Prop :=
| t_true: forall env,
    has_type env ttrue TBool  
| t_false: forall env,
    has_type env tfalse TBool 
| t_var: forall x env T ,
    indexr x env = Some T ->
    has_type env (tvar x) T  
| t_ref: forall t env,
    has_type env t TBool ->
    has_type env (tref t) (TRef TBool)  
| t_get: forall t env,
    has_type env t (TRef TBool)   ->
    has_type env (tget t) TBool 
| t_put: forall t1 t2 env ,
    has_type env t1 (TRef TBool) ->
    has_type env t2 TBool  ->
    has_type env (tput t1 t2) TBool
| t_app: forall env f t T1 T2 ,
    has_type env f (TFun T1 T2) ->  
    has_type env t T1  ->
    has_type env (tapp f t) T2 
| t_abs: forall env t T1 T2 ,
    has_type (T1::env) t T2 ->
    closed_ty (length env) T1 ->
    closed_ty (length env) T2 ->
    has_type env (tabs t) (TFun T1 T2)
| t_seq: forall env t1 t2,
    has_type env t1 TBool ->
    has_type env t2 TBool ->
    has_type env (tseq t1 t2) TBool
.

(*******************************************************************************
* Semantic Definitions
* - Bigstep Interpreter `teval`
* - Value Interpretation `val_type`
* - Semantic Typing `sem_type`
*******************************************************************************)

(* ---------- operational semantics ---------- *)


(*
None             means timeout
Some None        means stuck
Some (Some v))   means result v
*)  


Fixpoint teval(n: nat)(M:stor)(env: venv)(t: tm){struct n}: nat * stor * option (option vl) :=
  match n with
    | 0 => (0, M, None)
    | S n =>
      match t with
        | ttrue      => (1, M, Some (Some (vbool true)))
        | tfalse     => (1, M, Some (Some (vbool false)))
        | tvar x     => (1, M, Some (indexr x env))
        | tref ex    =>
          match teval n M env ex with
            | (dx, M', None)           => (1+dx, M', None)
            | (dx, M', Some None)      => (1+dx, M', Some None)
            | (dx, M', Some (Some vx)) => (1+dx, vx::M', Some (Some (vref (length M'))))
          end
        | tget ex    =>
          match teval n M env ex with
            | (dx, M', None)                     => (1+dx, M', None)
            | (dx, M', Some None)                => (1+dx, M', Some None)
            | (dx, M', Some (Some (vbool _)))    => (1+dx, M', Some None)
            | (dx, M', Some (Some (vabs _ _))) => (1+dx, M', Some None)
            | (dx, M', Some (Some (vref x)))     => (1+dx, M', Some (indexr x M'))
          end
        | tput er ex    =>
          match teval n M env er with
            | (dr, M', None)                     => (1+dr, M', None)
            | (dr, M', Some None)                => (1+dr, M', Some None)
            | (dr, M', Some (Some (vbool _)))    => (1+dr, M', Some None)
            | (dr, M', Some (Some (vabs _ _))) => (1+dr, M', Some None)
            | (dr, M', Some (Some (vref x))) =>
              match teval (n-dr) M' env ex with
                | (dx, M'', None)                => (1+dr+dx, M'', None)
                | (dx, M'', Some None)           => (1+dr+dx, M'', Some None)
                | (dx, M'', Some (Some vx)) =>
                    match indexr x M'' with
                    | Some v => (1+dr+dx, update M'' x vx, Some (Some (vbool true)))
                    | _      => (1+dr+dx, M'', Some None)
                    end
              end
          end
        | tseq e1 e2   =>
          match teval n M env e1 with
          | (dx, M', None) => (1+dx, M', None)
          | (dx, M', Some None) => (1+dx, M', Some None)
          | (dx, M', Some (Some (vbool b1))) => 
              match teval n M' env e2 with
              | (dr, M'', None) => (1+dx+dr, M'', None)
              | (dr, M'', Some None) => (1+dx+dr, M'', Some None)
              | (dr, M'', Some (Some (vbool b2))) => (1+dx+dr, M'', Some (Some (vbool (b1 && b2))))
              | (dr, M'', Some (Some (vref _))) => (1+dx+dr, M'', Some None)
              | (dr, M'', Some (Some (vabs _ _))) => (1+dx+dr, M'', Some None)
              end
          | (dx, M', Some (Some (vref _))) => (1+dx, M', Some None)
          | (dx, M', Some (Some (vabs _ _))) => (1+dx, M', Some None)
          end  
        | tabs y   => (1, M, Some (Some (vabs env y)))
        | tapp ef ex =>
          match teval n M env ef with
            | (df, M', None)                  => (1+df, M', None)
            | (df, M', Some None)             => (1+df, M', Some None)
            | (df, M', Some (Some (vbool _))) => (1+df, M', Some None)
            | (df, M', Some (Some (vref _)))  => (1+df, M', Some None)
            | (df, M', Some (Some (vabs env2 ey))) =>
              match teval (n-df) M' env ex with
                | (dx, M'', None)           => (1+df+dx, M'', None)
                | (dx, M'', Some None)      => (1+df+dx, M'', Some None)
                | (dx, M'', Some (Some vx)) =>
                  match teval (n-df-dx) M'' (vx::env2) ey with
                    | (dy, M''', ry) => (1+df+dx+dy, M''', ry)
                  end
              end
          end
      end
  end.

Definition tevaln M env e M' v :=
  exists nm,
  forall n,
    n > nm ->
    teval n M env e = (nm, M', Some (Some v)).



(* ---------- logical relation ---------- *)

Definition stty: Type := list ((vl -> Prop)).


Definition st_types (M: stty) := M.
Definition st_locs (M: stty) := pdom M.

Definition store_type (S: stor) (M: stty) :=
  length M = length S /\
    (forall l,
      st_locs M l ->
      exists vt v,
        indexr l M = Some vt /\
          indexr l S = Some v /\
          vt v)
.


Definition st_zero: stty := [].

Definition st_extend M1 vt: stty := vt::M1.

Definition st_chain (M: stty) (M1: stty) :=
  psub (st_locs M) (st_locs M1) /\
  forall l, (st_locs M) l -> 
   indexr l M = indexr l M1.


#[global] Hint Unfold st_types.
#[global] Hint Unfold st_locs.


(* value interpretation of types *)

Fixpoint val_type (M:stty)(H:venv) v T : Prop :=
  match v, T with
  | vbool b, TBool =>
      True
  | vref l, TRef T =>
      T = TBool /\
      st_locs M l /\
      exists vt,
        indexr l M = Some vt /\
      (forall M',
      st_chain M M' -> 
      forall v,
      (vt v <-> val_type M' H v T ))
      
  | vabs G ty, TFun T1 T2  =>
        closed_ty (length H) T1 /\
        closed_ty (length H) T2 /\
        (forall S' M' vx,
            st_chain M M' 
            ->
              store_type S' M'
            ->
            val_type
              M'
              H
              vx
              T1
            -> 
              exists S'' M'' vy,
                tevaln
                  S'
                  (vx::G)
                  ty
                  S''
                  vy
                /\
                  st_chain M' M'' 
                /\
                  store_type S'' M''
                /\
                  val_type
                    M''
                    H
                    vy
                    T2)
  | _,_ =>
      False
  end.

(* term interpretation *)

Definition exp_type S M H t T :=
  exists S' M' v,
    tevaln S H t S' v /\
    st_chain M M'  /\
    store_type S' M' /\
    val_type M' H v T.


(* semantic context interpretation *)

Definition env_type M H G :=
  length H = length G /\
    (forall x T,
        indexr x G = Some T ->
        exists v : vl,
          indexr x H = Some v /\
          val_type M H v T) 
.

(* semantic types *)
Definition sem_type G t T :=
  forall S M E,
    env_type M E G  ->
    store_type S M  ->
    exp_type S M E t T. 


#[export] Hint Constructors ty: core.
#[export] Hint Constructors tm: core.
#[export] Hint Constructors vl: cor.


#[export] Hint Constructors has_type: core.

#[export] Hint Constructors option: core.
#[export] Hint Constructors list: core.

(* ---------- qualifier reflection & tactics  ---------- *)

Ltac unfoldq := unfold psub, pdom, pnat, pdiff, pnot, pif, pand, por, pempty, pone  in *.
Ltac unfoldq1 := unfold qsub, qdom, qand, qempty, qone in *.



(* ---------- closedness, vars_locs lemmas  ---------- *)


Lemma closedty_extend : forall {m T}, closed_ty m T -> 
  forall {m'}, m <= m' -> closed_ty m' T.
Proof. 
    intros. induction T; constructor.
    all: inversion H; subst; intuition.
Qed.


(* ---------- store typing lemmas  ---------- *)

Lemma stchain_trans: forall M1 M2 M3,
  st_chain M1 M2  ->
  st_chain M2 M3  ->
  st_chain M1 M3.
Proof.
  intros. destruct H, H0.
  split. unfoldq. intuition.
  intros. rewrite H1, H2. eauto. eapply H in H3. auto. auto.
Qed.


Lemma stchain_refl: forall M,
    st_chain M M.
Proof.
  intros. split. unfoldq. intuition.
  split. 
Qed.

Lemma st_mono: forall M M',
  st_chain M M' ->
  length M <= length M'.
Proof.
  intros. destruct H as [? ?].
  unfoldq; intuition. unfold st_locs, pdom in *. 
  destruct (length M). lia. eapply H. lia.
Qed. 

Lemma storet_extend: forall S M S1 M1 E G T vx vt
  (ST:  store_type S M)
  (ST1: store_type S1 M1)
  (WFE: env_type M E G)
  (SC1: st_chain M M1)
  (SC2: st_chain M1 (st_extend M1 vt))
  (HVX: val_type M1 E vx T)
  (VT:  vt = (fun v : vl => val_type M1 E v T)),
  store_type (vx :: S1) (st_extend M1 vt).
Proof.
  intros.
  remember ST1 as ST1'. destruct ST1' as (STL & STT). clear HeqST1'.
  split.
  - simpl. lia.
  - intros l SL. unfold st_extend in *.
    bdestruct (l =? length M1).
    + subst l. 
      exists vt, vx.
      split. 2: split. 
      * rewrite indexr_head. eauto.
      * rewrite STL, indexr_head. intuition.
      * subst vt. eauto.
    + destruct (STT l) as (vt1 & v1 & IXM & IXS & VT1).
      unfold st_locs in *. unfoldq. simpl in SL. lia. 
      exists vt1, v1.
      split. 2: split. 
      * rewrite indexr_skip. eauto. lia.
      * rewrite indexr_skip. eauto. lia. 
      * intuition.
Qed.


(* ---------- val_type lemmas  ---------- *)

Lemma valt_closed: forall T M H v,
    val_type M H v T ->
    closed_ty (length H) T.
Proof. 
  intros T. induction T; intros; destruct v; simpl in *; intuition.
  + econstructor.
  + subst T. repeat econstructor; eauto.
  + econstructor; eauto. 
Qed.


Lemma valt_store_extend: forall T M' M H v,
    val_type M H v T ->
    st_chain M M' ->
    val_type M' H v T.
Proof.
  intros T. induction T; intros; destruct v; simpl in *; intuition.
  + eapply H1. auto.
  + destruct H4 as [? [? ?]]. 
    exists x; intuition. destruct H1 as [? ?]. erewrite <- H5. auto.
    auto. eapply H4. eapply stchain_trans; eauto. auto. 
    eapply H4. eapply stchain_trans; eauto. auto. 
  + eapply H4. eapply stchain_trans; eauto. auto. auto. 
Qed.

Lemma valt_extend: forall T M H' H v,
    closed_ty (length H) T ->
    val_type M (H'++H) v T <-> val_type M H v T.
Proof. 
  intros T. induction T; split; intros; destruct v; simpl in *; intuition.
  - (* ref shrink *)
    destruct H4 as [vt [IM HV]].
    exists vt; intuition. eapply HV in H4. 
    eapply IHT. inversion H0. auto. eauto. eauto.
    eapply IHT in H4. eapply HV in H4. auto. auto. inversion H0. auto.
  - (* ref grows *)
    destruct H4 as [vt [IM HV]]. 
    exists vt; intuition. eapply IHT. inversion H0. auto.  eapply HV; eauto.
    eapply HV. eauto. eapply IHT; eauto. inversion H0. auto.
  - inversion H0. auto.
  - inversion H0. auto. 
  - (* Abs shrink *)
    inversion H0. subst.
    destruct (H4 S' M' vx) as [S'' [M'' [vy [HEY HVY]]]]. eauto. eauto. 
    eapply IHT1; eauto.
    exists S'', M'', vy. intuition.
    eapply IHT2; eauto.
  - eapply closedty_extend; eauto.
  - eapply closedty_extend; eauto.
  - (* Abs grow *)
    inversion H0. subst.
    destruct (H4 S' M' vx) as [S'' [M'' [vy [HEY [ST2 [HVY HQY]]]]]]. eauto. eauto.
      eapply IHT1; eauto.
    exists S'', M'', vy. intuition.
    eapply IHT2; eauto.
Qed.


Lemma valt_extend1: forall T M H v vx,
    closed_ty (length H) T ->
    val_type M (vx::H) v T <-> val_type M H v T.
Proof.
  intros. replace (vx :: H)  with ([vx]  ++ H); auto.
  eapply valt_extend; eauto.
Qed.


(* ---------- environment lemmas  ---------- *)

Lemma wf_env_type: forall M H G, 
  env_type M H G -> 
  (length H = length G /\
    pdom H = pdom G) .
Proof.
    intros. unfold env_type in H0. intuition.
    unfold pdom. rewrite H1. auto.
Qed.


Lemma envt_store_extend: forall M M' H G,
    env_type M H G ->
    st_chain M M'  ->
    env_type M' H G .
Proof.
  intros. remember H0 as WFE1. clear HeqWFE1. destruct H0 as [L W]. 
  repeat split; auto.
  intros.
  destruct (W _  _ H0) as [vx [IH HVX]]; intuition.
  exists vx; intuition.
  eapply valt_store_extend. eauto. auto.
Qed.


Lemma envt_extend_full: forall M M1 H G vx T1,
    env_type M H G ->
    val_type M1 H vx T1 ->
    closed_ty (length H) T1 ->
    st_chain M M1 ->
    env_type M1 (vx :: H) (T1 :: G).
Proof. 
  intros. apply wf_env_type in H0 as H0'. destruct H0' as (L' & PD (*& SG*)). 

  rename H0 into WFE.
  rename H3 into SC.
  
  remember WFE as WFE1. clear HeqWFE1.
  destruct WFE as [L W].

  repeat split; eauto.
  - simpl. eauto.
  - intros.
    bdestruct (x =? length G); intuition. 
    + subst. rewrite indexr_head in H0. inversion H0. subst.
      exists vx. split.
      rewrite <- L'. rewrite indexr_head. auto.
      eapply valt_extend1; eauto.
  
    + rewrite indexr_skip in H0. 2: { apply indexr_var_some' in H0. simpl in H0. lia. }
      destruct (W _ _  H0) as [v [IH VALT]].
      exists v. split.
      rewrite indexr_skip. auto. lia.
      eapply valt_store_extend. eapply valt_extend1; eauto. 
      eapply valt_closed; eauto. auto.
Qed.
                                                      

(* ---------- compatibility lemmas ---------- *)

Lemma sem_true: forall G,
    sem_type G ttrue TBool.
Proof.
  intros. intros S M H WFE ST.
  exists S, M, (vbool true). 
  split. 2: split. 3: split. 
  - exists 1. intros. destruct n. lia. simpl. intuition.
  - eapply stchain_refl. 
  - eauto.
  - simpl. eauto.
Qed.
  
Lemma sem_false: forall G,
    sem_type G tfalse TBool.
Proof.
  intros. intros S M H WFE ST.
  exists S, M, (vbool false).
  split. 2: split. 3: split. 
  - exists 1. intros. destruct n. lia. simpl. intuition.
  - eapply stchain_refl. 
  - eauto.
  - simpl. eauto.
Qed.
  
Lemma sem_var: forall x G T,
    indexr x G = Some T ->
    sem_type G (tvar x) T.
Proof.
  intros. intros ? ? ? WFE ST.
  destruct WFE as [L WFE].
  destruct (WFE x T H) as [vx [HI VT]]. 
  exists S, M, vx.
  split. 2: split. 3: split. 
  - exists 1. intros. destruct n. lia. simpl. rewrite HI. reflexivity.
  - eapply stchain_refl. 
  - eauto.
  - auto.
Qed.



Lemma sem_ref: forall t G,
    sem_type G t TBool ->
    sem_type G (tref t) (TRef TBool).
Proof.
  intros. intros ? ? ? WFE ST. 
  destruct (H S M E WFE ST) as [S1 [M1 [vx [IW1 [SC1 [ST1 HVX]]]]]].
  remember (length S1) as x.
  remember (fun v => val_type M1 E v TBool) as vt.
  assert (st_chain M1 (st_extend M1 vt)). {
    split. 
    unfoldq. intuition. 
    unfold st_locs, st_extend in *. unfoldq. simpl. intuition.
    intros. unfold st_locs, st_extend in *. rewrite indexr_skip. eauto. unfoldq. lia. }

  exists (vx::S1).
  exists (st_extend M1 vt ).
  exists (vref x). split. 2: split. 3: split. 
  + (* expression evaluates *)
    destruct IW1 as [n1 IW1]. rename S into St.
    exists (S n1).
    intros. destruct n. lia.
    subst x. simpl. rewrite IW1. eauto. lia.
  + (* stty chain *)
    eapply stchain_trans. eauto. auto.
  + (* store typing *)
    eapply storet_extend. eapply ST. all: eauto. 
  + (* result well typed *)
    auto. 
    remember (st_extend M1 vt) as M2.
    assert (store_type (vx::S1) (M2)) as ST2. {
      subst M2. eapply storet_extend. eapply ST. all: eauto.
    }
    remember ST1 as ST1'.
    destruct ST1' as (STL & STT). clear HeqST1'.
    split. 2: split. 
    * auto.
    * subst M2. unfold st_extend in *. unfold st_locs in *. unfoldq. simpl. lia.
    * exists vt. split.
      -- subst x M2. rewrite <-STL. unfold st_extend. rewrite indexr_head. auto.
      -- intros. subst vt. split; intros. auto.
         destruct v; try inversion H2. constructor.
Qed.

Lemma sem_get: forall t env,
    sem_type env t (TRef TBool) ->
    sem_type env (tget t) TBool.
Proof.
  intros. intros ? ? ? WFE ST.
  destruct (H S M E WFE ST) as [S1 [M1 [vx [IW1 [SC1 [ST1 HVX ]]]]]]. 
  destruct vx; try solve [inversion HVX]. simpl in HVX.
  destruct HVX as (? & ? & HVX).
  destruct HVX as [vt [IM HVX]].

  remember ST1 as ST1'. clear HeqST1'. destruct ST1' as (L & STL).
  destruct (STL i) as [vt' [v [IXM' [IXS VTS]]]].
  unfold st_locs. unfoldq; intuition. rewrite IM in IXM'. inversion IXM'. subst vt'.
  exists S1, M1, v. split. 2: split. 3: split. 
  + (* expression evaluates *)
    destruct IW1 as [n1 IW1]. rename S into St.
    exists (S n1).
    intros. destruct n. lia.
    simpl. rewrite IW1. rewrite IXS. eauto. lia.
  + (* st chain *)
    eauto. 
  + (* store type *)
    eauto.
  + (* result well typed *)
    simpl. eapply HVX; eauto. eapply stchain_refl; eauto. 
Qed.


Lemma sem_put: forall t1 t2 env,
    sem_type env t1 (TRef TBool) ->
    sem_type env t2 TBool ->
    sem_type env (tput t1 t2) TBool.
Proof.
  intros. intros ? ? ? WFE ST.
  destruct (H S M E WFE ST) as [S1 [M1 [vr [IW1 [SC1 [ST1 HVR]]]]]]. 
  eapply envt_store_extend in WFE as WFE1. 2: eapply SC1. 
  destruct (H0 S1 M1 E WFE1 ST1) as [S2 [M2 [vx [IW2 [SC2 [ST2 HVX]]]]]].

  destruct vr; try solve [inversion HVR]. simpl in HVR.
  destruct HVR as (? & ? & vt ).
  destruct vt as (vt & IM & HVT).

  
  destruct ST2 as (? & ST2).
  destruct (ST2 i) as (vt'' & vz & ? & ? & ?). eapply SC2. eauto. 
  assert (indexr i M2 = indexr i M1) as R. { symmetry. eapply SC2. eauto. }
  rewrite R in H4. 
  rename H5 into SI.

  exists (update S2 i vx), M2, (vbool true).
  split. 2: split. 3: split. 
  + (* expression evaluates *)
    rename S into St.
    destruct IW1 as [n1 IW1].
    destruct IW2 as [n2 IW2].
    exists (S (n1+n2)).
    intros. destruct n. lia.
    simpl. rewrite IW1. rewrite IW2. rewrite SI. eauto. lia. lia.
  + eapply stchain_trans; eauto. 
  + (* store type *)
    split. rewrite <-update_length. eauto. 
    intros. bdestruct (i =? l).
    * subst i. 
      exists vt''. exists vx. split.  2: split.
      -- rewrite R. eapply H4.
      -- rewrite update_indexr_hit. eauto. eapply indexr_var_some'. eauto.
      -- rewrite H4 in IM. inversion IM. subst vt''. eapply HVT. eapply stchain_refl; eauto.
         eauto.
    * rewrite update_indexr_miss. 2: eauto.
      eapply ST2. eauto.
    
  + (* result well typed *)
    constructor.
Qed.

Lemma sem_abs: forall env t T1 T2,
    sem_type (T1::env) t T2 ->
    closed_ty (length env) T1 ->
    closed_ty (length env) T2 ->
    sem_type env (tabs t) (TFun T1 T2).
Proof.
  intros. intros ? ? ? WFE ST.
  exists S.
  exists M. 
  exists (vabs E t).
  split. 2: split. 3: split. 
  + (* term evaluates *)
    exists 1. intros. destruct n. lia. simpl. eauto.
  + eapply stchain_refl. 
  + (* store typing *)
    eauto.
  + (* result well typed *)
    simpl.
    assert (length env = length E) as LE. { symmetry. eapply WFE. }
    assert (pdom env = pdom E) as DE. { unfold pdom. rewrite LE. eauto. }
    split. 2: split.
    rewrite <- LE. auto. rewrite <- LE. auto.
    intros.
    
    (* INDUCTION *)
    destruct (H S' M' (vx::E)) as [S2 [M2 [vy IHW1]]].
    eapply envt_extend_full; eauto. rewrite <- LE. auto. auto.
    
    destruct IHW1 as [? IHW1].
    exists S2, M2, vy. intuition.
    eapply valt_extend1; eauto. rewrite <- LE. auto.
Qed.



Lemma sem_app: forall env f t T1 T2,
    sem_type env f (TFun T1 T2)  ->  
    sem_type env t T1 ->   
    sem_type env (tapp f t) T2.
Proof.
  intros. intros S0 ? ? WFE ST.
  rename H into IHW1. rename H0 into IHW2. 
  destruct (IHW1 S0 M E WFE ST) as [S1 [M1 [vf [IW1 [SC1 [ST1 HVF]]]]]]. 
  assert (env_type M1 E env) as WFE1. { eapply envt_store_extend; eauto. }
  destruct (IHW2 S1 M1 E WFE1 ST1) as [S2 [M2 [vx [IW2 [SC2 [ST2 HVX]]]]]]. 

  (* vf is a function value: it can eval its body *)
  destruct vf; try solve [inversion HVF]. 

  destruct HVF; intuition.
  rename H2 into HVF.
  destruct (HVF S2 M2 vx) as [S3 [M3 [vy [IW3 [SC3 [ST3 HVY]]]]]]; eauto. 

  (* EVALUATION *)
  exists S3, M3, vy. split. 2: split. 3: split. 
  + (* expression evaluates *)
    (* - initial fuel value *)
    destruct IW1 as [n1 IW1].
    destruct IW2 as [n2 IW2].
    destruct IW3 as [n3 IW3].
    exists (S (n1+n2+n3)).
    (* - forall greater fuel *)
    intros. destruct n. lia.
    (* - result computes *)
    simpl. rewrite IW1. rewrite IW2. rewrite IW3.
    repeat rewrite app_assoc. repeat rewrite app_nil_r. eauto.
    all: lia.

  + eapply stchain_trans. eapply stchain_trans. eauto. eauto.  eauto. 
    
  (* STORE_TYPE *)
  + eauto.
 
  (* VAL_TYPE *)
  + eapply HVY.
Qed.

Lemma sem_seq: forall env t1 t2
  (E1: sem_type env t1 TBool)
  (E2: sem_type env t2 TBool),
  sem_type env (tseq t1 t2) TBool.
Proof.
  intros. intros S1 M1 H WFE ST.
  (* E1 *)
  destruct (E1 S1 M1 H WFE ST) as [S2 [M2 [v1 [IE1 [SC1 [ST1 HV1]]]]]].
  destruct v1; try solve [inversion HV1]. simpl in HV1.

  (* E2 *) 
  eapply envt_store_extend in WFE as WFE'. 2: eapply SC1.
  destruct (E2 S2 M2 H WFE' ST1) as [S3 [M3 [v2 [IE2 [SC2 [ST2 HV2]]]]]].
  destruct v2; try solve [inversion HV2]. simpl in HV2.

  exists S3.
  exists M3, (vbool (b && b0)).
  split. 2: split. 3: split. 
  + destruct IE1 as [n1 IE1].
    destruct IE2 as [n2 IE2].
    exists (S(n1 + n2)). intros. destruct n. intuition.
    simpl. rewrite IE1. rewrite IE2. eauto. lia. lia.

  + eapply stchain_trans; eauto.
  
  + eauto.
  
  + constructor; eauto.
Qed.  


(* Fundamental Theorem *)
Theorem fundamental_property : forall t G T,
    has_type G t T ->
    sem_type G t T.
Proof.
  intros ? ? ? W. 
  induction W.
  - eapply sem_true; eauto.
  - eapply sem_false; eauto.
  - eapply sem_var; eauto.
  - eapply sem_ref; eauto. 
  - eapply sem_get; eauto. 
  - eapply sem_put; eauto.
  - eapply sem_app; eauto.
  - eapply sem_abs; eauto.
  - eapply sem_seq; eauto.
Qed.

(* Semantic type safety and termination: if the term is well-typed, then 
   it evaluates to an actual value (not stuck and not a timeout) of the
   same time (for large enough n) *)

Corollary safety : forall t T,
  has_type [] t T -> 
  exp_type [] st_zero [] t T.
Proof. 
  intros. eapply fundamental_property in H; eauto.
  destruct (H [] st_zero []). 
  - unfold env_type; intuition; simpl.
    inversion H0.
  - unfold store_type; intuition. unfold st_locs, st_zero in *. unfoldq. simpl in *. lia. 
  - destruct H0. eexists. eexists. eauto.
Qed.

End STLC.
