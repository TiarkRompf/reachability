(* Full safety for STLC *)

(*

An LR-based termination and semantic soundness proof for STLC.

Add first-order mutable references (restricted to TBool)

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

(* ---------- language syntax ---------- *)

Definition id := nat.

Inductive ty : Type :=
  | TBool  : ty
  | TRef   : ty
  | TList  : ty -> ty
  | TFun   : ty -> ty -> ty
.

Inductive tm : Type :=
  | ttrue  : tm
  | tfalse : tm
  | tvar   : id -> tm
  | tnil   : tm 
  | tcons  : tm -> tm -> tm 
  | tfold  : tm -> tm -> tm -> tm 
  | tref   : tm -> tm
  | tget   : tm -> tm
  | tput   : tm -> tm -> tm
  | tapp   : tm -> tm -> tm
  | tabs   : tm -> tm
.

Inductive vl: Type :=
| vbool :  bool -> vl
| vref  :  id -> vl
| vlist :  list vl -> vl
| vabs  :  list vl -> tm -> vl 
.

Definition venv := list vl.
Definition tenv := list ty.

Definition stor := list vl.

#[global] Hint Unfold venv.
#[global] Hint Unfold tenv.
#[global] Hint Unfold stor.


(* ---------- syntactic typing rules ---------- *)

Inductive has_type : tenv -> tm -> ty -> Prop :=
| t_true: forall env,
    has_type env ttrue TBool
| t_false: forall env,
    has_type env tfalse TBool
| t_var: forall x env T,
    indexr x env = Some T ->
    has_type env (tvar x) T
| t_nil: forall env T,
    has_type env tnil (TList T)
| t_cons: forall env t1 t2 T,
    has_type env t1 T ->
    has_type env t2 (TList T) ->
    has_type env (tcons t1 t2) (TList T)
| t_fold: forall f z env T1 T2 t, (* fold (fun acc x => acc OR x) false [true, false, true] *)
    has_type (T2::T1::env) f T2 ->
    has_type env z T2  ->
    has_type env t (TList T1) ->
    has_type env (tfold f z t) T2
| t_ref: forall t env,
    has_type env t TBool ->
    has_type env (tref t) TRef
| t_get: forall t env,
    has_type env t TRef ->
    has_type env (tget t) TBool
| t_put: forall t t2 env,
    has_type env t TRef ->
    has_type env t2 TBool ->
    has_type env (tput t t2) TBool
| t_app: forall env f t T1 T2,
    has_type env f (TFun T1 T2) ->
    has_type env t T1 ->
    has_type env (tapp f t) T2
| t_abs: forall env t T1 T2,
    has_type (T1::env) t T2 ->
    has_type env (tabs t) (TFun T1 T2)
.

(* ---------- operational semantics ---------- *)

Fixpoint teval(n: nat)(M:stor)(env: venv)(t: tm){struct n}: stor * option (option vl) :=
  match n with
    | 0 => (M, None)
    | S n =>
      match t with
        | ttrue      => (M, Some (Some (vbool true)))
        | tfalse     => (M, Some (Some (vbool false)))
        | tvar x     => (M, Some (indexr x env))
        | tnil        => (M, Some (Some (vlist nil)))
        | tcons ehd et1 =>
          match teval n M env ehd with
            | (M', None) => (M', None)
            | (M', Some None) => (M', Some None)
            | (M', Some (Some vh)) =>
              match teval n M' env et1 with
                | (M'', None) => (M'', None)
                | (M'', Some None) => (M'', Some None)
                | (M'', Some (Some (vbool _ )))    => (M'', Some None)
                | (M'', Some (Some (vref _)))      => (M'', Some None)
                | (M'', Some (Some (vabs _ _))) => (M'', Some None)
                | (M'', Some (Some (vlist vtl))) => (M'', Some (Some (vlist (vh::vtl))))
              end
          end
        | tfold ef ez els =>
          match teval n M env ez with 
            | (M', None) => (M', None)
            | (M', Some None) => (M', Some None)
            | (M', Some (Some vz)) => 
              match teval n M' env els with
                | (M'', None) => (M'', None)
                | (M'', Some None) => (M'', Some None)
                | (M'', Some (Some (vbool _))) => (M'', Some None)
                | (M'', Some (Some (vabs _ _))) => (M'', Some None)
                | (M'', Some (Some (vref _)))   => (M'', Some None)
                | (M'', Some (Some (vlist vls))) =>
                    let f := fun hd tl =>
                               match tl with
                               | (M'', None) => (M'', None)
                               | (M'', Some None) => (M'', Some None)
                               | (M'', Some (Some vtl)) =>
                                   teval n M'' (vtl::hd::env) ef
                               end in
                    fold_right f (M'', (Some (Some vz))) vls
              end 
          end 
        | tref ex    =>
          match teval n M env ex with
            | (M', None)           => (M', None)
            | (M', Some None)      => (M', Some None)
            | (M', Some (Some vx)) => (vx::M', Some (Some (vref (length M'))))
          end
        | tget ex    =>
          match teval n M env ex with
            | (M', None) => (M', None)
            | (M', Some None) => (M', Some None)
            | (M', Some (Some (vbool _))) => (M', Some None)
            | (M', Some (Some (vlist _))) => (M', Some None)
            | (M', Some (Some (vabs _ _))) => (M', Some None)
            | (M', Some (Some (vref x))) => (M', Some (indexr x M'))
          end
        | tput er ex    =>
          match teval n M env er with
            | (M', None) => (M', None)
            | (M', Some None) => (M', Some None)
            | (M', Some (Some (vbool _))) => (M', Some None)
            | (M', Some (Some (vlist _))) => (M', Some None)
            | (M', Some (Some (vabs _ _))) => (M', Some None)
            | (M', Some (Some (vref x))) =>
              match teval n M' env ex with
                | (M'', None) => (M'', None)
                | (M'', Some None) => (M'', Some None)
                | (M'', Some (Some vx)) =>
                    match indexr x M'' with
                    | Some v => (update M'' x vx, Some (Some (vbool true)))
                    | _ => (M'', Some None)
                    end
              end
          end
        | tabs y     => (M, Some (Some (vabs env y)))
        | tapp ef ex =>
          match teval n M env ef with
            | (M', None) => (M', None)
            | (M', Some None) => (M', Some None)
            | (M', Some (Some (vbool _))) => (M', Some None)
            | (M', Some (Some (vlist _))) => (M', Some None)
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

(* value interpretation of terms *)
Definition tevaln M env e M' v :=
  exists nm,
  forall n,
    n > nm ->
    teval n M env e = (M', Some (Some v)).


(* ---------- LR definitions  ---------- *)

Definition stty := nat. (* length of store *)

Definition store_type (S: stor) (M: stty) :=
  length S = M /\
    forall i,
      i < M ->
      exists b, indexr i S = Some (vbool b).

Definition st_chain (M:stty) (M1:stty) :=
  M <= M1.


Fixpoint val_type M v T : Prop :=
  match v, T with
  | vbool b, TBool =>  
      True
  | vref l, TRef => 
      l < M
  | vlist vs1, TList T1 =>
      Forall (fun v => val_type M v T1) vs1
  | vabs H ty, TFun T1 T2 =>
      forall S' M' vx,
        st_chain M M' ->
        store_type S' M' ->
        val_type M' vx T1 ->
        exists S'' M'' vy,
          st_chain M' M'' /\
          tevaln S' (vx::H) ty S'' vy /\
          store_type S'' M'' /\
          val_type M'' vy T2
  | _,_ =>
      False
  end.


Definition exp_type S M H t T :=
  exists S' M' v,
    st_chain M M' /\
    tevaln S H t S' v /\
    store_type S' M' /\
    val_type M' v T.

Definition env_type M (H: venv) (G: tenv) :=
  length H = length G /\
    forall x T,
      indexr x G = Some T ->
      exists v,
        indexr x H = Some v /\
        val_type M v T.

Definition sem_type G t T :=
  forall S M H,
    env_type M H G ->
    store_type S M ->
    exp_type S M H t T.


#[export] Hint Constructors ty: core.
#[export] Hint Constructors tm: core.
#[export] Hint Constructors vl: core.

#[export] Hint Constructors has_type: core.

#[export] Hint Constructors option: core.
#[export] Hint Constructors list: core.




(* ---------- LR helper lemmas  ---------- *)

Lemma stchain_refl: forall M,
    st_chain M M.
Proof.
  intros. intuition.
Qed.


Lemma envt_empty:
    env_type 0 [] [].
Proof.
  intros. split. eauto. intros. inversion H. 
Qed.

Lemma envt_extend: forall M E G v1 T1,
    env_type M E G ->
    val_type M v1 T1 ->
    env_type M (v1::E) (T1::G).
Proof.
  intros. 
  remember H as WFE. clear HeqWFE.
  destruct H. split. simpl. eauto.
  intros x T IX. bdestruct (x =? length G).
  - subst x. rewrite indexr_head in IX. inversion IX. subst T1.
    exists v1. rewrite <- H. rewrite indexr_head. eauto.
  - rewrite indexr_skip in IX; eauto.
    eapply WFE in IX as IX. destruct IX as (v2 & ? & ?).
    exists v2. rewrite indexr_skip; eauto. lia.
Qed.

Lemma storet_empty:
    store_type [] 0.
Proof.
  intros. split. eauto. intros. inversion H. 
Qed.

Lemma storet_extend: forall S M vx,
    store_type S M ->
    val_type M vx TBool ->
    store_type (vx :: S) (1 + M).
Proof.
  intros. destruct H. split.
  - simpl. lia.
  - intros. bdestruct (i <? M).
    eapply H1 in H3 as H4. destruct H4. exists x. rewrite indexr_skip. eauto. lia.
    destruct vx; inversion H0. exists b. replace i with (length S).
    rewrite indexr_head. eauto. lia. 
Qed.

Lemma valt_store_extend: forall T M M' vx,
    val_type M vx T ->
    st_chain M M' ->
    val_type M' vx T.
Proof.
  intros T. induction T; intros; destruct vx; simpl in H; try contradiction.
  - simpl. eauto.
  - simpl. unfold st_chain in *. lia.
  - simpl. induction H.
    -- constructor.
    -- constructor. eapply IHT; eauto. auto.
  - simpl. intros. destruct (H S' M'0 vx); eauto.
    unfold st_chain in *. lia.
Qed.

Lemma envt_store_extend: forall M M' H G,
    env_type M H G ->
    st_chain M M' ->
    env_type M' H G.
Proof.
  intros. destruct H0 as (L & IX). split. 
  - eauto.
  - intros. edestruct IX as (v & IX' & VX). eauto.
    exists v. split. eauto. eapply valt_store_extend; eauto.
Qed.


(* ---------- LR compatibility lemmas  ---------- *)

Lemma sem_true: forall G,
    sem_type G ttrue TBool.
Proof.
  intros. intros S M E WFE ST.
  exists S, M, (vbool true).
  split. 2: split. 3: split.
  - eapply stchain_refl. 
  - exists 0. intros. destruct n. lia. simpl. eauto.
  - eauto. 
  - simpl. eauto. 
Qed.

Lemma sem_false: forall G,
    sem_type G tfalse TBool.
Proof.
  intros. intros S M E WFE ST.
  exists S, M, (vbool false).
  split. 2: split. 3: split.
  - eapply stchain_refl. 
  - exists 0. intros. destruct n. lia. simpl. eauto.
  - eauto.
  - simpl. eauto. 
Qed.

Lemma sem_var: forall G x T,
    indexr x G = Some T ->
    sem_type G (tvar x) T.
Proof.
  intros. intros S M E WFE ST.
  eapply WFE in H as IX. destruct IX as (v & IX & VX).
  exists S, M, v.
  split. 2: split. 3: split.
  - eapply stchain_refl. 
  - exists 0. intros. destruct n. lia. simpl. rewrite IX. eauto.
  - eauto.
  - eauto. 
Qed.

Lemma sem_nil: forall G T,
  sem_type G tnil (TList T).
Proof.
  intros. intros S M E WFE ST.
  exists S, M, (vlist nil).
  split. 2: split. 3: split.
  - eapply stchain_refl. 
  - exists 0. intros. destruct n. lia. simpl. eauto.
  - eauto.
  - simpl. constructor.
Qed.

Lemma sem_cons: forall G t1 t2 T,
  sem_type G t1 T ->
  sem_type G t2 (TList T) ->
  sem_type G (tcons t1 t2) (TList T).
Proof.
  intros. intros S M E WFE ST.
  destruct (H S M E WFE ST) as (S' & M' & vx & SC & EX & ST' & VX).
  edestruct H0  as (S'' & M'' & vlist & SC' & EL & ST'' & VL).
  eapply envt_store_extend. eapply WFE. eauto. eauto.

  destruct vlist; simpl in VL; try contradiction.

  exists S'', M'', (vlist (vx::l)).
  split. 2: split. 3: split.
  - unfold st_chain in *. lia.
  - destruct EX as (n1 & EX).
    destruct EL as (n2 & EL).
    exists (1+n1+n2). intros. destruct n. lia. simpl. rewrite EX. rewrite EL. auto. 
    lia. lia.
  - auto.
  - simpl. clear EL. constructor. eapply valt_store_extend. eauto. eauto. auto.
Qed.

Lemma sem_tfold: forall f z t G T1 T2,
  sem_type G z T2 ->
  sem_type G t (TList T1) ->
  sem_type (T2::T1::G) f T2 ->
  sem_type G (tfold f z t) T2.
Proof.
  intros. intros S M E WFE ST.
  destruct (H S M E WFE ST) as (S' & M' & vz & SC & EZ & ST' & VZ).
  edestruct H0 with (M := M') as (S'' & M'' & vl & SC' & ET' & ST'' & VL).
  eapply envt_store_extend; eauto. eauto.

  destruct vl; simpl in VL; try contradiction.

  assert (forall vz ve S3 M3,
    store_type S3 M3 ->
    st_chain M'' M3 ->
    val_type M3 ve T1 ->
    val_type M3 vz T2 ->
    exists vr SR MR,
      tevaln S3 (vz::ve:: E) f SR vr /\
      store_type SR MR /\
      st_chain M3 MR /\
      val_type MR vr T2
  ) as HFF. {
    intros. edestruct H1 with (M := M3) as (S3' & M3' & vf & SC'' & EF & ST''' & VL').
    eapply envt_extend. eapply envt_extend. eapply envt_store_extend. eapply WFE.
    unfold st_chain in *. lia. eauto. eauto. eauto. 
    exists  vf, S3', M3'. auto.
  }
  
  remember (fun n => fun (hd:vl) (tl:stor * option (option vl)) =>
     match tl with
      | (S', None) => (S', None)
      | (S', Some None) => (S', Some None)
      | (S', Some (Some vtl)) =>  teval n S' (vtl::hd::E) f
  end) as ff.

  assert (exists vr SR MR,
    (exists nm, forall n, n > nm ->
      fold_right (ff n) (S'', Some (Some vz)) l = (SR, Some (Some vr))) /\
      store_type SR MR /\
      st_chain M'' MR /\
    val_type MR vr T2) as FOLD. {
    clear ET'.
    induction l. 
    - exists vz, S'', M''. split. 2: split. 3: split. 
      -- exists 0. intros. simpl. eauto.
      -- eauto.
      -- unfold st_chain. lia.
      -- eapply valt_store_extend; eauto.
    - inversion VL. subst x l0.
       edestruct IHl as (vr & SR & MR & (nr1 & A) & ? & ? & ?). eauto.
       simpl. edestruct HFF  with (S3 := SR)(M3 := MR) as (vr' & SR' & MR' & (nr2 & B) & ? & ? &?).
       eauto. 
       eauto. 
       eapply valt_store_extend; eauto.
       eauto.
       exists vr', SR', MR'. split. 2: split. 3: split.
       exists (nr1+nr2). intros. rewrite A. 2:lia. 
       subst ff. eapply B. lia.
       all:auto. unfold st_chain in *. lia. 
  }
  
  destruct FOLD as (vr & SR & MR &? &? &? & ?).
  exists SR, MR, vr.
  split. 2: split. 3: split.
  + unfold st_chain in *. lia.
  + destruct EZ as (n1 & EZ).
    destruct ET' as (n2 & ET).
    destruct H2 as (n3 & E2).
    exists (1+n1+n2+n3). intros. destruct n. lia.
    simpl. rewrite EZ. rewrite ET. 2,3: lia. 
    subst ff. rewrite E2. auto. lia.
  + eauto.
  + auto.
Qed.


Lemma sem_ref: forall G t,
    sem_type G t TBool ->
    sem_type G (tref t) TRef.
Proof.
  intros. intros S M E WFE ST.
  destruct (H S M E WFE ST) as (S' & M' & vx & SC & TX & ST' & VX).
  exists (vx::S'), (1+M'), (vref (length S')).
  split. 2: split. 3: split.
  - unfold st_chain in *. lia.
  - destruct TX as (n1 & TX).
    exists (1+n1). intros. destruct n. lia. simpl. rewrite TX. eauto. lia.
  - eapply storet_extend. eauto. eauto. 
  - simpl. destruct ST'. lia. 
Qed.

Lemma sem_get: forall G t,
    sem_type G t TRef ->
    sem_type G (tget t) TBool.
Proof.
  intros. intros S M E WFE ST.
  destruct (H S M E WFE ST) as (S' & M' & vx & SC & TX & ST' & VX).
  destruct vx; simpl in VX; intuition.
  destruct ST' as (L & B). subst M'.
  eapply indexr_var_some in VX as VX'. destruct VX' as (vx & IX).
  exists S', (length S'), vx.
  split. 2: split. 3: split.
  - eauto. 
  - destruct TX as (n1 & TX).
    exists (1+n1). intros. destruct n. lia. simpl. rewrite TX. rewrite IX. eauto. lia.
  - unfold store_type. eauto.
  - edestruct B as (b & IX'). eauto. rewrite IX in IX'. inversion IX'. simpl. eauto. 
Qed.

Lemma sem_put: forall G t t2,
    sem_type G t TRef ->
    sem_type G t2 TBool ->
    sem_type G (tput t t2) TBool.
Proof.
  intros. intros S M E WFE ST.
  destruct (H S M E WFE ST) as (S' & M' & vx & SC & TX & ST' & VX).
  eapply envt_store_extend in WFE as WFE'. 2: eauto.
  destruct (H0 S' M' E WFE' ST') as (S'' & M'' & vy & SC' & TY & ST'' & VY).
  eapply valt_store_extend in VX. 2: eauto. 
  destruct vx; simpl in VX; intuition.
  destruct vy; simpl in VY; intuition.
  destruct ST'' as (L & B). subst M''.
  eapply indexr_var_some in VX as VX'. destruct VX' as (vx & IX).
  exists (update S'' i (vbool b)), (length S''), (vbool true).
  split. 2: split. 3: split.
  - unfold st_chain in *. lia. 
  - destruct TX as (n1 & TX).
    destruct TY as (n2 & TY).
    exists (1+n1+n2). intros. destruct n. lia. simpl. rewrite TX, TY, IX. eauto. lia. lia. 
  - split. rewrite <-update_length. eauto. intros. 
    bdestruct (i0 =? i). subst i0. exists b. rewrite update_indexr_hit; eauto.
    edestruct B. eauto. exists x. rewrite update_indexr_miss; eauto. 
  - simpl. eauto. 
Qed.

Lemma sem_app: forall G f t T1 T2,
    sem_type G f (TFun T1 T2) ->
    sem_type G t T1 ->
    sem_type G (tapp f t) T2.
Proof.
  intros ? ? ? ? ? HF HX. intros S M E WFE ST.
  destruct (HF S M E WFE ST) as (S' & M' & vf & SC & TF & ST' & VF).
  eapply envt_store_extend in WFE as WFE'. 2: eauto.
  destruct (HX S' M' E WFE' ST') as (S'' & M'' & vx & SC' & TX & ST'' & VX).
  destruct vf; simpl in VF; intuition.
  edestruct VF as (S''' & M'''& vy & SC'' & TY & ST''' & VY). eauto. eauto. eauto. 
  exists S''', M''', vy.
  split. 2: split. 3: split. 
  - unfold st_chain in *. lia. (* stchain_chain *)
  - destruct TF as (n1 & TF).
    destruct TX as (n2 & TX).
    destruct TY as (n3 & TY).
    exists (1+n1+n2+n3). intros. destruct n. lia.
    simpl. rewrite TF, TX, TY. 2,3,4: lia.
    eauto.
  - eauto. 
  - eauto.
Qed.

Lemma sem_abs: forall G t T1 T2,
    sem_type (T1::G) t T2 ->
    sem_type G (tabs t) (TFun T1 T2).
Proof.
  intros ? ? ? ? HY. intros S M E WFE ST.
  assert (length E = length G) as L. eapply WFE.
  exists S, M, (vabs E t).
  split. 2: split. 3: split.
  - eapply stchain_refl. 
  - exists 0. intros. destruct n. lia. simpl. eauto.
  - eauto. 
  - simpl. intros. eapply HY. eapply envt_extend; eauto. eapply envt_store_extend; eauto. eauto.
Qed.


                                                       
(* ---------- LR fundamental property  ---------- *)

Theorem fundamental: forall G t T,
    has_type G t T ->
    sem_type G t T.
Proof.
  intros ? ? ? W. 
  induction W.
  - eapply sem_true; eauto.
  - eapply sem_false; eauto.
  - eapply sem_var; eauto.
  - eapply sem_nil; eauto.
  - eapply sem_cons; eauto.
  - eapply sem_tfold; eauto.
  - eapply sem_ref; eauto.
  - eapply sem_get; eauto.
  - eapply sem_put; eauto.
  - eapply sem_app; eauto. 
  - eapply sem_abs; eauto.
Qed.

Corollary safety: forall t T,
  has_type [] t T ->
  exp_type [] 0 [] t T.
Proof. 
  intros. eapply fundamental in H as ST; eauto.
  destruct (ST [] 0 []) as (S' & M' & v & ? & ? & ? & ?).
  eapply envt_empty.
  eapply storet_empty.
  exists S', M', v. intuition.
Qed.

End STLC.
