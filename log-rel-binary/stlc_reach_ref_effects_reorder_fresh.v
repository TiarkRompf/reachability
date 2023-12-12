(* Full safety for STLC *)

(*

BASED ON:

     stlc_reach_ref_effects.v
     stlc_ref_overlap_self_fresh_mut_nested.v (basic st_chain mechanism)
     stlc_reach_ref_effects_reorder_pempty.v (reordering proof for p = empty in tseq)
     stlc_reach_ref_effects_reorder_psep.v (tseq reordering with arbitrary non-overlapping p)
     stlc_reach_ref_overlap_self_fresh_mut.v

THIS FILE:

     - add the fresh marker

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

Definition pl := nat -> Prop.

Definition pempty: pl := fun x => False.                            (* empty set *)

Definition pone (x:nat): pl := fun x' => x' = x.                    (* singleton set *)

Definition pand p1 p2 (x:nat) := p1 x /\ p2 x.                      (* intersection *)

Definition por p1 p2 (x:nat) := p1 x \/ p2 x.                       (* union *)

Definition pnot p1 (x:nat) := ~ p1 x.                               (* complement *)

Definition pdiff p1 p2 (x:nat) := p1 x /\ ~ p2 x.                   (* difference *)

Definition pdom {X} (H: list X) := fun x' =>  x' < (length H).      (* domain of a list *)

Definition pnat n := fun x' =>  x' < n.                             (* smaller than n *)

Definition pif (b:bool) p (x:nat) := if b then p x else False.      (* conditional *)

Definition psub (p1 p2: pl): Prop := forall x:nat, p1 x -> p2 x.    (* subset inclusion *)

Definition plift (b: ql): pl := fun x => b x = true.                (* reflect nat->bool set *)

(* ---------- language syntax ---------- *)

Definition id := nat.

(* qualifiers:
   - expression type:   vars from env, may be fresh
   - function res type: from func, from arg, fresh
   - function arg type: overlap with function, may be fresh
*)



Inductive ty : Type :=
  | TBool  : ty
  | TRef   : ty -> ty
  | TFun   : ty -> bool -> ty -> bool ->ql -> ql -> ty
.

(* TFun
        T1      : argument type

        q1fr    : argument may be fresh?
        q1      : argument reachability qualifer (set of variables)

        T2      : result type

        q2fr    : result may be fresh?
        q2      : result reachability qualifer (set of variables)
        e2      : effects (set of variables)

*)

Inductive tm : Type :=
  | ttrue : tm
  | tfalse : tm
  | tvar : id -> tm
  | tref : tm -> tm
  | tget : tm -> tm
  | tput : tm -> tm -> tm  
  | tapp : tm -> tm -> tm (* f(x) *)
  | tabs : ql -> tm -> tm (* \f x.t *)   (* XXX: record free vars *)
  | tseq : tm -> tm -> tm
.


Inductive vl : Type :=
  | vbool : bool -> vl
  | vref  : id -> vl
  | vabs  : list vl -> ql -> tm -> vl    (* closure record  *)
                                         (* XX: record free vars *)
.

Definition venv := list vl.
Definition tenv := list (ty * bool).

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
| c_fun: forall m T1 T2 fr1 fr2 q2 e2,
    closed_ty m T1 ->
    closed_ty m T2 ->   (* not dependent *)
    closed_ql m q2 ->
    closed_ql m e2 ->   
    closed_ty m (TFun T1 fr1 (* qempty *) T2 fr2 q2 e2)
.


(* assume no overlap *)
Inductive has_type : tenv -> tm -> ty -> ql -> bool -> ql -> ql -> Prop :=
| t_true: forall env p,
    has_type env ttrue TBool p false qempty  qempty    (* nothing reachable from a primitive *)
| t_false: forall env p,
    has_type env tfalse TBool p false qempty qempty
| t_var: forall x env T p fr,
    indexr x env = Some (T, fr) ->
    (plift p) x ->                         (* x in phi *)
    has_type env (tvar x) T p false (qone x) qempty  (* x can reach only itself (no overlap) *)
| t_ref: forall t env p fr q e,
    has_type env t TBool p fr q e ->
    has_type env (tref t) (TRef TBool) p true q e
| t_get: forall t env p fr q e,
    has_type env t (TRef TBool) p fr q e ->
    has_type env (tget t) TBool p false qempty (qor e q)
| t_put: forall t1 t2 env p fr1 q1 e1 fr2 q2 e2,
    has_type env t1 (TRef TBool) p fr1 q1 e1 ->
    has_type env t2 TBool p fr2 q2 e2 ->
    has_type env (tput t1 t2) TBool p false qempty (qor e1 (qor e2 q1))
| t_app: forall env f t T1 T2 p fr1  frf qf frx q1 fr2 q2 ef e1 e2,
    has_type env f (TFun T1 fr1 (* qempty  *) T2 fr2 q2 e2) p frf qf ef ->  
    has_type env t T1 p frx q1 e1 ->
    (*---- different app cases: *)
    (*(if fr1 then 
      psub (pand (plift qf) (plift q1)) pempty
     else 
      True ) ->
    (* else 
      frx = false /\ psub (plift q1) pempty) ->   (* ??? *)*) *)
    (*-------*)  
    psub (pand (plift qf) (plift q1)) pempty ->  (* no overlapping *)
    psub (plift q2) (plift p) ->
    psub (plift e2) (plift p) ->
    has_type env (tapp f t) T2 p (frf||frx||fr2) (qor q2 q1) (qor ef (qor e1 e2))
| t_abs: forall env t T1 fr1 T2 p fr2 q2 qf e2,      (* assume argument is tracked *)
    has_type ((T1, fr1)::env) t T2 (qor (qand p qf) (qone (length env))) fr2 (qor q2 (qone (length env))) (qor e2 (qone (length env))) ->
    closed_ty (length env) T1 ->
    closed_ty (length env) T2 ->
    closed_ql (length env) q2 ->
    closed_ql (length env) qf ->
    closed_ql (length env) e2 ->
    has_type env (tabs (qand p qf) t) (TFun T1 fr1 T2 fr2 q2 e2) p true qf qempty
| t_seq: forall env t1 t2 p1 p2 p q1 q2 e1 e2,
    (* for now, require empty p for both exprs *)
    has_type env t1 TBool p1 false q1 e1 ->
    has_type env t2 TBool p2 false q2 e2 ->
    psub (pand (plift p1) (plift p2)) pempty ->          (* no overlapping *)
    psub (plift p1) (plift p) ->
    psub (plift p2) (plift p) ->
    has_type env (tseq t1 t2) TBool p false qempty (qor e1 (qor e2 q1))
| t_sub: forall env y T p fr1 q1 fr2 q2 e1 e2,
    has_type env y T p fr1 q1 e1 ->
    psub (plift q1) (plift q2) ->
    psub (plift q2) (pdom env)  ->
    psub (plift e1) (plift e2) ->
    psub (plift e2) (pdom env)  ->
    has_type env y T p (fr1 || fr2) q2 e2
.


(* ---------- logical relation ---------- *)

(* mapping values and variables to store locations *)

Fixpoint val_locs_fix (v: vl) (l: nat): bool :=
  match v with
  | vbool  _ => false
  | vref x   => x =? l
  | vabs H q t  =>
      (* alternative: use indexr x, for x < length H *)
      let fix vars_locs_fix (H: list vl) :=
        match H with
        | v :: H => (q (length H) && val_locs_fix v l) || vars_locs_fix H
        | [] => false
        end
      in vars_locs_fix H
  end.

Definition loc_locs (S: stor) (l: nat) (l': nat): bool :=
  match indexr l S with
  | Some v => val_locs_fix v l'
  | None => false
  end.



Fixpoint val_locs_n_fix n (S: stor) (v: vl) (l: nat): bool :=
  match n with
  | S n =>
      let fix vals_locs_fix (S: stor) :=
        match S with
        | v :: S' => val_locs_fix v (length S') && val_locs_n_fix n S v l
                     || vals_locs_fix S'
        | [] => false
        end
      in
      vals_locs_fix S
  | 0 => val_locs_fix v l
  end.


Fixpoint val_locs_trans (S: stor) (v: vl) (l: nat): bool :=
  let fix iter n :=
    match n with
    | S n' => val_locs_n_fix n S v l || iter n'
    | 0 => val_locs_n_fix 0 S v l
    end
  in iter (length S).

Fixpoint vars_locs_fix (H: venv) (q: ql) (l: nat): bool :=
  match H with
  | v :: H => (q (length H) && val_locs_fix v l) || vars_locs_fix H q l
  | [] => false
 end.

Definition val_locs v := plift (val_locs_fix v). 

Definition var_locs E x l := exists vx, indexr x E = Some vx /\ val_locs vx l.

Definition vars_locs E q l := exists x, q x /\ var_locs E x l.

(*----------- val_locs lemmas   -----------*)

Lemma val_locs_bool: forall b,
    val_locs (vbool b) = pempty.
Proof.
  intros. eapply functional_extensionality.
  intros. eapply propositional_extensionality.
  intuition.
Qed.

Lemma val_locs_ref: forall x,    
    val_locs (vref x) = pone x.
Proof.
  intros. eapply functional_extensionality.
  intros. eapply propositional_extensionality.
  unfold val_locs, qone, pone, plift in *. simpl in *. unfold qone. 
  bdestruct (x =? x0); intuition. 
Qed.

Lemma val_locs_abs: forall H p t,
    val_locs (vabs H p t) = vars_locs H (plift p).
Proof.
  intros. eapply functional_extensionality.
  intros. eapply propositional_extensionality.
  unfold val_locs, plift in *. 
  intuition.
  - simpl in H0.
  induction H. intuition.
  remember (p (length H)) as b1.
  remember (val_locs_fix a x) as b2.
  destruct b1. destruct b2. simpl in *.
  (* both true *)
  exists (length H). split. eauto. 
  exists a. rewrite indexr_head. intuition.
  unfold val_locs, plift. intuition.
  (* one false *)
  simpl in *. eapply IHlist in H0.
  destruct H0. exists x0. intuition.
  destruct H2. exists x1. rewrite indexr_extend1 in H0. intuition eauto.
  (* other false *)
  simpl in *. eapply IHlist in H0.
  destruct H0. exists x0. intuition.
  destruct H2. exists x1. rewrite indexr_extend1 in H0. intuition eauto.
  - simpl. destruct H0 as [? [? ?]]. destruct H1 as [? [? ?]].
    unfold indexr in H1. induction H.
    congruence.
    bdestruct (x0 =? length H).
    inversion H1. subst. rewrite H0.
    unfold val_locs, plift in H2. rewrite H2. simpl. eauto.
    rewrite IHlist.
    destruct (p (length H) && val_locs_fix a x); simpl; eauto.
    eauto. 
Qed.

Lemma val_locs_decide: forall v l,
    val_locs v l \/ ~ val_locs v l.
Proof.
  intros. unfold val_locs, plift.
  destruct (val_locs_fix v l); eauto.
Qed.

Lemma var_locs_decide: forall H x l, (* not used *)
    var_locs H x l \/ ~ var_locs H x l.
Proof.
  intros. unfold var_locs, plift.
  bdestruct (x <? length H).
  - assert (exists vx : vl, indexr x H = Some vx).
    eapply indexr_var_some. eauto.
    destruct H1. destruct (val_locs_decide x0 l).
    left. eauto.
    right. intros ?. eapply H2. destruct H3. destruct H3. congruence.
  - right. intros ?. destruct H1. destruct H1. eapply indexr_var_some' in H1. lia. 
Qed.


Lemma plift_vars_locs: forall H q,
    vars_locs H (plift q) = plift (vars_locs_fix H q).
Proof.
  intros. eapply functional_extensionality.
  intros. eapply propositional_extensionality.
  unfold vars_locs, var_locs, val_locs, plift in *.
  intuition.
  - simpl. destruct H0 as [? [? ?]]. destruct H1 as [? [? ?]].
    unfold indexr in H1. induction H.
    congruence. 
    bdestruct (x0 =? length H).
    inversion H1. subst. simpl. rewrite H0.
    unfold val_locs, plift in H2. rewrite H2. simpl. eauto.
    simpl. rewrite IHlist.
    destruct (q (length H) && val_locs_fix a x); simpl; eauto.
    eauto. 
  - induction H. intuition.
    remember (q (length H)) as b1.
    remember (val_locs_fix a x) as b2.
    destruct b1. destruct b2. simpl in H0.
    (* both true *)
    exists (length H). split. eauto.
    exists a. rewrite indexr_head. intuition.
    (* one false *)
    simpl in H0. rewrite <-Heqb1, <-Heqb2 in H0. simpl in H0. eapply IHlist in H0.
    destruct H0. exists x0. intuition.
    destruct H2. exists x1. rewrite indexr_extend1 in H0. intuition eauto.
    (* other false *)
    simpl in H0. rewrite <-Heqb1 in H0. simpl in H0. eapply IHlist in H0. 
    destruct H0. exists x0. intuition.
    destruct H2. exists x1. rewrite indexr_extend1 in H0. intuition eauto.
Qed.

Lemma vars_locs_decide: forall H p l,
    vars_locs H (plift p) l \/ ~ vars_locs H (plift p) l.
Proof.
  intros.
  rewrite plift_vars_locs. unfold plift. destruct (vars_locs_fix H p l); intuition. 
Qed.
  
Lemma vars_locs_sub: forall H p1 p2 l,
  vars_locs H p1 l ->
  psub p1 p2 ->
  vars_locs H p2 l.
Proof.
  intros. unfold vars_locs in *. unfold psub in H1.
  destruct H0 as (? & ? & ?). exists x; intuition.
Qed.


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
            | (M', None) => (M', None)
            | (M', Some None) => (M', Some None)
            | (M', Some (Some (vbool _))) => (M', Some None)
            | (M', Some (Some (vabs _ _ _))) => (M', Some None)
            | (M', Some (Some (vref x))) => (M', Some (indexr x M'))
          end
        | tput er ex    =>
          match teval n M env er with
            | (M', None) => (M', None)
            | (M', Some None) => (M', Some None)
            | (M', Some (Some (vbool _))) => (M', Some None)
            | (M', Some (Some (vabs _ _ _))) => (M', Some None)
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
        | tseq e1 e2   =>
            match teval n M env e1 with
            | (M', None) => (M', None)
            | (M', Some None) => (M', Some None)
            | (M', Some (Some (vbool b1))) => 
                match teval n M' env e2 with
                | (M'', None) => (M'', None)
                | (M'', Some None) => (M'', Some None)
                | (M'', Some (Some (vbool b2))) => (M'', Some (Some (vbool (b1 && b2))))
                | (M'', Some (Some (vref _))) => (M'', Some None)
                | (M'', Some (Some (vabs _ _ _))) => (M'', Some None)
                end
            | (M', Some (Some (vref _))) => (M', Some None)
            | (M', Some (Some (vabs _ _ _))) => (M', Some None)
            end
        | tabs p y     => (M, Some (Some (vabs env p y)))
        | tapp ef ex =>
          match teval n M env ef with
            | (M', None) => (M', None)
            | (M', Some None) => (M', Some None)
            | (M', Some (Some (vbool _))) => (M', Some None)
            | (M', Some (Some (vref _))) => (M', Some None)
            | (M', Some (Some (vabs env2 _ ey))) =>
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



Lemma store_grows: forall n M env t M' R, 
  teval n M env t = (M', R) ->
  length M <= length M'.
Proof.
  intros n. induction n; intros.  
  simpl in H. inversion H. lia.
  destruct t; simpl in H.
  + inversion H. lia.
  + inversion H. lia.
  + inversion H. lia.
  + remember (teval n M env t) as TT.  symmetry in HeqTT.  destruct TT. 
    eapply IHn in HeqTT.  destruct o. destruct o.
    all: inversion H; simpl in *; subst; auto.     
  + remember (teval n M env t) as TT.  symmetry in HeqTT.  destruct TT. 
    eapply IHn in HeqTT.  destruct o. destruct o. destruct v.
    all: inversion H; simpl in *; subst; auto.
  + remember (teval n M env t1) as TT1.  symmetry in HeqTT1.  destruct TT1. 
    eapply IHn in HeqTT1.  destruct o. destruct o. destruct v.
    all: inversion H; simpl in *; subst; auto.
    remember (teval n s env t2) as TT2.  symmetry in HeqTT2.  destruct TT2.
    eapply IHn in HeqTT2.  destruct o. destruct o. destruct (indexr i s0).
    all: inversion H; simpl in *; subst; auto; try rewrite <- update_length; lia.  
  + remember (teval n M env t1) as TT1.  symmetry in HeqTT1.  destruct TT1. 
    eapply IHn in HeqTT1.  destruct o. destruct o. destruct v.
    all: inversion H; simpl in *; subst; auto.
    remember (teval n s env t2) as TT2.  symmetry in HeqTT2.  destruct TT2.
    eapply IHn in HeqTT2.  destruct o. destruct o. 
    eapply IHn in H. lia.
    all: inversion H; simpl in *; subst; auto; lia.
  + inversion H. auto.
  + remember (teval n M env t1) as TT1.  symmetry in HeqTT1.  destruct TT1. 
    eapply IHn in HeqTT1.  destruct o. destruct o. destruct v.
    all: inversion H; simpl in *; subst; auto.
    remember (teval n s env t2) as TT2.  symmetry in HeqTT2.  destruct TT2.
    eapply IHn in HeqTT2.  destruct o. destruct o. destruct v. 
    all: inversion H; simpl in *; subst; auto; lia.
Qed.



(* store typings / "worlds" *)

(* consists of:

    - length of S1
    - length of S2
    - binary relation between locations that
      are supposed to be equivalent

   we enforce that this relation is a partial bijection
*)

Definition stty: Type := (nat * nat * (nat -> nat -> Prop)).

Definition length1 (M: stty) := fst (fst M).
Definition length2 (M: stty) := snd (fst M).
Definition strel (M: stty) := snd M.

Definition store_type (S1 S2: stor) (M: stty) := 
  length S1 = length1 M /\
  length S2 = length2 M /\
    (forall l1 l2 ,
      strel M l1 l2 ->
      exists b1 b2, 
      indexr l1 S1 = Some (vbool b1) /\
      indexr l2 S2 = Some (vbool b2) /\
      b1 = b2) /\
    (* enforce that strel is a partial bijection *)
    (forall l1 l2 l2',
        strel M l1 l2 ->
        strel M l1 l2' ->
        l2 = l2') /\
    (forall l1 l1' l2,
        strel M l1 l2 ->
        strel M l1' l2 ->
        l1 = l1').

Definition st_locs1 (M: stty) := (pnat (length1 M)).
Definition st_locs2 (M: stty) := (pnat (length2 M)).


(* store typing/world extension -- monotonic *)
Definition st_chain_partial (M:stty) (M1:stty) (p1:pl) (p2:pl) :=
  psub p1 (st_locs1 M) /\
  psub p1 (st_locs1 M1) /\
  psub p2 (st_locs2 M) /\
  psub p2 (st_locs2 M1) /\
  forall l1 l2,
    p1 l1 /\ p2 l2 ->
    strel M l1 l2 ->
    strel M1 l1 l2.

Definition st_chain_partial2 (M:stty) (M1:stty) (p1:pl) (p2:pl) :=
  psub p1 (st_locs1 M) /\
  psub p1 (st_locs1 M1) /\
  psub p2 (st_locs2 M) /\
  psub p2 (st_locs2 M1) /\
  forall l1 l2,
    p1 l1 \/ p2 l2 ->
    strel M l1 l2 ->
    strel M1 l1 l2.

Definition st_chain (M:stty) (M1:stty) :=
  st_chain_partial M M1 (st_locs1 M) (st_locs2 M) /\
    st_chain_partial2 M1 M (st_locs1 M) (st_locs2 M).
    


Definition st_extend (M:stty) :=
  (1 + length1 M,
    1 + length2 M,
    fun l1 l2 => l1 = length1 M /\ l2 = length2 M \/ strel M l1 l2).


#[global] Hint Unfold length1.
#[global] Hint Unfold length2.


(* store typing chain *)

Lemma st_mono1: forall M M',
  st_chain M M' ->
  length1 M <= length1 M'.
Proof.
  intros. unfold st_chain, st_chain_partial in H. intuition.
  unfold st_locs1, psub, pnat in *. intuition.
  destruct (length1 M). lia. eapply H0. lia. 
Qed.

Lemma st_mono2: forall M M',
  st_chain M M' ->
  length2 M <= length2 M'.
Proof.
  intros. unfold st_chain, st_chain_partial, st_chain_partial2 in H. intuition.
  unfold st_locs2, psub, pnat in *. intuition.
  destruct (length2 M). lia. eapply H5. lia.
Qed.

Lemma st_mono1': forall M M' l,
  st_chain M M' ->
  l < length1 M ->
  l < length1 M'.
Proof.
  intros. assert (length1 M <= length1 M'). eapply st_mono1; eauto. lia.
Qed.

Lemma st_mono2': forall M M' l,
  st_chain M M' ->
  l < length2 M ->
  l < length2 M'.
Proof.
  intros. assert (length2 M <= length2 M'). eapply st_mono2; eauto. lia.
Qed.


Lemma st_refl: forall M1,
    st_chain M1 M1.
Proof.
  intros. repeat split.
  intros ? ?. eauto.
  intros ? ?. eauto.
  intros ? ?. eauto.
  intros ? ?. eauto.
  intuition. 
  intros ? ?. eauto.
  intros ? ?. eauto.
  intros ? ?. eauto.
  intros ? ?. eauto.
  intuition. 
Qed.

Lemma st_trans: forall M1 M2 M3,
    st_chain M1 M2 ->
    st_chain M2 M3 ->
    st_chain M1 M3.
Proof.
  intros. unfold st_chain, st_chain_partial, st_chain_partial2, strel in *.
  intuition. 
  intros ? ?. unfold st_locs1, pnat, psub in *.  intuition. 
  intros ? ?. unfold st_locs2, pnat, psub in *.  intuition. 
  intros ? ?. unfold st_locs1, pnat, psub in *.  intuition.
  intros ? ?. unfold st_locs2, pnat, psub in *.  intuition.
Qed.

Lemma st_trans': forall M1 M2 M3 p1 p2,
    st_chain M1 M2 ->
    psub p1 (st_locs1 M1) ->
    psub p2 (st_locs2 M1) ->
    st_chain_partial M2 M3 p1 p2 ->
    st_chain_partial M1 M3 p1 p2.
Proof.
  intros. unfold st_chain, st_chain_partial, strel in *.
  intuition.
Qed.

Lemma st_trans'': forall M1 M2 M3 p1 p2,
    st_chain_partial M1 M2 p1 p2 ->
    st_chain_partial M2 M3 p1 p2 ->
    psub p1 (st_locs1 M1) ->
    psub p2 (st_locs2 M1) ->
    st_chain_partial M1 M3 p1 p2.
Proof.
  intros. unfold st_chain, st_chain_partial, strel in *.
  intuition.
Qed.

Lemma st_trans2'': forall M1 M2 M3 p1 p2,
    st_chain_partial2 M1 M2 p1 p2 ->
    st_chain_partial2 M2 M3 p1 p2 ->
    psub p1 (st_locs1 M3) ->
    psub p2 (st_locs2 M3) ->
    st_chain_partial2 M1 M3 p1 p2.
Proof.
  intros. unfold st_chain_partial2, strel in *.
  intuition.
Qed.

Lemma stchain_tighten: forall M1 M2 p1 p2 p1' p2',
    st_chain_partial M1 M2 p1 p2 ->
    psub p1' p1 ->
    psub p2' p2 -> 
    st_chain_partial M1 M2 p1' p2'.
Proof.
  intros. unfold st_extend, st_chain, st_chain_partial, strel in *. 
  simpl. intuition.
  intros ? ?. eauto.
  intros ? ?. eauto. 
  intros ? ?. eauto.
  intros ? ?. eauto.
Qed.

Lemma stchain_tighten': forall M1 M2 p1 p2 p1' p2',
    st_chain_partial2 M1 M2 p1 p2 ->
    psub p1' p1 ->
    psub p2' p2 -> 
    st_chain_partial2 M1 M2 p1' p2'.
Proof.
  intros. unfold st_extend, st_chain, st_chain_partial2, strel in *. 
  simpl. intuition.
  intros ? ?. eauto.
  intros ? ?. eauto. 
  intros ? ?. eauto.
  intros ? ?. eauto. 
Qed.


Lemma stchain_extend: forall M1,
    st_chain M1 (st_extend M1).
Proof.
  intros. unfold st_extend, st_chain, st_chain_partial, st_chain_partial2, strel. 
  simpl. intuition.
  intros ? ?. eauto.
  intros ? ?. eauto.
  unfold st_locs1, pnat, length1 in *. simpl. lia.
  intros ? ?. eauto.
  intros ? ?. unfold st_locs2, length1, length2, pnat in *. simpl. auto.
  intros ? ?. unfold st_locs1, pnat, length1 in *. simpl. lia.
  intros ? ?. eauto.
  intros ? ?. unfold st_locs2, length1, length2, pnat in *. simpl. auto.
  intros ? ?. auto.
  unfold st_locs1, pnat, length1 in *. lia.
  unfold st_locs2, pnat, length2 in *. lia.
Qed.


Lemma strel_mono: forall M M' i i0,
  st_chain M M' ->
  st_locs1 M i ->
  st_locs2 M i0 ->
  strel M i i0 ->
  strel M' i i0.
Proof.
  intros. unfold st_chain, st_chain_partial in H.
  intuition.
Qed.


(* store preservation invariant *)

Definition store_effect (S S1: stor) (p: pl) :=
  forall l v,
    ~ p l -> 
    indexr l S = Some v ->
    indexr l S1 = Some v.
    



(* value interpretation of types *)

Fixpoint val_type (M:stty) (H1 H2:venv) v1 v2 T1 T2 : Prop :=
  match v1, v2, T1, T2 with
  | vbool b1, vbool b2, TBool, TBool =>
      b1 = b2
  | vref l1, vref l2, TRef T, TRef T' => 
      T = TBool /\ T' = TBool /\
      l1 < length1 M /\ l2 < length2 M /\ strel M l1 l2
  | vabs G1 py1 ty1, vabs G2 py2 ty2, TFun T1 fr1 (* qempty *) T2 fr2 q2 e2, TFun T1' fr1'(* qempty *) T2' fr2' q2' e2' =>
        closed_ty (length H1) T1 /\
        closed_ty (length H1) T2 /\
        closed_ty (length H2) T1' /\
        closed_ty (length H2) T2' /\
        (psub (plift q2) (pdom H1)) /\
        (psub (plift q2') (pdom H2)) /\
        (psub (plift e2) (pdom H1)) /\
        (psub (plift e2') (pdom H2)) /\
        (psub (val_locs v1) (pnat (length1 M))) /\
        (psub (val_locs v2) (pnat (length2 M))) /\
        (forall l1 l2, strel M l1 l2 -> val_locs v1 l1 <-> val_locs v2 l2) /\  (* A *)
        (forall S1' S2' M' vx1 vx2,
            st_chain_partial M M' (val_locs v1) (val_locs v2)
            -> 
            st_chain_partial2 M' M (val_locs v1) (val_locs v2) (* needed for A ! *)
            ->    
            store_type S1' S2' M'
            ->
            val_type
              M'
              H1
              H2
              vx1
              vx2
              T1
              T1'
            ->
              psub (pand (val_locs v1) (val_locs vx1)) pempty ->
              psub (pand (val_locs v2) (val_locs vx2)) pempty
            ->
              exists S1'' S2'' M'' vy1 vy2,
                tevaln
                  S1'
                  (vx1::G1)
                  ty1
                  S1''
                  vy1
                /\
                tevaln
                  S2'
                  (vx2::G2)
                  ty2
                  S2''
                  vy2
                /\
                  st_chain M' M''
                /\
                  store_type S1'' S2'' M''
                /\
                  store_effect S1' S1'' (por (val_locs v1) (val_locs vx1))
                /\
                  store_effect S2' S2'' (por (val_locs v2) (val_locs vx2))
                /\
                  val_type
                    M''
                    H1
                    H2
                    vy1 
                    vy2
                    T2
                    T2'
                /\
                   psub
                    (val_locs vy1)
                    (por (pand (vars_locs H1 (plift q2)) (val_locs v1)) 
                      (por (val_locs vx1)
                        (pif fr2 (pdiff (pnat (length1 M'')) (pnat (length1 M'))))))
                /\
                  psub
                    (val_locs vy2)
                    (por (pand (vars_locs H2 (plift q2')) (val_locs v2)) 
                      (por (val_locs vx2)
                           (pif fr2 (pdiff (pnat (length2 M'')) (pnat (length2 M')))))))
  | _,_,_,_ =>
      False
  end.


Definition val_qual (N N1: nat) H v fr (q: pl) :=
  psub (val_locs v)
    (por (vars_locs H q)
      (pif fr (pdiff (pnat N1) (pnat N))))  .


Definition exp_type S1 S2 M H1 H2 t1 t2 S1' S2' M' v1 v2 T p  fr q (e: pl) :=
  tevaln S1 H1 t1 S1' v1 /\
  tevaln S2 H2 t2 S2' v2 /\
    st_chain M M' /\
    store_type S1' S2' M' /\
    store_effect S1 S1' (vars_locs H1 p) /\
    store_effect S2 S2' (vars_locs H2 p) /\
    val_type M' H1 H2 v1 v2 T T /\
    val_qual (length1 M)(length1 M') H1 v1 fr (pand p q) /\
    val_qual (length2 M)(length2 M') H2 v2 fr (pand p q).


Definition env_type M H1 H2 G p :=
  length H1 = length G /\
  length H2 = length G /\
    psub p (pdom H1) /\
    psub p (pdom H2) /\
    (forall x T (fr:bool),
        indexr x G = Some (T, fr) ->
        p x ->
        exists v1 v2 : vl,
          indexr x H1 = Some v1 /\
          indexr x H2 = Some v2 /\
          val_type M H1 H2 v1 v2 T T ) /\
          (*(fr = false -> psub (val_locs v1) pempty) /\
          (fr = false -> psub (val_locs v2) pempty)) /\*)
    (forall l x0 x1,
        p x0 ->
        var_locs H1 x0 l ->
        p x1 ->
        var_locs H1 x1 l ->
        x0 = x1) /\
    (forall l x0 x1,
        p x0 ->
        var_locs H2 x0 l ->
        p x1 ->
        var_locs H2 x1 l ->
        x0 = x1)
.



#[export] Hint Constructors ty: core.
#[export] Hint Constructors tm: core.
#[export] Hint Constructors vl: cor.


#[export] Hint Constructors has_type: core.

#[export] Hint Constructors option: core.
#[export] Hint Constructors list: core.

Lemma tevaln_unique: forall S S' S'' H e v v',
    tevaln S H e S' v ->
    tevaln S H e S'' v' ->
    v = v' /\ S' = S''.
Proof.
  intros.
  destruct H0 as [n1 ?].
  destruct H1 as [n2 ?].
  assert (1+n1+n2 > n1) as A1. lia.
  assert (1+n1+n2 > n2) as A2. lia.
  specialize (H0 _ A1).
  specialize (H1 _ A2).
  rewrite H0 in H1. inversion H1. intuition.
Qed.



(* ---------- qualifier reflection & tactics  ---------- *)


Ltac unfoldq := unfold val_qual, psub, pdom, pnat, pdiff, pnot, pif, pand, por, pempty, pone, var_locs, vars_locs in *.
Ltac unfoldq1 := unfold qsub, qdom, qand, qempty, qone in *.

(* general reflection proof principle *)
Lemma plift_qual_eq: forall q1 q2,
    (q1 = q2) = (plift q1 = plift q2).
  intros. eapply propositional_extensionality.
  remember (plift q1) as p1.
  remember (plift q2) as p2. 
  unfold plift in *. intuition.
  - subst. eauto.
  - eapply functional_extensionality. intros.
    remember (q1 x) as qx1. symmetry in Heqqx1.
    remember (q2 x) as qx2. symmetry in Heqqx2.
    destruct qx1; destruct qx2; try reflexivity.
    + replace (q1 x = true) with (p1 x) in *.
      rewrite H in Heqqx1. subst p2. eauto. subst p1. eauto. 
    + replace (q2 x = true) with (p2 x) in *. 
      rewrite <-H in Heqqx2. subst p1. eauto. subst p2. eauto.
Qed.

Lemma plift_empty: 
    plift (qempty) = pempty.
Proof.
  intros. unfoldq. unfold plift.
  eapply functional_extensionality. intros.
  eapply propositional_extensionality. 
  bdestruct (qempty x); intuition. 
  lia. Unshelve. apply 0.  
Qed.

Lemma plift_one: forall x,
    plift (qone x) = pone x.
Proof.
  intros. unfoldq. unfold plift.
  eapply functional_extensionality. intros.
  eapply propositional_extensionality. 
  bdestruct (qone x x0); intuition.
Qed.

Lemma plift_and: forall a b,
    plift (qand a b) = pand (plift a) (plift b).
Proof.
  intros. unfoldq. unfold plift.
  eapply functional_extensionality. intros.
  eapply propositional_extensionality. 
  bdestruct (qand a b x); intuition.
Qed.

Lemma plift_or: forall a b,
    plift (qor a b) = por (plift a) (plift b).
Proof.
  intros. unfoldq. unfold plift.
  eapply functional_extensionality. intros.
  eapply propositional_extensionality. 
  bdestruct (qor a b x); intuition.
Qed.

Lemma plift_if1: forall a b (c: bool),
    plift (if c then a else b) = if c then plift a else plift b.
Proof.
  intros. unfoldq. unfold plift.
  eapply functional_extensionality. intros.
  eapply propositional_extensionality.
  destruct c; intuition.
Qed.

Lemma plift_diff: forall a b,
    plift (qdiff a b) = pdiff (plift a) (plift b).
Proof.
  intros. unfoldq. unfold plift.
  eapply functional_extensionality. intros.
  eapply propositional_extensionality.
  unfold qdiff. destruct (a x); destruct (b x); intuition. 
Qed.

Lemma pand_or_distribute: forall p q s, 
  pand s (por p q)  = (por (pand s p) (pand s q)).
Proof.
  intros. unfoldq.  eapply functional_extensionality. intros.
  eapply propositional_extensionality. split; intros; intuition.
Qed.


Lemma pand_or_distribute2: forall p q s, 
  pand s (por (plift p) q)  = (por (pand s  (plift p)) (pand s q)).
Proof.
  intros. unfoldq. unfold plift. eapply functional_extensionality. intros.
  eapply propositional_extensionality. split; intros; intuition.
Qed.

Lemma pand_empty_l: forall p,
  pand pempty p = pempty.
Proof.
  intros. eapply functional_extensionality. intros.
  eapply propositional_extensionality; intuition.
  unfoldq; intuition. 
Qed.


Lemma por_empty_r: forall p,
  por p pempty = p.
Proof.
  intros. eapply functional_extensionality. intros.
  eapply propositional_extensionality; intuition.
  unfoldq; intuition. unfoldq; intuition. 
Qed.


(* ---------- closedness lemmas  ---------- *)

Lemma closedq_extend : forall {m q}, closed_ql m q -> 
  forall {m'}, m <= m' -> closed_ql m' q.
Proof.  
    intros. unfold closed_ql in *. intros. 
    specialize (H x). intuition.
Qed.

Lemma closedq_sub : forall {m q q'}, closed_ql m q' -> 
  psub (plift q) (plift q') -> closed_ql m q.
Proof.  
    intros. unfold closed_ql in *. intros. unfoldq; intuition. 
    specialize (H0 x). intuition.
Qed.

Lemma closedq_or: forall q1 q2 m,
  closed_ql m (qor q1 q2)  <->
  (closed_ql m q1 /\ closed_ql m q2).
Proof.
  intros. split; intros.
  - unfold closed_ql in *. split; intros.
    1,2: destruct (H x); intuition; bdestruct (qor q1 q2 x); intuition.
  - intuition. unfold closed_ql in *. intros. 
    bdestruct (qor q1 q2 x); intuition.
Qed.

Lemma  closedq_and: forall q1 q2 m,
  (closed_ql m q1 \/ closed_ql m q2) -> 
  closed_ql m (qand q1 q2).
Proof.
  intros. destruct H; unfold closed_ql in *; intros;
  bdestruct (qand q1 q2 x); intuition.
Qed.

Lemma closedq_one: forall m x,
  x < m ->
  closed_ql m (qone x).
Proof.
  intros. unfold closed_ql. intros.
  unfoldq1; intuition. apply Nat.eqb_eq in H0. subst. auto.
Qed.


Lemma closedql_empty: forall m,
  closed_ql m qempty.
Proof. 
  intros. unfold closed_ql. intros.
  unfoldq; intuition.
Qed.
#[global] Hint Resolve closedql_empty : core.

Lemma closedty_extend : forall {m T}, closed_ty m T -> 
  forall {m'}, m <= m' -> closed_ty m' T.
Proof. 
    intros. induction T; constructor.
    all: inversion H; subst; intuition.
    eapply closedq_extend; eauto.
    eapply closedq_extend; eauto.
Qed.


Lemma closedty_TBool: forall m, closed_ty m TBool.
Proof.
  intros. constructor.
Qed.
#[global] Hint Resolve closedty_TBool : core.

Lemma closedty_TRef: forall m T, 
  closed_ty m T ->
  closed_ty m (TRef T).
Proof.
  intros. constructor. auto.
Qed.
#[global] Hint Resolve closedty_TRef : core.


Lemma filter_closed: forall M H1 H2 G p,
  env_type M H1 H2 G (plift p) ->
  closed_ql (length G) p.
Proof.
  intros. destruct H as [L1 [L2 [P1 [P2 P3]]]].
  unfold closed_ql. intros.
  unfoldq; intuition. eapply P1 in H.  rewrite L1 in H. auto.
Qed.

Lemma valt_closed: forall T T' M H1 H2 v1 v2,
    val_type M H1 H2 v1 v2 T T' ->
    ( closed_ty (length H1) T /\
      closed_ty (length H2) T') .
Proof. 
  intros T. induction T; intros; destruct T'; destruct v1; destruct v2; simpl in *; intuition.
  + subst. econstructor. auto. 
  + subst. econstructor; eauto.
  + subst. econstructor; eauto. 
  + subst. econstructor; eauto.
Qed.



Lemma vars_locs_extend: forall H H' q,
    psub q (pdom H) ->
    vars_locs (H' ++ H) q = 
      vars_locs H q.
Proof. 
  intros. apply functional_extensionality.
  intros. apply propositional_extensionality.
  unfoldq. unfoldq. intuition.
  - destruct H1. exists x0. intuition.
    destruct H3. exists x1. intuition.
    eapply indexr_extend; eauto.
  - destruct H1. exists x0. intuition.
    destruct H3. exists x1. intuition.
    eapply indexr_extend in H3. eapply H3.
Qed.

Lemma vars_locs_empty: forall H,
  vars_locs H pempty = pempty.
Proof. 
  intros. eapply functional_extensionality.
  intros. eapply propositional_extensionality.
  split; intros. unfoldq; intuition. destruct H0. intuition.
  unfoldq; intuition.
Qed.


(* ---------- val_type lemmas  ---------- *)

Lemma valt_wf: forall T T' M H1 H2 v1 v2,
    val_type M H1 H2 v1 v2 T T' ->
    ( psub (val_locs v1) (pnat (length1 M)) /\
      psub (val_locs v2) (pnat (length2 M))).
Proof. 
  intros T. induction T; intros; destruct T'; destruct v1; destruct v2; simpl in *; intuition.
  + rewrite val_locs_bool. auto. unfoldq. intuition.
  + rewrite val_locs_bool. auto. unfoldq. intuition.
  + rewrite val_locs_ref. unfoldq. intuition.
  + rewrite val_locs_ref. unfoldq. intuition.
Qed.


Lemma valt_store_change: forall T T' M' M H1 H2 v1 v2,
    val_type M H1 H2 v1 v2 T T' ->
    st_chain_partial M M' (val_locs v1) (val_locs v2) ->
    st_chain_partial2 M' M (val_locs v1) (val_locs v2) ->
    val_type M' H1 H2 v1 v2 T T'.
Proof.  
  intros T. induction T; intros; destruct T'; destruct v1; destruct v2; simpl in *; intuition.
  + eapply H0. rewrite val_locs_ref. unfoldq. eauto. 
  + eapply H0. repeat rewrite val_locs_ref. unfoldq. eauto. 
  + eapply H0. repeat rewrite val_locs_ref. unfoldq. eauto. auto.  
  + eapply H0.
  + eapply H0.
  + destruct H0 as (? & ? & ? & ? & ?).
    destruct H3 as (? & ? & ? & ? & ?).
    eapply H13. eapply H24. left. eauto. eauto. eauto.
  + destruct H0 as (? & ? & ? & ? & ?).
    destruct H3 as (? & ? & ? & ? & ?).
    eapply H13. eapply H24. right. eauto. eauto. eauto.
  + destruct (H15 S1' S2' M'0 vx1 vx2) as [S1'' [S2''[M'' [vy1 [vy2  [IEY1 [IEY2 [SEY [HVY [HSEP1 HSEP2]]]]]]]]]].
    eapply st_trans''; eauto. eapply st_trans2''; eauto.  eauto. eauto. eauto. eauto. 
    exists S1'', S2'', M'', vy1, vy2. intuition.
Qed. 

(*
Lemma valt_store_change': forall T T' M' M H1 H2 v1 v2,
    val_type M H1 H2 v1 v2 T T' ->
    st_chain_partial M M' (val_locs v1) (val_locs v2) ->
    st_chain_partial2 M' M (val_locs v1) (val_locs v2) ->
    val_locs v1 = pempty ->
    val_locs v2 = pempty ->
    val_type M' H1 H2 v1 v2 T T'.
Proof.  
  intros T. induction T; intros; destruct T'; destruct v1; destruct v2; simpl in *; intuition.
  + eapply H0. rewrite val_locs_ref. unfoldq. eauto. 
  + eapply H0. repeat rewrite val_locs_ref. unfoldq. eauto. 
  + rewrite val_locs_ref in *. unfoldq; intuition.  
  + destruct H0 as (? & ? & ? & ? & ?).
    destruct H3 as (? & ? & ? & ? & ?).
    eapply H14. eapply H25. left. eauto. eauto. eauto.
  + destruct H0 as (? & ? & ? & ? & ?).
    destruct H3 as (? & ? & ? & ? & ?).
    eapply H14. eapply H25. right. eauto. eauto. eauto.
  + destruct (H16 S1' S2' M'0 vx1 vx2) as [S1'' [S2''[M'' [vy1 [vy2  [IEY1 [IEY2 [SEY [HVY [HSEP1 HSEP2]]]]]]]]]].
    eapply st_trans''; eauto. eapply st_trans2''; eauto. lia. eauto. eauto. eauto. eauto. 
    exists S1'', S2'', M'', vy1, vy2. intuition.
Qed. 
*)

Lemma valt_store_extend: forall T T' M' M H1 H2 v1 v2,
    val_type M H1 H2 v1 v2 T T' ->
    st_chain M M' ->
    val_type M' H1 H2 v1 v2 T T'.
Proof.
  intros. destruct H0 as [? ?].
  eapply valt_store_change. eauto.
  eapply stchain_tighten. eauto.
  eapply valt_wf. eauto.
  eapply valt_wf. eauto.
  eapply stchain_tighten'. eauto.
  eapply valt_wf. eauto.
  eapply valt_wf. eauto.
Qed.

(*
Proof.  
  intros T. induction T; intros; destruct v1; destruct v2; simpl in *; intuition.
  + eapply st_mono1'; eauto. 
  + eapply st_mono2'; eauto. 
  + eapply strel_mono; eauto.
  + intros ? ?. eapply st_mono1'; eauto. eapply H10; eauto.
  + intros ? ?. eapply st_mono2'; eauto. eapply H11; eauto. 
  + destruct (H13 S1' S2' M'0 vx1 vx2) as [S1'' [S2''[M'' [vy1 [vy2  [IEY1 [IEY2 [SEY [HVY [HSEP1 HSEP2]]]]]]]]]].
    eapply st_trans'; eauto. eauto. eauto. eauto. eauto. 
    exists S1'', S2'', M'', vy1, vy2. intuition.
Qed. *)

Lemma valt_extend: forall T T' M H1' H1 H2' H2 v1 v2,
    closed_ty (length H1) T ->
    closed_ty (length H2) T' ->
    val_type M (H1'++H1) (H2'++H2) v1 v2 T T' <-> 
    val_type M H1 H2 v1 v2 T T'.
Proof. 
  intros T. induction T; intros; destruct T'; split; intros; destruct v1; destruct v2; simpl in *; intuition.
  (* - destruct (H8 M' S1 S2 H7) as [v1 [v2 [IS1 [IS2 VT]]]].
    exists v1, v2; intuition. eapply IHT. inversion H.  auto. inversion H0. auto. eapply VT.
  - destruct (H8 M' S1 S2 H7) as [v1 [v2 [IS1 [IS2 VT]]]].
    exists v1, v2; intuition. eapply IHT. inversion H.  auto. inversion H0. auto. eapply VT.
  *)
  - inversion H. auto. 
  - inversion H. auto.
  - inversion H0. auto.
  - inversion H0. auto.
  - inversion H. auto.
  - inversion H0. auto.
  - inversion H. auto.
  - inversion H0. auto.
  - (* Abs shrink *)
    inversion H0. subst. inversion H. subst.
    destruct (H15 S1' S2' M' vx1 vx2) as [S1'' [S2'' [M'' [vy1 [vy2 [HEY HVY]]]]]].
      eauto.
      eauto.
      eauto.
      eapply IHT1; eauto.
      eauto. 
    eauto.
    exists S1'', S2'', M'', vy1, vy2. intuition.
    eapply IHT2; eauto.
    rewrite vars_locs_extend in H32; eauto.
    rewrite vars_locs_extend in H37; eauto.
  - eapply closedty_extend. apply H4. auto.
  - eapply closedty_extend. apply H3. auto.
  - eapply closedty_extend; eauto. 
  - eapply closedty_extend; eauto.
  - unfoldq. rewrite app_length. intuition. eapply H7 in H14. lia.
  - unfoldq. rewrite app_length. intuition. eapply H8 in H14. lia.
  - unfoldq. rewrite app_length. intuition. eapply H9 in H14. lia.
  - unfoldq. rewrite app_length. intuition. eapply H10 in H14. lia.
  - (* Abs grow *)
    inversion H0. subst.
    destruct (H15 S1' S2' M' vx1 vx2) as [S1'' [S2'' [M'' [vy1 [vy2 [HEY [HVY]]]]]]].
      eauto.
      eauto.
      eauto.
      eapply IHT1; eauto.
      eauto.  eauto.
    exists S1'',S2'', M'', vy1, vy2. intuition.
    eapply IHT2; eauto.
    rewrite vars_locs_extend; eauto. 
    rewrite vars_locs_extend; eauto.
Qed.

Lemma valt_extend1: forall T T' M H1 H2 v1 v2 vx1 vx2,
    closed_ty (length H1) T ->
    closed_ty (length H2) T' ->
    val_type M (vx1::H1)(vx2::H2) v1 v2 T T'<-> 
    val_type M H1 H2 v1 v2 T T'.
Proof.
  intros. 
  replace (vx1 :: H1)  with ([vx1]  ++ H1); auto.
  replace (vx2 :: H2)  with ([vx2]  ++ H2); auto.
  eapply valt_extend; eauto.
Qed.


(* ---------- val_qual lemmas  ---------- *)

Lemma valq_bool: forall M M1 H b q,
    val_qual M M1 H (vbool b) false q.
Proof.
  intros. unfoldq. rewrite val_locs_bool. intuition.
Qed.

(*
Lemma valq_fresh1: forall M M' H q,
    st_chain M M' ->
    val_qual (length1 M) (length1 M') H (vref (length1 M')) true q.
Proof.
  intros. unfoldq. eapply st_mono1 in H0.
  (* valq: index out of range*)
  rewrite val_locs_ref.
  intuition. unfoldq. lia.
Qed.

Lemma valq_fresh2: forall M M' H p q,
    st_chain M M' ->
    val_qual (length2 M) H (vref (length2 M')) p q.
Proof.
  intros. unfoldq. eapply st_mono2 in H0.
  (* valq: index out of range*)
  rewrite val_locs_ref.
  intuition. unfoldq. lia.
Qed.
*)

Lemma valq_abs: forall M M' H t p fr q,
    val_qual M M' H (vabs H (qand p q) t) fr (pand (plift p)(plift q)).
Proof.
  intros. unfoldq.
  rewrite val_locs_abs.
  rewrite plift_and.
  intuition. 
Qed.



Lemma valq_sub: forall M M1 H v fr fr' q q',
    val_qual M M1 H v fr q ->
    psub q q' ->
    psub q' (pdom H) ->
    val_qual M M1 H v (fr||fr') q'.
Proof.
  intros. unfoldq. intuition.
  specialize (H0 x). intuition.
  left. destruct H0 as [? [? ?]].
  exists x0; intuition.
  right. destruct fr; simpl; intuition.
Qed.


(* ---------- environment lemmas  ---------- *)

Lemma wf_env_type: forall M H1 H2 G p, 
  env_type M H1 H2 G p -> 
  (length H1 = length G /\
   length H2 = length G /\  
   pdom H1 = pdom G /\ 
   pdom H2 = pdom G /\ 
   psub p (pdom H1) /\
   psub p (pdom H2)
   ).
Proof.
    intros. unfold env_type in H. intuition.
    unfold pdom. rewrite H0. auto.
    unfold pdom. rewrite H. auto.
Qed.

Lemma envt_tighten: forall M H1 H2 G p p',
    env_type M H1 H2 G p ->
    psub p' p ->
    env_type M H1 H2 G p'.
Proof.
  intros. destruct H as [L1 [L2 [P1 [P2 W]]]].
  repeat split; auto.
  - unfoldq. intuition.
  - unfoldq. intuition.
  - intros.
    destruct W as [W ?].
    destruct (W x T fr); eauto. 
  - intros.
    destruct W as [? [W1 W2]].
    eauto.
  - intros.
    destruct W as [? [W1 W2]].
    eauto.
Qed.

Lemma has_type_closed: forall M H1 H2 G p t T fr q e,
  env_type M H1 H2 G (plift p) -> 
  has_type G t T p fr q e ->
  (
    closed_ty (length G) T /\
    closed_ql (length G) p /\
    closed_ql (length G) q /\
    closed_ql (length G) e
  ).
Proof.
  intros. eapply filter_closed in H as H'.  induction H0; intuition.
  + destruct H as [? [? [? [? [? [? ?]]]]]]. destruct (H7 x T fr) as [? [? [? [? ?]]]]; auto.
    eapply valt_closed in H12. rewrite <- H.  intuition.
  + unfold closed_ql. intros. unfold qone in H4. bdestruct (x0 =? x); intuition.
    apply indexr_var_some' in H0. lia.
  + eapply closedq_or; intuition.
  + eapply closedq_or; intuition. eapply closedq_or; intuition.
  + inversion H5. subst. auto.
  + eapply closedq_or; intuition. eapply closedq_sub. 2: eapply H3. auto.
  + eapply closedq_or; intuition. eapply closedq_or; intuition. eapply closedq_sub. 2: eapply H4. auto.
  + constructor; intuition.
  + assert (env_type M H1 H2 env (plift p1)). eapply envt_tighten; eauto. 
    assert (env_type M H1 H2 env (plift p2)). eapply envt_tighten. 2: eauto. auto.
    assert (closed_ql (length env) p1). eapply closedq_sub; eauto.
    assert (closed_ql (length env) p2). eapply closedq_sub. 2: eauto. auto.
    intuition. eapply closedq_or; intuition. eapply closedq_or; intuition.
Qed.


Lemma var_locs_head: forall v H l,
  var_locs (v :: H) (length H) l ->
  val_locs v l.
Proof. 
  intros. 
  destruct H0 as [vx [IVX VALVX]].
  
  assert (indexr (length H) (v :: H) = Some v). {
    replace (v :: H) with ([] ++ v :: H) in IVX; auto.
    rewrite indexr_insert in IVX; eauto.
    inversion IVX. subst.
    replace (vx :: H) with ([] ++ vx :: H); auto.
    rewrite indexr_insert; eauto.
  }
  rewrite H0 in IVX. inversion IVX. subst.
  auto.
Qed.


Lemma var_locs_shrink: forall v H x l,
  var_locs (v::H) x l ->
  x < length H ->
  var_locs H x l.
Proof.
  intros. unfoldq. 
  destruct H0 as [vx [IVX VALVX]].
  exists vx. split.
  erewrite <- indexr_skip; eauto. lia.
  auto.
Qed.


Lemma envt_extend: forall M H1 H2 G v1 v2 T fr q p,
    env_type M H1 H2 G p ->
    closed_ty (length G) T ->
    closed_ql (length G) q ->
    val_type M H1 H2 v1 v2 T T ->
   (* (fr = false -> psub (val_locs v1) pempty) ->
    (fr = false -> psub (val_locs v2) pempty) -> *)
    (* separation *)
    (forall x l, val_locs v1 l -> p x -> var_locs H1 x l -> False) ->
    (forall x l, val_locs v2 l -> p x -> var_locs H2 x l -> False) ->
    env_type M (v1::H1)(v2::H2) ((T,fr)::G) (por p (pone (length G))).
Proof. 
  intros. apply wf_env_type in H as HH.
  assert (length H1 = length H2). intuition.
  destruct H as [L1 [L2 [P1 [P2 [W1 [W2 W3]]]]]]. 
  repeat split; auto.
  - simpl. eauto.
  - simpl. auto.
  - unfoldq. simpl. intuition.
  - unfoldq. simpl. intuition.
  - intros. simpl in *. 
    rewrite L1 in *. rewrite L2 in *.
    
    bdestruct (x =? (length G)); intuition; subst.
    + inversion H. subst. exists v1, v2. intuition.
      eapply valt_extend1; eauto.
      assert (length H1 = length G). { auto. }
      rewrite H9. auto.
      assert (length H2 = length G). { auto. }
      rewrite H9. auto.
    + destruct (W1 _ _ _ H) as [v1' [v2' ?]]; eauto.
      unfoldq. intuition.
      exists v1', v2'. intuition. eauto.
      eapply valt_extend1; eauto.
      1,2: eapply valt_closed with (H2 := H2); eauto.   
  - intros.
    inversion H; inversion H9.
    + eapply W2; eauto.
      eapply var_locs_shrink. eauto. eapply P1; eauto.
      eapply var_locs_shrink. eauto. eapply P1; eauto.
    + destruct (H5 x0 l); eauto.
      assert (x1 = length H1). unfoldq. intuition.
      subst x1. eapply var_locs_head; eauto.
      eapply var_locs_shrink. eauto. eapply P1; eauto.
    + destruct (H5 x1 l); eauto.
      assert (x0 = length H1). unfoldq. intuition.
      subst x0. eapply var_locs_head; eauto.
      eapply var_locs_shrink. eauto. eapply P1; eauto.
    + unfoldq. lia.
  - intros.
    inversion H; inversion H9.
    + eapply W3; eauto.
      eapply var_locs_shrink. eauto. eapply P2; eauto.
      eapply var_locs_shrink. eauto. eapply P2; eauto.
    + destruct (H6 x0 l); eauto.
      assert (x1 = length H2). unfoldq. intuition.
      subst x1. eapply var_locs_head; eauto.
      eapply var_locs_shrink. eauto. eapply P2; eauto.
    + destruct (H6 x1 l); eauto.
      assert (x0 = length H2). unfoldq. intuition.
      subst x0. eapply var_locs_head; eauto.
      eapply var_locs_shrink. eauto. eapply P2; eauto.
    + unfoldq. lia.
Qed.


Lemma envt_store_change: forall M M' H1 H2 G p,
    env_type M H1 H2 G p ->
    st_chain_partial M M' (vars_locs H1 p) (vars_locs H2 p) ->
    st_chain_partial2 M' M (vars_locs H1 p) (vars_locs H2 p) ->
    env_type M' H1 H2 G p.
Proof.
  intros. destruct H as [L1 [L2 [P1 [P2 [W1 [W2 W3]]]]]]. 
  repeat split; auto. intros.
  destruct (W1 _ _  _ H H4) as [vx1 [vx2 [IH1 [IH2 HVX]]]]; intuition.
  exists vx1, vx2; intuition.
  eapply valt_store_change in HVX; eauto.
  eapply stchain_tighten. eauto.
  intros ? ?. exists x. intuition. exists vx1. intuition.
  intros ? ?. exists x. intuition. exists vx2. intuition.
  eapply stchain_tighten'. eauto.
  intros ? ?. exists x. intuition. exists vx1. intuition.
  intros ? ?. exists x. intuition. exists vx2. intuition.
Qed.

Lemma envt_store_extend: forall M M' H1 H2 G p,
    env_type M H1 H2 G p ->
    st_chain M M' ->
    env_type M' H1 H2 G p.
Proof.
  intros. destruct H as [L1 [L2 [P1 [P2 [W1 [W2 W3]]]]]]. 
  repeat split; auto. intros.
  destruct (W1 _ _ _ H H3) as [vx1 [vx2 [IH1 [IH2 HVX]]]]; intuition.
  exists vx1, vx2; intuition.
  eapply valt_store_extend in HVX; eauto.
Qed.


Lemma envt_extend_all: forall M M1 H1 H2 G vx1 vx2 T1 p fr q1 qf,
    env_type M H1 H2 G p ->
    st_chain_partial M M1 (vars_locs H1 (pand p qf)) (vars_locs H2 (pand p qf)) ->
    st_chain_partial2 M1 M (vars_locs H1 (pand p qf)) (vars_locs H2 (pand p qf)) ->
    val_type M1 H1 H2 vx1 vx2 T1 T1 ->
    psub (pand (vars_locs H1 (pand p qf)) (val_locs vx1)) pempty ->
    psub (pand (vars_locs H2 (pand p qf)) (val_locs vx2)) pempty ->
   (* (fr = false -> psub (val_locs vx1) pempty) ->
    (fr = false -> psub (val_locs vx2) pempty) -> *)
    closed_ty (length G) T1 ->
    closed_ql (length G) q1 ->
    env_type M1 (vx1 :: H1)(vx2 :: H2) ((T1,fr) :: G) (por (pand p qf) (pone (length G))).
Proof.
  intros.

  eapply envt_extend.
  eapply envt_store_change.
  eapply envt_tighten.
  eauto.
  unfoldq. intuition.
  eauto.
  eauto.
  auto.
  eauto.
  eauto.
  eauto.
  auto.
  auto.
  
  (* now prove separation on the first *) 
  intros.

  unfoldq. unfoldq.
  eapply H5. intuition.
  exists x. intuition.
  destruct H11.
  exists x0. intuition. eauto.
  destruct H11.
  eauto.


  (* now prove separation on the second *) 
  intros.

  unfoldq. unfoldq.
  eapply H6. intuition.
  exists x. intuition.
  destruct H11.
  exists x0. intuition. eauto.
  destruct H11.
  eauto.
Qed.



Lemma env_type_store_wf: forall M H1 H2 G p q,
    env_type M H1 H2 G p ->
    psub q p ->
    ( psub (vars_locs H1 q) (pnat (length1 M)) /\ 
      psub (vars_locs H2 q) (pnat (length2 M))).
Proof.
  unfoldq; intuition;
  intros; destruct H as [L1 [L2 [P1 [P2 [W1 [W2 W3]]]]]]; intuition;
  unfoldq; intuition.
  (* 1st *)
  destruct H3 as [? [? ?]].
  assert (p x0). eapply H0. eauto.
  assert (x0 < length H1). eauto.

  assert (exists xtq, indexr x0 G = Some xtq) as TY. 
  eapply indexr_var_some. rewrite <-L1. eauto.
  destruct TY as [[T fr] ?].
  destruct H3 as [? [? ?]].
  destruct (W1 x0 T fr) as [vx1 [vx2 [IX1 [IX2 IV]]]]. eauto. eauto.
  rewrite H3 in IX1. inversion IX1. subst x1.

  eapply valt_wf in IV.  intuition. eapply H8; eauto.

  (* 2st *)
  destruct H3 as [? [? ?]].
  assert (p x0). eapply H0. eauto.
  assert (x0 < length H2). eauto.

  assert (exists xtq, indexr x0 G = Some xtq) as TY. eapply indexr_var_some. rewrite <-L2. eauto. 
  destruct TY as [[T fr] ?].
  destruct H3 as [? [? ?]].
  destruct (W1 x0 T fr) as [vx1 [vx2 [IX1 [IX2 IV]]]]. eauto. eauto.
  rewrite H3 in IX2. inversion IX2. subst x1.

  eapply valt_wf in IV. eapply IV; eauto.
Qed.



(* NOTE: it may seem good enough if either q or q' are subsets of
         the filter p, because that rules out any overlap outside
         of the filter.

         Not true: consider

         E = { a -> l, b -> l }
         p = a
         q = b

         (locs q) & (locs p) = { l }
         q & p = {}
*)

(* XXX see if we can make this more liberal XXX *)

Lemma vars_locs_dist_and1: forall M E1 E2 env p q q'
    (WFE: env_type M E1 E2 env p),
    psub q p ->
    psub q' p ->
    pand (vars_locs E1 q) (vars_locs E1 q') = vars_locs E1 (pand q q').    
Proof.
  intros. 
  eapply functional_extensionality.
  intros. eapply propositional_extensionality.
  destruct WFE as [L1 [L2 [P1 [P2 [W [SEP1 SEP2]]]]]].
  intuition.
  - destruct H1 as [[? [? ?]]  [? [? ?]]].
    assert (x0 = x1). eapply SEP1; eauto. subst x1.
    exists x0. unfoldq. intuition.
  - destruct H1 as [? [? [? [? ?]]]].
    unfoldq. intuition.
    exists x0. intuition. exists x1. intuition.
      
    exists x0. intuition. exists x1. intuition.
Qed.

Lemma vars_locs_dist_and2: forall M E1 E2 env p q q'
    (WFE: env_type M E1 E2 env p),
    psub q p ->
    psub q' p ->
    pand (vars_locs E2 q) (vars_locs E2 q') = vars_locs E2 (pand q q'). 
Proof. 
  intros. eapply functional_extensionality.
  intros. eapply propositional_extensionality.
  destruct WFE as [L1 [L2 [P1 [P2 [W [SEP1 SEP2]]]]]].
  intuition.
  - destruct H1 as [[? [? ?]]  [? [? ?]]].
    assert (x0 = x1). eapply SEP2; eauto. subst x1.
    exists x0. unfoldq. intuition.
  - destruct H1 as [? [? [? [? ?]]]].
    unfoldq. intuition.
    exists x0. intuition. exists x1. intuition.
      
    exists x0. intuition. exists x1. intuition.  
Qed.



Lemma separation: forall M M' M'' H1 H2 G p vf1 vf2 vx1 vx2 frf qf frx q1
    (WFE: env_type M H1 H2 G p)
    (HQF1: val_qual (length1 M)(length1 M') H1 vf1 frf (pand p qf))
    (HQF2: val_qual (length2 M)(length2 M') H2 vf2 frf (pand p qf))
    (STC1: st_chain M M')
    (STC2: st_chain M' M'')
    (HQX1: val_qual (length1 M') (length1 M'') H1 vx1 frx (pand p q1))
    (HQX2: val_qual (length2 M') (length2 M'') H2 vx2 frx (pand p q1))
    (PVF1: psub (val_locs vf1) (pnat (length1 M')))
    (PVF2: psub (val_locs vf2) (pnat (length2 M')))
    (QSEP: psub (pand qf q1) pempty),
    (
    psub (pand (val_locs vf1) (val_locs vx1)) pempty /\
    psub (pand (val_locs vf2) (val_locs vx2)) pempty
    ).
Proof. 
  intros. unfoldq. intuition.
  intros. unfoldq. intuition.
  1,2: remember WFE as WFE1; clear HeqWFE1;
  destruct WFE as [L1 [L2 [P1 [P2 [W [SEP1 SEP2]]]]]].
  (* 1st *)
  + bdestruct (x <? length1 M).
  - destruct (HQF1 x). intuition.
    destruct (HQX1 x). eauto.
    destruct H4 as [? [[? ?] ?]].
    destruct H5 as [? [[? ?] ?]]. 
    assert (x0 = x1). eapply SEP1; intuition; eauto.
    eapply QSEP. subst x0. intuition; eauto.
    destruct frx; intuition. 
    destruct frf; intuition.
  - bdestruct (x <? length1 M').
    -- destruct (HQX1 x). intuition.
       destruct H5 as [? [[? ?] ?]].
      (* fresh loc in vf, also occurs in vx --> can't happen *)
      assert (psub (vars_locs H1 (pone x0)) (pnat (length1 M))) as L. {
        eapply env_type_store_wf with (H2 := H2). eauto. unfoldq. intuition. subst x1. eauto.
      }
      assert (x < length1 M). {
        eapply L. unfoldq. exists x0. intuition.
      }
      lia.
      destruct frx; intuition.
    -- (* fresh loc in vx, bigger than vf *)
      eapply PVF1 in H0. lia.
  
  (* 2nd *)
  + bdestruct (x <? length2 M).
  - destruct (HQF2 x). intuition.
    destruct (HQX2 x). eauto.
    destruct H4 as [? [[? ?] ?]].
    destruct H5 as [? [[? ?] ?]].  
    assert (x0 = x1). eapply SEP2; intuition; eauto.
    eapply QSEP. subst x0. intuition; eauto.
    destruct frx; intuition. 
    destruct frf; intuition.
  - bdestruct (x <? length2 M').
    -- destruct (HQX2 x). intuition.
       destruct H5 as [? [[? ?] ?]].
      (* fresh loc in vf, also occurs in vx --> can't happen *)
      assert (psub (vars_locs H2 (pone x0)) (pnat (length2 M))) as L. {
        eapply env_type_store_wf with (H2 := H2). eauto. unfoldq. intuition. subst x1. eauto.
      }
      assert (x < length2 M). {
        eapply L. unfoldq. exists x0. intuition.
      }
      lia.
      destruct frx; intuition.
    -- (* fresh loc in vx, bigger than vf *)
      eapply PVF2 in H0. lia.
Qed.


(* ---------- store typing lemmas ---------- *)

Lemma storet_length: forall S1 S2 M,
    store_type S1 S2 M ->
    (length S1 = length1 M /\
     length S2 = length2 M).
Proof.
  intros. destruct H; intuition.
Qed.


Lemma storet_extend: forall S1 S2 M H1 H2 b1 b2,
    store_type S1 S2 M ->
    val_type M H1 H2 (vbool b1)(vbool b2) TBool TBool ->
    store_type ((vbool b1) :: S1) ((vbool b2) :: S2) (st_extend M).
Proof.
  intros.
  unfold store_type in *. intuition.
  unfold length1. simpl. eauto.
  unfold length2. simpl. eauto.
  unfold strel in H6. simpl in H6.
  destruct H6.
  - (* hit *)
    destruct H6. 
    exists b1, b2. subst l1 l2.
    rewrite <-H3, indexr_head.
    rewrite <-H, indexr_head.
    simpl in H0. intuition.
  - (* miss *)
    edestruct H4 as [? [? [? [? ?]]]]; eauto.
    exists x, x0. subst.
    rewrite indexr_extend1 in H8; try lia.
    rewrite indexr_extend1 in H9; try lia. 
    intuition; eauto.
  - (* right unique *)
    simpl in H6, H8.
    destruct H6; destruct H8.
    + destruct H6, H8. congruence.
    + edestruct H4 as [? [? [? [? ?]]]]; eauto.
      rewrite indexr_extend in H9. lia. 
    + edestruct H4 as [? [? [? [? ?]]]]; eauto.
      rewrite indexr_extend in H9. lia.
    + eapply H5; eauto.
  - (* left unique *)
    simpl in H6, H8.
    destruct H6; destruct H8.
    + destruct H6, H8. congruence.
    + edestruct H4 as [? [? [? [? ?]]]]; eauto.
      rewrite indexr_extend in H10. lia. 
    + edestruct H4 as [? [? [? [? ?]]]]; eauto.
      rewrite indexr_extend in H10. lia.
    + eapply H7; eauto.
      Unshelve.
      eapply [].
      eapply [].
      eapply [].
      eapply [].
Qed.

Lemma storet_update: forall S1 S2 M H1 H2 i1 i2 b1 b2,
    store_type S1 S2 M ->
    val_type M H1 H2 (vref i1) (vref i2) (TRef TBool) (TRef TBool) ->
    val_type M H1 H2 (vbool b1) (vbool b2) TBool TBool -> 
    store_type (update S1 i1 (vbool b1)) (update S2 i2 (vbool b2)) M.
Proof.
  intros. destruct H as [L1 [L2 [ST [U2 U1]]]].
  repeat split. 
  (* length *)
  rewrite <-update_length. eauto.
  rewrite <-update_length. eauto.
  (* lookup *) {
    intros l1 l2 RL.
    destruct H0 as [? [? [? [? RI]]]].
    bdestruct (i1 =? l1).
    - subst. assert (i2 = l2). eapply U2; eauto. subst. 
      assert (b1 = b2). simpl in H3. auto. 
      exists b1, b2. subst.
      rewrite update_indexr_hit; intuition. 
      rewrite update_indexr_hit; intuition. 
    - assert (i2 <> l2). intros ?. subst. eapply H6. eapply U1; eauto.
      rewrite update_indexr_miss; intuition.
      rewrite update_indexr_miss; intuition.
  }
  (* right/left unique *)
  eauto. eauto. 
Qed.


(* ---------- compatibility lemmas & fundamental theorem ---------- *)

Lemma bi_vtrue: forall S1 S2 M H1 H2 p q,
  store_type S1 S2 M -> 
  exp_type S1 S2 M H1 H2 ttrue ttrue S1 S2 M (vbool true) (vbool true) TBool p false q pempty.
Proof.   
  intros. remember H as H''. clear HeqH''.
  destruct H as [SL1 [SL2  [SP1 SP2]]]. 
  split.
  exists 0. intros. destruct n. lia. simpl. eauto.
  split.
  exists 0. intros. destruct n. lia. simpl. eauto.
  split.
  eapply st_refl.
  split.
  (* store_typing*)
  eauto.
  split.
  intros ? ?. intuition.
  split.
  intros ? ?. intuition.
  
  simpl. repeat split.
  apply valq_bool. apply valq_bool.
Qed.

Lemma bi_vfalse: forall S1 S2 M H1 H2 p q,
  store_type S1 S2 M -> 
  exp_type S1 S2 M H1 H2 tfalse tfalse S1 S2 M (vbool false) (vbool false) TBool p false q pempty.
Proof.   
  intros.  remember H as H''. clear HeqH''.
  destruct H as [SL1 [SL2  [SP1 SP2]]]. 
  split.
  exists 0. intros. destruct n. lia. simpl. eauto.
  split.
  exists 0. intros. destruct n. lia. simpl. eauto.
  split.
  eapply st_refl.
  split. 
  (* store_typing*)
  eauto.
  split.
  intros ? ?. intuition.
  split.
  intros ? ?. intuition.
  
  simpl. repeat split.
  apply valq_bool. apply valq_bool.
Qed.

Lemma se_trans: forall S1 S2 S3 p,
    store_effect S1 S2 p ->
    store_effect S2 S3 p ->
    store_effect S1 S3 p.
Proof.
  intros. intros ? ? ? ?.
  eapply H0. eauto. eapply H. eauto. eauto. 
Qed.

Lemma se_sub: forall S1 S2 p p',
    store_effect S1 S2 p ->
    psub p p' ->
    store_effect S1 S2 p'.
Proof.
  intros. intros ? ? ? ?.
  eapply H. unfoldq. intuition. eauto. 
Qed.


Lemma bi_tref: forall e1 e2 M M' S1 S2 S1' S2' H1 H2 v1 v2 p fr q e,
  exp_type S1 S2 M H1 H2 e1 e2 S1' S2' M' v1 v2 TBool p fr q e ->
  exists S1'' S2'' M''  v1 v2,
  exp_type S1 S2 M H1 H2 (tref e1) (tref e2) S1'' S2''  M'' v1 v2 (TRef TBool) p true q e.
Proof.
  intros. 
  destruct H as [IE1 [IE2 [STC [ST [SP1 [SP2 [HV [HQ1 HQ2]]]]]]]].
  remember ST as ST'. clear HeqST'.
  destruct ST as [SL1 [SL2 [SP3 [SP4 SP5]]]].
  remember HV as  HV'. clear HeqHV'.
  destruct v1; destruct v2; try solve [inversion HV].
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
  (* st_chain *)
  eapply st_trans. eauto. eapply stchain_extend. 
  
  split.
  (* store_typing *)
  eapply storet_extend. eauto.
  auto.

  split.
  eapply se_trans. eauto. intros ? ?. intros. eapply indexr_extend1 in H0. eapply H0.
  split.
  eapply se_trans. eauto. intros ? ?. intros. eapply indexr_extend1 in H0. eapply H0.
  
  
  split.
  (* result type *)
  simpl. intuition.
  unfold length1, st_extend. simpl. lia.
  unfold length2, st_extend. simpl. lia.  
  
  split.
  rewrite SL1. unfoldq; intuition. 
  rewrite val_locs_ref in H. unfoldq; intuition.
  subst x. right. unfold length1 at 2. simpl. 
  eapply st_mono1 in STC. intuition.
  
  
  rewrite SL2. unfoldq; intuition. 
  rewrite val_locs_ref in H. unfoldq; intuition.
  subst x. right. unfold length2 at 2. simpl. 
  eapply st_mono2 in STC. intuition.

  Unshelve. apply []. apply [].
Qed.

Lemma bi_tget: forall t1 t2 S1 S2 S1' S2' M M'  H1 H2 p fr q e v1 v2,
  exp_type S1 S2 M H1 H2 t1 t2 S1' S2' M' v1 v2 (TRef (TBool)) p fr q e ->
  exists S1'' S2'' M'' v3 v4,
  exp_type S1 S2 M H1 H2 (tget t1) (tget t2)  S1'' S2''  M'' v3 v4 TBool p false pempty e.
Proof. 
  intros.  
  destruct H as [EV1 [EV2 [STC [STH [SPP1 [SPP2 [HV [HQ1 HQ2]]]]]]]].
  destruct v1; destruct v2; try solve [inversion HV]. simpl in HV.
  
  destruct HV as [HT [HT' [LS1 [LS2 VT]]]].
  remember STH as STH'. clear HeqSTH'.
  destruct STH as [STL1 [STL2 [SP1 [SP2 SP3]]]].

  assert (strel M' i i0) as A. eauto.
 
  destruct (SP1 i i0 A) as [b1 [b2 [IY1 [IY2 EQ]]]]. 
    
  exists S1', S2', M', (vbool b1), (vbool b2). 
  split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 8: split. 
  + destruct EV1 as [n1 IW1].
    exists (S n1). intros. destruct n. lia. simpl.
    rewrite IW1. rewrite IY1. eauto. lia.
  + destruct EV2 as [n1 IW2].
    exists (S n1). intros. destruct n. lia. simpl.
    rewrite IW2. rewrite IY2. eauto. lia.
  + eauto.
  + eauto.
  + eauto.
  + eauto.
  + eauto. 
  + eapply valq_bool.
  + eapply valq_bool.
Qed.
 
Lemma bi_put: forall S1 S2 M H1 H2 t1 t2 S1' S2' M' M'' S1'' S2'' v1 v2 v3 v4 p q1 q2 e1 e2 t3 t4 fr1 fr2
 (ST0: store_type S1 S2 M)
 (E1: exp_type S1 S2 M H1 H2 t1 t2 S1' S2' M' v1 v2 (TRef TBool) p fr1 q1 e1)
 (E2: exp_type S1' S2' M' H1 H2 t3 t4 S1'' S2'' M'' v3 v4 TBool p fr2 q2 e2),
 exists S1''' S2''' M'' v5 v6,
 exp_type S1 S2 M H1 H2 (tput t1 t3) (tput t2 t4) S1''' S2'''  M'' v5 v6 TBool p false pempty (por e1 (por e2 q1)).
Proof.
  intros. 
  destruct E1 as [IE1 [IE2 [SC [ST [SPP1 [SPP2 [HV [HQ1 HQ2]]]]]]]].
  destruct v1; destruct v2; try solve [inversion HV]. simpl in HV.
  destruct HV as [HT [HT'[LS1 [LS2 VT]]]].
  remember ST as ST'. clear HeqST'.
  destruct ST as [STL1 [STL2 [SP1 [SP2 SP3]]]].

  destruct E2 as [IE3 [IE4 [SC2 [ST2 [SPPP1 [SPPP2 [HV1 [HQ3 HQ4]]]]]]]].
  destruct v3; destruct v4; try solve [inversion HV1]. simpl in HV1.
  subst b0.
  remember ST2 as ST2'. clear HeqST2'.
  destruct ST2 as [STL3 [STL4 [SP4 [SP5 SP6]]]].

  exists (update S1'' i (vbool b)), (update S2'' i0 (vbool b)).
  exists M'', (vbool true), (vbool true).
  split. 2: split. 3: split. 4: split. 
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
  rewrite STL4. eapply st_mono2'; eauto. 
  apply indexr_var_some in H0. destruct H0. rewrite H0. auto. lia. lia.

  eapply st_trans; eauto.  
  
  (* store typing *)
  eapply storet_update; eauto. eapply valt_store_extend; eauto. 
  simpl. intuition. eapply st_mono2 in SC2. auto.
  simpl. eauto. 

  assert (length S1 = length1 M). destruct ST0 as (? & ? & ?). eauto.
  assert (length S2 = length2 M). destruct ST0 as (? & ? & ?). eauto.
  

  (* store preservation *)
  split. intros ? ?. intros.
  bdestruct (i =? l). { subst. destruct (HQ1 l).
  rewrite val_locs_ref. eapply indexr_var_some' in H4. unfoldq. intuition.
  destruct H3. eapply vars_locs_sub; eauto. intros ? ?. unfoldq; intuition.
  destruct fr1. simpl in *. unfoldq; intuition.
  apply indexr_var_some' in H4. lia.
  simpl in *. contradiction.
  }{ rewrite update_indexr_miss. eauto. eauto. }

  split. intros ? ?. intros.
  bdestruct (i0 =? l). { subst. destruct (HQ2 l).
  rewrite val_locs_ref. eapply indexr_var_some' in H4. unfoldq. intuition.
  destruct H3. eapply vars_locs_sub; eauto. intros ? ?. unfoldq; intuition.
  destruct fr1. simpl in *. unfoldq; intuition.
  apply indexr_var_some' in H4. lia.
  simpl in *. contradiction.
  }{ rewrite update_indexr_miss. eauto. eauto. }

  (* val_type and val_qual *)
  split. simpl. eauto. 
  split. eapply valq_bool. eapply valq_bool.
  Unshelve.
  apply []. apply [].
Qed.

Lemma bi_var: forall G M S1 S2 H1 H2 x T1 p fr
  (WFE: env_type M H1 H2 G p)
  (ST: store_type S1 S2 M),
  indexr x G = Some (T1,fr) ->
  p x ->
  exists v1 v2,
  exp_type S1 S2 M H1 H2 (tvar x) (tvar x) S1 S2 M v1 v2 T1 p false (pone x) pempty.
Proof.
  intros. 
  eapply WFE in H; auto. remember ST as ST'. clear HeqST'.
  destruct ST as [SL1 [SL2 [SP1 [SP2 SP3]]]]. 
  destruct H as [v1 [v2 [IX1 [IX2 VT]]]].
  exists v1, v2. 
  split.
  exists 0. intros. destruct n. lia. simpl. congruence.
  split.
  exists 0. intros. destruct n. lia. simpl. congruence.
  split.
  eapply st_refl.  
  split.
  eauto.
  split.
  intros ? ? ? ?. eauto. 
  split.
  intros ? ? ? ?. eauto. 
  split.
  auto.
  split.
  unfoldq. unfoldq. intuition. left.  exists x. intuition.
  exists v1. intuition.
  unfoldq. unfoldq. intuition. left.  exists x. intuition.
  exists v2. intuition.
Qed.

Lemma bi_tapp: forall M M' M'' S1 S2 S1' S2' S1'' S2'' vf1 vf2 vx1 vx2 G H1 H2 ef1 ef2 ex1 ex2 T1 T2 p qf ef q1 q2 e1 e2 fr1 fr2 frf frx
   (WFE: env_type M H1 H2 G p)
   (ST: store_type S1 S2 M)
   (IEF: exp_type S1 S2 M H1 H2 ef1 ef2 S1' S2' M' vf1 vf2 (TFun T1 fr1 T2 fr2 q2 e2) p frf qf ef)  
   (IEX: exp_type S1' S2' M' H1 H2 ex1 ex2 S1'' S2'' M'' vx1 vx2 T1 p frx q1 e1)  
   (QSEP: psub (pand qf q1) pempty ) 
   (Q2: psub (plift q2) p)
   (E2: psub (plift e2) p),
   exists S1''' S2''' M''' v5 v6,
   exp_type S1 S2 M H1 H2 (tapp ef1 ex1) (tapp ef2 ex2) S1''' S2''' M''' v5 v6 T2 p (frf||frx||fr2) (por (plift q2) q1) (por ef (por e1 (plift e2))).
Proof.
  intros. 
  destruct IEF as [IEF1 [IEF2 [SC1 [ST1 [SPP1 [SPP2 [HVF [HQF1 HQF2]]]]]]]].
  destruct IEX as [IEX1 [IEX2 [SC2 [ST2 [SPPP1 [SPPP2 [HV2 [HQX1 HQX2]]]]]]]].

  destruct vf1; destruct vf2; try solve [inversion HVF]; simpl in HVF; intuition.
  rename H13 into HVF.
  specialize (HVF S1'' S2'' M''  vx1 vx2); intuition.
  
  assert ( psub (pand (val_locs (vabs l q t)) (val_locs vx1)) pempty  /\
      psub (pand (val_locs (vabs l0 q0 t0)) (val_locs vx2)) pempty ). { 
       eapply separation; eauto.
  }
  intuition.
  destruct HVF as [S1'''[S2''' [M''' [r1 [r2 [IAPP1 [IAPP2 [IAPPSC [IAPPST [IVPP1 [IVPP2 [IVALY [HQY1 HQY2]]]]]]]]]]]]].

  eapply stchain_tighten; eauto. eapply SC2.
  eapply stchain_tighten'; eauto. eapply SC2.
  eapply st_mono2 in SC2. auto.
  eauto.
  eauto.
  eauto.
  eauto.
  
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
  eapply st_trans. eapply st_trans. eauto. eauto. eauto. 
  
  split.
  (* store typing *)
  eauto.

  split.
  (* store preservation 1 *)  
  intros ? ? ? ?. rewrite IVPP1. eauto. 2: eauto.
  assert (l1 < length1 M). { eapply indexr_var_some' in H15. destruct ST as (L & ?). lia. }
  intros ?. eapply H12. destruct H17. {
    destruct (HQF1 l1). unfoldq. intuition.
    eapply vars_locs_sub; eauto. intros ? ?. unfoldq; intuition.
    destruct frf; simpl in H18. unfoldq; intuition.
    contradiction.
  } {
    destruct (HQX1 l1). unfoldq. intuition. 
    eapply vars_locs_sub; eauto. intros ? ?. unfoldq; intuition.
    destruct frx; simpl in H18. unfoldq; intuition.
    eapply indexr_var_some' in H15. eapply st_mono1 in SC1. lia.
    contradiction.
  }
  
  split.
  (* store preservation 2 *)  
  intros ? ? ? ?. rewrite IVPP2. eauto. 2: eauto.
  assert (l1 < length2 M). { eapply indexr_var_some' in H15. destruct ST as (L & ?). lia. }
  intros ?. eapply H12. destruct H17. {
    destruct (HQF2 l1). unfoldq. intuition.
    eapply vars_locs_sub; eauto. intros ? ?. unfoldq; intuition.
    destruct frf; simpl in H18. unfoldq; intuition.
    contradiction.
  } {
    destruct (HQX2 l1). unfoldq. intuition. 
    eapply vars_locs_sub; eauto. intros ? ?. unfoldq; intuition.
    destruct frx; simpl in H18. unfoldq; intuition.
    eapply indexr_var_some' in H15. eapply st_mono2 in SC1. lia.
    contradiction.
  }

  split.
  (* result type *)
  eauto. 
  
  split.

  (* 1st qual *)
  assert (length1 M <= length1 M') as LM1. eapply st_mono1; eauto.
  assert (length1 M' <= length1 M'') as LM2. eapply st_mono1; eauto.
  assert (length1 M'' <= length1 M''') as LM3. eapply st_mono1; eauto.

  remember (vabs l q t) as vf1.
  unfold val_qual. intros ? ?.
  destruct fr1. {  (* function is fresh *) 
    destruct frx. { (* arguemtn is fresh *)
      destruct (HQY1 x); auto.
      destruct H15 as [? ?].
      + (* part of the function *)
        destruct (HQF1 x); auto.
        unfoldq; intuition.
        destruct H15 as [? [? ?]].
        destruct H17 as [? [[? ?] ?]].
        left. exists x0; intuition.
        unfoldq; intuition.
        destruct H15 as [? [? ?]].
        destruct frf. destruct H17 as [? ?].
        left. exists x0; intuition. contradiction.
      + (* part of argument *)
        destruct H15.
        destruct (HQX1 x); auto.
        unfoldq; intuition.
        destruct H16 as [? [[? ?] ?]].
        left. exists x0; intuition.
        simpl in H16. unfoldq; intuition.
        right. destruct frf; destruct fr2; simpl; intuition.  
        destruct fr2; destruct frf; simpl in *;
        unfoldq; intuition.
    } {
      destruct (HQY1 x); auto.
      unfoldq; intuition.
      (* part of function *) 
      destruct H16 as [? [? ?]].
      left. exists x0; intuition.
      (* part of argument *)
      unfoldq. destruct H15.
      destruct (HQX1 x); auto.
      left. destruct H16 as [? [[? ?] ?]].
      exists x0; intuition. contradiction.
      destruct fr2; destruct frf; simpl in *;
      intuition.  
    }
  } {
    destruct (HQY1 x); auto.
    (* part of function *)
    destruct H15. destruct (HQF1 x); auto.
    unfoldq; intuition.
    destruct H15 as [? [? ?]].
    destruct H17 as [? [[? ?] ?]]. 
    left. exists x0; intuition.
    destruct frf. simpl in *.
    unfoldq; intuition. simpl in *. contradiction.
    (* part of argument *)
    destruct H15. 
    destruct (HQX1 x); auto.
    unfoldq; intuition.
    destruct H16 as [? [[? ?] ?]].
    left. exists x0; intuition.
    destruct frx; destruct fr2; destruct frf; simpl in *; unfoldq; intuition.
    destruct fr2; destruct frf; destruct frx; simpl in *; unfoldq; intuition. 
  } 

  
  (* 2nd qual *)

  assert (length2 M <= length2 M') as LM1. eapply st_mono2; eauto.
  assert (length2 M' <= length2 M'') as LM2. eapply st_mono2; eauto.
  assert (length2 M'' <= length2 M''') as LM3. eapply st_mono2; eauto.

  remember (vabs l0 q0 t0) as vf2.
  unfold val_qual. intros ? ?.
  destruct fr1. {  (* function is fresh *) 
    destruct frx. { (* arguemtn is fresh *)
      destruct (HQY2 x); auto.
      destruct H15 as [? ?].
      + (* part of the function *)
        destruct (HQF2 x); auto.
        unfoldq; intuition.
        destruct H15 as [? [? ?]].
        destruct H17 as [? [[? ?] ?]].
        left. exists x0; intuition.
        unfoldq; intuition.
        destruct H15 as [? [? ?]].
        destruct frf. destruct H17 as [? ?].
        left. exists x0; intuition. contradiction.
      + (* part of argument *)
        destruct H15.
        destruct (HQX2 x); auto.
        unfoldq; intuition.
        destruct H16 as [? [[? ?] ?]].
        left. exists x0; intuition.
        simpl in H16. unfoldq; intuition.
        right. destruct frf; destruct fr2; simpl; intuition.  
        destruct fr2; destruct frf; simpl in *;
        unfoldq; intuition.
    } {
      destruct (HQY2 x); auto.
      unfoldq; intuition.
      (* part of function *) 
      destruct H16 as [? [? ?]].
      left. exists x0; intuition.
      (* part of argument *)
      unfoldq. destruct H15.
      destruct (HQX2 x); auto.
      left. destruct H16 as [? [[? ?] ?]].
      exists x0; intuition. contradiction.
      destruct fr2; destruct frf; simpl in *;
      intuition.  
    }
  } {
    destruct (HQY2 x); auto.
    (* part of function *)
    destruct H15. destruct (HQF2 x); auto.
    unfoldq; intuition.
    destruct H15 as [? [? ?]].
    destruct H17 as [? [[? ?] ?]]. 
    left. exists x0; intuition.
    destruct frf. simpl in *.
    unfoldq; intuition. simpl in *. contradiction.
    (* part of argument *)
    destruct H15. 
    destruct (HQX2 x); auto.
    unfoldq; intuition.
    destruct H16 as [? [[? ?] ?]].
    left. exists x0; intuition.
    destruct frx; destruct fr2; destruct frf; simpl in *; unfoldq; intuition.
    destruct fr2; destruct frf; destruct frx; simpl in *; unfoldq; intuition. 
  } 

Qed.


Lemma valt_same_locs: forall S1 S2 M H1 H2 v1 v2 T T' l1 l2,
    store_type S1 S2 M ->
    val_type M H1 H2 v1 v2 T T' ->
    strel M l1 l2 ->
    val_locs v1 l1 <-> val_locs v2 l2.
Proof.
  intros.
  destruct T; destruct T'; destruct v1; destruct v2; simpl in H0; try contradiction; eauto.
  - repeat rewrite val_locs_bool in *. unfoldq. intuition.
  - repeat rewrite val_locs_ref in *. unfoldq. 
    destruct H as (? & ? & ? & ? & ?).
    split; intros.
    subst l1. eapply H6. eauto. eapply H0.
    subst l2. eapply H7. eauto. eapply H0.
  - repeat rewrite val_locs_abs in *.
    eapply H0. eauto. 
Qed.

Lemma envt_same_locs: forall S1 S2 M H1 H2 G p p1 l1 l2,
    store_type S1 S2 M ->
    env_type M H1 H2 G p ->
    strel M l1 l2 ->
    psub p1 p ->
    vars_locs H1 p1 l1 <-> vars_locs H2 p1 l2.
Proof.
  intros.
  destruct H0 as (? & ? & ? & ? & WFX & ? & ?).
  split; intros V.
  - destruct V as (? & ? & v1 & ? & V).
    assert (exists T, indexr x G = Some T) as TT. {
      eapply indexr_var_some. rewrite <-H0. eapply indexr_var_some'. eauto. }
    destruct TT as [[T fr] ?].
    destruct (WFX x T fr) as (v1' & v2 & ? & ? & ?). eauto. eauto.
    rewrite H11 in H13. inversion H13. subst v1'.
    exists x. split. eauto. exists v2. split. eauto.
    edestruct valt_same_locs; eauto.
  - destruct V as (? & ? & v2 & ? & V).
    assert (exists T, indexr x G = Some T) as TT. {
      eapply indexr_var_some. rewrite <-H5. eapply indexr_var_some'. eauto. }
    destruct TT as [[T  fr] ?].
    destruct (WFX x T fr) as (v1 & v2' & ? & ? & ?). eauto. eauto.
    rewrite H11 in H14. inversion H14. subst v2'.
    exists x. split. eauto. exists v1. split. eauto.
    edestruct valt_same_locs; eauto.
Qed.


Lemma bi_tabs: forall H1 H2 S1 S2 M G t1 t2 T1 T2 p q2 qf e2 fr1 fr2 
  (WFE: env_type M H1 H2 G (plift p))
  (ST: store_type S1 S2 M)
  (EXP:  forall S1' S2' M' vx1 vx2,
      val_type M' H1 H2 vx1 vx2 T1 T1 ->
      psub (pand (vars_locs H1 (pand (plift p) (plift qf))) (val_locs vx1)) pempty ->
      psub (pand (vars_locs H2 (pand (plift p) (plift qf))) (val_locs vx2)) pempty  -> 
      env_type M' (vx1::H1) (vx2:: H2) ((T1,fr1)::G) (plift (qor (qand p qf)(qone (length G)))) ->
      store_type S1' S2' M'  ->
      exists S1'' S2'' M'' v1 v2,
        exp_type S1' S2' M' (vx1:: H1) (vx2:: H2) t1 t2  S1'' S2'' M'' v1 v2 T2 (plift (qor (qand p qf)(qone  (length G)))) fr2 (plift (qor q2 (qone (length G)))) (plift (qor e2 (qone (length G)))))
  (T1CL: closed_ty (length G) T1)      
  (T2CL: closed_ty (length G) T2)
  (HQ2: (psub (plift q2) (pdom G)))
  (HE2: (psub (plift e2) (pdom G)))
  (HCLQF: closed_ql (length G) qf),
  exists S1'' S2'' M'' v1'' v2'',
  exp_type S1 S2 M H1 H2 (tabs (qand p qf) t1) (tabs (qand p qf) t2) S1'' S2'' M''  v1'' v2'' (TFun T1 fr1 T2 fr2 q2 e2) (plift p) true (plift qf) pempty.
Proof. 
  intros. 
  apply wf_env_type in WFE as WFE'. 
  destruct WFE' as [L1 [L2 [PD1 [PD2 [P1 P2]]]]].
  remember ST as ST'. clear HeqST'.
  destruct ST as [SL1 [SL2 [SP1 [SP2 SP3]]]].
  rewrite plift_or in *. rewrite plift_and in *.
  exists S1, S2, M.
  exists (vabs H1 (qand p qf) t1). exists (vabs H2 (qand p qf) t2).
  split.
  
  (* 1st *)
  exists 0.  intros. destruct n. lia. simpl. eauto.
  split.
  (* 2nd *)
  exists 0.  intros. destruct n. lia. simpl. eauto.
  split.
  eapply st_refl.
  split. 
  (* store typing *)  
  eauto.

  (* store preserve *)
  split. intros ? ? ? ?. eauto.
  split. intros ? ? ? ?. eauto.   
   
   (* results *)
   repeat split. 
   rewrite L1. auto.
   rewrite L1. auto.
   rewrite L2. auto.
   rewrite L2. auto.
   rewrite PD1. auto.
   rewrite PD2. auto.
   rewrite PD1. auto.
   rewrite PD2. auto.
   rewrite val_locs_abs.
   eapply env_type_store_wf. eauto.
   rewrite plift_and. unfoldq. intuition.
   rewrite val_locs_abs.
   eapply env_type_store_wf. eauto.
   rewrite plift_and. unfoldq. intuition.
   
   (* strel same locs *)
   rewrite val_locs_abs, val_locs_abs. edestruct envt_same_locs; eauto. rewrite plift_and. unfoldq. intuition. 
   rewrite val_locs_abs, val_locs_abs. edestruct envt_same_locs; eauto. rewrite plift_and. unfoldq. intuition. 

   (* evaluation *)
   intros.

   repeat rewrite val_locs_abs in H. rewrite plift_and in H.
   repeat rewrite val_locs_abs in H0. rewrite plift_and in H0.

   rewrite val_locs_abs in H5. rewrite plift_and in H5.
   rewrite val_locs_abs in H6. rewrite plift_and in H6.
   

   assert (env_type
        M'
        (vx1 :: H1) (vx2 :: H2) 
        ((T1,fr1) :: G)
        (plift
           (qor (qand p qf)
              (qone (length G))))) as WFE'.
   rewrite plift_or. rewrite plift_and. rewrite plift_one.
   eapply envt_extend_all in WFE; eauto.

   destruct (EXP S1' S2' M' vx1 vx2) as [S1'' [S2'' [M'' [vy1 [vy2 IEY]]]]]; intuition.   
   rewrite plift_or, plift_and in WFE'. auto.
  

   destruct IEY as [IEY1 [IEY2 [YSC [YST [YSP1 [YSP2 [IVY [IYQ1 IYQ2]]]]]]]].
   
   exists S1'', S2'', M'', vy1, vy2. intuition.


   (* store preserve *)
   intros ? ? PV ?. eapply YSP1. intros VL. eapply PV.
   destruct VL as (? & VL & ?).
   destruct VL. {
     left. rewrite val_locs_abs, plift_and. exists x. split. eauto. eapply var_locs_shrink. eauto. eapply (wf_env_type _ _ _ _ _ WFE). unfoldq. intuition.     
   } {
     right. destruct H8. replace x with (length H1) in H8.
     rewrite indexr_head in H8. intuition. congruence.
     rewrite plift_one in H9. unfoldq. intuition.
   }
   eauto.

   intros ? ? PV ?. eapply YSP2. intros VL. eapply PV.
   destruct VL as (? & VL & ?).
   destruct VL. {
     left. rewrite val_locs_abs, plift_and. exists x. split. eauto. eapply var_locs_shrink. eauto. eapply (wf_env_type _ _ _ _ _ WFE). unfoldq. intuition.     
   } {
     right. destruct H8. replace x with (length H2) in H8.
     rewrite indexr_head in H8. intuition. congruence.
     rewrite plift_one in H9. unfoldq. intuition.
   }
   eauto.


   (* valt *)
   eapply valt_extend; eauto.
   rewrite L1. auto. rewrite L2. auto.
   replace (vx1::H1) with ([vx1]++H1) in IVY; auto.
   replace (vx2::H2) with ([vx2]++H2) in IVY; auto.
   eapply IVY.


   (* qual *)
     
  rewrite val_locs_abs in *. rename H4 into HVX;
  apply valt_wf in HVX; apply valt_wf in IVY.
   rewrite plift_or, plift_one, plift_and in *. 
   
  unfoldq. intuition.
  destruct (IYQ1 x). eauto. 

  unfoldq. 
  destruct H11. destruct H11. 
  bdestruct (x0 =? length H1).
  (* from arg *)
    right. destruct H12 as [? [? ?]]. subst x0. 
    rewrite indexr_head in H12. inversion H12. eauto.
  (* from func *)
    left. split.
    exists x0. intuition. 
    destruct H12 as [? [? ?]]. 
    rewrite indexr_skip in H12. exists x1. split; eauto. lia.
    exists x0. split.
    destruct H11; destruct H11; try lia. eapply H11.
    destruct H12 as [? [? ?]]. rewrite indexr_skip in H12; eauto.
    destruct fr2; simpl in *; intuition.

   (* 2nd *)

  rewrite val_locs_abs in *. rename H4 into HVX;
  apply valt_wf in HVX; apply valt_wf in IVY.
   rewrite plift_or, plift_one, plift_and in *. 
  
  unfoldq. intuition.
  destruct (IYQ2 x). eauto. 

  unfoldq.
  destruct H11. destruct H11.
  bdestruct (x0 =? length H2).
  (* from arg *)
    right. destruct H12 as [? [? ?]]. subst x0. 
    rewrite indexr_head in H12. inversion H12. eauto.
  (* from func *)
    left. split.
    exists x0. intuition. 
    destruct H12 as [? [? ?]]. 
    rewrite indexr_skip in H12. exists x1. split; eauto. lia.
    exists x0. split.
    destruct H11; destruct H11; try lia. eapply H11.
    destruct H12 as [? [? ?]]. rewrite indexr_skip in H12; eauto.
    
    destruct fr2; simpl in H11; intuition.

  eapply valq_abs; eauto.
  eapply valq_abs; eauto.
Qed.

Lemma vl_mono: forall H1 p p',
    psub p p' ->
    psub (vars_locs H1 p) (vars_locs H1 p').
Proof.
  intros. intros ? (? & ?).
  exists x0. intuition. 
Qed.

Lemma bi_seq: forall S1 S2 M H1 H2 t1 t2 S1' S2' M' M'' S1'' S2'' v1 v2 v3 v4 p p1 p2 q1 q2 e1 e2 t3 t4
 (E1: exp_type S1 S2 M H1 H2 t1 t2 S1' S2' M' v1 v2 TBool p1 false q1 e1)
 (E2: exp_type S1' S2' M' H1 H2 t3 t4 S1'' S2'' M'' v3 v4 TBool p2 false q2 e2),
    psub p1 p ->
    psub p2 p -> (* separation not required for soundness *)
 exists S1''' S2''' M'' v5 v6,
 exp_type S1 S2 M H1 H2 (tseq t1 t3) (tseq t2 t4) S1''' S2'''  M'' v5 v6 TBool p false pempty (por e1 (por e2 q1)).
Proof.
  intros. 
  destruct E1 as [IE1 [IE2 [SC [ST [SF1 [SF2 [HV [HQ1 HQ2]]]]]]]].
  destruct v1; destruct v2; try solve [inversion HV]. simpl in HV.
  destruct HV as [HT [LS1 [LS2 VT]]].
  remember ST as ST'. clear HeqST'.
  destruct ST as [STL1 [STL2 [SP1 [SP2 SP3]]]].

  destruct E2 as [IE3 [IE4 [SC2 [ST2 [SF3 [SF4 [HV1 [HQ3 HQ4]]]]]]]].
  destruct v3; destruct v4; try solve [inversion HV1]. simpl in HV1.
  subst b0.
  remember ST2 as ST2'. clear HeqST2'.
  destruct ST2 as [STL3 [STL4 [SP4 [SP5 SP6]]]].

  exists S1'', S2''.
  exists M'', (vbool (b && b1)), (vbool (b && b1)).
  split. 2: split. 3: split. 4: split. 
  (* first one *)
  destruct IE1 as [n1 IE1].
  destruct IE3 as [n3 IE3].
  exists (S(n1 + n3)). intros. destruct n. intuition.
  simpl. rewrite IE1. rewrite IE3. eauto. lia. lia.
  destruct IE2 as [n2 IE2].
  destruct IE4 as [n4 IE4].
  exists (S(n2 + n4)). intros. destruct n. intuition.
  simpl. rewrite IE2. rewrite IE4. eauto. lia. lia. 

  eapply st_trans; eauto.  
  
  (* store typing *)
  eauto.

  split. eapply se_trans; eapply se_sub; eauto; eapply vl_mono; eauto.
  split. eapply se_trans; eapply se_sub; eauto; eapply vl_mono; eauto. 

  split. simpl. eauto. 
  split. eapply valq_bool. eapply valq_bool.
Qed.

Lemma bi_qsub: forall S1 S2 S1' S2' M H1 H2 t1 t2 M' T p q q' e e' v1 v2 fr1 fr2,  
  exp_type S1 S2 M H1 H2 t1 t2 S1' S2' M' v1 v2 T p fr1 q e ->
  psub q q' ->
  psub e e' ->
  psub q' (pdom H1)  ->
  psub q' (pdom H2)  ->
  psub e' (pdom H1)  ->
  psub e' (pdom H2)  ->
  exists S1'' S2'' M'' v1' v2',
  exp_type S1 S2 M H1 H2 t1 t2 S1'' S2'' M'' v1' v2' T p (fr1||fr2) q' e'.
Proof.  
  intros.
  exists S1', S2', M', v1, v2.
  destruct H as [IE1 [IE2 [ISC [IST [ISP1 [ISP2 [IVAL [IQ1 IQ2]]]]]]]]. 
  split. eauto. split. eauto.
  split. eauto. split. eauto.
  split. eauto. split. eauto.
  split. eauto. 
  split. unfold val_qual in IQ1; intuition. eapply valq_sub; eauto.
  intros ? ?. unfoldq; intuition. intros ? ?. unfoldq; intuition.
  unfold val_qual in IQ2; intuition.
  eapply valq_sub; eauto.
  intros ? ?. unfoldq; intuition. intros ? ?. unfoldq; intuition.
Qed.



Theorem fundamental_property : forall t G T p fr q e
  (W: has_type G t T p fr q e),
  forall M H1 H2, env_type M H1 H2 G (plift p) ->
  forall S1 S2, store_type S1 S2 M ->
  exists S1' S2' M' v1 v2,
  exp_type S1 S2 M H1 H2 t t S1' S2' M' v1 v2 T (plift p) fr (plift q)  (plift e).
Proof.
  intros ? ?  ? ? ? ? ? ?.
  induction W; intros ? ? ? WFE ? ? ST.

  - (* Case "True". *)
    exists S1. exists S2. exists M.
    exists (vbool true), (vbool true).
    eapply bi_vtrue; auto.
  - (* Case "False". *)
    exists S1. exists S2. exists M.
    exists (vbool false), (vbool false).
    eapply bi_vfalse; auto.
  - (* Case "Var". *)
    exists S1. exists S2. exists M.
    rewrite plift_one. rewrite plift_empty.
    eapply bi_var; eauto. 
  - (* Case "Ref". *)
    specialize (IHW M  H1 H2); intuition.
    destruct (H S1 S2 ST) as [S1' [S2' [M' [v1 [v2 IE]]]]].
    eapply bi_tref; eauto.
  - (* Case "Get". *)
    specialize (IHW M  H1 H2); intuition.
    destruct (H S1 S2 ST) as [S1' [S2' [M' [v1 [v2 IE]]]]].
    rewrite plift_empty. rewrite plift_or.
    eapply bi_tget; eauto.
  - (* Case "Put". *)
    specialize (IHW1 M H1 H2 WFE S1 S2 ST) as [S1' [S2' [M' [v1 [v2 IE]]]]].
    assert (st_chain M M'). eapply IE. 
    assert (env_type M' H1 H2 env (plift p)) as WFE1. eapply envt_store_extend; eauto. 
    assert (store_type S1' S2' M') as ST'. eapply IE.
    specialize (IHW2 M' H1 H2 WFE1 S1' S2' ST') as [S1'' [S2'' [M'' [v3 [v4 IE2]]]]].
    repeat rewrite plift_or. rewrite plift_empty. 
    eapply bi_put; eauto.
  - (* Case tapp *)
    specialize (IHW1 M H2 H3 WFE S1 S2 ST) as [S1' [S2' [M' [v1 [v2 IE]]]]].
    assert (st_chain M M'). eapply IE. 
    assert (env_type M' H2 H3 env (plift p)) as WFE1. eapply envt_store_extend; eauto.
    assert (store_type S1' S2' M') as ST'. eapply IE.
    specialize (IHW2 M' H2 H3 WFE1 S1' S2' ST') as [S1'' [S2'' [M'' [v3 [v4 IE2]]]]].
    repeat rewrite plift_or. 
    eapply bi_tapp; eauto.
  - (* Case tabs *)
    eapply bi_tabs; eauto.
  - (* Case tseq *)
    repeat rewrite plift_or in *. rewrite plift_empty in *. 
    assert (env_type M H2 H3 env (plift p1)) as WFE0. eapply envt_tighten; eauto. unfoldq. intuition.
    specialize (IHW1 M H2 H3 WFE0 S1 S2 ST) as [S1' [S2' [M' [v1 [v2 IE]]]]].
    assert (st_chain M M'). eapply IE. 
    assert (env_type M' H2 H3 env (plift p2)) as WFE1. eapply envt_store_extend; eauto. eapply envt_tighten. eapply WFE. eauto. 
    assert (store_type S1' S2' M') as ST'. eapply IE.
    specialize (IHW2 M' H2 H3 WFE1 S1' S2' ST') as [S1'' [S2'' [M'' [v3 [v4 IE2]]]]].
    eapply bi_seq; eauto. 
  - (* Case qsub  *)
    specialize (IHW M H3 H4 WFE S1 S2 ST) as [S1' [S2' [M' [v1 [v2 IE]]]]].
    eapply bi_qsub; eauto. 
    all: apply wf_env_type in WFE; intuition.
    1,3: rewrite H6. 1,2: unfoldq; intuition.
    1,2: rewrite H8. 1,2: unfoldq; intuition.  
Qed.



(* ---------- store invariance / localization ---------- *)



Definition st_empty (S1 S2: stor): stty := (length S1, length S2, fun l1 l2 => False).

Lemma stchain_empty: forall S1 S2 M,
    st_chain_partial M (st_empty S1 S2) pempty pempty.
Proof.
  intros. unfold st_chain_partial, st_empty, st_locs1, length1 in *. simpl. intuition.
  intros ? ?. unfoldq. intuition.
  intros ? ?. unfoldq. intuition.
  intros ? ?. unfoldq. intuition.
  intros ? ?. unfoldq. intuition.
Qed.

Lemma stchain_empty': forall M M',
    st_chain_partial M M' pempty pempty.
Proof.
  intros. unfold st_chain_partial, st_empty, st_locs1, length1 in *. simpl. intuition.
  intros ? ?. unfoldq. intuition.
  intros ? ?. unfoldq. intuition.
  intros ? ?. unfoldq. intuition.
  intros ? ?. unfoldq. intuition.
Qed.


Lemma stchain_empty2: forall S1 S2 M,
    st_chain_partial2 (st_empty S1 S2) M pempty pempty.
Proof.
  intros. 
  unfold st_chain_partial2, st_empty, st_locs1, length1, length2 in *.  simpl. intuition.
  intros ? ?. unfoldq. intuition.
  intros ? ?. unfoldq. intuition.
  intros ? ?. unfoldq. intuition.
  intros ? ?. unfoldq. intuition.
Qed.


Lemma stchain_empty2': forall M M',
    st_chain_partial2 M M' pempty pempty.
Proof.
  intros. 
  unfold st_chain_partial2, st_empty, st_locs1, length1, length2 in *.  simpl. intuition.
  intros ? ?. unfoldq. intuition.
  intros ? ?. unfoldq. intuition.
  intros ? ?. unfoldq. intuition.
  intros ? ?. unfoldq. intuition.
Qed.

Lemma storet_empty: forall S1 S2,
    store_type S1 S2 (st_empty S1 S2).
Proof.
  intros. unfold st_empty. 
  split. 2: split. 3: split. 4: split. 
  eauto. eauto.
  intros. destruct H.
  intros. destruct H.
  intros. destruct H. 
Qed.

Definition st_tight (S1 S2: stor): stty := (length S1, length S2, fun l1 l2 => False).

Lemma valq_val_locs_empty: forall M1 M2 H v,
  val_qual M1 M2 H v false pempty ->
  val_locs v = pempty.
Proof.
  intros. eapply functional_extensionality.
  intros. eapply propositional_extensionality.
  split; intros.
  destruct (H0 x); auto. unfoldq; intuition. 
  destruct H2 as [? [? ?]]. contradiction.
  unfoldq; intuition. 
Qed.


Lemma val_locs_empty:  forall t G T q e
  (W: has_type G t T qempty false q e),
  forall  S1 S2 P H1 H2, 
     env_type ((length S1), (length S2), P) H1 H2 G (plift qempty) ->
  exists S1' S2'  v1 v2,
    tevaln S1 H1 t S1' v1 /\
    tevaln S2 H2 t S2' v2 /\
    val_locs v1 = pempty /\
    val_locs v2 = pempty.
Proof.
  intros.
  eapply fundamental_property with (S1 := S1) (S2 := S2) in W. 
  2: {
    eapply envt_store_change with (M' := (st_empty S1 S2)).
    eauto. rewrite plift_empty. repeat rewrite vars_locs_empty.
    eapply stchain_empty. 
    rewrite plift_empty. repeat rewrite vars_locs_empty. eapply stchain_empty2.
  }
  2: { eapply storet_empty. }
  
  destruct W as [S1' [S2' [M' [v1 [v2 [? ?]]]]]]; intuition.
  exists S1', S2', v1, v2; intuition.
  1,2: rewrite plift_empty in *; replace (pand pempty (plift q)) with pempty in H9, H11.
       eapply valq_val_locs_empty; eauto.
  2: eapply valq_val_locs_empty; eauto.
  eapply functional_extensionality.
  intros. eapply propositional_extensionality. unfoldq; intuition.
  eapply functional_extensionality.
  intros. eapply propositional_extensionality. unfoldq; intuition.
Qed.  


(* Theorem: if an expression typechecks with p = empty,
            we can evaluate it in ANY two stores S1, S2
            to equivalent values v1, v2. *)

Theorem store_invariance : forall t G T q e
  (W: has_type G t T qempty false q e),
  forall M H1 H2, env_type M H1 H2 G (plift qempty) ->
  forall S1 S2, (* <---- NO store_type required! *)
  exists S1' S2' M' v1 v2,
  exp_type S1 S2 (st_empty S1 S2) H1 H2 t t S1' S2' M' v1 v2 T (plift qempty) false (plift q) (plift e).
Proof.
  intros.
  eapply fundamental_property; eauto.
  eapply envt_store_change. eauto.
  eapply stchain_tighten. eapply stchain_empty.
  intros ? [? ?]. unfoldq. intuition.
  intros ? [? ?]. unfoldq. intuition.
  rewrite plift_empty. repeat rewrite vars_locs_empty. 
  eapply stchain_empty2.
  eapply storet_empty. 
Qed.


(* not related locations do not matter *)
Theorem store_invariance2 : forall t G T p p' fr q e
  (W: has_type G t T p fr q e),
  forall M H1 H2, env_type M H1 H2 G (plift p) ->
  forall S1 S2, store_type S1 S2 M ->
                (forall l1 l2, strel M l1 l2 -> ~ p' l1) ->
  forall S1', store_effect S1 S1' p' ->
                 length S1 <= length S1' ->
  exists S1'' S2' M' v1 v2,
  exp_type S1' S2 (length S1', length S2, strel M) H1 H2 t t S1'' S2' M' v1 v2 T (plift p) fr (plift q) (plift e).
Proof.
  intros. 
  eapply fundamental_property; eauto.
  eapply envt_store_change. eauto.

  assert (psub (vars_locs H1 (plift p)) (st_locs1 M)). {
    eapply env_type_store_wf; eauto. intros ? ?. eauto. }
  assert (psub (vars_locs H2 (plift p)) (st_locs2 M)). {
    eapply env_type_store_wf; eauto. intros ? ?. eauto. }
  unfold st_chain_partial. simpl. 
  intuition.
  intros ? ?. eapply H6 in H8.
  unfold st_locs1, pnat, length1. simpl.
  unfold st_locs1, pnat in H8.
  destruct H0. lia.
  intros ? ?. eapply H7 in H8.
  unfold st_locs2, pnat, length2. simpl.
  unfold st_locs2, pnat in H8.
  destruct H0. lia.
 
  assert (psub (vars_locs H1 (plift p)) (st_locs1 M)). {
    eapply env_type_store_wf; eauto. intros ? ?. eauto. }
  assert (psub (vars_locs H2 (plift p)) (st_locs2 M)). {
    eapply env_type_store_wf; eauto. intros ? ?. eauto. }
  unfold st_chain_partial2. simpl. 
  intuition.
  intros ? ?. eapply H6 in H8.
  unfold st_locs1, pnat, length1. simpl.
  unfold st_locs1, pnat in H8.
  destruct H0. lia.
  intros ? ?. eapply H7 in H8.
  unfold st_locs2, pnat, length2. simpl.
  unfold st_locs2, pnat in H8.
  destruct H0. lia.
  
  (* store type *)
  destruct H0 as (? & ? & P1 & P2 & P3).
  split. 2: split. 3: split. 4: split.
  - unfold length1. simpl. eauto.
  - eauto.
  - intros ? ? STR. simpl in STR. 
    destruct (P1 l1 l2) as (b1 & b2 & IX1 & IX2). eauto.
    exists b1, b2. split. 2: eauto.
    eapply H4. eauto. eauto. 
  - simpl. eauto.
  - simpl. eauto. 
Qed.


Theorem store_invariance3 : forall t G T p p' fr q e
  (W: has_type G t T p fr q e),
  forall M H1 H2, env_type M H1 H2 G (plift p) ->
  forall S1 S2, store_type S1 S2 M ->
                (forall l1 l2, strel M l1 l2 -> ~ p' l2) ->
  forall S2', store_effect S2 S2' p' ->
                 length S2 <= length S2' ->
  exists S1' S2'' M' v1 v2,
  exp_type S1 S2' (length S1, length S2', strel M) H1 H2 t t S1' S2'' M' v1 v2 T (plift p) fr (plift q) (plift e).
Proof. 
  intros. 
  eapply fundamental_property; eauto.
  eapply envt_store_change. eauto.

  assert (psub (vars_locs H1 (plift p)) (st_locs1 M)). {
    eapply env_type_store_wf; eauto. intros ? ?. eauto. }
  assert (psub (vars_locs H2 (plift p)) (st_locs2 M)). {
    eapply env_type_store_wf; eauto. intros ? ?. eauto. }
  unfold st_chain_partial. simpl. 
  intuition.
  intros ? ?. eapply H6 in H8.
  unfold st_locs1, pnat, length1. simpl.
  unfold st_locs1, pnat in H8.
  destruct H0. lia.
  intros ? ?. eapply H7 in H8.
  unfold st_locs2, pnat, length2. simpl.
  unfold st_locs2, pnat in H8.
  destruct H0. lia.
 
  assert (psub (vars_locs H1 (plift p)) (st_locs1 M)). {
    eapply env_type_store_wf; eauto. intros ? ?. eauto. }
  assert (psub (vars_locs H2 (plift p)) (st_locs2 M)). {
    eapply env_type_store_wf; eauto. intros ? ?. eauto. }
  unfold st_chain_partial2. simpl. 
  intuition.
  intros ? ?. eapply H6 in H8.
  unfold st_locs1, pnat, length1. simpl.
  unfold st_locs1, pnat in H8.
  destruct H0. lia.
  intros ? ?. eapply H7 in H8.
  unfold st_locs2, pnat, length2. simpl.
  unfold st_locs2, pnat in H8.
  destruct H0. lia.

  (* store type *)
  destruct H0 as (? & ? & P1 & P2 & P3).
  split. 2: split. 3: split. 4: split.
  - unfold length1. simpl. eauto.
  - eauto.
  - intros ? ? STR. simpl in STR. 
    destruct (P1 l1 l2) as (b1 & b2 & IX1 & IX2 & ?). eauto.
    exists b1, b2. split. 2: split.
    auto.  eapply H4. eauto. eauto. auto. 
  - simpl. eauto.
  - simpl. eauto. 
Qed.


Definition st_tighten H1 (H2: venv) p M :=
  (length1 M, length2 M, fun l1 l2 => vars_locs H1 p l1 /\ vars_locs H2 p l2 /\ strel M l1 l2).


Definition st_tighten1 H1 (H2: venv) p M :=
  (length1 M, length2 M, fun l1 l2 => vars_locs H1 p l1 /\ vars_locs H2 p l2 /\ strel M l1 l2).


(* localization *)
Theorem store_invariance2' : forall t G T p fr q e 
  (W: has_type G t T p fr q e),
  forall M H1 H2, env_type M H1 H2 G (plift p) ->
  forall S1 S2, store_type S1 S2 M ->
  forall S1' p', store_effect S1 S1' p' ->  
                 length S1 <= length S1' ->
                 psub (pand (vars_locs H1 (plift p)) p') pempty ->
  exists S1'' S2' M' v1 v2,
  exp_type S1' S2 (length S1', length S2, fun l1 l2 => vars_locs H1 (plift p) l1 /\ vars_locs H2 (plift p) l2 /\ strel M l1 l2) H1 H2 t t S1'' S2' M' v1 v2 T (plift p) fr (plift q) (plift e).
Proof.
  intros.
  remember (length S1, length S2, fun l1 l2 => vars_locs H1 (plift p) l1 /\ vars_locs H2 (plift p) l2 /\ strel M l1 l2) as Q.
  assert (st_chain_partial M Q (vars_locs H1 (plift p)) (vars_locs H2 (plift p))). {
    assert (psub (vars_locs H1 (plift p)) (st_locs1 M)). {
      eapply env_type_store_wf; eauto. intros ? ?. eauto. }
    assert (psub (vars_locs H2 (plift p)) (st_locs2 M)). {
      eapply env_type_store_wf; eauto. intros ? ?. eauto. }
    assert (st_locs1 Q = st_locs1 M). {
     subst Q. unfold st_locs1, pnat. 
     unfold store_type in H0. destruct H0 as (? & ? & ?).
     rewrite H0. intuition.
    }
    assert (st_locs2 Q = st_locs2 M). { 
      subst Q. unfold st_locs2, pnat. simpl.
      unfold store_type in H0. destruct H0 as (? & ? & ?).
      rewrite H9. intuition.
    }
    unfold st_chain_partial. intuition.
    + rewrite H8. eauto.
    + rewrite H9. eauto. 
    + subst Q. simpl. intuition.
  }

  assert (st_chain_partial2 Q M (vars_locs H1 (plift p)) (vars_locs H2 (plift p))) as B. {
    assert (psub (vars_locs H1 (plift p)) (st_locs1 M)). {
      eapply env_type_store_wf; eauto. intros ? ?. eauto. }
    assert (psub (vars_locs H2 (plift p)) (st_locs2 M)). {
      eapply env_type_store_wf; eauto. intros ? ?. eauto. }
    assert (st_locs1 Q = st_locs1 M). {
     subst Q. unfold st_locs1, pnat. 
     unfold store_type in H0. destruct H0 as (? & ? & ?).
     rewrite H0. intuition.
    }
    assert (st_locs2 Q = st_locs2 M) as A. { 
      subst Q. unfold st_locs2, pnat. simpl.
      unfold store_type in H0. destruct H0 as (? & ? & ?).
      rewrite H10. intuition.
    }
    unfold st_chain_partial2. intuition.
    + rewrite H9. eauto.
    + rewrite A. eauto. 
    + subst Q. simpl in *. intuition.
    + subst Q. simpl in *. intuition.
  }

  eapply store_invariance2 with (M:=Q) (S1:=S1) (S2:=S2) (S1':=S1') (p':=p') in W.
  2: { eapply envt_store_change; eauto.
     }
  2: { subst Q. destruct H0 as (? & ? & ? & ? & ?).
       split. unfold length1. simpl. eauto.
       split. unfold length2. simpl. eauto.
       split. intros. simpl in H11. eapply H8. eapply H11.
       simpl. intuition; eauto. }
  2: { intros. subst Q. simpl in *. intros ?.
       eapply H5. unfoldq. intuition. eauto. eauto. }
  2: eauto.
  2: eauto.

  subst Q. simpl. destruct W as (? & ? & ? & ? & ? & ?).
  eexists. eexists. eexists. eexists. eexists.

  eapply H7.
Qed. 

Theorem store_invariance3' : forall t G T p fr q e
  (W: has_type G t T p fr q e),
  forall M H1 H2, env_type M H1 H2 G (plift p) ->
  forall S1 S2, store_type S1 S2 M ->
  forall S2' p', store_effect S2 S2' p' ->  
                 length S2 <= length S2' ->
                 psub (pand (vars_locs H2 (plift p)) p') pempty ->
  exists S1' S2'' M' v1 v2,
  exp_type S1 S2' (length S1, length S2', fun l1 l2 => vars_locs H1 (plift p) l1 /\ vars_locs H2 (plift p) l2 /\ strel M l1 l2) H1 H2 t t S1' S2'' M' v1 v2 T (plift p) fr (plift q) (plift e).
Proof.
  intros.
  remember (length S1, length S2, fun l1 l2 => vars_locs H1 (plift p) l1 /\ vars_locs H2 (plift p) l2 /\ strel M l1 l2) as Q.
  assert (st_chain_partial M Q (vars_locs H1 (plift p)) (vars_locs H2 (plift p))). {
    assert (psub (vars_locs H1 (plift p)) (st_locs1 M)). {
      eapply env_type_store_wf; eauto. intros ? ?. eauto. }
    assert (psub (vars_locs H2 (plift p)) (st_locs2 M)). {
      eapply env_type_store_wf; eauto. intros ? ?. eauto. }
    assert (st_locs1 Q = st_locs1 M). {
     subst Q. unfold st_locs1, pnat. 
     unfold store_type in H0. destruct H0 as (? & ? & ?).
     rewrite H0. intuition.
    }
    assert (st_locs2 Q = st_locs2 M). { 
      subst Q. unfold st_locs2, pnat. simpl.
      unfold store_type in H0. destruct H0 as (? & ? & ?).
      rewrite H9. intuition.
    }
    unfold st_chain_partial. intuition.
    + rewrite H8. eauto.
    + rewrite H9. eauto. 
    + subst Q. simpl. intuition.
  }

  assert (st_chain_partial2 Q M (vars_locs H1 (plift p)) (vars_locs H2 (plift p))) as B. {
    assert (psub (vars_locs H1 (plift p)) (st_locs1 M)). {
      eapply env_type_store_wf; eauto. intros ? ?. eauto. }
    assert (psub (vars_locs H2 (plift p)) (st_locs2 M)). {
      eapply env_type_store_wf; eauto. intros ? ?. eauto. }
    assert (st_locs1 Q = st_locs1 M). {
     subst Q. unfold st_locs1, pnat. 
     unfold store_type in H0. destruct H0 as (? & ? & ?).
     rewrite H0. intuition.
    }
    assert (st_locs2 Q = st_locs2 M) as A. { 
      subst Q. unfold st_locs2, pnat. simpl.
      unfold store_type in H0. destruct H0 as (? & ? & ?).
      rewrite H10. intuition.
    }
    unfold st_chain_partial2. intuition.
    + rewrite H9. eauto.
    + rewrite A. eauto. 
    + subst Q. simpl in *. intuition.
    + subst Q. simpl in *. intuition.
  }

  eapply store_invariance3 with (M:=Q) (S1:=S1) (S2:=S2) (S2':=S2') (p':=p') in W.
  2: { eapply envt_store_change; eauto. }
  2: { subst Q. destruct H0 as (? & ? & ? & ? & ?).
       split. unfold length1. simpl. eauto.
       split. unfold length2. simpl. eauto.
       split. intros. simpl in H11. eapply H8. eapply H11.
       simpl. intuition; eauto. }
  2: { intros. subst Q. simpl in *. intros ?.
       eapply H5. unfoldq. intuition. eauto. eauto. 
     }
  2: eauto.
  2: eauto.

  subst Q. simpl. destruct W as (? & ? & ? & ? & ? & ?).
  eexists. eexists. eexists. eexists. eexists.

  eapply H7.
Qed.

Lemma vars_locs_sep1: forall p1 p2 p H1 H2 M G l
  (WFE: env_type M H1 H2 G p),
  psub p1 p ->
  psub p2 p ->
  psub (pand p1 p2) pempty ->
  vars_locs H1 p1 l ->
  ~ vars_locs H1 p2 l.
Proof.
  intros. intros ?. unfold psub, pand in H3.
  destruct H4 as [? [? ?]].
  destruct H5 as [? [? ?]].
  assert (p x). specialize (H x); intuition. 
  assert (p x0). specialize (H0 x0); intuition. 
  assert (x = x0). destruct WFE as [? [? [? [? [? [Y ?]]]]]]. eapply Y; eauto.  
  subst.
  specialize (H3 x0); intuition.
Qed.

Lemma vars_locs_sep2: forall p1 p2 p H1 H2 M G l
  (WFE: env_type M H1 H2 G p),
  psub p1 p ->
  psub p2 p ->
  psub (pand p1 p2) pempty ->
  vars_locs H2 p1 l ->
  ~ vars_locs H2 p2 l.
Proof.
  intros. intros ?. unfold psub, pand in H3.
  destruct H4 as [? [? ?]].
  destruct H5 as [? [? ?]].
  assert (p x). specialize (H x); intuition. 
  assert (p x0). specialize (H0 x0); intuition. 
  assert (x = x0). destruct WFE as [? [? [? [? [? [? Y]]]]]]. eapply Y; eauto.  
  subst.
  specialize (H3 x0); intuition.
Qed.


Theorem reorder_seq : forall t1 t2 G T p q e
  (W: has_type G (tseq t1 t2) T p false q e),
  forall M H1 H2, env_type M H1 H2 G (plift p) ->
  forall S1 S2, store_type S1 S2 M ->
  exists S1' S2' M' v1 v2,
  exp_type S1 S2 M H1 H2 (tseq t1 t2) (tseq t2 t1) S1' S2' M' v1 v2 T (plift p) false (plift q) (plift e).
Proof.
  intros ? ? ? ? ? ? ? W. remember (tseq t1 t2) as t. induction W; inversion Heqt. 
  - (* t_seq *)
    rename H3 into H3x. rename H4 into H4x.
    intros ? ? ? WFE ? ? ST. subst t0 t3. remember ST as STXX. clear HeqSTXX.

    assert (exists S1' S1x' M' v1 v1x, exp_type S1 S2 M H2 H3 t1 t1 S1' S1x' M' v1 v1x TBool (plift p1) false (plift q1) (plift e1)) as A. {
      eapply fundamental_property. eapply W1.
      eapply envt_tighten. eauto. eauto. eauto.
    } 

    destruct A as (S1' & S1x' & M' & v1 & v1x & E1 & E1x & ? & ? & SE1 & SE1x & ? & ? & ?). 

    assert (length S1 = length1 M). destruct ST. eauto. 
    assert (length S1' = length1 M'). destruct H5. eauto.
    assert (length S1 <= length S1'). eapply st_mono1 in H4. lia. 

    
    assert (exists S1'' S2' M'' v2 v2x,
               exp_type S1' S2
                 (length S1', length S2, fun l1 l2 => vars_locs H2 (plift p2) l1 /\ vars_locs H3 (plift p2) l2 /\ strel M l1 l2)
                 H2 H3 t2 t2 S1'' S2' M'' v2 v2x TBool (plift p2) false (plift q2) (plift e2)) as B. {
      eapply store_invariance2'. eapply W2.
      eapply envt_tighten. eauto. eauto.
      eauto.
      eauto.
      eauto.
      (* separation *)
      intros ? ?. eapply vars_locs_dist_and1 in WFE. rewrite WFE in H12. all: eauto.
      destruct H12. destruct H12. destruct (H x0). unfoldq. intuition. 
    }
      
    destruct B as (S1'' & S2' & M'' & v2 & v2x & E2' & E2 & ? & ? & SE2' & SE2 & ? & ? & ?).

    assert (length S2 <= length S2') as X. eapply st_mono2 in H12. unfold length2 in H12. simpl in H12. unfold store_type in H13. destruct H13 as (? & ? & ?). unfold length2  in H17. lia.
    assert (exists S1y' S2'' M''' v1y v1z,
               exp_type S1 S2'
                 (length S1, length S2', fun l1 l2 => vars_locs H2 (plift p1) l1 /\ vars_locs H3 (plift p1) l2 /\ strel M l1 l2)
                 H2 H3 t1 t1 S1y' S2'' M''' v1y v1z TBool (plift p1) false (plift q1) (plift e1)) as C. {
      eapply store_invariance3'. eapply W1.
      eapply envt_tighten. eauto. eauto.
      eauto.
      eauto.
      eauto.
      (* separation *)
      intros ? ?. eapply vars_locs_dist_and2 in WFE. rewrite WFE in H17. all: eauto.
      destruct H17. destruct H17. destruct (H x0). unfoldq. intuition. 
      
    }

    destruct C as (S1y' & S2'' & M''' & v1y & v1z & E1y & E2'' & ? & ? & SE1y & SE2'' & ? & ? & ?).     

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

    destruct v1; destruct v1x; destruct v1z; simpl in H6; simpl in H19; intuition. subst b0 b1.
    destruct v2; destruct v2x; simpl in H14; intuition. subst b0.
    
    assert (tevaln S1 H2 (tseq t1 t2) S1'' (vbool (b && b1))). {
      destruct E1 as [n1 E1].
      destruct E2' as [n1' E1'].
      exists (1+n1+n1'). intros.
      destruct n. lia. simpl.
      rewrite E1, E1'. eauto. lia. lia. 
    }

    assert (tevaln S2 H3 (tseq t2 t1) S2'' (vbool (b1 && b))). {
      destruct E2 as [n1 E2].
      destruct E2'' as [n1' E1'].
      exists (1+n1+n1'). intros.
      destruct n. lia. simpl.
      rewrite E2, E1'. eauto. lia. lia. 
    }

    assert (b && b1 = b1 && b). eauto with bool.
    rewrite H19 in *. 
(*
   H4 : st_chain M M'
   H12 : st_chain (length S1', length S2, ...) M''
   H17 : st_chain (length S1, length S2, ...) M'''
  
   ST : store_type S1 S2 M
   H7 : store_type S1'' S2' M''
   H12 : store_type S1' S2'' M'''

   Need to set up MM such that:

   st_chain M MM
   store_type S1'' S2'' MM
*)    

    destruct ST as (? & ? & ?).
    destruct H13 as (? & ? & ?).
    destruct H18 as (? & ? & ?).

    assert (forall S1 S2, length1 (st_empty S1 S2) = length S1) as R1. intros. unfold length1. simpl. eauto.
    assert (forall S1 S2, length2 (st_empty S1 S2) = length S2) as R2. intros. unfold length2. simpl. eauto.
    
    assert (length S1 <= length S1'). eapply st_mono1 in H4. lia. 
    assert (length S2 <= length S2'). eapply st_mono2 in H4. eapply st_mono2 in H12.  unfold length2 in H12. simpl in H12. unfold length2 in H25. lia.
    assert (length S1' <= length S1'').  eapply st_mono1 in H12.  unfold length1 in H12. simpl in H12. unfold length1 in H13. lia. 
    assert (length S2' <= length S2''). eapply st_mono2 in H17. unfold length2 in H17. simpl in H17. unfold length2 in H27. lia. 

    assert (forall l1 l2,
               l1 < length S1 \/ l2 < length S2' ->
               strel M''' l1 l2 ->
               vars_locs H2 (plift p1) l1 /\ vars_locs H3 (plift p1) l2 /\ strel M l1 l2
      ) as CES'''. {
      intros. eapply H17. unfold st_locs1, st_locs2, length1, length2, st_empty. simpl.
      unfoldq. lia. eauto.
    }

    assert (forall l1 l2,
               l1 < length S1' \/ l2 < length S2 ->
               strel M'' l1 l2 ->
               vars_locs H2 (plift p2) l1 /\ vars_locs H3 (plift p2) l2 /\ strel M l1 l2) as CES''. {
      intros. eapply H12. unfold st_locs1, st_locs2, length1, length2, st_empty. simpl. unfoldq. lia. eauto. 
    }

    



    remember (length S1'', length S2'',
               fun l1 l2 =>
                 strel M l1 l2 /\
                   ~ vars_locs H2 (plift p1) l1 /\
                   ~ vars_locs H3 (plift p1) l2 /\
                   ~ vars_locs H2 (plift p2) l1 /\
                   ~ vars_locs H3 (plift p2) l2 \/
                 strel M''' l1 l2 /\
                     vars_locs H2 (plift p1) l1 /\
                     vars_locs H3 (plift p1) l2 
                 (*  ~ vars_locs H2 (plift p2) l1 /\
                   ~ vars_locs H3 (plift p2) l2 *) \/
                 strel M'' l1 l2 /\
                   (* ~ vars_locs H2 (plift p1) l1 /\
                   ~ vars_locs H3 (plift p1) l2  *)
                    vars_locs H2 (plift p2) l1 /\
                    vars_locs H3 (plift p2) l2
              ) as MM.

    assert (forall a b, a || b = b || a) as RS. { intros. eauto with bool. }
    
    assert (st_chain M MM). {
      subst MM. unfold st_chain. unfold st_chain_partial, st_chain_partial2. split.
      - simpl. intuition.
        + unfoldq; intuition.
        + unfoldq; intuition. unfold st_locs1, pnat, length1. simpl.
          unfold st_locs1, pnat in H36. lia. 
        + unfoldq; intuition.
        + unfoldq; intuition. unfold st_locs2, pnat, length2. simpl.
          unfold st_locs2, pnat in H36. lia.
        + (* decidable vars_locs *)
          assert (vars_locs H2 (plift p1) l1 \/ ~vars_locs H2 (plift p1) l1). eapply vars_locs_decide.
          assert (vars_locs H3 (plift p1) l2 \/ ~vars_locs H3 (plift p1) l2). eapply vars_locs_decide.
          assert (vars_locs H2 (plift p2) l1 \/ ~vars_locs H2 (plift p2) l1). eapply vars_locs_decide.
          assert (vars_locs H3 (plift p2) l2 \/ ~vars_locs H3 (plift p2) l2). eapply vars_locs_decide.

          (* separation *)
          assert (forall l, vars_locs H2 (plift p1) l -> vars_locs H2 (plift p2) l -> False) as SEP1. {
            intros. unfold psub, pand in H.
            unfold vars_locs in H46, H47.
            destruct H46 as [? [? ?]]. destruct H47 as [? [? ?]].
            assert (plift p x). specialize (H0 x); intuition. 
            assert (plift p x0). specialize (H0 x0); intuition. 
            assert (x = x0). destruct WFE as [? [? [? [? [? [Y ?]]]]]]. eapply Y; eauto.  
            subst.
            specialize (H x0); intuition.
          }

          assert (forall l, vars_locs H3 (plift p1) l -> vars_locs H3 (plift p2) l -> False) as SEP1X. {
            intros. unfold psub, pand in H.
            unfold vars_locs in H46, H47.
            destruct H46 as [? [? ?]]. destruct H47 as [? [? ?]].
            assert (plift p x). specialize (H0 x); intuition. 
            assert (plift p x0). specialize (H0 x0); intuition. 
            assert (x = x0). destruct WFE as [? [? [? [? [? [? Y]]]]]]. eapply Y; eauto.  
            subst.
            specialize (H x0); intuition.
          }

          (* TODO: check !!! *)

          assert (vars_locs H2 (plift p1) l1 -> ~ vars_locs H3 (plift p1) l2 -> False) as SEP2. {
            intros. eapply H47. edestruct envt_same_locs with (p1:=plift p1). 2: eauto. eauto. eauto. eauto.
            eauto. 
          }

           assert (vars_locs H2 (plift p2) l1 -> ~ vars_locs H3 (plift p2) l2 -> False) as SEP3. {
            intros. eapply H47. edestruct envt_same_locs with (p1:=plift p2). 2: eauto. eauto. eauto. eauto.
            eauto. 
          }

          assert (vars_locs H3 (plift p1) l2 -> ~ vars_locs H2 (plift p1) l1 -> False) as SEP4. {
            intros. eapply H47. edestruct envt_same_locs with (p1:=plift p1). 2: eauto. eauto. eauto. eauto.
            eauto. 
          }

           assert (vars_locs H3 (plift p2) l2 -> ~ vars_locs H2 (plift p2) l1 -> False) as SEP5. {
            intros. eapply H47. edestruct envt_same_locs with (p1:=plift p2). 2: eauto. eauto. eauto. eauto.
            eauto. 
          }
          
          destruct H36; destruct H43; destruct H44; destruct H45.

          * (*   p1 l1,   p1 l2,   p2 l1,   p2 l2 *)
            edestruct (SEP1 l1); eauto. 
          * (*   p1 l1,   p1 l2,   p2 l1, ~ p2 l2 *)
            edestruct (SEP1 l1); eauto. 
          * (*   p1 l1,   p1 l2, ~ p2 l1,   p2 l2 *)
            edestruct (SEP1X l2); eauto.
          * (*   p1 l1,   p1 l2, ~ p2 l1, ~ p2 l2 *)
            right. left. intuition. (* M''' *)
            eapply H17. unfold st_locs1, st_locs2, pnat, length1, length2. simpl.
            apply env_type_store_wf  with (q := (plift p)) in WFE.
            destruct WFE as [A B]. 
            rewrite <- H22 in A. rewrite <- H23 in B. 
            assert (vars_locs H2 (plift p) l1) as C. eapply vars_locs_sub; eauto.
            assert (vars_locs H3 (plift p) l2) as D. eapply vars_locs_sub; eauto.
            split.
            unfold psub in A. specialize (A l1); intuition. (* too slow *)
            unfold psub in B. assert (pnat (length S2) l2). eapply B. auto.
            unfold pnat in H48. lia.

            intros ? ?. auto.
            simpl. intuition. 

          * (*   p1 l1, ~ p1 l2,   p2 l1,   p2 l2 *)
            edestruct (SEP1 l1); eauto.
          * (*   p1 l1, ~ p1 l2,   p2 l1, ~ p2 l2 *)
            edestruct (SEP1 l1); eauto.
          * (*   p1 l1, ~ p1 l2, ~ p2 l1,   p2 l2 *)
            right. left. 
            edestruct (SEP2). eauto. eauto. (* ??? *)
          * (*   p1 l1, ~ p1 l2, ~ p2 l1, ~ p2 l2 *)
            right. left. 
            edestruct (SEP2). eauto. eauto.
            
          * (* ~ p1 l1,   p1 l2,   p2 l1,   p2 l2 *)
            edestruct (SEP1X l2); eauto.
          * (* ~ p1 l1,   p1 l2,   p2 l1, ~ p2 l2 *)
            right. right. edestruct (SEP3). eauto. eauto. 
          * (* ~ p1 l1,   p1 l2, ~ p2 l1,   p2 l2 *)
            edestruct (SEP1X l2); eauto.
          * (* ~ p1 l1,   p1 l2, ~ p2 l1, ~ p2 l2 *)
            edestruct (SEP4); eauto.
            
          * (* ~ p1 l1, ~ p1 l2,   p2 l1,   p2 l2 *)
            right. right. intuition. (* M'' *)
            eapply H12. unfold st_locs1, st_locs2, pnat, length1, length2. simpl.
            apply env_type_store_wf  with (q := (plift p)) in WFE.
            destruct WFE as [A B]. 
            rewrite <- H22 in A. rewrite <- H23 in B. 
            assert (vars_locs H2 (plift p) l1) as C. eapply vars_locs_sub; eauto.
            assert (vars_locs H3 (plift p) l2) as D. eapply vars_locs_sub; eauto.
            split.
            unfold psub in A. specialize (A l1); intuition. unfold pnat in H48. lia. (* too slow *)
            unfold psub in B. assert (pnat (length S2) l2). eapply B. auto.
            unfold pnat in H48. lia.
            intros ? ?. auto.
            simpl. intuition. 
          * (* ~ p1 l1, ~ p1 l2,   p2 l1, ~ p2 l2 *)
            edestruct (SEP3); eauto.
          * (* ~ p1 l1, ~ p1 l2, ~ p2 l1,   p2 l2 *)
            edestruct (SEP5); eauto.
          * (* ~ p1 l1, ~ p1 l2, ~ p2 l1, ~ p2 l2 *)
            left. intuition. (* M *)

      - simpl. intuition.
        + unfoldq. intuition. unfold st_locs1, pnat, length1. simpl.
          unfold st_locs1, pnat in H36. lia.
        + unfoldq. intuition.
        + unfoldq. intuition. unfold st_locs2, pnat, length2. simpl.
          unfold st_locs2, pnat in H36. lia.
        + unfoldq. intuition.
        + eapply H17. 2: eauto. left.
          * unfold st_locs1, pnat, length1. simpl. unfold st_locs1 in H41. unfoldq. lia. 
          (* * unfold st_locs2, pnat, length2. simpl. unfold st_locs2 in H42. unfoldq. lia. *)
        + eapply H12. 2: eauto. left.
          * unfold st_locs1, pnat, length1. simpl. unfold st_locs1 in H41. unfoldq. lia. 
            (* * unfold st_locs2, pnat, length2. simpl. unfold st_locs2 in H42. unfoldq. lia. *)
        + eapply H17. 2: eauto. right.
          * unfold st_locs2, pnat, length2. simpl. unfold st_locs2 in H41. unfoldq. lia.
        + eapply H12. 2: eauto. right.
          * unfold st_locs2, pnat, length2. simpl. unfold st_locs2 in H41. unfoldq. lia.
    }

    (* invariants in exp_type:
       1. store_preserve: store outside of vars_locs p is unchanged
       2: st_chain: M1 is a conservative extension of M, i.e., only adds entries larger than size of M *)


    assert (store_type S1'' S2'' MM). {
      clear H27 IHW1 IHW2. 
      (* subst S1' S2' S1'' S2''. *)
      subst MM. unfold store_type; intuition.
      - simpl in H36. destruct H36 as [A | [B | C]].
        + destruct A as (? & ? & ? & ? & ?).
          destruct (H27 l1 l2) as (b0 & b2 & ? & ? & ?). eauto.
          exists b0, b2. split. 2: split.
          eapply SE2'. eauto.  (* ~ p2 l1 *)
          eapply SE1. eauto.   (* ~ p1 l1 *)
          eauto.
          eapply SE2''. eauto. (* ~ p1 l2 *)
          eapply SE2. eauto.   (* ~ p2 l2 *)
          eauto.
          eauto. 

        + destruct B as (? & ? & ?).
          destruct (H26 l1 l2) as (b0 & b2 & ? & ? & ?). eauto.
          exists b0, b2. split. 2: split. 
          eapply SE2'. eapply vars_locs_sep1. eapply WFE. 3: eapply H.
          eauto. eauto. eauto. eauto. eauto. eauto.
        + destruct C as (? & ? & ?).
          destruct (H24 l1 l2) as (b0 & b2 & ? & ? & ?). eauto.
          exists b0, b2. split. 2: split.
          eauto. eapply SE2''. eapply vars_locs_sep2. eapply WFE. 
          3: { assert (psub (pand (plift p2) (plift p1)) pempty). 
            intros ? ?. destruct H45 as [? ?]. eapply H. split; auto.
            eapply H45. }
          eauto. eauto. eauto. eauto. eauto. 
      - simpl in H36, H40.
        destruct H36 as [(A&?) | [(B&?) | (C&?)]]; destruct H40 as [(U&?) | [(V&?) | (W&?)]].
        + eauto.
        + eapply CES''' in V. intuition.
          left. destruct (H27 l1 l2) as (b0 & b2 & IX1 & IX2 & ?); eauto.
          eapply indexr_var_some' in IX1. lia.
        + eapply CES'' in W. simpl in W. intuition. 
          left. destruct (H27 l1 l2) as (b0 & b2 & IX1 & IX2 & ?); eauto.
          eapply indexr_var_some' in IX1. lia.
          
        + eapply CES''' in B. simpl in B. intuition.
          left. destruct (H27 l1 l2') as (b0 & b2 & IX1 & IX2 & ?); eauto.
          eapply indexr_var_some' in IX1. eauto.
        + eauto.
        + eapply CES'' in W. simpl in W. intuition.
          assert (strel M l1 l2). { eapply H17. left. unfold st_locs1, pnat, length1. simpl.
            eapply env_type_store_wf with (q := (plift p2)) in WFE as XX. destruct XX.
            eapply H43 in H44. unfold pnat in H44. lia. auto. auto. }
            destruct STXX as [? [? [? [ U ?]]]]. eapply U; eauto.
          left. destruct (H26 l1 l2) as (b0 & b2 & IX1 & IX2 & ?); eauto.
          eapply indexr_var_some' in IX1. eauto.
          
        + eapply CES'' in C. simpl in C. intuition.
          left. destruct (H27 l1 l2') as (b0 & b2 & IX1 & IX2 & ?); eauto.
          eapply indexr_var_some' in IX1. lia.
        + eapply CES'' in C. simpl in C. intuition.
          assert False. { 
          eapply vars_locs_sep1. eapply WFE. 
            3: { assert (psub (pand (plift p2) (plift p1)) pempty). 
            intros ? ?. destruct H42 as [? ?]. eapply H. split; auto.
            eapply H42. } auto. auto. eauto. eauto.
          }
          contradiction.
          left. destruct (H26 l1 l2') as (b0 & b2 & IX1 & IX2 & ?); eauto.
          eapply indexr_var_some' in IX1. lia.
        + eauto.
      - simpl in H36, H40.
        destruct H36 as [(A&?) | [(B&?) | (C&?)]]; destruct H40 as [(U&?) | [(V&?) | (W&?)]].
        + eauto.
        + eapply CES''' in V. simpl in V. intuition.
          right. destruct (H27 l1 l2) as (b0 & b2 & IX1 & IX2 & ?); eauto.
          eapply indexr_var_some' in IX2. lia.
        + eapply CES'' in W. simpl in W. intuition.
          right. destruct (H27 l1 l2) as (b0 & b2 & IX1 & IX2 & ?); eauto.
          eapply indexr_var_some' in IX2. lia.
          
        + eapply CES''' in B. simpl in B. intuition.
          right. destruct (H27 l1' l2) as (b0 & b2 & IX1 & IX2 & ?); eauto.
          eapply indexr_var_some' in IX2. lia.
        + eauto.
        + eapply CES''' in B. simpl in B.  intuition.
          assert False. { 
          eapply vars_locs_sep2. eapply WFE. 
            3: { assert (psub (pand (plift p2) (plift p1)) pempty). 
            intros ? ?. destruct H42 as [? ?]. eapply H. split; auto.
            eapply H42. } auto. auto. eauto. eauto.
          } contradiction.
          right. destruct (H24 l1' l2) as (b0 & b2 & IX1 & IX2 & ?); eauto.
          eapply indexr_var_some' in IX2. eauto.
          
        + eapply CES'' in C. simpl in C. intuition.
          right. destruct (H27 l1' l2) as (b0 & b2 & IX1 & IX2 & ?); eauto.
          eapply indexr_var_some' in IX2. lia.
        + eapply CES''' in V. simpl in V. intuition.
          assert False. { 
          eapply vars_locs_sep2. eapply WFE. 
            3: { assert (psub (pand (plift p2) (plift p1)) pempty). 
            intros ? ?. destruct H43 as [? ?]. eapply H. split; auto.
            eapply H43. } auto. auto. eauto. eauto.
          } contradiction.
          right. destruct (H24 l1 l2) as (b0 & b2 & IX1 & IX2 & ?); eauto.
          eapply indexr_var_some' in IX2. lia.
        + eauto.
    }
    
    exists S1'', S2''. exists MM. eexists. eexists.

    split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 8: split. 
    + eauto.
    + eauto.
    + eauto. 
    + eauto.
    + eapply se_trans. eapply se_sub. eauto. eapply vl_mono. eauto. eapply se_sub. eauto. eapply vl_mono. eauto.
    + eapply se_trans. eapply se_sub. eauto. eapply vl_mono. eauto. eapply se_sub. eauto. eapply vl_mono. eauto. 
    + simpl. eauto.
    + eapply valq_bool.
    + eapply valq_bool. 
    
  - (* t_sub *)    
    intros ? ? ? WFE ? ? ST. subst y.
    specialize (IHW H3 M H4 H5 WFE S1 S2 ST) as [S1' [S2' [M' [v1 [v2 IE]]]]].
    eapply bi_qsub; eauto. 
    all: apply wf_env_type in WFE; intuition.
    1,3: rewrite H7. 1,2: unfoldq; intuition.
    1,2: rewrite H9. 1,2: unfoldq; intuition.
Qed.



(* ---------- 2nd formulation of compatibility & fundamental lemmas ---------- *)


Definition sem_type G t1 t2 T p fr q e:=
  forall M H1 H2,
    env_type M H1 H2 G p ->
    forall S1 S2,
    store_type S1 S2 M ->
    exists S1' S2' M' v1 v2,
    exp_type S1 S2 M H1 H2 t1 t2 S1' S2' M' v1 v2 T p fr q e.

Lemma bi_vtrue2: forall G p,
  sem_type G ttrue ttrue TBool p false (plift qempty) (plift qempty).
Proof. 
  intros G p M H1 H2 WFE S1 S2 ST.
  exists S1, S2, M, (vbool true), (vbool true).
  eapply bi_vtrue. auto.
Qed.

Lemma bi_vfalse2: forall G p,
  sem_type G tfalse tfalse TBool p false (plift qempty) (plift qempty).
Proof.
  intros G p M H1 H2 WFE S1 S2 ST.
  exists S1, S2, M, (vbool false), (vbool false).
  eapply bi_vfalse; auto.
Qed.

Lemma bi_var2: forall G x T1 fr1 (p:pl),
  indexr x G = Some (T1, fr1) ->
  p x ->
  sem_type G (tvar x) (tvar x) T1 p false (plift (qone x)) (plift qempty).
Proof.
  intros G x T1 p ? ? ? M H1 H2 WFE S1 S2 ST.
  rewrite plift_one. rewrite plift_empty.
  exists S1, S2, M.
  eapply bi_var; eauto.
Qed.

Lemma bi_tref2: forall G t1 t2 p fr q e,
  sem_type G t1 t2 TBool p fr q e ->
  sem_type G (tref t1) (tref t2) (TRef TBool) p true q e.
Proof.
  intros. intros M H1 H2 WFE S1 S2 ST.
  unfold sem_type in H.
  destruct (H M H1 H2 WFE S1 S2 ST) as [S1' [S2' [M' [v1 [v2 IE]]]]].
  eapply bi_tref; eauto.
Qed.

Lemma bi_tget2: forall G t1 t2 p fr q e,
  sem_type G t1 t2 (TRef TBool) p fr q e ->
  sem_type G (tget t1) (tget t2) TBool p false pempty (por e q).
Proof. 
  intros.
  intros M H1 H2 WFE S1 S2 ST.
  unfold sem_type in H.
  destruct (H M H1 H2 WFE S1 S2 ST) as [S1' [S2' [M' [v1 [v2 IE]]]]].
  eapply bi_tget; eauto.
Qed.

Lemma bi_tput2: forall G t1 t2 t3 t4 p fr1 q1 fr2 q2 e1 e2,
  sem_type G t1 t2 (TRef TBool) p fr1 q1 e1 ->
  sem_type G t3 t4 TBool p fr2 q2 e2 ->
  sem_type G (tput t1 t3) (tput t2 t4) TBool p false pempty (por e1 (por e2 q1)).
Proof. 
  intros.
  intros M H1 H2 WFE S1 S2 ST.
  unfold sem_type in H. unfold sem_type in H0.
  destruct (H M H1 H2 WFE S1 S2 ST) as [S1' [S2' [M' [v1 [v2 IE]]]]].
  assert (st_chain M M'). eapply IE. 
  assert (env_type M' H1 H2 G p) as WFE1. eapply envt_store_extend; eauto.
  assert (store_type S1' S2' M') as ST1. eapply IE.
  destruct (H0 M' H1 H2 WFE1 S1' S2' ST1) as [S1'' [S2'' [M'' [v3 [v4 IE2]]]]].
  eapply bi_put; eauto. 
Qed.

Lemma bi_tabs2: forall G t1 t2 T1 fr1 T2 p qf fr2 q2 e2
 (SEM: sem_type ((T1,fr1) :: G) t1 t2 T2  (plift (qor (qand p qf)(qone (length G)))) fr2 (plift (qor q2 (qone (length G)))) (plift (qor e2 (qone (length G)))))
 (CLT1: closed_ty (length G) T1 )
 (CLT2: closed_ty (length G) T2 )  
 (QSUB: psub (plift q2) (pdom G) )
 (ESUB: psub (plift e2) (pdom G) )
 (CLQF: closed_ql (length G)  qf ),
 sem_type G (tabs (qand p qf) t1) (tabs (qand p qf) t2) (TFun T1 fr1 T2  fr2 q2 e2) (plift p) true (plift qf) pempty.
Proof. 
  intros. intros M H1 H2 WFE S1 S2 ST.
  eapply bi_tabs; eauto.
Qed.

Lemma bi_tseq2: forall G t1 t2 t3 t4 p1 p2 p q1 q2 e1 e2
  (H: sem_type G t1 t2 TBool p1 false q1 e1) 
  (H0: sem_type G t3 t4 TBool p2 false q2 e2) 
  (SUB1: psub p1 p)
  (SUB2: psub p2 p),
  sem_type G (tseq t1 t3) (tseq t2 t4) TBool p false pempty (por e1 (por e2 q1)).
Proof. 
  intros.
  intros M H1 H2 WFE S1 S2 ST.
  unfold sem_type in H. unfold sem_type in H0.
  assert (env_type M H1 H2 G p1) as WFE0. eapply envt_tighten; eauto. 
  destruct (H M H1 H2 WFE0 S1 S2 ST) as [S1' [S2' [M' [v1 [v2 IE]]]]].
  assert (st_chain M M'). eapply IE. 
  assert (env_type M' H1 H2 G p2) as WFE1. eapply envt_store_extend; eauto. eapply envt_tighten. eapply WFE. auto.
  assert (store_type S1' S2' M') as ST1. eapply IE. 
  destruct (H0 M' H1 H2 WFE1 S1' S2' ST1) as [S1'' [S2'' [M'' [v3 [v4 IE2]]]]].
  eapply bi_seq; eauto. 
Qed.

Lemma bi_qsub2: forall G t1 t2 T p fr1 q q' e e' fr2
  (SEM: sem_type G t1 t2 T p fr1 q e) 
  (PSUB1: psub q q')
  (ESUB1: psub e e')
  (PSUB2: psub q' (pdom G)) 
  (ESUB2: psub e' (pdom G)), 
  sem_type G t1 t2 T p (fr1||fr2) q' e'.
Proof.
  intros. intros M H1 H2 WFE S1 S2 ST.
  unfold sem_type in SEM.
  destruct (SEM M H1 H2 WFE S1 S2 ST) as [S1' [S2' [M' [v1 [v2 IE]]]]].
  eapply bi_qsub; eauto.
  all: apply wf_env_type in WFE; intuition.
  rewrite H0. auto. rewrite H4. auto.
  rewrite H0. auto. rewrite H4. auto.
Qed.

Lemma bi_app2: forall G t1 t2 ex1 ex2 T1 fr1 T2 e1 e2 p frf qf ef frx q1 fr2 q2
  (SEMF: sem_type G t1 t2 (TFun T1 fr1 T2 fr2 q2 e2) p frf qf ef) 
  (SEMX: sem_type G ex1 ex2 T1 p frx q1 e1)
  (SEP: psub (pand  qf q1) pempty)
  (QSUB: psub (plift q2) p)
  (ESUB: psub (plift e2) p),
  sem_type G (tapp t1 ex1) (tapp t2 ex2) T2 p (frf||frx||fr2) (por (plift q2) q1) (por ef (por e1 (plift e2))).
Proof.
  intros. intros M H1 H2 WFE S1 S2 ST.
  unfold sem_type in SEMF.  unfold sem_type in SEMX.
  destruct (SEMF M H1 H2 WFE S1 S2 ST) as [S1' [S2' [M' [vf1 [vf2 IEF]]]]].

  assert (st_chain M M'). eapply IEF.
  assert (env_type M' H1 H2 G p) as WFE1. { eapply envt_store_extend; eauto. }
  assert (store_type S1' S2' M') as ST1. eapply IEF.
  
  destruct (SEMX M' H1 H2 WFE1 S1' S2' ST1) as [S1'' [S2'' [M'' [vx1 [vx2 IEX]]]]].
   
  eapply bi_tapp; eauto.
Qed.

Theorem fundamental_property2 : forall t G T p fr q e,
  has_type G t T p fr q e -> 
  sem_type G t t T (plift p) fr (plift q) (plift e).
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
  - (* Case "tget"  *)
    rewrite plift_empty.
    eapply bi_tget2; eauto.
  - (* Case "tput" *)
    rewrite plift_empty.
    eapply bi_tput2; eauto.
  - (* Case "App" *)
    rewrite plift_or.
    eapply bi_app2; eauto. 
  - (* Case "Abs" *)
    eapply bi_tabs2; eauto.
  - (* Case "Seq" *)
    rewrite plift_empty.
    eapply bi_tseq2; eauto.
  - (* Case "qsub" *)
    eapply bi_qsub2; eauto.  
Qed.

Theorem reorder_seq2 : forall t1 t2 G T p q e
  (W: has_type G (tseq t1 t2) T p false q e),
  sem_type G (tseq t1 t2) (tseq t2 t1) T (plift p) false (plift q) (plift e).
Proof.
  intros t1 t2 G T p q e W.
  intros M H1 H2 WFE S1 S2 ST.
  eapply reorder_seq; eauto.
Qed.

Inductive ctx_type : (tm -> tm) -> tenv -> ty -> pl -> bool -> pl -> pl -> tenv -> ty -> pl -> bool -> pl -> pl -> Prop :=
| cx_top: forall G T p fr q e,
    ctx_type (fun x => x) G T p fr q e G T p fr q e
| cx_ref: forall G p fr q e,
    ctx_type (fun x => tref x) G TBool p fr q e G (TRef TBool) p true q e
| cx_get: forall G p q fr e,
    ctx_type (fun x => tget x) G (TRef TBool) p fr q e G TBool p false pempty (por e q)
| cx_put1: forall G t1 p fr1 q1 e1 e2 fr2 q2,
    has_type G t1 (TRef TBool) p fr1 q1 e1 ->
    ctx_type (fun x => tput t1 x) G TBool (plift p) fr2 q2 e2 G TBool (plift p) false pempty (por (plift e1) (por e2 (plift q1)))
| cx_put2: forall G t2 p fr1 q1 e1 e2 fr2 q2,
    has_type G t2 TBool p fr2 q2 e2 ->
    ctx_type (fun x => tput x t2) G (TRef TBool) (plift p) fr1 q1 e1 G TBool (plift p) false pempty (por e1 (por (plift e2) q1))
| cx_app1: forall t2 G T1 fr1 T2 frx q1 fr2 q2 e1 e2 ef p frf qf,
    has_type G t2 T1 p frx q1  e1 ->
    psub (pand qf (plift q1)) pempty ->
    psub (plift q2) (plift p) ->
    psub (plift e2) (plift p) ->
    ctx_type (fun x => tapp x t2) G (TFun T1 fr1 T2 fr2 q2 e2) (plift p) frf qf ef G T2 (plift p) (frf||frx||fr2) (por (plift q2) (plift q1)) (por ef (por (plift e1) (plift e2)))
| cx_app2: forall t1 G T1 fr1 T2 fr2 q2 e1 e2 p frf qf ef frx q1,
    has_type G t1 (TFun T1 fr1 T2 fr2 q2 e2) p frf qf ef ->
    psub (pand (plift qf) q1) pempty ->
    psub (plift q2) (plift p) ->
    psub (plift e2) (plift p) ->
    ctx_type (fun x => tapp t1 x) G T1 (plift p) frx q1 (plift e1)  G T2 (plift p) (frf||frx||fr2) (por (plift q2) q1)(por (plift ef) (por (plift e1) (plift e2)))
| cx_abs: forall G T1 fr1 T2 fr2 q2 e2 p qf ef,
    closed_ty (length G) T1 ->
    closed_ty (length G) T2 ->
    psub (plift q2) (pdom G) ->
    psub (plift e2) (pdom G) ->
    closed_ql (length G) qf ->
    ctx_type (fun x => tabs (qand p qf) x) ((T1,fr1)::G) T2 (plift (qor (qand p qf)(qone (length G)))) fr2 (plift (qor q2 (qone (length G)))) (plift (qor e2 (qone (length G)))) G (TFun T1 fr1 T2 fr2 q2 e2) (plift p) true (plift qf) (plift ef)
| cx_seq1: forall G t1 p p1 p2 q1 e1 e2 q2,
    has_type G t1 TBool p1 false q1 e1 ->
    psub (pand (plift p1)(plift p2)) pempty ->
    psub (plift p1) (plift p) ->
    psub (plift p2) (plift p) ->
    ctx_type (fun x => tseq t1 x) G TBool (plift p2) false q2 e2 G TBool (plift p) false  pempty (por (plift e1) (por e2 (plift q1)))
| cx_seq2: forall G t2 p p1 p2 q1 e1 e2 q2,
    has_type G t2 TBool p2 false q2 e2 ->
    psub (pand (plift p1)(plift p2)) pempty ->
    psub (plift p1) (plift p) ->
    psub (plift p2) (plift p) ->
    ctx_type (fun x => tseq x t2) G TBool (plift p1) false q1 e1 G TBool (plift p) false pempty (por e1 (por (plift e2) q1))
| cx_qsub: forall G T p fr1 q fr2 q' e e',
    psub q q' ->
    psub e e' ->
    psub q' (pdom G) -> 
    psub e' (pdom G) -> 
    ctx_type (fun x => x) G T p fr1 q e G T p (fr1||fr2) q' e'
.

Theorem congr:
  forall C G1 T1 p fr q e G2 T2 p' fr' q' e',
    ctx_type C G1 T1 p fr q e G2 T2 p' fr' q' e' ->
  forall t t',
    sem_type G1 t t' T1 p fr q e->
    sem_type G2 (C t) (C t') T2 p' fr' q' e'.
Proof.
  intros ? ? ? ? ? ? ? ? ? ? ? ? ? CX.
  induction CX; intros.
  - eauto.
  - eapply bi_tref2. eauto.
  - eapply bi_tget2. eauto.  
  - eapply bi_tput2; eauto. eapply fundamental_property2. eauto. 
  - eapply bi_tput2; eauto. eapply fundamental_property2. eauto. 
  - eapply bi_app2; eauto. eapply fundamental_property2. eauto.    
  - eapply bi_app2; eauto. eapply fundamental_property2. eauto. 
  - eapply bi_tabs2; eauto.
  - eapply bi_tseq2. eapply fundamental_property2. eauto. all: eauto.
  - eapply bi_tseq2; eauto. eapply fundamental_property2. eauto. 
  - eapply bi_qsub2; eauto.
Qed.


Lemma adequacy: forall e e' fr T,
  sem_type [] e e' T pempty fr pempty pempty  ->
  (exists v M, tevaln [] [] e M v) <-> 
  (exists v' M', tevaln [] [] e' M' v').
Proof. 
  intros. 
  assert (env_type (0, 0, (fun x1 x2: nat => False)) [] [] [] pempty) as WFE. { 
    unfold env_type; intuition. 
    1,2: unfoldq; intros; intuition.
  }
  assert (store_type [] [] (0, 0, (fun x1 x2: nat => False))) as ST.
  unfold store_type; intuition.
  unfold sem_type in H. 
  specialize (H (0, 0, (fun x1 x2: nat => False)) [] [] WFE [] [] ST). 
  destruct H as [S1 [S2 [M [v1 [v2 IE]]]]].
  destruct IE as [? [? [? [? [? ?]]]]].
  split. 
  + intros. exists v2, S2. intuition.
  + intros. exists v1, S1. intuition.
Qed.

Definition context_equiv G t1 t2 T1 p fr q e:=
  has_type G t1 T1 p fr q e ->
  has_type G t2 T1 p fr q e ->
  forall C,
    ctx_type C G T1 (plift p) fr (plift q) (plift e) [] TBool  (plift qempty) fr (plift qempty) (plift qempty) ->
    (exists v1 S1, tevaln [] [] (C t1) S1 v1) <->
    (exists v2 S2, tevaln [] [] (C t2) S2 v2).


(* soundness of binary logical relations *)
Theorem soundess: forall G t1 t2 T p fr q e,
  has_type G t1 T p fr q e ->
  has_type G t2 T p fr q e ->
    (sem_type G t1 t2 T (plift p) fr (plift q) (plift e) -> 
     context_equiv G t1 t2 T p fr q e).    
Proof. 
  intros. unfold context_equiv. intros.
  rewrite plift_empty in *.
  assert (sem_type [] (C t1)(C t2) TBool pempty fr pempty pempty). {
    specialize (congr C G  T (plift p) fr (plift q) (plift e) [] TBool pempty fr pempty pempty ); intuition.
  }
  eapply adequacy; eauto. 
Qed.

End STLC.
