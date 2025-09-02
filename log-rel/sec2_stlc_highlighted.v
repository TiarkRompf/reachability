(*******************************************************************************
* Coq mechanization of the simply typed calculus with first-order mutable store (the λ$_b$-calculus) with highlighted formulas.
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

(* compute free variables *)

Fixpoint fv (m: nat)(t: tm) : ql :=
  match t with 
  | ttrue => qempty 
  | tfalse => qempty 
  | tvar i => qone i
  | tref t => fv m t
  | tget t => fv m t
  | tput t1 t2 => qor (fv m t1) (fv m t2)
  | tapp t1 t2 => qor (fv m t1) (fv m t2)
  | tabs t => (qdiff (fv (S m) t) (qone m))
  | tseq t1 t2 => qor (fv m t1) (fv m t2)
  end.

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

(* mapping values and variables to store locations *)

Fixpoint val_locs_fix (v: vl) (l: nat): bool :=
  match v with
  | vbool  _ => false
  | vref x   => x =? l
  | vabs H t  =>
      let q := (qdiff (fv (S (length H)) t) (qone (length H))) in
      let fix vars_locs_fix (H: list vl) :=
          match H with
          | v :: H => (q (length H) && val_locs_fix v l) || vars_locs_fix H
          | [] => false
          end
        in vars_locs_fix H
   end.


Fixpoint vars_locs_fix (H: venv) (q: ql) (l: nat): bool :=
  match H with
  | v :: H => (q (length H) && val_locs_fix v l) || vars_locs_fix H q l
  | [] => false
  end.    

Definition val_locs v := plift (val_locs_fix v). 

Definition var_locs E x l := exists vx, indexr x E = Some vx /\ val_locs vx l.

Definition vars_locs E q l := exists x, q x /\ var_locs E x l.


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

Definition st_chain (M: stty) (M1: stty) q :=
  psub q (st_locs M) /\
  psub q (st_locs M1) /\
  forall l, q l ->
            indexr l M = indexr l M1.


#[global] Hint Unfold st_types.
#[global] Hint Unfold st_locs. 

(* store preservation invariant *)

Definition store_effect (S S1: stor) (p: pl) :=
  forall l v,
    ~ p l -> 
    indexr l S = Some v ->
    indexr l S1 = Some v.


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
      st_chain M M' pempty  -> 
      forall v,
      (vt v <-> val_type M' H v T ))
      
  | vabs G ty, TFun T1 T2  =>
        closed_ty (length H) T1 /\
        closed_ty (length H) T2 /\
        psub (val_locs v) (st_locs M) /\
        (forall S' M' vx,
            st_chain M M' (val_locs (v))
            ->
              store_type S' M'
            ->
            val_type
              M'
              H
              vx
              T1
            -> 
            psub (val_locs vx)(por (val_locs v)(pnot (val_locs v)))
            -> 
              exists S'' M'' vy,
                tevaln
                  S'
                  (vx::G)
                  ty
                  S''
                  vy
                /\
                  st_chain M' M'' (st_locs M') 
                /\
                  store_type S'' M''
                /\
                  store_effect S' S'' (por (val_locs vx)(val_locs v))
                /\
                  val_type
                    M''
                    H
                    vy
                    T2
                /\
                  psub (val_locs vy)
                    (por (val_locs v)
                      (por (val_locs vx)
                           (pnot (pdom M')))))
  | _,_ =>
      False
  end.

(* rechability *)
Definition val_qual (M M1: stty) H v (q: pl) :=
  psub (val_locs v)
    (por (vars_locs H  q) 
         (pnot (pdom M))).  

(* term interpretation *)

Definition exp_type S M H t T :=
  exists S' M' v,
    tevaln S H t S' v /\
    st_chain M M' (st_locs M) /\
    store_type S' M' /\
    store_effect S S' (vars_locs H (plift (fv (length H) t))) /\
    val_type M' H v T /\
    val_qual M M' H v (plift (fv (length H) t)).


(* semantic context interpretation *)

Definition env_type M H G p :=
  length H = length G /\
  psub p (pdom H) /\
    (forall x T,
        indexr x G = Some T ->
        exists v : vl,
          indexr x H = Some v /\
          (p x -> (val_type M H v T)))           
.

(* semantic types *)

Definition sem_type G t T :=
  forall S M E,
    env_type M E G (plift (fv (length E) t)) ->
    store_type S M  ->
    exp_type S M E t T. 


#[export] Hint Constructors ty: core.
#[export] Hint Constructors tm: core.
#[export] Hint Constructors vl: cor.


#[export] Hint Constructors has_type: core.

#[export] Hint Constructors option: core.
#[export] Hint Constructors list: core.

(* ---------- qualifier reflection & tactics  ---------- *)

Ltac unfoldq := unfold val_qual, psub, pdom, pnat, pdiff, pnot, pif, pand, por, pempty, pone, var_locs, vars_locs in *.
Ltac unfoldq1 := unfold qsub, qdom, qand, qempty, qone in *.

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

Lemma pand_empty_r: forall p,
  pand p pempty = pempty.
Proof.
  intros. unfoldq. eapply functional_extensionality. intros.
  eapply propositional_extensionality. split; intuition.
Qed. 

Lemma plift_or: forall a b,
    plift (qor a b) = por (plift a) (plift b).
Proof.
  intros. unfoldq. unfold plift.
  eapply functional_extensionality. intros.
  eapply propositional_extensionality. 
  bdestruct (qor a b x); intuition.
Qed.

Lemma por_empty_r: forall p,
  por p pempty = p.
Proof.
  intros. eapply functional_extensionality. intros. eapply propositional_extensionality. 
  split; unfoldq; intuition.
Qed.

Lemma plift_diff: forall a b,
    plift (qdiff a b) = pdiff (plift a) (plift b).
Proof.
  intros. unfoldq. unfold plift.
  eapply functional_extensionality. intros.
  eapply propositional_extensionality.
  unfold qdiff. destruct (a x); destruct (b x); intuition. 
Qed.

(* ---------- vars_locs lemmas ----------------*)
Lemma vars_locs_empty: forall H,
  vars_locs H pempty = pempty.
Proof. 
  intros. eapply functional_extensionality.
  intros. eapply propositional_extensionality.
  split; intros. unfoldq; intuition. destruct H0. intuition.
  unfoldq; intuition.
Qed.

Lemma vars_locs_monotonic: forall H q q',
    psub q q' ->
    psub (vars_locs H q) (vars_locs H q').
Proof. 
  intros. unfoldq. intros. 
  destruct H1; intuition. specialize (H0 x0); intuition.
  exists x0; intuition.
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

Lemma var_locs_extend: forall v H x l,
  var_locs H x l ->
  var_locs (v::H) x l.
Proof.
  intros. unfoldq. 
  destruct H0 as [vx [IVX VALVX]].
  exists vx. split.
  erewrite indexr_extend1 in IVX; eauto. 
  eapply IVX. eauto. 
Qed.


(* ---------- closedness, vars_locs lemmas  ---------- *)


Lemma closedty_extend : forall {m T}, closed_ty m T -> 
  forall {m'}, m <= m' -> closed_ty m' T.
Proof. 
    intros. induction T; constructor.
    all: inversion H; subst; intuition.
Qed.


(* ---------- store typing lemmas  ---------- *)


Lemma stchain_chain: forall M1 M2 M3 q1 q2,
  st_chain M1 M2 q1 ->
  st_chain M2 M3 q2 ->
  st_chain M1 M3 (pand q1 q2).
Proof.
  intros. destruct H, H0, H1, H2.
  split. unfoldq. intuition.
  split. unfoldq. intuition.
  intros. rewrite H3, H4. eauto. eapply H5. eapply H5.
Qed.

Lemma stchain_tighten: forall M1 M2 q1 q2,
  st_chain M1 M2 q2 ->
  psub q1 q2 ->
  st_chain M1 M2 q1.
Proof.
  intros. destruct H. destruct H1.
  split. unfoldq. intuition.
  split. unfoldq. intuition.
  intros. rewrite H2. eauto. eauto.
Qed.


Lemma stchain_chain': forall M1 M2 M3 q1 q2,
  st_chain M1 M2 q1 ->
  st_chain M2 M3 q2 ->
  psub q2 q1 ->
  st_chain M1 M3 q2.
Proof.
  intros. eapply stchain_tighten in H; eauto.
  replace q2 with (pand q2 q2). eapply stchain_chain; eauto.
  eapply functional_extensionality. intros.
  eapply propositional_extensionality. unfoldq. intuition. 
Qed.

Lemma stchain_chain'': forall M1 M2 M3 q1 q2,
  st_chain M1 M2 q1 ->
  st_chain M2 M3 q2 ->
  psub q1 q2 ->
  st_chain M1 M3 q1.
Proof.
  intros. eapply stchain_tighten in H0; eauto.
  replace q1 with (pand q1 q1). eapply stchain_chain; eauto.
  eapply functional_extensionality. intros.
  eapply propositional_extensionality. unfoldq. intuition. 
Qed.


Lemma stchain_refl: forall M,
    st_chain M M (st_locs M).
Proof.
  intros. split. unfoldq. intuition.
  split. unfoldq. intuition.
  intros. eauto.
Qed.

Lemma st_mono: forall M M',
  st_chain M M' (st_locs M) ->
  length M <= length M'.
Proof.
  intros. destruct H as [? [? ?]].
  unfoldq; intuition. unfold st_locs, pdom in *. 
  destruct (length M). lia. eapply H0. lia.
Qed. 

Lemma storet_extend: forall S M S1 M1 E G T vx vt p
    (ST:  store_type S M)
    (ST1: store_type S1 M1)
    (WFE: env_type M E G p)
    (SC1: st_chain M M1 (st_locs M))
    (SC2: st_chain M1 (st_extend M1 vt) (st_locs M1))
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

Lemma stchain_empty: forall M M',
  st_chain M M' pempty.
Proof.
  intros. repeat split; unfoldq; intuition.
Qed.


(*----------- fv lemmas -----------*)

Lemma plift_fv_shrink: forall t m n,
  n < m ->
  plift (fv (S m) t) n -> plift (fv m t) n.
Proof. 
  intros t. induction t; intros; simpl in *.
  rewrite plift_empty in H0. unfoldq; intuition.
  rewrite plift_empty in H0. unfoldq; intuition.
  eauto. 
  eapply IHt; eauto. eapply IHt; eauto.
  rewrite plift_or in *. destruct H0. left. eapply IHt1; eauto. right. eapply IHt2; eauto.
  rewrite plift_or in *. destruct H0. left. eapply IHt1; eauto. right. eapply IHt2; eauto.
  rewrite plift_diff in *. rewrite plift_one in *. destruct H0. split.
  eapply IHt in H0. auto. unfoldq; intuition. unfoldq; intuition. 
  rewrite plift_or in *. destruct H0. left. eapply IHt1; eauto. right. eapply IHt2; eauto.
Qed.


Lemma fv_shrink: forall t m n,
  n < m ->
  (fv (S m) t) n = true -> (fv m t) n = true.
Proof. 
  intros. eapply plift_fv_shrink; eauto.
Qed.

Lemma plift_fv_extend: forall t m1 m2 n,
  m1 <= m2 ->
  n < m2 ->
  plift (fv m1 t) n -> plift (fv m2 t) n.
Proof.
  intros t. induction t; intros; simpl in *.
  rewrite plift_empty in H1. unfoldq; intuition.
  rewrite plift_empty in H1. unfoldq; intuition.
  bdestruct (i <? m1); bdestruct (i <? m2); intuition.
  eapply IHt in H1; eauto.  eapply IHt in H1; eauto.  
  rewrite plift_or in *. destruct H1. left. eapply IHt1 in H1; eauto. right. eapply IHt2 in H1; eauto.
  rewrite plift_or in *. destruct H1. left. eapply IHt1 in H1; eauto. right. eapply IHt2 in H1; eauto.
  rewrite plift_diff in *. destruct H1. split. eapply IHt in H1; eauto. lia. 
  rewrite plift_one in *. unfoldq; intuition.
  rewrite plift_or in *. destruct H1. left. eapply IHt1 in H1; eauto. right. eapply IHt2 in H1; eauto.
Qed.


Lemma fv_extend: forall t m1 m2 n,
  m1 <= m2 ->
  n < m2 ->
  (fv m1 t) n = true -> (fv m2 t) n = true.
Proof. 
  intros. eapply plift_fv_extend in H1; eauto.
Qed.


(*----------- val_locs lemmas  -----------*)
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


Lemma plift_congr: forall q1 q2,
    q1 = q2 ->
    plift q1 = plift q2.
Proof.
  congruence.
Qed.


Lemma val_locs_abs: forall H t,
    val_locs (vabs H t) = vars_locs H (plift (fv (length H) (tabs t))).
Proof.
  intros. rewrite plift_vars_locs. unfold val_locs. simpl.
  remember (qdiff (fv (S (length H)) t) (qone (length H))) as q. clear Heqq.
  eapply plift_congr. 
  eapply functional_extensionality. intros.
  unfold vars_locs_fix. induction H. eauto.
  rewrite IHlist. eauto. 
Qed.

Lemma val_locs_decide: forall v l,
    val_locs v l \/ ~ val_locs v l.
Proof.
  intros. unfold val_locs, plift.
  destruct (val_locs_fix v l); eauto.
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

Lemma valt_wf: forall T M H v,
    val_type M H v T ->
    psub (val_locs v) (st_locs M).
Proof. 
  intros T. induction T; intros; destruct v; simpl in *; intuition.
  + rewrite val_locs_bool. auto. unfoldq. intuition.
  + rewrite val_locs_ref. intros ? ?. unfold pone in H2. subst x. auto.
Qed.


Lemma valt_store_change: forall T M' M H v,
    val_type M H v T ->
    st_chain M M' (val_locs v) ->
    val_type M' H v T.
Proof.
  intros T. induction T; intros; destruct v; simpl in *; intuition.
  + rewrite val_locs_ref in *.  eapply H1; eauto. unfoldq; intuition.
  + rewrite val_locs_ref in *. 
    remember H1 as H7. destruct H1 as (? & ? & ?). clear HeqH7.
    destruct H4 as [vt [IX VT]].
    assert (st_chain M M' (pempty)). {
      eapply stchain_empty; eauto.
    }
    exists vt.
    split. 
    * rewrite <-e. eauto. intuition.
    * intros. 
      assert (st_chain M M'0 pempty). {
        eapply stchain_empty; eauto. }
      eapply VT. eauto. 
  + intros ? ?. eapply H1. auto.
  + eapply H5. 
    eapply stchain_chain''. eauto. eauto. 
    intros ? ?. auto. 
    auto.
    eauto. eauto.
Qed.


Lemma valt_store_extend: forall T M' M H v,
    val_type M H v T ->
    st_chain M M' (st_locs M) ->
    val_type M' H v T.
Proof.
  intros ? ? ?. 
  replace (st_locs M') with (pnat (length M')).
  intros. eapply valt_store_change; eauto.
  eapply stchain_tighten; eauto.
  eapply valt_wf; eauto. 
  unfold st_locs. unfoldq. eauto.
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
    destruct (H5 S' M' vx) as [S'' [M'' [vy [HEY HVY]]]]. eauto. eauto. 
    eapply IHT1; eauto. auto.
    exists S'', M'', vy. intuition.
    eapply IHT2; eauto.
  - eapply closedty_extend; eauto.
  - eapply closedty_extend; eauto.
  - (* Abs grow *)
    inversion H0. subst.
    destruct (H5 S' M' vx) as [S'' [M'' [vy [HEY [ST2 [HVY HQY]]]]]]. eauto. eauto.
      eapply IHT1; eauto. auto.
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

(* ---------- val_qual lemmas  ---------- *)

Lemma valq_bool: forall M M1 H b q,
    val_qual M M1 H (vbool b) q.
Proof.
  intros. unfoldq. rewrite val_locs_bool. intuition.
Qed.

Lemma valq_abs: forall M M1 H t,
    val_qual M M1 H (vabs H t)  (plift (fv (length H) (tabs t))).
Proof.
  intros. unfoldq.
  rewrite val_locs_abs.
  intuition. 
Qed.


(* ---------- environment lemmas  ---------- *)


Lemma wf_env_type: forall M H G p, 
  env_type M H G p -> 
  (length H = length G /\
    pdom H = pdom G) .
Proof.
    intros. unfold env_type in H0. intuition.
    unfold pdom. rewrite H1. auto.
Qed.

Lemma env_type_store_wf: forall M H G p q,
    env_type M H G p ->
    psub q p ->
    psub (vars_locs H q) (st_locs M).
Proof.
  intros. destruct H0 as [L [P W]]; intuition.
  unfoldq. intuition.
  destruct H0 as [? [? ?]].
  destruct H2 as [? [? ?]].
  assert (x0 < length H). eapply indexr_var_some'. eauto. 

  assert (exists xt, indexr x0 G = Some xt) as TY.
  rewrite L in H4. eapply indexr_var_some in H4. intuition.
  destruct TY as [T  ?]. 
  destruct (W x0 T) as [vx [? ?]]. eauto.

  rewrite H2 in H6. inversion H6. subst x1.
  eapply valt_wf; eauto.
Qed.

Lemma envt_tighten: forall M H G p p',
    env_type M H G p ->
    psub p' p ->
    env_type M H G p'.
Proof.
  intros. destruct H0 as [L [P W]].
  repeat split; auto.
  - unfoldq. intuition.
  - intros.
    destruct (W x T); eauto.
    intuition. exists x0. intuition.
Qed.



Lemma envt_store_extend: forall M M' H G p,
    env_type M H G p ->
    st_chain M M' (st_locs M) ->
    env_type M' H G p.
Proof.
  intros. remember H0 as WFE1. clear HeqWFE1. destruct H0 as [L [P W]]. 
  repeat split; auto.
  intros.
  destruct (W _  _ H0) as [vx [IH HVX]]; intuition.
  exists vx; intuition.
  eapply valt_store_extend. eauto. auto.
Qed.


Lemma envt_extend_full: forall M M1 H G vx T1 t,
    env_type M H G (plift (fv (length H) (tabs t))) ->
    val_type M1 H vx T1 ->
    closed_ty (length H) T1 ->
    st_chain M M1 (val_locs (vabs H t)) ->
    env_type M1 (vx :: H) (T1 :: G) (plift (fv (length (vx::H)) t)).
Proof.  
  intros. apply wf_env_type in H0 as H0'. destruct H0' as (L' & PD (*& SG*)). 

  rename H0 into WFE.
  rename H3 into SC.
  
  remember WFE as WFE1. clear HeqWFE1.
  destruct WFE as [L [P W]].

  repeat split; eauto.
  - simpl. eauto.
  - simpl in *. rewrite plift_diff, plift_one in P.
    intros ? ?. 
    bdestruct (x =? length H); intuition.
    + unfoldq. simpl. intuition.
    + assert (pdom H x). eapply P. unfoldq. intuition.
      unfoldq. simpl. intuition. 
  - intros.
    bdestruct (x =? length G); intuition. 
    + subst. rewrite indexr_head in H0. inversion H0. subst.
      exists vx. split.
      ++ rewrite <- L'. rewrite indexr_head. auto.
      ++ intros.  eapply valt_extend1; eauto.
    + rewrite indexr_skip in H0. 2: { apply indexr_var_some' in H0. simpl in H0. lia. }
      destruct (W _ _  H0) as [v [IH VT]].
      exists v. split. 
      rewrite indexr_skip. auto. lia.
      intros. eapply valt_store_change. eapply valt_extend1; eauto. 
      eapply valt_closed; eauto. eapply VT.
      simpl in H4. simpl. rewrite plift_diff, plift_one. split; auto. apply indexr_var_some' in IH. unfoldq; intuition. 
      eapply VT. simpl in H4. simpl. rewrite plift_diff, plift_one. split; auto. apply indexr_var_some' in IH. unfoldq; intuition. 
      eapply stchain_tighten; eauto.
      intros ? ?. 
      simpl in H4. rewrite val_locs_abs. simpl. 
      eexists. split. 2: { eexists. intuition. eauto. auto. }
      rewrite plift_diff, plift_one. split. auto. apply indexr_var_some' in IH. unfoldq; intuition.
Qed.


(* effect lemmas *)

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
                                                          

(* ---------- main lemmas ---------- *)

Lemma sem_true: forall G,
    sem_type G ttrue TBool.
Proof.
  intros. intros S M H WFE ST.
  exists S, M, (vbool true). 
  split. 2: split. 3: split. 4: split. 5: split.
  - exists 1. intros. destruct n. lia. simpl. intuition.
  - eapply stchain_refl. 
  - eauto.
  - simpl. intros ? ? ? ?. auto.
  - simpl. eauto.
  - eapply valq_bool; eauto.
Qed.
  
Lemma sem_false: forall G,
    sem_type G tfalse TBool.
Proof.
  intros. intros S M H WFE ST.
  exists S, M, (vbool false).
  split. 2: split. 3: split. 4: split. 5: split.
  - exists 1. intros. destruct n. lia. simpl. intuition.
  - eapply stchain_refl. 
  - eauto.
  - simpl. intros ? ? ? ?. auto.
  - simpl. eauto.
  - eapply valq_bool; eauto.
Qed.
  
Lemma sem_var: forall x G T,
    indexr x G = Some T ->
    sem_type G (tvar x) T.
Proof.
  intros. intros ? ? ? WFE ST.
  destruct WFE as [L [P WFE]].
  destruct (WFE x T) as [vx [HI VT]].
  unfoldq; intuition. 
  exists S, M, vx.
  split. 2: split. 3: split. 4: split. 5: split.
  - exists 1. intros. destruct n. lia. simpl. rewrite HI. reflexivity.
  - eapply stchain_refl. 
  - eauto.
  - simpl. intros ? ? ? ?. auto.
  - eapply VT. apply indexr_var_some' in HI. simpl.
    bdestruct (x <? length E); intuition. rewrite plift_one. unfoldq; intuition.
  - intros ? ?. left.  
    eexists; intuition. simpl. 2: eexists; eauto. 
    bdestruct (x <? length E); intuition. rewrite plift_one. unfoldq; intuition. 
    apply indexr_var_some' in HI. lia.
Qed.

Lemma sem_ref: forall t G,
    sem_type G t TBool ->
    sem_type G (tref t) (TRef TBool).
Proof.
  intros. intros ? ? ? WFE ST. 
  destruct (H S M E WFE ST) as [S1 [M1 [vx [IW1 [SC1 [ST1 [SE1 [HVX HQX]]]]]]]].
  remember (length S1) as x.
  remember (fun v => val_type M1 E v TBool) as vt.
  assert (st_chain M1 (st_extend M1 vt) (st_locs M1)). {
    split. 2: split.
    unfoldq. intuition.
    unfoldq. intuition. 
    unfold st_locs, st_extend in *. unfoldq. simpl. intuition.
    intros. unfold st_locs, st_extend in *. rewrite indexr_skip. eauto. unfoldq. lia. }

  exists (vx::S1).
  exists (st_extend M1 vt ).
  exists (vref x). split. 2: split. 3: split.  4: split. 5: split.
  + (* expression evaluates *)
    destruct IW1 as [n1 IW1]. rename S into St.
    exists (S n1).
    intros. destruct n. lia.
    subst x. simpl. rewrite IW1. eauto. lia.
  + (* stty chain *)
    eapply stchain_chain''. eauto. 2: eapply SC1. eauto.
  + (* store typing *)
    eapply storet_extend. eapply ST. all: eauto.
  + simpl. eapply se_trans. eauto. intros ? ?. intros. eapply indexr_extend1 in H2. eapply H2. 
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
  + intros ? ?. 
  right. simpl. rewrite val_locs_ref in H1. unfold pone in H1. subst x0.  intros ?. unfoldq. eapply st_mono in SC1. destruct ST1. lia.
Qed.

Lemma sem_get: forall t env,
    sem_type env t (TRef TBool) ->
    sem_type env (tget t) TBool.
Proof.
  intros. intros ? ? ? WFE ST.
  destruct (H S M E WFE ST) as [S1 [M1 [vx [IW1 [SC1 [ST1 [SE1 [HVX HQX]]]]]]]]. 
  destruct vx; try solve [inversion HVX]. simpl in HVX.
  destruct HVX as (? & ? & HVX).
  destruct HVX as [vt [IM HVX]].

  remember ST1 as ST1'. clear HeqST1'. destruct ST1' as (L & STL).
  destruct (STL i) as [vt' [v [IXM' [IXS VTS]]]].
  unfold st_locs. unfoldq; intuition. rewrite IM in IXM'. inversion IXM'. subst vt'.
  (*unfold st_types in IXM'. simpl in IXM'.*) 
  exists S1, M1, v. split. 2: split. 3: split. 4: split. 5: split.
  + (* expression evaluates *)
    destruct IW1 as [n1 IW1]. rename S into St.
    exists (S n1).
    intros. destruct n. lia.
    simpl. rewrite IW1. rewrite IXS. eauto. lia.
  + (* st chain *)
    eauto. 
  + (* store type *)
    eauto.
  + eauto.
  + (* result well typed *)
    simpl. eapply HVX; eauto. eapply stchain_empty; eauto. 
  + intros ? ?. eapply HVX in VTS. destruct v; try contradiction. rewrite val_locs_bool in H2. unfoldq; intuition.
  eapply stchain_empty; eauto.
Unshelve. eauto. eauto.    
Qed.


Lemma sem_put: forall t1 t2 env,
    sem_type env t1 (TRef TBool) ->
    sem_type env t2 TBool ->
    sem_type env (tput t1 t2) TBool.
Proof.
  intros. intros ? ? ? WFE ST.
  simpl in WFE. rewrite plift_or in WFE.
  assert (env_type M E env (plift (fv (length E) t1))) as WFE1. eapply envt_tighten; eauto. unfoldq; intuition.
  destruct (H S M E WFE1 ST) as [S1 [M1 [vr [IW1 [SC1 [ST1 [SE1 [HVR HQR]]]]]]]]. 
  eapply envt_store_extend in WFE as WFE2. 2: eapply SC1.
  assert (env_type M1 E env (plift (fv (length E) t2))) as WFE2'. eapply envt_tighten; eauto. unfoldq; intuition. 
  destruct (H0 S1 M1 E WFE2' ST1) as [S2 [M2 [vx [IW2 [SC2 [ST2 [SE2 [HVX HQX]]]]]]]].

  destruct vr; try solve [inversion HVR]. simpl in HVR.
  destruct HVR as (? & ? & vt ).
  destruct vt as (vt & IM & HVT).

  
  destruct ST2 as (? & ST2).
  destruct (ST2 i) as (vt'' & vz & ? & ? & ?). eapply SC2. eauto. 
  assert (indexr i M2 = indexr i M1) as R. { symmetry. eapply SC2. eauto. }
  rewrite R in H4. 
  rename H5 into SI.

  exists (update S2 i vx), M2, (vbool true).
  split. 2: split. 3: split. 4: split. 5: split.
  + (* expression evaluates *)
    rename S into St.
    destruct IW1 as [n1 IW1].
    destruct IW2 as [n2 IW2].
    exists (S (n1+n2)).
    intros. destruct n. lia.
    simpl. rewrite IW1. rewrite IW2. rewrite SI. eauto. lia. lia.
  + eapply stchain_chain''; eauto. eapply SC1. 
  + (* store type *)
    split. rewrite <-update_length. eauto. 
    intros. bdestruct (i =? l).
    * subst i. 
      exists vt''. exists vx. split.  2: split.
      -- rewrite R. eapply H4.
      -- rewrite update_indexr_hit. eauto. eapply indexr_var_some'. eauto.
      -- rewrite H4 in IM. inversion IM. subst vt''. eapply HVT. eapply stchain_empty; eauto.          
         eauto.
    * rewrite update_indexr_miss. 2: eauto.
      eapply ST2. eauto.
  + assert (length S = length M). destruct ST.  eauto.
    intros ? ?. intros.
    bdestruct (i =? l). { subst.
    destruct (HQR l).
      rewrite val_locs_ref. unfoldq; intuition.
      assert False. eapply H7. simpl. rewrite plift_or. 
      eapply vars_locs_monotonic; eauto. unfoldq; intuition.
      contradiction.
      destruct H9. apply indexr_var_some' in H8. unfoldq. lia. 
    }{ rewrite update_indexr_miss.
        eapply SE1 in H8 as A; eauto.
        eapply SE2 in A  as B; eauto.
        intros ?. eapply H7. simpl. rewrite plift_or.
        eapply vars_locs_monotonic; eauto. unfoldq; intuition.
        intros ?. eapply H7. simpl. rewrite plift_or.
        eapply vars_locs_monotonic; eauto. unfoldq; intuition.
        lia.
     }
    
  + (* result well typed *)
    constructor.
  + eapply valq_bool; eauto.
Unshelve. eauto.
Qed.


Lemma sem_abs: forall env t T1 T2,
    sem_type (T1::env) t T2 ->
    closed_ty (length env) T1 ->
    closed_ty (length env) T2 ->
    sem_type env (tabs t) (TFun T1 T2).
Proof.
  intros. intros ? ? ? WFE ST.
  exists S.
  exists M. (* (st_tighten M (val_max (vabs E (qand p qf) t))). *)
  exists (vabs E t).
  split. 2: split. 3: split. 4: split. 5: split.
  + (* term evaluates *)
    exists 1. intros. destruct n. lia. simpl. eauto.
  + eapply stchain_refl. 
  + (* store typing *)
    eauto.
  + simpl. intros ? ? ? ?. auto.
  + (* result well typed *)
    simpl.
    assert (length env = length E) as LE. { symmetry. eapply WFE. }
    assert (pdom env = pdom E) as DE. { unfold pdom. rewrite LE. eauto. }
    split. 2: split. 3: split.
    rewrite <- LE. auto. rewrite <- LE. auto.
    intros ? ?. rewrite val_locs_abs in H2. eapply env_type_store_wf; eauto.  
    rewrite <- LE. simpl. intros ? ?. auto. 

    intros.
           
    (* INDUCTION *)
    destruct (H S' M' (vx::E)) as [S2 [M2 [vy IHW1]]].
    eapply envt_extend_full; eauto. 
    rewrite <- LE. auto. auto.
    
    destruct IHW1 as [? IHW1].
    exists S2, M2, vy. intuition.

    intros ? ? ? ?. rewrite H8; eauto.
    intros ?. eapply H11. 
    destruct H14 as [? [? [? [? ?]]]].
     
    rewrite val_locs_abs in *. 
    bdestruct (x =? length E); intuition.
    left. subst x. rewrite indexr_head in H15. inversion H15. subst x0. auto.
    right. simpl. rewrite indexr_skip in H15. 2: lia. 
    eexists. split. 2: eexists; eauto. rewrite plift_diff, plift_one. 
    split. simpl in H14. auto. unfoldq; intuition.
    
    eapply valt_extend1; eauto. rewrite <- LE. auto.
    
    intros ? ?. destruct (H12 x). auto.
    simpl in H13. destruct H13 as [? [? [? [? ?]]]].
    bdestruct (x0 =? length E). subst x0. 
    rewrite indexr_head in H14. inversion H14. inversion H17. subst x1.
    right. left. auto.
    rewrite indexr_skip in H14. 
    left. rewrite val_locs_abs.  eexists; eauto. split. 2: eexists; eauto.
    simpl. rewrite plift_diff, plift_one. split; auto. lia.
    right. right. auto.
  + simpl. eapply valq_abs; eauto.
Qed.



Lemma sem_app: forall env f t T1 T2,
    sem_type env f (TFun T1 T2)  ->  
    sem_type env t T1 ->   
    sem_type env (tapp f t) T2.
Proof.
  intros. intros S0 ? ? WFE ST.
  rename H into IHW1. rename H0 into IHW2. 
  destruct (IHW1 S0 M E) as [S1 [M1 [vf [IW1 [SC1 [ST1 [SE1 [HVF HQF]]]]]]]].
  eapply envt_tighten; eauto. simpl. rewrite plift_or. unfoldq; intuition.
  auto. 
  assert (env_type M1 E env (plift (fv (length E) t))) as WFE1. { eapply envt_store_extend; eauto. eapply envt_tighten; eauto. simpl. rewrite plift_or. unfoldq; intuition. }
  destruct (IHW2 S1 M1 E WFE1 ST1) as [S2 [M2 [vx [IW2 [SC2 [ST2 [SE2 [HVX HQX]]]]]]]]. 

  (* vf is a function value: it can eval its body *)
  destruct vf; try solve [inversion HVF]. 

  destruct HVF; intuition.
  rename H3 into HVF.
  destruct (HVF S2 M2 vx) as [S3 [M3 [vy [IW3 [SC3 [ST3 [SE3 [HVY HQY]]]]]]]]; eauto. 

  eapply stchain_tighten; eauto.  

  intros ? ?.  eapply val_locs_decide; eauto.

  (* EVALUATION *)
  exists S3, M3, vy. split. 2: split. 3: split. 4: split. 5: split.
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

  + eapply stchain_chain''. eapply stchain_chain''. eauto. eauto. eapply SC1. eauto. intros ? ?. eapply SC2. eapply SC1. eauto. 
    
  (* STORE_TYPE *)
  + eauto.

  + assert (length S0 = length M) as L0. destruct ST; intuition.
    assert (length M <= length M1) as L1. eapply st_mono in SC1. auto.
    assert (length M1 <= length M2) as L2. eapply st_mono in SC2. auto.
    intros ? ? PV. intros IS. rewrite SE3; eauto. { 
      intros ?. eapply PV.
      simpl. rewrite plift_or.  destruct H2. destruct (HQX l0). auto.
      eapply vars_locs_monotonic; eauto. unfoldq; intuition.
      destruct H3. apply indexr_var_some' in IS. unfoldq; intuition. 
      destruct (HQF l0). auto. 
      eapply vars_locs_monotonic; eauto. unfoldq; intuition.
      destruct H3. apply indexr_var_some' in IS. unfoldq; intuition. 
    } {
      rewrite SE2; eauto. {
        intros ?. eapply PV. simpl. rewrite plift_or. eapply vars_locs_monotonic; eauto. unfoldq; intuition.
      } {
        rewrite SE1; eauto. intros ?. eapply PV. simpl. rewrite plift_or. eapply vars_locs_monotonic; eauto. unfoldq; intuition.
      }
    }

 
  (* VAL_TYPE *)
  + eapply HVY.
  + assert (st_chain M1 M3 (st_locs M1)). { eapply stchain_chain''; eauto. eapply SC2; eauto. }
    assert (length M1 <= length M3) as A. { eapply st_mono in H2. auto. }
    assert (st_chain M M2 (st_locs M)). { eapply stchain_chain''; eauto. eapply SC1; eauto. }
    assert (length M <= length M2) as B. { apply st_mono in H3. auto. }
  intros ? ?. destruct (HQY x). auto. destruct (HQF x); auto.
  left. eapply vars_locs_monotonic; eauto. simpl. rewrite plift_or. unfoldq; intuition.
  right. auto.
  destruct H5 as[? | ?].
  destruct (HQX x). auto. simpl. rewrite plift_or. 
  left. eapply vars_locs_monotonic; eauto.  unfoldq; intuition.
  right. intros ?. eapply H6. eapply st_mono in SC1. unfold st_locs in *. unfoldq; intuition.
  right. intros ?. eapply H5. eapply st_mono in SC1, SC2. unfoldq; intuition.
Qed.

Lemma sem_seq: forall env t1 t2
  (E1: sem_type env t1 TBool)
  (E2: sem_type env t2 TBool),
  sem_type env (tseq t1 t2) TBool.
Proof.
  intros. intros S1 M1 H WFE ST. simpl in WFE. rewrite plift_or in WFE.
  (* E1 *)
  assert (env_type M1 H env (plift (fv (length H) t1))) as WFE1. eapply envt_tighten; eauto. unfoldq; intuition.
  destruct (E1 S1 M1 H WFE1 ST) as [S2 [M2 [v1 [IE1 [SC1 [ST1 [SE1 [HV1 HQ1]]]]]]]].
  destruct v1; try solve [inversion HV1]. simpl in HV1.

  (* E2 *) 
  assert (env_type M2 H env (plift (fv (length H) t2))) as WFE2. 
  eapply envt_store_extend in WFE. eapply envt_tighten; eauto. unfoldq; intuition.
  eauto.
  destruct (E2 S2 M2 H WFE2 ST1) as [S3 [M3 [v2 [IE2 [SC2 [ST2 [SE2 [HV2 HQ2]]]]]]]].
  destruct v2; try solve [inversion HV2]. simpl in HV2.

  exists S3.
  exists M3, (vbool (b && b0)).
  split. 2: split. 3: split. 4: split. 5: split. 
  + destruct IE1 as [n1 IE1].
    destruct IE2 as [n2 IE2].
    exists (S(n1 + n2)). intros. destruct n. intuition.
    simpl. rewrite IE1. rewrite IE2. eauto. lia. lia.

  + eapply stchain_chain''; eauto. eapply SC1.
  
  + eauto.
  
  + intros ? ? ? ?. erewrite SE2; eauto. intros ?. eapply H0.
    simpl. rewrite plift_or. eapply vars_locs_monotonic; eauto. unfoldq; intuition.
    erewrite SE1; eauto. intros ?. eapply H0. simpl. rewrite plift_or. eapply vars_locs_monotonic; eauto. unfoldq; intuition.
  + constructor.
  + eapply valq_bool; eauto.
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


Lemma hast_term_closed: forall t G T,
    has_type G t T ->
    psub (plift (fv (length G) t)) (pdom G).
Proof.
  intros. induction H.
  - unfoldq. intuition.
  - unfoldq. intuition.
  - simpl. rewrite plift_one. eapply indexr_var_some' in H. unfoldq. intuition. 
  - unfoldq. intuition.
  - unfoldq. intuition.
  - simpl. rewrite plift_or. unfoldq. intuition.
  - simpl. rewrite plift_or. unfoldq. intuition.
  - simpl in *. rewrite plift_diff, plift_one. unfoldq. intuition.
    eapply IHhas_type in H3. simpl in *. unfoldq. intuition.
  - simpl. rewrite plift_or. unfoldq. intuition. 
Qed.


(* Semantic type safety and termination: if the term is well-typed, then 
   it evaluates to an actual value (not stuck and not a timeout) of the
   same time (for large enough n) *)

Corollary safety : forall t T,
  has_type [] t T -> 
  exp_type [] st_zero [] t T.
Proof. 
  intros. eapply fundamental_property in H as H'; eauto.
  destruct (H' [] st_zero []). 
  - unfold env_type. intuition.
    intros ? ?. eapply hast_term_closed in H. eapply H in H0. unfoldq. intuition.
    inversion H0.
  - unfold store_type; intuition. unfold st_locs, st_zero in *. unfoldq. simpl in *. lia. 
  - destruct H0. eexists. eexists. eauto.
Qed.

End STLC.
