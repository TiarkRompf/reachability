(* Full safety for STLC *)

(* based on stlc_reach.v and stlc_ref.v *)
(* based on stlc_reach_ref_wip_overlap.v *)

(* 

Simply-typed lambda calculus with reachability types, combined 
proof of termination and type soundness (using logical relations).

THIS FILE:

- types and qualifiers
  - overlap (explicit transitive closure)
  - self refs
  - fresh flag
  - no deep subtyping, self/arg refs 
  - no parametric polymorphism

- references
  - boolean refs only
  - mutation with put/get
  - no nested refs

- effects
  - no effects


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

(* ---------- qualifier sets ---------- *)

Definition qif (b:bool) q (x:nat) := if b then q x else false.


Definition pl := nat -> Prop.

Definition pempty: pl := fun x => False.                            (* empty set *)

Definition pone (x:nat): pl := fun x' => x' = x.                    (* singleton set *)

Definition pand p1 p2 (x:nat) := p1 x /\ p2 x.                      (* intersection *)

Definition por p1 p2 (x:nat) := p1 x \/ p2 x.                       (* union *)

Definition pnot p1 (x:nat) := ~ p1 x.                               (* complement *)

Definition pdiff p1 p2 (x:nat) := p1 x /\ ~ p2 x.                   (* difference *)

Definition pnat n := fun x' =>  x' < n.      (* numeric bound *)

Definition pdom {X} (H: list X) := fun x' =>  x' < (length H).      (* domain of a list *)

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
  | TFun   : ty -> bool -> bool -> ql ->
             ty -> bool -> bool -> bool -> ql ->
             ty
.

(* TFun
        T1      : argument type

        q1fn    : argument may alias function?
        q1fr    : argument may be fresh?
        q1      : argument reachability qualifer (set of variables)

        T2      : result type

        q2f     : result may alias function?
        q2x     : result may alias argument?
        q2fr    : result may be fresh?
        q2      : argument reachability qualifer (set of variables)

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
.


Inductive vl : Type :=
  | vbool : bool -> vl
  | vref  : id -> vl
  | vabs  : list vl -> ql -> tm -> vl    (* closure record  *)
                                         (* XX: record free vars *)
.

Definition venv := list vl.
Definition tenv := list (ty * bool * ql).

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
| c_fun: forall m T1 T2 fn1 fr1 q1 fn2 ar2 fr2 q2,
    closed_ty m T1 ->
    closed_ty m T2 ->   (* not dependent *)
    closed_ql m q1 ->
    closed_ql m q2 ->   
    closed_ty m (TFun T1 fn1 fr1 q1 T2 fn2 ar2 fr2 q2)
.



(* trans(q1) = q1 \/ trans(lookup(q1)) *)

Fixpoint vars_trans_fix (env: tenv) (q: ql): ql :=
  match env with
  | [] => q
  | (T, fr, q')::env =>
      if q (length env) then qor (vars_trans_fix env q) (vars_trans_fix env q') else vars_trans_fix env q
  end.

Definition vars_trans' G q := plift (vars_trans_fix G q).

Definition var_trans G x1 x2 :=
  exists T fr q,
    indexr x1 G = Some (T, fr, q) /\
      vars_trans' G q x2.

Definition vars_trans G q1 x1 :=
  q1 x1 \/
    exists x2,
      q1 x2 /\
        x1 < x2 /\
        var_trans G x2 x1.


(* ---------- syntactic typing rules ---------- *)

Inductive has_type : tenv -> tm -> ty -> ql -> bool -> ql -> Prop :=
| t_true: forall env p,
    has_type env ttrue TBool p false qempty
| t_false: forall env p,
    has_type env tfalse TBool p false qempty
| t_var: forall x env T p fr q,
    indexr x env = Some (T, fr, q) ->
    (plift p) x ->
    has_type env (tvar x) T p false (qone x)
| t_ref: forall t env p fr q,
    has_type env t TBool p fr q ->
    has_type env (tref t) (TRef TBool) p true q
| t_get: forall t env p fr q,
    has_type env t (TRef TBool) p fr q ->
    has_type env (tget t) TBool p false qempty 
| t_put: forall t1 t2 env p fr1 q1 fr2 q2,
    has_type env t1 (TRef TBool) p fr1 q1 ->
    has_type env t2 TBool p fr2 q2 ->
    has_type env (tput t1 t2) TBool p false qempty 
| t_app: forall env f t T1 T2 p frf qf frx qx fn1 fr1 q1 fn2 ar2 fr2 q2,
    has_type env f (TFun T1 fn1 fr1 q1 T2 fn2 ar2 fr2 q2) p frf qf->  
    has_type env t T1 p frx qx ->
    (* ---- different app cases: *)
    (if fn1 then
       if fr1 then
         True
       else
         (frx = false /\ (exists x0, f = tvar x0 /\ psub (plift qx) (pone x0)) \/
            frx = false /\ psub (plift qx) (plift q1))
     else
       if fr1 then
         psub (pand 
                 (vars_trans' env qf)
                 (vars_trans' env qx))
           (plift q1)
       else
         frx = false /\ psub (plift qx) (plift q1)) ->
    (* ---- *)
    psub (plift q2) (plift p) ->   (* this is necessary (so far!) *)
    has_type env (tapp f t) T2 p
      (fn2 && frf || ar2 && frx || fr2)
      (qor (qif fn2 qf) (qor (qif ar2 qx) q2))
| t_abs: forall env t T1 T2 p fn1 fr1 q1 fn2 ar2 fr2 q2 qf,
    has_type ((T1, fr1, (qand p (qor q1 (qif fn1 qf))))::env) t T2 
      (qor (qand p qf) (qone (length env)))
      fr2
      (qor q2 (qor (qif ar2 (qone (length env)))(qif fn2 (qand p qf)))) ->
    psub (plift q1) (plift p) ->   (* relax? necessary so far *)
    closed_ty (length env) T1 ->
    closed_ty (length env) T2 ->
    closed_ql (length env) q1 ->
    closed_ql (length env) q2 ->
    closed_ql (length env) qf ->
    has_type env (tabs (qand p qf) t)
      (TFun T1 fn1 fr1 q1 T2 fn2 ar2 fr2 q2)
      p false qf
| t_sub: forall env y T p fr1 q1 fr2 q2,
    has_type env y T p fr1 q1 ->
    psub (plift q1) (plift q2) ->
    psub (plift q2) (pdom env)  ->
    has_type env y T p (fr1 || fr2)  q2
| t_sub_var: forall env y T p fr1 q1 qx x Tx,
    has_type env y T p fr1 q1 ->
    plift q1 x ->
    indexr x env = Some (Tx, false, qx) ->
    psub (plift qx) (plift p) -> (* necessary? *)
    has_type env y T p fr1 (qor (qdiff q1 (qone x)) qx)
.



(* ---------- operational semantics ---------- *)


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
                    | Some v => (update M'' x vx, Some (Some v))
                    | _ => (M'', Some None)
                    end
              end
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

Definition val_locs v := plift (val_locs_fix v). 

Definition var_locs E x l := exists vx, indexr x E = Some vx /\ val_locs vx l.

Definition vars_locs E q l := exists x, q x /\ var_locs E x l.



(* store typings / "worlds" *)

(* length and set of accessible locations *)

Definition stty: Type := nat * pl.

Definition st_length (M: stty) := fst M.
Definition st_locs (M: stty) := snd M.

Definition store_type (S: stor) (M: stty) :=
  length S = st_length M /\
    forall l,
      st_locs M l ->
      exists b,
        indexr l S = Some (vbool b).

Definition st_zero: stty :=
  (0, pempty).

Definition st_plus M1 M2: stty :=
  (st_length M1 + st_length M2,
    por (st_locs M1) (st_locs M2)).

Definition pstdiff M' M :=
  (* pdiff (pdom (M'++M)) (pdom M) *)
  pdiff (st_locs M') (st_locs M).

#[global] Hint Unfold st_length.
#[global] Hint Unfold st_locs.
#[global] Hint Unfold st_plus.
#[global] Hint Unfold pstdiff.


Definition st_extend M1 M2 :=
  st_length M1 <= st_length M2 /\
psub (st_locs M1) (st_locs M2).


Lemma stchain_refl: forall M,
    st_extend M M.
Proof.
  intros. unfold st_extend in *.
  intuition. intros ? Q. eauto.
Qed.

Lemma stchain_chain: forall M1 M2 M3,
    st_extend M1 M2 ->
    st_extend M2 M3 ->
    st_extend M1 M3.
Proof.
  intros. unfold st_extend in *.
  intuition. intros ? Q. eauto.
Qed.



(* value interpretation of types *)

Fixpoint val_type (M:stty) (H:venv) v T : Prop :=
  match v, T with
  | vbool b, TBool =>
      True
  | vref l, TRef TBool =>
      st_locs M l
  | vabs G py ty, TFun T1 fn1 fr1 q1 T2 fn2 ar2 fr2 q2 =>
        closed_ty (length H) T1 /\
        (psub (plift q1) (pdom H)) /\
        closed_ty (length H) T2 /\
        (psub (plift q2) (pdom H)) /\
        (psub (val_locs v) (st_locs M)) /\
        (forall S' M' vx,
            st_extend M M'
            ->
            store_type S' M'
            ->
            val_type
              M'
              H
              vx
              T1
            -> 
              psub (val_locs vx)
                (por (pif fn1 (val_locs v))
                   (por (pif fr1 (pnot (val_locs v)))
                      (vars_locs H (plift q1))))
            ->
              exists S'' M'' vy,
                tevaln
                  S'
                  (vx::G)
                  ty
                  S''
                  vy
                /\
                  st_extend M' M''
                /\
                  store_type S'' M''
                /\
                  val_type
                    M''
                    H
                    vy
                    T2
                /\
                  psub (val_locs vy)
                    (por (pand (vars_locs H (plift q2)) (val_locs v)) (* allow v \/ vx? *)
                       (por (pif fn2 (val_locs v))
                          (por (pif ar2 (val_locs vx))
                             (pif fr2 (pstdiff M'' M'))))))
  | _,_ =>
      False
  end.


Definition val_qual (M M1: stty) H v fr (q: pl) :=
  psub (val_locs v)
    (por (vars_locs H q)
       (pif fr (pstdiff M1 M))).


Definition exp_type S M H t T p fr q :=
  exists S' M' v,
    tevaln S H t S' v /\
    st_extend M M' /\
    store_type S' M' /\
    val_type M' H v T /\
    val_qual M M' H v fr (pand p q).



Definition env_type M H G p :=
  length H = length G /\
    psub p (pdom H) /\
    (forall x T fr (q:ql),
        indexr x G = Some (T, fr, q) ->
        (* p x -> not actually needed *)
        exists v : vl,
          psub (plift q) (pdom H) /\
          closed_ql x q /\
          indexr x H = Some v /\
          val_type M H v T /\
          (fr = false -> psub (val_locs v) (vars_locs H (plift q)))) /\
    (forall q q',
        psub q p ->
        psub q' p ->
        psub (pand (vars_locs H q) (vars_locs H q'))
          (vars_locs H (pand (vars_trans G q) (vars_trans G q')))).


Definition sem_type G e T p fr q :=
  forall S M E,
    env_type M E G p ->
    store_type S M  ->
    exp_type S M E e T p fr q. 


#[global] Hint Constructors ty.
#[global] Hint Constructors tm.
#[global] Hint Constructors vl.


#[global] Hint Constructors has_type.

#[global] Hint Constructors option.
#[global] Hint Constructors list.


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

Lemma plift_if: forall a (c: bool),
    plift (qif c a) = pif c (plift a).
Proof.
  intros. eapply functional_extensionality.
  intros. eapply propositional_extensionality.
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



(*----------- val_locs lemmas   -----------*)

(*
alternative: 

Definition val_locs' v: pl :=
  match v with
  | vbool _ => pempty
  | vref x  => pone x
  | vabs H q t => vars_locs H (plift q)
  end.

Fixpoint val_locs_fix (v: vl): ql :=
  match v with
  | vbool  _ => qempty
  | vref x   => qone x
  | vabs H q t  =>
      (* alternative: use indexr x, for x < length H *)
      let fix vars_locs_fix (H: list vl) :=
        match H with
        | v :: H => qor (qif (q (length H)) (val_locs_fix v)) (vars_locs_fix H)
        | [] => qempty
        end
      in vars_locs_fix H
  end.

Lemma plift_val_locs: forall v,
    plift (val_locs_fix v) = val_locs' v.
Proof.
  intros. eapply functional_extensionality.
  intros. eapply propositional_extensionality.
  unfold val_locs, plift in *.
  destruct v. 
  simpl in *. todo: simple ...
  simpl in *. todo: simple ...
  simpl in *.
  induction l.
  + unfold qempty, vars_locs, plift, var_locs. intuition.
    destruct H as (? & ? & ? & ? & ?). inversion H0.
  + intros. unfold qor, qif in *.
    remember (q (length l)) as C1.
    remember (val_locs_fix a x) as C2.
    destruct C1. destruct C2. simpl in *.
    * intuition. exists (length l).
      unfold plift, var_locs, val_locs. intuition.
      exists a. rewrite indexr_head. unfold plift. intuition.
    * simpl in *. intuition. destruct H2.
      exists x0. destruct H0. intuition.
      destruct H2. exists x1. intuition.
      rewrite indexr_extend1 in H3. intuition eauto.
      eapply H0. destruct H1. intuition. destruct H3.
      rewrite indexr_skip in H1. exists x0. intuition. exists x1. eauto.
      unfold plift in H2. intros ?. subst.
      rewrite indexr_head in H1. inversion H1. inversion H3. subst a.
      unfold val_locs, plift in H4. congruence.
    * simpl in *. intuition. destruct H2. 
      
    assert (vars_locs l (plift q) x).
    eapply IHl. symmetry. unfold val_locs_fix in HeqC2. eapply HeqC2. 
    eexists. split. 2: { exeauto. 
                         destruct H0 as (? & ? & ? & ? & ?).
      exists x0. intuition. exists x1.
      rewrite indexr_extend1 in H1. intuition eauto.
*)

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




(* ---------- closedness, vars_locs lemmas  ---------- *)

Lemma closedq_extend : forall {m q}, closed_ql m q -> 
  forall {m'}, m <= m' -> closed_ql m' q.
Proof.  
    intros. unfold closed_ql in *. intros. 
    specialize (H x). intuition.
Qed.

Lemma closedty_extend : forall {m T}, closed_ty m T -> 
  forall {m'}, m <= m' -> closed_ty m' T.
Proof. 
    intros. induction T; constructor.
    all: inversion H; subst; intuition.
    eapply closedq_extend; eauto.
    eapply closedq_extend; eauto.
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

Lemma vars_locs_extend1: forall H v q l,
    vars_locs H q l ->
    vars_locs (v :: H) q l.
Proof. 
  intros. unfoldq. intuition.
  destruct H0 as (? & ? & ? & ? & ?).
  rewrite indexr_extend1 in H1.
  exists x. intuition. exists x0. intuition eauto.
Qed.

Lemma vars_locs_monotonic: forall H q q',
    psub q q' ->
    psub (vars_locs H q) (vars_locs H q').
Proof. 
  intros. unfoldq. intros. 
  destruct H1; intuition. specialize (H0 x0); intuition.
  exists x0; intuition.
Qed.

Lemma vars_locs_and: forall H q1 q2,
  psub (vars_locs H (pand q1 q2)) 
  (pand  (vars_locs H q1) (vars_locs H q2)). 
Proof.
  intros. unfoldq. intros; intuition.
  destruct H0. exists x0. intuition.
  destruct H0. exists x0. intuition.
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


(*----------- saturation / trans closure lemmas   -----------*)

Definition telescope (env: tenv) := forall x T fr1 q1,
    indexr x env = Some (T, fr1, q1) -> closed_ql x q1. 

Lemma telescope_shrink: forall env T fr q,
    telescope ((T,fr,q)::env) -> telescope env.
Proof.
  intros G. intros.
  unfold telescope in *. intros.
  eapply H. eapply indexr_extend1 in H0. eapply H0.
Qed.

Lemma telescope_extend: forall env T fr q,
    closed_ql (length env) q ->
    telescope env -> telescope ((T,fr,q)::env).
Proof.
  intros G. intros.
  unfold telescope in *. intros.
  bdestruct (x =? length G).
  subst. rewrite indexr_head in H1. inversion H1. subst. eauto.
  rewrite indexr_skip in H1; eauto. 
Qed.

Lemma vars_trans_monotonic: forall env q,
    psub (plift q) (plift (vars_trans_fix env q)).
Proof.
  intros G. induction G; intros.
  - simpl. unfoldq. intuition.
  - simpl. intuition. intros ? ?. 
    eapply IHG in H. 
    destruct (q (length G)). rewrite plift_or. left. eauto. eauto. 
Qed.

Lemma vars_trans_closed: forall env q x,
    telescope env -> 
    plift (vars_trans_fix env q) x ->
    x >= length env ->
    plift q x.
Proof.
  intros G. induction G; intros.
  - eauto.
  - simpl in *. destruct a as ((? & ?) & ?).
    assert (telescope G). eapply telescope_shrink; eauto.
    destruct (q (length G)).
    + rewrite plift_or in H0. destruct H0.
      * eapply IHG; eauto. lia.
      * assert (plift q0 x). {
          eapply IHG; eauto. lia.
        }
        eapply (H (length G)) in H3. unfoldq. lia. 
        eapply indexr_head.
    +  eapply IHG; eauto. lia.
Qed.

Lemma vars_trans_extend: forall G a q1,
    psub (plift (vars_trans_fix G q1)) (plift (vars_trans_fix (a::G) q1)).
Proof.
  intros. intros ? ?. destruct a. destruct p. simpl.
  rewrite plift_if1, plift_or.
  destruct (q1 (length G)). unfoldq. intuition. eauto. 
Qed.

Lemma vt_extend: forall G a q1,
    psub (vars_trans G q1) (vars_trans (a::G) q1).
Proof.
  intros. intros ? ?. destruct H.
  - left. intuition.
  - right. destruct H as (? & ? & ? & T2 & fr2 & q2 & IX & VT).
    exists x0. intuition. exists T2, fr2, q2. intuition.
    rewrite indexr_extend1 in IX. eapply IX. eapply vars_trans_extend. eauto. 
Qed.

Lemma vt_mono: forall G q1 q2,
    psub q1 q2 ->
    psub (vars_trans G q1) (vars_trans G q2).
Proof.
  intros. intros ? ?. destruct H0.
  - left. eauto.
  - right. destruct H0 as (? & ? & ?).
    exists x0. intuition.
Qed.


Lemma plift_vt: forall G q,
    telescope G ->
    plift (vars_trans_fix G q) = vars_trans G (plift q).
Proof.
  intros G. induction G.
  - intros. eapply functional_extensionality.
    intros. eapply propositional_extensionality.
    unfold vars_trans_fix, vars_trans, var_trans. intuition.
    destruct H1 as (? & ? & ? & ? & ? & ? & ? & ?). inversion H2.
  - intros. eapply functional_extensionality.
    intros. eapply propositional_extensionality.
    simpl. destruct a as [[? ?] ?]. intuition.
    + (* ql -> pl *)
      rewrite plift_if1, plift_or in H0.
      
      remember (q (length G)) as c.
      destruct c. (* length G in q ? *)
      * (* length G in q *)
        destruct H0. (* q or q0 ? *)
        -- (* x in q *)
           rewrite IHG in H0.
           eapply vt_extend. eauto.
           eapply telescope_shrink. eauto.
        -- (* x in q0 *)
           right. exists (length G). intuition.
           unfold plift. eauto.
           assert (closed_ql (length G) q0).
           eapply H. rewrite indexr_head. eauto.
           bdestruct (x <? length G). eauto. 
           eapply vars_trans_closed in H0.
           eapply H1. eapply H0.
           eapply telescope_shrink. eauto.
           eauto.
           (* now the var_trans' *)
           eexists. eexists. eexists. 
           rewrite indexr_head. intuition.
           unfold vars_trans'. simpl.
           assert (closed_ql (length G) q0).
           eapply H. rewrite indexr_head. eauto.
           remember (q0 (length G)) as d.
           destruct d. symmetry in Heqd. eapply H1 in Heqd. lia. 
           eauto.
      * (* length G not in q *)
        rewrite IHG in H0.
        eapply vt_extend. eauto.
        eapply telescope_shrink. eauto.
    + (* pl -> ql *)
      rewrite plift_if1, plift_or.

      destruct H0.
      * (* x in q *)
        eapply vars_trans_monotonic in H0.
        destruct (q (length G)). left. eauto. eauto.
      * (* ex x2, ... *)
        destruct H0 as (? & ? & ? & T1 & fr1 & q1 & ? & ?).
        bdestruct (x0 =? length G).
        -- (* x0 = length G *)
          subst x0. rewrite H0. rewrite indexr_head in H2.
          inversion H2. subst t b q0.
           right. unfold vars_trans' in H3. simpl in H3.
           destruct (q1 (length G)). rewrite plift_or in H3.
           destruct H3; eauto. eauto.
        -- (* x0 < length G *)
           assert (closed_ql x0 q1). eapply H. eauto. 
           rewrite indexr_skip in H2; eauto.
           unfold vars_trans' in H3. simpl in H3. 
           remember (q1 (length G)) as c. destruct c.
           ++ (* length G in q1? contradiction *)
             assert (x0 < length G). rewrite indexr_extend in H2. lia.
             assert (length G < x0). eapply H5. eauto.
             lia.
           ++ (* length G not in q1 *)
             assert (plift (vars_trans_fix G q) x). {
               rewrite IHG. right. exists x0. intuition.
               exists T1, fr1, q1. intuition.               
               eapply telescope_shrink; eauto. }
             destruct (q (length G)). left. eauto. eauto.
Unshelve. apply [].
Qed.


(* ---------- store_type lemmas  ---------- *)

Lemma stplus_assoc: forall M1 M2 M3,
    st_plus M1 (st_plus M2 M3) = st_plus (st_plus M1 M2) M3.
Proof.
  intros. unfold st_plus. simpl.
  replace (st_length M1 + st_length M2 + st_length M3)
    with (st_length M1 + (st_length M2 + st_length M3)).
  replace (por (por (st_locs M1) (st_locs M2)) (st_locs M3))
    with (por (st_locs M1) (por (st_locs M2) (st_locs M3))).
  eauto.
  apply functional_extensionality. intros. 
  apply propositional_extensionality. unfoldq. intuition.
  lia.
Qed.

Lemma stplus_zero: forall M1,
    st_plus st_zero M1 = M1.
Proof.
  intros. unfold st_plus. simpl.
  replace (por pempty (st_locs M1)) with (st_locs M1).
  destruct M1. simpl. eauto. 
  apply functional_extensionality. intros. 
  apply propositional_extensionality. unfoldq. intuition.
Qed.


Lemma storet_wf: forall S M,
    store_type S M ->
    psub (st_locs M) (pdom S).
Proof.
  intros. intros ? ?. eapply H in H0.
  destruct H0. eapply indexr_var_some'. eauto. 
Qed.


(* ---------- val_type lemmas  ---------- *)

Lemma valt_wf: forall T M H v,
    val_type M H v T ->
    psub (val_locs v) (st_locs M).
Proof. 
  intros T. induction T; intros; destruct v; simpl in *; intuition.
  + rewrite val_locs_bool. auto. unfoldq. intuition.
  + rewrite val_locs_ref.
    destruct T; try contradiction.
    unfoldq. intuition. congruence.
Qed.


Lemma valt_closed: forall T M H v,
    val_type M H v T ->
    closed_ty (length H) T.
Proof. 
  intros T. induction T; intros; destruct v; simpl in *; intuition.
  + econstructor.
  + destruct T; try contradiction.
    repeat econstructor; eauto.
  + econstructor; eauto. 
Qed.


Lemma valt_store_extend: forall T M' M H v,
    val_type M H v T ->
    st_extend M M' ->
    val_type M' H v T.
Proof.  
  intros T. induction T; intros; destruct v; simpl in *; intuition.
  - destruct T; try contradiction.
    unfold st_extend in *. intuition.
  - intros ? Q. eapply H1. eauto.
  - destruct (H7 S' M'0 vx) as [S'' [M'' [vy  [HEY HVY]]]].
    eapply stchain_chain. eauto. eauto.
    eauto.
    eauto.
    eauto.
    exists S'', M'', vy.
    intuition. 
Qed. 


Lemma valt_extend: forall T M H' H v,
    closed_ty (length H) T ->
    val_type M (H'++H) v T <-> val_type M H v T.
Proof.
  intros T. induction T; split; intros; destruct v; simpl in *; intuition.
  - inversion H0. auto.
  - inversion H0. auto.
  - inversion H0. auto.
  - inversion H0. auto.
  - (* Abs shrink *)
    inversion H0. subst.
    rename q into q2. 
    destruct (H7 S' M' vx) as [S'' [M'' [vy [HEY HVY]]]]. eauto. eauto.
      eapply IHT1; eauto.
    rewrite vars_locs_extend; auto.
    exists S'', M'', vy. intuition.
    eapply IHT2; eauto.
    rewrite vars_locs_extend in H15.
    eauto. eauto.
  - eapply closedty_extend; eauto.
  - eapply closedq_extend; eauto.
  - eapply closedty_extend; eauto.
  - unfoldq. rewrite app_length. intuition. eapply H4 in H6. lia.
  - (* Abs grow *)
    inversion H0. subst.
    rename q into q2. 
    destruct (H7 S' M' vx) as [S'' [M'' [vy [HEY [ST2 [HVY HQY]]]]]]. eauto. eauto.
      eapply IHT1; eauto.
      rewrite vars_locs_extend in H10; auto.
    exists S'', M'', vy. intuition.
    eapply IHT2; eauto.
    rewrite vars_locs_extend. 
    eauto.
    eauto.
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
    val_qual M M1 H (vbool b) false q.
Proof.
  intros. unfoldq. rewrite val_locs_bool. intuition.
Qed.

(* TODO: currently inlined in sem_ref, could become
   a lemma again. *)
(*
Lemma valq_fresh: forall M M' H p q,
    val_qual M (st_plus (1,pone (st_length (st_plus M' M))) (st_plus M' M)) H (vref (st_length (st_plus M' M))) p true q.
Proof.
  intros. right. unfold pstdiff. unfoldq. simpl. unfoldq. 
  (* valq: index out of range*)
  rewrite stplus_length in *.
  rewrite val_locs_ref in *.
  intuition. unfoldq.
  lia. unfoldq. lia.
Qed.*)


Lemma valq_abs: forall M M1 H t p fr q,
    val_qual M M1 H (vabs H (qand p q) t) fr (pand (plift p) (plift q)).
Proof.
  intros. unfoldq.
  rewrite val_locs_abs.
  rewrite plift_and.
  intuition. 
Qed.


Lemma valq_sub: forall M M1 H v q fr fr' q',
    val_qual M M1 H v fr q ->
    psub q q' ->
    psub q' (pdom H) ->
    val_qual M M1 H v (fr || fr') q'.
Proof.
  intros. unfoldq. intuition.
  destruct (H0 x) as [H_q | H_fr]. intuition.
  - (* q  *) destruct H_q. left. exists x0. intuition.
  - (* fr *) destruct fr. 2: contradiction. right. eauto.
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

Lemma envt_telescope: forall M H G p,
    env_type M H G p -> telescope G.
Proof.
  intros. destruct H0 as (? & ? & ? & ?).
  intros ? ? ? ? ?. edestruct H2; eauto.
  intuition.
Qed.


Lemma env_type_store_wf: forall M H G p q,
    env_type M H G p ->
    psub q p ->
    psub (vars_locs H q) (st_locs M).
Proof.
  intros. destruct H0 as [L [P [W1 W2]]]; intuition.
  unfoldq. intuition.
  destruct H0 as [? [? ?]].
  assert (p x0). eapply H1. eauto.
  assert (x0 < length H). eauto.
  destruct H2 as [? [? ?]]. 

  assert (exists xtq, indexr x0 G = Some xtq) as TY.
  rewrite L in H4.  eapply indexr_var_some in H4. intuition.
  destruct TY as [TQ  ?]. destruct TQ as [[T0 fr0] q0].
  destruct (W1 x0 T0 fr0 q0) as [vx [? ?]]. eauto.
  
  intuition. apply valt_wf in H10. 
  rewrite H8 in H2. inversion H2. subst.
  unfoldq. intuition.
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
    destruct W as [W ?].
    destruct (W x T fr q); eauto. 
  - intros.
    destruct W as [? W].
    eapply W.
    unfoldq. intuition.
    unfoldq. intuition.
Qed.

Lemma envt_store_extend: forall M M' H G p,
    env_type M H G p ->
    st_extend M M' ->
    env_type M' H G p.
Proof.
  intros. destruct H0 as [L [P W]]. 
  repeat split; auto. intros.
  destruct W as [W W'].
  destruct (W _ _  _ _ H0) as [vx [QH [CL [IH [HVX HF]]]]]; intuition.
  exists vx; intuition.
  eapply valt_store_extend in HVX; eauto.
  intros.
  destruct W as [W' W].
  unfoldq. intuition.
Qed.

Lemma envt_extend_full: forall M M1 H G vx T1 p fr1 q1 qf,
    env_type M H G p ->
    val_type M1 H vx T1 ->
    psub qf p ->
    psub (plift q1) p -> 
    psub (pand (vars_locs H qf) (val_locs vx))
      (vars_locs H (plift q1)) ->
    (fr1 = false -> psub (val_locs vx) (vars_locs H (plift q1))) ->
    closed_ty (length H) T1 ->
    closed_ql (length H) q1 ->
    st_extend M M1 ->
    env_type M1 (vx :: H) ((T1, fr1, q1) :: G) (por qf (pone (length H))).
Proof.
  intros. apply wf_env_type in H0 as H0'. destruct H0' as (L' & PD (*& SG*)). 

  assert (env_type M1 H G p) as WFE. {
    eapply envt_store_extend; eauto. }

  remember WFE as WFE1. clear HeqWFE1.
  destruct WFE as [L [P [W1 W2]]].
  assert (psub p (pdom G)). rewrite <-PD. eauto. 

  repeat split; eauto.
  - simpl. eauto.
  - unfoldq. simpl. intuition.
  - intros.
    bdestruct (x =? length G); intuition. 
    + subst. rewrite indexr_head in H10. inversion H10. subst.
      exists vx. repeat split.
      unfoldq; intuition. simpl. 
      specialize (H2 x); intuition.
      rewrite <-L. eauto. 
      rewrite <-L. rewrite indexr_head. auto.
      eapply valt_extend1; auto.
      rewrite <-vars_locs_extend with (H':=[vx]) in H5; eauto. 
    + rewrite indexr_skip in H10. 
      specialize (W1 x T fr q H10).
      assert (x < length H). { rewrite L. apply indexr_var_some' in H10. auto. }
      rewrite indexr_skip.
      destruct W1 as [v [HSUB [TL [IH [VALT FR]]]]].
      exists v. repeat split.
      unfoldq; intuition. simpl. eapply HSUB in H13. lia.
      auto. auto.
      eapply valt_extend1. eapply valt_closed in VALT; eauto.
      auto.
      rewrite <-vars_locs_extend with (H':=[vx]) in FR; eauto. 
      lia. lia.
  - (* 2nd invariant *)
    intros q q' QSUB QSUB' x (QQ & QQ').

    destruct QQ as (? & VTQ & VLQ).
    destruct QQ' as (? & VTQ' & VLQ').

    destruct (QSUB x0); intuition; destruct (QSUB' x1); intuition.
    
    + (* qf, qf *)
      destruct (W2 (pand (pdom H) q) (pand (pdom H) q')) with (x:=x).

      intros ? ?. destruct (QSUB x2) as [? | ?]. unfoldq. intuition. 
      eauto. eauto. unfoldq. lia.
      intros ? ?. destruct (QSUB' x2) as [? | ?]. unfoldq. intuition. 
      eauto. eauto. unfoldq. lia. 

      split. 
      exists x0. unfoldq. intuition. eapply var_locs_shrink. eauto. eauto.
      exists x1. unfoldq. intuition. eapply var_locs_shrink. eauto. eauto.
      exists x2. intuition.
      destruct H13. split.
      eapply vt_extend. eapply vt_mono. 2: eapply H12. unfoldq. intuition.
      eapply vt_extend. eapply vt_mono. 2: eapply H13. unfoldq. intuition.
      eapply var_locs_extend. eauto. 

    + (* qf, x *)
      rename H4 into SEP.
      unfold pone in H11. subst x1. destruct (SEP x).
      unfoldq. intuition. exists x0. intuition.
      eapply var_locs_shrink. eauto. eauto. 
      destruct VLQ' as (? & IX & ?). rewrite indexr_head in IX. inversion IX. congruence.
  
      destruct (W2 (pand (pdom H) q) (plift q1)) with (x:=x).

      (* q *) intros ? ?. destruct (QSUB x2) as [? | ?]. unfoldq. intuition.
      eauto. eauto. unfoldq. lia.
      (* q1 *) eauto. 
      (* intros. destruct (QSUB' x2) as [? | [? | ?]]. unfoldq. intuition.
      eauto. eauto. unfoldq. lia. *)

      split. 
      exists x0. unfoldq. intuition. eapply var_locs_shrink. eauto. eauto.
      exists x1. unfoldq. intuition.

      exists x2. intuition. 
      destruct H4. split.
      eapply vt_extend. eapply vt_mono. 2: eapply H4. unfoldq. intuition.

      (* q1 expansion! *)
      right. exists (length H). intuition.
      destruct H14. rewrite indexr_extend in H14. eapply H14. 
      exists T1, fr1, q1. rewrite L. rewrite indexr_head. intuition.
      unfold vars_trans'. rewrite plift_vt. eapply vt_extend. eauto.
      eapply telescope_extend; eauto. intros ? ?. rewrite <-L. eapply P. eauto. eapply envt_telescope; eauto. 

      eapply var_locs_extend. eauto. 

    + (* x, qf *)
      rename H4 into SEP.
      unfold pone in H10. subst x0. destruct (SEP x).
      unfoldq. intuition. exists x1. intuition.
      eapply var_locs_shrink. eauto. eauto. 
      destruct VLQ as (? & IX & ?). rewrite indexr_head in IX. inversion IX. congruence.
  
      destruct (W2 (plift q1) (pand (pdom H) q')) with (x:=x).

      (* q1 *) eauto. 
      (* q' *) intros ? ?. destruct (QSUB' x2) as [? | ?]. unfoldq. intuition.
      eauto. eauto. unfoldq. lia.

      split. 
      exists x0. unfoldq. intuition. 
      exists x1. unfoldq. intuition. eapply var_locs_shrink. eauto. eauto.

      exists x2. intuition. 
      destruct H4. split.

      (* q1 expansion! *)
      right. exists (length H). intuition.
      destruct H14. rewrite indexr_extend in H14. eapply H14. 
      exists T1, fr1, q1. rewrite L. rewrite indexr_head. intuition.
      unfold vars_trans'. rewrite plift_vt. eapply vt_extend. eauto.
      eapply telescope_extend; eauto. intros ? ?. rewrite <-L. eapply P. eauto. eapply envt_telescope; eauto. 

      eapply vt_extend. eapply vt_mono. 2: eapply H10. unfoldq. intuition.

      eapply var_locs_extend. eauto. 

    + (* x, x *)
      unfold pone in H10, H11.
      subst x0 x1.

      exists (length H). intuition. split.
      left. eauto. left. eauto.
      
  Unshelve.
      eauto. eauto. 
Qed.

Lemma overlapping: forall M M' M'' H G p vf vx frf qf frx qx q1
    (WFE: env_type M H G p)
    (HQF: val_qual M M' H vf frf (pand p qf))
    (HQX: val_qual M' M'' H vx frx (pand p qx)),
    psub (val_locs vf) (st_locs M') ->
    psub (pand (vars_trans G (pand p qf)) (vars_trans G (pand p qx))) (plift q1) ->
    psub (pand (val_locs vf) (val_locs vx)) (vars_locs H (plift q1)).
Proof. 
  intros. unfoldq. intuition.
  remember WFE as WFE1. clear HeqWFE1.
  destruct WFE as [? [? [? SEP]]].
  destruct (HQF x) as [Hf_q | Hf_fr]. eauto.
  - destruct (HQX x) as [Hx_q | Hx_fr]. eauto.
    + destruct (SEP ((pand p qf)) ((pand p qx))) with (x := x).
      unfoldq. intuition.
      unfoldq. intuition.
      unfoldq. intuition.
      exists x0. intuition.
    + destruct frx. 2: contradiction.
      eapply env_type_store_wf in Hf_q; eauto. 2: { unfoldq; intuition. }
      assert False. eapply Hx_fr. eauto. contradiction.
  - destruct frf. 2: contradiction.
    destruct (HQX x) as [Hx_q | Hx_fr]. eauto.
    + eapply env_type_store_wf in Hx_q; eauto. 2: { unfoldq; intuition. }
      assert False. eapply Hf_fr. eauto. contradiction.
    + destruct frx. 2: contradiction.
      assert False. eapply Hx_fr. eapply Hf_fr. contradiction.
Qed.

(*
  destruct (HQF x) as
  bdestruct (x <? st_length M).
  - destruct (HQF x) as [Hf_q | Hf_fr]. eauto.
    destruct (HQX x) as [Hx_q | Hx_fr]. eauto. 
    
    (* unfoldq. intuition. *)
    destruct (SEP ((pand p qf)) ((pand p qx))) with (x := x).

    unfoldq. intuition.
    unfoldq. intuition.
        
    unfoldq. intuition.
    exists x0. intuition.

    (* vx fresh *)
    destruct frx. unfold pstdiff, pdiff in *. repeat rewrite stplus_length in *. lia. contradiction.
    (* vf fresh *)
    destruct frf. repeat rewrite app_length in *. lia. contradiction.

  - bdestruct (x <? length (M'++M)).
    + destruct (HQX x) as [Hx_q | Hx_fr]. eauto.
      destruct Hx_q.

      (* fresh loc in vf, also occurs in vx --> can't happen *)
      assert (psub (vars_locs H (pone x0)) (pdom M)) as L. {
        eapply env_type_store_wf. eauto. unfoldq. intuition. subst x1. eauto.
      }
      assert (x < length M). {
        eapply L. unfoldq. exists x0. intuition.
      }
      lia.

      (* vx fresh *)
      destruct frx. 2: contradiction.
      destruct Hx_fr. contradiction. 
    + (* fresh loc in vx, bigger than vf *)
      eapply H0 in H3. lia.
Qed.*)



(* ---------- main lemmas ---------- *)

Lemma sem_true: forall G p,
    sem_type G ttrue TBool p false pempty.
Proof.
  intros. intros S M H WFE ST.
  exists S, M, (vbool true).
  split. 2: split. 3: split. 4: split.
  - exists 0. intros. destruct n. lia. intuition.
  - eapply stchain_refl. 
  - eauto.
  - simpl. eauto.
  - eapply valq_bool.
Qed.
  
Lemma sem_false: forall G p,
    sem_type G tfalse TBool p false pempty.
Proof.
  intros. intros S M H WFE ST.
  exists S, M, (vbool false).
  split. 2: split. 3: split. 4: split.
  - exists 0. intros. destruct n. lia. intuition.
  - eapply stchain_refl. 
  - eauto.
  - simpl. eauto.
  - eapply valq_bool.
Qed.
  
Lemma sem_var: forall x G T (p:pl) fr q,
    indexr x G = Some (T, fr, q) ->
    p x ->
    sem_type G (tvar x) T p false (pone x).
Proof.
  intros. intros ? ? ? WFE ST.
  destruct WFE as [? [? [WFE ?]]].
  destruct (WFE x T fr q H) as [vx [HQ [TL [HI [VT ?]]]]]. 
  exists S, M, vx.
  split. 2: split. 3: split. 4: split.
  - exists 0. intros. destruct n. lia. simpl. rewrite HI. reflexivity.
  - eapply stchain_refl.
  - eauto.
  - eauto.
  - (* valq *)
  left. unfoldq. intros. exists x; intuition.
  exists vx. intuition.
Qed.

Lemma sem_ref: forall t G p fr q,
    sem_type G t TBool p fr q ->
    sem_type G (tref t) (TRef TBool) p true q.
Proof.
  intros. intros ? ? ? WFE ST. 
  destruct (H S M E WFE ST) as [S1 [M1 [vx [IW1 [SC1 [ST1 [HVX HQX]]]]]]].
  remember (length S1) as x.
  exists (vx::S1).
  exists (st_plus (1, pone x) M1).
  exists (vref x). split. 2: split. 3: split. 4: split.
  - (* expression evaluates *)
    destruct IW1 as [n1 IW1]. rename S into St.
    exists (S n1).
    intros. destruct n. lia.
    subst x. simpl. rewrite IW1. eauto. lia.
  - unfold st_plus, st_extend in *. intuition. simpl. lia.
    simpl. unfoldq. intuition. 
  - (* store typing *)
    (* lemma: storet_extend *)
    destruct ST1.
    unfold store_type in *. subst x. simpl. rewrite H0. simpl.
    intuition. simpl in H0. rewrite <-H0.
    bdestruct (l =? length S1).
    simpl in HVX. destruct vx; try contradiction. intuition eauto.
    destruct H4. inversion H4. unfoldq. congruence. 
    eapply H1. eauto. 
  - (* result well typed *)
    simpl. unfoldq. intuition.
  - (* qualifier *)
    (* eapply valq_fresh. *)
    intros ? ?. rewrite val_locs_ref in H0. 
    right. simpl. split. left. intuition.
    intros ?.
    assert (x0 < length S1). eapply storet_wf. eauto. 
    eapply SC1. eauto. inversion H0. lia. 
Qed.

Lemma sem_get: forall t env p fr q,
    sem_type env t (TRef TBool) p fr q ->
    sem_type env (tget t) TBool p false pempty.
Proof.
  intros. intros ? ? ? WFE ST.
  destruct (H S M E WFE ST) as [S1 [M1 [vx [IW1 [SC1 [ST1 [HVX HQX]]]]]]]. 
  destruct vx; try solve [inversion HVX]. simpl in HVX.
  eapply ST1 in HVX as HVX'.
  destruct HVX' as [b SI]. 
  exists S1, M1, (vbool b). split. 2: split. 3: split. 4: split.
  - (* expression evaluates *)
    destruct IW1 as [n1 IW1]. rename S into St.
    exists (S n1).
    intros. destruct n. lia.
    simpl. rewrite IW1. rewrite SI. eauto. lia.
  - eauto. 
  - (* store type *)
    eauto. 
  - (* result well typed *)
    simpl. eauto.
  - (* qualifier *)
    unfoldq. rewrite val_locs_bool; auto.
Qed.

Lemma sem_put: forall t1 t2 env p fr1 q1 fr2 q2,
    sem_type env t1 (TRef TBool) p fr1 q1 ->
    sem_type env t2 TBool p fr2 q2 ->
    sem_type env (tput t1 t2) TBool p false pempty.
Proof.
  intros. intros ? ? ? WFE ST.
  destruct (H S M E WFE ST) as [S1 [M1 [vr [IW1 [SC1 [ST1 [HVR HQR]]]]]]]. 
  eapply envt_store_extend in WFE as WFE1. 
  destruct (H0 S1 M1 E WFE1 ST1) as [S2 [M2 [vx [IW2 [SC2 [ST2 [HVX HQX]]]]]]]. 
  destruct vr; try solve [inversion HVR]. simpl in HVR.
  destruct vx; try solve [inversion HVX]. simpl in HVX.
  assert (exists b : bool, indexr i S2 = Some (vbool b)) as HVR'.
  eapply ST2. eapply SC2. eauto.
  destruct HVR' as [b0 SI].
  exists (update S2 i (vbool b)), M2, (vbool b0).
  split. 2: split. 3: split. 4: split.
  - (* expression evaluates *)
    rename S into St.
    destruct IW1 as [n1 IW1].
    destruct IW2 as [n2 IW2].
    exists (S (n1+n2)).
    intros. destruct n. lia.
    simpl. rewrite IW1. rewrite IW2. rewrite SI. eauto. lia. lia.
  - eapply stchain_chain; eauto.
  - (* store type *)
    destruct ST2. split. 
    rewrite <-update_length. eauto. 
    intros. bdestruct (i =? l).
    exists b. subst i. eapply update_indexr_hit. rewrite indexr_extend in SI. eapply SI.
    rewrite update_indexr_miss; eauto. 
  - (* result well typed *)
    simpl. eauto.
  - (* qualifier *)
    unfoldq. rewrite val_locs_bool; auto.
  - eauto. 
Unshelve.
  apply [].   
Qed.


Lemma sem_abs: forall env t T1 T2 p fn1 fr1 q1 fn2 ar2 fr2 q2 qf,
    sem_type ((T1, fr1, (qand p (qor q1 (qif fn1 qf))))::env) t T2 
      (por (pand (plift p) (plift qf)) (pone (length env)))
      fr2
      (por (plift q2) (por (pif ar2 (pone (length env)))(pif fn2 (plift (qand p qf))))) ->
    psub (plift q1) (plift p) ->   (* relax? seems necessary so far *)
    closed_ty (length env) T1 ->
    closed_ty (length env) T2 ->
    closed_ql (length env) q1 ->
    closed_ql (length env) q2 ->
    closed_ql (length env) qf ->
    sem_type env (tabs (qand p qf) t)
      (TFun T1 fn1 fr1 q1 T2 fn2 ar2 fr2 q2)
      (plift p) false (plift qf).
Proof.
  intros. intros ? ? ? WFE ST.
  exists S, M. exists (vabs E (qand p qf) t).
  split. 2: split. 3: split. 
  - (* term evaluates *)
    exists 0. intros. destruct n. lia. simpl. eauto.
  - eapply stchain_refl. 
  - (* store typing *)
    eauto. 
  - (* result well typed *)
    split. simpl. 

    assert (length env = length E) as LE. { symmetry. eapply WFE. }
    assert (pdom env = pdom E) as DE. { unfold pdom. rewrite LE. eauto. }
    
    (* rewrite DE in *. rewrite LE in *. repeat split; auto. *)
    rewrite val_locs_abs. rewrite plift_and. rewrite LE in *. intuition; eauto.
    eapply env_type_store_wf. eauto. unfoldq. intuition. 

    (* INDUCTION *)
    destruct (H S' M' (vx::E)) as [S2 [M2 [vy IHW1]]].
    
    (* ENV_TYPE*)
    eapply envt_extend_full; eauto. unfoldq. intuition.

    rewrite plift_and, plift_or, plift_if. destruct fn1.
    unfoldq. intuition. unfoldq. intuition.
    
    unfoldq. intuition.
    destruct (H9 x) as [F | [L | Q]]. eauto. {
      destruct fn1. 2: contradiction.
      rewrite plift_and, plift_or, plift_if.
      destruct F. exists x0. unfoldq. intuition.
    } {
      destruct fr1. 2: contradiction.
      destruct L. eauto.
    } {
      rewrite plift_and, plift_or, plift_if.
      destruct Q. exists x0. unfoldq. intuition.
    }

    intros. subst fr1. intros ? ?. eapply H9 in H10.
    destruct H10 as [ A | [B | C]]. {
      destruct fn1. 2: contradiction.
      simpl in A. eapply vars_locs_monotonic. 2: eauto.
      rewrite plift_and, plift_or. unfoldq. intuition.
    } {
      contradiction.
    } {
      eapply vars_locs_monotonic. 2: eauto.
      rewrite plift_and, plift_or. unfoldq. intuition.
    }
    
    assert (psub (plift (qand p (qor q1 (qif fn1 qf)))) (pdom E)).
    rewrite plift_and, plift_or, plift_if. unfoldq. intuition.
    destruct fn1; eapply H5; unfoldq. eapply H10. contradiction.
    
    intros ? ?. eapply H10. eapply H11. eauto. 
    
    destruct IHW1 as [? IHW1].
    exists S2, M2, vy. intuition.

    (* VAL_TYPE *)
    eapply valt_extend1; eauto.

    (* vy < vf \/ vx *)
    apply valt_wf in H8(*HVX*). apply valt_wf in H12(*HVY*).
    rename H15 into HVY.

    intros ? ?.
    destruct (HVY x) as [HY_q | HY_fr]. eauto.
    + (* q *) destruct HY_q as (? & (? & ?) & ?).
      bdestruct (x0 =? length E).
      * (* from arg *)
        subst x0. eapply var_locs_head in H17.
        right. right. left.
        destruct ar2. eauto. 
        destruct H16. { eapply H4 in H16. lia. }
        destruct H16. contradiction.
        destruct fn2. simpl in H16. rewrite plift_and in H16. destruct H16. eapply H5 in H18. lia.
        contradiction.
      * (* from func *)
        assert (x0 < length (vx::E)). destruct H17. rewrite indexr_extend1 in H17. eapply H17. simpl in H19.
        eapply var_locs_shrink in H17; try lia.
        destruct H15. 2: { contradiction. }
        destruct H16. 2: { 
          destruct ar2; destruct fn2; destruct H16; try contradiction. 
          right. left. simpl. exists x0; intuition.
          right. left. simpl. exists x0; intuition.
        }
                                
        left. split. 
        exists x0. intuition. 
        exists x0. intuition.
    + (* fr *)
      right. right. right. eapply HY_fr. 
        
    (* VAL_QUAL *)
    + eapply valq_abs.
Unshelve.
  apply (vbool true).
Qed.



Lemma sem_app: forall env f t T1 T2 p frf qf frx qx fn1 fr1 q1 fn2 ar2 fr2 q2,
    sem_type env f (TFun T1 fn1 fr1 q1 T2 fn2 ar2 fr2 q2) p frf (plift qf)->  
    sem_type env t T1 p frx (plift qx) ->
    (if fn1 then
       if fr1 then
         True
       else
         (* this case is tricky: *)
         (* qx < qf won't guarantee vx < vf!!! *)
         (* need f = tvar x0 and precisely qx = x0 *)
         (frx = false /\ (exists x0, f = tvar x0 /\ psub (plift qx) (pone x0)) \/
            frx = false /\ psub (plift qx) (plift q1))
     else
       if fr1 then
         psub (pand 
                 (plift (vars_trans_fix env qf))
                 (plift (vars_trans_fix env qx)))
           (plift q1)
       else
         frx = false /\ psub (plift qx) (plift q1)) ->

    psub (plift q2) p ->   (* this is necessary (so far!) *)
    sem_type env (tapp f t) T2 p
      (fn2 && frf || ar2 && frx || fr2)
      (por (pif fn2 (plift qf)) (por (pif ar2 (plift qx)) (plift q2))).
Proof.
  intros. intros S0 ? ? WFE ST.
  rename H into IHW1. rename H0 into IHW2. 
  destruct (IHW1 S0 M E WFE ST) as [S1 [M1 [vf [IW1 [SC1 [ST1 [HVF HQF]]]]]]]. auto. auto.
  assert (env_type M1 E env p) as WFE1. { eapply envt_store_extend; eauto. }
  destruct (IHW2 S1 M1 E WFE1 ST1) as [S2 [M2 [vx [IW2 [SC2 [ST2 [HVX HQX]]]]]]]. 

  assert (telescope env). eapply envt_telescope. eauto.

  (* vf is a function value: it can eval its body *)
  destruct vf; try solve [inversion HVF]. 

  apply valt_wf in HVF as WFQF. apply valt_wf in HVX as WFQX.

  destruct HVF; intuition.
  rename H8 into HVF.
  destruct (HVF S2 M2 vx) as [S3 [M3 [vy [IW3 [SC3 [ST3 HVY]]]]]]. eauto. eauto. eauto.

  (* SEPARATION / OVERLAP *)
  rename H1 into HSEP.
  intros ? ?.

  destruct fn1. { (* arg may overlap with function? *)
    destruct fr1. { (* arg may be fresh? *)
      (* fn, fr: anything goes *)
      edestruct val_locs_decide. left. eauto. right. left. eauto.
    } {
      (* fn, not fr *)
      destruct HSEP as [SEP | SEP]. { (* fn *)
        destruct SEP as (? & ? & ? & A). subst f frx.
        destruct IW1 as [? IW1]. assert (S x1 > x1) as P. lia. specialize (IW1 (S x1) P).
        simpl in IW1. inversion IW1. 
        destruct (HQX x) as [Hq | Hfr]. eauto. 2: { unfoldq. intuition. }
        left. simpl. destruct Hq as (? & (? & B) & ? & ? & ?).
        eapply A in B. unfoldq. congruence.
      } { (* q1 *)
        destruct SEP. subst frx.
        right. right. 
        eapply valq_sub with (q':=(pand p (plift q1))) (fr':=false) in HQX.
        destruct (HQX x) as [Hq | Hfr]. eauto. 2: contradiction.
        destruct Hq. exists x0. unfoldq. intuition.
        unfoldq. intuition. unfoldq. intuition. 
      }
    }
  } {
    destruct fr1. {
      (* not fn, fr *)
      edestruct val_locs_decide. {        
        right. right. 
        eapply overlapping. eapply WFE. eauto. eauto. eauto.
        intros ? [? ?]. eapply HSEP. split.
        rewrite plift_vt. eapply vt_mono. 2: eapply H8. unfoldq. intuition. eauto.
        rewrite plift_vt. eapply vt_mono. 2: eapply H9. unfoldq. intuition. eauto.
        unfoldq. intuition eauto.
      }{ 
        right. left. eauto.
      }
    } {
      (* not fn, not fr *)
      right. right. destruct HSEP as [? HSEP]. subst frx.
      eapply valq_sub with (q':=plift q1) (fr':=false) in HQX.
      destruct (HQX x) as [Hq | Hfr]. eauto. 2: contradiction.
      destruct Hq. exists x0. unfoldq. intuition.
      unfoldq. intuition. unfoldq. intuition. 
    }
  }

  (* EVALUATION *)
  exists S3, M3, vy.
  split. 2: split. 3: split. 4: split.
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

  (* STORE_EXTEND *)
  + eapply stchain_chain; eauto.
    eapply stchain_chain; eauto. 
    
  (* STORE_TYPE *)
  + eauto. 
    
  (* VAL_TYPE *)
  + eapply HVY.

  (* VAL_QUAL *)
  + destruct HVY as [HVY HQY].
    remember (vabs l q t0) as vf.
    intros ? ?. unfoldq.
    destruct (HQY  x) as [HY_q | [HY_f | [HY_x | HY_fr]]].
    repeat rewrite app_length. intuition.
    * (* q2, and part of function *)
      destruct HY_q as [[? ?] ?].
      left. exists x0. intuition.
    * (* part of function *)
      destruct fn2. 2: contradiction.
      destruct (HQF x) as [HF_q | HF_fr]. eauto.
      -- (* q *) destruct HF_q.
         left. exists x0. intuition.
      -- (* fr *) 
         destruct frf. 2: contradiction.
         right. destruct HF_fr; simpl. 
         split. eapply SC3. eapply SC2. eauto. eauto. 
    * (* part of arg *)
      destruct ar2. 2: contradiction.
      destruct (HQX x) as [HX_q | HX_fr]. eauto.
      -- (* q *) destruct HX_q.
         left. exists x0. intuition.
      -- (* fr *)
         destruct frx. 2: contradiction.
         right. destruct HX_fr. 
         destruct (fn2 && frf); simpl. 
         split. eapply SC3. eauto. 
         intros ?. eapply H9. eapply SC1. eauto. 
         split. eapply SC3. eauto.
         intros ?. eapply H9. eapply SC1. eauto. 
    * (* fresh *)
      destruct fr2. 2: contradiction.
      right. destruct HY_fr.
      repeat rewrite <-stplus_assoc in *. 
      destruct (fn2 && frf || ar2 && frx); simpl.
      split. eauto. intros ?. eapply H9. eapply SC2. eapply SC1. eauto.
      split. eauto. intros ?. eapply H9. eapply SC2. eapply SC1. eauto. 
Qed.


Lemma sem_sub: forall env y T p fr1 q1 fr2 q2,
    sem_type env y T p fr1 q1 ->
    psub q1 q2 ->
    psub q2 (pdom env)  ->
    sem_type env y T p (fr1 || fr2)  q2.
Proof.
  intros. intros ? ? ? WFE ST.
  destruct (H S M E WFE ST) as [S1 [M1 [vx [IW1 [SC1 [ST1 [HVX HQX]]]]]]].
  assert (psub q2 (pdom E)). {
    unfoldq. destruct WFE. rewrite H2. intuition. } 
  exists S1, M1. exists vx. split. 2: split. 3: split. 4: split.
  - eauto.
  - eauto.
  - eauto.
  - eauto.
  - unfold val_qual in HQX; intuition.
  eapply valq_sub. eauto. unfoldq. intuition. unfoldq. intuition. 
Qed.

Lemma sem_sub_var: forall env y T p fr1 q1 Tx qx x,
    sem_type env y T p fr1 q1 ->
    q1 x ->
    indexr x env = Some (Tx, false, qx) ->
    psub (plift qx) p -> 
    sem_type env y T p fr1 (por (pdiff q1 (pone x)) (plift qx)).
Proof.
  intros. rename x into z. intros ? ? ? WFE ST.
  destruct (H S M E WFE ST) as [S1 [M1 [vx [IW1 [SC1 [ST1 [HVX HQX]]]]]]].
  exists S1, M1. exists vx. intuition.
  eapply WFE in H1 as HZ.
  intros ? ?. destruct (HQX x). eauto.
  - destruct H4. bdestruct (x0 =? z).
    + subst. destruct HZ as [vz ?]. intuition.
      destruct H8 as (? & ? & ?). rewrite H7 in H8.
      inversion H8. subst x0. 
      left. eapply vars_locs_monotonic.
      2: { eapply H10; eauto. } 
      unfoldq. intuition.
    + left. exists x0. intuition. unfoldq. intuition.
  - right. intuition. 
Qed.



(* if well-typed, then result is an actual value (not stuck and not a timeout),
   for large enough n *)

(* TODO: automate plift_xxx using autorewrite *)

Theorem full_total_safety : forall e G T p fr q,
    has_type G e T p fr q ->
    sem_type G e T (plift p) fr (plift q).
Proof.
  intros ? ? ? ? ? ? W. 
  induction W.
  - rewrite plift_empty. eapply sem_true; eauto.
  - rewrite plift_empty. eapply sem_false; eauto.
  - rewrite plift_one. eapply sem_var; eauto.
  - eapply sem_ref; eauto. 
  - rewrite plift_empty. eapply sem_get; eauto.
  - rewrite plift_empty. eapply sem_put; eauto. 
  - repeat rewrite plift_or in *. repeat rewrite plift_if in *.
    eapply sem_app; eauto. 
  - repeat rewrite plift_or in *.
    repeat rewrite plift_and in *.
    repeat rewrite plift_if in *.
    repeat rewrite plift_one in *.
    eapply sem_abs; eauto.
  - eapply sem_sub; eauto.
  - rewrite plift_or, plift_diff, plift_one. 
    eapply sem_sub_var; eauto.
Qed.


(* note: not assuming anything other than has_type below *)
Corollary safety : forall e T fr q,
  has_type [] e T qempty fr q -> 
  exp_type [] st_zero [] e T (plift qempty) fr (plift q).
Proof. 
  intros. eapply full_total_safety in H; eauto.
  destruct (H [] st_zero []). 
  unfold env_type; intuition; simpl.
  unfoldq. intuition. inversion H0.
  unfoldq. unfoldq. intros.
  destruct H2 as [? [? [? [IX ?]]]]. intuition. inversion H5.
  unfold store_type; intuition. 
  destruct H0. eexists. eexists. eauto.
Qed.

End STLC.
