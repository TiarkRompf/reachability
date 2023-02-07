(* Full safety for STLC *)

(* based on stlc.v *)

(* 

Simply-typed lambda calculus, combined proof of termination and type 
soundness (using logical relations).

There are no store references yet.

This version adds reachability types. The type qualifiers are
modeled as functions that check set membership. Restrictions:
no argument overlap, no dependent app.

*)


(*Require Export Arith.EqNat.
Require Export Arith.Le. *)
Require Import Coq.Lists.List.
Require Import Psatz.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import FunctionalExtensionality.
Import ListNotations.

Require Import tactics.
Require Import env.
Require Import qualifiers.

Module STLC.

Definition id := nat.

Inductive ty : Type :=
  | TBool  : ty
  | TFun   : ty -> (* qempty -> *) ty -> ql -> ty
.

Inductive tm : Type :=
  | ttrue : tm
  | tfalse : tm
  | tvar : id -> tm
  | tapp : tm -> tm -> tm (* f(x) *)
  | tabs : tm -> tm (* \f x.t *)
.


Inductive vl : Type :=
  | vbool : bool -> vl
  | vabs  : list vl -> tm -> vl    (* closure record  *)
.

Definition venv := list vl.
Definition tenv := list ty.


#[global] Hint Unfold venv.
#[global] Hint Unfold tenv.


Definition closed_ql m q := (forall x, q x = true -> x < m).

Inductive closed_ty: nat -> ty -> Prop :=
| c_bool: forall m, closed_ty m TBool
| c_fun: forall m T1 T2 q2,
    closed_ty m T1 ->
    closed_ty m T2 ->   (* not dependent *)
    closed_ql m q2 ->   
    closed_ty m (TFun T1 (* qempty *) T2 q2)
.


(* assume no overlap *)
Inductive has_type : tenv -> tm -> ty -> ql -> ql -> Prop :=
| t_true: forall env p,
    has_type env ttrue TBool p qempty   
| t_false: forall env p,
    has_type env tfalse TBool p qempty
| t_var: forall x env T1 p,
    indexr x env = Some T1 ->
    p x = true ->              
    has_type env (tvar x) T1 p (qone x)   
| t_app: forall env f t T1 T2 p qf q1 q2,
    has_type env f (TFun T1 (* qempty  *) T2 q2) p qf->  
    has_type env t T1 p q1 ->     
    qsub (qand qf q1) qempty ->           
    has_type env (tapp f t) T2 p (qor q2 q1)  
| t_abs: forall env t T1 T2 p q2 qf, 
    has_type (T1::env) t T2 (qor (qand p qf) (qone (length env))) (qor q2 (qone (length env))) ->  (*q2+\{x\} <: (p\cap qf) + x*)
    closed_ty (length env) T1 ->
    closed_ty (length env) T2 ->
    closed_ql (length env) q2 ->
    closed_ql (length env) qf ->
    has_type env (tabs t) (TFun T1 T2 q2) p qf 
| t_sub: forall env y T p q1 q2,
    has_type env y T p q1 ->
    qsub q1 q2 ->
    qsub q2 (qdom env)  ->
    has_type env y T p q2
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
            | None => None  (* timeout *)
            | Some None => Some None 
            | Some (Some (vbool _)) => Some None
            | Some (Some (vabs env2 ey)) => (* closure record *)
              match teval n env ex with
                | None => None
                | Some None => Some None
                | Some (Some vx) =>
                  teval n (vx::env2) ey
              end
          end
      end
  end.

(* value interpretation of terms *)
Definition tevaln env e v :=
  exists nm,
  forall n,
    n > nm ->
    teval n env e = Some (Some v).


(* value intrepretation of types *)
Fixpoint val_type (H:venv) v T (p:ql) (q:ql) : Prop :=
  match v, T with
  | vbool b, TBool =>
      qsub q (qdom H) /\   
      qsub p (qdom H)  
  | vabs G ty, TFun T1 (* qempty *) T2 q2 => 
      closed_ty (length H) T1 /\
      closed_ty (length H) T2 /\
      qsub q2 (qdom H) /\ 
      qsub q (qdom H) /\
      qsub p (qdom H) /\  
        (forall vx,
            val_type
              H
              vx
              T1
              (qand p q)
              qempty
            ->          
              exists vy,
                tevaln
                  (vx::G)
                  ty      
                  vy      
                /\
                  val_type
                    H
                    vy
                    T2
                    (qand p q)
                    (qand p (qand q q2)))
  | _,_ =>
      False
end.

Definition exp_type H t v T p q :=
  tevaln H t v /\
    val_type H v T p q
.

Definition env_type H G p :=
  length H = length G /\
    qsub p (qdom H) /\
    (forall x T,
        indexr x G = Some T ->
        p x = true ->
        exists v : vl,
          indexr x H = Some v /\
            val_type H v T p (qone x)) 
.

Hint Constructors ty.
Hint Constructors tm.
Hint Constructors vl.


Hint Constructors has_type.

Hint Constructors option.
Hint Constructors list.

Lemma wf_env_type: forall H G P, 
  env_type H G P -> 
  (length H = length G /\ qsub P (qdom H)).
Proof.
    intros. unfold env_type in H0. intuition.
Qed.


Lemma clq: forall {X} {env: list X} {p}, 
    closed_ql (length env) p <-> qsub p (qdom env).
Proof. 
    intros. split; unfold closed_ql in *; unfold qsub in *; intros; auto;
    specialize (H x); intuition; bdestruct (qdom env x); intuition. 
Qed.

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
Qed.

Lemma valt_closed: forall T H p q v,
    val_type H v T p q->
    closed_ty (length H) T.
Proof. 
  intros T. induction T; intros; destruct v; simpl in *; intuition.
  + econstructor.
  + econstructor; eauto. apply clq. auto. 
Qed.

Lemma valt_extend: forall T H' H v p q,
    qsub p (qdom H) ->
    qsub q (qdom H) ->
    closed_ty (length H) T ->
    val_type (H'++H) v T p q <-> val_type H v T p q.
Proof.
  intros T. induction T; split; intros; destruct v; simpl in *; intuition.
  (* - (* Bool shrink *)
    eapply qsub_trans. eauto. eapply qsub_cons. *)
  - inversion H2. auto.  
  - inversion H2. subst. auto.
  - inversion H2. subst. apply clq. auto.
  - (* Abs shrink *)
    rename q into q2. 
    destruct (H9 vx) as [vy [HEY HVY]]. {
      intuition.
      eapply IHT1; eauto.
      inversion H2. subst. auto.
    } 
    exists vy. intuition.
    eapply IHT2; eauto.
    inversion H2. subst. auto.
  - eapply closedty_extend; eauto.
  - eapply closedty_extend; eauto.
    (* eapply qsub_trans; eauto. *)
  (* - (* Bool grow *)
    eapply qsub_trans. eauto. eapply qsub_cons.  *)
  - (* Abs grow *)
    rename q into q2. 
    destruct (H9 vx) as [vy [HEY HVY]]. {
      intuition.
      eapply IHT1; eauto.
    }
    exists vy. split.
    eapply HEY.
    eapply IHT2; eauto.
Qed.


Lemma valt_qual_wf: forall T H v p q,
    val_type H v T p q ->
    qsub q (qdom H).
Proof.
  intros. destruct T; destruct v; simpl in *; intuition.
Qed.

Lemma valt_filter_wf: forall T H v p q,
    val_type H v T p q ->
    qsub p (qdom H).
Proof.
  intros. destruct T; destruct v; simpl in *; intuition.
Qed.



(* properties:
   - filter p can be tightened up to q, loosened up to dom H
   - qual q can be loosened up to filter p
*)



Lemma valt_flex: forall T1 H vx p q qf,
    qsub p (qdom H) ->
    qsub q (qdom H) ->
    qsub qf (qdom H) ->
    val_type H vx T1 p q <-> val_type H vx T1 (qand qf p) (qand qf q).
Proof.
  intros T. induction T; split; intros; destruct vx; simpl in *; intuition.
  - rename H8 into HVX.
    destruct (H9 vx) as [vy [HEY HVY]]. {
      intuition.
      assert (qempty = qand qf qempty) as R1. { eauto. }
      assert (qand (qand qf p) (qand qf q0) = qand qf (qand p q0)) as R2. {
        rewrite qand_associative.
        rewrite qand_commutative with (p := p).
        rewrite <- qand_associative with (p := qf).
        rewrite <- qand_associative with (p := qf).
        rewrite qand_idempetic. 
        rewrite qand_associative.
        rewrite qand_commutative with (p := q0). auto. 
      }
      rewrite R1, R2 in HVX. 
      eapply IHT1 in HVX; eauto. 
    }
    exists vy. intuition.
    assert (qempty = qand qf qempty) as R1. { eauto. }
    assert (qand (qand qf p) (qand qf q0) = qand qf (qand p q0)) as R2. {
      rewrite qand_associative.
      rewrite qand_commutative with (p := p).
      rewrite <- qand_associative with (p := qf).
      rewrite <- qand_associative with (p := qf).
      rewrite qand_idempetic. 
      rewrite qand_associative.
      rewrite qand_commutative with (p := q0). auto.  
    }
    assert (qand (qand qf p) (qand (qand qf q0) q) = qand qf (qand p (qand q0 q))) as R3. {
      rewrite qand_associative.
      rewrite qand_commutative with (p := p).
      rewrite <- qand_associative with (p := qf).
      rewrite <- qand_associative with (p := qf).
      rewrite <- qand_associative with (p := qf).
      rewrite qand_idempetic. 
      rewrite qand_associative with (s := q).
      rewrite qand_associative with (s := p).
      rewrite qand_commutative with (p := p). auto.
    }
    rewrite R2, R3.
    destruct (IHT2 H vy (qand p q0) (qand p (qand q0 q)) qf); eauto.
  - rename H8 into HVX.
    destruct (H9 vx) as [vy [HEY HVY]]. {
      intuition.
      assert (qempty = qand qf qempty) as R1. { eauto. }
      assert (qand (qand qf p) (qand qf q0) = qand qf (qand p q0)) as R2. {
        rewrite qand_associative.
        rewrite qand_commutative with (p := p).
        rewrite <- qand_associative with (p := qf).
        rewrite <- qand_associative with (p := qf).
        rewrite qand_idempetic. 
        rewrite qand_associative.
        rewrite qand_commutative with (p := q0). auto.
      }
      rewrite R1, R2. 
      eapply IHT1 in HVX; eauto.
    }
    exists vy. intuition.
    assert (qand (qand qf p) (qand qf q0) = qand qf (qand p q0)) as R2. { 
      rewrite qand_associative.
      rewrite qand_commutative with (p := p).
      rewrite <- qand_associative with (p := qf).
      rewrite <- qand_associative with (p := qf).
      rewrite qand_idempetic. 
      rewrite qand_associative.
      rewrite qand_commutative with (p := q0). auto.
    }
    assert (qand (qand qf p) (qand (qand qf q0) q) = qand qf (qand p (qand q0 q))) as R3. { 
      rewrite qand_associative.
      rewrite qand_commutative with (p := p).
      rewrite <- qand_associative with (p := qf).
      rewrite <- qand_associative with (p := qf).
      rewrite <- qand_associative with (p := qf).
      rewrite qand_idempetic. 
      rewrite qand_associative with (s := q).
      rewrite qand_associative with (s := p).
      rewrite qand_commutative with (p := p). auto.
    }
    rewrite R2, R3 in HVY.
    eapply IHT2; try eapply HVY; eauto.
Qed.




Lemma valt_tighten: forall T1 H vx p q qf,
    val_type H vx T1 p q ->
    qsub qf (qdom H) -> 
    val_type H vx T1 (qand qf p) (qand qf q).
Proof.
  intros. eapply valt_flex in H0; eauto. eapply valt_filter_wf; eauto. eapply valt_qual_wf; eauto.
Qed.

Lemma valt_loosen: forall T1 H vx p q qf,
    val_type H vx T1 (qand qf p) (qand qf q) ->
    qsub p (qdom H) ->
    qsub q (qdom H) ->
    qsub qf (qdom H) ->
    val_type H vx T1 p q.
Proof.
  intros. eapply valt_flex; eauto. 
Qed.


Lemma valt_filter_flex: forall T H v p q p',
    qsub q p -> 
    qsub p p' ->
    qsub p' (qdom H) ->
    val_type H v T p q <-> val_type H v T p' q.
Proof.
  intros T. induction T; split; intros; destruct v; simpl in *; intuition.
  - eapply qsub_trans; eauto.
  - assert (qsub q0 p'). { eapply qsub_trans. eapply H0. eauto. }
    assert (qand p q0 = q0) as R1. { eauto. }
    assert (qand p' q0 = q0) as R2. { eauto. }
    assert (qand p (qand q0 q) = qand q0 q) as R3. { eauto. }
    assert (qand p' (qand q0 q) = qand q0 q) as R4. { eauto. }
    rewrite R1, R2, R3, R4 in *.
    eauto.
  - eapply qsub_trans; eauto.
  - assert (qsub q0 p'). { eapply qsub_trans. eapply H0. eauto. }
    assert (qand p q0 = q0) as R1. { eauto. }
    assert (qand p' q0 = q0) as R2. { eauto. }
    assert (qand p (qand q0 q) = qand q0 q) as R3. { eauto. }
    assert (qand p' (qand q0 q) = qand q0 q) as R4. { eauto. }
    rewrite R1, R2, R3, R4 in *.
    eauto.
Qed.

Lemma valt_filter_tighten: forall T H v p q p',
    val_type H v T p q ->
    qsub p' p ->
    qsub q p' ->
    val_type H v T p' q.
Proof.
  intros. eapply valt_filter_flex; eauto. eapply valt_filter_wf; eauto.
Qed.

Lemma valt_filter_loosen: forall T H v p q p',
    val_type H v T p q ->
    qsub q p ->
    qsub p p' ->
    qsub p' (qdom H) ->
    val_type H v T p' q.
Proof.
  intros. 
  destruct (valt_filter_flex T H v p q p'); eauto.
Qed.

Lemma valt_sub: forall T H v p q q',
    val_type H v T p q ->
    qsub q q' ->
    qsub q' (qdom H) -> 
    val_type H v T p q'.
Proof.
  intros T. induction T; destruct v; simpl in *; eauto; intuition.
  - destruct (H8 vx) as [vy [HEY HVY]]. {
      intuition.
      eapply valt_filter_tighten. eauto. eauto. eapply qsub_empty_l.
    }
    exists vy. intuition.

    eapply IHT2. eapply valt_filter_loosen; eauto.
    eapply qsub_sub_and_r. eapply qsub_sub_and. eauto.
    eapply qsub_trans; eauto. 
Qed.

Lemma valt_extend1: forall T H v vx p q,
    val_type H v T p q ->
    val_type (vx::H) v T (qor p (qone (length H))) q. 
Proof.
  intros.
  eapply valt_qual_wf in H0 as W1.
  eapply valt_filter_wf in H0 as W2.
  eapply valt_closed in H0 as W3.
  replace (vx :: H) with ([vx] ++ H); eauto.
  eapply valt_extend in H0; eauto.
  eapply valt_loosen with (qf := qdom H); eauto.
  + assert (qand (qdom H) (qor p (qone (length H))) = p) as R1. { 
      rewrite qand_commutative.
      rewrite qand_or_distribute2. 
      assert (qand p (qdom H) = p) as R3. { auto. }
      assert ((qand (qone (length H))(qdom H)) = qempty) as R4. { 
        rewrite qand_qone_empty. auto. 
        bdestruct ((qdom H)(length H)); intuition. lia.
      }
      rewrite R3. rewrite R4. rewrite qor_empty_id_r. auto.
    }
    assert (qand (qdom H) q = q) as R2. { auto. }
    rewrite R1, R2. eauto.
  + simpl. apply qsub_sub_or_l; intuition. apply qsub_one_dom. simpl. lia.
Qed. 

Lemma valt_shrink1: forall T H v vx p q,
    val_type (vx::H) v T (qor p (qone (length H))) (qor q (qone (length H))) ->
    closed_ty (length H) T ->
    qsub q (qdom H) ->
    qsub p (qdom H) ->
    val_type H v T p q.
Proof.
  intros.
  eapply valt_tighten with (qf := qdom H) in H0; eauto.
  assert (qand (qdom H) (qor p (qone (length H))) = p) as R1. {
    rewrite qand_commutative. rewrite qand_or_distribute2.  
    rewrite qand_sub_r; auto. 
      assert ((qand (qone (length H))(qdom H)) = qempty) as R3. { 
        rewrite qand_qone_empty. auto. 
        bdestruct ((qdom H)(length H)); intuition. 
      }
     rewrite R3. rewrite qor_empty_id_r. auto.
  }
  assert (qand (qdom H) (qor q (qone (length H))) = q) as R2. { 
    rewrite qand_commutative. rewrite qand_or_distribute2.  
    rewrite qand_sub_r; auto. 
      assert ((qand (qone (length H))(qdom H)) = qempty) as R3. { 
        rewrite qand_qone_empty. auto. 
        bdestruct ((qdom H)(length H)); intuition. 
      }
     rewrite R3. rewrite qor_empty_id_r. auto. 
  }
  rewrite R1, R2 in H0. 
  replace (vx :: H) with ([vx] ++ H) in H0; eauto.
  eapply valt_extend; eauto.
Qed.


Lemma valt_add_to_env: forall T H v p,
    val_type H v T p qempty ->
    closed_ty (length H) T ->
    val_type (v::H) v T (qor p (qone (length H))) (qone (length H)).
Proof.
  intros. eapply valt_sub. eapply valt_extend1; eauto.
  eauto. eauto. apply qsub_one_dom. simpl. lia.
Qed.

Lemma valt_app_arg: forall T1 H vx p q1 qf,
    val_type H vx T1 p q1 ->
    qsub qf (qdom H) -> 
    val_type H vx T1 (qand p qf) (qand p (qand qf q1)).
Proof.
  intros.
  eapply valt_filter_wf in H0 as W1.
  eapply valt_tighten with (qf := qf) in H0; eauto.
  eapply valt_tighten with (qf := p) in H0; eauto.
  replace (qand p (qand qf p)) with (qand p qf) in H0. eauto.
  rewrite qand_commutative with (p := qf).
  rewrite <- qand_associative. rewrite qand_idempetic. auto.
Qed.


Lemma valt_app_res: forall T2 H vy p q2 qf q1,
    val_type H vy T2 (qand p qf) (qand p (qand qf q2)) ->
    qsub (qand qf q1) qempty ->
    qsub qf (qdom H) ->
    qsub q1 (qdom H) ->
    qsub q2 (qdom H) ->
    qsub p (qdom H) ->
    val_type H vy T2 p (qor q2 q1).
Proof.
  intros.
  replace (qand p qf) with (qand qf p) in H0. 2: rewrite qand_commutative; auto. 
  replace (qand p (qand qf q2)) with (qand qf (qand p q2)) in H0. 
  assert (val_type H vy T2 p q2). {
    eapply valt_sub. eapply valt_loosen. eauto.
    eauto. eauto. eauto. eauto. eauto.
  }
  eapply valt_sub. eauto. eauto. eauto.
  rewrite <- qand_associative. rewrite qand_commutative with (p := qf).
  rewrite qand_associative. auto.
Qed.
  

Lemma envt_tighten: forall H G p p',
    env_type H G p ->
    qsub p' p ->
    env_type H G p'.
Proof.
  intros. destruct H0 as [L [P W]].
  repeat split; auto.
  - eapply qsub_trans; eauto.
  - intros.
    destruct (W x T); eauto. 
    exists x0. intuition.
    eapply valt_filter_tighten; eauto.
    eapply qsub_one. auto. 
Qed.

Lemma envt_extend: forall H G v T p,
    env_type H G p ->
    val_type H v T p qempty ->
    env_type (v::H) (T::G) (qor p (qone (length H))).
Proof.
  intros. apply valt_closed in H1 as W0. 
  destruct H0 as [L [P W]]. 
  repeat split; auto.
  - simpl. eauto.
  - apply qsub_sub_or_l; intuition. apply qsub_one_dom; intuition.
  - intros. simpl in *. rewrite <-L in *.
    bdestruct (x =? (length H)); intuition; subst.
    + inversion H0. subst. exists v. repeat split. 
      eapply valt_add_to_env; eauto.
    + assert (p x = true). { 
        bdestruct (qor p (qone (length H)) x); intuition.
        bdestruct (qone (length H) x). subst.  intuition. 
        discriminate.
      }
      destruct (W _ _ H0); eauto. 
      eexists. intuition. eauto.
      eapply valt_extend1. auto.
Qed.


(* if well-typed, then result is an actual value (not stuck and not a timeout),
   for large enough n *)

Theorem full_total_safety : forall e G T p q,
  has_type G e T p q -> forall E, env_type E G p ->
  exists v, exp_type E e v T p q.

Proof.
  intros ? ? ? ? ? W. 
  induction W; intros ? WFE; 
  apply wf_env_type in WFE as WFE'; intuition.  
  
  - (* Case "True". *) eexists. split. 
    exists 0. intros. destruct n. lia. intuition. simpl. intuition. 
  - (* Case "False". *) eexists. split.
    exists 0. intros. destruct n. lia. intuition. simpl. intuition.

  - (* Case "Var". *)
    destruct WFE as [? [? WFE]].
    destruct (WFE x T1 H) as [vx [HI ?]]. eauto.
    eexists. 
    split. exists 0. intros. destruct n. lia. simpl. rewrite HI. reflexivity.
    eauto. 
   
  - (* Case "App". *)
    (* induction on both subexpressions: obtain vf, vx *)
    destruct (IHW1 E WFE)  as [vf [IW1 HVF]].
    destruct (IHW2 E WFE) as [vx [IW2 HVX ]].

    (* vf is a function value: it can eval its body *)
    destruct vf; try solve [inversion HVF]. simpl in HVF.
    destruct HVF as [HCL1[HCL2[HS2F [HSFP [HSPE HVF]]]]].
    destruct (HVF vx) as [vy [IW3 HVY]]. 

    (* argument *)  
    assert (qand p (qand qf q1) = qempty) as R1. {
      eapply qsub_empty with (q := (qand qf q1)) in H. rewrite H. auto.
    } 
    rewrite <-R1.
    
    eapply valt_app_arg. eapply HVX. eauto. 
    
    (* result *)
    exists vy. split.
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
    + (* result well typed *)
      (* eapply valt_qual_widen1. *)    
      eapply valt_app_res. eapply HVY. eauto.
      eauto. eapply valt_qual_wf. eauto.
      auto. 
      eauto. 

  - (* Case "Abs". *)
    exists (vabs E t).
    split.
    + (* term evaluates *)
      exists 0. intros. destruct n. lia. simpl. eauto.
    + (* result well typed *)
      repeat split. 
      1,2: rewrite H3; auto.
      1,2: apply clq; rewrite H3; auto.
      eapply qsub_trans; eauto.
      intros vx HVX.
      destruct (IHW (vx:: E)) as [vy IHW1]. {
        rewrite <-H3.
        eapply envt_extend; auto.
        eapply envt_tighten; eauto.
      }
      rewrite <-H3 in IHW1.
      destruct IHW1 as [? IHW1].
      exists vy; intuition.
      eapply valt_shrink1 in IHW1; eauto.
      eapply valt_tighten with (qf := qf) in IHW1.
      eapply valt_tighten with (qf := p) in IHW1.
      replace (qand p qf) with (qand p (qand qf (qand p qf))). 
      eapply IHW1.
      
      rewrite qand_commutative with (p := qf) at 1.
      rewrite qand_associative with (s := qf).
      rewrite qand_idempetic.
      rewrite <- qand_associative.
      rewrite qand_idempetic. auto.
      eauto.
      apply clq. rewrite H3. auto.
      rewrite H3. eauto.
      apply clq. rewrite H3. auto.
      
  -  destruct (IHW E) as [vx [IW1 HVX]]. { eauto. }
     exists vx. split. eauto. eapply valt_sub; eauto.
     unfold qdom. rewrite H1.
     eapply qsub_trans; eauto.
Qed.


(* note: not assuming anything other than has_type below *)

Corollary safety : forall e T q,
  has_type [] e T qempty q -> 
  exists v, exp_type [] e v T qempty q.
Proof. 
  intros. eapply full_total_safety in H; eauto.
  unfold env_type; intuition; simpl.
Qed.

End STLC.
