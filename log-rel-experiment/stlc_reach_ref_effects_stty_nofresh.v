(* Full safety for STLC *)

(* based on stlc_reach.v and stlc_ref.v *)

(*
  WRITE OPERATION, BUT NO DEALLOCATION

  simpler model, no kill effects
 *)

(* 

Simply-typed lambda calculus, combined proof of termination and type 
soundness (using logical relations).

This version adds immutable references. The proof relies on a
monotonically growing store. Since values in the store don't change,
a separate store typing is not necessary (adding an assignment
operator would require store typings). Store entries are also
restricted to base types (TRef TBool) only.

This version adds reachability types. The type qualifiers are
modeled as functions that check set membership. Restrictions:
no argument overlap, no dependent app.

This version adds simple effects. Every dereference incurs
a use effect. Right now, there is no semantic interpretation
of effects, and hence no meaningful static checking.

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

Definition id := nat.


Definition pl := nat -> Prop.

Definition pempty: pl := fun x => False.                            (* empty set *)

Definition pone (x:nat): pl := fun x' => x' = x.                    (* singleton set *)

Definition pand p1 p2 (x:nat) := p1 x /\ p2 x.                      (* intersection *)

Definition por p1 p2 (x:nat) := p1 x \/ p2 x.                       (* union *)

Definition pdom {X} (H: list X) := fun x' =>  x' < (length H).      (* domain of a list *)

Definition psub (p1 p2: pl): Prop := forall x:nat, p1 x -> p2 x.    (* subset inclusion *)

Definition plift (b: ql): pl := fun x => b x = true.                (* reflect nat->bool set *)


Inductive ty : Type :=
  | TBool  : ty
  | TRef   : ty -> ty
  | TFun   : ty -> (* qempty -> *) ty -> ql -> ql -> ty
.

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
| c_fun: forall m T1 T2 q2 e2,
    closed_ty m T1 ->
    closed_ty m T2 ->   (* not dependent *)
    closed_ql m q2 ->
    closed_ql m e2 ->   
    closed_ty m (TFun T1 (* qempty *) T2 q2 e2)
.


(* assume no overlap *)
Inductive has_type : tenv -> tm -> ty -> ql -> ql -> ql -> Prop :=
| t_true: forall env p,
    has_type env ttrue TBool p qempty qempty    (* nothing reachable from a primitive *)
| t_false: forall env p,
    has_type env tfalse TBool p qempty qempty
| t_var: forall x env T  p,
    indexr x env = Some T ->
    (plift p) x ->                         (* x in phi *)
    has_type env (tvar x) T p (qone x) qempty  (* x can reach only itself (no overlap) *)
| t_ref: forall t env p q e,
    has_type env t TBool p q e ->
    has_type env (tref t) (TRef TBool) p q e
| t_get: forall t env p q e,
    has_type env t (TRef TBool) p q e ->
    has_type env (tget t) TBool p qempty (qor e q)
| t_put: forall t1 t2 env p q1 e1 q2 e2,
    has_type env t1 (TRef TBool) p q1 e1 ->
    has_type env t2 TBool p q2 e2 ->
    has_type env (tput t1 t2) TBool p qempty (qor e1 (qor e2 q1))
| t_app: forall env f t T1 T2 p qf q1 q2 ef e1 e2,
    has_type env f (TFun T1 (* qempty  *) T2 q2 e2) p qf ef ->  
    has_type env t T1 p q1 e1 ->
    psub (pand (plift qf) (plift q1)) pempty ->          (* no overlapping *)
    psub (plift q2) (plift p) ->
    psub (plift e2) (plift p) ->
    has_type env (tapp f t) T2 p (qor q2 q1) (qor ef (qor e1 (qor q1 e2)))
| t_abs: forall env t T1 T2 p q2 qf e2,      (* assume argument is tracked *)
    has_type (T1::env) t T2 (qor (qand p qf) (qone (length env))) (qor q2 (qone (length env))) (qor e2 (qone (length env))) ->
    closed_ty (length env) T1 ->
    closed_ty (length env) T2 ->
    closed_ql (length env) q2 ->
    closed_ql (length env) qf ->
    closed_ql (length env) e2 ->
    has_type env (tabs (qand p qf) t) (TFun T1 T2 q2 e2) p qf qempty
| t_sub: forall env y T p q1 q2 e1 e2,
    has_type env y T p q1 e1 ->
    psub (plift q1) (plift q2) ->
    psub (plift q2) (pdom env)  ->
    psub (plift e1) (plift e2) ->
    psub (plift e2) (pdom env)  ->
    has_type env y T p q2 e2
.



(* NOTE: the definitions below could be defined as computable Fixpoint 
   but it would take some effort to convince Coq of termination. 
   Since we're recursing on vl, tm, and (list vl) simultaneously, 
   Coq would require these three types to be defined jointly to 
   recognize structural recursion across them. Other options would
   include custom size measures or a well-foundedness predicate.

   Since this is all rather cumbersome, and termination is evident
   as long as values can't be cyclic, we axiomatize the definition
   of rechability below, without proving termination. *)

Axiom val_locs : vl -> pl. (* set of store locs for given val *)

Definition var_locs E x l := exists vx, indexr x E = Some vx /\ val_locs vx l.

Definition vars_locs E q l := exists x, q x /\ var_locs E x l.


Axiom val_locs_bool: forall b,
    val_locs (vbool b) = pempty.

Axiom val_locs_ref: forall x,    
    val_locs (vref x) = pone x. (* no deep store indirection for now *)

Axiom val_locs_abs: forall H p t,
    val_locs (vabs H p t) = vars_locs H (plift p).



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


(* store typings *)

Definition stty := list (vl -> Prop).

Definition store_type (S: stor) (M: stty) :=
  length S = length M /\
    forall l vt,
      indexr l M = Some vt ->
      exists v,
        indexr l S = Some v /\
          vt v.


Definition store_effects (S S' : stor) e :=
   forall l,
     (pdom S) l ->
     (exists v1 v2,
      indexr l S = Some v1 /\
      indexr l S' = Some v2 /\ 
      (e l 
      \/
      v1 = v2
      ))
.


(* value interpretation of types *)

Fixpoint val_type (M:stty) (H:venv) v T : Prop :=
  match v, T with
  | vbool b, TBool =>
      True
  | vref l, TRef T => 
       T = TBool /\
      exists vt,
        indexr l M = Some vt /\
          (forall M' vx, vt vx <-> val_type (M'++M) H vx T)
  | vabs G py ty, TFun T1 (* qempty *) T2 q2 e2 =>
      closed_ty (length H) T1 /\
        closed_ty (length H) T2 /\
        (psub (plift q2) (pdom H)) /\
        (psub (plift e2) (pdom H)) /\
        (psub (val_locs v) (pdom M)) /\
        (forall S' M' vx,
            store_type S' (M'++M)
            ->
            val_type
              (M'++M)
              H
              vx
              T1
            ->
              psub (pand (val_locs v) (val_locs vx)) pempty
            ->
              exists S'' M'' vy,
                tevaln
                  S'
                  (vx::G)
                  ty
                  S''
                  vy
                /\
                store_effects S' S'' (por (val_locs vx)(vars_locs H (plift e2)))
                /\
                store_type S'' (M''++M'++M)
                /\
                  val_type
                    (M''++M'++M)
                    H
                    vy
                    T2
                /\
                  psub
                    (pand (pdom (M'++M)) (val_locs vy))
                    (por (pand (vars_locs H (plift q2)) (val_locs v)) (val_locs vx)))
  | _,_ =>
      False
  end.


Definition val_qual (M: stty) H v p (q: pl) :=
  psub (pand (pdom M) (val_locs v)) (vars_locs H (pand p q)).


Definition exp_type S M H t S' M' v T p q (e: pl) :=
  tevaln S H t S' v /\
    store_effects S S' (vars_locs H e) /\
    store_type S' (M'++M) /\
    val_type (M'++M) H v T /\
    val_qual M H v p q.

(* what to do to check e ? restrict store? *)


Definition env_type M H G p :=
  length H = length G /\
    psub p (pdom H) /\
    (forall x T,
        indexr x G = Some T ->
        p x ->
        exists v : vl,
          indexr x H = Some v /\
            val_type M H v T) /\
    (forall l x0 x1,
        p x0 ->
        var_locs H x0 l ->
        p x1 ->
        var_locs H x1 l ->
        x0 = x1).



#[global] Hint Constructors ty.
#[global] Hint Constructors tm.
#[global] Hint Constructors vl.


#[global] Hint Constructors has_type.

#[global] Hint Constructors option.
#[global] Hint Constructors list.


(* ---------- qualifier reflection & tactics  ---------- *)


Ltac unfoldq := unfold val_qual, psub, pdom, pand, por, pempty, pone, var_locs, vars_locs in *.
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





(* ---------- closedness lemmas  ---------- *)

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



(* ---------- val_type lemmas  ---------- *)

Lemma valt_wf: forall T M H v,
    val_type M H v T ->
    psub (val_locs v) (pdom M).
Proof. 
  intros T. induction T; intros; destruct v; simpl in *; intuition.
  + rewrite val_locs_bool. auto. unfoldq. intuition.
  + rewrite val_locs_ref. 
    destruct H2 as [vx [IX VALX]]. 
    eapply indexr_var_some' in IX.
    unfoldq. intuition.
Qed.

Lemma valt_closed: forall T M H v,
    val_type M H v T ->
    closed_ty (length H) T.
Proof. 
  intros T. induction T; intros; destruct v; simpl in *; intuition.
  + econstructor.
  + subst. econstructor; eauto. constructor.
  + econstructor; eauto. 
Qed.


Lemma valt_store_extend: forall T M' M H v,
    val_type M H v T ->
    val_type (M'++M) H v T.
Proof.  
  intros T. induction T; intros; destruct v; simpl in *; intuition.
  + destruct H2 as [vt [IX VT]].
    exists vt. split. 
    eapply indexr_extend in IX. eapply IX.
    intros. split.
    intros. eapply IHT. eapply VT. eauto.
    intros. eapply VT. rewrite app_assoc in H0. eauto. 
  + unfoldq. rewrite app_length. intros. assert (x < length M). eauto. lia.
  + destruct (H6 S' (M'0 ++ M') vx) as [S'' [M'' [vy  [IEY [EFF [STY [HVY HSEP]]]]]]]. 
    rewrite <- app_assoc. auto.
    rewrite <- app_assoc. auto.
    auto. 
    exists S'', M'', vy. intuition.
    repeat erewrite <- app_assoc in STY; eauto.
    repeat erewrite <- app_assoc in HVY; eauto.
    repeat erewrite <- app_assoc in HSEP; eauto.
Qed. 


Lemma valt_extend: forall T M H' H v,
    closed_ty (length H) T ->
    val_type M (H'++H) v T <-> val_type M H v T.
Proof.
  intros T. induction T; split; intros; destruct v; simpl in *; intuition.
  (* - inversion H0. auto.  *)
  - (* Ref shrink *)
    destruct H3 as [vx [IX HVX]].
    exists vx. intuition.
    eapply IHT; eauto. inversion H0. auto. eapply HVX. eauto.
    eapply HVX. eapply IHT; eauto. inversion H0. eauto. 
  (* - eapply closedty_extend; eauto. *)
  - (* Ref grow *)
    subst T.
    destruct H3 as [vx [IX HVX]].
    exists vx. intuition. 
    (*
    eapply IHT; eauto.
    eapply HVX. eauto.
    eapply HVX. eapply IHT. eauto. eauto. 
    *)
  - inversion H0. auto.
  - inversion H0. auto.
  - inversion H0. auto.
  - inversion H0. auto.
  - (* Abs shrink *)
    inversion H0. subst.
    rename q into q2. 
    destruct (H7 S' M' vx) as [S'' [M'' [vy [IEY [EFF [HST [HEY HVY]]]]]]].
      eauto. 
      eapply IHT1; eauto.
      eauto.
    exists S'', M'', vy. intuition.
    
    rewrite vars_locs_extend in EFF. auto.
    unfoldq; intuition.
    eapply IHT2; eauto.
    rewrite vars_locs_extend in HVY.
    eauto. eauto.
  - eapply closedty_extend; eauto.
  - eapply closedty_extend; eauto.
  - unfoldq. rewrite app_length. intuition. eapply H3 in H6. lia.
  - unfoldq. rewrite app_length. intuition. eapply H4 in H6. lia.
  - (* Abs grow *)
    inversion H0. subst.
    rename q into q2. 
    destruct (H7 S' M' vx) as [S'' [M'' [vy [HEY [HEFF [HSK [HVY HQY]]]]]]].
      eauto.
      eapply IHT1; eauto.
      eauto.
    exists S'', M'', vy. intuition.
    rewrite vars_locs_extend; eauto.
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

Lemma valq_bool: forall M H b p q,
    val_qual M H (vbool b) p q.
Proof.
  intros. unfoldq. rewrite val_locs_bool. intuition.
Qed.


Lemma valq_fresh: forall M M' H p q,
    val_qual M H (vref (length (M' ++ M))) p q.
Proof.
  intros. unfoldq.
  (* valq: index out of range*)
  rewrite app_length.
  rewrite val_locs_ref.
  intuition. unfoldq. lia.
Qed.


Lemma valq_abs: forall M H t p q,
    val_qual M H (vabs H (qand p q) t) (plift p) (plift q).
Proof.
  intros. unfoldq.
  rewrite val_locs_abs.
  rewrite plift_and.
  intuition. 
Qed.


Lemma valq_sub: forall M H v p q q',
    val_qual M H v p q ->
    psub q q' ->
    psub q' (pdom H) ->
    val_qual M H v p q'.
Proof.
  intros. unfoldq. intuition.
  destruct (H0 x). intuition.
  exists x0. intuition.
Qed.

Lemma valq_store_extend: forall H M M' i p q1,
  i < length M ->
  val_qual M H (vref i) p q1 ->
  val_qual (M'++M)  H (vref i) p q1.
Proof.
  intros. unfoldq; intuition.
  rewrite val_locs_ref in  H4. unfoldq.  subst. 
  eapply H1; intuition.  rewrite val_locs_ref.
  unfoldq; intuition.
Qed.

Lemma valq_store_extend1: forall H M M1 v p q,
  val_qual M H v p q ->
  (forall l, val_locs v l  -> l < length M) ->
  val_qual (M1++M) H v p q.
Proof.
  intros. unfoldq; intuition.
Qed.

(* ---------- environment lemmas  ---------- *)

Lemma wf_env_type: forall M H G p, 
  env_type M H G p -> 
  (length H = length G /\ pdom H = pdom G /\ psub p (pdom H)).
Proof.
    intros. unfold env_type in H0. intuition.
    unfold pdom. rewrite H1. auto.
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
    destruct (W x T); eauto. 
  - intros.
    destruct W.
    eauto.
Qed.

Lemma aux1: forall v H l,
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


Lemma envt_extend: forall M H G v T q p,
    env_type M H G p ->
    closed_ty (length H) T ->
    closed_ql (length H) q ->
    val_type M H v T ->
    (* separation *)
    (forall x l, val_locs v l -> p x -> var_locs H x l -> False) ->
    env_type M (v::H) (T::G) (por p (pone (length H))).
Proof. 
  intros. destruct H0 as [L [P W]]. 
  repeat split; auto.
  - simpl. eauto.
  - unfoldq. simpl. intuition.
  - intros. simpl in *. rewrite <-L in *.
    bdestruct (x =? (length H)); intuition; subst.
    + inversion H0. subst. exists v. intuition.
      eapply valt_extend1; eauto.
    + destruct (H7 _ _  H0); eauto.
      unfoldq. intuition.
      eexists. intuition. eauto.
      eapply valt_extend1; eauto.
      eapply valt_closed; eauto.      
  - intros.
    inversion H0; inversion H6.
    + eapply W; eauto.
      eapply var_locs_shrink. eauto. eapply P; eauto.
      eapply var_locs_shrink. eauto. eapply P; eauto.
    + destruct (H4 x0 l); eauto.
      assert (x1 = length H). unfoldq. intuition.
      subst x1. eapply aux1; eauto.
      eapply var_locs_shrink. eauto. eapply P; eauto.
    + destruct (H4 x1 l); eauto.
      assert (x0 = length H). unfoldq. intuition.
      subst x0. eapply aux1; eauto.
      eapply var_locs_shrink. eauto. eapply P; eauto.
    + unfoldq. lia.
Qed.


Lemma envt_store_extend: forall M M' H G p,
    env_type M H G p ->
    env_type (M'++M) H G p.
Proof.
  intros. destruct H0 as [L [P W]]. 
  repeat split; auto. intros.
  destruct W as [W W'].
  destruct (W _ _  H0 H1) as [vx [IH HVX]]; intuition.
  exists vx; intuition.
  eapply valt_store_extend in HVX; eauto.
  intros.
  destruct W as [W' W].
  destruct (W l x0 x1); intuition. 
Qed.


Lemma envt_extend_all: forall M M1 H G vx T1 p q1 qf,
    env_type M H G p ->
    val_type (M1 ++ M) H vx T1 ->
    psub (pand (vars_locs H (pand p qf)) (val_locs vx)) pempty ->
    closed_ty (length H) T1 ->
    closed_ql (length H) q1 ->
    env_type (M1 ++ M) (vx :: H) (T1 :: G) (por (pand p qf) (pone (length H))).
Proof.
  intros.

  eapply envt_extend.
  eapply envt_tighten.
  eapply envt_store_extend.
  eauto.
  unfoldq. intuition.
  eauto.
  eauto.
  eauto.

  (* now prove separation *) 
  intros.

  unfoldq. unfoldq.
  eapply H2. intuition.
  exists x. intuition.
  destruct H7.
  exists x0. intuition. eauto.
  destruct H7.
  eauto.
  
(*
  assert (qand (vars_locs H (qand p qf)) (val_locs vx) = qempty). {
    eapply qsub_empty. eauto. }
 
  assert (vars_locs H (qand p qf) l = true). {
    eapply vars_locs_def. exists x. eauto. }

  assert (qand (vars_locs H (qand p qf)) (val_locs vx) l = true). {
    unfold qand at 1. rewrite H5,H9. eauto. }

  assert (qempty l = true). { 
    rewrite H8 in H10. eauto. }

  inversion H11.
*)
Qed.



Lemma env_type_store_wf: forall M H G p q,
    env_type M H G p ->
    psub q p ->
    psub (vars_locs H q) (pdom M).
Proof.
  intros. destruct H0 as [L [P [W1 W2]]]; intuition.
  unfoldq. intuition.
  destruct H0 as [? [? ?]].
  assert (p x0). eapply H1. eauto.
  assert (x0 < length H). eauto.
  destruct H2 as [? [? ?]].

  assert (exists T, indexr x0 G = Some T) as TY. eapply indexr_var_some. rewrite <-L. eauto.
  destruct TY as [T ?].
  destruct (W1 x0 T) as [vx [? ?]]. eauto. eauto.
  rewrite H2 in H7. inversion H7. subst x1.

  eapply valt_wf in H8. eapply H8; eauto.
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

Lemma vars_locs_dist_and: forall M E env p q q'
    (WFE: env_type M E env p),
    psub q p ->
    psub q' p ->
    pand (vars_locs E q) (vars_locs E q') = vars_locs E (pand q q').
Proof.
  intros. eapply functional_extensionality.
  intros. eapply propositional_extensionality.
  destruct WFE as [L [P [W SEP]]].
  intuition.
  - destruct H1 as [[? [? ?]]  [? [? ?]]].
    assert (x0 = x1). eapply SEP; eauto. subst x1.
    exists x0. unfoldq. intuition.
  - destruct H1 as [? [? [? [? ?]]]].
    unfoldq. intuition.
    exists x0. intuition. exists x1. intuition.
    exists x0. intuition. exists x1. intuition.
Qed.


Lemma separation: forall M M' H G p vf vx qf q1
    (WFE: env_type M H G p)
    (HQF: val_qual M H vf p qf)
    (HQX: val_qual (M'++M) H vx p q1),
    psub (val_locs vf) (pdom (M'++M)) ->
    psub (pand qf q1) pempty ->
    psub (pand (val_locs vf) (val_locs vx)) pempty.
Proof. 
  intros. unfoldq. intuition.
  remember WFE as WFE1. clear HeqWFE1.
  destruct WFE as [? [? [? SEP]]].
  bdestruct (x <? length M).
  - destruct (HQF x). intuition.
    destruct (HQX x). rewrite app_length. intuition.
    assert (x0 = x1). eapply SEP; intuition; eauto.
    eapply H1. subst x0. intuition; eauto.
  - bdestruct (x <? length (M'++M)).
    + destruct (HQX x). intuition.
      (* fresh loc in vf, also occurs in vx --> can't happen *)
      assert (psub (vars_locs H (pone x0)) (pdom M)) as L. {
        eapply env_type_store_wf. eauto. unfoldq. intuition. subst x1. eauto.
      }
      assert (x < length M). {
        eapply L. unfoldq. exists x0. intuition.
      }
      lia.
    + (* fresh loc in vx, bigger than vf *)
      eapply H0 in H3. lia.
Qed.

(* ---------- store typing lemmas ---------- *)


Lemma storet_length: forall S M,
    store_type S M ->
    length S = length M.
Proof.
  intros. destruct H. eapply H.
Qed.

Lemma storet_extend: forall S M H T vx,
    store_type S M ->
    val_type M H vx T ->
    store_type (vx :: S) ((fun v => val_type M H v T) :: M).
Proof.
  intros.
  unfold store_type in *. intuition.
  simpl. eauto. 
  bdestruct (l =? length M).
  - subst l. simpl in *. 
    bdestruct (length M =? length S); intuition.
    bdestruct (length M =? length M); intuition.
    inversion H4. exists vx. intuition. inversion H0. subst vt. eauto. 
  - rewrite indexr_skip in H0; eauto.
    bdestruct (l =? length S). lia.
    rewrite indexr_skip; eauto. 
Qed.

Lemma storet_update: forall S M H i vx,
    store_type S M ->
    val_type M H (vref i) (TRef TBool) ->
    val_type M H vx TBool -> 
    store_type (update S i vx) M.
Proof.
  intros. destruct H0 as [L ST].
  split. 
  (* length *)
  rewrite <-update_length. eauto.
  (* lookup *) {
    intros.
    eapply ST in H0 as XX. destruct XX.
    bdestruct (i =? l). subst l. 
    + rewrite update_indexr_hit. exists vx. intuition.
      destruct H1 as [CL [vt1 [IX ?]]].
      rewrite IX in H0. inversion H0. subst vt1.
      (* update -- we rely on the fact that we have a primitive *)
      eapply H1. eapply H2. 
      destruct H3. rewrite indexr_extend in H3. eapply H3.
    + rewrite update_indexr_miss. eauto. eauto.
  }
  Unshelve.
  eapply [].
  eapply [].
Qed.

Lemma store_extend: forall S M M' S',
  store_type S M ->
  store_type S' (M'++ M) ->
  psub (pdom S) (pdom S').
Proof.
  intros. destruct H as [L IX].
  destruct H0 as [L' IX'].
  rewrite app_length in L'.
  unfoldq; intuition.
Qed.

(* store effects *)

Lemma no_effects: forall S pempty,
  store_effects S S pempty.
Proof.
  intros. unfold store_effects. intuition.
  assert (l < length S). unfoldq; intuition.
  apply indexr_var_some in H0. destruct H0.
  exists x, x. intuition.
Qed.
  
Lemma fresh_no_harm: forall S S' e vx,
  psub (pdom S) (pdom S') ->
  store_effects S S' e -> 
  store_effects S (vx ::S') e.
Proof.
  intros. unfold store_effects in *. intuition.
  
  assert ((indexr l (vx :: S')) = (indexr l S')). {
      assert (pdom S' l); intuition.
      rewrite indexr_skip. auto. unfoldq; intuition.
    }
  destruct (H0 l H1); rewrite H2; auto.
 
Qed.

Lemma effects_sub: forall S S' e e',
  psub e e' ->
  store_effects S S' e ->
  store_effects S S' e'.
Proof.
  intros. unfold store_effects in *.
  intros. destruct (H0 l H1) as [v1 [v2 [IX1 [IX2 ?]]]]; intuition.
  exists v1, v2; intuition. 
  exists v1, v2; intuition.
Qed.

Lemma write_effects: forall S M H (p:pl) i v q1,
  i < length S ->
  store_type S M ->
  val_qual M H (vref i) p q1 -> 
  store_effects S (update S i v) (vars_locs H q1).
Proof.
  intros. destruct H1 as [L VT].
  unfold store_effects. intros.
  assert (l < length M). rewrite <- L. unfoldq; intuition.
  apply indexr_var_some in H3 as H3'. destruct H3' as [vt ?].
  destruct (VT l vt H4) as [v' ?]; intuition.
  bdestruct (i =? l); intuition.
  subst i.
  exists v', v; intuition.
  eapply update_indexr_hit. auto.
  left. intuition. 
  unfoldq.
  rewrite val_locs_ref in H2.
  destruct (H2 l) as [x0 ?]; intuition.
  exists x0; intuition.
  exists v', v'; intuition.
  rewrite update_indexr_miss. auto. auto.
Qed.

Lemma effects_mask: forall i S S1 M M1 e v
  (ST: store_type S M)
  (ST1: store_type S1 (M1 ++ M))
  (EFF1: store_effects S S1 e),
  i >= length S ->
  i < length S1 ->
  store_effects S (update S1 i v) e.
Proof.
  intros.
  destruct ST as [L IVT]. destruct ST1 as [L1 IVT1].
  unfold store_effects in *. intros.
  assert (l < length S). unfoldq; intuition.
  rewrite update_indexr_miss; auto. unfoldq; intuition.
Qed.

Lemma effects_compose: forall S S1 S2 M M1 M2 e1 e2 H
  (ST: store_type S M)
  (EFF1: store_effects S S1 (vars_locs H e1))
  (ST1: store_type S1 (M1 ++ M))
  (EFF2: store_effects S1 S2 (vars_locs H e2))
  (ST2: store_type S2 (M2++ M1 ++ M)),
  store_effects S S2 (vars_locs H  (por e1 e2)).
Proof.
  intros. 
  destruct ST as [L IVT].
  destruct ST1 as [L1 IVT1].
  destruct ST2 as [L2 IVT2].
  unfold store_effects in *.
  intros.  
  assert (pdom S1 l). 
  unfoldq; intuition. rewrite L1. rewrite app_length. lia.
  assert (l < length S). unfoldq; intuition.
  assert (l < length S1). unfoldq; intuition.
  apply indexr_var_some in H1. destruct H1 as [x1 IX1].
  apply indexr_var_some in H2. destruct H2 as [x2 IX2].
    
  destruct (EFF1 l H0) as [v1 [v2 [IS [IS1 IP1]]]].
  destruct (EFF2 l H3) as [v3 [v4 [IS1' [IS2 IP2]]]].
  rewrite IS1' in IS1. inversion IS1. subst v3.
  destruct IP1; destruct IP2.
  + (* modified twice *)
    exists v1, v4; intuition.
    left. intros. unfoldq; intuition.
    destruct H2. exists x; intuition.
  + (* in eff1 *)
    subst v4. 
    exists v1, v2; intuition. left.
    intros. 
    unfoldq; intuition.
    destruct H1. exists x; intuition.
  + (* in eff2 *)
    subst v2. exists v1, v4; intuition. left.
    unfoldq; intuition.
    destruct H2. exists x; intuition. 
  + (* not changed *)
    subst v2. subst v4.
    exists v1, v1; intuition.
Qed.

Lemma effects_compose_update: forall S S1 M M1 H q e i v
  (ST: store_type S M)
  (EFF1: store_effects S S1 (vars_locs H e))
  (ST1: store_type S1 (M1 ++ M))
  (EFF2: store_effects S1 (update S1 i v) (vars_locs H q))
  (VALT1: val_type (M1++M) H (vref i)(TRef TBool))
  (VALT2: val_type (M1++M) H v TBool),
  i < length S ->
  store_effects S (update S1 i v) (vars_locs H (por e q)).
Proof.
  intros.
  assert (store_type (update S1 i v) (M1++M)).
  eapply storet_update; eauto.
  eapply effects_compose with (M2:= []); eauto.
Qed.

Lemma put_effects:  forall S S1 S2 M M1 M2 H e1 e2 q1 i p v
  (ST: store_type S M)
  (EFF1: store_effects S S1 (vars_locs H e1))
  (ST1: store_type S1 (M1 ++ M))
  (EFF2: store_effects S1 S2 (vars_locs H e2))
  (ST2: store_type S2 (M2 ++ M1 ++ M))
  (VALT1: val_type (M2 ++ M1 ++M) H (vref i) (TRef TBool))
  (VALT2: val_type (M2 ++ M1 ++M) H v TBool)
  (VALQ:  val_qual M H (vref i) p q1),
  store_effects S  (update S2 i v)  (vars_locs H (por e1 (por e2 q1))).
Proof.
  intros.
  remember ST as ST'. clear HeqST'.
  remember ST1 as ST1'. clear HeqST1'.
  remember ST2 as ST2'. clear HeqST2'.

  destruct ST as [L VT].
  destruct ST1 as [L1 VT1].
  destruct ST2 as [L2 VT2].

  assert (store_effects S S2 (vars_locs H (por e1 e2))) as A.
  eapply effects_compose; eauto.

  bdestruct (i <? length S).
  + eapply write_effects with (v := v) in  H0 as H1'; eauto.
    assert (store_effects S2 (update S2 i v) (vars_locs H q1)).
    eapply write_effects; eauto.
    unfoldq; intuition.
    repeat rewrite app_length in *. lia.
    eapply valq_store_extend; eauto. repeat rewrite app_length. lia. 
    eapply valq_store_extend; eauto. lia. 
     
    replace (por e1 (por e2 q1)) with (por (por e1 e2) q1).
    assert (store_type (update S2 i v) (M2++M1++M)).
    eapply storet_update; eauto. 

    eapply effects_compose_update in H1. 2: eapply ST'. eapply H1. auto.
    replace (length (M2++M1 ++M)) with (length ((M2++M1)++M)) in L2.
    replace (M2++M1 ++M) with ((M2++M1)++M) in VT2.
    unfold store_type. split.  eapply L2. eapply VT2.
    rewrite app_assoc. auto. rewrite app_assoc. auto.

    1,2: rewrite <- app_assoc; auto. auto.

    unfoldq; intuition. apply functional_extensionality. intros; intuition.
    eapply propositional_extensionality. intuition.
  + assert (i < length S2). simpl in VALT1. intuition.
    destruct H2 as [vt [IM ?]].
    apply indexr_var_some' in IM. rewrite L2. auto.

    assert (store_effects S (update S2 i v) (vars_locs H (por e1 e2))).
    eapply effects_mask in A; eauto.
    replace (length (M2++M1 ++M)) with (length ((M2++M1)++M)) in L2.
    replace (M2++M1 ++M) with ((M2++M1)++M) in VT2.
    unfold store_type. split.  eapply L2. eapply VT2.
    rewrite app_assoc. auto. rewrite app_assoc. auto.
    
    replace (por e1 (por e2 q1)) with (por (por e1 e2) q1).
    eapply effects_sub; eauto. 
    unfoldq; intuition.
    destruct H3. exists x0; intuition.

    unfoldq; intuition. apply functional_extensionality. intros; intuition.
    eapply propositional_extensionality. intuition.
Qed.

Lemma effects_app: forall S M S1 S2 S3 M1 M2 M3 H Hf v e p q1 ef e1 pv ey qf
  (ST: store_type S M)
  (ST1: store_type S1 (M1++M))
  (ST2: store_type S2 (M2++M1++M))
  (ST3: store_type S3 (M3++M2++M1++M))
  (EFF1: store_effects S S1 (vars_locs H ef))
  (EFF2: store_effects S1 S2 (vars_locs H e1)) 
  (HQX: val_qual (M1++M) H v p q1)
  (HQF: val_qual M H (vabs Hf pv ey) p qf)
  (EFF3:  store_effects S2 S3 (por (val_locs v)(vars_locs H e))),
  psub e p ->
  store_effects S S3 (vars_locs H (por ef (por e1 (por q1 e)))).
Proof. 
  intros. 
  remember ST as ST'. clear HeqST'.
  remember ST1 as ST1'. clear HeqST1'.
  remember ST2 as ST2'. clear HeqST2'.
  remember ST3 as ST3'. clear HeqST3'.
  
  destruct ST as [L VT].
  destruct ST1 as [L1 VT1].
  destruct ST2 as [L2 VT2].
  destruct ST3 as [L3 VT3].
  
  assert (store_effects S S2 (vars_locs H (por ef e1))).
  eapply effects_compose. eapply ST'. eapply EFF1.
  eapply ST1'. auto. eauto.
  
  unfold store_effects in *. intros.
  destruct (EFF1 l H2) as [v1 [v2 [IS [IS1 P]]]].
  assert (l < length S). unfoldq; intuition.
  assert (l < length S3). rewrite L3. repeat rewrite app_length. lia.
  apply indexr_var_some in H3. destruct H3 as [v' IS'].
  apply indexr_var_some in H4. destruct H4 as [v'' IS3].
  exists v', v''; intuition. left. 
  unfoldq. destruct H3. exists x; intuition.
  subst v2.
  
  assert (pdom S1 l). unfoldq; intuition. rewrite L1. rewrite app_length. lia.
  destruct (EFF2 l H3) as [v2 [v3 [IS1' [IS2 P]]]].
  rewrite  IS1' in IS1. inversion IS1. subst v2.
  unfoldq; intuition.
  destruct H4; intuition.
  left. exists x; intuition.
  subst v3.
  
  assert (pdom S2 l). unfoldq; intuition. rewrite L2. repeat rewrite app_length. lia.
  assert (l < length (M1++M)). unfoldq; intuition.
  destruct (EFF3 l H4) as [v2 [v3 [IS2' [IS3' P]]]].
  rewrite IS2' in IS2. inversion IS2.  subst v2.
  destruct P. destruct H6.
  destruct (HQX l); intuition.
  left. exists x; intuition.
  
  destruct H6. left.  exists x; intuition.

  subst v3. rewrite IS3' in IS3. inversion IS3.
  subst v''. rewrite IS' in IS. inversion IS. subst v'.
  intuition.
Qed.


(* ---------- main lemmas ---------- *)

Lemma sem_app1: forall S S' S'' M M' M'' H Hf G T1 T2 ey vx pv p q1 q2 qf e2
    (WFE: env_type M H G p)
    (ST: store_type S M)
    (ST1: store_type S' (M'++M))
    (HVF: val_type (M'++M) H (vabs Hf pv ey) (TFun T1 T2 q2 e2))
    (HQF: val_qual M H (vabs Hf pv ey) p qf)
    (HVX: val_type (M''++M'++M) H vx T1)
    (HQX: val_qual (M'++M) H vx p q1),
    psub (pand qf q1) pempty ->
    psub (plift q2) p  -> 
    psub (plift e2) p ->
    (* exists vy, exp_type H ey vy T2 p q2. *) (* not exactly this!! *)
    store_type S'' (M''++M'++M) ->
    exists S''' M''' vy,
      tevaln S'' (vx::Hf) ey S''' vy /\
        store_effects S'' S''' (por (val_locs vx ) (vars_locs H (plift e2))) /\ 
        store_type S''' (M'''++M''++M'++M) /\
        val_type (M'''++M''++M'++M) H vy T2 /\
        val_qual M H vy p (por (plift q2) q1).
Proof.
  
  intros. apply valt_wf in HVF as WFQF. apply valt_wf in HVX as WFQX.
  destruct HVF; intuition.  
  rename H10 into HVF.
  destruct (HVF S'' M'' vx) as [S''' [M''' [vy [IW3 [HEFF [HST [HVY HQY]]]]]]].
  eauto. eauto.


  (* TODO 1: ARG TYPE *)

    (* go from 
        T1 p q1 
     to
        T1 (qand qf p) (qand qf q1)
     to
        T1 (qand qf p) qempty
     to
        T1 (qand p (val_locs vf)) qempty
     to
        T1 (val_locs vf) qempty
  *)


  (* TODO 2: SEPARATION *)

  eapply separation; eauto.
  
  (* TODO 3: VAL_TYPE *)
  
  (* go from 
        T2 (qand p qf) (qand p (qand qf q2))
     to
        T2 p (qor q2 q1)
  *)

  exists S''', M''', vy. split.
  auto.
    
  
  (* effects *)
   split.
   auto.
  
  (* store typing *)
  split. auto.

  (* val_type *)
  split. auto.

  (* TODO 3: VAL_QUAL *)

  (*  
  HQX:  vx & p <= q1
  HQF:  vabs Hf ey & p <= qf
  HQY1: vy <= (vabs Hf ey) | vx
  HVY:  vy & p & qf <= q2

  vy & p = vy & p & qf | vy & p & ~qf
        <= q2 | (qf | q1) & ~qf
        <= q2 | q1
  *)


  remember (vabs Hf pv ey) as vf.
  unfold val_qual in *.
  
  unfoldq. intros. 
  destruct (HQY x). repeat rewrite app_length. intuition.
  + (* part of function *)
    destruct (HQF x). intuition.
    destruct H10. destruct H10.
    exists x1. intuition.
  + (* part of argument *)
    destruct (HQX x). repeat rewrite app_length. intuition. 
    exists x0. intuition.
Qed.

Lemma eff_abs: forall S S' vx H e2 M
  (ST: store_type S M)
  (EFF: store_effects S S' (vars_locs (vx::H)(por e2 (pone (length H))))),
  (psub e2 (pdom H)) ->
  store_effects S S' (por (val_locs vx) (vars_locs H e2)).
Proof.
  intros. unfold store_effects in EFF.
  unfold store_effects. intros.
  destruct (EFF l H1) as [v1 [v2 [IS1 [IS2 P]]]].
  exists v1, v2; intuition. left.
  unfoldq; intuition.
  destruct H2. intuition. right. 
  exists x; intuition. unfoldq. destruct H4; intuition.
  rewrite indexr_skip in H4. exists x0; intuition.
  eapply H0 in H2. lia.

  subst x. unfoldq. destruct H4. intuition.
  rewrite indexr_head in H3. inversion H3. subst x.
  intuition.
Qed.

Lemma sem_abs1: forall S M M1 H G T1 T2 t vx p q2 qf e2
    (WFE: env_type M H G (plift p))
    (HVX: val_type (M1 ++ M) H vx T1) (* arg from valt *)
    (SEP : psub (pand (val_locs (vabs H (qand p qf) t)) (val_locs vx)) pempty)
    (IHW : (* induction *)
        env_type (M1 ++ M) (vx :: H) (T1 :: G) (plift (qor (qand p qf) (qone (length H)))) ->
        exists (S'' : stor) (M'': stty) (vy : vl),
          exp_type S (M1 ++ M) (vx :: H) t S'' M'' vy T2 (plift (qor (qand p qf) (qone (length H))))
            (plift (qor q2 (qone (length H)))) (plift (qor e2 (qone (length H)))))
    (HCLT1: closed_ty (length H) T1)        
    (HCLT2: closed_ty (length H) T2)
    (HCLQ:  closed_ql (length H) (qand p qf))
    (HCLE: closed_ql (length H) e2)
    (STY:   store_type S (M1 ++M)),
  exists (S'': stor) (M'' : stty) (vy : vl),
    tevaln S (vx :: H) t S'' vy /\
      store_effects S S'' (por (val_locs vx) (vars_locs H (plift e2)))  /\
      store_type S'' (M'' ++ M1 ++ M) /\
      val_type (M'' ++ M1 ++ M) H vy T2 /\
      psub (pand (pdom (M1 ++ M)) (val_locs vy))
        (por (pand (vars_locs H (plift q2)) (val_locs (vabs H (qand p qf) t))) (val_locs vx)).
Proof.
  intros.
  destruct (IHW) as [S2 [M2 [vy IHW1]]]. {
    rewrite val_locs_abs, plift_and in SEP.
    rewrite plift_or, plift_and, plift_one.
    eapply envt_extend_all; eauto.
  }
  destruct IHW1 as [HE [HEFF [HST [HVY HQY]]]].
  exists S2, M2, vy. intuition.

  (* effects *)
  rewrite plift_or, plift_one in HEFF. 
  eapply eff_abs; eauto.
  

  (* TODO 2: VAL_TYPE *)

  (* go from
        T2 (qor (qand p qf) (qone (length H))) (qor q2 (qone (length H)))
     to
        T2 (qand p qf) (qand p (qand qf q2))
   *)
  eapply valt_extend1; eauto.

  (* TODO 3: VAL_QUAL *)
  
  (* vy < vf \/ vx *)

  rewrite val_locs_abs in *.
  apply valt_wf in HVX. apply valt_wf in HVY.
    
  unfoldq. intuition.
  destruct (HQY x). eauto.
  rewrite plift_or, plift_and, plift_one in H0.
  rewrite plift_or, plift_one in H0.
  unfoldq.
  destruct H0. destruct H0.
  bdestruct (x0 =? length H).
  - (* from arg *)
    right. destruct H3 as [? [? ?]]. subst x0. rewrite indexr_head in H3. inversion H3. eauto.
  - (* from func *)
    left. split.
    exists x0. intuition. destruct H3 as [? [? ?]]. rewrite indexr_skip in H3. exists x1. split; eauto. lia.
    exists x0. rewrite plift_and. split.
    destruct H0; try lia. eapply H0.
    destruct H3 as [? [? ?]]. rewrite indexr_skip in H3; eauto.
Qed.
  





(* if well-typed, then result is an actual value (not stuck and not a timeout),
   for large enough n *)

Theorem full_total_safety : forall t G T p q e,
    has_type G t T p q e ->
    forall M E, env_type M E G (plift p) ->
    forall S, store_type S M ->
    exists S' M' v, exp_type S M E t S' M' v T (plift p) (plift q) (plift e).
Proof.
  intros ? ? ? ? ? ? W. 
  induction W; intros ? ? WFE S ST; 
  apply wf_env_type in WFE as WFE'; intuition.
  
  - (* Case "True". *) exists S. exists []. exists (vbool true). split.
    exists 0. intros. destruct n. lia. intuition. simpl. intuition.
    eapply no_effects. eapply valq_bool.
    
  - (* Case "False". *) exists S. exists []. eexists. split.
    exists 0. intros. destruct n. lia. intuition. simpl. intuition. 
    eapply no_effects. eapply valq_bool.
    
  - (* Case "Var". *)
    destruct WFE as [? [? [WFE ?]]].
    destruct (WFE x T H) as [vx [HI ?]]. eauto.
    exists S. exists []. eexists. 
    split. exists 0. intros. destruct n. lia. simpl. rewrite HI. reflexivity.
    intuition. eapply no_effects.
    
    (* valq *)
    unfoldq. rewrite plift_one.
    unfoldq. intuition.
    exists x. intuition.
    exists vx. intuition.
    
  - (* Case "Ref". *)
    destruct (IHW M E WFE S) as [S1 [M1 [vx [IW1 [EFF1 [ST1 [HVX HQX]]]]]]]. eauto. 
    remember (fun v => val_type (M1++M) E v TBool) as vt.
    exists (vx::S1). exists (vt::M1). exists (vref (length (M1++M))). split. 2: split. 3: split.  4: split.
    + (* expression evaluates *)
      eapply storet_length in ST1.
      destruct IW1 as [n1 IW1].
      rename S into Sx.
      exists (S n1).
      intros. destruct n. lia.
      simpl. rewrite IW1. rewrite ST1. eauto. lia.
    + (* effects *)
       eapply fresh_no_harm; eauto. eapply store_extend; eauto.
    + (* store typing *)
      subst vt. eapply storet_extend; eauto.

    + (* result well typed *)
      constructor. constructor.
      exists vt; intuition.
      simpl. bdestruct (length (M1 ++ M) =? length (M1 ++ M)); intuition.
      subst vt. eauto. subst vt. eauto. 
    + eapply valq_fresh. 

  - (* Case "Get". *)
    destruct (IHW M E WFE S) as [S1 [M1 [vx [IW1 [EFF1 [ST1 [HVX HQX]]]]]]]. eauto. 
    destruct vx; try solve [inversion HVX]. simpl in HVX.
    destruct (HVX) as [CL [vt [MI HVX1]]].
    remember ST1 as ST1x. clear HeqST1x.
    destruct ST1 as [LST ST1].
    destruct (ST1 i vt) as [vy [SI VT]]. eauto. 
    exists S1. exists M1. exists vy. 
    split. 2: split. 3: split.
    + (* expression evaluates *)
      destruct IW1 as [n1 IW1].
      rename S into Sx.
      exists (S n1).
      intros. destruct n. lia.
      simpl. rewrite IW1. rewrite SI. eauto. lia.
    + (* effects *)
      assert (psub (vars_locs E (plift e)) (vars_locs E (plift (qor e q)))).
      rewrite plift_or.
      unfoldq; intuition. destruct H5. exists x0; intuition.

      eapply effects_sub; eauto.
    + (* store typing *)
      auto.
    + (* result well typed *)
      specialize (HVX1 M vy).
      destruct vy; intuition.
      eapply valq_bool. 

  - (* Case "Put" *)
    destruct (IHW1 M E WFE S) as [S1 [M1 [vr [IW1 [EFF1 [ST1 [HVR HQR]]]]]]]; eauto.
    assert (env_type (M1++M) E env (plift p)) as WFE1. eapply envt_store_extend. eauto. 
    destruct (IHW2 (M1++M) E WFE1 S1) as [S2 [M2 [vx [IW2 [EFF2 [ST2 [HVX HQX]]]]]]]; eauto.
    remember HVR as HVR'. clear HeqHVR'. 
    destruct vr; try solve [inversion HVR]. simpl in HVR.
    destruct (HVR) as [CL [vt [MI HVR1]]].
    remember ST2 as ST2x. clear HeqST2x.
    destruct ST2 as [LST ST2].
    destruct (ST2 i vt) as [vy [SI VT]]. rewrite indexr_extend in MI. eapply MI. 
    exists (update S2 i vx).
    exists (M2++M1).
    exists vy. split. 2: split. 
    + (* expression evaluates *)
      (* - initial fuel value *)
      destruct IW1 as [n1 IW1].
      destruct IW2 as [n2 IW2].
      rename S into Sx.
      exists (S (n1+n2)).
      (* - forall greater fuel *)
      intros. destruct n. lia.
      (* - result computes *)
      simpl. rewrite IW1. rewrite IW2. rewrite SI.
      repeat rewrite app_assoc. repeat rewrite app_nil_r. eauto.
      all: lia.
    + (* effects *) 
      repeat rewrite plift_or.
      eapply put_effects; eauto.
      constructor; auto. 
      rewrite indexr_skips.
      exists vt; intuition. apply indexr_var_some' in MI. auto.

    + assert (val_type (M2++M1++M) E vy TBool) as HVY.
      eapply HVR1 in VT; eauto. 

      assert (forall M, val_qual M E vy (plift p) (plift qempty)).
      simpl in HVY. destruct vy; try contradiction. intros. eapply valq_bool.

      split. 2: split. 
      rewrite <-app_assoc. eapply storet_update; eauto.
      eapply valt_store_extend. eauto. eauto.
      eauto. 
    
  - (* Case "App". *)
    (* induction on both subexpressions: obtain vf, vx *)
    destruct (IHW1 M E WFE S) as [S1 [M1 [vf [IW1 [EFF1 [ST1 [HVF HQF]]]]]]]. eauto.
    assert (env_type (M1++M) E env (plift p)) as WFE1. { eapply envt_store_extend. eauto. }
    destruct (IHW2 (M1++M) E WFE1 S1) as [S2 [M2 [vx [IW2 [EFF2 [ST2 [HVX HQX]]]]]]]. eauto.

    (* vf is a function value: it can eval its body *)
    destruct vf; try solve [inversion HVF].
           
    assert (exists S3 M3 vy,
               tevaln S2 (vx::l) t0 S3 vy /\
                 store_effects S2 S3 (por (val_locs vx ) (vars_locs E (plift e2))) /\  
                 store_type S3 (M3++M2++M1++M) /\
                 val_type (M3++M2++M1++M) E vy T2 /\
                 val_qual M E vy (plift p) (plift (qor q2 q1))
           ) as HVY. {
      apply valt_wf in HVX as HVX'.
      rewrite plift_or.
      eapply sem_app1; eauto. }
    destruct HVY as [S3 [M3 [vy [IW3 [EFF3 [ST3 [HVY HQY]]]]]]].

    (* result *)
    exists S3. exists (M3++M2++M1). exists vy. split. 2: split.
    + (* expression evaluates *)
      (* - initial fuel value *)
      destruct IW1 as [n1 IW1].
      destruct IW2 as [n2 IW2].
      destruct IW3 as [n3 IW3].
      rename S into Sx.
      exists (S (n1+n2+n3)).
      (* - forall greater fuel *)
      intros. destruct n. lia.
      (* - result computes *)
      simpl. rewrite IW1. rewrite IW2. rewrite IW3.
      repeat rewrite app_assoc. repeat rewrite app_nil_r. eauto.
      all: lia.
    + (* effects *) 
      repeat rewrite plift_or.
      eapply effects_app; eauto. 
      
    + (* result well typed *)
      (* eapply valt_qual_widen1. *)    
      repeat rewrite <-app_assoc. split. 2: split.
      eauto. eapply HVY. eauto.
      
  - (* Case "Abs". *)
    exists S. exists []. exists (vabs E (qand p qf) t).
    split. 2: split.
    + (* term evaluates *)
      exists 0. intros. destruct n. lia. simpl. eauto.
    + (* effects *)
      eapply no_effects; eauto. 
    + (* result well typed *)
      rewrite app_nil_l.
      split. simpl. eauto. 
      
      assert (pdom env = pdom E) as LE. { unfold pdom. rewrite H4. eauto. }
      
      rewrite LE in *. rewrite <-H4 in *. repeat split; auto.
      rewrite val_locs_abs. eapply env_type_store_wf. eauto.
      rewrite plift_and. unfoldq. intuition.
      
      intros S1 M1 vx ST1 HVX SEP.
      eapply sem_abs1; eauto.
      assert (psub (pand (plift p) (plift qf)) (pdom E)) as CL. {
        unfoldq. intuition. }
      rewrite <- plift_and in CL.
      eapply CL.
      eapply valq_abs; eauto.
      
  -  destruct (IHW M E WFE S) as [S1 [M1 [vx [IW1 [SW1 [HVX HQX]]]]]]. { eauto. }
     assert (psub (plift q2) (pdom E)). {
       unfoldq. rewrite H3. intuition. }
     exists S1. exists M1. exists vx.
     split. 2: split. 3: split.
     eauto. eauto.
     unfold val_qual in HQX; intuition.
     eapply effects_sub; eauto.
     unfoldq; intuition.
     destruct H9. exists x0; intuition.
     auto. intuition.
     eapply valq_sub; eauto.
Qed.


(* note: not assuming anything other than has_type below *)

Corollary safety : forall t T q e,
  has_type [] t T qempty q e -> 
  exists S M v, exp_type [] [] [] t S M v T (plift qempty) (plift q) (plift e).
Proof. 
  intros. eapply full_total_safety in H; eauto.
  unfold env_type; intuition; simpl. unfoldq. intuition.
  split; intuition. inversion H0.
Qed.

End STLC.
