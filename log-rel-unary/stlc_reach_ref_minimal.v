(* Full safety for STLC *)

(* based on stlc_reach.v and stlc_ref.v *)

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
no result qualifier, no argument overlap, no dependent app.

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
  | TFun   : ty -> (* qempty -> *) ty -> (* qempty -> *) ty
.

Inductive tm : Type :=
  | ttrue : tm
  | tfalse : tm
  | tvar : id -> tm
  | tref : tm -> tm
  | tget : tm -> tm
(*| tput : tm -> tm -> tm  *)
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
| c_fun: forall m T1 T2,
    closed_ty m T1 ->
    closed_ty m T2 ->   (* not dependent *)
    closed_ty m (TFun T1 T2)
.


(* assume no overlap *)
Inductive has_type : tenv -> tm -> ty -> ql -> ql -> Prop :=
| t_true: forall env p,
    has_type env ttrue TBool p qempty     (* nothing reachable from a primitive *)
| t_false: forall env p,
    has_type env tfalse TBool p qempty
| t_var: forall x env T  p,
    indexr x env = Some T ->
    (plift p) x ->                        (* x in phi *)
    has_type env (tvar x) T p (qone x)    (* x can reach only itself (no overlap) *)
| t_ref: forall t env p q,
    has_type env t TBool p q ->
    has_type env (tref t) (TRef TBool) p q
| t_get: forall t env p q,
    has_type env t (TRef TBool) p q ->
    has_type env (tget t) TBool p qempty 
| t_app: forall env f t T1 T2 p qf q1,
    has_type env f (TFun T1 T2) p qf->  
    has_type env t T1 p q1 ->
    psub (pand (plift qf) (plift q1)) pempty -> (* no overlapping *)
    has_type env (tapp f t) T2 p (qor qf q1)
| t_abs: forall env t T1 T2 p q2 qf,
    has_type (T1::env) t T2 (qor (qand p qf) (qone (length env))) (qor q2 (qone (length env))) ->
    closed_ty (length env) T1 ->
    closed_ty (length env) T2 ->
    closed_ql (length env) q2 ->
    closed_ql (length env) qf ->
    has_type env (tabs (qand p qf) t) (TFun T1 T2) p qf
| t_sub: forall env y T p q1 q2,
    has_type env y T p q1 ->
    psub (plift q1) (plift q2) ->
    psub (plift q2) (pdom env)  ->
    has_type env y T p q2
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


(* value interpretation of types *)

Fixpoint val_type (M:stor) (H:venv) v T : Prop :=
  match v, T with
  | vbool b, TBool =>
      True
  | vref l, TRef T => (* restrict to TRef TBool ? *)
      exists vx,
      indexr l M = Some vx /\
        val_type M H vx T
  | vabs G py ty, TFun T1 (* qempty *) T2 =>
      closed_ty (length H) T1 /\
        closed_ty (length H) T2 /\
        (psub (val_locs v) (pdom M)) /\
        (forall M' vx,
            val_type
              (M'++M)
              H
              vx
              T1
            ->
              psub (pand (val_locs v) (val_locs vx)) pempty
            ->
              exists M'' vy,
                tevaln
                  (M'++M)
                  (vx::G)
                  ty
                  (M''++M'++M)
                  vy
                /\
                  val_type
                    (M''++M'++M)
                    H
                    vy
                    T2
                /\
                  psub
                    (pand (pdom (M'++M)) (val_locs vy))
                    (por (val_locs v) (val_locs vx)))
  | _,_ =>
      False
  end.


Definition val_qual (M: stor) H v p (q: pl) :=
  psub (pand (pdom M) (val_locs v)) (vars_locs H (pand p q)).


Definition exp_type M H t M' v T p q :=
  tevaln M H t (M'++M) v /\
    val_type (M'++M) H v T /\
    val_qual M H v p q.


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
    destruct H0 as [vx [IX VALX]]. 
    eapply indexr_var_some' in IX.
    unfoldq. intuition.
Qed.

Lemma valt_closed: forall T M H v,
    val_type M H v T ->
    closed_ty (length H) T.
Proof. 
  intros T. induction T; intros; destruct v; simpl in *; intuition.
  + econstructor.
  + destruct H0 as [? [? ?]]. econstructor. eapply IHT. eapply H1.
  + econstructor; eauto. 
Qed.


Lemma valt_store_extend: forall T M' M H v,
    val_type M H v T ->
    val_type (M'++M) H v T.
Proof.  
  intros T. induction T; intros; destruct v; simpl in *; intuition.
  + destruct H0 as [vx [IX VX]].
    exists vx. intuition. eapply indexr_extend in IX; intuition.
    eapply H0.
  + unfoldq. rewrite app_length. intros. assert (x < length M). eauto. lia.
  + destruct (H4 (M'0 ++ M') vx) as [M'' [vy  [IEY [HVY HSEP]]]]. 
    rewrite <- app_assoc. auto.
    auto.
    exists M''. exists vy. intuition.
    repeat erewrite <- app_assoc in IEY; eauto.
    repeat erewrite <- app_assoc in HVY; eauto.
    repeat erewrite <- app_assoc in HSEP; eauto.
Qed. 


Lemma valt_extend: forall T M H' H v,
    closed_ty (length H) T ->
    val_type M (H'++H) v T <-> val_type M H v T.
Proof.
  intros T. induction T; split; intros; destruct v; simpl in *; intuition.
  - (* Ref shrink *)
    destruct H1 as [vx [IX HVX]].
    exists vx. intuition.
    eapply IHT; eauto. inversion H0. auto. 
  - (* Ref grow *)
     destruct H1 as [vx [IX HVX]].
     exists vx. intuition.
    eapply IHT; eauto. inversion H0. auto.
  - inversion H0. auto.
  - inversion H0. auto.
  - (* Abs shrink *)
    inversion H0. subst.
    rename q into q2. 
    destruct (H5 M' vx) as [M'' [vy [HEY HVY]]].
      eapply IHT1; eauto.
    eauto.
    exists M'', vy. intuition.
    eapply IHT2; eauto.
  - eapply closedty_extend; eauto.
  - eapply closedty_extend; eauto.
  - (* Abs grow *)
    inversion H0. subst.
    rename q into q2. 
    destruct (H5 M' vx) as [M'' [vy [HEY [HVY HQY]]]]. 
      eapply IHT1; eauto.
      eauto.
    exists M'', vy. intuition.
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



(* ---------- main lemmas ---------- *)

Lemma sem_app1: forall M M' M'' H Hf G T1 T2 ey vx pv p q1 qf
    (WFE: env_type M H G p)
    (HVF: val_type (M'++M) H (vabs Hf pv ey) (TFun T1 T2))
    (HQF: val_qual M H (vabs Hf pv ey) p qf)
    (HVX: val_type (M''++M'++M) H vx T1)
    (HQX: val_qual (M'++M) H vx p q1),
    psub (pand qf q1) pempty ->
    (* exists vy, exp_type H ey vy T2 p q2. *) (* not exactly this!! *)
    exists M''' vy,
      tevaln (M''++M'++M) (vx::Hf) ey (M'''++M''++M'++M) vy /\
        val_type (M'''++M''++M'++M) H vy T2 /\
        val_qual M H vy p (por qf q1).
Proof.
  
  intros. apply valt_wf in HVF as WFQF. apply valt_wf in HVX as WFQX.
  destruct HVF; intuition.
  rename H5 into HVF.
  destruct (HVF M'' vx) as [M''' [vy [IW3 HVY]]]. eauto. 


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

  exists M''', vy. intuition.

  (* TODO 3: VAL_QUAL *)

  
  (* unfold env_type in WFE. *)
  
  assert (val_qual M H vy p (pand p (por qf q1))) as A. {

  rename H5 into HQY.
  remember (vabs Hf pv ey) as vf.
  unfold val_qual in *.
  
  rewrite <-(vars_locs_dist_and M H G p); eauto.
  2: { unfoldq. intuition. }
  2: { unfoldq. intuition. }
  
  unfoldq. intros. 
  destruct (HQY x). repeat rewrite app_length. intuition.
  + (* part of function *)
    destruct (HQF x). intuition.
    destruct H7. destruct H7.
    split.
    exists x0. intuition.
    exists x0. intuition.
  + (* part of argument *)
    destruct (HQX x). repeat rewrite app_length. intuition. split.
    exists x0. intuition.
    exists x0. intuition.
  }

  unfoldq. intuition.
  destruct (A x). intuition.
  exists x0. intuition.
  
Qed.



Lemma sem_abs1: forall M M1 H G T1 T2 t vx p q2 qf
    (WFE: env_type M H G (plift p))
    (HVX: val_type (M1 ++ M) H vx T1) (* arg from valt *)
    (SEP : psub (pand (val_locs (vabs H (qand p qf) t)) (val_locs vx)) pempty)
    (IHW : (* induction *)
        env_type (M1 ++ M) (vx :: H) (T1 :: G) (plift (qor (qand p qf) (qone (length H)))) ->
        exists (M'' : list vl) (vy : vl),
          exp_type (M1 ++ M) (vx :: H) t M'' vy T2 (plift (qor (qand p qf) (qone (length H))))
            (plift (qor q2 (qone (length H)))))
    (HCLT1: closed_ty (length H) T1)        
    (HCLT2: closed_ty (length H) T2)
    (HCLQ:  closed_ql (length H) (qand p qf)),
  exists (M'' : list vl) (vy : vl),
    tevaln (M1 ++ M) (vx :: H) t (M'' ++ M1 ++ M) vy /\
      val_type (M'' ++ M1 ++ M) H vy T2 /\
      psub (pand (pdom (M1 ++ M)) (val_locs vy))
        (por (val_locs (vabs H (qand p qf) t)) (val_locs vx)).
Proof.
  intros.
  destruct (IHW) as [M2 [vy IHW1]]. {
    rewrite val_locs_abs, plift_and in SEP.
    rewrite plift_or, plift_and, plift_one.
    eapply envt_extend_all; eauto.
  }
  destruct IHW1 as [? IHW1].
  exists M2, vy. intuition.

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
  apply valt_wf in HVX. apply valt_wf in H1.
  rename H2 into HVY.
  
  unfoldq. intuition.
  destruct (HVY x). eauto.
  rewrite plift_or, plift_and, plift_one in H2.
  rewrite plift_or, plift_one in H2.
  unfoldq.
  destruct H2. destruct H2.
  bdestruct (x0 =? length H).
  - (* from arg *)
    right. destruct H5 as [? [? ?]]. subst x0. rewrite indexr_head in H5. inversion H5. eauto.
  - (* from func *)
    left. 
    exists x0. intuition. destruct H5 as [? [? ?]]. rewrite indexr_skip in H5. rewrite plift_and. split; eauto. lia.
    destruct H5 as [? [? ?]]. rewrite indexr_skip in H5; eauto.
Qed.
  




(* if well-typed, then result is an actual value (not stuck and not a timeout),
   for large enough n *)

Theorem full_total_safety : forall e G T p q,
  has_type G e T p q -> forall M E, env_type M E G (plift p) ->
  exists M' v, exp_type M E e M' v T (plift p) (plift q).
Proof.
  intros ? ? ? ? ? W. 
  induction W; intros ? ? WFE; 
  apply wf_env_type in WFE as WFE'; intuition.  
  
  - (* Case "True". *) exists []. exists (vbool true). split.
    exists 0. intros. destruct n. lia. intuition. simpl. intuition.
    eapply valq_bool.
    
  - (* Case "False". *) exists []. eexists. split.
    exists 0. intros. destruct n. lia. intuition. simpl. intuition. 
    eapply valq_bool.
    
  - (* Case "Var". *)
    destruct WFE as [? [? [WFE ?]]].
    destruct (WFE x T H) as [vx [HI ?]]. eauto.
    exists []. eexists. 
    split. exists 0. intros. destruct n. lia. simpl. rewrite HI. reflexivity.
    intuition.

    (* valq *)
    unfoldq. rewrite plift_one.
    unfoldq. intuition.
    exists x. intuition.
    exists vx. intuition.
    
  - (* Case "Ref". *)
    destruct (IHW M E WFE) as [M1 [vx [IW1 [HVX HQX]]]].
    exists (vx::M1). exists (vref (length (M1++M))). split.
    + (* expression evaluates *)
      destruct IW1 as [n1 IW1].
      exists (S n1).
      intros. destruct n. lia.
      simpl. rewrite IW1. eauto. lia.
    + (* result well typed *)
      simpl. bdestruct (length (M1 ++ M) =? length (M1 ++ M)); intuition.
      exists vx; intuition.
      eapply valq_fresh. 

  - (* Case "Get". *)
    destruct (IHW M E WFE) as [M1 [vx [IW1 [HVX HQX]]]].
    destruct vx; try solve [inversion HVX]. simpl in HVX.
    destruct (HVX) as [vy [SI HVX1]].
    exists M1. exists vy. split.
    + (* expression evaluates *)
      destruct IW1 as [n1 IW1].
      exists (S n1).
      intros. destruct n. lia.
      simpl. rewrite IW1. rewrite SI. eauto. lia.
    + (* result well typed *)
      split. eauto.
      destruct vy; intuition.
      unfoldq. rewrite val_locs_bool; auto.
      intuition.
   
  - (* Case "App". *)
    (* induction on both subexpressions: obtain vf, vx *)
    destruct (IHW1 M E WFE) as [M1 [vf [IW1 [HVF HQF]]]].
    assert (env_type (M1++M) E env (plift p)) as WFE1. { eapply envt_store_extend. eauto. }
    destruct (IHW2 (M1++M) E WFE1) as [M2 [vx [IW2 [HVX HQX]]]].

    (* vf is a function value: it can eval its body *)
    destruct vf; try solve [inversion HVF].
    assert (exists M3 vy,
               tevaln (M2++M1++M) (vx::l) t0 (M3++M2++M1++M) vy /\
                 val_type (M3++M2++M1++M) E vy T2 /\
                 val_qual M E vy (plift p) (plift (qor qf q1))
           ) as HVY. {
      apply valt_wf in HVX as HVX'.
      rewrite plift_or.
      eapply sem_app1; eauto. }
    destruct HVY as [M3 [vy [IW3 [HVY HQY]]]].

    (* result *)
    exists (M3++M2++M1). exists vy. split.
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
      repeat rewrite <-app_assoc. repeat split.
      eapply HVY. auto. 

      
  - (* Case "Abs". *)
    exists []. exists (vabs E (qand p qf) t).
    split.
    + (* term evaluates *)
      exists 0. intros. destruct n. lia. simpl. eauto.
    + (* result well typed *)
      rewrite app_nil_l.
      split. simpl. 
      
      assert (pdom env = pdom E) as LE. { unfold pdom. rewrite H3. eauto. }
      
      rewrite LE in *. rewrite <-H3 in *. repeat split; auto.
      rewrite val_locs_abs. eapply env_type_store_wf. eauto.
      rewrite plift_and. unfoldq. intuition.
      
      intros M1 vx HVX SEP.
      eapply sem_abs1; eauto.
      assert (psub (pand (plift p) (plift qf)) (pdom E)) as CL. {
        unfoldq. intuition. }
      rewrite <- plift_and in CL.
      eapply CL.
      eapply valq_abs; eauto.
      
  -  destruct (IHW M E) as [M1 [vx [IW1 [HVX HQX]]]]. { eauto. }
     assert (psub (plift q2) (pdom E)). {
       unfoldq. rewrite H1. intuition. }
     exists M1. exists vx. repeat split. eauto. eauto.
     unfold val_qual in HQX; intuition.
     eapply valq_sub; eauto.
Qed.


(* note: not assuming anything other than has_type below *)

Corollary safety : forall e T q,
  has_type [] e T qempty q -> 
  exists M v, exp_type [] [] e M v T (plift qempty) (plift q).
Proof. 
  intros. eapply full_total_safety in H; eauto.
  unfold env_type; intuition; simpl. unfoldq. intuition.
Qed.

End STLC.
