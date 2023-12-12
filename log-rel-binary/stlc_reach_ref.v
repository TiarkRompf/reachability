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
no argument overlap, no dependent app.

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
  | TFun   : ty -> (* qempty -> *) ty -> ql -> ty
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
| c_fun: forall m T1 T2 q2,
    closed_ty m T1 ->
    closed_ty m T2 ->   (* not dependent *)
    closed_ql m q2 ->   
    closed_ty m (TFun T1 (* qempty *) T2 q2)
.


(* assume no overlap *)
Inductive has_type : tenv -> tm -> ty -> ql -> ql -> Prop :=
| t_true: forall env p,
    has_type env ttrue TBool p qempty     (* nothing reachable from a primitive *)
| t_false: forall env p,
    has_type env tfalse TBool p qempty
| t_var: forall x env T  p,
    indexr x env = Some T ->
    (plift p) x ->                       
    has_type env (tvar x) T p (qone x)   (* x can reach only itself (no overlap) *)
| t_ref: forall t env p q,
    has_type env t TBool p q ->
    has_type env (tref t) (TRef TBool) p q
| t_get: forall t env p q,
    has_type env t (TRef TBool) p q ->
    has_type env (tget t) TBool p qempty 
| t_app: forall env f t T1 T2 p qf q1 q2,
    has_type env f (TFun T1 (* qempty  *) T2 q2) p qf->  
    has_type env t T1 p q1 ->
    psub (pand (plift qf) (plift q1)) pempty ->          
    psub (plift q2) (plift p) ->     
    has_type env (tapp f t) T2 p (qor q2 q1)
| t_abs: forall env t T1 T2 p q2 qf,      
    has_type (T1::env) t T2 (qor (qand p qf) (qone (length env))) (qor q2 (qone (length env))) ->
    closed_ty (length env) T1 ->
    closed_ty (length env) T2 ->
    closed_ql (length env) q2 ->
    closed_ql (length env) qf ->
    has_type env (tabs (qand p qf) t) (TFun T1 T2 q2) p qf
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

Fixpoint val_type M1 M2 H1 H2 v1 v2 T : Prop :=
  match v1, v2, T with
  | vbool b1, vbool b2, TBool =>
      b1 = b2
  | vref l1, vref l2, TRef T => 
     T = TBool /\
     (exists vx1 vx2,
      indexr l1 M1 = Some vx1 /\
      indexr l2 M2 = Some vx2 /\
      val_type M1 M2 H1 H2 vx1 vx2 T)
  | vabs G1 py1 ty1, vabs G2 py2 ty2, TFun T1 (* qempty *) T2 q2 =>
      closed_ty (length H1) T1 /\
      closed_ty (length H1) T2 /\
      closed_ty (length H2) T1 /\
      closed_ty (length H2) T2 /\
      (psub (plift q2) (pdom H1)) /\ 
      (psub (plift q2) (pdom H2)) /\ 
      (psub (val_locs v1) (pdom M1)) /\
       psub (val_locs v2) (pdom M2) /\
      (forall M1' M2' vx1 vx2,
            val_type
              (M1'++M1)
              (M2'++M2)
              H1
              H2
              vx1
              vx2
              T1
            ->
              psub (pand (val_locs v1) (val_locs vx1)) pempty ->
              psub (pand (val_locs v2) (val_locs vx2)) pempty
            ->
              exists M1'' M2'' vy1 vy2,
                tevaln
                  (M1'++M1)
                  (vx1::G1)
                  ty1
                  (M1''++M1'++M1)
                  vy1
                /\
                tevaln
                  (M2'++M2)
                  (vx2::G2)
                  ty2
                  (M2''++M2'++M2)
                  vy2  
                /\
                  val_type
                    (M1''++M1'++M1)
                    (M2''++M2'++M2)
                    H1
                    H2
                    vy1
                    vy2
                    T2
                /\
                  psub
                    (pand (pdom (M1'++M1)) (val_locs vy1))
                    (por (pand (vars_locs H1 (plift q2)) (val_locs v1)) (val_locs vx1))
                /\
                  psub
                    (pand (pdom (M2'++M2)) (val_locs vy2))
                    (por (pand (vars_locs H2 (plift q2)) (val_locs v2)) (val_locs vx2)))
              
  | _,_,_ =>
      False
  end.


Definition val_qual (M: stor) H v p (q: pl) :=
  psub (pand (pdom M) (val_locs v)) (vars_locs H (pand p q)).


Definition exp_type M1 M2 H1 H2 t1 t2 M1' M2' T p q :=
  exists v1 v2,
  tevaln M1 H1 t1 (M1'++M1) v1 /\
  tevaln M2 H2 t2 (M2'++M2) v2 /\
    val_type (M1'++M1) (M2'++M2) H1 H2 v1 v2 T /\
    val_qual M1 H1 v1 p q /\
    val_qual M2 H2 v2 p q.


Definition env_type M1 M2 H1 H2 G p :=
  length H1 = length G /\
  length H2 = length G /\
    psub p (pdom H1) /\
    psub p (pdom H2) /\
    (forall x T,
        indexr x G = Some T ->
        p x ->
        exists v1 v2 : vl,
          indexr x H1 = Some v1 /\
          indexr x H2 = Some v2 /\
          val_type M1 M2 H1 H2 v1 v2 T ) /\
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



Hint Constructors ty.
Hint Constructors tm.
Hint Constructors vl.


Hint Constructors has_type.

Hint Constructors option.
Hint Constructors list.


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

Lemma valt_wf: forall T M1 M2 H1 H2 v1 v2,
    val_type M1 M2 H1 H2 v1 v2 T ->
    (psub (val_locs v1) (pdom M1) /\
     psub (val_locs v2) (pdom M2)).
Proof. 
  intros T. induction T; intros; destruct v1; destruct v2; simpl in *; intuition.
  + rewrite val_locs_bool. auto. unfoldq. intuition.
  + rewrite val_locs_bool. auto. unfoldq. intuition.
  + rewrite val_locs_ref. 
    destruct H3 as [vx1 [vx2 [IX1 [IX2 VAL]]]]. 
    eapply indexr_var_some' in IX1.
    unfoldq. intuition.
  + rewrite val_locs_ref. 
    destruct H3 as [vx1 [vx2 [IX1 [IX2 VAL]]]]. 
    eapply indexr_var_some' in IX2.
    unfoldq. intuition. 
Qed.

Lemma valt_closed: forall T M1 M2 H1 H2 v1 v2,
    val_type M1 M2 H1 H2 v1 v2 T ->
    ( closed_ty (length H1) T /\
      closed_ty (length H2) T) .
Proof. 
  intros T. induction T; intros; destruct v1; destruct v2; simpl in *; intuition.
  + econstructor.
  + econstructor.
  + destruct H3 as [? [? [? [? ?]]]]. 
    econstructor. eapply IHT with (H2 := H2). eapply H4.
  + destruct H3 as [? [? [? [? ?]]]]. 
    econstructor. eapply IHT with (H2 := H2). eapply H4.
  + econstructor; eauto.
  + econstructor; eauto.
Qed.


Lemma valt_store_extend: forall T M1' M2' M1 M2 H1 H2 v1 v2,
    val_type M1 M2 H1 H2 v1 v2 T ->
    val_type (M1'++M1) (M2'++M2) H1 H2 v1 v2 T.
Proof.  
  intros T. induction T; intros; destruct v1; destruct v2; simpl in *; intuition.
  + destruct H3 as [vx1 [vx2 [IX1 [IX2 VX]]]].
    exists vx1. exists vx2. intuition. eapply indexr_extend in IX1; intuition.  eapply H.
    eapply indexr_extend in IX2; intuition. eapply H.
  + unfoldq. rewrite app_length. intros. assert (x < length M1). eauto. lia.
  + unfoldq. rewrite app_length. intros. assert (x < length M2). eauto. lia.
  + destruct (H10 (M1'0 ++ M1') (M2'0 ++ M2') vx1 vx2) as [M1''[M2'' [vy1 [vy2 [IEY1 [IEY2 [HVY [HSEP1 HSEP2]]]]]]]]. 
    repeat rewrite <- app_assoc. auto.
    auto. auto.
    exists M1''. exists M2''. exists vy1. exists vy2. intuition.
    repeat erewrite <- app_assoc in IEY1; eauto.
    repeat erewrite <- app_assoc in IEY2; eauto.
    repeat erewrite <- app_assoc in HVY; eauto.
    repeat erewrite <- app_assoc in HSEP1.
    repeat erewrite <- app_assoc in HSEP2; eauto.
    repeat erewrite <- app_assoc in HSEP1.
    repeat erewrite <- app_assoc in HSEP2; eauto.
Qed. 


Lemma valt_extend: forall T M1 M2 H1' H1 H2' H2 v1 v2,
    closed_ty (length H1) T ->
    closed_ty (length H2) T ->
    val_type M1 M2 (H1'++H1) (H2'++H2) v1 v2 T <-> 
    val_type M1 M2 H1 H2 v1 v2 T.
Proof.
  intros T. induction T; split; intros; destruct v1; destruct v2; simpl in *; intuition.
  - (* Ref shrink *)
    destruct H5 as [vx1 [vx2 [IX1 [IX2 HVX]]]].
    exists vx1. exists vx2. intuition.
    eapply IHT; eauto. inversion H; auto. inversion H0; auto. 
  - (* Ref grow *)
     destruct H5 as [vx1 [vx2 [IX1 [IX2 HVX]]]].
     exists vx1. exists vx2. intuition.
    eapply IHT; eauto. inversion H. auto. inversion H0. auto.
  - inversion H. auto.
  - inversion H. auto.
  - inversion H0. auto.
  - inversion H0. auto.
  - inversion H. auto.
  - inversion H0. auto.
  - (* Abs shrink *)
    inversion H0. subst. inversion H. subst.
    rename q into q2. 
    destruct (H12 M1' M2' vx1 vx2) as [M1''[M2''[vy1 [vy2 [HEY1 [HEY2 HVY]]]]]].
      eapply IHT1; eauto.
    eauto. eauto.
    exists M1'', M2'', vy1, vy2. intuition.
    eapply IHT2; eauto.
    rewrite vars_locs_extend in H17. eauto. eauto.
    rewrite vars_locs_extend in H18. eauto. eauto.
  - eapply closedty_extend. apply H4. eauto. 
  - eapply closedty_extend. apply H3. eauto.
  - eapply closedty_extend; eauto. 
  - eapply closedty_extend; eauto. 
  - unfoldq. rewrite app_length. intuition. eapply H7 in H11. lia.
  - unfoldq. rewrite app_length. intuition. eapply H8 in H11. lia.
  - (* Abs grow *)
    inversion H0. subst. inversion H. subst.
    rename q into q2. 
    destruct (H12 M1' M2' vx1 vx2) as [M1''[M2''[vy1 [vy2 [HEY1 [HEY2 HVY]]]]]].
      eapply IHT1; eauto.  eauto. eauto. 
    exists M1'', M2'', vy1, vy2. intuition.
    eapply IHT2; eauto.
    rewrite vars_locs_extend. eauto. eauto.
    rewrite vars_locs_extend. eauto. eauto.
Qed.


Lemma valt_extend1: forall T M1 M2 H1 H2 v1 v2 vx1 vx2,
    closed_ty (length H1) T ->
    closed_ty (length H2) T ->
    val_type M1 M2 (vx1::H1) (vx2::H2) v1 v2 T <-> 
    val_type M1 M2 H1 H2 v1 v2 T.  
Proof.
  intros. 
  replace (vx1 :: H1)  with ([vx1]  ++ H1); auto.
  replace (vx2 :: H2)  with ([vx2]  ++ H2); auto.
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

Lemma wf_env_type: forall M1 M2 H1 H2 G p, 
  env_type M1 M2 H1 H2 G p -> 
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

Lemma envt_tighten: forall M1 M2 H1 H2 G p p',
    env_type M1 M2 H1 H2 G p ->
    psub p' p ->
    env_type M1 M2 H1 H2 G p'.
Proof.
  intros. destruct H as [L1 [L2 [P1 [P2 W]]]].
  repeat split; auto.
  - unfoldq. intuition.
  - unfoldq. intuition.
  - intros.
    destruct W as [W ?].
    destruct (W x T); eauto. 
  - intros.
    destruct W as [? [W1 W2]].
    eauto.
  - intros.
    destruct W as [? [W1 W2]].
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


Lemma envt_extend: forall M1 M2 H1 H2 G v1 v2 T q p,
    env_type M1 M2 H1 H2 G p ->
    closed_ty (length G) T ->
    closed_ql (length G) q ->
    val_type M1 M2 H1 H2 v1 v2 T ->
    (* separation *)
    (forall x l, val_locs v1 l -> p x -> var_locs H1 x l -> False) ->
    (forall x l, val_locs v2 l -> p x -> var_locs H2 x l -> False) ->
    env_type M1 M2 (v1::H1)(v2::H2) (T::G) (por p (pone (length G))).
Proof. 
  intros. apply wf_env_type in H as HH.
  assert (length H1 = length H2). intuition.
  destruct H as [L1 [L2 [P1 [P2 [W1 [W2 W3]]]]]]. 
  repeat split; auto.
  - simpl. eauto.
  - simpl. eauto.
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
    
    + destruct (W1 _ _ H) as [v1' [v2' ?]]; eauto.
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
      subst x1. eapply aux1; eauto.
      eapply var_locs_shrink. eauto. eapply P1; eauto.
    + destruct (H5 x1 l); eauto.
      assert (x0 = length H1). unfoldq. intuition.
      subst x0. eapply aux1; eauto.
      eapply var_locs_shrink. eauto. eapply P1; eauto.
    + unfoldq. lia.
  - intros.
    inversion H; inversion H9.
    + eapply W3; eauto.
      eapply var_locs_shrink. eauto. eapply P2; eauto.
      eapply var_locs_shrink. eauto. eapply P2; eauto.
    + destruct (H6 x0 l); eauto.
      assert (x1 = length H2). unfoldq. intuition.
      subst x1. eapply aux1; eauto.
      eapply var_locs_shrink. eauto. eapply P2; eauto.
    + destruct (H6 x1 l); eauto.
      assert (x0 = length H2). unfoldq. intuition.
      subst x0. eapply aux1; eauto.
      eapply var_locs_shrink. eauto. eapply P2; eauto.
    + unfoldq. lia.
Qed.


Lemma envt_store_extend: forall M1 M2 M1' M2' H1 H2 G p,
    env_type M1 M2 H1 H2 G p ->
    env_type (M1'++M1) (M2'++M2) H1 H2 G p.
Proof.
  intros. destruct H as [L1 [L2 [P1 [P2 [W1 [W2 W3]]]]]]. 
  repeat split; auto. intros.
  destruct (W1 _ _  H H0) as [vx1 [vx2 [IH1 [IH2 HVX]]]]; intuition.
  exists vx1, vx2; intuition.
  eapply valt_store_extend in HVX; eauto.
Qed.


Lemma envt_extend_all: forall M1 M2 M1' M2' H1 H2 G vx1 vx2 T1 p q1 qf,
    env_type M1 M2 H1 H2 G p ->
    val_type (M1' ++ M1)(M2' ++ M2) H1 H2 vx1 vx2 T1 ->
    psub (pand (vars_locs H1 (pand p qf)) (val_locs vx1)) pempty ->
    psub (pand (vars_locs H2 (pand p qf)) (val_locs vx2)) pempty ->
    closed_ty (length G) T1 ->
    closed_ql (length G) q1 ->
    env_type (M1' ++ M1)(M2' ++ M2) (vx1 :: H1)(vx2 :: H2) (T1 :: G) (por (pand p qf) (pone (length G))).
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
  eauto.
  eauto.

  (* now prove separation on the first *) 
  intros.

  unfoldq. unfoldq.
  eapply H3. intuition.
  exists x. intuition.
  destruct H9.
  exists x0. intuition. eauto.
  destruct H9.
  eauto.


  (* now prove separation on the second *) 
  intros.

  unfoldq. unfoldq.
  eapply H4. intuition.
  exists x. intuition.
  destruct H9.
  exists x0. intuition. eauto.
  destruct H9.
  eauto.
Qed.



Lemma env_type_store_wf: forall M1 M2 H1 H2 G p q,
    env_type M1 M2 H1 H2 G p ->
    psub q p ->
    ( psub (vars_locs H1 q) (pdom M1) /\
      psub (vars_locs H2 q) (pdom M2) ).
    
Proof.
  unfoldq; intuition;
  intros; destruct H as [L1 [L2 [P1 [P2 [W1 [W2 W3]]]]]]; intuition;
  unfoldq; intuition.
  (* 1st *)
  destruct H3 as [? [? ?]].
  assert (p x0). eapply H0. eauto.
  assert (x0 < length H1). eauto.

  assert (exists T, indexr x0 G = Some T) as TY. eapply indexr_var_some. rewrite <-L1. eauto.
  destruct TY as [T ?].
  destruct H3 as [? [? ?]].
  destruct (W1 x0 T) as [vx1 [vx2 [IX1 [IX2 IV ]]]]. eauto. eauto.
  rewrite H3 in IX1. inversion IX1. subst x1.

  eapply valt_wf in IV. eapply IV; eauto.

  (* 2st *)
  destruct H3 as [? [? ?]].
  assert (p x0). eapply H0. eauto.
  assert (x0 < length H2). eauto.

  assert (exists T, indexr x0 G = Some T) as TY. eapply indexr_var_some. rewrite <-L2. eauto.
  destruct TY as [T ?].
  destruct H3 as [? [? ?]].
  destruct (W1 x0 T) as [vx1 [vx2 [IX1 [IX2 IV ]]]]. eauto. eauto.
  rewrite H3 in IX2. inversion IX2. subst x1.

  eapply valt_wf in IV. eapply IV; eauto.
Qed.

Lemma vars_locs_dist_and1: forall M1 M2 E1 E2 env p q q'
    (WFE: env_type M1 M2 E1 E2 env p),
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

Lemma vars_locs_dist_and2: forall M1 M2 E1 E2 env p q q'
    (WFE: env_type M1 M2 E1 E2 env p),
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

Lemma separation: forall M1 M1' M2 M2' H1 H2 G p vf1 vf2 vx1 vx2 qf q1
    (WFE: env_type M1 M2 H1 H2 G p)
    (HQF1: val_qual M1 H1 vf1 p qf)
    (HQF2: val_qual M2 H2 vf2 p qf)
    (HQX1: val_qual (M1'++M1) H1 vx1 p q1)
    (HQX2: val_qual (M2'++M2) H2 vx2 p q1)
    (PVF1: psub (val_locs vf1) (pdom (M1'++M1)))
    (PVF2: psub (val_locs vf2) (pdom (M2'++M2)))
    (QSEP: psub (pand qf q1) pempty),
    (
    psub (pand (val_locs vf1) (val_locs vx1)) pempty /\
    psub (pand (val_locs vf2) (val_locs vx2)) pempty
    ).
Proof. 
  intros. unfoldq. intuition.
  1,2: remember WFE as WFE1; clear HeqWFE1;
  destruct WFE as [L1 [L2 [P1 [P2 [W [SEP1 SEP2]]]]]].
  (* 1st *)
  + bdestruct (x <? length M1).
  - destruct (HQF1 x). intuition.
    destruct (HQX1 x). rewrite app_length. intuition.
    assert (x0 = x1). eapply SEP1; intuition; eauto.
    eapply QSEP. subst x0. intuition; eauto.
  - bdestruct (x <? length (M1'++M1)).
    -- destruct (HQX1 x). intuition.
      (* fresh loc in vf, also occurs in vx --> can't happen *)
      assert (psub (vars_locs H1 (pone x0)) (pdom M1)) as L. {
        eapply env_type_store_wf with (M2:= M2)(H2 := H2). eauto. unfoldq. intuition. subst x1. eauto.
      }
      assert (x < length M1). {
        eapply L. unfoldq. exists x0. intuition.
      }
      lia.
    -- (* fresh loc in vx, bigger than vf *)
      eapply PVF1 in H0. lia.
  
  (* 2nd *)
  + bdestruct (x <? length M2).
  - destruct (HQF2 x). intuition.
    destruct (HQX2 x). rewrite app_length. intuition.
    assert (x0 = x1). eapply SEP2; intuition; eauto.
    eapply QSEP. subst x0. intuition; eauto.
  - bdestruct (x <? length (M2'++M2)).
    -- destruct (HQX2 x). intuition.
      (* fresh loc in vf, also occurs in vx --> can't happen *)
      assert (psub (vars_locs H2 (pone x0)) (pdom M2)) as L. {
        eapply env_type_store_wf with (M2:= M2)(H2 := H2). eauto. unfoldq. intuition. subst x1. eauto.
      }
      assert (x < length M2). {
        eapply L. unfoldq. exists x0. intuition.
      }
      lia.
    -- (* fresh loc in vx, bigger than vf *)
      eapply PVF2 in H0. lia.
Qed.


(* ---------- main lemmas ---------- *)

(* sem_app1 is merged into the compatibility lemma *)

Lemma sem_abs1: forall M1 M1' M2 M2' H1 H2 G T1 T2 t1 t2 vx1 vx2 p q2 qf
    (WFE: env_type M1 M2 H1 H2 G (plift p))
    (HVX: val_type (M1' ++ M1) (M2' ++ M2) H1 H2 vx1 vx2 T1) (* arg from valt *)
    (SEP1 : psub (pand (val_locs (vabs H1 (qand p qf) t1)) (val_locs vx1)) pempty)
    (SEP2 : psub (pand (val_locs (vabs H2 (qand p qf) t2)) (val_locs vx2)) pempty)
    (IHW : (* induction *)
       env_type (M1' ++ M1)(M2' ++ M2) (vx1 :: H1)(vx2 :: H2) (T1 :: G) (plift (qor (qand p qf) (qone (length G)))) -> 
        exists (M1'' M2'': list vl) ,
          exp_type (M1' ++ M1)(M2' ++ M2) (vx1 :: H1)(vx2 :: H2) t1 t2 M1'' M2'' T2 (plift (qor (qand p qf) (qone (length G))))
            (plift (qor q2 (qone (length G)))))
    (HCLT1: closed_ty (length G) T1)
    (HCLT2: closed_ty (length G) T2)
    (HCLQ:  closed_ql (length G) (qand p qf)),
  exists (M1'' M2'' : list vl) (vy1 vy2 : vl),
    tevaln (M1' ++ M1) (vx1 :: H1) t1 (M1'' ++ M1' ++ M1) vy1 /\
    tevaln (M2' ++ M2) (vx2 :: H2) t2 (M2'' ++ M2' ++ M2) vy2 /\
      val_type (M1'' ++ M1' ++ M1)(M2'' ++ M2' ++ M2) H1 H2 vy1 vy2 T2 /\
      psub (pand (pdom (M1' ++ M1)) (val_locs vy1))
        (por (pand (vars_locs H1 (plift q2)) (val_locs (vabs H1 (qand p qf) t1))) (val_locs vx1)) /\
      psub (pand (pdom (M2' ++ M2)) (val_locs vy2))
        (por (pand (vars_locs H2 (plift q2)) (val_locs (vabs H2 (qand p qf) t2))) (val_locs vx2)).  
Proof. 
  intros.
  destruct (IHW) as [M1'' [M2''[vy1 [vy2 IHW1]]]]. {
    rewrite val_locs_abs, plift_and in SEP1. 
    rewrite val_locs_abs, plift_and in SEP2. 
    rewrite plift_or, plift_and, plift_one.
    eapply envt_extend_all; eauto.
  }
  destruct IHW1 as [? IHW1].
  exists M1'', M2'', vy1, vy2. intuition.

  (* TODO 2: VAL_TYPE *)

  (* go from
        T2 (qor (qand p qf) (qone (length H))) (qor q2 (qone (length H)))
     to
        T2 (qand p qf) (qand p (qand qf q2))
   *)
  + eapply valt_extend1; eauto.
  assert (length H1 = length G). {  apply wf_env_type in WFE. intuition.  }
  rewrite H5. auto.
  assert (length H2 = length G). { apply wf_env_type in WFE. intuition. }
  rewrite H5. auto.

  (* TODO 3: VAL_QUAL *)
  
  (* vy < vf \/ vx *)
  (* 1st *)
  + assert (length G  = length H1) as L. {  apply wf_env_type in WFE. intuition.  }
  rewrite L in *.
  rewrite val_locs_abs in *.
  apply valt_wf in HVX. apply valt_wf in H4 .
  rename H3 into HQ1.
  
  unfoldq. intuition.
  destruct (HQ1 x). eauto.
  rewrite plift_or, plift_and, plift_one in H4.
  rewrite plift_or, plift_one in H4.
  unfoldq.
  destruct H4. destruct H4.
  bdestruct (x0 =? length H1).
  - (* from arg *)
    right. destruct H11 as [? [? ?]]. subst x0. 
    rewrite indexr_head in H11. inversion H11. eauto.
  - (* from func *)
    left. split. 
    exists x0. intuition. destruct H11 as [? [? ?]]. 
    rewrite indexr_skip in H11. exists x1. split; eauto. lia.
    exists x0. rewrite plift_and. split.
    destruct H4; try lia. eapply H4.
    destruct H11 as [? [? ?]]. rewrite indexr_skip in H11; eauto.

  (* 2nd *)
  + assert (length G  = length H2) as L. { apply wf_env_type in WFE. intuition. }
  rewrite L in *.
  rewrite val_locs_abs in *.
  apply valt_wf in HVX. apply valt_wf in H4 .
  rename H6 into HQ2.
  
  unfoldq. intuition.
  destruct (HQ2 x). eauto.
  rewrite plift_or, plift_and, plift_one in H4.
  rewrite plift_or, plift_one in H4.
  unfoldq.
  destruct H4. destruct H4.
  bdestruct (x0 =? length H2).
  - (* from arg *)
    right. destruct H11 as [? [? ?]]. subst x0. 
    rewrite indexr_head in H11. inversion H11. eauto.
  - (* from func *)
    left. split. 
    exists x0. intuition. destruct H11 as [? [? ?]]. 
    rewrite indexr_skip in H11. exists x1. split; eauto. lia.
    exists x0. rewrite plift_and. split.
    destruct H4; try lia. eapply H4.
    destruct H11 as [? [? ?]]. rewrite indexr_skip in H11; eauto.
  
Qed.


(* compatibility lemmas *)

Lemma bi_vtrue: forall M1 M2 H1 H2 p q,
  exp_type M1 M2 H1 H2 ttrue ttrue [] []  TBool p q.
Proof.   
  intros. exists (vbool true). exists (vbool true). repeat split.  
  exists 0. intros. destruct n. lia. simpl. eauto.
  exists 0. intros. destruct n. lia. simpl. eauto.
  apply valq_bool. apply valq_bool.
Qed.

Lemma bi_vfalse: forall M1 M2 H1 H2 p q,
  exp_type M1 M2 H1 H2 tfalse tfalse [] [] TBool p q.
Proof.   
  intros. exists (vbool false). exists (vbool false). repeat split.  
  exists 0. intros. destruct n. lia. simpl. eauto.
  exists 0. intros. destruct n. lia. simpl. eauto.
  apply valq_bool. apply valq_bool.
Qed.

Lemma bi_var: forall G M1 M2 H1 H2 x T1 p
  (WFE: env_type M1 M2 H1 H2 G p),
  indexr x G = Some T1 ->
  p x ->
  exp_type M1 M2 H1 H2 (tvar x) (tvar x) [] [] T1 p (pone x).
Proof.
  intros. 
  eapply WFE in H. destruct H as [v1 [v2 [IX1 [IX2 VT]]]].
  exists v1, v2. repeat split.
  exists 0. intros. destruct n. lia. simpl. congruence.
  exists 0. intros. destruct n. lia. simpl. congruence.
  auto.
  unfoldq. unfoldq. intuition.  exists x. intuition.
  exists v1. intuition.
  unfoldq. unfoldq. intuition.  exists x. intuition.
  exists v2. intuition.
  auto.
Qed.

Lemma bi_tref: forall e1 e2 M1 M2 M1' M2' H1 H2  p q,
  exp_type M1 M2 H1 H2 e1 e2 M1' M2' TBool p q->
  exists M1'' M2'',
   exp_type M1 M2 H1 H2 (tref e1) (tref e2) M1'' M2'' (TRef TBool) p q.
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
  
  apply valq_fresh. apply valq_fresh.
Qed.

Lemma bi_tget: forall e1 e2 M1 M2 M1' M2' H1 H2 p q,
  exp_type M1 M2 H1 H2 e1 e2 M1' M2' (TRef (TBool)) p q->
  exp_type M1 M2 H1 H2 (tget e1) (tget e2) M1' M2' TBool p pempty.
Proof. 
  intros. destruct H as [v1 [v2 [EV1 [EV2 [HV [HQ1 HQ2]]]]]].
  destruct v1; destruct v2; try solve [inversion HV]. simpl in HV.
  destruct HV as [HT [vy1 [vy2 [SI1 [SI2 HVY]]]]].
  unfold exp_type.
  exists vy1, vy2. repeat split.
  + destruct EV1 as [n1 IW1].
    exists (S n1). intros. destruct n. lia. simpl.
    rewrite IW1. rewrite SI1. eauto. lia.
  + destruct EV2 as [n1 IW2].
    exists (S n1). intros. destruct n. lia. simpl.
    rewrite IW2. rewrite SI2. eauto. lia.
  + destruct vy1; destruct vy2; intuition.
  + destruct vy1; destruct vy2; intuition. 
    unfoldq. rewrite val_locs_bool; auto. intuition.
  + destruct vy1; destruct vy2; intuition. 
    unfoldq. rewrite val_locs_bool; auto. intuition.
Qed.

Lemma bi_tabs: forall H1 H2 M1 M2 G e1 e2 T1 T2 p q2 qf
  (WFE: env_type M1 M2 H1 H2 G (plift p))
  (EXP:  forall M1' M2' vx1 vx2,
      val_type (M1'++M1) (M2'++M2) H1 H2 vx1 vx2 T1  ->
      env_type (M1'++M1) (M2'++M2) (vx1::H1) (vx2:: H2) (T1::G) (plift (qor (qand p qf)(qone (length G)))) ->
      exists M1''  M2'',
        exp_type (M1'++M1) (M2'++M2) (vx1:: H1) (vx2:: H2) e1 e2 M1'' M2'' T2 (plift (qor (qand p qf)(qone  (length G)))) (plift (qor q2 (qone (length G)))))
  (T1CL: closed_ty (length G) T1)      
  (T2CL: closed_ty (length G) T2)
  (HQ2: (psub (plift q2) (pdom G)))
  (HCLQF: closed_ql (length G) qf),
  exp_type M1 M2 H1 H2 (tabs (qand p qf) e1) (tabs (qand p qf) e2) [] [] (TFun T1 T2 q2 ) (plift p) (plift qf).
Proof. 
  intros. apply wf_env_type in WFE as WFE'. 
  destruct WFE' as [L1 [L2 [PD1 [PD2 [P1 P2]]]]].
  exists (vabs H1 (qand p qf) e1). exists (vabs H2 (qand p qf) e2).
  repeat split; simpl.
  + (* 1st *)
    exists 0.  intros. destruct n. lia. simpl. eauto.
  + (* 2nd *)
    exists 0.  intros. destruct n. lia. simpl. eauto.
  + rewrite L1. auto.
  + rewrite L1. auto.
  + rewrite L2. auto.
  + rewrite L2. auto.
  + rewrite PD1. auto.
  + rewrite PD2. auto.
  + rewrite val_locs_abs. eapply env_type_store_wf with (M2 := M2)(H2 := H2). eauto.
    rewrite plift_and. unfoldq. intuition.
  + rewrite val_locs_abs. eapply env_type_store_wf with (M2 := M2)(H2 := H2). eauto.
    rewrite plift_and. unfoldq. intuition.
  + intros.  eapply sem_abs1; eauto. 
    assert (psub (pand (plift p) (plift qf)) (pdom G)) as CL. {
        unfoldq. intuition. }
    rewrite <- plift_and in  CL. eapply CL.
  + eapply valq_abs; eauto.
  + eapply valq_abs; eauto.
Qed.


Lemma bi_tapp: forall M1 M2 M1' M2' M1'' M2'' G H1 H2 ef1 ef2 ex1 ex2 T1 T2 p qf q1 q2
   (WFE: env_type M1 M2 H1 H2 G p)
   (IEF: exp_type M1 M2 H1 H2 ef1 ef2 M1' M2' (TFun T1 T2 q2) p qf)  
   (IEX: exp_type (M1'++M1) (M2'++M2) H1 H2 ex1 ex2 M1'' M2'' T1 p q1)  
   (QSEP: psub (pand qf q1) pempty)
   (Q2: psub (plift q2) p),
   exists M1''' M2''',
   exp_type M1 M2 H1 H2 (tapp ef1 ex1)(tapp ef2 ex2) M1''' M2''' T2 p (por (plift q2) q1).
Proof.
  intros. 
  destruct IEF as [vf1 [vf2 [IEF1 [IEF2 [HVF [HQF1 HQF2]]]]]].
  destruct IEX as [vx1 [vx2 [IEX1 [IEX2 [HVX [HQX1 HQX2]]]]]].

  destruct vf1; destruct vf2; try solve [inversion HVF]; simpl in HVF; intuition.
  rename H10 into HVF.
  specialize (HVF M1'' M2'' vx1 vx2); intuition.
  
  assert ( psub (pand (val_locs (vabs l q t)) (val_locs vx1)) pempty  /\
      psub (pand (val_locs (vabs l0 q0 t0)) (val_locs vx2)) pempty ). { 
       eapply separation; eauto.
  }
  intuition.   
  destruct H9 as [M1'''[M2'''[r1 [r2 [IAPP1 [IAPP2 [IVALY [? ?]]]]]]]]. 
  exists (M1'''++M1''++M1'). exists (M2'''++M2''++M2'). exists r1. exists r2.

  repeat split; auto.
  + (* 1st function *)
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

  + (* 2nd function *)
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
  +
  replace ((M1''' ++  M1'' ++ M1') ++ M1)
    with  (M1''' ++  M1'' ++ M1' ++ M1). 
  replace ((M2''' ++  M2'' ++ M2') ++ M2)
    with  (M2''' ++  M2'' ++ M2' ++ M2). auto.
  1,2: repeat rewrite app_assoc; auto.

  
  + (* 1st *)
  assert (val_qual M1 H1 r1 p (pand p (por (plift q2) q1))) as A. {
    remember (vabs l q t) as vf1.
    unfold val_qual.
    rewrite <-(vars_locs_dist_and1 M1 M2 H1 H2 G p); eauto. 
    2: {unfoldq. intuition. }
    2: {unfoldq. intuition. }
    rename H9 into HQY1.  
    unfoldq. intros.
    destruct (HQY1 x). repeat rewrite app_length. intuition.
    - (* part of function *)
      destruct (HQF1 x). intuition.
      destruct H13. destruct H13.
      split.
      exists x0. intuition. unfoldq. intuition.
      exists x1. intuition. 
  - (* part of argument *)
    destruct (HQX1 x). repeat rewrite app_length. intuition. split.
    exists x0. intuition.
    exists x0. intuition.
  }
  unfoldq. intuition.
  destruct (A x). intuition.
  exists x0. intuition.

  + (* 2nd *)

  assert (val_qual M2 H2 r2 p (pand p (por (plift q2) q1))) as B. {
    remember (vabs l0 q0 t0) as vf2.
    unfold val_qual.
    rewrite <-(vars_locs_dist_and2 M1 M2 H1 H2 G p); eauto. 
  2: {unfoldq. intuition. }
  2: {unfoldq. intuition. }
  rename H10 into HQY2.  
  unfoldq. intros.
  destruct (HQY2 x). repeat rewrite app_length. intuition.
  - (* part of function *)
    destruct (HQF2 x). intuition.
    destruct H13. destruct H13.
    split.
    exists x0. intuition. unfoldq. intuition.
    exists x1. intuition. 
  - (* part of argument *)
    destruct (HQX2 x). repeat rewrite app_length. intuition. split.
    exists x0. intuition.
    exists x0. intuition.
  }
  unfoldq. intuition.
  destruct (B x). intuition.
  exists x0. intuition.
Qed.  

Lemma bi_qsub: forall M1 M2 H1 H2 e1 e2 M1' M2' T p q q',  
  exp_type M1 M2 H1 H2 e1 e2 M1' M2' T p q->
  psub q q' ->
  psub q' (pdom H1)  ->
  psub q' (pdom H2)  ->
  exp_type M1 M2 H1 H2 e1 e2 M1' M2' T p q'.
Proof.  
  intros.
  destruct H as [vx1 [vx2 [IE1 [IE2 [IVAL [IQ1 IQ2]]]]]]. 
  exists vx1. exists vx2. repeat split. eauto. eauto.
     unfold val_qual in IQ1; intuition.
     eapply valq_sub; eauto.
     unfold val_qual in IQ2; intuition.
     eapply valq_sub; eauto.
Qed.

(* if well-typed, then result is an actual value (not stuck and not a timeout),
   for large enough n *)

Theorem fundamental_property : forall e G T p q,
  has_type G e T p q  -> 
  forall M1 M2 H1 H2, env_type M1 M2 H1 H2 G (plift p) ->
  exists M1'  M2',
  exp_type M1 M2 H1 H2 e e M1' M2' T (plift p) (plift q).

Proof.
  intros ? ? ? ? ? W. 
  induction W; intros ? ? ? ? WFE.
  - (* Case "True". *)
    exists []. exists [].
    eapply bi_vtrue.
  - (* Case "False". *)
    exists []. exists [].
    eapply bi_vfalse.
  - (* Case "Var". *)
    exists []. exists [].
    rewrite plift_one.
    eapply bi_var; eauto.
  - (* Case "Ref". *)
    specialize (IHW M1 M2 H1 H2); intuition.
    destruct H as [M1' [M2' IEX]].
    eapply bi_tref; eauto.
  - (* Case "Get". *)
    specialize (IHW M1 M2 H1 H2); intuition.
    destruct H as [M1' [M2' IEX]].
    exists M1'. exists M2'.
    rewrite plift_empty.
    eapply bi_tget; eauto.
  - (* Case "App". *)
    specialize (IHW1 M1 M2 H1 H2); intuition.
    destruct H3 as [M1' [M2' IEF]].
    assert (env_type (M1'++M1) (M2'++M2) H1 H2 env (plift p)) as WFE1. { eapply envt_store_extend. eauto. }
    specialize (IHW2 (M1'++M1) (M2'++M2) H1 H2); intuition.
    destruct H3 as [M1'' [M2'' IEX]].
    rewrite plift_or.
    eapply bi_tapp; eauto. 
    
  - (* Case "Abs". *)
    exists []. exists[].
    eapply bi_tabs. eauto. intros. 
    eapply IHW; eauto. auto. auto.
    unfoldq; intuition. auto.

  - (* Case "qsub". *)
    specialize (IHW M1 M2 H1 H2 WFE).
    destruct IHW  as [M1' [M2' IHW]].

    assert (psub (plift q2) (pdom H1)). {
      assert (length H1 = length env) as L1. { apply wf_env_type in WFE.  intuition. }
           unfoldq. rewrite L1. intuition. }
      assert (psub (plift q2) (pdom H2)). {
        assert (length H2 = length env) as L2. { apply wf_env_type in WFE.  intuition. }
       unfoldq. rewrite L2. intuition. }
    exists M1'. exists M2'.   
    eapply bi_qsub; eauto.
Qed.


Definition sem_type G e1 e2 T p q:=
  forall M1 M2 H1 H2,
    env_type M1 M2 H1 H2 G p ->
    exists M1' M2',
    exp_type M1 M2 H1 H2 e1 e2 M1' M2' T p q.

Lemma bi_vtrue2: forall G p q,
  sem_type G ttrue ttrue TBool p q.
Proof. 
  intros G p q M1 m2 h1 H2 WFE.
   exists []. exists [].
  eapply bi_vtrue.
Qed.

Lemma bi_vfalse2: forall G p q,
  sem_type G tfalse tfalse TBool p q.
Proof.
  intros G p q M1 M2 H1 H2 WFE. 
  exists []. exists [].
  eapply bi_vfalse.
Qed.

Lemma bi_var2: forall G x T1 (p:pl),
  indexr x G = Some T1 ->
  p x ->
  sem_type G (tvar x) (tvar x) T1 p (pone x).
Proof.
  intros. intros M1 M2 H1 H2 WFE.
  exists []. exists [].
  eapply bi_var; eauto.
Qed.

Lemma bi_tref2: forall G e1 e2 p q,
  sem_type G e1 e2 TBool p q ->
  sem_type G (tref e1) (tref e2) (TRef TBool) p q.
Proof.
  intros.
  intros M1 M2 H1 H2 WFE.
  unfold sem_type in H.
  specialize (H M1 M2 H1 H2 WFE) as [M1' [M2' IE]].
  eapply bi_tref; eauto.
Qed.

Lemma bi_tget2: forall G e1 e2 p q,
  sem_type G e1 e2 (TRef TBool) p q ->
  sem_type G (tget e1) (tget e2) TBool p (plift qempty).
Proof. intros.
  intros M1 M2 H1 H2 WFE.
  unfold sem_type in H.
  specialize (H M1 M2 H1 H2 WFE) as [M1' [M2' IE]].
  exists M1'. exists M2'.
  rewrite plift_empty.
  eapply bi_tget; eauto.
Qed.

Lemma bi_tabs2: forall G e1 e2 T1 T2 p qf q2 
 (SEM: sem_type (T1 :: G) e1 e2 T2  (plift (qor (qand p qf)(qone (length G)))) (plift (qor q2 (qone (length G)))))
 (CLT1: closed_ty (length G) T1 )
 (CLT2: closed_ty (length G) T2 )  
 (QSUB: psub (plift q2) (pdom G) )
 (CLQF: closed_ql (length G)  qf ),
  sem_type G (tabs (qand p qf) e1) (tabs (qand p qf) e2) (TFun T1 T2  q2)  (plift p)  (plift qf).
Proof. 
  intros. intros M1 M2 H1 H2 WFE.
  exists []. exists []. 
  eapply bi_tabs; eauto. 
Qed.

Lemma bi_qsub2: forall G e1 e2 T p q q' 
  (SEM: sem_type G e1 e2 T p q) 
  (PSUB1: psub q q')
  (PSUB2: psub q' (pdom G)), 
  sem_type G e1 e2 T p q'.
Proof.
  intros. intros M1 M2 H1 H2 WFE.
  unfold sem_type in SEM.
  specialize (SEM M1 M2 H1 H2 WFE) as [M1' [M2' IE]].
  exists M1', M2'.
  eapply bi_qsub; eauto.
  all: apply wf_env_type in WFE; intuition.
  rewrite H0. auto. rewrite H4. auto.
Qed.

Lemma bi_app2: forall G e1 e2 ex1 ex2 T1 T2 p qf q1 q2
  (SEMF: sem_type G e1 e2 (TFun T1 T2 q2) p qf) 
  (SEMX: sem_type G ex1 ex2 T1 p q1)
  (SEP: psub (pand qf q1) pempty)
  (QSUB: psub (plift q2) p),
  sem_type G (tapp e1 ex1) (tapp e2 ex2) T2 p (por (plift q2) q1).
Proof.
  intros. intros M1 M2 H1 H2 WFE.
  unfold sem_type in SEMF.  unfold sem_type in SEMX.
  destruct (SEMF M1 M2 H1 H2 WFE) as [M1' [M2' IEF]].

  assert (env_type (M1'++M1) (M2'++M2) H1 H2 G p) as WFE1. { eapply envt_store_extend. eauto. }
  
  destruct (SEMX (M1'++M1) (M2'++M2) H1 H2 WFE1) as [M1'' [M2'' IEX]].
   
  eapply bi_tapp; eauto.
Qed.

Theorem fundamental_property2 : forall e G T p q,
  has_type G e T p q -> 
  sem_type G e e T (plift p) (plift q).
Proof.
  intros. induction H. 
  - (* Case "True". *)
    eapply bi_vtrue2.
  - (* Case "False". *)
    eapply bi_vfalse2.
  - (* Case "Var". *)
    rewrite plift_one.  eapply bi_var2; eauto.
  - (* Case "tref" *)
    eapply bi_tref2; eauto.
  - (* Case "tget"  *)
    eapply bi_tget2; eauto.
  - (* Case "App" *)
    rewrite plift_or.
    eapply bi_app2; eauto.
  - (* Case "Abs" *)
    eapply bi_tabs2; eauto.
  - (* Case "qsub" *)
    eapply bi_qsub2; eauto.  
Qed.


Inductive ctx_type : (tm -> tm) -> tenv -> ty -> pl -> pl -> tenv -> ty -> pl -> pl ->  Prop :=
| cx_top: forall G T p q,
    ctx_type (fun x => x) G T p q G T p q
| cx_ref: forall G  p q,
    ctx_type (fun x => tref x) G TBool p q G (TRef TBool) p q
| cx_app1: forall e2 G T1 T2 q1  q2 p qf,
    has_type G e2 T1 p q1 ->
    psub (pand qf (plift q1)) pempty ->
    psub (plift q2) (plift p) ->
    ctx_type (fun x => tapp x e2) G (TFun T1 T2 q2) (plift p) qf G T2 (plift p) (por (plift q2) (plift q1))
| cx_app2: forall e1 G T1 T2 q2 p qf q1,
    has_type G e1 (TFun T1 T2 q2) p qf ->
     psub (pand (plift qf) q1) pempty ->
    psub (plift q2) (plift p) ->
    ctx_type (fun x => tapp e1 x) G T1 (plift p) q1 G T2 (plift p) (por (plift q2) q1)
| cx_abs: forall G T1 T2 q2 p qf,
    closed_ty (length G) T1 ->
    closed_ty (length G) T2 ->
    psub (plift q2) (pdom G) ->
    closed_ql (length G) qf ->
    ctx_type (fun x => tabs (qand p qf) x) (T1::G) T2 (plift (qor (qand p qf)(qone (length G)))) (plift (qor q2 (qone (length G)))) G (TFun T1 T2 q2) (plift p) (plift qf) 
| cx_qsub: forall G T p q q',
    psub q q' ->
    psub q' (pdom G) -> 
    ctx_type (fun x => x) G T p q G T p q'
.

Theorem congr:
  forall C G1 T1 p q G2 T2 p' q',
    ctx_type C G1 T1 p q G2 T2 p' q' ->
  forall e e',
    sem_type G1 e e' T1 p q->
    sem_type G2 (C e) (C e') T2 p' q'.
Proof.
  intros ? ? ? ? ? ? ? ? ? CX.
  induction CX; intros.
  - eauto.
  - eapply bi_tref2. eauto.
  - eapply bi_app2; eauto. eapply fundamental_property2. eauto.    
  - eapply bi_app2; eauto. eapply fundamental_property2. eauto. 
  - eapply bi_tabs2; eauto.
  - eapply bi_qsub2; eauto.
Qed.


Lemma adequacy: forall e e',
  sem_type [] e e' TBool pempty pempty->
  (exists v M  M', 
    tevaln [] [] e M v <-> 
    tevaln [] [] e' M' v).
Proof. 
  intros. 
  assert (env_type [] [] [] [] [] pempty) as WFE. { 
    unfold env_type; intuition. 
    1,2: unfoldq; intros; intuition.
  }
  unfold sem_type in H. 
  specialize (H [] [] [] [] WFE). 
  destruct H as [M1 [M2 ?]].
  destruct H as [? [? [? [? [? ?]]]]].
  rewrite app_nil_r in *.
  destruct x; destruct x0; try solve [inversion H1]. simpl in H1.
  subst.
  exists (vbool b0), M1, M2; intuition. 
Qed.

Definition context_equiv G t1 t2 T1 p q:=
  has_type G t1 T1 p q ->
  has_type G t2 T1 p q->
  forall C,
    ctx_type C G T1 (plift p) (plift q) [] TBool (plift qempty) (plift qempty) ->
    (exists v M1 M2, tevaln [] [] (C t1) M1 v 
          <->
    tevaln [] [] (C t2) M2 v).


(* soundness of binary logical relations *)
Theorem soundess: forall G t1 t2 T p q,
  has_type G t1 T p q ->
  has_type G t2 T p q ->
    (sem_type G t1 t2 T (plift p) (plift q) -> 
     context_equiv G t1 t2 T p q).    
Proof. 
  intros. unfold context_equiv. intros.
  rewrite plift_empty in *.
  assert (sem_type [] (C t1)(C t2) TBool pempty pempty). {
   specialize (congr C G  T (plift p) (plift q) [] TBool pempty pempty ); intuition.
   }

  eapply adequacy; eauto. 
Qed.   



End STLC.
