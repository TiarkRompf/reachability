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
no dependent app.

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
  | TFun   : ty -> ql -> ty -> ql -> ty
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
Definition tenv := list (ty * ql).

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
| c_fun: forall m T1 T2 q1 q2,
    closed_ty m T1 ->
    closed_ty m T2 ->   (* not dependent *)
    closed_ql m q1 ->
    closed_ql m q2 ->   
    closed_ty m (TFun T1 q1 T2 q2)
.

Inductive saturated_var: tenv -> id -> pl -> Prop :=
| sat_var: forall tenv x T q q',
  indexr x tenv = Some (T, q) ->
  psub (plift q) q' ->
  saturated_var tenv x q'.  
#[global] Hint Constructors saturated_var : core.

Definition saturated (env: tenv) (q:  pl) : Prop := (forall x, q x -> saturated_var env x q).
#[global] Hint Unfold saturated : core.


Inductive has_type : tenv -> tm -> ty -> ql -> ql -> Prop :=
| t_true: forall env p,
    has_type env ttrue TBool p qempty     (* nothing reachable from a primitive *)
| t_false: forall env p,
    has_type env tfalse TBool p qempty
| t_var: forall x env T q p,
    indexr x env = Some (T, q) ->
    (plift p) x ->                         (* x in phi *)
    has_type env (tvar x) T p (qor q (qone x))   (* x can reach only itself (no overlap) *)
| t_ref: forall t env p q,
    has_type env t TBool p q ->
    has_type env (tref t) (TRef TBool) p q
| t_get: forall t env p q,
    has_type env t (TRef TBool) p q ->
    has_type env (tget t) TBool p qempty 
| t_app: forall env f t T1 T2 p qf qx q1 q2,
    has_type env f (TFun T1 q1 T2 q2) p qf->  
    has_type env t T1 p qx ->
    (* overlap checking: could relax to intersection of 
       saturated upper bounds, rather than needing qx,qf
       itself to be saturated. *)
    saturated env (pand (plift p) (plift qx)) ->
    saturated env (pand (plift p) (plift qf)) ->
    psub (pand (plift qf) (plift qx)) (plift q1) ->
    psub (plift q2) (plift p) ->   (* this is necessary *)
    has_type env (tapp f t) T2 p (qor q2 qx)
| t_abs: forall env t T1 T2 p q1 q2 qf,      (* assume argument is tracked *)
    has_type ((T1, q1)::env) t T2 (qor (qand p qf) (qone (length env))) (qor q2 (qone (length env))) ->
    closed_ty (length env) T1 ->
    closed_ty (length env) T2 ->
    closed_ql (length env) q1 ->
    closed_ql (length env) q2 ->
    closed_ql (length env) qf ->
    psub (plift q1) (pand (plift qf) (plift p)) -> (* relax it later *)
    has_type env (tabs (qand p qf) t) (TFun T1 q1 T2 q2) p qf
| t_sub: forall env y T p q1 q2,
    has_type env y T p q1 ->
    psub (plift q1) (plift q2) ->
    psub (plift q2) (pdom env)  ->
    has_type env y T p q2
.



(* NOTE: the definitions below could be defined as fixpoint 
   nat -> bool/Prop, but it would take some effort to convince Coq
   of termination. Since we're recursing on vl, tm, and (list vl) 
   simultaneously, Coq would require these three types to be defined 
   jointly to recognize structural recursion across them. 

   Since this is rather cumbersome, we axiomatize the definition of
   rechability below, without proving termination. *)

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
  | vabs G py ty, TFun T1 q1 T2 q2 =>
        closed_ty (length H) T1 /\
        (psub (plift q1) (pdom H)) /\
        closed_ty (length H) T2 /\
        (psub (plift q2) (pdom H)) /\
        (psub (val_locs v) (pdom M)) /\
        (forall M' vx,
            val_type
              (M'++M)
              H
              vx
              T1
            ->
              psub (pand (val_locs v) (val_locs vx)) (vars_locs H (plift q1))  
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
                    (por (pand (vars_locs H (plift q2)) (val_locs v)) (val_locs vx)))
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
    (forall x T (q:ql),
        indexr x G = Some (T, q) ->
     (*   p x -> *)
        exists v : vl,
        psub (plift q) (pdom H) /\  
       (* saturated G (plift q) /\  *)
        indexr x H = Some v /\
        val_type M H v T) /\
    (forall q q',
        psub q p ->
        psub q' p ->
        saturated G q ->
        saturated G q' ->
        psub (pand (vars_locs H q) (vars_locs H q'))
             (vars_locs H (pand q q'))).

(*    (forall l x0 x1,
        p x0 ->
        var_locs H x0 l ->
        p x1 ->
        var_locs H x1 l ->
        x0 = x1).
*)


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


(*----------- saturated lemmas   -----------*)
(*
Lemma saturated_pand : forall {Γ q1 q2}, saturated Γ q1 -> saturated Γ q2 -> saturated Γ (pand q1 q2).
Proof.  
  intros. unfold saturated in *. intros.
  specialize (H x). specialize (H0 x).
  assert (q1 x). { unfoldq. intuition. }
  assert (q2 x). { unfoldq. intuition. }
  intuition. destruct H4. destruct H.
  rewrite H in H0. inversion H0. subst. 
  econstructor; eauto. unfoldq. intuition.
Qed.
#[global] Hint Resolve saturated_pand : core.

Lemma saturated_por : forall {Γ q1 q2}, saturated Γ q1 -> saturated Γ q2 -> saturated Γ (por q1 q2).
Proof.  
  intros. unfold saturated in *. intros.
  assert (q1 x \/ q2 x). { unfoldq. intuition. }
  destruct H2. 
  specialize (H x). intuition.
  destruct H3. 
  econstructor; eauto. unfoldq. intuition.
  specialize (H0 x). intuition.
  destruct H3. 
  econstructor; eauto. unfoldq. intuition.
Qed.
#[global] Hint Resolve saturated_por : core.
*)

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
  + destruct (H6 (M'0 ++ M') vx) as [M'' [vy  [IEY [HVY HSEP]]]]. 
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
  - inversion H0. auto.
  - inversion H0. auto.
  - (* Abs shrink *)
    inversion H0. subst.
    rename q into q2. 
    destruct (H7 M' vx) as [M'' [vy [HEY HVY]]].
      eapply IHT1; eauto.
    rewrite vars_locs_extend; auto.
    exists M'', vy. intuition.
    eapply IHT2; eauto.
    rewrite vars_locs_extend in H10.
    eauto. eauto.
  - eapply closedty_extend; eauto.
  - eapply closedq_extend; eauto.
  - eapply closedty_extend; eauto.
  - unfoldq. rewrite app_length. intuition. eapply H4 in H6. lia.
  - (* Abs grow *)
    inversion H0. subst.
    rename q into q2. 
    destruct (H7 M' vx) as [M'' [vy [HEY [HVY HQY]]]]. 
      eapply IHT1; eauto.
      rewrite vars_locs_extend in H8; auto.
    exists M'', vy. intuition.
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


(* ---------- environment lemmas  ---------- *)

Lemma wf_env_type: forall M H G p, 
  env_type M H G p -> 
  (length H = length G /\
    pdom H = pdom G /\ 
   saturated G (pdom G)) .
Proof.
    intros. unfold env_type in H0. intuition.
    unfold pdom. rewrite H1. auto.
    unfold saturated. intros.
    assert (x < length G) as X. { unfoldq. auto. }
    apply indexr_var_some in X as X'. destruct X'. 
    destruct x0 as [T q].
    econstructor. eauto.
    specialize (H2 x T q  H5).
    destruct H2. assert (pdom H = pdom G). { unfold pdom. rewrite H1. intuition. }
    rewrite <- H6. intuition.
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
    destruct (W x T q); eauto. 
  - intros.
    destruct W as [? W].
    eapply W.
    unfoldq. intuition.
    unfoldq. intuition.
    auto. auto.
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



Lemma saturated_extendq: forall T q1 G (q':pl) x,
   q' (length G) ->
   (plift q1 x) ->
  saturated ((T, q1) :: G) q' ->  q' x.
Proof. 
  intros. 
  specialize (H1 (length G) H).
  inversion H1.
  rewrite indexr_head in H2. inversion H2. subst.
  unfoldq. intuition.
Qed.




Lemma saturated_shrink: forall M H T1 q1 q G p, 
  env_type M H G p ->
  saturated ((T1,q1) :: G) q -> saturated G (pand (pdom G) q).
Proof. 
  intros. destruct H0 as [L [P [W1 W2]]].
  unfold saturated in *. intros.
  specialize (H1 x) as H1'; intuition.
  assert (q x). { unfoldq. intuition. }
  assert ( x < length G). { unfoldq. intuition. }
  intuition. inversion H4. subst.
  rewrite indexr_skip in H5.
  econstructor; eauto.
  specialize (W1 x T q0 H5); intuition.
  destruct W1; intuition. 
  assert (psub (plift q0)(pdom G)).  {
    unfoldq. intuition. rewrite L in H8. eapply H8 in H0.  auto.
  }
  unfoldq. intuition. lia.
Qed.



Lemma envt_extend: forall M H G v T q1 p,
    env_type M H G p ->
    closed_ty (length H) T ->
    (psub (plift q1) (pdom H))  ->
    val_type M H v T ->
    (* overlapping *)
    (forall x l, val_locs v l -> p x -> var_locs H x l ->  (plift q1) x )  ->
    env_type M (v::H) ((T,q1)::G) (por p (pone (length H))).
Proof.
    intros. apply wf_env_type in H0 as H0'. intuition.
    remember H0 as WFE. clear HeqWFE.
    destruct H0 as [L [P [W1 W2]]]. rename H8 into SG. rename H7 into PD. 
    repeat split; auto.
  - simpl. eauto.
  - unfoldq. simpl. intuition.
  - intros. simpl in *. rewrite <-L in *.
    bdestruct (x =? (length H)); intuition; subst.
    +  (* x = length H *)
      inversion H0. subst. exists v. intuition.
      unfoldq. intuition. simpl. eapply H2 in H6. lia.
      eapply valt_extend1; eauto.
    + destruct (W1 _ _ _  H0); eauto.
      intuition.     
      rewrite L in *.
      
      eexists. intuition. 
      unfoldq. intuition. eapply H8 in H9. simpl. lia.
      eauto.
      eapply valt_extend1; eauto.
      eapply valt_closed; eauto.
  - intros.                           
    unfoldq. intuition. 
    destruct H10. destruct H11.
    destruct (H0 x0); intuition;
    destruct (H6 x1); intuition.       
    
    + assert (x0 < length H). { unfoldq. intuition. }
      assert (x1 < length H). { unfoldq. intuition.  }
      destruct (W2 (pand (pdom H) q) (pand (pdom H) q')) with (x:=x). 
      unfoldq. intros. specialize (H0 x2); intuition. 
      intros. specialize (H6 x2); intuition. 
      unfoldq. intuition.
      assert (pdom H = pdom G). { unfoldq. intuition. }
      rewrite H17.
      eapply saturated_shrink in H7; eauto.  
      assert (pdom H = pdom G). { unfoldq. intuition. }
      rewrite H17.
      eapply saturated_shrink in H8; eauto.  
      intuition.
      exists x0. intuition.
      unfoldq. intuition.
      eapply var_locs_shrink. eauto. auto.  
      exists x1. intuition.
      unfoldq. intuition.
      eapply var_locs_shrink. eauto. auto.
      
      unfoldq. destruct H17 as [[? ?] ?]. intuition.
      exists x2; intuition.
      destruct H19.  exists x3. intuition.
      rewrite indexr_skip; auto. lia.
    +
     (*For the cases where x0 < length H and x1 = length H, 
        I think you can show that x0 in q1, and you get from saturation that q1 < q’, 
        and hence x0 < q’ which completes the proof.
      *)
      assert (x0 < length H). { intuition. }
      assert ((plift q1) x0).  {  
        eapply H4; eauto. subst. eapply aux1 in H14. eauto.
        unfoldq.  destruct H13. exists x2. intuition.
        rewrite indexr_skip in H16.  auto. lia.
      }
      assert (q' x0). {
        subst. eapply saturated_extendq; eauto. rewrite <- L. auto.
      }
      exists x0. intuition.      
    + assert (x1 < length H). { intuition. }
      assert ((plift q1) x1).  {  
        eapply H4; eauto. subst. eapply aux1 in H13. eauto.
        unfoldq.  destruct H14. exists x2. intuition.
        rewrite indexr_skip in H16.  auto. lia.
      }
      assert (q x1). {
        subst. eapply saturated_extendq; eauto. rewrite <- L. auto.
      }
      exists x1. intuition. 
    + unfoldq. subst x0 x1.
      exists (length H). intuition.
Qed.



Lemma envt_store_extend: forall M M' H G p,
    env_type M H G p ->
    env_type (M'++M) H G p.
Proof.
  intros. destruct H0 as [L [P W]]. 
  repeat split; auto. intros.
  destruct W as [W W'].
  destruct (W _ _  _ H0) as [vx [QH [IH HVX]]]; intuition.
  exists vx; intuition.
  eapply valt_store_extend in HVX; eauto.
  intros.
  destruct W as [W' W].
  unfoldq. intuition.
Qed.

Lemma envt_extend_all: forall M M1 H G vx T1 p q1 qf,
    env_type M H G p ->
    val_type (M1 ++ M) H vx T1 ->
    psub (pand (vars_locs H (pand p qf)) (val_locs vx)) (vars_locs H (plift q1)) ->
    psub (plift q1) (pand  qf p) ->
    closed_ty (length H) T1 ->
    closed_ql (length H) q1 ->
    env_type (M1 ++ M) (vx :: H) ((T1, q1) :: G) (por (pand p qf) (pone (length H))).
Proof. 
  intros. apply wf_env_type in H0 as H0'.

  assert (env_type (M1 ++ M) H G (pand p qf)) as WFE. {
  eapply envt_store_extend. 
  eapply envt_tighten.
  eauto.
  unfoldq. intuition. }

  remember WFE as WFE1. clear HeqWFE1.
  destruct WFE as [L [P [W1 W2]]].
  repeat split; eauto.
  - simpl. auto.
  - unfoldq; intuition; simpl. 
    assert (x < length H). { eapply P; intuition. }
    lia. lia.
  - intros.
    bdestruct (x =? length G); intuition. 
    + subst. rewrite indexr_head in H6. inversion H6. subst.
      exists vx. repeat split.
      unfoldq; intuition. simpl. 
      specialize (H2 x); intuition.
      rewrite <-  L. rewrite indexr_head. auto.
      eapply valt_extend1; auto.
    + rewrite indexr_skip in H6. 
      specialize (W1 x T q H6).
      assert (x < length H). { rewrite L. apply indexr_var_some' in H6. auto. }
      rewrite indexr_skip.
      destruct W1 as [v [HSUB [IH VALT]]].
      exists v. repeat split.
      unfoldq; intuition. eapply HSUB in H12.  simpl. lia.
      auto.
      eapply valt_extend1. eapply valt_closed in VALT; eauto.
      auto. lia. lia.
  - (* 2nd invariant *)
    intros.
    unfoldq. intuition.
    destruct H14. destruct H15.
    destruct (H6 x0); intuition;
    destruct (H7 x1); intuition.
    + (* both < length H *)
      assert (x0 < length H). { eapply P; auto. }
      assert (x1 < length H). { eapply P; auto. }
      destruct (W2 (pand (pdom H)q ) (pand (pdom H) q')) with (x:=x).
      intros. unfoldq; intuition. 1,2: specialize (H6 x2); intuition. 
      intros. unfoldq; intuition. 1,2: specialize (H7 x2); intuition. 
      
      assert (pdom H = pdom G). { unfoldq. intuition. }
      rewrite H23.
      eapply saturated_shrink in H8; eauto.  
      assert (pdom H = pdom G). { unfoldq. intuition. }
      rewrite H23.
      eapply saturated_shrink in H9; eauto.  
      intuition.
      exists x0. intuition.
      unfoldq. intuition.
      eapply var_locs_shrink. eauto. auto.  
      exists x1. intuition.
      unfoldq. intuition.
      eapply var_locs_shrink. eauto. auto.
      
      unfoldq. destruct H23 as [[? ?] ?]. intuition.
      exists x2; intuition.
      destruct H25.  exists x3. intuition.
      rewrite indexr_skip; auto. lia.
    + rename H2 into SEP.
      assert (x0 < length H). eapply P; eauto.
      subst x1.
      destruct (SEP x).
      intuition. eexists x0. intuition.
      eapply var_locs_shrink; eauto.
      eapply aux1; eauto.
      
      assert (q' x1). {
        eapply saturated_extendq; eauto.
        rewrite <- L. auto. intuition.
      }

      destruct (W2 (pand (pdom H) q) (pand (pdom H) q')) with (x:=x).
      intros. unfoldq. intuition.  1,2: eapply H6 in H24; intuition.
      intros. unfoldq. intuition.  1,2: eapply H7 in H24; intuition.
      assert (pdom H = pdom G). { unfoldq. intuition. }
      rewrite H21.
      eapply saturated_shrink in H8; eauto.  
      assert (pdom H = pdom G). { unfoldq. intuition. }
      rewrite H21.
      eapply saturated_shrink in H9; eauto.
      
      intuition. 
      exists x0. intuition. unfoldq; intuition.
      eapply var_locs_shrink; eauto.
      exists x1. intuition. unfoldq; intuition.
      exists x2; intuition. 1,2: unfoldq; intuition.
      assert  (x2 < length H). { unfoldq; intuition. }
      unfoldq. destruct H24. 
      exists x3. intuition. rewrite indexr_skip; eauto.
      lia.
    + rename H2 into SEP. 
      assert (x1 < length H). { eapply P; eauto. } 
      subst x0.
      destruct (SEP x).  intuition.
      exists x1; intuition. eapply var_locs_shrink; eauto.
      eapply aux1; eauto.
      intuition.
      assert (q x0). {
        eapply saturated_extendq; eauto.
        rewrite <- L. auto. 
      }
      destruct (W2 (pand (pdom H) q) (pand (pdom H) q')) with (x:=x).
      intros. unfoldq. intuition.  1,2: eapply H6 in H24; intuition.
      intros. unfoldq. intuition.  1,2: eapply H7 in H24; intuition.
      assert (pdom H = pdom G). { unfoldq. intuition. }
      rewrite H22.
      eapply saturated_shrink in H8; eauto.  
      assert (pdom H = pdom G). { unfoldq. intuition. }
      rewrite H22.
      eapply saturated_shrink in H9; eauto.
      
      intuition. 
      exists x0. intuition. unfoldq; intuition.
      
      exists x1. intuition. unfoldq; intuition.
      eapply var_locs_shrink; eauto.
      exists x2; intuition. 1,2: unfoldq; intuition.
      assert  (x2 < length H). { unfoldq; intuition. }
      unfoldq. destruct H24. 
      exists x3. intuition. rewrite indexr_skip; eauto.
      lia.
    + subst. exists (length H); intuition.
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

  assert (exists xtq, indexr x0 G = Some xtq) as TY.
  rewrite L in H4.  eapply indexr_var_some in H4. intuition.
  destruct TY as [TQ  ?]. destruct TQ as [T0 q0].
  destruct (W1 x0 T0 q0) as [vx [? ?]]. eauto.
  
  intuition.  apply valt_wf  in H10. 
  rewrite H9 in H2. inversion H2. subst.
  unfoldq. intuition.
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
    saturated env q ->
    saturated env q' ->
    pand (vars_locs E q) (vars_locs E q') = vars_locs E (pand q q').
Proof.
  intros. eapply functional_extensionality.
  intros. eapply propositional_extensionality.
  destruct WFE as [L [P [W SEP]]].
  intuition.
  - eapply SEP; intuition.  
  - destruct H3 as [? [? [? [? ?]]]].
    unfoldq. intuition.
    exists x0. intuition. exists x1. intuition.
    exists x0. intuition. exists x1. intuition.
Qed.

(*
Lemma saturated_overlapping:forall G qf p,
  psub p (pdom G) ->
  saturated G (pand p qf) ->
  saturated G (pand (pdom G)(pand  p qf)).
Proof. 
  intros. unfold saturated in *. intros.
  assert (qf x /\ p x). {  unfoldq; intuition. }
  specialize (H0 x). specialize (H1 x). intuition.
  inversion H3. subst.
  inversion H0. subst. rewrite H7 in H1. inversion H1. subst.
  econstructor; eauto.
  unfoldq. intros. intuition.
Qed.
*)
Lemma overlapping: forall M M' H G p vf vx qf qx q1
    (WFE: env_type M H G p)
    (HQF: val_qual M H vf p qf)
    (HQX: val_qual (M'++M) H vx p qx),
    psub (val_locs vf) (pdom (M'++M)) ->
    saturated G (pand p qx) ->
    saturated G (pand p qf) ->

    psub (pand qf qx) (plift q1) ->
    psub (pand (val_locs vf) (val_locs vx)) (vars_locs H (plift q1)).
Proof. 
  intros. rename H3 into HS. unfoldq. intuition.
  remember WFE as WFE1. clear HeqWFE1.
  destruct WFE as [? [? [? SEP]]].
  bdestruct (x <? length M).
  - destruct (HQF x). intuition.
    destruct (HQX x). rewrite app_length. intuition.
    
    unfoldq. intuition.
    destruct (SEP (pand p qf) (pand p qx)) with (x := x).

    unfoldq. intuition.
    unfoldq. intuition.
    eauto.
    eauto.
        
    intuition.
    exists x0. intuition. unfoldq. intuition.
    exists x1. intuition. unfoldq. intuition.
    unfoldq. intuition.
    specialize (HS x2); intuition.     
    exists x2. intuition.

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
      eapply H0 in H4. lia.
Qed.



(* ---------- main lemmas ---------- *)

Lemma sem_app1: forall M M' M'' H Hf G T1 T2 ey vx qx pv p  q1 q2 qf
    (WFE: env_type M H G p)
    (HVF: val_type (M'++M) H (vabs Hf pv ey) (TFun T1 q1 T2 q2))
    (HQF: val_qual M H (vabs Hf pv ey) p qf)
    (HVX: val_type (M''++M'++M) H vx T1)
    (HQX: val_qual (M'++M) H vx p qx),
    saturated G (pand p qx) ->
    saturated G (pand p qf) ->
    psub (pand qf qx) (plift q1) ->
    psub (plift q2) p -> 
    (* exists vy, exp_type H ey vy T2 p q2. *) (* not exactly this!! *)
    exists M''' vy,
      tevaln (M''++M'++M) (vx::Hf) ey (M'''++M''++M'++M) vy /\
        val_type (M'''++M''++M'++M) H vy T2 /\
        val_qual M H vy p (por (plift q2) qx).
Proof.
  
  intros. apply valt_wf in HVF as WFQF. apply valt_wf in HVX as WFQX.
  
  destruct HVF; intuition.
  rename H10 into HVF.
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

  eapply overlapping; eauto.
  
  (* TODO 3: VAL_TYPE *)
  
  (* go from 
        T2 (qand p qf) (qand p (qand qf q2))
     to
        T2 p (qor q2 q1)
  *)

  exists M''', vy. intuition.

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

  
  rename H10 into HQY.
  remember (vabs Hf pv ey) as vf.
  unfold val_qual in *.

  intros ? ?. unfoldq. 
  destruct (HQY x) as [HH|]. repeat rewrite app_length. intuition.
  + (* part of function *)
    destruct (HQF x). intuition.
    destruct HH as [[? HH] ?].
    exists x1. intuition.
  + (* part of argument *)
    destruct (HQX x). repeat rewrite app_length. intuition. 
    exists x0. intuition.
Qed.

Lemma sem_abs1: forall M M1 H G T1 T2 t vx p q1 q2 qf
    (WFE: env_type M H G (plift p))
    (HSG: saturated G (pdom G))
    (HVX: val_type (M1 ++ M) H vx T1) (* arg from valt *)
    (HOVERLAP : psub (pand (val_locs (vabs H (qand p qf) t)) (val_locs vx)) (vars_locs H (plift q1)))
    (IHW : (* induction *)
        env_type (M1 ++ M) (vx :: H) ((T1, q1) :: G) (plift (qor (qand p qf) (qone (length H)))) ->
        exists (M'' : list vl) (vy : vl),
          exp_type (M1 ++ M) (vx :: H) t M'' vy T2 (plift (qor (qand p qf) (qone (length H))))
            (plift (qor q2 (qone (length H)))))
    (HCLT1: closed_ty (length H) T1)        
    (HCLT2: closed_ty (length H) T2)
    (HCLQ1: closed_ql (length H) q1)
    (HCLQ:  closed_ql (length H) (qand p qf))
    (HP1: psub (plift q1) (pand (plift qf) (plift p))),
  exists (M'' : list vl) (vy : vl),
    tevaln (M1 ++ M) (vx :: H) t (M'' ++ M1 ++ M) vy /\
      val_type (M'' ++ M1 ++ M) H vy T2 /\
      psub (pand (pdom (M1 ++ M)) (val_locs vy))
        (por (pand (vars_locs H (plift q2)) (val_locs (vabs H (qand p qf) t))) (val_locs vx)).  
Proof. 
  intros. apply wf_env_type in WFE as WFE'. destruct WFE' as [PL [DG SG]].
  destruct (IHW) as [M2 [vy IHW1]]. 
  rewrite val_locs_abs, plift_and in HOVERLAP.
  rewrite plift_or, plift_and, plift_one.
  eapply envt_extend_all; eauto. 
  
  
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
    left. split.
    exists x0. intuition. destruct H5 as [? [? ?]]. rewrite indexr_skip in H5. exists x1. split; eauto. lia.
    exists x0. rewrite plift_and. split.
    destruct H2; try lia. eapply H2.
    destruct H5 as [? [? ?]]. rewrite indexr_skip in H5; eauto. 
Qed.




(* if well-typed, then result is an actual value (not stuck and not a timeout),
   for large enough n *)

Theorem full_total_safety : forall e G T p q,
  has_type G e T p q -> forall M E, env_type M E G (plift p) ->  (* saturated G (plift p) -> (* get rid of it later *) *)
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
    destruct (WFE x T q H) as [vx [HQ [HI ?]]]. 
    exists []. eexists. 
    split. exists 0. intros. destruct n. lia. simpl. rewrite HI. reflexivity.
    intuition.

    (* valq *)
    unfoldq. intros. exists x; intuition.
    rewrite plift_or. rewrite plift_one. unfoldq.  intuition.
    unfoldq. intuition.
    exists vx. intuition.
    
  - (* Case "Ref". *)
    destruct (IHW M E WFE) as [M1 [vx [IW1 [HVX HQX]]]]. auto. auto.
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
    destruct (IHW M E WFE) as [M1 [vx [IW1 [HVX HQX]]]]. auto. auto.
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
    destruct (IHW1 M E WFE) as [M1 [vf [IW1 [HVF HQF]]]]. auto. auto.
    assert (env_type (M1++M) E env (plift p)) as WFE1. { eapply envt_store_extend. eauto. }
    destruct (IHW2 (M1++M) E WFE1) as [M2 [vx [IW2 [HVX HQX]]]]. auto. auto.

    (* vf is a function value: it can eval its body *)
    destruct vf; try solve [inversion HVF]. 
    assert (exists M3 vy,
               tevaln (M2++M1++M) (vx::l) t0 (M3++M2++M1++M) vy /\
                 val_type (M3++M2++M1++M) E vy T2 /\
                 val_qual M E vy (plift p) (plift (qor q2 qx))
           ) as HVY. {
      apply valt_wf in HVX as HVX'.
      rewrite plift_or.
      eapply sem_app1; eauto.  }
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

      assert (length env = length E) as LE. { eauto. }
      assert (pdom env = pdom E) as DE. { unfold pdom. destruct WFE. intuition.  }
      
      rewrite DE in *. rewrite LE in *. repeat split; auto.
      rewrite val_locs_abs. eapply env_type_store_wf. eauto.
      rewrite plift_and. unfoldq. intuition.
      
      intros M1 vx HVX SEP. rewrite <- DE in *.
      eapply sem_abs1; eauto.  
      assert (psub (pand (plift p) (plift qf)) (pdom E)) as CL. {
        unfoldq. intuition. }
      rewrite <- plift_and in CL.
      eapply CL.
      eapply valq_abs. 
      
      
  -  destruct (IHW M E) as [M1 [vx [IW1 [HVX HQX]]]]. { eauto. }
     assert (psub (plift q2) (pdom E)). {
       unfoldq. rewrite H1. intuition. } auto. auto.
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
  unfold env_type; intuition; simpl.
  unfoldq. intuition. inversion H0.
  unfoldq. unfoldq. intros.
  destruct H4 as [? [? [? [IX ?]]]]. intuition. inversion H7.
Qed.

End STLC.
