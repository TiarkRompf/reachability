(* Full safety for STLC *)

(* based on stlc_reach.v and stlc_ref.v *)
(* based on stlc_reach_ref_kill.v and stlc_reach_ref_nested_stty.v *)


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

This version adds use and kill effects. Every dereference incurs
a use effect. A free operation incurs a kill effect, and replaces
the store entry with a tombstone. Effect checking ensures that
all dereferences use live variables that have not been freed.

Extensions:

- nested variables (this file!)
- move effects

- mutation (swap) -- does is remain terminating, or will we need step indexing?

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

Definition pdiff p1 p2 (x:nat) := p1 x /\ ~ p2 x.                   (* difference *)

Definition pdom {X} (H: list X) := fun x' =>  x' < (length H).      (* domain of a list *)

Definition psub (p1 p2: pl): Prop := forall x:nat, p1 x -> p2 x.    (* subset inclusion *)

Definition plift (b: ql): pl := fun x => b x = true.                (* reflect nat->bool set *)


Inductive ty : Type :=
  | TBool  : ty
  | TRef   : ty -> ty
  | TFun   : ty -> (* qempty -> *) ty -> ql -> ql -> ql -> bool -> bool -> bool -> ty
.

(* TFun
        T1      : argument type
        T2      : result type

        q2      : result reachability qualifer (set of variables)
        e2      : result use effect qualifier (set of variables)
        k2      : result kill effect qualifier (set of variables)

        q2x     : argument reachable from result?
        e2x     : argument used?
        k2x     : argument killed?

   Q/TODO: explicit freshness marker, too?

*)

Inductive tm : Type :=
  | ttrue : tm
  | tfalse : tm
  | tvar : id -> tm
  | tref : tm -> tm
  | tget : tm -> tm
(*| tput : tm -> tm -> tm  *)
  | tfree : tm -> tm
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

Definition stor := list (option vl).


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
| c_fun: forall m T1 T2 q2 e2 k2 q2x e2x k2x,
    closed_ty m T1 ->
    closed_ty m T2 ->   (* not dependent *)
    closed_ql m q2 ->
    closed_ql m e2 ->
    closed_ql m k2 ->   
    closed_ty m (TFun T1 (* qempty *) T2 q2 e2 k2 q2x e2x k2x)
.


(* assume no overlap *)
Inductive has_type : tenv -> tm -> ty -> ql -> ql -> ql -> ql -> Prop :=
| t_true: forall env p,
    has_type env ttrue TBool p qempty qempty qempty    (* nothing reachable from a primitive *)
| t_false: forall env p,
    has_type env tfalse TBool p qempty qempty qempty
| t_var: forall x env T  p,
    indexr x env = Some T ->
    (plift p) x ->                         (* x in phi *)
    has_type env (tvar x) T p (qone x) qempty qempty  (* x can reach only itself (no overlap) *)
| t_ref: forall t env T p q e k,
    has_type env t T p q e k ->
    has_type env (tref t) (TRef T) p q e k
| t_get: forall t env T p q e k,
    has_type env t (TRef T) p q e k ->
    psub (pand (plift k) (plift q)) pempty ->
    has_type env (tget t) T p q (qor e q) k
| t_free: forall t env T p q e k,
    has_type env t (TRef T) p q e k ->
    has_type env (tfree t) TBool p qempty e (qor k q) (* always return 'false' *)
    (* returning killed value would be unsafe! *)
| t_app: forall env f t T1 T2 p qf q1 q2 ef e1 e2 kf k1 k2 q2x e2x k2x,
    has_type env f (TFun T1 (* qempty  *) T2 q2 e2 k2 q2x e2x k2x) p qf ef kf ->  
    has_type env t T1 p q1 e1 k1 ->
    psub (pand (plift qf) (plift q1)) pempty ->          (* no overlapping *)
    psub (pand (plift kf) (plift e1)) pempty ->          (* no use after kill *)
    psub (pand (por (plift kf) (plift k1)) (por (plift e2) (if e2x then (plift q1) else pempty))) pempty ->          (* no use after kill *)
    psub (plift q2) (plift p) ->
    psub (plift e2) (plift p) ->
    psub (plift k2) (plift p) ->
    (* NOTE: we can return OR kill the function arg, but not both.  *)
    (*       possible to refine: only an issue if the function arg may be fresh! *)
    (k2x = true -> q2x = false) ->
    has_type env (tapp f t) T2 p
      (qor q2                   (if q2x then q1 else qempty))
      (qor (qor ef (qor e1 e2)) (if e2x then q1 else qempty))
      (qor (qor kf (qor k1 k2)) (if k2x then q1 else qempty))
| t_abs: forall env t T1 T2 p q2 qf e2 k2 (q2x e2x k2x: bool),
    has_type (T1::env) t T2
      (qor (qand p qf) (qone (length env)))
      (qor q2 (if q2x then (qone (length env)) else qempty))
      (qor e2 (if e2x then (qone (length env)) else qempty))
      (qor k2 (if k2x then (qone (length env)) else qempty)) ->
    (* we can return OR kill the function arg, but not both. here:
       exclude arg from kill set. todo: allow the reverse, too *)
    closed_ty (length env) T1 ->
    closed_ty (length env) T2 ->
    closed_ql (length env) qf ->
    closed_ql (length env) q2 ->
    closed_ql (length env) e2 ->
    closed_ql (length env) k2 ->
    (*  *)
    has_type env (tabs (qand p qf) t) (TFun T1 T2 q2 e2 k2 q2x e2x k2x) p qf qempty qempty 
| t_sub: forall env y T p q1 q2 e1 e2 k1 k2,
    has_type env y T p q1 e1 k1 ->
    psub (plift q1) (plift q2) ->
    psub (plift e1) (plift e2) ->
    psub (plift k1) (plift k2) ->
    psub (plift q2) (pdom env) ->
    psub (plift e2) (pdom env) ->
    psub (plift k2) (pdom env) ->
    has_type env y T p q2 e2 k2
.


(* store typing: type + qual (list of store locs) *)

Definition stty := list ((vl -> Prop) * pl). 


(* NOTE: the definitions below could be defined as computable Fixpoint 
   but it would take some effort to convince Coq of termination. 
   Since we're recursing on vl, tm, and (list vl) simultaneously, 
   Coq would require these three types to be defined jointly to 
   recognize structural recursion across them. Other options would
   include custom size measures or a well-foundedness predicate.

   Since this is all rather cumbersome, and termination is evident
   as long as values can't be cyclic, we axiomatize the definition
   of rechability below, without proving termination. *)

Axiom val_locs : stty -> vl -> pl. (* set of store locs for given val *)

Definition var_locs S E x l := exists vx, indexr x E = Some vx /\ val_locs S vx l.

Definition vars_locs S E q l := exists x, q x /\ var_locs S E x l.

Definition loc_locs (S: stty) i l := exists vt q, indexr i S = Some (vt, q) /\ q l.


Axiom val_locs_bool: forall S b,
    val_locs S (vbool b) = pempty.

Axiom val_locs_ref: forall S x,    
    val_locs S (vref x) = por (pone x) (loc_locs S x).

Axiom val_locs_abs: forall S H p t,
    val_locs S (vabs H p t) = vars_locs S H (plift p).


(* An alternative would be to use numeric depth bounds -- this
   us some of the way to step-indexed logical relations *)

Fixpoint val_locsn (n: nat) (M: stor) (v: vl) {struct n}: pl := (* set of store locs for given val *)
  match n with
  | 0 => pempty (* pdom M? *)
  | S n =>
      let var_locsn n S E x l :=
        exists vx, indexr x E = Some vx /\ val_locsn n S vx l in 
      let vars_locs n S E q l :=
        exists x, q x /\ var_locsn n S E x l in
      let loc_locs n S i l :=
        exists vy, indexr i S = Some (Some vy) /\ val_locsn n S vy l in
      match v with
      | vbool b => pempty
      | vref x => por (pone x) (loc_locs n M x)
      | vabs H p t => vars_locs n M H (plift p)
      end
  end.


(* NOTE: with nested refs the termination story is a priori less
   clear. But we rely on the fact that references are immutable,
   so store entries can only point to *previous* locations in
   the store. *)


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
            | (M', Some (Some vx)) => ((Some vx)::M', Some (Some (vref (length M'))))
          end
        | tget ex    =>
          match teval n M env ex with
            | (M', None) => (M', None)
            | (M', Some None) => (M', Some None)
            | (M', Some (Some (vbool _))) => (M', Some None)
            | (M', Some (Some (vabs _ _ _))) => (M', Some None)
            | (M', Some (Some (vref x))) =>
              match indexr x M' with
                | Some (Some v) => (M', Some (Some v))
                | _ => (M', Some None)
              end
          end
        | tfree ex    =>
          match teval n M env ex with
            | (M', None) => (M', None)
            | (M', Some None) => (M', Some None)
            | (M', Some (Some (vbool _))) => (M', Some None)
            | (M', Some (Some (vabs _ _ _))) => (M', Some None)
          (*| (M', Some (Some (vref x))) => (update M' x None, Some (Some (vref x)))*)
            | (M', Some (Some (vref x))) => (update M' x None, Some (Some (vbool false)))
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
Definition tevaln S env e S' v :=
  exists nm,
  forall n,
    n > nm ->
    teval n S env e = (S', Some (Some v)).



(* store typings *)

Definition store_type (S: stor) (M: stty) (K: pl) :=
  length S = length M /\
    psub K (pdom M) /\
    forall l vt qt,
      indexr l M = Some (vt, qt) ->
      psub qt (pdom M) /\
      (K l \/
        exists v,
          indexr l S = Some (Some v) /\
            vt v /\ psub (val_locs M v) qt). (* XX check q? *)

(* value interpretation of types *)

Fixpoint val_type (M:stty) (H:venv) v T : Prop :=
  match v, T with
  | vbool b, TBool =>
      True
  | vref l, TRef T => (* restrict to TRef TBool ? *)
      closed_ty (length H) T /\
      exists vt q,
        indexr l M = Some (vt, q) /\
          (forall vx,
              vt vx ->
              val_type M H vx T) /\
          (psub q (pdom M))
  | vabs G py ty, TFun T1 (* qempty *) T2 q2 e2 k2 q2x e2x k2x => (* TODO! *)
      closed_ty (length H) T1 /\
        closed_ty (length H) T2 /\
        (psub (plift q2) (pdom H)) /\
        (psub (plift e2) (pdom H)) /\
        (psub (plift k2) (pdom H)) /\
        (psub (val_locs M v) (pdom M)) /\
        (forall S' M' K' vx,
            store_type S' (M'++M) K'
            ->
            val_type
              (M'++M)
              H
              vx
              T1
            ->
              psub (pand (val_locs (M'++M) v) (val_locs (M'++M) vx)) pempty
            ->
              psub
                (pand K'
                   (por (vars_locs (M'++M) H (plift e2))
                      (if e2x then (val_locs (M'++M) vx) else pempty)))
                pempty
            ->
              exists S'' M'' vy,
                tevaln
                  S'
                  (vx::G)
                  ty
                  S''
                  vy
                /\
                  store_type S'' (M''++M'++M)
                    (por K'
                       (por (vars_locs (M''++M'++M) H (plift k2))
                          (por (if k2x then (val_locs (M''++M'++M) vx) else pempty)  
                             (pdiff (pdiff (pdom (M''++M'++M)) (pdom (M'++M))) (val_locs (M''++M'++M) vy)))))
                /\
                  val_type
                    (M''++M'++M)
                    H
                    vy
                    T2
                /\
                  psub
                    (pand (pdom (M'++M)) (val_locs (M''++M'++M) vy))
                    (por (pand (vars_locs (M''++M'++M) H (plift q2)) (val_locs (M''++M'++M) v))
                       (if q2x then (val_locs (M''++M'++M) vx) else pempty)))
  | _,_ =>
      False
  end.


Definition val_qual (M M1: stty) H v p (q: pl) :=
  psub (pand (pdom M) (val_locs M1 v)) (vars_locs M1 H (pand p q)).



Definition exp_type S M K H t S' M' v T p q (e: pl) (k: pl) :=
  tevaln S H t S' v /\
    store_type S' (M'++M) (por K
                             (por (vars_locs (M'++M) H (pand p k))
                                (pdiff (pdiff (pdom (M'++M)) (pdom M))
                                       (val_locs (M'++M) v)))) /\ 
    val_type (M'++M) H v T /\
    val_qual M (M'++M) H v p q.

(* kill set after evaluating t to v is the union of:
   - previous cumulative kill set K
   - existing observable locations mentioned by t's effect annotation k (i.e., p /\ k)
   - fresh locations allocated during evaluation of t that aren't reachable from result v
 *)
   



(* what to do to check e,k ? restrict store? *)


Definition env_type M H G p :=
  length H = length G /\
    psub p (pdom H) /\
    (forall x T,
        indexr x G = Some T ->
        exists v : vl,
          indexr x H = Some v /\
            val_type M H v T) /\
    (forall l x0 x1,
        p x0 ->
        var_locs M H x0 l ->
        p x1 ->
        var_locs M H x1 l ->
        x0 = x1).



#[global] Hint Constructors ty.
#[global] Hint Constructors tm.
#[global] Hint Constructors vl.


#[global] Hint Constructors has_type.

#[global] Hint Constructors option.
#[global] Hint Constructors list.


(* ---------- qualifier reflection & tactics  ---------- *)


Ltac unfoldq := unfold val_qual, psub, pdom, pand, por, pdiff, pempty, pone, var_locs, vars_locs in *.
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

Lemma plift_if: forall a b (c: bool),
    plift (if c then a else b) = if c then plift a else plift b.
Proof.
  intros. unfoldq. unfold plift.
  eapply functional_extensionality. intros.
  eapply propositional_extensionality.
  destruct c; intuition.
Qed.


Lemma por_assoc: forall (a b c: pl),
    por (por a b) c = por a (por b c).
Proof.
  intros. eapply functional_extensionality.
  intros. eapply propositional_extensionality.
  unfoldq. intuition.
Qed.

Lemma pand_dist_or: forall p e q,
    (pand (p) (por (e) (q))) =
      (por (pand (p) (e)) (pand (p) (q))).
Proof.
  intros. eapply functional_extensionality.
  intros. eapply propositional_extensionality.
  unfoldq. intuition.
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
    eapply closedq_extend; eauto.
Qed.

(* ---------- val locs and var locs lemmas  ---------- *)


(* we assume this as an axiom (we don't currently have
   a suitable size measure on values), but we still show
   how to prove the relevant cases: *)

Axiom val_locs_extend: forall M M' v,
    psub (val_locs M v) (pdom M) ->
    val_locs M v = val_locs (M'++M) v.


Lemma val_locs_extend_proof: forall M M' v,
    psub (val_locs M v) (pdom M) ->
    val_locs (M'++M) v = val_locs M v.
Proof.
  intros. apply functional_extensionality.
  intros. apply propositional_extensionality.
  destruct v.
  - repeat rewrite val_locs_bool in *. intuition.
  - repeat rewrite val_locs_ref in *.
    assert (i < length M). eapply (H i). unfoldq. intuition.
    intuition.
    + destruct H1. left. eauto. right.
      unfold loc_locs.  unfold loc_locs in H1.
      destruct H1 as [vt [qt [? ?]]].
      exists vt, qt. intuition.
      rewrite indexr_extend. intuition. eapply H1.
    + destruct H1. left. eauto. right.
      unfold loc_locs.  unfold loc_locs in H1.
      destruct H1 as [vt [qt [? ?]]].
      exists vt, qt. intuition.
      rewrite indexr_extend in H1. eapply H1.
  - (* app case: recursion *)
    rewrite <-val_locs_extend. intuition. eauto. 
Qed.
    

Lemma vars_locs_extend: forall M H H' q,
    psub q (pdom H) ->
    vars_locs M (H' ++ H) q = 
      vars_locs M H q.
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


Lemma var_locs_store_extend: forall M M' H x,
    psub (var_locs M H x) (pdom M) ->
    var_locs M H x = var_locs (M'++M) H x.
Proof.
  intros. apply functional_extensionality.
  intros. apply propositional_extensionality.
  unfoldq. unfoldq. intuition.
  - destruct H1. exists x1. intuition.
    rewrite <-val_locs_extend. eauto.
    unfoldq. intuition. eapply H0. exists x1. intuition.
  - destruct H1. exists x1. intuition.
    rewrite <-val_locs_extend in H3. eauto.
    unfoldq. intuition. eapply H0. exists x1. intuition.
Qed.


Lemma vars_locs_dist_or: forall M E a b,
    vars_locs M E (por a b) = por (vars_locs M E a) (vars_locs M E b).
Proof.
  intros. apply functional_extensionality.
  intros. apply propositional_extensionality.
  unfoldq. split; intros. 
  - destruct H as [x0 [? [vx [? ?]]]]. destruct H.
    left. exists x0. intuition. exists vx. intuition.
    right. exists x0. intuition. exists vx. intuition.
  - destruct H; destruct H as [x0 [? ?]].
    exists x0. intuition.
    exists x0. intuition.
Qed.



(* Obligation for nested references *)

Lemma val_locs_nested: forall S M K i x vx vt qt,
    store_type S M K ->
    ~ K i ->
    indexr i S = Some (Some vx) ->
    indexr i M = Some (vt, qt) ->
    val_locs M vx x ->
    val_locs M (vref i) x.
Proof.
  intros. rewrite val_locs_ref. right.
  exists vt. exists qt. intuition.
  destruct H as [? [? ?]].
  eapply H5 in H2. destruct H2. destruct H6. eapply H0 in H6. contradiction. 
  destruct H6. destruct H6. destruct H7. eapply H8.
  congruence.
Qed.



(* ---------- val_type lemmas  ---------- *)

Lemma valt_wf: forall T M H v,
    val_type M H v T ->
    psub (val_locs M v) (pdom M).
Proof. 
  intros T. induction T; intros; destruct v; simpl in *; intuition.
  + rewrite val_locs_bool. auto. unfoldq. intuition.
  + rewrite val_locs_ref.
    destruct H2 as [vt [qt [IX VALX]]].
    unfoldq. unfold loc_locs. intuition. subst x.
    eapply indexr_extend with (H':=[]) in IX. eapply IX.
    destruct H4 as [? [? [? ?]]].
    rewrite IX in H3. inversion H3. subst.
    eapply H2 in H4. eauto.
Qed.

Lemma valt_closed: forall T M H v,
    val_type M H v T ->
    closed_ty (length H) T.
Proof. 
  intros T. induction T; intros; destruct v; simpl in *; intuition.
  + econstructor.
  + econstructor; eauto. 
  + econstructor; eauto. 
Qed.

Lemma valt_store_extend: forall T M' M H v,
    val_type M H v T ->
    val_type (M'++M) H v T.
Proof.  
  intros T. induction T; intros; destruct v; simpl in *; intuition.
  + destruct H2 as [vt [qt [IX VX]]].
    exists vt, qt. intuition. eapply indexr_extend in IX; intuition. eauto.
    unfoldq. intuition. rewrite app_length. eapply H2 in H3. lia.
  + unfoldq. intuition. rewrite <-val_locs_extend in H6. eapply H5 in H6. rewrite app_length. lia. eauto.
  + destruct (H7 S' (M'0++M') K' vx) as [S'' [M'' [vy  [IEY [ST [HVY HSEP]]]]]]. 
    rewrite <-app_assoc. auto.
    rewrite <-app_assoc. auto.
    rewrite <-app_assoc. auto.
    rewrite <-app_assoc. auto.
    exists S'', M''. exists vy. intuition.
    repeat erewrite <- app_assoc in ST; eauto.
    repeat erewrite <- app_assoc in HVY; eauto.
    repeat erewrite <- app_assoc in HSEP; eauto. 
Qed. 


Lemma valt_extend: forall T M H' H v,
    closed_ty (length H) T ->
    val_type M (H'++H) v T <-> val_type M H v T.
Proof.
  intros T. induction T; split; intros; destruct v; simpl in *; intuition.
  - inversion H0. auto.
  - (* Ref shrink *)
    destruct H3 as [vt [qt [IX HVX]]].
    exists vt, qt. intuition.
    eapply IHT; eauto. inversion H0. auto.
  - eapply closedty_extend; eauto.
  - (* Ref grow *)
    destruct H3 as [vt [qt  [IX HVX]]].
    exists vt, qt. intuition.
    eapply IHT; eauto. 
  - inversion H0. auto.
  - inversion H0. auto.
  - inversion H0. auto.
  - inversion H0. auto.
  - inversion H0. auto.    
  - (* Abs shrink *)
    inversion H0. subst.
(*    rename q into q2.  *)
    destruct (H8 S' M' K' vx) as [S'' [M'' [vy [HEY HVY]]]].
      eauto.
      eapply IHT1; eauto.
      eauto.
      rewrite vars_locs_extend. eauto. eauto. eauto.
    exists S'', M'', vy. intuition.
    rewrite vars_locs_extend in H12.
    eauto. eauto.
    eapply IHT2; eauto.
    rewrite vars_locs_extend in H15.
    eauto. eauto.
  - eapply closedty_extend; eauto.
  - eapply closedty_extend; eauto.
  - unfoldq. rewrite app_length. intuition. eapply H3 in H7. lia.
  - unfoldq. rewrite app_length. intuition. eapply H4 in H7. lia.
  - unfoldq. rewrite app_length. intuition. eapply H5 in H7. lia.
  - (* Abs grow *)
    inversion H0. subst.
(*    rename q into q2. *)
    destruct (H8 S' M' K' vx) as [S'' [M'' [vy [HEY [HVY HQY]]]]].
      eauto.
      eapply IHT1; eauto.
      eauto.
      rewrite vars_locs_extend in H11. eauto. eauto. eauto.
    exists S'', M'', vy. intuition.
    rewrite vars_locs_extend.
    eauto. eauto.
    eapply IHT2; eauto.
    rewrite vars_locs_extend. 
    eauto. eauto.
Qed.


Lemma valt_extend1: forall T M H v vx,
    closed_ty (length H) T ->
    val_type M (vx::H) v T <-> val_type M H v T.
Proof.
  intros. replace (vx :: H)  with ([vx]  ++ H); auto.
  eapply valt_extend; eauto.
Qed.


(* ---------- val_qual lemmas  ---------- *)

Lemma valq_bool: forall M M1 H b p q,
    val_qual M M1 H (vbool b) p q.
Proof.
  intros. unfoldq. rewrite val_locs_bool. intuition.
Qed.

(*
Lemma valq_fresh: forall M M' H p q,
    val_qual M H (vref (length (M' ++ M))) p q.
Proof.
  intros. unfoldq.
  (* valq: index out of range*)
  rewrite app_length.
  rewrite val_locs_ref.
  intuition. unfoldq. lia.
Qed.*)

Lemma valq_deref: forall S1 M M1 K E i p q vx vt qt,
    store_type S1 (M1 ++ M) K ->
    ~ K i ->
    indexr i S1 = Some (Some vx) ->
    indexr i (M1 ++ M) = Some (vt, qt) ->
    val_qual M (M1 ++ M) E (vref i) (plift p) (plift q) ->
    val_qual M (M1 ++ M) E vx (plift p) (plift q).
Proof.
  intros. 
  (* val qual: deref *)
  unfoldq. intros. eapply H3. intuition.
  eapply val_locs_nested; eauto.
  (*
  rewrite val_locs_ref. right.
  unfold loc_locs.
  destruct H.
  exists vt, qt. intuition.
  *)
Qed.


Lemma valq_abs: forall M M1 H t p q,
    val_qual M M1 H (vabs H (qand p q) t) (plift p) (plift q).
Proof.
  intros. unfoldq.
  rewrite val_locs_abs.
  rewrite plift_and.
  intuition. 
Qed.


Lemma valq_sub: forall M M1 H v p q q',
    val_qual M M1 H v p q ->
    psub q q' ->
    psub q' (pdom H) ->
    val_qual M M1 H v p q'.
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

Lemma aux1: forall v M H l,
  var_locs M (v :: H) (length H) l ->
  val_locs M v l.
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


Lemma var_locs_shrink: forall v M H x l,
  var_locs M (v::H) x l ->
  x < length H ->
  var_locs M H x l.
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
    (forall x l, val_locs M v l -> p x -> var_locs M H x l -> False) ->
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
    + destruct (H6 _ _ H0); eauto.
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

(* we have this below for sets of vars as env_type_store_wf *)
Lemma aux2: forall M H G p x,
    env_type M H G p ->
    p x ->
    psub (var_locs M H x) (pdom M).
Proof.
  intros. destruct H0 as [L [P W]].
  unfoldq. intuition.
  assert (exists T, indexr x G = Some T).
  eapply indexr_var_some. rewrite <-L. eauto.
  destruct H4. 
  destruct (H0 x x1); eauto.
  destruct H5. destruct H3. destruct H3. rewrite H3 in H5. inversion H5. subst x3.
  eapply valt_wf; eauto. 
Qed.

Lemma envt_store_extend: forall M M' H G p,
    env_type M H G p ->
    env_type (M'++M) H G p.
Proof.
  intros. remember H0 as WFE1. destruct H0 as [L [P W]]. 
  repeat split; auto. intros.
  destruct W as [W W'].
  destruct (W _ _  H0) as [vx [IH HVX]]; intuition.
  exists vx; intuition.
  eapply valt_store_extend in HVX; eauto.
  intros.
  destruct W as [W' W].
  rewrite <-var_locs_store_extend in H1, H3.
  destruct (W l x0 x1); intuition. 
  eapply aux2; eauto.
  eapply aux2; eauto.
Qed.


Lemma envt_extend_all: forall M M1 H G vx T1 p q1 qf,
    env_type M H G p ->
    val_type (M1 ++ M) H vx T1 ->
    psub (pand (vars_locs (M1++M) H (pand p qf)) (val_locs (M1++M) vx)) pempty ->
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
    psub (vars_locs M H q) (pdom M).
Proof.
  intros. destruct H0 as [L [P [W1 W2]]]; intuition.
  unfoldq. intuition.
  destruct H0 as [? [? ?]].
  assert (x0 < length H). destruct H1. eapply indexr_extend. 2: eapply H1. eauto.
  rewrite L in H2. eapply indexr_var_some in H2. destruct H2. 
  destruct (W1 x0 x1 H2).
  destruct H1. 
  eapply valt_wf. eapply H3. destruct H1. destruct H3. congruence.
Qed.

Lemma envt_var_store_wf: forall M H G p x,
    env_type M H G p ->
    psub (var_locs M H x) (pdom M).
Proof.
  intros. intros ? ?. eapply env_type_store_wf with (q:=pone x). eauto.
  unfoldq. exists x. intuition.
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
    pand (vars_locs M E q) (vars_locs M E q') = vars_locs M E (pand q q').
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


Lemma separation: forall M M' M'' H G TF TX p vf vx qf q1
    (WFE: env_type M H G p)
    (HVF: val_type (M'++M) H vf TF)
    (HVX: val_type (M''++M'++M) H vx TX)
    (HQF: val_qual M (M'++M) H vf p qf)
    (HQX: val_qual (M'++M) (M''++M'++M) H vx p q1),
    psub (val_locs (M'++M) vf) (pdom (M'++M)) ->
    psub (pand qf q1) pempty ->
    psub (pand (val_locs (M''++M'++M) vf) (val_locs (M''++M'++M) vx)) pempty.
Proof. 
  intros. unfoldq. intuition.
  remember WFE as WFE1. clear HeqWFE1.
  assert (env_type (M''++M'++M) H G p) as WFE2.
  rewrite app_assoc. eapply envt_store_extend. eauto.
  destruct WFE2 as [? [? [? SEP]]].
  bdestruct (x <? length M).
  - destruct (HQF x). intuition. rewrite <-val_locs_extend in H3. eauto. eapply valt_wf. eauto.
    destruct (HQX x). rewrite app_length. intuition.
    assert (x0 = x1). eapply SEP; intuition; eauto.
    rewrite <-var_locs_store_extend. eauto. eapply aux2. eapply envt_store_extend. eauto. eauto.
    eapply H1. subst x0. intuition; eauto.
  - bdestruct (x <? length (M'++M)).
    + destruct (HQX x). intuition.
      (* fresh loc in vf, also occurs in vx --> can't happen *)
      assert (psub (var_locs (M''++M'++M) H x0) (pdom M)) as L. {
        rewrite app_assoc. rewrite <-var_locs_store_extend. 
        eapply aux2. eauto. eapply H9.
        eapply aux2. eauto. eapply H9.
      }
      assert (x < length M). {
        eapply L. unfoldq. intuition.
      }
      lia.
    + (* fresh loc in vx, bigger than vf *)
      rewrite <-val_locs_extend in H3. 2: eapply valt_wf; eauto.
      assert (x < length (M'++M)). eauto. lia.
Qed.



(* ---------- store typing lemmas ---------- *)


Lemma storet_length: forall S M K,
    store_type S M K ->
    length S = length M.
Proof.
  intros. eapply H.
Qed.

Lemma storet_extend: forall S M K vx (vt: vl -> Prop) qt,
    store_type S M K ->
    vt vx ->
    psub qt (pdom M) ->
    psub (val_locs M vx) qt ->
    store_type ((Some vx) :: S) ((vt, qt) :: M) K. (* XXX *)
Proof.
  intros.
  unfold store_type in *. split. simpl. intuition. split. unfoldq. simpl. intuition.
  intros.
  bdestruct (l =? length M).
  - subst l. simpl in *.
    bdestruct (length M =? length S); intuition.
    bdestruct (length M =? length M); intuition.
    inversion H3. subst vt qt. unfoldq. simpl. intuition.

    bdestruct (length M =? length M); intuition.
    right. eexists. intuition.
    inversion H3. subst vt qt. eauto.
    inversion H3. subst vt qt. unfoldq. intuition.
    replace (((vt0, qt0) :: M)) with ([(vt0,qt0)]++M) in H8. 2: simpl; eauto.
    rewrite <-val_locs_extend in H8. eapply H2. eauto.
    unfoldq. intuition. 
  - rewrite indexr_skip in H3; eauto.
    rewrite indexr_skip. 2: lia.
    destruct H as [? [? ?]]. destruct (H6 l vt0 qt0).
    eauto. intuition. unfoldq. intuition. simpl.
    eapply H7 in H8. lia.
    unfoldq. intuition. simpl.
    eapply H7 in H8. lia. 
    right.
    destruct H9. 
    eexists x. intuition.
    replace (((vt, qt) :: M)) with ([(vt,qt)]++M). 2: simpl; eauto.
    rewrite <-val_locs_extend. eauto.
    unfoldq. intuition.
Qed.


Lemma storet_free: forall S M K i,
    store_type S M K ->
    K i ->
    store_type (update S i None) M K.
Proof.
  intros.
  unfold store_type in *. intuition.
  rewrite <-update_length. eauto.
  destruct (H3 l vt qt); eauto.
  bdestruct (i =? l).
  - subst i. intuition.
  - rewrite update_indexr_miss. eapply H3. eauto. eauto. 
Qed.

Lemma storet_restrict: forall S M K K',
    store_type S M K ->
    psub K K' ->
    psub K' (pdom M) ->
    store_type S M K'.
Proof.
  intros.
  unfold store_type in *. intuition.
  destruct (H4 l vt qt); intuition.
  destruct (H4 l vt qt); intuition.
Qed.

Lemma storet_restrict2: forall S M K G H p q v,
    env_type M H G p ->
    store_type S M K ->
    psub q (pdom H) ->
    store_type S M (por K (por (vars_locs M H q) (pdiff (pdiff (pdom M) (pdom M)) (val_locs M v)))).
Proof.
  intros.
  eapply storet_restrict. eauto.
  unfoldq. intuition.
  unfoldq. intuition. destruct H1. destruct H3. eapply H3. eauto.
  destruct H3. destruct H3. 
  eapply envt_var_store_wf; eauto.
Qed.




(* ---------- main lemmas ---------- *)

Lemma sem_app1: forall S'' M M' M'' K'' H Hf G T1 T2 ey vx pv p q1 q2 qf e2 k2 q2x e2x k2x
    (WFE: env_type M H G p)
    (HVF: val_type (M'++M) H (vabs Hf pv ey) (TFun T1 T2 q2 e2 k2 q2x e2x k2x))
    (HQF: val_qual M (M'++M) H (vabs Hf pv ey) p qf)
    (HVX: val_type (M''++M'++M) H vx T1)
    (HQX: val_qual (M'++M) (M''++M'++M) H vx p q1),
    psub (pand qf q1) pempty ->
    psub (plift q2) p  -> 
    (* exists vy, exp_type H ey vy T2 p q2. *) (* not exactly this!! *)
    psub (pand K''
            (por (vars_locs (M''++M'++M) H (plift e2))
               (if e2x then (val_locs (M''++M'++M) vx) else pempty))) pempty ->
    store_type S'' (M''++M'++M) K'' ->
    exists S''' M''' vy,
      tevaln S'' (vx::Hf) ey S''' vy /\
        store_type S''' (M'''++M''++M'++M)
          (por K''
             (por (vars_locs (M'''++M''++M'++M) H (plift k2))
                (por (if k2x then (val_locs (M'''++M''++M'++M) vx) else pempty)
                   (pdiff (pdiff (pdom (M'''++M''++M'++M)) (pdom (M''++M'++M))) (val_locs (M'''++M''++M'++M) vy))) )) /\ 
        val_type (M'''++M''++M'++M) H vy T2 /\
        val_qual M (M'''++M''++M'++M) H vy p (por (plift q2) (if q2x then q1 else pempty)) /\
        psub
          (pand (pdom (M''++M'++M)) (val_locs (M'''++M''++M'++M) vy))
          (por (val_locs (M'''++M''++M'++M) (vabs Hf pv ey))
             (if q2x then (val_locs (M'''++M''++M'++M) vx) else pempty)).
Proof.
  
  intros. remember HVF as HVF2. clear HeqHVF2.
  apply valt_wf in HVF as WFQF. apply valt_wf in HVX as WFQX.
  destruct HVF; intuition.
  rename H11 into HVF. 
  destruct (HVF S'' M'' K'' vx) as [S''' [M''' [vy [IW3 HVY]]]].
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

  (* TODO 2a: EFFECT SEPARATION *)
  eauto. eauto.
  
  (* TODO 3: VAL_TYPE *)
  
  (* go from 
        T2 (qand p qf) (qand p (qand qf q2))
     to
        T2 p (qor q2 q1)
  *)

  exists S''', M''', vy. intuition.

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


  {
  rename H13 into HQY.
  remember (vabs Hf pv ey) as vf.
  unfold val_qual in *.
  
  unfoldq. intros. 
  destruct (HQY x). repeat rewrite app_length. intuition.
  + (* part of function *)
    destruct (HQF x). intuition. { (* shrink vf *)
      rewrite app_assoc in H16.
      rewrite <-val_locs_extend in H16. eauto. eauto. }
    destruct H13. destruct H13.
    exists x1. intuition.
    
  + (* part of argument *)
    destruct q2x; try contradiction.
    destruct (HQX x). repeat rewrite app_length. intuition. { (* shrink vx *)
      rewrite <-val_locs_extend in H13. eauto. eauto. }
    
    exists x0. intuition. { (* extend x0 *)
      rewrite <-var_locs_store_extend. eauto.
      eapply aux2. rewrite app_assoc. eapply envt_store_extend; eauto. eauto. }
  }

  unfoldq. intuition. destruct (H13 x) as [[x0 ?] [? ?]|]; eauto. 
  
Qed.



Lemma sem_abs1: forall S M M1 K H G T1 T2 t vx p q2 qf e2 k2 (q2x e2x k2x: bool)
    (WFE: env_type M H G (plift p))
    (HVX: val_type (M1 ++ M) H vx T1) (* arg from valt *)
    (SEP : psub (pand (val_locs (M1++M) (vabs H (qand p qf) t)) (val_locs (M1++M) vx)) pempty)
    (IHW : (* induction *)
        env_type (M1 ++ M) (vx :: H) (T1 :: G) (plift (qor (qand p qf) (qone (length H)))) ->
        exists (S'' : stor) (M'' : stty) (vy : vl),
          exp_type S (M1 ++ M) K (vx :: H) t S'' M'' vy T2 (plift (qor (qand p qf) (qone (length H))))
            (plift (qor q2 (if q2x then (qone (length H)) else qempty)))
            (plift (qor e2 (if e2x then (qone (length H)) else qempty)))
            (plift (qor k2 (if k2x then (qone (length H)) else qempty))))
    (HCLT1: closed_ty (length H) T1)        
    (HCLT2: closed_ty (length H) T2)
    (HCLQ:  closed_ql (length H) (qand p qf))
    (HCLK:  closed_ql (length H) k2)
    (HCLQ2:  closed_ql (length H) q2)
    (STY:   store_type S (M1 ++M) K),
  exists (S'' : stor) (M'' : stty) (vy : vl),
    tevaln S (vx :: H) t S'' vy /\
      store_type S'' (M'' ++ M1 ++ M)
        (por K
           (por (vars_locs (M''++M1++M) H (plift k2))
              (por (if k2x then (val_locs (M''++M1++M) vx) else pempty)
                 (pdiff (pdiff (pdom (M''++M1++M)) (pdom (M1++M))) (val_locs (M''++M1++M) vy) )))) /\  (* !!! TODO: add M''++M1 - locs vy !!! *)
      val_type (M'' ++ M1 ++ M) H vy T2 /\
      psub (pand (pdom (M1 ++ M)) (val_locs (M''++M1++M) vy))
        (por (pand (vars_locs (M''++M1++M) H (plift q2)) (val_locs (M''++M1++M) (vabs H (qand p qf) t)))
           (if q2x then (val_locs (M''++M1++M) vx) else pempty)).
Proof.
  intros.
  destruct (IHW) as [S2 [M2 [vy IHW1]]]. {
    rewrite val_locs_abs, plift_and in SEP.
    rewrite plift_or, plift_and, plift_one.
    eapply envt_extend_all; eauto.
  }
  destruct IHW1 as [? IHW1]. 
  exists S2, M2, vy. intuition.

  eapply storet_restrict. eauto.
  unfoldq. intros. destruct H2 as [?|[?|?]].
  left. eauto.
  
  destruct H2. destruct H2. rewrite plift_or, plift_and, plift_one in H2. destruct H2. unfoldq.
  bdestruct (x0 =? length H).
  destruct k2x. subst x0.
  rewrite plift_or, plift_one in H6. unfoldq. destruct H6. eauto. eapply HCLK in H6. lia.
  right. right.
  destruct H5. destruct H5. rewrite indexr_head in H5; eauto. inversion H5. subst x0.
  intuition.
  (* k2x = false *)
  subst x0. rewrite plift_or, plift_empty in H6. destruct H6. eapply HCLK in H6. lia. unfoldq. contradiction.
  (* x0 <> length H *)
  destruct H2. 2: lia.
  right. left. exists x0. rewrite plift_or in H6. destruct H6. intuition. destruct H5. eexists x1. intuition. rewrite indexr_skip in H5. eauto. lia.
  destruct k2x. rewrite plift_one in H6. unfoldq. lia. rewrite plift_empty in H6. unfoldq. contradiction.

  right. right. right. eauto. 

  
  unfoldq. intros. destruct H2 as [H_K|[H_k2|[H_k2x|H_fresh]]].
  (* K *) destruct H1 as [? [KL ?]].
  eapply KL. left. eapply H_K. 
  (* k2 *) destruct H_k2. destruct H2.
  eapply envt_var_store_wf. eapply envt_store_extend. eapply envt_store_extend. eauto. eapply H5. 
  (* k2x *) destruct k2x. eauto. 
  eapply valt_wf. eapply valt_store_extend. eauto. eauto. contradiction.
  (* fresh *) eapply H_fresh. 

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
  apply valt_wf in HVX. apply valt_wf in H3.
  rename H4 into HVY.
  
  unfoldq. intuition.
  destruct (HVY x). eauto.
  rewrite plift_or, plift_and, plift_one in H2.
  rewrite plift_or in H2.
  unfoldq.
  destruct H2. destruct H2.
  destruct q2x. rewrite plift_one in H7.
  bdestruct (x0 =? length H).
  - (* from arg *)
    right. destruct H6 as [? [? ?]]. subst x0. rewrite indexr_head in H6. inversion H6. eauto.
  - (* from func *)
    left. split.
    exists x0. intuition. destruct H6 as [? [? ?]]. rewrite indexr_skip in H6. exists x1. split; eauto. lia.
    exists x0. rewrite plift_and. split.
    destruct H2; try lia. eapply H2.
    destruct H6 as [? [? ?]]. rewrite indexr_skip in H6; eauto.

  (* q2x is false, hence can't be arg *)
  - destruct H7.
    2: { rewrite plift_empty in H7. unfoldq. contradiction. }
    assert (x0 < length H). { eapply HCLQ2 in H7. eauto. }
    left. split.
    exists x0. intuition. destruct H6 as [? [? ?]]. rewrite indexr_skip in H6. exists x1. split; eauto. lia.
    exists x0. rewrite plift_and. split.
    destruct H2; try lia. eapply H2.
    destruct H6 as [? [? ?]]. rewrite indexr_skip in H6; eauto. lia.

Qed.


Lemma var_locs_store_extend0: forall M M1 H G x p,
    env_type M H G p ->
    p x -> 
    var_locs M H x = var_locs (M1++M) H x.
Proof.
  intros. eapply var_locs_store_extend.
  eapply aux2. eauto. eauto. 
Qed.

Lemma var_locs_store_extend1: forall M H G x p vt qt,
    env_type M H G p ->
    p x -> 
    var_locs M H x = var_locs ((vt,qt)::M) H x.
Proof.
  intros. rewrite var_locs_store_extend with (M' := [(vt,qt)]).
  intuition.
  eapply aux2. eauto. eauto. 
Qed.

Lemma vars_locs_store_extend: forall M M1 H G p q,
    env_type M H G p ->
    psub q p -> 
    vars_locs M H q = vars_locs (M1++M) H q.
Proof.
  intros. eapply functional_extensionality.
  intros. eapply propositional_extensionality.
  unfoldq. intuition.
  destruct H2 as [? [? ?]]. exists x0. rewrite <-var_locs_store_extend0 with (G:=G) (p:=p); eauto.
    destruct H2 as [? [? ?]]. exists x0. rewrite <-var_locs_store_extend0 with (G:=G) (p:=p) in H3; eauto. 
Qed.

Lemma vars_locs_store_extend1: forall M H G p q vt qt,
    env_type M H G p ->
    psub q p -> 
    vars_locs M H q = vars_locs ((vt,qt)::M) H q.
Proof.
  intros. eapply functional_extensionality.
  intros. eapply propositional_extensionality.
  unfoldq. intuition.
  destruct H2 as [? [? ?]]. exists x0. rewrite <-var_locs_store_extend1 with (G:=G) (p:=p); eauto.
    destruct H2 as [? [? ?]]. exists x0. rewrite <-var_locs_store_extend1 with (G:=G) (p:=p) in H3; eauto. 
Qed.
  

Lemma app_cons {A : Type} (x: A) (l1 : list A) :
  x::l1 = [x] ++ l1.
Proof.
  simpl. eauto. 
Qed.

Lemma app_length2 {A : Type} (x: nat) (l1 l2 : list A) :
  x < length l2 ->
  x < length (l1 ++ l2).
Proof.
  rewrite app_length. lia. 
Qed.




(* if well-typed, then result is an actual value (not stuck and not a timeout),
   for large enough n *)

Theorem full_total_safety : forall t G T p q e k,
    has_type G t T p q e k ->
    forall M E, env_type M E G (plift p) ->
    forall S K, store_type S M K ->
    psub (pand K (vars_locs M E (pand (plift p) (plift e)))) pempty ->
    exists S' M' v, exp_type S M K E t S' M' v T (plift p) (plift q) (plift e) (plift k).
Proof.
  intros ? ? ? ? ? ? ? W. 
  induction W; intros ? ? WFE; 
  destruct (wf_env_type M E env (plift p) WFE) as [LE [DE PC]]; intuition. 
  
  - (* Case "True". *) exists S. exists []. exists (vbool true). split.
    exists 0. intros. destruct n. lia. intuition. simpl. intuition.
    eapply storet_restrict2; eauto. unfoldq. intuition.
    eapply valq_bool.
    
  - (* Case "False". *) exists S. exists []. eexists. split.
    exists 0. intros. destruct n. lia. intuition. simpl. intuition. 
    eapply storet_restrict2; eauto. unfoldq. intuition.
    eapply valq_bool.
    
  - (* Case "Var". *)
    destruct WFE as [? [? [WFE ?]]].
    destruct (WFE x T H) as [vx [HI ?]]. eauto.
    exists S. exists []. eexists. 
    split. exists 0. intros. destruct n. lia. simpl. rewrite HI. reflexivity.
    intuition. simpl. 
    eapply storet_restrict2; eauto. econstructor; eauto. unfoldq. intuition.
    
    (* valq *)
    unfoldq. rewrite plift_one.
    unfoldq. intuition.
    exists x. intuition.
    exists vx. intuition.
    
  - (* Case "Ref". *)
    destruct (IHW M E WFE S K) as [S1 [M1 [vx [IW1 [ST1 [HVX HQX]]]]]]; eauto.
    remember (fun v => val_type (M1++M) E v T) as vt.
    remember (val_locs (M1 ++ M) vx) as qt.    
    exists (Some vx::S1).
    exists ((vt,qt)::M1).
    exists (vref (length (M1++M))). split.
    + (* expression evaluates *)
      eapply storet_length in ST1.
      destruct IW1 as [n1 IW1].
      rename S into Sx.
      exists (S n1).
      intros. destruct n. lia.
      simpl. rewrite IW1. rewrite ST1. eauto. lia.
    + (* result well typed *)
      split. 2: split. 
      (* store type *) {
        simpl. eapply storet_extend. eapply storet_restrict. eauto.
        
        (* K <: K' *) {
          rewrite val_locs_ref. unfoldq. intros.
          destruct H1 as [HX_K | [HX_k | HX_fresh]].
          (* K *) left. intuition.
          (* k *) right. left.
          destruct HX_k. exists x0. intuition. rewrite <-var_locs_store_extend1 with (G:=env) (p:=plift p). eauto. eapply envt_store_extend; eauto. eauto.
          (* fresh *)
          right. right.
          simpl. split. simpl. intuition.
          intros ?. destruct H1. lia.
          destruct H1 as [vt1 [qt1 [IX ?]]].
          rewrite indexr_head in IX. inversion IX. destruct HX_fresh. congruence.
        }
        
        (* K' <: dom(M1++M) *) {
          rewrite val_locs_ref. unfoldq. intros. 
          destruct H1 as [HX_K | [HX_k | HX_fresh]].
          (* K *) destruct ST1 as [? [KS ?]]. eapply KS. left. eapply HX_K.
          (* k *) eapply env_type_store_wf. eapply envt_store_extend. eauto. destruct HX_k. rewrite <-var_locs_store_extend1 with (G:=env) (p:=plift p) in a; eauto.
          exists x0. eapply a. eapply envt_store_extend. eauto. eapply a.
          (* fresh *) intuition. simpl in H3. lia.
        }
        
        subst. eauto.
        subst. eapply valt_wf. eauto.
        subst. unfoldq. intuition.
      }

      (* val_type *)
      simpl. intuition. eapply valt_closed. eauto.  
      bdestruct (length (M1 ++ M) =? length (M1 ++ M)); intuition.
      exists vt, qt. subst. intuition.
      rewrite app_cons. eapply valt_store_extend. eauto. 
      unfoldq. intuition. rewrite app_cons. eapply app_length2. eapply valt_wf; eauto.
      (* val_qual *)
      (* eapply valq_fresh. *)
      unfoldq. intuition.
      destruct (HQX x). intuition.
      rewrite val_locs_ref in H3. destruct H3.
      unfold pone in H1. rewrite app_length in H1. lia.
      unfold loc_locs in H1. destruct H1 as [vt1 [qt1 [IX ?]]].
      remember ((((vt, qt) :: M1)++M)) as Q. 
      simpl in HeqQ. subst Q. rewrite indexr_head in IX. inversion IX. subst.
      eauto.

      exists x0. intuition. rewrite var_locs_store_extend with (M':=[(vt,qt)]) in H5. eauto.

      unfoldq. intuition. destruct H4 as [vx1 [? ?]]. 
      assert (exists T1, indexr x0 env = Some T1) as TT. eapply indexr_var_some. (* rewrite <-H.*)
      rewrite <-LE. eapply indexr_var_some'. eauto. (* x0 < dom env *)
      destruct TT as [T1 TT].
      destruct WFE as [W1 [W2 [W3 ?]]]. 
      eapply W3 in TT; eauto.
      destruct TT as [vx2 [IX2 VT2]].
      eapply valt_wf in VT2.
      rewrite H4 in IX2. inversion IX2. subst vx2.
      rewrite app_length.
      rewrite <-val_locs_extend in H7; eauto.
      eapply VT2 in H7. unfoldq. lia.


  - (* Case "Get". *)
    destruct (IHW M E WFE S K) as [S1 [M1 [vx [IW1 [ST1 [HVX HQX]]]]]]. eauto.
    rewrite plift_or, pand_dist_or, vars_locs_dist_or in H1.
    unfoldq. intuition. eapply H1; eauto. 

    destruct vx; try solve [inversion HVX]. simpl in HVX.
    destruct (HVX) as [CL [vt [qt [MI [HVX1 HQX1]]]]].
    
    assert (i < length M -> vars_locs (M1++M) E (pand (plift p) (plift q)) i) as IQ. {
      unfoldq. intuition. rewrite val_locs_ref in HQX. destruct (HQX i). intuition. left. intuition.
      unfoldq. unfold not. intros. exists x. intuition.
    }
    assert (~ por K
              (por (vars_locs (M1++M) E (pand (plift p) (plift k)))
                 (pdiff (pdiff (pdom (M1 ++ M)) (pdom M)) (val_locs (M1++M) (vref i))))
      i) as NK. { 
      intros IO. destruct IO as [IO_K | [IO_k | IO_fresh]].
      (* not K *)
      rewrite <-vars_locs_store_extend with (G:=env) (p:=plift p) in IQ; eauto.
      assert (i < length M). { destruct H0 as [? [HK ?]]. eapply HK in IO_K. eauto. }
      rewrite plift_or, pand_dist_or, vars_locs_dist_or in H1.
      eapply IQ in H2. 
      eapply H1. unfoldq. split. eapply IO_K. right. eapply H2. 
      unfoldq. intuition.
      (* not k *)
      rewrite <-vars_locs_store_extend with (G:=env) (p:=plift p) in IO_k; eauto.
      rewrite <-vars_locs_store_extend with (G:=env) (p:=plift p) in IQ; eauto.
      assert (i < length M). { eapply env_type_store_wf; eauto. }
      destruct IO_k.
      destruct IQ. eauto.
      assert (x = x0). {
        destruct WFE as [? [? [? SEP]]].
        eapply SEP.
        eapply H3. eapply H3. 
        eapply H4. eapply H4.
      }
      subst x0. eapply (H x).
      unfoldq. intuition. unfoldq. intuition. unfoldq. intuition.
      (* not escaping value *)
      rewrite val_locs_ref in IO_fresh. unfoldq. intuition.
    }

    remember ST1 as ST1x. clear HeqST1x.
    destruct ST1 as [LST [KS1 ST1]].
    destruct (ST1 i vt qt) as [ ? [ ? | [vy [SI [VT QT]]]]]. eauto. contradiction.

    exists S1, M1, vy. split.
    + (* expression evaluates *)
      destruct IW1 as [n1 IW1].
      rename S into Sx.
      exists (S n1).
      intros. destruct n. lia.
      simpl. rewrite IW1. rewrite SI. eauto. lia.
    + (* result well typed *)
      split. 2: split. 
      specialize (HVX1 vy VT).
      eapply storet_restrict. eauto.
      (* K < K' *) {
        rewrite val_locs_ref. intros ? HX.
        destruct HX as [HX_K | [HX_k | HX_fresh]].
        (* K *) left. eauto.
        (* k *) right. left. eauto.
        (* fresh *) right. right.
        destruct HX_fresh as [? ? ?].
        unfoldq. split. split. eapply H3. eapply H3.
        intros ?.
        destruct H4. right. unfold loc_locs.
        exists vt, qt. intuition.
      }
      (* K < dom(M1++M) *) {
        unfoldq. intuition. 
      }
      eauto.
      unfoldq. intuition. eapply (HQX x). rewrite val_locs_ref.
      unfoldq. unfold loc_locs. split. eauto. 
      right. exists vt, qt. intuition. 

  - (* Case "Free". *)
    destruct (IHW M E WFE S K) as [S1 [M1 [vx [IW1 [SW1 [HVX HQX]]]]]]. eauto. eauto.
    destruct vx; try solve [inversion HVX]. simpl in HVX.
    destruct (HVX) as [CL [vy [SI HVX1]]].
    exists (update S1 i None).
    exists M1. exists (vbool false). split.
    + (* expression evaluates *)
      destruct IW1 as [n1 IW1].
      rename S into Sx.
      exists (S n1).
      intros. destruct n. lia.
      simpl. rewrite IW1. eauto. lia.
    + (* result well typed *)
      split.

      (* given *)
      assert (store_type S1 (M1 ++ M)
                (por K
                   (por (vars_locs (M1 ++ M) E (pand (plift p) (plift k)))
                      (pdiff (pdiff (pdom (M1 ++ M)) (pdom M))
                         (val_locs (M1++M) (vref i)))))). { eauto. }

      (* prove *)
      assert (store_type S1 (M1 ++ M)
                (por K
                   (por (vars_locs (M1 ++ M) E (pand (plift p) (plift (qor k q))))
                      (pdiff (pdiff (pdom (M1 ++ M)) (pdom M)) (val_locs (M1 ++ M) (vbool false)))))). {

        eapply storet_restrict. eauto.
        
        rewrite plift_or, val_locs_ref, val_locs_bool.
        intros ? ?. unfoldq. destruct H2 as [HX_K | [HX_k | HX_fresh]].
        (* K *) left. eauto.
        (* k *) right. left. destruct HX_k. exists x0. intuition.
        (* fresh *) right. right. intuition.

        rewrite plift_or, val_locs_bool.
        destruct SW1 as [? [KS ?]].
        rewrite <-vars_locs_store_extend with (G:=env) (p:=plift p); eauto. 
        intros ? ?. destruct H4 as [HX_K | [HX_k | HX_fresh]].
        (* K *) eapply KS. left. eauto.
        (* k *) eapply app_length2. eapply env_type_store_wf. eauto. eapply HX_k.
        eapply HX_fresh. unfoldq. intuition.
      }
        
      eapply storet_free. eauto. {
        rewrite <-vars_locs_store_extend with (G:=env) (p:=plift p); eauto.
        2: { unfoldq. intuition. }
        
        bdestruct (i <? length M).
        * unfoldq. 
          destruct (HQX i). rewrite val_locs_ref. intuition.
          left. unfoldq. intuition. 
          right. left. exists x. intuition.
          rewrite plift_or. unfoldq. intuition.
          rewrite <-var_locs_store_extend0 with (G:=env) (p:=plift p) in H10.
          eauto. eauto. eauto. 
        * right. right.
          rewrite val_locs_bool.
          unfoldq. intuition.
          eapply indexr_extend; eauto.
      }

      split. simpl. eauto.
      eapply valq_bool.
      
  - (* Case "App". *)
    rename H5 into K2X.
    rename H6 into H5.
    rename H7 into KSEP.
    
    (* induction on both subexpressions: obtain vf, vx *)
    destruct (IHW1 M E WFE S K) as [S1 [M1 [vf [IW1 [SW1 [HVF HQF]]]]]]. eauto.
    repeat rewrite plift_or in KSEP. repeat rewrite pand_dist_or in KSEP. repeat rewrite vars_locs_dist_or in KSEP.
    unfoldq. intuition. eapply (KSEP x). intuition.
    
    assert (env_type (M1++M) E env (plift p)) as WFE1. { eapply envt_store_extend. eauto. }
    remember (por K
                (por (vars_locs (M1 ++ M) E (pand (plift p) (plift kf)))
                   (pdiff (pdiff (pdom (M1 ++ M)) (pdom M)) (val_locs (M1 ++ M) vf)))) as K1.
(*  remember (por K (vars_locs E (pand (plift p) (plift kf)))) as K1. *)
    destruct (IHW2 (M1++M) E WFE1 S1 K1) as [S2 [M2 [vx [IW2 [SW2 [HVX HQX]]]]]]. eauto.

    (* K1SEP: K1 & locs (p & e1) < empty *)
    rewrite <-vars_locs_store_extend with (G:=env) (p:=plift p).
    2: eauto. 2: { unfoldq. intuition. }
    repeat rewrite plift_or in KSEP. 
    unfoldq. intuition. destruct H8. subst K1. destruct H7 as [|[|]].
    eapply (KSEP x). intuition. exists x0. intuition.
    destruct H7.
    rewrite <-var_locs_store_extend0 with (G:=env) (p:=plift p) in H7.
    2: eauto. 2: { unfoldq. intuition. }
    assert (x0 = x1). { (* separation *)
      destruct WFE as [? [? [? SEP]]].
      eapply SEP. eapply H6. eapply H6. eapply H7. eapply H7. 
    }
    subst x1. eapply (H0 x0). intuition.
    destruct H7. eapply H7. eapply envt_var_store_wf. eauto. eapply H6.


    (* uniformly take smallest store for things bound by qualifiers *)
    assert (forall q,
               vars_locs (M2 ++ M1 ++ M) E (pand (plift p) q) =
                 vars_locs M E (pand (plift p) q)) as VQ2. {
      intros. rewrite app_assoc. 
      rewrite <-vars_locs_store_extend with (G:=env) (M1:=M2++M1) (p:=plift p).
      eauto. eauto. unfoldq. intuition.
    }
    assert (forall q,
               vars_locs (M1 ++ M) E (pand (plift p) q) =
                 vars_locs M E (pand (plift p) q)) as VQ1. {
      intros. 
      rewrite <-vars_locs_store_extend with (G:=env) (M1:=M1) (p:=plift p).
      eauto. eauto. unfoldq. intuition.
    }



    
    (* vf is a function value: it can eval its body *)
    destruct vf; try solve [inversion HVF].
    remember (por K1
                (por (vars_locs (M2 ++ M1 ++ M) E (pand (plift p) (plift k1)))
                   (pdiff (pdiff (pdom (M2 ++ M1 ++ M)) (pdom (M1 ++ M)))
                      (val_locs (M2 ++ M1 ++ M) vx)))) as K2. 
(*    remember (por K1 (vars_locs E (pand (plift p) (plift k1)))) as K2. *)
    assert (exists S3 M3 vy,
               tevaln S2 (vx::l) t0 S3 vy /\
                 store_type S3 (M3++M2++M1++M)
                   (por K2
                      (por (vars_locs (M3 ++ M2 ++ M1 ++ M) E (plift k2))
                         (por (if k2x then (val_locs (M3 ++ M2 ++ M1 ++ M) vx) else pempty)
                            (pdiff (pdiff (pdom (M3++M2++M1++M)) (pdom (M2++M1++M))) (val_locs (M3 ++ M2 ++ M1 ++ M) vy))))) /\
                 val_type (M3++M2++M1++M) E vy T2 /\
                 val_qual M (M3 ++ M2 ++ M1 ++ M) E vy (plift p) (por (plift q2) (if q2x then (plift q1) else pempty)) /\
                 psub
                   (pand (pdom (M2++M1++M)) (val_locs (M3 ++ M2 ++ M1 ++ M) vy))
                   (por (val_locs (M3 ++ M2 ++ M1 ++ M) (vabs l q t0))
                      (if q2x then (val_locs (M3 ++ M2 ++ M1 ++ M) vx) else pempty))
           ) as HVY. {
      apply valt_wf in HVX as HVX'.
      eapply sem_app1; eauto.

      replace (plift e2) with (pand (plift p) (plift e2)).
      2: { intros. eapply functional_extensionality. intros. eapply propositional_extensionality. unfoldq. intuition. }
      unfold val_qual in HQF, HQX. 
      repeat rewrite VQ1 in *.
      repeat rewrite VQ2 in *.

      subst K2 K1. (* effect sep: K2 & e2 = empty <- e2 not killed *)

      repeat rewrite por_assoc. 
      unfoldq. intros. destruct H6 as [? ?]. destruct H7.
      destruct H7. destruct H7.
      destruct H6 as [|[|[|[]]]].
      eapply KSEP. split. eauto. exists x0. repeat rewrite plift_or. unfoldq. intuition.
      destruct H6. destruct H6. 
      assert (x0 = x1). destruct WFE as [? [? [? SEP]]]. eapply SEP. eapply H3. eauto. eapply H7. eapply H8. eapply H6. eauto. 
      subst x1. eapply H1. intuition. left. eauto. eauto.
      assert (x < length M). eapply envt_var_store_wf. eapply WFE. eapply H8. lia.
      destruct H6. destruct H6. 
      assert (x0 = x1). destruct WFE as [? [? [? SEP]]]. eapply SEP. eapply H3. eapply H7. eapply H8. eapply H6. eapply H9.
      subst x1. eapply H1. intuition. right. eauto. eauto. 
      assert (x < length M). destruct H6. eapply envt_var_store_wf. eauto. eapply H8.
      repeat rewrite app_length in H6. lia.

      destruct e2x. (* arg is used *)
      
      (* subst K2. subst K1.*) (* effect sep: K2 & vx = empty <- arg not killed *)
      
      unfoldq. intros. destruct H6 as [|[|[|[|]]]].
      eapply KSEP. intuition. eauto.
      assert (x < length M). destruct H5 as [? [H5 ?]]. eapply H5. eapply H6.
      destruct (HQX x). intuition. rewrite app_length. lia.
      eexists. intuition. eauto. repeat rewrite plift_or. unfoldq. intuition. eapply H11. 

      
      (* kf & vx *)
      destruct H6. destruct H6.
      eapply H1. split. left. eapply H6. right.
      destruct (HQX x). intuition.
      eapply app_length2. eapply envt_var_store_wf. eauto. eapply H8.
      assert (x0 = x1). destruct WFE as [? [? [? SEP]]].
      eapply SEP. eapply H6. eapply H8. eapply H9. eapply H9.
      subst x1. eapply H9. 
      
      specialize (HQX x). destruct HQX. intuition.
      destruct H6. destruct H8. assert (x < length M). eapply envt_var_store_wf. eauto. eauto. lia.
      
      (* k1 & vx *)
      destruct H6. 
      eapply H1. split. right. eapply H6. right.
      destruct (HQX x). intuition.
      eapply app_length2. eapply envt_var_store_wf. eauto. eapply H9.
      assert (x0 = x1). destruct WFE as [? [? [? W]]].
      eapply W. eapply H6. eapply H6. eapply H8. eapply H8.
      subst x1. eapply H8. 
      
      destruct H6. contradiction.

      (* e2x = false: arg is not used *)
      contradiction.
    }
    destruct HVY as [S3 [M3 [vy [IW3 [SW3 [HVY [HQY HQY2]]]]]]].

    (* result *)
    exists S3, (M3++M2++M1). exists vy. split.
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
    + (* result well typed *)
      (* eapply valt_qual_widen1. *)    
      repeat rewrite <-app_assoc.

    assert (forall q,
               vars_locs (M3 ++ M2 ++ M1 ++ M) E (pand (plift p) q) =
                 vars_locs M E (pand (plift p) q)) as VQ3. {
      intros. rewrite app_assoc. rewrite app_assoc. 
      rewrite <-vars_locs_store_extend with (G:=env) (M1:=(M3++M2)++M1) (p:=plift p).
      eauto. eauto. unfoldq. intuition.
    }

      
      unfold val_qual in *.
      repeat rewrite VQ3 in *.
      repeat rewrite VQ2 in *.
      repeat rewrite VQ1 in *.
      (* also tighten any val_locs based on val_type ? *)
      
      (* ----------- store_type  ---------- *)
      split. subst K2 K1. eapply storet_restrict. eapply SW3.

      (* (1) effect bound: K from val_type < K from has_type *)

      repeat rewrite por_assoc. repeat rewrite plift_or, plift_if, plift_empty, plift_or, plift_or.
      unfoldq. repeat rewrite app_length. intros x EXX.

      (* K --> K *)
      destruct EXX as [EX | EXX]. left. eauto.

      (* kf --> kf *)
      destruct EXX as [EX | EXX].
      right. left. 
      destruct EX as [x0 EX]. exists x0. intuition.

      (* !vf, !M, M1 --> !vy, could be vx *)
      destruct EXX as [EX | EXX].
      right. right. intuition.
      destruct (HQY2 x). { repeat rewrite app_length. intuition. }
      eapply H7. rewrite val_locs_extend with (M':=M3++M2). eauto. rewrite <-app_assoc. eapply H10. eapply valt_wf. eauto.   (* !vf *)
      destruct q2x. 2: contradiction.
      destruct (HQX x). rewrite app_length. intuition.
      rewrite val_locs_extend with (M':=M3). eauto. eapply valt_wf. eauto. 
      eapply H9. eapply envt_var_store_wf. eauto. eapply H11.

      (* k1 --> k1 *)
      destruct EXX as [EX | EXX].
      right. left.
      destruct EX as [x0 EX]. exists x0. intuition. 
      
      (* !vx, !M, !M1, M2 --> !vy, could be vf *)
      destruct EXX as [EX | EXX].
      right. right. intuition.
      destruct (HQY2 x). { repeat rewrite app_length. intuition. }
      eapply valt_wf in HVF. 
      eapply H9. rewrite <-app_length. eapply HVF. rewrite val_locs_extend with (M':=M3++M2). rewrite <-app_assoc. eauto. eapply HVF.
      destruct q2x. 2: contradiction.
      eapply valt_wf in HVX. 
      eapply H7. rewrite val_locs_extend with (M':=M3). eauto. eapply HVX. 

      (* k2 --> k2 *)
      destruct EXX as [EX | EXX].
      right. left.
      destruct EX as [x0 EX]. exists x0. intuition.
      rewrite var_locs_store_extend0 with (M1:=M3++M2++M1) (G:=env) (p:=plift p).
      repeat rewrite <-app_assoc. eauto. eauto. eauto. 

      (* k2x & vx --> q1 *)
      destruct EXX as [EX | EXX].
      destruct k2x. 2: contradiction.

      bdestruct (x <? length (M1 ++ M)). (* not fresh? *)
      destruct (HQX x). intuition.
      rewrite val_locs_extend with (M':= M3). eauto. eapply valt_wf. eauto. 
      right. left. exists x0. intuition.
      (* fresh? can't be returned! *)
      right. right. intuition. eapply valt_wf in EX; eauto.
      unfoldq. repeat rewrite app_length in EX. lia.
      eapply valt_store_extend. eauto. 
      rewrite app_length in H6. lia.
      (* vx --> !vy *)
      eapply valt_wf in HVX as HVX1.
      rewrite <-val_locs_extend in EX. 2: eapply HVX1.
      eapply valt_wf in HVF as HVF1.
      destruct (HQY2 x). intuition.
      eapply valt_wf in EX; eauto.
      rewrite app_assoc in H9.
      rewrite <-val_locs_extend in H9. 2: eapply HVF1.
      eapply valt_wf in H9; eauto.
      unfoldq. lia.
      rewrite H7 (* K2X *) in H9. contradiction.

      (* last one *)
      right. right. intuition.
      

      (* (2) K < dom *)
      repeat rewrite plift_or. unfoldq. repeat rewrite app_length. intros ? EXX.
      destruct EXX as [?|[?|?]].
      destruct H5 as [? [H5 ?]]. eapply H5 in H6. unfoldq. lia.
      destruct H6. destruct H6. destruct H6. eapply envt_var_store_wf in H7; eauto.
      unfoldq. lia. 
      eapply H6.

      (* ----------- val_type & val_qual  ---------- *)
      
      split. eapply HVY.
      destruct q2x. rewrite plift_or. eapply HQY.
      rewrite plift_or, plift_empty. eapply HQY.
      
  - (* Case "Abs". *)
    exists S. exists []. exists (vabs E (qand p qf) t).
    split.
    + (* term evaluates *)
      exists 0. intros. destruct n. lia. simpl. eauto.
    + (* result well typed *)
      rewrite app_nil_l.
      split. rewrite plift_empty in *.
      eapply storet_restrict. eauto. unfoldq. intuition. unfoldq. intuition.
      destruct H5 as [? [H5 ?]]. eapply H5. eauto. destruct H7 as [? [[? []] ?]]. 
      
      split. simpl. 
      
      rewrite <-LE in *. repeat split; eauto. 
      rewrite val_locs_abs. eapply env_type_store_wf. eauto.
      
      intros S1 M1 K1 vx ST1 HVX SEP KSEP.
      eapply sem_abs1; eauto.

      intros. eapply IHW. eauto. eauto.

      (* vx, e2 sep K1 *)
      rewrite val_locs_abs, plift_and in SEP.
      rewrite plift_or, plift_and, plift_or, plift_if, plift_one.
      unfoldq. intuition.
      destruct H10 as [x0 ?].
      bdestruct (x0 =? length E). destruct e2x. subst x0.
      
      destruct H8. destruct H8. destruct H8. destruct H8. eapply PC in H8. lia.
      destruct H11. eapply H3 in H11. lia.
      destruct H10. destruct H10. rewrite indexr_head in H10. inversion H10. subst x0.
      eapply KSEP. intuition. eauto. intuition.
      (* e2x = false *)
      subst x0.
      destruct H8. destruct H8. destruct H8. destruct H8. eapply PC in H8. lia.
      destruct H11. eapply H3 in H11. lia.
      rewrite plift_empty in H11. unfoldq. contradiction.
      (* x0 <> length E *)
      eapply KSEP. split. eauto.
      destruct H8. destruct H8. destruct H8. 2: lia.
      destruct H12. left. exists x0. intuition. eapply var_locs_shrink; eauto.
      right. destruct e2x. lia. rewrite plift_empty in H12. unfoldq. contradiction.

      assert (psub (pand (plift p) (plift qf)) (pdom E)) as CL. {
        unfoldq. intuition. }
      rewrite <- plift_and in CL.
      eapply CL.
      eapply valq_abs; eauto.
      
  -  (* Case "Sub". *)
    destruct (IHW M E WFE S K) as [S1 [M1 [vx [IW1 [SW1 [HVX HQX]]]]]]. { eauto. }
     assert (psub (plift q2) (pdom E)). {
      unfoldq. rewrite LE. intuition. }

    unfoldq. intuition. destruct H10. eapply (H6 x). intuition. exists x0. intuition.
    
    exists S1, M1, vx.
    unfold exp_type. intuition.
    eapply storet_restrict. eauto. 

    (* k1 < k2 *)
    unfoldq. intros. destruct H7 as [|[|]].
    left. intuition.
    right. left. destruct H7. exists x0. unfoldq. intuition.
    right. right. eauto.

    (* < dom M1 ++ M *)
    unfoldq. intros. destruct H7 as [|[|]].
    destruct SW1 as [? [SW1 ?]].
    eapply SW1. eauto.
    destruct H7.
    eapply envt_var_store_wf. eapply envt_store_extend. eauto. eapply H7. 
    eapply H7.
    
    eapply valq_sub; eauto. rewrite DE. eauto.
Qed.


(* note: not assuming anything other than has_type below *)

Corollary safety : forall t T q e k,
  has_type [] t T qempty q e k -> 
  exists S M v, exp_type [] [] (plift qempty) [] t S M v T (plift qempty) (plift q) (plift e) (plift k).
Proof. 
  intros. eapply full_total_safety in H; eauto.
  unfold env_type; intuition; simpl. unfoldq. intuition. inversion H0.
  unfold store_type. intuition.
  unfoldq. intuition. inversion H0. inversion H0. 
  unfoldq. intuition. 
Qed.

End STLC.
