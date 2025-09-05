(* Full safety for STLC *)

(* based on stlc_reach.v and stlc_ref.v *)
(* based on stlc_reach_ref_alt_kill3.v *)
(* based on stlc_reach_ref_kill_tight_effects *)

(*

NEW IN THIS FILE:

- tighten qualifiers further!

- surprisingly:
  - p isn't needed and can be empty!
  - function qualifiers can be empty!

Why does this work? The working hypothesis
is because in this file:

- no overlap
- no escaping values (self refs)
- no valt_store_change



----- from ../pub/..kill_tight_effects2.v

NEW IN THIS FILE

- prove that pure expressions don't change
  the store (store_effect invariant)



 ----- from ../pub/..kill_tight.v

WIP: INVESTIGATE ALTERNATIVE ENV FILTER NOTIONS

NEW IN THIS FILE:

- only intersect against e2, instead of qf!

This means we're only checking separation with
*used* values.

Key changes that made this work:
- split env_qual off from env_type
- require as input to val_type (making separation
  flow sensitive, not strictly context sensitive)


FROM PREVIOUS (alt 3):

- require arg intersection for function calls
  only if arg is used (e2x) !


FROM PREVIOUS (alt 2):

Goal: work towards a model where only 'used' things
are tracked. We're not quite there yet, but this
is a version that removes the v < p constraint
from val_qual and enforces it more selectively.

Filter model:

- every qualifier that gets intersected needs < p
  (e.g. qf/q1 in app, e/k effects)

- result of function body needs to be < qf in abs

Constraints removed:

- var rule doesn't need x < p

- app rule doesn't need q2 < p

This file matches ..alt_effects1.v but with kill
effects added from ..alt_kill1.v

*)




(* 

Simply-typed lambda calculus, combined proof of termination and type 
soundness (using logical relations).

This version adds immutable references. Store entries are 
restricted to base types (TRef TBool) only.

This version adds reachability types. The type qualifiers are
modeled as functions that check set membership. Restrictions:
no argument overlap, no dependent app.

This version adds use and kill effects. Every dereference incurs
a use effect. A free operation incurs a kill effect, and replaces
the store entry with a tombstone. Effect checking ensures that
all dereferences use live variables that have not been freed.

Since store entries are modified through deallocation, the 
store no longer grows monotonically. Hence the proof relies
on a store typing, along with a set of inaccessible locations
(both of which grow monotically).

Done:

- tightened invariants to allow killing *some* fresh 
  allocations -- but not if the fresh location escapes (see 
  note below and in exp_type)
- right now we prohibit killing function args -- this
  is incompatible with returning them. Allow the other
  version, too: kill but don't return.
  (e.g. extend TFun to include dependency info)

Cleanup - todo:

- some bits feel repetitive, what are suitable lemmas?

Extensions:

- nested variables
- move effects
- mutation (swap) -- does it remain terminating?

Note on killing fresh allocations:

  This is unsafe and should be an error:
  
    get(let x = ref(1); free(x); x) // returns something that 
                                    // looks valid but is not

  However, this case if fine, and should typecheck:
  
    get(let x = ref(1); free(x); 7)
    
  Hypothesis: while evaluating expression an e, we can kill
  everything that's freshly allocated (i.e., not previously
  in the store) as long as it doesn't escape (reachable 
  via e's result).
  
  Question 1: could this be used for *automatic* deallocation?
  
  Question 2: what if locations can escape through other means,
              e.g., via assignment to mutable refs (swap)?

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

Definition pnot p1 (x:nat) := ~ p1 x.                               (* complement *)

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
  | tput : tm -> tm -> tm  
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


(*
QUALIFIERS:

Filter p is currently unused.

Function qualifier contains q2, e2, k2.

Function app checks e2, k2 /\ q1 = 0

*)

Inductive has_type : tenv -> tm -> ty -> ql -> ql -> ql -> ql -> Prop :=
| t_true: forall env p,
    has_type env ttrue TBool p qempty qempty qempty    (* nothing reachable from a primitive *)
| t_false: forall env p,
    has_type env tfalse TBool p qempty qempty qempty
| t_var: forall x env T  p,
    indexr x env = Some T ->
    (* (plift p) x ->  not needed *)
    has_type env (tvar x) T p (qone x) qempty qempty  (* x can reach only itself (no overlap) *)
| t_ref: forall t env p q e k,
    has_type env t TBool p q e k ->
    has_type env (tref t) (TRef TBool) p q e k
| t_get: forall t env p q e k,
    has_type env t (TRef TBool) p q e k ->
    psub (pand (plift k) (plift q)) pempty ->
    True -> (* psub (plift k) (plift p) -> *) 
    True -> (* psub (plift q) (plift p) -> *)
    has_type env (tget t) TBool p qempty (qor e q) k
| t_put: forall t1 t2 env p q1 e1 q2 e2 k1 k2,
    has_type env t1 (TRef TBool) p q1 e1 k1 ->
    psub (pand (plift k1)(plift e2)) pempty ->
    psub (pand (plift k1)(plift q1)) pempty ->  
    psub (pand (plift k2)(plift q1)) pempty ->
    has_type env t2 TBool p q2 e2 k2 ->
    has_type env (tput t1 t2) TBool p qempty (qor e1 (qor e2 q1)) (qor k1 k2)
| t_free: forall t env p q e k,
    has_type env t (TRef TBool) p q e k ->
    has_type env (tfree t) TBool p qempty e (qor k q) (* always return 'false' *)
| t_app: forall env f t T1 T2 p qf q1 q2 ef e1 e2 kf k1 k2 q2x e2x k2x,
    has_type env f (TFun T1 (* qempty *) T2 q2 e2 k2 q2x e2x k2x) p qf ef kf ->  
    has_type env t T1 p q1 e1 k1 ->
    (* arg intersection *)
    (if e2x || k2x then psub (pand (por (plift e2) (plift k2)) (plift q1)) pempty else True) ->
    True -> (* (if e2x || k2x then psub (plift q1) (plift p) else True) -> *)
    (* effects *)
    psub (pand (plift kf) (plift e1)) pempty ->          (* no use after kill *)
    psub (pand (por (plift kf) (plift k1)) (por (plift e2) (if e2x then (plift q1) else pempty))) pempty ->          (* no use after kill *)
    True -> (* psub (plift kf) (plift p) -> *)
    True -> (* psub (plift k1) (plift p) -> *)
    True -> (* psub (plift e1) (plift p) -> *)
    True -> (* psub (plift e2) (plift p) -> *)
    True -> 
    (* NOTE: we can return OR kill the function arg, but not both.  *)
    (*       possible to refine: only an issue if the function arg may be fresh! *)
    (k2x = true -> q2x = false) ->
    has_type env (tapp f t) T2 p
      (qor q2                   (if q2x then q1 else qempty))
      (qor (qor ef (qor e1 e2)) (if e2x then q1 else qempty))
      (qor (qor kf (qor k1 k2)) (if k2x then q1 else qempty))
| t_abs: forall env t T1 T2 p q2 qf e2 k2 (q2x e2x k2x: bool),
    has_type (T1::env) t T2
      p (* (qor qf (if e2x then qone (length env) else qempty)) *)
      (qor q2 (if q2x then qone (length env) else qempty))
      (qor e2 (if e2x then qone (length env) else qempty))
      (qor k2 (if k2x then qone (length env) else qempty)) ->
    closed_ty (length env) T1 ->
    closed_ty (length env) T2 ->
    closed_ql (length env) qf ->
    closed_ql (length env) q2 ->
    closed_ql (length env) e2 ->
    closed_ql (length env) k2 ->
    (* NOTE: can simplify this to qf = qor p2 (qor e2 k2) *)
    True -> (* psub (plift q2) (plift qf) -> (* need for vy < q2 & vf *) *)
    True -> (* psub (plift e2) (plift qf) -> (* need for e2 & vf  *) *)
    True -> (* psub (plift k2) (plift qf) -> (* needed ? *) *)
    psub (plift qf) pempty -> (* !!! *)  (* psub (plift qf) (pdom env) -> (* psub (plift qf) (plift p) ->  *) *)
    (*  *)
    has_type env (tabs qf t) (TFun T1 T2 q2 e2 k2 q2x e2x k2x) p qf qempty qempty 
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
                    | Some v => (update M'' x (Some vx), Some (Some (vbool true)))
                    | _ => (M'', Some None)
                    end
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


(* env equal separation *)
Definition env_qual H (p:pl) :=
  forall l x0 x1,
    p x0 ->
    var_locs H x0 l ->
    p x1 ->
    var_locs H x1 l ->
    x0 = x1.

(* store typings *)

Definition stty := list (vl -> Prop).


Definition st_killed (S: stor) (M: stty) x :=
  indexr x S = Some None.



Definition store_type (S: stor) (M: stty) :=
  length S = length M /\
    forall l vt,
      indexr l M = Some vt ->
      indexr l S = Some None \/
        exists b,
          indexr l S = Some (Some (vbool b)).


(* store preservation invariant *)

Definition store_effect (S S1: stor) (p: pl) :=
  forall l v,
    ~ p l -> 
    indexr l S = Some v ->
    indexr l S1 = Some v.


(* value interpretation of types *)

Fixpoint val_type (M:stty) (H:venv) v T : Prop :=
  match v, T with
  | vbool b, TBool =>
      True
  | vref l, TRef T => 
      T = TBool /\
      exists vt,
      indexr l M = Some vt 
  | vabs G py ty, TFun T1 (* qempty *) T2 q2 e2 k2 q2x e2x k2x => (* TODO! *)
      closed_ty (length H) T1 /\
        closed_ty (length H) T2 /\
        (psub (plift q2) (pdom H)) /\
        (psub (plift e2) (pdom H)) /\
        (psub (plift k2) (pdom H)) /\
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
              env_qual H (por (plift e2) (plift k2))
            ->
              (if e2x || k2x then psub (pand ((vars_locs H (por (plift e2) (plift k2)))) (val_locs vx)) pempty else True)
            ->
              psub
                (pand (st_killed S' (M'++M))
                   (por (vars_locs H (plift e2))
                      (if e2x then (val_locs vx) else pempty)))
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
                /\
                  store_effect S' S''
                    (por (vars_locs H (por (plift e2) (plift k2)))
                         (if e2x || k2x then val_locs vx else pempty))
                /\
                  psub (st_killed S'' (M''++M'++M))
                    (por (st_killed S' (M'++M))
                       (por (vars_locs H (plift k2))
                          (por (if k2x then (val_locs vx) else pempty)  
                             (pdiff (pdiff (pdom (M''++M'++M)) (pdom (M'++M)))
                                (val_locs vy)))))
                /\
                  val_type
                    (M''++M'++M)
                    H
                    vy
                    T2
                /\
                  psub
                    (pand (pdom (M'++M)) (val_locs vy))
                    (por (vars_locs H (plift q2))
                       (if q2x then (val_locs vx) else pempty)))
  | _,_ =>
      False
  end.


Definition val_qual (M: stty) H v (p q: pl) :=
  psub (pand (pdom M) (val_locs v)) (vars_locs H q).


Definition store_qual S M H S' M' v (p k: pl) :=
    psub (st_killed S' (M'++M))
      (por (st_killed S M)
         (por (vars_locs H k)
            (pdiff (pdiff (pdom (M'++M)) (pdom M))
               (val_locs v)))).


Definition exp_type S M H t S' M' v T p q (e: pl) (k: pl) :=
  tevaln S H t S' v /\
    store_type S' (M'++M) /\
    store_effect S S' (vars_locs H (por e k)) /\
    store_qual S M H S' M' v p k /\ 
    val_type (M'++M) H v T /\
    val_qual M H v p q.

(* kill set after evaluating t to v is the union of:
   - previous cumulative kill set K
   - existing observable locations mentioned by t's effect annotation k (i.e., p /\ k)
   - fresh locations allocated during evaluation of t that aren't reachable from result v
 *)
   


Definition safe_qual S M H (p e: pl) := 
  psub (pand (st_killed S M) (vars_locs H e)) pempty.




(* what to do to check e,k ? restrict store? *)


Definition env_type M H G p :=
  length H = length G /\
    psub p (pdom H) /\
    forall x T,
      indexr x G = Some T ->
      exists v : vl,
        indexr x H = Some v /\
          val_type M H v T.



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

Lemma var_locs_extend: forall H H' x,
    x < length H ->
    var_locs (H' ++ H) x = 
      var_locs H x.
Proof. 
  intros. apply functional_extensionality.
  intros. apply propositional_extensionality.
  unfoldq. unfoldq. intuition.
  - destruct H1. exists x1. intuition.
    eapply indexr_extend; eauto.
  - destruct H1. exists x1. intuition.
    eapply indexr_extend in H2. eapply H2. 
Qed.


Lemma vars_locs_dist_or: forall E a b,
    vars_locs E (por a b) = por (vars_locs E a) (vars_locs E b).
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


(* ---------- val_type lemmas  ---------- *)

Lemma valt_wf: forall T M H v,
    val_type M H v T ->
    psub (val_locs v) (pdom M).
Proof. 
  intros T. induction T; intros; destruct v; simpl in *; intuition.
  + rewrite val_locs_bool. auto. unfoldq. intuition.
  + rewrite val_locs_ref.
    destruct H2 as [vt IX].
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
  + destruct H2 as [vt IX].
    exists vt. 
    eapply indexr_extend in IX. eapply IX.
  + unfoldq. rewrite app_length. intros. assert (x < length M). eauto. lia.
  + destruct (H7 S' (M'0 ++ M') vx) as [S'' [M'' [vy  [IEY [STY [SEY [HSK [HVY HSEP]]]]]]]].
    rewrite <- app_assoc. auto.
    rewrite <- app_assoc. auto.
    auto. auto. eauto.
    exists S'',  M'', vy. intuition.
    repeat erewrite <- app_assoc in STY; eauto.
    repeat erewrite <- app_assoc in HSK; eauto.
    repeat erewrite <- app_assoc in HVY; eauto.
    repeat erewrite <- app_assoc in HSEP; eauto.
Qed. 


Lemma valt_extend: forall T M H' H v,
    closed_ty (length H) T ->
    val_type M (H'++H) v T <-> val_type M H v T.
Proof.
  intros T. induction T; split; intros; destruct v; simpl in *; intuition.
  - inversion H0. auto.
  - inversion H0. subst. auto.
  - inversion H0. subst. intros ? ?. unfoldq; intuition.
  - inversion H0. subst. intros ? ?. unfoldq; intuition.
  - inversion H0. subst. intros ? ?. unfoldq; intuition.
  - (* Abs shrink *)
    inversion H0. subst.
(*    rename q into q2.  *)
    destruct (H8 S' M' vx) as [S'' [M'' [vy [HEY [HST [HSE [HSK [HVY HSEP]]]]]]]].
      eauto.
      eapply IHT1; eauto.
      unfold env_qual in *. intros.
      rewrite var_locs_extend in H14, H16.
      eapply H10; eauto.
      destruct H15. eapply H25; eauto. eapply H26; eauto. 
      destruct H13. eapply H25; eauto. eapply H26; eauto. 
      rewrite vars_locs_extend. eauto. unfoldq. intuition. 
      rewrite vars_locs_extend. eauto. eauto. 
    exists S'', M'', vy. intuition.
    rewrite vars_locs_extend in HSE. eauto. unfoldq. intuition.
    rewrite vars_locs_extend in HSK. eauto. eauto. 
    eapply IHT2; eauto.
    rewrite vars_locs_extend in HSEP. eauto. eauto.
  - eapply closedty_extend; eauto.
  - eapply closedty_extend; eauto.
  - unfoldq. rewrite app_length. intuition. eapply H3 in H7. lia.
  - unfoldq. rewrite app_length. intuition. eapply H4 in H7. lia.
  - unfoldq. rewrite app_length. intuition. eapply H5 in H7. lia.
  - (* Abs grow *)
    inversion H0. subst.
(*    rename q into q2. *)
    destruct (H8 S' M' vx) as [S'' [M'' [vy [HEY [HST [HSE [HSK [HVY HQY]]]]]]]].
      eauto.
      eapply IHT1; eauto.
      unfold env_qual in *. intros.
      eapply H10; eauto. 
      rewrite var_locs_extend. eauto. unfoldq. intuition. 
      rewrite var_locs_extend. eauto. unfoldq. intuition. 
      rewrite vars_locs_extend in H11. eauto. unfoldq. intuition.
      rewrite vars_locs_extend in H12. eauto. eauto. 
    exists S'', M'', vy. intuition.
    rewrite vars_locs_extend. eauto. unfoldq. intuition. 
    rewrite vars_locs_extend. eauto. eauto.
    eapply IHT2; eauto.
    rewrite vars_locs_extend. eauto. eauto.
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
    val_qual M H (vabs H q t) (plift p) (plift q).
Proof.
  intros. unfoldq.
  rewrite val_locs_abs.
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
    psub p' (pdom H) ->
    env_type M H G p'.
Proof.
  intros. destruct H0 as [L [P W]].
  repeat split; auto.
Qed.

Lemma envq_tighten: forall H p p',
    env_qual H p ->
    psub p' p ->
    env_qual H p'.
Proof.
  intros. unfold env_qual in *. intuition.
  eapply H0; intuition; eauto.
Qed.




Lemma envt_extend: forall M H G v T q p,
    env_type M H G p ->
    closed_ty (length H) T ->
    closed_ql (length H) q ->
    val_type M H v T ->
    (* separation *)
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
    + destruct (W _ _ H0); eauto.
      unfoldq. intuition.
      eexists. intuition. eauto.
      eapply valt_extend1; eauto.
      eapply valt_closed; eauto.
Qed.

Lemma envq_extend: forall H v q p,
    env_qual H p ->
    closed_ql (length H) q ->
    psub p (pdom H) ->
    (* separation *)
    (forall x l, val_locs v l -> p x -> var_locs H x l -> False) ->
    env_qual (v::H) (por p (pone (length H))).
Proof. 
  intros. unfold env_qual in *. intros. 
    inversion H4; inversion H6.
    + eapply H0; eauto.
      eapply var_locs_shrink. eauto. eapply H2; eauto.
      eapply var_locs_shrink. eauto. eapply H2; eauto.
    + destruct (H3 x0 l); eauto.
      assert (x1 = length H). unfoldq. intuition.
      subst x1. eapply aux1; eauto.
      eapply var_locs_shrink. eauto. eapply H2; eauto.
    + destruct (H3 x1 l); eauto.
      assert (x0 = length H). unfoldq. intuition.
      subst x0. eapply aux1; eauto.
      eapply var_locs_shrink. eauto. eapply H2; eauto.
    + unfoldq. lia.
Qed.




Lemma envt_store_extend: forall M M' H G p,
    env_type M H G p ->
    env_type (M'++M) H G p.
Proof.
  intros. destruct H0 as [L [P W]]. 
  repeat split; auto. intros.
  destruct (W _ _  H0) as [vx [IH HVX]]; intuition.
  exists vx; intuition.
  eapply valt_store_extend in HVX; eauto.
Qed.


Lemma envt_extend_all: forall M M1 H G vx T1 p q1 qf,
    env_type M H G p ->
    val_type (M1 ++ M) H vx T1 ->
    closed_ty (length H) T1 ->
    closed_ql (length H) q1 ->
    psub qf (pdom H) ->
    env_type (M1 ++ M) (vx :: H) (T1 :: G) (por qf (pone (length H))).
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
Qed.


Lemma envq_extend_all: forall H vx p q1 qf,
    env_qual H p ->
    psub (pand (vars_locs H qf) (val_locs vx)) pempty ->
    closed_ql (length H) q1 ->
    psub qf p ->
    psub p (pdom H) ->
    env_qual (vx :: H) (por qf (pone (length H))).
Proof.
  intros.

  eapply envq_extend.
  eapply envq_tighten.
  eauto.
  eauto.
  eauto.
  unfoldq. intuition.

  (* now prove separation *) 
  intros.

  unfoldq. unfoldq.
  eapply H1. intuition.
  exists x. intuition.
  destruct H7.
  exists x0. intuition. eauto.
  destruct H7.
  eauto.
Qed.




Lemma envt_extend_nosep: forall M H G v T q p,
    env_type M H G p ->
    closed_ty (length H) T ->
    closed_ql (length H) q ->
    val_type M H v T ->
    env_type M (v::H) (T::G) p.
Proof. 
  intros. destruct H0 as [L [P W]]. 
  repeat split; auto.
  - simpl. eauto.
  - unfoldq. simpl. intuition.
  - intros. simpl in *. rewrite <-L in *.
    bdestruct (x =? (length H)); intuition; subst.
    + inversion H0. subst. exists v. intuition.
      eapply valt_extend1; eauto.
    + destruct (W _ _ H0); eauto.
      unfoldq. intuition.
      eexists. intuition. eauto.
      eapply valt_extend1; eauto.
      eapply valt_closed; eauto.
Qed.

Lemma envq_extend_nosep: forall H v q p,
    env_qual H p ->
    closed_ql (length H) q ->
    psub p (pdom H) ->
    env_qual (v::H) p.
Proof. 
  intros. unfold env_qual in *. 
  - intros. unfoldq. destruct H4, H6. 
    rewrite indexr_skip in H4.
    rewrite indexr_skip in H6.
    eauto.
    eapply H2 in H5. lia.
    eapply H2 in H3. lia.
Qed.


Lemma envt_extend_all_nosep: forall M M1 H G vx T1 p q1 qf,
    env_type M H G p ->
    val_type (M1 ++ M) H vx T1 ->
    closed_ty (length H) T1 ->
    closed_ql (length H) q1 ->
    psub qf (pdom H) ->
    env_type (M1 ++ M) (vx :: H) (T1 :: G) qf.
Proof.
  intros.
  eapply envt_extend_nosep; eauto.
  eapply envt_store_extend; eauto.
  eapply envt_tighten; eauto.
Qed.

Lemma envq_extend_all_nosep: forall H vx p q1 qf,
    env_qual H p ->
    closed_ql (length H) q1 ->
    psub qf p ->
    psub p (pdom H) ->
    env_qual (vx :: H) qf.
Proof.
  intros.
  eapply envq_extend_nosep; eauto.
  eapply envq_tighten; eauto.
  unfoldq. intuition. 
Qed.






Lemma env_type_store_wf: forall M H G p q,
    env_type M H G p ->
    psub (vars_locs H q) (pdom M).
Proof.
  intros. destruct H0 as [L [P W1]]; intuition.
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
    psub (var_locs H x) (pdom M).
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
    (WFE: env_type M E env p)
    (SEP: env_qual E p),
    psub q p ->
    psub q' p ->
    pand (vars_locs E q) (vars_locs E q') = vars_locs E (pand q q').
Proof.
  intros. eapply functional_extensionality.
  intros. eapply propositional_extensionality.
  destruct WFE as [L [P W]].
  intuition.
  - destruct H1 as [[? [? ?]]  [? [? ?]]].
    assert (x0 = x1). eapply SEP; eauto. subst x1.
    exists x0. unfoldq. intuition.
  - destruct H1 as [? [? [? [? ?]]]].
    unfoldq. intuition.
    exists x0. intuition. exists x1. intuition.
    exists x0. intuition. exists x1. intuition.
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



Lemma env_wf_contra: forall M E G p k1 x,
    env_type M E G p ->
    ~ (x < length M) ->
    vars_locs E k1 x ->
    False.
Proof.
  intros. eapply H0. eapply env_type_store_wf; eauto. 
Qed.


Lemma env_sep_contra: forall E p k1 k2,
    env_qual E p ->
    psub (pand k1 k2) pempty -> forall x,
    vars_locs E k1 x ->
    vars_locs E k2 x ->
    psub k1 p ->
    psub k2 p ->
    False.
Proof.
  intros.
  rename H into SEP. unfoldq. intuition.
  destruct H1, H2, H, H1.
  assert (x0 = x1). eapply SEP; eauto.
  subst x1. eauto. 
Qed.

Lemma separation: forall M M' H G p vf vx qf q1
    (WFE: env_type M H G p)
    (SEP: env_qual H p)
    (HQF: val_qual M H vf p qf)
    (HQX: val_qual (M'++M) H vx p q1),
    psub (val_locs vf) (pdom (M'++M)) ->
    psub (pand qf q1) pempty ->
    psub qf p ->
    psub q1 p -> 
    psub (pand (val_locs vf) (val_locs vx)) pempty.
Proof. 
  intros. unfoldq. intuition.
  bdestruct (x <? length M).
  - destruct (HQF x). intuition.
    destruct (HQX x). rewrite app_length. intuition.
    assert (x0 = x1). eapply SEP; intuition; eauto.
    eapply H1. subst x0. intuition; eauto.
  - bdestruct (x <? length (M'++M)).
    + destruct (HQX x). intuition.
      (* fresh loc in vf, also occurs in vx --> can't happen *)
      assert (psub (vars_locs H (pone x0)) (pdom M)) as L. {
        eapply env_type_store_wf. eauto. 
      }
      assert (x < length M). {
        eapply L. unfoldq. exists x0. intuition.
      }
      lia.
    + (* fresh loc in vx, bigger than vf *)
      eapply H0 in H5. lia.
Qed.



(* ---------- store typing lemmas ---------- *)


Lemma storet_length: forall S M,
    store_type S M ->
    length S = length M.
Proof.
  intros. destruct H. eapply H.
Qed.

Lemma storeq_restrict: forall S M E S1 M1 v1 v2 p k1 k2,
    store_qual S M E S1 M1 v1 (plift p) (plift k1) ->
    psub (plift k1) (plift k2) ->
    psub (val_locs v2) (val_locs v1) -> 
    store_qual S M E S1 M1 v2 (plift p) (plift k2).
Proof.
  intros.
  unfold store_qual in *. unfold st_killed in *.
  unfoldq. intuition.
  destruct (H x) as [H_K | [H_k | H_fresh]]. eauto. 
  - left. eauto.
  - right. left. destruct H_k. exists x0. unfoldq. intuition.
  - right. right. intuition.
Qed.

Lemma storeq_seq: forall S M E G S1 S2 M1 M2 v1 v2 p k1 k2 q2,
    env_type M E G p ->
(*    psub (pand k1 k2) pempty -> *) True ->
(*    psub (pand k1 q2) pempty -> *) True ->
    store_qual S M E S1 M1 v1 p k1 ->
    store_qual S1 (M1 ++ M) E S2 M2 v2 p k2 -> 
     val_qual (M1++M) E v2 p q2 -> 
    store_qual S M E S2 (M2 ++ M1) v2 p (por k1 k2).
Proof.
  intros. rename H2 into SK1. rename H3 into SK2.
  rename H into WFE.
  rename H0 into SEPk1k2.
  rename H1 into SEPk1q2.
  rename H4 into VQ.
  intros ? ?. destruct (SK2 x) as [H_K | [H_k | H_fr]]. eauto.
  - eapply SK1 in H_K. destruct H_K as [H1_K | [H1_k | H1_fr]].
    + left. eauto.
    + right. left. destruct H1_k. exists x0. unfoldq. intuition.
    + right. right. unfoldq. intuition. repeat rewrite app_length in *. lia.
      (* destruct (VQ x). rewrite app_length. intuition. *)
      eapply env_wf_contra; eauto. eapply VQ. intuition. 
  - right. left. destruct H_k. exists x0. unfoldq. intuition.
  - right. right. unfoldq. rewrite <-app_assoc. intuition.  
    rewrite app_length in *. lia.
Qed.

Lemma storet_extend: forall S M H vx,
    store_type S M ->
    val_type M H vx TBool ->
    store_type (Some vx :: S) ((fun v => val_type M H v TBool) :: M).
Proof.
  intros.
  unfold store_type in *. intuition.
  simpl. eauto. unfoldq. intuition. simpl. intuition.
  bdestruct (l =? length M).
  - subst l. destruct vx; try inversion H1. simpl in *. 
    bdestruct (length M =? length S); intuition.
    bdestruct (length M =? length M); intuition.
    right. 
    exists b; intuition.
  - rewrite indexr_skip in H0; eauto.
    bdestruct (l =? length S). lia. 
    eapply H3. eauto. 
Qed.

Lemma storeq_extend: forall S M E S1 M1 vx vt p k,
    store_qual S M E S1 M1 vx (plift p) (plift k) ->
    store_qual S M E (Some vx :: S1) (vt :: M1) (vref (length (M1 ++ M))) (plift p) (plift k).
Proof.
  intros.
  unfold store_qual in *. unfold st_killed in *. 
  rewrite val_locs_ref. unfoldq. intuition.
  simpl in H0. bdestruct (x =? length S1). inversion H0. 
  destruct (H x) as [H_K | [H_k | H_fresh]]. eauto.
  - left. eauto.
  - right. left. destruct H_k. exists x0. eauto.
  - right. right. repeat rewrite app_length in *. simpl. intuition. 
Qed.


Lemma storet_free: forall S M i,
    store_type S M ->
    store_type (update S i None) M.
Proof.
  intros.
  unfold store_type in *. intuition.
  rewrite <-update_length. eauto.
  bdestruct (i =? l).
  - subst i. left. rewrite update_indexr_hit. eauto. rewrite H0. eapply indexr_extend. eauto. eauto. 
  - rewrite update_indexr_miss. eauto. eauto.
Qed.

Lemma storeq_free: forall S M E S1 M1 i p q k,
    store_type S M ->
    store_type S1 (M1++M) ->
    store_qual S M E S1 M1 (vref i) (plift p) (plift k) ->
    val_qual M E (vref i) (plift p) (plift q) ->
    store_qual S M E (update S1 i None) M1 (vbool false) (plift p) (plift (qor k q)).
Proof.
  intros.
  assert (store_qual S M E S1 M1 (vbool false) (plift p) (plift (qor k q))).
  eapply storeq_restrict. eauto. rewrite plift_or. unfoldq. intuition.
  rewrite val_locs_bool. rewrite val_locs_ref. unfoldq. intuition. 

  assert (length S = length M). destruct H. eauto. 
  assert (length S1 = length (M1++M)). destruct H0. eauto. 

  unfold store_qual in *. unfold st_killed in *. unfoldq. intuition.

  assert (x < length (M1++M)). {
    rewrite indexr_extend in H6.
    rewrite <-update_length in H6.
    rewrite <-H5. eapply H6.
  }
  bdestruct (x <? length M).
  - bdestruct (i =? x).
    + subst x. destruct (H2 i). rewrite val_locs_ref. intuition.
      right. left. exists x. rewrite plift_or. intuition. right. eauto.
    + rewrite update_indexr_miss in H6. 2: eauto.
      destruct (H1 x) as [H_K | [H_k | H_fresh]]. eauto.
      left. eauto.
      right. left. destruct H_k. exists x0. rewrite plift_or. unfoldq. intuition.
      right. right. rewrite val_locs_bool. intuition.
  - right. right. rewrite val_locs_bool. intuition. 
    Unshelve.
    eapply [].
Qed.


Lemma storet_update: forall S M H i vx v,
    indexr i S = Some (Some v) ->
    store_type S M ->
    val_type M H (vref i) (TRef TBool) ->
    val_type M H vx TBool -> 
    store_type (update S i (Some vx)) M.
Proof. 
  intros. destruct H1 as [L ST].
  split. 
  (* length *)
  rewrite <-update_length. eauto.
  (* lookup *) {
    intros.
    eapply ST in H1 as XX. destruct XX.
    + bdestruct (i =? l). subst l.
      - rewrite H0 in H4. inversion H4. 
      - rewrite update_indexr_miss. eauto. eauto.
    + bdestruct (i =? l). subst l.
      - right. rewrite update_indexr_hit. 
        destruct vx; try inversion H3.
        exists b. intuition.
        apply indexr_var_some' in H1. lia.
      - right. rewrite update_indexr_miss; auto. 
  }
Qed.


Lemma safeq_split: forall S M E p e q,
    safe_qual S M E p (por e q) ->
    safe_qual S M E p e /\
      safe_qual S M E p q.
Proof.
  intros. 
  unfold safe_qual in *. unfoldq. intuition.
  destruct H2. 
  destruct (H x). intuition. exists x0. intuition.
  destruct H2. 
  destruct (H x). intuition. exists x0. intuition.
Qed. 
  

Lemma valq_safe: forall S M E G S1 M1 v p pe q k,
    env_type M E G p ->
    env_qual E pe -> 
    store_type S M -> 
    safe_qual S M E p q ->
    store_qual S M E S1 M1 v p k ->
    psub (pand k q) pempty ->
    psub k pe ->
    psub q pe ->
    val_qual M E v p q ->
    psub (val_locs v) (pnot (st_killed S1 (M1++M))).
Proof.
  intros. unfold safe_qual, store_qual, pnot, st_killed in *. unfoldq. intuition.

  destruct (H3 x) as [H_K | [H_k | H_fresh]]. eauto.
  - assert (x < length M).
    rewrite indexr_extend in H_K. destruct H1. rewrite e in H_K. eapply H_K.
    destruct (H7 x). intuition.
    destruct (H2 x). intuition.
  - assert (x < length M). eapply env_type_store_wf; eauto. (* eapply H_k. *)
    destruct (H3 x). intuition.
    destruct (H2 x). intuition.
    destruct H9. 
    destruct H_k.
    destruct (H7 x). intuition.
    assert (x1 = x0). {
      eapply H0. (* SEP. *)
      eapply H6. eapply H12. eapply H12.
      eapply H5. eapply H9. eapply H9.
    }
    subst x1. eapply H4. split. eapply H9. eapply H12.
  - destruct H_fresh. eauto.
    Unshelve.
    apply []. 
Qed.

Lemma safeq_extend: forall S M E G S1 M1 v p pe q k,
    env_type M E G p ->
    env_qual E pe ->
    store_type S M -> 
    psub (pand k q) pempty ->
    psub k pe ->
    psub q pe -> 
    safe_qual S M E p q ->
    store_qual S M E S1 M1 v p k ->
    safe_qual S1 (M1++M) E p q.
Proof.
  intros.
  rename H6 into SK. 
  unfold safe_qual in *. 
  unfoldq. intuition. 
  destruct (SK x) as [H_K | [H_k | H_fr]]. eauto.
  - (* K *) destruct (H5 x). intuition.
  - (* k *) eapply env_sep_contra; eauto. 
  - (* fr *) unfoldq. eapply env_wf_contra; eauto. eapply H_fr. 
Qed.

  

Lemma se_refl: forall S1 p,
    store_effect S1 S1 p.
Proof.
  intros. intros ? ? ? ?. eauto. 
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


(* ---------- main lemmas ---------- *)

Lemma sem_app1: forall S'' M M' M'' H Hf G T1 T2 ey vx pv p q1 q2 qf e2 k2 (q2x e2x k2x: bool)
    (WFE: env_type M H G p)
    (SEP1: True) (* env_qual H p *)
    (SEP2: env_qual H (por (por (plift e2) (if e2x then q1 else pempty))
             (por (plift k2) (if k2x then q1 else pempty))))
    (HVF: val_type (M'++M) H (vabs Hf pv ey) (TFun T1 T2 q2 e2 k2 q2x e2x k2x))
    (HQF: val_qual M H (vabs Hf pv ey) p qf)
    (HVX: val_type (M''++M'++M) H vx T1)
    (HQX: val_qual (M'++M) H vx p q1),
    (if e2x || k2x then psub (pand (por (plift e2) (plift k2)) q1) pempty else True) ->
    True -> (* (if e2x then psub qf p else True) -> *)
    True -> (* (if e2x || k2x then psub q1 p else True)  -> *)
    (* exists vy, exp_type H ey vy T2 p q2. *) (* not exactly this!! *)
    psub (pand (st_killed S'' (M''++M'++M))
            (por (vars_locs H (plift e2))
               (if e2x then (val_locs vx) else pempty))) pempty ->
    store_type S'' (M''++M'++M) ->
    exists S''' M''' vy,
      tevaln S'' (vx::Hf) ey S''' vy /\
        store_type S''' (M'''++M''++M'++M) /\
        store_effect S'' S'''
          (por (vars_locs H (por (plift e2) (plift k2)))
             (if e2x || k2x then val_locs vx else pempty)) /\
        (* store_qual S'' (M''++M'++M) H S''' M''' vy p (plift k2) /\ *)
        psub (st_killed S''' (M'''++M''++M'++M))
          (por (st_killed S'' (M''++M'++M))
             (por (vars_locs H (plift k2))
                (por (if k2x then (val_locs vx) else pempty)
                   (pdiff (pdiff (pdom (M'''++M''++M'++M)) (pdom (M''++M'++M)))
                      (val_locs vy))) )) /\ 
        val_type (M'''++M''++M'++M) H vy T2 /\
        val_qual M H vy p (por (plift q2) (if q2x then q1 else pempty)) /\
        psub
          (pand (pdom (M''++M'++M)) (val_locs vy))
          (por (vars_locs H (plift q2))
             (if q2x then (val_locs vx) else pempty)).
Proof.
  
  intros. apply valt_wf in HVF as WFQF. apply valt_wf in HVX as WFQX.
  destruct HVF; intuition.
  rename H12 into HVF.
  destruct (HVF S'' M'' vx) as [S''' [M''' [vy [IW3 HVY]]]].
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


  (* env_qual H e2 *)
  eapply envq_tighten. eauto. unfoldq. intuition.
  
  (* TODO 2: SEPARATION *)

  assert (por (if e2x then q1 else pempty) (if k2x then q1 else pempty) =
            (if e2x || k2x then q1 else pempty)) as R. {
    eapply functional_extensionality. intros.
    eapply propositional_extensionality. intros.
    destruct e2x; destruct k2x; simpl; unfoldq; intuition. }
  
  assert (forall A B C D, por (por A B) (por C D) = por (por A C) (por B D)) as RR. {
    intros. eapply functional_extensionality. 
    intros. eapply propositional_extensionality. 
    unfoldq; intuition. }

  rewrite RR,R in SEP2. 

  destruct (e2x || k2x).
  intros ? ?. destruct H11. 

  destruct (HQX x). split. 2: eauto. eapply env_type_store_wf. eapply envt_store_extend. eauto. eauto. destruct H11. destruct (H0 x1). split. intuition. 
  assert (x0 = x1). 
  eapply SEP2.
  right. intuition. intuition. eauto. 
  left. intuition.  intuition. subst x0. intuition.
  eauto. 


  (* TODO 2a: EFFECT SEPARATION *)
  eauto. 
  
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
  rename H16 into HQY.
  remember (vabs Hf pv ey) as vf.
  unfold val_qual in *.
  
  unfoldq. intros. 
  destruct (HQY x). repeat rewrite app_length. intuition.
  + (* part of function *)
    destruct H16. destruct H16.
    exists x0. intuition.
    
  + (* part of argument *)
    destruct q2x; try contradiction.
    destruct (HQX x). repeat rewrite app_length. intuition. 
    exists x0. intuition.
  }

Qed.



Lemma sem_abs1: forall S M M1 H G T1 T2 t vx p q2 qf e2 k2 (q2x e2x k2x: bool)
    (WFE: env_type M H G (plift p))
    (HVX: val_type (M1 ++ M) H vx T1) (* arg from valt *)
    (SEP0: env_qual H (por (plift e2) (plift k2)))
    (SEPE : if e2x || k2x then psub (pand (vars_locs H (por (plift e2) (plift k2))) (val_locs vx)) pempty else True)
    (IHW : (* induction *)
      env_type (M1 ++ M) (vx :: H) (T1 :: G) (plift p) -> 
      (*env_type (M1 ++ M) (vx :: H) (T1 :: G) (plift (qor qf (if e2x then qone (length H) else qempty))) -> *)
      env_qual (vx :: H)
        (plift (qor (qor e2 k2) (if e2x || k2x then qone (length H) else qempty))) ->
        exists (S'' : stor) (M'' : stty) (vy : vl),
          exp_type S (M1 ++ M) (vx :: H) t S'' M'' vy T2 (plift (qor qf (if e2x then qone (length H) else qempty)))
            (plift (qor q2 (if q2x then (qone (length H)) else qempty)))
            (plift (qor e2 (if e2x then (qone (length H)) else qempty)))
            (plift (qor k2 (if k2x then (qone (length H)) else qempty))))
    (HCLT1: closed_ty (length H) T1)        
    (HCLT2: closed_ty (length H) T2)
    (HCLQ:  closed_ql (length H) qf)
    (HCLE:  closed_ql (length H) e2)
    (HCLK:  closed_ql (length H) k2)
    (HCLQ2:  closed_ql (length H) q2)
    (QFINP: psub (plift qf) (pdom H))
(*    (QFINP: psub (plift qf) (plift p)) *)
    (Q2INQF: True (* psub (plift q2) (plift qf) *) )

    (STY:   store_type S (M1 ++M)),
  exists (S'' : stor) (M'' : stty) (vy : vl),
    tevaln S (vx :: H) t S'' vy /\
      store_type S'' (M'' ++ M1 ++ M) /\
      store_effect S S''
        (por (vars_locs H (por (plift e2) (plift k2)))
           (if e2x || k2x then val_locs vx else pempty)) /\
      psub (st_killed S'' (M'' ++ M1 ++ M))
        (por (st_killed S (M1 ++ M))
           (por (vars_locs H (plift k2))
              (por (if k2x then (val_locs vx) else pempty)
                 (pdiff (pdiff (pdom (M''++M1++M)) (pdom (M1++M))) (val_locs vy) )))) /\  (* !!! TODO: add M''++M1 - locs vy !!! *)
      val_type (M'' ++ M1 ++ M) H vy T2 /\
      psub (pand (pdom (M1 ++ M)) (val_locs vy))
        (por (vars_locs H (plift q2))
           (if q2x then (val_locs vx) else pempty)).
Proof.
  intros.
  destruct (IHW) as [S2 [M2 [vy IHW1]]]. {
    (* rewrite val_locs_abs in SEP. *)
    (* rewrite plift_or, plift_if, plift_one, plift_empty.
    destruct e2x.
    eapply envt_extend_all; eauto. *)
    eapply envt_extend_all_nosep; eauto. unfoldq. intuition.
    eapply WFE. eauto. 
  } {
    (* envq *)
    rewrite plift_or, plift_if, plift_one, plift_empty, plift_or.

    destruct (e2x || k2x).
    eapply envq_extend_all; eauto. unfoldq. intuition. unfoldq. intuition. 
    eapply envq_extend_all_nosep; eauto. unfoldq. intuition. unfoldq. intuition.
  }
  destruct IHW1 as [? IHW1]. 
  exists S2, M2, vy. intuition.

  (* store_effect *)

  eapply se_sub. eauto. intros ? [? [OR ?]].
  rewrite plift_or, plift_if, plift_one, plift_empty in OR.
  rewrite plift_or, plift_if, plift_one, plift_empty in OR.
  destruct OR as [[HE | HEX] | [HK | HKX]].
  (* e2 *) left. exists x0. split. left. eauto. eapply var_locs_shrink; eauto.
  (* e2x *) destruct e2x. right. simpl. eapply aux1. replace x0 with (length H) in H5. eauto. unfoldq. intuition.
  (* k2 *) left. exists x0. split. right. eauto. eapply var_locs_shrink; eauto.
  (* k2x *) replace (e2x || k2x) with (k2x || e2x). 2: eauto with bool.
  destruct k2x. right. simpl. eapply aux1. replace x0 with (length H) in H5. eauto. unfoldq. intuition.
  
  (* eapply storet_restrict. eauto. *)
  rewrite plift_or, plift_if, plift_one, plift_empty in H2. 
  unfoldq. intros. destruct (H2 x) as [H_K | [H_k | H_fresh ]]. eauto.
  (* K *) left. eauto.
  (* k *) destruct H_k. destruct H7. rewrite plift_or, plift_if, plift_one, plift_empty in H7. 
  bdestruct (x0 =? length H).
  destruct k2x. subst x0.
  destruct H7. eapply HCLK in H7. lia.
  right. right.
  destruct H8. destruct H8. rewrite indexr_head in H8; eauto. inversion H8. subst x0.
  intuition.
  (* k2x = false *)
  subst x0. destruct H7. eapply HCLK in H7. lia. unfoldq. contradiction.
  (* x0 <> length H *)
  destruct H7. 
  right. left. exists x0. intuition. destruct H8. rewrite indexr_skip in H8. exists x1. eauto. lia. 
  destruct k2x. unfoldq. lia. unfoldq. contradiction.

  right. right. right. eauto. 

  
  (* TODO 2: VAL_TYPE *)

  (* go from
        T2 (qor (qand p qf) (qone (length H))) (qor q2 (qone (length H)))
     to
        T2 (qand p qf) (qand p (qand qf q2))
   *)
  eapply valt_extend1; eauto.

  (* TODO 3: VAL_QUAL *)
  
  (* vy < vf \/ vx *)

    apply valt_wf in HVX. apply valt_wf in H4.
  rename H6 into HVY.
  
  unfoldq. intuition.
  destruct (HVY x). eauto.
  rewrite plift_or, plift_if, plift_one, plift_empty in H5.
  unfoldq.
  destruct H5. destruct H5.
  destruct q2x. 
  bdestruct (x0 =? length H).
  - (* from arg *)
    right. destruct H8 as [? [? ?]]. subst x0. rewrite indexr_head in H8. inversion H8. eauto.
  - (* from func *)
    left. 
    exists x0. intuition. destruct H8 as [? [? ?]]. rewrite indexr_skip in H8. exists x1. split; eauto. lia.
    
  (* q2x is false, hence can't be arg *)
  - destruct H8.
    assert (x0 < length H). { eapply HCLQ2 in H5. eauto. }
    left. 
    exists x0. intuition. rewrite indexr_skip in H10. exists x1. split; eauto. lia.

  - (* arg? *) right.
    destruct q2x. subst x0. rewrite indexr_head in H8.
    destruct H8 as (? & ? & ?). congruence.
    contradiction.

Qed.





(* if well-typed, then result is an actual value (not stuck and not a timeout),
   for large enough n *)

Theorem full_total_safety : forall t G T p q e k,
    has_type G t T p q e k ->
    forall M E, env_type M E G (plift p) ->
                env_qual E (por (plift e) (plift k)) ->
    forall S, store_type S M ->
    safe_qual S M E (plift p) (plift e) ->
    exists S' M' v, exp_type S M E t S' M' v T (plift p) (plift q) (plift e) (plift k).
Proof.
  intros ? ? ? ? ? ? ? W. 
  induction W; intros ? ? WFE SEP; 
  destruct (wf_env_type M E env (plift p) WFE) as [LE [DE PC]]; intuition. 
  
  - (* Case "True". *) exists S. exists []. exists (vbool true). split.
    exists 0. intros. destruct n. lia. intuition. simpl. intuition.
    eapply se_refl. 
    unfold store_qual. unfoldq. intuition. 
    eapply valq_bool.
    
  - (* Case "False". *) exists S. exists []. eexists. split.
    exists 0. intros. destruct n. lia. intuition. simpl. intuition.
    eapply se_refl.
    unfold store_qual. unfoldq. intuition.
    eapply valq_bool.
    
  - (* Case "Var". *)
    destruct WFE as [? [? WFE]].
    destruct (WFE x T H) as [vx [HI ?]]. eauto.
    exists S. exists []. eexists. 
    split. exists 0. intros. destruct n. lia. simpl. rewrite HI. reflexivity.
    split. simpl. eauto.
    split. eapply se_refl.
    split. unfold store_qual. unfoldq. intuition. 
    split. simpl. eauto. 
    
    (* valq *)
    unfoldq. rewrite plift_one.
    unfoldq. intuition.
    exists x. intuition.
    exists vx. intuition.
    
  - (* Case "Ref". *)
    destruct (IHW M E WFE SEP S) as [S1 [M1 [vx [IW1 [ST1 [SE1 [HSK [HVX HQX]]]]]]]]; eauto.
    remember (fun v => val_type (M1++M) E v TBool) as vt.
    exists (Some vx::S1).
    exists (vt::M1).
    exists (vref (length (M1++M))). split.
    + (* expression evaluates *)
      eapply storet_length in ST1.
      destruct IW1 as [n1 IW1].
      rename S into Sx.
      exists (S n1).
      intros. destruct n. lia.
      simpl. rewrite IW1. rewrite ST1. eauto. lia.
    + (* result well typed *)
      split. 2: split. 3: split. 4: split. 
      
      simpl. subst. eapply storet_extend. eauto. eauto.

      (* extract lemma se_extend? *)
      intros ? ? ? ?. bdestruct (l <? length S).
      rewrite indexr_skip. eapply SE1. eauto. eauto.
      assert (length S = length M). eapply H.
      assert (length S1 = length M1 + length M). rewrite <-app_length. eapply ST1.
      lia. 
      eapply indexr_var_some' in H2. lia. 

      eapply storeq_extend. eauto. 

      simpl. intuition. 
      bdestruct (length (M1 ++ M) =? length (M1 ++ M)); intuition.
      exists vt; intuition.
      
      eapply valq_fresh. 

  - (* Case "Get". *)
    rewrite plift_or in *. 
    eapply safeq_split in H3. destruct H3.
    assert (env_qual E (por (plift e) (plift k))) as SEP1. eapply envq_tighten. eauto. unfoldq. intuition.
    destruct (IHW M E WFE SEP1 S) as [S1 [M1 [vx [IW1 [ST1 [HSE [HKS [HVX HQX]]]]]]]]; eauto.
    clear SEP1.
    
    destruct vx; try solve [inversion HVX]. simpl in HVX.
    destruct (HVX) as [CL [vt MI]].

    assert (~ st_killed S1 (M1++M) i). {
      unfold store_qual in *.  unfold st_killed.
      bdestruct (i <? length M).
      destruct (HQX i). rewrite val_locs_ref. unfoldq; intuition.
      specialize (HKS i); intuition. 
      unfold st_killed in H6. rewrite val_locs_ref in H6. 
      destruct H6. eapply H4. unfold st_killed; intuition. unfold pand. split. eauto. 
      unfold vars_locs. exists x; intuition.
      destruct H6. unfold vars_locs in H6.
      destruct H6 as [? [? ?]].
      assert (x = x0). eapply SEP; eauto. 
      unfoldq; intuition. unfoldq; intuition.
      subst. eapply H. unfoldq; intuition. eauto. auto.
      unfoldq; intuition.
      specialize (HKS i); intuition.
      rewrite val_locs_ref in H9. unfoldq; intuition.
      unfold st_killed in H10. apply indexr_var_some' in H10. destruct H2; intuition.
      assert (psub (vars_locs E (plift k)) (pdom M)).
      eapply env_type_store_wf with (q := (plift k)) in WFE.
      unfoldq; intuition. specialize (H10 i); intuition.
      unfoldq; intuition. 
    }
    
    remember ST1 as ST1x. clear HeqST1x.
    destruct ST1 as [LST ST1].
    destruct (ST1 i vt) as [|[vy SI]]. eauto. contradiction.

    exists S1, M1, (vbool vy). split.
    + (* expression evaluates *)
      destruct IW1 as [n1 IW1].
      rename S into Sx.
      exists (S n1).
      intros. destruct n. lia.
      simpl. rewrite IW1. rewrite SI. eauto. lia.
    + (* result well typed *)
      split.
      auto.
      split.
      eapply se_sub. eauto. intros ? [? ?]. exists x0. unfoldq. intuition. 
      split.
      eapply storeq_restrict; eauto.
      unfoldq. intuition. 
      rewrite val_locs_ref, val_locs_bool. unfoldq. intuition.

      split.
      constructor.

      eapply valq_bool. 
  
  - (* Case "Put". *)
    repeat rewrite plift_or in *.
    rename H3 into SQ.
    eapply safeq_split in SQ as SQ'. destruct SQ'.
    assert (env_qual E (por (plift e1) (plift k1))) as SEP1. eapply envq_tighten. eauto. unfoldq. intuition.
    destruct (IHW1 M E WFE SEP1 S) as [S1 [M1 [vr [IW1 [ST1 [HSEF1 [HSK1 [HVR HQR]]]]]]]]; eauto.
    assert (env_type (M1++M) E env (plift p)) as WFE1. eapply envt_store_extend. eauto.
    assert (env_qual E (por (plift e2) (plift k2))) as SEP2. eapply envq_tighten. eapply SEP. unfoldq. intuition. 
    destruct (IHW2 (M1++M) E WFE1 SEP2 S1) as [S2 [M2 [vx [IW2 [ST2 [HSEF2 [HSK2 [HVX HQX]]]]]]]]; eauto.
   
    rename H4 into SQ2.
    eapply safeq_split in SQ2. destruct SQ2 as [SQ21 SQ22]. eapply safeq_extend in SQ21. eauto. eauto. eapply SEP. 2: eapply H. all: eauto.  
    intros ? ?. unfoldq; intuition.
    intros ? ?. unfoldq; intuition.
    
    remember HVR as HVR'. clear HeqHVR'. 
    destruct vr; try solve [inversion HVR]. simpl in HVR.
    destruct (HVR) as [CL [vt MI]].
    remember ST2 as ST2x. clear HeqST2x.
    destruct ST2 as [LST ST2].

    assert (indexr i S2 <> Some None). {
      unfold store_qual, st_killed in HSK1, HSK2.
      unfoldq; intuition. rewrite val_locs_ref in *.
      bdestruct (i <? length M).
      destruct (HQR i) as [? [? ?]]; intuition.
      specialize (HSK2 i);  specialize (HSK1 i); intuition.
      eapply H4. unfold st_killed. unfoldq; intuition. eauto.
      exists x; intuition.

      destruct H11 as [? [? ?]]. 
      unfold env_qual in SEP. 
      assert (x0 = x). eapply SEP; eauto.
      subst. eapply H0; eauto. (* q1 and k1 are separate *)

      destruct H11 as [? [? ?]]. 
      unfold env_qual in SEP.
      assert (x0 = x). eapply SEP; eauto. subst. eapply H1; eauto. (* q1 and k2 are separate *)
      repeat rewrite app_length in *. lia.

      specialize (HSK2 i); intuition. specialize (HSK1 i); intuition.
      apply indexr_var_some' in H11. destruct H2; intuition.
      assert (psub (vars_locs E (plift k1)) (pdom M)).    
      eapply env_type_store_wf with (q := (plift k1)) in WFE; auto.
      unfoldq; intuition. specialize (H11 i); intuition.

      assert (psub (vars_locs E (plift k2)) (pdom M)).    
      eapply env_type_store_wf with (q := (plift k2)) in WFE; auto.
      unfoldq; intuition. specialize (H10 i); intuition.
      
      apply indexr_var_some' in MI. lia.
      
    } 
    assert (indexr i (M2++M1++M) = Some vt). rewrite indexr_extend in MI. eapply MI.
    specialize(ST2 i vt); intuition.
    destruct H10 as [vy SI]. 
    exists (update S2 i (Some vx)).
    exists (M2++M1).
    exists (vbool true). split. 2: split. 3: split. 4: split. 5: split.
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
    
    + rewrite <-app_assoc. eapply storet_update; eauto.
      eapply valt_store_extend. eauto.
      
    + (* effects *) 
      intros ? ?. intros.
      eapply indexr_var_some' in H10 as H10'.
      bdestruct (l <? length S); intuition.
      bdestruct (i =? l). subst.
      destruct H9; intuition. 
      unfoldq; intuition. 
      destruct (HQR l); intuition. destruct H2; intuition. rewrite val_locs_ref. unfoldq; intuition.
      exists x; intuition. intuition.
      rewrite update_indexr_miss. 
      assert (indexr l S1 = Some v). eapply HSEF1.
      unfoldq; intuition. destruct H9; intuition. 
      destruct H13 as [? [? ?]]. exists x; intuition. intuition. 
      eapply HSEF2. unfoldq; intuition.
      destruct H9; intuition. 
      destruct H14 as [? [? ?]]. exists x; intuition. intuition. auto. 

    + unfold store_qual. unfold st_killed.
      intros ? ?. unfoldq; intuition.
      bdestruct (i =? x). subst x.
      rewrite update_indexr_hit in H9. inversion H9. apply indexr_var_some' in SI. auto.
      rewrite update_indexr_miss in H9; auto.
      rewrite val_locs_bool.
      unfold store_qual, st_killed in *. unfoldq; intuition.
      specialize (HSK2 x); intuition.
      specialize (HSK1 x); intuition.
      right. left. destruct H11 as [? [? ?]].
      exists x0; intuition.
      right. right. intuition. rewrite <- app_assoc. rewrite app_length. lia. 
      right. left. destruct H11 as [? [? ?]].
      exists x0; intuition.
      right. right. rewrite <- app_assoc. intuition.
      rewrite app_length in H14. lia.      

    + constructor; auto. 

    + eapply valq_bool.
      
    
  - (* Case "Free". *)
    assert (env_qual E (por (plift e) (plift k))) as SEP1. eapply envq_tighten. eauto. rewrite plift_or. unfoldq. intuition.
    destruct (IHW M E WFE SEP1 S) as [S1 [M1 [vx [IW1 [SW1 [HSE [HKS [HVX HQX]]]]]]]]; eauto. 
    destruct vx; try solve [inversion HVX]. simpl in HVX.
    destruct (HVX) as [? [vy SI]].
    exists (update S1 i None).
    exists M1.
    exists (vbool false). split.
    + (* expression evaluates *)
      destruct IW1 as [n1 IW1].
      rename S into Sx.
      exists (S n1).
      intros. destruct n. lia.
      simpl. rewrite IW1. eauto. lia.
    + (* result well typed *)
      split. 2: split. 3: split. 4: split. 

      eapply storet_free. eauto. 

      (* se_free *)
      intros ? ? ? ?. bdestruct (i =? l).
      subst i. destruct H2.
      assert (length S = length M). eapply H. 
      bdestruct (l <? length M). 
      destruct (HQX l). rewrite val_locs_ref. unfoldq. intuition.
      rewrite plift_or. exists x. intuition. right. right. eauto. 
      eapply indexr_var_some' in H3. lia.
      rewrite update_indexr_miss. eapply HSE. intros ?. eapply H2.
      rewrite plift_or. 
      destruct H5. exists x. intuition. destruct H8. left. eauto. right. left. eauto.
      eauto. eauto. 

      eapply storeq_free. eauto. eauto. eauto. eauto. 
      
      simpl. eauto. 

      eapply valq_bool.
      
  - (* Case "App". *)

    rename H10 into H11.
    assert True. eauto.
    
    repeat rewrite plift_or in *. 
    repeat rewrite plift_if in *. 
    repeat rewrite plift_empty in *. 
    eapply safeq_split in H11; destruct H11.
    eapply safeq_split in H11; destruct H11.
    eapply safeq_split in H13; destruct H13.

    rename H13 into SAFE_E1.
    rename H14 into SAFE_E2.
    rename H12 into SAFE_E2X.


    assert (psub (pand (plift kf) (plift e2)) pempty). unfoldq. intuition.
    eapply H2. split. left. eauto. left. eauto. 

    assert (psub (pand (plift kf) (plift e2)) pempty). unfoldq. intuition.

    assert (psub (pand (plift kf) (if e2x then plift q1 else pempty)) pempty). unfoldq. intuition.
    eapply H2. split. left. eauto. right. eauto. 

    
    (* induction on both subexpressions: obtain vf, vx *)
    assert (env_qual E (por (plift ef) (plift kf))) as SEP1. eapply envq_tighten. eauto. unfoldq. intuition.
    
    destruct (IHW1 M E WFE SEP1 S) as [S1 [M1 [vf [IW1 [SW1 [SE1 [SQ1 [HVF HQF]]]]]]]]; eauto.
    clear SEP1.

    
    assert (env_type (M1++M) E env (plift p)) as WFE1. { eapply envt_store_extend. eauto. }
    (* assert (env_qual E (plift p)) as SEP1. { eauto. } *)

    eapply safeq_extend in SAFE_E1 as SAFE_E1'; eauto. 2: { intros ? ?. right. left. left. eauto. } 2: { intros ? ?. left. left. right. left. eauto. }

    eapply safeq_extend in SAFE_E2 as SAFE_E2'; eauto. 2: { intros ? ?. right. left. left. eauto. } 2: { intros ? ?. left. left. right. right. eauto. } 
    eapply safeq_extend in SAFE_E2X as SAFE_E2X'; eauto. 2: { intros ? ?. right. left. left. eauto. } 

    assert (env_qual E (por (plift e1) (plift k1))) as SEP2. eapply envq_tighten. eauto. unfoldq. intuition.
    destruct (IHW2 (M1++M) E WFE1 SEP2 S1) as [S2 [M2 [vx [IW2 [SW2 [SE2 [SQ2 [HVX HQX]]]]]]]]; eauto.
    clear SEP2.
    
    (* vf is a function value: it can eval its body *)
    destruct vf; try solve [inversion HVF].
    assert (exists S3 M3 vy,
               tevaln S2 (vx::l) t0 S3 vy /\
                 store_type S3 (M3++M2++M1++M) /\
                 store_effect S2 S3
                   (por (vars_locs E (por (plift e2) (plift k2)))
                      (if e2x || k2x then val_locs vx else pempty)) /\
                 psub (st_killed S3 (M3++M2++M1++M))
                   (por (st_killed S2 (M2++M1++M))
                      (por (vars_locs E (plift k2))
                         (por (if k2x then (val_locs vx) else pempty)
                            (pdiff (pdiff (pdom (M3++M2++M1++M)) (pdom (M2++M1++M)))
                               (val_locs vy))) )) /\ 
                 val_type (M3++M2++M1++M) E vy T2 /\
                 val_qual M E vy (plift p) (por (plift q2) (if q2x then (plift q1) else pempty)) /\
                 psub
                   (pand (pdom (M2++M1++M)) (val_locs vy))
                   (por (vars_locs E (plift q2))
                      (if q2x then (val_locs vx) else pempty))
           ) as HVY. {
      apply valt_wf in HVX as HVX'.
      eapply sem_app1. eauto. eauto.
      eapply envq_tighten. eauto. intros ? XX. destruct XX as [[XX|XX]|[XX|XX]].
        (* e2  *) left. left. right. right. eauto.
        (* e2x *) left. right. eauto.
        (* k2  *) right. left. right. right. eauto.
        (* k2x *) right. right. eauto.
      eauto. eauto. eauto. eauto. eauto. eauto. eauto. 

      (* effect sep *)

      eapply safeq_extend in SAFE_E2'. 8: eauto. all: eauto. 2: eauto. 
      (* eapply safeq_extend in SAFE_E2X'. 5: eauto. all: eauto. *)
      
      intros ? YY.
      destruct YY as [? YY]. destruct YY.
      (* e2 *) eapply SAFE_E2'. unfoldq. intuition. 
      (* e2x/q1 *) destruct e2x. 2: { unfoldq. intuition. }
      eapply valq_safe. 4: eapply SAFE_E2X'.
      eauto. eauto. eauto. eauto. all: eauto.

      unfoldq. intuition. eapply H2. split. right. eauto. right. eauto.

      intros ? ?. right. left. right. left. eauto.
      intros ? ?. left. right. eauto. 

      unfoldq. intuition. eapply H2. split. right. eauto. left. eauto.

      intros ? ?. right. left. right. left. eauto.
      intros ? ?. left. left. right. right. eauto. 
      }

    destruct HVY as [S3 [M3 [vy [IW3 [SW3 [SE3 [SQ3 [HVY [HQY HQY2]]]]]]]]].

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


      repeat rewrite plift_or in *.
      repeat rewrite plift_if in *.
      repeat rewrite plift_empty in *.

      
      assert (store_qual S1 (M1 ++ M) E S2 M2 vx (plift p) (plift k1)) as SQ12. {
        eapply SQ2.
      }

      assert (store_qual S M E S1 M1 (vabs l q t0) (plift p) (plift kf)) as SQ01. {
        eapply SQ1.
      }

      assert (store_qual S M E S2 (M2++M1) vx (plift p) (por (plift kf) (plift k1))) as SQ02. {
        eapply storeq_seq. eauto. 
        3: eapply SQ01.
        3: eapply SQ12.  
        3: eapply HQX. 
        eauto. eauto. 
      }


      (* dealing with fresh parts of vx, vy that may be deallocated *)

      (* key: if we're deallocating fresh parts of vx, we can't return them *)
      
      assert (store_qual S M E S3 (M3++M2++M1) vy (plift p)
                (por (plift kf) (por (plift k1) (por (plift k2) (if k2x then (plift q1) else pempty))))) as HYS2. {
        intros ? ?. destruct (SQ3 x) as [H_K | [H_k | [H_k2x | H_fr]]]. eauto. 
        (* K *)
        destruct (SQ2 x) as [H2_K | [H2_k | H2_fr]]. eauto. 
          (* K *) 
          destruct (SQ1 x) as [H1_K | [H1_k | H1_fr]]. eauto. 
            (* K *) left. eauto. 
            (* k *) right. left. destruct H1_k. exists x0. unfoldq. intuition.
            (* fr *)  right. right. destruct H1_fr. 
            split. unfoldq. repeat rewrite app_length in *. intuition.
            intros ?. 
            destruct (HQY2 x). split. unfoldq. repeat rewrite app_length in *. intuition. eauto.
            eapply env_wf_contra in H19. eauto. eapply WFE. eapply H16.
            destruct q2x. destruct (HQX x). split. eapply H16. eauto. 
            eapply env_wf_contra. eapply WFE. eapply H16. eauto. eexists. eauto. 
            contradiction.

          (* k *) right. left. destruct H2_k. exists x0. unfoldq. intuition.
          (* fr *) right. right. unfoldq. repeat rewrite app_length in *. intuition.
          destruct (HQY2 x). split. intuition. eauto.
          eapply env_wf_contra in H20. eauto. eapply WFE1. rewrite app_length. eauto. 
          destruct q2x. contradiction. contradiction.

        (* k *) right. left. destruct H_k. exists x0. unfoldq. intuition.
        (* k2x/q1 *) destruct k2x. 2: { unfoldq. intuition. } rewrite H8 in *; eauto.
        bdestruct (x <? length (M1++M)). {
        destruct (HQX x). unfoldq. intuition.
        right. left. destruct H17. exists x0. unfoldq. intuition.
        } {
        right. right. assert (x < length (M3++M2++M1++M)). eapply app_length2. eapply valt_wf; eauto. unfoldq. repeat rewrite app_length in *. intuition. 
        destruct (HQY2 x). split. 

        intuition. repeat rewrite <-app_length. eapply valt_wf; eauto. eauto. 
        assert (x < length (M1 ++ M)). eapply env_type_store_wf. eauto. eauto. 
        rewrite app_length in *. lia. contradiction. }

        (* fr *) right. right. rewrite <-app_assoc. unfoldq. repeat rewrite app_length in *. intuition. 
      }


      split. 2: split. 3: split. 4: split. 

      eauto.

      (* store_effect: would be good to use se_trans and se_sub, but need l < length S1 *)
      intros ? ? ? ?. eapply SE3. intros ?. eapply H15. clear H15. 
      destruct H17. destruct H15 as [? [? ?]]. exists x. intuition.
      destruct H15. left. left. right. right. eauto. right. left. right. right. eauto.
      assert (length S = length M). eapply H9.
      assert (length S1 = length (M1++M)). eapply SW1.
      destruct (HQX l0). unfoldq. rewrite app_length. eapply indexr_var_some' in H16. intuition.
      destruct e2x. simpl in *. eauto.
      destruct k2x. simpl in *. eauto.
      simpl in *. contradiction.
      destruct e2x. simpl in *. exists x. intuition. left. right. eauto. 
      destruct k2x. simpl in *. exists x. intuition. right. right. eauto.
      simpl in *. contradiction.
      (* trans 2 *)
      eapply SE2. intros ?. eapply H15. clear H15.
      destruct H17 as [? [? ?]]. exists x. split. 2: eauto.
      destruct H15. left. left. right. left. eauto. right. left. right. left. eauto. 
      (* trans 1 *)
      eapply SE1. intros ?. eapply H15. clear H15.
      destruct H17 as [? [? ?]]. exists x. split. 2: eauto.
      destruct H15. left. left. left. eauto. right. left. left. eauto. 
      eauto.

      (* store_qual *)
      repeat rewrite por_assoc. eauto.

      eauto.

      eauto.

    + (* fix up *)
      destruct e2x. eauto. unfoldq. intuition. unfoldq. intuition.

      
  - (* Case "Abs". *)
    exists S. exists []. exists (vabs E qf t).

    clear H5. assert True as H5. eauto.
    clear H6. assert True as H6. eauto.
    clear H7. assert True as H7. eauto.
    
    
    split.
    + (* term evaluates *)
      exists 0. intros. destruct n. lia. simpl. eauto.
    + (* result well typed *)
      rewrite app_nil_l. rewrite plift_empty in *.

      split. eauto.

      split. eapply se_refl. 

      split. intros ? ?. simpl in H11. left. eauto. 

      rewrite <-LE in *. repeat split; eauto. 
      rewrite val_locs_abs. eapply env_type_store_wf. eauto.
      
      intros S1 M1 vx ST1 HVX ENVQ SEP1 KSEP.
      eapply sem_abs1 with (e2x:=e2x).
      eauto. eauto. eauto. 

      (* temp *)
      destruct (e2x || k2x); try eauto.

(*
      intros ? ?. eapply SEP1. 
      unfoldq. intuition.

      destruct H12. destruct H11. destruct H11.

      rewrite val_locs_abs. destruct H12. exists x0. intuition. exists x1. intuition.
      rewrite val_locs_abs. destruct H12. exists x0. intuition. exists x1. intuition. 
      (* here we rely on e2,k2 <: qf *)
*)
      
      intros. eapply IHW. eauto.

      replace (por (plift (qor e2 (if e2x then qone (length E) else qempty)))
                (plift (qor k2 (if k2x then qone (length E) else qempty))))
        with (plift (qor (qor e2 k2) (if e2x || k2x then qone (length E) else qempty))).
      2: { (* TODO: cleanup *)
        intros. eapply functional_extensionality.
        intros. eapply propositional_extensionality.
        rewrite plift_or, plift_or, plift_or, plift_or,
          plift_if, plift_if, plift_if, plift_one, plift_empty.
        destruct e2x; destruct k2x; unfoldq; intuition.
      }
                                                                            
      eauto. eauto. 
      
      (* vx, e2 not killed *) {
        intros ? [? XX]. 
        destruct (KSEP x). split. eauto.
        (* rewrite val_locs_abs in SEP. *)
        destruct XX as [? [XX [? [YY ?]]]].
        rewrite plift_or, plift_if, plift_one, plift_empty in XX.
        simpl in YY. 
        bdestruct (x0 =? length E). {
          subst x0. inversion YY. subst x1.
          destruct e2x. right. eauto.
          destruct XX as [XX|XX]. eapply H3 in XX. lia. contradiction.
        } {
          destruct XX as [XX|XX]. left. exists x0. intuition. unfoldq. exists x1. intuition.
          destruct e2x. unfoldq. lia. unfoldq. contradiction.
        }
      }

      all: eauto.

      eapply valq_abs; eauto.
            
  -  (* Case "Sub". *)
    assert (env_qual E (por (plift e1) (plift k1))) as SEP'. eapply envq_tighten. eauto. unfoldq. intuition. 
    destruct (IHW M E WFE SEP' S) as [S1 [M1 [vx [IW1 [SW1 [SE1 [SQ1 [HVX HQX]]]]]]]]. eauto. eauto.

    (* safeq_sub *)
    intros ? ?. destruct (H6 x). unfoldq. intuition. destruct H9. exists x0. intuition.
    
    assert (psub (plift q2) (pdom E)). {
      unfoldq. rewrite LE. intuition. }

    exists S1, M1, vx.
    unfold exp_type. intuition.

    eapply se_sub. eauto. intros ? ?. destruct H8 as [? [? ?]]. exists x0. intuition. unfoldq. intuition. 

    (* storeq_sub *)
    intros ? ?. destruct (SQ1 x) as [H_K | [H_k | H_fr]]. eauto.
    (* K *) left. eauto.
    (* k *) right. left. destruct H_k. exists x0. unfoldq. intuition.
    (* fr *) right. right. eauto. 
    
    (* val_qual *)
    eapply valq_sub; eauto. 
Qed.


(* note: not assuming anything other than has_type below *)

Corollary safety : forall t T q e k,
  has_type [] t T qempty q e k -> 
  exists S M v, exp_type [] [] [] t S M v T (plift qempty) (plift q) (plift e) (plift k).
Proof. 
  intros. eapply full_total_safety in H; eauto.
  unfold env_type; intuition; simpl. unfoldq. intuition. inversion H0.
  unfold env_qual. intros. destruct H1 as (? & ? & ?). inversion H1. 
  unfold store_type. split. eauto. intros. inversion H0. 
  unfold safe_qual. unfoldq. intuition. inversion H1. 
Qed.


Lemma xxx: forall G t T p q e k,
    has_type G t T p q e k ->
    has_type G t T (qempty) q e k.
Proof.
  intros. induction H; econstructor; eauto.
Qed.

End STLC.
