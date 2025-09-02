(* Full safety for STLC *)

(* based on stlc_reach.v and stlc_ref.v *)
(* based on stlc_reach_ref_kill.v *)

(* 

Simply-typed lambda calculus, combined proof of termination and type 
soundness (using logical relations).

This version has mutable references. Store entries can contain
arbitrary types, including other references. Access to the store
is allowed only via a swap operation.

Every dereference incurs a use effect on the reference. A swap
operation (the only form of derefence here) also incurs a move
effect on the assigned value.

The internal model is that the store is tree-shaped (entries
are non-overlapping) and that we track when values are moved
into and out of the store.


Notes/status/todo:

- the standard qualifier separation requirement is too strict in
  this model: if a location has been moved from a variable into the
  store, it can be extracted out later and bound to new variables.
  Then the new variable and the old variable are not separate.
  This is OK because the effect system prevents any further
  use of the old variable, but we need to relax the
  separation invariant to accurately reflect this situation.

  Current workaround: 'use' effect on q1,qf in rule app.

  Proposed fix: guarantee separation in env_type only for non-
    moved locations, update appropriately when store changes

- cyclicity in store typing: since the store permits deep nested
  references with updates, the definition of value typing and
  store typing becomes recursive. This requires some form of
  indexing scheme (either based on execution steps or type
  structure).

  Current workaround: none, there's an 'admit' left in storet_swap

  Proposed fix: add type indexing scheme based on TRef
    nesting depth or execution step indexing

- deallocation: to reduce complexity, there is no 'free' operation
  in this file.

  Proposed fix: add it back in, either in a non-idempotent form
  under the existing destructive effect or with a separate category
  of idempotent kill effects, distinguished from moves.

- extension with overlap: the present version does not support
  overlapping qualifiers, which would be desirable to have both
  in the environment (straightforward, see file _overlap.v) and
  in the store, as part of nested reference types
  (harder, new work needed).

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
  | tswap : tm -> tm -> tm
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
    psub (pand (plift k) (plift q)) pempty ->
    has_type env (tref t) (TRef T) p qempty e (qor k q) (* kill/move q! *)
(* get is unsafe in this version -- hence disabled
| t_get: forall t env T p q e k,
    has_type env t (TRef T) p q e k ->
    psub (pand (plift k) (plift q)) pempty ->
    has_type env (tget t) T p qempty (qor e q) k 
| t_free: forall t env T p q e k,
    has_type env t (TRef T) p q e k ->
    psub (pand (plift k) (plift q)) pempty ->
    has_type env (tfree t) TBool p qempty e (qor k q) (* always return 'false' *) *)
| t_swap: forall t1 t2 env T p q1 e1 k1 q2 e2 k2,
    has_type env t1 (TRef T) p q1 e1 k1 ->
    has_type env t2 T p q2 e2 k2 ->

    (* effect 1/2 *)
    psub (pand (plift k1) (plift e2)) pempty -> (* no kill before use *)
    psub (pand (plift k1) (plift k2)) pempty -> (* no move before kill *)

    (* effect 2/3 *)
    psub (pand (por (plift k1) (plift k2)) (plift q1)) pempty -> (* no kill before use *)
    psub (pand (por (plift k1) (plift k2)) (plift q2)) pempty -> (* no kill before move *)

    has_type env (tswap t1 t2) T p qempty (qor e1 (qor e2 q1)) (qor k1 (qor k2 q2))
             
| t_app: forall env f t T1 T2 p qf q1 q2 ef e1 e2 kf k1 k2 q2x e2x k2x,
    has_type env f (TFun T1 (* qempty  *) T2 q2 e2 k2 q2x e2x k2x) p qf ef kf ->  
    has_type env t T1 p q1 e1 k1 ->
    
    psub (pand (plift qf) (plift q1)) pempty ->          (* no overlapping *)

    psub (pand (plift kf) (plift q1)) pempty ->          (* XXX necessary? XXX *)
    psub (pand (plift kf) (plift e1)) pempty ->          (* no use after kill *)
    psub (pand (plift kf) (plift k1)) pempty ->          (* no kill after kill *)

    psub (pand (plift k1) (plift qf)) pempty ->          (* XXX necessary? XXX *)

(*    psub (pand (por (plift kf) (plift k1)) (por (plift q2) (if q2x then (plift q1) else pempty))) pempty ->          (* XXX necessary? XXX *) *)
    psub (pand (por (plift kf) (plift k1)) (por (plift e2) (if e2x then (plift q1) else pempty))) pempty ->          (* no use after kill *)
    psub (pand (por (plift kf) (plift k1)) (por (plift k2) (if k2x then (plift q1) else pempty))) pempty ->          (* no kill after kill *)

    psub (plift q2) (plift p) ->
    psub (plift e2) (plift p) ->
    psub (plift k2) (plift p) ->

    (* NOTE: we can return OR kill the function arg, but not both.  *)
    (*       possible to refine: only an issue if the function arg may be fresh! *)
    (k2x = true -> q2x = false) ->

    has_type env (tapp f t) T2 p
      (qor q2                   (if q2x then q1 else qempty))
      (qor (qor qf q1) (qor (qor ef (qor e1 e2)) (if e2x then q1 else qempty))) (* TODO: get rid of qf, q1 !!! --> weaken env sep demands *)
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
        | tswap er ex    =>
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
                    | Some (Some v) => (update M'' x (Some vx), Some (Some v))
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



(* store typings *)

Definition stty := list (vl -> Prop).


Definition st_killed (S: stor) (M: stty) x :=
  indexr x S = Some None.

Definition st_moved (S: stor) (M: stty) x :=
  exists x0 v, indexr x0 S = Some (Some v) /\ val_locs v x.


Definition store_type (S: stor) (M: stty) :=
  length S = length M /\
    (forall l vt,
      indexr l M = Some vt ->
      (* indexr l S = Some None*) False \/ (* don't consider dealloc atm *)
        exists v,
          indexr l S = Some (Some v) /\
            vt v) /\
    (forall x l0 l1 v0 v1,
        (* could refine this: only if not covered by qt? *)
        indexr l0 S = Some (Some v0) ->
        val_locs v0 x ->
        indexr l1 S = Some (Some v1) ->
        val_locs v1 x ->
        l0 = l1
    ) /\
    (forall l v,
        indexr l S = Some (Some v) -> psub (val_locs v) (pdom S))
.

(* value interpretation of types *)

Fixpoint val_type (M:stty) (H:venv) v T : Prop :=
  match v, T with
  | vbool b, TBool =>
      True
  | vref l, TRef T => (* restrict to TRef TBool ? *)
      closed_ty (length H) T /\
      exists vt,
        indexr l M = Some vt /\
          (forall vx, vt vx -> val_type M H vx T)
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
              psub (pand (val_locs v) (val_locs vx)) pempty
      (*
              psub
                (pand (st_killed S' (M'++M))
                   (por (vars_locs H (plift e2))
                      (if e2x then (val_locs vx) else pempty)))
                pempty *)
            -> psub
                (pand (st_moved S' (M'++M))
                   (por (vars_locs H (plift e2))
                      (if e2x then (val_locs vx) else pempty)))
                pempty 
            ->
              psub
                (pand (st_moved S' (M'++M))
                   (por (vars_locs H (plift k2))
                      (if k2x then (val_locs vx) else pempty)))
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
(*
                  psub (st_killed S'' (M''++M'++M))
                    (por (st_killed S' (M'++M))
                       (por (vars_locs H (plift k2))
                          (por (if k2x then (val_locs vx) else pempty)  
                             (pdiff (pdiff (pdom (M''++M'++M)) (pdom (M'++M))) (val_locs vy))))) *)

                  psub (st_moved S'' (M''++M'++M))
                    (por (st_moved S' (M'++M))
                       (por (pdiff (vars_locs H (plift k2))
                               (val_locs vy))
                       (por (pdiff (if k2x then (val_locs vx) else pempty)
                               (val_locs vy))
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
                    (val_locs vy)
                    (por (pand (vars_locs H (plift q2)) (val_locs v))
                       (por (if q2x then (val_locs vx) else pempty)
                          (por (pand (vars_locs H (plift k2)) (val_locs v))
                             (por (if k2x then (val_locs vx) else pempty)
                                (por (pdiff (st_moved S' (M'++M)) (st_moved S'' (M''++M'++M)))
                                   (pdiff (pdom (M''++M'++M)) (pdom (M'++M)))))))))
  | _,_ =>
      False
  end.

(*

Definition val_qual (M: stty) H v p (q: pl) :=
  psub (pand (pdom M) (val_locs v)) (vars_locs H (pand p q)).

*)

Definition val_qual S M S' (M': stty) H v (p q k: pl) :=
  psub (val_locs v)
    (por (vars_locs H (pand p q))                          (* old and covered by qualifier *)
       (por (vars_locs H (pand p k))                          (* old and covered by qualifier *)
          (por (pdiff (st_moved S M) (st_moved S' (M'++M)))   (* no longer moved *)
             (pdiff (pdom (M'++M)) (pdom M))))).                               (* new allocation *)

(*
locs(v) < p & q
        | dom(M'++M) - dom(M)
        | moved(M) - moved(M'++M)
*)


(*
Previous version:

Definition store_qual S M H S' M' v p k :=
    psub (st_killed S' (M'++M))
      (por (st_killed S M)
         (por (vars_locs H (pand p k))
            (pdiff (pdiff (pdom (M'++M)) (pdom M))
               (val_locs v)))).
*)



Definition store_qual S M H S' M' v p k :=
      psub (st_moved S' (M'++M))
        (por (st_moved S M)
           (por (pdiff (vars_locs H (pand p k))
                   (val_locs v))
              (pdiff (pdiff (pdom (M'++M)) (pdom M))
                 (val_locs v)))) /\

      psub (st_moved S M) (pdom M)

.


Definition exp_type S M H t S' M' v T p q (e: pl) (k: pl) :=
  tevaln S H t S' v /\
    store_type S' (M'++M) /\
    store_qual S M H S' M' v p k /\ 
    val_type (M'++M) H v T /\
    val_qual S M S' M' H v p q k.

(* kill set after evaluating t to v is the union of:
   - previous cumulative kill set K
   - existing observable locations mentioned by t's effect annotation k (i.e., p /\ k)
   - fresh locations allocated during evaluation of t that aren't reachable from result v
 *)
   


Definition safe_qual S M H p e := 
  psub (pand (st_moved S M) (vars_locs H (pand p e))) pempty.




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


Ltac unfoldq := unfold val_qual, psub, pdom, pand, por, pnot, pdiff, pempty, pone, var_locs, vars_locs in *.
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



(* ---------- val_type lemmas  ---------- *)

Lemma valt_wf: forall T M H v,
    val_type M H v T ->
    psub (val_locs v) (pdom M).
Proof. 
  intros T. induction T; intros; destruct v; simpl in *; intuition.
  + rewrite val_locs_bool. auto. unfoldq. intuition.
  + rewrite val_locs_ref.
    destruct H2 as [vt [IX VX]].
    eapply indexr_var_some' in IX.
    unfoldq. intuition.
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
  + destruct H2 as [vt [IX VT]].
    exists vt. split. 
    eapply indexr_extend in IX. eapply IX.
    intros. eapply IHT. eauto.
  + unfoldq. rewrite app_length. intros. assert (x < length M). eauto. lia.
  + destruct (H7 S' (M'0 ++ M') vx) as [S'' [M'' [vy  [SEY [IEY [HSK [HVY HSEP]]]]]]].
    rewrite <- app_assoc. auto.
    rewrite <- app_assoc. auto.
    auto. auto. eauto.
    exists S'',  M'', vy. intuition.
    repeat erewrite <- app_assoc in SEY; eauto.
    repeat erewrite <- app_assoc in IEY; eauto.
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
  - (* Ref shrink *)
    destruct H3 as [vx [IX HVX]].
    exists vx. intuition.
    eapply IHT; eauto. inversion H0. auto.
  - eapply closedty_extend; eauto.
  - (* Ref grow *)
    destruct H3 as [vx [IX HVX]].
    exists vx. intuition.
    eapply IHT; eauto. 
  - inversion H0. auto.
  - inversion H0. auto.
  - inversion H0. auto.
  - inversion H0. auto.
  - inversion H0. auto.    
  - (* Abs shrink *)
    inversion H0. subst.
(*    rename q into q2.  *)
    destruct (H8 S' M' vx) as [S'' [M'' [vy [HEY [HSK HVY]]]]].
      eauto.
      eapply IHT1; eauto.
      eauto.
      rewrite vars_locs_extend. eauto. eauto.
      rewrite vars_locs_extend. eauto. eauto. 
    exists S'', M'', vy. intuition.
    rewrite vars_locs_extend in H13.
    eauto. eauto.
    eapply IHT2; eauto.
    rewrite vars_locs_extend in H16.
    rewrite vars_locs_extend in H16.
    eauto. eauto. eauto. 
  - eapply closedty_extend; eauto.
  - eapply closedty_extend; eauto.
  - unfoldq. rewrite app_length. intuition. eapply H3 in H7. lia.
  - unfoldq. rewrite app_length. intuition. eapply H4 in H7. lia.
  - unfoldq. rewrite app_length. intuition. eapply H5 in H7. lia.
  - (* Abs grow *)
    inversion H0. subst.
(*    rename q into q2. *)
    destruct (H8 S' M' vx) as [S'' [M'' [vy [HEY [HSK [HVY HQY]]]]]].
      eauto.
      eapply IHT1; eauto.
      eauto.
      rewrite vars_locs_extend in H11. eauto. eauto.
      rewrite vars_locs_extend in H12. eauto. eauto. 
    exists S'', M'', vy. intuition.
    rewrite vars_locs_extend.
    eauto. eauto.
    eapply IHT2; eauto.
    rewrite vars_locs_extend.
    rewrite vars_locs_extend. 
    eauto. eauto. eauto. 
Qed.


Lemma valt_extend1: forall T M H v vx,
    closed_ty (length H) T ->
    val_type M (vx::H) v T <-> val_type M H v T.
Proof.
  intros. replace (vx :: H)  with ([vx]  ++ H); auto.
  eapply valt_extend; eauto.
Qed.


(* ---------- val_qual lemmas  ---------- *)

Lemma valq_bool: forall S M S' M' H b p q k,
    val_qual S M S' M' H (vbool b) p q k.
Proof.
  intros. unfoldq. rewrite val_locs_bool. intuition.
Qed.


Lemma valq_fresh: forall S M S' M' H vx vt p q k,
    val_qual S M (vx::S') (vt::M') H (vref (length (M' ++ M))) p q k.
Proof.
  intros. unfoldq.
  (* valq: index out of range*)
  rewrite app_length.
  rewrite val_locs_ref.
  intuition. right. right. right. simpl. rewrite app_length. 
  unfoldq. intuition. 
Qed.


Lemma valq_abs: forall S M S' M' H t p q k,
    val_qual S M S' M' H (vabs H (qand p q) t) (plift p) (plift q) (plift k).
Proof.
  intros. unfoldq.
  rewrite val_locs_abs.
  rewrite plift_and.
  intuition. 
Qed.


Lemma valq_sub: forall S M S' M' H v p q q' k k',
    val_qual S M S' M' H v p q k ->
    psub q q' ->
    psub k k' ->
    psub q' (pdom H) ->
    psub k' (pdom H) ->
    val_qual S M S' M' H v p q' k'.
Proof.
  intros. unfoldq. intuition.
  destruct (H0 x) as [H_q | [H_m | H_fr]]. eauto. 
  - left. destruct H_q. exists x0. intuition.
  - right. left. destruct H_m. exists x0. intuition. 
  - right. right. eauto. 
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


Lemma envt_store_extend: forall M M' H G p,
    env_type M H G p ->
    env_type (M'++M) H G p.
Proof.
  intros. destruct H0 as [L [P W]]. 
  repeat split; auto. intros.
  destruct W as [W W'].
  destruct (W _ _  H0) as [vx [IH HVX]]; intuition.
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
    psub (vars_locs H q) (pdom M).
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


Lemma env_wf_contra: forall M E G p k1 x,
    env_type M E G p ->
    vars_locs E (pand p k1) x ->
    ~ (x < length M) ->
    False.
Proof.
  intros. eapply H1. eapply env_type_store_wf; eauto. 
Qed.


Lemma env_sep_contra: forall M E G p k1 k2 x,
    env_type M E G p ->
    psub (pand k1 k2) pempty ->
    vars_locs E (pand p k1) x ->
    vars_locs E (pand p k2) x -> 
    False.
Proof.
  intros.
  destruct H as [? [? [? SEP]]], H2, H1. unfoldq. intuition.
  assert (x0 = x1). eapply SEP; eauto.
  subst x1. eauto. 
Qed.


Lemma separation: forall S S' S'' M M' M'' H G p vf vx qf q1 kf k1
    (WFE: env_type M H G p)
    (SQF: store_qual S M H S' M' vf p kf)
    (SQX: store_qual S' (M'++M) H S'' M'' vx p k1)
    (HQF: val_qual S M S' M' H vf p qf kf)
    (HQX: val_qual S' (M'++M) S'' M'' H vx p q1 k1),
    psub (val_locs vf) (pdom (M'++M)) ->
    psub (vars_locs H (pand p qf)) (pnot (st_moved S M)) -> (* can we avoid this? *)
    psub (vars_locs H (pand p kf)) (pnot (st_moved S M)) -> (* can we avoid this? *)
    psub (vars_locs H (pand p q1)) (pnot (st_moved S M)) -> (* can we avoid this? *)
    psub (vars_locs H (pand p k1)) (pnot (st_moved S M)) -> (* can we avoid this? *)
    psub (pand qf q1) pempty ->
    psub (pand qf k1) pempty ->
    psub (pand kf q1) pempty ->
    psub (pand kf k1) pempty ->
    psub (pand (val_locs vf) (val_locs vx)) pempty.
Proof. 
  intros. unfoldq. intuition.
  remember WFE as WFE1. clear HeqWFE1.
  destruct WFE as [? [? [? SEP]]].
  destruct SQF as [SMF ?].
  destruct SQX as [SMX ?].
  destruct (HQF x) as [F_q | [F_m | [F_mv | F_fr]]];
    destruct (HQX x) as [X_q | [X_m | [X_mv | X_fr]]]; eauto.
  - (* qf,q1 *) eapply env_sep_contra with (k1:=qf)(k2:=q1); eauto.
  - (* qf,m1 *) eapply env_sep_contra with (k1:=qf)(k2:=k1); eauto.
  - (* qf,mv *) destruct X_mv.
    destruct (SMF x) as [SF_K | [SF_k | SF_fr]]. eauto.
    + eapply H1. eauto. eauto.
    + destruct SF_k. intuition.
    + destruct SF_fr. intuition.
  - (* qf,fr *) destruct X_fr. eapply env_wf_contra; eauto.
  - (* mf,q1 *) eapply env_sep_contra with (k1:=kf)(k2:=q1); eauto.
  - (* mf,m1 *) eapply env_sep_contra with (k1:=kf)(k2:=k1); eauto.
  - (* mf,mv *) destruct X_mv.
    destruct (SMF x) as [SF_K | [SF_k | SF_fr]]. eauto.
    + eapply H2. eauto. eauto.
    + destruct SF_k. intuition.
    + destruct SF_fr. intuition.
  - (* mf,fr *) destruct X_fr. eapply env_wf_contra; eauto.
  - (* mv,q1 *) destruct F_mv. eapply H3; eauto.
  - (* mv,m1 *) destruct F_mv. eapply H4; eauto.
  - (* mv,mv *) destruct F_mv. destruct X_mv. eauto.
  - (* mv,fr *) destruct F_mv. destruct X_fr. eauto.
  - (* fr,q1 *) destruct F_fr. eapply env_wf_contra; eauto.
  - (* fr,m1 *) destruct F_fr. eapply env_wf_contra; eauto. 
  - (* fr,mv *) destruct F_fr. destruct X_mv.
    destruct (SMF x) as [SF_K | [SF_k | SF_fr]]. eauto.
    + eapply H14 in SF_K. contradiction. 
    + destruct SF_k. intuition.
    + destruct SF_fr. intuition.
  - (* fr,fr *) destruct F_fr. destruct X_fr. eauto.
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
  unfold store_qual in *. 
  unfoldq. intuition.
  { destruct (H2 x) as [H_K | [H_k | H_fresh]]. eauto.
    - left. eauto.
    - right. left. destruct H_k. destruct H4. intuition. exists x0. unfoldq. intuition.
    - right. right. intuition. }
Qed.




Lemma storeq_seq: forall S M E G S1 S2 M1 M2 v1 v2 p k1 k2 q2,
    env_type M E G p ->
    psub (pand k1 k2) pempty ->
    psub (pand k1 q2) pempty ->
    store_qual S M E S1 M1 v1 p k1 ->
    store_qual S1 (M1 ++ M) E S2 M2 v2 p k2 -> 
    val_qual S1 (M1 ++ M) S2 M2 E v2 p q2 k2 ->
    store_qual S M E S2 (M2 ++ M1) v2 p (por k1 k2).
Proof.
  intros. destruct H2 as [SM1 SB1]. destruct H3 as [SM2 SB2].
  rename H into WFE.
  rename H0 into SEPk1k2.
  rename H1 into SEPk1q2.
  rename H4 into VQ.
  split.  {
    intros ? ?. destruct (SM2 x) as [H_K | [H_k | H_fr]]. eauto. 
    - eapply SM1 in H_K. destruct H_K as [H1_K | [H1_k | H1_fr]].
      + left. eauto.
      + right. left. unfoldq. intuition. destruct H0. exists x0. intuition.
        destruct (VQ x) as [V_q | [V_m | [V_mv | V_fr]]]. eauto.
        (* q *) eapply env_sep_contra; eauto.  
        (* m *) eapply env_sep_contra with (k2:=k2); eauto.  
        (* mv *) destruct V_mv. eauto.
        (* fr *) destruct V_fr. eapply env_wf_contra; eauto. rewrite app_length in *. lia.      + right. right. unfoldq. intuition. repeat rewrite app_length in *. lia.
        destruct (VQ x) as [V_q | [V_m | [V_mv | V_fr]]]. eauto.
        (* q *) eapply env_wf_contra; eauto. 
        (* m *) eapply env_wf_contra; eauto. 
        (* mv *) destruct V_mv. eauto.
        (* fr *) destruct V_fr. eauto. 
    - right. left. unfoldq. intuition. destruct H0. exists x0. intuition.
    - right. right. unfoldq. intuition. rewrite <-app_assoc. eauto.
      eapply H3. rewrite app_length. lia.
  } {
    eauto.
  }
Qed.


Lemma valq_seq: forall S M E S1 S2 M1 M2 v1 v3 p k1 k2 q2,
    store_qual S M E S1 M1 v1 p k1 ->
    val_qual S1 (M1 ++ M) S2 M2 E v3 p q2 k2 ->
    val_qual S M S2 (M2 ++ M1) E v3 p q2 (por k1 k2).
Proof.
  intros. intros ? ?. destruct (H0 x) as [H_q | [H_k | [H_mv | H_fr]]]. eauto. 
  - left. eauto.
  - right. left. unfoldq. intuition. destruct H_k. exists x0. intuition.
  - rename H into SQ_M.
    destruct H_mv as [SM ?]. eapply SQ_M in SM.
    destruct SM as [H_K | [H_k | H_fr]].
    + right. right. left. unfoldq. intuition.
    + right. left. unfoldq. intuition. destruct H2. exists x0. intuition.
    + right. right. right. unfoldq. rewrite <-app_assoc. rewrite app_length. intuition.
  - right. right. unfoldq. repeat rewrite app_length in *. lia. 
Qed.





(* -- allocation -- *)

Lemma storet_extend: forall S M H T vx,
    store_type S M ->
    val_type M H vx T ->
    psub (val_locs vx) (pnot (st_moved S M)) -> 
    store_type (Some vx :: S) ((fun v => val_type M H v T) :: M).
Proof.
  intros.
  unfold store_type in *. intuition.
  (* length *)
  simpl. eauto.
  (* lookup *) {
  simpl. simpl in H5. rewrite H3. bdestruct (l =? length M).
  - right. inversion H5. subst l vt.
    exists vx. intuition. 
  - eapply H0. eauto.
  }
  (* separation *) {
    simpl in H5, H8.
    bdestruct (l0 =? length S); bdestruct (l1 =? length S).
    - subst. eauto.
    - inversion H5. subst v0 l0.
      eapply H2 in H7. destruct H7. exists l1. exists v1. intuition.
    - inversion H8. subst v1 l1.
      eapply H2 in H9. destruct H9. exists l0. exists v0. intuition.
    - eapply H4; eauto. 
  }
  (* bound *) {
    simpl in H5.
    bdestruct (l =? length S).
    - subst l. unfoldq. intuition. inversion H5. subst v. 
      assert (x < length M). eapply valt_wf; eauto. simpl. lia.
    - unfoldq. simpl. intuition.
      assert (x < length S). eapply H6; eauto. lia. 
  }
Qed.

Lemma storeq_extend: forall S M G E S1 M1 vx vt p q k,
    env_type M E G (plift p) ->
    store_qual S M E S1 M1 vx (plift p) (plift k) ->
    val_qual S M S1 M1 E vx (plift p) (plift q) (plift k) ->
    psub (val_locs vx) (pdom (M1 ++ M)) -> 
    store_qual S M E (Some vx :: S1) (vt :: M1) (vref (length (M1 ++ M))) (plift p) (plift (qor k q)).
Proof.
  intros.
  rename H into WFE.
  rename H0 into H.
  rename H1 into H0.
  rename H2 into H1.
  unfold store_qual in *. split. 
  { (* move *)
    rewrite val_locs_ref. unfoldq. intuition. unfold st_moved in *.
    simpl in H. destruct H. destruct H.
    bdestruct (x0 =? length S1). destruct H. inversion H. subst x0 x1.
    (* x0 = i *)
    destruct (H0 x) as [H_q | [H_m | [H_mv | H_fr]]]. eauto. 
    - right. left. split. destruct H_q. exists x0. rewrite plift_or. unfoldq. intuition.
      intros. eapply env_wf_contra; eauto. rewrite app_length in *. lia. 
    - right. left. split. destruct H_m. exists x0. rewrite plift_or. unfoldq. intuition.
      intros. eapply env_wf_contra; eauto. rewrite app_length in *. lia.
    - destruct H_mv. left. eauto.
    - right. right. eapply H1 in H5. repeat rewrite app_length in *. simpl. intuition.
    (* x0 <> i *)
    - destruct (H2 x) as [H_K | [H_mv | H_fr]]. exists x0. intuition. exists x1. intuition.
      + left. eauto.
      + right. left. destruct H_mv. split. destruct H5. exists x2. rewrite plift_or. unfoldq. intuition.
        intros. eapply env_wf_contra; eauto. rewrite app_length in *. lia.
      + right. right. simpl. intuition.
  } {
    eapply H. 
  }
Qed. 
  



(* -- swap -- *)

Lemma storet_swap: forall S M H T i vx,
    store_type S M ->
    val_type M H (vref i) (TRef T) ->
    val_type M H vx T -> 
    True -> (* ~ st_killed S M i ->  don't consider dealloc case ... *)
    psub (val_locs vx) (pnot (st_moved S M)) -> 
    store_type (update S i (Some vx)) M.
Proof.
  intros. destruct H0 as [L [ST [SEP SB]]].
  split. 2: split. 3: split.
  (* length *)
  rewrite <-update_length. eauto.
  (* lookup *) {
    intros.
    eapply ST in H0 as XX. destruct XX.
    - (* none *)
      bdestruct (i =? l). subst l.
      + rewrite update_indexr_hit. contradiction.
      (* rewrite indexr_extend in H5. eapply H5.  don't consider dealloc case ... *) contradiction.
      + rewrite update_indexr_miss. eauto. eauto.
    - (* some *)
      bdestruct (i =? l). subst l. 
      + rewrite update_indexr_hit. right. exists vx. intuition.
        destruct H1 as [CL [vt1 [IX ?]]].
        rewrite IX in H0. inversion H0. subst vt1.
        admit. (* new v is well-typed <-- currently not checked because of store typing cyclicity (see note at top)  *)
        destruct H5. rewrite indexr_extend in H5. eapply H5.
      + rewrite update_indexr_miss. eauto. eauto.
  }
  (* separation *) {
    intros.
    assert (l0 < length S). rewrite indexr_extend in H0. rewrite <-update_length in H0. eapply H0.
    assert (l1 < length S). rewrite indexr_extend in H6. rewrite <-update_length in H6. eapply H6.
    bdestruct (l0 =? i); bdestruct (l1 =? i).
    - subst. rewrite update_indexr_hit in H0, H6; eauto.
    - subst. rewrite update_indexr_hit in H0; eauto. inversion H0. subst. 
      eapply H4 in H5. destruct H5. exists l1. exists v1. intuition.
      rewrite update_indexr_miss in H6. eauto. eauto.
    - subst. rewrite update_indexr_hit in H6; eauto. inversion H6. subst. 
      eapply H4 in H7. destruct H7. exists l0. exists v0. intuition.
      rewrite update_indexr_miss in H0. eauto. eauto.
    - rewrite update_indexr_miss in H0; eauto.
      rewrite update_indexr_miss in H6; eauto.
  }
  (* bound *) {
    intros. 
    unfoldq. bdestruct (i =? l).
    - subst l. rewrite update_indexr_hit in H0. inversion H0. subst v.
      intros. rewrite <-update_length. rewrite L. eapply valt_wf; eauto.
      rewrite indexr_extend in H0. rewrite <-update_length in H0. eapply H0.
    - rewrite update_indexr_miss in H0; eauto.
      rewrite <-update_length. eapply SB. eauto. 
  }
  Unshelve.
  eapply [].
  eapply [].
  eapply [].
  eapply [].
Admitted.



Lemma storeq_swap0: forall E S1 S2 M1 M2 i vx vy p k2 q2,
    store_type S2 (M2++M1) -> 
    store_qual S1 M1 E S2 M2 vx (plift p) (plift k2) ->
    val_qual S1 M1 S2 M2 E vx (plift p) (plift q2) (plift k2) ->
    indexr i S2 = Some (Some vy) ->
    psub (val_locs vx) (pnot (st_moved S2 (M2++M1))) -> (* get from val_qual? *)
    store_qual S1 M1 E (update S2 i (Some vx)) M2 vy (plift p)
      (por (plift k2) (plift q2)).
Proof.
  intros. destruct H0 as [SM2 SB].
  split. {
    (* move *)
    intros ? ?. destruct H0. destruct H0.
    bdestruct (x0 =? i).
    + subst x0. rewrite update_indexr_hit in H0. destruct H0. inversion H0. subst x1.
      destruct (H1 x) as [H_q | [H_m | [H_mv | H_fr]]]. eauto.
      (* q *) right. left. split. destruct H_q. exists x0. unfoldq. intuition.
      intros ?. eapply H3. eapply H4. exists i, vy. intuition. 
      (* m *) right. left. split. destruct H_m. exists x0. unfoldq. intuition. 
      intros ?. eapply H3. eapply H4. exists i, vy. intuition.
      (* mv *) left. eapply H_mv.
      (* fr *) right. right. eapply H3 in H4. unfoldq. intuition. eapply H4.
      exists i, vy. intuition.
      rewrite indexr_extend in H2. eapply H2. 
    + rewrite update_indexr_miss in H0. 2: eauto.
      assert (~val_locs vy x). { destruct H as [L [ST SEP]]. intros ?.
      eapply H4. eapply SEP. eapply H0. eapply H0. eapply H2. eapply H. }
      destruct (SM2 x) as [H_K | [H_q | H_fr]]. exists x0. exists x1. eauto. 
      (* K *) left. eauto.
      (* q *) right. left. destruct H_q. split. destruct H6. exists x2. unfoldq. intuition. eauto. 
      (* fr *) right. right. unfoldq. intuition.
  } {
    eauto.
  }  
  Unshelve.
  eapply [].
Qed.


Lemma valq_swap0: forall S2 M2 E i vx vy p q k,
    store_type S2 M2 -> 
    indexr i S2 = Some (Some vy) ->
    psub (val_locs vx) (pnot (st_moved S2 M2)) ->
    val_qual S2 M2 (update S2 i (Some vx)) [] E vy p q k. 
Proof. 
  intros. intros ? ?.
  right. right. left. split. {
    (* moved before *)
    exists i. exists vy. intuition; eauto.
  } {
    (* not moved after *)
    intros ?. destruct H3. destruct H3. destruct H3.
    bdestruct (x0 =? i).
    - subst x0. rewrite update_indexr_hit in H3.
      inversion H3. subst x1.
      eapply (H1 x). eauto. exists i. exists vy. intuition.
      rewrite indexr_extend in H3. rewrite <-update_length in H3. eapply H3. 
    - rewrite update_indexr_miss in H3. 2: eauto.
      destruct H as [? [? SEP]].
      eapply H5. eapply SEP; eauto. 
  }
  Unshelve.
    eapply [].
Qed.



Lemma storeq_swap: forall S M E G S1 S2 M1 M2 i vx vy p k1 k2 q2,
    env_type M E G (plift p) ->
    store_type S2 (M2++M1++M) -> 

    store_qual S M E S1 M1 (vref i) (plift p) (plift k1) ->

    store_qual S1 (M1 ++ M) E S2 M2 vx (plift p) (plift k2) ->

    val_qual S1 (M1 ++ M) S2 M2 E vx (plift p) (plift q2) (plift k2) ->

    indexr i S2 = Some (Some vy) ->

    psub (pand (plift k1) (plift k2)) pempty ->

    psub (pand (plift k1) (plift q2)) pempty ->
    
    psub (val_locs vx) (pnot (st_moved S2 (M2++M1++M))) -> (* get from val_qual? *) 

    store_qual S M E (update S2 i (Some vx)) (M2 ++ M1) vy (plift p)

      (plift (qor k1 (qor k2 q2))).

Proof.
  intros.
  repeat rewrite plift_or. repeat rewrite plift_and. 
  eapply storeq_seq; eauto.
  unfoldq. intuition. eapply H5; eauto. eapply H6; eauto.
  eapply storeq_swap0; eauto.
  eapply valq_seq with (M2:=[]); eauto.
  eapply valq_swap0; eauto.
Qed.




Lemma valq_swap: forall S M E S1 S2 M1 M2 i vx vy p k1 k2 q2,
    store_type S2 (M2++M1++M) -> 

    store_qual S M E S1 M1 (vref i) (plift p) (plift k1) ->

    store_qual S1 (M1 ++ M) E S2 M2 vx (plift p) (plift k2) ->

    val_qual S1 (M1 ++ M) S2 M2 E vx (plift p) (plift q2) (plift k2) ->

    indexr i S2 = Some (Some vy) ->

    psub (val_locs vx) (pnot (st_moved S2 (M2++M1++M))) -> (* get from val_qual? *)

    val_qual S M (update S2 i (Some vx)) (M2 ++ M1) E vy (plift p) (plift qempty)
      (plift (qor k1 (qor k2 q2))).

Proof.
  intros.
  repeat rewrite plift_or.
  eapply valq_seq. eauto. 
  eapply valq_seq with (M2:=[]); eauto.
  eapply valq_swap0; eauto.
Qed.






Lemma safeq_split: forall S M E p e q,
    safe_qual S M E (plift p) (plift (qor e q)) ->
    safe_qual S M E (plift p) (plift e) /\
      safe_qual S M E (plift p) (plift q).
Proof.
  intros. rewrite plift_or in *. 
  unfold safe_qual in *. unfoldq. intuition.
  destruct H2. 
  destruct (H x). intuition. exists x0. intuition.
  destruct H2. 
  destruct (H x). intuition. exists x0. intuition.
Qed. 

Lemma safeq_join: forall S M E p e q,
    safe_qual S M E (plift p) (plift e) ->
    safe_qual S M E (plift p) (plift q) ->
    safe_qual S M E (plift p) (plift (qor e q)).
Proof.
  intros. rewrite plift_or in *. 
  unfold safe_qual in *. unfoldq. intuition.
  destruct H3.
  destruct (H x). intuition. exists x0. intuition.
  destruct (H0 x). intuition. exists x0. intuition.
Qed. 

Lemma valq_safe: forall S M E S1 M1 v p q k,
    val_qual S M S1 M1 E v p q k ->
    store_qual S M E S1 M1 v p k ->
    safe_qual S M E p q ->
    safe_qual S M E p k ->
    psub (val_locs v) (pnot (st_moved S1 (M1++M))).
Proof.
  intros.
  (* destruct H0 as [L [ST SEP]]. *)
  destruct H0 as [SM SB].
  rename H1 into SFQ.
  rename H2 into SFK.
  rename H into VQ.

  intros ? ? ?. 

  destruct (SM x) as [H_K | [H_k | H_fr]]. eauto.
  - (* K *) destruct (VQ x) as [V_q | [V_m | [V_mv | V_fr]]]. eauto. 
    + (* q *) destruct (SFQ x). (* qual is safe *)
      unfold st_moved, st_killed, st_moved. unfoldq. intuition. 
    + (* m *) destruct (SFK x).
      unfold st_moved, st_killed, st_moved. unfoldq. intuition.
    + (* mv *)
      destruct V_mv. contradiction. 
    + (* fr *)
      destruct V_fr.
      (* it's already been moved in M, so must be < dom M *)
      eapply H2. eapply SB. eapply H_K.
  - (* k *) destruct H_k. contradiction.
  - (* fr *) destruct H_fr. contradiction.
Qed.


Lemma safeq_extend: forall S M E G S1 M1 v p q k,
    env_type M E G p ->
    store_type S M -> 
    safe_qual S M E p q ->
    store_qual S M E S1 M1 v p k ->
    psub (pand k q) pempty ->
    safe_qual S1 (M1++M) E p q.
Proof.
  intros.
  destruct H2 as [SM ?].
  unfold safe_qual.
  unfoldq. intuition. 
  destruct (SM x) as [H_K | [H_k | H_fr]]. eauto.
  - (* K *) destruct (H1 x). unfoldq. intuition.
  - (* k *) destruct H_k. eapply env_sep_contra. eauto. 2: eapply H6. 2: eapply H4. unfoldq. intuition. eapply H3. intuition; eauto. 
  - (* mv *) destruct H_fr. eapply env_wf_contra; eauto. lia. 
Qed. 




(* ---------- aux ---------- *)

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


Lemma storet_wf: forall M S,
    store_type S M -> 
    psub (st_moved S M) (pdom M).
Proof.
  intros. destruct H as [L [? [? SB]]].
  unfoldq. intuition.
  destruct H1 as [x1 [v1 [? ?]]]. rewrite <- L. eapply SB; eauto.
Qed.


Lemma storeq_empty: forall M E S v p,
    store_type S M -> 
    store_qual S M E S [] v (plift p) (plift qempty).
Proof.
  unfold store_qual. unfoldq. intuition. eapply storet_wf; eauto. 
Qed.
  

(* if well-typed, then result is an actual value (not stuck and not a timeout),
   for large enough n *)

Theorem full_total_safety : forall t G T p q e k,
    has_type G t T p q e k ->
    forall M E, env_type M E G (plift p) ->
    forall S, store_type S M ->
    safe_qual S M E (plift p) (plift e) ->
    safe_qual S M E (plift p) (plift k) ->
    exists S' M' v, exp_type S M E t S' M' v T (plift p) (plift q) (plift e) (plift k).
Proof.
  intros ? ? ? ? ? ? ? W. 
  induction W; intros ? ? WFE; 
  destruct (wf_env_type M E env (plift p) WFE) as [LE [DE PC]]; intuition. 
  
  - (* Case "True". *) exists S. exists []. exists (vbool true). split.
    exists 0. intros. destruct n. lia. intuition. simpl. intuition.
    eapply storeq_empty. eauto.
    eapply valq_bool.
    
  - (* Case "False". *) exists S. exists []. eexists. split.
    exists 0. intros. destruct n. lia. intuition. simpl. intuition. 
    eapply storeq_empty. eauto.
    eapply valq_bool.
    
  - (* Case "Var". *)
    destruct WFE as [? [? [WFE ?]]].
    destruct (WFE x T H) as [vx [HI ?]]. eauto.
    exists S. exists []. eexists. 
    split. exists 0. intros. destruct n. lia. simpl. rewrite HI. reflexivity.
    split. simpl. eauto.
    split. eapply storeq_empty. eauto.
    split. simpl. eauto. 
    
    (* valq *)
    unfoldq. rewrite plift_one.
    unfoldq. intuition.
    left. 
    exists x. intuition.
    exists vx. intuition.
    
  - (* Case "Ref". *)
    eapply safeq_split in H2. destruct H2. 
    destruct (IHW M E WFE S) as [S1 [M1 [vx [IW1 [ST1 [HSK [HVX HQX]]]]]]]; eauto.
    remember (fun v => val_type (M1++M) E v T) as vt.

    (* safe to access *)
    assert (psub (val_locs vx) (pnot (st_moved S1 (M1 ++ M)))). {
      eapply valq_safe; eauto.
    }
    assert (psub (val_locs vx) (pdom (M1 ++ M))). {
      eapply valt_wf; eauto.
    }
    
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
      split. 2: split. 3: split.
      
      simpl. subst. eapply storet_extend. eauto. eauto. eauto.

      eapply storeq_extend. eauto. eauto. eauto. eapply valt_wf. eauto. 

      simpl. intuition. eapply valt_closed. eauto. 
      bdestruct (length (M1 ++ M) =? length (M1 ++ M)); intuition.
      exists vt; intuition.
      subst vt. rewrite app_cons. apply valt_store_extend. eauto.

      eapply valq_fresh. 
(*
  - (* Case "Free". *)
    eapply safeq_split in H2. destruct H2. 
    destruct (IHW M E WFE S) as [S1 [M1 [vx [IW1 [SW1 [HKS [HVX HQX]]]]]]]; eauto.
    remember HVX as HVX'. clear HeqHVX'.
    destruct vx; try solve [inversion HVX]. simpl in HVX.
    destruct (HVX) as [CL [vy [SI HVX1]]].

    (* safe to access *)
    assert (psub (val_locs (vref i)) (pnot (st_moved S1 (M1 ++ M)))). {
      eapply valq_safe1; eauto.
    }
    assert (psub (val_locs (vref i)) (pdom (M1 ++ M))). {
      eapply valt_wf; eauto.
    }
    
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
      split. 2: split. 3: split. 

      eapply storet_free; eauto. 

      eapply storeq_free; eauto. eapply H4. rewrite val_locs_ref. unfoldq. intuition.
      
      simpl. eauto.
      
      eapply valq_bool.*)

  - (* Case "Swap". *)

    eapply safeq_split in H4,H5. destruct H4,H5.
    eapply safeq_split in H6,H7. destruct H6,H7.

    assert (psub (pand (plift k1) (plift q1)) pempty) as SK1Q1. {
      unfoldq. intuition. eapply H1. intuition. left. eauto. eauto.
    }
    assert (psub (pand (plift k2) (plift q1)) pempty) as SK2Q1. {
      unfoldq. intuition. eapply H1. intuition. right. eauto. eauto.
    }
    assert (psub (pand (plift k1) (plift q2)) pempty) as SK1Q2. {
      unfoldq. intuition. eapply H2. intuition. left. eauto. eauto.
    }
    assert (psub (pand (plift k2) (plift q2)) pempty) as SK2Q2. {
      unfoldq. intuition. eapply H2. intuition. right. eauto. eauto.
    }

    (* induction on lhs *)
    destruct (IHW1 M E WFE S) as [S1 [M1 [vr [IW1 [SW1 [HKS1 [HVR HQR]]]]]]]; eauto. 

    assert (env_type (M1++M) E env (plift p)) as WFE1. eapply envt_store_extend. eauto. 

    assert (safe_qual S1 (M1 ++ M) E (plift p) (plift e2)) as SE2. eapply safeq_extend; eauto.
    assert (safe_qual S1 (M1 ++ M) E (plift p) (plift k2)) as SK2. eapply safeq_extend; eauto.

    assert (psub (st_moved S1 (M1 ++ M)) (pdom (M1 ++ M))). eapply storet_wf; eauto.

    (* induction on rhs *)
    destruct (IHW2 (M1++M) E WFE1 S1) as [S2 [M2 [vx [IW2 [SW2 [HKS2 [HVX HQX]]]]]]]; eauto.

    remember HVR as HVR'. clear HeqHVR'.
    destruct vr; try solve [inversion HVR]. simpl in HVR.
    destruct (HVR) as [CL [vt [MI HVR1]]].

    assert (safe_qual S1 (M1 ++ M) E (plift p) (plift q1)) as SQ1. { eapply safeq_extend with (k:=plift k1); eauto. }

    assert (safe_qual S2 (M2 ++ M1 ++ M) E (plift p) (plift q1)) as SQ1'. { eapply safeq_extend with (k:=plift k2); eauto. }

    (*
    assert (~ st_killed S1 (M1++M) i). {
      eauto. (* we don't consider kill effects atm *)
    }
    assert (~ st_killed S2 (M2++M1++M) i). {
      eauto. (* we don't consider kill effects atm *)
    }*)

    remember SW2 as ST1x. clear HeqST1x.
    destruct SW2 as [LST [ST1 SEP]].
    destruct (ST1 i vt) as [|[vy [SI VT]]]. rewrite indexr_extend in MI. eapply MI. contradiction.

    assert (safe_qual S1 (M1 ++ M) E (plift p) (plift q2)) as SQ2. { eapply safeq_extend with (k:=plift k1); eauto. }
    
    assert (psub (val_locs vx) (pnot (st_moved S2 (M2 ++ M1 ++ M)))). { eapply valq_safe with (k:=plift k2); eauto. }

    exists (update S2 i (Some vx)).
    exists (M2++M1).
    exists vy. split.
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
    + split. 2: split. 3: split. 

      rewrite <-app_assoc. eapply storet_swap; eauto. 
      eapply valt_store_extend. eauto. 
      
      eapply storeq_swap; eauto. 

      eapply HVR1 in VT. repeat rewrite <-app_assoc. eapply valt_store_extend. eauto.

      eapply valq_swap; eauto. 
      

      
  - (* Case "App". *)

    eapply safeq_split in H11,H12; destruct H11,H12.
    eapply safeq_split in H11,H12. destruct H11,H12.

    eapply safeq_split in H13. destruct H13.
    eapply safeq_split in H13. destruct H13.
    
    eapply safeq_split in H18,H16. destruct H18,H16.

    rename H11 into SAFE_QF.
    rename H15 into SAFE_Q1. 
    
    (* induction on both subexpressions: obtain vf, vx *)
    destruct (IHW1 M E WFE S) as [S1 [M1 [vf [IW1 [SW1 [HKS1 [HVF HQF]]]]]]]; eauto.

    assert (env_type (M1++M) E env (plift p)) as WFE1. { eapply envt_store_extend. eauto. }

    assert (safe_qual S1 (M1 ++ M) E (plift p) (plift e1)) as SAFE1_E1. eapply safeq_extend; eauto.
    assert (safe_qual S1 (M1 ++ M) E (plift p) (plift k1)) as SAFE1_K1. eapply safeq_extend; eauto.
    
    destruct (IHW2 (M1++M) E WFE1 S1) as [S2 [M2 [vx [IW2 [SW2 [HKS2 [HVX HQX]]]]]]]; eauto.

    assert (safe_qual S M E (plift p) (plift (qor e2 (if e2x then q1 else qempty)))) as SAFE_E2x. eapply safeq_join; eauto.
    assert (safe_qual S M E (plift p) (plift (qor k2 (if k2x then q1 else qempty)))) as SAFE_K2x. eapply safeq_join; eauto.

    assert (psub (pand (plift kf) (plift (qor e2 (if e2x then q1 else qempty)))) pempty). rewrite plift_or, plift_if, plift_empty in *. unfoldq. intros ? [? ?]. eapply H4. split; eauto. 
    assert (psub (pand (plift kf) (plift (qor k2 (if k2x then q1 else qempty)))) pempty). rewrite plift_or, plift_if, plift_empty in *. unfoldq. intros ? [? ?]. eapply H5. split; eauto. 

    assert (safe_qual S1 (M1 ++ M) E (plift p) (plift (qor e2 (if e2x then q1 else qempty)))) as SAFE1_E2. eapply safeq_extend; eauto.
    assert (safe_qual S1 (M1 ++ M) E (plift p) (plift (qor k2 (if k2x then q1 else qempty)))) as SAFE1_K2. eapply safeq_extend; eauto.

    assert (psub (pand (plift k1) (plift (qor e2 (if e2x then q1 else qempty)))) pempty). rewrite plift_or, plift_if, plift_empty in *. unfoldq. intros ? [? ?]. eapply H4. split; eauto. 
    assert (psub (pand (plift k1) (plift (qor k2 (if k2x then q1 else qempty)))) pempty). rewrite plift_or, plift_if, plift_empty in *. unfoldq. intros ? [? ?]. eapply H5. split; eauto. 
    
    assert (safe_qual S2 (M2 ++ M1 ++ M) E (plift p) (plift (qor e2 ((if e2x then q1 else qempty))))) as SAFE2_E2. eapply safeq_extend; eauto.
    assert (safe_qual S2 (M2 ++ M1 ++ M) E (plift p) (plift (qor k2 ((if k2x then q1 else qempty))))) as SAFE2_K2. eapply safeq_extend; eauto.

    assert (psub (pand (por (plift kf) (plift k1)) (por (plift k2) (if k2x then plift q1 else pempty))) pempty). { eauto. }
(*    assert (psub (pand (por (plift kf) (plift k1)) (por (plift q2) (if q2x then plift q1 else pempty))) pempty) as SEP_KF1Q2. { eauto. } *)

    assert (psub (pand (plift k1) (plift qf)) pempty) as SEP_K1QF. eauto. 
    assert (psub (pand (plift qf) (plift k1)) pempty) as SEP_QFK1. unfoldq. intros ? [? ?]. eapply SEP_K1QF. split; eauto. 

    assert (psub (pand (plift kf) (plift k1)) pempty) as SEP_KFK1. eauto. 
    assert (psub (pand (plift kf) (plift k2)) pempty) as SEP_KFK2. unfoldq. intuition. eapply H5. split; eauto. 
    assert (psub (pand (plift k1) (plift k2)) pempty) as SEP_K1K2. unfoldq. intuition. eapply H5. split; eauto. 
      
    assert (safe_qual S1 (M1 ++ M) E (plift p) (if k2x then plift q1 else pempty)) as SAFE1_K2x. { eapply safeq_split in SAFE1_K2. rewrite plift_if, plift_empty in SAFE1_K2. eapply SAFE1_K2. }


    (* NOTE: we're at H24 here *)

    assert True. eauto. 


    (* vf is a function value: it can eval its body *)
    destruct vf; try solve [inversion HVF].

    apply valt_wf in HVX as HVX'.

    destruct HVF; intuition.
    rename H32 into HVF.
    destruct (HVF S2 M2 vx) as [S3 [M3 [vy [IW3 [SW3 [HKS3 [HVY HQY]]]]]]].
    eauto. eauto.
    

    (* separation *) {
      eapply separation. eapply WFE.
      eapply HKS1. eapply HKS2.
      eapply HQF. eapply HQX.
      eauto.
      unfoldq. intuition. eapply SAFE_QF. unfoldq. intuition; eauto. (* qf -- shouldn't need this*)
      unfoldq. intuition. eapply H12. unfoldq. intuition; eauto. (* kf *)
      unfoldq. intuition. eapply SAFE_Q1. unfoldq. intuition; eauto. (* q1 -- shouldn't need this*)
      unfoldq. intuition. eapply H16. unfoldq. intuition; eauto. (* k1 *)
      eauto. eauto. eauto. eauto. 
    }
    
    (* effect separation: e2/e2x not killed/moved *) {
      intros ? YY.
      destruct YY as [? YY]. destruct YY.
      (* e2 *) eapply SAFE2_E2. unfoldq. intuition. destruct H32. exists x0. unfoldq. intuition.
      (* e2x/q1 *) rewrite plift_or, plift_if, plift_empty. left. eauto. 
      destruct e2x. eapply valq_safe. eauto. eauto. eapply safeq_split. eauto. eauto. eauto. eauto. eauto. 
    }
    
    (* effect separation: k2/k2x not killed/moved *) {
      intros ? YY.
      destruct YY as [? YY]. destruct YY.
      (* k2 *) eapply SAFE2_K2. unfoldq. intuition. destruct H32. exists x0. unfoldq. intuition.
      (* k2x/q1 *) rewrite plift_or, plift_if, plift_empty. left. eauto. 
      destruct k2x. eapply valq_safe. eauto. eauto. eapply safeq_split. eapply SAFE1_K2. eauto. eauto. eauto. eauto. 
    }

    
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

      repeat rewrite <-app_assoc in *.

      
      
      repeat rewrite plift_or in *.
      repeat rewrite plift_if in *.
      repeat rewrite plift_empty in *.


      assert (store_qual S1 (M1 ++ M) E S2 M2 vx (plift p) (plift k1)) as SQ12. {
        eapply HKS2.
      }

      assert (store_qual S M E S1 M1 (vabs l q t0) (plift p) (plift kf)) as SQ01. {
        eapply HKS1.
      }

      assert (store_qual S M E S2 (M2++M1) vx (plift p) (por (plift kf) (plift k1))) as SQ02. {
        eapply storeq_seq. eauto. 
        3: eapply SQ01.
        3: eapply SQ12.  
        3: eapply HQX. 
        eauto. eauto. 
      }

      rename HKS3 into SQ3.
      destruct HKS2 (* SQ02 *) as [SQ2 ?].
      destruct HKS1 as [SQ1 ?].

      remember (vabs l q t0) as vf. 

      (*
      assert (psub (val_locs vf) (pnot (st_moved S1 (M1++M)))) as SAFE1_VF. {
        unfoldq. intuition.
        destruct (SQ1 x) as [H_K | [H_k | H_fr]]. eauto. 
        - (* K *) eapply SAFE_F0; eauto.
        - (* k *) intuition.
        - (* fr *) intuition.
      }

      assert (psub (val_locs vf) (pnot (st_moved S2 (M2++M1++M)))) as SAFE2_VF. {
        unfoldq. intuition.  
        destruct (SQ2 x) as [H_K | [H_k | H_fr]]. eauto. 
        - (* K *) eapply SAFE1_VF; eauto.
        - (* k *) destruct H_k. 
          destruct (HQF x) as [H1_q | [H1_k | [H1_mv | H1_fr]]]. eauto.
          eapply env_sep_contra. eauto. 2: eapply H1_q. 2: eapply H35. eauto. 
          eapply env_sep_contra. eauto. 2: eapply H1_k. 2: eapply H35. eauto. 
          eapply H16. (* safe k1 *) unfoldq. intuition. eauto. eapply H35.
          eapply env_wf_contra. eapply WFE. eauto. intros ?. eapply H1_fr. eauto. 
        - (* fr *) intuition.
      }*)


      (* XXX predicate on q2x/e2x/k2x ? *)
      assert (safe_qual S1 (M1++M) E (plift p) (plift q1) -> psub (val_locs vx) (pnot (st_moved S2 (M2++M1++M)))) as SAFE2_VX. {
        intros. eapply valq_safe. eauto. eauto. eauto. (* safe q1 !*)
        eauto.
      }

      (* dealing with fresh parts of vx, vy that may have been moved/deallocated *)

      (* key: if we're deallocating fresh parts of vx, we can't return them *)
      
      assert (store_qual S M E S3 (M3++M2++M1) vy (plift p)
                (por (plift kf) (por (plift k1) (por (plift k2) (if k2x then (plift q1) else pempty))))) as HYS2. {
        split. {
        intros ? ?.
        destruct (SQ3 x) as [H_K | [H_k | [H_k2x | H_fr]]]. eauto. 
        - (* K *)
          destruct (SQ2 x) as [H2_K | [H2_k | H2_fr]]. eauto.
          + (* K *) 
            destruct (SQ1 x) as [H1_K | [H1_k | H1_fr]]. eauto. 
            * (* K *) left. eauto. 
            * (* kf *) right. left. destruct H1_k. destruct H34. split. exists x0. unfoldq. intuition.
              intros ?. destruct (HQY x) as [Y_q2f | [Y_q2x | [Y_k2f | [Y_k2x | [Y_mv | Y_fr]]]]]. eauto.
              (* Y_q2f *) destruct Y_q2f. eauto. 
              (* Y_q2x *) destruct q2x; try contradiction.
                destruct (HQX x) as [X_q | [X_k | [X_mv | X_fr]]]. eauto. 
                (* q1 *) eapply env_sep_contra. eapply WFE. 2: { exists x0; eauto. }  2: eapply X_q. eauto. 
                (* k1 *) eapply env_sep_contra. eapply WFE. 2: { exists x0; eauto. }  2: eapply X_k. eauto. 
                (* mv *) destruct X_mv. eauto. 
                (* fr *) eapply env_wf_contra. eapply WFE. exists x0. eauto. unfoldq. intuition. 
                (* -- *)
              (* Y_k2f *) destruct Y_k2f. eauto. 
              (* Y_k2x *) destruct k2x; try contradiction. eapply SAFE2_VX. eauto. eauto. eauto.
              (* Y_mv  *) unfoldq. intuition. 
              (* Y_fr  *) eapply env_wf_contra. eapply WFE. exists x0. eauto. unfoldq. repeat rewrite app_length in *. lia. 
              
            * (* fr *)  right. right. unfoldq. repeat rewrite app_length in *. intuition.
              destruct (HQY x) as [Y_q2f | [Y_q2x | [Y_k2f | [Y_k2x | [Y_mv | Y_fr]]]]]. eauto.  
              (* Y_q2f *) destruct Y_q2f. eauto. 
              (* Y_q2x *) destruct q2x; try contradiction.
                destruct (HQX x) as [X_q | [X_k | [X_mv | X_fr]]]. eauto. 
                (* q1 *) eapply env_wf_contra. eapply WFE. eapply X_q. eauto. 
                (* k1 *) eapply env_wf_contra. eapply WFE. eapply X_k. eauto. 
                (* mv *) destruct X_mv. eauto. 
                (* fr *) intuition. 
                (* -- *)
              (* Y_k2f *) destruct Y_k2f. eauto. 
              (* Y_k2x *) destruct k2x; try contradiction. eapply SAFE2_VX. eauto. eauto. eauto.
              (* Y_mv  *) unfoldq. intuition.
              (* Y_fr  *) lia. 
          
          + (* k1 *) right. left. destruct H2_k. destruct H34. split. exists x0. unfoldq. intuition.
            intros ?.
              destruct (HQY x) as [Y_q2f | [Y_q2x | [Y_k2f | [Y_k2x | [Y_mv | Y_fr]]]]]. eauto.  
              (* Y_q2f *) destruct Y_q2f.
                destruct (HQF x) as [X_q | [X_k | [X_mv | X_fr]]]. eauto. 
                (* qf *) eapply env_sep_contra. eapply WFE. 2: eapply X_q. 2: exists x0; eauto. eauto. 
                (* kf *) eapply env_sep_contra. eapply WFE. 2: eapply X_k. 2: exists x0; eauto. eauto. 
                (* mv *) destruct X_mv. eapply H16. (* safe K1 ! *) unfoldq. intuition. eauto. eauto. 
                (* fr *) destruct X_fr. eapply env_wf_contra. eapply WFE. exists x0. intuition; eauto. intuition. 
                (* -- *)
              (* Y_q2x *) destruct q2x; try contradiction.  
              (* Y_k2f *) destruct Y_k2f. eapply env_sep_contra. eapply WFE. 2: { exists x0. eauto. } 2: {destruct H37. exists x1. unfoldq. intuition. eauto. } eauto. 
              (* Y_k2x *) destruct k2x; try contradiction. 
              (* Y_mv  *) unfoldq. intuition.
              (* Y_fr  *) eapply env_wf_contra. eapply WFE. exists x0. eauto. unfoldq. repeat rewrite app_length in *. lia. 

          + (* fr *) destruct H2_fr.
            right. right. unfoldq. repeat rewrite app_length in *. intuition.
            destruct (HQY x) as [Y_q2f | [Y_q2x | [Y_k2f | [Y_k2x | [Y_mv | Y_fr]]]]]. eauto.  
            (* Y_q2f *) destruct Y_q2f. eapply env_wf_contra. eapply WFE. destruct H38. exists x0. unfoldq. intuition. eauto. eauto. intuition. 
            (* Y_q2x *) destruct q2x; try contradiction. 
            (* Y_k2f *) destruct Y_k2f. eapply env_wf_contra. eapply WFE. destruct H38. exists x0. unfoldq. intuition. eauto. eauto. intuition. 
            (* Y_k2x *) destruct k2x; try contradiction. 
            (* Y_mv  *) unfoldq. intuition.
            (* Y_fr  *) lia. 

        - (* k *) right. left. destruct H_k. unfoldq. intuition. destruct H34. exists x0. unfoldq. intuition.
        - (* k2x/q1 *) destruct k2x. 2: { unfoldq. intuition. }
                                 destruct H_k2x. (* unfoldq. intuition. *)
            destruct (HQX x) as [X_q | [X_k | [X_mv | X_fr]]]. eauto. 
            (* q *) right. left. unfoldq. intuition. destruct X_q. exists x0. unfoldq. intuition.
            (* k *) right. left. unfoldq. intuition. destruct X_k. exists x0. unfoldq. intuition. 
            (* mv *) destruct X_mv.

              destruct (SQ1 x) as [H1_K | [H1_k | H1_fr]]. eauto. 
              (* K *) left. eauto. 
              (* kf *) right. left. unfoldq. intuition. destruct H38. exists x0. unfoldq. intuition.
              (* fr *) right. right. unfoldq. intuition. repeat rewrite app_length in *. lia. 
            
            (* fr *) right. right. unfoldq. intuition. repeat rewrite app_length in *. unfoldq. intuition.
            repeat rewrite app_length in *. unfoldq. intuition. 
                                     
        - (* fr *)
          right. right. unfoldq. repeat rewrite app_length in *. split. split. lia. lia. intuition.

        } {
          eauto.
        }
      }

      
      assert (val_qual S M S3 (M3++M2++M1) E vy (plift p)
                   (por (plift q2) (if q2x then (plift q1) else pempty)) 
                   (por (plift kf) (por (plift k1) (por (plift k2) (if k2x then (plift q1) else pempty))))) as HQY'. {
        intros ? ?.
        assert (x < length (M3 ++ M2 ++ M1 ++ M)). eapply valt_wf. eauto. eauto.
        (* bdestruct (x <? length (M2 ++ M1 ++ M)). *)
        destruct (HQY x) as [Y_q2f | [Y_q2x | [Y_k2f | [Y_k2x | [Y_mv | Y_fr]]]]]. eauto.  
        + (* q2f *) left. unfoldq. intuition.
          destruct H35. exists x0. intuition.
        + (* q2x *) destruct q2x. 2: { contradiction. } (**)
          destruct (HQX x) as [HX_q | [HX_k | [HX_mv | HX_fr]]]. eauto. 
          * (* - HX_q *) left. unfoldq. destruct HX_q. exists x0. intuition.
          * (* - HX_m *) right. left.  destruct HX_k. exists x0. unfoldq. intuition.
          * (* - HX_mv *) destruct HX_mv.
            destruct (SQ1 x) as [SF_K | [SF_k | SF_fr]]. eauto.
              (* K *) right. right. left. split. eauto. intros ?.
              destruct HYS2 as [S3' ?].
              destruct (SQ3 x) as [SS_K | [SS_k2 | [SS_k2x | SS_fr]]]. eauto.
                (* K *) eauto. 
                (* k *) eapply SAFE1_K2. split. eauto. destruct SS_k2. destruct H39. exists x0. unfoldq. intuition. 
                (* k2x *) destruct SS_k2x. eauto. 
                (* fr *) unfoldq. intuition. 
            (* k *) right. left. unfoldq. intuition. destruct H37. exists x0. intuition.
            (* fr *) right. right. right. unfoldq. repeat rewrite app_length in *. intuition.
          * (* - HX_fr *) right. right. right. unfoldq. repeat rewrite app_length in *. intuition.
        + (* k2f *) right. left. unfoldq. intuition.
          destruct H35. exists x0. intuition.
        + (* k2x *) destruct k2x. 2: { contradiction. } (**)
          destruct (HQX x) as [HX_q | [HX_k | [HX_mv | HX_fr]]]. eauto. 
          * (* - HX_q *) right. left. unfoldq. destruct HX_q. exists x0. intuition.
            * (* - HX_m *) right. left.  destruct HX_k. exists x0. unfoldq. intuition.
            * (* - HX_mv *) destruct HX_mv.
              destruct (SQ1 x) as [SF_K | [SF_k | SF_fr]]. eauto.
              (* K *) right. right. left. split. eauto. intros ?.
              destruct HYS2 as [S3' ?].
              destruct (SQ3 x) as [SS_K | [SS_k2 | [SS_k2x | SS_fr]]]. eauto.
                (* K *) eauto. 
                (* k *) eapply SAFE1_K2. split. eauto. destruct SS_k2. destruct H39. exists x0. unfoldq. intuition. 
                (* k2x *) destruct SS_k2x. eauto. 
                (* fr *) unfoldq. intuition. 
              (* k *) right. left. unfoldq. intuition. destruct H37. exists x0. intuition.
              (* fr *) right. right. right. unfoldq. repeat rewrite app_length in *. intuition.
            * (* - HX_fr *) right. right. right. unfoldq. repeat rewrite app_length in *. intuition.
        + (* mv *) destruct Y_mv. 
          destruct SQ02 as [SQ02 ?].
          destruct (SQ02 x) as [H_K | [H_k | H_fr]]. eauto.
          * (* K *) right. right. left. split; eauto.
          * (* k *) destruct H_k. intuition.
            right. left. destruct H38. exists x0. unfoldq. intuition.
          * (* fr *) right. right. right. unfoldq. repeat rewrite app_length in *. intuition.
        + (* fr *) right. right. right. unfoldq. repeat rewrite app_length in *. intuition. 
      }


      split. 2: split. 3: split.
      eauto.
      repeat rewrite por_assoc. eapply HYS2.
      eauto. 
      repeat rewrite por_assoc. eapply HQY'. 


      
  - (* Case "Abs". *)
    exists S. exists []. exists (vabs E (qand p qf) t).
    split.
    + (* term evaluates *)
      exists 0. intros. destruct n. lia. simpl. eauto.
    + (* result well typed *)
      rewrite app_nil_l. rewrite plift_empty in *.
      split. 2: split. 3: split.

      eauto. 

      rewrite <-plift_empty. eapply storeq_empty. eauto.

      simpl. rewrite <-LE in *. intuition; eauto.
      rewrite val_locs_abs. unfoldq. intuition.
      eapply env_type_store_wf. eauto. eauto. 


      assert (env_type (M' ++ M) (vx :: E) (T1 :: env) (plift (qor (qand p qf) (qone (length E))))) as WFE1. {
        rewrite val_locs_abs, plift_and in H10. 
        rewrite plift_or, plift_and, plift_one.
        eapply envt_extend_all; eauto.
      }
      
      destruct (IHW (M'++M) (vx::E)) with (S:=S') as [S'' [M'' [vy [IW3 [SW3 [HKS3 [HVY HQY]]]]]]]. 
      eauto. eauto.

      
      (* safe qual e -- needs to extend wrt vx *)
      {
        rename H11 into SAFE_E.
        rename H12 into SAFE_K.
        intros ? ?. destruct H11 as [? [? ?]]. destruct (SAFE_E x).
        unfoldq. intuition.
        bdestruct (x0 =? length E).
        - subst x0. rewrite plift_or, plift_and, plift_if, plift_one, plift_empty in *.
          right. destruct e2x.
          rewrite indexr_head in H14. destruct H14. destruct H13. congruence.
          destruct H15. eapply H3 in H13. lia. contradiction.
        - rewrite plift_or, plift_and, plift_if, plift_one, plift_empty in *.
          rewrite indexr_skip in H14; eauto.
          left. exists x0. intuition. destruct H15. eauto. destruct e2x; contradiction. 
      }

      (* safe qual k -- needs to extend wrt vx *)
      {
        rename H11 into SAFE_E.
        rename H12 into SAFE_K.
        intros ? ?. destruct H11 as [? [? ?]]. destruct (SAFE_K x).
        unfoldq. intuition.
        bdestruct (x0 =? length E).
        - subst x0. rewrite plift_or, plift_and, plift_if, plift_one, plift_empty in *.
          right. destruct k2x.
          rewrite indexr_head in H14. destruct H14. destruct H13. congruence.
          destruct H15. eapply H4 in H13. lia. contradiction.
        - rewrite plift_or, plift_and, plift_if, plift_one, plift_empty in *.
          rewrite indexr_skip in H14; eauto.
          left. exists x0. intuition. destruct H15. eauto. destruct k2x; contradiction. 
      }

      exists S'', M'', vy.
      
      intuition.

      (* store_qual *)
      {
        intros ? ?. destruct HKS3 as [SQ3 ?].
        destruct (SQ3 x) as [H_K | [H_k | H_fr]]. eauto. 
        - (* K *) left. eauto.
        - (* k *) destruct H_k as [H_k ?]. rewrite plift_or, plift_or, plift_and, plift_if, plift_one in H_k. unfoldq. destruct H_k. destruct H16. destruct H16. destruct H18.
          + (* k2 *) right. left. intuition. exists x0. intuition. eapply var_locs_shrink. eauto. eapply WFE. eauto.
            subst x0. eapply H4 in H18. lia. 
          + (* k2x/vx *) right. right. left. destruct k2x. 2: { unfoldq. intuition. } subst x0. unfoldq. destruct H17. rewrite indexr_head in H17. intuition. congruence. congruence. 
        - (* fr *) unfoldq. intuition.
      }
      
      eapply valt_extend1; eauto.  (* val_type *)

      (* val_qual *)
      {
        intros ? ?.
        destruct (HQY x) as [H_q | [H_m | [H_mv | H_fr]]]. unfoldq. intuition. 
        - (* q *) rewrite plift_or, plift_and, plift_or, plift_if, plift_one, plift_empty in H_q.
          destruct H_q as [? [[C1 C2] ?]]. destruct C1; destruct C2.
          + (* q2,qf *) left. unfoldq. intuition. exists x0. intuition. eapply var_locs_shrink. eauto. eapply WFE. eauto.
            rewrite val_locs_abs. exists x0. rewrite plift_and. unfoldq. intuition. eapply var_locs_shrink. eauto. eapply WFE. eauto.
          + (* q2x/q1,qf - contra *) destruct q2x; try contradiction.
            assert (length E < length E). unfoldq. intuition. eapply WFE. subst x0. eauto. lia.
          + (* q2,x - contra *) assert (length E < length E). unfoldq. intuition. eapply H2. subst x0. eauto. lia.
          + (* q2x/q1,x *) destruct q2x; try contradiction.
            unfoldq. intuition. subst x0. rewrite indexr_head in H14. destruct H14. destruct H14. inversion H14. subst x0.
            intuition.
        - (* m *) rewrite plift_or, plift_and, plift_or, plift_if, plift_one, plift_empty in H_m.
          destruct H_m as [? [[C1 C2] ?]]. destruct C1; destruct C2.
          
          + (* q2,qf *) right. right. left. unfoldq. intuition. exists x0. intuition. eapply var_locs_shrink. eauto. eapply WFE. eauto.
            rewrite val_locs_abs. exists x0. rewrite plift_and. unfoldq. intuition. eapply var_locs_shrink. eauto. eapply WFE. eauto.
          + (* q2x/q1,qf - contra *) destruct k2x; try contradiction.
            assert (length E < length E). unfoldq. intuition. eapply WFE. subst x0. eauto. lia.
          + (* q2,x - contra *) assert (length E < length E). unfoldq. intuition. eapply H4. subst x0. eauto. lia.
          + (* q2x/q1,x *) destruct k2x; try contradiction.
            unfoldq. intuition. subst x0. rewrite indexr_head in H14. destruct H14. destruct H14. inversion H14. subst x0.
            intuition.

        - (* mv *) unfoldq. intuition.
        - (* fr *) unfoldq. intuition. 
      }
      
      rewrite <-plift_empty. eapply valq_abs. 

      
  -  (* Case "Sub". *)
    destruct (IHW M E WFE S) as [S1 [M1 [vx [IW1 [SW1 [SQ1 [HVX HQX]]]]]]]. { eauto. }

    (* safeq_sub *)
    intros ? ?. destruct H8. eapply H6. unfoldq. intuition. destruct H9. exists x0. intuition.
    intros ? ?. destruct H8. eapply H7. unfoldq. intuition. destruct H9. exists x0. intuition. 

    exists S1, M1, vx.
    unfold exp_type. intuition.

    (* storeq_sub *) {
      destruct SQ1 as [SQ1 ?].
      split; eauto. intros ? ?. destruct (SQ1 x) as [H_K | [H_k | H_fr]]. eauto.
      + left. eauto.
      + right. left. unfoldq. intuition. destruct H10. exists x0. intuition. 
      + right. right. unfoldq. intuition. 
    }

    eapply valq_sub; eauto. rewrite DE. eauto. rewrite DE. eauto.
Qed.


(* note: not assuming anything other than has_type below *)

Corollary safety : forall t T q e k,
  has_type [] t T qempty q e k -> 
  exists S M v, exp_type [] [] [] t S M v T (plift qempty) (plift q) (plift e) (plift k).
Proof. 
  intros. eapply full_total_safety in H; eauto.
  unfold env_type; intuition; simpl. unfoldq. intuition. inversion H0.
  unfold store_type. intuition. inversion H0. inversion H0. inversion H0. 
  intros ? ?. rewrite plift_empty in H0. unfoldq. intuition. destruct H2. intuition.
  intros ? ?. rewrite plift_empty in H0. unfoldq. intuition. destruct H2. intuition.  
Qed.

End STLC.
