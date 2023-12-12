(* Full safety for STLC *)

(* based on stlc_reach.v and stlc_ref.v *)
(* based on stlc_reach_ref_move.v and stlc_reach_ref_nested_stty.v *)


(*
WIP: MOVE SEMANTICS

This file explores explicit move qualifiers (distinct from free).

Key challenge: a single store location is both "old" and "fresh".
The "old" access path should be disabled, but the "fresh" one
should remain.

Consider:

    get(move(x))      // ok

    move(x); get(x)   // error
        
Or:

    free(move(x))     // ok

    move(x); free(x)  // error


Approach explored here:

(A) val_qual (and therefore exp_type) ensures that
    locs(v) is partitioned three ways:

    1. old location (in dom(M)), covered by q
    2. old location, covered by m (move qualifier)
    3. new location, in dom(M1)-dom(M) 

    Previously, only 1. and 3. existed.

(B) exp_type removes m-locs(v) from the store typing,
    in addition to k and (dom(M1)-dom(M))-v


Questions:

(a): does it work to (ab)use the move qualifier this way?

    get(e)   // <-- seems ok if e's k and m are separate

    free(e)  // <-- seems unclear how to distinguish
                    free(move(x)) from move(x); free(x) ?

                    XX taken care of by m - locs(v) 

(b): what kind of store invariants etc will be needed
     once we have nested refs?

(c): should val_qual use m-k instead of m?

     this might remove the k sep m check in tget

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
- move effects (THIS FILE!)
- nested variables (THIS FILE!)

Cleanup - todo:

- some bits feel repetitive, what are suitable lemmas?

Extensions:

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
  | TFun   : ty -> (* qempty -> *) ty -> ql -> ql -> ql -> ql -> bool -> bool -> bool -> bool -> ty
.

(* TFun
        T1      : argument type
        T2      : result type

        q2      : result reachability qualifer (set of variables)
        e2      : result use effect qualifier (set of variables)
        k2      : result kill effect qualifier (set of variables)
        m2      : result move effect qualifier (set of variables)

        q2x     : argument reachable from result?
        e2x     : argument used?
        k2x     : argument killed?
        m2x     : argument moved?

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
  | tmove : tm -> tm
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
| c_fun: forall m T1 T2 q2 e2 k2 m2 q2x e2x k2x m2x,
    closed_ty m T1 ->
    closed_ty m T2 ->   (* not dependent *)
    closed_ql m q2 ->
    closed_ql m e2 ->
    closed_ql m k2 ->
    closed_ql m m2 ->
    closed_ty m (TFun T1 (* qempty *) T2 q2 e2 k2 m2 q2x e2x k2x m2x)
.


(* assume no overlap *)
Inductive has_type : tenv -> tm -> ty -> ql -> ql -> ql -> ql -> ql -> Prop :=
| t_true: forall env p,
    has_type env ttrue TBool p qempty qempty qempty qempty   (* nothing reachable from a primitive *)
| t_false: forall env p,
    has_type env tfalse TBool p qempty qempty qempty qempty
| t_var: forall x env T  p,
    indexr x env = Some T ->
    (plift p) x ->                         (* x in phi *)
    has_type env (tvar x) T p (qone x) qempty qempty qempty (* x can reach only itself (no overlap) *)
| t_ref: forall t env T p q e k m,
    has_type env t T p q e k m ->
    has_type env (tref t) (TRef T) p q e k m
| t_get: forall t env T p q e k m,
    has_type env t (TRef T) p q e k m ->
    psub (pand (plift k) (plift q)) pempty -> (* no kill before use *)
    psub (pand (plift m) (plift q)) pempty -> (* no move before use *)
    psub (pand (plift k) (plift m)) pempty -> (* no kill && move  <--  ?? *)
    (* XXX k & m:
       if we're dereferencing a Ref that's been moved, it'll be in m,
       we also have to make sure it hasn't been killed.
       Is this what we want?
       Could we ensure it generically for every expression in val_qual?
     *)
    has_type env (tget t) T p q (qor e q) k m
| t_free: forall t env T p q e k m,
    has_type env t (TRef T) p q e k m ->
    psub (pand (plift m) (plift q)) pempty -> (* no move before kill *)
    has_type env (tfree t) TBool p qempty e (qor k q) m (* always return 'false' *)
| t_move: forall t env T p q e k m,
    has_type env t (TRef T) p q e k m ->
    psub (pand (plift k) (plift q)) pempty -> (* no kill before move *)
    psub (pand (plift m) (plift q)) pempty -> (* no move before move *)
    has_type env (tmove t) (TRef T) p qempty e k (qor m q) 
| t_app: forall env f t T1 T2 p qf q1 q2 ef e1 e2 kf k1 k2 mf m1 m2 q2x e2x k2x m2x,
    has_type env f (TFun T1 (* qempty  *) T2 q2 e2 k2 m2 q2x e2x k2x m2x) p qf ef kf mf ->  
    has_type env t T1 p q1 e1 k1 m1 ->

    (* For moves:

       we'll need (of course)
         mf & m1 = 0

       but apparently also
         mf & q1 = 0
         qf & m1 = 0

       This makes sense given the encoding but also seems a bit
       unnecessary. 

       Would it be enough to enforece separation only for
       variables in e2, i.e., those that will be used?

       Right now we expect separation for all variables, i.e.,
       if m1 moves something that's part of qf, *and* returns it
       as part of vx, then we can't guarantee separation
       between vf and vx.

       Idea: take e2 as the p for functions??
     *)

    psub (pand (plift qf) (plift q1)) pempty ->          (* no overlapping *)

    psub (pand (plift qf) (plift m1)) pempty ->          (* extra! no q/m overlap, see above *)
    psub (pand (plift mf) (plift q1)) pempty ->          (* extra! no q/m overlap, see above *)
    
    (* effect 1/2 *)
    psub (pand (plift kf) (plift e1)) pempty ->          (* no kill before use  *)
    psub (pand (plift kf) (plift m1)) pempty ->          (* no kill before move *)
    psub (pand (plift mf) (plift e1)) pempty ->          (* no move before use  *)
    psub (pand (plift mf) (plift k1)) pempty ->          (* no move before kill *)
    psub (pand (plift mf) (plift m1)) pempty ->          (* no move before move *)

    psub (pand (plift k1) (plift m1)) pempty ->          (* no kill && move *)
    
    (* effect 2/3 *)
    psub (pand (por (plift kf) (plift k1))  (por (plift e2) (if e2x then (plift q1) else pempty))) pempty -> (* no kill before use  *)
    psub (pand (por (plift kf) (plift k1))  (por (plift m2) (if m2x then (plift q1) else pempty))) pempty -> (* no kill before move *)
    psub (pand (por (plift mf) (plift m1))  (por (plift e2) (if e2x then (plift q1) else pempty))) pempty -> (* no kill before use  *)
    psub (pand (por (plift mf) (plift m1))  (por (plift k2) (if k2x then (plift q1) else pempty))) pempty -> (* no kill before kill *)
    psub (pand (por (plift mf) (plift m1))  (por (plift m2) (if m2x then (plift q1) else pempty))) pempty -> (* no kill before move *)

    (* qualifier well-formedness *)
    psub (plift q2) (plift p) ->
    psub (plift e2) (plift p) ->
    psub (plift k2) (plift p) ->
    psub (plift m2) (plift p) ->
    
    (* NOTE: we can return OR kill the function arg, but not both.  *)
    (*       possible to refine: only an issue if the function arg may be fresh! *)
    (k2x = true -> q2x = false) ->
    (k2x = true -> m2x = false) ->
    
    has_type env (tapp f t) T2 p
      (qor q2                   (if q2x then q1 else qempty))
      (qor (qor ef (qor e1 e2)) (if e2x then q1 else qempty))
      (qor (qor kf (qor k1 k2)) (if k2x then q1 else qempty))
      (qor (qor mf (qor m1 m2)) (if m2x then q1 else qempty)) (* TODO: assoc por m2 (if m2x ...)? *)
      
| t_abs: forall env t T1 T2 p q2 qf e2 k2 m2 (q2x e2x k2x m2x: bool),
    has_type (T1::env) t T2
      (qor (qand p qf) (qone (length env)))
      (qor q2 (if q2x then (qone (length env)) else qempty))
      (qor e2 (if e2x then (qone (length env)) else qempty))
      (qor k2 (if k2x then (qone (length env)) else qempty))
      (qor m2 (if m2x then (qone (length env)) else qempty)) ->
    closed_ty (length env) T1 ->
    closed_ty (length env) T2 ->
    closed_ql (length env) qf ->
    closed_ql (length env) q2 ->
    closed_ql (length env) e2 ->
    closed_ql (length env) k2 ->
    closed_ql (length env) m2 ->
    (*  *)
    has_type env (tabs (qand p qf) t) (TFun T1 T2 q2 e2 k2 m2 q2x e2x k2x m2x) p qf qempty qempty qempty
| t_sub: forall env y T p q1 q2 e1 e2 k1 k2 m1 m2,
    has_type env y T p q1 e1 k1 m1 ->
    psub (plift q1) (plift q2) ->
    psub (plift e1) (plift e2) ->
    psub (plift k1) (plift k2) ->
    psub (plift m1) (plift m2) ->
    psub (plift q2) (pdom env) ->
    psub (plift e2) (pdom env) ->
    psub (plift k2) (pdom env) ->
    psub (plift m2) (pdom env) ->
    has_type env y T p q2 e2 k2 m2
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
        | tmove ex    =>
          match teval n M env ex with
            | (M', None) => (M', None)
            | (M', Some None) => (M', Some None)
            | (M', Some (Some (vbool _))) => (M', Some None)
            | (M', Some (Some (vabs _ _ _))) => (M', Some None)
            | (M', Some (Some (vref x))) => (M', Some (Some (vref x))) (* no-op *)
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
  | vabs G py ty, TFun T1 (* qempty *) T2 q2 e2 k2 m2 q2x e2x k2x m2x => (* TODO! *)
      closed_ty (length H) T1 /\
        closed_ty (length H) T2 /\
        (psub (plift q2) (pdom H)) /\
        (psub (plift e2) (pdom H)) /\
        (psub (plift k2) (pdom H)) /\
        (psub (plift m2) (pdom H)) /\
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
              psub (pand (val_locs M v) (val_locs (M'++M) vx)) pempty
            ->
              psub
                (pand K'
                   (por (vars_locs (M'++M) H (plift e2))
                      (if e2x then (val_locs (M'++M) vx) else pempty)))
                pempty
            ->
              psub
                (pand K'
                   (por (vars_locs (M'++M) H (plift m2))
                      (if m2x then (val_locs (M'++M) vx) else pempty)))
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
                       (por (vars_locs (M'++M) H (plift k2))
                          (por (if k2x then (val_locs (M'++M) vx) else pempty)  
                             (por (pdiff (vars_locs (M'++M) H (plift m2)) (val_locs (M''++M'++M) vy))
                                (por (if m2x then (pdiff (val_locs (M'++M) vx) (val_locs (M''++M'++M) vy)) else pempty)  (* - vy?*)
                                   (pdiff (pdiff (pdom (M''++M'++M)) (pdom (M'++M))) (val_locs (M''++M'++M) vy)))))))
                /\
                  val_type
                    (M''++M'++M)
                    H
                    vy
                    T2
                /\
                  psub (val_locs (M''++M'++M) vy)
                    (por (pand (vars_locs (M'++M) H (plift q2)) (val_locs M v))
                       (por (if q2x then (val_locs (M'++M) vx) else pempty)
                          (por (pand (vars_locs (M'++M) H (plift m2)) (val_locs M v))
                             (por (if m2x then (val_locs (M'++M) vx) else pempty)
                                (pnot (pdom (M'++M))))))))
  | _,_ =>
      False
  end.


Definition val_qual (M M': stty) H v (p q m: pl) :=
  psub (val_locs (M'++M) v)
    (por (vars_locs (M'++M) H (pand p q))
      (por (vars_locs (M'++M) H (pand p m))
        (pnot (pdom M)))).


Definition exp_type S M K H t S' M' v T (p q e k m: pl) :=
  tevaln S H t S' v /\
    store_type S' (M'++M) (por K
                             (por (vars_locs M H (pand p k))
                                (por (pdiff (vars_locs M H (pand p m)) (val_locs (M'++M) v)) 
                                   (pdiff (pdiff (pdom (M'++M)) (pdom M))
                                      (val_locs (M'++M) v))))) /\ 
    val_type (M'++M) H v T /\
    val_qual M M' H v p q m.

(* kill set after evaluating t to v is the union of:
   - previous cumulative kill set K
   - existing observable locations mentioned by t's effect annotation k (i.e., p /\ k)
   - NEW: locations that were moved but aren't reachable from result v
   - fresh locations allocated during evaluation of t that aren't reachable from result v
 *)
   
(* move set, in val_qual:
   - pre-existing location is either covered by qual or move set
*)


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

Lemma pand_dist_or1: forall p e q,
    (pand (por (e) (q)) p) =
      (por (pand (e) (p)) (pand (q) (p))).
Proof.
  intros. eapply functional_extensionality.
  intros. eapply propositional_extensionality.
  unfoldq. intuition.
Qed.

Lemma psub_dist_or: forall a b c,
    psub (por a b) c =
      (psub a c /\ psub b c).
Proof.
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

Lemma vars_locs_store_extend: forall M M' H q,
    psub (vars_locs M H q) (pdom M) ->
    vars_locs M H q = vars_locs (M'++M) H q.
Proof.
  intros. apply functional_extensionality.
  intros. apply propositional_extensionality.
  unfoldq. intuition.
  - destruct H1. exists x0. intuition.
    rewrite <-var_locs_store_extend. eauto.
    unfoldq. intuition. eapply H0. eauto.
  - destruct H1. exists x0. intuition.
    rewrite <-var_locs_store_extend in H3. eauto.
    unfoldq. intuition. eapply H0. eauto. 
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
  + destruct H2 as [vt [qt [IX VT]]].
    exists vt, qt. intuition. eapply indexr_extend in IX; intuition. eauto.
    unfoldq. intuition. rewrite app_length. eapply H2 in H3. lia.
  + unfoldq. intuition. rewrite <-val_locs_extend in H7. eapply H6 in H7. rewrite app_length. lia. eauto.
  +
    assert (val_locs (M' ++ M) (vabs l q3 t) =
            val_locs        M  (vabs l q3 t)) as VF. {
      rewrite <-val_locs_extend; eauto. 
    }
    
    destruct (H8 S' (M'0++M') K' vx) as [S'' [M'' [vy  [IEY [ST [HVY HSEP]]]]]]. 
    rewrite <-app_assoc. auto.
    rewrite <-app_assoc. auto.
    rewrite <-app_assoc. rewrite <-VF. eauto. 
    rewrite <-app_assoc. eauto. 
    rewrite <-app_assoc. eauto. 
    
    exists S'', M''. exists vy. rewrite VF. intuition.
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
    destruct H3 as [vt [qt [IX HVX]]].
    exists vt, qt. intuition.
    eapply IHT; eauto. 
  - inversion H0. auto.
  - inversion H0. auto.
  - inversion H0. auto.
  - inversion H0. auto.
  - inversion H0. auto.
  - inversion H0. auto.
  - (* Abs shrink *)
    inversion H0. subst.
(*    rename q into q2.  *)
    destruct (H9 S' M' K' vx) as [S'' [M'' [vy [HEY HVY]]]].
      eauto.
      eapply IHT1; eauto.
      eauto.
      rewrite vars_locs_extend. eauto. eauto.
      rewrite vars_locs_extend. eauto. eauto.
    exists S'', M'', vy. intuition.
    rewrite vars_locs_extend in H14.
    rewrite vars_locs_extend in H14.
    eauto. eauto. eauto. 
    eapply IHT2; eauto.
    rewrite vars_locs_extend in H17.
    rewrite vars_locs_extend in H17.
    eauto. eauto. eauto.
  - eapply closedty_extend; eauto.
  - eapply closedty_extend; eauto.
  - unfoldq. rewrite app_length. intuition. eapply H3 in H8. lia.
  - unfoldq. rewrite app_length. intuition. eapply H4 in H8. lia.
  - unfoldq. rewrite app_length. intuition. eapply H5 in H8. lia.
  - unfoldq. rewrite app_length. intuition. eapply H6 in H8. lia.
  - (* Abs grow *)
    inversion H0. subst.
(*    rename q into q2. *)
    destruct (H9 S' M' K' vx) as [S'' [M'' [vy [HEY [HVY HQY]]]]].
      eauto.
      eapply IHT1; eauto.
      eauto.
      rewrite vars_locs_extend in H12. eauto. eauto.
      rewrite vars_locs_extend in H13. eauto. eauto. 
    exists S'', M'', vy. intuition.
    rewrite vars_locs_extend.
    rewrite vars_locs_extend.
    eauto. eauto. eauto. 
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

Lemma valq_bool: forall M M' H b p q m,
    val_qual M M' H (vbool b) p q m.
Proof.
  intros. unfoldq. rewrite val_locs_bool. intuition.
Qed.

(* inlined 
Lemma valq_fresh: forall M M' H p q m,
    val_qual M H (vref (length (M' ++ M))) p q m.
Proof.
  intros. unfoldq.
  (* valq: index out of range*)
  rewrite app_length.
  rewrite val_locs_ref.
  intuition. unfoldq. lia.
Qed.
*)

Lemma valq_deref: forall S1 M M1 K E i p q m vx vt qt,
    store_type S1 (M1 ++ M) K ->
    ~ K i ->
    indexr i S1 = Some (Some vx) ->
    indexr i (M1 ++ M) = Some (vt, qt) ->
    val_qual M M1 E (vref i) (plift p) (plift q) (plift m) ->
    val_qual M M1 E vx (plift p) (plift q) (plift m).
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
    val_qual M M1 H (vabs H (qand p q) t) (plift p) (plift q) pempty.
Proof.
  intros. unfoldq.
  rewrite val_locs_abs.
  rewrite plift_and.
  intuition.
Qed.


Lemma valq_sub: forall M M1 H v p q q' m m',
    val_qual M M1 H v p q m ->
    psub q q' ->
    psub m m' ->
    psub q' (pdom H) ->
    psub m' (pdom H) ->
    val_qual M M1 H v p q' m'.
Proof.
  intros. unfoldq. intuition.  
  destruct (H0 x) as [H_q | [H_m | H_fresh]]. intuition.
  (* q *) left. destruct H_q. exists x0. intuition.
  (* m *) right. left. destruct H_m. exists x0. intuition.
  (* fresh *) right. right. intuition.
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

Lemma aux1: forall M H v l,
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


Lemma var_locs_shrink: forall M H v x l,
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


Lemma separation: forall M M' M'' H G TF TX p vf vx qf q1 mf m1
    (WFE: env_type M H G p)
    (HVF: val_type (M'++M) H vf TF)
    (HVX: val_type (M''++M'++M) H vx TX)
    (HQF: val_qual M M' H vf p qf mf)
    (HQX: val_qual (M'++M) M'' H vx p q1 m1),
    psub (val_locs (M'++M) vf) (pdom (M'++M)) ->
    psub (pand qf q1) pempty ->
    psub (pand mf m1) pempty ->
    psub (pand qf m1) pempty -> (* extra! *)
    psub (pand mf q1) pempty -> (* extra! *)
    psub (pand (val_locs (M'++M) vf) (val_locs (M''++M'++M) vx)) pempty.
Proof. 
  intros. unfoldq. intuition.
  remember WFE as WFE1. clear HeqWFE1.
  assert (env_type (M''++M'++M) H G p) as WFE2.
  rewrite app_assoc. eapply envt_store_extend. eauto.
  destruct WFE2 as [? [? [? SEP]]].
  eapply valt_wf in HVF as VF. specialize (VF _ H6).
  destruct (HQF x) as [HF_q | [HF_m | HF_fresh]];
  destruct (HQX x) as [HX_q | [HX_m | HX_fresh]]; eauto.
  - (* qf/q1 *)
    destruct HF_q. destruct HX_q. 
    assert (x0 = x1). {
      eapply SEP; intuition; eauto.
      rewrite <-var_locs_store_extend. eauto. eapply aux2.
      eapply envt_store_extend. eauto. eauto.
    }
    subst x1. intuition; eauto.
  - (* qf/m1 *)
    destruct HF_q. destruct HX_m. 
    assert (x0 = x1). {
      eapply SEP; intuition; eauto.
      rewrite <-var_locs_store_extend. eauto. eapply aux2.
      eapply envt_store_extend. eauto. eauto.
    }
    subst x1. intuition; eauto.
  - (* mf/q1 *)
    destruct HF_m. destruct HX_q. 
    assert (x0 = x1). {
      eapply SEP; intuition; eauto.
      rewrite <-var_locs_store_extend. eauto. eapply aux2.
      eapply envt_store_extend. eauto. eauto.
    }
    subst x1. intuition; eauto.
  - (* mf/m1 *)
    destruct HF_m. destruct HX_m. 
    assert (x0 = x1). {
      eapply SEP; intuition; eauto.
      rewrite <-var_locs_store_extend. eauto. eapply aux2.
      eapply envt_store_extend. eauto. eauto.
    }
    subst x1. intuition; eauto.
  - (* fresh/q1 *)
    destruct HX_q as [? [Hp Hq]].
    rewrite app_assoc in Hq.
    assert (psub (var_locs M H x0) (pdom M)) as HS. eapply aux2; eauto. eapply Hp.
    eapply HF_fresh. eapply HS. rewrite <-var_locs_store_extend in Hq; eauto.
  - (* fresh/m *)
    destruct HX_m as [? [Hp Hm]].
    rewrite app_assoc in Hm.
    assert (psub (var_locs M H x0) (pdom M)) as HS. eapply aux2; eauto. eapply Hp.
    eapply HF_fresh. eapply HS. rewrite <-var_locs_store_extend in Hm; eauto.
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
    store_type S M (por K (por (vars_locs M H q) (por (pdiff (vars_locs M H q) (val_locs M v)) (pdiff (pdiff (pdom M) (pdom M)) (val_locs M v))))).
Proof.
  intros.
  eapply storet_restrict. eauto.
  unfoldq. intuition.
  unfoldq. intuition. destruct H1. destruct H3. eapply H3. eauto.
  destruct H3. destruct H3. 
  eapply envt_var_store_wf; eauto.
  destruct H3.
  eapply envt_var_store_wf; eauto. eapply H3. 
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





(* ---------- main lemmas ---------- *)

Lemma sem_app1: forall S'' M M' M'' K'' H Hf G T1 T2 ey vx pv p q1 q2 qf m1 mf e2 k2 m2 q2x e2x k2x m2x
    (WFE: env_type M H G p)
    (HVF: val_type (M'++M) H (vabs Hf pv ey) (TFun T1 T2 q2 e2 k2 m2 q2x e2x k2x m2x))
    (HQF: val_qual M M' H (vabs Hf pv ey) p qf mf)
    (HVX: val_type (M''++M'++M) H vx T1)
    (HQX: val_qual (M'++M) M'' H vx p q1 m1),
    psub (pand qf q1) pempty ->
    psub (pand mf m1) pempty ->
    psub (pand qf m1) pempty -> (* extra! *)
    psub (pand mf q1) pempty -> (* extra! *)
    psub (plift q2) p  -> 
    psub (plift m2) p  -> 
    (* exists vy, exp_type H ey vy T2 p q2. *) (* not exactly this!! *)
    psub (pand K''
            (por (vars_locs (M''++M'++M) H (plift e2))
               (if e2x then (val_locs (M''++M'++M) vx) else pempty))) pempty ->
    psub (pand K''
            (por (vars_locs (M''++M'++M) H (plift m2))
               (if m2x then (val_locs (M''++M'++M) vx) else pempty))) pempty ->
    store_type S'' (M''++M'++M) K'' ->
    exists S''' M''' vy,
      tevaln S'' (vx::Hf) ey S''' vy /\
        store_type S''' (M'''++M''++M'++M)
          (por K''
             (por (vars_locs (M''++M'++M) H (plift k2))
                (por (if k2x then (val_locs (M''++M'++M) vx) else pempty)
                   (por (pdiff (vars_locs (M''++M'++M) H (plift m2)) (val_locs (M'''++M''++M'++M) vy))
                      (por (if m2x then (pdiff (val_locs (M''++M'++M) vx) (val_locs (M'''++M''++M'++M)vy)) else pempty)  (* - vy?*)
                         (pdiff (pdiff (pdom (M'''++M''++M'++M)) (pdom (M''++M'++M))) (val_locs (M'''++M''++M'++M)vy))))))) /\ 
        val_type (M'''++M''++M'++M) H vy T2 /\
        val_qual M (M'''++M''++M')H vy p
          (por (plift q2) (if q2x then q1 else pempty))
          (por mf (por m1 (por (plift m2) (if m2x then q1 else pempty)))) /\
        psub
          (pand (pdom (M''++M'++M)) (val_locs (M'''++M''++M'++M) vy))
          (por (val_locs (M'++M) (vabs Hf pv ey))
             (por (if q2x then (val_locs (M''++M'++M) vx) else pempty)
                (if m2x then (val_locs (M''++M'++M) vx) else pempty))).
Proof.
  
  intros. remember HVF as HVF2. clear HeqHVF2.
  intros. apply valt_wf in HVF as WFQF. apply valt_wf in HVX as WFQX.
  destruct HVF; intuition.
  rename H17 into HVF.
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
  rename H19 into HQY.
  remember (vabs Hf pv ey) as vf.
  unfold val_qual in *.

  unfoldq. intuition.
  destruct (HQY x) as [HY_q2 | [HY_q2x | [HY_m2 | [HY_m2x | HY_fresh]]]]. repeat rewrite app_assoc in *. eauto. 
  + (* q2 part of function *)
    (* destruct (HQF x) as [HF_q | [HF_m | HF_fresh]]. intuition. *)
    destruct HY_q2 as [[? ?] ?]. 
    left. exists x0. intuition.
    assert (psub (var_locs M H x0) (pdom M)). eapply aux2; eauto.
    rewrite app_assoc in H22.
    rewrite <-var_locs_store_extend in H22.
    rewrite <-var_locs_store_extend. eauto. eauto. eauto. 
    
  + (* q2x part of argument *) (* NOTE: this may also come from m1 !! *)
    destruct q2x; try contradiction.

    destruct (HQX x) as [HX_q | [HX_m | HX_fresh]]. eauto.
    (* q1 *)
    destruct HX_q. 
    left. exists x0. intuition.
    assert (psub (var_locs M H x0) (pdom M)). eapply aux2; eauto.
    rewrite app_assoc in H21.
    rewrite <-var_locs_store_extend in H21.
    rewrite <-var_locs_store_extend. eauto. eauto. eauto.
    (* m1 *)
    destruct HX_m. 
    right. left. exists x0. intuition.
    assert (psub (var_locs M H x0) (pdom M)). eapply aux2; eauto.
    rewrite app_assoc in H21.
    rewrite <-var_locs_store_extend in H21.
    rewrite <-var_locs_store_extend. eauto. eauto. eauto.
    (* fresh *)
    right. right. rewrite app_length in HX_fresh. lia.
    
  + (* m2 part of function *)
    (* destruct (HQF x) as [HF_q | [HF_m | HF_fresh]]. intuition. *)
    destruct HY_m2 as [[? ?] ?]. 
    right. left. exists x0. intuition.
    assert (psub (var_locs M H x0) (pdom M)). eapply aux2; eauto.
    rewrite app_assoc in H22.
    rewrite <-var_locs_store_extend in H22.
    rewrite <-var_locs_store_extend. eauto. eauto. eauto. 

  + (* m2x part of argument *) (* NOTE: this may also come from q1 !! *)
    destruct m2x; try contradiction.

    destruct (HQX x) as [HX_q | [HX_m | HX_fresh]]. eauto.
    (* q1 *)
    destruct HX_q. 
    right. left. exists x0. intuition. 
    assert (psub (var_locs M H x0) (pdom M)). eapply aux2; eauto.
    rewrite app_assoc in H21.
    rewrite <-var_locs_store_extend in H21.
    rewrite <-var_locs_store_extend. eauto. eauto. eauto.
    (* m1 *)
    destruct HX_m. 
    right. left. exists x0. intuition.
    assert (psub (var_locs M H x0) (pdom M)). eapply aux2; eauto.
    rewrite app_assoc in H21.
    rewrite <-var_locs_store_extend in H21.
    rewrite <-var_locs_store_extend. eauto. eauto. eauto.
    (* fresh *)
    right. right. rewrite app_length in HX_fresh. lia.
    
  + (* fresh *)
    right. right. repeat rewrite app_length in HY_fresh. lia. 
  }

  unfoldq. intuition.

  destruct (H19 x) as [? | [? | [? | ?]]]. eauto.

  destruct H17. eauto. eauto.
  destruct H17. eauto. 
  destruct H17. eauto.
  contradiction.

Qed.


Lemma sem_abs1: forall S M M1 K H G T1 T2 t vx p q2 qf e2 k2 m2 (q2x e2x k2x m2x: bool)
    (WFE: env_type M H G (plift p))
    (HVX: val_type (M1 ++ M) H vx T1) (* arg from valt *)
    (SEP : psub (pand (val_locs (M1++M) (vabs H (qand p qf) t)) (val_locs (M1++M) vx)) pempty)
    (IHW : (* induction *)
        env_type (M1 ++ M) (vx :: H) (T1 :: G) (plift (qor (qand p qf) (qone (length H)))) ->
        exists (S'' : stor) (M'' : stty) (vy : vl),
          exp_type S (M1 ++ M) K (vx :: H) t S'' M'' vy T2 (plift (qor (qand p qf) (qone (length H))))
            (plift (qor q2 (if q2x then (qone (length H)) else qempty)))
            (plift (qor e2 (if e2x then (qone (length H)) else qempty)))
            (plift (qor k2 (if k2x then (qone (length H)) else qempty)))
            (plift (qor m2 (if m2x then (qone (length H)) else qempty))))
    (HCLT1: closed_ty (length H) T1)        
    (HCLT2: closed_ty (length H) T2)
    (HCLQ:  closed_ql (length H) (qand p qf))
    (HCLK:  closed_ql (length H) k2)
    (HCLQ2: closed_ql (length H) q2)
    (HCLM:  closed_ql (length H) m2)
    (STY:   store_type S (M1 ++M) K),
  exists (S'' : stor) (M'' : stty) (vy : vl),
    tevaln S (vx :: H) t S'' vy /\
      store_type S'' (M'' ++ M1 ++ M)
        (por K
           (por (vars_locs (M1++M) H (plift k2))
              (por (if k2x then (val_locs (M1++M) vx) else pempty)
                 (por (pdiff (vars_locs (M1++M) H (plift m2)) (val_locs (M''++M1++M) vy))
                    (por (if m2x then (pdiff (val_locs (M1++M) vx) (val_locs (M''++M1++M) vy)) else pempty) (* - vy?*)
                       (pdiff (pdiff (pdom (M''++M1++M)) (pdom (M1++M))) (val_locs (M''++M1++M) vy) )))))) /\  (* !!! TODO: add M''++M1 - locs vy !!! *)
      val_type (M'' ++ M1 ++ M) H vy T2 /\
      psub (val_locs (M''++M1++M) vy)
        (por (pand (vars_locs (M1++M) H (plift q2)) (val_locs M (vabs H (qand p qf) t)))
           (por (if q2x then (val_locs (M1++M) vx) else pempty)
              (por (pand (vars_locs (M1++M) H (plift m2)) (val_locs M (vabs H (qand p qf) t)))
                 (por (if m2x then (val_locs (M1++M) vx) else pempty)
                   (pnot (pdom (M1++M)) ))))).
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
  unfoldq. intros. repeat rewrite plift_or in H2. repeat rewrite plift_and in H2. repeat rewrite plift_one in H2. 
  destruct H2 as [H_K | [H_k | [[H_m ?] | H_fresh]]].

  (* K *) left. eauto.
  
  (* k *) destruct H_k. unfoldq.
  bdestruct (x0 =? length H).
  destruct k2x. subst x0.
  rewrite plift_one in H2. unfoldq. destruct H2. destruct H2. destruct H6. eapply HCLK in H6. lia.
  right. right.
  destruct H5. destruct H5. rewrite indexr_head in H5; eauto. inversion H5. subst x0.
  intuition.
  (* k2x = false *)
  subst x0. rewrite plift_empty in H2. destruct H2. destruct H2. destruct H6. eapply HCLK in H6. lia. unfoldq. contradiction.
  (* x0 <> length H *)
  destruct H2. destruct H2. destruct H2. 2: lia. destruct H7.
  right. left. exists x0. intuition. destruct H6. eexists x1. intuition. rewrite indexr_skip in H6. eauto. lia.
  destruct k2x. rewrite plift_one in H7. unfoldq. lia. rewrite plift_empty in H7. unfoldq. contradiction.

  (* m *) destruct H_m. unfoldq.
  bdestruct (x0 =? length H).
  destruct m2x. subst x0.
  rewrite plift_one in H5. unfoldq. destruct H5. destruct H5. destruct H7. eapply HCLM in H7. lia.
  right. right. right. 
  destruct H6. destruct H6. rewrite indexr_head in H6; eauto. inversion H6. subst x0.
  intuition.
  (* k2x = false *)
  subst x0. rewrite plift_empty in H5. destruct H5. destruct H5. destruct H7. eapply HCLM in H7. lia. unfoldq. contradiction.
  (* x0 <> length H *)
  destruct H5. destruct H5. destruct H5. 2: lia. destruct H8.
  right. right. right. left. intuition. exists x0. intuition. destruct H7. eexists x1. intuition. rewrite indexr_skip in H7. eauto. lia.
  destruct m2x. rewrite plift_one in H8. unfoldq. lia. rewrite plift_empty in H8. unfoldq. contradiction.
  
  (* fresh *)
  right. right. right. eauto. 

  
  unfoldq. intros. destruct H2 as [H_K | [H_k2 | [H_k2x | [H_m2 | [H_m2x | H_fresh]]]]].
  (* K *) destruct H1 as [? [KL ?]].
  eapply KL. eauto.
  (* k2 *) destruct H_k2. destruct H2.
  eapply app_length2. eapply envt_var_store_wf. eapply envt_store_extend. eauto. eapply H5. 
  (* k2x *) destruct k2x; try contradiction.
  eapply app_length2. eapply valt_wf. eauto. eauto.
  (* m2 *) destruct H_m2. destruct H2. destruct H2. 
  eapply app_length2. eapply envt_var_store_wf. eapply envt_store_extend. eauto. eapply H6.
  (* m2x *) destruct m2x; try contradiction.
  eapply app_length2. eapply valt_wf. eauto. eapply H_m2x.
  (* fresh *)
  eapply H_fresh.

  
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

  repeat rewrite plift_or in HVY.
  repeat rewrite plift_and in HVY.
  repeat rewrite plift_if in HVY.
  repeat rewrite plift_one, plift_empty in HVY.
  unfoldq. intros. repeat rewrite plift_and. 
  destruct (HVY x) as [H_q2 | [H_m2 | H_fresh]]. eapply H2.
  (* q2 *) {
    destruct H_q2 as [? [[QPF Q2X] ?]].
    destruct Q2X.
    - (* from func *)
      assert (x0 < length H). eapply HCLQ2. eauto. 
      destruct QPF; try lia. 
      eapply var_locs_shrink in H4; eauto.
      rewrite <-var_locs_store_extend in H4.
      2: { intros ? ?. eapply aux2. eapply envt_store_extend. eauto. eapply H7. eauto. }
      remember H4 as H8. clear HeqH8.
      rewrite <-var_locs_store_extend in H8.
      2: { intros ? ?. eapply aux2. eauto. eapply H7. eauto. }
      left. unfoldq. intuition.
      exists x0. intuition. exists x0. intuition.
    - (* from arg *)
      destruct q2x; try contradiction.
      destruct QPF. assert (x0 < length H). { eapply WFE. eapply H6. } lia.
      right. left.
      destruct H4 as [? [? ?]].
      subst x0. rewrite indexr_head in H4. inversion H4. subst x1.
      rewrite <-val_locs_extend in H7. eauto. intros ? ?. eapply HVX. eauto.
  }
  (* m2 *) {
    destruct H_m2 as [? [[QPF Q2X] ?]].
    destruct Q2X.
    - (* from func *)
      assert (x0 < length H). eapply HCLM. eauto. 
      destruct QPF; try lia. 
      eapply var_locs_shrink in H4; eauto.
      rewrite <-var_locs_store_extend in H4.
      2: { intros ? ?. eapply aux2. eapply envt_store_extend. eauto. eapply H7. eauto. }
      remember H4 as H8. clear HeqH8.
      rewrite <-var_locs_store_extend in H8.
      2: { intros ? ?. eapply aux2. eauto. eapply H7. eauto. }
      right. right. left. unfoldq. intuition.
      exists x0. intuition. exists x0. intuition.
    - (* from arg *)
      destruct m2x; try contradiction.
      destruct QPF. assert (x0 < length H). { eapply WFE. eapply H6. } lia.
      right. right. right. 
      destruct H4 as [? [? ?]].
      subst x0. rewrite indexr_head in H4. inversion H4. subst x1.
      rewrite <-val_locs_extend in H7. eauto. intros ? ?. eapply HVX. eauto.
  }
  (* fresh *)
  lia. 
Qed.



(* ------ aux ------ *)

Lemma var_locs_se: forall M M1 H G x p,
    env_type M H G p ->
    p x -> 
    var_locs M H x = var_locs (M1++M) H x.
Proof.
  intros. eapply var_locs_store_extend.
  eapply aux2. eauto. eauto. 
Qed.

Lemma var_locs_se1: forall M H G x p vt qt,
    env_type M H G p ->
    p x -> 
    var_locs M H x = var_locs ((vt,qt)::M) H x.
Proof.
  intros. rewrite var_locs_store_extend with (M' := [(vt,qt)]).
  intuition.
  eapply aux2. eauto. eauto. 
Qed.

Lemma vars_locs_se: forall M M1 H G p q,
    env_type M H G p ->
    psub q p -> 
    vars_locs M H q = vars_locs (M1++M) H q.
Proof.
  intros. eapply functional_extensionality.
  intros. eapply propositional_extensionality.
  unfoldq. intuition.
  destruct H2 as [? [? ?]]. exists x0. rewrite <-var_locs_se with (G:=G) (p:=p); eauto.
    destruct H2 as [? [? ?]]. exists x0. rewrite <-var_locs_se with (G:=G) (p:=p) in H3; eauto. 
Qed.

Lemma vars_locs_se1: forall M H G p q vt qt,
    env_type M H G p ->
    psub q p -> 
    vars_locs M H q = vars_locs ((vt,qt)::M) H q.
Proof.
  intros. eapply functional_extensionality.
  intros. eapply propositional_extensionality.
  unfoldq. intuition.
  destruct H2 as [? [? ?]]. exists x0. rewrite <-var_locs_se1 with (G:=G) (p:=p); eauto.
    destruct H2 as [? [? ?]]. exists x0. rewrite <-var_locs_se1 with (G:=G) (p:=p) in H3; eauto. 
Qed.








(* if well-typed, then result is an actual value (not stuck and not a timeout),
   for large enough n *)

Theorem full_total_safety : forall t G T p q e k m,
    has_type G t T p q e k m ->
    forall M E, env_type M E G (plift p) ->
    forall S K, store_type S M K ->
    psub (pand K (vars_locs M E (pand (plift p) (plift e)))) pempty ->
    psub (pand K (vars_locs M E (pand (plift p) (plift m)))) pempty ->
    exists S' M' v, exp_type S M K E t S' M' v T (plift p) (plift q) (plift e) (plift k) (plift m).
Proof.
  intros ? ? ? ? ? ? ? ? W. 
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
    unfoldq. rewrite plift_one, plift_empty.
    unfoldq. intuition.
    left. 
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
          destruct H2 as [HX_K | [HX_k | [HX_m | HX_fresh]]].
          (* K *) left. intuition.
          (* k *) right. left. intuition.
          (* m *) right. right. left. 
          assert (x < length M). {
            destruct HX_m. eapply env_type_store_wf in H2.
            2: eapply WFE. unfoldq. eauto.
          }
          intuition. rewrite app_length in H6. lia.
          destruct H6 as [vt1 [qt1 [? ?]]].
          rewrite indexr_head in H5. congruence.
          (* fresh *)
          right. right. right.
          intuition.
          simpl. rewrite app_length in *. lia.
          destruct H6 as [vt1 [qt1 [? ?]]].
          rewrite indexr_head in H2. congruence.
        }
        (* K' <: dom(M1++M) *) {
          rewrite val_locs_ref. unfoldq. intros. 
          destruct H2 as [HX_K | [HX_k | [HX_m | HX_fresh]]].
          (* K *) destruct ST1 as [? [KS ?]]. eapply KS. left. eapply HX_K.
          (* k *) eapply app_length2. destruct HX_k as [? [[? ?] ?]].
          eapply env_type_store_wf; eauto. exists x0. split. eapply H2. eauto.
          (* m *) eapply app_length2. destruct HX_m as [[? [[? ?] ?]] ?].     
          eapply env_type_store_wf; eauto. exists x0. split. eapply H2. eauto.          (* fresh *) intuition. simpl in H4. lia.
        }

        subst. eauto.
        subst. eapply valt_wf. eauto.
        subst. unfoldq. intuition.
      }

      (* val_type *)
      simpl. intuition. eapply valt_closed. eauto.
      bdestruct (length (M1 ++ M) =? length (M1 ++ M)); intuition.
      exists vt, qt. subst. intuition.
      rewrite app_cons. apply valt_store_extend. eauto. 
      unfoldq. intuition. rewrite app_cons. eapply app_length2. eapply valt_wf; eauto.

      (* val_qual -- was: valq_fresh*)
      unfoldq. intuition.
      rewrite val_locs_ref in H2. destruct H2.
      (* fresh loc itself *) right. right. unfoldq. rewrite app_length in H2. lia.
      (* indirection *)
      assert (psub (val_locs (M1 ++ M) vx) (pdom (M1++M))). {
        eapply valt_wf; eauto.
      }
      assert (val_locs (M1 ++ M) vx x). {
        unfold loc_locs in H2. destruct H2 as [vt1 [qt1 [IX ?]]].
        remember ((((vt, qt) :: M1)++M)) as Q. 
        simpl in HeqQ. subst Q. rewrite indexr_head in IX. inversion IX. subst.
        eauto.
      }
      
      destruct (HQX x) as [H_q | [H_m | H_fresh]]. eauto.
      (* q *) left. destruct H_q. exists x0. intuition.
      simpl. rewrite <-var_locs_se1 with (G:=env) (p:=plift p); eauto.
      eapply envt_store_extend; eauto.
      (* m *) right. left. destruct H_m. exists x0. intuition.
      simpl. rewrite <-var_locs_se1 with (G:=env) (p:=plift p); eauto.
      eapply envt_store_extend; eauto.
      (* fresh *)
      right. right. eauto. 
      
  - (* Case "Get". *)
    rename H  into SEP_kq.
    rename H0 into SEP_mq.
    rename H1 into SEP_km.

    rename H3 into SEP_Keq.
    rename H4 into SEP_Km.
    
    rename H2 into ST.
    
    rewrite plift_or, pand_dist_or, vars_locs_dist_or, pand_dist_or, psub_dist_or in SEP_Keq.
    destruct SEP_Keq as [SEP_Ke SEP_Kq].
    
    destruct (IHW M E WFE S K) as [S1 [M1 [vx [IW1 [ST1 [HVX HQX]]]]]]; eauto.
    
    destruct vx; try solve [inversion HVX]. simpl in HVX.
    destruct (HVX) as [CL [vt [qt [MI [HVX1 HQX1]]]]].

    (* three cases to consider as per HQX for (vref i):

       1. old, covered by q
       2. moved, covered by m
       3. new, not covered by anything

       need to show that store lookup succeeds in each case

       1. q <> K (from premise), q <> k (from typing), q <> m (from typing)
       2. m <> K (from premise), m <> k (from typing), m == m --> so need to exclude locs(v) !!!
       3. m <> K,k,m because new --> locs(v) excluded       

     *)

    remember (vars_locs_se M M1 E env (plift p)) as VE.
    remember (fun x => var_locs_se M M1 E env x (plift p) WFE) as VE1.
    
    rewrite VE in SEP_Ke; eauto. 2: { unfoldq. intuition. }
    rewrite VE in SEP_Kq; eauto. 2: { unfoldq. intuition. }
    rewrite VE in SEP_Km; eauto. 2: { unfoldq. intuition. }
    
    assert (~ por K
              (por (vars_locs M E (pand (plift p) (plift k)))
                 (por (pdiff (vars_locs M E (pand (plift p) (plift m))) (val_locs (M1++M) (vref i)))
                    (pdiff (pdiff (pdom (M1 ++ M)) (pdom M)) (val_locs (M1++M) (vref i)))))
      i) as NK. { 
      intros IO. rewrite val_locs_ref in IO.
      destruct (HQX i) as [HQ_old | [HQ_moved | HQ_fresh]].
      rewrite val_locs_ref. left. intuition.

      (* - old *)
      destruct IO as [IO_K | [IO_k | [IO_m | IO_fresh]]].
      (* K *) eapply SEP_Kq. split. eapply IO_K. eapply HQ_old. 
      (* k *) destruct IO_k as [? IO]. destruct HQ_old as [? HQ].
      assert (x = x0). { eapply WFE. eapply IO. eapply IO. eapply HQ.
                         rewrite VE1. eapply HQ. eapply HQ. }
      subst x0. eapply SEP_kq. unfoldq. intuition; eauto.
      (* m *) destruct IO_m as [? IO]. unfoldq. eauto. 
      (* fresh *) destruct IO_fresh as [? IO]. unfoldq. eauto. 

      (* - moved *)
      destruct IO as [IO_K | [IO_k | [IO_m | IO_fresh]]].
      (* K *) eapply SEP_Km. unfoldq. intuition; eauto. 
      (* k *) destruct IO_k as [? IO]. destruct HQ_moved as [? HQ]. 
      assert (x = x0). { eapply WFE. eapply IO. eapply IO. eapply HQ.
                         rewrite VE1. eapply HQ. eapply HQ. }
      subst x0. eapply SEP_km. unfoldq. intuition; eauto.
      (* m *) destruct IO_m as [? IO]. unfoldq. eauto.
      (* fresh *) destruct IO_fresh as [? IO]. unfoldq. eauto. 

      (* - fresh *)
      destruct IO as [IO_K | [IO_k | [IO_m | IO_fresh]]].
      (* K *) eapply HQ_fresh. destruct ST as [? [ST ?]]. eapply ST. eauto.
      (* k *) eapply env_type_store_wf in IO_k; eauto. 
      (* m *) unfoldq. lia. 
      (* fresh *) unfoldq. lia. 
    }

    remember ST1 as ST1x. clear HeqST1x.
    destruct ST1 as [LST [KS1 ST1]].
    destruct (ST1 i vt qt) as [? [? | [vy [SI [VT QT]]]]]. eauto. contradiction.

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

      (* K <: K' *) {
        rewrite val_locs_ref.
        intros ? [XX_K | [XX_k | [XX_m | XX_fresh]]].
        (* K *) left. eauto.
        (* k *) right. left. eauto.
        (* m *) right. right. left.
        destruct XX_m. unfoldq. split. eapply H0.
        intros ?. destruct H1. right. unfold loc_locs.
        exists vt, qt. intuition.
        (* fresh *) right. right. right.
        destruct XX_fresh. unfoldq. split. split. eapply H0. eapply H0.
        intros ?. destruct H1. right. unfold loc_locs.
        exists vt, qt. intuition.
      }
      (* K < dom(M1++M) *) {
        intros ? [XX_K | [XX_k | [XX_m | XX_fresh]]].
        (* K *) eapply KS1. left. eapply XX_K.
        (* k *) eapply app_length2. eapply env_type_store_wf. eauto. eapply XX_k.
        (* m *) eapply app_length2. eapply env_type_store_wf. eauto. eapply XX_m.
        (* fresh *) unfoldq. lia.
      }
      
      (* val_type *)
      eauto.

      (* val_qual *)
      unfoldq. intros. eapply (HQX x). rewrite val_locs_ref.
      unfoldq. right. unfold loc_locs. exists vt, qt. intuition. 

      
  - (* Case "Free". *)
    destruct (IHW M E WFE S K) as [S1 [M1 [vx [IW1 [SW1 [HVX HQX]]]]]]; eauto.

    remember (fun q => vars_locs_se M M1 E env (plift p) q WFE) as VE.
    remember (fun x => var_locs_se M M1 E env x (plift p) WFE) as VE1.
    
    destruct vx; try solve [inversion HVX]. simpl in HVX.
    destruct (HVX) as [CL [vy [qy [SI HVX1]]]].
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

    (* three case to consider as per HQX for (vref i):

       1. old, covered by q
       2. moved, covered by m
       3. new, not covered by anything

       need to show that it can be counted as killed in result store typing:

       1. ok, k or q allowed
       2. ok, m allowed (and not escaping!)
       3. ok, new locs allowed (and not escaping!)

     *)
    
      (* given *)
      assert (store_type S1 (M1 ++ M)
                (por K
                   (por (vars_locs M E (pand (plift p) (plift k)))
                      (por (pdiff (vars_locs M E (pand (plift p) (plift m))) (val_locs (M1++M) (vref i)))
                         (pdiff (pdiff (pdom (M1 ++ M)) (pdom M))
                            (val_locs (M1++M) (vref i))))))). { eauto. }

      (* prove *)
      assert (store_type S1 (M1 ++ M)
                (por K
                   (por (vars_locs M E (pand (plift p) (plift (qor k q))))
                      (por (pdiff (vars_locs M E (pand (plift p) (plift m))) (val_locs (M1++M) (vbool false)))
                         (pdiff (pdiff (pdom (M1 ++ M)) (pdom M)) (val_locs (M1++M) (vbool false))))))). { 

        eapply storet_restrict. eauto.
        
        rewrite plift_or, val_locs_ref, val_locs_bool.
        intros ? XX. unfoldq. destruct XX as [XX_K | [XX_k | [XX_m | XX_fresh]]].
        (* K *) left. eauto.
        (* k *) right. left. destruct XX_k. exists x0. intuition.
        (* m *) right. right. left. destruct XX_m. intuition.
        (* fresh *) right. right. right. intuition.

        rewrite plift_or, val_locs_bool.
        intros ? XX. unfoldq. destruct XX as [XX_K | [XX_k | [XX_m | XX_fresh]]].
        (* K *) destruct SW1 as [? [SW1 ?]]. eapply SW1. eauto.
        (* k *) eapply env_type_store_wf in XX_k. 2: eapply WFE. unfoldq. rewrite app_length. lia.
        (* m *) destruct XX_m as [XX_m ?]. eapply env_type_store_wf in XX_m. 2: eapply WFE. unfoldq. rewrite app_length. lia.
        (* fresh *) intuition.
      }
      
      eapply storet_free. eauto. {
        rewrite plift_or, val_locs_bool. 
        destruct (HQX i) as [HQ_old | [HQ_moved | HQ_fresh]].
        rewrite val_locs_ref. intuition.
        left. unfoldq. intuition.
          
        (* - old *)
        right. left.
        rewrite <-VE in HQ_old. destruct HQ_old.
        exists x. unfoldq. intuition. unfoldq. intuition.
        (* - moved *)
        right. right. left.
        rewrite <-VE in HQ_moved. unfoldq. intuition. unfoldq. intuition.
        (* - fresh *)
        right. right. right. unfoldq. intuition.
        eapply indexr_extend; eauto. 
      }

      split. simpl. eauto.
      eapply valq_bool.

  - (* Case "Move". *)
    rewrite plift_or, pand_dist_or, vars_locs_dist_or, pand_dist_or, psub_dist_or in H3.
    destruct H3 as [HFF HFF'].

    destruct (IHW M E WFE S K) as [S1 [M1 [vx [IW1 [SW1 [HVX HQX]]]]]]; eauto. 

    remember (fun q => vars_locs_se M M1 E env (plift p) q WFE) as VE.
    remember (fun x => var_locs_se M M1 E env x (plift p) WFE) as VE1.

    destruct vx; try solve [inversion HVX]. simpl in HVX.        
    destruct (HVX) as [CL [vy [qy [SI [HVX1 HQXI]]]]].

    exists S1. exists M1. exists (vref i). split.
    + (* expression evaluates *)
      destruct IW1 as [n1 IW1].
      rename S into Sx.
      exists (S n1).
      intros. destruct n. lia.
      simpl. rewrite IW1. eauto. lia.
    + (* result well typed *)
      split. 2: split.

      (* given *)
      assert (store_type S1 (M1 ++ M)
                (por K
                   (por (vars_locs M E (pand (plift p) (plift k)))
                      (por (pdiff (vars_locs M E (pand (plift p) (plift m))) (val_locs (M1++M) (vref i)))
                         (pdiff (pdiff (pdom (M1 ++ M)) (pdom M))
                            (val_locs (M1++M) (vref i))))))). { eauto. }

      (* prove *)
      assert (store_type S1 (M1 ++ M)
                (por K
                   (por (vars_locs M E (pand (plift p) (plift k)))
                      (por (pdiff (vars_locs M E (pand (plift p) (plift (qor m q)))) (val_locs (M1++M) (vref i)))

                         (pdiff (pdiff (pdom (M1 ++ M)) (pdom M))
                            (val_locs (M1++M) (vref i))))))). {

        eapply storet_restrict. eauto.
        
        rewrite plift_or, val_locs_ref.
        intros ? XX. unfoldq. destruct XX as [XX_K | [XX_k | [XX_m | XX_fresh]]].
        (* K *) left. eauto.
        (* k *) right. left. destruct XX_k. exists x0. intuition.
        (* m *) right. right. left. destruct XX_m as [[? XX_m] ?]. split. exists x0. intuition. eauto. 
        (* fresh *) right. right. right. intuition.

        rewrite plift_or.
        intros ? XX. unfoldq. destruct XX as [XX_K | [XX_k | [XX_m | XX_fresh]]].
        (* K *) destruct SW1 as [? [SW1 ?]]. eapply SW1. eauto.
        (* k *) eapply env_type_store_wf in XX_k. 2: eapply WFE. unfoldq. rewrite app_length. lia.
        (* m *) destruct XX_m as [XX_m ?]. eapply env_type_store_wf in XX_m. 2: eapply WFE. unfoldq. rewrite app_length. lia.
        (* fresh *) intuition.
      }
      eauto. 

      (* val_type *)
      simpl. intuition.

      (* val_qual *)
      intros ? ?.       
      destruct (HQX x) as [HQ_old | [HQ_move | HQ_fresh]]. eauto.

      (* - old *)
      right. left. destruct HQ_old. exists x0. rewrite plift_or. unfoldq. intuition.
      (* - move *)
      right. left. destruct HQ_move. exists x0. rewrite plift_or. unfoldq. intuition.
      (* - fresh *)
      right. right. eauto. 
      
      
  - (* Case "App". *)
    rename H  into SEP_QFQ1.
    
    rename H0 into SEP_QFM1.
    rename H1 into SEP_MFQ1.
    
    rename H2 into SEP_KFE1.
    rename H3 into SEP_KFM1.
    rename H4 into SEP_MFE1.
    rename H5 into SEP_MFK1.
    rename H6 into SEP_MFM1.

    rename H7  into SEP_K1M1.
    
    rename H8  into SEP_KF1E2.
    rename H9  into SEP_KF1M2.
    rename H10  into SEP_MF1E2.
    rename H11 into SEP_MF1K2.
    rename H12 into SEP_MF1M2.

    repeat rewrite pand_dist_or  in SEP_KF1E2, SEP_KF1M2, SEP_MF1E2, SEP_MF1K2, SEP_MF1M2.
    repeat rewrite pand_dist_or1 in SEP_KF1E2, SEP_KF1M2, SEP_MF1E2, SEP_MF1K2, SEP_MF1M2.
    repeat rewrite psub_dist_or  in SEP_KF1E2, SEP_KF1M2, SEP_MF1E2, SEP_MF1K2, SEP_MF1M2.
    destruct SEP_KF1E2 as [[SEP_KFE2 SEP_K1E2] [SEP_KFE2x SEP_K1E2x]].
    destruct SEP_KF1M2 as [[SEP_KFM2 SEP_K1M2] [SEP_KFM2x SEP_K1M2x]].
    destruct SEP_MF1E2 as [[SEP_MFE2 SEP_M1E2] [SEP_MFE2x SEP_M1E2x]].
    destruct SEP_MF1K2 as [[SEP_MFK2 SEP_M1K2] [SEP_MFK2x SEP_M1K2x]].
    destruct SEP_MF1M2 as [[SEP_MFM2 SEP_M1M2] [SEP_MFM2x SEP_M1M2x]].
    
    rename H13 into Q2_WF.
    rename H14 into E2_WF.
    rename H15 into K2_WF.
    rename H16 into M2_WF.
    
    rename H17 into SEP_K2XQ2X.
    rename H18 into SEP_K2XM2X.

    rename H19 into ST.
    rename H20 into KSEPE.
    rename H21 into KSEPM.

    repeat rewrite plift_or in KSEPE,KSEPM. repeat rewrite pand_dist_or in KSEPE,KSEPM. repeat rewrite vars_locs_dist_or in KSEPE,KSEPM.
    repeat rewrite plift_if in KSEPE,KSEPM. repeat rewrite por_assoc in KSEPE,KSEPM.
    repeat rewrite plift_empty in KSEPE,KSEPM.


    (* helper lemmas *)
    assert (forall a b,
        psub (pand a b) pempty -> forall x,
        vars_locs M E (pand (plift p) a) x ->
        vars_locs M E (pand (plift p) b) x -> False) as vars_locs_sep.
    {
      intros. unfoldq. destruct H0. destruct H1.
      assert (x0 = x1). { eapply WFE. eapply H0. eapply H0. eapply H1. eapply H1. }
      subst x1. destruct (H x0). split. eapply H0. eapply H1. 
    }

    assert (forall a b,
        psub (pand (plift a) (plift b)) pempty -> 
        psub (pand (vars_locs M E (pand (plift p) (plift a))) 
          (vars_locs M E (pand (plift p) (plift b)))) pempty) as vars_locs_sep1.
    {
      intros. unfoldq. intros. eapply vars_locs_sep. eapply H. eapply H0. eapply H0. 
    }
    
    assert (forall a x M,
               vars_locs M E (pand (plift p) (plift a)) x -> forall (M1: stty),
                 env_type M E env (plift p) ->
        ~ (x < length M) -> False) as vars_locs_not_fresh.
    {
      intros. eapply H1. eapply env_type_store_wf. eauto. eapply H. 
    }
    assert (forall a x M,
               vars_locs M E (pand (plift p) (plift a)) x -> forall (M1 M2: stty),
                 env_type M E env (plift p) ->
        x < length (M2++M1++M) /\ ~ (x < length (M1++M)) -> False) as vars_locs_not_fresh2.
    {
      intros. eapply H1. eapply app_length2. eapply env_type_store_wf. eauto.
      eapply H. 
    }
    (* eapply vars_locs_sep1 in SEP_KFE1; eauto. *)

    assert (forall a, psub a (plift p) ->
       psub (vars_locs M E a)
         (vars_locs M E (pand (plift p) a))) as vars_locs_up.
    {
      intros. unfoldq. intros. destruct H0. exists x0. intuition.
    }

    
    (* end helper lemmas *)
    


    (* ---- 1st induction: vf ---- *)
    
    (* induction on both subexpressions: obtain vf, vx *)
    destruct (IHW1 M E WFE S K) as [S1 [M1 [vf [IW1 [ST1 [HVF HQF]]]]]]. eauto.

    (* K sep ef *) {
      unfoldq. intuition. eapply (KSEPE x). split. eauto. eauto. 
    }
    (* K sep mf *) {
      unfoldq. intuition. eapply (KSEPM x). split. eauto. eauto. 
    }



    (* ---- 2nd induction: vx ---- *)
    
    assert (env_type (M1++M) E env (plift p)) as WFE1. { eapply envt_store_extend. eauto. }
    
    remember (por K
                (por (vars_locs M E (pand (plift p) (plift kf)))
                   (por (pdiff (vars_locs M E (pand (plift p) (plift mf))) (val_locs (M1++M) vf))
                      (pdiff (pdiff (pdom (M1 ++ M)) (pdom M)) (val_locs (M1++M) vf))))) as K1.
    
    destruct (IHW2 (M1++M) E WFE1 S1 K1) as [S2 [M2 [vx [IW2 [ST2 [HVX HQX]]]]]]. eauto.


    (* K1 sep e1 *) {
      rewrite <-vars_locs_se with (G:=env) (p:=plift p).
      2: eauto. 2: { unfoldq. intuition. }

      subst K1. intros ? [? HY_e]. eapply (KSEPE x). unfoldq.
      destruct H as [HX_K | [HX_k | [[HX_m ?] | [[? HX_fresh] ?]]]].
      (* K *) eauto. 
      (* k *) destruct (vars_locs_sep _ _ SEP_KFE1 x); eauto.
      (* m *) destruct (vars_locs_sep _ _ SEP_MFE1 x); eauto.
      (* fresh *) destruct (vars_locs_not_fresh _ _ M HY_e M1); eauto. 
    }

    (* K1 sep m1 *) {
      rewrite <-vars_locs_se with (G:=env) (p:=plift p).
      2: eauto. 2: { unfoldq. intuition. }

      subst K1. intros ? [? HY_m]. eapply (KSEPM x). unfoldq.
      destruct H as [HX_K | [HX_k | [[HX_m ?] | [[? HX_fresh] ?]]]].
      (* K *) eauto.
      (* k *) destruct (vars_locs_sep _ _ SEP_KFM1 x); eauto.
      (* m *) destruct (vars_locs_sep _ _ SEP_MFM1 x); eauto.
      (* fresh *) destruct (vars_locs_not_fresh _ _ M HY_m M1); eauto.
    }

    (* uniformly take smallest store for things bound by qualifiers *)
    assert (forall q,
               vars_locs (M2 ++ M1 ++ M) E (pand (plift p) q) =
                 vars_locs M E (pand (plift p) q)) as VQ2. {
      intros. rewrite app_assoc. 
      rewrite <-vars_locs_se with (G:=env) (M1:=M2++M1) (p:=plift p).
      eauto. eauto. unfoldq. intuition.
    }
    assert (forall q,
               vars_locs (M1 ++ M) E (pand (plift p) q) =
                 vars_locs M E (pand (plift p) q)) as VQ1. {
      intros. 
      rewrite <-vars_locs_se with (G:=env) (M1:=M1) (p:=plift p).
      eauto. eauto. unfoldq. intuition.
    }

    (* ---- invert function value ---- *)

    (* vf is a function value: it can eval its body *)
    destruct vf; try solve [inversion HVF].
    remember (por K1
                (por (vars_locs (M1++M) E (pand (plift p) (plift k1)))
                   (por (pdiff (vars_locs (M1++M) E (pand (plift p) (plift m1))) (val_locs (M2++M1++M) vx))
                      (pdiff (pdiff (pdom (M2 ++ M1 ++ M)) (pdom (M1 ++ M)))
                         (val_locs (M2++M1++M) vx))))) as K2.

    assert (exists S3 M3 vy,
               tevaln S2 (vx::l) t0 S3 vy /\
                 store_type S3 (M3++M2++M1++M)
                   (por K2
                      (por (vars_locs (M2++M1++M) E (plift k2))
                         (por (if k2x then (val_locs (M2++M1++M) vx) else pempty)
                            (por (pdiff (vars_locs (M2++M1++M) E (plift m2)) (val_locs (M3++M2++M1++M) vy))
                               (por (if m2x then (pdiff (val_locs (M2++M1++M) vx) (val_locs (M3++M2++M1++M) vy)) else pempty)  (* - vy?*)
                                  (pdiff (pdiff (pdom (M3++M2++M1++M)) (pdom (M2++M1++M))) (val_locs (M3++M2++M1++M) vy))))))) /\
                 val_type (M3++M2++M1++M) E vy T2 /\
                 val_qual M (M3++M2++M1) E vy (plift p)
                   (por (plift q2) (if q2x then (plift q1) else pempty))
                   (por (plift mf) (por (plift m1) (por (plift m2) (if m2x then (plift q1) else pempty)))) /\
                 psub
                   (pand (pdom (M2++M1++M)) (val_locs (M3++M2++M1++M) vy))
                   (por (val_locs (M1++M) (vabs l q t0))
                      (por (if q2x then (val_locs (M2++M1++M) vx) else pempty)
                         (if m2x then (val_locs (M2++M1++M) vx) else pempty)))
           ) as HVY. {
      apply valt_wf in HVX as HVX'.
      eapply sem_app1; eauto.

      (* K2 sep e2/e2x *) {

        replace (plift e2) with (pand (plift p) (plift e2)).
        2: { intros. eapply functional_extensionality. intros. eapply propositional_extensionality. unfoldq. intuition. }
        unfold val_qual in HQF, HQX. 
        repeat rewrite VQ1 in *.
        repeat rewrite VQ2 in *.
        
        subst K2 K1. (* effect sep: K2 & e2 = empty <- e2 not killed *)
        repeat rewrite por_assoc.
        intros ? [HK2 He2]. 

        destruct He2.
        (* -- e2 -- *)
        
        destruct HK2 as [H_K | [H_kf | [[H_mf ?] | [H_freshf | [H_k1 | [H_m1 | H_fresh1]]]]]].

        (* K  *) eapply KSEPE. split. eauto. right. right. left. eauto. 
        (* kf *) eapply vars_locs_sep. eapply SEP_KFE2. eapply H_kf. eauto. 
        (* mf *) eapply vars_locs_sep. eapply SEP_MFE2. eapply H_mf. eauto. 
        (* fresh f *) eapply vars_locs_not_fresh. eauto. eauto. eauto. unfoldq. eapply H_freshf. 
        (* k1 *) eapply vars_locs_sep. eapply SEP_K1E2. eapply H_k1. eauto. 
        (* m1 *) eapply vars_locs_sep. eapply SEP_M1E2. eapply H_m1. eauto. 
        (* fresh x *) eapply vars_locs_not_fresh2; eauto. unfoldq. eapply H_fresh1. 
        
        (* -- e2x -> vx -- *)

        destruct e2x. 2: destruct H. 
        destruct (HQX x) as [HV_old | [HV_moved | HV_fresh]]. eauto.

        (* vx old: q1 *)
        destruct HK2 as [H_K | [H_kf | [[H_mf ?] | [H_freshf | [H_k1 | [H_m1 | H_fresh1]]]]]].

        (* K  *) eapply KSEPE. split. eauto. right. right. right. eauto. 
        (* kf *) eapply vars_locs_sep. eapply SEP_KFE2x. eapply H_kf. eauto.
        (* mf *) eapply vars_locs_sep. eapply SEP_MFE2x. eapply H_mf. eauto.
        (* fresh f *) eapply vars_locs_not_fresh. eauto. eauto. eapply WFE. eapply H_freshf.
        (* k1 *) eapply vars_locs_sep. eapply SEP_K1E2x. eapply H_k1. eauto. 
        (* m1 *) eapply H_m1. eauto. (* eapply vars_locs_sep. eapply SEP_M1E2x. eapply H_m1. eauto. *)
        (* fresh x *) eapply H_fresh1. eauto. 

        (* vx moved: m1 *)
        
        destruct HK2 as [H_K | [H_kf | [[H_mf ?] | [H_freshf | [H_k1 | [H_m1 | H_fresh1]]]]]].
        
        (* K  *) eapply KSEPM. split. eauto. right. left. eauto. 
        (* kf *) eapply vars_locs_sep. eapply SEP_KFM1. eapply H_kf. eauto.
        (* mf *) eapply vars_locs_sep. eapply SEP_MFM1. eapply H_mf. eauto.
        (* fresh f *) eapply vars_locs_not_fresh. eauto. eauto. eapply WFE. eapply H_freshf.
        (* k1 *) eapply vars_locs_sep. eapply SEP_K1M1. eapply H_k1. eauto. (* k1 sep m1 here *)
        (* m1 *) eapply H_m1. eauto. 
        (* fresh x *) eapply H_fresh1. eauto.

        (* vx fresh *)

        destruct ST1 as [? [ST1 ?]].        
        destruct HK2 as [H_K | [H_kf | [[H_mf ?] | [H_freshf | [H_k1 | [H_m1 | H_fresh1]]]]]].

        (* K  *) eapply HV_fresh. eapply ST1. left. eauto. 
        (* kf *) eapply HV_fresh. eapply ST1. right. left. eauto. 
        (* mf *) eapply HV_fresh. eapply ST1. right. right. left. split. eauto. eauto. 
        (* fresh f *) eapply HV_fresh. eapply H_freshf. 
        (* k1 *) eapply vars_locs_not_fresh2. eapply H_k1. eapply WFE.
        split. eapply valt_wf; eauto. eapply HV_fresh. (* can't return fresh kill *)
        (* m1 *) eapply H_m1. eauto. 
        (* fresh x *) eapply H_fresh1. eauto.
      }

      (* XXXX unfortunate duplication below -- refactor? XXXX *)
      
      (* K2 sep m2/m2x *) {
        
        replace (plift m2) with (pand (plift p) (plift m2)).
        2: { intros. eapply functional_extensionality. intros. eapply propositional_extensionality. unfoldq. intuition. }
        unfold val_qual in HQF, HQX. 
        repeat rewrite VQ1 in *.
        repeat rewrite VQ2 in *.

        subst K2 K1. (* effect sep: K2 & m2 = empty <- m2 not killed *)
        repeat rewrite por_assoc.
        intros ? [HK2 Hm2]. 

        destruct Hm2.
        (* -- m2 -- *)
        
        destruct HK2 as [H_K | [H_kf | [[H_mf ?] | [H_freshf | [H_k1 | [H_m1 | H_fresh1]]]]]].

        (* K  *) eapply KSEPM. split. eauto. right. right. left. eauto. 
        (* kf *) eapply vars_locs_sep. eapply SEP_KFM2. eapply H_kf. eauto. 
        (* mf *) eapply vars_locs_sep. eapply SEP_MFM2. eapply H_mf. eauto.
        (* fresh f *) eapply vars_locs_not_fresh; eauto. unfoldq. eapply H_freshf.
        (* k1 *) eapply vars_locs_sep. eapply SEP_K1M2. eapply H_k1. eauto.
        (* m1 *) eapply vars_locs_sep. eapply SEP_M1M2. eapply H_m1. eauto.
        (* fresh x *) eapply vars_locs_not_fresh2; eauto. unfoldq. eapply H_fresh1. 
        
        (* -- m2x -> vx -- *)

        destruct m2x. 2: destruct H. 
        destruct (HQX x) as [HV_old | [HV_moved | HV_fresh]]. eauto.

        (* vx old: q1 *)
        destruct HK2 as [H_K | [H_kf | [[H_mf ?] | [H_freshf | [H_k1 | [H_m1 | H_fresh1]]]]]].

        (* K  *) eapply KSEPM. split. eauto. right. right. right. eauto. 
        (* kf *) eapply vars_locs_sep. eapply SEP_KFM2x. eapply H_kf. eauto.
        (* mf *) eapply vars_locs_sep. eapply SEP_MFM2x. eapply H_mf. eauto.
        (* fresh f *) eapply vars_locs_not_fresh. eauto. eauto. eapply WFE. eapply H_freshf.
        (* k1 *) eapply vars_locs_sep. eapply SEP_K1M2x. eapply H_k1. eauto. 
        (* m1 *) eapply H_m1. eauto. (* eapply vars_locs_sep. eapply SEP_M1E2x. eapply H_m1. eauto. *)
        (* fresh x *) eapply H_fresh1. eauto. 

        (* vx moved: m1 *)
        
        destruct HK2 as [H_K | [H_kf | [[H_mf ?] | [H_freshf | [H_k1 | [H_m1 | H_fresh1]]]]]].
        
        (* K  *) eapply KSEPM. split. eauto. right. left. eauto. 
        (* kf *) eapply vars_locs_sep. eapply SEP_KFM1. eapply H_kf. eauto.
        (* mf *) eapply vars_locs_sep. eapply SEP_MFM1. eapply H_mf. eauto.
        (* fresh f *) eapply vars_locs_not_fresh. eauto. eauto. eapply WFE. eapply H_freshf.
        (* k1 *) eapply vars_locs_sep. eapply SEP_K1M1. eapply H_k1. eauto. (* k1 sep m1 here *)
        (* m1 *) eapply H_m1. eauto. 
        (* fresh x *) eapply H_fresh1. eauto.

        (* vx fresh *)

        destruct ST1 as [? [ST1 ?]].
        destruct HK2 as [H_K | [H_kf | [[H_mf ?] | [H_freshf | [H_k1 | [H_m1 | H_fresh1]]]]]].

        (* K  *) eapply HV_fresh. eapply ST1. left. eauto. 
        (* kf *) eapply HV_fresh. eapply ST1. right. left. eauto. 
        (* mf *) eapply HV_fresh. eapply ST1. right. right. left. split. eauto. eauto. 
        (* fresh f *) eapply HV_fresh. eapply H_freshf. 
        (* k1 *) eapply vars_locs_not_fresh2. eapply H_k1. eapply WFE. split. eapply valt_wf; eauto. eapply HV_fresh. (* can't return fresh kill *)
        (* m1 *) eapply H_m1. eauto. 
        (* fresh x *) eapply H_fresh1. eauto.
      }

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
      rewrite <-vars_locs_se with (G:=env) (M1:=(M3++M2)++M1) (p:=plift p).
      eauto. eauto. unfoldq. intuition.
    }

      unfold val_qual in *.
      (* also tighten any val_locs based on val_type ? *)
      
      (* ----------- store_type  ---------- *)
      split. eapply storet_restrict. eapply SW3.

      (* (1) effect bound: K from val_type < K from has_type *) {

      subst K2 K1. 
      repeat rewrite por_assoc. repeat rewrite plift_or, plift_if, plift_empty, plift_or, plift_or.
      repeat rewrite pand_dist_or. repeat rewrite vars_locs_dist_or. repeat rewrite por_assoc.

      replace (plift k2) with (pand (plift p) (plift k2)).
      2: { intros. eapply functional_extensionality. intros. eapply propositional_extensionality. unfoldq. intuition. }

      replace (plift m2) with (pand (plift p) (plift m2)).
      2: { intros. eapply functional_extensionality. intros. eapply propositional_extensionality. unfoldq. intuition. }

      replace (pand (plift p) (pand (plift p) (plift k2))) with (pand (plift p) (plift k2)).
      2: { intros. eapply functional_extensionality. intros. eapply propositional_extensionality. unfoldq. intuition. }

      replace (pand (plift p) (pand (plift p) (plift m2))) with (pand (plift p) (plift m2)).
      2: { intros. eapply functional_extensionality. intros. eapply propositional_extensionality. unfoldq. intuition. }
      
      unfold val_qual in HQF, HQX. 
      
      repeat rewrite VQ3 in *.
      repeat rewrite VQ2 in *.
      repeat rewrite VQ1 in *.
      
      unfoldq. repeat rewrite app_length. intros x EXX.

      destruct EXX as [H_K | [H_kf | [[H_mf ?] | [H_freshf | [H_k1 | [[H_m1 ?] | [H_fresh1 | [H_k2 | [H_k2x | [[H_m2 ?] | [H_m2x | H_fresh2]]]]]]]]]]].
      

      (* K --> K *)
      left. eauto.

      (* kf --> kf *)
      right. left. eauto. 

      (* mf, !vf  --> mf, !vy, could be vx *)
      right. right. right. right. right. left. split. eauto.
      intros ?.
      assert (x < length M). eapply env_type_store_wf. eauto. eapply H_mf. 
      destruct (HQY2 x) as [? | [? | ?]]. { repeat rewrite app_length. intuition. }
      contradiction. (* !vf *)
      (* - *) destruct q2x. 2: contradiction.
      destruct (HQX x) as [? | [? | ?]]. eauto.
      destruct H3. destruct H3. 
      eapply vars_locs_sep. eapply SEP_MFQ1. eauto. exists x0. intuition. 
      eapply vars_locs_sep. eapply SEP_MFM1. eauto. eauto.
      rewrite app_length in H3. lia. 
      destruct m2x. 2: contradiction.
      destruct (HQX x) as [? | [? | ?]]. eauto.
      destruct H3. destruct H3. 
      eapply vars_locs_sep. eapply SEP_MFQ1. eauto. exists x0. intuition.
      eapply vars_locs_sep. eapply SEP_MFM1. eauto. eauto.
      rewrite app_length in H3. lia. 
      
      (* fresh f: !vf, !M, M1 --> !vy, could be vx *)
      right. right. right. right. right. right. split. lia. intros ?.
      destruct (HQY2 x) as [? | [? | ?]]. { repeat rewrite app_length. intuition. }
      intuition. (* !vf *)
      destruct q2x. 2: contradiction.
      destruct (HQX x) as [? | [? | ?]]. eauto. 
      destruct H1. destruct H1. 
      eapply vars_locs_not_fresh. exists x0. eauto. eauto. eapply WFE. eapply H_freshf.
      eapply vars_locs_not_fresh. eauto. eauto. eauto. eapply H_freshf. rewrite app_length in H1. lia.
      destruct m2x. 2: contradiction.
      destruct (HQX x) as [? | [? | ?]]. eauto.
      destruct H1. destruct H1. 
      eapply vars_locs_not_fresh. exists x0. eauto. eauto. eapply WFE. eapply H_freshf.
      eapply vars_locs_not_fresh. eauto. eauto. eapply WFE. eapply H_freshf. rewrite app_length in H1. lia. 

      (* k1 --> k1 *)
      right. right. left. eauto.

      (* m1, !vx --> m1, !vy *)

      right. right. right. right. right. left. split. right. left. eapply H_m1. intros ?.
      assert (x < length M). eapply env_type_store_wf. eauto. eapply H_m1. 
      destruct (HQY2 x) as [? | [? | ?]]. { repeat rewrite app_length. intuition. }
      destruct (HQF x) as [? | [? | ?]]. intuition.
      destruct H3. destruct H3. 
      eapply vars_locs_sep. eapply SEP_QFM1. exists x0. eauto. eauto. 
      eapply vars_locs_sep. eapply SEP_MFM1. eauto. eauto.
      lia. 
      destruct q2x. eauto. contradiction.
      destruct m2x. eauto. contradiction.

      (* fresh x: !vx, !M, !M1, M2 --> !vy, could be vf *)
      right. right. right. right. right. right. split. lia. intros ?.
      destruct (HQY2 x) as [? | [? | ?]]. { repeat rewrite app_length. intuition. }
      destruct H_fresh1 as [[? H_f1] ?].
      eapply H_f1. rewrite <-app_length. eapply valt_wf; eauto.
      destruct q2x. 2: contradiction.
      eapply H_fresh1. eauto. 
      destruct m2x. 2: contradiction.
      eapply H_fresh1. eauto. 

      (* k2 --> k2 *)
      right. right. right. left. eauto.

      (* k2x & vx --> q1 or m1! *)
      destruct k2x. 2: contradiction.
      
      destruct (HQX x) as [HX_old | [HX_moved | HX_fresh]]. eauto.

      (* vx old *)
      right. right. right. right. left. eauto.

      (* vx moved *)
      right. right. right. right. right. left. split. right. left. eauto.
      intros ?. 
      destruct (HQY2 x) as [? | [? | ?]]. intuition.
      eapply valt_wf. eapply HVX. eauto.

        (* vy is vf *)
        eapply HQF in H0. destruct H0 as [HF_old | [HF_moved | HF_fresh]].
          (* vf olf *)
          eapply vars_locs_sep. eapply SEP_QFM1. eauto. eauto.
          (* vf moved *)
          eapply vars_locs_sep. eapply SEP_MFM1. eauto. eauto.
          (* vf fresh *)          
          eapply vars_locs_not_fresh. eapply HX_moved. eauto. eapply WFE. eauto. 
        (* vy is q2x/vx *)
        rewrite SEP_K2XQ2X in H0. contradiction. eauto.
        (* vy is m2x/vx *)
        rewrite SEP_K2XM2X in H0. contradiction. eauto.

      (* vx fresh *)
      right. right. right. right. right. right. unfoldq. 
      split. split. eapply valt_wf in H_k2x. unfoldq. repeat rewrite app_length in H_k2x. lia. eauto. rewrite app_length in HX_fresh. lia.
      intros ?. 
      destruct (HQY2 x) as [? | [? | ?]]. split.
      eapply valt_wf; eauto. eauto. 

      eapply HX_fresh. eapply valt_wf. eapply HVF. eauto. 
      rewrite SEP_K2XQ2X in H0. (* q2x = false *) contradiction. eauto.
      rewrite SEP_K2XM2X in H0. (* m2x = false *) contradiction. eauto.

      (* m2 --> m2 *)
      right. right. right. right. right. left. split. right. right. left. eauto. eauto.

      (* m2x & vx *)
      destruct m2x. 2: contradiction.

      destruct (HQX x) as [HX_old | [HX_moved | HX_fresh]]. eapply H_m2x. 

      (* vx old *)
      right. right. right. right. right. left. split. right. right. right. eauto.
      eapply H_m2x. (* ~ val_locs vy x *)
      (* vx moved *)
      right. right. right. right. right. left. split. right. left. eauto.
      eapply H_m2x. (* ~ val_locs vy x *)
      (* vx fresh *)
      right. right. right. right. right. right. unfoldq. repeat rewrite app_length in HX_fresh.
      split. split.
      eapply valt_wf in HVX. unfoldq. repeat rewrite app_length in HVX. destruct H_m2x. eapply HVX in H. lia. lia. eapply H_m2x.

      
      (* H_fresh2 *)
      right. right. right. right. right. right. intuition.

      }

      
      (* (2) K < dom *)
      repeat rewrite plift_or. unfoldq. repeat rewrite app_length. intros ? EXX.
      destruct EXX as [?|[?|[?|?]]].
      (* K  *) repeat rewrite <-app_length. destruct SW3 as [? [SW3 ?]]. eapply SW3. left. subst K2. left. subst K1. left. eauto.
      (* k2 *) destruct H. destruct H. destruct H. eapply envt_var_store_wf in H0; eauto. unfoldq. lia. 
      (* m2 *) destruct H. destruct H. destruct H. eapply envt_var_store_wf in H1; eauto. unfoldq. lia. 
      (* fresh *) lia. 

      
      (* ----------- val_type & val_qual  ---------- *)
      
      split. eapply HVY.
      destruct q2x.
      repeat rewrite plift_or. repeat rewrite por_assoc. rewrite plift_if, plift_empty. eapply HQY.
      repeat rewrite plift_or. repeat rewrite por_assoc. rewrite plift_if, plift_empty. eapply HQY.

      
      
  - (* Case "Abs". *)
    rename H6 into ST. 
    exists S. exists []. exists (vabs E (qand p qf) t).
    split.
    + (* term evaluates *)
      exists 0. intros. destruct n. lia. simpl. eauto.
    + (* result well typed *)
      rewrite app_nil_l.
      split. rewrite plift_empty in *.
      eapply storet_restrict. eauto. unfoldq. intuition. unfoldq. intuition.
      destruct ST as [? [ST ?]]. eapply ST. eauto. destruct H6 as [? [[? []] ?]]. destruct H6 as [? [[? []] ?]]. 
      
      split. simpl. 

      rewrite <-LE in *. repeat split; eauto. 
      rewrite val_locs_abs. eapply env_type_store_wf. eauto.
      
      intros S1 M1 K1 vx ST1 HVX SEP KSEPE KSEPM.

    assert (forall q,
               vars_locs (M1 ++ M) E (pand (plift p) q) =
                 vars_locs M E (pand (plift p) q)) as VQ1. {
      intros. 
      rewrite <-vars_locs_se with (G:=env) (M1:=M1) (p:=plift p).
      eauto. eauto. unfoldq. intuition.
    }

      
      assert (val_locs (M1++M) (vabs E (qand p qf) t) = val_locs M (vabs E (qand p qf) t)). {
        repeat rewrite val_locs_abs, plift_and. rewrite VQ1. eauto.
      }
      
      eapply sem_abs1 with (m2:=m2); eauto. 
      rewrite H6. eauto. clear H6.
      intros. eapply IHW. eauto. eauto.

      (* vx, e2 sep K1 *) {
      rewrite val_locs_abs, plift_and in SEP.
      rewrite plift_or, plift_and, plift_or, plift_if, plift_one, plift_empty.
      unfoldq. intuition.
      destruct H11 as [x0 ?].
      bdestruct (x0 =? length E). destruct e2x. subst x0.
      
      destruct H9. destruct H9. destruct H9. destruct H9. eapply PC in H9. lia.
      destruct H12. eapply H3 in H12. lia.
      destruct H11. destruct H11. rewrite indexr_head in H11. inversion H11. subst x0.
      eapply KSEPE. intuition. eauto. intuition.
      (* e2x = false *)
      subst x0.
      destruct H9. destruct H9. destruct H9. destruct H9. eapply PC in H9. lia.
      destruct H12. eapply H3 in H12. lia. contradiction.
      (* x0 <> length E *)
      eapply KSEPE. split. eauto.
      destruct H9. destruct H9. destruct H9. 2: lia.
      destruct H13. left. exists x0. intuition. eapply var_locs_shrink; eauto.
      right. destruct e2x. lia. contradiction.
      }

      (* vx, m2 sep K1 *) {
      rewrite val_locs_abs, plift_and in SEP.
      rewrite plift_or, plift_and, plift_or, plift_if, plift_one, plift_empty.
      unfoldq. intuition.
      destruct H11 as [x0 ?].
      bdestruct (x0 =? length E). destruct m2x. subst x0.
      
      destruct H9. destruct H9. destruct H9. destruct H9. eapply PC in H9. lia.
      destruct H12. eapply H5 in H12. lia.
      destruct H11. destruct H11. rewrite indexr_head in H11. inversion H11. subst x0.
      eapply KSEPM. intuition. eauto. intuition.      
      (* m2x = false *)
      subst x0.
      destruct H9. destruct H9. destruct H9. destruct H9. eapply PC in H9. lia.
      destruct H12. eapply H5 in H12. lia. contradiction.
      (* x0 <> length E *)
      eapply KSEPM. split. eauto.
      destruct H9. destruct H9. destruct H9. 2: lia.
      destruct H13. left. exists x0. intuition. eapply var_locs_shrink; eauto.
      right. destruct m2x. lia. contradiction.
      }

      assert (psub (pand (plift p) (plift qf)) (pdom E)) as CL. {
        unfoldq. intuition. }
      rewrite <- plift_and in CL.
      eapply CL.
      
      rewrite plift_empty.
      eapply valq_abs; eauto.

      
  -  (* Case "Sub". *)
    destruct (IHW M E WFE S K) as [S1 [M1 [vx [IW1 [SW1 [HVX HQX]]]]]]. { eauto. }
     assert (psub (plift q2) (pdom E)). {
      unfoldq. rewrite LE. intuition. }

    unfoldq. intuition. destruct H13. eapply (H8 x). intuition. exists x0. intuition.
    unfoldq. intuition. destruct H12. eapply (H9 x). intuition. exists x0. intuition.
    
    exists S1, M1, vx.
    unfold exp_type. intuition.
    eapply storet_restrict. eauto. 

    (* k1 < k2 *)
    unfoldq. intros. destruct H10 as [|[|[|]]].
    left. intuition.
    right. left. destruct H10. exists x0. unfoldq. intuition.
    right. right. left. destruct H10 as [[? ?] ?].
      intuition. exists x0. unfoldq. intuition.
    eauto.

    (* < dom M1 ++ M *)
    unfoldq. intros. destruct H10 as [|[|[|]]].
    destruct SW1 as [? [SW1 ?]]. eapply SW1. eauto.
    destruct H10.
    assert (x < length M). eapply envt_var_store_wf. eauto. eapply H10. 
    rewrite app_length. lia.
    destruct H10 as [[? ?] ?].
    assert (x < length M). eapply envt_var_store_wf. eauto. eapply H10. 
    rewrite app_length. lia.
    eapply H10.
    
    eapply valq_sub; eauto. rewrite DE. eauto. rewrite DE. eauto. 
Qed.


(* note: not assuming anything other than has_type below *)

Corollary safety : forall t T q e k m,
  has_type [] t T qempty q e k m -> 
  exists S M v, exp_type [] [] (plift qempty) [] t S M v T (plift qempty) (plift q) (plift e) (plift k) (plift m).
Proof. 
  intros. eapply full_total_safety in H; eauto.
  unfold env_type; intuition; simpl. unfoldq. intuition. inversion H0.
  unfold store_type. intuition.
  unfoldq. intuition. inversion H0.
  unfoldq. intuition. inversion H0.
  unfoldq. intuition.
  unfoldq. intuition.
Qed.

End STLC.
