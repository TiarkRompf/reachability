(*******************************************************************************
* Coq mechanization of the λ$^{\diamond}-calculus.
* - Syntactic definitions
* - Semantic definitions
* - Metatheory
*******************************************************************************)

(* Full safety for STLC *)

(* based on sec4_reach_nested.v *)

(* 

Simply-typed lambda calculus with higher-order mutable stores and reachability types, combined 
proof of termination,  logical equivalence, congruencey of binary logical relations,
and soundness of binay logical relations. 


THIS FILE:


- types and qualifiers
  - overlap (explicit transitive closure)
  - self refs
  - fresh flag
  - no parametric polymorphism

- references
  - generic and nested refs (non-fresh qualifier)
  - mutation with put/get
  - self flag (for get, to enable escaping)

  - no self for put (would enable recursion)
  - no fresh values in store (would require move effects)

- effects
  - no effect qualifiers

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

(*******************************************************************************
* Syntactic Definitions
* - Typing `has_type`
* - Context typing 'ctx_type'
*******************************************************************************)

(* ---------- qualifier sets ---------- *)

Definition qif (b:bool) q (x:nat) := if b then q x else false.


Definition pl := nat -> Prop.

Definition pempty: pl := fun x => False.                            (* empty set *)

Definition pone (x:nat): pl := fun x' => x' = x.                    (* singleton set *)

Definition pand p1 p2 (x:nat) := p1 x /\ p2 x.                      (* intersection *)

Definition por p1 p2 (x:nat) := p1 x \/ p2 x.                       (* union *)

Definition pnot p1 (x:nat) := ~ p1 x.                               (* complement *)

Definition pdiff p1 p2 (x:nat) := p1 x /\ ~ p2 x.                   (* difference *)

Definition pnat n := fun x' =>  x' < n.                             (* numeric bound *)

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
  | TRef   : ty -> bool -> ql -> ty
  | TFun   : ty -> bool -> bool -> ql ->
             ty -> bool -> bool -> bool -> ql ->
             ty
.

(*
   TRef
        T       : element type
        qrf     : element may be fresh/self? (result of get needs to alias ref)
        q       : element reachability qualifier

   TFun
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
  | tapp : tm -> tm -> tm 
  | tabs : ql -> tm -> tm 
  | tseq : tm -> tm -> tm
.


Inductive vl : Type :=
  | vbool : bool -> vl
  | vref  : id -> vl
  | vabs  : list vl -> ql -> tm -> vl    (* closure record  *)
                                         
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
| c_ref: forall m T fr q,
    closed_ty m T ->
    closed_ql m q ->
    closed_ty m (TRef T fr q)
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
| t_ref: forall t env T p q,
    has_type env t T p false q ->
    psub (plift q) (plift p) ->
    has_type env (tref t) (TRef T false q) p true q
| t_get1: forall t env T p q1 fr q, (* special case 1 *)
    has_type env t (TRef T false q1) p fr q ->
    psub (plift q1) (plift p) -> 
    has_type env (tget t) T p false q1
| t_get2: forall t env T p q1 fr q, (* special case 2 *)
    has_type env t (TRef T false q1) p fr q ->
    has_type env (tget t) T p fr q
| t_get: forall t env T p q1 rf1 fr q,
    has_type env t (TRef T rf1 q1) p fr q ->
    psub (plift q1) (plift p) ->
    has_type env (tget t) T p (if rf1 then fr else false) (qor q1 (qif rf1 q))

| t_put: forall t1 t2 T env p fr1 q1 rf2 q2,
    has_type env t1 (TRef T rf2 q2) p fr1 q1 ->
    has_type env t2 T p false q2 ->
    has_type env (tput t1 t2) TBool p false qempty 
| t_app: forall env f t T1 T2 p frf qf frx qx fn1 fr1 q1 fn2 ar2 fr2 q2,
    has_type env f (TFun T1 fn1 fr1 q1 T2 fn2 ar2 fr2 q2) p frf qf ->  
    has_type env t T1 p frx qx ->
    (* ---- different app cases: *)
    (if fn1 then
       if fr1 then
         True
       else
         (frx = false /\ (exists x0, f = tvar x0 /\ psub (plift qx) (pone x0))) \/ (* f : µz. (x: A^z); f(f); val x: A^f; f(x)*)
         (frx = false /\ (exists p0 t0, f = tabs p0 t0 /\ psub (plift qx) (plift p0))) \/
         (frx = false /\ psub (plift qx) (plift q1)) 
     else
       if fr1 then
         psub (pand 
                 (vars_trans' env qf)
                 (vars_trans' env qx))
           (plift q1)
       else
         frx = false /\ psub (plift qx) (plift q1)) ->
    (* ---- *)
    psub (plift q1) (plift p) ->   
    psub (plift q2) (plift p) ->   
    has_type env (tapp f t) T2 p
      (fn2 && frf || ar2 && frx || fr2)
      (qor (qif fn2 qf) (qor (qif ar2 qx) q2))
| t_abs: forall env t T1 T2 p fn1 fr1 q1 fn2 ar2 fr2 q2 qf,
    has_type ((T1, fr1, (qand p (qor q1 (qif fn1 qf))))::env) t T2 
      (qor (qand p qf) (qone (length env)))
      fr2
      (qor q2 (qor (qif ar2 (qone (length env)))(qif fn2 (qand p qf)))) 
      ->
    psub (plift q1) (pand (plift p) (plift qf)) ->   
    closed_ty (length env) T1 ->
    closed_ty (length env) T2 ->
    closed_ql (length env) q1 ->
    closed_ql (length env) q2 ->
    closed_ql (length env) qf ->
    has_type env (tabs (qand p qf) t)
      (TFun T1 fn1 fr1 q1 T2 fn2 ar2 fr2 q2)
      p false qf 
| t_seq: forall env t1 t2 p1 p2 p q1 q2,
    has_type env t1 TBool p1 false q1 ->
    has_type env t2 TBool p2 false q2 ->
    psub (plift p1) (plift p) ->
    psub (plift p2) (plift p) ->
    has_type env (tseq t1 t2) TBool p false qempty
| t_sub: forall env y T p fr1 q1 fr2 q2,
    has_type env y T p fr1 q1 ->
    psub (plift q1) (plift q2) ->
    psub (plift q2) (pdom env) ->
    has_type env y T p (fr1 || fr2)  q2
| t_sub_var: forall env y T p fr1 q1 qx x Tx,
    has_type env y T p fr1 q1 ->
    plift q1 x ->
    indexr x env = Some (Tx, false, qx) ->
    psub (plift qx) (plift p) -> 
    has_type env y T p fr1 (qor (qdiff q1 (qone x)) qx)
.

(*******************************************************************************
* Semantic Definitions
* - Bigstep Interpreter `teval`
* - Value Interpretation `val_type`
* - Term Interpretation 'exp_type'
* - Semantic Typing `sem_type`
*******************************************************************************)

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
                    | Some v => (update M'' x vx, Some (Some (vbool true)))
                    | _ => (M'', Some None)
                    end
              end
          end
        | tseq e1 e2   =>
          match teval n M env e1 with
          | (M', None) => (M', None)
          | (M', Some None) => (M', Some None)
          | (M', Some (Some (vbool b1))) => 
              match teval n M' env e2 with
              | (M'', None) => (M'', None)
              | (M'', Some None) => (M'', Some None)
              | (M'', Some (Some (vbool b2))) => (M'', Some (Some (vbool (b1 && b2))))
              | (M'', Some (Some (vref _))) => (M'', Some None)
              | (M'', Some (Some (vabs _ _ _))) => (M'', Some None)
              end
          | (M', Some (Some (vref _))) => (M', Some None)
          | (M', Some (Some (vabs _ _ _))) => (M', Some None)
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
      let fix vars_locs_fix (H: list vl) :=
        match H with
        | v :: H => (q (length H) && val_locs_fix v l) || vars_locs_fix H
        | [] => false
        end
      in vars_locs_fix H
  end.


Definition loc_locs (S: stor) (l: nat) (l': nat): bool :=
  match indexr l S with
  | Some v => val_locs_fix v l'
  | None => false
  end.



Fixpoint val_locs_n_fix n (S: stor) (v: vl) (l: nat): bool :=
  match n with
  | S n =>
      let fix vals_locs_fix (S: stor) :=
        match S with
        | v :: S' => val_locs_fix v (length S') && val_locs_n_fix n S v l
                     || vals_locs_fix S'
        | [] => false
        end
      in
      vals_locs_fix S
  | 0 => val_locs_fix v l
  end.


Fixpoint val_locs_trans (S: stor) (v: vl) (l: nat): bool :=
  let fix iter n :=
    match n with
    | S n' => val_locs_n_fix n S v l || iter n'
    | 0 => val_locs_n_fix 0 S v l
    end
  in iter (length S).


Fixpoint vars_locs_fix (H: venv) (q: ql) (l: nat): bool :=
  match H with
  | v :: H => (q (length H) && val_locs_fix v l) || vars_locs_fix H q l
  | [] => false
  end.




Definition val_locs v := plift (val_locs_fix v). 

Definition var_locs E x l := exists vx, indexr x E = Some vx /\ val_locs vx l.

Definition vars_locs E q l := exists x, q x /\ var_locs E x l.



Inductive locs_locs_stor: stor -> pl -> pl :=
| llss_z: forall S (q:pl) x,
    q x ->
    locs_locs_stor S q x
| llss_s: forall S (q:pl) x x1 v,
    q x1 ->
    indexr x1 S = Some v ->
    locs_locs_stor S (val_locs v) x ->
    locs_locs_stor S q x.



(* "worlds" *)

(* consists of:

    - store type for S1
    - store type for S2
    - binary relation between locations that
      are supposed to be equivalent

   we enforce that this relation is a partial bijection
*)

Definition st: Type := list ql.

Fixpoint locs_locs_stty_fix (M: st) (q: ql): ql :=
  match M with
  | [] => q
  | qt :: M =>
      if q (length M) then
        qor (locs_locs_stty_fix M q) (locs_locs_stty_fix M qt)
      else
        locs_locs_stty_fix M q
  end.

Inductive locs_locs_stty: st -> pl -> pl :=
| lls_z: forall M (q:pl) x,
    q x ->
    locs_locs_stty M q x
| lls_s: forall M (q:pl) x x1 qt,
    q x1 ->
    indexr x1 M = Some qt ->
    locs_locs_stty M (plift qt) x ->
    locs_locs_stty M q x.

Definition stty: Type := (st * st * (nat -> nat -> Prop) * (nat -> nat -> (vl -> vl -> Prop))).
Definition st1 (M: stty) := fst (fst (fst M)).
Definition st2 (M: stty) := snd (fst (fst M)).
Definition length1 (M: stty) := length(st1 M).
Definition length2 (M: stty) := length(st2 M).
Definition strel (M: stty) := snd (fst M).
Definition st_valtype (M: stty) := snd M.

Definition st_locs1 (M: stty) := (pnat (length1 M)).
Definition st_locs2 (M: stty) := (pnat (length2 M)).

Definition st_filter (M:stty) (p1 p2: pl) :=
  psub p1 (st_locs1 M) /\
  psub p2 (st_locs2 M) /\
  (forall l1 l2,
    strel M l1 l2 ->
    (p1 l1 <-> p2 l2)).


Definition sst_chain_partial (M: st)(M1:st)(p: pl) :=
  psub p (pdom M) /\
  psub p (pdom M1) /\
  forall l, p l ->
    indexr l M = indexr l M1
.


(* world extension -- monotonic *)

Definition st_chain_partial (M:stty) (M1:stty) (p1 p2: pl) :=
  st_filter M p1 p2 /\
  st_filter M1 p1 p2 /\
  sst_chain_partial (st1 M)(st1 M1) p1 /\
  sst_chain_partial (st2 M)(st2 M1) p2 /\
  (forall l1 l2 , 
            p1 l1 ->
            p2 l2 ->
            strel M l1 l2 ->
            st_valtype M l1 l2 = st_valtype M1 l1 l2) /\
  (forall l1 l2,
    p1 l1 /\ p2 l2 -> 
    strel M l1 l2 <-> strel M1 l1 l2).

Definition sst_chain (M: st)(M1: st) :=
  sst_chain_partial M M1 (pdom M).

Definition st_chain (M:stty) (M1:stty) :=
  st_chain_partial M M1 (st_locs1 M) (st_locs2 M).    

 
Definition st_extend M vt q1 q2: stty :=
  (q1 :: (st1 M),
   q2 :: (st2 M),
   (fun l1 l2 => l1 = length1 M /\ l2 = length2 M \/ strel M l1 l2),
   (fun l1 l2 v1 v2 => l1 = length1 M /\ l2 = length2 M /\ vt v1 v2 \/ 
                       (exists vt', l1 < length1 M /\ l2 < length2 M /\ st_valtype M l1 l2 = vt' /\ vt' v1 v2))).


#[global] Hint Unfold length1.
#[global] Hint Unfold length2.

Definition sstore_type (S: stor)(M: st) :=
    length S = length M /\
    forall l, 
      l < length S ->
      exists qt v,
      indexr l M = Some qt /\
      indexr l S = Some v /\
      psub (locs_locs_stty M (val_locs v)) (locs_locs_stty M (plift qt)) /\
      psub (plift qt) (pnat l)
.

Definition store_type (S1 S2: stor) (M: stty) := 
  sstore_type S1 (st1 M) /\
  sstore_type S2 (st2 M) /\
    (forall l1 l2 ,
      strel M l1 l2 ->
      exists vt qt1 qt2 v1 v2, 
      indexr l1 (st1 M) = Some qt1 /\
      indexr l2 (st2 M) = Some qt2 /\
      indexr l1 S1 = Some v1 /\
      indexr l2 S2 = Some v2 /\
      st_valtype M l1 l2 = vt /\
      vt v1 v2 /\
      st_filter M (locs_locs_stty (st1 M) (val_locs v1))(locs_locs_stty (st2 M) (val_locs v2)) 
      ) /\
    (* enforce that strel is a partial bijection *)
    (forall l1 l2 l2',
        strel M l1 l2 ->
        strel M l1 l2' ->
        l2 = l2') /\
    (forall l1 l1' l2,
        strel M l1 l2 ->
        strel M l1' l2 ->
        l1 = l1').

(* store preservation invariant *)

Definition store_effect (S S1: stor) (p: pl) :=
  forall l v,
    ~ p l -> 
    indexr l S = Some v ->
    indexr l S1 = Some v.

(* value interpretation of types *)

Fixpoint val_type (M:stty) (H1 H2:venv) v1 v2 T1 T2 : Prop :=
  match v1, v2, T1, T2 with
  | vbool b1, vbool b2, TBool, TBool =>
      b1 = b2
  | vref l1, vref l2, TRef T1 fr1 q1, TRef T2 fr2 q2 => 
    closed_ty (length H1) T1 /\
    closed_ty (length H2) T2 /\
    fr1 = false /\
    fr2 = false /\
    psub (plift q1) (pdom H1) /\
    psub (plift q2) (pdom H2) /\
    strel M l1 l2 /\ 
    st_filter M (locs_locs_stty (st1 M) (val_locs v1)) (locs_locs_stty (st2 M) (val_locs v2)) /\
    exists vt qt1 qt2,
        indexr l1 (st1 M) = Some qt1 /\ 
        indexr l2 (st2 M) = Some qt2 /\
        st_valtype M l1 l2 = vt /\
        (forall M' S1' S2',
            st_chain_partial M M' (locs_locs_stty (st1 M) (plift qt1)) (locs_locs_stty (st2 M) (plift qt2)) ->
            store_type S1' S2' M' ->
            forall v1' v2',
              st_filter M' (locs_locs_stty (st1 M') (val_locs v1'))(locs_locs_stty (st2 M') (val_locs v2')) ->  
              psub (locs_locs_stty (st1 M') (val_locs v1')) (locs_locs_stty (st1 M') (plift qt1)) -> 
              psub (locs_locs_stty (st2 M') (val_locs v2')) (locs_locs_stty (st2 M') (plift qt2)) ->
              (vt v1' v2' <-> val_type M' H1 H2 v1' v2' T1 T2)) /\
        plift qt1 = vars_locs H1 (plift q1) /\
        plift qt2 = vars_locs H2 (plift q2) /\
        psub (locs_locs_stty (st1 M) (plift qt1)) (locs_locs_stty (st1 M) (pone l1)) /\ 
        psub (locs_locs_stty (st2 M) (plift qt2)) (locs_locs_stty (st2 M) (pone l2)) 
  |  vabs G1 py1 ty1, vabs G2 py2 ty2, TFun T1 fn1 fr1 q1 T2 fn2 ar2 fr2 q2, TFun T1' fn1' fr1' q1' T2' fn2' ar2' fr2' q2' =>
        closed_ty (length H1) T1 /\
        (psub (plift q1) (pdom H1)) /\
        closed_ty (length H1) T2 /\
        (psub (plift q2) (pdom H1)) /\
        closed_ty (length H2) T1' /\
        (psub (plift q1') (pdom H2)) /\
        closed_ty (length H2) T2' /\
        (psub (plift q2') (pdom H2)) /\
        (st_filter M (locs_locs_stty (st1 M)(val_locs v1))(locs_locs_stty (st2 M)(val_locs v2))) /\
        (forall S1' S2' M' vx1 vx2,
            st_chain_partial M M' (locs_locs_stty (st1 M) (val_locs v1)) (locs_locs_stty (st2 M) (val_locs v2))
            -> 
            st_filter M' (st_locs1 M')(st_locs2 M')
            ->
            store_type S1' S2' M'
            ->
            val_type
              M'
              H1
              H2
              vx1
              vx2
              T1
              T1'
            -> 
            psub (locs_locs_stty (st1 M') (val_locs vx1))
                    (por (pif fn1 (locs_locs_stty (st1 M') (val_locs v1)))
                      (por (pif fr1 (pnot (locs_locs_stty (st1 M') (val_locs v1))))
                        (locs_locs_stty (st1 M') (vars_locs H1 (plift q1)))))
            ->
            psub (locs_locs_stty (st2 M') (val_locs vx2))
                    (por (pif fn1' (locs_locs_stty (st2 M') (val_locs v2)))
                      (por (pif fr1' (pnot (locs_locs_stty (st2 M') (val_locs v2))))
                        (locs_locs_stty (st2 M') (vars_locs H2 (plift q1')))))
            ->
            exists S1'' S2'' M'' vy1 vy2,
              tevaln
              S1'
              (vx1::G1)
              ty1
              S1''
              vy1
            /\
            tevaln
              S2'
              (vx2::G2)
              ty2
              S2''
              vy2
            /\
            st_chain M' M''
            /\
            st_filter M'' (st_locs1 M'')(st_locs2 M'')  
            /\
            store_type S1'' S2'' M''
            /\
            store_effect S1' S1'' (por (locs_locs_stty (st1 M') (val_locs v1)) (locs_locs_stty (st1 M') (val_locs vx1)))
            /\
            store_effect S2' S2'' (por (locs_locs_stty (st2 M') (val_locs v2)) (locs_locs_stty (st2 M') (val_locs vx2)))
            /\
            val_type
              M''
              H1
              H2
              vy1 
              vy2
              T2
              T2'
            /\
            psub (locs_locs_stty (st1 M'') (val_locs vy1))
              (por (pand (locs_locs_stty (st1 M'') (vars_locs H1 (plift q2))) (locs_locs_stty (st1 M'') (val_locs v1))) (* allow v \/ vx? <- no, support tightening of q2 if fn2 *)
                (por (pif fn2 (locs_locs_stty (st1 M'') (val_locs v1)))
                  (por (pif ar2 (locs_locs_stty (st1 M'') (val_locs vx1)))
                    (pif fr2 (pdiff (pnat (length1 M'')) (pnat (length1 M')))))))
            /\
            psub (locs_locs_stty (st2 M'') (val_locs vy2))
              (por (pand (locs_locs_stty (st2 M'') (vars_locs H2 (plift q2'))) (locs_locs_stty (st2 M'') (val_locs v2))) (* allow v \/ vx? <- no, support tightening of q2 if fn2 *)
                (por (pif fn2' (locs_locs_stty (st2 M'') (val_locs v2)))
                  (por (pif ar2' (locs_locs_stty (st2 M'') (val_locs vx2)))
                    (pif fr2' (pdiff (pnat (length2 M'')) (pnat (length2 M'))))))))
  | _,_,_,_ =>
      False
  end.

(* reachability *)
Definition val_qual (M M1: st) H v fr (q: pl) :=
  psub (locs_locs_stty M1 (val_locs v))
    (por (locs_locs_stty M1 (vars_locs H q)) (* locs(v) & M & ~(p&q) = O *)
      (pif fr (pdiff (pnat (length M1)) (pnat (length M))))).


(* term interpretation *)
Definition exp_type S1 S2 M H1 H2 t1 t2 S1' S2' M' v1 v2 T p  fr q :=
  tevaln S1 H1 t1 S1' v1 /\
  tevaln S2 H2 t2 S2' v2 /\
  st_chain M M' /\
  st_filter M' (st_locs1 M') (st_locs2 M') /\
  store_type S1' S2' M' /\
  store_effect S1 S1' (locs_locs_stty (st1 M) (vars_locs H1 p)) /\
  store_effect S2 S2' (locs_locs_stty (st2 M) (vars_locs H2 p)) /\
  val_type M' H1 H2 v1 v2 T T /\
  val_qual (st1 M)(st1 M') H1 v1 fr (pand p q) /\
  val_qual (st2 M)(st2 M') H2 v2 fr (pand p q).

(* semantic context typing *)
Definition env_type M H1 H2 G p :=
  length H1 = length G /\
  length H2 = length G /\
  psub p (pdom H1) /\
  psub p (pdom H2) /\
  (forall x T fr (q:ql),
    indexr x G = Some (T, fr, q) ->
    exists v1 v2 : vl,
      closed_ql x q /\
      indexr x H1 = Some v1 /\
      indexr x H2 = Some v2 /\
      (p x -> val_type M H1 H2 v1 v2 T T) /\
      (fr = false -> p x -> psub (plift q) p -> psub (locs_locs_stty (st1 M) (val_locs v1)) (locs_locs_stty (st1 M) (vars_locs H1 (plift q)))) /\
      (fr = false -> p x -> psub (plift q) p -> psub (locs_locs_stty (st2 M) (val_locs v2)) (locs_locs_stty (st2 M) (vars_locs H2 (plift q))))
  ) 
  /\
 (forall q q',
    psub q p ->
    psub q' p ->
    psub (pand (vars_trans G q) (vars_trans G q')) p ->
    psub (pand (locs_locs_stty (st1 M) (vars_locs H1 q)) (locs_locs_stty (st1 M) (vars_locs H1 q')))
      (locs_locs_stty (st1 M) (vars_locs H1 (pand (vars_trans G q) (vars_trans G q')))))
  /\    
  (forall q q',
    psub q p ->
    psub q' p ->
    psub (pand (vars_trans G q) (vars_trans G q')) p ->
    psub (pand (locs_locs_stty (st2 M) (vars_locs H2 q)) (locs_locs_stty (st2 M) (vars_locs H2 q')))
      (locs_locs_stty (st2 M) (vars_locs H2 (pand (vars_trans G q) (vars_trans G q')))))
.

(* semantic type *)
Definition sem_type G t1 t2 T p fr q :=
  forall M H1 H2,
    env_type M H1 H2 G p ->
    st_filter M (st_locs1 M)(st_locs2 M) ->
    forall S1 S2,
    store_type S1 S2 M ->
    exists S1' S2' M' v1 v2,
    exp_type S1 S2 M H1 H2 t1 t2 S1' S2' M' v1 v2 T p fr q
.


#[export] Hint Constructors ty: core.
#[export] Hint Constructors tm: core.
#[export] Hint Constructors vl: cor.


#[export] Hint Constructors has_type: core.

#[export] Hint Constructors option: core.
#[export] Hint Constructors list: core.


Lemma tevaln_unique: forall S S' S'' H e v v',
    tevaln S H e S' v ->
    tevaln S H e S'' v' ->
    v = v' /\ S' = S''.
Proof.
  intros.
  destruct H0 as [n1 ?].
  destruct H1 as [n2 ?].
  assert (1+n1+n2 > n1) as A1. lia.
  assert (1+n1+n2 > n2) as A2. lia.
  specialize (H0 _ A1).
  specialize (H1 _ A2).
  rewrite H0 in H1. inversion H1. intuition.
Qed.

(* ---------- qualifier reflection & tactics  ---------- *)

Ltac unfoldq := unfold val_qual, psub, pdom, pnat, pdiff, pnot, pif, pand, por, pempty, pone, var_locs, vars_locs in *.
Ltac unfoldq1 := unfold qsub, qdom, qand, qempty, qone in *.

(* general reflection proof principle *)
Lemma plift_qual_eq: forall q1 q2,
    (q1 = q2) = (plift q1 = plift q2).
  intros. eapply propositional_extensionality.
  remember (plift q1) as p1.
  remember (plift q2) as p2. 
  unfold plift in *. intuition.
  - subst. eauto.
  - eapply functional_extensionality. intros.
    remember (q1 x) as qx1. symmetry in Heqqx1.
    remember (q2 x) as qx2. symmetry in Heqqx2.
    destruct qx1; destruct qx2; try reflexivity.
    + replace (q1 x = true) with (p1 x) in *.
      rewrite H in Heqqx1. subst p2. eauto. subst p1. eauto. 
    + replace (q2 x = true) with (p2 x) in *. 
      rewrite <-H in Heqqx2. subst p1. eauto. subst p2. eauto.
Qed.

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

Lemma pand_empty_r: forall p,
  pand p pempty = pempty.
Proof.
  intros. unfoldq. eapply functional_extensionality. intros.
  eapply propositional_extensionality. split; intuition.
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

Lemma var_locs_decide: forall H x l, 
    var_locs H x l \/ ~ var_locs H x l.
Proof.
  intros. unfold var_locs, plift.
  bdestruct (x <? length H).
  - assert (exists vx : vl, indexr x H = Some vx).
    eapply indexr_var_some. eauto.
    destruct H1. destruct (val_locs_decide x0 l).
    left. eauto.
    right. intros ?. eapply H2. destruct H3. destruct H3. congruence.
  - right. intros ?. destruct H1. destruct H1. eapply indexr_var_some' in H1. lia. 
Qed.

Lemma plift_vars_locs: forall H q,
    vars_locs H (plift q) = plift (vars_locs_fix H q).
Proof.
  intros. eapply functional_extensionality.
  intros. eapply propositional_extensionality.
  unfold vars_locs, var_locs, val_locs, plift in *.
  intuition.
  - simpl. destruct H0 as [? [? ?]]. destruct H1 as [? [? ?]].
    unfold indexr in H1. induction H.
    congruence. 
    bdestruct (x0 =? length H).
    inversion H1. subst. simpl. rewrite H0.
    unfold val_locs, plift in H2. rewrite H2. simpl. eauto.
    simpl. rewrite IHlist.
    destruct (q (length H) && val_locs_fix a x); simpl; eauto.
    eauto. 
  - induction H. intuition.
    remember (q (length H)) as b1.
    remember (val_locs_fix a x) as b2.
    destruct b1. destruct b2. simpl in H0.
    (* both true *)
    exists (length H). split. eauto.
    exists a. rewrite indexr_head. intuition.
    (* one false *)
    simpl in H0. rewrite <-Heqb1, <-Heqb2 in H0. simpl in H0. eapply IHlist in H0.
    destruct H0. exists x0. intuition.
    destruct H2. exists x1. rewrite indexr_extend1 in H0. intuition eauto.
    (* other false *)
    simpl in H0. rewrite <-Heqb1 in H0. simpl in H0. eapply IHlist in H0. 
    destruct H0. exists x0. intuition.
    destruct H2. exists x1. rewrite indexr_extend1 in H0. intuition eauto.
Qed.



(* ---------- closedness lemmas  ---------- *)

Lemma closedq_extend : forall {m q}, closed_ql m q -> 
  forall {m'}, m <= m' -> closed_ql m' q.
Proof.  
    intros. unfold closed_ql in *. intros. 
    specialize (H x). intuition.
Qed.

Lemma closedq_sub : forall {m q q'}, closed_ql m q' -> 
  psub (plift q) (plift q') -> closed_ql m q.
Proof.  
    intros. unfold closed_ql in *. intros. unfoldq; intuition. 
    specialize (H0 x). intuition.
Qed.

Lemma closedq_or: forall q1 q2 m,
  closed_ql m (qor q1 q2)  <->
  (closed_ql m q1 /\ closed_ql m q2).
Proof.
  intros. split; intros.
  - unfold closed_ql in *. split; intros.
    1,2: destruct (H x); intuition; bdestruct (qor q1 q2 x); intuition.
  - intuition. unfold closed_ql in *. intros. 
    bdestruct (qor q1 q2 x); intuition.
Qed.

Lemma  closedq_and: forall q1 q2 m,
  (closed_ql m q1 \/ closed_ql m q2) -> 
  closed_ql m (qand q1 q2).
Proof.
  intros. destruct H; unfold closed_ql in *; intros;
  bdestruct (qand q1 q2 x); intuition.
Qed.

Lemma closedq_one: forall m x,
  x < m ->
  closed_ql m (qone x).
Proof.
  intros. unfold closed_ql. intros.
  unfoldq1; intuition. apply Nat.eqb_eq in H0. subst. auto.
Qed.


Lemma closedql_empty: forall m,
  closed_ql m qempty.
Proof. 
  intros. unfold closed_ql. intros.
  unfoldq; intuition.
Qed.
#[global] Hint Resolve closedql_empty : core.

Lemma closedq_if: forall m p b,
  closed_ql m p ->
  closed_ql m (qif b p).
Proof.
  intros. destruct b. unfoldq; intuition. unfoldq; intuition.
Qed.

Lemma closedty_extend : forall {m T}, closed_ty m T -> 
  forall {m'}, m <= m' -> closed_ty m' T.
Proof. 
    intros. induction T; constructor.
    all: inversion H; subst; intuition.
    all: eapply closedq_extend; eauto.
Qed.


Lemma closedty_TBool: forall m, closed_ty m TBool.
Proof.
  intros. constructor.
Qed.
#[global] Hint Resolve closedty_TBool : core.

Lemma closedty_TRef: forall m T fr q, 
  closed_ty m T ->
  closed_ql m q ->
  closed_ty m (TRef T fr q).
Proof.
  intros. constructor; auto.
Qed.
#[global] Hint Resolve closedty_TRef : core.


Lemma filter_closed: forall M H1 H2 G p,
  env_type M H1 H2 G (plift p) ->
  closed_ql (length G) p.
Proof.
  intros. destruct H as [L1 [L2 [P1 [P2 P3]]]].
  unfold closed_ql. intros.
  unfoldq; intuition. eapply P1 in H.  rewrite L1 in H. auto.
Qed.

Lemma valt_closed: forall T T' M H1 H2 v1 v2,
    val_type M H1 H2 v1 v2 T T' ->
    ( closed_ty (length H1) T /\
      closed_ty (length H2) T') .
Proof. 
  intros T. induction T; intros; destruct T'; destruct v1; destruct v2; simpl in *; intuition.
  + econstructor; auto. 
  + subst. econstructor; auto.
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

Lemma vars_locs_mono: forall H q q',
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

Lemma vars_locs_empty: forall H,
  vars_locs H pempty = pempty.
Proof. 
  intros. eapply functional_extensionality.
  intros. eapply propositional_extensionality.
  split; intros. unfoldq; intuition. destruct H0. intuition.
  unfoldq; intuition.
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


Lemma vt_closed': forall G q1,
    telescope G ->
    psub (plift q1) (pdom G) ->
    psub (vars_trans G (plift q1)) (pdom G).
Proof.
  intros. intros ? ?. 
  bdestruct (x <? (length G)).
  - unfoldq. intuition.
  - eapply H0.
    eapply vars_trans_closed. eauto.
    rewrite plift_vt. eauto. eauto. eauto. 
Qed.

Lemma vt_closed: forall G q1,
    telescope G ->
    psub q1 (pdom G) ->
    psub (vars_trans G q1) (pdom G).
Proof.
  intros. intros ? ?.
  destruct H1. eauto.
  destruct H1 as (? & ? & ? & ?).
  destruct H3 as (? & ? & ? & ? & ?).
  eapply vt_closed'. eauto. eapply H in H3. unfoldq. intuition.
  2: rewrite <-plift_vt. 2: eapply H4. eapply H3 in H5.
  eapply H0 in H1. lia. eauto. 
Qed.


Lemma vt_head: forall G T1 fr1 q1 (q: pl),
    telescope G ->
    psub (plift q1) (pdom G) ->
    q (length G) ->
    psub (vars_trans G (plift q1)) (vars_trans ((T1, fr1, q1) :: G) q).
Proof.
  intros. intros ? ?. 
  right. exists (length G). intuition. 
  eapply vt_closed; eauto. 
  exists T1, fr1, q1. rewrite indexr_head. intuition.
  unfold vars_trans'. rewrite plift_vt. eapply vt_extend. eauto.
  eapply telescope_extend; eauto. 
Qed.


(* ---------- store typing lemmas  ---------- *)


(* st_filter *)

Lemma stf_empty: forall M,
  st_filter M pempty pempty.
Proof.
  intros. unfold st_filter; intuition.
  intros ? ?. unfold pempty in H. contradiction. 
  intros ? ?. unfold pempty in H. contradiction. 
Qed.

(* store typing chain *)

Lemma sst_mono: forall M M',
  sst_chain M M' ->
  length M <= length M'.
Proof.
  intros. unfold sst_chain, sst_chain_partial, pdom in H. intuition.
  destruct (length M). lia. eapply H. lia.
Qed.

Lemma st_mono1: forall M M',
  st_chain M M' ->
  length1 M <= length1 M'.
Proof.
  intros. unfold st_chain, st_chain_partial in H. intuition.
  unfold st_locs1, psub, pnat in *. intuition.
  destruct (length1 M). lia. eapply H. lia. 
Qed.

Lemma st_mono2: forall M M',
  st_chain M M' ->
  length2 M <= length2 M'.
Proof.
  intros. unfold st_chain, st_chain_partial in H. intuition.
  unfold st_locs2, psub, pnat in *. intuition.
  destruct (length2 M). lia. eapply H. lia.
Qed.

Lemma st_mono1': forall M M' l,
  st_chain M M' ->
  l < length1 M ->
  l < length1 M'.
Proof.
  intros. assert (length1 M <= length1 M'). eapply st_mono1; eauto. lia.
Qed.

Lemma st_mono2': forall M M' l,
  st_chain M M' ->
  l < length2 M ->
  l < length2 M'.
Proof.
  intros. assert (length2 M <= length2 M'). eapply st_mono2; eauto. lia.
Qed.


Lemma st_refl: forall M1,
    st_filter M1 (st_locs1 M1)(st_locs2 M1) ->
    st_chain M1 M1.
Proof.
  intros. destruct H as [? [? ?]]. repeat split; auto.
  intros. eapply H1; eauto.
  intros. eapply H1; eauto.
  intros. eapply H1; eauto.
  intros. eapply H1; eauto.
Qed.

Lemma sst_chain_partial_symmetry: forall M1 M2 p,
   sst_chain_partial M1 M2 p ->
   sst_chain_partial M2 M1 p.
Proof.
  intros. unfold sst_chain_partial in *; intuition.
  eapply H2 in H1. auto.
Qed.

Lemma stchain_symmetry: forall M1 M2 p1 p2,
    st_chain_partial M1 M2 p1 p2 ->
    st_chain_partial M2 M1 p1 p2.
Proof.
  intros.
  destruct H as (F1 & F2 & Z1 & Z2 & Z3 & Z4).
  split. 2: split. 3: split. 4: split. 5: split.
  eauto. eauto.
  eapply sst_chain_partial_symmetry; eauto.
  eapply sst_chain_partial_symmetry; eauto.
  intros. symmetry. eapply Z3; eauto. eapply Z4; eauto.
  symmetry. eauto.
Qed.


Lemma sst_trans: forall M1 M2 M3,
    sst_chain M1 M2 ->
    sst_chain M2 M3 ->
    sst_chain M1 M3.
Proof.
   intros. destruct H as [HA [HB HC]]. destruct H0 as [HD [HE HF]].
   unfold sst_chain, sst_chain_partial in *; intros. repeat split; auto; intros.
   + intros ? ?. unfold pdom in *. eapply HB in H. eapply HE. auto.
   + eapply HC in H as H'.  rewrite H'. eapply HF. unfold pdom in *. eapply HB in H. auto. 
Qed.

Lemma st_trans: forall M1 M2 M3,
    st_chain M1 M2 ->
    st_chain M2 M3 ->
    st_chain M1 M3.
Proof.
  intros. destruct H as [[SF1A [SF1B SF1C]] [[SF2A [SF2B SF2C]] [IM1 [IM2 [STV1 STV2]]]]]. 
  destruct H0 as [[SF3A [SF3B SF3C]] [[SF4A [SF4B SF4C]] [IM3 [IM4 [STV3 STV4]]]]]. 
  unfold st_chain, st_chain_partial, st_filter, strel in *.
  intuition.
  - intros ? ?. eapply SF2A in H. eapply SF3A in H. auto.
  - intros ? ?. eapply SF2B in H. eapply SF3B in H. auto.
  - eapply SF4C in H as H'. eapply SF2A in H0 as H0'. 
    intuition. specialize (STV4 l1 l2); intuition. eapply SF2C; eauto. 
  - eapply SF4C in H as H'. eapply SF2B in H0 as H0'.
    intuition. specialize (STV4 l1 l2); intuition. eapply SF2C; eauto. 
  - eapply sst_trans; eauto.
  - eapply sst_trans; eauto.
  - eapply STV1 in H as H'; eauto.  eapply SF2A in H. eapply STV3 in H; eauto. congruence. eapply STV2; intuition. eapply SF1C; eauto. 
  - eapply STV2 in H as H'; eauto.  eapply SF2A in H0. eapply SF2B in H1. eapply STV4; eauto. 
  - eapply STV4 in H as H'; eauto.  eapply SF2A in H0 as H0'. eapply SF2B in H1 as H1'. eapply STV2; eauto.
Qed.  

Lemma sst_trans': forall M1 M2 M3 p,
    sst_chain M1 M2 ->
    psub p (pdom M1) ->
    sst_chain_partial M2 M3 p ->
    sst_chain_partial M1 M3 p.
Proof.
    intros. destruct H as [HA [HB HC]]. destruct H1 as [HD [HE HF]].
    unfold sst_chain_partial. repeat split; auto.
    intros. eapply H0 in H as H'. eapply HC in H'. eapply HF in H. congruence.   
Qed.

Lemma st_trans': forall M1 M2 M3 p1 p2,
    st_chain M1 M2 ->
    psub p1 (st_locs1 M1) ->
    psub p2 (st_locs2 M1) ->
    st_chain_partial M2 M3 p1 p2 ->
    st_chain_partial M1 M3 p1 p2.
Proof. 
  intros. destruct H as [[SF1A [SF1B SF1C]] [[SF2A [SF2B SF2C]] [IM1 [IM2 [STV1 STV2]]]]]. 
  destruct H2 as [[SF3A [SF3B SF3C]] [[SF4A [SF4B SF4C]] [IM3 [IM4 [STV3 STV4]]]]]. 
  unfold st_chain_partial, st_filter. intuition.
  - eapply SF3C; eauto.  eapply STV2; eauto. eapply SF1C in H. eapply H0 in H2. intuition.
  - eapply SF3C; eauto.  eapply STV2; eauto. eapply SF1C in H. eapply H1 in H2. intuition.
  - eapply sst_trans'; eauto.
  - eapply sst_trans'; eauto.
  - specialize (STV3 l1 l2); intuition. eapply H0 in H. eapply H1 in H2.
    specialize (STV1 l1 l2); intuition. specialize (STV2 l1 l2); intuition. congruence. 
  - specialize (STV4 l1 l2); intuition.  eapply H0 in H2. eapply H1 in H3.
    specialize (STV2 l1 l2); intuition.
  - specialize (STV4 l1 l2); intuition.  eapply H0 in H2. eapply H1 in H3.
    specialize (STV2 l1 l2); intuition.
Qed.

Lemma sst_trans'': forall M1 M2 M3 p,
    sst_chain_partial M1 M2 p ->
    sst_chain_partial M2 M3 p  ->
    psub p (pdom M1) ->
    sst_chain_partial M1 M3 p.
Proof. 
  intros. destruct H as [HA [HB HC]]. destruct H0 as [HD [HE HF]].
  unfold sst_chain_partial. intuition.
  eapply HC in H as H'. eapply HF in H. congruence.
Qed.

Lemma sst_trans''': forall M1 M2 M3 p p',
    sst_chain_partial M1 M2 p ->
    sst_chain_partial M2 M3 p'  ->
    psub p (pdom M1) ->
    psub p p' ->
    sst_chain_partial M1 M3 p.
Proof. 
  intros. destruct H as [HA [HB HC]]. destruct H0 as [HD [HE HF]].
  unfold sst_chain_partial. intuition.
  intros ? ?. eapply H2 in H. eapply HE; eauto.
  assert (p' l). { eapply H2; eauto. }
  eapply HC in H as H'. eapply HF in H0. congruence.
Qed.


Lemma st_trans'': forall M1 M2 M3 p1 p2,
    st_chain_partial M1 M2 p1 p2 ->
    st_chain_partial M2 M3 p1 p2 ->
    psub p1 (st_locs1 M1) ->
    psub p2 (st_locs2 M1) ->
    st_chain_partial M1 M3 p1 p2.
Proof.   
  intros. intros. destruct H as [[SF1A [SF1B SF1C]] [[SF2A [SF2B SF2C]] [IM1 [IM2 [STV1 STV2]]]]]. 
  destruct H0 as [[SF3A [SF3B SF3C]] [[SF4A [SF4B SF4C]] [IM3 [IM4 [STV3 STV4]]]]]. 
  unfold st_chain_partial, st_filter in *.
  intuition.
  - eapply sst_trans''; eauto. 
  - eapply sst_trans''; eauto. 
  - rewrite <- STV3; auto. eapply STV2; eauto.
  - rewrite <- STV4; auto. eapply STV2; eauto.
  - rewrite STV2; eauto. eapply STV4; eauto.
Qed.

Lemma sstchain_symmetry: forall M1 M2 p,
  sst_chain_partial M1 M2 p ->
  sst_chain_partial M2 M1 p.
Proof.
  intros. destruct H as [? [? ?]].
  repeat split; auto.
  intros ? ?. eapply H1 in H2. congruence.
Qed.

Lemma sstchain_tighten: forall M1 M2 q p,
    sst_chain_partial M1 M2 p ->
    psub q p  ->
    sst_chain_partial M1 M2 q.
Proof.
  intros. destruct H as [A [B C]].
  unfold sst_chain_partial; repeat split; auto.
  intros ? ?. eapply H0 in H. eapply A in H. auto.
  intros ? ?. eapply H0 in H. eapply B in H. auto.
Qed.

Lemma stchain_tighten: forall M1 M2 p1 p2 p1' p2',
    st_filter M1 p1' p2' ->
    st_chain_partial M1 M2 p1 p2 ->
    psub p1' p1 ->
    psub p2' p2 -> 
    st_chain_partial M1 M2 p1' p2'.
Proof.  
  intros. destruct H as [SF1A [SF1B SF1C]]. 
  destruct H0 as [[SF3A [SF3B SF3C]] [[SF4A [SF4B SF4C]] [IM3 [IM4 [STV3 STV4]]]]]. 
  unfold st_chain_partial, st_filter in *. intuition.
  - intros ? ?. eapply H1 in H. eapply SF4A. auto.
  - intros ? ?. eapply H2 in H. eapply SF4B. auto.
  - eapply SF1C; eauto. eapply STV4; eauto. eapply H1 in H0. intuition. eapply SF4C; eauto.
  - eapply SF1C; eauto. eapply STV4; eauto. eapply H2 in H0. intuition. eapply SF4C; eauto.
  - eapply sstchain_tighten; eauto.
  - eapply sstchain_tighten; eauto.
  - eapply STV4; eauto.
  - eapply STV4; eauto.
Qed.

Lemma stchain_extend: forall M1 vt q1 q2,
    st_filter M1 (st_locs1 M1) (st_locs2 M1) -> 
    st_chain M1 (st_extend M1 vt q1 q2).
Proof.
  intros. unfold st_extend, st_chain, st_chain_partial, st_filter, sst_chain_partial, strel, st_locs1, st_locs2, pnat, length1, length2, pdom in *. 
  simpl. intuition.
  intros ? ?. eauto.
  intros ? ?. eauto.
  eapply H2; eauto.
  eapply H2; eauto.
  intros ? ?. lia.
  bdestruct (l =? (length (st1 M1))); intuition.
  intros ? ?. lia.
  bdestruct (l =? (length (st2 M1))); intuition.
  eapply functional_extensionality. intros. eapply functional_extensionality. intros.
  eapply propositional_extensionality. split; intros.
  right. exists (st_valtype M1 l1 l2); intuition.
  destruct H5 as [[? ?] | [? [? [? [? ?]]]]]. lia.
  subst x1. auto. 
Qed.

Lemma strel_mono: forall M M' i i0,
  st_chain M M' ->
  st_locs1 M i ->
  st_locs2 M i0 ->
  strel M i i0 ->
  strel M' i i0.
Proof.
  intros. unfold st_chain, st_chain_partial, st_filter in H.
  intuition.
  eapply H12; intuition.
Qed.

Lemma strel_wf: forall S1 S2 M l1 l2,
  store_type S1 S2 M ->
  strel M l1 l2 ->
  (l1 < length1 M /\ l2 < length2 M).
Proof.
  intros. destruct H as [? [? [A [? ?]]]].
  destruct (A l1 l2) as [vt [qt1 [qt2 [v1 [v2 [IM1 [IM2 [IS1 [IS2 ?]]]]]]]]]. auto.
  apply indexr_var_some' in IM1, IM2. 
  unfold length1, length2. intuition.
Qed.


(* location saturation lemmas *)

Lemma lls_mono: forall M q q',
    psub q q' ->
    psub (locs_locs_stty M q) (locs_locs_stty M q').
Proof.
  intros. intros ? ?. inversion H0; subst. left. eapply H in H1. auto.
  eapply lls_s; eauto. 
Qed.

Lemma lls_indexr_closed': forall S M l qt ,
    sstore_type S M ->
    indexr l M = Some qt ->
    psub (plift qt) (pnat l).
Proof.
  intros. destruct H as (L & SST).
  intros ? ?.
  assert (l < length S). rewrite L. eapply indexr_var_some'. eauto.
  destruct (SST l) as (qt' & v  & ? & ? & ? & ?). auto.
  rewrite H2 in H0. inversion H0. subst qt'.
  unfold pnat. eapply H5 in H. unfold pnat in H. auto.
Qed.

Lemma lt_stlocs: forall{X} (M:list X) i x,
    pnat i x -> i <= length M ->
    (pnat (length M)) x.
Proof.
  intros. unfold pnat in *. lia.
Qed.

Lemma lt_stlocs': forall{X} (M: list X) i,
    i <= length M ->
    psub (pnat i) (pnat (length M)).
Proof.
  intros. intros ? ?. unfold pnat in *. lia.
Qed.


Lemma lls_closed: forall M S q1,
    sstore_type S M ->
    psub (locs_locs_stty M q1) (por q1 (pnat (length M))).
Proof.
  intros. intros ? ?. induction H0; intros; subst.
  - left. eauto.
  - right. destruct IHlocs_locs_stty. eauto.
    destruct H.
    assert (x1 < length M). eapply indexr_var_some'. eauto. 
    destruct (H4 x1) as (qt' & v & ? & ? & ? & ? ); eauto. 
    intuition. 
    eapply lt_stlocs. eapply H9. congruence. lia.
    eauto. 
Qed.


Lemma lls_closed': forall M S q1,
    sstore_type S M ->
    psub q1 (pnat (length M)) -> 
    psub (locs_locs_stty M q1) (pnat (length M)).
Proof.
  intros. intros ? ?.
  eapply lls_closed in H1; eauto.
  destruct H1; eauto. 
Qed.


Lemma lls_indexr_closed'': forall M S qt x1,
    sstore_type S M ->
    indexr x1 M = Some qt ->
    psub (locs_locs_stty M (plift qt)) (pnat x1).
Proof.
  intros. intros ? ?.
  remember (plift qt) as qt'.
  generalize dependent qt.
  generalize dependent x1.

  induction H1; intros; subst.
  - eapply lls_indexr_closed'; eauto. 
  - eapply IHlocs_locs_stty in H1; eauto. 
    destruct H. destruct (H4 x0) as (? & ? & ? & ? & ? & ?). { eapply indexr_var_some' in H3. lia. }
    rewrite H3 in H5. inversion H5. subst.
    eapply H8 in H0. 
    unfold pnat in *. lia.
Qed.

Lemma lls_empty: forall M, 
  locs_locs_stty M pempty = pempty.
Proof.
  intros. eapply functional_extensionality;
  intros; eapply propositional_extensionality; split.
  intros. inversion H. auto. unfold pempty in H0. contradiction.
  intros. unfold pempty in H. contradiction.
Qed.

Lemma lls_indexr_closed''': forall M S qt x1,
    sstore_type S M ->
    indexr x1 M = Some qt ->
    psub (locs_locs_stty M (plift qt)) (pnat (length M)).
Proof.
  intros. intros ? ?. 
  eapply lt_stlocs. eapply lls_indexr_closed''; eauto. eapply indexr_var_some' in H0. lia. 
Qed.



Lemma lls_shrink: forall S M v a q1 x,
    sstore_type (v::S) (a::M) ->
    locs_locs_stty (a::M) q1 x ->
    psub q1 (pnat (length M)) ->
    locs_locs_stty M q1 x.
Proof.
  intros. remember (a::M) as M0.
  generalize dependent H1. generalize dependent H.
  induction H0; intros; subst.
  - eapply lls_z. eauto.
  - assert (x1 < length M). eapply H3 in H. unfold pnat in H. specialize (H3 x1); intuition.
    rewrite indexr_skip in H0; intuition. 
    assert (psub (plift qt) (pnat x1)). eapply lls_indexr_closed'; eauto.
    rewrite indexr_skip. eauto. lia. 
    eapply lls_s; eauto. eapply H6. intros ? ?. eapply H5 in H7. unfold pnat in H7. specialize (H3 x1); intuition. 
    unfold pnat in *. lia.
Qed.

Lemma lls_shrink': forall S M a q1 x,
    sstore_type S M ->
    locs_locs_stty (a::M) q1 x ->
    psub q1 (pnat (length M)) ->
    locs_locs_stty M q1 x.
Proof.
  intros. remember (a::M) as M0.
  generalize dependent H1. generalize dependent H.
  induction H0; intros; subst.
  - eapply lls_z. eauto.
  - assert (x1 < length M). eapply H3 in H. unfold pnat in H. auto.
    rewrite indexr_skip in H0; intuition. 
    assert (psub (plift qt) (pnat x1)). eapply lls_indexr_closed'; eauto. 
    eapply lls_s; eauto. eapply H6. intros ? ?. eapply H5 in H7. unfold pnat in *. lia.
Qed.


Lemma lls_extend: forall  M a q1 x,
    locs_locs_stty M q1 x ->
    locs_locs_stty (a::M) q1 x.    
Proof.
  intros. remember (a::M) as M1.
  induction H; intros; subst.
  - eapply lls_z. eauto.
  - eapply indexr_extend1 in H0. 
    eapply lls_s. eauto. eapply H0. 
    eapply IHlocs_locs_stty. eauto. 
Qed.

Lemma val_lls: forall v l M,
  val_locs v l ->
  locs_locs_stty M (val_locs v) l.
Proof.
  intros. left. auto.
Qed.

Lemma lls_vars: forall (M :st) E q l,
    locs_locs_stty M (vars_locs E q) l ->
    exists x, q x /\ locs_locs_stty M (var_locs E x) l.
Proof.
  intros. remember (vars_locs E q) as Q.
  generalize dependent E.
  generalize dependent q.
  induction H; intros; subst.
  - destruct H. exists x0. intuition eauto using lls_z.
  - destruct H. exists x0. intuition eauto using lls_s.
Qed.

Lemma lls_vars': forall M E (q: pl) x l,
    locs_locs_stty M (var_locs E x) l ->
    q x ->
    locs_locs_stty M (vars_locs E q) l.
Proof.
  intros. remember (var_locs E x) as Q.
  generalize dependent E.
  generalize dependent q.
  generalize dependent x.
  induction H; intros; subst.
  - eapply lls_z. exists x0. intuition. 
  - eapply lls_s. exists x0. intuition. eauto. eauto. eauto. 
Qed.

Lemma lls_var: forall M E x l,
    locs_locs_stty M (var_locs E x) l ->
    exists vx, indexr x E = Some vx /\ locs_locs_stty M (val_locs vx) l.
Proof.
  intros. remember (var_locs E x) as Q.
  generalize dependent E.
  generalize dependent x.
  induction H; intros; subst.
  - destruct H. exists x1. intuition eauto using lls_z.
  - destruct H. exists x2. intuition eauto using lls_s.
Qed.

Lemma lls_var': forall M E vx x l,
    indexr x E = Some vx ->
    locs_locs_stty M (val_locs vx) l ->
    locs_locs_stty M (var_locs E x) l.
Proof.
  intros. remember (val_locs vx) as Q.
  generalize dependent E.
  generalize dependent x.
  induction H0; intros; subst.
  - eapply lls_z. exists vx. eauto. 
  - eapply lls_s. exists vx. intuition. eauto. eauto. eauto. 
Qed.


Lemma lls_qt: forall l S M v qt
  (IS: indexr l S = Some v)
  (IM: indexr l M = Some qt) 
  (ST: sstore_type S M), 
  psub (locs_locs_stty M (val_locs v)) (locs_locs_stty M (plift qt)).
Proof.
  intros. destruct v. 
  - rewrite val_locs_bool. rewrite lls_empty. intros ? ?. inversion H.
  - rewrite val_locs_ref. bdestruct (i =? l).
    + subst. 
      remember ST as ST'. clear HeqST'.
      destruct ST as [? ?]. apply indexr_var_some' in IS as IS'. destruct (H0 l) as [qt' [v [IM' [IS'' [P1 P2]]]]]. auto.
      rewrite IS'' in IS. inversion IS. rewrite IM' in IM. inversion IM. subst v. subst qt'. rewrite val_locs_ref in P1. auto.
    + remember ST as ST'. clear HeqST'.
      destruct ST as [? ?]. apply indexr_var_some' in IS as IS'. destruct (H1 l) as [qt' [v [IM' [IS'' [P1 P2]]]]]. auto.
      rewrite IS'' in IS. inversion IS. rewrite IM' in IM. inversion IM. subst v. subst qt'. rewrite val_locs_ref in P1. auto.
  - remember (vabs l0 q t) as vf. 
    remember ST as ST'. clear HeqST'.
    destruct ST as [? ?]. apply indexr_var_some' in IS as IS'. destruct (H0 l) as [qt' [v [IM' [IS'' [P1 P2]]]]]. auto.
    rewrite IS'' in IS. inversion IS. rewrite IM' in IM. inversion IM. subst v. subst qt'.  auto.
Qed.

Lemma lls_qt': forall M S1 l qt, 
  sstore_type S1 M ->  
  indexr l M = Some qt ->
  psub (locs_locs_stty M (plift qt)) (locs_locs_stty M (pone l)).
Proof.   
  intros. intros ? ?. eapply lls_indexr_closed'' in H0 as H0'; eauto.
  inversion H1; subst.
  + eapply lls_s; eauto. unfoldq; intuition.
  + eapply lls_indexr_closed'' in H3; eauto.  eapply lls_s; eauto. unfoldq; intuition.
Qed.


Lemma lls_filter: forall M p l, 
  locs_locs_stty M p l ->
  psub (locs_locs_stty M (pone l)) (locs_locs_stty M p).
Proof.
  intros. induction H; intros ??. inversion H0; subst; inversion H1; subst.
  eapply lls_z; eauto. eapply lls_s; eauto. eapply lls_s; eauto.
Qed.

Lemma val_reach_p: forall l S M v qt H p,
  locs_locs_stty M (vars_locs H p) l ->
  indexr l S = Some v ->
  indexr l M = Some qt -> 
  sstore_type S M -> 
  psub (locs_locs_stty M (val_locs v)) (locs_locs_stty M ((vars_locs H p))).
Proof.
  intros. eapply lls_filter in H0 as H0'; eauto. eapply lls_qt' in H2 as H2'; eauto.
  intros ? ?. eapply lls_qt in H2; eauto.
Qed.

Lemma lls_reach_trans: forall M p l x,
  locs_locs_stty M p l ->
  psub (locs_locs_stty M (pone x)) (locs_locs_stty M (pone l)) ->
  psub (locs_locs_stty M (pone x)) (locs_locs_stty M p).
Proof.
  intros. intros ? ?. eapply H0 in H1. 
  induction H; subst. inversion H1; subst. inversion H1; subst.
  unfold pone in H2, H3. subst x0. left. auto.
  unfold pone in H2, H3. subst x0. subst x3. left. auto.
  unfold pone in H2. subst x3. eapply lls_s; eauto.
  intuition. eapply lls_s; eauto.
Qed.

Lemma val_reach_wf: forall l S M v x,
  indexr l S = Some v ->
  sstore_type S M ->
  locs_locs_stty M (val_locs v) x ->
  pdom M x.
Proof.
  intros. destruct v. 
  - rewrite val_locs_bool in H1. rewrite lls_empty in H1. unfoldq; intuition. 
  - rewrite val_locs_ref in H1. inversion H1;subst. 
    + unfoldq; intuition. subst. 
      remember H0 as H0'. clear HeqH0'.
      destruct H0 as [? ?]. apply indexr_var_some' in H as H'. destruct (H2 l) as [qt [v [IM [IS [P1 P2]]]]]. auto.
      rewrite H in IS. inversion IS. subst v. eapply lls_indexr_closed'' in IM; eauto. rewrite val_locs_ref in P1.  
      assert (psub (locs_locs_stty M(pone i))(pnat l)). { intros ? ?. eapply P1 in H3. eapply IM in H3. auto. }
      specialize (H3 i). intuition. unfoldq; intuition.
    + subst. unfoldq; intuition. subst. remember H0 as H0'. clear HeqH0'.
      destruct H0 as [? ?]. apply indexr_var_some' in H3 as H3'. rewrite <- H0 in H3'. destruct (H2 i) as [qt' [v' [IM' [IS' [P1 P2]]]]]. auto.
      rewrite H3 in IM'. inversion IM'. subst qt'. eapply lls_indexr_closed'' in H3; eauto. eapply H3 in H4. unfoldq; intuition.
  - remember (vabs l0 q t) as vf. inversion H1; subst. 
    + remember H0 as H0'. clear HeqH0'.
      destruct H0 as [? ?]. apply indexr_var_some' in H as H'. destruct (H3 l) as [qt [v [IM [IS [P1 P2]]]]]. auto.
      rewrite H in IS. inversion IS. rewrite H5 in *. eapply lls_indexr_closed'' in IM; eauto. 
      assert (psub (locs_locs_stty M((val_locs v)))(pnat l)). { intros ? ?. eapply P1 in H4. eapply IM in H4. auto. }
      specialize (H4 x). intuition. unfoldq; intuition.
    + remember H0 as H0'. clear HeqH0'.
      destruct H0 as [? ?]. apply indexr_var_some' in H3 as H3'. rewrite <- H0 in H3'. destruct (H5 x1) as [qt' [v' [IM' [IS' [P1 P2]]]]]. auto.
      rewrite H3 in IM'. inversion IM'. subst qt'. eapply lls_indexr_closed'' in H3; eauto. eapply H3 in H4. unfoldq; intuition.
Qed.


Lemma lls_change: forall M M' q,
    sst_chain_partial M M' (locs_locs_stty M q) ->
    locs_locs_stty M q = locs_locs_stty M' q.
Proof.
  intros. eapply functional_extensionality.
  intros. eapply propositional_extensionality.
  split; intros.
  - induction H0. left. eauto.
    eapply lls_s. eauto. destruct H. destruct a. rewrite <-e. eauto.
    eapply lls_z. eauto.
    eapply IHlocs_locs_stty.
    destruct H. destruct H3.
    split. intros ? ?. eapply H. eapply lls_s. eauto. eauto. eauto.
    split. intros ? ?. eapply H3. eapply lls_s. eauto. eauto. eauto.
    intros. eapply H4. eapply lls_s. eauto. eauto. eauto. 
  - induction H0. left. eauto.
    eapply lls_s. eauto. destruct H. destruct a. rewrite e. eauto.
    eapply lls_z. eauto.
    eapply IHlocs_locs_stty.
    destruct H. destruct H3.
    rewrite <-H4 in H1.
    split. intros ? ?. eapply H. eapply lls_s. eauto. eauto. eauto.
    split. intros ? ?. eapply H3. eapply lls_s. eauto. eauto. eauto.
    intros. eapply H4. eapply lls_s. eauto. eauto. eauto.
    left. eauto.
Qed.

  


Lemma lls_change1X: forall M M' q1 p1 p2 l1
    (SCP: st_chain_partial M M' p1 p2),
    psub (pand (locs_locs_stty (st1 M) q1) (locs_locs_stty (st1 M') q1)) p1 ->
    locs_locs_stty (st1 M) q1 l1 -> locs_locs_stty (st1 M') q1 l1.
Proof.
  intros. 
  remember (st1 M).
  induction H0. left. eauto.
  subst M0.
  eapply lls_s. eauto.
  destruct SCP as (F1 & F2 & (Z3A & Z3B & Z3C) & Z4 & Z5).
  rewrite <-Z3C. eauto. eapply H.
  split. eapply lls_z. eauto.
  eapply lls_z. eauto. 
  eapply IHlocs_locs_stty. eauto.
  intros ? Q. eapply H. 
  destruct Q.
  split. eapply lls_s. eauto. eauto. eauto.
  eapply lls_s. eauto.
  destruct SCP as (F1 & F2 & (Z3A & Z3B & Z3C) & Z4 & Z5).
  rewrite <-Z3C. eauto. 2: eauto.
  eapply H. split. eapply lls_z. eauto. eapply lls_z. eauto. 
Qed.

Lemma lls_change1: forall M M' q1 q2
    (SCP: st_chain_partial M M' (locs_locs_stty (st1 M) q1) (locs_locs_stty (st2 M) q2)),
    locs_locs_stty (st1 M) q1 = locs_locs_stty (st1 M') q1.
Proof.
  intros. eapply functional_extensionality;
  intros; eapply propositional_extensionality.
  split. 
  eapply lls_change1X. eauto. intros ? Q. eapply Q. 
  eapply lls_change1X. eapply stchain_symmetry. eauto. intros ? Q. eapply Q. 
Qed.


Lemma lls_change2X: forall M M' q2 p1 p2 l1
    (SCP: st_chain_partial M M' p1 p2),
    psub (pand (locs_locs_stty (st2 M) q2) (locs_locs_stty (st2 M') q2)) p2 ->
    locs_locs_stty (st2 M) q2 l1 -> locs_locs_stty (st2 M') q2 l1.
Proof.
  intros. 
  remember (st2 M).
  induction H0. left. eauto.
  destruct SCP as (F1 & F2 & Z3 & (Z4A & Z4B & Z4C) & Z5).
  subst M0.
  eapply lls_s. eauto.
  rewrite <-Z4C. eauto. eapply H.
  split. eapply lls_z. eauto.
  eapply lls_z. eauto. 
  eapply IHlocs_locs_stty. eauto.
  intros ? Q. eapply H. 
  destruct Q.
  split. eapply lls_s. eauto. eauto. eauto.
  eapply lls_s. eauto.
  rewrite <-Z4C. eauto. 2: eauto.
  eapply H. split. eapply lls_z. eauto. eapply lls_z. eauto. 
Qed.


Lemma lls_change2: forall M M' q1 q2
    (SCP: st_chain_partial M M' (locs_locs_stty (st1 M) q1) (locs_locs_stty (st2 M) q2)),
    locs_locs_stty (st2 M) q2 = locs_locs_stty (st2 M') q2.
Proof.
  intros.  eapply functional_extensionality;
  intros; eapply propositional_extensionality.
  split. 
  eapply lls_change2X. eauto. intros ? Q. eapply Q. 
  eapply lls_change2X. eapply stchain_symmetry. eauto. intros ? Q. eapply Q. 
Qed.


(* ---------- val_type lemmas  ---------- *)

Lemma valt_wf: forall T T' M H1 H2 v1 v2,
    val_type M H1 H2 v1 v2 T T' ->
    ( psub (val_locs v1) (pnat (length1 M)) /\
      psub (val_locs v2) (pnat (length2 M))).
Proof. 
  intros T. induction T; intros; destruct T'; destruct v1; destruct v2; simpl in *; intuition.
  + rewrite val_locs_bool. auto. unfoldq. intuition.
  + rewrite val_locs_bool. auto. unfoldq. intuition.
  + rewrite val_locs_ref. unfoldq. intuition. subst i. eapply H8. left. rewrite val_locs_ref. unfoldq; intuition.
  + rewrite val_locs_ref. unfoldq. intuition. subst i0. eapply H8. left. rewrite val_locs_ref. unfoldq; intuition.
  + intros ? ?. eapply H9. left. auto.
  + intros ? ?. eapply H9. left. auto.
Qed.

Lemma valt_deep_wf: forall T T' M H1 H2 v1 v2,
    val_type M H1 H2 v1 v2 T T' ->
    ( psub (locs_locs_stty (st1 M) (val_locs v1)) (st_locs1 M) /\
      psub (locs_locs_stty (st2 M) (val_locs v2)) (st_locs2 M)). 
Proof.
  intros T. induction T; intros; destruct T'; destruct v1; destruct v2; simpl in *; intuition.
  + rewrite val_locs_bool. intros ? ?. inversion H0; subst. unfoldq. intuition. unfoldq. intuition.
  + rewrite val_locs_bool. intros ? ?. inversion H0; subst. unfoldq. intuition. unfoldq. intuition.
  + eapply H8.
  + eapply H8.
  + eapply H9; eauto.
  + eapply H9; eauto.
Qed.


Lemma indexr_filter: forall S1 S2 M  qt1 qt2 i i0
  (ST: store_type S1 S2 M)
  (SF: st_filter M (locs_locs_stty (st1 M) (pone i)) (locs_locs_stty (st2 M) (pone i0)))
  (IX1: indexr i (st1 M) = Some qt1)
  (IX2: indexr i0 (st2 M) = Some qt2),
  strel M i i0 ->
  st_filter M (locs_locs_stty (st1 M) (plift qt1)) (locs_locs_stty (st2 M)(plift qt2)).
Proof.
  intros. destruct ST as [SST1 [SST2 [ST [U2 U1]]]]. split. 2: split. 
  + intros ? ?. eapply SF. eapply lls_s; eauto. unfoldq; intuition.
  + intros ? ?. eapply SF. eapply lls_s; eauto. unfoldq; intuition.
  + intros. destruct SF as (? & ? & ?). eapply H3 in H0 as HV.
      split.
      - intros. eapply lls_s in H4 as HU. 3: eapply IX1. eapply HV in HU. 2: intuition.
        inversion HU.
          * subst. inversion H5. subst l2.
            assert (i = l1). eapply U1; eauto.
            subst i. 
            assert (pnat l1 l1). eapply lls_indexr_closed''. eapply SST1. eauto. eauto.
            unfold pnat in H6. lia. 
          * subst. inversion H5. subst x1. rewrite IX2 in H6. inversion H6. subst. eauto.
        - (* symmetric *)
          intros. eapply lls_s in H4 as HU. 3: eapply IX2. eapply HV in HU. 2: intuition.
          inversion HU.
          * subst. inversion H5. subst l1.
            assert (i0 = l2). eapply U2; eauto.
            subst i0. 
            assert (pnat l2 l2). eapply lls_indexr_closed''. eapply SST2. eauto. eauto.
            unfold pnat in H6. lia. 
          * subst. inversion H5. subst x1. rewrite IX1 in H6. inversion H6. subst. eauto.
Qed.
  

Lemma valt_store_change: forall T T' M' M S1 S2 H1 H2 v1 v2
    (ST: store_type S1 S2 M),
    val_type M H1 H2 v1 v2 T T' ->
    st_chain_partial M M' (locs_locs_stty (st1 M) (val_locs v1)) (locs_locs_stty (st2 M) (val_locs v2)) ->
    val_type M' H1 H2 v1 v2 T T'.
Proof. 
  intros T. induction T; intros; destruct T'; destruct v1; destruct v2; simpl in *; intuition.
  + eapply H0; eauto. split; left; rewrite val_locs_ref; unfoldq; intuition.
  + repeat rewrite val_locs_ref in *. split. 2: split. 
    * intros ? ?. eapply H0; eauto. erewrite lls_change. eauto. eapply stchain_tighten. eauto. eauto. unfoldq; intuition. unfoldq; intuition.
    * intros ? ?. eapply H0; eauto. erewrite lls_change. eauto. eapply stchain_tighten. eauto. eauto. unfoldq; intuition. unfoldq; intuition.
    * intros ? ? ?. split; intros.
      rewrite <- lls_change with (M := (st1 M)) in H12. rewrite <- lls_change with (M := st2 M).
      intuition. eapply H0; eauto. eapply H0; eauto. eapply H0; eauto.
      rewrite <- lls_change with (M := (st2 M)) in H12. rewrite <- lls_change with (M := st1 M).
      intuition. eapply H0; eauto. eapply H0; eauto. eapply H0; eauto.
  + repeat rewrite val_locs_ref in *.
    remember H0 as SC1. clear HeqSC1. 
    destruct H0 as (? & ? & (? & ? & ?) & (? & ? & ?) & ? & ?).
    destruct H11 as [vt [qt1 [qt2 [IX1 [IX2 [ST_VT [VT [QT1 [QT2 [QT3 QT4]]]]]]]]]].
    assert (st_chain_partial M M' (locs_locs_stty (st1 M) (plift qt1)) (locs_locs_stty (st2 M) (plift qt2))). {
      eapply stchain_tighten. eapply indexr_filter; eauto. eauto. eauto. eauto. }
    
    exists vt, qt1, qt2.
    split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 
    * rewrite <-H14. eauto. left. intuition.
    * rewrite <- H17. auto. left. intuition.
    * rewrite H18 in ST_VT; eauto. left. unfoldq; intuition. left. unfoldq; intuition.
    * intros M'' S1'' S2''. intros. 
      eapply VT. eapply st_trans''; eauto. erewrite lls_change1. erewrite lls_change2. eauto. eauto. eauto. 
      eapply H11. eapply H11. eauto. auto. auto. auto.
    * auto.
    * auto.
    * erewrite <- lls_change1; eauto. intros ? ?. erewrite <- lls_change1.  eauto. eauto. 
    * erewrite <- lls_change2; eauto. intros ? ?. erewrite <- lls_change2.  eauto. eauto. 
  + { split. 2: split.
      * erewrite <- lls_change1; eauto. eapply H0.
      * erewrite <- lls_change2; eauto. eapply H0.
      * intros. split; intros.
        ** erewrite <- lls_change1 in H13; eauto.
           erewrite <- lls_change2; eauto.
           destruct H0 as (? & (? & ? & ?) & ? & ? & ?). 
           eapply H16 in H11 as A. intuition.
        ** erewrite <- lls_change2 in H13; eauto.
           erewrite <- lls_change1; eauto.
           destruct H0 as (? & (? & ? & ?) & ? & ? & ?). 
           eapply H16 in H11 as A. intuition.
    }  
  + eapply H12; auto. 
    eapply st_trans''; eauto. erewrite lls_change1. erewrite lls_change2. eauto. eauto. eauto.
    eapply H10. eapply H10.
Qed.

Lemma valt_filter: forall T T' v1 v2 M H1 H2 ,
  val_type M H1 H2 v1 v2 T T' ->
  st_filter M (locs_locs_stty (st1 M) (val_locs v1)) (locs_locs_stty (st2 M) (val_locs v2)).
Proof. 
  intros T. induction T; intros; destruct T'; destruct v1; destruct v2; unfold st_filter; simpl in *; intuition.
  + repeat rewrite val_locs_bool. rewrite lls_empty. unfoldq; intuition.
  + repeat rewrite val_locs_bool. rewrite lls_empty. unfoldq; intuition.
  + repeat rewrite val_locs_bool in *. rewrite lls_empty in  *. unfoldq; intuition.
  + repeat rewrite val_locs_bool in *. rewrite lls_empty in  *. unfoldq; intuition.
  + eapply H8; eauto.
  + eapply H8; eauto.
  + eapply H8; eauto.
  + eapply H8; eauto.
  + eapply H9; eauto.
  + eapply H9; eauto.
  + eapply H9; eauto.
  + eapply H9; eauto.
Qed.


Lemma valt_store_extend: forall T T' M' M S1 S2 H1 H2 v1 v2
    (ST: store_type S1 S2 M),  
    val_type M H1 H2 v1 v2 T T' ->
    st_chain M M' ->
    val_type M' H1 H2 v1 v2 T T'.
Proof. 
  intros. remember H0 as SC. clear HeqSC.  
  destruct SC as (SC1 & SC2 & SC3).
  unfold st_chain in H0.
  eapply valt_store_change; eauto.
  eapply stchain_tighten. eapply valt_filter in H. eauto. eauto.
  eapply valt_deep_wf. eauto.
  eapply valt_deep_wf. eauto.
Qed.

Lemma valt_extend: forall T T' M H1' H1 H2' H2 v1 v2,
    closed_ty (length H1) T ->
    closed_ty (length H2) T' ->
    val_type M (H1'++H1) (H2'++H2) v1 v2 T T' <-> 
    val_type M H1 H2 v1 v2 T T'.
Proof. 
  intros T. induction T; intros; destruct T'; split; intros; destruct v1; destruct v2; simpl in *; intuition.
  - inversion H. auto. 
  - inversion H0. auto.
  - inversion H. auto.
  - inversion H0. auto.
  - destruct H12 as [vt [qt1 [qt2 [IX1 [IX2 [STVT [ST [VT [? [? ?]]]]]]]]]].
    exists vt, qt1, qt2; intuition. 
    edestruct (ST M' S1' S2'); eauto. intuition.
    eapply IHT; eauto. inversion H; intuition. inversion H0; intuition.
    edestruct (ST M' S1' S2'); eauto. intuition.
    eapply IHT in H19; eauto. inversion H; intuition. inversion H0; intuition.
    erewrite <- vars_locs_extend; eauto. inversion H; intuition.
    erewrite <- vars_locs_extend; eauto. inversion H0; intuition.
  - eapply closedty_extend; eauto.
  - eapply closedty_extend; eauto.
  - intros ? ?. eapply H7 in H11. unfoldq; intuition. rewrite app_length. lia.
  - intros ? ?. eapply H8 in H11. unfoldq; intuition. rewrite app_length. lia.
  - destruct H12 as [vt [qt1 [qt2 [IX1 [IX2 [STVT [ST [VT [? [? ?]]]]]]]]]].
    exists vt, qt1, qt2; intuition. 
    specialize (ST M' S1' S2'); intuition. specialize (H21 v1' v2'); intuition.
    eapply IHT; eauto.
    edestruct (ST M' S1' S2'); eauto. intuition. 
    erewrite IHT in H19; eauto. 
    erewrite vars_locs_extend; eauto. 
    erewrite vars_locs_extend; eauto. 
  - inversion H. auto.
  - inversion H. auto.
  - inversion H. auto.
  - inversion H. auto.
  - inversion H0. auto.
  - inversion H0. auto.
  - inversion H0. auto.
  - inversion H0. auto.
  - (* Abs shrink *)
    inversion H0. subst. inversion H. subst.
    destruct (H13 S1' S2' M' vx1 vx2) as [S1'' [S2'' [M'' [vy1 [vy2 [HEY HVY]]]]]].
      eauto.
      eauto.
      eauto.
      eapply IHT1; eauto.
      rewrite vars_locs_extend; eauto. 
      rewrite vars_locs_extend; eauto. 
    
    exists S1'', S2'', M'', vy1, vy2. intuition.
    eapply IHT2; eauto.
    rewrite vars_locs_extend in H28; eauto.
    rewrite vars_locs_extend in H33; eauto.  
  - eapply closedty_extend. apply H4. auto.
  - unfoldq. rewrite app_length. intuition. eapply H3 in H12. lia.
  - eapply closedty_extend. apply H5. auto.
  - unfoldq. rewrite app_length. intuition. eapply H6 in H12. lia.
  - eapply closedty_extend; eauto. 
  - unfoldq. rewrite app_length. intuition. eapply H8 in H12. lia.
  - eapply closedty_extend; eauto.
  - unfoldq. rewrite app_length. intuition. eapply H10 in H12. lia.
  - (* Abs grow *)
    inversion H0. subst.
    destruct (H13 S1' S2' M' vx1 vx2) as [S1'' [S2'' [M'' [vy1 [vy2 [HEY [HVY]]]]]]].
      eauto.
      eauto.
      eauto.
      eapply IHT1; eauto.
      rewrite vars_locs_extend in H17; eauto. 
      rewrite vars_locs_extend in H18; eauto. 
    
    exists S1'',S2'', M'', vy1, vy2. intuition.
    eapply IHT2; eauto.
    rewrite vars_locs_extend; eauto. 
    rewrite vars_locs_extend; eauto.
Qed.

Lemma valt_extend1: forall T T' M H1 H2 v1 v2 vx1 vx2,
    closed_ty (length H1) T ->
    closed_ty (length H2) T' ->
    val_type M (vx1::H1)(vx2::H2) v1 v2 T T'<-> 
    val_type M H1 H2 v1 v2 T T'.
Proof.
  intros. 
  replace (vx1 :: H1)  with ([vx1]  ++ H1); auto.
  replace (vx2 :: H2)  with ([vx2]  ++ H2); auto.
  eapply valt_extend; eauto.
Qed.


Lemma valt_same_locs_deep: forall  M H1 H2 v1 v2 T T' l1 l2,
    val_type M H1 H2 v1 v2 T T' ->
    strel M l1 l2 ->
    locs_locs_stty (st1 M) (val_locs v1) l1 <-> locs_locs_stty (st2 M) (val_locs v2) l2.
Proof.
  intros.
  destruct T; destruct T'; destruct v1; destruct v2; simpl in H; try contradiction; eauto.
  - repeat rewrite val_locs_bool. repeat rewrite lls_empty. intuition.
  - destruct H as (? & ? & ? & ? & ? & ? & ? & ? & ? & ?). 
    eapply H9. auto.
  - destruct H as (? & ? & ? & ? & ? & ? & ? & ? & ? & ?).   
    eapply H10. auto.
Qed.


(* ---------- val_qual lemmas  ---------- *)

Lemma valq_bool: forall M M1 H b q,
    val_qual M M1 H (vbool b) false q.
Proof.
  intros. unfoldq. rewrite val_locs_bool. intuition.
  inversion H0. subst. destruct H1. subst. destruct H1.
Qed.


Lemma valq_abs: forall M M' H t p fr q,
    val_qual M M' H (vabs H (qand p q) t) fr (pand (plift p)(plift q)).
Proof.
  intros. unfoldq.
  rewrite val_locs_abs.
  rewrite plift_and. intros. left.
  intuition. 
Qed.

Lemma valq_val_locs_empty: forall M1 M2 H v,
  val_qual M1 M2 H v false pempty ->
  locs_locs_stty M2 (val_locs v) = pempty.
Proof.
  intros. eapply functional_extensionality.
  intros. eapply propositional_extensionality.
  split; intros.
  destruct (H0 x); auto. rewrite vars_locs_empty in H2. inversion H2. subst.
  unfoldq; intuition. subst. unfoldq; intuition.
  unfoldq; intuition. 
Qed.


Lemma valq_sub: forall M M1 H v fr fr' q q',
    val_qual M M1 H v fr q ->
    psub q q' ->
    psub q' (pdom H) ->
    val_qual M M1 H v (fr||fr') q'.
Proof.
  intros. intros ? ?. 
  destruct (H0 x) as [H_q | H_fr]. eauto. 
  - (* q  *) left. eapply lls_mono. 2: eauto. intros ? ?. eapply vars_locs_mono; eauto.
  - (* fr *) destruct fr. 2: contradiction. right. eauto.
Qed.



(* ---------- environment lemmas  ---------- *)

Lemma wf_env_type: forall M H1 H2 G p, 
  env_type M H1 H2 G p -> 
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


Lemma envt_telescope: forall M H1 H2 G p,
    env_type M H1 H2 G p -> telescope G.
Proof.
  intros. destruct H as (? & ? & ? & ? & ? & ? & ?).
  intros ? ? ? ? ?. edestruct H5 as (? & ? & ? & ? & ? & ?); eauto.
Qed.


Lemma envt_store_wf: forall M H1 H2 G p q,
  env_type M H1 H2 G p ->
  psub q p ->
  (psub (vars_locs H1 q) (pnat (length1 M)) /\ 
  psub (vars_locs H2 q) (pnat (length2 M))).
Proof.
  unfoldq; intuition;
  intros; destruct H as [L1 [L2 [P1 [P2 [W1 [W2 W3]]]]]]; intuition;
  unfoldq; intuition.
  (* 1st *)
  destruct H3 as [? [? ?]].
  assert (p x0). eapply H0. eauto.
  assert (x0 < length H1). eauto.

  assert (exists xtq, indexr x0 G = Some xtq) as TY.  
  eapply indexr_var_some. rewrite <-L1. eauto.
  destruct TY as [[[Tx frx] qx] ?].
  destruct H3 as [? [? ?]].
  destruct (W1 x0 Tx frx qx) as [vx1 [vx2 [CLQ [IX1 [IX2 [VT [? ?]]]]]]]; eauto. 
  rewrite H3 in IX1. inversion IX1. subst x1. intuition.
  eapply valt_wf in H10.  intuition. eapply H11; eauto.

  (* 2st *)
  destruct H3 as [? [? ?]].
  assert (p x0). eapply H0. eauto.
  assert (x0 < length H2). eauto.

  assert (exists xtq, indexr x0 G = Some xtq) as TY. eapply indexr_var_some. rewrite <-L2. eauto. 
  destruct TY as [[[Tx frx] qx] ?].
  destruct H3 as [? [? ?]].
  destruct (W1 x0 Tx frx qx) as [vx1 [vx2 [CLQ [IX1 [IX2 [VT [? ?]]]]]]]; intuition. 
  rewrite H3 in IX2. inversion IX2. subst x1.

  eapply valt_wf in H10. intuition. eapply H12; eauto.
Qed.


Lemma envt_store_deep_wf: forall M H1 H2 G p q,
    env_type M H1 H2 G p ->
    psub q p ->
    ( psub (locs_locs_stty (st1 M) (vars_locs H1 q)) (pnat (length1 M)) /\ 
      psub (locs_locs_stty (st2 M) (vars_locs H2 q)) (pnat (length2 M))).
Proof.
  intros. eapply envt_store_wf with (q := q) in H as H'; auto. destruct H' as [A B].
  destruct H as [L1 [L2 [P1 [P2 [W1 [W2 W3]]]]]]; intuition.

  +  (* 1st *)
    intros ? ?. inversion H; subst. eapply A; auto.
    destruct H3 as [? [? [? [? ?]]]].
    assert (x0 < length H1). apply indexr_var_some' in H6. auto.
    assert (exists xtq, indexr x0 G = Some xtq) as TY. 
    eapply indexr_var_some. rewrite <-L1. eauto.
    destruct TY as [[[Tx frx] qx] ?].
    destruct (W1 x0 Tx frx qx) as [vx1 [vx2 [CLQ [IX1 [IX2 [VT [? ?]]]]]]]; eauto. 
    rewrite H6 in IX1. inversion IX1. subst x2. intuition.
    assert (p x0). unfoldq. intuition. intuition.
    eapply valt_deep_wf in H13; eauto.  destruct H13.
    eapply H13. eapply lls_s; eauto.
  + (* 2st *)
    intros ? ?. inversion H; subst. eapply B; auto.
    destruct H3 as [? [? [? [? ?]]]].
    assert (x0 < length H2). apply indexr_var_some' in H6. auto.
    assert (exists xtq, indexr x0 G = Some xtq) as TY. 
    eapply indexr_var_some. rewrite <-L2. eauto.
    destruct TY as [[[Tx frx] qx] ?].
    destruct (W1 x0 Tx frx qx) as [vx1 [vx2 [CLQ [IX1 [IX2 [VT [? ?]]]]]]]; eauto. 
    rewrite H6 in IX2. inversion IX2. subst x2. intuition.
    assert (p x0). unfoldq. intuition. intuition.
    eapply valt_deep_wf in H13; eauto. destruct H13.
    eapply H14. eapply lls_s; eauto.
Qed.

Lemma envt_tighten: forall M H1 H2 G p p',
    env_type M H1 H2 G p ->
    psub p' p ->
    env_type M H1 H2 G p'.
Proof.
  intros. destruct H as [L1 [L2 [P1 [P2 W]]]].
  repeat split; auto.
  - unfoldq. intuition.
  - unfoldq. intuition.
  - intros.
    destruct W as [W ?].
    destruct (W x T fr q) as [v1 [v2 [? [? [? [? [? ?]]]]]]]; eauto.
    exists v1, v2; intuition.
    eapply H14. intuition. unfoldq; intuition.
    eapply H8. intuition. unfoldq; intuition.
  - intros.
    destruct W as [? [W1 W2]].
    eapply W1; eauto. all: unfoldq; intuition.
  - intros.
    destruct W as [? [W1 W2]].
    eapply W2; eauto. all: unfoldq; intuition.
Qed.

Lemma has_type_closed: forall M H1 H2 G p q T t fr,
  env_type M H1 H2 G (plift p) ->
  has_type G t T p fr q ->
  (
    closed_ty (length G) T /\
    closed_ql (length G) p /\
    closed_ql (length G) q 
  ).
Proof.
  intros. eapply filter_closed in H as H'.  induction H0; intuition.
  + destruct H as [? [? [? [? [? [? ?]]]]]]. destruct (H7 x T fr q) as [? [? [? [? [? [? [? ?]]]]]]]; auto.
    intuition. eapply valt_closed in H16. rewrite <- H.  intuition.
  + unfold closed_ql. intros. unfold qone in H4. bdestruct (x0 =? x); intuition.
    apply indexr_var_some' in H0. lia.
  + inversion H4. auto.
  + inversion H4. auto.
  + inversion H3. auto.
  + inversion H4. auto.
  + inversion H4. subst. eapply closedq_or; intuition. intros ? ?.
    destruct rf1. unfoldq; intuition. unfoldq; intuition.
  + inversion H5. subst. auto. 
  + inversion H5. subst. eapply closedq_or; intuition.
    intros ? ?. destruct fn2; unfoldq; intuition.
    eapply closedq_or; intuition. 
    intros ? ?. destruct ar2; unfoldq; intuition.
  + constructor; intuition.
  +  eapply closedq_or; intuition. 
    unfold closed_ql. intros. unfold qdiff in H8. apply andb_true_iff in H8.
    destruct H8. eapply H9 in H8. auto.
    eapply closedq_sub. eapply H'. auto.
Qed.

Lemma envt_filter_deep: forall M H1 H2 S1 S2 G p q,
    env_type M H1 H2 G p ->
    store_type S1 S2 M ->
    psub q p ->
    st_filter M (locs_locs_stty (st1 M) (vars_locs H1 q)) (locs_locs_stty (st2 M) (vars_locs H2 q)).
Proof. 
  intros. eapply envt_store_deep_wf with (q := q) in H as H'; auto. 
  destruct H' as [W4 W5]. remember H as WFE. clear HeqWFE.
  destruct H as [L1 [L2 [P1 [P2 [W1 [W2 W3]]]]]].
  remember H0 as ST'. clear HeqST'.
  destruct H0 as [SST1 [SST2 [ST [R L]]]].
  repeat split; auto. 
  + intros. eapply lls_vars in H0. destruct H0 as [? [? ?]].
    eapply lls_var in H4. destruct H4 as [? [? ?]].
    eapply H3 in H0 as H0'.
    assert (x < length G).  eapply P1 in H0'. unfold pdom in H0'. rewrite <- L1. lia.
    eapply indexr_var_some in H6. destruct H6 as [[[T frt] qt] ?].
    destruct (W1 x T frt qt) as [v1 [v2 [? [IX1 [IX2 [VT [? ?]]]]]]]; auto.
    rewrite IX1 in H4. inversion H4. subst x0. 
    eapply valt_same_locs_deep in H5; eauto.
    eapply lls_var' in H5; eauto.
    eapply lls_vars'; eauto.
  + intros. eapply lls_vars in H0. destruct H0 as [? [? ?]].
    eapply lls_var in H4. destruct H4 as [? [? ?]].
    eapply H3 in H0 as H0'.
    assert (x < length G).  eapply P1 in H0'. unfold pdom in H0'. rewrite <- L1. lia.
    eapply indexr_var_some in H6. destruct H6 as [[[T frt] qt] ?].
    destruct (W1 x T frt qt) as [v1 [v2 [? [IX1 [IX2 [VT [? ?]]]]]]]; auto.
    rewrite IX2 in H4. inversion H4. subst x0. 
    eapply valt_same_locs_deep in H5; eauto.
    eapply lls_var' in H5; eauto.
    eapply lls_vars'; eauto.
Qed.


Lemma envt_same_locs: forall S1 S2 M H1 H2 G p p1 l1 l2,
    store_type S1 S2 M ->
    env_type M H1 H2 G p ->
    strel M l1 l2 ->
    psub p1 p ->
    locs_locs_stty (st1 M) (vars_locs H1 p1) l1 <-> (locs_locs_stty (st2 M) (vars_locs H2 p1)) l2.
Proof.
  intros.
  remember (locs_locs_stty (st1 M) (vars_locs H1 p1)) as A.
  remember (locs_locs_stty (st2 M) (vars_locs H2 p1)) as B.
  assert (st_filter M A B). {
    subst A B. eapply envt_filter_deep; eauto.
  }
  subst A B. eapply H5. auto.
Qed.


Lemma envt_store_change: forall M M' H1 H2 G S1 S2 p
    (WFE: env_type M H1 H2 G p)
    (ST: store_type S1 S2 M)
    (SCP: st_chain_partial M M'(locs_locs_stty (st1 M) (vars_locs H1 p))  (locs_locs_stty (st2 M) (vars_locs H2  p))),
    env_type M' H1 H2 G p.
Proof. 
  intros. remember WFE as WFE'. clear HeqWFE'.
  destruct WFE as [L1 [L2 [P1 [P2 [W1 [W2 W3]]]]]]. 
  repeat split; auto. intros.
  destruct (W1 _ _ _  _ H) as [vx1 [vx2 [IH1 [IH2 [CLQ [HVX ?]]]]]]; intuition.
  exists vx1, vx2. intuition.
  - eapply valt_store_change; eauto. eapply valt_deep_wf in H5 as H5'.
    destruct H5' as [C D].
    eapply stchain_tighten. eapply valt_filter. eauto. eauto.
    intros ? Q. eapply lls_vars'; eauto. eapply lls_var'; eauto.
    intros ? Q. eapply lls_vars'; eauto. eapply lls_var'; eauto. 
  - erewrite <- lls_change1.  intros ? ?. erewrite <- lls_change1. eauto. eapply stchain_tighten; eauto.
    eapply envt_filter_deep; eauto. eapply lls_mono. eapply vars_locs_mono; eauto.
    eapply lls_mono.  eapply vars_locs_mono. auto.
    eapply stchain_tighten. eapply valt_filter; eauto. eauto.
    intros ? ?. eapply H3 in H7. eapply lls_mono; eauto. eapply vars_locs_mono; eauto.
    intros ? ?. eapply H8 in H7. eapply lls_mono; eauto. eapply vars_locs_mono; eauto.
  - erewrite <- lls_change2. intros ? ?. erewrite <- lls_change2. eauto. eapply stchain_tighten; eauto.
    eapply envt_filter_deep; eauto. eapply lls_mono. eapply vars_locs_mono; eauto.
    eapply lls_mono. eapply vars_locs_mono; eauto.
    eapply stchain_tighten. eapply valt_filter; eauto. eauto.
    intros ? ?. eapply H3 in H7. eapply lls_mono; eauto. eapply vars_locs_mono; eauto.
    intros ? ?. eapply H8 in H7. eapply lls_mono; eauto. eapply vars_locs_mono; eauto.
  - intros. eapply W2 in H3 as H3'; eauto. intros ? ?. 
    erewrite <- lls_change with (M := (st1 M))(M' := (st1 M')) in H4.
    erewrite <- lls_change with (M := (st1 M))(M' := (st1 M')) in H4.
    eapply H3' in H4. 
    erewrite <- lls_change; eauto.
    eapply stchain_tighten. eapply envt_filter_deep; eauto. eauto.
    eapply lls_mono. eapply vars_locs_mono; eauto.
    eapply lls_mono. eapply vars_locs_mono; eauto.
    eapply stchain_tighten. eapply envt_filter_deep; eauto. eauto.
    eapply lls_mono. eapply vars_locs_mono; eauto.
    eapply lls_mono. eapply vars_locs_mono; eauto.
    eapply stchain_tighten. eapply envt_filter_deep; eauto. eauto.
    eapply lls_mono. eapply vars_locs_mono; eauto.
    eapply lls_mono. eapply vars_locs_mono; eauto.
  - intros. eapply W3 in H3 as H3'; eauto. intros ? ?. 
    erewrite <- lls_change with (M := (st2 M))(M' := (st2 M')) in H4.
    erewrite <- lls_change with (M := (st2 M))(M' := (st2 M')) in H4.
    eapply H3' in H4. 
    erewrite <- lls_change; eauto.
    eapply stchain_tighten. eapply envt_filter_deep; eauto. eauto.
    eapply lls_mono. eapply vars_locs_mono; eauto.
    eapply lls_mono. eapply vars_locs_mono; eauto.
    eapply stchain_tighten. eapply envt_filter_deep; eauto. eauto.
    eapply lls_mono. eapply vars_locs_mono; eauto.
    eapply lls_mono. eapply vars_locs_mono; eauto.
    eapply stchain_tighten. eapply envt_filter_deep; eauto. eauto.
    eapply lls_mono. eapply vars_locs_mono; eauto.
    eapply lls_mono. eapply vars_locs_mono; eauto.
Qed.


Lemma envt_store_extend: forall M M' H1 H2 S1 S2 G p,
    env_type M H1 H2 G p ->
    store_type S1 S2 M ->
    st_chain M M' ->
    env_type M' H1 H2 G p.
Proof. 
  intros. remember H as WFE. clear HeqWFE. 
  eapply envt_store_deep_wf with (q := p) in WFE as WFE'. 2: {intros ? ?. auto. } 
  destruct WFE' as [WP1 WP2].
  remember H0 as ST. clear HeqST. destruct H0 as [SST1 [SST2 SC]]. 
  destruct H as [L1 [L2 [P1 [P2 [W1 [W2 W3]]]]]]. 
  repeat split; auto. intros.
  destruct (W1 _ _ _  _ H) as [vx1 [vx2 [IH1 [IH2 [CLQ [HVX [FR1 FR2]]]]]]]; intuition.
  assert (st_chain_partial M M' (locs_locs_stty (st1 M) (vars_locs H1  p))  (locs_locs_stty (st2 M) (vars_locs H2 p))). {
    eapply stchain_tighten; eauto. eapply envt_filter_deep; eauto. intros ? ?. auto.
  }
  assert (fr = false -> psub (plift q) p -> st_chain_partial M M' (locs_locs_stty (st1 M) (vars_locs H1 (plift q)))  (locs_locs_stty (st2 M) (vars_locs H2 (plift q)))). {
    intros ?. intuition.
    eapply stchain_tighten; eauto. eapply envt_filter_deep; eauto. 
    eapply lls_mono; auto. eapply vars_locs_mono; eauto.
    eapply lls_mono; auto. eapply vars_locs_mono; eauto.
  }
  assert (p x -> fr = false -> psub (plift q) p -> st_chain_partial M M' (locs_locs_stty (st1 M) (val_locs vx1))  (locs_locs_stty (st2 M) (val_locs vx2))). {
    intros ? ?. intuition.
    eapply stchain_tighten; eauto. eapply valt_filter; eauto.
  }
  exists vx1, vx2; intuition.
  + eapply valt_store_extend in H10; eauto. 
  + erewrite <- lls_change1. intros ? ?. erewrite <- lls_change1. eauto. eauto. eauto.
  + erewrite <- lls_change2. intros ? ?. erewrite <- lls_change2. eauto. eauto. eauto.
  + intros. erewrite <- lls_change1. 
    2: { eapply stchain_tighten. eapply envt_filter_deep. eauto. eauto. eauto. eauto.
         eapply lls_closed'; eauto. eapply envt_store_wf; eauto.
         eapply lls_closed'; eauto. eapply envt_store_wf; eauto.
    }
    replace (locs_locs_stty (st1 M') (vars_locs H1 q')) with (locs_locs_stty (st1 M) (vars_locs H1 q')).
    2:{ eapply lls_change. eapply stchain_tighten. eapply envt_filter_deep. eauto. eauto. eauto. eauto.
        eapply lls_closed'; eauto. eapply envt_store_wf; eauto.
        eapply lls_closed'; eauto. eapply envt_store_wf; eauto. }
    replace (locs_locs_stty (st1 M') (vars_locs H1 (pand (vars_trans G q) (vars_trans G q')))) with 
            (locs_locs_stty (st1 M) (vars_locs H1 (pand (vars_trans G q) (vars_trans G q')))).
    2: { eapply lls_change. eapply stchain_tighten. eapply envt_filter_deep. eauto. eauto. eauto. eauto.
         eapply lls_closed'; eauto. eapply envt_store_wf; eauto.
         eapply lls_closed'; eauto. eapply envt_store_wf; eauto. }        
    eapply W2; eauto.     
    
  + intros. erewrite <- lls_change2. 
    2: { eapply stchain_tighten. eapply envt_filter_deep. eauto. eauto. eauto. eauto.
         eapply lls_closed'; eauto. eapply envt_store_wf; eauto.
         eapply lls_closed'; eauto. eapply envt_store_wf; eauto.
      }
    replace (locs_locs_stty (st2 M') (vars_locs H2 q')) with (locs_locs_stty (st2 M) (vars_locs H2 q')).
    2:{ eapply lls_change2. eapply stchain_tighten. eapply envt_filter_deep. eauto. eauto. eauto. eauto.
        eapply lls_closed'; eauto. eapply envt_store_wf; eauto.
        eapply lls_closed'; eauto. eapply envt_store_wf; eauto. }
    replace (locs_locs_stty (st2 M') (vars_locs H2 (pand (vars_trans G q) (vars_trans G q')))) with 
          (locs_locs_stty (st2 M) (vars_locs H2 (pand (vars_trans G q) (vars_trans G q')))).
    2: { eapply lls_change. eapply stchain_tighten. eapply envt_filter_deep. eauto. eauto. eauto. eauto.
         eapply lls_closed'; eauto. eapply envt_store_wf; eauto.
         eapply lls_closed'; eauto. eapply envt_store_wf; eauto. }        
  eapply W3; eauto.     
Qed.

Lemma valq_store_change1: forall M M' M'' S1 S2 G H1 H2 v1 v2 T T' fr p q
    (WFE: env_type M' H1 H2 G p)
    (ST: store_type S1 S2 M')
    (VT: val_type M' H1 H2 v1 v2 T T')
    (VQ: val_qual (st1 M) (st1 M') H1 v1 fr (pand p q)), 
    st_chain M' M'' ->
    val_qual (st1 M) (st1 M'') H1 v1 fr (pand p q).
Proof.
  intros. intros ? ?.
  assert (locs_locs_stty (st1 M') (val_locs v1) x). {
    erewrite lls_change1. eauto.
    eapply stchain_tighten; eauto. eapply valt_filter; eauto.
    1,2: eapply valt_deep_wf in VT; intuition.
  }
  destruct (VQ x H3). {
    left. erewrite <-lls_change1. eauto.
    eapply stchain_tighten; eauto. eapply envt_filter_deep; eauto.
    intros ? ?. unfoldq; intuition.
    1,2: eapply envt_store_deep_wf; eauto; unfoldq; intuition. 
  } {
    right. destruct fr; try contradiction. 
    simpl in *. unfold pdiff , pnat in *. intuition. 
    eapply st_mono1' in H; eauto.
  }
Qed.

Lemma valq_store_change2: forall M M' M'' S1 S2 G H1 H2 v1 v2 T T' fr p q
    (WFE: env_type M' H1 H2 G p)
    (ST: store_type S1 S2 M')
    (VT: val_type M' H1 H2 v1 v2 T T')
    (VQ: val_qual (st2 M) (st2 M') H2 v2 fr (pand p q)), 
    st_chain M' M'' ->
    val_qual (st2 M) (st2 M'') H2 v2 fr (pand p q).
Proof.
  intros. intros ? ?.
  assert (locs_locs_stty (st2 M') (val_locs v2) x). {
    erewrite lls_change2. eauto.
    eapply stchain_tighten; eauto. eapply valt_filter; eauto.
    1,2: eapply valt_deep_wf in VT; intuition.
  }
  destruct (VQ x H3). {
    left. erewrite <-lls_change2. eauto.
    eapply stchain_tighten; eauto. eapply envt_filter_deep; eauto.
    intros ? ?. unfoldq; intuition.
    1,2: eapply envt_store_deep_wf; eauto; unfoldq; intuition. 
  } {
    right. destruct fr; try contradiction. 
    simpl in *. unfold pdiff , pnat in *. intuition. 
    eapply st_mono2' in H; eauto.
  }
Qed.



Lemma lls_vars_shrink: forall q H M v, 
  psub q (pdom H) ->
  locs_locs_stty M (vars_locs (v ::H) q) = locs_locs_stty M (vars_locs H q).
Proof.
  intros. eapply functional_extensionality.
  intros. eapply propositional_extensionality.
  split; intros.
  - inversion H1; subst. left. destruct H2 as [? [? ?]]. exists x0. split; auto. eapply var_locs_shrink; eauto. eapply H0. auto.
    eapply lls_s; eauto. destruct H2 as [? [? ?]]. exists x0. split; auto. eapply var_locs_shrink; eauto. eapply H0. auto.
  - inversion H1; subst. left. eapply vars_locs_extend1; eauto. 
    eapply lls_s; eauto. eapply vars_locs_extend1; eauto.
Qed.

Lemma vars_or: forall H p1 p2,
  vars_locs H (por p1 p2) = por (vars_locs H p1)(vars_locs H p2).
Proof.
  intros. eapply functional_extensionality. intros ?. 
  eapply propositional_extensionality. split; intros.
  + unfoldq; intuition. destruct H0 as [? [? ?]]. destruct H0.
    left. exists x0; intuition. right. exists x0; intuition.
  + unfoldq; intuition.
    destruct H1 as [? [? ?]]. exists x0; intuition.
    destruct H1 as [? [? ?]]. exists x0; intuition. 
Qed.

Lemma lls_vars_or: forall M H p1 p2,
  locs_locs_stty M (vars_locs H (por p1 p2)) = por (locs_locs_stty M (vars_locs H p1))(locs_locs_stty M (vars_locs H p2)).
Proof.
  intros. eapply functional_extensionality. intros ?. 
  eapply propositional_extensionality. split; intros.
  + inversion H0. 
    - subst. rewrite vars_or in H1. destruct H1. left. left. auto.
      right. left. auto.
    - subst. rewrite vars_or in H1. destruct H1. left. eapply lls_s; eauto.
      right. eapply lls_s; eauto.
  + destruct H0.
    - eapply lls_mono; eauto. eapply vars_locs_mono; eauto. unfoldq; intuition.
    - eapply lls_mono; eauto.  eapply vars_locs_mono; eauto. unfoldq; intuition.
Qed.


Lemma lls_vars_and: forall (q q': pl)  x0 H x M,
  q x0 ->
  q' x0 ->
  locs_locs_stty M (var_locs H x0) x ->
  locs_locs_stty M (vars_locs H (pand q q')) x.
Proof.
  intros. remember (var_locs H x0) as X.
  induction H2; subst q0.
  + eapply lls_z. exists x0. intuition. unfoldq; intuition.
  + eapply lls_s; eauto. exists x0. intuition. unfoldq; intuition.
Qed.


Lemma envt_extend_full: forall M M1 H1 H2 G S1 S2 vx1 vx2 T1 p fr1 q1 qf
    (WFE: env_type M H1 H2 G p)
    (SC: st_chain_partial M M1 (locs_locs_stty (st1 M) (vars_locs H1 (pand p qf))) (locs_locs_stty (st2 M) (vars_locs H2 (pand p qf))))
    (ST: store_type S1 S2 M)
    (VT: val_type M1 H1 H2 vx1 vx2 T1 T1)
    (VQ1: psub (pand (locs_locs_stty (st1 M1) (vars_locs H1 qf)) (locs_locs_stty (st1 M1) (val_locs vx1)))
      (locs_locs_stty (st1 M1) (vars_locs H1 (plift q1))))
    (VQ2: psub (pand (locs_locs_stty (st2 M1) (vars_locs H2 qf)) (locs_locs_stty (st2 M1) (val_locs vx2)))
      (locs_locs_stty (st2 M1) (vars_locs H2 (plift q1))))  
    (A1: (fr1 = false -> psub (locs_locs_stty (st1 M1) (val_locs vx1)) (locs_locs_stty (st1 M1) (vars_locs H1 (plift q1)))))
    (A2: (fr1 = false -> psub (locs_locs_stty (st2 M1) (val_locs vx2)) (locs_locs_stty (st2 M1) (vars_locs H2 (plift q1)))))
    (SUB1: psub qf p)
    (SUB2: psub (plift q1) qf) ,
    closed_ty (length G) T1 ->
    closed_ql (length G) q1 ->
    env_type M1 (vx1 :: H1) (vx2 :: H2)((T1, fr1, q1) :: G) (por qf (pone (length G))).
Proof. 
  intros.  
  remember WFE as WFE1. clear HeqWFE1.
  destruct WFE as [L1 [L2 [PD1 [PD2 [W1 [W2 W3]]]]]].
  assert (psub p (pdom G)). { intros ? ?. unfold pdom. rewrite <- L1. eapply PD1. auto.  }

  repeat split; eauto.
  - simpl. eauto.
  - simpl. eauto.
  - unfoldq. simpl. intuition. 
  - unfoldq. simpl. intuition.
  - intros.
    bdestruct (x =? length G); intuition. 
    + subst. rewrite indexr_head in H4. inversion H4. subst.
      exists vx1, vx2. repeat split.
      auto.
      rewrite <-L1. rewrite indexr_head. auto. 
      rewrite <-L2. rewrite indexr_head. auto.
      intros. eapply valt_extend1; auto. rewrite L1. auto. rewrite L2. auto.
      intros. intros ? ?. eapply A1 in H8. eapply lls_mono; eauto. intros ? ?. eapply vars_locs_extend1; eauto. auto.
      intros. intros ? ?. eapply A2 in H8. eapply lls_mono; eauto. intros ? ?. eapply vars_locs_extend1; eauto. auto.
    + rewrite indexr_skip in H4. 2: lia. 
      assert (x < length G). { apply indexr_var_some' in H4. auto. }
      destruct (W1 _ _ _ _ H4) as [v1' [v2' [CL2 [IH1 [IH2 [VALT [FR1 FR2]]]]]]]; intuition.
      exists v1', v2'. intuition.
      rewrite indexr_skip. auto. lia.
      rewrite indexr_skip. auto. lia.
      assert (p x). { unfoldq; intuition.  }
      eapply valt_extend1; eauto. 1,2: eapply valt_closed in VALT; intuition. eapply VALT in H8. 
      (* XXX store extend/tighten XXX *) {
        eapply valt_store_change. eapply ST. auto. unfoldq. intuition.        
        eapply stchain_tighten; eauto. eapply valt_filter; eauto.
        intros ? ?. eapply lls_mono; eauto. exists x. intuition. eexists. eauto.
        intros ? ?. eapply lls_mono; eauto. exists x. intuition. eexists. eauto.
      } {
        intros. intros ? ?.
        assert (psub (plift q) qf). {
          intros ? A. eapply CL2 in A as B. 
          eapply H9 in A. unfoldq; intuition.
        }
        assert (p x). {
          destruct H8. unfoldq; intuition. unfoldq; intuition.  
        }
        assert (psub (plift q) p). {
          destruct H8. unfoldq; intuition. unfoldq; intuition.
        }
        erewrite lls_change with (M' := (st1 M1)) in H10. eapply H10 in H12. rewrite <- vars_locs_extend with (H' := [vx1]) in H12. simpl in H12. 
        erewrite <- lls_change; eauto.
        rewrite lls_vars_shrink; auto. rewrite lls_vars_shrink in H12; auto. 
        eapply stchain_tighten; eauto. eapply envt_filter_deep; eauto. unfoldq; intuition. 
        eapply lls_mono; eauto. intros ? ?. eapply vars_locs_mono; eauto. unfoldq; intuition.
        unfoldq; intuition. 
        eapply lls_mono; eauto. eapply vars_locs_mono; eauto. unfoldq; intuition.
        unfoldq; intuition.
        auto.
        unfoldq; intuition. unfoldq; intuition. auto. auto.
        eapply sstchain_tighten. eapply SC.
        intuition. intros ? ?. eapply H11 in H10. 
        eapply lls_mono; eauto. eapply vars_locs_mono; eauto. unfoldq; intuition.
      }{
        intros. intros ? ?.
        rewrite lls_vars_shrink; eauto.
        assert (psub (plift q) qf). {
          intros ? A. eapply CL2 in A as B.
          eapply H9 in A. unfoldq; intuition.
        }
        assert (p x). {
          destruct H8. unfoldq; intuition. unfoldq; intuition.  
        }
        assert (psub (plift q) p). {
          destruct H8. unfoldq; intuition. unfoldq; intuition.
        }
        intuition. erewrite <- lls_change with (M := (st2 M)) in H12. eapply H17 in H12. 
        erewrite <- lls_change; eauto.
        eapply sstchain_tighten. eapply SC. 
        eapply lls_mono; eauto. intros ? ?. eapply vars_locs_mono; eauto. unfoldq; intuition.
        eapply sstchain_tighten. eapply SC. intros ? ?.
        eapply H17 in H10.
        eapply lls_mono; eauto. intros ? ?. eapply vars_locs_mono; eauto. unfoldq; intuition.
        intros ? ?. eapply CL2 in H13. unfoldq; intuition.
      }  
       
  - (* 2nd invariant *)
    
    clear W1. (* distraction*)
    eapply envt_telescope in WFE1 as TL1.
    
    intros q q' QSUB QSUB' QSUBTR x (QQ & QQ').
    eapply lls_vars in QQ.
    eapply lls_vars in QQ'. 
    
    destruct QQ as (? & VTQ & VLQ).
    destruct QQ' as (? & VTQ' & VLQ').

    destruct (QSUB x0); intuition; destruct (QSUB' x1); intuition.
    
    + (* qf, qf *)
      
      assert (psub (pand (vars_trans G (pand (pdom H1) q)) (vars_trans G (pand (pdom H1) q'))) qf) as QSUBTR1. {
        intros ? [? ?]. destruct (QSUBTR x2) as [? | ?].
        split. (* extend *)
        eapply vt_extend. eapply vt_mono. 2: eapply H6. unfoldq. intuition.
        eapply vt_extend. eapply vt_mono. 2: eapply H7. unfoldq. intuition.
        eauto.
        eapply vt_closed in H6 as CL; eauto. unfoldq. intuition. unfoldq. intuition. (* contra *)
      }
      
      eassert _ as W4. {
        eapply (W2 (pand (pdom H1) q) (pand (pdom H1) q')) with (x:=x).
        
        intros ? ?. destruct (QSUB x2) as [? | ?]. unfoldq. intuition. 
        eauto. eauto. unfoldq. lia.
        
        intros ? ?. destruct (QSUB' x2) as [? | ?]. unfoldq. intuition. 
        eauto. eauto. unfoldq. lia. 

        intros ? ?.  eapply QSUBTR1 in H6. eapply SUB1. auto.
        
        split.

        erewrite lls_change. 
        eapply lls_vars'. eapply lls_mono. 2: eapply VLQ. intros ? ?. eapply var_locs_shrink. eauto. unfoldq. intuition. unfoldq. intuition.
        eapply stchain_tighten. eapply envt_filter_deep; eauto. 
        intros ? ?. destruct H6. unfoldq. eapply QSUB in H7. unfoldq; intuition. 
        eapply SC; eauto. eapply lls_mono. eapply vars_locs_mono. unfoldq. intuition. destruct (QSUB x2); eauto. lia. 
        eapply QSUB in H8. unfoldq; intuition.

        eapply lls_mono; eauto. eapply vars_locs_mono; eauto. unfoldq; intuition.
        eapply QSUB in H8. unfoldq; intuition. 
        eapply QSUB in H8. unfoldq; intuition. 

        erewrite lls_change. 
        eapply lls_vars'. eapply lls_mono. 2: eapply VLQ'. intros ? ?. eapply var_locs_shrink. eauto. unfoldq. intuition. unfoldq. intuition.
        
        eapply stchain_tighten. eapply envt_filter_deep; eauto. 
        intros ? ?. destruct H6. unfoldq. eapply QSUB' in H7. unfoldq; intuition. 
        eapply SC; eauto. eapply lls_mono. eapply vars_locs_mono. unfoldq. intuition. destruct (QSUB' x2); eauto. lia. 
        eapply QSUB' in H8. unfoldq; intuition.

        eapply lls_mono; eauto. eapply vars_locs_mono; eauto. unfoldq; intuition.
        eapply QSUB' in H8. unfoldq; intuition.
        eapply QSUB' in H8. unfoldq; intuition.

      }

      erewrite lls_change in W4.
      
      eapply lls_vars in W4. destruct W4 as (? & (? & ?) & ?). 
      
      eapply lls_vars'. eapply lls_mono. 2: eauto. intros ? ?. eapply var_locs_extend. eauto. split.
      eapply vt_extend. eapply vt_mono. 2: eapply H6. unfoldq. intuition.
      eapply vt_extend. eapply vt_mono. 2: eapply H7. unfoldq. intuition.

      eapply stchain_tighten. eapply envt_filter_deep; eauto. 
      intros ? ?. eapply QSUBTR1 in H6. auto. eauto. 

      eapply lls_mono. eapply vars_locs_mono. 
      intros ? ?. eapply QSUBTR1 in H6. unfoldq; intuition. auto. 

      eapply lls_mono; eauto. eapply vars_locs_mono; eauto. 
      intros ? ?. eapply QSUBTR1 in H6. unfoldq; intuition.  
      
    + (* qf, x *)
      unfold pone in H5. subst x1. 
      
      assert (psub (pand (vars_trans G (pand (pdom H1) q)) (vars_trans G (plift q1))) qf) as QSUBTR1. {
        intros ? [? ?]. destruct (QSUBTR x1) as [? | ?].
        split. {
          eapply vt_extend. eapply vt_mono. 2: eapply H5. unfoldq. intuition. (* extend q *)
        }{
          eapply vt_head. eauto. unfoldq; intuition.  eauto. eauto.  (* pick q1 *)
        }
        eauto.
        eapply vt_closed in H6; eauto. unfoldq. intuition.  (* contra *)
      }

      eassert _ as W4. {
        eapply (W2 (pand (pdom H1) q) (plift q1)) with (x:=x).

        intros ? ?. destruct (QSUB x1) as [? | ?]. unfoldq. intuition. 
        eauto. eauto. unfoldq. lia.

        unfoldq. intuition.

        intros ? ?. eapply QSUBTR1 in H5. eauto.

        split. 

        erewrite lls_change. 
        eapply lls_vars'. eapply lls_mono. 2: eapply VLQ. intros ? ?. eapply var_locs_shrink. eauto. unfoldq. intuition. unfoldq. intuition.
        eapply stchain_tighten. eapply envt_filter_deep; eauto. unfoldq; intuition. eapply QSUB in H7. unfoldq; intuition.
        eauto. eapply lls_mono. eapply vars_locs_mono. unfoldq. intuition. destruct (QSUB x1); eauto. lia. eapply QSUB in H7. unfoldq; intuition.
        eapply lls_mono. eapply vars_locs_mono. unfoldq. intuition. destruct (QSUB x1); eauto. lia. eapply QSUB in H7. unfoldq; intuition.

        erewrite lls_change.
        eapply VQ1. split.
        eapply lls_vars'. eapply lls_mono. 2: eapply VLQ. intros ? ?. eapply var_locs_shrink. eauto. unfoldq. intuition. auto. 

        eapply lls_var in VLQ'. destruct VLQ' as (? & IX & ?). rewrite <- L1 in IX.
        rewrite indexr_head in IX. inversion IX. eauto.
        eapply stchain_tighten. eapply envt_filter_deep; eauto. unfoldq; intuition. eauto.
        eapply lls_mono. eapply vars_locs_mono. unfoldq. intuition.
        eapply lls_mono. eapply vars_locs_mono. unfoldq. intuition.
      }


      erewrite lls_change in W4.

      eapply lls_vars in W4. destruct W4 as (? & (? & ?) & ?). 

      eapply lls_vars'. eapply lls_mono. 2: eauto. intros ? ?. eapply var_locs_extend. eauto. split.
      eapply vt_extend. eapply vt_mono. 2: eapply H5. unfoldq. intuition.
      eapply vt_head. eauto. eauto. eauto. eauto. 

      eapply stchain_tighten. eapply envt_filter_deep; eauto.
      intros ? ?. eapply QSUBTR1 in H5. auto. eauto. 
      eapply lls_mono. eapply vars_locs_mono. intros ? ?. eapply QSUBTR1 in H5. unfoldq; intuition.
      eapply lls_mono. eapply vars_locs_mono. intros ? ?. eapply QSUBTR1 in H5. unfoldq; intuition.
      

    + (* x, qf *)
      unfold pone in H4. subst x0. 
      
      assert (psub (pand (vars_trans G (plift q1)) (vars_trans G (pand (pdom H1) q'))) qf) as QSUBTR1. {
        intros ? [? ?]. destruct (QSUBTR x0) as [? | ?].
        split. {
          eapply vt_head. eauto. auto. auto. auto.  (* pick q1 *)
        }{
          eapply vt_extend. eapply vt_mono. 2: eapply H6. unfoldq. intuition. (* extend q' *)
        }
        eauto.
        eapply vt_closed in H6; eauto. unfoldq. intuition. unfoldq. intuition. (* contra *)
      }

      eassert _ as W4. {
        eapply (W2 (plift q1) (pand (pdom H1) q')) with (x:=x).

        unfoldq. intuition.

        intros ? ?. destruct (QSUB' x0) as [? | ?]. unfoldq. intuition. 
        eauto. eauto. unfoldq. lia.

        intros ? ?. eapply QSUBTR1 in H4. eauto.

        split. 
        erewrite lls_change.
        eapply VQ1. split.
        eapply lls_vars'. eapply lls_mono. 2: eapply VLQ'. intros ? ?. eapply var_locs_shrink. eauto. unfoldq. intuition. eauto. 

        eapply lls_var in VLQ. destruct VLQ as (? & IX & ?). rewrite <- L1 in IX.
        rewrite indexr_head in IX. inversion IX. eauto.
        eapply stchain_tighten. eapply envt_filter_deep; eauto. unfoldq; intuition. eauto.
        eapply lls_mono. eapply vars_locs_mono. unfoldq. intuition.
        eapply lls_mono. eapply vars_locs_mono. unfoldq. intuition.

        erewrite lls_change. 
        eapply lls_vars'. eapply lls_mono. 2: eapply VLQ'. intros ? ?. eapply var_locs_shrink. eauto. unfoldq. intuition. unfoldq. intuition.
        eapply stchain_tighten. eapply envt_filter_deep; eauto. unfoldq; intuition. eapply QSUB' in H7. unfoldq; intuition.
        eauto.
        eapply lls_mono. eapply vars_locs_mono. unfoldq. intuition. eapply QSUB' in H7. unfoldq; intuition. eapply QSUB' in H7. unfoldq; intuition.
        eapply lls_mono. eapply vars_locs_mono. unfoldq. intuition. eapply QSUB' in H7. unfoldq; intuition. eapply QSUB' in H7. unfoldq; intuition.
      }

      erewrite lls_change in W4.

      eapply lls_vars in W4. destruct W4 as (? & (? & ?) & ?). 

      eapply lls_vars'. eapply lls_mono. 2: eauto. intros ? ?. eapply var_locs_extend. eauto. split.
      eapply vt_head. eauto. auto. auto. auto. 
      eapply vt_extend. eapply vt_mono. 2: eapply H6. unfoldq. intuition.

      eapply stchain_tighten. eapply envt_filter_deep; eauto. 
      intros ? ?. eapply QSUBTR1 in H4. auto. eauto. 
      eapply lls_mono. eapply vars_locs_mono. intros ? ?.  eapply QSUBTR1 in H4. unfoldq; intuition.
      eapply lls_mono. eapply vars_locs_mono. intros ? ?.  eapply QSUBTR1 in H4. unfoldq; intuition.
      
    + (* x, x *)
      unfold pone in H4, H5.
      subst x0 x1.

      eapply lls_vars'. eauto. split.
      left. eauto. left. eauto.
  - (* 3rd invariant *)
  clear W1. (* distraction*)
  eapply envt_telescope in WFE1 as TL1.
  
  intros q q' QSUB QSUB' QSUBTR x (QQ & QQ').
  eapply lls_vars in QQ.
  eapply lls_vars in QQ'. 
  
  destruct QQ as (? & VTQ & VLQ).
  destruct QQ' as (? & VTQ' & VLQ').

  destruct (QSUB x0); intuition; destruct (QSUB' x1); intuition.
  
  + (* qf, qf *)
    
    assert (psub (pand (vars_trans G (pand (pdom H2) q)) (vars_trans G (pand (pdom H2) q'))) qf) as QSUBTR1. {
      intros ? [? ?]. destruct (QSUBTR x2) as [? | ?].
      split. (* extend *)
      eapply vt_extend. eapply vt_mono. 2: eapply H6. unfoldq. intuition.
      eapply vt_extend. eapply vt_mono. 2: eapply H7. unfoldq. intuition.
      eauto.
      eapply vt_closed in H6 as CL; eauto. unfoldq. intuition. unfoldq. intuition. (* contra *)
    }
    
    eassert _ as W4. {
      eapply (W3 (pand (pdom H2) q) (pand (pdom H2) q')) with (x:=x).
      
      intros ? ?. destruct (QSUB x2) as [? | ?]. unfoldq. intuition. 
      eauto. eauto. unfoldq. lia.
      
      intros ? ?. destruct (QSUB' x2) as [? | ?]. unfoldq. intuition. 
      eauto. eauto. unfoldq. lia. 

      intros ? ?.  eapply QSUBTR1 in H6. eapply SUB1. auto.
      
      split.

      erewrite lls_change. 
      eapply lls_vars'. eapply lls_mono. 2: eapply VLQ. intros ? ?. eapply var_locs_shrink. eauto. unfoldq. intuition. unfoldq. intuition.
      eapply stchain_tighten. eapply envt_filter_deep; eauto. 
      intros ? ?. destruct H6. unfoldq. eapply QSUB in H7. unfoldq; intuition. 
      eapply SC; eauto. eapply lls_mono. eapply vars_locs_mono. unfoldq. intuition. destruct (QSUB x2); eauto. lia. 
      eapply QSUB in H8. unfoldq; intuition.

      eapply lls_mono; eauto. eapply vars_locs_mono; eauto. unfoldq; intuition.
      eapply QSUB in H8. unfoldq; intuition. 
      eapply QSUB in H8. unfoldq; intuition. 

      erewrite lls_change. 
      eapply lls_vars'. eapply lls_mono. 2: eapply VLQ'. intros ? ?. eapply var_locs_shrink. eauto. unfoldq. intuition. unfoldq. intuition.
      
      eapply stchain_tighten. eapply envt_filter_deep; eauto. 
      intros ? ?. destruct H6. unfoldq. eapply QSUB' in H7. unfoldq; intuition. 
      eapply SC; eauto. eapply lls_mono. eapply vars_locs_mono. unfoldq. intuition. destruct (QSUB' x2); eauto. lia. 
      eapply QSUB' in H8. unfoldq; intuition.

      eapply lls_mono; eauto. eapply vars_locs_mono; eauto. unfoldq; intuition.
      eapply QSUB' in H8. unfoldq; intuition.
      eapply QSUB' in H8. unfoldq; intuition.

    }

    erewrite lls_change in W4.
    
    eapply lls_vars in W4. destruct W4 as (? & (? & ?) & ?). 
    
    eapply lls_vars'. eapply lls_mono. 2: eauto. intros ? ?. eapply var_locs_extend. eauto. split.
    eapply vt_extend. eapply vt_mono. 2: eapply H6. unfoldq. intuition.
    eapply vt_extend. eapply vt_mono. 2: eapply H7. unfoldq. intuition.

    eapply stchain_tighten. eapply envt_filter_deep; eauto. 
    intros ? ?. eapply QSUBTR1 in H6. auto. eauto. 

    eapply lls_mono. eapply vars_locs_mono. 
    intros ? ?. eapply QSUBTR1 in H6. unfoldq; intuition. auto. 

    eapply lls_mono; eauto. eapply vars_locs_mono; eauto. 
    intros ? ?. eapply QSUBTR1 in H6. unfoldq; intuition.  
    
  + (* qf, x *)
    unfold pone in H5. subst x1. 
    
    assert (psub (pand (vars_trans G (pand (pdom H2) q)) (vars_trans G (plift q1))) qf) as QSUBTR1. {
      intros ? [? ?]. destruct (QSUBTR x1) as [? | ?].
      split. {
        eapply vt_extend. eapply vt_mono. 2: eapply H5. unfoldq. intuition. (* extend q *)
      }{
        eapply vt_head. eauto. unfoldq; intuition.  eauto. eauto.  (* pick q1 *)
      }
      eauto.
      eapply vt_closed in H6; eauto. unfoldq. intuition.  (* contra *)
    }

    eassert _ as W4. {
      eapply (W3 (pand (pdom H2) q) (plift q1)) with (x:=x).

      intros ? ?. destruct (QSUB x1) as [? | ?]. unfoldq. intuition. 
      eauto. eauto. unfoldq. lia.

      unfoldq. intuition.

      intros ? ?. eapply QSUBTR1 in H5. eauto.

      split. 

      erewrite lls_change. 
      eapply lls_vars'. eapply lls_mono. 2: eapply VLQ. intros ? ?. eapply var_locs_shrink. eauto. unfoldq. intuition. unfoldq. intuition.
      eapply stchain_tighten. eapply envt_filter_deep; eauto. unfoldq; intuition. eapply QSUB in H7. unfoldq; intuition.
      eauto. eapply lls_mono. eapply vars_locs_mono. unfoldq. intuition. destruct (QSUB x1); eauto. lia. eapply QSUB in H7. unfoldq; intuition.
      eapply lls_mono. eapply vars_locs_mono. unfoldq. intuition. destruct (QSUB x1); eauto. lia. eapply QSUB in H7. unfoldq; intuition.

      erewrite lls_change.
      eapply VQ2. split.
      eapply lls_vars'. eapply lls_mono. 2: eapply VLQ. intros ? ?. eapply var_locs_shrink. eauto. unfoldq. intuition. auto. 

      eapply lls_var in VLQ'. destruct VLQ' as (? & IX & ?). rewrite <- L2 in IX.
      rewrite indexr_head in IX. inversion IX. eauto.
      eapply stchain_tighten. eapply envt_filter_deep; eauto. unfoldq; intuition. eauto.
      eapply lls_mono. eapply vars_locs_mono. unfoldq. intuition.
      eapply lls_mono. eapply vars_locs_mono. unfoldq. intuition.
    }


    erewrite lls_change in W4.

    eapply lls_vars in W4. destruct W4 as (? & (? & ?) & ?). 

    eapply lls_vars'. eapply lls_mono. 2: eauto. intros ? ?. eapply var_locs_extend. eauto. split.
    eapply vt_extend. eapply vt_mono. 2: eapply H5. unfoldq. intuition.
    eapply vt_head. eauto. eauto. eauto. eauto. 

    eapply stchain_tighten. eapply envt_filter_deep; eauto.
    intros ? ?. eapply QSUBTR1 in H5. auto. eauto. 
    eapply lls_mono. eapply vars_locs_mono. intros ? ?. eapply QSUBTR1 in H5. unfoldq; intuition.
    eapply lls_mono. eapply vars_locs_mono. intros ? ?. eapply QSUBTR1 in H5. unfoldq; intuition.
    

  + (* x, qf *)
    unfold pone in H4. subst x0. 
    
    assert (psub (pand (vars_trans G (plift q1)) (vars_trans G (pand (pdom H2) q'))) qf) as QSUBTR1. {
      intros ? [? ?]. destruct (QSUBTR x0) as [? | ?].
      split. {
        eapply vt_head. eauto. auto. auto. auto.  (* pick q1 *)
      }{
        eapply vt_extend. eapply vt_mono. 2: eapply H6. unfoldq. intuition. (* extend q' *)
      }
      eauto.
      eapply vt_closed in H6; eauto. unfoldq. intuition. unfoldq. intuition. (* contra *)
    }

    eassert _ as W4. {
      eapply (W3 (plift q1) (pand (pdom H2) q')) with (x:=x).

      unfoldq. intuition.

      intros ? ?. destruct (QSUB' x0) as [? | ?]. unfoldq. intuition. 
      eauto. eauto. unfoldq. lia.

      intros ? ?. eapply QSUBTR1 in H4. eauto.

      split. 
      erewrite lls_change.
      eapply VQ2. split.
      eapply lls_vars'. eapply lls_mono. 2: eapply VLQ'. intros ? ?. eapply var_locs_shrink. eauto. unfoldq. intuition. eauto. 

      eapply lls_var in VLQ. destruct VLQ as (? & IX & ?). rewrite <- L2 in IX.
      rewrite indexr_head in IX. inversion IX. eauto.
      eapply stchain_tighten. eapply envt_filter_deep; eauto. unfoldq; intuition. eauto.
      eapply lls_mono. eapply vars_locs_mono. unfoldq. intuition.
      eapply lls_mono. eapply vars_locs_mono. unfoldq. intuition.

      erewrite lls_change. 
      eapply lls_vars'. eapply lls_mono. 2: eapply VLQ'. intros ? ?. eapply var_locs_shrink. eauto. unfoldq. intuition. unfoldq. intuition.
      eapply stchain_tighten. eapply envt_filter_deep; eauto. unfoldq; intuition. eapply QSUB' in H7. unfoldq; intuition.
      eauto.
      eapply lls_mono. eapply vars_locs_mono. unfoldq. intuition. eapply QSUB' in H7. unfoldq; intuition. eapply QSUB' in H7. unfoldq; intuition.
      eapply lls_mono. eapply vars_locs_mono. unfoldq. intuition. eapply QSUB' in H7. unfoldq; intuition. eapply QSUB' in H7. unfoldq; intuition.
    }

    erewrite lls_change in W4.

    eapply lls_vars in W4. destruct W4 as (? & (? & ?) & ?). 

    eapply lls_vars'. eapply lls_mono. 2: eauto. intros ? ?. eapply var_locs_extend. eauto. split.
    eapply vt_head. eauto. auto. auto. auto. 
    eapply vt_extend. eapply vt_mono. 2: eapply H6. unfoldq. intuition.

    eapply stchain_tighten. eapply envt_filter_deep; eauto. 
    intros ? ?. eapply QSUBTR1 in H4. auto. eauto. 
    eapply lls_mono. eapply vars_locs_mono. intros ? ?.  eapply QSUBTR1 in H4. unfoldq; intuition.
    eapply lls_mono. eapply vars_locs_mono. intros ? ?.  eapply QSUBTR1 in H4. unfoldq; intuition.
    
  + (* x, x *)
    unfold pone in H4, H5.
    subst x0 x1.

    eapply lls_vars'. eauto. split.
    left. eauto. left. eauto.
Qed.

Lemma overlapping: forall S1 S2 M S1' S2' M' M'' H1 H2 G p vf1 vf2 vx1 vx2 frf qf frx qx q1 TF1 TF2
    (WFE: env_type M H1 H2 G p)
    (ST : store_type S1 S2 M)
    (ST1 : store_type S1' S2' M')
    (STC1: st_chain M M')
    (STC2: st_chain M' M'')
    (VTF: val_type M' H1 H2 vf1 vf2 TF1 TF2) 
    (HQF1: val_qual (st1 M) (st1 M') H1 vf1 frf (pand p qf))
    (HQF2: val_qual (st2 M) (st2 M') H2 vf2 frf (pand p qf))
    (HQX1: val_qual (st1 M') (st1 M'') H1 vx1 frx (pand p qx))
    (HQX2: val_qual (st2 M') (st2 M'') H2 vx2 frx (pand p qx))
    (WFF1: psub (val_locs vf1) (st_locs1 M'))
    (WFF2: psub (val_locs vf2) (st_locs2 M'))
    (SUB: psub (plift q1) p)
    (OVERLAP: psub (pand (vars_trans G (pand p qf)) (vars_trans G (pand p qx))) (plift q1)), 
    psub (pand (locs_locs_stty (st1 M'') (val_locs vf1)) (locs_locs_stty (st1 M'') (val_locs vx1))) (locs_locs_stty (st1 M'') (vars_locs H1 (plift q1))) /\
    psub (pand (locs_locs_stty (st2 M'') (val_locs vf2)) (locs_locs_stty (st2 M'') (val_locs vx2))) (locs_locs_stty (st2 M'') (vars_locs H2 (plift q1))).
Proof. 
  intros. 
  remember WFE as WFE1. clear HeqWFE1.
  eapply envt_store_extend in WFE as WFE'; eauto.
  eapply envt_store_extend in WFE' as WFE''; eauto.  
  destruct WFE'' as [L1 [L2 [P1 [P2 [W [O1 O2]]]]]].
  
  split.
  + (* 1st *)
    intros ? [LLSF LLSX]. destruct (HQF1 x) as [Hf_q | Hf_fr]; destruct (HQX1 x) as [Hx_q | Hx_fr]; auto.
    - erewrite <- lls_change with (M := (st1 M')) in LLSF; eauto.
      eapply stchain_tighten. eapply valt_filter; eauto. eapply STC2.  
      1,2: eapply valt_deep_wf; eauto.
    - erewrite lls_change; eauto. eapply stchain_tighten. eapply valt_filter; eauto. eapply STC2.
      1,2: eapply valt_deep_wf; eauto.
    - assert ((pand (locs_locs_stty (st1 M'') (vars_locs H1 (pand p qf)))
                   (locs_locs_stty (st1 M'') (vars_locs H1 (pand p qx)))) x).
                   
        erewrite lls_change in Hf_q. 2: { 
        eapply stchain_tighten. eapply envt_filter_deep; eauto.  unfoldq; intuition.
        eauto.
        eapply envt_store_deep_wf; eauto. unfoldq; intuition. 
        eapply envt_store_deep_wf; eauto. unfoldq; intuition. }

        split; eauto.
        eapply O1 with (q := (pand p qf)) (q' := (pand p qx)) in H.
        eapply lls_mono. eapply vars_locs_mono. 2: eauto.
        unfoldq. intuition.
        unfoldq. intuition.
        unfoldq. intuition.
        unfoldq. intuition. 
    - destruct frx. 2: contradiction. 
      eapply envt_store_deep_wf in Hf_q.
        2: {  eauto. } 2: { unfoldq. intuition. }
        assert False. eapply Hx_fr. eauto. contradiction.
    - destruct frf. 2: contradiction. simpl in Hf_fr. unfold pdiff in Hf_fr.
      rewrite <- lls_change with (M := (st1 M)) in Hx_q. eapply envt_store_deep_wf in Hx_q; eauto. 
      destruct Hf_fr. unfold length1 in Hx_q. contradiction. unfoldq; intuition.
      eapply stchain_tighten. eapply envt_filter_deep; eauto. unfoldq; intuition. 
      eapply st_trans; eauto. 
      eapply envt_store_deep_wf; eauto. unfoldq; intuition. 
      eapply envt_store_deep_wf; eauto. unfoldq; intuition. 
    - destruct frf; destruct frx; simpl in *; unfold pdiff in *; destruct Hf_fr; destruct Hx_fr; try contradiction.
  
  +  (* 2nd *)
    intros ? [LLSF LLSX]. destruct (HQF2 x) as [Hf_q | Hf_fr]; destruct (HQX2 x) as [Hx_q | Hx_fr]; auto.
    - erewrite <- lls_change with (M := (st2 M')) in LLSF; eauto.
      eapply stchain_tighten. eapply valt_filter; eauto. eapply STC2.  
      1,2: eapply valt_deep_wf; eauto.
    - erewrite lls_change; eauto. eapply stchain_tighten. eapply valt_filter; eauto. eapply STC2.
      1,2: eapply valt_deep_wf; eauto.
    - assert ((pand (locs_locs_stty (st2 M'') (vars_locs H2 (pand p qf)))
                   (locs_locs_stty (st2 M'') (vars_locs H2 (pand p qx)))) x).
        erewrite lls_change in Hf_q. 2: { 
        eapply stchain_tighten. eapply envt_filter_deep; eauto.  unfoldq; intuition.
        eauto.
        eapply envt_store_deep_wf; eauto. unfoldq; intuition. 
        eapply envt_store_deep_wf; eauto. unfoldq; intuition. }

        split; eauto.
        eapply O2 with (q := (pand p qf)) (q' := (pand p qx)) in H.
        eapply lls_mono. eapply vars_locs_mono. 2: eauto.
        unfoldq. intuition.
        unfoldq. intuition.
        unfoldq. intuition.
        unfoldq. intuition. 
    - destruct frx. 2: contradiction. 
      eapply envt_store_deep_wf in Hf_q.
        2: {  eauto. } 2: { unfoldq. intuition. }
        assert False. eapply Hx_fr. eauto. contradiction.
    - destruct frf. 2: contradiction. simpl in Hf_fr. unfold pdiff in Hf_fr.
      rewrite <- lls_change with (M := (st2 M)) in Hx_q. eapply envt_store_deep_wf in Hx_q; eauto. 
      destruct Hf_fr. unfold length1 in Hx_q. contradiction. unfoldq; intuition.
      eapply stchain_tighten. eapply envt_filter_deep; eauto. unfoldq; intuition. 
      eapply st_trans; eauto. 
      eapply envt_store_deep_wf; eauto. unfoldq; intuition. 
      eapply envt_store_deep_wf; eauto. unfoldq; intuition. 
    - destruct frf; destruct frx; simpl in *; unfold pdiff in *; destruct Hf_fr; destruct Hx_fr; try contradiction.
Qed.



(* ---------- store vs store typing reachability ---------- *)


Lemma lls_indexr_closed: forall S M a x1 qt,
    sstore_type S (a::M) ->
    indexr x1 (a::M) = Some qt ->
    psub (plift qt) (pnat (length M)).
Proof.
  intros. destruct H as (STL & STT).
  intros ? ?.
  assert (x1 < length (a::M)). eapply indexr_var_some'. eauto.
  destruct (STT x1) as (qt' & v1 & ? & ? & ? & ?).
  eapply lt_stlocs; eauto. rewrite <- STL. lia.
  rewrite H0 in H2. inversion H2. subst qt'.
  eapply lt_stlocs. eauto. simpl in *. lia. 
Qed.

(*----------- sstore typing lemmas ----------*)

Lemma storet_shrink: forall M S v a,
    sstore_type (v::S) (a::M) ->
    sstore_type S M.
Proof.
  intros. destruct H as (STL & STT).
  assert (length M = length S) as STL1. simpl in STL. lia. 
  split. 
  - eauto.
  - intros. 
    destruct (STT l) as (qt & v' & ? & ? & ? & ?).
    unfoldq. simpl. lia.
    exists qt, v'.
    split. 2: split. 3: split. 
    + rewrite indexr_skip in H0. eauto. unfoldq. lia.  
    + rewrite indexr_skip in H1. eauto. unfoldq. lia. 
    + intros ? ?. eapply lls_shrink.
      split. eauto. eapply STT.
      eapply H2. eauto. eapply lls_extend; eauto.
      
      intros ? ?. unfold pnat in *. eapply H3 in H5. lia.
    + intros. intuition.
Qed.



Lemma plift_lls_z: forall M q x,
    plift q x ->
    plift (locs_locs_stty_fix M q) x.
Proof.
  intros M. induction M; intros.
  - simpl. eauto.
  - simpl. rewrite plift_if1, plift_or.
    destruct (q (length M)). left. eauto. eauto. 
Qed.

Lemma lls_fix_shrink: forall M' M q x,
    psub (plift q) (pnat (length M)) ->
    locs_locs_stty_fix (M'++M) q x = locs_locs_stty_fix M q x.
Proof.
  intros M'. induction M'; intros.
  - simpl. eauto. 
  - simpl. 
    remember (q (length (M' ++ M))). destruct b.
    symmetry in Heqb. eapply H in Heqb.
    unfold pnat in *. rewrite app_length in *. unfoldq. lia. 
    eauto. 
Qed.

Lemma lls_fix_shrink1: forall M a q,
    psub (plift q) (pnat (length M)) ->
    locs_locs_stty_fix (a::M) q = locs_locs_stty_fix M q.
Proof.
  intros. eapply functional_extensionality. intros. 
  replace (a::M) with ([a]++M). eapply lls_fix_shrink. eauto. eauto. 
Qed.

Lemma plift_lls_s: forall M q x x1 qt,
    plift q x1 ->
    indexr x1 M = Some qt ->
    psub (plift qt) (pnat x1) ->
    plift (locs_locs_stty_fix M qt) x ->
    plift (locs_locs_stty_fix M q) x.
Proof.
  intros M. induction M; intros.
  - inversion H0.
  - bdestruct (x1 =? length M).
    + subst x1. rewrite indexr_head in H0. inversion H0. subst a.
      simpl. rewrite H. rewrite plift_or.
      right. rewrite lls_fix_shrink1 in H2. eauto.
      unfoldq. intuition. 
    + simpl. rewrite plift_if1, plift_or.
      rewrite indexr_skip in H0; eauto.
      rewrite lls_fix_shrink1 in H2.
      2: { rewrite indexr_extend1 in H0. unfold pnat in *. unfoldq. intuition. eapply H1 in H0. lia. }
      eapply IHM in H0; eauto.
      remember (q (length M)). destruct b. left. eauto. eauto.
  Unshelve.
  apply qempty.
Qed.

Lemma plift_lls: forall S M q,
    sstore_type S M -> 
    plift (locs_locs_stty_fix M q) = locs_locs_stty M (plift q).
Proof.
  intros. eapply functional_extensionality.
  intros. eapply propositional_extensionality.
  split.
  - intros. generalize dependent q. generalize dependent S. induction M.
    + intros. eapply lls_z. eauto.
    + intros. destruct S. inversion H. inversion H1. 
      simpl in H0.
      remember (q (length M)) as b1.
      assert (sstore_type S M). eapply storet_shrink. eauto.
      destruct b1.
      * rewrite plift_or in H0. destruct H0.
        -- eapply IHM in H0; eauto. destruct H0. eapply lls_z. eauto.
           eapply lls_s. eauto. eapply indexr_extend1 in H2. eapply H2.
           eapply lls_extend. eauto. 
        -- eapply lls_s. symmetry. eauto. eapply indexr_head.
           eapply lls_extend. eauto. 
      * eapply lls_extend. eauto. 
  - intros.
    remember (plift q) as q'.
    generalize dependent q. induction H0.
    + intros. eapply plift_lls_z. subst. eauto.
    + intros. eapply plift_lls_s. subst. eauto. eauto.
      eapply lls_indexr_closed'; eauto. eauto. 
Qed.

Lemma val_locs_stty_decide: forall S M q l,
    sstore_type S M -> 
    locs_locs_stty M (plift q) l \/ ~ locs_locs_stty M (plift q) l.
Proof.
  intros. erewrite <-plift_lls; eauto.
  unfold plift. destruct (locs_locs_stty_fix M q l). eauto. eauto. 
Qed.

(* effect lemmas *)

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

                                                          

(* ---------- compatibility lemmas ---------- *)

Lemma sem_true: forall G p,
    sem_type G ttrue ttrue TBool p false pempty.
Proof.
  intros. intros M H1 H2 WFE STF S1 S2 ST.
  exists S1, S2, M, (vbool true), (vbool true). 
  split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 8: split. 9: split. 
  - exists 1. intros. destruct n. lia. simpl. intuition.
  - exists 1. intros. destruct n. lia. simpl. intuition.
  - eapply st_refl; auto. 
  - eauto.
  - auto.
  - intros ? ?. intuition.
  - intros ? ?. intuition.
  - simpl. eauto. 
  - eapply valq_bool.
  - eapply valq_bool.
Qed.
  
Lemma sem_false: forall G p,
    sem_type G tfalse tfalse TBool p false pempty.
Proof.
  intros. intros M H1 H2 WFE STF S1 S2 ST.
  exists S1, S2, M, (vbool false), (vbool false). 
  split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 8: split. 9: split. 
  - exists 1. intros. destruct n. lia. simpl. intuition.
  - exists 1. intros. destruct n. lia. simpl. intuition.
  - eapply st_refl. auto. 
  - eauto.
  - auto.
  - intros ? ?. intuition.
  - intros ? ?. intuition.
  - simpl. eauto. 
  - eapply valq_bool.
  - eapply valq_bool.
Qed.
  
Lemma sem_var: forall G x T1 (p:pl) fr q,
  indexr x G = Some (T1,fr, q) ->
  p x ->
  sem_type G (tvar x) (tvar x) T1 p false (pone x).
Proof.
  intros. intros M H1 H2 WFE STF S1 S2 ST. 
  eapply WFE in H; auto. remember ST as ST'. clear HeqST'.
  destruct ST as [SST1 [SST2 [SP1 [SP2 SP3]]]].
  remember SST1 as SST1'. remember SST2 as SST2'. clear HeqSST1' HeqSST2'.  
  destruct H as [v1 [v2 [CLQ [IX1 [IX2 [VT [? ?]]]]]]].
  exists S1, S2, M, v1, v2. 
  split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 8: split. 9: split. 
  exists 1. intros. destruct n. lia. simpl. congruence.
  exists 1. intros. destruct n. lia. simpl. congruence.
  eapply st_refl. auto.
  auto.
  eauto.
  intros ? ? ? ?. eauto.
  intros ? ? ? ?. eauto. 
  auto.
  left. eapply lls_mono; eauto. intros ? ?. unfoldq. 
  unfoldq. exists x. intuition. exists v1. intuition.
  left. eapply lls_mono; eauto. intros ? ?. unfoldq. 
  unfoldq. exists x. intuition. exists v2. intuition.
Qed.

Lemma val_locs_wf: forall S M,
  sstore_type S M ->
  forall l v qt,
  indexr l S = Some v ->
  indexr l M = Some qt ->
  psub (val_locs v) (pnat (length M)).
Proof.
  intros S M ST . remember ST as ST'. clear HeqST'. induction ST; intros.
  apply indexr_var_some' in H1 as H1'. 
  destruct (H0 l) as [qt' [v' [? [? [? ?]]]]]; auto.
  rewrite H1 in H4. inversion H4. subst v'.
  rewrite H2 in H3. inversion H3. subst qt'. 
  assert (psub (val_locs v ) (locs_locs_stty M (val_locs v))).
  intros ? ?. left. auto.
  intros ? ?. eapply H7 in H8.
  eapply lls_indexr_closed''' in H2; eauto.
Qed.

Lemma val_reach_wf_store: forall l S M v,
  indexr l S = Some v ->
  sstore_type S M ->
  psub (locs_locs_stty M (val_locs v)) (pdom M).
Proof.
  intros. destruct v. 
  - rewrite val_locs_bool. rewrite lls_empty. unfoldq; intuition. 
  - intros ? ?. eapply val_reach_wf in H; eauto.
  - remember (vabs l0 q t) as vf. intros ? ?. eapply val_reach_wf in H1; eauto.
Qed.


Lemma storet_extend: forall M H1 H2 G p S1 S2 S1' S2' M' q vt v1 v2 qt1 qt2 T
    (WFE: env_type M H1 H2 G p)
    (ST: store_type S1 S2 M)
    (ST1: store_type S1' S2' M')
    (QP: psub (plift q) p)
    (SC1: st_chain M M')
    (QT1: qt1 = vars_locs_fix H1 q)
    (QT2: qt2 = vars_locs_fix H2 q)
    (SC2: st_chain M' (st_extend M' vt qt1 qt2))
    (HVX: val_type M' H1 H2 v1 v2 T T)
    (HQX1: val_qual (st1 M) (st1 M') H1 v1 false (pand p (plift q)))
    (HQX2: val_qual (st2 M) (st2 M') H2 v2 false (pand p (plift q)))
    (VT: vt v1 v2),
    store_type (v1::S1')(v2::S2')(st_extend M' vt qt1 qt2).
Proof. 
  intros. 
  assert (env_type M H1 H2 G (pand p (plift q))) as WFET. eapply envt_tighten; eauto. intros ? ?. unfoldq; intuition.
  eapply envt_store_deep_wf with (q := (pand p (plift q))) in WFET. 2: intros ? ?; unfoldq; intuition.
  destruct WFET as [WFET1 WFET2].
  eapply envt_store_wf with (q := (plift q)) in WFE as WFE'; auto.
  assert (st_filter M' (locs_locs_stty (st1 M') (val_locs v1)) (locs_locs_stty (st2 M') (val_locs v2))) as SFV. {
    eapply valt_filter; eauto.
  }
  destruct WFE' as [WFE1 WFE2]. remember ST as ST'. clear HeqST'. remember ST1 as ST1'. clear HeqST1'.
  destruct ST as [SST1 [SST2 ST]]. destruct ST1 as [? [? ?]].
  remember H as SST1'. remember H0 as SST2'. clear HeqSST1'. clear HeqSST2'.
  remember SC2 as SC2'. clear HeqSC2'. 
  destruct SC2' as [SC2A SC2B].
  assert (length (st1 M) <= length (st1 M')) as L1. eapply st_mono1 in SC1. unfold length1 in *. auto.
  assert (length (st2 M) <= length (st2 M')) as L2. eapply st_mono2 in SC1. unfold length2 in *. auto.
  assert (sstore_type (v1 :: S1') (st1 (st_extend M' vt qt1 qt2))) as SSTA. {
    unfold sstore_type in H, H0, SST1, SST2.  unfold sstore_type. intuition. 
    + unfold length1. simpl. eauto.
    + bdestruct (l <? length S1').
      unfold st_extend. simpl.
      destruct (H11 l) as [qt [v [? [? [? ?]]]]]. auto.
      exists qt, v; intuition.
       bdestruct (l =? length (st1 M')); intuition.
       bdestruct (l =? length S1'); intuition.
       unfold st1. simpl. 
       intros ? ?. auto.
       eapply lls_shrink' in H26; eauto. 
       eapply H24 in H26. eapply lls_extend. auto.
       eapply val_locs_wf; eauto. 

       unfold st_extend. simpl. rewrite <- H10. simpl in H19.
       bdestruct (l =? length S1'); intuition.
       exists qt1, v1; intuition.
       simpl. intros ? ?.
       eapply lls_shrink' in H23. 2: eauto. 2: eapply valt_wf; eauto.
       destruct (HQX1 x) as [H_q | H_fr]. eauto.
        (* q *) subst qt1. rewrite <-plift_vars_locs. erewrite <-lls_change1 with (q2 := (plift qt2)).  eapply lls_mono. 2: eauto. intros ? ?. eapply vars_locs_mono; eauto. unfoldq. intuition. 
        subst qt2. eapply stchain_tighten with (p1 := st_locs1 M') (p2 := st_locs2 M'); eauto.
        assert (env_type M' H1 H2 G p) as WFE'. eapply envt_store_extend; eauto.
        eapply envt_filter_deep in WFE'; eauto. rewrite <- plift_vars_locs. auto.
        eapply envt_store_deep_wf. eapply envt_store_extend. eauto. eauto. eauto. eauto.
        rewrite <-plift_vars_locs. eapply envt_store_deep_wf. eapply envt_store_extend. eauto. eauto. eauto. eauto.
        (* fr *) destruct H_fr.
        subst qt1. intros ? ?. erewrite <- plift_vars_locs in H23.
        unfoldq. eapply WFE1 in H23. subst l. eapply st_mono1 in SC1. unfold length1 in *. simpl in H19. lia.
    }
  assert (sstore_type (v2 :: S2') (st2 (st_extend M' vt qt1 qt2))) as SSTB. {
    unfold sstore_type in H, H0, SST1, SST2.  unfold sstore_type. intuition.
    + simpl. lia. 
    + bdestruct (l <? length S2').
      unfold st_extend. simpl.
      destruct (H12 l) as [qt [v [? [? [? ?]]]]]. auto.
      exists qt, v; intuition.
       bdestruct (l =? length (st2 M')); intuition.
       bdestruct (l =? length S2'); intuition.
       unfold st2. simpl. 
       intros ? ?.
       eapply lls_shrink' in H26; eauto.
       eapply H24 in H26. eapply lls_extend. auto.
       eapply val_locs_wf; eauto. 

       unfold st_extend. simpl.
       rewrite <- H. simpl in H19.  bdestruct (l =? length S2'); intuition.
       exists qt2, v2; intuition.
       simpl. intros ? ?.
       eapply lls_shrink' in H23. 2: eauto. 2: eapply valt_wf; eauto.
       destruct (HQX2 x) as [H_q | H_fr]. eauto.
        (* q *) subst qt2. rewrite <-plift_vars_locs. erewrite <-lls_change2 with (q1 := (plift qt1)).  eapply lls_mono. 2: eauto. intros ? ?. eapply vars_locs_mono; eauto. unfoldq. intuition. 
        subst qt1. eapply stchain_tighten with (p1 := st_locs1 M') (p2 := st_locs2 M'); eauto. 
        assert (env_type M' H1 H2 G p) as WFE'. eapply envt_store_extend; eauto.
        eapply envt_filter_deep in WFE'; eauto. rewrite <- plift_vars_locs. auto.
        intros ? ?. eapply envt_store_deep_wf. eapply envt_store_extend. eauto. eauto. eauto. eauto.
        rewrite plift_vars_locs. eauto. 
        intros ? ?. eapply envt_store_deep_wf. eapply envt_store_extend. eauto. eauto. eauto. eauto. eauto.
        (* fr *) destruct H_fr.
        subst qt2. intros ? ?. erewrite <- plift_vars_locs in H23.
        unfoldq. eapply WFE2 in H23. subst l. eapply st_mono2 in SC1. unfold length2 in *. lia.
  }
  unfold store_type. intuition.
  - unfold st_extend in *. simpl in *.
    unfold strel in H13. simpl in H13. destruct H13.
    destruct H13 as [? ?].
    exists vt, qt1, qt2, v1, v2. repeat split.
    + subst l1. unfold length1. 
      bdestruct (length (st1 M') =? length (st1 M')); intuition.
    + subst l2. unfold length2. 
      bdestruct (length (st2 M') =? length (st2 M')); intuition.
    + subst l1. assert (length1 M' = length S1'). { unfold length1. destruct SST1'; intuition. }
      rewrite H13. bdestruct (length S1' =? length S1'); intuition.
    + subst l2. assert (length2 M' = length S2'). { unfold length2. destruct SST2'; intuition. }
      rewrite H15. bdestruct (length S2' =? length S2'); intuition.
    + eapply functional_extensionality. intros. eapply functional_extensionality. intros.
      eapply propositional_extensionality. split; intros.
      * destruct H16; intuition. destruct H16 as [? [? [? ?]]]. lia.
      * left. intuition.  
    + auto.
    + unfold st1. simpl. unfold st_locs1. eapply lls_closed'; eauto.
      intros ? ?. eapply valt_wf in HVX. destruct HVX as [A B].
      eapply A in H16. unfold pnat in *. unfold length1, st1 in H16. simpl. lia.
    + unfold st2. simpl. unfold st_locs2. eapply lls_closed'; eauto.
      intros ? ?. eapply valt_wf in HVX. destruct HVX as [A B].
      eapply B in H16. unfold pnat in *. unfold length2, st2 in H16. simpl. lia.
    + unfold strel in H16. simpl in H16.
      destruct H16.
      * destruct H16 as [A B]. rewrite <- H13 in A. inversion A. subst l0.
        rewrite <- H15 in B. inversion B. subst l3.
        unfold st1, st2. simpl. intros.
        eapply valt_deep_wf in HVX as HVX'. destruct HVX' as [A B].
        eapply lls_shrink in H18; eauto. eapply A in H18.
        unfold st_locs1, pnat in H18. lia.
        intros ? ?. eapply valt_wf; eauto.
      * unfold st1, st2. simpl. intros.
        eapply lls_shrink in H17; eauto. 
        destruct H3 as [C [D E]]. unfold strel in E. simpl in E.
        assert (st_locs1 M' l0). {
          eapply lls_closed' in H17; eauto. eapply valt_wf; eauto.
        }
        specialize (E l0 l3); intuition. clear H21.
        eapply SFV in H16; intuition. eapply lls_extend; eauto.
        eapply valt_wf; eauto.
    + unfold strel in H16. simpl in H16.
      destruct H16.
      * destruct H16 as [A B]. rewrite <- H13 in A. inversion A. subst l0.
        rewrite <- H15 in B. inversion B. subst l3.
        unfold st1, st2. simpl. intros.
        eapply valt_deep_wf in HVX as HVX'. destruct HVX' as [A B].
        eapply lls_shrink in H18; eauto. eapply B in H18.
        unfold st_locs2, pnat in H18. lia.
        intros ? ?. eapply valt_wf; eauto.
      * unfold st1, st2. simpl. intros.
        eapply lls_shrink in H17; eauto. 
        destruct H3 as [C [D E]]. unfold strel in E. simpl in E.
        assert (st_locs2 M' l3). {
          eapply lls_closed' in H17; eauto. eapply valt_wf; eauto.
        }
        specialize (E l0 l3); intuition. clear H19.
        eapply SFV in H16; intuition. eapply lls_extend; eauto.
        eapply valt_wf; eauto.
    + eapply H6 in H13 as H13'.  destruct H13' as [vt' [qt1' [qt2' [v1' [v2' ?]]]]]; intuition.
      exists vt', qt1', qt2', v1', v2'; intuition.
      * apply indexr_var_some' in H16 as H16'. bdestruct (l1 =? length (st1 M')); intuition.
      * apply indexr_var_some' in H15 as H15'. bdestruct (l2 =? length (st2 M')); intuition.
      * apply indexr_var_some' in H17 as H17'. bdestruct (l1 =? length S1'); intuition.
      * apply indexr_var_some' in H18 as H18'. bdestruct (l2 =? length S2'); intuition.
      * eapply functional_extensionality. intros. eapply functional_extensionality. intros.
        eapply propositional_extensionality. split; intros.
        ** destruct H21.
           *** destruct H21 as [? [? ?]]. apply indexr_var_some' in H16. unfold length1 in H21. lia.
           *** destruct H21 as [? [? [? [? ?]]]]. rewrite H19 in H24. subst x1. auto.
        ** right. exists vt'. intuition. apply indexr_var_some' in H16. unfold length1. lia.
           apply indexr_var_some' in H15. unfold length2. lia. 
      * (* st_filter *)
        destruct H22 as [STF1 [STF2 STF3]].
        repeat split.
        ** unfold st1, st_locs1, pnat, length1. simpl. intros ? ?.
           eapply lls_shrink in H21; eauto. eapply STF1 in H21. unfold st_locs1, pnat, length1, st1 in H21. lia.
           intros ? ?.  eapply lls_z with (M :=  (st1 M')) in H22; eauto. eapply STF1. auto.
        ** unfold st2, st_locs2, pnat, length2. simpl. intros ? ?.
           eapply lls_shrink in H21; eauto. eapply STF2 in H21. unfold st_locs2, pnat, length2, st2 in H21. lia.
           intros ? ?.  eapply lls_z with (M :=  (st2 M')) in H22; eauto. eapply STF2. auto.
        ** unfold strel in H21. simpl in H21. destruct H21 as [[? ?] | ?].
           *** unfold st1, st2. simpl. intros. subst l0 l3. eapply lls_shrink in H23; eauto.
               eapply STF1 in H23.  unfold st_locs1 in H23. unfoldq; intuition.
               intros ? ?.  eapply lls_z with (M := st1 M') in H21.  eapply STF1 in H21. unfold st_locs1 in H21. unfold pnat, length1, st1 in *. lia. 
           *** unfold st1, st2. simpl. intros ?. eapply lls_shrink in H22; eauto.
               specialize (STF3 l0 l3); intuition. eapply lls_extend; eauto.
               intros ? ?.  eapply lls_z with (M :=  (st1 M')) in H23; eauto. eapply STF1. auto.
        ** unfold strel in H21. simpl in H21. unfold st1, st2. simpl. intros. destruct H21 as [[? ?] | ?].
           *** subst l0 l3. eapply lls_shrink in H22; eauto. eapply STF2 in H22. unfold st_locs2 in H22. unfoldq; intuition.
               intros ? ?.  eapply lls_z with (M := st2 M') in H21.  eapply STF2 in H21. unfold st_locs2 in H21. unfold pnat, length2, st2 in *. lia.
           *** eapply lls_shrink in H22; eauto.
               specialize (STF3 l0 l3); intuition. eapply lls_extend; eauto.
               intros ? ?.  eapply lls_z with (M :=  (st2 M')) in H23; eauto. eapply STF2. auto.
  -  (* right unique *)
    unfold strel in H13, H15. simpl in H13, H15.
    destruct H13; destruct H15.
    + destruct H13 as [? ?]. destruct H15 as [? ?]. congruence.
    + destruct H13 as [? ?]. 
      edestruct H6 as [vt' [qt1' [qt2' [v1' [v2' [IM1 [IM2 [IS1 [IS2 [STVT [VT' STF']]]]]]]]]]]; eauto.
      subst l1. apply indexr_var_some' in IM1. unfold length1 in IM1. lia.
    + destruct H15 as [? ?].  
      edestruct H6 as [vt' [qt1' [qt2' [v1' [v2' [IM1 [IM2 [IS1 [IS2 [STVT [VT' STF']]]]]]]]]]]; eauto.
      subst l1. apply indexr_var_some' in IM1. unfold length1 in IM1. lia. 
    + eapply H5; eauto.
  - (* left unique *)
    unfold strel in H13, H15. simpl in H13, H15.
    destruct H13; destruct H15.
    + destruct H13 as [? ?]. destruct H15 as [? ?]. congruence.
    + destruct H13 as [? ?]. 
      edestruct H6 as [vt' [qt1' [qt2' [v1' [v2' [IM1 [IM2 [IS1 [IS2 [STVT [VT' STF']]]]]]]]]]]; eauto.
      apply indexr_var_some' in IM2. unfold length2 in H16. lia.
    + destruct H15 as [? ?].  
      edestruct H6 as [vt' [qt1' [qt2' [v1' [v2' [IM1 [IM2 [IS1 [IS2 [STVT [VT' STF']]]]]]]]]]]; eauto.
      apply indexr_var_some' in IM2. unfold length2 in H16. lia. 
    + eapply H11; eauto.
Qed.

Lemma sem_ref: forall t1 t2 G T p q,
    sem_type G t1 t2 T p false (plift q) ->
    psub (plift q) p ->
    sem_type G (tref t1) (tref t2)(TRef T false q) p true (plift q).
Proof.
  intros. intros M H1 H2 WFE STF S1 S2 ST.
  eapply wf_env_type in WFE as WFE'.
  destruct WFE' as [ L1 [L2 [P1 [P2 [P3 P4]]]]].
  destruct (H M H1 H2 WFE STF S1 S2 ST) as [S1' [S2' [M' [v1 [v2 IE]]]]].
  destruct IE as [IE1 [IE2 [STC [SF1 [ST1 [SP1 [SP2 [HV [HQ1 HQ2]]]]]]]]].
  remember ST1 as ST1'. clear HeqST1'.
  destruct ST1 as [[SL1 SSP1] [[SL2 SSP2][SP3 [U L]]]].
  remember HV as  HV'. clear HeqHV'.
  remember (length S1) as x.
  remember (fun v1 v2  => val_type M' H1 H2 v1 v2 T T) as vt.
  
  remember (vars_locs_fix H1 q) as qt1.
  remember (vars_locs_fix H2 q) as qt2.
  assert (st_chain M' (st_extend M' vt qt1 qt2)). {
    assert (st_chain_partial M' (st_extend M' vt qt1 qt2)
                (st_locs1 M') (st_locs2 M')). {
      unfold st_chain_partial. split. auto. split. 
      {
        repeat split. 
        intros ? ?. unfold st_extend, st_locs1, pnat, length1 in *. simpl. lia.
        intros ? ?. unfold st_extend, st_locs2, pnat, length2 in *. simpl. lia.
        intros. simpl in H3. destruct H3. destruct H3 as [? ?].
        subst l1. unfold st_locs1, pnat in H4. lia. eapply SF1; eauto.
        intros. simpl in H3. destruct H3. destruct H3 as [? ?].
        subst l2. unfold st_locs2, pnat in H4. lia. eapply SF1; eauto.
      }
      repeat split.
      unfoldq; intuition.
      intros ? ?. unfold st_extend, pdom. simpl. unfold st_locs1, pnat, length1 in *. lia.
      intros ? ?. unfold st_extend. simpl. unfold st_locs1, pnat, length1 in *.
      bdestruct (l =? length (st1 M')); intuition.
      unfoldq; intuition.
      intros ? ?. unfold st_extend, pdom. simpl. unfold st_locs2, pnat, length2 in *. lia.
      intros ? ?. unfold st_extend. simpl. unfold st_locs2, pnat, length2 in *.
      bdestruct (l =? length (st2 M')); intuition.
      intros. simpl. 
      eapply functional_extensionality. intros. eapply functional_extensionality. intros.
      unfold st_locs1, pnat in H. unfold st_locs2, pnat in *. 
      eapply propositional_extensionality. split. intros. right. 

      exists (st_valtype M' l1 l2). intuition.
      intros.  destruct H6. 
      destruct H6 as [? [? ?]]. lia.
      destruct H6 as [? [? [? [? ?]]]]. subst x2. auto. 
      intros. unfold st_extend. unfold strel. simpl. right. auto.
      unfold st_extend, strel. simpl. intros. destruct H4 as [[? ?] | ?].
      destruct H3 as [? ?]. unfold st_locs1, pnat in *. lia.
      auto.
    }

    unfold st_chain. intuition.
  }
    
  exists (v1::S1'), (v2::S2'), (st_extend M' vt qt1 qt2).
  exists (vref (length S1')), (vref (length S2')).

  split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 8: split. 9: split.

  + (* 1st term *)
    destruct IE1 as [n1 IE1].
    exists (S n1). intros. destruct n. lia. simpl. rewrite IE1.  auto. lia.
  
  + (* 2nd term *)
    destruct IE2 as [n2 IE2].
    exists (S n2). intros. destruct n. lia. simpl. rewrite IE2. auto. lia.
  
  + (* st_chain *)
    eapply st_trans. eauto. eapply stchain_extend. auto.
  
  + repeat split.
    - intros ? ?. auto.
    - intros ? ?. auto.
    - unfold st_locs1, st_locs2, pnat, length1, length2. simpl. simpl in H3.
      intros. destruct H4. destruct H4 as [? ?]. subst l2. unfold length2. lia. 
      destruct (SP3 l1 l2) as [vt' [frt1 [frt2 [qt1' [qt2' [v1' [v2' [IM1 [IM2 ?]]]]]]]]]; auto.
      apply indexr_var_some' in IM2. lia.
    - simpl in H4. destruct H4. destruct H4. intros. unfold st_locs1, pnat, length1. simpl. unfold length1 in H4. lia.
      unfold st_locs1, st_locs2, pnat, length1, length2. simpl. intros.
      destruct (SP3 l1 l2) as [vt' [frt1 [frt2 [qt1' [qt2' [v1' [v2' [IM1 [IM2 ?]]]]]]]]]; auto.
      apply indexr_var_some' in IM1. lia.
  + (* store_typing *)
    eapply storet_extend; eauto. subst vt. auto.
  
  + eapply se_trans. eauto. intros ? ?. intros. eapply indexr_extend1 in H5. eapply H5.
  
  + eapply se_trans. eauto. intros ? ?. intros. eapply indexr_extend1 in H5. eapply H5.
  

  + (* result type *)
    remember ((st_extend M' vt qt1 qt2)) as M2.
    assert (store_type (v1::S1')(v2::S2') (M2)) as ST2. {
      subst M2. eapply storet_extend. 2: eapply ST. all: eauto.
      subst vt. auto. 
    }
    assert (psub (plift qt1) (st_locs1 M')) as KM1. {
      subst qt1. rewrite <-plift_vars_locs. eapply envt_store_wf; eauto.
      eapply envt_store_extend; eauto.
    }

    assert (psub (plift qt2) (st_locs2 M')) as KM2. {
      subst qt2. rewrite <-plift_vars_locs. eapply envt_store_wf; eauto.
      eapply envt_store_extend; eauto.
    }

  simpl. split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 8: split. 
  - eapply valt_closed in HV'; intuition.
  - eapply valt_closed in HV'; intuition.
  - auto.
  - auto.
  - unfoldq; intuition.
  - unfoldq; intuition.
  - subst M2. simpl. left. intuition. 
  - split. 2: split.
    * rewrite val_locs_ref in *. intros ? ?. 
    rewrite SL1 in H4. inversion H4. subst M0 q0 x0 M2. 
    unfold st1, st_extend, st_locs1, length1, pnat. simpl.
    unfold pone in H5. lia. 
    subst M0 q0 x1 M2 x. unfold pone in H5. subst x2.
    unfold st_extend in H6. simpl in H6.
    bdestruct (length (st1 M') =? (length (st1 M'))); intuition.
    inversion H6. subst qt. 
    unfold st_locs1, st_extend, pnat, length1. simpl.
    eapply lls_shrink in H7; eauto.
    eapply lls_closed' in H7; eauto. 
    destruct ST1'.  eapply s. destruct ST2. eauto.

    * rewrite val_locs_ref in *. intros ? ?. 
    rewrite SL2 in H4. inversion H4. subst M0 q0 x0 M2. 
    unfold st2, st_extend, st_locs2, length2, pnat. simpl.
    unfold pone in H5. lia. 
    subst M0 q0 x1 M2 x. unfold pone in H5. subst x2.
    unfold st_extend in H6. simpl in H6.
    bdestruct (length (st2 M') =? (length (st2 M'))); intuition.
    inversion H6. subst qt. 
    unfold st_locs2, st_extend, pnat, length2. simpl.
    eapply lls_shrink in H7; eauto.
    eapply lls_closed' in H7; eauto. 
    destruct ST1' as [? [? ?]].  eapply s0. destruct ST2 as [? [? ?]]. eauto.
    * intros. repeat rewrite val_locs_ref. subst M2. unfold st1, st2, st_extend in *. simpl in *. 
    unfold strel in H4. simpl in H4. destruct H4 as [[? ?] | ?]. 
    ** split. intros. left. subst l2. unfoldq; intuition.
       intros. left. subst l1. unfoldq; intuition.
    ** destruct ST2 as [ST2A [ST2B ST2C]].
       split. intros. edestruct (SP3 l1 l2) as [vt' [frt1 [frt2 [qt1' [qt2' [v1'' [v2'' [IM1 [IM2 [IS1 [IS2 VT]]]]]]]]]]]; auto.
       inversion H5. subst. unfold pone in H6. apply indexr_var_some' in IM1. lia.
       subst. eapply lls_shrink in H8 as H8'.       
       eapply lls_s in H8. 3: eauto. 2: eauto.
       eapply lls_s with (x1 := (length S2')); eauto.
       unfoldq; intuition. rewrite SL2. rewrite indexr_head. eauto.
       eapply lls_extend; eauto.
       unfold pone in H6. subst x1.
       rewrite SL1 in H7. rewrite indexr_head in H7. inversion H7.
       subst qt. rewrite <- plift_vars_locs in *. 
       eapply envt_same_locs; eauto. eapply envt_store_extend; eauto. 
       eauto. unfold pone in H6. subst x1.
       rewrite SL1 in H7. unfold st1 in H7. rewrite indexr_head in H7.
       inversion H7. subst. rewrite <- plift_vars_locs.
       eapply envt_store_wf with (q := (plift q)). eapply envt_store_extend. eauto. eauto. auto. auto. 
       
       intros. edestruct (SP3 l1 l2) as [vt' [frt1 [frt2 [qt1' [qt2' [v1'' [v2'' [IM1 [IM2 [IS1 [IS2 VT]]]]]]]]]]]; auto.
       inversion H5. subst. unfold pone in H6. apply indexr_var_some' in IM2. lia.
       subst. eapply lls_shrink in H8 as H8'.       
       eapply lls_s in H8. 3: eauto. 2: eauto.
       eapply lls_s with (x1 := (length S1')); eauto.
       unfoldq; intuition. rewrite SL1. rewrite indexr_head. eauto.
       eapply lls_extend; eauto.
       unfold pone in H6. subst x1.
       rewrite SL2 in H7. rewrite indexr_head in H7. inversion H7.
       subst qt. rewrite <- plift_vars_locs in *. 
       eapply envt_same_locs; eauto. eapply envt_store_extend; eauto. 
       eauto. unfold pone in H6. subst x1.
       rewrite SL2 in H7. unfold st2 in H7. rewrite indexr_head in H7.
       inversion H7. subst. rewrite <- plift_vars_locs.
       eapply envt_store_wf with (q := (plift q)). eapply envt_store_extend. eauto. eauto. auto. auto. 
       
  - exists vt, qt1, qt2.
    split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 
    -- subst M2. rewrite SL1. unfold st1 at 2, st_extend. simpl.
       bdestruct (length (st1 M') =? length (st1 M')); intuition.
    
    -- subst M2. rewrite SL2. unfold st2 at 2, st_extend. simpl.
       bdestruct (length (st2 M') =? length (st2 M')); intuition.
    
    -- subst vt. subst M2. unfold st_extend. 
       eapply functional_extensionality. intros. eapply functional_extensionality. intros. simpl.
       eapply propositional_extensionality. split. intros.
       intuition. destruct H5 as [? [? [? [? ?]]]]. unfold length1 in H4. lia.  intros. intuition.
    -- intros M3.  intros.
       remember H3 as STC'. clear HeqSTC'. 
       destruct H3 as [STC1' STC2'].
       remember (plift qt1) as qt1'. remember (plift qt2) as qt2'.

         assert (psub (locs_locs_stty (st1 M') qt1') (st_locs1 M')). {
           subst qt1' qt1. rewrite <-plift_vars_locs. eapply envt_store_deep_wf.
           eapply envt_store_extend. eauto. eauto. eauto. auto.
         }

         assert (psub (locs_locs_stty (st2 M') qt2') (st_locs2 M')). {
           subst qt2' qt2. rewrite <-plift_vars_locs. eapply envt_store_deep_wf.
           eapply envt_store_extend. eauto. eauto. eauto. auto.
         }

         assert (st_chain_partial M' M2 (locs_locs_stty (st1 M') qt1') (locs_locs_stty (st2 M') qt2')). {
           eapply stchain_tighten; eauto. 
           split. 2: split.
           * auto.
           * auto.
           * intros. destruct H4 as [SFA [SFB SC]].
             destruct SFA as [? [? X]]. 
             assert (strel M2 l1 l2). {
               subst M2. simpl. right. auto.
             }
             eapply X in H12. split.
             intros. subst M2. unfold st1, st2, st_extend in H12. simpl in H12.
             eapply lls_extend with (a := qt1) in H13. intuition.
             eapply lls_shrink in H12; eauto. destruct ST2 as [? [? ?]]; eauto.
             intros. subst M2. unfold st1, st2, st_extend in H12. simpl in H12.
             eapply lls_extend with (a := qt2) in H13. intuition.
             eapply lls_shrink in H12; eauto. destruct ST2 as [? [? ?]]; eauto.
         }

         
         assert (locs_locs_stty (st1 M3) qt1' = locs_locs_stty (st1 M2) qt1') as L321. {
           erewrite <- lls_change1. eauto. eauto. 
         }
         assert (locs_locs_stty (st2 M3) qt2' = locs_locs_stty (st2 M2) qt2') as L322. {
           erewrite <-lls_change2. eauto. eauto.  
         }

         assert (locs_locs_stty (st1 M2) qt1' = locs_locs_stty (st1 M') qt1') as L211. {
           erewrite <- lls_change1 with (q2 := qt2'). eauto. eapply stchain_tighten; eauto. 
           eapply H10.
           intros ? ?. auto. intros ? ?. auto.
         }

         assert (locs_locs_stty (st2 M2) qt2' = locs_locs_stty (st2 M') qt2') as L212. {
           erewrite <- lls_change2 with (q1 := qt1'). eauto. eapply stchain_tighten; eauto.
           eapply H10.
           intros ? ?. auto. intros ? ?. auto.
         }

         assert (st_chain_partial M' M3 (locs_locs_stty (st1 M') qt1')(locs_locs_stty (st2 M') qt2')). {
           eapply st_trans''. eapply stchain_tighten. eauto.
           eapply H10. eauto.
           intros ? ?. auto. intros ? ?. auto.
           rewrite <- L211. rewrite <- L212. auto.
           auto. auto. 
         }
         

         assert (st_chain_partial M' M3 (locs_locs_stty (st1 M3) qt1') (locs_locs_stty (st2 M3) qt2')). {
           rewrite L321, L211. rewrite L322, L212. auto.
         }

         
         assert (st_chain_partial M3 M' (locs_locs_stty (st1 M3) qt1') (locs_locs_stty (st2 M3) qt2')). {
           eapply stchain_symmetry. auto. 
         }
               
         
        assert (st_chain_partial M3 M' (locs_locs_stty (st1 M3) (val_locs v1')) (locs_locs_stty (st2 M3) (val_locs v2'))). {
           eapply stchain_tighten.  auto. 
           eauto. eauto. eauto. 
         }

         
         
         assert (psub (locs_locs_stty (st1 M3) (val_locs v1')) (locs_locs_stty (st1 M') qt1')). {
           rewrite <-L211, <-L321. eauto. 
         }

         assert (psub (locs_locs_stty (st2 M3) (val_locs v2')) (locs_locs_stty (st2 M') qt2')). {
           rewrite <-L212, <-L322. eauto. 
         }
         
         assert (st_chain_partial M3 M' (locs_locs_stty (st1 M') (val_locs v1')) (locs_locs_stty (st2 M') (val_locs v2'))). {
           erewrite <-lls_change1.  erewrite <- lls_change2. eauto. eauto. eauto. 
         }

         assert (st_chain_partial M' M3 (locs_locs_stty (st1 M3) (val_locs v1')) (locs_locs_stty (st2 M3) (val_locs v2'))). {
           eapply stchain_symmetry. auto.
         }
         

         assert (st_chain_partial M' M3 (locs_locs_stty (st1 M') (val_locs v1')) (locs_locs_stty (st2 M') (val_locs v2'))). {
           erewrite <- lls_change1. erewrite <- lls_change2. eauto. eauto. eauto.  
         }
   
        
        subst vt. split; intros.
        eapply valt_store_change. 2: eapply H20. eauto. eauto. 
        eapply valt_store_change. 2: eapply H20. eauto. eauto. 
    -- intros. subst qt1. rewrite plift_vars_locs. auto.
    -- intros. subst qt2. rewrite plift_vars_locs. auto.
    -- intros ? ?. subst x M2. eapply lls_s. unfoldq. eauto. 
         unfold st_extend. simpl. bdestruct (length S1' =? length (st1 M')); intuition.
         auto.
    -- intros ? ?. subst x M2. eapply lls_s. unfoldq. eauto. 
         unfold st_extend. simpl. bdestruct (length S2' =? length (st2 M')); intuition.
         auto.
  + (* valq 1 *)
    intros ? ?. inversion H4.
    * right. simpl. subst x1 q0 M0. rewrite val_locs_ref in *.
      unfold pone in H5. subst x x0. unfold pdiff, pnat. unfoldq.
      simpl. rewrite SL1. split.  eapply st_mono1 in H3. unfold length1 in H3. lia.
      eapply st_mono1 in STC.  unfold length1 in STC. lia.
    * left. simpl. subst x1 q0 M0. rewrite val_locs_ref in *.
      unfold pone in H5. subst x x2. unfold st_extend in *.
      unfold st1 in *. simpl in *. rewrite SL1 in H6.
      bdestruct (length (fst (fst (fst M'))) =? length (fst (fst (fst M')))); intuition.
      inversion H6.  subst qt. 
      eapply lls_mono. 2: eapply H7. subst qt1. rewrite <-plift_vars_locs. 
      intros ? ?. eapply vars_locs_mono; eauto. unfoldq; intuition.
  + (* valq 2 *)
    intros ? ?. inversion H4.
    * right. simpl. subst x1 q0 M0. rewrite val_locs_ref in *.
      unfold pone in H5. subst x x0. unfold pdiff, pnat. unfoldq.
      simpl. rewrite SL2. split.  eapply st_mono2 in H3. unfold length1 in H3. lia.
      eapply st_mono2 in STC.  unfold length2 in STC. lia.
    * left. simpl. subst x1 q0 M0. rewrite val_locs_ref in *.
      unfold pone in H5. subst x x2. unfold st_extend in *.
      unfold st2 in *. simpl in *. rewrite SL2 in H6.
      bdestruct (length (snd (fst (fst M'))) =? length (snd (fst (fst M')))); intuition.
      inversion H6.  subst qt. 
      eapply lls_mono. 2: eapply H7. subst qt2. rewrite <-plift_vars_locs. 
      intros ? ?. eapply vars_locs_mono; eauto. unfoldq; intuition.
Qed.



Lemma sem_get1: forall t1 t2 env T p q1 fr q,
    sem_type env t1 t2 (TRef T false q1) p fr q ->
    psub (plift q1) p ->
    sem_type env (tget t1) (tget t2) T p false (plift q1).
Proof.
  intros. intros M H1 H2 WFE STF S1 S2 ST.
  destruct (H M H1 H2 WFE STF S1 S2 ST) as [S1' [S2' [M' [v1 [v2 IE]]]]].
  destruct IE as [IE1 [IE2 [STC [STF' [ST' [SE1 [SE2 [HV [HQ1 HQ2]]]]]]]]]. 
  remember HV as HV'. clear HeqHV'.
  destruct v1; destruct v2; try solve [inversion HV]. simpl in HV.
  
  destruct HV as [HT [HT' [F1 [F2 [SUB1 [SUB2 [STREL [STF'' ?]]]]]]]].
  remember ST' as ST''. clear HeqST''.
  destruct ST' as [SST1 [SST2 [SP1 [R L]]]].

  assert (strel M' i i0) as A. eauto.
 
  destruct (SP1 i i0 A) as [vt [qt1 [qt2 [v1 [v2 [IM1 [IM2 [IS1 [IS2 [STVT [VT STFV]]]]]]]]]]]. 

  destruct H3 as [vt' [qt1' [qt2' [IM1' [IM2' [STVALT [VT1 ?]]]]]]]; intuition.
  rewrite IM1 in IM1'. inversion IM1'. subst qt1'.
  rewrite IM2 in IM2'. inversion IM2'. subst qt2'.
  
  exists S1', S2', M', v1, v2. 
  split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 8: split. 9: split.
  + destruct IE1 as [n1 IW1].
    exists (S n1). intros. destruct n. lia. simpl.
    rewrite IW1. rewrite IS1. eauto. lia.
  + destruct IE2 as [n1 IW2].
    exists (S n1). intros. destruct n. lia. simpl.
    rewrite IW2. rewrite IS2. eauto. lia.
  + (* st_chain *) eauto. 
  + (* st_filter *) eauto.
  + (* store_type *) eauto.
  + (* effect 1 *) eauto.
  + (* effect 2 *) eauto. 
  + (* valt *)
    assert (st_chain M' M'). eapply st_refl; eauto.
    eapply valt_store_extend.  2: eapply VT1. eapply ST''. 2: eapply ST''.
    eapply stchain_tighten; eauto. eapply indexr_filter; eauto.
    eapply valt_filter in HV' as B. repeat rewrite val_locs_ref in B. auto.
    eapply lls_indexr_closed'''; eauto. eapply lls_indexr_closed'''; eauto.
    auto.
    destruct SST1 as (X & Y). destruct (Y i) as [qt1' [v' [IM1'' [IS1' [? ?]]]]].
    apply indexr_var_some' in IS1. lia.   
    rewrite IM1 in IM1''.  inversion IM1''. subst qt1'.
    rewrite IS1 in IS1'. inversion IS1'. subst v'. eapply H8. 
    destruct SST2 as (X & Y). destruct (Y i0) as [qt2' [v2' [IM2'' [IS2' [? ?]]]]].
    apply indexr_var_some' in IS2. lia. rewrite IM2 in IM2''.  inversion IM2''. subst qt2'.
    rewrite IS2 in IS2'. inversion IS2'. subst v2'. eapply H8. 
    rewrite STVALT in STVT. subst. 
    auto. auto.
    
  + intros ? ?.  left. 
    destruct SST1 as (X & Y). destruct (Y i) as [qt1' [v' [IM1'' [IS1' [? ?]]]]].
    apply indexr_var_some' in IS1. lia. rewrite IM1 in IM1''.  inversion IM1''. subst qt1'.
    rewrite IS1 in IS1'. inversion IS1'. subst v'.
    eapply H8 in H6; eauto. rewrite H4 in H6. eapply lls_mono; eauto. eapply vars_locs_mono. unfoldq; intuition. 

  + intros ? ?.  left. 
    destruct SST2 as (X & Y). destruct (Y i0) as [qt2' [v' [IM2'' [IS2' [? ?]]]]].
    apply indexr_var_some' in IS2. lia. rewrite IM2 in IM2''.  inversion IM2''. subst qt2'.
    rewrite IS2 in IS2'. inversion IS2'. subst v'.
    eapply H8 in H6; eauto. rewrite H3 in H6. eapply lls_mono; eauto. eapply vars_locs_mono. unfoldq; intuition. 
Qed.

(* like with functions, we want a second rule where the result is aliased
   with the ref -- this is necessary for refs to go out of scope *)
Lemma sem_get2: forall t1 t2 env T p rf1 q1 fr q,
    sem_type env t1 t2 (TRef T rf1 q1) p fr q ->
    sem_type env (tget t1) (tget t2) T p fr q.
Proof.
  intros. intros M H1 H2 WFE STF S1 S2 ST.
  destruct (H M H1 H2 WFE STF S1 S2 ST) as [S1' [S2' [M' [v1 [v2 IE]]]]].
  destruct IE as [IE1 [IE2 [STC [STF' [ST' [SE1 [SE2 [HV [HQ1 HQ2]]]]]]]]]. 
  remember HV as HV'. clear HeqHV'.
  destruct v1; destruct v2; try solve [inversion HV]. simpl in HV.
  
  destruct HV as [HT [HT' [F1 [F2 [SUB1 [SUB2 [STREL [? ?]]]]]]]].
  remember ST' as ST''. clear HeqST''.
  destruct ST' as [STL1 [STL2 [SP1 [SP2 SP3]]]].

  assert (strel M' i i0) as A. eauto.
 
  destruct (SP1 i i0 A) as [vt [qt1 [qt2 [v1 [v2 [IM1 [IM2 [IS1 [IS2 [SVT [VT STFV]]]]]]]]]]]. 

  destruct H3 as [vt' [qt1' [qt2' [IM1' [IM2'[SVT' [VT' ?]]]]]]]; intuition.
  rewrite IM1 in IM1'. inversion IM1'. subst qt1'.
  rewrite IM2 in IM2'. inversion IM2'. subst qt2'.
  
  exists S1', S2', M', v1, v2. 
  split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 8: split. 9: split.
  + destruct IE1 as [n1 IW1].
    exists (S n1). intros. destruct n. lia. simpl.
    rewrite IW1. rewrite IS1. eauto. lia.
  + destruct IE2 as [n1 IW2].
    exists (S n1). intros. destruct n. lia. simpl.
    rewrite IW2. rewrite IS2. eauto. lia.
  + eauto.
  + eauto.
  + eauto.
  + eauto.
  + eauto. 
  + assert (st_chain M' M'). eapply st_refl; eauto.
    eapply valt_store_extend.  2: eapply VT'. eapply ST''. 2: eapply ST''.
    eapply stchain_tighten; eauto. eapply indexr_filter; eauto.
    eapply valt_filter in HV' as B. repeat rewrite val_locs_ref in B. auto.
    eapply lls_indexr_closed'''; eauto. eapply lls_indexr_closed'''; eauto.
    auto.
    destruct STL1 as (X & Y). destruct (Y i) as [qt1' [v' [IM1'' [IS1' [? ?]]]]].
    apply indexr_var_some' in IS1. lia. rewrite IM1 in IM1''.  inversion IM1''. subst qt1'.
    rewrite IS1 in IS1'. inversion IS1'. subst v'. eapply H8. auto.
    destruct STL2 as (X & Y). destruct (Y i0) as [qt2' [v2' [IM2'' [IS2' [? ?]]]]].
    apply indexr_var_some' in IS2. lia. rewrite IM2 in IM2''.  inversion IM2''. subst qt2'.
    rewrite IS2 in IS2'. inversion IS2'. subst v2'. eapply H8. auto.
    rewrite SVT in SVT'. subst. auto.
    auto.
    
  + intros ? ?. eapply HQ1. rewrite val_locs_ref. 
    eapply lls_s; eauto. unfoldq; intuition.
    destruct STL1 as (X & Y). destruct (Y i) as [qt1' [v' [IM1'' [IS1' [? ?]]]]].
    apply indexr_var_some' in IS1. lia. rewrite IM1 in IM1''.  inversion IM1''. subst qt1'.
    rewrite IS1 in IS1'. inversion IS1'. subst v'. intuition. 
    
  + intros ? ?. eapply HQ2. rewrite val_locs_ref. 
    eapply lls_s; eauto. unfoldq; intuition.
    destruct STL2 as (X & Y). destruct (Y i0) as [qt2' [v' [IM2'' [IS2' [? ?]]]]].
    apply indexr_var_some' in IS2. lia. rewrite IM2 in IM2''.  inversion IM2''. subst qt2'.
    rewrite IS2 in IS2'. inversion IS2'. subst v'. intuition. 
Qed.

Lemma sem_get: forall t1 t2 env T p q1 rf1 fr q,
    sem_type env t1 t2 (TRef T rf1 q1) p fr q ->
    psub (plift q1) p ->
    sem_type env (tget t1) (tget t2) T p (if rf1 then fr else false) (por (plift q1) (pif rf1 q)).
Proof.
  intros. intros M H1 H2 WFE STF S1 S2 ST.
  destruct (H M H1 H2 WFE STF S1 S2 ST) as [S1' [S2' [M' [v1 [v2 IE]]]]].
  destruct IE as [IE1 [IE2 [STC [STF' [ST' [SE1 [SE2 [HV [HQ1 HQ2]]]]]]]]]. 
  remember HV as HV'. clear HeqHV'.
  destruct v1; destruct v2; try solve [inversion HV]. simpl in HV.
  
  destruct HV as [HT [HT' [F1 [F2 [SUB1 [SUB2 [STREL [? ?]]]]]]]].
  remember ST' as ST''. clear HeqST''.
  destruct ST' as [STL1 [STL2 [SP1 [SP2 SP3]]]].

  assert (strel M' i i0) as A. eauto.
 
  destruct (SP1 i i0 A) as [vt [qt1 [qt2 [v1 [v2 [IM1 [IM2 [IS1 [IS2 [SVT [VT SFT]]]]]]]]]]]. 

  destruct H4 as [vt' [qt1' [qt2' [IM1' [IM2'[SVT' [VT' ?]]]]]]]; intuition.
  rewrite IM1 in IM1'. inversion IM1'. subst qt1'.
  rewrite IM2 in IM2'. inversion IM2'. subst qt2'.
  
  exists S1', S2', M', v1, v2. 
  split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 8: split. 9: split.
  + destruct IE1 as [n1 IW1].
    exists (S n1). intros. destruct n. lia. simpl.
    rewrite IW1. rewrite IS1. eauto. lia.
  + destruct IE2 as [n1 IW2].
    exists (S n1). intros. destruct n. lia. simpl.
    rewrite IW2. rewrite IS2. eauto. lia.
  + eauto.
  + eauto.
  + eauto.
  + eauto.
  + eauto. 
  + assert (st_chain M' M'). eapply st_refl; eauto.
    eapply valt_store_extend.  2: eapply VT'. eapply ST''. 2: eapply ST''.
    eapply stchain_tighten; eauto. eapply indexr_filter; eauto.
    eapply valt_filter in HV' as B. repeat rewrite val_locs_ref in B. auto.
    eapply lls_indexr_closed'''; eauto. eapply lls_indexr_closed'''; eauto.
    auto.
    destruct STL1 as (X & Y). destruct (Y i) as [qt1' [v' [IM1'' [IS1' [? ?]]]]].
    apply indexr_var_some' in IS1. lia. rewrite IM1 in IM1''.  inversion IM1''. subst qt1'.
    rewrite IS1 in IS1'. inversion IS1'. subst v'. eapply H9. auto.
    destruct STL2 as (X & Y). destruct (Y i0) as [qt2' [v2' [IM2'' [IS2' [? ?]]]]].
    apply indexr_var_some' in IS2. lia. rewrite IM2 in IM2''.  inversion IM2''. subst qt2'.
    rewrite IS2 in IS2'. inversion IS2'. subst v2'. eapply H9. auto.
    rewrite SVT in SVT'. subst. auto.
    auto.
    
  + destruct STL1 as (X & Y). destruct (Y i) as [qt1' [v' [IM1'' [IS1' [? ?]]]]].
    apply indexr_var_some' in IS1. lia. rewrite IM1 in IM1''.  inversion IM1''. subst qt1'.
    rewrite IS1 in IS1'. inversion IS1'. subst v'. 

    destruct rf1. 
    * assert (val_qual (st1 M) (st1 M') H1 v1 fr (pand p q)). {
        intros ? ?. eapply HQ1. rewrite val_locs_ref.
        eapply lls_s. unfold pone. intuition. eauto. eapply H7; eauto.
     }
      intros ? ?. destruct (H10 x). 
      -- eauto.
      -- left. eapply lls_mono. 2: eauto. eapply vars_locs_mono. unfoldq. intuition.
      -- right. eauto. 
    * assert (val_qual (st1 M) (st1 M') H1 v1 false (pand p (plift q1))). { 
        intros ? ?. left. eapply H7 in H10; auto. rewrite H5 in H10; auto. eapply lls_mono; eauto.
        eapply vars_locs_mono; eauto. unfoldq; intuition.
      }
      intros ? ?. destruct (H10 x). 
      -- auto.
      -- left. eapply lls_mono; eauto. eapply vars_locs_mono. 
         intros ? ?. unfoldq; intuition.
      -- right. auto.
    
  + destruct STL2 as (X & Y). destruct (Y i0) as [qt2' [v' [IM2'' [IS2' [? ?]]]]].
    apply indexr_var_some' in IS2. lia. rewrite IM2 in IM2''.  inversion IM2''. subst qt2'.
    rewrite IS2 in IS2'. inversion IS2'. subst v'. 

    destruct rf1. 
    * assert (val_qual (st2 M) (st2 M') H2 v2 fr (pand p q)). {
        intros ? ?. eapply HQ2. rewrite val_locs_ref.
        eapply lls_s. unfold pone. intuition. eauto. eauto.
     }
      intros ? ?. destruct (H10 x). 
      -- eauto.
      -- left. eapply lls_mono. 2: eauto. eapply vars_locs_mono. unfoldq. intuition.
      -- right. eauto. 
    * assert (val_qual (st2 M) (st2 M') H2 v2 false (pand p (plift q1))). { 
        intros ? ?. left. eapply H7 in H10; auto. rewrite H4 in H10; auto. eapply lls_mono; eauto.
        eapply vars_locs_mono; eauto. unfoldq; intuition.
      }
      intros ? ?. destruct (H10 x). 
      -- auto.
      -- left. eapply lls_mono; eauto. eapply vars_locs_mono. 
         intros ? ?. unfoldq; intuition.
      -- right. auto.
Qed.


Lemma sem_put: forall t1 t2 t3 t4 env T p fr1 q1 rf2 q2,
    sem_type env t1 t2 (TRef T rf2 q2) p fr1 q1 ->
    sem_type env t3 t4 T p false (plift q2)  ->
    sem_type env (tput t1 t3) (tput t2 t4) TBool p false pempty.
Proof.
  intros. intros M H1 H2 WFE STF S1 S2 ST.
  destruct (H M H1 H2 WFE STF S1 S2 ST) as [S1' [S2' [M' [v1 [v2 IE]]]]].
  destruct IE as [IE1 [IE2 [STC [STF1 [ST1 [SE1 [SE2 [HV1 [HQ1 HQ2]]]]]]]]]. 
  eapply envt_store_extend in WFE as WFE1. 2: eapply ST. 2: eauto.

  destruct (H0 M' H1 H2 WFE1 STF1 S1' S2' ST1) as [S1'' [S2'' [M''[v3 [v4 IE]]]]].
  destruct IE as [IE3 [IE4 [SC2 [STF2 [ST2 [SE3 [SE4 [HV2 [HQ3 HQ4]]]]]]]]]. 

  remember ST as ST'. clear HeqST'.
  destruct ST as [SST1 [SST2 [SP1 [SP2 SP3]]]].
  destruct SST1 as [LS1 PS1]. destruct SST2 as [LS2 PS2].

  remember HV1 as HV1'. clear HeqHV1'.

  destruct v1; destruct v2; try solve [inversion HV1]. simpl in HV1.
  destruct HV1 as (CLT1 & CLT2 & F1 & F2 & PLS1 & PLS2 & STR & STRP & vt & qt1 & qt2 & IM1 & IM2 & ? & VT & ? & ? & ?).

  remember ST2 as ST2'. clear HeqST2'.
  destruct ST2 as [SST3 [SST4 [SP4 [SP5 SP6]]]].
  destruct SST3 as [LS3 PS3]. destruct SST4 as [LS4 PS4].

  assert (indexr i (st1 M') = indexr i (st1 M'')) as R1. { eapply SC2; auto.  eapply indexr_var_some' in IM1. unfoldq; intuition. }
  assert (indexr i0 (st2 M') = indexr i0 (st2 M'')) as R2. { eapply SC2; auto. eapply indexr_var_some' in IM2. unfoldq; intuition. }

  exists (update S1'' i v3), (update S2'' i0 v4).
  exists M'', (vbool true), (vbool true).
  split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 8: split. 9: split. 
  * (* first one *)
    destruct IE1 as [n1 IE1].
    destruct IE3 as [n3 IE3].
    exists (S(n1 + n3)). intros. destruct n. intuition.
    simpl. rewrite IE1. rewrite IE3.
    assert (i < length S1''). 
    rewrite LS3. eapply st_mono1'; eauto.
    eapply indexr_var_some' in IM1. unfold length1. auto.  destruct (PS3 i) as [? [? [? [IS ?]]]]. auto.
    rewrite IS. auto. lia. lia.

  
  * (* 2nd  one *) 
    destruct IE2 as [n2 IE2].
    destruct IE4 as [n4 IE4].
    exists (S(n2 + n4)). intros. destruct n. intuition.
    simpl. rewrite IE2. rewrite IE4. 
    assert (i0 < length S2''). 
    rewrite LS4. eapply st_mono2'; eauto. 
    apply indexr_var_some' in IM2. unfold length2. auto. destruct (PS4 i0) as [? [? [? [IS ?]]]]. auto.
    rewrite IS. auto. lia. lia.

  * eapply st_trans; eauto.  

  * auto.
  
  * (* store typing *)
    repeat split. 
    + (* length *)
      rewrite <-update_length. eauto.
    + rewrite <-update_length.  
      intros. destruct (PS3 l) as [qt1' [v1' [IM1' [IS1' [P1' P2']]]]]; auto.
      bdestruct (l =? i).
      - exists qt1', v3; intuition. 
        -- subst l. rewrite update_indexr_hit. auto. auto.
        -- subst l. rewrite <- R1 in IM1'. rewrite IM1 in IM1'. inversion IM1'. subst qt1.
           intros ? ?. eapply HQ3 in H6. destruct H6.
           rewrite H4. 
           eapply lls_mono; eauto. eapply vars_locs_mono; eauto.
           intros ? ?. unfoldq; intuition. 
           simpl in H6. intuition.
      - exists qt1', v1'; intuition. rewrite update_indexr_miss. auto. auto.
    + (* length *)
      rewrite <-update_length. eauto.
    + rewrite <-update_length.  
      intros. destruct (PS4 l) as [qt2' [v2' [IM2' [IS2' [P1' P2']]]]]; auto.
      bdestruct (l =? i0).
      - exists qt2', v4; intuition. 
        -- subst l. rewrite update_indexr_hit. auto. auto.
        -- subst l. rewrite <- R2 in IM2'. rewrite IM2 in IM2'. inversion IM2'. subst qt2.
           intros ? ?. eapply HQ4 in H6. destruct H6. 
           eapply lls_mono; eauto. rewrite H5. eapply vars_locs_mono; eauto.
           intros ? ?. unfoldq; intuition. 
           simpl in H6. intuition.
      - exists qt2', v2'; intuition. rewrite update_indexr_miss. auto. auto.
    + intros. destruct (SP4 l1 l2) as [vt' [qt1' [qt2' [v1' [v2' [IM1' [IM2' [IS1' [IS2' [SVT' [VTT STF']]]]]]]]]]]; auto.
      assert (st_locs1 M' i) as A. {  apply indexr_var_some' in IM1. unfold st_locs1, pnat, length1. lia. }
      assert (st_locs2 M' i0) as B. {  apply indexr_var_some' in IM2. unfold st_locs2, pnat, length2. lia. }
      bdestruct (l1 =? i). 
      assert (l2 = i0).  {
        destruct HV1'. subst.
        destruct SC2 as [? [? [? [? [? ?]]]]].  
        specialize (H14 i i0); intuition.
        eapply SP5; eauto.
      }
      - subst l1 l2. remember ST2' as ST2''. clear HeqST2''. 
        destruct ST' as [SST1' [SST2' ST' ]].
        exists vt, qt1', qt2', v3, v4; intuition.
        rewrite update_indexr_hit. auto. apply indexr_var_some' in IS1'. lia.
        rewrite update_indexr_hit. auto. apply indexr_var_some' in IS2'. lia.
        
        destruct SC2 as [? [? [? [? [? ?]]]]]. specialize (H16 i i0); intuition.
        congruence.

        eapply VT. 6: eapply HV2. 2: eapply ST2'. eapply stchain_tighten; eauto. eapply indexr_filter; eauto.
        repeat rewrite <- val_locs_ref.
        eapply valt_filter. eauto. eapply lls_indexr_closed'''; eauto. destruct ST1 as [? [? ?]]; eauto. 
        eapply lls_indexr_closed'''; eauto. destruct ST1 as [? [? ?]]; eauto.   
        eapply valt_filter. eauto. 
        intros ? ?. destruct (HQ3 x); auto. 
        rewrite H4. eapply lls_mono; eauto. eapply vars_locs_mono. unfoldq; intuition.
        simpl in H13. contradiction.

        intros ? ?. destruct (HQ4 x); auto.
        rewrite H5. eapply lls_mono; eauto. eapply vars_locs_mono. unfoldq; intuition.
        simpl in H13. contradiction.
        
        eapply valt_filter; eauto.

      - assert (l2 = i0 -> False). {
        intros. subst. 
        assert (strel M'' i i0). {
          destruct SC2 as [? [? [? [? [? ?]]]]]. eapply H13. intuition. auto.
        }
        assert (l1 = i). eapply SP6; eauto. contradiction.
      }
        exists vt', qt1', qt2', v1', v2'; intuition.
        rewrite update_indexr_miss. auto. auto. 
        rewrite update_indexr_miss. auto. auto. 
    + eauto.
    + eauto.
  
  * (* store preservation 1 *)
    assert (length S1 = length1 M). destruct ST1 as ((? & ?) & ? & ?). eauto.
    assert (length S2 = length2 M). destruct ST1 as (? & (? & ?) & ?). eauto.
    eapply envt_store_deep_wf with (q := p) in WFE as WFE'. 2: { intros ? ?. auto. } destruct WFE' as [WFEA WFEB].
    intros ? ?. intros.
    bdestruct (i =? l). { subst. destruct (HQ1 l).
      left. rewrite val_locs_ref. unfoldq; intuition.
      destruct H9. erewrite lls_change1. eapply lls_mono; eauto.
      eapply vars_locs_mono. unfoldq; intuition.
      eapply stchain_tighten. eapply envt_filter_deep. eauto. eauto. unfoldq; intuition. eauto.
      eapply envt_store_deep_wf; eauto. unfoldq; intuition. eapply envt_store_deep_wf; eauto. unfoldq; intuition.
            
      destruct fr1. simpl in *. unfold pdiff, pnat in H3. apply indexr_var_some' in H10.
      rewrite LS1 in H10. destruct H3. contradiction.
      simpl in H3. contradiction.
      
    }{ rewrite update_indexr_miss.
       assert ((locs_locs_stty (st1 M) (vars_locs H1 p) l) =
               locs_locs_stty (st1 M') (vars_locs H1 p) l) as LLS1. {
          assert (st_chain_partial M M' (locs_locs_stty (st1 M) (vars_locs H1 p)) (locs_locs_stty (st2 M) (vars_locs H2 p))).
          eapply stchain_tighten; eauto. eapply envt_filter_deep; eauto. unfoldq; intuition.
          eapply lls_change1 in H12. rewrite H12. auto.
        }

        assert ( ~ locs_locs_stty (st1 M) (vars_locs H1 p) l) as X. { 
          intros ?. eapply H9. eapply lls_mono; eauto. eapply vars_locs_mono; eauto. unfoldq; intuition.
        }
        
        unfold store_effect in *.
        eapply SE1 in X as A; eauto. 
        eapply SE3 in A; eauto.
        rewrite <- LLS1. 
        intros ?. eapply H9. eapply lls_mono; eauto. eapply vars_locs_mono; eauto. unfoldq; intuition.
        lia.
     }
  * (* store preservation 2 *)
    assert (length S1 = length1 M). destruct ST1 as ((? & ?) & ? & ?). eauto.
    assert (length S2 = length2 M). destruct ST1 as (? & (? & ?) & ?). eauto.
    eapply envt_store_deep_wf with (q := p) in WFE as WFE'. 2: { intros ? ?. auto. } destruct WFE' as [WFEA WFEB].
    intros ? ?. intros.
    bdestruct (i0 =? l). { subst. destruct (HQ2 l).
      left. rewrite val_locs_ref. unfoldq; intuition.
      destruct H9. erewrite lls_change2. eapply lls_mono; eauto. 
      eapply vars_locs_mono. unfoldq; intuition.
      eapply stchain_tighten. eapply envt_filter_deep; eauto. unfoldq; intuition. eauto.
      eapply envt_store_deep_wf; eauto. unfoldq; intuition.
      eapply envt_store_deep_wf; eauto. unfoldq; intuition.
      
      destruct fr1. simpl in *. unfold pdiff, pnat in H3. apply indexr_var_some' in H10.
      rewrite LS2 in H10. destruct H3. contradiction.
      simpl in H3. contradiction.
      
    }{ rewrite update_indexr_miss.
       assert ((locs_locs_stty (st2 M) (vars_locs H2 p) l) =
               locs_locs_stty (st2 M') (vars_locs H2 p) l) as LLS2. {
          assert (st_chain_partial M M' (locs_locs_stty (st1 M) (vars_locs H1 p)) (locs_locs_stty (st2 M) (vars_locs H2 p ))).
          eapply stchain_tighten. eapply envt_filter_deep; eauto. unfoldq; intuition. eauto.
          eapply envt_store_deep_wf; eauto. unfoldq; intuition.
          eapply envt_store_deep_wf; eauto. unfoldq; intuition.
          eapply lls_change2 in H12. rewrite H12. auto.
        }

        assert ( ~ locs_locs_stty (st2 M) (vars_locs H2 p ) l) as X. { 
          intros ?. eapply H9. eapply lls_mono; eauto. eapply vars_locs_mono; eauto. unfoldq; intuition.
        }

        unfold store_effect in *.
        eapply SE2 in X as A; eauto. 
        eapply SE4 in A; eauto.
        rewrite <- LLS2. 
        intros ?. eapply H9. eapply lls_mono; eauto. eapply vars_locs_mono; eauto. unfoldq; intuition.
        lia.
     }
  
  * (* val_type *)
  simpl. auto.
  * constructor. rewrite val_locs_bool in H7. eapply lls_mono; eauto. intros ? ?. unfoldq; intuition.
  * constructor. rewrite val_locs_bool in H7. eapply lls_mono; eauto. intros ? ?. unfoldq; intuition.
Qed.

Lemma sem_abs: forall env t1 t2 T1 T2 p fn1 fr1 q1 fn2 ar2 fr2 q2 qf,
    sem_type ((T1, fr1, (qand p (qor q1 (qif fn1 qf))))::env) t1 t2 T2 
      (por (pand (plift p) (plift qf)) (pone (length env)))
      fr2
      (por (plift q2) (por (pif ar2 (pone (length env)))(pif fn2 (plift (qand p qf)))))
      ->
    psub (plift q1) (pand (plift p) (plift qf)) ->   
    closed_ty (length env) T1 ->
    closed_ty (length env) T2 ->
    closed_ql (length env) q1 ->
    closed_ql (length env) q2 ->
    closed_ql (length env) qf ->
    sem_type env (tabs (qand p qf) t1) (tabs (qand p qf) t2)
      (TFun T1 fn1 fr1 q1 T2 fn2 ar2 fr2 q2)
      (plift p) false (plift qf).
Proof.
  intros. intros ? ? ? WFE STF ? ? ST.
  exists S1, S2.
  exists M. 
  exists (vabs H6 (qand p qf) t1), (vabs H7 (qand p qf) t2).
  split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 8: split. 9: split.
  + (* term evaluates *)
    exists 1. intros. destruct n. lia. simpl. eauto.
  + (* term evaluates *)
    exists 1. intros. destruct n. lia. simpl. eauto.  
  + eapply st_refl. auto.
  + auto.
  + (* store typing *)
    eauto.
  + intros ? ? ? ?. eauto.
  + intros ? ? ? ?. eauto.
  + (* result well typed *)
    apply wf_env_type in WFE as WFE'. 
    destruct WFE' as [L1 [L2 [PD1 [PD2 [P1 P2]]]]].
    simpl. 

     (* results *)
   rewrite L1, L2 in *. rewrite PD1, PD2 in *. intuition; eauto.  

   repeat rewrite val_locs_abs.
   eapply envt_filter_deep; eauto. rewrite plift_and. unfoldq; intuition.

     (* INDUCTION *)
   rename H12 into HQX1. rename H13 into HQX2. 
   rewrite val_locs_abs in *. rewrite val_locs_abs in *.
   rewrite plift_and in *. 
   assert (env_type M' (vx1 :: H6) (vx2 :: H7) ((T1,fr1, (qand p (qor q1 (qif fn1 qf)))) :: env) 
           (por (pand (plift p) (plift qf)) (pone (length env)))) as WFE'. {
      eapply envt_extend_full in WFE; eauto.
      - eapply stchain_tighten; eauto. eapply envt_filter_deep; eauto. unfoldq; intuition.
        eapply lls_mono; eauto. eapply vars_locs_mono; eauto. unfoldq; intuition.
        eapply lls_mono; eauto. eapply vars_locs_mono; eauto. unfoldq; intuition.
      - intros ? ?. destruct H12.
        destruct (HQX1 x) as [F | [L | Q]]. auto. {
          destruct fn1. 2: contradiction.
          rewrite plift_and, plift_or, plift_if.
          eapply lls_mono. 2: eapply F. intros ? F'.
          destruct F'. exists x1. unfoldq. intuition.
        }{
          destruct fr1. 2: contradiction.
          destruct L. eauto.
        } {
          rewrite plift_and, plift_or, plift_if.
          eapply lls_mono. 2: eapply Q. intros ? Q'.
          destruct Q'. exists x1. unfoldq. intuition. eapply H0; eauto. 
        }
    
      - intros ? ?. destruct H12.
        destruct (HQX2 x) as [F | [L | Q]]. auto. {
        destruct fn1. 2: contradiction.
        rewrite plift_and, plift_or, plift_if.
        eapply lls_mono. 2: eapply F. intros ? F'.
        destruct F'. exists x1. unfoldq. intuition.
      }{
        destruct fr1. 2: contradiction.
        destruct L. eauto.
      } {
        rewrite plift_and, plift_or, plift_if.
        eapply lls_mono. 2: eapply Q. intros ? Q'.
        destruct Q'. exists x1. unfoldq. intuition. eapply H0; eauto. 
      }
    - intros. rewrite plift_and in *. rewrite plift_or in *. 
      subst fr1. intros ? ?. eapply HQX1 in H12.
      destruct H12 as [ A | [B | C]]. {
        destruct fn1. 2: contradiction.
        simpl in A. eapply lls_mono. 2: eauto. eapply vars_locs_mono. 
        unfoldq. intuition.
      } {
        contradiction.
      } {
        eapply lls_mono. 2: eauto. eapply vars_locs_mono. 
        unfoldq. intuition. eapply H0; eauto.
      }
    - intros. rewrite plift_and in *. rewrite plift_or in *. 
      subst fr1. intros ? ?. eapply HQX2 in H12.
      destruct H12 as [ A | [B | C]]. {
        destruct fn1. 2: contradiction.
        simpl in A. eapply lls_mono. 2: eauto. eapply vars_locs_mono. 
        unfoldq. intuition.
      } {
        contradiction.
      } {
        eapply lls_mono. 2: eauto. eapply vars_locs_mono. 
        unfoldq. intuition. eapply H0; eauto.
      }
    - unfoldq; intuition.
    - rewrite plift_and, plift_or, plift_if. rewrite pand_or_distribute2.
      intros ? ?. destruct H12. destruct H12. eapply H0 in H13. unfoldq; intuition. destruct fn1; unfoldq; intuition. 
    - eapply closedq_and; eauto.
  }    
    
   destruct (H M' (vx1::H6) (vx2::H7) WFE' H9  S1' S2' H10) as [S1'' [S2'' [M'' [vy1 [vy2 IHW1]]]]].
   unfold exp_type in IHW1.
   destruct IHW1 as [IE3 [IE4 [SC''[STF'' [ST'' [SE3 [SE4 [HVY [HQY1 HQY2]]]]]]]]].

   exists S1'', S2'', M'', vy1, vy2. intuition.


  - (* store preserve 1 *)
    intros ? ? PV ?. eapply SE3. intros VL. eapply PV. rewrite lls_vars_or in VL.
    destruct VL. {
      left. replace (vx1::H6) with ([vx1]++H6) in H13. rewrite vars_locs_extend in H13. auto. unfoldq; intuition. eapply H5 in H18. rewrite L1. auto. auto.
    }{
      right. eapply lls_vars in H13. destruct H13 as [? [? ?]]. unfold pone in H13. subst x. eapply lls_var in H14.
      destruct H14 as [? [? ?]]. replace (length env) with (length H6) in H13.  rewrite indexr_head in H13. inversion H13. subst x. auto.
    }
    auto.
   
   
  - (* store preserve 2 *)
  intros ? ? PV ?. eapply SE4. intros VL. eapply PV. rewrite lls_vars_or in VL.
  destruct VL. {
    left. replace (vx2::H7) with ([vx2]++H7) in H13. rewrite vars_locs_extend in H13. auto. unfoldq; intuition. eapply H5 in H18. rewrite L2. auto. auto.
  }{
    right. eapply lls_vars in H13. destruct H13 as [? [? ?]]. unfold pone in H13. subst x. eapply lls_var in H14.
    destruct H14 as [? [? ?]]. replace (length env) with (length H7) in H13.  rewrite indexr_head in H13. inversion H13. subst x. auto.
  }
  auto.

  - (* valt *)
    eapply valt_extend; eauto.
    rewrite L1. auto. rewrite L2. auto.
    replace (vx1::H6) with ([vx1]++H6) in HVY; auto.
    replace (vx2::H7) with ([vx2]++H7) in HVY; auto.
    eapply HVY.


  - (* valq 1 *)
   intros ? ?.
   destruct (HQY1 x) as [HY_q | HY_fr]. eauto.
   --  (* q *)
     eapply lls_vars in HY_q. 
     destruct HY_q as (? & (? & ?) & ?).
     replace (length env) with (length H6) in *.
     bdestruct (x0 =? length H6).
      (* from arg *)
     * subst x0. eapply lls_mono in H15. 2: { intros ? ?. eapply var_locs_head. eauto. }
       right. right. left.
       destruct ar2. eauto. 
       destruct H13. { destruct H13. eapply H5 in H16. lia.  }
       destruct H14. eapply H4 in H14. lia.
       destruct fn2. destruct H14; simpl in H14. contradiction. 
       destruct H14. eapply H5 in H16. lia. 
       destruct H14; simpl in H14; contradiction.
     * (* from func *)
       assert (x0 < length (vx1:: H6)). eapply lls_var in H15. destruct H15. rewrite indexr_extend1 in H15. eapply H15. simpl in H17.
       eapply lls_mono in H15. 2: { intros ? ?. eapply var_locs_shrink. eauto. lia. }
       destruct H13 as [[? ?] | ?]; destruct H14 as [? | [? | ?] ].
       left. split. 
       eapply lls_mono. 2: eapply H15. intros ? ?. exists x0. intuition. 
       eapply lls_vars'. eapply H15. unfoldq; intuition.
       destruct ar2; contradiction. 
       destruct fn2. right. left. simpl. eapply lls_vars'. eapply H15. auto. 
       simpl in H14. contradiction. contradiction. 
       
       contradiction. contradiction.
     
   -- (* fr *)
      right. right. right. eapply HY_fr.   
  
  - (* valq 2 *)
  
    intros ? ?.
    destruct (HQY2 x) as [HY_q | HY_fr]. eauto.
    -- (* q *)
      eapply lls_vars in HY_q. 
      destruct HY_q as (? & (? & ?) & ?).
      replace (length env) with (length H7) in *.
      bdestruct (x0 =? length H7).
      * (* from arg *)
        subst x0. eapply lls_mono in H15. 2: { intros ? ?. eapply var_locs_head. eauto. }
        right. right. left.
        destruct ar2. eauto. 
        destruct H13. { destruct H13. eapply H5 in H16. lia.  }
        destruct H14. eapply H4 in H14. lia.
        destruct fn2. simpl in H14.  destruct H14; simpl in H14. contradiction. 
        destruct H14. eapply H5 in H16. lia. 
        destruct H14; simpl in H14; contradiction.
      * (* from func *)
        assert (x0 < length (vx2:: H7)). eapply lls_var in H15. destruct H15. rewrite indexr_extend1 in H15. eapply H15. simpl in H16.
        eapply lls_mono in H15. 2: { intros ? ?. eapply var_locs_shrink. eauto. simpl in H17. lia. }
        destruct H13 as [[? ?] | ?]; destruct H14 as [? | [? | ?] ].
        left. split. 
        eapply lls_mono. 2: eapply H15. intros ? ?. exists x0. intuition. 
        eapply lls_vars'. eapply H15. unfoldq; intuition.
        destruct ar2; contradiction. 
        destruct fn2. right. left. simpl. eapply lls_vars'. eapply H15. auto. 
        simpl in H14. contradiction. contradiction. contradiction. contradiction.
    
    -- (* fr *)
       right. right. right. eapply HY_fr.   

  + eapply valq_abs; eauto.
  + eapply valq_abs; eauto.
Unshelve. eauto. eauto.
Qed.


Lemma sem_app: forall env f1 f2 t1 t2 T1 T2 p frf qf frx qx fn1 fr1 q1 fn2 ar2 fr2 q2,
    sem_type env f1 f2 (TFun T1 fn1 fr1 q1 T2 fn2 ar2 fr2 q2) (plift p) frf (plift qf)  ->  
    sem_type env t1 t2 T1 (plift p) frx (plift qx) ->
    (if fn1 then
       if fr1 then
         True
       else
         (frx = false /\ (exists x0, f1 = tvar x0 /\ psub (plift qx) (pone x0))) \/
         (frx = false /\ (exists p0 t, f1 = tabs p0 t /\ psub (plift qx) (plift p0))) \/
         (frx = false /\ psub (plift qx) (plift q1))
     else
       if fr1 then
         psub (pand 
                 (plift (vars_trans_fix env qf))
                 (plift (vars_trans_fix env qx)))
           (plift q1)
       else
         frx = false /\ psub (plift qx) (plift q1)) ->

        (if fn1 then
         if fr1 then
           True
         else
           (frx = false /\ (exists x0, f2 = tvar x0 /\ psub (plift qx) (pone x0))) \/
           (frx = false /\ (exists p0 t, f2 = tabs p0 t /\ psub (plift qx) (plift p0))) \/
           (frx = false /\ psub (plift qx) (plift q1))
       else
         if fr1 then
           psub (pand 
                   (plift (vars_trans_fix env qf))
                   (plift (vars_trans_fix env qx)))
             (plift q1)
         else
           frx = false /\ psub (plift qx) (plift q1)) ->

    psub (plift q1) (plift p) ->   
    psub (plift q2) (plift p) ->   
    sem_type env (tapp f1 t1) (tapp f2 t2) T2 (plift p)
      (fn2 && frf || ar2 && frx || fr2)
      (por (pif fn2 (plift qf)) (por (pif ar2 (plift qx)) (plift q2)))
      .
Proof. 
  intros. intros M ? ? WFE STF S1 S2 ST.
  rename H into IHW1. rename H0 into IHW2.
  unfold sem_type in IHW1. 
  destruct (IHW1 M H5 H6 WFE STF S1 S2 ST) as [S1' [S2' [M1 IEF]]]. 
  destruct IEF as [vf1 [vf2 [IEF1 [IEF2 [SC1 [STF1 [ST1 [SEF1 [SEF2 [HVF [HQF1 HQF2]]]]]]]]]]].
  remember HVF as HVF'. clear HeqHVF'. remember HVF' as HVF''. clear HeqHVF''.

  assert (env_type M1 H5 H6 env (plift p)) as WFE1. { eapply envt_store_extend; eauto. }
  destruct (IHW2 M1 H5 H6 WFE1 STF1 S1' S2' ST1) as [S1'' [S2'' [M2 IEX]]].
  destruct IEX as [vx1 [vx2 [IEX1 [IEX2 [SC2 [STF2 [ST2 [SEF3 [SEF4 [HVX [HQX1 HQX2]]]]]]]]]]].


  assert (telescope env). eapply envt_telescope. eauto.

  (* vf is a function value: it can eval its body *)
  destruct vf1; destruct vf2; try solve [inversion HVF]; simpl in HVF; intuition.

  apply valt_wf in HVF' as WFQF. apply valt_wf in HVX as WFQX.

  destruct HVF'; intuition.
  rename H30 into HVF.
  destruct (HVF S1'' S2'' M2 vx1 vx2) as [S1''' [S2''' [M3 [vy1 [vy2 [IEY1 [IEY2 [SC3 [STF3 [ST3 [SEF5 [SEF6 [HVY [HQY1 HQY2]]]]]]]]]]]]]]; eauto.


  eapply stchain_tighten. eapply valt_filter; eauto. eauto. eapply H28. eapply H28.
  
  (* SEPARATION / OVERLAP *)
  (* 1st *)
  rename H1 into HSEP.
  intros ? ?.

  destruct fn1. { (* arg may overlap with function? *)
    destruct fr1. { (* arg may be fresh? *)
      (* fn, fr: anything goes *)
      edestruct val_locs_stty_decide. destruct ST2; eauto. left. simpl.  eauto. 
      right. left. eauto.
    } {
      (* fn, not fr *) 
      destruct HSEP as [SEP | [SEP | SEP]]. { (* fn *)
        destruct SEP as (? & ? & ? & A). subst f1 frx.
        destruct IEF1 as [? IEF1]. assert (S x1 > x1) as P. lia. specialize (IEF1 (S x1) P).
        simpl in IEF1. inversion IEF1.
        destruct (HQX1 x) as [Hq | Hfr]. eauto. 2: { unfoldq. intuition. }
        left. simpl. eapply lls_vars in Hq. destruct Hq as (? & (? & B) & ?).
        eapply lls_var in H32. destruct H32 as (? & ? & ?).
        eapply A in B. unfoldq. subst x0. congruence. 
      } { (* fn 2, value *)
        destruct SEP as (? & ? & ? & ? & A). subst f1 frx.
        destruct IEF1 as [? IEF1]. assert (S x2 > x2) as P. lia. specialize (IEF1 (S x2) P).
        simpl in IEF1. inversion IEF1. 
        destruct (HQX1 x) as [Hq | Hfr]. eauto. 2: { unfoldq. intuition. }
        subst. left. simpl. eapply lls_vars in Hq. destruct Hq as (? & (? & B) & ?).
        rewrite val_locs_abs. 
        eapply A in B. eapply lls_vars'. eauto. eauto. 
      } { (* q1 *)
        destruct SEP. subst frx.
        right. right. 
        eapply valq_sub with (q':=plift q1) (fr':=false) in HQX1.
        destruct (HQX1 x) as [Hq | Hfr]. eauto. 2: contradiction.
        eapply lls_vars in Hq. destruct Hq as (? & ? & ?). eapply lls_vars'. eauto. unfoldq. intuition. 
        unfoldq; intuition. eauto.
      }
    }
  } {
    right. destruct fr1. {
      (* not fn, fr *) 
      edestruct val_locs_stty_decide. destruct ST2; eauto. { (* check to see if we're aliasing function *)
        right. eapply overlapping. 6: eapply HVF''. 3: eauto. 3: eauto. 3: eauto. 2: eauto. eapply WFE. eauto. eauto. eauto. eauto.
        eapply valt_wf; eauto. eapply valt_wf; eauto. auto.
        
        intros ? [? ?]. eapply HSEP. split.
        rewrite plift_vt. eapply vt_mono. 2: eapply H30. unfoldq. intuition. eauto. 
        rewrite plift_vt. eapply vt_mono. 2: eapply H31. unfoldq. intuition. eauto.
        unfoldq. intuition eauto.
      }{ 
        left. eauto.
      }
    } {
      (* not fn, not fr *)
      right. destruct HSEP as [? HSEP]. subst frx.
      eapply valq_sub with (q':=plift q1) (fr':=false) in HQX1.
      destruct (HQX1 x) as [Hq | Hfr]. eauto. 2: contradiction.
      eapply lls_vars in Hq. destruct Hq as (? & ? & ?). eapply lls_vars'. eauto. unfoldq. intuition.
      unfoldq; intuition. eauto. 
    }
  }

  (* 2nd *)
  rename H2 into HSEP.
  intros ? ?.

  destruct fn1. { (* arg may overlap with function? *)
    destruct fr1. { (* arg may be fresh? *)
      (* fn, fr: anything goes *)
      edestruct val_locs_stty_decide. destruct ST2 as [? [A ?]]. eapply A. left. simpl.  eauto. 
      right. left. eauto.
    } {
      (* fn, not fr *) 
      destruct HSEP as [SEP | [SEP | SEP]]. { (* fn *)
        destruct SEP as (? & ? & ? & A). subst f2 frx.
        destruct IEF2 as [? IEF2]. assert (S x1 > x1) as P. lia. specialize (IEF2 (S x1) P).
        simpl in IEF2. inversion IEF2.
        destruct (HQX2 x) as [Hq | Hfr]. eauto. 2: { unfoldq. intuition. }
        left. simpl. eapply lls_vars in Hq. destruct Hq as (? & (? & B) & ?).
        eapply lls_var in H32. destruct H32 as (? & ? & ?).
        eapply A in B. unfoldq.  congruence.  
      } { (* fn 2, value *)
        destruct SEP as (? & ? & ? & ? & A). subst f2 frx.
        destruct IEF2 as [? IEF2]. assert (S x2 > x2) as P. lia. specialize (IEF2 (S x2) P).
        simpl in IEF2. inversion IEF2. 
        destruct (HQX2 x) as [Hq | Hfr]. eauto. 2: { unfoldq. intuition. }
        subst. left. simpl. eapply lls_vars in Hq. destruct Hq as (? & (? & B) & ?).
        rewrite val_locs_abs. 
        eapply A in B. eapply lls_vars'. eauto. eauto. 
      } { (* q1 *)
        destruct SEP. subst frx.
        right. right. 
        eapply valq_sub with (q':=plift q1) (fr':=false) in HQX1.
        destruct (HQX2 x) as [Hq | Hfr]. eauto. 2: contradiction.
        eapply lls_vars in Hq. destruct Hq as (? & ? & ?). eapply lls_vars'. eauto. unfoldq. intuition.
        unfoldq; intuition.  eauto. 
      }
    }
  } {
    right. destruct fr1. {
      (* not fn, fr *) 
      edestruct val_locs_stty_decide. destruct ST2 as [? [X ?]]. eapply X.  { (* check to see if we're aliasing function *)
        right. eapply overlapping. 6: eapply HVF''. 3: eauto. 3: eauto. 3: eauto. 2: eauto. eapply WFE. eauto. eauto. eauto. eauto.
        eapply valt_wf; eauto. eapply valt_wf; eauto. auto.
        
        intros ? [? ?]. eapply HSEP. split.
        rewrite plift_vt. eapply vt_mono. 2: eapply H30. unfoldq. intuition. eauto. 
        rewrite plift_vt. eapply vt_mono. 2: eapply H31. unfoldq. intuition. eauto.
        unfoldq. intuition eauto.
      }{ 
        left. eauto.
      }
    } {
      (* not fn, not fr *)
      right. destruct HSEP as [? HSEP]. subst frx.
      eapply valq_sub with (q':=plift q1) (fr':=false) in HQX2.
      destruct (HQX2 x) as [Hq | Hfr]. eauto. 2: contradiction.
      eapply lls_vars in Hq. destruct Hq as (? & ? & ?). eapply lls_vars'. eauto. unfoldq. intuition.
      unfoldq; intuition. eauto. 
    }
  }

  (* EVALUATION *)
  exists S1''', S2''', M3, vy1, vy2. split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 8: split. 9: split.
  + (* expression evaluates *)
    (* - initial fuel value *)
    destruct IEF1 as [n1 IEF1].
    destruct IEX1 as [n2 IEX1].
    destruct IEY1 as [n3 IEY1].
    exists (S (n1+n2+n3)).
    (* - forall greater fuel *)
    intros. destruct n. lia.
    (* - result computes *)
    simpl. rewrite IEF1. rewrite IEX1. rewrite IEY1.
    repeat rewrite app_assoc. repeat rewrite app_nil_r. eauto.
    all: lia.

  + (* expression evaluates *)
    (* - initial fuel value *)
    destruct IEF2 as [n1 IEF2].
    destruct IEX2 as [n2 IEX2].
    destruct IEY2 as [n3 IEY2].
    exists (S (n1+n2+n3)).
    (* - forall greater fuel *)
    intros. destruct n. lia.
    (* - result computes *)
    simpl. rewrite IEF2. rewrite IEX2. rewrite IEY2.
    repeat rewrite app_assoc. repeat rewrite app_nil_r. eauto.
    all: lia.

  + eapply st_trans. eapply st_trans. eauto. eauto. eauto. 

  + eauto.
      
  (* STORE_TYPE *)
  + eauto.
  
  + (* store preservation 1 *)  

    assert (length1 M <= length1 M1) as L1. eapply st_mono1 in SC1. auto.
    assert (st_chain M M2) as SCC. eapply st_trans. eauto. eauto.

    assert (length1 M1 <= length1 M2) as L2. eapply st_mono1 in SC2. auto.
    intros ? ? PV. intros IS. rewrite SEF5; eauto. intros ?. eapply PV.
    assert (l1 < length1 M). apply indexr_var_some' in IS. destruct ST as ((L & ?) & ?). unfold length1. lia.
    destruct H29 as [EF | EX]. {
      destruct (HQF1 l1).  
      erewrite lls_change; eauto. 
      eapply stchain_tighten; eauto. 
      eapply valt_filter; eauto.
      eapply valt_filter; eauto.
      erewrite lls_change. eapply lls_mono. 2: eapply H29. eapply vars_locs_mono; eauto.
      unfoldq; intuition. eapply stchain_tighten; eauto. eapply envt_filter_deep; eauto. intros ? ?. auto.
      eapply envt_store_deep_wf; eauto. unfoldq; intuition.
      eapply envt_store_deep_wf; eauto. unfoldq; intuition.
      destruct frf. destruct H29. contradiction. simpl in H29. contradiction.
    } {
      destruct (HQX1 l1). auto.
      erewrite lls_change. 
      eapply lls_mono; eauto. eapply vars_locs_mono; eauto. unfoldq; intuition.

      eapply stchain_tighten. eapply envt_filter_deep; eauto. unfoldq; intuition.
      eauto. 
      eapply envt_store_deep_wf; eauto. unfoldq; intuition.
      eapply envt_store_deep_wf; eauto. unfoldq; intuition.

      destruct frx; unfold pif, pdiff in H29. destruct H29. 
      eapply st_mono1 in SC1. unfold length1, pnat in *. lia.
      contradiction. 
    } 
    rewrite SEF3; eauto. intros ?. eapply PV.
    erewrite lls_change. eapply lls_mono; eauto. eapply vars_locs_mono; eauto. unfoldq; intuition.
    eapply stchain_tighten; eauto. eapply envt_filter_deep; eauto. unfoldq; intuition.
    eapply envt_store_deep_wf; eauto. unfoldq; intuition.
    eapply envt_store_deep_wf; eauto. unfoldq; intuition.

  + (* store preservation 2 *)  
  assert (length2 M <= length2 M1) as L1. eapply st_mono2 in SC1. auto.
  assert (st_chain M M2) as SCC. eapply st_trans. eauto. eauto.
    
  assert (length2 M1 <= length2 M2) as L2. eapply st_mono2 in SC2. auto.
  intros ? ? PV. intros IS. rewrite SEF6; eauto. intros ?. eapply PV.
  assert (l1 < length2 M). apply indexr_var_some' in IS. destruct ST as (? & (L & ?) & ?). unfold length2. lia.
  destruct H29 as [EF | EX]. {
    destruct (HQF2 l1). erewrite lls_change; eauto.
    eapply stchain_tighten; eauto. eapply valt_filter; eauto. eapply valt_filter; eauto.
    erewrite lls_change. eapply lls_mono; eauto. eapply vars_locs_mono; eauto. unfoldq; intuition.
    eapply stchain_tighten; eauto. eapply envt_filter_deep; eauto. unfoldq; intuition.
    eapply envt_store_deep_wf; eauto. unfoldq; intuition.
    eapply envt_store_deep_wf; eauto. unfoldq; intuition.

    destruct frf; simpl in H29. destruct H29. contradiction. contradiction.
    
  } {
    destruct (HQX2 l1). auto.
    erewrite lls_change. 
    eapply lls_mono; eauto. eapply vars_locs_mono; eauto. unfoldq; intuition.
    
    eapply stchain_tighten. eapply envt_filter_deep; eauto. unfoldq; intuition.
    eauto. 
    eapply envt_store_deep_wf; eauto. unfoldq; intuition.
    eapply envt_store_deep_wf; eauto. unfoldq; intuition.
    
    destruct frx; unfold pif, pdiff in H29. destruct H29. 
    eapply st_mono2 in SC2. unfold length2, pnat in *. lia.
    contradiction.
  }  
  rewrite SEF4; eauto. intros ?. eapply PV.
  erewrite lls_change. eapply lls_mono; eauto. eapply vars_locs_mono; eauto. unfoldq; intuition.
  eapply stchain_tighten; eauto. eapply envt_filter_deep; eauto. unfoldq; intuition.
  eapply envt_store_deep_wf; eauto. unfoldq; intuition.
  eapply envt_store_deep_wf; eauto. unfoldq; intuition.
  

  (* VAL_TYPE *)
  + eapply HVY.

  (* VAL_QUAL 1 *)
  + remember (vabs l q t) as vf.
    assert (val_qual (st1 M) (st1 M3) H5 vf frf (pand (plift p) (plift qf))) as HQF'. {
      eapply valq_store_change1. eauto. eauto. eauto. eauto. eapply st_trans; eauto.  }
    assert (val_qual (st1 M1) (st1 M3) H5 vx1 frx (pand (plift p) (plift qx))) as HQX'. {
      eapply valq_store_change1. eapply envt_store_extend; eauto. eauto. eauto. eauto. eauto. }
    
    intros ? ?. unfoldq.
    destruct (HQY1 x) as [HY_q | [HY_f | [HY_x | HY_fr]]].
    repeat rewrite app_length. intuition.
    * (* q2, and part of function *)
      destruct HY_q as [? ?].
      left. eapply lls_mono. eapply vars_locs_mono. 2: eauto.
      intros ? ?. intuition. 
    * (* part of function *)
      destruct fn2. 2: contradiction.
      destruct (HQF' x) as [HF_q | HF_fr]. eauto. 
      -- (* q *) left. eapply lls_mono. 2: eauto. eapply vars_locs_mono. unfoldq. intuition.
      -- (* fr *) 
         destruct frf. 2: contradiction.
         right. destruct HF_fr; simpl. 
         split. eauto. eauto. 
    * (* part of arg *)
      destruct ar2. 2: contradiction.
      destruct (HQX' x) as [HX_q | HX_fr]. eauto.
      -- (* q *) left. eapply lls_mono. 2: eauto. eapply vars_locs_mono. unfoldq. intuition. 
      -- (* fr *)
         destruct frx. 2: contradiction.
         right. destruct HX_fr. 
         destruct (fn2 && frf); simpl. 
         split. eauto. intros ?. eapply H31. eapply SC1. eauto. 
         split. eauto. intros ?. eapply H31. eapply SC1. eauto. 
    * (* fresh *)
      destruct fr2. 2: contradiction.
      right. destruct HY_fr.
      destruct (fn2 && frf || ar2 && frx); simpl.
      split. eauto. intros ?. eapply H31. eapply SC2. eapply SC1. eauto.   
      split. eauto. intros ?. eapply H31. eapply SC2. eapply SC1. eauto.

  (* VAL_QUAL 2 *)
  + remember (vabs l0 q0 t0) as vf.
    assert (val_qual (st2 M) (st2 M3) H6 vf frf (pand (plift p) (plift qf))) as HQF'. {
      eapply valq_store_change2. eauto. eauto. eauto. eauto. eapply st_trans; eauto.  }
    assert (val_qual (st2 M1) (st2 M3) H6 vx2 frx (pand (plift p) (plift qx))) as HQX'. {
      eapply valq_store_change2. eapply envt_store_extend; eauto. eauto. eauto. eauto. eauto. }
    
    intros ? ?. unfoldq.
    destruct (HQY2 x) as [HY_q | [HY_f | [HY_x | HY_fr]]].
    repeat rewrite app_length. intuition.
    * (* q2, and part of function *)
      destruct HY_q as [? ?].
      left. eapply lls_mono. eapply vars_locs_mono. 2: eauto.
      intros ? ?. intuition. 
    * (* part of function *)
      destruct fn2. 2: contradiction.
      destruct (HQF' x) as [HF_q | HF_fr]. eauto. 
      -- (* q *) left. eapply lls_mono. 2: eauto. eapply vars_locs_mono. unfoldq. intuition.
      -- (* fr *) 
         destruct frf. 2: contradiction.
         right. destruct HF_fr; simpl. 
         split. eauto. eauto. 
    * (* part of arg *)
      destruct ar2. 2: contradiction.
      destruct (HQX' x) as [HX_q | HX_fr]. eauto.
      -- (* q *) left. eapply lls_mono. 2: eauto. eapply vars_locs_mono. unfoldq. intuition. 
      -- (* fr *)
         destruct frx. 2: contradiction.
         right. destruct HX_fr. 
         destruct (fn2 && frf); simpl. 
         split. eauto. intros ?. eapply H31. eapply SC1. eauto. 
         split. eauto. intros ?. eapply H31. eapply SC1. eauto. 
    * (* fresh *)
      destruct fr2. 2: contradiction.
      right. destruct HY_fr.
      destruct (fn2 && frf || ar2 && frx); simpl.
      split. eauto. intros ?. eapply H31. eapply SC2. eapply SC1. eauto.   
      split. eauto. intros ?. eapply H31. eapply SC2. eapply SC1. eauto.    
     
Qed.


Lemma sem_sub: forall env y1 y2 T p fr1 q1 fr2 q2,
    sem_type env y1 y2  T p fr1 q1 ->
    psub q1 q2 ->
    psub q2 (pdom env)  ->
    sem_type env y1 y2 T p (fr1 || fr2)  q2.
Proof.
  intros. intros ? ? ? WFE  STF S1 S2 ST.
  destruct (H M H2 H3 WFE STF S1 S2 ST) as [S1' [S2' [M1 [vx1 [vx2 IE]]]]]. 
  destruct IE as [IE1 [IE2 [SC1 [STF1 [ST1 [SE1 [SE2 [HVX [HQX1 HQX2]]]]]]]]].
  assert (psub q2 (pdom H2)). {
    unfoldq. destruct WFE. rewrite H4. intuition. } 
  assert (psub q2 (pdom H3)). {
    unfoldq. destruct WFE as [? [? ?]]. rewrite H6. intuition. }   
  exists S1', S2', M1. exists vx1, vx2. 
  split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 8: split. 9: split.
  eauto. eauto. eauto. eauto. eauto. 
  eapply se_sub; eauto. eapply lls_mono. eapply vars_locs_mono. unfoldq; intuition.
  eapply se_sub; eauto. eapply lls_mono. eapply vars_locs_mono. unfoldq; intuition.
  eauto.
  eapply valq_sub; eauto. unfoldq; intuition. unfoldq; intuition.
  eapply valq_sub; eauto. unfoldq; intuition. unfoldq; intuition.
Qed.

Lemma sem_sub_var: forall env y1 y2 T p fr1 q1 Tx qx x,
    sem_type env y1 y2 T p fr1 q1 ->
    q1 x ->
    indexr x env = Some (Tx, false, qx) ->
    psub (plift qx) p -> 
    sem_type env y1 y2 T p fr1 (por (pdiff q1 (pone x)) (plift qx)).
Proof.
  intros. rename x into z. intros ? ? ? WFE STF S1 S2 ST.
  destruct (H M H3 H4 WFE STF S1 S2 ST) as [S1' [S2' [M1 [vx1 [vx2 IE]]]]]. 
  destruct IE as [IE1 [IE2 [SC1 [STF1 [ST1 [SE1 [SE2 [HVX [HQX1 HQX2]]]]]]]]].
  exists S1', S2', M1. exists vx1, vx2. 
  split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 8: split. 9: split.
  - eauto. 
  - eauto. 
  - eauto. 
  - eauto. 
  - eauto. 
  - eapply se_sub; eauto. eapply lls_mono. eapply vars_locs_mono. unfoldq; intuition.
  - eapply se_sub; eauto. eapply lls_mono. eapply vars_locs_mono. unfoldq; intuition.
  - eauto.
  
  - eapply WFE in H1 as HZ.
    intros ? ?. destruct (HQX1 x). eauto.
    * eapply lls_vars in H6. destruct H6. bdestruct (x0 =? z).
      + subst. destruct HZ as [vz1 [vz2 ?]]. intuition.      
        eapply lls_var in H10. destruct H10 as (? & ? & ?). rewrite H10 in H6.
        inversion H6. subst x0. destruct H7. intuition. 
        left.
        erewrite lls_change with (M':=(st1 M1)) in H13.
        erewrite lls_change with (M:=(st1 M)) (M':=(st1 M1)) in H13.
        eapply lls_mono. 2: eapply H13. eapply vars_locs_mono.
        unfoldq. intuition.
        eauto.
        eapply stchain_tighten. eapply envt_filter_deep; eauto. eauto. eapply envt_store_deep_wf. eauto. eauto. eapply envt_store_deep_wf. eauto. eauto.
        eapply stchain_tighten. eapply valt_filter; eauto. eauto. eapply valt_deep_wf; eauto. eapply valt_deep_wf; eauto.
      + left. eapply lls_vars'. eapply H6. unfoldq. intuition.
    * right. intuition.
 - eapply WFE in H1 as HZ.
    intros ? ?. destruct (HQX2 x). eauto.
    * eapply lls_vars in H6. destruct H6. bdestruct (x0 =? z).
      + subst. destruct HZ as [vz1 [vz2 ?]]. intuition.      
        eapply lls_var in H10. destruct H10 as (? & ? & ?). rewrite H10 in H9.
        inversion H9. subst x0. destruct H7. intuition. 
        left.
        erewrite lls_change with (M':=(st2 M1)) in H12.
        erewrite lls_change with (M:=(st2 M)) (M':=(st2 M1)) in H12.
        eapply lls_mono. 2: eapply H12. eapply vars_locs_mono.
        unfoldq. intuition.
        eauto.
        eapply stchain_tighten. eapply envt_filter_deep; eauto. eauto. eapply envt_store_deep_wf. eauto. eauto. eapply envt_store_deep_wf. eauto. eauto.
        eapply stchain_tighten. eapply valt_filter; eauto. eauto. eapply valt_deep_wf; eauto. eapply valt_deep_wf; eauto.
      + left. eapply lls_vars'. eapply H6. unfoldq. intuition.
    * right. intuition.
Qed.

Lemma sem_seq: forall env t1 t2 t3 t4 p1 p2 p q1 q2
  (E1: sem_type env t1 t2 TBool p1 false q1)
  (E2: sem_type env t3 t4 TBool p2 false q2)
  (SUB1: psub p1 p)
  (SUB2: psub p2 p),
  sem_type env (tseq t1 t3) (tseq t2 t4) TBool p false pempty.
Proof.
  intros. intros ? ? ? WFE STF S1 S2 ST.
  (* E1 *)
  assert (env_type M H1 H2 env p1) as WFE1. { eapply envt_tighten; eauto. }
  
  destruct (E1 M H1 H2 WFE1 STF S1 S2 ST) as [S1' [S2' [M' [v1 [v2 IE]]]]].
  destruct IE as [IE1 [IE2 [SC1 [STF1 [ST1 [SE1 [SE2 [HV1 [HQ1 HQ2]]]]]]]]].
  destruct v1; destruct v2; try solve [inversion HV1]. simpl in HV1.
  destruct HV1 as [HT [LS1 [LS2 VT]]].
  remember ST1 as ST1'. clear HeqST1'.
  destruct ST1 as [STL1 [STL2 [SP1 [SP2 SP3]]]].

  (* E2 *) 
  eapply envt_store_extend in WFE as WFE'. 2: eapply ST. 2: eauto.
  assert (env_type M' H1 H2 env p2) as WFE2. { eapply envt_tighten; eauto. }

  destruct (E2 M' H1 H2 WFE2 STF1 S1' S2' ST1') as [S1'' [S2'' [M''[v3 [v4 IE]]]]].
  destruct IE as [IE3 [IE4 [SC2 [STF2 [ST2 [SE3 [SE4 [HV2 [HQ3 HQ4]]]]]]]]].
  destruct v3; destruct v4; try solve [inversion HV2]. simpl in HV2.
  subst b0.
  remember ST2 as ST2'. clear HeqST2'.
  destruct ST2 as [STL3 [STL4 [SP4 [SP5 SP6]]]].
  
  exists S1'', S2''.
  exists M'', (vbool (b && b1)), (vbool (b && b1)).
  split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 8: split. 9: split.
  + (* first one *)
    destruct IE1 as [n1 IE1].
    destruct IE3 as [n3 IE3].
    exists (S(n1 + n3)). intros. destruct n. intuition.
    simpl. rewrite IE1. rewrite IE3. eauto. lia. lia.

  + (* 2nd one *)
    destruct IE2 as [n2 IE2].
    destruct IE4 as [n4 IE4].
    exists (S(n2 + n4)). intros. destruct n. intuition.
    simpl. rewrite IE2. rewrite IE4. eauto. lia. lia. 

  + eapply st_trans; eauto. 
  
  + eauto.
  
  + (* store typing *)
    eauto.

  + eapply se_trans; eapply se_sub; eauto. eapply lls_mono; eapply vars_locs_mono; eauto. 
    erewrite <- lls_change with (M := (st1 M)). eapply lls_mono; eapply vars_locs_mono; eauto. unfoldq; intuition.
    eapply stchain_tighten. eapply envt_filter_deep. eapply WFE. eauto. unfoldq; intuition. eauto.
    eapply envt_store_deep_wf. eapply WFE. unfoldq; intuition.
    eapply envt_store_deep_wf. eapply WFE. unfoldq; intuition.
  
  + eapply se_trans; eapply se_sub; eauto. eapply lls_mono; eapply vars_locs_mono; eauto.
    erewrite <- lls_change with (M := (st2 M)). eapply lls_mono; eapply vars_locs_mono; eauto. unfoldq; intuition.
    eapply stchain_tighten. eapply envt_filter_deep. eapply WFE. eauto. unfoldq; intuition. eauto.
    eapply envt_store_deep_wf. eapply WFE. unfoldq; intuition.
    eapply envt_store_deep_wf. eapply WFE. unfoldq; intuition.

  + simpl. eauto. 
  + eapply valq_bool. 
  + eapply valq_bool.
Qed.  
  

(* Fundamental Theorem *)

Theorem fundamental_property : forall t G T p fr q,
    has_type G t T p fr q ->
    sem_type G t t T (plift p) fr (plift q).
Proof.
  intros ? ? ? ? ? ? W. 
  induction W.
  - rewrite plift_empty. eapply sem_true; eauto.
  - rewrite plift_empty. eapply sem_false; eauto.
  - rewrite plift_one. eapply sem_var; eauto.
  - eapply sem_ref; eauto. 
  - eapply sem_get1; eauto. 
  - eapply sem_get2; eauto.
  - rewrite plift_or, plift_if. eapply sem_get; eauto. 
  - rewrite plift_empty. repeat rewrite plift_or. eapply sem_put; eauto.
  - repeat rewrite plift_or in *. repeat rewrite plift_if in *. 
    eapply sem_app; eauto.
  - repeat rewrite plift_or in *.
    repeat rewrite plift_and in *.
    repeat rewrite plift_if in *.
    repeat rewrite plift_one in *.
    eapply sem_abs; eauto.
  - rewrite plift_empty. repeat rewrite plift_or. eapply sem_seq; eauto.
  - eapply sem_sub; eauto.
  - rewrite plift_or, plift_diff, plift_one. 
    eapply sem_sub_var; eauto.
Qed.

(* context typing *)
Inductive ctx_type : (tm -> tm) -> tenv -> ty -> pl -> bool -> pl -> tenv -> ty -> pl -> bool -> pl ->  Prop :=
| cx_top: forall G T p fr q,
    ctx_type (fun x => x) G T p fr q G T p fr q
| cx_ref: forall G t p T  q,
    has_type G t T p false q ->
    psub (plift q)(plift p) ->
    ctx_type (fun x => tref x) G T (plift p) false (plift q) G (TRef T false q) (plift p) true (plift q)
| cx_get1: forall G T p q fr q1,
    psub (plift q1) p ->
    ctx_type (fun x => tget x) G (TRef T false q1) p fr q G T p false (plift q1)
| cx_get2: forall G T p q fr q1,
    ctx_type (fun x => tget x) G (TRef T false q1) p fr q G T p fr q    
| cx_get: forall G T p q fr fr1 q1,
    psub (plift q1) p ->
    ctx_type (fun x => tget x) G (TRef T fr1 q1) p fr (plift q) G T p (if fr1 then fr else false) (por (plift q1) (pif fr1 (plift q)))     
| cx_put1: forall G t1 T p fr1 q1 fr2 q2,
    has_type G t1 (TRef T fr2 q2) p fr1 q1 ->
    psub (plift q2)(plift p) ->
    ctx_type (fun x => tput t1 x) G T (plift p) false (plift q2) G TBool (plift p) false pempty 
| cx_put2: forall G t2 T p fr1 q1 fr2 q2,
    has_type G t2 T p false q2  ->
    psub (plift q2)(plift p) ->
    ctx_type (fun x => tput x t2) G (TRef T fr2 q2) (plift p) fr1 (plift q1) G TBool (plift p) false pempty 
| cx_app1: forall t2 G T1 (fr1:bool) T2 frx q1 fr2 q2 p frf qf ar2 qx (fn1:bool) fn2,
    has_type G t2 T1 p frx qx ->
    (if fn1 then
       if fr1 then
         True
       else
         (frx = false /\ psub (plift qx) (plift q1)) 
     else
       if fr1 then
         psub (pand 
                 (vars_trans' G qf)
                 (vars_trans' G qx))
           (plift q1)
       else
         frx = false /\ psub (plift qx) (plift q1)) -> 
    psub (plift q1) (plift p) ->
    psub (plift q2) (plift p) ->
    ctx_type (fun x => tapp x t2) G (TFun T1 fn1 fr1 q1 T2 fn2 ar2 fr2 q2) (plift p) frf (plift qf) G T2 (plift p) (fn2 && frf || ar2 && frx || fr2) (por (pif fn2 (plift qf)) (por (pif ar2 (plift qx)) (plift q2))) 
| cx_app2: forall t1 G T1 T2 p frf qf frx qx fn1 fr1 q1 fn2 ar2 fr2 q2,
    has_type G t1 (TFun T1 fn1 fr1 q1 T2 fn2 ar2 fr2 q2) p frf qf ->
    (if fn1 then
       if fr1 then
         True
       else
         (frx = false /\ (exists x0, t1 = tvar x0 /\ psub (plift qx) (pone x0))) \/ 
         (frx = false /\ (exists p0 t0, t1 = tabs p0 t0 /\ psub (plift qx) (plift p0))) \/
         (frx = false /\ psub (plift qx) (plift q1)) 
     else
       if fr1 then
         psub (pand 
                 (vars_trans' G qf)
                 (vars_trans' G qx))
           (plift q1)
       else
         frx = false /\ psub (plift qx) (plift q1)) -> 
    psub (plift q1) (plift p) ->     
    psub (plift q2) (plift p) ->
    ctx_type (fun x => tapp t1 x) G T1 (plift p) frx (plift qx)   G T2 (plift p) (fn2 && frf || ar2 && frx || fr2) (plift (qor (qif fn2 qf) (qor (qif ar2 qx) q2)))
| cx_abs: forall G T1 T2 p fn1 fr1 q1 fn2 ar2 fr2 q2 qf,
    closed_ty (length G) T1 ->
    closed_ty (length G) T2 ->
    closed_ql (length G) q1 ->
    closed_ql (length G) q2 ->
    closed_ql (length G) qf ->
    psub (plift q1)(pand (plift p)(plift qf)) ->
    ctx_type (fun x => tabs (qand p qf) x) ((T1,fr1, (qand p (qor q1 (qif fn1 qf))))::G) T2 (plift (qor (qand p qf)(qone (length G)))) fr2 (plift (qor q2 (qor (qif ar2 (qone (length G)))(qif fn2 (qand p qf)))) ) G (TFun T1 fn1 fr1 q1 T2 fn2 ar2 fr2 q2) (plift p) false (plift qf)
| cx_seq1: forall G t1 p p1 p2 q1 q2,
    has_type G t1 TBool p1 false q1 ->
    psub (pand (plift p1)(plift p2)) pempty ->
    psub (plift p1) (plift p) ->
    psub (plift p2) (plift p) ->
    ctx_type (fun x => tseq t1 x) G TBool (plift p2) false q2 G TBool (plift p) false  pempty 
| cx_seq2: forall G t2 p p1 p2 q1 q2,
    has_type G t2 TBool p2 false q2  ->
    psub (pand (plift p1)(plift p2)) pempty ->
    psub (plift p1) (plift p) ->
    psub (plift p2) (plift p) ->
    ctx_type (fun x => tseq x t2) G TBool (plift p1) false q1 G TBool (plift p) false pempty 
| cx_qsub: forall G T p fr1 q fr2 q',
    psub q q' ->
    psub q' (pdom G) -> 
    ctx_type (fun x => x) G T p fr1 q G T p (fr1||fr2) q'
| cx_sub_var: forall G y T p fr1 q1 qx x Tx,
    has_type G y T p fr1 q1 ->
    plift q1 x ->
    indexr x G = Some (Tx, false, qx) ->
    psub (plift qx)(plift p) ->
    ctx_type (fun x => x) G T (plift p) fr1 (plift q1) G T (plift p) fr1 (por (pdiff (plift q1)(pone x)) (plift qx)) 
| cx_trans: forall f g G1 p1 T1 fr1 q1 G2 p2 T2 fr2 q2 G3 p3 T3 fr3 q3,
    ctx_type f G1 T1 p1 fr1 q1 G2 T2 p2 fr2 q2 ->
    ctx_type g G2 T2 p2 fr2 q2 G3 T3 p3 fr3 q3 ->
    ctx_type (fun x => g (f x)) G1 T1 p1 fr1 q1 G3 T3 p3 fr3 q3
.

Theorem congr:
  forall C G1 T1 p fr q G2 T2 p' fr' q',
    ctx_type C G1 T1 p fr q G2 T2 p' fr' q' ->
  forall t t',
    sem_type G1 t t' T1 p fr q ->
    sem_type G2 (C t) (C t') T2 p' fr' q'.
Proof.
  intros ? ? ? ? ? ? ? ? ? ? ? CX.
  induction CX; intros.
  - eauto.
  - eapply sem_ref; eauto.
  - eapply sem_get1; eauto.  
  - eapply sem_get2; eauto.
  - eapply sem_get; eauto.    
  - eapply sem_put; eauto. eapply fundamental_property. eauto. 
  - eapply sem_put; eauto. eapply fundamental_property. eauto. 
  - eapply sem_app; eauto. eapply fundamental_property. eauto.
    destruct fn1.
    destruct fr1. eauto. right. right. eauto.
    destruct fr1. eauto. eauto. 
    destruct fn1.
    destruct fr1. eauto. right. right. eauto.
    destruct fr1. eauto. eauto. 
  - repeat rewrite plift_or. repeat rewrite plift_if. eapply sem_app; eauto. eapply fundamental_property. eauto.
  - repeat rewrite plift_or in *.
    repeat rewrite plift_and in *.
    repeat rewrite plift_one in *.
    repeat rewrite plift_if in *.
    repeat rewrite plift_one in *.
    repeat rewrite plift_and in *.
    eapply sem_abs; eauto. rewrite plift_and. auto.
  - eapply sem_seq. eapply fundamental_property. eauto. all: eauto.
  - eapply sem_seq; eauto. eapply fundamental_property. eauto. 
  - eapply sem_sub; eauto.
  - eapply sem_sub_var; eauto.
  - eapply IHCX2. eapply IHCX1. eauto. 
Qed.


Lemma adequacy: forall e e' fr T,
  sem_type [] e e' T pempty fr pempty   ->
  (exists v M, tevaln [] [] e M v) <-> 
  (exists v' M', tevaln [] [] e' M' v').
Proof. 
  intros. 
  remember (([]:st), ([]:st), (fun x1 x2: nat => False), (fun x1 x2: nat => (fun v1 v2 : vl => False))) as ME. 
  assert (env_type ME [] [] [] pempty) as WFE. { 
    unfold env_type; intuition. 
    1,2: unfoldq; intros; intuition.
    inversion H0; intuition.
    intros ? [? ?]. eapply lls_vars in H3. destruct H3 as [? [? ?]]. eapply lls_var in H5. destruct H5 as [? [? ?]]. inversion H5.
    intros ? [? ?]. eapply lls_vars in H3. destruct H3 as [? [? ?]]. eapply lls_var in H5. destruct H5 as [? [? ?]]. inversion H5.
  }
  assert (store_type [] [] ME) as ST. {
    subst ME. unfold store_type; intuition.
    1,2: unfold sstore_type; intuition; inversion H0.
  }
  
  assert (st_filter ME (st_locs1 ME) (st_locs2 ME)) as STF. {
     subst ME. unfold st_filter; intuition.
     1,2: intros ? ?; unfoldq; intuition.
  }
  unfold sem_type in H.
  specialize (H ME [] [] WFE STF [] [] ST). 
  destruct H as [S1 [S2 [M' [v1 [v2 IE]]]]].
  destruct IE as [? [? [? [? [? ?]]]]].
  split. 
  + intros. exists v2, S2. intuition.
  + intros. exists v1, S1. intuition.
Qed.

Definition context_equiv G t1 t2 T1 p fr q :=
  has_type G t1 T1 p fr q ->
  has_type G t2 T1 p fr q ->
  forall C,
    ctx_type C G T1 (plift p) fr (plift q) [] TBool  (plift qempty) fr (plift qempty) ->
    (exists v1 S1, tevaln [] [] (C t1) S1 v1) <->
    (exists v2 S2, tevaln [] [] (C t2) S2 v2).


(* soundness of binary logical relations *)
Theorem contextual_equivalence: forall G t1 t2 T p fr q,
  has_type G t1 T p fr q ->
  has_type G t2 T p fr q ->
    (sem_type G t1 t2 T (plift p) fr (plift q) -> 
     context_equiv G t1 t2 T p fr q).    
Proof. 
  intros. unfold context_equiv. intros.
  rewrite plift_empty in *.
  assert (sem_type [] (C t1)(C t2) TBool pempty fr pempty). {
    specialize (congr C G  T (plift p) fr (plift q) [] TBool pempty fr pempty ); intuition.
  }
  eapply adequacy; eauto. 
Qed.

(* encapsulation lemma *)
Lemma encapsulation: forall G t T
  (W: has_type G t T qempty false qempty),
  forall H1 H2 S1 S2 M,
  env_type M H1 H2 G pempty ->  
  st_filter M (st_locs1 M)(st_locs2 M) -> 
  store_type S1 S2 M ->
  forall S1' S2' M', 
  st_chain_partial M M' pempty pempty ->
  store_type S1' S2' M' ->
  st_filter M' (st_locs1 M') (st_locs2 M') ->
  exists S1'' S2'' M'' v1 v2,
  exp_type S1' S2' M' H1 H2 t t S1'' S2'' M'' v1 v2 T pempty false pempty.
Proof.
  intros G t T ?. intros H1 H2 S1 S2 M WFE STF ST.
  intros S1' S2' M' STC ST' STF'.
  eapply fundamental_property in W. 
  rewrite plift_empty in W.
  eapply W. eapply envt_store_change. eauto. eauto.
  rewrite vars_locs_empty. rewrite lls_empty.
  rewrite vars_locs_empty. rewrite lls_empty.
  auto. auto. auto.
Qed.

End STLC.
