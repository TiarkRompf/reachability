(*******************************************************************************
* Coq mechanization of the λ$^{\diamond}-calculus.
* - Syntactic definitions
* - Semantic definitions
* - Metatheory
*******************************************************************************)


(* Full safety for STLC *)

(* based on sec3_reach.v *)
(* 

Simply-typed lambda calculus with higher-order mutable store and reachability types, combined 
proof of termination and semantic type soundness (using logical relations).

THIS FILE:


- types and qualifiers
  - overlap (explicit transitive closure)
  - self refs
  - fresh flag
  - no deep subtyping, self/arg refs 
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

Definition pnat n := fun x' =>  x' < n.      (* numeric bound *)

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
    psub (plift q2)(plift p) -> 
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
    has_type env t1 TBool p1 false q1  ->
    has_type env t2 TBool p2 false q2  ->
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


Fixpoint teval(n: nat)(M:stor)(env: venv)(t: tm){struct n}: nat * stor * option (option vl) :=
  match n with
    | 0 => (0, M, None)
    | S n =>
      match t with
        | ttrue      => (1, M, Some (Some (vbool true)))
        | tfalse     => (1, M, Some (Some (vbool false)))
        | tvar x     => (1, M, Some (indexr x env))
        | tref ex    =>
          match teval n M env ex with
            | (dx, M', None)           => (1+dx, M', None)
            | (dx, M', Some None)      => (1+dx, M', Some None)
            | (dx, M', Some (Some vx)) => (1+dx, vx::M', Some (Some (vref (length M'))))
          end
        | tget ex    =>
          match teval n M env ex with
            | (dx, M', None)                     => (1+dx, M', None)
            | (dx, M', Some None)                => (1+dx, M', Some None)
            | (dx, M', Some (Some (vbool _)))    => (1+dx, M', Some None)
            | (dx, M', Some (Some (vabs _ _ _))) => (1+dx, M', Some None)
            | (dx, M', Some (Some (vref x)))     => (1+dx, M', Some (indexr x M'))
          end
        | tput er ex    =>
          match teval n M env er with
            | (dr, M', None)                     => (1+dr, M', None)
            | (dr, M', Some None)                => (1+dr, M', Some None)
            | (dr, M', Some (Some (vbool _)))    => (1+dr, M', Some None)
            | (dr, M', Some (Some (vabs _ _ _))) => (1+dr, M', Some None)
            | (dr, M', Some (Some (vref x))) =>
              match teval (n-dr) M' env ex with
                | (dx, M'', None)                => (1+dr+dx, M'', None)
                | (dx, M'', Some None)           => (1+dr+dx, M'', Some None)
                | (dx, M'', Some (Some vx)) =>
                    match indexr x M'' with
                    | Some v => (1+dr+dx, update M'' x vx, Some (Some (vbool true)))
                    | _      => (1+dr+dx, M'', Some None)
                    end
              end
          end
        | tseq e1 e2   =>
          match teval n M env e1 with
          | (dx, M', None) => (1+dx, M', None)
          | (dx, M', Some None) => (1+dx, M', Some None)
          | (dx, M', Some (Some (vbool b1))) => 
              match teval n M' env e2 with
              | (dr, M'', None) => (1+dx+dr, M'', None)
              | (dr, M'', Some None) => (1+dx+dr, M'', Some None)
              | (dr, M'', Some (Some (vbool b2))) => (1+dx+dr, M'', Some (Some (vbool (b1 && b2))))
              | (dr, M'', Some (Some (vref _))) => (1+dx+dr, M'', Some None)
              | (dr, M'', Some (Some (vabs _ _ _))) => (1+dx+dr, M'', Some None)
              end
          | (dx, M', Some (Some (vref _))) => (1+dx, M', Some None)
          | (dx, M', Some (Some (vabs _ _ _))) => (1+dx, M', Some None)
          end  
        | tabs p y   => (1, M, Some (Some (vabs env p y)))
        | tapp ef ex =>
          match teval n M env ef with
            | (df, M', None)                  => (1+df, M', None)
            | (df, M', Some None)             => (1+df, M', Some None)
            | (df, M', Some (Some (vbool _))) => (1+df, M', Some None)
            | (df, M', Some (Some (vref _)))  => (1+df, M', Some None)
            | (df, M', Some (Some (vabs env2 _ ey))) =>
              match teval (n-df) M' env ex with
                | (dx, M'', None)           => (1+df+dx, M'', None)
                | (dx, M'', Some None)      => (1+df+dx, M'', Some None)
                | (dx, M'', Some (Some vx)) =>
                  match teval (n-df-dx) M'' (vx::env2) ey with
                    | (dy, M''', ry) => (1+df+dx+dy, M''', ry)
                  end
              end
          end
      end
  end.


Definition tevaln M env e M' v :=
  exists nm,
  forall n,
    n > nm ->
    teval n M env e = (nm, M', Some (Some v)).



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



(* store typings *)

(* list of (semantic type *  qual) pairs *)

Definition stty: Type := list ((vl -> Prop) * ql).

Fixpoint locs_locs_stty_fix (M: stty) (q: ql): ql :=
  match M with
  | [] => q
  | (_,qt) :: M =>
      if q (length M) then
        qor (locs_locs_stty_fix M q) (locs_locs_stty_fix M qt)
      else
        locs_locs_stty_fix M q
  end.

Inductive locs_locs_stty: stty -> pl -> pl :=
| lls_z: forall M (q:pl) x,
    q x ->
    locs_locs_stty M q x
| lls_s: forall M (q:pl) x x1 vt qt,
    q x1 ->
    indexr x1 M = Some (vt, qt) ->
    locs_locs_stty M (plift qt) x ->
    locs_locs_stty M q x.
  


Definition st_types (M: stty) := M.
Definition st_locs (M: stty) := pdom M.

Definition store_type (S: stor) (M: stty) :=
  length M = length S /\
    (forall l,
      st_locs M l ->
      exists vt qt v,
        indexr l M = Some (vt, qt) /\
          indexr l S = Some v /\
          vt v /\
          psub (locs_locs_stty M (val_locs v)) (locs_locs_stty M (plift qt)) /\
          psub (plift qt) (pnat l))
.


Definition st_zero: stty := [].

Definition st_extend M1 vt qt: stty :=
  (vt,qt)::M1.

Definition st_chain (M: stty) (M1: stty) q :=
  psub q (st_locs M) /\
  psub q (st_locs M1) /\
  forall l, q l ->
            indexr l M = indexr l M1.


Definition pstdiff M' M :=
  pdiff (st_locs M') (st_locs M).


#[global] Hint Unfold st_types.
#[global] Hint Unfold st_locs.
#[global] Hint Unfold pstdiff. 


(* store preservation invariant *)

Definition store_effect (S S1: stor) (p: pl) :=
  forall l v,
    ~ p l -> 
    indexr l S = Some v ->
    indexr l S1 = Some v.


Fixpoint val_type (M:stty) (H:venv) v T : Prop :=
  match v, T with
  | vbool b, TBool =>
      True
  | vref l, TRef T fr q =>
      closed_ty (length H) T /\
      fr = false /\
      psub (plift q) (pdom H) /\
      psub (locs_locs_stty M (val_locs v)) (st_locs M) /\ 
      exists vt qt,
        indexr l M = Some (vt, qt) /\ 
        (forall M',
            st_chain M M' (locs_locs_stty M (plift qt)) ->
            forall v,
              psub (locs_locs_stty M' (val_locs v)) (locs_locs_stty M' (plift qt)) -> 
              (vt v <-> val_type M' H v T)) /\
        plift qt = vars_locs H (plift q) /\
        psub (locs_locs_stty M (plift qt)) (locs_locs_stty M (pone l)) 
  | vabs G py ty, TFun T1 fn1 fr1 q1 T2 fn2 ar2 fr2 q2 =>
        closed_ty (length H) T1 /\
        (psub (plift q1) (pdom H)) /\
        closed_ty (length H) T2 /\
        (psub (plift q2) (pdom H)) /\
        (psub (locs_locs_stty M (val_locs v)) (st_locs M)) /\
        (forall S' M' vx,
            st_chain M M' (locs_locs_stty M (val_locs v))
            ->
              store_type S' M'
            ->
            val_type
              M'
              H
              vx
              T1
            -> 
              psub (locs_locs_stty M' (val_locs vx))
                (por (pif fn1 (locs_locs_stty M' (val_locs v)))
                   (por (pif fr1 (pnot (locs_locs_stty M' (val_locs v))))
                      (locs_locs_stty M' (vars_locs H (plift q1)))))
            ->
              exists S'' M'' vy,
                tevaln
                  S'
                  (vx::G)
                  ty
                  S''
                  vy
                /\
                  st_chain M' M'' (st_locs M') 
                /\
                  store_type S'' M''
                /\
                  store_effect S' S'' (por (locs_locs_stty M' (val_locs v)) (locs_locs_stty M' (val_locs vx)))
                /\
                  val_type
                    M''
                    H
                    vy
                    T2
                /\
                  psub (locs_locs_stty M'' (val_locs vy))
                    (por (pand (locs_locs_stty M'' (vars_locs H (plift q2))) (locs_locs_stty M'' (val_locs v))) (* allow v \/ vx? <- no, support tightening of q2 if fn2 *)
                       (por (pif fn2 (locs_locs_stty M'' (val_locs v)))
                          (por (pif ar2 (locs_locs_stty M'' (val_locs vx)))
                             (pif fr2 (pnot (pdom M')))))))
  | _,_ =>
      False
  end.


Definition val_qual (M M1: stty) H v p fr (q: pl) :=
  psub (locs_locs_stty M1 (val_locs v))
    (por (locs_locs_stty M1 (vars_locs H (pand p q))) (* locs(v) & M & ~(p&q) = O *)
       (pif fr (pnot (pdom M)))).


Definition exp_type S M H t T p fr q :=
  exists S' M' v,
    tevaln S H t S' v /\
    st_chain M M' (st_locs M) /\
    store_type S' M' /\
    store_effect S S' (locs_locs_stty M (vars_locs H p)) /\  
    val_type M' H v T /\
    val_qual M M' H v p fr q.



Definition env_type M H G p :=
  length H = length G /\
    psub p (pdom H) /\
    (forall x T fr (q:ql),
        indexr x G = Some (T, fr, q) ->
        exists v : vl,
          closed_ql x q /\
          indexr x H = Some v /\
          (p x -> val_type M H v T) /\
          (fr = false -> psub (plift q) p -> psub (locs_locs_stty M (val_locs v)) (locs_locs_stty M (vars_locs H (plift q))))) /\
    (forall q q',
        psub q p ->
        psub q' p ->
        psub (pand (vars_trans G q) (vars_trans G q')) p ->
        psub (pand (locs_locs_stty M (vars_locs H q)) (locs_locs_stty M (vars_locs H q')))
          (locs_locs_stty M (vars_locs H (pand (vars_trans G q) (vars_trans G q'))))).


Definition sem_type G t T p fr q :=
  forall S M E,
    env_type M E G p ->
    store_type S M  ->
    exp_type S M E t T p fr q. 


#[export] Hint Constructors ty: core.
#[export] Hint Constructors tm: core.
#[export] Hint Constructors vl: cor.


#[export] Hint Constructors has_type: core.

#[export] Hint Constructors option: core.
#[export] Hint Constructors list: core.


(* ---------- qualifier reflection & tactics  ---------- *)

Ltac unfoldq := unfold val_qual, psub, pdom, pnat, pdiff, pnot, pif, pand, por, pempty, pone, var_locs, vars_locs in *.
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



(* ---------- closedness, vars_locs lemmas  ---------- *)

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

Lemma  closedq_and: forall q1 q2 m,
  (closed_ql m q1 \/ closed_ql m q2) -> 
  closed_ql m (qand q1 q2).
Proof.
  intros. destruct H; unfold closed_ql in *; intros;
  bdestruct (qand q1 q2 x); intuition.
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


Lemma stchain_chain: forall M1 M2 M3 q1 q2,
  st_chain M1 M2 q1 ->
  st_chain M2 M3 q2 ->
  st_chain M1 M3 (pand q1 q2).
Proof.
  intros. destruct H, H0, H1, H2.
  split. unfoldq. intuition.
  split. unfoldq. intuition.
  intros. rewrite H3, H4. eauto. eapply H5. eapply H5.
Qed.

Lemma stchain_tighten: forall M1 M2 q1 q2,
  st_chain M1 M2 q2 ->
  psub q1 q2 ->
  st_chain M1 M2 q1.
Proof.
  intros. destruct H. destruct H1.
  split. unfoldq. intuition.
  split. unfoldq. intuition.
  intros. rewrite H2. eauto. eauto.
Qed.


Lemma stchain_chain': forall M1 M2 M3 q1 q2,
  st_chain M1 M2 q1 ->
  st_chain M2 M3 q2 ->
  psub q2 q1 ->
  st_chain M1 M3 q2.
Proof.
  intros. eapply stchain_tighten in H; eauto.
  replace q2 with (pand q2 q2). eapply stchain_chain; eauto.
  eapply functional_extensionality. intros.
  eapply propositional_extensionality. unfoldq. intuition. 
Qed.

Lemma stchain_chain'': forall M1 M2 M3 q1 q2,
  st_chain M1 M2 q1 ->
  st_chain M2 M3 q2 ->
  psub q1 q2 ->
  st_chain M1 M3 q1.
Proof.
  intros. eapply stchain_tighten in H0; eauto.
  replace q1 with (pand q1 q1). eapply stchain_chain; eauto.
  eapply functional_extensionality. intros.
  eapply propositional_extensionality. unfoldq. intuition. 
Qed.


Lemma stchain_refl: forall M,
    st_chain M M (st_locs M).
Proof.
  intros. split. unfoldq. intuition.
  split. unfoldq. intuition.
  intros. eauto.
Qed.

Lemma st_mono: forall M M',
  st_chain M M' (st_locs M) ->
  length M <= length M'.
Proof.
  intros. destruct H as [? [? ?]].
  unfoldq; intuition. unfold st_locs, pdom in *. 
  destruct (length M). lia. eapply H0. lia.
Qed. 


Lemma lls_vars: forall M E q l,
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


Lemma lls_mono: forall M q q',
    psub q q' ->
    psub (locs_locs_stty M q) (locs_locs_stty M q').
Proof.
  intros. intros ? ?. inversion H0; subst. left. unfoldq. intuition.
  eapply lls_s; eauto. 
Qed.


Lemma lls_change: forall M M' q,
    st_chain M M' (locs_locs_stty M q) ->
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
    - eapply lls_mono; eauto. eapply vars_locs_monotonic; eauto. unfoldq; intuition.
    - eapply lls_mono; eauto.  eapply vars_locs_monotonic; eauto. unfoldq; intuition.
Qed.


(* ---------- val_type lemmas  ---------- *)

Lemma valt_wf: forall T M H v,
    val_type M H v T ->
    psub (val_locs v) (st_locs M).
Proof. 
  intros T. induction T; intros; destruct v; simpl in *; intuition.
  + rewrite val_locs_bool. auto. unfoldq. intuition.
  + rewrite val_locs_ref. unfoldq. intuition. subst i. eapply H3; eauto. left. rewrite val_locs_ref. unfoldq; intuition.
  + intros ? ?. eapply H4. left. eauto. 
Qed.

Lemma valt_deep_wf: forall T M H v,
    val_type M H v T ->
    psub (locs_locs_stty M (val_locs v)) (st_locs M).
Proof.
  intros T. induction T; intros; destruct v; simpl in *; intuition.
  + rewrite val_locs_bool. intros ? ?. inversion H1; subst. unfoldq. intuition. unfoldq. intuition. 
Qed.


Lemma valt_closed: forall T M H v,
    val_type M H v T ->
    closed_ty (length H) T.
Proof. 
  intros T. induction T; intros; destruct v; simpl in *; intuition.
  + econstructor.
  + repeat econstructor; eauto.
  + econstructor; eauto. 
Qed.

Lemma valt_store_change: forall T M' M H v,
    val_type M H v T ->
    st_chain M M' (locs_locs_stty M (val_locs v)) ->
    val_type M' H v T.
Proof.
  intros T. induction T; intros; destruct v; simpl in *; intuition.
  + rewrite val_locs_ref in *. intros ? ?. eapply H1. erewrite lls_change. eauto. eapply stchain_tighten. eauto. intros ? ?. eauto. 
  + rewrite val_locs_ref in H1.
    remember H1 as H7. destruct H1 as (? & ? & ?). clear HeqH7.
    destruct H6 as [vt [qt [IX [VT [QT QT1]]]]].
    assert (st_chain M M' (locs_locs_stty M (plift qt))). {
      eapply stchain_tighten. eauto. intros ? ?. eapply lls_s. 2: eauto. intuition. eauto. }
    exists vt, qt.
    split. 2: split. 3: split. 
    * rewrite <-e. eauto. left. intuition.
    * intros M''. intros.
      assert (st_chain M M'' (locs_locs_stty M (plift qt))). {
        eapply stchain_chain'. eauto. erewrite lls_change. eauto. 
        eauto. intros ? ?. eauto. }
      eapply VT. eauto. eauto. 
    * eauto. 
    * rewrite <-lls_change with (M:=M) (M':=M').
      rewrite <-lls_change with (M:=M) (M':=M').
      eauto. eauto. eauto.
  + intros ? ?. eapply H1. erewrite lls_change. eauto.
    eapply stchain_tighten. eauto. intros ? ?. eauto. 
  + eapply H7. 
    eapply stchain_chain'. eauto. 
    erewrite lls_change. eauto. eapply stchain_tighten. eauto. intros ? ?.  eauto. 
    intros ? ?. eauto. 
    eauto. eauto. eauto.
Qed.

Lemma valt_store_extend: forall T M' M H v,
    val_type M H v T ->
    psub (locs_locs_stty M (val_locs v)) (st_locs M) ->
    st_chain M M' (st_locs M) ->
    val_type M' H v T.
Proof.
  intros ? ? ?. 
  replace (st_locs M') with (pnat (length M')).
  intros. eapply valt_store_change; eauto.
  eapply stchain_tighten; eauto. 
  unfold st_locs. unfoldq. eauto. 
Qed.



Lemma valt_extend: forall T M H' H v,
    closed_ty (length H) T ->
    val_type M (H'++H) v T <-> val_type M H v T.
Proof. 
  intros T. induction T; split; intros; destruct v; simpl in *; intuition.
  - inversion H0. auto.
  - inversion H0. auto.
  - (* Ref shrink *)
    destruct H6 as [vt [qt [IX [VT [QT QT1]]]]].
    exists vt, qt. intuition.
    eapply IHT; eauto. inversion H0. auto. eapply VT; eauto.
    eapply VT; eauto. eapply IHT; eauto. inversion H0. auto. 
    rewrite vars_locs_extend in QT. eauto. inversion H0. eauto.
  - inversion H0. eapply closedty_extend. eauto. rewrite app_length. lia. 
  - unfoldq. intuition. rewrite app_length. eapply H3 in H5. lia. 
  - (* Ref grow *)
    destruct H6 as [vt [qt [IX [VT [QT QT1]]]]].
    exists vt, qt. intuition.
    eapply IHT; eauto. inversion H0. eauto. eapply VT; eauto.
    eapply VT; eauto. eapply IHT; eauto. inversion H0.
    rewrite vars_locs_extend. eauto. eauto. 
  - inversion H0. auto.
  - inversion H0. auto.
  - inversion H0. auto.
  - inversion H0. auto.
  - (* Abs shrink *)
    inversion H0. subst.
    destruct (H7 S' M' vx) as [S'' [M'' [vy [HEY HVY]]]]. eauto. eauto. 
    eapply IHT1; eauto.
    rewrite vars_locs_extend; auto.
    exists S'', M'', vy. intuition.
    eapply IHT2; eauto.
    rewrite vars_locs_extend in H17.
    eauto. eauto.
  - eapply closedty_extend; eauto.
  - eapply closedq_extend; eauto.
  - eapply closedty_extend; eauto.
  - unfoldq. rewrite app_length. intuition. eapply H4 in H6. lia.
  - (* Abs grow *)
    inversion H0. subst.
    destruct (H7 S' M' vx) as [S'' [M'' [vy [HEY [ST2 [HVY HQY]]]]]]. eauto. eauto.
      eapply IHT1; eauto. 
      rewrite vars_locs_extend in H10; auto.
    exists S'', M'', vy. intuition.
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

Lemma valq_bool: forall M M1 H b p q,
    val_qual M M1 H (vbool b) p false q.
Proof.
  intros. unfoldq. rewrite val_locs_bool. intuition.
  inversion H0. subst. destruct H1. subst. destruct H1.
Qed.

Lemma valq_abs: forall M M1 H t p fr q,
    val_qual M M1 H (vabs H (qand p q) t) (plift p) fr (plift q).
Proof.
  intros. unfoldq.
  rewrite val_locs_abs.
  rewrite plift_and.
  intuition. 
Qed.


Lemma valq_sub: forall M M1 H v p q fr fr' q',
    val_qual M M1 H v p fr q ->
    psub q q' ->
    psub q' (pdom H) ->
    val_qual M M1 H v p (fr || fr') q'.
Proof.
  intros. intros ? ?. 
  destruct (H0 x) as [H_q | H_fr]. eauto. 
  - (* q  *) left. eapply lls_mono. 2: eauto. eapply vars_locs_monotonic. unfoldq. intuition.
  - (* fr *) destruct fr. 2: contradiction. right. eauto.
Qed.


(* ---------- environment lemmas  ---------- *)

Lemma wf_env_type: forall M H G p, 
  env_type M H G p -> 
  (length H = length G /\
    pdom H = pdom G) .
Proof.
    intros. unfold env_type in H0. intuition.
    unfold pdom. rewrite H1. auto.
Qed.

Lemma envt_telescope: forall M H G p,
    env_type M H G p -> telescope G.
Proof.
  intros. destruct H0 as (? & ? & ? & ?).
  intros ? ? ? ? ?. edestruct H2; eauto.
  intuition.
Qed.


Lemma env_type_store_wf: forall M H G p q,
    env_type M H G p ->
    psub q p ->
    psub (vars_locs H q) (st_locs M).
Proof.
  intros. destruct H0 as [L [P [W1 W2]]]; intuition.
  unfoldq. intuition.
  destruct H0 as [? [? ?]].
  destruct H2 as [? [? ?]].
  assert (x0 < length H). eapply indexr_var_some'. eauto. 

  assert (exists xtq, indexr x0 G = Some xtq) as TY.
  rewrite L in H4. eapply indexr_var_some in H4. intuition.
  destruct TY as [TQ  ?]. destruct TQ as [[T0 fr0] q0].
  destruct (W1 x0 T0 fr0 q0) as [vx [? ?]]. eauto.
  
  intuition. rewrite H2 in H8. inversion H8. subst x1.
  eapply valt_wf; eauto. 
Qed.



Lemma env_type_store_deep_wf: forall M H G p q,
    env_type M H G p ->
    psub q p ->
    psub (locs_locs_stty M (vars_locs H q)) (st_locs M).
Proof.
  intros. intros ? ?. inversion H2; subst. eapply env_type_store_wf; eauto.
  destruct H0 as [L [P [W1 W2]]]; intuition.
  destruct H3 as (? & ? & ? & ? & ?).
  assert (x0 < length H). eapply indexr_var_some'. eauto.
  

  assert (exists xtq, indexr x0 G = Some xtq) as TY.
  rewrite L in H7. eapply indexr_var_some in H7. intuition.
  destruct TY as [TQ  ?]. destruct TQ as [[T0 fr0] q0].
  destruct (W1 x0 T0 fr0 q0) as [vx [? ?]]. eauto.
  
  intuition. rewrite H3 in H11. inversion H11. subst x2.
  eapply valt_deep_wf; eauto.

  eapply lls_s. eauto. eauto. eauto. 
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
    destruct (W x T fr q); eauto.
    intuition. exists x0. intuition.
    eapply H9. unfoldq. intuition. 
  - intros.
    destruct W as [? W].
    eapply W.
    unfoldq. intuition.
    unfoldq. intuition.
    unfoldq. intuition.
Qed.

Lemma envt_store_extend: forall M M' H G p,
    env_type M H G p ->
    st_chain M M' (st_locs M) ->
    env_type M' H G p.
Proof.
  intros. remember H0 as WFE1. clear HeqWFE1. destruct H0 as [L [P W]]. 
  repeat split; auto.
  - intros.
    destruct W as [W W'].
    destruct (W _ _  _ _ H0) as [vx [QH [IH [HVX HF]]]]; intuition.
    exists vx; intuition.
    eapply valt_store_extend. eauto. eapply valt_deep_wf. eauto. auto.
    rewrite lls_change with (M:=M) (M':=M') in H5.
    rewrite lls_change with (M:=M) (M':=M') in H5.
    eauto. 
    eapply stchain_tighten. eauto. eapply env_type_store_deep_wf. eauto. eauto.
    eapply stchain_tighten. eauto. intros ? ?. eapply env_type_store_deep_wf. eauto. eauto. eauto. 
  - intros. 
    destruct W as [W' W].
    intros ? [? ?]. specialize (W _ _ H0 H2 H3).
    erewrite <-lls_change in H4.
    erewrite <-lls_change in H5.
    erewrite <-lls_change.
    eapply W. split; eauto.

    eapply stchain_tighten. eauto.
    eapply env_type_store_deep_wf. eauto. eauto.  
    eapply stchain_tighten. eauto.
    eapply env_type_store_deep_wf. eauto. eauto.  
    eapply stchain_tighten. eauto.
    eapply env_type_store_deep_wf. eauto. eauto.  
Qed.

Lemma envt_store_change: forall M M' H G p,
  env_type M H G p ->
  st_chain M M' (locs_locs_stty M (vars_locs H p)) ->
  env_type M' H G p.
Proof.
  intros. remember H0 as WFE1. clear HeqWFE1. destruct H0 as [L [P W]]. 
  repeat split; auto.
  - intros.
    destruct W as [W W'].
    destruct (W _ _  _ _ H0) as [vx [QH [IH [HVX HF]]]]; intuition.
    exists vx; intuition.
    + eapply valt_store_change; eauto.  
      eapply stchain_tighten. eauto. 
      intros ? Q. eapply lls_vars'; eauto.  eapply lls_var'; eauto.
    + rewrite lls_change with (M:=M) (M':=M') in H5.
      rewrite lls_change with (M:=M) (M':=M') in H5.
      eauto. 
      eapply stchain_tighten. eauto. eapply lls_mono; eauto. eapply vars_locs_monotonic; eauto.
      eapply stchain_tighten. eauto. 
      intros ? ?. eapply H5 in H4. eapply lls_mono; eauto. eapply vars_locs_monotonic; eauto.
  - intros. 
    destruct W as [W' W].
    intros ? [? ?]. specialize (W _ _ H0 H2 H3).
    erewrite <-lls_change in H4.
    erewrite <-lls_change in H5.
    erewrite <-lls_change.
    eapply W. split; eauto.

    eapply stchain_tighten. eauto.
    eapply lls_mono; eauto. eapply vars_locs_monotonic; eauto.
    eapply stchain_tighten. eauto.
    eapply lls_mono; eauto. eapply vars_locs_monotonic; eauto.
    eapply stchain_tighten. eauto.
    eapply lls_mono; eauto. eapply vars_locs_monotonic; eauto.
Qed.  



Lemma envt_extend_full: forall M M1 H G vx T1 p fr1 q1 qf,
    env_type M H G p ->
    val_type M1 H vx T1 ->
    psub qf p ->
    psub (plift q1) qf -> 
    psub (pand (locs_locs_stty M1 (vars_locs H qf)) (locs_locs_stty M1 (val_locs vx)))
      (locs_locs_stty M1 (vars_locs H (plift q1))) ->
    (fr1 = false -> psub (locs_locs_stty M1 (val_locs vx)) (locs_locs_stty M1 (vars_locs H (plift q1)))) ->
    closed_ty (length H) T1 ->
    closed_ql (length H) q1 ->
    True ->
    st_chain M M1 (locs_locs_stty M (vars_locs H qf)) ->
    env_type M1 (vx :: H) ((T1, fr1, q1) :: G) (por qf (pone (length H))).
Proof. 
  intros. apply wf_env_type in H0 as H0'. destruct H0' as (L' & PD (*& SG*)). 
  rename H8 into CH.

  rename H0 into WFE.
  remember True as H0.
  rename H9 into SC.
  
  remember WFE as WFE1. clear HeqWFE1.
  destruct WFE as [L [P [W1 W2]]].
  assert (psub p (pdom G)). rewrite <-PD. eauto. 

  repeat split; eauto.
  - simpl. eauto.
  - unfoldq. simpl. intuition.
  - intros.
    bdestruct (x =? length G); intuition. 
    + subst. rewrite indexr_head in H9. inversion H9. subst.
      exists vx. repeat split.
      rewrite <-L. eauto. 
      rewrite <-L. rewrite indexr_head. auto.
      intros. eapply valt_extend1; auto.
      rewrite <-vars_locs_extend with (H':=[vx]) in H5; eauto. 
    + rewrite indexr_skip in H9. 
      specialize (W1 x T fr q H9).
      assert (x < length H). { rewrite L. apply indexr_var_some' in H9. auto. }
      rewrite indexr_skip.
      destruct W1 as [v [Hcl [IH [VALT FR]]]].
      exists v. repeat split.
      auto. auto.  
      intros. eapply valt_extend1. eapply valt_closed in VALT; eauto. unfoldq. intuition. 
      (* XXX store extend/tighten XXX *) {
        eapply valt_store_change. eapply VALT. unfoldq. intuition.        
        assert (qf x). { destruct H12. eauto. unfoldq. lia. }
        eapply stchain_tighten. eauto.
        eapply lls_mono. unfoldq. intuition. exists x. intuition. eexists. eauto.
      } {
        intros. intros ? ?.
        assert (psub (plift q) qf). {
          intros ? A. eapply H13 in A as B. eapply Hcl in A as C.
          eapply indexr_var_some' in IH. unfoldq. intuition. }

        erewrite lls_change with (M:=M) (M':=M1) in FR.
        erewrite lls_change with (M:=M) (M':=M1) in FR.
        rewrite <-vars_locs_extend with (H':=[vx]) in FR; eauto.
        eapply FR. eauto. unfoldq. intuition. eauto. unfoldq; intuition. 
        
        eapply stchain_tighten. eauto. intros ? ?.
        eapply lls_mono. 2: eauto. eapply vars_locs_monotonic. eauto.

        eapply stchain_tighten. eauto. intros ? ?.
        eapply lls_mono. eapply vars_locs_monotonic.
        2: eapply FR. eauto. eauto. unfoldq. intuition. eauto. 
      }
        
      lia. lia.
      
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
      assert (psub (pand (vars_trans G (pand (pdom H) q)) (vars_trans G (pand (pdom H) q'))) qf) as QSUBTR1. {
        intros ? [? ?]. destruct (QSUBTR x2) as [? | ?].
        split. (* extend *)
        eapply vt_extend. eapply vt_mono. 2: eapply H11. unfoldq. intuition.
        eapply vt_extend. eapply vt_mono. 2: eapply H12. unfoldq. intuition.
        eauto.
        eapply vt_closed in H11 as CL; eauto. unfoldq. intuition. unfoldq. intuition. (* contra *)
      }
      
      eassert _ as W3. {
        eapply (W2 (pand (pdom H) q) (pand (pdom H) q')) with (x:=x).

        intros ? ?. destruct (QSUB x2) as [? | ?]. unfoldq. intuition. 
        eauto. eauto. unfoldq. lia.
        
        intros ? ?. destruct (QSUB' x2) as [? | ?]. unfoldq. intuition. 
        eauto. eauto. unfoldq. lia. 

        intros ? ?. eapply H2. eapply QSUBTR1. eauto.

        split.

        erewrite lls_change. 
        eapply lls_vars'. eapply lls_mono. 2: eapply VLQ. intros ? ?. eapply var_locs_shrink. eauto. unfoldq. intuition. unfoldq. intuition.
        eapply stchain_tighten. eauto. eapply lls_mono. eapply vars_locs_monotonic. unfoldq. intuition. destruct (QSUB x2); eauto. lia.
        
        erewrite lls_change. 
        eapply lls_vars'. eapply lls_mono. 2: eapply VLQ'. intros ? ?. eapply var_locs_shrink. eauto. unfoldq. intuition. unfoldq. intuition.
        eapply stchain_tighten. eauto. eapply lls_mono. eapply vars_locs_monotonic. unfoldq. intuition. destruct (QSUB' x2); eauto. lia.
      }

      erewrite lls_change in W3.
      
      eapply lls_vars in W3. destruct W3 as (? & (? & ?) & ?). 
      
      eapply lls_vars'. eapply lls_mono. 2: eauto. intros ? ?. eapply var_locs_extend. eauto. split.
      eapply vt_extend. eapply vt_mono. 2: eapply H11. unfoldq. intuition.
      eapply vt_extend. eapply vt_mono. 2: eapply H12. unfoldq. intuition.

      eapply stchain_tighten. eauto.

      eapply lls_mono. eapply vars_locs_monotonic. 

      eapply QSUBTR1. 
      
    + (* qf, x *)
      unfold pone in H10. subst x1. 
      
      assert (psub (pand (vars_trans G (pand (pdom H) q)) (vars_trans G (plift q1))) qf) as QSUBTR1. {
        intros ? [? ?]. destruct (QSUBTR x1) as [? | ?].
        split. {
          eapply vt_extend. eapply vt_mono. 2: eapply H10. unfoldq. intuition. (* extend q *)
        }{
          eapply vt_head. eauto. rewrite <-PD. eauto. rewrite <-L. eauto. eauto. (* pick q1 *)
        }
        eauto.
        eapply vt_closed in H11; eauto. unfoldq. intuition. unfoldq. intuition. (* contra *)
      }

      eassert _ as W3. {
        eapply (W2 (pand (pdom H) q) (plift q1)) with (x:=x).

        intros ? ?. destruct (QSUB x1) as [? | ?]. unfoldq. intuition. 
        eauto. eauto. unfoldq. lia.

        unfoldq. intuition.

        intros ? ?. eapply H2. eapply QSUBTR1. eauto.

        split. 

        erewrite lls_change. 
        eapply lls_vars'. eapply lls_mono. 2: eapply VLQ. intros ? ?. eapply var_locs_shrink. eauto. unfoldq. intuition. unfoldq. intuition.
        eapply stchain_tighten. eauto. eapply lls_mono. eapply vars_locs_monotonic. unfoldq. intuition. destruct (QSUB x1); eauto. lia.

        erewrite lls_change.
        eapply H4. split.
        eapply lls_vars'. eapply lls_mono. 2: eapply VLQ. intros ? ?. eapply var_locs_shrink. eauto. unfoldq. intuition. eauto. 

        eapply lls_var in VLQ'. destruct VLQ' as (? & IX & ?).
        rewrite indexr_head in IX. inversion IX. eauto.
        eapply stchain_tighten. eauto. eapply lls_mono. eapply vars_locs_monotonic. unfoldq. intuition.
      }

      erewrite lls_change in W3.

      eapply lls_vars in W3. destruct W3 as (? & (? & ?) & ?). 

      eapply lls_vars'. eapply lls_mono. 2: eauto. intros ? ?. eapply var_locs_extend. eauto. split.
      eapply vt_extend. eapply vt_mono. 2: eapply H10. unfoldq. intuition.
      eapply vt_head. eauto. rewrite <-PD. eauto. rewrite <-L. eauto. eauto.

      eapply stchain_tighten. eauto.
      eapply lls_mono. eapply vars_locs_monotonic.
      eapply QSUBTR1.
      

    + (* x, qf *)
      unfold pone in H9. subst x0. 
      
      assert (psub (pand (vars_trans G (plift q1)) (vars_trans G (pand (pdom H) q'))) qf) as QSUBTR1. {
        intros ? [? ?]. destruct (QSUBTR x0) as [? | ?].
        split. {
          eapply vt_head. eauto. rewrite <-PD. eauto. rewrite <-L. eauto. eauto. (* pick q1 *)
        }{
          eapply vt_extend. eapply vt_mono. 2: eapply H11. unfoldq. intuition. (* extend q' *)
        }
        eauto.
        eapply vt_closed in H11; eauto. unfoldq. intuition. unfoldq. intuition. (* contra *)
      }

      eassert _ as W3. {
        eapply (W2 (plift q1) (pand (pdom H) q')) with (x:=x).

        unfoldq. intuition.

        intros ? ?. destruct (QSUB' x0) as [? | ?]. unfoldq. intuition. 
        eauto. eauto. unfoldq. lia.

        intros ? ?. eapply H2. eapply QSUBTR1. eauto.

        split. 

        erewrite lls_change.
        eapply H4. split.
        eapply lls_vars'. eapply lls_mono. 2: eapply VLQ'. intros ? ?. eapply var_locs_shrink. eauto. unfoldq. intuition. eauto. 

        eapply lls_var in VLQ. destruct VLQ as (? & IX & ?).
        rewrite indexr_head in IX. inversion IX. eauto.
        eapply stchain_tighten. eauto. eapply lls_mono. eapply vars_locs_monotonic. unfoldq. intuition.

        erewrite lls_change. 
        eapply lls_vars'. eapply lls_mono. 2: eapply VLQ'. intros ? ?. eapply var_locs_shrink. eauto. unfoldq. intuition. unfoldq. intuition.
        eapply stchain_tighten. eauto. eapply lls_mono. eapply vars_locs_monotonic. unfoldq. intuition. destruct (QSUB' x0); eauto. lia.
      }

      erewrite lls_change in W3.

      eapply lls_vars in W3. destruct W3 as (? & (? & ?) & ?). 

      eapply lls_vars'. eapply lls_mono. 2: eauto. intros ? ?. eapply var_locs_extend. eauto. split.
      eapply vt_head. eauto. rewrite <-PD. eauto. rewrite <-L. eauto. eauto.
      eapply vt_extend. eapply vt_mono. 2: eapply H11. unfoldq. intuition.

      eapply stchain_tighten. eauto.
      eapply lls_mono. eapply vars_locs_monotonic.
      eapply QSUBTR1.
      
    + (* x, x *)
      unfold pone in H9, H10.
      subst x0 x1.

      eapply lls_vars'. eauto. split.
      left. eauto. left. eauto. 
Qed.



Lemma lt_stlocs: forall M i x,
    pnat i x -> i <= length M ->
    st_locs M x.
Proof.
  intros. unfold st_locs. unfoldq. lia.
Qed.

Lemma lt_stlocs': forall M i,
    i <= length M ->
    psub (pnat i) (st_locs M).
Proof.
  intros. intros ? ?. unfold st_locs. unfoldq. lia.
Qed.

Lemma lls_closed: forall M S q1,
    store_type S M ->
    psub (locs_locs_stty M q1) (por q1 (st_locs M)).
Proof.
  intros. intros ? ?. induction H0; intros; subst.
  - left. eauto.
  - right. destruct IHlocs_locs_stty. eauto.
    destruct H.
    assert (x1 < length M). eapply indexr_var_some'. eauto. 
    destruct (H4 x1) as (vt' & frt' & qt' & v & ?); eauto. 
    intuition. 
    eapply lt_stlocs. eapply H10. congruence. lia.
    eauto. 
Qed.

Lemma lls_closed': forall M S q1,
    store_type S M ->
    psub q1 (st_locs M) -> 
    psub (locs_locs_stty M q1) (st_locs M).
Proof.
  intros. intros ? ?.
  eapply lls_closed in H1; eauto.
  destruct H1; eauto. 
Qed.


Lemma overlapping: forall S' M M' M'' H G p vf vx frf qf frx qx q1
    (ST : store_type S' M')
    (WFE: env_type M H G p)
    (CH1: st_chain M M' (st_locs M))
    (CH2: st_chain M' M'' (st_locs M'))
    (HQF: val_qual M M' H vf p frf qf)
    (HQX: val_qual M' M'' H vx p frx qx)
    (A: psub (locs_locs_stty M' (val_locs vf))  (st_locs M')),
    psub (val_locs vf) (st_locs M') ->
    psub (plift q1) p ->
    psub (pand (vars_trans G (pand p qf)) (vars_trans G (pand p qx))) (plift q1) ->
    psub (pand (locs_locs_stty M'' (val_locs vf)) (locs_locs_stty M'' (val_locs vx))) (locs_locs_stty M'' (vars_locs H (plift q1))).
Proof. 
  intros. intros ? [? ?]. 
  remember WFE as WFE1. clear HeqWFE1.
  eapply envt_store_extend in WFE; eauto.
  eapply envt_store_extend in WFE; eauto.  
  destruct WFE as [? [? [? SEP]]].

  destruct (HQF x) as [Hf_q | Hf_fr].
  erewrite lls_change. eauto.
  eapply stchain_tighten. eauto. (* could also get from HQF, E *)
  eapply lls_closed'. eauto. eauto. 

  - destruct (HQX x) as [Hx_q | Hx_fr]. eauto.
    + assert ((pand (locs_locs_stty M'' (vars_locs H (pand p qf)))
                 (locs_locs_stty M'' (vars_locs H (pand p qx)))) x).
      erewrite lls_change in Hf_q. 2: { 
      eapply stchain_tighten. eauto.
      eapply env_type_store_deep_wf. eapply envt_store_extend. eauto. eauto.
      unfoldq. intuition. }

      split; eauto.
      eapply SEP in H8.
      eapply lls_mono. eapply vars_locs_monotonic. 2: eauto.
      unfoldq. intuition.
      unfoldq. intuition.
      unfoldq. intuition.
      unfoldq. intuition. 
    + destruct frx. 2: contradiction.
      eapply env_type_store_deep_wf in Hf_q.
      2: { eapply envt_store_extend; eauto. } 2: { unfoldq. intuition. }
      assert False. eapply Hx_fr. eauto. contradiction.
  - destruct frf. 2: contradiction.
    destruct (HQX x) as [Hx_q | Hx_fr]. eauto.
    + erewrite <-lls_change in Hx_q.
      2: { eapply stchain_chain''. 2: eauto. eapply stchain_tighten. eauto.
           eapply env_type_store_deep_wf. eauto. unfoldq. intuition.
           intros ? ?. eapply env_type_store_deep_wf in H8. eapply CH1. eauto.
           eauto. unfoldq. intuition. }
      eapply env_type_store_deep_wf in Hx_q.
      2: { eauto. }
      2: { unfoldq. intuition. }
      assert False. eapply Hf_fr. eauto. contradiction.
    + destruct frx. 2: contradiction. simpl in *.
      assert False. eapply Hx_fr. eapply A. erewrite lls_change; eauto. eapply stchain_tighten; eauto.
      contradiction. 
Qed.

Lemma lls_indexr_closed: forall S M a x1 vt qt,
    store_type S (a::M) ->
    indexr x1 (a::M) = Some (vt, qt) ->
    psub (plift qt) (st_locs M).
Proof.
  intros. destruct H as (STL & STT).
  intros ? ?.
  assert (x1 < length (a::M)). eapply indexr_var_some'. eauto.
  destruct (STT x1) as (vt' & qt' & v1 & ? & ? & ? & ? & ? ).
  eapply lt_stlocs; eauto.
  rewrite H0 in H2. inversion H2. subst vt' qt'.
  eapply lt_stlocs. eauto. simpl in *. lia. 
Qed.

Lemma lls_indexr_closed': forall S M x1 vt qt,
    store_type S M ->
    indexr x1 M = Some (vt, qt) ->
    psub (plift qt) (pnat x1).
Proof.
  intros. destruct H as (STL & STT).
  intros ? ?.
  assert (x1 < length M). eapply indexr_var_some'. eauto.
  destruct (STT x1) as (vt' & qt' & v1 & ? & ? & ? & ? & ?).
  unfold st_locs, pdom. eauto.
  rewrite H0 in H2. inversion H2. subst vt' qt'.
  eapply H6. eauto. 
Qed.

Lemma lls_indexr_closed'': forall M S vt qt x1,
    store_type S M ->
    indexr x1 M = Some (vt, qt) ->
    psub (locs_locs_stty M (plift qt)) (pnat x1).
Proof.
  intros. intros ? ?.
  remember (plift qt) as qt'.
  generalize dependent qt.
  generalize dependent x1.
  generalize dependent vt.
  

  induction H1; intros; subst.
  - eapply lls_indexr_closed'; eauto. 
  - eapply IHlocs_locs_stty in H1; eauto. 
    destruct H. destruct (H4 x0) as (? & ? & ? & ? & ? & ? & ? & ?). { eapply indexr_var_some' in H3. unfold st_locs. unfoldq. lia. }
    rewrite H3 in H5. inversion H5. subst.
    eapply H9 in H0. 
    unfoldq. lia. 
Qed.

Lemma lls_indexr_closed''': forall M S vt qt x1,
    store_type S M ->
    indexr x1 M = Some (vt, qt) ->
    psub (locs_locs_stty M (plift qt)) (st_locs M).
Proof.
  intros. intros ? ?.
  eapply lt_stlocs. eapply lls_indexr_closed''; eauto. eapply indexr_var_some' in H0. lia. 
Qed.

Lemma lls_shrink': forall S M a q1 x,
    store_type S M ->
    locs_locs_stty (a::M) q1 x ->
    psub q1 (st_locs M) ->
    locs_locs_stty M q1 x.
Proof.
  intros. remember (a::M) as M0.
  generalize dependent H1. generalize dependent H.
  induction H0; intros; subst.
  - eapply lls_z. eauto.
  - assert (x1 < length M). eapply H3 in H. unfold st_locs in *. unfoldq. lia.
    rewrite indexr_skip in H0; intuition. 
    assert (psub (plift qt) (pnat x1)). eapply lls_indexr_closed'; eauto. 
    eapply lls_s; eauto. eapply H6. intros ? ?. eapply H5 in H7. unfold st_locs in *. unfoldq. intuition. 
Qed.

Lemma lls_shrink: forall S M v a q1 x,
    store_type (v::S) (a::M) ->
    locs_locs_stty (a::M) q1 x ->
    psub q1 (st_locs M) ->
    locs_locs_stty M q1 x.
Proof.
  intros. remember (a::M) as M0.
  generalize dependent H1. generalize dependent H.
  induction H0; intros; subst.
  - eapply lls_z. eauto.
  - assert (x1 < length M). eapply H3 in H. unfold st_locs in *. unfoldq. lia.
    rewrite indexr_skip in H0; intuition. 
    assert (psub (plift qt) (pnat x1)). eapply lls_indexr_closed'; eauto.
    rewrite indexr_skip. eauto. lia. 
    eapply lls_s; eauto. eapply H6. intros ? ?. eapply H5 in H7. unfold st_locs in *. unfoldq. intuition. 
Qed.

Lemma lls_extend: forall S M a v q1 x,
    store_type (v::S) (a::M) ->
    locs_locs_stty M q1 x ->
    locs_locs_stty (a::M) q1 x.    
Proof.
  intros. remember (a::M) as M1.
  generalize dependent H.
  induction H0; intros; subst.
  - eapply lls_z. eauto.
  - eapply indexr_extend1 in H0. 
    eapply lls_s. eauto. eapply H0. 
    eapply IHlocs_locs_stty. eauto. eauto. 
Qed.

Lemma lls_empty: forall M, 
  locs_locs_stty M pempty = pempty.
Proof.
  intros. eapply functional_extensionality;
  intros; eapply propositional_extensionality; split.
  intros. inversion H. auto. unfold pempty in H0. contradiction.
  intros. unfold pempty in H. contradiction.
Qed.

Lemma storet_shrink: forall M S v a,
    store_type (v::S) (a::M) ->
    store_type S M.
Proof.
  intros. destruct H as (STL & STT).
  assert (length M = length S) as STL1. simpl in STL. lia. 
  split. 
  - eauto.
  - intros. unfold st_locs in *. 
    destruct (STT l) as (vt & qt & v1 & ? & ? & ? & ? & ?).
    unfoldq. simpl. lia.
    exists vt, qt, v1.
    split. 2: split. 3: split. 4: split. 
    + rewrite indexr_skip in H0. eauto. unfoldq. lia.  
    + rewrite indexr_skip in H1. eauto. unfoldq. lia. 
    + eauto.
    + intros ? ?. eapply lls_shrink.
      split. eauto. eapply STT.
      eapply H3. eauto. eapply lls_extend; eauto.
      split. eauto. eapply STT.

      intros ? ?. eapply lt_stlocs. eauto.
      eapply indexr_var_some' in H0. simpl in H0. lia. 
    + eauto. 
Qed.



Lemma plift_lls_z: forall M q x,
    plift q x ->
    plift (locs_locs_stty_fix M q) x.
Proof.
  intros M. induction M; intros.
  - simpl. eauto.
  - simpl. destruct a. rewrite plift_if1, plift_or.
    destruct (q (length M)). left. eauto. eauto. 
Qed.

Lemma lls_fix_shrink: forall M' M q x,
    psub (plift q) (st_locs M) ->
    locs_locs_stty_fix (M'++M) q x = locs_locs_stty_fix M q x.
Proof.
  intros M'. induction M'; intros.
  - simpl. eauto. 
  - simpl. destruct a. 
    remember (q (length (M' ++ M))). destruct b.
    symmetry in Heqb. eapply H in Heqb.
    unfold st_locs in *. rewrite app_length in *. unfoldq. lia. 
    eauto. 
Qed.

Lemma lls_fix_shrink1: forall M a q,
    psub (plift q) (st_locs M) ->
    locs_locs_stty_fix (a::M) q = locs_locs_stty_fix M q.
Proof.
  intros. eapply functional_extensionality. intros. 
  replace (a::M) with ([a]++M). eapply lls_fix_shrink. eauto. eauto. 
Qed.

Lemma plift_lls_s: forall M q x x1 vt qt,
    plift q x1 ->
    indexr x1 M = Some (vt, qt) ->
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
    + simpl. destruct a. rewrite plift_if1, plift_or.
      rewrite indexr_skip in H0; eauto.
      rewrite lls_fix_shrink1 in H2.
      2: { rewrite indexr_extend1 in H0. unfold st_locs in *. unfoldq. intuition. eapply H1 in H0. lia. }
      eapply IHM in H0; eauto.
      remember (q (length M)). destruct b. left. eauto. eauto.
  Unshelve.
  apply (fun v => False,  qempty).
Qed.

Lemma plift_lls: forall S M q,
    store_type S M -> 
    plift (locs_locs_stty_fix M q) = locs_locs_stty M (plift q).
Proof.
  intros. eapply functional_extensionality.
  intros. eapply propositional_extensionality.
  split.
  - (* ql -> pl *)
    intros. generalize dependent q. generalize dependent S. induction M.
    + intros. eapply lls_z. eauto.
    + intros. destruct S. inversion H. inversion H1. 
      destruct a. simpl in H0.
      remember (q (length M)) as b1.
      assert (store_type S M). eapply storet_shrink. eauto.
      destruct b1.
      * rewrite plift_or in H0. destruct H0.
        -- eapply IHM in H0; eauto. destruct H0. eapply lls_z. eauto.
           eapply lls_s. eauto. eapply indexr_extend1 in H2. eapply H2.
           eapply lls_extend. eauto. eauto. 
        -- eapply lls_s. symmetry. eauto. eapply indexr_head.
           eapply lls_extend. eauto. eauto.
      * eapply lls_extend. eauto. eauto.
  - (* pl -> ql *)
    intros.
    remember (plift q) as q'.
    generalize dependent q. induction H0.
    + intros. eapply plift_lls_z. subst. eauto.
    + intros. eapply plift_lls_s. subst. eauto. eauto.
      eapply lls_indexr_closed'; eauto. eauto. 
Qed.

Lemma val_locs_stty_decide: forall S M q l,
    store_type S M -> 
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

                                                          

(* ---------- main lemmas ---------- *)

Lemma sem_true: forall G p,
    sem_type G ttrue TBool p false pempty.
Proof.
  intros. intros S M H WFE ST.
  exists S, M, (vbool true). 
  split. 2: split. 3: split. 4: split. 5: split. 
  - exists 1. intros. destruct n. lia. simpl. intuition.
  - eapply stchain_refl. 
  - eauto.
  - intros ? ?. intuition.
  - simpl. eauto. 
  - eapply valq_bool.
Qed.
  
Lemma sem_false: forall G p,
    sem_type G tfalse TBool p false pempty.
Proof.
  intros. intros S M H WFE ST.
  exists S, M, (vbool false).
  split. 2: split. 3: split. 4: split. 5: split.
  - exists 1. intros. destruct n. lia. simpl. intuition.
  - eapply stchain_refl. 
  - eauto.
  - intros ? ?. intuition.
  - simpl. eauto. 
  - eapply valq_bool.
Qed.
  
Lemma sem_var: forall x G T (p:pl) fr q,
    indexr x G = Some (T, fr, q) ->
    p x ->
    sem_type G (tvar x) T p false (pone x).
Proof.
  intros. intros ? ? ? WFE ST.
  destruct WFE as [? [? [WFE ?]]].
  destruct (WFE x T fr q H) as [vx [HQ [HI [VT ?]]]]. 
  exists S, M, vx.
  split. 2: split. 3: split. 4: split. 5: split.
  - exists 1. intros. destruct n. lia. simpl. rewrite HI. reflexivity.
  - eapply stchain_refl. 
  - eauto.
  - intros ? ?. intuition.
  - eauto.
  - (* valq *)
    left. eapply lls_mono. 2: eauto. intros ? ?.
    exists x. unfoldq. intuition. exists vx. intuition. 
Qed.


Lemma storet_extend: forall S M S1 M1 E G T p q vx vt qt
    (ST:  store_type S M)
    (ST1: store_type S1 M1)
    (WFE: env_type M E G p)
    (QP:  psub (plift q) p)
    (SC1: st_chain M M1 (st_locs M))
    (SC2: st_chain M1 (st_extend M1 vt qt) (st_locs M1))
    (HVX: val_type M1 E vx T)
    (HQX: val_qual M M1 E vx p false (plift q))
    (QT:  qt = vars_locs_fix E q)
    (VT:  vt = (fun v : vl => val_type M1 E v T)),
    store_type (vx :: S1) (st_extend M1 vt qt).
Proof.
  intros.
  remember ST1 as ST1'. destruct ST1' as (STL & STT). clear HeqST1'.
  split.
  - simpl. lia.
  - intros l SL. unfold st_extend in *.
    bdestruct (l =? length M1).
    + subst l. 
      assert (psub (vars_locs E (plift q)) (st_locs M1)). {
        eapply env_type_store_wf. eapply envt_store_extend. eauto. eauto. eauto. }
      
      exists vt, qt, vx.
      split. 2: split. 3: split. 4: split. 
      * rewrite indexr_head. eauto.
      * rewrite STL, indexr_head. intuition.
      * subst vt. eauto.
      * intros. intros ? ?.
        eapply lls_shrink' in H0. 2: eauto. 2: eapply valt_wf; eauto.
        destruct (HQX x) as [H_q | H_fr]. eauto.
        (* q *) subst qt. rewrite <-plift_vars_locs. erewrite <-lls_change. eapply lls_mono. 2: eauto. eapply vars_locs_monotonic. unfoldq. intuition. eapply stchain_tighten. eauto.
        eapply env_type_store_deep_wf. eapply envt_store_extend. eauto. eauto. eauto.
        (* fr *) destruct H_fr.
      * subst qt. rewrite <-plift_vars_locs. intros ? ?. eapply env_type_store_wf. eapply envt_store_extend. eauto. eauto. eauto. eauto. 
    + destruct (STT l) as (vt1 & qt1 & v1 & IXM & IXS & VT1 & VL1 & VL2).
      unfold st_locs in *. unfoldq. simpl in SL. lia. 
      exists vt1, qt1, v1.
      split. 2: split. 3: split. 4: split. 
      * rewrite indexr_skip. eauto. lia.
      * rewrite indexr_skip. eauto. lia. 
      * intuition.
      * intros ? ?.
        erewrite <-lls_change in H0. eauto. eapply VL1 in H0; eauto. 
        erewrite <-lls_change. eapply H0; eauto.
        eapply stchain_tighten; eauto. eapply lls_indexr_closed'''; eauto.
        eapply stchain_tighten; eauto. intros ? ?.
        eapply VL1 in H1; eauto. eapply lls_indexr_closed'''; eauto. 
      * eauto. 
Qed.

Lemma sem_ref: forall t G T p q,
    sem_type G t T p false (plift q) ->
    psub (plift q) p ->
    sem_type G (tref t) (TRef T false q) p true (plift q).
Proof.
  intros. intros ? ? ? WFE ST. 
  destruct (H S M E WFE ST) as [S1 [M1 [vx [IW1 [SC1 [ST1 [SE1 [HVX HQX]]]]]]]].
  remember (length S1) as x.
  remember (vars_locs_fix E q) as qt.
  remember (fun v => val_type M1 E v T) as vt.
  assert (st_chain M1 (st_extend M1 vt qt) (st_locs M1)). {
    split. 2: split.
    unfoldq. intuition.
    unfoldq. intuition. 
    unfold st_locs, st_extend in *. unfoldq. simpl. intuition.
    intros. unfold st_locs, st_extend in *. rewrite indexr_skip. eauto. unfoldq. lia. }

  exists (vx::S1).
  exists (st_extend M1 vt qt ).
  exists (vref x). split. 2: split. 3: split. 4: split. 5: split. 
  + (* expression evaluates *)
    destruct IW1 as [n1 IW1]. rename S into St.
    exists (S n1).
    intros. destruct n. lia.
    subst x. simpl. rewrite IW1. eauto. lia.
  + (* stty chain *)
    eapply stchain_chain''. eauto. 2: eapply SC1. eauto.
  + (* store typing *)
    eapply storet_extend. eapply ST. all: eauto.
  + eapply se_trans. eauto. intros ? ?. intros. eapply indexr_extend1 in H3. eapply H3. 
  + (* result well typed *)
    remember (st_extend M1 vt qt) as M2.
    assert (store_type (vx::S1) (M2)) as ST2. {
      subst M2. eapply storet_extend. eapply ST. all: eauto. 
    }
    remember ST1 as ST1'.
    destruct ST1' as (STL & STT). clear HeqST1'.
    assert (psub (plift qt) (st_locs M1)) as KM1. {
      subst qt. rewrite <-plift_vars_locs. eapply env_type_store_wf; eauto.
      eapply envt_store_extend; eauto.
    }
    split. 2: split. 3: split. 4: split.
    * eapply valt_closed. eauto.
    * auto.
    * intros ? ?. eapply H0 in H2. eapply WFE. eauto. 
    * intros ? ?. rewrite val_locs_ref in H2. inversion H2.
      subst M0 q0 x1.
      subst M2. unfold st_locs, st_extend. unfoldq. simpl. lia.
      subst M0 q0 x1.
      unfold pone in H3. subst x x2.
      subst M2. unfold st_extend in *. rewrite <-STL in H4.
      rewrite indexr_head in H4. inversion H4. subst vt0  qt0.
      eapply lls_shrink in H5; eauto.
      eapply lls_closed' in H5; eauto. unfold st_locs in *. unfoldq. simpl. lia. 

    * exists vt, qt.
      split. 2: split. 3: split. 
      -- subst x M2. rewrite <-STL. unfold st_extend. rewrite indexr_head. eauto.
      -- intros M3. intros.
         clear STT.
         remember (plift qt) as qt'.
         
         assert (locs_locs_stty M3 qt' = locs_locs_stty M2 qt'). {
           erewrite <-lls_change. eauto. eauto. 
         }
         assert (locs_locs_stty M2 qt' = locs_locs_stty M1 qt'). {
           erewrite <-lls_change. eauto. eapply stchain_tighten.
           eauto. subst qt' qt. rewrite <-plift_vars_locs. eapply env_type_store_deep_wf.
           eapply envt_store_extend. eauto. eauto. eauto. 
         }

         assert (st_chain M1 M3 (locs_locs_stty M1 qt')). {
           eapply stchain_chain'. eauto. 
           eapply stchain_tighten. eauto.
           rewrite H5. intros ? ?. eauto.
           subst qt' qt. rewrite <-plift_vars_locs. eapply env_type_store_deep_wf.
           eapply envt_store_extend. eauto. eauto. eauto.
         }

         assert (st_chain M1 M3 (locs_locs_stty M3 qt')). {
           rewrite H4, H5. eauto.
         }

         assert (st_chain M3 M1 (locs_locs_stty M3 qt')). {
           destruct H7. destruct H8. 
           split. 2: split.
           eauto. eauto. symmetry. eauto. 
         }
         assert (st_chain M3 M1 (locs_locs_stty M3 (val_locs v))). {
           eapply stchain_tighten. eauto. eauto. 
         }
         
         assert (psub (locs_locs_stty M3 (val_locs v)) (locs_locs_stty M1 qt')). {
           rewrite <-H5, <-H4. eauto. 
         }
         
         assert (st_chain M3 M1 (locs_locs_stty M1 (val_locs v))). {
           erewrite <-lls_change. eauto. eauto.
         }

         assert (st_chain M1 M3 (locs_locs_stty M1 (val_locs v))). {
           destruct H11. destruct H12.
           split. 2: split.
           eauto. eauto. symmetry. eauto. 
         }
         
         subst vt. split; intros.
         eapply valt_store_change. eauto. eauto.
         eapply valt_store_change. eauto. eauto. 
      -- subst qt. rewrite plift_vars_locs. auto.
      -- intros ? ?. subst x M2. eapply lls_s. unfoldq. eauto. 
         unfold st_extend. eapply indexr_head. eauto.
  + (* qualifier *)  
    intros ? ?. inversion H2.
    * right. simpl. subst x1 q0 M0. rewrite val_locs_ref in H3.
      unfold pone in H3. subst x x0. unfold pstdiff, st_locs, st_extend. unfoldq.
      simpl. destruct ST1. destruct SC1 as (? & ? & ?). unfoldq. unfold st_locs in *.  intros ?. assert (length M <= length M1). unfoldq. 
      destruct (length M). lia. 
      specialize (H6 n). lia. lia.
    * left. simpl. subst x1 q0 M0. rewrite val_locs_ref in H3.
      unfold pone in H3. subst x x2. unfold st_extend in *.
      destruct ST1. rewrite <-H3, indexr_head in H4. inversion H4.
      subst qt0 vt0. subst qt. 
      eapply lls_mono. 2: eapply H5. rewrite <-plift_vars_locs. eapply vars_locs_monotonic.
      unfoldq. intuition. 
Qed.


Lemma sem_get1: forall t env T p q1 fr q,
    sem_type env t (TRef T false q1) p fr q ->
    psub (plift q1) p ->
    sem_type env (tget t) T p false (plift q1).
Proof.
  intros. intros ? ? ? WFE ST.
  destruct (H S M E WFE ST) as [S1 [M1 [vx [IW1 [SC1 [ST1 [SE1 [HVX HQX]]]]]]]]. 
  destruct vx; try solve [inversion HVX]. simpl in HVX.
  destruct HVX as (? & ? & ? & HVX' & HVX).
  eapply ST1 in HVX' as HVX''. 2: { left. rewrite val_locs_ref. unfoldq; intuition. }
  destruct HVX as [vt [qt [IXM [VTM [VTQ VTQ' ]]]]].
  destruct HVX'' as [vt' [qt' [v [IXM' [IXS [VTS [VLS VLS']]]]]]].
  rewrite IXM in IXM'.
  inversion IXM'. clear IXM'. subst vt'  qt'. 
  exists S1, M1, v. split. 2: split. 3: split. 4: split. 5: split.
  + (* expression evaluates *)
    destruct IW1 as [n1 IW1]. rename S into St.
    exists (S n1).
    intros. destruct n. lia.
    simpl. rewrite IW1. rewrite IXS. eauto. lia.
  + (* st chain *)
    eauto. 
  + (* store type *)
    eauto.
  + auto. 
  + (* result well typed *)
    eapply valt_store_extend. eapply VTM. 2: eapply VLS. 2: eauto. 2: eauto.
    eapply stchain_tighten. eapply stchain_refl.
    
    rewrite VTQ. eapply env_type_store_deep_wf. eapply envt_store_extend; eauto. auto.
    intros ? ?. eapply VLS in H4. rewrite VTQ in H4. eapply env_type_store_deep_wf. 3: eapply H4. eapply envt_store_extend; eauto. auto.
    eapply stchain_refl. 
  + (* qualifier *)
    intros ? ?. left. eapply VLS in H4; eauto. 
    rewrite VTQ in H4. eapply lls_mono. 2: eauto. eapply vars_locs_monotonic. unfoldq. intuition. 
Qed.

Lemma sem_get2: forall t env T p rf1 q1 fr q,
    sem_type env t (TRef T rf1 q1) p fr q ->
    sem_type env (tget t) T p fr q.
Proof.
  intros. intros ? ? ? WFE ST.
  destruct (H S M E WFE ST) as [S1 [M1 [vx [IW1 [SC1 [ST1 [SE1 [HVX HQX]]]]]]]]. 
  destruct vx; try solve [inversion HVX]. simpl in HVX.
  destruct HVX as (? & ? & ? & HVX' & HVX).
  eapply ST1 in HVX' as HVX''. 2: { left. rewrite val_locs_ref. unfoldq; intuition. }
  destruct HVX as [vt [qt [IXM [VTM [VTQ VTQ' ]]]]].
  destruct HVX'' as [vt' [qt' [v [IXM' [IXS [VTS [VLS VLS']]]]]]].
  rewrite IXM in IXM'.
  inversion IXM'. clear IXM'. subst vt' qt'. 
  exists S1, M1, v. split. 2: split. 3: split. 4: split. 5: split.
  + (* expression evaluates *)
    destruct IW1 as [n1 IW1]. rename S into St.
    exists (S n1).
    intros. destruct n. lia.
    simpl. rewrite IW1. rewrite IXS. eauto. lia.
  + (* st chain *)
    eauto. 
  + (* store type *)
    eauto.
  + auto. 
  + (* result well typed *)
    eapply valt_store_extend. eapply VTM. 2: eapply VLS. 2: eauto. 2: eauto.
    eapply stchain_tighten. eapply stchain_refl.
    
    intros ? ?. eapply VTQ' in H3. inversion H3; subst. unfold pone in H4. subst x.
    eapply indexr_var_some' in IXS. unfold st_locs. destruct ST1 as [L ?]. rewrite <- L in IXS. unfoldq; intuition.
    unfold pone in H4. subst x1. eapply lls_closed' in H3; eauto. apply indexr_var_some' in H5. unfoldq; intuition.
    subst x0. unfold st_locs. unfoldq; intuition. 

    intros ? ?. eapply VLS in H3. eapply VTQ' in H3. inversion H3; subst. unfold pone in H4. subst x.
    eapply indexr_var_some' in IXS. unfold st_locs. destruct ST1 as [L ?]. rewrite <- L in IXS. unfoldq; intuition.
    unfold pone in H4. subst x1. eapply lls_closed' in H3; eauto. apply indexr_var_some' in H5. unfoldq; intuition.
    subst x0. unfold st_locs. unfoldq; intuition. 
    eapply stchain_refl. 
  + (* qualifier *)
    intros ? ?. eapply HQX. rewrite val_locs_ref.
    eapply lls_s. unfold pone. intuition. eauto. eapply VLS. eauto. 
Qed.

Lemma sem_get: forall t env T p q1 rf1 fr q,
    sem_type env t (TRef T rf1 q1) p fr q ->
    psub (plift q1) p ->
    sem_type env (tget t) T p (if rf1 then fr else false) (por (plift q1) (pif rf1 q)).
Proof.
  intros. intros ? ? ? WFE ST.
  destruct (H S M E WFE ST) as [S1 [M1 [vx [IW1 [SC1 [ST1 [SE1 [HVX HQX]]]]]]]]. 
  destruct vx; try solve [inversion HVX]. simpl in HVX.
  destruct HVX as (? & ? & ? & HVX' & HVX).
  eapply ST1 in HVX' as HVX''. 2: { left. rewrite val_locs_ref; eauto. unfoldq; intuition. }
  destruct HVX as [vt [qt [IXM [VTM [VTQ VTQ' ]]]]].
  destruct HVX'' as [vt' [qt' [v [IXM' [IXS [VTS [VLS VLS1]]]]]]].
  rewrite IXM in IXM'.
  inversion IXM'. clear IXM'. subst vt' qt'. 
  exists S1, M1, v. split. 2: split. 3: split. 4: split. 5: split.
  + (* expression evaluates *)
    destruct IW1 as [n1 IW1]. rename S into St.
    exists (S n1).
    intros. destruct n. lia.
    simpl. rewrite IW1. rewrite IXS. eauto. lia.
  + (* st chain *)
    eauto. 
  + (* store type *)
    eauto.
  + auto. 
  + (* result well typed *)
    eapply valt_store_extend. eapply VTM. 2: eapply VLS. 2: eauto. 2: eauto.
    eapply stchain_tighten. eapply stchain_refl.
    
    intros ? ?. eapply VTQ' in H4. inversion H4; subst. unfold pone in H5. subst x.
    eapply indexr_var_some' in IXS. unfold st_locs. destruct ST1 as [L ?]. rewrite <- L in IXS. unfoldq; intuition.
    unfold pone in H5. subst x1. eapply lls_closed' in H4; eauto. apply indexr_var_some' in H6. unfoldq; intuition.
    subst x0. unfold st_locs. unfoldq; intuition. 

    intros ? ?. eapply VLS in H4. eapply VTQ' in H4. inversion H4; subst. unfold pone in H5. subst x.
    eapply indexr_var_some' in IXS. unfold st_locs. destruct ST1 as [L ?]. rewrite <- L in IXS. unfoldq; intuition.
    unfold pone in H5. subst x1. eapply lls_closed' in H4; eauto. apply indexr_var_some' in H6. unfoldq; intuition.
    subst x0. unfold st_locs. unfoldq; intuition. 
    eapply stchain_refl. 
  + (* qualifier *)
    destruct rf1. 
    * assert (val_qual M M1 E v p fr q). {
        intros ? ?. eapply HQX. rewrite val_locs_ref.
        eapply lls_s. unfold pone. intuition. eauto. eapply VLS. eauto.  }
      intros ? ?. destruct (H4 x). (* valq_sub, but don't have q < E *)
      -- eauto.
      -- left. eapply lls_mono. 2: eauto. eapply vars_locs_monotonic. unfoldq. intuition.
      -- right. eauto. 
    * assert (val_qual M M1 E v p false (plift q1)). {
        intros ? ?. left. eapply VLS in H4; eauto. 
        rewrite VTQ in H4. eapply lls_mono. 2: eauto. eapply vars_locs_monotonic. unfoldq. intuition. 
         }
      replace false with (false || false).
      eapply valq_sub. eauto. unfoldq. intuition. unfoldq. intuition. 
Qed.


Lemma sem_put: forall t1 t2 env T p fr1 q1 rf2 q2,
    sem_type env t1 (TRef T rf2 q2) p fr1 q1 ->
    sem_type env t2 T p false (plift q2) ->
    psub (plift q2) p -> 
    sem_type env (tput t1 t2) TBool p false pempty.
Proof.
  intros. intros ? ? ? WFE ST.
  destruct (H S M E WFE ST) as [S1 [M1 [vr [IW1 [SC1 [ST1 [SE1 [HVR HQR]]]]]]]]. 
  eapply envt_store_extend in WFE as WFE1. 2: eapply SC1.
  destruct (H0 S1 M1 E WFE1 ST1) as [S2 [M2 [vx [IW2 [SC2 [ST2 [SE2 [HVX HQX]]]]]]]]. 
  destruct vr; try solve [inversion HVR]. simpl in HVR.
  destruct HVR as (? & ? & ? & ? & vt & qt & ? & ? & ? & ?).
  remember H8 as VQT1.
  remember H9 as VQT.
  destruct ST2 as (? & ST2).
  destruct (ST2 i) as (vt' & qt' & vz & ? & ? & ? & ? & ?). eapply SC2. eapply indexr_var_some' in H6. unfoldq; intuition.
  assert (indexr i M2 = indexr i M1) as R. { symmetry. eapply SC2. eapply indexr_var_some' in H6. unfoldq; intuition. }
  rewrite R in H11. rewrite H11 in H6. inversion H6. subst vt' qt'.
  rename H12 into SI.
  exists (update S2 i vx), M2, (vbool true).
  split. 2: split. 3: split. 4: split. 5: split.
  + (* expression evaluates *)
    rename S into St.
    destruct IW1 as [n1 IW1].
    destruct IW2 as [n2 IW2].
    exists (S (n1+n2)).
    intros. destruct n. lia.
    simpl. rewrite IW1. rewrite IW2. rewrite SI. eauto. lia. lia.
  + eapply stchain_chain''; eauto. eapply SC1. 
  + (* store type *)
    split. rewrite <-update_length. eauto. 
    intros. bdestruct (i =? l).
    * exists vt, qt, vx. subst i. 
      split. 2: split. 3: split. 4: split. 
      -- rewrite R. eapply H11.
      -- rewrite update_indexr_hit. eauto. eapply indexr_var_some'. eauto.
      -- unfold val_qual in HQX.
        
         eapply H7. eapply stchain_tighten. eauto.
         eapply lls_indexr_closed'''; eauto. 

         intros ? ?. eapply HQX in H16. destruct H16. 2: contradiction.
         rewrite VQT1.
         eapply lls_mono; eauto. eapply vars_locs_monotonic. unfoldq. intuition.
         intuition.
      -- intros. intros ? ?. eapply HQX in H16. destruct H16. 2: contradiction.
         rewrite VQT1.
         eapply lls_mono. 2: eauto.
         eapply vars_locs_monotonic. 
         unfoldq. intuition. 
      -- eauto.
    * rewrite update_indexr_miss. 2: eauto.
      eapply ST2. eauto.
  + (* store preservation *)
    assert (length S = length M). destruct ST.  eauto.
    intros ? ?. intros.
    bdestruct (i =? l). { subst.
    destruct (HQR l).
      left. rewrite val_locs_ref. unfoldq; intuition.
      destruct H16.  simpl. 
      erewrite lls_change with (q := (vars_locs E p )). eapply lls_mono; eauto.
      eapply vars_locs_monotonic. intros ? ?. unfoldq; intuition. 
      eapply stchain_tighten; eauto.  eapply env_type_store_deep_wf; eauto.
      intros ? ?. unfoldq; intuition. 
      destruct fr1. simpl in *. unfold pstdiff, pdiff in H3. apply indexr_var_some' in H17.
      unfold st_locs in H3. unfoldq; intuition.
      simpl in H13. contradiction. 
    }{ rewrite update_indexr_miss.
       assert (locs_locs_stty M (vars_locs E p) l = locs_locs_stty  M1 (vars_locs E p) l) as LLS1. {
         erewrite lls_change; eauto. 
         eapply stchain_tighten; eauto. eapply env_type_store_deep_wf; eauto. intros ? ?. unfoldq; intuition.
      }
      unfold store_effect in *.
      eapply SE1 in H17 as A; eauto. 
      2: {
        auto.
      }
      eapply SE2 in A  as B; eauto.
      intros ?. eapply H16. erewrite <- lls_change in H19.
      eapply lls_mono with (q := (vars_locs E p)); eauto. eapply vars_locs_monotonic. intros ? ?. unfoldq; intuition.
      eapply stchain_tighten; eauto. eapply env_type_store_deep_wf; eauto. unfoldq; intuition. 
     }
    
  + (* result well typed *)
    constructor. 

  + (* qualifier *)
    eapply valq_bool.
Qed.


Lemma sem_abs: forall env t T1 T2 p fn1 fr1 q1 fn2 ar2 fr2 q2 qf,
    sem_type ((T1, fr1, (qand p (qor q1 (qif fn1 qf))))::env) t T2 
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
    sem_type env (tabs (qand p qf) t) (TFun T1 fn1 fr1 q1 T2 fn2 ar2 fr2 q2) (plift p) false (plift qf).
Proof.
  intros. intros ? ? ? WFE ST.
  exists S.
  exists M. (* (st_tighten M (val_max (vabs E (qand p qf) t))). *)
  exists (vabs E (qand p qf) t).
  split. 2: split. 3: split. 4: split. 5: split.
  + (* term evaluates *)
    exists 1. intros. destruct n. lia. simpl. eauto.
  + eapply stchain_refl. 
  + (* store typing *)
    eauto.
  + intros ? ?. intuition. 
  + (* result well typed *)
    simpl. 

    assert (length env = length E) as LE. { symmetry. eapply WFE. }
    assert (pdom env = pdom E) as DE. { unfold pdom. rewrite LE. eauto. }
    
    rewrite val_locs_abs. rewrite plift_and. rewrite LE in *. intuition; eauto.
    intros ? ?.  eapply env_type_store_deep_wf with (q := (pand (plift p)(plift qf))) in WFE as WFE'.
    eapply WFE' in H6; eauto. unfoldq; intuition.

    (* INDUCTION *)
    destruct (H S' M' (vx::E)) as [S2 [M2 [vy IHW1]]].
    
    (* ENV_TYPE*) {
    rewrite <-plift_and in H6. rewrite <-val_locs_abs with (t:=t) in H6.
    
    eapply envt_extend_full; eauto. unfoldq. intuition.

    rewrite plift_and, plift_or, plift_if. destruct fn1.
    unfoldq. intuition. eapply H0; eauto.  unfoldq. intuition. eapply H0; eauto.

    unfoldq. intuition.
    destruct (H9 x) as [F | [L | Q]]. eauto. {
      destruct fn1. 2: contradiction.
      rewrite plift_and, plift_or, plift_if.
      eapply lls_mono. 2: eapply F. intros ? F'.
      destruct F'. exists x1. unfoldq. intuition. 
    } {
      destruct fr1. 2: contradiction.
      destruct L. eauto.
    } {
      rewrite plift_and, plift_or, plift_if.
      eapply lls_mono. 2: eapply Q. intros ? Q'.
      destruct Q'. exists x1. unfoldq. intuition. eapply H0; eauto. 
    }

    intros. subst fr1. intros ? ?. eapply H9 in H10.
    destruct H10 as [ A | [B | C]]. {
      destruct fn1. 2: contradiction.
      simpl in A. eapply lls_mono. 2: eauto. eapply vars_locs_monotonic. 
      rewrite plift_and, plift_or. unfoldq. intuition.
    } {
      contradiction.
    } {
      eapply lls_mono. 2: eauto. eapply vars_locs_monotonic. 
      rewrite plift_and, plift_or. unfoldq. intuition. eapply H0; eauto.
    }

    assert (psub (plift (qand p (qor q1 (qif fn1 qf)))) (pdom E)).
    rewrite plift_and, plift_or, plift_if. unfoldq. intuition.
    destruct fn1; eapply H5; unfoldq. eapply H10. contradiction.

    intros ? ?. eapply H10. eapply H11. 

    eapply stchain_tighten. eapply H6. 
    rewrite val_locs_abs, plift_and. 
    intros ? ?. eauto.
    }

    eauto.
    
    destruct IHW1 as [? IHW1].
    exists S2, M2, vy. intuition.

    (* store preservation *)
    intros ? ? PV ?. eapply H12.
    intros ?. eapply PV. rewrite lls_vars_or in H17. 
    destruct H17. {
      left. replace (vx::E) with ([vx]++E) in H17. rewrite vars_locs_extend in H17. auto. unfoldq; intuition. auto.
    } {
      right. eapply lls_vars in H17. destruct H17 as [? [? ?]]. unfold pone in H17. subst x. eapply lls_var in H18.
      destruct H18 as [? [? ?]]. rewrite indexr_head in H17. inversion H17. subst x. auto.
    } 
    auto.  
    
    (* VAL_TYPE *)
    eapply valt_extend1; eauto.

    (* vy < vf \/ vx *)
    apply valt_wf in H8(*HVX*). apply valt_wf in H14(*HVY*).
    rename H16 into HVY.

    intros ? ?.
    destruct (HVY x) as [HY_q | HY_fr]. eauto.
    - (* q *)
      eapply lls_vars in HY_q. 
      destruct HY_q as (? & (? & ?) & ?).
      bdestruct (x0 =? length E).
      * (* from arg *)
        subst x0. eapply lls_mono in H18. 2: { intros ? ?. eapply var_locs_head. eauto. }
        right. right. left.
        destruct ar2. eauto. 
        destruct H17. { eapply H4 in H17. lia. }
        destruct H17. contradiction.
        destruct fn2. simpl in H17. rewrite plift_and in H17. destruct H17. eapply H5 in H19. lia.
        simpl in H17. contradiction.
      * (* from func *)
        assert (x0 < length (vx::E)). eapply lls_var in H18. destruct H18. rewrite indexr_extend1 in H18. eapply H18. simpl in H20.
        eapply lls_mono in H18. 2: { intros ? ?. eapply var_locs_shrink. eauto. lia. }
        destruct H16. 2: { contradiction. }
        destruct H17.         
        left. split. 
        eapply lls_mono. 2: eapply H18. intros ? ?. exists x0. intuition. 
        eapply lls_vars'. eapply H18. eauto.
        destruct H17. destruct ar2; contradiction. 
        destruct fn2. right. left. simpl. eapply lls_vars'. eapply H18. auto. 
        simpl in H17. contradiction.
      
    - (* fr *)
      right. right. right. destruct fr2; simpl in *. auto. auto.
        
  (* VAL_QUAL *)
  + eapply valq_abs.
Unshelve.
  apply (vbool true).
Qed.



Lemma valq_store_change: forall M M' M'' G H v p fr q,
    env_type M' H G p ->
    val_qual M M' H v p fr q ->
    psub (locs_locs_stty M' (val_locs v)) (st_locs M') ->
    st_chain M' M'' (st_locs M') ->
    val_qual M M'' H v p fr q.
Proof.
  intros. intros ? ?. 
  assert (locs_locs_stty M' (val_locs v) x). {
    erewrite lls_change. eauto.
    eapply stchain_tighten. eauto.
    intros ? ?. eapply H2 in H5. eauto.
  }
  destruct (H1 x H5). {
    left. erewrite <-lls_change. eauto.
    eapply stchain_tighten. eauto.
    eapply env_type_store_deep_wf. eauto. unfoldq. intuition. 
  } {
    right. destruct fr; try contradiction. 
    simpl in *. unfold pnot, st_locs in *. intuition.
  }
Qed.


Lemma sem_app: forall env f t T1 T2 p frf qf frx qx fn1 fr1 q1 fn2 ar2 fr2 q2,
    sem_type env f (TFun T1 fn1 fr1 q1 T2 fn2 ar2 fr2 q2) p frf (plift qf) ->  
    sem_type env t T1 p frx (plift qx)  ->
    (if fn1 then
       if fr1 then
         True
       else
         (frx = false /\ (exists x0, f = tvar x0 /\ psub (plift qx) (pone x0))) \/
         (frx = false /\ (exists p0 t, f = tabs p0 t /\ psub (plift qx) (plift p0))) \/
         (frx = false /\ psub (plift qx) (plift q1))
     else
       if fr1 then
         psub (pand 
                 (plift (vars_trans_fix env qf))
                 (plift (vars_trans_fix env qx)))
           (plift q1)
       else
         frx = false /\ psub (plift qx) (plift q1)) ->

    psub (plift q1) p ->   
    psub (plift q2) p ->   
    sem_type env (tapp f t) T2 p
      (fn2 && frf || ar2 && frx || fr2)
      (por (pif fn2 (plift qf)) (por (pif ar2 (plift qx)) (plift q2))).
Proof.
  intros. intros S0 ? ? WFE ST.
  rename H into IHW1. rename H0 into IHW2. 
  destruct (IHW1 S0 M E WFE ST) as [S1 [M1 [vf [IW1 [SC1 [ST1 [SE1 [HVF HQF]]]]]]]]. auto. auto.
  assert (env_type M1 E env p) as WFE1. { eapply envt_store_extend; eauto. }
  destruct (IHW2 S1 M1 E WFE1 ST1) as [S2 [M2 [vx [IW2 [SC2 [ST2 [SE2 [HVX HQX]]]]]]]]. 

  assert (telescope env). eapply envt_telescope. eauto.

  (* vf is a function value: it can eval its body *)
  destruct vf; try solve [inversion HVF]. 

  apply valt_wf in HVF as WFQF. apply valt_wf in HVX as WFQX.

  destruct HVF; intuition.
  rename H9 into HVF.
  destruct (HVF S2 M2 vx) as [S3 [M3 [vy [IW3 [SC3 [ST3 [SE3 HVY]]]]]]]; eauto. 

  eapply stchain_tighten. eauto. eauto. 
  
  (* SEPARATION / OVERLAP *)
  rename H1 into HSEP.
  intros ? ?.

  destruct fn1. { (* arg may overlap with function? *)
    destruct fr1. { (* arg may be fresh? *)
      (* fn, fr: anything goes *)
      edestruct val_locs_stty_decide. eauto. left. simpl. eauto. right. left. eauto.
    } {
      (* fn, not fr *) 
      destruct HSEP as [SEP | [SEP | SEP]]. { (* fn *)
        destruct SEP as (? & ? & ? & A). subst f frx.
        destruct IW1 as [? IW1]. assert (S x1 > x1) as P. lia. specialize (IW1 (S x1) P).
        simpl in IW1. inversion IW1.
        destruct (HQX x) as [Hq | Hfr]. eauto. 2: { unfoldq. intuition. }
        left. simpl. eapply lls_vars in Hq. destruct Hq as (? & (? & B) & ?).
        eapply lls_var in H12. destruct H12 as (? & ? & ?).
        eapply A in B. unfoldq. congruence. 
      } { (* fn 2, value *)
        destruct SEP as (? & ? & ? & ? & A). subst f frx.
        destruct IW1 as [? IW1]. assert (S x2 > x2) as P. lia. specialize (IW1 (S x2) P).
        simpl in IW1. inversion IW1. 
        destruct (HQX x) as [Hq | Hfr]. eauto. 2: { unfoldq. intuition. }
        subst. left. simpl. eapply lls_vars in Hq. destruct Hq as (? & (? & B) & ?).
        rewrite val_locs_abs. 
        eapply A in B. eapply lls_vars'. eauto. eauto. 
      } { (* q1 *)
        destruct SEP. subst frx.
        right. right. 
        eapply valq_sub with (q':=plift q1) (fr':=false) in HQX.
        destruct (HQX x) as [Hq | Hfr]. eauto. 2: contradiction.
        eapply lls_vars in Hq. destruct Hq as (? & ? & ?). eapply lls_vars'. eauto. unfoldq. intuition. 
        eauto. eauto.
      }
    }
  } {
    right. destruct fr1. {
      (* not fn, fr *) 
      edestruct val_locs_stty_decide. eauto. { (* check to see if we're aliasing function *)
        right. eapply overlapping. eapply ST1. eapply WFE. eauto. eauto. eauto. eauto. eauto. eauto.
        eauto.
        intros ? [? ?]. eapply HSEP. split.
        rewrite plift_vt. eapply vt_mono. 2: eapply H9. unfoldq. intuition. eauto.
        rewrite plift_vt. eapply vt_mono. 2: eapply H10. unfoldq. intuition. eauto.
        unfoldq. intuition eauto.
      }{ 
        left. eauto.
      }
    } {
      (* not fn, not fr *)
      right. destruct HSEP as [? HSEP]. subst frx.
      eapply valq_sub with (q':=plift q1) (fr':=false) in HQX.
      destruct (HQX x) as [Hq | Hfr]. eauto. 2: contradiction.
      eapply lls_vars in Hq. destruct Hq as (? & ? & ?). eapply lls_vars'. eauto. unfoldq. intuition. 
      eauto. eauto.
    }
  }

  (* EVALUATION *)
  exists S3, M3, vy. split. 2: split. 3: split. 4: split. 5: split.
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

  + eapply stchain_chain''. eapply stchain_chain''. eauto. eauto. eapply SC1. eauto. intros ? ?. eapply SC2. eapply SC1. eauto. 
    
  (* STORE_TYPE *)
  + eauto.
  
  + (* store preservation *)
    intros ? ? ? ?. rewrite SE3. eauto. 2: eauto.
    assert (l0 < length M). { eapply indexr_var_some' in H9. destruct ST as (L & ?). lia. }
    intros ?. eapply H8. destruct H11. {
    destruct (HQF l0). erewrite lls_change; eauto. eapply stchain_tighten; eauto. 
    erewrite lls_change. eapply lls_mono. 2: eapply H12. eapply vars_locs_monotonic; eauto. unfoldq; intuition.
    eapply stchain_tighten; eauto. eapply env_type_store_deep_wf; eauto. intros ? ?. auto.
    destruct frf. destruct H12. unfoldq; intuition. destruct H12.
  } {
    destruct (HQX l0). auto. erewrite lls_change. eapply lls_mono. 2: eapply H12. eapply vars_locs_monotonic; eauto. unfoldq; intuition.
    eapply stchain_tighten; eauto. eapply stchain_chain''; eauto. eapply SC1; eauto. eapply env_type_store_deep_wf; eauto. intros ? ?. auto.
    destruct frx; try contradiction. destruct H12. destruct SC1 as [A [B ?]]. eapply B in H10. unfoldq; intuition.
  }
  eapply SE2; eauto. erewrite <- lls_change; eauto. eapply stchain_tighten; eauto. eapply env_type_store_deep_wf; eauto. unfoldq; intuition.

  (* VAL_TYPE *)
  + eapply HVY.

  (* VAL_QUAL *)
  + destruct HVY as [HVY HQY].
    remember (vabs l q t0) as vf.
    assert (val_qual M M3 E vf p frf (plift qf)) as HQF'. {
      eapply valq_store_change. eauto. eauto. eauto. eapply stchain_chain''. eauto. eauto. eapply SC2.  }
    assert (val_qual M1 M3 E vx p frx (plift qx)) as HQX'. {
      eapply valq_store_change. eapply envt_store_extend; eauto. eauto.
      eapply valt_deep_wf. eauto. eauto. }
    
    intros ? ?. unfoldq.
    destruct (HQY x) as [HY_q | [HY_f | [HY_x | HY_fr]]].
    repeat rewrite app_length. intuition.
    * (* q2, and part of function *)
      destruct HY_q as [? ?].
      left. eapply lls_mono. eapply vars_locs_monotonic. 2: eauto.
      intros ? ?. intuition. 
    * (* part of function *)
      destruct fn2. 2: contradiction.
      destruct (HQF' x) as [HF_q | HF_fr]. eauto. 
      -- (* q *) left. eapply lls_mono. 2: eauto. eapply vars_locs_monotonic. unfoldq. intuition.
      -- (* fr *) 
         destruct frf. 2: contradiction.
         right. simpl. auto.
    * (* part of arg *)
      destruct ar2. 2: contradiction.
      destruct (HQX' x) as [HX_q | HX_fr]. eauto.
      -- (* q *) left. eapply lls_mono. 2: eauto. eapply vars_locs_monotonic. unfoldq. intuition. 
      -- (* fr *)
         destruct frx. 2: contradiction.
         right. simpl. 
         destruct (fn2 && frf); simpl. 
         intros ?. eapply HX_fr. eapply SC1; eauto.
         intros ?. eapply HX_fr. eapply SC1. eauto. 
    * (* fresh *)
      destruct fr2. 2: contradiction.
      right. destruct (fn2 && frf || ar2 && frx); simpl.
      intros ?. eapply HY_fr. eapply SC2; eauto. eapply SC1; eauto.
      intros ?. eapply HY_fr. eapply SC2; eauto. eapply SC1; eauto.
Qed.

Lemma sem_seq: forall env t1 t2 p1 p2 p q1 q2
  (E1: sem_type env t1 TBool p1 false q1)
  (E2: sem_type env t2 TBool p2 false q2)
  (SUB1: psub p1 p)
  (SUB2: psub p2 p),
  sem_type env (tseq t1 t2) TBool p false pempty.
Proof.
  intros. intros S1 M1 H WFE ST.
  (* E1 *)
  assert (env_type M1 H env p1) as WFE1. { eapply envt_tighten; eauto. }
  destruct (E1 S1 M1 H WFE1 ST) as [S2 [M2 [v1 [IE1 [SC1 [ST1 [SE1 [HV1 HQ1]]]]]]]].
  destruct v1; try solve [inversion HV1]. simpl in HV1.

  (* E2 *) 
  eapply envt_store_extend in WFE as WFE'. 2: eapply SC1. 
  assert (env_type M2 H env p2) as WFE2. { eapply envt_tighten; eauto. }

  destruct (E2 S2 M2 H WFE2 ST1) as [S3 [M3 [v2 [IE2 [SC2 [ST2 [SE2 [HV2 HQ2]]]]]]]].
  destruct v2; try solve [inversion HV2]. simpl in HV2.
  
  exists S3.
  exists M3, (vbool (b && b0)).
  split. 2: split. 3: split. 4: split. 5: split. 
  + destruct IE1 as [n1 IE1].
    destruct IE2 as [n2 IE2].
    exists (S(n1 + n2)). intros. destruct n. intuition.
    simpl. rewrite IE1. rewrite IE2. eauto. lia. lia.

  + eapply stchain_chain''; eauto. eapply SC1.
  
  + eauto.
  
  + eapply se_trans; eapply se_sub; eauto. eapply lls_mono; eauto. eapply vars_locs_monotonic. eauto. 
    intros ? ?. erewrite lls_change. eapply lls_mono; eauto. eapply vars_locs_monotonic; eauto.
    eapply stchain_tighten; eauto. eapply env_type_store_deep_wf. eapply WFE. intros ? ?. auto.
  
  + simpl. eauto. 
  + eapply valq_bool.
Qed.


Lemma sem_sub: forall env y T p fr1 q1 fr2 q2,
    sem_type env y T p fr1 q1 ->
    psub q1 q2 ->
    psub q2 (pdom env)  ->
    sem_type env y T p (fr1 || fr2)  q2.
Proof.
  intros. intros ? ? ? WFE ST.
  destruct (H S M E WFE ST) as [S1 [M1 [vx [IW1 [SC1 [ST1 [SE1 [HVX HQX]]]]]]]].
  assert (psub q2 (pdom E)). {
    unfoldq. destruct WFE. rewrite H2. intuition. } 
  exists S1, M1. exists vx. split. 2: split. 3: split. 4: split. 5: split.
  eauto. eauto. eauto.
  unfold val_qual in HQX; intuition.
  eauto.
  eapply valq_sub; eauto.
Qed.

Lemma sem_sub_var: forall env y T p fr1 q1 Tx qx x,
    sem_type env y T p fr1 q1 ->
    q1 x ->
    indexr x env = Some (Tx, false, qx) ->
    psub (plift qx) p -> 
    sem_type env y T p fr1 (por (pdiff q1 (pone x)) (plift qx)).
Proof.
  intros. rename x into z. intros ? ? ? WFE ST.
  destruct (H S M E WFE ST) as [S1 [M1 [vx [IW1 [SC1 [ST1 [SE1 [HVX HQX]]]]]]]].
  exists S1, M1. exists vx. intuition.
  eapply WFE in H1 as HZ.
  intros ? ?. destruct (HQX x). eauto.
  - eapply lls_vars in H4. destruct H4. bdestruct (x0 =? z).
    + subst. destruct HZ as [vz ?]. intuition.      
      eapply lls_var in H8. destruct H8 as (? & ? & ?). rewrite H4 in H8.
      inversion H8. subst x0. 
      left.
      erewrite lls_change with (M:=M) (M':=M1) in H10.
      erewrite lls_change with (M:=M) (M':=M1) in H10.
      eapply lls_mono. 2: eapply H10. eapply vars_locs_monotonic.
      unfoldq. intuition.
      eauto.
      eapply stchain_tighten. eauto. eapply env_type_store_deep_wf. eauto. eauto.
      eapply stchain_tighten. eauto. eapply valt_deep_wf. eapply H7. eapply H5.
    + left. eapply lls_vars'. eapply H4. unfoldq. intuition.
  - right. intuition. 
Qed.



(* if well-typed, then result is an actual value (not stuck and not a timeout),
   for large enough n *)

Theorem fundamental_property : forall t G T p fr q,
    has_type G t T p fr q ->
    sem_type G t T (plift p) fr (plift q).
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
  - rewrite plift_empty. eapply sem_seq; eauto.
  - eapply sem_sub; eauto.
  - rewrite plift_or, plift_diff, plift_one. 
    eapply sem_sub_var; eauto.
Qed.


(* Semantic type safety and termination: if the term is well-typed, then 
   it evaluates to an actual value (not stuck and not a timeout) of the
   same time (for large enough n) *)
Corollary safety : forall t T fr q,
  has_type [] t T qempty fr q -> 
  exp_type [] st_zero [] t T (plift qempty) fr (plift q).
Proof. 
  intros. eapply fundamental_property in H; eauto.
  destruct (H [] st_zero []). 
  - unfold env_type; intuition; simpl.
    unfoldq. intuition. inversion H0.
    intros ? [? ?]. inversion H3.
    subst. destruct H5. destruct H5. eapply H0 in H5. rewrite plift_empty in H5. destruct H5.
    subst. destruct H5. destruct H5. eapply H0 in H5. rewrite plift_empty in H5. destruct H5.
  - unfold store_type; intuition. unfold st_locs, st_zero in *. unfoldq. simpl in *. lia. 
  - destruct H0. eexists. eexists. eauto.
Qed.

(* encapsulation lemma *)

Lemma encapsulation: forall G t T
  (W: has_type G t T qempty false qempty),
  forall H M,
  env_type M H G pempty ->   
  forall S' M', 
  st_chain M M' pempty ->
  store_type S' M' ->
  exp_type S' M' H t T pempty false pempty.
Proof.
  intros G t T ?. intros H M WFE.
  intros S' M' STC ST'.
  eapply fundamental_property in W. 
  rewrite plift_empty in W.
  eapply W. eapply envt_store_change. eauto.
  rewrite vars_locs_empty. rewrite lls_empty.
  auto. auto.
Qed.

End STLC.
