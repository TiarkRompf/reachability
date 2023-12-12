(* Full safety for STLC *)

(* based on stlc_reach.v and stlc_ref.v *)
(* based on stlc_reach_ref_wip_overlap.v *)
(* based on stlc_reach_ref_overlap_self_fresh_mut.v *)

(*

Simply-typed lambda calculus with reachability types, combined
proof of termination and type soundness (using logical relations).


THIS FILE:

- types and qualifiers
  - overlap (explicit transitive closure)
  - self refs
  - fresh flag
  - subtyping, self/arg refs
  - no parametric polymorphism

- references
  - boolean refs only
  - mutation with put/get
  - no nested refs

- effects
  - no effects

- examples
  - box type, transparent <: opaque


Internals:

- st_chain
- mirror env V, no val_locs
- no upper bound on overlap in env_type


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
  | TRef   : ty -> ty
  | TFun   : ty -> bool -> bool -> ql ->
             ty -> bool -> bool -> bool -> ql ->
             ty
.

(* TFun
        T1      : argument type

        q1fn    : argument may alias function?
        q1fr    : argument may be fresh?
        q1      : argument reachability qualifer (set of variables)

        T2      : result type

        q2fn    : result may alias function?
        q2ar    : result may alias argument?
        q2fr    : result may be fresh?
        q2      : result reachability qualifer (set of variables)

*)

Inductive tm : Type :=
  | ttrue : tm
  | tfalse : tm
  | tvar : id -> tm
  | tref : tm -> tm
  | tget : tm -> tm
  | tput : tm -> tm -> tm
  | tapp : tm -> tm -> tm (* f(x) *)
  | tabs : tm -> tm (* \f x.t *)
.


Inductive vl : Type :=
  | vbool : bool -> vl
  | vref  : id -> vl
  | vabs  : list vl -> tm -> vl    (* closure record  *)
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
| c_ref: forall m T,
    closed_ty m T ->
    closed_ty m (TRef T)
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

Definition bsub b1 b2 := b1 = true -> b2 = true.

Inductive qstp : tenv -> ql -> ql -> ql -> Prop :=
| qs_sub: forall G p q1 q2,
    psub (plift q1) (plift q2) ->
    closed_ql (length G) q1 ->
    closed_ql (length G) q2 ->
    qstp G p q1 q2
| qs_var: forall G p x Tx qx q1 ,
    plift q1 x ->
    psub (plift qx) (plift p) ->
    indexr x G = Some (Tx, false, qx) ->
    closed_ql (length G) q1 ->
    closed_ql (length G) qx -> (* get from env? we even know < x *)
    qstp G p q1 (qor (qdiff q1 (qone x)) qx)
| qs_trans: forall G p q1 q2 q3,
    qstp G p q1 q2 ->
    qstp G p q2 q3 ->
    qstp G p q1 q3
.

Inductive stp : tenv -> ql -> bool -> ty -> bool -> ql -> ty -> bool -> ql -> Prop :=
| s_bool: forall G p grf q1 q2 fr1 fr2,
    qstp G p q1 q2 ->
    bsub fr1 fr2 ->
    stp G p grf TBool fr1 q1 TBool fr2 q2
| s_ref: forall G p grf T1 q1 q2 fr1 fr2,
    qstp G p q1 q2 ->
    bsub fr1 fr2 ->
    closed_ty (length G) T1 ->
    stp G p grf (TRef T1) fr1 q1 (TRef T1) fr2 q2 (* todo: T1 <: T2, T2 <: T1 *)
| s_fun: forall G p T1a q1fn_a q1fr_a q1a T2a q2fn_a q2ar_a q2fr_a q2a qffr_a qfa
            gr2 grf T1b q1fn_b q1fr_b q1b T2b q2fn_b q2ar_b q2fr_b q2b qffr_b qfb,
    stp G p false
      T1b
      (q1fn_b || q1fr_b)
      q1b
      T1a (q1fn_a || q1fr_a)
      q1a ->
    stp G p gr2
      T2a
      (q2fn_a || q2ar_a || q2fr_a) (* might be diff in syntactic formalization *)
      q2a
      T2b
      (q2fn_b || q2ar_b || q2fr_b) q2b ->
    bsub q1fn_b q1fn_a ->
    bsub q1fr_b q1fr_a ->
    bsub q2fn_a q2fn_b ->
    bsub q2ar_a q2ar_b ->
    bsub q2fr_a q2fr_b ->
    bsub qffr_a qffr_b ->
    qstp G p qfa qfb ->
    stp G p grf (* grf: whether it allows to grow locations *)
      (TFun T1a q1fn_a q1fr_a q1a T2a q2fn_a q2ar_a q2fr_a q2a) qffr_a qfa
      (TFun T1b q1fn_b q1fr_b q1b T2b q2fn_b q2ar_b q2fr_b q2b) qffr_b qfb
| s_fun_fresh_arg_to_self_res: forall G p T1a T1b T2 fr1 fr2 q1 q2 q1b q1a q1fn_a q2fn_a q2ar_a q2ar_b,
    closed_ty (length G) T2 ->
    closed_ql (length G) q1 ->
    closed_ql (length G) q2 ->
    psub (plift q1b) (pdom G) ->
    psub (plift q1a) (plift p) ->
    psub (plift q1) (plift q2) -> (* use qstp? *)
    (q2ar_a = true -> psub (plift q1a) (plift q2)) -> (* only needed when switching x -> f *)
    stp G p true T1b false q1b T1a false (*fr2*) q1a ->                  (*  A2^u  -> A1^a  *)
    (* GW: q1a is not used in the conclusion? *)
    (* GW: what is grf? *)
    (q1fn_a = true \/ fr1 = false /\ q1 = qempty) ->
    bsub fr1 fr2 ->
    stp G p q2ar_a
      (TFun T1a q1fn_a true qempty T2 q2fn_a q2ar_a false qempty) fr1 q1  (*  A1^f* -> B^x  q1    *)
      (TFun T1b false  false q1b   T2 true   q2ar_b false qempty) fr2 q2  (*  A2^u  -> B^f  q1,a  *)
| s_fun_q2_to_fn2: forall G p T1 T2 q1fr q2fn_a q1 q2 fr1 qfa qfb,
    closed_ty (length G) T1 ->
    closed_ty (length G) T2 ->
    closed_ql (length G) qfa ->
    closed_ql (length G) qfb ->
    closed_ql (length G) q1 ->
    psub (plift qfb) (plift p) ->
    psub (plift qfa) (plift qfb) ->
    psub (plift q2)  (plift qfb) ->
    stp G p true
      (TFun T1 false q1fr q1 T2 q2fn_a false false q2)     fr1 qfa  (*   A^u -> B^af      *)
      (TFun T1 false q1fr q1 T2 true false false qempty) fr1 qfb  (* ( A^u -> B^f )^a  *)
| s_fun_non_drop_grow: forall G p T1a q1fn_a q1fr_a q1a T2a q2a qffr_a qfa
                              gr2 T1b q1fn_b q1fr_b q1b T2b q2b qffr_b qfb,
    stp G p true
      T1b (q1fn_b || q1fr_b) q1b
      T1a (q1fn_a || q1fr_a) q1a ->
    stp G p gr2
      T2a true q2a
      T2b true q2b ->
    bsub q1fn_b q1fn_a ->
    bsub q1fr_b q1fr_a ->
    bsub qffr_a qffr_b ->
    qstp G p qfa qfb ->
    qstp G p q1a qfb ->
    closed_ql (length G) q1a ->
    closed_ql (length G) q1b ->
    closed_ql (length G) q2a ->
    closed_ql (length G) q2b ->
    q1fn_b = true -> q1fn_a = true /\ q1fr_a = true ->
    stp G p true (* grf: whether it allows to grow locations *)
      (TFun T1a q1fn_a q1fr_a q1a T2a false true false q2a) qffr_a qfa
      (TFun T1b q1fn_b q1fr_b q1b T2b true  true false q2b) qffr_b qfb
| s_fun_expand_arg: forall G p T1 T2 fr1 q1 q1b q1fn_a q2fn_a grf,
    closed_ty (length G) T1 ->
    closed_ty (length G) T2 ->
    closed_ql (length G) q1b ->
    closed_ql (length G) q1 ->
    (q1fn_a = true \/ fr1 = false /\ q1 = qempty) ->
    stp G p grf
      (TFun T1 q1fn_a true qempty T2 q2fn_a true false qempty) fr1 q1  (*  A^*f   -> B^x  *)
      (TFun T1 q1fn_a true q1b    T2 q2fn_a true false qempty) fr1 q1  (*  A^*f,a -> B^x  *)
| s_refl: forall G p grf T1 q1 fr1, (* not strictly needed, s_boo/ref/fun all support refl *)
    closed_ty (length G) T1 ->
    closed_ql (length G) q1 ->
    stp G p grf T1 fr1 q1 T1 fr1 q1
| s_trans: forall G p grf T1 T2 T3 q1 q2 q3 fr1 fr2 fr3,
    stp G p grf T1 fr1 q1 T2 fr2 q2 ->
    stp G p grf T2 fr2 q2 T3 fr3 q3 ->
    stp G p grf T1 fr1 q1 T3 fr3 q3.

Inductive has_type : tenv -> tm -> ty -> ql -> bool -> ql -> Prop :=
| t_true: forall env p,
    has_type env ttrue TBool p false qempty
| t_false: forall env p,
    has_type env tfalse TBool p false qempty
| t_var: forall x env T p fr q,
    indexr x env = Some (T, fr, q) ->
    (plift p) x ->
    has_type env (tvar x) T p false (qone x)
| t_ref: forall t env p fr q,
    has_type env t TBool p fr q ->
    has_type env (tref t) (TRef TBool) p true q
| t_get: forall t env p fr q,
    has_type env t (TRef TBool) p fr q ->
    has_type env (tget t) TBool p false qempty
| t_put: forall t1 t2 env p fr1 q1 fr2 q2,
    has_type env t1 (TRef TBool) p fr1 q1 ->
    has_type env t2 TBool p fr2 q2 ->
    has_type env (tput t1 t2) TBool p false qempty
| t_app: forall env f t T1 T2 p frf qf frx qx fn1 fr1 q1 fn2 ar2 fr2 q2,
    has_type env f (TFun T1 fn1 fr1 q1 T2 fn2 ar2 fr2 q2) p frf qf->
    has_type env t T1 p frx qx ->
    (* ---- different app cases: *)
    (if fn1 then
       if fr1 then
         True
       else
         (frx = false /\ (exists x0, f = tvar x0 /\ psub (plift qx) (pone x0)) \/
            frx = false /\ psub (plift qx) (plift q1))
     else
       if fr1 then
         psub (pand
                 (vars_trans' env qf)
                 (vars_trans' env qx))
           (plift q1)
           (* TODO: also support qx < q1! *)
       else
         frx = false /\ psub (plift qx) (plift q1)) ->
    (* ---- *)
    psub (plift q2) (plift p) ->   (* this is necessary (so far!) *)
    has_type env (tapp f t) T2 p
      (fn2 && frf || ar2 && frx || fr2)
      (qor (qif fn2 qf) (qor (qif ar2 qx) q2))
| t_abs: forall env t T1 T2 p fn1 fr1 q1 fn2 ar2 fr2 q2 qf,
    has_type ((T1, fr1, (qand p (qor q1 (qif fn1 qf))))::env) t T2
      (qor (qand p qf) (qone (length env)))
      fr2
      (qor q2 (qor (qif fn2 qf) (qif ar2 (qone (length env))))) ->
    psub (plift q1) (plift p) ->   (* relax? necessary so far *)
    closed_ty (length env) T1 ->
    closed_ty (length env) T2 ->
    closed_ql (length env) q1 ->
    closed_ql (length env) q2 ->
    closed_ql (length env) qf ->
    has_type env (tabs t)
      (TFun T1 fn1 fr1 q1 T2 fn2 ar2 fr2 q2)
      p false qf
| t_sub: forall env y T p fr1 q1 fr2 q2, (* not necessary? *)
    has_type env y T p fr1 q1 ->
    psub (plift q1) (plift q2) ->
    psub (plift q2) (pdom env)  ->
    has_type env y T p (fr1 || fr2)  q2
| t_sub_var: forall env y T p fr1 q1 qx x Tx, (* not necessary? *)
    has_type env y T p fr1 q1 ->
    plift q1 x ->
    indexr x env = Some (Tx, false, qx) ->
    psub (plift qx) (plift p) -> (* necessary? *)
    has_type env y T p fr1 (qor (qdiff q1 (qone x)) qx)
| t_sub_stp: forall env grf y T1 T2 p fr1 q1 fr2 q2,
    has_type env y T1 p fr1 q1 ->
    stp env p grf T1 fr1 q1 T2 fr2 q2 ->
    psub (plift q2) (plift p) -> (* necessary? *)
    has_type env y T2 p fr2 q2
.



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
            | (M', Some (Some (vabs _ _))) => (M', Some None)
            | (M', Some (Some (vref x))) => (M', Some (indexr x M'))
          end
        | tput er ex    =>
          match teval n M env er with
            | (M', None) => (M', None)
            | (M', Some None) => (M', Some None)
            | (M', Some (Some (vbool _))) => (M', Some None)
            | (M', Some (Some (vabs _ _))) => (M', Some None)
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
        | tabs y       => (M, Some (Some (vabs env y)))
        | tapp ef ex =>
          match teval n M env ef with
            | (M', None) => (M', None)
            | (M', Some None) => (M', Some None)
            | (M', Some (Some (vbool _))) => (M', Some None)
            | (M', Some (Some (vref _))) => (M', Some None)
            | (M', Some (Some (vabs env2 ey))) =>
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



(* ---------- logical relation ---------- *)


(* mapping values and variables to store locations *)

Definition lenv: Type := list ql.

Definition var_locs E x l := exists vx, indexr x E = Some vx /\ plift vx l.

Definition vars_locs E q l := exists x, q x /\ var_locs E x l.

Fixpoint vars_locs_fix (V: lenv) (q: ql) (l: nat): bool :=
  match V with
  | ls :: V => (q (length V) && ls l) || vars_locs_fix V q l
  | [] => false
  end.


(* store typings / "worlds" *)

(* length and set of accessible locations *)

Definition stty: Type := nat * pl.

Definition st_length (M: stty) := fst M.
Definition st_locs (M: stty) := snd M.

Definition store_type (S: stor) (M: stty) :=
  length S = st_length M /\
    forall l,
      st_locs M l ->
      exists b,
        indexr l S = Some (vbool b).

Definition st_zero: stty :=
  (0, pempty).

Definition st_plus M1 M2: stty :=
  (st_length M1 + st_length M2,
    por (st_locs M1) (st_locs M2)).

Definition pstdiff M' M :=
  (* pdiff (pdom (M'++M)) (pdom M) *)
  pdiff (st_locs M') (st_locs M).

#[global] Hint Unfold st_length.
#[global] Hint Unfold st_locs.
#[global] Hint Unfold st_plus.
#[global] Hint Unfold pstdiff.


Definition st_extend M1 M2 :=
  st_length M1 <= st_length M2 /\
psub (st_locs M1) (st_locs M2).


Lemma stchain_refl: forall M,
    st_extend M M.
Proof.
  intros. unfold st_extend in *.
  intuition. intros ? Q. eauto.
Qed.

Lemma stchain_chain: forall M1 M2 M3,
    st_extend M1 M2 ->
    st_extend M2 M3 ->
    st_extend M1 M3.
Proof.
  intros. unfold st_extend in *.
  intuition. intros ? Q. eauto.
Qed.



(* value interpretation of types *)

Fixpoint val_type (M:stty) (H:venv) (V:lenv) v T (ls: ql): Prop :=
  match v, T with
  | vbool b, TBool =>
      ls = qempty
  | vref l, TRef TBool =>
      st_locs M l /\ ls = qone l
  | vabs G ty, TFun T1 fn1 fr1 q1 T2 fn2 ar2 fr2 q2 =>
        closed_ty (length H) T1 /\
        (psub (plift q1) (pdom H)) /\
        closed_ty (length H) T2 /\
        (psub (plift q2) (pdom H)) /\
        (psub (plift ls) (st_locs M)) /\
        (forall S' M' vx lsx,
            st_extend M M'
            ->
            store_type S' M'
            ->
            val_type
              M'
              H
              V
              vx
              T1
              lsx
            ->
              psub (plift lsx)
                (por (vars_locs V (plift q1))
                   (por (pif fn1 (plift ls))
                      (pif fr1 (pnot (plift ls)))))
            ->
              exists S'' M'' vy lsy,
                tevaln
                  S'
                  (vx::G)
                  ty
                  S''
                  vy
                /\
                  st_extend M' M''
                /\
                  store_type S'' M''
                /\
                  val_type
                    M''
                    H
                    V
                    vy
                    T2
                    lsy
                /\
                  psub (plift lsy)
                    (por (vars_locs V (plift q2)) (* allow v \/ vx? *)
                       (por (pif fn2 (plift ls))
                          (por (pif ar2 (plift lsx))
                             (pif fr2 (pstdiff M'' M'))))))
  | _,_ =>
      False
  end.


Definition val_qual (M M1: stty) V lsv fr (q: pl) :=
  psub (plift lsv)
    (por (vars_locs V q)
       (pif fr (pstdiff M1 M))).


Definition exp_type S M H V t T p fr q :=
  exists S' M' v ls,
    tevaln S H t S' v /\
    st_extend M M' /\
    store_type S' M' /\
    val_type M' H V v T ls /\
    val_qual M M' V ls fr (pand p q) /\
    (match t with tvar x => psub (vars_locs V (pone x)) (plift ls) | _ => True end)
.



Definition env_type M H G V p :=
  length H = length G /\
  length V = length G /\
    psub p (pdom V) /\
    (forall x T fr (q:ql),
        indexr x G = Some (T, fr, q) ->
        (* p x -> not actually needed *)
        exists (v : vl) ls,
          psub (plift q) (pdom H) /\
          closed_ty x T /\
          closed_ql x q /\
          indexr x H = Some v /\
          indexr x V = Some ls /\
          val_type M H V v T ls /\
          (fr = false -> psub (plift ls) (vars_locs V (plift q)))) /\
    (forall q q',
        psub q p ->
        psub q' p ->
        psub (pand (vars_locs V q) (vars_locs V q'))
          (vars_locs V (pand (vars_trans G q) (vars_trans G q')))).


Definition sem_type G e T p fr q :=
  forall S M E V,
    env_type M E G V p ->
    store_type S M  ->
    exp_type S M E V e T p fr q.


#[global] Hint Constructors ty.
#[global] Hint Constructors tm.
#[global] Hint Constructors vl.


#[global] Hint Constructors has_type.

#[global] Hint Constructors option.
#[global] Hint Constructors list.


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

Lemma plift_closed: forall (env: venv) q,
    closed_ql (length env) q = psub (plift q) (pdom env).
Proof.
  intros. unfoldq. unfold closed_ql, plift. eauto.
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

Lemma pand_sub: forall p q,
    psub p q ->
    pand q p = p.
Proof.
  intros. unfoldq. unfold plift. eapply functional_extensionality. intros.
  eapply propositional_extensionality. split; intros; intuition.
Qed.



Lemma plift_vars_locs: forall H q,
    plift (vars_locs_fix H q) = vars_locs H (plift q).
Proof.
  intros. eapply functional_extensionality.
  intros. eapply propositional_extensionality.
  unfold vars_locs, var_locs, plift in *.
  intuition.
  - induction H. intuition.
    remember (q (length H)) as b1.
    remember (a x) as b2.
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
  - simpl. destruct H0 as [? [? ?]]. destruct H1 as [? [? ?]].
    unfold indexr in H1. induction H.
    congruence.
    bdestruct (x0 =? length H).
    inversion H1. subst. simpl. rewrite H0.
    unfold plift in H2. rewrite H2. simpl. eauto.
    simpl. rewrite IHlist.
    destruct (q (length H) && a x); simpl; eauto.
    eauto.
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
  plift v l.
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
    indexr x env = Some (T, fr1, q1) -> closed_ty x T /\ closed_ql x q1.

Lemma telescope_shrink: forall env T fr q,
    telescope ((T,fr,q)::env) -> telescope env.
Proof.
  intros G. intros.
  unfold telescope in *. intros.
  eapply H. eapply indexr_extend1 in H0. eapply H0.
Qed.

Lemma telescope_extend: forall env T fr q,
    closed_ql (length env) q ->
    closed_ty (length env) T ->
    telescope env -> telescope ((T,fr,q)::env).
Proof.
  intros G. intros.
  unfold telescope in *. intros.
  bdestruct (x =? length G).
  subst. rewrite indexr_head in H2. inversion H2. subst. eauto.
  rewrite indexr_skip in H2; eauto.
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


(* ---------- store_type lemmas  ---------- *)

Lemma stplus_assoc: forall M1 M2 M3,
    st_plus M1 (st_plus M2 M3) = st_plus (st_plus M1 M2) M3.
Proof.
  intros. unfold st_plus. simpl.
  replace (st_length M1 + st_length M2 + st_length M3)
    with (st_length M1 + (st_length M2 + st_length M3)).
  replace (por (por (st_locs M1) (st_locs M2)) (st_locs M3))
    with (por (st_locs M1) (por (st_locs M2) (st_locs M3))).
  eauto.
  apply functional_extensionality. intros.
  apply propositional_extensionality. unfoldq. intuition.
  lia.
Qed.

Lemma stplus_zero: forall M1,
    st_plus st_zero M1 = M1.
Proof.
  intros. unfold st_plus. simpl.
  replace (por pempty (st_locs M1)) with (st_locs M1).
  destruct M1. simpl. eauto.
  apply functional_extensionality. intros.
  apply propositional_extensionality. unfoldq. intuition.
Qed.


Lemma storet_wf: forall S M,
    store_type S M ->
    psub (st_locs M) (pdom S).
Proof.
  intros. intros ? ?. eapply H in H0.
  destruct H0. eapply indexr_var_some'. eauto.
Qed.


(* ---------- val_type lemmas  ---------- *)

Lemma valt_wf: forall T M H V v ls,
    val_type M H V v T ls ->
    psub (plift ls) (st_locs M).
Proof.
  intros T. induction T; intros; destruct v; simpl in *; intuition.
  + subst. unfoldq. intuition.
  + destruct T, H0. subst. rewrite plift_one. unfoldq. intros. subst. intuition.
Qed.


Lemma valt_closed: forall T M H V v ls,
    val_type M H V v T ls ->
    closed_ty (length H) T.
Proof.
  intros T. induction T; intros; destruct v; simpl in *; intuition.
  + econstructor.
  + destruct T; try contradiction.
    repeat econstructor; eauto.
  + econstructor; eauto.
Qed.


Lemma valt_store_extend: forall T M' M H V v ls,
    val_type M H V v T ls ->
    st_extend M M' ->
    val_type M' H V v T ls.
Proof.
  intros T. induction T; intros; destruct v; simpl in *; intuition.
  - destruct T; try contradiction.
    unfold st_extend in *. intuition.
  - intros ? Q. eapply H1. eauto.
  - destruct (H7 S' M'0 vx lsx) as [S'' [M'' [vy  [lsy [HEY HVY]]]]].
    eapply stchain_chain. eauto. eauto.
    eauto.
    eauto.
    eauto.
    exists S'', M'', vy, lsy.
    intuition.
Qed.


Lemma valt_extend: forall T M H' H V' V v ls
    (L: length H = length V),
    closed_ty (length H) T ->
    val_type M (H'++H) (V'++V) v T ls <-> val_type M H V v T ls.
Proof.
  intros T. induction T; split; intros; destruct v; simpl in *; intuition.
  - inversion H0. auto.
  - inversion H0. auto.
  - inversion H0. auto.
  - inversion H0. auto.
  - (* Abs shrink *)
    inversion H0. subst.
    rename q into q2.
    destruct (H7 S' M' vx lsx) as [S'' [M'' [vy [lsy [HEY HVY]]]]]. eauto. eauto.
      eapply IHT1; eauto.
    rewrite vars_locs_extend; auto.
    unfoldq. intuition. eapply H23 in H11. lia.
    exists S'', M'', vy, lsy. intuition.
    eapply IHT2; eauto.
    rewrite vars_locs_extend in H15. eauto.
    unfoldq. intuition. eapply H24 in H14. lia.
  - eapply closedty_extend; eauto.
  - eapply closedq_extend; eauto.
  - eapply closedty_extend; eauto.
  - unfoldq. rewrite app_length. intuition. eapply H4 in H6. lia.
  - (* Abs grow *)
    inversion H0. subst.
    rename q into q2.
    destruct (H7 S' M' vx lsx) as [S'' [M'' [vy [lsy [HEY [ST2 [HVY HQY]]]]]]]. eauto. eauto.
      eapply IHT1; eauto.
      rewrite vars_locs_extend in H10; auto.
      unfoldq. intuition. eapply H23 in H11. lia.
    exists S'', M'', vy, lsy. intuition.
    eapply IHT2; eauto.
    rewrite vars_locs_extend.
    eauto.
    unfoldq. intuition. eapply H24 in H13. lia.
Qed.


Lemma valt_extend1: forall T M H V v vx ls lsx,
    length H = length V ->
    closed_ty (length H) T ->
    val_type M (vx::H) (lsx::V) v T ls <-> val_type M H V v T ls.
Proof.
  intros.
  replace (vx :: H)  with ([vx] ++ H); auto.
  replace (lsx :: V)  with ([lsx] ++ V); auto.
  eapply valt_extend; eauto.
Qed.


(* ---------- val_qual lemmas  ---------- *)

Lemma valq_sub: forall M M1 V v q fr fr' q',
    val_qual M M1 V v fr q ->
    psub q q' ->
    psub q' (pdom V) ->
    val_qual M M1 V v (fr || fr') q'.
Proof.
  intros. unfoldq. intuition.
  destruct (H x) as [H_q | H_fr]. intuition.
  - (* q  *) destruct H_q. left. exists x0. intuition.
  - (* fr *) destruct fr. 2: contradiction. right. eauto.
Qed.


(* ---------- environment lemmas  ---------- *)

Lemma wf_env_type: forall M H G V p,
  env_type M H G V p ->
  length H = length G /\
  length V = length G /\
  pdom H = pdom G /\
  pdom V = pdom G.
Proof.
  intros. unfold env_type in H0. intuition.
  unfold pdom. rewrite H1. auto.
  unfold pdom. rewrite H0. auto.
Qed.

Lemma envt_telescope: forall M H G V p,
    env_type M H G V p -> telescope G.
Proof.
  intros. destruct H0 as (? & ? & ? & ? & ?).
  intros ? ? ? ? ?. edestruct H3 as (? & ? & ?); eauto.
  intuition.
Qed.


Lemma env_type_store_wf: forall M H G V p q,
    env_type M H G V p ->
    psub q p ->
    psub (vars_locs V q) (st_locs M).
Proof.
  intros. destruct H0 as [L1 [L2 [P [W1 W2]]]]; intuition.
  unfoldq. intuition.
  destruct H0 as [? [? ?]].
  assert (p x0). eapply H1. eauto.
  assert (x0 < length V). eauto.
  destruct H2 as [? [? ?]].

  assert (exists xtq, indexr x0 G = Some xtq) as TY.
  rewrite L2 in H4.  eapply indexr_var_some in H4. intuition.
  destruct TY as [TQ  ?]. destruct TQ as [[T0 fr0] q0].
  destruct (W1 x0 T0 fr0 q0) as [vx [lsx [? ?]]]. eauto.

  intuition. apply valt_wf in H12.
  rewrite H2 in H11. inversion H11. subst.
  unfoldq. intuition.
Qed.


Lemma env_type_store_wf2: forall M H G V p q,
    env_type M H G V p ->
    psub q (pdom G) ->
    psub (vars_locs V q) (st_locs M).
Proof.
  intros. destruct H0 as [L1 [L2 [P [W1 W2]]]]; intuition.
  unfoldq. intuition.
  destruct H0 as [? [? ?]].
  assert ((pdom G) x0). eapply H1. eauto.
  assert (x0 < length V). rewrite L2. eauto.
  destruct H2 as [? [? ?]].

  assert (exists xtq, indexr x0 G = Some xtq) as TY.
  rewrite L2 in H4.  eapply indexr_var_some in H4. intuition.
  destruct TY as [TQ  ?]. destruct TQ as [[T0 fr0] q0].
  destruct (W1 x0 T0 fr0 q0) as [vx [lsx [? ?]]]. eauto.

  intuition. apply valt_wf in H12.
  rewrite H2 in H11. inversion H11. subst.
  unfoldq. intuition.
Qed.


Lemma envt_tighten: forall M H G V p p',
    env_type M H G V p ->
    psub p' p ->
    env_type M H G V p'.
Proof.
  intros. destruct H0 as [L1 [L2 [P W]]].
  repeat split; auto.
  - unfoldq. intuition.
  - intros.
    destruct W as [W ?].
    destruct (W x T fr q); eauto.
  - intros.
    destruct W as [? W].
    eapply W.
    unfoldq. intuition.
    unfoldq. intuition.
Qed.

Lemma envt_store_extend: forall M M' H G V p,
    env_type M H G V p ->
    st_extend M M' ->
    env_type M' H G V p.
Proof.
  intros. destruct H0 as [L1 [L2 [P W]]].
  repeat split; auto. intros.
  destruct W as [W W'].
  destruct (W _ _  _ _ H0) as [vx [lsx [QH [CT [CL [IH [IV [HVX HF]]]]]]]]; intuition.
  exists vx, lsx; intuition.
  eapply valt_store_extend in HVX; eauto.
  intros.
  destruct W as [W' W].
  unfoldq. intuition.
Qed.

Lemma envt_extend_full: forall M M1 H G V vx T1 p fr1 q1 qf lsx,
    env_type M H G V p ->
    val_type M1 H V vx T1 lsx ->
    psub qf p ->
    psub (plift q1) p ->
    psub (pand (vars_locs V qf) (plift lsx))
      (vars_locs V (plift q1)) ->
    (fr1 = false -> psub (plift lsx) (vars_locs V (plift q1))) ->
    closed_ty (length H) T1 ->
    closed_ql (length H) q1 ->
    st_extend M M1 ->
    env_type M1 (vx :: H) ((T1, fr1, q1) :: G) (lsx::V) (por qf (pone (length H))).
Proof.
  intros. apply wf_env_type in H0 as H0'. destruct H0' as (L' & L'' & PD & PD' (*& SG*)).

  assert (env_type M1 H G V p) as WFE. {
    eapply envt_store_extend; eauto. }

  remember WFE as WFE1. clear HeqWFE1.
  destruct WFE as [L1 [L2 [P [W1 W2]]]].
  assert (psub p (pdom G)) as PG. rewrite <-PD'. eauto.
  assert (psub p (pdom H)) as PH. rewrite PD. eauto.
  assert True. eauto.

  repeat split; eauto.
  - simpl. eauto.
  - simpl. eauto.
  - unfoldq. simpl. intuition.
  - intros.
    bdestruct (x =? length G); intuition.
    + subst. rewrite indexr_head in H10. inversion H10. subst.
      exists vx, lsx. repeat split.
      unfoldq; intuition. simpl.
      specialize (H2 x); intuition.
      rewrite <-L'. eauto.
      rewrite <-L'. eauto.
      rewrite <-L'. rewrite indexr_head. auto.
      rewrite <-L''. rewrite indexr_head. auto.
      eapply valt_extend1; auto. lia.
      rewrite <-vars_locs_extend with (H':=[lsx]) in H5; eauto.
      unfoldq. intuition.
    + rewrite indexr_skip in H10.
      specialize (W1 x T fr q H10).
      assert (x < length H). { rewrite L'. apply indexr_var_some' in H10. auto. }
      rewrite indexr_skip, indexr_skip.
      destruct W1 as [v [ls [HSUB [TL1 [TL [IH [IV [VALT FR]]]]]]]].
      exists v, ls. repeat split.
      unfoldq; intuition. simpl. eapply HSUB in H13. lia.
      auto. auto. auto. auto.
      eapply valt_extend1. lia. eapply valt_closed in VALT; eauto.
      auto.
      rewrite <-vars_locs_extend with (H':=[lsx]) in FR; eauto.
      intros ? Q. eapply TL in Q. unfoldq. lia.
      lia. lia. lia.
  - (* 2nd invariant *)
    intros q q' QSUB QSUB' x (QQ & QQ').

    destruct QQ as (? & VTQ & VLQ).
    destruct QQ' as (? & VTQ' & VLQ').

    destruct (QSUB x0); intuition; destruct (QSUB' x1); intuition.

    + (* qf, qf *)
      destruct (W2 (pand (pdom H) q) (pand (pdom H) q')) with (x:=x).

      intros ? ?. destruct (QSUB x2) as [? | ?]. unfoldq. intuition.
      eauto. eauto. unfoldq. lia.
      intros ? ?. destruct (QSUB' x2) as [? | ?]. unfoldq. intuition.
      eauto. eauto. unfoldq. lia.

      split.
      exists x0. unfoldq. intuition. eapply var_locs_shrink. eauto. eauto.
      exists x1. unfoldq. intuition. eapply var_locs_shrink. eauto. eauto.
      exists x2. intuition.
      destruct H13. split.
      eapply vt_extend. eapply vt_mono. 2: eapply H12. unfoldq. intuition.
      eapply vt_extend. eapply vt_mono. 2: eapply H13. unfoldq. intuition.
      eapply var_locs_extend. eauto.

    + (* qf, x *)
      rename H4 into SEP.
      unfold pone in H11. subst x1. destruct (SEP x).

      unfoldq. intuition. exists x0. intuition.
      eapply var_locs_shrink. eauto. eauto.
      destruct VLQ' as (? & IX & ?). rewrite L1,<-L2,indexr_head in IX. inversion IX. congruence.

      destruct (W2 (pand (pdom H) q) (plift q1)) with (x:=x).

      (* q *) intros ? ?. destruct (QSUB x2) as [? | ?]. unfoldq. intuition.
      eauto. eauto. unfoldq. lia.
      (* q1 *) eauto.
      (* intros. destruct (QSUB' x2) as [? | [? | ?]]. unfoldq. intuition.
      eauto. eauto. unfoldq. lia. *)

      split.
      exists x0. unfoldq. intuition. eapply var_locs_shrink. eauto. eauto.
      exists x1. unfoldq. intuition.

      exists x2. intuition.
      destruct H4. split.
      eapply vt_extend. eapply vt_mono. 2: eapply H4. unfoldq. intuition.

      (* q1 expansion! *)
      right. exists (length H). intuition.
      destruct H14. rewrite indexr_extend,L2,<-L1 in H14. eapply H14.
      exists T1, fr1, q1. rewrite L1. rewrite indexr_head. intuition.
      unfold vars_trans'. rewrite plift_vt. eapply vt_extend. eauto.
      eapply telescope_extend; eauto. intros ? ?. rewrite <-L2. eapply P. eauto.
      rewrite <-L1. eauto. eapply envt_telescope; eauto.

      eapply var_locs_extend. eauto.

    + (* x, qf *)
      rename H4 into SEP.
      unfold pone in H10. subst x0. destruct (SEP x).

      unfoldq. intuition. exists x1. intuition.
      eapply var_locs_shrink. eauto. eauto.
      destruct VLQ as (? & IX & ?). rewrite L1,<-L2,indexr_head in IX. inversion IX. congruence.

      destruct (W2 (plift q1) (pand (pdom H) q')) with (x:=x).

      (* q1 *) eauto.
      (* q' *) intros ? ?. destruct (QSUB' x2) as [? | ?]. unfoldq. intuition.
      eauto. eauto. unfoldq. lia.

      split.
      exists x0. unfoldq. intuition.
      exists x1. unfoldq. intuition. eapply var_locs_shrink. eauto. eauto.

      exists x2. intuition.
      destruct H4. split.

      (* q1 expansion! *)
      right. exists (length H). intuition.
      destruct H14. rewrite indexr_extend,L2,<-L1 in H14. eapply H14.
      exists T1, fr1, q1. rewrite L1. rewrite indexr_head. intuition.
      unfold vars_trans'. rewrite plift_vt. eapply vt_extend. eauto.
      eapply telescope_extend; eauto. intros ? ?. rewrite <-L2. eapply P. eauto.
      rewrite <-L1. eauto. eapply envt_telescope; eauto.

      eapply vt_extend. eapply vt_mono. 2: eapply H10. unfoldq. intuition.

      eapply var_locs_extend. eauto.

    + (* x, x *)
      unfold pone in H10, H11.
      subst x0 x1.

      exists (length H). intuition. split.
      left. eauto. left. eauto.

  Unshelve.
      eauto. eauto.
Qed.


Lemma overlapping: forall M M' M'' H G V p vf vx frf qf frx qx q1
    (WFE: env_type M H G V p)
    (HQF: val_qual M M' V vf frf (pand p qf))
    (HQX: val_qual M' M'' V vx frx (pand p qx)),
    psub (plift vf) (st_locs M') ->
    psub (pand (vars_trans G (pand p qf)) (vars_trans G (pand p qx))) (plift q1) ->
    psub (pand (plift vf) (plift vx)) (vars_locs V (plift q1)).
Proof.
  intros. unfoldq. intuition.
  remember WFE as WFE1. clear HeqWFE1.
  destruct WFE as [? [? [? [? SEP]]]].
  destruct (HQF x) as [Hf_q | Hf_fr]. eauto.
  - destruct (HQX x) as [Hx_q | Hx_fr]. eauto.
    + destruct (SEP ((pand p qf)) ((pand p qx))) with (x := x).
      unfoldq. intuition.
      unfoldq. intuition.
      unfoldq. intuition.
      exists x0. intuition.
    + destruct frx. 2: contradiction.
      eapply env_type_store_wf in Hf_q; eauto. 2: {unfoldq; intuition. }
      assert False. eapply Hx_fr. eauto. contradiction.
  - destruct frf. 2: contradiction.
    destruct (HQX x) as [Hx_q | Hx_fr]. eauto.
    + eapply env_type_store_wf in Hx_q; eauto. 2: {unfoldq; intuition. }
      assert False. eapply Hf_fr. eauto. contradiction.
    + destruct frx. 2: contradiction.
      assert False. eapply Hx_fr. eapply Hf_fr. contradiction.
Qed.


(* ---------- main lemmas: semantic type assignment ---------- *)

Lemma sem_true: forall G p,
    sem_type G ttrue TBool p false pempty.
Proof.
  intros. intros S M H WFE ST.
  exists S, M, (vbool true), qempty.
  split. 2: split. 3: split. 4: split. 5: split.
  - exists 0. intros. destruct n. lia. intuition.
  - eapply stchain_refl.
  - eauto.
  - simpl. eauto.
  - unfoldq. intuition.
  - eauto.
Qed.

Lemma sem_false: forall G p,
    sem_type G tfalse TBool p false pempty.
Proof.
  intros. intros S M H WFE ST.
  exists S, M, (vbool false), qempty.
  split. 2: split. 3: split. 4: split. 5: split.
  - exists 0. intros. destruct n. lia. intuition.
  - eapply stchain_refl.
  - eauto.
  - simpl. eauto.
  - unfoldq. intuition.
  - eauto.
Qed.

Lemma sem_var: forall x G T (p:pl) fr q,
    indexr x G = Some (T, fr, q) ->
    p x ->
    sem_type G (tvar x) T p false (pone x).
Proof.
  intros. intros ? ? ? ? WFE ST.
  destruct WFE as [? [? [? [WFE ?]]]].
  destruct (WFE x T fr q H) as [vx [lsx [HQ [TL1 [TL [IH [IV [VT ?]]]]]]]].
  exists S, M, vx, lsx.
  split. 2: split. 3: split. 4: split. 5: split.
  - exists 0. intros. destruct n. lia. simpl. rewrite IH. reflexivity.
  - eapply stchain_refl.
  - eauto.
  - eauto.
  - (* valq *)
    left. unfoldq. intros. exists x; intuition.
    exists lsx. intuition.
  - intros ? Q. destruct Q as (? & P & ? & IV2 & ?).
    inversion P. congruence.
Qed.

Lemma sem_ref: forall t G p fr q,
    sem_type G t TBool p fr q ->
    sem_type G (tref t) (TRef TBool) p true q.
Proof.
  intros. intros ? ? ? ? WFE ST.
  destruct (H S M E V WFE ST) as [S1 [M1 [vx [lsx [IW1 [SC1 [ST1 [HVX [HQX HPX]]]]]]]]].
  remember (length S1) as x.
  exists (vx::S1).
  exists (st_plus (1, pone x) M1).
  exists (vref x).
  exists (qone x).
  split. 2: split. 3: split. 4: split. 5: split.
  - (* expression evaluates *)
    destruct IW1 as [n1 IW1]. rename S into St.
    exists (S n1).
    intros. destruct n. lia.
    subst x. simpl. rewrite IW1. eauto. lia.
  - unfold st_plus, st_extend in *. intuition. simpl. lia.
    simpl. unfoldq. intuition.
  - (* store typing *)
    (* lemma: storet_extend *)
    destruct ST1.
    unfold store_type in *. subst x. simpl. rewrite H0. simpl.
    intuition. simpl in H0. rewrite <-H0.
    bdestruct (l =? length S1).
    simpl in HVX. destruct vx; try contradiction. intuition eauto.
    destruct H4. inversion H4. unfoldq. congruence.
    eapply H1. eauto.
  - (* result well typed *)
    simpl. unfoldq. intuition.
  - (* qualifier *)
    (* eapply valq_fresh. *)
    intros ? Q. rewrite plift_one in Q. inversion Q. subst x0.
    right. simpl. split. left. intuition.
    intros ?.
    assert (x < length S1). eapply storet_wf. eauto.
    eapply SC1. eauto. lia.
  - intuition.
Qed.

Lemma sem_get: forall t env p fr q,
    sem_type env t (TRef TBool) p fr q ->
    sem_type env (tget t) TBool p false pempty.
Proof.
  intros. intros ? ? ? ? WFE ST.
  destruct (H S M E V WFE ST) as [S1 [M1 [vx [lsx [IW1 [SC1 [ST1 [HVX [HQX HPX]]]]]]]]].
  destruct vx; try solve [inversion HVX]. simpl in HVX.
  destruct HVX as [HVX ?].
  eapply ST1 in HVX as HVX'.
  destruct HVX' as [b SI].
  exists S1, M1, (vbool b), qempty.
  split. 2: split. 3: split. 4: split. 5: split.
  - (* expression evaluates *)
    destruct IW1 as [n1 IW1]. rename S into St.
    exists (S n1).
    intros. destruct n. lia.
    simpl. rewrite IW1. rewrite SI. eauto. lia.
  - eauto.
  - (* store type *)
    eauto.
  - (* result well typed *)
    simpl. eauto.
  - (* qualifier *)
    unfoldq. intuition.
  - intuition.
Qed.

Lemma sem_put: forall t1 t2 env p fr1 q1 fr2 q2,
    sem_type env t1 (TRef TBool) p fr1 q1 ->
    sem_type env t2 TBool p fr2 q2 ->
    sem_type env (tput t1 t2) TBool p false pempty.
Proof.
  intros. intros ? ? ? ? WFE ST.
  destruct (H S M E V WFE ST) as [S1 [M1 [vr [lsr [IW1 [SC1 [ST1 [HVR [HQR HPR]]]]]]]]].
  eapply envt_store_extend in WFE as WFE1.
  destruct (H0 S1 M1 E V WFE1 ST1) as [S2 [M2 [vx [lsx [IW2 [SC2 [ST2 [HVX [HQX HPX]]]]]]]]].
  destruct vr; try solve [inversion HVR]. simpl in HVR. destruct HVR as [HVR ?].
  destruct vx; try solve [inversion HVX]. simpl in HVX.
  assert (exists b : bool, indexr i S2 = Some (vbool b)) as HVR'.
  eapply ST2. eapply SC2. eauto.
  destruct HVR' as [b0 SI].
  exists (update S2 i (vbool b)), M2, (vbool b0), qempty.
  split. 2: split. 3: split. 4: split. 5: split.
  - (* expression evaluates *)
    rename S into St.
    destruct IW1 as [n1 IW1].
    destruct IW2 as [n2 IW2].
    exists (S (n1+n2)).
    intros. destruct n. lia.
    simpl. rewrite IW1. rewrite IW2. rewrite SI. eauto. lia. lia.
  - eapply stchain_chain; eauto.
  - (* store type *)
    destruct ST2. split.
    rewrite <-update_length. eauto.
    intros. bdestruct (i =? l).
    exists b. subst i. eapply update_indexr_hit. rewrite indexr_extend in SI. eapply SI.
    rewrite update_indexr_miss; eauto.
  - (* result well typed *)
    simpl. eauto.
  - (* qualifier *)
    unfoldq. intuition.
  - eauto.
  - eauto.
Unshelve.
  apply [].
Qed.


Lemma sem_abs: forall env t T1 T2 p fn1 fr1 q1 fn2 ar2 fr2 q2 qf,
    sem_type ((T1, fr1, (qand p (qor q1 (qif fn1 qf))))::env) t T2
      (por (pand (plift p) (plift qf)) (pone (length env)))
      fr2
      (por (plift q2) (por (pif fn2 (plift qf)) (pif ar2 (pone (length env))))) ->
    psub (plift q1) (plift p) ->  (* relax? seems necessary so far *)
    closed_ty (length env) T1 ->
    closed_ty (length env) T2 ->
    closed_ql (length env) q1 ->
    closed_ql (length env) q2 ->
    closed_ql (length env) qf ->
    sem_type env (tabs t)
      (TFun T1 fn1 fr1 q1 T2 fn2 ar2 fr2 q2)
      (plift p) false (plift qf).
Proof.
  intros. intros ? ? ? ? WFE ST.
  exists S, M. exists (vabs E t), (vars_locs_fix V (qand p qf)).
  split. 2: split. 3: split. 4: split. 5: split.
  - (* term evaluates *)
    exists 0. intros. destruct n. lia. simpl. eauto.
  - eapply stchain_refl.
  - (* store typing *)
    eauto.
  - (* result well typed *)
    simpl.

    assert (length env = length E) as LE. { symmetry. eapply WFE. }
    assert (length env = length V) as LV. { symmetry. eapply WFE. }
    assert (pdom env = pdom E) as DE. { unfold pdom. rewrite LE. eauto. }
    assert (pdom env = pdom V) as DV. { unfold pdom. rewrite LV. eauto. }

    (* rewrite DE in *. rewrite LE in *. repeat split; auto. *)
    repeat rewrite plift_vars_locs, plift_and.
    rewrite LE in *. intuition; eauto.
    eapply env_type_store_wf. eauto. unfoldq. intuition.

    (* INDUCTION *)
    destruct (H S' M' (vx::E) (lsx::V)) as [S2 [M2 [vy [lsy IHW1]]]].

    (* ENV_TYPE*)
    eapply envt_extend_full; eauto. unfoldq. intuition.

    rewrite plift_and, plift_or, plift_if. destruct fn1.
    unfoldq. intuition. unfoldq. intuition.

    unfoldq. intuition.
    destruct (H9 x) as [Q | [F | L]]. eauto. {
      rewrite plift_and, plift_or, plift_if.
      destruct Q. exists x0. unfoldq. intuition.
    } {
      destruct fn1. 2: contradiction.
      rewrite plift_and, plift_or, plift_if.
      destruct F. exists x0. unfoldq. intuition.
    } {
      destruct fr1. 2: contradiction.
      destruct L. eauto.
    }

    intros. subst fr1. intros ? ?. eapply H9 in H10.
    destruct H10 as [ A | [B | C]]. {
      eapply vars_locs_monotonic. 2: eauto.
      rewrite plift_and, plift_or. unfoldq. intuition.
    } {
      destruct fn1. 2: contradiction.
      simpl in B. eapply vars_locs_monotonic. 2: eauto.
      rewrite plift_and, plift_or. unfoldq. intuition.
    } {
      contradiction.
    }

    assert (psub (plift (qand p (qor q1 (qif fn1 qf)))) (pdom E)).
    rewrite plift_and, plift_or, plift_if. unfoldq. intuition.
    destruct fn1; eapply H5; unfoldq. eapply H10. contradiction.

    intros ? ?. eapply H10. eapply H11. eauto.

    destruct IHW1 as [? IHW1].
    exists S2, M2, vy, lsy. intuition.

    (* VAL_TYPE *)
    eapply valt_extend1; eauto.

    (* vy < vf \/ vx *)
    apply valt_wf in H8(*HVX*). apply valt_wf in H12(*HVY*).
    rename H14 into HVY.

    intros ? ?.
    destruct (HVY x) as [HY_q | HY_fr]. eauto.
    + (* q *) destruct HY_q as (? & (? & ?) & ?).
      bdestruct (x0 =? length V).
      * (* from arg *)
        subst x0. eapply var_locs_head in H18.
        right. right. left.
        destruct ar2. eauto.
        destruct H17. { eapply H4 in H17. lia. }
        destruct H17. destruct fn2. eapply H5 in H17. lia. contradiction.
        contradiction.
      * (* from func *)
        assert (x0 < length (lsx::V)). destruct H18. rewrite indexr_extend1 in H18. eapply H18. simpl in H20.
        eapply var_locs_shrink in H18; try lia.
        destruct H15. 2: { inversion H15. lia. }
        destruct H17 as [H_q2 | [H_fn2 | H_ar2]].

(*        2: { destruct ar2; inversion H17; lia. } *)

        left.
        exists x0. intuition.

        destruct fn2. 2: contradiction.
        right. left.
        exists x0. intuition.

        destruct ar2; inversion H_ar2; lia.

    + (* fr *)
      right. right. right. eapply HY_fr.

    (* VAL_QUAL *)
    - unfoldq. rewrite plift_vars_locs, plift_and. intuition.
    - intuition.
Unshelve.
  apply qempty.
Qed.


Lemma sem_app: forall env f t T1 T2 p frf qf frx qx fn1 fr1 q1 fn2 ar2 fr2 q2,
    sem_type env f (TFun T1 fn1 fr1 q1 T2 fn2 ar2 fr2 q2) p frf (plift qf)->
    sem_type env t T1 p frx (plift qx) ->
    (if fn1 then
       if fr1 then
         True
       else
         (* this case is tricky: *)
         (* qx < qf won't guarantee vx < vf!!! *)
         (* need f = tvar x0 and precisely qx = x0 *)
         (frx = false /\ (exists x0, f = tvar x0 /\ psub (plift qx) (pone x0)) \/
            frx = false /\ psub (plift qx) (plift q1))
     else
       if fr1 then
         psub (pand
                 (plift (vars_trans_fix env qf))
                 (plift (vars_trans_fix env qx)))
           (plift q1)
       else
         frx = false /\ psub (plift qx) (plift q1)) ->

    psub (plift q2) p ->   (* this is necessary (so far!) *)
    sem_type env (tapp f t) T2 p
      (fn2 && frf || ar2 && frx || fr2)
      (por (pif fn2 (plift qf)) (por (pif ar2 (plift qx)) (plift q2))).
Proof.
  intros. intros S0 ? ? ? WFE ST.
  rename H into IHW1. rename H0 into IHW2.
  destruct (IHW1 S0 M E V WFE ST) as [S1 [M1 [vf [lvf [IW1 [SC1 [ST1 [HVF [HQF HPF]]]]]]]]]. auto. auto.
  assert (env_type M1 E env V p) as WFE1. { eapply envt_store_extend; eauto. }
  destruct (IHW2 S1 M1 E V WFE1 ST1) as [S2 [M2 [vx [lvx [IW2 [SC2 [ST2 [HVX [HQX HPX]]]]]]]]].

  assert (telescope env). eapply envt_telescope. eauto.

  (* vf is a function value: it can eval its body *)
  destruct vf; try solve [inversion HVF].

  apply valt_wf in HVF as WFQF. apply valt_wf in HVX as WFQX.

  destruct HVF; intuition.
  rename H8 into HVF.
  destruct (HVF S2 M2 vx lvx) as [S3 [M3 [vy [lvy [IW3 [SC3 [ST3 [HVY HQY]]]]]]]]. eauto. eauto. eauto.

  (* SEPARATION / OVERLAP *)
  rename H1 into HSEP.
  intros ? ?.

  destruct fn1. { (* arg may overlap with function? *)
    destruct fr1. { (* arg may be fresh? *)
      (* fn, fr: anything goes *)
      assert (plift lvf x \/ ~ plift lvf x) as D. unfold plift. destruct (lvf x); eauto.
      destruct D. right. left. eauto. right. right. eauto.
    } {
      (* fn, not fr *)
      destruct HSEP as [SEP | SEP]. { (* fn *)
        destruct SEP as (? & ? & ? & A). subst f frx.
        destruct (HQX x) as [Hq | Hfr]. eauto. 2: { unfoldq. intuition. }
        right. left. eapply HPF. eapply vars_locs_monotonic. eapply A.
        eapply vars_locs_monotonic. 2: eauto. unfoldq. intuition.
      } { (* q1 *)
        destruct SEP. subst frx.
        left.
        eapply valq_sub with (q':=(pand p (plift q1))) (fr':=false) in HQX.
        destruct (HQX x) as [Hq | Hfr]. eauto. 2: contradiction.
        destruct Hq. exists x0. unfoldq. intuition.
        unfoldq. intuition. unfoldq. intuition.
        eapply H4 in H10. destruct WFE. lia.
      }
    }
  } {
    destruct fr1. {
      (* not fn, fr *)
      assert (plift lvf x \/ ~ plift lvf x) as D. unfold plift. destruct (lvf x); eauto.
      (*edestruct val_locs_decide.*) destruct D. {
        left.
        eapply overlapping. eapply WFE. eauto. eauto. eauto.
        intros ? [? ?]. eapply HSEP. split.
        rewrite plift_vt. eapply vt_mono. 2: eapply H8. unfoldq. intuition. eauto.
        rewrite plift_vt. eapply vt_mono. 2: eapply H9. unfoldq. intuition. eauto.
        unfoldq. intuition eauto.
      } {
        right. right. eauto.
      }
    } {
      (* not fn, not fr *)
      left. destruct HSEP as [? HSEP]. subst frx.
      eapply valq_sub with (q':=plift q1) (fr':=false) in HQX.
      destruct (HQX x) as [Hq | Hfr]. eauto. 2: contradiction.
      destruct Hq. exists x0. unfoldq. intuition.
      unfoldq. intuition. unfoldq. intuition.
      eapply H4 in H7. destruct WFE. lia.
    }
  }

  (* EVALUATION *)
  exists S3, M3, vy, lvy.
  split. 2: split. 3: split. 4: split. 5: split.
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

  (* STORE_EXTEND *)
  + eapply stchain_chain; eauto.
    eapply stchain_chain; eauto.

  (* STORE_TYPE *)
  + eauto.

  (* VAL_TYPE *)
  + eapply HVY.

  (* VAL_QUAL *)
  + remember (vabs l t0) as vf.
    intros ? ?. unfoldq.
    destruct (HQY  x) as [HY_q | [HY_f | [HY_x | HY_fr]]].
    repeat rewrite app_length. intuition.
    * (* q2 *)
      destruct HY_q.
      left. exists x0. intuition.
    * (* part of function *)
      destruct fn2. 2: contradiction.
      destruct (HQF x) as [HF_q | HF_fr]. eauto.
      -- (* q *) destruct HF_q.
         left. exists x0. intuition.
      -- (* fr *)
         destruct frf. 2: contradiction.
         right. destruct HF_fr; simpl.
         split. eapply SC3. eapply SC2. eauto. eauto.
    * (* part of arg *)
      destruct ar2. 2: contradiction.
      destruct (HQX x) as [HX_q | HX_fr]. eauto.
      -- (* q *) destruct HX_q.
         left. exists x0. intuition.
      -- (* fr *)
         destruct frx. 2: contradiction.
         right. destruct HX_fr.
         destruct (fn2 && frf); simpl.
         split. eapply SC3. eauto.
         intros ?. eapply H9. eapply SC1. eauto.
         split. eapply SC3. eauto.
         intros ?. eapply H9. eapply SC1. eauto.
    * (* fresh *)
      destruct fr2. 2: contradiction.
      right. destruct HY_fr.
      destruct (fn2 && frf || ar2 && frx); simpl.
      split. eauto. intros ?. eapply H9. eapply SC2. eapply SC1. eauto.
      split. eauto. intros ?. eapply H9. eapply SC2. eapply SC1. eauto.

  + eauto.
Qed.

Lemma sem_sub: forall env y T p fr1 q1 fr2 q2,
    sem_type env y T p fr1 q1 ->
    psub q1 q2 ->
    psub q2 (pdom env)  ->
    sem_type env y T p (fr1 || fr2)  q2.
Proof.
  intros. intros ? ? ? ? WFE ST.
  destruct (H S M E V WFE ST) as [S1 [M1 [vx [lvx [IW1 [SC1 [ST1 [HVX [HQX HPX]]]]]]]]].
  assert (psub q2 (pdom E)). {
    unfoldq. destruct WFE. rewrite H2. intuition. }
  exists S1, M1. exists vx, lvx.
  split. 2: split. 3: split. 4: split. 5: split.
  - eauto.
  - eauto.
  - eauto.
  - eauto.
  - unfold val_qual in HQX; intuition.
    eapply valq_sub. eauto. unfoldq. intuition. unfoldq. intuition.
    eapply H1 in H5. destruct WFE. intuition.
  - eauto.
Qed.

Lemma sem_sub_var: forall env y T p fr1 q1 Tx qx x,
    sem_type env y T p fr1 q1 ->
    q1 x ->
    indexr x env = Some (Tx, false, qx) ->
    psub (plift qx) p ->
    sem_type env y T p fr1 (por (pdiff q1 (pone x)) (plift qx)).
Proof.
  intros. rename x into z. intros ? ? ? ? WFE ST.
  destruct (H S M E V WFE ST) as [S1 [M1 [vx [lvx [IW1 [SC1 [ST1 [HVX [HQX HPX]]]]]]]]].
  exists S1, M1. exists vx, lvx. intuition.
  eapply WFE in H1 as HZ.
  intros ? ?. destruct (HQX x). eauto.
  - destruct H4. bdestruct (x0 =? z).
    + subst. destruct HZ as [vz [lvz ?]]. intuition.
      destruct H8 as (? & ? & ?). rewrite H8 in H10.
      inversion H10. subst x0.
      left. eapply vars_locs_monotonic.
      2: { eapply H12; eauto. }
      unfoldq. intuition.
    + left. exists x0. intuition. unfoldq. intuition.
  - right. intuition.
Qed.


(* ---------- semantic subtyping ---------- *)

(* NOTE: there are several variations and special cases
         mechanized below. Not all are required to prove
         the general results, but they are useful for
         experimentation (todo: clean up later).
 *)


(* sementic interpretation of qualifier subtyping. *)

Definition sem_qstp G p q1 q2 :=
  forall M E V,
    env_type M E G V p ->
    psub (vars_locs V (q1)) (vars_locs V (q2)) /\
    psub (vars_locs V (pand p q1)) (vars_locs V (pand p q2)). (* annoying split ... *)


Lemma sem_qs_sub: forall G p q1 q2,
    psub q1 q2 ->
    sem_qstp G p q1 q2.
Proof.
  intros. intros ? ? ? WFE.
  split.
  eapply vars_locs_monotonic. unfoldq. intuition.
  eapply vars_locs_monotonic. unfoldq. intuition.
Qed.

Lemma sem_qs_var: forall G p (q1:pl) Tx qx x,
    q1 x ->
    indexr x G = Some (Tx, false, qx) ->
    psub (plift qx) p ->
    sem_qstp G p q1 (por (pdiff q1 (pone x)) (plift qx)).
Proof.
  intros. intros ? ? ? WFE.
  split. {
  eapply WFE in H0.
  destruct H0 as (? & ? & ? & ?).
  intros ? Q. destruct Q as (? & ? & ?).
  bdestruct (x =? x3).
  - subst x3. intuition.
    eapply vars_locs_monotonic. 2: eapply H9.
    unfoldq. intuition.
    destruct H4. destruct H4. rewrite H7 in H4.
    inversion H4. subst. eauto.
  - exists x3. unfoldq. intuition.
    } {
  eapply WFE in H0.
  destruct H0 as (? & ? & ? & ?).
  intros ? Q. destruct Q as (? & ? & ?).
  bdestruct (x =? x3).
  - subst x3. intuition.
    eapply vars_locs_monotonic. 2: eapply H9.
    unfoldq. intuition.
    destruct H4. destruct H4. rewrite H7 in H4.
    inversion H4. subst. eauto.
  - exists x3. unfoldq. intuition.
}
Qed.

Lemma sem_qs_trans: forall G p q1 q2 q3,
    sem_qstp G p q1 q2 ->
    sem_qstp G p q2 q3 ->
    sem_qstp G p q1 q3.
Proof.
  intros. intros ? ? ? WFE.
  split.
  intros ? Q. eapply H0. eauto. eapply H. eauto. eauto.
  intros ? Q. eapply H0. eauto. eapply H. eauto. eauto.
Qed.


(* semantic interpretation of value subtyping *)

Definition sem_stpT G p T1 T2 :=
  forall S M E V,
    env_type M E G V p ->
    (* env_qual M E G (pif u q1) pempty -> *)
    (* env_accs M V (pif u q1) -> *)
    store_type S M ->
    forall v ls,
      val_type M E V v T1 ls ->
      val_type M E V v T2 ls.

Definition sem_stp0 G p T1 (fr1:bool) q1 T2 (fr2:bool) q2 :=
  forall S M E V lp,
    env_type M E G V p ->
    (* env_qual M E G (pif u q1) pempty -> *)
    (* env_accs M V (pif u q1) -> *)
    store_type S M ->
    forall v ls,
      val_type M E V v T1 ls ->
      psub (plift ls) (por (vars_locs V q1) lp) ->
      val_type M E V v T2 ls /\
      psub (plift ls) (por (vars_locs V q2) lp)
.

Definition sem_stp0_precise G p T1 (fr1:bool) q1 T2 (fr2:bool) q2 :=
  forall S M E V,
    env_type M E G V p ->
    (* env_qual M E G (pif u q1) pempty -> *)
    (* env_accs M V (pif u q1) -> *)
    store_type S M ->
    forall v ls,
      val_type M E V v T1 ls ->
      psub (plift ls) (vars_locs V q1) ->
      val_type M E V v T2 ls /\
      psub (plift ls) (vars_locs V q2)
.

Definition sem_stp1 G p T1 fr1 q1 T2 fr2 q2 :=
  forall S M E V lp,
    env_type M E G V p ->
    (* env_qual M E G (pif u q1) pempty -> *)
    (* env_accs M V (pif u q1) -> *)
    store_type S M ->
    forall v ls ls',
      val_type M E V v T1 ls ->
      psub (plift ls) (por (vars_locs V q1) (pif fr1 lp)) ->
      plift ls' = por (plift ls) (vars_locs V (pand p q2)) ->
      val_type M E V v T2 ls' /\
      psub (plift ls') (por (vars_locs V q2) (pif fr2 lp)).

Definition sem_stp1_precise G p T1 (fr1:bool) q1 T2 (fr2:bool) q2 :=
  forall S M E V,
    env_type M E G V p ->
    (* env_qual M E G (pif u q1) pempty -> *)
    (* env_accs M V (pif u q1) -> *)
    store_type S M ->
    forall v ls ls',
      val_type M E V v T1 ls ->
      psub (plift ls) (vars_locs V q1) ->
      plift ls' = por (plift ls) (vars_locs V (pand p q2)) ->
      val_type M E V v T2 ls' /\
      psub (plift ls') (vars_locs V q2).

Definition sem_stp2 G p grow T1 fr1 q1 T2 fr2 q2 := (* this one is the most general *)
  forall S M E V lp,
    env_type M E G V p ->
    (* env_qual M E G (pif u q1) pempty -> *)
    (* env_accs M V (pif u q1) -> *)
    store_type S M ->
    forall v ls,
      val_type M E V v T1 ls ->
      psub (plift ls) (por (vars_locs V q1) (pif fr1 lp)) ->
      exists ls',
      val_type M E V v T2 ls' /\
      psub (plift ls') (por (vars_locs V q2) (pif fr2 lp)) /\
      psub (plift ls) (plift ls') /\
      (grow = false -> psub (plift ls') (plift ls))
.


Lemma stp_upT: forall G p T1 T2 q1 q2 fr1 fr2,
    sem_stpT G p T1 T2 ->
    sem_qstp G p q1 q2 ->
    sem_stp0 G p T1 (fr1:bool) q1 T2 (fr2:bool) q2.
Proof.
  intros. intros ? ? ? ? ? WFE (* WFQ WFX *) ST vf lf HVF HQF.
  split. eauto.
  intros ? Q. eapply HQF in Q. destruct Q.
  left. eapply H0; eauto. right. eauto.
Qed.


Lemma stp_up2: forall G p gr T1 T2 q1 q2 fr1 fr2,
    sem_stp0 G p T1 (fr1:bool) q1 T2 (fr2:bool) q2 ->
    bsub fr1 fr2 ->
    sem_stp2 G p gr T1 (fr1:bool) q1 T2 (fr2:bool) q2.
Proof.
  intros. intros ? ? ? ? ? WFE (* WFQ WFX *) ST vf lf HVF HQF.
  exists lf. intuition.
  eapply H; eauto.
  eapply H; eauto. intros ? Q. eapply HQF in Q. destruct Q. left. eauto.
  destruct fr1. rewrite H0. right. eauto. eauto. contradiction.
  unfoldq. intuition.
  unfoldq. intuition.
Qed.



(* prerequisite: when can we grow the set of locations of a function value?

   - no self ref: no problem
   - self ref in the result type: covariant, no problem
   - self ref in the argument type: contravariant, need to be careful:
     - if the argument type is fresh, we can grow it!

       A^f* -> B  <:  A^f -> B

*)
Lemma valt_locs_sub: forall T1 T2 M E V v ls ls'
                  q1fn_a q1fr_a q1a q2fn_a q2ar_a q2fr_a q2a
                  q1fn_b q1fr_b q1b,
    val_type M E V v (TFun T1 q1fn_a q1fr_a q1a T2 q2fn_a q2ar_a q2fr_a q2a) ls ->
    psub (plift ls) (plift ls') ->
    psub (plift ls') (st_locs M) ->
    (q1fn_b = true ->
       q1fr_a = true /\ (q1fn_a = true \/ ls = qempty) \/
       psub (plift ls') (vars_locs V (plift q1a))) ->
    bsub q1fr_b q1fr_a ->
    psub (vars_locs V (plift q1b)) (vars_locs V (plift q1a)) ->
    psub (plift q1b) (pdom E) ->
    val_type M E V v (TFun T1 q1fn_b q1fr_b q1b T2 q2fn_a q2ar_a q2fr_a q2a) ls'.
Proof.
  intros. destruct v; simpl in *; intuition.
  destruct (H11 S' M' vx lsx) as (S'' & M'' & vy & lsy & ? & ? & ? & ? & ?).
  + eauto.
  + eauto.
  + eauto.
  + intros ? Q. eapply H14 in Q. destruct Q as [H_q1 | [H_fn | H_fr]].
    * left. eauto.
    * destruct q1fn_b. 2: contradiction.
      destruct H2 as [H_fr | H_q1]. eauto.
      -- right. destruct H_fr as [R1 R2].
         assert (plift ls x \/ pnot (plift ls) x) as C. unfold pnot,plift. destruct (ls x); eauto.
         destruct C.
         ++ destruct R2.
            ** subst. left. eauto.
            ** subst. rewrite plift_empty in *. contradiction.
         ++ subst. right. eauto.
      -- left. eauto.
    * destruct q1fr_b. 2: contradiction.
      right. right. rewrite H3; eauto. intros ?. eapply H_fr. eauto.
  + exists S'', M'', vy, lsy. intuition.
    intros ? Q. eapply H19 in Q. destruct Q as [H_q2 | [H_vf | [H_vx | H_fr]]].
    * left. eapply H_q2.
    * destruct q2fn_a. 2: contradiction.
      right. left. eapply H0. eauto.
    * right. right. left. eauto.
    * right. right. right. eauto.
Qed.

Lemma sem_stp_fun0: forall G p T1a T2a T1b T2b qfa qfb
                          q1fn_a q1fr_a q1a q2fn_a q2ar_a q2fr_a qffr_a q2a
                          q1fn_b q1fr_b q1b q2fn_b q2ar_b q2fr_b qffr_b q2b,
    sem_stp0 G p T1b q1fr_b (plift q1b) T1a q1fr_a (plift q1a) ->
    sem_stp0 G p T2a q2fr_a (plift q2a) T2b q2fr_b (plift q2b) ->
    (* --- regular sub-qualifier rules --- *)
    (* arg *)
    bsub q1fn_b q1fn_a ->
    bsub q1fr_b q1fr_a ->
    (* res *)
    bsub q2fn_a q2fn_b ->
    bsub q2ar_a q2ar_b ->
    bsub q2fr_a q2fr_b ->
    (* fun *)
    bsub qffr_a qffr_b ->
    sem_qstp G p qfa qfb ->
    (* --- closedness --- *)
    closed_ty (length G) T1b ->
    psub (plift q1b) (pdom G) ->
    closed_ty (length G) T2b ->
    psub (plift q2b) (pdom G) ->
    (* --- result --- *)
    sem_stp0 G p
      (TFun T1a q1fn_a q1fr_a q1a T2a q2fn_a q2ar_a q2fr_a q2a) qffr_a qfa
      (TFun T1b q1fn_b q1fr_b q1b T2b q2fn_b q2ar_b q2fr_b q2b) qffr_b qfb.
Proof.
  intros. intros ? ? ? ? ? WFE (* WFQ WFX *) ST vf lf HVF.

  specialize H as STX. (* specialize (H S M E V) as STX. *)
  specialize H0 as STY. (* specialize (H0 S M E V) as STY. *)

  destruct vf; try solve [inversion HVF].

  assert (length G = length E) as L. symmetry. eapply WFE.
  assert (pdom G = pdom E) as PD. unfoldq. rewrite L. eauto.

  destruct HVF; intuition.
  rename H19 into HVF.
  simpl. intuition.

  - rewrite <-L. eauto.
  - rewrite <-PD. eauto.
  - rewrite <-L. eauto.
  - rewrite <-PD. eauto.

  - destruct (HVF S' M' vx lsx) as (S'' & M'' & vy & lsy & ? & ? & ? & ? & ?).
    + eauto.
    + eauto.
    + (* transform argument value *)
      eapply STX; eauto.
      eapply envt_store_extend. eauto. eauto.
    + eapply STX. 2,3: eauto.
      eapply envt_store_extend. eauto. eauto.
      intros ? Q. eapply H21 in Q. destruct Q as [H_q1 | [H_vf | H_fr]].
      -- left. eauto.
      -- right. left. destruct q1fn_b. 2: contradiction. rewrite H1; eauto.
      -- right. right. destruct q1fr_b. 2: contradiction. rewrite H2; eauto.
    + exists S'', M'', vy, lsy.
      split. 2: split. 3: split. 4: split.
      * eauto.
      * eauto.
      * eauto.
      * (* transform result value *)
        eapply STY; eauto.
        eapply envt_store_extend. eauto. eapply stchain_chain; eauto.
      * eapply STY. 2,3: eauto.
        eapply envt_store_extend. eauto. eapply stchain_chain; eauto.
        intros ? Q. eapply H26 in Q. destruct Q as [H_q2 | [H_vf | [H_vx | H_fr]]].
        -- left. eauto.
        -- right. left. destruct q2fn_a. 2: contradiction. rewrite H3; eauto.
        -- right. right. left. destruct q2ar_a. 2: contradiction. rewrite H4; eauto.
        -- right. right. right. destruct q2fr_a. 2: contradiction. rewrite H5; eauto.
  - intros ? Q. eapply H14 in Q. destruct Q as [H_q | H_fr].
    -- left. eapply H7; eauto.
    -- right. eauto.
Qed.

Lemma sem_stp_fun2: forall G p T1a T2a T1b T2b qfa qfb gr1 gr2 grf
                          q1fn_a q1fr_a q1a q2fn_a q2ar_a q2fr_a qffr_a q2a
                          q1fn_b q1fr_b q1b q2fn_b q2ar_b q2fr_b qffr_b q2b,
    sem_stp2 G p gr1 T1b (q1fn_b || q1fr_b) (plift q1b) T1a (q1fn_a || q1fr_a) (plift q1a) ->
    sem_stp2 G p gr2 T2a (q2fn_a || q2ar_a || q2fr_a) (plift q2a) T2b (q2fn_b || q2ar_b || q2fr_b) (plift q2b) ->
    (* --- regular sub-qualifier rules --- *)
    (* arg *)
    bsub q1fn_b q1fn_a ->
    bsub q1fr_b q1fr_a ->
    (* res *)
    (q2fn_a = true ->       (* reach function? either: *)
       q2fn_b = true \/     (* - keep *)
       sem_qstp G p (plift qfa) (plift q2b) /\ qffr_a = false  (* - resolve func qual, if not fresh *)
    ) ->
    (*bsub q2ar_a q2ar_b*)
    (q2ar_a = true ->      (* reach argument? *)
      (gr1 = true ->       (*   can it grow? *)
        (sem_qstp G p (plift q1a) (plift q2b) \/   (* covered by q2 *)
          q2fn_b = true /\ grf = true /\ sem_qstp G p (plift q1a) (plift qfb))) /\  (* covered by qf, function grows as well *)
      (gr1 = false ->      (*   not growing *)
        (q2ar_b = true \/  (*     keep arg *)
           sem_qstp G p (plift q1b) (plift q2b))) /\ (* expand qualifier *)
      (q1fn_b = true -> q2ar_b = true \/ q2fn_b = true) /\
      (q1fr_b = true -> q2ar_b = true)
    ) ->
    bsub q2fr_a q2fr_b ->
    (* fun *)
    bsub qffr_a qffr_b ->
    sem_qstp G p (plift qfa) (plift qfb) ->
    (* --- constraints --- *)
    (grf = true ->
     q1fn_b = true ->
     q1fr_a = true /\
       q1fn_a = true (* \/ ...
       sem_qstp G p (plift qfb) (plift q1a) *)
    ) ->
    True ->
    True ->
    True ->
    (* --- closedness --- *)
    closed_ty (length G) T1b ->
    psub (plift q1b) (pdom G) ->
    closed_ty (length G) T2b ->
    psub (plift q2b) (pdom G) ->
    psub (plift qfb) (pdom G) ->
    (* --- result --- *)
    sem_stp2 G p grf
      (TFun T1a q1fn_a q1fr_a q1a T2a q2fn_a q2ar_a q2fr_a q2a) qffr_a (plift qfa)
      (TFun T1b q1fn_b q1fr_b q1b T2b q2fn_b q2ar_b q2fr_b q2b) qffr_b (plift qfb).
Proof.
  intros. intros ? ? ? ? ? WFE (* WFQ WFX *) ST vf lf HVF.

  rename H into STX. (* specialize (H S M E V) as STX. *)
  rename H0 into STY. (* specialize (H0 S M E V) as STY. *)

  rename H1 into BS_Q1FN.
  rename H2 into BS_Q1FR.
  rename H3 into BS_Q2FN.
  rename H4 into BS_Q2AR.
  rename H5 into BS_Q2FR.
  rename H6 into BS_QFFR.
  rename H7 into QS_QF.
  rename H8 into GRF_Q1FN.
    
  destruct vf; try solve [inversion HVF].

  assert (length G = length E) as L. symmetry. eapply WFE.
  assert (pdom G = pdom E) as PD. unfoldq. rewrite L. eauto.

  destruct HVF; intuition.
  rename H6 into HVF.

  exists (qor lf (qif grf (vars_locs_fix V qfb))).

  simpl. intuition.

  - rewrite <-L. eauto.
  - rewrite <-PD. eauto.
  - rewrite <-L. eauto.
  - rewrite <-PD. eauto.
  - rewrite plift_or, plift_if, plift_vars_locs.
    intros ? Q. destruct Q. eauto.
    destruct grf. 2: contradiction.
    eapply env_type_store_wf2; eauto.

  - edestruct STX as (lsx' & HVX & HQX & HGX & HGX'). 2,3:eauto.
    eapply envt_store_extend. eauto. eauto. {
      intros ? Q. 

      eapply H8 in Q as Q1. destruct Q1 as [H_q1 | H_rest].
      -- left. eauto.
      -- right. remember (q1fn_b || q1fr_b) as C. destruct C.
         assert ((pand (plift lsx) (por
           (pif q1fn_b (plift (qor lf (qif grf (vars_locs_fix V qfb)))))
           (pif q1fr_b
              (pnot (plift (qor lf (qif grf (vars_locs_fix V qfb)))))))) x) as QQ. 
         split. eauto. eauto.
         eapply QQ. (* eapply H_rest. *)
         destruct q1fn_b; destruct q1fr_b; destruct H_rest; inversion HeqC; try contradiction. }

    destruct (HVF S' M' vx lsx') as (S'' & M'' & vy & lsy & ? & ? & ? & ? & ?).
    + eauto.
    + eauto.
    + (* transform argument value *)
      eauto.
    + intros ? Q. eapply HQX in Q. destruct Q as [H_q1 | H_rest].
      -- left. eauto.
      -- remember (q1fn_a || q1fr_a) as C. destruct C. 2: contradiction.
         destruct H_rest as [A B]. 
         destruct B as [H_vf | H_fr].
         ** destruct q1fn_b. 2: contradiction. rewrite BS_Q1FN; eauto.
            rewrite plift_or, plift_if, plift_vars_locs in H_vf.
            destruct H_vf. right. left. eauto.
            destruct grf. 2: contradiction.
            destruct GRF_Q1FN. eauto. eauto. subst.
            assert (plift lf x \/ pnot (plift lf) x) as C. unfold pnot, plift. destruct (lf x); intuition. destruct C.
            right. left. eauto. right. right. eauto. 
         ** destruct q1fr_b. 2: contradiction. rewrite BS_Q1FR; eauto.
            rewrite plift_or, plift_if, plift_vars_locs in H_fr.
            right. right. intros Q. eapply H_fr. left. eauto.

    + edestruct STY as (lsy' & HVY & HQY & HGY & HGY'). 2,3:eauto.
      eapply envt_store_extend. eauto. eapply stchain_chain; eauto. {
        intros ? Q. eapply H21 in Q. destruct Q as [H_q2 | H_rest].
        -- left. eauto.
        -- right. remember (q2fn_a || q2ar_a || q2fr_a) as C. destruct C. eapply H_rest.
           destruct q2fn_a; destruct q2ar_a; destruct q2fr_a; destruct H_rest as [A | [B | C]]; inversion HeqC; try contradiction. }
      exists S'', M'', vy, lsy'.
      split. 2: split. 3: split. 4: split.
      * eauto.
      * eauto.
      * eauto.
      * (* transform result value *)
        eauto.
      * intros ? Q. eapply HQY in Q. destruct Q as [H_q2 | H_rest].
        -- left. eauto.
        -- remember (q2fn_b || q2ar_b || q2fr_b) as C. destruct C. 2: contradiction.
           destruct H_rest as [H_fn | [H_ar | H_fr]].
           ++ (* q2fn_a -> q1fn_b \/ qfa <: q2b /\ !qffr *)
              destruct q2fn_a. 2: contradiction.
              destruct BS_Q2FN as [A | [A B]]. eauto. 
              ** rewrite A. right. left. rewrite plift_or, plift_if, plift_vars_locs. left. eauto.
              ** eapply H1 in H_fn. destruct H_fn.
                 left. eapply A; eauto.
                 rewrite B in H22. contradiction.
           ++ destruct q2ar_a. 2: contradiction.
              destruct gr1.
              ** destruct BS_Q2AR as [A [B [C D]]]. eauto. 
                 eapply HQX in H_ar. destruct H_ar.
                 +++ destruct A as [A | [A1 [A2 A3]]]. eauto. 
                     left. eapply A. eauto. eauto.
                     right. left. rewrite A1, A2.
                     rewrite plift_or, plift_if, plift_vars_locs. right.
                     eapply A3. eauto. eauto. 
                 +++ destruct (q1fn_a || q1fr_a). 2: contradiction.
                     destruct H22. destruct H23. 
                     *** destruct q1fn_b. 2: contradiction. destruct C. eauto.
                         right. right. left. rewrite H24. eauto.
                         right. left. rewrite H24. eauto.
                     *** destruct q1fr_b. 2: contradiction.
                         rewrite D. right. right. left. eauto. eauto.
              ** eapply HGX' in H_ar. 2: eauto.
                 destruct BS_Q2AR as [A B]. eauto. destruct B as [B  [C D]]. eauto.
                 eapply H8 in H_ar as H_A. destruct H_A as [U | [W | X]].
                 +++ destruct B as [B|B]. eauto. 
                     rewrite B. right. right. left. eauto.
                     left. eapply B; eauto. 
                 +++ destruct q1fn_b. 2: contradiction. destruct C. eauto. 
                     *** right. right. left. rewrite H22. eauto.
                     *** right. left. rewrite H22. eauto. 
                 +++ destruct q1fr_b. 2: contradiction.
                     rewrite D. eauto. right. right. left. eauto. eauto. 
                                       
           ++ right. right. right. destruct q2fr_a. 2: contradiction. rewrite BS_Q2FR; eauto.
  - rewrite plift_or, plift_if, plift_vars_locs.
    intros ? Q. destruct Q as [Q|Q]. eapply H1 in Q. destruct Q as [H_q | H_fr].
    -- left. eapply QS_QF; eauto.
    -- right. destruct qffr_a. 2: contradiction. rewrite BS_QFFR; eauto.
    -- left. destruct grf. 2: contradiction. eauto.
  - subst. rewrite plift_or, plift_if. intros ? Q. left. eauto.
  - subst. rewrite plift_or, plift_if. intros ? [Q|Q]. eauto. contradiction.
Qed.




Lemma sem_stp_fun_refl: forall G p T1a T2a T1b T2b
                                         q1fn_a q1fr_a q1a q2fn_a q2ar_a q2fr_a q2a
                                         qffr_a qfa,
    (* --- closedness -- *)
    closed_ty (length G) T1b ->
    closed_ty (length G) T2b ->
    sem_stp0 G p
      (TFun T1a q1fn_a q1fr_a q1a T2a q2fn_a q2ar_a q2fr_a q2a) qffr_a qfa
      (TFun T1a q1fn_a q1fr_a q1a T2a q2fn_a q2ar_a q2fr_a q2a) qffr_a qfa.
Proof.
  intros. intros ? ? ? ? ? WFE (* WFQ WFX *) ST vf lf HVF.

  specialize H as STX. (* specialize (H S M E V) as STX. *)
  specialize H0 as STY. (* specialize (H0 S M E V) as STY. *)

  destruct vf; try solve [inversion HVF].

  assert (length G = length E) as L. symmetry. eapply WFE.
  assert (pdom G = pdom E) as PD. unfoldq. rewrite L. eauto.

  destruct HVF; intuition.
  rename H8 into HVF.
  simpl. intuition.
Qed.


(*

If a separate from q (needs q non-fresh) then:

        (A^* -> B)^q  <:  (A^a -> B)^q

It's possible to treat a fresh-arg function as one taking arg a,
as long as a is separate from the function.

(Proved here for q = 0)

*)


Lemma sem_stp_fun_arg_change_fresh_to_qual: forall G p T1a T2a T1b T2b
                                         q1fn_a (*q1fr_a*) (*q1a*) q2fn_a q2ar_a q2fr_a q2a
                                         q1b qffr_a qfa,
    (* --- closedness -- *)
    closed_ty (length G) T1b ->
    psub (plift q1b) (pdom G) ->
    closed_ty (length G) T2b ->
    (* todo: any qf that doesn't overlap with q1b is fine *)
    qfa = pempty ->
    sem_stp0_precise G p
      (TFun T1a q1fn_a true qempty T2a q2fn_a q2ar_a q2fr_a q2a) false qfa
      (TFun T1a q1fn_a false q1b   T2a q2fn_a q2ar_a q2fr_a q2a) qffr_a qfa.
Proof.
  intros. intros ? ? ? ? WFE (* WFQ WFX *) ST vf lf HVF.

  specialize H as STX. (* specialize (H S M E V) as STX. *)
  specialize H0 as STY. (* specialize (H0 S M E V) as STY. *)

  destruct vf; try solve [inversion HVF].

  assert (length G = length E) as L. symmetry. eapply WFE.
  assert (pdom G = pdom E) as PD. unfoldq. rewrite L. eauto.

  destruct HVF; intuition.
  rename H10 into HVF.
  simpl. intuition.

  - rewrite <-PD. eauto.

  - destruct (HVF S' M' vx lsx) as (S'' & M'' & vy & lsy & ? & ? & ? & ? & ?).
    + eauto.
    + eauto.
    + eauto.
    + intros ? Q. eapply H12 in Q. destruct Q as [H_q1 | [H_vf | H_fr]].
      * right. right. intros Q. eapply H5 in Q. subst qfa.
        destruct Q as (? & ? & ?). contradiction.
      * right. left. eauto.
      * contradiction.
    + exists S'', M'', vy, lsy.
      split. 2: split. 3: split. 4: split.
      * eauto.
      * eauto.
      * eauto.
      * eauto.
      * eauto.
Qed.

Lemma sem_stp_fun_arg_drop_self: forall G p T1a T2a T1b T2b
                                         (*q1fn_a*) q1fr_a q1a q2fn_a q2ar_a q2fr_a q2a
                                         false qfa,
    (* --- closedness -- *)
    closed_ty (length G) T1b ->
    psub (plift q1a) (pdom G) ->
    closed_ty (length G) T2b ->
    sem_stp0 G p
      (TFun T1a true  q1fr_a q1a T2a q2fn_a q2ar_a q2fr_a q2a) false (plift qfa)
      (TFun T1a false q1fr_a q1a T2a q2fn_a q2ar_a q2fr_a q2a) false (plift qfa).
Proof.
  intros. intros ? ? ? ? ? WFE (* WFQ WFX *) ST vf lf HVF.

  specialize H as STX. (* specialize (H S M E V) as STX. *)
  specialize H0 as STY. (* specialize (H0 S M E V) as STY. *)

  destruct vf; try solve [inversion HVF].

  assert (length G = length E) as L. symmetry. eapply WFE.
  assert (pdom G = pdom E) as PD. unfoldq. rewrite L. eauto.

  destruct HVF; intuition.
  rename H9 into HVF.
  simpl. intuition.

    - destruct (HVF S' M' vx lsx) as (S'' & M'' & vy & lsy & ? & ? & ? & ? & ?).
    + eauto.
    + eauto.
    + eauto.
    + intros ? Q. eapply H11 in Q. destruct Q as [H_q1 | [H_vf | H_qfr]].
      * left. eauto.
      * remember false as F. destruct F. right. left. eauto. contradiction. (* weird *)
      * right. right. eauto.
    + exists S'', M'', vy, lsy.
      split. 2: split. 3: split. 4: split.
      * eauto.
      * eauto.
      * eauto.
      * eauto.
      * eauto.
Qed.

(* we've removed q2 < qf -- now need sem_stp1 *)

Lemma sem_stp_fun_res_change_qual_to_self: forall G p T1a T2a T1b T2b
                                         q1fn_a q1fr_a q1a q2fn_a q2ar_a q2fr_a q2a
                                         qffr_a qfa,
    (* --- closedness -- *)
    closed_ty (length G) T1b ->
    closed_ty (length G) T2b ->
    psub (plift q2a) (pand p qfa) ->
    (q1fn_a = true -> q1fr_a = true \/ psub (qfa) (plift q1a)) ->
    sem_stp1 G p
      (TFun T1a q1fn_a q1fr_a q1a T2a q2fn_a    q2ar_a q2fr_a q2a        ) qffr_a qfa
      (TFun T1a q1fn_a q1fr_a q1a T2a true(*!*) q2ar_a q2fr_a qempty(*!*)) qffr_a qfa.
Proof.
  intros. intros ? ? ? ? ? WFE (* WFQ WFX *) ST vf lf lf' HVF HQF AQ.

  specialize H as STX. (* specialize (H S M E V) as STX. *)
  specialize H0 as STY. (* specialize (H0 S M E V) as STY. *)

  destruct vf; try solve [inversion HVF].

  assert (length G = length E) as L. symmetry. eapply WFE.
  assert (pdom G = pdom E) as PD. unfoldq. rewrite L. eauto.

  destruct HVF; intuition.
  rename H9 into HVF.
  simpl. intuition.

  - unfoldq. intuition.
  - rewrite AQ. intros ? Q. destruct Q. eauto. eapply env_type_store_wf; eauto. unfoldq. intuition.
  - destruct (HVF S' M' vx lsx) as (S'' & M'' & vy & lsy & ? & ? & ? & ? & ?).
    + eauto.
    + eauto.
    + eauto.
    + intros ? Q. eapply H11 in Q. destruct Q as [H_q1 | [H_fn | H_fr]].
      * left. eauto.
      * destruct q1fn_a. 2: contradiction.
        destruct H2 as [H_fr | H_q1]; eauto.
        assert (plift lf x \/ pnot (plift lf) x) as C. unfold pnot,plift. destruct (lf x); eauto.
        destruct C. subst. right. left. eauto. right. right. subst. eauto.
        rewrite AQ in H_fn. destruct H_fn.
        right. left. eauto. left. eapply vars_locs_monotonic. 2: eauto. unfoldq. intuition.
      * right. right. destruct q1fr_a. 2: contradiction.
        intros Q. eapply H_fr. rewrite AQ. left. eauto.
    + exists S'', M'', vy, lsy.
      split. 2: split. 3: split. 4: split.
      * eauto.
      * eauto.
      * eauto.
      * eauto.
      * intros ? Q. eapply H16 in Q. destruct Q as [H_q2 | [H_fn | [H_ar | H_fr]]].
        -- right. left. rewrite AQ. right. eapply vars_locs_monotonic. 2: eauto. unfoldq. intuition.
        -- destruct q2fn_a. 2: contradiction.
           right. left. rewrite AQ. left. eauto.
        -- right. right. left. eauto.
        -- right. right. right. eauto.
  - rewrite AQ. intros ? Q. destruct Q as [H_vf | H_qf].
    + eauto.
    + left. eapply vars_locs_monotonic. 2: eauto. unfoldq. intuition.
Qed.



(* change result to self if result mentions argument: *)

(*    x:A^a -> A^x   <:  x:A^a -> A^f)  where a non-fresh  *)

(* works now, without q2 < qf *)

Lemma sem_stp_fun_res_change_arg_to_self: forall G p T1a T2a T1b T2b
                                         q1fn_a (*q1fr_a*) q1a q2fn_a (*q2ar_a*) q2fr_a q2a
                                         qffr_a qfa,
    (* --- closedness -- *)
    closed_ty (length G) T1b ->
    closed_ty (length G) T2b ->
    (* TODO: currently we require q1a = 0 ! *)
    sem_stp0 G p
      (TFun T1a q1fn_a false q1a T2a q2fn_a             true  q2fr_a q2a) qffr_a qfa
      (TFun T1a q1fn_a false q1a T2a (q2fn_a || q1fn_a) false q2fr_a (qor q2a q1a)) qffr_a qfa.
Proof.
  intros. intros ? ? ? ? ? WFE (* WFQ WFX *) ST vf lf HVF.

  specialize H as STX. (* specialize (H S M E V) as STX. *)
  specialize H0 as STY. (* specialize (H0 S M E V) as STY. *)

  destruct vf; try solve [inversion HVF].

  assert (length G = length E) as L. symmetry. eapply WFE.
  assert (pdom G = pdom E) as PD. unfoldq. rewrite L. eauto.

  destruct HVF; intuition.
  rename H8 into HVF.
  simpl. intuition.

  - rewrite plift_or. unfoldq. intuition.

  - destruct (HVF S' M' vx lsx) as (S'' & M'' & vy & lsy & ? & ? & ? & ? & ?).
    + eauto.
    + eauto.
    + eauto.
    + eauto.
    + exists S'', M'', vy, lsy.
      split. 2: split. 3: split. 4: split.
      * eauto.
      * eauto.
      * eauto.
      * eauto.
      * intros ? Q. eapply H15 in Q. destruct Q as [H_q2 | [H_fn | [H_ar | H_fr]]].
        -- left. rewrite plift_or.
           eapply vars_locs_monotonic. 2: eauto. unfoldq. intuition.
        -- right. left. destruct q2fn_a. 2: contradiction. simpl. eauto.
        -- eapply H10 in H_ar. destruct H_ar as [H_q1 | [H_fn | H_fr]].
           ++ left. rewrite plift_or.
              eapply vars_locs_monotonic. 2: eauto. unfoldq. intuition.
           ++ destruct q1fn_a. 2: contradiction.
              right. left. simpl. rewrite orb_comm. eauto.
           ++ contradiction.
        -- right. right. right. eauto.
Qed.



(*

Instantiate a fresh-arg function with a concrete argument type,
introducing a function self type:

(1)
        A^f* -> A^x   ^q
    <:  A^a  -> A^f   ^q,a

Specialized version if initial function qualifier is empty:

(2)
        A^* -> A^x   ^0
    <:  A^a -> A^f   ^a

Other possible variants (not covered here, but below):

(3) Add qualifier directly to the result type:

        A^* -> A^x   ^0
    <:  A^a -> A^a   ^0

(4) Keep result dependency on arg:

        A^* -> A^x   ^0
    <:  A^a -> A^x   ^0


*)


Lemma sem_stp_fun_fresh_arg_to_self: forall G p T1a T1b T2 fr1 fr2 q1 q2
                                            q1b q1a
                                            q1fn_a q2ar_a q2fn_a q2ar_b,
    closed_ty (length G) T2 ->
    closed_ty (length G) T1b ->
    psub (plift q1b) (pdom G) ->
    psub (plift q1a) p ->
    psub (plift q1) (plift q2) ->
    (q2ar_a = true -> psub (plift q1a) (plift q2)) -> (* only needed when switching x -> f *)
    sem_stp2 G p true T1b false (plift q1b) T1a false (*fr2*) (plift q1a) ->  (*  A2^u  -> A1^a  *)
    (q1fn_a = true \/ fr1 = false /\ q1 = qempty) ->
    bsub fr1 fr2 ->
    True ->
    sem_stp2 G p q2ar_a (* grow when switching x -> f *)
      (TFun T1a q1fn_a true qempty T2 q2fn_a(*false*) q2ar_a(*true*) false qempty) fr1 (plift q1) (*  A1^f* -> B^x  q1    *)
      (TFun T1b false false q1b T2 true q2ar_b false qempty) fr2 (plift q2).  (*  A2^u  -> B^f  q1,a  *)
Proof.
  intros. intros ? ? ? ? ? WFE (* WFQ WFX *) ST vf lf. intros HVF HQF.

  rename H5 into STX. (* specialize (H S M E V) as STX. *)
  (* specialize H0 as STY. (* specialize (H0 S M E V) as STY. *) *)
  rename H6 into HGF.

  destruct vf; try solve [inversion HVF].

  assert (length G = length E) as L. symmetry. eapply WFE.
  assert (pdom G = pdom E) as PD. unfoldq. rewrite L. eauto.

  eexists (qor lf (qif q2ar_a (vars_locs_fix V q1a))).

  destruct HVF as (? & ? & ? & ? & ? & HVF).
  split. 2: split.
  simpl.
  split. 2: split. 3: split. 4: split. 5: split.

  - rewrite <-L. eauto.
  - rewrite <-PD. eauto.
  - intuition.
  - intuition.

  - rewrite plift_or, plift_if, plift_vars_locs. intros ? Q. destruct Q. eauto.
    eapply env_type_store_wf. eauto. 2: eauto. eauto.
    destruct q2ar_a. 2: contradiction. eauto. 

  - intros ? ? ? ? ? ? HVX HQX.
    edestruct STX as (lsx' & HVX' & HQX' & HGX).
    3: eapply HVX.
    eapply envt_store_extend. eauto. eauto. eauto. {
      intros ? Q. eapply HQX in Q. destruct Q as [H_q1 | H_rest].
      -- left. rewrite plift_empty in *. eauto.
      -- destruct H_rest. contradiction. contradiction. }

    destruct (HVF S' M' vx lsx') as (S'' & M'' & vy & lsy & ? & ? & ? & ? & HQY).
    + eauto.
    + eauto.
    + (* transform argument value *)
      eauto.
    + intros ? Q. eapply HQX' in Q.
      assert (plift lf x \/ pnot (plift lf) x) as C. unfold pnot,plift. destruct (lf x); eauto.
      destruct C as [C|C].
      * destruct q1fn_a.
        -- right. left. eauto.
        -- eapply HQF in C. destruct HGF as [HGF|HGF]. inversion HGF. destruct HGF. subst.
           destruct C. left. eauto. (* contra *) contradiction.
      * right. right. eauto.

    + exists S'', M'', vy, lsy.
      split. 2: split. 3: split. 4: split.
      * eauto.
      * eauto.
      * eauto.
      * eauto.
      * intros ? Q. eapply HQY in Q. destruct Q as [H_q2 | [H_fn | [H_ar | H_fr]]].
        -- left. eauto.
        -- right. left. destruct q2fn_a. 2: contradiction.
           rewrite plift_or. left. eauto. 
        -- right. left. destruct q2ar_a. 2: contradiction.
           rewrite plift_or, plift_if, plift_vars_locs.
           eapply HQX' in H_ar. destruct H_ar. right. eauto. contradiction.
        -- right. right. right. eauto.
  - rewrite plift_or, plift_if, plift_vars_locs. intros ? Q. destruct Q.
    eapply HQF in H12. destruct H12. left.
    eapply vars_locs_monotonic. 2: eauto. unfoldq. intuition.
    right. destruct fr1. 2: contradiction. rewrite H7. eauto. eauto.
    left. destruct q2ar_a. 2: contradiction. eapply vars_locs_monotonic. 2: eauto. unfoldq. intuition.
  - rewrite plift_or, plift_if, plift_vars_locs.
    intuition. intros ? Q. left. eauto.
    subst. intros ? [Q|Q]. eauto. contradiction.
    subst. intros ? Q. left. eauto.
    subst. intros ? [Q|Q]. eauto. contradiction.
Unshelve.
  apply pempty.
Qed.


(* ---------- break down self intro into elementary rules --------- *)

(* piecewise, step by step:

   A^f* -> B^x        <-- contravariant use in arg position ( a < f* )
   A^a  -> B^x
   A^a  -> B^a
 ( A^a  -> B^f )^a    <-- contravariant use in res position ( a < f )

*)

(* A^f* -> B^x  <:  A^a -> B^x *)
Lemma sem_stp_fun_fn1fr1_to_q1': forall G p T1 T2 fr1 q1 q1b q1fn_a q2fn_a,
    psub (plift q1b) (pdom G) ->
    (q1fn_a = true \/ fr1 = false /\ q1 = qempty) ->
    sem_stp2 G p false
      (TFun T1 q1fn_a true  qempty T2 q2fn_a true false qempty) fr1 (plift q1)  (*  A^f* -> B^x  *)
      (TFun T1 false  false q1b    T2 q2fn_a true false qempty) fr1 (plift q1). (*  A^a  -> B^x  *)
Proof.
  intros. intros ? ? ? ? ? WFE ST vf lf. intros HVF HQF.

  rename H0 into HGF.

  destruct vf; try solve [inversion HVF].

  assert (length G = length E) as L. symmetry. eapply WFE.
  assert (pdom G = pdom E) as PD. unfoldq. rewrite L. eauto.

  eexists lf.

  destruct HVF as (? & ? & ? & ? & ? & HVF).
  split. 2: split.
  simpl.
  split. 2: split. 3: split. 4: split. 5: split.
  - eauto.
  - rewrite <-PD. eauto.
  - eauto.
  - eauto.
  - eauto.
  - intros ? ? ? ? ? ? HVX HQX.
    destruct (HVF S' M' vx lsx) as (S'' & M'' & vy & lsy & ? & ? & ? & ? & HQY).
    + eauto.
    + eauto.
    + eauto.
    + intros ? Q. eapply HQX in Q.
      assert (plift lf x \/ pnot (plift lf) x) as C. unfold pnot,plift. destruct (lf x); eauto.
      destruct C as [C|C].
      * destruct q1fn_a.
        -- right. left. eauto.
        -- eapply HQF in C. destruct HGF as [HGF|HGF]. inversion HGF. destruct HGF. subst.
           destruct C. left. eauto. (* contra *) contradiction.
      * right. right. eauto.

    + exists S'', M'', vy, lsy.
      split. 2: split. 3: split. 4: split.
      * eauto.
      * eauto.
      * eauto.
      * eauto.
      * eauto.
  - eauto.
  - unfoldq. intuition.
Qed.

Lemma sem_stp_fun_fn1fr1_to_q1'': forall G p T1 T2 fr1 q1 q1b q1fn_a q2fn_a,
    psub (plift q1b) (pdom G) ->
    (q1fn_a = true \/ fr1 = false /\ q1 = qempty) ->
    sem_stp2 G p false
      (TFun T1 q1fn_a true qempty T2 q2fn_a true false qempty) fr1 (plift q1)  (*  A^f* -> B^x  *)
      (TFun T1 q1fn_a true q1b    T2 q2fn_a true false qempty) fr1 (plift q1). (*  A^a  -> B^x  *)
Proof.
  intros. intros ? ? ? ? ? WFE ST vf lf. intros HVF HQF.

  rename H0 into HGF.

  destruct vf; try solve [inversion HVF].

  assert (length G = length E) as L. symmetry. eapply WFE.
  assert (pdom G = pdom E) as PD. unfoldq. rewrite L. eauto.

  eexists lf.

  destruct HVF as (? & ? & ? & ? & ? & HVF).
  split. 2: split.
  simpl.
  split. 2: split. 3: split. 4: split. 5: split.
  - eauto.
  - rewrite <-PD. eauto.
  - eauto.
  - eauto.
  - eauto.
  - intros ? ? ? ? ? ? HVX HQX.
    destruct (HVF S' M' vx lsx) as (S'' & M'' & vy & lsy & ? & ? & ? & ? & HQY).
    + eauto.
    + eauto.
    + eauto.
    + intros ? Q. eapply HQX in Q.
      assert (plift lf x \/ pnot (plift lf) x) as C. unfold pnot,plift. destruct (lf x); eauto.
      destruct C as [C|C].
      * destruct q1fn_a.
        -- right. left. eauto.
        -- eapply HQF in C. destruct HGF as [HGF|HGF]. inversion HGF. destruct HGF. subst.
           destruct C. left. eauto. (* contra *) contradiction.
      * right. right. eauto.

    + exists S'', M'', vy, lsy.
      split. 2: split. 3: split. 4: split.
      * eauto.
      * eauto.
      * eauto.
      * eauto.
      * eauto.
  - eauto.
  - unfoldq. intuition.
Qed.

(* ( A^* -> B^x )^0  <:  A^a -> B^x *)
Lemma sem_stp_fun_fn1_to_q1: forall G p T1 T2 q1b q2fn_a,
    psub (plift q1b) (pdom G) ->
    sem_stp2 G p false
      (TFun T1 false true  qempty T2 q2fn_a true false qempty) false (plift qempty)  (* ( A^* -> B^x )^0  *)
      (TFun T1 false false q1b    T2 q2fn_a true false qempty) false (plift qempty). (* ( A^a -> B^x )^0  *)
Proof.
  intros. eapply sem_stp_fun_fn1fr1_to_q1'. eauto. intuition.
Qed.

(* A^f* -> B^x  <:  A^a -> B^x *)
Lemma sem_stp_fun_fn1fr1_to_q1: forall G p T1 T2 q1b fr1 q1 q2fn_a,
    psub (plift q1b) (pdom G) ->
    sem_stp2 G p false
      (TFun T1 true  true  qempty T2 q2fn_a true false qempty) fr1 (plift q1)  (*  A^f* -> B^x  *)
      (TFun T1 false false q1b    T2 q2fn_a true false qempty) fr1 (plift q1). (*  A^a  -> B^x  *)
Proof.
  intros. eapply sem_stp_fun_fn1fr1_to_q1'. eauto. intuition.
Qed.


(* A^a -> B^x  <:  A^a -> B^a  (covariant elimination of arg ref -- note: can't do this for A^a* -> ... diff notion of freshness for arg/res) *)
Lemma sem_stp_fun_ar2_to_q2: forall G p T1 T2 q1fn q1 fr1 qf q2fn_a q2fn_b,
    q2fn_b = q1fn || q2fn_a ->
    sem_stp2 G p false
      (TFun T1 q1fn false q1 T2 q2fn_a true  false qempty) fr1 (plift qf)  (*  A^a -> B^x  *)
      (TFun T1 q1fn false q1 T2 q2fn_b false false q1)     fr1 (plift qf). (*  A^a -> B^a  *)
Proof.
  intros. intros ? ? ? ? ? WFE ST vf lf. intros HVF HQF.

  destruct vf; try solve [inversion HVF].

  assert (length G = length E) as L. symmetry. eapply WFE.
  assert (pdom G = pdom E) as PD. unfoldq. rewrite L. eauto.

  eexists lf.

  destruct HVF as (? & ? & ? & ? & ? & HVF).
  split. 2: split.
  simpl.
  split. 2: split. 3: split. 4: split. 5: split.
  - eauto.
  - eauto.
  - eauto.
  - eauto.
  - eauto.
  - intros ? ? ? ? ? ? HVX HQX.
    destruct (HVF S' M' vx lsx) as (S'' & M'' & vy & lsy & ? & ? & ? & ? & HQY).
    + eauto.
    + eauto.
    + eauto.
    + eauto.
    + exists S'', M'', vy, lsy.
      split. 2: split. 3: split. 4: split.
      * eauto.
      * eauto.
      * eauto.
      * eauto.
      * intros ? Q. eapply HQY in Q. destruct Q as [H_q | [H_vf | H_fr]].
        -- left. eapply vars_locs_monotonic. 2: eauto. unfoldq. intuition.
        -- right. left. destruct q2fn_a. 2: contradiction.
           rewrite H. destruct q1fn; eauto. 
        -- destruct H_fr as [H_vx | H_fr].
           ++ eapply HQX in H_vx. destruct H_vx as [H_q1 | [H_fn | H_fr]].
              ** left. eauto.
              ** right. left. rewrite H. destruct q1fn; eauto. contradiction.
              ** contradiction.
           ++ right. right. right. eauto.
  - eauto.
  - unfoldq. intuition.
Qed.


(* A^u -> B^a  <:  ( A^u -> A^f )^a  *)
Lemma sem_stp_fun_q2_to_fn2: forall G p T1 T2 q1fr q2fn q1 q2 fr1 qfa qfb,
    psub (plift qfb) p ->
    psub (plift qfa) (plift qfb) ->
    psub (plift q2) (plift qfb) ->
    sem_stp2 G p true
      (TFun T1 false q1fr q1 T2 q2fn false false q2)     fr1 (plift qfa)  (*   A^u -> B^a      *)
      (TFun T1 false q1fr q1 T2 true  false false qempty) fr1 (plift qfb). (* ( A^u -> B^f )^a  *)
Proof.
  intros. intros ? ? ? ? ? WFE ST vf lf. intros HVF HQF.

  destruct vf; try solve [inversion HVF].

  assert (length G = length E) as L. symmetry. eapply WFE.
  assert (pdom G = pdom E) as PD. unfoldq. rewrite L. eauto.

  eexists (qor lf (vars_locs_fix V qfb)).

  destruct HVF as (? & ? & ? & ? & ? & HVF).
  split. 2: split.
  simpl.
  split. 2: split. 3: split. 4: split. 5: split.
  - eauto.
  - eauto.
  - eauto.
  - rewrite plift_empty. unfoldq. intuition.
  - rewrite plift_or, plift_vars_locs. unfoldq. intuition.
    eapply env_type_store_wf. eauto. eauto. eauto.
  - intros ? ? ? ? ? ? HVX HQX.
    destruct (HVF S' M' vx lsx) as (S'' & M'' & vy & lsy & ? & ? & ? & ? & HQY).
    + eauto.
    + eauto.
    + eauto.
    + intros ? Q. eapply HQX in Q. destruct Q as [H_q1 | [H_fn | H_fr]].
      * left. eauto.
      * right. left. contradiction.
      * right. right. destruct q1fr. 2: contradiction. intros Q.
        eapply H_fr. rewrite plift_or, plift_vars_locs. left. eauto.
    + exists S'', M'', vy, lsy.
      split. 2: split. 3: split. 4: split.
      * eauto.
      * eauto.
      * eauto.
      * eauto.
      * intros ? Q. eapply HQY in Q. destruct Q as [H_q | [H_vf | H_fr]].
        -- right. left. rewrite plift_or, plift_vars_locs. right.
           eapply vars_locs_monotonic. 2: eauto. unfoldq. intuition.
        -- right. left. destruct q2fn. rewrite plift_or. left. eauto.
           contradiction.
        -- destruct H_fr as [H_vx | H_fr].
           ++ contradiction.
           ++ contradiction.
  - rewrite plift_or, plift_vars_locs. intros ? Q. destruct Q as [H_vf | H_q2].
    + eapply HQF in H_vf. destruct H_vf as [H_q | H_fr].
      * left. eapply vars_locs_monotonic. 2: eauto. unfoldq. intuition.
      * right. eauto.
    + left. eauto.
  - rewrite plift_or, plift_vars_locs. unfoldq. intuition.
Qed.


(* A^f* -> B^x  <:  ( A^a -> B^f )^a   (derived form)  *)
Lemma sem_stp_fun_fn1fr1_to_q1fn2: forall G p T1 T2 q1 fr1 qfa qfb q2fn_a,
    psub (plift qfb) p ->
    psub (plift q1) (pdom G) ->
    psub (plift qfa) (plift qfb) ->
    psub (plift q1) (plift qfb) ->
    sem_stp2 G p true
      (TFun T1 true  true  qempty T2 q2fn_a true  false qempty) fr1 (plift qfa)  (*   A^f* -> B^x      *)
      (TFun T1 false false q1     T2 true  false false qempty) fr1 (plift qfb). (* ( A^a  -> B^f )^a  *)
Proof.
  intros. intros ? ? ? ? ? WFE (* WFQ WFX *) ST vf lf. intros HVF HQF.
  edestruct sem_stp_fun_fn1fr1_to_q1 with (q1b:=q1). eauto. eauto. eauto. eapply HVF. eapply HQF.
  edestruct sem_stp_fun_ar2_to_q2 with (q1:=q1). eauto. eauto. eauto. eapply H3. eapply H3.
  edestruct sem_stp_fun_q2_to_fn2. 4: eauto. 4: eauto. 4: eapply H4. 4: eapply H4.
  eauto. eauto. eauto.
  exists x1. intuition.
  unfoldq. intuition.
Qed.

(* B^b  <:  A^a   -->   A^a -> C^f  <:  ( B^b -> C^f )^a  *)
Lemma sem_stp_fun_T1q1: forall G p T1a T1b T2 fr1 q1b q1a qfa qfb,
    closed_ty (length G) T2 ->
    closed_ty (length G) T1b ->
    psub (plift q1b) (pdom G) ->
    psub (plift qfb) p ->
    psub (plift qfa) (plift qfb) ->
    psub (plift q1b) (plift qfb) ->
    sem_stp2 G p true T1b false (plift q1b) T1a false (*fr2*) (plift q1a) ->  (*   B^b -> A^a      *)
    sem_stp2 G p true
      (TFun T1a false false q1a T2 true false false qempty) fr1 (plift qfa)   (*   A^a -> C^f      *)
      (TFun T1b false false q1b T2 true false false qempty) fr1 (plift qfb).  (* ( B^b -> C^f )^b  *)
Proof.
  intros. intros ? ? ? ? ? WFE ST vf lf. intros HVF HQF.

  rename H5 into STX. (* specialize (H S M E V) as STX. *)

  destruct vf; try solve [inversion HVF].

  assert (length G = length E) as L. symmetry. eapply WFE.
  assert (pdom G = pdom E) as PD. unfoldq. rewrite L. eauto.

  eexists (qor lf (vars_locs_fix V qfb)).

  destruct HVF as (? & ? & ? & ? & ? & HVF).
  split. 2: split.
  simpl.
  split. 2: split. 3: split. 4: split. 5: split.
  - rewrite <-L. eauto.
  - rewrite <-PD. eauto.
  - eauto.
  - rewrite plift_empty. unfoldq. intuition.
  - rewrite plift_or, plift_vars_locs. intros ? Q. destruct Q. eauto.
    eapply env_type_store_wf. eauto. eauto. eauto.
  - intros ? ? ? ? ? ? HVX HQX.
    edestruct STX as (lsx' & ? & HQX' & ? & ?).
    3: eauto. eapply envt_store_extend; eauto. eauto. {
      intros ? Q. eapply HQX in Q. destruct Q as [H_q1 | [H_fn | H_fr]].
      * left. eauto.
      * contradiction.
      * contradiction. }
    destruct (HVF S' M' vx lsx') as (S'' & M'' & vy & lsy & ? & ? & ? & ? & HQY).
    + eauto.
    + eauto.
    + eauto.
    + intros ? Q. eapply HQX' in Q. destruct Q as [H_q1 | ?].
      * left. eauto.
      * contradiction.
    + exists S'', M'', vy, lsy.
      split. 2: split. 3: split. 4: split.
      * eauto.
      * eauto.
      * eauto.
      * eauto.
      * intros ? Q. eapply HQY in Q. destruct Q as [H_q | [H_vf | H_fr]].
        -- left. eauto.
        -- right. left. rewrite plift_or. left. eauto.
        -- destruct H_fr as [H_vx | H_fr].
           ++ contradiction.
           ++ contradiction.
  - rewrite plift_or, plift_vars_locs. intros ? Q. destruct Q as [H_vf | H_q2].
    + eapply HQF in H_vf. destruct H_vf as [H_q | H_fr].
      * left. eapply vars_locs_monotonic. 2: eauto. unfoldq. intuition.
      * right. eauto.
    + left. eauto.
  - rewrite plift_or, plift_vars_locs. unfoldq. intuition.
Unshelve.
    apply pempty.
Qed.


(* same as the other "fresh_arg_to_self" lemma above, but proved through
   transitive chain of more elementary rules *)
Lemma sem_stp_fun_fresh_arg_to_self_piecewise: forall G p T1a T1b T2 fr1 q1b q1a qfa qfb,
    closed_ty (length G) T2 ->
    closed_ty (length G) T1b ->
    psub (plift q1a) (pdom G) ->
    psub (plift q1b) (pdom G) ->
    psub (plift qfb) p ->
    psub (plift q1b) (plift q1a) ->
    psub (plift qfa) (plift qfb) ->
    psub (plift q1a) (plift qfb) ->
    sem_stp2 G p true T1b false (plift q1b) T1a false (*fr2*) (plift q1a) ->     (*   B^b  -> A^a      *)
    sem_stp2 G p true
      (TFun T1a true  true  qempty T2 false true  false qempty) fr1 (plift qfa)  (*   A^f* -> B^x      *)
      (TFun T1b false false q1b    T2 true  false false qempty) fr1 (plift qfb). (* ( A^a  -> B^f )^a  *)
Proof.
  intros. intros ? ? ? ? ? WFE (* WFQ WFX *) ST vf lf. intros HVF HQF.
  edestruct sem_stp_fun_fn1fr1_to_q1fn2 with (q1:=q1a) (qfb:=qfb).
  5: eauto. 5: eauto. 5: eapply HVF. 5: eapply HQF.
  eauto. eauto. eauto. eauto.
  edestruct sem_stp_fun_T1q1. 7: eauto. 7: eauto. 7: eauto. 7: eapply H8. 7: eapply H8.
  eauto. eauto. eauto. eauto. unfoldq. intuition. unfoldq. intuition.
  exists x0. intuition.
  eauto. unfoldq. intuition.
Qed.



(* (A^q -> B^f)^a  <:  (A^q -> B^q)^a   (covariant elimination of self - self must be non-fresh) *)
Lemma sem_stp_fun_fn2_to_q2: forall G p T1 T2 q1fn q1fr q1 qf,
    psub (plift qf) (pdom G) ->
    psub (plift qf) p ->
    sem_stp2 G p false
      (TFun T1 q1fn q1fr q1 T2 true  false false qempty) false (plift qf)  (* ( A^q -> B^f )^a  *)
      (TFun T1 q1fn q1fr q1 T2 false false false qf)     false (plift qf). (* ( A^q -> B^a )^a  *)
Proof.
  intros. intros ? ? ? ? ? WFE ST vf lf. intros HVF HQF.

  destruct vf; try solve [inversion HVF].

  assert (length G = length E) as L. symmetry. eapply WFE.
  assert (pdom G = pdom E) as PD. unfoldq. rewrite L. eauto.

  eexists lf.

  destruct HVF as (? & ? & ? & ? & ? & HVF).
  split. 2: split.
  simpl.
  split. 2: split. 3: split. 4: split. 5: split.
  - eauto.
  - eauto.
  - eauto.
  - rewrite <-PD. eauto.
  - eauto.
  - intros ? ? ? ? ? ? HVX HQX.
    destruct (HVF S' M' vx lsx) as (S'' & M'' & vy & lsy & ? & ? & ? & ? & HQY).
    + eauto.
    + eauto.
    + eauto.
    + eauto.
    + exists S'', M'', vy, lsy.
      split. 2: split. 3: split. 4: split.
      * eauto.
      * eauto.
      * eauto.
      * eauto.
      * intros ? Q. eapply HQY in Q. destruct Q as [H_q | [H_vf | H_fr]].
        -- left. eapply vars_locs_monotonic. 2: eauto. unfoldq. intuition.
        -- eapply HQF in H_vf. destruct H_vf.
           ++ left. eauto.
           ++ contradiction.
        -- destruct H_fr as [H_vx | H_fr].
           ++ contradiction.
           ++ contradiction.
  - eauto.
  - unfoldq. intuition.
Qed.


(*

   ((A^a -> A^f)^*f -> A^x)^a
<: ((A^*f -> A^x)^*f -> A^xf)^a


Inner growth:

   (A^*f -> A^fx)  TF_inner_opaque A
<: (A^a -> A^f)^a  TF_inner_transp A a


Outer growth: with A <: B^a (growth)

   B^*f -> A^x
<: (B^*fa -> A^xa)
<: (A^*f -> A^xa)
<: (A^*f -> A^xf)^a


*)

Definition TF_inner_transp A a := TFun A false false a A true false false qempty.

Definition TF_inner_opaque A := TFun A true true qempty A true true false qempty.

Lemma sem_stp_opaque_inner: forall G p A a fr1,
    (* --- closedness --- *)
    closed_ty (length G) A ->
    closed_ql (length G) a ->
    psub (plift a) p ->
    (* --- result --- *)
    sem_stp2 G p true
      (TF_inner_opaque A) fr1 (plift qempty)
      (TF_inner_transp A a) fr1 (plift a).
Proof.
  intros. intros ? ? ? ? ? WFE (* WFQ WFX *) ST vf lf. intros HVF HQF.
  eapply sem_stp_fun_fn1fr1_to_q1fn2; eauto.
  unfoldq. intuition. unfoldq. intuition. 
Qed.


Definition TF_outer_transp A B := TFun A true true qempty B false true false qempty.

Definition TF_outer_opaque A B := TFun A true true qempty B true true false qempty.


Lemma sem_stp_opaque_outer: forall G p A B a fr1,
    (* --- closedness --- *)
    closed_ty (length G) A ->
(*  closed_ty (length G) B -> *)
    closed_ql (length G) a ->
    psub (plift a) p ->
    (* --- result --- *)
    sem_stp2 G p true
      (TF_outer_transp (TF_inner_transp A a) B) fr1 (plift a)
      (TF_outer_opaque (TF_inner_opaque A) B) fr1 (plift a).
Proof.
  intros. intros ? ? ? ? ? WFE (* WFQ WFX *) ST vf lf. intros HVF HQF.

  
  destruct vf; try solve [inversion HVF].

  assert (length G = length E) as L. symmetry. eapply WFE.
  assert (pdom G = pdom E) as PD. unfoldq. rewrite L. eauto.

  eexists (qor lf (vars_locs_fix V a)).

  destruct HVF as (? & ? & ? & ? & ? & HVF).
  split. 2: split.
  split. 2: split. 3: split. 4: split. 5: split.
  - rewrite <-L. econstructor; eauto. rewrite L. eauto. rewrite L. eauto. 
  - rewrite <-PD. rewrite plift_empty. unfoldq. intuition. 
  - eauto. 
  - rewrite plift_empty. unfoldq. intuition.
  - rewrite plift_or, plift_vars_locs. intros ? Q. destruct Q. eauto.
    eapply env_type_store_wf. eauto. eauto. eauto.
  - intros ? ? ? ? ? ? HVX HQX.
    edestruct sem_stp_opaque_inner as (lsx' & ? & HQX' & ? & ?).
    6: eapply HVX. eauto. eauto. eauto. 
    eapply envt_store_extend; eauto. eauto. {
      intros ? Q. right. assert (pif true (plift lsx) x). eapply Q. eauto. }
    (* need to compare with previous lsx! *)
    destruct (HVF S' M' vx lsx') as (S'' & M'' & vy & lsy & ? & ? & ? & ? & HQY).
    + eauto.
    + eauto.
    + eauto.
    + intros ? Q. eapply HQX' in Q. 
      remember (lf x) as C. destruct C.
      right. left. simpl. unfold plift. eauto.
      right. right. simpl. intros C. unfold plift in *. rewrite C in HeqC. inversion HeqC. 
    + exists S'', M'', vy, lsy.
      split. 2: split. 3: split. 4: split.
      * eauto.
      * eauto.
      * eauto.
      * eauto.
      * intros ? Q. eapply HQY in Q. destruct Q as [H_q | [H_vf | H_fr]].
        -- left. eauto.
        -- contradiction. (* right. left. rewrite plift_or. left. eauto. *)
        -- destruct H_fr as [H_vx | H_fr].
           eapply HQX' in H_vx. destruct H_vx.
           ++ right. left. rewrite plift_or, plift_vars_locs. right. eauto.
           ++ right. right. left. eauto. 
           ++ right. right. right. eauto. 
  - rewrite plift_or, plift_vars_locs. intros ? Q. destruct Q as [H_vf | H_q2].
    + eapply HQF in H_vf. destruct H_vf as [H_q | H_fr].
      * left. eapply vars_locs_monotonic. 2: eauto. unfoldq. intuition.
      * right. eauto.
    + left. eauto.
  - rewrite plift_or, plift_vars_locs. unfoldq. intuition.
Qed.



(* ---- other assorted minimal subtypting rules --- *)


(* A -> B  <:  A -> B *)
Lemma sem_stp_fun_refl': forall G p T1a T2a T1b T2b
                               q1fn_a q1fr_a q1a q2fn_a q2ar_a q2fr_a q2a
                               qffr_a qfa,
    (* --- closedness --- *)
    closed_ty (length G) T1b ->
    closed_ty (length G) T2b ->
    (* --- result --- *)
    sem_stp0 G p
      (TFun T1a q1fn_a q1fr_a q1a T2a q2fn_a q2ar_a q2fr_a q2a) qffr_a qfa
      (TFun T1a q1fn_a q1fr_a q1a T2a q2fn_a q2ar_a q2fr_a q2a) qffr_a qfa.
Proof.
  intros. intros ? ? ? ? ? WFE (* WFQ WFX *) ST vf lf HVF.

  specialize H as STX. (* specialize (H S M E V) as STX. *)
  specialize H0 as STY. (* specialize (H0 S M E V) as STY. *)

  destruct vf; try solve [inversion HVF].

  assert (length G = length E) as L. symmetry. eapply WFE.
  assert (pdom G = pdom E) as PD. unfoldq. rewrite L. eauto.

  destruct HVF; intuition.
  rename H8 into HVF.
  simpl. intuition.
Qed.

(* A -> B  <:  A -> B' *)
Lemma sem_stp_fun_res_type: forall G p T1a T2a
                               q1fn_a q1fr_a q1a q2fn_a q2ar_a q2fr_a q2a
                               qffr_a qfa
                               T2b,
    sem_stp0 G p T2a (*q2fr_a*) true (plift q2a) T2b (*q2fr_a*) true (plift q2a) ->
    (* --- closedness --- *)
    closed_ty (length G) T2b ->
    (* --- result --- *)
    sem_stp0 G p
      (TFun T1a q1fn_a q1fr_a q1a T2a q2fn_a q2ar_a q2fr_a q2a) qffr_a qfa
      (TFun T1a q1fn_a q1fr_a q1a T2b(*!*) q2fn_a q2ar_a q2fr_a q2a) qffr_a qfa.
Proof.
  intros. intros ? ? ? ? ? WFE (* WFQ WFX *) ST vf lf HVF.

  specialize H as STY. (* specialize (H S M E V) as STX. *)

  destruct vf; try solve [inversion HVF].

  assert (length G = length E) as L. symmetry. eapply WFE.
  assert (pdom G = pdom E) as PD. unfoldq. rewrite L. eauto.

  destruct HVF; intuition.
  rename H8 into HVF.
  simpl. intuition.

  - rewrite <-L. eauto.
  - destruct (HVF S' M' vx lsx) as (S'' & M'' & vy & lsy & ? & ? & ? & ? & ?).
    + eauto.
    + eauto.
    + eauto.
    + eauto.
    + exists S'', M'', vy, lsy.
      split. 2: split. 3: split. 4: split.
      * eauto.
      * eauto.
      * eauto.
      * eapply STY.
        eapply envt_store_extend. eauto. eapply stchain_chain; eauto.
        eauto. eauto.
        (* could just do eauto, but going step by step to serve as template *)
        assert (psub (plift lsy)
                  (por (vars_locs V (plift q2a))
                     (por (pif q2fn_a (plift lf))
                        (por (pif q2ar_a (plift lsx))
                           (pif q2fr_a (pstdiff M'' M')))))) as P. {
        intros ? Q. eapply H15 in Q. destruct Q as [H_q2 | [H_vf | [H_vx | H_fr]]].
        -- left. eauto.
        -- right. left. eauto.
        -- right. right. left. eauto.
        -- right. right. right. eauto.
        }
        eapply P.
      * eauto.
Qed.

(* A -> B^a  <:  A -> B^a' *)
Lemma sem_stp_fun_res_qual: forall G p T1a T2a
                               q1fn_a q1fr_a q1a q2fn_a q2ar_a q2fr_a q2a
                               qffr_a qfa
                               q2b,
    sem_qstp G p (plift q2a) (plift q2b) ->
    (* --- closedness --- *)
    psub (plift q2b) (pdom G) ->
    (* --- result --- *)
    sem_stp0 G p
      (TFun T1a q1fn_a q1fr_a q1a T2a q2fn_a q2ar_a q2fr_a q2a) qffr_a qfa
      (TFun T1a q1fn_a q1fr_a q1a T2a q2fn_a q2ar_a q2fr_a q2b(*!*)) qffr_a qfa.
Proof.
  intros. intros ? ? ? ? ? WFE (* WFQ WFX *) ST vf lf HVF.

  specialize H as STY. (* specialize (H S M E V) as STX. *)

  destruct vf; try solve [inversion HVF].

  assert (length G = length E) as L. symmetry. eapply WFE.
  assert (pdom G = pdom E) as PD. unfoldq. rewrite L. eauto.

  destruct HVF; intuition.
  rename H8 into HVF.
  simpl. intuition.

  - rewrite <-PD. eauto.
  - destruct (HVF S' M' vx lsx) as (S'' & M'' & vy & lsy & ? & ? & ? & ? & ?).
    + eauto.
    + eauto.
    + eauto.
    + eauto.
    + exists S'', M'', vy, lsy.
      split. 2: split. 3: split. 4: split.
      * eauto.
      * eauto.
      * eauto.
      * eauto.
      * intros ? Q. eapply H15 in Q. destruct Q as [H_q2 | [H_vf | [H_vx | H_fr]]].
        -- left. eapply STY; eauto.
        -- right. left. eauto.
        -- right. right. left. eauto.
        -- right. right. right. eauto.
Qed.

(* A -> B  <:  A -> B' *)
Lemma sem_stp_fun_res_typequal: forall G p T1a T2a
                               q1fn_a q1fr_a q1a q2fn_a q2ar_a q2fr_a q2a
                               qffr_a qfa
                               T2b q2b,
    sem_stp0 G p T2a (*q2fr_a*) true (plift q2a) T2b (*q2fr_a*) true (plift q2b) ->
    (* --- closedness --- *)
    closed_ty (length G) T2b ->
    psub (plift q2b) (pdom G) ->
    (* --- result --- *)
    sem_stp0 G p
      (TFun T1a q1fn_a q1fr_a q1a T2a q2fn_a q2ar_a q2fr_a q2a) qffr_a qfa
      (TFun T1a q1fn_a q1fr_a q1a T2b(*!*) q2fn_a q2ar_a q2fr_a q2b(*!*)) qffr_a qfa.
Proof.
  intros. intros ? ? ? ? ? WFE (* WFQ WFX *) ST vf lf HVF.

  specialize H as STY. (* specialize (H S M E V) as STX. *)

  destruct vf; try solve [inversion HVF].

  assert (length G = length E) as L. symmetry. eapply WFE.
  assert (pdom G = pdom E) as PD. unfoldq. rewrite L. eauto.

  destruct HVF; intuition.
  rename H9 into HVF.
  simpl. intuition.

  - rewrite <-L. eauto.
  - rewrite <-PD. eauto.
  - destruct (HVF S' M' vx lsx) as (S'' & M'' & vy & lsy & ? & ? & ? & ? & ?).
    + eauto.
    + eauto.
    + eauto.
    + eauto.
    + exists S'', M'', vy, lsy.
      split. 2: split. 3: split. 4: split.
      * eauto.
      * eauto.
      * eauto.
      * eapply STY.
        eapply envt_store_extend. eauto. eapply stchain_chain; eauto.
        eauto. eauto.
        (* could just use eauto, but go step by step anyways *)
        assert (psub (plift lsy)
                  (por (vars_locs V (plift q2a))
                     (por (pif q2fn_a (plift lf))
                        (por (pif q2ar_a (plift lsx))
                           (pif q2fr_a (pstdiff M'' M')))))) as P. {
        intros ? Q. eapply H16 in Q. destruct Q as [H_q2 | [H_vf | [H_vx | H_fr]]].
        -- left. eauto.
        -- right. left. eauto.
        -- right. right. left. eauto.
        -- right. right. right. eauto.
        }
        eapply P.
      * eapply STY in H15. destruct H15. intros ? Q. eapply H16 in Q as Q2.
        destruct Q2 as [H_q2 | ?].
        -- left. eauto.
        -- right. eauto.
        -- intros ? Q. eapply H17 in Q as Q2. destruct Q2 as [H_q2 | ?].
           left. eauto.
           right. eauto.
        -- eapply envt_store_extend; eauto. eapply stchain_chain; eauto.
        -- eauto.
Qed.


(* ---------- *)

Lemma sem_stpT_refl: forall G p T1,
    sem_stpT G p T1 T1.
Proof.
  intros. intros ? ? ? ? ? ?. intuition.
Qed.

Lemma sem_stp2_refl: forall G p gr T1 fr1 q1,
    sem_stp2 G p gr T1 fr1 q1 T1 fr1 q1.
Proof.
  intros. eapply stp_up2. eapply stp_upT. eapply sem_stpT_refl.
  intros ? ? ? ?. intuition.
  unfoldq. intuition.
  unfoldq. intuition.
  unfold bsub. intuition.
Qed.

Lemma sem_stp2_trans: forall G p gr T1 T2 T3 fr1 fr2 fr3 q1 q2 q3,
    sem_stp2 G p gr T1 fr1 q1 T2 fr2 q2 ->
    sem_stp2 G p gr T2 fr2 q2 T3 fr3 q3 ->
    sem_stp2 G p gr T1 fr1 q1 T3 fr3 q3.
Proof.
    intros. intros ? *. intros.
    edestruct H. eauto. eauto. eapply H3. eapply H4.
    edestruct H0. eauto. eauto. eapply H5. eapply H5.
    exists x0. intuition.
    unfoldq. intuition.
    unfoldq. intuition.
Qed.


(* type assignment: subsumption rule using value subtyping *)
Lemma sem_sub_stp0: forall env y p T1 T2 fr1 fr2 q1 q2,
    sem_type env y T1 p fr1 q1 ->
    sem_stp0 env p T1 fr1 q1 T2 fr2 q2 ->
    sem_qstp env p q1 q2 -> (* XXX *)
    bsub fr1 fr2 ->
    sem_type env y T2 p fr2 q2.
Proof.
  intros. intros ? ? ? ? WFE ST.
  destruct (H S M E V) as [S1 [M1 [vx [lsx [IW1 [SC1 [ST1 [HVX [HQX HPX]]]]]]]]].
  eauto. eauto.

  exists S1, M1. exists vx, lsx.
  split. 2: split. 3: split. 4: split. 5: split.
  - eauto.
  - eauto.
  - eauto.
  - eapply H0. eapply envt_store_extend; eauto.
    eauto. eauto.
    intros ? Q. eapply HQX in Q. destruct Q as [H_q | H_fr].
    left. eapply vars_locs_monotonic; eauto. unfoldq. intuition.
    right. eauto.
  - intros ? Q. eapply HQX in Q. destruct Q as [H_q | H_fr].
    left. eapply H1; eauto.
    right. destruct fr1,fr2,H2; eauto. contradiction.
  - eauto.
Qed.

Lemma sem_sub_stp1: forall env y p T1 T2 fr1 fr2 q1 q2 q2',
    sem_type env y T1 p fr1 q1 ->
    sem_stp1 env p T1 fr1 q1 T2 fr2 q2 ->
    sem_qstp env p q1 q2 -> (* XXX *)
    bsub fr1 fr2 ->
    plift q2' = pand p q2 ->
    sem_type env y T2 p fr2 q2.
Proof.
  intros. intros ? ? ? ? WFE ST.
  destruct (H S M E V) as [S1 [M1 [vx [lsx [IW1 [SC1 [ST1 [HVX [HQX HPX]]]]]]]]].
  eauto. eauto.

  exists S1, M1. exists vx, (qor lsx (vars_locs_fix V q2')).
  split. 2: split. 3: split. 4: split. 5: split.
  - eauto.
  - eauto.
  - eauto.
  - eapply H0. eapply envt_store_extend; eauto.
    eauto.
    eauto.
    intros ? Q. eapply HQX in Q. destruct Q as [H_q | H_fr].
    left. eapply vars_locs_monotonic; eauto. unfoldq. intuition.
    right. eauto.
    rewrite plift_or, plift_vars_locs, H3. eauto.
  - intros ? Q. rewrite plift_or in Q. destruct Q as [H_lsx | H_q2].
    + eapply HQX in H_lsx. destruct H_lsx as [H_q | H_fr].
      left. eapply H1. eauto. eauto.
      right. destruct fr1,fr2,H2; eauto. contradiction.
    + left. rewrite plift_vars_locs in H_q2. eapply vars_locs_monotonic. 2: eauto.
      rewrite H3. unfoldq. intuition.
  - destruct y; eauto.
    intros ? Q. eapply HPX in Q. rewrite plift_or. left. eauto.
Qed.

Lemma sem_sub_stp2: forall env y p gr T1 T2 fr1 fr2 q1 q2,
    sem_type env y T1 p fr1 q1 ->
    sem_stp2 env p gr T1 fr1 q1 T2 fr2 q2 ->
    psub q2 p ->
    bsub fr1 fr2 ->
    sem_type env y T2 p fr2 q2.
Proof.
  intros. intros ? ? ? ? WFE ST.
  destruct (H S M E V) as [S1 [M1 [vx [lsx [IW1 [SC1 [ST1 [HVX [HQX HPX]]]]]]]]].
  eauto. eauto.

  edestruct H0 as (lsx' & ? & HQX' & ?). eapply envt_store_extend; eauto. eauto. eauto.
  intros ? Q. eapply HQX in Q. destruct Q as [H_q | H_fr].
  left. eapply vars_locs_monotonic; eauto. unfoldq. intuition.
  right. eauto.

  exists S1, M1. exists vx, lsx'.
  split. 2: split. 3: split. 4: split. 5: split.
  - eauto.
  - eauto.
  - eauto.
  - eauto.
  - intros ? Q. eapply HQX' in Q. destruct Q as [H_q | H_fr].
    left. eapply vars_locs_monotonic. 2: eauto. unfoldq. intuition.
    right. eauto.
  - assert (psub (plift lsx) (plift lsx')). eapply H4.
    destruct y; intuition.
    intros ? Q. eapply H5. eapply HPX. eauto.
Qed.


(* semantic subtyping on expressions (as opposed to values) *)
Definition sem_stp G p T1 fr1 q1 T2 fr2 q2 :=
  forall t,
    sem_type G t T1 p fr1 q1 ->
    sem_type G t T2 p fr2 q2.

Lemma sem_stp0_to_stp: forall env p T1 T2 fr1 fr2 q1 q2,
    sem_stp0 env p T1 fr1 q1 T2 fr2 q2 ->
    sem_qstp env p q1 q2 -> (* XXX *)
    bsub fr1 fr2 ->
    sem_stp env p T1 fr1 q1 T2 fr2 q2.
Proof.
  intros. intros ? ? ?. eapply sem_sub_stp0; eauto.
Qed.

Lemma sem_stp2_to_stp: forall env p gr T1 T2 fr1 fr2 q1 q2,
    sem_stp2 env p gr T1 fr1 q1 T2 fr2 q2 ->
    bsub fr1 fr2 ->
    psub q2 p ->
    sem_stp env p T1 fr1 q1 T2 fr2 q2.
Proof.
  intros. intros ? ? ?. eapply sem_sub_stp2; eauto.
Qed.

Lemma sem_stp1_to_stp: forall env p T1 T2 fr1 fr2 q1 q2 q2',
    sem_stp1 env p T1 fr1 q1 T2 fr2 q2 ->
    sem_qstp env p q1 q2 -> (* XXX *)
    bsub fr1 fr2 ->
    plift q2' = pand p q2 ->
    sem_stp env p T1 fr1 q1 T2 fr2 q2.
Proof.
  intros. intros ? ? ?. eapply sem_sub_stp1; eauto.
Qed.


(* type assignment: subsumption rule using expression subtyping *)
Lemma sem_sub_stp: forall env y T1 T2 p fr1 q1 fr2 q2,
    sem_type env y T1 p fr1 q1 ->
    sem_stp env p T1 fr1 q1 T2 fr2 q2 ->
    sem_type env y T2 p fr2 q2.
Proof.
  intros. eauto.
Qed.


(* ----- fundamental lemmas ----- *)

Theorem qstp_fundamental : forall G p q1 q2,
    qstp G p q1 q2 ->
    sem_qstp G (plift p) (plift q1) (plift q2).
Proof.
  intros. induction H.
  - eapply sem_qs_sub; eauto.
  - rewrite plift_or, plift_diff, plift_one. eapply sem_qs_var; eauto.
  - eapply sem_qs_trans; eauto.
Qed.


Lemma stp_qstp: forall G p gr T1 T2 q1 q2 fr1 fr2,
    stp G p gr T1 fr1 q1 T2 fr2 q2 ->
    qstp G p q1 q2 /\ bsub fr1 fr2.
Proof.
  intros. induction H; eauto.
  - (* fresh arg, self res *)
    split. eapply qs_sub. intros ? Q. unfoldq. intuition.
    eauto. eauto. eauto.
  - (* covariant self res *) intuition.
    eapply qs_sub. intros ? Q. eauto. eauto. eauto.
    unfold bsub. intuition.
  - intuition.
    eapply qs_sub. intros ? Q. eauto. eauto. eauto.
    unfold bsub. intuition. apply qs_sub. intro. intuition. eauto. eauto. intro. eauto.
  - (* expand arg *) split. apply qs_sub. intro. auto. auto. auto. intro. auto.
  - (* trans *) intuition.
    eapply qs_trans; eauto.
    unfold bsub in *. intuition.
Qed.


Lemma plift_closed': forall (env: tenv) q,
    closed_ql (length env) q = psub (plift q) (pdom env).
Proof.
  intros. unfoldq. unfold closed_ql, plift. eauto.
Qed.

Lemma qstp_closed: forall G p q1 q2,
    qstp G p q1 q2 ->
    closed_ql (length G) q1 /\ closed_ql (length G) q2.
Proof.
  intros. induction H.
  - eauto.
  - split. eauto.
    rewrite plift_closed', plift_or, plift_diff, plift_one in *. unfoldq. intuition.
  (* get from env_type? *)
  - intuition.
Qed.

Lemma stp_closed: forall G p gr T1 T2 q1 q2 fr1 fr2,
    stp G p gr T1 fr1 q1 T2 fr2 q2 ->
    closed_ty (length G) T1 /\ closed_ty (length G) T2.
Proof.
  intros. induction H.
  - split; econstructor.
  - split; econstructor; eauto.
  - eapply stp_qstp in H. destruct H. eapply qstp_closed in H. destruct H.
    eapply stp_qstp in H0. destruct H0. eapply qstp_closed in H0.
    split; econstructor; intuition.
  - split; econstructor; intuition.
    intros ?. intuition.
    intros ?. intuition.
    intros ?. intuition.
    intros ?. intuition.
    intros ?. intuition.
    intros ?. intuition.
  - split; econstructor; intuition. intros ? ?. apply H2. apply H6. auto. intros ?. intuition.
  - split; econstructor; intuition.
  - split; econstructor; eauto; intro; unfold qempty; intuition. 
  - intuition.
  - intuition.
Qed.


Lemma stp2_up_gr : forall G p gr T1 T2 q1 q2 fr1 fr2,
    sem_stp2 G (plift p) false T1 fr1 (plift q1) T2 fr2 (plift q2) ->
    sem_stp2 G (plift p) gr T1 fr1 (plift q1) T2 fr2 (plift q2).
Proof.
  intros. intros ? *. intros.
  edestruct H; eauto.
  exists x. intuition.
Qed.

Theorem stp2_fundamental : forall G p gr T1 T2 q1 q2 fr1 fr2,
    stp G p gr T1 fr1 q1 T2 fr2 q2 ->
    sem_stp2 G (plift p) gr T1 fr1 (plift q1) T2 fr2 (plift q2).
Proof.
  intros. induction H.
  - (* bool *)
    eapply qstp_fundamental in H.
    eapply stp_up2. eapply stp_upT.
    intros ? ? ? ? ? ?. eauto. eauto. eauto.
  - (* ref *)
    eapply qstp_fundamental in H.
    eapply stp_up2. eapply stp_upT.
    intros ? ? ? ? ? ?. eauto. eauto. eauto.
  - (* fun *)
    eapply stp_closed in H as CLH. destruct CLH as[CLH CLH'].
    eapply stp_closed in H0 as CLH0. destruct CLH0 as [CLH0 CLH0'].
    eapply stp_qstp in H as QH. destruct QH as [QH QH'].
    eapply stp_qstp in H0 as QH0. destruct QH0 as [QH0 QH0'].
    eapply qstp_closed in QH as CLQH. destruct CLQH as [CLQH CLQH'].
    eapply qstp_closed in QH0 as CLQH0. destruct CLQH0 as [CLQH0 CLQH0'].
    eapply qstp_fundamental in QH as QFH.
    eapply qstp_fundamental in QH0 as QFH0.

    eapply stp2_up_gr. eapply sem_stp_fun2. (* always compute with gr = false, then upcast *)
    (* rewrite plift_or, plift_if in IHstp1. *)
    eapply IHstp1.
    (* rewrite plift_or, plift_or, plift_if, plift_or, plift_if, plift_if in IHstp2. *)
    eapply IHstp2.

    all: eauto.
    repeat split; intros; auto. intuition.
    eapply qstp_fundamental; eauto.
    intuition. apply qstp_closed in H7. intuition.
  - (* fun fresh arg self res *)
    eapply stp_closed in H6 as CLH. destruct CLH as[CLH CLH'].
    eapply sem_stp_fun_fresh_arg_to_self; eauto.
  - (* fun covariant self res *) eapply sem_stp_fun_q2_to_fn2. eauto. eauto. eauto.
  - eapply sem_stp_fun2; eauto. intuition. right. intuition.
    apply qstp_fundamental. auto. intro. auto. apply qstp_fundamental. auto.
    intuition. apply stp_closed in H. intuition. apply stp_closed in H0. intuition.
    apply qstp_closed in H5. intuition.
  - (* expand arg *) eapply stp2_up_gr. eapply sem_stp_fun_fn1fr1_to_q1''. eauto. eauto.
  - (* refl *)
    intros ? *. intros. exists ls. intuition. unfoldq. intuition. unfoldq. intuition.
  - (* trans *)
    intros ? *. intros.
    edestruct IHstp1; eauto.
    edestruct IHstp2. eauto. eauto. eapply H5. eapply H5.
    eexists. intuition. eapply H5. eapply H8.
    unfoldq. intuition.
    unfoldq. intuition.
Qed.



Theorem stp_fundamental : forall G p gr T1 T2 q1 q2 fr1 fr2,
    stp G p gr T1 fr1 q1 T2 fr2 q2 ->
    psub (plift q2) (plift p) ->
    sem_stp G (plift p) T1 fr1 (plift q1) T2 fr2 (plift q2).
Proof.
  intros.
  eapply stp_qstp in H as QH. destruct QH as [QH FRH].
  eapply sem_stp2_to_stp; eauto.
  eapply stp2_fundamental; eauto.
Qed.




(* if well-typed, then result is an actual value (not stuck and not a timeout),
   for large enough n *)

Theorem full_total_safety : forall e G T p fr q,
    has_type G e T p fr q ->
    sem_type G e T (plift p) fr (plift q).
Proof.
  intros ? ? ? ? ? ? W.
  induction W.
  - rewrite plift_empty. eapply sem_true; eauto.
  - rewrite plift_empty. eapply sem_false; eauto.
  - rewrite plift_one. eapply sem_var; eauto.
  - eapply sem_ref; eauto.
  - rewrite plift_empty. eapply sem_get; eauto.
  - rewrite plift_empty. eapply sem_put; eauto.
  - repeat rewrite plift_or in *. repeat rewrite plift_if in *.
    eapply sem_app; eauto.
  - repeat rewrite plift_or in *.
    repeat rewrite plift_and in *.
    repeat rewrite plift_if in *.
    repeat rewrite plift_one in *.
    eapply sem_abs; eauto.
  - eapply sem_sub; eauto.
  - rewrite plift_or, plift_diff, plift_one.
    eapply sem_sub_var; eauto.
  - eapply sem_sub_stp. eauto. eapply stp_fundamental; eauto.
Qed.


(* note: not assuming anything other than has_type below *)
Corollary safety : forall e T fr q,
  has_type [] e T qempty fr q ->
  exp_type [] st_zero [] [] e T (plift qempty) fr (plift q).
Proof.
  intros. eapply full_total_safety in H; eauto.
  destruct (H [] st_zero [] []).
  unfold env_type; intuition; simpl.
  unfoldq. intuition. inversion H0.
  unfoldq. unfoldq. intros.
  destruct H2 as [? [? [? [IX ?]]]]. intuition. inversion H5.
  unfold store_type; intuition.
  destruct H0. eexists. eexists. eauto.
Qed.


(* ---------- examples ---------- *)

(* NOTE: we're back in the syntactic world *)

Lemma qif_false: forall q,
    qif false q = qempty.
Proof.
  unfold qif. eauto with bool.
Qed.

Lemma qif_true: forall q,
    qif true q = q.
Proof.
  unfold qif. eauto with bool.
Qed.

Lemma qor_empty: forall q,
    qor q qempty = q.
Proof.
  unfold qor, qempty.
  intros. eapply functional_extensionality.
  intros. eauto with bool.
Qed.

Lemma qor_emptyl: forall q,
    qor qempty q = q.
Proof.
  unfold qor, qempty.
  intros. eapply functional_extensionality.
  intros. eauto with bool.
Qed.

Lemma qor_comm: forall q q',
    qor q q' = qor q' q.
Proof.
  unfold qor, qempty.
  intros. eapply functional_extensionality.
  intros. eauto with bool.
Qed.

Lemma qand_same: forall q,
    qand q q = q.
Proof.
  unfold qand.
  intros. eapply functional_extensionality.
  intros. destruct (q x); eauto.
Qed.

Lemma qand_sub: forall a p,
    psub (plift a) (plift p) ->
    qand p a = a.
Proof.
  unfold qand.
  intros. eapply functional_extensionality.
  intros. remember (a x) as A. destruct A.
  unfoldq. rewrite H. eauto. unfold plift. eauto.
  eauto with bool.
Qed.

Lemma qand_or_dist: forall a b c,
    qand (qor a b) c = (qor (qand a c) (qand b c)).
Proof.
  unfold qand, qor.
  intros. eapply functional_extensionality.
  intros. destruct (a x), (b x), (c ); eauto with bool.
Qed.

Lemma closedql_or_dist: forall a b x,
    closed_ql x (qor a b) = (closed_ql x a /\ closed_ql x b).
Proof.
  intros. eapply propositional_extensionality.
  unfold closed_ql, qor.
  split; intros.
  split; intros. eapply H. rewrite H0. eauto.
  intros. eapply H. rewrite H0. eauto with bool.
  destruct H. specialize (H x0). specialize (H1 x0).
  destruct (a x0), (b x0); eauto.
Qed.

Lemma qand_one: forall a l,
    closed_ql l a ->
    qand (qone l) a = qempty.
Proof.
  unfold qand, qone, qempty.
  intros. eapply functional_extensionality.
  intros. bdestruct (x =? l).
  specialize (H x).
  destruct (a x). lia. eauto.
  destruct (a x); eauto.
Qed.

Lemma hast_closed: forall env t T1 p fr1 q1, (* note: needs telescope env? *)
    has_type env t T1 p fr1 q1 ->
    telescope env ->
    closed_ty (length env) T1 /\
      closed_ql (length env) q1.
Proof.
  intros. induction H.
  - split. econstructor. intros ? Q. inversion Q.
  - split. econstructor. intros ? Q. inversion Q.
  - split. specialize (H0 x _ _ _ H). intuition.
    eapply closedty_extend; eauto. eapply indexr_var_some' in H. lia.
    eapply closedq_extend. eapply indexr_var_some' in H. 2: eauto.
    intros ? ?. unfold qone in H2. bdestruct (x0 =? x). subst. eauto.
    inversion H2.
  - intuition. econstructor. eauto.
  - intuition. inversion H2. eauto. intros ? Q. inversion Q.
  - intuition. intros ? Q. inversion Q.
  - intuition. inversion H5. eauto.
    inversion H5. subst.
    rewrite closedql_or_dist. rewrite closedql_or_dist.
    intuition. destruct fn2; intuition.
    rewrite qif_false. intros ? Q. inversion Q.
    destruct ar2; intuition.
    rewrite qif_false. intros ? Q. inversion Q.
  - intuition. econstructor; intuition.
  - intuition.
  - intuition. rewrite closedql_or_dist. intuition.
    intros ? Q. unfold qdiff in *. eapply H6. destruct (q1 x0). eauto.
    inversion Q.
    eapply closedq_extend. eapply H0. eauto. eapply indexr_var_some' in H2. lia.
  - intuition.
    eapply stp_closed in H1. intuition.
    eapply stp_qstp in H1. destruct H1.
    eapply qstp_closed in H1. destruct H1.
    eauto.
Qed.


Lemma stp_refl: forall env p gr T1 q1 fr1,
    closed_ty (length env) T1 ->
    closed_ql (length env) q1 ->
    stp env p gr T1 fr1 q1 T1 fr1 q1.
Proof.
  intros. eapply s_refl. eauto. eauto.
Qed.

Lemma stp_qs: forall T1 env p gr q1 q2 fr1 fr2, (* XXX: check if this holds! *)
    closed_ty (length env) T1 ->
    qstp env p q1 q2 ->
    bsub fr1 fr2 ->
    stp env p gr T1 fr1 q1 T1 fr2 q2.
Proof.
  intros T1. induction T1; intros.
  - eapply s_bool; eauto.
  - inversion H. eapply s_ref; eauto.
  - inversion H. eapply s_fun; eauto.
    eapply IHT1_1; eauto.
    eapply qs_sub. intros ? Q. eapply Q.
    eauto. eauto.
    unfold bsub. eauto.
    eapply IHT1_2; eauto.
    eapply qs_sub. intros ? Q. eapply Q.
    eauto. eauto.
    unfold bsub. eauto.
    unfold bsub. eauto.
    unfold bsub. eauto.
    unfold bsub. eauto.
    unfold bsub. eauto.
    unfold bsub. eauto.
Unshelve.
    apply true.
Qed.



Ltac qsimpl :=
  repeat (try rewrite qif_false;
          try rewrite qif_true;
          try rewrite qor_empty;
          try rewrite qor_emptyl;
          try rewrite qand_same;
          try rewrite qand_or_dist;
          try (rewrite qand_one; [|assumption]);
          try (rewrite qand_sub; [|assumption])).

Ltac plift_any :=
  repeat (try rewrite plift_closed' in *;
          try rewrite plift_or in *;
          try rewrite plift_and in *;
          try rewrite plift_if in *;
          try rewrite plift_diff in *;
          try rewrite plift_one in *;
          try rewrite plift_empty in *).

Ltac crush :=
  qsimpl; plift_any; unfoldq; intuition.

Ltac closed :=
  try (constructor);
  try (eapply closedty_extend; constructor);
  try (eapply closedq_extend; [eauto|subst;simpl; unfold ql; lia]);
  try (eapply closedty_extend; [eauto|subst;simpl; unfold ql; lia]).




(* derived forms of app rule *)

Lemma t_app_plain: forall env f t T1 T2 p frf qf q1 ar2 fr2 q2 q1' q2',
    has_type env f (TFun T1 false false q1 T2 false ar2 fr2 q2) p frf qf->
    has_type env t T1 p false q1' ->
    closed_ty (length env) T2 ->
    closed_ql (length env) q2' ->
    psub (plift q1') (plift q1) ->
    psub (plift q2) (plift p) ->   (* this is necessary (so far!) *)
    psub (plift q2') (plift p) ->   (* this is necessary (so far!) *)
    psub (plift (qor (qif ar2 q1') q2)) (plift q2') ->
    has_type env (tapp f t) T2 p fr2 q2'.
Proof.
  intros. eapply t_sub_stp. eapply t_app. eauto. eauto.
  simpl. unfoldq. intuition. eauto.
  rewrite qif_false, qor_emptyl.
  eapply stp_qs. eauto. eapply qs_sub. eauto.
  rewrite plift_closed' in *. unfoldq. intuition.
  eauto. intros ?. destruct ar2; simpl in *; eauto.
  eauto.
  Unshelve. apply true.
Qed.


(* basic syntactic sugar for let *)

Definition tlet e1 e2 := tapp (tabs e2) e1.

Lemma t_let_plain: forall env t1 t2 p T1 q1 T2 ar2 fr2 q2 q2' q2'',
    has_type env t1 T1 p false q1 ->
    has_type ((T1, false, qand p q1)::env) t2 T2 (qor p (qone (length env))) fr2 q2' ->
    q2' = qor q2 (qif ar2 (qone (length env))) ->
    q2'' = qor q2 (qif ar2 q1) ->
    closed_ty (length env) T2 ->
    closed_ql (length env) q2 ->
    closed_ql (length env) p ->
    telescope env ->
    psub (plift q1) (plift p) -> (* shouldn't be necessary *)
    psub (plift q2) (plift p) ->
    has_type env (tlet t1 t2) T2 p fr2 q2''.
Proof.
  intros. subst. unfold tlet.
  eapply t_app_plain. 2: eapply H.
  eapply t_abs with (fn1:=false) (fn2:=false) (ar2:=ar2) (q1:=q1) (* q1 := pand p q1 *)(qf:=p) (q2:=q2).
  qsimpl. rewrite qand_sub in H0.
  eapply H0.
  eauto. eauto. (* q1 < p *)
  eapply hast_closed. eauto. eauto.
  eauto.
  eapply hast_closed. eauto. eauto.
  eauto.
  eauto.
  eauto.
  destruct ar2; crush. crush. crush.
  destruct ar2; crush. crush.
Qed.


Lemma t_let_fresh: forall env t1 t2 p T1 q1 T2 ar2 fr2 q2,
    has_type env t1 T1 p true q1 ->
    has_type ((T1, true, qand p (vars_trans_fix env q1))::env) t2 T2 (qor p (qone (length env))) fr2 (qor q2 (qif ar2 (qone (length env)))) ->
    closed_ty (length env) T2 ->
    closed_ql (length env) q2 ->
    closed_ql (length env) p ->
    closed_ql (length env) (vars_trans_fix env q1) -> (* follows from line above and line below *)
    psub (plift (vars_trans_fix env q1)) (plift p) ->
    telescope env ->
    psub (plift q2) (plift p) ->
    has_type env (tlet t1 t2) T2 p (fr2 || ar2) (qor q2 (qif ar2 q1)).
Proof.
  intros. unfold tlet.
  eapply t_sub_stp. eapply t_app. 2: eapply H.
  eapply t_abs with (fn1:=false) (fn2:=false) (ar2:=ar2) (q1:=(vars_trans_fix env q1)) (qf:=p) (q2:=q2).
  qsimpl. rewrite qand_sub in H0.
  eapply H0.
  eauto. eauto. (* q1 < p *)
  eapply hast_closed. eauto. eauto.
  eauto.
  eauto.
  eauto.
  eauto.
  simpl. intros ? (? & Q). eapply Q.
  eauto.
  qsimpl. simpl. replace (ar2 && true) with ar2. 2: eauto with bool.
  rewrite qor_comm. rewrite orb_comm.
  eapply stp_refl; eauto.
  destruct ar2; crush. eapply hast_closed; eauto.
  destruct ar2; crush. eapply H5. rewrite plift_vt. left. eauto. eauto.
  Unshelve.
  apply true.
Qed.


Lemma t_var_plain: forall x env T p q,
    indexr x env = Some (T, false, q) ->
    (plift p) x ->
    closed_ty (length env) T ->
    closed_ql x q ->
    psub (plift q) (plift p) ->
    has_type env (tvar x) T p false q.
Proof.
  intros. eapply t_sub_stp. eapply t_var. eauto. eauto.
  eapply stp_qs. eauto.
  replace q with (qor (qdiff (qone x) (qone x)) q).
  eapply qs_var. crush. crush.
  eauto.
  crush. subst. eapply indexr_var_some' in H.
  eauto.
  crush. eapply H2 in H4. eapply indexr_var_some' in H. unfold tenv in *.
  assert (x0 < length env). lia. eauto.
  replace (qdiff (qone x) (qone x)) with qempty. crush.
  eapply functional_extensionality. intros.
  unfold qempty, qdiff, qone. crush.
  unfold bsub. eauto.
  crush.
  Unshelve.
  apply true.
Qed.




(* box (single-element pair) *)

Definition tboxf z := tabs(*a:A*) (tabs(*f:A=>A*) (tapp (tvar (1+z)) (tvar z))).

Definition tbox z a := tapp (tboxf z) a.

Definition tunbox z b := tapp b (tabs(*a:A*) (tvar z)).


Definition TFun_pure T1 q1 T2 q2 := TFun T1 false false q1 T2 false false false q2.

Definition TFun_pure_fn1 T1 q1 T2 q2 := TFun T1 true false q1 T2 false false false q2.

Definition TFun_pure_ar2 T1 q1 T2 q2 := TFun T1 false false q1 T2 false true false q2.



(* fully transparent boxes: no use of self types, freshness, etc. *)

Definition TBox_transparent A a := (TFun_pure (TFun_pure A a A a) a A a).

Definition TBoxf_transparent A a := (TFun_pure A a (TBox_transparent A a) a).


Lemma t_boxf_transparent: forall env p A a,
    closed_ty (length env) A ->
    closed_ql (length env) a ->
    psub (plift a) (plift p) ->
    has_type env (tboxf (length env)) (TBoxf_transparent A a) p false a.
Proof.
  intros. unfold ql in *.

  eapply t_abs. {
    qsimpl. remember (_ :: env) as env1.
    replace (1+length env) with (length env1).
    (* note: check t_abs with unrestricted p, then cast it down *)
    2: { subst. eauto. }
    eapply t_sub_stp.
    2: { eapply stp_qs with (fr1:=false) (q1:=qor a (qone (length env))). closed.
         eapply qs_trans. eapply qs_var with (x:=length env).
         crush. 2: { subst. eapply indexr_head. }
              crush. crush. simpl in *. eapply H0 in H3.
         subst env1. simpl. lia.
         subst env1. unfold ql. simpl. lia.
         crush. subst env1. simpl. eapply H0 in H2. lia.
         eapply qs_sub. crush.
         crush. eapply H0 in H3. subst env1. simpl. lia.
         eapply H0 in H3. subst env1. simpl. lia.
         crush. eapply H0 in H2. subst. simpl. lia.
         unfold bsub. eauto.
    }

    eapply t_abs. {
      qsimpl. remember (_::env1) as env2.
      eapply t_app_plain. {
        eapply t_var_plain. subst env2. eapply indexr_head.
        crush. closed. crush. subst env1. simpl. eapply H0 in H2. lia.
        crush.
      } {
        eapply t_var_plain. subst. rewrite indexr_skip.
        eapply indexr_head. eauto.
        crush. closed. crush. crush.
      }
      all: closed; crush.
    }
    all: closed; crush.
    all: subst; simpl; crush.
  }
  all: closed; crush.
  Unshelve. apply true.
Qed.

Lemma t_box_transparent: forall env t p A a,
    has_type env t A p false a ->
    closed_ty (length env) A ->
    closed_ql (length env) a ->
    psub (plift a) (plift p) ->
    has_type env (tbox (length env) t) (TBox_transparent A a) p false a.
Proof.
  intros. unfold ql in *.

  eapply t_app_plain. {
    eapply t_boxf_transparent. eauto. eauto. eauto.
  } {
    eauto.
  }
  all: closed; crush.
Qed.

Lemma t_unbox_transparent: forall env t p A a b,
    has_type env t (TBox_transparent A a) p false b ->
    closed_ty (length env) A ->
    closed_ql (length env) a ->
    closed_ql (length env) p ->
    psub (plift a) (plift p) ->
    has_type env (tunbox (length env) t) A p false a.
Proof.
  intros. unfold tenv, ql in *.

  eapply t_app_plain with (q1':=a). {
    eauto.
  } {
    eapply t_abs. {
      qsimpl. remember (_::env) as env1.
      eapply t_var_plain. subst. eapply indexr_head.
      crush. closed. crush. crush.
    }
    all: closed; crush.
  }
  closed.
  all: crush.
Qed.


(*
  let a = Ref(0)
  ---
  let b = Box(a)    : Box(Ref^a)^b
  let c = unbox(b)  : Ref^a
*)

Lemma ex_box_unbox_transparent1:
    has_type
      [(TRef (TBool), true, qempty)]
      (tlet (tbox 1 (tvar 0))
         (tunbox 2 (tvar 1)))
      (TRef (TBool))
      (qone 0)
      false
      (qone 0).
Proof.
  eapply t_let_plain. {
    eapply t_box_transparent. {
      eapply t_var. simpl. eauto. crush.
    }
    closed.
    crush. simpl. lia.
    crush.
  } {
    eapply t_unbox_transparent with (a:=qone 0). {
      eapply t_var. simpl. eauto.
      crush.
    }
    all: crush.
    closed.
    all: simpl in *; lia.
  }
  crush. crush.
  closed.
  crush. simpl. lia.
  crush. simpl. lia.
  all: crush.
  (* telescope *)
  intros ? ? ? ? ?.
  destruct x. simpl in *. inversion H. subst. intuition. constructor. constructor.
  intros ? Q. inversion Q. simpl in H. inversion H.
Qed.

(*
  let a = Ref(0)
  let b = Box(a)    : Box^a
  b                 : Box(Ref^a)^b  -->  Box(Ref^self)^b
*)


(* opaque fun: empty qualifiers, arg depends on fun, res depends on arg *)
Definition TFun_opaque T1 T2 := TFun T1 true false qempty T2 false true false qempty.

Definition TBox_opaque A := (TFun_opaque (TFun_opaque A A) A).


Lemma t_unbox_opaque1: forall env p A a,
    closed_ty (length env) A ->
    closed_ql (length env) a ->
    closed_ql (length env) p ->
    psub (plift a) (plift p) ->
    plift p (length env) ->
    has_type
      (((TBox_opaque A),false,a)::env)
      (tunbox (1+length env) (tvar (length env))) A p false a.
Proof.
  intros. unfold tenv, ql in *.

  eapply t_sub_stp. (* upcast at the end -- this is the truly opaque case,
                       always using the entire outer qualifier of the box *)
  eapply t_app. {
    eapply t_var_plain. eapply indexr_head. eauto. closed. all: crush.
  }
  2: { simpl. left. intuition. eexists. intuition. rewrite plift_one. intros ? Q. eauto. }
  {
    eapply t_abs. {
      qsimpl.
      eapply t_var. eapply indexr_head.
      crush.
    }
    all: crush.
    closed. closed. subst. simpl. unfold ql. lia.
  }
  crush.
  eapply stp_qs. closed. eapply qs_trans. eapply qs_var.
  3: { eapply indexr_head. }
  crush. crush. crush. subst. simpl. unfold ql. lia.
  crush. simpl. eapply H0 in H4. lia.
  eapply qs_sub. crush. crush. eapply H0 in H5. simpl. lia.
  crush. eapply H0 in H4. simpl. lia.
  unfold bsub. eauto. eauto.
  Unshelve. apply true.
Qed.




(* ----- second implementation, refined type signature ----- *)


(* transparent -> opaque box upcast via typing  *)

(*  Transparent:

        p^a : (f^p*: x:A^a -> A^f) -> A^f

    Opaque:

        p^* : (f^*: x:A^* -> A^x) -> A^fp



   x:A^* -> A^x   <:  x:A^a -> A^f)


        x:A^* -> A^x  (opaque inner)
    <:  x:A^a -> A^f  (transp inner)

   potential intermediate steps:

                q1 < vf | q2 < qf | none  <-- side conditions

        A^* -> A^x    ^0    ^0    ^0
        A^a -> A^x    ^a!   ^0    ^0
        A^a -> A^a    ^a    ^a!   ^0
        A^a -> A^f    ^a    ^a    ^a!

 *)



(* f^a(g^⧫f(x: A^a -> A^g) -> A^g) *)

(* A^a -> B^f *)
Definition TFun_trans_inner A a B := TFun A false false a B true false false qempty.

(* A^f* -> B^f *)
Definition TFun_trans_inner_ignore A B := TFun A true true qempty B true false false qempty.

(* A^f* -> B^x *)
Definition TFun_trans_outer A B := TFun A true true qempty B false true false qempty.


(* f^a(g^∅(x: A^⧫g -> A^xg) -> A^f) *)
Definition TFun_opaque_inner A B := TFun A true true qempty B true true false qempty.

Definition TFun_opaque_outer A B := TFun A true true qempty B true true false qempty.


Definition TBox_transparent2 A a := TFun_trans_outer (TFun_trans_inner A a A) A.

Definition TBoxf_transparent2 A a := (TFun_pure A a (TBox_transparent2 A a) a).



Lemma t_boxf_transparent2: forall env p A a,
    closed_ty (length env) A ->
    closed_ql (length env) a ->
    psub (plift a) (plift p) ->
    has_type env (tboxf (length env)) (TBoxf_transparent2 A a) p false a.
Proof.
  intros. unfold ql in *.

  eapply t_abs. {
    qsimpl. remember (_ :: env) as env1.
    replace (1+length env) with (length env1).
    (* note: check t_abs with unrestricted p, then cast it down *)
    2: { subst. eauto. }
    eapply t_sub_stp.
    2: { eapply stp_qs with (fr1:=false) (q1:=qor a (qone (length env))). closed.
         crush. crush. crush.
         eapply qs_trans. eapply qs_var with (x:=length env).
         crush. 2: { subst. eapply indexr_head. }
              crush. crush. simpl in *. eapply H0 in H3.
         subst env1. simpl. lia.
         subst env1. unfold ql. simpl. lia.
         crush. subst env1. simpl. eapply H0 in H2. lia.
         eapply qs_sub. crush.
         crush. eapply H0 in H3. subst env1. simpl. lia.
         eapply H0 in H3. subst env1. simpl. lia.
         crush. eapply H0 in H2. subst. simpl. lia.
         unfold bsub. eauto.
    }
    eapply t_abs with (ar2:=true). {
      qsimpl. remember (_::env1) as env2.
      eapply t_sub_stp.
      eapply t_app. {
        subst env2.
        eapply t_var. rewrite indexr_head.
        crush. crush.
      } {
        eapply t_var_plain. subst. rewrite indexr_skip.
        eapply indexr_head. eauto.
        crush. closed. crush. crush.
      }
      simpl. crush. (* x0 < a *) crush. (* use q1 qualifier *)
      qsimpl.
      eapply stp_refl. closed. crush. subst. simpl. unfold ql. lia.
      crush.
    }
    all: crush.
    closed. crush.
    closed. eapply H0 in H3. subst. simpl. lia. subst. simpl. unfold ql. lia.
  }
  all: crush.
  closed.
  all: crush.
  Unshelve.
  apply true.
  apply true.
Qed.

Lemma t_box_transparent2: forall env t p A a,
    has_type env t A p false a ->
    closed_ty (length env) A ->
    closed_ql (length env) a ->
    psub (plift a) (plift p) ->
    has_type env (tbox (length env) t) (TBox_transparent2 A a) p false a.
Proof.
  intros. unfold ql in *.

  eapply t_app_plain. {
    eapply t_boxf_transparent2. eauto. eauto. eauto.
  } {
    eauto.
  }
  all: closed; crush.
Qed.

Lemma t_unbox_transparent2: forall env t p A a b,
    has_type env t (TBox_transparent2 A a) p false b ->
    closed_ty (length env) A ->
    closed_ql (length env) a ->
    closed_ql (length env) p ->
    psub (plift a) (plift p) ->
    has_type env (tunbox (length env) t) A p false a.
Proof.
  intros. unfold tenv, ql in *.

  eapply t_sub_stp.
  eapply t_app. {
    eauto.
  }
  2: { simpl. eauto. }
  {
    (* eapply t_sub_stp with (T1:=(TFun_transparent3 A a A)) (fr1:=false) (q1:=a). *)

    eapply t_abs with (qf:=a) (fn1:=false) (fr1:=false) (fn2:=true) (ar2:=false). {
      remember (_::env) as env1.
      eapply t_sub_stp.
      eapply t_var_plain. subst. eapply indexr_head.
      crush. closed. crush. crush.
      eapply stp_qs. closed. eapply qs_sub. crush. crush.
      eapply H1 in H4. subst. simpl. lia.
      crush. eapply H1 in H4. subst. simpl. lia.
      unfold bsub. eauto. crush.
    }
    crush.
    closed. closed.
    crush.
    crush.
    crush.
  }
  crush. crush.
  eapply stp_refl. closed. crush. eauto.
  Unshelve.
  apply true.
  apply true.
Qed.


(*
  let a = Ref(0)
  ---
  let b = Box(a)    : Box(Ref^a)^b
  let c = unbox(b)  : Ref^a
*)

Lemma ex_box_unbox_transparent2:
    has_type
      [(TRef (TBool), true, qempty)]
      (tlet (tbox 1 (tvar 0))
         (tunbox 2 (tvar 1)))
      (TRef (TBool))
      (qone 0)
      false
      (qone 0).
Proof.
  eapply t_let_plain. {
    eapply t_box_transparent2. {
      eapply t_var. simpl. eauto. crush.
    }
    closed.
    crush. simpl. lia.
    crush.
  } {
    eapply t_unbox_transparent2 with (a:=qone 0). {
      eapply t_var. simpl. eauto.
      crush.
    }
    all: crush.
    closed.
    all: simpl in *; lia.
  }
  crush. crush.
  closed.
  crush. simpl. lia.
  crush. simpl. lia.
  all: crush.
  (* telescope *)
  intros ?. intros. destruct x; simpl in *.
  inversion H. subst. intuition. constructor. constructor. intros ? Q. inversion Q.
  inversion H.
Qed.

(*
  let a = Ref(0)
  let b = Box(a)    : Box^a
  b                 : Box(Ref^a)^b  -->  Box(Ref^self)^b
*)





Definition TBox_opaque2 A := TFun_opaque_outer (TFun_opaque_inner A A) A.

Lemma t_unbox_opaque2: forall env t p A a,
    has_type env t (TBox_opaque2 A) p false a ->
    closed_ty (length env) A ->
    closed_ql (length env) a ->
    closed_ql (length env) p ->
    psub (plift a) (plift p) ->
    has_type env (tunbox (length env) t) A p false a.
Proof.
  intros. unfold tenv, ql in *.

  eapply t_sub_stp.
  eapply t_app. {
    eauto.
  }
  2: { simpl. split.  }
  {
    (* eapply t_sub_stp with (q1:= qempty). *)
    eapply t_abs with (fn1:=true) (ar2:=true). {
      qsimpl. remember (_::env) as env1.
      eapply t_var. subst. eapply indexr_head.
      crush.
    }
    all: crush.
  }
  crush.
  qsimpl. eapply stp_refl.
  all: crush.
Unshelve.
  apply true.
Qed.




(*  Transparent:

        p^a : (f^p*: x:A^a -> A^f) -> A^f

    Opaque:

        p^* : (f^*: x:A^* -> A^x) -> A^fp



   x:A^* -> A^x   <:  x:A^a -> A^f)

*)


(* syntactic version of sem_stp_fun_box_outer

    sem_stp0 G p (TFun_trans_outer A a) fr1 q1 (TFun_opaque_outer A) fr1 q2.

*)

Lemma upcast_box: forall env e2 fr,
    env = [e2;(TRef TBool, true, qempty)] ->
    stp env (qor (qone 0) (qone 1)) true
      (TBox_transparent2 (TRef TBool) (qone 0)) fr (qone 0)
      (TBox_opaque2 (TRef TBool)) fr (qone 0).
Proof.
  intros.
  unfold TBox_transparent2, TBox_opaque2.

  (*
  stp env (qor (qone 0) (qone 1))
    (TFun_any
       (TFun
          (TRef TBool) true false (qone 0)        // arg: drop (qone 0)
          (TRef TBool) true false false qempty)   // res: reach fun
       (TRef TBool)) fr (qone 0)
    (TFun_any
       (TFun
          (TRef TBool) true false qempty
          (TRef TBool) false true false qempty)   // res: reach arg
       (TRef TBool)) fr (qone 0)
*)

  eapply s_trans.
  eapply s_fun_expand_arg with (q1b := qone 0).
  1,2: closed. 1,2: constructor.
  1-4: intro; subst; unfold qone, qempty; simpl; intro; try apply Nat.eqb_eq in H; lia.
  intuition.
  eapply s_fun_non_drop_grow; unfold bsub; simpl; auto.
  eapply s_fun_fresh_arg_to_self_res with (q1a := qone 0); eauto.
  closed. crush. crush.
  subst. simpl. lia. crush.
  subst. simpl. lia.
  crush. crush. crush.
  eapply s_refl. closed. crush.
  subst. simpl. lia.
  unfold bsub. eauto.
  eapply s_refl. closed. crush.
  eapply qs_sub. crush. crush. subst. simpl. lia. crush. subst. simpl. lia.
  apply qs_sub. all: crush; subst; simpl; lia.
Unshelve.
  apply true.
Qed.


Lemma ex_escape1:
  has_type
    []
    (tlet (tref ttrue)
       (tlet (tbox 1 (tvar 0))
          (tvar 1)))
    (TBox_opaque2 (TRef (TBool)))
    qempty
    true
    qempty.
Proof.
  eapply t_sub_stp. {
    eapply t_let_fresh with (q1:=qempty) (ar2:=true) (T2:=TBox_opaque2 (TRef (TBool))). { (* outer let *)
      eapply t_ref. eapply t_true.
    } {
      (* remember ([(_,_,_)]) as env. *)
      simpl. qsimpl. eapply t_let_plain with (q1:=qone 0). { (* inner let *)
        eapply t_sub_stp. eapply t_box_transparent2. {
          eapply t_var. simpl. eauto. crush.
        }
        closed. crush. simpl. crush. crush.
        eapply stp_refl. all: crush. closed. 1,2,5: closed.
        all: crush; simpl; try lia.
      } {
        remember ([(_,_,_);(_,_,_)]) as env.
        simpl in *. rewrite qand_same in *.
        eapply t_sub_stp. {
          eapply t_var_plain. subst env. simpl. eauto.
          all: crush.
          closed. closed. closed.
          all: crush.
          subst. simpl. lia.
          closed. unfold qone. intros ? Q. bdestruct (x =? 0). lia. lia.
        } { (* stp transparent <: opaque *)
          eapply upcast_box. eauto.
        }
        crush.
      }
      crush. crush.

      { closed. 1,2,5: closed. all: crush; simpl; lia. }

      crush. simpl. lia.
      crush. simpl. lia.
      2: crush.
      2: crush.
      (* telescope *)
      intros ?. intros. destruct x; simpl in *.
      inversion H. subst. intuition. closed. intros ? Q. inversion Q.
      inversion H.
    }

    { closed. 1,2,5: closed. all: crush. }

    all: crush.
    intros ?????. inversion H.
  } { (* stp refl *)
    eapply stp_refl. closed. 1,2,5: closed. all: crush.
  }
  crush.
  Unshelve.
  apply true.
  apply true.
Qed.





(* TODO: pairs *)

Definition tpairf z := tabs(*a:A*) (tabs(*b:B*) (tabs(*f:A=>B=>C*) (tapp (tapp (tvar (2+z)) (tvar z)) (tvar (1+z))))).

Definition tpair z a b := (tapp (tapp (tpairf z) a) b).

Definition tfst z p := tapp p (tabs(*a:A*) (tabs(*b:B*) (tvar z))).

Definition tsnd z p := tapp p (tabs(*a:A*) (tabs(*b:B*) (tvar (1+z)))).

Definition TPair_opaque A := TFun_opaque_outer (TFun_opaque_inner A (TFun_opaque_inner A A)) A.

Definition TPair_trans A a b := TFun_trans_outer (TFun_trans_inner A a (TFun_trans_inner A b A)) A.

Definition TPair_trans_fst A a := TFun_trans_outer (TFun_trans_inner A a (TFun_trans_inner_ignore A A)) A.

Definition TPair_trans_snd A b := TFun_trans_outer (TFun_trans_inner_ignore A (TFun_trans_inner A b A)) A.

Definition TMaker A a B := TFun A false false a B true true false qempty.

Definition TPairf_trans A a1 a2 := TMaker A a1 (TMaker A a2 (TPair_trans A a1 a2)).

(*
opaque:
  f₁^∅(a: A^⧫f₁ -> f₂^a(b: A^⧫f₂ ->
    f₃^bf₂( g₁^∅(a: A^⧫g₁ -> g₂^ag₁(b: A^⧫g₂ -> A^bg₂)) -> A^f₃ )
  ))
  fst(TR): ^a(x: A^a -> A^⧫ -> A^x)  ; this way we avoid polluting function qualifier with B
transparent:
  f₁^∅(A^a -> f₂^a(A^b ->
    f₃^ab( g₁^⧫f₃(A^a -> g₂^g₁(A^b -> A^g₂)) -> A^g₁ )
  ))
  fst: g^a(A^a -> f^g(A^b -> A^f))
  snd: g^b(A^a -> ...)  ;TR: not sure if we can type this
*)

Lemma t_pairf_transparent: forall env p A a1 a2,
    closed_ty (length env) A ->
    closed_ql (length env) a1 ->
    closed_ql (length env) a2 ->
    psub (plift a1) (plift p) ->
    psub (plift a2) (plift p) ->
    has_type env (tpairf (length env)) (TPairf_trans A a1 a2) p false (qor a1 a2).
Proof.
  intros. unfold ql in *.

  eapply t_abs; try crush.
  2: repeat (apply c_fun; try crush).
  assert (psub (plift (qor a1 a2)) (plift p)).
  crush.
  replace (qand p (qor a1 a2)) with (qor a1 a2).
  2: crush.
  eapply t_abs; try crush.
  2: { eapply closedty_extend. exact H. crush. }
  2: { eapply closedty_extend. apply c_fun. 2: exact H. apply c_fun. 2: apply c_fun. all: crush. }
  2-5: simpl; try (rewrite H7 || rewrite H6); crush.
  replace (qor (qand a1 a2) a2) with a2.
  2: rewrite qor_sub_id; crush.
  eapply t_abs; try crush.
  3: { eapply closedty_extend. exact H. crush. }
  2: { eapply closedty_extend. apply c_fun. exact H. apply c_fun. all: crush. }
  2-5: simpl; try (rewrite H6 || rewrite H5); crush.
  eapply t_sub_stp.
  3: crush.
  eapply t_app.
  eapply t_app.
  replace (2 + length env) with (length ((A, false, a2) :: (A, false, a1) :: env)) at 1.
  2: crush.
  eapply t_var.
  apply indexr_head.
  crush.
  apply t_var_plain.
  rewrite indexr_skip.
  rewrite indexr_skip.
  apply indexr_head.
  1,2: simpl; intuition.
  crush.
  eapply closedty_extend.
  exact H.
  simpl; intuition.
  1,2,3,4,7: crush.
  apply t_var_plain.
  replace (1 + length env) with (length ((A, false, a1) :: env)) at 1.
  2: crush.
  rewrite indexr_skip.
  apply indexr_head.
  simpl; intuition.
  1,4: crush.
  eapply closedty_extend.
  exact H.
  simpl; crush.
  replace (1 + length env) with (length ((A, false, a1) :: env)) at 1.
  2: crush.
  crush; simpl; intuition.
  crush.
  simpl.
  crush.
  apply s_refl; crush.
  eapply closedty_extend.
  exact H.
  simpl; intuition.
  rewrite H5; intuition.
Unshelve.
  apply true.
Qed.

Lemma t_pair_transparent: forall env p t1 t2 A a1 a2,
    has_type env t1 A p false a1 ->
    has_type env t2 A p false a2 ->
    closed_ty (length env) A ->
    closed_ql (length env) a1 ->
    closed_ql (length env) a2 ->
    psub (plift a1) (plift p) ->
    psub (plift a2) (plift p) ->
    has_type env (tpair (length env) t1 t2) (TPair_trans A a1 a2) p false (qor a1 a2).
Proof.
  intros; unfold ql in *.
  eapply t_sub_stp.
  3: crush.
  eapply t_app.
  eapply t_app.
  apply t_pairf_transparent.
  exact H1.
  7,10: crush.
  all: simpl.
  9: repeat rewrite qif_true.
  5: exact H.
  6: exact H0.
  exact H2.
  exact H3.
  all: crush.
  simpl.
  replace (qor (qor a1 a2) a1) with (qor a1 a2).
  replace (qor (qor a1 a2) a2) with (qor a1 a2).
  2,3: symmetry; rewrite qor_comm; apply qor_sub_id; crush.
  apply s_refl.
  repeat apply c_fun.
  all: crush.
Unshelve.
  apply true.
Qed.


(* typing of fst p -- spelling out intermediate steps for clarity, though not strictly needed *)

Lemma aux1: forall env p fr A b,
    closed_ty (length env) A ->
    closed_ql (length env) b ->
    psub (plift b) (plift p) ->
    stp env p false
      (TFun_trans_inner_ignore A A) fr qempty
      (TFun_trans_inner A b A) fr qempty.
Proof.
  intros. eapply s_fun_fresh_arg_to_self_res; eauto. 
  crush. crush. crush. crush.
  eapply s_refl; eauto.
  unfold bsub. eauto.
Qed.

Lemma aux2: forall env p fr A a b,
    closed_ty (length env) A ->
    closed_ql (length env) a ->
    closed_ql (length env) b ->
    psub (plift b) (plift p) ->
    stp env p false
      (TFun_trans_inner A a (TFun_trans_inner_ignore A A)) fr qempty
      (TFun_trans_inner A a (TFun_trans_inner A b A)) fr qempty.
Proof.
  intros. eapply s_fun. eapply s_refl; eauto.
  eapply aux1; eauto.
  all: unfold bsub; eauto.
  eapply qs_sub; crush. 
Qed.

Lemma t_pair_to_fst: forall env p A a b fr,
    closed_ty (length env) A ->
    closed_ql (length env) a ->
    closed_ql (length env) b ->
    psub (por (plift a) (plift b)) (plift p) ->
    stp env p true (TPair_trans A a b) fr (qor a b) (TPair_trans_fst A a) fr (qor a b). 
Proof.
  intros. 
  eapply s_fun. simpl. eapply aux2; eauto. crush.
  simpl. eapply s_refl; eauto. crush. 
  all: unfold bsub; eauto.
  eapply qs_sub; crush.
Unshelve.
  eapply false.
Qed.


Lemma t_fstf: forall env p A a,
    psub (plift a) (plift p) ->
    closed_ty (length env) A ->
    closed_ql (length env) a ->
    has_type env
      (tabs(*a:A*) (tabs(*b:B*) (tvar (length env))))
      (TFun_trans_inner A a (TFun_trans_inner_ignore A A))
      p false a.
Proof.
  intros. unfold tenv, ql in *.
  eapply t_abs with (qf:=a). {
    qsimpl. remember (_ :: env) as env1.
    (* inner tabs needs to use x, so it'll become part of
       inner qf -- we can remove it via subtyping *)
    eapply t_sub_stp with
      (T1 := (TFun_trans_inner_ignore A A))
      (q1 := qor a (qone (length env))). {
      eapply t_abs. {
        qsimpl. remember (_ :: env1) as env2.
        eapply t_sub_stp. {
          eapply t_var_plain.
          subst env2 env1. rewrite indexr_skip, indexr_head. crush.
          simpl. lia.
          2: closed.
          all: crush.
        }
        eapply stp_qs. closed. eapply qs_sub. crush. crush.
        subst. simpl. crush.
        subst. rewrite plift_closed'. crush. simpl. crush. simpl. unfold tenv, ql. lia.
        unfold bsub. eauto.
        crush.
      }
      2,3: closed.
      all: crush. 
      all: subst; simpl; crush.
    } {
      eapply stp_qs. closed. crush. crush.
      eapply qs_trans. eapply qs_var with (x:=length env).
      3: { subst. rewrite indexr_head. eauto. }
      5: { eapply qs_sub. all: crush. all: subst; simpl; crush. }
      all: crush.
      all: subst; simpl; crush. 
      unfold bsub. eauto. 
    }
    crush.
  }
  2,3: closed.
  all: crush. 
Unshelve.
  eapply false.
  eapply false. 
Qed.


Lemma t_fst_transparent: forall env p t A a1 a2,
    has_type env t (TPair_trans A a1 a2) p false (qor a1 a2) ->
    closed_ty (length env) A ->
    closed_ql (length env) a1 ->
    closed_ql (length env) a2 ->
    psub (plift a1) (plift p) ->
    psub (plift a2) (plift p) ->
    has_type env (tfst (length env) t) A p false a1.
Proof.
  intros. unfold tenv, ql in *. 
  eapply t_sub_stp. {
    eapply t_app. {
      eapply t_sub_stp.
      eapply H. 
      eapply t_pair_to_fst; eauto.
      crush. crush. 
    } {
      eapply t_fstf; eauto.
    }
    all: crush.
  }
  simpl. qsimpl. eapply s_refl; eauto.
  crush.
Unshelve.
  eapply false. 
Qed.


Lemma t_snd_transparent: forall env p t A a1 a2,
    has_type env t (TPair_trans A a1 a2) p false (qor a1 a2) ->
    closed_ty (length env) A ->
    closed_ql (length env) a1 ->
    closed_ql (length env) a2 ->
    psub (plift a1) (plift p) ->
    psub (plift a2) (plift p) ->
    has_type env (tsnd (length env) t) A p false a2.
Proof.
  intros.
  eapply t_sub_stp.
  eapply t_app with (frx := false) (qx := a2).
  assert (has_type env t (TPair_trans_snd A a2) p false (qor a1 a2)). {
    eapply t_sub_stp.
    apply H.
    2: crush.
    eapply s_fun.
    2: apply s_refl.
    10: apply qs_sub.
    2,3,10-12: crush.
    2-7: unfold bsub; eauto.
    simpl.
    eapply s_fun_fresh_arg_to_self_res.
    8: apply s_refl.
    closed.
    all: crush.
    unfold bsub.
    eauto.
  }
  exact H5. {
    apply t_abs; crush.
    2: closed; crush.
    apply t_abs; crush.
    apply t_var_plain; crush.
    replace (1 + length env) with (length ((A, true, a2) :: env)).
    apply indexr_head.
    crush.
    1-4: closed.
    apply H2 in H5.
    lia.
    all: simpl; intuition.
  }
  all: simpl; crush.
  apply s_refl.
  all: crush.
Unshelve.
  all: apply true.
Qed.


Lemma t_pair_trans_to_opaque: forall env p t A a1 a2,
    has_type env t (TPair_trans A a1 a2) p false (qor a1 a2) ->
    closed_ty (length env) A ->
    closed_ql (length env) a1 ->
    closed_ql (length env) a2 ->
    psub (plift a1) (plift p) ->
    psub (plift a2) (plift p) ->
    has_type env t (TPair_opaque A) p false (qor a1 a2).
Proof.
  intros.
  eapply t_sub_stp.
  apply H.
  2: crush.
  eapply s_trans.
  apply s_fun_expand_arg with (q1b := qor a1 a2). closed. 1-6: crush.
  eapply s_fun_non_drop_grow; unfold bsub; eauto.
  2: apply stp_refl. 2-9: crush. 2,3: apply qs_sub; crush.
  eapply s_trans. eapply s_fun_fresh_arg_to_self_res with (q1b := qor a1 a2).
  8: apply stp_refl. 7: intros ? ? ?; eauto. closed. 1-10: crush. unfold bsub; eauto.
  eapply s_trans. eapply s_fun. apply stp_qs with (q1 := a1). crush. apply qs_sub.
  crush. crush. crush. unfold bsub. eauto.
  eapply s_fun_fresh_arg_to_self_res with (q1b := a2).
  8: apply stp_refl. 7: intros ? ?; eauto. 1-9: crush. 1-7: unfold bsub; eauto.
  apply qs_sub. intros ? ?. eauto. crush. crush.
  apply s_fun_q2_to_fn2. 1-8: crush. closed. crush.
Unshelve.
  apply true.
Qed.


Lemma TPair_opaque_fst:  forall env p t A a,
    has_type env t (TPair_opaque A) p false a ->
    closed_ty (length env) A ->
    closed_ql (length env) a ->
    psub (plift a) (plift p) ->
    has_type env (tfst (length env) t) A p false a.
Proof.
  intros.
  eapply t_sub_stp.
  eapply t_app with (qx := qempty).
  apply H. {
    unfold TFun_opaque_inner.
    apply t_abs. {
      assert (psub (plift qempty) (plift p)).
      crush. qsimpl.
      apply t_abs. {
        qsimpl.
        eapply t_sub_stp.
        eapply t_var.
        rewrite indexr_skip, indexr_head.
        reflexivity.
        simpl; lia.
        2: {
          apply stp_qs.
          closed.
          apply qs_sub.
          all: crush.
          all: try (rewrite H4 || rewrite H5); intuition.
          unfold bsub; eauto.
        }
        all: crush.
      }
      all: crush.
      1-2: closed.
      rewrite H4; intuition.
    }
    3: closed.
    all: crush.
  }
  1,4: simpl.
  4: qsimpl; apply s_refl.
  all: crush.
Unshelve.
  all: apply true.
Qed.


Lemma TPair_opaque_snd:  forall env p t A a,
    has_type env t (TPair_opaque A) p false a ->
    closed_ty (length env) A ->
    closed_ql (length env) a ->
    psub (plift a) (plift p) ->
    has_type env (tsnd (length env) t) A p false a.
Proof.
  intros.
  eapply t_sub_stp.
  eapply t_app with (qx := qempty).
  apply H. {
    unfold TFun_opaque_inner.
    apply t_abs. {
      assert (psub (plift qempty) (plift p)).
      crush. qsimpl.
      apply t_abs. {
        qsimpl.
        eapply t_sub_stp.
        eapply t_var.
        replace (1 + length env) with (length ((A, true, qempty) :: env)).
        rewrite indexr_head.
        reflexivity.
        simpl; lia.
        2: {
          apply stp_qs.
          closed.
          apply qs_sub.
          all: crush.
          all: try (rewrite H4 || rewrite H5); intuition.
          unfold bsub; eauto.
        }
        all: crush.
      }
      all: crush.
      1-2: closed.
      rewrite H4; intuition.
    }
    3: closed.
    all: crush.
  }
  1,4: simpl.
  4: qsimpl; apply s_refl.
  all: crush.
Unshelve.
  all: apply true.
Qed.


End STLC.
