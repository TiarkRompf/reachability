(* Full safety for STLC *)

(*

An LR-based semantic soundness proof for STLC.

Step-indexed LR: soundness only, no termination.

Full higher-order mutable references (TRef T, for any T)

stlc_reach_ref_overlap_self_fresh_mut_tight.v + 
stlc_reach_ref_overlap_self_fresh_mut_nested_shallow.v



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
  | TRef   : ty -> bool -> ql -> ty
  | TFun   : ty -> bool -> bool -> ql ->
             ty -> bool -> bool -> bool -> ql ->
                   bool -> bool -> bool -> ql ->
             ty
.

(* 
     TRef
        T       : element type
        qrf     : element self ref (result of get needs to alias ref)
        q   

    TFun
        T1      : argument type

        q1fn    : argument may alias function?
        q1fr    : argument may be fresh?
        q1      : argument reachability qualifer (set of variables)

        T2      : result type

        q2fn    : result may alias function?
        q2ar    : result may alias argument?
        q2fr    : result may be fresh?
        q2      : result reachability qualifer (set of variables)

        e2fn    : effect on function?
        e2ar    : effect on argument?
        e2fr    : effect on fresh?
        e2      : effect reachability qualifer (set of variables)


*)

Inductive tm : Type :=
  | ttrue : tm
  | tfalse : tm
  | tvar : id -> tm
  | tref : tm -> tm
  | tget : tm -> tm
  | tput : tm -> tm -> tm
  | tapp : tm -> tm -> tm
  | tabs : tm -> tm
.

Inductive vl: Type :=
| vbool :  bool -> vl
| vref  :  id -> vl
| vabs  :  list vl -> tm -> vl 
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
| c_fun: forall m T1 T2 fn1 fr1 q1 fn2 ar2 fr2 q2 e2fn e2ar e2fr e2,
    closed_ty m T1 ->
    closed_ty m T2 ->   (* not dependent *)
    closed_ql m q1 ->
    closed_ql m q2 ->
    closed_ql m e2 ->
    closed_ty m (TFun T1 fn1 fr1 q1 T2 fn2 ar2 fr2 q2 e2fn e2ar e2fr e2)
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

Inductive has_type : tenv -> tm -> ty -> bool -> ql -> ql -> Prop :=
| t_true: forall env e,
    has_type env ttrue TBool false qempty e
| t_false: forall env e,
    has_type env tfalse TBool false qempty e
| t_var: forall x env T fr q e,
    indexr x env = Some (T, fr, q) ->
    has_type env (tvar x) T false (qone x) e
(* standard refs (shallow), purely driven by inner qualifier *)
| t_ref: forall t env T q e1,
    has_type env t T false q e1 ->
    psub (plift  q) (plift e1) ->
    psub (plift e1) (pdom env) ->
    has_type env (tref t) (TRef T false q) true qempty e1
| t_get: forall t env T fr q q1 e1,
    has_type env t (TRef T false q1) fr q e1 ->
    psub (plift q) (plift e1) -> (* effect *)
    has_type env (tget t) T false q1 e1
(* refs with self-ref (deep), accounted to outer qualifier *)
(* NOTE/TODO: there could be hybrids that account part to 
   inner/outer q -- what should a general rule look like? *)
| t_ref2: forall t env T q e,
   has_type env t T false q e ->
   psub (plift q) (plift e) ->
   has_type env (tref t) (TRef T true qempty) true q e
| t_ref_sub: forall t env T fr1 q1 fr2 q2 e2, (* upcast operation -- should move into subtyping *)
   has_type env t (TRef T fr1 q1) fr2 q2 e2 ->
   psub (plift q1) (plift e2) ->
   has_type env t (TRef T true qempty) fr2 (qor q2 q1) e2
| t_get2: forall t env T fr q e,
   has_type env t (TRef T true qempty) fr q e ->
   psub (plift q)(plift e) ->
   has_type env (tget t) T fr q e
(* put operation is shared *)
| t_put: forall t1 t2 env T fr2 fr1 q1 q2 e,
    has_type env t1 (TRef T fr2 q2) fr1 q1 e ->
    has_type env t2 T false q2 e ->
    psub (plift q1) (plift e) ->
    psub (plift q2) (plift e) ->
    has_type env (tput t1 t2) TBool false qempty e
| t_app: forall env f t T1 T2 frf e qf frx qx fn1 fr1 q1 fn2 ar2 fr2 q2 e2fn e2ar e2fr e2,
    has_type env f (TFun T1 fn1 fr1 q1 T2 fn2 ar2 fr2 q2 e2fn e2ar e2fr e2) frf qf e ->  
    has_type env t T1 frx qx e ->
    psub (plift e2) (plift e) ->   
    (e2fn = true -> psub (plift qf) (plift e)) -> 
    (e2ar = true -> psub (plift qx) (plift e)) -> 
    (* ---- different app cases: *)
    (if fn1 then
       if fr1 then
         True
       else
         (* fn1 /\ ~fr1: disabled tvar and tabs cases *)
         (* (frx = false /\ (exists x0, f = tvar x0 /\ psub (plift qx) (pone x0)) \/ *)
         (* (frx = false /\ (exists p0 t0, f = tabs p0 t0 /\ psub (plift qx) (plift p0))) \/ *)
         frx = false /\ psub (plift qx) (plift q1)
     else
       if fr1 then
         psub (pand 
                 (plift (vars_trans_fix env
                           (qor
                              (qif (e2fn||fn2) qf)
                              (qor e2 q2)))) (* need q2, too? *)
                 (plift (vars_trans_fix env (qif (e2ar||ar2) qx)))) (* ar2 needed? *)
           (plift q1)
           (* TODO: also support qx < q1! *)
       else
         frx = false /\ psub (plift qx) (plift q1)) ->
    (* ---- *)
    has_type env (tapp f t) T2
      (fn2 && frf || ar2 && frx || fr2)
      (qor (qif fn2 qf) (qor (qif ar2 qx) q2))
      e
| t_abs: forall env t T1 T2 fn1 fr1 q1 fn2 ar2 fr2 q2 e2fn e2ar e2fr e2 qf,
    has_type ((T1, fr1, (qor q1 (qif fn1 (qdom env))))::env) t T2 
      fr2
      (qor q2 (qor (qif fn2 qf) (qif ar2 (qone (length env)))))
      (qor e2 (qor (qif e2fn qf) (qif e2ar (qone (length env))))) ->
    (e2ar=true -> psub (plift q1) (plift e2)) ->  (* relax? need only if e2ar & q1fr *)
    (ar2=true -> psub (plift q1) (plift q2)) ->  (* relax? *)
    qf = qempty ->

    closed_ty (length env) T1 ->
    closed_ty (length env) T2 ->
    closed_ql (length env) q1 ->
    closed_ql (length env) q2 ->
    closed_ql (length env) e2 ->
    closed_ql (length env) qf ->
    has_type env (tabs t)
      (TFun T1 fn1 fr1 q1 T2 fn2 ar2 fr2 q2 e2fn e2ar e2fr e2)
      false qf qempty
| t_sub: forall env y T fr1 q1 e1 fr2 q2, (* TODO: e2 *)
    has_type env y T fr1 q1 e1 ->
    psub (plift q1) (plift q2) ->
    psub (plift q2) (pdom env)  ->
    has_type env y T (fr1 || fr2) q2 e1
| t_sub_var: forall env y T fr1 q1 qx x Tx e1, (* TODO: upcast e1 *)
    has_type env y T fr1 q1 e1 ->
    plift q1 x ->
    plift e1 x -> (* !!! ANNOYING we're only interested in upcasting q1 *)
    indexr x env = Some (Tx, false, qx) ->
    (* psub (plift qx) (plift p) ->  *)
    has_type env y T fr1 (qor (qdiff q1 (qone x)) qx) e1
| t_sub_escape: forall env T1 T2 t e q fr
        q1fn_a q1fr_a q1a 
        q2fn_a q2ar_a q2fr_a q2a
        e2fn_a e2ar_a e2fr_a e2a,
    has_type env t (TFun T1 q1fn_a q1fr_a q1a T2 q2fn_a q2ar_a q2fr_a q2a e2fn_a e2ar_a e2fr_a e2a) fr q e ->
    has_type env t (TFun T1 q1fn_a q1fr_a qempty T2 true (*q2fn_a*) q2ar_a q2fr_a qempty true (*e2fn_a*) e2ar_a e2fr_a qempty) fr (qor q (qor e2a q2a)) e
.

(* ---------- operational semantics ---------- *)

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
            | (dx, M', Some (Some (vabs _ _)))   => (1+dx, M', Some None)
            | (dx, M', Some (Some (vref x)))     => (1+dx, M', Some (indexr x M'))
          end
        | tput er ex    =>
          match teval n M env er with
            | (dr, M', None)                     => (1+dr, M', None)
            | (dr, M', Some None)                => (1+dr, M', Some None)
            | (dr, M', Some (Some (vbool _)))    => (1+dr, M', Some None)
            | (dr, M', Some (Some (vabs _ _)))   => (1+dr, M', Some None)
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
        | tabs y   => (1, M, Some (Some (vabs env y)))
        | tapp ef ex =>
          match teval n M env ef with
            | (df, M', None)                  => (1+df, M', None)
            | (df, M', Some None)             => (1+df, M', Some None)
            | (df, M', Some (Some (vbool _))) => (1+df, M', Some None)
            | (df, M', Some (Some (vref _)))  => (1+df, M', Some None)
            | (df, M', Some (Some (vabs env2 ey))) =>
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


(* value interpretation of terms *)
Definition tevaln M env e M' v :=
  exists nm,
  forall n,
    n > nm ->
    teval n M env e = (M', Some (Some v)).

Lemma eval_deterministic: forall m n, n < m -> forall S S1 H t n1 r j,
  teval n S H t = (n1, S1, Some r) -> j >= n -> (* alt: j >= n1 ? *)
  teval j S H t = (n1, S1, Some r).
Proof.
  intros m. induction m. intros. inversion H.
  intros. destruct n. inversion H1. destruct j. inversion H2.
  destruct t; simpl; simpl in H1; try eauto.
  - remember (teval n S H0 t) as tf. destruct tf as [[nf Sf] [rf|]].
    rewrite IHm with (n:=n) (n1:=nf) (r:=rf) (S1:=Sf).
    destruct rf; try destruct v; try solve [inversion H1; eauto].
    lia. eauto. lia.
    inversion H1. 
  - remember (teval n S H0 t) as tf. destruct tf as [[nf Sf] [rf|]].
    rewrite IHm with (n:=n) (n1:=nf) (r:=rf) (S1:=Sf).
    destruct rf; try destruct v; try solve [inversion H1; eauto].
    lia. eauto. lia.
    inversion H1. 
  - remember (teval n S H0 t1) as tf. destruct tf as [[nf Sf] [rf|]].
    rewrite IHm with (n:=n) (n1:=nf) (r:=rf) (S1:=Sf).
    destruct rf; try destruct v; try solve [inversion H1; eauto]. 
    remember (teval (n-nf) Sf H0 t2) as tx. destruct tx as [[nx Sx] [rx|]].
    rewrite IHm with (n:=n-nf) (n1:=nx) (r:=rx) (S1:=Sx).
    destruct rx; try solve [destruct v; inversion H1; eauto].
    eauto. lia. eauto. lia.
    inversion H1. inversion H1.
    lia. eauto. lia.
    inversion H1.
  - remember (teval n S H0 t1) as tf. destruct tf as [[nf Sf] [rf|]].
    rewrite IHm with (n:=n) (n1:=nf) (r:=rf) (S1:=Sf).
    destruct rf; try destruct v; try solve [inversion H1; eauto]. 
    remember (teval (n-nf) Sf H0 t2) as tx. destruct tx as [[nx Sx] [rx|]].
    rewrite IHm with (n:=n-nf) (n1:=nx) (r:=rx) (S1:=Sx).
    destruct rx; try solve [destruct v; inversion H1; eauto].
    remember (teval (n-nf-nx) Sx (v :: l) t) as ty. destruct ty as [[ny Sy] [ry|]].
    rewrite IHm with (n:=n-nf-nx) (n1:=ny) (r:=ry) (S1:=Sy).
    eauto. lia. eauto. lia.
    inversion H1. inversion H1.
    eauto. lia. eauto. lia.
    inversion H1.
    lia. eauto. lia.
    inversion H1.
Qed.

Lemma eval_bounded: forall m n, n < m -> forall S S1 H t n1 r,
    teval n S H t = (n1, S1, Some r) ->
    1 <= n1 /\ n1 <= n.
Proof.
  intros m. induction m. intros. inversion H.
  intros. destruct n. inversion H1.
  destruct t; simpl in *; inversion H1; try lia.
  - remember (teval n S H0 t) as tf. destruct tf as [[nf Sf] [rf|]]. 2: { inversion H1. }
    symmetry in Heqtf. eapply IHm with (n:=n) (n1:=nf) (r:=rf) in Heqtf as HF1. 2: lia.
    destruct rf. 2: { inversion H1. lia. } inversion H1. lia. 
  - remember (teval n S H0 t) as tf. destruct tf as [[nf Sf] [rf|]]. 2: { inversion H1. }
    symmetry in Heqtf. eapply IHm with (n:=n) (n1:=nf) (r:=rf) in Heqtf as HF1. 2: lia.
    destruct rf. 2: { inversion H1. lia. } destruct v; inversion H1; lia. 
  - remember (teval n S H0 t1) as tf. destruct tf as [[nf Sf] [rf|]]. 2: { inversion H1. }
    symmetry in Heqtf. eapply IHm with (n:=n) (n1:=nf) (r:=rf) in Heqtf as HF1. 2: lia.
    destruct rf. 2: { inversion H1. lia. } destruct v. inversion H1. lia.
    remember (teval (n-nf) Sf H0 t2) as tx. destruct tx as [[nx Sx] [rx|]]. 2: inversion H1.
    symmetry in Heqtx. eapply IHm in Heqtx as HX1. 2: lia.
    destruct rx. 2: { inversion H1. lia. }
    remember (indexr i Sx). destruct o. inversion H1. lia. inversion H1. lia. inversion H1. lia. 
  - remember (teval n S H0 t1) as tf. destruct tf as [[nf Sf] [rf|]]. 2: { inversion H1. }
    symmetry in Heqtf. eapply IHm with (n:=n) (n1:=nf) (r:=rf) in Heqtf as HF1. 2: lia.
    destruct rf. 2: { inversion H1. lia. } destruct v; inversion H1; try lia.
    remember (teval (n-nf) Sf H0 t2) as tx. destruct tx as [[nx Sx] [rx|]]. 2: inversion H1. 
    symmetry in Heqtx. eapply IHm in Heqtx as HX1. 2: lia.
    destruct rx. 2: { inversion H1. lia. } inversion H1. 
    remember (teval (n-nf-nx) Sx (v :: l) t) as ty. destruct ty as [[ny Sy] [ry|]].
    symmetry in Heqty. eapply IHm in Heqty as HY1. 2: lia. 2: inversion H1. 
    inversion H1. lia. 
Qed.


Lemma indexr_map: forall {A B C} (M: list (A * C)) x v (f: A -> B),
    indexr x M = v ->
    indexr x (map (fun '(vt, q) => (f vt,q)) M) = (match v with Some (v,q) => Some ((f v), q) | None => None end).
Proof.
  intros ? ? ? M. induction M; intros.
  simpl. destruct v; intuition. inversion H. 
  simpl in *. rewrite map_length.
  bdestruct (x =? length M). destruct a.  subst v. congruence. eauto.
Qed.

Lemma map_map: forall {A B C} (M: list A) (f: A -> B) (g: B -> C),
    map g (map f M) = map (fun vt => g(f(vt))) M.
Proof.
  intros ? ? ? M. induction M. intros. simpl. eauto.
  intros. simpl in *. rewrite IHM. eauto. 
Qed.

(*
Lemma map_map': forall {A B C D} (M: list (A * D)) (f: A -> B) (g: B -> C),
    map g (map f M) = map (fun '(vt, q) => (g(f(vt)), q)) M.
Proof.
  intros ? ? ? M. induction M. intros. simpl. eauto.
  intros. simpl in *. rewrite IHM. eauto. 
Qed.
*)

Lemma map_eq_f: forall {A B} (f1 f2: A -> B) M,
    f1 = f2 ->
    map f1 M = map f2 M.
Proof.
  intros. congruence.
Qed.


(* ---------- LR definitions  ---------- *)


(* Type approximation machinery:

    We want semantic types to represent sets of values, each
    coupled with a store typing.

    So roughly, the definitions should be like this:

      Definition vtype := stty -> vl -> Prop

      Definition stty := list vtype

    But this doesn't work due to the obvious circularity.
    Instead, we define an indexed approximation, i.e. roughly:

      Fixpoint vtypen (n+1) := list (vtypen n) -> vl -> Prop

    This again needs to be a little bit more flexible, so we
    settle on the definitions below.

*)

(* definition of indexed types and store typings *)
Fixpoint vtypen n: Type :=
  match n with
  | 0 => Prop
  | S n => forall (nx: nat) (M: list ((vtypen (n-nx)) * ql)) (v: vl)(q: ql), Prop
  end.

(* alternative:

  | S n => forall (j: nat) (M: list (vtypen (n-(n-j)))) (v: vl), Prop

 *)

Definition sttyn n := list ((vtypen n) * ql).

(* semantic types are the set of all finite approximations *)
Definition vtype := forall n, vtypen n.

Definition stty := list (vtype * ql).


(* the empty type *)
Definition vtnone n: vtypen n :=
  match n with
  | 0 => False
  | S n => fun nx (M: list ((vtypen (n-nx)) * ql)) (v: vl)(q: ql) => False
  end.

Check vtnone: vtype.


(* every indexed type can be approximated with a lower index (vt_dec) *)

Lemma aux_lt1: forall n, S n <= 0 -> False. lia. Qed.

Lemma aux_lt2: forall n j nx, S j <= S n -> (j-nx = n - (n-j+nx)). intros. lia. Qed.


Definition vtn_aux_eq: forall n1 n2 (q: n1 = n2), vtypen n1 -> vtypen n2.
Proof. intros. subst n2. eauto.
Defined.

Definition sttyn_aux_eq: forall n1 n2 (q: n1 = n2) (vt: list ((vtypen n1) * ql)), list ((vtypen n2) *ql).
Proof. intros. rewrite q in *. eauto.
Defined.


Lemma vt_dec: forall n j, j <= n -> vtypen n -> vtypen j.
Proof.
  intros n. intros.
  destruct n, j. eauto. edestruct aux_lt1. eapply H. simpl. eapply True.
  simpl in *. intros. eapply (X (n-j+nx)).
  eapply sttyn_aux_eq. eapply aux_lt2. eauto. eauto. eauto. eauto. 
Defined.

Print vt_dec.


(* physical approximation *)

Definition vt_wrap n (vt: vtypen n): vtype :=
  fun n1 =>
    match le_dec n1 n with
    | left a => vt_dec _ _ a vt
    | _ => vtnone n1
    end.

Definition vt_pick n (vt: vtype): vtypen n :=
  vt n.

Definition vt_apprx n (vt: vtype): vtype :=
  vt_wrap n (vt n). 

Definition stty_wrap n (M: sttyn n): stty :=
  map (fun '(vt,q) => ((vt_wrap n vt), q)) M. 

Definition stty_pick n (M: stty): sttyn n :=
  map (fun '(vt,q) => ((vt _), q)) M. 

Definition stty_apprx n (M: stty): stty :=
  stty_wrap n (stty_pick n M).
  (* map (fun vt => vt_apprx n vt) M. *)



(* logical approximation *)

Definition vt_approx n (vt: vtype): vtype :=
  fun n1 =>
    match lt_dec n1 n with
    | left a => vt n1
    | _ => vtnone n1
    end.

Definition stty_approx n (M: stty): stty :=
  map (fun '(vt,q) => ((vt_approx n vt),q)) M.     

(* lifting element access to the logical level:
   vtyp_elem reconstructs the abstraction of vtype
   as set of (nat, stty, vl) elements
*)

Definition vt_elem n nx (vt: vtypen n) (M: stty) (v: vl)(q: ql) :=
  match n, vt, M with
  | 0, _, _ => vt
  | S n, vt, M => vt nx (stty_pick _  M) v q
  end.

Definition vtyp_elem n (vt: vtype) (M: stty) (v: vl)(q: ql) :=
  forall nx, vt_elem n nx (vt n) M v q. 



(* equivalence on vtype up to n-approximation *)

Definition vtyp_equiv n (vt1 vt2: vtype) :=
  (vt_approx n vt1) = (vt_approx n vt2).


Definition istypeC nu (vt: vtype) :=     
  forall j,
    j < nu ->
    (vt_apprx j vt) = (vt_approx (S j) vt).

Definition isstoretypeD nu (M: list (vtype * ql)) :=
  forall j,
    j < nu ->
    (stty_apprx j M) = (stty_approx (S j) M).

    
Definition st_locs (M: stty) := pnat (length M).

Definition pstdiff M' M :=
  (* pdiff (pdom (M'++M)) (pdom M) *)
  pdiff (st_locs M') (st_locs M).

#[global] Hint Unfold st_locs.  
#[global] Hint Unfold pstdiff.

Definition st_chain n j (M:stty) (M1:stty) p :=
    psub p (st_locs M) /\
    psub p (st_locs M1) /\
    j <= n /\ length M <= length M1 /\
      forall i vt qt,
        indexr i M = Some (vt, qt) ->
        exists vt',
          indexr i M1 = Some (vt', qt) /\
            vtyp_equiv j vt vt'.

Definition st_extend n j M1 M2 :=
  st_chain n j M1 M2 (st_locs M1).

Definition istypeA (vt: vtype) := forall n j M M' v qt,
    isstoretypeD n M ->
    isstoretypeD j M' ->
    st_extend n j M M' -> 
    vtyp_elem n vt M v qt -> vtyp_elem j vt M' v qt.


Definition vtyp_elem_approx n vt M v ls :=
  forall j,
    j < n ->
    vtyp_elem j (vt_approx n vt) (stty_approx j M) v ls.

Definition store_type n S M: Prop := 
  length S = length M /\
    forall i vt qt,
      indexr i M = Some (vt, qt) ->
      istypeA vt /\
      istypeC n vt /\
      exists v ls,
        indexr i S = Some v /\
          vtyp_elem_approx n vt M v ls /\
          psub (plift ls)(plift qt) /\
          psub (plift qt) (pnat i).


Definition vt_wrap1 (vt: nat -> stty -> vl -> ql -> Prop): vtype :=
  fun j =>
    match j return vtypen j with
    | 0 => True
    | S j => fun nx M vx q => vt (S j-nx) (stty_wrap (j-nx) M) vx q
    end.

(* mapping values and variables to store locations *)

Definition lenv: Type := list (nat * stty * Prop * ql).

Definition var_locs (E:lenv) x l := exists j M u vx, indexr x E = Some (j, M, u, vx) /\ plift vx l.

Definition vars_locs (E:lenv) q l := exists x, q x /\ var_locs E x l.

Fixpoint vars_locs_fix (V: lenv) (q: ql) (l: nat): bool :=
  match V with
  | (M,u,ls) :: V => (q (length V) && ls l) || vars_locs_fix V q l
  | [] => false
  end.


Definition env_qual G V (p:pl) :=
  (forall q q',
      psub q p ->
      psub q' p ->
      psub (pand (vars_locs V q) (vars_locs V q'))
        (vars_locs V (pand (vars_trans G q) (vars_trans G q')))).    

Definition env_accs n (M:stty) (V:lenv) (p: pl) :=
  (forall x,
      p x ->
      exists j M' u ls,
        indexr x V = Some (j, M', u, ls) /\ u /\ st_chain j n M' M (plift ls)). 
        

Fixpoint val_type n (M: stty)(G:tenv)(H: venv)(V: lenv) v T (u: Prop)(ls:ql) {struct T}: Prop :=
  match n, M with
  | 0, M => True
  | S n, M => 
      match v, T with
      | vbool b, TBool =>  
          ls = qempty
      | vref l, TRef T fr q  =>
          closed_ty (length H) T /\
          psub (plift q) (pdom H) /\
          (u -> plift ls l /\
          psub (plift ls)(st_locs M) /\
          exists vt qt,
          indexr l M = Some (vt, qt) /\
           (psub (plift qt) (por (vars_locs V (plift q)) (pif fr (plift ls)))) /\ (* Q: should choice be exclusive? *)
           (psub (vars_locs V (plift q)) (plift qt)) /\
           (vtyp_equiv (S n) vt
                       (vt_wrap1 (fun n M v lsv =>  val_type n M G H V v T u lsv))))

      | vabs H' ty, TFun T1 fn1 fr1 q1 T2 fn2 ar2 fr2 q2 e2fn e2ar e2fr e2 =>
          closed_ty (length H) T1 /\
          (psub (plift q1) (pdom H)) /\
          closed_ty (length H) T2 /\
          (psub (plift q2) (pdom H)) /\
          (psub (plift e2) (pdom H)) /\
          (u -> (psub (plift ls) (st_locs M))) /\
          forall S' nx M' vx lsx (uy: bool)(u': Prop),
            (e2fn || uy && fn2 = true -> st_chain (S n) (n-nx) M M' (plift ls)) (* if uy && fn2 *) 
            ->
            store_type (n-nx) S' M' ->
            (uy = true -> fn2 = true -> u) (* ??? *)
            ->
            (e2fn = true -> u)
            ->
            env_qual G V (por (plift e2) (pif uy (plift q2))) (* !!! want effect *) (* if uy, add q2! *)
            ->
            env_accs (n-nx) M' V (por (plift e2) (pif uy (plift q2))) (* !!! want effect *)
            ->
            val_type (n-nx) M' G H V vx T1 (e2ar || uy && ar2=true) lsx 
            ->
            psub (plift lsx)
            (por (vars_locs V (plift q1))
               (por (pif (fn1 && fr1) (pnot pempty))
                  (pif fr1
                     (* if observe arg, must track overlap with other *)
                     (* observed vars: e2, and possibly q2  *)
                     (pnot (pif (e2ar || uy && ar2)
                              (por (vars_locs V (por (plift e2) (* pif e2ar *)
                                      (pif uy (plift q2)))) (* if q2ar? e2ar?? *)
                              (pif (e2fn || uy && fn2) (plift ls)))))))) (* fn2 ? *)
           (* (pif fr1 (pnot (plift ls))))) *)
           ->

            forall S'' ny ry,
              teval (n-nx) S' (vx::H') ty = (ny, S'', (Some ry)) ->
              exists M'' vy lsy,
                st_extend (n-nx) (n-nx-ny) M' M'' /\
                store_type (n-nx-ny) S'' M'' /\
                ry = Some vy /\
                val_type (n-nx-ny) M'' G H V vy T2 (uy=true) lsy /\
                psub (plift lsy)
                (por (vars_locs V (plift q2)) (* allow v \/ vx? *)
                   (por (pif fn2 (plift ls))
                      (por (pif ar2 (plift lsx))
                         (pif fr2 (pstdiff M'' M')))))


      | _,_ =>
          False
      end
  end.

Definition val_qual (M M1: stty) V lsv fr (q: pl) :=
  psub (plift lsv)
    (por (vars_locs V q)
       (pif fr (pstdiff M1 M))).

Definition exp_type n S M G H V t T u (p: pl) fr q :=
  forall n' S' r,
    teval n S H t = (n', S', Some r) ->
    exists M' v ls,
      st_extend n (n-n') M M' /\
      store_type (n-n') S' M' /\
      r = Some v /\
      val_type (n-n') M' G H V v T u ls /\
      val_qual M M' V ls fr q /\
    (match t with tvar x => psub (vars_locs V (pone x)) (plift ls) | _ => True end).

Definition env_type n (H: venv) (G: tenv) V :=
  length H = length G /\
  length V = length G /\
    (forall x T fr (q: ql),
      indexr x G = Some (T, fr, q) ->
      exists v u ls M' j,
        psub (plift q)(pdom H) /\
        closed_ty x T /\
        closed_ql x q /\
        indexr x H = Some v /\
        indexr x V = Some (j, M', u, ls) /\
        val_type n M' G H V v T u ls /\
        (fr = false -> psub (plift ls) (vars_locs V (plift q)))).

Definition sem_type G t T p fr q :=
  forall n S M H V u,
    env_type n H G V ->
    env_qual G V (por p (pif u q)) ->
    env_accs n M V (por p (pif u q)) ->
    store_type n S M ->
    exp_type n S M G H V t T (u=true) p fr q.


#[export] Hint Constructors ty: core.
#[export] Hint Constructors tm: core.
#[export] Hint Constructors vl: core.

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

Lemma plift_dom: forall A (E: list A),
    plift (qdom E) = pdom E.
Proof.
  intros. unfoldq. unfold plift.
  eapply functional_extensionality. intros.
  eapply propositional_extensionality. 
  bdestruct (qdom E x); intuition. 
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

Lemma pif_false: forall p,
  pif false p = pempty.
Proof.
  intros. eapply functional_extensionality. intros. simpl. auto.
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

Lemma por_empty_r: forall p,
  por p pempty = p.
Proof.
  intros. eapply functional_extensionality. intros. eapply propositional_extensionality. 
  split; unfoldq; intuition.
Qed.

Lemma pand_sub: forall p q,
    psub p q ->
    pand q p = p.
Proof.
  intros. unfoldq. unfold plift. eapply functional_extensionality. intros.
  eapply propositional_extensionality. split; intros; intuition.
Qed.



Lemma plift_vars_locs: forall V q,
    plift (vars_locs_fix V q) = vars_locs V (plift q).
Proof.
  intros. eapply functional_extensionality.
  intros. eapply propositional_extensionality.
  unfold vars_locs, var_locs, plift in *.
  intuition.
  - induction V. intuition.
    destruct a as [[[n M] u] ls].
    remember (q (length V)) as b1.
    remember (ls x) as b2.
    destruct b1. destruct b2. simpl in H.
    (* both true *)
    exists (length V). split. eauto.
    exists n, M, u, ls. rewrite indexr_head. intuition.
    (* one false *)
    simpl in H. rewrite <-Heqb1, <-Heqb2 in H. simpl in H. eapply IHV in H.
    destruct H. exists x0. intuition.
    destruct H1 as (n' & M' & u' & ls' & ?). exists n', M', u', ls'. rewrite indexr_extend1 in H. intuition eauto. 
    (* other false *)
    simpl in H. rewrite <-Heqb1 in H. simpl in H. eapply IHV in H. 
    destruct H. exists x0. intuition.
    destruct H1 as (n' & M' & u' & ls' & ?). exists n', M', u', ls'. rewrite indexr_extend1 in H. intuition eauto.
  - simpl. destruct H as [? [? ?]]. destruct H0 as (? & ? & ? & ? & ? & ?).
    unfold indexr in H0. induction V.
    congruence.
    destruct a as [[[n M] u] ls].
    bdestruct (x0 =? length V).
    inversion H0. subst. simpl. rewrite H.
    unfold plift in H1. rewrite H1. simpl. eauto.
    simpl. rewrite IHV.
    destruct (q (length V) && ls x); simpl; eauto.
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
    destruct H3 as (? & ? & ? & ? & ?). exists x1, x2, x3, x4. intuition.
    eapply indexr_extend; eauto.
  - destruct H1. exists x0. intuition.
    destruct H3 as (? & ? & ? & ? & ?). exists x1, x2, x3, x4. intuition.
    eapply indexr_extend in H3. eapply H3.
Qed.

Lemma vars_locs_extend1: forall H v q l,
    vars_locs H q l ->
    vars_locs (v :: H) q l.
Proof. 
  intros. unfoldq. intuition.
  destruct H0 as (? & ? & ? & ? & ? & ? & ?).
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

Lemma var_locs_head: forall n M u v H l,
  var_locs ((n, M,u,v) :: H) (length H) l ->
  plift v l.
Proof. 
  intros. 
  destruct H0 as [nx [Mx [ux [vx [IVX VALVX]]]]].
  
  assert (indexr (length H) ((n,M,u,v) :: H) = Some (n,M,u,v)). {
    replace ((n,M,u,v) :: H) with ([] ++ (n,M,u,v) :: H) in IVX; auto.
    rewrite indexr_insert in IVX; eauto.
    inversion IVX. subst.
    replace ((nx,Mx,ux,vx) :: H) with ([] ++ (nx,Mx,ux,vx) :: H); auto.
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
  destruct H0 as [nx [Mx [ux [vx [IVX VALVX]]]]].
  exists nx, Mx, ux, vx. split.
  erewrite <- indexr_skip; eauto. lia.
  auto.
Qed.

Lemma var_locs_extend: forall v H x l,
  var_locs H x l ->
  var_locs (v::H) x l.
Proof.
  intros. unfoldq. 
  destruct H0 as [nx [Mx [ux [vx [IVX VALVX]]]]].
  exists nx, Mx, ux, vx. split.
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


Lemma envt_telescope: forall n H G V,
    env_type n H G V -> telescope G.
Proof.
  intros. destruct H0 as (? & ? & ?).
  intros ? ? ? ? ?. edestruct H2 as (? & ? & ? & ? & ? & ?); eauto.
  intuition.
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

Lemma vars_trans_shrink: forall G a q1,
    psub (plift q1) (pdom G) ->
    psub (plift (vars_trans_fix (a::G) q1)) (plift (vars_trans_fix G q1)).
Proof.
  intros. intros ? ?. destruct a. destruct p. simpl in H0.
  rewrite plift_if1, plift_or in H0.
  remember (q1 (length G)) as b1. 
  destruct b1.
  assert (plift q1 (length G)). unfold plift. eauto.
  eapply H in H1. unfoldq. lia.
  eauto. 
Qed.

Lemma vars_trans_shrink2: forall G' G q1,
    psub (plift q1) (pdom G) ->
    psub (plift (vars_trans_fix (G'++G) q1)) (plift (vars_trans_fix G q1)).
Proof.
  intros G'. induction G'.
  - simpl. intros. intros ? ?. eauto.
  - intros. intros ? ?. eapply IHG'. eauto. eapply vars_trans_shrink. unfoldq. rewrite app_length. intuition. eapply H in H1. intuition. eauto. 
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

Lemma vt_extend2: forall G' G q1,
    psub (vars_trans G q1) (vars_trans (G'++G) q1).
Proof.
  intros G'. induction G'.
  - intros. simpl. intros ? ?. eauto. 
  - intros. simpl. intros ? ?. eapply vt_extend. eapply IHG'. eauto. 
Qed.


Lemma vt_shrink2: forall G G' q1,
    psub q1 (pdom G) ->
    telescope G ->
    psub (vars_trans (G'++G) q1) (vars_trans G q1).
Proof.
  intros. intros ? ?. destruct H1.
  - left. intuition.
  - right. destruct H1 as (? & ? & ? & T2 & fr2 & q2 & IX & VT).
    assert (x0 < length G). eapply H in H1. unfoldq. lia. 
    rewrite indexr_skips in IX. 2: eauto. 
    exists x0. intuition. exists T2, fr2, q2. intuition.
    eapply vars_trans_shrink2. 2: eauto.
    unfold telescope in *. eapply H0 in IX.
    intros ? ?. unfoldq. eapply IX in H4. eapply H in H1. lia. 
Qed.

Lemma vt_shrink: forall G a q1,
    psub q1 (pdom G) ->
    telescope G ->
    psub (vars_trans (a::G) q1) (vars_trans G q1).
Proof.
  intros. replace (a::G) with ([a]++G). 2: eauto.
  eapply vt_shrink2; eauto. 
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
  2: rewrite <-plift_vt. 2: eapply H4. 2: eauto.
  eapply H6 in H3. eapply H0 in H1. lia. 
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
  unfold vars_trans'. eapply vars_trans_extend. rewrite plift_vt; eauto.
Qed.


(* ---------- helper lemmas: vtype, vtyp_equiv, etc  ---------- *)


Lemma vt_approx_comm: forall n1 n2 vt,    
    (vt_approx n1 (vt_approx n2 vt)) = (vt_approx n2 (vt_approx n1 vt)).
Proof.
  intros.
  extensionality nx.
  unfold vt_approx.
  destruct (lt_dec nx n1), (lt_dec nx n2); eauto. 
Qed.

Lemma vt_approx_neutral: forall n1 n2 vt,
    n1 <= n2 ->
    (vt_approx n1 (vt_approx n2 vt)) = (vt_approx n1 vt).
Proof.
  intros.
  extensionality nx.
  unfold vt_approx.
  destruct (lt_dec nx n1), (lt_dec nx n2); eauto. lia. 
Qed.


Lemma stty_approx_neutral: forall M n1 n2,
    n1 <= n2 ->
    (stty_approx n1 (stty_approx n2 M)) = (stty_approx n1 M).
Proof.
  intros. unfold stty_approx. rewrite map_map. eapply map_eq_f.
  extensionality vt. destruct vt. f_equal. eapply vt_approx_neutral. eauto.
Qed.

Lemma stty_approx_length: forall M n,
  length (stty_approx n M) = length M.
Proof.
  intros. unfold stty_approx. rewrite map_length. auto.
Qed.

Lemma vtyp_approx_equiv: forall j (vt1 vt2: vtype),
  vt1 = vt2 ->
  vtyp_equiv j (vt1) (vt2).
Proof.
  intros. congruence. 
Qed.

Lemma vtyp_equiv_dec: forall n j (vt1 vt2: vtype),
  vtyp_equiv n vt1 vt2 -> j <= n ->
  vtyp_equiv j (vt1) (vt2).
Proof.
  intros. unfold vtyp_equiv in *.
  intros. unfold vt_approx, vtyp_elem in *.
  extensionality n1.
  eapply equal_f_dep with (x:=n1) in H. 
  destruct (lt_dec n1 j), (lt_dec n1 n); eauto. lia.
Qed.


Lemma vte_approx: forall n n1 vt M v q,
    vtyp_elem_approx n vt M v q ->
    n1 <= n ->
    vtyp_elem_approx n1 vt M v q.
Proof.
  intros. unfold vtyp_elem_approx, vtyp_elem in *. 
  intros. unfold vt_elem in *.
  destruct j.

  specialize (H 0). simpl in H.
  unfold vt_approx in *.
  destruct (lt_dec 0 n1). 2: lia.
  destruct (lt_dec 0 n). 2: lia. eauto. 
  
  unfold vt_approx in *.
  remember (lt_dec (S j) n1). destruct s. 2: lia.
  specialize (H (S j)).
  remember (lt_dec (S j) n). destruct s. 2: lia.
  eapply H. eauto. 
Qed.



(* ---------- LR helper lemmas  ---------- *)

Lemma st_extend_refl: forall n M,
    st_extend n n M M.
Proof.
  intros. 
  split. 2: split. 3: split. 4: split.
  intros ? ?. auto. 
  intros ? ?. auto. 
  eauto. eauto. 
  intros. exists vt. split. eauto.
  intuition. 
Qed.

Lemma st_chain_refl: forall n n1 M p,
  n1 <= n ->
  psub p (st_locs M) ->
  st_chain n n1 M M p.
Proof.
  intros. 
  split. 2: split. 3: split. 4: split.
  intros ? ?. auto. 
  intros ? ?. auto. 
  lia. eauto. 
  intros. exists vt. split. eauto.
  intuition.
Qed.

Lemma st_extend_refl': forall n n1 M,
    n1 <= n ->
    st_extend n n1 M M.
Proof.
  intros. 
  split. 2: split. 3: split. 4: split.
  intros ? ?. auto. 
  intros ? ?. auto. 
  lia. eauto. 
  intros. exists vt. split. eauto.
  intuition.
Qed.

Lemma st_extend': forall n n1 vt M,
    n1 <= n ->
    st_extend n n1 M (vt::M).
Proof.
  intros. 
  split. 2: split. 3: split. 4: split.
  intros ? ?. auto. 
  intros ? ?. unfold st_locs, pnat in *. simpl. lia.
  eauto. simpl. lia. 
  intros. exists vt0. split. eapply indexr_extend1 in H0. eapply H0. 
  intuition.
Qed.

Lemma st_mono: forall n n1 M M1,
  st_extend n n1 M M1 ->
  length M <= length M1.
Proof.
  intros. unfold st_extend, st_chain in H. intuition.
Qed.

Lemma stchain_tighten: forall n n1 M1 M2 p p',
    st_chain n n1 M1 M2 p ->
    psub p' p ->
    st_chain n n1 M1 M2 p'.
Proof.
  intros. unfold st_chain in *.
  intuition. intros ? ?. eauto.
  intros ? ?. eauto. 
Qed.

Lemma stchain_chain: forall n1 n2 n3 M1 M2 M3 p1 p2 p3,
    st_chain n1 n2 M1 M2 p1 ->
    st_chain n2 n3 M2 M3 p2 ->
    psub p3 (pand p1 p2) ->
    st_chain n1 n3 M1 M3 p3.
Proof.
  intros. 
  destruct H as (? & ? & ? & ? & ?).
  destruct H0 as (? & ? & ? & ? & ?).
  split. 2: split. 3: split. 4: split.
  - intros ? Q.  eapply H1 in Q. destruct Q. eauto.
  - intros ? Q.  eapply H1 in Q. destruct Q. eauto.
  - lia.
  - lia.
  - intros i vt1 qt1 IX1.
    edestruct H5 as (vt2 & IX2 & ?). eapply IX1.
    edestruct H9 as (vt3 & IX3 & ?). eapply IX2.
    eexists. eexists. eapply IX3.
    eapply vtyp_equiv_dec in H10. 
    unfold vtyp_equiv in *. rewrite H10. eauto. eauto.
Qed.


Lemma st_extend_chain: forall n1 n2 n3 M1 M2 M3,
    st_extend n1 n2 M1 M2 ->
    st_extend n2 n3 M2 M3 ->
    st_extend n1 n3 M1 M3.
Proof.
  intros. eapply stchain_chain; eauto. 
  unfoldq; intuition. eapply H. auto.
Qed.

Lemma stchain_step': forall n n1 n' M M1 p,
    st_chain n n1 M M1 p ->
    n <= n' ->
    st_chain n' n1 M M1 p.
Proof.
  intros. unfold st_chain in *. intuition.
Qed.

Lemma stchain_step''': forall n n1 n' M M1 p,
    st_chain n n1 M M1 p ->
    n1 <= n' ->
    st_chain n' n1 M M1 p.
Proof.
  intros. unfold st_chain in *. intuition.
Qed.


Lemma st_extend_step': forall n n1 n' M M1,
    st_extend n n1 M M1 ->
    n <= n' ->
    st_extend n' n1 M M1.
Proof.
  intros. eapply stchain_step'; eauto.
Qed.

Lemma st_extend_step'': forall n n1 n2 M M1,
    st_extend n n1 M M1 ->
    n2 <= n1 ->
    st_extend n n2 M M1.
Proof.
  intros.
  eapply st_extend_chain. eauto.
  eapply st_extend_refl'. eauto. 
Qed.


Lemma stchain_step'': forall n n1 n2 M M1 P,
    st_chain n n1 M M1 P ->
    n2 <= n1 ->
    st_chain n n2 M M1 P.
Proof.
  intros.
  unfold st_chain in *. intuition.
  destruct (H5 i vt qt H4) as [vt' [? ?]].
  exists vt'. intuition.
  eapply vtyp_equiv_dec; eauto.
Qed.

Lemma st_extend_approx: forall n j M,
    j < n ->
    st_extend n j M (stty_approx j M).
Proof.
  intros. split. 2: split. 3: split. 4: split.
  intros ? ?. auto.
  intros ? ?. unfold st_locs in *. unfold stty_approx. rewrite map_length. eauto.
  lia. 
  unfold stty_approx. rewrite map_length. eauto.
  intros. eapply indexr_map in H0.
  eexists. split. unfold stty_approx.  eapply H0.
  unfold vtyp_equiv. rewrite vt_approx_neutral; eauto. 
Qed.

Lemma st_extend_approx'': forall n j nx M M',
    st_extend (S n) (S j) M M' ->
    st_extend (S n - nx) (S j - nx)
      (stty_approx (S (n - nx)) M)
      (stty_approx (S (j - nx)) M').
Proof.
  intros. destruct H as (? & ? & ? & ? & ?).
  split. 2: split. 3: split. 4: split.
  intros ? ?. auto.
  unfold st_locs, stty_approx. rewrite map_length. rewrite map_length. eauto.
  lia. 
  unfold stty_approx. rewrite map_length, map_length. eauto.
  
  intros. unfold stty_approx in *.
  eapply indexr_var_some' in H4 as IX1. rewrite map_length in IX1.
  eapply indexr_var_some in IX1 as IX2. destruct IX2 as ((vt1 & qt1) & IX2).
  eapply H3 in IX2 as IX4. destruct IX4 as (vt2 & IX4 & EQ2). 
  eapply indexr_map with (f := vt_approx (S (j - nx))) in IX4 as IX5.

  eapply indexr_map in IX2 as IX6. rewrite IX6 in H4.
  inversion H4. subst vt. 

  eexists. split. erewrite IX5. f_equal. f_equal. eauto. 
  unfold vtyp_equiv. repeat rewrite vt_approx_neutral; eauto.
  eapply vtyp_equiv_dec. eauto. lia. lia. lia. 
Qed.

Lemma st_extend_apprx: forall n j nx M M',
    isstoretypeD (S n) M ->
    isstoretypeD (S j) M' ->
    st_extend (S n) (S j) M M' ->
    st_extend (S n - nx) (S j - nx)
      (stty_apprx (n - nx) M)
      (stty_apprx (j - nx) M').
Proof.
  intros.
  destruct H1 as (? & ? & ? & ? & ?).
  rewrite H, H0.
  eapply st_extend_approx''. split; eauto. lia. lia. 
Qed.

Lemma vt_extend_eq: forall G' G p,
    psub p (pdom G) ->
    telescope G ->
    vars_trans (G'++G) p = vars_trans G p.
Proof.
  intros. eapply functional_extensionality.
  intros. eapply propositional_extensionality.
  split. eapply vt_shrink2; eauto. eapply vt_extend2; eauto. 
Qed.

Lemma envq_extend: forall G' G V' V p
    (L: length G = length V)
    (TL: telescope G),   
    psub p (pdom V) ->
    env_qual (G'++G) (V'++V) p <-> env_qual G V p.
Proof.
  intros.
  assert (psub p (pdom G)) as O.
  unfoldq. intuition. eapply H in H0. lia.
  unfold env_qual. split.
  - intros W2. 
    + intros. specialize (W2 q q'). 
      rewrite vt_extend_eq in W2; eauto.  rewrite vt_extend_eq in W2; eauto. 
      rewrite vars_locs_extend in W2. rewrite vars_locs_extend in W2. rewrite vars_locs_extend in *. 
      eapply W2. all: eauto. 2-5: unfoldq; intuition.
      intros ? Q. destruct Q. replace (pdom V) with (pdom G). 
      eapply vt_closed. eauto. 2: eauto. unfoldq. intuition.
      unfoldq. rewrite L. eauto.
  - intros W2. 
    + intros ? ? ? ?. 
      rewrite vt_extend_eq. rewrite vt_extend_eq. intros. 
      rewrite vars_locs_extend. rewrite vars_locs_extend. rewrite vars_locs_extend.
      eapply W2. all: eauto. 2-5: unfoldq; intuition. 
      intros ? Q. destruct Q. replace (pdom V) with (pdom G).
      eapply vt_closed. eauto. 2: eauto. unfoldq. intuition.
      unfoldq. rewrite L. eauto. 
Qed.


Lemma wf_env_type: forall H G V n, 
  env_type n H G V -> 
  length H = length G /\
  length V = length G /\
  pdom H = pdom G /\
  pdom V = pdom G.
Proof.
  intros. unfold env_type in H0. intuition.
  unfold pdom. rewrite H1. auto.
  unfold pdom. rewrite H0. auto.
Qed.

Lemma envq_extend_full: forall (*M*) M1 H G V vx T1 p fn1 fr1 q1 qf qf1 u lsx n nx nx',
  env_type n H G V ->
  env_qual G V p ->
  psub p (pdom G) -> (* should probably be part of envq? *)
  (u=true -> psub (plift q1) p) ->
  psub qf p ->
  psub qf (plift qf1) -> (* initially had p < qf1, but seems not necessary! *)
  psub (plift qf1) (pdom G) ->
  val_type nx M1 G H V vx T1 (u=true) lsx ->
  (u=true -> psub (plift lsx)
    (por (vars_locs V (plift q1))
       (por (pif (fn1 && fr1) (pnot pempty))
          (pif fr1 (pnot (vars_locs V qf)))))) ->
  closed_ty (length H) T1 ->
  env_qual ((T1, fr1, qor q1 (qif fn1 qf1)) :: G) ((nx', M1,u=true,lsx)::V) (por qf (pif u (pone (length H)))).
Proof.
  intros. apply wf_env_type in H0 as H0'. destruct H0' as (L1 & L2 & PD & PD' (*& SG*)).
  rename H1 into W2.
  assert (psub p (pdom G)) as PG. unfoldq. intuition. 
  assert (psub p (pdom H)) as PH. rewrite PD. eauto. 
  assert (psub p (pdom V)) as PV. rewrite PD'. eauto.

  intros q q' QSUB QSUB' x (QQ & QQ').

  destruct QQ as (? & VTQ & VLQ).
  destruct QQ' as (? & VTQ' & VLQ').
  destruct (QSUB x0); intuition; destruct (QSUB' x1); intuition.
  + (* qf, qf *)
    destruct (W2 (pand (pdom H) q) (pand (pdom H) q')) with (x:=x).
    intros ? ?. destruct (QSUB x2) as [? | ?]. unfoldq. intuition. 
    eauto. destruct u. 2: contradiction. eauto. unfoldq. lia.
    intros ? ?. destruct (QSUB' x2) as [? | ?]. unfoldq. intuition. 
    eauto. destruct u. 2: contradiction. eauto. unfoldq. lia. 
    split. 
    exists x0. unfoldq. intuition. eapply var_locs_shrink. eauto. eauto.
    exists x1. unfoldq. intuition. eapply var_locs_shrink. eauto. eauto.
    exists x2. intuition.
    destruct H12. split.
    eapply vt_extend. eapply vt_mono. 2: eapply H11. unfoldq. intuition.
    eapply vt_extend. eapply vt_mono. 2: eapply H12. unfoldq. intuition.
    eapply var_locs_extend. eauto.
  + (* qf, x *)
    rename H8 into SEP.
    destruct u. 2: contradiction.
    unfold pif,pone in H10. subst x1. 
    (* shrink VLQ *)
    eapply var_locs_shrink in VLQ. 2: { rewrite L2. eapply H2, H4, H1. }
    (* shrink VLQ', unpack it *)
    destruct VLQ' as (? & ? & ? & ?& IX & LSX). rewrite L1,<-L2,indexr_head in IX. inversion IX. subst x1 x2 x3 x4. 
    eapply SEP in LSX. destruct LSX as [H_q1 | [H_fn | H_fr]].
    * destruct H_q1 as (? & PQ1 & VL1).
      destruct (W2 (pand (pdom H) q) (plift q1)) with (x:=x) as (? & QA & PP). 
      ++ intros ? ?. destruct (QSUB x2) as [? | ?]. unfoldq. intuition.
         eauto. eauto. unfoldq. lia. 
      ++ eauto. 
      ++ split.
         exists x0. unfoldq. intuition.
         exists x1. intuition. 
      ++ destruct QA as [P0 P1].
         exists x2. split. split.
         ** eapply vt_extend. eapply vt_mono. 2: eapply P0. unfoldq. intuition.
         ** right. exists (length G). intuition.
            rewrite <-L1. eauto.
            rewrite <-L2. destruct PP as (? & ? & ? & ? & ? & ?). eapply indexr_var_some'. eauto. 
            exists T1, fr1, (qor q1 (qif fn1 qf1)). rewrite indexr_head. split. eauto.
            unfold vars_trans'. rewrite plift_vt, plift_or, plift_if. eapply vt_extend.
            eapply vt_mono. 2: eapply P1. unfoldq. intuition. 
            eapply telescope_extend.
            rewrite <-L1, plift_closed, plift_or, plift_if, PD.
            unfoldq. intuition. destruct fn1; intuition eauto.
            rewrite <-L1. eauto.
            eapply envt_telescope. eauto.
         ** eapply var_locs_extend. eauto. 
    * destruct fn1, fr1; try contradiction.
      eexists. split. split.
      ++ left. eauto.
      ++ right. eexists. split. eauto. split. eapply PH; eauto. 
         eexists. eexists. eexists.
         split. rewrite L1. rewrite indexr_head. eauto.
         unfold vars_trans'. rewrite plift_vt.
         left. rewrite plift_or, plift_if.
         right. eapply H5. eauto.
         eapply telescope_extend.
         rewrite <-L1, plift_closed, plift_or, plift_if, PD.
         unfoldq. intuition. 
         rewrite <-L1. eauto.
         eapply envt_telescope. eauto.
      ++ eapply var_locs_extend. eauto. 
    * destruct fr1. 2: contradiction.
      destruct H_fr. eexists. intuition. eauto. eauto.
    * eauto. 
  + (* x, qf *)
    rename H8 into SEP.
    destruct u. 2: contradiction.
    unfold pif,pone in H1. subst x0. 
    (* shrink VLQ' *)
    eapply var_locs_shrink in VLQ'. 2: { rewrite L2. eapply H2, H4, H10. }
    (* shrink VLQ, unpack it *)
    destruct VLQ as (? & ? & ? & ? & IX & LSX). rewrite L1,<-L2,indexr_head in IX. inversion IX. subst x0 x2 x3 x4.  
    eapply SEP in LSX. destruct LSX as [H_q1 | [H_fn | H_fr]].
    * destruct H_q1 as (? & PQ1 & VL1).
      destruct (W2 (plift q1) (pand (pdom H) q')) with (x:=x) as (? & QA & PP).
      ++ eauto.
      ++ intros ? ?. destruct (QSUB' x2) as [? | ?]. unfoldq. intuition.
         eauto. eauto. unfoldq. lia. 
      ++ split.
         exists x0. intuition. 
         exists x1. unfoldq. intuition.
      ++ destruct QA as [P0 P1].
         exists x2. split. split.
         ** right. exists (length G). intuition.
            rewrite <-L1. eauto.
            rewrite <-L2. destruct PP as (? & ? & ? & ? & ? & ?). eapply indexr_var_some'. eauto. 
            exists T1, fr1, (qor q1 (qif fn1 qf1)). rewrite indexr_head. split. eauto.
            unfold vars_trans'. rewrite plift_vt, plift_or, plift_if. eapply vt_extend.
            eapply vt_mono. 2: eapply P0. unfoldq. intuition. 
            eapply telescope_extend.
            rewrite <-L1, plift_closed, plift_or, plift_if, PD.
            unfoldq. intuition. destruct fn1; intuition eauto.
            rewrite <-L1. eauto.
            eapply envt_telescope. eauto.
         ** eapply vt_extend. eapply vt_mono. 2: eapply P1. unfoldq. intuition.
         ** eapply var_locs_extend. eauto. 
    * destruct fn1, fr1; try contradiction.
      eexists. split. split.
      ++ right. eexists. split. eauto. split. eapply PH; eauto. 
         eexists. eexists. eexists.
         split. rewrite L1. rewrite indexr_head. eauto.
         unfold vars_trans'. rewrite plift_vt.
         left. rewrite plift_or, plift_if.
         right. eapply H5. eauto.
         eapply telescope_extend.
         rewrite <-L1, plift_closed, plift_or, plift_if, PD.
         unfoldq. intuition. 
         rewrite <-L1. eauto.
         eapply envt_telescope. eauto.
      ++ left. eauto.
      ++ eapply var_locs_extend. eauto. 
    * destruct fr1. 2: contradiction.
      destruct H_fr. eexists. intuition. eauto. eauto.
    * eauto. 
  + (* x, x *)
    destruct u. 2: contradiction.
    unfold pif,pone in H1, H10.
    subst x0 x1.
    exists (length H). intuition. split.
    left. eauto. left. eauto.
Qed.

Lemma envx_extend: forall n M V' V p,
    psub p (pdom V) ->
    env_accs n M (V'++V) p <-> env_accs n M V p.
Proof.
  intros. unfold env_accs. split.
  - intros. edestruct H0 as (j & M' & u & ls & IX & U & SC). eauto.
    rewrite indexr_skips in IX. eexists j, M', u, ls. intuition.
    eapply H. eauto. 
  - intros. edestruct H0 as (j & M' & u & ls & IX & U & SC). eauto.
    rewrite indexr_extend in IX. eexists j, M', u, ls. intuition.
    eapply H2. 
Qed.


Lemma envx_extend_full: forall (*M*) M1 H G V vx T1 p qf u lsx n nx nx',
    env_accs n M1 V p ->
    length H = length V -> (* XXX *)
    val_type nx M1 G H V vx T1 (u=true) lsx ->
    psub qf p ->
    (u=true -> psub (plift lsx) (st_locs M1)) -> 
    closed_ty (length H) T1 ->
    True -> (* st_chain M M1 (vars_locs V qf) -> *)
     n <= nx' -> 
    env_accs n M1 ((nx',M1,u=true,lsx)::V) (por qf (pif u (pone (length H)))).
Proof.
  intros. 
  intros ? P. destruct P as [H_qf | H_x].
  - destruct (H0 x) as (j & M' & u' & ls' & IX & U & SC). unfoldq. intuition.
    exists j, M', u', ls'.
    split. 2: split.
    + eapply indexr_extend1 in IX. eapply IX.
    + eauto.
    + eauto. 
  - destruct u. 2: contradiction.
    exists nx', M1, (true=true), lsx. intuition.
    + inversion H_x. subst. rewrite H1. rewrite indexr_head. eauto.
    + eapply st_chain_refl. lia. auto. 
Qed.

Lemma envx_extend_full': forall M1 H G V vx T1 p qf u lsx n nx nx',
    env_accs n M1 V p ->
    length H = length V -> (* XXX *)
    val_type nx M1 G H V vx T1 (u=true) lsx ->
    psub qf p ->
    (u=true -> psub (plift lsx) (st_locs M1)) -> 
    closed_ty (length H) T1 ->
    n <= nx' ->
    env_accs n M1 ((nx', M1,u=true,lsx)::V) (por qf (pif u (pone (length H)))).
Proof.
  intros.
  eapply envx_extend_full; eauto.
Qed.



Lemma valt_extend: forall T M G' G H' H V' V v u ls n
    (L: length H = length V)
    (LG: length G = length V)
    (TL: telescope G),
    closed_ty (length H) T ->
    val_type n M (G'++G) (H'++H) (V'++V) v T u ls <-> val_type n M G H V v T u ls.
Proof.
  intros T. induction T; split; intros; destruct n; destruct v; simpl in *; intuition.
  - inversion H0. auto.
  - inversion H0. auto.
  - destruct H7 as (vt & qt & IM & QT1 & QT2 & VT).
    exists vt. exists qt. intuition. 
    rewrite vars_locs_extend in QT1. eauto. inversion H0. subst. intros ? ?. eapply H11 in H6. unfoldq. lia.
    rewrite vars_locs_extend in QT2. eauto. inversion H0. subst. intros ? ?. eapply H11 in H6. unfoldq. lia.
    unfold vtyp_equiv in *. rewrite VT. f_equal. f_equal. 
    eapply functional_extensionality. intros. eapply functional_extensionality. intros.
    eapply functional_extensionality. intros. eapply functional_extensionality. intros.
    eapply propositional_extensionality. eapply IHT; eauto. inversion H0. auto.
  - eapply closedty_extend; eauto.
  - intros ? ?. eapply H1 in H3. unfoldq. rewrite app_length. lia.
  - destruct H7 as (vt & qt & IM & QT1 & QT2 & VT).
    exists vt. exists qt. intuition. 
    rewrite vars_locs_extend. auto. intros ? ?. eapply H1 in H6. unfoldq. lia.
    rewrite vars_locs_extend. auto. intros ? ?. eapply H1 in H6. unfoldq. lia.
    unfold vtyp_equiv in *. rewrite VT. f_equal. f_equal. 
    eapply functional_extensionality. intros. eapply functional_extensionality. intros.
    eapply functional_extensionality. intros. eapply functional_extensionality. intros. 
    eapply propositional_extensionality. split; intros; eapply IHT; eauto.
  - inversion H0. auto.
  - inversion H0. auto.
  - inversion H0. auto.
  - inversion H0. auto.
  - inversion H0. auto.
  - (* Abs shrink *)
    inversion H0. subst.
    rename q1 into e2. 
    rename q into q1.
    rename q0 into q2. 
    edestruct (H8 S' nx M' vx lsx uy u') as [M''' [vy [lsy [SC [ST [HR [HVY HQY]]]]]]].
    eauto. eauto. eauto. eauto. eapply envq_extend. eauto. eauto.
      unfoldq. intuition. eapply H35 in H18. lia. destruct uy. eapply H34 in H18. lia. lia. 
      eauto. 
      eapply envx_extend. 
      unfoldq. intuition. eapply H35 in H18. lia. destruct uy. eapply H34 in H18. lia. lia. 
      eauto. 
      eapply IHT1; eauto.
    rewrite vars_locs_extend; auto.
    rewrite vars_locs_extend; auto.
    unfoldq. intuition. eapply H35 in H18. lia.
    unfoldq. intuition. destruct uy. 2: contradiction. eapply H34 in H18. lia.
    unfoldq. intuition. eapply H33 in H17. lia. eauto.
    exists M''', vy , lsy. intuition.
    eapply IHT2; eauto.
    rewrite vars_locs_extend in HQY. eauto.
    unfoldq. intuition. eapply H34 in H17. lia. 
  - eapply closedty_extend; eauto.
  - eapply closedq_extend; eauto.
  - eapply closedty_extend; eauto.
  - eapply closedq_extend; eauto. 
  - eapply closedq_extend; eauto.
  - (* Abs grow *)
    inversion H0. subst.
    rename q1 into e2. 
    rename q into q1.
    rename q0 into q2. 
    edestruct (H8 S' nx M' vx lsx uy u') as [M''' [vy [lsy [SC [ST [HR [HVY HQY]]]]]]].
      eauto. eauto. eauto. eauto. eauto. 
      eapply envq_extend. eauto. eauto.
      unfoldq. intuition. eapply H35 in H18. lia. destruct uy. eapply H34 in H18. lia. lia. 
      eauto. 
      eapply envx_extend. 
      unfoldq. intuition. eapply H35 in H18. lia. destruct uy. eapply H34 in H18. lia. lia. 
      eauto. 
      eapply IHT1; eauto.
      rewrite vars_locs_extend in H15; auto.
      rewrite vars_locs_extend in H15; auto.
      unfoldq. intuition. eapply H35 in H18. lia.
      unfoldq. intuition. destruct uy. 2: contradiction. eapply H34 in H18. lia.
      unfoldq. intuition. eapply H33 in H17. lia. eauto. 
    exists M''', vy, lsy. intuition.
    eapply IHT2; eauto.
    rewrite vars_locs_extend. 
    eauto.
    unfoldq. intuition. eapply H34 in H17. lia. 
Qed.

Lemma valt_extend1: forall T M G H V T1 fr1 q1 v nx vx u ux ls lsx n M',
    length H = length V ->
    length G = length V ->
    closed_ty (length H) T ->
    telescope G ->
    val_type n M ((T1, fr1, q1)::G) (vx::H) ((nx, M', ux, lsx)::V) v T u ls <-> val_type n M G H V v T u ls.
Proof.
  intros.
  replace (vx :: H)  with ([vx] ++ H); auto.
  replace ((nx, M', ux, lsx) :: V)  with ([(nx, M', ux, lsx)] ++ V); auto.
  replace ((T1, fr1, q1) :: G)  with ([(T1, fr1, q1)] ++ G); auto.
  eapply valt_extend; eauto.
Qed.

Lemma envt_empty: forall n,
    env_type n [] [] [].
Proof.
  intros. split. 2: split. eauto. eauto. intros. inversion H. 
Qed.


Lemma envt_extend: forall n E G V M T1 fr1 q1 vx ux nx lsx,
    env_type n E G V ->
    val_type n M G E V vx T1 ux lsx ->
    (fr1 = false -> psub (plift lsx) (vars_locs V (plift q1))) ->
    closed_ty (length E) T1 ->
    closed_ql (length E) q1 ->
    env_type n (vx::E) ((T1, fr1, q1)::G) ((nx, M, ux, lsx)::V).
Proof.
  intros. 
  remember H as WFE. clear HeqWFE.
  destruct H as (LE & LV & W). 
  split. 2: split. 
  - simpl. eauto.
  - simpl. auto.
  - intros x T fr q IX. bdestruct (x =? length G).
    -- subst x. rewrite indexr_head in IX. inversion IX. subst T1 fr1 q1.
        exists vx, ux, lsx, M, nx. intuition.
        * intros ? ?. eapply H3 in H. unfoldq. simpl. lia.
        * rewrite <- LE. auto.
        * rewrite <- LE. auto.
        * rewrite <- LE. rewrite indexr_head. auto.
        * rewrite <- LV. rewrite indexr_head. auto.
        * eapply valt_extend1. lia. lia. auto. eapply envt_telescope; eauto. auto.
        * rewrite <-vars_locs_extend with (H':=[(nx, M, ux, lsx)]) in H4; eauto.
          unfoldq. intuition. eapply H3 in H1. lia.
    -- rewrite indexr_skip in IX; eauto.
       eapply WFE in IX as (v2 & u2 & ls2 &  M2 & j & ?). intuition.
       exists v2, u2, ls2, M2, j. intuition. 
       unfoldq; intuition. simpl. eapply H5 in H10. lia. 
       rewrite indexr_skip; eauto. lia.
       rewrite indexr_skip; eauto. lia.
       eapply valt_extend1 in H9; eauto. simpl. lia. 
       eapply closedty_extend; eauto. apply indexr_var_some' in H7. lia.
       eapply envt_telescope; eauto.
       rewrite <- vars_locs_extend with (H':=[(nx, M, ux, lsx)]) in H12; eauto.
       unfoldq. intuition. eapply H6 in H11. apply indexr_var_some' in H8. lia.
Qed.


Lemma envx_step: forall n1 n M V p,
   n1 <= n ->
   env_accs n M V p ->
   env_accs n1 M V p.
Proof.
  intros. unfold env_accs in *.
  intros. destruct (H0 x H1) as [j [M' [u [ls [IV [U SC]]]]]].
  exists j, M', u, ls. intuition.
  eapply stchain_step''; eauto.
Qed.

Lemma envx_store_change: forall n1 n M M' V p,
    env_accs n M V p ->
    st_chain n n1 M M' (vars_locs V p) ->
    env_accs n1 M' V p.
Proof.
  intros. intros ? ?.  
  destruct (H x H1) as (j & M1 & u & ls & IX & U & SC). 
  exists j, M1, u, ls.
  split. 2: split.  3: split. 4: split. 5: split. 6: split. 
  - eauto.
  - eauto.
  - eapply SC.
  - intros ? Q. eapply H0. exists x. split. auto. eexists. eexists. eexists. eexists. split. eauto. eauto.
  - assert (n1 <= n). eapply H0. assert (n <= j). eapply SC. lia.
  - destruct H0. destruct SC. intuition.
  - destruct H0. destruct SC. intuition.
    eapply H11 in H9. destruct H9 as [? [? ?]].
    eapply H10 in H9. destruct H9 as [? [? ?]].
    exists x1. intuition. eapply vtyp_equiv_dec in H12; eauto.
    unfold vtyp_equiv in *. congruence.
Qed.

Lemma envx_store_extend: forall n1 n M M' V p,
    env_accs n M V p ->
    st_extend n n1 M M' ->
    env_accs n1 M' V p.
Proof.
  intros. unfold env_accs in H.
  intros ? ?. 
  destruct (H x H1) as [? [M'' [u'' [ls'' ?]]]].
  eexists. eexists. eexists. eexists. intuition. eauto. eauto. 
  eapply stchain_chain; eauto. unfoldq; intuition. eapply H5. auto.
Qed.

Lemma envx_wf: forall n M V p q,
    env_accs n M V p ->
    psub q p ->
    psub (vars_locs V q) (st_locs M).
Proof.
  intros. intros ? Q. destruct Q as (? & ? & Q).
  assert (p x0) as P. eapply H0. auto.
  destruct (H x0 P) as (j & M1 & u & ls & IX & U & SC). 
  eapply SC. destruct Q as (? & ? & ? & ? & IX2 & ?).
  rewrite IX2 in IX. inversion IX. subst. eauto.
Qed.

Lemma valt_wf: forall T M G H V v u ls n,
    val_type n M G H V v T u ls ->
    n > 0 ->
    u -> psub (plift ls) (st_locs M).
Proof. 
  intros T. induction T; intros; destruct v; destruct n; simpl in *; intuition.
  + subst. unfoldq. intuition.
Qed.

Lemma valt_closed: forall T M G H V v ls n u,
    val_type n M G H V v T u ls ->
    n  > 0 ->
    closed_ty (length H) T.
Proof. 
  intros T. induction T; intros; try constructor; destruct v; destruct n; simpl in *; intuition.
Qed.

Lemma valt_zero: forall M H G V vx T u lsx,
    val_type 0 M H G V vx T u lsx.
Proof.
  intros. destruct vx, T; simpl; eauto.
Qed.

Lemma valt_step: forall m n, n < m -> forall n1 v1 M M1 H G V T1 u ls,
    val_type n M H G V v1 T1 u ls ->
    st_extend n n1 M M1 -> 
    val_type n1 M1 H G V v1 T1 u ls.
Proof.
  intros m. induction m. lia. intros.
  remember H2 as SC. 
  destruct H2 as (A & B & C & D & E).

  destruct n1. destruct v1, T1; simpl in H1; simpl; eauto. destruct n. lia.
  destruct v1, T1; simpl in H1; try contradiction.
  - simpl. eauto.
  - simpl. intuition.
    intros ? ?. eapply H5 in H6. auto.
    destruct H7 as (vt & qt & ? & ? & ? & ?). 
    eapply E in H6 as XX. destruct XX as (vt' & IM & ?).

    exists vt', qt. split. 2: split. 3: split. 
    auto.
    auto. 
    auto.
    eapply vtyp_equiv_dec with (j:= S n1) in H9. 2: lia.
    unfold vtyp_equiv in *. congruence.

  - simpl. intros. intuition.
    intros ? ?. unfoldq; intuition.
    
    assert (b4 || uy && b1 = true -> st_chain (S n) (n1 - nx) M M' (plift ls)) as SC'. {
      intros. eapply stchain_chain. eauto. eapply H7. eauto.
      intros ? ?. split; auto. destruct b4; destruct uy; destruct b1; unfoldq; intuition.
    }
    (*
    assert (env_accs (n - n1 + nx) M' V (por (plift q1) (pif uy (plift q0)))) as envx'. {
      eapply envx_step. 2: eapply H13.  lia.
    } *)
    
    assert (n-(n-n1+nx) = n1-nx) as R. lia.
    specialize (H8  S' (n-n1+nx) M' vx lsx uy); intuition.
    rewrite R in H17. eapply H17; eauto. 
Qed.

Lemma valt_step': forall n n1 v1 M H G V T1 u ls,
    val_type n M H G V v1 T1 u ls ->
    n1 <= n ->
    val_type n1 M H G V v1 T1 u ls.
Proof.
  intros. eapply valt_step. 2: eauto. eauto.
  eapply st_extend_refl'. eauto. 
Qed.

Lemma valt_store_change:  forall m n, n < m -> forall n1 v M M1 H G V T u ls p,
    val_type n M G H V v T u ls ->
    (* (u -> st_chain n n1 M M' p) -> *)
    (st_chain n n1 M M1 p) ->
    psub (plift ls) p ->
    val_type n1 M1 G H V v T u ls.
Proof.
  intros m. induction m. lia. intros.
  remember H2 as SC. 
  destruct H2 as (A & B & C & D & E).

  destruct n1. eapply valt_zero. destruct n. lia. 
  destruct v, T; simpl in H1; try contradiction.
  - simpl. eauto.
  - simpl. intuition.
    intros ? ?. eapply H6 in H7. unfold st_locs, pnat in *. lia.
    destruct H8 as (vt & qt & ? & ? & ? & ?). 
    eapply E in H7 as XX. destruct XX as (vt' & IM & ?).
    exists vt', qt. split. 2: split. 3: split. 
    auto.
    auto.
    auto. 
    eapply vtyp_equiv_dec with (j:= S n1) in H10. 2: lia.
    unfold vtyp_equiv in *. congruence.
  - simpl. intros. intuition.
    intros ? ?. unfoldq; intuition.
    
    assert (b4 || uy && b1 = true -> st_chain (S n) (n1 - nx) M M' (plift ls)) as SC'. {
      intros. eapply stchain_chain. eauto. eapply H8. eauto.
      intros ? ?. split; auto. 
    }
    (* assert (env_accs (S n) M' V (por (plift q1) (pif uy (plift q0)))) as EACC'. {
      eapply envx_step; eauto.
    } *)

    assert (n-(n-n1+nx) = n1-nx) as R. lia.
    specialize (H9  S' (n-n1+nx) M' vx lsx uy); intuition.
    rewrite R in H18. eapply H18; eauto.
Qed.

Lemma valt_store_change':  forall m n, n < m -> forall v M M1 H G V T u ls,
    val_type n M G H V v T u ls ->
    (u -> False) -> 
    val_type n M1 G H V v T u ls.
Proof.
  intros m. induction m. lia. intros.

  destruct n. eapply valt_zero. 
  destruct v, T; simpl in H1; try contradiction.
  - simpl. eauto.
  - simpl. intuition.
  - simpl. intros. intuition.
    eapply H9; eauto. 

    intros. destruct H2. destruct b4,uy,b1; eauto. 
Qed.



Lemma valt_useable: forall T M G H V v (u u': Prop) ls n,
    val_type n M G H V v T u ls ->
    (u' -> u) ->
    val_type n M G H V v T u' ls.
Proof. 
  intros T. induction T; intros; destruct v; destruct n; simpl in *; intuition.
  - destruct H7 as [vt [qt ?]]. exists vt, qt; intuition.
    unfold vtyp_equiv in *. rewrite H10. f_equal. f_equal. 
    eapply functional_extensionality. intros ?. eapply functional_extensionality. intros. 
    eapply functional_extensionality. intros.  eapply functional_extensionality. intros. 
    eapply propositional_extensionality. split; intros; eapply IHT; eauto. 
  - eapply H8; eauto.
Qed.


Lemma ista_valt: forall T G H V u ,
  istypeA (vt_wrap1 (fun (n : nat) (M : stty)(v : vl)(lsv: ql)  => val_type n M G H V v T u lsv)).
Proof.
  intros. intros ? ? ? ? ? ? ? ? ? ? ?.
  unfold vtyp_elem, vt_elem in *.
  specialize (H3 nx).
  destruct j. simpl. eauto. 
  destruct n. destruct H2 as [? ?]. lia.
  eapply valt_step. 2: eauto. eauto.
  eapply st_extend_apprx. eauto. eauto. eauto. 
Qed.


(* 
How to deal with equalities that can't be destructed - see:
http://adam.chlipala.net/cpdt/html/Cpdt.Equality.html

(In the end this wasn't necessary)

Import Eqdep.

Check UIP_refl. (* see http://adam.chlipala.net/cpdt/html/Cpdt.Equality.html *)
Check eq_rect_eq.

Lemma aa1: forall n1 (q1:n1=n1) (vt1: vtypen n1), 
    vt1 = a1 n1 n1 q1 vt1.
Proof.
  intros.
  assert (q1 = eq_refl). eapply UIP_refl.
  unfold a1, eq_rect. rewrite H. eauto. 
Qed. 

*)

Lemma sttyw_eq: forall n1 n2 M1 (q: n1 = n2),
    stty_wrap n1 M1 = stty_wrap n2 (sttyn_aux_eq _ _ q M1).
Proof.
  intros. subst n1.
  unfold sttyn_aux_eq, eq_rect.
  eauto.
Qed.

Lemma istc_valt: forall nu T G H V u,
  istypeC nu (vt_wrap1 (fun (n : nat) (M : stty) (v : vl)(lsv: ql) => val_type n M G H V v T u lsv)).
Proof.
  intros. unfold istypeC. intros.
  extensionality n1.
  unfold vt_approx, vt_apprx, vt_wrap, vt_wrap1.
  destruct (le_dec n1 j).
  destruct (lt_dec n1 (S j)). 2: lia.
  destruct j, n1. simpl. eauto. simpl.
  destruct (aux_lt1 n1 l). simpl. eauto.

  extensionality nz.
  extensionality M.
  extensionality vz.
  unfold vt_dec. 
  erewrite <-sttyw_eq.
  assert ((S j - (j - n1 + nz)) = (S n1 -nz)). lia. rewrite H1. eauto.

  destruct (lt_dec n1 (S j)). destruct n1. lia. lia. eauto. 
Qed.

Lemma ista_approx: forall n vt,
    istypeA vt ->
    istypeA (vt_approx n vt).
Proof.
  intros. intros ? ? ? ? ? IM IM' ? ? ?.
  eapply H in H1 as H3. destruct H1 as (? & ? & ? & ? & ?). clear l0 e.

  unfold vtyp_elem in *.  
  intros. 
  unfold vt_approx in *.
  destruct (lt_dec n0 n). 2: { destruct n0,H2; eauto. }
  destruct (lt_dec j n). 2: lia. eauto.
  eauto. eauto. 
Qed.


Lemma istc_step': forall nu n vt,
    istypeC nu vt ->
    n <= nu ->
    istypeC n vt.
Proof.
  intros. intros ? ?. eapply H. lia. 
Qed.


Lemma istc_approx: forall nu n vt,
    istypeC nu vt ->
    n <= nu ->
    istypeC n (vt_approx n vt).
Proof.
  intros. unfold istypeC in *. intros.  
  assert (j < nu). lia.
  extensionality n1.
  specialize (H j). eapply equal_f_dep with (x:=n1) in H. 2: lia. 
  unfold vt_approx, vt_apprx, vt_wrap in *.
  destruct (le_dec n1 j). 
  destruct (lt_dec n1 (S j)). 2: lia. 
  destruct (lt_dec j n). 2: lia. 
  destruct (lt_dec n1 n). 2: lia. eauto. 
  destruct (lt_dec n1 (S j)). 2: eauto.
  destruct (lt_dec n1 n). eauto. eauto.
Qed.


Definition isstoretypeC nu (M: list (vtype * ql)) :=
  forall x vt q, indexr x M = Some (vt, q) -> istypeC nu vt.

Lemma isstc_to_d: forall n1 M,
  isstoretypeC n1 M ->     
  isstoretypeD n1 M.
Proof.
  intros. intros ? ?. unfold isstoretypeC in H. 
  unfold stty_apprx, stty_approx, stty_wrap, stty_pick.
  rewrite map_map. induction M.
  simpl. eauto. simpl.
  rewrite IHM. destruct a. rewrite <-H. eauto. eapply indexr_head. eauto.
  intros. eapply H. rewrite indexr_skip. eauto. eapply indexr_var_some' in H1. lia. 
Qed.

Lemma isstd_approx: forall nu n M,
    isstoretypeD nu M ->
    n <= nu ->
    isstoretypeD n (stty_approx n M).
Proof.
  intros. unfold isstoretypeD in *. intros.
  assert (j < nu). lia.
  specialize (H j H2). rewrite stty_approx_neutral, <-H.
  unfold stty_apprx, stty_wrap, stty_pick, stty_approx.
  repeat rewrite map_map. eapply map_eq_f.
  extensionality vt. destruct vt.
  unfold vt_wrap, vt_approx. f_equal. 
  extensionality n1.
  destruct (le_dec n1 j). 2: eauto.
  destruct (lt_dec j n). 2: lia. eauto. lia. 
Qed.





Lemma storet_empty: forall n,
    store_type n [] [].
Proof.
  intros. split. eauto. intros. inversion H. 
Qed.

Lemma storet_step': forall n n1 S M,
      store_type n S M ->
      n1 <= n ->
      store_type n1 S M.
Proof.
  intros. destruct H. split. eauto.
  intros. edestruct H1 as (TY & TYB & v & ? & ? & ? & ? & ?). eauto.
  split. 2: split. eapply TY. eapply istc_step'. eapply TYB. lia. exists v. exists x. 
  split. 2: split. 3: split. eauto.
  bdestruct (n1 =? n). subst n1. eauto. 
  eapply vte_approx. eauto. eauto. auto. auto. 
Qed.

Lemma storet_approx: forall n n1 S M,
      store_type n S M ->
      n1 < n ->
      store_type n1 S (stty_approx n1 M).
Proof.
  intros. destruct H. split. unfold stty_approx. rewrite map_length. eauto.
  intros. unfold stty_approx in H2.
  eapply indexr_var_some' in H2 as H3. rewrite map_length in H3.
  eapply indexr_var_some in H3. destruct H3. destruct x.
  eapply indexr_map with (f := fun vt => vt_approx n1 vt) in H3  as H4.  
  rewrite  H2 in H4.
  inversion H4. subst vt. clear H4.

  edestruct H1 as (TY & TYB & v' & ? & ? & ? & ? & ?). eauto.
  split. 2: split.
  eapply ista_approx. eapply TY.
  eapply istc_approx. eapply TYB. lia. 
  exists v', x. split. 2: split. 3: split. eauto.
  intros ? ?. rewrite vt_approx_neutral, stty_approx_neutral. 2,3: lia.
  eapply vte_approx. eauto. 1,2: lia. auto. auto.
Qed.



Lemma storet_extend: forall n n1 S S1 M M1 vx vt qt ls q V
    (ST: store_type (n) S M) 
    (ST1: store_type (n1) S1 M1) 
    (SC: st_extend n n1 M M1)
    (TA: istypeA vt)
    (TC: istypeC n1 vt) 
    (VT': vtyp_elem_approx n1 vt ((vt,qt)::M1) vx ls)
   (* (VT: vt = vt_approx n (vt_wrap1 (fun n M v lsv => psub (plift lsv) (plift qt) /\ val_type n M  G E V v T (u = true) lsv))) *)
    (HQX: val_qual M M1 V ls false (plift q))
    (QT: qt = vars_locs_fix V q)
    (WFQT: psub (plift qt) (st_locs M)),
    store_type (n1) (vx :: S1) ((vt, qt) :: M1). 
Proof. 
  intros. destruct ST1. split.
  - simpl. lia.
  - intros. bdestruct (i <? length M1).
    + rewrite indexr_skip in H1. 2: lia. eapply H0 in H1.
      destruct H1 as (TY & TYB & v & ? & ? & ? & ? & ?).
      split. 2: split. 
      eapply TY. eapply TYB. 
      exists v, x. split. 2: split. 3: split. 
      rewrite indexr_skip. 2: lia. eauto.
      assert (istypeA (vt_approx n1 vt0)). eapply ista_approx; eauto.
      intros ? ?. eapply H6. 4: eauto.
      eapply isstd_approx. eapply isstc_to_d. intros ? ? ? IX. eapply H0 in IX. eapply IX. lia.
      eapply isstd_approx. eapply isstc_to_d. intros ? ? ? IX. bdestruct (x0 =? length M1).
      subst x0. rewrite indexr_head in IX. inversion IX. subst vt qt.  eauto. 
      rewrite indexr_skip in IX. 2: eauto. eapply H0 in IX. eapply IX. lia. 
      simpl. 
      eapply st_extend'. eauto.
      auto.
      auto. 
    + eapply indexr_var_some' in H1 as IL. simpl in IL. 
      replace i with (length S1). 2: lia. rewrite indexr_head. 
      replace i with (length M1) in H1. 2: lia. rewrite indexr_head in H1.
      inversion H1. subst vt0.
      split. 2: split. eauto. eauto. subst qt0. 
      exists vx, ls. split. 2: split. 3: split. eauto. eauto. 
      intros ? ?.  destruct (HQX x); try contradiction. auto. subst qt. rewrite plift_vars_locs. auto.
      intros ? ?. eapply WFQT in H3. eapply st_mono in SC. unfold st_locs in *. unfoldq. lia.
Qed.


Lemma storet_isstd: forall n S M,
    store_type n S M ->
    isstoretypeD n M.
Proof.
  intros. eapply isstc_to_d. intros ? ? ? ?. eapply H in H0. eapply H0.
Qed.




(* ---------- vtype/stchain conversion helper lemmas  ---------- *)

Lemma stchain_aux_ref': forall n2 j nx0 M',
    isstoretypeD n2 M' ->
    S j < n2 ->
    st_extend n2 (S j - nx0)
      (stty_approx n2 M')
      (stty_apprx (j - nx0) (stty_approx (S j) (stty_approx n2 M'))).
Proof.
  intros. 
  rewrite stty_approx_neutral.
  eapply isstd_approx in H.
  erewrite H. 
  rewrite stty_approx_neutral. 2-5: lia.

  replace (stty_approx (S (j - nx0)) M') with ((stty_approx (S (j - nx0)) (stty_approx n2 M'))). 2: { rewrite stty_approx_neutral. eauto. lia. }
  
  eapply stchain_step''. eapply st_extend_approx. lia. lia. 
Qed.

Lemma stchain_aux_ref: forall n2 j nx0 M' vt,
    isstoretypeD n2 M' ->
    S j < n2 ->
    st_extend n2 (S j - nx0)
      (stty_approx n2 M')
      (stty_apprx (j - nx0) (stty_approx (S j) (vt :: (stty_approx n2 M')))).
Proof.
  intros. remember (S j - nx0).
  unfold stty_approx, stty_apprx, stty_wrap, stty_pick. simpl. subst n. 
  eapply stchain_chain. 2: eapply st_extend'. 2: eauto. 
  eapply stchain_aux_ref'. eauto. eauto. 
  unfold st_locs, stty_approx, pnat. rewrite map_length. rewrite map_length. rewrite map_length.
  rewrite map_length. rewrite map_length.  unfoldq; intuition.
Qed.

Lemma stchain_aux_get: forall nx1 M',
    isstoretypeD (S nx1) M' ->

    st_extend (S nx1) (S nx1)
      (stty_apprx (nx1 - 0) (stty_approx (S nx1) M'))
      (stty_approx (S nx1) M').    
Proof. 
  intros. replace (nx1 - 0) with nx1. 2: lia. 
  eapply isstd_approx in H.
  erewrite H, stty_approx_neutral.
  eapply st_extend_refl. all: lia. 
Qed.

Lemma stchain_aux_put: forall ny1 nx0 j M2,
    isstoretypeD (S ny1) M2 ->
    j < ny1 ->
    st_extend (Datatypes.S ny1) (Datatypes.S j - nx0)
      M2
      (stty_apprx (j - nx0) (stty_approx (Datatypes.S j) M2)).
Proof.
  intros.
  eapply isstd_approx in H.
  erewrite H, stty_approx_neutral.
  eapply stchain_step''. eapply st_extend_approx. all: lia. 
Qed.

(* ---------- environment lemmas  ---------- *)



Lemma envt_step: forall n n1  H G V,
    env_type n H G V ->
    n1 <= n ->
    env_type n1 H G V.
Proof.
  intros. destruct H0 as [? [? ?]]. split. 2: split.
  auto. auto.
  intros. eapply H3 in H4. destruct H4 as [? [? [? [? [? ?]]]]]. 
  eexists. eexists. eexists. eexists. eexists. intuition eauto.
  eapply valt_step'; eauto. 
Qed.


Lemma envq_tighten: forall G V p p',
    env_qual G V p ->
    psub p' p ->
    env_qual G V p'.
Proof.
  intros. intros ? ? ? ?.
  intros ? Q. eapply H.
  unfoldq. intuition.
  unfoldq. intuition.
  eauto. 
Qed.

Lemma envx_tighten: forall n M V p p',
  env_accs n M V p ->
  psub p' p ->
  env_accs n M V p'.
Proof.
  intros. intros ? ?.
  eapply H. eauto. 
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


(* ---------- LR compatibility lemmas  ---------- *)

Lemma sem_true: forall G p,
    sem_type G ttrue TBool p false pempty.
Proof.
  intros. intros n S M E V U WFE ENQ ENACE ST. intros ? ? ? EV.
  destruct n; inversion EV. subst n' S' r.
  assert (Datatypes.S n - 1 = n) as R. lia. 
  exists M, (vbool true), qempty.
  split. 2: split. 3: split. 4: split. 5: split.
  - rewrite R. eapply st_extend_refl'. lia. 
  - rewrite R. eapply storet_step'; eauto. 
  - eauto.
  - destruct n; simpl; eauto.
  - unfoldq; intuition.
  - auto.
Qed.

Lemma sem_false: forall G p,
    sem_type G tfalse TBool p false pempty.
Proof.
  intros. intros n S M E V U WFE ENQ ENACE ST. intros ? ? ? EV.
  destruct n; inversion EV. subst n' S' r.
  assert (Datatypes.S n - 1 = n) as R. lia. 
  exists M, (vbool false), qempty.
  split. 2: split. 3: split. 4: split. 5: split.
  - rewrite R. eapply st_extend_refl'. lia. 
  - rewrite R. eapply storet_step'; eauto. 
  - eauto.
  - destruct n; simpl; eauto.
  - unfoldq; intuition.
  - auto. 
Qed.

Lemma sem_var: forall G x T (p: pl) fr q,
    indexr x G = Some (T, fr, q) ->
    sem_type G (tvar x) T p false (pone x).
Proof.
  intros ? ? ? ?  ? ? IX. intros n S M E V u WFE WFQ WFX ST. intros ? ? ? EV.
  destruct n; inversion EV. subst n' S' r.
  destruct WFE as [? [? WFE]].
  destruct (WFE x T fr q IX) as [vx [uy [lsx [Mx [nx [HQ [TL1 [TL [IH [IV [VT ?]]]]]]]]]]].
  assert (Datatypes.S n - 1 = n) as R. lia. 
  destruct u. { 
      assert ((por p (pif true (pone x))) x) as A. { right. unfoldq; intuition. }
      destruct (WFX x A) as (j & Mj & ? & ? & ? & ? & ?). 
      rewrite IV in H2. inversion H2. subst j Mj x0 x1.
      exists M, vx, lsx.
      split. 2: split. 3: split. 4: split. 5: split.
      - rewrite R. eapply st_extend_refl'. lia. 
      - rewrite R. eapply storet_step'; eauto.
      - eauto.
      - assert (uy = (true = true)).
        eapply propositional_extensionality. intuition.
        rewrite <- H5.   
        eapply valt_step' with (n1 := (Datatypes.S n -1)) in VT. 2: { lia. }
        eapply valt_store_change. 2: eapply VT. eauto. 2: intros ? ?; eauto.
        assert (Datatypes.S n <= nx). { eapply H4. }        
        eapply stchain_step'' with (n2:=Datatypes.S n - 1) in H4. 2: lia.
        eapply stchain_step''' with (n':=Datatypes.S n - 1) in H4. 2: lia. 
        eauto. 
      - clear A. left. unfoldq. intros. exists x; intuition.
        unfold var_locs. exists nx, Mx, uy, lsx. intuition.
      - intros ? Q. destruct Q as (? & P & ? & ? & ? & ? & IV2 & ?).
        inversion P. subst. congruence.
  } {
    exists M, vx, lsx.
    split. 2: split. 3: split. 4: split. 5: split.
    - rewrite R. eapply st_extend_refl'. lia. 
    - rewrite R. eapply storet_step'; eauto.
    - auto.
    - eapply valt_step'. eapply valt_store_change'. eauto. eapply valt_useable. eauto.
      intuition. intuition. lia. 
    - left. unfoldq. intros. exists x; intuition.
      unfold var_locs. exists nx, Mx, uy, lsx. intuition.
    - intros ? Q. destruct Q as (? & P & ? & ? & IV2 & ? & ? & ?).
    inversion P. subst. congruence. 
  }
Qed.


Lemma sem_ref: forall G t p T q,
    sem_type G t T p false (plift q) ->
    psub (plift q) p ->
    psub p (pdom G) ->
    sem_type G (tref t) (TRef T false q) p true pempty.
Proof.
  intros ? ? ? ?  ? HX. intros SUB SUB1 n S M E V u WFE WFQ WFX ST. intros n1 S1 r1 EV.
  destruct n; simpl in EV. inversion EV.
  
  remember (teval n S E t) as tx. symmetry in Heqtx. destruct tx as [[nx S'] [rx|]]. 2: inversion EV.
  edestruct (HX (1+n) S M E V u) as (M' & vx & ls' & SC' & ST' & RX & VX & VQ & Ht). eauto. 
  {
    eapply envq_tighten; eauto. destruct u; unfoldq; intuition.
  }
  {
    eapply envx_tighten. eapply WFX. destruct u; unfoldq; intuition.
  }
  eauto. 
  eapply eval_deterministic. eauto. eauto. lia. 
  eapply eval_bounded in Heqtx as BX; eauto.
  subst rx.

  inversion EV. subst n1 S1 r1.

  replace (Datatypes.S n - Datatypes.S nx) with (n-nx) in *. 2: lia.
  remember (n-nx) as n2. 
  remember (n2-1) as n3. 

  remember (vars_locs_fix V q) as qt.
  remember (vt_wrap1 (fun n M v lsv => val_type n M  G E V v T (u = true) lsv)) as vt. 
  remember (stty_approx (n2) M') as MA.
  remember (vt_approx (n2) vt) as vta. 
  
  assert (st_extend (1+n-nx) (n2) M' MA) as SCA. {
    subst MA. eapply st_extend_approx. lia. }

  assert (st_extend (1+n-nx) n2 M' ((vta, qt)::MA)) as SCAE. {
    subst MA. eapply stchain_chain. 2: eapply st_extend'. eauto. lia.
    intros ? ?. split. auto. unfold st_locs, pnat in *. unfold stty_approx. rewrite map_length. lia.   }

  
  assert (val_type n2 MA G E V vx T (u = true) ls'). {
    eapply valt_step; eauto. (* destruct n2. replace n3 with 0. eauto. 
    eapply stchain_step''. eauto. lia.*) }
  
  exists ((vta, qt) :: MA), (vref (length S')), (qone (length S')).
  split. 2: split. 3: split. 4: split. 5: split.
  - subst MA. 
    eapply stchain_chain with (p2 := (st_locs M)). eauto. eapply stchain_chain.
    2: { eapply st_extend'. eauto. } eapply SCA.
    intros ? ?. split. unfold st_locs, pnat in *. eapply st_mono in SC'. lia.
    unfold st_locs, pnat in *. unfold stty_approx. rewrite map_length. eapply st_mono in SC'. lia.
    unfoldq; intuition.
  - eapply storet_extend with (ls := ls'). eapply ST. subst MA. eapply storet_approx. eauto. lia.
    {  eapply st_extend_chain. eapply SC'. eapply SCA. }
    subst vt vta. eapply ista_approx. eapply ista_valt.
    subst vt vta. eapply istc_approx. eapply istc_valt. eauto. 

    intros. unfold vtyp_elem_approx, vtyp_elem, vt_approx. 

    intros. 
    remember (lt_dec j n2). destruct s. 2: lia.

    subst vta vt MA. 

    unfold vt_approx.
    unfold vtyp_elem, vt_elem.
    unfold vt_wrap1.

    rewrite <-Heqs. 

    destruct j. eauto. 
    eapply valt_step. 2: eauto. eauto. 
    eapply stchain_aux_ref. eapply storet_isstd. eapply storet_step'. eauto. lia. eauto.
    

    eauto. auto. subst qt. rewrite plift_vars_locs. eapply envx_wf; eauto. intros ? ?. left. auto.
    
  - eauto.
  - simpl. destruct n2; try contradiction. auto.
    subst MA. assert (length S' = length M') as L. { destruct ST'. auto. }
    split. 2: split. 3: split. 4: split.
    -- eapply valt_closed; eauto. lia.
    -- intros ? ?. eapply SUB in H0. eapply SUB1 in H0. destruct WFE. unfoldq. lia.
    -- rewrite plift_one. unfoldq; intuition.
    -- rewrite plift_one. 
       unfold st_locs, pnat. simpl. unfold stty_approx. rewrite map_length. 
       unfoldq; intuition. 
    -- exists vta, qt. 
       unfold stty_approx. rewrite map_length. 
       split.  2: split. 3: split.
       bdestruct (length S' =? length M'); intuition.
       rewrite pif_false, por_empty_r. subst qt. rewrite plift_vars_locs. intros ? ?. auto.
       subst qt. rewrite plift_vars_locs. intros ? ?. auto.
       {
       subst vta vt. 
       unfold vtyp_equiv. rewrite vt_approx_neutral. auto. auto.
       }
       
  - intros ? Q. rewrite plift_one in Q. inversion Q. subst x. 
      right. simpl. split. unfold st_locs, pnat. simpl. rewrite HeqMA. 
      unfold stty_approx. rewrite map_length.  destruct ST'. lia.
      intros ?. unfold st_locs, pnat in H0. destruct ST. destruct ST'. eapply st_mono in SC'. lia.
  - auto.
Qed.

Lemma sem_get: forall G t p T fr q q1,
    sem_type G t (TRef T false q1) p fr q ->
    psub q p -> (* effect *)
    sem_type G (tget t) T p false (plift q1).
Proof.
  intros ? ? ? ?  ? ? ? HX. intros SUB.  intros n  ? ? ? ? u  WFE WFQ WFX ST.  
  intros n1 S1 r1 EV.
  assert (env_qual G V (por p (pif true q))) as WFQ1. {
    eapply envq_tighten. eauto. unfoldq. intuition.  }
  destruct n. inversion EV. simpl in EV. 

  remember (teval n S H t) as tx. symmetry in Heqtx. destruct tx as [[nx S'] [rx|]]. 2: inversion EV.
  edestruct (HX (1+n) S M H V true) as (M' & vx & lsx & SC' & ST' & RX & VX & VQX). eauto. eauto.
  {
    eapply envx_tighten. eauto. unfoldq; intuition. 
  }
  eauto. eapply eval_deterministic. eauto. eauto. lia. 
  eapply eval_bounded in Heqtx as BX; eauto.
  subst rx.

  remember (1 + n - nx) as nx1. destruct nx1. lia. 
  simpl in VX. destruct vx; try contradiction. 
  
  inversion EV. subst n1 S1 r1. 
 
  destruct VX as (HT & Q1 & LSX). intuition. 
  destruct H7 as  (vt & qt & IX & QT1 & QT2 & VT). 
  destruct ST' as (L & B). eapply B in IX as IX1.
  destruct IX1 as (TY & TYB & vx & lsx' & IS & VT' & QT1' & QT2'). 

  exists (stty_approx (n-nx) M'), vx, lsx'. 
  split. 2: split. 3: split. 4: split. 5: split.
  - eapply stchain_chain. eauto. eapply st_extend_approx. lia.
    intros ? ?. split. auto. unfold st_locs, pnat in *. eapply st_mono in SC'. lia. 
  - eapply storet_approx. split; eauto. lia. 
  - eauto.
  - unfold vtyp_elem_approx in VT'. 
    assert (nx1 = n-nx). lia.
    replace ((Datatypes.S n - Datatypes.S nx)) with nx1 in *.
    rewrite <-H6 in *. 

    unfold vtyp_equiv in VT. rewrite VT in VT'. 

    assert (nx1 < Datatypes.S nx1). lia. 
    eapply VT' in H7.
    
    unfold vtyp_elem, vt_elem, vt_approx, vt_wrap1 in H7.
    destruct nx1. eapply valt_zero.

    remember (lt_dec (nx1) (Datatypes.S nx1)). destruct s. 2: lia.
    remember (lt_dec (Datatypes.S nx1) (Datatypes.S (Datatypes.S nx1))). destruct s. 2: lia.

    specialize (H7 0). 
    replace (Datatypes.S nx1 - 0) with (Datatypes.S nx1) in *. 2: lia.
    
    eapply valt_step. 
    3: { eapply stchain_aux_get. eapply storet_isstd. eapply storet_step'. split; eauto. lia. } 
    2:  {  eapply valt_useable. eauto. eauto.   }  eauto.
  - unfoldq. intuition.
  - auto.   
Qed.


Lemma sem_put: forall G t t2 T fr1 q1 fr2 q2 e,
    sem_type G t (TRef T fr2 q2) e fr1 (plift q1) ->
    sem_type G t2  T e false (plift q2) ->
    psub (plift q1) e -> (* effect *)
    psub (plift q2) e ->  
    sem_type G (tput t t2) TBool e false pempty.
Proof.
  intros ? ? ? ? ? ? ? ? ? HX HY. intros SUB1 SUB2 n S M E V u WFE WFQ WFX ST. 
  intros n3 S3 r3 EV.
  assert (env_qual G V (por e (pif true (plift q2)))) as WFQ1. {
    eapply envq_tighten. eauto. unfoldq. intuition. }
  
  assert (env_qual G V (por e (pif true (plift q1)))) as WFQ2. {
    eapply envq_tighten. eapply WFQ. unfoldq. intuition. }  
  destruct n. inversion EV. simpl in EV. 
    
  remember (teval n S E t) as tx. symmetry in Heqtx. destruct tx as [[nx S1] [rx|]]. 2: inversion EV.
  edestruct (HX (1+n) S M E) as (M1 & vx & lsx & SC1 & ST1 & RX & VX & VQX & Htx). eauto. eauto. 
  {
    eapply envx_tighten. eauto. unfoldq; intuition. 
  }
  eauto.
  eapply eval_deterministic. eauto. eauto. lia. 
  eapply eval_bounded in Heqtx as BX; eauto.
  subst rx.

  remember (1 + n - nx) as nx1. destruct nx1. lia. 
  simpl in VX. destruct vx; try contradiction.

  remember (teval (n-nx) S1 E t2) as ty. symmetry in Heqty. destruct ty as [[ny S2] [ry|]]. 2: inversion EV.
  edestruct (HY (1+n-nx) S1 M1 E) as (M2 & vy & lsy & SC2 & ST2 & RY & VY & VYQ & Hty).
  eapply envt_step. eauto. lia. eauto.
  {
    eapply envx_store_extend. eapply envx_tighten.  eapply WFX.
    unfoldq; intuition.
    replace (Datatypes.S n) with (1 + n). 2: { lia. }
    eapply stchain_step''; eauto. lia.
  }
  
  rewrite Heqnx1 in ST1. eapply ST1.

  eapply eval_deterministic. 2: eauto. eauto. lia. 
  eapply eval_bounded in Heqty as BY; eauto.
  subst ry.

  remember (1+n-nx-ny) as ny1. destruct ny1. lia.
  simpl in VX. destruct VX as (HT & Q1 & LSX1 & LSX2 & vt & qt & IM1 & QT1 & QT2 & VT). intuition. 

  destruct ST1 as (L1 & B1). 
  remember ST2 as ST2'. clear HeqST2'.
  destruct ST2' as (L2 & B2). 
  eapply SC2 in IM1. destruct IM1 as (vtx2 & IX2 & EQ2). 
  eapply indexr_var_some' in IX2 as IX3. 
  assert (i < length S2) as VX'. lia. 
  eapply indexr_var_some in VX'. destruct VX' as (vx & IX).
  rewrite IX in EV. inversion EV. subst n3 S3 r3.

  eapply B2 in IX2 as IX4. destruct IX4 as (TY & TYB & vtx' & lsx' & ? & AB & ? & ?) .
  rewrite IX in H. inversion H. subst vtx'. 
  
  exists (stty_approx (n-nx-ny) M2), (vbool true), qempty. 
  split. 2: split. 3: split. 4: split. 5: split.
  - eapply st_extend_chain. eauto. eapply st_extend_chain. 
    eapply st_extend_step'. eauto. lia.
    eapply stchain_step''. eapply st_extend_approx. lia. lia. 
  - eapply storet_step'. eapply storet_approx. split; eauto.
    rewrite <-update_length. eauto. 
    intros.  bdestruct (i0 =? i).
    + subst i0. rewrite IX2 in H2. inversion H2. subst vt0 qt0.
      split. 2: split. eauto. eauto. 
      exists vy, lsy. rewrite update_indexr_hit; eauto. 2: lia. 
      split. 2: split. 3: split. eauto. 

      unfold vtyp_equiv in *. 
      intros ? ?.  rewrite <-EQ2. eapply vtyp_equiv_dec in VT. rewrite VT. 2: lia. 
      intros ?. unfold vt_approx. 
      remember (lt_dec (j) (Datatypes.S ny1)). destruct s. 2: lia.
      unfold vt_elem, vt_wrap1.
      destruct j. auto. 
      remember (Datatypes.S j - nx0) as nj.
      destruct nj. eapply valt_zero.
      { eapply valt_step. 2: { eapply VY. } eauto.
        rewrite Heqnj. eapply stchain_aux_put. eapply storet_isstd. eapply storet_step'. eauto. auto. 
        lia.
      }
      
      {
        intros ? ?. destruct (VYQ x); try contradiction. auto.  eapply QT2. auto.
      }
      auto.
      
    + eapply B2 in H2 as IX5.
      rewrite update_indexr_miss; eauto.
    + lia.
    + lia. 
      
  - eauto.
  - simpl. remember (n - (nx + ny)) as ny2. destruct ny2.
    eauto. eauto.
  - intros ? ?. unfoldq; intuition.
  - auto. 
Qed.

(* ---- refs with self ref support (put operation is shared) --- *)

(* constructor for ref with self (use outer qualifier) *)
Lemma sem_ref2: forall t G T p q,
  sem_type G t T p false (plift q) ->
  psub (plift q) p ->
  sem_type G (tref t) (TRef T true qempty) p true (plift q).
Proof. 
  intros ? ? ? ?  ? HX. intros SUB n S M E V u WFE WFQ WFX ST. intros n1 S1 r1 EV.
  destruct n; simpl in EV. inversion EV.

  remember (teval n S E t) as tx. symmetry in Heqtx. destruct tx as [[nx S'] [rx|]]. 2: inversion EV.
  edestruct (HX (1+n) S M E V u) as (M' & vx & ls' & SC' & ST' & RX & VX & VQ & Ht). eauto. 
  {
    eapply envq_tighten; eauto. destruct u; unfoldq; intuition.
  }
  {
    eapply envx_tighten. eapply WFX. destruct u; unfoldq; intuition.
  }
  eauto. 
  eapply eval_deterministic. eauto. eauto. lia. 
  eapply eval_bounded in Heqtx as BX; eauto.
  subst rx.

  inversion EV. subst n1 S1 r1.

  replace (Datatypes.S n - Datatypes.S nx) with (n-nx) in *. 2: lia.
  remember (n-nx) as n2. 
  remember (n2-1) as n3. 

  remember (vars_locs_fix V q) as qt.
  remember (vt_wrap1 (fun n M v lsv => val_type n M  G E V v T (u = true) lsv)) as vt. 
  remember (stty_approx (n2) M') as MA.
  remember (vt_approx (n2) vt) as vta. 

  assert (st_extend (1+n-nx) (n2) M' MA) as SCA. {
    subst MA. eapply st_extend_approx. lia. }

  assert (st_extend (1+n-nx) n2 M' ((vta, qt)::MA)) as SCAE. {
    subst MA. eapply stchain_chain. 2: eapply st_extend'. eauto. lia.
    intros ? ?. split. auto. unfold st_locs, pnat in *. unfold stty_approx. rewrite map_length. lia.   }


  assert (val_type n2 MA G E V vx T (u = true) ls'). {
    eapply valt_step; eauto. (* destruct n2. replace n3 with 0. eauto. 
    eapply stchain_step''. eauto. lia.*) }

  exists ((vta, qt) :: MA), (vref (length S')), (qor (qone (length S')) qt).
  split. 2: split. 3: split. 4: split. 5: split.
  - subst MA. 
    eapply stchain_chain with (p2 := (st_locs M)). eauto. eapply stchain_chain.
    2: { eapply st_extend'. eauto. } eapply SCA.
    intros ? ?. split. unfold st_locs, pnat in *. eapply st_mono in SC'. lia.
    unfold st_locs, pnat in *. unfold stty_approx. rewrite map_length. eapply st_mono in SC'. lia.
    unfoldq; intuition.
  - eapply storet_extend with (ls := ls'). eapply ST. subst MA. eapply storet_approx. eauto. lia.
    {  eapply st_extend_chain. eapply SC'. eapply SCA. }
    subst vt vta. eapply ista_approx. eapply ista_valt.
    subst vt vta. eapply istc_approx. eapply istc_valt. eauto. 

    intros. unfold vtyp_elem_approx, vtyp_elem, vt_approx. 

    intros. 
    remember (lt_dec j n2). destruct s. 2: lia.

    subst vta vt MA. 

    unfold vt_approx.
    unfold vtyp_elem, vt_elem.
    unfold vt_wrap1.

    rewrite <-Heqs. 

    destruct j. eauto. 
    
    eapply valt_step. 2: eauto. eauto. 
    eapply stchain_aux_ref. eapply storet_isstd. eapply storet_step'. eauto. lia. eauto.


    eauto. auto. subst qt. rewrite plift_vars_locs. eapply envx_wf; eauto. intros ? ?. left. auto.

  - eauto.
  - simpl. destruct n2; try contradiction. auto.
    subst MA. assert (length S' = length M') as L. { destruct ST'. auto. }
    split. 2: split. 3: split. 4: split.
    -- eapply valt_closed; eauto. lia.
    -- rewrite plift_empty. unfoldq; intuition.
    -- rewrite plift_or, plift_one. unfoldq; intuition.
    -- rewrite plift_or, plift_one. 
       unfold st_locs, pnat. simpl. unfold stty_approx. rewrite map_length. 
       unfoldq; intuition. subst qt. rewrite plift_vars_locs in H4. eapply envx_wf in H4; eauto.
       eapply envx_step. 2: { eapply envx_tighten. eapply envx_store_extend. eauto. eauto. intros ? ?. left. auto. }
       eauto.
    -- exists vta, qt. 
       unfold stty_approx. rewrite map_length. 
       split.  2: split. 3: split.
       bdestruct (length S' =? length M'); intuition.
       rewrite plift_empty, plift_or, plift_one. intros ? ?. right. right. auto.
       rewrite plift_empty. subst qt. rewrite plift_vars_locs. eapply vars_locs_monotonic; eauto. unfoldq; intuition.
           
       {
       subst vta vt. 
       unfold vtyp_equiv. rewrite vt_approx_neutral. auto. auto.
       }

  - intros ? Q. rewrite plift_or, plift_one in Q. destruct Q as [L | Q].
    * right. simpl. inversion L. subst x. subst MA. unfold stty_approx. 
      destruct ST'. destruct SC' as (? & ? & ?). unfoldq. unfold st_locs in *.
      split. unfold st_locs, pnat. simpl. rewrite map_length. lia.
      intros ?. assert (length M <= length M'). { lia. }
      unfold st_locs, pnat in H5.  lia.
    * subst qt. left. rewrite plift_vars_locs in Q. eapply vars_locs_monotonic. 2: eauto. unfoldq. intuition.
  - auto.
Qed.


(* upcast to add self ref, for escaping *)
Lemma sem_ref_sub: forall t G p T fr1 q1 fr2 q2,
    sem_type G t (TRef T fr1 q1) p fr2 q2 ->
    psub (plift q1) p ->
   (*  psub q2 p -> *)
    sem_type G t (TRef T true qempty) p fr2 (por q2 (plift q1)).
Proof.
  intros ? ? ? ?  ? ? ? ? HX. intros SUB1 (* SUB2 *) n S M E V u WFE WFQ WFX ST. 
  intros n1 S1 r1 EV.
  remember EV as EV'. clear HeqEV'.
  destruct n; simpl in EV. inversion EV.

  remember (teval (Datatypes.S n) S E t) as tx. symmetry in Heqtx.
  destruct tx as [[nx S'] [rx|]]. 2: inversion EV'.
  edestruct (HX (1+n) S M E V u) as (M' & vx & ls' & SC' & ST' & RX & VX & VQ & Ht). eauto. 
  {
    eapply envq_tighten; eauto. destruct u; unfoldq; intuition.
  }
  {
    eapply envx_tighten. eapply envx_step. 2: eapply WFX. lia. destruct u; unfoldq; intuition.
  }
  eapply storet_step'. eauto. lia. 
  eauto.
  inversion EV'. subst n1 S1 r1.

  exists M', vx, (qor ls'(vars_locs_fix V q1)).
  split. 2: split. 3: split. 4: split. 5: split.
  - eauto. 
  - eauto.
  - eauto.
  - simpl in VX. simpl. destruct nx; destruct vx; try contradiction.
    -- intuition. rewrite plift_empty. unfoldq;intuition.
       rewrite plift_or. left. auto.
       rewrite plift_or, plift_vars_locs. intros ? [? | ?].
       eapply H3. auto.
       eapply envx_wf in H4. 2: { eapply envx_store_extend; eauto. } eauto.
       intros ? ?. left. auto.
       destruct H5 as [vt [qt ?]].
       exists vt, qt; intuition.
       rewrite plift_or, plift_vars_locs. intros ? ?. eapply H4 in H7. destruct H7.
       right. right. auto. destruct fr1; try contradiction.
       right. left. auto.
       rewrite plift_empty.  unfoldq; intuition. destruct H7 as [? [? ?]]. contradiction. 
    -- destruct (n - nx). auto. contradiction.
    -- destruct (n - nx). auto. intuition.
       rewrite plift_empty. unfoldq;intuition.
       rewrite plift_or. left. auto.
       rewrite plift_or, plift_vars_locs. intros ? [? | ?].
       eapply H3. auto.
       eapply envx_wf in H4. 2: { eapply envx_store_extend; eauto. } eauto.
       intros ? ?. left. auto.
       destruct H5 as [vt [qt ?]].
       exists vt, qt; intuition.
       rewrite plift_or, plift_vars_locs. intros ? ?. eapply H4 in H7. destruct H7.
       right. right. auto. destruct fr1; try contradiction.
       right. left. auto.
       rewrite plift_empty.  unfoldq; intuition. destruct H7 as [? [? ?]]. contradiction. 
    -- destruct (n- nx); auto.

  - (* qualifier *)
    intros ? A. rewrite plift_or in A. destruct A as [Q2 | Q1].
    * eapply VQ in Q2. destruct Q2 as [Q | F]. 
      left. eapply vars_locs_monotonic. 2: eauto. unfoldq. intuition.
      right. eauto.
    * rewrite plift_vars_locs in Q1. left. eapply vars_locs_monotonic. 2: eauto. unfoldq. intuition.
  - destruct t; intuition.
    intros ? ?. rewrite plift_or, plift_vars_locs. left. eauto.
Qed.    

(* get with outer qualifier *)
Lemma sem_get2: forall G t p T fr q,
    sem_type G t (TRef T true qempty) p fr q ->
    psub q p -> (* effect *)
    sem_type G (tget t) T p fr q.
Proof.
  intros ? ? ? ?  ? ? HX. intros SUB.  intros n  ? ? ? ? u  WFE WFQ WFX ST.  
  intros n1 S1 r1 EV.
  assert (env_qual G V (por p (pif true q))) as WFQ1. {
    eapply envq_tighten. eauto. unfoldq. intuition.  }
  destruct n. inversion EV. simpl in EV. 

  remember (teval n S H t) as tx. symmetry in Heqtx. destruct tx as [[nx S'] [rx|]]. 2: inversion EV.
  edestruct (HX (1+n) S M H V true) as (M' & vx & lsx & SC' & ST' & RX & VX & VQX). eauto. eauto.
  {
    eapply envx_tighten. eauto. unfoldq; intuition. 
  }
  eauto. eapply eval_deterministic. eauto. eauto. lia. 
  eapply eval_bounded in Heqtx as BX; eauto.
  subst rx.

  remember (1 + n - nx) as nx1. destruct nx1. lia. 
  simpl in VX. destruct vx; try contradiction. 
  
  inversion EV. subst n1 S1 r1. 
 
  destruct VX as (HT & Q1 & LSX). intuition. 
  destruct H7 as  (vt & qt & IX & QT1 & QT2 & VT). 
  destruct ST' as (L & B). eapply B in IX as IX1.
  destruct IX1 as (TY & TYB & vx & lsx' & IS & VT' & QT1' & QT2'). 

  exists (stty_approx (n-nx) M'), vx, lsx'. 
  split. 2: split. 3: split. 4: split. 5: split.
  - eapply stchain_chain. eauto. eapply st_extend_approx. lia.
    intros ? ?. split. auto. unfold st_locs, pnat in *. eapply st_mono in SC'. lia. 
  - eapply storet_approx. split; eauto. lia. 
  - eauto.
  - unfold vtyp_elem_approx in VT'. 
    assert (nx1 = n-nx). lia.
    replace ((Datatypes.S n - Datatypes.S nx)) with nx1 in *.
    rewrite <-H6 in *. 

    unfold vtyp_equiv in VT. rewrite VT in VT'. 

    assert (nx1 < Datatypes.S nx1). lia. 
    eapply VT' in H7.
    
    unfold vtyp_elem, vt_elem, vt_approx, vt_wrap1 in H7.
    destruct nx1. eapply valt_zero.

    remember (lt_dec (nx1) (Datatypes.S nx1)). destruct s. 2: lia.
    remember (lt_dec (Datatypes.S nx1) (Datatypes.S (Datatypes.S nx1))). destruct s. 2: lia.

    specialize (H7 0). 
    replace (Datatypes.S nx1 - 0) with (Datatypes.S nx1) in *. 2: lia.
    
    eapply valt_step. 
    3: { eapply stchain_aux_get. eapply storet_isstd. eapply storet_step'. split; eauto. lia. } 
    2:  {  eapply valt_useable. eauto. eauto.   }  eauto.
  - intros ? ?. 
    eapply QT1' in H6. eapply QT1 in H6. destruct H6. 
    rewrite plift_empty in H6. left. eapply vars_locs_monotonic; eauto. unfoldq; intuition.
    destruct (H0 x). auto. left. auto.
    right. destruct fr; try contradiction. simpl in *. destruct H7. split. 
    unfold st_locs, pnat in *. unfold stty_approx. rewrite map_length. lia.
    auto.
  - auto.   
Qed.


Lemma sem_app: forall G f t T1 T2 p frf qf frx qx fn1 fr1 q1 fn2 ar2 fr2 q2 e2fn e2ar e2fr e2,
    sem_type G f (TFun T1 fn1 fr1 q1 T2 fn2 ar2 fr2 q2 e2fn e2ar e2fr e2) p frf (plift qf) ->
    sem_type G t T1 p frx (plift qx) ->
    psub (plift e2) p ->   
    (e2fn = true -> psub (plift qf) p) -> 
    (e2ar = true -> psub (plift qx) p) -> 
    (if fn1 then
       if fr1 then
         True
       else
         (* fn1 /\ ~fr1: disabled tvar and tabs cases *)
         (* (frx = false /\ (exists x0, f = tvar x0 /\ psub (plift qx) (pone x0)) \/ *)
         (* (frx = false /\ (exists p0 t0, f = tabs p0 t0 /\ psub (plift qx) (plift p0))) \/ *)
         frx = false /\ psub (plift qx) (plift q1)
     else
       if fr1 then         
         psub (pand 
                 (plift (vars_trans_fix G
                           (qor
                              (qif (e2fn||fn2) qf)
                              (qor e2 q2)))) (* need q2, too? *)
                 (plift (vars_trans_fix G (qif (e2ar||ar2) qx)))) (* ar2 needed? *)
           (plift q1)
           (* TODO: also support qx < q1! *)
       else
         frx = false /\ psub (plift qx) (plift q1)) ->
    sem_type G (tapp f t) T2 p
      (fn2 && frf || ar2 && frx || fr2)
      (por (pif fn2 (plift qf)) (por (pif ar2 (plift qx)) (plift q2))).
Proof.
  intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? HF HX. 
  intros SUB1 SUB2 SUB3 HSEP n S M E V u WFE WFQ WFX ST. 
  assert (env_qual G V (por p (pif (e2fn||u&&fn2) (plift qf)))) as WFQ1. {
    eapply envq_tighten. eauto. unfoldq. destruct e2fn,u,fn2; intuition. }
  
  assert (env_qual G V (por p (pif (e2ar||u&&ar2) (plift qx)))) as WFQ2. {
    eapply envq_tighten. eapply WFQ. unfoldq. destruct e2ar,u,ar2; intuition. }  
  
  intros n3' S3' r3' EV.
  destruct n. inversion EV. simpl in EV. 

  (* function evaluates *)
  remember (teval n S E f) as tf. symmetry in Heqtf. destruct tf as [[nf S1] [rf|]]. 2: inversion EV.
  edestruct (HF (1+n) S M E) as (M1 & vf & lsf & SC1 & ST1 & RF & VF & HQF & HFt). eauto. eauto. 
  {
    replace (1+n) with (Datatypes.S n). 2: lia.
    eapply envx_tighten. eapply envx_step. 2: eauto. lia. unfoldq. destruct e2fn,u,fn2; intuition. 
  }

  eapply storet_step'. eauto. lia.

  eapply eval_deterministic. 2: eauto. eauto. lia. 
  eapply eval_bounded in Heqtf as BF; eauto.
  remember (1+n-nf) as nf1. destruct nf1. lia.
  subst rf.

  (* result is a function value *)
  simpl in VF. destruct vf; try contradiction.

  (* argument evaluates *)
  remember (teval (n-nf) S1 E t) as tx. symmetry in Heqtx. destruct tx as [[nx S2] [rx|]]. 2: inversion EV.
  edestruct (HX (1+n-nf) S1 M1 E) as (M2 & vx & lsx & SC2 & ST2 & RX & VX & HQX & HXt).
  eapply envt_step. eauto. lia. eapply WFQ2.
  {
    eapply envx_store_extend. eapply envx_tighten. eapply WFX.
    intros ? Q. destruct Q as [Q|Q]. left. eauto.
    destruct e2ar. left. simpl in Q. intuition. right. destruct u,ar2; simpl in Q; intuition.
    right. left. eauto. 
    replace (Datatypes.S n) with (1 +n). 2: lia.
    eapply st_extend_step''. eauto. lia.
  }
  eapply storet_step'. eauto. lia.

  eapply eval_deterministic. 2: eauto. eauto. lia.
  eapply eval_bounded in Heqtx as BX; eauto.
  remember (1+n-nx) as nx1. destruct nx1. lia.
  subst rx. 

  (* function body evaluates *)
  remember (teval (n-nf-nx) S2 (vx :: l) t0) as ty. symmetry in Heqty. destruct ty as [[ny S3] [ry|]]. 2: inversion EV.
  eapply eval_bounded in Heqty as BY; eauto.
  inversion EV. subst n3' S3' r3'. 

  (* from function LR: function body result is well-typed *)
  assert (nf1 = n-nf). lia. subst nf1.
  assert (Datatypes.S (n-nf) = 1+n-nf) as R1. lia.
  assert (n - nf - (nx - 1) = 1+n-nf-nx) as R2. lia.
  intuition. rename H12 into VF. 
  remember (e2ar (*|| u && ar2*)) as ux. 
  remember (e2fn (*|| u && fn2*)) as uf. 

  assert (telescope G) as TL. eapply envt_telescope. eauto.

  edestruct (VF S2 (nx-1) M2 vx lsx u (ux = true)) as (M3 & vy & lsy & SC3 & ST3 & RY & VY & HQY).
  - intros ?. eapply stchain_tighten.  
    replace (Datatypes.S (n - nf)) with (1 + n - nf). 
    replace (n - nf - (nx -1)) with (1 + n - nf - nx). eauto. eauto.
  - eapply storet_step'; eauto. lia.
  - intros. destruct uf; intuition.
  - intros. intuition.
  - eapply envq_tighten. eapply WFQ. 
    intros ? Q. destruct u,fn2,ar2; try contradiction; unfoldq; intuition eauto. 
  - eapply envx_store_change. eapply envx_tighten. eapply WFX.
    intros ? Q.
    destruct u,fn2,ar2; try contradiction; unfoldq; intuition eauto.
    eapply stchain_tighten.
    eapply st_extend_chain. eauto. eapply st_extend_step'. eapply st_extend_step''. eauto. lia. lia.
    eapply envx_wf; eauto.
    intros ? [? | ?]. left. auto.
    destruct u; try contradiction. right. right. right.  auto.
  - subst ux. 
    replace (n - nf - (nx - 1)) with (1 + n - nf - nx). eauto.
  -  (* SEPARATION / OVERLAP *)
  intros ? ?.

  destruct fn1. { (* arg may overlap with function? *)
    destruct fr1. { (* arg may be fresh? *)
      (* fn, fr: anything goes *)
      right. left. simpl. intros Q. contradiction. 
      (*remember (vars_locs_fix V (qor e2 (qif u q2))) as VF.
      assert (plift VF x \/ ~ plift VF x) as D. unfold plift. destruct (VF x); eauto.
      destruct D. right. left. *)
      
      (* assert (plift lvf x \/ ~ plift lvf x) as D. unfold plift. destruct (lvf x); eauto.
      destruct D. right. left. eauto. right. right. eauto. *)
    } {
      rename HSEP into SEP. 
      (* fn, not fr *)
      (*destruct HSEP as [SEP | SEP]. { (* fn *)
        destruct SEP as (? & ? & ? & A). subst f frx.
        destruct (HQX x) as [Hq | Hfr]. eauto. 2: { unfoldq. intuition. }
        right. left. eapply HPF. eapply vars_locs_monotonic. eapply A. 
        eapply vars_locs_monotonic. 2: eauto. unfoldq. intuition. 
      }*) { (* q1 *)
        destruct SEP as [? SEP]. subst frx.
        left.
        eapply valq_sub with (q':=(plift q1)) (fr':=false) in HQX.
        destruct (HQX x) as [Hq | Hfr]. eauto. 2: contradiction.
        eauto. eauto. destruct WFE as (LE & LV  & WFE).
        intros ? Q. eapply H7 in Q. unfoldq. intuition. 
      }
    }
  } {
    destruct fr1. {
      (* not fn, fr *)
      rename H11 into LVX.
      subst ux. remember (e2ar||u&&ar2) as ux. destruct ux.
      2: { right. right. intros C. contradiction. }
      subst uf. remember (e2fn||u&&fn2) as uf. (*destruct uf.
      2: { right. right. intros C. destruc
           destruct e2fn,fn2; intuition. }*)
      
      (* assert (plift lvf x \/ ~ plift lvf x) as D. unfold plift. destruct (lvf x); eauto. *)
      remember (qor (qif uf lsf) (vars_locs_fix V ((qor e2 (qif u q2))))) as VF'.
      assert (plift VF' x \/ ~ plift VF' x) as D. unfold plift. destruct (VF' x); eauto.

      (*edestruct val_locs_decide.*) destruct D as [D|D]. {
        subst VF'. rewrite plift_or, plift_if, plift_vars_locs, plift_or, plift_if in D. 
        
        assert (psub
           (pand (plift (vars_trans_fix G (qor (qif uf qf) ((qor e2 (qif u q2))))))
              (plift (vars_trans_fix G qx))) (plift q1)) as HSEP1. {
          intros ? [Q1 Q2].
          eapply HSEP.
          remember (e2ar || ar2) as ux'. assert (ux' = true) as R. { destruct e2ar,u,ar2; intuition. } rewrite R. 
          split. rewrite plift_vt, plift_or, plift_if, plift_or, plift_if in *.
          destruct u. simpl in Q1.
          destruct e2ar,ar2,e2fn,fn2; subst uf; simpl in *; eapply Q1.
          eapply vt_mono. 2: eapply Q1.
          unfoldq. destruct e2ar,ar2,e2fn,fn2; subst uf; simpl; intuition.
          eauto. eauto. eauto. eauto.
          eauto.
        } (* TODO: simplify *)

        rewrite plift_vt, plift_vt, plift_or, plift_if, plift_or, plift_if in HSEP1. 

        eapply HQX in LVX.
        
        destruct D as [H_vf | H_q2]. {
          destruct uf. 2: contradiction. eapply HQF in H_vf.
          destruct H_vf as [H_qf | H_fr]. {
            left.
            eapply vars_locs_monotonic. 
            eapply HSEP1.
            eapply WFQ.

            intros ? Q. destruct Q as [H_qf' | H_q2].
            unfoldq. destruct u,fn2,e2fn; intuition. 
            destruct H_q2. left. eauto. right. unfoldq. destruct u; intuition.

            intros ? Q. destruct e2ar. left. intuition. right.
            destruct u,ar2; inversion Hequx. 
            right. left. eauto. 
                        
            split.
            eapply vars_locs_monotonic. 2: eauto. unfoldq. intuition.
            destruct LVX as [H_qx|H_fr]. eauto.
            destruct frx. 2: contradiction. destruct H_fr as [? H_fr]. destruct H_fr.
            eapply SC1. 
            eapply envx_wf. eapply WFX. 2: eapply H_qf.

            unfoldq. destruct u,fn2,e2fn; intuition.
          } {
            (* frf *)
            destruct frf. 2: contradiction.
            destruct LVX as [H_qx|H_fr']. destruct H_fr as [? H_fr']. destruct H_fr'.
            eapply envx_wf. eapply WFX. 2: eapply H_qx.
            intros ? Q. destruct e2ar. left. intuition. right.
            destruct u,ar2; try inversion Hequx. right. left. eauto.
            destruct frx. 2: contradiction.
            destruct H_fr' as [? H_fr']. destruct H_fr'. eapply H_fr.
          }
        } {            
          left.        
          eapply vars_locs_monotonic. 
          eapply HSEP1. 
          eapply WFQ.
          
          intros ? Q. destruct Q as [H_qf | H_q2'].
          destruct uf. 2: contradiction. unfoldq. destruct u,fn2,e2fn; intuition.

          destruct H_q2' as [H_e2 | H_q2'].
          left. intuition. destruct u. 2: contradiction. right. right. right. eauto.

          intros ? Q. destruct e2ar. left. intuition. right.
          destruct u,ar2; try inversion Hequx. right. left. eauto. 
          
          split.
          eapply vars_locs_monotonic. 2: eauto. unfoldq. intuition. 
          
          destruct LVX as [H_qx|H_fr]. eauto.
          (* contra: fresh vs e2/q2 *)
          destruct frx. 2: contradiction. destruct H_fr as [? H_fr]. destruct H_fr.
          eapply SC1. 
          eapply envx_wf. eapply WFX. 2: eapply H_q2.
          
          intros ? Q. destruct Q as [H_e2 | H_q2'].
          left. eauto. destruct e2ar,u,ar2; simpl in Hequx; try inversion Hequx.
          unfoldq. intuition.
          unfoldq. intuition.
          unfoldq. intuition.
          unfoldq. intuition.
          unfoldq. intuition. 
        }
        eauto. eauto.
      } { 
        right. right. subst VF'. intros Q. eapply D.
        rewrite plift_or, plift_if, plift_vars_locs, plift_or, plift_if.
        destruct Q as [H_q2 | H_vf].
        right. eauto.
        left. eauto. 
      }
    } {
      (* not fn, not fr *)
      left. destruct HSEP as [? HSEP]. subst frx.
      eapply valq_sub with (q':=plift q1) (fr':=false) in HQX.
      destruct (HQX x) as [Hq | Hfr]. eauto. 2: contradiction.
      destruct Hq. exists x0. unfoldq. intuition.
      unfoldq. intuition. unfoldq. intuition.
      eapply H7 in H12. destruct WFE. lia. 
    }
  }
 
  - rewrite R2. eapply eval_deterministic. 2: eauto. eauto. lia.
  - subst ry.

  (* return result *)
  exists M3, vy,  lsy. split. 2: split. 3: split. 4: split. 5: split. 
  -- eapply st_extend_chain. eauto.
     eapply st_extend_chain. rewrite R1. eauto.
     eapply st_extend_chain. rewrite R2 in SC3. eapply SC3.
     eapply st_extend_refl'. lia. 
  -- eapply storet_step'. eauto. lia. 
  -- eauto. 
  -- eapply valt_step'. eauto. lia.
  -- remember (vabs l t0) as vf.
     intros ? ?. unfoldq.
     destruct (HQY  x) as [HY_q | [HY_f | [HY_x | HY_fr]]].
     repeat rewrite app_length. intuition.
     * (* q2 *)
       destruct HY_q.
       left. exists x0. intuition.
     * (* part of function *)
       destruct fn2. 2: contradiction.
       destruct (HQF x) as [HF_q | HF_fr]. eauto.
       ** (* q *) destruct HF_q.
          left. exists x0. intuition.
       ** (* fr *) 
          destruct frf. 2: contradiction.
          right. destruct HF_fr; simpl. 
          split. eapply SC3. eapply SC2. eauto. eauto. 
     * (* part of arg *)
       destruct ar2. 2: contradiction.
       destruct (HQX x) as [HX_q | HX_fr]. eauto.
       ** (* q *) destruct HX_q.
          left. exists x0. intuition.
       ** (* fr *)
          destruct frx. 2: contradiction.
          right. destruct HX_fr. 
          destruct (fn2 && frf); simpl. 
          split. eapply SC3. eauto. 
          intros ?. eapply H13. eapply SC1. eauto. 
          split. eapply SC3. eauto.
          intros ?. eapply H13. eapply SC1. eauto. 
     * (* fresh *)
       destruct fr2. 2: contradiction.
       right. destruct HY_fr.
       destruct (fn2 && frf || ar2 && frx); simpl.
       split. eauto. intros ?. eapply H13. eapply SC2. eapply SC1. eauto.
       split. eauto. intros ?. eapply H13. eapply SC2. eapply SC1. eauto.
  -- auto. 
Qed.

Lemma sem_abs: forall G t T1 T2 fn1 fr1 q1 fn2 ar2 fr2 q2 e2fn e2ar e2fr e2 qf q1',
    sem_type ((T1, fr1, q1')::G) t T2 
      (por (plift e2) (por (pif e2fn (plift qf)) (pif e2ar (pone (length G)))))
      fr2
      (por (plift q2) (por (pif fn2 (plift qf)) (pif ar2 (pone (length G)))))->

    q1' = (qor q1 (qif fn1 (qdom G))) ->
    
    (e2ar=true -> psub (plift q1) (plift e2)) ->  (* relax? need only if e2ar & q1fr *)
    (ar2=true -> psub (plift q1) (plift q2)) ->  (* relax? *)
    qf = qempty ->
      
    closed_ty (length G) T1 ->
    closed_ty (length G) T2 ->
    closed_ql (length G) q1 ->
    closed_ql (length G) q2 ->
    closed_ql (length G) e2 ->
    closed_ql (length G) qf ->
    sem_type G (tabs t) 
      (TFun T1 fn1 fr1 q1 T2 fn2 ar2 fr2 q2 e2fn e2ar e2fr e2)
      pempty false (plift qf).
Proof.
  intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? HY. intros. 
  intros n S M E V u WFE WFQ WFX ST. intros ? ? ? EV.
  destruct n. inversion EV. simpl in EV.

  inversion EV. subst n' S' r.
  
  exists M, (vabs E t), qempty. split. 2: split. 3: split. 4: split. 5: split. 
  - eapply st_extend_refl'. lia. 
  - eapply storet_step'. eauto. lia. 
  - eauto. 
  - simpl. remember (n-0) as n'. destruct n'.
    simpl. eauto.
    assert (length G = length E) as LE. { symmetry. eapply WFE. }
    assert (length G = length V) as LV. { symmetry. eapply WFE. }
    assert (pdom G = pdom E) as DE. { unfold pdom. rewrite LE. eauto. }
    assert (pdom G = pdom V) as DV. { unfold pdom. rewrite LV. eauto. }
    simpl. intuition. rewrite <- LE. auto. rewrite <- DE. auto.
    rewrite <- LE. auto. rewrite <- DE. auto. rewrite <- DE. auto.
    unfoldq; intuition.

    (* INDUCTION *)
    edestruct (HY (n' - nx) S' M' (vx::E) (((n' - nx), M',  (e2ar || uy && ar2 = true), lsx) :: V) uy) as (M2 & vy' & lsy & SC2 & ST2 & RY & VY & HQY & Hty). 
    + eapply envt_extend; eauto. eapply envt_step; eauto. lia.
      intros. subst fr1. intros ? Q. eapply H16 in Q.
      destruct Q as [ H_q1 | [H_fn | H_fr]]. {
        subst q1'. rewrite plift_or, plift_if.
        eapply vars_locs_monotonic. 2: eauto. unfoldq. intuition.        
      } {
        destruct fn1; contradiction. (*
        destruct fn1. 2: contradiction. 
        eapply vars_locs_monotonic. 2: eauto. unfoldq. intuition.
        subst qf. rewrite plift_empty in H19. contradiction. (* qf < e2 *) *)
      } {
        contradiction.
      }
      rewrite <- LE. auto.
      subst q1'. rewrite plift_closed, plift_or, plift_if, plift_dom.
      unfoldq. destruct fn1; intuition.
      eapply H5 in H18. lia. eapply H5 in H18. lia.
    + remember (e2ar || uy && ar2) as ux. 
      replace (por (por (plift e2) 
                      (por (pif e2fn (plift qf))
                           (pif e2ar (pone (length G)))))
                   (pif uy (por (plift q2)
                            (por (pif fn2 (plift qf))
                            (pif ar2 (pone (length G)))))))
      with (por (por (plift e2)
            (*(por*) (pif uy (plift q2)))
              (*(pif (e2fn||uy&&fn2) (plift qf))))*)
                (pif ux (pone (length E)))). 
      2:  {
        subst qf.
        eapply functional_extensionality. intros. 
        eapply propositional_extensionality. split; intros Q.
        - destruct Q as [[? | ?] | ?].
          left. left. auto.
          right. destruct uy; try contradiction. left. auto.
          destruct ux; try contradiction. simpl in H2. unfold pone in H2. subst x.
          destruct e2ar. left. right. right. unfoldq; intuition.
          destruct ar2. right. destruct uy; try contradiction. right. right. unfoldq; intuition.
          simpl in Hequx. intuition.
          destruct uy; simpl in *. intuition. intuition.
        - rewrite plift_empty in *. destruct Q as [Q | Q]. 
          -- destruct Q as [? | [? | ?]].
             left. left. auto.
             destruct e2fn; try contradiction.
             destruct e2ar; try contradiction. simpl in H2. unfold pone in H2. subst x.
             destruct ux; try contradiction. right. unfoldq; intuition.
             destruct uy; destruct ar2; intuition.
          -- destruct uy; try contradiction. destruct Q as [? | [? | ?]].
             left. right. auto. 
             destruct fn2; intuition.
             destruct ar2; try contradiction. simpl in H2. unfold pone in H2. subst x.
             destruct ux; try contradiction. right. unfoldq; intuition.
             destruct e2ar; intuition.
      }

      subst q1'. eapply envq_extend_full; eauto.
      ++ intros ? [? | ?]. eapply H7. auto. destruct uy; try contradiction. eapply H6 in H. auto.
      ++ intros. subst ux. destruct e2ar,uy,ar2; unfoldq; intuition.
      ++ unfoldq; intuition.
      ++ rewrite plift_dom. unfoldq. intuition. destruct uy; try contradiction. eapply H6 in H18. lia.
      ++ rewrite plift_dom. intros ? ?. auto.
      ++ intros. intros ? Q. eapply H16 in Q.
         destruct Q as [Q|Q]. left. eauto.
         destruct Q as [Q|Q]. right. left. eauto.
         destruct fr1. 2: contradiction. 
         right. right. intros Q1.
         eapply Q. rewrite H. left. eauto.
      ++ rewrite <- LE. auto.
    
    + remember (e2ar || uy && ar2) as ux. 
      replace (por (por (plift e2)
                    (por (pif e2fn (plift qf))
                        (pif e2ar (pone (length G)))))
                    (pif uy (por (plift q2)
                        (por (pif fn2 (plift qf))
                        (pif ar2 (pone (length G)))))))
      with (por (por (plift e2) (pif uy (plift q2))) (pif ux (pone (length E)))).
      2: { 
        subst qf.
        eapply functional_extensionality. intros. 
        eapply propositional_extensionality. split; intros Q.
        - destruct Q as [[? | ?] | ?].
          left. left. auto.
          right. destruct uy; try contradiction. left. auto.
          destruct ux; try contradiction. simpl in H2. unfold pone in H2. subst x.
          destruct e2ar. left. right. right. unfoldq; intuition.
          destruct ar2. right. destruct uy; try contradiction. right. right. unfoldq; intuition.
          simpl in Hequx. intuition.
          destruct uy; simpl in *. intuition. intuition.
        - rewrite plift_empty in *. destruct Q as [Q | Q]. 
          -- destruct Q as [? | [? | ?]].
             left. left. auto.
             destruct e2fn; try contradiction.
             destruct e2ar; try contradiction. simpl in H2. unfold pone in H2. subst x.
             destruct ux; try contradiction. right. unfoldq; intuition.
             destruct uy; destruct ar2; intuition.
          -- destruct uy; try contradiction. destruct Q as [? | [? | ?]].
             left. right. auto. 
             destruct fn2; intuition.
             destruct ar2; try contradiction. simpl in H2. unfold pone in H2. subst x.
             destruct ux; try contradiction. right. unfoldq; intuition.
             destruct e2ar; intuition.
       }
      
      eapply envx_extend_full'; eauto. 
      lia.
      intros ? [Q | Q]. left. auto. destruct uy; try contradiction. right. auto.
      intros ?. eapply valt_wf; eauto. 
      { eapply eval_bounded in H17; eauto. lia.  }
      rewrite <- LE. auto.

    + auto.
    + eauto.
    + exists M2, vy', lsy. split. 2: split. 3: split. 4: split.
      ++ auto.
      ++ auto.
      ++ auto.
      ++ eapply valt_extend1; eauto. lia. rewrite <- LE. auto. eapply envt_telescope; eauto.
      ++ intros ? ?.
         destruct (HQY x) as [HY_q | HY_fr]. eauto.
         * (* q *) destruct HY_q as (? & QL & VL).
           bdestruct (x0 =? length V).
           -- (* from arg *)
             subst x0. eapply var_locs_head in VL.
             right. right. left.
             destruct ar2. eauto.
             destruct QL as [H_q2 | [H_fn2 | H_ar2]].
             --- eapply H6 in H_q2. lia.
             --- destruct fn2. eapply H8 in H_fn2. lia. contradiction. 
             --- contradiction.
           -- (* from func *)
             assert (x0 < length ((nx, M',e2ar || uy && ar2 = true, lsx)::V)).
             destruct VL as (? & ? & ? & ? & IX & ?).
             rewrite indexr_extend1 in IX. eapply IX. simpl in *.
             eapply var_locs_shrink in VL; try lia.
             destruct QL as [H_q2 | [H_fn2 | H_ar2]].
             --- left. exists x0. intuition.
             --- destruct fn2. 2: contradiction.
                 subst qf. unfoldq; intuition.
             --- destruct ar2; inversion H_ar2; lia.

         * (* fr *)
           right. right. right. eapply HY_fr.
  - unfoldq. intuition.
  - auto.
Unshelve. eauto.
Qed.

Lemma sem_sub: forall G y T p fr1 q1 fr2 q2,
    sem_type G y T p fr1 q1 ->
    psub q1 q2 ->
    psub q2 (pdom G)  ->
    sem_type G y T p (fr1 || fr2)  q2.
Proof.
  intros. intros ? ? ? ? ? u WFE WFQ WFX ST.
  assert (env_qual G V (por p (pif u q1))) as WFQ1. {
    eapply envq_tighten. eauto. unfoldq. destruct u; intuition. }
  assert (env_accs n M V (por p (pif u q1))) as WFX1. {
    eapply envx_tighten. eauto. unfoldq. destruct u; intuition. }

  intros n1 S1 r1 EV.  
  edestruct (H n S M H2) as [M2 [vx [lvx [SC1 [ST1 [HR [HVX [HQX HPX]]]]]]]].
  eauto. eauto. eauto. eauto. eauto. 
  assert (psub q2 (pdom V)). {
    unfoldq. destruct WFE as (? & ? & ?). rewrite H4. intuition.  } 
  exists  M2, vx, lvx.
  split. 2: split. 3: split. 4: split. 5: split.
  - eauto.
  - eauto.
  - eauto.
  - eauto.
  - unfold val_qual in HQX; intuition.
    eapply valq_sub. eauto. unfoldq. intuition. unfoldq. intuition.
  - eauto.
Qed.

Lemma sem_sub_var: forall G y T p fr1 q1 Tx qx x,
    sem_type G y T p fr1 q1 ->
    q1 x ->
    p x -> (* b/c need q1 < p for induction *)
    indexr x G = Some (Tx, false, qx) ->
    (*psub (plift qx) p -> *) True ->
    sem_type G y T p fr1 (por (pdiff q1 (pone x)) (plift qx)).
Proof.
  intros. intros ? ? ? ? ? u WFE WFQ WFX ST.
  rename x into z. 
  assert (env_qual G V (por p (pif u q1))) as WFQ1. {
    eapply envq_tighten. eauto. unfoldq. destruct u; intuition.
    bdestruct (x =? z). subst. intuition. intuition. }
  assert (env_accs n M V (por p (pif u q1))) as WFX1. {
    eapply envx_tighten. eauto. unfoldq. destruct u; intuition.
    bdestruct (x =? z). subst. intuition. intuition. }

  intros n1 S1 r1 EV.  
  edestruct (H n S M H4) as [M2 [vx [lvx [SC1 [ST1 [HR [HVX [HQX HPX]]]]]]]].
  eauto. eauto. eauto. eauto. eauto.  
  exists M2. exists vx, lvx. intuition.
  eapply WFE in H2 as HZ.
  intros ? ?. destruct (HQX x). eauto.
  - destruct H6. bdestruct (x0 =? z).
    + subst. destruct HZ as [vz [M' [u' [lvz [? ?]]]]]. intuition.
      destruct H10 as (? & ? & ? & ? & ? & ?). rewrite H10 in H12.
      inversion H12. subst x1 x2 x3 x4. 
      left. eapply vars_locs_monotonic.
      2: { eapply H14; eauto. }
      unfoldq. intuition.
    + left. exists x0. intuition. unfoldq. intuition.
  - right. intuition. 
Qed.

(* ---------- semantic subtyping ---------- *)

(* prerequisite: when can we grow the set of locations of a function value?

   - no self ref: no problem
   - self ref in the result type: covariant, no problem
   - self ref in the argument type: contravariant, need to be careful:
     - if the argument type is fresh, we can grow it!

       A^f* -> B  <:  A^f -> B

*)
Lemma valt_locs_sub: forall n T1 T2 M G E V v u ls ls'
                  q1fn_a q1fr_a q1a 
                  q1fn_b q1fr_b q1b
                  q2fn_a q2ar_a q2fr_a q2a
                  e2fn_a e2ar_a e2fr_a e2a,
    val_type n M G E V v (TFun T1 q1fn_a q1fr_a q1a T2 q2fn_a q2ar_a q2fr_a q2a e2fn_a e2ar_a e2fr_a e2a) u ls ->
    psub (plift ls) (plift ls') ->
    psub (plift ls') (st_locs M) ->
    (* (q1fn_b = true ->
       q1fr_a = true /\ (q1fn_a = true \/ ls = qempty) \/
       psub (plift ls') (vars_locs V (plift q1a))) -> *)
    bsub q1fn_b q1fn_a ->
    bsub q1fr_b q1fr_a ->
    psub (vars_locs V (plift q1b)) (vars_locs V (plift q1a)) ->
    psub (plift q1b) (pdom E) ->
    val_type n M G E V v (TFun T1 q1fn_b q1fr_b q1b T2 q2fn_a q2ar_a q2fr_a q2a e2fn_a e2ar_a e2fr_a e2a) u ls'.
Proof.
  intros. destruct v; destruct n; simpl in *; intuition. 
  edestruct (H12 S' nx M' vx lsx uy u') as (M'' & vy & lsy & ? & ? & ? & ? & ?).
  + intuition. eapply stchain_tighten. eauto. eauto.
  + eauto.
  + eauto.
  + eauto.
  + eauto.
  + eauto.
  + eauto.
  + intros ? Q. eapply H19 in Q. destruct Q as [H_q1 | [H_fn | H_fr]].
    * left. eauto. 
    * destruct q1fn_b, q1fr_b. 2-4: contradiction. simpl in H_fn.
      rewrite H2, H3; eauto.
      right. left. eauto. 
      (* destruct H2 as [H_fr | H_q1]. eauto.
      -- right. destruct H_fr as [R1 R2].         
         assert (plift ls x \/ pnot (plift ls) x) as C. unfold pnot,plift. destruct (ls x); eauto. 
         destruct C.
         ++ destruct R2.
            ** subst. left. eauto.
            ** subst. rewrite plift_empty in *. contradiction. 
         ++ subst. right. eauto.
      -- left. eauto. *)
    * destruct q1fr_b. 2: contradiction.
      right. right. rewrite H3; eauto.
      intros ?. eapply H_fr.
      remember (e2ar_a || uy && q2ar_a) as ux. destruct ux. 2: contradiction.
      destruct H21 as [H_q | H_fn].
      -- left. eauto.
      -- right. unfoldq. destruct e2fn_a,uy,q2fn_a; simpl; intuition.

  + eauto.
  + exists M'', vy, lsy. split. 2: split. 3: split. 4: split. 
    auto. auto. auto. auto. 
    intros ? Q. eapply H25 in Q. destruct Q as [H_q2 | [H_vf | [H_vx | H_fr]]].
    * left. eapply H_q2. 
    * destruct q2fn_a. 2: contradiction.
      right. left. eapply H0. eauto.
    * right. right. left. eauto.
    * right. right. right. eauto.
Qed.

(* escape a function value: replace internal q2, e2 qualifiers with self refs *)
Lemma valt_escape: forall n T1 T2 M G E V v u ls
                  q1fn_a q1fr_a q1a 
                  q2fn_a q2ar_a q2fr_a q2a
                  e2fn_a e2ar_a e2fr_a e2a,
    val_type n M G E V v (TFun T1 q1fn_a q1fr_a q1a T2 q2fn_a q2ar_a q2fr_a q2a e2fn_a e2ar_a e2fr_a e2a) (u=true) ls ->

    env_qual G V (pif u (por (plift e2a) (pif true (plift q2a)))) ->
    env_accs n M V (pif u (por (plift e2a) (pif true (plift q2a)))) ->
    
    val_type n M G E V v (TFun T1 q1fn_a q1fr_a qempty T2 true (*q2fn_a*) q2ar_a q2fr_a qempty true (*e2fn_a*) e2ar_a e2fr_a qempty) (u=true) (qor (ls) (vars_locs_fix V (qor (e2a) (q2a)))).
Proof.
  intros. rename H0 into WFQ. rename H1 into WFX.
  destruct v; destruct n; simpl in *; intuition.
  rewrite plift_empty. unfoldq. intuition.
  rewrite plift_empty. unfoldq. intuition. 
  rewrite plift_empty. unfoldq. intuition.
  rewrite plift_or, plift_vars_locs, plift_or.
  { intros ? Q. destruct Q as [H_ls | H_q].
    - eauto.
    - eapply envx_wf. eapply WFX. 2: eauto. unfoldq. destruct u; intuition. (* u -> e2a, q2a < st_locs  *)
  }
  
  edestruct (H6 S' nx M' vx lsx uy (u=true)) as (M''' & vy & lsy & ? & ? & ? & ?).
  + intros. eapply stchain_tighten. eauto. rewrite plift_or. unfoldq. intuition. 
  + eauto.
  + eauto.
  + eauto. 
  + (* envq e2, q2 <-- no can do, only got envq qempty *)
    eapply envq_tighten. eapply WFQ. unfoldq. destruct uy,u; intuition.
  + (* envx: same *)
    eapply envx_store_change. eapply envx_tighten. eapply WFX.
    unfoldq. destruct uy,u; intuition.
    eapply stchain_tighten. eauto.
    rewrite plift_or, plift_vars_locs, plift_or.
    intros ? Q. right. eapply vars_locs_monotonic. 2: eauto.
    unfoldq. destruct uy; intuition. 
  + eauto.
  + intros ? Q. eapply H13 in Q. destruct Q as [H_q1 | [H_fn | H_fr]].
    * rewrite plift_empty in H_q1. destruct H_q1 as (? & ? & ?). contradiction.
    * right. left. eauto.
    * destruct q1fr_a. 2: contradiction.
      right. right. intros C. eapply H_fr.
      remember (e2ar_a || uy && q2ar_a) as ux.
      destruct ux. 2: contradiction. destruct C as [H_q | H_fn].
      -- right. rewrite plift_or, plift_vars_locs, plift_or. right.
         eapply vars_locs_monotonic. 2: eauto. unfoldq. destruct uy; intuition.
      -- right. rewrite plift_or. left. destruct e2fn_a,uy,q2fn_a; intuition.
  + eauto.
  + exists M''', vy, lsy. intuition.
    intros ? Q. eapply H20 in Q. destruct Q as [H_q2 | [H_vf | [H_vx | H_fr]]].
    * rewrite plift_or, plift_vars_locs, plift_or. 
      right. left. right.
      eapply vars_locs_monotonic. 2: eauto. unfoldq. intuition.
    * destruct q2fn_a. 2: contradiction.
      rewrite plift_or, plift_vars_locs, plift_or.
      right. left. left. eauto.
    * right. right. left. eauto.
    * right. right. right. eauto.
Qed.

Lemma sem_sub_escape: forall G T1 T2 t p q fr
                  q1fn_a q1fr_a q1a 
                  q2fn_a q2ar_a q2fr_a q2a
                  e2fn_a e2ar_a e2fr_a e2a,
    sem_type G t (TFun T1 q1fn_a q1fr_a q1a T2 q2fn_a q2ar_a q2fr_a q2a e2fn_a e2ar_a e2fr_a e2a) p fr q ->

    
    sem_type G t (TFun T1 q1fn_a q1fr_a qempty T2 true (*q2fn_a*) q2ar_a q2fr_a qempty true (*e2fn_a*) e2ar_a e2fr_a qempty) p fr (por q (por (plift e2a) (plift q2a))).
Proof.
  intros. intros ? ? ? ? ? ? WFE WFQ WFX ST.
  intros n1 S1 r1 EV.
  edestruct (H n S M H0 V u) as [M2 [vx [lvx [SC1 [ST1 [HR [HVX [HQX HPX]]]]]]]].
  - eauto.
  - eapply envq_tighten. eauto. unfoldq. destruct u; intuition. 
  - eapply envx_tighten. eauto. unfoldq. destruct u; intuition.
  - eauto.
  - eauto.
  - eapply valt_escape in HVX as HVX'. 
    exists M2, vx. eexists. intuition. eauto.
    intros ? Q. rewrite plift_or, plift_vars_locs, plift_or in Q.
    destruct Q as [H_ls | H_q].
    eapply HQX in H_ls. destruct H_ls as [H_q | H_fr].
    left. eapply vars_locs_monotonic. 2: eauto. unfoldq. intuition.
    right. eauto.
    left. eapply vars_locs_monotonic. 2: eauto. unfoldq. intuition.
    destruct t; intuition.
    rewrite plift_or, plift_vars_locs, plift_or. unfoldq. intuition.
    eapply envq_tighten. eauto. unfoldq. destruct u; intuition. 
    eapply envx_tighten. eapply envx_store_extend. eauto. eauto. unfoldq. destruct u; intuition. 
Qed.

                                                       
(* ---------- LR fundamental property  ---------- *)

Theorem fundamental_property : forall t G T fr q e,
    has_type G t T fr q e ->
    sem_type G t T (plift e) fr (plift q).
Proof.
  intros ? ? ? ? ?  ? W. 
  induction W.
  - rewrite plift_empty. eapply sem_true; eauto.
  - rewrite plift_empty. eapply sem_false; eauto.
  - rewrite plift_one. eapply sem_var; eauto.
  - rewrite plift_empty. eapply sem_ref; eauto. 
  - eapply sem_get; eauto.
  - eapply sem_ref2; eauto.
  - rewrite plift_or. eapply sem_ref_sub; eauto. 
  - eapply sem_get2; eauto.
  - rewrite plift_empty. eapply sem_put;eauto.
  - repeat rewrite plift_or in *. repeat rewrite plift_if in *.
    eapply sem_app; eauto. 
  - subst qf. 
    repeat rewrite plift_or in *.
    repeat rewrite plift_and in *.
    repeat rewrite plift_if in *.
    repeat rewrite plift_one in *.
    repeat rewrite plift_empty in *.
    rewrite <-plift_empty at 2.    
    eapply sem_abs. 
    rewrite plift_empty. all: eauto. 
  - eapply sem_sub; eauto.
  - rewrite plift_or, plift_diff, plift_one. 
    eapply sem_sub_var; eauto.
  - repeat rewrite plift_or in *. 
    eapply sem_sub_escape; eauto.
Qed.

Corollary safety : forall t T fr q e n,
  has_type [] t T fr q e -> 
  closed_ql 0 e -> closed_ql 0 q -> (* TODO: follows from has_type *)
  exp_type n [] [] [] [] [] t T True (plift e) fr (plift q) .
Proof. 
  intros. eapply fundamental_property in H; eauto.
  unfold exp_type.
  intros n1 S1 r1 EV.
    
  edestruct (H n [] [] [] [] true) as [M2 [vx [lvx [SC1 [ST1 [HR [HVX [HQX HPX]]]]]]]].
  eapply envt_empty.
  { intros ? ? ? ? ? [? ?]. destruct H4 as [? [? ?]]. destruct H6 as [? [? [? [? [? ?]]]]]. inversion H6.  }
  { intros ? ?. destruct H2. eapply H0 in H2. lia. eapply H1 in H2. lia.  }
  { eapply storet_empty; eauto.  }
  eauto.
  exists M2, vx, lvx. intuition. eapply valt_useable; eauto.
Qed.

End STLC.
