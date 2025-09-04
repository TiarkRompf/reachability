(*******************************************************************************
* Coq mechanization of the λ♦ᵣ-calculus [1] and its type checking algorithm.
* - Syntactic definitions
* - Semantic definitions
* - Metatheory
*******************************************************************************)

(* Full safety for STLC *)

(*
Simply-typed lambda calculus with reachability types, combined
proof of termination and type soundness (using logical relations).

THIS FILE:

- types and qualifiers
  - overlap (explicit transitive closure)
  - self refs (for functions and refs)
  - fresh flag
  - simple subtyping
  - no deep self/arg refs
  - no parametric polymorphism

- references
  - generic and nested refs
  - mutation with put/get
  - self refs in mutable refs (get path, to allow escaping)
  - no self for put (would enable recursion)
  - no fresh values in store (would require move/swap)

- effects
  - write effects
  - no kill/move effects


NEW IN THIS FILE

- shallow separation for nested ref cells (see below)
- self refs for nested ref cells (to support escaping)
- adding environment entries for self in t_abs and
  for arg in s_fun


NESTED REFS - SHALLOW MODEL

- nested refs (qpoly model, subject to internal qual)

- the transitive reachability through the store is approximated
  from above using the store typing -- a value in the store
  must be covered by the corersponding qualifier in the
  store typing (this is like in other files)

- the present file is in constrast to a TRef[T]^q model
  where all nesting was accounted on the outer q
  (i.e., the self-ref for TRef model).

- the present file starts from a TRef[T^q1] model, where
  all nesting is strictly accounted on the inner q1

- this leads to simplified internal invariants:
  instead of propagating (lls M ...) everywhere, we only
  need it for valt_store_change, via

      st_chain M M' (lls M (val_locs v)),

  in order to update the element interpretation from
  the store typing.

- we track write effects, and thus ensure that only the
  shallow locations are modified during evaluation

- we also support ref cells with an inner self
  reference TRef[T^self] -- the get operation on
  those again accounts the element to the
  outer qualifier

- this facility is cruicial for allowing ref cells
  to escape -- the self ref is supposed to be
  introduced through upcasing

- in summary we obtain a hybrid where we get

  1. precision when not using TRef self and only q1
     (e.g. for precise effect tracking)
  2. upcasting to TRef[T^self] when possible
     (for escaping)


OTHER TECHNICAL NOTES

- val_locs is removed and is now part of val_type,
  just like in the typechecking oopsla'24/popl'25
  submission artifact (..._stp file).

- questions remain if certain internal invariants
  are strictly necessery:
  - "p x -> ..." and "psub qx p -> ..." in env_type


*)


Require Import Coq.Lists.List.
Require Import Psatz.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Coq.Program.Wf.
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
* - Subtyping `stp`
* - Subqualifying `qstp`
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


Definition bsub b1 b2 := b1 = true -> b2 = true.


(* ---------- language syntax ---------- *)

Definition id := nat.

(* qualifiers:
   - expression type:   vars from env, may be fresh
   - function res type: from func, from arg, fresh
   - function arg type: overlap with function, may be fresh
*)

Definition ql2: Type := (ql * ql).
Definition qbvs (q: ql2) := fst q.
Definition qfvs (q: ql2) := snd q.

Inductive ty : Type :=
  | TUnit  : ty
  | TBool  : ty
  | TRef   : ty -> bool -> ql2 -> ty
  | TFun   : ty -> bool -> bool -> ql2 ->
             ty -> bool -> ql2 -> ty
.

(*
   TRef
        T       : element type
        qrf     : element self ref (result of get needs to alias ref)
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
  | tapp : tm -> tm -> tm (* f(x) *)
  | tabs : (*ql ->*) tm -> tm (* \f x.t *)
  | tas  : tm -> ty -> bool -> ql -> tm (* t: T *)
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
Definition closed_ql2 mb mf q := closed_ql mb (qbvs q) /\ closed_ql mf (qfvs q).

Inductive closed_ty: nat -> nat -> ty -> Prop :=
| c_unit: forall mb mf,
    closed_ty mb mf TUnit
| c_bool: forall mb mf,
    closed_ty mb mf TBool
| c_ref: forall mb mf T fr q,
    closed_ty mb mf T ->
    closed_ql2 mb mf q ->
    closed_ty mb mf (TRef T fr q)
| c_fun: forall mb mf T1 T2 fn1 fr1 q1 fr2 q2,
    closed_ty mb mf T1 ->
    closed_ty (mb+2) mf T2 ->
    closed_ql2 mb mf q1 ->
    closed_ql2 (mb+2) mf q2 ->
    closed_ty mb mf (TFun T1 fn1 fr1 q1 T2 fr2 q2)
.

Definition openq (bn: nat) (fn: ql) (q: ql2): ql2 :=
  (qdiff (qbvs q) (qone bn), qor (qfvs q) (qif (qbvs q bn) fn)).

Lemma openq_closed' mb mf q p
  (Q: closed_ql mf p):
  closed_ql2 (S mb) mf q <-> closed_ql2 mb mf (openq mb p q).
Proof.
  destruct q as [bq fq]. unfold closed_ql2, openq. simpl. intuition.
  - unfold closed_ql, qdiff, qone in *. intros ? H.
    rewrite andb_true_iff, negb_true_iff, Nat.eqb_neq in H.
    destruct H. specialize (H0 _ H). lia.
  - unfold closed_ql, qor, qif in *. intros ? H.
    rewrite orb_true_iff in H. destruct H. intuition.
    destruct (bq mb); intuition.
  - unfold closed_ql, qdiff in *. intros ? H.
    destruct (x =? mb) eqn:?. apply Nat.eqb_eq in Heqb. lia.
    eassert (E: _). 2: specialize (H0 x E).
    apply andb_true_iff. intuition. apply negb_true_iff. auto. lia.
  - unfold closed_ql, qor in *. intros ? H.
    eapply or_introl in H. rewrite <-orb_true_iff in H. specialize (H1 _ H). auto.
Qed.

Lemma openq_closed mb mf q p
  (H: closed_ql2 (S mb) mf q)
  (Q: closed_ql mf p):
  closed_ql2 mb mf (openq mb p q).
Proof.
  apply openq_closed'; auto.
Qed.

Fixpoint openq_rec (n bn fn: nat) (q: ql2): ql2 :=
  match n with
  | S n => openq bn (qone (n+fn)) (openq_rec n (S bn) fn q)
  | 0 => q
  end.

Fixpoint opent (bn: nat) (fn: ql) (T: ty): ty :=
  match T with
  | TRef T fr q =>
    TRef (opent bn fn T) fr (openq bn fn q)
  | TFun T1 fn1 fr1 q1 T2 fr2 q2 =>
    TFun (opent bn fn T1) fn1 fr1 (openq bn fn q1)
         (opent (bn+2) fn T2) fr2 (openq (bn+2) fn q2)
  | _ => T
  end.

Lemma opent_closed': forall T mb mf p
  (Q: closed_ql mf p),
  closed_ty (S mb) mf T <-> closed_ty mb mf (opent mb p T).
Proof.
  intros T. induction T; intros; subst.
  - simpl. split; intros. constructor. constructor.
  - simpl. split; intros. constructor. constructor.
  - simpl. split; intros.
    inversion H; subst. constructor. rewrite <-IHT; auto. rewrite <-openq_closed'; auto.
    inversion H; subst. constructor. rewrite IHT; eauto. rewrite openq_closed'; eauto.
  - simpl. split; intros.
    inversion H; subst. constructor.
    rewrite <-IHT1; auto. rewrite <-IHT2; auto.
    rewrite <-openq_closed'; auto. rewrite <-openq_closed'; auto.
    inversion H; subst. constructor.
    rewrite IHT1; eauto. rewrite Nat.add_succ_l, IHT2; eauto.
    rewrite openq_closed'; eauto. rewrite Nat.add_succ_l, openq_closed'; eauto.
Qed.

Lemma opent_closed mb mf T p
  (H: closed_ty (S mb) mf T)
  (Q: closed_ql mf p):
  closed_ty mb mf (opent mb p T).
Proof.
  apply opent_closed'; auto.
Qed.

Fixpoint opent_rec (n bn fn: nat) (t: ty): ty :=
  match n with
  | S n => opent bn (qone (n+fn)) (opent_rec n (S bn) fn t)
  | 0 => t
  end.

Lemma opent_rec_iff: forall n mb mf T,
  opent_rec n mb mf T = match T with
  | TRef T fr q =>
    TRef (opent_rec n mb mf T) fr (openq_rec n mb mf q)
  | TFun T1 fn1 fr1 q1 T2 fr2 q2 =>
    TFun (opent_rec n mb mf T1) fn1 fr1 (openq_rec n mb mf q1)
         (opent_rec n (mb+2) mf T2) fr2 (openq_rec n (mb+2) mf q2)
  | _ => T
  end.
Proof.
  intros n. induction n; intros.
  - simpl in *. destruct T; reflexivity.
  - simpl in *. rewrite IHn. destruct T; simpl; auto.
Qed.


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

Inductive occurrence_flag: Type :=
| contravariant_only
| covariant_only
| not_free.

Definition flip_occ f :=
  match f with
  | contravariant_only => covariant_only
  | covariant_only => contravariant_only
  | not_free => not_free
  end.

Fixpoint occurrences_fvs flag T x: Prop :=
  match T with
  | TRef T fr q =>
    occurrences_fvs not_free T x /\
    ~ plift (qfvs q) x
  | TFun T1 _ _ q1 T2 _ q2 =>
    occurrences_fvs (flip_occ flag) T1 x /\
    (plift (qfvs q1) x -> flag = contravariant_only) /\
    occurrences_fvs flag T2 x /\
    (plift (qfvs q2) x -> flag = covariant_only)
  | _ => True
  end.

Fixpoint occurrences_bvs flag T x: Prop :=
  match T with
  | TRef T fr q =>
    occurrences_bvs not_free T x /\
    ~ plift (qbvs q) x
  | TFun T1 _ _ q1 T2 _ q2 =>
    occurrences_bvs (flip_occ flag) T1 x /\
    (plift (qbvs q1) x -> flag = contravariant_only) /\
    occurrences_bvs flag T2 (x+2) /\
    (plift (qbvs q2) (x+2) -> flag = covariant_only)
  | _ => True
  end.


(*******************************************************************************
* Semantic Definitions
* - Bigstep Interpreter `teval`
* - Value Interpretation `val_type`
* - Semantic Typing `sem_type`
* - Semantic Subtyping `sem_stp2`
* - Semantic Subqualifying `sem_qtp2`
* - and various semantic typing rules...
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
                  match teval (n-df-dx) M'' (vx::(vabs env2 ey)::env2) ey with
                    | (dy, M''', ry) => (1+df+dx+dy, M''', ry)
                  end
              end
          end
        | tas t T fr q =>
          let '(d, M', v) := teval n M env t in
          (1+d, M', v)
      end
  end.

(* value interpretation of terms *)
Definition tevaln M env e M' v :=
  exists nm,
  forall n,
    n > nm ->
    teval n M env e = (nm, M', Some (Some v)).



(* ---------- logical relation ---------- *)

Definition lenv: Type := list ql.

Definition var_locs (E: lenv) x l := exists vx, indexr x E = Some vx /\ plift vx l.

Definition vars_locs (E: lenv) q l := exists x, q x /\ var_locs E x l.

Fixpoint vars_locs_fix (H: lenv) (q: ql) (l: nat): bool :=
  match H with
  | v :: H => (q (length H) && v l) || vars_locs_fix H q l
  | [] => false
  end.


(* store typings / "worlds" *)

(* consists of:

    - store type for S1
    - store type for S2
    - binary relation between locations that
      are supposed to be equivalent

   we enforce that this relation is a partial bijection
*)

Definition stty: Type := list ((vl -> ql -> Prop) * ql).


Definition st_types (M: stty) := M.
Definition st_locs (M: stty) := pdom M.


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



Definition store_type (S: stor) (M: stty) :=
  length M = length S /\
    (forall l,
      st_locs M l ->
      exists vt qt v ls,
        indexr l M = Some (vt, qt) /\
          indexr l S = Some v /\
          vt v ls /\
          psub (plift ls) (plift qt) /\
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


Definition st_chain_deep (M: stty) (M1: stty) q := st_chain M M1 (locs_locs_stty M q).

Definition st_chain_full (M: stty) (M1: stty) := st_chain M M1 (st_locs M).




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

Fixpoint ty_size (t: ty) :=
  match t with
  | TRef T fr q =>
    1 + ty_size T
  | TFun T1 fn1 fr1 q1 T2 fr2 q2 =>
    1 + ty_size T1 + ty_size T2
  | _ => 0
  end.

Lemma opent_preserves_ty_size: forall bn fn t,
  ty_size (opent bn fn t) = ty_size t.
Proof.
  intros. generalize dependent bn. induction t; intros.
  - simpl. auto.
  - simpl. auto.
  - simpl. rewrite IHt. auto.
  - simpl. rewrite IHt1, IHt2. auto.
Qed.


(* value interpretation of types *)

Program Fixpoint val_type' (M:stty) (H:venv) (V:lenv) v T (ls:ql) {measure (ty_size T)}: Prop :=
  match v, T with
  | v, TUnit =>
      (psub (plift ls) (st_locs M))
  | vbool b, TBool =>
      (psub (plift ls) (st_locs M))
  | vref l, TRef T fr q =>
      closed_ty 0 (length H) T /\
      plift ls l /\
      closed_ql2 0 (length H) q /\
      psub (plift ls) (st_locs M) /\
      exists vt qt,
        indexr l M = Some (vt, qt) /\
        (psub (plift qt) (por (vars_locs V (plift (qfvs q))) (pif fr (plift ls)))) /\
        (psub (vars_locs V (plift (qfvs q))) (plift qt)) /\
        (forall v lsv,
            psub (plift lsv) (plift qt) ->
            (vt v lsv <-> val_type' M H V v T lsv))
  | vabs G ty, TFun T1 fn1 fr1 q1 T2 fr2 q2 =>
        closed_ty 0 (length H) T1 /\
        closed_ql2 0 (length H) q1 /\
        closed_ty 2 (length H) T2 /\
        closed_ql2 2 (length H) q2 /\
        (psub (plift ls) (st_locs M)) /\
        bsub fn1 fr1 /\
        occurrences_bvs covariant_only T2 1 /\
        (forall S' M' vx lsx,
            st_chain_deep M M' (plift ls)
            ->
              store_type S' M'
            ->
            val_type'
              M'
              H
              V
              vx
              T1
              lsx
            ->
              psub (plift lsx)
                (por (pif fn1 (plift ls))
                   (por (pif fr1 (pnot (plift ls)))
                      (vars_locs V (plift (qfvs q1)))))
            ->
              exists S'' M'' vy lsy,
                tevaln
                  S'
                  (vx::v::G)
                  ty
                  S''
                  vy
                /\
                  st_chain_full M' M''
                /\
                  store_type S'' M''
                /\
                  store_effect S' S'' (por (plift ls) (plift lsx))
                /\
                  val_type'
                    M''
                    (vx::v::H)
                    (lsx::ls::V)
                    vy
                    (opent_rec 2 0 (length H) T2)
                    lsy
                /\
                  psub (plift lsy)
                    (por (vars_locs V (plift (qfvs q2)))
                       (por (pif (qbvs q2 1) (plift ls))
                          (por (pif (qbvs q2 0) (plift lsx))
                             (pif fr2 (pnot (pdom M')))))))
  | _,_ =>
      False
  end.
Next Obligation. simpl. lia. Qed.
Next Obligation.
  simpl. repeat rewrite opent_preserves_ty_size. lia.
Qed.
Next Obligation. intuition; discriminate. Qed.
Next Obligation. intuition; discriminate. Qed.
Next Obligation. intuition; discriminate. Qed.
Next Obligation. intuition; discriminate. Qed.
Next Obligation. intuition; discriminate. Qed.
Next Obligation. intuition; discriminate. Qed.

Lemma val_type'_def: forall M H V v T ls,
  val_type' M H V v T ls =
  match v, T with
  | v, TUnit =>
      (psub (plift ls) (st_locs M))
  | vbool b, TBool =>
      (psub (plift ls) (st_locs M))
  | vref l, TRef T fr q =>
      closed_ty 0 (length H) T /\
      plift ls l /\
      closed_ql2 0 (length H) q /\
      psub (plift ls) (st_locs M) /\
      exists vt qt,
        indexr l M = Some (vt, qt) /\
        (psub (plift qt) (por (vars_locs V (plift (qfvs q))) (pif fr (plift ls)))) /\
        (psub (vars_locs V (plift (qfvs q))) (plift qt)) /\
        (forall v lsv,
            psub (plift lsv) (plift qt) ->
            (vt v lsv <-> val_type' M H V v T lsv))
  | vabs G ty, TFun T1 fn1 fr1 q1 T2 fr2 q2 =>
        closed_ty 0 (length H) T1 /\
        closed_ql2 0 (length H) q1 /\
        closed_ty 2 (length H) T2 /\
        closed_ql2 2 (length H) q2 /\
        (psub (plift ls) (st_locs M)) /\
        (* (psub (vars_locs V (plift q1)) (plift ls)) /\   *)
        bsub fn1 fr1 /\
        occurrences_bvs covariant_only T2 1 /\
        (forall S' M' vx lsx,
            st_chain_deep M M' (plift ls)
            ->
              store_type S' M'
            ->
            val_type'
              M'
              H
              V
              vx
              T1
              lsx
            ->
              psub (plift lsx)
                (por (pif fn1 (plift ls))
                  (por (pif fr1 (pnot (plift ls)))
                      (vars_locs V (plift (qfvs q1)))))
            ->
              exists S'' M'' vy lsy,
                tevaln
                  S'
                  (vx::v::G)
                  ty
                  S''
                  vy
                /\
                  st_chain_full M' M''
                /\
                  store_type S'' M''
                /\
                  store_effect S' S'' (por (plift ls) (plift lsx))
                /\
                  val_type'
                    M''
                    (vx::v::H)
                    (lsx::ls::V)
                    vy
                    (opent_rec 2 0 (length H) T2)
                    lsy
                /\
                  psub (plift lsy)
                    (por (vars_locs V (plift (qfvs q2)))
                      (por (pif (qbvs q2 1) (plift ls))
                          (por (pif (qbvs q2 0) (plift lsx))
                            (pif fr2 (pnot (pdom M')))))))
  | _,_ =>
      False
  end.
Proof.
  intros. unfold val_type' at 1, val_type'_func.
  destruct v; destruct T; try reflexivity.
  - rewrite WfExtensionality.fix_sub_eq_ext; simpl. reflexivity.
  - rewrite WfExtensionality.fix_sub_eq_ext; simpl. reflexivity.
Qed.

Inductive val_type (M:stty) (H:venv) (V:lenv) v T (ls:ql): Prop :=
| v0: val_type' M H V v T ls -> val_type M H V v T ls.

Lemma val_type'_iff: forall M H V v T ls,
  val_type' M H V v T ls = val_type M H V v T ls.
Proof.
  intros. apply propositional_extensionality. split; intros.
  constructor; auto. inversion H0; auto.
Qed.

Lemma val_type_def: forall T M H V v ls,
  val_type M H V v T ls =
  match v, T with
  | v, TUnit =>
      (psub (plift ls) (st_locs M))
  | vbool b, TBool =>
      (psub (plift ls) (st_locs M))
  | vref l, TRef T fr q =>
      closed_ty 0 (length H) T /\
      plift ls l /\
      closed_ql2 0 (length H) q /\
      psub (plift ls) (st_locs M) /\
      exists vt qt,
        indexr l M = Some (vt, qt) /\
        (psub (plift qt) (por (vars_locs V (plift (qfvs q))) (pif fr (plift ls)))) /\
        (psub (vars_locs V (plift (qfvs q))) (plift qt)) /\
        (forall v lsv,
            psub (plift lsv) (plift qt) ->
            (vt v lsv <-> val_type M H V v T lsv))
  | vabs G ty, TFun T1 fn1 fr1 q1 T2 fr2 q2 =>
        closed_ty 0 (length H) T1 /\
        closed_ql2 0 (length H) q1 /\
        closed_ty 2 (length H) T2 /\
        closed_ql2 2 (length H) q2 /\
        (psub (plift ls) (st_locs M)) /\
        bsub fn1 fr1 /\
        occurrences_bvs covariant_only T2 1 /\
        (forall S' M' vx lsx,
            st_chain_deep M M' (plift ls)
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
                (por (pif fn1 (plift ls))
                  (por (pif fr1 (pnot (plift ls)))
                      (vars_locs V (plift (qfvs q1)))))
            ->
              exists S'' M'' vy lsy,
                tevaln
                  S'
                  (vx::v::G)
                  ty
                  S''
                  vy
                /\
                  st_chain_full M' M''
                /\
                  store_type S'' M''
                /\
                  store_effect S' S'' (por (plift ls) (plift lsx))
                /\
                  val_type
                    M''
                    (vx::v::H)
                    (lsx::ls::V)
                    vy
                    (opent_rec 2 0 (length H) T2)
                    lsy
                /\
                  psub (plift lsy)
                    (por (vars_locs V (plift (qfvs q2)))
                      (por (pif (qbvs q2 1) (plift ls))
                          (por (pif (qbvs q2 0) (plift lsx))
                            (pif fr2 (pnot (pdom M')))))))
  | _,_ =>
      False
  end.
Proof.
  intros. rewrite <-val_type'_iff.
  destruct T; destruct v; auto; rewrite val_type'_def;
  apply propositional_extensionality; intuition.
  + destruct H5 as (vt & qt & ?). exists vt, qt. intuition.
    rewrite <-val_type'_iff. apply H8; auto.
    rewrite <-val_type'_iff in H9. apply H8; auto.
  + destruct H5 as (vt & qt & ?). exists vt, qt. intuition.
    rewrite val_type'_iff. apply H8; auto.
    rewrite val_type'_iff in H9. apply H8; auto.
  + rewrite <-val_type'_iff in H10.
    destruct (H8 _ _ _ _ H7 H9 H10 H11) as (S'' & M'' & vy & lsy & ?).
    exists S'', M'', vy, lsy. intuition.
    rewrite <-val_type'_iff. auto.
  + rewrite val_type'_iff in H10.
    destruct (H8 _ _ _ _ H7 H9 H10 H11) as (S'' & M'' & vy & lsy & ?).
    exists S'', M'', vy, lsy. intuition.
    rewrite val_type'_iff. auto.
Qed.

Definition val_qual (M M1: stty) H ls p fr (q: pl) :=
  psub (plift ls)
    (por (vars_locs H (pand p q)) (* locs(v) & M & ~(p&q) = O *)
       (pif fr (pnot (pdom M)))).

Definition exp_qual V t ls :=
  match t with
  | tvar x => psub (vars_locs V (pone x)) (plift ls)
  | _ => True
  end.


Definition exp_type S M H V t T p fr q :=
  exists S' M' v ls,
    tevaln S H t S' v /\
    st_chain_full M M' /\
    store_type S' M' /\
    store_effect S S' (vars_locs V p) /\  (* p and e *)
    val_type M' H V v T ls /\
    val_qual M M' V ls p fr q /\
    exp_qual V t ls
.



Definition env_type M H G V p :=
  length H = length G /\
  length V = length G /\
    psub p (pdom H) /\
    (forall x T fr (q:ql),
        indexr x G = Some (T, fr, q) ->
        exists (v : vl) ls,
          closed_ty 0 x T /\
          closed_ql x q /\
          indexr x H = Some v /\
          indexr x V = Some ls /\
          (p x -> val_type M H V v T ls) /\
          (fr = false -> (* psub (plift q) p *) True -> psub (plift ls) (vars_locs V (plift q)))) /\
    (forall q q',
        psub q p ->
        psub q' p ->
        psub (pand (vars_trans G q) (vars_trans G q')) p ->
        psub (pand (vars_locs V q) (vars_locs V q'))
          (vars_locs V (pand (vars_trans G q) (vars_trans G q')))).


Definition sem_type G t T p fr q :=
  forall S M E V,
    env_type M E G V p ->
    store_type S M  ->
    exp_type S M E V t T p fr q.

Definition sem_sqtp G p T1 fr1 q1 T2 fr2 q2 :=
  forall t,
    sem_type G t T1 p fr1 q1 ->
    sem_type G t T2 p fr2 q2.


#[export] Hint Constructors ty: core.
#[export] Hint Constructors tm: core.
#[export] Hint Constructors vl: cor.


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

Lemma por_false: forall q1 q2,
    (por (pif false q1) q2) = q2.
Proof.
  intros. eapply functional_extensionality.
  intros. eapply propositional_extensionality.
  unfoldq. intuition.
Qed.

Lemma por_comm: forall q1 q2,
    (por q1 q2) = (por q2 q1).
Proof.
  intros. eapply functional_extensionality.
  intros. eapply propositional_extensionality.
  unfoldq. intuition.
Qed.


(*----------- val_locs lemmas   -----------*)

Lemma val_locs_decide: forall (v:ql) l,
    plift v l \/ ~ plift v l.
Proof.
  intros. unfold plift. remember (v l).
  destruct b; intuition.
Qed.


Lemma var_locs_decide: forall H x l,
    var_locs H x l \/ ~ var_locs H x l.
Proof.
  intros. unfold var_locs, plift.
  bdestruct (x <? length H).
  - assert (exists vx, indexr x H = Some vx).
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
  unfold vars_locs, var_locs, plift in *.
  intuition.
  - simpl. destruct H0 as [? [? ?]]. destruct H1 as [? [? ?]].
    unfold indexr in H1. induction H.
    congruence.
    bdestruct (x0 =? length H).
    inversion H1. subst. simpl. rewrite H0.
    unfold plift in H2. rewrite H2. simpl. eauto.
    simpl. rewrite IHlist.
    destruct (q (length H) && a x); simpl; eauto.
    eauto.
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
Qed.


Lemma vars_locs_fix_empty: forall E,
  vars_locs_fix E qempty = qempty.
Proof.
  intros. induction E; simpl. intuition.
  rewrite IHE. intuition.
Qed.


(* ---------- closedness, vars_locs lemmas  ---------- *)

Lemma closedq_extend : forall {m q}, closed_ql m q ->
  forall {m'}, m <= m' -> closed_ql m' q.
Proof.
    intros. unfold closed_ql in *. intros.
    specialize (H x). intuition.
Qed.

Lemma closedq2_extend : forall {m1 m2 q}, closed_ql2 m1 m2 q ->
  forall {m'1 m'2}, m1 <= m'1 -> m2 <= m'2 -> closed_ql2 m'1 m'2 q.
Proof.
    intros. unfold closed_ql2 in *. intuition.
    eapply closedq_extend; eauto.
    eapply closedq_extend; eauto.
Qed.

Lemma closedty_extend : forall {m1 m2 T}, closed_ty m1 m2 T ->
  forall {m'1 m'2}, m1 <= m'1 -> m2 <= m'2 -> closed_ty m'1 m'2 T.
Proof.
    intros. generalize dependent m'1. generalize dependent m'2.
    induction H; intros.
    - constructor.
    - constructor.
    - constructor. intuition. eapply closedq2_extend; eauto.
    - constructor. intuition. intuition.
      eapply closedq2_extend; eauto.
      eapply closedq2_extend; eauto. lia.
Qed.

Lemma  closedq_and: forall q1 q2 m,
  (closed_ql m q1 \/ closed_ql m q2) ->
  closed_ql m (qand q1 q2).
Proof.
  intros. destruct H; unfold closed_ql in *; intros;
  bdestruct (qand q1 q2 x); intuition.
Qed.

Lemma closedq_empty: forall m,
  closed_ql m qempty.
Proof.
  intros. unfold closed_ql. intros.
  unfoldq; intuition.
Qed.
#[global] Hint Resolve closedq_empty : core.

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

Lemma vars_locs_or: forall H q1 q2,
  vars_locs H (por q1 q2) = por (vars_locs H q1) (vars_locs H q2).
Proof.
  intros. apply functional_extensionality. intros x.
  apply propositional_extensionality. split; intros.
  - destruct H0 as (x0 & [H1 | H1] & H2).
    left. eexists. eauto. right. eexists. eauto.
  - destruct H0 as [(x0 & H1 & H2) | (x0 & H1 & H2)].
    eexists. split; eauto. left. auto. eexists. split; eauto. right. auto.
Qed.

Lemma vars_locs_if: forall H b q,
  vars_locs H (pif b q) = pif b (vars_locs H q).
Proof.
  intros. apply functional_extensionality. intros x.
  apply propositional_extensionality. split; intros.
  - destruct H0 as (x0 & H1 & H2). destruct b; auto; simpl in *. eexists. eauto.
  - destruct b; simpl in *; intuition.
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

Lemma vars_locs_head: forall v H,
  vars_locs (v :: H) (pone (length H)) = plift v.
Proof.
  intros. apply functional_extensionality. intros x.
  apply propositional_extensionality. split; intros.
  - destruct H0 as (x0 & H1 & H2). inversion H1. subst x0. eapply var_locs_head. eauto.
  - eexists. split. reflexivity. eexists. split. apply indexr_head. auto.
Qed.

Lemma vars_locs_tighten: forall v H q,
  psub q (pdom H) -> vars_locs (v :: H) q = vars_locs H q.
Proof.
  intros. apply functional_extensionality. intros x.
  apply propositional_extensionality. split; intros.
  - destruct H1 as (x0 & H1 & H2). eexists. split. eauto.
    destruct H2 as (x1 & H2 & H3). rewrite indexr_skip in H2. eexists. eauto.
    apply H0 in H1. unfold pdom in H1. lia.
  - apply vars_locs_extend1. auto.
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

Lemma vars_locs_change_skip: forall q V V' v v',
  ~ q (length V) ->
  vars_locs (V' ++ v :: V) q = vars_locs (V' ++ v' :: V) q.
Proof.
  intros. apply functional_extensionality; intros.
  apply propositional_extensionality; intros; split; intros.
  - destruct H0 as (x0 & ?). exists x0. intuition.
    destruct H2 as (x1 & ?). exists x1. intuition.
    assert (x0 <> length V). intro. apply H. subst x0. auto.
    destruct (x0 <? length V) eqn:?.
    * apply Nat.ltb_lt in Heqb. rewrite <-indexr_insert_lt; auto.
      rewrite <-indexr_insert_lt in H2; auto.
    * apply Nat.ltb_nlt in Heqb. destruct x0. lia.
      rewrite <-indexr_insert_ge; try lia.
      rewrite <-indexr_insert_ge in H2; try lia. auto.
  - destruct H0 as (x0 & ?). exists x0. intuition.
    destruct H2 as (x1 & ?). exists x1. intuition.
    assert (x0 <> length V). intro. apply H. subst x0. auto.
    destruct (x0 <? length V) eqn:?.
    * apply Nat.ltb_lt in Heqb. rewrite <-indexr_insert_lt; auto.
      rewrite <-indexr_insert_lt in H2; auto.
    * apply Nat.ltb_nlt in Heqb. destruct x0. lia.
      rewrite <-indexr_insert_ge; try lia.
      rewrite <-indexr_insert_ge in H2; try lia. auto.
Qed.

Lemma vars_locs_change_congr: forall q V V' v v',
  psub (plift v) (plift v') ->
  psub (vars_locs (V' ++ v :: V) q) (vars_locs (V' ++ v' :: V) q).
Proof.
  intros. intros ? ?. destruct H0 as (x0 & ?). exists x0. intuition.
  destruct H2 as (x1 & ?). bdestruct (x0 =? length V).
  - subst x0. exists v'. rewrite indexr_insert. rewrite indexr_insert in H0.
    intuition. inversion H2; subst. apply H. auto.
  - exists x1. intuition. bdestruct (x0 <? length V).
    rewrite <-indexr_insert_lt in H3; auto. rewrite <-indexr_insert_lt; auto.
    destruct x0. lia. rewrite <-indexr_insert_ge; try lia.
    rewrite <-indexr_insert_ge in H3; try lia. auto.
Qed.


(*----------- saturation / trans closure lemmas   -----------*)

Definition telescope (env: tenv) := forall x T fr1 q1,
    indexr x env = Some (T, fr1, q1) -> closed_ql x q1 /\ closed_ty 0 x T.

Lemma telescope_shrink: forall env T fr q,
    telescope ((T,fr,q)::env) -> telescope env.
Proof.
  intros G. intros.
  unfold telescope in *. intros.
  eapply H. eapply indexr_extend1 in H0. eapply H0.
Qed.

Lemma telescope_extend: forall env T fr q,
    closed_ql (length env) q ->
    closed_ty 0 (length env) T ->
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
    + eapply IHG; eauto. lia.
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
  2: rewrite <-plift_vt. 2: eapply H4. eapply H5 in H3.
  eapply H0 in H1. lia. eauto.
Qed.


Lemma vt_head: forall G T1 fr1 q1 (q: pl),
    telescope G ->
    psub (plift q1) (pdom G) ->
    q (length G) ->
    closed_ty 0 (length G) T1 ->
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

Lemma stchain_empty: forall M1 M2,
  st_chain M1 M2 pempty.
Proof.
  intros. unfold st_chain. unfoldq. intuition.
Qed.

Lemma stchain_symm: forall M1 M2 q1,
  st_chain M1 M2 q1 ->
  st_chain M2 M1 q1.
Proof.
  intros. destruct H. destruct H0.
  symmetry in H1. split. eauto. split. eauto. eauto.
Qed.


Lemma st_mono: forall M M',
  st_chain M M' (st_locs M) ->
  length M <= length M'.
Proof.
  intros. destruct H as [? [? ?]].
  unfoldq; intuition. unfold st_locs, pdom in *.
  destruct (length M). lia. eapply H0. lia.
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
    destruct (H4 x1) as (vt' & frt' & qt' & v & ls & ?); eauto.
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
    exists vx, indexr x E = Some vx /\ locs_locs_stty M (plift vx) l.
Proof.
  intros. remember (var_locs E x) as Q.
  generalize dependent E.
  generalize dependent x.
  induction H; intros; subst.
  - destruct H. exists x1. intuition eauto using lls_z.
  - destruct H. exists x2. intuition eauto using lls_s.
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


Lemma stchaindf_tighten: forall S M M' q,
    store_type S M ->
    st_chain_full M M' ->
    psub q (st_locs M) ->
    st_chain_deep M M' q.
Proof.
  intros. destruct H0 as (? & ? & ?).
  assert (psub (locs_locs_stty M q) (st_locs M)). {
    eapply lls_closed'. eauto. eauto. }
  split. 2: split.
  eauto. unfoldq. intuition. intros. eauto.
Qed.

Lemma stchaindf_tighten': forall S M M' q,
    store_type S M ->
    st_chain_full M M' ->
    psub q (st_locs M) ->
    st_chain_deep M' M q.
Proof.
  intros.
  assert (st_chain_deep M M' q). {
    eapply stchaindf_tighten; eauto. }
  remember H2 as H3. clear HeqH3. destruct H2 as (? & ? & ?).
  rewrite lls_change with (M':=M') in H2. 2: eauto.
  rewrite lls_change with (M':=M') in H4. 2: eauto.
  rewrite lls_change with (M':=M') in H5. 2: eauto.
  split. 2: split. eauto. eauto. symmetry. eauto.
Qed.

Lemma stchaind_tighten: forall M1 M2 q1 q2,
  st_chain_deep M1 M2 q2 ->
  psub q1 q2 ->
  st_chain_deep M1 M2 q1.
Proof.
  intros.
  eapply stchain_tighten. eauto. eapply lls_mono. eauto.
Qed.

Lemma stchaind_symm: forall M1 M2 q1,
  st_chain_deep M1 M2 q1 ->
  st_chain_deep M2 M1 q1.
Proof.
  intros.
  eapply stchain_symm in H as SC.
  rewrite lls_change with (M':=M2) in SC. eauto. eauto.
Qed.

Lemma stchaind_chain': forall M1 M2 M3 q1 q2,
  st_chain_deep M1 M2 q1 ->
  st_chain_deep M2 M3 q2 ->
  psub q2 q1 ->
  st_chain_deep M1 M3 q2.
Proof.
  intros. unfold st_chain_deep in *.
  assert (st_chain M2 M3 (locs_locs_stty M1 q2)). {
    eapply stchain_tighten. eauto.
    erewrite lls_change. intros ? ?. eauto.
    eapply stchain_tighten. eauto.
    eapply lls_mono. eauto. }
  eapply stchain_chain'. eauto. eauto.
  eapply lls_mono. eauto.
Qed.



(* ---------- val_type lemmas  ---------- *)

Lemma valt_wf: forall T M H V v ls,
    val_type M H V v T ls ->
    psub (plift ls) (st_locs M).
Proof.
  intros T. induction T; intros; destruct v; rewrite val_type_def in *; simpl in *; intuition.
Qed.


Lemma valt_closed: forall T M H V v ls,
    val_type M H V v T ls ->
    closed_ty 0 (length H) T.
Proof.
  intros T. induction T; intros; try constructor; destruct v; rewrite val_type_def in *; simpl in *; intuition.
Qed.

Lemma variance_fvs_closed: forall T x y n f,
  x < y ->
  occurrences_fvs f T x ->
  occurrences_fvs f (opent n (qone y) T) x.
Proof.
  intros T. induction T; intros; intuition.
  - simpl in *. intuition. apply H2.
    rewrite plift_or, plift_if, plift_one in H0.
    destruct H0; auto. destruct (qbvs q n); inversion H0. lia.
  - simpl in *. repeat rewrite plift_or, plift_if, plift_one. intuition.
    apply H0. destruct H3; auto. destruct (qbvs q n); inversion H3. lia.
    apply H4. destruct H3; auto. destruct (qbvs q0 (n+2)); inversion H3. lia.
Qed.

Lemma variance_fvs_closed': forall T x y n q f,
  x <> y ->
  q x = false ->
  occurrences_fvs f T x ->
  occurrences_fvs f (opent n (qor (qone y) q) T) x.
Proof.
  intros T. induction T; intros; intuition.
  - simpl in *. intuition. apply H3.
    rewrite plift_or, plift_if, plift_or, plift_one in H1.
    destruct H1; auto. destruct (qbvs q n); inversion H1.
    unfold pone in H4. lia. exfalso. rewrite H4 in H0. discriminate.
  - simpl in *. repeat rewrite plift_or, plift_if, plift_or, plift_one. intuition.
    apply H1. destruct H4; auto. destruct (qbvs q n); inversion H4.
    unfold pone in H6. intuition. rewrite H6 in H0. discriminate.
    apply H5. destruct H4; auto. destruct (qbvs q0 (n+2)); inversion H4.
    unfold pone in H6. intuition. rewrite H6 in H0. discriminate.
Qed.

Lemma variance_open: forall T x m n f,
  closed_ty m n T ->
  occurrences_bvs f T x ->
  occurrences_fvs f (opent x (qone n) T) n.
Proof.
  intros T. induction T; intros; intuition.
  - inversion H; subst. simpl in *. intuition.
    eapply IHT; eauto. apply H2.
    rewrite plift_or, plift_if, plift_one in H0. destruct H0.
    exfalso. destruct H7. apply H4 in H0. lia.
    destruct (qbvs q x) eqn:?. auto. inversion H0.
  - inversion H; subst. simpl in *.
    repeat rewrite plift_or, plift_if, plift_one. intuition.
    eapply IHT1; eauto. apply H0.
    destruct H3. exfalso. destruct H12. apply H6 in H3. lia.
    destruct (qbvs q x) eqn:?. auto. inversion H3.
    eapply IHT2; eauto. apply H4.
    destruct H3. exfalso. destruct H13. apply H6 in H3. lia.
    destruct (qbvs q0 (x+2)) eqn:?. auto. inversion H3.
Qed.

Lemma valt_lenv_change: forall T M H V' lsx lsx' V v ls f,
  length V < length H ->
  val_type M H (V'++lsx::V) v T ls ->
  occurrences_fvs f T (length V) ->
  match f with
  | covariant_only => psub (plift lsx) (plift lsx')
  | contravariant_only => psub (plift lsx') (plift lsx)
  | not_free => True
  end ->
  val_type M H (V'++lsx'::V) v T ls.
Proof.
  intros T. remember (ty_size T) as n.
  assert (Hge: n >= ty_size T). lia. clear Heqn.
  generalize dependent T. induction n; intros.
  all: destruct T; simpl in Hge; try lia.
  all: rewrite val_type_def in *; destruct v; intuition.
  - simpl in H2. destruct H8 as (vt & qt & ?).
    exists vt, qt. intuition.
    erewrite vars_locs_change_skip; eauto.
    erewrite vars_locs_change_skip; eauto.
    eapply IHn; eauto. lia. apply H12; auto. simpl; auto.
    apply H12; auto. eapply IHn; eauto. lia. simpl; auto.
  - simpl in H2. intuition. eapply IHn with (lsx' := lsx) in H13.
    2: lia. 2: auto. 2: eauto. 2: destruct f; simpl in *; auto.
    eapply H11 in H13; eauto. destruct H13 as (S'' & M'' & vy & lsy & ?).
    exists S'', M'', vy, lsy. intuition.
    repeat rewrite app_comm_cons in *. eapply IHn.
    simpl. repeat rewrite opent_preserves_ty_size. lia. simpl. lia. eauto.
    simpl. apply variance_fvs_closed. lia.
    apply variance_fvs_closed; eauto. auto.
    intros ? HL. apply H23 in HL as [HL | [HL | [HL | HL]]].
    left. destruct f.
    erewrite vars_locs_change_skip; eauto. intro. discriminate H18. auto.
    eapply vars_locs_change_congr; eauto.
    erewrite vars_locs_change_skip; eauto. intro. discriminate H18. auto.
    1-3: unfoldq; intuition.
    intros ? HL. apply H14 in HL as [HL | [HL | HL]].
    1-2: unfoldq; intuition. right. right. destruct f.
    eapply vars_locs_change_congr; eauto.
    erewrite vars_locs_change_skip; eauto. intro. discriminate H2. auto.
    erewrite vars_locs_change_skip; eauto. intro. discriminate H2. auto.
Qed.


Lemma valt_grow: forall T M H V v ls ls1,
  val_type M H V v T ls ->
  psub (plift ls) (plift ls1) ->
  psub (plift ls1) (st_locs M) ->
  length H = length V ->
  val_type M H V v T ls1.
Proof.
  intros T. induction T; intros.
  all: destruct v; rewrite val_type_def in *; try solve [intuition].
  - intuition. destruct H8 as (vt & qt & ?). exists vt, qt. intuition.
    intros ? HL. apply H7 in HL. destruct HL. left. auto.
    right. destruct b. apply H1. auto. inversion H10.
  - intuition. eapply H11 in H13; eauto. clear H11.
    destruct H13 as (S'' & M'' & vy & lsy & ?). exists S'', M'', vy, lsy.
    intuition. intros ? ? ?. apply H16. unfoldq. intuition.
    replace (lsx :: ls :: V) with ([lsx] ++ ls :: V) in H17. 2: reflexivity.
    eapply valt_lenv_change in H17. exact H17. simpl. lia.
    simpl. apply variance_fvs_closed. lia.
    rewrite <-H3. eapply variance_open; eauto. simpl; auto.
    intros ? HL. apply H19 in HL. destruct HL as [HL | [HL | [HL | HL]]].
    2: { destruct (qbvs q0 1). unfoldq. intuition. inversion HL. }
    1-3: unfoldq; intuition.
    eapply stchaind_tighten; eauto.
    intros ? HL. apply H14 in HL. destruct b. rewrite H8; auto.
    destruct (ls x) eqn:?. unfoldq. intuition.
    apply not_true_iff_false in Heqb. unfoldq. intuition.
    unfoldq; destruct b0; intuition.
Qed.


Lemma valt_store_change: forall T M' M H V v ls,
    val_type M H V v T ls ->
    st_chain_deep M M' (plift ls) ->
    val_type M' H V v T ls.
Proof.
  intros T. induction T; intros; destruct v; rewrite val_type_def in *; simpl in *; intuition.
  + intros ? ?. eapply H1. eapply lls_z. eauto.
  + intros ? ?. eapply H1. eapply lls_z. eauto.
  + intros ? ?. eapply H1. eapply lls_z. eauto.
  + intros ? ?. eapply H1. eapply lls_z. eauto.
  + intros ? ?. eapply H1. eapply lls_z. eauto.
  + remember H1 as H8. destruct H1 as (? & ? & ?). clear HeqH8.
    destruct H6 as [vt [qt [IX [QT [QT' VT]]]]].
    exists vt, qt.
    split. 2: split. 3: split. 4: split.
    * rewrite <-e. eauto. eapply lls_z. unfoldq. intuition.
    * eauto.
    * eauto.
    * intros. eapply IHT. eapply VT. eauto. eauto.
      eapply stchain_tighten. eauto.
      eapply lls_mono in H1.
      intros ? ?. eapply H1 in H6.
      eapply lls_s. 2: eauto. 2: eauto. unfoldq. intuition.
    * intros. eapply VT. eauto. eauto. eapply IHT. eauto.
      eapply stchaind_symm.
      eapply stchain_tighten. eauto.
      eapply lls_mono in H1.
      intros ? ?. eapply H1 in H6.
      eapply lls_s. 2: eauto. 2: eauto. unfoldq. intuition.
  + intros ? ?. eapply H1. eapply lls_z. eauto.
  + eapply H9.
    eapply stchaind_chain'. eauto.
    auto.
    intros ? ?. eauto.
    eauto. eauto. eauto.
Qed.

Lemma valt_store_extend: forall T M' M S H V v ls,
    val_type M H V v T ls ->
    store_type S M ->
    st_chain_full M M' ->
    val_type M' H V v T ls.
Proof.
  intros ? ? ?.
  replace (st_locs M') with (pnat (length M')).
  intros. eapply valt_store_change; eauto.
  eapply stchaindf_tighten; eauto.
  eapply valt_wf. eauto. unfoldq. eauto.
Qed.

Lemma closedq_openq_rec': forall n bn fn q mf,
  mf >= n + fn ->
  closed_ql2 (n+bn) mf q <-> closed_ql2 bn mf (openq_rec n bn fn q).
Proof.
  intros n. induction n; intros.
  - simpl in *. intuition.
  - simpl in *. rewrite <-Nat.add_succ_r, IHn with (fn := fn). 2: lia.
    rewrite <-openq_closed'. intuition.
    unfold closed_ql, qone. setoid_rewrite Nat.eqb_eq. intuition.
Qed.

Lemma closedq_openq_rec: forall n bn fn q mf,
  closed_ql2 (n+bn) fn q ->
  mf >= n + fn ->
  closed_ql2 bn mf (openq_rec n bn fn q).
Proof.
  intros. apply closedq_openq_rec'; auto. eapply closedq2_extend; eauto. lia.
Qed.

Lemma closedty_opent_rec': forall n bn fn t mf,
  mf >= n + fn ->
  closed_ty (n+bn) mf t <-> closed_ty bn mf (opent_rec n bn fn t).
Proof.
  intros n. induction n; intros.
  - simpl in *. intuition.
  - simpl in *. rewrite <-Nat.add_succ_r, IHn with (fn := fn). 2: lia.
    rewrite <-opent_closed'. intuition.
    unfold closed_ql, qone. setoid_rewrite Nat.eqb_eq. intuition.
Qed.

Lemma closedty_opent_rec: forall n bn fn t mf,
  closed_ty (n+bn) fn t ->
  mf >= n + fn ->
  closed_ty bn mf (opent_rec n bn fn t).
Proof.
  intros. apply closedty_opent_rec'; auto. eapply closedty_extend; eauto. lia.
Qed.

Definition qnat (n x: nat) := x <? n.

Lemma plift_nat: forall n,
  plift (qnat n) = pnat n.
Proof.
  unfold plift, qnat, pnat. intros.
  apply functional_extensionality; intros.
  apply propositional_extensionality.
  rewrite Nat.ltb_lt. split; auto.
Qed.

Lemma openq_rec_qbvs: forall n bn fn q,
  qbvs (openq_rec n bn fn q) = qdiff (qbvs q) (qdiff (qnat (n+bn)) (qnat bn)).
Proof.
  assert (forall p q x, (plift p x <-> plift q x) <-> p x = q x).
  { intros. unfold plift. destruct (p x); destruct (q x); intuition. }
  intros n. induction n; intros; simpl in *.
  all: apply functional_extensionality; intros; rewrite <-H.
  - repeat rewrite plift_diff. repeat rewrite plift_nat.
    unfoldq; intuition.
  - rewrite IHn, Nat.add_succ_r. repeat rewrite plift_diff.
    repeat rewrite plift_nat. rewrite plift_one.
    unfoldq; intuition.
Qed.

Lemma vars_locs_openq_rec: forall n V' V bn fn fn' q,
  closed_ql (length V) (qfvs q) ->
  fn = length V + fn' ->
  vars_locs (V'++V) (plift (qfvs (openq_rec n bn fn q))) =
  por (vars_locs V' (plift (qfvs (openq_rec n bn fn' (qbvs q, qempty)))))
      (vars_locs V (plift (qfvs q))).
Proof.
  intros n. induction n; intros; subst; simpl in *.
  - destruct q as (qb, qf). simpl in *. rewrite plift_empty, vars_locs_empty.
    rewrite vars_locs_extend. 2: auto.
    apply functional_extensionality. intros.
    apply propositional_extensionality. split; intros.
    unfoldq; intuition. unfoldq; intuition.
  - repeat rewrite plift_or, plift_if, plift_one, vars_locs_or, vars_locs_if.
    rewrite IHn with (fn' := fn'); auto.
    repeat rewrite openq_rec_qbvs. simpl.
    replace (vars_locs (V' ++ V) (pone _)) with (vars_locs V' (pone (n + fn'))).
    all: apply functional_extensionality; intros; apply propositional_extensionality.
    unfoldq; intuition. split; intros.
    * destruct H0 as (x0 & ? & ?). inversion H0. exists (x0+length V). split.
      unfoldq. lia.
      destruct H1 as (x1 & ? & ?). exists x1. split; auto.
      rewrite indexr_skips'. replace (x0 + _ - _) with x0; auto. lia. lia.
    * destruct H0 as (x0 & ? & ?). inversion H0. exists (x0 - length V). split.
      unfoldq. lia.
      destruct H1 as (x1 & ? & ?). exists x1. split; auto.
      rewrite <-indexr_skips'. auto. lia.
Qed.

Lemma opent_rec_fold: forall n a b T,
  opent n (qone (a + b)) (opent_rec a (S n) b T) = opent_rec (S a) n b T.
Proof.
  intros. auto.
Qed.

Lemma variance_bvs_closed: forall T n q x f,
  n > x ->
  occurrences_bvs f (opent n q T) x = occurrences_bvs f T x.
Proof.
  intros T. induction T; intros; intuition.
  all: apply propositional_extensionality; split.
  all: simpl; intuition.
  - rewrite IHT in H1; auto.
  - apply H2. rewrite plift_diff, plift_one. unfoldq. intuition.
  - rewrite IHT; auto.
  - apply H2. rewrite plift_diff in H0. unfoldq. intuition.
  - rewrite IHT1 in H1; auto.
  - apply H0. rewrite plift_diff, plift_one. unfoldq. intuition.
  - rewrite IHT2 in H2; auto. lia.
  - apply H4. rewrite plift_diff, plift_one. unfoldq. intuition.
  - rewrite IHT1; auto.
  - apply H0. rewrite plift_diff in H3. unfoldq. intuition.
  - rewrite IHT2; auto. lia.
  - apply H4. rewrite plift_diff in H3. unfoldq. intuition.
Qed.

Lemma variance_bvs_closed_rec: forall m T n q x f,
  n > x ->
  occurrences_bvs f (opent_rec m n q T) x = occurrences_bvs f T x.
Proof.
  intros m. induction m; intros.
  - simpl. auto.
  - simpl. rewrite variance_bvs_closed; auto.
Qed.

Lemma valt_opent: forall T M H0 H' H V0 V' V v ls
    (L: length H = length V)
    (L': length H' = length V')
    (L0: length H0 = length V0),
    closed_ty (length H0) (length H) T ->
    val_type M (H0++H'++H) (V0++V'++V) v (opent_rec (length H0) 0 (length (H'++H)) T) ls <->
    val_type M (H0++H) (V0++V) v (opent_rec (length H0) 0 (length H) T) ls.
Proof.
  intros T. induction T; split; intros; destruct v.
  all: rewrite val_type_def in *; simpl in *; intuition.
  all: rewrite opent_rec_iff in *; try contradiction; intuition.
  - apply closedty_opent_rec. inversion H1; subst. rewrite Nat.add_0_r. auto.
    rewrite app_length. lia.
  - apply closedq_openq_rec. inversion H1; subst. rewrite Nat.add_0_r. auto.
    rewrite app_length. lia.
  - (* Ref shrink *)
    inversion H1; subst. destruct H13. rewrite L in H8.
    destruct H7 as (vt & qt & ?). exists vt, qt. intuition.
    rewrite vars_locs_openq_rec with (fn' := 0); auto.
    rewrite vars_locs_openq_rec with (fn' := 0) in H7.
    rewrite vars_locs_extend in H7; auto.
    eapply closedq_extend; eauto. repeat rewrite app_length; lia. lia.
    rewrite vars_locs_openq_rec with (fn' := 0); auto.
    rewrite vars_locs_openq_rec with (fn' := 0) in H10.
    rewrite vars_locs_extend in H10; auto.
    eapply closedq_extend; eauto. repeat rewrite app_length; lia. lia.
    apply H13 in H14; auto. eapply IHT with (H := H) in H14; eauto.
    apply H13; auto. apply IHT; auto.
  - apply closedty_opent_rec. inversion H1; subst.
    eapply closedty_extend; eauto. lia. rewrite app_length. lia.
  - apply closedq_openq_rec. inversion H1; subst.
    eapply closedq2_extend; eauto. lia. rewrite app_length. lia.
  - (* Ref grow *)
    inversion H1; subst. destruct H13. rewrite L in H8.
    destruct H7 as (vt & qt & ?). exists vt, qt. intuition.
    rewrite vars_locs_openq_rec with (fn' := 0).
    rewrite vars_locs_openq_rec with (fn' := 0) in H7; auto.
    rewrite vars_locs_extend; auto. lia.
    eapply closedq_extend; eauto. repeat rewrite app_length; lia.
    rewrite vars_locs_openq_rec with (fn' := 0).
    rewrite vars_locs_openq_rec with (fn' := 0) in H10; auto.
    rewrite vars_locs_extend; auto. lia.
    eapply closedq_extend; eauto. repeat rewrite app_length; lia.
    eapply IHT with (H' := H'); eauto. apply H13; auto.
    apply H13; auto. apply IHT in H14; auto.
  - apply closedty_opent_rec. rewrite Nat.add_0_r. inversion H1. auto.
    rewrite app_length. lia.
  - apply closedq_openq_rec. rewrite Nat.add_0_r. inversion H1. auto.
    rewrite app_length. lia.
  - apply closedty_opent_rec. simpl. inversion H1. auto.
    rewrite app_length. lia.
  - apply closedq_openq_rec. simpl. inversion H1. auto.
    rewrite app_length. lia.
  - rewrite variance_bvs_closed_rec. rewrite variance_bvs_closed_rec in H8.
    auto. lia. lia.
  - (* Abs shrink *)
    inversion H1. subst. destruct H25. destruct H26. rewrite L in H15, H17.
    destruct (H10 S' M' vx lsx) as [S'' [M'' [vy [lsy [HEY HVY]]]]]. eauto. eauto.
    eapply IHT1; eauto.
    rewrite vars_locs_openq_rec with (fn' := 0).
    rewrite vars_locs_openq_rec with (fn' := 0) in H13; auto.
    rewrite vars_locs_extend; auto. lia.
    eapply closedq_extend; eauto. repeat rewrite app_length; lia.
    exists S'', M'', vy, lsy. intuition; simpl in *.
    rewrite app_length, opent_rec_fold, <-Nat.add_succ_l, opent_rec_fold in H22.
    repeat rewrite app_comm_cons in H22.
    replace (S (S (length H0))) with (length (vx :: vabs l t :: H0)) in H22; auto.
    eapply IHT2 with (H := H) in H22; eauto. simpl in H22. rewrite app_length; auto.
    simpl. rewrite L0. auto. simpl. eapply closedty_extend; eauto. lia.
    rewrite openq_rec_qbvs in *. rewrite vars_locs_openq_rec with (fn' := 0); auto.
    rewrite vars_locs_openq_rec with (fn' := 0) in H25. rewrite vars_locs_extend in H25; auto.
    eapply closedq_extend; eauto. repeat rewrite app_length; lia. lia.
  - apply closedty_opent_rec. inversion H1; subst. eapply closedty_extend; eauto.
    lia. rewrite app_length. lia.
  - apply closedq_openq_rec. inversion H1; subst. eapply closedq2_extend; eauto.
    lia. rewrite app_length. lia.
  - apply closedty_opent_rec. inversion H1; subst. eapply closedty_extend; eauto.
    rewrite app_length. lia.
  - apply closedq_openq_rec. inversion H1; subst. eapply closedq2_extend; eauto.
    rewrite app_length. lia.
  - rewrite variance_bvs_closed_rec. rewrite variance_bvs_closed_rec in H8.
    auto. lia. lia.
  - (* Abs grow *)
    inversion H1. subst. destruct H25. destruct H26. rewrite L in H15, H17.
    destruct (H10 S' M' vx lsx) as [S'' [M'' [vy [lsy [HEY HVY]]]]]. eauto. eauto.
    eapply IHT1 with (H := H) in H12; eauto.
    rewrite vars_locs_openq_rec with (fn' := 0); auto.
    rewrite vars_locs_openq_rec with (fn' := 0) in H13.
    rewrite vars_locs_extend in H13; auto.
    eapply closedq_extend; eauto. repeat rewrite app_length; lia. lia.
    exists S'', M'', vy, lsy. intuition; simpl in *.
    rewrite app_length, opent_rec_fold, <-Nat.add_succ_l, opent_rec_fold.
    repeat rewrite app_comm_cons.
    replace (S (S (length H0))) with (length (vx :: vabs l t :: H0)); auto.
    eapply IHT2 with (H := H); eauto. simpl. rewrite L0. auto.
    simpl. eapply closedty_extend; eauto. lia.
    simpl. rewrite app_length in H22. auto.
    rewrite openq_rec_qbvs in *. rewrite vars_locs_openq_rec with (fn' := 0).
    rewrite vars_locs_openq_rec with (fn' := 0) in H25; auto.
    rewrite vars_locs_extend; auto. lia.
    eapply closedq_extend; eauto. repeat rewrite app_length; lia.
Qed.

Lemma valt_extend: forall T M H' H V' V v ls
  (L: length H = length V)
  (L': length H' = length V'),
  closed_ty 0 (length H) T ->
  val_type M (H'++H) (V'++V) v T ls <->
  val_type M H V v T ls.
Proof.
  intros. specialize (valt_opent T M [] H' H [] V' V v ls) as H1.
  simpl in H1. apply H1; auto.
Qed.

Lemma valt_extend1: forall T M H V v ls vx lsx,
    length H = length V ->
    closed_ty 0 (length H) T ->
    val_type M (vx::H) (lsx::V) v T ls <-> val_type M H V v T ls.
Proof.
  intros.
  replace (vx :: H)  with ([vx]  ++ H); auto.
  replace (lsx :: V)  with ([lsx] ++ V); auto.
  eapply valt_extend; eauto.
Qed.


(* ---------- val_qual lemmas  ---------- *)

Lemma valq_sub: forall M M1 H v p q fr fr' q',
    val_qual M M1 H v p fr q ->
    psub q q' ->
    psub q' (pdom H) ->
    val_qual M M1 H v p (fr || fr') q'.
Proof.
  intros. intros ? ?.
  destruct (H0 x) as [H_q | H_fr]. eauto.
  - (* q  *) left. eapply vars_locs_monotonic; eauto. unfoldq. intuition.
  - (* fr *) destruct fr. 2: contradiction. right. eauto.
Qed.

Lemma valq_sub': forall M M1 H v p q fr fr' q',
    val_qual M M1 H v p fr q ->
    psub q q' ->
    psub q' (pdom H) ->
    bsub fr fr' ->
    val_qual M M1 H v p fr' q'.
Proof.
  intros. intros ? ?.
  destruct (H0 x) as [H_q | H_fr]. eauto.
  - (* q  *) left. eapply vars_locs_monotonic; eauto. unfoldq. intuition.
  - (* fr *) destruct fr. 2: contradiction. right.
    rewrite H3. eauto. eauto.
Qed.

Lemma valq_sub'': forall M M1 H v p q fr fr' q',
    val_qual M M1 H v p fr q ->
    psub (vars_locs H q) (vars_locs H q') ->
    psub q' p ->
    bsub fr fr' ->
    val_qual M M1 H v p fr' q'.
Proof.
  intros. intros ? ?.
  destruct (H0 x) as [H_q | H_fr]. eauto.
  - (* q  *) left.
    assert (vars_locs H q x) as VL. {
      eapply vars_locs_monotonic. 2: eauto. unfoldq. intuition. }
    eapply H1 in VL.
    eapply vars_locs_monotonic; eauto. unfoldq. intuition.
  - (* fr *) destruct fr. 2: contradiction. right.
    rewrite H3. eauto. eauto.
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
  destruct H2 as [? [? ?]].
  assert (x0 < length V). eapply indexr_var_some'. eauto.

  assert (exists xtq, indexr x0 G = Some xtq) as TY.
  rewrite L2 in H4. eapply indexr_var_some in H4. intuition.
  destruct TY as [TQ  ?]. destruct TQ as [[T0 fr0] q0].
  destruct (W1 x0 T0 fr0 q0) as [vx [lsx [? ?]]]. eauto.

  intuition. rewrite H2 in H9. inversion H9. subst x1.
  eapply valt_wf; eauto.
Qed.


Lemma env_type_store_deep_wf: forall M H G V p q,
    env_type M H G V p ->
    psub q p ->
    psub (vars_locs V q) (st_locs M).
Proof.
  intros. intros ? ?. inversion H2; subst. eapply env_type_store_wf; eauto.
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
    destruct (W x T fr q) as (v & ls & ?); eauto.
    intuition. exists v, ls. intuition.
  - intros.
    destruct W as [? W].
    eapply W.
    unfoldq. intuition.
    unfoldq. intuition.
    unfoldq. intuition.
Qed.

Lemma envt_store_change: forall M M' H G V p,
    env_type M H G V p ->
    st_chain_deep M M' (vars_locs V p) ->
    env_type M' H G V p.
Proof.
  intros. remember H0 as WFE1. clear HeqWFE1. destruct H0 as [L1 [L2 [P W]]].
  repeat split; auto.
  - intros.
    destruct W as [W W'].
    destruct (W _ _  _ _ H0) as [vx [lsx [CL [IH [HVX HF]]]]]; intuition.
    exists vx, lsx; intuition.
    eapply valt_store_change. eauto. eapply stchaind_tighten. eauto.
    intros ? ?. exists x. split. eauto. exists lsx. intuition.
  - intros.
    destruct W as [W' W].
    intros ? [? ?]. specialize (W _ _ H0 H2 H3).
    eapply W. split; eauto.
Qed.

Lemma envt_store_change_empty: forall M M' H G V,
    env_type M H G V pempty ->
    env_type M' H G V pempty.
Proof.
  intros. eapply envt_store_change. eauto.
  eapply stchain_tighten. eapply stchain_empty.
  intros ? ?. eapply lls_vars in H1. destruct H1 as (? & (? & ?)).
  contradiction.
Qed.

Lemma envt_store_extend: forall S M M' H G V p,
    env_type M H G V p ->
    store_type S M ->
    st_chain_full M M' ->
    env_type M' H G V p.
Proof.
  intros. remember H0 as WFE1. clear HeqWFE1. destruct H0 as [L1 [L2 [P W]]].
  repeat split; auto.
  - intros.
    destruct W as [W W'].
    destruct (W _ _  _ _ H0) as [vx [lsx [CL [IH [HVX HF]]]]]; intuition.
    exists vx, lsx; intuition.
    eapply valt_store_extend; eauto.
  - intros.
    destruct W as [W' W].
    intros ? [? ?]. specialize (W _ _ H0 H3 H4).
    eapply W. split; eauto.
Qed.


Lemma envt_extend_full: forall M M1 H G V vx T1 p fr1 q1 qf lsx,
    env_type M H G V p ->
    val_type M1 H V vx T1 lsx ->
    psub qf p ->
    psub (plift q1) qf ->
    psub (pand (vars_locs V qf) (plift lsx))
         (vars_locs V (plift q1)) ->
    (fr1 = false -> psub (plift lsx) (vars_locs V (plift q1))) ->
    closed_ty 0 (length H) T1 ->
    closed_ql (length H) q1 ->
    True ->
    st_chain_deep M M1 (vars_locs V qf) ->
    env_type M1 (vx :: H) ((T1, fr1, q1) :: G) (lsx::V) (por qf (pone (length H))).
Proof.
  intros. apply wf_env_type in H0 as H0'. destruct H0' as (L' & L'' & PD & PD' (*& SG*)).
  rename H8 into CH.

  rename H0 into WFE.
  remember True as H0.
  rename H9 into SC.

  remember WFE as WFE1. clear HeqWFE1.
  destruct WFE as [L1 [L2 [P [W1 W2]]]].
  assert (length V = length H) as L3. intuition.
  assert (psub p (pdom G)). rewrite <-PD. eauto.
  assert (psub p (pdom V)) as PV. unfoldq. rewrite L3. intuition.

  repeat split; eauto.
  - simpl. eauto.
  - simpl. eauto.
  - unfoldq. simpl. intuition.
  - intros.
    bdestruct (x =? length G); intuition.
    + subst. rewrite indexr_head in H9. inversion H9. subst.
      exists vx, lsx. repeat split.
      rewrite <-L1. eauto.
      rewrite <-L1. eauto.
      rewrite <-L1. rewrite indexr_head. auto.
      rewrite <-L2. rewrite indexr_head. auto.
      intros. eapply valt_extend1; auto.
      rewrite <-vars_locs_extend with (H':=[lsx]) in H5; eauto.
      intros ? ?. eapply H7 in H0. unfoldq. intuition.
    + rewrite indexr_skip in H9.
      specialize (W1 x T fr q H9).
      assert (x < length H). { rewrite L1. apply indexr_var_some' in H9. auto. }
      rewrite indexr_skip. rewrite indexr_skip.
      destruct W1 as [v [ls [TLT [TL [IH1 [IH2  [VALT FR]]]]]]].
      exists v, ls. repeat split; eauto.
      intros. eapply valt_extend1. eauto. eapply valt_closed in VALT; eauto. unfoldq. intuition.
      {
        eapply valt_store_change. eapply VALT. unfoldq. intuition.
        assert (qf x). { destruct H12. eauto. unfoldq. lia. }
        eapply stchaind_tighten. eauto.
        unfoldq. intuition. exists x; intuition. exists ls; intuition.
      } {
        intros. intros ? ?.
        rewrite <-vars_locs_extend with (H':=[lsx]) in FR; eauto.
        eapply FR. eauto. auto. auto. unfoldq. intuition. eapply TL in H15.
        apply indexr_var_some' in H9. lia.
      }
      lia. lia. lia.
  - (* 2nd invariant *)
    clear W1. (* distraction*)
    eapply envt_telescope in WFE1 as TL1.

    intros q q' QSUB QSUB' QSUBTR x (QQ & QQ').

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

        eapply QSUB in VTQ as A. destruct A.
        eexists. split. 2: eapply var_locs_shrink. 2: eapply VLQ. unfoldq ; intuition.
        eapply H2 in H11. eapply PV; auto.
        unfold pone in H11. subst x0.
        eapply H2 in H9. eapply PV in H9. unfoldq; intuition.

        eapply QSUB' in VTQ' as B. destruct B.
        eexists. split. 2: eapply var_locs_shrink. 2: eapply VLQ'. unfoldq ; intuition.
        eapply H2 in H11. eapply PV; auto.
        unfold pone in H11. subst x1.
        eapply H2 in H10. eapply PV in H10. unfoldq; intuition.
      }

      destruct W3 as (? & (? & ?) & ?).

      eexists. split. split.
      eapply vt_extend. eapply vt_mono. 2: eapply H11. unfoldq. intuition.
      eapply vt_extend. eapply vt_mono. 2: eapply H12. unfoldq. intuition.
      eapply var_locs_extend; eauto.
    + (* qf, x *)
      unfold pone in H10. subst x1.

      assert (psub (pand (vars_trans G (pand (pdom H) q)) (vars_trans G (plift q1))) qf) as QSUBTR1. {
        intros ? [? ?]. destruct (QSUBTR x1) as [? | ?].
        split. {
          eapply vt_extend. eapply vt_mono. 2: eapply H10. unfoldq. intuition. (* extend q *)
        }{
          eapply vt_head. eauto. rewrite <-PD. eauto. rewrite <-L1. eauto.
          rewrite <-L1. eauto. eauto. (* pick q1 *)
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

        eexists. split. 2: eapply var_locs_shrink in VLQ; eauto.
        unfoldq; intuition. eapply H2 in H9. eapply PV. auto.

        eapply H4. split. exists x0; intuition. eapply var_locs_shrink; eauto. eapply H2 in H9. eapply PV. auto.
        destruct VLQ' as [? [? ?]]. rewrite <-L3, indexr_head in H10. inversion H10. subst x1. auto.
      }

      destruct W3 as (? & (? & ?) & ?).
      eexists. split. split.
      eapply vt_extend. eapply vt_mono. 2: eapply H10. unfoldq. intuition.
      eapply vt_head. eauto. rewrite <-PD. eauto. rewrite <-L1. eauto.
      rewrite <-L1. eauto. eauto.
      eapply var_locs_extend; eauto.

    + (* x, qf *)
      unfold pone in H9. subst x0.

      assert (psub (pand (vars_trans G (plift q1)) (vars_trans G (pand (pdom H) q'))) qf) as QSUBTR1. {
        intros ? [? ?]. destruct (QSUBTR x0) as [? | ?].
        split. {
          eapply vt_head. eauto. rewrite <-PD. eauto. rewrite <-L1. eauto.
          rewrite <-L1. eauto. eauto. (* pick q1 *)
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

        eapply H4. split.
        eexists. split. eapply H10. eapply var_locs_shrink; eauto. eapply H2 in H10. eapply PV. auto.
        destruct VLQ as [? [? ?]]. rewrite <-L3, indexr_head in H9. inversion H9. subst x0. auto.
        eexists. split. 2: { eapply var_locs_shrink; eauto. eapply H2 in H10. eapply PV. auto. } unfoldq; intuition.
      }

      destruct W3 as (? & (? & ?) & ?).
      eexists. split. split.

      eapply vt_head. eauto. rewrite <-PD. eauto. rewrite <-L1. eauto.
      rewrite <-L1. eauto. eauto.
      eapply vt_extend. eapply vt_mono. 2: eapply H11. unfoldq. intuition.
      eapply var_locs_extend; eauto.

    + (* x, x *)
      unfold pone in H9, H10.
      subst x0 x1.
      eexists. split. split.
      3: eauto.
      left. eauto. left. eauto.
Qed.



Lemma overlapping: forall S S' M M' M'' H G V p lsf lsx frf qf frx qx q1
    (ST0 : store_type S M)
    (ST : store_type S' M')
    (WFE: env_type M H G V p)
    (CH1: st_chain_full M M')
    (CH2: st_chain_full M' M'')
    (HQF: val_qual M M' V lsf p frf qf)
    (HQX: val_qual M' M'' V lsx p frx qx),
    psub (plift lsf) (st_locs M') ->
    psub (plift q1) p ->
    psub (pand (vars_trans G (pand p qf)) (vars_trans G (pand p qx))) (plift q1) ->
    psub (pand (plift lsf) (plift lsx)) (vars_locs V (plift q1)).
Proof.
  intros. intros ? [? ?].
  remember WFE as WFE1. clear HeqWFE1.
  eapply envt_store_extend in WFE; eauto.
  eapply envt_store_extend in WFE; eauto.
  destruct WFE as [? [? [? SEP]]].

  destruct (HQF x) as [Hf_q | Hf_fr]. auto.

  - destruct (HQX x) as [Hx_q | Hx_fr]. eauto.
    + assert ((pand (vars_locs V (pand p qf))
                    (vars_locs V (pand p qx))) x).
      split; eauto.
      eapply SEP in H8.
      eapply vars_locs_monotonic. 2: eauto.
      unfoldq. intuition.
      unfoldq. intuition.
      unfoldq. intuition.
      unfoldq. intuition.
    + destruct frx. 2: contradiction.
      eapply env_type_store_wf in Hf_q.
      2: { eapply envt_store_extend; eauto. } 2: { unfoldq. intuition. }
      assert False. eapply Hx_fr. eauto. contradiction.
  - destruct frf. 2: contradiction.
    destruct (HQX x) as [Hx_q | Hx_fr]. eauto.
    + eapply env_type_store_wf in Hx_q.
      2: { eauto. }
      2: { unfoldq. intuition. }
      assert False. eapply Hf_fr. eauto. contradiction.
    + destruct frx. 2: contradiction.
      assert False. eapply Hx_fr. eapply H0. eauto. contradiction.
Qed.



(* ---------- store vs store typing reachability ---------- *)

Lemma storet_shrink: forall M S v a,
    store_type (v::S) (a::M) ->
    store_type S M.
Proof.
  intros. destruct H as (STL & STT).
  assert (length M = length S) as STL1. simpl in STL. lia.
  split.
  - eauto.
  - intros. unfold st_locs in *.
    destruct (STT l) as (vt & qt & v1 & ls & ? & ? & ? & ? & ?).
    unfoldq. simpl. lia.
    exists vt, qt, v1, ls.
    split. 2: split. 3: split. 4: split.
    + rewrite indexr_skip in H0. eauto. unfoldq. lia.
    + rewrite indexr_skip in H1. eauto. unfoldq. lia.
    + eauto.
    + eauto.
    + eauto.
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



(* ----- qualifier subsumption -----*)

Definition env_type' M H G V p :=
  length H = length G /\
  length V = length G /\
    psub p (pdom H) /\
    (forall x T fr (q:ql),
        indexr x G = Some (T, fr, q) ->
        exists (v : vl) ls,
          closed_ty 0 x T /\
          closed_ql x q /\
          indexr x H = Some v /\
          indexr x V = Some ls /\
          (p x -> val_type M H V v T ls) /\
          (fr = false -> (* psub (plift q) p *) True -> psub (plift ls) (vars_locs V (plift q)))).

Lemma wf_env_type': forall M H G V p,
  env_type' M H G V p ->
  length H = length G /\
  length V = length G /\
  pdom H = pdom G /\
  pdom V = pdom G.
Proof.
  intros. unfold env_type' in H0. intuition.
  unfold pdom. rewrite H1. auto.
  unfold pdom. rewrite H0. auto.
Qed.

Lemma envt_tighten': forall M H G V p p',
    env_type' M H G V p ->
    psub p' p ->
    env_type' M H G V p'.
Proof.
  intros. destruct H0 as [L1 [L2 [P W]]].
  repeat split; auto.
  - unfoldq. intuition.
  - intros.
    destruct (W x T fr q) as (v & ls & ?); eauto.
    intuition. exists v, ls. intuition.
Qed.

Lemma envt_store_change': forall M M' H G V p,
    env_type' M H G V p ->
    st_chain_deep M M' (vars_locs V p) ->
    env_type' M' H G V p.
Proof.
  intros. remember H0 as WFE1. clear HeqWFE1. destruct H0 as [L1 [L2 [P W]]].
  repeat split; auto.
  - intros.
    destruct (W _ _  _ _ H0) as [vx [lsx [CL [IH [HVX HF]]]]]; intuition.
    exists vx, lsx; intuition.
    eapply valt_store_change. eauto. eapply stchaind_tighten. eauto.
    intros ? ?. exists x. split. eauto. exists lsx. intuition.
Qed.

Lemma env_type_store_wf': forall M H G V p q,
    env_type' M H G V p ->
    psub q p ->
    psub (vars_locs V q) (st_locs M).
Proof.
  intros. destruct H0 as [L1 [L2 [P W1]]]; intuition.
  unfoldq. intuition.
  destruct H0 as [? [? ?]].
  destruct H2 as [? [? ?]].
  assert (x0 < length V). eapply indexr_var_some'. eauto.

  assert (exists xtq, indexr x0 G = Some xtq) as TY.
  rewrite L2 in H4. eapply indexr_var_some in H4. intuition.
  destruct TY as [TQ  ?]. destruct TQ as [[T0 fr0] q0].
  destruct (W1 x0 T0 fr0 q0) as [vx [lsx [? ?]]]. eauto.

  intuition. rewrite H2 in H9. inversion H9. subst x1.
  eapply valt_wf; eauto.
Qed.

Lemma envt_extend_stub': forall M M1 H G V vx lsx T1 fr1 q1 p p',
    env_type' M H G V p ->
    val_type M1 H V vx T1 lsx ->
    (fr1 = false -> psub (plift lsx) (vars_locs V (plift q1))) ->
    closed_ty 0 (length H) T1 ->
    closed_ql (length H) q1 ->
    st_chain_deep M M1 (vars_locs V p) ->
    psub p' p ->
    env_type' M1 (vx :: H) ((T1, fr1, q1) :: G) (lsx :: V) (por p' (pone (length H))).
Proof.
  intros. eapply envt_store_change' in H0. 2: eauto.
  destruct H0 as (? & ? & ? & ?).
  split. 2: split. 3: split.
  - simpl. eauto.
  - simpl. eauto.
  - unfoldq. simpl. intuition.
  - intros. bdestruct (x =? length G).
    + subst. rewrite indexr_head in H10. inversion H10. subst T1 fr1 q1.
      exists vx, lsx. repeat split.
      rewrite <-H0. eauto.
      rewrite <-H0. eauto.
      rewrite <-H0. rewrite indexr_head. eauto.
      rewrite <-H7. rewrite indexr_head. eauto.
      intros. eapply valt_extend1. congruence. auto. auto.
      intros. intros ? ?. eapply vars_locs_extend1. eapply H2. eauto. eauto.
    + destruct (H9 x T fr q) as (v & ls & ? & ? & ? & ?).
      rewrite indexr_skip in H10. eauto. eauto.
      exists v, ls. intuition.
      rewrite indexr_extend1 in H14. eapply H14.
      rewrite indexr_extend1 in H16. eapply H16.
      assert (HPX: p x). destruct H17; auto. congruence.
      apply H15 in HPX. apply valt_closed in HPX as HVC.
      eapply valt_extend1. congruence. auto. auto.
      intros ? ?. eapply vars_locs_extend1. eauto.
Qed.

Definition sem_qtp2 G fr1 q1 fr2 q2 :=
  forall M E V p,
    env_type' M E G V p ->
    bsub fr1 fr2 /\
    psub q1 (pdom G) /\
    psub q2 (pdom G) /\
    psub (vars_locs V q1) (vars_locs V q2) /\
    True.

Lemma sem_qtp2_sub: forall G fr1 q1 fr2 q2,
    psub q1 q2 ->
    psub q2 (pdom G) ->
    bsub fr1 fr2 ->
    sem_qtp2 G fr1 q1 fr2 q2.
Proof.
  intros. intros ? ? ? WFE. split. auto.
  split. unfoldq. intuition.
  split. eauto.
  split. eapply vars_locs_monotonic. unfoldq. intuition.
  auto.
Qed.

Lemma sem_qtp2_var: forall G (q1:pl) Tx qx x fr1,
    q1 x ->
    indexr x G = Some (Tx, false, qx) ->
    psub q1 (pdom G) ->
    True ->
    sem_qtp2 G fr1 q1 fr1 (por (pdiff q1 (pone x)) (plift qx)).
Proof.
  intros. rename H2 into QP. intros ? ? ? ? WFE.
  eapply WFE in H0.
  destruct H0 as (v & ls & ? & ? & ? & ?).
  split. unfold bsub. auto.
  split. eauto.
  split. {
    intros ? ?. unfoldq. intuition.
    assert (x0 < x). eapply H2. auto. apply indexr_var_some' in H3.  destruct WFE as [? ?]. lia.
  } split. {
    intros ? (? & ? & ?).
    bdestruct (x =? x1).
    - subst x1. intuition.
      eapply vars_locs_monotonic. 2: eapply H9.
      unfoldq. intuition.
      destruct H6. destruct H6. rewrite H6 in H7.
      inversion H7. subst. eauto.
    - exists x1. unfoldq. intuition.
  }
  auto.
Qed.

Lemma sem_qtp2_trans: forall G (q1 q2 q3: pl) fr1 fr2 fr3,
  sem_qtp2 G fr1 q1 fr2 q2 ->
  sem_qtp2 G fr2 q2 fr3 q3 ->
  sem_qtp2 G fr1 q1 fr3 q3 .
Proof.
  intros. intros ? ? ? ? WFE.
  destruct (H M E V p WFE) as [P0 [P1 [P2 P3]]].
  destruct (H0 M E V p WFE) as [Q0 [Q1 [Q2 Q3]]].
  split. unfold bsub in *. auto. split. 2: split. 3: split; auto.
  + auto.
  + auto.
  + unfoldq; intuition.
Qed.


(* ---------- main lemmas ---------- *)

Lemma sem_true: forall G p,
    sem_type G ttrue TBool p false pempty.
Proof.
  intros. intros S M H ? WFE ST.
  exists S, M, (vbool true), qempty.
  split. 2: split. 3: split. 4: split. 5: split.
  - exists 1. intros. destruct n. lia. simpl. intuition.
  - eapply stchain_refl.
  - eauto.
  - intros ? ? ? ?. auto.
  - rewrite val_type_def. unfoldq. intuition.
  - simpl. unfoldq. intuition.
Qed.

Lemma sem_false: forall G p,
    sem_type G tfalse TBool p false pempty.
Proof.
  intros. intros S M H ? WFE ST.
  exists S, M, (vbool false), qempty.
  split. 2: split. 3: split. 4: split. 5: split.
  - exists 1. intros. destruct n. lia. simpl. intuition.
  - eapply stchain_refl.
  - eauto.
  - intros ? ? ? ?. auto.
  - rewrite val_type_def. unfoldq. intuition.
  - simpl. unfoldq. intuition.
Qed.

Lemma sem_var: forall x G T (p:pl) fr q,
    indexr x G = Some (T, fr, q) ->
    p x ->
    sem_type G (tvar x) T p false (pone x).
Proof.
  intros. intros ? ? ? ? WFE ST.
  destruct WFE as [? [? [? [WFE ?]]]].
  destruct (WFE x T fr q H) as [vx [lsx [HT [HQ [HI [HI' [VT ?]]]]]]].
  exists S, M, vx, lsx.
  split. 2: split. 3: split. 4: split. 5: split. 6: split.
  - exists 1. intros. destruct n. lia. simpl. rewrite HI. reflexivity.
  - eapply stchain_refl.
  - eauto.
  - intros ? ? ? ?. auto.
  - eauto.
  - (* valq *)
    left.
    exists x. unfoldq. intuition. exists lsx. intuition.
  - intros ? (? & ? & ? & ? & ?). inversion H6. subst x1.
    congruence.
Qed.


Lemma storet_extend: forall S M S1 M1 E G V T p q vx lsx vt qt
    (ST:  store_type S M)
    (ST1: store_type S1 M1)
    (WFE: env_type M E G V p)
    (QP:  psub (plift q) p)
    (SC1: st_chain_full M M1)
    (SC2: st_chain_full M1 (st_extend M1 vt qt))
    (HVX: val_type M1 E V vx T lsx)
    (HQX: val_qual M M1 V lsx p false (plift q))
    (QT:  qt = vars_locs_fix V q)
    (VT:  vt = (fun (v : vl) => fun ls => val_type M1 E V v T ls)),
    store_type (vx :: S1) (st_extend M1 vt qt).
Proof.
  intros.
  remember ST1 as ST1'. destruct ST1' as (STL & STT). clear HeqST1'.
  split.
  - simpl. lia.
  - intros l SL. unfold st_extend in *.
    bdestruct (l =? length M1).
    + subst l.
      assert (psub (vars_locs V (plift q)) (st_locs M1)). {
        eapply env_type_store_wf. eapply envt_store_extend. eauto. eauto. eauto. eauto. }

      exists vt, qt, vx, lsx.
      split. 2: split. 3: split. 4: split.
      * rewrite indexr_head. eauto.
      * rewrite STL, indexr_head. intuition.
      * subst vt. eauto.
      * intros. intros ? ?.
        destruct (HQX x) as [H_q | H_fr]. eauto.
        (* q *) subst qt. rewrite <-plift_vars_locs. eapply vars_locs_monotonic; eauto. unfoldq. intuition.
        (* fr *) destruct H_fr.
      * subst qt. rewrite <-plift_vars_locs. intros ? ?. eapply env_type_store_wf. eapply envt_store_extend. eauto. eauto. eauto. eauto. eauto.
    + destruct (STT l) as (vt1 & qt1 & v1 & ls1 & IXM & IXS & VT1 & VL1 & VL2).
      unfold st_locs in *. unfoldq. simpl in SL. lia.
      exists vt1, qt1, v1, ls1.
      split. 2: split. 3: split. 4: split.
      * rewrite indexr_skip. eauto. lia.
      * rewrite indexr_skip. eauto. lia.
      * intuition.
      * intros ? ?.
        eauto.
      * eauto.
Qed.


Lemma sem_ref: forall t G p T q,
    sem_type G t T p false (plift q) ->
    psub (plift q) p ->
    sem_type G (tref t) (TRef T false (qempty, q)) p true pempty.
Proof.
  intros. intros ? ? ? ? WFE ST.
  destruct (H S M E V WFE ST) as [S1 [M1 [vx [lsx [IW1 [SC1 [ST1 [SE1 [HVX [HQX HQV]]]]]]]]]].
  remember (length S1) as x.
  remember (vars_locs_fix V q) as qt.
  remember (fun v => fun ls => val_type M1 E V v T ls) as vt.
  assert (st_chain M1 (st_extend M1 vt qt) (st_locs M1)). {
    split. 2: split.
    unfoldq. intuition.
    unfoldq. intuition.
    unfold st_locs, st_extend in *. unfoldq. simpl. intuition.
    intros. unfold st_locs, st_extend in *. rewrite indexr_skip. eauto. unfoldq. lia. }

  exists (vx::S1).
  exists (st_extend M1 vt qt ).
  exists (vref x).
  exists (qone (length S1)).
  split. 2: split. 3: split. 4: split. 5: split. 6: split.
  + (* expression evaluates *)
    destruct IW1 as [n1 IW1]. rename S into St.
    exists (S n1).
    intros. destruct n. lia.
    subst x. simpl. rewrite IW1. eauto. lia.
  + (* stty chain *)
    eapply stchain_chain''. eauto. 2: eapply SC1. eauto.
  + (* store typing *)
    (* lemma: storet_extend *)
    (* store_type (vx :: S1) (st_extend M1 x vt fr qt) *)
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
    rewrite val_type_def. split. 2: split. 3: split. 4: split.
    * eapply valt_closed. eauto.
    * rewrite plift_one. unfoldq. intuition.
    * split. simpl. intros ? ?. unfold qempty in H2. discriminate.
      intros ? ?. eapply WFE. unfoldq. intuition.
    * rewrite plift_one. intros ? ?. subst x.
      subst M2. unfold st_extend in *. unfold st_locs in *. unfoldq. simpl. lia.
    * exists vt, qt.
      split. 2: split. 3: split. 4: split.
      -- subst x M2. rewrite <-STL. unfold st_extend. rewrite indexr_head. eauto.
      -- subst qt. rewrite plift_vars_locs. unfoldq. intuition.
      -- subst qt. rewrite plift_vars_locs. unfoldq. intuition.
      -- (* get path *) intros. subst vt qt.
         eapply valt_store_change. eauto. eapply stchaindf_tighten. eauto. eauto. eapply valt_wf. eauto.
      -- (* puth path *) intros. subst vt qt.
         assert (psub (plift lsv) (st_locs M1)). { intros ? ?. eapply env_type_store_wf. eapply envt_store_extend. eauto. eauto. eauto. eauto. rewrite plift_vars_locs. eauto. }
         eapply valt_store_change. eauto. eapply stchaindf_tighten'. eauto. eauto. eauto.
  + (* qualifier *)
    intros ? ?.
    right. simpl. rewrite plift_one in H2. unfold pone in H2. subst x0.  unfold pstdiff, st_locs, st_extend. unfoldq.
    simpl. destruct ST1. destruct SC1 as (? & ? & ?). unfoldq. unfold st_locs in *. intros ?. assert (length M <= length M1). unfoldq.
    destruct (length M). lia.
    specialize (H5 n). lia. lia.
  + simpl. eauto.
Qed.

Lemma sem_get: forall t env p T fr q q1,
    sem_type env t (TRef T false q1) p fr q ->
    psub (plift (qfvs q1)) p ->
    sem_type env (tget t) T p false (plift (qfvs q1)).
Proof.
  intros. intros ? ? ? ? WFE ST.
  destruct (H S M E V WFE ST) as [S1 [M1 [vx [lsx [IW1 [SC1 [ST1 [SE1 [HVX HQX]]]]]]]]].
  rewrite val_type_def in HVX.
  destruct vx; try contradiction.
  destruct HVX as (? & ? & ? & HVX' & HVX).
  eapply ST1 in HVX' as HVX''.  2: { eauto. }
  destruct HVX as [vt [qt [IXM [QTM VTM]]]].
  destruct HVX'' as [vt' [qt' [v [ls' [IXM' [IXS [VTS [VLS VLS1]]]]]]]].
  rewrite IXM in IXM'.
  inversion IXM'. clear IXM'. subst vt' qt'.
  exists S1, M1, v, ls'. split. 2: split. 3: split. 4: split. 5: split. 6: split.
  + (* expression evaluates *)
    destruct IW1 as [n1 IW1]. rename S into St.
    exists (S n1).
    intros. destruct n. lia.
    simpl. rewrite IW1. rewrite IXS. eauto. lia.
  + (* st chain *)
    eauto.
  + (* store type *)
    eauto.
  + (* store effect *)
    eauto.
  + (* result well typed *)
    eapply VTM. eauto. eauto.
  + (* qualifier *)
    intros ? ?. left. eapply VLS in H4; eauto. eapply QTM in H4.
    destruct H4. 2: contradiction.
    eapply vars_locs_monotonic. 2: eauto. unfoldq. intuition.
  + simpl. eauto.
Qed.


Lemma sem_put: forall t1 t2 env p T fr1 q1 fr2 q2,
    sem_type env t1 (TRef T fr1 q1) p fr2 q2 ->
    sem_type env t2 T p false (plift (qfvs q1)) ->
    psub (plift (qfvs q1)) p ->
    sem_type env (tput t1 t2) TBool p false pempty.
Proof.
  intros. intros ? ? ? ? WFE ST.
  destruct (H S M E V WFE ST) as [S1 [M1 [vr [lsr [IW1 [SC1 [ST1 [SE1 [HVR [HQR HRVV]]]]]]]]]].
  eapply envt_store_extend in WFE as WFE1. 2: eauto. 2: eapply SC1.
  destruct (H0 S1 M1 E V WFE1 ST1) as [S2 [M2 [vx [lsx [IW2 [SC2 [ST2 [SE2 [HVX [HQX HXVV]]]]]]]]]].
  rewrite val_type_def in HVR. destruct vr; try contradiction.
  destruct HVR as (? & ? & ? & ? & vt & qt & ? & ? & ? & VT).
  destruct ST2 as (? & ST2).
  assert (st_locs M1 i) as B. { apply indexr_var_some' in H6. unfold st_locs. unfoldq; intuition. }
  destruct (ST2 i) as (vt' & qt' & vz & ? & IX & SI & ? & ?). eapply SC2. eauto.
  assert (indexr i M2 = indexr i M1) as R. { symmetry. eapply SC2. eauto. }
  rewrite R in IX. rewrite IX in H6. inversion H6. subst vt' qt'.
  exists (update S2 i vx), M2, (vbool true), qempty.
  split. 2: split. 3: split. 4: split. 5: split. 6: split.
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
    * exists vt, qt, vx, lsx. subst i.
      split. 2: split. 3: split. 4: split.
      -- rewrite R. eapply IX.
      -- rewrite update_indexr_hit. eauto. eapply indexr_var_some'. eauto.
      -- unfold val_qual in HQX.

         eapply VT.

         intros ? A. eapply HQX in A. destruct A. 2: contradiction.
         eapply H8. eapply vars_locs_monotonic. 2: eauto. unfoldq. intuition.

         eapply valt_store_change. eauto.
         eapply stchaindf_tighten'. eauto. eauto.
         intros ? VV. eapply HQX in VV. destruct VV. 2: contradiction.
         eapply env_type_store_wf. eauto. 2: eauto. unfoldq. intuition.
      -- intros ? VV. eapply HQX in VV. destruct VV. 2: contradiction.
         eapply H8. eapply vars_locs_monotonic. 2: eauto. unfoldq. intuition.
      -- eapply H11.
    * rewrite update_indexr_miss. 2: eauto.
      eapply ST2. eauto.
  + (* store preservation *)
    assert (length S = length M). destruct ST. eauto.
    intros ? ?. intros N ?.
    bdestruct (i =? l). {
    destruct (HQR l). subst i. eauto.
      destruct N.
      eapply vars_locs_monotonic. 2: eauto. unfoldq; intuition.

      destruct fr2. simpl in *. apply indexr_var_some' in H13.
      unfold st_locs in H15. unfoldq; intuition.
      simpl in H15. contradiction.
    }{
      rewrite update_indexr_miss.
      unfold store_effect in *.
      eapply SE1 in H13 as A; eauto.
      lia.
    }

  + (* result well typed *)
    rewrite val_type_def. unfoldq. intuition.
  + (* qualifier *)
    simpl. unfoldq. intuition.
  + simpl. eauto.
Qed.


(* ---- refs with self ref support (put operation is shared) --- *)

(* constructor for ref with self (use outer qualifier) *)
Lemma sem_ref2: forall t G p T q,
    sem_type G t T p false (plift q) ->
    psub (plift q) p ->
    sem_type G (tref t) (TRef T true (qempty, qempty)) p true (plift q).
Proof.
  intros. intros ? ? ? ? WFE ST.
  destruct (H S M E V WFE ST) as [S1 [M1 [vx [lsx [IW1 [SC1 [ST1 [SE1 [HVX [HQX HXVV]]]]]]]]]].
  remember (length S1) as x.
  remember (vars_locs_fix V q) as qt.
  remember (fun v => fun ls => val_type M1 E V v T ls) as vt.
  assert (st_chain M1 (st_extend M1 vt qt) (st_locs M1)). {
    split. 2: split.
    unfoldq. intuition.
    unfoldq. intuition.
    unfold st_locs, st_extend in *. unfoldq. simpl. intuition.
    intros. unfold st_locs, st_extend in *. rewrite indexr_skip. eauto. unfoldq. lia. }

  exists (vx::S1).
  exists (st_extend M1 vt qt ).
  exists (vref x).
  exists (qor (qone (length S1)) qt).
  split. 2: split. 3: split. 4: split. 5: split. 6: split.
  + (* expression evaluates *)
    destruct IW1 as [n1 IW1]. rename S into St.
    exists (S n1).
    intros. destruct n. lia.
    subst x. simpl. rewrite IW1. eauto. lia.
  + (* stty chain *)
    eapply stchain_chain''. eauto. 2: eapply SC1. eauto.
  + (* store typing *)
    (* lemma: storet_extend *)
    (* store_type (vx :: S1) (st_extend M1 x vt fr qt) *)
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
    rewrite val_type_def. split. 2: split. 3: split. 4: split.
    * eapply valt_closed. eauto.
    * rewrite plift_or, plift_one. unfoldq. intuition.
    * split. intros ? ?. inversion H2. intros ? ?. inversion H2.
    * rewrite plift_or, plift_one. intros ? [L | Q].
      -- inversion L. subst x0.
         subst M2. unfold st_extend in *. unfold st_locs in *. unfoldq. simpl. lia.
      -- subst qt. rewrite <-plift_vars_locs in Q.
         eapply env_type_store_wf. eapply envt_store_extend. eauto. eauto.
         eapply stchain_chain''. eauto. eauto. eapply SC1. 2: eauto. eauto.
    * exists vt, qt.
      split. 2: split. 3: split. 4: split.
      -- subst x M2. rewrite <-STL. unfold st_extend. rewrite indexr_head. eauto.
      -- subst qt. simpl. rewrite plift_empty, plift_or. right. right. eauto.
      -- subst qt. simpl. rewrite <-plift_vars_locs, plift_empty.
         eapply vars_locs_monotonic. unfoldq. intuition.
      -- (* get path *) intros. subst vt qt.
         eapply valt_store_change. eauto. eapply stchaindf_tighten. eauto. eauto. eapply valt_wf. eauto.
      -- (* puth path *) intros. subst vt qt.
         assert (psub (plift lsv) (st_locs M1)). { intros ? ?. eapply env_type_store_wf. eapply envt_store_extend. eauto. eauto. eauto. eauto. rewrite plift_vars_locs. eauto. }
         eapply valt_store_change. eauto. eapply stchaindf_tighten'. eauto. eauto. eauto.
  + (* qualifier *)
    intros ? Q. rewrite plift_or, plift_one in Q. destruct Q as [L | Q].
    * right. simpl. inversion L. subst x0.
      destruct ST1. destruct SC1 as (? & ? & ?). unfoldq. unfold st_locs in *. intros ?. assert (length M <= length M1). unfoldq.
      destruct (length M). lia.
      specialize (H5 n). lia. lia.
    * subst qt. left. rewrite <-plift_vars_locs in Q. eapply vars_locs_monotonic. 2: eauto. unfoldq. intuition.
  + simpl. eauto.
Qed.

(* get with outer qualifier *)
Lemma sem_get2: forall t env p T fr q,
    sem_type env t (TRef T true (qempty, qempty)) p fr q ->
    sem_type env (tget t) T p fr q.
Proof.
  intros. intros ? ? ? ? WFE ST.
  destruct (H S M E V WFE ST) as [S1 [M1 [vx [lsx [IW1 [SC1 [ST1 [SE1 [HVX [HQX HXVV]]]]]]]]]].
  rewrite val_type_def in HVX. destruct vx; try contradiction.
  destruct HVX as (? & ? & ? & HVX' & HVX).
  eapply ST1 in HVX' as HVX''.  2: { eauto. }
  destruct HVX as [vt [qt [IXM [QTM [QTM' VTM]]]]].
  destruct HVX'' as [vt' [qt' [v [ls' [IXM' [IXS [VTS [VLS VLS1]]]]]]]].
  rewrite IXM in IXM'.
  inversion IXM'. clear IXM'. subst vt' qt'.
  exists S1, M1, v, ls'. split. 2: split. 3: split. 4: split. 5: split. 6: split.
  + (* expression evaluates *)
    destruct IW1 as [n1 IW1]. rename S into St.
    exists (S n1).
    intros. destruct n. lia.
    simpl. rewrite IW1. rewrite IXS. eauto. lia.
  + (* st chain *)
    eauto.
  + (* store type *)
    eauto.
  + (* store effect *)
    eauto.
  + (* result well typed *)
    eapply VTM. eauto. eauto.
  + (* qualifier *)
    intros ? ?.
    eapply VLS in H3. eapply QTM in H3. simpl in H3. rewrite plift_empty in H3. destruct H3.
    * left. eapply vars_locs_monotonic. 2: eauto. unfoldq. intuition.
    * eapply HQX in H3. eauto.
  + simpl. eauto.
Qed.


Lemma plift_closed: forall (env: venv) q,
    closed_ql (length env) q = psub (plift q) (pdom env).
Proof.
  intros. unfoldq. unfold closed_ql, plift. eauto.
Qed.
Lemma plift_closed': forall (env: tenv) q,
    closed_ql (length env) q = psub (plift q) (pdom env).
Proof.
  intros. unfoldq. unfold closed_ql, plift. eauto.
Qed.
Lemma plift_closed'l: forall {a} (env: list a) q,
    closed_ql (length env) q = psub (plift q) (pdom env).
Proof.
  intros. unfoldq. unfold closed_ql, plift. eauto.
Qed.

Lemma qdiff_skip: forall q x y,
  y <> x ->
  qdiff q (qone x) y = q y.
Proof.
  intros. unfold qdiff, qone. rewrite <-Nat.eqb_neq in H. rewrite H.
  simpl. rewrite andb_true_r. reflexivity.
Qed.

Lemma sem_abs: forall env t T1 T2 p fn1 fr1 ff q1 fr2 q2 qf,
    let xx := qone (1 + length env) in
    let xf := qone (length env) in
    let qf' := qand p qf in
    let q1' := qand (qfvs q1) qf' in
    sem_type ((T1, fr1 || ff, (qor q1' (qif (fn1 || ff) xf)))::(TUnit, false, qf')::env) t
      (opent_rec 2 0 (length env) T2)
      (por (por (plift qf') (pone (length env))) (pone (1 + length env)))
      fr2
      (plift (qfvs (openq_rec 2 0 (length env) q2)))
      ->
    (ff = false -> psub (plift (qfvs q1)) (plift qf')) ->
    closed_ty 0 (length env) T1 ->
    closed_ty 2 (length env) T2 ->
    closed_ql2 0 (length env) q1 ->
    closed_ql2 2 (length env) q2 ->
    closed_ql (length env) qf ->
    bsub fn1 fr1 ->
    occurrences_bvs covariant_only T2 1 ->
    sem_type env (tabs t)
      (TFun T1 fn1 fr1 q1 T2 fr2 q2)
      (plift p) false (plift qf).
Proof.
  intros. rename H6 into Hfc1, H7 into Hfc2. intros ? ? ? ? WFE ST.
  exists S.
  exists M.
  exists (vabs E t).
  exists (vars_locs_fix V qf').
  split. 2: split. 3: split. 4: split. 5: split. 6: split.
  + (* term evaluates *)
    exists 1. intros. destruct n. lia. simpl. eauto.
  + eapply stchain_refl.
  + (* store typing *)
    eauto.
  + intros ? ? ? ?. auto.
  + (* result well typed *)
    rewrite val_type_def.

    assert (length env = length E) as LE. { symmetry. eapply WFE. }
    assert (pdom env = pdom E) as DE. { unfold pdom. rewrite LE. eauto. }
    assert (length env = length V) as LEV. { symmetry. eapply WFE. }
    assert (length V = length E) as LV. { symmetry. destruct WFE as (? & ? & ?). intuition. }

    rewrite <-plift_vars_locs. unfold q1', qf' in *. rewrite plift_and. rewrite LE in *. intuition; eauto.
    intros ? ?.  eapply env_type_store_wf with (q := (pand (plift p)(plift qf))) in WFE as WFE'.
    eapply WFE' in H6; eauto. unfoldq; intuition.

    (* INDUCTION *)
    destruct (H S' M' (vx::(vabs E t)::E) (lsx::(vars_locs_fix V (qand p qf))::V)) as [S2 [M2 [vy [lsy IHW1]]]].

    (* ENV_TYPE*) {
    rewrite <-plift_and in H9.

    assert (env_type M' (vabs E t :: E)
    ((TUnit, false, qand p qf) :: env)
    ((vars_locs_fix V (qand p qf)) :: V)
    (por (pand (plift p) (plift qf))
       (pone (length E)))). {
      eapply envt_extend_full; eauto.

      rewrite val_type_def. rewrite <-plift_vars_locs. rewrite plift_and. intros ? ?. eapply H6. eapply lls_z. eauto.
      unfoldq. intuition. rewrite plift_and. unfoldq. intuition.
      rewrite plift_and. intros ? (? & ?). eauto.
      intros. rewrite <-plift_vars_locs. intros ? ?. eauto.
      constructor. rewrite plift_closed, plift_and. unfoldq. intuition. }

    eapply envt_extend_full. eauto.

    eapply valt_extend1. eauto. eapply closedty_extend; eauto. eauto.

    rewrite plift_and. unfoldq. intuition.

    subst xf. rewrite plift_or, plift_if, plift_one, plift_and, plift_and.
    destruct (fn1 || ff).
    unfoldq. intuition. unfoldq. intuition.

    intros ? [? ?].
    unfold xf. rewrite plift_or, plift_and, plift_if, plift_one, LE, LEV.
    assert (vars_locs V (plift (qand p qf)) x). {
      destruct H11 as (x0 & [H11a | H11a] & H11b).
      exists x0. split. auto. eapply var_locs_shrink. eauto. rewrite <-LEV.
      apply H5. eapply proj2. rewrite plift_and in H11a. eauto.
      inversion H11a. subst x0. rewrite LEV in H11b. apply var_locs_head in H11b.
      rewrite plift_vars_locs. auto.
    }
    destruct (fn1 || ff) eqn:Heq. {
      exists (length V). split. unfoldq. intuition. eexists. split.
      apply indexr_head. rewrite <-plift_vars_locs. auto.
    }
    apply orb_false_iff in Heq as [? ?]. subst fn1 ff. specialize (H0 eq_refl).
    destruct (H9 x) as [F | [L | Q]]. eauto. {
      contradiction.
    } {
      destruct fr1; contradiction.
    } {
      eapply vars_locs_extend1 in Q.
      eapply vars_locs_monotonic. 2: eapply Q. unfoldq; intuition.
    }

    intros. apply orb_false_iff in H11 as [? ?]. subst fr1 ff. intros ? ?. eapply H9 in H11.
    destruct H11 as [ A | [B | C]]. {
      destruct fn1. 2: contradiction.
      simpl in A. subst xf. rewrite plift_or, plift_if, plift_one, plift_and.
      eexists (length V). split. simpl. unfoldq. intuition.
      eexists. rewrite indexr_head. split. eauto.
      rewrite <-plift_vars_locs. eauto.
    } {
      contradiction.
    } {
      rewrite plift_or, plift_if, plift_and. eapply vars_locs_extend1 in C.
      eapply vars_locs_monotonic; eauto. unfoldq. intuition.
    }

    eapply closedty_extend. eauto. simpl. eauto. simpl. lia.
    rewrite plift_closed. rewrite plift_or, plift_if, plift_and. unfoldq. intuition.
    simpl. eapply H3 in H11. lia.
    simpl. destruct (fn1 || ff). 2: contradiction. subst xf. rewrite plift_one in H12. unfoldq. lia.

    eauto.

    rewrite plift_and.
    split. eapply lls_closed'. eauto. eapply env_type_store_wf. eauto. intros ? ?. eauto.
    split. eapply lls_closed'. eauto. eapply env_type_store_wf. eauto. intros ? ?. eauto.
    intros. eauto.
    }

    eauto.

    destruct IHW1 as [? IHW1].
    exists S2, M2, vy, lsy. intuition; clear H17.

    (* store preservation *)
    intros ? ? PV ?. eapply H12.
    intros ?. eapply PV. destruct H17 as [? [? ?]].
    destruct H17. {
      destruct H17. {
        rewrite plift_and in H17.
        left. eexists. split; eauto.
        assert (x < length V). rewrite LV. eapply WFE. eapply H17.
        eapply var_locs_shrink; eauto.
        eapply var_locs_shrink; eauto. simpl. eauto.
      } {
        assert (x = length V). unfoldq. intuition.
        left. subst x. destruct H18. destruct H18.
        rewrite indexr_skip in H18. 2: {simpl. lia. }
        rewrite indexr_head in H18. inversion H18. subst x.
        rewrite <-plift_vars_locs, plift_and in H19.
        eauto.
      }
    } {
      unfold pone in H17. subst x. destruct H18 as [? [? ?]].
      replace (1 + length E) with (length (vars_locs_fix V (qand p qf) :: V)) in H17.
      2: { simpl. eauto. }
      rewrite indexr_head in H17. inversion H17. right. auto.
    }
    auto.

    (* vy < vf \/ vx *)
    apply valt_wf in H8(*HVX*). apply valt_wf in H14(*HVY*).
    rename H15 into HVY.

    intros ? ?.
    destruct (HVY x) as [HY_q | HY_fr]. eauto.
    - (* q *)
      destruct HY_q as (? & (? & ?) & ?).
      simpl in H17. rewrite qdiff_skip in H17. 2: lia.
      rewrite plift_or, plift_or, plift_if, plift_if, plift_one, plift_one in H17.
      remember (qbvs q2 0) as ar2. remember (qbvs q2 1) as fn2.
      bdestruct (x0 =? length (vabs E t::E)).
      * (* from arg *)
        subst x0.
        right. right. left.
        destruct ar2. { simpl in H18. destruct H18 as [? [? ?]].
        replace (Datatypes.S (length E)) with (length (vars_locs_fix V (qand p qf) :: V)) in H18.
        2: { simpl. eauto. }
        rewrite indexr_head in H18. inversion H18. subst. simpl. auto. } {
        destruct H17. destruct H17. { eapply H4 in H17. simpl in H17. unfoldq. lia. }
        destruct fn2. 2: contradiction. simpl in H17. unfoldq. lia.
        contradiction. }
      * (* from func *)
        bdestruct (x0 =? length E). {
        subst x0.
        right. left.
        destruct fn2. { destruct H18 as [? [? ?]]. rewrite LEV in H18.
        rewrite indexr_skip in H18. 2: { simpl.  lia. }
        rewrite indexr_head in H18. inversion H18. subst x0.
        rewrite <-plift_vars_locs, plift_and in H20. eauto. }
        destruct H17. destruct H17. { eapply H4 in H17. simpl in H17. unfoldq. lia. }
        contradiction.
        destruct ar2. 2: contradiction. unfoldq. lia. } {
        (* x0 < length E *)
          destruct H18 as [? [? ?]].
          rewrite indexr_skip in H18. 2: { simpl in *. lia. }
          rewrite indexr_skip in H18. 2: { simpl. lia. }
          left.
          destruct H17. destruct H17. exists x0. intuition. exists x1. intuition.
          destruct fn2; contradiction. destruct ar2; contradiction.
        }
    - (* fr *)
      right. right. right. eapply HY_fr.

  (* VAL_QUAL *)
  + intros ? ?. unfold qf' in H6. rewrite <-plift_vars_locs, plift_and in H6. left. eauto.
  + simpl. auto.
Qed.



Lemma valq_store_change: forall M M' M'' G H V v p fr q,
    env_type M' H G V p ->
    val_qual M M' V v p fr q ->
    st_chain_full M' M''  ->
    val_qual M M'' V v p fr q.
Proof.
  intros. intros ? ?.
  destruct (H1 x H3). {
    left. auto.
  } {
    right. destruct fr; try contradiction.
    simpl in *. unfold pstdiff, pdiff, st_locs in *. intuition.
  }
Qed.

Lemma openq_reorder: forall a qa b qb q,
  a <> b ->
  openq a qa (openq b qb q) = openq b qb (openq a qa q).
Proof.
  intros. unfold openq. simpl. repeat rewrite qdiff_skip; auto.
  apply pair_equal_spec; split; apply functional_extensionality; intros.
  unfold qdiff. rewrite <-andb_assoc, andb_comm with (b1 := negb _), andb_assoc. auto.
  unfold qor. rewrite <-orb_assoc, orb_comm with (b1 := qif _ _ _), orb_assoc. auto.
Qed.

Lemma opent_reorder: forall T a qa b qb,
  a <> b ->
  opent a qa (opent b qb T) = opent b qb (opent a qa T).
Proof.
  intros T. induction T; simpl; intros; auto.
  rewrite IHT; auto. rewrite openq_reorder; auto.
  rewrite IHT1; auto. rewrite IHT2. 2: lia.
  rewrite openq_reorder; auto. rewrite openq_reorder with (qa := qa). 2: lia.
  auto.
Qed.

Lemma openq_closed_eq: forall m n x q1 q2 q,
  closed_ql n q1 ->
  closed_ql n q2 ->
  closed_ql2 m n (openq x q1 q) <-> closed_ql2 m n (openq x q2 q).
Proof.
  intros. unfold openq, closed_ql2, closed_ql in *. simpl. intuition.
  - unfold qor in *. rewrite orb_true_iff in *. destruct H1.
    apply H3. rewrite orb_true_iff in *. intuition.
    destruct (qbvs q x); intuition.
  - unfold qor in *. rewrite orb_true_iff in *. destruct H1.
    apply H3. rewrite orb_true_iff in *. intuition.
    destruct (qbvs q x); intuition.
Qed.

Lemma opent_closed_eq: forall T m n x q1 q2,
  closed_ql n q1 ->
  closed_ql n q2 ->
  closed_ty m n (opent x q1 T) <-> closed_ty m n (opent x q2 T).
Proof.
  intro T. induction T; intros; simpl; try solve [intuition]; split; intros.
  - inversion H1; subst. constructor. eapply IHT. 3: eauto. 1-2: auto.
    eapply openq_closed_eq. 3: eauto. 1-2: auto.
  - inversion H1; subst. constructor. eapply IHT. 3: eauto. 1-2: auto.
    eapply openq_closed_eq. 3: eauto. 1-2: auto.
  - inversion H1; subst. constructor.
    eapply IHT1. 3: eauto. 1-2: auto. eapply IHT2. 3: eauto. 1-2: auto.
    eapply openq_closed_eq. 3: eauto. 1-2: auto.
    eapply openq_closed_eq. 3: eauto. 1-2: auto.
  - inversion H1; subst. constructor.
    eapply IHT1. 3: eauto. 1-2: auto. eapply IHT2. 3: eauto. 1-2: auto.
    eapply openq_closed_eq. 3: eauto. 1-2: auto.
    eapply openq_closed_eq. 3: eauto. 1-2: auto.
Qed.

Lemma valt_opent_change: forall T M H V v n q1 q2 ls,
  length H = length V ->
  closed_ql (length H) q1 ->
  closed_ql (length H) q2 ->
  vars_locs V (plift q1) = vars_locs V (plift q2) ->
  val_type M H V v (opent n q1 T) ls <->
  val_type M H V v (opent n q2 T) ls.
Proof.
  intros T. remember (ty_size T) as n. assert (Hge: n >= ty_size T). lia.
  clear Heqn. generalize dependent T. induction n; intros.
  all: destruct T; simpl in *; try lia; try solve [intuition].
  all: repeat rewrite val_type_def; destruct v; try solve [intuition].
  - simpl. repeat rewrite plift_or, plift_if.
    repeat rewrite vars_locs_or, vars_locs_if. repeat rewrite H3.
    setoid_rewrite IHn with (q1 := q1); eauto. 2: lia.
    rewrite openq_closed_eq with (q1 := q1); eauto.
    rewrite opent_closed_eq with (q1 := q1); eauto.
    intuition.
  - simpl. repeat rewrite plift_or, plift_if.
    repeat rewrite vars_locs_or, vars_locs_if. repeat rewrite H3.
    repeat rewrite variance_bvs_closed.
    repeat setoid_rewrite opent_reorder with (a := 1).
    repeat setoid_rewrite opent_reorder with (a := 0). 2-9: lia.
    setoid_rewrite IHn with (n := n0) (q1 := q1); eauto. 2: lia.
    setoid_rewrite IHn with (n := n0 + 2) (q1 := q1) (q2 := q2).
    rewrite openq_closed_eq with (q1 := q1); eauto.
    rewrite openq_closed_eq with (q1 := q1); eauto.
    rewrite opent_closed_eq with (q1 := q1); eauto.
    rewrite opent_closed_eq with (q1 := q1); eauto.
    intuition.
    repeat rewrite opent_preserves_ty_size. lia. simpl. lia.
    eapply closedq_extend; eauto. simpl. lia.
    eapply closedq_extend; eauto. simpl. lia.
    rewrite <-(app_nil_l V). repeat rewrite app_comm_cons.
    repeat rewrite vars_locs_extend. auto.
    rewrite H0 in H2. intros ? ?. apply H2. auto.
    rewrite H0 in H1. intros ? ?. apply H1. auto.
Qed.

Lemma notfree_bvs_closed: forall T x q,
  occurrences_bvs not_free T x ->
  opent x q T = T.
Proof.
  assert (Q: forall q x q', ~ plift (qbvs q) x -> openq x q' q = q). {
    intros. destruct q. unfold openq. simpl in *. unfold plift in H.
    apply pair_equal_spec; split; apply functional_extensionality; intros.
    - unfold qdiff, qone. destruct (q x0) eqn:?; auto. simpl.
      apply negb_true_iff. apply Nat.eqb_neq. intro; subst. contradiction.
    - unfold qor, qif. apply not_true_iff_false in H. rewrite H.
      apply orb_false_r.
  }
  intros T. induction T; intros; simpl in *; auto.
  - intuition. rewrite IHT; auto. replace (openq x q0 q) with q; auto.
    rewrite Q; auto.
  - intuition. rewrite IHT1, IHT2; auto. repeat rewrite Q; auto.
    intuition. discriminate. intuition. discriminate.
Qed.

Lemma sem_app: forall env f t T1 T2 p frf qf frx qx fn1 fr1 q1 fr2 q2 qx',
    sem_type env f (TFun T1 fn1 fr1 q1 T2 fr2 q2) (plift p) frf (plift qf) ->
    sem_type env t T1 (plift p) frx (plift qx) ->
    (if fn1 then
       True (* no longer applicable given valt_grow *)
       (* if fr1 then
         True
       else
         (* this case is tricky: *)
         (* qx < qf won't guarantee vx < vf!!! *)
         (* need f = tvar x0 and precisely qx = x0 *)
         (* OR f = tabs <-- needed for syntactic soundness *)
         (frx = false /\ (exists x0, f = tvar x0 /\ psub (plift qx) (pone x0))) \/
         (frx = false /\ (exists p0 t, f = tabs p0 t /\ psub (plift qx) (plift p0))) \/
         (frx = false /\ psub (plift qx) (plift (qfvs q1))) *)
     else
       if fr1 then
         sem_qtp2 env frx (pand (plift p) (plift qx)) frx (plift qx') /\
         psub (plift qx') (plift p) /\
         psub (pand (vars_trans' env qf)
                    (vars_trans' env (qdiff qx' (qfvs q1))))
              pempty
         (* psub (pand
                 (plift (vars_trans_fix env qf))
                 (plift (vars_trans_fix env qx)))
           (plift (qfvs q1)) *)
       else
         sem_qtp2 env frx (plift qx) fr1 (plift (qfvs q1))) ->

    psub (plift (qfvs q1)) (plift p) ->   (* this is necessary (so far!) *)
    psub (plift (qfvs q2)) (plift p) ->   (* this is necessary (so far!) *)
    (frf = true -> occurrences_bvs not_free T2 1) ->
    (frx = true -> occurrences_bvs not_free T2 0) ->
    sem_type env (tapp f t) (opent 0 (qand p qx) (opent 1 (qand p qf) T2)) (plift p)
      (qbvs q2 1 && frf || qbvs q2 0 && frx || fr2)
      (plift (qfvs (openq 0 qx (openq 1 qf q2)))).
Proof.
  intros. simpl. rewrite qdiff_skip. 2: lia.
  rewrite plift_or, plift_or, plift_if, plift_if.
  intros S0 ? ? ? WFE ST.
  rename H into IHW1. rename H0 into IHW2.
  destruct (IHW1 S0 M E V WFE ST) as [S1 [M1 [vf [lsf [IW1 [SC1 [ST1 [SE1 [HVF [HQF HFVV]]]]]]]]]]. auto. auto.
  assert (env_type M1 E env V (plift p)) as WFE1. { eapply envt_store_extend; eauto. }
  destruct (IHW2 S1 M1 E V WFE1 ST1) as [S2 [M2 [vx [lsx [IW2 [SC2 [ST2 [SE2 [HVX [HQX HXVV]]]]]]]]]].

  assert (telescope env). eapply envt_telescope. eauto.
  apply wf_env_type in WFE as WFEc.
  destruct WFEc as (HLE & HLV & HPE & HPV).
  eassert (WFEp: _). exact WFE. destruct WFEp as (_ & _ & WFEp & _).
  rewrite HPE in WFEp.

  (* vf is a function value: it can eval its body *)
  destruct vf; try solve [rewrite val_type_def in HVF; contradiction].

  apply valt_wf in HVF as WFQF. apply valt_wf in HVX as WFQX.

  rewrite val_type_def in HVF. intuition.
  rename H13 into HVF.

  pose (if frx then lsx else vars_locs_fix V (qand p qx)) as lsx'.
  apply valt_grow with (ls1 := lsx') in HVX.
  2: {
    unfold lsx'. unfold val_qual in HQX. destruct frx.
    unfoldq. intuition. rewrite <-plift_vars_locs, plift_and.
    intros ? HL. apply HQX in HL as [HL | HL]. auto. contradiction.
  }
  2: {
    unfold lsx'. destruct frx. auto. rewrite <-plift_vars_locs, plift_and.
    intros ? HL. destruct SC2 as (_ & SC2 & _).
    apply SC2. eapply env_type_store_wf in HL; eauto. unfoldq. intuition.
  }
  2: auto with *.
  assert (HQX': val_qual M1 M2 V lsx' (plift p) frx (plift qx)). {
    unfold val_qual in *. unfold lsx'. destruct frx. auto.
    rewrite <-plift_vars_locs, plift_and. unfoldq. intuition.
  }
  clear HQX. rename HQX' into HQX.

  destruct (HVF S2 M2 vx lsx') as [S3 [M3 [vy [lsy [IW3 [SC3 [ST3 [SE3 HVY]]]]]]]]; eauto.

  eapply stchaindf_tighten. eauto. eauto. eauto.

  (* SEPARATION / OVERLAP *)
  rename H1 into HSEP.
  intros ? ?.

  destruct fn1. { (* arg may overlap with function? *)
    rewrite H10; auto. destruct (lsf x) eqn:HL.
    unfoldq. intuition. apply not_true_iff_false in HL. unfoldq. intuition.
  } {
    assert (WFE': env_type' M E env V (plift p)).
    { unfold env_type'; unfold env_type in *. intuition. }
    right. destruct fr1. {
      (* not fn, fr *)
      destruct (lsf x) eqn:?. { (* check to see if we're aliasing function *)
        destruct HSEP as [HSEP1 [HSEP3 HSEP2]]. specialize (HSEP1 _ _ _ _ WFE').
        right. apply HQX in H1. destruct H1.
        2: { apply WFQF in Heqb. destruct frx; contradiction. }
        apply HQF in Heqb. destruct Heqb.
        2: { eapply env_type_store_wf in H1. 2: apply WFE. exfalso.
          destruct frf; contradiction. clear. unfoldq; intuition. }
        edestruct val_locs_decide. rewrite plift_vars_locs. eauto.
        exfalso. rewrite <-plift_vars_locs in H13.
        destruct WFE as (_ & _ & _ & _ & WFE).
        destruct HSEP1 as (_ & _ & _ & HSEP1 & _).
        assert (vars_locs V (pdiff (plift qx') (plift (qfvs q1))) x). {
          apply HSEP1 in H1. destruct H1. exists x0. unfold pdiff. intuition.
          apply H13. exists x0. intuition.
        }
        eassert (VL: pand _ _ x). split. exact H12. exact H14.
        eassert (VTsub: _). 2: apply WFE in VL. 2: {
          apply vars_locs_monotonic with (q' := pempty) in VL.
          rewrite vars_locs_empty in VL. inversion VL.
          intros ? HL. apply HSEP2. generalize dependent x0. exact VTsub.
        } {
          intros ? [HL1 HL2]. unfold vars_trans'. rewrite plift_vt, plift_vt, plift_diff; auto.
          split; auto. eapply vt_mono. 2: exact HL1. unfoldq; intuition.
        }
        1-2: unfoldq; intuition.
        intros ? HL. apply VTsub in HL. exfalso. eapply HSEP2. eauto.
      }{
        left. apply not_true_iff_false in Heqb. eauto.
      }
    } {
      (* not fn, not fr *)
      right. specialize (HSEP _ _ _ _ WFE').
      destruct HSEP as (? & _ & _ & HSEP & _). destruct frx. discriminate H12; auto.
      apply HSEP. apply HQX in H1 as [H1 | H1]. eapply vars_locs_monotonic. 2: exact H1.
      unfoldq. intuition. inversion H1.
    }
  }

  (* EVALUATION *)
  exists S3, M3, vy, lsy. split. 2: split. 3: split. 4: split. 5: split. 6: split.
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
    assert (length M <= length M1) as L1. eapply st_mono in SC1. auto.
    assert (st_chain M M2 (st_locs M)) as SCC. eapply stchain_chain''; eauto. intros ? ?. unfold st_locs in *. unfoldq; intuition.
    assert (st_chain M M1 (vars_locs V (plift p) )) as A.  {
      eapply stchain_tighten; eauto. eapply env_type_store_wf in WFE; eauto. unfoldq; intuition.
    }
    assert (st_chain M M2 (vars_locs V (plift p) )) as B. {
      eapply stchain_tighten; eauto. eapply env_type_store_deep_wf in WFE; eauto.
      intros ? ?. unfoldq; intuition.
    }
    assert (st_chain M M2 (vars_locs V (plift p))) as C. {
     eapply stchain_tighten in SCC; eauto. eapply env_type_store_wf in WFE; eauto.
     intros ? ?. unfoldq; intuition.
    }
    assert (length M1 <= length M2) as L2. eapply st_mono in SC2. auto.
    intros ? ? PV. intros IS. rewrite SE3; eauto. intros ?. eapply PV.
    assert (l0 < length M). apply indexr_var_some' in IS. destruct ST; intuition.
    destruct H12 as [? | ?].
    destruct (HQF l0). auto.
    eapply vars_locs_monotonic. 2: eapply H14.  intros ? ?. unfoldq; intuition.
    destruct frf; simpl in H11. unfoldq; intuition. contradiction.

    destruct (HQX l0). auto.
    eapply vars_locs_monotonic. 2: eapply H14.  intros ? ?. unfoldq; intuition.
    destruct frx; simpl in H12. unfoldq; intuition. contradiction.

  (* VAL_TYPE *)
  + simpl in HVY. destruct HVY as [HVY HQY].
    pose (if frf then lsf else vars_locs_fix V (qand p qf)) as lsf'.
    eapply valt_extend with (H' := [vx; vabs l t0]) (V' := [lsx'; lsf']).
    lia. simpl. auto.
    repeat apply opent_closed. auto.
    rewrite plift_closed, plift_and. rewrite HPE. unfoldq; intuition.
    rewrite plift_closed, plift_and. rewrite HPE. unfoldq; intuition.
    simpl. replace (lsx' :: lsf :: V) with ([lsx'] ++ lsf :: V) in HVY. 2: reflexivity.
    eapply valt_lenv_change with (lsx' := lsf') in HVY.
    2: simpl; lia.
    2: {
      rewrite HLV, <-HLE. apply variance_fvs_closed. lia.
      eapply variance_open; eauto.
    }
    2: {
      simpl. unfold lsf'. destruct frf. unfoldq. intuition.
      unfold val_qual in HQF. rewrite <-plift_vars_locs, plift_and.
      intros ? HL. apply HQF in HL. unfoldq. intuition.
    }
    simpl in HVY.
    assert (notfree_rw: forall T x q1 q2, occurrences_bvs not_free T x ->
      opent x q1 T = opent x q2 T).
    { intros. repeat rewrite notfree_bvs_closed; auto. }
    eassert (HVY': val_type M3 (vx::vabs l t0::E) (lsx'::lsf'::V) vy _ lsy).
    destruct frx. {
      rewrite notfree_rw with (q2 := qand p qx) in HVY. eauto.
      rewrite variance_bvs_closed. auto. lia.
    } {
      rewrite valt_opent_change with (q2 := qand p qx) in HVY. auto.
      simpl. lia.
      simpl. unfold closed_ql, qone. setoid_rewrite Nat.eqb_eq. auto with *.
      apply @closedq_extend with (m := length E). rewrite plift_closed, plift_and.
      rewrite HPE. unfoldq. intuition. simpl. lia.
      unfold lsx'. rewrite plift_one. replace (S (length E)) with (length (lsf' :: V)).
      rewrite vars_locs_head, <-plift_vars_locs, plift_and. 2: simpl; lia.
      rewrite <-(app_nil_l V) at 3. repeat rewrite app_comm_cons.
      rewrite vars_locs_extend; auto. rewrite HPV. unfoldq. intuition.
    }
    clear HVY. rename HVY' into HVY. destruct frf. {
      erewrite notfree_rw with (x := 1) in HVY. eauto. auto.
    } {
      rewrite opent_reorder in HVY. 2: lia.
      rewrite valt_opent_change with (q2 := qand p qf) in HVY.
      rewrite opent_reorder. auto. lia.
      simpl. lia. unfold closed_ql, qone. simpl.
      setoid_rewrite Nat.eqb_eq. auto with *.
      apply (@closedq_extend (length E)). rewrite plift_closed, plift_and, HPE.
      unfoldq. intuition. simpl. lia.
      unfold lsf' in *. rewrite plift_one, vars_locs_tighten, HLE, <-HLV.
      rewrite vars_locs_head, <-plift_vars_locs, plift_and.
      rewrite <-(app_nil_l V) at 3. repeat rewrite app_comm_cons.
      rewrite vars_locs_extend. auto. rewrite HPV. unfoldq. intuition.
      rewrite HLE, <-HLV. unfoldq. simpl. auto with *.
    }

  (* VAL_QUAL *)
  + destruct HVY as [HVY HQY].
    remember (vabs l t0) as vf.
    assert (val_qual M M3 V lsf (plift p) frf (plift qf)) as HQF'. {
      eapply valq_store_change. eauto. eauto. eapply stchain_chain''. eauto. eauto. eapply SC2.  }
    assert (val_qual M1 M3 V lsx' (plift p) frx (plift qx)) as HQX'. {
      eapply valq_store_change. eapply envt_store_extend; eauto. eauto. eauto. }

    intros ? ?.
    remember (qbvs q2 0) as ar2. remember (qbvs q2 1) as fn2.
    destruct (HQY x) as [HY_q | [HY_f | [HY_x | HY_fr]]].
    repeat rewrite app_length. intuition.
    * (* q2, and part of function *)
      destruct HY_q as [? ?].
      left. eapply vars_locs_monotonic. 2: { exists x0. eauto. }
      unfoldq. intuition.
    * (* part of function *)
      destruct fn2. 2: contradiction.
      destruct (HQF' x) as [HF_q | HF_fr]. eauto.
      -- (* q *) left. eapply vars_locs_monotonic. 2: eapply HF_q. unfoldq. intuition.
      -- (* fr *)
         destruct frf. 2: contradiction.
         right. simpl. eauto.
    * (* part of arg *)
      destruct ar2. 2: contradiction.
      destruct (HQX' x) as [HX_q | HX_fr]. eauto.
      -- (* q *) left. eapply vars_locs_monotonic. 2: eapply HX_q. unfoldq. intuition.
      -- (* fr *)
         destruct frx. 2: contradiction.
         right. destruct (fn2 && frf); simpl.
         intros ?. eapply HX_fr. eapply SC1. eauto.
         intros ?. eapply HX_fr. eapply SC1. eauto.
    * (* fresh *)
      destruct fr2. 2: contradiction.
      right. destruct (fn2 && frf || ar2 && frx); simpl.
      intros ?. eapply HY_fr. eapply SC2. eapply SC1. eauto.
      intros ?. eapply HY_fr. eapply SC2. eapply SC1. eauto.
  + simpl. eauto.
Qed.

Lemma sem_ascript: forall G e T p fr q,
  sem_type G e T p fr (plift q) ->
  psub (plift q) p ->
  sem_type G (tas e T fr q) T p fr (plift q).
Proof.
  intros. unfold sem_type, exp_type. intros.
  destruct (H _ _ _ _ H1 H2) as (S' & M' & v & ls & ?).
  exists S', M', v, ls. intuition.
  - unfold tevaln in *. destruct H4 as (n & ?). exists (Datatypes.S n). intros.
    destruct n0. lia. simpl. rewrite H4. auto. lia.
  - simpl. auto.
Qed.

(* alternative subtyping *)

Definition sem_stp2 G gr T1 T2 :=
  forall S M E V,
    env_type' M E G V gr ->
    store_type S M ->
    forall v ls1,
      val_type M E V v T1 ls1 ->
      exists gl,
        val_type M E V v T2 (qor ls1 gl) /\
        psub (plift gl) (vars_locs V gr).

Lemma sem_sub_qtp2_stp2: forall G p gr T1 fr1 q1 T2 fr2 q2,
  sem_stp2 G gr T1 T2 ->
  sem_qtp2 G fr1 (por q1 gr) fr2 q2 ->
  psub q2 p ->
  psub gr p ->
  sem_sqtp G p T1 fr1 q1 T2 fr2 q2.
Proof.
  intros. rename H into STP, H0 into QTP, H1 into PQ.
  unfold sem_sqtp, sem_type. intros. rename H0 into WFE, H1 into HST.
  specialize (H _ _ _ _ WFE HST). unfold exp_type in *.
  destruct H as (S' & M' & v & ls1 & HEV & HSC & HST' & HSE & HVT & HVQ & HEQ).
  specialize (envt_store_extend _ _ _ _ _ _ _ WFE HST HSC) as WFE'0.
  assert (WFE': env_type' M' E G V p).
  unfold env_type'. unfold env_type in WFE'0. intuition.
  destruct (QTP _ _ _ _ WFE') as (HFR & ? & ? & HQT & HQTp).
  apply envt_tighten' with (p' := gr) in WFE'. 2: auto.
  destruct (STP _ _ _ _ WFE' HST' _ _ HVT) as (gl & HVT' & HVQ'). clear STP.
  exists S', M', v, (qor ls1 gl). intuition.
  - unfold val_qual in *. rewrite plift_or.
    intros L [HL | HL]. apply HVQ in HL as [HL | HL].
    * left. eapply vars_locs_monotonic. 2: apply HQT. unfoldq. intuition.
      eapply vars_locs_monotonic. 2: apply HL. unfoldq. intuition.
    * right. clear - HFR HL. unfoldq. unfold bsub in *.
      destruct fr1. specialize (HFR eq_refl). subst. auto. contradiction.
    * left. apply HVQ' in HL. eapply vars_locs_monotonic. 2: apply HQT. unfoldq. intuition.
      eapply vars_locs_monotonic. 2: apply HL. unfoldq. intuition.
  - unfold exp_qual in *. destruct t; auto; rewrite plift_or; clear - HEQ.
    unfoldq. intuition.
Qed.

Lemma sem_stp2_bool: forall env,
    sem_stp2 env pempty TBool TBool.
Proof.
  intros. intros S M E V WFE HST v ls1 HVT.
  exists qempty. rewrite <-qor_empty_id_r, plift_empty.
  unfoldq. intuition.
Qed.

Lemma sem_stp2_unit: forall env,
    sem_stp2 env pempty TUnit TUnit.
Proof.
  intros. intros S M E V WFE HST v ls1 HVT.
  exists qempty. rewrite <-qor_empty_id_r, plift_empty.
  unfoldq. intuition.
Qed.

Lemma sem_stp2_ref: forall env T1 fr1 q1 T2 fr2 q2,
    sem_stp2 env pempty T1 T2 ->
    sem_stp2 env pempty T2 T1 ->
    sem_qtp2 env fr1 (plift (qfvs q1)) fr2 (plift (qfvs q2)) ->
    sem_qtp2 env fr2 (plift (qfvs q2)) fr1 (plift (qfvs q1)) ->
    closed_ty 0 (length env) T2 ->
    closed_ql2 0 (length env) q2 ->
    sem_stp2 env pempty (TRef T1 fr1 q1) (TRef T2 fr2 q2).
Proof.
  intros. intros S M E V WFE HST v ls VV.
  exists qempty. rewrite <-qor_empty_id_r, plift_empty.
  split. 2: { unfoldq. intuition. }

  destruct v; rewrite val_type_def in *; try contradiction.
  destruct VV as (? & ? & ? & ? & vt & qt & IX & QT & QT' & VT1).
  split. 2: split. 3: split. 4: split.
  - replace (length E) with (length env). auto. apply wf_env_type' in WFE. intuition.
  - auto.
  - replace (length E) with (length env). auto. apply wf_env_type' in WFE. intuition.
  - eauto.
  - exists vt, qt. split. 2: split. 3: split.
    + eauto.
    + intros ? H10. eapply QT in H10. destruct H10.
      left. eapply H1. eauto. eauto.
      right. destruct (H1 _ _ _ _ WFE) as (H1' & _).
      destruct fr1. 2: contradiction. rewrite H1'; auto.
    + intros ? ?. eapply QT'. eapply H2. eauto. eauto.
    + intros. assert (HE: forall q, psub (plift q) (vars_locs V pempty) -> qempty = q). {
        clear. intros. rewrite vars_locs_empty in H. apply functional_extensionality.
        intros x. specialize (H x). destruct (q x) eqn:?; intuition. } split.
      intros HVV. apply VT1 in HVV. 2: assumption.
      edestruct H as (gl & H' & H'1). eauto. eauto. eauto.
      apply HE in H'1. subst. rewrite qor_empty_id_r. auto.
      intros HVV. apply VT1. auto.
      edestruct H0 as (gl & H' & H'1). eauto. eauto. eauto.
      apply HE in H'1. subst. rewrite qor_empty_id_r. auto.
Qed.

Lemma sem_stp2_ref_grow: forall env T fr1 q1,
  True ->
  closed_ty 0 (length env) T ->
  closed_ql2 0 (length env) q1 ->
  sem_stp2 env (plift (qfvs q1)) (TRef T fr1 q1) (TRef T true (qempty, qempty)).
Proof.
  intros. intros S M E V WFE HST v ls VV.
  destruct v; rewrite val_type_def in *; try contradiction.
  destruct VV as (? & HI & HQ1 & HLS & vt & qt & HIM & HQT & HVQ1 & HVT).
  exists (vars_locs_fix V (qfvs q1)). rewrite val_type_def. split. split. auto.
  split. rewrite plift_or. left. auto.
  split. split; simpl. intros ? ?. inversion H3.
         intros ? ?.  inversion H3.
  split. rewrite plift_or. intros ? [HX | HX]. auto.
         rewrite <-plift_vars_locs in HX. apply HVQ1 in HX.
         assert (i < length M). eapply indexr_var_some'; eauto.
         assert (HMI: st_locs M i). auto.
         apply HST in HMI as (vt' & qt' & ? & ? & HIM' & _ & _ & _ & HQTI).
         rewrite HIM in HIM'. inversion HIM'. subst. apply HQTI in HX.
         unfold pnat, st_locs, pdom in *. lia.
  exists vt, qt. split. auto. simpl.
  rewrite plift_empty, plift_or, <-plift_vars_locs, vars_locs_empty.
  split. intros ? HX. right. simpl. apply HQT in HX as [HX | HX].
         right. auto. left. destruct fr1. auto. contradiction.
  split. intro. contradiction. auto.
  rewrite <-plift_vars_locs. apply vars_locs_monotonic. clear - H. unfoldq. intuition.
Qed.

Lemma sem_stp2_trans: forall env T1 T2 T3 gr1 gr2,
  sem_stp2 env gr1 T1 T2 ->
  sem_stp2 env gr2 T2 T3 ->
  True ->
  sem_stp2 env (por gr1 gr2) T1 T3.
Proof.
  intros. unfold sem_stp2 in *. intros S M E V WFE HST ? ? HV1.
  apply envt_tighten' with (p' := gr1) in WFE as WFE'1. 2: unfoldq; intuition.
  destruct (H _ _ _ _ WFE'1 HST _ _ HV1) as (gr1' & HV2 & HG1).
  apply envt_tighten' with (p' := gr2) in WFE as WFE'2. 2: unfoldq; intuition.
  destruct (H0 _ _ _ _ WFE'2 HST _ _ HV2) as (gr2' & HV3 & HG2).
  exists (qor gr1' gr2'). split.
  - rewrite <-qor_associative. auto.
  - rewrite plift_or. intros ? [HX | HX].
    apply HG1 in HX. eapply vars_locs_monotonic. 2: apply HX. unfoldq. intuition.
    apply HG2 in HX. eapply vars_locs_monotonic. 2: apply HX. unfoldq. intuition.
Qed.

Lemma sem_stp2_fun_arg: forall env T1 fn1 fr1 q1 q1' T2 fr2 q2,
  closed_ql2 0 (length env) q1' ->
  bsub fn1 fr1 ->
  sem_stp2 env pempty (TFun T1 true true q1  T2 fr2 q2)
                      (TFun T1 fn1  fr1  q1' T2 fr2 q2).
Proof.
  intros. intros S M E V WFE HST v lsf VV.
  apply wf_env_type' in WFE as WFEc. destruct WFEc as (HLE & HLV & HPE & HPV).
  destruct v; rewrite val_type_def in *; try contradiction.
  exists qempty. rewrite val_type_def.
  rewrite HLE, <-qor_empty_id_r in *.
  intuition.
  - eapply H9 in H11; eauto. clear. intros L HL.
    destruct (lsf L) eqn:Heq. left. auto.
    apply not_true_iff_false in Heq. right. left. auto.
  - unfoldq. intuition.
Qed.

Lemma vars_locs_openq: forall v V a b l,
  psub a (pdom V) ->
  l = length V ->
  vars_locs (v::V) (por a (pif b (pone l))) = por (vars_locs V a) (pif b (plift v)).
Proof.
  intros. rewrite vars_locs_or, vars_locs_if, H0, vars_locs_head.
  rewrite vars_locs_tighten; auto.
Qed.

Lemma vars_locs_openq': forall v V a b l,
  psub (plift a) (pdom V) ->
  l = length V ->
  vars_locs (v::V) (plift (qor a (qif b (qone l)))) = por (vars_locs V (plift a)) (pif b (plift v)).
Proof.
  intros. rewrite plift_or, plift_if, plift_one. auto using vars_locs_openq.
Qed.

Lemma vars_locs_openq'_or: forall v V a b c l,
  psub (plift a) (pdom V) ->
  psub (plift c) (pdom V) ->
  l = length V ->
  vars_locs (v::V) (plift (qor a (qif b (qor (qone l) c)))) =
  por (vars_locs V (plift a)) (pif b (por (plift v) (vars_locs V (plift c)))).
Proof.
  intros. rewrite plift_or, plift_if, plift_or, plift_one. subst l.
  rewrite vars_locs_or, vars_locs_if, vars_locs_or, vars_locs_head.
  rewrite vars_locs_tighten, vars_locs_tighten; auto.
Qed.

Lemma psub_or_dist_l: forall a b c,
  psub a c -> psub b c ->
  psub (por a b) c.
Proof.
  intros. unfoldq. intuition.
Qed.

Lemma psub_if_assume_l: forall b x y,
  psub x y ->
  psub (pif b x) y.
Proof.
  intros. unfoldq. destruct b. intuition. intuition.
Qed.

Lemma psub_pdom_tighten_r: forall {X} a (b: X) (L: list X),
  psub a (pdom L) ->
  psub a (pdom (b::L)).
Proof.
  intros. unfoldq. simpl. intuition.
Qed.

Lemma sem_stp2_fun_grow: forall env gr T1 fn1 fr1 q1
                                       T2 fr2 q2 q2',
  let qF := qone (length env) in
  sem_qtp2 ((T1, fr1, qor (qfvs q1) (qif fn1 qF))::(TUnit, true, qempty)::env)
      false                 (plift (qfvs (openq_rec 2 0 (length env) q2)))
      false (por (plift gr) (plift (qfvs (openq_rec 2 0 (length env) q2')))) ->
  True ->
  closed_ql2 2 (length env) q2' ->
  qbvs q2' 1 = true -> (* self ref required *)
  sem_stp2 env (plift gr)
      (TFun T1 fn1 fr1 q1 T2 fr2 q2)
      (TFun T1 fn1 fr1 q1 T2 fr2 q2').
Proof.
  intros. simpl in H. rewrite qdiff_skip, qdiff_skip in H. 2,3: lia.
  intros S M E V WFE HST v lsf VV.
  apply wf_env_type' in WFE as WFEc. destruct WFEc as (HLE & HLV & HPE & HPV).
  eassert (WFEc: _). exact WFE. destruct WFEc as (_ & _ & HGE & _). rewrite HPE in HGE.
  destruct v; rewrite val_type_def in *; try contradiction.
  exists (vars_locs_fix V gr). rewrite val_type_def. rewrite HLE in *.
  rewrite plift_or, <-plift_vars_locs. intuition.
  - intros L [HL | HL]. unfoldq; intuition. eapply env_type_store_wf' in HL.
    eauto. eauto. unfoldq; intuition.
  - unfold closed_ql2 in *.
    eassert (WFE2: env_type' M' (vx::vabs l t::E) _ (lsx::(qor lsf (vars_locs_fix V gr))::V) _).
    2: specialize (H _ _ _ _ WFE2). {
      eapply envt_extend_stub'. eapply envt_extend_stub'. eauto.
      rewrite val_type_def, plift_or, <-plift_vars_locs.
      apply psub_or_dist_l. eauto. eapply env_type_store_wf'; eauto. intro; auto.
      intro; discriminate. constructor. intros ? HL; inversion HL.
      eapply stchaindf_tighten; eauto. apply stchain_refl.
      eapply env_type_store_wf'; eauto. intros ? HL; exact HL. intros ? HL; exact HL.
      rewrite valt_extend1. auto. lia. rewrite HLE. auto.
      intro; subst. unfold qF.
      rewrite vars_locs_openq', plift_or, <-plift_vars_locs.
      intros ? HL. destruct (H14 _ HL) as [HL' | [HL' | HL']].
      right. auto. inversion HL'. left. auto.
      rewrite HPV. intuition. lia.
      eapply closedty_extend; eauto. simpl. lia.
      rewrite plift_closed, plift_or, plift_if.
      apply psub_or_dist_l. apply psub_pdom_tighten_r. rewrite HPE. intuition.
      apply psub_if_assume_l. unfold qF. rewrite plift_one. unfoldq. simpl. intuition.
      replace (pone (length E)) with (pif true (pone (length E))). 2: reflexivity.
      rewrite vars_locs_openq, plift_or, <-plift_vars_locs. eapply stchaind_tighten; eauto.
      unfoldq. intuition. rewrite HPV. intuition. lia.
      intros ? HL; exact HL.
    }
    rewrite H2 in *. remember (qbvs q2 1) as fn2.
    remember (qbvs q2 0) as ar2. remember (qbvs q2' 0) as ar2'.
    eapply H11 in H13. 3: eauto.
    * destruct H13 as (S'' & M'' & vy & lsy & HEV & HCF & HST'' & HSE' & HVY & HQY).
      exists S'', M'', vy, lsy. intuition.
      eapply se_sub. eauto. unfoldq; intuition.
      pose (qor lsf (vars_locs_fix V gr)) as lsf'.
      replace (lsx :: _ :: V) with ([lsx] ++ lsf' :: V) at 1. 2: simpl; auto.
      eapply valt_lenv_change. simpl. lia. simpl. eauto. simpl.
      apply variance_fvs_closed. lia. rewrite HLV. eapply variance_open; eauto.
      simpl. unfold lsf'. rewrite plift_or. unfoldq. intuition. rename H19 into HQ.
      rewrite vars_locs_openq', vars_locs_openq', plift_or, <-plift_vars_locs in HQ.
      rewrite vars_locs_or, vars_locs_openq', vars_locs_openq', plift_or, <-plift_vars_locs in HQ.
      rewrite vars_locs_tighten, vars_locs_tighten in HQ.
      2-11: simpl; try lia; try rewrite plift_or, plift_if, plift_one.
      5,7: apply psub_or_dist_l. 3,5,7: apply psub_pdom_tighten_r.
      7,8: apply psub_if_assume_l; unfoldq; simpl; lia.
      2-7: rewrite HPV; intuition.
      intros L HL. apply HQY in HL. destruct (fr2 && negb ((qdom M') L)) eqn:HL'.
      + unfold qdom in HL'. right. right. right.
        rewrite andb_true_iff, negb_true_iff, Nat.ltb_nlt in HL'.
        destruct HL'  as [? HL']. subst fr2. auto.
      + eassert (HL'': _ L). 2: apply HQ in HL''. destruct HL as [HL | [HL | [HL | HL]]].
        unfoldq. intuition. destruct fn2. unfoldq. intuition. inversion HL.
        unfoldq. intuition. destruct fr2. simpl in HL'. rewrite negb_false_iff in HL'.
        unfold qdom in HL'. rewrite Nat.ltb_lt in HL'. contradiction. inversion HL.
        unfoldq. intuition.
    * eapply stchaind_tighten. eauto. unfoldq; intuition.
    * destruct fn1. rewrite H8 in *; auto.
      intros L HL. destruct (lsf L) eqn:Heq. unfoldq; intuition.
      apply not_true_iff_false in Heq. unfoldq; intuition.
      intros L HL. apply H14 in HL as [HL | [HL | HL]]. inversion HL.
      destruct fr1; unfoldq; intuition. unfoldq; intuition.
  - unfoldq; intuition.
Qed.

Lemma valt_hybrid_change: forall T M H V' lsx V q v ls,
  length V + length V' + 1 = length H ->
  closed_ql (length V) q ->
  closed_ty (S (length V')) (length V) T ->
  val_type M H (V'++qor lsx (vars_locs_fix V q)::V) v
    (opent_rec (length V') 0 (S (length V)) (opent (length V')      (qone (length V))    T)) ls
  <->
  val_type M H (V'++    lsx                    ::V) v
    (opent_rec (length V') 0 (S (length V)) (opent (length V') (qor (qone (length V)) q) T)) ls.
Proof.
  intros T. induction T; intros; simpl.
  all: rewrite opent_rec_iff; symmetry; try rewrite opent_rec_iff; symmetry; simpl.
  all: repeat rewrite val_type_def; destruct v; try solve [intuition].
  - inversion H2; subst.
    setoid_rewrite <-closedq_openq_rec'. setoid_rewrite <-closedty_opent_rec'.
    setoid_rewrite Nat.add_0_r. all: try lia.
    setoid_rewrite <-opent_closed'. setoid_rewrite <-openq_closed'.
    all: try (rewrite plift_closed'l; try rewrite plift_or; try apply psub_or_dist_l).
    all: try (rewrite plift_one; unfoldq; intuition).
    all: try (intros ? Q0; specialize (H1 _ Q0); unfoldq; lia).
    setoid_rewrite IHT; auto. destruct H9.
    setoid_rewrite vars_locs_openq_rec with (fn' := 0).
    simpl. setoid_rewrite vars_locs_openq'. setoid_rewrite vars_locs_openq'_or.
    setoid_rewrite plift_or. setoid_rewrite <-plift_vars_locs.
    all: try solve [simpl; try lia; auto].
    all: try (rewrite plift_closed'l; simpl; rewrite plift_or; apply psub_or_dist_l).
    all: try (rewrite plift_if; apply psub_if_assume_l).
    all: try (rewrite plift_or; apply psub_or_dist_l).
    all: try (rewrite plift_one; unfoldq; simpl; intuition).
    all: try (apply psub_pdom_tighten_r; unfoldq; intuition).
    intuition.
  - inversion H2; subst.
    setoid_rewrite variance_bvs_closed_rec. setoid_rewrite variance_bvs_closed.
    setoid_rewrite <-closedq_openq_rec'. setoid_rewrite <-closedty_opent_rec'.
    setoid_rewrite Nat.add_0_r. all: try lia.
    setoid_rewrite <-opent_closed'. setoid_rewrite <-openq_closed'.
    all: try (rewrite plift_closed'l; try rewrite plift_or; try apply psub_or_dist_l).
    all: try (rewrite plift_one; unfoldq; intuition).
    all: try (intros ? Q0; specialize (H1 _ Q0); unfoldq; lia).
    setoid_rewrite IHT1; auto.
    assert (Hfold: forall T,
      opent_rec 2 0 (length H) (opent_rec (length V') 2 (S (length V)) T)
      = opent_rec (length V' + 2) 0 (S (length V)) T). {
      intros. rewrite Nat.add_comm, <-H0.
      replace (length V + length V' + 1) with (length V' + S (length V)).
      auto. lia.
    }
    setoid_rewrite Hfold.
    assert (Hv2: forall M H v1 v2 v3 v q ls,
      val_type M H (v1::v2::V'++v3::V) v
        (opent_rec (length V'+2) 0 (S (length V)) (opent (length V' + 2) q T2)) ls
      = val_type M H ((v1::v2::V')++v3::V) v
        (opent_rec (length (v1::v2::V')) 0 (S (length V)) (opent (length (v1::v2::V')) q T2)) ls).
    { intros. rewrite Nat.add_comm. simpl. auto. }
    setoid_rewrite Hv2. setoid_rewrite IHT2; auto. 2: simpl; lia.
    2: { eapply closedty_extend; eauto. simpl. lia. }
    destruct H14, H15.
    setoid_rewrite vars_locs_openq_rec with (fn' := 0). simpl.
    setoid_rewrite vars_locs_openq'. setoid_rewrite vars_locs_openq'_or.
    setoid_rewrite plift_or. setoid_rewrite <-plift_vars_locs.
    assert (HB: forall a b q x,
      qbvs (openq_rec (length V') 2 a (openq (length V' + 2) b q)) x
      = qdiff (qbvs q) (qdiff (qnat (length V' + 3)) (qnat 2)) x).
    { intros. rewrite openq_rec_qbvs. unfold openq. simpl. unfold qdiff, qone, qnat.
      destruct (qbvs q2 x). 2: simpl; auto. simpl.
      bdestruct (x <? 2). simpl. repeat rewrite andb_false_r. simpl.
        rewrite andb_true_r, negb_true_iff, Nat.eqb_neq. lia.
      simpl. repeat rewrite andb_true_r. rewrite <-negb_orb.
      bdestruct (x <? length V' + 3); simpl.
      apply negb_false_iff. bdestruct (x =? length V' + 2); simpl. auto.
      apply Nat.ltb_lt. lia. apply negb_true_iff. apply orb_false_iff; split.
      apply Nat.eqb_neq. lia. apply Nat.ltb_nlt. lia.
    }
    setoid_rewrite HB. intuition.
    all: try solve [simpl; lia]; auto.
    all: rewrite plift_closed'l; unfold openq; simpl.
    all: rewrite plift_or; apply psub_or_dist_l.
    all: try (rewrite plift_if; apply psub_if_assume_l).
    all: try (rewrite plift_or; apply psub_or_dist_l).
    all: try (rewrite plift_one; unfoldq; simpl; lia).
    all: apply psub_pdom_tighten_r; auto.
Qed.

Lemma sem_stp2_fun: forall env T1a fn1a fr1a q1a T2a fr2a q2a
                               T1b fn1b fr1b q1b T2b fr2b q2b
                               gr1 gr2,
  let pF := pone (length env) in
  let qF := qone (length env) in
  let pX := pone (length env + 1) in
  sem_stp2 env (plift gr1) T1b T1a ->
  sem_qtp2 env fr1b (por (plift (qfvs q1b)) (plift gr1))
               fr1a      (plift (qfvs q1a)) ->
  sem_stp2 ((T1b, fr1b, qor (qfvs q1b) (qif fn1b qF))::(TUnit, true, qempty)::env) (plift gr2)
      (opent 0 (qor (qone (S (length env))) gr1) (opent 1 (qone (length env)) T2a))
      (opent_rec 2 0 (length env) T2b) ->
  sem_qtp2 ((T1b, fr1b, qor (qfvs q1b) (qif fn1b qF))::(TUnit, true, qempty)::env)
      fr2a (por (plift (qfvs (openq 0 (qor (qone (S (length env))) gr1) (openq 1 (qone (length env)) q2a)))) (plift gr2))
      fr2b      (plift (qfvs (openq_rec 2 0 (length env) q2b))) ->
  closed_ty 0 (length env) T1b ->
  closed_ql2 0 (length env) q1b ->
  closed_ty 2 (length env) T2b ->
  closed_ql2 2 (length env) q2b ->
  bsub fn1b fn1a ->
  True ->
  True ->
  occurrences_bvs covariant_only T2b 1 ->
  bsub fn1b fr1b ->
  True ->
  sem_stp2 env (por (plift gr1) (pdiff (pdiff (plift gr2) pF) pX))
      (TFun T1a fn1a fr1a q1a T2a fr2a q2a)
      (TFun T1b fn1b fr1b q1b T2b fr2b q2b).
Proof.
  intros. rename H into HS1, H0 into HQ1, H1 into HS2, H2 into HQ2,
    H7 into HFN1, H11 into HG1.
  intros S M E V WFE HST vf lsf HVF. destruct vf; rewrite val_type_def in *; try contradiction.
  apply wf_env_type' in WFE as WFEc. destruct WFEc as (HLE & HLV & HPE & HPV).
  specialize WFE as WFE'. destruct WFE' as (_ & _ & WFEp & _). rewrite HPE in WFEp.
  pose (qdiff (qdiff gr2 (qone (length env))) (qone (length env + 1))) as gr2'.
  exists (vars_locs_fix V (qor gr1 gr2')). rewrite val_type_def.
  unfold gr2', pF, pX in *. rewrite plift_or, <-plift_vars_locs, HLE, plift_or in *.
  repeat rewrite plift_diff, plift_one in *. intuition.
  intros ? [HL | HL]; auto. eapply env_type_store_wf'; eauto. intro; auto. 2: intro; auto.
  rename H11 into HG2, H14 into HMM, H15 into HVF, H16 into HST', H17 into HVX, H18 into HLX.
  eassert (WFE': env_type' M' E env V _). {
    eapply envt_store_change'. exact WFE.
    eapply stchaind_tighten. exact HMM.
    unfoldq. intuition.
  }
  destruct (HQ1 _ _ _ _ WFE') as (HF1 & ? & ? & HQ1a & ?).
  eassert (WFE's: _). 2: destruct (HS1 _ _ _ _ WFE's HST' _ _ HVX) as (lsx' & HS1a & HS1b).
  { eapply envt_tighten'. eauto. unfoldq. intuition. }
  pose (qor lsx (vars_locs_fix V gr1)) as lsx''.
  eapply valt_grow with (ls1 := lsx'') in HS1a.
  2: { unfold lsx''; repeat rewrite plift_or; rewrite <-plift_vars_locs. unfoldq; intuition. }
  2: {
    unfold lsx''. rewrite plift_or, <-plift_vars_locs. intros ? [HL | HL].
    apply valt_wf in HVX. auto. eapply env_type_store_wf'. 3: exact HL. eauto.
    intro; auto.
  }
  2: lia. clear WFE's. unfold closed_ql2 in *.
  eapply HVF in HS1a. 2: { eapply stchaind_tighten. eauto. unfoldq. intuition. } 2: eauto.
  destruct HS1a as (S'' & M'' & vy & lsy & HEV & HMM' & HST'' & HSE & HVY & HLY).
  pose (qor lsf (vars_locs_fix V (qor gr1 gr2'))) as lsf'.
  unfold lsx'' in HVY. simpl in HVY.
  rewrite <-app_nil_l with (l := _ :: _ :: V) in HVY.
  assert (HVY': val_type M'' (vx::vabs l t::E) ([] ++ qor lsx (vars_locs_fix (lsf::V) gr1)::lsf::V) vy
    (opent_rec (@length ql []) 0 (Datatypes.S (length (lsf::V)))
      (opent (@length ql []) (qone (length (lsf::V)))
      (opent 1 (qone (length env)) T2a))) lsy).
  replace (vars_locs_fix (lsf::V) gr1) with (vars_locs_fix V gr1).
  simpl. rewrite HLV. auto. {
    apply functional_extensionality. intros. simpl.
    replace (gr1 (length V)) with false. simpl. auto.
    symmetry. rewrite HLV. apply not_true_iff_false. intro.
    eapply or_introl in H16. apply WFEp in H16. unfoldq; intuition.
  }
  rewrite valt_hybrid_change in HVY'.
  simpl in HVY'. rewrite HLV in HVY'.
  clear HVY. rename HVY' into HVY.
  replace (_::_::V) with ([lsx] ++ lsf :: V) in HVY. 2: simpl; auto.
  2: simpl; lia. 2: { rewrite plift_closed'l. apply psub_pdom_tighten_r.
    rewrite HPV. unfoldq; intuition. }
  2: { apply opent_closed. eapply closedty_extend; eauto. simpl. lia.
    rewrite plift_closed'l, plift_one, <-HLV. unfoldq; simpl; intuition. }
  eapply valt_lenv_change with (lsx' := lsf') (f := covariant_only) in HVY.
  2: simpl; lia. 2: { apply variance_fvs_closed'. lia. apply not_true_iff_false.
    rewrite HLV. intro. eapply or_introl in H16. apply WFEp in H16. unfoldq. intuition.
    rewrite HLV. eapply variance_open; eauto. }
  2: { unfold lsf'. rewrite plift_or. unfoldq; intuition. }
  eassert (WFE'': env_type' M'' (vx::vabs l t::E) _ (lsx::lsf'::V) (plift gr2)).
  2: specialize (HQ2 _ _ _ _ WFE''). {
    unfold lsf', gr2'. eapply envt_store_change'. eapply envt_tighten'.
    eapply envt_extend_stub'. eapply envt_extend_stub'. exact WFE.
    rewrite val_type_def, plift_or, <-plift_vars_locs, plift_or.
    repeat rewrite plift_diff, plift_one.
    intros ? [HL | HL]. eauto. eapply env_type_store_wf'; eauto. intro; auto.
    intro; discriminate. constructor. apply closedq_empty.
    eapply stchaindf_tighten; eauto. apply stchain_refl.
    eapply env_type_store_wf'; eauto. intro; auto.
    intros ? HL; exact HL.
    rewrite valt_extend1; eauto. lia. rewrite HLE. auto.
    intro; subst. unfold qF.
    rewrite vars_locs_openq', plift_or, <-plift_vars_locs, plift_or.
    repeat rewrite plift_diff, plift_one.
    intros ? HL. specialize (HLX _ HL). clear - HLX. unfoldq. intuition.
    rewrite HPV. intuition. lia. eapply closedty_extend; eauto. simpl. lia.
    unfold qF. rewrite plift_closed, plift_or, plift_if, plift_one.
    apply psub_or_dist_l. apply psub_pdom_tighten_r. rewrite HPE. intuition.
    apply psub_if_assume_l. unfoldq. simpl. lia.
    replace (pone (length E)) with (pif true (pone (length E))). 2: reflexivity.
    rewrite vars_locs_openq, plift_or, <-plift_vars_locs, plift_or.
    repeat rewrite plift_diff, plift_one.
    eapply stchaind_tighten; eauto. clear. unfoldq. intuition.
    rewrite HPV. auto. lia.
    intros ? HL; exact HL. simpl. rewrite HLE. clear. intros ? HL.
    bdestruct (x =? length env). unfoldq. intuition.
    bdestruct (x =? length env + 1). unfoldq. intuition.
    unfoldq. intuition.
    replace (qdiff (qdiff gr2 _) _) with gr2'. 2: auto.
    replace (plift gr2) with (por (plift gr2')
      (por (pif (gr2 (length V)) (pone (length V)))
           (pif (gr2 (length V + 1)) (pone (length V + 1))))).
    2: { unfold gr2'. repeat rewrite plift_diff, plift_one. rewrite HLV.
      apply functional_extensionality; intros. apply propositional_extensionality.
      split; intros HL. destruct HL as [HL | [HL | HL]].
      unfoldq. intuition.
      destruct (gr2 (length env)) eqn:HL2; inversion HL. auto.
      destruct (gr2 (length env + 1)) eqn:HL2; inversion HL. auto.
      bdestruct (x =? length env). subst. rewrite HL. unfoldq. intuition.
      bdestruct (x =? length env + 1). subst. rewrite HL. unfoldq. intuition.
      unfoldq. intuition.
    }
    eapply stchaindf_tighten; eauto. repeat rewrite vars_locs_or. repeat rewrite vars_locs_if.
    rewrite vars_locs_tighten, vars_locs_tighten, vars_locs_tighten.
    replace (length V + 1) with (length (qor lsf (vars_locs_fix V (qor gr1 gr2')) :: V)).
    rewrite vars_locs_head, vars_locs_head, plift_or, <-plift_vars_locs, plift_or.
    2: simpl; rewrite Nat.add_comm; auto.
    2: unfoldq; simpl; intuition.
    3: apply psub_pdom_tighten_r.
    2,3: rewrite HPV; unfold gr2'; repeat rewrite plift_diff, plift_one; unfoldq; intuition.
    repeat apply psub_or_dist_l; try apply psub_if_assume_l.
    2: apply psub_or_dist_l.
    1,3: eapply env_type_store_wf'; eauto; unfold gr2'; repeat rewrite plift_diff, plift_one;
      unfoldq; intuition.
    destruct HMM as (_ & HMM & _). intros ? HL. apply HMM. constructor.
    unfoldq. intuition.
    eapply valt_wf; eauto.
  }
  replace (pdiff (pdiff (plift gr2) (pone (length env))) (pone (length env + 1)))
    with (plift gr2') in *.
  2: { unfold gr2'. repeat rewrite plift_diff, plift_one. auto. }
  destruct (HS2 _ _ _ _ WFE'' HST'' _ _ HVY) as (lsy' & HS2a & HS2b).
  destruct HQ2 as (HF2 & ? & ? & HQ2a & ?). simpl in HQ2a.
  assert (tmp: forall a b c d,
      qor a (qif b (qor (qone c) d)) = qor (qor a (qif b (qone c))) (qif b d)). {
    intros. apply functional_extensionality; intros. unfold qor, qif.
    destruct (a x); simpl; auto. destruct b; simpl; auto.
  }
  rewrite qdiff_skip, qdiff_skip in HQ2a. 2,3: lia.
  rewrite tmp in HQ2a. clear tmp.
  rewrite vars_locs_or, plift_or, vars_locs_or, plift_if, vars_locs_if in HQ2a.
  rewrite vars_locs_openq', vars_locs_openq', vars_locs_openq', vars_locs_openq' in HQ2a.
  rewrite vars_locs_tighten, vars_locs_tighten in HQ2a.
  2-11: simpl; try lia.
  2-7: try rewrite plift_or, plift_if; repeat apply psub_or_dist_l;
    try apply psub_if_assume_l.
  2-9: try (rewrite plift_one; unfoldq; simpl; lia).
  2-7: try apply psub_pdom_tighten_r; rewrite HPV; unfoldq; intuition.
  exists S'', M'', vy, (qor lsy lsy'). intuition.
  - eapply se_sub. eauto. unfold lsx''. rewrite plift_or, <-plift_vars_locs.
    intros ? [HL | [HL | HL]].
    unfoldq. intuition. unfoldq. intuition. left. right.
    eapply vars_locs_monotonic. 2: eauto. unfoldq. intuition.
  - rewrite plift_or. unfold lsx'' in HLY. rewrite plift_or, <-plift_vars_locs in HLY.
    clear - HLY HS2b HQ2a HF2. unfold lsf' in HQ2a.
    rewrite plift_or, <-plift_vars_locs, plift_or in HQ2a.
    rewrite vars_locs_or in *.
    intros x HL. destruct (fr2a && negb (qdom M' x)) eqn:Heq.
    * apply andb_true_iff in Heq as [? Heq].
      subst fr2a. rewrite HF2. 2: auto.
      rewrite negb_true_iff in Heq. unfold qdom in Heq. rewrite Nat.ltb_nlt in Heq.
      unfoldq. intuition.
    * eassert (HM: _ x). 2: apply HQ2a in HM.
      destruct HL as [HL | HL]. apply HLY in HL. destruct HL as [HL | [HL | [HL | HL]]].
      + unfoldq. intuition.
      + destruct (qbvs q2a 1). unfoldq. intuition. inversion HL.
      + destruct (qbvs q2a 0). destruct HL. unfoldq. intuition. unfoldq. intuition.
        inversion HL.
      + destruct fr2a; try contradiction. simpl in Heq. exfalso. apply HL.
        apply negb_false_iff in Heq. unfold qdom in Heq. apply Nat.ltb_lt. auto.
      + unfoldq. intuition.
      + unfoldq. intuition.
  - unfold lsx''. rewrite plift_or, <-plift_vars_locs. clear - HLX HQ1a HF1 HG2 HFN1.
    intros ? [HL | HL]. apply HLX in HL as [HL | [HL | HL]].
    * destruct fn1b. rewrite HFN1 in *; auto. rewrite HG2 in *; auto.
      destruct (lsf x) eqn:Hx. unfoldq. intuition.
      apply not_true_iff_false in Hx. unfoldq. intuition. inversion HL.
    * destruct fr1b. rewrite HF1 in *; auto. unfoldq. intuition.
      inversion HL.
    * eassert (H: _). 2: specialize (HQ1a x H). rewrite vars_locs_or.
      unfoldq. intuition. unfoldq. intuition.
    * eassert (H: _). 2: specialize (HQ1a x H). rewrite vars_locs_or.
      unfoldq. intuition. unfoldq. intuition.
Qed.


Ltac plift_any :=
  repeat (try rewrite plift_closed' in *;
          try rewrite plift_or in *;
          try rewrite plift_and in *;
          try rewrite plift_if in *;
          try rewrite plift_diff in *;
          try rewrite plift_one in *;
          try rewrite plift_empty in *).

Ltac crush :=
  plift_any; unfoldq; intuition.

Ltac closed :=
  try (constructor);
  try (eapply closedty_extend; constructor);
  try (eapply closedq_extend; [eauto|subst;simpl; unfold ql; lia]);
  try (eapply closedty_extend; [eauto|subst;simpl; unfold ql; lia]).

(* subtyping incl qualifiers: G^p |- T1^q1 <: T2^q2 *)

Inductive qtp : tenv -> bool -> ql -> bool -> ql -> Prop :=
| q_sub: forall env fr1 q1 fr2 q2,
    psub (plift q1) (plift q2) ->
    bsub fr1 fr2 ->
    closed_ql (length env) q2 ->
    qtp env fr1 q1 fr2 q2
| q_var: forall G x Tx qx q1 fr1,
    plift q1 x ->
    indexr x G = Some (Tx, false, qx) ->
    closed_ql (length G) q1 ->
    closed_ql (length G) qx ->
    qtp G fr1 q1 fr1 (qor (qdiff q1 (qone x)) qx)
| q_trans: forall G q1 fr1 q2 fr2 q3 fr3,
    qtp G fr1 q1 fr2 q2 ->
    qtp G fr2 q2 fr3 q3 ->
    qtp G fr1 q1 fr3 q3
.

Lemma qtp_closed: forall G fr1 q1 fr2 q2,
  qtp G fr1 q1 fr2 q2 ->
  bsub fr1 fr2 /\ closed_ql (length G) q1 /\ closed_ql (length G) q2.
Proof.
intros. induction H.
- intuition. intros ? ?. apply H1. apply H. auto.
- intuition. intro; auto. intros ? ?. unfold qor, qdiff in H3.
  rewrite orb_true_iff, andb_true_iff in H3. intuition.
- intuition. intro; auto.
Qed.

Lemma q_cong: forall G fr1a q1a fr1b q1b fr2a q2a fr2b q2b,
  qtp G fr1a q1a fr1b q1b ->
  qtp G fr2a q2a fr2b q2b ->
  qtp G (fr1a || fr2a) (qor q1a q2a) (fr1b || fr2b) (qor q1b q2b).
Proof.
  intros. generalize dependent q2a. generalize dependent q2b.
  generalize dependent fr2a. generalize dependent fr2b.
  induction H; intros.
  - generalize dependent q1. generalize dependent q2.
    generalize dependent fr1. generalize dependent fr2. induction H2; intros.
    * apply q_sub; crush. unfold bsub in *. repeat rewrite orb_true_iff. intuition.
    * apply q_trans with (q2 := qor q2 q1) (fr2 := fr2 || fr1).
      + apply q_sub; crush. unfold bsub in *. repeat rewrite orb_true_iff. intuition.
      + eapply q_trans. eapply q_var; eauto; crush. apply q_sub; crush.
        intro; auto.
    * eapply q_trans. eapply IHqtp1; eauto. apply IHqtp2; auto; intro; auto.
  - generalize dependent q1. generalize dependent x. generalize dependent Tx. generalize dependent qx.
    generalize dependent fr1. induction H3; intros.
    * apply q_trans with (q2 := qor q0 q2) (fr2 := fr0 || fr2). apply q_sub; crush.
      unfold bsub in *; repeat rewrite orb_true_iff. intuition.
      eapply q_trans. eapply q_var; eauto; crush. apply q_sub; crush. intro; auto.
    * bdestruct (x =? x0); subst. rewrite H0 in H4. inversion H4; subst. clear H4.
      eapply q_trans. eapply q_var; eauto; crush. apply q_sub; crush. intro; auto.
      eapply q_trans. eapply q_var with (x := x0); eauto; crush.
      eapply q_trans. eapply q_var with (x := x); eauto.
      crush. crush. apply q_sub; crush. intro; auto.
    * eapply q_trans. eapply IHqtp1. 2: eauto. 1-3: auto. apply qtp_closed in H3_ as H4c.
      apply q_trans with (q2 := qor (qor q0 qx) q2) (fr2 := fr0 || fr2).
      apply q_sub; crush. intro; auto.
      eapply q_trans. eapply IHqtp2. 2: eauto. auto. crush. crush.
      apply qtp_closed in H3_0 as H3_0c.
      apply q_sub; crush. intro; auto.
  - eapply q_trans. eapply IHqtp1; eauto. apply IHqtp2.
    apply qtp_closed in H1 as H1c.
    apply q_sub; crush. intro; auto.
Qed.

(* There are extra closedness conditions added to separate bvars/fvars*)
(* Those can be omitted in paper presentations (marked as _omitted_) *)
Inductive stp : tenv -> ql -> ty -> ty -> Prop :=
| s_bool: forall env,
    stp env qempty TBool TBool
| s_unit: forall env,
    stp env qempty TUnit TUnit
| s_ref: forall env T1 fr1 q1 T2 fr2 q2,
    stp env qempty T1 T2 ->
    stp env qempty T2 T1 ->
    qtp env fr1 (qfvs q1) fr2 (qfvs q2) ->
    qtp env fr2 (qfvs q2) fr1 (qfvs q1) ->
     (* omitted *) closed_ql2 0 (length env) q1 ->
     (* omitted *) closed_ql2 0 (length env) q2 ->
    stp env qempty (TRef T1 fr1 q1) (TRef T2 fr2 q2)
| s_ref_grow: forall env T fr1 q1,
    closed_ty 0 (length env) (TRef T fr1 q1) ->
    stp env (qfvs q1) (TRef T fr1 q1) (TRef T true (qempty, qempty))
| s_trans: forall env gr1 gr2 T1 T2 T3,
    stp env gr1 T1 T2 ->
    stp env gr2 T2 T3 ->
    stp env (qor gr1 gr2) T1 T3
| s_fun_arg: forall env T1 fn1 fr1 q1 q1' T2 fr2 q2,
    closed_ty 0 (length env) (TFun T1 true true q1 T2 fr2 q2) ->
    closed_ql2 0 (length env) q1' ->
    bsub fn1 fr1 ->
    stp env qempty (TFun T1 true true q1  T2 fr2 q2)
                   (TFun T1 fn1  fr1  q1' T2 fr2 q2)
| s_fun_grow: forall env gr T1 fn1 fr1 q1 T2 fr2 q2 q2',
    qtp ((T1, fr1, qor (qfvs q1) (qif fn1 (qone (length env))))::(TUnit, true, qempty)::env)
      false         (qfvs (openq_rec 2 0 (length env) q2))
      false (qor gr (qfvs (openq_rec 2 0 (length env) q2'))) ->
    closed_ql (length env) gr ->
    closed_ty 0 (length env) (TFun T1 fn1 fr1 q1 T2 fr2 q2) ->
     (* omitted *) closed_ql2 2 (length env) q2' ->
    qbvs q2' 1 = true ->
    stp env gr (TFun T1 fn1 fr1 q1 T2 fr2 q2)
               (TFun T1 fn1 fr1 q1 T2 fr2 q2')
| s_fun: forall env T1a fn1a fr1a q1a T2a fr2a q2a
                    T1b fn1b fr1b q1b T2b fr2b q2b gr1 gr2,
    stp env gr1 T1b T1a ->
    qtp env fr1b (qor (qfvs q1b) gr1) fr1a (qfvs q1a) ->
    bsub fn1b fn1a ->
    stp ((T1b, fr1b, qor (qfvs q1b) (qif fn1b (qone (length env))))::(TUnit, true, qempty)::env) gr2
      (opent 0 (qor (qone (S (length env))) gr1) (opent 1 (qone (length env)) T2a))
      (opent_rec 2 0 (length env) T2b) ->
    qtp ((T1b, fr1b, qor (qfvs q1b) (qif fn1b (qone (length env))))::(TUnit, true, qempty)::env)
      fr2a (qor (qfvs (openq 0 (qor (qone (S (length env))) gr1) (openq 1 (qone (length env)) q2a))) gr2)
      fr2b      (qfvs (openq_rec 2 0 (length env) q2b)) ->
     (* omitted *) closed_ql2 0 (length env) q1a ->
     (* omitted *) closed_ql2 0 (length env) q1b ->
     (* omitted *) closed_ty 2 (length env) T2a ->
     (* omitted *) closed_ty 2 (length env) T2b ->
     (* omitted *) closed_ql2 2 (length env) q2a ->
     (* omitted *) closed_ql2 2 (length env) q2b ->
    occurrences_bvs covariant_only T2b 1 ->
    bsub fn1b fr1b ->
    stp env (qor gr1 (qdiff (qdiff gr2 (qone (length env))) (qone (length env + 1))))
            (TFun T1a fn1a fr1a q1a T2a fr2a q2a)
            (TFun T1b fn1b fr1b q1b T2b fr2b q2b).

Fixpoint wf_abs (T: ty): Prop :=
  match T with
  | TFun T1 fn1 fr1 q1 T2 fr2 q2 =>
      wf_abs T1 /\ wf_abs T2 /\
      bsub fn1 fr1 /\ occurrences_bvs covariant_only T2 1
  | TRef T fr q => wf_abs T
  | _ => True
  end.

Lemma opent_preserves_wf_abs: forall T n q,
  wf_abs T ->
  wf_abs (opent n q T).
Proof.
  intros T. induction T; intros; simpl; auto.
  simpl in H. intuition. rewrite variance_bvs_closed; auto. lia.
Qed.

Lemma s_refl: forall T G,
  closed_ty 0 (length G) T ->
  wf_abs T ->
  stp G qempty T T.
Proof.
  intros T. remember (ty_size T) as n.
  assert (n >= ty_size T). lia. clear Heqn.
  generalize dependent T. induction n; intros.
  all: destruct T; simpl in H; try lia; try solve [constructor].
  - inversion H0; subst. unfold closed_ql2 in H8. simpl in H1.
    constructor; auto.
    apply IHn; auto. lia. apply IHn; auto. lia.
    apply q_sub. crush. intro; auto. intuition.
    apply q_sub. crush. intro; auto. intuition.
  - inversion H0; subst. unfold closed_ql2 in H14, H13. simpl in H1.
    destruct H1 as (? & ? & ? & ?).
    eassert (Hq: qempty = _). 2: rewrite Hq; apply s_fun; eauto.
    all: unfold bsub; auto.
    2: apply IHn; auto; lia.
    3: {
      simpl. rewrite <-qor_empty_id_r. apply IHn.
      repeat rewrite opent_preserves_ty_size. lia.
      simpl. apply opent_closed. apply opent_closed. eapply closedty_extend; eauto.
      unfold closed_ql, qone. setoid_rewrite Nat.eqb_eq. lia.
      unfold closed_ql, qone. setoid_rewrite Nat.eqb_eq. lia.
      repeat apply opent_preserves_wf_abs. auto.
    }
    * apply functional_extensionality. intros.
      unfold qempty, qor, qdiff. reflexivity.
    * rewrite <-qor_empty_id_r. apply q_sub. crush. intro; auto. intuition.
    * repeat rewrite <-qor_empty_id_r. simpl. apply q_sub.
      crush. intro; auto.
      rewrite plift_closed'l.
      repeat rewrite plift_or. repeat rewrite plift_if, plift_one.
      repeat apply psub_or_dist_l; try apply psub_if_assume_l.
      repeat apply psub_pdom_tighten_r. intuition.
      all: unfoldq; simpl; lia.
Qed.

Lemma stp_closed: forall G gr T1 T2,
  stp G gr T1 T2 ->
  closed_ql (length G) gr /\ closed_ty 0 (length G) T1 /\ closed_ty 0 (length G) T2.
Proof.
  intros. induction H.
  - intuition. constructor. constructor.
  - intuition. constructor. constructor.
  - apply qtp_closed in H1. intuition.
    constructor; auto. constructor; auto.
  - inversion H; subst. intuition.
    destruct H6; auto. constructor; auto. split; auto.
  - intuition. rewrite plift_closed'l in *. rewrite plift_or.
    unfoldq. intuition.
  - intuition. inversion H; subst. constructor; auto.
  - intuition. inversion H1; subst. constructor; auto.
  - intuition. intros ? ?. unfold closed_ql in H12, H14.
    apply orb_true_iff in H15 as [? | ?]; auto.
    unfold qdiff, negb in H15.
    destruct (qone (length env) x) eqn:?.
    destruct (qone (length env + 1) x) eqn:?. repeat rewrite andb_true_iff in H15.
    destruct H15 as [[? ?] ?]. discriminate.
    repeat rewrite andb_true_iff in H15. destruct H15 as [[? ?] ?]. discriminate.
    destruct (qone (length env + 1) x) eqn:?.
    repeat rewrite andb_true_iff in H15. destruct H15 as [[? ?] ?]. discriminate.
    repeat rewrite andb_true_iff in H15. destruct H15 as [[? ?] ?].
    eapply H14 in H15. unfold qone in Heqb, Heqb0. bdestruct (x =? length env). discriminate.
    bdestruct (x=?length env + 1). discriminate. replace ((T1b, fr1b, qor (qfvs q1b) (qif fn1b (qone (length env)))) :: (TUnit, true, qempty) :: env) with ([(T1b, fr1b, qor (qfvs q1b) (qif fn1b (qone (length env))))] ++ (TUnit, true, qempty) :: env) in H15.
    replace ((TUnit, true, qempty) :: env) with ([(TUnit, true, qempty)] ++ env) in H15. simpl in *. lia. auto. auto.
    constructor; auto. constructor; auto.
Qed.


Inductive has_type : tenv -> tm -> ty -> ql -> bool -> ql -> Prop :=
| t_true: forall env p,
    has_type env ttrue TBool p false qempty
| t_false: forall env p,
    has_type env tfalse TBool p false qempty
| t_var: forall x env T p fr q,
    indexr x env = Some (T, fr, q) ->
    (plift p) x ->
    has_type env (tvar x) T p false (qone x)
(* standard refs (shallow), purely driven by inner qualifier *)
| t_ref: forall t env T p q,
    has_type env t T p false q ->
    True ->
    has_type env (tref t) (TRef T false (qempty, q)) p true qempty
| t_get: forall t env T p fr q q1,
    has_type env t (TRef T false q1) p fr q ->
    psub (plift (qfvs q1)) (plift p) ->
    has_type env (tget t) T p false (qfvs q1)
(* refs with self-ref (deep), accounted to outer qualifier *)
| t_ref2: forall t env T p q,
    has_type env t T p false q ->
    True ->
    has_type env (tref t) (TRef T true (qempty, qempty)) p true q
| t_get2: forall t env T p fr q,
    has_type env t (TRef T true (qempty, qempty)) p fr q ->
    has_type env (tget t) T p fr q
(* put operation is shared *)
| t_put: forall t1 t2 env T p fr1 q1 fr2 q2,
    has_type env t1 (TRef T fr1 q1) p fr2 q2 ->
    has_type env t2 T p false (qfvs q1) ->
    True ->
    has_type env (tput t1 t2) TBool p false qempty
| t_app: forall env f t T1 T2 p frf qf frx qx qx' fn1 fr1 q1 fr2 q2,
    has_type env f (TFun T1 fn1 fr1 q1 T2 fr2 q2) p frf qf ->
    has_type env t T1 p frx qx  ->
    (* ---- different app cases: *)
    (if fn1 then
       True
     else
       if fr1 then
         qtp env frx qx frx qx' /\
         psub (plift qx') (plift p) /\
         psub (pand
                 (vars_trans' env qf)
                 (vars_trans' env (qdiff qx' (qfvs q1))))
           pempty
       else
         qtp env frx qx fr1 (qfvs q1)) ->
    (* ---- *)
    psub (plift (qfvs q1)) (plift p) ->   (* this is necessary (so far!) *)
    psub (plift (qfvs q2)) (plift p) ->   (* this is necessary (so far!) *)
    (frf = true -> occurrences_bvs not_free T2 1) ->
    (frx = true -> occurrences_bvs not_free T2 0) ->
    has_type env (tapp f t) (opent 0 qx (opent 1 qf T2)) p
      (qbvs q2 1 && frf || qbvs q2 0 && frx || fr2)
      (qfvs (openq 0 qx (openq 1 qf q2)))
| t_abs: forall env t T1 T2 p ff fn1 fr1 q1 fr2 q2 qf,
    has_type ((T1, fr1 || ff, (qor (qand (qfvs q1) qf) (qif (fn1 || ff) (qone (length env)))))::(TUnit, false, qf)::env) t
      (opent_rec 2 0 (length env) T2)
      (qor (qor qf (qone (length env))) (qone (1 + length env)))
      fr2
      (qfvs (openq_rec 2 0 (length env) q2))
      ->
    (ff = false -> psub (plift (qfvs q1)) (plift qf)) ->
    closed_ty 0 (length env) T1 ->
    closed_ql2 0 (length env) q1 ->
    (* omitted *) closed_ty 2 (length env) T2 ->
    (* omitted *) closed_ql2 2 (length env) q2 ->
    closed_ql (length env) qf ->
    psub (plift qf) (plift p) ->
    bsub fn1 fr1 ->
    occurrences_bvs covariant_only T2 1 ->
    has_type env (tabs t)
      (TFun T1 fn1 fr1 q1 T2 fr2 q2)
      p false qf
| t_sub_stp: forall env y T1 T2 p fr1 q1 fr2 q2 gr,
    has_type env y T1 p fr1 q1 ->
    stp env gr T1 T2 ->
    qtp env fr1 (qor q1 gr) fr2 q2 ->
    psub (plift gr) (plift p) ->
    psub (plift q2) (plift p) -> (* necessary? *)
    has_type env y T2 p fr2 q2
| t_ascript: forall G e T p fr q,
    has_type G e T p fr q -> has_type G (tas e T fr q) T p fr q
.

(* ---------- main theorems ---------- *)


Theorem qtp_fundamental: forall env fr1 q1 fr2 q2,
    qtp env fr1 q1 fr2 q2 ->
    sem_qtp2 env fr1 (plift q1) fr2 (plift q2).
Proof.
  intros. induction H.
  - eapply sem_qtp2_sub; eauto.
  - rewrite plift_or, plift_diff, plift_one.
    eapply sem_qtp2_var; eauto.
  - eapply sem_qtp2_trans; eauto.
Qed.


Theorem stp_fundamental: forall env gr T1 T2,
    stp env gr T1 T2 ->
    sem_stp2 env (plift gr) T1 T2.
Proof.
  intros. induction H.
  - rewrite plift_empty. eapply sem_stp2_bool.
  - rewrite plift_empty. eapply sem_stp2_unit.
  - rewrite plift_empty in *. eapply sem_stp2_ref; eauto; simpl.
    eapply qtp_fundamental; eauto.
    eapply qtp_fundamental; eauto.
    apply stp_closed in H. intuition.
  - inversion H; subst. eapply sem_stp2_ref_grow; eauto.
  - rewrite plift_or. eapply sem_stp2_trans; eauto.
  - rewrite plift_empty. eapply sem_stp2_fun_arg; eauto.
  - eapply sem_stp2_fun_grow; eauto.
    rewrite <-plift_or. eapply qtp_fundamental; eauto.
  - rewrite plift_or. repeat rewrite plift_diff, plift_one. eapply sem_stp2_fun; eauto.
    rewrite <-plift_or. eapply qtp_fundamental; eauto.
    rewrite <-plift_or. eapply qtp_fundamental; eauto.
    apply stp_closed in H. intuition.
Qed.


Lemma hast_closed: forall env t T1 p fr1 q1,
  has_type env t T1 p fr1 q1 ->
  telescope env ->
  closed_ty 0 (length env) T1 /\
    closed_ql (length env) q1 /\
    psub (plift q1) (plift p).
Proof.
  intros. induction H.
  - intuition. constructor. rewrite plift_empty. intro; intuition.
  - intuition. constructor. rewrite plift_empty. intro; intuition.
  - specialize (H0 _ _ _ _ H). eapply indexr_var_some' in H. intuition.
    eapply closedty_extend; eauto. lia.
    rewrite plift_closed'l, plift_one. unfoldq. lia.
    rewrite plift_one. unfoldq. intros. subst. intuition.
  - intuition. constructor; auto. split; simpl; auto.
    rewrite plift_empty. intro; intuition.
  - specialize (IHhas_type H0). destruct IHhas_type. inversion H2; subst.
    destruct H10. intuition.
  - intuition. constructor; auto. split; auto.
  - intuition. inversion H2; subst. auto.
  - intuition. constructor. rewrite plift_empty. intro; auto with *.
  - destruct (IHhas_type1 H0). inversion H7; subst.
    destruct q2. destruct H21. simpl in *. intuition.
    apply opent_closed; auto. apply opent_closed; auto.
    rewrite plift_closed'l, plift_or, plift_or, plift_if, plift_if.
    repeat apply psub_or_dist_l; repeat apply psub_if_assume_l; auto.
    rewrite plift_or, plift_or, plift_if, plift_if.
    repeat apply psub_or_dist_l; repeat apply psub_if_assume_l; auto.
  - intuition. constructor; auto.
  - apply qtp_closed in H2. apply stp_closed in H1.
    intuition.
  - intuition.
Qed.

Lemma hast_filter_widening: forall Γ e T p1 p2 fr q,
  psub (plift p1) (plift p2) ->
  has_type Γ e T p1 fr q -> has_type Γ e T p2 fr q.
Proof.
  intros. generalize dependent p2. induction H0; intros.
  - constructor.
  - constructor.
  - eapply t_var. eauto. crush.
  - constructor; auto.
  - eapply t_get. auto. crush.
  - eapply t_ref2; auto.
  - eapply t_get2. auto.
  - eapply t_put; auto.
  - eapply t_app; auto.
    destruct fn1; auto. destruct fr1; auto. destruct H as (? & ? & ?). split; eauto.
    split; auto. crush. crush. crush.
  - eapply t_abs; auto. apply IHhas_type. intro; auto. auto. crush.
  - eapply t_sub_stp; auto. eauto. auto. crush. crush.
  - constructor. auto.
Qed.

(* if well-typed, then result is an actual value (not stuck and not a timeout),
   for large enough n *)

Lemma fundamental_property' : forall t G T p fr q,
    telescope G -> (* without loss of generality *)
    has_type G t T p fr q ->
    sem_type G t T (plift p) fr (plift q).
Proof.
  intros ? ? ? ? ? ? ? W.
  induction W.
  - rewrite plift_empty. eapply sem_true; eauto.
  - rewrite plift_empty. eapply sem_false; eauto.
  - rewrite plift_one. eapply sem_var; eauto.
  - rewrite plift_empty. eapply sem_ref; eauto.
    apply hast_closed in W; intuition.
  - eapply sem_get; eauto.
  - eapply sem_ref2; eauto. apply hast_closed in W; intuition.
  - eapply sem_get2; eauto.
  - rewrite plift_empty. eapply sem_put; eauto.
    apply hast_closed in W2; intuition.
  - assert (qf = qand p qf). {
      apply hast_closed in W1; auto. apply functional_extensionality; intros.
      unfold qand. destruct (qf x) eqn:?. destruct W1 as (_ & _ & W1).
      apply W1 in Heqb. rewrite Heqb. auto. rewrite andb_false_r. auto.
    }
    assert (qx = qand p qx). {
      apply hast_closed in W2; auto. apply functional_extensionality; intros.
      unfold qand. destruct (qx x) eqn:?. destruct W2 as (_ & _ & W2).
      apply W2 in Heqb. rewrite Heqb. auto. rewrite andb_false_r. auto.
    }
    rewrite H6, H5 at 1. eapply sem_app; eauto.
    destruct fn1; auto. destruct fr1. intuition.
    rewrite <-plift_and. rewrite <-H6. apply qtp_fundamental; eauto. auto. auto.
    apply qtp_fundamental; eauto.
  - repeat rewrite plift_or in *.
    repeat rewrite plift_and in *.
    repeat rewrite plift_if in *.
    repeat rewrite plift_one in *.
    assert (qf = qand p qf). {
      apply functional_extensionality; intros. unfold qand.
      destruct (qf x) eqn:?. apply H6 in Heqb. rewrite Heqb. auto.
      rewrite andb_false_r. auto.
    }
    eapply sem_abs; eauto.
    repeat rewrite <-H9. apply IHW. eapply telescope_extend.
    rewrite plift_closed'l, plift_or, plift_and, plift_if, plift_one.
    apply psub_or_dist_l. apply psub_pdom_tighten_r. unfoldq. intuition.
    apply psub_if_assume_l. unfoldq. simpl. intros; subst. apply Nat.lt_succ_diag_r.
    eapply closedty_extend; eauto. simpl. apply Nat.le_succ_diag_r.
    eapply telescope_extend; auto. constructor.
    rewrite <-H9. eauto.
  - eapply sem_sub_qtp2_stp2 with (gr := plift gr); eauto.
    apply stp_fundamental; auto. rewrite <-plift_or. apply qtp_fundamental; auto.
  - eapply sem_ascript; auto. apply hast_closed in W; intuition.
Qed.

Theorem fundamental_property : forall t G T p fr q,
  has_type G t T p fr q ->
  sem_type G t T (plift p) fr (plift q).
Proof.
  unfold sem_type. intros. eapply fundamental_property'; eauto.
  eapply envt_telescope; eauto.
Qed.


(* note: not assuming anything other than has_type below *)
Corollary safety : forall t T fr q,
  has_type [] t T qempty fr q ->
  exp_type [] st_zero [] [] t T (plift qempty) fr (plift q).
Proof.
  intros. eapply fundamental_property in H; eauto.
  destruct (H [] st_zero [] []).
  - unfold env_type; intuition; simpl.
    unfoldq. intuition. inversion H0.
    intros ? [? ?]. destruct H3 as [? [? ?]].
    destruct H5. destruct H5. inversion H5.
  - unfold store_type; intuition. unfold st_locs, st_zero in *. unfoldq. simpl in *. lia.
  - destruct H0. eexists. eexists. eauto.
Qed.


End STLC.