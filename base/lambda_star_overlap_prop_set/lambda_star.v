Require Export Arith.EqNat.
Require Export Arith.Le.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Program.Equality.
Require Import Coq.Lists.List.
Require Import Psatz.
Require Import ZArith.
Require Import Coq.Arith.Compare_dec.
Import ListNotations.

Require Import nats.
Require Import vars.
Require Import env.
Require Import tactics.
Require Import qualifiers.

Import QualNotations.
Local Open Scope qualifiers.

Require Import FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.

Definition id := nat.

Definition lt_S_n :=
  fun n m : nat => proj2 (Nat.succ_lt_mono n m).
Definition le_plus_r := 
  fun n m : nat => Nat.le_add_l m n.

(* Definitions *)

(* ### Syntax ### *)
(* We represent terms and types in locally nameless style. *)

(* Types *)
Inductive ty : Type :=
| TUnit : ty                             (* Unit base type*)
| TFun  : qual -> qual -> ty -> ty -> ty (* Dependent function type TFun q1 q2 T1 T2 ~> ((x: T1^q1) => T2^q2),
                                            where x is bound in T2 and q2.
                                            Bound variables are represented by de Bruijn indices, where x ~> #0. *)
| TRef  : ty -> ty                       (* Mutable reference type TRef T ~> Ref[T]. *)
.

(* Terms *)
Inductive tm : Type :=
| tunit   : tm              (* The unit value. *)
| tvar    : var -> tm       (* Term variable, either free (tvar $n) (de Bruijn level), or bound (tvar #n) (de Bruijn index). *)
| tabs    : tm  -> tm       (* Lambda abstractions (tabs t) ~> λx.t, where x ~> #0. *)
| tapp    : tm  -> tm -> tm (* Function application. *)
| tloc    : loc -> tm       (* A store location literal. *)
| tref    : tm  -> tm       (* Reference allocation (tref t) ~> new Ref(t). *)
| tderef  : tm  -> tm       (* Dereference (tderef t) ~> !t. *)
| tassign : tm  -> tm -> tm (* Reference assignment (tassign t1 t2) ~> t1 := t2. *)
.

Notation "& l" := (tloc l) (at level 0).
Notation "! t" := (tderef t) (at level 0).
Coercion tvar : var >-> tm. (* lightens the notation of term variables *)

Definition tenv := list (ty * qual).
Definition senv := list ty. (* Sigma store typing *)

#[global] Hint Rewrite (@N_lift_dom ty) : nlift_rewrite.
#[global] Hint Rewrite (@N_lift_dom (ty * qual)) : nlift_rewrite.

Definition extends {A} (l1 l2 : list A): Prop := exists l', l1 = l' ++ l2.
Notation "x ⊇ y" := (extends x y) (at level 0).

(* Opening a term *)
Fixpoint open_rec_tm (k : nat) (u : tm) (t : tm) {struct t} : tm :=
  match t with
  | tunit            => tunit
  | tvar   (varF x) => tvar (varF x)
  | tvar   (varB x) => if Nat.eqb k x then u else tvar (varB x)
  | tabs    t       => tabs    (open_rec_tm (S k) u t)
  | tapp    t1 t2   => tapp    (open_rec_tm k u t1) (open_rec_tm k u t2)
  | tloc    l       => tloc l
  | tref    t       => tref    (open_rec_tm k u t)
  | tderef  t       => tderef  (open_rec_tm k u t)
  | tassign t1 t2   => tassign (open_rec_tm k u t1) (open_rec_tm k u t2)
  end
.

(*simultaneous opening with self-ref and argument: *)
Definition open_tm (u t : tm) := open_rec_tm 0 u t.
Definition open_tm' {A : Type} (env : list A) t :=
  open_rec_tm 0 (varF (length env)) t.

(* alternative without match *)
Definition openq (u d : qual) : qual := open_qual 0 u d.
Definition openq' {A} (env : list A) d :=
  openq (just_fv (length env)) d.

(* Opening a type with a qualifier *)
Fixpoint open_rec_ty (k : nat) (d' : qual) (T : ty) : ty :=
  match T with
  | TUnit            => TUnit
  | TFun d1 d2 T1 T2 => TFun (open_qual k d' d1) (open_qual (S k) d' d2) (open_rec_ty k d' T1) (open_rec_ty (S k) d' T2)
  | TRef T           => TRef (open_rec_ty k d' T)
  end.

Definition open_ty (u : id) (T : ty) := (open_rec_ty 0 (just_fv u) T).
Definition open_ty' {A : Type} (env : list A) (T : ty) :=
  open_ty (length env) T.

Module OpeningNotations.
  Declare Scope opening.
  Notation "[[ k ~> u ]]ᵗ t" := (open_rec_tm k u t) (at level 10) : opening.
  Notation "[[ k ~> U ]]ᵀ T" := (open_rec_ty k U T) (at level 10) : opening.
  Notation "[[ k ~> d' ]]ᵈ d" := (open_qual k d' d) (at level 10) : opening.
End OpeningNotations.
Import OpeningNotations.
Local Open Scope opening.

(* measure for induction over terms *)
Fixpoint tm_size (t : tm) : nat :=
  match t with
  | tunit         => 0
  | tvar    _     => 0
  | tabs    t     => S (tm_size t)
  | tapp    t1 t2 => S (tm_size t1 + tm_size t2)
  | tloc    _     => 0
  | tref    t     => S (tm_size t)
  | tderef  t     => S (tm_size t)
  | tassign t1 t2 => S (tm_size t1 + tm_size t2)
  end.

(* measure for induction over types *)
Fixpoint ty_size (T : ty) : nat :=
  match T with
  | TUnit           => 0
  | TFun  _ _ T1 T2 => S (ty_size T1 + ty_size T2)
  | TRef  T         => S (ty_size T)
  end.

Fixpoint splice (n : nat) (t : tm) {struct t} : tm :=
  match t with
  | tunit          => tunit
  | tvar (varF i)  =>
    if le_lt_dec n i then tvar (varF (S i))
    else tvar (varF i)
  | tvar (varB i)  => tvar    (varB i)
  | tabs    t      => tabs    (splice n t)
  | tapp    t1 t2  => tapp    (splice n t1) (splice n t2)
  | tloc    l      => tloc     l
  | tref    t      => tref    (splice n t)
  | tderef  t      => tderef  (splice n t)
  | tassign t1 t2  => tassign (splice n t1) (splice n t2)
  end.

Fixpoint splice_ty (n : nat) (T : ty) {struct T} : ty :=
  match T with
  | TUnit            => TUnit
  | TFun d1 d2 T1 T2 => TFun (splice_qual n d1) (splice_qual n d2) (splice_ty n T1) (splice_ty n T2)
  | TRef T           => TRef (splice_ty n T)
  end.

Fixpoint unsplice_ty (n : nat) (T : ty) {struct T} : ty :=
  match T with
  | TUnit            => TUnit
  | TFun d1 d2 T1 T2 => TFun (unsplice_qual n d1) (unsplice_qual n d2) (unsplice_ty n T1) (unsplice_ty n T2)
  | TRef T           => TRef (unsplice_ty n T)
  end.

Fixpoint closed_tm (b f l : nat ) (t : tm) : Prop :=
  match t with
  | tunit          => True
  | tvar (varF i)  => i < f
  | tvar (varB i)  => i < b
  | tabs    t      => closed_tm (S b) f l t
  | tapp    t1 t2  => closed_tm b f l t1 /\ closed_tm b f l t2
  | tloc    l'     => l' < l
  | tref    t      => closed_tm b f l t
  | tderef  t      => closed_tm b f l t
  | tassign t1 t2  => closed_tm b f l t1 /\ closed_tm b f l t2
  end.

Fixpoint closed_ty (b f l : nat ) (T : ty) : Prop :=
  match T with
  | TUnit            => True
  | TRef T           => closed_ty 0 0 0 T
  | TFun d1 d2 T1 T2 =>
      closed_Qual b f l (Q_lift d1) /\
      closed_Qual (S b) f l (Q_lift d2) /\
      closed_ty b f l T1 /\
      closed_ty (S b) f l T2
  end.

Definition splice_tenv (n : nat) (Γ : tenv) : tenv :=
  map (fun p => ((splice_ty n (fst p)), (splice_qual n (snd p)))) Γ.

Inductive stp : tenv -> senv -> ty -> qual -> ty -> qual -> Prop :=
| s_base : forall Γ Σ d1 d2,
    Qstp (length Γ) (length Σ) (Q_lift d1) (Q_lift d2) ->
    stp Γ Σ TUnit d1 TUnit d2
| s_ref : forall Γ Σ T1 T2 d1 d2,
    Qstp (length Γ) (length Σ) (Q_lift d1) (Q_lift d2) ->
    stp [] [] T1 ∅ T2 ∅ -> (* we don't have bottom, so use ∅ here *)
    stp [] [] T2 ∅ T1 ∅ ->
    stp Γ Σ (TRef T1) d1 (TRef T2) d2
| s_fun : forall Γ Σ T1 d1 T2 d2 T3 d3 T4 d4 d5 d6,
    closed_ty 0 (length Γ) (length Σ) (TFun d1 d2 T1 T2) ->
    closed_ty 0 (length Γ) (length Σ) (TFun d3 d4 T3 T4) ->
    Qstp (length Γ) (length Σ) (Q_lift d5) (Q_lift d6) ->
    stp Γ Σ T3 d3 T1 d1 ->
    stp ((T3,d3) :: Γ) Σ (open_ty' Γ T2) (openq' Γ d2) (open_ty' Γ T4) (openq' Γ d4) ->
    stp Γ Σ (TFun d1 d2 T1 T2) d5 (TFun d3 d4 T3 T4) d6
| s_trans : forall Γ Σ T1 d1 T2 d2 T3 d3,
    stp Γ Σ T1 d1 T2 d2 -> stp Γ Σ T2 d2 T3 d3 -> stp Γ Σ T1 d1 T3 d3
.
#[global] Hint Constructors stp : dsub.

(* Specifies that the variable x's qualifier is subsumed by q in context Γ *)
Definition saturated_var (Γ : tenv) (Σ : senv) (x : id) (q : qual)  : Prop := exists U q',
  indexr x Γ = Some (U, q') /\
  (Subq (Q_lift q') (Q_lift q) /\
  closed_Qual 0 x (length Σ) (Q_lift q')).

(* Specifies that q is transitively closed w.r.t. Γ, i.e., each variable x in q is a saturated variable in the above sense. *)
Definition saturated (Γ : tenv) (Σ : senv) (q: qual) : Prop := forall x, (varF x) ∈ᵥ q -> saturated_var Γ Σ x q.

(* A typing context is well-formed iff all its assumptions are saturated. *)
Definition wf_tenv (Γ : tenv) (Σ : senv):= forall x T q, indexr x Γ = Some (T, q) -> saturated Γ Σ q.

Inductive has_type : tenv -> qual -> senv -> tm -> ty -> qual -> Prop :=
| t_base : forall Γ Σ φ,
    closed_Qual 0 (length Γ) (length Σ) (Q_lift φ) ->
    has_type Γ φ Σ tunit TUnit ∅ (* use ∅ instead of bottom *)

| t_var : forall Γ φ Σ x T d,
    indexr x Γ = Some (T,d) ->
    Subq (Q_lift (d ⊕ x)) (Q_lift φ) ->
    closed_Qual 0 (length Γ) (length Σ) (Q_lift φ) ->
    closed_ty 0 x (length Σ) T ->
    closed_Qual 0 x (length Σ) (Q_lift d) ->
    has_type Γ φ Σ (tvar (varF x)) T (d ⊕ x)

| t_abs: forall Γ φ Σ T1 d1 T2 d2 df t,
    closed_tm 1 (length Γ) (length Σ) t ->
    closed_ty 0 (length Γ) (length Σ) (TFun d1 d2 T1 T2) ->
    closed_Qual 0 (length Γ) (length Σ) (Q_lift φ) ->
    Subq (Q_lift df) (Q_lift φ) ->
    saturated Γ Σ d1 ->
    saturated Γ Σ df ->
    has_type ((T1,d1) :: Γ) (df ⊔ (just_fv (length Γ))) Σ (open_tm' Γ t) (open_ty' Γ T2) (openq' Γ d2) ->
    has_type Γ φ Σ (tabs t) (TFun d1 d2 T1 T2) df

| t_app : forall Γ φ Σ t1 d1 t2 d2 df T1 T2,
    has_type Γ φ Σ t1 (TFun (df ⊓ d1) d2 T1 T2) df ->
    has_type Γ φ Σ t2 T1 d1 ->
    closed_ty 0 (length Γ) (length Σ) T2 ->
    Subq (Q_lift (openq ∅ d2)) (Q_lift φ) ->
    saturated Γ Σ (openq ∅ d2) ->
    has_type Γ φ Σ (tapp t1 t2) T2 (openq d1 d2)

| t_loc : forall Γ φ Σ l T,
    closed_Qual 0 (length Γ) (length Σ) (Q_lift φ) ->
    indexr l Σ = Some T ->
    closed_ty 0 0 0 T ->
    Subq (Q_lift (just_loc l)) (Q_lift φ) ->
    has_type Γ φ Σ (tloc l) (TRef T) (just_loc l)

| t_ref: forall Γ φ Σ t d,
    has_type Γ φ Σ t TUnit d   ->
    has_type Γ φ Σ (tref t) (TRef TUnit) ∅

| t_deref: forall Γ φ Σ T d t,
    has_type Γ φ Σ t (TRef T) d ->
    has_type Γ φ Σ (tderef t) T ∅

| t_assign: forall Γ φ Σ t1 t2 d1 d2,
    has_type Γ φ Σ t1 (TRef TUnit) d1 ->
    has_type Γ φ Σ t2 TUnit d2 ->
    has_type Γ φ Σ (tassign t1 t2) TUnit ∅

| t_sub: forall Γ φ  Σ e T1 d1 T2 d2,
    has_type Γ φ Σ e T1 d1 ->
    stp Γ Σ T1 d1 T2 d2 ->
    Subq (Q_lift d2) (Q_lift φ) ->
    saturated Γ Σ d2 ->
    has_type Γ φ Σ e T2 d2
.
#[global] Hint Constructors has_type : core.

Inductive value : tm -> Prop :=
| value_abs : forall t, value (tabs t)
| value_cst : value tunit
| value_loc : forall l, value (tloc l)
.
#[global] Hint Constructors value : core.

Definition store := list tm.

Inductive step : tm -> store -> tm -> store -> Prop :=
(*contraction rules*)
| step_beta : forall t v σ,
    value v ->
    step (tapp (tabs t) v) σ (open_tm v t) σ
| step_ref : forall v σ,
    value v ->
    step (tref v) σ (tloc (length σ)) (v :: σ)
| step_deref : forall σ l v,
    indexr l σ = Some v ->
    step (tderef (tloc l)) σ v σ
| step_assign : forall σ l v,
    l < (length σ) ->
    value v ->
    step (tassign (tloc l) v) σ tunit (update σ l v)
(*congruence rules*)
| step_c_ref : forall t t' σ σ',
    step t σ t' σ' ->
    step (tref t) σ (tref t') σ'
| step_c_deref : forall t t' σ σ',
    step t σ t' σ' ->
    step (tderef t) σ (tderef t') σ'
| step_c_app_l : forall t1 t1' t2 σ σ',
    step t1 σ t1' σ' ->
    step (tapp t1 t2) σ (tapp t1' t2) σ'
| step_c_app_r : forall v t2 t2' σ σ',
    value v ->
    step t2 σ t2' σ' ->
    step (tapp v t2) σ (tapp v t2') σ'
| step_c_assign_l : forall t1 t1' t2 σ σ',
    step t1 σ t1' σ' ->
    step (tassign t1 t2) σ (tassign t1' t2) σ'
| step_c_assign_r : forall v t2 t2' σ σ',
    value v ->
    step t2 σ t2' σ' ->
    step (tassign v t2) σ (tassign v t2') σ'
.

Definition CtxOK (Γ : tenv) (φ : qual) (Σ : senv) (σ : store) : Prop :=
  length Σ = length σ /\
  forall l v T, indexr l Σ = Some T -> indexr l σ = Some v -> value v /\ has_type Γ φ Σ v T ∅.

(* Substitutions

   It is assumed that substitution is always on the first two context entries, which
   is why other free variables are unconditionally decremented.
*)
Fixpoint subst_tm (t : tm) (v : nat) (u : tm) : tm :=
  match t with
  | tunit         => tunit
  | # x           => # x
  | $ x           => if Nat.eqb x v then u else $(pred x)
  | tabs t        => tabs (subst_tm t v u)
  | tapp t1 t2    => tapp (subst_tm t1 v u) (subst_tm t2 v u)
  | & l           => & l
  | tref t        => tref (subst_tm t v u)
  | ! t           => ! (subst_tm t v u)
  | tassign t1 t2 => tassign (subst_tm t1 v u) (subst_tm t2 v u)
  end.
Notation "{ v1 |-> t1 ; t2 }ᵗ t" := (subst_tm (subst_tm t v1 t1) v1 t2) (at level 10).
Notation "{ v1 |-> t1 }ᵗ t" := (subst_tm t v1 t1) (at level 10).

Fixpoint subst_ty (T : ty) (v : nat) (q : qual) : ty :=
  match T with
  | TUnit            => TUnit
  | TFun q1 q2 T1 T2 => TFun (subst_qual q1 v q) (subst_qual q2 v q) (subst_ty T1 v q) (subst_ty T2 v q)
  | TRef T           => TRef (subst_ty T v q)
  end.

Definition subst_tenv (Γ : tenv) (v : nat) (q1 : qual) : tenv :=
  map (fun p => match p with
             | (T,q') => ((subst_ty T v q1) , (subst_qual q' v q1))
             end) Γ.

Module SubstitutionNotations.
  Declare Scope substitutions.
  Notation "{ v1 |-> t1 ; t2 }ᵗ t" := (subst_tm (subst_tm t v1 t1) v1 t2) (at level 10) : substitutions.
  Notation "{ v1 |-> t1 }ᵗ t" := (subst_tm t v1 t1) (at level 10) : substitutions.
  Notation "{ v1 |-> q1 ; q2 }ᵈ q" := (subst_qual (subst_qual q v1 q1) v1 q2) (at level 10) : substitutions.
  Notation "{ v1 |-> q1 }ᵈ q" := (subst_qual q v1 q1) (at level 10) : substitutions.
  Notation "{ v1 |-> q1 ; q2  }ᵀ T" := (subst_ty (subst_ty T v1 q1) v1 q2) (at level 10) : substitutions.
  Notation "{ v1 |-> q1 }ᵀ T" := (subst_ty T v1 q1) (at level 10) : substitutions.
  Notation "{ v1 |-> q1 }ᴳ G" := (subst_tenv G v1 q1) (at level 10) : substitutions.
  Notation "{ v1 |-> q1 ; q2 }ᴳ G" := (subst_tenv (subst_tenv G v1 q1) v1 q2) (at level 10) : substitutions.
End SubstitutionNotations.
Import SubstitutionNotations.
Local Open Scope substitutions.

(* Indicates that d is freshly picked w.r.t to the store typing Σ and contained in Σ'.
   This is used in the type safety theorem to specify that steps may only introduce a fresh qualifier from storage effects.
   More specifically, the "fresh" qualifier d is at most a singleton containing a fresh store location. *)
Inductive disjointq (Σ Σ' : senv) (d : qual) : Prop :=
| disj_bot : d = ∅ -> disjointq Σ Σ' d
| disj_loc : forall l,
    (length Σ) <= l ->
    l < (length Σ') ->
    d = (just_loc l) -> disjointq Σ Σ' d
.
Arguments disj_loc { Σ Σ' d }.
#[global] Hint Constructors disjointq : core.

(* :! -- directly invertible value typing *)

Inductive vtp: senv -> tm -> ty -> qual -> Prop :=
| vtp_base: forall Σ d,
  closed_Qual 0 0 (length Σ) (Q_lift d) ->
  vtp Σ tunit TUnit d

| vtp_loc:  forall Σ l T U d,
  closed_Qual 0 0 (length Σ) (Q_lift d) ->
  closed_ty 0 0 0 T ->
  indexr l Σ = Some T ->
  stp [] [] T ∅ U ∅ -> (* we don't have bottom, so use ∅ here *)
  stp [] [] U ∅ T ∅ ->
  Qstp 0 (length Σ) (Q_lift (just_loc l)) (Q_lift d) ->
  vtp Σ (tloc l) (TRef U) d

| vtp_abs: forall Σ T1 d1 T2 d2 T3 d3 T4 d4 df1 df2 t,
  closed_tm 1 0 (length Σ) t ->
  closed_Qual 0 0 (length Σ) (Q_lift df2) ->
  closed_ty 0 0 (length Σ) (TFun d3 d4 T3 T4) ->  (* sub type *)
  closed_ty 0 0 (length Σ) (TFun d1 d2 T1 T2) ->  (* super type *)
  has_type [(T1,d1)] (df1 ⊔ (just_fv 0)) Σ (open_tm' ([]: tenv) t) (open_ty' ([]: tenv) T2) (openq' ([]: tenv) d2) ->
  stp [] Σ T3 d3 T1 d1 ->
  Qstp 0 (length Σ) (Q_lift df1) (Q_lift df2) ->
  stp [(T3, d3)] Σ (open_ty' ([]: tenv) T2) (openq' ([] : tenv) d2) (open_ty' ([]: tenv) T4) (openq' ([]: tenv) d4) ->
  vtp Σ (tabs t) (TFun d3 d4 T3 T4) df2
  .
#[global] Hint Constructors vtp : core.

(* The concluding statement of the preservation part of type safety, i.e., typing is preserved after a step under an extended store, so
   that the initial qualifier is increased by at most a fresh storage effect. *)
Inductive preserve (Γ : tenv) (Σ : senv) (t' : tm) (T : ty) (d : qual) (σ' : store) : Prop :=
| Preserve : forall Σ' d',
    Σ' ⊇ Σ ->
    CtxOK Γ (qdom Σ') Σ' σ' ->
    disjointq Σ Σ' d' ->
    has_type Γ (qdom Σ') Σ' t' T (d ⊔ d') ->
    preserve Γ Σ t' T d σ'.
Arguments Preserve {Γ Σ t' T d σ'}.

(* deterministic relations (used to recover standard progress & preservation from the type safety theorem. ) *)
Definition relation (X : Type)(Y: Type) := X -> Y -> X ->  Y -> Prop.
Definition deterministic {X : Type}{Y: Type} (R : relation X Y) :=
  forall (x x1 x2 : X) (y y1 y2: Y), R x y x1 y1 -> R x y x2 y2 -> x1 = x2 /\ y1 = y2.

(* The concluding statement of the separation of preservation corollary, i.e., interleaving the execution of two well-typed
   terms with disjoint qualifiers preserves the types and keeps qualifiers disjoint.  *)
Inductive separate (Σ : senv) (t1' : tm) (T1 : ty) (t2' : tm) (T2 : ty) : Prop :=
| Separate : forall Σ' Σ'' q1' q2',
    Σ' ⊇ Σ ->
    Σ'' ⊇ Σ' ->
    has_type [] (qdom Σ') Σ' t1' T1 q1' ->
    has_type [] (qdom Σ'') Σ'' t2' T2 q2' ->
    q1' ⊓ q2' ⊑↑ ∅ ->
    separate Σ t1' T1 t2' T2.
Arguments Separate {Σ t1' T1 t2' T2}.

(** Metatheory **)

Lemma extends_refl : forall {A}, forall{l : list A}, extends l l.
  intros. unfold extends. exists []. auto.
Qed.
#[global] Hint Resolve extends_refl : core.

Lemma extends_cons : forall {A}, forall{l : list A}, forall{a:A}, extends (a :: l) l.
  intros. unfold extends. exists [a]. auto.
Qed.

Lemma extends_length : forall {A}, forall{l1 l2 : list A}, extends l1 l2 -> length l1 >= length l2.
  intros. unfold extends in H. destruct H as [l' Heq]. subst. rewrite app_length. lia.
Qed.

Lemma extends_ldom : forall {Σ' Σ : senv}, (Σ') ⊇ (Σ) -> qdom Σ ⊑↑ qdom Σ'.
  intros. inversion H. unfold qdom. simpl.
  intuition. assert (length Σ' = length (x ++ Σ)). subst. auto.
  rewrite app_length in H1. assert (length Σ <= length Σ'). lia.
  unfold Subq. unfold_N. intuition. simpl in *. apply Nat.ltb_lt in H3. apply Nat.ltb_lt. lia.
Qed.

Lemma open_tm'_len : forall {A} {Γ Γ' : list A} {t}, length Γ = length Γ' -> open_tm' Γ t = open_tm' Γ' t.
  intros.  unfold open_tm'. rewrite H. auto.
Qed.

Lemma open_ty'_len : forall {A} {Γ Γ' : list A} {T}, length Γ = length Γ' -> open_ty' Γ T = open_ty' Γ' T.
  intros.  unfold open_ty'. rewrite H. auto.
Qed.

Lemma openq'_len : forall {A} {Γ Γ' : list A} {q}, length Γ = length Γ' -> openq' Γ q = openq' Γ' q.
  intros.  unfold openq'. rewrite H. auto.
Qed.

Lemma open_preserves_size: forall t x j, tm_size t = tm_size (open_rec_tm j (tvar x) t).
  induction t; intros; simpl; eauto.
  destruct v. auto. destruct (Nat.eqb j i); auto.
Qed.

Lemma open_ty_preserves_size: forall T d j, ty_size T = ty_size (open_rec_ty j d T).
  induction T; intros; simpl; eauto.
Qed.

Lemma splice_qual_empty : forall {k}, splice_qual k ∅ = ∅.
  intros. simpl. unfold_q. repeat f_equal.
  apply N_lift_eq. nlift. unfold_N. intuition.
Qed.
#[global] Hint Resolve splice_qual_empty : core.

Lemma closed_qual_ldom : forall {Σ : senv}, closed_Qual 0 0 (length Σ) (Qdom Σ).
  intros. unfold_Q; unfold_N; unfold N_lift; intuition.
Qed.
#[global] Hint Resolve closed_qual_ldom : core.

(* This property is specific to the restricted version of the system we consider here *)
Lemma qstp_inv : forall {Γ Σ d1 d2}, qstp Γ Σ d1 d2 -> d1 ⊑↑ d2.
  intros. inversion H. auto.
Qed.

Lemma splice_tenv_length : forall {n Γ}, length (splice_tenv n Γ) = length Γ.
  intros. unfold splice_tenv. rewrite map_length. auto.
Qed.

Lemma closed_tm_monotone : forall {t b l f}, closed_tm b f l t -> forall {b' f' l'}, b <= b' -> f <= f' -> l <= l' -> closed_tm b' f' l' t.
intros T. induction T; simpl in *; intuition; eauto. destruct v; intuition. eapply IHT; eauto. lia.
Qed.

Lemma closed_ty_monotone : forall {T b l f}, closed_ty b f l T -> forall {b' f' l'}, b <= b' -> f <= f' -> l <= l' -> closed_ty b' f' l' T.
Proof.
  intros T b l f H. generalize dependent b. induction T; unfold_Q; intuition eauto 3 with arith.
Qed.
#[global] Hint Resolve closed_ty_monotone : core.

Lemma closed_tm_open_id : forall {t b f l}, closed_tm b f l t -> forall {n}, b <= n -> forall {x}, (open_rec_tm n x t) = t.
intros t b f l H. generalize dependent b. induction t; intros; simpl in *; intuition;
    try solve [erewrite IHt1; eauto; erewrite IHt2; eauto; lia | erewrite IHt; eauto; lia].
  destruct v eqn:Eqv; auto. bdestruct (n =? i); auto. lia.
Qed.

Lemma closed_ty_open_id : forall {t b f l}, closed_ty b f l t -> forall {n}, b <= n -> forall {x}, (open_rec_ty n x t) = t.
intros t b f l H. generalize dependent b. induction t; intros; simpl in *; intuition.
erewrite IHt1; eauto; erewrite IHt2; eauto. repeat erewrite closed_qual_open_id; eauto. lia. lia.
  erewrite IHt; eauto. eapply closed_ty_monotone; eauto; lia.
Qed.

Lemma closed_tm_open' : forall {T b f l}, closed_tm (S b) f l T -> forall {x}, x <= f -> forall {t}, closed_tm 0 x l t -> closed_tm b f l (open_rec_tm b t T).
induction T; intros; simpl in *; intuition;
  try solve [eapply IHT1; eauto | eapply IHT2; eauto | eapply IHT; eauto ].
  destruct v; auto. bdestruct (b =? i); subst. eapply closed_tm_monotone; eauto; lia.
  simpl. lia.
Qed.

Lemma closed_ty_open' : forall {T b f l}, closed_ty (S b) f l T -> forall {x}, x <= f -> forall {d}, closed_Qual 0 x l (Q_lift d) -> closed_ty b f l (open_rec_ty b d T).
  induction T; intros; simpl in *; intuition.
  1,2 : rewrite Q_lift_open_qual; eapply closed_qual_open'; eauto.
  all: try solve [eapply IHT1; eauto | eapply IHT2; eauto | eapply IHT; eauto ].
  erewrite closed_ty_open_id; eauto. lia.
Qed.

Lemma splice_tm_id : forall {T b f l}, closed_tm b f l T -> (splice f T ) = T.
induction T; intros; simpl in *; auto; intuition;
    try solve [erewrite IHT1; eauto; erewrite IHT2; eauto | erewrite IHT; eauto].
    destruct v; auto. destruct (le_lt_dec f i) eqn:Heq. lia. auto.
Qed.

Lemma splice_ty_id : forall {T b f l},
  closed_ty b f l T ->
  (splice_ty f T) = T.
induction T; intros; simpl in *; auto; f_equal; intuition eauto using splice_qual_id.
eapply IHT; eapply closed_ty_monotone; eauto; lia.
Qed.

Lemma splice_tm_open : forall {T j n m}, splice n (open_rec_tm j (varF (m + n)) T) = open_rec_tm j (varF (S (m + n))) (splice n T).
  induction T; intros; simpl; auto;
    try solve [erewrite IHT1; eauto; erewrite IHT2; eauto | erewrite IHT; eauto].
  destruct v; simpl. destruct (le_lt_dec n i) eqn:Heq; auto.
  destruct (PeanoNat.Nat.eqb j i) eqn:Heq; auto.
  simpl. destruct (le_lt_dec n (m + n)) eqn:Heq'. auto. lia.
Qed.

Lemma splice_ty_open : forall {T j n m}, splice_ty n (open_rec_ty j (just_fv (m + n)) T) = open_rec_ty j (just_fv (S (m + n))) (splice_ty n T).
  induction T; intros; simpl; auto;
    try solve [erewrite IHT1; eauto; erewrite IHT2; eauto | erewrite IHT; eauto]. rewrite splice_qual_open. rewrite splice_qual_open. rewrite IHT1. rewrite IHT2. auto.
Qed.

Lemma splice_tm_open' : forall {T} {A} {D : A} {ρ ρ'}, splice (length ρ') (open_tm' (ρ ++ ρ') T) = open_tm' (ρ ++ D :: ρ') (splice (length ρ') T).
  intros. unfold open_tm'.
  replace (length (ρ ++ ρ')) with ((length ρ) + (length ρ')).
  replace (S (length (ρ ++ D :: ρ'))) with (S (S (length ρ) + (length ρ'))).
  replace (length (ρ ++ D :: ρ')) with (S ((length ρ) + (length ρ'))).
  rewrite <- splice_tm_open. auto.
  all: rewrite app_length; simpl; lia.
Qed.

Lemma splice_qual_open' : forall {d} {A} {D : A} {ρ ρ'}, splice_qual (length ρ') (openq' (ρ ++ ρ') d) = openq' (ρ ++ D :: ρ') (splice_qual (length ρ') d).
  intros. unfold openq'. unfold openq.
  replace (length (ρ ++ ρ')) with ((length ρ) + (length ρ')).
  replace (S (length (ρ ++ D :: ρ'))) with (S (S (length ρ) + (length ρ'))).
  replace (length (ρ ++ D :: ρ')) with (S ((length ρ) + (length ρ'))).
  rewrite <- splice_qual_open. auto.
  all: rewrite app_length; simpl; lia.
Qed.

Lemma splice_ty_open' : forall {T} {A} {D : A} {ρ ρ'}, splice_ty (length ρ') (open_ty' (ρ ++ ρ') T) = open_ty' (ρ ++ D :: ρ') (splice_ty (length ρ') T).
  intros. unfold open_ty'. unfold open_ty.
  replace (length (ρ ++ ρ')) with ((length ρ) + (length ρ')).
  replace (S (length (ρ ++ D :: ρ'))) with (S (S (length ρ) + (length ρ'))).
  replace (length (ρ ++ D :: ρ')) with (S ((length ρ) + (length ρ'))).
  rewrite <- splice_ty_open. auto.
  all: rewrite app_length; simpl; lia.
Qed.

Lemma splice_tm_closed : forall {T b n m l}, closed_tm b (n + m) l T -> closed_tm b (S (n + m)) l (splice m T).
  induction T; simpl; intros; intuition.
  destruct v; intuition.
  destruct (le_lt_dec m i) eqn:Heq; simpl; lia.
Qed.

Lemma splice_Qual_closed : forall {d b n m l},
    closed_Qual b (n + m)     l d ->
    forall {i}, i <= m -> closed_Qual b (S (n + m)) l (splice_Qual i d).
Proof.
  intros. qual_destruct d. unfold_Q. intuition.
Qed.

Lemma splice_ty_closed : forall {T b n m l}, closed_ty b (n + m) l T -> forall {i}, i <= m -> closed_ty b (S (n + m)) l (splice_ty i T).
  induction T; simpl; intros; intuition.
  1,2 : rewrite Q_lift_splice_qual; apply splice_Qual_closed; auto.
  erewrite splice_ty_id; eauto. eapply closed_ty_monotone; eauto. lia.
Qed.

Lemma splice_closed' : forall {T b l} {A} {D : A} {ρ ρ'},
    closed_tm b (length (ρ ++ ρ')) l T ->  closed_tm b (length (ρ ++ D :: ρ')) l (splice (length ρ') T).
  intros. rewrite app_length in H.
  replace (length (ρ ++ D :: ρ')) with (S (length ρ) + (length ρ')).
  apply splice_tm_closed. auto. simpl. rewrite app_length. simpl. lia.
Qed.

Lemma splice_qual_closed' : forall {d b l} {A} {D : A} {ρ ρ'},
    closed_Qual b (length (ρ ++ ρ')) l d -> closed_Qual b (length (ρ ++ D :: ρ')) l (splice_Qual (length ρ') d).
  intros. rewrite app_length in H.
  replace (length (ρ ++ D :: ρ')) with (S (length ρ) + (length ρ')).
  eapply splice_Qual_closed; eauto. simpl. rewrite app_length. simpl. lia.
Qed.

Lemma splice_ty_closed' : forall {T b l} {A} {D : A} {ρ ρ'},
    closed_ty b (length (ρ ++ ρ')) l T -> closed_ty b (length (ρ ++ D :: ρ')) l (splice_ty (length ρ') T).
  intros. rewrite app_length in H.
  replace (length (ρ ++ D :: ρ')) with (S (length ρ) + (length ρ')).
  eapply splice_ty_closed; eauto. simpl. rewrite app_length. simpl. lia.
Qed.

Lemma splice_ty_closed'' : forall {T x b l k}, closed_ty b x l T -> k <= x -> closed_ty b (S x) l (splice_ty k T).
  induction T; simpl; intros; intuition.
  1,2: rewrite Q_lift_splice_qual; unfold_Q; intuition.
  erewrite splice_ty_id; eauto.
  eapply closed_ty_monotone; eauto. lia.
Qed.

Lemma splice_qual_open'' : forall {k df d},
    splice_qual k (openq df d) =
    openq (splice_qual k df) (splice_qual k d).
Proof.
  intros. qual_destruct d; qual_destruct df; simpl.
  unfold openq. unfold_q. destruct (bvs 0); auto.
  unfold_n. repeat f_equal. apply functional_extensionality. intros.
  bdestruct (x =? k); bdestruct (x <? k); intuition.
Qed.

Lemma splice_qual_qplus_dist : forall {i k d},
    k <= i -> (splice_qual k d ⊕ S i) = splice_qual k (d ⊕ i).
Proof.
  intros. qual_destruct d. simpl. unfold_q. unfold_n. repeat f_equal. apply functional_extensionality. intuition. bdestruct (x =? k). subst. simpl. apply Nat.eqb_neq. lia. bdestruct (x <? k). destruct (fvs x); auto. bdestruct (x =? i); bdestruct (x =? S i); intuition.
  destruct (fvs (Init.Nat.pred x)); auto. bdestruct ((x =? S i)); bdestruct (Init.Nat.pred x =? i); intuition.
Qed.

Lemma splice_Qual_qplus_id : forall {i k l d},
    closed_Qual 0 i l (Q_lift d) -> i < k -> splice_Qual k (Q_lift (d ⊕ i)) = (Q_lift (d ⊕ i)).
Proof.
  intros. qual_destruct d. unfold_Q. unfold_q. repeat rewrite N_lift_or. repeat rewrite N_lift_one. repeat rewrite N_lift_empty. repeat f_equal. unfold_N. apply functional_extensionality. intros. apply propositional_extensionality. intuition.
  - bdestruct (x =? i). right. auto. left. bdestruct (x <? k); intuition. assert (x > k) by lia. intuition. apply H1 in H6. lia.
  - subst. apply H1 in H4. lia.
  - destruct (fvs (Init.Nat.pred x)) eqn:Eqm. left. unfold N_lift. auto. right. apply H1 in H4. lia.
Qed.

Lemma splice_qual_qplus_id : forall {i k l d},
    closed_Qual 0 i l (Q_lift d) -> i < k -> splice_qual k (d ⊕ i) = (d ⊕ i).
Proof.
  intros. pose proof (splice_Qual_qplus_id H H0). unfold_Q. unfold_N. qual_destruct d. unfold Q_lift,N_lift in *. unfold_q. unfold_n. repeat f_equal. apply functional_extensionality. intuition. bdestruct (x=?k).
  - subst. bdestruct (k =? i); intuition. destruct (fvs k) eqn:Eq; intuition. apply H2 in Eq. lia.
  - bdestruct (x <? k); intuition. destruct (fvs x) eqn:Eq1;destruct (fvs (Init.Nat.pred x)) eqn:Eq2; bdestruct (x =? i); bdestruct (Init.Nat.pred x =? i); intuition. apply H2 in Eq1. lia.  apply H2 in Eq2. lia.
Qed.

Lemma qplus_closed_qual : forall {d b f l x},
    closed_Qual b f l (Q_lift d) ->
    forall {f'}, f <= f' -> x < f' -> closed_Qual b f' l (Q_lift (d ⊕ x)).
Proof.
  intros. qual_destruct d. rewrite Q_lift_or. unfold_Q. unfold_q. rewrite N_lift_one. rewrite N_lift_empty. unfold_N. intuition eauto using Nat.lt_le_trans. rewrite H5. auto.
Qed.
#[global] Hint Resolve qplus_closed_qual : core.

Lemma stp_closed : forall {Γ Σ T1 d1 T2 d2},
    stp Γ Σ T1 d1 T2 d2 ->
    closed_ty 0 (length Γ) (length Σ) T1
    /\ closed_Qual 0 (length Γ) (length Σ) (Q_lift d1)
    /\ closed_ty 0 (length Γ) (length Σ) T2
    /\ closed_Qual 0 (length Γ) (length Σ) (Q_lift d2).
Proof.  intros Γ Σ T1 d1 T2 d2 HS. induction HS. 1,2: qual_destruct d1; qual_destruct d2; unfold_Q; unfold_N; intuition eauto.
- qual_destruct d5. qual_destruct d6. unfold_Q. unfold_N. intuition eauto.
- intuition.
Qed.

Lemma stp_refl : forall {n T}, ty_size T < n -> forall {Γ Σ}, closed_ty 0 (length Γ) (length Σ) T -> forall {d d'}, Qstp (length Γ) (length Σ) (Q_lift d) (Q_lift d') -> stp Γ Σ T d T d'.
  induction n; try lia; destruct T; simpl; intros Hsize Γ Σ Hc d d' Hstp; intuition.
  - (*TFun*) constructor; simpl; auto. apply IHn. lia. auto. apply Qstp_refl; auto. apply IHn. unfold open_ty'. unfold open_ty. rewrite <- open_ty_preserves_size. lia. simpl. unfold open_ty'. unfold open_ty.
    eapply closed_ty_open' with (x:=S (length Γ)); eauto. unfold_Q. nlift. unfold_N. intuition. unfold openq',openq. rewrite Q_lift_open_qual. constructor. unfold_Q. nlift. unfold_N. intuition.
    unfold_Q. nlift. unfold_N.
    ndestruct (snd (fst q0) 0); intuition. eapply closed_Nats_tighten; eauto.
  - (*TRef*) constructor. auto.
    all : apply IHn; try lia; auto. all: unfold_Q; nlift; unfold_N; intuition.
Qed.

Lemma stp_refl_qual : forall {Γ Σ T0 d0 T1 d1 d2},
  stp Γ Σ T0 d0 T1 d1 ->
  closed_Qual 0 (length Γ) (length Σ) (Q_lift d2) ->
  stp Γ Σ T0 d2 T1 d2.
intros. induction H.
  - eapply stp_refl; eauto. constructor. Qcrush.
  - constructor; auto. Qcrush.
  - constructor; auto. Qcrush.
  - apply s_trans with (d2:=d2) (T2:=T2).
    apply IHstp1. Qcrush.
    apply IHstp2. Qcrush.
Qed.

Lemma stp_qstp_inv : forall {Γ Σ T1 d1 T2 d2}, stp Γ Σ T1 d1 T2 d2 -> Qstp (length Γ) (length Σ) (Q_lift d1) (Q_lift d2).
  intros Γ Σ T1 d1 T2 d2 HS. induction HS; intuition. eapply qstp_trans; eauto.
Qed.

Lemma weaken_qstp_gen : forall {Γ1 Γ2 Σ d1 d2},
    Qstp (length (Γ1 ++ Γ2)) Σ d1 d2 ->
    forall T', Qstp (length ((splice_tenv (length Γ2) Γ1) ++ T' :: Γ2)) Σ (splice_Qual (length Γ2) d1) (splice_Qual (length Γ2) d2).
Proof.
  intros Γ1 Γ2 Σ d1 d2 HSTP (T', d'). inversion HSTP. subst.
  qual_destruct d1. qual_destruct d2.
  constructor; unfold_Q; intuition.
  rewrite app_length in *. rewrite splice_tenv_length. simpl. rewrite <- plus_n_Sm. intuition.
Qed.

Lemma weaken_stp_gen : forall {Γ1 Γ2 Σ T1 d1 T2 d2},  stp (Γ1 ++ Γ2) Σ T1 d1 T2 d2 ->
    forall T', stp ((splice_tenv (length Γ2) Γ1) ++ T' :: Γ2) Σ (splice_ty (length Γ2) T1) (splice_qual (length Γ2) d1) (splice_ty (length Γ2) T2) (splice_qual (length Γ2) d2).
Proof. intros Γ1 Γ2 Σ T1 d1 T2 d2  Hstp T'. remember (Γ1 ++ Γ2)  as Γ. generalize dependent Γ1. induction Hstp; intros.
- subst. constructor. qual_destruct d1. qual_destruct d2. unfold_Q. unfold_q. repeat rewrite N_lift_splice. rewrite app_length in *. rewrite splice_tenv_length. simpl. rewrite <- plus_n_Sm. intuition eauto.
  - assert (stp Γ Σ (TRef T1) d1 (TRef T2) d2). { constructor; intuition. } subst.
    apply stp_closed in H0 as Hcl. intuition. simpl in *.
    replace (splice_ty (length Γ2) T1) with T1. replace (splice_ty (length Γ2) T2) with T2.
    constructor; auto; fold splice_ty.
    qual_destruct d1. qual_destruct d2. unfold_Q. unfold_q. repeat rewrite N_lift_splice. rewrite app_length in *. rewrite splice_tenv_length. simpl. rewrite <- plus_n_Sm. simpl. intuition eauto.
    1,2 : erewrite splice_ty_id; eauto; eapply closed_ty_monotone; eauto; lia.
  - assert (stp Γ Σ (TFun d1 d2 T1 T2) d5 (TFun d3 d4 T3 T4) d6). { constructor; intuition. } intros.
    subst. simpl in *. apply qstp_closed in H1 as Hcl. intuition.
    qual_destruct d1. qual_destruct d2. qual_destruct d3. qual_destruct d4. qual_destruct d5. qual_destruct d6.
    constructor; try fold splice_ty.
    1-3: rewrite app_length in *; rewrite splice_tenv_length in *; simpl; rewrite <- plus_n_Sm; unfold_Q; unfold_q; repeat rewrite N_lift_splice in *; intuition eauto using splice_ty_closed.
    specialize (IHHstp1 Γ1). intuition.
    specialize (IHHstp2 ((T3, (fvs1, bvs1, lcs1)) :: Γ1)). intuition.
    repeat rewrite <- splice_ty_open'. repeat rewrite <- splice_qual_open'. unfold open_ty' in *. unfold open_ty in *. unfold openq' in *. unfold openq in *. rewrite app_length in *. rewrite splice_tenv_length. simpl. auto.
  - intros. specialize (IHHstp1 Γ1). specialize (IHHstp2 Γ1). intuition.
    eapply s_trans; eauto.
Qed.

Lemma weaken_stp : forall {Γ Σ T1 d1 T2 d2}, stp Γ Σ T1 d1 T2 d2 -> forall T', stp (T' :: Γ) Σ T1 d1 T2 d2.
Proof. intros Γ Σ T1 d1 T2 d2 HST. specialize (@weaken_stp_gen [] Γ Σ T1 d1 T2 d2) as Hsp. simpl in *.  specialize (Hsp HST).
       intros.  specialize (Hsp T'). apply stp_closed in HST. intuition. replace (splice_ty (length Γ) T1) with T1 in Hsp.
       replace (splice_ty (length Γ) T2) with T2 in Hsp.
       replace (splice_qual (length Γ) d1) with d1 in Hsp.
       replace (splice_qual (length Γ) d2) with d2 in Hsp. intuition.
       1,2 : erewrite  splice_qual_id; eauto.
       1,2 : erewrite splice_ty_id; eauto.
Qed.

Lemma weaken_stp' : forall {Γ Σ T1 d1 T2 d2}, stp Γ Σ T1 d1 T2 d2 -> forall Γ', stp (Γ' ++ Γ) Σ T1 d1 T2 d2.
  intros. induction Γ'.
  - simpl. auto.
  - replace ((a :: Γ') ++ Γ) with (a :: (Γ' ++ Γ)).
    apply weaken_stp. auto. simpl. auto.
Qed.
Lemma weaken_stp_store : forall {Σ Γ T1 d1 T2 d2}, stp Γ Σ T1 d1 T2 d2 -> forall Σ', stp Γ (Σ' ++ Σ) T1 d1 T2 d2.
Proof.
  intros Σ Γ T1 d1 T2 d2 HSTP. induction HSTP; intros.
  1-3: constructor; auto; unfold_Q; rewrite app_length; intuition eauto using closed_Nats_mono,le_plus_r.
  specialize (IHHSTP1 Σ'). specialize (IHHSTP2 Σ'). eapply s_trans in IHHSTP2; eauto.
Qed.

Lemma weaken_stp_store_ext : forall {Σ Γ T1 d1 T2 d2}, stp Γ Σ T1 d1 T2 d2 -> forall {Σ'}, Σ' ⊇ Σ ->  stp Γ Σ' T1 d1 T2 d2.
  intros. unfold extends in H0. destruct H0. subst. apply weaken_stp_store. auto.
Qed.

Lemma narrowing_Qstp_gen : forall{Γ1 U du Γ2 Σ d1 d2},
    Qstp (length (Γ1 ++ (U,du) :: Γ2)) (length Σ) d1 d2 ->
    forall {V dv}, stp Γ2 Σ V dv U du ->
              Qstp (length (Γ1 ++ (V,dv) :: Γ2)) (length Σ) d1 d2.
  intros Γ1 U du Γ2 Σ d1 d2 HQ V dv HSTP.
  inversion HQ. subst. constructor.
  auto. rewrite app_length in *. simpl in *. auto.
Qed.

Lemma narrowing_stp_gen : forall{Γ1 U du Γ2 Σ T1 d1 T2 d2}, stp (Γ1 ++ (U,du) :: Γ2) Σ T1 d1 T2 d2 -> forall {V dv}, (stp Γ2 Σ V dv U du) -> stp (Γ1 ++ (V,dv) :: Γ2) Σ T1 d1 T2 d2.
Proof. intros Γ1 U du Γ2 Σ T1 d1 T2 d2 HST. remember (Γ1 ++ (U,du) :: Γ2) as Γ.
  generalize dependent Γ1; induction HST; intros; intuition.
  1,2: subst; constructor; auto; eapply narrowing_Qstp_gen; eauto.
  - subst. constructor; auto. 1,2: eapply closed_ty_monotone; eauto; repeat rewrite app_length; simpl; auto. eapply narrowing_Qstp_gen; eauto.
    unfold open_ty' in *. unfold openq' in *.
    rewrite app_length in *. simpl in *.
    repeat rewrite app_comm_cons.
    eapply IHHST2; eauto.
  - subst. specialize (IHHST1 Γ1).  specialize (IHHST2 Γ1). intuition.
    specialize (H0 V dv).  specialize (H1 V dv). intuition.  eapply s_trans; eauto.
Qed.

Lemma narrowing_stp : forall{U du Γ Σ T1 d1 T2 d2}, stp ((U,du) :: Γ) Σ T1 d1 T2 d2 -> forall {V dv}, stp Γ Σ V dv U du -> stp ((V,dv) :: Γ) Σ T1 d1 T2 d2.
  intros. specialize (@narrowing_stp_gen [] U du Γ Σ T1 d1 T2 d2) as narrow. simpl in *. eapply narrow; eauto.
Qed.

Lemma stp_scale_plus : forall {Γ Σ T1 d1 T2 d2}, stp Γ Σ T1 d1 T2 d2 -> forall {x}, x < length Γ -> stp Γ Σ T1 (d1 ⊕ x) T2 (d2 ⊕ x).
  intros Γ Σ T1 d1 T2 d2 HSTP. induction HSTP; intros; econstructor; unfold_Q; nlift; unfold_N; intuition.
Qed.

Lemma saturated_empty : forall {Γ Σ}, saturated Γ Σ ∅.
  intros. unfold saturated. intros. intuition.
Qed.
#[global] Hint Resolve saturated_empty : core.

Lemma saturated_empty_tenv : forall {q Σ}, closed_Qual 0 0 (length Σ) (Q_lift q) -> saturated [] Σ q.
  intros. unfold saturated. intros.
  inversion H. subst. simpl in *. unfold_q. unfold N_lift in H0.
  simpl in H0. apply H1 in H0. lia.
Qed.
#[global] Hint Resolve saturated_empty_tenv : core.

Lemma saturated_cons : forall {Γ Σ q}, saturated Γ Σ q -> forall {T q'}, saturated ((T, q') :: Γ) Σ q.
intros. unfold saturated in *. intros. apply H in H0. unfold saturated_var in *. destruct H0 as [U H0]. destruct H0 as [q0 H0]. intuition. exists U. exists q0. intuition. rewrite indexr_skip; eauto. apply indexr_var_some' in H1. lia.
Qed.

Lemma saturated_app : forall {Γ' Γ Σ q}, saturated Γ Σ q -> saturated (Γ' ++ Γ) Σ q.
  induction Γ'; intros; simpl; intuition.
  apply saturated_cons; auto.
Qed.

Lemma saturated_qplus : forall {Γ Σ x T q}, indexr x Γ = Some (T, q) -> closed_Qual 0 x (length Σ) (Q_lift q) -> saturated Γ Σ q -> saturated Γ Σ (q ⊕ x).
  intros. unfold saturated. intros.
qual_destruct q. unfold saturated,saturated_var in *. unfold_Q. nlift. unfold_N. intuition.
  - specialize (H1 x0 H4). destruct H1 as [U [q' H1]]. exists U,q'. intuition.
  - subst. exists T, (fvs, bvs, lcs). intuition.
Qed.

Lemma saturated_openq : forall {Γ Σ d1 d2}, saturated Γ Σ d1 -> saturated Γ Σ (openq ∅ d2) -> saturated Γ Σ (openq d1 d2).
intros. qual_destruct d1. qual_destruct d2. unfold saturated, saturated_var, openq in *. intros. simpl in *. unfold_q.
    ndestruct (bvs0 0); intuition. simpl in *. nlift. ndestruct (fvs x).
  - specialize (H x H3). destruct H as [U [q' H]]. exists U,q'. unfold_Q. nlift. unfold_N. intuition.
  - assert (H': N_or (N_lift fvs0) N_empty x). unfold_N. intuition. specialize (H0 x H'). destruct H0 as [U [q' H0]]. exists U,q'. unfold_Q. nlift. unfold_N. intuition.
    + left. eapply H5 in H11. intuition.
    + exfalso; eauto.
    + left. eapply H9 in H11. intuition.
Qed.

Lemma saturated_qor : forall {Γ Σ q1 q2}, saturated Γ Σ q1 -> saturated Γ Σ q2 -> saturated Γ Σ (q1 ⊔ q2).
intros. qual_destruct q1. qual_destruct q2. unfold saturated in *. intros. unfold saturated_var in *. simpl in *.
unfold_q. nlift.
ndestruct (fvs x).
  - specialize (H x H2). destruct H as [U [q' H]]. exists U,q'. unfold_Q. nlift. unfold_N. intuition.
  - assert (Hfvs0: N_lift fvs0 x). { unfold_N. intuition. }
    specialize (H0 x Hfvs0). destruct H0 as [U [q' H0]]. exists U,q'. unfold_Q. nlift. unfold_N. intuition.
Qed.

Lemma saturated_just_loc : forall {Γ Σ l}, saturated Γ Σ (just_loc l).
  intros. unfold saturated. intros. simpl in *.
  unfold_q. unfold N_lift in *. unfold_n. discriminate.
Qed.
#[global] Hint Resolve saturated_just_loc : core.

Lemma saturated_qand : forall {Γ Σ q1 q2}, saturated Γ Σ q1 -> saturated Γ Σ q2 -> saturated Γ Σ (q1 ⊓ q2).
intros. qual_destruct q1. qual_destruct q2. unfold saturated in *. intros. unfold saturated_var in *. simpl in *.
  assert (Hx : $ (x) ∈ᵥ (fvs, bvs, lcs) /\ $ (x) ∈ᵥ (fvs0, bvs0, lcs0)). {
    simpl. unfold_Q. nlift. unfold_N. intuition.
  }
  intuition. simpl in *. apply H in H2. apply H0 in H3. destruct H2 as [U' [q' H2]]. destruct H3 as [U'' [q'' H3]]. intuition. rewrite H4 in H2. inversion H2. subst. exists U'',q''. intuition. unfold_Q. nlift. unfold_N. intuition.
Qed.

Lemma saturated_closed_Qual : forall {b Γ Σ q}, closed_Qual b 0 (length Σ) (Q_lift q) -> saturated Γ Σ q .
intros. unfold saturated. intros. qual_destruct q. unfold_q. exfalso. Qcrush. intuition eauto.
Qed.

Lemma weaken_store_saturated : forall {Γ Σ q}, saturated Γ Σ q -> forall {Σ'}, Σ' ⊇ Σ -> saturated Γ Σ' q.
  intros. unfold saturated in *. intros. specialize (H x H1).
  unfold saturated_var in *. destruct H as [U [q' H]]. exists U. exists q'. intuition. unfold_Q. intuition. eapply closed_Nats_mono; eauto. apply extends_length; auto.
Qed.

Lemma wf_tenv_empty : forall {Σ}, wf_tenv [] Σ.
  unfold wf_tenv. intros. simpl in H. discriminate.
Qed.
#[global] Hint Resolve wf_tenv_empty : core.

Lemma wf_tenv_cons : forall {Γ Σ}, wf_tenv Γ Σ -> forall {T q}, saturated Γ Σ q -> wf_tenv ((T, q) :: Γ) Σ.
  intros. unfold wf_tenv. intros. bdestruct (x =? (length Γ)).
  - subst. rewrite indexr_head in H1. inversion H1. subst. apply saturated_cons. auto.
  - rewrite indexr_skip in H1; auto. apply H in H1. apply saturated_cons. auto.
Qed.

Fixpoint has_type_closed  {Γ φ Σ t T d} (ht : has_type Γ φ Σ t T d) :
  closed_Qual 0 (length Γ) (length Σ) (Q_lift φ) /\
  closed_tm 0 (length Γ) (length Σ) t /\
  closed_ty 0 (length Γ) (length Σ) T /\
  closed_Qual 0 (length Γ) (length Σ) (Q_lift d).
Proof.
  destruct ht; intuition; try apply has_type_closed in ht; try apply has_type_closed in ht1;
  try apply has_type_closed in ht2; simpl in *; intuition eauto.
  - apply indexr_var_some' in H. auto.
  - apply indexr_var_some' in H.
    eapply closed_ty_monotone; eauto. lia.
  - apply indexr_var_some' in H.
    eapply qplus_closed_qual; eauto. lia.
  - unfold_Q. unfold_N. intuition eauto.
  - unfold openq in *. rewrite Q_lift_open_qual. qual_destruct d1. qual_destruct d2. unfold_Q. unfold_N. unfold_q.
    (* NOTE: requires some complex strategy <2023-05-22, David Deng> *)
    ndestruct (bvs0 0); intuition.
  - apply indexr_var_some' in H0. auto.
  - unfold_Q. unfold_q. rewrite N_lift_one,N_lift_empty in *. intuition eauto.
  - eapply closed_ty_monotone; eauto; lia.
  - apply stp_closed in H. intuition.
  - apply stp_closed in H. intuition.
Qed.

Lemma openq_subqual : forall {d1 d2 φ}, Subq (Q_lift d1) (Q_lift φ) -> Subq (Q_lift (openq ∅ d2)) (Q_lift φ) -> Subq (Q_lift (openq d1 d2)) (Q_lift φ).
intros. qual_destruct d1. qual_destruct d2. qual_destruct φ. unfold openq in *. rewrite Q_lift_open_qual in *. unfold_Q. unfold_N. unfold_q.
ndestruct (bvs0 0); intuition.
Qed.

Fixpoint has_type_filter {Γ φ Σ t T d} (ht : has_type Γ φ Σ t T d) : d ⊑↑ φ.
destruct ht; try apply subq_empty. all: try apply openq_subqual; eauto.
Qed.

Fixpoint has_type_saturated {Γ φ Σ t T d} (wfG : wf_tenv Γ Σ) (ht : has_type Γ φ Σ t T d) : saturated Γ Σ d.
  destruct ht; intuition. eapply saturated_qplus; eauto.
  apply saturated_openq; auto. apply has_type_saturated in ht2; auto.
Qed.

Lemma indexr_splice_tenv : forall {Γ1 i Γ2 U du},
    indexr i (Γ1 ++ Γ2) = Some (U, du) ->
    forall {k}, k <= i -> (length Γ2) <= i -> indexr i (splice_tenv k Γ1 ++ Γ2) = Some (splice_ty k U, splice_qual k du).
  induction Γ1; intros; simpl in *; intuition. apply indexr_var_some' in H. lia.
  rewrite app_length in *. rewrite splice_tenv_length.
  destruct (Nat.eqb i (length Γ1 + length Γ2)) eqn:Heq. inversion H. subst.
  simpl. auto. apply IHΓ1; eauto.
Qed.

Lemma weaken_saturated : forall {Γ1 Γ2 Σ d1},
    saturated (Γ1 ++ Γ2) Σ d1 ->
    let k := (length Γ2) in forall X, saturated ((splice_tenv k Γ1) ++ X :: Γ2) Σ (splice_qual k d1).
  intros. unfold saturated. intros. bdestruct (x <? k).
  - specialize (H x). apply splice_qual_mem_lt in H0; auto. intuition. unfold saturated_var in *. destruct H2 as [U H2]. destruct H2 as [q0 H2]. exists U. exists q0. intuition.
    rewrite indexr_skips in H; try lia.
    rewrite indexr_skips. rewrite indexr_skip; auto. lia. simpl. lia.
    replace q0 with (splice_qual k q0). repeat rewrite Q_lift_splice_qual. unfold_Q. intuition.
    eapply splice_qual_id. eapply closed_Qual_monotone; eauto. lia.
  - bdestruct (x =? k).
    + subst. simpl in *. qual_destruct d1. unfold_q. rewrite N_lift_splice in H0. unfold_N. intuition.
    + destruct x. lia. specialize (H x). assert (Hx : x >= k). lia.
      assert ($ (x) ∈ᵥ d1). qual_destruct d1. unfold_q. rewrite N_lift_splice in H0. unfold_N. intuition.
simpl in *. intuition. unfold saturated_var in *. intuition.
      destruct H4 as [U H4]. destruct H4 as [q0 H4].
      exists (splice_ty k U). exists (splice_qual k q0). intuition. eapply indexr_splice_tenv; eauto. rewrite <- indexr_insert_ge; eauto. simpl. lia. all: repeat rewrite Q_lift_splice_qual; unfold_Q; intuition.
Qed.

Lemma weaken_gen : forall {t Γ1 Γ2 φ Σ T d},
    has_type (Γ1 ++ Γ2) φ Σ t T d ->
    let k := (length Γ2) in
    forall X, has_type ((splice_tenv k Γ1) ++ X :: Γ2) (splice_qual k φ) Σ (splice k t) (splice_ty k T) (splice_qual k d).
  intros t Γ1 Γ2 φ Σ T d HT. remember (Γ1 ++ Γ2) as Γ. generalize dependent Γ1. generalize dependent Γ2.
  induction HT; intros; subst.
  - (* tunit *) simpl. rewrite n_splice_id; eauto. constructor.
    qual_destruct φ. rewrite Q_lift_splice_qual. rewrite app_length in *. rewrite splice_tenv_length. unfold_Q. intuition. rewrite <- plus_n_Sm. eauto using N_splice_closed. unfold_n. intuition.
  - (* t_var *)
    (* simpl. *)
    destruct (le_lt_dec k x) eqn:Heq.
    + (* |Γ2| <= x < |Γ1|+|Γ2|*)
      erewrite <- splice_qual_qplus_dist; eauto. simpl. rewrite Heq. constructor.
      rewrite <- indexr_insert_ge. apply indexr_splice_tenv; eauto. lia.
      rewrite splice_qual_qplus_dist; try lia. repeat rewrite Q_lift_splice_qual. rewrite Subq_splice_dist. auto.
rewrite Q_lift_splice_qual. qual_destruct φ. unfold_Q. rewrite app_length in *. rewrite splice_tenv_length. simpl. rewrite <- plus_n_Sm. intuition. apply splice_ty_closed''; intuition.
      rewrite Q_lift_splice_qual. unfold_Q. intuition.
    + (* |Γ2| > x *)
      erewrite splice_qual_qplus_id; eauto. simpl. rewrite Heq. constructor.
      rewrite <- indexr_insert_lt; auto. rewrite indexr_skips; auto.
      rewrite indexr_skips in H; auto.
      erewrite splice_ty_id. auto.
      eapply closed_ty_monotone; eauto. lia.
      1,2: rewrite Q_lift_splice_qual.
      erewrite <- @splice_Qual_qplus_id with (k:=k); eauto. rewrite <- @Subq_splice_dist with (i:=k) in H0; auto.
      rewrite app_length in *. rewrite splice_tenv_length. qual_destruct φ. unfold_Q. unfold_N. intuition. bdestruct (x0<?k); intuition. assert (x0 > k) by lia. intuition. apply H0 in H15. lia.
      erewrite splice_ty_id; eauto. auto.
  - (* t_abs *) rewrite app_length in *. simpl. constructor.
    apply splice_closed'.
    1-3: rewrite app_length; rewrite splice_tenv_length; simpl. auto.
    1,2: repeat rewrite <- plus_n_Sm.
    1-3: repeat rewrite Q_lift_splice_qual.
    simpl in H0. intuition; unfold_Q; intuition; apply splice_ty_closed''; eauto; lia.
    1,2: unfold_Q; intuition.
    1,2: apply weaken_saturated; auto.
    rewrite app_comm_cons.
    replace ((splice_ty k T1, splice_qual k d1) :: splice_tenv k Γ1) with (splice_tenv k ((T1, d1) :: Γ1)); auto.
    replace (splice_qual k df ⊔ just_fv (length (splice_tenv k Γ1 ++ X :: Γ2)))
            with (splice_qual k (df ⊔ just_fv (length Γ1 + length Γ2))).
    subst k. rewrite <- splice_tm_open'. rewrite <- splice_ty_open'. rewrite <- splice_qual_open'.
    rewrite @open_tm'_len with (Γ':=(Γ1 ++ Γ2)). rewrite @open_ty'_len with (Γ':=(Γ1 ++ Γ2)).
    rewrite @openq'_len with (Γ':=(Γ1 ++ Γ2)).
    apply IHHT; intuition. 1-4 : repeat rewrite app_length; rewrite splice_tenv_length; auto. replace (length Γ1 + length (X :: Γ2)) with (length Γ1 + S (length Γ2)) by auto. rewrite <- plus_n_Sm. rewrite splice_qual_qplus_dist. unfold qor. unfold qor. auto. lia.
  - (* tapp *) simpl. rewrite splice_qual_open''. apply t_app with (T1:=(splice_ty k T1)) (df:=(splice_qual k df)).
    replace (TFun (splice_qual k df ⊓ splice_qual k d1)  (splice_qual k d2) (splice_ty k T1) (splice_ty k T2)) with
    (splice_ty k (TFun (df ⊓ d1) d2 T1 T2)); auto.
    apply IHHT1; auto. simpl. f_equal. rewrite <- splice_qual_qand_dist.
(* NOTE: Q: define a lemma? unfold? <2023-05-23, David Deng> *)
    unfold_q. repeat f_equal.
    apply IHHT2; auto.
    eapply splice_ty_closed'. rewrite app_length in *. rewrite splice_tenv_length. auto.
    1,2 : subst k; rewrite <- @splice_qual_empty with (k := length Γ2); rewrite <- splice_qual_open''.
    repeat rewrite Q_lift_splice_qual. rewrite Subq_splice_dist; auto.
    apply weaken_saturated; auto.
  - (* t_loc *) simpl. rewrite n_splice_id. constructor. rewrite Q_lift_splice_qual.
    eapply splice_qual_closed'. rewrite app_length in *. rewrite splice_tenv_length. unfold_Q. intuition.
    1,2: erewrite splice_ty_id; eauto; eapply closed_ty_monotone; eauto; lia.
    rewrite Q_lift_splice_qual. unfold_Q. intuition. rewrite N_lift_empty. unfold_N. intuition.
    unfold_n. intuition.
  - (* t_ref *) simpl. rewrite n_splice_id. eapply t_ref. simpl in IHHT. specialize (IHHT Γ2 Γ1). intuition. unfold_n. intuition.
  - (* t_deref *) simpl. rewrite n_splice_id. econstructor. simpl in IHHT. subst k. apply IHHT; auto. unfold_n. intuition.
  - (* t_assign *) replace (splice_qual k ∅) with (∅) by auto. replace (splice_ty k TUnit) with (TUnit) by auto. simpl. eapply t_assign.
    1-2: replace (∅) with (splice_qual k ∅) by auto.
    replace (TRef TUnit) with (splice_ty k (TRef TUnit)) by auto. apply IHHT1; auto.
    replace (TUnit) with ((splice_ty k TUnit)) by auto. apply IHHT2; auto.
  - (* t_sub *) eapply t_sub. eapply IHHT; auto.
    apply @weaken_stp_gen; eauto; lia. apply subq_splice_dist. auto.
    apply weaken_saturated; auto.
Qed.

Lemma weaken_flt : forall {Γ φ Σ t T d},
    has_type Γ φ Σ t T d ->
    forall {φ'}, Subq (Q_lift φ) (Q_lift φ') ->
                 closed_Qual 0 (length Γ) (length Σ) (Q_lift φ') ->
    has_type Γ φ' Σ t T d.
  intros Γ φ Σ t T d HT. induction HT; intros; econstructor; eauto; unfold_Q; intuition; nlift; unfold_N; intuition.
Qed.

Lemma weaken : forall {φ Σ t T d},
    has_type [] φ Σ t T d -> forall {Γ}, has_type Γ φ Σ t T d.
  intros φ Σ t T d HT. induction Γ; auto.
  specialize (@weaken_gen t [] Γ φ Σ T d) as Hsp. simpl in *.
  specialize (Hsp IHΓ a).
  apply has_type_closed in HT. intuition. simpl in *.
  replace (splice (length Γ) t) with t in Hsp.
  replace (splice_ty (length Γ) T) with T in Hsp.
  replace (splice_qual (length Γ) d) with d in Hsp.
  replace (splice_qual (length Γ) φ) with φ in Hsp. auto.
  all : symmetry.
  eapply splice_qual_id; eauto. eapply closed_Qual_monotone; eauto; lia.
  eapply splice_qual_id; eauto. eapply closed_Qual_monotone; eauto; lia.
  eapply splice_ty_id; eauto.   eapply closed_ty_monotone; eauto; lia.
  eapply splice_tm_id; eauto.      eapply closed_tm_monotone; eauto; lia.
Qed.

Lemma weaken' : forall {φ Σ t T d},
    has_type [] φ Σ t T d -> forall {φ'}, Subq (Q_lift φ) (Q_lift φ') -> forall {Γ}, closed_Qual 0 (length Γ) (length Σ) (Q_lift φ') -> has_type Γ φ' Σ t T d.
  intros. eapply weaken_flt; eauto. apply weaken. eauto.
Qed.

Lemma weaken_store : forall {Γ φ Σ t T d}, has_type Γ φ Σ t T d -> forall {Σ'}, Σ' ⊇ Σ -> has_type Γ φ Σ' t T d.
  intros Γ φ Σ t T d HT.
  induction HT; intros; intuition; econstructor; eauto;
    try solve [unfold_Q; intuition; eapply closed_Nats_mono; eauto; apply extends_length; eauto];
    try solve [eapply closed_qual_monotone; eauto; apply extends_length; auto];
    try solve [eapply closed_tm_monotone; eauto; apply extends_length; auto];
    try solve [eapply closed_ty_monotone; eauto; apply extends_length; auto];
    try solve [eapply weaken_store_saturated; eauto].
  - unfold extends in H3. destruct H3. rewrite H3.
    rewrite indexr_skips. auto. eapply indexr_var_some'. eauto.
  - eapply weaken_stp_store_ext; eauto.
Qed.

Lemma values_stuck : forall {v}, value v -> forall {t σ σ'}, step v σ t σ' -> False.
  intros. inversion H0; subst; inversion H.
Qed.

Lemma CtxOK_ext : forall {Γ φ Σ σ}, CtxOK Γ φ Σ σ -> forall {v T}, has_type Γ φ Σ v T ∅ -> value v -> CtxOK Γ φ (T :: Σ) (v :: σ).
  intros. unfold CtxOK in *. split. simpl. lia.
  intros. destruct H as [Hlen Hprev]. destruct (Nat.eqb l (length σ)) eqn:Heql.
  - simpl in *. rewrite Heql in *. inversion H3. subst.
    rewrite <- Hlen in Heql. rewrite Heql in H2. inversion H2. subst. intuition.
    eapply weaken_store; eauto. apply extends_cons.
  - simpl in *. rewrite Heql in *. rewrite <- Hlen in Heql. rewrite Heql in H2.
    specialize (Hprev _ _ _ H2 H3) as Hprev. intuition.
    eapply weaken_store; eauto. apply extends_cons.
Qed.

Lemma CtxOK_update : forall {Γ φ Σ σ}, CtxOK Γ φ Σ σ -> forall {l T}, l < length σ -> indexr l Σ = Some T -> forall {v}, has_type Γ φ Σ v T ∅ -> value v -> CtxOK Γ φ Σ (update σ l v).
  intros. unfold CtxOK in *. destruct H as [Hlen Hprev].
  split. rewrite <- update_length. auto.
  intros. destruct (Nat.eqb l l0) eqn:Heq.
  - apply Nat.eqb_eq in Heq. subst.
    apply (@update_indexr_hit _ σ l0 v) in H0. rewrite H1 in H. inversion H. subst.
    rewrite H4 in H0. inversion H0. subst. intuition.
  - apply Nat.eqb_neq in Heq. apply (@update_indexr_miss _ σ l v l0) in Heq.
    rewrite Heq in H4. eapply Hprev; eauto.
Qed.

Lemma CtxOK_empty : forall {Γ φ}, CtxOK Γ φ [] [].
  intros. constructor; intuition; simpl in H; try discriminate.
Qed.
#[global] Hint Resolve CtxOK_empty : core.

Lemma CtxOK_weaken_flt : forall {Γ φ Σ σ}, CtxOK Γ φ Σ σ -> forall {φ'}, closed_Qual 0 (length Γ) (length Σ) (Q_lift φ') -> φ ⊑↑ φ' -> CtxOK Γ φ' Σ σ.
  intros. inversion H. subst. constructor; intuition.
  all : specialize (H3 _ _ _ H4 H5); intuition.
  eapply weaken_flt; eauto.
Qed.

Lemma subst1_tenv_length : forall {v q Γ}, length ({ v |-> q }ᴳ Γ) = length Γ.
  intros. unfold subst_tenv. rewrite map_length. auto.
Qed.

Lemma subst_tenv_length : forall {v q q' Γ}, length ({ v |-> q ; q' }ᴳ Γ) = length Γ.
  intros. repeat rewrite subst1_tenv_length. auto.
Qed.

Lemma subst1_ty_id : forall {T b l}, closed_ty b 0 l T -> forall {d1}, { 0 |-> d1 }ᵀ T = T.
induction T; intros; simpl in *; auto; intuition;
                       try solve [erewrite IHT; eauto];
                       try solve [erewrite IHT1; eauto; erewrite IHT2; eauto].
  erewrite IHT1; eauto. erewrite IHT2; eauto.
  erewrite subst1_qual_id; eauto. erewrite subst1_qual_id; eauto.
Qed.

Lemma subst_ty_id : forall {b l T}, closed_ty b 0 l T -> forall {d1 d2}, { 0 |-> d1 ; d2 }ᵀ T = T.
  intros. repeat erewrite subst1_ty_id; eauto.
Qed.

Lemma subst1_tm_id : forall {t b l}, closed_tm b 0 l t -> forall {t1}, { 0 |-> t1 }ᵗ t = t.
induction t; intros; simpl in *; intuition;
                       try solve [erewrite IHt; eauto];
                       try solve [erewrite IHt1; eauto; erewrite IHt2; eauto].
destruct v; intuition.
Qed.

Lemma open_subst1_qual : forall {q b l},
    closed_Qual b 0 l (Q_lift q) ->
    forall {k d1},
    [[k ~> d1 ]]ᵈ q = { 0 |-> d1 }ᵈ ([[k ~> (just_fv 0)]]ᵈ q).
intros. qual_destruct d1. qual_destruct q. unfold_Q. unfold_q.
destruct (bvs0 k) eqn:Eq; simpl; f_equal.
- assert (Ht: n_or fvs0 (n_one 0) 0 = true). { apply (proj1 (reflect_iff _ _ (n_reflect_true _ _))). nlift. unfold_N. intuition. } rewrite Ht. apply Q_lift_eq. unfold_Q. nlift. unfold_N. repeat f_equal; apply functional_extensionality; intros; apply propositional_extensionality; intuition. exfalso; eauto 3 with arith.
- destruct (fvs0 0) eqn:Eq2; apply Q_lift_eq; unfold_Q; nlift; unfold_N; repeat f_equal; apply functional_extensionality; intuition; apply propositional_extensionality; intuition. all: exfalso; eauto 3 with arith.
Qed.

Lemma open_subst1_ty : forall {T b l},
    closed_ty b 0 l T ->
    forall {k d1},
      [[k ~> d1 ]]ᵀ T = { 0 |-> d1 }ᵀ ([[k ~> (just_fv 0)]]ᵀ T).
  induction T; intros; simpl in *; intuition.
  erewrite IHT1; eauto. erewrite IHT2; eauto.
  erewrite <- open_subst1_qual; eauto. erewrite <- open_subst1_qual; eauto.
  erewrite IHT; eauto.
Qed.

Lemma open_subst1_tm : forall {t b l},
    closed_tm b 0 l t ->
    forall {k b' l' t1},
      closed_tm b' 0 l' t1 ->
      [[k ~> t1 ]]ᵗ t = { 0 |-> t1 }ᵗ ([[k ~> $ 0]]ᵗ t).
induction t; intros b loc Hc; intros; simpl in *; intuition;
    try solve [erewrite IHt; eauto];
    try solve [erewrite IHt1; eauto; erewrite IHt2; eauto].
  destruct v; intuition. bdestruct (k =? i); simpl; intuition.
Qed.

Fixpoint open_subst1_tm_comm {t : tm} :
  forall {k  g tf ff lf}, closed_tm 0 ff lf tf ->
    [[k ~> $ (g) ]]ᵗ ({0 |-> tf }ᵗ t) = {0 |-> tf }ᵗ ([[ k ~> $ (S g) ]]ᵗ  t).
    destruct t; intros; simpl; intuition;
      try solve [repeat erewrite open_subst1_tm_comm; eauto].
    destruct v; simpl.
    bdestruct (i =? 0); simpl. eapply closed_tm_open_id; eauto. lia. auto.
    bdestruct (k =? i); simpl; auto.
Qed.

Lemma open_subst1_qual_comm : forall {q : qual} {k g df ff lf},
    closed_Qual 0 ff lf (Q_lift df) ->
    [[k ~> just_fv g ]]ᵈ ({0 |-> df }ᵈ q) = {0 |-> df }ᵈ ([[ k ~> just_fv (S g) ]]ᵈ q).
  intros. qual_destruct df. qual_destruct q. unfold_q.
  ndestruct (fvs0 0); ndestruct (bvs0 k); simpl.
  - ndestruct (n_or bvs0 bvs k); ndestruct (n_or fvs0 (n_one (S g)) 0); apply Q_lift_eq; unfold_Q; nlift; unfold_N; repeat f_equal; apply functional_extensionality; intros; apply propositional_extensionality; intuition. all: exfalso; eauto.
  - ndestruct (n_or bvs0 bvs k); ndestruct (fvs0 0); apply Q_lift_eq; unfold_Q; nlift; unfold_N; repeat f_equal; apply functional_extensionality; intros; apply propositional_extensionality; intuition. all: exfalso; eauto.
  - ndestruct (bvs0 k); ndestruct (n_or fvs0 (n_one (S g)) 0); apply Q_lift_eq; unfold_Q; nlift; unfold_N; repeat f_equal; apply functional_extensionality; intros; apply propositional_extensionality; intuition. all: exfalso; eauto.
  - ndestruct (bvs0 k); ndestruct (fvs0 0); apply Q_lift_eq; unfold_Q; nlift; unfold_N; repeat f_equal; apply functional_extensionality; intros; apply propositional_extensionality; intuition. all: exfalso; eauto.
Qed.

Fixpoint open_subst1_ty_comm {T : ty} :
  forall {k g df ff lf}, closed_qual 0 ff lf df ->
    [[k ~> just_fv g ]]ᵀ ({0 |-> df }ᵀ T) = {0 |-> df }ᵀ ([[ k ~> just_fv (S g) ]]ᵀ  T).
    destruct T; intros; simpl; intuition;
      try solve [repeat erewrite open_subst1_ty_comm; eauto].
    erewrite open_subst1_qual_comm; eauto.
    erewrite open_subst1_qual_comm; eauto.
    erewrite open_subst1_ty_comm; eauto.
    erewrite open_subst1_ty_comm; eauto.
Qed.

Lemma closed_Qual_subst1 : forall {q b f l},
    closed_Qual b (S f) l (Q_lift q) ->
    forall {d1 l1}, closed_Qual 0 0 l1 (Q_lift d1) ->
    forall{l2},
      l <= l2 -> l1 <= l2 ->
      closed_Qual b f l2 (Q_lift ({0 |-> d1}ᵈ q)).
  intros. rewrite Q_lift_subst_qual. unfold_Q. unfold_N. intuition; nlem; intuition;
  try solve [ exfalso; eauto ];
  try solve [ eauto using lt_S_n,Nat.lt_le_trans ].
Qed.

Lemma closed_ty_subst1 : forall {T b f l},
    closed_ty b (S f) l T ->
    forall {d1 l1}, closed_Qual 0 0 l1 (Q_lift d1) ->
    forall{l2},
      l <= l2 -> l1 <= l2 ->
      closed_ty b f l2 ({0 |-> d1}ᵀ T).
  intros T b f l Hc. remember (S f) as f'. generalize dependent f. generalize dependent b.
  induction T; intros; subst; simpl in *; intuition.
  1,2: eapply closed_Qual_subst1; eauto.
  eapply IHT1; eauto.
  eapply IHT2; eauto; lia.
  erewrite subst1_ty_id; eauto.
Qed.

Lemma closed_tm_subst1 : forall {t b f l},
    closed_tm b (S f) l t ->
    forall {t1 l1}, closed_tm 0 0 l1 t1 ->
    forall{l2},
      l <= l2 -> l1 <= l2 ->
      closed_tm b f l2 ({0 |-> t1}ᵗ t).
  intros t b f l Hc. remember (S f) as f'.
  generalize dependent f.
  generalize dependent b.
  induction t; intros; subst; simpl in *; intuition; try constructor;
    try solve [eapply IHt; eauto; lia ];
    try solve [eapply IHt1; eauto];
    try solve [eapply IHt2; eauto].
  destruct v; auto. bdestruct (i =? 0).
  eapply closed_tm_monotone; eauto; lia. simpl; lia.
Qed.

Lemma subst1_qor_dist : forall {q1 q2 df},
    ({ 0 |-> df }ᵈ (q1 ⊔ q2)) = (({ 0 |-> df }ᵈ q1) ⊔ ({ 0 |-> df }ᵈ q2)).
intros. qual_destruct q1. qual_destruct q2. unfold subst_qual. unfold_q.
ndestruct (n_or fvs fvs0 0); ndestruct (fvs 0); ndestruct (fvs0 0); apply Q_lift_eq;
unfold_Q; nlift; unfold_N; repeat f_equal; apply functional_extensionality; intros; apply propositional_extensionality; intuition.
Qed.

Lemma subst1_qual_plus_dist : forall {x d df},
    1 <= x -> ({ 0 |-> df }ᵈ (d ⊕ x)) = (({ 0 |-> df }ᵈ d) ⊕ (pred x)).
Proof.
  intros. qual_destruct d; qual_destruct df. simpl. apply Q_lift_eq. repeat rewrite Q_lift_or,Q_lift_subst_qual. unfold_Q. nlift. unfold_N. repeat f_equal; apply functional_extensionality; intros; apply propositional_extensionality; intuition.
  ndestruct (fvs 0); intuition.
Qed.

Lemma indexr_subst1 : forall {x Γ T U d dx},
    x >= 1 ->
    indexr x (Γ ++ [U]) = Some (T, d) ->
    indexr (pred x) ({ 0 |-> dx }ᴳ Γ) = Some ({ 0 |-> dx }ᵀ T, { 0 |-> dx }ᵈ d).
  intros. destruct x; try lia.
  rewrite <- indexr_insert_ge in H0; simpl; try lia.
  rewrite app_nil_r in H0. induction Γ; intros; simpl in *. discriminate.
  rewrite subst1_tenv_length. (bdestruct (x =? length Γ)); auto.
  inversion H0. auto.
Qed.

Lemma closed_qual_subst1' : forall {Γ0 X l df φ b},
    closed_Qual 0 0 l (Q_lift df) ->
    closed_Qual b (length (Γ0 ++ [X])) l (Q_lift φ) ->
    closed_Qual b (length ({0 |-> df }ᴳ Γ0)) l (Q_lift ({0 |-> df }ᵈ φ)).
  intros. eapply closed_Qual_subst1; eauto. rewrite subst1_tenv_length.
  rewrite app_length in *. simpl in *. replace (length Γ0 + 1) with (S (length Γ0)) in H0 by lia. auto.
Qed.

Lemma closed_tm_subst1' : forall {Γ0 X l df tx t b},
    closed_tm 0 0 l tx ->
    closed_tm b (length (Γ0 ++ [X])) l t ->
    closed_tm b (length ({0 |-> df }ᴳ Γ0)) l ({0 |-> tx }ᵗ t).
  intros. eapply closed_tm_subst1; eauto. rewrite subst1_tenv_length.
  rewrite app_length in *. simpl in *. replace (length Γ0 + 1) with (S (length Γ0)) in H0.
  auto. lia.
Qed.

Lemma closed_ty_subst1' : forall {Γ0 X l df T b},
    closed_qual 0 0 l df ->
    closed_ty b (length (Γ0 ++ [X])) l T ->
    closed_ty b (length ({0 |-> df }ᴳ Γ0)) l ({0 |-> df }ᵀ T).
  intros. repeat eapply closed_ty_subst1; eauto. rewrite subst1_tenv_length.
  rewrite app_length in *. simpl in *. replace (length Γ0 + 1) with (S (length Γ0)) in H0.
  auto. lia.
Qed.

Lemma subst_qstp :  forall {gl df' sl d1 d2},
    Qstp (S gl) sl (Q_lift d1) (Q_lift d2) ->
    closed_Qual 0 0 sl (Q_lift df') ->
    (* Substq df df' -> *)
    Qstp gl sl (Q_lift ({0 |-> df' }ᵈ d1)) (Q_lift ({0 |-> df' }ᵈ d2)).
  intros. qual_destruct d1. qual_destruct d2. qual_destruct df'. repeat rewrite Q_lift_subst_qual. unfold_Q. unfold_N. intuition.
  all: nlem; intuition; eauto using lt_S_n. exfalso. eauto.
Qed.

Lemma subst_stp : forall{T1 T2},
    forall {Γ Tf df df' Σ d1 d2},
      stp (Γ ++ [(Tf,df)]) Σ T1 d1 T2 d2 ->
      closed_qual 0 0 (length Σ) df' ->
      (* Substq' (Q_lift df') (Q_lift df) -> *)
      stp ({ 0 |-> df' }ᴳ Γ) Σ
          ({ 0 |-> df' }ᵀ T1) ({ 0 |-> df' }ᵈ d1)
          ({ 0 |-> df' }ᵀ T2) ({ 0 |-> df' }ᵈ d2).
  intros T1 T2 Γ Tf df df' Σ d1 d2 HS.
  remember (Γ ++ [(Tf, df)]) as Γ'.
  generalize dependent Γ. generalize dependent df.  generalize dependent Tf. induction HS; intros; subst.
- simpl. constructor. rewrite app_length in H. simpl in H. rewrite Nat.add_1_r in H. rewrite subst1_tenv_length. eapply subst_qstp; simpl in *; eauto.
- specialize (stp_closed HS1). specialize (stp_closed HS2). intuition. simpl. constructor. rewrite app_length in H. simpl in H. rewrite Nat.add_1_r in H. rewrite subst1_tenv_length. eapply subst_qstp; simpl in *; eauto. all : repeat erewrite subst1_ty_id; eauto.
- intuition. rewrite app_length in *. simpl in *. rewrite Nat.add_1_r in *. constructor; simpl; intuition; try rewrite subst1_tenv_length;
  try solve [eapply closed_Qual_subst1; eauto];
  try solve [eapply closed_ty_subst1; eauto].
  eapply subst_qstp; eauto. eapply IHHS1; eauto.
  unfold open_ty' in *. unfold open_ty in *.
  unfold openq' in *. unfold openq in *.
  rewrite app_length in *. rewrite subst1_tenv_length. simpl in *.
  replace (length Γ0 + 1) with (S (length Γ0)) in *; try lia.
  specialize (IHHS2 Tf df ((T3, d3) :: Γ0)). simpl in IHHS2. intuition. rename H10 into IHHS2.
  erewrite <- open_subst1_ty_comm in IHHS2; eauto. erewrite <- open_subst1_ty_comm in IHHS2; eauto.
  erewrite <- open_subst1_qual_comm in IHHS2; eauto. erewrite <- open_subst1_qual_comm in IHHS2; eauto.
  -  econstructor; eauto.
Qed.

Lemma substitution_stp : forall{T1 T2},
    forall {Tf df dx Σ d1 d2},
      stp ([(Tf,df ⊓ dx)]) Σ T1 d1 T2 d2 -> closed_qual 0 0 (length Σ) dx ->
      stp [] Σ ({ 0 |-> dx }ᵀ T1) ({ 0 |-> dx }ᵈ d1) ({ 0 |-> dx }ᵀ T2) ({ 0 |-> dx }ᵈ d2).
  intros. replace [(Tf, df ⊓ dx)] with ([] ++ [(Tf, df ⊓ dx)]) in H; auto.
  replace [] with ({0 |-> dx }ᴳ []); auto.
  eapply subst_stp; eauto.
Qed.

Lemma subst1_just_fv0 : forall {q}, {0 |-> q }ᵈ (just_fv 0) = q.
  intros. apply Q_lift_eq. unfold_Q. nlift. unfold_N. repeat f_equal; apply functional_extensionality; intros; apply propositional_extensionality; intuition.
Qed.

Lemma subst1_preserves_separation : forall {df d1 Tx dx dx' Γ Σ φ},
    dx' ⊓ φ = dx ->
    closed_Qual 0 0 (length Σ) (Q_lift dx') ->
    df ⊑↑ φ -> d1 ⊑↑ φ ->
    saturated (Γ ++ [(Tx, dx)]) Σ d1 ->
    saturated (Γ ++ [(Tx, dx)]) Σ df ->
    {0 |-> dx' }ᵈ df ⊓ {0 |-> dx' }ᵈ d1 = {0 |-> dx' }ᵈ (df ⊓ d1).
  intros. qual_destruct df. qual_destruct d1. unfold_q.
  unfold saturated,saturated_var,qmem in *.
ndestruct (fvs 0); ndestruct (fvs0 0); ndestruct (n_and fvs fvs0 0); apply Q_lift_eq; unfold_Q; nlift; unfold_N; unfold N_lift in H; repeat f_equal; apply functional_extensionality; intros; apply propositional_extensionality; intuition.
  - exfalso; eauto.
  - specialize (H4 0). intuition. destruct H15 as [U' [q' H15]]. intuition. assert (Hl0: 0 = (length ([]: tenv))). auto. rewrite Hl0 in H4. rewrite indexr_insert in H4. inversion H4. subst. simpl in *. nlift. unfold_N. intuition.
  - exfalso; eauto.
  - specialize (H3 0). intuition. destruct H16 as [U' [q' H16]]. intuition. assert (Hl0: 0 = (length ([]: tenv))). auto. rewrite Hl0 in H3. rewrite indexr_insert in H3. inversion H3. subst. simpl in *. nlift. unfold_N. intuition.
Qed.

Lemma subst1_mem : forall {x dx df l}, closed_Qual 0 0 l (Q_lift dx) -> $ (x) ∈ᵥ {0 |-> dx }ᵈ df -> $ (S x) ∈ᵥ df.
intros. qual_destruct dx. qual_destruct df. simpl in *. unfold_Q. unfold_q.
ndestruct (fvs0 0); simpl in *; nlift; unfold_N; intuition. exfalso; eauto.
Qed.

Lemma subst1_saturated : forall {Γ Σ Tx dx df dx'},
    saturated (Γ ++ [(Tx, dx)]) Σ df ->
    closed_Qual 0 0 (length Σ) (Q_lift dx') ->
    saturated ({0 |-> dx' }ᴳ Γ) Σ ({0 |-> dx' }ᵈ df).
intros. unfold saturated in *. intros.
eapply subst1_mem in H1; eauto. apply H in H1. clear H.
unfold subst_qual,saturated_var in *. qual_destruct df. unfold_q. unfold_Q. destruct H1 as [U [q' H1]]. exists ({0 |-> dx' }ᵀ U),({0 |-> dx' }ᵈ q').
ndestruct (fvs 0); intuition.
1,8: eapply @indexr_subst1 with (x:=(S x)); eauto; lia.
all: qual_destruct q'; qual_destruct dx'; unfold_q; ndestruct (fvs0 0); simpl; nlift; unfold_N; intuition.
  all: try solve [eauto using lt_S_n]; try solve [exfalso; eauto].
Qed.

Lemma vtp_closed:
  forall {Σ t T d}, vtp Σ t T d ->
    closed_tm 0 0 (length Σ) t /\
    closed_ty 0 0 (length Σ) T /\
    closed_Qual 0 0 (length Σ) (Q_lift d).
Proof.
  intros. induction H; simpl in *; intuition.
  - apply indexr_var_some' in H1; intuition.
  - apply stp_closed in H2. intuition.
Qed.

Lemma vtp_widening: forall {Σ T1 d1 T2 d2 t},
  vtp Σ t T1 d1 -> stp ([]: tenv) Σ T1 d1 T2 d2 -> vtp Σ t T2 d2.
Proof.
  intros. remember t as tt. remember [] as Γ.  induction H0; subst.
  - (* vtp_base *)
    inversion H. subst. econstructor; eauto. apply qstp_closed in H0; intuition.
  - (* vtp_ref *) inversion H. subst. econstructor; eauto; intuition.
    + apply qstp_closed in H0; intuition.
    + eapply s_trans; eauto.
    + eapply s_trans; eauto.
    + eapply qstp_trans; eauto.
  - (* vtp_abs *) inversion H. subst. econstructor; eauto.
    + apply qstp_closed in H2; intuition.
    + eapply s_trans; eauto.
    + eapply qstp_trans; eauto.
    + assert (stp [] Σ (TFun d1 d2 T1 T2) d5 (TFun d3 d4 T3 T4) d6).
      { apply s_fun; intuition.  }
      assert (stp [] Σ (TFun d0 d7 T0 T5) df1 (TFun d1 d2 T1 T2) d5).
      { apply s_fun; intuition.  }
      assert (stp [] Σ (TFun d0 d7 T0 T5) df1 (TFun d3 d4 T3 T4) d6).
      { eapply s_trans; eauto. }
      assert (stp [] Σ T3 d3 T1 d1). { eauto. }
      specialize (@narrowing_stp_gen [] T1 d1 [] Σ
                                     (open_ty' ([]: tenv) T5)(openq' ([]:tenv) d7) (open_ty' ([]:tenv) T2) (openq' ([]: tenv) d2)) as narrow.
      replace ([] ++ [(T1, d1)]) with [(T1, d1)] in narrow; intuition.
      simpl in *. apply H11 in H6. clear H11.
      eapply s_trans; eauto.
  - intuition.
Qed.

Lemma has_type_vtp: forall {Σ φ t T d},
  value t ->
  has_type [] φ Σ t T d ->
  vtp Σ t T d.
Proof.
  intros. remember [] as Γ.  induction H0; eauto; try inversion H; subst.
  - (* tabs *) eapply vtp_abs; simpl in *; eauto; intuition.
    + apply @closed_Qual_sub with (d:=φ); auto.
    + eapply stp_refl; eauto. unfold_Q; unfold_N; intuition.
    + unfold_Q; unfold_N; intuition.
    + eapply stp_refl; eauto. eapply closed_ty_open'; simpl; eauto. unfold_Q; nlift; unfold_N; intuition. unfold openq',openq. constructor; auto. rewrite Q_lift_open_qual. eapply closed_qual_open'; eauto. unfold_Q; nlift; unfold_N; intuition.
  - (* tloc *) eapply vtp_loc; eauto; intuition.
    + eapply closed_Qual_sub; eauto.
    + eapply stp_refl; eauto. unfold_Q; unfold_N; intuition.
    + eapply stp_refl; eauto. unfold_Q; unfold_N; intuition.
    + apply Qstp_refl; auto. unfold_Q; unfold_N; intuition.
  - intuition. eapply vtp_widening; eauto.
  - intuition. eapply vtp_widening; eauto.
  - intuition. eapply vtp_widening; eauto.
Qed.

Lemma vtp_has_type: forall {Σ t T d}, vtp Σ t T d ->  has_type [] d Σ t T d.
Proof.
  intros. induction H.
  - econstructor; eauto. econstructor; eauto. constructor. unfold_Q; unfold_N; intuition. eapply closed_Qual_sub; eauto.
  - assert (has_type [] (just_loc l) Σ (tloc l) (TRef T) (just_loc l)). { econstructor; eauto. unfold_Q; unfold_N; intuition. }
    eapply weaken_flt with (φ' := d) in H5; intuition. eapply t_sub; eauto.
    constructor; intuition. unfold_Q; unfold_N; intuition.
  - specialize (qstp_closed H5) as Hcl. intuition.
    assert (has_type [] df1 Σ (tabs t) (TFun d1 d2 T1 T2) df1). {
    constructor; eauto. apply saturated_empty_tenv. unfold_Q; unfold_N; intuition. }
    eapply weaken_flt with (φ' := df2) in H9; eauto.
    eapply t_sub; eauto. constructor; intuition. unfold_Q; unfold_N; intuition.
Qed.

Lemma narrow_saturated : forall {Γ0 df df' Σ Tx d},
  df ⊑↑ df' ->
  saturated (Γ0 ++ [(Tx, df')]) Σ d ->
  saturated (Γ0 ++ [(Tx, df)]) Σ d.
intros. unfold saturated,saturated_var in *. intros. specialize (H0 x H1). destruct x; destruct H0 as [U [q' H0]]; intuition.
  - replace 0 with (length ([] : tenv)) in * by auto. rewrite indexr_insert in H2. inversion H2. clear H2. subst. exists U,df. intuition. rewrite indexr_insert. auto. all: Qcrush.
  - exists U,q'. intuition. rewrite <- indexr_insert_ge in H2. rewrite <- indexr_insert_ge. auto. all: simpl; lia.
Qed.

Lemma stp_scale_qor_l : forall {Γ Σ T d1 d2},
  closed_ty 0 (length Γ) (length Σ) T ->
  closed_Qual 0 (length Γ) (length Σ) (Q_lift d1) ->
  closed_Qual 0 (length Γ) (length Σ) (Q_lift d2) ->
  stp Γ Σ T d2 T (d1 ⊔ d2).
intros. induction T; constructor; auto.
1,2: Qcrush. simpl in H. intuition. eapply stp_refl; eauto. Qcrush. unfold open_ty',openq',open_ty,openq. eapply stp_refl; eauto. simpl in H. eapply closed_ty_open'; eauto. intuition. simpl. eapply closed_ty_monotone; eauto. Qcrush. simpl in H. intuition. apply Qstp_refl. simpl. rewrite Q_lift_open_qual. eapply closed_qual_open'; eauto. Qcrush. Qcrush. 1,2: eapply stp_refl; eauto; apply Qstp_refl; Qcrush.
Qed.

Lemma subst1_Qual_plus' : forall {du du' l},
    closed_Qual 0 0 l (Q_lift du') -> subst_Qual (Q_lift (du' ⊕ 0)) 0 (Q_lift du) = Qor (Q_lift du') (Q_lift du).
Proof.
  intros. qual_destruct du'. qual_destruct du. Qcrush. exfalso. eauto.
Qed.

Lemma subst1_qual_plus' : forall {du du' l},
    closed_Qual 0 0 l (Q_lift du') -> subst_qual (du' ⊕ 0) 0 du = (du' ⊔ du).
Proof.
  intros. apply Q_lift_eq. apply Q_lift_closed' in H. repeat rewrite Q_lift_subst_qual. erewrite subst1_Qual_plus'. rewrite Q_lift_or. auto. eauto.
Qed.

Lemma substitution_gen :
  forall {t Γ φ' Tx dx dx' Σ T d}, dx' ⊓ φ' ⊑↑ dx ->
    forall {φ}, φ ⊑↑ φ' ->
      has_type (Γ ++ [(Tx,dx)]) φ Σ t T d -> wf_tenv (Γ ++ [(Tx,dx)]) Σ ->
        forall {tx}, vtp Σ tx Tx dx' ->
                        has_type ({ 0 |-> dx' }ᴳ Γ) ({ 0 |-> dx' }ᵈ φ) Σ
                                 ({ 0 |-> tx  }ᵗ t)
                                 ({ 0 |-> dx' }ᵀ T)
                                 ({ 0 |-> dx' }ᵈ d).
  intros t Γ φ' Tx dx dx' Σ T d Hsep φ Hphi HT HwfG tx HTx. specialize (vtp_closed HTx) as Hclx.
  simpl in Hclx. intuition. remember (Γ ++ [(Tx, dx)]) as Γ'.
  generalize dependent Γ. generalize dependent φ'.
  induction HT; intros; subst; pose (φs := {0 |-> dx' }ᵈ φ); replace ({0 |-> dx' }ᵈ φ) with φs in *; auto.
  - simpl. replace ({0 |-> dx' }ᵈ ∅) with (∅) by auto.
    apply t_base; auto. eapply closed_qual_subst1'; eauto.
  - simpl. bdestruct (x =? 0).
    + (*x is 0 *) rewrite indexr_skips in H0; simpl; auto; try lia. simpl in H0. subst. simpl in H0.
      inversion H0. subst. erewrite subst1_ty_id; eauto.
      apply vtp_has_type in HTx. erewrite subst1_qual_plus'; eauto.
      apply t_sub with (T1:=T) (d1:=dx').
      eapply @weaken_flt with (φ:=dx'); eauto.
      eapply weaken; eauto.
      subst φs. qual_destruct φ. assert (N_lift fvs 0). { Qcrush. }
      unfold subst_qual. unfold_q. destruct (fvs 0) eqn:Eq. Qcrush. unfold N_lift in H7. rewrite H7 in Eq. discriminate.
      subst φs. rewrite subst1_tenv_length. rewrite app_length in H4. simpl in H4. rewrite <- plus_n_Sm in H4. rewrite Nat.add_0_r in H4. eapply closed_Qual_subst1; eauto.
      apply stp_scale_qor_l; eauto. eapply closed_ty_monotone; eauto; lia. 1,2: eapply closed_Qual_monotone; eauto; lia.
      subst φs. apply @subst1_Qual_subq with (du':=dx') in H3. eapply @Subq_trans with (d2:={0 |-> dx' }ᵈ (d ⊕ 0)); eauto. erewrite subst1_qual_plus'; eauto.
      apply saturated_qor; eapply saturated_closed_Qual; eauto.
    + (* x is in Γ0 *) assert (Hx: 1 <= x); try lia. destruct x; try lia.
      rewrite subst1_qual_plus_dist; auto. apply t_var; auto.
      eapply indexr_subst1; eauto. rewrite <- subst1_qual_plus_dist; auto.
      repeat apply subst_qual_subqual_monotone. auto.
      eapply closed_qual_subst1'; eauto. simpl. eapply closed_ty_subst1; eauto.
      simpl. eapply closed_Qual_subst1; eauto.
  - simpl.
    (* assert (HwfG' : wf_tenv ((T1, d1) :: Γ0 ++ [(Tx, dx)]) Σ). apply wf_tenv_cons; auto. *)
    assert (HwfG' : wf_tenv ((T1, d1) :: Γ0 ++ [(Tx, dx)]) Σ). apply wf_tenv_cons; auto.
    intuition. rename H8 into IHHT.
    apply t_abs; auto. eapply closed_tm_subst1'; eauto.
    inversion H3. subst. constructor; intuition; try eapply closed_ty_subst1'; eauto; eapply closed_qual_subst1'; eauto.
    eapply closed_qual_subst1'; eauto. apply subst_qual_subqual_monotone. auto.
    1,2 : eapply subst1_saturated; eauto.
    (* 1. instantiate the IH *)
    replace (length (Γ0 ++ [(Tx, dx)])) with (S (length Γ0)) in IHHT.
    rewrite subst1_tenv_length. rewrite app_comm_cons in IHHT. (*  rewrite app_comm_cons in IHHT. *)
    remember (df ⊔ just_fv (S (length Γ0))) as DF.
    replace ({0 |-> dx' }ᵈ df ⊔ just_fv (length Γ0)) with ({0 |-> dx' }ᵈ DF).
    specialize IHHT with (φ' := φ' ⊔ just_fv (S (length Γ0))) (Γ := (((T1, d1) :: Γ0))).
    (* 2. reason about opening and subst, apply IH *)
    unfold open_tm' in *. unfold open_ty' in *. unfold open_ty in *.
    unfold openq' in *. unfold openq in *.
    rewrite app_length in IHHT. rewrite subst1_tenv_length.
simpl in *.
    replace (length Γ0 + 1) with (S (length Γ0)) in IHHT; try lia.
    erewrite <- open_subst1_tm_comm in IHHT; eauto.
    erewrite <- open_subst1_ty_comm in IHHT; eauto.
    erewrite <- open_subst1_qual_comm in IHHT; eauto.
rewrite qand_qor_dist_l in IHHT. replace (dx' ⊓ $$ (S (length Γ0))) with (∅) in IHHT.
rewrite qor_empty_right in IHHT. subst.
assert (df ⊔ $$ (S (length Γ0)) ⊑↑ φ' ⊔ $$ (S (length Γ0))). Qcrush.
    apply IHHT; auto.
    (* done, prove some leftovers *)
apply Q_lift_eq. Qcrush. eauto.
    subst. apply Q_lift_eq. rewrite subst1_qor_dist. Qcrush.
    rewrite app_length. simpl. lia.
  - intuition. rename H7 into IHHT2. rename H5 into IHHT1. simpl.
    replace ({ 0 |-> dx' }ᵈ (openq d1 d2)) with (openq ({ 0 |-> dx' }ᵈ d1) ({ 0 |-> dx' }ᵈ d2)).
    (* separation/overap is preserved after substitution *)
    assert (Hoverlap: {0 |-> dx' }ᵈ (df ⊓ d1) = {0 |-> dx' }ᵈ df ⊓ {0 |-> dx' }ᵈ d1). {
      specialize (has_type_filter HT1). specialize (has_type_filter HT2).
      specialize (has_type_saturated HwfG HT1). specialize (has_type_saturated HwfG HT2). intros.
      symmetry. eapply @subst1_preserves_separation with (φ:=φ'); eauto.
      all: eapply @narrow_saturated with (df:=(dx' ⊓ φ')); eauto.
    }
    apply t_app with (T1:= { 0 |-> dx' }ᵀ T1) (df:=({0 |-> dx' }ᵈ df)).
    replace (TFun ({0 |-> dx' }ᵈ df ⊓ {0 |-> dx' }ᵈ d1) ({0 |-> dx' }ᵈ d2) ({0 |-> dx' }ᵀ T1) ({0 |-> dx' }ᵀ T2))
            with ({ 0 |-> dx' }ᵀ (TFun (df ⊓ d1) d2 T1 T2)).
    eapply IHHT1; eauto. simpl. f_equal. apply Hoverlap.
    eapply IHHT2; eauto.
    2,3 : unfold openq; rewrite <- @subst1_qual_empty with (dx:=dx'); erewrite <- subst1_open_qual_comm; eauto.
    + eapply closed_ty_subst1'; eauto.
    + apply subst_qual_subqual_monotone. unfold openq in H4. auto.
    + eapply subst1_saturated; eauto.
    + unfold openq. repeat erewrite <- subst1_open_qual_comm; eauto.
  - erewrite @subst1_qual_id with (q:=(just_loc l)); eauto. simpl. erewrite subst1_ty_id; eauto.
    apply t_loc; auto. eapply closed_qual_subst1'; eauto.
    subst φs. qual_destruct φ. qual_destruct dx'. unfold_q.
    ndestruct (fvs 0); simpl in *; unfold_Q; nlift; unfold_N; intuition.
    unfold_Q; nlift; unfold_N; intuition.
  - replace ({0 |-> dx' }ᵈ ∅) with (∅) in * by auto.
    replace ({0 |-> dx' }ᵀ (TRef TUnit)) with (TRef TUnit) in * by auto.
    replace ({0 |-> dx' }ᵀ (TUnit)) with (TUnit) in * by auto.
    eapply t_ref. fold subst_tm. eapply IHHT; eauto.
  - simpl. rewrite subst1_qual_empty.
    apply t_deref with (d := { 0 |-> dx' }ᵈ d). eapply IHHT; eauto.
  - replace ({0 |-> dx' }ᵈ ∅) with (∅) in * by auto.
    replace ({0 |-> dx' }ᵀ (TRef TUnit)) with (TRef TUnit) in * by auto.
    replace ({0 |-> dx' }ᵀ (TUnit)) with (TUnit) in * by auto.
    eapply t_assign; eauto.
  - apply t_sub with (T1:={ 0 |-> dx' }ᵀ T1) (d1:={ 0 |-> dx' }ᵈ d1).
    eapply IHHT; eauto. eapply subst_stp; eauto. apply subst_qual_subqual_monotone; auto.
    eapply subst1_saturated; eauto.
    Unshelve. all : auto.
Qed.

Lemma open_Qual_mono : forall {d1 d1' d2 k}, d1 ⊑↑ d1' -> ([[ k ~> d1 ]]ᵈ d2) ⊑↑ ([[ k ~> d1' ]]ᵈ d2).
  intros. repeat rewrite Q_lift_open_qual. Qcrush.
Qed.

Lemma open_qual_mono : forall {d1 d1' d2 k}, d1 ⊑ d1' -> ([[ k ~> d1 ]]ᵈ d2) ⊑ ([[ k ~> d1' ]]ᵈ d2).
  intros. apply Q_lift_subq. apply Q_lift_subq' in H. apply open_Qual_mono. auto.
Qed.

Lemma open_Qual_mono2 : forall {d1 d2 d2' k}, d2 ⊑↑ d2' -> ([[ k ~> d1 ]]ᵈ d2) ⊑↑ ([[ k ~> d1 ]]ᵈ d2').
  intros. repeat rewrite Q_lift_open_qual. Qcrush. all: nlem; intuition eauto 3.
Qed.

Lemma open_qual_mono2 : forall {d1 d2 d2' k}, d2 ⊑ d2' -> ([[ k ~> d1 ]]ᵈ d2) ⊑ ([[ k ~> d1 ]]ᵈ d2').
  intros. apply Q_lift_subq. apply Q_lift_subq' in H. apply open_Qual_mono2. auto.
Qed.

Lemma openq_mono : forall {d1 d1' d2 d2' f l},
  closed_qual 0 f l d1' -> d1 ⊑ d1' -> d2 ⊑ d2' -> (openq d1 d2) ⊑ (openq d1' d2').
  intros. unfold openq.
  specialize (@open_qual_mono d1 d1' d2' 0 H0) as S1.
  specialize (@open_qual_mono2 d1 d2 d2' 0 H1) as S2.
  eapply subq_trans; eauto.
Qed.

Lemma stp_scale_qor : forall {Γ Σ T1 d1 T2 d2}, stp Γ Σ T1 d1 T2 d2 -> forall {d}, closed_Qual 0 (length Γ) (length Σ) (Q_lift d) -> stp Γ Σ T1 (d1 ⊔ d) T2 (d2 ⊔ d).
  intros Γ Σ T1 d1 T2 d2 HSTP. induction HSTP; intros.
  - inversion H. constructor. constructor.
    apply Subq_qor; auto. apply closed_qual_qor; auto.
  - inversion H. constructor; auto. constructor.
    apply Subq_qor; auto. apply closed_qual_qor; auto.
  - inversion H1. constructor; auto. constructor. apply Subq_qor; auto. apply closed_qual_qor; auto.
  - econstructor; auto.
Qed.

Lemma open_qual_qor_dist : forall {k d1 d2 d3}, ([[ k ~> d1  ]]ᵈ (d2 ⊔ d3)) = (([[ k ~> d1  ]]ᵈ d2) ⊔ ([[ k ~> d1  ]]ᵈ d3)).
  intros. apply Q_lift_eq. qual_destruct d2. qual_destruct d3. qual_destruct d1. rewrite Q_lift_or,Q_lift_open_qual. unfold_q.
ndestruct (bvs k); ndestruct (bvs0 k); Qcrush.
all: intuition eauto.
Qed.

Lemma openq_u_distribute: forall {d1 d2 d3 : qual}, openq d1 (d2 ⊔ d3) = (openq d1 d2 ⊔ openq d1 d3).
  intros. unfold openq. repeat rewrite open_qual_qor_dist. auto.
Qed.

Lemma openq_u_distribute1 : forall {d1 d2 l},
    openq d1 (d2 ⊔ (just_loc l)) = ((openq d1 d2) ⊔ (just_loc l)).
  intros. unfold openq. rewrite open_qual_qor_dist. auto.
Qed.

Lemma openq_duplicate_eq : forall {d1 d2 l},
    (((openq (d1 ⊔ (just_loc l)) d2) ⊔ (just_loc l)) = ((openq d1 d2) ⊔ (just_loc l))).
intros. unfold openq. qual_destruct d2. qual_destruct d1. apply Q_lift_eq. unfold_q.
ndestruct (bvs 0); unfold_Q; nlift; unfold_N; repeat f_equal; apply functional_extensionality; intros; apply propositional_extensionality; intuition.
Qed.

Lemma freshness : forall {Σ Σ' l b f d1}, disjointq Σ Σ' (just_loc l) -> closed_Qual b f (length Σ) (Q_lift d1) -> just_loc l ⊓ d1 = ∅.
  intros. inversion H; subst. unfold_q. unfold just_loc in H1.
  inversion H1. apply N_lift_eq' with (x:=l) in H3. Qcrush.
  inversion H3. apply N_lift_eq' with (x:=l) in H5. apply Q_lift_eq. rewrite Q_lift_and. Qcrush. subst. eauto.
Qed.

Lemma just_loc_ldom : forall {l} {Σ : senv}, l < length Σ -> just_loc l ⊑↑ qdom Σ.
  intros. unfold qdom. unfold_Q. nlift. unfold_N. intuition.
Qed.

Lemma vtp_canonical_form_loc : forall {Σ t T d},
   vtp Σ t (TRef T) d -> value t -> exists (l : loc), t = tloc l.
Proof.
  intros. remember (TRef T) as R. remember t as tt. generalize dependent T.
  induction H; intuition; try discriminate; inversion H0; subst. exists l. intuition.
Qed.

Lemma vtp_canonical_form_lam : forall {Σ t T1 T2 d1 d2 df},
    vtp Σ t (TFun d1 d2 T1 T2) df -> value t -> exists (t' : tm), t = tabs t'.
Proof.
  intros Σ t T1 T2 d1 d2 df H. remember (TFun d1 d2 T1 T2) as T.
  generalize dependent d1. generalize dependent d2. generalize dependent T1. generalize dependent T2.
  induction H; intuition; try discriminate; inversion H0; subst. exists t. intuition.
Qed.

Lemma substitution : forall {t df Tx dx dx' Σ T d},
    has_type [(Tx,dx')] (df ⊔ (just_fv 0)) Σ t T d ->
    wf_tenv [(Tx,dx')] Σ ->
    df ⊓ dx ⊑↑ dx' ->
    closed_Qual 0 0 (length Σ) (Q_lift df) ->
            forall {vx}, vtp Σ vx Tx dx ->
                    has_type [] (df ⊔ dx) Σ
                             ({ 0 |-> vx }ᵗ t)
                             ({ 0 |-> dx }ᵀ T)
                             ({ 0 |-> dx }ᵈ d).
  intros t df Tx dx dx' Σ T d H Hwf Hsub Hcl vx Hvtp. intros. specialize (vtp_closed Hvtp) as Hclx. specialize (has_type_closed H) as Hclt.
  intuition. replace ([(Tx, dx')]) with ([] ++ [(Tx, dx')]) in H; auto.
  remember (df ⊔ (just_fv 0)) as DF.
  assert (Hsepf : dx ⊓ (df ⊔ just_fv 0) ⊑ dx'). {
    rewrite qand_qor_dist_l. replace (dx ⊓ $$ 0) with (∅). rewrite qor_empty_right. rewrite qand_commute. auto. apply Q_lift_eq. Qcrush. eauto.
  }
  assert (Hrefl : DF ⊑↑ DF). unfold_Q; unfold_N; intuition. subst DF.
replace ([(Tx, dx')]) with ([] ++ [(Tx, dx')]) in H by auto.
  eapply (substitution_gen Hsepf Hrefl) in H; eauto.
  replace ({0 |-> dx }ᵈ (df ⊔ just_fv 0)) with (df ⊔ dx) in H. apply H.
  (* done, prove earlier replacements *)
  rewrite subst1_qor_dist. rewrite subst1_just_fv0. erewrite subst1_qual_id; eauto.
Qed.

(* Main results: type soundness & preservation of separation *)

Theorem type_safety: forall {Σ t T d},
  has_type [] (qdom Σ) Σ t T d ->
    value t \/
    forall {σ} , CtxOK [] (qdom Σ) Σ σ ->
    exists t' σ', step t σ t' σ' /\ preserve [] Σ t' T d σ'.
Proof.
  intros Σ t T d H.
  specialize (has_type_closed H) as HX. remember [] as G. remember t as tt. remember T as TT. remember (qdom Σ) as φ.
  revert T t HeqTT Heqtt HeqG Heqφ.
  induction H; try (left; constructor); intros.
  - (* tvar *)  subst. inversion H.
  - (* tapp *) right. subst. intuition.
    apply has_type_closed in H as HH. intuition. apply has_type_closed in H0 as HH0. intuition.
    (* t1 *) specialize (H7 (TFun (df ⊓ d1) d2 T1 T) t1).  intuition.
    (* t2 *) specialize (H9 T1 t2). intuition.
    + (* beta *)
      (* turn has_type to vtp *)
      apply has_type_vtp in H as VH; intuition.
      pose (VHH := VH). inversion VH. subst.
      specialize (has_type_filter H0) as Hflt0.
      apply has_type_vtp in H0 as VH0; intuition.
      exists (open_tm  t2 t). exists σ. intuition.
      * constructor. intuition.
      * apply (Preserve Σ ∅); auto. rewrite qor_empty_right.
        apply qstp_closed in H32 as H32'; intuition.
        apply stp_qstp_inv in H31 as H31'. unfold Qstp in H31'. intuition.
        apply Q_lift_subq in H21.

        change (length []) with 0 in *. subst.
        assert (HT' : has_type [(T0, d0)] (df ⊔ just_fv 0) Σ (open_tm' ([]:tenv) t) (open_ty' ([]:tenv) T2) (openq' ([]:tenv) d3)). {
          eapply weaken_flt; eauto. unfold_Q; nlift; unfold_N; intuition.
        }
        eapply @substitution  with ( vx:= t2) (dx:=d1)  in HT' as HT''; eauto; intuition.
        unfold open_tm' in HT''. unfold open_ty' in HT''. unfold openq' in HT''. simpl in HT''. inversion H26; subst.
        unfold open_ty in HT''. unfold openq in HT''.
        erewrite <- open_subst1_tm in HT''; eauto. erewrite <- open_subst1_qual in HT''; eauto. erewrite <- open_subst1_ty in HT''; eauto.
        fold (open_tm t2 t) in HT''. fold (openq d1 d3) in HT''.
        apply @weaken_flt with (φ':= (qdom Σ)) in HT''; auto; intuition.
        eapply t_sub; eauto.
        simpl in *. rename H33 into Hsub.
        eapply @subst_stp with (Γ := [])(df' := d1) in Hsub; eauto.
        replace (open_ty' ([] : tenv) T) with T in *. (* because T is closed *)
        simpl in Hsub. unfold openq' in Hsub. unfold openq in Hsub. simpl in Hsub.
        erewrite @subst1_ty_id with (T := T) in Hsub; eauto.
        unfold open_ty' in Hsub. unfold open_ty in Hsub.
        erewrite <- open_subst1_ty in Hsub; eauto.
        erewrite <- open_subst1_qual in Hsub; eauto.
        erewrite <- open_subst1_qual in Hsub; eauto.
        Qcrush.
        unfold open_ty'. unfold open_ty. repeat erewrite closed_ty_open_id; eauto.
        unfold openq. intuition. eapply openq_subqual; auto.
        apply qor_bound; auto. apply has_type_filter in H. auto.
        intuition eauto.
        intuition eauto.
        apply wf_tenv_cons; auto.
        eapply vtp_widening; eauto.
        eapply stp_refl_qual; eauto.
    + (* (tabs t) t2 -> (tabs t) t2' *)
      apply has_type_vtp in H as VH; intuition.
      apply vtp_canonical_form_lam in VH as HH; intuition.
      pose (HH10 := H10).
      unfold CtxOK in HH10. specialize (H7 σ). intuition.
      destruct H21 as [t2' [σ' HH21]]. exists (tapp t1 t2'). exists σ'. intuition. constructor; intuition.
      destruct H21.  apply (Preserve Σ' d'); intuition.
      inversion H23; subst.
      * rewrite qor_empty_right. rewrite qor_empty_right in H24. eapply t_app with (df := df); eauto.
        eapply weaken_flt. eapply weaken_store; eauto; intuition. apply extends_ldom. auto.
        apply extends_length in H21. unfold_Q; erewrite N_lift_dom; unfold_N; intuition.
        eapply closed_ty_monotone; eauto. apply extends_length. intuition.
        Qcrush.
        apply extends_length in H21. unfold_N. eauto 4 using Nat.lt_le_trans.
        eapply weaken_store_saturated; eauto.
      * specialize (has_type_closed H). specialize (has_type_closed H24). intuition. simpl in H32. intuition. rewrite <- openq_duplicate_eq.
        apply t_sub with (T1 := T) (d1 := (openq (d1 ⊔ (just_loc l)) d2)).
        -- eapply t_app with (T1 := T1) (df:=df); eauto. erewrite <- qand_fresh_r; eauto. eapply weaken_flt. eapply weaken_store; eauto.
           apply extends_ldom. auto. simpl. auto.
           eapply Subq_trans; eauto. apply extends_ldom; auto.
           eapply weaken_store_saturated; eauto.
        -- eapply stp_refl; eauto. unfold openq. simpl. repeat rewrite Q_lift_or,Q_lift_open_qual,Q_lift_or. clear - H25 H26 H32 H33 H35 H34. Qcrush. nlem; intuition. nlem; intuition. eapply closed_Nats_tighten; eauto. nlem; intuition eauto 4 using Nat.le_lt_trans,Nat.lt_trans.
        -- apply has_type_filter in H0. apply qor_bound. apply openq_subqual. apply qor_bound.
           1, 3 : eapply Subq_trans; eauto; apply extends_ldom; auto. all : apply just_loc_ldom; auto.
        -- apply saturated_qor; auto. apply saturated_openq. apply saturated_qor; auto.
           apply saturated_empty_tenv. eapply closed_Qual_monotone; eauto. lia. eapply weaken_store_saturated; eauto.
    + (*  t t2 -> t' t2  *)
      apply has_type_closed in H0 as Hcl. intuition.
      specialize (H18 σ H10). destruct H18 as [t1' [σ' HH5]]. exists (tapp t1' t2). exists σ'. intuition. apply step_c_app_l. intuition.
      destruct H22. apply (Preserve Σ' d'); intuition. inversion H25; subst.
      * rewrite qor_empty_right. rewrite qor_empty_right in H26. eapply t_app; eauto.
        eapply weaken_flt. eapply weaken_store; eauto. apply extends_ldom. auto. Qcrush.
        eapply closed_ty_monotone; eauto. apply extends_length. auto.
        eapply Subq_trans; eauto; apply extends_ldom; auto.
        eapply weaken_store_saturated; eauto.
      * rewrite <- openq_u_distribute1. eapply t_sub with (T1 := T)(d1 := (openq d1 d2)).
        -- eapply t_app with (df:=(df ⊔ just_loc l)); eauto. erewrite <- qand_fresh_l; eauto.
           eapply weaken_flt. eapply weaken_store. eauto. auto. apply extends_ldom; auto. Qcrush.
           eapply Subq_trans; eauto. apply extends_ldom; auto. eapply weaken_store_saturated; eauto.
        -- eapply stp_refl; eauto. simpl.
           constructor. eapply openq_mono; eauto. apply subq_qor_gt.
           unfold openq. rewrite Q_lift_open_qual. eapply closed_qual_open'; eauto. simpl in H12. intuition. apply closed_Qual_qor; eauto. Qcrush.
        -- apply has_type_filter in H0. apply openq_subqual. eapply Subq_trans; eauto. apply extends_ldom. auto.
           rewrite openq_u_distribute1. apply qor_bound. eapply Subq_trans; eauto. apply extends_ldom. auto.
           apply just_loc_ldom. auto.
        -- rewrite openq_u_distribute1. apply saturated_qor; auto. apply saturated_openq. apply saturated_empty_tenv.
           eapply closed_Qual_monotone; eauto. lia. eapply weaken_store_saturated; eauto.
  - (* tref *) subst. intuition. specialize (has_type_closed H) as HH. intuition. specialize (H8 TUnit t). intuition.
    + (* contraction *) right. intros.
      exists (tloc (length (σ))). exists (t :: σ). intuition.
      econstructor; eauto. apply (Preserve (TUnit :: Σ) (just_loc (length σ))). apply extends_cons. eapply CtxOK_weaken_flt.
      apply CtxOK_ext; auto. apply H8.
      pose (HV := H). apply has_type_vtp in HV; intuition. inversion HV; subst. constructor. auto. Qcrush.
      Qcrush. simpl. lia. simpl.
      inversion H8. apply (disj_loc (length σ)); simpl; eauto; lia.
      replace (∅ ⊔ just_loc (length σ)) with (just_loc (length σ)).
      inversion H8. rewrite <- H10.
      eapply t_loc; eauto. Qcrush.
      apply indexr_head.
      Qcrush. simpl. lia. Qcrush.
    + (* congruence *) right. intros. specialize (H5 σ H8). destruct H5 as [t' [σ' HH8]]. exists (tref t'). exists σ'. intuition. econstructor; eauto.
      destruct H10. apply (Preserve Σ' ∅); intuition. rewrite qor_empty_right. eapply t_ref; eauto.
  - (* tderef *) subst. intuition. specialize (has_type_closed H) as HH. intuition. specialize (H3 (TRef T0) t). intuition.
    + (* contraction *) right. intros. pose (HV := H). apply has_type_vtp in HV; intuition.
      specialize (vtp_canonical_form_loc HV) as Hcan. intuition. destruct H10 as [l HH10]. subst.
      pose (HHV := HV). inversion HHV. subst.  pose (HH3 := H3). destruct HH3. subst.
      pose (HH14 := H14). apply indexr_var_some' in HH14. rewrite H10 in HH14. apply indexr_var_some in HH14.
      destruct HH14 as [v HHH14].  exists v. exists σ. intuition. apply step_deref; intuition.
      apply (Preserve Σ ∅); intuition.
      simpl. rewrite qor_empty_right.  apply t_sub with (T1 := T)(d1:= ∅); auto.
      specialize (H11 l v T). intuition.
      replace Σ with (Σ ++ []); intuition. eapply weaken_stp_store. auto.
    + (* congruence *) right. intros. specialize (H8 σ H3).
      destruct H8 as [t' [σ' HH8]]. exists (tderef t'). exists σ'. intuition. constructor; auto.
      destruct H10. apply (Preserve Σ' ∅); intuition. simpl. rewrite qor_empty_right. eapply t_deref; eauto.
  - (* tassign *) subst. intuition. rename H into Ht1. rename H0 into Ht2. intuition.
    apply has_type_closed in Ht1 as Ht1C. intuition.
    apply has_type_closed in Ht2 as Ht2C. intuition.
    specialize (H4 (TRef TUnit) t1). intuition.
    specialize (H6 TUnit t2). intuition.
    + (* contraction *)
      right. intros.
      pose (Ht1' := Ht1). eapply has_type_vtp in Ht1'; eauto.
      pose (Hloc := Ht1'). apply vtp_canonical_form_loc in Hloc; auto.
      inversion Ht1'. destruct Hloc. subst.
      pose (Ht2' := Ht2). apply has_type_vtp in Ht2'; auto.
      inversion Ht2'. subst.
      exists tunit. exists (update σ x tunit). inversion H21. subst.
      simpl in  H7. inversion H6. subst. intuition.
      econstructor; eauto. lia. apply (Preserve Σ ∅); auto.
      eapply CtxOK_update; eauto. lia. apply t_sub with (T1:=TUnit) (d1:=∅); auto.
      replace Σ with (Σ ++ []); intuition. eapply weaken_stp_store. auto.
    + (* right congruence *)
      right. intros. specialize (H4 σ H6). destruct H4 as [t' [σ' H4']].
      exists (tassign t1 t'). exists σ'. intuition. econstructor; eauto.
      pose (HV := Ht1). apply has_type_vtp in HV; intuition. inversion HV; subst.
      destruct H14. apply (Preserve Σ' ∅); eauto. simpl. rewrite qor_empty_right.
      eapply t_assign; eauto.
      assert (qdom Σ ⊑ qdom Σ'). apply extends_ldom. auto.
      eapply weaken_store in Ht1; eauto. eapply weaken_flt in Ht1; eauto. Qcrush.
    + (* left congruence *)
      right. intros. specialize (H12 σ H4). destruct H12 as [t' [σ' H12']].
      exists (tassign t' t2). exists σ'. intuition. econstructor; eauto.
      destruct H14. apply (Preserve Σ' ∅); eauto. simpl. rewrite qor_empty_right.
      eapply t_assign; eauto. eapply weaken_store in Ht2; eauto. eapply weaken_flt; eauto. apply extends_ldom; auto. Qcrush.
  - (* subsumption *) subst. intuition. specialize (stp_closed H0) as H00. intuition.
    specialize (H6 T1 t). intuition. right.
    intros. specialize (H11 σ H6). destruct H11 as [t' [σ' HH9]]. exists t'. exists σ'. intuition.
    destruct H13. apply (Preserve Σ' d'); intuition. eapply t_sub; eauto. apply stp_scale_qor.
    eapply weaken_stp_store_ext; eauto. apply extends_length in H13. inversion H15; subst; intuition. Qcrush.
    apply qor_bound. eapply Subq_trans; eauto. apply extends_ldom; auto. inversion H15; subst; auto.
    apply just_loc_ldom; auto. apply saturated_qor. eapply weaken_store_saturated; eauto.
    inversion H15; subst; auto.
Qed.

Lemma step_deterministic:  deterministic step.
  unfold deterministic. intros t t1 t2 σ σ1 σ2 Hstep1 Hstep2. generalize dependent σ2. generalize dependent t2.
  induction Hstep1; intros; inversion Hstep2; subst; auto; try solve [match goal with
  | [ H : step _ _ _ _  |- _ ] => eapply values_stuck in H; eauto; contradiction (* stuck cases, contradiction *)
  | [ H1 : step ?t ?s ?t' ?s', (* congruence cases, use IH *)
      IH : forall _ _, step ?t ?s _ _ -> _ |- _ = _ /\ _ = ?s' ] => specialize (IH t' s'); intuition; f_equal; auto
  end].
  rewrite H1 in H. inversion H. subst. intuition.
Qed.

Lemma progress : forall {Σ t T d},
    has_type [] (qdom Σ) Σ t T d ->
    value t \/ forall {σ}, CtxOK [] (qdom Σ) Σ σ -> exists t' σ', step t σ t' σ'.
Proof.
  intros Σ t T d HT.
  specialize (type_safety HT). intuition. right. intros σ HCtxOK.
  specialize (H0 σ HCtxOK). destruct H0 as [t' [σ' [Hstep  HPreserve]]].
  exists t'. exists σ'. intuition.
Qed.

Lemma preservation : forall {Σ t T d},
    has_type [] (qdom Σ) Σ t T d ->
    forall{σ}, CtxOK [] (qdom Σ) Σ σ ->
    forall {t' σ'}, step t σ t' σ' ->
    preserve [] Σ t' T d σ'.
Proof.
  intros Σ t T d HT σ  HCtxOK t' σ' HStep.  specialize (type_safety HT). intuition.
  - inversion HStep; subst; inversion H0.
  - specialize (H0 σ HCtxOK). destruct H0 as [t'' [σ'' [HStep2 HPreserve]]].
    assert (t'' = t' /\ σ' = σ''). { intuition. 1,2: eapply step_deterministic; eauto.  }
    intuition. subst. intuition.
Qed.

Corollary preservation_of_separation : forall {Σ t1 T1 q1 t2 T2 q2},
  has_type [] (qdom Σ) Σ t1 T1 q1 ->
  has_type [] (qdom Σ) Σ t2 T2 q2 -> q1 ⊓ q2 ⊑ ∅ ->
    forall{σ}, CtxOK [] (qdom Σ) Σ σ ->
      forall {t1' σ'}, step t1 σ t1' σ' ->
      forall {t2' σ''}, step t2 σ' t2' σ'' -> separate Σ t1' T1 t2' T2.
  intros Σ t1 T1 q1 t2 T2 q2 HT1 HT2 Hsep σ HOK t1' σ' Hstep1 t2' σ'' Hstep2.
  (* execute preservation in sequence *)
  specialize (preservation HT1 HOK Hstep1) as P1. destruct P1 as [Σ' d1 Hext1 HOK' Hdisj1 HT1'].
  assert (HT2': has_type [] (qdom Σ') Σ' t2 T2 q2). {
    eapply weaken_flt. eapply weaken_store. eauto. auto. apply extends_ldom; auto. Qcrush. }
  specialize (preservation HT2' HOK' Hstep2) as P2. destruct P2 as [Σ'' d2 Hext2 HOK'' Hdisj2 HT2''].
  apply (Separate Σ' Σ'' (q1 ⊔ d1) (q2 ⊔ d2) Hext1 Hext2 HT1' HT2'').
  (* now we just need to show that the disjointness is preserved. this is intuitively true from the disjointness
     of the heap effects d1 and d2. *)
  inversion Hdisj1; inversion Hdisj2; subst. 1-3 : repeat rewrite qor_empty_right; auto.
  - rewrite qand_qor_dist_l. rewrite (@qand_commute q1 (just_loc l)). erewrite freshness; eauto.
    rewrite qor_empty_right. auto. apply has_type_closed in HT1. intuition. eapply closed_Qual_monotone; eauto.
    apply extends_length. auto.
  - rewrite qand_qor_dist_r. erewrite freshness; eauto. rewrite qor_empty_right. auto.
    apply has_type_closed in HT2. intuition. eapply closed_Qual_monotone; eauto.
  - rewrite qand_qor_dist_l. rewrite qand_qor_dist_r. rewrite qand_qor_dist_r.
    erewrite freshness; eauto. rewrite (@qand_commute (just_loc l) (just_loc l0)).
    erewrite @freshness with (Σ := Σ'); eauto. repeat rewrite qor_empty_right.
    rewrite (@qand_commute q1 (just_loc l0)). erewrite freshness; eauto. rewrite qor_empty_right. auto.
    apply has_type_closed in HT1. 3 : apply has_type_closed in HT2. 1,3: intuition; eapply closed_Qual_monotone; eauto;
    apply extends_length; auto. Qcrush.
    Unshelve. all : auto.
Qed.
