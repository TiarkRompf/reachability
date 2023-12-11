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

Require Import vars.
Require Import env.
Require Import tactics.
Require Import NatSets.
Require Import setfacts.
Require Import qualifiers.

Import QualNotations.
Local Open Scope qualifiers.

(* Definitions *)

(* ### Syntax ### *)
(* We represent terms and types in locally nameless style. *)

(* Types *)
Inductive ty : Type :=
| TUnit : ty                             (* Unit base type*)
| TFun  : qual -> qual -> ty -> ty -> ty (* Dependent function type TFun q1 q2 T1 T2 ~> f((x: T1^q1) => T2^q2),
                                            where f (self reference) and x are bound in T2 and q2.
                                            Bound variables are represented by de Bruijn indices, where f ~> #0
                                            and x ~> #1. *)
| TRef  : ty -> ty                       (* Mutable reference type TRef T ~> Ref[T]. *)
.

(* Terms *)
Inductive tm : Type :=
| tunit   : tm              (* The unit value. *)
| tvar    : var -> tm       (* Term variable, either free (tvar $n) (de Bruijn level), or bound (tvar #n) (de Bruijn index). *)
| tabs    : tm  -> tm       (* Recursive lambda abstractions (tabs t) ~> λf(x).t, where f ~> #0 (self reference), and x ~> #1 (parameter). *)
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

Definition extends {A} (l1 l2 : list A): Prop := exists l', l1 = l' ++ l2.
Notation "x ⊇ y" := (extends x y) (at level 0).

(* Opening a term *)
Fixpoint open_rec_tm (k : nat) (u : tm) (t : tm) {struct t} : tm :=
  match t with
  | tunit           => tunit
  | tvar   (varF x) => tvar (varF x)
  | tvar   (varB x) => if Nat.eqb k x then u else tvar (varB x)
  | tabs    t       => tabs    (open_rec_tm (S (S k)) u t)
  | tapp    t1 t2   => tapp    (open_rec_tm k u t1) (open_rec_tm k u t2)
  | tloc    l       => tloc l
  | tref    t       => tref    (open_rec_tm k u t)
  | tderef  t       => tderef  (open_rec_tm k u t)
  | tassign t1 t2   => tassign (open_rec_tm k u t1) (open_rec_tm k u t2)
  end
.

(*simultaneous opening with self-ref and argument: *)
Definition open_tm (u u' t : tm) := open_rec_tm 1 u' (open_rec_tm 0 u t).
Definition open_tm' {A : Type} (env : list A) t :=
  open_rec_tm 1 (varF (S (length env))) (open_rec_tm 0 (varF (length env)) t).

(* Opening a qualifier *)
Definition open_qual (k : nat) (d' : qual) (d : qual) : qual :=
  match d, d' with
  | qset vs bs ls, qset vs' bs' ls' =>
    match NatSet.F.mem k bs with
    | true => qset (NatSet.F.union vs vs')
                  (NatSet.F.union (NatSet.F.remove k bs) bs')
                  (NatSet.F.union ls ls')
    | _         => qset vs bs ls
    end
  end.
Definition openq (u u' d : qual) : qual := open_qual 1 u' (open_qual 0 u d).
Definition openq' {A} (env : list A) d :=
  openq (just_fv (length env)) (just_fv (S (length env))) d.

(* Opening a type with a qualifier *)
Fixpoint open_rec_ty (k : nat) (d' : qual) (T : ty) : ty :=
  match T with
  | TUnit            => TUnit
  | TFun d1 d2 T1 T2 => TFun (open_qual k d' d1) (open_qual (S (S k)) d' d2) (open_rec_ty k d' T1) (open_rec_ty (S (S k)) d' T2)
  | TRef T           => TRef (open_rec_ty k d' T)
  end.

Definition open_ty (u u' : id) (T : ty) := (open_rec_ty 1 (just_fv u') (open_rec_ty 0 (just_fv u) T)).
Definition open_ty' {A : Type} (env : list A) (T : ty) := open_ty (length env) (S (length env)) T.

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

Definition splice_qual (n : nat) (d : qual) : qual :=
  match d with
  | qset vs bs ls => qset (splice_set n vs) bs ls
  end.

Fixpoint splice_ty (n : nat) (T : ty) {struct T} : ty :=
  match T with
  | TUnit            => TUnit
  | TFun d1 d2 T1 T2 => TFun (splice_qual n d1) (splice_qual n d2) (splice_ty n T1) (splice_ty n T2)
  | TRef T           => TRef (splice_ty n T)
  end.

Inductive closed_tm: nat(*B*) -> nat(*F*) -> nat(*Loc*) -> tm -> Prop :=
| cl_tsct : forall b f l,
    closed_tm b f l tunit
| cl_tvarb: forall b f l x,
    x < b ->
    closed_tm b f l (tvar (varB x))
| cl_tvarf: forall b f l x,
    x < f ->
    closed_tm b f l (tvar (varF x))
| cl_tabs:  forall b f l tm,
    closed_tm (S (S b)) f l tm ->
    closed_tm b f l (tabs tm)
| cl_tapp:  forall b f l tm1 tm2,
    closed_tm b f l tm1 ->
    closed_tm b f l tm2 ->
    closed_tm b f l (tapp tm1 tm2)
| cl_tloc: forall b f l l',
    l' < l ->
    closed_tm b f l (tloc l')
| cl_tref:  forall b f l tm,
    closed_tm b f l tm ->
    closed_tm b f l (tref tm)
| cl_tderef:  forall b f l tm,
    closed_tm b f l tm ->
    closed_tm b f l (tderef tm)
| cl_tassign:  forall b f l tm1 tm2,
    closed_tm b f l tm1 ->
    closed_tm b f l tm2 ->
    closed_tm b f l (tassign tm1 tm2)
.
#[global] Hint Constructors closed_tm : core.

Inductive closed_qual : nat(*B*) -> nat(*F*) -> nat(*Loc*) -> qual -> Prop :=
| cl_qset : forall b f l vs bs ls,
    bound vs <= f ->
    bound bs <= b ->
    bound ls <= l ->
    closed_qual b f l (qset vs bs ls)
.
#[global] Hint Constructors closed_qual : core.

Inductive closed_ty : nat(*B*) -> nat(*F*) -> nat(*Loc*) -> ty -> Prop :=
| cl_TUnit : forall b f l,
    closed_ty b f l TUnit
| cl_TRef : forall b f l T,
    closed_ty 0 0 0 T ->
    closed_ty b f l (TRef T)
| cl_TFun : forall b f l d1 d2 T1 T2,
    closed_qual b f l d1 ->
    closed_qual (S (S b)) f l d2 ->
    closed_ty b f l T1 ->
    closed_ty (S (S b)) f l T2 ->
    closed_ty b f l (TFun d1 d2 T1 T2)
.
#[global] Hint Constructors closed_ty : core.

Inductive qstp : tenv -> senv -> qual -> qual -> Prop :=
| qs_sq : forall Γ Σ d1 d2,
    d1 ⊑ d2 ->
    closed_qual 0 (length Γ) (length Σ) d2 ->
    qstp Γ Σ d1 d2
.
#[global] Hint Constructors qstp : dsub.

Definition splice_tenv (n : nat) (Γ : tenv) : tenv :=
  map (fun p => ((splice_ty n (fst p)), (splice_qual n (snd p)))) Γ.

Inductive stp : tenv -> senv -> ty -> qual -> ty -> qual -> Prop :=
| s_base : forall Γ Σ d1 d2,
    qstp Γ Σ d1 d2 ->
    stp Γ Σ TUnit d1 TUnit d2
| s_ref : forall Γ Σ T1 T2 d1 d2,
    qstp Γ Σ d1 d2 ->
    stp [] [] T1 ∅ T2 ∅ -> (* we don't have bottom, so use ∅ here *)
    stp [] [] T2 ∅ T1 ∅ ->
    stp Γ Σ (TRef T1) d1 (TRef T2) d2
| s_fun : forall Γ Σ T1 d1 T2 d2 T3 d3 T4 d4 d5 d6,
    closed_ty 0 (length Γ) (length Σ) (TFun d1 d2 T1 T2) ->
    closed_ty 0 (length Γ) (length Σ) (TFun d3 d4 T3 T4) ->
    qstp Γ Σ d5 d6 ->
    stp Γ Σ T3 d3 T1 d1 ->
    stp ((T3,d3) :: (TFun d1 d2 T1 T2, d5) :: Γ) Σ (open_ty' Γ T2) (openq' Γ d2) (open_ty' Γ T4) (openq' Γ d4) ->
    stp Γ Σ (TFun d1 d2 T1 T2) d5 (TFun d3 d4 T3 T4) d6
| s_trans : forall Γ Σ T1 d1 T2 d2 T3 d3,
    stp Γ Σ T1 d1 T2 d2 -> stp Γ Σ T2 d2 T3 d3 -> stp Γ Σ T1 d1 T3 d3
.
#[global] Hint Constructors stp : dsub.

(* Specifies that the variable x's qualifier is subsumed by q in context Γ *)
Inductive saturated_var (Γ : tenv) (Σ : senv) (x : id) (q : qual) : Prop :=
| sat_var : forall U q',
    indexr x Γ = Some (U, q') ->
    q' ⊑ q ->
    closed_qual 0 x (length Σ) q' ->
    saturated_var Γ Σ x q.
Arguments sat_var {Γ Σ x q}.
#[global] Hint Constructors saturated_var : core.

(* Specifies that q is transitively closed w.r.t. Γ, i.e., each variable x in q is a saturated variable in the above sense. *)
Definition saturated (Γ : tenv) (Σ : senv) (q: qual) : Prop := forall x, (varF x) ∈ᵥ q -> saturated_var Γ Σ x q.

Inductive has_type : tenv -> qual -> senv -> tm -> ty -> qual -> Prop :=
| t_base : forall Γ Σ φ,
    closed_qual 0 (length Γ) (length Σ) φ ->
    has_type Γ φ Σ tunit TUnit ∅ (* use ∅ instead of bottom *)

| t_var : forall Γ φ Σ x T d,
    indexr x Γ = Some (T,d) ->
    (just_fv x) ⊑ φ ->
    closed_qual 0 (length Γ) (length Σ) φ ->
    closed_ty 0 x (length Σ) T ->
    closed_qual 0 x (length Σ) d ->
    has_type Γ φ Σ (tvar (varF x)) T (just_fv x)

| t_abs: forall Γ φ Σ T1 d1 T2 d2 df t,
    closed_tm 2 (length Γ) (length Σ) t ->
    closed_ty 0 (length Γ) (length Σ) (TFun d1 d2 T1 T2) ->
    closed_qual 0 (length Γ) (length Σ) φ ->
    df ⊑ φ ->
    has_type ((T1,d1) :: ((TFun d1 d2 T1 T2), df) :: Γ) (df ⊔ (just_fv (length Γ)) ⊔ (just_fv (S (length Γ)))) Σ (open_tm' Γ t) (open_ty' Γ T2) (openq' Γ d2) ->
    has_type Γ φ Σ (tabs t) (TFun d1 d2 T1 T2) df

| t_app : forall Γ φ Σ t1 d1 t2 d2 df T1 T2,
    has_type Γ φ Σ t1 (TFun (df ⋒ d1) d2 T1 T2) df ->
    has_type Γ φ Σ t2 T1 d1 ->
    closed_ty 0 (length Γ) (length Σ) T2 ->
    (openq ∅ ∅ d2) ⊑ φ ->
    saturated Γ Σ d1 ->
    saturated Γ Σ df ->
    has_type Γ φ Σ (tapp t1 t2) T2 (openq df d1 d2)

| t_loc : forall Γ φ Σ l T,
    closed_qual 0 (length Γ) (length Σ) φ ->
    indexr l Σ = Some T ->
    closed_ty 0 0 0 T ->
    (just_loc l) ⊑ φ ->
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
    d2 ⊑ φ ->
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
    step (tapp (tabs t) v) σ (open_tm (tabs t) v t) σ
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

Definition subst_q (q : qual) (v : nat) (q' : qual) : qual :=
  match q with
  | qset fvs bvs ls =>
    match NatSet.F.mem v fvs with
    | true =>  match q' with
              | qset fvs' bvs' ls' =>
                qset (NatSet.F.union (unsplice_set 0 (NatSet.F.remove v fvs)) fvs')
                     (NatSet.F.union bvs bvs')
                     (NatSet.F.union ls ls')
              end
    | false=> qset (unsplice_set 0 (NatSet.F.remove v fvs)) bvs ls
    end
  end.

Fixpoint subst_ty (T : ty) (v : nat) (q : qual) : ty :=
  match T with
  | TUnit            => TUnit
  | TFun q1 q2 T1 T2 => TFun (subst_q q1 v q) (subst_q q2 v q) (subst_ty T1 v q) (subst_ty T2 v q)
  | TRef T           => TRef (subst_ty T v q)
  end.

Definition subst_tenv (Γ : tenv) (v : nat) (q1 : qual) : tenv :=
  map (fun p => match p with
             | (T,q') => ((subst_ty T v q1) , (subst_q q' v q1))
             end) Γ.

Module SubstitutionNotations.
  Declare Scope substitutions.
  Notation "{ v1 |-> t1 ; t2 }ᵗ t" := (subst_tm (subst_tm t v1 t1) v1 t2) (at level 10) : substitutions.
  Notation "{ v1 |-> t1 }ᵗ t" := (subst_tm t v1 t1) (at level 10) : substitutions.
  Notation "{ v1 |-> q1 ; q2 }ᵈ q" := (subst_q (subst_q q v1 q1) v1 q2) (at level 10) : substitutions.
  Notation "{ v1 |-> q1 }ᵈ q" := (subst_q q v1 q1) (at level 10) : substitutions.
  Notation "{ v1 |-> q1 ; q2  }ᵀ T" := (subst_ty (subst_ty T v1 q1) v1 q2) (at level 10) : substitutions.
  Notation "{ v1 |-> q1 }ᵀ T" := (subst_ty T v1 q1) (at level 10) : substitutions.
  Notation "{ v1 |-> q1 }ᴳ G" := (subst_tenv G v1 q1) (at level 10) : substitutions.
  Notation "{ v1 |-> q1 ; q2 }ᴳ G" := (subst_tenv (subst_tenv G v1 q1) v1 q2) (at level 10) : substitutions.
End SubstitutionNotations.
Import SubstitutionNotations.
Local Open Scope substitutions.

(* Indicates the relation between an assumption's qualifier and the qualifier we substitute for the variable.
   This helps ensure that the substitution lemma can be expressed uniformly on a single variable. *)
Inductive Substq : qual -> qual -> Prop :=
| SFun : forall df, Substq df df           (* we substitute a recursive function into itself *)
| SArg : forall df dx, Substq (df ⋒ dx) dx (* we substitute an argument to a function call, note the difference.*)
.
#[global] Hint Constructors Substq : core.

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
  closed_qual 0 0 (length Σ) d ->
  vtp Σ tunit TUnit d

| vtp_loc:  forall Σ l T U d,
  closed_qual 0 0 (length Σ) d ->
  closed_ty 0 0 0 T ->
  indexr l Σ = Some T ->
  stp [] [] T ∅ U ∅ -> (* we don't have bottom, so use ∅ here *)
  stp [] [] U ∅ T ∅ ->
  qstp [] Σ (just_loc l) d ->
  vtp Σ (tloc l) (TRef U) d

| vtp_abs: forall Σ T1 d1 T2 d2 T3 d3 T4 d4 df1 df2 t,
  closed_tm 2 0 (length Σ) t ->
  closed_qual 0 0 (length Σ) df2 ->
  closed_ty 0 0 (length Σ) (TFun d3 d4 T3 T4) ->  (* supertype *)
  closed_ty 0 0 (length Σ) (TFun d1 d2 T1 T2) ->  (* subtype *)
  has_type [(T1,d1) ; (TFun d1 d2 T1 T2, df1)] (df1 ⊔ (just_fv 0) ⊔ (just_fv 1)) Σ (open_tm' ([]: tenv) t) (open_ty' ([]: tenv) T2) (openq' ([]: tenv) d2) ->
  stp [] Σ T3 d3 T1 d1 ->
  qstp [] Σ df1 df2 ->
  stp [(T3, d3) ; (TFun d1 d2 T1 T2, df1)] Σ (open_ty' ([]: tenv) T2) (openq' ([] : tenv) d2) (open_ty' ([]: tenv) T4) (openq' ([]: tenv) d4) ->
  vtp Σ (tabs t) (TFun d3 d4 T3 T4) df2
  .
#[global] Hint Constructors vtp : core.

(* The concluding statement of the preservation part of type safety, i.e., typing is preserved after a step under an extended store, so
   that the initial qualifier is increased by at most a fresh storage effect. *)
Inductive preserve (Γ : tenv) (Σ : senv) (t' : tm) (T : ty) (d : qual) (σ' : store) : Prop :=
| Preserve : forall Σ' d',
    Σ' ⊇ Σ ->
    CtxOK Γ (ldom Σ') Σ' σ' ->
    disjointq Σ Σ' d' ->
    has_type Γ (ldom Σ') Σ' t' T (d ⋓ d') ->
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
    has_type [] (ldom Σ') Σ' t1' T1 q1' ->
    has_type [] (ldom Σ'') Σ'' t2' T2 q2' ->
    q1' ⊓ q2' ⊑ ∅ ->
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

Lemma extends_ldom : forall {Σ' Σ : senv}, (Σ') ⊇ (Σ) -> ldom Σ ⊑ ldom Σ'.
  intros. inversion H. unfold ldom. simpl.
  intuition. unfold dom.
  assert (length Σ' = length (x ++ Σ)). subst. auto.
  rewrite app_length in H1. assert (length Σ <= length Σ'). lia.
  apply nset_subset. lia.
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
  intros. simpl. rewrite splice_set_empty. auto.
Qed.
#[global] Hint Resolve splice_qual_empty : core.

Lemma closed_qual_sub : forall {b f l d}, closed_qual b f l d -> forall {d'}, d' ⊑ d -> closed_qual b f l d'.
Proof.
  intros. inversion H. subst. destruct d'.
  inversion H0. destruct H5. constructor.
  eapply subset_bound; eauto.
  eapply subset_bound; eauto.
  eapply subset_bound; eauto.
Qed.

Lemma closed_qual_empty : forall {b f l}, closed_qual b f l ∅.
  intros. constructor; rewrite bound_empty; lia.
Qed.
#[global] Hint Resolve closed_qual_empty : core.

Lemma closed_qual_ldom : forall {Σ : senv}, closed_qual 0 0 (length Σ) (ldom Σ).
  intros. unfold ldom. constructor. 1,2 : rewrite bound_empty; auto.
  rewrite bound_dom. auto.
Qed.
#[global] Hint Resolve closed_qual_ldom : core.

Lemma closed_qual_cong : forall {b f l d},
    closed_qual b f l d -> forall {d'}, d ≡ d' -> closed_qual b f l d'.
Proof.
  intros b f l d H. induction H; intros d' Heq.
  destruct d'. inversion Heq. destruct H3. constructor.
  eapply set_eq_bound; eauto.
  eapply set_eq_bound; eauto.
  eapply set_eq_bound; eauto.
Qed.

Lemma just_fv_closed : forall {x b f l}, x < f <-> closed_qual b f l (just_fv x).
Proof.
  split; intros.
  - unfold just_fv. constructor; unfold bound.
    rewrite max_elt_singleton. lia.
    rewrite max_elt_empty. lia.
    rewrite max_elt_empty. lia.
  - inversion H. subst.
    unfold bound in H6. rewrite max_elt_singleton in H6. lia.
Qed.

Lemma just_loc_closed : forall {x b f l}, x < l <-> closed_qual b f l (just_loc x).
Proof.
  split; intros.
  - unfold just_loc. constructor; unfold bound.
    rewrite max_elt_empty. lia.
    rewrite max_elt_empty. lia.
    rewrite max_elt_singleton. lia.
  - inversion H. subst. unfold bound in H8.
    rewrite max_elt_singleton in H8. lia.
Qed.

Lemma qstp_closed : forall {Γ Σ d1 d2}, qstp Γ Σ d1 d2 -> closed_qual 0 (length Γ) (length Σ) d1 /\ closed_qual 0 (length Γ) (length Σ) d2.
  intros Γ Σ d1 d2 HSQ. induction HSQ; intuition.
  eapply closed_qual_sub; eauto.
Qed.

Lemma qstp_refl : forall {d d'}, d ≡ d' -> forall {Γ Σ}, closed_qual 0 (length Γ) (length Σ) d -> qstp Γ Σ d d'.
  intros d d' Heq Γ Σ Hc. constructor. destruct d. destruct d'. qdec.
  eapply closed_qual_cong; eauto.
Qed.

Lemma qstp_trans : forall {Γ Σ d1 d2}, qstp Γ Σ d1 d2 -> forall {d3}, qstp Γ Σ d2 d3 -> qstp Γ Σ d1 d3.
  intros. inversion H. subst. inversion H0. subst. constructor.
  eapply subqual_trans; eauto. auto.
Qed.

(* This property is specific to the restricted version of the system we consider here *)
Lemma qstp_inv : forall {Γ Σ d1 d2}, qstp Γ Σ d1 d2 -> d1 ⊑ d2.
  intros. inversion H. auto.
Qed.

Lemma splice_tenv_length : forall {n Γ}, length (splice_tenv n Γ) = length Γ.
  intros. unfold splice_tenv. rewrite map_length. auto.
Qed.

Lemma closed_tm_monotone : forall {t b l f}, closed_tm b f l t -> forall {b' f' l'}, b <= b' -> f <= f' -> l <= l' -> closed_tm b' f' l' t.
  intros T b f l H. induction H; intuition.
Qed.

Lemma closed_qual_monotone : forall {f b l d}, closed_qual b f l d -> forall {b' f' l'}, b <= b' -> f <= f' -> l <= l' -> closed_qual b' f' l' d.
  intros. destruct d; intuition.
  inversion H. subst. constructor; lia.
Qed.

Lemma closed_ty_monotone : forall {T b l f}, closed_ty b f l T -> forall {b' f' l'}, b <= b' -> f <= f' -> l <= l' -> closed_ty b' f' l' T.
  intros T b f l H. induction H; intuition.
  constructor; auto. eapply closed_qual_monotone; eauto.
  eapply closed_qual_monotone; eauto. lia.
  eapply IHclosed_ty2; eauto. lia.
Qed.

Lemma closed_tm_open_id : forall {t b f l}, closed_tm b f l t -> forall {n}, b <= n -> forall {x}, (open_rec_tm n x t) = t.
  intros t b f l H. induction H; intros; simpl; auto;
    try solve [erewrite IHclosed_tm1; eauto; erewrite IHclosed_tm2; eauto; lia | erewrite IHclosed_tm; eauto; lia].
  destruct (Nat.eqb n x) eqn:Heq; auto. apply Nat.eqb_eq in Heq. lia.
Qed.

Lemma closed_qual_open_id : forall {d b f l},
    closed_qual b f l d -> forall {n}, b <= n -> forall {x}, (open_qual n x d) = d.
Proof.
  intros. destruct d; simpl. auto. destruct x.
  inversion H. subst.
  replace (NatSet.F.mem n t0) with false. auto.
  unfold bound in H8.
  destruct (NatSet.F.max_elt t0) eqn:Hmax.
  - symmetry.
    apply NatSetProperties.FM.not_mem_iff.
    eapply max_gt_bound_not_in; eauto.
  - specialize (@NatSet.F.max_elt_3 _ Hmax) as Hmt. symmetry.
    apply NatSetProperties.FM.not_mem_iff. intro HF.
    apply NatSetProperties.empty_is_empty_1 in Hmt.
    apply NatSet.eq_if_Equal in Hmt. rewrite Hmt in HF.
    rewrite NatSetFacts.empty_iff in HF. apply HF.
Qed.

Lemma closed_ty_open_id : forall {T b f l}, closed_ty b f l T -> forall {n}, b <= n -> forall {x}, (open_rec_ty n x T) = T.
  intros T b f l H. induction H; intros; simpl; auto;
    try solve [erewrite IHclosed_ty1; eauto; erewrite IHclosed_ty2; eauto; lia | erewrite IHclosed_ty; eauto; lia].
  erewrite IHclosed_ty1; eauto; erewrite IHclosed_ty2; eauto.
  erewrite closed_qual_open_id; eauto. erewrite closed_qual_open_id; eauto.
  all : lia.
Qed.

Lemma closed_tm_open : forall {T b f l}, closed_tm (S b) f l T -> forall {x}, x < f -> closed_tm b f l (open_rec_tm b (varF x) T).
  induction T; intros; simpl; intuition; inversion H; subst; try constructor;
  try solve [apply IHT1; auto | apply IHT2; auto | apply IHT; auto ].
  destruct (Nat.eqb b x0) eqn:Heq; intuition.
  apply Nat.eqb_neq in Heq. constructor. lia. auto. auto.
Qed.

Lemma closed_qual_open : forall {d b f l},
    closed_qual (S b) f l d ->
    forall {x}, x < f -> closed_qual b f l (open_qual b (just_fv x) d).
Proof.
  intros. destruct d. simpl. inversion H. subst.
  destruct (NatSet.F.mem b t0) eqn:Heq.
  - constructor.
    + pose (@bound_singleton x).
      pose (@union_bound_max t (NatSet.F.singleton x)). lia.
    + specialize (@NatSetProperties.empty_union_2 {}N (NatSet.F.remove b t0) NatSet.F.empty_1) as HU.
      apply NatSet.eq_if_Equal in HU. rewrite HU. clear HU.
      unfold bound in H8.
      apply NatSet.F.mem_2 in Heq.
      destruct (NatSet.F.max_elt t0) eqn:Hmax.
      * inversion H8. subst. unfold bound.
        destruct (NatSet.F.max_elt (NatSet.F.remove b t0)) eqn:Hmax'.
        eapply remove_max_bound; eauto. lia.
        subst. assert (e < b) by lia. unfold bound.
        destruct (NatSet.F.max_elt (NatSet.F.remove b t0)) eqn:Hmax'.
        eapply remove_nonexist_bound; eauto. lia.
      * specialize (@NatSet.F.max_elt_3 _ Hmax) as H'.
        apply NatSetProperties.empty_is_empty_1 in H'.
        apply NatSet.eq_if_Equal in H'. rewrite H' in Heq.
        rewrite NatSetFacts.empty_iff in Heq. inversion Heq.
    + specialize (@NatSetProperties.empty_union_2 {}N t1 NatSet.F.empty_1) as HU.
      apply NatSet.eq_if_Equal in HU. rewrite HU. auto.
  - constructor; auto. unfold bound in H8. unfold bound.
    rewrite <- NatSetProperties.FM.not_mem_iff in Heq.
    destruct (NatSet.F.max_elt t0) eqn:Hmax.
    + inversion H8. subst. specialize (@NatSet.F.max_elt_1 _ _ Hmax) as Heq'.
      contradiction. lia.
    + lia.
Qed.

Lemma closed_ty_open : forall {T b f l}, closed_ty (S b) f l T -> forall {x}, x < f -> closed_ty b f l (open_rec_ty b (just_fv x) T).
  induction T; intros; simpl; intuition; inversion H; subst; try constructor;
    try solve [apply IHT1; auto | apply IHT2; auto | apply IHT; auto ].
  1,2 : eapply closed_qual_open; eauto.
  erewrite closed_ty_open_id; eauto. lia.
Qed.

Lemma closed_tm_open' : forall {T b f l}, closed_tm (S b) f l T -> forall {x}, x <= f -> forall {t}, closed_tm 0 x l t -> closed_tm b f l (open_rec_tm b t T).
  induction T; intros; simpl; intuition; inversion H; subst; try constructor;
  try solve [eapply IHT1; eauto | eapply IHT2; eauto | eapply IHT; eauto ].
  destruct (Nat.eqb b x0) eqn:Heq; intuition. eapply closed_tm_monotone; eauto; lia.
  apply Nat.eqb_neq in Heq. constructor. lia. auto. auto.
Qed.

Lemma closed_qual_open' : forall {d b f l},
    closed_qual (S b) f l d ->
    forall {x}, x <= f ->
    forall {d'}, closed_qual 0 x l d' -> closed_qual b f l (open_qual b d' d).
Proof.
  destruct d; intros; simpl; intuition. inversion H. subst.
  destruct d'.
  inversion H1. subst.
  destruct (NatSet.F.mem b t0) eqn:Hmem.
  - constructor.
    + specialize (@union_bound_max t t2) as Hbound. lia.
    + unfold bound in H9.
      destruct (NatSet.F.max_elt t0) eqn:Hmax.
      assert (e <= b) by lia.
      specialize (@union_bound_max (NatSet.F.remove b t0) t3) as Hbound.
      specialize (@remove_max_bound' _ _ _ Hmax Hmem H2) as Hr. lia.
      specialize (@max_elt_none_mem _ _ Hmax Hmem) as bot. inversion bot.
    + specialize (@union_bound_max t1 t4) as Hbound. lia.
  - constructor; auto. unfold bound in H9. unfold bound.
    destruct (NatSet.F.max_elt t0) eqn:Hmax.
    inversion H9. subst.
    specialize (@NatSet.F.max_elt_1 _ _ Hmax) as HIn.
    rewrite <- NatSetProperties.FM.not_mem_iff in Hmem.
    contradiction. subst. lia. lia.
Qed.

Lemma closed_ty_open' : forall {T b f l}, closed_ty (S b) f l T -> forall {x}, x <= f -> forall {d}, closed_qual 0 x l d -> closed_ty b f l (open_rec_ty b d T).
  induction T; intros; simpl; intuition; inversion H; subst; try constructor;
    try solve [eapply IHT1; eauto | eapply IHT2; eauto | eapply IHT; eauto ].
  1,2 : eapply closed_qual_open'; eauto.
  erewrite closed_ty_open_id; eauto. lia.
Qed.

Lemma closed_tm_open_ge : forall {T b f l}, closed_tm (S b) f l T -> forall {x}, f <= x -> closed_tm b (S x) l (open_rec_tm b (varF x) T).
  induction T; intros; simpl; intuition; inversion H; subst; try constructor;
      try solve [eapply IHT1; eauto | eapply IHT2; eauto | eapply IHT; eauto ].
  destruct (Nat.eqb b x0) eqn:Heq. intuition.
  apply Nat.eqb_neq in Heq. inversion H. subst.
  constructor. lia. lia. auto.
Qed.

Lemma closed_qual_open_ge : forall {d b f l},
    closed_qual (S b) f l d ->
    forall {x}, f <= x -> closed_qual b (S x) l (open_qual b (just_fv x) d).
Proof.
  destruct d; intros; simpl; intuition. inversion H. subst.
  destruct (NatSet.F.mem b t0) eqn: Hmem.
  - constructor.
    + eapply bound_increase; eauto.
    + specialize (@NatSetProperties.empty_union_2 {}N (NatSet.F.remove b t0) NatSet.F.empty_1) as HU.
      apply NatSet.eq_if_Equal in HU. rewrite HU. clear HU.
      unfold bound. unfold bound in H8.
      destruct (NatSet.F.max_elt t0) eqn:Hmax1; inversion H8. subst.
      destruct (NatSet.F.max_elt (NatSet.F.remove b t0)) eqn:Hmax2.
      eapply remove_max_bound; eauto. lia.
      subst. destruct (NatSet.F.max_elt (NatSet.F.remove b t0)) eqn:Hmax2.
      assert (e < b) by lia. eapply remove_nonexist_bound; eauto. lia.
      subst. specialize (@max_elt_none_mem _ _ Hmax1 Hmem) as bot. inversion bot.
    + specialize (@NatSetProperties.empty_union_2 {}N t1 NatSet.F.empty_1) as HU.
      apply NatSet.eq_if_Equal in HU. rewrite HU. auto.
  - constructor; try lia.
    unfold bound in H8. unfold bound. destruct (NatSet.F.max_elt t0) eqn:Hmax.
    inversion H8; subst. specialize (@NatSet.F.max_elt_1 _ _ Hmax) as HIn.
    rewrite <- NatSetProperties.FM.not_mem_iff in Hmem. contradiction. lia. lia.
Qed.

Lemma closed_ty_open_ge : forall {T b f l}, closed_ty (S b) f l T -> forall {x}, f <= x -> closed_ty b (S x) l (open_rec_ty b (just_fv x) T).
  induction T; intros; simpl; intuition; inversion H; subst; try constructor;
    try solve [eapply IHT1; eauto | eapply IHT2; eauto | eapply IHT; eauto ].
  1,2:eapply closed_qual_open_ge; eauto.
  erewrite closed_ty_open_id; eauto. lia.
Qed.

Lemma closed_open_succ : forall {T b f l}, closed_tm b f l T -> forall {j}, closed_tm b (S f) l (open_rec_tm j (varF f) T).
  induction T; intros; simpl; intuition; inversion H; subst; try constructor;
    try solve [eapply IHT1; eauto | eapply IHT2; eauto | eapply IHT; eauto ].
    destruct (Nat.eqb j x) eqn:Heq. intuition.
    apply Nat.eqb_neq in Heq. inversion H. subst. intuition. lia. auto.
Qed.

Lemma closed_qual_open_succ : forall {d b f l},
    closed_qual b f l d ->
    forall {j}, closed_qual b (S f) l (open_qual j (just_fv f) d).
Proof.
  destruct d; intros; simpl; intuition. inversion H. subst.
  destruct (NatSet.F.mem j t0) eqn:Hmem.
  - constructor. specialize (@union_bound_max t (NatSet.F.singleton f)) as Hmax.
    rewrite bound_singleton in Hmax. lia. rewrite empty_union_right.
    apply remove_preserves_bound; auto. rewrite empty_union_right. lia.
  - constructor; auto.
Qed.

Lemma closed_ty_open_succ : forall {T b f l}, closed_ty b f l T -> forall {j}, closed_ty b (S f) l (open_rec_ty j (just_fv f) T).
  induction T; intros; simpl; intuition; inversion H; subst; try constructor;
    try solve [eapply IHT1; eauto | eapply IHT2; eauto | eapply IHT; eauto ].
  1,2:eapply closed_qual_open_succ; eauto.
  erewrite closed_ty_open_id; eauto. lia.
Qed.

Lemma closed_tm_open_succ : forall {t b f l}, closed_tm b f l t -> forall {j}, closed_tm b (S f) l (open_rec_tm j $f t).
  induction t; intros; simpl; intuition; inversion H; subst; try constructor;
    try solve [eapply IHt1; eauto | eapply IHt2; eauto | eapply IHt; eauto ].
  bdestruct (j =? x); intuition. lia. auto.
Qed.

Lemma open_rec_tm_commute : forall t i j x y, i <> j -> open_rec_tm i (varF x) (open_rec_tm j (varF y) t) = open_rec_tm j (varF y) (open_rec_tm i (varF x) t).
  induction t; intros; simpl; eauto;
    try solve [rewrite IHt1; eauto; rewrite IHt2; eauto | rewrite IHt; eauto].
  destruct v. intuition.
  destruct (Nat.eqb i i0) eqn:Hii0; destruct (Nat.eqb j i0) eqn:Hji0; simpl;
    try rewrite Hii0; try rewrite Hji0; auto.
  apply Nat.eqb_eq in Hii0. apply Nat.eqb_eq in Hji0. subst. contradiction.
Qed.

Lemma open_qual_commute : forall d i j x y, i <> j -> open_qual i (just_fv x) (open_qual j (just_fv y) d) = open_qual j (just_fv y) (open_qual i (just_fv x) d).
  destruct d; intros; simpl; intuition.
  destruct (NatSet.F.mem j t0) eqn:Heqj; destruct (NatSet.F.mem i t0) eqn:Heqi; simpl.
  destruct (NatSet.F.mem i (NatSet.F.union (NatSet.F.remove j t0) {}N)) eqn:Hmem;
  destruct (NatSet.F.mem j (NatSet.F.union (NatSet.F.remove i t0) {}N)) eqn:Hmem'.
  f_equal; qdec. f_equal.
  apply NatSet.F.mem_2 in Heqj. apply NatSet.F.mem_2 in Heqi.
  apply NatSet.F.mem_2 in Hmem. rewrite <- NatSetProperties.FM.not_mem_iff in Hmem'.
  NatSetNotin.notin_simpl_hyps. fnsetdec.
  apply NatSet.F.mem_2 in Heqj. apply NatSet.F.mem_2 in Heqi. apply NatSet.F.mem_2 in Hmem.
  rewrite <- NatSetProperties.FM.not_mem_iff in Hmem'.
  NatSetNotin.notin_simpl_hyps. fnsetdec. fnsetdec.
  apply NatSet.F.mem_2 in Heqj. apply NatSet.F.mem_2 in Heqi. apply NatSet.F.mem_2 in Hmem'.
  rewrite <- NatSetProperties.FM.not_mem_iff in Hmem.
  NatSetNotin.notin_simpl_hyps. f_equal; fnsetdec.
  rewrite <- NatSetProperties.FM.not_mem_iff in Hmem'.
  rewrite <- NatSetProperties.FM.not_mem_iff in Hmem.
  apply NatSet.F.mem_2 in Heqj. apply NatSet.F.mem_2 in Heqi.
  NatSetNotin.notin_simpl_hyps. f_equal; fnsetdec.
  rewrite Heqj. destruct (NatSet.F.mem i (NatSet.F.union (NatSet.F.remove j t0) {}N)) eqn:Hmem.
  rewrite <- NatSetProperties.FM.not_mem_iff in Heqi.
  apply NatSet.F.mem_2 in Hmem. apply NatSet.F.mem_2 in Heqj. f_equal; fnsetdec. auto.
  rewrite Heqi. destruct (NatSet.F.mem j (NatSet.F.union (NatSet.F.remove i t0) {}N)) eqn:Hmem.
  rewrite <- NatSetProperties.FM.not_mem_iff in Heqj.
  apply NatSet.F.mem_2 in Heqi. apply NatSet.F.mem_2 in Hmem. f_equal; fnsetdec. auto.
  rewrite Heqj. rewrite Heqi. auto.
Qed.

Lemma open_rec_ty_commute : forall T i j x y,
    i <> j -> open_rec_ty i (just_fv x) (open_rec_ty j (just_fv y) T) = open_rec_ty j (just_fv y) (open_rec_ty i (just_fv x) T).
  induction T; intros; simpl; eauto;
    try solve [erewrite IHT1; eauto; erewrite IHT2; eauto | erewrite IHT; eauto].
  erewrite open_qual_commute; eauto.
  erewrite open_qual_commute with (i:=(S (S i))); eauto.
  erewrite IHT1; eauto; erewrite IHT2; eauto.
Qed.

Lemma open_rec_tm_commute' : forall t i j x t' f l, i <> j -> closed_tm 0 f l t' -> open_rec_tm i (varF x) (open_rec_tm j t' t) = open_rec_tm j t' (open_rec_tm i (varF x) t).
  induction t; intros; simpl; eauto;
    try solve [erewrite IHt1; eauto; erewrite IHt2; eauto | erewrite IHt; eauto].
  destruct v. intuition.
  destruct (Nat.eqb i i0) eqn:Hii0; destruct (Nat.eqb j i0) eqn:Hji0; simpl;
    try rewrite Hii0; try rewrite Hji0; auto.
  apply Nat.eqb_eq in Hii0. apply Nat.eqb_eq in Hji0. subst. contradiction.
  eapply closed_tm_open_id; eauto. lia.
Qed.

Lemma open_qual_commute' : forall d i j x d' f l,
    i <> j -> closed_qual 0 f l d' ->
    open_qual i (just_fv x) (open_qual j d' d) = open_qual j d' (open_qual i (just_fv x) d).
Proof.
  intros. destruct d; intros. destruct d'. inversion H0. subst. simpl in *.
  unfold open_qual. destruct (just_fv x) eqn:Hfv. unfold just_fv in Hfv.
  inversion Hfv. subst.
  destruct (NatSet.F.mem j t0) eqn:Hjt0.
  - destruct (NatSet.F.mem i t0) eqn:Hit0.
    + destruct (NatSet.F.mem i (NatSet.F.union (NatSet.F.remove j t0) t3)) eqn:Hiu;
        destruct (NatSet.F.mem j (NatSet.F.union (NatSet.F.remove i t0) {}N)) eqn:Hju;
        try fnsetdec.
      f_equal. fnsetdec.
      rewrite empty_union_right. rewrite empty_union_right.
      rewrite empty_union_right in Hju.
      apply bound_0_empty in H8. rewrite H8 in *.
      rewrite empty_union_right in *.
      rewrite empty_union_right in *. fnsetdec.
      rewrite empty_union_right. rewrite empty_union_right. auto.
      rewrite empty_union_right in Hju.
      specialize (@NatSetFacts.remove_neq_b t0 _ _ H) as Hru.
      rewrite Hjt0 in Hru. rewrite Hju in Hru. inversion Hru.
      assert (j <> i) by lia.
      specialize (@NatSetFacts.remove_neq_b t0 _ _ H1) as Hru.
      apply bound_0_empty in H8. rewrite H8 in Hiu.
      rewrite empty_union_right in Hiu. rewrite Hiu in Hru. rewrite Hit0 in Hru.
      inversion Hru. rewrite empty_union_right in Hju.
      specialize (@NatSetFacts.remove_neq_b t0 _ _ H) as Hru.
      rewrite Hjt0 in Hru. rewrite Hju in Hru. inversion Hru.
    + apply bound_0_empty in H8. rewrite H8 in *.
      rewrite empty_union_right in *.
      rewrite Hjt0. assert (j <> i) by lia.
      rewrite (@NatSetFacts.remove_neq_b t0 _ _ H1). rewrite Hit0. auto.
  - destruct (NatSet.F.mem i t0) eqn:Hit0.
    rewrite empty_union_right in *. rewrite empty_union_right in *.
    rewrite (@NatSetFacts.remove_neq_b t0 _ _ H). rewrite Hjt0. auto.
    rewrite Hjt0. auto.
Qed.

Lemma open_rec_ty_commute' : forall T i j x d f l, i <> j -> closed_qual 0 f l d -> open_rec_ty i (just_fv x) (open_rec_ty j d T) = open_rec_ty j d (open_rec_ty i (just_fv x) T).
  induction T; intros; simpl; eauto;
    try solve [erewrite IHT1; eauto; erewrite IHT2; eauto | erewrite IHT; eauto].
  erewrite open_qual_commute'; eauto. erewrite open_qual_commute'; eauto.
  erewrite IHT1; eauto; erewrite IHT2; eauto.
Qed.

Lemma open_rec_tm_commute'' : forall t i j t' t'' f l, i <> j -> closed_tm 0 f l t' -> closed_tm 0 f l t'' -> open_rec_tm i t'' (open_rec_tm j t' t) = open_rec_tm j t' (open_rec_tm i t'' t).
  induction t; intros; simpl; eauto;
    try solve [erewrite IHt1; eauto; erewrite IHt2; eauto | erewrite IHt; eauto].
  destruct v. intuition.
  destruct (Nat.eqb i i0) eqn:Hii0; destruct (Nat.eqb j i0) eqn:Hji0; simpl;
    try rewrite Hii0; try rewrite Hji0; auto.
  apply Nat.eqb_eq in Hii0. apply Nat.eqb_eq in Hji0. subst. contradiction.
  symmetry. eapply closed_tm_open_id; eauto. lia. eapply closed_tm_open_id; eauto. lia.
Qed.

Lemma open_qual_commute'' : forall d i j d' d'' f l,
    i <> j -> closed_qual 0 f l d' -> closed_qual 0 f l d'' ->
    open_qual i d'' (open_qual j d' d) = open_qual j d' (open_qual i d'' d).
Proof.
  destruct d; destruct d'; destruct d''; intros; simpl; intuition.
  unfold open_qual. inversion H0. subst. inversion H1. subst.
  apply bound_0_empty in H9. apply bound_0_empty in H12.
  subst. rewrite empty_union_right in *. rewrite empty_union_right in *.
  destruct (NatSet.F.mem j t0) eqn:Hj.
  - assert (j <> i) by lia.
    rewrite (@NatSetFacts.remove_neq_b t0 _ _ H2).
    destruct (NatSet.F.mem i t0) eqn:Hi.
    rewrite (@NatSetFacts.remove_neq_b t0 _ _ H).
    rewrite Hj. f_equal; try fnsetdec.
    rewrite Hj. f_equal; try fnsetdec.
  - destruct (NatSet.F.mem i t0) eqn:Hi.
    rewrite (@NatSetFacts.remove_neq_b t0 _ _ H).
    rewrite Hj. f_equal; try fnsetdec.
    rewrite Hj. auto.
Qed.

Lemma open_rec_ty_commute'' : forall T i j d' d'' f l, i <> j -> closed_qual 0 f l d' -> closed_qual 0 f l d'' -> open_rec_ty i d'' (open_rec_ty j d' T) = open_rec_ty j d' (open_rec_ty i d'' T).
  induction T; intros; simpl; eauto;
    try solve [erewrite IHT1; eauto; erewrite IHT2; eauto | erewrite IHT; eauto].
  erewrite open_qual_commute''; eauto.
  erewrite open_qual_commute'' with (i:=S (S i)); eauto.
  erewrite IHT1; eauto; erewrite IHT2; eauto.
Qed.

Lemma closed_tm_open'_id : forall {t f l}, closed_tm 0 f l t -> forall {A} {G : list A}, open_tm' G t = t.
  intros. unfold open_tm'. unfold open_tm. repeat erewrite closed_tm_open_id; eauto.
Qed.

Lemma closed_ty_open'_id : forall {T f l}, closed_ty 0 f l T -> forall {A} {G : list A}, open_ty' G T = T.
  intros. unfold open_ty'. unfold open_ty. repeat erewrite closed_ty_open_id; eauto.
Qed.

Lemma closed_qual_open'_id : forall {q f l}, closed_qual 0 f l q -> forall {A} {G : list A}, openq' G q = q.
  intros. unfold openq'. unfold openq. repeat erewrite closed_qual_open_id; eauto.
Qed.

Lemma open_tm'_bv0 : forall A (G : list A), open_tm' G #0 = $(length G).
  intros. compute. auto.
Qed.

Lemma open_tm'_bv1 : forall A (G : list A), open_tm' G #1 = $(S (length G)).
  intros. compute. auto.
Qed.

Lemma openq'_bv0 : forall A (G : list A) X Y, openq' G (qset X (NatSet.F.singleton 0) Y) = ((qset X {}N Y) ⊕ (length G)).
  intros. unfold qplus. compute. rewrite mem_singleton. compute. rewrite remove_singleton_empty.
  repeat rewrite empty_union_left. rewrite NatSetFacts.empty_b. auto.
Qed.

Lemma openq'_bv1 : forall A (G : list A) X Y, openq' G (qset X (NatSet.F.singleton 1) Y) = ((qset X {}N Y) ⊕ (S (length G))).
  intros. unfold qplus. compute. rewrite mem_singleton. compute. rewrite mem_singleton. compute.
  rewrite remove_singleton_empty. repeat rewrite empty_union_left. auto.
Qed.

Lemma open_qual_just_fv : forall i d x, open_qual i d (just_fv x) = (just_fv x).
  intros. compute. destruct d. rewrite NatSetFacts.empty_b. auto.
Qed.

Lemma open_qual_just_loc : forall i d x, open_qual i d (just_loc x) = (just_loc x).
  intros. compute. destruct d. rewrite NatSetFacts.empty_b. auto.
Qed.

Lemma open_rec_tm_bv : forall i t, open_rec_tm i t (#i) = t.
  intros. simpl. rewrite Nat.eqb_refl. auto.
Qed.

Lemma open_rec_tm_bv_skip : forall j i t, j <> i -> open_rec_tm j t (#i) = #i.
  intros. simpl. rewrite <- Nat.eqb_neq in H. rewrite H. auto.
Qed.

Lemma splice_id : forall {T b f l}, closed_tm b f l T -> (splice f T ) = T.
  induction T; intros; inversion H; subst; simpl; auto;
    try solve [erewrite IHT1; eauto; erewrite IHT2; eauto | erewrite IHT; eauto].
    destruct (le_lt_dec f x) eqn:Heq. lia. auto.
Qed.

Lemma splice_qual_id : forall {d b f l}, closed_qual b f l d -> (splice_qual f d) = d.
Proof.
  destruct d; intros; intuition.
  inversion H. subst. simpl.
  f_equal. unfold splice_set. unfold inc.
  unfold bound in H6.
  destruct (NatSet.F.max_elt t) eqn:Hmax.
  - assert (e < f) by lia. autounfold. erewrite filter_lt. erewrite filter_gt.
    rewrite NatSetProperties.fold_empty. fnsetdec. all: eauto.
  - apply max_elt_empty' in Hmax. rewrite Hmax.
    rewrite filter_empty. rewrite filter_empty.
    rewrite NatSetProperties.fold_empty. fnsetdec.
Qed.

Lemma splice_ty_id : forall {T b f l}, closed_ty b f l T -> (splice_ty f T) = T.
  induction T; intros; inversion H; subst; simpl; auto;
    try solve [erewrite IHT1; eauto; erewrite IHT2; eauto | erewrite IHT; eauto].
  repeat erewrite splice_qual_id; eauto.
  erewrite IHT1; eauto. erewrite IHT2; eauto.
  erewrite IHT; eauto. eapply closed_ty_monotone; eauto. lia.
Qed.

Lemma splice_open : forall {T j n m}, splice n (open_rec_tm j (varF (m + n)) T) = open_rec_tm j (varF (S (m + n))) (splice n T).
  induction T; intros; simpl; auto;
    try solve [erewrite IHT1; eauto; erewrite IHT2; eauto | erewrite IHT; eauto].
  destruct v; simpl. destruct (le_lt_dec n i) eqn:Heq; auto.
  destruct (PeanoNat.Nat.eqb j i) eqn:Heq; auto.
  simpl. destruct (le_lt_dec n (m + n)) eqn:Heq'. auto. lia.
Qed.

Lemma splice_qual_open : forall {d j n m},
    splice_qual n (open_qual j (just_fv (m + n)) d) =
    open_qual j (just_fv (S (m + n))) (splice_qual n d).
Proof.
  destruct d; simpl; intuition.
  destruct (NatSet.F.mem j t0) eqn:Hmem; simpl; f_equal.
  unfold splice_set. remember (m + n) as mn.
  remember (NatSet.F.singleton mn) as Smn.
  rewrite union_assoc.
  rewrite filter_union_dist.
  rewrite filter_union_dist. autounfold.
  replace (NatSet.F.filter (fun i : NatSet.F.elt => n <=? i) Smn) with Smn.
  replace (NatSet.F.filter (fun i : NatSet.F.elt => i <? n) Smn) with {}N.
  rewrite empty_union_right. rewrite inc_union_dist.
  rewrite HeqSmn. rewrite inc_singleton. fnsetdec.
  rewrite HeqSmn. symmetry.
  apply filter_singleton_2. rewrite Heqmn. apply Nat.ltb_ge. lia.
  rewrite HeqSmn. symmetry. apply filter_singleton_1. apply leb_correct. lia.
Qed.

Lemma splice_ty_open : forall {T j n m}, splice_ty n (open_rec_ty j (just_fv (m + n)) T) = open_rec_ty j (just_fv (S (m + n))) (splice_ty n T).
  induction T; intros; simpl; auto;
    try solve [erewrite IHT1; eauto; erewrite IHT2; eauto | erewrite IHT; eauto].
  rewrite splice_qual_open. rewrite splice_qual_open. rewrite IHT1. rewrite IHT2. auto.
Qed.

Lemma splice_open' : forall {T} {A} {D : A} {ρ ρ'}, splice (length ρ') (open_tm' (ρ ++ ρ') T) = open_tm' (ρ ++ D :: ρ') (splice (length ρ') T).
  intros. unfold open_tm'.
  replace (length (ρ ++ ρ')) with ((length ρ) + (length ρ')).
  replace (S (length (ρ ++ D :: ρ'))) with (S (S (length ρ) + (length ρ'))).
  replace (length (ρ ++ D :: ρ')) with (S ((length ρ) + (length ρ'))).
  repeat rewrite <- splice_open. auto.
  all: rewrite app_length; simpl; lia.
Qed.

Lemma splice_qual_open' : forall {d} {A} {D : A} {ρ ρ'}, splice_qual (length ρ') (openq' (ρ ++ ρ') d) = openq' (ρ ++ D :: ρ') (splice_qual (length ρ') d).
  intros. unfold openq'. unfold openq.
  replace (length (ρ ++ ρ')) with ((length ρ) + (length ρ')).
  replace (S (length (ρ ++ D :: ρ'))) with (S (S (length ρ) + (length ρ'))).
  replace (length (ρ ++ D :: ρ')) with (S ((length ρ) + (length ρ'))).
  repeat rewrite <- splice_qual_open. auto.
  all: rewrite app_length; simpl; lia.
Qed.

Lemma splice_ty_open' : forall {T} {A} {D : A} {ρ ρ'}, splice_ty (length ρ') (open_ty' (ρ ++ ρ') T) = open_ty' (ρ ++ D :: ρ') (splice_ty (length ρ') T).
  intros. unfold open_ty'. unfold open_ty.
  replace (length (ρ ++ ρ')) with ((length ρ) + (length ρ')).
  replace (S (length (ρ ++ D :: ρ'))) with (S (S (length ρ) + (length ρ'))).
  replace (length (ρ ++ D :: ρ')) with (S ((length ρ) + (length ρ'))).
  repeat rewrite <- splice_ty_open. auto.
  all: rewrite app_length; simpl; lia.
Qed.

Lemma splice_closed : forall {T b n m l}, closed_tm b (n + m) l T -> closed_tm b (S (n + m)) l (splice m T).
  induction T; simpl; intros; inversion H; subst; intuition.
  destruct (le_lt_dec m x) eqn:Heq; intuition.
Qed.

Lemma splice_qual_closed : forall {d b n m l},
    closed_qual b (n + m)     l d ->
    forall {i}, i <= m -> closed_qual b (S (n + m)) l (splice_qual i d).
Proof.
  destruct d; simpl; intuition.
  inversion H. subst. constructor; auto.
  clear H7 H8. inversion H. subst.
  unfold bound in H7. destruct (NatSet.F.max_elt t) eqn: Hmax.
  - bdestruct (e <? i).
    + specialize (@splice_set_preserves_bound _ _ _ Hmax H1) as Hs.
      unfold bound in Hs. rewrite Hmax in Hs. unfold bound. rewrite <- Hs. lia.
    + specialize (@splice_set_inc_bound _ _ _ Hmax H1) as Hs.
      unfold bound in Hs. rewrite Hmax in Hs. unfold bound. rewrite <- Hs. lia.
  - unfold splice_set.
    apply max_elt_empty' in Hmax. rewrite Hmax.
    rewrite filter_empty. rewrite filter_empty.
    unfold inc. rewrite NatSetProperties.fold_empty.
    rewrite empty_union_right. unfold bound. rewrite max_elt_empty. lia.
Qed.

Lemma splice_ty_closed : forall {T b n m l}, closed_ty b (n + m) l T -> forall {i}, i <= m -> closed_ty b (S (n + m)) l (splice_ty i T).
  induction T; simpl; intros; inversion H; subst; intuition.
  constructor. 1,2 : apply splice_qual_closed; auto. all: intuition.
  constructor. erewrite splice_ty_id; eauto. eapply closed_ty_monotone; eauto. lia.
Qed.

Lemma splice_closed' : forall {T b l} {A} {D : A} {ρ ρ'},
    closed_tm b (length (ρ ++ ρ')) l T ->  closed_tm b (length (ρ ++ D :: ρ')) l (splice (length ρ') T).
  intros. rewrite app_length in H.
  replace (length (ρ ++ D :: ρ')) with (S (length ρ) + (length ρ')).
  apply splice_closed. auto. simpl. rewrite app_length. simpl. lia.
Qed.

Lemma splice_qual_closed' : forall {d b l} {A} {D : A} {ρ ρ'},
    closed_qual b (length (ρ ++ ρ')) l d -> closed_qual b (length (ρ ++ D :: ρ')) l (splice_qual (length ρ') d).
  intros. rewrite app_length in H.
  replace (length (ρ ++ D :: ρ')) with (S (length ρ) + (length ρ')).
  eapply splice_qual_closed; eauto. simpl. rewrite app_length. simpl. lia.
Qed.

Lemma splice_ty_closed' : forall {T b l} {A} {D : A} {ρ ρ'},
    closed_ty b (length (ρ ++ ρ')) l T -> closed_ty b (length (ρ ++ D :: ρ')) l (splice_ty (length ρ') T).
  intros. rewrite app_length in H.
  replace (length (ρ ++ D :: ρ')) with (S (length ρ) + (length ρ')).
  eapply splice_ty_closed; eauto. simpl. rewrite app_length. simpl. lia.
Qed.

Lemma splice_qual_closed'' : forall {q x b l k}, closed_qual b x l q -> k <= x -> closed_qual b (S x) l (splice_qual k q).
  destruct q; simpl; intuition.
  inversion H; subst. constructor; auto.
  unfold bound in H7.
  destruct (NatSet.F.max_elt t) eqn:Hmax.
  - assert (e < x) by lia. bdestruct (e =? k).
    + subst. erewrite <- splice_set_inc_bound; eauto.
      unfold bound. rewrite Hmax. lia.
    + bdestruct (e <? k).
      * unfold splice_set. autounfold. erewrite filter_gt; eauto. erewrite filter_lt; eauto.
        rewrite inc_empty. erewrite empty_union_left. unfold bound.
        rewrite Hmax. lia.
      * assert (e > k) by lia.
        erewrite <- splice_set_inc_bound. unfold bound. rewrite Hmax. lia.
        apply Hmax. lia.
  - apply max_elt_empty' in Hmax. subst.
    rewrite splice_set_empty. rewrite bound_empty. lia.
Qed.

Lemma splice_ty_closed'' : forall {T x b l k}, closed_ty b x l T -> k <= x -> closed_ty b (S x) l (splice_ty k T).
  induction T; simpl; intros; inversion H; subst; constructor; intuition.
  1,2 : eapply splice_qual_closed''; eauto. erewrite splice_ty_id; eauto.
  eapply closed_ty_monotone; eauto. lia.
Qed.

Lemma splice_open_succ : forall {T b n l j}, closed_tm b n l T -> splice n (open_rec_tm j (varF n) T) = open_rec_tm j (varF (S n)) T.
  induction T; simpl; intros; inversion H; subst; auto;
    try solve [erewrite IHT1; eauto; erewrite IHT2; eauto | erewrite IHT; eauto].
  destruct (PeanoNat.Nat.eqb j x) eqn:Heq; auto. simpl.
  destruct (le_lt_dec n n) eqn:Heq'; auto. lia.
  simpl. destruct (le_lt_dec n x) eqn:Heq; auto. lia.
Qed.

Lemma splice_qual_open_succ : forall {d b n l j},
    closed_qual b n l d ->
    splice_qual n (open_qual j (just_fv n) d) = open_qual j (just_fv (S n)) d.
Proof.
  destruct d; simpl; intuition. inversion H. subst.
  destruct (NatSet.F.mem j t0) eqn:Hmem; simpl; f_equal.
  - unfold splice_set. unfold bound in H6.
    destruct (NatSet.F.max_elt t) eqn:Hmax.
    + assert (e < n) by lia.
      rewrite filter_union_dist. rewrite filter_union_dist.
      rewrite filter_singleton_1.
      2: { apply leb_correct. lia. }
      rewrite filter_singleton_2.
      2: { apply Nat.ltb_ge. lia. }
      rewrite empty_union_right. autounfold.
      rewrite (@filter_lt _ _ _ H0 Hmax). rewrite (@filter_gt _ _ _ H0 Hmax).
      rewrite empty_union_left. rewrite inc_singleton. fnsetdec.
    + apply max_elt_empty' in Hmax. rewrite Hmax.
      rewrite empty_union_left. rewrite empty_union_left.
      rewrite filter_singleton_1.
      2: { apply leb_correct. lia. }
      rewrite filter_singleton_2.
      2: { apply Nat.ltb_ge. lia. }
      rewrite empty_union_right. rewrite inc_singleton. auto.
  - unfold splice_set. unfold bound in H6.
    destruct (NatSet.F.max_elt t) eqn:Hmax.
    + assert (e < n) by lia. autounfold.
      rewrite (@filter_lt _ _ _ H0 Hmax).
      rewrite (@filter_gt _ _ _ H0 Hmax).
      rewrite inc_empty. fnsetdec.
    + apply max_elt_empty' in Hmax. rewrite Hmax.
      rewrite filter_empty. rewrite inc_empty.
      rewrite filter_empty. fnsetdec.
Qed.

Lemma splice_ty_open_succ : forall {T b n l j}, closed_ty b n l T -> splice_ty n (open_rec_ty j (just_fv n) T) = open_rec_ty j (just_fv (S n)) T.
  induction T; simpl; intros; inversion H; subst; auto;
    try solve [erewrite IHT1; eauto; erewrite IHT2; eauto | erewrite IHT; eauto].
  erewrite splice_qual_open_succ; eauto. erewrite splice_qual_open_succ; eauto.
  erewrite IHT1; eauto. erewrite IHT2; eauto.
  erewrite closed_ty_open_id; eauto. erewrite closed_ty_open_id; eauto.
  erewrite splice_ty_id; eauto. eapply closed_ty_monotone; eauto. all : lia.
Qed.

Lemma splice_qual_open'' : forall {k df d1 d2},
    splice_qual k (openq df d1 d2) =
    openq (splice_qual k df) (splice_qual k d1) (splice_qual k d2).
Proof.
  intros. destruct d2; destruct d1; destruct df; simpl.
  unfold splice_qual. unfold openq. unfold open_qual.
  destruct (NatSet.F.mem 0 t0) eqn: H1.
  - destruct (NatSet.F.mem 1 (NatSet.F.union (NatSet.F.remove 0 t0) t6)) eqn: H2.
    + f_equal. rewrite splice_set_union_dist. rewrite splice_set_union_dist. auto.
    + f_equal. rewrite splice_set_union_dist. auto.
  - destruct (NatSet.F.mem 1 t0) eqn:H2.
    + f_equal. rewrite splice_set_union_dist. auto.
    + qdec.
Qed.

Lemma splice_qual_qplus_dist : forall {i k d},
    k <= i -> (splice_qual k d ⊕ S i) = splice_qual k (d ⊕ i).
Proof.
  intros. destruct d; simpl; intuition.
  f_equal. rewrite splice_set_union_dist. f_equal.
  unfold splice_set.
  rewrite filter_singleton_1.
  rewrite filter_singleton_2.
  rewrite empty_union_right. rewrite inc_singleton. auto.
  apply Nat.ltb_ge. lia. rewrite leb_correct; auto.
Qed.

Lemma splice_qual_qplus_id : forall {i k l d},
    closed_qual 0 i l d -> i < k -> splice_qual k (d ⊕ i) = (d ⊕ i).
Proof.
  intros. inversion H; subst. simpl. auto.
  simpl. repeat rewrite listlub_empty_right.
  f_equal. rewrite splice_set_union_dist.
  f_equal. unfold splice_set.
  unfold bound in H1. destruct (NatSet.F.max_elt vs) eqn:Hmax.
  - assert (e < k) by lia. autounfold. erewrite filter_lt. 2: apply H4. 2: apply Hmax.
    erewrite filter_gt. 2: apply H4. 2: apply Hmax.
    rewrite inc_empty. fnsetdec.
  - apply max_elt_empty' in Hmax. rewrite Hmax.
    (* fnsetdec even does not work for empty sets :-( *)
    rewrite filter_empty. rewrite inc_empty.
    rewrite filter_empty. fnsetdec.
  - apply splice_set_singleton_inv; auto.
Qed.

Lemma subqual_splice_lr' : forall {i du df},
    splice_qual i du ⊑ splice_qual i df <-> du ⊑ df.
Proof.
  intros. intuition.
  - destruct du. destruct df.
    unfold splice_qual in *. inversion H.
    intuition. constructor; auto.
    eapply splice_set_subset_dist. eauto.
  - destruct du. destruct df.
    inversion H. intuition.
    constructor; auto.
    eapply splice_set_subset_dist. auto.
Qed.

Lemma subqualb_splice_lr' : forall {i du df}, (splice_qual i du ⊑? splice_qual i df) = (du ⊑? df).
  intros. specialize (@subqual_splice_lr' i du df) as SQS.
  destruct (du ⊑? df) eqn:Heq.
  rewrite subqualb_true_iff in Heq. rewrite subqualb_true_iff. intuition.
  rewrite subqualb_false_iff in Heq. rewrite subqualb_false_iff. intuition.
Qed.

Lemma subqual_splice_lr : forall {i du k df},
    k >= i -> splice_qual i du ⊕ S k ⊑ splice_qual i df <-> du ⊕ k ⊑ df.
  intros. rewrite splice_qual_qplus_dist. apply subqual_splice_lr'. auto.
Qed.

Lemma subqualb_splice_lr : forall {i du k df}, k >= i -> (splice_qual i du ⊕ S k ⊑? splice_qual i df) = (du ⊕ k ⊑? df).
  intros. specialize (@subqual_splice_lr i du k df H) as SQS.
  destruct (du ⊕ k ⊑? df) eqn:Heq.
  rewrite subqualb_true_iff in Heq. rewrite subqualb_true_iff. intuition.
  rewrite subqualb_false_iff in Heq. rewrite subqualb_false_iff. intuition.
Qed.

Lemma subqual_splice_r : forall {d1 d2 i f l},
    i >= f -> closed_qual 0 f l d1 -> d1 ⊑ d2 <-> d1 ⊑ splice_qual i d2.
Proof.
  intros. split; intros.
  - unfold splice_qual. inversion H0. subst. destruct d2.
    unfold subqual in *. intros; intuition.
    eapply splice_set_preserves_superset_1; eauto.
  - unfold subqual in *. destruct d1. destruct d2.
    unfold splice_qual in *. intuition; try fnsetdec.
    inversion H0. subst.
    eapply splice_set_preserves_superset_2. apply H. apply H10. apply H2.
Qed.

Lemma subqualb_splice_r :  forall {d1 d2 i f l}, i >= f -> closed_qual 0 f l d1 -> (d1 ⊑? d2) = (d1 ⊑? splice_qual i d2).
  intros. specialize (@subqual_splice_r d1 d2 i f l H H0) as SQS.
  destruct (d1 ⊑? splice_qual i d2) eqn:Heq.
  rewrite subqualb_true_iff in Heq. rewrite subqualb_true_iff. intuition.
  rewrite subqualb_false_iff in Heq. rewrite subqualb_false_iff. intuition.
Qed.

Lemma qplus_closed_qual : forall {d b f l x},
    closed_qual b f l d ->
    forall {f'}, f' >= f -> f' > x -> closed_qual b f' l (d ⊕ x).
Proof.
  intros. inversion H; subst; simpl; intuition.
  constructor. specialize (@bound_singleton x) as Hs.
  specialize (@union_bound_max vs (NatSet.F.singleton x)) as Hu. lia.
  all: rewrite empty_union_right; auto.
Qed.

Lemma stp_closed : forall {Γ Σ T1 d1 T2 d2},
    stp Γ Σ T1 d1 T2 d2 ->
    closed_ty 0 (length Γ) (length Σ) T1
    /\ closed_qual 0 (length Γ) (length Σ) d1
    /\ closed_ty 0 (length Γ) (length Σ) T2
    /\ closed_qual 0 (length Γ) (length Σ) d2.
Proof.  intros Γ Σ T1 d1 T2 d2 HS. induction HS.
  - intuition. all: apply qstp_closed in H; intuition.
  - intuition. all: apply qstp_closed in H; intuition.
  - intuition. apply qstp_closed in H1; intuition. apply qstp_closed in H1; intuition.
  - intuition.
Qed.

Lemma stp_refl' : forall {n T}, ty_size T < n -> forall {Γ Σ}, closed_ty 0 (length Γ) (length Σ) T -> forall {d d'}, qstp Γ Σ d d' -> stp Γ Σ T d T d'.
  induction n; try lia; destruct T; simpl; intros Hsize Γ Σ Hc d d' Hstp; inversion Hc; subst.
  - (*TUnit*) constructor. auto.
  - (*TFun*) constructor; auto. apply IHn. lia. auto. apply qstp_refl. apply eqqual_refl. auto.
    apply IHn. unfold open_ty'. unfold open_ty. rewrite <- open_ty_preserves_size. rewrite <- open_ty_preserves_size. simpl. lia. simpl. unfold open_ty'. unfold open_ty. rewrite open_rec_ty_commute; auto.
    eapply closed_ty_open' with (x:=S (S (length Γ))); eauto.
    eapply closed_ty_open' with (x:=S (S (length Γ))); eauto.
    eapply closed_ty_monotone; eauto.
    rewrite <- just_fv_closed. lia.
    rewrite <- just_fv_closed. lia.
    apply qstp_refl. apply eqqual_refl. unfold openq'. unfold openq. rewrite open_qual_commute; auto.
    simpl. eapply closed_qual_open. eapply closed_qual_open. eapply closed_qual_monotone; eauto.
    lia. lia.
  - (*TRef*) constructor. auto.
    all : apply IHn; try lia; auto. all: apply qstp_refl; try apply eqqual_refl; constructor.
    all : simpl; rewrite bound_empty; lia.
Qed.

Lemma stp_refl : forall {T Γ Σ}, closed_ty 0 (length Γ) (length Σ) T -> forall {d d'}, qstp Γ Σ d d' -> stp Γ Σ T d T d'.
  intros. eapply stp_refl'; eauto.
Qed.

Lemma stp_qstp_inv : forall {Γ Σ T1 d1 T2 d2}, stp Γ Σ T1 d1 T2 d2 -> qstp Γ Σ d1 d2.
  intros Γ Σ T1 d1 T2 d2 HS. induction HS; intuition.  eapply qstp_trans; eauto.
Qed.

Lemma weaken_qstp_gen : forall {Γ1 Γ2 Σ d1 d2},
    qstp (Γ1 ++ Γ2) Σ d1 d2 ->
    forall T', qstp ((splice_tenv (length Γ2) Γ1) ++ T' :: Γ2) Σ (splice_qual (length Γ2) d1) (splice_qual (length Γ2) d2).
Proof.
  intros Γ1 Γ2 Σ d1 d2 HSTP T'. inversion HSTP. subst.
  constructor. inversion H0; subst. destruct d1.
  unfold splice_qual. unfold subqual in *. intros.
  - destruct H. destruct H4. intuition. clear H4 H5 H2 H3.
    rewrite app_length in H1.
    remember (length Γ1) as l1. remember (length Γ2) as l2.
    eapply splice_set_preserves_subset. apply H. apply H1.
  - apply splice_qual_closed'. rewrite app_length in *. rewrite splice_tenv_length. auto.
Qed.

Lemma weaken_qstp_store : forall {Γ Σ d1 d2}, qstp Γ Σ d1 d2 -> forall {Σ'}, qstp Γ (Σ' ++ Σ) d1 d2.
  intros. destruct H. constructor. auto. rewrite app_length. eapply closed_qual_monotone; eauto. lia.
Qed.

Lemma weaken_qstp_store_ext : forall {Γ Σ d1 d2}, qstp Γ Σ d1 d2 -> forall {Σ'}, Σ' ⊇ Σ -> qstp Γ Σ' d1 d2.
  intros. unfold extends in H0. destruct H0. subst. apply weaken_qstp_store. auto.
Qed.

Lemma weaken_stp_gen : forall {Γ1 Γ2 Σ T1 d1 T2 d2},  stp (Γ1 ++ Γ2) Σ T1 d1 T2 d2 ->
    forall T', stp ((splice_tenv (length Γ2) Γ1) ++ T' :: Γ2) Σ (splice_ty (length Γ2) T1) (splice_qual (length Γ2) d1) (splice_ty (length Γ2) T2) (splice_qual (length Γ2) d2).
Proof. intros Γ1 Γ2 Σ T1 d1 T2 d2  Hstp T'. remember (Γ1 ++ Γ2)  as Γ. generalize dependent Γ1.  induction Hstp. intros Γ1.
  - constructor. eapply weaken_qstp_gen. subst. auto.
  - intros. assert (stp Γ Σ (TRef T1) d1 (TRef T2) d2). { constructor; intuition. } subst.
    apply stp_closed in H0 as Hcl. intuition.
    inversion H1. inversion H2. subst.
    constructor. apply weaken_qstp_gen. subst; auto. 1,2: fold splice_ty. apply stp_closed in H0 as Hcl. intuition.
    replace (splice_ty (length Γ2) T1) with T1. replace (splice_ty (length Γ2) T2) with T2.  intuition.
    1,2 : erewrite splice_ty_id; eauto; eapply closed_ty_monotone; eauto; intuition.
    replace (splice_ty (length Γ2) T2) with T2. replace (splice_ty (length Γ2) T1) with T1.  intuition.
    1,2 : erewrite splice_ty_id; eauto; eapply closed_ty_monotone; eauto; lia.
  - assert (stp Γ Σ (TFun d1 d2 T1 T2) d5 (TFun d3 d4 T3 T4) d6). { constructor; intuition. } intros.
    subst. intuition. inversion H0; inversion H; subst. apply qstp_closed in H1 as Hcl. intuition.
    constructor; try fold splice_ty. 1-3: constructor.
    1,2,5,6,10 : apply splice_qual_closed'. 6-9 : apply splice_ty_closed'.
    1-9: rewrite app_length in *; rewrite splice_tenv_length in *; auto.
    inversion H1. subst. rewrite subqual_splice_lr'; intuition.
    specialize (IHHstp1 Γ1). intuition.
    specialize (IHHstp2 ((T3, d3) :: (TFun d1 d2 T1 T2, d5) :: Γ1)). intuition.
    rewrite <- splice_ty_open'. rewrite <- splice_ty_open'. rewrite <- splice_qual_open'. rewrite <- splice_qual_open'.
    unfold open_ty' in *. unfold open_ty in *. unfold openq' in *. unfold openq in *.
    rewrite app_length in *. rewrite splice_tenv_length. simpl. auto.
  - intros. specialize (IHHstp1 Γ1). specialize (IHHstp2 Γ1). intuition.
    eapply s_trans; eauto.
Qed.

Lemma weaken_stp : forall {Γ Σ T1 d1 T2 d2}, stp Γ Σ T1 d1 T2 d2 -> forall T', stp (T' :: Γ) Σ T1 d1 T2 d2.
Proof.
  intros Γ Σ T1 d1 T2 d2 HST. specialize (@weaken_stp_gen [] Γ Σ T1 d1 T2 d2) as Hsp. simpl in *.  specialize (Hsp HST).
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
  - constructor. apply weaken_qstp_store. auto.
  - constructor; auto. apply weaken_qstp_store. auto.
  - constructor; auto. 1,2 : rewrite app_length; eapply closed_ty_monotone; eauto; lia.
    apply weaken_qstp_store. auto.
  - specialize (IHHSTP1 Σ'). specialize (IHHSTP2 Σ'). eapply s_trans in IHHSTP2; eauto.
Qed.

Lemma weaken_stp_store_ext : forall {Σ Γ T1 d1 T2 d2}, stp Γ Σ T1 d1 T2 d2 -> forall {Σ'}, Σ' ⊇ Σ ->  stp Γ Σ' T1 d1 T2 d2.
  intros. unfold extends in H0. destruct H0. subst. apply weaken_stp_store. auto.
Qed.

Lemma narrowing_qstp_gen : forall{Γ1 U du Γ2 Σ d1 d2},
    qstp (Γ1 ++ (U,du) :: Γ2) Σ d1 d2 ->
    forall {V dv}, stp Γ2 Σ V dv U du ->
              qstp (Γ1 ++ (V,dv) :: Γ2) Σ d1 d2.
  intros Γ1 U du Γ2 Σ d1 d2 HQ V dv HSTP.
  inversion HQ. subst. constructor.
  auto. rewrite app_length in *. simpl in *. auto.
Qed.

Lemma narrowing_stp_gen : forall{Γ1 U du Γ2 Σ T1 d1 T2 d2}, stp (Γ1 ++ (U,du) :: Γ2) Σ T1 d1 T2 d2 -> forall {V dv}, (stp Γ2 Σ V dv U du) -> stp (Γ1 ++ (V,dv) :: Γ2) Σ T1 d1 T2 d2.
Proof. intros Γ1 U du Γ2 Σ T1 d1 T2 d2 HST. remember (Γ1 ++ (U,du) :: Γ2) as Γ.
  generalize dependent Γ1; induction HST; intros; intuition.
  - subst. constructor. eapply narrowing_qstp_gen; eauto.
  - subst. constructor. eapply narrowing_qstp_gen; eauto. auto. auto.
  - rewrite HeqΓ in *. constructor.
    subst. rewrite app_length in *. simpl in *. auto.
    subst. rewrite app_length in *. simpl in *. auto.
    eapply narrowing_qstp_gen; subst; eauto. eapply IHHST1; eauto.
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

Lemma closed_qual_qlub: forall {b f l d1 d2}, closed_qual b f l d1 -> closed_qual b f l d2 -> closed_qual b f l (d1 ⊔ d2).
  intros. inversion H; subst; inversion H0; subst; intuition.
  simpl. constructor.
  specialize (@union_bound_max vs vs0). lia.
  specialize (@union_bound_max bs bs0). lia.
  specialize (@union_bound_max ls ls0). lia.
Qed.

Lemma closed_qual_qqplus: forall {b f l d1 d2}, closed_qual b f l d1 -> closed_qual b f l d2 -> closed_qual b f l (d1 ⋓ d2).
  intros. destruct d1.
  apply closed_qual_qlub; auto.
Qed.

Lemma closed_qual_qqcap : forall {q1 q2 b f l},
    closed_qual b f l q1 -> closed_qual b f l q2 -> closed_qual b f l (q1 ⋒ q2).
  intros. inversion H; subst; inversion H0; subst; simpl; intuition.
  constructor.
  specialize (@inter_bound_min vs vs0) as Hb. lia.
  specialize (@inter_bound_min bs bs0) as Hb. lia.
  specialize (@inter_bound_min ls ls0) as Hb. lia.
Qed.

Lemma qstp_qual_irrelevance : forall {Γ1 Γ2 Σ U du d1 d2}, qstp (Γ2 ++ (U,du) :: Γ1) Σ d1 d2 -> forall {du'}, qstp (Γ2 ++ (U,du') :: Γ1) Σ d1 d2.
  intros. inversion H. subst. constructor. auto.
  rewrite app_length in *. simpl in *. auto.
Qed.

Lemma stp_qual_irrelevance : forall {Γ1 Γ2 Σ U du T1 d1 T2 d2}, stp (Γ2 ++ (U,du) :: Γ1) Σ T1 d1 T2 d2 -> forall {du'}, stp (Γ2 ++ (U,du') :: Γ1) Σ T1 d1 T2 d2.
  intros. remember (Γ2 ++ (U, du) :: Γ1) as Γ. generalize dependent du'. generalize dependent Γ2.
  generalize dependent U. generalize dependent du. generalize dependent Γ1.
  induction H; intros; subst.
  - constructor. eapply qstp_qual_irrelevance; eauto.
  - constructor; auto. eapply qstp_qual_irrelevance; eauto.
  - constructor; auto. 1,2 : rewrite app_length in *; simpl in *; auto.
    eapply qstp_qual_irrelevance; eauto. eapply IHstp1; eauto.
    specialize (IHstp2 Γ1 du U ((T3, d3) :: (TFun d1 d2 T1 T2, d5) :: Γ2)).
    intuition.
    unfold open_ty' in *. unfold open_ty in *.
    unfold openq' in *. unfold openq in *. rewrite app_length in *. simpl in *. auto.
  - eapply s_trans; eauto.
Qed.

Lemma stp_qual_irrelevance' : forall {Γ1 X Σ U du T1 d1 T2 d2}, stp (X :: (U,du) :: Γ1) Σ T1 d1 T2 d2 -> forall {du'}, stp (X :: (U,du') :: Γ1) Σ T1 d1 T2 d2.
  intros. replace (X :: (U, du) :: Γ1) with ([X] ++ (U, du) :: Γ1) in H; auto.
  replace (X :: (U, du') :: Γ1) with ([X] ++ (U, du') :: Γ1) ; auto.
  eapply stp_qual_irrelevance. eauto.
Qed.

Lemma stp_scale_plus : forall {Γ Σ T1 d1 T2 d2}, stp Γ Σ T1 d1 T2 d2 -> forall {x}, x < length Γ -> stp Γ Σ T1 (d1 ⊕ x) T2 (d2 ⊕ x).
  intros Γ Σ T1 d1 T2 d2 HSTP. induction HSTP; intros.
  - constructor. inversion H. subst. constructor. apply subqual_plus. auto.
    destruct (length Γ) eqn:Heq. lia. eapply qplus_closed_qual; eauto.
  - constructor; auto. constructor. apply subqual_plus. auto. inversion H. subst. auto.
    inversion H. subst. destruct (length Γ) eqn:Heq. lia. eapply qplus_closed_qual; eauto.
  - constructor; auto. inversion H1. subst. constructor. apply subqual_plus. auto.
    destruct (length Γ) eqn:Heq. lia. eapply qplus_closed_qual; eauto.
    eapply stp_qual_irrelevance'; eauto.
  - econstructor; eauto.
Qed.

Lemma stp_scale_qqplus : forall {Γ Σ T1 d1 T2 d2}, stp Γ Σ T1 d1 T2 d2 -> forall {d}, closed_qual 0 (length Γ) (length Σ) d -> stp Γ Σ T1 (d1 ⋓ d) T2 (d2 ⋓ d).
  intros Γ Σ T1 d1 T2 d2 HSTP. induction HSTP; intros.
  - constructor. inversion H. subst. constructor.
    apply subqual_qqplus. auto. apply closed_qual_qqplus; auto.
  - constructor; auto. constructor. apply subqual_qqplus. inversion H. subst. auto.
    inversion H. subst. apply closed_qual_qqplus; auto.
  - constructor; auto. inversion H1. subst. constructor. apply subqual_qqplus. auto.
    apply closed_qual_qqplus; auto. eapply stp_qual_irrelevance'; eauto.
  - econstructor; auto.
Qed.

Lemma stp_scale_qglb : forall {Γ Σ T1 d1 T2 d2}, stp Γ Σ T1 d1 T2 d2 -> forall {d}, closed_qual 0 (length Γ) (length Σ) d -> stp Γ Σ T1 (d1 ⊓ d) T2 (d2 ⊓ d).
  intros Γ Σ T1 d1 T2 d2 HSTP. induction HSTP; intros.
  - constructor. inversion H. subst. constructor. apply subqual_qglb_r. auto. apply closed_qual_qqcap; auto.
  - constructor; auto. constructor. apply subqual_qglb_r. inversion H. subst. auto. apply closed_qual_qqcap; auto.
    apply qstp_closed in H. intuition.
  - constructor; auto. inversion H1. subst. constructor. apply subqual_qglb_r. auto.
    apply closed_qual_qqcap; auto. eapply stp_qual_irrelevance'; eauto.
  - econstructor; auto.
Qed.

Lemma stp_shrink_var : forall {Γ Σ T1 d1 T2 d2}, stp Γ Σ T1 d1 T2 d2 -> forall {x}, x < length Γ -> stp Γ Σ T1 (just_fv x) T2 (just_fv x).
    intros. assert (Hstp: stp Γ Σ T1 ∅ T2 ∅). {
      replace (∅) with (d1 ⊓ ∅) at 1; auto.
      replace (∅) with (d2 ⊓ ∅) at 2; auto. apply stp_scale_qglb; auto.
    }
    replace (just_fv x) with (∅ ⊔ (just_fv x)); auto.
    apply stp_scale_qqplus; auto. apply just_fv_closed. auto.
Qed.

Lemma saturated_empty : forall {Γ Σ}, saturated Γ Σ ∅.
  intros. unfold saturated. intros.
  simpl in H. apply NatSetNotin.notin_empty in H. contradiction.
Qed.
#[global] Hint Resolve saturated_empty : core.

Lemma saturated_empty_tenv : forall {q Σ}, closed_qual 0 0 (length Σ) q -> saturated [] Σ q.
  intros. unfold saturated. intros.
  inversion H. subst. simpl in H0. apply bound_0_empty in H1. subst.
  apply NatSetNotin.notin_empty in H0. contradiction.
Qed.
#[global] Hint Resolve saturated_empty_tenv : core.

Lemma saturated_cons : forall {Γ Σ q}, saturated Γ Σ q -> forall {T q'}, saturated ((T, q') :: Γ) Σ q.
  intros. unfold saturated in *. intros. apply H in H0. inversion H0. subst.
  econstructor; eauto. rewrite indexr_skip; eauto. apply indexr_var_some' in H1. lia.
Qed.

Lemma saturated_app : forall {Γ' Γ Σ q}, saturated Γ Σ q -> saturated (Γ' ++ Γ) Σ q.
  induction Γ'; intros; simpl; intuition.
  apply saturated_cons; auto.
Qed.

Lemma qmem_plus_decomp : forall {x0 q x l}, $ (x0) ∈ᵥ q ⊕ x -> closed_qual 0 x l q -> $ (x0) ∈ᵥ q \/ x0 = x.
  intros. inversion H0. subst. simpl in *. apply NatSet.F.union_1 in H. intuition.
  right. rewrite NatSetFacts.singleton_iff in H4. auto.
Qed.

Lemma saturated_qplus : forall {Γ Σ x T q}, indexr x Γ = Some (T, q) -> closed_qual 0 x (length Σ) q -> saturated Γ Σ q -> saturated Γ Σ (q ⊕ x).
  unfold saturated. intros. specialize (qmem_plus_decomp H2 H0) as Hx. destruct Hx.
  - apply H1 in H3. inversion H3. subst. econstructor; eauto. eapply subqual_trans; eauto.
  - subst. econstructor; eauto.
Qed.

Lemma saturated_open_qual : forall {Γ Σ d1 d2}, saturated Γ Σ d1 -> forall {k}, saturated Γ Σ ([[ k ~> ∅ ]]ᵈ d2) -> saturated Γ Σ ([[ k ~> d1 ]]ᵈ d2).
  intros. destruct d1. destruct d2. simpl in *.
  destruct (NatSet.F.mem k t3) eqn:Hmem; intuition.
  repeat rewrite empty_union_right in H0.
  unfold saturated in *. intros. specialize (H x). specialize (H0 x).
  assert (Hx : $ (x) ∈ᵥ qset t t0 t1 \/ $ (x) ∈ᵥ qset t2 (NatSet.F.remove k t3) t4). {
    simpl. simpl in H1. fnsetdec.
  }
  intuition.
  - inversion H3. subst. econstructor; eauto. eapply subqual_trans; eauto. simpl. intuition.
  - inversion H3. subst. econstructor; eauto. eapply subqual_trans; eauto. simpl. intuition.
Qed.

Lemma saturated_openq : forall {Γ Σ df d1 d2},
    saturated Γ Σ df -> closed_qual 0 (length Γ) (length Σ) df ->
    saturated Γ Σ d1 -> closed_qual 0 (length Γ) (length Σ) d1 -> saturated Γ Σ (openq ∅ ∅ d2) -> saturated Γ Σ (openq df d1 d2).
  intros. unfold openq in *. apply saturated_open_qual; auto.
  erewrite open_qual_commute''; eauto. erewrite open_qual_commute'' in H3; eauto.
  eapply saturated_open_qual; auto. Unshelve. all: apply 0.
Qed.

Lemma saturated_qqplus : forall {Γ Σ q1 q2}, saturated Γ Σ q1 -> saturated Γ Σ q2 -> saturated Γ Σ (q1 ⋓ q2).
  intros. destruct q1. destruct q2. simpl in *. unfold saturated. intros.
  assert (Hx : $ (x) ∈ᵥ qset t t0 t1 \/ $ (x) ∈ᵥ qset t2 t3 t4). {
    simpl. simpl in H1. fnsetdec.
  }
  intuition. apply H in H2. 2 : apply H0 in H2.
  all : inversion H2; subst; econstructor; eauto; eapply subqual_trans; eauto; simpl; intuition.
Qed.

Lemma saturated_just_loc : forall {Γ Σ l}, saturated Γ Σ (just_loc l).
  intros. unfold saturated. intros. simpl in *.
  apply NatSetNotin.notin_empty in H. contradiction.
Qed.
#[global] Hint Resolve saturated_just_loc : core.

Lemma saturated_qqcap : forall {Γ Σ q1 q2}, saturated Γ Σ q1 -> saturated Γ Σ q2 -> saturated Γ Σ (q1 ⋒ q2).
  intros. destruct q1. destruct q2. simpl in *. unfold saturated. intros.
  assert (Hx : $ (x) ∈ᵥ qset t t0 t1 /\ $ (x) ∈ᵥ qset t2 t3 t4). {
    simpl. simpl in H1. fnsetdec.
  }
  intuition. apply H in H2. apply H0 in H3. inversion H2. subst. inversion H3. subst.
  econstructor; eauto. rewrite H4 in H7. inversion H7. subst. destruct q'0. simpl in *; intuition.
Qed.

Lemma weaken_store_saturated : forall {Γ Σ q}, saturated Γ Σ q -> forall {Σ'}, Σ' ⊇ Σ -> saturated Γ Σ' q.
  intros. unfold saturated in *. intros. specialize (H x H1).
  inversion H. subst. apply (sat_var U q'); auto. eapply closed_qual_monotone; eauto.
  apply extends_length; auto.
Qed.

Fixpoint has_type_closed  {Γ φ Σ t T d} (ht : has_type Γ φ Σ t T d) :
  closed_qual 0 (length Γ) (length Σ) φ /\
  closed_tm 0 (length Γ) (length Σ) t /\
  closed_ty 0 (length Γ) (length Σ) T /\
  closed_qual 0 (length Γ) (length Σ) d.
Proof.
  destruct ht; intuition; try apply has_type_closed in ht; try apply has_type_closed in ht1;
    try apply has_type_closed in ht2; intuition.
  - constructor. apply indexr_var_some' in H. auto.
  - apply indexr_var_some' in H.
    eapply closed_ty_monotone; eauto. lia.
  - apply just_fv_closed. apply indexr_var_some' in H. auto.
  - eapply closed_qual_sub; eauto.
  - inversion H6. subst. unfold openq.
    erewrite open_qual_commute''; eauto.
    eapply closed_qual_open'; eauto. eapply closed_qual_open'; eauto.
  - constructor. apply indexr_var_some' in H0. auto.
  - apply just_loc_closed. apply indexr_var_some' in H0. auto.
  - inversion H0. subst. inversion H0. subst. eapply closed_ty_monotone; eauto; lia.
  - apply stp_closed in H. intuition.
  - apply stp_closed in H. intuition.
Qed.

Lemma open_qual_subqual : forall {d1 d2 φ}, d1 ⊑ φ -> forall {k}, ([[ k ~> ∅ ]]ᵈ d2) ⊑ φ -> ([[ k ~> d1 ]]ᵈ d2) ⊑ φ.
  intros. destruct d1. destruct d2. destruct φ. simpl in *. intuition.
  destruct (NatSet.F.mem k t3) eqn:Hmem; simpl in *; intuition; fnsetdec.
Qed.

Lemma openq_subqual : forall {df d1 d2 φ f l}, closed_qual 0 f l φ -> df ⊑ φ -> d1 ⊑ φ -> (openq ∅ ∅ d2) ⊑ φ -> (openq df d1 d2) ⊑ φ.
  intros. unfold openq in *. apply open_qual_subqual; auto. erewrite open_qual_commute''; eauto.
  erewrite open_qual_commute'' in H2; eauto. apply open_qual_subqual; auto. eapply closed_qual_sub; eauto.
  Unshelve. all : apply 0.
Qed.

Fixpoint has_type_filter {Γ φ Σ t T d} (ht : has_type Γ φ Σ t T d) : d ⊑ φ.
  destruct ht; intuition. specialize (has_type_closed ht1) as Hc. intuition. eapply openq_subqual; eauto.
Qed.

Lemma closed_qual_qmem_fv : forall {b f l q}, closed_qual b f l q -> forall {x}, $x ∈ᵥ q -> x < f.
  intros. specialize (@subqual_just_fv_bound x q) as Hx. destruct q. inversion H. subst.
  simpl in *. intuition.
  assert (Hsub  : NatSet.F.Subset (NatSet.F.singleton x) t). fnsetdec.
  assert (Hsub' : NatSet.F.Subset {}N t0). fnsetdec.
  assert (Hsub'': NatSet.F.Subset {}N t1). fnsetdec.
  intuition.
Qed.

Lemma bound_vars_untypable : forall {Γ φ Σ T d i}, has_type Γ φ Σ #i T d -> False.
  intros Γ φ Σ T d i HT. remember (tvar #i) as t. induction HT; try discriminate.
  intuition.
Qed.

Lemma indexr_splice_tenv : forall {Γ1 i Γ2 U du},
    indexr i (Γ1 ++ Γ2) = Some (U, du) ->
    forall {k}, k <= i -> (length Γ2) <= i -> indexr i (splice_tenv k Γ1 ++ Γ2) = Some (splice_ty k U, splice_qual k du).
  induction Γ1; intros; simpl in *; intuition. apply indexr_var_some' in H. lia.
  rewrite app_length in *. rewrite splice_tenv_length.
  destruct (Nat.eqb i (length Γ1 + length Γ2)) eqn:Heq. inversion H. subst.
  simpl. auto. apply IHΓ1; eauto.
Qed.

Lemma splice_qual_glb_dist : forall {d1 d2 k}, splice_qual k (d1 ⊓ d2) = (splice_qual k d1) ⊓ (splice_qual k d2).
  intros. destruct d1; destruct d2; intuition.
  simpl. f_equal. apply splice_set_inter_dist.
Qed.

Lemma splice_qual_lub_dist : forall {d1 d2 k}, splice_qual k (d1 ⊔ d2) = ((splice_qual k d1) ⊔ (splice_qual k d2)).
  intros. destruct d1; destruct d2; intuition.
  simpl. f_equal. apply splice_set_union_dist.
Qed.

Lemma splice_qual_qqcap_dist : forall {d1 d2 k}, splice_qual k (d1 ⋒ d2) = (splice_qual k d1) ⋒ (splice_qual k d2).
  intros. destruct d1; destruct d2; intuition.
  simpl. f_equal. apply splice_set_inter_dist.
Qed.

Lemma splice_qual_mem_lt : forall {x k d1}, x < k -> $x ∈ᵥ splice_qual k d1 -> $x ∈ᵥ d1.
  intros. destruct d1. simpl in *.
  assert (NatSet.F.Subset (NatSet.F.singleton x) (splice_set k t)).
  fnsetdec. replace (NatSet.F.singleton x) with (splice_set k (NatSet.F.singleton x)) in H1.
  rewrite splice_set_subset_dist in H1.  assert (NatSet.F.In x (NatSet.F.singleton x)).
  fnsetdec. intuition. apply splice_set_singleton_inv. auto.
Qed.

Lemma splice_set_singleton_inc : forall {i k},
    i >= k -> splice_set k (NatSet.F.singleton i) = NatSet.F.singleton (S i).
  intros. apply NatSet.eq_if_Equal. unfold splice_set. split; intros.
  - rewrite NatSetFacts.union_iff in H0. intuition.
    destruct a. apply inc_non_zero in H1. contradiction. rewrite <- inc_in_iff in H1.
    apply in_singleton_filter in H1. unfold ge_fun in *. intuition. subst. fnsetdec.
    apply in_singleton_filter in H1. unfold lt_fun in *. intuition. subst.
    rewrite Nat.ltb_lt in H2. lia.
  - rewrite NatSetFacts.singleton_iff in H0. rewrite <- H0.
    apply NatSet.F.union_2. rewrite <- inc_in_iff.
    rewrite filter_singleton_1. fnsetdec. unfold ge_fun. rewrite Nat.leb_le. lia.
Qed.

Lemma splice_qual_mem_ge : forall {x k d1}, x >= k -> $(S x) ∈ᵥ splice_qual k d1 -> $x ∈ᵥ d1.
  intros. destruct d1. simpl in *.
  assert (NatSet.F.Subset (NatSet.F.singleton (S x)) (splice_set k t)).
  fnsetdec. replace (NatSet.F.singleton (S x)) with (splice_set k (NatSet.F.singleton x)) in H1.
  rewrite splice_set_subset_dist in H1. assert (NatSet.F.In x (NatSet.F.singleton x)).
  fnsetdec. intuition. apply splice_set_singleton_inc. auto.
Qed.

Lemma splice_qual_not_mem : forall {k d1}, $ (k) ∈ᵥ splice_qual k d1 -> False.
  intros. destruct d1. simpl in H.
  unfold splice_set in *. apply NatSet.F.union_1 in H. intuition.
  - destruct k. apply inc_non_zero in H0. auto.
    rewrite <- inc_in_iff in H0. apply filter_ge_fun_prop in H0. lia.
  - apply filter_lt_fun_prop in H0. lia.
Qed.

Lemma splice_qual_just_fv_ge : forall {k j}, k <= j -> splice_qual k (just_fv j) = just_fv (S j).
  intros. unfold just_fv. simpl. rewrite splice_set_singleton_inc; auto.
Qed.

Lemma splice_qual_just_fv_lt : forall {k j}, k > j -> splice_qual k (just_fv j) = just_fv j.
  intros. unfold just_fv. simpl. rewrite splice_set_singleton_inv; auto.
Qed.

Lemma closed_qual_qplus : forall {b f l q x}, closed_qual b f l q -> x < f -> closed_qual b f l (q ⊕ x).
  intros. destruct q. simpl. inversion H. subst. repeat rewrite empty_union_right. constructor; auto.
  apply union_bound; auto. rewrite bound_singleton. lia.
Qed.

Lemma weaken_saturated : forall {Γ1 Γ2 Σ d1},
    saturated (Γ1 ++ Γ2) Σ d1 ->
    let k := (length Γ2) in forall X, saturated ((splice_tenv k Γ1) ++ X :: Γ2) Σ (splice_qual k d1).
  intros. unfold saturated. intros. bdestruct (x <? k).
  - specialize (H x). apply splice_qual_mem_lt in H0; auto. intuition. inversion H2.
    rewrite indexr_skips in H; try lia. apply (sat_var U q'); auto.
    rewrite indexr_skips. rewrite indexr_skip; auto. lia. simpl. lia.
    replace q' with (splice_qual k q'). apply subqual_splice_lr'. auto.
    eapply splice_qual_id. eapply closed_qual_monotone; eauto. lia.
  - bdestruct (x =? k).
    + subst. apply splice_qual_not_mem in H0. contradiction.
    + destruct x. lia. specialize (H x). assert (Hx : x >= k). lia.
      assert ($ (x) ∈ᵥ d1). apply (splice_qual_mem_ge Hx H0). intuition.
      inversion H4. subst. econstructor. rewrite <- indexr_insert_ge.
      eapply indexr_splice_tenv. eauto. lia. lia. lia. rewrite subqual_splice_lr'. auto.
      apply splice_qual_closed''; auto.
Qed.

Lemma weaken_gen : forall {t Γ1 Γ2 φ Σ T d},
    has_type (Γ1 ++ Γ2) φ Σ t T d ->
    let k := (length Γ2) in
    forall X, has_type ((splice_tenv k Γ1) ++ X :: Γ2) (splice_qual k φ) Σ (splice k t) (splice_ty k T) (splice_qual k d).
  intros t Γ1 Γ2 φ Σ T d HT. remember (Γ1 ++ Γ2) as Γ. generalize dependent Γ1. generalize dependent Γ2.
  induction HT; intros; subst.
  - (* tunit *) simpl. rewrite splice_set_empty.
    constructor. eapply splice_qual_closed'.
    rewrite app_length in *. rewrite splice_tenv_length. auto.
    - (* t_var *) simpl.
    destruct (le_lt_dec k x) eqn:Heq.
    * (* |Γ2| <= x < |Γ1|+|Γ2|*)
      rewrite splice_set_singleton_inc; auto. apply t_var with (d:=(splice_qual k d)).
      rewrite <- indexr_insert_ge. apply indexr_splice_tenv; eauto. lia.
      erewrite <- splice_qual_just_fv_ge; eauto.
      rewrite subqual_splice_lr'. auto.
      eapply splice_qual_closed'.
      rewrite app_length in *. rewrite splice_tenv_length. auto.
      eapply splice_ty_closed''; eauto. eapply splice_qual_closed''; eauto.
    * (* |Γ2| > x *)
      rewrite indexr_skips in H; auto. rewrite splice_set_singleton_inv; auto.
      apply t_var with (d:=d).
      rewrite <- indexr_insert_lt; auto. rewrite indexr_skips; auto.
      erewrite splice_ty_id. auto.
      eapply closed_ty_monotone; eauto. lia.
      erewrite <- splice_qual_just_fv_lt; eauto.
      rewrite subqual_splice_lr'. auto.
      eapply splice_qual_closed'.
      rewrite app_length in *. rewrite splice_tenv_length. auto.
      erewrite splice_ty_id; eauto. eapply closed_ty_monotone; eauto. lia. auto.
  - (* t_abs *) rewrite app_length in *. simpl. constructor.
    apply splice_closed'.
    1-3: rewrite app_length; rewrite splice_tenv_length; simpl;
      replace (length Γ1 + S (length Γ2)) with (S (length Γ1 + length Γ2)); eauto.
    inversion H0. subst. constructor. 1,2,5: apply splice_qual_closed; auto. 1,2 : apply splice_ty_closed; auto.
    rewrite subqual_splice_lr'. auto.
    rewrite app_comm_cons.
    replace ((splice_ty k T1, splice_qual k d1)
                :: ((TFun (splice_qual k d1) (splice_qual k d2) (splice_ty k T1)
                          (splice_ty k T2), splice_qual k df) :: splice_tenv k Γ1) ++ X :: Γ2)
            with (splice_tenv k ((T1, d1) :: (TFun d1 d2 T1 T2, df) :: Γ1) ++ X :: Γ2).
    replace (splice_qual k df
               ⋓ just_fv (length (splice_tenv k Γ1 ++ X :: Γ2))
                 ⋓ just_fv (S (length (splice_tenv k Γ1 ++ X :: Γ2))))
            with (splice_qual k (df ⊔ just_fv (length Γ1 + length Γ2) ⊔ (just_fv (S (length Γ1 + length Γ2))))).
    subst k. rewrite <- splice_open'. rewrite <- splice_ty_open'. rewrite <- splice_qual_open'.
    rewrite @open_tm'_len with (Γ':=(Γ1 ++ Γ2)). rewrite @open_ty'_len with (Γ':=(Γ1 ++ Γ2)).
    rewrite @openq'_len with (Γ':=(Γ1 ++ Γ2)).
    apply IHHT; intuition. 1-4 : repeat rewrite app_length; rewrite splice_tenv_length; auto.
    simpl. repeat rewrite splice_qual_lub_dist.
    f_equal. simpl. f_equal. rewrite splice_set_union_dist. repeat rewrite splice_set_singleton_inc; try lia; repeat f_equal; lia.
    simpl. auto.
  - (* tapp *) simpl. rewrite splice_qual_open''. apply t_app with (T1:=(splice_ty k T1)) (df:=(splice_qual k df)).
    replace (TFun (splice_qual k df ⋒ splice_qual k d1)  (splice_qual k d2) (splice_ty k T1) (splice_ty k T2)) with
    (splice_ty k (TFun (df ⋒ d1) d2 T1 T2)); auto.
    apply IHHT1; auto. simpl. f_equal. rewrite <- splice_qual_glb_dist. auto.
    apply IHHT2; auto.
    eapply splice_ty_closed'. rewrite app_length in *. rewrite splice_tenv_length. auto.
    subst k; rewrite <- @splice_qual_empty with (k := length Γ2); rewrite <- splice_qual_open''.
    rewrite subqual_splice_lr'; auto.
    all : apply weaken_saturated; auto.
  - (* t_loc *) simpl. rewrite splice_set_empty. constructor. eapply splice_qual_closed'.
    rewrite app_length in *. rewrite splice_tenv_length. auto.
    erewrite splice_ty_id; eauto. eapply closed_ty_monotone; eauto. lia.
    erewrite splice_ty_id; eauto. eapply closed_ty_monotone; eauto. lia.
    destruct φ. simpl in *. intuition.
  - (* t_ref *) simpl. rewrite splice_set_empty. eapply t_ref. simpl in IHHT. specialize (IHHT Γ2 Γ1). intuition.
  - (* t_deref *) simpl. rewrite splice_set_empty. econstructor. simpl in IHHT. subst k. apply IHHT; auto.
  - (* t_assign *) replace (splice_qual k ∅) with (∅) by auto. replace (splice_ty k TUnit) with (TUnit) by auto. simpl. eapply t_assign.
    1-2: replace (∅) with (splice_qual k ∅) by auto.
    replace (TRef TUnit) with (splice_ty k (TRef TUnit)) by auto. apply IHHT1; auto.
    replace (TUnit) with ((splice_ty k TUnit)) by auto. apply IHHT2; auto.
  - (* t_sub *) eapply t_sub. eapply IHHT; auto.
    apply @weaken_stp_gen; eauto; lia. apply subqual_splice_lr'. auto.
Qed.

Lemma weaken_flt : forall {Γ φ Σ t T d},
    has_type Γ φ Σ t T d ->
    forall {φ'}, φ ⊑ φ' ->
                 closed_qual 0 (length Γ) (length Σ) φ' ->
    has_type Γ φ' Σ t T d.
  intros Γ φ Σ t T d HT. induction HT; intros; econstructor; eauto; eapply subqual_trans; eauto.
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
  eapply splice_qual_id; eauto. eapply closed_qual_monotone; eauto; lia.
  eapply splice_qual_id; eauto. eapply closed_qual_monotone; eauto; lia.
  eapply splice_ty_id; eauto.   eapply closed_ty_monotone; eauto; lia.
  eapply splice_id; eauto.      eapply closed_tm_monotone; eauto; lia.
Qed.

Lemma weaken' : forall {φ Σ t T d},
    has_type [] φ Σ t T d -> forall {φ'}, φ ⊑ φ' -> forall {Γ}, closed_qual 0 (length Γ) (length Σ) φ' -> has_type Γ φ' Σ t T d.
  intros. eapply weaken_flt; eauto. apply weaken. auto.
Qed.

Lemma weaken_store : forall {Γ φ Σ t T d}, has_type Γ φ Σ t T d -> forall {Σ'}, Σ' ⊇ Σ -> has_type Γ φ Σ' t T d.
  intros Γ φ Σ t T d HT.
  induction HT; intros; intuition; econstructor; eauto;
    try solve [eapply closed_qual_monotone; eauto; apply extends_length; auto];
    try solve [eapply closed_tm_monotone; eauto; apply extends_length; auto];
    try solve [eapply closed_ty_monotone; eauto; apply extends_length; auto];
    try solve [eapply weaken_store_saturated; eauto].
  - unfold extends in H3. destruct H3. rewrite H3.
    rewrite indexr_skips. auto. eapply indexr_var_some'. eauto.
  - eapply weaken_stp_store_ext; eauto.
Qed.

Lemma narrowing_saturated : forall {Γ1 U du Γ2 Σ q},
    saturated (Γ1 ++ (U,du) :: Γ2) Σ q ->
    forall {V dv}, stp Γ2 Σ V dv U du -> saturated (Γ1 ++ (V,dv) :: Γ2) Σ q.
  intros. unfold saturated. intros.
  specialize (H x H1). inversion H. destruct (PeanoNat.Nat.lt_trichotomy x (length Γ2)) as [Hlen | [Hlen | Hlen] ].
  - apply (sat_var U0 q'); auto. rewrite indexr_skips in H2; simpl; auto.
    rewrite indexr_skips. rewrite indexr_skip in H2; try lia. rewrite indexr_skip; try lia.
    auto. simpl. auto.
  - rewrite indexr_skips in H2; simpl; auto. subst. rewrite indexr_head in H2. inversion H2. subst.
    apply (sat_var V dv). rewrite indexr_skips; auto. rewrite indexr_head. auto.
    apply stp_qstp_inv in H0. apply qstp_inv in H0. eapply subqual_trans; eauto.
    apply stp_closed in H0. intuition. lia.
  - destruct x. lia. rewrite <- indexr_insert_ge in H2; try lia.
    apply (sat_var U0 q'); auto. rewrite <- indexr_insert_ge; try lia. auto.
Qed.

Lemma narrowing_gen : forall {t Γ1 U du Γ2 φ Σ T d},
    has_type (Γ1 ++ (U,du) :: Γ2) φ Σ t T d ->
    forall {V dv}, stp Γ2 Σ V dv U du -> saturated Γ2 Σ du -> has_type (Γ1 ++ (V,dv) :: Γ2) φ Σ t T d.
  intros t Γ1 U du Γ2 φ Σ T d HT. remember (Γ1 ++ (U, du) :: Γ2) as Γ.
  generalize dependent Γ1. generalize dependent U. generalize dependent du. generalize dependent Γ2.
  induction HT; intros; subst.
  - econstructor; eauto.
    repeat rewrite app_length in *; simpl in *; auto.
  - repeat rewrite app_length in *; simpl in *; auto.
    destruct (PeanoNat.Nat.lt_trichotomy x (length Γ2)) as [Hlen | [Hlen | Hlen] ].
    + apply t_var with (d:=d); auto. rewrite <- indexr_insert_lt; auto. rewrite <- indexr_insert_lt in H; auto.
      repeat rewrite app_length in *; simpl in *; auto.
    + subst. rewrite indexr_insert in H. inversion H. subst.
      apply t_sub with (T1:=V) (d1:=just_fv (length Γ2)); auto. apply t_var with (d:=dv).
      rewrite indexr_insert. auto. destruct φ. simpl. auto.
      repeat rewrite app_length in *; simpl in *; auto.
      1,2 : apply stp_closed in H4; intuition.
      eapply stp_shrink_var; eauto. eapply weaken_stp'; eauto. eapply weaken_stp; eauto. rewrite app_length. simpl. lia.
    + apply t_var with (d:=d); auto. destruct x. lia. rewrite <- indexr_insert_ge; try lia.
      rewrite <- indexr_insert_ge in H; try lia. auto.
      repeat rewrite app_length in *; simpl in *; auto.
  - repeat rewrite app_length in *; simpl in *; auto.
    constructor; auto. 1-3 : rewrite app_length in *; simpl in *; auto.
    rewrite @open_tm'_len with (Γ' := (Γ1 ++ (U, du) :: Γ2)).
    rewrite @open_ty'_len with (Γ' := (Γ1 ++ (U, du) :: Γ2)).
    rewrite @openq'_len with (Γ' := (Γ1 ++ (U, du) :: Γ2)).
    2-4 : repeat rewrite app_length; simpl; auto.
    rewrite app_length. simpl.
    rewrite app_comm_cons. rewrite app_comm_cons.
    eapply IHHT; eauto. simpl. auto.
  - econstructor; eauto.
    repeat rewrite app_length in *; simpl in *; auto.
    all: eapply narrowing_saturated; eauto.
  - econstructor; eauto.
    repeat rewrite app_length in *; simpl in *; auto.
  - eapply t_ref; eauto.
  - econstructor; eauto.
  - eapply t_assign; eauto.
  - eapply t_sub; eauto. eapply narrowing_stp_gen; eauto.
Qed.

Lemma narrowing : forall {Γ U du φ Σ t T d}, has_type ((U,du) :: Γ) φ Σ t T d -> forall {V dv}, stp Γ Σ V dv U du -> saturated Γ Σ du -> has_type ((V,dv) :: Γ) φ Σ t T d.
  intros. specialize (@narrowing_gen t [] U du Γ φ Σ T d) as narrow. simpl in *. eapply narrow; eauto.
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

Lemma CtxOK_weaken_flt : forall {Γ φ Σ σ}, CtxOK Γ φ Σ σ -> forall {φ'}, closed_qual 0 (length Γ) (length Σ) φ' -> φ ⊑ φ' -> CtxOK Γ φ' Σ σ.
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

Lemma subst1_qual_id : forall {b l q}, closed_qual b 0 l q -> forall {q1}, { 0 |-> q1 }ᵈ q = q.
Proof.
  intros. inversion H; subst; intros; intuition. simpl.
  rewrite bound_le_mem_false. 2: lia.
  erewrite unsplice_set_inv; eauto; apply bound_0_empty in H0; subst; rewrite remove_empty; auto.
  rewrite bound_empty. lia.
Qed.

Lemma subst1_qual_empty : forall {dx}, {0 |-> dx }ᵈ ∅ = ∅.
  intros. apply (@subst1_qual_id 0 0). auto.
Qed.
#[global] Hint Resolve subst1_qual_empty : core.

Lemma subst1_ty_id : forall {T b l}, closed_ty b 0 l T -> forall {d1}, { 0 |-> d1 }ᵀ T = T.
  induction T; intros; inversion H; subst; simpl; intuition;
                       try solve [erewrite IHT; eauto];
                       try solve [erewrite IHT1; eauto; erewrite IHT2; eauto].
  erewrite IHT1; eauto. erewrite IHT2; eauto.
  erewrite subst1_qual_id; eauto. erewrite subst1_qual_id; eauto.
Qed.

Lemma subst_ty_id : forall {b l T}, closed_ty b 0 l T -> forall {d1 d2}, { 0 |-> d1 ; d2 }ᵀ T = T.
  intros. repeat erewrite subst1_ty_id; eauto.
Qed.

Lemma subst1_tm_id : forall {t b l}, closed_tm b 0 l t -> forall {t1}, { 0 |-> t1 }ᵗ t = t.
  induction t; intros b loc Hc; inversion Hc; subst; intros; simpl; intuition;
                       try solve [erewrite IHt; eauto];
                       try solve [erewrite IHt1; eauto; erewrite IHt2; eauto].
Qed.

Lemma open_subst1_qual : forall {q b l},
    closed_qual b 0 l q ->
    forall {k d1},
      [[k ~> d1 ]]ᵈ q = { 0 |-> d1 }ᵈ ([[k ~> (just_fv 0)]]ᵈ q).
  intros. inversion H; subst; intuition. simpl.
  destruct d1.
  rewrite empty_union_right. rewrite empty_union_right.
  destruct (NatSet.F.mem k bs) eqn: Hmem. simpl.
  assert (NatSet.F.mem 0 (NatSet.F.union vs (NatSet.F.singleton 0)) = true).
  apply NatSet.F.mem_1. fnsetdec.
  rewrite H3. f_equal. apply bound_0_empty in H0. rewrite H0.
  rewrite empty_union_left. rewrite empty_union_left.
  rewrite remove_singleton_empty. rewrite unsplice_set_empty.
  rewrite empty_union_left. auto.
  simpl. rewrite bound_le_mem_false; auto.
  apply bound_0_empty in H0. subst.
  rewrite remove_empty. rewrite unsplice_set_empty. auto.
Qed.

Lemma open_subst1_ty : forall {T b l},
    closed_ty b 0 l T ->
    forall {k d1},
      [[k ~> d1 ]]ᵀ T = { 0 |-> d1 }ᵀ ([[k ~> (just_fv 0)]]ᵀ T).
  induction T; intros; inversion H; subst; simpl; intuition.
  erewrite IHT1; eauto. erewrite IHT2; eauto.
  erewrite <- open_subst1_qual; eauto. erewrite <- open_subst1_qual; eauto.
  erewrite IHT; eauto.
Qed.

Lemma open_subst1_tm : forall {t b l},
    closed_tm b 0 l t ->
    forall {k t1},
      [[k ~> t1 ]]ᵗ t = { 0 |-> t1 }ᵗ ([[k ~> $ 0]]ᵗ t).
  induction t; intros b loc Hc; inversion Hc; subst; intros; simpl; intuition;
    try solve [erewrite IHt; eauto];
    try solve [erewrite IHt1; eauto; erewrite IHt2; eauto].
  bdestruct (k =? x); simpl; intuition.
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
    closed_qual 0 ff lf df ->
    [[k ~> just_fv g ]]ᵈ ({0 |-> df }ᵈ q) = {0 |-> df }ᵈ ([[ k ~> just_fv (S g) ]]ᵈ q).
  intros. destruct q; simpl; intuition. destruct df.
  inversion H. subst.
  destruct (NatSet.F.mem 0 t) eqn: Hmem1.
  - destruct (NatSet.F.mem k t0) eqn: Hmem2.
    + simpl. rewrite NatSet.F.mem_1. rewrite NatSet.F.mem_1.
      f_equal; try fnsetdec. rewrite remove_union_dist.
      rewrite unsplice_set_union_dist.
      rewrite remove_singleton_inv by lia.
      unfold unsplice_set at 3. rewrite filter_singleton_1. rewrite dec_singleton.
      rewrite filter_singleton_2. simpl. rewrite empty_union_right. fnsetdec.
      apply Nat.ltb_ge. lia. apply leb_correct. lia.
      apply bound_0_empty in H7. subst.
      repeat rewrite empty_union_right. auto.
      apply NatSet.F.union_2. apply NatSet.F.mem_2. auto.
      apply NatSet.F.union_2. apply NatSet.F.mem_2. auto.
    + simpl. apply bound_0_empty in H7. subst.
      repeat rewrite empty_union_right.
      rewrite Hmem2. rewrite Hmem1. auto.
  - destruct (NatSet.F.mem k t0) eqn: Hmem2.
    + simpl. rewrite Hmem2. rewrite not_member_union; auto.
      f_equal. rewrite remove_union_dist. rewrite remove_singleton_inv by lia.
      rewrite unsplice_set_union_dist. unfold unsplice_set at 3.
      rewrite filter_singleton_1. rewrite dec_singleton. simpl.
      rewrite filter_singleton_2. simpl. rewrite empty_union_right. fnsetdec.
      apply Nat.ltb_ge. lia. apply leb_correct. lia.
      rewrite mem_singleton. simpl. auto.
    + simpl. rewrite Hmem1.  rewrite Hmem2. auto.
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

Lemma closed_qual_subst1 : forall {q b f l},
    closed_qual b (S f) l q ->
    forall {d1 l1}, closed_qual 0 0 l1 d1 ->
    forall{l2},
      l <= l2 -> l1 <= l2 ->
      closed_qual b f l2 ({0 |-> d1}ᵈ q).
  intros. inversion H; subst; intuition. inversion H0. subst.
  simpl. destruct (NatSet.F.mem 0 vs) eqn:Hmem.
  constructor. apply bound_0_empty in H6. subst.
  rewrite empty_union_right.
  apply unsplice_set_dec. apply H3.
  apply union_bound; lia.
  apply union_bound; lia.
  constructor; try lia. apply unsplice_set_dec. apply H3.
Qed.

Lemma closed_ty_subst1 : forall {T b f l},
    closed_ty b (S f) l T ->
    forall {d1 l1}, closed_qual 0 0 l1 d1 ->
    forall{l2},
      l <= l2 -> l1 <= l2 ->
      closed_ty b f l2 ({0 |-> d1}ᵀ T).
  intros T b f l Hc. remember (S f) as f'. generalize dependent f.
  induction Hc; intros; subst; simpl in *; intuition; try constructor;
    try solve [eapply IHHc; eauto; lia ];
    try solve [eapply IHHc1; eauto];
    try solve [eapply IHHc2; eauto; lia].
  erewrite subst1_ty_id; eauto.
  eapply closed_qual_subst1; eauto.
  eapply closed_qual_subst1; eauto.
Qed.

Lemma closed_tm_subst1 : forall {t b f l},
    closed_tm b (S f) l t ->
    forall {t1 l1}, closed_tm 0 0 l1 t1 ->
    forall{l2},
      l <= l2 -> l1 <= l2 ->
      closed_tm b f l2 ({0 |-> t1}ᵗ t).
  intros t b f l Hc. remember (S f) as f'.
  generalize dependent f.
  induction Hc; intros; subst; simpl in *; intuition; try constructor;
    try solve [eapply IHHc; eauto; lia ];
    try solve [eapply IHHc1; eauto];
    try solve [eapply IHHc2; eauto].
  bdestruct (x =? 0).
  eapply closed_tm_monotone; eauto; lia. intuition.
Qed.

Lemma open_subst2_qual : forall {q l},
    closed_qual 2 0 l q ->
    forall {d1 df}, closed_qual 0 0 l d1 ->
    [[1~> df ]]ᵈ ([[0~> d1 ]]ᵈ q) = { 0 |-> d1; df }ᵈ ([[1 ~> (just_fv 1)]]ᵈ ([[0 ~> (just_fv 0)]]ᵈ q)).
  intros. erewrite <- open_subst1_qual_comm; eauto.
  erewrite open_subst1_qual; eauto. f_equal. f_equal.
  erewrite open_subst1_qual; eauto. erewrite open_subst1_qual; eauto.
  eapply closed_qual_subst1; eauto. eapply closed_qual_open_succ; eauto.
Qed.

Lemma open_subst2_ty : forall {T l},
    closed_ty 2 0 l T ->
    forall {d1 df}, closed_qual 0 0 l d1 ->
    [[1~> df ]]ᵀ ([[0~> d1 ]]ᵀ T) = { 0 |-> d1; df }ᵀ ([[1 ~> (just_fv 1)]]ᵀ ([[0 ~> (just_fv 0)]]ᵀ T)).
  intros. erewrite <- open_subst1_ty_comm; eauto.
  erewrite open_subst1_ty; eauto. f_equal. f_equal.
  erewrite open_subst1_ty; eauto. erewrite open_subst1_ty; eauto.
  eapply closed_ty_subst1; eauto. eapply closed_ty_open_succ; eauto.
Qed.

Lemma open_subst2_tm : forall {t l},
    closed_tm 2 0 l t ->
    forall {t1 tf}, closed_tm 0 0 l t1 ->
    [[1~> tf ]]ᵗ ([[0~> t1 ]]ᵗ t) = { 0 |-> t1; tf }ᵗ ([[1 ~> $1 ]]ᵗ ([[0 ~> $0 ]]ᵗ t)).
  intros. erewrite <- open_subst1_tm_comm; eauto.
  erewrite open_subst1_tm; eauto. f_equal. f_equal.
  erewrite open_subst1_tm; eauto. erewrite open_subst1_tm; eauto.
  eapply closed_tm_subst1; eauto. eapply closed_tm_open_succ; eauto.
Qed.

Lemma subst1_qlub_dist : forall {q1 q2 df},
    ({ 0 |-> df }ᵈ (q1 ⊔ q2)) = (({ 0 |-> df }ᵈ q1) ⊔ ({ 0 |-> df }ᵈ q2)).
  intros. destruct q1; destruct q2; destruct df; simpl; auto.
  destruct (NatSet.F.mem 0 t) eqn: Hmem1.
  - rewrite NatSet.F.mem_1.
    destruct (NatSet.F.mem 0 t2) eqn: Hmem2.
    simpl. f_equal; try fnsetdec.
    rewrite union_assoc. rewrite remove_union_dist.
    rewrite unsplice_set_union_dist. rewrite union_assoc. f_equal.
    fnsetdec.
    simpl. f_equal; try fnsetdec.
    rewrite union_assoc. rewrite remove_union_dist.
    rewrite unsplice_set_union_dist. fnsetdec.
    apply NatSet.F.union_2. apply NatSet.F.mem_2. auto.
  - destruct (NatSet.F.mem 0 t2) eqn: Hmem2.
    + simpl. rewrite NatSet.F.mem_1.
      f_equal; try fnsetdec.
      rewrite remove_union_dist.
      rewrite unsplice_set_union_dist. fnsetdec.
      apply NatSet.F.union_3. apply NatSet.F.mem_2. auto.
    + simpl. rewrite not_member_union; auto.
      f_equal; try fnsetdec.
      rewrite <- unsplice_set_union_dist. rewrite <- remove_union_dist. auto.
Qed.

Lemma subst1_qual_plus : forall {l du},
    closed_qual 0 0 l du -> du = {0 |-> du }ᵈ (du ⊕ 0).
  intros. destruct du; intuition. unfold qplus.
  inversion H. subst. apply bound_0_empty in H6. subst.
  simpl. rewrite empty_union_left. repeat rewrite empty_union_right.
  rewrite NatSet.F.mem_1 by fnsetdec. f_equal; try fnsetdec.
  rewrite remove_singleton_empty. rewrite unsplice_set_empty. auto.
Qed.

Lemma subst1_qual_plus' : forall {du du' l},
    du' ⊑ du -> closed_qual 0 0 l du -> {0 |-> du }ᵈ (du' ⊕ 0) = du.
Proof.
  intros. destruct du'; intuition. destruct du.
  inversion H. destruct H2. inversion H0. subst.
  simpl. rewrite NatSet.F.mem_1 by fnsetdec.
  repeat rewrite empty_union_right.
  apply bound_0_empty in H10. apply bound_0_empty in H11.
  subst. assert (t = {}N) by fnsetdec. assert (t0 = {}N) by fnsetdec.
  subst. repeat rewrite empty_union_right.
  repeat rewrite empty_union_left. f_equal.
  rewrite remove_singleton_empty. rewrite unsplice_set_empty. auto.
  fnsetdec.
Qed.

Lemma subst1_qual_plus_dist : forall {x d df},
    1 <= x -> ({ 0 |-> df }ᵈ (d ⊕ x)) = (({ 0 |-> df }ᵈ d) ⊕ (pred x)).
Proof.
  intros. destruct d; destruct df; intuition; simpl.
  destruct (NatSet.F.mem 0 t) eqn: Hmem1.
  - rewrite NatSet.F.mem_1. simpl.
    repeat rewrite empty_union_right. f_equal.
    rewrite union_assoc. rewrite remove_union_dist.
    rewrite unsplice_set_union_dist. rewrite union_assoc. f_equal.
    rewrite remove_singleton_inv by lia. unfold unsplice_set.
    rewrite filter_singleton_1. rewrite filter_singleton_2.
    rewrite dec_singleton. rewrite empty_union_right. fnsetdec. autounfold.
    rewrite Nat.ltb_ge. lia. rewrite leb_correct. lia. lia.
    apply NatSet.F.union_2. apply NatSet.F.mem_2 in Hmem1. auto.
  - assert (NatSet.F.mem 0 (NatSet.F.union t (NatSet.F.singleton x)) = false).
    rewrite NatSetProperties.Dec.F.union_b. rewrite Hmem1. simpl.
    rewrite mem_singleton. bdestruct (0 =? x). lia. auto.
    rewrite H0. simpl.
    repeat rewrite empty_union_right. f_equal.
    rewrite remove_union_dist. rewrite unsplice_set_union_dist.
    f_equal.
    rewrite remove_singleton_inv by lia. unfold unsplice_set.
    rewrite filter_singleton_1. rewrite filter_singleton_2.
    rewrite dec_singleton. fnsetdec. autounfold.
    rewrite Nat.ltb_ge. lia. rewrite leb_correct. lia. lia.
Qed.

Lemma subst1_open_qual_comm : forall {k l d1 d2 q1},
    closed_qual 0 0 l q1 ->
    { 0 |-> q1 }ᵈ (open_qual k d1 d2) = open_qual k ({ 0 |-> q1 }ᵈ d1) ({ 0 |-> q1 }ᵈ d2).
Proof.
  intros. destruct d2; simpl; auto. destruct d1; simpl. destruct q1; simpl.
  inversion H. subst. apply bound_0_empty in H6. apply bound_0_empty in H7.
  subst.
  repeat rewrite empty_union_right.
  destruct (NatSet.F.mem k t0) eqn:Hmem1.
  - simpl. destruct (NatSet.F.mem 0 t2) eqn:Hmem2.
    + rewrite NatSet.F.mem_1.
      destruct (NatSet.F.mem 0 t) eqn:Hmem3;
      simpl; rewrite Hmem1; rewrite empty_union_right;
        f_equal; try fnsetdec; rewrite <- unsplice_set_union_dist;
          rewrite <- remove_union_dist; auto.
      apply NatSet.F.union_3. apply NatSet.F.mem_2. auto.
    + destruct (NatSet.F.mem 0 t) eqn:Hmem3.
      * rewrite NatSet.F.mem_1.
        simpl. rewrite Hmem1. rewrite empty_union_right.
        f_equal; try fnsetdec.
        rewrite <- unsplice_set_union_dist. rewrite <- remove_union_dist. auto.
        apply NatSet.F.union_2. apply NatSet.F.mem_2. auto.
      * rewrite not_member_union; auto. simpl. rewrite Hmem1.
        f_equal.
        rewrite <- unsplice_set_union_dist. rewrite <- remove_union_dist. auto.
  - simpl. destruct (NatSet.F.mem 0 t) eqn: Hmem2.
    + destruct (NatSet.F.mem 0 t2) eqn: Hmem3; simpl;
        rewrite Hmem1; repeat rewrite empty_union_right; auto.
    + destruct (NatSet.F.mem 0 t2) eqn: Hmem3; simpl; rewrite Hmem1; auto.
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

Lemma subst_qual_subqual_monotone : forall {d1 d2}, d1 ⊑ d2 -> forall {df}, ({0 |-> df }ᵈ d1) ⊑ ({0 |-> df }ᵈ d2).
Proof.
  intros. destruct d1; destruct d2; destruct df; simpl; intuition.
  inversion H. intuition.
  destruct (NatSet.F.mem 0 t) eqn: Hmem1; destruct (NatSet.F.mem 0 t2) eqn: Hmem2;
    simpl; intuition; try fnsetdec.
  - apply NatSetProperties.union_subset_4.
    apply unsplice_set_subset_monotone. auto.
  - specialize (@subset_inclusion _ _ _ H0 Hmem1 Hmem2) as F. inversion F.
  - specialize (@subset_inclusion _ _ _ H0 Hmem1 Hmem2) as F. inversion F.
  - specialize (@subset_inclusion _ _ _ H0 Hmem1 Hmem2) as F. inversion F.
  - specialize (@NatSetProperties.union_subset_1 (unsplice_set 0 (NatSet.F.remove 0 t2)) t5) as Hs.
    specialize (@unsplice_set_subset_monotone t t2 H0) as Hs2.
    fnsetdec.
  - apply unsplice_set_subset_monotone. auto.
Qed.

Lemma subst1_just_fv : forall {x dy},
    just_fv x = {0 |-> dy }ᵈ (just_fv (S x)).
  intros. simpl. rewrite mem_singleton. simpl.
  rewrite remove_singleton_inv by lia.
  unfold unsplice_set.
  specialize (@max_elt_singleton (S x)) as H.
  assert (0 <= S x) by lia.
  rewrite filter_singleton_1. rewrite filter_singleton_2.
  rewrite empty_union_right. rewrite dec_singleton. simpl.
  unfold just_fv. auto. apply Nat.ltb_ge. lia. apply leb_correct. lia.
Qed.

Lemma closed_qual_subst1' : forall {Γ0 X l df φ b},
    closed_qual 0 0 l df ->
    closed_qual b (length (Γ0 ++ [X])) l φ ->
    closed_qual b (length ({0 |-> df }ᴳ Γ0)) l ({0 |-> df }ᵈ φ).
  intros. repeat eapply closed_qual_subst1; eauto. rewrite subst1_tenv_length.
  rewrite app_length in *. simpl in *. replace (length Γ0 + 1) with (S (length Γ0)) in H0.
  auto. lia.
Qed.

Lemma closed_tm_subst1' : forall {Γ0 X l df tx t b},
    closed_tm 0 0 l tx ->
    closed_tm b (length (Γ0 ++ [X])) l t ->
    closed_tm b (length ({0 |-> df }ᴳ Γ0)) l ({0 |-> tx }ᵗ t).
  intros. repeat eapply closed_tm_subst1; eauto. rewrite subst1_tenv_length.
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

Lemma subst_qstp :  forall {Γ Tf df df' Σ d1 d2},
    qstp (Γ ++ [(Tf, df)]) Σ d1 d2 ->
    closed_qual 0 0 (length Σ) df' ->
    Substq df df' ->
    qstp ({0 |-> df' }ᴳ Γ) Σ ({0 |-> df' }ᵈ d1) ({0 |-> df' }ᵈ d2).
  intros. inversion H. subst.
  constructor. apply subst_qual_subqual_monotone. auto.
  eapply closed_qual_subst1'; eauto.
Qed.

Lemma subst_stp : forall{T1 T2},
    forall {Γ Tf df df' Σ d1 d2},
      stp (Γ ++ [(Tf,df)]) Σ T1 d1 T2 d2 ->
      closed_qual 0 0 (length Σ) df' ->
      Substq df df' ->
      stp ({ 0 |-> df' }ᴳ Γ) Σ
          ({ 0 |-> df' }ᵀ T1) ({ 0 |-> df' }ᵈ d1)
          ({ 0 |-> df' }ᵀ T2) ({ 0 |-> df' }ᵈ d2).
  intros T1 T2 Γ Tf df df' Σ d1 d2 HS.
  remember (Γ ++ [(Tf, df)]) as Γ'.
  generalize dependent Γ. generalize dependent df.  generalize dependent Tf. induction HS; intros; subst.
  - simpl. constructor. eapply subst_qstp; eauto.
  - specialize (stp_closed HS1). intuition. specialize (stp_closed HS2). intuition.
    simpl. constructor. eapply subst_qstp; eauto.
    all : repeat erewrite subst1_ty_id; eauto.
  - simpl. constructor. inversion H. subst. 2 : inversion H0. subst.
    1,2: constructor; try eapply closed_ty_subst1'; eauto; eapply closed_qual_subst1'; eauto.
    eapply subst_qstp; eauto. eapply IHHS1; eauto.
    unfold open_ty' in *. unfold open_ty in *.
    unfold openq' in *. unfold openq in *.
    rewrite app_length in *. rewrite subst1_tenv_length. simpl in *.
    replace (length Γ0 + 1) with (S (length Γ0)) in *; try lia.
    specialize (IHHS2 Tf df ((T3, d3) :: (TFun d1 d2 T1 T2, d5) :: Γ0)). simpl in IHHS2. intuition. rename H4 into IHHS2.
    erewrite <- open_subst1_ty_comm in IHHS2; eauto. erewrite <- open_subst1_ty_comm in IHHS2; eauto.
    erewrite <- open_subst1_ty_comm in IHHS2; eauto. erewrite <- open_subst1_ty_comm in IHHS2; eauto.
    erewrite <- open_subst1_qual_comm in IHHS2; eauto. erewrite <- open_subst1_qual_comm in IHHS2; eauto.
    erewrite <- open_subst1_qual_comm in IHHS2; eauto. erewrite <- open_subst1_qual_comm in IHHS2; eauto.
  -  econstructor; eauto.
Qed.

Lemma substitution_stp : forall{T1 T2},
    forall {Tx Tf df dx Σ d1 d2},
      stp ([(Tx,df ⋒ dx); (Tf,df)]) Σ T1 d1 T2 d2 ->
      closed_ty 0 0 (length Σ) Tx ->
      closed_qual 0 0 (length Σ) df -> closed_qual 0 0 (length Σ) dx ->
      stp [] Σ ({ 0 |-> df; dx }ᵀ T1) ({ 0 |-> df ; dx }ᵈ d1) ({ 0 |-> df ; dx }ᵀ T2) ({ 0 |-> df ; dx }ᵈ d2).
  intros. replace [(Tx, df ⋒ dx); (Tf,df)] with ([(Tx, df ⋒ dx)] ++ [(Tf,df)]) in H; auto.
  eapply @subst_stp with (df':=df) in H; auto.
  replace ({0 |-> df }ᴳ [(Tx, df ⋒ dx)]) with ([(Tx, df ⋒ dx)]) in H.
  replace ([(Tx, df ⋒ dx)]) with ([] ++ [(Tx, df ⋒ dx)]) in H; auto.
  eapply @subst_stp with (df':=dx) in H; auto.
  simpl. erewrite subst1_ty_id; eauto. erewrite subst1_qual_id; eauto.
  apply closed_qual_qqcap; eauto.
Qed.

Lemma subst_filter0 : forall {d φ l}, closed_qual 0 0 l d -> (just_fv 0) ⊑ φ -> d ⊑ { 0 |-> d }ᵈ φ.
  intros. destruct d; simpl in *. destruct φ. intuition. simpl.
  inversion H. subst. rewrite NatSet.F.mem_1. intuition.
  eapply NatSetProperties.in_subset; eauto. fnsetdec.
Qed.

Lemma subst1_just_fv0 : forall {q}, {0 |-> q }ᵈ (just_fv 0) = q.
  intros. simpl. destruct q; intuition. repeat rewrite empty_union_left.
  rewrite NatSet.F.mem_1 by fnsetdec. rewrite remove_singleton_empty.
  rewrite unsplice_set_empty. rewrite empty_union_left. auto.
Qed.

Lemma subst1_just_fv0' : forall {q}, {0 |-> q }ᵈ (just_fv 0) = (q ⊔ ∅).
  intros. simpl. destruct q; intuition. repeat rewrite empty_union_left.
  rewrite NatSet.F.mem_1 by fnsetdec. rewrite remove_singleton_empty.
  rewrite unsplice_set_empty. rewrite empty_union_left.
  rewrite empty_neutral_set. auto.
Qed.

Lemma subst_filter1 : forall {d' q φ l}, closed_qual 0 0 l q -> q ⋒ d' ⊕ 0 ⊑ φ -> q ⊑ { 0 |-> q }ᵈ φ.
  intros. destruct q. destruct d'. simpl in *. destruct φ.
  intuition. simpl. rewrite NatSet.F.mem_1.
  intuition.
  assert (NatSet.F.In 0 (NatSet.F.union  (NatSet.F.inter t t2) (NatSet.F.singleton 0))). fnsetdec.
  eapply NatSetProperties.in_subset; eauto.
Qed.

Lemma subqual_qqcap' :  forall {a b c d'}, qset a b c ⋒ d' ⊑ qset a b c.
  destruct d'.
  specialize @qglb_is_glb with (d1:=(qset a b c)) (d2:=qset t t0 t1). intuition.
Qed.

Import NatSet.F.

Lemma saturated0 : forall {Γ Σ Tx fx bx lx ff bf lf},
    mem 0 ff = true -> saturated (Γ ++ [(Tx, qset fx bx lx)]) Σ (qset ff bf lf) -> fx [<=] ff /\ bx [<=] bf /\ lx [<=] lf.
  intros. specialize (H0 0). simpl in H0. apply mem_2 in H.
  apply H0 in H. inversion H. rewrite indexr_skips in H1; auto. simpl in H1.
  inversion H1. subst. simpl in H2. auto.
Qed.

Lemma subst1_preserves_separation : forall {df d1 Tx dx dx' Γ Σ φ},
    dx' ⋒ φ ≡ dx ->
    closed_qual 0 0 (length Σ) dx' ->
    df ⊑ φ -> d1 ⊑ φ ->
    saturated (Γ ++ [(Tx, dx)]) Σ d1 ->
    saturated (Γ ++ [(Tx, dx)]) Σ df ->
    {0 |-> dx' }ᵈ df ⋒ {0 |-> dx' }ᵈ d1 = {0 |-> dx' }ᵈ (df ⋒ d1).
  intros. destruct df as [ff bf lf]. destruct d1 as [f1 b1 l1]. destruct dx' as [fx' bx' lx'].
  destruct φ as [fp bp lp]. inversion H0. subst. apply bound_0_empty in H11, H12.
  subst. destruct dx as [fx bx lx]. simpl in H. intuition. rewrite inter_empty_left in H5.
  rewrite inter_empty_left in H. symmetry in H5. symmetry in H. apply NatSet.eq_if_Equal in H5.
  apply NatSet.eq_if_Equal in H. subst. simpl.
  destruct (mem 0 ff) eqn:Hmem0ff; destruct (mem 0 f1) eqn:Hmem0f1; simpl; rewrite NatSetFacts.inter_b;
    rewrite Hmem0ff; rewrite Hmem0f1; simpl.
  - (*0 ∈ df, 0 ∈ d1 : this is trivial since we substitute the first variable for a closed value. The case for general
      substitution would require more careful reasoning. *)
    f_equal; try fnsetdec. repeat rewrite empty_union_right.
    apply NatSet.eq_if_Equal. apply inter_unsplice_0.
  - (* 0 ∈ df, 0 ∉ d1 *) f_equal; try fnsetdec. repeat rewrite empty_union_right.
    apply NatSet.eq_if_Equal. apply inter_unsplice_0.
    (* the interesting bit is reasoning about the overlap, this requires the extra assumptions about
       saturation of the sets and the boundedness of the context. *)
    apply NatSet.eq_if_Equal.
    setoid_rewrite NatSetProperties.union_inter_1.
    assert (Hl1 : inter lx' l1 [<=] lx). { simpl in H2. intuition. fnsetdec. }
    specialize (saturated0 Hmem0ff H4) as Hlx.
    fnsetdec.
  - (* 0 ∉ df, 0 ∈ d1, analogous to the previous case *)
    f_equal; try fnsetdec. repeat rewrite empty_union_right.
    apply NatSet.eq_if_Equal. apply inter_unsplice_0.
    apply NatSet.eq_if_Equal. rewrite NatSetProperties.inter_sym.
    setoid_rewrite NatSetProperties.union_inter_1.
    assert (Hl1 : inter lx' lf [<=] lx). { simpl in H1. intuition. fnsetdec. }
    specialize (saturated0 Hmem0f1 H3) as Hlx.
    fnsetdec.
  - (* 0 ∉ df, 0 ∉ d1 : trivial, since the substitution has no effect (other than unsplicing the sets) *)
    f_equal; try fnsetdec. apply NatSet.eq_if_Equal. apply inter_unsplice_0.
Qed.

Lemma subst1_mem : forall {x dx df l}, closed_qual 0 0 l dx -> $ (x) ∈ᵥ {0 |-> dx }ᵈ df -> $ (S x) ∈ᵥ df.
  intros. inversion H. subst. apply bound_0_empty in H1, H2. subst. destruct df. simpl in *.
  destruct (mem 0 t0) eqn:Hmem0t0; simpl in H0;
    unfold unsplice_set in H0; rewrite filter_lt_0 in H0; rewrite filter_ge0_id in H0;
    repeat rewrite empty_union_right in H0.
  - destruct x. rewrite dec_in0 in H0. fnsetdec. fnsetdec.
    change (S x) with (pred (S (S x))) in H0. rewrite <- dec_in_iff in H0. fnsetdec. lia.
  - destruct x. rewrite dec_in0 in H0. fnsetdec. fnsetdec.
    change (S x) with (pred (S (S x))) in H0. rewrite <- dec_in_iff in H0. fnsetdec. lia.
Qed.

Lemma subst1_saturated : forall {Γ Σ Tx dx df dx'},
    saturated (Γ ++ [(Tx, dx)]) Σ df ->
    closed_qual 0 0 (length Σ) dx' ->
    saturated ({0 |-> dx' }ᴳ Γ) Σ ({0 |-> dx' }ᵈ df).
  intros. inversion H0. subst. apply bound_0_empty in H1.
  apply bound_0_empty in H2. subst. unfold saturated. intros.
  eapply subst1_mem in H1; eauto.
  apply H in H1. inversion H1. apply @indexr_subst1 with (dx:=(qset {}N {}N ls)) in H2.
  simpl in H2. econstructor. eauto. apply subst_qual_subqual_monotone. auto.
  eapply closed_qual_subst1; eauto. lia.
Qed.

Lemma qqcap_increase_fresh : forall {dx dx' φ' l X},
  dx' ⋒ φ' ≡ dx ->
  closed_qual 0 0 l dx' ->
  dx' ⋒ (φ' ⋓ qset X {}N {}N) ≡ dx.
  intros. inversion H0. subst. apply bound_0_empty in H1, H2.
  subst. destruct dx. destruct φ'. simpl in *. intuition; try fnsetdec.
Qed.

Lemma vtp_closed:
  forall {Σ t T d}, vtp Σ t T d ->
    closed_tm 0 0 (length Σ) t /\
    closed_ty 0 0 (length Σ) T /\
    closed_qual 0 0 (length Σ) d .
Proof.
  intros. induction H; intuition.
  - constructor. apply indexr_var_some' in H1; intuition.
  - constructor. apply stp_closed in H2. intuition.
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
      assert (narrow: stp [(T3, d3); (TFun d0 d7 T0 T5, df1)] Σ (open_ty' ([]: tenv) T5)(openq' ([]:tenv) d7) (open_ty' ([]:tenv) T2) (openq' ([]: tenv) d2)). {
        eapply narrowing_stp; eauto.  apply weaken_stp. auto.
      }
      simpl in *. eapply s_trans; eauto.
      replace ([(T3, d3); (TFun d0 d7 T0 T5, df1)]) with ([(T3, d3)] ++ (TFun d0 d7 T0 T5, df1) :: []); auto.
      clear H5. eapply narrowing_stp_gen; eauto. auto.
  - intuition.
Qed.

Lemma has_type_vtp: forall {Σ φ t T d},
  value t ->
  has_type [] φ Σ t T d ->
  vtp Σ t T d.
Proof.
  intros. remember [] as Γ.  induction H0; eauto; subst; try inversion H.
  - subst. simpl in *. (* tabs *) eapply vtp_abs; eauto.
    + eapply closed_qual_sub; eauto.
    + eapply stp_refl. inversion H1. subst. intuition.
      apply qstp_refl. apply eqqual_refl; intuition.
      inversion H2; subst. inversion H1. intuition.
    + apply qstp_refl. apply eqqual_refl; intuition. eapply closed_qual_sub; eauto.
    + apply stp_refl. inversion H1. subst.
      * simpl in *. unfold open_ty'. unfold open_ty. simpl in *.
        rewrite open_rec_ty_commute; auto.
        apply closed_ty_open; auto. apply closed_ty_open; auto. eapply closed_ty_monotone; eauto.
      * apply qstp_refl.  apply eqqual_refl.  apply has_type_closed in H4; intuition.
  - (* tloc *) eapply vtp_loc; eauto.
    + eapply closed_qual_sub; eauto.
    + apply stp_refl. intuition. apply qstp_refl. eapply eqqual_refl. apply closed_qual_empty.
    + apply stp_refl. intuition. constructor. intuition. apply closed_qual_empty.
    + apply qstp_refl. apply eqqual_refl. apply just_loc_closed. apply indexr_var_some' in H1. intuition.
  - subst. intuition. eapply vtp_widening; eauto.
  - subst. intuition. eapply vtp_widening; eauto.
  - subst. intuition. eapply vtp_widening; eauto.
Qed.

Lemma vtp_has_type: forall {Σ t T d}, vtp Σ t T d ->  has_type [] d Σ t T d.
Proof.
  intros. induction H.
  - econstructor; eauto. econstructor; eauto. constructor. auto. eapply closed_qual_sub; eauto.
  - assert (has_type [] (just_loc l) Σ (tloc l) (TRef T) (just_loc l)). {
      econstructor; eauto. apply just_loc_closed. apply indexr_var_some' in H1. auto. }
    eapply weaken_flt with (φ' := d) in H5; intuition. eapply t_sub; eauto.
    constructor; intuition. inversion H4. intuition.
  - specialize (qstp_closed H5) as Hcl. intuition.
    assert (has_type [] df1 Σ (tabs t0) (TFun d1 d2 T1 T2) df1). {
    constructor; eauto. }
    eapply weaken_flt with (φ' := df2) in H9; eauto.
    eapply t_sub; eauto. constructor; intuition. inversion H5. auto.
Qed.

Lemma substitution_gen :
  forall {t Γ φ' Tx dx dx' Σ T d}, dx' ⋒ φ' ≡ dx ->
    forall {φ}, φ ⊑ φ' ->
      has_type (Γ ++ [(Tx,dx)]) φ Σ t T d -> Substq dx dx' ->
        forall {tx}, vtp Σ tx Tx dx' ->
                        has_type ({ 0 |-> dx' }ᴳ Γ) ({ 0 |-> dx' }ᵈ φ) Σ
                                 ({ 0 |-> tx  }ᵗ t)
                                 ({ 0 |-> dx' }ᵀ T)
                                 ({ 0 |-> dx' }ᵈ d).
  Import NatSet.F.
  intros t Γ φ' Tx dx dx' Σ T d Hsep φ Hphi HT HSubst tx HTx. specialize (vtp_closed HTx) as Hclx.
  simpl in Hclx. intuition. remember (Γ ++ [(Tx, dx)]) as Γ'.
  generalize dependent Γ. generalize dependent φ'.
  induction HT; intros; subst; pose (φs := {0 |-> dx' }ᵈ φ); replace ({0 |-> dx' }ᵈ φ) with φs in *; auto.
  - simpl. rewrite NatSetFacts.empty_b. rewrite remove_empty. rewrite unsplice_set_empty.
    apply t_base; auto. eapply closed_qual_subst1'; eauto.
  - simpl. (bdestruct (x =? 0)).
    + (*x is 0 *) rewrite indexr_skips in H0; simpl; auto; try lia. simpl in H0. subst. simpl in H0.
      rewrite mem_singleton. simpl. rewrite remove_singleton_empty. rewrite unsplice_set_empty.
      destruct dx'. repeat rewrite empty_union_left.
      inversion H0. subst. erewrite subst1_ty_id; eauto. inversion HSubst; subst.
      * (*subst fun, dx = dx' *)
        apply vtp_has_type in HTx.
        eapply weaken'; eauto. eapply subst_filter0; eauto.
        eapply closed_qual_subst1'; eauto.
      * (*subst arg, dx = df ⋒ dx = dx' ⋒ φ *)
        apply vtp_has_type in HTx. eapply weaken'; eauto.
        rewrite <- qplus_empty in H3.
        eapply subst_qual_subqual_monotone in H3. erewrite subst1_qual_plus' in H3; eauto.
        eapply closed_qual_subst1'; eauto.
    + (*x is in Γ0*) assert (Hx: 1 <= x); try lia. destruct x; try lia.
      rewrite mem_singleton. simpl. rewrite remove_singleton_inv; auto.
      rewrite unsplice_set_singleton_dec; try lia.
      apply t_var with (d:={0 |-> dx' }ᵈ d). change x with (pred (S x)).
      eapply indexr_subst1; eauto. erewrite subst1_just_fv.
      repeat eapply subst_qual_subqual_monotone. auto.
      eapply closed_qual_subst1'; eauto. simpl. eapply closed_ty_subst1; eauto.
      simpl. eapply closed_qual_subst1; eauto.
  - simpl. intuition. rename H7 into IHHT.
    apply t_abs; auto. eapply closed_tm_subst1'; eauto.
    inversion H3. subst. constructor; try eapply closed_ty_subst1'; eauto; eapply closed_qual_subst1'; eauto.
    eapply closed_qual_subst1'; eauto. apply subst_qual_subqual_monotone. auto.
    (* 1. instantiate the IH *)
    replace (length (Γ0 ++ [(Tx, dx)])) with (S (length Γ0)) in IHHT.
    rewrite subst1_tenv_length. rewrite app_comm_cons in IHHT. rewrite app_comm_cons in IHHT.
    remember (df ⊔ just_fv (S (length Γ0)) ⊔ just_fv (S (S (length Γ0)))) as DF.
    replace ({0 |-> dx' }ᵈ df ⊔ just_fv (length Γ0) ⊔ just_fv (S (length Γ0))) with ({0 |-> dx' }ᵈ DF).
    remember (φ' ⊔ just_fv (S (length Γ0)) ⊔ just_fv (S (S (length Γ0)))) as φ''.
    specialize IHHT with (φ' := φ'') (Γ := (((T1, d1) :: (TFun d1 d2 T1 T2, df) :: Γ0))).
    (* 2. reason about opening and subst, apply IH *)
    unfold open_tm' in *. unfold open_ty' in *. unfold open_ty in *.
    unfold openq' in *. unfold openq in *.
    rewrite app_length in IHHT. rewrite subst1_tenv_length. simpl in *.
    replace (length Γ0 + 1) with (S (length Γ0)) in IHHT; try lia.
    erewrite <- open_subst1_tm_comm in IHHT; eauto. erewrite <- open_subst1_tm_comm in IHHT; eauto.
    erewrite <- open_subst1_ty_comm in IHHT; eauto. erewrite <- open_subst1_ty_comm in IHHT; eauto.
    erewrite <- open_subst1_qual_comm in IHHT; eauto. erewrite <- open_subst1_qual_comm in IHHT; eauto.
    apply IHHT; auto.
    (* done, prove some leftovers *)
    subst. repeat rewrite empty_union_right. eapply qqcap_increase_fresh; eauto.
    subst. destruct df. destruct φ'. destruct φ. simpl in *. intuition; try fnsetdec.
    subst. rewrite subst1_qlub_dist. rewrite subst1_qlub_dist. f_equal.
    repeat rewrite <- subst1_just_fv. auto. rewrite app_length. simpl. lia.
  - intuition. rename H6 into IHHT2. rename H7 into IHHT1. simpl.
    replace ({ 0 |-> dx' }ᵈ (openq df d1 d2)) with
               (openq ({ 0 |-> dx' }ᵈ df) ({ 0 |-> dx' }ᵈ d1) ({ 0 |-> dx' }ᵈ d2)).
      (*separation/overap is preserved after substitution*)
    assert (Hoverlap: {0 |-> dx' }ᵈ (df ⋒ d1) = {0 |-> dx' }ᵈ df ⋒ {0 |-> dx' }ᵈ d1). {
      specialize (has_type_filter HT1). specialize (has_type_filter HT2).
      symmetry. eapply subst1_preserves_separation; eauto. 1,2: eapply subqual_trans; eauto.
    }
    apply t_app with (T1:= { 0 |-> dx' }ᵀ T1) (df:=({0 |-> dx' }ᵈ df)).
    replace (TFun ({0 |-> dx' }ᵈ df ⋒ {0 |-> dx' }ᵈ d1) ({0 |-> dx' }ᵈ d2) ({0 |-> dx' }ᵀ T1) ({0 |-> dx' }ᵀ T2))
            with ({ 0 |-> dx' }ᵀ (TFun (df ⋒ d1) d2 T1 T2)).
    eapply IHHT1; eauto. simpl. f_equal. apply Hoverlap.
    eapply IHHT2; eauto.
    2 : unfold openq; rewrite <- @subst1_qual_empty with (dx:=dx');
        erewrite <- subst1_open_qual_comm; eauto; erewrite <- subst1_open_qual_comm; eauto.
    + eapply closed_ty_subst1'; eauto.
    + apply subst_qual_subqual_monotone. unfold openq in H4. auto.
    + eapply subst1_saturated; eauto.
    + eapply subst1_saturated; eauto.
    + unfold openq. repeat erewrite <- subst1_open_qual_comm; eauto.
  - erewrite @subst1_qual_id with (q:=(just_loc l)); eauto. simpl. erewrite subst1_ty_id; eauto.
    apply t_loc; auto. eapply closed_qual_subst1'; eauto.
    subst φs. destruct φ. destruct dx'. simpl in *. destruct (NatSet.F.mem 0 t0); intuition; fnsetdec.
    constructor; intuition. rewrite bound_empty. lia.
  - replace ({0 |-> dx' }ᵈ ∅) with (∅) in * by auto.
    replace ({0 |-> dx' }ᵀ (TRef TUnit)) with (TRef TUnit) in * by auto.
    replace ({0 |-> dx' }ᵀ (TUnit)) with (TUnit) in * by auto.
    eapply t_ref. fold subst_tm. eapply IHHT; eauto.
  - simpl. rewrite NatSetFacts.empty_b. rewrite remove_empty.
    rewrite unsplice_set_empty.
    apply t_deref with (d := { 0 |-> dx' }ᵈ d). eapply IHHT; eauto.
  - replace ({0 |-> dx' }ᵈ ∅) with (∅) in * by auto.
    replace ({0 |-> dx' }ᵀ (TRef TUnit)) with (TRef TUnit) in * by auto.
    replace ({0 |-> dx' }ᵀ (TUnit)) with (TUnit) in * by auto.
    eapply t_assign; eauto.
  - apply t_sub with (T1:={ 0 |-> dx' }ᵀ T1) (d1:={ 0 |-> dx' }ᵈ d1).
    eapply IHHT; eauto. eapply subst_stp; eauto. apply subst_qual_subqual_monotone; auto.
    Unshelve. all : auto.
Qed.

Lemma substitution : forall {t Tf df Tx dx Σ T d},
    has_type [(Tx,df ⋒ dx) ; (Tf,df)] (df ⋓ just_fv 0 ⋓ just_fv 1) Σ t T d ->
    forall {vf}, vtp Σ vf Tf df ->
        forall {vx}, vtp Σ vx Tx dx ->
                    has_type [] (df ⊔ dx) Σ
                             ({ 0 |-> vf ; vx }ᵗ t)
                             ({ 0 |-> df ; dx }ᵀ T)
                             ({ 0 |-> df ; dx }ᵈ d).
  intros. subst. specialize (vtp_closed H0) as Hclf. specialize (vtp_closed H1) as Hclx.
  intuition. replace ([(Tx, df ⋒ dx); (Tf, df)]) with ([(Tx, df ⋒ dx)] ++ [(Tf, df)]) in H; auto.
  remember (df ⊔ (just_fv 0) ⊔ (just_fv 1)) as DF.
  assert (Hsepf : df ⋒ DF ≡ df). { destruct df. subst. simpl. intuition. }
  assert (Hrefl : DF ⊑ DF). apply subqual_refl.
  eapply (substitution_gen Hsepf Hrefl) in H; eauto.
  replace ({0 |-> df }ᴳ [(Tx, df ⋒ dx)]) with ([] ++ [(Tx, df ⋒ dx)]) in H.
  replace ({0 |-> df }ᵈ DF) with (df ⋓ just_fv 0) in H.
  assert (Hsepf' : dx ⋒ (df ⋓ just_fv 0) ≡ df ⋒ dx). {
    rewrite (@qglb_commute df dx). destruct df. destruct dx. simpl.
    inversion H8. subst. simpl in *. apply bound_0_empty in H14.
    subst. intuition. repeat rewrite inter_empty_left. intuition.
  }
  assert (Hrefl' : (df ⋓ just_fv 0) ⊑ (df ⋓ just_fv 0)). apply subqual_refl.
  eapply (substitution_gen Hsepf' Hrefl') in H; eauto. simpl in H.
  replace ({0 |-> dx }ᵈ (df ⋓ just_fv 0)) with (df ⋓ dx) in H. apply H.
  (*done, prove earlier replacements *)
  rewrite subst1_qlub_dist. rewrite subst1_just_fv0. erewrite subst1_qual_id; eauto.
  subst. repeat rewrite subst1_qlub_dist. rewrite subst1_just_fv0. rewrite <- subst1_just_fv.
  erewrite subst1_qual_id; eauto. rewrite qlub_assoc. rewrite qlub_idem. auto.
  simpl. erewrite subst1_qual_id; eauto. erewrite subst1_ty_id; eauto.
  apply closed_qual_qqcap; eauto.
Qed.

Lemma open_qual_mono : forall {d1 d1' d2 k}, d1 ⊑ d1' -> ([[ k ~> d1 ]]ᵈ d2) ⊑ ([[ k ~> d1' ]]ᵈ d2).
  intros. destruct d2; destruct d1'; destruct d1. simpl.
  inversion H. intuition.
  destruct (NatSet.F.mem k t1) eqn:Hmem.
  simpl. intuition; fnsetdec.
  constructor; fnsetdec.
Qed.

Lemma open_qual_mono2 : forall {d1 d2 d2' k}, d2 ⊑ d2' -> ([[ k ~> d1 ]]ᵈ d2) ⊑ ([[ k ~> d1 ]]ᵈ d2').
  intros. destruct d2; destruct d2'; destruct d1; simpl; intuition.
  inversion H. intuition. destruct (NatSet.F.mem k t1) eqn: Hmem1.
  destruct (NatSet.F.mem k t4) eqn: Hmem2. simpl. intuition; fnsetdec.
  specialize (@subset_inclusion _ _ _ H2 Hmem1 Hmem2) as F. inversion F.
  destruct (NatSet.F.mem k t4) eqn: Hmem2. simpl. intuition; try fnsetdec.
  apply subset_union_remove; auto. auto.
Qed.

Lemma openq_mono : forall {d1 d1' d2 d2' d3 d3' f l},
    closed_qual 0 f l d1' -> closed_qual 0 f l d2' ->
    d1 ⊑ d1' -> d2 ⊑ d2' -> d3 ⊑ d3' -> (openq d1 d2 d3) ⊑ (openq d1' d2' d3').
  intros. unfold openq.
  specialize (@open_qual_mono d1 d1' d3' 0 H1) as S1.
  specialize (@open_qual_mono2 d1 d3 d3' 0 H3) as S2.
  specialize (subqual_trans S2 S1) as S3. clear S1. clear S2.
  specialize (@open_qual_mono2 d2' _ _ 1 S3) as S4.
  eapply subqual_trans. 2: eauto. eapply open_qual_mono; eauto.
Qed.

Lemma openq_qstp_monotone : forall {Γ Σ d1 d1' d2 d2' d3 d3'},
    qstp Γ Σ d1 d1' -> qstp Γ Σ d2 d2' -> qstp Γ Σ d3 d3' -> qstp Γ Σ (openq d1 d2 d3) (openq d1' d2' d3').
  intros. inversion H; subst. inversion H0; subst. inversion H1; subst. constructor.
  eapply openq_mono; eauto.
  unfold openq. erewrite open_qual_commute'' with (i:=1); eauto.
  repeat eapply closed_qual_open'; eauto. eapply closed_qual_monotone; eauto.
Qed.

Lemma openq'_subqual : forall {A: Type} {Γ : list A} {d1 d2},
    (openq' Γ d1) ⊑ (openq' Γ (d1 ⋓ d2)).
  intros. unfold openq'. eapply @openq_mono with (f:=(S (S (length Γ)))) (l:=0).
  constructor; intuition. simpl. rewrite bound_singleton. lia.
  rewrite bound_empty. lia. rewrite bound_empty. lia.
  constructor; intuition. simpl. rewrite bound_singleton. lia.
  rewrite bound_empty. lia. rewrite bound_empty. lia.
  apply subqual_refl. apply subqual_refl. apply qqplus_gt.
Qed.

Lemma open_ty'_closed : forall {l} {T},
    closed_ty 0 0 l T ->
    closed_ty 0 2 l (open_ty' (@nil (ty * qual)) T).
  intros. unfold open_ty'. unfold open_ty.
  apply closed_ty_open_succ. auto. apply closed_ty_open_succ. auto.
Qed.

Lemma open_qual_qlub_dist : forall {k d1 d2 d3}, ([[ k ~> d1  ]]ᵈ (d2 ⊔ d3)) = (([[ k ~> d1  ]]ᵈ d2) ⊔ ([[ k ~> d1  ]]ᵈ d3)).
  intros. destruct d2; destruct d3; destruct d1; simpl; auto.
  destruct (NatSet.F.mem k t1) eqn: Hmem1.
  - rewrite NatSet.F.mem_1. 2: apply NatSet.F.union_2; apply NatSet.F.mem_2; auto.
    destruct (NatSet.F.mem k t4) eqn: Hmem2.
    simpl. f_equal; fnsetdec. simpl. f_equal. fnsetdec.
    rewrite remove_union_dist; try fnsetdec. rewrite (@remove_not_in k t4); auto. fnsetdec. fnsetdec.
  - destruct (NatSet.F.mem k t4) eqn: Hmem2.
    rewrite NatSet.F.mem_1. 2: apply NatSet.F.union_3; apply NatSet.F.mem_2; auto.
    simpl. f_equal; try fnsetdec.
    rewrite remove_union_dist. rewrite (@remove_not_in k t1); auto. fnsetdec.
    rewrite not_member_union; auto.
Qed.

Lemma open_qual_qqplus_dist : forall {k d1 d2 d3}, ([[ k ~> d1  ]]ᵈ (d2 ⋓ d3)) = (([[ k ~> d1  ]]ᵈ d2) ⋓ ([[ k ~> d1  ]]ᵈ d3)).
  intros. destruct d2.
  rewrite open_qual_qlub_dist. simpl. destruct d1; auto.
Qed.

Lemma openq_u_distribute: forall {df d1 d2 d3 : qual}, openq df d1 (d2 ⋓ d3) = (openq df d1 d2 ⋓ openq df d1 d3).
  intros. unfold openq. repeat rewrite open_qual_qqplus_dist. auto.
Qed.

Lemma openq_just_fv_id: forall {df d1 : qual} {x}, openq df d1 (just_fv x) = just_fv x.
  intros. unfold openq. simpl. destruct df. destruct d1.
  rewrite NatSetFacts.empty_b. simpl. rewrite NatSetFacts.empty_b. auto.
Qed.

Lemma openq_just_bv0: forall {df d1 : qual} {f l}, closed_qual 0 f l df -> openq df d1 (just_bv 0) = df.
  intros. inversion H. subst. apply bound_0_empty in H1. subst.
  unfold openq. simpl. destruct d1. rewrite mem_singleton. simpl.
  rewrite remove_singleton_empty. repeat rewrite empty_union_left.
  rewrite NatSetFacts.empty_b. auto.
Qed.

Lemma openq_just_bv1: forall {df d1 : qual}, openq df d1 (just_bv 1) = d1.
  intros. unfold openq. simpl. destruct d1. destruct df. rewrite mem_singleton.
  simpl. rewrite mem_singleton. simpl. qdec.
Qed.

Lemma open_qual_just_bv_skip: forall {i j d}, j <> i -> [[ j ~> d ]]ᵈ (just_bv i) = (just_bv i).
  intros. simpl. destruct d. rewrite mem_singleton. rewrite <- Nat.eqb_neq in H.
  rewrite H. auto.
Qed.

Lemma open_qual_just_bv: forall {i d}, [[ i ~> d ]]ᵈ (just_bv i) = d.
  intros. simpl. destruct d. rewrite mem_singleton. rewrite Nat.eqb_refl. qdec.
Qed.

Lemma openq_u_distribute1 : forall {df d1 d2 l},
    openq df d1 (d2 ⋓ (just_loc l)) = ((openq df d1 d2) ⋓ (just_loc l)).
  intros. unfold openq. repeat rewrite open_qual_qqplus_dist. f_equal.
  simpl. destruct df; simpl; destruct d1; simpl; auto.
  rewrite NatSetFacts.empty_b. simpl.
  rewrite NatSetFacts.empty_b. simpl. auto.
Qed.

Lemma openq_u_distribute2 : forall {df d1 d2 l},
    openq df d1 (d2 ⋓ (just_loc l)) = openq (df ⋓ (just_loc l)) d1 (d2 ⋓ (just_loc l)).
  intros. unfold openq. f_equal.
  destruct d2; simpl; auto. repeat rewrite listlub_empty_right.
  destruct df; simpl; auto. repeat rewrite empty_union_right.
  destruct (NatSet.F.mem 0 t1) eqn:Hmem. f_equal. fnsetdec. auto.
Qed.

Lemma openq_u_distribute3 : forall {df d1 d2 l},
    openq (df ⋓ (just_loc l)) d1 (d2 ⋓ (just_loc l)) = ((openq df d1 d2) ⋓ (just_loc l)).
  intros. rewrite <- openq_u_distribute2. rewrite openq_u_distribute1. auto.
Qed.

Lemma openq_duplicate_eq : forall {df d1 d2 l},
    (((openq df (d1 ⋓ (just_loc l)) d2) ⋓ (just_loc l)) = ((openq df d1 d2) ⋓ (just_loc l))).
  intros. unfold openq. destruct d2; simpl. auto. destruct d1; simpl. auto.
  repeat rewrite empty_union_right. destruct df; simpl.
  destruct (NatSet.F.mem 0 t1) eqn: Hmem1.
  - simpl. destruct (NatSet.F.mem 1 (NatSet.F.union (NatSet.F.remove 0 t1) t7)) eqn: Hmem2.
    + simpl. f_equal; fnsetdec.
    + simpl. f_equal; fnsetdec.
  - simpl. destruct (NatSet.F.mem 1 t1) eqn: Hmem2.
    + simpl. f_equal; fnsetdec.
    + simpl. f_equal; fnsetdec.
Qed.

Lemma openq_closed : forall {a b c f l},
    closed_qual 2 f l c -> closed_qual 0 f l a -> closed_qual 0 f l b -> closed_qual 0 f l (openq a b c).
  intros. unfold openq. erewrite open_qual_commute''; eauto.
  repeat eapply closed_qual_open'; eauto.
Qed.

Lemma qqcap_fresh_r : forall {d1 df f l},
    closed_qual 0 f l d1 -> closed_qual 0 f l df -> forall {l'}, l <= l' -> d1 ⋒ df = d1 ⋒ (df ⋓ (just_loc l')).
  intros. inversion H; subst; inversion H0; subst; simpl; auto.
  repeat rewrite empty_union_right. f_equal.
  eapply disjoint_glb_lub_eq; eauto. lia.
Qed.

Lemma qqcap_fresh_l : forall {d1 df f l},
    closed_qual 0 f l d1 -> closed_qual 0 f l df -> forall {l'}, l <= l' -> d1 ⋒ df = (d1 ⋓ just_loc l') ⋒ df.
  intros. rewrite qqcap_commute. erewrite qqcap_fresh_r; eauto.
  rewrite qqcap_commute. auto.
Qed.

Lemma freshness : forall {Σ Σ' l b f d1}, disjointq Σ Σ' (just_loc l) -> closed_qual b f (length Σ) d1 -> just_loc l ⋒ d1 = ∅.
  intros. inversion H; subst. unfold just_loc in H1.
  inversion H1. apply singleton_nonempty in H3. contradiction.
  inversion H3. apply singleton_injective in H5. subst. inversion H0. subst.
  unfold just_loc. simpl. repeat rewrite inter_empty_left. f_equal.
  assert (Hcontra : bound ls <= l0). lia. apply bound_le_mem_false in Hcontra.
  rewrite <- NatSetFacts.not_mem_iff in Hcontra. fnsetdec.
Qed.

Lemma just_loc_ldom : forall {l} {Σ : senv}, l < length Σ -> just_loc l ⊑ ldom Σ.
  intros. unfold ldom. unfold dom. simpl. intuition. specialize (lt_mem_nset H).
  intros. fnsetdec.
Qed.

Lemma stp_subqual: forall {Γ Σ T1 d1 T2 d2},
    stp Γ Σ T1 d1 T2 d2 -> d1 ⊑ d2.
Proof.
  intros. induction H; inversion H; intuition; subst.
  - inversion H1. intuition.
  - eapply subqual_trans; eauto.
  - eapply subqual_trans; eauto.
  - eapply subqual_trans; eauto.
  - eapply subqual_trans; eauto.
Qed.

(* well-typed values belonging to each type *)

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
  induction H; intuition; try discriminate; inversion H0; subst. exists t0. intuition.
Qed.

(* Main results: type soundness & preservation of separation *)

Theorem type_safety: forall {Σ t T d},
  has_type [] (ldom Σ) Σ t T d ->
    value t \/
    forall {σ} , CtxOK [] (ldom Σ) Σ σ ->
    exists t' σ', step t σ t' σ' /\ preserve [] Σ t' T d σ'.
Proof.
  intros Σ t T d H.
  specialize (has_type_closed H) as HX. remember [] as G. remember t as tt. remember T as TT. remember (ldom Σ) as φ.
  revert T t HeqTT Heqtt HeqG Heqφ.
  induction H; try (left; constructor); intros.
  - (* tvar *) subst. inversion H.
  - (* tapp *) right. subst. intuition.
    apply has_type_closed in H as HH. intuition. apply has_type_closed in H0 as HH0. intuition.
    (* t1 *) specialize (H8 (TFun (df ⋒ d1) d2 T1 T) t1).  intuition.
    (* t2 *) specialize (H10 T1 t2). intuition.
    + (* beta *)
      (* turn has_type to vtp *)
      apply has_type_vtp in H as VH; intuition.
      pose (VHH := VH). inversion VH. subst.
      specialize (has_type_filter H0) as Hflt0.
      apply has_type_vtp in H0 as VH0; intuition.
      exists (open_tm (tabs t0) t2 t0). exists σ. intuition.
      * constructor. intuition.
      * apply (Preserve Σ ∅); auto.  rewrite qqplus_qbot_right_neutral.
        apply qstp_closed in H33 as H33'; intuition.
        change (length []) with 0 in *. subst.
        pose (VH' := H30). eapply t_abs with (φ:=df1) in VH'; eauto. apply has_type_vtp in VH'.
        assert (Hst : stp [] Σ T1 (df1 ⋒ d1) T1 (df ⋒ d1)). { apply stp_refl; auto. constructor. apply subqual_qglb_r.
          inversion H33. subst. auto. apply closed_qual_qqcap; auto. }
        assert (HT' : has_type [(T1, df1 ⋒ d1) ; (TFun d0 d3 T0 T2, df1)] (df1 ⊔ just_fv 0 ⊔ just_fv 1) Σ (open_tm' ([]:tenv) t0) (open_ty' ([]:tenv) T2) (openq' ([]:tenv) d3)). {
          assert (Hst' : stp [] Σ T1 (df1 ⋒ d1) T0 d0). eapply s_trans; eauto.
          eapply narrowing; eauto. eapply weaken_stp; eauto. apply saturated_cons; auto.
          apply saturated_empty_tenv. apply stp_closed in H32. intuition.
        }
        eapply @substitution with ( vx:= t2) in HT' as HT''; eauto; intuition.
        unfold open_tm' in HT''. unfold open_ty' in HT''. unfold openq' in HT''. simpl in HT''. inversion H26; subst.
        unfold open_ty in HT''. unfold openq in HT''.
        erewrite <- open_subst2_tm in HT''; eauto.
        erewrite <- open_subst2_ty in HT''; eauto.
        erewrite <- open_subst2_qual in HT''; eauto.
        fold (open_tm (tabs t0) t2 t0) in HT''. fold (openq df1 d1 d3) in HT''.
        apply @weaken_flt with (φ':= (ldom Σ)) in HT''; auto; intuition.
        eapply t_sub; eauto.
        inversion H27. subst. clear H40.
        assert (Hsub : stp [(T1, df1 ⋒ d1); (TFun d0 d3 T0 T2, df1)] Σ (open_ty' ([] : tenv) T2) (openq' ([] : tenv) d3) (open_ty' ([] : tenv) T) (openq' ([] : tenv) d2)). {
          eapply narrowing_stp; eauto. eapply weaken_stp; eauto.
        }
        eapply substitution_stp in Hsub; eauto.
        replace (open_ty' ([] : tenv) T) with T in *. (* because T is closed *)
        simpl in Hsub. unfold openq' in Hsub. unfold openq in Hsub. simpl in Hsub.
        erewrite @subst1_ty_id with (T := T) in Hsub; eauto.
        erewrite @subst1_ty_id with (T := T) in Hsub; eauto.
        unfold open_ty' in Hsub. unfold open_ty in Hsub.
        erewrite <- open_subst2_ty in Hsub; eauto.
        erewrite <- open_subst2_qual in Hsub; eauto.
        erewrite <- open_subst2_qual in Hsub; eauto.
        fold (openq df1 d1 d3) in Hsub. fold (openq df1 d1 d2) in Hsub.
        eapply s_trans; eauto. apply stp_refl; auto. constructor.
        eapply openq_mono; eauto. inversion H33. auto. apply openq_closed; auto.
        unfold open_ty'. unfold open_ty. repeat erewrite closed_ty_open_id; eauto.
        eapply openq_subqual; eauto. apply has_type_filter in H. auto.
        apply qlub_bound; auto. apply has_type_filter in H. inversion H33. subst.
        eapply subqual_trans; eauto. inversion H27. auto. inversion H27. auto. auto.
    + (* (tabs t) t2 -> (tabs t) t2' *)
      apply has_type_vtp in H as VH; intuition.
      apply vtp_canonical_form_lam in VH as HH; intuition.
      pose (HH11 := H11).
      unfold CtxOK in HH11. specialize (H8 σ). intuition.
      destruct H22 as [t2' [σ' HH22]]. exists (tapp t1 t2'). exists σ'. intuition. constructor; intuition.
      destruct H22.  apply (Preserve Σ' d'); intuition.
      inversion H24; subst.
      * rewrite qqplus_qbot_right_neutral. rewrite qqplus_qbot_right_neutral in H25. eapply t_app with (df := df); eauto.
        eapply weaken_flt. eapply weaken_store; eauto; intuition. apply extends_ldom. all : auto.
        eapply closed_ty_monotone; eauto. apply extends_length. intuition.
        eapply subqual_trans; eauto; apply extends_ldom; auto.
        all : eapply weaken_store_saturated; eauto.

      * specialize (has_type_closed H). specialize (has_type_closed H25). intuition. inversion H33. subst. rewrite <- openq_duplicate_eq.
        apply t_sub with (T1 := T) (d1 := (openq df (d1 ⋓ (just_loc l)) d2)).
        -- eapply t_app with (T1 := T1) (df:=df); eauto.  erewrite <- qqcap_fresh_r; eauto. eapply weaken_flt. eapply weaken_store; eauto.
           apply extends_ldom. auto. simpl. auto.
           simpl. eapply closed_ty_monotone in H1; eauto. apply extends_length. auto.
           eapply subqual_trans; eauto; apply extends_ldom; auto. eapply weaken_store_saturated; eauto.
        -- apply stp_refl. simpl. eapply closed_ty_monotone in H1; eauto. apply extends_length. auto.
           constructor. apply qqplus_gt. apply closed_qual_qqplus; auto.
           eapply openq_closed; eauto; try solve [eapply closed_qual_monotone; eauto; apply extends_length; auto].
           constructor; auto; try rewrite bound_empty; try rewrite bound_singleton; try lia.
        -- apply has_type_filter in H0. apply has_type_filter in H. apply qqplus_bound. eapply openq_subqual; eauto.
           2: apply qqplus_bound. 1, 2, 4 : eapply subqual_trans; eauto; apply extends_ldom; auto.
           all : apply just_loc_ldom; auto.
    + (* t t2 -> t' t2  *)
      apply has_type_closed in H0 as Hcl. intuition.
      specialize (H19 σ H11). destruct H19 as [t1' [σ' HH6]]. exists (tapp t1' t2). exists σ'. intuition. apply step_c_app_l. intuition.
      destruct H23. apply (Preserve Σ' d'); intuition. inversion H26; subst.
      * rewrite qqplus_qbot_right_neutral. rewrite qqplus_qbot_right_neutral in H27. eapply t_app; eauto.
        eapply weaken_flt. eapply weaken_store; eauto. apply extends_ldom. auto. simpl. auto.
        eapply closed_ty_monotone; eauto. apply extends_length. auto.
        eapply subqual_trans; eauto; apply extends_ldom; auto.
        all : eapply weaken_store_saturated; eauto.
      * rewrite <- openq_u_distribute3. eapply t_sub with (T1 := T)(d1 := (openq (df ⋓ just_loc l) d1 d2)).
        -- eapply t_app with (df:=(df ⋓ just_loc l)); eauto. erewrite <- qqcap_fresh_l; eauto.
           eapply weaken_flt. eapply weaken_store. eauto. auto. apply extends_ldom; auto.
           auto. simpl. eapply closed_ty_monotone; eauto. apply extends_length; auto.
           eapply subqual_trans; eauto. apply extends_ldom; auto. eapply weaken_store_saturated; eauto.
           apply saturated_qqplus. eapply weaken_store_saturated; eauto. apply saturated_just_loc.
        -- apply stp_refl. simpl. eapply closed_ty_monotone; eauto. lia.
           constructor. eapply @openq_mono with (f:=0) (l:=(length Σ')); eauto. apply closed_qual_qqplus; auto.
           1,3 : eapply closed_qual_monotone; eauto; lia. apply just_loc_closed. auto.
           inversion H13; subst. apply openq_closed. 1,2 : apply closed_qual_qqplus.
           2,4 : apply just_loc_closed; auto. all : eapply closed_qual_monotone; eauto; try lia.
        -- apply has_type_filter in H0. apply has_type_filter in H. eapply openq_subqual; eauto. apply qqplus_bound.
           1,3 : eapply subqual_trans; eauto; apply extends_ldom; auto. apply just_loc_ldom. auto.
           rewrite openq_u_distribute1. apply qqplus_bound. eapply subqual_trans; eauto. apply extends_ldom. auto.
           apply just_loc_ldom. auto.
  - (* tref *) subst. intuition. specialize (has_type_closed H) as HH. intuition. specialize (H3 TUnit t0). intuition.
    + (* contraction *) right. intros.
      exists (tloc (length (σ))). exists (t0 :: σ). intuition.
      econstructor; eauto. apply (Preserve (TUnit :: Σ) (just_loc (length σ))). apply extends_cons. eapply CtxOK_weaken_flt.
      apply CtxOK_ext; auto. apply H3.
      pose (HV := H). apply has_type_vtp in HV; intuition. inversion HV; subst. constructor. auto.
      simpl. econstructor; eauto; try rewrite bound_empty; try lia.
      rewrite bound_dom. simpl. lia. simpl. intuition; try fnsetdec.
      unfold dom. simpl. fnsetdec.
      apply (disj_loc (length σ)); auto.
      1,2: unfold CtxOK in H3; simpl; intuition.
      replace (∅ ⋓ just_loc (length σ)) with (just_loc (length σ)).
      eapply t_loc; eauto. inversion H3. rewrite <- H10.
      apply indexr_head. simpl. intuition; try fnsetdec.
      unfold dom. simpl. inversion H3. rewrite H10. fnsetdec.
      simpl. unfold just_loc. f_equal; try fnsetdec.
    + (* congruence *) right. intros. specialize (H8 σ H3). destruct H8 as [t' [σ' HH8]]. exists (tref t'). exists σ'. intuition. econstructor; eauto.
      destruct H10. apply (Preserve Σ' ∅); intuition. simpl. rewrite empty_union_left. eapply t_ref; eauto.
  - (* tderef *) subst. intuition. specialize (has_type_closed H) as HH. intuition. specialize (H3 (TRef T0) t0). intuition.
    + (* contraction *) right. intros. pose (HV := H). apply has_type_vtp in HV; intuition.
      specialize (vtp_canonical_form_loc HV) as Hcan. intuition. destruct H10 as [l HH10]. subst.
      pose (HHV := HV). inversion HHV. subst. pose (HH3 := H3). destruct HH3. subst.
      pose (HH14 := H14). apply indexr_var_some' in HH14. rewrite H10 in HH14. apply indexr_var_some in HH14.
      destruct HH14 as [v HHH14].  exists v. exists σ. intuition. apply step_deref; intuition.
      apply (Preserve Σ ∅); intuition.
      simpl. rewrite empty_union_left.  apply t_sub with (T1 := T)(d1:= ∅); auto.
      specialize (H11 l v T). intuition.
      replace Σ with (Σ ++ []); intuition. eapply weaken_stp_store. auto.
    + (* congruence *) right. intros. specialize (H8 σ H3).
      destruct H8 as [t' [σ' HH8]]. exists (tderef t'). exists σ'. intuition. constructor; auto.
      destruct H10. apply (Preserve Σ' ∅); intuition. simpl. rewrite empty_union_left. eapply t_deref; eauto.
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
      inversion H7. inversion H6. subst. intuition.
      econstructor; eauto. lia. apply (Preserve Σ ∅); auto.
      eapply CtxOK_update; eauto. lia. apply t_sub with (T1:=TUnit) (d1:=∅); auto.
      replace Σ with (Σ ++ []); intuition. eapply weaken_stp_store. auto.
      simpl. rewrite empty_union_left. auto.
    + (* right congruence *)
      right. intros. specialize (H4 σ H6). destruct H4 as [t' [σ' H4']].
      exists (tassign t1 t'). exists σ'. intuition. econstructor; eauto.
      pose (HV := Ht1). apply has_type_vtp in HV; intuition. inversion HV; subst.
      destruct H14. apply (Preserve Σ' ∅); eauto. simpl. rewrite empty_union_left.
      eapply t_assign; eauto.
      assert (ldom Σ ⊑ ldom Σ'). apply extends_ldom. auto.
      eapply weaken_store in Ht1; eauto. eapply weaken_flt in Ht1; eauto.
    + (* left congruence *)
      right. intros. specialize (H12 σ H4). destruct H12 as [t' [σ' H12']].
      exists (tassign t' t2). exists σ'. intuition. econstructor; eauto.
      destruct H14. apply (Preserve Σ' ∅); eauto. simpl. rewrite empty_union_left.
      eapply t_assign; eauto. eapply weaken_store in Ht2; eauto. eapply weaken_flt; eauto. apply extends_ldom; auto.
  - (* subsumption *) subst. intuition. specialize (stp_closed H0) as H00. intuition.
    specialize (H5 T1 t0). intuition. right.
    intros. specialize (H10 σ H5). destruct H10 as [t' [σ' HH8]]. exists t'. exists σ'. intuition.
    destruct H12. apply (Preserve Σ' d'); intuition. eapply t_sub; eauto. apply stp_scale_qqplus.
    eapply weaken_stp_store_ext; eauto. inversion H14; subst; intuition; constructor; intuition; try rewrite bound_singleton; try rewrite bound_empty; try lia; auto.
    apply qqplus_bound. eapply subqual_trans; eauto. apply extends_ldom; auto. inversion H14; subst; auto.
    apply just_loc_ldom; auto.
Qed.

Lemma step_deterministic: deterministic step.
Proof.
  unfold deterministic. intros t t1 t2 σ σ1 σ2 Hstep1 Hstep2. generalize dependent σ2. generalize dependent t2.
  induction Hstep1; intros.
  - assert (step (tapp (tabs t0) v) σ (open_tm (tabs t0) v t0) σ). { constructor; intuition. }
    inversion Hstep2; subst. intuition.
    + inversion H6 .
    + inversion H7; subst; inversion H.
  - inversion Hstep2; subst. intuition. inversion H1; subst; inversion H.
  - inversion Hstep2; subst.
    + rewrite H in H1. inversion H1. intuition.
    + inversion H1.
  - inversion Hstep2; subst; intuition.
    + inversion H6;  subst; intuition.
    + inversion H0; subst; inversion H6.
    + inversion H7; subst;  inversion H0.
    + inversion H7; subst; inversion H0.
  - inversion Hstep2; subst; intuition.
    + inversion H0; subst; try inversion Hstep1.
    + inversion Hstep1; subst; inversion H0.
    + specialize (IHHstep1 t'0  σ2). intuition. subst. intuition.
    + specialize (IHHstep1 t'0  σ2). intuition.
  - inversion Hstep2; subst; intuition.
    + inversion Hstep1.
    + inversion Hstep1.
    + specialize (IHHstep1 t'0  σ2). intuition. subst. intuition.
    + specialize (IHHstep1 t'0  σ2). intuition.
  - inversion Hstep2; subst; intuition.
    + inversion Hstep1.
    + inversion Hstep1.
    + specialize (IHHstep1 t1'0 σ2). intuition. subst. intuition.
    + specialize (IHHstep1 t1'0 σ2). intuition.
    + inversion Hstep1; subst; inversion H1.
    + inversion Hstep1; subst; inversion H1.
  - inversion Hstep2; subst.
    + inversion Hstep1; subst; inversion H5.
    + inversion H5; subst; inversion H.
    + specialize (IHHstep1 t2'0  σ2). intuition. subst. intuition.
  - inversion Hstep2; subst.
    + inversion Hstep1.
    + specialize (IHHstep1 t1'0  σ2). intuition. subst. intuition.
    + inversion Hstep1; subst; inversion H1.
  - inversion Hstep2; subst.
    + inversion Hstep1; subst; inversion H6.
    + inversion H5; subst; inversion H.
    + specialize (IHHstep1 t2'0  σ2). intuition. subst. intuition.
Qed.

Lemma progress : forall {Σ t T d},
    has_type [] (ldom Σ) Σ t T d ->
    value t \/ forall {σ}, CtxOK [] (ldom Σ) Σ σ -> exists t' σ', step t σ t' σ'.
Proof.
  intros Σ t T d HT.
  specialize (type_safety HT). intuition. right. intros σ HCtxOK.
  specialize (H0 σ HCtxOK). destruct H0 as [t' [σ' [Hstep  HPreserve]]].
  exists t'. exists σ'. intuition.
Qed.

Lemma preservation : forall {Σ t T d},
    has_type [] (ldom Σ) Σ t T d ->
    forall{σ}, CtxOK [] (ldom Σ) Σ σ ->
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
  has_type [] (ldom Σ) Σ t1 T1 q1 ->
  has_type [] (ldom Σ) Σ t2 T2 q2 -> q1 ⊓ q2 ⊑ ∅ ->
    forall{σ}, CtxOK [] (ldom Σ) Σ σ ->
      forall {t1' σ'}, step t1 σ t1' σ' ->
      forall {t2' σ''}, step t2 σ' t2' σ'' -> separate Σ t1' T1 t2' T2.
  intros Σ t1 T1 q1 t2 T2 q2 HT1 HT2 Hsep σ HOK t1' σ' Hstep1 t2' σ'' Hstep2.
  (* execute preservation in sequence *)
  specialize (preservation HT1 HOK Hstep1) as P1. destruct P1 as [Σ' d1 Hext1 HOK' Hdisj1 HT1'].
  assert (HT2': has_type [] (ldom Σ') Σ' t2 T2 q2). {
    eapply weaken_flt. eapply weaken_store. eauto. auto. apply extends_ldom; auto. auto.
  }
  specialize (preservation HT2' HOK' Hstep2) as P2. destruct P2 as [Σ'' d2 Hext2 HOK'' Hdisj2 HT2''].
  apply (Separate Σ' Σ'' (q1 ⋓ d1) (q2 ⋓ d2) Hext1 Hext2 HT1' HT2'').
  (* now we just need to show that the disjointness is preserved. this is intuitively true from the disjointness
     of the heap effects d1 and d2. *)
  inversion Hdisj1; inversion Hdisj2; subst. 1-3 : repeat rewrite qqplus_qbot_right_neutral; auto.
  - rewrite qglb_qlub_dist_l. rewrite (@qglb_commute q1 (just_loc l)). erewrite freshness; eauto.
    rewrite qlub_empty_right. auto. apply has_type_closed in HT1. intuition. eapply closed_qual_monotone; eauto.
    apply extends_length. auto.
  - rewrite qglb_qlub_dist_r. erewrite freshness; eauto. rewrite qlub_empty_right. auto.
    apply has_type_closed in HT2. intuition. eapply closed_qual_monotone; eauto.
  - rewrite qglb_qlub_dist_l. rewrite qglb_qlub_dist_r. rewrite qglb_qlub_dist_r.
    erewrite freshness; eauto. rewrite (@qglb_commute (just_loc l) (just_loc l0)).
    erewrite @freshness with (Σ := Σ'); eauto. repeat rewrite qlub_empty_right.
    rewrite (@qglb_commute q1 (just_loc l0)). erewrite freshness; eauto. rewrite qlub_empty_right. auto.
    apply has_type_closed in HT1. 3 : apply has_type_closed in HT2. 1,3: intuition; eapply closed_qual_monotone; eauto;
    apply extends_length; auto. apply just_loc_closed. auto.
    Unshelve. all : auto.
Qed.
