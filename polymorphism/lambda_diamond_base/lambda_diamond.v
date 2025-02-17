Require Export PeanoNat.
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

(* Import the most relevant definitions from NatSet.F. A full import pollutes the namespace, affecting name generation.*)
Module NatSetView.
  Import NatSet.
  Export F(singleton,mem,inter,union,remove,In,max_elt,Subset,Equal,is_empty,Empty).
  Notation "s [=] t" := (Equal s t) (at level 70, no associativity).
  Notation "s [<=] t" := (Subset s t) (at level 70, no associativity).
End NatSetView.
Import NatSetView.

(* Definitions *)

(* ### Syntax ### *)
(* We represent terms and types in locally nameless style. *)
Inductive ty : Type :=
| TUnit : ty
| TFun  : qual -> qual -> ty -> ty -> ty
| TRef  : qual -> ty -> ty
.

Inductive tm : Type :=
| tunit   : tm
| tvar    : var -> tm
| tabs    : tm  -> tm (* convention: #0: self-ref, #1: argument *)
| tapp    : tm  -> tm -> tm
| tloc    : loc -> tm
| tref    : tm  -> tm
| tderef  : tm  -> tm
| tassign : tm  -> tm -> tm
.
Notation "& l"   := (tloc l) (at level 0, right associativity).
Notation "! t"   := (tderef t) (at level 0, right associativity).
Coercion tvar : var >-> tm. (* lightens the notation of term variables *)

Definition tenv := list (bool * ty * qual). (* (isFunctionSelfRef, Type, Qual) *)
Definition senv := list (ty * qual). (* Sigma store typing *)

Definition extends {A} (l1 l2 : list A): Prop := exists l', l1 = l' ++ l2.
Notation "x ⊇ y" := (extends x y) (at level 75). (* \supseteq*)

Notation "‖ x ‖" := (length x) (at level 10). (* \Vert *)

(* Opening a term *)
Fixpoint open_rec_tm (k : nat) (u : tm) (t : tm) {struct t} : tm :=
  match t with
  | tunit            => tunit
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
Definition open_tm' {A : Type} (env : list A) t := open_rec_tm 1 $(S (‖ env ‖)) (open_rec_tm 0 ($‖env‖) t).

(* Opening a qualifier *)
Definition open_qual (k : nat) (q' : qual) (q : qual) : qual :=
  match q with
  | qset fresh1 vs bs ls =>
    match mem k bs with
    | true => (qset fresh1 vs (remove k bs) ls) ⊔ q'
    | _    => qset fresh1 vs bs ls
    end
  end.
Definition openq (u u' q : qual) : qual := open_qual 1 u' (open_qual 0 u q).
Definition openq' {A} (env : list A) q  := openq ($!‖env‖) $!(S (‖env‖)) q.

(* Opening a type with a qualifier *)
Fixpoint open_rec_ty (k : nat) (d' : qual) (T : ty) : ty :=
  match T with
  | TUnit            => TUnit
  | TFun d1 d2 T1 T2 => TFun (open_qual k d' d1) (open_qual (S (S k)) d' d2) (open_rec_ty k d' T1) (open_rec_ty (S (S k)) d' T2)
  | TRef d1 T        => TRef (open_qual k d' d1) (open_rec_ty k d' T)
  end.
Definition open_ty (u u' : qual) (T : ty) := (open_rec_ty 1 u' (open_rec_ty 0 u T)).
Definition open_ty' {A : Type} (env : list A) (T : ty) := open_ty $!(‖env‖) $!(S (‖env‖)) T.

Module OpeningNotations.
  Declare Scope opening.
  Notation "[[ k ~> u ]]ᵗ t"  := (open_rec_tm k u t) (at level 10) : opening.
  Notation "[[ k ~> U ]]ᵀ T"  := (open_rec_ty k U T) (at level 10) : opening.
  Notation "[[ k ~> q' ]]ᵈ q" := (open_qual k q' q) (at level 10) : opening.
  Notation "t <~ᵗ q ; q'"     := (open_tm q q' t) (at level 10, q at next level) : opening.
  Notation "T <~ᵀ q ; q'"     := (open_ty q q' T) (at level 10, q at next level) : opening.
  Notation "q <~ᵈ q' ; q''"   := (openq q' q'' q) (at level 10, q' at next level) : opening.
  Notation "t <~²ᵗ g"         := (open_tm' g t) (at level 10) : opening.
  Notation "T <~²ᵀ g"         := (open_ty' g T) (at level 10) : opening.
  Notation "q <~²ᵈ g"         := (openq' g q) (at level 10) : opening.
End OpeningNotations.
Import OpeningNotations.
Local Open Scope opening.

(* measure for induction over types *)
Fixpoint ty_size (T : ty) : nat :=
  match T with
  | TUnit           => 0
  | TFun  _ _ T1 T2 => S (ty_size T1 + ty_size T2)
  | TRef  _ T       => S (ty_size T)
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
  | qset fresh vs bs ls => qset fresh (splice_set n vs) bs ls
  end.

Fixpoint splice_ty (n : nat) (T : ty) {struct T} : ty :=
  match T with
  | TUnit            => TUnit
  | TFun d1 d2 T1 T2 => TFun (splice_qual n d1) (splice_qual n d2) (splice_ty n T1) (splice_ty n T2)
  | TRef d1 T        => TRef (splice_qual n d1) (splice_ty n T)
  end.

Definition splice_tenv (n : nat) (Γ : tenv) : tenv :=
  map (fun p => (fst (fst p), (splice_ty n (snd (fst p))), (splice_qual n (snd p)))) Γ.

Module SplicingNotations.
  Declare Scope splicing.
  Notation "t ↑ᵗ n" := (splice n t) (at level 10) : splicing.
  Notation "T ↑ᵀ n" := (splice_ty n T) (at level 10) : splicing.
  Notation "q ↑ᵈ n" := (splice_qual n q) (at level 10) : splicing.
  Notation "g ↑ᴳ n" := (splice_tenv n g) (at level 10) : splicing.
End SplicingNotations.
Import SplicingNotations.
Local Open Scope splicing.

Inductive closed_tm: nat(*B*) -> nat(*F*) -> nat(*Loc*) -> tm -> Prop :=
| cl_tsct : forall b f l,
    closed_tm b f l tunit
| cl_tvarb: forall b f l x,
    x < b ->
    closed_tm b f l #x
| cl_tvarf: forall b f l x,
    x < f ->
    closed_tm b f l $x
| cl_tabs:  forall b f l tm,
    closed_tm (S (S b)) f l tm ->
    closed_tm b f l (tabs tm)
| cl_tapp:  forall b f l tm1 tm2,
    closed_tm b f l tm1 ->
    closed_tm b f l tm2 ->
    closed_tm b f l (tapp tm1 tm2)
| cl_tloc: forall b f l l',
    l' < l ->
    closed_tm b f l &l'
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
| cl_qset : forall b f l fresh vs bs ls,
    bound vs <= f ->
    bound bs <= b ->
    bound ls <= l ->
    closed_qual b f l (qset fresh vs bs ls)
.
#[global] Hint Constructors closed_qual : core.

Inductive closed_ty : nat(*B*) -> nat(*F*) -> nat(*Loc*) -> ty -> Prop :=
| cl_TUnit : forall b f l,
    closed_ty b f l TUnit
| cl_TRef : forall b f l T q,
    closed_ty b f l T ->
    closed_qual b f l q ->
    closed_ty b f l (TRef q T)
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
    closed_qual 0 (‖Γ‖) (‖Σ‖) d2 ->
    qstp Γ Σ d1 d2
| qs_self : forall Γ Σ f df T1 d1 T2 d2,
    indexr f Γ = Some (true, (TFun d1 d2 T1 T2), df) ->
    closed_qual 0 f (‖Σ‖) df ->
    ♦∉ df ->
    qstp Γ Σ (df ⊔ $!f) $!f
| qs_qvar : forall Γ Σ b U x q1,
    indexr x Γ = Some(b, U, q1) ->
    closed_ty 0 x (‖Σ‖) U ->
    closed_qual 0 x (‖Σ‖) q1 ->
    ♦∉ q1 ->
    qstp Γ Σ $!x q1
| qs_cong : forall Γ Σ q d1 d2,
    qstp Γ Σ d1 d2 ->
    closed_qual 0 (‖Γ‖) (‖Σ‖) q ->
    qstp Γ Σ (q ⊔ d1) (q ⊔ d2)
| qs_trans : forall Γ Σ d1 d2 d3,
    qstp Γ Σ d1 d2 -> qstp Γ Σ d2 d3 -> qstp Γ Σ d1 d3
.
#[global] Hint Constructors qstp : core.

Inductive stp : tenv -> senv -> ty -> qual -> ty -> qual -> Prop :=
| s_base : forall Γ Σ d1 d2,
    qstp Γ Σ d1 d2 ->
    stp Γ Σ TUnit d1 TUnit d2
| s_ref : forall Γ Σ T1 T2 q1 q2 d1 d2,
    qstp Γ Σ d1 d2 ->
    stp Γ Σ T1 ∅ T2 ∅ ->
    stp Γ Σ T2 ∅ T1 ∅ ->
    qstp Γ Σ q1 q2 ->
    qstp Γ Σ q2 q1 ->
    stp Γ Σ (TRef q1 T1) d1 (TRef q2 T2) d2
| s_fun : forall Γ Σ T1 d1 T2 d2 T3 d3 T4 d4 d5 d6,
    closed_ty 0 (‖ Γ ‖) (‖ Σ ‖) (TFun d1 d2 T1 T2) ->
    closed_ty 0 (‖ Γ ‖) (‖ Σ ‖) (TFun d3 d4 T3 T4) ->
    qstp Γ Σ d5 d6 ->
    stp Γ Σ T3 d3 T1 d1 ->
    stp ((false, T3,d3) :: (true, TFun d1 d2 T1 T2, {♦}) :: Γ) Σ (open_ty' Γ T2) (openq' Γ d2) (open_ty' Γ T4) (openq' Γ d4) ->
    stp Γ Σ (TFun d1 d2 T1 T2) d5 (TFun d3 d4 T3 T4) d6
.
#[global] Hint Constructors stp : core.

(* Specifies that q covers variable x's qualifier in context Γ|Σ *)
Inductive saturated_var (Γ : tenv) (Σ : senv) (x : id) (q : qual) : Prop :=
| sat_var : forall b U q',
    indexr x Γ = Some (b, U, q') ->
    q' ⊑ q ->
    closed_qual 0 x (‖Σ‖) q' ->
    saturated_var Γ Σ x q.
Arguments sat_var {Γ Σ x q}.
#[global] Hint Constructors saturated_var : core.

(* q covers l's qualifier in Σ *)
Inductive saturated_loc (Σ : senv) (l : id) (q : qual) : Prop :=
| sat_loc : forall U q',
    indexr l Σ = Some (U, q') ->
    q' ⊑ q ⊔ {♦} ->
    closed_qual 0 0 l q' ->
    saturated_loc Σ l q.
Arguments sat_loc {Σ l q}.
#[global] Hint Constructors saturated_loc : core.

Definition tenv_saturated (Γ : tenv) (Σ : senv) (q: qual) : Prop := (forall x, (varF x) ∈ᵥ q -> saturated_var Γ Σ x q).
Definition senv_saturated (Σ : senv) (q: qual) : Prop := (forall l, l ∈ₗ q -> saturated_loc Σ l q).
#[global] Hint Unfold tenv_saturated : core.
#[global] Hint Unfold senv_saturated : core.

(* Specifies that q is transitively closed w.r.t. Γ|Σ, i.e., q covers each of its contained variables/locations in Γ|Σ *)
Inductive saturated (Γ : tenv) (Σ : senv) (q: qual) : Prop :=
| sat_qual : tenv_saturated Γ Σ q ->
             senv_saturated Σ q ->
             saturated Γ Σ q
.
Arguments sat_qual {Γ Σ q}.
#[global] Hint Constructors saturated : core.

(* Store typing contains closed types and well-scoped, saturated qualifiers. *)
Inductive wf_senv : senv -> Prop :=
| wf_senv_nil : wf_senv []
| wf_senv_cons : forall Σ T q,
    wf_senv Σ ->
    closed_ty 0 0 (‖Σ‖) T ->
    closed_qual 0 0 (‖Σ‖) q ->
    senv_saturated Σ q ->
    wf_senv ((T, q) :: Σ)
.
#[global] Hint Constructors wf_senv : core.

(* deBruijn index v occurs nowhere in T *)
Definition not_free (v : id) (T : ty): Prop := [[ v ~> ∅ ]]ᵀ T = T.

Inductive has_type : tenv -> qual -> senv -> tm -> ty -> qual -> Prop :=
| t_base : forall Γ Σ φ,
    closed_qual 0 (‖Γ‖) (‖Σ‖) φ ->
    has_type Γ φ Σ tunit TUnit ∅

| t_var : forall Γ φ Σ x b T d,
    indexr x Γ = Some (b,T,d) ->
    $!x ⊑ φ ->
    closed_qual 0 (‖Γ‖) (‖Σ‖) φ ->
    closed_ty   0 x (‖Σ‖) T ->
    closed_qual 0 x (‖Σ‖) d ->
    has_type Γ φ Σ $x T $!x

| t_abs: forall Γ φ Σ T1 d1 T2 d2 df t,
    closed_tm   2 (‖Γ‖) (‖Σ‖) t ->
    closed_ty   0 (‖Γ‖) (‖Σ‖) (TFun d1 d2 T1 T2) ->
    closed_qual 0 (‖Γ‖) (‖Σ‖) φ ->
    df ⊑ φ ->
    ♦∉ df ->
    senv_saturated Σ df ->
    has_type ((false, T1, d1) :: (true, (TFun d1 d2 T1 T2), df) :: Γ)
             (df ⊔ ($!‖Γ‖) ⊔ $!(S (‖Γ‖)) ⊔ {♦}) Σ (t <~²ᵗ Γ) (T2 <~²ᵀ Γ) (d2 <~²ᵈ Γ) ->
    has_type Γ φ Σ (tabs t) (TFun d1 d2 T1 T2) df

| t_app : forall Γ φ Σ t1 d1 t2 d2 df T1 T2,
    has_type Γ φ Σ t1 (TFun d1 d2 T1 T2) df ->
    has_type Γ φ Σ t2 T1 d1 ->
    (d2 <~ᵈ ∅ ; ∅) ⊑ φ ->
    ♦∉ d1 ->
    senv_saturated Σ (d2 <~ᵈ ∅ ; ∅) ->
    not_free 0 T2 ->
    has_type Γ φ Σ (tapp t1 t2) (T2 <~ᵀ ∅ ; d1) (d2 <~ᵈ df ; d1)

| t_app_fresh : forall Γ φ Σ t1 d1 d1' t2 d2 df df' T1 T2,
    has_type Γ φ Σ t1 (TFun (df' ⋒ d1') d2 T1 T2) df ->
    d1 ⊑ d1' ->
    df ⊑ df' ->
    has_type Γ φ Σ t2 T1 d1 ->
    (♦∈ d1 -> not_free 1 T2) ->
    not_free 0 T2 ->
    (d2 <~ᵈ ∅ ; ∅) ⊑ φ ->
    d1' ⊑ φ ->
    df' ⊑ φ ->
    saturated Γ Σ d1' ->
    saturated Γ Σ df' ->
    senv_saturated Σ (d2 <~ᵈ ∅ ; ∅) ->
    has_type Γ φ Σ (tapp t1 t2) (T2 <~ᵀ ∅ ; d1) (d2 <~ᵈ df ; d1)

| t_loc : forall Γ φ Σ l T q,
    closed_qual 0 (‖Γ‖) (‖Σ‖) φ ->
    indexr l Σ = Some (T,q) ->
    closed_ty 0 0 (‖Σ‖) T ->
    closed_qual 0 0 (‖Σ‖) q ->
    &!l ⊑ φ ->
    q ⊑ φ ->
    ♦∉ q ->
    has_type Γ φ Σ &l (TRef q T) (q ⊔ &!l)

| t_ref: forall Γ φ Σ T t d1,
    has_type Γ φ Σ t T d1 ->
    closed_ty 0 (‖Γ‖) (‖Σ‖) T ->
    {♦} ⊑ φ ->
    ♦∉ d1 ->
    has_type Γ φ Σ (tref t) (TRef d1 T) ({♦} ⊔ d1)

| t_deref: forall Γ φ Σ T d d1 t,
    has_type Γ φ Σ t (TRef d1 T) d ->
    ♦∉ d1 ->
    d1 ⊑ φ ->
    senv_saturated Σ d1 ->
    has_type Γ φ Σ !t T d1

| t_assign: forall Γ φ Σ T t1 d d1 t2,
    has_type Γ φ Σ t1 (TRef d1 T) d ->
    has_type Γ φ Σ t2 T d1 ->
    ♦∉ d1 ->
    has_type Γ φ Σ (tassign t1 t2) TUnit ∅

| t_sub: forall Γ φ  Σ e T1 d1 T2 d2,
    has_type Γ φ Σ e T1 d1 ->
    stp Γ Σ T1 d1 T2 d2 ->
    d2 ⊑ φ ->
    senv_saturated Σ d2 ->
    has_type Γ φ Σ e T2 d2
.
#[global] Hint Constructors has_type : core.

Inductive value : tm -> Prop :=
| value_abs : forall t, value (tabs t)
| value_cst : value tunit
| value_loc : forall l, value &l
.
#[global] Hint Constructors value : core.

Definition store := list tm.

Inductive step : tm -> store -> tm -> store -> Prop :=
(*contraction rules*)
| step_beta : forall t v σ,
    value v ->
    step (tapp (tabs t) v) σ (t <~ᵗ (tabs t); v) σ
| step_ref : forall v σ,
    value v ->
    step (tref v) σ (&‖σ‖) (v :: σ)
| step_deref : forall σ l v,
    indexr l σ = Some v ->
    step (! &l) σ v σ
| step_assign : forall σ l v,
    l < ‖σ‖ ->
    value v ->
    step (tassign &l v) σ tunit (update σ l v)
(*congruence rules*)
| step_c_ref : forall t t' σ σ',
    step t σ t' σ' ->
    step (tref t) σ (tref t') σ'
| step_c_deref : forall t t' σ σ',
    step t σ t' σ' ->
    step !t σ !t' σ'
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
  ‖Σ‖ = ‖σ‖ /\
  forall l v T q, indexr l Σ = Some (T,q) -> indexr l σ = Some v -> value v /\ has_type Γ φ Σ v T q.

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
  | qset fresh fvs bvs ls =>
    match mem v fvs with
    | true  => (qset fresh (unsplice_set 0 (remove v fvs)) bvs ls) ⊔ q'
    | false => qset fresh (unsplice_set 0 fvs) bvs ls
    end
  end.

Fixpoint subst_ty (T : ty) (v : nat) (q : qual) : ty :=
  match T with
  | TUnit            => TUnit
  | TFun q1 q2 T1 T2 => TFun (subst_q q1 v q) (subst_q q2 v q) (subst_ty T1 v q) (subst_ty T2 v q)
  | TRef q1 T        => TRef (subst_q q1 v q) (subst_ty T v q)
  end.

Definition subst_tenv (Γ : tenv) (v : nat) (q1 : qual) : tenv :=
  map (fun p => match p with
             | (b,T,q') => (b, (subst_ty T v q1) , (subst_q q' v q1))
             end) Γ.

Module SubstitutionNotations.
  Declare Scope substitutions.
  Notation "{ v1 |-> t1 ; t2 }ᵗ t"  := (subst_tm (subst_tm t v1 t1) v1 t2) (at level 10) : substitutions.
  Notation "{ v1 |-> t1 }ᵗ t"       := (subst_tm t v1 t1) (at level 10) : substitutions.
  Notation "{ v1 |-> q1 ; q2 }ᵈ q"  := (subst_q (subst_q q v1 q1) v1 q2) (at level 10) : substitutions.
  Notation "{ v1 |-> q1 }ᵈ q"       := (subst_q q v1 q1) (at level 10) : substitutions.
  Notation "{ v1 |-> q1 ; q2  }ᵀ T" := (subst_ty (subst_ty T v1 q1) v1 q2) (at level 10) : substitutions.
  Notation "{ v1 |-> q1 }ᵀ T"       := (subst_ty T v1 q1) (at level 10) : substitutions.
  Notation "{ v1 |-> q1 }ᴳ G"       := (subst_tenv G v1 q1) (at level 10) : substitutions.
  Notation "{ v1 |-> q1 ; q2 }ᴳ G"  := (subst_tenv (subst_tenv G v1 q1) v1 q2) (at level 10) : substitutions.
End SubstitutionNotations.
Import SubstitutionNotations.
Local Open Scope substitutions.

(* Indicates the relation between an assumption's qualifier and the qualifier we substitute for the variable.
   This helps ensure that the substitution lemma can be expressed uniformly on a single variable. *)
Inductive Substq : qual -> qual -> Prop :=
| SExact : forall df,    ♦∉ df -> Substq df df        (* precise substitution, e.g., we substitute a recursive function into itself or the argument in t_app *)
| SGrow  : forall df dx, ♦∉ dx -> Substq (df ⋒ dx) dx (* a growing substitution, e.g., we substitute the argument in t_app_fresh, note the difference. *)
.
#[global] Hint Constructors Substq : core.

(* disjointq Σ Σ' q q' (in symbols: Σ → Σ' ∋ q ⊕ q') is an invariant propagated through the type safety proof.
   Given a reduction step starting in store typing Σ and resulting in Σ', and a qualifier q, then
   Σ → Σ' ∋ q ⊕ q' specifies that the step has increased q by q' (e.g., from allocation effects).
   q' is either empty (no observable change to q), or q' = (q'' ⊔ &!‖Σ‖) for some q'' where q'' ⊑ q.
   That is, q increases at most by a single fresh store location (&!‖Σ‖, the next free address), and this
   new location stores a value that is already aliased by q. *)
Inductive disjointq (Σ Σ' : senv) : qual -> qual -> Prop :=
| disj_bot : forall q,
    disjointq Σ Σ' q ∅
| disj_loc : forall T q q',
    q ⊑ q' ->
    closed_ty 0 0 (‖Σ‖) T ->
    closed_qual 0 0 (‖Σ‖) q ->
    senv_saturated Σ q ->
    Σ' = (T,q) :: Σ ->
    disjointq Σ Σ' q' (q ⊔ &!‖Σ‖)
.
Arguments disj_loc { Σ Σ' }.
#[global] Hint Constructors disjointq : core.
Notation " S → T ∋ q ⊕ q'" := (disjointq S T q q') (at level 10).

(* :! -- directly invertible value typing *)

Inductive vtp: senv -> tm -> ty -> qual -> Prop :=
| vtp_base: forall Σ d,
  closed_qual 0 0 (‖Σ‖) d ->
  senv_saturated Σ d ->
  vtp Σ tunit TUnit d

| vtp_loc:  forall Σ l T U q d,
  closed_qual 0 0 (‖Σ‖) d ->
  closed_ty 0 0 (‖Σ‖) T ->
  closed_qual 0 0 (‖Σ‖) q ->
  indexr l Σ = Some (T,q) ->
  stp [] Σ T ∅ U ∅ ->
  stp [] Σ U ∅ T ∅ ->
  qstp [] Σ (q ⊔ &!l) d ->
  ♦∉ q ->
  senv_saturated Σ d ->
  vtp Σ &l (TRef q U) d

| vtp_abs: forall Σ T1 d1 T2 d2 T3 d3 T4 d4 df1 df2 t,
  closed_tm 2 0 (‖Σ‖) t ->
  closed_qual 0 0 (‖Σ‖) df2 ->
  closed_ty 0 0 (‖Σ‖) (TFun d3 d4 T3 T4) -> (* supertype *)
  closed_ty 0 0 (‖Σ‖) (TFun d1 d2 T1 T2) -> (* subtype *)
  has_type [(false,T1,d1) ; (true, (TFun d1 d2 T1 T2), df1)]
            (df1 ⊔ $!0 ⊔ $!1 ⊔ {♦}) Σ (t <~²ᵗ ([] : tenv)) (T2 <~²ᵀ ([] : tenv)) (d2 <~²ᵈ ([] : tenv)) ->
  stp [] Σ T3 d3 T1 d1 ->
  qstp [] Σ df1 df2 ->
  stp [(false,T3, d3) ; (true, (TFun d1 d2 T1 T2), {♦})] Σ
      (T2 <~²ᵀ ([] : tenv)) (d2 <~²ᵈ ([] : tenv))
      (T4 <~²ᵀ ([] : tenv)) (d4 <~²ᵈ ([] : tenv)) ->
  ♦∉ df1 ->
  senv_saturated Σ df1 ->
  senv_saturated Σ df2 ->
  vtp Σ (tabs t) (TFun d3 d4 T3 T4) df2
.
#[global] Hint Constructors vtp : core.

(* The concluding statement of the preservation part of type safety, i.e., typing is preserved after a step under an extended store, so
   that the initial qualifier is increased by at most a fresh storage effect. *)
Inductive preserve (Γ : tenv) (Σ : senv) (t' : tm) (T : ty) (d : qual) (σ' : store) : Prop :=
| Preserve : forall Σ' d',
    Σ' ⊇ Σ ->
    wf_senv Σ' ->
    CtxOK Γ (ldom Σ') Σ' σ' ->
    Σ → Σ' ∋ d ⊕ d'  ->
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
    q1' ⋒ q2' ⊑ {♦} ->
    senv_saturated Σ'' q1' ->
    senv_saturated Σ'' q2' ->
    separate Σ t1' T1 t2' T2.
Arguments Separate {Σ t1' T1 t2' T2}.

(** Metatheory *)

Lemma extends_refl : forall {A}, forall{l : list A}, l ⊇ l.
  intros. unfold extends. exists []. auto.
Qed.
#[global] Hint Resolve extends_refl : core.

Lemma extends_trans : forall {A}, forall{l1 l2 l3 : list A}, l2 ⊇ l1 -> l3 ⊇ l2 -> l3 ⊇ l1.
  intros. unfold extends in *. destruct H. destruct H0. subst. exists (x0 ++ x). rewrite app_assoc. auto.
Qed.
#[global] Hint Resolve extends_trans : core.

Lemma extends_empty : forall {A}, forall{l : list A}, l ⊇ [].
  intros. unfold extends. exists l. rewrite app_nil_r. auto.
Qed.
#[global] Hint Resolve extends_empty : core.

Lemma extends_cons : forall {A}, forall{l : list A}, forall{a:A}, (a :: l) ⊇ l.
  intros. unfold extends. exists [a]. auto.
Qed.
#[global] Hint Resolve extends_cons : core.

Lemma extends_length : forall {A}, forall{l1 l2 : list A}, l1 ⊇ l2 -> length l2 <= length l1.
  intros. unfold extends in H. destruct H as [l' Heq]. subst. rewrite length_app. lia.
Qed.
#[global] Hint Resolve extends_length : core.

Lemma extends_ldom : forall {Σ' Σ : senv}, Σ' ⊇ Σ -> ldom Σ ⊑ ldom Σ'.
  intros. inversion H. unfold ldom. simpl.
  intuition. unfold dom.
  assert (‖Σ'‖ = ‖x ++ Σ‖). subst. auto.
  rewrite length_app in H1. assert (‖Σ‖ <= ‖Σ'‖). lia.
  apply nset_subset. lia.
Qed.
#[global] Hint Resolve extends_ldom: core.

Lemma open_tm'_len : forall {A} {Γ Γ' : list A} {t}, ‖Γ‖ = ‖Γ'‖ -> open_tm' Γ t = open_tm' Γ' t.
  intros.  unfold open_tm'. rewrite H. auto.
Qed.

Lemma open_ty'_len : forall {A} {Γ Γ' : list A} {T}, ‖Γ‖ = ‖Γ'‖ -> open_ty' Γ T = open_ty' Γ' T.
  intros.  unfold open_ty'. rewrite H. auto.
Qed.

Lemma openq'_len : forall {A} {Γ Γ' : list A} {q}, ‖Γ‖ = ‖Γ'‖ -> openq' Γ q = openq' Γ' q.
  intros.  unfold openq'. rewrite H. auto.
Qed.

Lemma open_ty_preserves_size: forall T d j, ty_size T = ty_size (open_rec_ty j d T).
  induction T; intros; simpl; eauto.
Qed.

Lemma splice_qual_empty : forall {k}, ∅ ↑ᵈ k = ∅.
  intros. simpl. rewrite splice_set_empty. auto.
Qed.
#[global] Hint Resolve splice_qual_empty : core.

Lemma splice_qual_fresh : forall {k}, {♦} ↑ᵈ k = {♦}.
  intros. simpl. rewrite splice_set_empty. auto.
Qed.
#[global] Hint Resolve splice_qual_fresh : core.

Lemma closed_qual_sub : forall {b f l d}, closed_qual b f l d -> forall {d'}, d' ⊑ d -> closed_qual b f l d'.
Proof.
  intros. inversion H. subst. destruct d'.
  inversion H0. intuition. constructor.
  eapply subset_bound; eauto.
  eapply subset_bound; eauto.
  eapply subset_bound; eauto.
Qed.
#[global] Hint Resolve closed_qual_sub : core.

Lemma closed_qual_empty : forall {b f l}, closed_qual b f l ∅.
  intros. constructor; rewrite bound_empty; lia.
Qed.
#[global] Hint Resolve closed_qual_empty : core.

Lemma closed_qual_fresh : forall {b f l}, closed_qual b f l {♦}.
  intros. constructor; rewrite bound_empty; lia.
Qed.
#[global] Hint Resolve closed_qual_fresh : core.

Lemma closed_qual_ldom : forall {Σ : senv}, closed_qual 0 0 (‖Σ‖) (ldom Σ).
  intros. unfold ldom. constructor. 1,2 : rewrite bound_empty; auto.
  rewrite bound_dom. auto.
Qed.
#[global] Hint Resolve closed_qual_ldom : core.

Lemma closed_qual_cong : forall {b f l d},
    closed_qual b f l d -> forall {d'}, d ≡ d' -> closed_qual b f l d'.
Proof.
  intros b f l d H. induction H; intros d' Heq.
  destruct d'. inversion Heq. intuition. constructor.
  eapply set_eq_bound; eauto.
  eapply set_eq_bound; eauto.
  eapply set_eq_bound; eauto.
Qed.

Lemma just_fv_closed : forall {x b f l fr}, x < f <-> closed_qual b f l (${ fr } x).
Proof.
  split; intros.
  - constructor; unfold bound.
    rewrite max_elt_singleton. lia.
    rewrite max_elt_empty. lia.
    rewrite max_elt_empty. lia.
  - inversion H. subst.
    unfold bound in H6. rewrite max_elt_singleton in H6. lia.
Qed.

Lemma just_loc_closed : forall {x b f l fr}, x < l <-> closed_qual b f l (&{ fr } x).
Proof.
  split; intros.
  - constructor; unfold bound.
    rewrite max_elt_empty. lia.
    rewrite max_elt_empty. lia.
    rewrite max_elt_singleton. lia.
  - inversion H. subst. unfold bound in H9.
    rewrite max_elt_singleton in H9. lia.
Qed.

Lemma splice_tenv_length : forall {n Γ}, ‖ Γ ↑ᴳ n ‖ = ‖Γ‖.
  intros. unfold splice_tenv. rewrite length_map. auto.
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
  constructor; auto. eapply closed_qual_monotone; eauto.
  eapply closed_qual_monotone; eauto. lia.
  eapply IHclosed_ty2; eauto. lia.
Qed.

Lemma closed_tm_open_id : forall {t b f l}, closed_tm b f l t -> forall {n}, b <= n -> forall {x}, [[n ~> x ]]ᵗ t = t.
  intros t b f l H. induction H; intros; simpl; auto;
    try solve [erewrite IHclosed_tm1; eauto; erewrite IHclosed_tm2; eauto; lia | erewrite IHclosed_tm; eauto; lia].
  destruct (Nat.eqb n x) eqn:Heq; auto. apply Nat.eqb_eq in Heq. lia.
Qed.

Lemma closed_qual_open_id : forall {d b f l},
    closed_qual b f l d -> forall {n}, b <= n -> forall {x}, [[n ~> x ]]ᵈ d = d.
  intros. destruct d; simpl. replace (mem n t0) with false. auto.
  inversion H. subst. symmetry. rewrite <- NatSetFacts.not_mem_iff.
  apply bound_le_not_in. lia.
Qed.

Lemma closed_ty_open_id : forall {T b f l}, closed_ty b f l T -> forall {n}, b <= n -> forall {x}, [[n ~> x ]]ᵀ T = T.
  intros T b f l H. induction H; intros; simpl; auto;
    try solve [erewrite IHclosed_ty1; eauto; erewrite IHclosed_ty2; eauto; try lia;
                  try solve [erewrite closed_qual_open_id; eauto; erewrite closed_qual_open_id; eauto; lia]
                | erewrite IHclosed_ty; eauto; try lia; try solve [erewrite closed_qual_open_id; eauto]].
Qed.

Lemma closed_tm_open : forall {t b f l}, closed_tm (S b) f l t -> forall {x}, x < f -> closed_tm b f l ([[ b ~> $x ]]ᵗ t).
  induction t; intros; simpl; intuition; inversion H; subst; try constructor;
  try solve [apply IHt1; auto | apply IHt2; auto | apply IHt; auto ].
  destruct (Nat.eqb b x0) eqn:Heq; intuition.
  apply Nat.eqb_neq in Heq. constructor. lia. auto. auto.
Qed.

Lemma closed_qual_open : forall {d b f l fr},
    closed_qual (S b) f l d ->
    forall {x}, x < f -> closed_qual b f l ([[ b ~> ${fr}x ]]ᵈ d).
  intros. destruct d. simpl. inversion H. subst.
  destruct (mem b t0) eqn:Heq.
  - repeat rewrite empty_union_right. constructor; auto.
    rewrite union_bound_max'. rewrite bound_singleton. lia.
    apply remove_bound; auto.
  - apply remove_bound in H9. rewrite <- NatSetFacts.not_mem_iff in Heq.
    rewrite remove_equal in H9; auto.
Qed.

Lemma closed_ty_open : forall {T fr b f l}, closed_ty (S b) f l T -> forall {x}, x < f -> closed_ty b f l ([[ b ~> ${fr}x ]]ᵀ T).
  induction T; intros; simpl; intuition; inversion H; subst; try constructor;
    try solve [apply IHT1; auto | apply IHT2; auto | apply IHT; auto ].
  1,2,3 : eapply closed_qual_open; eauto.
Qed.

Lemma closed_tm_open' : forall {t b f l}, closed_tm (S b) f l t -> forall {x}, x <= f -> forall {t'}, closed_tm 0 x l t' -> closed_tm b f l ([[ b ~> t' ]]ᵗ t).
  induction t; intros; simpl; intuition; inversion H; subst; try constructor;
  try solve [eapply IHt1; eauto | eapply IHt2; eauto | eapply IHt; eauto ].
  destruct (Nat.eqb b x0) eqn:Heq; intuition. eapply closed_tm_monotone; eauto; lia.
  apply Nat.eqb_neq in Heq. constructor. lia. auto. auto.
Qed.

Lemma closed_qual_open' : forall {d b f l},
    closed_qual (S b) f l d ->
    forall {x}, x <= f ->
    forall {d'}, closed_qual 0 x l d' -> closed_qual b f l ([[ b ~> d' ]]ᵈ d).
Proof.
  destruct d; intros; simpl; intuition. inversion H. subst.
  destruct d'.
  inversion H1. subst.
  destruct (mem b0 t0) eqn:Hmem.
  - constructor.
    * specialize (@union_bound_max t t2) as Hbound. lia.
    * unfold bound in H10.
      destruct (max_elt t0) eqn:Hmax.
      assert (e <= b0) by lia.
      specialize (@union_bound_max (remove b0 t0) t3) as Hbound.
      specialize (@remove_max_bound' _ _ _ Hmax Hmem H2) as Hr. lia.
      specialize (@max_elt_none_mem _ _ Hmax Hmem) as bot. inversion bot.
    * specialize (@union_bound_max t1 t4) as Hbound. lia.
  - constructor; auto. unfold bound in H10. unfold bound.
    destruct (max_elt t0) eqn:Hmax.
    inversion H10. subst.
    specialize (@NatSet.F.max_elt_1 _ _ Hmax) as HIn.
    rewrite <- NatSetProperties.FM.not_mem_iff in Hmem.
    contradiction. subst. lia. lia.
Qed.

Lemma closed_ty_open' : forall {T b f l}, closed_ty (S b) f l T -> forall {x}, x <= f -> forall {d}, closed_qual 0 x l d -> closed_ty b f l ([[ b ~> d ]]ᵀ T).
  induction T; intros; simpl; intuition; inversion H; subst; try constructor;
    try solve [eapply IHT1; eauto | eapply IHT2; eauto | eapply IHT; eauto ].
  1,2,3 : eapply closed_qual_open'; eauto.
Qed.

Lemma closed_tm_open_ge : forall {t b f l}, closed_tm (S b) f l t -> forall {x}, f <= x -> closed_tm b (S x) l ([[ b ~> $x ]]ᵗ t).
  induction t; intros; simpl; intuition; inversion H; subst; try constructor;
      try solve [eapply IHt1; eauto | eapply IHt2; eauto | eapply IHt; eauto ].
  destruct (Nat.eqb b x0) eqn:Heq. intuition.
  apply Nat.eqb_neq in Heq. inversion H. subst.
  constructor. lia. lia. auto.
Qed.

Lemma closed_qual_open_ge : forall {d fr b f l},
    closed_qual (S b) f l d ->
    forall {x}, f <= x -> closed_qual b (S x) l ([[ b ~> ${fr}x ]]ᵈ d).
Proof.
  destruct d; intros; simpl; intuition. inversion H. subst.
  destruct (mem b0 t0) eqn: Hmem.
  - constructor.
    * eapply bound_increase; eauto.
    * specialize (@NatSetProperties.empty_union_2 {}N (remove b0 t0) NatSet.F.empty_1) as HU.
      apply NatSet.eq_if_Equal in HU. rewrite HU. clear HU.
      unfold bound. unfold bound in H9.
      destruct (max_elt t0) eqn:Hmax1; inversion H9. subst.
      destruct (max_elt (remove b0 t0)) eqn:Hmax2.
      eapply remove_max_bound; eauto. lia.
      subst. destruct (max_elt (remove b0 t0)) eqn:Hmax2.
      assert (e < b0) by lia. eapply remove_nonexist_bound; eauto. lia.
      subst. specialize (@max_elt_none_mem _ _ Hmax1 Hmem) as bot. inversion bot.
    * specialize (@NatSetProperties.empty_union_2 {}N t1 NatSet.F.empty_1) as HU.
      apply NatSet.eq_if_Equal in HU. rewrite HU. auto.
  - constructor; try lia.
    unfold bound in H9. unfold bound. destruct (max_elt t0) eqn:Hmax.
    inversion H9; subst. specialize (@NatSet.F.max_elt_1 _ _ Hmax) as HIn.
    rewrite <- NatSetProperties.FM.not_mem_iff in Hmem. contradiction. lia. lia.
Qed.

Lemma closed_ty_open_ge : forall {T fr b f l}, closed_ty (S b) f l T -> forall {x}, f <= x -> closed_ty b (S x) l ([[ b ~> ${fr}x ]]ᵀ T).
  induction T; intros; simpl; intuition; inversion H; subst; try constructor;
    try solve [eapply IHT1; eauto | eapply IHT2; eauto | eapply IHT; eauto ].
  1,2,3 :eapply closed_qual_open_ge; eauto.
Qed.

Lemma closed_open_succ : forall {t b f l}, closed_tm b f l t -> forall {j}, closed_tm b (S f) l ([[ j ~> $f ]]ᵗ t).
  induction t; intros; simpl; intuition; inversion H; subst; try constructor;
    try solve [eapply IHt1; eauto | eapply IHt2; eauto | eapply IHt; eauto ].
    destruct (Nat.eqb j x) eqn:Heq. intuition.
    apply Nat.eqb_neq in Heq. inversion H. subst. intuition. lia. auto.
Qed.

Lemma closed_qual_open_succ : forall {d b fr f l},
    closed_qual b f l d ->
    forall {j}, closed_qual b (S f) l ([[j ~> ${fr}f ]]ᵈ d).
Proof.
  destruct d; intros; simpl; intuition. inversion H. subst.
  destruct (mem j t0) eqn:Hmem.
  - constructor. specialize (@union_bound_max t (singleton f)) as Hmax.
    rewrite bound_singleton in Hmax. lia. rewrite empty_union_right.
    apply remove_preserves_bound; auto. rewrite empty_union_right. lia.
  - constructor; auto.
Qed.

Lemma closed_ty_open_succ : forall {T fr b f l}, closed_ty b f l T -> forall {j}, closed_ty b (S f) l ([[ j ~> ${fr}f ]]ᵀ T).
  induction T; intros; simpl; intuition; inversion H; subst; try constructor;
    try solve [eapply IHT1; eauto | eapply IHT2; eauto | eapply IHT; eauto ].
  1,2,3 :eapply closed_qual_open_succ; eauto.
Qed.

Lemma closed_tm_open_succ : forall {t b f l}, closed_tm b f l t -> forall {j}, closed_tm b (S f) l ([[ j ~> $f ]]ᵗ t).
  induction t; intros; simpl; intuition; inversion H; subst; try constructor;
    try solve [eapply IHt1; eauto | eapply IHt2; eauto | eapply IHt; eauto ].
  bdestruct (j =? x); intuition. lia. auto.
Qed.

Lemma open_rec_tm_commute : forall t i j x y, i <> j ->
  [[i ~> $ x ]]ᵗ ([[j ~> $ y ]]ᵗ t) = [[j ~> $ y ]]ᵗ ([[i ~> $ x ]]ᵗ t).
  induction t; intros; simpl; eauto;
    try solve [rewrite IHt1; eauto; rewrite IHt2; eauto | rewrite IHt; eauto].
  destruct v. intuition.
  destruct (Nat.eqb i i0) eqn:Hii0; destruct (Nat.eqb j i0) eqn:Hji0; simpl;
    try rewrite Hii0; try rewrite Hji0; auto.
  apply Nat.eqb_eq in Hii0. apply Nat.eqb_eq in Hji0. subst. contradiction.
Qed.

Lemma open_qual_commute : forall d frx fry i j x y, i <> j ->
    [[i ~> ${frx} x ]]ᵈ ([[j ~> ${fry} y ]]ᵈ d)
  = [[j ~> ${fry} y ]]ᵈ ([[i ~> ${frx} x ]]ᵈ d).
  destruct d; intros; simpl; intuition.
  destruct (mem j t0) eqn:Heqj; destruct (mem i t0) eqn:Heqi; simpl; repeat rewrite empty_union_right;
    try replace (mem i (remove j t0)) with (mem i t0); try replace (mem j (remove i t0)) with (mem j t0);
      try rewrite Heqj; try rewrite Heqi; auto.
  f_equal; try fnsetdec. destr_bool.
  all : symmetry.
  all : repeat match goal with
        | [ H : mem _ _ = true  |- _ ] => apply NatSet.F.mem_2 in H
        | [ |-  mem _ _ = true ]       => apply NatSet.F.mem_1
        | [ H : mem _ _ = false |- _ ] => rewrite <- NatSetProperties.FM.not_mem_iff in H
        | [ |-  mem _ _ = false ]      => rewrite <- NatSetProperties.FM.not_mem_iff
        end.
  all : fnsetdec.
Qed.

Lemma open_rec_ty_commute : forall T frx fry i j x y, i <> j ->
    [[i ~> ${frx} x ]]ᵀ ([[j ~> ${fry} y ]]ᵀ T)
  = [[j ~> ${fry} y ]]ᵀ ([[i ~> ${frx} x ]]ᵀ T).
  induction T; intros; simpl; eauto.
  erewrite open_qual_commute; eauto.
  erewrite open_qual_commute with (i:=(S (S i))); eauto.
  erewrite IHT1; eauto; erewrite IHT2; eauto.
  erewrite IHT; eauto. erewrite open_qual_commute; eauto.
Qed.

Lemma open_rec_tm_commute' : forall t i j x t' f l, i <> j -> closed_tm 0 f l t' ->
  [[i ~> $ x ]]ᵗ ([[j ~> t' ]]ᵗ t) = [[j ~> t' ]]ᵗ ([[i ~> $ x ]]ᵗ t).
  induction t; intros; simpl; eauto;
    try solve [erewrite IHt1; eauto; erewrite IHt2; eauto | erewrite IHt; eauto].
  - destruct v. intuition.
    destruct (Nat.eqb i i0) eqn:Hii0; destruct (Nat.eqb j i0) eqn:Hji0; simpl;
      try rewrite Hii0; try rewrite Hji0; auto.
    apply Nat.eqb_eq in Hii0. apply Nat.eqb_eq in Hji0. subst. contradiction.
    eapply closed_tm_open_id; eauto. lia.
Qed.

Lemma open_qual_commute' : forall d i j fr x d' f l, i <> j -> closed_qual 0 f l d' ->
    [[ i ~> ${fr}x ]]ᵈ ([[ j ~> d' ]]ᵈ d)
  = [[ j ~> d' ]]ᵈ ([[ i ~> ${fr}x ]]ᵈ d).
  destruct d; destruct d'; intros; simpl; intuition.
  inversion H0. subst. apply bound_0_empty in H9. subst.
  destruct (mem j t0) eqn:Heqj; destruct (mem i t0) eqn:Heqi; simpl; repeat rewrite empty_union_right;
    try replace (mem i (remove j t0)) with (mem i t0); try replace (mem j (remove i t0)) with (mem j t0);
      try rewrite Heqj; try rewrite Heqi; auto.
  f_equal; try fnsetdec. destr_bool.
  all : symmetry.
  all : repeat match goal with
        | [ H : mem _ _ = true  |- _ ] => apply NatSet.F.mem_2 in H
        | [ |-  mem _ _ = true ]       => apply NatSet.F.mem_1
        | [ H : mem _ _ = false |- _ ] => rewrite <- NatSetProperties.FM.not_mem_iff in H
        | [ |-  mem _ _ = false ]      => rewrite <- NatSetProperties.FM.not_mem_iff
        end.
  all : fnsetdec.
Qed.

Lemma open_rec_ty_commute' : forall T i j fr x d f l, i <> j -> closed_qual 0 f l d ->
    [[ i ~> ${fr}x ]]ᵀ ([[ j ~> d ]]ᵀ T)
  = [[ j ~> d ]]ᵀ ([[ i ~> ${fr}x ]]ᵀ T).
  induction T; intros; simpl; eauto.
  erewrite open_qual_commute'; eauto. erewrite open_qual_commute'; eauto.
  erewrite IHT1; eauto; erewrite IHT2; eauto.
  erewrite open_qual_commute'; eauto. erewrite IHT; eauto.
Qed.

Lemma open_rec_tm_commute'' : forall t i j t' t'' f l, i <> j -> closed_tm 0 f l t' -> closed_tm 0 f l t'' ->
    [[ i ~> t'']]ᵗ ([[ j ~> t' ]]ᵗ t)
  = [[ j ~> t' ]]ᵗ ([[ i ~> t'' ]]ᵗ t).
  induction t; intros; simpl; eauto;
    try solve [erewrite IHt1; eauto; erewrite IHt2; eauto | erewrite IHt; eauto].
  - destruct v. intuition.
    destruct (Nat.eqb i i0) eqn:Hii0; destruct (Nat.eqb j i0) eqn:Hji0; simpl;
      try rewrite Hii0; try rewrite Hji0; auto.
    apply Nat.eqb_eq in Hii0. apply Nat.eqb_eq in Hji0. subst. contradiction.
    symmetry. eapply closed_tm_open_id; eauto. lia. eapply closed_tm_open_id; eauto. lia.
Qed.

Lemma open_qual_commute'' : forall d i j d' d'' f l, i <> j -> closed_qual 0 f l d' -> closed_qual 0 f l d'' ->
    [[ i ~> d'']]ᵈ ([[ j ~> d' ]]ᵈ d)
  = [[ j ~> d' ]]ᵈ ([[ i ~> d'' ]]ᵈ d).
  destruct d; destruct d'; destruct d''; intros; simpl; intuition.
  inversion H0. subst. inversion H1. subst. apply bound_0_empty in H10, H13. subst.
  repeat rewrite empty_union_right in *.
  destruct (mem j t0) eqn:Heqj; destruct (mem i t0) eqn:Heqi; simpl; repeat rewrite empty_union_right;
    try replace (mem i (remove j t0)) with (mem i t0); try replace (mem j (remove i t0)) with (mem j t0);
      try rewrite Heqj; try rewrite Heqi; auto.
  f_equal; try fnsetdec. destr_bool.
  all : symmetry.
  all : repeat match goal with
        | [ H : mem _ _ = true  |- _ ] => apply NatSet.F.mem_2 in H
        | [ |-  mem _ _ = true ]       => apply NatSet.F.mem_1
        | [ H : mem _ _ = false |- _ ] => rewrite <- NatSetProperties.FM.not_mem_iff in H
        | [ |-  mem _ _ = false ]      => rewrite <- NatSetProperties.FM.not_mem_iff
        end.
  all : fnsetdec.
Qed.

Lemma open_rec_ty_commute'' : forall T i j d' d'' f l, i <> j -> closed_qual 0 f l d' -> closed_qual 0 f l d'' ->
    [[ i ~> d'']]ᵀ ([[ j ~> d' ]]ᵀ T)
  = [[ j ~> d' ]]ᵀ ([[ i ~> d'' ]]ᵀ T).
  induction T; intros; simpl; eauto.
  erewrite open_qual_commute''; eauto.
  erewrite open_qual_commute'' with (i:=S (S i)); eauto.
  erewrite IHT1; eauto; erewrite IHT2; eauto.
  erewrite open_qual_commute''; eauto. erewrite IHT; eauto.
Qed.

Lemma open_qual_empty_id : forall k q fr, [[ k ~> q]]ᵈ ∅{ fr } = ∅{ fr }.
  intros. destruct q. compute. rewrite NatSetFacts.empty_b. auto.
Qed.

Lemma closed_tm_open'_id : forall {t f l}, closed_tm 0 f l t -> forall {A} {G : list A}, t <~²ᵗ G = t.
  intros. unfold open_tm'. unfold open_tm. repeat erewrite closed_tm_open_id; eauto.
Qed.

Lemma closed_ty_open'_id : forall {T f l}, closed_ty 0 f l T -> forall {A} {G : list A}, T <~²ᵀ G = T.
  intros. unfold open_ty'. unfold open_ty. repeat erewrite closed_ty_open_id; eauto.
Qed.

Lemma closed_qual_open'_id : forall {q f l}, closed_qual 0 f l q -> forall {A} {G : list A}, q <~²ᵈ G = q.
  intros. unfold openq'. unfold openq. repeat erewrite closed_qual_open_id; eauto.
Qed.

Lemma open_tm'_bv0 : forall A (G : list A), #0 <~²ᵗ G = $‖G‖.
  intros. compute. auto.
Qed.

Lemma open_tm'_bv1 : forall A (G : list A), #1 <~²ᵗ G = $(S (‖G‖)).
  intros. compute. auto.
Qed.

Lemma openq'_bv0 : forall A (G : list A) fr X Y, (qset fr X (singleton 0) Y) <~²ᵈ G = (qset fr X {}N Y ⊔ $!‖G‖).
  intros. compute. rewrite mem_singleton. compute. rewrite remove_singleton_empty.
  repeat rewrite empty_union_left. rewrite NatSetFacts.empty_b. auto.
Qed.

Lemma openq'_bv1 : forall A (G : list A) fr X Y, (qset fr X (singleton 1) Y) <~²ᵈ G = (qset fr X {}N Y ⊔ $!(S (‖G‖))).
  intros. compute. rewrite mem_singleton. compute. rewrite mem_singleton. compute.
  rewrite remove_singleton_empty. repeat rewrite empty_union_left. auto.
Qed.

Lemma open_qual_just_fv : forall i d fr x, [[ i ~> d ]]ᵈ ${fr}x = ${fr}x.
  intros. compute. destruct d. rewrite NatSetFacts.empty_b. auto.
Qed.

Lemma open_qual_just_loc : forall i d fr x, [[i ~> d ]]ᵈ &{fr}x = &{fr}x.
  intros. compute. destruct d. rewrite NatSetFacts.empty_b. auto.
Qed.

Lemma open_rec_tm_bv : forall i t, [[ i ~> t ]]ᵗ #i = t.
  intros. simpl. rewrite Nat.eqb_refl. auto.
Qed.

Lemma open_rec_tm_bv_skip : forall j i t, j <> i -> [[ j ~> t ]]ᵗ #i = #i.
  intros. simpl. rewrite <- Nat.eqb_neq in H. rewrite H. auto.
Qed.

Lemma splice_id : forall {T b f l}, closed_tm b f l T -> T ↑ᵗ f = T.
  induction T; intros; inversion H; subst; simpl; auto;
    try solve [erewrite IHT1; eauto; erewrite IHT2; eauto | erewrite IHT; eauto].
    destruct (le_lt_dec f x) eqn:Heq. lia. auto.
Qed.

Lemma splice_qual_id : forall {d b f l}, closed_qual b f l d -> d ↑ᵈ f = d.
  destruct d; intros; intuition.
  inversion H. subst. simpl.
  f_equal. unfold splice_set. unfold inc.
  unfold bound in H6.
  destruct (max_elt t) eqn:Hmax.
  - assert (e < f) by lia. autounfold. erewrite filter_lt. erewrite filter_gt.
    rewrite NatSetProperties.fold_empty. fnsetdec. all: eauto.
  - apply max_elt_empty' in Hmax. rewrite Hmax.
    rewrite filter_empty. rewrite filter_empty.
    rewrite NatSetProperties.fold_empty. fnsetdec.
Qed.

Lemma splice_ty_id : forall {T b f l}, closed_ty b f l T -> T ↑ᵀ f = T.
  induction T; intros; inversion H; subst; simpl; auto.
  repeat erewrite splice_qual_id; eauto.
  erewrite IHT1; eauto. erewrite IHT2; eauto.
  erewrite splice_qual_id; eauto.
  erewrite IHT; eauto.
Qed.

Lemma splice_open : forall {T j n m}, ([[ j ~> $(m + n) ]]ᵗ T) ↑ᵗ n = [[ j ~> $(S (m + n)) ]]ᵗ (T ↑ᵗ n).
  induction T; intros; simpl; auto;
    try solve [erewrite IHT1; eauto; erewrite IHT2; eauto | erewrite IHT; eauto].
  destruct v; simpl. destruct (le_lt_dec n i) eqn:Heq; auto.
  destruct (PeanoNat.Nat.eqb j i) eqn:Heq; auto.
  simpl. destruct (le_lt_dec n (m + n)) eqn:Heq'. auto. lia.
Qed.

Lemma splice_qual_open : forall {d j fr n m}, ([[j ~> ${fr}(m + n) ]]ᵈ d) ↑ᵈ n = [[j ~> ${fr}(S (m + n)) ]]ᵈ (d ↑ᵈ n).
  destruct d; simpl; intuition. destruct (mem j t0) eqn:Hmem; simpl; f_equal.
  rewrite splice_set_union_dist. f_equal. rewrite splice_set_singleton_inc; auto. lia.
Qed.

Lemma splice_ty_open : forall {T j fr n m}, ([[j ~> ${fr}(m + n) ]]ᵀ T) ↑ᵀ n = [[j ~> ${fr}(S (m + n)) ]]ᵀ (T ↑ᵀ n).
  induction T; intros; simpl; auto.
  rewrite splice_qual_open. rewrite splice_qual_open. rewrite IHT1. rewrite IHT2. auto.
  rewrite splice_qual_open. rewrite IHT. auto.
Qed.

Lemma splice_open' : forall {T} {A} {D : A} {ρ ρ'}, ((T <~²ᵗ (ρ ++ ρ')) ↑ᵗ ‖ρ'‖) = (T ↑ᵗ ‖ρ'‖) <~²ᵗ (ρ ++ D :: ρ').
  intros. unfold open_tm'.
  replace (‖ ρ ++ ρ' ‖) with (‖ρ‖ + ‖ρ'‖).
  replace (S (‖ ρ ++ D :: ρ' ‖)) with (S (S (‖ρ‖) + (‖ρ'‖))).
  replace (‖ ρ ++ D :: ρ' ‖) with (S (‖ρ‖ + ‖ρ'‖)).
  repeat rewrite <- splice_open. auto.
  all: rewrite length_app; simpl; lia.
Qed.

Lemma splice_qual_open' : forall {d} {A} {D : A} {ρ ρ'}, ((d <~²ᵈ (ρ ++ ρ')) ↑ᵈ ‖ρ'‖) = (d ↑ᵈ ‖ρ'‖) <~²ᵈ (ρ ++ D :: ρ').
  intros. unfold openq'. unfold openq.
  replace (‖ ρ ++ ρ' ‖) with (‖ρ‖ + ‖ρ'‖).
  replace (S (‖ ρ ++ D :: ρ' ‖)) with (S (S (‖ρ‖) + (‖ρ'‖))).
  replace (‖ ρ ++ D :: ρ' ‖) with (S (‖ρ‖ + ‖ρ'‖)).
  repeat rewrite <- splice_qual_open. auto.
  all: rewrite length_app; simpl; lia.
Qed.

Lemma splice_ty_open' : forall {T} {A} {D : A} {ρ ρ'}, ((T <~²ᵀ (ρ ++ ρ')) ↑ᵀ ‖ρ'‖) = (T ↑ᵀ ‖ρ'‖) <~²ᵀ (ρ ++ D :: ρ').
  intros. unfold open_ty'. unfold open_ty.
  replace (‖ ρ ++ ρ' ‖) with (‖ρ‖ + ‖ρ'‖).
  replace (S (‖ ρ ++ D :: ρ' ‖)) with (S (S (‖ρ‖) + (‖ρ'‖))).
  replace (‖ ρ ++ D :: ρ' ‖) with (S (‖ρ‖ + ‖ρ'‖)).
  repeat rewrite <- splice_ty_open. auto.
  all: rewrite length_app; simpl; lia.
Qed.

Lemma splice_closed : forall {T b n m l}, closed_tm b (n + m) l T -> closed_tm b (S (n + m)) l (T ↑ᵗ m).
  induction T; simpl; intros; inversion H; subst; intuition.
  destruct (le_lt_dec m x) eqn:Heq; intuition.
Qed.

Lemma splice_qual_closed : forall {d b n m l}, closed_qual b (n + m) l d -> forall {i}, i <= m -> closed_qual b (S (n + m)) l (d ↑ᵈ i).
  destruct d; simpl; intuition.
  inversion H. subst. constructor; auto. destruct (max_elt t) eqn:Hmax.
  - bdestruct (e <? i).
    + erewrite <- splice_set_preserves_bound; eauto.
    + erewrite <- splice_set_inc_bound; eauto. lia.
  - apply max_elt_empty' in Hmax. subst. rewrite splice_set_empty. lia.
Qed.

Lemma splice_ty_closed : forall {T b n m l}, closed_ty b (n + m) l T -> forall {i}, i <= m -> closed_ty b (S (n + m)) l (T ↑ᵀ i).
  induction T; simpl; intros; inversion H; subst; intuition.
  constructor. 1,2 : apply splice_qual_closed; auto. all: intuition.
  constructor. intuition.
  apply splice_qual_closed; auto.
Qed.

Lemma splice_closed' : forall {T b l} {A} {D : A} {ρ ρ'}, closed_tm b (‖ρ ++ ρ'‖) l T -> closed_tm b (‖ρ ++ D :: ρ'‖) l (T ↑ᵗ ‖ρ'‖).
  intros. rewrite length_app in H.
  replace (‖ ρ ++ D :: ρ' ‖) with (S (‖ρ‖ + ‖ρ'‖)).
  apply splice_closed. auto. simpl. rewrite length_app. simpl. lia.
Qed.

Lemma splice_qual_closed' : forall {d b l} {A} {D : A} {ρ ρ'}, closed_qual b (‖ρ ++ ρ'‖) l d -> closed_qual b (‖ρ ++ D :: ρ'‖) l (d ↑ᵈ ‖ρ'‖).
  intros. rewrite length_app in H.
  replace (‖ ρ ++ D :: ρ' ‖) with (S (‖ρ‖ + ‖ρ'‖)).
  eapply splice_qual_closed; eauto. simpl. rewrite length_app. simpl. lia.
Qed.

Lemma splice_ty_closed' : forall {T b l} {A} {D : A} {ρ ρ'}, closed_ty b (‖ρ ++ ρ'‖) l T -> closed_ty b (‖ρ ++ D :: ρ'‖) l (T ↑ᵀ ‖ρ'‖).
  intros. rewrite length_app in H.
  replace (‖ ρ ++ D :: ρ' ‖) with (S (‖ρ‖ + ‖ρ'‖)).
  eapply splice_ty_closed; eauto. simpl. rewrite length_app. simpl. lia.
Qed.

Lemma splice_qual_closed'' : forall {q x b l k}, closed_qual b x l q -> k <= x -> closed_qual b (S x) l (q ↑ᵈ k).
  destruct q; simpl; intuition.
  inversion H. subst. constructor; auto. destruct (max_elt t) eqn:Hmax.
  - bdestruct (e <? k).
    + erewrite <- splice_set_preserves_bound; eauto.
    + erewrite <- splice_set_inc_bound; eauto. lia.
  - apply max_elt_empty' in Hmax. subst. rewrite splice_set_empty. lia.
Qed.

Lemma splice_ty_closed'' : forall {T x b l k}, closed_ty b x l T -> k <= x -> closed_ty b (S x) l (T ↑ᵀ k).
  induction T; simpl; intros; inversion H; subst; constructor; intuition.
  1,2,3 : eapply splice_qual_closed''; eauto.
Qed.

Lemma splice_open_succ : forall {T b n l j}, closed_tm b n l T -> ([[ j ~> $n ]]ᵗ T) ↑ᵗ n = [[ j ~> $ (S n) ]]ᵗ T.
  induction T; simpl; intros; inversion H; subst; auto;
    try solve [erewrite IHT1; eauto; erewrite IHT2; eauto | erewrite IHT; eauto].
  destruct (PeanoNat.Nat.eqb j x) eqn:Heq; auto. simpl.
  destruct (le_lt_dec n n) eqn:Heq'; auto. lia.
  simpl. destruct (le_lt_dec n x) eqn:Heq; auto. lia.
Qed.

Lemma splice_qual_open_succ : forall {d b fr n l j}, closed_qual b n l d ->
  ([[j ~> ${fr}n ]]ᵈ d) ↑ᵈ n = [[j ~> ${fr}(S n) ]]ᵈ d.
  destruct d; simpl; intuition. destruct (mem j t0) eqn:Hmem; simpl; f_equal.
  rewrite splice_set_union_dist. f_equal. 2: rewrite splice_set_singleton_inc; auto.
  all: destruct (max_elt t) eqn:Hmax.
  1,3: erewrite splice_set_id; eauto; inversion H; subst; unfold bound in H6; rewrite Hmax in H6; lia.
  all : apply max_elt_empty' in Hmax; subst; auto.
Qed.

Lemma splice_ty_open_succ : forall {T b fr n l j}, closed_ty b n l T -> ([[ j ~> ${fr} n ]]ᵀ T) ↑ᵀ n = [[ j ~> ${fr} (S n) ]]ᵀ T.
  induction T; simpl; intros; inversion H; subst; auto.
  erewrite splice_qual_open_succ; eauto. erewrite splice_qual_open_succ; eauto.
  erewrite IHT1; eauto. erewrite IHT2; eauto. erewrite IHT; eauto.
  erewrite splice_qual_open_succ; eauto.
Qed.

Lemma splice_qual_open_qual : forall {k n df d2}, ([[n ~> df ]]ᵈ d2) ↑ᵈ k = ([[n ~> df ↑ᵈ k ]]ᵈ (d2 ↑ᵈ k)).
  intros. destruct d2; destruct df; simpl.
  destruct (mem n t0) eqn: H1; simpl; auto. f_equal. rewrite splice_set_union_dist. auto.
Qed.

Lemma splice_qual_open'' : forall {k df d1 d2}, (d2 <~ᵈ df; d1) ↑ᵈ k = (d2 ↑ᵈ k) <~ᵈ (df ↑ᵈ k); (d1 ↑ᵈ k).
  intros. unfold openq. repeat rewrite splice_qual_open_qual. auto.
Qed.

Lemma splice_ty_open_rec_ty : forall {T n k df}, ([[n ~> df ]]ᵀ T) ↑ᵀ k = ([[n ~> df ↑ᵈ k ]]ᵀ (T ↑ᵀ k)).
  induction T; intros; auto.
  - simpl. repeat rewrite splice_qual_open_qual. erewrite IHT1. erewrite IHT2. auto.
  - simpl. repeat rewrite splice_qual_open_qual. erewrite IHT. auto.
Qed.

Lemma splice_ty_open'' : forall {T k df d1}, (T <~ᵀ df; d1) ↑ᵀ k = (T ↑ᵀ k) <~ᵀ (df ↑ᵈ k); (d1 ↑ᵈ k).
  intros. unfold open_ty. repeat rewrite splice_ty_open_rec_ty. auto.
Qed.

Lemma splice_qual_qlub_dist : forall {k q1 q2}, (q1 ⊔ q2) ↑ᵈ k = ((q1 ↑ᵈ k) ⊔ (q2 ↑ᵈ k)).
  intros. destruct q1. destruct q2. simpl. f_equal.
  rewrite splice_set_union_dist. auto.
Qed.

Lemma subqual_splice_lr' : forall {i du df}, du ↑ᵈ i ⊑ df ↑ᵈ i <-> du ⊑ df.
  intros. intuition.
  - destruct du. destruct df.
    unfold splice_qual in *. inversion H.
    intuition. constructor; intuition.
    eapply splice_set_subset_dist. eauto.
  - destruct du. destruct df.
    inversion H. intuition.
    constructor; intuition.
    eapply splice_set_subset_dist. auto.
Qed.
#[global] Hint Resolve subqual_splice_lr' : core.

Lemma subqualb_splice_lr' : forall {i du df}, (du ↑ᵈ i ⊑? df ↑ᵈ i) = (du ⊑? df).
  intros. specialize (@subqual_splice_lr' i du df) as SQS.
  destruct (du ⊑? df) eqn:Heq.
  rewrite subqualb_true_iff in Heq. rewrite subqualb_true_iff. intuition.
  rewrite subqualb_false_iff in Heq. rewrite subqualb_false_iff. intuition.
Qed.

Lemma subqual_splice_r : forall {d1 d2 i f l}, i >= f -> closed_qual 0 f l d1 -> d1 ⊑ d2 <-> d1 ⊑ d2 ↑ᵈ i.
  intros. split; intros.
  - unfold splice_qual. inversion H0. subst. destruct d2.
    unfold subqual in *. intros; intuition.
    eapply splice_set_preserves_superset_1; eauto.
  - unfold subqual in *. destruct d1. destruct d2.
    unfold splice_qual in *. intuition; try fnsetdec.
    inversion H0. subst.
    eapply splice_set_preserves_superset_2. apply H. all: auto.
Qed.

Lemma subqualb_splice_r :  forall {d1 d2 i f l}, i >= f -> closed_qual 0 f l d1 -> (d1 ⊑? d2) = (d1 ⊑? d2 ↑ᵈ i).
  intros. specialize (@subqual_splice_r d1 d2 i f l H H0) as SQS.
  destruct (d1 ⊑? splice_qual i d2) eqn:Heq.
  rewrite subqualb_true_iff in Heq. rewrite subqualb_true_iff. intuition.
  rewrite subqualb_false_iff in Heq. rewrite subqualb_false_iff. intuition.
Qed.

Lemma closed_qual_qlub: forall {b f l d1 d2}, closed_qual b f l d1 -> closed_qual b f l d2 -> closed_qual b f l (d1 ⊔ d2).
  intros. inversion H; subst; inversion H0; subst; intuition.
  simpl. constructor.
  specialize (@union_bound_max vs vs0). lia.
  specialize (@union_bound_max bs bs0). lia.
  specialize (@union_bound_max ls ls0). lia.
Qed.

Lemma closed_qual_qlub_inv: forall {b f l d1 d2}, closed_qual b f l (d1 ⊔ d2) -> closed_qual b f l d1 /\ closed_qual b f l d2.
  intros. destruct d1. destruct d2. inversion H; subst.
  rewrite union_bound_max' in H6. rewrite union_bound_max' in H8. rewrite union_bound_max' in H9. intuition.
Qed.

Lemma closed_qual_qqplus: forall {b f l d1 d2}, closed_qual b f l d1 -> closed_qual b f l d2 -> closed_qual b f l (d1 ⋓ d2).
  intros. destruct d1. destruct b0; unfold qqplus. rewrite qfresh_true. apply closed_qual_qlub; auto.
  rewrite qfresh_false. auto.
Qed.

Lemma closed_qual_qglb : forall {q1 q2 b f l},
    closed_qual b f l q1 -> closed_qual b f l q2 -> closed_qual b f l (q1 ⊓ q2).
  intros. inversion H; subst; inversion H0; subst; simpl; intuition.
  constructor.
  specialize (@inter_bound_min vs vs0) as Hb. lia.
  specialize (@inter_bound_min bs bs0) as Hb. lia.
  specialize (@inter_bound_min ls ls0) as Hb. lia.
Qed.

Lemma closed_qual_open2 : forall {f l d1 d2 d}, closed_qual 2 f l d -> closed_qual 0 f l d1 -> closed_qual 0 f l d2 -> closed_qual 0 f l ([[1 ~> d1 ]]ᵈ ([[0 ~> d2 ]]ᵈ d)).
  intros. erewrite open_qual_commute''; eauto. eapply closed_qual_open'; eauto. eapply closed_qual_open'; eauto.
Qed.

Lemma closed_ty_open2 : forall {f l d1 d2 T}, closed_ty 2 f l T -> closed_qual 0 f l d1 -> closed_qual 0 f l d2 -> closed_ty 0 f l ([[1 ~> d1 ]]ᵀ ([[0 ~> d2 ]]ᵀ T)).
  intros. erewrite open_rec_ty_commute''; eauto. eapply closed_ty_open'; eauto. eapply closed_ty_open'; eauto.
Qed.

Lemma qstp_closed : forall {Γ Σ d1 d2}, qstp Γ Σ d1 d2 -> closed_qual 0 (‖Γ‖) (‖Σ‖) d1 /\ closed_qual 0 (‖Γ‖) (‖Σ‖) d2.
  intros Γ Σ d1 d2 HSQ. induction HSQ; intuition.
  - eapply closed_qual_sub; eauto.
  - apply indexr_var_some' in H. apply closed_qual_qlub. eapply closed_qual_monotone; eauto. lia. apply just_fv_closed. auto.
  - apply indexr_var_some' in H. apply just_fv_closed. auto.
  - apply indexr_var_some' in H. apply just_fv_closed. auto.
  - apply indexr_var_some' in H. eapply closed_qual_monotone; eauto. lia.
  - apply closed_qual_qlub; auto.
  - apply closed_qual_qlub; auto.
Qed.

Lemma qstp_refl : forall {d d'}, d ≡ d' -> forall {Γ Σ}, closed_qual 0 (‖Γ‖) (‖Σ‖) d -> qstp Γ Σ d d'.
  intros d d' Heq Γ Σ Hc. constructor. destruct d. destruct d'. qdec.
  eapply closed_qual_cong; eauto.
Qed.

Lemma qs_cong_r  : forall Γ Σ q d1 d2,
    qstp Γ Σ d1 d2 ->
    closed_qual 0 (‖Γ‖) (‖Σ‖) q ->
    qstp Γ Σ (d1 ⊔ q) (d2 ⊔ q).
  intros. rewrite (@qlub_commute d1). rewrite (@qlub_commute d2). apply qs_cong; auto.
Qed.

Lemma stp_closed : forall {Γ Σ T1 d1 T2 d2},
    stp Γ Σ T1 d1 T2 d2 ->
    closed_ty 0 (‖Γ‖) (‖Σ‖) T1
    /\ closed_qual 0 (‖Γ‖) (‖Σ‖) d1
    /\ closed_ty 0 (‖Γ‖) (‖Σ‖) T2
    /\ closed_qual 0 (‖Γ‖) (‖Σ‖) d2.
Proof.  intros Γ Σ T1 d1 T2 d2 HS. induction HS.
  - intuition. all: apply qstp_closed in H; intuition.
  - intuition. all: apply qstp_closed in H, H0, H1; intuition.
  - intuition. apply qstp_closed in H1; intuition. apply qstp_closed in H1; intuition.
  (* - intuition; repeat apply closed_qual_qlub; auto. *)
Qed.

Lemma stp_refl' : forall {n T}, ty_size T < n -> forall {Γ Σ}, closed_ty 0 (‖Γ‖) (‖Σ‖) T -> forall {d d'}, qstp Γ Σ d d' -> stp Γ Σ T d T d'.
  induction n; try lia; destruct T; simpl; intros Hsize Γ Σ Hc d d' Hstp; inversion Hc; subst.
  - (*TUnit*) constructor. auto.
  - (*TFun*) constructor; auto. apply IHn. lia. auto. apply qstp_refl. apply eqqual_refl. auto.
    apply IHn. unfold open_ty'. unfold open_ty. rewrite <- open_ty_preserves_size. rewrite <- open_ty_preserves_size. simpl. lia. simpl. unfold open_ty'. unfold open_ty.
    eapply closed_ty_open2. eapply closed_ty_monotone; eauto. 1,2 : eapply just_fv_closed; eauto.
    apply qstp_refl. apply eqqual_refl. unfold openq'. unfold openq. rewrite open_qual_commute; auto.
    simpl. eapply closed_qual_open. eapply closed_qual_open. eapply closed_qual_monotone; eauto.
    lia. lia.
  - (*TRef*) constructor; auto.
    all : apply IHn; try lia; auto.
Qed.

Lemma stp_refl : forall {T Γ Σ}, closed_ty 0 (‖Γ‖) (‖Σ‖) T -> forall {d d'}, qstp Γ Σ d d' -> stp Γ Σ T d T d'.
  intros. eapply stp_refl'; eauto.
Qed.

Lemma indexr_splice_tenv : forall {Γ1 i Γ2 b U du},
    indexr i (Γ1 ++ Γ2) = Some (b, U, du) -> forall {k}, ‖Γ2‖ <= i ->
    indexr i (Γ1 ↑ᴳ k ++ Γ2) = Some (b, U ↑ᵀ k, du ↑ᵈ k).
  induction Γ1; intros; simpl in *; intuition. apply indexr_var_some' in H. lia.
  rewrite length_app in *. rewrite splice_tenv_length.
  destruct (Nat.eqb i (‖Γ1‖ + ‖Γ2‖)) eqn:Heq. inversion H. subst.
  simpl. auto. apply IHΓ1; eauto.
Qed.

Lemma splice_qual_glb_dist : forall {d1 d2 k}, (d1 ⊓ d2) ↑ᵈ k = d1 ↑ᵈ k ⊓ d2 ↑ᵈ k.
  intros. destruct d1; destruct d2; intuition.
  simpl. f_equal. apply splice_set_inter_dist.
Qed.

Lemma splice_qual_lub_dist : forall {d1 d2 k}, (d1 ⊔ d2) ↑ᵈ k = (d1 ↑ᵈ k ⊔ d2 ↑ᵈ k).
  intros. destruct d1; destruct d2; intuition.
  simpl. f_equal. apply splice_set_union_dist.
Qed.

Lemma splice_qual_mem_lt : forall {x k d1}, x < k -> $x ∈ᵥ d1 ↑ᵈ k -> $x ∈ᵥ d1.
  intros. destruct d1. simpl in *.
  assert (Subset (singleton x) (splice_set k t)).
  fnsetdec. replace (singleton x) with (splice_set k (singleton x)) in H1.
  rewrite splice_set_subset_dist in H1. assert (In x (singleton x)).
  fnsetdec. intuition. apply splice_set_singleton_inv. auto.
Qed.

Lemma splice_qual_mem_ge : forall {x k d1}, x >= k -> $(S x) ∈ᵥ d1 ↑ᵈ k -> $x ∈ᵥ d1.
  intros. destruct d1. simpl in *.
  assert (Subset (singleton (S x)) (splice_set k t)).
  fnsetdec. replace (singleton (S x)) with (splice_set k (singleton x)) in H1.
  rewrite splice_set_subset_dist in H1. assert (In x (singleton x)).
  fnsetdec. intuition. apply splice_set_singleton_inc. auto.
Qed.

Lemma splice_qual_mem_loc : forall {l k d1}, l ∈ₗ d1 ↑ᵈ k <-> l ∈ₗ d1.
  intros. destruct d1. simpl in *. intuition.
Qed.

Lemma splice_qual_not_mem : forall {k d1}, $k ∈ᵥ (d1 ↑ᵈ k) -> False.
  intros. destruct d1. simpl in H.
  unfold splice_set in *. apply NatSet.F.union_1 in H. intuition.
  * destruct k. apply inc_non_zero in H0. auto.
    rewrite <- inc_in_iff in H0. apply filter_ge_fun_prop in H0. lia.
  * apply filter_lt_fun_prop in H0. lia.
Qed.

Lemma splice_qual_just_fv_ge : forall {k j fr}, k <= j -> ${fr} j ↑ᵈ k = ${fr}(S j).
  intros. simpl. rewrite splice_set_singleton_inc; auto.
Qed.
Lemma splice_qual_just_fv_lt : forall {k j fr}, k > j -> ${fr} j ↑ᵈ k = ${fr}j.
  intros. simpl. rewrite splice_set_singleton_inv; auto.
Qed.

Lemma not_fresh_splice_iff : forall {df n}, ♦∉ df <-> ♦∉ df ↑ᵈ n.
  intros. destruct df. intuition.
Qed.

Lemma fresh_splice_iff : forall {df n}, ♦∈ df <-> ♦∈ df ↑ᵈ n.
  intros. destruct df. intuition.
Qed.

Lemma stp_qstp_inv : forall {Γ Σ T1 d1 T2 d2}, stp Γ Σ T1 d1 T2 d2 -> qstp Γ Σ d1 d2.
  intros Γ Σ T1 d1 T2 d2 HS. induction HS; intuition.
Qed.

Lemma weaken_qstp_gen : forall {Γ1 Γ2 Σ d1 d2},
    qstp (Γ1 ++ Γ2) Σ d1 d2 ->
    forall T', qstp ((Γ1 ↑ᴳ ‖Γ2‖) ++ T' :: Γ2) Σ (d1 ↑ᵈ ‖Γ2‖) (d2 ↑ᵈ ‖Γ2‖).
Proof.
  intros Γ1 Γ2 Σ d1 d2 HSTP. remember (Γ1 ++ Γ2) as Γ. generalize dependent Γ1. induction HSTP; intros Γ1 HeqG T'; subst.
  - constructor. apply subqual_splice_lr'. auto. apply splice_qual_closed'.
    rewrite length_app in *. rewrite splice_tenv_length. auto.
  - rewrite splice_qual_qlub_dist. bdestruct (f <? ‖Γ2‖).
    * rewrite splice_qual_just_fv_lt; auto. erewrite @splice_qual_id with (d:=df).
      eapply qs_self; eauto. rewrite indexr_skips. rewrite indexr_skips in H. rewrite indexr_skip. eauto.
      1-3: simpl; lia. eapply closed_qual_monotone; eauto. lia.
    * rewrite splice_qual_just_fv_ge; auto.
      eapply qs_self; eauto. rewrite <- indexr_insert_ge; auto.
      eapply @indexr_splice_tenv with (k:=‖Γ2‖) in H; auto. simpl in H. eauto.
      eapply splice_qual_closed''; eauto. rewrite <- not_fresh_splice_iff. auto.
  - bdestruct (x <? ‖Γ2‖).
    * rewrite splice_qual_just_fv_lt; auto. erewrite @splice_qual_id with (d:=q1).
      eapply qs_qvar; eauto. rewrite indexr_skips. rewrite indexr_skips in H. rewrite indexr_skip. eauto.
      1-3: simpl; lia. eapply closed_qual_monotone; eauto. lia.
    * rewrite splice_qual_just_fv_ge; auto.
      eapply qs_qvar. rewrite <- indexr_insert_ge; auto.
      eapply @indexr_splice_tenv with (k:=‖Γ2‖) in H; auto. simpl in H. eauto.
      eapply splice_ty_closed''; eauto. eapply splice_qual_closed''; eauto.
      rewrite <- not_fresh_splice_iff. auto.
  - repeat rewrite splice_qual_qlub_dist. eapply qs_cong.
    eapply IHHSTP. auto. apply splice_qual_closed'. rewrite length_app in *. rewrite splice_tenv_length. auto.
  - eapply qs_trans; eauto.
Qed.

Lemma weaken_qstp : forall {Γ Σ d1 d2}, qstp Γ Σ d1 d2 -> forall T', qstp (T' :: Γ) Σ d1 d2.
  intros Γ Σ d1 d2 HST. specialize (@weaken_qstp_gen [] Γ Σ d1 d2) as Hsp. simpl in *.
  specialize (Hsp HST). intros. specialize (Hsp T'). apply qstp_closed in HST. intuition.
  replace (d1 ↑ᵈ ‖Γ‖) with d1 in Hsp. replace (d2 ↑ᵈ ‖Γ‖) with d2 in Hsp. intuition.
  1,2 : erewrite  splice_qual_id; eauto.
Qed.

Lemma weaken_qstp' : forall {Γ Σ d1 d2}, qstp Γ Σ d1 d2 -> forall Γ', qstp (Γ' ++ Γ) Σ d1 d2.
  intros. induction Γ'.
  - simpl. auto.
  - replace ((a :: Γ') ++ Γ) with (a :: (Γ' ++ Γ)).
    apply weaken_qstp. auto. simpl. auto.
Qed.

Lemma weaken_qstp_store : forall {Γ Σ d1 d2}, qstp Γ Σ d1 d2 -> forall {Σ'}, qstp Γ (Σ' ++ Σ) d1 d2.
  intros. induction H.
  - apply qs_sq; auto. rewrite length_app. eapply closed_qual_monotone; eauto. lia.
  - eapply qs_self; eauto. erewrite length_app. eapply closed_qual_monotone; eauto. lia.
  - eapply qs_qvar; eauto. all : erewrite length_app. eapply closed_ty_monotone; eauto. lia. eapply closed_qual_monotone; eauto. lia.
  - eapply qs_cong; eauto. rewrite length_app. eapply closed_qual_monotone; eauto. lia.
  - eapply qs_trans; eauto.
Qed.

Lemma weaken_qstp_store_ext : forall {Γ Σ d1 d2}, qstp Γ Σ d1 d2 -> forall {Σ'}, Σ' ⊇ Σ -> qstp Γ Σ' d1 d2.
  intros. unfold extends in H0. destruct H0. subst. apply weaken_qstp_store. auto.
Qed.

Lemma weaken_stp_gen : forall {Γ1 Γ2 Σ T1 d1 T2 d2},  stp (Γ1 ++ Γ2) Σ T1 d1 T2 d2 ->
    forall T', stp ((Γ1 ↑ᴳ ‖Γ2‖) ++ T' :: Γ2) Σ (T1 ↑ᵀ ‖Γ2‖) (d1 ↑ᵈ ‖Γ2‖) (T2 ↑ᵀ ‖Γ2‖) (d2 ↑ᵈ ‖Γ2‖).
Proof. intros Γ1 Γ2 Σ T1 d1 T2 d2  Hstp T'. remember (Γ1 ++ Γ2)  as Γ. generalize dependent Γ1.  induction Hstp. intros Γ1.
  - constructor. eapply weaken_qstp_gen. subst. auto.
  - intros. assert (stp Γ Σ (TRef q1 T1) d1 (TRef q2 T2) d2). { constructor; intuition. } subst.
    apply stp_closed in H2 as Hcl. intuition.
    inversion H3. inversion H4. subst. simpl.
    specialize (IHHstp1 Γ1). intuition.
    specialize (IHHstp2 Γ1). intuition.
    constructor. apply weaken_qstp_gen. subst; auto.
    1,2 : rewrite splice_qual_empty in H6, H8; auto.
    all: apply weaken_qstp_gen; auto.
  - assert (stp Γ Σ (TFun d1 d2 T1 T2) d5 (TFun d3 d4 T3 T4) d6). { constructor; intuition. } intros.
    subst. intuition. inversion H0; inversion H; subst. apply qstp_closed in H1 as Hcl. intuition.
    constructor; try fold splice_ty. 1-2: constructor.
    1,2,5,6 : apply splice_qual_closed'. 5-8 : apply splice_ty_closed'.
    1-8: rewrite length_app in *; rewrite splice_tenv_length in *; auto.
    apply weaken_qstp_gen. auto.
    specialize (IHHstp1 Γ1). intuition.
    specialize (IHHstp2 ((false,T3, d3) :: (true,(TFun d1 d2 T1 T2), {♦}) :: Γ1)). intuition.
    repeat rewrite <- splice_ty_open'. repeat rewrite <- splice_qual_open'. simpl in H5.
    repeat rewrite @open_ty'_len with (Γ:=(Γ1 ↑ᴳ ‖Γ2‖) ++ Γ2) (Γ':=Γ1++Γ2).
    repeat rewrite @openq'_len with (Γ:=(Γ1 ↑ᴳ ‖Γ2‖) ++ Γ2) (Γ':=Γ1++Γ2). rewrite splice_set_empty in H5. auto.
    all: repeat rewrite length_app; rewrite splice_tenv_length; auto.
  (* - intros. specialize (IHHstp1 Γ1). specialize (IHHstp2 Γ1). intuition.
    eapply s_trans; eauto. *)
Qed.

Lemma weaken_stp : forall {Γ Σ T1 d1 T2 d2}, stp Γ Σ T1 d1 T2 d2 -> forall T', stp (T' :: Γ) Σ T1 d1 T2 d2.
  intros Γ Σ T1 d1 T2 d2 HST. specialize (@weaken_stp_gen [] Γ Σ T1 d1 T2 d2) as Hsp. simpl in *.
  specialize (Hsp HST). intros. specialize (Hsp T'). apply stp_closed in HST. intuition.
  replace (T1 ↑ᵀ ‖Γ‖) with T1 in Hsp. replace (T2 ↑ᵀ ‖Γ‖) with T2 in Hsp.
  replace (d1 ↑ᵈ ‖Γ‖) with d1 in Hsp. replace (d2 ↑ᵈ ‖Γ‖) with d2 in Hsp. intuition.
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
Proof. intros Σ Γ T1 d1 T2 d2 HSTP. induction HSTP; intros.
  + constructor. apply weaken_qstp_store. auto.
  + constructor; auto. all : apply weaken_qstp_store; auto.
  + constructor; auto. 1,2 : rewrite length_app; eapply closed_ty_monotone; eauto; lia.
    apply weaken_qstp_store. auto.
  (* + specialize (IHHSTP1 Σ'). specialize (IHHSTP2 Σ'). eapply s_trans in IHHSTP2; eauto. *)
Qed.

Lemma weaken_stp_store_ext : forall {Σ Γ T1 d1 T2 d2}, stp Γ Σ T1 d1 T2 d2 -> forall {Σ'}, Σ' ⊇ Σ ->  stp Γ Σ' T1 d1 T2 d2.
  intros. unfold extends in H0. destruct H0. subst. apply weaken_stp_store. auto.
Qed.

Lemma qstp_non_fresh : forall {Γ Σ q1 q2}, qstp Γ Σ q1 q2 -> ♦∉ q2 -> ♦∉ q1.
  intros. induction H; intuition.
  - eapply not_fresh_sub; eauto.
  - apply not_fresh_qlub' in H0. intuition.
Qed.

Lemma narrowing_qstp_gen : forall{Γ1 b U du Γ2 Σ d1 d2},
    qstp (Γ1 ++ (b,U,du) :: Γ2) Σ d1 d2 -> (b = true -> (♦∈ du)) ->
    forall {V dv}, stp Γ2 Σ V dv U du ->
              qstp (Γ1 ++ (b,V,dv) :: Γ2) Σ d1 d2.
  intros Γ1 b U du Γ2 Σ d1 d2 HST Hb. remember (Γ1 ++ (b,U,du) :: Γ2) as Γ.
  generalize dependent Γ1; induction HST; intros; subst; intuition.
  - constructor. auto. rewrite length_app in *. simpl in *. auto.
  - eapply qs_self; eauto. destruct (PeanoNat.Nat.lt_trichotomy f (‖Γ2‖)) as [Hlen | [Hlen | Hlen] ].
    * rewrite indexr_skips. rewrite indexr_skips in H.
      rewrite indexr_skip.  rewrite indexr_skip in H. eauto. all: simpl; lia.
    * subst. rewrite indexr_skips in H; auto. rewrite indexr_head in H. inversion H. subst.
      intuition. rewrite H1 in H3. discriminate.
    * rewrite indexr_skips'; auto. rewrite indexr_skips' in H; auto.
  - destruct (PeanoNat.Nat.lt_trichotomy x (‖Γ2‖)) as [Hlen | [Hlen | Hlen] ].
    * eapply qs_qvar; eauto. rewrite indexr_skips. rewrite indexr_skips in H.
      rewrite indexr_skip.  rewrite indexr_skip in H. eauto. 1-4: simpl; lia.
    * subst.  pose (H':=H). rewrite indexr_skips in H'. rewrite indexr_head in H'. inversion H'. subst.
      eapply qs_trans. eapply qs_qvar. rewrite indexr_skips; auto. apply indexr_head.
      1,2 : apply stp_closed in H3; intuition.
      apply stp_qstp_inv in H3. eapply qstp_non_fresh; eauto.
      apply stp_qstp_inv in H3. eapply weaken_qstp'. eapply weaken_qstp. auto. auto.
    * eapply qs_qvar; eauto. rewrite indexr_skips'; auto. rewrite indexr_skips' in H. eauto.
      simpl. lia.
  - eapply qs_cong; eauto. rewrite length_app in *. simpl in *. auto.
  - eapply qs_trans; eauto.
Qed.

Lemma narrowing_stp_gen : forall{Γ1 b U du Γ2 Σ T1 d1 T2 d2}, stp (Γ1 ++ (b,U,du) :: Γ2) Σ T1 d1 T2 d2 -> (b = true -> (♦∈ du)) ->
    forall {V dv}, (stp Γ2 Σ V dv U du) -> stp (Γ1 ++ (b,V,dv) :: Γ2) Σ T1 d1 T2 d2.
Proof. intros Γ1 b U du Γ2 Σ T1 d1 T2 d2 HST Hb. remember (Γ1 ++ (b,U,du) :: Γ2) as Γ.
  generalize dependent Γ1; induction HST; intros; intuition.
  - subst. constructor. eapply narrowing_qstp_gen; eauto.
  - subst. constructor. 1,4,5 : eapply narrowing_qstp_gen; eauto. auto. auto.
  - rewrite HeqΓ in *. constructor.
    subst. rewrite length_app in *. simpl in *. auto.
    subst. rewrite length_app in *. simpl in *. auto.
    eapply narrowing_qstp_gen; subst; eauto. eapply IHHST1; eauto.
    unfold open_ty' in *. unfold openq' in *.
    rewrite length_app in *. simpl in *.
    repeat rewrite app_comm_cons.
    eapply IHHST2; eauto.
  (* - subst. specialize (IHHST1 Γ1).  specialize (IHHST2 Γ1). intuition.
    specialize (H0 V dv).  specialize (H1 V dv). intuition.  eapply s_trans; eauto. *)
Qed.

Lemma narrowing_stp : forall{b U du Γ Σ T1 d1 T2 d2}, stp ((b,U,du) :: Γ) Σ T1 d1 T2 d2 -> (b = true -> (♦∈ du)) ->
    forall {V dv}, stp Γ Σ V dv U du -> stp ((b,V,dv) :: Γ) Σ T1 d1 T2 d2.
  intros. specialize (@narrowing_stp_gen [] b U du Γ Σ T1 d1 T2 d2) as narrow. simpl in *. eapply narrow; eauto.
Qed.

Lemma stp_change_q : forall {Γ Σ T1 d1 T2 d2}, stp Γ Σ T1 d1 T2 d2 -> forall {q1 q2}, qstp Γ Σ q1 q2 -> stp Γ Σ T1 q1 T2 q2.
  intros. induction H; constructor; auto.
Qed.

Lemma stp_shrink_var : forall {Γ Σ T1 d1 T2 d2}, stp Γ Σ T1 d1 T2 d2 -> forall {fr x}, x < ‖Γ‖ -> stp Γ Σ T1 ${fr}x T2 ${fr}x.
  intros. eapply stp_change_q; eauto. apply qs_sq; auto. apply just_fv_closed. auto.
Qed.

Lemma s_trans' : forall n T2, ty_size T2 < n -> forall Γ Σ T1 d1 d2 T3 d3,
  stp Γ Σ T1 d1 T2 d2 -> stp Γ Σ T2 d2 T3 d3 -> stp Γ Σ T1 d1 T3 d3.
  induction n; intros T2 Hsz; try lia; destruct T2; intros Γ Σ T1 d1 d2 T3 d3 H12 H23; inversion H12; inversion H23; subst; simpl in Hsz.
  - constructor; eauto.
  - constructor; eauto. eapply IHn; eauto. lia.
    assert (H13' : stp ((false, T8, d11) :: (true, TFun d0 d4 T0 T2, {♦}) :: Γ) Σ  (T2 <~²ᵀ Γ) (d4 <~²ᵈ Γ) (T2_2 <~²ᵀ Γ) (q0 <~²ᵈ Γ)). {
      eapply narrowing_stp; eauto. intuition. apply weaken_stp. auto. }
    assert (H28' : stp ((false, T8, d11) :: (true, TFun d0 d4 T0 T2, {♦}) :: Γ) Σ (T2_2 <~²ᵀ Γ) (q0 <~²ᵈ Γ) (T9 <~²ᵀ Γ) (d12 <~²ᵈ Γ)). {
      replace ((false, T8, d11) :: (true, TFun d0 d4 T0 T2, {♦}) :: Γ) with ([(false, T8, d11)] ++ ((true, TFun d0 d4 T0 T2, {♦}) :: Γ)); auto.
      eapply narrowing_stp_gen. eapply H28. intuition. eapply stp_change_q; eauto.
    }
    eapply IHn; eauto. unfold open_ty'. unfold open_ty. repeat rewrite <- open_ty_preserves_size. lia.
  - constructor; eauto. all: eapply IHn; eauto; lia.
Qed.

Lemma s_trans : forall Γ Σ T1 d1 T2 d2 T3 d3, stp Γ Σ T1 d1 T2 d2 -> stp Γ Σ T2 d2 T3 d3 -> stp Γ Σ T1 d1 T3 d3.
  intros. eapply s_trans'; eauto.
Qed.

Lemma stp_scale_qlub : forall {Γ Σ T1 d1 T2 d2}, stp Γ Σ T1 d1 T2 d2 -> forall {q}, closed_qual 0 (‖Γ‖) (‖Σ‖) q -> stp Γ Σ T1 (d1 ⊔ q) T2 (d2 ⊔ q).
  intros. eapply stp_change_q; eauto. apply stp_qstp_inv in H. rewrite qlub_commute. rewrite @qlub_commute with (d1:=d2). eauto.
Qed.

Lemma stp_scale_qqplus : forall {Γ Σ T1 d1 T2 d2}, stp Γ Σ T1 d1 T2 d2 -> forall {d}, closed_qual 0 (‖Γ‖) (‖Σ‖) d -> stp Γ Σ T1 (d1 ⋓ d) T2 (d2 ⋓ d).
  intros. destruct (♦∈? d1) eqn:fr1; destruct (♦∈? d2) eqn:fr2.
  - repeat rewrite qqplus_fresh; auto. apply stp_scale_qlub; auto.
  - apply stp_qstp_inv in H. specialize (qstp_non_fresh H fr2) as Hc. destruct d1. simpl in *.
    subst. discriminate.
  - rewrite @qqplus_fresh with (d:=d2); auto. unfold qqplus. rewrite fr1.
    eapply s_trans; eauto. apply stp_refl. apply stp_closed in H. intuition.
    apply qs_sq; auto. apply stp_closed in H. intuition. apply closed_qual_qlub; auto.
  - unfold qqplus. rewrite fr1. rewrite fr2. auto.
Qed.

Lemma saturated_cons : forall {Γ Σ q}, saturated Γ Σ q -> forall {b T q'}, saturated ((b, T, q') :: Γ) Σ q.
  intros. constructor; intros. unfold tenv_saturated. intros. apply H in H0. inversion H0.
  econstructor; eauto. rewrite indexr_skip; eauto. apply indexr_var_some' in H1. lia.
  inversion H. intuition.
Qed.

Lemma senv_saturated_conss : forall {Σ q}, senv_saturated Σ q -> forall {T q'}, senv_saturated ((T, q') :: Σ) q.
  intros. unfold senv_saturated. intros. apply H in H0. inversion H0. econstructor. rewrite indexr_skip.
  eauto. apply indexr_var_some' in H1. lia. all : auto.
Qed.

Lemma saturated_conss : forall {Γ Σ q}, saturated Γ Σ q -> forall {T q'}, saturated Γ ((T, q') :: Σ) q.
  intros. constructor; intros. unfold tenv_saturated. intros. apply H in H0. inversion H0. subst.
  econstructor; eauto. simpl. eapply closed_qual_monotone; eauto. unfold senv_saturated. intros.
  apply senv_saturated_conss; auto. inversion H. auto.
Qed.

Lemma saturated_app : forall {Γ' Γ Σ q}, saturated Γ Σ q -> saturated (Γ' ++ Γ) Σ q.
  induction Γ'; intros; simpl; intuition.
  apply saturated_cons; auto.
Qed.

Lemma saturated_apps : forall {Σ' Γ Σ q}, saturated Γ Σ q -> saturated Γ (Σ' ++ Σ) q.
  induction Σ'; intros; simpl; intuition.
  apply saturated_conss; auto.
Qed.

Lemma senv_saturated_app : forall {Σ' Σ q}, senv_saturated Σ q -> senv_saturated (Σ' ++ Σ) q.
  induction Σ'; intros; simpl; intuition.
  apply senv_saturated_conss; auto.
Qed.

Lemma wf_senv_prop : forall {Σ}, wf_senv Σ -> forall l T q, indexr l Σ = Some (T, q) -> (closed_ty 0 0 l T /\ closed_qual 0 0 l q /\ senv_saturated Σ q).
  intros Σ Hwf. induction Hwf; intros. simpl in H. discriminate. destruct (l =? ‖Σ‖) eqn:Heq.
  - simpl in H2. rewrite Heq in H2. inversion H2. subst. apply Nat.eqb_eq in Heq. subst. intuition.
    apply senv_saturated_conss. auto.
  - simpl in H2. rewrite Heq in H2. apply IHHwf in H2. intuition. apply senv_saturated_conss. auto.
Qed.

Lemma senv_saturated_empty : forall {Σ fr}, senv_saturated Σ ∅{ fr }.
  intros. unfold senv_saturated. intros. simpl in H. apply NatSetNotin.notin_empty in H; contradiction.
Qed.
#[global] Hint Resolve senv_saturated_empty : core.

Lemma tenv_saturated_empty : forall {Γ Σ fr}, tenv_saturated Γ Σ ∅{ fr }.
  intros. unfold tenv_saturated. intros. simpl in H. apply NatSetNotin.notin_empty in H; contradiction.
Qed.
#[global] Hint Resolve tenv_saturated_empty : core.

Lemma saturated_empty : forall {Γ Σ fr}, saturated Γ Σ ∅{ fr }.
  intuition.
Qed.
#[global] Hint Resolve saturated_empty : core.

Lemma senv_saturated_just_fv : forall {Σ fr x}, senv_saturated Σ ${fr}x.
  intros. unfold senv_saturated. intros. simpl in H. apply NatSetNotin.notin_empty in H. contradiction.
Qed.
#[global] Hint Resolve senv_saturated_just_fv : core.

Lemma tenv_saturated_empty_tenv : forall {Σ q}, closed_qual 0 0 (‖Σ‖) q -> tenv_saturated [] Σ q.
  intros. unfold tenv_saturated. intros. inversion H. subst. apply bound_0_empty in H1,H2.
  subst. simpl in *. apply NatSetNotin.notin_empty in H0. contradiction.
Qed.
#[global] Hint Resolve tenv_saturated_empty_tenv : core.

Lemma senv_saturated_open_qual : forall {Σ d1 d2}, senv_saturated Σ d1 -> forall {k}, senv_saturated Σ ([[ k ~> ∅ ]]ᵈ d2) -> senv_saturated Σ ([[ k ~> d1 ]]ᵈ d2).
  intros. destruct d1. destruct d2. simpl in *.
  destruct (mem k t3) eqn:Hmem; intuition.
  repeat rewrite empty_union_right in H0. rewrite orb_false_r in H0.
  unfold senv_saturated in *. intros. simpl in *. specialize (H l). specialize (H0 l).
  assert (Hl : In l t4 \/ In l t1). fnsetdec. intuition.
  * inversion H3. econstructor; eauto. eapply subqual_trans; eauto. qdec.
  * inversion H3. econstructor; eauto. eapply subqual_trans; eauto. qdec.
Qed.

Lemma senv_saturated_openq : forall {f Σ df d1 d2},
    senv_saturated Σ df -> closed_qual 0 f (‖Σ‖) df ->
    senv_saturated Σ d1 -> closed_qual 0 f (‖Σ‖) d1 -> senv_saturated Σ (openq ∅ ∅ d2) -> senv_saturated Σ (openq df d1 d2).
    intros. unfold openq in *. apply senv_saturated_open_qual; auto.
    erewrite open_qual_commute''; eauto. erewrite open_qual_commute'' in H3; eauto.
    eapply senv_saturated_open_qual; auto. Unshelve. all: apply 0.
Qed.

Lemma saturated_senv_qlub : forall {Σ q1 q2}, senv_saturated Σ q1 -> senv_saturated Σ q2 -> senv_saturated Σ (q1 ⊔ q2).
  intros. unfold senv_saturated in *. intros. specialize (H l). specialize (H0 l).
  destruct q1. destruct q2. simpl in *. assert (In l t1 \/ In l t4). fnsetdec. intuition.
  - inversion H2. subst. econstructor; eauto. eapply subqual_trans; eauto. qdec.
  - inversion H2. subst. econstructor; eauto. eapply subqual_trans; eauto. qdec.
Qed.
#[global] Hint Resolve saturated_senv_qlub : core.

Lemma saturated_qlub : forall {Γ Σ q1 q2}, saturated Γ Σ q1 -> saturated Γ Σ q2 -> saturated Γ Σ (q1 ⊔ q2).
  intros. inversion H. inversion H0. constructor; auto.
  unfold tenv_saturated in *. intros. specialize (H1 x). specialize (H3 x).
  rewrite qmem_lub_or_commute in H5. intuition.
  - inversion H5. subst. econstructor; eauto. eapply subqual_trans; eauto.
  - inversion H5. subst. econstructor; eauto. eapply subqual_trans; eauto.
Qed.
#[global] Hint Resolve saturated_qlub : core.

Lemma senv_saturated_qqplus : forall {Σ q1 q2}, senv_saturated Σ q1 -> senv_saturated Σ q2 -> senv_saturated Σ (q1 ⋓ q2).
  intros. destruct q1. destruct b; unfold qqplus. rewrite qfresh_true. auto.
  rewrite qfresh_false. auto.
Qed.
#[global] Hint Resolve senv_saturated_qqplus : core.

Lemma saturated_qqplus : forall {Γ Σ q1 q2}, saturated Γ Σ q1 -> saturated Γ Σ q2 -> saturated Γ Σ (q1 ⋓ q2).
  intros. destruct q1. destruct b; unfold qqplus. rewrite qfresh_true. apply saturated_qlub; auto.
  rewrite qfresh_false. auto.
Qed.
#[global] Hint Resolve saturated_qqplus : core.

Lemma saturated_senv_qglb : forall {Σ q1 q2}, senv_saturated Σ q1 -> senv_saturated Σ q2 -> senv_saturated Σ (q1 ⊓ q2).
  intros. unfold senv_saturated in *. intros. specialize (H l). specialize (H0 l).
  rewrite qmem_glb_and_commute in H1. intuition.
  inversion H. inversion H1. subst. econstructor; eauto. rewrite H0 in H6. inversion H6. subst.
  rewrite qlub_qglb_dist_r. apply qglb_bound; auto.
Qed.
#[global] Hint Resolve saturated_senv_qglb : core.

Lemma saturated_qglb : forall {Γ Σ q1 q2}, saturated Γ Σ q1 -> saturated Γ Σ q2 -> saturated Γ Σ (q1 ⊓ q2).
  intros. inversion H. inversion H0. constructor; auto. unfold tenv_saturated in *. intros.
  rewrite qmem_glb_and_commute in H5. specialize (H1 x). specialize (H3 x). intuition.
  inversion H5. inversion H1. subst. econstructor; eauto. rewrite H3 in H10. inversion H10. subst.
  apply qglb_bound; auto.
Qed.
#[global] Hint Resolve saturated_qglb : core.

Lemma weaken_store_senv_saturated : forall {Σ q}, senv_saturated Σ q -> forall {Σ'}, Σ' ⊇ Σ -> senv_saturated Σ' q.
  intros. unfold senv_saturated. intros.
  apply H in H1. inversion H1. econstructor; eauto. unfold extends in H0. destruct H0 as [Σ'' Hs].
  subst. rewrite indexr_skips. eauto. apply indexr_var_some' in H2. lia.
Qed.

Lemma weaken_store_tenv_saturated : forall {Γ Σ q}, tenv_saturated Γ Σ q -> forall {Σ'}, Σ' ⊇ Σ -> tenv_saturated Γ Σ' q.
  intros. unfold tenv_saturated. intros. apply H in H1. inversion H1. econstructor; eauto. eapply closed_qual_monotone; eauto.
Qed.

Lemma weaken_store_saturated : forall {Γ Σ q}, saturated Γ Σ q -> forall {Σ'}, Σ' ⊇ Σ -> saturated Γ Σ' q.
  intros. inversion H. constructor. eapply weaken_store_tenv_saturated; eauto. eapply weaken_store_senv_saturated; eauto.
Qed.

Fixpoint has_type_closed  {Γ φ Σ t T d} (ht : has_type Γ φ Σ t T d) :
  closed_qual 0 (‖Γ‖) (‖Σ‖) φ /\
  closed_tm 0 (‖Γ‖) (‖Σ‖) t /\
  closed_ty 0 (‖Γ‖) (‖Σ‖) T /\
  closed_qual 0 (‖Γ‖) (‖Σ‖) d.
Proof.
  destruct ht; intuition; try apply has_type_closed in ht; try apply has_type_closed in ht1;
    try apply has_type_closed in ht2; intuition; eauto.
  9,10 : try (apply closed_qual_qlub; auto); eauto.
  - constructor. apply indexr_var_some' in H. auto.
  - apply indexr_var_some' in H. eapply closed_ty_monotone; eauto. lia.
  (* - apply stp_closed in H; intuition. *)
  - inversion H6. subst. unfold open_ty.
    eapply closed_ty_open2; eauto.
  - inversion H6. subst. unfold openq.
    eapply closed_qual_open2; eauto.
  - inversion H12. subst. unfold open_ty.
    eapply closed_ty_open2; eauto.
  - inversion H12. subst. unfold openq.
    eapply closed_qual_open2; eauto.
  - constructor. apply indexr_var_some' in H0. auto.
  - econstructor. eapply closed_ty_monotone; eauto; lia.
    eapply closed_qual_monotone; eauto; lia.
  - inversion H3. subst. auto.
  - apply stp_closed in H. intuition.
Qed.

Lemma open_qual_subqual : forall {d1 d2 φ}, d1 ⊑ φ -> forall {k}, ([[ k ~> ∅ ]]ᵈ d2) ⊑ φ -> ([[ k ~> d1 ]]ᵈ d2) ⊑ φ.
  intros. destruct d1. destruct d2. destruct φ. simpl in *. intuition.
  destruct (mem k t3) eqn:Hmem; simpl in *; intuition; try fnsetdec. destr_bool.
Qed.

Lemma openq_subqual : forall {df d1 d2 φ f l}, closed_qual 0 f l φ -> df ⊑ φ -> d1 ⊑ φ -> d2 <~ᵈ ∅; ∅ ⊑ φ -> d2 <~ᵈ df; d1 ⊑ φ.
  intros. unfold openq in *. apply open_qual_subqual; auto. erewrite open_qual_commute''; eauto.
  erewrite open_qual_commute'' in H2; eauto. apply open_qual_subqual; auto.
  Unshelve. all : apply 0.
Qed.

Fixpoint has_type_filter {Γ φ Σ t T d} (ht : has_type Γ φ Σ t T d) : d ⊑ φ.
  destruct ht; intuition. 1,2: specialize (has_type_closed ht1) as Hc; intuition; eapply openq_subqual; eauto.
  apply qlub_bound; auto. apply qlub_bound; auto. apply has_type_filter in ht. auto.
Qed.

Lemma closed_qual_qmem_fv : forall {b f l q}, closed_qual b f l q -> forall {x}, $x ∈ᵥ q -> x < f.
  intros. specialize (@subqual_just_fv_bound x q) as Hx. destruct q. inversion H. subst.
  simpl in *. intuition.
  assert (Hsub  : Subset (singleton x) t). fnsetdec.
  assert (Hsub' : Subset {}N t0). fnsetdec.
  assert (Hsub'': Subset {}N t1). fnsetdec.
  intuition.
Qed.

Lemma bound_vars_untypable : forall {Γ φ Σ T d i}, has_type Γ φ Σ #i T d -> False.
  intros Γ φ Σ T d i HT. remember (tvar #i) as t. induction HT; try discriminate; intuition.
Qed.

Lemma splice_senv_saturated : forall {Σ d1}, senv_saturated Σ d1 -> forall {k}, senv_saturated Σ (d1 ↑ᵈ k).
  intros. unfold senv_saturated in *. destruct d1. simpl in *. intros. apply H in H0.
  inversion H0. econstructor; eauto. inversion H3. subst. apply bound_0_empty in H4, H5. subst. qdec.
Qed.
#[global] Hint Resolve splice_senv_saturated : core.

Lemma weaken_tenv_saturated : forall {Γ1 Γ2 Σ d1},
    tenv_saturated (Γ1 ++ Γ2) Σ d1 -> forall X, tenv_saturated ((Γ1 ↑ᴳ ‖Γ2‖) ++ X :: Γ2) Σ (d1 ↑ᵈ ‖Γ2‖).
  intros. unfold tenv_saturated in *. intros. bdestruct (x <? ‖Γ2‖).
  - apply splice_qual_mem_lt in H0; auto. apply H in H0. inversion H0.
    rewrite indexr_skips in H2; try lia. apply (sat_var b U q'); auto.
    rewrite indexr_skips. rewrite indexr_skip; auto. lia. simpl. lia.
    replace q' with (q' ↑ᵈ ‖Γ2‖). apply subqual_splice_lr'. auto.
    eapply splice_qual_id. eapply closed_qual_monotone; eauto. lia.
  - bdestruct (x =? ‖Γ2‖).
    * subst. apply splice_qual_not_mem in H0. contradiction.
    * destruct x. lia. assert (Hx : x >= ‖Γ2‖). lia.
      specialize (splice_qual_mem_ge Hx H0) as Hxd1. apply H in Hxd1.
      inversion Hxd1. econstructor. rewrite <- indexr_insert_ge.
      eapply indexr_splice_tenv. eauto. lia. lia. rewrite subqual_splice_lr'. auto.
      apply splice_qual_closed''; auto.
Qed.
#[global] Hint Resolve weaken_tenv_saturated : core.

Lemma weaken_saturated : forall {Γ1 Γ2 Σ d1},
    saturated (Γ1 ++ Γ2) Σ d1 -> forall X, saturated ((Γ1 ↑ᴳ ‖Γ2‖) ++ X :: Γ2) Σ (d1 ↑ᵈ ‖Γ2‖).
  intros. inversion H. intuition.
Qed.
#[global] Hint Resolve weaken_saturated : core.

Lemma splice_qual_injective : forall {k q q'}, q ↑ᵈ k = q' ↑ᵈ k -> q = q'.
  intros. destruct q. destruct q'. simpl in *. inversion H. subst.
  f_equal. eapply splice_set_injective; eauto.
Qed.

Lemma splice_ty_injective : forall {T T' k}, T ↑ᵀ k = T' ↑ᵀ k -> T = T'.
  induction T; intros; intuition; destruct T'; simpl in H; intuition; try discriminate.
  - inversion H. apply splice_qual_injective in H1, H2. subst.
    specialize (IHT1 T'1 k). specialize (IHT2 T'2 k). intuition. subst. auto.
  - inversion H. apply splice_qual_injective in H1. subst.
    specialize (IHT T' k). intuition. subst. auto.
Qed.

Lemma not_free_splice_ty_iff : forall {v k T}, not_free v T <-> not_free v (T ↑ᵀ k).
  intros v k. unfold not_free. intros. intuition.
  - replace (∅) with (∅ ↑ᵈ k); auto. rewrite <- splice_ty_open_rec_ty. rewrite H. auto.
  - replace (∅) with (∅ ↑ᵈ k) in H; auto. rewrite <- splice_ty_open_rec_ty in H.
    eapply splice_ty_injective; eauto.
Qed.

Lemma weaken_gen : forall {t Γ1 Γ2 φ Σ T d},
    has_type (Γ1 ++ Γ2) φ Σ t T d ->
    forall X, has_type ((Γ1 ↑ᴳ ‖Γ2‖) ++ X :: Γ2) (φ ↑ᵈ ‖Γ2‖) Σ (t ↑ᵗ ‖Γ2‖) (T ↑ᵀ ‖Γ2‖) (d ↑ᵈ ‖Γ2‖).
  intros t Γ1 Γ2 φ Σ T d HT. remember (Γ1 ++ Γ2) as Γ. generalize dependent Γ1. generalize dependent Γ2.
  induction HT; intros; subst.
  - (* tunit *) simpl. rewrite splice_set_empty.
    constructor. eapply splice_qual_closed'.
    rewrite length_app in *. rewrite splice_tenv_length. auto.
    - (* t_var *) simpl.
    destruct (le_lt_dec (‖Γ2‖) x) eqn:Heq.
    * (* |Γ2| <= x < |Γ1|+|Γ2|*)
      rewrite splice_set_singleton_inc; auto. apply t_var with (b:=b) (d:=d ↑ᵈ ‖Γ2‖).
      rewrite <- indexr_insert_ge. apply indexr_splice_tenv; eauto. lia.
      erewrite <- splice_qual_just_fv_ge; eauto.
      rewrite subqual_splice_lr'. auto.
      eapply splice_qual_closed'.
      rewrite length_app in *. rewrite splice_tenv_length. auto.
      eapply splice_ty_closed''; eauto. eapply splice_qual_closed''; eauto.
    * (* |Γ2| > x *)
      rewrite indexr_skips in H; auto. rewrite splice_set_singleton_inv; auto.
      apply t_var with (b:=b) (d:=d).
      rewrite <- indexr_insert_lt; auto. rewrite indexr_skips; auto.
      erewrite splice_ty_id. auto.
      eapply closed_ty_monotone; eauto. lia.
      erewrite <- splice_qual_just_fv_lt; eauto.
      rewrite subqual_splice_lr'. auto.
      eapply splice_qual_closed'.
      rewrite length_app in *. rewrite splice_tenv_length. auto.
      erewrite splice_ty_id; eauto. eapply closed_ty_monotone; eauto. lia. auto.
  - (* t_abs *) rewrite length_app in *. simpl. constructor; auto.
    apply splice_closed'.
    1-3: rewrite length_app; rewrite splice_tenv_length; simpl;
      replace (‖Γ1‖ + S (‖Γ2‖)) with (S (‖Γ1‖ + ‖Γ2‖)); eauto.
    inversion H0. subst. constructor. 1,2,5: apply splice_qual_closed; auto. 1,2 : apply splice_ty_closed; auto.
    rewrite subqual_splice_lr'. auto. rewrite <- not_fresh_splice_iff. auto.
    rewrite app_comm_cons.
    replace ((false, T1 ↑ᵀ ‖Γ2‖, d1 ↑ᵈ ‖Γ2‖)
                :: ((true, TFun (d1 ↑ᵈ ‖Γ2‖) (d2 ↑ᵈ ‖Γ2‖) (T1 ↑ᵀ ‖Γ2‖) (T2 ↑ᵀ ‖Γ2‖), df ↑ᵈ ‖Γ2‖)
                      :: (Γ1 ↑ᴳ ‖Γ2‖)) ++ X :: Γ2)
            with ((((false,T1, d1) :: (true, TFun d1 d2 T1 T2, df) :: Γ1) ↑ᴳ ‖Γ2‖) ++ X :: Γ2).
    replace ((df ↑ᵈ ‖Γ2‖) ⊔ $!(‖(Γ1 ↑ᴳ ‖Γ2‖) ++ X :: Γ2‖) ⊔ $!(S (‖(Γ1 ↑ᴳ ‖Γ2‖) ++ X :: Γ2‖)) ⊔ {♦})
      with  ((df ⊔ $!(‖Γ1‖ + ‖Γ2‖) ⊔ $!(S (‖Γ1‖ + ‖Γ2‖)) ⊔ {♦}) ↑ᵈ ‖Γ2‖).
    rewrite <- splice_open'. rewrite <- splice_ty_open'. rewrite <- splice_qual_open'.
    rewrite @open_tm'_len with (Γ':=(Γ1 ++ Γ2)). rewrite @open_ty'_len with (Γ':=(Γ1 ++ Γ2)).
    rewrite @openq'_len with (Γ':=(Γ1 ++ Γ2)).
    apply IHHT; intuition. 1-4 : repeat rewrite length_app; rewrite splice_tenv_length; auto.
    repeat rewrite splice_qual_lub_dist. rewrite splice_qual_fresh. simpl.
    f_equal. repeat rewrite splice_set_singleton_inc; try lia; repeat f_equal; lia.
    simpl. auto.
  - (* t_app *) simpl. rewrite splice_qual_open''. rewrite splice_ty_open''. rewrite splice_qual_empty. apply t_app with (T1:=T1 ↑ᵀ ‖Γ2‖) (df:=df ↑ᵈ ‖Γ2‖).
    apply IHHT1; auto.
    apply IHHT2; auto.
    rewrite <- @splice_qual_empty with (k := ‖Γ2‖); rewrite <- splice_qual_open''.
    rewrite subqual_splice_lr'; auto. rewrite <- not_fresh_splice_iff. auto.
    replace ((d2 ↑ᵈ (‖ Γ2 ‖)) <~ᵈ ∅; ∅) with ((d2 <~ᵈ ∅; ∅) ↑ᵈ (‖ Γ2 ‖)); auto.
    rewrite splice_qual_open''. f_equal; auto. rewrite <- not_free_splice_ty_iff. auto.
  - (* t_app_fresh *) simpl. rewrite splice_qual_open''. rewrite splice_ty_open''. rewrite splice_qual_empty.
    apply t_app_fresh with (T1:=T1 ↑ᵀ ‖Γ2‖) (d1:=d1 ↑ᵈ ‖Γ2‖) (df:=df ↑ᵈ ‖Γ2‖) (d1':=d1' ↑ᵈ ‖Γ2‖) (df':=df' ↑ᵈ ‖Γ2‖); auto.
    replace (TFun ((df' ↑ᵈ (‖ Γ2 ‖) ⋒ d1' ↑ᵈ (‖ Γ2 ‖))) (d2 ↑ᵈ (‖ Γ2 ‖)) (T1 ↑ᵀ (‖ Γ2 ‖)) (T2 ↑ᵀ (‖ Γ2 ‖)))
       with ((TFun (df' ⋒ d1') d2 T1 T2) ↑ᵀ (‖ Γ2 ‖)). auto.
    simpl. rewrite splice_qual_qlub_dist. rewrite splice_qual_fresh. rewrite splice_qual_glb_dist. auto.
    1,2 : rewrite subqual_splice_lr'; auto.
    intros Hfresh. rewrite <- fresh_splice_iff in Hfresh. rewrite <- not_free_splice_ty_iff. auto.
    rewrite <- not_free_splice_ty_iff. auto.
    rewrite <- @splice_qual_empty with (k := ‖Γ2‖); rewrite <- splice_qual_open''.
    1-3 : rewrite subqual_splice_lr'; auto.
    replace ((d2 ↑ᵈ (‖ Γ2 ‖)) <~ᵈ ∅; ∅) with ((d2 <~ᵈ ∅; ∅) ↑ᵈ (‖ Γ2 ‖)); auto.
    rewrite splice_qual_open''. f_equal; auto.
  - (* t_loc *) simpl. rewrite splice_qual_qlub_dist. simpl. rewrite splice_set_empty. apply t_loc. eapply splice_qual_closed'.
    rewrite length_app in *. rewrite splice_tenv_length. auto.
    erewrite splice_ty_id; eauto. erewrite splice_qual_id; eauto. eapply closed_qual_monotone; eauto. lia. eapply closed_ty_monotone; eauto. lia.
    erewrite splice_ty_id; eauto. eapply closed_ty_monotone; eauto. lia.
    erewrite splice_qual_id; eauto. eapply closed_qual_monotone; eauto. lia.
    destruct φ. simpl in *. intuition. apply subqual_splice_lr'. auto. rewrite <- not_fresh_splice_iff. auto.
  - (* t_ref *) simpl in *. specialize (IHHT Γ2 Γ1). intuition.
    specialize (H2 (a0, b0, b)). destruct d1. repeat rewrite empty_union_left.
    replace (qset true t0 t1 t2) with ({♦} ⊔ (qset b1 t0 t1 t2)); try qdec.
    rewrite splice_qual_qlub_dist. rewrite splice_qual_fresh. apply t_ref; auto.
    apply has_type_closed in H2. intuition.
    destruct φ. intuition. subst. simpl. intuition.
  - (* t_deref *) simpl. econstructor; eauto. rewrite <- not_fresh_splice_iff. auto. apply subqual_splice_lr'. auto.
  - (* t_assign *) simpl. specialize (IHHT1 Γ2 Γ1). specialize (IHHT2 Γ2 Γ1). intuition.
    specialize (H0 (a0,b0,b)). specialize (H1 (a0,b0,b)). simpl in *. rewrite splice_set_empty in *.
    eapply t_assign; eauto. rewrite <- not_fresh_splice_iff. auto.
  - (* t_sub *) eapply t_sub. eapply IHHT; auto.
    apply @weaken_stp_gen; eauto; lia. apply subqual_splice_lr'. auto. auto.
Qed.

Lemma weaken_flt : forall {Γ φ Σ t T d},
    has_type Γ φ Σ t T d ->
    forall {φ'}, φ ⊑ φ' -> closed_qual 0 (‖Γ‖) (‖Σ‖) φ' ->
    has_type Γ φ' Σ t T d.
  intros Γ φ Σ t T d HT.
  induction HT; intros; try solve [econstructor; eauto; try solve [eapply subqual_trans; eauto]].
Qed.

Lemma weaken : forall {φ Σ t T d},
    has_type [] φ Σ t T d -> forall {Γ}, has_type Γ φ Σ t T d.
  intros φ Σ t T d HT. induction Γ; auto.
  specialize (@weaken_gen t [] Γ φ Σ T d) as Hsp. simpl in *.
  specialize (Hsp IHΓ a).
  apply has_type_closed in HT. intuition. simpl in *.
  replace (splice (‖Γ‖) t) with t in Hsp.
  replace (splice_ty (‖Γ‖) T) with T in Hsp.
  replace (splice_qual (‖Γ‖) d) with d in Hsp.
  replace (splice_qual (‖Γ‖) φ) with φ in Hsp. auto.
  all : symmetry.
  eapply splice_qual_id; eauto. eapply closed_qual_monotone; eauto; lia.
  eapply splice_qual_id; eauto. eapply closed_qual_monotone; eauto; lia.
  eapply splice_ty_id; eauto.   eapply closed_ty_monotone; eauto; lia.
  eapply splice_id; eauto.      eapply closed_tm_monotone; eauto; lia.
Qed.

Lemma weaken' : forall {φ Σ t T d},
    has_type [] φ Σ t T d -> forall {φ'}, φ ⊑ φ' -> forall {Γ}, closed_qual 0 (‖Γ‖) (‖Σ‖) φ' -> has_type Γ φ' Σ t T d.
  intros. eapply weaken_flt; eauto. apply weaken. auto.
Qed.

Lemma weaken_store : forall {Γ φ Σ t T d}, has_type Γ φ Σ t T d -> forall {Σ'}, Σ' ⊇ Σ -> has_type Γ φ Σ' t T d.
  intros Γ φ Σ t T d HT.
  induction HT; intros; intuition; try solve [econstructor; eauto;
    try solve [eapply closed_qual_monotone; eauto; apply extends_length; auto];
    try solve [eapply closed_tm_monotone; eauto; apply extends_length; auto];
    try solve [eapply closed_ty_monotone; eauto; apply extends_length; auto];
    try solve [eapply weaken_store_saturated; eauto];
    try solve [eapply weaken_store_senv_saturated; eauto]].
  - econstructor; eauto. eapply closed_qual_monotone; eauto; apply extends_length; auto.
    unfold extends in H6. destruct H6. rewrite H6.
    rewrite indexr_skips. auto. eapply indexr_var_some'. eauto.
    eapply closed_ty_monotone; eauto.
    eapply closed_qual_monotone; eauto.
  - econstructor; eauto. eapply weaken_stp_store_ext; eauto.
    eapply weaken_store_senv_saturated; eauto.
Qed.

Lemma qstp_empty : forall {Σ q1 q2}, qstp [] Σ q1 q2 -> q1 ⊑ q2.
  intros. remember [] as Γ. induction H; subst; auto.
  simpl in H. discriminate.
  simpl in H. discriminate.
  intuition. eapply subqual_trans; eauto.
Qed.

Lemma narrowing_saturated : forall {Γ1 b U du Γ2 Σ q},
    saturated (Γ1 ++ (b,U,du) :: Γ2) Σ q ->
    forall {V dv}, stp [] Σ V dv U du -> saturated (Γ1 ++ (b,V,dv) :: Γ2) Σ q.
  intros. inversion H. constructor; intros; auto. unfold tenv_saturated. intros.
  apply H1 in H3. inversion H3. destruct (PeanoNat.Nat.lt_trichotomy x (‖Γ2‖)) as [Hlen | [Hlen | Hlen] ].
  - apply (sat_var b0 U0 q'); auto. rewrite indexr_skips in H4; simpl; auto.
    rewrite indexr_skips. rewrite indexr_skip in H4; try lia. rewrite indexr_skip; try lia.
    auto. simpl. auto.
  - rewrite indexr_skips in H4; simpl; auto. subst. rewrite indexr_head in H4. inversion H4. subst.
    apply (sat_var b0 V dv). rewrite indexr_skips; auto. rewrite indexr_head. auto.
    apply stp_qstp_inv in H0. apply qstp_empty in H0. eapply subqual_trans; eauto.
    apply stp_closed in H0. intuition. eapply closed_qual_monotone; eauto. lia.
  - destruct x. lia. rewrite <- indexr_insert_ge in H4; try lia.
    apply (sat_var b0 U0 q'); auto. rewrite <- indexr_insert_ge; try lia. auto.
Qed.

Lemma narrowing_gen : forall {t Γ1 b U du Γ2 φ Σ T d},
    has_type (Γ1 ++ (b,U,du) :: Γ2) φ Σ t T d -> (b = true -> (♦∈ du)) ->
    forall {V dv}, stp [] Σ V dv U du -> has_type (Γ1 ++ (b,V,dv) :: Γ2) φ Σ t T d.
  intros t Γ1 b U du Γ2 φ Σ T d HT Hb. remember (Γ1 ++ (b,U, du) :: Γ2) as Γ.
  generalize dependent Γ1. generalize dependent U. generalize dependent du. generalize dependent Γ2.
  induction HT; intros; subst.
  - econstructor; eauto.
    repeat rewrite length_app in *; simpl in *; auto.
  - repeat rewrite length_app in *; simpl in *; auto.
    destruct (PeanoNat.Nat.lt_trichotomy x (‖Γ2‖)) as [Hlen | [Hlen | Hlen] ].
    * apply t_var with (b:=b0) (d:=d); auto. rewrite <- indexr_insert_lt; auto. rewrite <- indexr_insert_lt in H; auto.
      repeat rewrite length_app in *; simpl in *; auto.
    * subst. rewrite indexr_insert in H. inversion H. subst.
      apply t_sub with (T1:=V) (d1:=$!‖Γ2‖); auto. apply t_var with (b:=b0) (d:=dv).
      rewrite indexr_insert. auto. destruct φ. simpl. auto.
      repeat rewrite length_app in *; simpl in *; auto.
      1,2 : apply stp_closed in H4; intuition. eapply closed_ty_monotone; eauto. eapply closed_qual_monotone; eauto.
      eapply stp_shrink_var; eauto. eapply weaken_stp'; eauto. eapply weaken_stp; eauto.
      replace Γ2 with (Γ2 ++ []). eapply weaken_stp'; eauto. rewrite app_nil_r. auto. rewrite length_app. simpl. lia.
    * apply t_var with (b:=b0) (d:=d); auto. destruct x. lia. rewrite <- indexr_insert_ge; try lia.
      rewrite <- indexr_insert_ge in H; try lia. auto.
      repeat rewrite length_app in *; simpl in *; auto.
  - repeat rewrite length_app in *; simpl in *; auto.
    constructor; auto. 1-3 : rewrite length_app in *; simpl in *; auto.
    rewrite @open_tm'_len with (Γ' := (Γ1 ++ (b,U, du) :: Γ2)).
    rewrite @open_ty'_len with (Γ' := (Γ1 ++ (b,U, du) :: Γ2)).
    rewrite @openq'_len with (Γ' := (Γ1 ++ (b,U, du) :: Γ2)).
    2-4 : repeat rewrite length_app; simpl; auto.
    rewrite length_app. simpl.
    rewrite app_comm_cons. rewrite app_comm_cons.
    eapply IHHT; eauto. simpl. auto.
  - econstructor; eauto.
  - eapply t_app_fresh; eauto.
    repeat rewrite length_app in *; simpl in *; auto.
    all: eapply narrowing_saturated; eauto.
  - econstructor; eauto.
    repeat rewrite length_app in *; simpl in *; auto.
  - econstructor; eauto. repeat rewrite length_app in *; simpl in *; auto.
  - econstructor; eauto.
  - econstructor; eauto.
  - eapply t_sub; eauto. eapply narrowing_stp_gen; eauto.
    replace (Γ2) with (Γ2 ++ []). eapply weaken_stp'; eauto. rewrite app_nil_r. auto.
Qed.

Lemma narrowing : forall {Γ b U du φ Σ t T d}, has_type ((b,U,du) :: Γ) φ Σ t T d -> (b = true -> (♦∈ du)) -> forall {V dv}, stp [] Σ V dv U du -> has_type ((b,V,dv) :: Γ) φ Σ t T d.
  intros. specialize (@narrowing_gen t [] b U du Γ φ Σ T d) as narrow. simpl in *. eapply narrow; eauto.
Qed.

Lemma values_stuck : forall {v}, value v -> forall {t σ σ'}, step v σ t σ' -> False.
  intros. inversion H0; subst; inversion H.
Qed.

Lemma CtxOK_ext : forall {Γ φ Σ σ}, CtxOK Γ φ Σ σ -> forall {v T q}, has_type Γ φ Σ v T q -> value v -> CtxOK Γ φ ((T,q) :: Σ) (v :: σ).
  intros. unfold CtxOK in *. split. simpl. lia.
  intros. destruct H as [Hlen Hprev]. destruct (Nat.eqb l (length σ)) eqn:Heql.
  - simpl in *. rewrite Heql in *. inversion H3. subst.
    rewrite <- Hlen in Heql. rewrite Heql in H2. inversion H2. subst. intuition.
    eapply weaken_store; eauto.
  - simpl in *. rewrite Heql in *. rewrite <- Hlen in Heql. rewrite Heql in H2.
    specialize (Hprev _ _ _ _ H2 H3) as Hprev. intuition.
    eapply weaken_store; eauto.
Qed.

Lemma CtxOK_update : forall {Γ φ Σ σ}, CtxOK Γ φ Σ σ -> forall {l T q}, l < ‖σ‖ -> indexr l Σ = Some (T,q) -> forall {v}, has_type Γ φ Σ v T q -> value v -> CtxOK Γ φ Σ (update σ l v).
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

Lemma CtxOK_weaken_flt : forall {Γ φ Σ σ}, CtxOK Γ φ Σ σ -> forall {φ'}, closed_qual 0 (‖Γ‖) (‖Σ‖) φ' -> φ ⊑ φ' -> CtxOK Γ φ' Σ σ.
  intros. inversion H. subst. constructor; intuition.
  all : specialize (H3 _ _ _ _ H4 H5); intuition.
  eapply weaken_flt; eauto.
Qed.

Lemma subst1_tenv_length : forall {v q Γ}, ‖ { v |-> q }ᴳ Γ ‖ = ‖Γ‖.
  intros. unfold subst_tenv. rewrite length_map. auto.
Qed.

Lemma subst_tenv_length : forall {v q q' Γ}, ‖ { v |-> q ; q' }ᴳ Γ ‖ = ‖Γ‖.
  intros. repeat rewrite subst1_tenv_length. auto.
Qed.

Lemma subst1_qual_id : forall {b l q}, closed_qual b 0 l q -> forall {q1}, { 0 |-> q1 }ᵈ q = q.
Proof.
  intros. inversion H; subst; intros; intuition. simpl.
  rewrite bound_le_mem_false. 2: lia.
  erewrite unsplice_set_inv; eauto; apply bound_0_empty in H0; subst; rewrite remove_empty; auto.
Qed.

Lemma subst1_qual_empty : forall {dx}, {0 |-> dx }ᵈ ∅ = ∅.
  intros. apply (@subst1_qual_id 0 0). auto.
Qed.
#[global] Hint Resolve subst1_qual_empty : core.

Lemma subst1_qual_fresh : forall {dx}, {0 |-> dx }ᵈ {♦} = {♦}.
  intros. apply (@subst1_qual_id 0 0). auto.
Qed.
#[global] Hint Resolve subst1_qual_fresh : core.

Lemma subst1_ty_id : forall {T b l}, closed_ty b 0 l T -> forall {d1}, { 0 |-> d1 }ᵀ T = T.
  induction T; intros; inversion H; subst; simpl; intuition.
  erewrite IHT1; eauto. erewrite IHT2; eauto.
  erewrite subst1_qual_id; eauto. erewrite subst1_qual_id; eauto.
  erewrite IHT; eauto. erewrite subst1_qual_id; eauto.
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
      [[k ~> d1 ]]ᵈ q = { 0 |-> d1 }ᵈ ([[k ~> $!0 ]]ᵈ q).
  intros. inversion H; subst; intuition. simpl.
  destruct d1.
  rewrite empty_union_right. rewrite empty_union_right.
  destruct (mem k bs) eqn: Hmem. simpl.
  assert (mem 0 (union vs (singleton 0)) = true).
  apply NatSet.F.mem_1. fnsetdec.
  rewrite H3. f_equal. destr_bool. apply bound_0_empty in H0. rewrite H0.
  rewrite empty_union_left. rewrite empty_union_left.
  rewrite remove_singleton_empty. rewrite unsplice_set_empty.
  rewrite empty_union_left. auto.
  simpl. rewrite bound_le_mem_false; auto.
  apply bound_0_empty in H0. subst.
  rewrite unsplice_set_empty. auto.
Qed.

Lemma open_subst1_ty : forall {T b l},
    closed_ty b 0 l T ->
    forall {k d1},
      [[k ~> d1 ]]ᵀ T = { 0 |-> d1 }ᵀ ([[k ~> $!0]]ᵀ T).
  induction T; intros; inversion H; subst; simpl; intuition.
  erewrite IHT1; eauto. erewrite IHT2; eauto.
  erewrite <- open_subst1_qual; eauto. erewrite <- open_subst1_qual; eauto.
  erewrite IHT; eauto. erewrite <- open_subst1_qual; eauto.
Qed.

Lemma open_subst1_tm : forall {t b l},
    closed_tm b 0 l t -> forall {k t1},
      [[k ~> t1 ]]ᵗ t = { 0 |-> t1 }ᵗ ([[k ~> $0]]ᵗ t).
  induction t; intros b loc Hc; inversion Hc; subst; intros; simpl; intuition;
    try solve [erewrite IHt; eauto];
    try solve [erewrite IHt1; eauto; erewrite IHt2; eauto].
  bdestruct (k =? x); simpl; intuition.
Qed.

Fixpoint open_subst1_tm_comm {t : tm} :
  forall {k  g tf ff lf}, closed_tm 0 ff lf tf ->
    [[k ~> $g ]]ᵗ ({0 |-> tf }ᵗ t) = {0 |-> tf }ᵗ ([[ k ~> $(S g) ]]ᵗ  t).
    destruct t; intros; simpl; intuition;
      try solve [repeat erewrite open_subst1_tm_comm; eauto].
    destruct v; simpl.
    bdestruct (i =? 0); simpl. eapply closed_tm_open_id; eauto. lia. auto.
    bdestruct (k =? i); simpl; auto.
Qed.

Lemma open_subst1_qual_comm : forall {q : qual} {k g fr df ff lf},
    closed_qual 0 ff lf df ->
    [[k ~> ${fr}g ]]ᵈ ({0 |-> df }ᵈ q) = {0 |-> df }ᵈ ([[ k ~> ${fr}(S g) ]]ᵈ q).
  intros. destruct q; simpl; intuition. destruct df.
  inversion H. subst.
  destruct (NatSet.F.mem 0 t) eqn: Hmem1.
  - destruct (NatSet.F.mem k t0) eqn: Hmem2.
    + simpl. rewrite NatSet.F.mem_1. rewrite NatSet.F.mem_1.
      f_equal; try fnsetdec. destr_bool. rewrite remove_union_dist.
      rewrite unsplice_set_union_dist.
      rewrite remove_singleton_inv by lia.
      unfold unsplice_set at 3. rewrite filter_singleton_1. rewrite dec_singleton.
      rewrite filter_singleton_2. simpl. rewrite empty_union_right. fnsetdec.
      apply Nat.ltb_ge. lia. apply leb_correct. lia.
      apply bound_0_empty in H8. subst.
      repeat rewrite empty_union_right. auto.
      apply NatSet.F.union_2. apply NatSet.F.mem_2. auto.
      apply NatSet.F.union_2. apply NatSet.F.mem_2. auto.
    + simpl. apply bound_0_empty in H8. subst.
      repeat rewrite empty_union_right.
      rewrite Hmem2. rewrite Hmem1. auto.
  - destruct (NatSet.F.mem k t0) eqn: Hmem2.
    + simpl. rewrite Hmem2. rewrite not_member_union; auto.
      f_equal. rewrite unsplice_set_union_dist. rewrite unsplice_set_singleton_dec; auto.
      lia. rewrite mem_singleton. simpl. auto.
    + simpl. rewrite Hmem1.  rewrite Hmem2. auto.
Qed.

Fixpoint open_subst1_ty_comm {T : ty} :
  forall {k fr g df ff lf}, closed_qual 0 ff lf df ->
    [[k ~> ${fr}g ]]ᵀ ({0 |-> df }ᵀ T) = {0 |-> df }ᵀ ([[ k ~> ${fr}(S g) ]]ᵀ  T).
    destruct T; intros; simpl; intuition;
      try solve [repeat erewrite open_subst1_ty_comm; eauto].
    erewrite open_subst1_qual_comm; eauto. erewrite open_subst1_qual_comm; eauto.
    erewrite open_subst1_ty_comm; eauto. erewrite open_subst1_ty_comm; eauto.
    erewrite open_subst1_ty_comm; eauto. erewrite open_subst1_qual_comm; eauto.
Qed.

Lemma closed_qual_subst1 : forall {q b f l},
    closed_qual b (S f) l q ->
    forall {d1 l1}, closed_qual 0 0 l1 d1 ->
    forall{l2},
      l <= l2 -> l1 <= l2 ->
      closed_qual b f l2 ({0 |-> d1}ᵈ q).
  intros. inversion H; subst; intuition. inversion H0. subst.
  simpl. destruct (mem 0 vs) eqn:Hmem.
  constructor. apply bound_0_empty in H6. subst.
  rewrite empty_union_right.
  apply unsplice_set_dec. apply H3.
  apply union_bound; lia.
  apply union_bound; lia.
  constructor; try lia. apply unsplice_set_bound. apply H3.
  rewrite <- NatSetFacts.not_mem_iff in Hmem. auto.
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
  all : eapply closed_qual_subst1; eauto.
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
    [[1~> df ]]ᵈ ([[0~> d1 ]]ᵈ q) = { 0 |-> d1; df }ᵈ ([[1 ~> $!1]]ᵈ ([[0 ~> $!0]]ᵈ q)).
  intros. erewrite <- open_subst1_qual_comm; eauto.
  erewrite open_subst1_qual; eauto. f_equal. f_equal.
  erewrite open_subst1_qual; eauto. erewrite open_subst1_qual; eauto.
  eapply closed_qual_subst1; eauto. eapply closed_qual_open_succ; eauto.
Qed.

Lemma open_subst2_ty : forall {T l},
    closed_ty 2 0 l T ->
    forall {d1 df}, closed_qual 0 0 l d1 ->
    [[1~> df ]]ᵀ ([[0~> d1 ]]ᵀ T) = { 0 |-> d1; df }ᵀ ([[1 ~> $!1]]ᵀ ([[0 ~> $!0]]ᵀ T)).
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
  destruct (mem 0 t) eqn: Hmem1.
  - rewrite NatSet.F.mem_1.
    destruct (mem 0 t2) eqn: Hmem2.
    simpl. f_equal; try fnsetdec. destr_bool.
    rewrite union_assoc. rewrite remove_union_dist.
    rewrite unsplice_set_union_dist. rewrite union_assoc. f_equal.
    fnsetdec.
    simpl. f_equal; try fnsetdec. destr_bool.
    rewrite remove_union_dist. rewrite unsplice_set_union_dist.
    rewrite (remove_not_in Hmem2). fnsetdec.
    apply NatSet.F.union_2. apply NatSet.F.mem_2. auto.
  - destruct (mem 0 t2) eqn: Hmem2.
    + simpl. rewrite NatSet.F.mem_1.
      f_equal; try fnsetdec. destr_bool.
      rewrite remove_union_dist.
      rewrite unsplice_set_union_dist.
      rewrite (remove_not_in Hmem1). fnsetdec.
      apply NatSet.F.union_3. apply NatSet.F.mem_2. auto.
    + simpl. rewrite not_member_union; auto.
      f_equal; try fnsetdec.
      rewrite <- unsplice_set_union_dist. auto.
Qed.

Lemma subst1_qual_plus : forall {l du},
    closed_qual 0 0 l du -> du = {0 |-> du }ᵈ (du ⊔ $!0).
  intros. destruct du; intuition.
  inversion H. subst. apply bound_0_empty in H6. subst.
  apply bound_0_empty in H8. subst.
  simpl. rewrite empty_union_left. repeat rewrite empty_union_right.
  rewrite NatSet.F.mem_1 by fnsetdec. f_equal; try fnsetdec. destr_bool.
  rewrite remove_singleton_empty. rewrite unsplice_set_empty. auto.
Qed.

Lemma subst1_qual_plus' : forall {du du' l},
    du' ⊑ du -> closed_qual 0 0 l du -> {0 |-> du }ᵈ (du' ⊔ $!0) = du.
  intros. destruct du'; intuition. destruct du.
  inversion H. intuition. inversion H0. subst.
  apply bound_0_empty in H11, H13. subst.
  simpl. rewrite NatSet.F.mem_1 by fnsetdec.
  repeat rewrite empty_union_right.
  assert (t = {}N) by fnsetdec. assert (t0 = {}N) by fnsetdec.
  subst. repeat rewrite empty_union_left. f_equal. destr_bool.
  rewrite remove_singleton_empty. rewrite unsplice_set_empty. auto.
  fnsetdec.
Qed.

Lemma subst1_open_qual_comm : forall {k l d1 d2 q1},
    closed_qual 0 0 l q1 ->
    {0 |-> q1 }ᵈ ([[k ~> d1 ]]ᵈ d2) = [[k ~> {0 |-> q1 }ᵈ d1 ]]ᵈ ({0 |-> q1 }ᵈ d2).
Proof.
  intros. destruct d2; simpl; auto. destruct d1; simpl. destruct q1; simpl.
  inversion H. subst. apply bound_0_empty in H6. apply bound_0_empty in H8.
  subst.
  repeat rewrite empty_union_right.
  destruct (mem k t0) eqn:Hmem1.
  - simpl. destruct (mem 0 t2) eqn:Hmem2.
    + rewrite NatSet.F.mem_1.
      destruct (mem 0 t) eqn:Hmem3;
      simpl; rewrite Hmem1; rewrite empty_union_right;
        f_equal; try fnsetdec; try solve [destr_bool]; rewrite <- unsplice_set_union_dist;
          try rewrite <- remove_union_dist; auto. rewrite remove_union_dist. rewrite (remove_not_in Hmem3). auto.
      apply NatSet.F.union_3. apply NatSet.F.mem_2. auto.
    + destruct (mem 0 t) eqn:Hmem3.
      * rewrite NatSet.F.mem_1.
        simpl. rewrite Hmem1. rewrite empty_union_right.
        f_equal; try fnsetdec. destr_bool.
        rewrite <- unsplice_set_union_dist. rewrite remove_union_dist. rewrite (remove_not_in Hmem2). auto.
        apply NatSet.F.union_2. apply NatSet.F.mem_2. auto.
      * rewrite not_member_union; auto. simpl. rewrite Hmem1.
        f_equal.
        rewrite <- unsplice_set_union_dist. auto.
  - simpl. destruct (mem 0 t) eqn: Hmem2.
    + destruct (mem 0 t2) eqn: Hmem3; simpl;
        rewrite Hmem1; repeat rewrite empty_union_right; auto.
    + destruct (mem 0 t2) eqn: Hmem3; simpl; rewrite Hmem1; auto.
Qed.

Lemma subst1_open_ty_comm : forall {T k l d1 q1},
    closed_qual 0 0 l q1 ->
    {0 |-> q1 }ᵀ ([[k ~> d1 ]]ᵀ T) = [[k ~> {0 |-> q1 }ᵈ d1 ]]ᵀ ({0 |-> q1 }ᵀ T).
  induction T; intros; intuition.
  - simpl. erewrite IHT1; eauto. erewrite IHT2; eauto. repeat erewrite subst1_open_qual_comm; eauto.
  - simpl. erewrite IHT; eauto. repeat erewrite subst1_open_qual_comm; eauto.
Qed.

Lemma indexr_subst1 : forall {x Γ b T U d dx},
    x >= 1 ->
    indexr x (Γ ++ [U]) = Some (b, T, d) ->
    indexr (pred x) ({ 0 |-> dx }ᴳ Γ) = Some (b, { 0 |-> dx }ᵀ T, { 0 |-> dx }ᵈ d).
  intros. destruct x; try lia.
  rewrite <- indexr_insert_ge in H0; simpl; try lia.
  rewrite app_nil_r in H0. induction Γ; intros; simpl in *. discriminate.
  rewrite subst1_tenv_length. (bdestruct (x =? ‖Γ‖)); auto.
  inversion H0. auto.
Qed.

Lemma subst_qual_subqual_monotone : forall {d1 d2}, d1 ⊑ d2 -> forall {df}, ({0 |-> df }ᵈ d1) ⊑ ({0 |-> df }ᵈ d2).
Proof.
  intros. destruct d1; destruct d2; destruct df; simpl; intuition.
  inversion H. intuition.
  destruct (mem 0 t) eqn: Hmem1; destruct (mem 0 t2) eqn: Hmem2;
    simpl; intuition; try fnsetdec. 1,3,7 : destr_bool.
  - apply NatSet.F.mem_2 in Hmem1. rewrite <- NatSetFacts.not_mem_iff in Hmem2. fnsetdec.
  - apply NatSetProperties.union_subset_4.
    apply unsplice_set_subset_monotone. auto.
  - specialize (@subset_inclusion _ _ _ H2 Hmem1 Hmem2) as F. inversion F.
  - specialize (@subset_inclusion _ _ _ H2 Hmem1 Hmem2) as F. inversion F.
  - specialize (@subset_inclusion _ _ _ H2 Hmem1 Hmem2) as F. inversion F.
  - specialize (@NatSetProperties.union_subset_1 (unsplice_set 0 (remove 0 t2)) t5) as Hs.
    specialize (@unsplice_set_subset_monotone t t2 H2) as Hs2.
    rewrite (remove_not_in Hmem1) in Hs2. fnsetdec.
  - rewrite <- (remove_not_in Hmem1). rewrite <- (remove_not_in Hmem2).
    apply unsplice_set_subset_monotone. auto.
Qed.

Lemma subst1_just_fv : forall {fr x dy},
    ${fr}x = {0 |-> dy }ᵈ ${fr}(S x).
  intros. simpl. rewrite mem_singleton. simpl.
  rewrite unsplice_set_singleton. auto.
Qed.

Lemma closed_qual_subst1' : forall {Γ0 X l df φ b},
    closed_qual 0 0 l df ->
    closed_qual b (‖ Γ0 ++ [X] ‖) l φ ->
    closed_qual b (‖ {0 |-> df }ᴳ Γ0 ‖) l ({0 |-> df }ᵈ φ).
  intros. repeat eapply closed_qual_subst1; eauto. rewrite subst1_tenv_length.
  rewrite length_app in *. simpl in *. replace (‖Γ0‖ + 1) with (S (‖Γ0‖)) in H0.
  auto. lia.
Qed.

Lemma closed_tm_subst1' : forall {Γ0 X l df tx t b},
    closed_tm 0 0 l tx ->
    closed_tm b (‖ Γ0 ++ [X] ‖) l t ->
    closed_tm b (‖ {0 |-> df }ᴳ Γ0 ‖) l ({0 |-> tx }ᵗ t).
  intros. repeat eapply closed_tm_subst1; eauto. rewrite subst1_tenv_length.
  rewrite length_app in *. simpl in *. replace (‖Γ0‖ + 1) with (S (‖Γ0‖)) in H0.
  auto. lia.
Qed.

Lemma closed_ty_subst1' : forall {Γ0 X l df T b},
    closed_qual 0 0 l df ->
    closed_ty b (‖ Γ0 ++ [X] ‖) l T ->
    closed_ty b (‖ {0 |-> df }ᴳ Γ0 ‖) l ({0 |-> df }ᵀ T).
  intros. repeat eapply closed_ty_subst1; eauto. rewrite subst1_tenv_length.
  rewrite length_app in *. simpl in *. replace (‖Γ0‖ + 1) with (S (‖Γ0‖)) in H0.
  auto. lia.
Qed.

Lemma subst_filter0 : forall {d φ l fr}, closed_qual 0 0 l d -> ${fr}0 ⊑ φ -> d ⊑ { 0 |-> d }ᵈ φ.
  intros. destruct d; simpl in *. destruct φ. intuition. simpl.
  inversion H. subst. rewrite NatSet.F.mem_1. intuition. destr_bool.
  eapply NatSetProperties.in_subset; eauto. fnsetdec.
Qed.

Lemma subst1_qual_0 : forall {q' q}, q' ⊑ q -> forall {df}, $0 ∈ᵥ df -> q' ⊑ { 0 |-> q }ᵈ df.
  intros. destruct df; simpl in *. destruct q. intuition. simpl.
  apply NatSet.F.mem_1 in H0. rewrite H0. destruct q'. qdec.
Qed.

Lemma subst1_qual_0' : forall {q' q}, q' ⊑ q ⊔ {♦} -> forall {df}, $0 ∈ᵥ df -> q' ⊑ { 0 |-> q }ᵈ df ⊔ {♦}.
  intros. destruct df; simpl in *. destruct q. intuition. simpl.
  apply NatSet.F.mem_1 in H0. rewrite H0. destruct q'. qdec.
Qed.

Lemma subst1_just_fv0_gen : forall {q fr}, {0 |-> q }ᵈ ${fr}0 = (q ⊔ ∅{ fr }).
  intros. simpl. destruct q; intuition. repeat rewrite empty_union_left.
  rewrite NatSet.F.mem_1 by fnsetdec. rewrite remove_singleton_empty.
  rewrite unsplice_set_empty. qdec.
Qed.

Lemma subst1_just_fv0 : forall {q}, {0 |-> q }ᵈ $!0 = q.
  intros. rewrite (@subst1_just_fv0_gen q false). auto.
Qed.

Lemma saturated0 : forall {Γ Σ Tx frx fx bx lx fr ff bf lf},
    mem 0 ff = true -> saturated (Γ ++ [(Tx, qset frx fx bx lx)]) Σ (qset fr ff bf lf) -> implb frx fr = true /\ fx [<=] ff /\ bx [<=] bf /\ lx [<=] lf.
  intros. inversion H0. specialize (H1 0). simpl in H1. apply NatSet.F.mem_2 in H.
  apply H0 in H. inversion H. rewrite indexr_skips in H3; auto. simpl in H3.
  inversion H3. subst. simpl in H4. intuition.
Qed.

Lemma subst1_preserves_separation : forall {df d1 sx Tx dx dx' Γ Σ φ},
    dx' ⊓ φ ⊑ dx ->
    closed_qual 0 0 (‖Σ‖) dx' ->
    df ⊑ φ -> d1 ⊑ φ ->
    saturated (Γ ++ [(sx, Tx, dx)]) Σ d1 ->
    saturated (Γ ++ [(sx, Tx, dx)]) Σ df ->
    {0 |-> dx' }ᵈ df ⊓ {0 |-> dx' }ᵈ d1 = {0 |-> dx' }ᵈ (df ⊓ d1).
  intros. destruct df as [frf ff bf lf]. destruct d1 as [fr1 f1 b1 l1]. destruct dx' as [frx' fx' bx' lx'].
  destruct φ as [frp fp bp lp]. inversion H0. subst. apply bound_0_empty in H11, H13. (* simpl in H5. *) subst.
  destruct dx as [frx fx bx lx]. simpl in H. intuition. rewrite inter_empty_left in H6.
  rewrite inter_empty_left in H.
  destruct (mem 0 ff) eqn:Hmem0ff; destruct (mem 0 f1) eqn:Hmem0f1; simpl; rewrite NatSetFacts.inter_b;
    rewrite Hmem0ff; rewrite Hmem0f1; simpl.
  - (*0 ∈ df, 0 ∈ d1 : this is trivial since we substitute the first variable for a closed value. The case for general
      substitution would require more careful reasoning. *)
    f_equal; try fnsetdec. destr_bool. repeat rewrite empty_union_right.
    apply NatSet.eq_if_Equal. apply inter_unsplice_0.
  - (* 0 ∈ df, 0 ∉ d1 *)
    (* the interesting bit is reasoning about the overlap, this requires the extra assumptions about
       saturation of the sets and the boundedness of the context, which imply Hlx: *)
    specialize (saturated0 Hmem0ff H4) as Hlx.
    f_equal; try fnsetdec.
    (* case frf = false, requires saturation/Hlx above: *)
    destruct frf; simpl; auto. intuition. destr_bool; intuition.
    repeat rewrite empty_union_right.
    replace (inter ff f1) with (remove 0 (inter ff f1)).
    rewrite <- (remove_not_in Hmem0f1) at 1.
    apply NatSet.eq_if_Equal. apply inter_unsplice_0. apply NatSet.F.mem_2 in Hmem0ff.
    rewrite <- NatSetFacts.not_mem_iff in Hmem0f1. fnsetdec.
    apply NatSet.eq_if_Equal.
    setoid_rewrite NatSetProperties.union_inter_1.
    assert (Hl1 : inter lx' l1 [<=] lx). { simpl in H2. intuition. fnsetdec. }
    fnsetdec.
  - (* 0 ∉ df, 0 ∈ d1, analogous to the previous case *)
    specialize (saturated0 Hmem0f1 H3) as Hlx.
    f_equal; try fnsetdec.
    (* case fr1 = false, requires saturation/Hlx above: *)
    destruct fr1; simpl; auto. intuition. destr_bool; intuition.
    repeat rewrite empty_union_right.
    replace (inter ff f1) with (remove 0 (inter ff f1)).
    rewrite <- (remove_not_in Hmem0ff) at 1.
    apply NatSet.eq_if_Equal. apply inter_unsplice_0. apply NatSet.F.mem_2 in Hmem0f1.
    rewrite <- NatSetFacts.not_mem_iff in Hmem0ff. fnsetdec.
    apply NatSet.eq_if_Equal. rewrite NatSetProperties.inter_sym.
    setoid_rewrite NatSetProperties.union_inter_1.
    assert (Hl1 : inter lx' lf [<=] lx). { simpl in H1. intuition. fnsetdec. }
    fnsetdec.
  - (* 0 ∉ df, 0 ∉ d1 : trivial, since the substitution has no effect (other than unsplicing the sets) *)
    f_equal; try fnsetdec. apply NatSet.eq_if_Equal. replace (inter ff f1) with (remove 0 (inter ff f1)).
    rewrite <- (remove_not_in Hmem0f1) at 1. rewrite <- (remove_not_in Hmem0ff) at 1. apply inter_unsplice_0.
    rewrite <- NatSetFacts.not_mem_iff in Hmem0f1, Hmem0ff. fnsetdec.
Qed.

Lemma subst1_mem : forall {x dx df l}, closed_qual 0 0 l dx -> $x ∈ᵥ {0 |-> dx }ᵈ df -> $(S x) ∈ᵥ df.
  intros. inversion H. subst. apply bound_0_empty in H1, H2. subst. destruct df. simpl in *.
  destruct (mem 0 t) eqn:Hmem0t0; simpl in H0;
    unfold unsplice_set in H0; rewrite filter_lt_0 in H0; rewrite filter_ge0_id in H0;
    repeat rewrite empty_union_right in H0.
  * destruct x. rewrite dec_in0 in H0. fnsetdec. fnsetdec.
    change (S x) with (pred (S (S x))) in H0. rewrite <- dec_in_iff in H0. fnsetdec. lia.
  * destruct x. rewrite dec_in0 in H0. fnsetdec. rewrite <- NatSetFacts.not_mem_iff in Hmem0t0. auto.
    change (S x) with (pred (S (S x))) in H0. rewrite <- dec_in_iff in H0. fnsetdec. lia.
Qed.

Lemma subst1_mem_loc : forall {dx df l}, l ∈ₗ {0 |-> dx }ᵈ df ->  (l ∈ₗ dx /\ $0 ∈ᵥ df) \/ l ∈ₗ df.
  intros. destruct dx. destruct df. simpl in *. destruct (mem 0 t2) eqn:Hmem; simpl in *; intuition.
  apply NatSet.F.mem_2 in Hmem. fnsetdec.
Qed.

Lemma subst1_senv_saturated : forall {Σ df dx'},
    senv_saturated Σ df ->
    closed_qual 0 0 (‖Σ‖) dx' -> senv_saturated Σ dx' ->
    senv_saturated Σ ({0 |-> dx' }ᵈ df).
  intros. inversion H0. subst. apply bound_0_empty in H2, H3. subst.
  unfold senv_saturated in *. intros. apply subst1_mem_loc in H2. intuition.
  - apply H1 in H2. inversion H2. econstructor; eauto. apply subst1_qual_0'; auto.
  - apply H in H3. inversion H3. econstructor; eauto. inversion H6. subst.
    apply bound_0_empty in H7, H8. subst. destruct df. simpl. destruct (mem 0 t); qdec.
Qed.

Lemma subst1_saturated : forall {Γ Σ bx Tx dx df dx'},
    saturated (Γ ++ [(bx, Tx, dx)]) Σ df ->
    closed_qual 0 0 (‖Σ‖) dx' -> senv_saturated Σ dx' ->
    saturated ({0 |-> dx' }ᴳ Γ) Σ ({0 |-> dx' }ᵈ df).
  intros. inversion H0. subst. apply bound_0_empty in H2, H3.
  subst. inversion H. constructor; intros. unfold tenv_saturated. intros.
  - eapply subst1_mem in H5; eauto.
    apply H2 in H5. inversion H5. apply @indexr_subst1 with (dx:=(qset fresh {}N {}N ls)) in H6.
    simpl in H6. econstructor. eauto. apply subst_qual_subqual_monotone. auto.
    eapply closed_qual_subst1; eauto. lia.
  - apply subst1_senv_saturated; auto.
Qed.

Lemma qglb_increase_fresh : forall {dx dx' φ' l X},
  dx' ⊓ φ' ≡ dx ->
  closed_qual 0 0 l dx' ->
  dx' ⊓ (φ' ⊔ qset false X {}N {}N) ≡ dx.
  intros. destruct dx' as [frx' fx' bx' lx'].
  inversion H0. subst. apply bound_0_empty in H7, H9.
  subst. destruct dx as [frx fx bx lx]. destruct φ' as [frp' fp' bp' lp']. qdec.
Qed.

Lemma qglb_disjoint_freshv : forall {dx' l x},
  closed_qual 0 0 l dx' -> dx' ⊓ $!x = ∅.
  intros. destruct dx' as [frx' fx' bx' lx'].
  inversion H. subst. apply bound_0_empty in H6, H8.
  subst. qdec.
Qed.

Lemma qglb_disjoint_fresh : forall {dx' l},
  closed_qual 0 0 l dx' -> dx' ⊓ {♦} = ∅{ ♦∈? dx' }.
  intros. destruct dx' as [frx' fx' bx' lx'].
  inversion H. subst. apply bound_0_empty in H6, H8.
  subst. qdec.
Qed.

Lemma qmem_plus_decomp : forall {x0 q x}, x0 ∈ₗ q ⊔ &!x -> closed_qual 0 0 x q -> x0 ∈ₗ q \/ x0 = x.
  intros. inversion H0. subst. simpl in *. apply NatSet.F.union_1 in H. intuition.
  right. rewrite NatSetFacts.singleton_iff in H4. auto.
Qed.

Lemma senv_saturated_qplus : forall {Σ l T q}, indexr l Σ = Some (T, q) -> closed_qual 0 0 l q -> senv_saturated Σ q -> senv_saturated Σ (q ⊔ &!l).
  unfold senv_saturated. intros. specialize (qmem_plus_decomp H2 H0) as Hl. destruct Hl.
  - apply H1 in H3. inversion H3. subst. econstructor; eauto. eapply subqual_trans; eauto.
  - subst. econstructor; eauto. rewrite <- qlub_assoc. auto.
Qed.

Lemma wf_senv_saturated_qplus : forall {Σ}, wf_senv Σ -> forall {l T q}, indexr l Σ = Some (T, q) -> senv_saturated Σ (q ⊔ &!l).
  intros. specialize (wf_senv_prop H l T q) as Hwf. intuition. eapply senv_saturated_qplus; eauto.
Qed.

Lemma has_type_senv_saturated : forall {Γ φ Σ t T q}, has_type Γ φ Σ t T q -> wf_senv Σ -> senv_saturated Σ q.
  intros. induction H; eauto.
  - intuition. apply has_type_closed in H, H1. intuition. eapply senv_saturated_openq; eauto.
  - intuition. apply has_type_closed in H, H3. intuition. eapply senv_saturated_openq; eauto.
  - eapply wf_senv_saturated_qplus; eauto.
Qed.

Lemma vtp_closed:
  forall {Σ t T d}, vtp Σ t T d ->
    closed_tm 0 0 (‖Σ‖) t /\
    closed_ty 0 0 (‖Σ‖) T /\
    closed_qual 0 0 (‖Σ‖) d .
Proof.
  intros. induction H; intuition.
  + constructor. apply indexr_var_some' in H2; intuition.
  + constructor. apply stp_closed in H3. intuition. auto.
Qed.

Lemma vtp_widening: forall {Σ T1 d1 T2 d2 t},
  vtp Σ t T1 d1 -> stp [] Σ T1 d1 T2 d2 -> senv_saturated Σ d2 -> vtp Σ t T2 d2.
Proof. intros. inversion H; subst.
  - inversion H0; subst. constructor; auto. apply qstp_closed in H4. intuition.
  - inversion H0; subst. eapply vtp_loc; eauto. apply qstp_closed in H13. intuition.
    apply qstp_closed in H18. intuition.
    apply qstp_empty in H18. apply qstp_empty in H22.
    replace q2 with q; auto. apply eq_if_eqqual; apply subqual_antisymm; auto.
    1,2 : eapply s_trans; eauto.
    apply qstp_empty in H18. apply qstp_empty in H22.
    replace q2 with q; auto. eauto. apply eq_if_eqqual; apply subqual_antisymm; auto.
    apply qstp_empty in H18. apply qstp_empty in H22.
    replace q2 with q; auto. eauto. apply eq_if_eqqual; apply subqual_antisymm; auto.
  - inversion H0; subst. econstructor. 5: eapply H6. all : eauto.
    apply qstp_closed in H24. intuition.
    eapply s_trans; eauto.
    assert (stp [(false, T7, d8); (true, TFun d0 d3 T0 T3, {♦})] Σ (T3 <~²ᵀ ([]: tenv)) (d3 <~²ᵈ ([]: tenv)) (T5 <~²ᵀ ([]: tenv)) (d5 <~²ᵈ ([]: tenv))). {
      eapply narrowing_stp; eauto. intuition. apply weaken_stp. auto.
    }
    assert (stp [] Σ (TFun d0 d3 T0 T3) {♦} (TFun d4 d5 T4 T5) {♦}). { eauto. }
    assert (stp [(false, T7, d8); (true, TFun d0 d3 T0 T3, {♦})] Σ (T5 <~²ᵀ ([]: tenv)) (d5 <~²ᵈ ([]: tenv)) (T8 <~²ᵀ ([]: tenv)) (d9 <~²ᵈ ([]: tenv))). {
      replace ([(false, T7, d8); (true, TFun d0 d3 T0 T3, {♦})]) with ([(false, T7, d8)] ++ [(true, TFun d0 d3 T0 T3, {♦})]); auto.
      eapply narrowing_stp_gen. 3 : eapply H14. auto. intuition.
    }
    eapply s_trans; eauto.
Qed.

Lemma has_type_vtp: forall {Σ φ t T d},
  value t ->
  has_type [] φ Σ t T d ->
  wf_senv Σ ->
  vtp Σ t T d.
Proof. intros. remember [] as Γ. induction H0; eauto; subst; try solve [inversion H].
  - (* tabs *) eapply vtp_abs; eauto.
    * eapply stp_refl. inversion H2. subst. intuition.
      apply qstp_refl; auto. inversion H2; subst. auto.
    * apply stp_refl. inversion H2. subst.
      + simpl in *. unfold open_ty'. unfold open_ty. simpl in *.
        eapply closed_ty_open2; eauto. eapply closed_ty_monotone; eauto.
        all: eapply just_fv_closed; eauto.
      + apply qstp_refl; auto. apply has_type_closed in H7; intuition.
  - (* tloc *) eapply vtp_loc; eauto.
     * subst. apply closed_qual_qlub; auto. eapply closed_qual_sub. eapply H0. auto.
     * apply stp_refl; auto.
     * apply stp_refl; auto.
     * eapply wf_senv_saturated_qplus; eauto.
  - (* tsub *)
     intuition. eapply vtp_widening; eauto.
Qed.

Lemma vtp_has_type: forall {Σ t T d}, vtp Σ t T d -> has_type [] d Σ t T d.
  intros. inversion H; subst.
  + econstructor; eauto.
  + apply t_sub with (T1:=TRef q T0) (d1:=(q ⊔ &!l)); auto.
    eapply t_loc; eauto. all :  apply qstp_empty in H6.
    all : eapply subqual_trans. 2,4 : eapply H6. all : auto.
  + specialize (qstp_closed H6) as Hcl. intuition.
    assert (has_type [] df1 Σ (tabs t0) (TFun d1 d2 T1 T2) df1). {
    constructor; eauto. }
    eapply weaken_flt with (φ' := d) in H13; eauto.
    apply qstp_empty in H6. auto.
Qed.

Lemma vtp_saturated: forall {Σ t T d}, vtp Σ t T d -> saturated [] Σ d.
  intros. inversion H; subst; constructor; auto.
Qed.

Lemma subst1_fresh_id : forall {x dx'}, {x |-> dx' }ᵈ {♦} = {♦}.
  intros. simpl. rewrite mem_empty. rewrite unsplice_set_empty. auto.
Qed.

Lemma Substq_non_fresh : forall {dx dx'}, Substq dx dx' -> ♦∉ dx'.
  intros. inversion H; auto.
Qed.
#[global] Hint Resolve Substq_non_fresh : core.

Lemma subst1_non_fresh : forall {x qx q}, ♦∉ q -> ♦∉ qx -> ♦∉ ({ x |-> qx }ᵈ q).
  intros. destruct q. destruct qx. simpl in *. subst.
  destruct (mem x t); auto.
Qed.
#[global] Hint Resolve subst1_non_fresh : core.

Lemma subst1_fresh : forall {x qx q}, ♦∈ q -> ♦∈ ({ x |-> qx }ᵈ q).
  intros. destruct q. destruct qx. simpl in *. subst.
  destruct (mem x t); auto.
Qed.
#[global] Hint Resolve subst1_fresh : core.

Lemma un_subst1_fresh : forall {x qx q}, ♦∉ qx -> ♦∈ ({ x |-> qx }ᵈ q) -> ♦∈ q.
  intros. destruct q. destruct qx. simpl in *.
  destruct (mem x t); auto. simpl in H0. destr_bool.
Qed.
#[global] Hint Resolve un_subst1_fresh : core.

Lemma subst_qstp :  forall {Γ b Tf df df' Σ d1 d2},
    qstp (Γ ++ [(b, Tf, df)]) Σ d1 d2 ->
    closed_qual 0 0 (‖Σ‖) df' ->
    Substq df df' ->
    qstp ({0 |-> df' }ᴳ Γ) Σ ({0 |-> df' }ᵈ d1) ({0 |-> df' }ᵈ d2).
  intros Γ b Tf df df' Σ d1 d2 H. remember (Γ ++ [(b, Tf, df)]) as Γ'.
  generalize dependent Γ. generalize dependent df.  generalize dependent Tf.
  induction H; intros; subst.
  - apply qs_sq. apply subst_qual_subqual_monotone. auto. eapply closed_qual_subst1'; eauto.
  -  bdestruct (f =? 0).
    * pose (H' := H). subst. rewrite indexr_skips in H'; auto. simpl in H'. inversion H'. subst.
      rewrite subst1_qlub_dist. rewrite subst1_just_fv0. erewrite subst1_qual_id; eauto. inversion H3; subst.
      + rewrite qlub_idem. apply qs_sq; auto. rewrite subst1_tenv_length. eapply closed_qual_monotone; eauto. lia.
      + apply not_fresh_fresh_false in H1. contradiction.
    * rewrite subst1_qlub_dist. destruct f. lia. rewrite <- subst1_just_fv.
      eapply qs_self; eauto. eapply @indexr_subst1 with (dx:=df') in H; try lia. eauto.
      eapply closed_qual_subst1; eauto.
  - bdestruct (x =? 0).
    * subst. pose (H' := H). subst. rewrite indexr_skips in H'; auto. simpl in H'. inversion H'. subst.
      rewrite subst1_just_fv0. erewrite subst1_qual_id; eauto. inversion H4; subst.
      + apply qs_sq. auto. rewrite subst1_tenv_length. eapply closed_qual_monotone; eauto. lia.
      + apply not_fresh_fresh_false in H2. contradiction.
    * destruct x. lia. rewrite <- subst1_just_fv. eapply qs_qvar. apply @indexr_subst1 with (dx:=df') in H; try lia.
      eauto. eapply closed_ty_subst1; eauto. eapply closed_qual_subst1; eauto. eauto.
  - repeat rewrite subst1_qlub_dist. eapply qs_cong; eauto. eapply closed_qual_subst1'; eauto.
  - eapply qs_trans. eapply IHqstp1; eauto. eauto.
    Unshelve. all : auto.
Qed.

Lemma subst_stp : forall{T1 T2},
    forall {Γ b Tf df df' Σ d1 d2},
      stp (Γ ++ [(b,Tf,df)]) Σ T1 d1 T2 d2 ->
      closed_qual 0 0 (‖Σ‖) df' ->
      Substq df df' ->
      stp ({ 0 |-> df' }ᴳ Γ) Σ
          ({ 0 |-> df' }ᵀ T1) ({ 0 |-> df' }ᵈ d1)
          ({ 0 |-> df' }ᵀ T2) ({ 0 |-> df' }ᵈ d2).
  intros T1 T2 Γ b Tf df df' Σ d1 d2 HS.
  remember (Γ ++ [(b, Tf, df)]) as Γ'.
  generalize dependent Γ. generalize dependent df.  generalize dependent Tf. induction HS; intros; subst.
  - simpl. constructor. eapply subst_qstp; eauto.
  - specialize (stp_closed HS1). intuition. specialize (stp_closed HS2). intuition.
    simpl. constructor. eapply subst_qstp; eauto.
    specialize (IHHS1 Tf df Γ0). intuition. erewrite subst1_qual_empty in H11. auto.
    specialize (IHHS2 Tf df Γ0). intuition. erewrite subst1_qual_empty in H11. auto.
    all : eapply subst_qstp; eauto.
  - simpl. constructor. inversion H. subst. 2 : inversion H0. subst.
    1,2: constructor; try eapply closed_ty_subst1'; eauto; eapply closed_qual_subst1'; eauto.
    eapply subst_qstp; eauto. eapply IHHS1; eauto.
    unfold open_ty' in *. unfold open_ty in *.
    unfold openq' in *. unfold openq in *.
    rewrite length_app in *. rewrite subst1_tenv_length. simpl in *.
    replace (‖Γ0‖ + 1) with (S (‖Γ0‖)) in *; try lia.
    specialize (IHHS2 Tf df ((false, T3, d3) :: (true, TFun d1 d2 T1 T2, {♦}) :: Γ0)). intuition. rename H4 into IHHS2. simpl in IHHS2.
    rewrite mem_empty in IHHS2. rewrite unsplice_set_empty in IHHS2.
    erewrite <- open_subst1_ty_comm in IHHS2; eauto. erewrite <- open_subst1_ty_comm in IHHS2; eauto.
    erewrite <- open_subst1_ty_comm in IHHS2; eauto. erewrite <- open_subst1_ty_comm in IHHS2; eauto.
    erewrite <- open_subst1_qual_comm in IHHS2; eauto. erewrite <- open_subst1_qual_comm in IHHS2; eauto.
    erewrite <- open_subst1_qual_comm in IHHS2; eauto. erewrite <- open_subst1_qual_comm in IHHS2; eauto.
  (* - eapply s_trans. eapply IHHS1; eauto. eapply IHHS2; eauto. *)
Qed.

Lemma un_subst1_qual_open : forall {v dx q l}, closed_qual 0 0 l dx -> {0 |-> dx }ᵈ ([[v ~> ∅ ]]ᵈ q) = {0 |-> dx }ᵈ q -> [[v ~> ∅ ]]ᵈ q = q.
  intros. destruct q. inversion H. subst. apply bound_0_empty in H1, H2. subst. simpl in *.
  repeat rewrite empty_union_right in *.
  destruct (mem v t0) eqn:Hmemvt0; auto. destruct (mem 0 t) eqn:Hmem0t; auto; simpl in *.
  repeat rewrite empty_union_right in *. rewrite Hmem0t in H0. inversion H0. repeat rewrite H4. qdec.
  rewrite Hmem0t in H0. inversion H0. repeat rewrite H4. qdec.
Qed.

Lemma not_free_subst1_ty_iff : forall {v dx T l}, closed_qual 0 0 l dx -> not_free v T <-> not_free v ({0 |-> dx }ᵀ T).
  intros. unfold not_free. intuition.
  - replace (∅) with ({0 |-> dx }ᵈ ∅); auto. erewrite <- subst1_open_ty_comm; eauto. rewrite H0. auto.
  - replace (∅) with ({0 |-> dx }ᵈ ∅) in H0; auto. erewrite <- subst1_open_ty_comm in H0; eauto.
    generalize dependent v. induction T; intros; simpl; intuition;
    simpl in H0; inversion H0; f_equal; intuition; eapply un_subst1_qual_open; eauto.
Qed.

Lemma substitution_gen :
  forall {t Γ φ bx Tx dx dx' Σ T d}, dx' ⊓ φ ⊑ dx ->
      has_type (Γ ++ [(bx,Tx,dx)]) φ Σ t T d -> Substq dx dx' ->
        forall {tx}, vtp Σ tx Tx dx' ->
                        has_type ({ 0 |-> dx' }ᴳ Γ) ({ 0 |-> dx' }ᵈ φ) Σ
                                 ({ 0 |-> tx  }ᵗ t)
                                 ({ 0 |-> dx' }ᵀ T)
                                 ({ 0 |-> dx' }ᵈ d).
  intros t Γ φ bx Tx dx dx' Σ T d Hsep (* φ Hphi *) HT HSubst tx HTx. specialize (vtp_closed HTx) as Hclx.
  specialize (vtp_saturated HTx) as Hsatx. destruct Hsatx as [Htsatx Hssatx].
  simpl in Hclx. intuition. remember (Γ ++ [(bx,Tx, dx)]) as Γ'.
  generalize dependent Γ.
  induction HT; intros; subst; pose (φs := {0 |-> dx' }ᵈ φ); replace ({0 |-> dx' }ᵈ φ) with φs in *; auto.
  - (* t_base *) simpl. rewrite NatSetFacts.empty_b. rewrite unsplice_set_empty.
    apply t_base; auto. eapply closed_qual_subst1'; eauto.
  - (* t_var *) simpl. (bdestruct (x =? 0)).
    * (*x is 0 *) rewrite indexr_skips in H0; simpl; auto; try lia. simpl in H0. subst. simpl in H0.
        rewrite mem_singleton. simpl. rewrite remove_singleton_empty. rewrite unsplice_set_empty.
        destruct dx'. repeat rewrite empty_union_left.
        inversion H0. subst. erewrite subst1_ty_id; eauto. inversion HSubst; subst.
        + (*subst fun, dx = dx' *)
          apply vtp_has_type in HTx.
          eapply weaken'; eauto. eapply subst_filter0; eauto.
          eapply closed_qual_subst1'; eauto.
        + (*subst arg, dx = df ⋒ dx = dx' ⋒ φ *)
          apply vtp_has_type in HTx.
          eapply weaken'; eauto.
          eapply @subst_qual_subqual_monotone with (df:=qset b0 t t0 t1) in H3.
          subst φs. erewrite subst1_just_fv0 in H3. auto.
          eapply closed_qual_subst1'; eauto.
    * (*x is in Γ0*) assert (Hx: 1 <= x); try lia. destruct x; try lia.
      rewrite mem_singleton. simpl.
      rewrite unsplice_set_singleton_dec; try lia.
      apply t_var with (b:=b) (d:={0 |-> dx' }ᵈ d). change x with (pred (S x)).
      eapply indexr_subst1; eauto. erewrite subst1_just_fv.
      repeat eapply subst_qual_subqual_monotone. auto.
      eapply closed_qual_subst1'; eauto. simpl. eapply closed_ty_subst1; eauto.
      simpl. eapply closed_qual_subst1; eauto.
  - (* t_abs *) simpl. apply t_abs; auto. eapply closed_tm_subst1'; eauto.
    inversion H3. subst. constructor; try eapply closed_ty_subst1'; eauto; eapply closed_qual_subst1'; eauto.
    eapply closed_qual_subst1'; eauto. apply subst_qual_subqual_monotone. auto. eauto.
    apply subst1_senv_saturated; auto.
    (* 1. instantiate the IH *)
    replace (length (Γ0 ++ [(bx, Tx, dx)])) with (S (‖Γ0‖)) in IHHT.
    rewrite subst1_tenv_length. rewrite app_comm_cons in IHHT. rewrite app_comm_cons in IHHT.
    remember (df ⊔ $!(S (‖Γ0‖)) ⊔ $!(S (S (‖Γ0‖))) ⊔ {♦}) as DF.
    replace ({0 |-> dx' }ᵈ df ⊔ $!(‖Γ0‖) ⊔ $!(S (‖Γ0‖)) ⊔ {♦}) with ({0 |-> dx' }ᵈ DF).
    (* remember (φ' ⊔ $!(S (‖Γ0‖)) ⊔ $!(S (S (‖Γ0‖)))) as φ''. *)
    assert (Hsep' : dx' ⊓ DF ⊑ dx). {
      subst. repeat rewrite qglb_qlub_dist_l. erewrite qglb_disjoint_freshv; eauto. erewrite qglb_disjoint_freshv; eauto.
      erewrite qglb_disjoint_fresh; eauto. repeat rewrite qlub_empty_left. apply Substq_non_fresh in HSubst.
      rewrite HSubst. rewrite qlub_empty_right. eapply (subqual_trans _ Hsep).
    }
    intuition. rename H8 into IHHT. specialize IHHT with (Γ := (((false,T1, d1) :: (true, (TFun d1 d2 T1 T2), df) :: Γ0))).
    (* 2. reason about opening and subst, apply IH *)
    unfold open_tm' in *. unfold open_ty' in *. unfold open_ty in *.
    unfold openq' in *. unfold openq in *.
    rewrite length_app in IHHT. rewrite subst1_tenv_length. simpl in *.
    replace (‖Γ0‖ + 1) with (S (‖Γ0‖)) in IHHT; try lia.
    erewrite <- open_subst1_tm_comm in IHHT; eauto. erewrite <- open_subst1_tm_comm in IHHT; eauto.
    erewrite <- open_subst1_ty_comm in IHHT; eauto. erewrite <- open_subst1_ty_comm in IHHT; eauto.
    erewrite <- open_subst1_qual_comm in IHHT; eauto. erewrite <- open_subst1_qual_comm in IHHT; eauto.
    subst. rewrite subst1_qlub_dist. repeat rewrite subst1_qlub_dist. f_equal.
    repeat rewrite <- subst1_just_fv. rewrite subst1_fresh_id. auto. rewrite length_app. simpl. lia.
  - (* t_app *) intuition. rename H7 into IHHT1. rename H6 into IHHT2. simpl.
    replace ({ 0 |-> dx' }ᵈ (openq df d1 d2)) with
               (openq ({ 0 |-> dx' }ᵈ df) ({ 0 |-> dx' }ᵈ d1) ({ 0 |-> dx' }ᵈ d2)).
    replace ({0 |-> dx' }ᵀ (T2 <~ᵀ ∅; d1)) with
               (({0 |-> dx' }ᵀ T2) <~ᵀ (∅); ({0 |-> dx' }ᵈ d1)).
    apply t_app with (T1:= { 0 |-> dx' }ᵀ T1) (df:=({0 |-> dx' }ᵈ df)).
    replace (TFun ({0 |-> dx' }ᵈ d1) ({0 |-> dx' }ᵈ d2) ({0 |-> dx' }ᵀ T1) ({0 |-> dx' }ᵀ T2))
            with ({ 0 |-> dx' }ᵀ (TFun d1 d2 T1 T2)); auto.
    eapply IHHT2; eauto.
    1,3 : unfold openq; rewrite <- @subst1_qual_empty with (dx:=dx');
        erewrite <- subst1_open_qual_comm; eauto; erewrite <- subst1_open_qual_comm; eauto.
    * apply subst_qual_subqual_monotone. unfold openq in H4. auto.
    * apply subst1_senv_saturated; auto.
    * eauto.
    * erewrite <- not_free_subst1_ty_iff; eauto.
    * replace (∅) with ({0 |-> dx' }ᵈ ∅) at 1; auto. unfold open_ty. repeat erewrite <- subst1_open_ty_comm; eauto.
    * unfold openq. repeat erewrite <- subst1_open_qual_comm; eauto.
  - (* t_app_fresh *) intuition. rename H13 into IHHT1. rename H12 into IHHT2. simpl.
    replace ({ 0 |-> dx' }ᵈ (openq df d1 d2)) with
               (openq ({ 0 |-> dx' }ᵈ df) ({ 0 |-> dx' }ᵈ d1) ({ 0 |-> dx' }ᵈ d2)).
    replace ({0 |-> dx' }ᵀ (T2 <~ᵀ ∅; d1)) with
               (({0 |-> dx' }ᵀ T2) <~ᵀ ∅; ({0 |-> dx' }ᵈ d1)).
    (*separation/overap is preserved after substitution*)
    assert (Hoverlap: {0 |-> dx' }ᵈ (df' ⊓ d1') = {0 |-> dx' }ᵈ df' ⊓ {0 |-> dx' }ᵈ d1'). {
      (* specialize (has_type_filter HT1). specialize (has_type_filter HT2). *)
      symmetry. eapply subst1_preserves_separation; eauto.
    }
    eapply t_app_fresh with (T1:= { 0 |-> dx' }ᵀ T1) (df:=({0 |-> dx' }ᵈ df)) (d1:=({0 |-> dx' }ᵈ d1)) (df':=({0 |-> dx' }ᵈ df')) (d1':=({0 |-> dx' }ᵈ d1')); eauto.
    replace (TFun (({0 |-> dx' }ᵈ df' ⋒ {0 |-> dx' }ᵈ d1')) ({0 |-> dx' }ᵈ d2) ({0 |-> dx' }ᵀ T1) ({0 |-> dx' }ᵀ T2))
      with  ({0 |-> dx' }ᵀ (TFun (df' ⋒ d1') d2 T1 T2)). auto.
    simpl. rewrite subst1_qlub_dist. rewrite Hoverlap. rewrite subst1_fresh_id. auto.
    5 : unfold openq; rewrite <- @subst1_qual_empty with (dx:=dx');
        erewrite <- subst1_open_qual_comm; eauto; erewrite <- subst1_open_qual_comm; eauto.
    1,2,5,6,7 : apply subst_qual_subqual_monotone; auto.
    intro Hfresh. 1,2 : erewrite <- not_free_subst1_ty_iff; eauto; apply Substq_non_fresh in HSubst.
    1,2 : eapply subst1_saturated; eauto.
    unfold openq; rewrite <- @subst1_qual_empty with (dx:=dx');
    erewrite <- subst1_open_qual_comm; eauto; erewrite <- subst1_open_qual_comm; eauto. apply subst1_senv_saturated; auto.
    replace (∅) with ({0 |-> dx' }ᵈ ∅) at 1; auto. unfold open_ty. repeat erewrite <- subst1_open_ty_comm; eauto.
    unfold openq. repeat erewrite <- subst1_open_qual_comm; eauto.
  - (* t_loc *) rewrite subst1_qlub_dist. erewrite @subst1_qual_id with (q:=(&!l)); eauto. simpl. erewrite subst1_ty_id; eauto.
    erewrite subst1_qual_id; eauto. apply t_loc; auto. eapply closed_qual_subst1'; eauto.
    erewrite <- @subst1_qual_id with (q:=(&!l)); eauto. eapply subst_qual_subqual_monotone; eauto.
    2 : erewrite <- @subst1_qual_id with (q:=q); eauto; eapply subst_qual_subqual_monotone; eauto.
    all : apply indexr_var_some' in H3; eapply just_loc_closed; eauto.
  - (* t_ref *) rewrite subst1_qlub_dist. rewrite subst1_qual_fresh. simpl. apply t_ref; auto.
    eapply closed_ty_subst1'; eauto.
    erewrite <- subst1_qual_fresh.
    eapply subst_qual_subqual_monotone; eauto. apply subst1_non_fresh; eauto.
  - (* t_deref *) simpl. apply t_deref with (d := { 0 |-> dx' }ᵈ d); auto.
    apply subst1_non_fresh; eauto. apply subst_qual_subqual_monotone. auto.
    apply subst1_senv_saturated; auto.
  - (* t_assign *) rewrite subst1_qual_empty in *. simpl. simpl in IHHT1.
    apply t_assign with (T:={0 |-> dx' }ᵀ T) (d:=({0 |-> dx' }ᵈ d)) (d1:=({0 |-> dx' }ᵈ d1)); auto.
    apply subst1_non_fresh; eauto.
  - (* t_sub *) apply t_sub with (T1:={ 0 |-> dx' }ᵀ T1) (d1:={ 0 |-> dx' }ᵈ d1).
    eapply IHHT; eauto. eapply subst_stp; eauto. apply subst_qual_subqual_monotone; auto.
    apply subst1_senv_saturated; auto.
  Unshelve. all : auto.
Qed.

(* case for t_app *)
Lemma substitution1 : forall {t bf Tf df bx Tx dx Σ T d},
    has_type [(bx,Tx,dx) ; (bf,Tf,df)] (df ⊔ $!0 ⊔ $!1 ⊔ {♦}) Σ t T d ->
    forall {vf}, vtp Σ vf Tf df -> ♦∉ df ->
        forall {vx}, vtp Σ vx Tx dx -> ♦∉ dx ->
                    has_type [] (df ⊔ dx ⊔ {♦}) Σ
                             ({ 0 |-> vf ; vx }ᵗ t)
                             ({ 0 |-> df ; dx }ᵀ T)
                             ({ 0 |-> df ; dx }ᵈ d).
  intros. specialize (vtp_closed H0) as Hclf. specialize (vtp_closed H2) as Hclx.
  intuition. replace ([(bx,Tx, dx); (bf,Tf, df)]) with ([(bx,Tx,dx)] ++ [(bf,Tf, df)]) in H; auto.
  remember (df ⊔ $!0 ⊔ $!1 ⊔ {♦}) as DF.
  assert (Hsepf : df ⊓ DF ⊑ df). { destruct df. subst. qdec. }
  eapply (substitution_gen Hsepf) in H; eauto.
  replace ({0 |-> df }ᴳ [(bx, Tx, dx)]) with ([] ++ [(bx, Tx, dx)]) in H.
  replace ({0 |-> df }ᵈ DF) with (df ⊔ $!0 ⊔ {♦}) in H.
  assert (Hsepf' : dx ⊓ (df ⊔ $!0 ⊔ {♦}) ⊑ dx). auto.
  eapply (substitution_gen Hsepf') in H; eauto.
  replace ({0 |-> dx }ᵈ (df ⊔ $!0 ⊔ {♦})) with (df ⊔ dx ⊔ {♦}) in H. simpl in H. apply H.
  (*done, prove earlier replacements *)
  repeat rewrite subst1_qlub_dist. rewrite subst1_just_fv0. erewrite subst1_qual_id; eauto. rewrite subst1_fresh_id. auto.
  subst. repeat rewrite subst1_qlub_dist. rewrite subst1_just_fv0. rewrite <- subst1_just_fv. rewrite subst1_fresh_id.
  erewrite subst1_qual_id; eauto. rewrite (@qlub_assoc df df). rewrite qlub_idem. auto.
  simpl. erewrite subst1_qual_id; eauto. erewrite subst1_ty_id; eauto.
Qed.

(* t_app case *)
Lemma substitution_stp1 : forall{T1 T2},
    forall {bx Tx bf Tf df dx Σ d1 d2},
      stp ([(bx,Tx,dx); (bf,Tf,{♦})]) Σ T1 d1 T2 d2 ->
      closed_ty 0 0 (‖Σ‖) Tx ->
      closed_qual 0 0 (‖Σ‖) df -> closed_qual 0 0 (‖Σ‖) dx -> ♦∉ df -> ♦∉ dx ->
      stp [] Σ ({ 0 |-> df; dx }ᵀ T1) ({ 0 |-> df ; dx }ᵈ d1) ({ 0 |-> df ; dx }ᵀ T2) ({ 0 |-> df ; dx }ᵈ d2).
  intros. replace [(bx, Tx, dx); (bf, Tf,{♦})] with ([(bx, Tx, dx)] ++ [(bf, Tf,{♦})]) in H; auto.
  eapply @subst_stp with (df':=df) in H; auto.
  replace ({0 |-> df }ᴳ [(bx, Tx, dx)]) with ([(bx, Tx, dx)]) in H.
  replace ([(bx, Tx, dx)]) with ([] ++ [(bx, Tx, dx)]) in H; auto.
  eapply @subst_stp with (df':=dx) in H; auto. auto.
  simpl. erewrite subst1_ty_id; eauto. erewrite subst1_qual_id; eauto.
  replace ({♦}) with (∅ ⋒ df). auto. destruct df. qdec.
Qed.

(* case for t_app_fresh *)
Lemma substitution2 : forall {t bf Tf df df' Tx dx dx' Σ T d},
    has_type [(false,Tx,(df' ⊓ dx') ⊔ {♦}) ; (bf,Tf,df)] (df ⊔ $!0 ⊔ $!1 ⊔ {♦}) Σ t T d ->
    forall {vf}, vtp Σ vf Tf df -> ♦∉ df -> df ⊑ df' -> closed_qual 0 0 (‖Σ‖) df' ->
        forall {vx}, vtp Σ vx Tx dx -> ♦∉ dx -> dx ⊑ dx' -> closed_qual 0 0 (‖Σ‖) dx' ->
                    has_type [] (df ⊔ dx ⊔ {♦}) Σ
                             ({ 0 |-> vf ; vx }ᵗ t)
                             ({ 0 |-> df ; dx }ᵀ T)
                             ({ 0 |-> df ; dx }ᵈ d).
  intros. specialize (vtp_closed H0) as Hclf. specialize (vtp_closed H4) as Hclx.
  assert (Hcl : closed_qual 0 0 (‖ Σ ‖) (df' ⋒ dx')). { apply closed_qual_qlub; auto. apply closed_qual_qglb; auto. }
  intuition. replace ([(false,Tx, (df' ⋒ dx')); (bf,Tf, df)]) with ([(false,Tx, (df' ⋒ dx'))] ++ [(bf,Tf, df)]) in H; auto.
  remember (df ⊔ $!0 ⊔ $!1 ⊔ {♦}) as DF.
  assert (Hsepf : df ⊓ DF ⊑ df). { destruct df. subst. qdec. }
  eapply (substitution_gen Hsepf) in H; eauto.
  replace ({0 |-> df }ᴳ [(false, Tx, df' ⋒ dx')]) with ([(false, Tx, df' ⋒ dx')]) in H.
  replace ({0 |-> df }ᵈ DF) with (df ⊔ $!0 ⊔ {♦}) in H.
  assert (Hstparg : stp [] Σ Tx (df ⋒ dx) Tx (df' ⋒ dx')). { apply stp_refl; auto. }
  eapply narrowing in H; eauto.
  assert (Hsepf' : dx ⊓ (df ⊔ $!0 ⊔ {♦}) ⊑ (df ⊓ dx) ⊔ {♦}). {
    rewrite (@qglb_commute df dx). repeat rewrite qglb_qlub_dist_l. erewrite qglb_disjoint_freshv; eauto.
    destruct dx. destruct df. simpl in *. qdec.
  }
  replace ([(false, Tx, df ⋒ dx)]) with ([] ++ [(false, Tx, df ⋒ dx)]) in H.
  eapply (substitution_gen Hsepf') in H; eauto.
  replace ({0 |-> dx }ᵈ (df ⊔ $!0 ⊔ {♦})) with (df ⊔ dx ⊔ {♦}) in H. simpl in H. apply H.
  (*done, prove earlier replacements *)
  repeat rewrite subst1_qlub_dist. rewrite subst1_just_fv0. erewrite subst1_qual_id; eauto. rewrite subst1_fresh_id. auto.
  simpl. auto. subst. repeat rewrite subst1_qlub_dist. rewrite subst1_just_fv0. rewrite <- subst1_just_fv. rewrite subst1_fresh_id.
  erewrite subst1_qual_id; eauto. rewrite (@qlub_assoc df df). rewrite qlub_idem. auto.
  simpl. erewrite subst1_qual_id; eauto. erewrite subst1_ty_id; eauto.
Qed.

(* t_app_fresh case *)
Lemma substitution_stp2 : forall{T1 T2},
    forall {Tx bf Tf df df' dx dx' Σ d1 d2},
      stp ([(false,Tx,df' ⋒ dx'); (bf,Tf,{♦})]) Σ T1 d1 T2 d2 ->
      closed_ty 0 0 (‖Σ‖) Tx ->
      closed_qual 0 0 (‖Σ‖) df' -> closed_qual 0 0 (‖Σ‖) dx' -> ♦∉ df -> ♦∉ dx -> df ⊑ df' -> dx ⊑ dx' ->
      stp [] Σ ({ 0 |-> df; dx }ᵀ T1) ({ 0 |-> df ; dx }ᵈ d1) ({ 0 |-> df ; dx }ᵀ T2) ({ 0 |-> df ; dx }ᵈ d2).
  intros.  assert (Hcl : closed_qual 0 0 (‖ Σ ‖) (df' ⋒ dx')). { apply closed_qual_qlub; auto. apply closed_qual_qglb; auto. }
  replace [(false, Tx, df' ⋒ dx'); (bf, Tf,{♦})] with ([(false, Tx, df' ⋒ dx')] ++ [(bf, Tf,∅ ⋒ df)]) in H; auto.
  eapply @subst_stp with (df':=df) in H; eauto.
  replace ({0 |-> df }ᴳ [(false, Tx, df' ⋒ dx' )]) with ([(false, Tx, df' ⋒ dx')]) in H.
  assert (H' : stp [(false, Tx, df ⋒ dx)] Σ ({0 |-> df }ᵀ T1) ({0 |-> df }ᵈ d1) ({0 |-> df }ᵀ T2) ({0 |-> df }ᵈ d2)). {
    eapply narrowing_stp; eauto. apply stp_refl; auto.
  }
  replace ([(false, Tx, df ⋒ dx )]) with ([] ++ [(false, Tx, df ⋒ dx)]) in H'; auto.
  replace ([]) with ({0 |-> dx}ᴳ []); auto. eapply subst_stp; eauto.
  simpl. erewrite subst1_ty_id; eauto. erewrite subst1_qual_id; eauto.
  simpl. destruct df. repeat f_equal. qdec.
Qed.

Lemma open_qual_mono : forall {d1 d1' d2 k}, d1 ⊑ d1' -> ([[ k ~> d1 ]]ᵈ d2) ⊑ ([[ k ~> d1' ]]ᵈ d2).
  intros. destruct d2; destruct d1'; destruct d1. simpl.
  inversion H. intuition.
  destruct (mem k t0) eqn:Hmem.
  simpl. intuition; try fnsetdec. destr_bool. auto.
Qed.

Lemma open_qual_mono2 : forall {d1 d2 d2' k}, d2 ⊑ d2' -> ([[ k ~> d1 ]]ᵈ d2) ⊑ ([[ k ~> d1 ]]ᵈ d2').
  intros. destruct d2; destruct d2'; destruct d1; simpl; intuition.
  inversion H. intuition. destruct (mem k t0) eqn: Hmem1.
  destruct (mem k t3) eqn: Hmem2. qdec.
  specialize (@subset_inclusion _ _ _ H1 Hmem1 Hmem2) as F. inversion F.
  destruct (mem k t3) eqn: Hmem2. simpl. intuition; try fnsetdec. destr_bool.
  apply subset_union_remove; auto. auto.
Qed.

Lemma openq_mono : forall {d1 d1' d2 d2' d3 d3' f l},
    closed_qual 0 f l d1' -> closed_qual 0 f l d2' ->
    d1 ⊑ d1' -> d2 ⊑ d2' -> d3 ⊑ d3' -> (d3 <~ᵈ d1; d2) ⊑ (d3' <~ᵈ d1'; d2').
  intros. unfold openq.
  specialize (@open_qual_mono d1 d1' d3' 0 H1) as S1.
  specialize (@open_qual_mono2 d1 d3 d3' 0 H3) as S2.
  specialize (subqual_trans S2 S1) as S3. clear S1. clear S2.
  specialize (@open_qual_mono2 d2' _ _ 1 S3) as S4.
  eapply subqual_trans. 2: eauto. eapply open_qual_mono; eauto.
Qed.

Lemma open_ty'_closed : forall {l} {T} {A},
    closed_ty 0 0 l T ->
    closed_ty 0 2 l (T <~²ᵀ ([] : list A)).
  intros. unfold open_ty'. unfold open_ty.
  apply closed_ty_open_succ. auto. apply closed_ty_open_succ. auto.
Qed.

Lemma open_qual_qlub_dist : forall {k d1 d2 d3}, ([[ k ~> d1  ]]ᵈ (d2 ⊔ d3)) = (([[ k ~> d1  ]]ᵈ d2) ⊔ ([[ k ~> d1  ]]ᵈ d3)).
  intros. destruct d2; destruct d3; destruct d1; simpl; auto.
  destruct (mem k t0) eqn: Hmem1.
  - rewrite NatSet.F.mem_1. 2: apply NatSet.F.union_2; apply NatSet.F.mem_2; auto.
    destruct (mem k t3) eqn: Hmem2.
    simpl. qdec. simpl. f_equal; try fnsetdec. destr_bool.
    rewrite remove_union_dist; try fnsetdec. rewrite (@remove_not_in k t3); auto. fnsetdec.
  - destruct (mem k t3) eqn: Hmem2.
    rewrite NatSet.F.mem_1. 2: apply NatSet.F.union_3; apply NatSet.F.mem_2; auto.
    simpl. f_equal; try fnsetdec. destr_bool.
    rewrite remove_union_dist. rewrite (@remove_not_in k t0); auto. fnsetdec.
    rewrite not_member_union; auto.
Qed.

Lemma qfresh_true_open : forall {k d1 t t0 t1}, (♦∈? ([[k ~> d1 ]]ᵈ (qset true t t0 t1))) = true.
  intros. destruct d1. compute. destruct (mem k t0); auto.
Qed.

Lemma qfresh_true_openq : forall {d1 df t t0 t1}, (♦∈? ((qset true t t0 t1) <~ᵈ df; d1)) = true.
  intros. unfold openq. simpl. destruct (mem 0 t0); auto.
  destruct df. all :apply qfresh_true_open.
Qed.

Lemma open_qual_qqplus_dist : forall {k d1 d2 d3}, ♦∈ d2 -> ([[ k ~> d1 ]]ᵈ (d2 ⋓ d3)) = (([[ k ~> d1 ]]ᵈ d2) ⋓ ([[ k ~> d1 ]]ᵈ d3)).
  intros. destruct d2. destruct b; unfold qqplus.
  * rewrite qfresh_true. rewrite qfresh_true_open. apply open_qual_qlub_dist.
  * simpl in H. discriminate.
Qed.

(* Some distributive laws about openq and qqplus, required in the type safety proof for function application t_app. *)
Lemma open_qual_duplicate_eq : forall {k d1 d2 d}, ♦∈ d1 ->
  ([[ k ~> d1 ]]ᵈ d2 ⋓ d) = ([[ k ~> d1 ⋓ d ]]ᵈ d2 ⋓ d).
  intros. destruct d1. destruct b; unfold qqplus. 2: simpl in H; discriminate.
  destruct d. destruct d2. destruct b0.
  * repeat rewrite qfresh_true_open. unfold qfresh. simpl.
    destruct (mem k t6) eqn:Hmemk3; simpl; qdec.
  * simpl. destruct (mem k t6) eqn:Hmemk3; unfold qfresh; qdec.
Qed.

(* when the argument steps *)
Lemma openq_duplicate_eq_r : forall {df d1 d2 d}, ♦∈ d1 ->
  (d2 <~ᵈ df; d1 ⋓ d) = (d2 <~ᵈ df; (d1 ⋓ d) ⋓ d).
  intros. unfold openq. rewrite open_qual_duplicate_eq; auto.
Qed.

(* when the function steps *)
Lemma openq_duplicate_eq_l : forall {f l df d1 d2 d},
  ♦∈ df -> closed_qual 0 f l df -> closed_qual 0 f l d1 -> closed_qual 0 f l d ->
  (d2 <~ᵈ df; d1 ⋓ d) = ((d2 <~ᵈ df ⋓ d; d1) ⋓ d).
  intros. unfold openq. erewrite open_qual_commute''; eauto.
  erewrite @open_qual_commute'' with (i:=1); eauto.
  rewrite open_qual_duplicate_eq; auto.
  apply closed_qual_qqplus; auto.
Qed.

Lemma qqcap_fresh_r : forall {d1 df f Σ Σ' d'},
    closed_qual 0 f (‖Σ‖) d1 -> closed_qual 0 f (‖Σ‖) df ->
    Σ → Σ' ∋ df ⊕ d' -> (d1 ⋒ df) = (d1 ⋒ (df ⋓ d')).
  intros. destruct d1 as [fr1 f1 b1 l1]. destruct df as [frf ff bf lf].
  inversion H1; subst.
  - rewrite qqplus_qbot_right_neutral. auto.
  - assert (Hfresh: ~ In (‖Σ‖) l1). { inversion H. subst. apply bound_le_not_in. auto. }
     destruct q as [frq fq bq lq]. simpl in *. destruct frf. 2 : qdec.
    simpl in *. intuition. f_equal; try fnsetdec.
Qed.

Lemma qqcap_fresh_l : forall {d1 df f Σ Σ' d'},
    closed_qual 0 f (‖Σ‖) d1 -> closed_qual 0 f (‖Σ‖) df ->
    Σ → Σ' ∋ d1 ⊕ d' -> (d1 ⋒ df) = ((d1 ⋓ d') ⋒ df).
  intros. destruct d1 as [fr1 f1 b1 l1]. destruct df as [frf ff bf lf]. inversion H1; subst.
  - rewrite qqplus_qbot_right_neutral. auto.
  - assert (Hfresh: ~ In (‖Σ‖) lf). { inversion H0. subst. apply bound_le_not_in. auto. }
    destruct q as [frq fq bq lq]. simpl in *. destruct fr1. 2 : qdec.
    simpl in *. intuition. f_equal; try fnsetdec.
Qed.

Lemma openq_closed : forall {a b c f l},
    closed_qual 2 f l c -> closed_qual 0 f l a -> closed_qual 0 f l b -> closed_qual 0 f l (openq a b c).
  intros. unfold openq. eapply closed_qual_open2; eauto.
Qed.

Lemma disjointq_ldom : forall {Σ Σ' d d'}, Σ → Σ' ∋ d ⊕ d' -> d' ⊑ ldom Σ'.
  intros. inversion H; subst; auto. unfold ldom. unfold dom. inversion H2. subst.
  simpl.  apply bound_0_empty in H4, H5. subst. apply bound_dom_sub in H6. qdec.
Qed.
#[global] Hint Resolve disjointq_ldom : core.

Lemma disjointq_ldom' : forall {Σ Σ' d d'}, Σ → Σ' ∋ d ⊕ d' -> {♦} ⊔ d' ⊑ ldom Σ'.
  intros. inversion H; subst; auto; unfold ldom; unfold dom. qdec. inversion H2. subst.
  simpl.  apply bound_0_empty in H4, H5. subst. apply bound_dom_sub in H6. qdec.
Qed.
#[global] Hint Resolve disjointq_ldom' : core.

Lemma disjointq_closed : forall {Σ Σ' d d'}, Σ → Σ' ∋ d ⊕ d' -> closed_qual 0 0 (‖Σ'‖) d'.
  intros. inversion H; subst; auto. simpl. apply closed_qual_qlub. eapply closed_qual_monotone; eauto.
  apply just_loc_closed. simpl. lia.
Qed.
#[global] Hint Resolve disjointq_closed : core.

Lemma disjointq_saturated : forall {Σ Σ' d d'}, Σ → Σ' ∋ d ⊕ d' -> wf_senv Σ -> senv_saturated Σ' d'.
  intros. inversion H; subst. auto. eapply wf_senv_saturated_qplus; eauto. apply indexr_head.
Qed.
#[global] Hint Resolve disjointq_saturated : core.

Lemma disjointq_scale : forall {Σ Σ' d d'}, Σ → Σ' ∋ d ⊕ d' -> forall {d''}, d ⊑ d'' -> Σ → Σ' ∋ d'' ⊕ d'.
  intros. inversion H; subst. auto. econstructor; eauto. eapply subqual_trans; eauto.
Qed.
#[global] Hint Resolve disjointq_scale : core.


Lemma ldom_fresh : forall {A} {Σ : list A}, {♦} ⊑ ldom Σ.
  intros. simpl. intuition.
Qed.
#[global] Hint Resolve ldom_fresh : core.

(* well-typed values belonging to each type *)

Lemma vtp_canonical_form_loc : forall {Σ t T q d},
   vtp Σ t (TRef q T) d -> value t -> exists (l : loc), t = tloc l.
Proof. intros. remember (TRef q T) as R. remember t as tt. generalize dependent T.
       induction H; intuition; try discriminate; inversion H0; subst. exists l. intuition.
Qed.

Lemma vtp_canonical_form_lam : forall {Σ t T1 T2 d1 d2 df},
    vtp Σ t (TFun d1 d2 T1 T2) df -> value t -> exists (t' : tm), t = tabs t'.
Proof. intros Σ t T1 T2 d1 d2 df H. remember (TFun d1 d2 T1 T2) as T.
       generalize dependent d1. generalize dependent d2. generalize dependent T1. generalize dependent T2.
       induction H; intuition; try discriminate; inversion H0; subst. exists t. intuition.
Qed.

Lemma qstp_delete_fresh : forall {Σ q1 q2}, qstp [] Σ q1 q2 -> ♦∉ q1 -> qstp [] Σ q1 (qset false (qfvs q2) (qbvs q2) (qlocs q2)).
  intros. specialize (qstp_closed H) as Hcl. intuition. apply qstp_empty in H. apply qs_sq.
  destruct q1. destruct q2. qdec. destruct q2. simpl. inversion H2. subst. constructor; auto.
Qed.

Lemma senv_saturated_non_fresh : forall {Σ q}, senv_saturated Σ q -> senv_saturated Σ (qset false (qfvs q) (qbvs q) (qlocs q)).
  intros. unfold senv_saturated in *. intros. specialize (H l). destruct q. simpl in *. intuition.
  inversion H1. subst. econstructor; eauto. destruct q'. qdec.
Qed.

Lemma vtp_non_fresh : forall {Σ v T q}, vtp Σ v T q -> vtp Σ v T (qset false (qfvs q) (qbvs q) (qlocs q)).
  intros. destruct q. inversion H; subst.
  - constructor. inversion H0. subst. eauto. apply senv_saturated_non_fresh. auto.
  - inversion H0. subst. econstructor; eauto.
    apply qstp_delete_fresh; auto. apply senv_saturated_non_fresh. auto.
  - inversion H2. subst. econstructor; eauto.
    apply qstp_delete_fresh; auto. apply senv_saturated_non_fresh. auto.
Qed.

Lemma stp_set_not_fresh : forall {d1 T Γ Σ}, closed_ty 0 (‖Γ‖) (‖Σ‖) T -> closed_qual 0 (‖Γ‖) (‖Σ‖) d1 -> stp Γ Σ T (qset false (qfvs d1) (qbvs d1) (qlocs d1)) T d1.
  intros. apply stp_refl; auto.
Qed.
#[global] Hint Resolve stp_set_not_fresh : core.

Lemma openq_subqual_0 : forall {df d2 d1 l}, closed_qual 0 0 l df -> closed_qual 0 0 l d1 -> mem 0 (qbvs d2) = true -> df ⊑ d2 <~ᵈ df; d1.
  intros. destruct d2 as [fr2 f2 b2 l2]. destruct df as [frf ff bf lf]. destruct d1 as [fr1 f1 b1 l1].
  inversion H. inversion H0. subst. apply bound_0_empty in H8,H10,H18,H20. subst.
  unfold openq. simpl in *. rewrite H1. simpl. apply NatSet.F.mem_2 in H1. destruct (mem 1 (union (remove 0 b2) {}N)) eqn:Hmem.
  apply NatSet.F.mem_2 in Hmem. qdec.
  rewrite <- NatSetFacts.not_mem_iff in Hmem. qdec.
Qed.

Lemma openq_subqual_0_false : forall {df d2 d1}, mem 0 (qbvs d2) = false -> forall {df'}, d2 <~ᵈ df; d1 = d2 <~ᵈ df'; d1.
  intros. destruct d2 as [fr2 f2 b2 l2]. unfold openq. simpl in *. rewrite H. auto.
Qed.

Lemma openq_subqual_1 : forall {df d2 d1 l}, closed_qual 0 0 l df -> closed_qual 0 0 l d1 -> mem 1 (qbvs d2) = true -> d1 ⊑ d2 <~ᵈ df; d1.
  intros. destruct d2 as [fr2 f2 b2 l2]. destruct df as [frf ff bf lf]. destruct d1 as [fr1 f1 b1 l1].
  inversion H. inversion H0. subst. apply bound_0_empty in H8,H10,H18,H20. subst.
  unfold openq. simpl in *. destruct (mem 0 b2) eqn:Hmem; simpl. rewrite empty_union_right.
  assert (H1' : mem 1 (remove 0 b2) = true). { apply NatSet.F.mem_1. apply NatSet.F.mem_2 in H1,Hmem. fnsetdec. }
  rewrite H1'. apply NatSet.F.mem_2 in H1, Hmem. qdec.
  rewrite H1. qdec.
Qed.

Lemma openq_subqual_1_false : forall {df d2 d1 l}, closed_qual 0 0 l df -> mem 1 (qbvs d2) = false -> forall {d1'}, d2 <~ᵈ df; d1 = d2 <~ᵈ df; d1'.
  intros. destruct d2 as [fr2 f2 b2 l2]. destruct df as [frf ff bf lf]. destruct d1 as [fr1 f1 b1 l1]. unfold openq. simpl in *.
  inversion H. subst. apply bound_0_empty in H7, H9. subst.
  destruct (mem 0 b2) eqn:Hmem; simpl. repeat rewrite empty_union_right.
  assert (H0' : mem 1 (remove 0 b2) = false). {
    rewrite <- NatSetFacts.not_mem_iff in H0. apply NatSet.F.mem_2 in Hmem. rewrite <- NatSetFacts.not_mem_iff. fnsetdec.
  } rewrite H0'. 2: rewrite H0. all : auto.
Qed.

Lemma open_qual_not_free : forall {k q}, [[k ~> ∅ ]]ᵈ q = q -> forall {q'}, [[k ~> q' ]]ᵈ q = q.
  intros. destruct q. destruct q'. simpl in *. destruct (mem k t0) eqn:Hmem; auto.
  repeat rewrite empty_union_right in H. inversion H. rewrite <- H2 in Hmem.
  apply NatSet.F.mem_2 in Hmem. fnsetdec.
Qed.

Lemma not_free_prop1 : forall {T k}, not_free k T -> forall {d}, ([[k ~> d ]]ᵀ T) = T.
  unfold not_free. induction T; intros. auto. simpl in H. inversion H.
  rewrite H1, H2, H3, H4. simpl. rewrite IHT1; auto. rewrite IHT2; auto.
  repeat rewrite open_qual_not_free; auto.
  simpl in H. inversion H. rewrite H1, H2. simpl. rewrite IHT; auto.
  rewrite open_qual_not_free; auto.
Qed.

Lemma not_free_prop2 : forall {T k}, not_free k T -> forall {d d'}, ([[k ~> d ]]ᵀ T) = ([[k ~> d' ]]ᵀ T).
  intros. repeat rewrite not_free_prop1; auto.
Qed.
#[global] Hint Resolve not_free_prop2 : core.

Lemma not_free_prop3 : forall {T k}, not_free k T -> forall {f l}, closed_ty (S k) f l T -> closed_ty k f l T.
  intros. rewrite <- (@not_free_prop1 _ _ H ∅). eapply closed_ty_open'; eauto.
Qed.

(* Main results: type soundness & preservation of separation *)

Theorem type_safety: forall {Σ t T d},
  has_type [] (ldom Σ) Σ t T d -> wf_senv Σ -> (
    value t \/
    (forall {σ} , CtxOK [] (ldom Σ) Σ σ ->
      (exists t' σ',
        step t σ t' σ' /\ preserve [] Σ t' T d σ'
      )
    )
  ).

Proof. intros Σ t T d H HwfSigma.
       specialize (has_type_closed H) as HX. remember [] as G. remember t as tt. remember T as TT. remember (ldom Σ) as φ.
       revert T t HeqTT Heqtt HeqG Heqφ.
       induction H; try (left; constructor); intros.
   + (* tvar *)  subst. inversion H.

   + (* tapp *) right. subst. intuition.
     apply has_type_closed in H as HH. intuition. apply has_type_closed in H0 as HH0. intuition.
     (* t1 *) specialize (H11 (TFun d1 d2 T1 T2) t1). intuition.

     (* t2 *) specialize (H8 T1 t2). intuition.
     - (* contraction *)
       (* turn has_type to vtp *)
       apply has_type_vtp in H as VH; intuition.
       pose (VHH := VH). inversion VH. subst.

       specialize (has_type_filter H0) as Hflt0.

       apply has_type_vtp in H0 as VH0; intuition.

       exists (open_tm (tabs t) t2 t). exists σ. intuition.
       * constructor. intuition.

       * apply (Preserve Σ ∅); auto.  rewrite qqplus_qbot_right_neutral.
         apply qstp_closed in H30 as H32'; intuition.

         change (length []) with 0 in *. subst.
         pose (VH' := H28). eapply t_abs with (φ:=df1) in VH'; eauto. apply has_type_vtp in VH'; auto.

         assert (HT' : has_type [(false, T1, d1) ; (true, TFun d0 d3 T0 T3, df1)] (df1 ⊔ $!0 ⊔ $!1 ⊔ {♦}) Σ (open_tm' ([]:tenv) t) (open_ty' ([]:tenv) T3) (openq' ([]:tenv) d3)). {
           eapply narrowing. eapply H28. intuition. auto.
         }
         eapply @substitution1 with ( vx:= t2) in HT' as HT''; eauto; intuition.

         unfold open_tm' in HT''. unfold open_ty' in HT''. unfold openq' in HT''. simpl in HT''. inversion H26; subst. inversion H27. subst.
         unfold open_ty in HT''. unfold openq in HT''.

         erewrite <- open_subst2_tm in HT''; eauto.
         erewrite <- open_subst2_ty in HT''; eauto.
         erewrite <- open_subst2_qual in HT''; eauto.
         fold (open_tm (tabs t) t2 t) in HT''. fold (openq df1 d1 d3) in HT''. fold (open_ty df1 d1 T3) in HT''.
         apply @weaken_flt with (φ':= (ldom Σ)) in HT''; auto; intuition.
         eapply t_sub; eauto.

         pose (Hsub:=H33). eapply @substitution_stp1 with (df:=df1) in Hsub; eauto.
         simpl in Hsub. unfold openq' in Hsub. unfold openq in Hsub. unfold open_ty' in Hsub. unfold open_ty in Hsub. simpl in Hsub.
         erewrite <- open_subst2_ty in Hsub; eauto. erewrite <- open_subst2_ty in Hsub; eauto.
         erewrite <- open_subst2_qual in Hsub; eauto. erewrite <- open_subst2_qual in Hsub; eauto.
         unfold open_ty. unfold openq.
         replace ([[0 ~> ∅ ]]ᵀ T2) with ([[0 ~> df1 ]]ᵀ T2); auto. (* since not_free 0 T2 *)

         eapply s_trans; eauto. apply stp_refl; auto. apply closed_ty_open2; auto.
         constructor. eapply openq_mono; eauto. apply qstp_empty in H30. auto. apply openq_closed; auto.

         eapply openq_subqual; eauto. apply has_type_filter in H. auto.
         eapply senv_saturated_openq; eauto. eapply has_type_senv_saturated; eauto.
         repeat apply qlub_bound; auto. apply has_type_filter in H. apply qstp_empty in H30.
         eapply subqual_trans; eauto.

     -  (* right congruence *)
        apply has_type_vtp in H as VH; intuition.
        apply vtp_canonical_form_lam in VH as HH; intuition.

        pose (HH12 := H10).
        unfold CtxOK in HH12. specialize (H11 σ). intuition.

        destruct H22 as [t2' [σ' HH9]]. exists (tapp t1 t2'). exists σ'. intuition. constructor; intuition.

        (* d1 is not fresh, so we don't observe the growth *)
        destruct H22. apply (Preserve Σ' ∅); intuition.
        rewrite not_fresh_qqplus in H26; auto. rewrite qqplus_qbot_right_neutral.
        eapply t_app with (T1:=T1); eauto. eapply weaken_flt. eapply weaken_store; eauto. auto. auto.
        eapply subqual_trans; eauto.
        eapply weaken_store_senv_saturated; eauto.

     -  (* left congruence *)
        apply has_type_closed in H0 as Hcl. intuition.
        specialize (H19 σ H10). destruct H19 as [t1' [σ' HH7]]. exists (tapp t1' t2). exists σ'. intuition. apply step_c_app_l. intuition.
        destruct H23. destruct (mem 0 (qbvs d2)) eqn:Hmem.
        * (* d2 is dependent on f, so the growth in df might be observable  *)
          apply (Preserve Σ' d'); auto.
          -- eapply disjointq_scale; eauto. eapply openq_subqual_0; eauto. (* this is the sole reason why need to distinguish whether d2 is dependent on f or not *)
          -- destruct (♦∈? df) eqn:Hfresh.
             ** erewrite @openq_duplicate_eq_l with (f:=0) (l:=‖Σ'‖). 3,4 : eapply closed_qual_monotone; eauto. 2,3 : eauto.
                eapply t_sub with (T1 := (T2 <~ᵀ ∅; d1))(d1 := (openq (df ⋓ d') d1 d2)).
                --- eapply t_app with (T1:=T1) (df:=(df ⋓ d')); eauto.
                    eapply weaken_flt. eapply weaken_store; eauto. auto. auto.
                    eapply subqual_trans; eauto. eapply weaken_store_senv_saturated; eauto.
                --- apply stp_refl. simpl. eapply closed_ty_monotone; eauto.
                    constructor; auto. apply closed_qual_qqplus; auto.
                    inversion H13; subst. apply openq_closed. 2 : apply closed_qual_qqplus.
                    1,2,4 : eapply closed_qual_monotone; eauto; lia. all: eapply disjointq_closed; eauto.
                --- apply has_type_filter in H0. apply has_type_filter in H. apply qqplus_bound.
                    eapply openq_subqual; eauto. apply qqplus_bound.
                    1,3,4 : eapply subqual_trans; eauto. all : eapply disjointq_ldom; eauto.
                --- apply senv_saturated_qqplus; eauto. eapply senv_saturated_openq.
                    apply senv_saturated_qqplus; eauto. 1,3,5 : eapply weaken_store_senv_saturated; eauto.
                    1,2 : eapply has_type_senv_saturated; eauto. apply closed_qual_qqplus. 1,3 : eapply closed_qual_monotone; eauto. eauto.
             ** rewrite not_fresh_qqplus in H28; auto. apply t_sub with (T1:=(T2 <~ᵀ ∅; d1)) (d1:=d2 <~ᵈ df; d1).
                --- eapply t_app with (T1:=T1); eauto. eapply weaken_flt. eapply weaken_store; eauto. auto. auto.
                    eapply subqual_trans; eauto. eapply weaken_store_senv_saturated; eauto.
                --- inversion H13. subst. clear H39. apply stp_refl. simpl. eapply closed_ty_monotone; eauto.
                    constructor. auto. apply closed_qual_qqplus; auto.
                    apply openq_closed; try solve [eapply closed_qual_monotone; eauto]. eauto.
                --- apply qqplus_bound. apply has_type_filter in H0. apply has_type_filter in H. eapply openq_subqual; eauto.
                    1,2,3 : eapply subqual_trans; eauto. eapply disjointq_ldom; eauto.
                --- apply senv_saturated_qqplus; eauto. eapply weaken_store_senv_saturated; eauto. eapply senv_saturated_openq.
                    eapply has_type_senv_saturated; eauto. apply has_type_closed in H. intuition. eauto.
                    eapply has_type_senv_saturated; eauto. apply has_type_closed in H0. intuition. eauto.
        * (* d2 is not dependent on f, so we don't observe the growth in df *)
          apply (Preserve Σ' ∅); auto. rewrite qqplus_qbot_right_neutral.
          replace (d2 <~ᵈ df; d1) with (d2 <~ᵈ df ⋓ d'; d1). (* since f doesn't occur in d2 *)
          eapply t_app with (T1:=T1); eauto. eapply weaken_flt. eapply weaken_store; eauto. auto. auto.
          eapply subqual_trans; eauto.
          eapply weaken_store_senv_saturated; eauto.
          apply openq_subqual_0_false; auto.

    + (* t_app_fresh *) right. subst. intuition.
     apply has_type_closed in H as HH. intuition. apply has_type_closed in H2 as HH0. intuition.
     (* t1 *) specialize (H17 (TFun (df' ⋒ d1') d2 T1 T2) t1). intuition.

     (* t2 *) specialize (H14 T1 t2). intuition.

     - (* contraction *)
       (* turn has_type to vtp *)
       apply has_type_vtp in H as VH; intuition.
       pose (VHH := VH). inversion VH. subst.

       specialize (has_type_filter H2) as Hflt0.

       apply has_type_vtp in H2 as VH0; intuition.

       exists (open_tm (tabs t) t2 t). exists σ. intuition.
       * constructor. intuition.

       * apply (Preserve Σ ∅); auto. rewrite qqplus_qbot_right_neutral.
         apply qstp_closed in H36 as H37'; intuition.

         change (length []) with 0 in *. subst.
         pose (VH' := H34). eapply t_abs with (φ:=df1) in VH'; eauto. apply has_type_vtp in VH'; auto.

         (* remove potential freshness flag from the argument, in order to apply substitution lemma *)
         apply vtp_non_fresh in VH0. remember (qset false (qfvs d1) (qbvs d1) (qlocs d1)) as d1''.
         assert (Hd1'' : d1'' ⊑ d1'). { subst. eapply subqual_trans; eauto. }
         assert (Hdf1 : df1 ⊑ df'). { apply qstp_empty in H36. eapply subqual_trans; eauto. }
         assert (Hd1''fr : ♦∉ d1''). { subst. auto. }

         assert (HT' : has_type [(false, T1, df' ⋒ d1') ; (true, TFun d0 d3 T0 T3, df1)] (df1 ⊔ $!0 ⊔ $!1 ⊔ {♦}) Σ (open_tm' ([]:tenv) t) (open_ty' ([]:tenv) T3) (openq' ([]:tenv) d3)). {
           eapply narrowing. eapply H34. intuition. auto.
         }
         eapply @substitution2 with ( vx:= t2) in HT' as HT''; eauto; intuition.

         unfold open_tm' in HT''. unfold open_ty' in HT''. unfold openq' in HT''. simpl in HT''. inversion H32; subst.
         unfold open_ty in HT''. unfold openq in HT''.

         erewrite <- open_subst2_tm in HT''; eauto.
         erewrite <- open_subst2_ty in HT''; eauto.
         erewrite <- open_subst2_qual in HT''; eauto.
         fold (open_tm (tabs t) t2 t) in HT''. fold (openq df1 (qset false (qfvs d1) (qbvs d1) (qlocs d1)) d3) in HT''.
         apply @weaken_flt with (φ':= (ldom Σ)) in HT''; auto; intuition.
         eapply t_sub; eauto.

         inversion H33. subst. rename H39 into Hsub.
         eapply @substitution_stp2 with (dx := (qset false (qfvs d1) (qbvs d1) (qlocs d1))) (df:=df1) in Hsub; eauto.

         simpl in Hsub. unfold openq' in Hsub. unfold openq in Hsub. simpl in Hsub.
         unfold open_ty' in Hsub. unfold open_ty in Hsub.
         erewrite <- open_subst2_ty in Hsub; eauto. erewrite <- open_subst2_ty in Hsub; eauto.
         erewrite <- open_subst2_qual in Hsub; eauto. erewrite <- open_subst2_qual in Hsub; eauto.
         fold (openq df1 (qset false (qfvs d1) (qbvs d1) (qlocs d1)) d3) in Hsub. fold (openq df1 (qset false (qfvs d1) (qbvs d1) (qlocs d1)) d2) in Hsub.
         fold (open_ty df1 (qset false (qfvs d1) (qbvs d1) (qlocs d1)) T3) in Hsub. fold (open_ty df1 (qset false (qfvs d1) (qbvs d1) (qlocs d1)) T2) in Hsub.
         fold (open_ty df1 (qset false (qfvs d1) (qbvs d1) (qlocs d1)) T3).
         (* need to reason about growth of d1 *)
         { destruct (♦∈? d1) eqn:Hfresh.
         ++ (* d1 fresh, so the function can't be dependent on the argument *)
            intuition. replace (T2 <~ᵀ ∅; d1) with T2. replace (T2 <~ᵀ df1; (qset false (qfvs d1) (qbvs d1) (qlocs d1))) with T2 in Hsub. (* since no dependence *)
            eapply s_trans; eauto. apply stp_refl; auto. apply not_free_prop3; auto. apply not_free_prop3; auto.
            constructor; auto. eapply openq_mono; eauto. apply qstp_empty in H36. auto.
            all : unfold open_ty; rewrite not_free_prop1; auto. all : rewrite not_free_prop1; auto.
         ++ (* d1 non-fresh *)
            assert (Hd1 : (qset false (qfvs d1) (qbvs d1) (qlocs d1))= d1). { destruct d1. simpl. simpl in Hfresh. subst. auto. }
            rewrite Hd1 in *. replace (T2 <~ᵀ ∅; d1) with (T2 <~ᵀ df1; d1). (* since no dependence *)
            eapply s_trans; eauto. apply stp_refl; auto. apply closed_ty_open2; auto. constructor; auto.
            eapply openq_mono; eauto. apply qstp_empty in H36. auto.
            unfold open_ty. f_equal. auto.
         }

         eapply openq_subqual; eauto. apply has_type_filter in H. auto.
         eapply senv_saturated_openq; eauto. eapply has_type_senv_saturated; eauto.
         repeat apply qlub_bound; auto. apply has_type_filter in H.
         eapply subqual_trans; eauto. destruct d1. qdec.
         1,2 : inversion H33; auto.

     -  (* right congruence *)
        apply has_type_vtp in H as VH; intuition.
        apply vtp_canonical_form_lam in VH as HH; intuition.
        specialize (H17 σ). intuition.

        destruct H14 as [t2' [σ' HH22]]. exists (tapp t1 t2'). exists σ'. intuition. constructor; intuition.

        destruct H17. destruct (♦∈? d1) eqn:Hfresh.
        * (* d1 fresh *) destruct (mem 1 (qbvs d2)) eqn:Hmem.
          -- (* d2 dependent on x *) apply (Preserve Σ' d'); auto.
             eapply disjointq_scale; eauto. eapply openq_subqual_1; eauto. intuition.
             replace (T2 <~ᵀ ∅; d1) with (T2 <~ᵀ ∅; (d1 ⋓ d')). (* T2 not dependent on x *)
             rewrite openq_duplicate_eq_r; auto. apply t_sub with (T1 := (T2 <~ᵀ ∅; (d1 ⋓ d'))) (d1 := (openq df (d1 ⋓ d') d2)).
             ** eapply t_app_fresh with (T1 := T1) (d1':=d1' ⋓ d') (df':=df') (df:=df); eauto. replace (df' ⋒ d1' ⋓ d') with (df' ⋒ d1').
                eapply weaken_flt. eapply weaken_store; eauto. all : auto. eapply @qqcap_fresh_r with (Σ':=Σ'); eauto.
                eapply subqual_trans; eauto; apply extends_ldom; auto. apply qqplus_bound; eauto. 1,2 : eapply subqual_trans; eauto.
                apply saturated_qqplus; eauto. 1,2: eapply weaken_store_saturated; eauto.
                eapply weaken_store_saturated; eauto.
            **  apply has_type_closed in H30. intuition. inversion H19. subst.
                apply stp_refl. unfold open_ty. eapply closed_ty_open2; eauto. eapply closed_ty_monotone; eauto.
                constructor; auto. apply closed_qual_qqplus; auto.
                eapply openq_closed; try solve [eapply closed_qual_monotone; eauto]. eauto.
            **  apply has_type_filter in H2. apply has_type_filter in H. apply qqplus_bound. eapply openq_subqual; eauto.
                2: apply qqplus_bound. 1, 2, 4 : eapply subqual_trans; eauto. eapply subqual_trans; eauto. all : eauto.
            **  apply senv_saturated_qqplus; eauto. eapply senv_saturated_openq.
                1, 5 : eapply weaken_store_senv_saturated; eauto. 1,3 : eapply has_type_senv_saturated; eauto.
                2 : apply closed_qual_qqplus. 1,2 : eapply closed_qual_monotone; eauto. eauto.
            ** unfold open_ty. apply not_free_prop2. rewrite not_free_prop1; auto.
          -- (* d2 not dependent on x *) apply (Preserve Σ' ∅); auto. rewrite qqplus_qbot_right_neutral. intuition.
             replace (d2 <~ᵈ df; d1) with (d2 <~ᵈ df; (d1 ⋓ d')).  replace (T2 <~ᵀ ∅; d1) with (T2 <~ᵀ ∅; (d1 ⋓ d')). (* T2 not dependent on x *)
             eapply t_app_fresh with (T1:=T1) (d1':=((d1' ⋓ d'))); eauto.
             erewrite <- @qqcap_fresh_r with (Σ':=Σ'); eauto.
             eapply weaken_flt. eapply weaken_store; eauto. auto. auto.
             eapply subqual_trans; eauto. apply qqplus_bound; eauto.
             1,2 : eapply subqual_trans; eauto. apply saturated_qqplus; eauto.
             1,2 : eapply weaken_store_saturated; eauto. eapply weaken_store_senv_saturated; eauto.
             unfold open_ty. repeat rewrite not_free_prop1; auto.
             eapply openq_subqual_1_false; eauto.
        * (* d1 not fresh *) rewrite not_fresh_qqplus in H30; auto. apply (Preserve Σ' ∅); auto.
          rewrite qqplus_qbot_right_neutral.
          eapply t_app_fresh with (T1:=T1); eauto. eapply weaken_flt. eapply weaken_store; eauto. auto. auto.
          eapply subqual_trans; eauto. 1,2 : eapply subqual_trans; eauto.
          1,2 : eapply weaken_store_saturated; eauto. eapply weaken_store_senv_saturated; eauto.

     -  (* left congruence *)
        apply has_type_closed in H2 as Hcl. intuition.
        specialize (H25 σ H16). destruct H25 as [t1' [σ' HH6]]. exists (tapp t1' t2). exists σ'. intuition. apply step_c_app_l. intuition.
        destruct H29. destruct (♦∈? df) eqn:Hfresh.
        * (* df fresh *) destruct (mem 0 (qbvs d2)) eqn:Hmem.
          -- (* d2 dependent on f *) apply (Preserve Σ' d'); auto.
            eapply disjointq_scale; eauto. eapply openq_subqual_0; eauto.
            erewrite @openq_duplicate_eq_l with (l:=‖Σ'‖) (f:=0); auto. 2,3 : eapply closed_qual_monotone; eauto. 2: eauto.
            apply t_sub with (T1 := (T2 <~ᵀ ∅; d1)) (d1 := (openq (df ⋓ d') d1 d2)).
            ** eapply t_app_fresh with (T1 := T1) (df':=df' ⋓ d'); eauto. erewrite <- @qqcap_fresh_l with (Σ':=Σ'); eauto.
               eapply weaken_flt. eapply weaken_store; eauto. all : auto.
               eapply subqual_trans; eauto; apply extends_ldom; auto. 2 : apply qqplus_bound; eauto. 1,2 : eapply subqual_trans; eauto.
               2 : apply saturated_qqplus; eauto. 1,2: eapply weaken_store_saturated; eauto.
               eapply weaken_store_saturated; eauto.
            ** apply has_type_closed in H34. intuition. inversion H19. subst.
               apply stp_refl. simpl. eapply closed_ty_monotone; eauto.
               constructor; auto. apply closed_qual_qqplus; auto.
               eapply openq_closed; try solve [eapply closed_qual_monotone; eauto]. eauto.
            ** apply has_type_filter in H2. apply has_type_filter in H. apply qqplus_bound. eapply openq_subqual; eauto.
               apply qqplus_bound. 1, 3, 4 : eapply subqual_trans; eauto. eapply subqual_trans; eauto. all : eauto.
            ** apply senv_saturated_qqplus; eauto. eapply senv_saturated_openq. apply senv_saturated_qqplus.
               1,4,6 : eapply weaken_store_senv_saturated; eauto. 1,2 : eapply has_type_senv_saturated; eauto. eauto.
               apply closed_qual_qqplus. 1,3 : eapply closed_qual_monotone; eauto. eauto.
          -- (* d2 not dependent on f *) apply (Preserve Σ' ∅); auto. rewrite qqplus_qbot_right_neutral.
             replace (d2 <~ᵈ df; d1) with (d2 <~ᵈ df ⋓ d'; d1).
             eapply t_app_fresh with (T1:=T1) (df':=((df' ⋓ d'))); eauto.
             erewrite <- @qqcap_fresh_l with (Σ':=Σ'); eauto.
             eapply weaken_flt. eapply weaken_store; eauto. auto. auto.
             eapply subqual_trans; eauto. 2:  apply qqplus_bound; eauto.
             1,2 : eapply subqual_trans; eauto. 2 : apply saturated_qqplus; eauto.
             1,2 : eapply weaken_store_saturated; eauto. eapply weaken_store_senv_saturated; eauto.
             eapply openq_subqual_0_false; auto.
        * (* df not fresh *) rewrite not_fresh_qqplus in H34; auto. apply (Preserve Σ' ∅); auto.
          rewrite qqplus_qbot_right_neutral.
          eapply t_app_fresh with (T1:=T1); eauto. eapply weaken_flt. eapply weaken_store; eauto. auto. auto.
          eapply subqual_trans; eauto. 1,2 : eapply subqual_trans; eauto.
          1,2 : eapply weaken_store_saturated; eauto. eapply weaken_store_senv_saturated; eauto.

  + (*tref*) subst. intuition. specialize (has_type_closed H) as HH. intuition. specialize (H8 T t). intuition.
    * (*contraction*) right. intros.
      exists (tloc (‖σ‖)). exists (t :: σ). intuition.
      econstructor; eauto. apply (Preserve ((T,d1) :: Σ) (d1 ⊔ &!‖σ‖)); auto.
      apply wf_senv_cons; auto. eapply has_type_senv_saturated; eauto.
      eapply CtxOK_weaken_flt. apply CtxOK_ext; auto. apply H8. all: auto.
      inversion H8. rewrite <- H13. eapply disj_loc; eauto. eapply has_type_senv_saturated; eauto.
      inversion H8. rewrite qqplus_fresh; auto. rewrite qlub_assoc. rewrite <- @qlub_assoc with (q1:={♦}). rewrite qlub_idem.
      apply t_sub with (T1:=TRef d1 T) (d1:=(d1 ⊔ &!‖σ‖)).
      apply t_loc; auto. rewrite <- H13.
      apply indexr_head. simpl. eapply closed_ty_monotone; eauto. simpl. eapply closed_qual_monotone; eauto.
      simpl. intuition. unfold dom. simpl. rewrite H13. fnsetdec.
      apply has_type_filter in H. eapply subqual_trans; eauto.
      apply stp_refl; auto. constructor; auto. simpl. eapply closed_ty_monotone; eauto. eapply closed_qual_monotone; eauto.
      constructor. auto. repeat apply closed_qual_qlub; auto.
      simpl. eapply closed_qual_monotone; eauto.
      apply just_loc_closed. rewrite <- H13. auto.
      rewrite <- qlub_assoc. eapply @disjointq_ldom' with (Σ:=Σ) (d:={♦} ⊔ d1); eauto. rewrite <- H13. eapply disj_loc; eauto.
      eapply has_type_senv_saturated; eauto.
      rewrite <- qlub_assoc. apply saturated_senv_qlub; auto.
      eapply wf_senv_saturated_qplus. apply wf_senv_cons; eauto. eapply has_type_senv_saturated; eauto.
      rewrite <- H13. rewrite indexr_head. eauto.
    * (*congruence*) right. intros. specialize (H11 σ H8). destruct H11 as [t' [σ' HH10]].
      exists (tref t'). exists σ'. intuition. econstructor; eauto.
      destruct H13. apply (Preserve Σ' ∅); intuition. rewrite qqplus_qbot_right_neutral.
      rewrite not_fresh_qqplus in H17; auto.
      eapply t_ref; eauto. inversion H4. subst. eapply closed_ty_monotone; eauto.

  + (*tderef*) subst. intuition. specialize (has_type_closed H) as HH. intuition. specialize (H8 (TRef d1 T0) t). intuition.
    * (* contraction *) right. intros. pose (HV := H). apply has_type_vtp in HV; intuition.

      specialize (vtp_canonical_form_loc HV) as Hcan. intuition. destruct H13 as [l HH10]. subst.

      pose (HHV := HV). inversion HHV. subst.  pose (HH3 := H8). inversion HH3. subst.
      pose (HH14 := H19). apply indexr_var_some' in HH14. rewrite H13 in HH14. apply indexr_var_some in HH14.
      destruct HH14 as [v HHH14].  exists v. exists σ. intuition. apply step_deref; intuition.
      apply (Preserve Σ ∅); intuition. rewrite qqplus_qbot_right_neutral.
      specialize (H14 l v T d1). apply t_sub with (T1 := T)(d1:= d1); auto. intuition.
      replace (d1) with (∅ ⊔ d1); auto. apply stp_scale_qlub; auto.

    * (*congruence *) right. intros. specialize (H11 σ H8).
      destruct H11 as [t' [σ' HH8]]. exists (tderef t'). exists σ'. intuition. constructor; auto.
      destruct H13. apply (Preserve Σ' ∅); intuition. rewrite qqplus_qbot_right_neutral. eapply t_deref; eauto.
      eapply subqual_trans; eauto. eapply weaken_store_senv_saturated; eauto.

  + (*tassign*) subst. intuition. rename H into Ht1. rename H0 into Ht2. intuition.
    apply has_type_closed in Ht1 as Ht1C. intuition.
    apply has_type_closed in Ht2 as Ht2C. intuition.
    specialize (H8 (TRef d1 T) t1). intuition.
    specialize (H5 T t2). intuition.
    * (* contraction *)
      right. intros.
      pose (Ht1' := Ht1). eapply has_type_vtp in Ht1'; eauto.
      pose (Hloc := Ht1'). apply vtp_canonical_form_loc in Hloc; auto.
      inversion Ht1'. destruct Hloc. subst.
      pose (Ht2' := Ht2). apply has_type_vtp in Ht2'; auto.
      exists tunit. exists (update σ x t2). inversion H25. subst.
      inversion H5. subst. specialize (indexr_var_some' H20) as HH20. intuition.
      econstructor; eauto. rewrite <- H15. auto. apply (Preserve Σ ∅); auto.
      eapply CtxOK_update; eauto. rewrite <- H15. auto. apply t_sub with (T1:=T) (d1:=d1); auto.
      replace (d1) with (∅ ⊔ d1); auto. apply stp_scale_qlub; auto.
      apply has_type_filter in Ht2; auto.
      eapply has_type_senv_saturated; eauto.
    * (* right congruence *)
      right. intros. specialize (H8 σ H5). destruct H8 as [t' [σ' H4']].
      exists (tassign t1 t'). exists σ'. intuition. econstructor; eauto.
      pose (HV := Ht1). apply has_type_vtp in HV; intuition. inversion HV; subst.
      destruct H15. apply (Preserve Σ' ∅); eauto. rewrite not_fresh_qqplus in H26; auto. simpl.
      eapply t_assign; eauto. eapply weaken_flt. eapply weaken_store; eauto. auto. auto.
    * (* left congruence *)
      right. intros. specialize (H13 σ H8). destruct H13 as [t' [σ' H12']].
      exists (tassign t' t2). exists σ'. intuition. econstructor; eauto.
      destruct H15. apply (Preserve Σ' ∅); eauto. simpl.
      eapply t_assign; eauto. eapply weaken_flt. eapply weaken_store; eauto.
      all: auto.

  + (*t_sub*) subst. intuition. specialize (stp_closed H0) as H00. intuition.
    specialize (H8 T1 t). intuition. right.
    intros. specialize (H11 σ H8). destruct H11 as [t' [σ' HH8]]. exists t'. exists σ'. intuition.
    destruct H13. apply (Preserve Σ' d'); intuition. eapply disjointq_scale; eauto. apply stp_qstp_inv in H0.
    apply qstp_empty in H0. auto. eapply t_sub; eauto. apply stp_scale_qqplus.
    eapply weaken_stp_store_ext; eauto. eapply disjointq_closed; eauto.
    apply qqplus_bound. eapply subqual_trans; eauto. eapply disjointq_ldom; eauto.
    apply senv_saturated_qqplus; eauto. eapply weaken_store_senv_saturated; eauto.
Qed.

(* To show preservation_of_separation, we derive progress & preservation from type safety: *)

(* This requires proving that the reduction relation is deterministic. *)
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
    has_type [] (ldom Σ) Σ t T d -> wf_senv Σ ->
    value t \/ forall {σ}, CtxOK [] (ldom Σ) Σ σ -> exists t' σ', step t σ t' σ'.
Proof. intros Σ t T d HT Hwf.
       specialize (type_safety HT). intuition. right. intros σ HCtxOK.
       specialize (H σ). intuition. destruct H0 as [t' [σ' [Hstep  HPreserve]]].
       exists t'. exists σ'. intuition.
Qed.

Lemma preservation : forall {Σ t T d},
    has_type [] (ldom Σ) Σ t T d -> wf_senv Σ ->
    forall{σ}, CtxOK [] (ldom Σ) Σ σ ->
    forall {t' σ'}, step t σ t' σ' ->
    preserve [] Σ t' T d σ'.
Proof.  intros Σ t T d HT Hwf σ  HCtxOK t' σ' HStep.  specialize (type_safety HT). intuition.
  + inversion HStep; subst; inversion H.
  + specialize (H σ HCtxOK). destruct H as [t'' [σ'' [HStep2 HPreserve]]].
    assert (t'' = t' /\ σ' = σ''). { intuition. 1,2: eapply step_deterministic; eauto.  }
    intuition. subst. intuition.
Qed.

Corollary preservation_of_separation : forall {Σ t1 T1 q1 t2 T2 q2},
  has_type [] (ldom Σ) Σ t1 T1 q1 ->
  has_type [] (ldom Σ) Σ t2 T2 q2 -> wf_senv Σ -> q1 ⋒ q2 ⊑ {♦} ->
    forall{σ}, CtxOK [] (ldom Σ) Σ σ ->
      forall {t1' σ'}, step t1 σ t1' σ' ->
      forall {t2' σ''}, step t2 σ' t2' σ'' -> separate Σ t1' T1 t2' T2.
  intros Σ t1 T1 q1 t2 T2 q2 HT1 HT2 Hwf Hsep σ HOK t1' σ' Hstep1 t2' σ'' Hstep2.
  (* execute preservation in sequence *)
  specialize (preservation HT1 Hwf HOK Hstep1) as P1. destruct P1 as [Σ' d1 Hext1 Hwf' HOK' Hdisj1 HT1'].
  assert (HT2': has_type [] (ldom Σ') Σ' t2 T2 q2). {
    eapply weaken_flt. eapply weaken_store. eauto. auto. apply extends_ldom; auto. auto.
  }
  specialize (preservation HT2' Hwf' HOK' Hstep2) as P2. destruct P2 as [Σ'' d2 Hext2 Hwf'' HOK'' Hdisj2 HT2''].
  apply (Separate Σ' Σ'' (q1 ⋓ d1) (q2 ⋓ d2) Hext1 Hext2 HT1' HT2'').
  (* now we just need to show that the disjointness is preserved. this is intuitively true from the disjointness
     of the heap effects d1 and d2. *)
  erewrite <- @qqcap_fresh_r; eauto. erewrite <- qqcap_fresh_l; eauto.
  apply has_type_closed in HT1. intuition. eauto.
  apply has_type_closed in HT2. intuition. eauto.
  apply closed_qual_qqplus. apply has_type_closed in HT1. intuition.
  eapply closed_qual_monotone; eauto. eapply disjointq_closed; eauto.
  apply has_type_closed in HT2. intuition. eapply closed_qual_monotone; eauto.
  (* finally, the qualifiers are completely saturated, i.e., the results indeed have fully disjoint object graphs  *)
  all : apply senv_saturated_qqplus; eauto.
  apply has_type_senv_saturated in HT1; auto. eapply weaken_store_senv_saturated; eauto.
  eapply weaken_store_senv_saturated; eauto.
  apply has_type_senv_saturated in HT2; auto. eapply weaken_store_senv_saturated; eauto.
Qed.
