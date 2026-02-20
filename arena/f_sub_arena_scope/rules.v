(****************************************
*  The formal typing rules, stepping of our work
 ****************************************)

Require Export Arith.EqNat.
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
Require Import nats.
Require Import qualifiers.
Require Import boolean.
Require Import lang.
Require Import qenv.
Require Import ops.
Require Import lemmas.
Require Import killsep.

Import QualNotations.
Local Open Scope qualifiers.
Import OpeningNotations.
Local Open Scope opening.

Import SplicingNotations.
Local Open Scope splicing.
Import SubstitutionNotations.
Local Open Scope substitutions.


(* qstp actually needs to read the context, so we require the wf_tenv in main proofs:
    all elements inside tenv is separate from killed, even with the growth of kill
  However, as we only read one cell, we can directly require one cell to avoid passing wf_tenv everywhere
*)

(* qualifier subtyping *)
Inductive qstp : tenv -> senv -> qual -> qual -> Prop :=
| qs_sq : forall Γ Σ d1 d2,
    d1 ⊑↑ d2 ->
    closed_Qual 0 (‖Γ‖) (‖Σ‖) d2↑ ->
    qstp Γ Σ d1 d2

| qs_self : forall Γ Σ f df T1 d1 T2 d2,
    indexr f Γ = Some ((bind_tm, true, (TFun d1 d2 T1 T2), df)) ->
    closed_Qual 0 f (‖Σ‖) df↑ ->
    ♦∉ df ->
    qstp Γ Σ (df ⊔ $!f) $!f

| qs_self_all : forall Γ Σ f df T1 d1 T2 d2,
    indexr f Γ = Some ((bind_tm, true, (TAll d1 d2 T1 T2), df)) ->
    closed_Qual 0 f (‖Σ‖) df↑ ->
    ♦∉ df ->
    qstp Γ Σ (df ⊔ $!f) $!f

| qs_qvar : forall Γ Σ b U x q1,
    indexr x Γ = Some((bind_tm, b, U, q1)) ->
    closed_ty 0 x (‖Σ‖) U ->
    closed_Qual 0 x (‖Σ‖) q1↑ ->
    ♦∉ q1 ->
    qstp Γ Σ $!x q1

| qs_qvar_ty : forall Γ Σ b U x q1,
    indexr x Γ = Some((bind_ty, b, U, q1)) ->
    closed_ty 0 x (‖Σ‖) U ->
    closed_Qual 0 x (‖Σ‖) q1↑ ->
    ♦∉ q1 ->
    qstp Γ Σ $!x q1

| qs_cong : forall Γ Σ q d1 d2,
    qstp Γ Σ d1 d2 ->
    closed_Qual 0 (‖Γ‖) (‖Σ‖) q↑ ->
    qstp Γ Σ (q ⊔ d1) (q ⊔ d2)

| qs_trans : forall Γ Σ d1 d2 d3,
    qstp Γ Σ d1 d2 -> qstp Γ Σ d2 d3 -> qstp Γ Σ d1 d3
.
#[global] Hint Constructors qstp : core.


(* subtyping *)
Inductive stp : tenv -> senv -> ty -> qual -> ty -> qual -> Prop :=
| s_top : forall Γ Σ T d1 d2,
    closed_ty 0 (‖ Γ ‖) (‖ Σ ‖) T ->
    qstp Γ Σ d1 d2 ->
    stp Γ Σ T d1 TTop d2

| s_tvar_refl: forall Γ Σ x d1 d2 v,    (* ignore  q *)
    indexr x Γ = Some v ->              (* follows DOT *)
    qstp Γ Σ d1 d2 ->
    stp Γ Σ (TVar (varF x)) d1 (TVar (varF x)) d2

| s_tvar_trans: forall Γ Σ T1 T2 d0 d1 d2 x,  (* use  type var *)
    indexr x Γ = Some((bind_ty, false, T1, d0)) ->
    closed_ty  0 0 (‖ Σ ‖) T1 ->
    stp Γ Σ T1 d1 T2 d2 ->
    stp Γ Σ (TVar (varF x)) d1 T2 d2

| s_all: forall Γ Σ T1 T2 T3 T4 d1 d2 d3 d4 d5 d6,
    closed_ty 0 (‖ Γ ‖) (‖ Σ ‖) (TAll d1 d2 T1 T2) ->
    closed_ty 0 (‖ Γ ‖) (‖ Σ ‖) (TAll d3 d4 T3 T4) ->
    qstp Γ Σ d5 d6 ->
    stp Γ Σ T3 d3 T1 d1  ->
    stp ((bind_ty, false, T3, d3) :: (bind_tm, true, TAll d1 d2 T1 T2, {♦}) :: Γ) Σ (open_ty' Γ T2) (openq' Γ d2) (open_ty' Γ T4) (openq' Γ d4) ->
    stp Γ Σ (TAll d1 d2 T1 T2) d5 (TAll d3 d4 T3 T4) d6

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
    stp ((bind_tm, false, T3,d3) :: (bind_tm, true, TFun d1 d2 T1 T2, {♦}) :: Γ) Σ (open_ty' Γ T2) (openq' Γ d2) (open_ty' Γ T4) (openq' Γ d4) ->
    stp Γ Σ (TFun d1 d2 T1 T2) d5 (TFun d3 d4 T3 T4) d6

| s_trans : forall Γ Σ T1 T2 T3 d1 d2 d3,
    stp Γ Σ T1 d1 T2 d2 -> stp Γ Σ T2 d2 T3 d3 -> stp Γ Σ T1 d1 T3 d3
.
#[global] Hint Constructors stp : core.

(* deBruijn index v occurs nowhere in T *)
Definition not_free (v : id) (T : ty): Prop := [[ v ~> TUnit ~ ∅ ]]ᵀ T = T.

(* computes all local locations inside a term,
  if a twithr has not yet stepped to a twithc, then the location is not allocated
  which deal with stacked scope declaration
*)
Fixpoint local_locs (t: tm) : qual :=
  match t with
  | ttabs t  => local_locs t
  | ttapp t  => local_locs t
  | tabs  t  => local_locs t
  | tapp t1 t2  => (local_locs t1) ⊔ (local_locs t2)
  | tref  t  => local_locs t
  | trefat t1 t2 => (local_locs t1) ⊔ (local_locs t2)
  | tderef t  => local_locs t
  | tassign t1 t2  => (local_locs t1) ⊔ (local_locs t2)
  | twithr t1 t2  => (local_locs t1) ⊔ (local_locs t2)
  | twithc l t => &!l ⊔ (local_locs t)
  | _ => ∅
  end.


(* term typing *)
Inductive has_type : tenv -> qual -> senv -> tm -> ty -> qual -> Prop :=
| t_tabs: forall Γ φ Σ t T1 T2 df d1 d2,
    closed_tm 2 (‖Γ‖) (‖Σ‖) t ->
    closed_ty 0 (‖Γ‖) (‖Σ‖) (TAll d1 d2 T1 T2) ->
    closed_Qual 0 (‖Γ‖) (‖Σ‖) φ↑ ->
    d1 ⊑↑ df ⊔ {♦} ->
    df ⊑↑ φ ->
    ♦∉ df ->
    kill_sep (local_locs t) df ->
    has_type ((bind_ty, false, T1, d1)  :: (bind_tm, true, (TAll d1 d2 T1 T2), df) :: Γ)
             (df ⊔ ($!‖Γ‖) ⊔ $!(S (‖Γ‖))) Σ (t <~²ᵗ Γ) (T2 <~²ᵀ Γ) (d2 <~²ᵈ Γ) ->
    has_type Γ φ Σ (ttabs t) (TAll d1 d2 T1 T2) df

| t_tapp: forall Γ φ Σ t T1 T2 d1 d2 df,
    has_type Γ φ Σ t (TAll d1 d2 T1 T2) df ->
    closed_ty 0 (‖Γ‖) (‖Σ‖) T1 ->
    closed_Qual 0 (‖Γ‖) (‖Σ‖) d1↑ ->
    (d2 <~ᵈ ∅ ; ∅) ⊑↑ (φ ⊔ {♦}) ->
    ♦∉ d1 ->
    d1 ⊑↑ φ ->
    not_free 0 T2 ->
    kill_sep (local_locs t) d1 ->
    kill_sep (local_locs t) (d2) ->
    has_type Γ φ Σ (ttapp t) (T2 <~ᵀ TUnit ~ ∅ ; T1 ~ d1) (d2 <~ᵈ df ; d1)

| t_tapp_fresh : forall Γ φ Σ t d1 d2 df T1 T2,
    has_type Γ φ Σ t (TAll (q_trans_tenv Γ df ⋒ q_trans_tenv Γ d1) d2 T1 T2) df ->
    closed_ty 0 (‖Γ‖) (‖Σ‖) T1 ->
    closed_Qual 0 (‖Γ‖) (‖Σ‖) d1↑ ->
    d1 ⊑↑ (φ ⊔ {♦}) ->
    (♦∈ d1 -> not_free 1 T2) ->
    not_free 0 T2 ->
    (d2 <~ᵈ ∅ ; ∅) ⊑↑ (φ ⊔ {♦}) ->
    (q_trans_tenv Γ d1) ⋒ (q_trans_tenv Γ df) ⊑↑ (φ ⊔ {♦}) ->
    kill_sep (local_locs t) d1 ->
    kill_sep (local_locs t) (d2) ->
    kill_sep (local_locs t) ((q_trans_tenv Γ d1) ⋒ (q_trans_tenv Γ df)) ->
    has_type Γ φ Σ (ttapp t) (T2 <~ᵀ TUnit ~ ∅ ; T1 ~ d1) (d2 <~ᵈ df ; d1)

| t_base : forall Γ Σ φ,
    closed_Qual 0 (‖Γ‖) (‖Σ‖) φ↑ ->
    has_type Γ φ Σ tunit TUnit ∅

| t_var : forall Γ φ Σ x b T d,
    indexr x Γ = Some ((bind_tm, b,T,d)) ->
    $!x ⊑↑ φ ->
    closed_Qual 0 (‖Γ‖) (‖Σ‖) φ↑ ->
    closed_ty   0 x (‖Σ‖) T ->
    closed_Qual 0 x (‖Σ‖) d↑ ->
    has_type Γ φ Σ $x T $!x

| t_abs: forall Γ φ Σ T1 d1 T2 d2 df t,
    closed_tm   2 (‖Γ‖) (‖Σ‖) t ->
    closed_ty   0 (‖Γ‖) (‖Σ‖) (TFun d1 d2 T1 T2) ->
    closed_Qual 0 (‖Γ‖) (‖Σ‖) φ↑ ->
    d1 ⊑↑ df ⊔ {♦} ->
    df ⊑↑ φ ->
    ♦∉ df ->
    kill_sep (local_locs t) df ->
    has_type ((bind_tm, false, T1, d1) :: (bind_tm, true, (TFun d1 d2 T1 T2), df) :: Γ)
             (df ⊔ ($!‖Γ‖) ⊔ $!(S (‖Γ‖))) Σ (t <~²ᵗ Γ) (T2 <~²ᵀ Γ) (d2 <~²ᵈ Γ) ->
    has_type Γ φ Σ (tabs t) (TFun d1 d2 T1 T2) df

| t_app : forall Γ φ φd Σ t1 d1 t2 d2 df T1 T2,
    has_type Γ φ Σ t1 (TFun d1 d2 T1 T2) df ->
    has_type Γ φd Σ t2 T1 d1 ->
    (d2 <~ᵈ ∅ ; ∅) ⊑↑ (φ ⊔ {♦}) ->
    ♦∉ d1 ->
    not_free 0 T2 ->
    (qdiff φ (local_locs t1)) = φd ->
    kill_sep (local_locs t2) (df) ->
    kill_sep (local_locs t1 ⊔ local_locs t2) (d2) ->
    has_type Γ φ Σ (tapp t1 t2) (T2 <~ᵀ TUnit ~ ∅ ; T1 ~ d1) (d2 <~ᵈ df ; d1)

| t_app_fresh : forall Γ φ φd Σ t1 d1 t2 d2 df T1 T2,
    has_type Γ φ Σ t1 (TFun (q_trans_tenv Γ df ⋒ q_trans_tenv Γ d1) d2 T1 T2) df ->
    has_type Γ φd Σ t2 T1 d1 ->
    (♦∈ d1 -> not_free 1 T2) ->
    not_free 0 T2 ->
    (d2 <~ᵈ ∅ ; ∅) ⊑↑ (φ ⊔ {♦}) ->
    (q_trans_tenv Γ d1) ⋒ (q_trans_tenv Γ df) ⊑↑ (φ ⊔ {♦}) ->
    (qdiff φ (local_locs t1)) = φd ->
    kill_sep (local_locs t2) (df) ->
    kill_sep (local_locs t1 ⊔ local_locs t2) (d2) ->
    kill_sep (local_locs t1) ((q_trans_tenv Γ d1) ⋒ (q_trans_tenv Γ df)) ->
    has_type Γ φ Σ (tapp t1 t2) (T2 <~ᵀ TUnit ~ ∅ ; T1 ~ d1) (d2 <~ᵈ df ; d1)

| t_loc : forall Γ φ Σ l o T q,
    closed_Qual 0 (‖Γ‖) (‖Σ‖) φ↑ ->
    sindexr l o Σ = Some (T,q) ->
    closed_ty 0 0 (‖Σ‖) T ->
    closed_Qual 0 0 (‖Σ‖) q↑ ->
    &!l ⊑↑ φ ->
    ♦∉ q ->
    (* location is not killed, guaranteed by φ *)
    has_type Γ φ Σ &(l,o) (TRef q T) (&!l)

| t_ref: forall Γ φ Σ T t d1,
    has_type Γ φ Σ t T d1 ->
    closed_ty 0 (‖Γ‖) (‖Σ‖) T ->
    ♦∉ d1 ->
    has_type Γ φ Σ (tref t) (TRef d1 T) ({♦})

| t_refat : forall Γ φ φd Σ t1 t2 T d T1 d1 d2,
    has_type Γ φd Σ t1 T d ->
    ♦∉ d ->
    has_type Γ φ Σ (t2) (TRef d1 T1) (d2) ->
    (qdiff φ (local_locs t2)) = φd ->
    kill_sep (local_locs t1) (d2) ->
    has_type Γ φ Σ (trefat t1 t2) (TRef (d) T) (d2)

| t_deref: forall Γ φ Σ T d d1 t,
    has_type Γ φ Σ t (TRef d1 T) d ->
    ♦∉ d1 ->
    d1 ⊑↑ φ ->
    (* why pose kill_sep here:
      the minimum requirement: cannot deref direct refs of future kill, i.e. the new Ref(l) cases for the scope exit
      because the statics requires T,d closed, but the dynamics only require d, we need to exclude some extra and not possible patterns after stepping.
      as d1 is inside TRef, it cannot either grow by substitution (closed) nor step (no-fresh), so it remains the requirement
    *)
    kill_sep (local_locs t) d1 ->
    has_type Γ φ Σ !t T d1

| t_assign: forall Γ φ φd Σ T t1 d d1 t2,
    has_type Γ φ Σ t1 (TRef d1 T) d ->
    has_type Γ φd Σ t2 T d1 ->
    ♦∉ d1 ->
    (qdiff φ (local_locs t1)) = φd ->
    kill_sep (local_locs t2) (d) ->
    has_type Γ φ Σ (tassign t1 t2) TUnit ∅

| t_sub: forall Γ φ Σ e T1 d1 T2 d2,
    has_type Γ φ Σ e T1 d1 ->
    stp Γ Σ T1 d1 T2 d2 ->
    d2 ⊑↑ (φ ⊔ {♦}) ->
    kill_sep (local_locs e) d2 ->
    has_type Γ φ Σ e T2 d2

| t_withr : forall Γ φ φd Σ t1 t2 T1 d1 T2 d2,
    has_type Γ φ Σ t1 T1 d1 ->
    ♦∉ d1 -> (* content of ref cannot include fresh *)
    (* push a new ref into the context, and a fake self, so adding only Ref(x) to varphi
      This follows the convention of our calculus
    *)
    closed_ty 0 (‖Γ‖) (‖Σ‖) T2 ->   (* alternative of not_free 0 1*)
    closed_Qual 0 (‖Γ‖) (‖Σ‖) d2↑ ->  (*alternative of not_free 0 1*)
    closed_tm 2 (‖Γ‖) (‖Σ‖) t2 ->
    has_type ((bind_tm, false, TRef d1 T1, {♦}) :: (bind_tm, true, TUnit, {♦}) :: Γ)
      (φd ⊔ $!(S (‖Γ‖))) Σ (t2 <~²ᵗ Γ) (T2) (d2) ->
    φd ⊑↑ φ -> (* this is fine here. because we don't have right congruence *)
    kill_sep (local_locs t1) φd ->
    has_type Γ φ Σ (twithr t1 t2) T2 d2


| t_withc : forall Γ φ Σ l t T d,
    l < ‖Σ‖ -> (* can be simply inferred by the filter, but put here for simplicity *)
    has_type Γ (φ) Σ t T d ->   (* after step, we should pick φ+l as new filter *)
    closed_ty 0 0 (‖Σ‖) T -> (* as it is purely dynamic term *)
    closed_Qual 0 0 (‖Σ‖) d↑ ->
    kill_sep &!l d ->
    has_type Γ φ Σ (twithc l t) T d
.
#[global] Hint Constructors has_type : core.


Inductive value : tm -> Prop :=
| value_ttabs: forall t, value (ttabs t)
| value_abs : forall t, value (tabs t)
| value_cst : value tunit
| value_loc : forall l o, value &(l, o)
.
#[global] Hint Constructors value : core.

Definition store := list (option (list (tm))).

Inductive step : tm -> store -> tm -> store -> Prop :=
(*contraction rules*)
| step_ttapp: forall t σ,
  step (ttapp (ttabs t)) σ (t <~ᵗ (ttabs t); tunit) σ
| step_beta : forall t v σ,
    value v ->
    step (tapp (tabs t) v) σ (t <~ᵗ (tabs t); v) σ
| step_ref : forall v σ,
    value v ->
    step (tref v) σ (&‖σ‖) ((Some [v]) :: σ)
| step_refat: forall v l o s σ,
    value v ->
    indexr l σ = Some (Some s) ->
      (* it must be zero *)
    step (trefat v &(l, o)) σ &(l, ‖s‖) (cinsert σ l (v))
| step_deref : forall σ l o s v,
    indexr l σ = Some (Some s) ->
    indexr o s = Some (v) ->
    step (! &(l, o)) σ v σ
| step_assign : forall σ l o v s,
    l < ‖σ‖ ->
    indexr l σ = Some (Some s) ->
    o < ‖s‖ -> (* check existance *)
    value v ->
    step (tassign &(l, o) v) σ tunit (supdate σ l o v)
| step_twithr : forall σ v t,
    value v ->
    step (twithr v t) σ (twithc (‖σ‖) (t <~ᵗ tunit; (&‖σ‖))) ((Some [v]) :: σ)
| step_twithc : forall σ v l,
    value v ->
    step (twithc l v) σ v (update σ l None)
(*congruence rules*)
| step_c_tapp: forall t t' σ σ',
  step t σ t' σ' ->
  step (ttapp t)  σ (ttapp t') σ'
| step_c_ref : forall t t' σ σ',
    step t σ t' σ' ->
    step (tref t) σ (tref t') σ'
| step_c_refat_l : forall t1 t1' t2 σ σ',
    value t2 ->
    step t1 σ t1' σ' ->
    step (trefat t1 t2) σ (trefat t1' t2) σ'
| step_c_refat_r : forall t1 t2 t2' σ σ',
    step t2 σ t2' σ' ->
    step (trefat t1 t2) σ (trefat t1 t2') σ'
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
| step_c_twithr_l : forall t1 t2 t1' σ σ',
  step t1 σ t1' σ' ->
  step (twithr t1 t2) σ (twithr t1' t2) σ'
| step_c_twithc : forall l t t' σ σ',
  step t σ t' σ' ->
  step (twithc l t) σ (twithc l t') σ'
.


(* deterministic relations (used to recover standard progress & preservation from the type safety theorem. ) *)
Definition relation (X : Type)(Y: Type) := X -> Y -> X ->  Y -> Prop.
Definition deterministic {X : Type}{Y: Type} (R : relation X Y) :=
  forall (x x1 x2 : X) (y y1 y2: Y), R x y x1 y1 -> R x y x2 y2 -> x1 = x2 /\ y1 = y2.

(* Supporting lemmas for basic definitions *)

Local Open Scope splicing.
Local Open Scope substitutions.

(* Indicates the relation between an assumption's qualifier and the qualifier we substitute for the variable.
   This helps ensure that the substitution lemma can be expressed uniformly on a single variable. *)
Inductive Substq : tenv -> senv -> qual -> qual -> Prop :=
| SExact : forall Γ Σ df,    ♦∉ df -> Substq Γ Σ df df        (* precise substitution, e.g., we substitute a recursive function into itself or the argument in t_app *)
| SGrow  : forall Γ Σ df dx,
    ♦∉ dx ->
    closed_Qual 0 (‖ Γ ‖) (‖ Σ ‖) df ↑ ->
    Substq Γ Σ (q_trans_tenv Γ df ⋒ q_trans_tenv Γ dx) dx (* a growing substitution, e.g., we substitute the argument in t_app_fresh, note the difference. *)
.
#[global] Hint Constructors Substq : core.

Lemma Substq_non_fresh : forall {Γ Σ dx dx'}, Substq Γ Σ dx dx' -> ♦∉ dx'.
  intros. inversion H; auto.
Qed.
#[global] Hint Resolve Substq_non_fresh : core.


(* Basics for qualifier subtyping and subtyping *)

Lemma qstp_closed : forall {Γ Σ d1 d2}, qstp Γ Σ d1 d2 -> closed_Qual 0 (‖Γ‖) (‖Σ‖) d1↑ /\ closed_Qual 0 (‖Γ‖) (‖Σ‖) d2↑.
  intros Γ Σ d1 d2 HSQ. induction HSQ; intuition.
  - eapply closed_Qual_sub; eauto.
  - apply indexr_var_some' in H. apply closed_qual_qor. eapply closed_qual_monotone; eauto. lia. apply just_fv_closed. auto.
  - apply indexr_var_some' in H. apply just_fv_closed. auto.
  - apply indexr_var_some' in H. apply closed_qual_qor. eapply closed_qual_monotone; eauto. lia. apply just_fv_closed.  auto.
  - apply indexr_var_some' in H. apply just_fv_closed. auto.
  - apply indexr_var_some' in H. apply just_fv_closed. auto.
  - apply indexr_var_some' in H. eapply closed_qual_monotone; eauto. lia.
  - apply indexr_var_some' in H. apply just_fv_closed. auto.
  - apply indexr_var_some' in H. eapply closed_qual_monotone; eauto. lia.
  - apply closed_qual_qor; auto.
  - apply closed_qual_qor; auto.
Qed.

Lemma qstp_refl : forall {d}, forall {Γ Σ }, closed_qual 0 (‖Γ‖) (‖Σ‖) d -> qstp Γ Σ d d.
  intros d Γ Σ Hc. constructor; auto.
Qed.

Lemma stp_closed : forall {Γ Σ T1 d1 T2 d2},
    stp Γ Σ T1 d1 T2 d2 ->
    closed_ty 0 (‖Γ‖) (‖Σ‖) T1
    /\ closed_qual 0 (‖Γ‖) (‖Σ‖) d1
    /\ closed_ty 0 (‖Γ‖) (‖Σ‖) T2
    /\ closed_qual 0 (‖Γ‖) (‖Σ‖) d2.
Proof.  intros Γ Σ T1 d1 T2 d2 HS. induction HS.
  - intuition. all: apply qstp_closed in H0; intuition.
  - intuition. 1,3: constructor; apply indexr_var_some' in H; auto. 1,2: apply qstp_closed in H0; intuition; auto.
  - intuition. apply indexr_var_some' in H; auto.
  - apply qstp_closed in H1; intuition; auto.
  - intuition. all: apply qstp_closed in H; intuition.
  - intuition. all: apply qstp_closed in H; apply qstp_closed in H1; intuition.
  - intuition. apply qstp_closed in H1; intuition. apply qstp_closed in H1; intuition.
  - intuition.
Qed.

Lemma stp_refl' : forall {n T}, ty_size T < n -> forall {Γ Σ}, closed_ty 0 (‖Γ‖) (‖Σ‖) T -> forall {d d'}, qstp Γ Σ d d' -> stp Γ Σ T d T d'.
  induction n; try lia; destruct T; simpl; intros Hsize Γ Σ Hc d d' Hstp; inversion Hc; subst.
  - (* TTOP *) constructor; auto.
  - (* TVarF refl *) apply indexr_var_some in H3. destruct H3. econstructor; eauto.
  - (* TVarB  *) inversion H3.
  - (* TAll *) inversion Hc. subst. apply s_all. auto. auto. auto.
    eapply IHn. lia. auto. auto.
    eapply IHn. unfold open_ty'. unfold open_ty. rewrite <- open_ty_preserves_size. rewrite <- open_ty_preserves_size. lia.
    auto. unfold open_ty'. unfold open_ty. rewrite open_rec_ty_commute; auto.
    eapply closed_ty_open' with (x:=S (S (‖Γ‖))); eauto.
    eapply closed_ty_open' with (x:=S (S (‖Γ‖))); eauto.
    eapply closed_ty_monotone; eauto. apply just_fv_closed. lia.
    rewrite <- just_fv_closed. lia.
    apply qstp_refl. unfold openq'. unfold openq. rewrite open_qual_commute; auto.
    simpl. eapply closed_qual_open'; eauto. eapply closed_qual_open'; eauto. 1-3: apply Q_lift_closed; Qcrush.
  - (*TUnit*) constructor. auto.
  - (*TFun*) constructor; auto. apply IHn. lia. auto. auto.
    apply IHn. unfold open_ty'. unfold open_ty. rewrite <- open_ty_preserves_size. rewrite <- open_ty_preserves_size. simpl. lia. auto. simpl. unfold open_ty'. unfold open_ty. rewrite open_rec_ty_commute; auto.
    eapply closed_ty_open' with (x:=S (S (‖Γ‖))); eauto.
    eapply closed_ty_open' with (x:=S (S (‖Γ‖))); eauto.
    eapply closed_ty_monotone; eauto.
    rewrite <- just_fv_closed. lia.
    rewrite <- just_fv_closed. lia.
    apply qstp_refl. unfold openq'. unfold openq. rewrite open_qual_commute; auto.
    simpl. eapply closed_qual_open'; eauto. eapply closed_qual_open'; eauto. 1-3: apply Q_lift_closed; Qcrush.
  - (*TRef*) constructor; auto.
    1-2 : apply IHn; try lia; auto.
Qed.

Lemma stp_refl : forall {T Γ Σ}, closed_ty 0 (‖Γ‖) (‖Σ‖) T -> forall {d d'}, qstp Γ Σ d d' -> stp Γ Σ T d T d'.
  intros. eapply stp_refl'; eauto.
Qed.


Lemma qstp_non_fresh : forall {Γ Σ q1 q2}, qstp Γ Σ q1 q2 -> ♦∉ q2 -> ♦∉ q1.
  intros. induction H; Qcrush.
Qed.

Lemma stp_qstp_inv : forall {Γ Σ T1 d1 T2 d2}, stp Γ Σ T1 d1 T2 d2 -> qstp Γ Σ d1 d2.
  intros Γ Σ T1 d1 T2 d2 HS. induction HS; intuition.
  eapply qs_trans; eauto.
Qed.

Lemma s_trans' : forall {Γ Σ T1 d1 T2 d2 T3}, stp Γ Σ T1 d1 T2 d2 -> stp Γ Σ T2 d2 T3 d2 -> stp Γ Σ T1 d1 T3 d2.
Proof.
  intros. eapply s_trans; eauto.
Qed.

Lemma stp_qual_irrelevance: forall {Γ Σ T1 d1 T2 d2}, stp Γ Σ T1 d1 T2 d2 ->
      forall {d3 d4}, qstp Γ Σ d3 d4 -> stp Γ Σ T1 d3 T2 d4.
Proof.
  intros Γ Σ T1 d1 T2 d2 Hstp. induction Hstp; intros; try econstructor; eauto.
  assert (qstp Γ Σ d4 d4). { apply qs_sq; auto. apply qstp_closed in H. intuition. }
  specialize(IHHstp2 d4 d4). apply IHHstp2 in H0 as IHHstp2'.
  eapply s_trans'. eapply IHHstp2'. eapply stp_refl; eauto. eapply stp_closed in Hstp2. intuition.
Qed.


(* =========== dynamic store ============ *)

Definition tph := tunit.    (* term placeholder *)
Definition root' (c : option (list tm)) : (option tm) :=
  match c with
  | None => None
  | Some (s) => match indexr 0 s with
                | None => Some tph
                | Some x => Some x
                end
  end.
Definition squish' (σ : store) : list (option tm) := map (root') σ.
Definition indexr' {X : Type} (n : nat) (l : option (list X)) : option X :=
  match l with
    | None => None
    | Some c => indexr n c
  end.
Fixpoint sindexr' {X : Type} (l : loc) (o : offset) (σ : list (option (list X))) : option X :=
  match σ with
    | [] => None
    | a :: σ' =>
      if (Nat.eqb l (length σ')) then indexr' o a else sindexr' l o σ'
  end.

(* ========= indexr', update' ========= *)

Lemma squish'_length : forall s,
  ‖ squish' s ‖ = ‖s‖.
Proof. induction s; simpl; auto.
Qed.

Lemma sindexr'_skip : forall {A} {c : option (list A)} {xs} {i} {o}, i <> length xs -> sindexr' i o (c :: xs) = sindexr' i o xs.
Proof.
  intros.
  rewrite <- PeanoNat.Nat.eqb_neq in H. auto.
  simpl. rewrite H. reflexivity.
Qed.

Lemma sindexr'_skips : forall {A} {xs' xs : list (option (list A))} {i} {o}, i < length xs -> sindexr' i o (xs' ++ xs) = sindexr' i o xs.
  induction xs'; intros; intuition.
  replace ((a :: xs') ++ xs) with (a :: (xs' ++ xs)).
  rewrite sindexr'_skip. eauto. rewrite app_length. lia. auto.
Qed.

Lemma sindexr'_head : forall {X} s (c : option (list X)) o, sindexr' (length s) o (c :: s) = indexr' o c.
  simpl. intros. rewrite Nat.eqb_refl; auto.
Qed.

Lemma update'_indexr'_hit : forall {s : option (list tm)} {x v t},indexr' x (update' s x v) = Some t ->
  t = v.
Proof.
  destruct s. 2: { intros; simpl in H; discriminate H. } induction l; intros; simpl. simpl in H; discriminate H.
  unfold update' in H; simpl in H. bdestruct (x =? ‖l‖); subst. rewrite indexr_head in H; inversion H; auto. rewrite indexr_skip in H.
  destruct (le_lt_dec x (‖l‖) ). rewrite update_indexr_hit in H; auto. inversion H; auto. lia. rewrite indexr_outrange in H. discriminate H. rewrite <- update_length. lia. rewrite <- update_length; auto.
Qed.


Lemma supdate_sindexr'_hit : forall {σ : store} {l o v t},
  sindexr' l o (supdate σ l o v) = Some t ->
  t = v.
Proof.
  induction σ; intros; simpl in *; auto. discriminate H.
  bdestruct (l =? ‖ σ ‖).
    subst. rewrite sindexr'_head in H. apply update'_indexr'_hit in H; auto.
    rewrite sindexr'_skip in H. eapply IHσ; eauto. rewrite <- supdate_length. auto.
Qed.

Lemma update'_indexr'_miss : forall (s : option (list tm)) x x' v,
  x <> x' ->
  indexr' x (update' s x' v) = indexr' x s.
Proof.
  destruct s. 2:{ intros; simpl; auto. }
  induction l; intros; simpl; auto.
  bdestruct (x' =? ‖ l ‖); bdestruct (x =? ‖ l ‖); try lia.
  rewrite indexr_skip; auto. subst. erewrite update_length. rewrite indexr_head; auto. rewrite indexr_skip. rewrite update_indexr_miss; auto. rewrite <- update_length; auto.
Qed.


Lemma supdate_sindexr'_miss : forall {σ : store} {l o l' o' v},
  l <> l' \/ o <> o' ->
  sindexr' l o (supdate σ l' o' v) = sindexr' l o σ.
Proof.
  induction σ; intros; simpl; auto. destruct H.
  - bdestruct (l' =? ‖ σ ‖); bdestruct (l =? ‖ σ ‖); try lia.
    + rewrite sindexr'_skip; auto.
    + subst. replace (‖ σ ‖) with (‖ supdate σ l' o' v ‖).  erewrite sindexr'_head; auto. rewrite <- supdate_length; eauto.
    + rewrite sindexr'_skip; auto. rewrite <- supdate_length; auto.
  - bdestruct (l' =? ‖ σ ‖); bdestruct (l =? ‖ σ ‖); try lia.
    + subst. rewrite sindexr'_head. rewrite update'_indexr'_miss; auto.
    + rewrite sindexr'_skip; auto.
    + subst. erewrite supdate_length. rewrite sindexr'_head; auto.
    + subst. rewrite sindexr'_skip. eapply IHσ; eauto. rewrite <- supdate_length; auto.
Qed.

Lemma sindexr'_indexr_rewrite : forall {σ : store } {l o c}, indexr l σ = Some (Some c) -> sindexr' l o σ = indexr o c.
Proof.
  induction σ; intros; subst. inversion H.
  bdestruct (l =? ‖σ‖); subst. rewrite indexr_head in H. inversion H; subst. rewrite sindexr'_head; auto.
  rewrite sindexr'_skip; auto. rewrite indexr_skip in H; auto.
Qed.

Lemma supdate_indexr_miss_l : forall {A} {σ : list (option (list A))} {l o v l0 c}, l <> l0 ->
  indexr l (supdate σ l0 o v) = Some c -> indexr l σ = Some c.
Proof.
  induction σ; simpl; intuition.
  destruct (Nat.eqb l (length σ)) eqn:Hls.
  apply Nat.eqb_eq in Hls. bdestruct (l0 =? ‖ σ ‖); try lia. subst. erewrite supdate_length in H0. rewrite indexr_head in H0; auto.
  simpl. apply Nat.eqb_neq in Hls. bdestruct (l0 =? ‖ σ ‖); try lia; subst. rewrite indexr_skip in H0; auto. rewrite indexr_skip in H0; auto. eapply IHσ. 2: eauto. lia. rewrite <- supdate_length. lia.
Qed.

Lemma qdom'_squish : forall {σ : store},
  qdom' (squish' σ) = qdom' σ.
Proof.
  induction σ; simpl; auto. unfold qdom' in *. f_equal. inversion IHσ. unfold n_dom'; simpl.
  rewrite squish'_length; simpl. apply FunctionalExtensionality.functional_extensionality; intros. f_equal. bdestruct (x =? ‖σ‖); subst; simpl.
    + unfold root'. induction a; simpl; auto. destruct (indexr 0 a); simpl; auto.
    + inversion IHσ; unfold n_dom' in H2. apply FunctionalExtensionality.equal_f with (x := x) in H2. rewrite squish'_length in H2.
      bdestruct (x <? ‖ σ ‖). inversion H2; auto. rewrite indexr_miss. rewrite indexr_miss; auto. 2: rewrite squish'_length. 1-2: lia.
Qed.

Lemma qdom'_sub_qdom_squish : forall σ Σ,
  qdom' (squish' σ) ⊑↑ qdom (squish Σ) -> qdom' σ ⊑↑ qdom Σ.
Proof.
  intros. rewrite qdom'_squish in H. rewrite <- qdom_squish in H; auto.
Qed.
#[global] Hint Resolve qdom'_sub_qdom_squish : core.




(* Lemmas for measurements of local locs *)

Lemma local_locs_open : forall t t' k,
  local_locs ([[ k ~> t']]ᵗ t) ⊑↑ local_locs t' ⊔ local_locs t.
Proof.
  induction t; intros; simpl; auto.
  destruct v; simpl; auto. bdestruct (k=?i); simpl; auto.
  apply Qor_bound. eapply Subq_trans; eauto. eapply Subq_trans; eauto.
  apply Qor_bound. eapply Subq_trans; eauto. eapply Subq_trans; eauto.
  apply Qor_bound. eapply Subq_trans; eauto. eapply Subq_trans; eauto.
  apply Qor_bound. eapply Subq_trans; eauto. eapply Subq_trans; eauto.
  apply Qor_bound. Qcrush. eapply Subq_trans; eauto.
Qed.

Lemma local_locs_open' : forall t t' k,
  local_locs t' = ∅ ->
  local_locs ([[ k ~> t']]ᵗ t) = local_locs t.
Proof.
  induction t; intros; simpl; auto.
  destruct v; simpl; auto. bdestruct (k=?i); simpl; auto.
  rewrite IHt1; auto. rewrite IHt2; auto.
  rewrite IHt1; auto. rewrite IHt2; auto.
  rewrite IHt1; auto. rewrite IHt2; auto.
  rewrite IHt1; auto. rewrite IHt2; auto.
  rewrite IHt; auto.
Qed.

Lemma local_locs_closed : forall t b f l,
  closed_tm b f l t ->
  closed_Qual 0 0 l (local_locs t)↑.
Proof.
  induction t; intros; inversion H; subst; simpl; eauto.
  eapply closed_Qual_qor; eauto.
  eapply closed_Qual_qor; eauto.
  eapply closed_Qual_qor; eauto.
  eapply closed_Qual_qor; eauto.
  eapply closed_Qual_qor; eauto. Qcrush.
Qed.

Lemma local_locs_subst : forall t t' k,
  local_locs ({ k |-> t' }ᵗ t) ⊑↑ local_locs t ⊔ local_locs t'.
Proof.
  induction t; intros; simpl; auto.
  destruct v; simpl; auto. bdestruct (i =? k); simpl; auto.
  apply Qor_bound. eapply Subq_trans; eauto. eapply Subq_trans; eauto.
  apply Qor_bound. eapply Subq_trans; eauto. eapply Subq_trans; eauto.
  apply Qor_bound. eapply Subq_trans; eauto. eapply Subq_trans; eauto.
  apply Qor_bound. eapply Subq_trans; eauto. eapply Subq_trans; eauto.
  rewrite <- qor_assoc. specialize (IHt t' k). Qcrush.
Qed.

Lemma local_locs_subst' : forall t t' k,
  local_locs t' = ∅ ->
  local_locs ({ k |-> t' }ᵗ t) = local_locs t.
Proof.
  induction t; intros; simpl; auto.
  destruct v; simpl; auto. bdestruct (i =? k); simpl; auto.
  rewrite IHt1; auto. rewrite IHt2; auto.
  rewrite IHt1; auto. rewrite IHt2; auto.
  rewrite IHt1; auto. rewrite IHt2; auto.
  rewrite IHt1; auto. rewrite IHt2; auto.
  rewrite IHt; auto.
Qed.

Lemma subst_qual_locs_bound : forall d dx k,
  (N_sub (N_lift (qlocs ({k |-> dx }ᵈ d))) (N_lift (qlocs (d ⊔ dx)))).
Proof.
  intros. qual_destruct d. qual_destruct dx. unfold_q. destruct (fvs k); simpl. apply N_lift_sub. Qcrush. simpl. Qcrush.
Qed.

Lemma local_locs_substitution : forall t tx d dx b f l,
  local_locs tx = ∅ ->
  closed_tm b f l t ->
  kill_sep (local_locs t) dx ->
  kill_sep (local_locs t) d ->
  kill_sep (local_locs ({0 |-> tx}ᵗ t)) ({0 |-> dx}ᵈ d).
Proof.
  intros. rewrite local_locs_subst'; auto. rewrite kill_sep_only_locs. 2: eapply local_locs_closed; eauto. eapply kill_sep_sub with (q:= (false, n_empty, n_empty, qlocs (d ⊔ dx))).
  specialize (subst_qual_locs_bound d dx 0); intros. Qcrush.
  rewrite <- kill_sep_only_locs. 2: eapply local_locs_closed; eauto. apply kill_sep_qor; auto.
Qed.


Lemma local_locs_splice : forall t k,
  local_locs t = local_locs (t ↑ᵗ k).
Proof.
  intros. induction t; simpl; auto.
  destruct v; simpl; auto. destruct (le_lt_dec k i); auto.
  f_equal; auto. f_equal; auto. f_equal; auto. f_equal; auto. f_equal; auto.
Qed.

Lemma kill_sep_local_locs_splice : forall t q k b f l,
  closed_tm b f l t ->
  kill_sep (local_locs t) q -> kill_sep (local_locs (t ↑ᵗ k)) (q ↑ᵈ k).
Proof.
  intros. rewrite <- local_locs_splice. rewrite kill_sep_only_locs.
  qual_destruct q. unfold_q. rewrite kill_sep_only_locs in H0. auto.
  1-2: eapply local_locs_closed; eauto.
Qed.


Lemma qdiff_local_loc_prop : forall φ φd dif,
  (qdiff φ dif) = φd ->
  kill_sep dif φd /\ φd ⊑↑ φ.
Proof.
  intros. subst. qual_destruct φ; qual_destruct dif. split.
  unfold kill_sep. Qcrush. Qcrush.
Qed.

Lemma qdiff_empty : forall d,
  qdiff d ∅ = d.
Proof.
  intros. qual_destruct d. apply Q_lift_eq. Qcrush.
Qed.

Lemma qdiff_subqual_monotone : forall d1 d2 dif,
  d1 ⊑↑ d2 ->
  qdiff d1 dif ⊑↑ qdiff d2 dif.
Proof.
  intros. qual_destruct d1; qual_destruct d2; qual_destruct dif. Qcrush.
Qed.



Lemma qdiff_splice_dist : forall d1 d2 k,
  (qdiff d1 d2) ↑ᵈ k = qdiff (d1 ↑ᵈ k) (d2 ↑ᵈ k).
Proof.
  intros. qual_destruct d1; qual_destruct d2. apply Q_lift_eq. unfold_q. simpl. Qcrush.
  bdestruct (x=?k). auto. bdestruct (x<?k). specialize (H H6). specialize (H1 H6). Qcrush.
  assert (x > k). lia. specialize (H2 H7). specialize (H5 H7). Qcrush.
Qed.


Lemma qdiff_subst1_dist : forall d1 d2 q l,
  closed_Qual 0 0 l d2↑ -> q ⊓ d2 = ∅ ->
  { 0 |-> q }ᵈ (qdiff d1 d2) = qdiff ({ 0 |-> q }ᵈ d1) ({ 0 |-> q }ᵈ d2).
Proof.
  intros. qual_destruct d1; qual_destruct d2. assert (fvs0 = n_empty). { clear - H. apply N_lift_eq. Qcrush. specialize (H0 x H1). lia. } assert (bvs0 = n_empty). { clear - H.  apply N_lift_eq. Qcrush. specialize (H x H1). lia. } subst.
  assert (qdiff (fr, fvs, bvs, lcs) (fr0, n_empty, n_empty, lcs0) = ((andb fr (negb fr0)), fvs, bvs, n_diff lcs lcs0)). apply Q_lift_eq. Qcrush. rewrite H1. clear H1.
  replace (({0 |-> q }ᵈ (fr0, n_empty, n_empty, lcs0))) with (fr0, n_empty, n_empty, lcs0). 2: { apply Q_lift_eq. Qcrush. }
  apply Q_lift_eq' in H0.
  unfold subst_qual; simpl. unfold qfvs, qbvs, qlocs; simpl. destruct (fvs 0) eqn:Efvs. apply Q_lift_eq. qual_destruct q; unfold_q; simpl.  Qcrush.
    inversion H0; auto.
    assert ((fun x : nat => N_lift lcs1 x /\ N_lift lcs0 x) = (fun _ : nat => False) ). inversion H0; auto. cut ((fun x : nat => N_lift lcs1 x /\ N_lift lcs0 x) x = (fun _ : nat => False) x). intros. simpl in H6. rewrite <- H6. auto. rewrite H5. auto.
  apply Q_lift_eq. qual_destruct q; unfold_q; simpl.  Qcrush.
Qed.

Lemma local_locs_non_fresh : forall t,
  ♦∉ (local_locs t).
Proof.
  intros. induction t; simpl; auto. Qcrush. Qcrush. Qcrush. Qcrush.
Qed.

Lemma local_locs_kill_sep_empty : forall t d,
  kill_sep (local_locs t) d ->
  d ⊓ (local_locs t) = ∅.
Proof.
  intros. unfold kill_sep in H. specialize (local_locs_non_fresh t); intros. apply Q_lift_eq. Qcrush.
  apply (H x); auto. apply (H2 x); auto. apply (H4 x); auto.
Qed.


Lemma qdiff_substitution : forall dx q t b f l,
  kill_sep (local_locs t) dx ->
  closed_tm b f l t ->
  qdiff ({0 |-> dx }ᵈ q) (local_locs (t)) = {0 |-> dx }ᵈ (qdiff q (local_locs t)).
Proof.
  intros. erewrite qdiff_subst1_dist. f_equal. erewrite subst1_qual_id; eauto. 1-2: eapply local_locs_closed; eauto.
  eapply local_locs_kill_sep_empty; eauto.
Qed.

Lemma qdiff_subqual_rev_monotone : forall q d1 d2,
  d2 ⊑↑ d1 ->
  qdiff q d1 ⊑↑ qdiff q d2.
Proof.
  intros. qual_destruct d1; qual_destruct d2; qual_destruct q. Qcrush.
Qed.

Lemma qdiff_incr: forall d1 d2 l b f,
  closed_Qual b f l d1↑ ->
  qdiff d1 d2 ⊑↑ qdiff (d1 ⊔ &!l) (d2 ⊔ &!l).
Proof.
  intros. qual_destruct d1; qual_destruct d2. Qcrush. subst. specialize (H2 l H3). lia.
Qed.

Lemma qdiff_eval : forall d dif,
  kill_sep dif d ->
  qdiff (d ⊔ dif) dif ⊑↑ d.
Proof.
  intros. unfold kill_sep in *. qual_destruct d; qual_destruct dif. Qcrush.
Qed.

Lemma qdiff_kill_sep : forall d dif,
  kill_sep dif (qdiff d dif).
Proof.
  intros. qual_destruct dif; qual_destruct d. unfold kill_sep. Qcrush.
Qed.

Lemma qdiff_in : forall l d dif,
  l ∈ₗ d  ->
  kill_sep dif &!l ->
  l ∈ₗ (qdiff d dif).
Proof.
  intros. qual_destruct dif; qual_destruct d. unfold kill_sep in H0. Qcrush. apply (H4 l). auto.
Qed.

Lemma kill_sep_subq_incr_irrevelance : forall d1 d2 l,
  d1 ⊑↑ (d2 ⊔ &!l) -> kill_sep &!l d1 -> kill_sep &!l d2 ->
  d1 ⊑↑ d2.
Proof.
  unfold kill_sep. intros. qual_destruct d1; qual_destruct d2. Qcrush.
  specialize (H1 x H0); rewrite or_false_elim in H1; auto. specialize (H5 x H0); rewrite or_false_elim in H5; auto. specialize (H9 x H0). destruct H9; auto. exfalso. apply (H10 x); auto.
Qed.


Lemma closed_Qual_qdiff : forall b f l d1 d2,
  closed_Qual b f l d1↑ ->
  closed_Qual b f l d2↑ ->
  closed_Qual b f l (qdiff d1 d2)↑.
Proof.
  intros. Qcrush.
Qed.


Lemma qdiff_remove : forall d1 d2 l Σ b f,
  l ∈ₗ d2 -> l < ‖Σ‖ ->
  closed_Qual b f (‖Σ‖) d1↑ ->
  qdiff d1 d2 ⊑↑ qdiff (q_remove Σ l d1) d2.
Proof.
  intros. Qcrush. rewrite or_false_elim. specialize (q_remove_in Σ l x d1). intros. Qcrush. rewrite or_false_elim in H7. bdestruct (x=?l); subst. specialize (H6 H). lia.
  apply H7; auto. unfold kill_sep. Qcrush.
Qed.


(* ====== store indexing ======== *)

Lemma indexr'_inv : forall {A} {σs : option (list A)} {l x}, indexr' l σs = Some x -> exists y, σs = Some y /\ indexr l y = Some x.
Proof.
  intros. destruct σs. simpl. exists l0; auto. simpl in H. inversion H.
Qed.

Lemma sindexr'_inv : forall {A} {σ : list (option (list A))} {l o x}, sindexr' l o σ = Some x ->
  exists y, indexr l σ = Some (Some y) /\ indexr o y = Some x.
Proof.
  induction σ; intros; simpl. inversion H. simpl in H. bdestruct (l =? length σ).
  apply indexr'_inv in H. destruct H as [? [? ?]]; subst. exists x0; split; auto.
  apply IHσ in H. destruct H as [? [? ?]]. subst. exists x0. split; auto.
Qed.

Lemma sindexr'_var_some' :  forall {A} {σ : list (option (list A))} {l o x}, sindexr' l o σ = Some x -> (l < length σ) /\ (exists y, indexr l σ = Some (Some y) /\ (o < length y)).
Proof.
  intros. apply sindexr'_inv in H as H'. destruct H'. destruct H0. split. apply indexr_var_some' in H0; auto. exists x0; auto. split; auto. apply indexr_var_some' in H1; auto.
Qed.