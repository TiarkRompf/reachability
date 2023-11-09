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
Require Import nats.
Require Import qualifiers.
Require Import boolean.

Import QualNotations.
Local Open Scope qualifiers.

(* Definitions *)

(* ### Syntax ### *)
(* We represent terms and types in locally nameless style. *)
Inductive ty : Type :=
| TTop  : ty
| TVar  : var -> ty
| TAll  : qual -> qual -> ty ->  ty -> ty  (* ∀ X<:T^d. T^d *)
| TUnit : ty
| TFun  : qual -> qual -> ty -> ty -> ty
| TRef  : qual -> ty -> ty
.

Inductive tm : Type :=
| ttabs   : (* ty -> *) tm -> tm    (* type bound is now implicit *)
| ttapp   : tm -> (* ty -> *) tm    (* type argument is now implicit *)
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
Coercion TVar : var >-> ty.

Inductive binding :=
| bind_tm : binding  (* term typing x: T *)
| bind_ty : binding  (* abstract tying X <: T*)
.

Definition tenv := list (binding * bool * ty * qual). (* (binding, isFunctionSelfRef, Type, Qual) *)
Definition senv := list (ty * qual). (* Sigma store typing *)

#[global] Hint Rewrite (@N_lift_dom (binding * bool * ty * qual)) : nlift_rewrite.
#[global] Hint Rewrite (@N_lift_dom (ty * qual)) : nlift_rewrite.

Definition extends {A} (l1 l2 : list A): Prop := exists l', l1 = l' ++ l2.
Notation "x ⊇ y" := (extends x y) (at level 75). (* \supseteq*)

Notation "‖ x ‖" := (length x) (at level 10). (* \Vert *)

(* Opening a term *)
Fixpoint open_rec_tm (k : nat) (u : tm) (t : tm) {struct t} : tm :=
  match t with
  | ttabs (* Tᵈ *) t => ttabs (* ... *) (open_rec_tm (S (S k)) u t)
  | ttapp t (* Tᵈ *) => ttapp (open_rec_tm k u t) (* ... *)
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

Definition openq (u u' q : qual) : qual := open_qual 1 u' (open_qual 0 u q).
Definition openq' {A} (env : list A) q  := openq ($!‖env‖) $!(S (‖env‖)) q.

(* Opening a type with a type and a qualifier *)
Fixpoint open_rec_ty (k : nat)(U:  ty) (d' : qual) (T : ty) : ty :=
  match T with
  | TTop              => TTop
  | TVar (varF x)     => TVar (varF x)
  | TVar (varB x)     => if Nat.eqb k x then U else (TVar (varB x))
  | TAll d1 d2 T1 T2  => TAll (open_qual k d' d1) (open_qual (S (S k)) d' d2) (open_rec_ty k U d' T1) (open_rec_ty (S (S k)) U d' T2)
  | TUnit             => TUnit
  | TFun d1 d2 T1 T2  => TFun (open_qual k d' d1) (open_qual (S (S k)) d' d2) (open_rec_ty k U d' T1) (open_rec_ty (S (S k)) U d' T2)
  | TRef d T          => TRef (open_qual k d' d) (open_rec_ty k U d' T)
  end.
Definition open_ty (U : ty)(du : qual)(V : ty)(dv : qual) (T : ty) : ty := (open_rec_ty 1 V dv  (open_rec_ty 0 U du T)).
Definition open_ty' {A : Type} (env : list A) (T : ty) :=
  open_ty  (TVar $(‖env‖)) ($!‖env‖) (TVar $(S (‖env‖))) ($!( S (‖env‖))) T.

Module OpeningNotations.
  Declare Scope opening.
  Notation "[[ k ~> u ]]ᵗ t"       := (open_rec_tm k u t) (at level 10) : opening.
  Notation "[[ k ~> U ~ d ]]ᵀ T"   := (open_rec_ty k U d T) (at level 10) : opening.
  Notation "[[ k ~> q' ]]ᵈ q"      := (open_qual k q' q) (at level 10) : opening.
  Notation "t <~ᵗ q ; q'"          := (open_tm q q' t) (at level 10, q at next level) : opening.
  Notation "T <~ᵀ U ~ du ; V ~ dv" := (open_ty U du V dv  T) (at level 10, U, du at next level) : opening.
  Notation "q <~ᵈ q' ; q''"        := (openq q' q'' q) (at level 10, q' at next level) : opening.
  Notation "t <~²ᵗ g"              := (open_tm' g t) (at level 10) : opening.
  Notation "T <~²ᵀ g"              := (open_ty' g T) (at level 10) : opening.
  Notation "q <~²ᵈ g"              := (openq' g q) (at level 10) : opening.
End OpeningNotations.
Import OpeningNotations.
Local Open Scope opening.

(* measure for induction over types *)
Fixpoint ty_size (T : ty) : nat :=
  match T with
  | TTop            => 0
  | TVar _          => 0
  | TAll _ _ T1 T2  => S (ty_size T1 + ty_size T2)
  | TUnit           => 0
  | TFun  _ _ T1 T2 => S (ty_size T1 + ty_size T2)
  | TRef  _ T       => S (ty_size T)
  end.

Fixpoint splice (n : nat) (t : tm) {struct t} : tm :=
  match t with
  | ttabs (*T*) t  => ttabs (splice n t)
  | ttapp t (*T*)  => ttapp (splice n t)
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
  | TTop             => TTop
  | TVar (varF i)    => if le_lt_dec n i then TVar (varF (S i)) else TVar (varF i)
  | TVar (varB i)    => TVar (varB i)
  | TAll d1 d2 T1 T2 => TAll (splice_qual n d1) (splice_qual n d2) (splice_ty n T1) (splice_ty n T2)
  | TUnit            => TUnit
  | TFun d1 d2 T1 T2 => TFun (splice_qual n d1) (splice_qual n d2) (splice_ty n T1) (splice_ty n T2)
  | TRef d1 T        => TRef (splice_qual n d1) (splice_ty n T)
  end.

Definition liftb (h: bool -> bool) (f: ty -> ty)(g: qual -> qual) b :=
  match b with
    | (bind_tm, self, T, q) => (bind_tm, (h self), (f T), (g q))
    | (bind_ty, self, T, q) => (bind_ty, (h self), (f T), (g q))
end.

Definition idfun (n: nat)(x: bool) : bool := x.

Lemma idfun_inv: forall {n x},  idfun n x = x.
Proof.  intros.  unfold idfun.  auto.
Qed.
#[global] Hint Resolve idfun_inv : core.

Definition splice_tenv (n : nat) (Γ : tenv) : tenv :=
  map (fun p => (liftb (idfun n) (splice_ty n) (splice_qual n) p)) Γ.

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
| cl_ttabs: forall b f l t,
  closed_tm (S (S b)) f l t ->
  closed_tm b f l (ttabs t)
| cl_ttapp: forall b f l t,
  closed_tm b f l t ->
  closed_tm b f l (ttapp t)
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

Inductive closed_ty : nat(*B*) -> nat(*F*) -> nat(*Loc*) -> ty -> Prop :=
| cl_TTop : forall b f l,
  closed_ty b  f l TTop
| cl_ttvarf: forall b f l x,
  x < f ->
  closed_ty b f l (TVar (varF x))
| cl_ttvarb: forall b f l x,
  x < b ->
  closed_ty b f l (TVar (varB x))
|  cl_TAll:  forall b f l d1 d2 T1 T2 ,
  closed_Qual b f l d1 ↑ ->
  closed_Qual  (S (S b)) f l d2 ↑ ->
  closed_ty b f l T1 ->
  closed_ty (S (S b)) f l T2 ->
  closed_ty b f l (TAll d1 d2 T1 T2)
| cl_TUnit : forall b f l,
    closed_ty b f l TUnit
| cl_TRef : forall b f l T q,
    closed_ty 0 0 0 T ->
    closed_Qual b f l q ↑ ->
    closed_ty b f l (TRef q T)
| cl_TFun : forall b f l d1 d2 T1 T2,
    closed_Qual b f l d1 ↑ ->
    closed_Qual (S (S b)) f l d2 ↑ ->
    closed_ty b f l T1 ->
    closed_ty (S (S b)) f l T2 ->
    closed_ty b f l (TFun d1 d2 T1 T2)
.
#[global] Hint Constructors closed_ty : core.

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
    stp ((bind_ty, false, T3, d3) :: (bind_tm, true, TAll d1 d2 T1 T2, {♦}) :: Γ) Σ  (open_ty' Γ T2) (openq' Γ d2) (open_ty' Γ T4) (openq' Γ d4) ->
    stp Γ Σ (TAll d1 d2 T1 T2) d5 (TAll d3 d4 T3 T4) d6

| s_base : forall Γ Σ d1 d2,
    qstp Γ Σ d1 d2 ->
    stp Γ Σ TUnit d1 TUnit d2

| s_ref : forall Γ Σ T1 T2 q d1 d2,
    qstp Γ Σ d1 d2 ->
    stp [] [] T1 ∅ T2 ∅ ->
    stp [] [] T2 ∅ T1 ∅ ->
    closed_Qual 0 (‖Γ‖) (‖Σ‖) q ↑ ->
    stp Γ Σ (TRef q T1) d1 (TRef q T2) d2

| s_fun : forall Γ Σ T1 d1 T2 d2 T3 d3 T4 d4 d5 d6,
    closed_ty 0 (‖ Γ ‖) (‖ Σ ‖) (TFun d1 d2 T1 T2) ->
    closed_ty 0 (‖ Γ ‖) (‖ Σ ‖) (TFun d3 d4 T3 T4) ->
    qstp Γ Σ d5 d6 ->
    stp Γ Σ T3 d3 T1 d1 ->
    stp ((bind_tm, false, T3,d3) :: (bind_tm, true, TFun d1 d2 T1 T2, {♦}) :: Γ) Σ (open_ty' Γ T2) (openq' Γ d2) (open_ty' Γ T4) (openq' Γ d4) ->
    stp Γ Σ (TFun d1 d2 T1 T2) d5 (TFun d3 d4 T3 T4) d6

| s_trans' : forall Γ Σ T1 T2 T3 d1 d2,
    stp Γ Σ T1 d1 T2 d2 -> stp Γ Σ T2 d2 T3 d2 -> stp Γ Σ T1 d1 T3 d2
.
#[global] Hint Constructors stp : core.

(* Specifies that q covers variable x's qualifier in context Γ|Σ *)
Inductive saturated_var (Γ : tenv) (Σ : senv) (x : id) (q : qual) : Prop :=
| sat_var : forall b U q',
    indexr x Γ = Some ((bind_tm, b, U, q')) ->
    q' ⊑↑ q ->
    closed_Qual 0 x (‖Σ‖) q' ↑ ->
    saturated_var Γ Σ x q
| sat_tvar : forall b U q',
    indexr x Γ = Some ((bind_ty, b, U, q')) ->
    q' ⊑↑ q ->
    closed_Qual 0 x (‖Σ‖) q' ↑ ->
    saturated_var Γ Σ x q.
Arguments sat_var {Γ Σ x q}.
Arguments sat_tvar {Γ Σ x q}.
#[global] Hint Constructors saturated_var : core.

(* q covers l's qualifier in Σ *)
Inductive saturated_loc (Σ : senv) (l : id) (q : qual) : Prop :=
| sat_loc : forall U q',
    indexr l Σ = Some (U, q') ->
    q' ⊑↑ q ⊔ {♦} ->
    closed_Qual 0 0 l q' ↑ ->
    saturated_loc Σ l q.
Arguments sat_loc {Σ l q}.
#[global] Hint Constructors saturated_loc : core.

Definition tenv_saturated (Γ : tenv) (Σ : senv) (q: qual) : Prop := (forall x, (varF x) ∈ᵥ q -> saturated_var Γ Σ x q).
Definition senv_saturated (Σ : senv) (q: qual) : Prop := (forall l, l ∈ₗ q -> saturated_loc Σ l q).
#[global] Hint Unfold tenv_saturated : core.
#[global] Hint Unfold senv_saturated : core.

(* Specifies that q is transitively closed w.r.t. Γ|Σ, i.e., q covers each of its contained variables/locations in Γ|Σ *)
Definition saturated (Γ : tenv) (Σ : senv) (q: qual) := tenv_saturated Γ Σ q /\ senv_saturated Σ q.

(* Store typing contains closed types and well-scoped, saturated qualifiers. *)
Inductive wf_senv : senv -> Prop :=
| wf_senv_nil : wf_senv []
| wf_senv_cons : forall Σ T q,
    wf_senv Σ ->
    closed_ty 0 0 (‖Σ‖) T ->
    closed_Qual 0 0 (‖Σ‖) q↑ ->
    senv_saturated Σ q ->
    wf_senv ((T, q) :: Σ)
.
#[global] Hint Constructors wf_senv : core.

(* deBruijn index v occurs nowhere in T *)
Definition not_free (v : id) (T : ty): Prop := [[ v ~> TUnit ~ ∅ ]]ᵀ T = T.

Inductive has_type : tenv -> qual -> senv -> tm -> ty -> qual -> Prop :=
| t_tabs: forall Γ φ Σ t T1 T2 df d1 d2,
    closed_tm 2 (‖Γ‖) (‖Σ‖) t ->
    closed_ty 0 (‖Γ‖) (‖Σ‖) (TAll d1 d2 T1 T2) ->
    closed_Qual 0 (‖Γ‖) (‖Σ‖) φ↑ ->
    df ⊑↑ φ ->
    ♦∉ df ->
    senv_saturated Σ df ->
    has_type ((bind_ty, false, T1, d1)  :: (bind_tm, true, (TAll d1 d2 T1 T2), df) :: Γ)
             (df ⊔ ($!‖Γ‖) ⊔ $!(S (‖Γ‖)) ⊔ {♦}) Σ (t <~²ᵗ Γ) (T2 <~²ᵀ Γ) (d2 <~²ᵈ Γ) ->
    has_type Γ φ Σ (ttabs t) (TAll d1 d2 T1 T2) df

| t_tapp: forall Γ φ Σ t T1 T2 d1 d2  df,
    has_type Γ φ Σ t (TAll d1 d2 T1 T2) df ->
    closed_ty 0 (‖Γ‖) (‖Σ‖) T1 ->
    closed_Qual 0 (‖Γ‖) (‖Σ‖) d1↑ ->
    (d2 <~ᵈ ∅ ; ∅) ⊑↑ φ ->
    ♦∉ d1 ->
    d1 ⊑↑ φ ->
    senv_saturated Σ (d2 <~ᵈ ∅ ; ∅) ->
    senv_saturated Σ d1 ->
    not_free 0 T2 ->
    has_type Γ φ Σ (ttapp t) (T2 <~ᵀ TUnit ~ ∅; T1 ~ d1) (d2 <~ᵈ df ; d1)

| t_tapp_fresh : forall Γ φ Σ t d1 d1' d2 df df' T1 T2,
    has_type Γ φ Σ t (TAll (df' ⋒ d1') d2 T1 T2) df ->
    d1 ⊑↑ d1' ->
    df ⊑↑ df' ->
    closed_ty 0 (‖Γ‖) (‖Σ‖) T1 ->
    closed_Qual 0 (‖Γ‖) (‖Σ‖) d1↑ ->
    (d2 <~ᵈ ∅ ; ∅) ⊑↑ φ ->
    not_free 0 T2 ->
    (♦∈ d1 -> not_free 1 T2) ->
    d1' ⊑↑ φ ->
    df' ⊑↑ φ ->
    saturated Γ Σ d1' ->
    saturated Γ Σ df' ->
    senv_saturated Σ (d2 <~ᵈ ∅ ; ∅) ->
    senv_saturated Σ d1 -> (* !!! demanded by has_type_senv_saturated  !!! *)
    has_type Γ φ Σ (ttapp t) (T2 <~ᵀ TUnit ~ ∅; T1 ~ d1 ) (d2 <~ᵈ df ; d1)

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
    df ⊑↑ φ ->
    ♦∉ df ->
    senv_saturated Σ df ->
    has_type ((bind_tm, false, T1, d1) :: (bind_tm, true, (TFun d1 d2 T1 T2), df) :: Γ)
             (df ⊔ ($!‖Γ‖) ⊔ $!(S (‖Γ‖)) ⊔ {♦}) Σ (t <~²ᵗ Γ) (T2 <~²ᵀ Γ) (d2 <~²ᵈ Γ) ->
    has_type Γ φ Σ (tabs t) (TFun d1 d2 T1 T2) df

| t_app : forall Γ φ Σ t1 d1 t2 d2 df T1 T2,
    has_type Γ φ Σ t1 (TFun d1 d2 T1 T2) df ->
    has_type Γ φ Σ t2 T1 d1 ->
    (d2 <~ᵈ ∅ ; ∅) ⊑↑ φ ->
    ♦∉ d1 ->
    not_free 0 T2 ->
    senv_saturated Σ (d2 <~ᵈ ∅ ; ∅) ->
    has_type Γ φ Σ (tapp t1 t2) (T2 <~ᵀ TUnit ~ ∅ ; T1 ~ d1) (d2 <~ᵈ df ; d1)

| t_app_fresh : forall Γ φ Σ t1 d1 d1' t2 d2 df df' T1 T2,
    has_type Γ φ Σ t1 (TFun (df' ⋒ d1') d2 T1 T2) df ->
    d1 ⊑↑ d1' ->
    df ⊑↑ df' ->
    has_type Γ φ Σ t2 T1 d1 ->
    (♦∈ d1 -> not_free 1 T2) ->
    not_free 0 T2 ->
    (d2 <~ᵈ ∅ ; ∅) ⊑↑ φ ->
    d1' ⊑↑ φ ->
    df' ⊑↑ φ ->
    saturated Γ Σ d1' ->
    saturated Γ Σ df' ->
    senv_saturated Σ (d2 <~ᵈ ∅ ; ∅) ->
    has_type Γ φ Σ (tapp t1 t2) (T2 <~ᵀ TUnit ~ ∅ ; T1 ~ d1) (d2 <~ᵈ df ; d1)

| t_loc : forall Γ φ Σ l T q,
    closed_Qual 0 (‖Γ‖) (‖Σ‖) φ↑ ->
    indexr l Σ = Some (T,q) ->
    closed_ty 0 0 0 T ->
    closed_Qual 0 0 (‖Σ‖) q↑ ->
    &!l ⊑↑ φ ->
    q ⊑↑ φ ->
    ♦∉ q ->
    has_type Γ φ Σ &l (TRef q T) (q ⊔ &!l)

| t_ref: forall Γ φ Σ T t d1,
    has_type Γ φ Σ t T d1 ->
    closed_ty 0 0 0 T ->
    {♦} ⊑↑ φ ->
    ♦∉ d1 ->
    has_type Γ φ Σ (tref t) (TRef d1 T) ({♦} ⊔ d1)

| t_deref: forall Γ φ Σ T d d1 t,
    has_type Γ φ Σ t (TRef d1 T) d ->
    ♦∉ d1 ->
    d1 ⊑↑ φ ->
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
    d2 ⊑↑ φ ->
    senv_saturated Σ d2 ->
    has_type Γ φ Σ e T2 d2
.
#[global] Hint Constructors has_type : core.

Inductive value : tm -> Prop :=
| value_ttabs: forall t, value (ttabs t)
| value_abs : forall t, value (tabs t)
| value_cst : value tunit
| value_loc : forall l, value &l
.
#[global] Hint Constructors value : core.

Definition store := list tm.

Inductive step : tm -> store -> tm -> store -> Prop :=
(*contraction rules*)
| step_ttapp: forall t σ,
  step (ttapp (ttabs t)) σ (t <~ᵗ (ttabs t); tunit) σ
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
| step_c_tapp: forall t t' σ σ',
  step t σ t' σ' ->
  step (ttapp t)  σ (ttapp t') σ'
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
  | ttabs t       => ttabs (subst_tm t v u)
  | ttapp t       => ttapp (subst_tm t v u)
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

Fixpoint subst_ty (T : ty) (v : nat) (U: ty) (q : qual) : ty :=
  match T with
  | TTop             => TTop
  | TVar (varF i)    => if Nat.eqb i v then U else (TVar (varF (pred i)))
  | TVar (varB i)    => TVar (varB i)
  | TAll q1 q2 T1 T2 => TAll (subst_qual q1 v q) (subst_qual q2 v q) (subst_ty T1 v U q) (subst_ty T2 v U q)
  | TUnit            => TUnit
  | TFun q1 q2 T1 T2 => TFun (subst_qual q1 v q) (subst_qual q2 v q) (subst_ty T1 v U q) (subst_ty T2 v U q)
  | TRef q1 T        => TRef (subst_qual q1 v q) (subst_ty T v U q)
  end.

Definition subst_tenv (Γ : tenv) (v : nat) (U: ty)(q1 : qual) : tenv :=
  map (fun p => match p with
             | (bind_tm, b, T, q') => (bind_tm, b, (subst_ty T v U q1) , (subst_qual q' v q1))
             | (bind_ty, b,  T, q') => (bind_ty, b, (subst_ty T v U q1) , (subst_qual q' v q1))
             end) Γ.

Module SubstitutionNotations.
  Declare Scope substitutions.
  Notation "{ v1 |-> t1 ; t2 }ᵗ t"  := (subst_tm (subst_tm t v1 t1) v1 t2) (at level 10) : substitutions.
  Notation "{ v1 |-> t1 }ᵗ t"       := (subst_tm t v1 t1) (at level 10) : substitutions.
  Notation "{ v1 |-> q1 ; q2 }ᵈ q"  := (subst_qual (subst_qual q v1 q1) v1 q2) (at level 10) : substitutions.
  Notation "{ v1 |-> q1 }ᵈ q"       := (subst_qual q v1 q1) (at level 10) : substitutions.
  Notation "{ v1 |-> U1 ~ q1 ; U2 ~ q2  }ᵀ T" := (subst_ty (subst_ty T v1 U1 q1) v1 U2 q2) (at level 10) : substitutions.
  Notation "{ v1 |-> U1 ~ q1 }ᵀ T" := (subst_ty T v1 U1 q1) (at level 10) : substitutions.
  Notation "{ v1 |-> T1 ~ q1 }ᴳ G" := (subst_tenv G v1 T1 q1) (at level 10) : substitutions.
  Notation "{ v1 |-> T1 ~ q1 ; T2 ~ q2 }ᴳ G" := (subst_tenv (subst_tenv G v1 T1 q1) v1 T2 q2) (at level 10) : substitutions.
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
    q ⊑↑ q' ->
    closed_ty 0 0 (‖Σ‖) T ->
    closed_Qual 0 0 (‖Σ‖) q↑ ->
    senv_saturated Σ q ->
    Σ' = (T,q) :: Σ ->
    disjointq Σ Σ' q' (q ⊔ &!‖Σ‖)
.
Arguments disj_loc { Σ Σ' }.
#[global] Hint Constructors disjointq : core.
Notation " S → T ∋ q ⊕ q'" := (disjointq S T q q') (at level 10).

(* :! -- directly invertible value typing *)

Inductive vtp: senv -> tm -> ty -> qual -> Prop :=
| vtp_tabs: forall Σ t T1 T2 T3 T4 d1 d2 d3 d4 df1 df2,
  closed_tm 2 0 (‖Σ‖) t ->
  closed_ty 0 0 (‖Σ‖) (TAll d3 d4 T3 T4) -> (* supertype *)
  closed_ty 0 0 (‖Σ‖) (TAll d1 d2 T1 T2) -> (* subtype *)
  has_type [(bind_ty, false, T1, d1); (bind_tm, true, (TAll d1 d2 T1 T2), df1)] (df1 ⊔ $!0 ⊔ $!1 ⊔ {♦})  Σ
           (t <~²ᵗ ([] : tenv)) (T2 <~²ᵀ ([] : tenv)) (d2 <~²ᵈ ([] : tenv)) ->
  stp [] Σ T3 d3 T1 d1 ->
  qstp [] Σ df1 df2 ->
  stp [(bind_ty, false, T3, d3); (bind_tm, true, (TAll d1 d2 T1 T2), {♦})] Σ
      (T2 <~²ᵀ ([] : tenv)) (d2 <~²ᵈ ([] : tenv))
      (T4 <~²ᵀ ([] : tenv)) (d4 <~²ᵈ ([] : tenv)) ->
  ♦∉ df1 ->
  senv_saturated Σ df1 ->
  senv_saturated Σ df2 ->
  vtp Σ (ttabs t) (TAll d3 d4 T3 T4) df2

| vtp_base: forall Σ d,
  closed_Qual 0 0 (‖Σ‖) d↑ ->
  senv_saturated Σ d ->
  vtp Σ tunit TUnit d

| vtp_loc:  forall Σ l T U q d,
  closed_Qual 0 0 (‖Σ‖) d↑ ->
  closed_ty 0 0 0 T ->
  closed_Qual 0 0 (‖Σ‖) q↑ ->
  indexr l Σ = Some (T,q) ->
  stp [] [] T ∅ U ∅ ->
  stp [] [] U ∅ T ∅ ->
  qstp [] Σ (q ⊔ &!l) d ->
  ♦∉ q ->
  senv_saturated Σ d ->
  vtp Σ &l (TRef q U) d

| vtp_abs: forall Σ T1 d1 T2 d2 T3 d3 T4 d4 df1 df2 t,
  closed_tm 2 0 (‖Σ‖) t ->
  closed_Qual 0 0 (‖Σ‖) df2↑ ->
  closed_ty 0 0 (‖Σ‖) (TFun d3 d4 T3 T4) -> (* supertype *)
  closed_ty 0 0 (‖Σ‖) (TFun d1 d2 T1 T2) -> (* subtype *)
  has_type [(bind_tm, false,T1,d1) ; (bind_tm, true, (TFun d1 d2 T1 T2), df1)]
            (df1 ⊔ $!0 ⊔ $!1 ⊔ {♦}) Σ (t <~²ᵗ ([] : tenv)) (T2 <~²ᵀ ([] : tenv)) (d2 <~²ᵈ ([] : tenv)) ->
  stp [] Σ T3 d3 T1 d1 ->
  qstp [] Σ df1 df2 ->
  stp [(bind_tm, false,T3, d3) ; (bind_tm, true, (TFun d1 d2 T1 T2), {♦})] Σ
      (T2 <~²ᵀ ([] : tenv)) (d2 <~²ᵈ ([] : tenv))
      (T4 <~²ᵀ ([] : tenv)) (d4 <~²ᵈ ([] : tenv)) ->
  ♦∉ df1 ->
  senv_saturated Σ df1 ->
  senv_saturated Σ df2 ->
  vtp Σ (tabs t) (TFun d3 d4 T3 T4) df2

| vtp_top: forall Σ t T d,
  vtp Σ t T d ->
  senv_saturated Σ d ->   (* due to vtp_saturated *)
  vtp Σ t TTop d
.
#[global] Hint Constructors vtp : core.

(* The concluding statement of the preservation part of type safety, i.e., typing is preserved after a step under an extended store, so
   that the initial qualifier is increased by at most a fresh storage effect. *)
Inductive preserve (Γ : tenv) (Σ : senv) (t' : tm) (T : ty) (d : qual) (σ' : store) : Prop :=
| Preserve : forall Σ' d',
    Σ' ⊇ Σ ->
    wf_senv Σ' ->
    CtxOK Γ (qdom Σ') Σ' σ' ->
    Σ → Σ' ∋ d ⊕ d'  ->
    has_type Γ (qdom Σ') Σ' t' T (d ⋓ d') ->
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
    q1' ⋒ q2' ⊑↑ {♦} ->
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
  intros. unfold extends. exists l. apply app_nil_end.
Qed.
#[global] Hint Resolve extends_empty : core.

Lemma extends_cons : forall {A}, forall{l : list A}, forall{a:A}, (a :: l) ⊇ l.
  intros. unfold extends. exists [a]. auto.
Qed.
#[global] Hint Resolve extends_cons : core.

Lemma extends_length : forall {A}, forall{l1 l2 : list A}, l1 ⊇ l2 -> length l2 <= length l1.
  intros. unfold extends in H. destruct H as [l' Heq]. subst. rewrite app_length. lia.
Qed.
#[global] Hint Resolve extends_length : core.

Lemma extends_qdom : forall {Σ' Σ : senv}, Σ' ⊇ Σ -> qdom Σ ⊑↑ qdom Σ'.
intros. inversion H. Qcrush.
assert (‖Σ'‖ = ‖x‖ + ‖Σ‖). subst. rewrite app_length. auto. lia.
Qed.
#[global] Hint Resolve extends_qdom: core.

Lemma open_tm'_len : forall {A} {Γ Γ' : list A} {t}, ‖Γ‖ = ‖Γ'‖ -> open_tm' Γ t = open_tm' Γ' t.
  intros.  unfold open_tm'. rewrite H. auto.
Qed.

Lemma open_ty'_len : forall {A} {Γ Γ' : list A} {T}, ‖Γ‖ = ‖Γ'‖ -> open_ty' Γ T = open_ty' Γ' T.
  intros.  unfold open_ty'. rewrite H. auto.
Qed.

Lemma openq'_len : forall {A} {Γ Γ' : list A} {q}, ‖Γ‖ = ‖Γ'‖ -> openq' Γ q = openq' Γ' q.
  intros.  unfold openq'. rewrite H. auto.
Qed.

Lemma open_ty_preserves_size: forall T d j x, ty_size T = ty_size (open_rec_ty j (TVar (varF x)) d T).
Proof.  induction T; intros; simpl; eauto. destruct v. auto. destruct (Nat.eqb j i); auto.
Qed.

Lemma closed_Qual_qdom : forall {Σ : senv}, closed_Qual 0 0 (‖Σ‖) (qdom Σ)↑.
  intros. Qcrush.
Qed.
#[global] Hint Resolve closed_Qual_qdom : core.
Lemma closed_qual_qdom : forall {Σ : senv}, closed_qual 0 0 (‖Σ‖) (qdom Σ).
  intros. apply Q_lift_closed. auto.
Qed.
#[global] Hint Resolve closed_qual_qdom : core.

Lemma closed_qual_cong : forall {b f l d},
    closed_qual b f l d -> forall {d'}, d = d' -> closed_qual b f l d'.
Proof.
  intros. subst. auto.
Qed.

Lemma just_fv_closed : forall {x b f l fr}, x < f <-> closed_qual b f l (${ fr } x).
Proof.
  split; intros.
  - apply Q_lift_closed. Qcrush.
  - apply Q_lift_closed' in H. Qcrush.
Qed.

Lemma just_loc_closed : forall {x b f l fr}, x < l <-> closed_qual b f l (&{ fr } x).
Proof.
  split; intros.
  - apply Q_lift_closed. Qcrush.
  - apply Q_lift_closed' in H. Qcrush.
Qed.

Lemma splice_tenv_length : forall {n Γ}, ‖ Γ ↑ᴳ n ‖ = ‖Γ‖.
  intros. unfold splice_tenv. rewrite map_length. auto.
Qed.

Lemma closed_tm_monotone : forall {t b l f}, closed_tm b f l t -> forall {b' f' l'}, b <= b' -> f <= f' -> l <= l' -> closed_tm b' f' l' t.
  intros T b f l H. induction H; intuition.
Qed.

Lemma closed_ty_monotone : forall {T b l f}, closed_ty b f l T -> forall {b' f' l'}, b <= b' -> f <= f' -> l <= l' -> closed_ty b' f' l' T.
  intros T b f l H. induction H; intuition.
  constructor. 1,2: eapply closed_qual_monotone; eauto; lia.
  eapply IHclosed_ty1; eauto. eapply IHclosed_ty2; eauto. lia.
  constructor; auto. eapply closed_qual_monotone; eauto.
  constructor. 1,2: eapply closed_qual_monotone; eauto; lia.
  eapply IHclosed_ty1; eauto. eapply IHclosed_ty2; eauto. lia.
Qed.

Lemma closed_tm_open_id : forall {t b f l}, closed_tm b f l t -> forall {n}, b <= n -> forall {x}, [[n ~> x ]]ᵗ t = t.
  intros t b f l H. induction H; intros; simpl; auto;
    try solve [erewrite IHclosed_tm1; eauto; erewrite IHclosed_tm2; eauto; lia | erewrite IHclosed_tm; eauto; lia].
  destruct (Nat.eqb n x) eqn:Heq; auto. apply Nat.eqb_eq in Heq. lia.
Qed.

Lemma closed_ty_open_id : forall {T b f l}, closed_ty b f l T -> forall {n}, b <= n -> forall {U d}, (open_rec_ty n U d T) = T.
  intros T b f l H. induction H; intros; simpl; auto;
    try solve [erewrite IHclosed_ty1; eauto; erewrite IHclosed_ty2; eauto; lia | erewrite IHclosed_ty; eauto; lia].
  destruct (Nat.eqb n x) eqn: Hnx; intuition.  apply Nat.eqb_eq in Hnx. intuition.
  erewrite IHclosed_ty1; eauto; erewrite IHclosed_ty2; eauto.
  erewrite closed_qual_open_id; eauto. erewrite closed_qual_open_id; eauto. lia. lia.
  erewrite IHclosed_ty; eauto. erewrite closed_qual_open_id; eauto. lia.
  erewrite IHclosed_ty1; eauto; erewrite IHclosed_ty2; eauto.
  erewrite closed_qual_open_id; eauto. erewrite closed_qual_open_id; eauto.
  all : lia.
Qed.

Lemma closed_tm_open : forall {t b f l}, closed_tm (S b) f l t -> forall {x}, x < f -> closed_tm b f l ([[ b ~> $x ]]ᵗ t).
  induction t; intros; simpl; intuition; inversion H; subst; try constructor;
  try solve [apply IHt1; auto | apply IHt2; auto | apply IHt; auto ].
  destruct (Nat.eqb b x0) eqn:Heq; intuition.
  apply Nat.eqb_neq in Heq. constructor. lia. auto. auto.
Qed.

Lemma closed_tm_open' : forall {t b f l}, closed_tm (S b) f l t -> forall {x}, x <= f -> forall {t'}, closed_tm 0 x l t' -> closed_tm b f l ([[ b ~> t' ]]ᵗ t).
  induction t; intros; simpl; intuition; inversion H; subst; try constructor;
  try solve [eapply IHt1; eauto | eapply IHt2; eauto | eapply IHt; eauto ].
  destruct (Nat.eqb b x0) eqn:Heq; intuition. eapply closed_tm_monotone; eauto; lia.
  apply Nat.eqb_neq in Heq. constructor. lia. auto. auto.
Qed.

Lemma closed_ty_open' : forall {T b f l}, closed_ty (S b) f l T -> forall {x}, x <= f ->
  forall {U d}, closed_ty 0 x l U -> closed_qual 0 x l d -> closed_ty b f l ([[ b ~> U ~ d ]]ᵀ T).
  induction T; intros; simpl; intuition; inversion H; subst; try constructor;
    try solve [eapply IHT1; eauto | eapply IHT2; eauto | eapply IHT; eauto ]; intuition.
  destruct (b =? x0) eqn: Hbi; intuition. apply Nat.eqb_eq in Hbi. eapply closed_ty_monotone; eauto. lia.
  apply Nat.eqb_neq in Hbi. intuition.
  1-4,6 : eapply closed_qual_open'; eauto.
  erewrite closed_ty_open_id; eauto. lia.
Qed.

Lemma closed_open_succ : forall {t b f l}, closed_tm b f l t -> forall {j}, closed_tm b (S f) l ([[ j ~> $f ]]ᵗ t).
  induction t; intros; simpl; intuition; inversion H; subst; try constructor;
    try solve [eapply IHt1; eauto | eapply IHt2; eauto | eapply IHt; eauto ].
    destruct (Nat.eqb j x) eqn:Heq. intuition.
    apply Nat.eqb_neq in Heq. inversion H. subst. intuition. lia. auto.
Qed.

Lemma closed_ty_open_succ : forall {T fr b f l}, closed_ty b f l T -> forall {j}, closed_ty b (S f) l ([[ j ~>  (TVar (varF f))  ~  ${fr}f ]]ᵀ T).
  induction T; intros; simpl; intuition; inversion H; subst; try constructor;
    try solve [eapply IHT1; eauto | eapply IHT2; eauto | eapply IHT; eauto ]; try rewrite Q_lift_open_qual; intuition.
   destruct (j =? x) eqn: Heq. apply Nat.eqb_eq in Heq. intuition. apply Nat.eqb_neq in Heq. intuition.
  erewrite closed_ty_open_id; eauto. lia.
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

Lemma open_rec_ty_commute : forall T frx fry i j x y, i <> j ->
    [[i ~> (TVar (varF x)) ~ ${frx} x ]]ᵀ ([[j ~> (TVar (varF y)) ~ ${fry} y ]]ᵀ T)
  = [[j ~> (TVar (varF y)) ~ ${fry} y ]]ᵀ ([[i ~> (TVar (varF x)) ~ ${frx} x ]]ᵀ T).
  induction T; intros; simpl; eauto;
    try solve [erewrite IHT1; eauto; erewrite IHT2; eauto | erewrite IHT; eauto].
  destruct v. auto.
  destruct (Nat.eqb j i0) eqn:Hji0; simpl; try rewrite Hii0; try rewrite Hji0; auto.
  apply Nat.eqb_eq in Hji0. subst. rewrite <- Nat.eqb_neq in H. rewrite H. simpl.
  rewrite Nat.eqb_refl. auto.
  destruct (Nat.eqb i i0) eqn:Hii0; simpl. auto. rewrite Hji0. auto.
  1-3: f_equal.
  1,2,5,6,9: erewrite open_qual_commute; eauto.
  1,3: erewrite IHT1; eauto.  3: erewrite IHT; eauto.  all: erewrite IHT2; eauto.
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

Lemma open_rec_ty_commute' : forall T  U i j fr x d f l, i <> j -> closed_ty 0 f l U -> closed_qual 0 f l d ->
    [[ i ~> (TVar (varF x)) ~ ${fr}x ]]ᵀ ([[ j ~> U ~ d ]]ᵀ T)
  = [[ j ~> U ~ d ]]ᵀ ([[ i ~> (TVar (varF x)) ~ ${fr}x ]]ᵀ T).
  induction T; intros; simpl; eauto;
    try solve [erewrite IHT1; eauto; erewrite IHT2; eauto | erewrite IHT; eauto].
  destruct v eqn:Heqv; auto.
  destruct (Nat.eqb i0 i) eqn:Hii0; destruct (Nat.eqb j i) eqn:Hji0; simpl;
      try rewrite Hii0; try rewrite Hji0; auto.
  apply Nat.eqb_eq in Hii0. apply Nat.eqb_eq in Hji0. subst. contradiction.
  rewrite Nat.eqb_sym in Hii0. rewrite Hii0. rewrite Nat.eqb_eq in Hii0. subst. rewrite Hji0. simpl. rewrite Nat.eqb_refl. auto.
  rewrite Nat.eqb_eq in Hji0. lia. rewrite Nat.eqb_sym in Hii0. rewrite Hii0. simpl.
  destruct (j =? i0) eqn:Hji00; simpl. erewrite closed_ty_open_id; eauto. lia.
  rewrite Hii0. auto.
  1-3: f_equal. 1,2,5,6,9:  erewrite open_qual_commute'; eauto.
  1,3: erewrite IHT1; eauto. 3: erewrite IHT; eauto. all: erewrite IHT2; eauto.
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

Lemma open_rec_ty_commute'' : forall T i j U' U'' d' d'' f l, i <> j -> closed_ty 0 f l U' -> closed_ty 0 f l U'' -> closed_qual 0 f l d' -> closed_qual 0 f l d'' ->
    [[ i ~> U'' ~ d'']]ᵀ ([[ j ~> U' ~ d' ]]ᵀ T)
  = [[ j ~> U' ~ d' ]]ᵀ ([[ i ~> U'' ~  d'' ]]ᵀ T).
  induction T; intros; simpl; eauto;
    try solve [erewrite IHT1; eauto; erewrite IHT2; eauto | erewrite IHT; eauto].
  destruct v eqn:Heqv. auto.
  destruct (Nat.eqb i0 i) eqn:Hii0; destruct (Nat.eqb j i) eqn:Hji0; simpl;
      try rewrite Hii0; try rewrite Hji0; auto.
    apply Nat.eqb_eq in Hii0. apply Nat.eqb_eq in Hji0. subst. lia.
  rewrite Nat.eqb_sym in Hii0. rewrite Hii0. rewrite Nat.eqb_eq in Hii0. subst.
  rewrite Hji0. simpl. rewrite Nat.eqb_refl. erewrite closed_ty_open_id; eauto. lia.
  rewrite Nat.eqb_eq in Hji0. lia.
  rewrite Nat.eqb_sym in Hii0. rewrite Hii0. simpl.
  destruct (j =? i0) eqn:Hji00; simpl. erewrite closed_ty_open_id; eauto. lia.
  rewrite Hii0. auto.
  1-3: f_equal. 1,2,5,6,9:  erewrite open_qual_commute''; eauto.
  1,3: erewrite IHT1; eauto. 3: erewrite IHT; eauto. all: erewrite IHT2; eauto.
Qed.

Lemma open_qual_empty_id : forall k q fr, [[ k ~> q]]ᵈ ∅{ fr } = ∅{ fr }.
  Qcrush.
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

Lemma splice_ty_id : forall {T b f l}, closed_ty b f l T -> T ↑ᵀ f = T.
  induction T; intros; inversion H; subst; simpl; auto;
    try solve [erewrite IHT1; eauto; erewrite IHT2; eauto | erewrite IHT; eauto].
  repeat erewrite splice_qual_id; eauto.
  destruct (le_lt_dec f x) eqn: Heq; intuition.
  1-3: f_equal. 1,2,5,6,9: eapply splice_qual_id; eauto.  1,3: eapply IHT1; eauto. 1-2: eapply IHT2; eauto.
  eapply IHT; eauto. eapply closed_ty_monotone; eauto. lia.
Qed.

Lemma splice_open : forall {T j n m}, ([[ j ~> $(m + n) ]]ᵗ T) ↑ᵗ n = [[ j ~> $(S (m + n)) ]]ᵗ (T ↑ᵗ n).
  induction T; intros; simpl; auto;
    try solve [erewrite IHT1; eauto; erewrite IHT2; eauto | erewrite IHT; eauto].
  destruct v; simpl. destruct (le_lt_dec n i) eqn:Heq; auto.
  destruct (PeanoNat.Nat.eqb j i) eqn:Heq; auto.
  simpl. destruct (le_lt_dec n (m + n)) eqn:Heq'. auto. lia.
Qed.

Lemma splice_ty_open : forall {T j fr n m},
  ([[j ~> $(m + n) ~ ${fr}(m + n) ]]ᵀ T) ↑ᵀ n =
  [[j ~> $(S (m + n)) ~ ${fr}(S (m + n)) ]]ᵀ (T ↑ᵀ n).
  induction T; intros; simpl; auto;
    try solve [erewrite IHT1; eauto; erewrite IHT2; eauto | erewrite IHT; eauto].
  destruct v; simpl.
  destruct (le_lt_dec n i ); simpl; auto.
  destruct (j =? i ); simpl; auto.
  f_equal. destruct (le_lt_dec n (m + n) ); simpl; auto. intuition.
  1-3: f_equal. 1,2,5,6,9: erewrite splice_qual_open; eauto.
  1,3: eapply IHT1; eauto. 3: eapply IHT; eauto. all: eapply IHT2; eauto.
Qed.

Lemma splice_open' : forall {T} {A} {D : A} {ρ ρ'}, ((T <~²ᵗ (ρ ++ ρ')) ↑ᵗ ‖ρ'‖) = (T ↑ᵗ ‖ρ'‖) <~²ᵗ (ρ ++ D :: ρ').
  intros. unfold open_tm'.
  replace (‖ ρ ++ ρ' ‖) with (‖ρ‖ + ‖ρ'‖).
  replace (S (‖ ρ ++ D :: ρ' ‖)) with (S (S (‖ρ‖) + (‖ρ'‖))).
  replace (‖ ρ ++ D :: ρ' ‖) with (S (‖ρ‖ + ‖ρ'‖)).
  repeat rewrite <- splice_open. auto.
  all: rewrite app_length; simpl; lia.
Qed.

Lemma splice_qual_open' : forall {d} {A} {D : A} {ρ ρ'}, ((d <~²ᵈ (ρ ++ ρ')) ↑ᵈ ‖ρ'‖) = (d ↑ᵈ ‖ρ'‖) <~²ᵈ (ρ ++ D :: ρ').
  intros. unfold openq'. unfold openq.
  replace (‖ ρ ++ ρ' ‖) with (‖ρ‖ + ‖ρ'‖).
  replace (S (‖ ρ ++ D :: ρ' ‖)) with (S (S (‖ρ‖) + (‖ρ'‖))).
  replace (‖ ρ ++ D :: ρ' ‖) with (S (‖ρ‖ + ‖ρ'‖)).
  repeat rewrite <- splice_qual_open. auto.
  all: rewrite app_length; simpl; lia.
Qed.

Lemma splice_qual_open''': forall {k d i} {q}, ([[i ~> d ]]ᵈ q) ↑ᵈ k = [[i ~> (d ↑ᵈ k)]]ᵈ (q ↑ᵈ k ).
Proof. qual_destruct q. qual_destruct d. unfold_q.
#[local] Hint Resolve n_reflect_true : bdestruct.
bdestruct (bvs i); simpl; auto. Qcrush. unfold_n. bdestruct (x =? k); bdestruct (x <? k); auto.
#[local] Remove Hints n_reflect_true : bdestruct.
Qed.

Lemma splice_ty_open' : forall {T} {A} {D : A} {ρ ρ'}, ((T <~²ᵀ (ρ ++ ρ')) ↑ᵀ ‖ρ'‖) = (T ↑ᵀ ‖ρ'‖) <~²ᵀ (ρ ++ D :: ρ').
  intros. unfold open_ty'. unfold open_ty.
  replace (‖ ρ ++ ρ' ‖) with (‖ρ‖ + ‖ρ'‖).
  replace (S (‖ ρ ++ D :: ρ' ‖)) with (S (S (‖ρ‖) + (‖ρ'‖))).
  replace (‖ ρ ++ D :: ρ' ‖) with (S (‖ρ‖ + ‖ρ'‖)).
  repeat rewrite <- splice_ty_open. auto.
  all: rewrite app_length; simpl; lia.
Qed.

Lemma splice_ty_open_rec_ty: forall {T T1  d1} {k i},
  splice_ty k ([[i ~> T1 ~ d1 ]]ᵀ T) = [[ i ~> (splice_ty k T1) ~ (splice_qual k d1) ]]ᵀ (splice_ty k T) .
Proof. intros. generalize dependent k. generalize dependent i. induction T; intros; simpl; auto;
    try solve [erewrite IHT1; eauto; erewrite IHT2; eauto | erewrite IHT; eauto].
    destruct v; simpl.
    destruct (le_lt_dec k i0); auto.
    destruct (i =? i0); auto.
    rewrite IHT1. rewrite IHT2. f_equal. 1,2: rewrite splice_qual_open'''; auto.
    rewrite IHT1. rewrite IHT2. f_equal. 1,2: rewrite splice_qual_open'''; auto.
    rewrite IHT.  f_equal. rewrite splice_qual_open'''; auto.
Qed.

Lemma splice_closed : forall {T b n m l}, closed_tm b (n + m) l T -> closed_tm b (S (n + m)) l (T ↑ᵗ m).
  induction T; simpl; intros; inversion H; subst; intuition.
  destruct (le_lt_dec m x) eqn:Heq; intuition.
Qed.

Lemma splice_Qual_closed : forall {d b n m l}, closed_Qual b (n + m) l d ↑ -> forall {i}, i <= m -> closed_Qual b (S (n + m)) l (d ↑ᵈ i) ↑.
intros. Qcrush. bdestruct (x <=? i); intuition. eauto using Nat.lt_pred_lt_succ.
Qed.

Lemma splice_qual_closed : forall {d b n m l}, closed_qual b (n + m) l d -> forall {i}, i <= m -> closed_qual b (S (n + m)) l (d ↑ᵈ i).
intros. apply Q_lift_closed. apply Q_lift_closed' in H. eauto using splice_Qual_closed.
Qed.

Lemma splice_ty_closed : forall {T b n m l}, closed_ty b (n + m) l T -> forall {i}, i <= m -> closed_ty b (S (n + m)) l (T ↑ᵀ i).
  induction T; simpl; intros; inversion H; subst; intuition.
  destruct (le_lt_dec i x); auto. intuition.
  1-3: constructor. 1,2,5,6,10: apply splice_qual_closed; auto.
  1,3: eapply IHT1; eauto; lia.
  1-2: eapply IHT2; eauto; lia.
  erewrite splice_ty_id; eauto. eapply closed_ty_monotone; eauto. lia.
Qed.

Lemma splice_closed' : forall {T b l} {A} {D : A} {ρ ρ'}, closed_tm b (‖ρ ++ ρ'‖) l T -> closed_tm b (‖ρ ++ D :: ρ'‖) l (T ↑ᵗ ‖ρ'‖).
  intros. rewrite app_length in H.
  replace (‖ ρ ++ D :: ρ' ‖) with (S (‖ρ‖ + ‖ρ'‖)).
  apply splice_closed. auto. simpl. rewrite app_length. simpl. lia.
Qed.

Lemma splice_qual_closed' : forall {d b l} {A} {D : A} {ρ ρ'}, closed_qual b (‖ρ ++ ρ'‖) l d -> closed_qual b (‖ρ ++ D :: ρ'‖) l (d ↑ᵈ ‖ρ'‖).
  intros. rewrite app_length in H.
  replace (‖ ρ ++ D :: ρ' ‖) with (S (‖ρ‖ + ‖ρ'‖)).
  eapply splice_qual_closed; eauto. simpl. rewrite app_length. simpl. lia.
Qed.

Lemma splice_ty_closed' : forall {T b l} {A} {D : A} {ρ ρ'}, closed_ty b (‖ρ ++ ρ'‖) l T -> closed_ty b (‖ρ ++ D :: ρ'‖) l (T ↑ᵀ ‖ρ'‖).
  intros. rewrite app_length in H.
  replace (‖ ρ ++ D :: ρ' ‖) with (S (‖ρ‖ + ‖ρ'‖)).
  eapply splice_ty_closed; eauto. simpl. rewrite app_length. simpl. lia.
Qed.

Lemma splice_Qual_closed'' : forall {q x b l k}, closed_Qual b x l q ↑ -> k <= x -> closed_Qual b (S x) l (q ↑ᵈ k) ↑.
intros. Qcrush. bdestruct (x0 <=? k); intuition. eauto using Nat.lt_pred_lt_succ.
Qed.

Lemma splice_qual_closed'' : forall {q x b l k}, closed_qual b x l q -> k <= x -> closed_qual b (S x) l (q ↑ᵈ k).
intros. apply Q_lift_closed. eauto using splice_Qual_closed''.
Qed.

Lemma splice_ty_closed'' : forall {T x b l k}, closed_ty b x l T -> k <= x -> closed_ty b (S x) l (T ↑ᵀ k).
  induction T; simpl; intros; inversion H; subst; try eapply closed_ty_monotone; eauto.
  destruct (le_lt_dec k x0); auto. intuition.
  1-3: constructor.
  1,2,5,6,10 : eapply splice_qual_closed''; eauto. 1,3: eapply IHT1; eauto.
  1-2: eapply IHT2; eauto. erewrite splice_ty_id; eauto.
  eapply closed_ty_monotone; eauto. lia.
Qed.

Lemma splice_open_succ : forall {T b n l j}, closed_tm b n l T -> ([[ j ~> $n ]]ᵗ T) ↑ᵗ n = [[ j ~> $ (S n) ]]ᵗ T.
  induction T; simpl; intros; inversion H; subst; auto;
    try solve [erewrite IHT1; eauto; erewrite IHT2; eauto | erewrite IHT; eauto].
  destruct (PeanoNat.Nat.eqb j x) eqn:Heq; auto. simpl.
  destruct (le_lt_dec n n) eqn:Heq'; auto. lia.
  simpl. destruct (le_lt_dec n x) eqn:Heq; auto. lia.
Qed.

Lemma gt_n_lt_sn_absurd : forall {x n}, x > n -> x < S n -> False.
intros. lia.
Qed.

Lemma splice_Qual_open_succ : forall {d b fr n l j}, closed_Qual b n l d ↑ ->
  ([[j ~> ${fr}n ]]ᵈ d) ↑ᵈ n = [[j ~> ${fr}(S n) ]]ᵈ d.
intros. qual_destruct d. unfold_q.
#[local] Hint Resolve n_reflect_true : bdestruct.
bdestruct (bvs j); simpl; apply Q_lift_eq.
#[local] Remove Hints n_reflect_true : bdestruct.
all: Qcrush.
1,4: bdestruct (x <? n); intuition; bdestruct (x =? n); intuition; assert (x > n) by lia; intuition; exfalso; eauto using gt_n_lt_sn_absurd,Nat.lt_pred_lt_succ.
all: exfalso; eauto.
Qed.

Lemma splice_qual_open_succ : forall {d b fr n l j}, closed_qual b n l d ->
  ([[j ~> ${fr}n ]]ᵈ d) ↑ᵈ n = [[j ~> ${fr}(S n) ]]ᵈ d.
intros. apply Q_lift_closed' in H. eauto using splice_Qual_open_succ.
Qed.

Lemma splice_ty_open_succ : forall {T b fr n l j}, closed_ty b n l T -> ([[ j ~> $n ~ ${fr} n ]]ᵀ T) ↑ᵀ n = [[ j ~> $(S n) ~ ${fr} (S n) ]]ᵀ T.
  induction T; simpl; intros; inversion H; subst; auto;
    try solve [erewrite IHT1; eauto; erewrite IHT2; eauto | erewrite IHT; eauto]. simpl.
  destruct (le_lt_dec n x); auto. intuition.
  destruct (j =? x); auto. simpl. destruct (le_lt_dec n n); auto. intuition.
  erewrite splice_qual_open_succ; eauto.
  erewrite IHT1; eauto. erewrite IHT2; eauto.
  erewrite splice_qual_open_succ; eauto.
  erewrite IHT1; eauto. erewrite IHT2; eauto.
  erewrite splice_qual_open_succ; eauto.
  erewrite splice_qual_open_succ; eauto.
  erewrite IHT; eauto. erewrite splice_qual_open_succ; eauto. eapply closed_ty_monotone; eauto. all : lia.
Qed.

Lemma splice_qual_open'' : forall {k df d1 d2}, (d2 <~ᵈ df; d1) ↑ᵈ k = (d2 ↑ᵈ k) <~ᵈ (df ↑ᵈ k); (d1 ↑ᵈ k).
  intros. qual_destruct d2; qual_destruct d1; qual_destruct df; simpl.
unfold openq. unfold_q.
#[local] Hint Resolve n_reflect_true : bdestruct.
apply Q_lift_eq.
bdestruct (bvs 0); simpl.
#[local] Remove Hints n_reflect_true : bdestruct.
- destruct (n_or (n_diff bvs (n_one 0)) bvs1 1); Qcrush; bdestruct (x <? k); intuition; assert (x > k) by lia; intuition.
- destruct (bvs 1); Qcrush. bdestruct (x <? k); intuition; assert (x > k) by lia; intuition.
Qed.

Lemma splice_ty_open'' : forall {T U V k df d1}, (T <~ᵀ U ~ df; V ~ d1) ↑ᵀ k = (T ↑ᵀ k) <~ᵀ (U ↑ᵀ k) ~ (df ↑ᵈ k); (V ↑ᵀ k) ~ (d1 ↑ᵈ k).
  intros. unfold open_ty. repeat rewrite splice_ty_open_rec_ty. auto.
Qed.

Lemma splice_qual_qor_dist : forall {k q1 q2}, (q1 ⊔ q2) ↑ᵈ k = ((q1 ↑ᵈ k) ⊔ (q2 ↑ᵈ k)).
  intros. apply Q_lift_eq. Qcrush. bdestruct (x <? k); intuition. assert (x > k) by lia. Qcrush.
Qed.

Lemma subqual_splice_lr' : forall {i du df}, du ↑ᵈ i ⊑↑ df ↑ᵈ i <-> du ⊑↑ df.
  intros. intuition.
  - Qcrush. bdestruct (x <? i); intuition. specialize (H x); intuition. assert (S x > i) by lia. specialize (H (S x)); intuition.
  - Qcrush.
Qed.
#[global] Hint Resolve subqual_splice_lr' : core.

Lemma closed_ty_open2 : forall {f l d1 d2 T T1 T2}, closed_ty 2 f l T -> closed_ty 0 f l T1 -> closed_qual 0 f l d1 -> closed_ty 0 f l T2 -> closed_qual 0 f l d2 -> closed_ty 0 f l ([[1 ~> T1 ~ d1 ]]ᵀ ([[0 ~> T2 ~ d2 ]]ᵀ T)).
  intros. erewrite open_rec_ty_commute''; eauto. eapply closed_ty_open'; eauto. eapply closed_ty_open'; eauto.
Qed.

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

Lemma qstp_refl : forall {d}, forall {Γ Σ}, closed_qual 0 (‖Γ‖) (‖Σ‖) d -> qstp Γ Σ d d.
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
  - intuition. all: apply qstp_closed in H; intuition.
  - intuition. apply qstp_closed in H1; intuition. apply qstp_closed in H1; intuition.
  - intuition.
Qed.

Lemma stp_refl' : forall {n T}, ty_size T < n -> forall {Γ Σ}, closed_ty 0 (‖Γ‖) (‖Σ‖) T -> forall {d d'}, qstp Γ Σ d d' -> stp Γ Σ T d T d'.
  induction n; try lia; destruct T; simpl; intros Hsize Γ Σ Hc d d' Hstp; inversion Hc; subst.
  - (* TTOP *) constructor; auto.
  - (* TVarF refl *) apply indexr_var_some in H3. destruct H3. econstructor; eauto.
  - (* TVarB  *) inversion H3.
  - (* TAll *) inversion Hc. subst. eapply s_all; eauto. eapply IHn; eauto; try lia.
    eapply IHn; eauto.
    unfold open_ty'. unfold open_ty. rewrite <- open_ty_preserves_size. rewrite <- open_ty_preserves_size. lia.
    simpl. unfold open_ty'. unfold open_ty. rewrite open_rec_ty_commute; auto.
    eapply closed_ty_open' with (x:=S (S (‖Γ‖))); eauto.
    eapply closed_ty_open' with (x:=S (S (‖Γ‖))); eauto.
    eapply closed_ty_monotone; eauto. apply just_fv_closed. lia.
    rewrite <- just_fv_closed. lia.
     apply qstp_refl. unfold openq'. unfold openq. rewrite open_qual_commute; auto.
    simpl. eapply closed_qual_open'; eauto. eapply closed_qual_open'; eauto. all: apply Q_lift_closed; Qcrush.
  - (*TUnit*) constructor. auto.
  - (*TFun*) constructor; auto. apply IHn. lia. auto. apply qstp_refl. auto.
    apply IHn. unfold open_ty'. unfold open_ty. rewrite <- open_ty_preserves_size. rewrite <- open_ty_preserves_size. simpl. lia. simpl. unfold open_ty'. unfold open_ty. rewrite open_rec_ty_commute; auto.
    eapply closed_ty_open' with (x:=S (S (‖Γ‖))); eauto.
    eapply closed_ty_open' with (x:=S (S (‖Γ‖))); eauto.
    eapply closed_ty_monotone; eauto.
    rewrite <- just_fv_closed. lia.
    rewrite <- just_fv_closed. lia.
    apply qstp_refl. unfold openq'. unfold openq. rewrite open_qual_commute; auto.
    simpl. eapply closed_qual_open'; eauto. eapply closed_qual_open'; eauto. all: apply Q_lift_closed; Qcrush.
  - (*TRef*) constructor; auto.
    all : apply IHn; try lia; auto.
Qed.

Lemma stp_refl : forall {T Γ Σ}, closed_ty 0 (‖Γ‖) (‖Σ‖) T -> forall {d d'}, qstp Γ Σ d d' -> stp Γ Σ T d T d'.
  intros. eapply stp_refl'; eauto.
Qed.

Lemma indexr_splice_tenv : forall {Γ1 i Γ2 b U du},
    indexr i (Γ1 ++ Γ2) = Some ((bind_tm, b, U, du)) -> forall {k}, ‖Γ2‖ <= i ->
    indexr i (Γ1 ↑ᴳ k ++ Γ2) = Some ((bind_tm, b, U ↑ᵀ k, du ↑ᵈ k)).
  induction Γ1; intros; simpl in *; intuition. apply indexr_var_some' in H. lia.
  rewrite app_length in *. rewrite splice_tenv_length.
  destruct (Nat.eqb i (‖ Γ1 ‖ + ‖ Γ2 ‖)) eqn:Heq. inversion H. subst.
  simpl.  intuition.   apply IHΓ1; eauto.
Qed.

Lemma indexr_splice_ty_tenv : forall {Γ1 i Γ2 b U du},  indexr i (Γ1 ++ Γ2) = Some ((bind_ty, b, U, du)) ->
forall {k}, k <= i -> (length Γ2) <= i -> indexr i (splice_tenv k Γ1 ++ Γ2) = Some ((bind_ty, b, splice_ty k U, splice_qual k du)).
Proof.  induction Γ1; intros; simpl in *; intuition. apply indexr_var_some' in H. lia.
  rewrite app_length in *. rewrite splice_tenv_length.
  destruct (Nat.eqb i (‖ Γ1 ‖ + ‖ Γ2 ‖)) eqn:Heq.  inversion H. subst.
  simpl. auto. apply IHΓ1; eauto.
Qed.

Lemma splice_qual_glb_dist : forall {d1 d2 k}, (d1 ⊓ d2) ↑ᵈ k = d1 ↑ᵈ k ⊓ d2 ↑ᵈ k.
  intros. apply Q_lift_eq. Qcrush.
Qed.

Lemma splice_qual_lub_dist : forall {d1 d2 k}, (d1 ⊔ d2) ↑ᵈ k = (d1 ↑ᵈ k ⊔ d2 ↑ᵈ k).
  intros. apply Q_lift_eq. Qcrush. bdestruct (x <? k); intuition. bdestruct (x =? k); intuition. assert (x > k) by lia. Qcrush.
Qed.

Lemma splice_qual_mem_ge : forall {x k d1}, x >= k -> $(S x) ∈ᵥ d1 ↑ᵈ k -> $x ∈ᵥ d1.
  intros. Qcrush.
Qed.

Lemma splice_qual_mem_loc : forall {l k d1}, l ∈ₗ d1 ↑ᵈ k <-> l ∈ₗ d1.
  intros. Qcrush.
Qed.

Lemma splice_qual_not_mem : forall {k d1}, $k ∈ᵥ (d1 ↑ᵈ k) -> False.
  intros. Qcrush.
Qed.

Lemma splice_qual_just_fv_ge : forall {k j fr}, k <= j -> ${fr} j ↑ᵈ k = ${fr}(S j).
  intros. apply Q_lift_eq. Qcrush.
Qed.

Lemma splice_qual_just_fv_lt : forall {k j fr}, k > j -> ${fr} j ↑ᵈ k = ${fr}j.
  intros. apply Q_lift_eq. Qcrush.
Qed.

Lemma not_fresh_splice_iff : forall {df n}, ♦∉ df <-> ♦∉ df ↑ᵈ n.
  intros. Qcrush.
Qed.

Lemma fresh_splice_iff : forall {df n}, ♦∈ df <-> ♦∈ df ↑ᵈ n.
  intros. Qcrush.
Qed.

Lemma qstp_non_fresh : forall {Γ Σ q1 q2}, qstp Γ Σ q1 q2 -> ♦∉ q2 -> ♦∉ q1.
  intros. induction H; Qcrush.
Qed.

Lemma stp_qstp_inv : forall {Γ Σ T1 d1 T2 d2}, stp Γ Σ T1 d1 T2 d2 -> qstp Γ Σ d1 d2.
  intros Γ Σ T1 d1 T2 d2 HS. induction HS; intuition.
Qed.

Lemma stp_qual_irrelevance: forall {Γ Σ T1 d1 T2 d2}, stp Γ Σ T1 d1 T2 d2 ->
      forall {d3 d4}, qstp Γ Σ d3 d4 -> stp Γ Σ T1 d3 T2 d4.
Proof. intros Γ Σ T1 d1 T2 d2 Hstp. induction Hstp; intros; try econstructor; eauto.
       assert (stp Γ Σ T1 d1 T3 d2). { eapply s_trans'; eauto. }
       assert (qstp Γ Σ d4 d4). { apply qs_sq; auto. apply qstp_closed in H. intuition. }
       specialize(IHHstp1 d4 d4). intuition.
Qed.

Lemma weaken_qstp_gen : forall {Γ1 Γ2 Σ d1 d2},
    qstp (Γ1 ++ Γ2) Σ d1 d2 ->
    forall T', qstp ((Γ1 ↑ᴳ ‖Γ2‖) ++ T' :: Γ2) Σ (d1 ↑ᵈ ‖Γ2‖) (d2 ↑ᵈ ‖Γ2‖).
Proof.
  intros Γ1 Γ2 Σ d1 d2 HSTP. remember (Γ1 ++ Γ2) as Γ. generalize dependent Γ1. induction HSTP; intros Γ1 HeqG T'; subst.
  - constructor. apply subqual_splice_lr'. auto. apply splice_qual_closed'.
    rewrite app_length in *. rewrite splice_tenv_length. auto.
  - rewrite splice_qual_qor_dist. bdestruct (f <? ‖Γ2‖).
    * rewrite splice_qual_just_fv_lt; auto. erewrite @splice_qual_id with (d:=df).
      eapply qs_self; eauto. rewrite indexr_skips. rewrite indexr_skips in H. rewrite indexr_skip. eauto.
      1-3: simpl; lia. eapply closed_qual_monotone; eauto. lia.
    * rewrite splice_qual_just_fv_ge; auto.
      eapply qs_self; eauto. rewrite <- indexr_insert_ge; auto.
      eapply @indexr_splice_tenv with (k:=‖Γ2‖) in H; auto. simpl in H. eauto.
      eapply splice_qual_closed''; eauto.
  - rewrite splice_qual_qor_dist. bdestruct (f <? ‖Γ2‖).
    * rewrite splice_qual_just_fv_lt; auto. erewrite @splice_qual_id with (d:=df).
      eapply qs_self_all; eauto. rewrite indexr_skips. rewrite indexr_skips in H. rewrite indexr_skip. eauto.
      1-3: simpl; lia. eapply closed_qual_monotone; eauto. lia.
    * rewrite splice_qual_just_fv_ge; auto.
      eapply qs_self_all; eauto. rewrite <- indexr_insert_ge; auto.
      eapply @indexr_splice_tenv with (k:=‖Γ2‖) in H; auto. simpl in H. eauto.
      eapply splice_qual_closed''; eauto.
  - bdestruct (x <? ‖Γ2‖).
    * rewrite splice_qual_just_fv_lt; auto. erewrite @splice_qual_id with (d:=q1).
      eapply qs_qvar; eauto. rewrite indexr_skips. rewrite indexr_skips in H. rewrite indexr_skip. eauto.
      1-3: simpl; lia. eapply closed_qual_monotone; eauto. lia.
    * rewrite splice_qual_just_fv_ge; auto.
      eapply qs_qvar. rewrite <- indexr_insert_ge; auto.
      eapply @indexr_splice_tenv with (k:=‖Γ2‖) in H; auto. simpl in H. eauto.
      eapply splice_ty_closed''; eauto. eapply splice_qual_closed''; eauto.
      rewrite <- not_fresh_splice_iff. auto.
  - bdestruct (x <? ‖Γ2‖).
    * rewrite splice_qual_just_fv_lt; auto. erewrite @splice_qual_id with (d:=q1).
      eapply qs_qvar_ty; eauto. rewrite indexr_skips. rewrite indexr_skips in H. rewrite indexr_skip. eauto.
      1-3: simpl; lia. eapply closed_qual_monotone; eauto. lia.
    * rewrite splice_qual_just_fv_ge; auto.
      eapply qs_qvar_ty. rewrite <- indexr_insert_ge; auto.
      eapply @indexr_splice_ty_tenv with (k:=‖Γ2‖) in H; auto. simpl in H. eauto.
      eapply splice_ty_closed''; eauto. eapply splice_qual_closed''; eauto.
      rewrite <- not_fresh_splice_iff. auto.
  - repeat rewrite splice_qual_qor_dist. eapply qs_cong.
    eapply IHHSTP. auto. apply splice_qual_closed'. rewrite app_length in *. rewrite splice_tenv_length. auto.
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
  - apply qs_sq; auto. rewrite app_length. eapply closed_qual_monotone; eauto. lia.
  - eapply qs_self; eauto. erewrite app_length. eapply closed_qual_monotone; eauto. lia.
  - eapply qs_self_all; eauto. erewrite app_length. eapply closed_qual_monotone; eauto. lia.
  - eapply qs_qvar; eauto. all : erewrite app_length. eapply closed_ty_monotone; eauto. lia. eapply closed_qual_monotone; eauto. lia.
  - eapply qs_qvar_ty; eauto. all : erewrite app_length. eapply closed_ty_monotone; eauto. lia. eapply closed_qual_monotone; eauto. lia.
  - eapply qs_cong; eauto. rewrite app_length. eapply closed_qual_monotone; eauto. lia.
  - eapply qs_trans; eauto.
Qed.

Lemma weaken_qstp_store_ext : forall {Γ Σ d1 d2}, qstp Γ Σ d1 d2 -> forall {Σ'}, Σ' ⊇ Σ -> qstp Γ Σ' d1 d2.
  intros. unfold extends in H0. destruct H0. subst. apply weaken_qstp_store. auto.
Qed.

Lemma weaken_stp_gen : forall {Γ1 Γ2 Σ T1 d1 T2 d2},  stp (Γ1 ++ Γ2) Σ T1 d1 T2 d2 ->
    forall T', stp ((Γ1 ↑ᴳ ‖Γ2‖) ++ T' :: Γ2) Σ (T1 ↑ᵀ ‖Γ2‖) (d1 ↑ᵈ ‖Γ2‖) (T2 ↑ᵀ ‖Γ2‖) (d2 ↑ᵈ ‖Γ2‖).
Proof. intros Γ1 Γ2 Σ T1 d1 T2 d2  Hstp T'. remember (Γ1 ++ Γ2)  as Γ. generalize dependent Γ1.  induction Hstp. intros Γ1.
  - (* TTop *) intros. subst. constructor.  rewrite app_length in *. rewrite splice_tenv_length in *. simpl.
    replace (‖ Γ1 ‖ + S (‖ Γ2 ‖)) with (S ((‖ Γ1 ‖) +  (‖ Γ2 ‖))). eapply splice_ty_closed; eauto. lia.
    eapply weaken_qstp_gen. auto.
  - (* TVarF x *)  intros; subst. (* specialize (IHHstp Γ1).  intuition. *)  apply stp_refl.
    apply indexr_var_some' in H.  rewrite app_length. rewrite splice_tenv_length.
    replace (‖ Γ1 ‖ + ‖ T' :: Γ2 ‖) with (S ((‖ Γ1 ‖) +  (‖ Γ2 ‖))).
    assert (closed_ty 0 ((‖ Γ1 ‖) +  (‖ Γ2 ‖)) (length Σ) $x). { constructor. rewrite app_length in *.  auto. }
    intuition. eapply splice_ty_closed;  auto. simpl.  lia.
    eapply weaken_qstp_gen. intuition.
  - (* TVarF x trans *) intros; subst. simpl.  intuition. specialize (IHHstp Γ1).  intuition.
     destruct (le_lt_dec (‖ Γ2 ‖)  x) eqn:Heq.
    * (* |Γ2| <= x < |Γ1|+|Γ2| *)
      econstructor; eauto.
      rewrite <- indexr_insert_ge; eauto.
      apply @indexr_splice_ty_tenv with(Γ1 := Γ1)(i := x)(Γ2 := Γ2)(k := ‖ Γ2 ‖)(du := d0) in H; eauto.
      erewrite splice_ty_id  in H; eauto. eapply closed_ty_monotone; eauto. lia.
      erewrite  splice_ty_id in H1.  auto. eapply closed_ty_monotone; eauto. lia.
    * (* |Γ2| > x *)  econstructor; eauto.
      erewrite indexr_skips in H. erewrite indexr_skips;  auto. erewrite  indexr_skip.
      apply H. lia. simpl. lia. lia.
      erewrite splice_ty_id in H1; eauto.  eapply closed_ty_monotone; eauto.  lia.
  - (* TAll *) intros; subst.  assert (stp (Γ1 ++ Γ2) Σ (TAll d1 d2 T1 T2) d5 (TAll d3 d4 T3 T4) d6). { econstructor; eauto. }
    intuition.
    specialize (IHHstp1 Γ1).  specialize (IHHstp2 ((bind_ty, false, T3, d3) :: (bind_tm, true,(TAll d1 d2 T1 T2), {♦}) :: Γ1)). intuition.
    inversion H0. inversion H. subst. apply qstp_closed in H1 as H1'; intuition. econstructor; eauto; fold splice_ty.
    constructor. 5: constructor.
    1,2,5,6: apply splice_qual_closed'; auto; eapply closed_qual_monotone; eauto; rewrite app_length in*.
    5-8: apply splice_ty_closed'; auto; eapply closed_ty_monotone; eauto; rewrite app_length in*.

    1-8: rewrite app_length; erewrite splice_tenv_length; lia.

    eapply weaken_qstp_gen; eauto.
    erewrite app_length in *; eauto.
    repeat rewrite <- splice_ty_open'. repeat rewrite <- splice_qual_open'. simpl in H3.
    repeat rewrite idfun_inv in H3.
    repeat rewrite @open_ty'_len with (Γ:=(Γ1 ↑ᴳ ‖Γ2‖) ++ Γ2) (Γ':=Γ1++Γ2).
    repeat rewrite @openq'_len with (Γ:=(Γ1 ↑ᴳ ‖Γ2‖) ++ Γ2) (Γ':=Γ1++Γ2).
    replace ({♦} ↑ᵈ (‖ Γ2 ‖)) with ({♦}) in H3; auto.
    all: repeat rewrite app_length; rewrite splice_tenv_length; auto.
  - constructor. eapply weaken_qstp_gen. subst. auto.
  - intros. assert (stp Γ Σ (TRef q T1) d1 (TRef q T2) d2). { constructor; intuition. } subst.
    apply stp_closed in H1 as Hcl. intuition.
    inversion H2. inversion H3. subst.
    constructor. apply weaken_qstp_gen. subst; auto. 1,2: fold splice_ty. apply stp_closed in H1 as Hcl. intuition.
    1,2 : replace (T1 ↑ᵀ ‖Γ2‖) with T1; replace (T2 ↑ᵀ ‖Γ2‖) with T2; intuition.
    1-6 : erewrite splice_ty_id; eauto; eapply closed_ty_monotone; eauto; intuition.
    apply splice_qual_closed'. rewrite app_length in *. rewrite splice_tenv_length. auto.
  - assert (stp Γ Σ (TFun d1 d2 T1 T2) d5 (TFun d3 d4 T3 T4) d6). { constructor; intuition. } intros.
    subst. intuition. inversion H0; inversion H; subst. apply qstp_closed in H1 as Hcl. intuition.
    constructor; try fold splice_ty. 1-2: constructor.
    1,2,5,6 : apply splice_qual_closed'. 5-8 : apply splice_ty_closed'.
    1-8: rewrite app_length in *; rewrite splice_tenv_length in *; auto.
    apply weaken_qstp_gen. auto.
    specialize (IHHstp1 Γ1). intuition.
    specialize (IHHstp2 ((bind_tm, false,T3, d3) :: (bind_tm, true,(TFun d1 d2 T1 T2), {♦}) :: Γ1)). intuition.
    repeat rewrite <- splice_ty_open'. repeat rewrite <- splice_qual_open'. simpl in H5.
    repeat rewrite @open_ty'_len with (Γ:=(Γ1 ↑ᴳ ‖Γ2‖) ++ Γ2) (Γ':=Γ1++Γ2).
    repeat rewrite @openq'_len with (Γ:=(Γ1 ↑ᴳ ‖Γ2‖) ++ Γ2) (Γ':=Γ1++Γ2).
    replace ({♦} ↑ᵈ (‖ Γ2 ‖)) with ({♦}) in H5; auto.
    all: repeat rewrite app_length; rewrite splice_tenv_length; auto.
  - intros. specialize (IHHstp1 Γ1). specialize (IHHstp2 Γ1). intuition.
    eapply s_trans'; eauto.
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

Lemma narrowing_qstp_gen : forall{Γ1 b U du Γ2 Σ d1 d2},
    qstp (Γ1 ++ (bind_tm, b,U,du) :: Γ2) Σ d1 d2 -> (b = true -> (♦∈ du)) ->
    forall {V dv}, stp Γ2 Σ V dv U du ->
              qstp (Γ1 ++ (bind_tm, b,V,dv) :: Γ2) Σ d1 d2.
  intros Γ1 b U du Γ2 Σ d1 d2 HST Hb. remember (Γ1 ++ (bind_tm, b,U,du) :: Γ2) as Γ.
  generalize dependent Γ1; induction HST; intros; subst; intuition.
  - constructor. auto. rewrite app_length in *. simpl in *. auto.
  - eapply qs_self; eauto. destruct (PeanoNat.Nat.lt_trichotomy f (‖Γ2‖)) as [Hlen | [Hlen | Hlen] ].
    * rewrite indexr_skips. rewrite indexr_skips in H.
      rewrite indexr_skip.  rewrite indexr_skip in H. eauto. all: simpl; lia.
    * subst. rewrite indexr_skips in H; auto. rewrite indexr_head in H. inversion H. subst. intuition.
    * rewrite indexr_skips'; auto. rewrite indexr_skips' in H; auto.
  - eapply qs_self_all; eauto. destruct (PeanoNat.Nat.lt_trichotomy f (‖Γ2‖)) as [Hlen | [Hlen | Hlen] ].
    * rewrite indexr_skips. rewrite indexr_skips in H.
      rewrite indexr_skip.  rewrite indexr_skip in H. eauto. all: simpl; lia.
    * subst. rewrite indexr_skips in H; auto. rewrite indexr_head in H. inversion H. subst. intuition.
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
  - destruct (PeanoNat.Nat.lt_trichotomy x (‖Γ2‖)) as [Hlen | [Hlen | Hlen] ].
    * eapply qs_qvar_ty; eauto. rewrite indexr_skips. rewrite indexr_skips in H.
      rewrite indexr_skip.  rewrite indexr_skip in H. eauto. 1-4: simpl; lia.
    * subst.  pose (H':=H). rewrite indexr_skips in H'. rewrite indexr_head in H'. inversion H'. subst.
      simpl. lia.
    * eapply qs_qvar_ty; eauto. rewrite indexr_skips'; auto. rewrite indexr_skips' in H. eauto.
      simpl. lia.
  - eapply qs_cong; eauto. rewrite app_length in *. simpl in *. auto.
  - eapply qs_trans; eauto.
Qed.

Lemma narrowing_stp_gen : forall{Γ1 b U du Γ2 Σ T1 d1 T2 d2},
  stp (Γ1 ++ (bind_tm, b,U,du) :: Γ2) Σ T1 d1 T2 d2 -> (b = true -> (♦∈ du)) ->
  forall {V dv}, (stp Γ2 Σ V dv U du) -> stp (Γ1 ++ (bind_tm, b,V,dv) :: Γ2) Σ T1 d1 T2 d2.
Proof. intros Γ1 b U du Γ2 Σ T1 d1 T2 d2 HST Hb. remember (Γ1 ++ (bind_tm, b,U,du) :: Γ2) as Γ.
  generalize dependent Γ1; induction HST; intros; intuition.
  - (* TTop *) subst. constructor. rewrite app_length in *.  simpl in *. intuition. eapply narrowing_qstp_gen; eauto.
  - (* TVarF x refl *) subst. destruct (Nat.eqb x (length Γ2)) eqn: Heqn.
     + eapply s_tvar_refl; eauto. apply Nat.eqb_eq in Heqn. subst. eapply indexr_insert.
       eapply narrowing_qstp_gen; eauto.
     + eapply s_tvar_refl; eauto.
      eapply indexr_var_same. assumption. eassumption. eapply narrowing_qstp_gen; eauto.
  - (* TVarF x trans *) subst. destruct (Nat.eqb x (length Γ2)) eqn: Heqn.
       specialize (IHHST Γ1).  intuition.  specialize (H2 V dv).  intuition.
    +  eapply s_tvar_trans. apply Nat.eqb_eq in  Heqn; subst.
       erewrite  indexr_skips in  H; eauto. erewrite indexr_head in H.  inversion H. apply H0.
       auto.
    +  eapply s_tvar_trans.  eapply indexr_var_same.  assumption. eassumption. apply H0. auto.
  - (* TAll *) rewrite HeqΓ in *. econstructor.
    subst. rewrite app_length in *. simpl in *. auto.
    subst. rewrite app_length in *. simpl in *. auto.
    eapply narrowing_qstp_gen; subst; eauto. eapply IHHST1; eauto.
    unfold open_ty' in *. unfold open_ty in *. unfold openq' in *. unfold openq in *.
    rewrite app_length in *. simpl in *.
    repeat rewrite app_comm_cons.
    specialize (IHHST2 ((bind_ty, false, T3, d3) :: (bind_tm, true, TAll d1 d2 T1 T2, {♦}) :: Γ1)). intuition.
  - subst. constructor. eapply narrowing_qstp_gen; eauto.
  - subst. constructor. eapply narrowing_qstp_gen; eauto. auto. auto.
    rewrite app_length in *. simpl in *. auto.
  - rewrite HeqΓ in *. constructor.
    subst. rewrite app_length in *. simpl in *. auto.
    subst. rewrite app_length in *. simpl in *. auto.
    eapply narrowing_qstp_gen; subst; eauto. eapply IHHST1; eauto.
    unfold open_ty' in *. unfold openq' in *.
    rewrite app_length in *. simpl in *.
    repeat rewrite app_comm_cons.
    eapply IHHST2; eauto.
  - subst. specialize (IHHST1 Γ1).  specialize (IHHST2 Γ1). intuition.
    specialize (H0 V dv).  specialize (H1 V dv). intuition.  eapply s_trans'; eauto.
  Unshelve. auto.
Qed.

Lemma narrowing_stp : forall{b U du Γ Σ T1 d1 T2 d2}, stp ((bind_tm, b,U,du) :: Γ) Σ T1 d1 T2 d2 -> (b = true -> (♦∈ du)) ->
    forall {V dv}, stp Γ Σ V dv U du -> stp ((bind_tm, b,V,dv) :: Γ) Σ T1 d1 T2 d2.
  intros. specialize (@narrowing_stp_gen [] b U du Γ Σ T1 d1 T2 d2) as narrow. simpl in *. eapply narrow; eauto.
Qed.

Lemma narrowing_qstp_ty_gen : forall{Γ1 U du Γ2 Σ d1 d2},
    qstp (Γ1 ++ (bind_ty, false,U,du) :: Γ2) Σ d1 d2 ->
    forall {V dv}, stp Γ2 Σ V dv U du ->
            qstp (Γ1 ++ (bind_ty, false,V,dv) :: Γ2) Σ d1 d2.
  intros Γ1 U du Γ2 Σ d1 d2 HST Hb. remember (Γ1 ++ (bind_ty, false,U,du) :: Γ2) as Γ.
  generalize dependent Γ1; induction HST; intros; subst; intuition.
  - constructor. auto. rewrite app_length in *. simpl in *. auto.
  - eapply qs_self; eauto. destruct (PeanoNat.Nat.lt_trichotomy f (‖Γ2‖)) as [Hlen | [Hlen | Hlen] ].
    * rewrite indexr_skips. rewrite indexr_skips in H.
      rewrite indexr_skip.  rewrite indexr_skip in H. eauto. all: simpl; lia.
    * subst. rewrite indexr_skips in H; auto. rewrite indexr_head in H. inversion H.
    * rewrite indexr_skips'; auto. rewrite indexr_skips' in H; auto.
  - eapply qs_self_all; eauto. destruct (PeanoNat.Nat.lt_trichotomy f (‖Γ2‖)) as [Hlen | [Hlen | Hlen] ].
    * rewrite indexr_skips. rewrite indexr_skips in H.
      rewrite indexr_skip.  rewrite indexr_skip in H. eauto. all: simpl; lia.
    * subst. rewrite indexr_skips in H; auto. rewrite indexr_head in H. inversion H.
    * rewrite indexr_skips'; auto. rewrite indexr_skips' in H; auto.
  - destruct (PeanoNat.Nat.lt_trichotomy x (‖Γ2‖)) as [Hlen | [Hlen | Hlen] ].
    * eapply qs_qvar; eauto. rewrite indexr_skips. rewrite indexr_skips in H.
      rewrite indexr_skip.  rewrite indexr_skip in H. eauto. 1-4: simpl; lia.
    * subst.  pose (H':=H). rewrite indexr_skips in H'. rewrite indexr_head in H'. inversion H'.
      simpl. lia.
    * eapply qs_qvar; eauto. rewrite indexr_skips'; auto. rewrite indexr_skips' in H. eauto.
      simpl. lia.
  - destruct (PeanoNat.Nat.lt_trichotomy x (‖Γ2‖)) as [Hlen | [Hlen | Hlen] ].
    * eapply qs_qvar_ty; eauto. rewrite indexr_skips. rewrite indexr_skips in H.
      rewrite indexr_skip.  rewrite indexr_skip in H. apply H. eauto. 1-4: simpl; lia.
    * subst. pose (H':=H). rewrite indexr_skips in H'. rewrite indexr_head in H'. inversion H'.
      subst.  eapply qs_trans. eapply qs_qvar_ty.
      rewrite indexr_skips; auto. apply indexr_head.
      1,2 : apply stp_closed in H3; intuition.
      apply stp_qstp_inv in H3. eapply qstp_non_fresh; eauto.
      apply stp_qstp_inv in H3. eapply weaken_qstp'. eapply weaken_qstp. auto. auto.
    * eapply qs_qvar_ty; eauto. rewrite indexr_skips'; auto. rewrite indexr_skips' in H. eauto.
      simpl. lia.
  - eapply qs_cong; eauto. rewrite app_length in *. simpl in *. auto.
  - specialize (IHHST1 Γ1). intuition. specialize (H0 dv). intuition.
    specialize (IHHST2 Γ1). intuition. specialize (H0 dv). intuition.
    eapply qs_trans; eauto.
Qed.

Lemma weaken_stp_store : forall {Σ Γ T1 d1 T2 d2}, stp Γ Σ T1 d1 T2 d2 -> forall Σ', stp Γ (Σ' ++ Σ) T1 d1 T2 d2.
Proof. intros Σ Γ T1 d1 T2 d2 HSTP. induction HSTP; intros.
  + constructor; auto. eapply closed_ty_monotone; eauto. rewrite app_length. lia. apply weaken_qstp_store. auto.
  + econstructor; eauto. apply weaken_qstp_store. auto.
  + econstructor; eauto. eapply closed_ty_monotone; eauto. rewrite app_length. lia.
  + econstructor; eauto. eapply closed_ty_monotone in H; eauto. rewrite app_length. lia.
    eapply closed_ty_monotone in H0; eauto. rewrite app_length. lia.
    eapply weaken_qstp_store. intuition.
  + constructor. apply weaken_qstp_store. auto.
  + constructor; auto. apply weaken_qstp_store. auto. rewrite app_length. eapply closed_qual_monotone; eauto. lia.
  + constructor; auto. 1,2 : rewrite app_length; eapply closed_ty_monotone; eauto; lia.
    apply weaken_qstp_store. auto.
  + specialize (IHHSTP1 Σ'). specialize (IHHSTP2 Σ'). eapply s_trans' in IHHSTP2; eauto.
Qed.

Lemma weaken_stp_store_ext : forall {Σ Γ T1 d1 T2 d2}, stp Γ Σ T1 d1 T2 d2 -> forall {Σ'}, Σ' ⊇ Σ ->  stp Γ Σ' T1 d1 T2 d2.
  intros. unfold extends in H0. destruct H0. subst. apply weaken_stp_store. auto.
Qed.

Lemma stp_shrink_var : forall {Γ Σ T1 d1 T2 d2}, stp Γ Σ T1 d1 T2 d2 -> forall {fr x}, x < ‖Γ‖ -> stp Γ Σ T1 ${fr}x T2 ${fr}x.
  intros. eapply stp_qual_irrelevance; eauto. apply qs_sq; auto. apply just_fv_closed. auto.
Qed.

Lemma s_trans : forall {Γ Σ T1 d1 T2 d2 T3 d3}, stp Γ Σ T1 d1 T2 d2 -> stp Γ Σ T2 d2 T3 d3 -> stp Γ Σ T1 d1 T3 d3.
Proof.
  intros.
  assert (stp Γ Σ T2 d2 T3 d2). { eapply stp_qual_irrelevance; eauto. apply qs_sq; auto. apply stp_closed in H. intuition. }
  assert (stp Γ Σ T1 d1 T3 d2). { eapply s_trans'; eauto. }
  eapply stp_qual_irrelevance; eauto. apply stp_qstp_inv in H. apply stp_qstp_inv in H0. eapply qs_trans; eauto.
Qed.

Lemma narrowing_stp_ty_gen : forall{Γ1 U du Γ2 Σ T1 d1 T2 d2},
      stp (Γ1 ++ ((bind_ty, false, U, du)) :: Γ2) Σ T1 d1 T2 d2 ->
      forall {V dv }, closed_ty  0 0 (‖ Σ ‖) V -> closed_qual  0 0 (‖ Σ ‖) dv ->
      (stp Γ2 Σ V dv U du) ->
      stp (Γ1 ++ ((bind_ty, false, V, dv)) :: Γ2) Σ T1 d1 T2 d2.
Proof. intros Γ1 U du Γ2 Σ T1 d1 T2 d2 HST. remember (Γ1 ++ ((bind_ty, false, U, du)) :: Γ2) as Γ.
  generalize dependent Γ1; induction HST; intros; intuition.
  - (* TTop *) subst. constructor. rewrite app_length in *.  simpl in *. intuition.
    eapply  narrowing_qstp_ty_gen; eauto.
  - (* TVarF x refl *) subst. destruct (Nat.eqb x  (‖ Γ2 ‖)) eqn: Heqn.
     + eapply s_tvar_refl; eauto. simpl in Heqn. apply Nat.eqb_eq in Heqn. subst. eapply indexr_insert.
       eapply narrowing_qstp_ty_gen; eauto.
     + eapply s_tvar_refl; eauto.  eapply indexr_var_same. assumption. eassumption. eapply narrowing_qstp_ty_gen; eauto.

  - (* TVarF x trans *) assert (stp Γ Σ $x d1 T2 d2). {
         econstructor; eauto.
       }
      subst. destruct (Nat.eqb x  (‖ Γ2 ‖)) eqn: Heqn.
     + apply Nat.eqb_eq  in  Heqn. subst.

       erewrite indexr_skips in H. erewrite indexr_head in H. inversion H. subst.
     econstructor; eauto.
     assert (indexr (‖ Γ2 ‖) (Γ1 ++ (bind_ty, false, V, dv) :: Γ2) = Some ((bind_ty, false, V, dv))). {
       erewrite indexr_skips. erewrite indexr_head. auto. simpl. lia.
     }
     apply H5.
     specialize (IHHST Γ1); intuition. specialize(H5 V dv); intuition.
     assert (stp (Γ1 ++ (bind_ty, false, V, dv) :: Γ2) Σ V dv T1 d0). {
       eapply weaken_stp'; eauto. eapply weaken_stp; eauto.
     }

     apply stp_qstp_inv in H6 as H6'.
     assert (stp (Γ1 ++ (bind_ty, false, V, dv) :: Γ2) Σ V d1 T1 d1). {
       assert (qstp (Γ1 ++ (bind_ty, false, V, dv) :: Γ2) Σ d1 d1). {
         apply qstp_refl; auto. apply qstp_closed in H6'; intuition.
       }
       eapply stp_qual_irrelevance; eauto.
     }
     eapply s_trans; eauto.  simpl. lia.
    +  specialize (IHHST Γ1). intuition.  specialize (H5 V dv). intuition.
       eapply s_tvar_trans.
       eapply indexr_var_same; eauto. auto. auto.

  - (* TAll *) rewrite HeqΓ in *. econstructor.
    subst. rewrite app_length in *. simpl in *. auto.
    subst. rewrite app_length in *. simpl in *. auto.
    eapply narrowing_qstp_ty_gen; subst; eauto. eapply IHHST1; eauto.
    specialize (IHHST2 ((bind_ty, false, T3, d3) :: (bind_tm, true, TAll d1 d2 T1 T2, {♦}) :: Γ1 )). intuition.
    specialize (H5 V dv). intuition.
    unfold open_ty' in *. unfold openq' in *.
    rewrite app_length in *. simpl in *.
    repeat rewrite app_comm_cons. auto.
  - (* TUnit *) subst. constructor. eapply narrowing_qstp_ty_gen; eauto.
  - (* TRef *) subst. constructor. eapply narrowing_qstp_ty_gen; eauto. auto. auto.
    rewrite app_length in *. simpl in *. auto.
  - (* TFUN *)  rewrite HeqΓ in *. constructor.
    subst. rewrite app_length in *. simpl in *. auto.
    subst. rewrite app_length in *. simpl in *. auto.
    eapply narrowing_qstp_ty_gen; subst; eauto. eapply IHHST1; eauto.
    unfold open_ty' in *. unfold openq' in *.
    rewrite app_length in *. simpl in *.
    repeat rewrite app_comm_cons.
    eapply IHHST2; eauto.
  - subst. specialize (IHHST1 Γ1).  specialize (IHHST2 Γ1). intuition.
    specialize (H2 V dv). specialize (H3 V dv). intuition.  eapply s_trans'; eauto.
Qed.

Lemma narrowing_stp_ty : forall{U du Γ Σ T1 d1 T2 d2}, stp (((bind_ty, false, U, du)) :: Γ) Σ T1 d1 T2 d2 ->
  forall {V dv}, closed_ty 0 0 (length Σ) V -> closed_Qual 0 0 (length Σ) dv↑ ->  stp Γ Σ V dv U du ->
    stp (((bind_ty, false, V, dv)) :: Γ) Σ T1 d1 T2 d2.
   intros. specialize (@narrowing_stp_ty_gen [] U du Γ Σ T1 d1 T2 d2) as narrow. simpl in narrow. intuition.
Qed.

Lemma stp_scale_qor : forall {Γ Σ T1 d1 T2 d2}, stp Γ Σ T1 d1 T2 d2 -> forall {q}, closed_Qual 0 (‖Γ‖) (‖Σ‖) q↑ -> stp Γ Σ T1 (d1 ⊔ q) T2 (d2 ⊔ q).
  intros. eapply stp_qual_irrelevance; eauto. apply stp_qstp_inv in H. replace (d1 ⊔ q) with (q ⊔ d1). replace (d2 ⊔ q) with (q ⊔ d2). eauto.
all: apply Q_lift_eq; Qcrush.
Qed.

Lemma qqplus_fresh : forall {d d'}, ♦∈ d -> (d ⋓ d') = (d ⊔ d').
intros. unfold qqplus, qfresh in *. apply Is_true_eq_true in H. rewrite H. auto.
Qed.

Lemma stp_scale_qqplus : forall {Γ Σ T1 d1 T2 d2}, stp Γ Σ T1 d1 T2 d2 -> forall {d}, closed_Qual 0 (‖Γ‖) (‖Σ‖) d↑ -> stp Γ Σ T1 (d1 ⋓ d) T2 (d2 ⋓ d).
#[local] Hint Resolve is_true_reflect : bdestruct.
  intros. bdestruct (♦∈? d1); bdestruct (♦∈? d2).
#[local] Remove Hints is_true_reflect : bdestruct.
  - repeat rewrite qqplus_fresh; auto. apply stp_scale_qor; auto.
  - apply stp_qstp_inv in H. specialize (qstp_non_fresh H H2) as Hc. unfold_q. contradiction.
  - rewrite @qqplus_fresh with (d:=d2); auto. unfold qqplus. apply Is_true_eq_false in H1. rewrite H1.
    eapply s_trans; eauto. apply stp_refl. apply stp_closed in H. intuition.
    apply qs_sq. Qcrush. apply stp_closed in H. apply closed_Qual_qor; intuition.
  - unfold qqplus. apply Is_true_eq_false in H1,H2. rewrite H1,H2. auto.
Qed.

Lemma saturated_cons : forall {Γ Σ q}, saturated Γ Σ q -> forall {b T q'}, saturated ((bind_tm, b, T, q') :: Γ) Σ q.
intros. unfold saturated in *. intuition. unfold tenv_saturated in *. intros. apply H0 in H. inversion H.
  * econstructor; eauto. rewrite indexr_skip; eauto. apply indexr_var_some' in H2. lia.
  * subst. eapply sat_tvar; eauto. rewrite indexr_skip; eauto. apply indexr_var_some' in H2. lia.
Qed.

Lemma saturated_ty_cons : forall {Γ Σ q}, saturated Γ Σ q -> forall {b T q'}, saturated ((bind_ty, b, T, q') :: Γ) Σ q.
intros. unfold saturated in *. intuition. unfold tenv_saturated in *. intros. apply H0 in H. inversion H.
  * econstructor; eauto. rewrite indexr_skip; eauto. apply indexr_var_some' in H2. lia.
  * subst. eapply sat_tvar; eauto. rewrite indexr_skip; eauto. apply indexr_var_some' in H2. lia.
Qed.

Lemma senv_saturated_conss : forall {Σ q}, senv_saturated Σ q -> forall {T q'}, senv_saturated ((T, q') :: Σ) q.
  intros. unfold senv_saturated. intros. apply H in H0. inversion H0. econstructor. rewrite indexr_skip.
  eauto. apply indexr_var_some' in H1. lia. all : auto.
Qed.
#[global] Hint Resolve senv_saturated_conss : core.

Lemma saturated_conss : forall {Γ Σ q}, saturated Γ Σ q -> forall {T q'}, saturated Γ ((T, q') :: Σ) q.
  intros. unfold saturated in *. intuition. unfold tenv_saturated. intros. apply H0 in H. inversion H.
  * econstructor; eauto.
  * eapply sat_tvar; eauto.
Qed.

Lemma wf_senv_prop : forall {Σ}, wf_senv Σ -> forall l T q, indexr l Σ = Some (T, q) -> (closed_ty 0 0 l T /\ closed_qual 0 0 l q /\ senv_saturated Σ q).
  intros Σ Hwf. induction Hwf; intros. simpl in H. discriminate. destruct (l =? ‖Σ‖) eqn:Heq.
  - simpl in H2. rewrite Heq in H2. inversion H2. subst. apply Nat.eqb_eq in Heq. subst. intuition.
  - simpl in H2. rewrite Heq in H2. apply IHHwf in H2. intuition.
Qed.

Lemma senv_saturated_empty : forall {Σ fr}, senv_saturated Σ ∅{ fr }.
  intros. unfold senv_saturated. intros. Qcrush.
Qed.
#[global] Hint Resolve senv_saturated_empty : core.

Lemma tenv_saturated_empty : forall {Γ Σ fr}, tenv_saturated Γ Σ ∅{ fr }.
  intros. unfold tenv_saturated. intros. Qcrush.
Qed.
#[global] Hint Resolve tenv_saturated_empty : core.

Lemma saturated_empty : forall {Γ Σ fr}, saturated Γ Σ ∅{ fr }.
  intros. unfold saturated. intuition.
Qed.
#[global] Hint Resolve saturated_empty : core.

Lemma senv_saturated_just_fv : forall {Σ fr x}, senv_saturated Σ ${fr}x.
  intros. unfold senv_saturated. intros. Qcrush.
Qed.
#[global] Hint Resolve senv_saturated_just_fv : core.

Lemma tenv_saturated_empty_tenv : forall {Σ q}, closed_Qual 0 0 (‖Σ‖) q↑ -> tenv_saturated [] Σ q.
  intros. unfold tenv_saturated. intros. exfalso. Qcrush. eauto.
Qed.
#[global] Hint Resolve tenv_saturated_empty_tenv : core.

Lemma senv_saturated_open_qual : forall {Σ d1 d2}, senv_saturated Σ d1 -> forall {k}, senv_saturated Σ ([[ k ~> ∅ ]]ᵈ d2) -> senv_saturated Σ ([[ k ~> d1 ]]ᵈ d2).
intros. qual_destruct d1. qual_destruct d2. unfold open_qual in *; unfold_q.
#[local] Hint Resolve n_reflect_true : bdestruct.
  bdestruct (bvs0 k); intuition.
#[local] Remove Hints n_reflect_true : bdestruct.
  repeat rewrite empty_union_right in H0. rewrite orb_false_r in H0.
  unfold senv_saturated in *. intros. simpl in *. specialize (H l). specialize (H0 l). nlift.
#[local] Hint Resolve n_reflect_true : bdestruct.
bdestruct (lcs l); intuition.
#[local] Remove Hints n_reflect_true : bdestruct.
  - inversion H4. econstructor; eauto. eapply Subq_trans; eauto. Qcrush.
  - assert (N_or (N_lift lcs0) N_empty l). Qcrush. intuition. inversion H5. econstructor; eauto. eapply Subq_trans; eauto. Qcrush.
Qed.

Lemma senv_saturated_openq : forall {f Σ df d1 d2},
    senv_saturated Σ df -> closed_qual 0 f (‖Σ‖) df ->
    senv_saturated Σ d1 -> closed_qual 0 f (‖Σ‖) d1 -> senv_saturated Σ (openq ∅ ∅ d2) -> senv_saturated Σ (openq df d1 d2).
    intros. unfold openq in *. apply senv_saturated_open_qual; auto.
    erewrite open_qual_commute''; eauto. erewrite open_qual_commute'' in H3; eauto.
    eapply senv_saturated_open_qual; auto. Unshelve. all: apply 0.
Qed.

Lemma saturated_senv_qor : forall {Σ q1 q2}, senv_saturated Σ q1 -> senv_saturated Σ q2 -> senv_saturated Σ (q1 ⊔ q2).
  intros. unfold senv_saturated in *. intros. specialize (H l). specialize (H0 l).
  qual_destruct q1. qual_destruct q2. simpl in *. nlift.
#[local] Hint Resolve n_reflect_true : bdestruct.
bdestruct (lcs l); intuition.
#[local] Remove Hints n_reflect_true : bdestruct.
  - inversion H3. econstructor; eauto. eapply Subq_trans; eauto. Qcrush.
  - assert (N_lift lcs0 l). Qcrush. intuition. inversion H4. econstructor; eauto. eapply Subq_trans; eauto. Qcrush.
Qed.
#[global] Hint Resolve saturated_senv_qor : core.

Lemma saturated_qor : forall {Γ Σ q1 q2}, saturated Γ Σ q1 -> saturated Γ Σ q2 -> saturated Γ Σ (q1 ⊔ q2).
  intros. inversion H. inversion H0. constructor; auto.
  unfold tenv_saturated in *. intros. specialize (H1 x). specialize (H3 x).
#[local] Hint Resolve qmem_reflect : bdestruct.
bdestruct ($ x ∈?ᵥ q1); intuition.
#[local] Remove Hints qmem_reflect : bdestruct.
  - inversion H7.
    + eapply sat_var; eauto. eapply Subq_trans; eauto. Qcrush.
    + eapply sat_tvar; eauto. eapply Subq_trans; eauto. Qcrush.
  - assert ($ x ∈ᵥ q2). Qcrush. intuition. inversion H8.
    + eapply sat_var; eauto. eapply Subq_trans; eauto. Qcrush.
    + eapply sat_tvar; eauto. eapply Subq_trans; eauto. Qcrush.
Qed.
#[global] Hint Resolve saturated_qor : core.

Lemma senv_saturated_qqplus : forall {Σ q1 q2}, senv_saturated Σ q1 -> senv_saturated Σ q2 -> senv_saturated Σ (q1 ⋓ q2).
  intros. qual_destruct q1. destruct fr; simpl; auto.
Qed.
#[global] Hint Resolve senv_saturated_qqplus : core.

Lemma saturated_qqplus : forall {Γ Σ q1 q2}, saturated Γ Σ q1 -> saturated Γ Σ q2 -> saturated Γ Σ (q1 ⋓ q2).
  intros. qual_destruct q1. destruct fr; simpl; auto.
Qed.
#[global] Hint Resolve saturated_qqplus : core.

Lemma saturated_senv_qglb : forall {Σ q1 q2}, senv_saturated Σ q1 -> senv_saturated Σ q2 -> senv_saturated Σ (q1 ⊓ q2).
  intros. unfold senv_saturated in *. intros. specialize (H l). specialize (H0 l).
  assert (l ∈ₗ q1). Qcrush. assert (l ∈ₗ q2). Qcrush. intuition.
  inversion H. inversion H4. rewrite H0 in H7. inversion H7. subst. econstructor; eauto. rewrite qor_qand_dist_r. Qcrush.
Qed.
#[global] Hint Resolve saturated_senv_qglb : core.

Lemma saturated_qglb : forall {Γ Σ q1 q2}, saturated Γ Σ q1 -> saturated Γ Σ q2 -> saturated Γ Σ (q1 ⊓ q2).
  intros. inversion H. inversion H0. constructor; auto. unfold tenv_saturated, senv_saturated in *. intros. assert ($x ∈ᵥ q1). Qcrush. assert ($x ∈ᵥ q2). Qcrush.

  specialize (H1 x). specialize (H3 x). intuition.
  inversion H8; inversion H1.
  * eapply sat_var; eauto. rewrite H3 in H11. inversion H11. subst. Qcrush.
  * rewrite H3 in H11. discriminate.
  * rewrite H3 in H11. discriminate.
  * eapply sat_tvar; eauto. rewrite H3 in H11. inversion H11. subst. Qcrush.
Qed.
#[global] Hint Resolve saturated_qglb : core.

Lemma weaken_store_senv_saturated : forall {Σ q}, senv_saturated Σ q -> forall {Σ'}, Σ' ⊇ Σ -> senv_saturated Σ' q.
  intros. unfold senv_saturated. intros.
  apply H in H1. inversion H1. econstructor; eauto. unfold extends in H0. destruct H0 as [Σ'' Hs].
  subst. rewrite indexr_skips. eauto. apply indexr_var_some' in H2. lia.
Qed.

Lemma weaken_store_tenv_saturated : forall {Γ Σ q}, tenv_saturated Γ Σ q -> forall {Σ'}, Σ' ⊇ Σ -> tenv_saturated Γ Σ' q.
  intros. unfold tenv_saturated. intros. apply H in H1. inversion H1.
  * econstructor; eauto.
  * eapply sat_tvar; eauto.
Qed.

Lemma weaken_store_saturated : forall {Γ Σ q}, saturated Γ Σ q -> forall {Σ'}, Σ' ⊇ Σ -> saturated Γ Σ' q.
  intros. inversion H. constructor. eapply weaken_store_tenv_saturated; eauto. eapply weaken_store_senv_saturated; eauto.
Qed.

Lemma closed_Qual_open2 : forall {f l d1 d2 d}, closed_Qual 2 f l d ↑ -> closed_Qual 0 f l d1 ↑ -> closed_Qual 0 f l d2 ↑ -> closed_Qual 0 f l ([[1 ~> d1 ]]ᵈ ([[0 ~> d2 ]]ᵈ d)) ↑.
  intros. apply Q_lift_closed'. erewrite open_qual_commute''; eauto.
Qed.

Fixpoint has_type_closed  {Γ φ Σ t T d} (ht : has_type Γ φ Σ t T d) :
  closed_Qual 0 (‖Γ‖) (‖Σ‖) φ↑ /\
  closed_tm 0 (‖Γ‖) (‖Σ‖) t /\
  closed_ty 0 (‖Γ‖) (‖Σ‖) T /\
  closed_Qual 0 (‖Γ‖) (‖Σ‖) d↑.
Proof.
  destruct ht; intuition; try apply has_type_closed in ht; try apply has_type_closed in ht1;
  try apply has_type_closed in ht2; intuition; eauto;
    try match goal with
    | [ H : closed_ty _ _ _ (_ _ _ _ ?T)  |- closed_ty _ _ _ (?T <~ᵀ _ ~ _; _ ~ _) ] =>
       inversion H; subst; unfold open_ty; eapply closed_ty_open2; eauto
    | [ H : closed_ty _ _ _ (_ _ ?q _ _)  |- closed_Qual _ _ _ (?q <~ᵈ _ ; _ )↑ ] =>
       inversion H; subst; unfold openq; eapply closed_qual_open2; eauto
    end.
  - constructor. apply indexr_var_some' in H. auto.
  - apply indexr_var_some' in H. eapply closed_ty_monotone; eauto. lia.
  - constructor. apply indexr_var_some' in H0. auto.
  - Qcrush.
  - inversion H3. subst. eapply closed_ty_monotone; eauto; lia.
  - apply stp_closed in H. intuition.
Qed.

Lemma qstp_empty : forall {Σ q1 q2}, qstp [] Σ q1 q2 -> q1 ⊑↑ q2.
  intros. remember [] as Γ. induction H; subst; auto; try solve [simpl in H; discriminate]. auto.
  intuition. Qcrush.
  intuition. eapply Subq_trans; eauto.
Qed.

Lemma open_qual_subqual : forall {d1 d2 φ}, d1 ⊑↑ φ -> forall {k}, ([[ k ~> ∅ ]]ᵈ d2) ⊑↑ φ -> ([[ k ~> d1 ]]ᵈ d2) ⊑↑ φ.
  intros. qual_destruct d2.
#[local] Hint Resolve n_reflect_true : bdestruct.
unfold_q. bdestruct (bvs k); simpl; auto. Qcrush.
#[local] Remove Hints n_reflect_true : bdestruct.
Qed.

Lemma openq_subqual : forall {df d1 d2 φ f l}, closed_Qual 0 f l φ↑ -> df ⊑↑ φ -> d1 ⊑↑ φ -> d2 <~ᵈ ∅; ∅ ⊑↑ φ -> d2 <~ᵈ df; d1 ⊑↑ φ.
  intros. unfold openq in *. apply open_qual_subqual; auto. erewrite open_qual_commute''; eauto.
  erewrite open_qual_commute'' in H2; eauto. apply open_qual_subqual; auto.
  Unshelve. all : apply 0.
Qed.

Fixpoint has_type_filter {Γ φ Σ t T d} (ht : has_type Γ φ Σ t T d) {struct ht} : d ⊑↑ φ.
  destruct ht; intuition.
  1-4: try specialize (has_type_closed ht) as Hc; try specialize (has_type_closed ht1) as Hc; intuition; eapply openq_subqual; eauto.
  Qcrush.
  apply has_type_filter in ht. apply Qor_bound; auto.
Qed.

Lemma bound_vars_untypable : forall {Γ φ Σ T d i}, has_type Γ φ Σ #i T d -> False.
  intros Γ φ Σ T d i HT. remember (tvar #i) as t. induction HT; try discriminate; intuition.
Qed.

Lemma splice_senv_saturated : forall {Σ d1}, senv_saturated Σ d1 -> forall {k}, senv_saturated Σ (d1 ↑ᵈ k).
  intros. unfold senv_saturated in *. qual_destruct d1. simpl in *. intros. apply H in H0.
  inversion H0. econstructor; eauto. Qcrush. bdestruct (x=?k). exfalso; eauto. bdestruct (x<?k); eauto.
Qed.
#[global] Hint Resolve splice_senv_saturated : core.

Lemma weaken_tenv_saturated : forall {Γ1 Γ2 Σ d1},
    tenv_saturated (Γ1 ++ Γ2) Σ d1 -> forall X, tenv_saturated ((Γ1 ↑ᴳ ‖Γ2‖) ++ X :: Γ2) Σ (d1 ↑ᵈ ‖Γ2‖).
  intros. unfold tenv_saturated in *. intros. bdestruct (x <? ‖Γ2‖).
  - apply splice_qual_mem_lt in H0; auto. apply H in H0. inversion H0.
    * rewrite indexr_skips in H2; try lia. apply (sat_var b U q'); auto.
      rewrite indexr_skips. rewrite indexr_skip; auto. lia. simpl. lia.
      replace q' with (q' ↑ᵈ ‖Γ2‖). apply subqual_splice_lr'. auto.
      eapply splice_qual_id. eapply closed_qual_monotone; eauto. lia.
    * rewrite indexr_skips in H2; try lia. apply (sat_tvar b U q'); auto.
      rewrite indexr_skips. rewrite indexr_skip; auto. lia. simpl. lia.
      replace q' with (q' ↑ᵈ ‖Γ2‖). apply subqual_splice_lr'. auto.
      eapply splice_qual_id. eapply closed_qual_monotone; eauto. lia.
  - bdestruct (x =? ‖Γ2‖).
    * subst. apply splice_qual_not_mem in H0. contradiction.
    * destruct x. lia. assert (Hx : x >= ‖Γ2‖). lia.
      specialize (splice_qual_mem_ge Hx H0) as Hxd1. apply H in Hxd1.
      inversion Hxd1.
      + econstructor. rewrite <- indexr_insert_ge.
        eapply indexr_splice_tenv. eauto. lia. lia. rewrite subqual_splice_lr'. auto.
        apply splice_qual_closed''; auto.
      + eapply sat_tvar. rewrite <- indexr_insert_ge.
        eapply indexr_splice_ty_tenv. eauto. lia. lia. lia. rewrite subqual_splice_lr'. auto.
        apply splice_qual_closed''; auto.
Qed.
#[global] Hint Resolve weaken_tenv_saturated : core.

Lemma weaken_saturated : forall {Γ1 Γ2 Σ d1},
    saturated (Γ1 ++ Γ2) Σ d1 -> forall X, saturated ((Γ1 ↑ᴳ ‖Γ2‖) ++ X :: Γ2) Σ (d1 ↑ᵈ ‖Γ2‖).
intros. unfold saturated in *. inversion H. intuition.
Qed.
#[global] Hint Resolve weaken_saturated : core.

(* may not be needed in the later version *)
Lemma splice_openq: forall {q j d1 n}, ([[j ~> d1]]ᵈ q) ↑ᵈ n = ([[j ~> d1 ↑ᵈ n ]]ᵈ (q ↑ᵈ n)).
  qual_destruct q. qual_destruct d1. unfold_q.
#[local] Hint Resolve n_reflect_true : bdestruct.
  bdestruct (bvs j); simpl; auto.
#[local] Remove Hints n_reflect_true : bdestruct.
intros. apply Q_lift_eq. Qcrush.
bdestruct (x=?n); intuition.
bdestruct (x<?n); intuition.
assert (x > n) by lia. intuition.
Qed.

Lemma n_splice_injective : forall n n' k, n_splice k n = n_splice k n' -> n = n'.
Proof.
  intros. unfold_n. apply FunctionalExtensionality.functional_extensionality. intros. bdestruct (x <? k).
  - apply FunctionalExtensionality.equal_f with (x:=x) in H. bdestruct (x =? k). intuition. apply Nat.ltb_lt in H0. rewrite H0 in H. apply H.
  - apply FunctionalExtensionality.equal_f with (x:=S x) in H. bdestruct (S x =? k). lia. bdestruct (S x <? k). lia. simpl in *. apply H.
Qed.

Lemma splice_qual_injective : forall {k q q'}, q ↑ᵈ k = q' ↑ᵈ k -> q = q'.
intros. qual_destruct q. qual_destruct q'.
unfold_q. inversion H. subst. repeat f_equal. eapply n_splice_injective; eauto.
Qed.

Lemma n_splice_one_S : forall i k, i >= k -> n_splice k (n_one i) = n_one (S i).
intros. unfold_n. apply FunctionalExtensionality.functional_extensionality. intros. bdestruct (x =? k).
  - subst. bdestruct (k =? S i); intuition.
  - bdestruct (x <? k). bdestruct (x <? i); intuition. bdestruct (x =? i); intuition. bdestruct (x =? S i); intuition.
    bdestruct (pred x =? i); bdestruct (x =? S i); intuition.
Qed.

Lemma splice_ty_injective : forall {T T' k}, T ↑ᵀ k = T' ↑ᵀ k -> T = T'.
  induction T; intros; intuition; destruct T'; simpl in H; intuition; try destruct v; try destruct v0; try discriminate; auto;
  try match goal with
  | [ H: _ = (if le_lt_dec ?k ?i then _ else _) |- _ ] => destruct (le_lt_dec k i); discriminate
  | [ H: (if le_lt_dec ?k ?i then _ else _) = _ |- _ ] => destruct (le_lt_dec k i); discriminate
  end.
  - destruct (le_lt_dec k i) eqn:Hltki; destruct (le_lt_dec k i0) eqn:Hltk0; inversion H; subst; auto; try lia.
  - qual_destruct q. qual_destruct q0. qual_destruct q1. qual_destruct q2. inversion H. apply n_splice_injective in H2, H6. unfold_q. subst.
    specialize (IHT1 T'1 k). specialize (IHT2 T'2 k). intuition. subst. auto.
  - qual_destruct q. qual_destruct q0. qual_destruct q1. qual_destruct q2. inversion H. apply n_splice_injective in H2, H6. unfold_q. subst.
    specialize (IHT1 T'1 k). specialize (IHT2 T'2 k). intuition. subst. auto.
  - qual_destruct q. qual_destruct q0. inversion H. apply n_splice_injective in H2. unfold_q. subst.
    specialize (IHT T' k). intuition. subst. auto.
Qed.

Lemma not_free_splice_ty_iff : forall {v k T}, not_free v T <-> not_free v (T ↑ᵀ k).
  intros v k. unfold not_free. intros. intuition.
  - replace (∅) with (∅ ↑ᵈ k); auto. replace (TUnit) with (TUnit ↑ᵀ k); auto. rewrite <- splice_ty_open_rec_ty. rewrite H. auto.
  - replace (∅) with (∅ ↑ᵈ k) in H; auto. replace (TUnit) with (TUnit ↑ᵀ k) in H; auto. rewrite <- splice_ty_open_rec_ty in H.
    eapply splice_ty_injective; eauto.
Qed.

Lemma weaken_gen : forall {t Γ1 Γ2 φ Σ T d},
    has_type (Γ1 ++ Γ2) φ Σ t T d ->
    forall X, has_type ((Γ1 ↑ᴳ ‖Γ2‖) ++ X :: Γ2) (φ ↑ᵈ ‖Γ2‖) Σ (t ↑ᵗ ‖Γ2‖) (T ↑ᵀ ‖Γ2‖) (d ↑ᵈ ‖Γ2‖).
  intros t Γ1 Γ2 φ Σ T d HT. remember (Γ1 ++ Γ2) as Γ. generalize dependent Γ1. generalize dependent Γ2.
  induction HT; intros; subst.
  - (* t_tabs *) rewrite app_length in *. simpl.  constructor.
    apply splice_closed'.
    1-3: rewrite app_length; rewrite splice_tenv_length; simpl;
      replace (‖Γ1‖ + S (‖Γ2‖)) with (S (‖Γ1‖ + ‖Γ2‖)); eauto.
    inversion H0. subst. constructor. 1,2,5: apply splice_qual_closed; auto. 1,2 : apply splice_ty_closed; auto.
    rewrite subqual_splice_lr'. auto. (*  apply weaken_saturated. auto. *)
    rewrite <- not_fresh_splice_iff. auto.
    eauto.
    rewrite app_comm_cons.
    replace ((bind_ty, false, T1 ↑ᵀ ‖Γ2‖, d1 ↑ᵈ ‖Γ2‖)
         :: ((bind_tm, true, TAll (d1 ↑ᵈ ‖Γ2‖) (d2 ↑ᵈ ‖Γ2‖) (T1 ↑ᵀ ‖Γ2‖) (T2 ↑ᵀ ‖Γ2‖), df ↑ᵈ ‖Γ2‖)
                      :: (Γ1 ↑ᴳ ‖Γ2‖)) ++ X :: Γ2)
       with ((((bind_ty, false,T1, d1) :: (bind_tm, true, TAll d1 d2 T1 T2, df) :: Γ1) ↑ᴳ ‖Γ2‖) ++ X :: Γ2).
    specialize (IHHT Γ2 ((bind_ty, false, T1, d1) :: (bind_tm, true, TAll d1 d2 T1 T2, df) :: Γ1)). intuition.  rename H5 into IHHT. remember (a, b1, b0, b) as X.
    specialize (IHHT X). intuition.
    replace ((df ↑ᵈ ‖Γ2‖) ⊔ $!(‖(Γ1 ↑ᴳ ‖Γ2‖) ++ X :: Γ2‖) ⊔ $!(S (‖(Γ1 ↑ᴳ ‖Γ2‖) ++ X :: Γ2‖)) ⊔ {♦})
      with  ((df ⊔ $!(‖Γ1‖ + ‖Γ2‖) ⊔ $!(S (‖Γ1‖ + ‖Γ2‖)) ⊔ {♦}) ↑ᵈ ‖Γ2‖).
    rewrite <- splice_open'. rewrite <- splice_ty_open'. rewrite <- splice_qual_open'.
    rewrite @open_tm'_len with (Γ':=(Γ1 ++ Γ2)). rewrite @open_ty'_len with (Γ':=(Γ1 ++ Γ2)).
    rewrite @openq'_len with (Γ':=(Γ1 ++ Γ2)). auto.
    1-4 : repeat rewrite app_length; rewrite splice_tenv_length; auto.
    repeat rewrite splice_qual_lub_dist. rewrite splice_qual_fresh. simpl.
    repeat rewrite <- plus_n_Sm. repeat f_equal; unfold_q; rewrite n_splice_one_S; try lia; repeat f_equal; lia.
    simpl. auto.

  - (* t_tapp *) simpl. rewrite splice_qual_open''. rewrite splice_ty_open''. rewrite splice_qual_empty.
    apply t_tapp; eauto.
    1-2: erewrite app_length in *; erewrite splice_tenv_length; simpl in *;
    replace (‖ Γ1 ‖ + S (‖ Γ2 ‖)) with (S (‖ Γ1 ‖ + ‖ Γ2 ‖)); try lia.
    apply splice_ty_closed; eauto. apply splice_qual_closed; eauto.
    rewrite <- @splice_qual_empty with (k := ‖Γ2‖); rewrite <- splice_qual_open''.
    rewrite subqual_splice_lr'; auto. rewrite subqual_splice_lr'; auto.
    replace ((d2 ↑ᵈ (‖ Γ2 ‖)) <~ᵈ ∅; ∅) with ((d2 <~ᵈ ∅; ∅) ↑ᵈ (‖ Γ2 ‖)); auto.
    rewrite splice_qual_open''. f_equal; auto. rewrite <- not_free_splice_ty_iff. auto.

  - (* t_tapp_fresh *) simpl. rewrite splice_qual_open''. rewrite splice_ty_open''. rewrite splice_qual_empty.
    apply t_tapp_fresh with (Γ := ((Γ1 ↑ᴳ (‖ Γ2 ‖)) ++ X :: Γ2))(φ := φ ↑ᵈ (‖ Γ2 ‖))(Σ := Σ) (t := t ↑ᵗ (‖ Γ2 ‖))
      (T1 := T1 ↑ᵀ (‖ Γ2 ‖))(d1 := d1 ↑ᵈ (‖ Γ2 ‖))(T2 := (T2 ↑ᵀ (‖ Γ2 ‖)))
      (df:=(df ↑ᵈ ‖ Γ2 ‖))(d1' := (d1' ↑ᵈ ‖ Γ2 ‖)) (df' := (df' ↑ᵈ ‖ Γ2 ‖)); eauto.
    replace (TAll ((df' ↑ᵈ (‖ Γ2 ‖) ⋒ d1' ↑ᵈ (‖ Γ2 ‖)))(d2 ↑ᵈ (‖ Γ2 ‖)) (T1 ↑ᵀ (‖ Γ2 ‖)) (T2 ↑ᵀ (‖ Γ2 ‖)))
       with ((TAll ( (df' ⋒ d1') ) d2 T1 T2) ↑ᵀ (‖ Γ2 ‖) ); eauto.
    simpl. rewrite splice_qual_qor_dist. rewrite splice_qual_fresh. rewrite splice_qual_glb_dist. auto.
    1,2 : rewrite subqual_splice_lr'; auto.
    1-2: erewrite app_length in *; erewrite splice_tenv_length; simpl in *;
    replace (‖ Γ1 ‖ + S (‖ Γ2 ‖)) with (S (‖ Γ1 ‖ + ‖ Γ2 ‖)); try lia.
    apply splice_ty_closed; eauto. apply splice_qual_closed; eauto.
    rewrite <- @splice_qual_empty with (k := ‖Γ2‖); rewrite <- splice_qual_open''.
    1,4,5 : rewrite subqual_splice_lr'; auto. rewrite <- not_free_splice_ty_iff. auto.
    intros Hfresh. rewrite <- fresh_splice_iff in Hfresh. rewrite <- not_free_splice_ty_iff. auto.
    rewrite <- @splice_qual_empty with (k := ‖Γ2‖); rewrite <- splice_qual_open''. eauto.

  - (* tunit *) simpl. rewrite splice_qual_empty.
    constructor. eapply splice_qual_closed'.
    rewrite app_length in *. rewrite splice_tenv_length. auto.
    - (* t_var *) simpl.
    destruct (le_lt_dec (‖Γ2‖) x) eqn:Heq.
    * (* |Γ2| <= x < |Γ1|+|Γ2|*)
      rewrite splice_qual_one_S; auto.
      apply t_var with (b:=b) (d:=d ↑ᵈ ‖Γ2‖).
      rewrite <- indexr_insert_ge. apply indexr_splice_tenv; eauto. lia.
      erewrite <- splice_qual_just_fv_ge; eauto.
      rewrite subqual_splice_lr'. auto.
      eapply splice_qual_closed'.
      rewrite app_length in *. rewrite splice_tenv_length. auto.
      eapply splice_ty_closed''; eauto. eapply splice_qual_closed''; eauto.
    * (* |Γ2| > x *)
      rewrite indexr_skips in H; auto. rewrite splice_qual_one_inv; auto.
      apply t_var with (b:=b) (d:=d).
      rewrite <- indexr_insert_lt; auto. rewrite indexr_skips; auto.
      erewrite splice_ty_id. auto.
      eapply closed_ty_monotone; eauto. lia.
      erewrite <- splice_qual_just_fv_lt; eauto.
      rewrite subqual_splice_lr'. auto.
      eapply splice_qual_closed'.
      rewrite app_length in *. rewrite splice_tenv_length. auto.
      erewrite splice_ty_id; eauto. eapply closed_ty_monotone; eauto. lia. auto.
  - (* t_abs *) rewrite app_length in *. simpl. constructor; auto.
    apply splice_closed'.
    1-3: rewrite app_length; rewrite splice_tenv_length; simpl;
      replace (‖Γ1‖ + S (‖Γ2‖)) with (S (‖Γ1‖ + ‖Γ2‖)); eauto.
    inversion H0. subst. constructor. 1,2,5: apply splice_qual_closed; auto. 1,2 : apply splice_ty_closed; auto.
    rewrite subqual_splice_lr'. auto.
(* rewrite <- not_fresh_splice_iff. auto. *)
    rewrite app_comm_cons.
    replace ((bind_tm, false, T1 ↑ᵀ ‖Γ2‖, d1 ↑ᵈ ‖Γ2‖)
                :: ((bind_tm, true, TFun (d1 ↑ᵈ ‖Γ2‖) (d2 ↑ᵈ ‖Γ2‖) (T1 ↑ᵀ ‖Γ2‖) (T2 ↑ᵀ ‖Γ2‖), df ↑ᵈ ‖Γ2‖)
                      :: (Γ1 ↑ᴳ ‖Γ2‖)) ++ X :: Γ2)
            with ((((bind_tm, false,T1, d1) :: (bind_tm, true, TFun d1 d2 T1 T2, df) :: Γ1) ↑ᴳ ‖Γ2‖) ++ X :: Γ2).
    replace ((df ↑ᵈ ‖Γ2‖) ⊔ $!(‖(Γ1 ↑ᴳ ‖Γ2‖) ++ X :: Γ2‖) ⊔ $!(S (‖(Γ1 ↑ᴳ ‖Γ2‖) ++ X :: Γ2‖)) ⊔ {♦})
      with  ((df ⊔ $!(‖Γ1‖ + ‖Γ2‖) ⊔ $!(S (‖Γ1‖ + ‖Γ2‖)) ⊔ {♦}) ↑ᵈ ‖Γ2‖).
    rewrite <- splice_open'. rewrite <- splice_ty_open'. rewrite <- splice_qual_open'.
    rewrite @open_tm'_len with (Γ':=(Γ1 ++ Γ2)). rewrite @open_ty'_len with (Γ':=(Γ1 ++ Γ2)).
    rewrite @openq'_len with (Γ':=(Γ1 ++ Γ2)).
    apply IHHT; intuition. 1-4 : repeat rewrite app_length; rewrite splice_tenv_length; auto.
    repeat rewrite splice_qual_lub_dist. rewrite splice_qual_fresh. simpl.
    repeat rewrite <- plus_n_Sm. repeat f_equal; unfold_q; rewrite n_splice_one_S; try lia; repeat f_equal; lia.
    simpl. auto.
  - (* t_app *) simpl. rewrite splice_qual_open''. rewrite splice_ty_open''. rewrite splice_qual_empty. apply t_app with (T1:=T1 ↑ᵀ ‖Γ2‖) (df:=df ↑ᵈ ‖Γ2‖).
    apply IHHT1; auto.
    apply IHHT2; auto.
    rewrite <- @splice_qual_empty with (k := ‖Γ2‖); rewrite <- splice_qual_open''.
    rewrite subqual_splice_lr'; auto. rewrite <- not_fresh_splice_iff. auto.
    rewrite <- not_free_splice_ty_iff. auto.
    replace ((d2 ↑ᵈ (‖ Γ2 ‖)) <~ᵈ ∅; ∅) with ((d2 <~ᵈ ∅; ∅) ↑ᵈ (‖ Γ2 ‖)); auto.
    rewrite splice_qual_open''. f_equal; auto.
  - (* t_app_fresh *) simpl. rewrite splice_qual_open''. rewrite splice_ty_open''. rewrite splice_qual_empty.
    apply t_app_fresh with (T1:=T1 ↑ᵀ ‖Γ2‖) (d1:=d1 ↑ᵈ ‖Γ2‖) (df:=df ↑ᵈ ‖Γ2‖) (d1':=d1' ↑ᵈ ‖Γ2‖) (df':=df' ↑ᵈ ‖Γ2‖); auto.
    replace (TFun ((df' ↑ᵈ (‖ Γ2 ‖) ⋒ d1' ↑ᵈ (‖ Γ2 ‖))) (d2 ↑ᵈ (‖ Γ2 ‖)) (T1 ↑ᵀ (‖ Γ2 ‖)) (T2 ↑ᵀ (‖ Γ2 ‖)))
       with ((TFun (df' ⋒ d1') d2 T1 T2) ↑ᵀ (‖ Γ2 ‖)). auto.
    simpl. rewrite splice_qual_qor_dist. rewrite splice_qual_fresh. rewrite splice_qual_glb_dist. auto.
    1,2 : rewrite subqual_splice_lr'; auto.
    intros Hfresh. rewrite <- fresh_splice_iff in Hfresh. rewrite <- not_free_splice_ty_iff. auto.
    rewrite <- not_free_splice_ty_iff. auto.
    rewrite <- @splice_qual_empty with (k := ‖Γ2‖); rewrite <- splice_qual_open''.
    1-3 : rewrite subqual_splice_lr'; auto.
    replace ((d2 ↑ᵈ (‖ Γ2 ‖)) <~ᵈ ∅; ∅) with ((d2 <~ᵈ ∅; ∅) ↑ᵈ (‖ Γ2 ‖)); auto.
    rewrite splice_qual_open''. f_equal; auto.
  - (* t_loc *) simpl. rewrite splice_qual_qor_dist. replace (&! l ↑ᵈ (‖ Γ2 ‖)) with (&! l). apply t_loc. eapply splice_qual_closed'.
    rewrite app_length in *. rewrite splice_tenv_length. auto.
    erewrite splice_ty_id; eauto. erewrite splice_qual_id; eauto. eapply closed_qual_monotone; eauto. lia. eapply closed_ty_monotone; eauto. lia.
    erewrite splice_ty_id; eauto. eapply closed_ty_monotone; eauto. lia.
    erewrite splice_qual_id; eauto. eapply closed_qual_monotone; eauto. lia.
    qual_destruct φ. Qcrush. Qcrush. Qcrush. apply Q_lift_eq. Qcrush.
  - (* t_ref *) simpl in *. specialize (IHHT Γ2 Γ1). intuition. remember (a, b1, b0, b) as X.
    specialize (H2 X).
    rewrite splice_qual_qor_dist. rewrite splice_qual_fresh. apply t_ref; auto.
    erewrite splice_ty_id; auto. eapply closed_ty_monotone; eauto. lia. Qcrush.
  - (* t_deref *) simpl. econstructor; eauto. apply subqual_splice_lr'. auto.
  - (* t_assign *) simpl. specialize (IHHT1 Γ2 Γ1). specialize (IHHT2 Γ2 Γ1). intuition.
    remember (a, b1, b0, b) as X.
    specialize (H0 X). specialize (H1 X). simpl in *. rewrite splice_qual_empty. eapply t_assign; eauto.
  - (* t_sub *) eapply t_sub. eapply IHHT; auto.
    apply @weaken_stp_gen; eauto; lia. apply subqual_splice_lr'. auto. auto.
Qed.

Lemma weaken_flt : forall {Γ φ Σ t T d},
    has_type Γ φ Σ t T d ->
    forall {φ'}, φ ⊑↑ φ' -> closed_Qual 0 (‖Γ‖) (‖Σ‖) φ'↑ ->
    has_type Γ φ' Σ t T d.
  intros Γ φ Σ t T d HT.
  induction HT; intros; try solve [econstructor; eauto].
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
    has_type [] φ Σ t T d -> forall {φ'}, φ ⊑↑ φ' -> forall {Γ}, closed_Qual 0 (‖Γ‖) (‖Σ‖) φ'↑ -> has_type Γ φ' Σ t T d.
  intros. eapply weaken_flt; eauto. apply weaken. auto.
Qed.

Lemma weaken_store : forall {Γ φ Σ t T d}, has_type Γ φ Σ t T d -> forall {Σ'}, Σ' ⊇ Σ -> has_type Γ φ Σ' t T d.
Proof.  intros Γ φ Σ t T d HT.
  induction HT; intros; intuition; try solve [econstructor; eauto;
    try solve [eapply closed_qual_monotone; eauto; apply extends_length; auto];
    try solve [eapply closed_tm_monotone; eauto; apply extends_length; auto];
    try solve [eapply closed_ty_monotone; eauto; apply extends_length; auto];
    try solve [eapply weaken_store_saturated; eauto];
    try solve [eapply weaken_store_senv_saturated; eauto]].
  - econstructor; eauto.
    unfold extends in H6. destruct H6. rewrite H6.
    rewrite indexr_skips. auto. eapply indexr_var_some'. eauto.
  - econstructor; eauto. eapply weaken_stp_store_ext; eauto.
    eapply weaken_store_senv_saturated; eauto.
Qed.

Lemma narrowing_saturated : forall {Γ1 b U du Γ2 Σ q},
    saturated (Γ1 ++ (bind_tm, b,U,du) :: Γ2) Σ q ->
    forall {V dv}, stp [] Σ V dv U du -> saturated (Γ1 ++ (bind_tm, b,V,dv) :: Γ2) Σ q.
Proof.  intros. inversion H. constructor; intros; auto. unfold tenv_saturated. intros.
  apply H1 in H3. inversion H3.
  - destruct (PeanoNat.Nat.lt_trichotomy x (‖Γ2‖)) as [Hlen | [Hlen | Hlen] ].
    * apply (sat_var b0 U0 q'); auto. rewrite indexr_skips in H4; simpl; auto.
      rewrite indexr_skips. rewrite indexr_skip in H4; try lia. rewrite indexr_skip; try lia.
      auto. simpl. auto.
    * rewrite indexr_skips in H4; simpl; auto. subst. rewrite indexr_head in H4. inversion H4. subst.
      apply (sat_var b0 V dv). rewrite indexr_skips; auto. rewrite indexr_head. auto.
      apply stp_qstp_inv in H0. apply qstp_empty in H0. eapply Subq_trans; eauto.
      apply stp_closed in H0. intuition. eapply closed_qual_monotone; eauto. lia.
    * destruct x. lia. rewrite <- indexr_insert_ge in H4; try lia.
      apply (sat_var b0 U0 q'); auto. rewrite <- indexr_insert_ge; try lia. auto.
  - destruct (PeanoNat.Nat.lt_trichotomy x (‖Γ2‖)) as [Hlen | [Hlen | Hlen] ].
    * eapply (sat_tvar); eauto. rewrite indexr_skips in H4; simpl; auto.
      rewrite indexr_skips. rewrite indexr_skip in H4; try lia. rewrite indexr_skip; try lia. eauto.
      simpl. auto.
    * subst. rewrite indexr_skips in H4; simpl; auto. rewrite indexr_head in H4. discriminate.
    * destruct x. lia. rewrite <- indexr_insert_ge in H4; try lia.
      eapply sat_tvar; eauto. rewrite <- indexr_insert_ge; try lia. eauto.
Qed.

Lemma narrowing_saturated_ty : forall {Γ1 U du Γ2 Σ q},
    saturated (Γ1 ++ (bind_ty, false,U,du) :: Γ2) Σ q ->
    forall {V dv}, stp [] Σ V dv U du -> saturated (Γ1 ++ (bind_ty, false,V,dv) :: Γ2) Σ q.
  intros. inversion H. constructor; intros; auto. unfold tenv_saturated. intros.
  apply H1 in H3. inversion H3.
  - destruct (PeanoNat.Nat.lt_trichotomy x (‖Γ2‖)) as [Hlen | [Hlen | Hlen] ].
    * apply (sat_var b U0 q'); auto. rewrite indexr_skips in H4; simpl; auto.
      rewrite indexr_skips. rewrite indexr_skip in H4; try lia. rewrite indexr_skip; try lia.
      auto. simpl. auto.
    * rewrite indexr_skips in H4; simpl; auto. subst. rewrite indexr_head in H4. discriminate. lia.
    * destruct x. lia. rewrite <- indexr_insert_ge in H4; try lia.
      apply (sat_var b U0 q'); auto. rewrite <- indexr_insert_ge; try lia. auto.
  - destruct (PeanoNat.Nat.lt_trichotomy x (‖Γ2‖)) as [Hlen | [Hlen | Hlen] ].
    * eapply sat_tvar; eauto. rewrite indexr_skips in H4; simpl; auto.
      rewrite indexr_skips. rewrite indexr_skip in H4; try lia. rewrite indexr_skip; try lia.
      eauto. simpl. auto.
    * rewrite indexr_skips in H4; simpl; auto. subst. rewrite indexr_head in H4. inversion H4. subst.
      eapply sat_tvar. rewrite indexr_skips; auto. rewrite indexr_head. eauto.
      apply stp_qstp_inv in H0. apply qstp_empty in H0. eapply Subq_trans; eauto.
      apply stp_closed in H0. intuition. eapply closed_qual_monotone; eauto. lia.
    * destruct x. lia. rewrite <- indexr_insert_ge in H4; try lia.
      apply (sat_tvar b U0 q'); auto. rewrite <- indexr_insert_ge; try lia. auto.
Qed.

Lemma narrowing_gen : forall {t Γ1 b U du Γ2 φ Σ T d},
    has_type (Γ1 ++ (bind_tm, b,U,du) :: Γ2) φ Σ t T d -> (b = true -> (♦∈ du)) ->
    forall {V dv}, stp [] Σ V dv U du -> has_type (Γ1 ++ (bind_tm, b,V,dv) :: Γ2) φ Σ t T d.
Proof. intros t Γ1 b U du Γ2 φ Σ T d HT Hb. remember (Γ1 ++ (bind_tm, b, U, du) :: Γ2) as Γ.
  generalize dependent Γ1. generalize dependent U. generalize dependent du. generalize dependent Γ2.
  induction HT; intros; subst.
  - (* t_tabs*) repeat  rewrite app_length in *. simpl in *.
    constructor; auto. 1-3: rewrite app_length in *; simpl in *; auto.
    rewrite @open_tm'_len with (Γ' := (Γ1 ++ (bind_tm, b,U, du) :: Γ2)).
    rewrite @open_ty'_len with (Γ' := (Γ1 ++ (bind_tm, b,U, du) :: Γ2)).
    rewrite @openq'_len with (Γ' := (Γ1 ++ (bind_tm, b,U, du) :: Γ2)).
    2-4: repeat rewrite app_length; simpl; auto.
    rewrite app_length. simpl.
    rewrite app_comm_cons. rewrite app_comm_cons.
    eapply IHHT; eauto. simpl. auto.
  - econstructor; eauto. all : rewrite app_length in *; simpl in *; auto.
  - (* t_tapp_fresh*)
    eapply t_tapp_fresh; eauto.
    1,2: repeat rewrite app_length in *; simpl in *; auto.
    all: eapply narrowing_saturated; eauto.
  - econstructor; eauto.
    repeat rewrite app_length in *; simpl in *; auto.
  - repeat rewrite app_length in *; simpl in *; auto.
    destruct (PeanoNat.Nat.lt_trichotomy x (‖Γ2‖)) as [Hlen | [Hlen | Hlen] ].
    * apply t_var with (b:=b0) (d:=d); auto. rewrite <- indexr_insert_lt; auto. rewrite <- indexr_insert_lt in H; auto.
      repeat rewrite app_length in *; simpl in *; auto.
    * subst. rewrite indexr_insert in H. inversion H. subst.
      apply t_sub with (T1:=V) (d1:=$!‖Γ2‖); auto. apply t_var with (b:=b0) (d:=dv).
      rewrite indexr_insert. auto. destruct φ. simpl. auto.
      repeat rewrite app_length in *; simpl in *; auto.
      1,2 : apply stp_closed in H4; intuition. eapply closed_ty_monotone; eauto. eapply closed_qual_monotone; eauto.
      eapply stp_shrink_var; eauto. eapply weaken_stp'; eauto. eapply weaken_stp; eauto.
      replace Γ2 with (Γ2 ++ []). eapply weaken_stp'; eauto. rewrite app_nil_r. auto. rewrite app_length. simpl. lia.
    * apply t_var with (b:=b0) (d:=d); auto. destruct x. lia. rewrite <- indexr_insert_ge; try lia.
      rewrite <- indexr_insert_ge in H; try lia. auto.
      repeat rewrite app_length in *; simpl in *; auto.
  - repeat rewrite app_length in *; simpl in *; auto.
    constructor; auto. 1-3 : rewrite app_length in *; simpl in *; auto.
    rewrite @open_tm'_len with (Γ' := (Γ1 ++ (bind_tm, b,U, du) :: Γ2)).
    rewrite @open_ty'_len with (Γ' := (Γ1 ++ (bind_tm, b,U, du) :: Γ2)).
    rewrite @openq'_len with (Γ' := (Γ1 ++ (bind_tm, b,U, du) :: Γ2)).
    2-4 : repeat rewrite app_length; simpl; auto.
    rewrite app_length. simpl.
    rewrite app_comm_cons. rewrite app_comm_cons.
    eapply IHHT; eauto. simpl. auto.
  - econstructor; eauto.
  - eapply t_app_fresh; eauto. all: eapply narrowing_saturated; eauto.
  - econstructor; eauto. repeat rewrite app_length in *; simpl in *; auto.
  - econstructor; eauto.
  - econstructor; eauto.
  - econstructor; eauto.
  - eapply t_sub; eauto. eapply narrowing_stp_gen; eauto.
    replace (Γ2) with (Γ2 ++ []). eapply weaken_stp'; eauto. rewrite app_nil_r. auto.
Qed.

Lemma narrowing : forall {Γ b U du φ Σ t T d}, has_type ((bind_tm, b,U,du) :: Γ) φ Σ t T d -> (b = true -> (♦∈ du)) -> forall {V dv}, stp [] Σ V dv U du -> has_type ((bind_tm, b,V,dv) :: Γ) φ Σ t T d.
  intros. specialize (@narrowing_gen t [] b U du Γ φ Σ T d) as narrow. simpl in *. eapply narrow; eauto.
Qed.

Lemma narrowing_ty_gen : forall {t Γ1 U du Γ2 φ Σ T d},
    has_type (Γ1 ++ (bind_ty, false,U,du) :: Γ2) φ Σ t T d ->
    forall {V dv}, stp [] Σ V dv U du ->
    has_type (Γ1 ++ (bind_ty, false,V,dv) :: Γ2) φ Σ t T d.
Proof. intros t Γ1 U du Γ2 φ Σ T d HT. remember (Γ1 ++ (bind_ty, false, U, du) :: Γ2) as Γ.
  generalize dependent Γ1. generalize dependent U. generalize dependent du. generalize dependent Γ2.
  induction HT; intros; subst.
  - (* t_tabs*) repeat  rewrite app_length in *. simpl in *.
    constructor; auto. 1-3: rewrite app_length in *; simpl in *; auto.
    rewrite @open_tm'_len with (Γ' := (Γ1 ++ (bind_ty, false,U, du) :: Γ2)).
    rewrite @open_ty'_len with (Γ' := (Γ1 ++ (bind_ty, false,U, du) :: Γ2)).
    rewrite @openq'_len with (Γ' := (Γ1 ++ (bind_ty, false,U, du) :: Γ2)).
    2-4: repeat rewrite app_length; simpl; auto.
    rewrite app_length. simpl.
    rewrite app_comm_cons. rewrite app_comm_cons.
    eapply IHHT; eauto. simpl. auto.
  - econstructor; eauto. all : rewrite app_length in *; simpl in *; auto.
  - (* t_tapp_fresh*)
    eapply t_tapp_fresh; eauto.
    1,2: repeat rewrite app_length in *; simpl in *; auto.
    all: eapply narrowing_saturated_ty; eauto.
  - econstructor; eauto.
    repeat rewrite app_length in *; simpl in *; auto.
  - repeat rewrite app_length in *; simpl in *; auto.
    destruct (PeanoNat.Nat.lt_trichotomy x (‖Γ2‖)) as [Hlen | [Hlen | Hlen] ].
    * apply t_var with (b:=b) (d:=d); auto. rewrite <- indexr_insert_lt; auto. rewrite <- indexr_insert_lt in H; auto.
      repeat rewrite app_length in *; simpl in *; auto.
    * subst. rewrite indexr_insert in H. inversion H.
    * apply t_var with (b:=b) (d:=d); auto. destruct x. lia. rewrite <- indexr_insert_ge; try lia.
      rewrite <- indexr_insert_ge in H; try lia. auto.
      repeat rewrite app_length in *; simpl in *; auto.
  - repeat rewrite app_length in *; simpl in *; auto.
    constructor; auto. 1-3 : rewrite app_length in *; simpl in *; auto.
    rewrite @open_tm'_len with (Γ' := (Γ1 ++ (bind_ty, false,U, du) :: Γ2)).
    rewrite @open_ty'_len with (Γ' := (Γ1 ++ (bind_ty, false,U, du) :: Γ2)).
    rewrite @openq'_len with (Γ' := (Γ1 ++ (bind_ty, false,U, du) :: Γ2)).
    2-4 : repeat rewrite app_length; simpl; auto.
    rewrite app_length. simpl.
    rewrite app_comm_cons. rewrite app_comm_cons.
    eapply IHHT; eauto. simpl. auto.
  - econstructor; eauto.
  - eapply t_app_fresh; eauto. all: eapply narrowing_saturated_ty; eauto.
  - econstructor; eauto. repeat rewrite app_length in *; simpl in *; auto.
  - econstructor; eauto.
  - econstructor; eauto.
  - econstructor; eauto.
  - eapply t_sub; eauto. eapply narrowing_stp_ty_gen; eauto. 1,2: apply stp_closed in H2; intuition.
    replace (Γ2) with (Γ2 ++ []). eapply weaken_stp'; eauto. rewrite app_nil_r. auto.
Qed.

Lemma narrowing_ty : forall {Γ U du φ Σ t T d}, has_type ((bind_ty, false,U,du) :: Γ) φ Σ t T d ->
  forall {V dv}, stp [] Σ V dv U du ->
  has_type ((bind_ty, false,V,dv) :: Γ) φ Σ t T d.
  intros. specialize (@narrowing_ty_gen t [] U du Γ φ Σ T d). intuition. eapply H2; eauto.
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

Lemma CtxOK_weaken_flt : forall {Γ φ Σ σ}, CtxOK Γ φ Σ σ -> forall {φ'}, closed_Qual 0 (‖Γ‖) (‖Σ‖) φ'↑ -> φ ⊑↑ φ' -> CtxOK Γ φ' Σ σ.
  intros. inversion H. subst. constructor; intuition.
  all : specialize (H3 _ _ _ _ H4 H5); intuition.
  eapply weaken_flt; eauto.
Qed.

Lemma subst1_tenv_length : forall {v T  q Γ}, ‖ { v |-> T ~ q }ᴳ Γ ‖ = ‖Γ‖.
  intros. unfold subst_tenv. rewrite map_length. auto.
Qed.

Lemma subst_tenv_length : forall {v T q T' q' Γ}, ‖ { v |-> T ~ q ; T' ~ q' }ᴳ Γ ‖ = ‖Γ‖.
  intros. repeat rewrite subst1_tenv_length. auto.
Qed.

Lemma subst1_qual_fresh : forall {dx}, {0 |-> dx }ᵈ {♦} = {♦}.
  intros. apply (@subst1_qual_id 0 0). auto.
Qed.
#[global] Hint Resolve subst1_qual_fresh : core.

Lemma subst1_ty_id : forall {T b l}, closed_ty b 0 l T -> forall {T1  d1}, { 0 |-> T1 ~ d1 }ᵀ T = T.
  induction T; intros; inversion H; subst; simpl; intuition;
                       try solve [erewrite IHT; eauto];
                       try solve [erewrite IHT1; eauto; erewrite IHT2; eauto].
  erewrite IHT1; eauto. erewrite IHT2; eauto. erewrite subst1_qual_id; eauto.  erewrite subst1_qual_id; eauto.
  erewrite IHT1; eauto. erewrite IHT2; eauto. erewrite subst1_qual_id; eauto.  erewrite subst1_qual_id; eauto.
  erewrite IHT; eauto. erewrite subst1_qual_id; eauto.
Qed.

Lemma subst_ty_id : forall {b l T}, closed_ty b 0 l T -> forall {T1 T2 d1 d2}, { 0 |-> T1 ~ d1 ; T2 ~ d2 }ᵀ T = T.
  intros. repeat erewrite subst1_ty_id; eauto.
Qed.

Lemma subst1_tm_id : forall {t b l}, closed_tm b 0 l t -> forall {t1}, { 0 |-> t1 }ᵗ t = t.
  induction t; intros b loc Hc; inversion Hc; subst; intros; simpl; intuition;
                       try solve [erewrite IHt; eauto];
                       try solve [erewrite IHt1; eauto; erewrite IHt2; eauto].
Qed.

Lemma open_subst1_qual : forall {q b l},
    closed_Qual b 0 l q↑ ->
    forall {k d1},
      [[k ~> d1 ]]ᵈ q = { 0 |-> d1 }ᵈ ([[k ~> $!0 ]]ᵈ q).
  intros. qual_destruct q. qual_destruct d1. unfold_q.
#[local] Hint Resolve n_reflect_true : bdestruct.
bdestruct (bvs k); simpl.
bdestruct (n_or fvs (n_one 0) 0); simpl. apply Q_lift_eq. Qcrush; exfalso; eauto.
exfalso. Qcrush.
bdestruct (fvs 0). apply Q_lift_eq. Qcrush; exfalso; eauto.
apply Q_lift_eq. Qcrush; exfalso; eauto.
#[local] Remove Hints n_reflect_true : bdestruct.
Qed.

Lemma open_subst1_ty : forall {T b l},
    closed_ty b 0 l T ->
    forall {k T1 d1},
      [[k ~> T1 ~ d1 ]]ᵀ T = { 0 |-> T1 ~ d1 }ᵀ ([[k ~> $0 ~ $!0]]ᵀ T).
  induction T; intros; inversion H; subst; simpl; intuition.
  destruct (k =? x); auto.
  erewrite IHT1; eauto. erewrite IHT2; eauto.
  erewrite <- open_subst1_qual; eauto. erewrite <- open_subst1_qual; eauto.
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

Fixpoint open_subst1_ty_comm {T : ty} :
  forall {k fr g Tf df ff lf}, closed_ty 0 ff lf Tf ->  closed_qual 0 ff lf df ->
    [[k ~> $g ~ ${fr}g ]]ᵀ ({0 |-> Tf ~ df }ᵀ T) = {0 |-> Tf ~ df }ᵀ ([[ k ~> $(S g) ~ ${fr}(S g) ]]ᵀ  T).
    destruct T; intros; try destruct v; simpl; intuition;
      try solve [repeat erewrite open_subst1_ty_comm; eauto].
    + destruct (i =? 0) eqn: Heq; intuition.  erewrite closed_ty_open_id; eauto. lia.
    + edestruct (k =? 0) eqn: Heq; intuition.
      destruct (k =? i); simpl; auto.  destruct (k =? i); simpl; auto.
    + erewrite open_subst1_qual_comm; eauto. erewrite open_subst1_qual_comm; eauto.
    erewrite open_subst1_ty_comm; eauto. erewrite open_subst1_ty_comm; eauto.
    + erewrite open_subst1_qual_comm; eauto. erewrite open_subst1_qual_comm; eauto.
    erewrite open_subst1_ty_comm; eauto.
    erewrite open_subst1_ty_comm; eauto.
    + erewrite open_subst1_ty_comm; eauto. erewrite open_subst1_qual_comm; eauto.
Qed.

Lemma closed_ty_subst1 : forall {T b f l},
    closed_ty b (S f) l T ->
    forall {T1 d1 l1}, closed_ty 0 0 l1 T1 -> closed_qual 0 0 l1 d1 ->
    forall{l2},
      l <= l2 -> l1 <= l2 ->
      closed_ty b f l2 ({0 |-> T1 ~ d1}ᵀ T).
  intros T b f l Hc. remember (S f) as f'. generalize dependent f.
  induction Hc; intros; subst; simpl in *; intuition; try constructor;
    try solve [eapply IHHc; eauto; lia ];
    try solve [eapply IHHc1; eauto];
    try solve [eapply IHHc2; eauto; lia].
  destruct (x =? 0) eqn: Heq. eapply closed_ty_monotone; eauto; lia.
  constructor. inversion H. subst. eapply Nat.eqb_neq in  Heq. lia.  subst.  lia.
  1,2,4-6: eapply closed_qual_subst1; eauto.
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
  induction Hc; intros; subst; simpl in *; intuition; try constructor;
    try solve [eapply IHHc; eauto; lia ];
    try solve [eapply IHHc1; eauto];
    try solve [eapply IHHc2; eauto].
  bdestruct (x =? 0).
  eapply closed_tm_monotone; eauto; lia. intuition.
Qed.

Lemma open_subst2_qual : forall {q l},
    closed_Qual 2 0 l q ↑ ->
    forall {d1 df}, closed_Qual 0 0 l d1 ↑ ->
    [[1~> df ]]ᵈ ([[0~> d1 ]]ᵈ q) = { 0 |-> d1; df }ᵈ ([[1 ~> $!1]]ᵈ ([[0 ~> $!0]]ᵈ q)).
  intros. erewrite <- open_subst1_qual_comm; eauto.
  erewrite open_subst1_qual; eauto. f_equal. f_equal.
  erewrite open_subst1_qual; eauto. erewrite open_subst1_qual; eauto.
  eapply closed_qual_subst1; eauto. eapply closed_qual_open_succ; eauto.
Qed.

Lemma open_subst2_ty : forall {T l},
    closed_ty 2 0 l T ->
    forall {T1 d1 Tf df}, closed_ty 0 0 l T1 -> closed_Qual 0 0 l d1 ↑ ->
    [[1~> Tf ~ df ]]ᵀ ([[0~> T1 ~ d1 ]]ᵀ T) = { 0 |-> T1 ~ d1; Tf ~ df }ᵀ ([[1 ~> $1 ~ $!1]]ᵀ ([[0 ~> $0 ~ $!0]]ᵀ T)).
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

Lemma indexr_subst1 : forall {x Γ b T U d Tx dx},
    x >= 1 ->
    indexr x (Γ ++ [U]) = Some ((bind_tm, b, T, d)) ->
    indexr (pred x) ({ 0 |-> Tx ~ dx }ᴳ Γ) = Some ((bind_tm, b, { 0 |-> Tx ~ dx }ᵀ T, { 0 |-> dx }ᵈ d)).
  intros. destruct x; try lia.
  rewrite <- indexr_insert_ge in H0; simpl; try lia.
  rewrite app_nil_r in H0. induction Γ; intros; simpl in *. discriminate.
  rewrite subst1_tenv_length. (bdestruct (x =? ‖Γ‖)); auto.
  inversion H0. auto.
Qed.

Lemma indexr_subst1_ty: forall {x Γ b T U d Tx dx},
    x >= 1 ->
    indexr x (Γ ++ [U]) = Some ((bind_ty, b, T, d)) ->
    indexr (pred x) ({ 0 |-> Tx ~  dx }ᴳ Γ) = Some ((bind_ty, b, { 0 |-> Tx ~ dx }ᵀ T, { 0 |-> dx }ᵈ d)).
Proof.   intros. destruct x; try lia.
  rewrite <- indexr_insert_ge in H0; simpl; try lia.
  rewrite app_nil_r in H0. induction Γ; intros; simpl in *. discriminate.
  rewrite subst1_tenv_length. (bdestruct (x =? length Γ)); auto.
  inversion H0. auto.
Qed.

Lemma indexr_subst1_ty': forall {x Γ b T d U du},
    indexr x (Γ ++ [(bind_ty, b, T, d)]) = Some ((bind_ty, b, U, du)) ->
    (x = 0 /\ T = U  /\ d = du \/
    x >  0  /\ indexr (pred x) ({ 0 |-> T ~ d }ᴳ Γ) = Some ((bind_ty, b, { 0 |-> T ~ d }ᵀ U, { 0 |-> d }ᵈ du))).
Proof.   intros. induction  Γ; intros.
  + simpl  in H. destruct (x =? 0) eqn: Heqn.
    -  inversion H. subst. left.  intuition.  apply Nat.eqb_eq in Heqn. auto.
    -  inversion H.
  + remember (length (Γ ++ [(bind_ty, b, T, d)])) as L.
     destruct (Nat.eqb x L) eqn: Heqn.
    - assert (x = L). eapply Nat.eqb_eq. eauto.
      eapply indexr_hit in H.
      right. split. rewrite app_length in HeqL. simpl in HeqL. lia.
       assert ((pred x) = (‖ ({ 0 |-> T ~  d }ᴳ Γ) ‖)).
       rewrite subst1_tenv_length. rewrite app_length in HeqL. simpl in HeqL.  lia.
       simpl. eapply Nat.eqb_eq in H1.  subst.
       destruct (pred (length (Γ ++ [(bind_ty, b, T, d)])) =? length ({0 |-> T ~ d }ᴳ Γ)); auto.
       inversion H1.
       subst. eauto.
    - assert (x <> L). eapply Nat.eqb_neq. eauto.
       replace ((a :: Γ) ++ [(bind_ty, b, T, d)]) with  (a :: (Γ ++ [(bind_ty, b, T, d)])) in H.
       rewrite indexr_skip in H. intuition.
       right. split. eauto.
       simpl.
       assert ((pred x) <> ( ‖({ 0 |-> T ~  d }ᴳ Γ)‖)).
       rewrite app_length in HeqL. simpl in HeqL. rewrite subst1_tenv_length.
       unfold not. intros. subst L.
       unfold not in H0. eapply H0. rewrite <-H2. lia.
       eapply Nat.eqb_neq in H2. rewrite H2.
       eauto. subst. eauto.  intuition.
Qed.

Lemma indexr_subst1_ty'': forall {x Γ b  T d b' U du},
    indexr x (Γ ++ [(bind_tm, b, T, d)]) = Some ((bind_ty, b', U, du)) ->
    forall {d'},
    x >  0  /\ indexr (pred x) ({ 0 |-> T ~ d' }ᴳ Γ) = Some ((bind_ty, b', { 0 |-> T ~ d' }ᵀ U,  { 0 |->  d' }ᵈ du)).
Proof.  intros. induction  Γ; intros.
  + simpl  in H. destruct (x =? 0) eqn: Heqn.
    -  inversion H.
    -  inversion H.
  + remember (length (Γ ++ [(bind_tm, b, T, d)])) as L.
     destruct (Nat.eqb x L) eqn: Heqn.
    - assert (x = L). eapply Nat.eqb_eq. eauto.
      eapply indexr_hit in H.
      split. rewrite app_length in HeqL. simpl in HeqL. lia.
       assert ((pred x) = (length ({ 0 |-> T ~  d' }ᴳ Γ))).
       rewrite subst1_tenv_length. rewrite app_length in HeqL. simpl in HeqL.  lia.
       simpl. eapply Nat.eqb_eq in H1.  subst.  rewrite  H1.  auto.
       subst. eauto.
    - assert (x <> L). {  eapply Nat.eqb_neq. eauto. }
       replace ((a :: Γ) ++ [(bind_tm, b, T, d)]) with  (a :: (Γ ++ [(bind_tm, b, T, d)])) in H.
       rewrite indexr_skip in H.  intuition.
       simpl.
       assert ((pred x) <> (length ({ 0 |-> T ~  d' }ᴳ Γ))).
       rewrite app_length in HeqL. simpl in HeqL. rewrite subst1_tenv_length.
       unfold not. intros. subst L.
       unfold not in H0. eapply H0. rewrite <-H1. lia.
       eapply Nat.eqb_neq in H1. rewrite H1.
       eauto. subst. eauto.  intuition.
Qed.

Lemma subst1_openq_comm: forall {l q d1 d2}, closed_qual 0 0 l q -> {0 |-> q}ᵈ (open_qual 0 d1 d2) = open_qual 0 ({0 |-> q}ᵈ d1) ({0 |-> q}ᵈ d2).
Proof. intros. erewrite subst1_open_qual_comm; eauto.
Qed.

Lemma subst1_open_ty_comm : forall {l Tc dc T3 d3 T k}, closed_ty 0 0 l Tc -> closed_qual 0 0 l dc ->
        ({0 |-> Tc ~ dc }ᵀ ([[k ~> T3 ~ d3 ]]ᵀ T) = ([[k ~> ({0 |-> Tc ~ dc }ᵀ T3) ~ ({0  |-> dc}ᵈ d3)]]ᵀ ({0 |-> Tc ~ dc }ᵀ T))).
Proof.  intros. generalize dependent k. induction T; try destruct v; intuition; simpl.
  + bdestruct (i =? 0); simpl; intuition. erewrite closed_ty_open_id; eauto. lia.
  + bdestruct (k =? i); simpl; auto.
  + f_equal. 1,2:erewrite subst1_open_qual_comm; eauto; erewrite subst1_qual_empty; eauto.  erewrite IHT1; eauto. erewrite IHT2; auto.
  + f_equal. 1,2: erewrite subst1_open_qual_comm; eauto; erewrite subst1_qual_empty; eauto.  erewrite IHT1; eauto. erewrite IHT2; auto.
  + f_equal. erewrite subst1_open_qual_comm; eauto. eapply IHT; eauto.
Qed.

Lemma subst_qual_subqual_monotone : forall {d1 d2}, d1 ⊑↑ d2 -> forall {df}, ({0 |-> df }ᵈ d1) ⊑↑ ({0 |-> df }ᵈ d2).
Proof.
  intros. qual_destruct d1; qual_destruct d2; qual_destruct df; unfold_q.
  #[local] Hint Resolve n_reflect_true : bdestruct.
  bdestruct (fvs0 0); simpl;
  bdestruct (fvs 0); simpl; Qcrush.
  #[local] Remove Hints n_reflect_true : bdestruct.
Qed.

Lemma subst1_just_fv : forall {fr x dy},
    ${fr}x = {0 |-> dy }ᵈ ${fr}(S x).
  intros. apply Q_lift_eq. Qcrush.
Qed.

Lemma closed_qual_subst1' : forall {Γ0 X l Tf df φ b},
    closed_ty 0 0 l Tf ->
    closed_qual 0 0 l df ->
    closed_qual b (‖ Γ0 ++ [X] ‖) l φ ->
    closed_qual b (‖ {0 |-> Tf ~ df }ᴳ Γ0 ‖) l ({0 |-> df }ᵈ φ).
  intros. eapply closed_qual_subst1; eauto. rewrite subst1_tenv_length.
  rewrite app_length in *. simpl in *. replace (‖ Γ0 ‖ + 1) with (S (‖ Γ0 ‖) ) in H1.
  auto. lia.
Qed.

Lemma closed_ty_subst1' : forall {Γ0 X l Tf df T b},
    closed_ty 0 0 l Tf ->
    closed_qual 0 0 l df ->
    closed_ty b (‖ Γ0 ++ [X] ‖) l T ->
    closed_ty b (‖ {0 |-> Tf ~ df }ᴳ Γ0 ‖) l ({0 |-> Tf ~ df }ᵀ T).
  intros. repeat eapply closed_ty_subst1; eauto. rewrite subst1_tenv_length.
  rewrite app_length in *. simpl in *. replace (‖Γ0‖ + 1) with (S (‖Γ0‖)) in H0.
  eapply closed_ty_monotone; eauto. lia. lia.
Qed.

Lemma closed_tm_subst1' : forall {Γ0 X l Tf df tx t b},
    closed_tm 0 0 l tx ->
    closed_tm b (‖ Γ0 ++ [X] ‖) l t ->
    closed_tm b (‖ {0 |-> Tf ~ df }ᴳ Γ0 ‖) l ({0 |-> tx }ᵗ t).
  intros. repeat eapply closed_tm_subst1; eauto. rewrite subst1_tenv_length.
  rewrite app_length in *. simpl in *. replace (length Γ0 + 1) with (S (length Γ0)) in H0.
  auto. lia.
Qed.

Lemma subst1_qual_0' : forall {q' q}, q' ⊑↑ q ⊔ {♦} -> forall {df}, $0 ∈ᵥ df -> q' ⊑↑ { 0 |-> q }ᵈ df ⊔ {♦}.
  intros. qual_destruct df. qual_destruct q. qual_destruct q'. unfold_q. unfold N_lift in H0. rewrite H0. simpl. Qcrush.
- apply H in H3. intuition.
- apply H2 in H3. intuition.
- apply H4 in H3. intuition.
Qed.

Lemma subst1_just_fv0_gen : forall {q fr}, {0 |-> q }ᵈ ${fr}0 = (q ⊔ ∅{ fr }).
  intros. apply Q_lift_eq. Qcrush.
Qed.

Lemma subst1_just_fv0 : forall {q}, {0 |-> q }ᵈ $!0 = q.
  intros. apply Q_lift_eq. Qcrush.
Qed.

Lemma saturated0 : forall {Γ Σ Tx sx frx fx bx lx fr ff bf lf},
  N_lift ff 0 -> saturated (Γ ++ [(bind_tm, sx, Tx, (frx,fx,bx,lx))]) Σ (fr,ff,bf,lf) -> (Is_true frx -> Is_true fr) /\ N_sub (N_lift fx) (N_lift ff) /\ N_sub (N_lift bx) (N_lift bf) /\ N_sub (N_lift lx) (N_lift lf).
  intros. inversion H0. specialize (H1 0). unfold_q. assert (N_lift ff 0) by auto. apply H1 in H3. inversion H3.
- rewrite indexr_skips in H4; auto. simpl in H4. inversion H4. subst. unfold_Q. unfold_N. intuition.
- rewrite indexr_skips in H4; auto. simpl in H4. discriminate.
Qed.

Lemma saturated0_ty : forall {Γ Σ Tx sx frx fx bx lx fr ff bf lf},
  N_lift ff 0 -> saturated (Γ ++ [(bind_ty, sx, Tx, (frx,fx,bx,lx))]) Σ (fr,ff,bf,lf) -> (Is_true frx -> Is_true fr) /\ N_sub (N_lift fx) (N_lift ff) /\ N_sub (N_lift bx) (N_lift bf) /\ N_sub (N_lift lx) (N_lift lf).
  intros. inversion H0. specialize (H1 0). unfold_q. assert (N_lift ff 0) by auto. apply H1 in H3. inversion H3.
- rewrite indexr_skips in H4; auto. simpl in H4. inversion H4.
- rewrite indexr_skips in H4; auto. simpl in H4. inversion H4. subst. unfold_Q. unfold_N. intuition.
Qed.

Lemma subst1_preserves_separation : forall {df d1 sx Tx dx dx' Γ Σ φ},
    dx' ⊓ φ ⊑↑ dx ->
    closed_Qual 0 0 (‖Σ‖) dx'↑ ->
    df ⊑↑ φ -> d1 ⊑↑ φ ->
    saturated (Γ ++ [(bind_tm, sx, Tx, dx)]) Σ d1 ->
    saturated (Γ ++ [(bind_tm, sx, Tx, dx)]) Σ df ->
    {0 |-> dx' }ᵈ df ⊓ {0 |-> dx' }ᵈ d1 = {0 |-> dx' }ᵈ (df ⊓ d1).
  intros. qual_destruct df. qual_destruct d1.
#[local] Hint Resolve n_reflect_true : bdestruct.
  unfold_q. bdestruct (fvs 0); bdestruct (fvs0 0); clift.
#[local] Remove Hints n_reflect_true : bdestruct.
  - apply Q_lift_eq; Qcrush.
  - (* 0 ∈ df, 0 ∉ d1 *)
    qual_destruct dx. specialize (saturated0 H5 H4) as Hlx. apply Q_lift_eq; Qcrush.
  - (* 0 ∉ df, 0 ∈ d1, analogous to the previous case *)
    qual_destruct dx. specialize (saturated0 H6 H3) as Hlx. apply Q_lift_eq; Qcrush.
Qed.

Lemma subst1_ty_preserves_separation : forall {df d1 sx Tx dx dx' Γ Σ φ},
    dx' ⊓ φ ⊑↑ dx ->
    closed_Qual 0 0 (‖Σ‖) dx'↑ ->
    df ⊑↑ φ -> d1 ⊑↑ φ ->
    saturated (Γ ++ [(bind_ty, sx, Tx, dx)]) Σ d1 ->
    saturated (Γ ++ [(bind_ty, sx, Tx, dx)]) Σ df ->
    {0 |-> dx' }ᵈ df ⊓ {0 |-> dx' }ᵈ d1 = {0 |-> dx' }ᵈ (df ⊓ d1).
Proof.
  intros. qual_destruct df. qual_destruct d1.
#[local] Hint Resolve n_reflect_true : bdestruct.
  unfold_q. bdestruct (fvs 0); bdestruct (fvs0 0); clift.
#[local] Remove Hints n_reflect_true : bdestruct.
  - apply Q_lift_eq; Qcrush.
  - (* 0 ∈ df, 0 ∉ d1 *)
    qual_destruct dx. specialize (saturated0_ty H5 H4) as Hlx. apply Q_lift_eq; Qcrush.
  - (* 0 ∉ df, 0 ∈ d1, analogous to the previous case *)
    qual_destruct dx. specialize (saturated0_ty H6 H3) as Hlx. apply Q_lift_eq; Qcrush.
Qed.

Lemma subst1_mem : forall {x dx df l}, closed_Qual 0 0 l dx↑ -> $x ∈ᵥ {0 |-> dx }ᵈ df -> $(S x) ∈ᵥ df.
  intros. qual_destruct df. unfold_q.
#[local] Hint Resolve n_reflect_true : bdestruct.
  bdestruct (fvs 0); Qcrush. exfalso; eauto.
#[local] Remove Hints n_reflect_true : bdestruct.
Qed.

Lemma subst1_mem_loc : forall {dx df l}, l ∈ₗ {0 |-> dx }ᵈ df ->  (l ∈ₗ dx /\ $0 ∈ᵥ df) \/ l ∈ₗ df.
  intros. qual_destruct df. qual_destruct dx. unfold_q.
#[local] Hint Resolve n_reflect_true : bdestruct.
  bdestruct (fvs 0); Qcrush.
#[local] Remove Hints n_reflect_true : bdestruct.
Qed.

Lemma subst1_senv_saturated : forall {Σ df dx'},
    senv_saturated Σ df ->
    closed_Qual 0 0 (‖Σ‖) dx'↑ -> senv_saturated Σ dx' ->
    senv_saturated Σ ({0 |-> dx' }ᵈ df).
  intros. unfold senv_saturated in *. intros. apply subst1_mem_loc in H2. intuition.
  - apply H1 in H2. inversion H2. econstructor; eauto. apply subst1_qual_0'; auto.
  - apply H in H3. inversion H3. econstructor; eauto. qual_destruct df. unfold_q.
#[local] Hint Resolve n_reflect_true : bdestruct.
  bdestruct (fvs 0); Qcrush.
#[local] Remove Hints n_reflect_true : bdestruct.
    * exfalso; eauto.
    * apply H14 in H12. intuition.
Qed.

Lemma subst1_saturated : forall {Γ Σ bx Tx dx df dx'},
    saturated (Γ ++ [(bind_tm, bx, Tx, dx)]) Σ df ->
    closed_Qual 0 0 (‖Σ‖) dx'↑ -> senv_saturated Σ dx' ->
    saturated ({0 |-> Tx ~ dx' }ᴳ Γ) Σ ({0 |-> dx' }ᵈ df).
  intros. inversion H. constructor; intros.
  - unfold tenv_saturated in *. intros.
    eapply subst1_mem in H4; eauto. specialize (H2 (S x)); intuition. inversion H5.
    * eapply @indexr_subst1 with (dx:=dx') in H2. simpl in *. econstructor; eauto. apply subst_qual_subqual_monotone. eauto. eapply closed_qual_subst1; eauto. lia.
    * eapply @indexr_subst1_ty with (dx:=dx') in H2. simpl in *. eapply sat_tvar; eauto. apply subst_qual_subqual_monotone. eauto. eapply closed_qual_subst1; eauto. lia.
  - apply subst1_senv_saturated; auto.
Qed.

Lemma subst1_ty_saturated : forall {Γ Σ bx Tx dx df dx'},
    saturated (Γ ++ [(bind_ty, bx, Tx, dx)]) Σ df ->
    closed_Qual 0 0 (‖Σ‖) dx'↑ -> senv_saturated Σ dx' ->
    saturated ({0 |-> Tx ~ dx' }ᴳ Γ) Σ ({0 |-> dx' }ᵈ df).
  intros. inversion H. constructor; intros.
  - unfold tenv_saturated in *. intros.
    eapply subst1_mem in H4; eauto. specialize (H2 (S x)); intuition. inversion H5.
    * eapply @indexr_subst1 with (dx:=dx') in H2. simpl in *. econstructor; eauto. apply subst_qual_subqual_monotone. eauto. eapply closed_qual_subst1; eauto. lia.
    * eapply @indexr_subst1_ty with (dx:=dx') in H2. simpl in *. eapply sat_tvar; eauto. apply subst_qual_subqual_monotone. eauto. eapply closed_qual_subst1; eauto. lia.
  - apply subst1_senv_saturated; auto.
Qed.

Lemma qglb_increase_fresh : forall {dx dx' φ' l X},
  dx' ⊓ φ' = dx ->
  closed_Qual 0 0 l dx'↑ ->
  dx' ⊓ (φ' ⊔ (false,X,n_empty,n_empty)) = dx.
intros. apply Q_lift_eq' in H. apply Q_lift_eq. rewrite <- H. Qcrush. exfalso; eauto.
Qed.

Lemma qglb_disjoint_freshv : forall {dx' l x},
  closed_Qual 0 0 l dx'↑ -> dx' ⊓ $!x = ∅.
  intros. apply Q_lift_eq. Qcrush. eauto.
Qed.

Lemma qglb_disjoint_fresh : forall {dx' l},
  closed_Qual 0 0 l dx'↑ -> dx' ⊓ {♦} = ∅{ ♦∈? dx' }.
  intros. apply Q_lift_eq. Qcrush.
Qed.

Lemma qmem_plus_decomp : forall {x0 q x}, x0 ∈ₗ q ⊔ &!x -> closed_Qual 0 0 x q↑ -> x0 ∈ₗ q \/ x0 = x.
  intros. assert (x0 ∈ₗ q \/ x0 ∈ₗ &! x); Qcrush.
Qed.

Lemma senv_saturated_qplus : forall {Σ l T q}, indexr l Σ = Some (T, q) -> closed_Qual 0 0 l q↑ -> senv_saturated Σ q -> senv_saturated Σ (q ⊔ &!l).
  unfold senv_saturated. intros. specialize (qmem_plus_decomp H2 H0) as Hl. destruct Hl.
  - apply H1 in H3. inversion H3. subst. econstructor; eauto. eapply Subq_trans; eauto. Qcrush.
  - subst. econstructor; eauto. Qcrush.
Qed.

Lemma wf_senv_saturated_qplus : forall {Σ}, wf_senv Σ -> forall {l T q}, indexr l Σ = Some (T, q) -> senv_saturated Σ (q ⊔ &!l).
  intros. specialize (wf_senv_prop H l T q) as Hwf. intuition. eapply senv_saturated_qplus; eauto.
Qed.

Lemma has_type_senv_saturated : forall {Γ φ Σ t T q}, has_type Γ φ Σ t T q -> wf_senv Σ -> senv_saturated Σ q.
  intros. induction H; eauto; intuition.
  - intuition. apply has_type_closed in H. intuition. eapply senv_saturated_openq; eauto.
  - intuition. apply has_type_closed in H. intuition. eapply senv_saturated_openq; eauto.
  - intuition. apply has_type_closed in H, H1. intuition. eapply senv_saturated_openq; eauto.
  - intuition. apply has_type_closed in H, H3. intuition. eapply senv_saturated_openq; eauto.
  - eapply wf_senv_saturated_qplus; eauto.
Qed.

Lemma vtp_closed:
  forall {Σ t T d}, vtp Σ t T d ->
    closed_tm 0 0 (‖Σ‖) t /\
    closed_ty 0 0 (‖Σ‖) T /\
    closed_Qual 0 0 (‖Σ‖) d↑.
Proof.
  intros. induction H; intuition.
  + apply qstp_closed in H4. subst. intuition.
  + constructor. apply indexr_var_some' in H2; intuition.
  + constructor. apply stp_closed in H3. intuition. auto.
Qed.

Lemma vtp_qual_ex: forall {Σ t T d d'}, vtp Σ t T d -> qstp ([]: tenv) Σ d d'  -> senv_saturated Σ d'-> vtp Σ  t T d'.
Proof.  intros. apply qstp_closed in  H0 as  Hcl_qstp; intuition.  induction  H.
  + assert  (qstp  [] Σ  df1 d'). { eapply qs_trans;  eauto. }
    econstructor; eauto.
  + econstructor;  eauto.
  + econstructor; eauto.
  + assert (qstp [] Σ df1 d').  { eapply qs_trans; eauto. }
    econstructor; eauto.
  + econstructor; eauto.
Qed.

Lemma vtp_saturated: forall {Σ t T d}, vtp Σ t T d -> saturated [] Σ d.
  intros. inversion H; subst; constructor; auto.
  1,2: apply tenv_saturated_empty_tenv; apply vtp_closed in H; intuition.
Qed.

Lemma vtp_widening: forall {Σ T1 d1 T2 d2 t},
  vtp Σ t T1 d1 -> stp [] Σ T1 d1 T2 d2 -> senv_saturated Σ d2 -> vtp Σ t T2 d2.
Proof. intros Σ T1 d1 T2 d2 t HVtp HStp. remember t as tt. remember [] as Γ.  induction HStp; subst.
  - (* TTop *) apply qstp_closed in H0 as Hcl_qstp. intuition.
      inversion HVtp;  subst.
      +  (* TAll  *) apply qstp_closed in H9 as Hcl_qstp. intuition.
         assert (qstp [] Σ df1 d2). { eapply qs_trans; eauto. }
         assert (vtp Σ (ttabs t0)  (TAll d4 d5 T3 T4) df1). {  econstructor; eauto.  }
         assert (vtp Σ (ttabs t0)  (TAll d4 d5 T3 T4) d2). {  econstructor; eauto. }
         eapply vtp_top; eauto.
      + (* TUnit  *) assert  (vtp Σ tunit TUnit d2).  { econstructor; eauto. }
        eapply vtp_top; auto.
      + (* Tloc *) inversion H. subst. econstructor; eauto; intuition.
      + assert  (vtp Σ (tabs t0) (TFun  d4 d5 T3 T4) d2). {  econstructor;  eauto. }
        eapply vtp_top; eauto.
      + assert (vtp Σ t T0 d2).  { eapply vtp_qual_ex; eauto. }
        eapply vtp_top; eauto.
  - (* TVarf_refl *) inversion HVtp.
  - (* Tvarf_trans *) inversion HVtp.
  - (* TAll *) inversion HVtp. subst. apply stp_closed in HStp1 as Hcl.
      econstructor; eauto.
      + eapply s_trans; eauto.
      + assert (stp [] Σ (TAll d0 d7 T0 T5) df1 (TAll d1 d2 T1 T2) d5). {  apply s_all; intuition.  }
        assert (stp [] Σ (TAll d1 d2 T1 T2) d5 (TAll d3 d4 T3 T4) d6). {  apply s_all; intuition.  }
        assert ( stp [] Σ (TAll d0 d7 T0 T5) df1 (TAll d3 d4 T3 T4) d6). { eapply s_trans; eauto. }
        assert (stp [] Σ T3 d3 T1 d1). { eauto. }

       assert (narrow: stp [(bind_ty, false,T3, d3); (bind_tm, true,TAll d0 d7 T0 T5, {♦})] Σ (open_ty' ([]: tenv) T5)(openq' ([]:tenv) d7) (open_ty' ([]:tenv) T2) (openq' ([]: tenv) d2)). {
          eapply narrowing_stp_ty; eauto. 1,2: apply stp_closed in H12; intuition.
          apply weaken_stp. auto.
        }

       (* apply trans *)
       simpl in *. eapply s_trans; eauto.

        specialize (@narrowing_stp_gen [(bind_ty, false, T3, d3)] true (TAll d1 d2 T1 T2) {♦} [] Σ
            (T2 <~²ᵀ ([]:tenv)) (d2 <~²ᵈ ([]:tenv)) (T4 <~²ᵀ ([]:tenv)) (d4 <~²ᵈ ([]:tenv))) as narrowing.
        simpl in narrowing. intuition.
  - inversion HVtp; subst. constructor; auto. apply qstp_closed in H. intuition.
  - inversion HVtp; subst. eapply vtp_loc; eauto. apply qstp_closed in H. intuition.
    all : eapply s_trans; eauto.
  - inversion HVtp; subst. econstructor. 5: eapply H10. all : eauto.
    apply qstp_closed in H1. intuition.
    eapply s_trans; eauto.

    assert (stp [] Σ (TFun d1 d2 T1 T2) d5 (TFun d3 d4 T3 T4) d6).
        { apply s_fun; intuition. }
        assert (stp [] Σ (TFun d0 d7 T0 T5) df1 (TFun d1 d2 T1 T2) d5).
        { apply s_fun; intuition. }
        assert (stp [] Σ (TFun d0 d7 T0 T5) df1 (TFun d3 d4 T3 T4) d6).
        { eapply s_trans; eauto. }
       assert (stp [] Σ T3 d3 T1 d1). { eauto. }

       assert (narrow: stp [(bind_tm, false,T3, d3); (bind_tm, true,TFun d0 d7 T0 T5, {♦})] Σ (open_ty' ([]: tenv) T5)(openq' ([]:tenv) d7) (open_ty' ([]:tenv) T2) (openq' ([]: tenv) d2)). {
          eapply narrowing_stp; eauto. intros. inversion H14. apply weaken_stp. auto.
        }
        (* Set Printing All. *)
        (* apply trans *)
        simpl in *. eapply s_trans; eauto.
        assert (forall T (a:T) (b:T), [a;b] = [a]++[b]) as R. eauto.
        rewrite R in HStp2. rewrite R.

        eapply @narrowing_stp_gen with (U := (TFun d1 d2 T1 T2))(du:={♦})(Γ2 := []: tenv)  in HStp2. 3: constructor. all: eauto.
    - intuition.
Qed.

Lemma has_type_vtp: forall {Σ φ t T d},
  value t ->
  has_type [] φ Σ t T d ->
  wf_senv Σ ->
  vtp Σ t T d.
Proof. intros Σ φ t T d HV Ht HWF. remember [] as Γ.  induction Ht; eauto; subst; try inversion HV; subst; intuition;
        try solve [simpl in H1; discriminate].
       + (* ttabs *) subst. apply has_type_closed in Ht as Hcl. intuition.
         inversion H0. subst.  eapply vtp_tabs; eauto.
          * eapply stp_refl. intuition.
            apply qstp_refl; intuition.
          * apply stp_refl; intuition.
       + (* tabs *) subst.  subst. apply has_type_closed in Ht as Hcl. intuition.
         inversion H0. subst.  eapply vtp_abs; eauto.
          * eapply stp_refl; intuition.
          * apply stp_refl; intuition.
       + (* tloc *) intros.  eapply vtp_loc; eauto.
          * eapply closed_qual_qor; auto. apply just_loc_closed. apply indexr_var_some' in H0. lia.
          * apply stp_refl; auto.
          * apply stp_refl; auto.
          * eapply wf_senv_saturated_qplus; eauto.
       + intuition. eapply vtp_widening; eauto.
       + intuition. eapply vtp_widening; eauto.
       + intuition. eapply vtp_widening; eauto.
       + intuition. eapply vtp_widening; eauto.
Qed.

Lemma vtp_has_type: forall {Σ t T d}, vtp Σ t T d -> has_type [] d Σ t T d.
  intros. induction H.
  + (* ttabs *)
    assert (has_type [] df1 Σ (ttabs t) (TAll d1  d2 T1 T2) df1). {
      constructor; eauto. apply qstp_closed  in H4.  intuition.   }
    assert (has_type [] df2 Σ (ttabs t) (TAll d1 d2 T1 T2) df1). {
      apply qstp_empty in H4 as H4'.  eapply weaken_flt; eauto. apply qstp_closed in H4. intuition. }
    eapply t_sub; eauto.
  + (* tunit *) econstructor; eauto.
  + (* tloc *) eapply qstp_empty in H5.
    eapply t_sub. eapply t_loc; eauto. Qcrush. Qcrush. eauto. eauto. eauto.
  + (* tabs *) assert (has_type [] df1 Σ (tabs t) (TFun d1 d2 T1 T2) df1). {
    constructor; eauto. apply qstp_closed in H5 as Hcl; intuition. }
    assert (has_type [] df2 Σ (tabs t) (TFun d1 d2 T1 T2) df1). {
    inversion H1. subst. eapply weaken_flt with  (φ' := df2) in H10; intuition.
    apply qstp_empty in H5. auto. }
    eapply t_sub; eauto; intuition.
  + (* ttop *) apply has_type_closed in IHvtp as Hcl. intuition.
      econstructor; eauto.
Qed.

Lemma subst1_fresh_id : forall {x dx'}, {x |-> dx' }ᵈ {♦} = {♦}.
  intros. Qcrush.
Qed.

Lemma Substq_non_fresh : forall {dx dx'}, Substq dx dx' -> ♦∉ dx'.
  intros. inversion H; auto.
Qed.
#[global] Hint Resolve Substq_non_fresh : core.

Lemma subst1_non_fresh : forall {x qx q}, ♦∉ q -> ♦∉ qx -> ♦∉ ({ x |-> qx }ᵈ q).
  intros. unfold subst_qual. destruct (qfvs q x). Qcrush. Qcrush.
Qed.
#[global] Hint Resolve subst1_non_fresh : core.

Lemma subst1_fresh : forall {x qx q}, ♦∈ q -> ♦∈ ({ x |-> qx }ᵈ q).
  intros. unfold subst_qual. destruct (qfvs q x). Qcrush. Qcrush.
Qed.
#[global] Hint Resolve subst1_fresh : core.

Lemma un_subst1_fresh : forall {x qx q}, ♦∉ qx -> ♦∈ ({ x |-> qx }ᵈ q) -> ♦∈ q.
intros. qual_destruct q. qual_destruct qx. Qcrush. unfold_q. destruct (fvs x); auto. simpl in *. blift. destruct H0; eauto.
Qed.
#[global] Hint Resolve un_subst1_fresh : core.

Lemma qor_idem : forall {q}, (q ⊔ q) = q.
intros. apply Q_lift_eq; Qcrush.
Qed.

Lemma not_fresh_fresh_false : forall {d}, (♦∉ (d ⊔ {♦})) -> False.
Qcrush.
Qed.

Lemma subst_qstp :  forall {Γ b Tf df df' Σ d1 d2},
    qstp (Γ ++ [(bind_tm, b, Tf, df)]) Σ d1 d2 ->
    closed_ty 0 0 (‖Σ‖) Tf ->
    closed_Qual 0 0 (‖Σ‖) df'↑ ->
    Substq df df' ->
    qstp ({0 |-> Tf ~ df' }ᴳ Γ) Σ ({0 |-> df' }ᵈ d1) ({0 |-> df' }ᵈ d2).
  intros Γ b Tf df df' Σ d1 d2 H. remember (Γ ++ [(bind_tm, b, Tf, df)]) as Γ'.
  generalize dependent Γ. generalize dependent df.  generalize dependent Tf.
  induction H; intros; subst.
  - apply qs_sq. apply subst_qual_subqual_monotone. auto. eapply closed_qual_subst1'; eauto.
  -  bdestruct (f =? 0).
    * pose (H' := H). subst. rewrite indexr_skips in H'; auto. simpl in H'. inversion H'. subst.
      rewrite subst1_qor_dist. rewrite subst1_just_fv0. erewrite subst1_qual_id; eauto. inversion H4; subst.
      + rewrite qor_idem. apply qs_sq; auto. rewrite subst1_tenv_length. eapply closed_qual_monotone; eauto. lia.
      + apply not_fresh_fresh_false in H1. contradiction.
    * rewrite subst1_qor_dist. destruct f. lia. rewrite <- subst1_just_fv.
      eapply qs_self; eauto. eapply @indexr_subst1 with (dx:=df') in H; try lia. eauto.
      eapply closed_qual_subst1; eauto.
    -  bdestruct (f =? 0).
    * pose (H' := H). subst. rewrite indexr_skips in H'; auto. simpl in H'. inversion H'. subst.
      rewrite subst1_qor_dist. rewrite subst1_just_fv0. erewrite subst1_qual_id; eauto. inversion H4; subst.
      + rewrite qor_idem. apply qs_sq; auto. rewrite subst1_tenv_length. eapply closed_qual_monotone; eauto. lia.
      + apply not_fresh_fresh_false in H1. contradiction.
    * rewrite subst1_qor_dist. destruct f. lia. rewrite <- subst1_just_fv.
      eapply qs_self_all; eauto. eapply @indexr_subst1 with (dx:=df') in H; try lia. eauto.
      eapply closed_qual_subst1; eauto.
  - bdestruct (x =? 0).
    * subst. pose (H' := H). subst. rewrite indexr_skips in H'; auto. simpl in H'. inversion H'. subst.
      rewrite subst1_just_fv0. erewrite subst1_qual_id; eauto. inversion H5; subst.
      + apply qs_sq. auto. rewrite subst1_tenv_length. eapply closed_qual_monotone; eauto. lia.
      + apply not_fresh_fresh_false in H2. contradiction.
    * destruct x. lia. rewrite <- subst1_just_fv. eapply qs_qvar. apply @indexr_subst1 with (Tx := Tf)(dx:=df') in H; try lia.
      eauto. eapply closed_ty_subst1; eauto. eapply closed_qual_subst1; eauto. eauto.
  - bdestruct (x =? 0).
    * subst. pose (H' := H). subst. rewrite indexr_skips in H'; auto. simpl in H'. inversion H'.
    * destruct x. lia. rewrite <- subst1_just_fv. eapply qs_qvar_ty. apply @indexr_subst1_ty with (Tx := Tf)(dx:=df') in H; try lia.
      eauto. eapply closed_ty_subst1; eauto. eapply closed_qual_subst1; eauto. eauto.
  - repeat rewrite subst1_qor_dist. eapply qs_cong; eauto. eapply closed_qual_subst1'; eauto.
  - eapply qs_trans. eapply IHqstp1; eauto. eauto.
    Unshelve. all : auto.
Qed.

Lemma subst_ty_qstp :  forall {Γ T d d' Σ d1 d2},
    qstp (Γ ++ [(bind_ty, false, T, d)]) Σ d1 d2 ->
    closed_ty 0 0 (length Σ) T ->
    closed_Qual 0 0 (length Σ) d'↑ ->
    Substq d d' ->
    qstp ({0 |-> T ~ d' }ᴳ Γ) Σ ({0 |-> d' }ᵈ d1) ({0 |-> d' }ᵈ d2).
Proof. intros Γ T d d' Σ d1 d2 H. remember (Γ ++ [(bind_ty, false, T, d)]) as Γ'.
  generalize dependent Γ. generalize dependent d.  generalize dependent T.
  induction H; intros; subst.
  - apply qs_sq. apply subst_qual_subqual_monotone. auto. eapply closed_qual_subst1'; eauto.
  -  bdestruct (f =? 0).
    * pose (H' := H). subst. rewrite indexr_skips in H'; auto. simpl in H'. inversion H'.
    * rewrite subst1_qor_dist. destruct f. lia. rewrite <- subst1_just_fv.
      eapply qs_self; eauto. eapply @indexr_subst1 with (dx:=d') in H; try lia. eauto.
      eapply closed_qual_subst1; eauto.
  -  bdestruct (f =? 0).
    * pose (H' := H). subst. rewrite indexr_skips in H'; auto. simpl in H'. inversion H'.
    * rewrite subst1_qor_dist. destruct f. lia. rewrite <- subst1_just_fv.
      eapply qs_self_all; eauto. eapply @indexr_subst1 with (dx:=d') in H; try lia. eauto.
      eapply closed_qual_subst1; eauto.
  - bdestruct (x =? 0).
    * subst. pose (H' := H). subst. rewrite indexr_skips in H'; auto. simpl in H'. inversion H'.
    * destruct x. lia. rewrite <- subst1_just_fv. eapply qs_qvar.
      apply @indexr_subst1 with (Tx := T)(dx:=d') in H; try lia.
      simpl in H. eauto. eapply closed_ty_subst1; eauto. eapply closed_qual_subst1; eauto. eauto.
  - bdestruct (x =? 0).
    * subst. pose (H' := H). erewrite indexr_skips in H'; auto. simpl in H'. inversion H'. subst.
      rewrite subst1_just_fv0. erewrite subst1_qual_id; eauto. inversion H5; subst.
      + apply qs_sq. auto. erewrite subst1_tenv_length. eapply closed_qual_monotone; eauto. lia.
      + apply not_fresh_fresh_false in H2. contradiction.
    * destruct x. lia. rewrite <- subst1_just_fv. eapply qs_qvar_ty.
      apply @indexr_subst1_ty with (Tx := T)(dx:=d') in H; try lia. simpl in H. eauto.
      eapply closed_ty_subst1; eauto. eapply closed_qual_subst1; eauto. eauto.
  - repeat rewrite subst1_qor_dist. eapply qs_cong; eauto. eapply closed_qual_subst1'; eauto.
  - eapply qs_trans. eapply IHqstp1; eauto. eauto.
  Unshelve. all : auto.
Qed.

Lemma subst_stp : forall{T1 T2},
    forall {Γ b Tf df df' Σ d1 d2},
      stp (Γ ++ [(bind_tm, b,Tf,df)]) Σ T1 d1 T2 d2 ->
      closed_ty 0 0  (‖Σ‖) Tf ->
      closed_Qual 0 0 (‖Σ‖) df'↑ ->
      Substq df df' ->
      stp ({ 0 |-> Tf ~ df' }ᴳ Γ) Σ
          ({ 0 |-> Tf ~ df' }ᵀ T1) ({ 0 |-> df' }ᵈ d1)
          ({ 0 |-> Tf ~ df' }ᵀ T2) ({ 0 |-> df' }ᵈ d2).
  intros T1 T2 Γ b Tf df df' Σ d1 d2 HS.
  remember (Γ ++ [(bind_tm, b, Tf, df)]) as Γ'.
  generalize dependent Γ. generalize dependent df.  generalize dependent Tf. induction HS; intros; subst.
  - (* TTop *) simpl. constructor. eapply closed_ty_subst1'; eauto. eapply subst_qstp; eauto.
  - (* TVarF x *) simpl.  (bdestruct (x =? 0)).
    * (*x is 0 *) rewrite indexr_skips in H; simpl; auto; try lia. simpl in H. subst. simpl in H.
      inversion H. subst. eapply subst_qstp in H0; eauto. eapply stp_refl; eauto.
      eapply closed_ty_monotone; eauto. lia.

    * (*x is in Γ0*) assert (Hx: 1 <= x); try lia. destruct x; try lia.
      destruct v. destruct p. specialize (@subst_qstp _ _  _ _ df' _ _ _ H0); intuition.
      eapply stp_refl; eauto. constructor. erewrite subst1_tenv_length.
      erewrite <-  indexr_insert_ge in  H.  replace (Γ0 ++  [])  with Γ0 in H.
      apply indexr_var_some' in  H. intuition. intuition.
      intuition.
  - (* TVarF x  trans *)
    specialize (@indexr_subst1_ty'' x Γ0 b Tf df false T1). intros.
    specialize (H4 d0). intuition. specialize (H5 df').  destruct H5.
    * (*x is not  in 0 *)
      assert  (Nat.eqb x 0  = false ).  { eapply Nat.eqb_neq; lia. }  simpl.  rewrite H6.
      econstructor. erewrite subst1_ty_id in H5; eauto.  auto.
      specialize (IHHS Tf df Γ0). intuition.
      erewrite subst1_ty_id in H8; eauto.
  - (* TAll *) simpl. inversion H. inversion H0. subst.  econstructor; eauto.
    1,2: constructor; try eapply closed_ty_subst1'; eauto; eapply closed_qual_subst1'; eauto.
    eapply subst_qstp; eauto.
    specialize (IHHS2 Tf df ((bind_ty, false, T3, d3) :: (bind_tm, true, TAll d1 d2 T1 T2, {♦}) :: Γ0)). intuition.
    unfold open_ty' in *. unfold open_ty in *.
    unfold openq' in *. unfold openq in *.
    rewrite app_length in *. rewrite subst1_tenv_length. simpl in *.
    replace (‖Γ0‖ + 1) with (S (‖Γ0‖)) in *; try lia.
    erewrite <- open_subst1_ty_comm in H6; eauto. erewrite <- open_subst1_ty_comm in H6; eauto.
    erewrite <- open_subst1_ty_comm in H6; eauto. erewrite <- open_subst1_ty_comm in H6; eauto.
    erewrite <- open_subst1_qual_comm in H6; eauto. erewrite <- open_subst1_qual_comm in H6; eauto.
    erewrite <- open_subst1_qual_comm in H6; eauto. erewrite <- open_subst1_qual_comm in H6; eauto.
  - simpl. constructor. eapply subst_qstp; eauto.
  - specialize (stp_closed HS1). intuition. specialize (stp_closed HS2). intuition.
    simpl. constructor. eapply subst_qstp; eauto.
    all : repeat erewrite subst1_ty_id; eauto. eapply closed_qual_subst1'; eauto.
  - simpl. constructor. inversion H. subst. 2 : inversion H0. subst.
    1,2: constructor; try eapply closed_ty_subst1'; eauto; eapply closed_qual_subst1'; eauto.
    eapply subst_qstp; eauto. eapply IHHS1; eauto.
    unfold open_ty' in *. unfold open_ty in *.
    unfold openq' in *. unfold openq in *.
    rewrite app_length in *. rewrite subst1_tenv_length. simpl in *.
    replace (‖Γ0‖ + 1) with (S (‖Γ0‖)) in *; try lia.
    specialize (IHHS2 Tf df ((bind_tm, false, T3, d3) :: (bind_tm, true, TFun d1 d2 T1 T2, {♦}) :: Γ0)). intuition. rename H6 into IHHS2. simpl in IHHS2.
    erewrite <- open_subst1_ty_comm in IHHS2; eauto. erewrite <- open_subst1_ty_comm in IHHS2; eauto.
    erewrite <- open_subst1_ty_comm in IHHS2; eauto. erewrite <- open_subst1_ty_comm in IHHS2; eauto.
    erewrite <- open_subst1_qual_comm in IHHS2; eauto. erewrite <- open_subst1_qual_comm in IHHS2; eauto.
    erewrite <- open_subst1_qual_comm in IHHS2; eauto. erewrite <- open_subst1_qual_comm in IHHS2; eauto.
  - eapply s_trans. eapply IHHS1; eauto. eapply IHHS2; eauto.
Qed.

Lemma subst_ty_stp : forall{T1 T2},
    forall {Γ T d d' Σ d1 d2},
      stp (Γ ++ [(bind_ty, false, T, d)]) Σ T1 d1 T2 d2 ->
      closed_ty 0 0 (‖Σ‖) T ->
      closed_Qual 0 0 (‖Σ‖) d'↑ ->
      Substq d d' ->
      stp ({ 0 |-> T ~ d' }ᴳ Γ) Σ
          ({ 0 |-> T ~ d' }ᵀ T1) ({ 0 |-> d' }ᵈ d1)
          ({ 0 |-> T ~ d' }ᵀ T2) ({ 0 |-> d' }ᵈ d2).
 Proof.   intros T1 T2 Γ T d d' Σ d1 d2 HS.
  remember (Γ ++ [(bind_ty, false, T, d)]) as Γ'.
  generalize dependent Γ.  generalize dependent T.  induction HS; intros; subst.
  - (* TTop *) simpl. constructor. eapply closed_ty_subst1'; eauto. eapply subst_ty_qstp; eauto.
  - (* TVarF x *) simpl.  (bdestruct (x =? 0)).
    * (*x is 0 *)
    rewrite indexr_skips in H; simpl; auto; try lia. simpl in H. subst. simpl in H.
      inversion H. subst. eapply subst_ty_qstp in H0; eauto. eapply stp_refl; eauto. eapply closed_ty_monotone; eauto. lia.

    * (*x is in Γ0*) assert (Hx: 1 <= x); try lia. destruct x; try lia.
      destruct v. destruct p. specialize (@subst_ty_qstp _ _  _ d' _ _ _ H0); intuition.
      eapply stp_refl; eauto. constructor. erewrite subst1_tenv_length.
      erewrite <-  indexr_insert_ge in  H.  replace (Γ0 ++  [])  with Γ0 in H.
      apply indexr_var_some' in  H. intuition. intuition.
      intuition.
  - (* TVarF trans *) simpl. (bdestruct (x =? 0)).
    * (*x is 0 *) subst. eapply @indexr_subst1_ty'  in H. intuition. subst.
    specialize (IHHS T1 Γ0). intuition. erewrite subst1_ty_id in H5; eauto.

    * (*x is in Γ0*) intuition. apply @indexr_subst1_ty with (Tx := T)(dx :=d') in H; try lia.
    econstructor; eauto.
    erewrite subst1_ty_id; auto. apply H0.
  - (* TAll *) simpl. inversion H0. inversion H. subst. econstructor.
    1,2: constructor; try eapply closed_ty_subst1'; eauto; eapply closed_qual_subst1'; eauto.
    eapply subst_ty_qstp; eauto. eapply IHHS1; eauto.
    unfold open_ty' in *. unfold open_ty in *.
    unfold openq' in *. unfold openq in *.
    rewrite app_length in *. rewrite subst1_tenv_length. simpl in *.
    replace (‖ Γ0 ‖ + 1) with (S (‖ Γ0 ‖)) in *; try lia.
    specialize (IHHS2 T  ((bind_ty, false, T3, d3) :: (bind_tm, true, TAll d1 d2 T1 T2, {♦}) :: Γ0)). simpl in IHHS2. intuition.
    rename H6 into IHHS2.
    replace (‖Γ0‖ + 1) with (S (‖Γ0‖)) in *; try lia.
    erewrite <- open_subst1_ty_comm in IHHS2; eauto. erewrite <- open_subst1_ty_comm in IHHS2; eauto.
    erewrite <- open_subst1_ty_comm in IHHS2; eauto. erewrite <- open_subst1_ty_comm in IHHS2; eauto.
    erewrite <- open_subst1_qual_comm in IHHS2; eauto. erewrite <- open_subst1_qual_comm in IHHS2; eauto.
    erewrite <- open_subst1_qual_comm in IHHS2; eauto. erewrite <- open_subst1_qual_comm in IHHS2; eauto.
  - constructor. eapply subst_ty_qstp; eauto.
  - intuition. specialize (stp_closed HS1). intuition. specialize (stp_closed HS2). intuition.
    simpl. constructor. eapply subst_ty_qstp; eauto.
    all : repeat erewrite subst1_ty_id; eauto. eapply closed_qual_subst1'; eauto.
  - simpl. constructor. inversion H. subst. 2 : inversion H0. subst.
    1,2: constructor; try eapply closed_ty_subst1'; eauto; eapply closed_qual_subst1'; eauto.
    eapply subst_ty_qstp; eauto.  eapply IHHS1; eauto.
    unfold open_ty' in *. unfold open_ty in *.
    unfold openq' in *. unfold openq in *.
    rewrite app_length in *. rewrite subst1_tenv_length. simpl in *.
    replace (‖Γ0‖ + 1) with (S (‖Γ0‖)) in *; try lia.
    specialize (IHHS2 T ((bind_tm, false, T3, d3) :: (bind_tm, true, TFun d1 d2 T1 T2, {♦}) :: Γ0)). intuition.
    rename H6 into IHHS2. simpl in IHHS2.
    erewrite <- open_subst1_ty_comm in IHHS2; eauto. erewrite <- open_subst1_ty_comm in IHHS2; eauto.
    erewrite <- open_subst1_ty_comm in IHHS2; eauto. erewrite <- open_subst1_ty_comm in IHHS2; eauto.
    erewrite <- open_subst1_qual_comm in IHHS2; eauto. erewrite <- open_subst1_qual_comm in IHHS2; eauto.
    erewrite <- open_subst1_qual_comm in IHHS2; eauto. erewrite <- open_subst1_qual_comm in IHHS2; eauto.
  - eapply s_trans'. eapply IHHS1; eauto. eapply IHHS2; eauto.
Qed.

Lemma or_false_elim : forall A, (A \/ False) = A.
intros. apply PropExtensionality.propositional_extensionality. intuition.
Qed.

Lemma un_subst1_qual_open : forall {v dx q l}, closed_Qual 0 0 l dx↑ -> {0 |-> dx }ᵈ ([[v ~> ∅ ]]ᵈ q) = {0 |-> dx }ᵈ q -> [[v ~> ∅ ]]ᵈ q = q.
intros. qual_destruct q. qual_destruct dx. apply Q_lift_eq' in H0.
#[local] Hint Resolve n_reflect_true : bdestruct.
unfold_q. inversion H0. clear H0.
bdestruct (bvs v); eauto.
apply Q_lift_eq. Qcrush.
bdestruct (fvs 0); Qcrush; bdestruct (n_or fvs n_empty 0); Qcrush.
#[local] Remove Hints n_reflect_true : bdestruct.
  - assert (notin: N_lift bvs0 x = False). { apply PropExtensionality.propositional_extensionality; intuition eauto. }
    eapply FunctionalExtensionality.equal_f with (x:=x) in H4; repeat rewrite or_false_elim in H4.
    rewrite notin in *. rewrite H4. eauto.
  - assert (notin: N_lift bvs0 x = False). { apply PropExtensionality.propositional_extensionality; intuition eauto. }
    eapply FunctionalExtensionality.equal_f with (x:=x) in H4; repeat rewrite or_false_elim in H4.
    rewrite H4. eauto.
Qed.

Lemma not_free_subst1_ty_iff : forall {v Tx dx T l}, closed_ty 0 0 l Tx -> closed_Qual 0 0 l dx ↑ -> not_free v T <-> not_free v ({0 |-> Tx ~ dx }ᵀ T).
  intros. unfold not_free. intuition.
  - replace (∅) with ({0 |-> dx }ᵈ ∅); auto. replace (TUnit) with ({0 |-> Tx ~ dx }ᵀ TUnit); auto.
    erewrite <- subst1_open_ty_comm; eauto. rewrite H1. auto.
  - replace (∅) with ({0 |-> dx }ᵈ ∅) in H1; auto. replace (TUnit) with ({0 |-> Tx ~ dx }ᵀ TUnit) in H1; auto.
    erewrite <- subst1_open_ty_comm in H1; eauto.
    generalize dependent v. induction T; intros; simpl; intuition;
    simpl in H1; inversion H1; f_equal; intuition; try solve [eapply un_subst1_qual_open; eauto].
    destruct v; auto.
    destruct (v0 =? i) eqn:Heqvi; intuition.
Qed.

Lemma qor_empty_left : forall {d}, (q_empty ⊔ d) = d.
intros. apply Q_lift_eq. rewrite Q_lift_or. Qcrush.
Qed.

Lemma substitution_gen :
  forall {t Γ φ bx Tx dx dx' Σ T d}, dx' ⊓ φ ⊑↑ dx ->
      has_type (Γ ++ [(bind_tm, bx,Tx,dx)]) φ Σ t T d -> Substq dx dx' ->
        forall {tx}, vtp Σ tx Tx dx' ->
                        has_type ({ 0 |-> Tx ~ dx' }ᴳ Γ) ({ 0 |-> dx' }ᵈ φ) Σ
                                 ({ 0 |-> tx  }ᵗ t)
                                 ({ 0 |-> Tx ~ dx' }ᵀ T)
                                 ({ 0 |-> dx' }ᵈ d).
  intros t Γ φ bx Tx dx dx' Σ T d Hsep (* φ Hphi *) HT HSubst tx HTx. specialize (vtp_closed HTx) as Hclx.
  specialize (vtp_saturated HTx) as Hsatx. destruct Hsatx as [Htsatx Hssatx].
  simpl in Hclx. intuition. remember (Γ ++ [(bind_tm, bx,Tx, dx)]) as Γ'.
  generalize dependent Γ.
  induction HT; intros; subst; pose (φs := {0 |-> dx' }ᵈ φ); replace ({0 |-> dx' }ᵈ φ) with φs in *; auto.
  - (* ttabs *) simpl. eapply t_tabs; auto. eapply closed_tm_subst1'; eauto.
    inversion H3. subst. constructor; try eapply closed_ty_subst1'; eauto; eapply closed_qual_subst1'; eauto.
    eapply closed_qual_subst1'; eauto. apply subst_qual_subqual_monotone. auto. eauto.

    apply subst1_senv_saturated; auto.

    (* 1. instantiate the IH *)
    replace (length (Γ0 ++ [(bind_tm, bx, Tx, dx)])) with (S (‖Γ0‖)) in IHHT.
    rewrite subst1_tenv_length. rewrite app_comm_cons in IHHT.
    remember (df ⊔ $!(S (‖Γ0‖)) ⊔ $!(S (S (‖Γ0‖))) ⊔ {♦}) as DF.
    replace ({0 |-> dx' }ᵈ df ⊔ $!(‖Γ0‖) ⊔ $!(S (‖Γ0‖)) ⊔ {♦}) with ({0 |-> dx' }ᵈ DF).
    (* remember (φ' ⊔ $!(S (‖Γ0‖)) ⊔ $!(S (S (‖Γ0‖)))) as φ''. *)
    assert (Hsep' : dx' ⊓ DF ⊑↑ dx). {
      subst. repeat rewrite qand_qor_dist_l. erewrite qglb_disjoint_freshv; eauto. erewrite qglb_disjoint_freshv; eauto.
      erewrite qglb_disjoint_fresh; eauto. repeat rewrite qor_empty_left. apply Substq_non_fresh in HSubst.
      eapply (Subq_trans _ Hsep).
    }
    intuition. rename H8 into IHHT. specialize IHHT with (Γ := (((bind_ty, false,T1, d1):: ((bind_tm, true, TAll d1 d2 T1 T2, df)) :: Γ0))).
    intuition. rename H8 into IHHT.
    (* 2. reason about opening and subst, apply IH *)
    unfold open_tm' in *. unfold open_ty' in *. unfold open_ty in *.
    unfold openq' in *. unfold openq in *.
    rewrite app_length in IHHT. rewrite subst1_tenv_length. simpl in *.
    replace (‖Γ0‖ + 1) with (S (‖Γ0‖)) in IHHT; try lia.
    erewrite <- open_subst1_tm_comm in IHHT; eauto. erewrite <- open_subst1_tm_comm in IHHT; eauto.
    erewrite <- open_subst1_ty_comm in IHHT; eauto. erewrite <- open_subst1_ty_comm in IHHT; eauto.
    erewrite <- open_subst1_qual_comm in IHHT; eauto. erewrite <- open_subst1_qual_comm in IHHT; eauto.

    subst. rewrite subst1_qor_dist. repeat rewrite subst1_qor_dist. f_equal.
    rewrite app_length. simpl. lia.
  - (* t_tapp *) intuition. rename H10 into IHHT. simpl.
    replace ({ 0 |-> dx' }ᵈ (openq df d1 d2)) with
      (openq ({ 0 |-> dx' }ᵈ df) ({ 0 |-> dx' }ᵈ d1) ({ 0 |-> dx' }ᵈ d2)).
    replace ({0 |-> Tx ~ dx' }ᵀ (T2 <~ᵀ TUnit ~ ∅; T1 ~ d1)) with
      (({0 |-> Tx ~ dx' }ᵀ T2) <~ᵀ TUnit ~ ∅ ; ({0 |-> Tx ~ dx' }ᵀ T1) ~ ({0 |-> dx' }ᵈ d1)).
    apply t_tapp. apply IHHT; auto.
    eapply closed_ty_subst1; eauto.
    2: eapply closed_qual_subst1; eauto.
    1-2: rewrite app_length in *; simpl in *; rewrite subst1_tenv_length.
    1-2: replace  (S (‖ Γ0 ‖)) with (‖ Γ0 ‖ + 1); eauto; lia.
    1,4: unfold openq; replace (∅) with ({0 |-> dx' }ᵈ ∅) by solve [apply subst1_qual_empty];
        erewrite <- subst1_open_qual_comm; eauto;
        erewrite <- subst1_open_qual_comm; eauto.
    * unfold openq. apply subst_qual_subqual_monotone. auto.
    * apply subst1_senv_saturated; auto.
    * eauto.
    * apply subst_qual_subqual_monotone. auto.
    * apply subst1_senv_saturated; auto.
    * erewrite <- not_free_subst1_ty_iff; eauto.
    * replace (∅) with ({0 |-> dx' }ᵈ ∅) at 1; auto.
      unfold open_ty. repeat erewrite subst1_open_ty_comm; eauto.
    * unfold openq. repeat erewrite <- subst1_open_qual_comm; eauto.
  - (* t_tapp_fresh *) intuition. rename H15 into IHHT. simpl.
    replace ({ 0 |-> dx' }ᵈ (openq df d1 d2)) with
               (openq ({ 0 |-> dx' }ᵈ df) ({ 0 |-> dx' }ᵈ d1) ({ 0 |-> dx' }ᵈ d2)).
    replace ({0 |-> Tx ~ dx' }ᵀ (T2 <~ᵀ TUnit ~ ∅; T1 ~ d1)) with
               (({0 |-> Tx ~ dx' }ᵀ T2) <~ᵀ TUnit ~ ∅; ({0 |-> Tx ~ dx' }ᵀ T1) ~ ({0 |-> dx' }ᵈ d1)).
    (*separation/overap is preserved after substitution*)
    assert (Hoverlap: {0 |-> dx' }ᵈ (df' ⊓ d1') = {0 |-> dx' }ᵈ df' ⊓ {0 |-> dx' }ᵈ d1'). {
      symmetry. eapply subst1_preserves_separation; eauto.
    }
    eapply t_tapp_fresh with (df':=({0 |-> dx' }ᵈ df')) (d1':=({0 |-> dx' }ᵈ d1')).
    replace (TAll (({0 |-> dx' }ᵈ df' ⋒ {0 |-> dx' }ᵈ d1')) ({0 |-> dx' }ᵈ d2) ({0 |-> Tx ~ dx' }ᵀ T1) ({0 |-> Tx ~ dx' }ᵀ T2))
      with  ({0 |-> Tx ~ dx' }ᵀ (TAll (df' ⋒ d1') d2 T1 T2)). auto.

    simpl. rewrite subst1_qor_dist. rewrite Hoverlap. rewrite subst1_fresh_id. auto.
    5 : unfold openq; replace (∅) with ({0 |-> dx' }ᵈ ∅) by solve [apply subst1_qual_empty];
        erewrite <- subst1_open_qual_comm; eauto; erewrite <- subst1_open_qual_comm; eauto.
    1,2,5,8,9 : apply subst_qual_subqual_monotone; auto.
    eapply closed_ty_subst1'; eauto. eapply closed_qual_subst1'; eauto.
    2 : intro Hfresh. 1,2 : erewrite <- not_free_subst1_ty_iff; eauto; apply Substq_non_fresh in HSubst.
    1,2 : eapply subst1_saturated; eauto.
    unfold openq; replace (∅) with ({0 |-> dx' }ᵈ ∅) by solve [apply subst1_qual_empty];
    erewrite <- subst1_open_qual_comm; eauto; erewrite <- subst1_open_qual_comm; eauto. 1,2: apply subst1_senv_saturated; auto.
    replace (∅) with ({0 |-> dx' }ᵈ ∅) at 1; auto. unfold open_ty. repeat erewrite subst1_open_ty_comm; eauto.
    unfold openq. repeat erewrite <- subst1_open_qual_comm; eauto.
  - (* t_base *) simpl. replace ({0 |-> dx' }ᵈ ∅) with (∅) by solve [symmetry; apply subst1_qual_empty].
    apply t_base; auto. eapply closed_qual_subst1'; eauto.
  - (* t_var *) simpl. (bdestruct (x =? 0)).
    * (*x is 0 *) rewrite indexr_skips in H0; simpl; auto; try lia. simpl in H0. subst. simpl in H0.
        qual_destruct dx'. inversion H0. subst. erewrite subst1_ty_id; eauto. inversion HSubst; subst.
        + (*subst fun, dx = dx' *)
          apply vtp_has_type in HTx.
          eapply weaken'; eauto. eapply subst_filter0; eauto.
          eapply closed_qual_subst1'; eauto.
        + (*subst arg, dx = df ⋒ dx = dx' ⋒ φ *)
          apply vtp_has_type in HTx.
          eapply weaken'; eauto.
          eapply @subst_qual_subqual_monotone with (df:=(fr, fvs, bvs, lcs)) in H3.
          subst φs. erewrite subst1_just_fv0 in H3. auto.
          eapply closed_qual_subst1'; eauto.
    * (*x is in Γ0*) assert (Hx: 1 <= x); try lia. destruct x; try lia.
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
    replace (length (Γ0 ++ [(bind_tm, bx, Tx, dx)])) with (S (‖Γ0‖)) in IHHT.
    rewrite subst1_tenv_length. rewrite app_comm_cons in IHHT. rewrite app_comm_cons in IHHT.
    remember (df ⊔ $!(S (‖Γ0‖)) ⊔ $!(S (S (‖Γ0‖))) ⊔ {♦}) as DF.
    replace ({0 |-> dx' }ᵈ df ⊔ $!(‖Γ0‖) ⊔ $!(S (‖Γ0‖)) ⊔ {♦}) with ({0 |-> dx' }ᵈ DF).
    (* remember (φ' ⊔ $!(S (‖Γ0‖)) ⊔ $!(S (S (‖Γ0‖)))) as φ''. *)
    assert (Hsep' : dx' ⊓ DF ⊑↑ dx). {
      subst. repeat rewrite qand_qor_dist_l. erewrite qglb_disjoint_freshv; eauto. erewrite qglb_disjoint_freshv; eauto.
      erewrite qglb_disjoint_fresh; eauto. repeat rewrite qor_empty_left. apply Substq_non_fresh in HSubst. Qcrush.
    }
    intuition. rename H8 into IHHT. specialize IHHT with (Γ := (((bind_tm, false,T1, d1) :: (bind_tm, true, (TFun d1 d2 T1 T2), df) :: Γ0))).
    (* 2. reason about opening and subst, apply IH *)
    unfold open_tm' in *. unfold open_ty' in *. unfold open_ty in *.
    unfold openq' in *. unfold openq in *.
    rewrite app_length in IHHT. rewrite subst1_tenv_length. simpl in *.
    replace (‖Γ0‖ + 1) with (S (‖Γ0‖)) in IHHT; try lia.
    erewrite <- open_subst1_tm_comm in IHHT; eauto. erewrite <- open_subst1_tm_comm in IHHT; eauto.
    erewrite <- open_subst1_ty_comm in IHHT; eauto. erewrite <- open_subst1_ty_comm in IHHT; eauto.
    erewrite <- open_subst1_qual_comm in IHHT; eauto. erewrite <- open_subst1_qual_comm in IHHT; eauto.
    subst. rewrite subst1_qor_dist. repeat rewrite subst1_qor_dist. f_equal.
    repeat rewrite <- subst1_just_fv. rewrite app_length. simpl. lia.
  - (* t_app *) intuition. rename H7 into IHHT1. rename H6 into IHHT2. simpl.
    replace ({ 0 |-> dx' }ᵈ (openq df d1 d2)) with
               (openq ({ 0 |-> dx' }ᵈ df) ({ 0 |-> dx' }ᵈ d1) ({ 0 |-> dx' }ᵈ d2)).
    replace ({0 |-> Tx ~ dx' }ᵀ (T2 <~ᵀ TUnit ~ ∅; T1 ~ d1)) with
               (({0 |-> Tx ~ dx' }ᵀ T2) <~ᵀ TUnit ~ ∅; ({0 |-> Tx ~ dx' }ᵀ T1) ~ ({0 |-> dx' }ᵈ d1)).
    apply t_app with (T1:= { 0 |-> Tx ~ dx' }ᵀ T1) (df:=({0 |-> dx' }ᵈ df)).
    replace (TFun ({0 |-> dx' }ᵈ d1) ({0 |-> dx' }ᵈ d2) ({0 |-> Tx ~ dx' }ᵀ T1) ({0 |-> Tx ~ dx' }ᵀ T2))
            with ({ 0 |->Tx ~ dx' }ᵀ (TFun d1 d2 T1 T2)); auto.
    eapply IHHT2; eauto.
    1,4: unfold openq; replace (∅) with ({0 |-> dx' }ᵈ ∅) by solve [apply subst1_qual_empty];
        erewrite <- subst1_open_qual_comm; eauto; erewrite <- subst1_open_qual_comm; eauto.
    * apply subst_qual_subqual_monotone. unfold openq in H4. auto.
    * apply subst1_senv_saturated; auto.
    * eauto.
    * erewrite <- not_free_subst1_ty_iff; eauto.
    * replace (∅) with ({0 |-> dx' }ᵈ ∅) at 1; auto. unfold open_ty. repeat erewrite subst1_open_ty_comm; eauto.
    * unfold openq. repeat erewrite <- subst1_open_qual_comm; eauto.
  - (* t_app_fresh *) intuition. rename H13 into IHHT1. rename H12 into IHHT2. simpl.
    replace ({ 0 |-> dx' }ᵈ (openq df d1 d2)) with
               (openq ({ 0 |-> dx' }ᵈ df) ({ 0 |-> dx' }ᵈ d1) ({ 0 |-> dx' }ᵈ d2)).
    replace ({0 |-> Tx ~ dx' }ᵀ (T2 <~ᵀ TUnit ~ ∅; T1 ~ d1)) with
               (({0 |-> Tx ~ dx' }ᵀ T2) <~ᵀ TUnit ~ ∅; ({0 |-> Tx ~ dx' }ᵀ T1) ~ ({0 |-> dx' }ᵈ d1)).
    (*separation/overap is preserved after substitution*)
    assert (Hoverlap: {0 |-> dx' }ᵈ (df' ⊓ d1') = {0 |-> dx' }ᵈ df' ⊓ {0 |-> dx' }ᵈ d1'). {
      symmetry. eapply subst1_preserves_separation; eauto.
    }
    eapply t_app_fresh with (T1:= { 0 |-> Tx ~ dx' }ᵀ T1) (df:=({0 |-> dx' }ᵈ df)) (d1:=({0 |-> dx' }ᵈ d1)) (df':=({0 |-> dx' }ᵈ df')) (d1':=({0 |-> dx' }ᵈ d1')); eauto.
    replace (TFun (({0 |-> dx' }ᵈ df' ⋒ {0 |-> dx' }ᵈ d1')) ({0 |-> dx' }ᵈ d2) ({0 |-> Tx ~ dx' }ᵀ T1) ({0 |-> Tx ~ dx' }ᵀ T2))
      with  ({0 |-> Tx ~ dx' }ᵀ (TFun (df' ⋒ d1') d2 T1 T2)). auto.
    simpl. rewrite subst1_qor_dist. rewrite Hoverlap. rewrite subst1_fresh_id. auto.
5 : unfold openq; replace (∅) with ({0 |-> dx' }ᵈ ∅) by solve [apply subst1_qual_empty];
        erewrite <- subst1_open_qual_comm; eauto; erewrite <- subst1_open_qual_comm; eauto.
    1,2,5,6,7 : apply subst_qual_subqual_monotone; auto.
    intro Hfresh. 1,2 : erewrite <- not_free_subst1_ty_iff; eauto; apply Substq_non_fresh in HSubst.
    1,2 : eapply subst1_saturated; eauto.
    unfold openq; replace (∅) with ({0 |-> dx' }ᵈ ∅) by solve [apply subst1_qual_empty];
    erewrite <- subst1_open_qual_comm; eauto; erewrite <- subst1_open_qual_comm; eauto. apply subst1_senv_saturated; auto.
    replace (∅) with ({0 |-> dx' }ᵈ ∅) at 1; auto. unfold open_ty. repeat erewrite subst1_open_ty_comm; eauto.
    unfold openq. repeat erewrite <- subst1_open_qual_comm; eauto.
  - (* t_loc *) rewrite subst1_qor_dist. erewrite @subst1_qual_id with (q:=(&!l)); eauto. simpl. erewrite subst1_ty_id; eauto.
    erewrite subst1_qual_id; eauto. apply t_loc; auto. eapply closed_qual_subst1'; eauto.
    erewrite <- @subst1_qual_id with (q:=(&!l)); eauto. eapply subst_qual_subqual_monotone; eauto.
    2 : erewrite <- @subst1_qual_id with (q:=q); eauto; eapply subst_qual_subqual_monotone; eauto.
    all : apply indexr_var_some' in H3; eapply just_loc_closed; eauto.
  - (* t_ref *) rewrite subst1_qor_dist. rewrite subst1_qual_fresh. simpl. apply t_ref; auto.
    erewrite subst1_ty_id; eauto. erewrite <- subst1_qual_fresh.
    eapply subst_qual_subqual_monotone; eauto. apply subst1_non_fresh; eauto.
  - (* t_deref *) simpl. apply t_deref with (d := { 0 |-> dx' }ᵈ d); auto.
    apply subst1_non_fresh; eauto. apply subst_qual_subqual_monotone. auto.
    apply subst1_senv_saturated; auto.
  - (* t_assign *) rewrite subst1_qual_empty in *. simpl. simpl in IHHT1.
    apply t_assign with (T:={0 |-> Tx ~ dx' }ᵀ T) (d:=({0 |-> dx' }ᵈ d)) (d1:=({0 |-> dx' }ᵈ d1)); auto.
    apply subst1_non_fresh; eauto.
  - (* t_sub *) apply t_sub with (T1:={ 0 |-> Tx ~ dx' }ᵀ T1) (d1:={ 0 |-> dx' }ᵈ d1).
    eapply IHHT; eauto. eapply subst_stp; eauto. apply subst_qual_subqual_monotone; auto.
    apply subst1_senv_saturated; auto.
  Unshelve. Qcrush. all : auto.
Qed.

Lemma qor_assoc : forall {q1 q2 q3}, (q1 ⊔ (q2 ⊔ q3)) = ((q1 ⊔ q2) ⊔ q3).
intros. apply Q_lift_eq. Qcrush.
Qed.

(* case for t_app *)
Lemma substitution1 : forall {t bf Tf df bx Tx dx Σ T d},
    has_type [(bind_tm, bx,Tx,dx) ; (bind_tm, bf,Tf,df)] (df ⊔ $!0 ⊔ $!1 ⊔ {♦}) Σ t T d ->
    forall {vf}, vtp Σ vf Tf df -> ♦∉ df ->
        forall {vx}, vtp Σ vx Tx dx -> ♦∉ dx ->
                    has_type [] (df ⊔ dx ⊔ {♦}) Σ
                             ({ 0 |-> vf ; vx }ᵗ t)
                             ({ 0 |-> Tf ~ df ; Tx ~ dx }ᵀ T)
                             ({ 0 |-> df ; dx }ᵈ d).
  intros. specialize (vtp_closed H0) as Hclf. specialize (vtp_closed H2) as Hclx.
  intuition. replace ([(bind_tm, bx,Tx, dx); (bind_tm, bf,Tf, df)]) with ([(bind_tm, bx,Tx,dx)] ++ [(bind_tm, bf,Tf, df)]) in H; auto.
  remember (df ⊔ $!0 ⊔ $!1 ⊔ {♦}) as DF.
  assert (Hsepf : df ⊓ DF ⊑↑ df). { Qcrush. }
  eapply (substitution_gen Hsepf) in H; eauto.
  replace ({0 |-> Tf ~ df }ᴳ [(bind_tm, bx, Tx, dx)]) with ([] ++ [(bind_tm, bx, Tx, dx)]) in H.
  replace ({0 |-> df }ᵈ DF) with (df ⊔ $!0 ⊔ {♦}) in H.
  assert (Hsepf' : dx ⊓ (df ⊔ $!0 ⊔ {♦}) ⊑↑ dx). { Qcrush. }
  eapply (substitution_gen Hsepf') in H; eauto.
  replace ({0 |-> dx }ᵈ (df ⊔ $!0 ⊔ {♦})) with (df ⊔ dx ⊔ {♦}) in H. simpl in H. apply H.
  (*done, prove earlier replacements *)
  repeat rewrite subst1_qor_dist. rewrite subst1_just_fv0. erewrite subst1_qual_id; eauto.
(* rewrite subst1_fresh_id. auto. *)
  subst. repeat rewrite subst1_qor_dist. rewrite subst1_just_fv0. rewrite <- subst1_just_fv.
(* rewrite subst1_fresh_id. *)
  erewrite subst1_qual_id; eauto.
rewrite (@qor_assoc df df).
rewrite qor_idem. auto.
  simpl. erewrite subst1_qual_id; eauto. erewrite subst1_ty_id; eauto.
Qed.

(* t_app case *)
Lemma substitution_stp1 : forall{T1 T2},
    forall {bx Tx bf Tf df dx Σ d1 d2},
      stp ([(bind_tm, bx,Tx,dx); (bind_tm, bf,Tf,{♦})]) Σ T1 d1 T2 d2 ->
      closed_ty 0 0 (‖Σ‖) Tx ->
      closed_ty 0 0 (‖Σ‖) Tf ->
      closed_Qual 0 0 (‖Σ‖) df↑ -> closed_Qual 0 0 (‖Σ‖) dx↑ -> ♦∉ df -> ♦∉ dx ->
      stp [] Σ ({ 0 |-> Tf ~ df; Tx ~ dx }ᵀ T1) ({ 0 |-> df ; dx }ᵈ d1) ({ 0 |-> Tf ~ df ; Tx ~ dx }ᵀ T2) ({ 0 |-> df ; dx }ᵈ d2).
  intros. replace [(bind_tm, bx, Tx, dx); (bind_tm, bf, Tf,{♦})] with ([(bind_tm, bx, Tx, dx)] ++ [(bind_tm, bf, Tf,{♦})]) in H; auto.
  eapply @subst_stp with (df':=df) in H; auto.
  replace ({0 |-> Tf ~ df }ᴳ [(bind_tm, bx, Tx, dx)]) with ([(bind_tm, bx, Tx, dx)]) in H.
  replace ([(bind_tm, bx, Tx, dx)]) with ([] ++ [(bind_tm, bx, Tx, dx)]) in H; auto.
  eapply @subst_stp with (df':=dx) in H; auto. auto.
  simpl. erewrite subst1_ty_id; eauto. erewrite subst1_qual_id; eauto.
  replace ({♦}) with (∅ ⋒ df); auto.
Qed.

(* case for t_app_fresh *)
Lemma substitution2 : forall {t bf Tf df df' Tx dx dx' Σ T d},
    has_type [(bind_tm, false,Tx,(df' ⊓ dx') ⊔ {♦}) ; (bind_tm, bf,Tf,df)] (df ⊔ $!0 ⊔ $!1 ⊔ {♦}) Σ t T d ->
    forall {vf}, vtp Σ vf Tf df -> ♦∉ df -> df ⊑↑ df' -> closed_Qual 0 0 (‖Σ‖) df'↑ ->
        forall {vx}, vtp Σ vx Tx dx -> ♦∉ dx -> dx ⊑↑ dx' -> closed_Qual 0 0 (‖Σ‖) dx'↑ ->
                    has_type [] (df ⊔ dx ⊔ {♦}) Σ
                             ({ 0 |-> vf ; vx }ᵗ t)
                             ({ 0 |-> Tf ~ df ; Tx ~ dx }ᵀ T)
                             ({ 0 |-> df ; dx }ᵈ d).
  intros. specialize (vtp_closed H0) as Hclf. specialize (vtp_closed H4) as Hclx.
  assert (Hcl : closed_Qual 0 0 (‖ Σ ‖) (df' ⋒ dx')↑). { apply closed_qual_qor; auto. apply closed_qual_qand; auto. }
  intuition. replace ([(bind_tm, false,Tx, (df' ⋒ dx')); (bind_tm, bf,Tf, df)]) with ([(bind_tm, false,Tx, (df' ⋒ dx'))] ++ [(bind_tm, bf,Tf, df)]) in H; auto.
  remember (df ⊔ $!0 ⊔ $!1 ⊔ {♦}) as DF.
  assert (Hsepf : df ⊓ DF ⊑↑ df). { Qcrush. }
  eapply (substitution_gen Hsepf) in H; eauto.
  replace ({0 |-> Tf ~ df }ᴳ [(bind_tm, false, Tx, df' ⋒ dx')]) with ([(bind_tm, false, Tx, df' ⋒ dx')]) in H.
  replace ({0 |-> df }ᵈ DF) with (df ⊔ $!0 ⊔ {♦}) in H.
  assert (Hstparg : stp [] Σ Tx (df ⋒ dx) Tx (df' ⋒ dx')). { apply stp_refl; auto. constructor; auto. Qcrush. }
  eapply narrowing in H; eauto.
  assert (Hsepf' : dx ⊓ (df ⊔ $!0 ⊔ {♦}) ⊑↑ (df ⊓ dx) ⊔ {♦}). {
    repeat rewrite qand_qor_dist_l. erewrite qglb_disjoint_freshv; eauto. Qcrush.
  }
  replace ([(bind_tm, false, Tx, df ⋒ dx)]) with ([] ++ [(bind_tm, false, Tx, df ⋒ dx)]) in H.
  eapply (substitution_gen Hsepf') in H; eauto.
  replace ({0 |-> dx }ᵈ (df ⊔ $!0 ⊔ {♦})) with (df ⊔ dx ⊔ {♦}) in H. simpl in H. apply H.
  (*done, prove earlier replacements *)
  repeat rewrite subst1_qor_dist. rewrite subst1_just_fv0. erewrite subst1_qual_id; eauto. auto. intros. discriminate.
subst. repeat rewrite subst1_qor_dist. rewrite subst1_just_fv0. rewrite <- subst1_just_fv.
  erewrite subst1_qual_id; eauto. rewrite (@qor_assoc df df). rewrite qor_idem. auto.
  simpl. erewrite subst1_qual_id; eauto. erewrite subst1_ty_id; eauto.
Qed.

(* t_app_fresh case *)
Lemma substitution_stp2 : forall{T1 T2},
    forall {Tx bf Tf df df' dx dx' Σ d1 d2},
      stp ([(bind_tm, false,Tx,df' ⋒ dx'); (bind_tm, bf,Tf,{♦})]) Σ T1 d1 T2 d2 ->
      closed_ty 0 0 (‖Σ‖) Tx ->
      closed_ty 0 0 (‖Σ‖) Tf ->
      closed_Qual 0 0 (‖Σ‖) df'↑ -> closed_Qual 0 0 (‖Σ‖) dx'↑ -> ♦∉ df -> ♦∉ dx -> df ⊑↑ df' -> dx ⊑↑ dx' ->
      stp [] Σ ({ 0 |-> Tf ~ df; Tx ~ dx }ᵀ T1) ({ 0 |-> df ; dx }ᵈ d1) ({ 0 |-> Tf ~ df ; Tx ~ dx }ᵀ T2) ({ 0 |-> df ; dx }ᵈ d2).
  intros.  assert (Hcl : closed_Qual 0 0 (‖ Σ ‖) (df' ⋒ dx')↑). { apply closed_qual_qor; auto. apply closed_qual_qand; auto. }
  replace [(bind_tm, false, Tx, df' ⋒ dx'); (bind_tm, bf, Tf,{♦})] with ([(bind_tm, false, Tx, df' ⋒ dx')] ++ [(bind_tm, bf, Tf,∅ ⋒ df)]) in H; auto.
  eapply @subst_stp with (df':=df) in H; eauto.
  replace ({0 |-> Tf ~ df }ᴳ [(bind_tm, false, Tx, df' ⋒ dx' )]) with ([(bind_tm, false, Tx, df' ⋒ dx')]) in H.
  assert (H' : stp [(bind_tm, false, Tx, df ⋒ dx)] Σ ({0 |-> Tf ~ df }ᵀ T1) ({0 |-> df }ᵈ d1) ({0 |-> Tf ~ df }ᵀ T2) ({0 |-> df }ᵈ d2)). {
    eapply narrowing_stp; eauto. intros. discriminate. apply stp_refl; auto. constructor; auto. Qcrush.
  }
  replace ([(bind_tm, false, Tx, df ⋒ dx )]) with ([] ++ [(bind_tm, false, Tx, df ⋒ dx)]) in H'; auto.
  replace ([]) with ({0 |-> Tx ~ dx}ᴳ []); auto. eapply subst_stp; eauto.
  simpl. erewrite subst1_ty_id; eauto. erewrite subst1_qual_id; eauto.
Qed.

Lemma open_qual_mono : forall {d1 d1' d2 k}, d1 ⊑↑ d1' -> ([[ k ~> d1 ]]ᵈ d2) ⊑↑ ([[ k ~> d1' ]]ᵈ d2).
  intros. unfold_q. qual_destruct d2; qual_destruct d1'; qual_destruct d1. simpl.
#[local] Hint Resolve n_reflect_true : bdestruct.
bdestruct (bvs k); Qcrush.
#[local] Remove Hints n_reflect_true : bdestruct.
Qed.

Lemma open_qual_mono2 : forall {d1 d2 d2' k}, d2 ⊑↑ d2' -> ([[ k ~> d1 ]]ᵈ d2) ⊑↑ ([[ k ~> d1 ]]ᵈ d2').
  intros. unfold_q. qual_destruct d2; qual_destruct d2'; qual_destruct d1. simpl.
#[local] Hint Resolve n_reflect_true : bdestruct.
bdestruct (bvs0 k); bdestruct (bvs k); Qcrush.
#[local] Remove Hints n_reflect_true : bdestruct.
bdestruct (x =? k); Qcrush. exfalso; eauto.
Qed.

Lemma openq_mono : forall {d1 d1' d2 d2' d3 d3' f l},
    closed_Qual 0 f l d1'↑ -> closed_Qual 0 f l d2'↑ ->
    d1 ⊑↑ d1' -> d2 ⊑↑ d2' -> d3 ⊑↑ d3' -> (d3 <~ᵈ d1; d2) ⊑↑ (d3' <~ᵈ d1'; d2').
  intros. unfold openq.
  specialize (@open_qual_mono d1 d1' d3' 0 H1) as S1.
  specialize (@open_qual_mono2 d1 d3 d3' 0 H3) as S2.
  specialize (Subq_trans S2 S1) as S3. clear S1. clear S2.
  specialize (@open_qual_mono2 d2' _ _ 1 S3) as S4.
  eapply Subq_trans. 2: eauto. eapply open_qual_mono; eauto.
Qed.

Lemma open_ty'_closed : forall {l} {T} {A},
    closed_ty 0 0 l T ->
    closed_ty 0 2 l (T <~²ᵀ ([] : list A)).
  intros. unfold open_ty'. unfold open_ty.
  apply closed_ty_open_succ. auto. apply closed_ty_open_succ. auto.
Qed.

Lemma open_qual_qor_dist : forall {k d1 d2 d3}, ([[ k ~> d1  ]]ᵈ (d2 ⊔ d3)) = (([[ k ~> d1  ]]ᵈ d2) ⊔ ([[ k ~> d1  ]]ᵈ d3)).
  intros. qual_destruct d2; qual_destruct d3; qual_destruct d1; unfold_q.
#[local] Hint Resolve n_reflect_true : bdestruct.
apply Q_lift_eq. bdestruct (bvs k); bdestruct (bvs0 k); Qcrush.
#[local] Remove Hints n_reflect_true : bdestruct.
all: bdestruct (x =? k); Qcrush; exfalso; eauto.
Qed.

Lemma qfresh_true_open : forall {k d1 t t0 t1}, (♦∈? ([[k ~> d1 ]]ᵈ ((true,t,t0,t1)))) = true.
  intros. unfold_q. destruct (t0 k); auto.
Qed.

Lemma qfresh_true_openq : forall {d1 df t t0 t1}, (♦∈? (((true,t,t0,t1)) <~ᵈ df; d1)) = true.
  intros. unfold openq. unfold open_qual at 2. unfold qbvs, qfvs. simpl. destruct (t0 0). unfold "♦∈?" at 2. simpl. all: apply qfresh_true_open.
Qed.

(* Some distributive laws about openq and qqplus, required in the type safety proof for function application t_app. *)
Lemma open_qual_duplicate_eq : forall {k d1 d2 d}, ♦∈ d1 ->
  ([[ k ~> d1 ]]ᵈ d2 ⋓ d) = ([[ k ~> d1 ⋓ d ]]ᵈ d2 ⋓ d).
  intros. apply Q_lift_eq. qual_destruct d1. qual_destruct d2. unfold_q. destruct fr; auto.
#[local] Hint Resolve n_reflect_true : bdestruct.
bdestruct (bvs0 k); destruct (fr0); Qcrush.
#[local] Remove Hints n_reflect_true : bdestruct.
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
    closed_Qual 0 f (‖Σ‖) d1↑ -> closed_Qual 0 f (‖Σ‖) df↑ ->
    Σ → Σ' ∋ df ⊕ d' -> (d1 ⋒ df) = (d1 ⋒ (df ⋓ d')).
  intros. qual_destruct d1. qual_destruct df.
  inversion H1; subst.
  - unfold qqplus. destruct fr0; simpl. rewrite qor_empty_right. auto. auto.
  - assert (Hfresh: ~ N_lift lcs0 (‖Σ‖)). { inversion H0. unfold_N. unfold_q. intuition. eauto. }
     unfold_q. destruct fr0; auto; simpl. apply Q_lift_eq. Qcrush. exfalso; eauto.
Qed.

Lemma qqcap_fresh_l : forall {d1 df f Σ Σ' d'},
    closed_Qual 0 f (‖Σ‖) d1↑ -> closed_Qual 0 f (‖Σ‖) df↑ ->
    Σ → Σ' ∋ d1 ⊕ d' -> (d1 ⋒ df) = ((d1 ⋓ d') ⋒ df).
  intros. qual_destruct df. qual_destruct d1.
  inversion H1; subst.
  - unfold qqplus. destruct fr0; simpl. rewrite qor_empty_right. auto. auto.
  - assert (Hfresh: ~ N_lift lcs0 (‖Σ‖)). { inversion H0. unfold_N. unfold_Q. intuition. eauto. }
     unfold_q. destruct fr0; auto; simpl. apply Q_lift_eq. Qcrush. exfalso; eauto.
Qed.

Lemma openq_closed : forall {a b c f l},
    closed_qual 2 f l c -> closed_qual 0 f l a -> closed_qual 0 f l b -> closed_qual 0 f l (openq a b c).
  intros. unfold openq. erewrite open_qual_commute''; eauto.
Qed.

Lemma openQ_closed : forall {a b c f l},
    closed_Qual 2 f l c↑ -> closed_Qual 0 f l a↑ -> closed_Qual 0 f l b↑ -> closed_Qual 0 f l (openq a b c)↑.
  intros. apply Q_lift_closed'. unfold openq. erewrite open_qual_commute''; eauto.
Qed.

Lemma openty_closed: forall {T1 d1 T2 d2 T f l},
  closed_ty 2 f l T -> closed_ty 0 f l T1 -> closed_ty 0 f l T2 -> closed_qual 0 f l d1 -> closed_qual 0 f l d2 ->
  closed_ty 0 f l (T <~ᵀ T1 ~ d1; T2 ~ d2).
Proof. intros. unfold open_ty. unfold open_ty'. erewrite open_rec_ty_commute''; eauto.
  repeat eapply closed_ty_open'; eauto.
Qed.

Lemma disjointq_Qdom : forall {Σ Σ' d d'}, Σ → Σ' ∋ d ⊕ d' -> d' ⊑↑ qdom Σ'.
intros. inversion H; subst; Qcrush; subst; eauto using Nat.lt_lt_succ_r.
Qed.
#[global] Hint Resolve disjointq_Qdom : core.

Lemma disjointq_qdom : forall {Σ Σ' d d'}, Σ → Σ' ∋ d ⊕ d' -> d' ⊑ qdom Σ'.
intros. apply Q_lift_subq. inversion H; subst; Qcrush; subst; eauto using Nat.lt_lt_succ_r.
Qed.
#[global] Hint Resolve disjointq_qdom : core.

Lemma disjointq_Qdom' : forall {Σ Σ' d d'}, Σ → Σ' ∋ d ⊕ d' -> {♦} ⊔ d' ⊑↑ qdom Σ'.
intros. inversion H; subst; Qcrush; subst; eauto using Nat.lt_lt_succ_r.
Qed.
#[global] Hint Resolve disjointq_Qdom' : core.

Lemma disjointq_qdom' : forall {Σ Σ' d d'}, Σ → Σ' ∋ d ⊕ d' -> {♦} ⊔ d' ⊑ qdom Σ'.
intros. apply Q_lift_subq. inversion H; subst; Qcrush; subst; eauto using Nat.lt_lt_succ_r.
Qed.
#[global] Hint Resolve disjointq_qdom' : core.

Lemma disjointq_closed : forall {Σ Σ' d d'}, Σ → Σ' ∋ d ⊕ d' -> closed_Qual 0 0 (‖Σ'‖) d'↑.
  intros. inversion H; subst; auto. simpl. apply closed_qual_qor. eapply closed_qual_monotone; eauto.
  apply just_loc_closed. simpl. lia.
Qed.
#[global] Hint Resolve disjointq_closed : core.

Lemma disjointq_saturated : forall {Σ Σ' d d'}, Σ → Σ' ∋ d ⊕ d' -> wf_senv Σ -> senv_saturated Σ' d'.
  intros. inversion H; subst. intuition. eapply wf_senv_saturated_qplus; eauto. apply indexr_head.
Qed.
#[global] Hint Resolve disjointq_saturated : core.

Lemma disjointq_scale : forall {Σ Σ' d d'}, Σ → Σ' ∋ d ⊕ d' -> forall {d''}, d ⊑↑ d'' -> Σ → Σ' ∋ d'' ⊕ d'.
  intros. inversion H; subst. auto. econstructor; eauto.
Qed.
#[global] Hint Resolve disjointq_scale : core.

Lemma qdom_fresh : forall {A} {Σ : list A}, {♦} ⊑↑ qdom Σ.
  intros. Qcrush.
Qed.
#[global] Hint Resolve qdom_fresh : core.

Lemma substitution_ty_gen :
  forall {t Γ φ Σ Tx dx dx' T d}, dx' ⊓ φ ⊑↑ dx ->
      closed_ty 0 0 (length Σ) Tx ->  closed_Qual 0 0 (length Σ) dx↑ ->
      closed_Qual 0 0 (length Σ) dx'↑ ->
      senv_saturated Σ dx' ->
      has_type (Γ ++ [(bind_ty, false,Tx,dx)]) φ Σ t T d -> Substq dx dx' ->
      has_type ({ 0 |-> Tx ~ dx' }ᴳ Γ) ({ 0 |-> dx' }ᵈ φ) Σ
                                 ({ 0 |-> tunit  }ᵗ t)
                                 ({ 0 |-> Tx ~  dx' }ᵀ T)
                                 ({ 0 |-> dx' }ᵈ d).
Proof.
    intros t Γ φ Σ Tx dx dx' T d Hsep Tx_Hcl Qx_Hcl Qx'_Hcl
    Hsenv_satu
    HT HSubst. specialize (has_type_closed HT) as Hcl. intuition.
    remember (Γ ++ [(bind_ty, false, Tx, dx)]) as Γ'.
    generalize dependent Γ. induction HT; intros; subst; auto.
  - (* ttabs *)  simpl. inversion H0. inversion H1. subst. apply has_type_closed in HT as Hcl_HT.
     rewrite app_length in *.
     replace (‖ (bind_ty, false, T1, d1) :: Γ0 ++ [(bind_ty, false, Tx, dx)] ‖) with (S (S (‖ Γ0 ‖))) in *.
     replace (‖ Γ0 ‖ + ‖ [(bind_ty, false, Tx, dx)] ‖) with (S (‖ Γ0 ‖)) in *.
     intuition.
     assert (dx' ⊓ (df ⊔ $! (S (‖ Γ0 ‖)) ⊔ $! (S (S (‖ Γ0 ‖))) ⊔ {♦}) ⊑↑ dx). {
      repeat rewrite qand_qor_dist_l. erewrite qglb_disjoint_freshv; eauto. erewrite qglb_disjoint_freshv; eauto.
      erewrite qglb_disjoint_fresh; eauto. repeat rewrite qor_empty_left. apply Substq_non_fresh in HSubst. Qcrush.
     }
     intuition.
     specialize (H14 ((bind_ty, false, T1, d1) :: (bind_tm, true, TAll d1 d2 T1 T2, df) :: Γ0)). intuition.
     eapply t_tabs; eauto.
     2: constructor; eauto.  1-6: erewrite subst1_tenv_length; eauto.
     eapply closed_tm_subst1; eauto.  1,2,5: eapply closed_qual_subst1; eauto.
     1,2:eapply closed_ty_subst1; eauto.
     eapply subst_qual_subqual_monotone; eauto.

     apply subst1_senv_saturated; auto.

     assert (closed_tm 0 0 (‖ Σ ‖)  tunit). { econstructor; eauto.  }

     unfold open_tm' in *. unfold open_ty' in *. unfold open_ty in *.
     unfold openq' in *. unfold openq in *.
     erewrite subst1_tenv_length in *.
     repeat erewrite subst1_qor_dist in  H15. erewrite app_length in H15.
     replace (‖ Γ0 ‖ + ‖ [(bind_ty, false, Tx, dx)] ‖)
       with  (S (‖ Γ0 ‖)) in H15.
     erewrite open_subst1_tm_comm. eauto. erewrite open_subst1_tm_comm. eauto.
     erewrite open_subst1_qual_comm; eauto. erewrite open_subst1_qual_comm; eauto.
     erewrite  open_subst1_ty_comm; eauto. erewrite  open_subst1_ty_comm; eauto.
     intuition. auto. 1-2: simpl; lia. simpl. erewrite app_length. simpl. lia.
  - (*  t_tapp *) simpl in *.  apply has_type_closed in HT as Hcl. intuition.
    specialize (H14 Γ0). intuition.
    replace ({0 |-> Tx ~ dx }ᵀ ([[0 ~> T1 ~ d1 ]]ᵀ T2)) with ( open_rec_ty 0 ({0 |-> Tx ~ dx }ᵀ T1)({ 0 |-> dx }ᵈ d1) ({0 |-> Tx ~ dx }ᵀ T2)).
    eapply t_tapp with (Γ :=  ({ 0 |-> Tx ~ dx' }ᴳ Γ0))(φ := ({ 0 |-> dx' }ᵈ φ))(Σ := Σ)
                      (t := ({ 0 |-> tunit }ᵗ t))(d2 := { 0 |-> dx' }ᵈ d2)
                      (T1 := ({ 0 |-> Tx ~ dx' }ᵀ  T1)) (T2 := ({ 0 |-> Tx ~ dx' }ᵀ  T2))
                      (d1 := { 0 |-> dx' }ᵈ d1) in H16; eauto.
    inversion H12. subst. erewrite app_length in *. intuition.
    replace ({0 |-> Tx ~ dx' }ᵀ (T2 <~ᵀ TUnit ~ ∅; T1 ~ d1))
      with  (({0 |-> Tx ~ dx' }ᵀ T2) <~ᵀ TUnit ~ ∅; {0 |-> Tx ~ dx' }ᵀ T1 ~ ({0 |-> dx' }ᵈ d1)).
    replace ({0 |-> dx' }ᵈ (d2 <~ᵈ df; d1))
      with  (({0 |-> dx' }ᵈ d2) <~ᵈ ({0 |-> dx' }ᵈ df); ({0 |-> dx' }ᵈ d1)). auto.
    unfold openq. erewrite subst1_open_qual_comm; eauto. erewrite subst1_open_qual_comm; eauto.
    replace (∅) with ({0 |-> dx' }ᵈ ∅) at 1; auto. unfold open_ty. erewrite subst1_open_ty_comm; eauto. erewrite subst1_open_ty_comm; eauto.
    1-2: rewrite subst1_tenv_length; rewrite app_length in *; simpl in *;
    replace  (‖ Γ0 ‖ + 1) with (S (‖Γ0‖)) in *; try lia.
    eapply closed_ty_subst1; eauto. eapply closed_qual_subst1; eauto.
    1,3: unfold openq; rewrite <- @subst1_qual_empty with (dx:=dx');
        erewrite <- subst1_open_qual_comm; eauto; erewrite <- subst1_open_qual_comm; eauto.
    1,3: apply subst_qual_subqual_monotone; auto.
    1,2: apply subst1_senv_saturated; auto.
    erewrite <- not_free_subst1_ty_iff; eauto.
    erewrite <- subst1_open_ty_comm; eauto.
  - (* t_tapp_fresh *)  simpl in *. intuition. apply has_type_closed in HT as Hcl. intuition.
    specialize (H20 Γ0). intuition.
    apply has_type_closed in H17 as Hcl. intuition.
    replace ({0 |-> Tx ~ dx' }ᵀ (T2 <~ᵀ TUnit ~ ∅; T1 ~ d1))
       with (({0 |-> Tx ~ dx' }ᵀ T2) <~ᵀ TUnit ~ ∅; ({0 |-> Tx ~ dx' }ᵀ T1) ~ ({0 |-> dx' }ᵈ d1)).
    replace ({0 |-> dx' }ᵈ (d2 <~ᵈ df; d1))
      with  (({0 |-> dx' }ᵈ d2) <~ᵈ ({0 |-> dx' }ᵈ df); ({0 |-> dx' }ᵈ d1)).
    apply t_tapp_fresh with (df' := ({0 |-> dx' }ᵈ df'))(d1' := ({0 |-> dx' }ᵈ d1')).
    (*separation/overap is preserved after substitution*)
    assert (Hoverlap: {0 |-> dx' }ᵈ (df' ⊓  d1') = ({0 |-> dx' }ᵈ df' ⊓  {0 |-> dx' }ᵈ d1')). {
      symmetry. eapply subst1_ty_preserves_separation; eauto.
    }
    replace (TAll (({0 |-> dx' }ᵈ df' ⋒ {0 |-> dx' }ᵈ d1')) ({0 |-> dx' }ᵈ d2) ({0 |-> Tx ~ dx' }ᵀ T1) ({0 |-> Tx ~ dx' }ᵀ T2))
      with  ({0 |-> Tx ~ dx' }ᵀ (TAll (df' ⋒ d1') d2 T1 T2)). auto.
    simpl. rewrite subst1_qor_dist. rewrite Hoverlap. rewrite subst1_fresh_id. auto.

    5 : unfold openq; rewrite <- @subst1_qual_empty with (dx:=dx');
      erewrite <- subst1_open_qual_comm; eauto; erewrite <- subst1_open_qual_comm; eauto.
    1,2,5,8,9 : apply subst_qual_subqual_monotone; auto.

    eapply closed_ty_subst1'; eauto. eapply closed_qual_subst1'; eauto.

    2: intro Hfresh. 1,2 : erewrite <- not_free_subst1_ty_iff; eauto; apply Substq_non_fresh in HSubst.

    1,2 : eapply subst1_ty_saturated; eauto.
    unfold openq; rewrite <- @subst1_qual_empty with (dx:=dx');
    erewrite <- subst1_open_qual_comm; eauto; erewrite <- subst1_open_qual_comm; eauto. 1,2: apply subst1_senv_saturated; auto.
    unfold openq. repeat erewrite <- subst1_open_qual_comm; eauto.
    replace (∅) with ({0 |-> dx' }ᵈ ∅) at 1; auto. unfold open_ty. repeat erewrite subst1_open_ty_comm; eauto.

  - (* tunit *) assert ({ 0 |-> dx' }ᵈ (∅) = (∅)). { erewrite subst1_qual_empty; eauto. } rewrite H4. constructor.
    erewrite subst1_tenv_length. eapply closed_qual_subst1; eauto. erewrite app_length in *. simpl in H.
    replace (S (length Γ0)) with (length Γ0 + 1). intuition. lia.
  - (* $(x) *)  (bdestruct (x =? 0)).
    + (*  x is 0 *)
      rewrite indexr_skips in H2; simpl; auto; try lia. simpl in H2. subst. simpl in H2. inversion H2.
    + (* x is in Γ0 *)
    assert (Hx: 1 <= x); try lia. destruct x; try lia.
    (*erewrite subst1_tm_id.  replace ({0 |-> ∅ }ᵈ $! (S x)) with ($!(S x)).*)
    apply @indexr_subst1 with (Tx := Tx)(dx := dx') in H2; auto.
    (* simpl.  rewrite mem_singleton. simpl. replace (remove 0 (singleton (S x))) with (singleton  (S x)). *)
    (* rewrite unsplice_set_singleton_dec; try lia. *)
    apply t_var with (b:=b) (d:={0 |-> dx' }ᵈ d)(φ  := ({0 |-> dx' }ᵈ φ)). change x with (pred (S x)). auto.
    erewrite subst1_just_fv.
    repeat eapply subst_qual_subqual_monotone. auto.
    eapply closed_qual_subst1'; eauto. simpl. eapply closed_ty_subst1; eauto.
    simpl. eapply closed_qual_subst1; eauto.
  - (* tabs *)
    assert( has_type (Γ0 ++ [(bind_ty, false, Tx, dx)]) φ Σ (tabs t) (TFun d1 d2 T1 T2) df). { econstructor; eauto. }
    apply has_type_closed in HT as Hcl. intuition. inversion H0. subst. rewrite app_comm_cons in *. rewrite app_length in  *.
    replace (‖ Γ0 ‖ + ‖ [(bind_ty, false, Tx, dx)] ‖) with (S (‖ Γ0 ‖)) in *.
    simpl. apply t_abs; auto. erewrite subst1_tenv_length.
    eapply closed_tm_subst1; eauto.
    constructor.
    1-5: erewrite subst1_tenv_length.
    1,2,5: eapply closed_qual_subst1; eauto.
    1-2: eapply closed_ty_subst1; eauto.
    apply subst_qual_subqual_monotone; auto.
    eauto.
    apply subst1_senv_saturated; auto.

    assert (dx' ⊓ (df ⊔ $! (S (‖ Γ0 ‖)) ⊔ $! (S (S (‖ Γ0 ‖))) ⊔ {♦}) ⊑↑ dx). {
      repeat rewrite qand_qor_dist_l. erewrite qglb_disjoint_freshv; eauto. erewrite qglb_disjoint_freshv; eauto.
      erewrite qglb_disjoint_fresh; eauto. repeat rewrite qor_empty_left. apply Substq_non_fresh in HSubst. Qcrush.
    }
    intuition. specialize (H15 ((bind_tm, false, T1, d1) :: ((bind_tm, true, TFun d1 d2 T1 T2, df) :: Γ0))).

    rename  H15  into IHHT.
    replace (‖ ((bind_tm, false, T1, d1) :: (bind_tm, true, TFun d1 d2 T1 T2, df) :: Γ0) ++ [(bind_ty, false, Tx, dx)] ‖)
       with (S (S (S (‖ Γ0 ‖)))) in IHHT.
    replace (S (‖ Γ0 ++ [(bind_ty, false, Tx, dx)] ‖)) with (S (S (‖ Γ0 ‖))) in IHHT.

    replace (‖ (bind_tm, false, T1, d1) :: ((bind_tm, true, TFun d1 d2 T1 T2, df) :: Γ0) ++ [(bind_ty, false, Tx, dx)] ‖)
       with (S (S (S (‖ Γ0 ‖)))) in *.

    unfold open_tm' in *. unfold open_ty' in *. unfold open_ty in *.
    unfold openq' in *. unfold openq in *.
    rewrite app_length in H14.
    rewrite subst1_tenv_length.

    assert  (closed_tm 0 0 (length Σ) tunit). { constructor. }
    intuition.

    rename H16 into IHHT.

   replace ({0 |-> Tx ~ dx'}ᴳ ((bind_tm, false, T1, d1)
             :: (bind_tm, true, TFun d1 d2 T1 T2, df) :: Γ0))
     with ((bind_tm, false, {0 |-> Tx ~ dx' }ᵀ T1, {0 |-> dx' }ᵈ d1)
   :: (bind_tm, true, TFun ({0 |-> dx' }ᵈ d1) ({0 |-> dx' }ᵈ d2)
          ({0 |-> Tx ~ dx' }ᵀ T1) ({0 |-> Tx ~ dx' }ᵀ T2),
        {0 |-> dx' }ᵈ df) :: {0 |-> Tx ~ dx' }ᴳ Γ0) in IHHT.

   replace ({0 |-> dx' }ᵈ (df ⊔ $! (S (‖ Γ0 ‖)) ⊔ $! (S (S (‖ Γ0 ‖))) ⊔ {♦}))
     with  ({0 |-> dx' }ᵈ df ⊔ $! (‖ Γ0 ‖) ⊔ $! (S (‖ Γ0 ‖)) ⊔ {♦}) in IHHT. intuition.
     rewrite app_length in IHHT.
     replace (‖ Γ0 ‖ + ‖ [(bind_ty, false, Tx, dx)] ‖) with (S (‖ Γ0 ‖)) in IHHT.

   erewrite <- open_subst1_qual_comm in IHHT; eauto. erewrite <- open_subst1_qual_comm in IHHT; eauto.
   erewrite <- open_subst1_ty_comm in IHHT; eauto. erewrite <- open_subst1_ty_comm in IHHT; eauto.
   erewrite <- open_subst1_tm_comm in IHHT; eauto. erewrite <- open_subst1_tm_comm in IHHT; eauto.

   simpl. lia.
   erewrite subst1_qor_dist; eauto. f_equal.
   simpl. auto.
   simpl; erewrite app_length; eauto; simpl; lia.
   erewrite app_length; eauto. simpl. lia.
   erewrite app_length; eauto. simpl. lia.
   simpl. lia.
  - (* t_app *) intuition. rename H9 into IHHT1. rename H8 into IHHT2. simpl.
    replace ({ 0 |-> dx' }ᵈ (openq df d1 d2)) with
               (openq ({ 0 |-> dx' }ᵈ df) ({ 0 |-> dx' }ᵈ d1) ({ 0 |-> dx' }ᵈ d2)).
    replace ({0 |-> Tx ~ dx' }ᵀ (T2 <~ᵀ TUnit ~ ∅; T1 ~ d1)) with
               (({0 |-> Tx ~ dx' }ᵀ T2) <~ᵀ TUnit ~ ∅; ({0 |-> Tx ~ dx' }ᵀ T1) ~ ({0 |-> dx' }ᵈ d1)).
    apply t_app with (T1:= { 0 |-> Tx ~ dx' }ᵀ T1) (df:=({0 |-> dx' }ᵈ df)).
    replace (TFun ({0 |-> dx' }ᵈ d1) ({0 |-> dx' }ᵈ d2) ({0 |-> Tx ~ dx' }ᵀ T1) ({0 |-> Tx ~ dx' }ᵀ T2))
            with ({ 0 |->Tx ~ dx' }ᵀ (TFun d1 d2 T1 T2)); auto.
    eapply IHHT1; eauto. 4: eapply IHHT2; eauto.
    1-6 : apply has_type_closed in HT1; apply has_type_closed in HT2 ;intuition; inversion H1; subst; rewrite app_length in *; simpl in *; auto.
    1,4 : unfold openq; rewrite <- @subst1_qual_empty with (dx:=dx');
        erewrite <- subst1_open_qual_comm; eauto; erewrite <- subst1_open_qual_comm; eauto.
    * apply subst_qual_subqual_monotone. unfold openq in H4. auto.
    * apply subst1_senv_saturated; auto.
    * eauto.
    * erewrite <- not_free_subst1_ty_iff; eauto.
    * replace (∅) with ({0 |-> dx' }ᵈ ∅) at 1; auto. unfold open_ty. repeat erewrite subst1_open_ty_comm; eauto.
    * unfold openq. repeat erewrite <- subst1_open_qual_comm; eauto.
  - (* t_app_fresh *) intuition. rename H15 into IHHT1. rename H14 into IHHT2. simpl.
    replace ({ 0 |-> dx' }ᵈ (openq df d1 d2)) with
               (openq ({ 0 |-> dx' }ᵈ df) ({ 0 |-> dx' }ᵈ d1) ({ 0 |-> dx' }ᵈ d2)).
    replace ({0 |-> Tx ~ dx' }ᵀ (T2 <~ᵀ TUnit ~ ∅; T1 ~ d1)) with
               (({0 |-> Tx ~ dx' }ᵀ T2) <~ᵀ TUnit ~ ∅; ({0 |-> Tx ~ dx' }ᵀ T1) ~ ({0 |-> dx' }ᵈ d1)).
    (*separation/overap is preserved after substitution*)
    assert (Hoverlap: {0 |-> dx' }ᵈ (df' ⊓ d1') = {0 |-> dx' }ᵈ df' ⊓ {0 |-> dx' }ᵈ d1'). {
      symmetry. eapply subst1_ty_preserves_separation; eauto.
    }
    eapply t_app_fresh with (T1:= { 0 |-> Tx ~ dx' }ᵀ T1) (df:=({0 |-> dx' }ᵈ df)) (d1:=({0 |-> dx' }ᵈ d1)) (df':=({0 |-> dx' }ᵈ df')) (d1':=({0 |-> dx' }ᵈ d1')); eauto.
    replace (TFun (({0 |-> dx' }ᵈ df' ⋒ {0 |-> dx' }ᵈ d1')) ({0 |-> dx' }ᵈ d2) ({0 |-> Tx ~ dx' }ᵀ T1) ({0 |-> Tx ~ dx' }ᵀ T2))
      with  ({0 |-> Tx ~ dx' }ᵀ (TFun (df' ⋒ d1') d2 T1 T2)).
    eapply IHHT1; auto. 7 : eapply IHHT2; auto.
    1-3,7-9 : apply has_type_closed in HT1; apply has_type_closed in HT2 ;intuition; inversion H1; subst; rewrite app_length in *; simpl in *; auto.
    simpl. rewrite subst1_qor_dist. rewrite Hoverlap. rewrite subst1_fresh_id. auto.
    5 : unfold openq; rewrite <- @subst1_qual_empty with (dx:=dx');
        erewrite <- subst1_open_qual_comm; eauto; erewrite <- subst1_open_qual_comm; eauto.
    1,2,5,6,7 : apply subst_qual_subqual_monotone; auto.
    intro Hfresh. 1,2 : erewrite <- not_free_subst1_ty_iff; eauto; apply Substq_non_fresh in HSubst.
    1,2 : eapply subst1_ty_saturated; eauto.
    unfold openq; rewrite <- @subst1_qual_empty with (dx:=dx');
    erewrite <- subst1_open_qual_comm; eauto; erewrite <- subst1_open_qual_comm; eauto. apply subst1_senv_saturated; auto.
    replace (∅) with ({0 |-> dx' }ᵈ ∅) at 1; auto. unfold open_ty. repeat erewrite subst1_open_ty_comm; eauto.
    unfold openq. repeat erewrite <- subst1_open_qual_comm; eauto.

  - (* t_loc *) erewrite app_length in *; eauto. simpl in H0, H1, H3, H, H6.
    replace ({0 |-> tunit }ᵗ & (l)) with (& (l)).
    replace  ({0 |-> dx' }ᵈ (&! l)) with (&! l).
    replace ({0 |-> Tx ~ dx' }ᵀ (TRef q T))
      with  (TRef ({0 |-> dx' }ᵈ q)({0 |-> Tx ~ dx' }ᵀ T)).
    replace ({0 |-> dx' }ᵈ (q ⊔ &! l)) with (({0 |-> dx' }ᵈ q) ⊔ &! l).
   apply t_loc.
   erewrite subst1_tenv_length. eapply closed_qual_subst1; eauto.
   replace (S (‖ Γ0 ‖)) with ((‖ Γ0 ‖) + 1). intuition. lia.
   1,2: erewrite subst1_ty_id; eauto. 1,2,5: erewrite subst1_qual_id; eauto.
   replace (&! l) with ({0 |-> dx' }ᵈ (&! l)). eapply subst_qual_subqual_monotone; eauto.
   erewrite subst1_qual_id; eauto. eapply just_loc_closed; eauto.
   eapply subst_qual_subqual_monotone; eauto.
   erewrite subst1_qor_dist. repeat erewrite subst1_qual_id; eauto. eapply just_loc_closed; eauto.
   intuition.
   erewrite subst1_qual_id; eauto. eapply just_loc_closed; eauto. auto.
  - (* t_ref *) inversion H0. inversion H1. subst.  erewrite app_length in *. intuition.
    apply has_type_closed in HT as Hcl; intuition.
    assert (closed_ty 0 (‖ Γ0 ‖ + ‖ [(bind_ty, false, Tx, dx)] ‖) (‖ Σ ‖) T). {
      simpl. eapply closed_ty_monotone; eauto.  erewrite app_length. simpl. lia.
    } intuition.
    specialize (H6 Γ0). intuition.
    replace ({0 |-> tunit }ᵗ (tref t)) with (tref ({0 |-> tunit }ᵗ  t)).
    rewrite subst1_qor_dist.
    replace ({0 |-> dx' }ᵈ {♦}) with ({♦}).
    constructor. 1,2: fold subst_ty. auto.
    erewrite subst1_ty_id; eauto.
    replace ({♦}) with ({0 |-> dx' }ᵈ {♦}). apply  subst_qual_subqual_monotone. auto. auto.
    eauto. auto. auto.
  - (* t_ref  *)  intuition. inversion H1. subst. intuition. apply has_type_closed in HT as Hcl. intuition.
   specialize (H6 Γ0). intuition.
   replace ({0 |-> tunit }ᵗ ! (t)) with (! ({0 |-> tunit }ᵗ (t))).
   replace ({0 |-> Tx ~ dx' }ᵀ (TRef d1 T))
     with  (TRef ({0 |-> dx' }ᵈ d1) ({0 |-> Tx ~ dx' }ᵀ T)) in H9.
   apply t_deref with (d := ({0 |-> dx' }ᵈ d)); auto.
   eauto.
   apply subst_qual_subqual_monotone. auto.
   apply subst1_senv_saturated; auto.
   intuition. auto.
  - (* t_assign  *)  intuition.  inversion H1. subst. intuition.
    apply has_type_closed in HT1 as HT1_Hcl. intuition.
    apply has_type_closed in HT2 as  HT2_Hcl. intuition.
    specialize  (H4 Γ0). specialize(H6 Γ0). intuition.  erewrite subst1_qual_empty in *.
    replace ({0 |-> tunit }ᵗ (tassign t1 t2)) with (tassign  ({0 |-> tunit }ᵗ t1) ({0 |-> tunit }ᵗ t2)).
    (* replace ({0 |-> Tc ~ dc }ᵀ (TRef T)) with (TRef ({0 |-> Tc ~ dc }ᵀ  T)). *)
    replace ({0 |-> Tx ~ dx' }ᵀ TUnit) with TUnit.
    eapply t_assign; eauto. all: auto.
 - (* t_sub *) intuition. apply has_type_closed in HT as Hcl. intuition.  simpl in *. erewrite app_length in *. simpl in *.
    apply t_sub with (T1:={ 0 |-> Tx ~ dx' }ᵀ T1) (d1:={ 0 |-> dx' }ᵈ d1).
    eapply H6; eauto. eapply subst_ty_stp; eauto. apply subst_qual_subqual_monotone; auto.
    apply subst1_senv_saturated; auto.

  Unshelve. all: auto. all: apply 1.
 Qed.

(* case for t_tapp *)
Lemma substitution1_ty : forall {t Tx Tf dx df Σ T d},
     has_type [(bind_ty, false, Tx, dx) ; (bind_tm, true,Tf,df)] (df ⊔ $!0 ⊔ $!1 ⊔ {♦}) Σ t T d ->
     closed_ty 0 0 (length Σ) Tx ->
     closed_qual 0 0 (length Σ) dx -> ♦∉ dx ->  senv_saturated Σ dx ->
     forall {vt}, vtp Σ vt Tf df -> ♦∉ df ->
     has_type [] (df ⊔ dx ⊔ {♦}) Σ  ( { 0 |-> vt; tunit  }ᵗ t)  ( { 0 |-> Tf ~ df; Tx ~ dx }ᵀ T) ({ 0 |-> df; dx }ᵈ d).
Proof. intros. subst. specialize (vtp_closed  H4) as HV_cl. specialize (has_type_closed H) as Hcl. intuition.
       intuition. replace ([(bind_ty, false,Tx, dx); (bind_tm, true,Tf, df)]) with ([(bind_ty, false,Tx,dx)] ++ [(bind_tm, true,Tf, df)]) in H; auto.
  remember (df ⊔ $!0 ⊔ $!1 ⊔ {♦}) as DF.
  assert (Hsepf : df ⊓ DF ⊑↑ df). { Qcrush. }
  eapply (substitution_gen Hsepf) in H; eauto.
  replace ({0 |-> Tf ~ df }ᴳ [(bind_ty, false, Tx, dx)]) with ([] ++ [(bind_ty, false, Tx, dx)]) in H.
  replace ({0 |-> df }ᵈ DF) with (df ⊔ $!0 ⊔ {♦}) in H.
  assert (Hsepf' : dx ⊓ (df ⊔ $!0 ⊔ {♦}) ⊑↑ dx). { Qcrush. }
  eapply (substitution_ty_gen Hsepf') in H; eauto.
  replace ({0 |-> dx }ᵈ (df ⊔ $!0 ⊔ {♦})) with (df ⊔ dx ⊔ {♦}) in H. simpl in H. apply H.
  (*done, prove earlier replacements *)
  repeat rewrite subst1_qor_dist. rewrite subst1_just_fv0. erewrite subst1_qual_id; eauto.
  subst. repeat rewrite subst1_qor_dist. rewrite subst1_just_fv0. rewrite <- subst1_just_fv.
  erewrite subst1_qual_id; eauto. rewrite (@qor_assoc df df). rewrite qor_idem. auto.
  simpl. erewrite subst1_qual_id; eauto. erewrite subst1_ty_id; eauto.
Qed.

(* t_tapp case *)
Lemma substitution_ty_stp1 : forall{T1 T2},
    forall {Tx Tf df dx Σ d1 d2},
      stp ([(bind_ty, false,Tx,dx); (bind_tm, true,Tf,{♦})]) Σ T1 d1 T2 d2 ->
      closed_ty 0 0 (‖Σ‖) Tx ->
      closed_ty 0 0 (‖Σ‖) Tf ->
      closed_Qual 0 0 (‖Σ‖) df↑ -> closed_Qual 0 0 (‖Σ‖) dx↑ -> ♦∉ df -> ♦∉ dx ->
      stp [] Σ ({ 0 |-> Tf ~ df; Tx ~ dx }ᵀ T1) ({ 0 |-> df ; dx }ᵈ d1) ({ 0 |-> Tf ~ df ; Tx ~ dx }ᵀ T2) ({ 0 |-> df ; dx }ᵈ d2).
Proof. intros. replace [(bind_ty, false, Tx, dx); (bind_tm, true, Tf,{♦})]
                  with ([(bind_ty, false, Tx, dx)] ++ [(bind_tm, true, Tf,{♦})]) in H; auto.
  eapply @subst_stp  with (df':=df) in H; auto.
  replace ({0 |-> Tf ~ df }ᴳ [(bind_ty, false, Tx, dx)]) with ([(bind_ty, false, Tx, dx)]) in H.
  replace ([(bind_ty, false, Tx, dx)]) with ([] ++ [(bind_ty, false, Tx, dx)]) in H; auto.
  eapply @subst_ty_stp with (d':=dx) in H; auto.
  simpl. erewrite subst1_ty_id; eauto. erewrite subst1_qual_id; eauto.
  replace ({♦}) with (∅ ⋒ df). auto. auto.
Qed.

(* case for t_tapp_fresh *)
Lemma substitution2_ty : forall {t df df' Tf Tx dx dx' Σ T d},
    has_type [(bind_ty, false,Tx,(df' ⊓ dx') ⊔ {♦}); (bind_tm, true,Tf,df)] (df ⊔ $!0 ⊔ $!1 ⊔ {♦}) Σ t T d ->
    senv_saturated Σ dx ->  closed_ty 0 0 (‖ Σ ‖) Tx -> ♦∉ dx -> dx ⊑↑ dx' -> closed_Qual 0 0 (‖Σ‖) dx'↑ ->
    forall {vt}, vtp Σ vt Tf df ->  ♦∉ df -> df ⊑↑ df' ->  closed_Qual 0 0 (‖Σ‖) df'↑ ->
    has_type [] (df ⊔ dx ⊔ {♦}) Σ
                ({ 0 |-> vt; tunit }ᵗ t)
                ({ 0 |-> Tf ~ df; Tx ~ dx}ᵀ T)
                ({ 0 |-> df ; dx }ᵈ d).
Proof.  intros. specialize (has_type_closed H) as Hcl. intuition.
  assert (Hcl : closed_qual 0 0 (‖ Σ ‖) (df' ⋒ dx')). { apply closed_qual_qor; auto. apply closed_qual_qand; auto. }
  intuition. replace ([(bind_ty, false,Tx, (df' ⋒ dx')); (bind_tm, true,Tf, df)])
                with ([(bind_ty, false,Tx, (df' ⋒ dx'))] ++ [(bind_tm, true,Tf, df)]) in H; auto.
  remember (df ⊔ $!0 ⊔ $!1 ⊔ {♦}) as DF.
  assert (Hsepf : df ⊓ DF ⊑↑ df). { Qcrush.  }
  eapply (substitution_gen Hsepf) in H; eauto.
  replace ({0 |-> Tf ~ df }ᴳ [(bind_ty, false, Tx, df' ⋒ dx')])
     with ([(bind_ty, false, Tx, df' ⋒ dx')]) in H.
  replace ({0 |-> df }ᵈ DF) with (df ⊔ $!0 ⊔ {♦}) in H.
  assert (Hstparg : stp [] Σ Tx (df ⋒ dx) Tx (df' ⋒ dx')). { apply stp_refl; auto. constructor; eauto. Qcrush. }
  eapply narrowing_ty in H; eauto.
  assert (Hsepf' : dx ⊓ (df ⊔ $!0 ⊔ {♦}) ⊑↑ (df ⊓ dx) ⊔ {♦}). {
    repeat rewrite qand_qor_dist_l. erewrite qglb_disjoint_freshv; eauto. Qcrush.
  }
  replace ([(bind_ty, false, Tx, df ⋒ dx)]) with ([] ++ [(bind_ty, false, Tx, df ⋒ dx)]) in H.
  eapply (substitution_ty_gen Hsepf') in H; eauto.
  replace ({0 |-> dx }ᵈ (df ⊔ $!0 ⊔ {♦})) with (df ⊔ dx ⊔ {♦}) in H. simpl in H. apply H.
  (*done, prove earlier replacements *)
  repeat rewrite subst1_qor_dist. rewrite subst1_just_fv0. erewrite subst1_qual_id; eauto.
  Qcrush. auto.
  subst. repeat rewrite subst1_qor_dist. rewrite subst1_just_fv0. rewrite <- subst1_just_fv. erewrite subst1_qual_id; eauto. rewrite (@qor_assoc df df). rewrite qor_idem. auto.
  simpl. erewrite subst1_qual_id; eauto. erewrite subst1_ty_id; eauto.
Qed.

(* t_tapp_fresh case *)
Lemma substitution_stp2_ty : forall{T1 T2},
    forall {Tx bf Tf df df' dx dx' Σ d1 d2},
      stp ([(bind_ty, false,Tx,df' ⋒ dx'); (bind_tm, bf,Tf,{♦})]) Σ T1 d1 T2 d2 ->
      closed_ty 0 0 (‖Σ‖) Tx ->
      closed_ty 0 0 (‖Σ‖) Tf ->
      closed_Qual 0 0 (‖Σ‖) df'↑ -> closed_Qual 0 0 (‖Σ‖) dx'↑ -> ♦∉ df -> ♦∉ dx -> df ⊑↑ df' -> dx ⊑↑ dx' ->
      stp [] Σ ({ 0 |-> Tf ~ df; Tx ~ dx }ᵀ T1) ({ 0 |-> df ; dx }ᵈ d1) ({ 0 |-> Tf ~ df ; Tx ~ dx }ᵀ T2) ({ 0 |-> df ; dx }ᵈ d2).
Proof.  intros.  assert (Hcl : closed_Qual 0 0 (‖ Σ ‖) (df' ⋒ dx')↑). { apply closed_qual_qor; auto. apply closed_qual_qand; auto. }
  replace [(bind_ty, false, Tx, df' ⋒ dx'); (bind_tm, bf, Tf,{♦})] with ([(bind_ty, false, Tx, df' ⋒ dx')] ++ [(bind_tm, bf, Tf,∅ ⋒ df)]) in H; auto.
  eapply @subst_stp with (df':=df) in H; eauto.
  replace ({0 |-> Tf ~ df }ᴳ [(bind_ty, false, Tx, df' ⋒ dx' )]) with ([(bind_ty, false, Tx, df' ⋒ dx')]) in H.
  assert (H' : stp [(bind_ty, false, Tx, df ⋒ dx)] Σ ({0 |-> Tf ~ df }ᵀ T1) ({0 |-> df }ᵈ d1) ({0 |-> Tf ~ df }ᵀ T2) ({0 |-> df }ᵈ d2)). {
    eapply narrowing_stp_ty; eauto. Qcrush. apply stp_refl; auto. constructor; auto. Qcrush.
  }
  replace ([(bind_ty, false, Tx, df ⋒ dx )]) with ([] ++ [(bind_ty, false, Tx, df ⋒ dx)]) in H'; auto.
  replace ([]) with ({0 |-> Tx ~ dx}ᴳ []); auto. eapply subst_ty_stp; eauto.
  simpl. erewrite subst1_ty_id; eauto. erewrite subst1_qual_id; eauto.
Qed.

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

Lemma vtp_canonical_form_ttabs : forall {Σ t T1 T2 d1 d2 df},
  vtp Σ t (TAll d1 d2 T1 T2) df -> value t -> exists t',  t = ttabs  t'.
Proof. intros Σ t T1 T2 d1 d2 df H HV. remember (TAll d1 d2 T1 T2) as T.
       generalize dependent T1. generalize dependent T2.
       induction H; intuition; try discriminate. exists t. intuition.
Qed.

Lemma qstp_delete_fresh : forall {Σ q1 q2}, qstp [] Σ q1 q2 -> ♦∉ q1 -> qstp [] Σ q1 (false, (qfvs q2), (qbvs q2), (qlocs q2)).
  intros. specialize (qstp_closed H) as Hcl. intuition. apply qstp_empty in H. apply qs_sq. Qcrush. Qcrush.
Qed.

Lemma senv_saturated_non_fresh : forall {Σ q}, senv_saturated Σ q -> senv_saturated Σ (false, (qfvs q), (qbvs q), (qlocs q)).
  intros. unfold senv_saturated in *. intros. specialize (H l). simpl in *. intuition.
  inversion H1. subst. econstructor; eauto. Qcrush.
Qed.

Lemma vtp_non_fresh : forall {Σ v T q}, vtp Σ v T q -> vtp Σ v T (false, (qfvs q), (qbvs q), (qlocs q)).
Proof. intros. induction H.
  + apply qstp_closed in H4 as Hcl_qstp.  intuition. apply qstp_empty in H4 as H4'.  eapply vtp_tabs; eauto.
    econstructor; eauto. Qcrush. apply senv_saturated_non_fresh. auto.
  + inversion H. subst. econstructor; auto. apply senv_saturated_non_fresh. auto.
  + inversion H1. subst. econstructor; eauto.
    apply qstp_delete_fresh; auto. Qcrush.
    apply senv_saturated_non_fresh. auto.
  + apply qstp_closed in H5 as Hcl_qstp.  intuition. inversion H11.  subst. eapply vtp_abs; eauto.
    apply qstp_empty in H5. subst. econstructor; eauto.  destruct df1. simpl in H7. subst. Qcrush.
    apply senv_saturated_non_fresh. auto.
  + apply vtp_closed in IHvtp as Hcl_vtp; intuition. inversion H4. subst.
    eapply vtp_top; eauto. apply senv_saturated_non_fresh. auto.
Qed.

Lemma stp_set_not_fresh : forall {d1 T Γ Σ}, closed_ty 0 (‖Γ‖) (‖Σ‖) T -> closed_Qual 0 (‖Γ‖) (‖Σ‖) d1↑ -> stp Γ Σ T (false, (qfvs d1), (qbvs d1), (qlocs d1)) T d1.
  intros. apply stp_refl; auto. constructor; auto. Qcrush.
Qed.
#[global] Hint Resolve stp_set_not_fresh : core.

Lemma openq_subqual_0 : forall {df d2 d1 l}, closed_Qual 0 0 l df↑ -> closed_Qual 0 0 l d1↑ -> N_lift (qbvs d2) 0 -> df ⊑↑ d2 <~ᵈ df; d1.
  intros.
qual_destruct d2. qual_destruct d1. qual_destruct df. unfold openq. unfold_q. clift. simpl.
#[local] Hint Resolve n_reflect_true : bdestruct.
bdestruct (n_or (n_diff bvs (n_one 0)) bvs1 1); Qcrush; exfalso; eauto.
#[local] Remove Hints n_reflect_true : bdestruct.
Qed.

Lemma openq_subqual_0_false : forall {df d2 d1}, ~N_lift (qbvs d2) 0 -> forall {df'}, d2 <~ᵈ df; d1 = d2 <~ᵈ df'; d1.
  intros. unfold openq. unfold_q. clift. apply Q_lift_eq. Qcrush.
Qed.

Lemma openq_subqual_1 : forall {df d2 d1 l}, closed_Qual 0 0 l df↑ -> closed_Qual 0 0 l d1↑ -> N_lift (qbvs d2) 1 -> d1 ⊑↑ d2 <~ᵈ df; d1.
  intros.
  qual_destruct d2. unfold openq. unfold_q.
#[local] Hint Resolve n_reflect_true : bdestruct.
bdestruct (bvs 0); simpl; clift. bdestruct (n_or (n_diff bvs (n_one 0)) (snd (fst df)) 1).
#[local] Remove Hints n_reflect_true : bdestruct.
all: Qcrush.
Qed.

Lemma openq_subqual_1_false : forall {df d2 d1 l}, closed_Qual 0 0 l df↑ -> ~N_lift (qbvs d2) 1 -> forall {d1'}, d2 <~ᵈ df; d1 = d2 <~ᵈ df; d1'.
intros. qual_destruct d2. qual_destruct df. unfold openq. unfold_q.
#[local] Hint Resolve n_reflect_true : bdestruct.
bdestruct (bvs 0); simpl; clift; auto.
bdestruct (n_or (n_diff bvs (n_one 0)) bvs0 1); auto.
#[local] Remove Hints n_reflect_true : bdestruct.
exfalso. assert (~N_lift (n_diff bvs (n_one 0)) 1). Qcrush. assert (~N_lift bvs0 1). Qcrush. eauto. Qcrush.
Qed.

Lemma open_qual_not_free : forall {k q}, [[k ~> ∅ ]]ᵈ q = q -> forall {q'}, [[k ~> q' ]]ᵈ q = q.
  intros. qual_destruct q. qual_destruct q'. unfold_q.
#[local] Hint Resolve n_reflect_true : bdestruct.
bdestruct (bvs k); auto.
#[local] Remove Hints n_reflect_true : bdestruct.
exfalso. inversion H. rewrite <- H4 in H0. Qcrush.
Qed.

Lemma not_free_prop1 : forall {T k}, not_free k T -> forall {U d}, ([[k ~> U ~ d ]]ᵀ T) = T.
  unfold not_free. induction T; intros; try destruct v; try solve [simpl; auto].
  simpl in *. destruct (k =? i) eqn:Heqki; intuition. inversion H.
  auto. simpl in H. inversion H.
  rewrite H1, H2, H3, H4. simpl. rewrite IHT1; auto. rewrite IHT2; auto.
  repeat rewrite open_qual_not_free; auto.
  simpl in H. inversion H.
  rewrite H1, H2, H3, H4. simpl. rewrite IHT1; auto. rewrite IHT2; auto.
  repeat rewrite open_qual_not_free; auto.
  simpl in H. inversion H. rewrite H1, H2. simpl. rewrite IHT; auto.
  rewrite open_qual_not_free; auto.
Qed.

Lemma not_free_prop2 : forall {T k}, not_free k T -> forall {U d V d'}, ([[k ~> U ~ d ]]ᵀ T) = ([[k ~> V ~ d' ]]ᵀ T).
  intros. repeat rewrite not_free_prop1; auto.
Qed.
#[global] Hint Resolve not_free_prop2 : core.

Lemma not_free_prop3 : forall {T k}, not_free k T -> forall {f l}, closed_ty (S k) f l T -> closed_ty k f l T.
  intros. rewrite <- (@not_free_prop1 _ _ H TUnit ∅). eapply closed_ty_open'; eauto.
Qed.

(* Main results: type soundness & preservation of separation *)

Lemma Qqplus_upper_l : forall {d1 d2}, d1 ⊑↑ (d1 ⋓ d2).
  intros. qual_destruct d1. unfold_q. destruct fr; auto. Qcrush.
Qed.
(* #[global] Hint Resolve Qqplus_upper_l : core. *)

Lemma qqplus_upper_l : forall {d1 d2}, d1 ⊑ (d1 ⋓ d2).
  intros. apply Q_lift_subq. apply Qqplus_upper_l.
Qed.
(* #[global] Hint Resolve qqplus_upper_l : core. *)

Lemma qqplus_qbot_right_neutral : forall {d}, (d ⋓ ∅) = d.
intros. qual_destruct d. unfold_q. destruct fr; auto. apply Q_lift_eq. Qcrush.
Qed.
#[global] Hint Resolve qqplus_qbot_right_neutral : core.

Lemma qqplus_qbot_left_cancel : forall {d}, (∅ ⋓ d) = ∅.
intros. unfold_q. auto.
Qed.
#[global] Hint Resolve qqplus_qbot_left_cancel : core.

Lemma Subqual_qqplus : forall {d1 d2 d}, d1 ⊑↑ d2 -> d1 ⋓ d ⊑↑ d2 ⋓ d.
  intros. qual_destruct d1. qual_destruct d2. qual_destruct d. unfold_q. destruct fr; destruct fr0; Qcrush.
Qed.
(* #[global] Hint Resolve Subqual_qqplus : core. *)

Lemma subqual_qqplus : forall {d1 d2 d}, d1 ⊑ d2 -> d1 ⋓ d ⊑ d2 ⋓ d.
  intros. apply Q_lift_subq. apply Q_lift_subq' in H. apply Subqual_qqplus; auto.
Qed.
(* #[global] Hint Resolve subqual_qqplus : core. *)

Lemma Subqual_qqplus_l : forall {d1 d2 d}, d1 ⊑↑ d2 -> d ⋓ d1 ⊑↑ d ⋓ d2.
  intros. qual_destruct d. qual_destruct d1. qual_destruct d2. unfold_q. destruct fr; destruct fr0; Qcrush.
Qed.
(* #[global] Hint Resolve Subqual_qqplus_l : core. *)

Lemma subqual_qqplus_l : forall {d1 d2 d}, d1 ⊑ d2 -> d ⋓ d1 ⊑ d ⋓ d2.
  intros. apply Q_lift_subq. apply Q_lift_subq' in H. apply Subqual_qqplus_l; auto.
Qed.
(* #[global] Hint Resolve subqual_qqplus_l : core. *)

Lemma Qqplus_bound : forall {q1 q2 q3}, q1 ⊑↑ q3 -> q2 ⊑↑ q3 -> q1 ⋓ q2 ⊑↑ q3.
  intros. qual_destruct q1. unfold_q. destruct fr; Qcrush.
Qed.

Lemma qqplus_bound : forall {q1 q2 q3}, q1 ⊑ q3 -> q2 ⊑ q3 -> q1 ⋓ q2 ⊑ q3.
  intros. apply Q_lift_subq. apply Q_lift_subq' in H,H0. apply Qqplus_bound; auto.
Qed.

Lemma not_fresh_qqplus : forall {d1 d'}, ♦∉ d1 -> (d1 ⋓ d') = d1.
  intros. qual_destruct d1. unfold_q. destruct fr; Qcrush.
Qed.
#[global] Hint Resolve not_fresh_qqplus : core.

Theorem type_safety: forall {Σ t T d},
  has_type [] (qdom Σ) Σ t T d -> wf_senv Σ -> (
    value t \/
    (forall {σ} , CtxOK [] (qdom Σ) Σ σ ->
      (exists t' σ',
        step t σ t' σ' /\ preserve [] Σ t' T d σ'
      )
    )
  ).

Proof.
  intros Σ t T d H HwfSigma.
  specialize (has_type_closed H) as HX. remember [] as G. remember t as tt. remember T as TT. remember (qdom Σ) as φ.
  revert T t HeqTT Heqtt HeqG Heqφ.
  induction H; try (left; constructor); intros.

  + (* t_tapp *) right. subst. intuition.
     apply has_type_closed in H as HH. intuition.
     specialize (H13 (TAll d1 d2 T1 T2) t). intuition.

     - (* contraction *)
       (* turn has_type to vtp *)
       apply has_type_vtp in H as VH; intuition.
       pose (VHH := VH). inversion VH. subst.

       exists (t0 <~ᵗ (ttabs t0); tunit). exists σ. intuition.
       * constructor.

       * apply (Preserve Σ ∅); auto.
         rewrite qqplus_qbot_right_neutral.
         replace (d2 <~ᵈ df; d1 ⋓ ∅) with (d2 <~ᵈ df; d1) by solve [unfold qqplus; destruct (♦∈? d2 <~ᵈ df; d1); auto; rewrite qor_empty_right; auto].
         apply qstp_closed in H27 as H32'; intuition.
         change (length []) with 0 in *.
         pose (VH' := H25). eapply t_tabs with (φ:=df1) in VH'; eauto. apply has_type_vtp in VH'; auto.
         assert (HT' : has_type [(bind_ty, false, T1, d1) ; (bind_tm, true, TAll d0 d3 T0 T3, df1)] (df1 ⊔ $!0 ⊔ $!1 ⊔ {♦}) Σ (open_tm' ([]:tenv) t0) (open_ty' ([]:tenv) T3) (openq' ([]:tenv) d3)). {
           eapply narrowing_ty. eapply H25. intuition.
         }
         eapply @substitution1_ty in HT' as HT''; eauto; intuition.

         unfold open_tm' in HT''. unfold open_ty' in HT''. unfold openq' in HT''. simpl in HT''. inversion H23; subst. inversion H24. subst.
         unfold open_ty in HT''. unfold openq in HT''.

         erewrite <- open_subst2_tm in HT''; eauto.
         erewrite <- open_subst2_ty in HT''; eauto.
         erewrite <- open_subst2_qual in HT''; eauto.
         fold (open_tm (ttabs t0) tunit t0) in HT''. fold (openq df1 d1 d3) in HT''. fold (open_ty (TAll d0 d3 T0 T3) df1 T1 d1 T3) in HT''.
         apply @weaken_flt with (φ':= (qdom Σ)) in HT''; auto; intuition.
         eapply t_sub; eauto. eauto.
         pose (Hsub:=H30). eapply @substitution_ty_stp1 with (df:=df1) in Hsub; eauto.
         simpl in Hsub. unfold openq' in Hsub. unfold openq in Hsub. unfold open_ty' in Hsub. unfold open_ty in Hsub. simpl in Hsub.
         erewrite <- open_subst2_ty in Hsub; eauto. erewrite <- open_subst2_ty in Hsub; eauto.
         erewrite <- open_subst2_qual in Hsub; eauto. erewrite <- open_subst2_qual in Hsub; eauto.
         unfold open_ty. unfold openq.
         replace ([[0 ~> TUnit ~ ∅ ]]ᵀ T2) with ([[0 ~> TAll d0 d3 T0 T3 ~ df1 ]]ᵀ T2); auto. (* since not_free 0 T2 *)

         eapply s_trans; eauto. apply stp_refl; auto. apply closed_ty_open2; auto.
         constructor. eapply openq_mono; eauto. apply qstp_empty in H27. auto. apply openq_closed; auto.

         eapply openq_subqual; eauto. apply has_type_filter in H. auto.
         eapply senv_saturated_openq; eauto.
         repeat apply qor_bound; auto. apply has_type_filter in H. apply qstp_empty in H27.
         Qcrush; eauto.
     -  (* left congruence *)
        specialize (H17 σ H11). destruct H17 as [t0' [σ' HH7]]. exists (ttapp t0'). exists σ'. intuition. constructor. intuition.
        destruct H17.
        #[local] Hint Resolve n_reflect_true : bdestruct.
        bdestruct ((qbvs d2) 0).
        #[local] Remove Hints n_reflect_true : bdestruct.
        * (* d2 is dependent on f, so the growth in df might be observable  *)
          apply (Preserve Σ' d'); auto.
          -- eapply disjointq_scale; eauto. eapply openq_subqual_0; eauto. (* this is the sole reason why need to distinguish whether d2 is dependent on f or not *)
          -- destruct (♦∈? df) eqn:Hfresh.
             ** erewrite @openq_duplicate_eq_l with (f:=0) (l:=‖Σ'‖). 3,4 : eapply closed_qual_monotone; eauto. 2,3 : eauto.
                eapply t_sub with (T1 := (T2 <~ᵀ TUnit ~ ∅; T1 ~ d1))(d1 := (openq (df ⋓ d') d1 d2)).
                --- apply t_tapp; auto; apply extends_length in H17 as H17'.
                    eapply closed_ty_monotone; eauto.
                    eapply closed_qual_monotone; eauto.
                    1,2 : Qcrush; eauto using Nat.lt_le_trans.
                    1,2 : eapply weaken_store_senv_saturated; eauto.
                --- apply stp_refl. simpl. eapply closed_ty_monotone; eauto.
                    constructor; auto. apply Qqplus_upper_l. apply closed_qual_qqplus; auto.
                    inversion H15; subst. apply openq_closed. 2 : apply closed_qual_qqplus.
                    1,2,4 : eapply closed_qual_monotone; eauto; lia. all: eapply disjointq_closed; eauto.
                --- apply has_type_filter in H. apply Qqplus_bound.
                    #[global] Hint Resolve Nat.lt_le_trans : core.
                    eapply openq_subqual. eauto. apply Qqplus_bound. 1,3,4: eapply Subq_trans; eauto. all: eauto.
                --- apply senv_saturated_qqplus; eauto. eapply senv_saturated_openq.
                    apply senv_saturated_qqplus; eauto. 1,3,5 : eapply weaken_store_senv_saturated; eauto.
                    eapply has_type_senv_saturated; eauto. apply closed_qual_qqplus. 1,3 : eapply closed_qual_monotone; eauto. eauto.
             ** rewrite not_fresh_qqplus in H22; auto. apply t_sub with (T1:=(T2 <~ᵀ TUnit ~ ∅; T1 ~ d1)) (d1:=d2 <~ᵈ df; d1).
                --- apply t_tapp; auto.
                    eapply closed_ty_monotone; eauto.
                    eapply closed_qual_monotone; eauto.
                    1,2 : eapply Subq_trans; eauto. 1,2: eapply weaken_store_senv_saturated; eauto.
                --- inversion H15. subst. clear H33. apply stp_refl. simpl. eapply closed_ty_monotone; eauto.
                    constructor. auto. apply Qqplus_upper_l. apply closed_qual_qqplus; auto.
                    apply openq_closed; try solve [eapply closed_qual_monotone; eauto]. eauto.
                --- apply Qqplus_bound. apply has_type_filter in H. eapply openq_subqual; eauto. eauto.
                --- apply senv_saturated_qqplus; eauto. eapply weaken_store_senv_saturated; eauto. eapply senv_saturated_openq.
                    eapply has_type_senv_saturated; eauto. apply has_type_closed in H. intuition. eauto. all : auto.
        * (* d2 is not dependent on f, so we don't observe the growth in df *)
          apply (Preserve Σ' ∅); auto. rewrite qqplus_qbot_right_neutral.
          replace (d2 <~ᵈ df; d1) with (d2 <~ᵈ df ⋓ d'; d1). (* since f doesn't occur in d2 *)
          apply t_tapp; auto.
          eapply closed_ty_monotone; eauto.
          eapply closed_qual_monotone; eauto.
          1,2 : eapply Subq_trans; eauto. 1,2 : eapply weaken_store_senv_saturated; eauto.
          apply openq_subqual_0_false; auto.

  + (* t_app_fresh *) right. subst. intuition.
     apply has_type_closed in H as HH. intuition.
     specialize (H18 (TAll (df' ⋒ d1') d2 T1 T2) t). intuition.

     - (* contraction *)
       (* turn has_type to vtp *)
       apply has_type_vtp in H as VH; intuition.
       pose (VHH := VH). inversion VH. subst.

       exists (t0 <~ᵗ (ttabs t0); tunit). exists σ. intuition.
       * constructor.

       * apply (Preserve Σ ∅); auto. rewrite qqplus_qbot_right_neutral.
         apply qstp_closed in H32 as H37'; intuition.

         change (length []) with 0 in *. subst.
         pose (VH' := H30). eapply t_tabs with (φ:=df1) in VH'; eauto. apply has_type_vtp in VH'; auto.

         (* remove potential freshness flag from the argument, in order to apply substitution lemma *)
         remember (false,(qfvs d1),(qbvs d1),(qlocs d1)) as d1''.
         assert (Hd1'' : d1'' ⊑↑ d1'). { subst. Qcrush. }
         assert (Hdf1 : df1 ⊑↑ df'). { apply qstp_empty in H32. Qcrush. }
         assert (Hd1''fr : ♦∉ d1''). { subst. auto. }

         assert (HT' : has_type [(bind_ty, false, T1, df' ⋒ d1') ; (bind_tm, true, TAll d0 d3 T0 T3, df1)] (df1 ⊔ $!0 ⊔ $!1 ⊔ {♦}) Σ (open_tm' ([]:tenv) t0) (open_ty' ([]:tenv) T3) (openq' ([]:tenv) d3)). {
           eapply narrowing_ty. eapply H30. intuition.
         }
         eapply @substitution2_ty with (dx:=d1'') in HT' as HT''; eauto; intuition.

         unfold open_tm' in HT''. unfold open_ty' in HT''. unfold openq' in HT''. simpl in HT''. inversion H29; subst.
         unfold open_ty in HT''. unfold openq in HT''.

         erewrite <- open_subst2_tm in HT''; eauto.
         erewrite <- open_subst2_ty in HT''; eauto.
         erewrite <- open_subst2_qual in HT''; eauto.
         fold (open_tm (ttabs t0) tunit t0) in HT''. fold (openq df1 (false,(qfvs d1),(qbvs d1),(qlocs d1)) d3) in HT''.
         apply @weaken_flt with (φ':= (qdom Σ)) in HT''; auto; intuition.
         eapply t_sub; eauto.

         inversion H28. subst. rename H35 into Hsub.
         eapply @substitution_stp2_ty with (dx := (false,(qfvs d1),(qbvs d1),(qlocs d1))) (df:=df1) in Hsub; eauto.

         simpl in Hsub. unfold openq' in Hsub. unfold openq in Hsub. simpl in Hsub.
         unfold open_ty' in Hsub. unfold open_ty in Hsub.
         erewrite <- open_subst2_ty in Hsub; eauto. erewrite <- open_subst2_ty in Hsub; eauto.
         erewrite <- open_subst2_qual in Hsub; eauto. erewrite <- open_subst2_qual in Hsub; eauto.
         fold (openq df1 (false,(qfvs d1),(qbvs d1),(qlocs d1)) d3) in Hsub. fold (openq df1 (false,(qfvs d1),(qbvs d1),(qlocs d1)) d2) in Hsub.
         fold (open_ty (TAll d0 d3 T0 T3) df1 T1 (false,(qfvs d1),(qbvs d1),(qlocs d1)) T3) in Hsub. fold (open_ty (TAll d0 d3 T0 T3) df1 T1 (false,(qfvs d1),(qbvs d1),(qlocs d1)) T2) in Hsub.
         fold (open_ty (TAll d0 d3 T0 T3) df1 T1 (false,(qfvs d1),(qbvs d1),(qlocs d1)) T3).
         (* need to reason about growth of d1 *)
         { destruct (♦∈? d1) eqn:Hfresh.
         ++ (* d1 fresh, so the function can't be dependent on the argument *)
            intuition. replace (T2 <~ᵀ TUnit ~ ∅; T1 ~ d1) with T2.
            replace (T2 <~ᵀ (TAll d0 d3 T0 T3) ~ df1; T1 ~ (false,(qfvs d1),(qbvs d1),(qlocs d1))) with T2 in Hsub. (* since no dependence *)
            eapply s_trans; eauto. apply stp_refl; auto. apply not_free_prop3; auto. apply not_free_prop3; auto.
            constructor; auto. eapply openq_mono; eauto. apply qstp_empty in H32. auto. Qcrush.
            all : unfold open_ty; rewrite not_free_prop1; auto. all : rewrite not_free_prop1; auto.
         ++ (* d1 non-fresh *)
            assert (Hd1 : (false,(qfvs d1),(qbvs d1),(qlocs d1))= d1). { qual_destruct d1. unfold_q. apply Q_lift_eq. Qcrush. eauto. }
            rewrite Hd1 in *. replace (T2 <~ᵀ TUnit ~ ∅; T1 ~ d1) with (T2 <~ᵀ (TAll d0 d3 T0 T3) ~ df1; T1 ~ d1). (* since no dependence *)
            eapply s_trans; eauto. apply stp_refl; auto. apply closed_ty_open2; auto. constructor; auto.
            eapply openq_mono; eauto. apply qstp_empty in H32. auto.
            unfold open_ty. f_equal. auto.
         }

         eapply openq_subqual; eauto. apply has_type_filter in H.
         eapply senv_saturated_openq; eauto.
         repeat apply Qor_bound; eauto.
         subst. apply senv_saturated_non_fresh. auto.
     -  (* left congruence *)
        apply has_type_closed in H as Hcl. intuition.
        specialize (H22 σ H16). destruct H22 as [t0' [σ' HH6]]. exists (ttapp t0'). exists σ'. intuition. constructor. intuition.
        destruct H26. destruct (♦∈? df) eqn:Hfresh.
       * (* df fresh *)
         #[local] Hint Resolve n_reflect_true : bdestruct.
         bdestruct ((qbvs d2) 0).
         #[local] Remove Hints n_reflect_true : bdestruct.
          -- (* d2 dependent on f *) apply (Preserve Σ' d'); auto.
            eapply disjointq_scale; eauto. eapply openq_subqual_0; eauto.
            erewrite @openq_duplicate_eq_l with (l:=‖Σ'‖) (f:=0); auto. 2,3 : eapply closed_qual_monotone; eauto. 2: eauto.
            apply t_sub with (T1 := (T2 <~ᵀ TUnit ~ ∅; T1 ~ d1)) (d1 := (openq (df ⋓ d') d1 d2)).
            ** apply has_type_closed in H31 as H31'; intuition.
               apply t_tapp_fresh with (T1 := T1) (df':=df' ⋓ d') (d1' :=d1'); auto. erewrite <- @qqcap_fresh_l with (Σ':=Σ') (Σ:=Σ); eauto.
               eapply Subqual_qqplus; eauto.
               eapply closed_ty_monotone; eauto.
               eapply closed_qual_monotone; eauto.
               eapply Subq_trans; eauto.
               eapply Subq_trans; eauto.
               eapply Subq_trans; eauto.
               apply Qqplus_bound; eauto.
               eapply weaken_store_saturated; eauto.
               apply saturated_qqplus; eauto. eapply weaken_store_saturated; eauto.
               constructor; eauto.
               all: eapply weaken_store_saturated; eauto; constructor; eauto.
            ** apply has_type_closed in H31. intuition. inversion H33. subst.
               apply stp_refl. simpl. eapply closed_ty_monotone; eauto.
               constructor; auto. apply Qqplus_upper_l.
               apply closed_qual_qqplus; auto.
               eapply openq_closed; eauto. inversion H34. eapply closed_qual_monotone; eauto. eauto.
            ** apply has_type_filter in H. apply Qqplus_bound. eapply openq_subqual; eauto.
               apply Qqplus_bound. all: eapply Subq_trans; eauto.
            ** apply senv_saturated_qqplus; eauto. eapply senv_saturated_openq. apply senv_saturated_qqplus.
               1,4,6 : eapply weaken_store_senv_saturated; eauto. eapply has_type_senv_saturated; eauto. eauto.
               apply closed_qual_qqplus. 1,3 : eapply closed_qual_monotone; eauto. eauto.
          -- (* d2 not dependent on f *) apply (Preserve Σ' ∅); auto. rewrite qqplus_qbot_right_neutral.
             replace (d2 <~ᵈ df; d1) with (d2 <~ᵈ df ⋓ d'; d1).
             apply t_tapp_fresh with (T1:=T1) (df':=((df' ⋓ d'))) (d1':=d1'); auto.
             erewrite <- @qqcap_fresh_l with (Σ':=Σ'); eauto.
             eapply Subqual_qqplus; eauto.
             eapply closed_ty_monotone; eauto. eapply closed_Qual_monotone; eauto.
             1,2: eapply Subq_trans; eauto.
             apply Qqplus_bound; eauto.
             eapply weaken_store_saturated; eauto.
             apply saturated_qqplus; eauto.
             eapply weaken_store_saturated; eauto.
             constructor; eauto.
             1,2: eapply weaken_store_senv_saturated; eauto.
             eapply openq_subqual_0_false; auto.
        * (* df not fresh *) rewrite not_fresh_qqplus in H31; auto. apply (Preserve Σ' ∅); auto.
          rewrite qqplus_qbot_right_neutral.
          eapply t_tapp_fresh with (T1:=T1) (df':=df') (d1':=d1'); auto.
          eapply closed_ty_monotone; eauto. eapply closed_qual_monotone; eauto.
          1-3 : eapply Subq_trans; eauto.
          1,2: eapply weaken_store_saturated; eauto. eapply weaken_store_senv_saturated; eauto.
          eapply weaken_store_senv_saturated; eauto.

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

         assert (HT' : has_type [(bind_tm, false, T1, d1) ; (bind_tm, true, TFun d0 d3 T0 T3, df1)] (df1 ⊔ $!0 ⊔ $!1 ⊔ {♦}) Σ (open_tm' ([]:tenv) t) (open_ty' ([]:tenv) T3) (openq' ([]:tenv) d3)). {
           eapply narrowing. eapply H28. intuition. auto.
         }
         eapply @substitution1 with ( vx:= t2) in HT' as HT''; eauto; intuition.

         unfold open_tm' in HT''. unfold open_ty' in HT''. unfold openq' in HT''. simpl in HT''. inversion H26; subst. inversion H27. subst.
         unfold open_ty in HT''. unfold openq in HT''.

         erewrite <- open_subst2_tm in HT''; eauto.
         erewrite <- open_subst2_ty in HT''; eauto.
         erewrite <- open_subst2_qual in HT''; eauto.
         fold (open_tm (tabs t) t2 t) in HT''. fold (openq df1 d1 d3) in HT''. fold (open_ty (TFun d0 d3 T0 T3) df1 T1 d1 T3) in HT''.
         apply @weaken_flt with (φ':= (qdom Σ)) in HT''; auto; intuition.
         eapply t_sub; eauto.

         pose (Hsub:=H33). eapply @substitution_stp1 with (df:=df1) in Hsub; eauto.
         simpl in Hsub. unfold openq' in Hsub. unfold openq in Hsub. unfold open_ty' in Hsub. unfold open_ty in Hsub. simpl in Hsub.
         erewrite <- open_subst2_ty in Hsub; eauto. erewrite <- open_subst2_ty in Hsub; eauto.
         erewrite <- open_subst2_qual in Hsub; eauto. erewrite <- open_subst2_qual in Hsub; eauto.
         unfold open_ty. unfold openq.
         replace ([[0 ~> TUnit ~ ∅ ]]ᵀ T2) with ([[0 ~> TFun d0 d3 T0 T3 ~ df1 ]]ᵀ T2); auto. (* since not_free 0 T2 *)

         eapply s_trans; eauto. apply stp_refl; auto. apply closed_ty_open2; auto.
         constructor. eapply openq_mono; eauto. apply qstp_empty in H30. auto. apply openq_closed; auto.

         eapply openq_subqual; eauto. apply has_type_filter in H. auto.
         eapply senv_saturated_openq; eauto. eapply has_type_senv_saturated; eauto.
         repeat apply Qor_bound; auto. Qcrush; eauto.

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
        eapply weaken_store_senv_saturated; eauto.

     -  (* left congruence *)
        apply has_type_closed in H0 as Hcl. intuition.
        specialize (H19 σ H10). destruct H19 as [t1' [σ' HH7]]. exists (tapp t1' t2). exists σ'. intuition. apply step_c_app_l. intuition.
        destruct H23.
        #[local] Hint Resolve n_reflect_true : bdestruct.
        bdestruct (qbvs d2 0).
        #[local] Remove Hints n_reflect_true : bdestruct.
        * (* d2 is dependent on f, so the growth in df might be observable  *)
          apply (Preserve Σ' d'); auto.
          -- eapply disjointq_scale; eauto. eapply openq_subqual_0; eauto. (* this is the sole reason why need to distinguish whether d2 is dependent on f or not *)
          -- destruct (♦∈? df) eqn:Hfresh.
             ** erewrite @openq_duplicate_eq_l with (f:=0) (l:=‖Σ'‖). 3,4 : eapply closed_qual_monotone; eauto. 2,3 : eauto.
                eapply t_sub with (T1 := (T2 <~ᵀ TUnit ~ ∅; T1 ~ d1))(d1 := (openq (df ⋓ d') d1 d2)).
                --- eapply t_app with (T1:=T1) (df:=(df ⋓ d')); eauto.
                    eapply weaken_flt. eapply weaken_store; eauto. auto. auto.
                    eapply weaken_store_senv_saturated; eauto.
                --- apply stp_refl. simpl. eapply closed_ty_monotone; eauto.
                    constructor; auto. apply Qqplus_upper_l. apply closed_qual_qqplus; auto.
                    inversion H13; subst. apply openq_closed. 2 : apply closed_qual_qqplus.
                    1,2,4 : eapply closed_qual_monotone; eauto; lia. all: eapply disjointq_closed; eauto.
                --- apply has_type_filter in H0. apply has_type_filter in H. apply Qqplus_bound.
                    eapply openq_subqual; eauto. apply Qqplus_bound; eauto.
                    eapply disjointq_Qdom; eauto.
                --- apply senv_saturated_qqplus; eauto. eapply senv_saturated_openq.
                    apply senv_saturated_qqplus; eauto. 1,3,5 : eapply weaken_store_senv_saturated; eauto.
                    1,2 : eapply has_type_senv_saturated; eauto. apply closed_qual_qqplus. 1,3 : eapply closed_qual_monotone; eauto. eauto.
             ** rewrite not_fresh_qqplus in H28; auto. apply t_sub with (T1:=(T2 <~ᵀ TUnit ~ ∅; T1 ~ d1)) (d1:=d2 <~ᵈ df; d1).
                --- eapply t_app with (T1:=T1); eauto. eapply weaken_flt. eapply weaken_store; eauto. auto. auto.
                    eapply weaken_store_senv_saturated; eauto.
                --- inversion H13. subst. clear H39. apply stp_refl. simpl. eapply closed_ty_monotone; eauto.
                    constructor. auto. apply Qqplus_upper_l. apply closed_qual_qqplus; auto.
                    apply openq_closed; try solve [eapply closed_qual_monotone; eauto]. eauto.
                --- apply Qqplus_bound. apply has_type_filter in H0. apply has_type_filter in H. eapply openq_subqual; eauto.
                    eapply disjointq_Qdom; eauto.
                --- apply senv_saturated_qqplus; eauto. eapply weaken_store_senv_saturated; eauto. eapply senv_saturated_openq.
                    eapply has_type_senv_saturated; eauto. apply has_type_closed in H. intuition. eauto.
                    eapply has_type_senv_saturated; eauto. apply has_type_closed in H0. intuition. eauto.
        * (* d2 is not dependent on f, so we don't observe the growth in df *)
          apply (Preserve Σ' ∅); auto. rewrite qqplus_qbot_right_neutral.
          replace (d2 <~ᵈ df; d1) with (d2 <~ᵈ df ⋓ d'; d1). (* since f doesn't occur in d2 *)
          eapply t_app with (T1:=T1); eauto. eapply weaken_flt. eapply weaken_store; eauto. auto. auto.
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
         apply vtp_non_fresh in VH0. remember (false,(qfvs d1),(qbvs d1),(qlocs d1)) as d1''.
         assert (Hd1'' : d1'' ⊑↑ d1'). { subst. Qcrush. }
         assert (Hdf1 : df1 ⊑↑ df'). { apply qstp_empty in H36. eapply Subq_trans; eauto. }
         assert (Hd1''fr : ♦∉ d1''). { subst. auto. }

         assert (HT' : has_type [(bind_tm, false, T1, df' ⋒ d1') ; (bind_tm, true, TFun d0 d3 T0 T3, df1)] (df1 ⊔ $!0 ⊔ $!1 ⊔ {♦}) Σ (open_tm' ([]:tenv) t) (open_ty' ([]:tenv) T3) (openq' ([]:tenv) d3)). {
           eapply narrowing. eapply H34. intuition. auto.
         }
         eapply @substitution2 with ( vx:= t2) in HT' as HT''; eauto; intuition.

         unfold open_tm' in HT''. unfold open_ty' in HT''. unfold openq' in HT''. simpl in HT''. inversion H32; subst.
         unfold open_ty in HT''. unfold openq in HT''.

         erewrite <- open_subst2_tm in HT''; eauto.
         erewrite <- open_subst2_ty in HT''; eauto.
         erewrite <- open_subst2_qual in HT''; eauto.
         fold (open_tm (tabs t) t2 t) in HT''. fold (openq df1 (false,(qfvs d1),(qbvs d1),(qlocs d1)) d3) in HT''.
         apply @weaken_flt with (φ':= (qdom Σ)) in HT''; auto; intuition.
         eapply t_sub; eauto.

         inversion H33. subst. rename H39 into Hsub.
         eapply @substitution_stp2 with (dx := (false,(qfvs d1),(qbvs d1),(qlocs d1))) (df:=df1) in Hsub; eauto.

         simpl in Hsub. unfold openq' in Hsub. unfold openq in Hsub. simpl in Hsub.
         unfold open_ty' in Hsub. unfold open_ty in Hsub.
         erewrite <- open_subst2_ty in Hsub; eauto. erewrite <- open_subst2_ty in Hsub; eauto.
         erewrite <- open_subst2_qual in Hsub; eauto. erewrite <- open_subst2_qual in Hsub; eauto.
         fold (openq df1 (false,(qfvs d1),(qbvs d1),(qlocs d1)) d3) in Hsub. fold (openq df1 (false,(qfvs d1),(qbvs d1),(qlocs d1)) d2) in Hsub.
         fold (open_ty (TFun d0 d3 T0 T3) df1 T1 (false,(qfvs d1),(qbvs d1),(qlocs d1)) T3) in Hsub. fold (open_ty (TFun d0 d3 T0 T3) df1 T1 (false,(qfvs d1),(qbvs d1),(qlocs d1)) T2) in Hsub.
         fold (open_ty (TFun d0 d3 T0 T3) df1 T1 (false,(qfvs d1),(qbvs d1),(qlocs d1)) T3).
         (* need to reason about growth of d1 *)
         { destruct (♦∈? d1) eqn:Hfresh.
         ++ (* d1 fresh, so the function can't be dependent on the argument *)
            intuition. replace (T2 <~ᵀ TUnit ~ ∅; T1 ~ d1) with T2. replace (T2 <~ᵀ (TFun d0 d3 T0 T3) ~ df1; T1 ~ (false,(qfvs d1),(qbvs d1),(qlocs d1))) with T2 in Hsub. (* since no dependence *)
            eapply s_trans; eauto. apply stp_refl; auto. apply not_free_prop3; auto. apply not_free_prop3; auto.
            constructor; auto. eapply openq_mono; eauto. apply qstp_empty in H36. auto. Qcrush.
            all : unfold open_ty; rewrite not_free_prop1; auto. all : rewrite not_free_prop1; auto.
         ++ (* d1 non-fresh *)
            assert (Hd1 : (false,(qfvs d1),(qbvs d1),(qlocs d1))= d1). { apply Q_lift_eq. Qcrush; eauto. }
            rewrite Hd1 in *. replace (T2 <~ᵀ TUnit ~ ∅; T1 ~ d1) with (T2 <~ᵀ (TFun d0 d3 T0 T3) ~ df1; T1 ~ d1). (* since no dependence *)
            eapply s_trans; eauto. apply stp_refl; auto. apply closed_ty_open2; auto. constructor; auto.
            eapply openq_mono; eauto. apply qstp_empty in H36. auto.
            unfold open_ty. f_equal. auto.
         }

         eapply openq_subqual; eauto. apply has_type_filter in H. auto.
         eapply senv_saturated_openq; eauto. eapply has_type_senv_saturated; eauto.
         repeat apply Qor_bound; auto. apply has_type_filter in H; eauto.
         eapply Subq_trans; eauto. 1,2 : inversion H33; auto.

     -  (* right congruence *)
        apply has_type_vtp in H as VH; intuition.
        apply vtp_canonical_form_lam in VH as HH; intuition.
        specialize (H17 σ). intuition.

        destruct H14 as [t2' [σ' HH22]]. exists (tapp t1 t2'). exists σ'. intuition. constructor; intuition.

        destruct H17. destruct (♦∈? d1) eqn:Hfresh.
        * (* d1 fresh *)
          #[local] Hint Resolve n_reflect_true : bdestruct.
          bdestruct (qbvs d2 1).
          #[local] Remove Hints n_reflect_true : bdestruct.
          -- (* d2 dependent on x *) apply (Preserve Σ' d'); auto.
             eapply disjointq_scale; eauto. eapply openq_subqual_1; eauto. intuition.
             replace (T2 <~ᵀ TUnit ~ ∅; T1 ~ d1) with (T2 <~ᵀ TUnit ~ ∅; T1 ~ (d1 ⋓ d')). (* T2 not dependent on x *)
             rewrite openq_duplicate_eq_r; auto. apply t_sub with (T1 := (T2 <~ᵀ TUnit ~ ∅; T1 ~ (d1 ⋓ d'))) (d1 := (openq df (d1 ⋓ d') d2)).
             ** eapply t_app_fresh with (T1 := T1) (d1':=d1' ⋓ d') (df':=df') (df:=df); eauto. replace (df' ⋒ d1' ⋓ d') with (df' ⋒ d1').
                eapply weaken_flt. eapply weaken_store; eauto. all : auto. eapply @qqcap_fresh_r with (Σ':=Σ'); eauto.
                eapply Subqual_qqplus; eauto. apply Qqplus_bound; eauto.
                apply saturated_qqplus; eauto. 1,3: eapply weaken_store_saturated; eauto.
                constructor; eauto.
                eapply weaken_store_saturated; eauto. constructor; eauto.
            **  apply has_type_closed in H30. intuition. inversion H19. subst.
                apply stp_refl. unfold open_ty. eapply closed_ty_open2; eauto. eapply closed_ty_monotone; eauto.
                constructor; auto. apply Qqplus_upper_l. apply closed_Qual_qqplus; auto.
                eapply openq_closed; try solve [eapply closed_qual_monotone; eauto]. eauto.
            **  apply has_type_filter in H2. apply has_type_filter in H. apply Qqplus_bound. eapply openq_subqual; eauto.
                apply Qqplus_bound; eauto. eapply Subq_trans; eauto.
            **  apply senv_saturated_qqplus; eauto. eapply senv_saturated_openq.
                1, 5 : eapply weaken_store_senv_saturated; eauto. 1,3 : eapply has_type_senv_saturated; eauto.
                2 : apply closed_qual_qqplus. 1,2 : eapply closed_qual_monotone; eauto. eauto.
            ** unfold open_ty. apply not_free_prop2. rewrite not_free_prop1; auto.
          -- (* d2 not dependent on x *) apply (Preserve Σ' ∅); auto. rewrite qqplus_qbot_right_neutral. intuition.
             replace (d2 <~ᵈ df; d1) with (d2 <~ᵈ df; (d1 ⋓ d')).  replace (T2 <~ᵀ TUnit ~ ∅; T1 ~ d1) with (T2 <~ᵀ TUnit ~ ∅; T1 ~ (d1 ⋓ d')). (* T2 not dependent on x *)
             eapply t_app_fresh with (T1:=T1) (d1':=((d1' ⋓ d'))); eauto.
             erewrite <- @qqcap_fresh_r with (Σ':=Σ'); eauto.
             eapply weaken_flt. eapply weaken_store; eauto. auto. auto.
             eapply Subqual_qqplus; eauto. eapply Qqplus_bound; eauto.
             apply saturated_qqplus; eauto.
             eapply weaken_store_saturated; eauto.
             constructor; eauto.
             eapply weaken_store_saturated; eauto.
             eapply weaken_store_senv_saturated; eauto.
             unfold open_ty. repeat rewrite not_free_prop1; auto.
             eapply openq_subqual_1_false; eauto.
        * (* d1 not fresh *) rewrite not_fresh_qqplus in H30; auto. apply (Preserve Σ' ∅); auto.
          rewrite qqplus_qbot_right_neutral.
          eapply t_app_fresh with (T1:=T1); eauto. eapply weaken_flt. eapply weaken_store; eauto. auto. auto.
          1,2 : eapply weaken_store_saturated; eauto. eapply weaken_store_senv_saturated; eauto.

     -  (* left congruence *)
        apply has_type_closed in H2 as Hcl. intuition.
        specialize (H25 σ H16). destruct H25 as [t1' [σ' HH6]]. exists (tapp t1' t2). exists σ'. intuition. apply step_c_app_l. intuition.
        destruct H29. destruct (♦∈? df) eqn:Hfresh.
        * (* df fresh *)
          #[local] Hint Resolve n_reflect_true : bdestruct.
          bdestruct (qbvs d2 0).
          #[local] Remove Hints n_reflect_true : bdestruct.
          -- (* d2 dependent on f *) apply (Preserve Σ' d'); auto.
            eapply disjointq_scale; eauto. eapply openq_subqual_0; eauto.
            erewrite @openq_duplicate_eq_l with (l:=‖Σ'‖) (f:=0); auto. 2,3 : eapply closed_qual_monotone; eauto. 2: eauto.
            apply t_sub with (T1 := (T2 <~ᵀ TUnit ~ ∅; T1 ~ d1)) (d1 := (openq (df ⋓ d') d1 d2)).
            ** eapply t_app_fresh with (T1 := T1) (df':=df' ⋓ d'); eauto. erewrite <- @qqcap_fresh_l with (Σ':=Σ'); eauto.
               eapply Subqual_qqplus; eauto.
               eapply weaken_flt. eapply weaken_store; eauto. auto. auto.
               eapply Qqplus_bound; eauto.
               eapply weaken_store_saturated; eauto.
               apply saturated_qqplus; eauto.
               constructor; eauto.
               eapply weaken_store_saturated; eauto.
               constructor; eauto.
               eapply weaken_store_senv_saturated; eauto.
            ** apply has_type_closed in H34. intuition. inversion H19. subst.
               apply stp_refl. simpl. eapply closed_ty_monotone; eauto.
               constructor; auto. apply Qqplus_upper_l. apply closed_Qual_qqplus; auto. apply openQ_closed; eauto. eauto.
            ** apply has_type_filter in H2. apply has_type_filter in H. apply Qqplus_bound. eapply openq_subqual; eauto.
               apply Qqplus_bound. eapply Subq_trans; eauto. all : eauto.
            ** apply senv_saturated_qqplus; eauto. eapply senv_saturated_openq. apply senv_saturated_qqplus.
               1,4,6 : eapply weaken_store_senv_saturated; eauto. 1,2 : eapply has_type_senv_saturated; eauto. eauto.
               apply closed_qual_qqplus. 1,3 : eapply closed_qual_monotone; eauto. eauto.
          -- (* d2 not dependent on f *) apply (Preserve Σ' ∅); auto. rewrite qqplus_qbot_right_neutral.
             replace (d2 <~ᵈ df; d1) with (d2 <~ᵈ df ⋓ d'; d1).
             eapply t_app_fresh with (T1:=T1) (df':=((df' ⋓ d'))); eauto.
             erewrite <- @qqcap_fresh_l with (Σ':=Σ'); eauto.
             eapply Subqual_qqplus; eauto.
             eapply weaken_flt. eapply weaken_store; eauto. auto. auto.
             apply Qqplus_bound; eauto.
             2 : apply saturated_qqplus; eauto.
             1,2 : eapply weaken_store_saturated; eauto. constructor; eauto.
             eapply weaken_store_senv_saturated; eauto.
             eapply openq_subqual_0_false; auto.
        * (* df not fresh *) rewrite not_fresh_qqplus in H34; auto. apply (Preserve Σ' ∅); auto.
          rewrite qqplus_qbot_right_neutral.
          eapply t_app_fresh with (T1:=T1); eauto. eapply weaken_flt. eapply weaken_store; eauto. auto. auto.
          1,2 : eapply weaken_store_saturated; eauto. eapply weaken_store_senv_saturated; eauto.

    + (*tref*) subst. intuition. specialize (has_type_closed H) as HH. intuition. specialize (H8 T t). intuition.
      * (*contraction*) right. intros.
        exists (tloc (‖σ‖)). exists (t :: σ). intuition.
        econstructor; eauto. apply (Preserve ((T,d1) :: Σ) (d1 ⊔ &!‖σ‖)); auto.
        apply wf_senv_cons; auto. eapply has_type_senv_saturated; eauto.
        eapply CtxOK_weaken_flt. apply CtxOK_ext; auto. apply H8. all: auto.
        inversion H8. rewrite <- H13. eapply disj_loc; eauto. Qcrush. eapply has_type_senv_saturated; eauto.
        inversion H8. rewrite qqplus_fresh; auto. rewrite qor_assoc. rewrite <- @qor_assoc with (q1:={♦}). rewrite qor_idem.
        apply t_sub with (T1:=TRef d1 T) (d1:=(d1 ⊔ &!‖σ‖)).
        apply t_loc; auto. rewrite <- H13.
        apply indexr_head. simpl. eapply closed_qual_monotone; eauto. rewrite <- H13. Qcrush. simpl. lia.
        unfold qdom. Qcrush; eauto.
        apply stp_refl; auto. constructor; auto. simpl. eapply closed_qual_monotone; eauto.
        constructor. Qcrush.
        apply closed_Qual_qor; eauto. rewrite <- H13. Qcrush.
        rewrite <- H13.
        apply has_type_filter in H. repeat apply Qor_bound; eauto.
        unfold qdom. Qcrush. simpl. lia.
        rewrite <- H13.
        rewrite <- qor_assoc.
        apply saturated_senv_qor; auto.
        eapply wf_senv_saturated_qplus. apply wf_senv_cons; eauto. eapply has_type_senv_saturated; eauto.
        rewrite indexr_head. eauto.
      * (*congruence*) right. intros. specialize (H11 σ H8). destruct H11 as [t' [σ' HH10]].
        exists (tref t'). exists σ'. intuition. econstructor; eauto.
        destruct H13. apply (Preserve Σ' ∅); intuition. rewrite qqplus_qbot_right_neutral.
        rewrite not_fresh_qqplus in H17; auto.

    + (*tderef*) subst. intuition. specialize (has_type_closed H) as HH. intuition. specialize (H8 (TRef d1 T0) t). intuition.
      * (* contraction *) right. intros. pose (HV := H). apply has_type_vtp in HV; intuition.

        specialize (vtp_canonical_form_loc HV) as Hcan. intuition. destruct H13 as [l HH10]. subst.

        pose (HHV := HV). inversion HHV. subst.  pose (HH3 := H8). inversion HH3. subst.
        pose (HH14 := H19). apply indexr_var_some' in HH14. rewrite H13 in HH14. apply indexr_var_some in HH14.
        destruct HH14 as [v HHH14].  exists v. exists σ. intuition. apply step_deref; intuition.
        apply (Preserve Σ ∅); intuition. rewrite qqplus_qbot_right_neutral.
        specialize (H14 l v T d1). apply t_sub with (T1 := T)(d1:= d1); auto. intuition.
        replace (d1) with (∅ ⊔ d1); auto. apply stp_scale_qor; auto. eapply weaken_stp_store_ext; eauto. rewrite qor_empty_left; auto.

      * (*congruence *) right. intros. specialize (H11 σ H8).
        destruct H11 as [t' [σ' HH8]]. exists (tderef t'). exists σ'. intuition. constructor; auto.
        destruct H13. apply (Preserve Σ' ∅); intuition. rewrite qqplus_qbot_right_neutral. eapply t_deref; eauto.
        eapply weaken_store_senv_saturated; eauto.

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
        replace (d1) with (∅ ⊔ d1); auto. apply stp_scale_qor; auto.
        eapply weaken_stp_store_ext; eauto. apply has_type_filter in Ht2; auto.
        rewrite qor_empty_left; auto. Qcrush; eauto.
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
      apply Qqplus_bound. eapply Subq_trans; eauto. eapply disjointq_Qdom; eauto.
      apply senv_saturated_qqplus; eauto. eapply weaken_store_senv_saturated; eauto.
      Unshelve. all: apply 0.
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
    has_type [] (qdom Σ) Σ t T d -> wf_senv Σ ->
    value t \/ forall {σ}, CtxOK [] (qdom Σ) Σ σ -> exists t' σ', step t σ t' σ'.
Proof. intros Σ t T d HT Hwf.
       specialize (type_safety HT). intuition. right. intros σ HCtxOK.
       specialize (H σ). intuition. destruct H0 as [t' [σ' [Hstep  HPreserve]]].
       exists t'. exists σ'. intuition.
Qed.

Lemma preservation : forall {Σ t T d},
    has_type [] (qdom Σ) Σ t T d -> wf_senv Σ ->
    forall{σ}, CtxOK [] (qdom Σ) Σ σ ->
    forall {t' σ'}, step t σ t' σ' ->
    preserve [] Σ t' T d σ'.
Proof.  intros Σ t T d HT Hwf σ  HCtxOK t' σ' HStep.  specialize (type_safety HT). intuition.
  + inversion HStep; subst; inversion H.
  + specialize (H σ HCtxOK). destruct H as [t'' [σ'' [HStep2 HPreserve]]].
    assert (t'' = t' /\ σ' = σ''). { intuition. 1,2: eapply step_deterministic; eauto.  }
    intuition. subst. intuition.
Qed.

Corollary preservation_of_separation : forall {Σ t1 T1 q1 t2 T2 q2},
  has_type [] (qdom Σ) Σ t1 T1 q1 ->
  has_type [] (qdom Σ) Σ t2 T2 q2 -> wf_senv Σ -> q1 ⋒ q2 ⊑↑ {♦} ->
    forall{σ}, CtxOK [] (qdom Σ) Σ σ ->
      forall {t1' σ'}, step t1 σ t1' σ' ->
      forall {t2' σ''}, step t2 σ' t2' σ'' -> separate Σ t1' T1 t2' T2.
  intros Σ t1 T1 q1 t2 T2 q2 HT1 HT2 Hwf Hsep σ HOK t1' σ' Hstep1 t2' σ'' Hstep2.
  (* execute preservation in sequence *)
  specialize (preservation HT1 Hwf HOK Hstep1) as P1. destruct P1 as [Σ' d1 Hext1 Hwf' HOK' Hdisj1 HT1'].
  assert (HT2': has_type [] (qdom Σ') Σ' t2 T2 q2). {
    eapply weaken_flt. eapply weaken_store. eauto. auto. apply extends_qdom; auto. auto.
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
