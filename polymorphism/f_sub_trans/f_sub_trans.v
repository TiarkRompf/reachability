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

Fixpoint unsplice_ty (n : nat) (T : ty) {struct T} : ty :=
  match T with
  | TTop             => TTop
  | TVar (varF i)    => if lt_dec n i then TVar (varF (Init.Nat.pred i)) else TVar (varF i)
  | TVar (varB i)    => TVar (varB i)
  | TAll d1 d2 T1 T2 => TAll (unsplice_qual n d1) (unsplice_qual n d2) (unsplice_ty n T1) (unsplice_ty n T2)
  | TUnit            => TUnit
  | TFun d1 d2 T1 T2 => TFun (unsplice_qual n d1) (unsplice_qual n d2) (unsplice_ty n T1) (unsplice_ty n T2)
  | TRef d1 T        => TRef (unsplice_qual n d1) (unsplice_ty n T)
  end.

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
    closed_ty b f l T ->
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

(**********
*  tfvs  *
**********)

Fixpoint tfvs (T : ty) (n : nat) {struct T} : bool :=
  match T with
  | TVar (varF i)    => i =? n
  | TAll d1 d2 T1 T2 => qfvs d1 n || qfvs d2 n || tfvs T1 n || tfvs T2 n
  | TFun d1 d2 T1 T2 => qfvs d1 n || qfvs d2 n || tfvs T1 n || tfvs T2 n
  | TRef d1 T        => qfvs d1 n || tfvs T n
  | _                => false
  end.

Fixpoint Tfvs (T : ty) (n : nat) {struct T} : Prop :=
  match T with
  | TVar (varF i)    => i = n
  | TAll d1 d2 T1 T2 => qfvs d1↑ n \/ qfvs d2↑ n \/ Tfvs T1 n \/ Tfvs T2 n
  | TFun d1 d2 T1 T2 => qfvs d1↑ n \/ qfvs d2↑ n \/ Tfvs T1 n \/ Tfvs T2 n
  | TRef d1 T        => qfvs d1↑ n \/ Tfvs T n
  | _                => False
  end.

(**********
*  qenv  *
**********)

Definition env := fun (p : Type) => list p.

Definition tenv := env (binding * bool * ty * qual). (* (binding, isFunctionSelfRef, Type, Qual) *)
Definition senv := env (ty * qual). (* Sigma store typing *)

(* environment with qualifiers *)
Class qenv {p : Type} : Type := {
  (* how to retrieve the qualifier from an environment element *)
  qenv_q : p -> qual;
  (* which component of the qualifier should be used to do transitive lookup *)
  qenv_qn : qual -> nats;
  qenv_Qn : Qual -> Nats;
  qenv_qn_prop : qnmap qenv_qn qenv_Qn;
}.

#[export] Instance tenv_qenv : @qenv (binding * bool * ty * qual) := {
  qenv_q := snd; qenv_qn := qfvs; qenv_Qn := qfvs;
  qenv_qn_prop := qnmap_qfvs;
}.
#[global] Hint Resolve tenv_qenv : core.

#[export] Instance senv_qenv : @qenv (ty * qual) := {
  qenv_q := snd; qenv_qn := qlocs; qenv_Qn := qlocs;
  qenv_qn_prop := qnmap_qlocs;
}.
#[global] Hint Resolve senv_qenv : core.

(* Store typing contains closed types and well-scoped, saturated qualifiers. *)
Inductive wf_senv : senv -> Prop :=
| wf_senv_nil : wf_senv []
| wf_senv_cons : forall Σ T q,
    wf_senv Σ ->
    ♦∉ q ->
    closed_ty 0 0 (‖Σ‖) T ->
    closed_Qual 0 0 (‖Σ‖) q↑ ->
    wf_senv ((T, q) :: Σ)
.
#[global] Hint Constructors wf_senv : core.

Inductive wf_tenv : tenv -> senv -> Prop :=
  | wf_tenv_nil : forall Σ, wf_senv Σ -> wf_tenv [] Σ
  | wf_tenv_cons : forall Γ Σ bd fr T q,
      wf_tenv Γ Σ ->
      closed_ty 0 (‖Γ‖) (‖Σ‖) T ->
      closed_Qual 0 (‖Γ‖) (‖Σ‖) q↑ ->
      wf_tenv ((bd, fr, T, q) :: Γ) Σ
.
#[global] Hint Constructors wf_tenv : core.


(***************************
 *  wf_qenv: "Telescope"  *
 **************************)

Inductive wf_qenv {p : Type} `{qenv p} : (env p) -> Prop :=
  | wf_qenv_nil : wf_qenv []
  | wf_qenv_cons : forall E a,
      wf_qenv E ->
      closed_Nats (‖E‖) (qenv_Qn (qenv_q a) ↑) ->
      wf_qenv (a :: E).
#[global] Hint Constructors wf_qenv : core.

(*****************
*  closed_qenv  *
*****************)

Definition closed_qenv {p : Type} `{qenv p} (b f l : nat) (E : env p) : Prop :=
  forall x a, indexr x E = Some a -> closed_Qual b f l (qenv_q a) ↑.

(********************
*  closed_qenv_qn  *
********************)

Definition closed_qenv_qn {p : Type} `{qenv p} (n : nat) (E : env p) : Prop :=
  forall x a, indexr x E = Some a -> closed_Nats n (qenv_Qn (qenv_q a) ↑).

Fixpoint q_trans_one {p : Type} `{qenv p} (E : env p) (q : qual) :=
  match E with
  | a :: E' => if (qenv_qn q (length E'))
      then qor (q_trans_one E' q) (qenv_q a)
      else (q_trans_one E' q)
  | [] => q
  end.

Definition N_trans_one {p : Type} `{qenv p} (E : env p) (q : Qual) (f : Qual -> Nats) (x : nat) : Prop :=
  f q x \/
    exists x',
      qenv_Qn q x' /\
        exists a, indexr x' E = Some a /\ f (Q_lift (qenv_q a)) x.

Fixpoint q_trans'' {p : Type} `{qenv p} (E : env p) (q : qual) (fuel : nat) {struct fuel} :=
  match fuel with
  | 0 => q
  | S fuel' => q_trans'' E (q_trans_one E q) fuel'
  end.
#[global] Hint Unfold q_trans'' : core.

(* the returning natset contains the component indicated by f, of the transitive closure of q expanding upon environment E *)
Definition N_trans'' {p : Type} `{qenv p} (E : env p) (q : Qual) (f : Qual -> Nats) (fuel : nat) (x : nat) : Prop :=
  f q x \/
  exists fuel', fuel = S fuel' /\
  exists x', qenv_Qn q x' /\
  exists a, indexr x' E = Some a /\ f (Q_lift (q_trans'' E (qenv_q a) fuel')) x.
#[global] Hint Unfold N_trans'' : core.

(******************
*  splicible_env  *
 ******************)

Class splicible_env {p : Type} `{@qenv p}: Type := {
  (* how to splice/unsplice an element in the environment *)
  env_splice : nat -> p -> p;
  env_unsplice : nat -> p -> p;
  env_elmt_fvs : p -> nat -> bool;
  env_splice_unsplice_id : forall {n : nat} {a : p}, (env_unsplice n (env_splice n a)) = a;
  (* env_unsplice_splice_id : forall {n : nat} {a : p}, ~N_lift (qfvs (qenv_q a)) n -> (env_splice n (env_unsplice n a)) = a; *)
}.

Definition splice_tenv_elmt := (fun n (X : (binding * bool * ty * qual)) =>
  match X with
  | (bd, b, T, q) => (bd, b, splice_ty n T, splice_qual n q)
  end).

Definition splice_senv_elmt := (fun n (X : (ty * qual)) =>
  match X with
  | (T, q) => (splice_ty n T, splice_qual n q)
  end).

Definition unsplice_tenv_elmt := (fun n (X : (binding * bool * ty * qual)) =>
  match X with
  | (bd, b, T, q) => (bd, b, unsplice_ty n T, unsplice_qual n q)
  end).

Definition unsplice_senv_elmt := (fun n (X : (ty * qual)) =>
  match X with
  | (T, q) => (unsplice_ty n T, unsplice_qual n q)
  end).

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

| s_ref : forall Γ Σ T1 T2 q1 q2 d1 d2,
    qstp Γ Σ d1 d2 ->
    stp Γ Σ T1 ∅ T2 ∅ ->
    stp Γ Σ T2 ∅ T1 ∅ ->
    closed_Qual 0 (‖Γ‖) (‖Σ‖) q1 ↑ ->
    closed_Qual 0 (‖Γ‖) (‖Σ‖) q2 ↑ ->
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
    q' ⊑↑ q ->
    closed_Qual 0 0 l q' ↑ ->
    saturated_loc Σ l q.
Arguments sat_loc {Σ l q}.
#[global] Hint Constructors saturated_loc : core.

(* deBruijn index v occurs nowhere in T *)
Definition not_free (v : id) (T : ty): Prop := [[ v ~> TUnit ~ ∅ ]]ᵀ T = T.

Definition q_trans_tenv (Γ : tenv) (q : qual) := q_trans'' Γ q (‖Γ‖).
#[global] Hint Unfold q_trans_tenv : core.
Definition q_trans_senv (Σ : senv) (q : qual) := q_trans'' Σ q (‖Σ‖).
#[global] Hint Unfold q_trans_senv : core.

(* the free variable can point to something in the store, but not vise versa *)
Definition q_trans (Γ : tenv) (Σ : senv) (q : qual) := (q_trans_senv Σ (q_trans_tenv Γ q)).
#[global] Hint Unfold q_trans : core.

Definition Q_trans_one {p : Type} `{qenv p} (E : env p) (q : Qual) : Qual :=
  (N_trans_one E q Qfr 0, N_trans_one E q qfvs, N_trans_one E q qbvs, N_trans_one E q qlocs).
#[global] Hint Unfold Q_trans_one : core.

Definition Q_trans'' {p : Type} `{qenv p} (E : env p) (q : Qual) (fuel : nat) : Qual :=
  (N_trans'' E q Qfr fuel 0, N_trans'' E q qfvs fuel, N_trans'' E q qbvs fuel, N_trans'' E q qlocs fuel).
#[global] Hint Unfold Q_trans'' : core.

Definition Q_trans (Γ : tenv) (Σ : senv) (q : Qual) := (Q_trans'' Σ (Q_trans'' Γ q (‖Γ‖)) (‖Σ‖)).
#[global] Hint Unfold Q_trans : core.

Definition qenv_saturated_q {p : Type} `{qenv p} (E : env p) (q : qual) :=
  forall x a,
  qenv_Qn q↑ x ->
  indexr x E = Some a ->
  (qenv_q a) ⊑↑ q.
#[global] Hint Unfold qenv_saturated_q : core.

Definition qenv_saturated_q'' {p : Type} `{qenv p} (E : env p) (q : qual) :=
  q_trans_one E q = q.
#[global] Hint Unfold qenv_saturated_q'' : core.

Definition tenv_saturated (Γ : tenv) (q: qual) := qenv_saturated_q Γ q.
Definition senv_saturated (Σ : senv) (q: qual) := qenv_saturated_q Σ q.

#[global] Hint Unfold tenv_saturated : core.
#[global] Hint Unfold senv_saturated : core.

(* Specifies that q is transitively closed w.r.t. Γ|Σ, i.e., q covers each of its contained variables/locations in Γ|Σ *)
Definition saturated (Γ : tenv) (Σ : senv) (q: qual) := tenv_saturated Γ q /\ senv_saturated Σ q.

Fixpoint cardinality (q : qual) {p : Type} `{qenv p} (E : env p) : nat :=
  match E with
  | [] => 0
  | a :: E' => if qenv_qn q (‖ E' ‖) then S (cardinality q E') else cardinality q E'
  end.

Inductive has_type : tenv -> qual -> senv -> tm -> ty -> qual -> Prop :=
| t_tabs: forall Γ φ Σ t T1 T2 df d1 d2,
    closed_tm 2 (‖Γ‖) (‖Σ‖) t ->
    closed_ty 0 (‖Γ‖) (‖Σ‖) (TAll d1 d2 T1 T2) ->
    closed_Qual 0 (‖Γ‖) (‖Σ‖) φ↑ ->
    d1 ⊑↑ df ⊔ {♦}  ->
    df ⊑↑ φ ->
    ♦∉ df ->
    senv_saturated Σ df ->
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
    senv_saturated Σ (d2 <~ᵈ ∅ ; ∅) ->
    senv_saturated Σ d1 ->
    not_free 0 T2 ->
    has_type Γ φ Σ (ttapp t) (T2 <~ᵀ TUnit ~ ∅ ; T1 ~ d1) (d2 <~ᵈ df ; d1)

| t_tapp_fresh : forall Γ φ Σ t d1 d2 df T1 T2,
    has_type Γ φ Σ t (TAll (q_trans Γ Σ df ⋒ q_trans Γ Σ d1) d2 T1 T2) df ->
    closed_ty 0 (‖Γ‖) (‖Σ‖) T1 ->
    closed_Qual 0 (‖Γ‖) (‖Σ‖) d1↑ ->
    d1 ⊑↑ (φ ⊔ {♦}) ->
    (♦∈ d1 -> not_free 1 T2) ->
    senv_saturated Σ d1 -> (* !!! demanded by has_type_senv_saturated  !!! *)
    not_free 0 T2 ->
    (d2 <~ᵈ ∅ ; ∅) ⊑↑ (φ ⊔ {♦}) ->
    (q_trans Γ Σ d1) ⋒ (q_trans Γ Σ df) ⊑↑ (φ ⊔ {♦}) ->
    senv_saturated Σ (d2 <~ᵈ ∅ ; ∅) ->
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
    d1 ⊑↑ df ⊔ {♦}  ->
    df ⊑↑ φ ->
    ♦∉ df ->
    senv_saturated Σ df ->
    has_type ((bind_tm, false, T1, d1) :: (bind_tm, true, (TFun d1 d2 T1 T2), df) :: Γ)
             (df ⊔ ($!‖Γ‖) ⊔ $!(S (‖Γ‖))) Σ (t <~²ᵗ Γ) (T2 <~²ᵀ Γ) (d2 <~²ᵈ Γ) ->
    has_type Γ φ Σ (tabs t) (TFun d1 d2 T1 T2) df

| t_app : forall Γ φ Σ t1 d1 t2 d2 df T1 T2,
    has_type Γ φ Σ t1 (TFun d1 d2 T1 T2) df ->
    has_type Γ φ Σ t2 T1 d1 ->
    (d2 <~ᵈ ∅ ; ∅) ⊑↑ (φ ⊔ {♦}) ->
    ♦∉ d1 ->
    not_free 0 T2 ->
    senv_saturated Σ (d2 <~ᵈ ∅ ; ∅) ->
    has_type Γ φ Σ (tapp t1 t2) (T2 <~ᵀ TUnit ~ ∅ ; T1 ~ d1) (d2 <~ᵈ df ; d1)

| t_app_fresh : forall Γ φ Σ t1 d1 t2 d2 df T1 T2,
    has_type Γ φ Σ t1 (TFun (q_trans Γ Σ df ⋒ q_trans Γ Σ d1) d2 T1 T2) df ->
    has_type Γ φ Σ t2 T1 d1 ->
    (♦∈ d1 -> not_free 1 T2) ->
    not_free 0 T2 ->
    (d2 <~ᵈ ∅ ; ∅) ⊑↑ (φ ⊔ {♦}) ->
    (q_trans Γ Σ d1) ⋒ (q_trans Γ Σ df) ⊑↑ (φ ⊔ {♦}) ->
    senv_saturated Σ (d2 <~ᵈ ∅ ; ∅) ->
    has_type Γ φ Σ (tapp t1 t2) (T2 <~ᵀ TUnit ~ ∅ ; T1 ~ d1) (d2 <~ᵈ df ; d1)

| t_loc : forall Γ φ Σ l T q,
    closed_Qual 0 (‖Γ‖) (‖Σ‖) φ↑ ->
    indexr l Σ = Some (T,q) ->
    closed_ty 0 0 (‖Σ‖) T ->
    closed_Qual 0 0 (‖Σ‖) q↑ ->
    &!l ⊑↑ φ ->
    senv_saturated Σ q ->
    q ⊑↑ φ ->
    ♦∉ q ->
    has_type Γ φ Σ &l (TRef q T) (q ⊔ &!l)

| t_ref: forall Γ φ Σ T t d1,
    has_type Γ φ Σ t T d1 ->
    closed_ty 0 (‖Γ‖) (‖Σ‖) T ->
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
    d2 ⊑↑ (φ ⊔ {♦}) ->
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

Definition store := list (option tm).

Inductive step : tm -> store -> tm -> store -> Prop :=
(*contraction rules*)
| step_ttapp: forall t σ,
  step (ttapp (ttabs t)) σ (t <~ᵗ (ttabs t); tunit) σ
| step_beta : forall t v σ,
    value v ->
    step (tapp (tabs t) v) σ (t <~ᵗ (tabs t); v) σ
| step_ref : forall v σ,
    value v ->
    step (tref v) σ (&‖σ‖) ((Some v) :: σ)
| step_deref : forall σ l v,
    indexr l σ = Some (Some v) ->
    step (! &l) σ v σ
| step_assign : forall σ l v,
    l < ‖σ‖ ->
    value v ->
    step (tassign &l v) σ tunit (update σ l (Some v))
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
  qdom' σ ⊑↑ qdom Σ /\ ‖ σ ‖ = ‖ Σ ‖ /\
  φ ⊑↑ (qdom' σ) /\ forall l v T q,
  l ∈ₗ φ ->
  indexr l Σ = Some (T,q) ->
  indexr l σ = Some (Some v) ->
  value v /\ has_type Γ φ Σ v T q.

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

(**********************
*  substitutable_env  *
 **********************)

Class substitutable_env {p : Type} `{@qenv p}: Type := {
  (* how to substitute an element in the environment *)
  env_subst : nat -> ty -> qual -> p -> p;
  env_subst_qenv_q_dist : forall a v T' q', subst_qual (qenv_q a) v q' = qenv_q (env_subst v T' q' a)
}.

Definition subst_tenv_elmt := (fun n T' q' (X : (binding * bool * ty * qual)) =>
  match X with
  | (bd, b, T, q) => (bd, b, subst_ty T n T' q', subst_qual q n q')
  end).

Definition subst_senv_elmt := (fun n T' q' (X : (ty * qual)) =>
  match X with
  | (T, q) => (subst_ty T n T' q', subst_qual q n q')
  end).

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
    ♦∉ q ->
    Σ' = (T,q) :: Σ ->
    disjointq Σ Σ' q' (q ⊔ &!‖Σ‖)
.
Arguments disj_loc { Σ Σ' }.
#[global] Hint Constructors disjointq : core.
Notation " S → T ∋ q ⊕ q'" := (disjointq S T q q') (at level 10).

(* :! -- directly invertible value typing *)

Inductive vtp: senv -> qual -> tm -> ty -> qual -> Prop :=
| vtp_tabs: forall Σ φ t T1 T2 T3 T4 d1 d2 d3 d4 df1 df2,
  closed_tm 2 0 (‖Σ‖) t ->
  closed_ty 0 0 (‖Σ‖) (TAll d3 d4 T3 T4) -> (* supertype *)
  closed_ty 0 0 (‖Σ‖) (TAll d1 d2 T1 T2) -> (* subtype *)
  has_type [(bind_ty, false, T1, d1); (bind_tm, true, (TAll d1 d2 T1 T2), df1)] (df1 ⊔ $!0 ⊔ $!1)  Σ
           (t <~²ᵗ ([] : tenv)) (T2 <~²ᵀ ([] : tenv)) (d2 <~²ᵈ ([] : tenv)) ->
  stp [] Σ T3 d3 T1 d1 ->
  qstp [] Σ df1 df2 ->
  stp [(bind_ty, false, T3, d3); (bind_tm, true, (TAll d1 d2 T1 T2), {♦})] Σ
      (T2 <~²ᵀ ([] : tenv)) (d2 <~²ᵈ ([] : tenv))
      (T4 <~²ᵀ ([] : tenv)) (d4 <~²ᵈ ([] : tenv)) ->
  d1 ⊑↑ df1 ⊔ {♦} ->
  ♦∉ df1 ->
  senv_saturated Σ df1 ->
  senv_saturated Σ df2 ->
  vtp Σ φ (ttabs t) (TAll d3 d4 T3 T4) df2

| vtp_base: forall Σ φ d,
  closed_Qual 0 0 (‖Σ‖) d↑ ->
  senv_saturated Σ d ->
  vtp Σ φ tunit TUnit d

| vtp_loc:  forall Σ φ l T U q1 q2 d,
  closed_Qual 0 0 (‖Σ‖) d↑ ->
  closed_ty 0 0 (‖Σ‖) T ->
  closed_Qual 0 0 (‖Σ‖) q1↑ ->
  closed_Qual 0 0 (‖Σ‖) q2↑ ->
  l ∈ₗ φ ->
  indexr l Σ = Some (T,q1) ->
  stp [] Σ T ∅ U ∅ ->
  stp [] Σ U ∅ T ∅ ->
  qstp [] Σ (q2 ⊔ &!l) d ->
  ♦∉ q1 ->
  senv_saturated Σ d ->
  senv_saturated Σ q1 ->
  qstp [] Σ q1 q2 ->
  qstp [] Σ q2 q1 ->
  vtp Σ φ &l (TRef q2 U) d

| vtp_abs: forall Σ φ T1 d1 T2 d2 T3 d3 T4 d4 df1 df2 t,
  closed_tm 2 0 (‖Σ‖) t ->
  closed_Qual 0 0 (‖Σ‖) df2↑ ->
  closed_ty 0 0 (‖Σ‖) (TFun d3 d4 T3 T4) -> (* supertype *)
  closed_ty 0 0 (‖Σ‖) (TFun d1 d2 T1 T2) -> (* subtype *)
  has_type [(bind_tm, false,T1,d1) ; (bind_tm, true, (TFun d1 d2 T1 T2), df1)]
            (df1 ⊔ $!0 ⊔ $!1) Σ (t <~²ᵗ ([] : tenv)) (T2 <~²ᵀ ([] : tenv)) (d2 <~²ᵈ ([] : tenv)) ->
  stp [] Σ T3 d3 T1 d1 ->
  qstp [] Σ df1 df2 ->
  stp [(bind_tm, false,T3, d3) ; (bind_tm, true, (TFun d1 d2 T1 T2), {♦})] Σ
      (T2 <~²ᵀ ([] : tenv)) (d2 <~²ᵈ ([] : tenv))
      (T4 <~²ᵀ ([] : tenv)) (d4 <~²ᵈ ([] : tenv)) ->
  d1 ⊑↑ df1 ⊔ {♦} ->
  ♦∉ df1 ->
  senv_saturated Σ df1 ->
  senv_saturated Σ df2 ->
  vtp Σ φ (tabs t) (TFun d3 d4 T3 T4) df2

| vtp_top: forall Σ φ t T d,
  vtp Σ φ t T d ->
  senv_saturated Σ d ->   (* due to vtp_saturated *)
  vtp Σ φ t TTop d
.
#[global] Hint Constructors vtp : core.

(* The concluding statement of the preservation part of type safety, i.e., typing is preserved after a step under an extended store, so
   that the initial qualifier is increased by at most a fresh storage effect. *)
Inductive preserve (Γ : tenv) (Σ : senv) (φ : qual) (t' : tm) (T : ty) (d : qual) (σ' : store) : Prop :=
| Preserve : forall Σ' d' φ',
    Σ' ⊇ Σ ->
    φ ⊑↑ φ' ->
    d' ⊑↑ φ' ->
    wf_senv Σ' ->
    CtxOK Γ φ' Σ' σ' ->
    Σ → Σ' ∋ d ⊕ d'  ->
    has_type Γ φ' Σ' t' T (d ⋓ d') ->
    preserve Γ Σ φ t' T d σ'.
Arguments Preserve {Γ Σ φ t' T d σ'}.

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

(* Supporting lemmas for basic definitions *)

Lemma tfvs_reflect : forall {T n}, reflect (Tfvs T n) (tfvs T n).
intros. induction T; simpl; intuition.
- destruct v; intuition.
- ndestruct (qfvs q n); ndestruct (qfvs q0 n); destruct (tfvs T1 n); destruct (tfvs T2 n); intuition. all: inversion IHT1; inversion IHT2; intuition. apply iff_reflect. intuition.
- ndestruct (qfvs q n); ndestruct (qfvs q0 n); destruct (tfvs T1 n); destruct (tfvs T2 n); intuition. all: inversion IHT1; inversion IHT2; intuition. apply iff_reflect. intuition.
- ndestruct (qfvs q n); destruct (tfvs T n); intuition. all: inversion IHT; intuition. apply iff_reflect. intuition.
Qed.

Lemma wf_qenv_prop' : forall {p : Type} `{qenv p} (E : env p), wf_qenv E <-> (forall x a, indexr x E = Some a -> (closed_Nats x (qenv_Qn (qenv_q a)↑))).
split.
- intros Hwf x a Hidx. pose proof qenv_qn_prop as Hqn. induction Hwf; intros. simpl in H. discriminate. bdestruct (x =? ‖E‖); subst.
  + simpl in Hidx. rewrite Nat.eqb_refl in Hidx. inversion Hidx. subst. intuition.
  + simpl in Hidx. apply Nat.eqb_neq in H1. rewrite H1 in Hidx. apply IHHwf. auto.
- intros. induction E. auto. constructor. apply IHE. intros. specialize (H0 x a0). erewrite <- indexr_skip in H1; eauto using indexr_var_some',Nat.lt_neq. eapply H0. apply indexr_head.
Qed.

Lemma wf_qenv_prop : forall {p : Type} `{qenv p} (E : env p), wf_qenv E -> (forall x a, indexr x E = Some a -> (closed_Nats x (qenv_Qn ((qenv_q a)↑)))).
intros p ? E. pose proof (wf_qenv_prop' E) as Hwf. inversion Hwf. auto.
Qed.

Lemma wf_qenv_prop'' : forall {p : Type} `{qenv p} (E : env p), wf_qenv E -> (forall x a, indexr x E = Some a -> (closed_Nats (‖ E ‖) (qenv_Qn ((qenv_q a)↑)))).
intros p ? E. pose proof (wf_qenv_prop' E) as Hwf. inversion Hwf. intros. eapply closed_Nats_mono with (n:=x); eauto. apply indexr_extend1 in H3; eauto. lia.
Qed.

Lemma wf_qenv_shrink : forall {p : Type} `{qenv p} {E : env p} {a}, wf_qenv (a::E) -> wf_qenv E.
intros. inversion H0. auto.
Qed.
#[global] Hint Resolve wf_qenv_shrink : core.

Lemma wf_qenv_shrink' : forall {p : Type} `{qenv p} {E E' : env p} , wf_qenv (E'++E) -> wf_qenv E.
intros. induction E'; simpl; auto. apply IHE'. simpl in H0. eapply wf_qenv_shrink; eauto.
Qed.
#[global] Hint Resolve wf_qenv_shrink' : core.

Lemma wf_tenv_wf_qenv : forall Γ Σ,
  wf_tenv Γ Σ ->
  wf_qenv Γ.
intros. induction H; auto. constructor; auto. Qcrush.
Qed.
#[global] Hint Resolve wf_tenv_wf_qenv : core.

Lemma wf_senv_wf_qenv : forall Σ,
  wf_senv Σ ->
  wf_qenv Σ.
intros. induction H; auto. constructor; auto. Qcrush.
Qed.
#[global] Hint Resolve wf_senv_wf_qenv : core.

Lemma closed_qenv_shrink : forall {p : Type} `{qenv p} (E : env p) (a : p) (b f l : nat),
  closed_qenv b f l (a :: E) -> closed_qenv b f l E.
intros. unfold closed_qenv in *. intros. eapply H0. apply indexr_extend1. eauto.
Qed.

Lemma closed_qenv_monotone : forall {p : Type} `{qenv p} (E : env p) {b f l : nat},
  closed_qenv b f l E -> forall b' f' l',
  b <= b' -> f <= f' -> l <= l' ->
  closed_qenv b' f' l' E.
intros. unfold closed_qenv in *. intros. eapply closed_Qual_monotone; eauto.
Qed.

Lemma closed_qenv_extend : forall {p : Type} `{qenv p} (E : env p) (a : p) {b f l : nat},
  closed_qenv b f l E ->
  closed_Qual b f l (qenv_q a) ↑ ->
  closed_qenv b f l (a :: E).
intros. unfold closed_qenv in *. intros. simpl in *. bdestruct (x =? (‖ E ‖)).
- inversion H2. subst. auto.
- apply H0 in H2. auto.
Qed.

Lemma closed_qenv_empty : forall {p : Type} `{qenv p} (b f l : nat) (E : env p),
  closed_qenv b f l [].
unfold closed_qenv. intros. simpl in H0. discriminate.
Qed.
#[global] Hint Resolve closed_qenv_empty : core.

Lemma closed_qenv_qn_shrink : forall {p : Type} `{qenv p} (E : env p) (a : p) (n : nat),
  closed_qenv_qn n (a :: E) -> closed_qenv_qn n E.
intros. unfold closed_qenv_qn in *. intros. eapply H0. apply indexr_extend1. eauto.
Qed.

Lemma closed_qenv_qn_extend : forall {p : Type} `{qenv p} (E : env p) (a : p) {n : nat},
  closed_qenv_qn n E ->
  closed_Nats n (qenv_Qn (qenv_q a) ↑) ->
  closed_qenv_qn n (a :: E).
intros. unfold closed_qenv_qn in *. intros. simpl in *. bdestruct (x =? (‖ E ‖)).
- inversion H2. subst. auto.
- apply H0 in H2. auto.
Qed.

Lemma closed_qenv_qn_monotone : forall {p : Type} `{qenv p} (E : env p) {n : nat},
  closed_qenv_qn n E -> forall n',
  n <= n' ->
  closed_qenv_qn n' E.
intros. unfold closed_qenv_qn in *. intros. eapply closed_Nats_mono; eauto.
Qed.
#[global] Hint Resolve closed_qenv_qn_monotone : core.

Lemma closed_qenv_qn_empty : forall {p : Type} `{qenv p} (E : env p) (n : nat) ,
  closed_qenv_qn n [].
unfold closed_qenv_qn. intros. simpl in H0. discriminate.
Qed.
#[global] Hint Resolve closed_qenv_qn_empty : core.

Lemma wf_tenv_closed_qenv_qn : forall Γ Σ,
  wf_tenv Γ Σ ->
  closed_qenv_qn (‖ Γ ‖) Γ.
intros. induction H; simpl; auto. apply closed_qenv_qn_empty. apply ([]:tenv).
apply closed_qenv_qn_extend; eauto. Qcrush.
Qed.
#[global] Hint Resolve wf_tenv_closed_qenv_qn : core.

Lemma wf_senv_closed_qenv_qn : forall Σ,
  wf_senv Σ ->
  closed_qenv_qn (‖ Σ ‖) Σ.
intros. induction H; simpl; auto. apply closed_qenv_qn_empty. apply ([]:senv).
apply closed_qenv_qn_extend; eauto. Qcrush.
Qed.
#[global] Hint Resolve wf_senv_closed_qenv_qn : core.

Lemma closed_tenv_closed_qn: forall b f l (Γ : tenv), closed_qenv b f l Γ -> closed_qenv_qn f Γ.
intros. unfold closed_qenv, closed_qenv_qn in *. intros. specialize (H x a H0). Qcrush.
Qed.

Lemma closed_senv_closed_qn: forall b f l (Σ : senv), closed_qenv b f l Σ -> closed_qenv_qn l Σ.
intros. unfold closed_qenv, closed_qenv_qn in *. intros. specialize (H x a H0). Qcrush.
Qed.

(* qenv.v ends *)

Lemma N_lift_trans_one : forall {p : Type} `{qenv p} (E : env p) q (f : qual -> nats) (F : Qual -> Nats),
  @qnmap f F ->
  N_lift (f (q_trans_one E q)) = N_trans_one E (Q_lift q) F.
Proof.
  intros p H E q f F HfF. pose proof qenv_qn_prop as Hqenv. rewrite Q_lift_qn. generalize dependent q. induction E; intros.
- unfold N_trans_one. Qcrush. Ex. discriminate.
- apply FunctionalExtensionality.functional_extensionality. intros. apply PropExtensionality.propositional_extensionality. split.
  + intros. simpl in *.
    ndestruct (qenv_qn q (‖ E ‖)).
    ++ (* including a *)
      rewrite <- Q_lift_qn in H0. rewrite qn_or_dist in H0. nlift. repeat rewrite Q_lift_qn in H0. rewrite IHE in H0. destruct H0.
      -- (* in the rest of the environment E *)
         unfold N_trans_one in *. intuition. right. Ex. exists x0. intuition. exists x1. intuition. apply indexr_extend1. auto.
      -- (* in a *)
         unfold N_trans_one in *. intuition. right. Ex. exists (‖ E ‖). intuition. rewrite <- Q_lift_qn. auto. exists a. intuition. eapply indexr_head; eauto.
    ++ (* not including a *)
      rewrite <- Q_lift_qn in H0. rewrite Q_lift_qn in H0. rewrite IHE in H0. unfold N_trans_one in *. intuition. right. Ex. exists x0. intuition. exists x1. intuition. apply indexr_extend1. auto.
  + intros. simpl in *.
    ndestruct (qenv_qn q (‖ E ‖)).
    ++ (* including a *)
      rewrite <- Q_lift_qn. rewrite qn_or_dist. nlift. repeat rewrite Q_lift_qn. rewrite IHE. unfold N_trans_one. unfold N_trans_one in H0. destruct H0.
      (* q reaches x directly *)
      left. left. auto.
      (* q reaches x transitively *)
      Ex. bdestruct (x0 =? ‖ E ‖).
      -- (* q -> ‖ E ‖ -> x *)
         right. subst. rewrite indexr_head in H3. inversion H3. subst. auto.
      -- (* q -> x1 -> x *)
         left. right. exists x0. intuition. exists x1. intuition. erewrite <- indexr_skip; eauto.
    ++ (* not including a *)
      rewrite IHE. unfold N_trans_one in *. intuition. right. Ex. bdestruct (x0 =? ‖ E ‖).
      -- (* q reaches E, impossible *)
         subst. rewrite <- Q_lift_qn in H2. contradiction.
      -- (* q -> x1 -> x *)
         exists x0. intuition. exists x1. intuition. erewrite <- indexr_skip; eauto.
Qed.

Lemma q_trans_one_qenv_qn_id: forall {p : Type} `{qenv p} (E : env p) (q : qual),
  closed_qenv_qn 0 E ->
  qenv_qn (q_trans_one E q) = (qenv_qn q).
intros. induction E; simpl; auto. ndestruct (qenv_qn q (‖ E ‖)).
- specialize (H0 (‖ E ‖) a) as H'. rewrite indexr_head in H'. intuition. erewrite qn_or_dist. rewrite IHE. apply N_lift_eq. nlift. repeat erewrite @Q_lift_qn with (Qn:=qenv_Qn). intros. Qcrush. exfalso. eauto. 1,2: apply qenv_qn_prop. eapply closed_qenv_qn_shrink; eauto.
- apply IHE. eapply closed_qenv_qn_shrink; eauto.
  Unshelve. apply qenv_Qn. apply qenv_qn_prop.
Qed.

Lemma q_trans''_qenv_qn_id: forall {p : Type} `{qenv p} (E : env p) (q : qual) (fuel : nat),
  closed_qenv_qn 0 E ->
  qenv_qn (q_trans'' E q fuel) = (qenv_qn q).
intros. generalize dependent q. induction fuel; intros; simpl; auto. rewrite IHfuel. apply q_trans_one_qenv_qn_id; auto.
Qed.

Lemma unsplice_splice_qual_id : forall {q k}, ~(varF k) ∈ᵥ q -> splice_qual k (unsplice_qual k q) = q.
intros.
apply Q_lift_eq. Qcrush.
- bdestruct (x <? k); intuition. assert (x > k); intuition. destruct x. lia. eauto.
- subst. eauto.
- destruct x. lia. eauto.
Qed.

Lemma unsplice_splice_Qual_id : forall {q k}, ~(qfvs q) k -> splice_Qual k (unsplice_Qual k q) = q.
intros. qual_destruct q. Qcrush.
- bdestruct (x <? k); intuition. assert (x > k); intuition. destruct x. lia. eauto.
- subst. eauto.
- destruct x. lia. eauto.
Qed.

Lemma unsplice_splice_ty_id : forall {T k}, ~Tfvs T k -> splice_ty k (unsplice_ty k T) = T.
intros. induction T; simpl in *; eauto.
- destruct v; auto. destruct (lt_dec k i); simpl. destruct (le_lt_dec k (pred i)); destruct i; eauto; lia. destruct (le_lt_dec k i); destruct i; eauto; lia.
- rewrite IHT1, IHT2. repeat rewrite unsplice_splice_qual_id. all: intuition.
- rewrite IHT1, IHT2. repeat rewrite unsplice_splice_qual_id. all: intuition.
- rewrite IHT, unsplice_splice_qual_id; intuition.
Qed.

Lemma splice_unsplice_qual_id : forall {q k}, unsplice_qual k (splice_qual k q) = q.
intros.
apply Q_lift_eq. Qcrush. bdestruct (x <? k); intuition.
Qed.

Lemma splice_unsplice_Qual_id : forall {q k}, unsplice_Qual k (splice_Qual k q) = q.
intros. qual_destruct q. unfold unsplice_Qual. Qcrush. bdestruct (x <? k); intuition.
Qed.

Lemma splice_unsplice_ty_id : forall {T k}, unsplice_ty k (splice_ty k T) = T.
intros. induction T; simpl; repeat rewrite splice_unsplice_qual_id ; repeat rewrite IHT; repeat rewrite IHT1; repeat rewrite IHT2; auto. destruct v; auto. destruct (le_lt_dec k i); simpl; auto. destruct (lt_dec k (S i)); auto. lia. destruct (lt_dec k i); auto. lia.
Qed.

Lemma splice_unsplice_tenv_elmt_id : forall n a, unsplice_tenv_elmt n (splice_tenv_elmt n a) = a.
intros. destruct a as [ [ [ bd b ] T] q]. simpl. rewrite splice_unsplice_qual_id, splice_unsplice_ty_id. auto.
Qed.

Lemma splice_unsplice_senv_elmt_id : forall n a, unsplice_senv_elmt n (splice_senv_elmt n a) = a.
intros. destruct a as [T q]. simpl. rewrite splice_unsplice_qual_id, splice_unsplice_ty_id. auto.
Qed.

#[export] Instance tenv_splicible : @splicible_env (binding * bool * ty * qual) tenv_qenv := {
  env_splice := splice_tenv_elmt;
  env_unsplice := unsplice_tenv_elmt;
  env_elmt_fvs := fun a n => tfvs (snd (fst a)) n || qfvs (snd a) n;
  env_splice_unsplice_id := splice_unsplice_tenv_elmt_id;
  (* env_unsplice_splice_id := unsplice_splice_tenv_elmt_id; *)
}.
#[global] Hint Resolve tenv_splicible : core.

#[export] Instance senv_splicible : @splicible_env (ty * qual) senv_qenv := {
  env_splice := splice_senv_elmt;
  env_unsplice := unsplice_senv_elmt;
  env_elmt_fvs := fun a n => tfvs (fst a) n || qfvs (snd a) n;
  env_splice_unsplice_id := splice_unsplice_senv_elmt_id;
  (* env_unsplice_splice_id := unsplice_splice_senv_elmt_id; *)
}.
#[global] Hint Resolve senv_splicible : core.

#[global] Hint Rewrite (@N_lift_dom (binding * bool * ty * qual)) : nlift_rewrite.
#[global] Hint Rewrite (@N_lift_dom (ty * qual)) : nlift_rewrite.

Definition splice_env {p : Type} `{splicible_env p} (n : nat) (E : env p) : env p := map (env_splice n) E.
Definition splice_tenv (n : nat) (Γ : tenv) : tenv := splice_env n Γ.
Definition splice_senv (n : nat) (Σ : senv) : senv := splice_env n Σ.

Module SplicingNotations.
  Declare Scope splicing.
  Notation "t ↑ᵗ n" := (splice n t) (at level 10) : splicing.
  Notation "T ↑ᵀ n" := (splice_ty n T) (at level 10) : splicing.
  Notation "q ↑ᵈ n" := (splice_qual n q) (at level 10) : splicing.
  Notation "g ↑ᴳ n" := (splice_env n g) (at level 10) : splicing.
End SplicingNotations.
Import SplicingNotations.
Local Open Scope splicing.

(********************
*  N_lift_trans''  *
********************)

Lemma q_trans_one_extend_closed_id : forall {p : Type} `{qenv p} (E E' : env p) q,
  E' ⊇ E ->
  closed_Nats (‖ E ‖) (qenv_Qn q ↑) ->
  (q_trans_one E' q) = (q_trans_one E q).
intros. unfold extends in H0. destruct H0. subst. induction x; simpl; auto. rewrite app_length. ndestruct (qenv_qn q (‖ x ‖ + ‖ E ‖)). exfalso. unfold closed_Nats in *. specialize (H1 (‖ x ‖ + ‖ E ‖)). erewrite Q_lift_qn in H0; eauto. apply H1 in H0. lia. eauto. Unshelve. apply qenv_qn_prop.
Qed.

Lemma q_trans_one_extend_closed_id' : forall {p : Type} `{qenv p} (a : p) (E : env p) q,
  closed_Nats (‖ E ‖) (qenv_Qn q ↑) ->
  (q_trans_one (a::E) q) = (q_trans_one E q).
intros. simpl. ndestruct (qenv_qn q (‖ E ‖)). exfalso. unfold closed_Nats in *. specialize (H0 (‖ E ‖)). erewrite Q_lift_qn in H1; eauto. apply H0 in H1. lia. eauto. Unshelve. apply qenv_qn_prop.
Qed.

Lemma q_trans_one_subq' : forall {p : Type} `{qenv p} (E : env p) (q : qual),
  q ⊑↑ q_trans_one E q.
intros. induction E; auto. simpl. ndestruct (qenv_qn q (‖ E ‖)); Qcrush.
Qed.

Lemma q_trans''_incr_subq : forall {p : Type} `{qenv p} (E : env p) q (fuel : nat),
  q_trans'' E q fuel ⊑↑ q_trans'' E q (S fuel).
intros. generalize dependent q. induction fuel; intros; simpl in *.
- induction E; simpl in *; auto. ndestruct (qenv_qn q (‖ E ‖)); Qcrush.
- apply IHfuel.
Qed.

Lemma q_trans''_incr_subq' : forall {p : Type} `{qenv p} (E : env p) q (F : Qual -> Nats) (fuel x: nat),
  Qn_sub' F ->
  F (q_trans'' E q fuel) ↑ x ->
  F (q_trans'' E q (S fuel)) ↑ x.
intros. unfold Qn_sub', N_sub in H0. eapply H0 with (q1:=(q_trans'' E q fuel)↑); eauto. eapply q_trans''_incr_subq; eauto.
Qed.

Lemma q_trans''_incr_subq'' : forall {p : Type} `{qenv p} (E : env p) q (F : Qual -> Nats) (x: nat),
  Qn_sub' F ->
  F q ↑ x ->
  F (q_trans_one E q) ↑ x.
intros. unfold Qn_sub', N_sub in H0. eapply H0 with (q1:=q↑); eauto. apply q_trans_one_subq'.
Qed.

Lemma q_trans''_incr_subq''' : forall {p : Type} `{qenv p} (E : env p) q (F : Qual -> Nats) (fuel x: nat),
  Qn_sub' F ->
  F q ↑ x ->
  F (q_trans'' E q fuel) ↑ x.
intros. unfold Qn_sub', N_sub in H0. induction fuel; simpl; auto. eapply q_trans''_incr_subq'; eauto.
Qed.


Lemma N_lift_trans'': forall {p : Type} `{qenv p} (E : env p) q (f : qual -> nats) (F : Qual -> Nats) (fuel : nat),
  @qnmap f F ->
  N_lift (f (q_trans'' E q fuel)) = N_trans'' E (Q_lift q) F fuel.
Proof.
  intros p H E q f F fuel HfF. rewrite Q_lift_qn. generalize dependent q. pose proof qenv_qn_prop as Hqn. induction fuel; intros.
- simpl. unfold N_trans''. Qcrush. Ex.
- apply FunctionalExtensionality.functional_extensionality. intros. apply PropExtensionality.propositional_extensionality. split; intros.
  + (* N_trans'' (q_trans_one q) fuel -> N_trans'' q (S fuel) *)
    simpl in *. rewrite IHfuel in H0. unfold N_trans''. unfold N_trans'' in H0. destruct H0.
      -- (* q_trans_one q x *)
         rewrite <- Q_lift_qn in H0. erewrite N_lift_trans_one in H0; eauto. unfold N_trans_one in H0. destruct H0. intuition. right. Ex. exists fuel. intuition. exists x0. intuition. exists x1. intuition. rewrite IHfuel. unfold N_trans''. intuition.
      -- (* q_trans_one q -[fuel']-> x, need to show q -[S fuel']-> x *)
         destruct H0 as [fuel' H0]. right. exists fuel. intuition. rewrite <- Q_lift_qn in H2. erewrite N_lift_trans_one in H2; eauto. subst. Ex. unfold N_trans_one in H1. destruct H1.
exists x0. intuition. exists x1. intuition. eapply q_trans''_incr_subq'; eauto. eapply Qn_sub; eauto.
Ex. exists x2. intuition. exists x3. intuition. rewrite IHfuel. unfold N_trans''. right. exists fuel'. intuition. exists x0. intuition. exists x1. intuition.
  + (* N_trans'' (q_trans_one q) fuel -> N_trans'' q (S fuel) *)
    simpl. rewrite IHfuel. unfold N_trans''. unfold N_trans'' in H0. destruct H0.
      -- (* directly reachable *)
         left. intuition. simpl in *. eapply q_trans''_incr_subq''; eauto. eapply Qn_sub; eauto.
      -- (* reachable in S fuel steps *)
         Ex. inversion H1. subst. rename x0 into fuel. destruct fuel as [|fuel'].
         (* fuel = 0. reachable via one step *)
         * left. inversion H1. subst. simpl in *.
rewrite <- Q_lift_qn. erewrite N_lift_trans_one; eauto. unfold N_trans_one. right. exists x1. intuition. exists x2. intuition.
         (* fuel > 0. reachable via multiple steps *)
         * right. exists fuel'. intuition. rewrite IHfuel in H4. unfold N_trans'' in H4. destruct H4.
           ++ (* q -> x1 -> x2 -> x *)
              exists x1. intuition. eapply q_trans''_incr_subq''; eauto. apply qenv_qn_prop. exists x2. intuition. eapply q_trans''_incr_subq'''; eauto. apply Qn_sub.
           ++ (* q -> x1 -> x2 -> x3 -> x4 -> x *)
              Ex. exists x3. intuition. rewrite <- Q_lift_qn. erewrite N_lift_trans_one; eauto. unfold N_trans_one. right. exists x1. intuition. exists x2. intuition. exists x4. intuition. inversion H4. subst. auto.
Qed.

(******************
*  Q_lift_trans  *
******************)

Lemma Q_lift_trans_one : forall {p : Type} `{qenv p} (E : env p) q,
  Q_lift (q_trans_one E q) = Q_trans_one E (Q_lift q).
  intros p Hp E q. unfold Q_lift. replace (♦∈ q_trans_one E q) with (N_lift (qfr (q_trans_one E q)) 0).
repeat erewrite N_lift_trans_one; eauto. unfold N_trans_one, Q_trans_one. Qcrush.
unfold qfr,qfresh,N_lift,Is_true. destruct (fst (fst (fst (q_trans_one E q)))); Qcrush.
Qed.

Lemma Q_lift_trans'' : forall {p : Type} `{qenv p} (E : env p) q fuel,
  Q_lift (q_trans'' E q fuel) = Q_trans'' E (Q_lift q) fuel.
Proof.
  intros p Hp E q fuel. generalize dependent q. induction fuel. intros. unfold Q_trans'', N_trans''. Qcrush; Ex. intros. simpl. rewrite IHfuel. generalize dependent q. induction E; intros; simpl.
  - unfold Q_trans'', N_trans''. Qcrush; Ex; discriminate.
  - ndestruct (qenv_qn q (‖ E ‖)).
    + (* (‖ E ‖) in q *)
      unfold Q_trans'', Qor.
      f_equal. f_equal. f_equal.
      all: try apply FunctionalExtensionality.functional_extensionality;
      intros; try apply PropExtensionality.propositional_extensionality.
      -- repeat erewrite <- N_lift_trans'' with (f:=qfr); eauto. simpl. unfold N_lift in H. rewrite H. rewrite N_lift_trans'' with (F:=Qfr); eauto. erewrite Q_lift_or; eauto. intuition.
      -- repeat erewrite <- N_lift_trans'' with (f:=qfvs); eauto. simpl. unfold N_lift in H. rewrite H. rewrite N_lift_trans'' with (F:=qfvs); eauto. erewrite Q_lift_or; eauto. intuition.
      -- repeat erewrite <- N_lift_trans'' with (f:=qbvs); eauto. simpl. unfold N_lift in H. rewrite H. rewrite N_lift_trans'' with (F:=qbvs); eauto. erewrite Q_lift_or; eauto. intuition.
      -- repeat erewrite <- N_lift_trans'' with (f:=qlocs); eauto. simpl. unfold N_lift in H. rewrite H. rewrite N_lift_trans'' with (F:=qlocs); eauto. erewrite Q_lift_or; eauto. intuition.
    + unfold Q_trans'', Qor.
      f_equal. f_equal. f_equal.
      all: try apply FunctionalExtensionality.functional_extensionality;
      intros; try apply PropExtensionality.propositional_extensionality.
      -- repeat erewrite <- N_lift_trans'' with (f:=qfr); eauto. simpl. clift. intuition.
      -- repeat erewrite <- N_lift_trans'' with (f:=qfvs); eauto. simpl. clift. intuition.
      -- repeat erewrite <- N_lift_trans'' with (f:=qbvs); eauto. simpl. clift. intuition.
      -- repeat erewrite <- N_lift_trans'' with (f:=qlocs); eauto. simpl. clift. intuition.
Qed.

Lemma Q_lift_trans : forall (Γ : tenv) (Σ : senv) (q : qual),
  Q_lift (q_trans Γ Σ q) = Q_trans Γ Σ (Q_lift q).
intros. unfold q_trans, Q_trans, q_trans_senv, q_trans_tenv. repeat rewrite Q_lift_trans''; auto.
Qed.

(**************
*  trans or  *
**************)

Lemma q_trans''_one_commute : forall {p : Type} `{qenv p} (E : env p) {q : qual} {fuel : nat},
  q_trans_one E (q_trans'' E q fuel) = q_trans'' E (q_trans_one E q) fuel.
intros. generalize dependent q. induction fuel; intros; simpl; auto.
Qed.

Lemma q_trans_one_or_dist : forall {p : Type} `{qenv p} (E : env p) q1 q2,
  (q_trans_one E q1 ⊔ q_trans_one E q2) = q_trans_one E (q1 ⊔ q2).
intros. induction E; simpl; auto. ndestruct (qenv_qn q1 (‖ E ‖)); ndestruct (qenv_qn q2 (‖ E ‖)); erewrite qn_or_dist; eauto using qenv_qn_prop; clift; rewrite <- IHE; apply Q_lift_eq; Qcrush. Unshelve. all: eauto using qenv_qn_prop.
Qed.

Lemma q_trans''_or_dist : forall {p : Type} `{qenv p} (E : env p) q1 q2 fuel,
  (q_trans'' E q1 fuel ⊔ q_trans'' E q2 fuel) = q_trans'' E (q1 ⊔ q2) fuel.
intros. generalize dependent q1. generalize dependent q2. induction fuel; intros; simpl; auto. rewrite IHfuel. rewrite q_trans_one_or_dist. auto.
Qed.

Lemma q_trans_or_dist : forall Γ Σ q1 q2,
  (q_trans Γ Σ q1 ⊔ q_trans Γ Σ q2) = q_trans Γ Σ (q1 ⊔ q2).
intros. unfold q_trans,q_trans_tenv,q_trans_senv. repeat rewrite q_trans''_or_dist. auto.
Qed.

(*****************
*  trans fresh  *
*****************)

Lemma q_trans_one_tenv_freshv_id : forall (Γ : tenv), q_trans_one Γ ({♦}) = {♦}.
intros. induction Γ; simpl; auto.
Qed.

Lemma q_trans''_tenv_freshv_id : forall (Γ : tenv) n fuel, n >= (‖ Γ ‖) -> (q_trans'' Γ {♦} fuel) = {♦}.
intros. induction fuel; simpl; auto. rewrite q_trans_one_tenv_freshv_id; auto.
Qed.

Lemma q_trans_one_senv_freshv_id : forall (Σ : senv), q_trans_one Σ ({♦}) = {♦}.
intros. induction Σ; simpl; auto.
Qed.

Lemma q_trans''_senv_freshv_id : forall (Σ : senv) n fuel, n >= (‖ Σ ‖) -> (q_trans'' Σ {♦} fuel) = {♦}.
intros. induction fuel; simpl; auto. rewrite q_trans_one_senv_freshv_id; auto.
Qed.

Lemma q_trans_freshv_id : forall Γ Σ, q_trans Γ Σ {♦} = {♦}.
intros. unfold q_trans,q_trans_tenv,q_trans_senv. erewrite q_trans''_tenv_freshv_id; eauto. erewrite q_trans''_senv_freshv_id; eauto.
Qed.

(***************
*  trans sub  *
***************)

Lemma q_trans''_subq : forall {p : Type} `{qenv p} (E : env p) {q1 q2 : qual} {fuel : nat},
  q1 ⊑↑ q2 ->
  q_trans'' E q1 fuel ⊑↑ q_trans'' E q2 fuel.
intros. repeat rewrite Q_lift_trans''. unfold Q_trans'', N_trans''. pose proof qenv_qn_prop. Qcrush; Ex; right.
  - exists x. intuition. exists x0. intuition. eapply Qn_sub; eauto. Qcrush. exists x1. intuition.
  - exists x0. intuition. exists x1. intuition. eapply Qn_sub; eauto. Qcrush. exists x2. intuition.
  - exists x0. intuition. exists x1. intuition. eapply Qn_sub; eauto. Qcrush. exists x2. intuition.
  - exists x0. intuition. exists x1. intuition. eapply Qn_sub; eauto. Qcrush. exists x2. intuition.
Qed.

Lemma q_trans''_subq' : forall {p : Type} `{qenv p} (E : env p) (q : qual) (fuel : nat),
  q ⊑↑ q_trans'' E q fuel.
intros. repeat rewrite Q_lift_trans''. unfold Q_trans'', N_trans''. pose proof qenv_qn_prop. Qcrush; Ex; right.
Qed.

Lemma q_trans_subq : forall {Γ Σ} {q1 q2 : qual},
  q1 ⊑↑ q2 ->
  q_trans Γ Σ q1 ⊑↑ q_trans Γ Σ q2.
intros. unfold q_trans. repeat eapply q_trans''_subq; eauto.
Qed.

Lemma q_trans_subq_fresh : forall {Γ Σ} {q1 q2 : qual},
  q1 ⊑↑ q2 ⊔ {♦} ->
  q_trans Γ Σ q1 ⊑↑ q_trans Γ Σ q2 ⊔ {♦}.
intros. replace (q_trans Γ Σ q2 ⊔ {♦}) with (q_trans Γ Σ (q2 ⊔ {♦})). unfold q_trans. repeat eapply q_trans''_subq; eauto. rewrite <- q_trans_or_dist. rewrite q_trans_freshv_id; auto.
Qed.

Lemma q_trans_subq' : forall {Γ Σ} {q : qual},
  q ⊑↑ q_trans Γ Σ q.
intros. unfold q_trans,q_trans_senv,q_trans_tenv. pose proof (q_trans''_subq' Σ (q_trans'' Γ q (‖ Γ ‖)) (‖ Σ ‖)). pose proof (q_trans''_subq' Γ q (‖ Γ ‖)). Qcrush.
Qed.
#[global] Hint Resolve q_trans_subq' : core.

Lemma q_trans_one_extend_subq : forall {p : Type} `{qenv p} (E E' : env p) {q1 q2 : qual} {fuel : nat},
  E' ⊇ E ->
  q1 ⊑↑ q2 ->
  q_trans_one E q1 ⊑↑ q_trans_one E' q2.
intros. unfold extends in *. Ex. subst. repeat rewrite Q_lift_trans_one. unfold Q_trans_one, N_trans_one. pose proof qenv_qn_prop. Qcrush; right; Ex.
  - exists x0. intuition. eapply Qn_sub; eauto. Qcrush. exists x1. intuition. apply indexr_extend. auto.
  - exists x1. intuition. eapply Qn_sub; eauto. Qcrush. exists x2. intuition. apply indexr_extend. auto.
  - exists x1. intuition. eapply Qn_sub; eauto. Qcrush. exists x2. intuition. apply indexr_extend. auto.
  - exists x1. intuition. eapply Qn_sub; eauto. Qcrush. exists x2. intuition. apply indexr_extend. auto.
Qed.

Lemma q_trans''_extend_subq : forall {p : Type} `{qenv p} (E E' : env p) {q1 q2 : qual} {fuel : nat},
  E' ⊇ E ->
  q1 ⊑↑ q2 ->
  q_trans'' E q1 fuel ⊑↑ q_trans'' E' q2 fuel.
intros. generalize dependent q1. generalize dependent q2. generalize dependent E. generalize dependent E'. induction fuel; intros. simpl; auto. simpl. unfold extends in *. Ex. subst.
eapply IHfuel; eauto. eapply q_trans_one_extend_subq; eauto. unfold extends. eauto.
Qed.

(***********
*  trans fv  *
***********)

Lemma q_trans_one_senv_fv_id : forall (Σ : senv) n, q_trans_one Σ ($! n) = $! n.
intros. induction Σ; simpl; auto.
Qed.

Lemma q_trans''_senv_fv_id : forall (Σ : senv) n fuel, q_trans'' Σ ($! n) fuel = $! n.
intros. induction fuel; simpl; auto. rewrite q_trans_one_senv_fv_id. rewrite IHfuel. auto.
Qed.

Lemma q_trans_one_tenv_fv_id : forall (Γ : tenv) n, n >= (‖ Γ ‖) -> q_trans_one Γ ($! n) = $! n.
intros. induction Γ; simpl; auto. ndestruct (qfvs $! n (‖ Γ ‖)). Qcrush. apply IHΓ. simpl in *. lia.
Qed.

Lemma q_trans''_tenv_fv_id : forall (Γ : tenv) n fuel, n >= (‖ Γ ‖) -> (q_trans'' Γ $! n fuel) = $! n.
intros. induction fuel; simpl; auto. rewrite q_trans_one_tenv_fv_id; auto.
Qed.

Lemma q_trans_fv_id : forall Γ Σ n, n >= (‖ Γ ‖) -> q_trans Γ Σ $! n = $! n.
intros. unfold q_trans,q_trans_tenv,q_trans_senv. rewrite q_trans''_tenv_fv_id; auto. rewrite q_trans''_senv_fv_id; auto.
Qed.

(********************
*  qenv_saturated  *
********************)

Lemma qenv_saturated_iff : forall {p : Type} `{qenv p} (E : env p) (q : qual),
  qenv_saturated_q E q <-> qenv_saturated_q'' E q.
intros. unfold qenv_saturated_q, qenv_saturated_q''. split; intros.
- induction E. auto. simpl. ndestruct (qenv_qn q (‖ E ‖)). rewrite IHE. specialize (H0 (‖ E ‖) a). rewrite indexr_head in H0. pose proof qenv_qn_prop. erewrite Q_lift_qn in H1; eauto. intuition. apply Q_lift_eq. Qcrush. intros. specialize (H0 x a0). intuition. rewrite indexr_extend1 in H3. intuition eauto. apply IHE. intros. eapply H0; eauto. rewrite indexr_extend1 in H3. intuition eauto.
  - generalize dependent x. generalize dependent a. generalize dependent q. induction E; intros. discriminate. simpl in H0. ndestruct (qenv_qn q (‖ E ‖)). bdestruct (x =? (‖ E ‖)). subst. rewrite indexr_head in H2. inversion H2. subst. rewrite <- H0. Qcrush. eapply IHE; eauto. apply Q_lift_eq. assert ((q_trans_one E q) ⊑↑ q). rewrite <- H0 at 2. Qcrush. pose proof (q_trans_one_subq' E q). Qcrush. erewrite <- indexr_skip; eauto. bdestruct (x =? (‖ E ‖)). subst. exfalso. pose proof qenv_qn_prop. rewrite Q_lift_qn in H3. intuition. eapply IHE; eauto. erewrite <- indexr_skip; eauto.
Qed.

Lemma qenv_saturated_trans''_id : forall {p : Type} `{qenv p} (E : env p) (q : qual),
  qenv_saturated_q'' E q -> forall fuel, q_trans'' E q fuel = q.
intros. induction fuel; simpl; auto. unfold qenv_saturated_q'' in H0. rewrite H0. auto.
Qed.


(****************
*  trans fuel  *
****************)

Lemma cardinality_max : forall {p : Type} `{qenv p} (E : env p) q, cardinality q E <= (‖ E ‖).
intros. induction E; simpl; auto. ndestruct (qenv_qn q (‖ E ‖)); lia.
Qed.

Lemma cardinality_subq_le : forall {p : Type} `{qenv p} (E : env p) q1 q2,
  q1 ⊑↑ q2 ->
  cardinality q1 E <= cardinality q2 E.
Proof.
  intros. induction E; simpl; auto. ndestruct (qenv_qn q1 (‖ E ‖)).
  - assert (N_lift (qenv_qn q2) (‖ E ‖)). { erewrite @Q_lift_qn with (Qn:=qenv_Qn) in H1; eauto using qenv_qn_prop. erewrite @Q_lift_qn with (Qn:=qenv_Qn); eauto using qenv_qn_prop. eapply @Qn_sub with (qn:=qenv_qn); eauto using qenv_qn_prop. } clift. lia.
  - ndestruct (qenv_qn q2 (‖ E ‖)). lia. lia.
Qed.

Lemma cardinality_qor_trans : forall {p : Type} `{qenv p} (E : env p) q1 q2,
  cardinality q1 E = cardinality (q1 ⊔ q2) E ->
  (q_trans_one E q1 ⊔ q_trans_one E q2) = ((q_trans_one E q1) ⊔ q2).
Proof.
  intros. induction E; simpl; auto. ndestruct (qenv_qn q1 (‖ E ‖)).
  - assert (Hor: N_lift (qenv_qn (q1 ⊔ q2)) (‖ E ‖)). { erewrite qn_or_dist. Qcrush. }
    assert (cardinality q1 E = cardinality (q1 ⊔ q2) E). { simpl in H0. unfold N_lift in H1,Hor. rewrite H1,Hor in H0. auto. }
    ndestruct (qenv_qn q2 (‖ E ‖)).
    + (* both q1 and q2 reaches store location *)
      replace ((q_trans_one E q1 ⊔ qenv_q a) ⊔ q_trans_one E q2 ⊔ qenv_q a) with ((q_trans_one E q1 ⊔ q_trans_one E q2) ⊔ qenv_q a). rewrite IHE; auto. apply Q_lift_eq. Qcrush. apply Q_lift_eq. Qcrush.
    + (* only q1 reaches store location *)
      replace ((q_trans_one E q1 ⊔ qenv_q a) ⊔ q_trans_one E q2) with ((q_trans_one E q1 ⊔ q_trans_one E q2) ⊔ qenv_q a). rewrite IHE; auto. apply Q_lift_eq. Qcrush. apply Q_lift_eq. Qcrush.
  - ndestruct (qenv_qn q2 (‖ E ‖)).
    + (* impossible. q1 doesn't reach, but q2 reaches store location *)
      exfalso. simpl in H0. unfold N_lift in H1,H2. assert (Hor: N_lift (qenv_qn (q1 ⊔ q2)) (‖ E ‖)). { erewrite qn_or_dist. Qcrush. } apply not_true_is_false in H1. rewrite H1,Hor in H0. pose proof (cardinality_subq_le E q1 (q1 ⊔ q2)). assert (q1 ⊑↑ q1 ⊔ q2). Qcrush. intuition.
    + (* neither q1 nor q2 reaches store location *)
      simpl in H0. unfold N_lift in H1,H2. assert (Hor: ~N_lift (qenv_qn (q1 ⊔ q2)) (‖ E ‖)). { erewrite qn_or_dist. Qcrush. } apply not_true_is_false in H1,Hor. rewrite H1,Hor in H0. intuition.
Unshelve. all: try apply qenv_Qn; eauto using qenv_qn_prop.
Qed.

Lemma cardinality_eq_sat : forall {p : Type} `{qenv p} (E : env p) q,
  cardinality q E = cardinality (q_trans_one E q) E ->
  qenv_saturated_q'' E (q_trans_one E q). (* (q_trans_one E (q_trans_one E q)) = (q_trans_one E q). *)
unfold qenv_saturated_q''. intros. generalize dependent q. induction E; intros; simpl in *; auto. ndestruct (qenv_qn q (‖ E ‖)).
    + assert (N_lift (qenv_qn (q_trans_one E q ⊔ qenv_q a)) (‖ E ‖)). { erewrite qn_or_dist. Qcrush. left. erewrite @N_lift_trans_one with (F:=qenv_Qn); eauto. unfold N_trans_one. left. erewrite <- Q_lift_qn; eauto. apply qenv_qn_prop. }
      unfold N_lift in H2. rewrite H2 in *. inversion H0.
assert (cardinality q E <= cardinality (q_trans_one E q) E). { apply cardinality_subq_le. rewrite Q_lift_trans_one. unfold Q_trans_one, N_trans_one. Qcrush. }
assert (cardinality (q_trans_one E q) E <= cardinality q E). { rewrite H4. apply cardinality_subq_le. Qcrush. }
assert (cardinality q E = cardinality (q_trans_one E q) E). { lia. } intuition.
rewrite H6 in H4. apply cardinality_qor_trans in H4. rewrite IHE in H4; auto. rewrite <- q_trans_one_or_dist. rewrite IHE; auto. rewrite H4. apply Q_lift_eq. Qcrush.
    + ndestruct (qenv_qn (q_trans_one E q) (‖ E ‖)).
      -- (* impossible due to cardinality: q doesn't have (‖ E ‖), but trans q does *)
         exfalso. pose proof (cardinality_subq_le E q (q_trans_one E q) (q_trans_one_subq' _ _)). lia.
      -- (* neither q nor trans q have (‖ E ‖) *)
         apply IHE; auto.
Unshelve. apply qenv_Qn. all: eauto using qenv_qn_prop.
Qed.

Lemma cardinality_zero : forall {p : Type} `{qenv p} (E : env p) q,
  cardinality q E = 0 ->
  qenv_saturated_q'' E q. (* q_trans_one E q = q. *)
unfold qenv_saturated_q''. intros. induction E; auto. simpl in *. ndestruct (qenv_qn q (‖ E ‖)); eauto. lia.
Qed.

Lemma cardinality_inc_or_sat : forall {p : Type} `{qenv p} (E : env p) q q',
  q' = q_trans_one E q ->
  S (cardinality q E) <= cardinality q' E \/ qenv_saturated_q'' E q'.
unfold qenv_saturated_q''. intros. bdestruct (cardinality q E =? cardinality q' E).
  - (* cardinality is equal, no growth, must be saturated. *)
    subst. right. apply cardinality_eq_sat; auto.
  - (* cardinality not equal *)
    subst. left. pose proof (cardinality_subq_le E q (q_trans_one E q) (q_trans_one_subq' _ _)). intuition.
Qed.

Lemma cardinality_inc_or_sat' : forall {p : Type} `{qenv p} (E : env p) q q' fuel,
  q' = q_trans'' E q fuel ->
  cardinality q E + fuel <= cardinality q' E \/
  qenv_saturated_q'' E q'.
intros. generalize dependent q'. generalize dependent q. induction fuel; intros. left. simpl in *. subst. lia.
specialize (IHfuel (q_trans_one E q) (q_trans'' E (q_trans_one E q) fuel)).
pose proof (cardinality_inc_or_sat E q (q_trans_one E q)). destruct H1; auto.
  - (* cardinality increasing, q_trans_one not saturated *)
    intuition.
    + (* cardinality increasing, q_trans'' not saturated *)
      subst. left. simpl. lia.
    + (* q_trans'' saturated, the entire thing must be saturated *)
      subst. right. simpl. auto.
  - (* q_trans_one saturated *)
    subst. right. simpl. pose proof (qenv_saturated_trans''_id _ _ H1). rewrite H0. auto.
Qed.

Lemma cardinality_max_sat : forall {p : Type} `{qenv p} (E : env p) q,
  cardinality q E = (‖ E ‖) ->
  q_trans_one E (q_trans_one E q) = q_trans_one E q.
intros. pose proof (cardinality_inc_or_sat E q (q_trans_one E q)). intuition. pose proof (cardinality_max E (q_trans_one E q)). lia.
Qed.

Lemma q_trans''_fuel_max_gen : forall {p : Type} `{qenv p} (E : env p) (q : qual) (fuel : nat),
  ‖ E ‖ < S fuel ->
  q_trans'' E (q_trans_one E q) fuel = q_trans'' E q fuel.
intros. rewrite <- q_trans''_one_commute.
pose proof (cardinality_inc_or_sat' E q (q_trans'' E q fuel) fuel).
pose proof (cardinality_inc_or_sat E (q_trans'' E q fuel) (q_trans_one E (q_trans'' E q fuel))). intuition.
  - (* cardinality increasing, impossible *)
    pose proof (cardinality_max E (q_trans_one E (q_trans'' E q fuel))). lia.
  - bdestruct (cardinality q E =? 0).
    + (* cardinality is zero, already saturated *)
      apply cardinality_zero in H3. unfold qenv_saturated_q'' in H2, H3. rewrite q_trans''_one_commute. rewrite H3. auto.
    + (* cardinalty not zero, impossible because exceeds max bound *)
      pose proof (cardinality_max E (q_trans'' E q fuel)). lia.
Qed.

Lemma q_trans''_fuel_max : forall {p : Type} `{qenv p} (E : env p) (q : qual) (fuel : nat),
  fuel >= (‖ E ‖) ->
  q_trans'' E q fuel = q_trans'' E q (‖ E ‖).
intros. generalize dependent E. generalize dependent q. induction fuel; intros.
  - assert (Hl: (‖ E ‖) = 0). lia. rewrite Hl. auto.
  - simpl. bdestruct ((‖ E ‖) =? S fuel).
    + rewrite H1. simpl. eauto.
    + rewrite <- IHfuel; try lia.
      apply q_trans''_fuel_max_gen. lia.
Qed.

Lemma tenv_subst_qenv_q_dist : forall (a : (binding * bool * ty * qual)) v T' q', subst_qual (snd a) v q' = snd (subst_tenv_elmt v T' q' a).
intros. destruct a as [ [ [ ? ? ] ? ] ? ]. simpl. auto.
Qed.

Lemma senv_subst_qenv_q_dist : forall (a : (ty * qual)) v T' q', subst_qual (snd a) v q' = snd (subst_senv_elmt v T' q' a).
intros. destruct a as [ ? ? ]. simpl. auto.
Qed.

#[export] Instance tenv_substitutable : @substitutable_env (binding * bool * ty * qual) tenv_qenv := {
  env_subst := subst_tenv_elmt;
  env_subst_qenv_q_dist := tenv_subst_qenv_q_dist;
}.
#[global] Hint Resolve tenv_substitutable : core.

#[export] Instance senv_substitutable : @substitutable_env (ty * qual) senv_qenv := {
  env_subst := subst_senv_elmt;
  env_subst_qenv_q_dist := senv_subst_qenv_q_dist;
}.
#[global] Hint Resolve senv_substitutable : core.

Definition subst_env {p : Type} `{substitutable_env p} (E : env p) (n : nat) (T' : ty) (q' : qual) : env p := map (env_subst n T' q') E.

Definition subst_tenv (Γ : tenv) (v : nat) (U: ty)(q1 : qual) : tenv := subst_env Γ v U q1.
Definition subst_senv (Σ : senv) (v : nat) (U: ty)(q1 : qual) : senv := subst_env Σ v U q1.

Module SubstitutionNotations.
  Declare Scope substitutions.
  Notation "{ v1 |-> t1 ; t2 }ᵗ t"  := (subst_tm (subst_tm t v1 t1) v1 t2) (at level 10) : substitutions.
  Notation "{ v1 |-> t1 }ᵗ t"       := (subst_tm t v1 t1) (at level 10) : substitutions.
  Notation "{ v1 |-> q1 ; q2 }ᵈ q"  := (subst_qual (subst_qual q v1 q1) v1 q2) (at level 10) : substitutions.
  Notation "{ v1 |-> q1 }ᵈ q"       := (subst_qual q v1 q1) (at level 10) : substitutions.
  Notation "{ v1 |-> U1 ~ q1 ; U2 ~ q2  }ᵀ T" := (subst_ty (subst_ty T v1 U1 q1) v1 U2 q2) (at level 10) : substitutions.
  Notation "{ v1 |-> U1 ~ q1 }ᵀ T" := (subst_ty T v1 U1 q1) (at level 10) : substitutions.
  Notation "{ v1 |-> T1 ~ q1 }ᴳ G" := (subst_env G v1 T1 q1) (at level 10) : substitutions.
  Notation "{ v1 |-> T1 ~ q1 ; T2 ~ q2 }ᴳ G" := (subst_env (subst_env G v1 T1 q1) v1 T2 q2) (at level 10) : substitutions.
End SubstitutionNotations.
Import SubstitutionNotations.
Local Open Scope substitutions.

(* Indicates the relation between an assumption's qualifier and the qualifier we substitute for the variable.
   This helps ensure that the substitution lemma can be expressed uniformly on a single variable. *)
Inductive Substq : tenv -> senv -> qual -> qual -> Prop :=
| SExact : forall Γ Σ df,    ♦∉ df -> Substq Γ Σ df df        (* precise substitution, e.g., we substitute a recursive function into itself or the argument in t_app *)
| SGrow  : forall Γ Σ df dx,
    ♦∉ dx ->
    closed_Qual 0 (‖ Γ ‖) (‖ Σ ‖) df ↑ ->
    Substq Γ Σ (q_trans Γ Σ df ⋒ q_trans Γ Σ dx) dx (* a growing substitution, e.g., we substitute the argument in t_app_fresh, note the difference. *)
.
#[global] Hint Constructors Substq : core.

(** Metatheory *)

Lemma Substq_non_fresh : forall {Γ Σ dx dx'}, Substq Γ Σ dx dx' -> ♦∉ dx'.
  intros. inversion H; auto.
Qed.
#[global] Hint Resolve Substq_non_fresh : core.

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

Lemma splice_env_app : forall {p : Type} `{splicible_env p} (E1 E2 : env p) n,
  (E1 ↑ᴳ n ++ E2 ↑ᴳ n) = (E1 ++ E2) ↑ᴳ n.
intros. induction E1; simpl; auto. rewrite IHE1. auto.
Qed.

Lemma splice_env_length : forall {p : Type} `{splicible_env p} (E : env p) {n E}, ‖ E ↑ᴳ n ‖ = ‖E‖.
  intros. unfold splice_env. rewrite map_length. auto.
Qed.

Lemma splice_ty_not_in : forall T k, ~Tfvs (T ↑ᵀ k) k.
intros. induction T; simpl; auto.
  - destruct v; destruct (le_lt_dec k i); simpl; lia.
  - Qcrush.
  - Qcrush.
  - Qcrush.
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
  erewrite IHclosed_ty; eauto. erewrite closed_qual_open_id; eauto.
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
  1-5 : eapply closed_qual_open'; eauto.
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
all: eauto using closed_Qual_open_succ.
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
  eapply IHT; eauto.
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
  eapply closed_ty_monotone; eauto.
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
  1-2: eapply IHT2; eauto.
  eapply closed_ty_monotone; eauto.
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
  erewrite IHT; eauto. erewrite splice_qual_open_succ; eauto.
Qed.

Lemma splice_qual_open'' : forall {k df d1 d2}, (d2 <~ᵈ df; d1) ↑ᵈ k = (d2 ↑ᵈ k) <~ᵈ (df ↑ᵈ k); (d1 ↑ᵈ k).
  intros. qual_destruct d2; qual_destruct d1; qual_destruct df; simpl.
unfold openq. unfold_q.
apply Q_lift_eq.
ndestruct (bvs 0); simpl.
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
  rewrite app_length in *. erewrite splice_env_length; eauto.
  destruct (Nat.eqb i (‖ Γ1 ‖ + ‖ Γ2 ‖)) eqn:Heq. inversion H. subst.
  simpl.  intuition.   apply IHΓ1; eauto.
Qed.

Lemma indexr_splice_ty_tenv : forall {Γ1 i Γ2 b U du},  indexr i (Γ1 ++ Γ2) = Some ((bind_ty, b, U, du)) ->
forall {k}, k <= i -> (length Γ2) <= i -> indexr i (splice_tenv k Γ1 ++ Γ2) = Some ((bind_ty, b, splice_ty k U, splice_qual k du)).
Proof.  induction Γ1; intros; simpl in *; intuition. apply indexr_var_some' in H. lia.
  rewrite app_length in *. unfold splice_tenv. erewrite splice_env_length; eauto.
  destruct (Nat.eqb i (‖ Γ1 ‖ + ‖ Γ2 ‖)) eqn:Heq.  inversion H. subst.
  simpl. auto. apply IHΓ1; eauto.
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

Lemma weaken_qstp_gen : forall {Γ1 Γ2 Σ d1 d2},
    qstp (Γ1 ++ Γ2) Σ d1 d2 ->
    forall T', qstp ((Γ1 ↑ᴳ ‖Γ2‖) ++ T' :: Γ2) Σ (d1 ↑ᵈ ‖Γ2‖) (d2 ↑ᵈ ‖Γ2‖).
Proof.
  intros Γ1 Γ2 Σ d1 d2 HSTP. remember (Γ1 ++ Γ2) as Γ. generalize dependent Γ1. induction HSTP; intros Γ1 HeqG T'; subst.
  - constructor. apply subqual_splice_lr'. auto. apply splice_qual_closed'.
    rewrite app_length in *. unfold splice_tenv. erewrite splice_env_length; eauto.
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
    eapply IHHSTP. auto. apply splice_qual_closed'. rewrite app_length in *. unfold splice_tenv. erewrite splice_env_length; eauto.
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

Lemma weaken_stp_gen : forall {Γ1 Γ2 Σ T1 d1 T2 d2},  stp (Γ1 ++ Γ2) Σ T1 d1 T2 d2 ->
    forall T', stp ((Γ1 ↑ᴳ ‖Γ2‖) ++ T' :: Γ2) Σ (T1 ↑ᵀ ‖Γ2‖) (d1 ↑ᵈ ‖Γ2‖) (T2 ↑ᵀ ‖Γ2‖) (d2 ↑ᵈ ‖Γ2‖).
Proof. intros Γ1 Γ2 Σ T1 d1 T2 d2  Hstp T'. remember (Γ1 ++ Γ2)  as Γ. generalize dependent Γ1.  induction Hstp. intros Γ1.
  - (* TTop *) intros. subst. constructor.  rewrite app_length in *. rewrite splice_env_length in *; auto. simpl.
    replace (‖ Γ1 ‖ + S (‖ Γ2 ‖)) with (S ((‖ Γ1 ‖) +  (‖ Γ2 ‖))). eapply splice_ty_closed; eauto. lia.
    eapply weaken_qstp_gen. auto.
  - (* TVarF x *)  intros; subst. (* specialize (IHHstp Γ1).  intuition. *)  apply stp_refl.
    apply indexr_var_some' in H.  rewrite app_length. unfold splice_tenv. erewrite splice_env_length; eauto.
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

    1-8: rewrite app_length; erewrite splice_env_length; eauto; lia.

    eapply weaken_qstp_gen; eauto.
    erewrite app_length in *; eauto.
    repeat rewrite <- splice_ty_open'. repeat rewrite <- splice_qual_open'. simpl in H3.
    repeat rewrite idfun_inv in H3.
    repeat rewrite @open_ty'_len with (Γ:=(Γ1 ↑ᴳ ‖Γ2‖) ++ Γ2) (Γ':=Γ1++Γ2).
    repeat rewrite @openq'_len with (Γ:=(Γ1 ↑ᴳ ‖Γ2‖) ++ Γ2) (Γ':=Γ1++Γ2).
    replace ({♦} ↑ᵈ (‖ Γ2 ‖)) with ({♦}) in H3; auto.
    all: repeat rewrite app_length; rewrite splice_env_length; auto.
  - constructor. eapply weaken_qstp_gen. subst. auto.
  - intros. assert (stp Γ Σ (TRef q1 T1) d1 (TRef q2 T2) d2). { constructor; intuition. } subst.
    apply stp_closed in H4 as Hcl. intuition.
    inversion H5. inversion H6. subst. simpl.
    specialize (IHHstp1 Γ1). intuition.
    specialize (IHHstp2 Γ1). intuition.
    constructor. apply weaken_qstp_gen. subst; auto.
    1,2 : rewrite splice_qual_empty in H8, H10; auto.
    1,2: apply splice_qual_closed'; rewrite app_length in *; rewrite splice_env_length; auto.
    1, 2: eapply weaken_qstp_gen; intuition.
  - assert (stp Γ Σ (TFun d1 d2 T1 T2) d5 (TFun d3 d4 T3 T4) d6). { constructor; intuition. } intros.
    subst. intuition. inversion H0; inversion H; subst. apply qstp_closed in H1 as Hcl. intuition.
    constructor; try fold splice_ty. 1-2: constructor.
    1,2,5,6 : apply splice_qual_closed'. 5-8 : apply splice_ty_closed'.
    1-8: rewrite app_length in *; rewrite splice_env_length in *; auto.
    apply weaken_qstp_gen. auto.
    specialize (IHHstp1 Γ1). intuition.
    specialize (IHHstp2 ((bind_tm, false,T3, d3) :: (bind_tm, true,(TFun d1 d2 T1 T2), {♦}) :: Γ1)). intuition.
    repeat rewrite <- splice_ty_open'. repeat rewrite <- splice_qual_open'. simpl in H5.
    repeat rewrite @open_ty'_len with (Γ:=(Γ1 ↑ᴳ ‖Γ2‖) ++ Γ2) (Γ':=Γ1++Γ2).
    repeat rewrite @openq'_len with (Γ:=(Γ1 ↑ᴳ ‖Γ2‖) ++ Γ2) (Γ':=Γ1++Γ2).
    replace ({♦} ↑ᵈ (‖ Γ2 ‖)) with ({♦}) in H5; auto.
    all: repeat rewrite app_length; rewrite splice_env_length; auto.
  - intros. specialize (IHHstp1 Γ1). specialize (IHHstp2 Γ1). intuition.
    eapply s_trans; eauto.
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

Lemma narrowing_qstp_gen : forall{Γ1 bd b U du Γ2 Σ d1 d2},
    qstp (Γ1 ++ (bd, b,U,du) :: Γ2) Σ d1 d2 -> (b = true -> (♦∈ du)) ->
    forall {V dv}, stp Γ2 Σ V dv U du ->
              qstp (Γ1 ++ (bd, b,V,dv) :: Γ2) Σ d1 d2.
  intros Γ1 bd b U du Γ2 Σ d1 d2 HST Hb. remember (Γ1 ++ (bd, b,U,du) :: Γ2) as Γ.
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
      eapply qs_trans. eapply qs_qvar_ty. rewrite indexr_skips; auto. apply indexr_head.
      1,2 : apply stp_closed in H3; intuition.
      apply stp_qstp_inv in H3. eapply qstp_non_fresh; eauto.
      apply stp_qstp_inv in H3. eapply weaken_qstp'. eapply weaken_qstp. auto. auto.
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
       erewrite  indexr_skips in  H; eauto. erewrite indexr_head in H.  inversion H. subst. apply H0.
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
    1, 2: rewrite app_length in *; simpl in *; auto.
    1, 2: eapply narrowing_qstp_gen; subst; eauto.
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
    Unshelve. auto.
Qed.

Lemma narrowing_stp : forall{b U du Γ Σ T1 d1 T2 d2}, stp ((bind_tm, b,U,du) :: Γ) Σ T1 d1 T2 d2 -> (b = true -> (♦∈ du)) ->
    forall {V dv}, stp Γ Σ V dv U du -> stp ((bind_tm, b,V,dv) :: Γ) Σ T1 d1 T2 d2.
  intros. specialize (@narrowing_stp_gen [] b U du Γ Σ T1 d1 T2 d2) as narrow. simpl in *. eapply narrow; eauto.
Qed.

Lemma narrowing_qstp_ty_gen : forall{Γ1 bd U du Γ2 Σ d1 d2},
    qstp (Γ1 ++ (bind_ty, bd,U,du) :: Γ2) Σ d1 d2 ->
    forall {V dv}, stp Γ2 Σ V dv U du ->
            qstp (Γ1 ++ (bind_ty, bd,V,dv) :: Γ2) Σ d1 d2.
  intros Γ1 bd U du Γ2 Σ d1 d2 HST Hb. remember (Γ1 ++ (bind_ty, bd,U,du) :: Γ2) as Γ.
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
  + constructor; auto. apply weaken_qstp_store. auto.
    1, 2: rewrite app_length; eapply closed_qual_monotone; eauto; lia.
    1, 2: eapply weaken_qstp_store; intuition.
  + constructor; auto. 1,2 : rewrite app_length; eapply closed_ty_monotone; eauto; lia.
    apply weaken_qstp_store. auto.
  + specialize (IHHSTP1 Σ'). specialize (IHHSTP2 Σ'). eapply s_trans in IHHSTP2; eauto.
Qed.

Lemma weaken_stp_store_ext : forall {Σ Γ T1 d1 T2 d2}, stp Γ Σ T1 d1 T2 d2 -> forall {Σ'}, Σ' ⊇ Σ ->  stp Γ Σ' T1 d1 T2 d2.
  intros. unfold extends in H0. destruct H0. subst. apply weaken_stp_store. auto.
Qed.

Lemma stp_shrink_var : forall {Γ Σ T1 d1 T2 d2}, stp Γ Σ T1 d1 T2 d2 -> forall {fr x}, x < ‖Γ‖ -> stp Γ Σ T1 ${fr}x T2 ${fr}x.
  intros. eapply stp_qual_irrelevance; eauto. apply qs_sq; auto. apply just_fv_closed. auto.
Qed.

Lemma narrowing_stp_ty_gen : forall{Γ1 b U du Γ2 Σ T1 d1 T2 d2},
      stp (Γ1 ++ ((bind_ty, b, U, du)) :: Γ2) Σ T1 d1 T2 d2 ->
      forall {V dv }, closed_ty  0 0 (‖ Σ ‖) V -> closed_qual  0 0 (‖ Σ ‖) dv ->
      (stp Γ2 Σ V dv U du) ->
      stp (Γ1 ++ ((bind_ty, b, V, dv)) :: Γ2) Σ T1 d1 T2 d2.
Proof. intros Γ1 b U du Γ2 Σ T1 d1 T2 d2 HST. remember (Γ1 ++ ((bind_ty, b, U, du)) :: Γ2) as Γ.
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
    1,2 : rewrite app_length in *; simpl in *; auto.
    1,2: eapply narrowing_qstp_ty_gen; subst; eauto.
  - (* TFUN *)  rewrite HeqΓ in *. constructor.
    subst. rewrite app_length in *. simpl in *. auto.
    subst. rewrite app_length in *. simpl in *. auto.
    eapply narrowing_qstp_ty_gen; subst; eauto. eapply IHHST1; eauto.
    unfold open_ty' in *. unfold openq' in *.
    rewrite app_length in *. simpl in *.
    repeat rewrite app_comm_cons.
    eapply IHHST2; eauto.
  - subst. specialize (IHHST1 Γ1).  specialize (IHHST2 Γ1). intuition.
    specialize (H2 V dv). specialize (H3 V dv). intuition.  eapply s_trans; eauto.
Qed.

Lemma narrowing_stp_ty : forall{bd U du Γ Σ T1 d1 T2 d2}, stp (((bind_ty, bd, U, du)) :: Γ) Σ T1 d1 T2 d2 ->
  forall {V dv}, closed_ty 0 0 (length Σ) V -> closed_Qual 0 0 (length Σ) dv↑ ->  stp Γ Σ V dv U du ->
    stp (((bind_ty, bd, V, dv)) :: Γ) Σ T1 d1 T2 d2.
   intros. specialize (@narrowing_stp_ty_gen [] bd U du Γ Σ T1 d1 T2 d2) as narrow. simpl in narrow. intuition.
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

Lemma saturated_tenv_saturated : forall {Γ Σ q}, saturated Γ Σ q -> tenv_saturated Γ q.
  intros. inversion H. auto.
Qed.
#[global] Hint Resolve saturated_tenv_saturated : core.

Lemma saturated_senv_saturated : forall {Γ Σ q}, saturated Γ Σ q -> senv_saturated Σ q.
  intros. inversion H. auto.
Qed.
#[global] Hint Resolve saturated_senv_saturated : core.

Lemma senv_saturated_conss : forall {Σ q}, senv_saturated Σ q -> closed_Qual 0 0 (‖ Σ ‖) q ↑ -> forall {T q'}, senv_saturated ((T, q') :: Σ) q.
intros. unfold senv_saturated,qenv_saturated_q. intros. eapply H; eauto. erewrite <- indexr_skip; eauto. Qcrush. eauto.
Qed.
#[global] Hint Resolve senv_saturated_conss : core.

Lemma wf_tenv_prop : forall {Γ Σ}, wf_tenv Γ Σ -> forall l bd fr T q, indexr l Γ = Some (bd, fr, T, q) -> (closed_ty 0 l (‖ Σ ‖) T /\ closed_Qual 0 l (‖ Σ ‖) q↑).
  intros Γ Σ Hwf. induction Hwf; intros. simpl in H0. discriminate. destruct (l =? ‖Γ‖) eqn:Heq.
  - simpl in H1. rewrite Heq in H1. inversion H1. subst. apply Nat.eqb_eq in Heq. subst. intuition; eauto using closed_Qual_monotone,closed_ty_monotone.
  - simpl in H1. rewrite Heq in H1. apply IHHwf in H1. intuition; eauto using closed_Qual_monotone,closed_ty_monotone.
Qed.

Lemma wf_tenv_wf_senv : forall {Γ Σ}, wf_tenv Γ Σ -> wf_senv Σ.
  intros Γ Σ Hwf. induction Hwf; intros; auto.
Qed.
#[global] Hint Resolve wf_tenv_wf_senv : core.

Lemma wf_tenv_closed_qenv :
  forall Γ Σ, wf_tenv Γ Σ -> closed_qenv 0 (‖ Γ ‖) (‖ Σ ‖) Γ.
intros. induction Γ; unfold closed_qenv.
- intros. simpl in *. discriminate.
- inversion H. subst. intros. bdestruct (x =? (‖ Γ ‖)). subst. rewrite indexr_head in H0. inversion H0. subst. simpl. eapply closed_Qual_monotone; eauto. auto. destruct a as [ [ [bd' fr'] T'] q']. simpl. specialize (wf_tenv_prop H x bd' fr' T' q'). intuition. eapply closed_Qual_monotone; eauto. apply indexr_var_some' in H0. simpl in H0. lia.
Qed.

Lemma wf_senv_prop : forall {Σ}, wf_senv Σ -> forall l T q, indexr l Σ = Some (T, q) -> (closed_ty 0 0 l T /\ closed_Qual 0 0 l q ↑ /\ ♦∉ q).
  intros Σ Hwf. induction Hwf; intros. simpl in H. discriminate. destruct (l =? ‖Σ‖) eqn:Heq.
  - simpl in H2. rewrite Heq in H2. inversion H2. subst. apply Nat.eqb_eq in Heq. subst. intuition.
  - simpl in H2. rewrite Heq in H2. apply IHHwf in H2. intuition.
Qed.

Lemma wf_senv_closed_qenv :
  forall Σ, wf_senv Σ -> closed_qenv 0 0 (‖ Σ ‖) Σ.
intros. induction Σ; unfold closed_qenv.
- intros. simpl in *. discriminate.
- inversion H. subst. intros. bdestruct (x =? (‖ Σ ‖)). subst. rewrite indexr_head in H0. inversion H0. subst. simpl. eapply closed_Qual_monotone; eauto. auto. destruct a as [T' q']. simpl. specialize (wf_senv_prop H x T' q'). intuition. eapply closed_Qual_monotone; eauto. apply indexr_var_some' in H0. simpl in H0. lia.
Qed.
#[global] Hint Resolve wf_senv_closed_qenv : core.

Lemma senv_saturated_empty : forall {Σ fr}, senv_saturated Σ ∅{ fr }.
  intros. unfold senv_saturated. intros. Qcrush.
Qed.
#[global] Hint Resolve senv_saturated_empty : core.

Lemma tenv_saturated_empty : forall {Γ fr}, tenv_saturated Γ ∅{ fr }.
  Qcrush.
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

Lemma tenv_saturated_empty_tenv : forall {q}, tenv_saturated [] q.
  intros. unfold tenv_saturated,qenv_saturated_q. intros. exfalso. discriminate.
Qed.
#[global] Hint Resolve tenv_saturated_empty_tenv : core.

Lemma senv_saturated_open_qual : forall {Σ d1 d2}, senv_saturated Σ d1 -> forall {k}, senv_saturated Σ ([[ k ~> ∅ ]]ᵈ d2) -> senv_saturated Σ ([[ k ~> d1 ]]ᵈ d2).
intros. qual_destruct d1. qual_destruct d2. unfold open_qual in *; unfold_q.
  ndestruct (bvs0 k); intuition.
  repeat rewrite empty_union_right in H0. rewrite orb_false_r in H0.
unfold senv_saturated,qenv_saturated_q in *. intros. simpl in *. specialize (H x). specialize (H0 x). nlift.
  ndestruct (lcs x); intuition.
  - eapply H in H4; eauto. eapply Subq_trans; eauto. Qcrush.
  - assert (N_or (N_lift lcs0) N_empty x). Qcrush. eapply H0 in H5; eauto. eapply Subq_trans; eauto. Qcrush.
Qed.

Lemma senv_saturated_openq : forall {f Σ df d1 d2},
    senv_saturated Σ df -> closed_Qual 0 f (‖Σ‖) df↑ ->
    senv_saturated Σ d1 -> closed_Qual 0 f (‖Σ‖) d1↑ -> senv_saturated Σ (openq ∅ ∅ d2) -> senv_saturated Σ (openq df d1 d2).
    intros. unfold openq in *. apply senv_saturated_open_qual; auto.
    erewrite open_qual_commute''; eauto. erewrite open_qual_commute'' in H3; eauto.
    eapply senv_saturated_open_qual; auto. Unshelve. all: apply 0.
Qed.

Lemma saturated_senv_qor : forall {Σ q1 q2}, senv_saturated Σ q1 -> senv_saturated Σ q2 -> senv_saturated Σ (q1 ⊔ q2).
  intros. unfold senv_saturated,qenv_saturated_q in *. intros. specialize (H x). specialize (H0 x).
  qual_destruct q1. qual_destruct q2. simpl in *. nlift.
  ndestruct (lcs x); intuition.
  - eapply H in H3; eauto. eapply Subq_trans; eauto.
  - assert (N_lift lcs0 x). Qcrush. eapply H0 in H4; eauto. eapply Subq_trans; eauto.
Qed.
#[global] Hint Resolve saturated_senv_qor : core.

Lemma saturated_qor : forall {Γ Σ q1 q2}, saturated Γ Σ q1 -> saturated Γ Σ q2 -> saturated Γ Σ (q1 ⊔ q2).
  intros. inversion H. inversion H0. constructor; auto.
  unfold tenv_saturated,qenv_saturated_q in *. intros. specialize (H1 x). specialize (H3 x).
#[local] Hint Resolve qmem_reflect : bdestruct.
bdestruct ($ x ∈?ᵥ q1); intuition.
#[local] Remove Hints qmem_reflect : bdestruct.
  - eapply H1 in H7; eauto. eapply Subq_trans; eauto.
  - assert ($ x ∈ᵥ q2). Qcrush. eapply H3 in H8; eauto. eapply Subq_trans; eauto.
Qed.
#[global] Hint Resolve saturated_qor : core.

(* NOTE: depends on the fact that d does not have free variables <2024-01-07, David Deng> *)
Lemma senv_saturated_splice : forall Σ d n, senv_saturated Σ d -> forall {b l}, closed_qenv b 0 l Σ -> senv_saturated Σ (d ↑ᵈ n).
intros. unfold senv_saturated,qmem,qenv_saturated_q in *. intros. specialize (H x). assert (N_lift (qlocs d) x). Qcrush. specialize (H0 x a). intuition. eapply H in H2; eauto. Qcrush. eauto. exfalso; eauto.
Qed.
#[global] Hint Resolve senv_saturated_splice : core.

Lemma senv_saturated_qqplus : forall {Σ q1 q2}, senv_saturated Σ q1 -> senv_saturated Σ q2 -> senv_saturated Σ (q1 ⋓ q2).
  intros. qual_destruct q1. destruct fr; simpl; auto.
Qed.
#[global] Hint Resolve senv_saturated_qqplus : core.

Lemma saturated_qqplus : forall {Γ Σ q1 q2}, saturated Γ Σ q1 -> saturated Γ Σ q2 -> saturated Γ Σ (q1 ⋓ q2).
  intros. qual_destruct q1. destruct fr; simpl; auto.
Qed.
#[global] Hint Resolve saturated_qqplus : core.

Lemma qenv_saturated_q_qand : forall {p : Type} `{qenv p} {E : env p} {q1 q2}, qenv_saturated_q E q1 -> qenv_saturated_q E q2 -> qenv_saturated_q E (q1 ⊓ q2).
  intros. unfold qenv_saturated_q in *. intros. specialize (H0 x). specialize (H1 x).
rewrite Q_lift_and in H2. erewrite Qn_and_dist in H2; eauto. assert (qenv_Qn q1↑ x). Qcrush. assert (qenv_Qn q2↑ x). Qcrush. eapply H0 in H4; eauto. eapply H1 in H5; eauto. Qcrush.
Unshelve. apply qenv_qn. apply qenv_qn_prop.
Qed.
#[global] Hint Resolve qenv_saturated_q_qand : core.

Lemma saturated_qand : forall {Γ Σ q1 q2}, saturated Γ Σ q1 -> saturated Γ Σ q2 -> saturated Γ Σ (q1 ⊓ q2).
  intros. inversion H. inversion H0. constructor; auto.
Qed.
#[global] Hint Resolve saturated_qand : core.

Lemma weaken_store_senv_saturated : forall {Σ q}, senv_saturated Σ q -> forall {b f}, closed_Qual b f (‖ Σ ‖) q ↑ -> forall {Σ'}, Σ' ⊇ Σ -> senv_saturated Σ' q.
intros. unfold senv_saturated,qenv_saturated_q in *. intros.
eapply H; eauto. inversion H1. subst. bdestruct (x <? (‖ Σ ‖)). rewrite indexr_skips in H3; auto. Qcrush. exfalso. eauto.
Qed.

Lemma weaken_store_saturated : forall {Γ Σ q}, saturated Γ Σ q -> forall {b f}, closed_Qual b f (‖ Σ ‖) q ↑ -> forall {Σ'}, Σ' ⊇ Σ -> saturated Γ Σ' q.
  intros. inversion H. constructor; auto. eapply weaken_store_senv_saturated; eauto.
Qed.

Lemma closed_Qual_open2 : forall {f l d1 d2 d}, closed_Qual 2 f l d ↑ -> closed_Qual 0 f l d1 ↑ -> closed_Qual 0 f l d2 ↑ -> closed_Qual 0 f l ([[1 ~> d1 ]]ᵈ ([[0 ~> d2 ]]ᵈ d)) ↑.
  intros. apply Q_lift_closed'. erewrite open_qual_commute''; eauto using closed_qual_open'.
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
  - econstructor. eapply closed_ty_monotone; eauto; lia.
    eapply closed_qual_monotone; eauto; lia.
  - inversion H3. intuition. econstructor; Qcrush.
  - inversion H3. intuition.
  - apply stp_closed in H. intuition.
  - apply stp_closed in H. intuition.
Qed.

Lemma qenv_saturated_q_shrink : forall {p : Type} `{qenv p} (E : env p) (q : qual) (a : p),
  qenv_saturated_q (a::E) q ->
  qenv_saturated_q (E) q.
intros. unfold qenv_saturated_q in *. intros. eapply H0 in H1; eauto. apply indexr_extend1; auto.
Qed.
#[global] Hint Resolve qenv_saturated_q_shrink: core.

(* NOTE: the alternative saturated definition does not require telescope <2024-01-08, David Deng> *)
Lemma senv_saturated_qplus : forall {Σ l T q}, indexr l Σ = Some (T, q) -> senv_saturated Σ q -> senv_saturated Σ (q ⊔ &!l).
unfold senv_saturated,qenv_saturated_q. intros. qual_destruct q. simpl in *. rewrite N_lift_or in H1. destruct H1.
  - apply H0 in H2. Qcrush. eauto.
  - nlift. unfold N_one in H1. subst. rewrite H in H2. inversion H2. subst. simpl. Qcrush.
Qed.

Lemma wf_senv_saturated_qplus : forall {Σ}, wf_senv Σ -> forall {l T q}, indexr l Σ = Some (T, q) -> senv_saturated Σ q -> senv_saturated Σ (q ⊔ &!l).
  intros. specialize (wf_senv_prop H l T q) as Hwf. intuition. eapply senv_saturated_qplus; eauto.
Qed.

Lemma has_type_senv_saturated : forall {Γ φ Σ t T q}, has_type Γ φ Σ t T q -> (*wf_senv Σ -> *)senv_saturated Σ q.
intros. induction H; eauto; intuition.
  - apply has_type_closed in H. intuition. eapply senv_saturated_openq; eauto.
  - apply has_type_closed in H. intuition. eapply senv_saturated_openq; eauto.
  - intuition. apply has_type_closed in H, H0. intuition. eapply senv_saturated_openq; eauto.
  - intuition. apply has_type_closed in H, H0. intuition. eapply senv_saturated_openq; eauto.
  - eapply senv_saturated_qplus; eauto.
Qed.

Lemma qstp_empty : forall {Σ q1 q2}, qstp [] Σ q1 q2 -> q1 ⊑↑ q2.
  intros. remember [] as Γ. induction H; subst; auto; try solve [simpl in H; discriminate]. auto.
  intuition. Qcrush.
Qed.

Lemma open_qual_subqual : forall {d1 d2 φ}, d1 ⊑↑ φ -> forall {k}, ([[ k ~> ∅ ]]ᵈ d2) ⊑↑ φ -> ([[ k ~> d1 ]]ᵈ d2) ⊑↑ φ.
  intros. qual_destruct d2.
unfold_q. ndestruct (bvs k); simpl; auto. Qcrush.
Qed.

Lemma openq_subqual : forall {df d1 d2 φ f l}, closed_Qual 0 f l φ↑ -> df ⊑↑ φ -> d1 ⊑↑ φ -> d2 <~ᵈ ∅; ∅ ⊑↑ φ -> d2 <~ᵈ df; d1 ⊑↑ φ.
  intros. unfold openq in *. apply open_qual_subqual; auto. erewrite open_qual_commute''; eauto.
  erewrite open_qual_commute'' in H2; eauto. apply open_qual_subqual; auto.
  Unshelve. all : apply 0.
Qed.

Fixpoint has_type_filter {Γ φ Σ t T d} (ht : has_type Γ φ Σ t T d) {struct ht} : d ⊑↑ φ ⊔ {♦}.
Proof.
  destruct ht; intuition.
  - Qcrush.
  - specialize (has_type_closed ht) as Hc. specialize (has_type_filter _ _ _ _ _ _ ht). intuition.
    assert (d1 ⊑↑ φ ⊔ {♦}). Qcrush.
    assert (d2 <~ᵈ ∅; ∅ ⊑↑ φ ⊔ {♦}). Qcrush.
    assert (closed_Qual 0 (‖ Γ ‖) (‖ Σ ‖) (φ ⊔ {♦}) ↑). Qcrush.
    eapply openq_subqual; eauto.
  - specialize (has_type_closed ht) as Hc. specialize (has_type_filter _ _ _ _ _ _ ht). intuition.
    assert (d1 ⊑↑ φ ⊔ {♦}). Qcrush.
    assert (d2 <~ᵈ ∅; ∅ ⊑↑ φ ⊔ {♦}). Qcrush.
    assert (closed_Qual 0 (‖ Γ ‖) (‖ Σ ‖) (φ ⊔ {♦}) ↑). Qcrush.
    eapply openq_subqual; eauto.
  - Qcrush.
  - Qcrush.
  - specialize (has_type_closed ht1) as Hc1. specialize (has_type_closed ht2) as Hc2. intuition.
    inversion H6. subst. specialize (has_type_filter _ _ _ _ _ _ ht1) as Hfl1.
    specialize (has_type_filter _ _ _ _ _ _ ht2) as Hfl2.
    assert (d2 <~ᵈ ∅; ∅ ⊑↑ φ ⊔ {♦}). Qcrush.
    assert (closed_Qual 0 (‖ Γ ‖) (‖ Σ ‖) (φ ⊔ {♦}) ↑). Qcrush.
    eapply openq_subqual; eauto.
  - specialize (has_type_closed ht1) as Hc1. specialize (has_type_closed ht2) as Hc2. intuition.
    inversion H6. subst. specialize (has_type_filter _ _ _ _ _ _ ht1) as Hfl1.
    specialize (has_type_filter _ _ _ _ _ _ ht2) as Hfl2.
    assert (d2 <~ᵈ ∅; ∅ ⊑↑ φ ⊔ {♦}). Qcrush.
    assert (closed_Qual 0 (‖ Γ ‖) (‖ Σ ‖) (φ ⊔ {♦}) ↑). Qcrush.
    eapply openq_subqual; eauto.
  - Qcrush.
  - specialize (has_type_filter _ _ _ _ _ _ ht). Qcrush.
  - Qcrush.
Qed.

Lemma bound_vars_untypable : forall {Γ φ Σ T d i}, has_type Γ φ Σ #i T d -> False.
  intros Γ φ Σ T d i HT. remember (tvar #i) as t. induction HT; try discriminate; intuition.
Qed.

Lemma n_splice_injective : forall n n' k, n_splice k n = n_splice k n' -> n = n'.
Proof.
  intros. unfold_n. apply FunctionalExtensionality.functional_extensionality. intros. bdestruct (x <? k).
  - apply FunctionalExtensionality.equal_f with (x:=x) in H. bdestruct (x =? k). intuition. apply Nat.ltb_lt in H0. rewrite H0 in H. apply H.
  - apply FunctionalExtensionality.equal_f with (x:=S x) in H. bdestruct (S x =? k). lia. bdestruct (S x <? k). lia. simpl in *. apply H.
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

(**********************
*  q_trans'' splice  *
**********************)

Lemma q_trans_one_splice_tenv_gen : forall (Γ : tenv) d n,
  n >= (‖ Γ ‖) ->
  (q_trans_one Γ d) ↑ᵈ n = q_trans_one (Γ ↑ᴳ n) (d ↑ᵈ n).
intros. generalize dependent n. induction Γ; intros; simpl; auto. rewrite splice_env_length; auto. ndestruct (qfvs d (‖ Γ ‖)).
  - assert (N_lift (qfvs (d ↑ᵈ n)) (‖ Γ ‖)). Qcrush. clift. rewrite splice_qual_qor_dist. rewrite IHΓ. Qcrush. simpl in *. lia.
  - assert (~N_lift (qfvs (d ↑ᵈ n)) (‖ Γ ‖)). Qcrush. clift. Qcrush.
Qed.

Lemma q_trans_one_splice_tenv : forall (Γ1 Γ2 : tenv) X d,
  (q_trans_one (Γ1 ++ Γ2) d) ↑ᵈ (‖ Γ2 ‖) =
  (q_trans_one (Γ1 ↑ᴳ (‖ Γ2 ‖) ++ X :: Γ2 ↑ᴳ (‖ Γ2 ‖)) (d ↑ᵈ (‖ Γ2 ‖))).
intros. induction Γ1; simpl; try rewrite splice_env_length; auto.
  - ndestruct (qfvs (d ↑ᵈ (‖ Γ2 ‖)) (‖ Γ2 ‖)).
    + exfalso. Qcrush.
    + rewrite q_trans_one_splice_tenv_gen; eauto.
  - ndestruct (qfvs d (‖ Γ1 ++ Γ2 ‖)).
    + assert (N_lift (qfvs (d ↑ᵈ (‖ Γ2 ‖))) (‖ Γ1 ↑ᴳ (‖ Γ2 ‖) ++ X :: Γ2 ↑ᴳ (‖ Γ2 ‖) ‖)). { rewrite app_length,splice_env_length in *; auto. simpl. rewrite splice_env_length; auto. rewrite <- plus_n_Sm. Qcrush. } clift. rewrite <- IHΓ1. rewrite splice_qual_qor_dist. destruct a as [ [ [bd b] T] q]. simpl. auto.
    + assert (~N_lift (qfvs (d ↑ᵈ (‖ Γ2 ‖))) (‖ Γ1 ↑ᴳ (‖ Γ2 ‖) ++ X :: Γ2 ↑ᴳ (‖ Γ2 ‖) ‖)). { rewrite app_length,splice_env_length in *; auto. simpl. rewrite splice_env_length; auto. rewrite <- plus_n_Sm. Qcrush. } clift.
Qed.

Lemma q_trans''_splice_tenv_qfr_inv : forall (Γ1 Γ2 : tenv) X d fuel,
(qfr (q_trans'' (Γ1 ++ Γ2) d fuel)) =
(qfr (q_trans'' (Γ1 ↑ᴳ (‖ Γ2 ‖) ++ X :: Γ2 ↑ᴳ (‖ Γ2 ‖)) (d ↑ᵈ (‖ Γ2 ‖)) fuel)).
intros. generalize dependent d. induction fuel; intros; simpl; auto. rewrite IHfuel. erewrite q_trans_one_splice_tenv; eauto.
Qed.

Lemma q_trans''_splice_tenv_qfvs_dist : forall (Γ1 Γ2 : tenv) X d fuel,
qfvs ((q_trans'' (Γ1 ++ Γ2) d fuel) ↑ᵈ (‖ Γ2 ‖)) =
qfvs ((q_trans'' (Γ1 ↑ᴳ (‖ Γ2 ‖) ++ X :: Γ2 ↑ᴳ (‖ Γ2 ‖)) (d ↑ᵈ (‖ Γ2 ‖)) fuel)).
intros. generalize dependent d. induction fuel; intros; simpl; auto. rewrite IHfuel. erewrite q_trans_one_splice_tenv; eauto.
Qed.

Lemma q_trans''_splice_tenv_qbvs_inv : forall (Γ1 Γ2 : tenv) X d fuel,
(qbvs (q_trans'' (Γ1 ++ Γ2) d fuel)) =
(qbvs (q_trans'' (Γ1 ↑ᴳ (‖ Γ2 ‖) ++ X :: Γ2 ↑ᴳ (‖ Γ2 ‖)) (d ↑ᵈ (‖ Γ2 ‖)) fuel)).
intros. generalize dependent d. induction fuel; intros; simpl; auto. rewrite IHfuel. erewrite q_trans_one_splice_tenv; eauto.
Qed.

Lemma q_trans''_splice_tenv_qlocs_inv : forall (Γ1 Γ2 : tenv) X d fuel,
(qlocs (q_trans'' (Γ1 ++ Γ2) d fuel)) =
(qlocs (q_trans'' (Γ1 ↑ᴳ (‖ Γ2 ‖) ++ X :: Γ2 ↑ᴳ (‖ Γ2 ‖)) (d ↑ᵈ (‖ Γ2 ‖)) fuel)).
intros. generalize dependent d. induction fuel; intros; simpl; auto. rewrite IHfuel. erewrite q_trans_one_splice_tenv; eauto.
Qed.

Lemma splice_q_trans_tenv_comm : forall {Γ1 Γ2 X q},
(q_trans_tenv (Γ1 ↑ᴳ (‖ Γ2 ‖) ++ X :: Γ2 ↑ᴳ (‖ Γ2 ‖)) (q ↑ᵈ (‖ Γ2 ‖))) =
(q_trans_tenv (Γ1 ++ Γ2) q ↑ᵈ (‖ Γ2 ‖)).
intros. apply Q_lift_eq. unfold q_trans_tenv. rewrite Q_lift_splice_qual. repeat rewrite Q_lift_trans''. unfold splice_Qual, Q_trans''. unfold qfresh,qfvs,qbvs,qlocs; simpl. f_equal. f_equal. f_equal.
- repeat rewrite <- N_lift_trans'' with (f:=qfr); auto. rewrite app_length. simpl. rewrite <- plus_n_Sm. erewrite <- q_trans''_splice_tenv_qfr_inv; eauto. rewrite q_trans''_fuel_max. auto. rewrite app_length. repeat rewrite splice_env_length; auto.
- rewrite <- N_lift_trans'' with (f:=qfvs); auto. rewrite <- q_trans''_splice_tenv_qfvs_dist. rewrite Q_lift_qn. rewrite Q_lift_splice_qual. unfold splice_Qual. unfold qfvs. simpl. rewrite q_trans''_fuel_max. rewrite N_lift_trans'' with (F:=qfvs); eauto. repeat rewrite app_length. simpl. repeat rewrite splice_tenv_length. rewrite <- plus_n_Sm. repeat rewrite splice_env_length; auto.
- repeat rewrite <- N_lift_trans'' with (f:=qbvs); auto. rewrite app_length. simpl. rewrite <- plus_n_Sm. erewrite <- q_trans''_splice_tenv_qbvs_inv; eauto. rewrite q_trans''_fuel_max. auto. rewrite app_length. repeat rewrite splice_env_length; auto.
- repeat rewrite <- N_lift_trans'' with (f:=qlocs); auto. rewrite app_length. simpl. rewrite <- plus_n_Sm. erewrite <- q_trans''_splice_tenv_qlocs_inv; eauto. rewrite q_trans''_fuel_max. auto. rewrite app_length. repeat rewrite splice_env_length; auto.
Qed.

Lemma q_trans_one_splice_senv : forall (Σ : senv) d n,
  (q_trans_one Σ d) ↑ᵈ n =
  q_trans_one (Σ ↑ᴳ n) (d ↑ᵈ n).
intros. induction Σ; simpl; auto. rewrite splice_env_length; auto. ndestruct (qlocs d (‖ Σ ‖)); auto. rewrite splice_qual_qor_dist. rewrite IHΣ. Qcrush.
Qed.

Lemma q_trans''_splice_senv_qfr_inv : forall Σ n d fuel,
  (qfr (q_trans'' (Σ ↑ᴳ n) (d ↑ᵈ n) fuel)) =
  (qfr ((q_trans'' Σ d fuel) ↑ᵈ n)).
intros. generalize dependent d. induction fuel; intros; simpl; auto. rewrite <- IHfuel. rewrite q_trans_one_splice_senv. auto.
Qed.

Lemma q_trans''_splice_senv_qfvs_dist : forall Σ n d fuel,
  (qfvs (q_trans'' (Σ ↑ᴳ n) (d ↑ᵈ n) fuel)) =
  (n_splice n (qfvs (q_trans'' Σ d fuel))).
intros. generalize dependent d. induction fuel; intros; simpl; auto. rewrite <- IHfuel. rewrite q_trans_one_splice_senv. auto.
Qed.

Lemma q_trans''_splice_senv_qbvs_inv : forall Σ n d fuel,
  (qbvs (q_trans'' (Σ ↑ᴳ n) (d ↑ᵈ n) fuel)) =
  (qbvs (q_trans'' Σ d fuel)).
intros. generalize dependent d. induction fuel; intros; simpl; auto. rewrite <- IHfuel. rewrite q_trans_one_splice_senv. auto.
Qed.

Lemma q_trans''_splice_senv_qlocs_inv : forall Σ n d fuel,
  (qlocs (q_trans'' (Σ ↑ᴳ n) (d ↑ᵈ n) fuel)) =
  (qlocs (q_trans'' Σ d fuel)).
intros. generalize dependent d. induction fuel; intros; simpl; auto. rewrite <- IHfuel. rewrite q_trans_one_splice_senv. auto.
Qed.

Lemma splice_q_trans_senv_comm : forall {Σ q n},
(q_trans_senv (Σ ↑ᴳ n) (q ↑ᵈ n)) =
(q_trans_senv Σ q ↑ᵈ n).
intros. apply Q_lift_eq. unfold q_trans_senv. rewrite Q_lift_splice_qual. repeat rewrite Q_lift_trans''. unfold splice_Qual, Q_trans''. unfold qfresh,qfvs,qbvs,qlocs; simpl. f_equal. f_equal. f_equal.
- repeat rewrite <- N_lift_trans'' with (f:=qfr); auto. erewrite q_trans''_splice_senv_qfr_inv; eauto. erewrite splice_env_length; eauto.
- repeat rewrite <- N_lift_trans'' with (f:=qfvs); auto. erewrite q_trans''_splice_senv_qfvs_dist; eauto. erewrite splice_env_length; eauto. rewrite N_lift_splice. auto.
- repeat rewrite <- N_lift_trans'' with (f:=qbvs); auto. erewrite q_trans''_splice_senv_qbvs_inv; eauto. erewrite splice_env_length; eauto.
- repeat rewrite <- N_lift_trans'' with (f:=qlocs); auto. erewrite q_trans''_splice_senv_qlocs_inv; eauto. erewrite splice_env_length; eauto.
Qed.

Lemma wf_tenv_splice_lower_id : forall Γ1 Γ2 Σ d,
  wf_tenv Γ2 Σ ->
  forall n, (‖ Γ2 ‖) <= n ->
  q_trans_tenv (Γ1 ++ Γ2 ↑ᴳ n) d =
  q_trans_tenv (Γ1 ++ Γ2) d.
intros. unfold q_trans_tenv. repeat rewrite app_length. erewrite splice_env_length; eauto. remember (‖ Γ1 ‖ + ‖ Γ2 ‖). generalize dependent Γ1. generalize dependent n. induction Γ2; intros; simpl; auto. inversion H. subst. simpl. erewrite splice_ty_id; eauto using closed_ty_monotone. erewrite splice_qual_id; eauto using closed_Qual_monotone. replace (Γ1 ++ (bd, fr, T, q) :: Γ2 ↑ᴳ n) with ((Γ1 ++ [(bd, fr, T, q)]) ++ Γ2 ↑ᴳ n) by intuition. replace (Γ1 ++ (bd, fr, T, q) :: Γ2) with ((Γ1 ++ [(bd, fr, T, q)]) ++ Γ2) by intuition. erewrite IHΓ2; eauto. simpl in H0. lia. simpl. rewrite app_length. simpl. lia.
Qed.

Lemma wf_tenv_splice_lower_id' : forall Γ1 Γ2 X Σ d,
  wf_tenv Γ2 Σ ->
  forall n, (‖ Γ2 ‖) <= n ->
  q_trans_tenv (Γ1 ++ X :: Γ2 ↑ᴳ n) d =
  q_trans_tenv (Γ1 ++ X :: Γ2) d.
intros. replace (Γ1 ++ X :: Γ2 ↑ᴳ n) with ((Γ1 ++ [X]) ++ Γ2 ↑ᴳ n) by intuition. erewrite wf_tenv_splice_lower_id; eauto. replace ((Γ1 ++ [X]) ++ Γ2) with (Γ1 ++ X :: Γ2) by intuition. auto.
Qed.

Lemma wf_senv_splice_id : forall Σ n,
  wf_senv Σ ->
  Σ ↑ᴳ n = Σ.
intros. induction Σ; simpl; auto. inversion H. subst. simpl. erewrite splice_ty_id. erewrite splice_qual_id. rewrite IHΣ; auto. eapply closed_qual_monotone; eauto. lia. eapply closed_ty_monotone; eauto. lia.
Qed.

Lemma wf_senv_shrink : forall {Σ a}, wf_senv (a::Σ) -> wf_senv Σ.
intros. inversion H. auto.
Qed.
#[global] Hint Resolve wf_senv_shrink : core.

Lemma wf_tenv_shrink : forall {Γ Σ a}, wf_tenv (a::Γ) Σ -> wf_tenv Γ Σ.
intros. inversion H. auto.
Qed.
#[global] Hint Resolve wf_tenv_shrink : core.

Lemma closed_qenv_q_trans_one_monotone : forall {p : Type} `{qenv p} (E : env p) (q : qual) (b f l : nat),
  closed_qenv b f l E -> closed_Qual b f l q ↑ -> closed_Qual b f l (q_trans_one E q)↑.
intros. induction E; simpl; auto. ndestruct (qenv_qn q (‖ E ‖)). apply closed_Qual_qor. apply IHE. eapply closed_qenv_shrink; eauto. apply H0 with (x:=(‖ E ‖)). apply indexr_head. apply IHE. eapply closed_qenv_shrink; eauto.
Qed.

Lemma closed_qenv_q_trans''_monotone : forall {p : Type} `{qenv p} (E : env p) (q : qual) (b f l fuel : nat),
  closed_qenv b f l E -> closed_Qual b f l q ↑ -> closed_Qual b f l (q_trans'' E q fuel)↑.
intros. generalize dependent q. induction fuel; intros; simpl; auto. apply IHfuel. apply closed_qenv_q_trans_one_monotone; auto.
Qed.

Lemma closed_qenv_qn_trans_one_closed : forall {p : Type} `{qenv p} (E : env p) q n,
  n >= (‖ E ‖) ->
  closed_qenv_qn n E ->
  closed_Nats n (qenv_Qn q ↑) ->
  closed_Nats n (qenv_Qn (q_trans_one E q) ↑).
intros. generalize dependent n. induction E; intros; simpl; auto. ndestruct (qenv_qn q (‖ E ‖)). erewrite <- @Q_lift_qn with (qn:=qenv_qn); eauto. erewrite qn_or_dist. assert (closed_Nats n (qenv_Qn (q_trans_one E q) ↑)). eapply IHE; eauto. simpl in *. lia. eapply closed_qenv_qn_shrink; eauto.
nlift. repeat erewrite Q_lift_qn; eauto. unfold closed_Nats in *. intros. destruct H5. apply H4. eauto. unfold closed_qenv_qn in H1. specialize (H1 (‖ E ‖) a). eapply H1; eauto. apply indexr_head. apply qenv_qn_prop. apply IHE; eauto. simpl in *. lia. eapply closed_qenv_qn_shrink; eauto. Unshelve. all: try apply qenv_qn_prop.
Qed.

Lemma q_trans''_extend_closed_id : forall {p : Type} `{qenv p} (E E' : env p) q fuel,
  E' ⊇ E ->
  closed_qenv_qn (‖ E ‖) E ->
  closed_Nats (‖ E ‖) (qenv_Qn q ↑) ->
  q_trans'' E' q fuel = q_trans'' E q fuel.
intros. generalize dependent q. induction fuel; intros; simpl; auto. erewrite q_trans_one_extend_closed_id; eauto. rewrite IHfuel; auto. apply closed_qenv_qn_trans_one_closed; auto.
Qed.

Lemma q_trans''_extend_closed_id' : forall {p : Type} `{qenv p} (a : p) (E : env p) q fuel,
  closed_qenv_qn (‖ E ‖) E ->
  closed_Nats (‖ E ‖) (qenv_Qn q ↑) ->
  q_trans'' (a::E) q fuel = q_trans'' E q fuel.
intros. generalize dependent q. induction fuel; intros. simpl; auto. replace (q_trans'' (a :: E) q (S fuel)) with (q_trans'' (a :: E) (q_trans_one (a :: E) q) (fuel)); auto. erewrite q_trans_one_extend_closed_id'; eauto. rewrite IHfuel; auto. apply closed_qenv_qn_trans_one_closed; auto.
Qed.

Lemma q_trans_extend_tenv_closed_id' : forall Γ Σ bd b T q q',
  closed_qenv_qn (‖ Γ ‖) Γ ->
  closed_Nats (‖ Γ ‖) (qfvs q' ↑) ->
  q_trans ((bd, b, T, q) :: Γ) Σ q' = q_trans Γ Σ q'.
intros. unfold q_trans,q_trans_tenv. rewrite q_trans''_extend_closed_id'; auto. rewrite q_trans''_fuel_max; auto.
Qed.

Lemma weaken_gen : forall {t Γ1 Γ2 φ Σ T d},
  wf_tenv Γ2 Σ ->
  wf_senv Σ ->
  has_type (Γ1 ++ Γ2) φ Σ t T d ->
  forall X, has_type ((Γ1 ↑ᴳ ‖Γ2‖) ++ X :: Γ2) (φ ↑ᵈ ‖Γ2‖) Σ (t ↑ᵗ ‖Γ2‖) (T ↑ᵀ ‖Γ2‖) (d ↑ᵈ ‖Γ2‖).
  intros t Γ1 Γ2 φ Σ T d wft wfs HT. remember (Γ1 ++ Γ2) as Γ. generalize dependent Γ1. generalize dependent Γ2.
  induction HT; intros; subst.
  - (* t_tabs *) rewrite app_length in *. simpl.  constructor.
    apply splice_closed'.
    1-3: rewrite app_length; rewrite splice_env_length; simpl;
      replace (‖Γ1‖ + S (‖Γ2‖)) with (S (‖Γ1‖ + ‖Γ2‖)); eauto.
    inversion H0. subst. constructor. 1,2,5: apply splice_qual_closed; auto. 1,2 : apply splice_ty_closed; auto.
    erewrite <- splice_qual_fresh. rewrite <- splice_qual_qor_dist. rewrite subqual_splice_lr'. auto.
    rewrite subqual_splice_lr'. auto.
    rewrite <- not_fresh_splice_iff. auto. eauto.
    rewrite app_comm_cons.
    replace ((bind_ty, false, T1 ↑ᵀ ‖Γ2‖, d1 ↑ᵈ ‖Γ2‖)
         :: ((bind_tm, true, TAll (d1 ↑ᵈ ‖Γ2‖) (d2 ↑ᵈ ‖Γ2‖) (T1 ↑ᵀ ‖Γ2‖) (T2 ↑ᵀ ‖Γ2‖), df ↑ᵈ ‖Γ2‖)
                      :: (Γ1 ↑ᴳ ‖Γ2‖)) ++ X :: Γ2)
       with ((((bind_ty, false,T1, d1) :: (bind_tm, true, TAll d1 d2 T1 T2, df) :: Γ1) ↑ᴳ ‖Γ2‖) ++ X :: Γ2).
    specialize (IHHT wfs Γ2 wft ((bind_ty, false, T1, d1) :: (bind_tm, true, TAll d1 d2 T1 T2, df) :: Γ1)). intuition.  rename H6 into IHHT. remember (a, b1, b0, b) as X.
    specialize (IHHT X). intuition.
    replace ((df ↑ᵈ ‖Γ2‖) ⊔ $!(‖(Γ1 ↑ᴳ ‖Γ2‖) ++ X :: Γ2‖) ⊔ $!(S (‖(Γ1 ↑ᴳ ‖Γ2‖) ++ X :: Γ2‖)))
      with  ((df ⊔ $!(‖Γ1‖ + ‖Γ2‖) ⊔ $!(S (‖Γ1‖ + ‖Γ2‖))) ↑ᵈ ‖Γ2‖).
    rewrite <- splice_open'. rewrite <- splice_ty_open'. rewrite <- splice_qual_open'.
    rewrite @open_tm'_len with (Γ':=(Γ1 ++ Γ2)). rewrite @open_ty'_len with (Γ':=(Γ1 ++ Γ2)).
    rewrite @openq'_len with (Γ':=(Γ1 ++ Γ2)). auto.
    1-4 : repeat rewrite app_length; rewrite splice_env_length; auto.
    repeat rewrite splice_qual_lub_dist. simpl.
    repeat rewrite <- plus_n_Sm. repeat f_equal; unfold_q; rewrite n_splice_one_S; try lia; repeat f_equal; lia.
    simpl. auto.

  - (* t_tapp *) simpl. rewrite splice_qual_open''. rewrite splice_ty_open''. rewrite splice_qual_empty.
    apply t_tapp; eauto.
    1-2: erewrite app_length in *; erewrite splice_env_length; eauto; simpl in *;
    replace (‖ Γ1 ‖ + S (‖ Γ2 ‖)) with (S (‖ Γ1 ‖ + ‖ Γ2 ‖)); try lia.
    apply splice_ty_closed; eauto. apply splice_qual_closed; eauto.
    rewrite <- @splice_qual_empty with (k := ‖Γ2‖); rewrite <- splice_qual_open''.
    specialize (@splice_qual_lub_dist φ ({♦}) (‖ Γ2 ‖)) as Hdist. rewrite splice_qual_fresh in Hdist.
    rewrite <- Hdist. rewrite subqual_splice_lr'; auto. rewrite subqual_splice_lr'; auto. apply wf_senv_closed_qenv in wfs.
    replace ((d2 ↑ᵈ (‖ Γ2 ‖)) <~ᵈ ∅; ∅) with ((d2 <~ᵈ ∅; ∅) ↑ᵈ (‖ Γ2 ‖)); eauto.
    rewrite splice_qual_open''. f_equal; auto. rewrite <- not_free_splice_ty_iff. auto.

  - (* t_tapp_fresh *) simpl. rewrite splice_qual_open''. rewrite splice_ty_open''. rewrite splice_qual_empty.
    apply t_tapp_fresh with (T1:=T1 ↑ᵀ ‖Γ2‖) (d1:=d1 ↑ᵈ ‖Γ2‖) (df:=df ↑ᵈ ‖Γ2‖); auto.
    replace (TAll
     (q_trans (Γ1 ↑ᴳ (‖ Γ2 ‖) ++ X :: Γ2) Σ (df ↑ᵈ (‖ Γ2 ‖))
      ⋒ q_trans (Γ1 ↑ᴳ (‖ Γ2 ‖) ++ X :: Γ2) Σ (d1 ↑ᵈ (‖ Γ2 ‖)))
     (d2 ↑ᵈ (‖ Γ2 ‖)) (T1 ↑ᵀ (‖ Γ2 ‖)) (T2 ↑ᵀ (‖ Γ2 ‖)))
     with ((TAll (q_trans (Γ1 ++ Γ2) Σ df ⋒ q_trans (Γ1 ++ Γ2) Σ d1) d2 T1 T2) ↑ᵀ (‖ Γ2 ‖)). auto.
    simpl. rewrite splice_qual_qor_dist. rewrite splice_qual_fresh. rewrite splice_qual_glb_dist. f_equal.
unfold q_trans. erewrite <- wf_tenv_splice_lower_id' with (Γ1:=(Γ1 ↑ᴳ (‖ Γ2 ‖))) (n:=(‖ Γ2 ‖)) (d:=(df ↑ᵈ (‖ Γ2 ‖))); eauto. erewrite <- wf_tenv_splice_lower_id' with (Γ1:=(Γ1 ↑ᴳ (‖ Γ2 ‖))) (n:=(‖ Γ2 ‖)) (d:=(d1 ↑ᵈ (‖ Γ2 ‖))); eauto.
repeat rewrite splice_q_trans_tenv_comm. repeat rewrite <- splice_q_trans_senv_comm. replace ((Σ ↑ᴳ (‖ Γ2 ‖))) with Σ. auto.
rewrite wf_senv_splice_id; auto.
    rewrite app_length. simpl. rewrite <- plus_n_Sm. apply splice_ty_closed; auto. eapply closed_ty_monotone; eauto. erewrite splice_env_length; eauto. rewrite app_length. lia.
    rewrite app_length. simpl. rewrite <- plus_n_Sm. apply splice_Qual_closed; auto. eapply closed_Qual_monotone; eauto. erewrite splice_env_length; eauto. rewrite app_length. lia.
    erewrite <- splice_qual_fresh. rewrite <- splice_qual_qor_dist. rewrite subqual_splice_lr'; auto.
    intros Hfresh. rewrite <- fresh_splice_iff in Hfresh. rewrite <- not_free_splice_ty_iff. auto.
    eapply senv_saturated_splice; eauto.
    rewrite <- not_free_splice_ty_iff. auto.
    rewrite <- @splice_qual_empty with (k := ‖Γ2‖); rewrite <- splice_qual_open''.
    erewrite <- splice_qual_fresh. rewrite <- splice_qual_qor_dist. rewrite subqual_splice_lr'; auto.
    unfold q_trans. erewrite <- wf_tenv_splice_lower_id' with (Γ1:=(Γ1 ↑ᴳ (‖ Γ2 ‖))) (n:=(‖ Γ2 ‖)) (d:=(df ↑ᵈ (‖ Γ2 ‖))); eauto. erewrite <- wf_tenv_splice_lower_id' with (Γ1:=(Γ1 ↑ᴳ (‖ Γ2 ‖))) (n:=(‖ Γ2 ‖)) (d:=(d1 ↑ᵈ (‖ Γ2 ‖))); eauto. repeat rewrite splice_q_trans_tenv_comm. erewrite <- wf_senv_splice_id with (Σ:=Σ); auto. repeat rewrite splice_q_trans_senv_comm. rewrite <- splice_qual_qand_dist. erewrite <- splice_qual_fresh. rewrite <- splice_qual_qor_dist. rewrite <- splice_qual_qor_dist. rewrite subqual_splice_lr'; auto.
    erewrite <- splice_qual_empty. rewrite <- splice_qual_open''. eapply senv_saturated_splice; eauto.
  - (* tunit *) simpl. rewrite splice_qual_empty.
    constructor. eapply splice_qual_closed'.
    rewrite app_length in *. unfold splice_tenv. erewrite splice_env_length; eauto.
  - (* t_var *) simpl.
    destruct (le_lt_dec (‖Γ2‖) x) eqn:Heq.
    * (* |Γ2| <= x < |Γ1|+|Γ2|*)
      rewrite splice_qual_one_S; auto.
      apply t_var with (b:=b) (d:=d ↑ᵈ ‖Γ2‖).
      rewrite <- indexr_insert_ge. apply indexr_splice_tenv; eauto. lia.
      erewrite <- splice_qual_just_fv_ge; eauto.
      rewrite subqual_splice_lr'. auto.
      eapply splice_qual_closed'.
      rewrite app_length in *. unfold splice_tenv. erewrite splice_env_length; eauto. auto.
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
      rewrite app_length in *. unfold splice_tenv. erewrite splice_env_length; eauto. auto.
      erewrite splice_ty_id; eauto. eapply closed_ty_monotone; eauto. lia. auto.
  - (* t_abs *) rewrite app_length in *. simpl. constructor; auto.
    apply splice_closed'.
    1-3: rewrite app_length; rewrite splice_env_length; simpl;
      replace (‖Γ1‖ + S (‖Γ2‖)) with (S (‖Γ1‖ + ‖Γ2‖)); eauto.
    inversion H0. subst. constructor. 1,2,5: apply splice_qual_closed; auto. 1,2 : apply splice_ty_closed; auto.
    erewrite <- splice_qual_fresh. rewrite <- splice_qual_qor_dist. rewrite subqual_splice_lr'. auto.
    rewrite subqual_splice_lr'; auto.
    eapply senv_saturated_splice; eauto.
    rewrite app_comm_cons.
    replace ((bind_tm, false, T1 ↑ᵀ ‖Γ2‖, d1 ↑ᵈ ‖Γ2‖)
                :: ((bind_tm, true, TFun (d1 ↑ᵈ ‖Γ2‖) (d2 ↑ᵈ ‖Γ2‖) (T1 ↑ᵀ ‖Γ2‖) (T2 ↑ᵀ ‖Γ2‖), df ↑ᵈ ‖Γ2‖)
                      :: (Γ1 ↑ᴳ ‖Γ2‖)) ++ X :: Γ2)
            with ((((bind_tm, false,T1, d1) :: (bind_tm, true, TFun d1 d2 T1 T2, df) :: Γ1) ↑ᴳ ‖Γ2‖) ++ X :: Γ2).
    replace ((df ↑ᵈ ‖Γ2‖) ⊔ $!(‖(Γ1 ↑ᴳ ‖Γ2‖) ++ X :: Γ2‖) ⊔ $!(S (‖(Γ1 ↑ᴳ ‖Γ2‖) ++ X :: Γ2‖)))
      with  ((df ⊔ $!(‖Γ1‖ + ‖Γ2‖) ⊔ $!(S (‖Γ1‖ + ‖Γ2‖))) ↑ᵈ ‖Γ2‖).
    rewrite <- splice_open'. rewrite <- splice_ty_open'. rewrite <- splice_qual_open'.
    rewrite @open_tm'_len with (Γ':=(Γ1 ++ Γ2)). rewrite @open_ty'_len with (Γ':=(Γ1 ++ Γ2)).
    rewrite @openq'_len with (Γ':=(Γ1 ++ Γ2)).
    apply IHHT; intuition. 1-4 : repeat rewrite app_length; rewrite splice_env_length; auto.
    repeat rewrite splice_qual_lub_dist. simpl.
    repeat rewrite <- plus_n_Sm. repeat f_equal; unfold_q; rewrite n_splice_one_S; try lia; repeat f_equal; lia.
    simpl. auto.
  - (* t_app *) simpl. rewrite splice_qual_open''. rewrite splice_ty_open''. rewrite splice_qual_empty. apply t_app with (T1:=T1 ↑ᵀ ‖Γ2‖) (df:=df ↑ᵈ ‖Γ2‖).
    apply IHHT1; auto. apply IHHT2; auto.
    specialize (@splice_qual_lub_dist φ ({♦}) (‖ Γ2 ‖)) as Hdist. rewrite splice_qual_fresh in Hdist.
    rewrite <- Hdist. rewrite <- @splice_qual_empty with (k := ‖Γ2‖); rewrite <- splice_qual_open''.
    rewrite subqual_splice_lr'; auto. rewrite <- not_fresh_splice_iff. auto.
    rewrite <- not_free_splice_ty_iff. auto.
    replace ((d2 ↑ᵈ (‖ Γ2 ‖)) <~ᵈ ∅; ∅) with ((d2 <~ᵈ ∅; ∅) ↑ᵈ (‖ Γ2 ‖)); auto.
    eapply senv_saturated_splice; eauto.
    rewrite splice_qual_open''.
f_equal; auto.
  - (* t_app_fresh *) simpl. rewrite splice_qual_open''. rewrite splice_ty_open''. rewrite splice_qual_empty.
    apply t_app_fresh with (T1:=T1 ↑ᵀ ‖Γ2‖) (d1:=d1 ↑ᵈ ‖Γ2‖) (df:=df ↑ᵈ ‖Γ2‖); auto.
    replace (TFun
     (q_trans (Γ1 ↑ᴳ (‖ Γ2 ‖) ++ X :: Γ2) Σ (df ↑ᵈ (‖ Γ2 ‖))
      ⋒ q_trans (Γ1 ↑ᴳ (‖ Γ2 ‖) ++ X :: Γ2) Σ (d1 ↑ᵈ (‖ Γ2 ‖)))
     (d2 ↑ᵈ (‖ Γ2 ‖)) (T1 ↑ᵀ (‖ Γ2 ‖)) (T2 ↑ᵀ (‖ Γ2 ‖)))
     with ((TFun (q_trans (Γ1 ++ Γ2) Σ df ⋒ q_trans (Γ1 ++ Γ2) Σ d1) d2 T1 T2) ↑ᵀ (‖ Γ2 ‖)). auto.
    simpl. rewrite splice_qual_qor_dist. rewrite splice_qual_fresh. rewrite splice_qual_glb_dist. f_equal.
unfold q_trans. erewrite <- wf_tenv_splice_lower_id' with (Γ1:=(Γ1 ↑ᴳ (‖ Γ2 ‖))) (n:=(‖ Γ2 ‖)) (d:=(df ↑ᵈ (‖ Γ2 ‖))); eauto. erewrite <- wf_tenv_splice_lower_id' with (Γ1:=(Γ1 ↑ᴳ (‖ Γ2 ‖))) (n:=(‖ Γ2 ‖)) (d:=(d1 ↑ᵈ (‖ Γ2 ‖))); eauto.
repeat rewrite splice_q_trans_tenv_comm. repeat rewrite <- splice_q_trans_senv_comm. replace ((Σ ↑ᴳ (‖ Γ2 ‖))) with Σ. auto.
rewrite wf_senv_splice_id; auto.
    intros Hfresh. rewrite <- fresh_splice_iff in Hfresh. rewrite <- not_free_splice_ty_iff. auto.
    rewrite <- not_free_splice_ty_iff. auto.
    rewrite <- @splice_qual_empty with (k := ‖Γ2‖); rewrite <- splice_qual_open''.
    erewrite <- splice_qual_fresh. rewrite <- splice_qual_qor_dist. rewrite subqual_splice_lr'; auto.
    unfold q_trans. erewrite <- wf_tenv_splice_lower_id' with (Γ1:=(Γ1 ↑ᴳ (‖ Γ2 ‖))) (n:=(‖ Γ2 ‖)) (d:=(df ↑ᵈ (‖ Γ2 ‖))); eauto. erewrite <- wf_tenv_splice_lower_id' with (Γ1:=(Γ1 ↑ᴳ (‖ Γ2 ‖))) (n:=(‖ Γ2 ‖)) (d:=(d1 ↑ᵈ (‖ Γ2 ‖))); eauto. repeat rewrite splice_q_trans_tenv_comm. erewrite <- wf_senv_splice_id with (Σ:=Σ); auto. repeat rewrite splice_q_trans_senv_comm. rewrite <- splice_qual_qand_dist. erewrite <- splice_qual_fresh. rewrite <- splice_qual_qor_dist. rewrite <- splice_qual_qor_dist. apply subqual_splice_lr'. auto.
    erewrite <- splice_qual_empty. rewrite <- splice_qual_open''.
    eapply senv_saturated_splice; eauto.
  - (* t_loc *) simpl. rewrite splice_qual_qor_dist. replace (&! l ↑ᵈ (‖ Γ2 ‖)) with (&! l). apply t_loc. eapply splice_qual_closed'.
    rewrite app_length in *. unfold splice_tenv. erewrite splice_env_length; eauto. auto.
    erewrite splice_ty_id; eauto. erewrite splice_qual_id; eauto. eapply closed_qual_monotone; eauto. lia. eapply closed_ty_monotone; eauto. lia.
    erewrite splice_ty_id; eauto. eapply closed_ty_monotone; eauto. lia.
    erewrite splice_qual_id; eauto. eapply closed_qual_monotone; eauto. lia.
    Qcrush.
    eapply senv_saturated_splice; eauto.
    1-2: Qcrush. apply Q_lift_eq. Qcrush.
  - (* t_ref *) simpl in *. specialize (IHHT wfs Γ2 wft Γ1). intuition. remember (a, b1, b0, b) as X.
    specialize (H1 X).
    rewrite splice_qual_qor_dist. rewrite splice_qual_fresh. apply t_ref; auto.
    apply has_type_closed in H1. intuition.
  - (* t_deref *) simpl. econstructor; eauto. apply subqual_splice_lr'. auto.
  - (* t_assign *) simpl. specialize (IHHT1 wfs Γ2 wft Γ1). specialize (IHHT2 wfs Γ2 wft Γ1). intuition.
    remember (a, b1, b0, b) as X.
    specialize (H0 X). specialize (H1 X). simpl in *. rewrite splice_qual_empty. eapply t_assign; eauto.
  - (* t_sub *) eapply t_sub. eapply IHHT; auto.
    apply @weaken_stp_gen; eauto; lia.
    specialize (@splice_qual_lub_dist φ ({♦}) (‖ Γ2 ‖)) as Hdist. rewrite splice_qual_fresh in Hdist.
    rewrite <- Hdist. apply subqual_splice_lr'. auto.
    eapply senv_saturated_splice; eauto.
Qed.

Lemma weaken_flt : forall {Γ φ Σ t T d},
    has_type Γ φ Σ t T d ->
    forall {φ'}, φ ⊑↑ φ' -> closed_Qual 0 (‖Γ‖) (‖Σ‖) φ'↑ ->
    has_type Γ φ' Σ t T d.
  intros Γ φ Σ t T d HT.
  induction HT; intros.
  1,4-6,9-12: try solve [econstructor; eauto using Subq_trans].
  - assert (φ ⊔ {♦} ⊑↑ φ' ⊔ {♦}). eapply Subq_qor; eauto.
    econstructor; eauto. eapply Subq_trans; eauto. eauto using Subq_trans.
  - assert (φ ⊔ {♦} ⊑↑ φ' ⊔ {♦}). eapply Subq_qor; eauto.
    eapply t_tapp_fresh; eauto. eapply Subq_trans; eauto.
    Qcrush. Qcrush.
  - assert (φ ⊔ {♦} ⊑↑ φ' ⊔ {♦}). eapply Subq_qor; eauto.
    econstructor; eauto. eapply Subq_trans; eauto.
  - assert (φ ⊔ {♦} ⊑↑ φ' ⊔ {♦}). eapply Subq_qor; eauto.
    eapply t_app_fresh; eauto. eapply Subq_trans; eauto.
    Qcrush.
  - econstructor; eauto. assert (φ ⊔ {♦} ⊑↑ φ' ⊔ {♦}). eapply Subq_qor; eauto.
    eapply Subq_trans; eauto.
Qed.

Lemma weaken : forall {φ Σ t T d},
    wf_senv Σ ->
    has_type [] φ Σ t T d -> forall {Γ},
    wf_tenv Γ Σ ->
    has_type Γ φ Σ t T d.
  intros φ Σ t T d wfs HT Γ wft. induction Γ; auto.
  specialize (@weaken_gen t [] Γ φ Σ T d) as Hsp. simpl in *.
apply wf_tenv_shrink in wft as wft'. intuition. rename H0 into Hsp.
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
  wf_senv Σ -> has_type [] φ Σ t T d -> forall {φ'}, φ ⊑↑ φ' -> forall {Γ}, wf_tenv Γ Σ -> closed_Qual 0 (‖Γ‖) (‖Σ‖) φ'↑ -> has_type Γ φ' Σ t T d.
  intros. eapply weaken_flt; eauto. apply weaken; auto.
Qed.

Lemma weaken_store : forall {Γ φ Σ t T d}, has_type Γ φ Σ t T d -> forall {Σ'}, Σ' ⊇ Σ -> closed_qenv 0 (‖ Γ ‖) (‖ Σ ‖) Γ -> closed_qenv_qn (‖ Σ ‖) Σ -> has_type Γ φ Σ' t T d.
Proof.  intros Γ φ Σ t T d HT. induction HT; intros; intuition.
    - econstructor; eauto using closed_tm_monotone, closed_ty_monotone, closed_Qual_monotone, extends_length, weaken_store_senv_saturated. apply IHHT; auto. simpl. apply closed_qenv_extend; auto. apply closed_qenv_extend; auto. eapply closed_qenv_monotone; eauto. Qcrush. inversion H0. Qcrush.
    - apply has_type_closed in HT as Hcl. eapply t_tapp; eauto using closed_tm_monotone, closed_ty_monotone, closed_Qual_monotone, extends_length; eapply weaken_store_senv_saturated; eauto; intuition; eapply closed_Qual_monotone; eauto. inversion H11. subst. apply closed_Qual_open2; eauto.
    - eapply t_tapp_fresh; eauto using closed_tm_monotone, closed_ty_monotone, closed_Qual_monotone, extends_length.
    apply has_type_closed in HT. intuition. unfold q_trans,q_trans_senv in *.
    erewrite q_trans''_extend_closed_id with (q:=(q_trans_tenv Γ df)); eauto.
    erewrite q_trans''_extend_closed_id with (q:=(q_trans_tenv Γ d1)); eauto.
    repeat rewrite @q_trans''_fuel_max with (fuel:=(‖ Σ' ‖)); auto.
    pose proof closed_qenv_q_trans''_monotone Γ d1 0 (‖ Γ ‖) (‖ Σ ‖) as Hcl. apply Hcl; auto.
    pose proof closed_qenv_q_trans''_monotone Γ df 0 (‖ Γ ‖) (‖ Σ ‖) as Hcl. apply Hcl; auto.
    eapply weaken_store_senv_saturated; eauto.
    unfold q_trans,q_trans_senv in *.
    erewrite q_trans''_extend_closed_id with (q:=(q_trans_tenv Γ df)); eauto.
    erewrite q_trans''_extend_closed_id with (q:=(q_trans_tenv Γ d1)); eauto.
    apply extends_length in H8.
    repeat rewrite @q_trans''_fuel_max with (fuel:=(‖ Σ' ‖)); auto.
    eapply closed_qenv_q_trans''_monotone; eauto.
    eapply closed_qenv_q_trans''_monotone; eauto.
    eapply has_type_closed; eauto.
    eapply weaken_store_senv_saturated; eauto. eapply closed_Qual_open2; eauto. apply has_type_closed in HT as Hcl. intuition. inversion H12. eapply closed_Qual_monotone; eauto.
    - econstructor; eauto using closed_Qual_monotone.
    - econstructor; eauto using closed_ty_monotone, closed_Qual_monotone.
    - econstructor; eauto using closed_tm_monotone, closed_ty_monotone, closed_Qual_monotone, extends_length, weaken_store_senv_saturated. apply IHHT; auto. simpl. apply closed_qenv_extend; auto. apply closed_qenv_extend; auto. eapply closed_qenv_monotone; eauto. Qcrush. inversion H0. Qcrush.
    - apply has_type_closed in HT1 as Hcl. eapply t_app; eauto using closed_tm_monotone, closed_ty_monotone, closed_Qual_monotone, extends_length; eapply weaken_store_senv_saturated; eauto; intuition; eapply closed_Qual_monotone; eauto.
      inversion H7. subst. apply closed_Qual_open2; eauto.
    - eapply t_app_fresh; eauto.
    apply has_type_closed in HT1, HT2. intuition. unfold q_trans,q_trans_senv in *.
    erewrite q_trans''_extend_closed_id with (q:=(q_trans_tenv Γ df)); eauto.
    erewrite q_trans''_extend_closed_id with (q:=(q_trans_tenv Γ d1)); eauto.
    repeat rewrite @q_trans''_fuel_max with (fuel:=(‖ Σ' ‖)); auto.
    pose proof closed_qenv_q_trans''_monotone Γ d1 0 (‖ Γ ‖) (‖ Σ ‖) as Hcl. apply Hcl; auto.
    pose proof closed_qenv_q_trans''_monotone Γ df 0 (‖ Γ ‖) (‖ Σ ‖) as Hcl. apply Hcl; auto.
    unfold q_trans,q_trans_senv in *.
    erewrite q_trans''_extend_closed_id with (q:=(q_trans_tenv Γ df)); eauto.
    erewrite q_trans''_extend_closed_id with (q:=(q_trans_tenv Γ d1)); eauto.
    apply extends_length in H4.
    repeat rewrite @q_trans''_fuel_max with (fuel:=(‖ Σ' ‖)); auto.
    eapply closed_qenv_q_trans''_monotone; eauto. eapply has_type_closed; eauto.
    eapply closed_qenv_q_trans''_monotone; eauto. eapply has_type_closed; eauto.
    eapply weaken_store_senv_saturated; eauto.
    eapply closed_Qual_open2; eauto. apply has_type_closed in HT1 as Hcl. intuition. inversion H8. eapply closed_Qual_monotone; eauto.
  - econstructor; eauto using closed_Qual_monotone.
    unfold extends in H7. destruct H7. rewrite H7.
    rewrite indexr_skips. auto. eapply indexr_var_some'. eauto.
    assert (‖ Σ' ‖ >= ‖ Σ ‖). { auto. } eapply closed_ty_monotone; eauto.
    eapply weaken_store_senv_saturated; eauto.
  - econstructor; eauto. eapply closed_ty_monotone; eauto.
  - apply has_type_closed in HT as Hcl. econstructor; eauto.
    eapply weaken_store_senv_saturated; eauto. specialize (IHHT Σ'). intuition. eapply closed_Qual_monotone; eauto.
  - econstructor; eauto.
  - econstructor; eauto. eapply weaken_stp_store_ext; eauto. eapply weaken_store_senv_saturated; eauto.
    apply stp_closed in H. intuition. eapply closed_Qual_monotone; eauto.
Qed.

Lemma q_trans_one_narrowing_subq : forall Γ1 Γ2 d1 d2 bd b U du V dv,
  dv ⊑↑ du ->
  d1 ⊑↑ d2 ->
  q_trans_one (Γ1 ++ (bd, b, V, dv) :: Γ2) d1 ⊑↑ q_trans_one (Γ1 ++ (bd, b, U, du) :: Γ2) d2.
intros. repeat rewrite Q_lift_trans_one. unfold Subq, N_sub,Q_trans_one, N_trans_one. intuition; unfold_q.
  - intuition. left. Qcrush. right. Ex. exists x. intuition. Qcrush. bdestruct (x =? (‖ Γ2 ‖)). subst. rewrite indexr_insert in H3. inversion H3. subst. exists (bd, b, U, du). intuition. apply indexr_insert. Qcrush. exists x0. intuition. bdestruct (x <? (‖ Γ2 ‖)). rewrite <- indexr_insert_lt; auto. rewrite <- indexr_insert_lt in H3; auto. assert (x > (‖ Γ2 ‖)) by lia. destruct x. lia. rewrite <- indexr_insert_ge; intuition. rewrite <- indexr_insert_ge in H3; intuition.
  - intuition. left. Qcrush. right. Ex. exists x0. intuition. Qcrush. bdestruct (x0 =? (‖ Γ2 ‖)). subst. rewrite indexr_insert in H3. inversion H3. subst. exists (bd, b, U, du). intuition. apply indexr_insert. Qcrush. exists x1. intuition. bdestruct (x0 <? (‖ Γ2 ‖)). rewrite <- indexr_insert_lt; auto. rewrite <- indexr_insert_lt in H3; auto. assert (x0 > (‖ Γ2 ‖)) by lia. destruct x0. lia. rewrite <- indexr_insert_ge; intuition. rewrite <- indexr_insert_ge in H3; intuition.
  - intuition. left. Qcrush. right. Ex. exists x0. intuition. Qcrush. bdestruct (x0 =? (‖ Γ2 ‖)). subst. rewrite indexr_insert in H3. inversion H3. subst. exists (bd, b, U, du). intuition. apply indexr_insert. Qcrush. exists x1. intuition. bdestruct (x0 <? (‖ Γ2 ‖)). rewrite <- indexr_insert_lt; auto. rewrite <- indexr_insert_lt in H3; auto. assert (x0 > (‖ Γ2 ‖)) by lia. destruct x0. lia. rewrite <- indexr_insert_ge; intuition. rewrite <- indexr_insert_ge in H3; intuition.
  - intuition. left. Qcrush. right. Ex. exists x0. intuition. Qcrush. bdestruct (x0 =? (‖ Γ2 ‖)). subst. rewrite indexr_insert in H3. inversion H3. subst. exists (bd, b, U, du). intuition. apply indexr_insert. Qcrush. exists x1. intuition. bdestruct (x0 <? (‖ Γ2 ‖)). rewrite <- indexr_insert_lt; auto. rewrite <- indexr_insert_lt in H3; auto. assert (x0 > (‖ Γ2 ‖)) by lia. destruct x0. lia. rewrite <- indexr_insert_ge; intuition. rewrite <- indexr_insert_ge in H3; intuition.
Qed.

Lemma q_trans_tenv_narrowing_subq : forall Γ1 Γ2 d1 d2 bd b U du V dv fuel,
  dv ⊑↑ du ->
  d1 ⊑↑ d2 ->
  (q_trans'' (Γ1 ++ (bd, b, V, dv) :: Γ2) d1 fuel) ⊑↑ (q_trans'' (Γ1 ++ (bd, b, U, du) :: Γ2) d2 fuel).
intros. repeat rewrite Q_lift_trans''. generalize dependent d2. generalize dependent d1. induction fuel; intros. repeat rewrite <- Q_lift_trans''. simpl. auto.
repeat rewrite <- Q_lift_trans''. simpl. repeat rewrite Q_lift_trans''. apply IHfuel. apply q_trans_one_narrowing_subq; auto.
Qed.

Lemma q_trans_narrowing_subq : forall Σ Γ1 Γ2 d1 d2 bd b U du V dv,
  dv ⊑↑ du ->
  d1 ⊑↑ d2 ->
  (q_trans (Γ1 ++ (bd, b, V, dv) :: Γ2) Σ d1) ⊑↑ (q_trans (Γ1 ++ (bd, b, U, du) :: Γ2) Σ d2).
intros. qual_destruct d1. qual_destruct d2. unfold q_trans,q_trans_senv,q_trans_tenv. apply q_trans''_subq; auto. replace (‖ Γ1 ++ (bd, b, V, dv) :: Γ2 ‖) with (‖ Γ1 ++ (bd, b, U, du) :: Γ2 ‖). apply q_trans_tenv_narrowing_subq; auto. repeat rewrite app_length. simpl. auto.
Qed.
#[global] Hint Resolve q_trans_narrowing_subq : core.

Lemma narrowing_gen : forall {t Γ1 bd b U du Γ2 φ Σ T d},
    has_type (Γ1 ++ (bd, b,U,du) :: Γ2) φ Σ t T d -> (b = true -> (♦∈ du)) ->
    forall {V dv}, stp [] Σ V dv U du -> dv ⊑↑ du -> wf_senv Σ -> has_type (Γ1 ++ (bd, b,V,dv) :: Γ2) φ Σ t T d.
Proof. intros t Γ1 bd b U du Γ2 φ Σ T d HT Hb. remember (Γ1 ++ (bd, b, U, du) :: Γ2) as Γ.
  generalize dependent Γ1. generalize dependent U. generalize dependent du. generalize dependent Γ2.
  induction HT; intros; subst.
  - repeat rewrite app_length in *; simpl in *; auto.
    constructor; auto. 1-3 : rewrite app_length in *; simpl in *; auto.
    rewrite @open_tm'_len with (Γ' := (Γ1 ++ (bd, b,U, du) :: Γ2)).
    rewrite @open_ty'_len with (Γ' := (Γ1 ++ (bd, b,U, du) :: Γ2)).
    rewrite @openq'_len with (Γ' := (Γ1 ++ (bd, b,U, du) :: Γ2)).
    2-4 : repeat rewrite app_length; simpl; auto.
    rewrite app_length. simpl.
    rewrite app_comm_cons. rewrite app_comm_cons.
    eapply IHHT; eauto. simpl. auto.
  - econstructor; eauto. all : rewrite app_length in *; simpl in *; auto.
  - eapply t_tapp_fresh; eauto.
    apply has_type_filter in HT as Hft.
    apply t_sub with (T1:=(TAll
     (q_trans (Γ1 ++ (bd, b, U, du) :: Γ2) Σ df
      ⋒ q_trans (Γ1 ++ (bd, b, U, du) :: Γ2) Σ d1) d2 T1 T2)) (d1:=df); auto.
    eapply IHHT; eauto.
    apply has_type_closed in HT. intuition. inversion H12. subst. constructor. 1,2,3: constructor; auto. 1-9: repeat rewrite app_length in *; simpl in *; auto; intuition. apply closed_Qual_qor; auto. assert (closed_Qual 0 (‖ Γ1 ‖ + S (‖ Γ2 ‖)) (‖ Σ ‖) (q_trans (Γ1 ++ (bd, b, U, du) :: Γ2) Σ df ⊓ q_trans (Γ1 ++ (bd, b, U, du) :: Γ2) Σ d1) ↑). Qcrush. eapply @closed_Qual_subq_and with (d1':=q_trans (Γ1 ++ (bd, b, U, du) :: Γ2) Σ df) (d2':=q_trans (Γ1 ++ (bd, b, U, du) :: Γ2) Σ d1); eauto.
    {
      destruct bd.
      + apply @narrowing_stp_gen with (U:=U) (du:=du); eauto.
        apply stp_refl; auto. constructor; auto. apply Subq_qor. apply Subq_qand_split. 1,2: apply q_trans_narrowing_subq; auto.
        replace (Γ2) with (Γ2 ++ []) by intuition. apply weaken_stp'; eauto.
      + apply @narrowing_stp_ty_gen with (U:=U) (du:=du); eauto.
        apply stp_refl; auto. constructor; auto. apply Subq_qor. apply Subq_qand_split. 1,2: apply q_trans_narrowing_subq; auto.
        1,2: eapply stp_closed in H8; intuition.
        replace (Γ2) with (Γ2 ++ []) by intuition. apply weaken_stp'; eauto.
    }
    eapply stp_refl. simpl.
    apply closed_ty_open2; simpl; repeat rewrite app_length; simpl; auto.
    eapply closed_ty_monotone; eauto. repeat rewrite app_length. simpl. lia.
    1,2: apply Q_lift_closed; Qcrush.
    apply qstp_refl. simpl.
    apply closed_Qual_open2; simpl; repeat rewrite app_length; simpl; auto.
    eapply closed_Qual_monotone; eauto. repeat rewrite app_length. simpl. lia.
    1-2: Qcrush.
    eapply has_type_senv_saturated; eauto.
    eapply closed_ty_monotone; eauto. repeat rewrite app_length. simpl. lia.
    eapply closed_Qual_monotone; eauto. repeat rewrite app_length. simpl. lia.
    eapply @Subq_trans with (d2:=(q_trans (Γ1 ++ (bd, b, U, du) :: Γ2) Σ d1 ⋒ q_trans (Γ1 ++ (bd, b, U, du) :: Γ2) Σ df)); auto. apply Subq_qor. apply Subq_qand_split.
    1,2: apply q_trans_narrowing_subq; eauto using has_type_filter.
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
      Qcrush.
    * apply t_var with (b:=b0) (d:=d); auto. destruct x. lia. rewrite <- indexr_insert_ge; try lia.
      rewrite <- indexr_insert_ge in H; try lia. auto.
      repeat rewrite app_length in *; simpl in *; auto.
  - repeat rewrite app_length in *; simpl in *; auto.
    constructor; auto. 1-3 : rewrite app_length in *; simpl in *; auto.
    rewrite @open_tm'_len with (Γ' := (Γ1 ++ (bd, b,U, du) :: Γ2)).
    rewrite @open_ty'_len with (Γ' := (Γ1 ++ (bd, b,U, du) :: Γ2)).
    rewrite @openq'_len with (Γ' := (Γ1 ++ (bd, b,U, du) :: Γ2)).
    2-4 : repeat rewrite app_length; simpl; auto.
    rewrite app_length. simpl.
    rewrite app_comm_cons. rewrite app_comm_cons.
    eapply IHHT; eauto. simpl. auto.
  - econstructor; eauto.
  - eapply t_app_fresh; eauto.
    apply has_type_filter in HT1 as Hft.
    apply t_sub with (T1:=(TFun
     (q_trans (Γ1 ++ (bd, b, U, du) :: Γ2) Σ df
      ⋒ q_trans (Γ1 ++ (bd, b, U, du) :: Γ2) Σ d1) d2 T1 T2)) (d1:=df); auto.
    eapply IHHT1; eauto.
    apply has_type_closed in HT1, HT2. intuition. inversion H12. subst. constructor. 1,2,3: constructor; auto. 1-9: repeat rewrite app_length in *; simpl in *; auto; intuition. apply closed_Qual_qor; auto. assert (closed_Qual 0 (‖ Γ1 ‖ + S (‖ Γ2 ‖)) (‖ Σ ‖) (q_trans (Γ1 ++ (bd, b, U, du) :: Γ2) Σ df ⊓ q_trans (Γ1 ++ (bd, b, U, du) :: Γ2) Σ d1) ↑). Qcrush. eapply @closed_Qual_subq_and with (d1':=q_trans (Γ1 ++ (bd, b, U, du) :: Γ2) Σ df) (d2':=q_trans (Γ1 ++ (bd, b, U, du) :: Γ2) Σ d1); eauto.
    {
      destruct bd.
      + apply @narrowing_stp_gen with (U:=U) (du:=du); eauto.
        apply stp_refl; auto. constructor; auto. apply Subq_qor. apply Subq_qand_split. 1,2: apply q_trans_narrowing_subq; auto.
        replace (Γ2) with (Γ2 ++ []) by intuition. apply weaken_stp'; eauto.
      + apply @narrowing_stp_ty_gen with (U:=U) (du:=du); eauto.
        apply stp_refl; auto. constructor; auto. apply Subq_qor. apply Subq_qand_split. 1,2: apply q_trans_narrowing_subq; auto.
        1,2: eapply stp_closed in H4; intuition.
        replace (Γ2) with (Γ2 ++ []) by intuition. apply weaken_stp'; eauto.
    }
    eapply stp_refl. simpl.
    apply closed_ty_open2; simpl; repeat rewrite app_length; simpl; auto.
    eapply closed_ty_monotone; eauto. repeat rewrite app_length. simpl. lia.
    1,2: apply Q_lift_closed; Qcrush.
    apply qstp_refl. simpl.
    apply closed_Qual_open2; simpl; repeat rewrite app_length; simpl; auto.
    eapply closed_Qual_monotone; eauto. repeat rewrite app_length. simpl. lia.
    1,2: Qcrush.
    eapply has_type_senv_saturated; eauto.
    eapply @Subq_trans with (d2:=(q_trans (Γ1 ++ (bd, b, U, du) :: Γ2) Σ d1 ⋒ q_trans (Γ1 ++ (bd, b, U, du) :: Γ2) Σ df)); auto. apply Subq_qor. apply Subq_qand_split.
    1,2: apply q_trans_narrowing_subq; eauto using has_type_filter.
  - econstructor; eauto. repeat rewrite app_length in *; simpl in *; auto.
  - econstructor; eauto. repeat rewrite app_length in *; simpl in *; auto.
  - econstructor; eauto.
  - econstructor; eauto.
  - eapply t_sub; eauto.
    {
      destruct bd.
      + eapply narrowing_stp_gen; eauto. replace (Γ2) with (Γ2 ++ []). eapply weaken_stp'; eauto. rewrite app_nil_r. auto.
      + eapply narrowing_stp_ty_gen; eauto. 1,2: eapply stp_closed in H2; intuition.
        replace (Γ2) with (Γ2 ++ []). eapply weaken_stp'; eauto. rewrite app_nil_r. auto.
    }
Qed.

Lemma narrowing : forall {Γ bd b U du φ Σ t T d}, has_type ((bd, b,U,du) :: Γ) φ Σ t T d -> (b = true -> (♦∈ du)) -> forall {V dv}, stp [] Σ V dv U du -> dv ⊑↑ du -> wf_senv Σ -> has_type ((bd, b,V,dv) :: Γ) φ Σ t T d.
  intros. specialize (@narrowing_gen t [] bd b U du Γ φ Σ T d) as narrow. simpl in *. eapply narrow; eauto.
Qed.

Lemma values_stuck : forall {v}, value v -> forall {t σ σ'}, step v σ t σ' -> False.
  intros. inversion H0; subst; inversion H.
Qed.

Lemma qmem_plus_decomp : forall {x0 q x}, x0 ∈ₗ q ⊔ &!x -> closed_Qual 0 0 x q↑ -> x0 ∈ₗ q \/ x0 = x.
  intros. assert (x0 ∈ₗ q \/ x0 ∈ₗ &! x); Qcrush.
Qed.

Lemma closed_Qual_subq_qdom : forall q (Σ: senv),
  closed_Qual 0 0 (‖ Σ ‖) q ↑ ->
  q ⊑↑ (qdom Σ).
intros. unfold qdom. Qcrush; eauto.
Qed.

Lemma CtxOK_weaken' : forall {Σ σ T t d φ},
    CtxOK [] φ Σ σ ->
    value t ->
    has_type [] φ Σ t T d ->
    wf_senv Σ ->
    CtxOK [] (φ ⊔ &! (‖ σ ‖)) ((T, d) :: Σ) (Some t :: σ).
Proof.
  intros. unfold CtxOK in *. destruct H, H3, H4.
  split. 2: split. 3: split. 4: intros.
  clear - H H3. Qcrush. unfold N_lift, n_dom' in *. apply andb_true_iff in H0.
  destruct H0. apply Nat.ltb_lt in H0. simpl in *. lia. Qcrush.
  clear - H H3 H4. Qcrush; unfold N_lift in *. eapply H1. apply H9. eapply H5. apply H9.
  apply H8 in H9. clear - H9. unfold n_dom' in *. apply andb_true_iff in H9. destruct H9.
  apply Nat.ltb_lt in H. rewrite indexr_skip. 2: lia. rewrite H0.
  replace (x <? ‖ Some t :: σ ‖) with true. auto. symmetry. apply Nat.ltb_lt. simpl. lia.
  unfold n_dom'. subst. rewrite indexr_head. simpl. replace (‖ σ ‖ <? S (‖ σ ‖)) with true.
  auto. symmetry. apply Nat.ltb_lt. lia.
  apply qmem_plus_decomp in H6.
  2: { rewrite H3. eapply closed_Qual_sub. apply closed_Qual_qdom. Qcrush. }
  destruct H6. assert (l < ‖ Σ ‖). Qcrush. rewrite indexr_skip in H7. rewrite indexr_skip in H8.
  2-3: lia. eapply H5 in H6. 2-3: eauto. intuition. eapply weaken_flt. eapply weaken_store.
  1-2: eauto. apply closed_qenv_empty. apply []. eauto. eauto.
  apply closed_Qual_qor; eauto. rewrite H3. Qcrush.
  subst. rewrite H3 in H7. rewrite indexr_head in H8. rewrite indexr_head in H7.
  inversion H7. inversion H8. subst. intuition.
  eapply weaken_flt. eapply weaken_store. 1-2: eauto. apply closed_qenv_empty. apply []. eauto. eauto.
  apply closed_Qual_qor; eauto. rewrite H3. Qcrush.
Qed.

Lemma qdom_cons_qor: forall a (Σ : senv),
  (qdom (a :: Σ)) = (qdom Σ ⊔ &! (‖ Σ ‖)).
intros. apply Q_lift_eq. rewrite Q_lift_or. repeat rewrite Q_lift_qdom. Qcrush; simpl in *. lia. lia. bdestruct (x =? (‖ Σ ‖)); intuition.
Qed.

Lemma CtxOK_weaken'' : forall {Σ σ T t d φ},
  CtxOK [] (qdom Σ) Σ σ ->
  value t ->
  has_type [] φ Σ t T d ->
  wf_senv Σ ->
  CtxOK [] (qdom ((T, d) :: Σ)) ((T, d) :: Σ) (Some t :: σ).
Proof.
  intros. replace (qdom ((T, d) :: Σ)) with (qdom Σ ⊔ &! (‖ σ ‖)). eapply CtxOK_weaken'; eauto. eapply @weaken_flt with (φ:=φ); eauto. apply has_type_closed in H1. intuition. apply closed_Qual_subq_qdom; auto. rewrite qdom_cons_qor. inversion H. intuition. rewrite H5. auto.
Qed.

Lemma update_preserve_qdom : forall {σ : store} {l v}, l ∈ₗ (qdom' σ) -> qdom' σ = qdom' (update σ l (Some v)).
Proof.
  intros. unfold qdom' in *. f_equal. unfold n_dom' in *. rewrite <- update_length.
  simpl in *. unfold N_lift in *. apply andb_true_iff in H. destruct H.
  destruct (indexr l σ) eqn:?. destruct o. all: intuition.
  apply FunctionalExtensionality.functional_extensionality. intro.
  bdestruct (x <? ‖ σ ‖); simpl; auto.
  bdestruct (x =? l). subst. rewrite update_indexr_hit. rewrite Heqo. auto. auto.
  rewrite update_indexr_miss. auto. auto.
Qed.

Lemma CtxOK_update : forall {Γ φ Σ σ},
  CtxOK Γ φ Σ σ ->
  forall {l T q}, l < ‖σ‖ -> indexr l Σ = Some (T,q) -> l ∈ₗ (qdom' σ) ->
  forall {v}, has_type Γ φ Σ v T q -> value v -> CtxOK Γ φ Σ (update σ l (Some v)).
Proof.
  intros. unfold CtxOK in *. destruct H as [Hlen [Hphi Hprev]].
  split. rewrite <- update_preserve_qdom. auto. auto.
  split. rewrite <- update_length. lia. split. rewrite <- update_preserve_qdom.
  intuition. intuition.
  intros. destruct (Nat.eqb l l0) eqn:Heq.
  - apply Nat.eqb_eq in Heq. subst.
    apply (@update_indexr_hit _ σ l0 (Some v)) in H0. rewrite H0 in H6. inversion H6. subst.
    rewrite H5 in H1. inversion H1. subst. auto.
  - apply Nat.eqb_neq in Heq. apply (@update_indexr_miss _ σ l (Some v) l0) in Heq.
    rewrite Heq in H6. eapply Hprev; eauto.
Qed.

Lemma subst1_env_length : forall {p : Type} `{substitutable_env p} (E : env p) {v T q}, ‖ { v |-> T ~ q }ᴳ E ‖ = ‖E‖.
  intros. unfold subst_env. rewrite map_length. auto.
Qed.

Lemma closed_qual_subst1'' : forall {q b f l},
    closed_Qual b (S f) l q ↑ ->
    forall {d1 l1}, closed_Qual b f l1 d1 ↑ ->
    forall{l2},
      l <= l2 -> l1 <= l2 ->
      closed_Qual b f l2 (subst_qual q 0 d1) ↑.
Proof.
  intros. qual_destruct q. unfold_q.
  ndestruct (fvs 0); Qcrush; try solve [eauto using Arith_prebase.lt_S_n, Nat.lt_le_trans]; try solve [exfalso; eauto 3].
Qed.

Lemma subst_qual_subqual_monotone' : forall {d1 d2}, d1 ⊑↑ d2 -> forall {df}, ({0 |-> d1 }ᵈ df) ⊑↑ ({0 |-> d2 }ᵈ df).
intros. qual_destruct df. unfold_q. ndestruct (fvs 0). Qcrush. auto.
Qed.

Lemma closed_qenv_subst1_monotone : forall {p : Type} `{substitutable_env p} (E : env p) (b f l : nat) Tx d1 d2,
  d1 ⊑↑ d2 ->
  closed_qenv b f l ({0 |-> Tx ~ d2 }ᴳ E) ->
  closed_qenv b f l ({0 |-> Tx ~ d1 }ᴳ E).
intros. induction E; simpl; auto. unfold subst_env in *. simpl in *. eapply closed_qenv_shrink in H2 as H2'. eapply closed_qenv_extend; intuition. specialize (H2 (‖ E ‖) (env_subst 0 Tx d2 a)). erewrite <- map_length in H2. rewrite indexr_head in H2. intuition. rewrite <- env_subst_qenv_q_dist in *. apply subst_qual_subqual_monotone' with (df:=(qenv_q a)) in H1. Qcrush.
Qed.

Lemma closed_qenv_subst1 : forall {p : Type} `{substitutable_env p} (E : env p) (b f l : nat) Tx dx,
  closed_qenv b (S f) l E ->
  closed_Qual b f l dx ↑ ->
  closed_qenv b f l ({0 |-> Tx ~ dx }ᴳ E).
intros. induction E; simpl; auto. apply closed_qenv_empty. apply []. apply closed_qenv_extend. apply IHE. eapply closed_qenv_shrink; eauto. rewrite <- env_subst_qenv_q_dist. eapply closed_qual_subst1''; eauto. unfold closed_qenv in H1. specialize (H1 (‖ E ‖) a). rewrite indexr_head in H1. intuition.
Qed.

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
    forall {T1 d1 l1}, closed_ty 0 0 l1 T1 -> closed_Qual 0 0 l1 d1↑ ->
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
  all: eapply closed_qual_subst1; eauto.
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

Lemma indexr_subst1 : forall {x Γ bd b T U d Tx dx},
    x >= 1 ->
    indexr x (Γ ++ [U]) = Some ((bd, b, T, d)) ->
    indexr (pred x) ({ 0 |-> Tx ~ dx }ᴳ Γ) = Some ((bd, b, { 0 |-> Tx ~ dx }ᵀ T, { 0 |-> dx }ᵈ d)).
  intros. destruct x; try lia.
  rewrite <- indexr_insert_ge in H0; simpl; try lia.
  rewrite app_nil_r in H0. induction Γ; intros; simpl in *. discriminate.
  rewrite subst1_env_length. (bdestruct (x =? ‖Γ‖)); auto.
  inversion H0. auto.
Qed.

Lemma indexr_subst1' : forall {x Γ bd b b' T U d du},
    indexr x (Γ ++ [(bd, b, T, d)]) = Some ((bd, b', U, du)) ->
    (x = 0 /\ T = U  /\ d = du /\ b = b' \/
    x >  0  /\ indexr (pred x) ({ 0 |-> T ~ d }ᴳ Γ) = Some ((bd, b', { 0 |-> T ~ d }ᵀ U, { 0 |-> d }ᵈ du))).
Proof.   intros. induction  Γ; intros.
  + simpl  in H. destruct (x =? 0) eqn: Heqn.
    -  inversion H. subst. left.  intuition.  apply Nat.eqb_eq in Heqn. auto.
    -  inversion H.
  + remember (length (Γ ++ [(bd, b, T, d)])) as L.
     destruct (Nat.eqb x L) eqn: Heqn.
    - assert (x = L). eapply Nat.eqb_eq. eauto.
      eapply indexr_hit in H.
      right. split. rewrite app_length in HeqL. simpl in HeqL. lia.
       assert ((pred x) = (‖ ({ 0 |-> T ~  d }ᴳ Γ) ‖)).
       rewrite subst1_env_length. rewrite app_length in HeqL. simpl in HeqL.  lia.
       simpl. eapply Nat.eqb_eq in H1.  subst.
       destruct (pred (length (Γ ++ [(bd, b, T, d)])) =? length ({0 |-> T ~ d }ᴳ Γ)); auto.
       inversion H1.
       subst. eauto.
    - assert (x <> L). eapply Nat.eqb_neq. eauto.
       replace ((a :: Γ) ++ [(bd, b, T, d)]) with  (a :: (Γ ++ [(bd, b, T, d)])) in H.
       rewrite indexr_skip in H. intuition.
       right. split. eauto.
       simpl.
       assert ((pred x) <> ( ‖({ 0 |-> T ~  d }ᴳ Γ)‖)).
       rewrite app_length in HeqL. simpl in HeqL. rewrite subst1_env_length.
       unfold not. intros. subst L.
       unfold not in H0. eapply H0. rewrite <-H2. lia.
       eapply Nat.eqb_neq in H2. rewrite H2.
       eauto. subst. eauto.  intuition.
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
  ndestruct (fvs0 0); simpl;
  ndestruct (fvs 0); simpl; Qcrush.
Qed.

Lemma subst1_just_fv : forall {fr x dy},
    ${fr}x = {0 |-> dy }ᵈ ${fr}(S x).
  intros. apply Q_lift_eq. Qcrush.
Qed.

Lemma closed_qual_subst1' : forall {p : Type} `{substitutable_env p} (E : env p) {X l Tf df φ b},
    closed_ty 0 0 l Tf ->
    closed_Qual 0 0 l df ↑ ->
    closed_Qual b (‖ E ++ [X] ‖) l φ ↑ ->
    closed_Qual b (‖ {0 |-> Tf ~ df }ᴳ E ‖) l ({0 |-> df }ᵈ φ) ↑.
  intros. eapply closed_qual_subst1; eauto. rewrite subst1_env_length.
  rewrite app_length in *. simpl in *. rewrite <- plus_n_Sm in *. rewrite <- plus_n_O in *. auto.
Qed.

Lemma closed_ty_subst1' : forall {p : Type} `{substitutable_env p} (E : env p) {X l Tf df T b},
    closed_ty 0 0 l Tf ->
    closed_Qual 0 0 l df ↑ ->
    closed_ty b (‖ E ++ [X] ‖) l T ->
    closed_ty b (‖ {0 |-> Tf ~ df }ᴳ E ‖) l ({0 |-> Tf ~ df }ᵀ T).
  intros. repeat eapply closed_ty_subst1; eauto. rewrite subst1_env_length.
  rewrite app_length in *. simpl in *. replace (‖E‖ + 1) with (S (‖E‖)) in H0.
  eapply closed_ty_monotone; eauto. lia. lia.
Qed.

Lemma closed_tm_subst1' : forall {p : Type} `{substitutable_env p} (E : env p) {X l Tf df tx t b},
    closed_tm 0 0 l tx ->
    closed_tm b (‖ E ++ [X] ‖) l t ->
    closed_tm b (‖ {0 |-> Tf ~ df }ᴳ E ‖) l ({0 |-> tx }ᵗ t).
  intros. repeat eapply closed_tm_subst1; eauto. rewrite subst1_env_length.
  rewrite app_length in *. simpl in *. rewrite <- plus_n_Sm in *. rewrite <- plus_n_O in *. auto.
Qed.

Lemma subst1_qual_0 : forall {q' q}, q' ⊑↑ q -> forall {df}, $0 ∈ᵥ df -> q' ⊑↑ { 0 |-> q }ᵈ df.
  intros. qual_destruct df. qual_destruct q. qual_destruct q'. unfold_q. unfold N_lift in H0. rewrite H0. simpl. Qcrush.
Qed.

Lemma subst1_just_fv0 : forall {q}, {0 |-> q }ᵈ $!0 = q.
  intros. apply Q_lift_eq. Qcrush.
Qed.

Lemma qenv_saturated_q''_0 : forall {p : Type} `{qenv p} (E : env p) (a : p) q,
  N_lift (qenv_qn q) 0 ->
  qenv_saturated_q'' (E ++ [a]) q ->
  (qenv_q a) ⊑↑ q.
intros. unfold qenv_saturated_q'' in *. induction E; simpl in *.
  - unfold N_lift in H0. rewrite H0 in H1. rewrite <- H1. Qcrush.
  - ndestruct (qenv_qn q (‖ E ++ [a] ‖)); auto.
    apply IHE. pose proof (q_trans_one_subq' (E ++ [a]) q). assert ((q_trans_one (E ++ [a]) q ⊔ qenv_q a0) ⊑↑ q). rewrite H1. auto. apply Q_lift_eq. Qcrush.
Qed.

Lemma subst1_qand_saturated : forall {df d1 bd sx Tx dx dx'} {φ} {Γ : tenv} {Σ : senv},
    dx' ⊓ φ ⊑↑ dx ->
    closed_Qual 0 0 (‖Σ‖) dx'↑ ->
    df ⊑↑ φ -> d1 ⊑↑ φ ->
    qenv_saturated_q'' (Γ ++ [(bd, sx, Tx, dx)]) d1 ->
    qenv_saturated_q'' (Γ ++ [(bd, sx, Tx, dx)]) df ->
    {0 |-> dx' }ᵈ df ⊓ {0 |-> dx' }ᵈ d1 = {0 |-> dx' }ᵈ (df ⊓ d1).
  intros. qual_destruct df. qual_destruct d1.
  unfold_q. ndestruct (fvs 0); ndestruct (fvs0 0); clift.
  - apply Q_lift_eq; Qcrush.
  - (* 0 ∈ df, 0 ∉ d1 *)
    apply qenv_saturated_q''_0 in H4; auto. apply Q_lift_eq; Qcrush.
  - (* 0 ∉ df, 0 ∈ d1, analogous to the previous case *)
    apply qenv_saturated_q''_0 in H3; auto. apply Q_lift_eq; Qcrush.
Qed.

Lemma subst1_qand_saturated' : forall {df d1 bd sx Tx dx dx'} {φ} {Γ : tenv} {Σ : senv},
    dx' ⊓ φ ⊑↑ dx ->
    ♦∉ dx' ->
    closed_Qual 0 0 (‖Σ‖) dx'↑ ->
    df ⊑↑ φ ⊔ {♦} -> d1 ⊑↑ φ ⊔ {♦} ->
    qenv_saturated_q'' (Γ ++ [(bd, sx, Tx, dx)]) d1 ->
    qenv_saturated_q'' (Γ ++ [(bd, sx, Tx, dx)]) df ->
    {0 |-> dx' }ᵈ df ⊓ {0 |-> dx' }ᵈ d1 = {0 |-> dx' }ᵈ (df ⊓ d1).
  intros. qual_destruct df. qual_destruct d1.
  unfold_q. ndestruct (fvs 0); ndestruct (fvs0 0); clift.
  - apply Q_lift_eq; Qcrush.
  - (* 0 ∈ df, 0 ∉ d1 *)
    apply qenv_saturated_q''_0 in H5; auto. apply Q_lift_eq; Qcrush. destruct (H16 x); intuition. destruct (H21 x); intuition.
  - (* 0 ∉ df, 0 ∈ d1, analogous to the previous case *)
    apply qenv_saturated_q''_0 in H4; auto. apply Q_lift_eq; Qcrush. destruct (H14 x); intuition. destruct (H20 x); intuition.
Qed.

Lemma subst1_mem_loc : forall {dx df l}, l ∈ₗ {0 |-> dx }ᵈ df ->  (l ∈ₗ dx /\ $0 ∈ᵥ df) \/ l ∈ₗ df.
  intros. qual_destruct df. qual_destruct dx. unfold_q.
#[local] Hint Resolve n_reflect_true : bdestruct.
  bdestruct (fvs 0); Qcrush.
#[local] Remove Hints n_reflect_true : bdestruct.
Qed.

Lemma subst1_senv_saturated : forall {Σ df dx'},
    senv_saturated Σ df ->
    senv_saturated Σ dx' ->
    closed_Qual 0 0 (‖Σ‖) dx'↑ ->
    wf_senv Σ ->
    senv_saturated Σ ({0 |-> dx' }ᵈ df).
  intros. unfold senv_saturated,qenv_saturated_q in *. intros. apply subst1_mem_loc in H3. intuition.
  - eapply H0 in H3; eauto. apply subst1_qual_0; auto.
  - destruct a as [t q]. pose proof (wf_senv_prop H2 x t q). intuition. eapply H in H4; eauto. rewrite Q_lift_subst_qual. Qcrush.
Qed.

Lemma qglb_disjoint_freshv : forall {dx' l x},
  closed_Qual 0 0 l dx'↑ -> dx' ⊓ $!x = ∅.
  intros. apply Q_lift_eq. Qcrush. eauto.
Qed.

Lemma vtp_closed:
  forall {Σ φ t T d}, vtp Σ φ t T d ->
    closed_tm 0 0 (‖Σ‖) t /\
    closed_ty 0 0 (‖Σ‖) T /\
    closed_Qual 0 0 (‖Σ‖) d↑.
Proof.
  intros. induction H; intuition.
  - apply qstp_closed in H4. subst. intuition.
  - constructor. apply indexr_var_some' in H4; intuition.
  - constructor. apply stp_closed in H5. intuition.  simpl in *. auto.
Qed.

Lemma vtp_qual_ex: forall {Σ φ t T d d'}, vtp Σ φ t T d -> qstp ([]: tenv) Σ d d'  -> senv_saturated Σ d'-> vtp Σ φ t T d'.
Proof.
  intros. apply qstp_closed in  H0 as  Hcl_qstp; intuition.  induction  H.
  - assert  (qstp  [] Σ  df1 d'). { eapply qs_trans;  eauto. }
    econstructor; eauto.
  - econstructor;  eauto.
  - econstructor. Focus 6. eapply H8. all: eauto.
  - assert (qstp [] Σ df1 d').  { eapply qs_trans; eauto. }
    econstructor; eauto.
  - econstructor; eauto.
Qed.

Lemma vtp_saturated: forall {Σ φ t T d}, vtp Σ φ t T d -> saturated [] Σ d.
  intros. inversion H; subst; constructor; auto.
Qed.

Lemma subQual_eq : forall {p q}, p ⊑↑ q -> q ⊑↑ p -> p = q.
Proof. intros. apply Q_lift_eq. Qcrush. Qed.

Lemma vtp_qual_widening : forall {Σ φ t T1 d1 d2},
    vtp Σ φ t T1 d1 -> qstp [] Σ d1 d2 -> senv_saturated Σ d2 -> vtp Σ φ t T1 d2.
Proof.
  intros. induction H.
  - econstructor; eauto.
  - econstructor; eauto.
    eapply qstp_closed in H0. intuition.
  - eapply qstp_empty in H13. eapply qstp_empty in H14.
    assert (q1 = q2). eapply subQual_eq; eauto. subst.
    econstructor; eauto.
    eapply qstp_closed in H0. intuition.
  - econstructor; eauto.
    eapply qstp_closed in H0. intuition.
  - econstructor; eauto.
Qed.

Lemma vtp_type_widening: forall {Σ φ T1 T2 d1 d2 d3 t},
    vtp Σ φ t T1 d1 -> stp [] Σ T1 d2 T2 d3 -> vtp Σ φ t T2 d1.
Proof.
  intros Σ φ T1 T2 d1 d2 d3 t HVtp HStp. remember t as tt. remember [] as Γ.
  induction HStp; subst.
  - apply qstp_closed in H0 as HC. intuition.
    inversion HVtp; subst; econstructor; eauto.
  - inversion HVtp.
  - inversion HVtp.
  - eapply vtp_closed in HVtp as HC. intuition.
    eapply stp_closed in HStp1 as HC. intuition.
    inversion HVtp; subst; econstructor; eauto.
    assert (narrow: stp [(bind_ty, false,T3, d3); (bind_tm, true,TAll d7 d8 T0 T5, {♦})] Σ (open_ty' ([]: tenv) T5)(openq' ([]:tenv) d8) (open_ty' ([]:tenv) T2) (openq' ([]: tenv) d2)). {
      eapply narrowing_stp_ty; eauto.
      apply weaken_stp. auto.
    }
    simpl in *. eapply s_trans; eauto.
    specialize (@narrowing_stp_gen [(bind_ty, false, T3, d3)] true (TAll d0 d2 T1 T2) {♦} [] Σ
                  (T2 <~²ᵀ ([]:tenv)) (d2 <~²ᵈ ([]:tenv)) (T4 <~²ᵀ ([]:tenv)) (d4 <~²ᵈ ([]:tenv))) as narrowing.
    simpl in narrowing. intuition.
  - auto.
  - inversion HVtp; subst. intros. eapply vtp_loc. Focus 6. eapply H11. all: eauto.
    apply qstp_closed in H. intuition.
    assert (qstp [] Σ (q2 ⊔ &! l) (q1 ⊔ &! l)). {
      replace (q2 ⊔ &! l) with (&! l  ⊔ q2).
      replace (q1 ⊔ &! l) with (&! l  ⊔ q1).
      eapply qs_cong; eauto. econstructor. Qcrush. intuition. Qcrush. Qcrush.
      eapply indexr_var_some' in H11. lia.
      all: apply Q_lift_eq; Qcrush.
    }
    assert (qstp [] Σ (q2 ⊔ &! l) d1). { eapply qs_trans; eauto. }
    eapply qs_trans; eauto.
  - inversion HVtp; subst; econstructor; eauto.
    assert (narrow: stp [(bind_tm, false,T3, d3); (bind_tm, true,TFun d7 d8 T0 T5, {♦})] Σ (open_ty' ([]: tenv) T5)(openq' ([]:tenv) d8) (open_ty' ([]:tenv) T2) (openq' ([]: tenv) d2)). {
      eapply narrowing_stp; eauto. intros. inversion H2.
      apply weaken_stp. auto.
    }
    simpl in *. eapply s_trans; eauto.
    assert (forall T (a:T) (b:T), [a;b] = [a]++[b]) as R. eauto.
    rewrite R in HStp2. rewrite R.
    eapply @narrowing_stp_gen with (U := (TFun d0 d2 T1 T2))(du:={♦})(Γ2 := []: tenv)  in HStp2. 3: constructor. all: eauto.
  - intuition.
Qed.

Lemma vtp_widening: forall {Σ φ T1 d1 T2 d2 t},
  vtp Σ φ t T1 d1 -> stp [] Σ T1 d1 T2 d2 -> senv_saturated Σ d2 -> vtp Σ φ t T2 d2.
Proof.
  intros Σ φ T1 d1 T2 d2 t HVtp HStp Hsat.
  eapply vtp_closed in HVtp as HC. intuition.
  assert (stp [] Σ T1 d1 T2 d1). { eapply stp_qual_irrelevance. eapply HStp. eapply qstp_refl. simpl. auto. }
  eapply vtp_type_widening in HVtp. 2: eapply H0.
  eapply vtp_qual_widening; eauto. eapply stp_qstp_inv in HStp. eauto.
Qed.

Lemma has_type_vtp: forall {Σ φ t T d},
  value t ->
  has_type [] φ Σ t T d ->
  wf_senv Σ ->
  vtp Σ φ t T d.
Proof.
  intros Σ φ t T d HV Ht HWF. remember [] as Γ. induction Ht; eauto; subst; try inversion HV; subst; intuition;
    try solve [simpl in H1; discriminate].
  - (* ttabs *) subst. apply has_type_closed in Ht as Hcl. intuition.
    inversion H0. subst.  eapply vtp_tabs; eauto.
    + eapply stp_refl. intuition. apply qstp_refl; intuition.
    + apply stp_refl; intuition.
  - (* tunit *) constructor; eauto using senv_saturated_empty.
  - (* tabs *) subst.  subst. apply has_type_closed in Ht as Hcl. intuition.
    inversion H0. subst.  eapply vtp_abs; eauto.
    + eapply stp_refl; intuition.
    + apply stp_refl; intuition.
  - (* tloc *) intros.  eapply vtp_loc; eauto.
    + eapply closed_qual_qor; auto. apply just_loc_closed. apply indexr_var_some' in H0. lia.
    + Qcrush.
    + apply stp_refl; auto.
    + apply stp_refl; auto.
    + eapply wf_senv_saturated_qplus; eauto.
  - intuition. eapply vtp_widening; eauto.
  - intuition. eapply vtp_widening; eauto.
  - intuition. eapply vtp_widening; eauto.
  - intuition. eapply vtp_widening; eauto.
Qed.

Lemma vtp_has_type: forall {Σ t T d φ}, vtp Σ φ t T d -> has_type [] d Σ t T d.
  intros. induction H.
  + (* ttabs *) assert (has_type [] df1 Σ (ttabs t) (TAll d1 d2 T1 T2) df1). {
    constructor; eauto. apply qstp_closed in H4 as Hcl; intuition. }
    assert (has_type [] df2 Σ (ttabs t) (TAll d1 d2 T1 T2) df1). {
    inversion H1. subst. eapply weaken_flt with  (φ' := df2) in H10; intuition.
    eapply qstp_empty; eauto. eapply qstp_closed; eauto. }
    eapply t_sub; eauto; intuition.
  + (* tunit *) econstructor; eauto.
  + (* tloc *) eapply qstp_empty in H7.
    eapply t_sub; auto. eapply t_loc; eauto. Qcrush. assert (q2 ⊑↑ d). Qcrush. apply qstp_empty in H11. Qcrush.
    eapply s_ref; eauto. eapply qs_sq; eauto. eapply qstp_empty in H11, H12. Qcrush.
  + (* tabs *) assert (has_type [] df1 Σ (tabs t) (TFun d1 d2 T1 T2) df1). {
    constructor; eauto. apply qstp_closed in H5 as Hcl; intuition. }
    assert (has_type [] df2 Σ (tabs t) (TFun d1 d2 T1 T2) df1). {
    inversion H1. subst. eapply weaken_flt with  (φ' := df2) in H11; intuition.
    eapply qstp_empty; eauto. }
    eapply t_sub; eauto; intuition.
  + (* ttop *) apply has_type_closed in IHvtp as Hcl. intuition.
      econstructor; eauto.
Qed.

Lemma subst_qstp :  forall {Γ bd b Tf df df' Σ d1 d2},
    qstp (Γ ++ [(bd, b, Tf, df)]) Σ d1 d2 ->
    closed_ty 0 0 (‖Σ‖) Tf ->
    closed_Qual 0 0 (‖Σ‖) df'↑ ->
    Substq (Γ ++ [(bd, b, Tf, df)]) Σ df df' ->
    qstp ({0 |-> Tf ~ df' }ᴳ Γ) Σ ({0 |-> df' }ᵈ d1) ({0 |-> df' }ᵈ d2).
  intros Γ bd b Tf df df' Σ d1 d2 H. remember (Γ ++ [(bd, b, Tf, df)]) as Γ'.
  generalize dependent Γ. generalize dependent df.  generalize dependent Tf.
  induction H; intros; subst.
  - apply qs_sq. apply subst_qual_subqual_monotone. auto. eapply closed_qual_subst1'; eauto.
  -  bdestruct (f =? 0).
    * pose (H' := H). subst. rewrite indexr_skips in H'; auto. simpl in H'. inversion H'. subst.
      rewrite subst1_qor_dist. rewrite subst1_just_fv0. erewrite subst1_qual_id; eauto. inversion H4; subst.
      + rewrite qor_idem. apply qs_sq; auto. rewrite subst1_env_length. eapply closed_qual_monotone; eauto. lia.
      + rewrite <- H9 in H1. apply not_fresh_fresh_false in H1. contradiction.
    * rewrite subst1_qor_dist. destruct f. lia. rewrite <- subst1_just_fv.
      eapply qs_self; eauto. eapply @indexr_subst1 with (dx:=df') in H; try lia. eauto.
      eapply closed_qual_subst1; eauto.
    -  bdestruct (f =? 0).
    * pose (H' := H). subst. rewrite indexr_skips in H'; auto. simpl in H'. inversion H'. subst.
      rewrite subst1_qor_dist. rewrite subst1_just_fv0. erewrite subst1_qual_id; eauto. inversion H4; subst.
      + rewrite qor_idem. apply qs_sq; auto. rewrite subst1_env_length. eapply closed_qual_monotone; eauto. lia.
      + rewrite <- H9 in H1. apply not_fresh_fresh_false in H1. contradiction.
    * rewrite subst1_qor_dist. destruct f. lia. rewrite <- subst1_just_fv.
      eapply qs_self_all; eauto. eapply @indexr_subst1 with (dx:=df') in H; try lia. eauto.
      eapply closed_qual_subst1; eauto.
  - bdestruct (x =? 0).
    * subst. pose (H' := H). subst. rewrite indexr_skips in H'; auto. simpl in H'. inversion H'. subst.
      rewrite subst1_just_fv0. erewrite subst1_qual_id; eauto. inversion H5; subst.
      + apply qs_sq. auto. rewrite subst1_env_length. eapply closed_qual_monotone; eauto. lia.
      + rewrite <- H10 in H2. apply not_fresh_fresh_false in H2. contradiction.
    * destruct x. lia. rewrite <- subst1_just_fv. eapply qs_qvar. apply @indexr_subst1 with (Tx := Tf)(dx:=df') in H; try lia.
      eauto. eapply closed_ty_subst1; eauto. eapply closed_qual_subst1; eauto. eauto.
  - bdestruct (x =? 0).
    * subst. pose (H' := H). subst. rewrite indexr_skips in H'; auto. simpl in H'. inversion H'; destruct bd; subst; try discriminate.
      rewrite subst1_just_fv0. erewrite subst1_qual_id; eauto. inversion H5; subst.
      + apply qs_sq. auto. erewrite subst1_env_length. eapply closed_qual_monotone; eauto. lia.
      + rewrite <- H11 in H2. apply not_fresh_fresh_false in H2. contradiction.
    * destruct x. lia. rewrite <- subst1_just_fv. eapply qs_qvar_ty. apply @indexr_subst1 with (Tx := Tf)(dx:=df') in H; try lia.
      eauto. eapply closed_ty_subst1; eauto. eapply closed_qual_subst1; eauto. eauto.
  - repeat rewrite subst1_qor_dist. eapply qs_cong; eauto. eapply closed_qual_subst1'; eauto.
  - eapply qs_trans. eapply IHqstp1; eauto. eauto.
    Unshelve. all : auto.
Qed.

Lemma subst_ty_qstp :  forall {Γ T d d' Σ d1 d2},
    qstp (Γ ++ [(bind_ty, false, T, d)]) Σ d1 d2 ->
    closed_ty 0 0 (length Σ) T ->
    closed_Qual 0 0 (length Σ) d'↑ ->
    Substq (Γ ++ [(bind_ty, false, T, d)]) Σ d d' ->
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
      + apply qs_sq. auto. erewrite subst1_env_length. eapply closed_qual_monotone; eauto. lia.
      + rewrite <- H10 in H2. apply not_fresh_fresh_false in H2. contradiction.
    * destruct x. lia. rewrite <- subst1_just_fv. eapply qs_qvar_ty.
      apply @indexr_subst1 with (Tx := T)(dx:=d') in H; try lia. simpl in H. eauto.
      eapply closed_ty_subst1; eauto. eapply closed_qual_subst1; eauto. eauto.
  - repeat rewrite subst1_qor_dist. eapply qs_cong; eauto. eapply closed_qual_subst1'; eauto.
  - eapply qs_trans. eapply IHqstp1; eauto. eauto.
  Unshelve. all : auto.
Qed.

Lemma Substq_weaken : forall Γ Σ a df df',
  closed_Qual 0 (‖Γ‖) (‖Σ‖) df'↑ ->
  closed_qenv_qn (‖Γ‖) Γ ->
  Substq Γ Σ df df' ->
  Substq (a :: Γ) Σ df df'.
intros. induction H1; subst. constructor; auto. replace (q_trans Γ Σ df ⋒ q_trans Γ Σ dx) with (q_trans (a::Γ) Σ df ⋒ q_trans (a::Γ) Σ dx). constructor; auto. simpl. eapply closed_Qual_monotone; eauto. unfold q_trans,q_trans_tenv,q_trans_senv. repeat rewrite q_trans''_extend_closed_id'; auto. repeat rewrite q_trans''_fuel_max with (E:=Γ) (fuel:=(‖ a :: Γ ‖)); auto. all: simpl; Qcrush; exfalso; eauto.
Qed.

Lemma subst_stp : forall{T1 T2},
    forall {Γ bd b Tf df df' Σ d1 d2},
      stp (Γ ++ [(bd, b,Tf,df)]) Σ T1 d1 T2 d2 ->
      wf_tenv (Γ ++ [(bd, b,Tf,df)]) Σ ->
      closed_ty 0 0  (‖Σ‖) Tf ->
      closed_Qual 0 0 (‖Σ‖) df'↑ ->
      Substq (Γ ++ [(bd, b,Tf,df)]) Σ df df' ->
      stp ({ 0 |-> Tf ~ df' }ᴳ Γ) Σ
          ({ 0 |-> Tf ~ df' }ᵀ T1) ({ 0 |-> df' }ᵈ d1)
          ({ 0 |-> Tf ~ df' }ᵀ T2) ({ 0 |-> df' }ᵈ d2).
  intros T1 T2 Γ bd b Tf df df' Σ d1 d2 HS.
  remember (Γ ++ [(bd, b, Tf, df)]) as Γ'.
  generalize dependent Γ. generalize dependent df.  generalize dependent Tf. induction HS; intros; subst.
  - (* TTop *) simpl. constructor. eapply closed_ty_subst1'; eauto. eapply subst_qstp; eauto.
  - (* TVarF x *) simpl.  (bdestruct (x =? 0)).
    * (*x is 0 *) rewrite indexr_skips in H; simpl; auto; try lia. simpl in H. subst. simpl in H.
      inversion H. subst. eapply subst_qstp in H0; eauto. eapply stp_refl; eauto.
      eapply closed_ty_monotone; eauto. lia.

    * (*x is in Γ0*) assert (Hx: 1 <= x); try lia. destruct x; try lia.
      destruct v. destruct p. specialize (@subst_qstp _ _  _ _ _ df' _ _ _ H0); intuition.
      eapply stp_refl; eauto. constructor. erewrite subst1_env_length.
      erewrite <-  indexr_insert_ge in  H.  replace (Γ0 ++  [])  with Γ0 in H.
      apply indexr_var_some' in  H. intuition. intuition.
      intuition.
  - (* TVarF x  trans *)
    destruct bd; simpl; bdestruct (x =? 0).
(* bind_tm *)
    * (*x is 0 *) subst. rewrite indexr_skips in H. simpl in H. inversion H. simpl. lia.
    * (*x is in Γ0*) intuition. apply @indexr_subst1 with (Tx := Tf)(dx :=df') in H; try lia.
    econstructor; eauto.
    erewrite subst1_ty_id; auto. apply H0.
(* bind_ty *)
    * (*x is 0 *) subst. eapply @indexr_subst1' in H.
    specialize (IHHS Tf df Γ0). intuition. subst. erewrite subst1_ty_id in H7; eauto.
    * (*x is in Γ0*) intuition. apply @indexr_subst1 with (Tx := Tf)(dx :=df') in H; try lia.
    econstructor. eauto.
    erewrite subst1_ty_id; eauto. eapply IHHS; eauto.
  - (* TAll *) simpl. inversion H. inversion H0. subst.  econstructor; eauto.
    1,2: constructor; try eapply closed_ty_subst1'; eauto; eapply closed_qual_subst1'; eauto.
    eapply subst_qstp; eauto.
    specialize (IHHS2 Tf df ((bind_ty, false, T3, d3) :: (bind_tm, true, TAll d1 d2 T1 T2, {♦}) :: Γ0)). intuition.
    unfold open_ty' in *. unfold open_ty in *.
    unfold openq' in *. unfold openq in *.
    rewrite app_length in *. rewrite subst1_env_length. simpl in *.
    replace (‖Γ0‖ + 1) with (S (‖Γ0‖)) in *; try lia.
rename H6 into HH.
    erewrite <- open_subst1_ty_comm in HH; eauto. erewrite <- open_subst1_ty_comm in HH; eauto.
    erewrite <- open_subst1_ty_comm in HH; eauto. erewrite <- open_subst1_ty_comm in HH; eauto.
    erewrite <- open_subst1_qual_comm in HH; eauto. erewrite <- open_subst1_qual_comm in HH; eauto.
    erewrite <- open_subst1_qual_comm in HH; eauto. erewrite <- open_subst1_qual_comm in HH; eauto.
apply HH; auto.
inversion H0. inversion H. subst. constructor; eauto. constructor; eauto. 1-3: simpl; rewrite app_length; simpl; rewrite Nat.add_1_r. auto. eapply closed_ty_monotone; eauto. eapply closed_Qual_monotone; eauto.
apply Substq_weaken. simpl; rewrite app_length; simpl. eapply closed_Qual_monotone; eauto. lia. eapply wf_tenv_closed_qenv_qn. econstructor; eauto. simpl; rewrite app_length; simpl. eapply closed_ty_monotone; eauto. lia.
apply Substq_weaken; eauto. simpl; rewrite app_length; simpl. eapply closed_Qual_monotone; eauto. lia.
  - simpl. constructor. eapply subst_qstp; eauto.
  - specialize (stp_closed HS1). intuition. specialize (stp_closed HS2). intuition.
    simpl. constructor. eapply subst_qstp; eauto.
    eapply IHHS1; eauto. eapply IHHS2; eauto.
    1, 2: repeat erewrite subst1_ty_id; eauto.
    1, 2: eapply closed_qual_subst1'; eauto.
    1, 2: eapply subst_qstp; eauto.
  - simpl. constructor. inversion H. subst. 2 : inversion H0. subst.
    1,2: constructor; try eapply closed_ty_subst1'; eauto; eapply closed_qual_subst1'; eauto.
    eapply subst_qstp; eauto. eapply IHHS1; eauto.
    unfold open_ty' in *. unfold open_ty in *.
    unfold openq' in *. unfold openq in *.
    rewrite app_length in *. rewrite subst1_env_length. simpl in *.
    replace (‖Γ0‖ + 1) with (S (‖Γ0‖)) in *; try lia.
    specialize (IHHS2 Tf df ((bind_tm, false, T3, d3) :: (bind_tm, true, TFun d1 d2 T1 T2, {♦}) :: Γ0)). intuition. rename H6 into IHHS2. simpl in IHHS2.
    erewrite <- open_subst1_ty_comm in IHHS2; eauto. erewrite <- open_subst1_ty_comm in IHHS2; eauto.
    erewrite <- open_subst1_ty_comm in IHHS2; eauto. erewrite <- open_subst1_ty_comm in IHHS2; eauto.
    erewrite <- open_subst1_qual_comm in IHHS2; eauto. erewrite <- open_subst1_qual_comm in IHHS2; eauto.
    erewrite <- open_subst1_qual_comm in IHHS2; eauto. erewrite <- open_subst1_qual_comm in IHHS2; eauto.
apply IHHS2; auto.
inversion H0. inversion H. subst. constructor; eauto. constructor; eauto. 1-3: simpl; rewrite app_length; simpl; rewrite Nat.add_1_r. auto. eapply closed_ty_monotone; eauto. eapply closed_Qual_monotone; eauto.
apply Substq_weaken. simpl; rewrite app_length; simpl. eapply closed_Qual_monotone; eauto. lia. eapply wf_tenv_closed_qenv_qn. econstructor; eauto. simpl; rewrite app_length; simpl. eapply closed_ty_monotone; eauto. lia.
apply Substq_weaken; eauto. simpl; rewrite app_length; simpl. eapply closed_Qual_monotone; eauto. lia.
  - eapply s_trans. eapply IHHS1; eauto. eapply IHHS2; eauto.
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

Lemma wf_senv_subst1_id : forall Σ T q, wf_senv Σ -> ({0 |-> T ~ q }ᴳ Σ) = Σ.
intros. induction H; auto. simpl. rewrite IHwf_senv. erewrite subst1_ty_id; eauto. erewrite subst1_qual_id; eauto.
Qed.

Lemma q_trans_one_subst1_senv_comm : forall (Σ : senv) d T dx',
  wf_senv Σ ->
  senv_saturated Σ dx' ->
({0 |-> dx' }ᵈ (q_trans_one Σ d)) = (q_trans_one ({0 |-> T ~ dx' }ᴳ Σ) ({0 |-> dx' }ᵈ d)).
intros. generalize dependent d. induction Σ; intros; simpl; auto. ndestruct (qlocs d (‖ Σ ‖)).
  - assert (N_lift (qlocs ({0 |-> dx' }ᵈ d)) (‖ Σ ‖)). { rewrite Q_lift_qn. rewrite Q_lift_subst_qual. Qcrush. }
    rewrite subst1_env_length in *. clift. destruct a. simpl. rewrite subst1_qor_dist. rewrite <- IHΣ. auto. eapply wf_senv_shrink; eauto. unfold senv_saturated, qenv_saturated_q in *. intros. eapply H0 in H3. eauto. apply indexr_extend1; auto.
  - ndestruct (qlocs dx' (‖ Σ ‖)).
    + apply qenv_saturated_iff in H0 as H0'. autounfold in H0'. destruct a. simpl in *. rewrite subst1_env_length. ndestruct (qfvs d 0).
      -- assert (N_lift (qlocs ({0 |-> dx' }ᵈ d)) (‖ Σ ‖)). { rewrite Q_lift_qn. rewrite Q_lift_subst_qual. Qcrush. } inversion H. subst. erewrite @subst1_qual_id with (q:=q); eauto. unfold N_lift in H2. rewrite H2 in H0'. clift. rewrite <- IHΣ. rewrite <- H0'. assert (N_lift (qfvs (q_trans_one Σ d)) 0). { erewrite N_lift_trans_one; eauto. unfold N_trans_one. left. auto. } apply Q_lift_eq. rewrite Q_lift_or. rewrite Q_lift_subst_qual. Qcrush.
         eapply wf_senv_shrink; eauto. eapply qenv_saturated_q_shrink; eauto.
      -- assert (~N_lift (qlocs ({0 |-> dx' }ᵈ d)) (‖ Σ ‖)). { rewrite Q_lift_qn. rewrite Q_lift_subst_qual. Qcrush. } clift. rewrite IHΣ. auto.
eapply wf_senv_shrink; eauto. eapply qenv_saturated_q_shrink; eauto.
    + assert (~N_lift (qlocs ({0 |-> dx' }ᵈ d)) (‖ Σ ‖)). { rewrite Q_lift_qn. rewrite Q_lift_subst_qual. unfold not. intros. Qcrush. } rewrite subst1_env_length. clift. rewrite IHΣ. auto.
eapply wf_senv_shrink; eauto. eapply qenv_saturated_q_shrink; eauto.
Qed.

Lemma q_trans''_subst1_senv_comm : forall (Σ : senv) d T dx' fuel,
  wf_senv Σ ->
  senv_saturated Σ dx' ->
  {0 |-> dx' }ᵈ (q_trans'' Σ d fuel) = q_trans'' ({0 |-> T ~ dx' }ᴳ Σ) ({0 |-> dx' }ᵈ d) fuel.
intros. generalize dependent d. induction fuel; intros; simpl; auto. rewrite IHfuel. erewrite q_trans_one_subst1_senv_comm; eauto.
Qed.

Lemma q_trans''_subst1_senv_comm' : forall (Σ : senv) d dx' fuel,
  wf_senv Σ ->
  senv_saturated Σ dx' ->
  {0 |-> dx' }ᵈ (q_trans'' Σ d fuel) = q_trans'' Σ ({0 |-> dx' }ᵈ d) fuel.
intros. generalize dependent d. induction fuel; intros; simpl; auto. rewrite IHfuel. erewrite q_trans_one_subst1_senv_comm; eauto. rewrite wf_senv_subst1_id; eauto. Unshelve. apply TUnit.
Qed.

Lemma q_trans_one_subst1_tenv_comm : forall (Γ : tenv) (Σ : senv) bd bx Tx d dx',
  wf_tenv (Γ ++ [(bd,bx,Tx,dx')]) Σ ->
  wf_senv Σ ->
  closed_Qual 0 0 (‖ Σ ‖) dx' ↑ ->
  senv_saturated Σ dx' ->
  ({0 |-> dx' }ᵈ (q_trans_one (Γ ++ [(bd, bx, Tx, dx')]) d)) =
  (q_trans_one ({0 |-> Tx ~ dx' }ᴳ Γ) ({0 |-> dx' }ᵈ d)).
intros. generalize dependent d. induction Γ; intros. simpl. auto. ndestruct (qfvs d 0); auto. rewrite subst1_qor_dist. erewrite @subst1_qual_id with (q:=dx'); eauto. apply Q_lift_eq. rewrite Q_lift_or. rewrite Q_lift_subst_qual. Qcrush.
simpl. rewrite app_length, subst1_env_length. simpl. rewrite Nat.add_1_r. ndestruct (qfvs d (S (‖ Γ ‖))); simpl.
- assert (N_lift (qfvs ({0 |-> dx' }ᵈ d)) (‖ Γ ‖)). { unfold subst_qual. ndestruct (qfvs d 0); Qcrush. } clift. rewrite <- IHΓ. rewrite subst1_qor_dist. destruct a as [ [ [ bb b ] T ] q ]. simpl. auto. eauto.
- assert (~N_lift (qfvs ({0 |-> dx' }ᵈ d)) (‖ Γ ‖)). { unfold subst_qual. ndestruct (qfvs d 0); Qcrush. eauto. } clift. rewrite <- IHΓ; eauto.
Qed.

Lemma q_trans''_subst1_tenv_comm : forall (Γ : tenv) (Σ : senv) bd bx Tx d dx' fuel,
  wf_tenv (Γ ++ [(bd, bx,Tx,dx')]) Σ ->
  wf_senv Σ ->
  closed_Qual 0 0 (‖ Σ ‖) dx' ↑ ->
  senv_saturated Σ dx' ->
({0 |-> dx' }ᵈ (q_trans'' (Γ ++ [(bd, bx, Tx, dx')]) d fuel)) =
(q_trans'' ({0 |-> Tx ~ dx' }ᴳ Γ) ({0 |-> dx' }ᵈ d) fuel).
intros. generalize dependent d. induction fuel; intros; simpl; auto. rewrite IHfuel. erewrite q_trans_one_subst1_tenv_comm; eauto.
Qed.

Lemma q_trans_one_subst1_tenv_comm' : forall (Γ : tenv) (Σ : senv) bd bx Tx d dx' df0,
  wf_tenv (Γ ++ [(bd,bx,Tx,dx')]) Σ ->
  wf_senv Σ ->
  closed_Qual 0 0 (‖ Σ ‖) dx' ↑ ->
  senv_saturated Σ dx' ->
  ({0 |-> dx' }ᵈ (q_trans_one (Γ ++ [(bd, bx, Tx, df0 ⊓ dx')]) d)) =
  (q_trans_one ({0 |-> Tx ~ dx' }ᴳ Γ) ({0 |-> dx' }ᵈ d)).
intros. generalize dependent d. induction Γ; intros. simpl. auto. ndestruct (qfvs d 0); auto. rewrite subst1_qor_dist. erewrite @subst1_qual_id with (q:=(df0 ⊓ dx')); eauto. apply Q_lift_eq. rewrite Q_lift_or. rewrite Q_lift_subst_qual. Qcrush. Qcrush.
simpl. rewrite app_length, subst1_env_length. simpl. rewrite Nat.add_1_r. ndestruct (qfvs d (S (‖ Γ ‖))); simpl.
- assert (N_lift (qfvs ({0 |-> dx' }ᵈ d)) (‖ Γ ‖)). { unfold subst_qual. ndestruct (qfvs d 0); Qcrush. } clift. rewrite <- IHΓ. rewrite subst1_qor_dist. destruct a as [ [ [ bb b ] T ] q ]. simpl. auto. eauto.
- assert (~N_lift (qfvs ({0 |-> dx' }ᵈ d)) (‖ Γ ‖)). { unfold subst_qual. ndestruct (qfvs d 0); Qcrush. eauto. } clift. rewrite <- IHΓ; eauto.
Qed.

Lemma q_trans''_subst1_tenv_comm' : forall (Γ : tenv) (Σ : senv) bd bx Tx d dx' df0 fuel,
  wf_tenv (Γ ++ [(bd,bx,Tx,dx')]) Σ ->
  wf_senv Σ ->
  closed_Qual 0 0 (‖ Σ ‖) dx' ↑ ->
  senv_saturated Σ dx' ->
  ({0 |-> dx' }ᵈ (q_trans'' (Γ ++ [(bd, bx, Tx, df0 ⊓ dx')]) d fuel)) =
  (q_trans'' ({0 |-> Tx ~ dx' }ᴳ Γ) ({0 |-> dx' }ᵈ d) fuel).
intros. generalize dependent d. induction fuel; intros; simpl; auto. rewrite IHfuel. erewrite q_trans_one_subst1_tenv_comm'; eauto.
Qed.

Lemma wf_tenv_weaken : forall (Γ1 Γ2 : tenv) Σ bd bx Tx dx Tx' dx',
   wf_tenv (Γ1 ++ (bd, bx, Tx, dx) :: Γ2) Σ ->
   closed_ty 0 (‖ Γ2 ‖) (‖ Σ ‖) Tx' ->
   closed_Qual 0 (‖ Γ2 ‖) (‖ Σ ‖) dx' ↑ ->
   wf_tenv (Γ1 ++ (bd, bx, Tx', dx') :: Γ2) Σ.
intros. induction Γ1; simpl in *. constructor; auto. eapply wf_tenv_shrink; eauto.
destruct a as [ [ [ bd0 bx0 ] Tx0 ] dx0]. pose proof (wf_tenv_prop H (‖ Γ1 ++ (bd, bx, Tx, dx) :: Γ2 ‖) bd0 bx0 Tx0 dx0) as Hprop. rewrite indexr_head in Hprop. intuition. constructor; eauto. all: simpl in *; rewrite app_length in *; auto.
Qed.

Lemma wf_tenv_weaken' : forall (Γ1 Γ2 : tenv) Σ bd bx Tx dx dx',
   wf_tenv (Γ1 ++ (bd, bx, Tx, dx) :: Γ2) Σ ->
   closed_Qual 0 (‖ Γ2 ‖) (‖ Σ ‖) dx' ↑ ->
   wf_tenv (Γ1 ++ (bd, bx, Tx, dx') :: Γ2) Σ.
intros. eapply wf_tenv_weaken; eauto. pose proof (wf_tenv_prop H (‖ Γ2 ‖) bd bx Tx dx) as Hprop. rewrite indexr_insert in Hprop. intuition.
Qed.

Lemma q_trans''_subst1_tenv_subq : forall Γ0 Σ bd Tx dx' df0 df bx,
  wf_senv Σ ->
  wf_tenv (Γ0 ++ [(bd, bx, Tx, dx')]) Σ ->
  closed_Qual 0 0 (‖ Σ ‖) dx' ↑ ->
  senv_saturated Σ dx' ->
  (q_trans'' ({0 |-> Tx ~ dx' }ᴳ Γ0) ({0 |-> dx' }ᵈ df) (‖ Γ0 ‖)) ⊑↑
  ({0 |-> dx' }ᵈ (q_trans'' (Γ0 ++ [(bd, bx, Tx, df0 ⋒ dx')]) df (S (‖ Γ0 ‖)))).
intros. erewrite <- q_trans''_subst1_tenv_comm' with (df0:=df0); eauto. apply subst_qual_subqual_monotone. eapply Subq_trans. apply q_trans''_incr_subq. eapply q_trans_tenv_narrowing_subq; eauto.
Qed.

Lemma q_trans''_subst1_tenv_subq' : forall Γ0 Σ bd Tx dx' dx df bx,
  wf_senv Σ ->
  wf_tenv (Γ0 ++ [(bd, bx, Tx, dx)]) Σ ->
  closed_Qual 0 0 (‖ Σ ‖) dx' ↑ ->
  Substq (Γ0 ++ [(bd, bx, Tx, dx)]) Σ dx dx' ->
  senv_saturated Σ dx' ->
  (q_trans'' ({0 |-> Tx ~ dx' }ᴳ Γ0) ({0 |-> dx' }ᵈ df) (‖ Γ0 ‖)) ⊑↑
  ({0 |-> dx' }ᵈ (q_trans'' (Γ0 ++ [(bd, bx, Tx, dx)]) df (S (‖ Γ0 ‖)))).
intros. inversion H2; subst.
- erewrite <- q_trans''_subst1_tenv_comm; eauto. apply subst_qual_subqual_monotone. apply q_trans''_incr_subq.
- eapply @Subq_trans with (d2:=
  ({0 |-> dx' }ᵈ (q_trans'' (Γ0 ++ [(bd, bx, Tx, q_trans (Γ0 ++ [(bd, bx, Tx, dx)]) Σ df0 ⋒ dx')]) df (S (‖ Γ0 ‖))))); eauto.
eapply q_trans''_subst1_tenv_subq; eauto. eapply wf_tenv_weaken'; eauto.
apply subst_qual_subqual_monotone. apply q_trans_tenv_narrowing_subq; auto. apply Subq_qor; auto. apply Subq_qand_split; auto.
Qed.

Lemma closed_Qual_q_trans_one_monotone : forall {p : Type} `{qenv p} (E : env p) q b f l,
  closed_Qual b f l q ↑ ->
  closed_qenv b f l E ->
  closed_Qual b f l (q_trans_one E q) ↑.
intros. induction E; simpl; auto. apply closed_qenv_shrink in H1 as H1'. intuition. ndestruct (qenv_qn q (‖ E ‖)); auto. apply closed_Qual_qor; auto. specialize (H1 (‖ E ‖) a). rewrite indexr_head in H1. intuition.
Qed.

Lemma closed_Qual_q_trans''_monotone : forall {p : Type} `{qenv p} (E : env p) q b f l fuel,
  closed_Qual b f l q ↑ ->
  closed_qenv b f l E ->
  closed_Qual b f l (q_trans'' E q fuel) ↑.
intros. generalize dependent q. induction fuel; intros; simpl; auto. apply IHfuel. apply closed_Qual_q_trans_one_monotone; auto.
Qed.

Lemma q_trans_one_qand_subq : forall {p : Type} `{qenv p} (E : env p) q1 q2,
  q_trans_one E (q1 ⊓ q2) ⊑↑ q_trans_one E q1 ⊓ q_trans_one E q2.
intros. induction E; simpl; auto. ndestruct (qenv_qn (q1 ⊓ q2) (‖ E ‖)).
- assert (N_lift (qenv_qn q1) (‖ E ‖)). { erewrite @Q_lift_qn with (Qn:=qenv_Qn) in *; eauto. rewrite Q_lift_and in H0. erewrite @Qn_and_dist with (qn:=qenv_qn) (Qn:=qenv_Qn) in H0; eauto. Qcrush. all: apply qenv_qn_prop. }
  assert (N_lift (qenv_qn q2) (‖ E ‖)). { erewrite @Q_lift_qn with (Qn:=qenv_Qn) in *; eauto. rewrite Q_lift_and in H0. erewrite @Qn_and_dist with (qn:=qenv_qn) (Qn:=qenv_Qn) in H0; eauto. Qcrush. all: apply qenv_qn_prop. }
  clift. rewrite <- qor_qand_dist_r. eauto using Subq_qor.
- ndestruct (qenv_qn q1 (‖ E ‖)). assert (~N_lift (qenv_qn q2) (‖ E ‖)). { erewrite @Q_lift_qn with (Qn:=qenv_Qn) in *; eauto. rewrite Q_lift_and in H0. erewrite @Qn_and_dist with (qn:=qenv_qn) (Qn:=qenv_Qn) in H0; eauto. Qcrush. all: apply qenv_qn_prop. } clift. rewrite qand_qor_dist_r. eapply Subq_trans; eauto.
  ndestruct (qenv_qn q2 (‖ E ‖)). rewrite qand_qor_dist_l. eapply Subq_trans; eauto. auto.
Qed.

Lemma q_trans''_qand_subq : forall {p : Type} `{qenv p} (E : env p) q1 q2 fuel,
  q_trans'' E (q1 ⊓ q2) fuel ⊑↑ q_trans'' E q1 fuel ⊓ q_trans'' E q2 fuel.
intros. generalize dependent q2. generalize dependent q1. induction fuel; intros; simpl; auto. specialize (IHfuel (q_trans_one E q1) (q_trans_one E q2)). eapply @Subq_trans with (d2:=(q_trans'' E (q_trans_one E q1 ⊓ q_trans_one E q2) fuel)); eauto. apply q_trans''_subq. apply q_trans_one_qand_subq.
Qed.

Lemma q_trans_one_gt_id : forall {p : Type} `{qenv p} (E : env p) q,
  (forall n, n < (‖ E ‖) -> ~N_lift (qenv_qn q) n) ->
  (q_trans_one E q) = q.
intros. induction E; simpl; auto. ndestruct (qenv_qn q (‖ E ‖)).
- exfalso. specialize (H0 (‖ E ‖)). simpl in H0. intuition.
- rewrite IHE; auto. intros. apply H0. simpl. lia.
Qed.

Lemma q_trans''_gt_id : forall {p : Type} `{qenv p} (E : env p) q fuel,
  (forall n, n < (‖ E ‖) -> ~N_lift (qenv_qn q) n) ->
  (q_trans'' E q fuel) = q.
intros. induction fuel; simpl; auto. rewrite q_trans_one_gt_id; auto.
Qed.

Lemma q_trans_one_empty_id : forall {p : Type} `{qenv p} (E : env p) q,
  (forall n, ~N_lift (qenv_qn q) n) ->
  (q_trans_one E q) = q.
intros. induction E; simpl; auto. rewrite IHE. specialize (H0 (‖ E ‖)). unfold N_lift in H0. apply not_true_is_false in H0. rewrite H0. auto.
Qed.

Lemma q_trans''_empty_id : forall {p : Type} `{qenv p} (E : env p) q fuel,
  (forall n, ~N_lift (qenv_qn q) n) ->
  (q_trans'' E q fuel) = q.
intros. induction fuel; simpl; auto. rewrite q_trans_one_empty_id; auto.
Qed.

Lemma q_trans_empty_id : forall Γ Σ,
  (q_trans Γ Σ ∅) = ∅.
intros. unfold q_trans,q_trans_senv,q_trans_tenv. repeat rewrite q_trans''_empty_id; Qcrush.
Qed.

Lemma q_trans_one_qenv_swallow : forall {p : Type} `{qenv p} (a : p) (E : env p) q,
  (qenv_q a) ⊑↑ (q_trans_one E q) ->
  q_trans_one (a :: E) q = (q_trans_one E q).
intros. simpl. ndestruct (qenv_qn q (‖ E ‖)).
- apply Q_lift_eq. Qcrush.
- Qcrush.
Qed.

Lemma q_trans''_qenv_swallow : forall {p : Type} `{qenv p} (a : p) (E : env p) q fuel,
  (qenv_q a) ⊑↑ (q_trans_one E q) ->
  q_trans'' (a :: E) q fuel = (q_trans'' E q fuel).
intros. generalize dependent q. induction fuel; intros; auto.
simpl. ndestruct (qenv_qn q (‖ E ‖)).
- rewrite IHfuel. rewrite <- q_trans''_or_dist. assert (q_trans'' E (qenv_q a) fuel ⊑↑ q_trans'' E (q_trans_one E q) fuel). apply q_trans''_subq. auto. apply Q_lift_eq. Qcrush. rewrite <- q_trans_one_or_dist. eapply Subq_trans; eauto. eapply @Subq_trans with (d2:=q_trans_one E (q_trans_one E q)). apply q_trans_one_subq'. Qcrush.
- rewrite IHfuel; auto. eapply Subq_trans; eauto. apply q_trans_one_subq'.
Qed.

Lemma q_trans''_qenv_swallow' : forall {p : Type} `{qenv p} (a : p) (E : env p) q fuel,
  (qenv_q a) ⊑↑ q ->
  q_trans'' (a :: E) q fuel = (q_trans'' E q fuel).
intros. apply q_trans''_qenv_swallow. eapply Subq_trans; eauto. apply q_trans_one_subq'.
Qed.

Lemma q_trans_tenv_fv : forall Γ bd fr T q,
  q_trans_tenv ((bd, fr, T, q) :: Γ) $!(‖ Γ ‖) = ((q_trans_tenv Γ q) ⊔ $!(‖ Γ ‖)).
intros. unfold q_trans_tenv. simpl. assert (N_lift (qfvs $! (‖ Γ ‖)) (‖ Γ ‖)). Qcrush. clift. rewrite q_trans''_qenv_swallow'. rewrite <- q_trans''_or_dist. rewrite q_trans_one_gt_id. rewrite q_trans''_gt_id. apply Q_lift_eq. all: Qcrush.
Qed.

Lemma q_trans_fv : forall Γ Σ bd fr T q,
  q_trans ((bd, fr, T, q) :: Γ) Σ $!(‖ Γ ‖) = ((q_trans Γ Σ q) ⊔ $!(‖ Γ ‖)).
intros. unfold q_trans. rewrite q_trans_tenv_fv; auto. unfold q_trans_senv. rewrite <- q_trans''_or_dist. rewrite q_trans''_gt_id with (q:=$! (‖ Γ ‖)); auto. intros. Qcrush.
Qed.

Lemma wf_tenv_closed_subst : forall Γ Σ a bd b T q,
  wf_tenv (Γ ++ [a]) Σ ->
  closed_ty 0 0 (‖ Σ ‖) T ->
  closed_Qual 0 0 (‖ Σ ‖) q↑ ->
  wf_tenv (Γ ++ [(bd, b, T, q)]) Σ.
intros. induction Γ; simpl in *.
- constructor; auto. constructor. eapply wf_tenv_wf_senv; eauto.
- inversion H. subst. constructor; auto. all: rewrite app_length in *; simpl in *; auto.
Qed.

Lemma wf_tenv_subst : forall Γ Σ bd b T q,
  wf_tenv (Γ ++ [(bd, b, T, q)]) Σ ->
  wf_tenv ({0 |-> T ~ q }ᴳ Γ) Σ.
intros. remember (Γ ++ [(bd, b, T, q)]) as Γ0. generalize dependent Γ. induction H; intros.
- destruct Γ; simpl in *; discriminate.
- destruct Γ0. simpl. apply wf_tenv_nil; auto. eapply wf_tenv_wf_senv; eauto.
  simpl in HeqΓ0. inversion HeqΓ0. subst. simpl. pose proof (@wf_tenv_prop _ Σ H). constructor; auto.
  eapply closed_ty_subst1; eauto. eapply closed_ty_monotone; eauto. rewrite app_length,subst1_env_length in *. simpl. lia.
  1,2: specialize (H2 (‖ ([]:tenv) ‖) bd b T q); rewrite indexr_insert in H2; intuition.
  eapply closed_qual_subst1; eauto. eapply closed_Qual_monotone; eauto. rewrite app_length,subst1_env_length in *. simpl. lia.
  specialize (H2 (‖ ([]:tenv) ‖) bd b T q). rewrite indexr_insert in H2. intuition.
Qed.

Lemma wf_tenv_subst' : forall Γ Σ bd b T q df,
  wf_tenv (Γ ++ [(bd, b, T, df ⋒ q)]) Σ ->
  closed_Qual 0 0 (‖ Σ ‖) q↑ ->
  wf_tenv ({0 |-> T ~ q }ᴳ Γ) Σ.
intros. remember (Γ ++ [(bd, b, T, df ⋒ q)]) as Γ0. generalize dependent Γ. induction H; intros.
- destruct Γ; simpl in *; discriminate.
- destruct Γ0. simpl. apply wf_tenv_nil; auto. eapply wf_tenv_wf_senv; eauto.
  simpl in HeqΓ0. inversion HeqΓ0. subst. simpl. pose proof (@wf_tenv_prop _ Σ H) as Hprop. constructor; auto.
  eapply closed_ty_subst1; eauto. eapply closed_ty_monotone; eauto. rewrite app_length,subst1_env_length in *. simpl. lia.
  1,2: specialize (Hprop (‖ ([]:tenv) ‖) bd b T (df ⋒ q)); rewrite indexr_insert in Hprop; intuition.
  eapply closed_qual_subst1; eauto. eapply closed_Qual_monotone; eauto. rewrite app_length,subst1_env_length in *. simpl. lia.
Qed.

Lemma fuel_max_qenv_saturated_q'': forall {p : Type} `{qenv p} (E : env p) (q : qual) (fuel : nat),
  qenv_saturated_q'' E (q_trans'' E q (‖ E ‖)).
intros. unfold qenv_saturated_q''. rewrite <- q_trans''_fuel_max with (fuel:=(S (‖ E ‖))) at 2; auto.
simpl. rewrite q_trans''_one_commute. auto.
Qed.

Lemma qenv_qn_qenv_saturated_q'': forall {p : Type} `{qenv p} (E : env p) (a b : qual),
  qenv_qn a = qenv_qn b ->
  a ⊑↑ b ->
  qenv_saturated_q'' E a ->
  qenv_saturated_q'' E b.
intros. unfold qenv_saturated_q'' in *. induction E; simpl in *; auto. rewrite <- H0. ndestruct (qenv_qn a (‖ E ‖)); auto.
pose proof (q_trans_one_subq' E a).
assert (q_trans_one E a ⊔ qenv_q a0 ⊑↑ a). { rewrite H2. auto. }
assert (qenv_q a0 ⊑↑ b). Qcrush.
rewrite IHE; auto. all: apply Q_lift_eq; Qcrush.
Qed.

(* ad-hoc lemma for substitution *)
Lemma q_trans_one_closed_qenv_qfvs: forall {p : Type} `{qenv p} (E : env p) b l d,
  closed_qenv b 0 l E ->
  qfvs (q_trans_one E d) = qfvs d.
intros. induction E; simpl; auto. ndestruct (qenv_qn d (‖ E ‖)).
- rewrite qn_or_dist. rewrite IHE. specialize (H0 (‖ E ‖) a). rewrite indexr_head in H0. intuition. apply N_lift_eq. Qcrush. exfalso; eauto. eapply closed_qenv_shrink; eauto.
- apply IHE. eapply closed_qenv_shrink; eauto.
Qed.

(* ad-hoc lemma for substitution *)
Lemma q_trans''_closed_qenv_qfvs: forall {p : Type} `{qenv p} (E : env p) b l fuel d,
  closed_qenv b 0 l E ->
  qfvs (q_trans'' E d fuel) = qfvs d.
intros. induction fuel; simpl; auto. rewrite <- IHfuel. rewrite <- q_trans''_one_commute. erewrite q_trans_one_closed_qenv_qfvs; eauto.
Qed.

Lemma q_trans_qenv_saturated_q''_tenv: forall Γ Σ d {b l}, closed_qenv b 0 l Σ -> qenv_saturated_q'' Γ (q_trans Γ Σ d).
intros. unfold q_trans. remember (q_trans_tenv Γ d) as d'.
assert (qenv_saturated_q'' Γ d'). { subst d'. apply fuel_max_qenv_saturated_q''. apply 1. }
pose proof (q_trans''_closed_qenv_qfvs Σ b l (‖ Σ ‖) d'). intuition.
eapply qenv_qn_qenv_saturated_q'' with (a:=d'); eauto. apply q_trans''_subq'.
Qed.

Lemma q_trans_one_closed_id : forall {p : Type} `{qenv p} (E : env p) d,
  closed_Nats 0 (qenv_Qn d↑) ->
  q_trans_one E d = d.
intros. induction E; simpl; auto. ndestruct (qenv_qn d (‖ E ‖)). rewrite @Q_lift_qn with (Qn:=qenv_Qn) in H1. exfalso. eauto. apply qenv_qn_prop. apply IHE.
Qed.

Lemma q_trans''_closed_id : forall {p : Type} `{qenv p} (E : env p) fuel d,
  closed_Nats 0 (qenv_Qn d↑) ->
  q_trans'' E d fuel = d.
intros. induction fuel; simpl; auto. rewrite q_trans_one_closed_id; auto.
Qed.

Lemma q_trans_senv_locs : forall Σ T q,
  q_trans_senv ((T, q) :: Σ) &!(‖ Σ ‖) = ((q_trans_senv Σ q) ⊔ &!(‖ Σ ‖)).
intros. unfold q_trans_senv. simpl. assert (N_lift (qlocs &! (‖ Σ ‖)) (‖ Σ ‖)). Qcrush. clift. rewrite q_trans''_qenv_swallow'. rewrite <- q_trans''_or_dist. rewrite q_trans_one_gt_id. rewrite q_trans''_gt_id. apply Q_lift_eq. all: Qcrush.
Qed.

Lemma qqcap_fresh_l' : forall {d1 df f Σ Σ' d'},
    closed_Qual 0 f (‖Σ‖) d1↑ ->
    closed_Qual 0 f (‖Σ‖) df↑ ->
    closed_qenv 0 0 (‖Σ‖) Σ ->
    Σ → Σ' ∋ d1 ⊕ d' ->
    (q_trans [] Σ' d1 ⋒ q_trans [] Σ' df) =
    (q_trans [] Σ' (d1 ⋓ d') ⋒ q_trans [] Σ' df).
  intros. inversion H2; subst; simpl; destruct (♦∈? d1); auto.
  - rewrite qor_empty_right; auto.
  - repeat rewrite <- q_trans_or_dist. repeat rewrite qand_qor_dist_r.
    replace (q_trans [] ((T, q) :: Σ) &! (‖ Σ ‖) ⊓ q_trans [] ((T, q) :: Σ) df) with (q_trans [] ((T, q) :: Σ) q ⊓ q_trans [] ((T, q) :: Σ) df).
repeat rewrite <- qand_qor_dist_r. repeat rewrite q_trans_or_dist.    replace (d1 ⊔ q ⊔ q) with d1; auto.
    apply Q_lift_eq. Qcrush.
    replace (q_trans [] ((T, q) :: Σ) &! (‖ Σ ‖)) with ((q_trans [] ((T, q) :: Σ) q) ⊔ &! (‖ Σ ‖)). rewrite qand_qor_dist_r.
    replace (&! (‖ Σ ‖) ⊓ q_trans [] ((T, q) :: Σ) df) with (∅). rewrite qor_empty_right; auto. assert (closed_Qual 0 f (‖ Σ ‖) (q_trans [] ((T, q) :: Σ) df)↑). {
      unfold q_trans,q_trans_senv,q_trans_tenv.
      repeat apply closed_Qual_q_trans''_monotone.
      eapply closed_Qual_monotone; eauto.
      eapply closed_qenv_empty; eauto. apply [].
      apply closed_qenv_extend.
      eapply closed_qenv_monotone; eauto. lia.
      eapply closed_Qual_monotone; eauto. lia.
    }
    apply Q_lift_eq. Qcrush. eauto.
rewrite q_trans_senv_locs; auto. unfold q_trans,q_trans_senv. rewrite q_trans''_qenv_swallow'; auto. rewrite q_trans''_fuel_max. unfold q_trans_tenv. simpl. auto. simpl. lia.
Qed.

Lemma qqcap_fresh_r' : forall {d1 df f Σ Σ' d'},
    closed_Qual 0 f (‖Σ‖) d1↑ -> closed_Qual 0 f (‖Σ‖) df↑ ->
    closed_qenv 0 0 (‖Σ‖) Σ ->
    Σ → Σ' ∋ d1 ⊕ d' ->
    (q_trans [] Σ' df ⋒ q_trans [] Σ' d1) =
    (q_trans [] Σ' df ⋒ q_trans [] Σ' (d1 ⋓ d')).
  intros. inversion H2; subst; simpl; destruct (♦∈? d1); auto.
  - rewrite qor_empty_right; auto.
  - repeat rewrite <- q_trans_or_dist. repeat rewrite qand_qor_dist_l.
    replace (q_trans [] ((T, q) :: Σ) df ⊓ q_trans [] ((T, q) :: Σ) &! (‖ Σ ‖)) with (q_trans [] ((T, q) :: Σ) df ⊓ q_trans [] ((T, q) :: Σ) q).
    repeat rewrite <- qand_qor_dist_l. repeat rewrite q_trans_or_dist.    replace (d1 ⊔ q ⊔ q) with d1; auto.
    apply Q_lift_eq. Qcrush.
    replace (q_trans [] ((T, q) :: Σ) &! (‖ Σ ‖)) with ((q_trans [] ((T, q) :: Σ) q) ⊔ &! (‖ Σ ‖)). rewrite qand_qor_dist_l.
    replace (q_trans [] ((T, q) :: Σ) df ⊓ &! (‖ Σ ‖)) with (∅). rewrite qor_empty_right; auto. assert (closed_Qual 0 f (‖ Σ ‖) (q_trans [] ((T, q) :: Σ) df)↑). {
      unfold q_trans,q_trans_senv,q_trans_tenv.
      repeat apply closed_Qual_q_trans''_monotone.
      eapply closed_Qual_monotone; eauto.
      eapply closed_qenv_empty; eauto. apply [].
      apply closed_qenv_extend.
      eapply closed_qenv_monotone; eauto. lia.
      eapply closed_Qual_monotone; eauto. lia.
    }
    apply Q_lift_eq. Qcrush. eauto.
rewrite q_trans_senv_locs; auto. unfold q_trans,q_trans_senv. rewrite q_trans''_qenv_swallow'; auto. rewrite q_trans''_fuel_max. unfold q_trans_tenv. simpl. auto. simpl. lia.
Qed.


Lemma qor_non_fresh : forall q1 q2,
  ♦∉ q1 ->
  ♦∉ q2 ->
  ♦∉ q1 ⊔ q2.
intros. Qcrush.
Qed.

Lemma q_trans_one_non_fresh : forall {p : Type} `{qenv p} (E : env p) d,
  (forall (x : nat) (a : p), indexr x E = Some a -> ♦∉ (qenv_q a)) ->
  ♦∉ d ->
  ♦∉ q_trans_one E d.
intros. induction E; simpl; auto. ndestruct (qenv_qn d (‖ E ‖)).
- apply qor_non_fresh.
  apply IHE. intros. eapply H0 with (x:=x); eauto. rewrite indexr_skip; auto. apply indexr_var_some' in H3. lia.
eapply H0 with (x:=(‖ E ‖)). rewrite indexr_head. auto.
- apply IHE. intros. eapply H0 with (x:=x); eauto. rewrite indexr_skip; auto. apply indexr_var_some' in H3. lia.
Qed.

Lemma q_trans''_non_fresh : forall {p : Type} `{qenv p} (E : env p) fuel d,
  (forall (x : nat) (a : p), indexr x E = Some a -> ♦∉ (qenv_q a)) ->
  ♦∉ d ->
  ♦∉ q_trans'' E d fuel.
intros. generalize dependent d. induction fuel; intros; simpl; auto. apply IHfuel. apply q_trans_one_non_fresh; auto.
Qed.

Lemma q_trans_senv_wf_senv_non_fresh : forall Σ dx,
  wf_senv Σ ->
  ♦∉ dx ->
  ♦∉ q_trans_senv Σ dx.
intros. unfold q_trans_senv. apply q_trans''_non_fresh; auto. intros. destruct a. simpl. eapply wf_senv_prop with (l:=x) (T:=t) (q:=q) in H; intuition.
Qed.

Lemma subst_qual_subqual_monotone_fresh : forall {d1 d2}, d1 ⊑↑ d2 ⊔ {♦} -> forall {df}, ({0 |-> df }ᵈ d1) ⊑↑ ({0 |-> df }ᵈ d2) ⊔ {♦}.
Proof.
  intros. qual_destruct d1; qual_destruct d2; qual_destruct df; unfold_q.
  ndestruct (fvs0 0); simpl;
  ndestruct (fvs 0); simpl; Qcrush; eauto.
  all: try match goal with
  | [ H : forall x : nat, N_lift _ x -> _ ,
      H1 : N_lift _ _ |- _ ] =>
      apply H in H1
      end; intuition.
Qed.

Lemma qand_diamond_r_non_fresh : forall q, ♦∉ q -> (q ⊓ {♦}) = ∅.
intros. apply Q_lift_eq. Qcrush.
Qed.

Lemma qand_diamond_r_fresh : forall q, ♦∈ q -> (q ⊓ {♦}) = {♦}.
intros. apply Q_lift_eq. Qcrush.
Qed.

Lemma substitution_gen :
  forall {t Γ φ φ' bd bx Tx dx dx' Σ T d}, (q_trans (Γ ++ [(bd, bx,Tx,dx)]) Σ dx') ⊓ (q_trans (Γ ++ [(bd, bx,Tx,dx)]) Σ φ) ⊑↑ dx ->
  has_type (Γ ++ [(bd, bx,Tx,dx)]) φ Σ t T d -> wf_tenv (Γ ++ [(bd, bx,Tx,dx)]) Σ -> wf_senv Σ -> Substq (Γ ++ [(bd, bx,Tx,dx)]) Σ dx dx' ->
        forall {tx}, vtp Σ φ' tx Tx dx' ->
                        has_type ({ 0 |-> Tx ~ dx' }ᴳ Γ) ({ 0 |-> dx' }ᵈ φ) Σ
                                 ({ 0 |-> tx  }ᵗ t)
                                 ({ 0 |-> Tx ~ dx' }ᵀ T)
                                 ({ 0 |-> dx' }ᵈ d).
  intros t Γ φ φ' bd bx Tx dx dx' Σ T d Hsep (* φ Hphi *) HT HwfΓ HwfΣ HSubst tx HTx. specialize (vtp_closed HTx) as Hclx.
  specialize (vtp_saturated HTx) as Hsatx. destruct Hsatx as [Htsatx Hssatx].
  simpl in Hclx. intuition. remember (Γ ++ [(bd, bx,Tx, dx)]) as Γ'.
  generalize dependent Γ.
  induction HT; intros; subst; pose (φs := {0 |-> dx' }ᵈ φ); replace ({0 |-> dx' }ᵈ φ) with φs in *; auto.
  - (* t_tabs *) simpl. apply t_tabs; auto. eapply closed_tm_subst1'; eauto.
    inversion H3. subst. constructor; try eapply closed_ty_subst1'; eauto; eapply closed_qual_subst1'; eauto.
    eapply closed_qual_subst1'; eauto.
    erewrite <- subst1_fresh_id. rewrite <- subst1_qor_dist. apply subst_qual_subqual_monotone; auto.
    apply subst_qual_subqual_monotone; auto. eauto.
    apply subst1_senv_saturated; auto.
    (* 1. instantiate the IH *)
    replace (length (Γ0 ++ [(bd, bx, Tx, dx)])) with (S (‖Γ0‖)) in IHHT.
    rewrite subst1_env_length. rewrite app_comm_cons in IHHT. rewrite app_comm_cons in IHHT.
    remember (df ⊔ $!(S (‖Γ0‖)) ⊔ $!(S (S (‖Γ0‖))) ⊔ {♦}) as DF.
    replace ({0 |-> dx' }ᵈ df ⊔ $!(‖Γ0‖) ⊔ $!(S (‖Γ0‖)) ⊔ {♦}) with ({0 |-> dx' }ᵈ DF).
    intuition. specialize IHHT with (Γ := (((bind_ty, false,T1, d1) :: (bind_tm, true, (TAll d1 d2 T1 T2), df) :: Γ0))).
    (* 2. reason about opening and subst, apply IH *)
    unfold open_tm' in *. unfold open_ty' in *. unfold open_ty in *.
    unfold openq' in *. unfold openq in *.
    rewrite app_length in IHHT. rewrite subst1_env_length. simpl in *.
    replace (‖Γ0‖ + 1) with (S (‖Γ0‖)) in IHHT; try lia.
    erewrite <- open_subst1_tm_comm in IHHT; eauto. erewrite <- open_subst1_tm_comm in IHHT; eauto.
    erewrite <- open_subst1_ty_comm in IHHT; eauto. erewrite <- open_subst1_ty_comm in IHHT; eauto.
    erewrite <- open_subst1_qual_comm in IHHT; eauto. erewrite <- open_subst1_qual_comm in IHHT; eauto. repeat erewrite subst1_qor_dist in IHHT. apply IHHT; auto.
    apply has_type_filter in HT as Hft.
    subst.
    inversion H3. subst. rewrite app_length in *. simpl in *. rewrite Nat.add_1_r in *.
    repeat rewrite <- q_trans_or_dist. repeat rewrite qand_qor_dist_l. assert (Hqn: closed_qenv_qn (S (‖ Γ0 ‖)) ((bind_ty, false, T1, d1) :: (bind_tm, true, TAll d1 d2 T1 T2, df) :: Γ0 ++ [(bd, bx, Tx, dx)])). {
      unfold closed_qenv_qn. intros.
    bdestruct (x =? (S (S (‖ Γ0 ‖)))). replace x with (‖ (bind_tm, true, TAll d1 d2 T1 T2, df) :: Γ0 ++ [(bd, bx, Tx, dx)] ‖) in *. rewrite indexr_head in H9. inversion H9. subst. simpl. Qcrush. subst. simpl. rewrite app_length. simpl. lia.
    bdestruct (x =? (S (‖ Γ0 ‖))). replace x with (‖ Γ0 ++ [(bd, bx, Tx, dx)] ‖) in *. rewrite indexr_skip in H9; auto. rewrite indexr_head in H9. inversion H9. subst. simpl. Qcrush. subst. simpl. rewrite app_length. simpl. lia.
    rewrite indexr_skip in H9; auto. rewrite indexr_skip in H9; auto. destruct a as [ [ [ b fr ] T' ] q']. eapply wf_tenv_prop in HwfΓ; eauto. simpl. apply indexr_var_some' in H9. rewrite app_length in *. simpl in *. rewrite Nat.add_1_r in *. eapply closed_Nats_mono; eauto. Qcrush. 1,2: subst; simpl; rewrite app_length; simpl; lia.
    }
    repeat apply Subq_qor_l. unfold q_trans,q_trans_tenv. repeat erewrite q_trans''_extend_closed_id'. rewrite q_trans''_fuel_max. eapply @Subq_trans with (d2:=(q_trans (Γ0 ++ [(bd, bx, Tx, dx)]) Σ dx' ⊓ q_trans (Γ0 ++ [(bd, bx, Tx, dx)]) Σ φ)); eauto. unfold q_trans,q_trans_tenv.
    eapply Subq_qand_split; eauto.
    repeat eapply q_trans''_subq; eauto. rewrite q_trans''_fuel_max. apply q_trans''_subq; auto. 1,2: simpl; lia.
    eapply closed_qenv_qn_monotone; eauto.
    1-3: simpl; rewrite app_length; simpl; rewrite Nat.add_1_r.
    Qcrush.
    eapply closed_qenv_qn_shrink in Hqn; eauto.
    Qcrush.
    eapply closed_qenv_qn_shrink in Hqn; eauto.
    eapply closed_Nats_mono with (n:=0). Qcrush. lia.
    eapply closed_qenv_qn_shrink in Hqn; eauto. simpl. eapply closed_qenv_qn_monotone; eauto. rewrite app_length. lia.
    eapply closed_Nats_mono with (n:=0). Qcrush. lia.
    erewrite q_trans_extend_tenv_closed_id' with (q':=$! (S (‖ Γ0 ‖))). replace (S (‖ Γ0 ‖)) with (‖ Γ0 ++ [(bd, bx, Tx, dx)] ‖). rewrite q_trans_fv. rewrite qand_qor_dist_l. erewrite qglb_disjoint_freshv; eauto. rewrite qor_empty_right. repeat erewrite q_trans_extend_tenv_closed_id'. eapply @Subq_trans with (d2:=(q_trans (Γ0 ++ [(bd, bx, Tx, dx)]) Σ dx' ⊓ q_trans (Γ0 ++ [(bd, bx, Tx, dx)]) Σ φ)); eauto. apply Subq_qand_split; auto.
    eapply closed_qenv_qn_shrink in Hqn; eauto.
    eapply closed_Nats_mono with (n:=0). Qcrush. lia.
    eapply closed_qenv_qn_shrink in Hqn; eauto.
    simpl. eapply closed_qenv_qn_monotone; eauto.
    rewrite app_length. simpl. lia.
    eapply closed_Nats_mono with (n:=0). Qcrush. lia.
    apply closed_Qual_q_trans''_monotone; eauto using wf_senv_closed_qenv.
    unfold q_trans_tenv. rewrite q_trans''_closed_id; auto. Qcrush.
    simpl; rewrite app_length; simpl; lia.
    1,2: simpl; rewrite app_length; simpl; rewrite Nat.add_1_r.
    eapply closed_qenv_qn_shrink in Hqn; eauto.
    Qcrush.
    replace (S (S (‖ Γ0 ‖))) with (‖ (bind_tm, true, TAll d1 d2 T1 T2, df) :: Γ0 ++ [(bd, bx, Tx, dx)] ‖). rewrite q_trans_fv. rewrite qand_qor_dist_l. erewrite qglb_disjoint_freshv; eauto. rewrite qor_empty_right. rewrite q_trans_extend_tenv_closed_id'.
    rewrite q_trans_extend_tenv_closed_id'. rewrite q_trans_extend_tenv_closed_id'.
    eapply @Subq_trans with (d2:=(q_trans (Γ0 ++ [(bd, bx, Tx, dx)]) Σ dx' ⊓ (q_trans (Γ0 ++ [(bd, bx, Tx, dx)]) Σ (φ ⊔ {♦})))); eauto.
    apply Subq_qand_split; auto. apply q_trans_subq. eapply Subq_trans; eauto.
    rewrite <- q_trans_or_dist. rewrite q_trans_freshv_id. rewrite qand_qor_dist_l.
    rewrite qand_diamond_r_non_fresh. rewrite qor_empty_right; auto. unfold q_trans.
    apply q_trans_senv_wf_senv_non_fresh; auto. unfold q_trans_tenv.
    rewrite q_trans''_closed_id; eauto. Qcrush.
    eapply closed_qenv_qn_shrink in Hqn; eauto.

    rewrite app_length. simpl. rewrite Nat.add_1_r. Qcrush.
    eapply closed_qenv_qn_shrink in Hqn; eauto.
    eapply closed_Nats_mono with (n:=0). Qcrush. lia.
    eapply closed_qenv_qn_shrink in Hqn; eauto.
    eapply closed_qenv_qn_monotone; eauto. simpl. rewrite app_length. lia.
    eapply closed_Nats_mono with (n:=0). Qcrush. lia.
    unfold q_trans,q_trans_tenv. rewrite q_trans''_closed_id; auto.
    unfold q_trans_senv. apply closed_Qual_q_trans''_monotone; eauto. Qcrush.
    simpl. rewrite app_length. simpl. lia.
    inversion H3. subst. constructor. constructor; auto. eapply closed_Qual_monotone; eauto. eapply closed_ty_monotone; eauto. eapply closed_Qual_monotone; eauto.
    apply Substq_weaken. simpl; rewrite app_length; simpl. eapply closed_Qual_monotone; eauto. lia. eapply wf_tenv_closed_qenv_qn. econstructor; eauto.
    apply Substq_weaken; eauto. simpl; rewrite app_length; simpl. eapply closed_Qual_monotone; eauto. lia.
    subst DF. repeat rewrite subst1_qor_dist.
    erewrite <- @subst1_just_fv with (x:=(‖ Γ0 ‖)). erewrite <- @subst1_just_fv with (x:=(S (‖ Γ0 ‖))). rewrite subst1_fresh_id. auto. rewrite app_length. simpl. lia.
  - (* t_tapp *) intuition. rename H8 into IHHT. simpl.
    replace ({ 0 |-> dx' }ᵈ (openq df d1 d2)) with
               (openq ({ 0 |-> dx' }ᵈ df) ({ 0 |-> dx' }ᵈ d1) ({ 0 |-> dx' }ᵈ d2)).
    replace ({0 |-> Tx ~ dx' }ᵀ (T2 <~ᵀ TUnit ~ ∅; T1 ~ d1)) with
               (({0 |-> Tx ~ dx' }ᵀ T2) <~ᵀ TUnit ~ ∅; ({0 |-> Tx ~ dx' }ᵀ T1) ~ ({0 |-> dx' }ᵈ d1)).
    apply t_tapp with (T1:= { 0 |-> Tx ~ dx' }ᵀ T1) (df:=({0 |-> dx' }ᵈ df)).
    replace (TAll ({0 |-> dx' }ᵈ d1) ({0 |-> dx' }ᵈ d2) ({0 |-> Tx ~ dx' }ᵀ T1) ({0 |-> Tx ~ dx' }ᵀ T2))
            with ({ 0 |-> Tx ~ dx' }ᵀ (TAll d1 d2 T1 T2)); auto.
    * eapply closed_ty_subst1; eauto; eapply closed_ty_monotone; eauto. rewrite subst1_env_length,app_length. simpl. lia.
    * eapply closed_qual_subst1; eauto; eapply closed_Qual_monotone; eauto. rewrite subst1_env_length,app_length. simpl. lia.
    * replace (∅) with ({0 |-> dx' }ᵈ ∅) by auto; unfold openq. repeat erewrite <- subst1_open_qual_comm; eauto. erewrite <- subst1_fresh_id. subst φs. rewrite <- subst1_qor_dist. apply subst_qual_subqual_monotone; auto.
    * apply subst1_non_fresh; eauto.
    * apply subst_qual_subqual_monotone. auto.
    * replace (∅) with ({0 |-> dx' }ᵈ ∅) by auto; unfold openq. repeat erewrite <- subst1_open_qual_comm; eauto. apply subst1_senv_saturated; auto.
    * apply subst1_senv_saturated; auto.
    * erewrite <- not_free_subst1_ty_iff; eauto.
    * replace (∅) with ({0 |-> dx' }ᵈ ∅) at 1; auto. unfold open_ty. repeat erewrite subst1_open_ty_comm; eauto.
    * replace (∅) with ({0 |-> dx' }ᵈ ∅) by auto; unfold openq. repeat erewrite <- subst1_open_qual_comm; eauto.
  - (* t_tapp_fresh *) intuition. rename H11 into IHHT. simpl.
    replace ({ 0 |-> dx' }ᵈ (openq df d1 d2)) with
               (openq ({ 0 |-> dx' }ᵈ df) ({ 0 |-> dx' }ᵈ d1) ({ 0 |-> dx' }ᵈ d2)).
    replace ({0 |-> Tx ~ dx' }ᵀ (T2 <~ᵀ TUnit ~ ∅; T1 ~ d1)) with
               (({0 |-> Tx ~ dx' }ᵀ T2) <~ᵀ TUnit ~ ∅; ({0 |-> Tx ~ dx' }ᵀ T1) ~ ({0 |-> dx' }ᵈ d1)).
    (*separation/overap is preserved after substitution*)
    assert (Hoverlap: {0 |-> dx' }ᵈ (q_trans (Γ0 ++ [(bd, bx, Tx, dx)]) Σ df ⊓ q_trans (Γ0 ++ [(bd, bx, Tx, dx)]) Σ d1) = ({0 |-> dx' }ᵈ (q_trans (Γ0 ++ [(bd, bx, Tx, dx)]) Σ df) ⊓ {0 |-> dx' }ᵈ (q_trans (Γ0 ++ [(bd, bx, Tx, dx)]) Σ d1))). {
      erewrite @subst1_qand_saturated' with (dx:=dx) (φ:=q_trans (Γ0 ++ [(bd, bx, Tx, dx)]) Σ φ). auto.
eapply @Subq_trans with (d2:=q_trans (Γ0 ++ [(bd, bx, Tx, dx)]) Σ dx' ⊓ q_trans (Γ0 ++ [(bd, bx, Tx, dx)]) Σ φ ); eauto. apply Subq_qand_split; auto.
eauto. eauto.
1,2: eapply q_trans_subq_fresh; eauto. eapply has_type_filter; eauto.
1,2: unfold q_trans; eapply q_trans_qenv_saturated_q''_tenv; eauto; eapply wf_senv_closed_qenv; eauto.
    }
    eapply t_tapp_fresh with (T1:= { 0 |-> Tx ~ dx' }ᵀ T1) (df:=({0 |-> dx' }ᵈ df)) (d1:=({0 |-> dx' }ᵈ d1)); eauto.
    apply t_sub with (T1:=({0 |-> Tx ~ dx' }ᵀ (TAll (q_trans (Γ0 ++ [(bd, bx, Tx, dx)]) Σ df
                  ⋒ q_trans (Γ0 ++ [(bd, bx, Tx, dx)]) Σ d1) d2 T1 T2))) (d1:=({0 |-> dx' }ᵈ df)). auto.
    simpl. rewrite subst1_qor_dist. rewrite Hoverlap. rewrite subst1_fresh_id. auto. unfold q_trans, q_trans_senv, q_trans_tenv.
(* stp *)
    { inversion HSubst. subst.
      -- repeat erewrite q_trans''_subst1_senv_comm with (T:=Tx); eauto. repeat erewrite q_trans''_subst1_tenv_comm with (Tx:=Tx); eauto. repeat rewrite q_trans''_fuel_max with (fuel:=(‖ Γ0 ++ [(bd, bx, Tx, dx')] ‖)). repeat rewrite subst1_env_length. repeat rewrite wf_senv_subst1_id; eauto. apply has_type_closed in HT. intuition. inversion H13. subst. apply stp_refl.
        + rewrite subst1_env_length,app_length in *. simpl in *. try rewrite Nat.add_1_r in *. constructor.
          apply closed_Qual_qor; auto. apply closed_Qual_qand.
          apply closed_Qual_q_trans''_monotone. apply closed_Qual_q_trans''_monotone. eapply closed_qual_subst1; eauto.

          apply wf_tenv_subst in HwfΓ. apply wf_tenv_closed_qenv in HwfΓ. rewrite subst1_env_length in HwfΓ. auto.
          apply wf_senv_closed_qenv in HwfΣ. eapply closed_qenv_monotone; eauto. lia.
          apply closed_Qual_q_trans''_monotone. apply closed_Qual_q_trans''_monotone. eapply closed_qual_subst1; eauto.
          apply wf_tenv_subst in HwfΓ. apply wf_tenv_closed_qenv in HwfΓ. rewrite subst1_env_length in HwfΓ. auto.
          apply wf_senv_closed_qenv in HwfΣ. eapply closed_qenv_monotone; eauto. lia.
          eapply closed_qual_subst1; eauto.
          1,2: eapply closed_ty_subst1; eauto; eapply closed_ty_monotone; eauto.
        + apply qstp_refl. rewrite app_length,subst1_env_length in *; simpl in *; try rewrite Nat.add_1_r in *. eapply closed_qual_subst1; eauto.
        + rewrite app_length,subst1_env_length in *; simpl in *; try rewrite Nat.add_1_r in *. lia.
        + rewrite app_length,subst1_env_length in *; simpl in *; try rewrite Nat.add_1_r in *. lia.
      -- rename H15 into Heq. repeat erewrite q_trans''_subst1_senv_comm with (T:=Tx); eauto.
         apply has_type_closed in HT as Hcl. intuition. inversion H17. subst. rewrite subst1_env_length,app_length in *. simpl in *. try rewrite Nat.add_1_r in *. constructor; repeat rewrite subst1_env_length.
          constructor. apply closed_Qual_qor; auto. apply closed_Qual_qand.
apply closed_Qual_q_trans''_monotone. eapply closed_qual_subst1; eauto. apply closed_Qual_q_trans''_monotone. eapply closed_Qual_monotone; eauto. rewrite Heq. apply wf_tenv_closed_qenv in HwfΓ. eapply closed_qenv_monotone; eauto. rewrite app_length. simpl. lia.
          apply wf_senv_closed_qenv in HwfΣ. eapply closed_qenv_subst1; eauto. eapply closed_qenv_monotone; eauto. lia. eapply closed_Qual_monotone; eauto. lia.
          apply closed_Qual_q_trans''_monotone. eapply closed_qual_subst1; eauto. apply closed_Qual_q_trans''_monotone. eapply closed_Qual_monotone; eauto. apply wf_tenv_closed_qenv in HwfΓ. eapply closed_qenv_monotone; eauto. rewrite Heq. eapply closed_qenv_monotone; eauto. rewrite app_length. simpl. lia.
          apply wf_senv_closed_qenv in HwfΣ. eapply closed_qenv_subst1; eauto. eapply closed_qenv_monotone; eauto. lia. eapply closed_Qual_monotone; eauto. lia.
          eapply closed_qual_subst1; eauto.
          eapply closed_ty_subst1; eauto.
          eapply closed_ty_subst1; eauto.
          constructor; auto. apply closed_Qual_qor; auto. apply closed_Qual_qand.
          apply closed_Qual_q_trans''_monotone. apply closed_Qual_q_trans''_monotone. eapply closed_qual_subst1; eauto.
rewrite <- Heq in HwfΓ. apply wf_tenv_subst' in HwfΓ; auto. apply wf_tenv_closed_qenv in HwfΓ. rewrite subst1_env_length in HwfΓ. eapply closed_qenv_subst1_monotone; eauto.
apply wf_senv_closed_qenv in HwfΣ. unfold q_trans,q_trans_tenv. rewrite q_trans''_closed_id. apply closed_Qual_q_trans''_monotone; eauto. Qcrush.
apply wf_senv_closed_qenv in HwfΣ. eapply closed_qenv_monotone; eauto. lia.
          apply closed_Qual_q_trans''_monotone. apply closed_Qual_q_trans''_monotone. eapply closed_qual_subst1; eauto.
rewrite <- Heq in HwfΓ. apply wf_tenv_subst' in HwfΓ; auto. apply wf_tenv_closed_qenv in HwfΓ. rewrite subst1_env_length in HwfΓ. auto.
          apply wf_senv_closed_qenv in HwfΣ. eapply closed_qenv_subst1_monotone; eauto.
apply wf_senv_closed_qenv in HwfΣ. unfold q_trans,q_trans_tenv. rewrite q_trans''_closed_id. apply closed_Qual_q_trans''_monotone; eauto. Qcrush.
          apply wf_senv_closed_qenv in HwfΣ. eapply closed_qenv_monotone; eauto. lia.
          eapply closed_qual_subst1; eauto.
          eapply closed_ty_subst1; eauto.
          eapply closed_ty_subst1; eauto.
        + constructor; auto. eapply closed_qual_subst1; eauto. eapply closed_Qual_monotone; eauto. rewrite subst1_env_length. lia.
        + eapply stp_refl'; eauto. eapply closed_ty_subst1; eauto. eapply closed_ty_monotone; eauto. rewrite subst1_env_length. lia. constructor. repeat rewrite wf_senv_subst1_id; eauto. apply Subq_qor. apply Subq_qand_split; eauto; apply q_trans''_subq. 1,2: rewrite Heq; eapply q_trans''_subst1_tenv_subq'; eauto.
          rewrite Heq. rewrite subst1_env_length. apply closed_Qual_qor; auto. apply closed_Qual_qand.
apply closed_Qual_q_trans''_monotone. eapply closed_qual_subst1; eauto. eapply closed_Qual_q_trans''_monotone; eauto. replace (S (‖ Γ0 ‖)) with (‖ Γ0 ++ [(bd, bx, Tx, dx)] ‖). apply wf_tenv_closed_qenv; auto. rewrite app_length. simpl. lia. apply closed_qenv_subst1. eapply closed_qenv_monotone. apply wf_senv_closed_qenv; auto. 1-3: lia. eapply closed_Qual_monotone; eauto. lia.
apply closed_Qual_q_trans''_monotone. eapply closed_qual_subst1; eauto. eapply closed_Qual_q_trans''_monotone; eauto. replace (S (‖ Γ0 ‖)) with (‖ Γ0 ++ [(bd, bx, Tx, dx)] ‖). apply wf_tenv_closed_qenv; auto. rewrite app_length. simpl. lia. apply closed_qenv_subst1. eapply closed_qenv_monotone. apply wf_senv_closed_qenv; auto. 1-3: lia. eapply closed_Qual_monotone; eauto. lia.
        + apply stp_refl. simpl. rewrite subst1_env_length. apply closed_ty_open2; try rewrite subst1_env_length; auto. eapply closed_ty_subst1; eauto. eapply closed_ty_monotone; eauto. 1,2: apply Q_lift_closed; Qcrush. apply qstp_refl. simpl. apply closed_Qual_open2; try rewrite subst1_env_length. eapply closed_qual_subst1; eauto. eapply closed_Qual_monotone; eauto. 1,2: Qcrush.
         }
    apply has_type_filter in HT. subst φs. erewrite <- subst1_fresh_id. rewrite <- subst1_qor_dist. apply subst_qual_subqual_monotone; auto.
    eapply subst1_senv_saturated; eauto. eapply has_type_senv_saturated; eauto.
    1,2 : rewrite subst1_env_length.
    eapply closed_ty_subst1; eauto. eapply closed_ty_monotone; eauto. rewrite app_length. simpl. lia.
    eapply closed_qual_subst1; eauto. eapply closed_Qual_monotone; eauto. rewrite app_length. simpl. lia.
    subst φs. erewrite <- subst1_fresh_id. rewrite <- subst1_qor_dist. apply subst_qual_subqual_monotone; auto.
    erewrite <- not_free_subst1_ty_iff; eauto; apply Substq_non_fresh in HSubst.
    apply subst1_senv_saturated; auto.
    erewrite <- not_free_subst1_ty_iff; eauto; apply Substq_non_fresh in HSubst.
    unfold openq; replace (∅) with ({0 |-> dx' }ᵈ ∅) by solve [apply subst1_qual_empty]; repeat erewrite <- subst1_open_qual_comm; eauto. subst φs. erewrite <- subst1_fresh_id. rewrite <- subst1_qor_dist. apply subst_qual_subqual_monotone; auto.
    apply Subq_qor_l; eauto.
    eapply @Subq_trans with (d2:={0 |-> dx'}ᵈ (q_trans (Γ0 ++ [(bd, bx, Tx, dx)]) Σ d1 ⊓ q_trans (Γ0 ++ [(bd, bx, Tx, dx)]) Σ df)); eauto.
    assert (dx' ⊓ q_trans (Γ0 ++ [(bd, bx, Tx, dx)]) Σ φ ⊑↑ dx). eapply @Subq_trans with (d2:=q_trans (Γ0 ++ [(bd, bx, Tx, dx)]) Σ dx' ⊓ q_trans (Γ0 ++ [(bd, bx, Tx, dx)]) Σ φ); eauto. apply Subq_qand_split; auto.
    erewrite <- @subst1_qand_saturated' with (dx':=dx'); eauto. apply Subq_qand_split; unfold q_trans,q_trans_tenv,q_trans_senv; erewrite q_trans''_subst1_senv_comm'; eauto.
    apply q_trans''_subq. rewrite subst1_env_length,app_length. simpl. rewrite Nat.add_1_r. eapply q_trans''_subst1_tenv_subq'; eauto.
    apply q_trans''_subq. rewrite subst1_env_length,app_length. simpl. rewrite Nat.add_1_r. eapply q_trans''_subst1_tenv_subq'; eauto.
    1,2: apply q_trans_subq_fresh; eauto. eapply has_type_filter; eauto.
    unfold qenv_saturated_q''.  unfold q_trans, q_trans_senv, q_trans_tenv.
    1,2: unfold q_trans; eapply q_trans_qenv_saturated_q''_tenv; eauto; eapply wf_senv_closed_qenv; eauto.
    erewrite <- subst1_fresh_id. subst φs. rewrite <- subst1_qor_dist. apply subst_qual_subqual_monotone. Qcrush.
    unfold openq; rewrite <- @subst1_qual_empty with (dx:=dx').
    erewrite <- subst1_open_qual_comm; eauto. erewrite <- subst1_open_qual_comm; eauto. apply subst1_senv_saturated; auto.
    replace (∅) with ({0 |-> dx' }ᵈ ∅) at 1; auto. unfold open_ty. repeat erewrite subst1_open_ty_comm; eauto.
    unfold openq. repeat erewrite <- subst1_open_qual_comm; eauto.
  - (* t_base *) simpl. replace ({0 |-> dx' }ᵈ ∅) with (∅) by solve [symmetry; apply subst1_qual_empty].
    apply t_base; auto. eapply closed_qual_subst1'; eauto.
  - (* t_var *) simpl. (bdestruct (x =? 0)).
    * (*x is 0 *) rewrite indexr_skips in H0; simpl; auto; try lia. simpl in H0. subst. simpl in H0.
      qual_destruct dx'.
inversion H0. subst. erewrite subst1_ty_id; eauto. inversion HSubst; subst.
        + (*subst fun, dx = dx' *)
          apply vtp_has_type in HTx.
          eapply weaken'; eauto. subst φs. eapply subst_filter0; eauto.
          eapply wf_tenv_subst; eauto.
          eapply closed_qual_subst1'; eauto.
        + (*subst arg, dx = df ⋒ dx = dx' ⋒ φ *)
          apply vtp_has_type in HTx.
          eapply weaken'; eauto.
          eapply @subst_qual_subqual_monotone with (df:=(fr, fvs, bvs, lcs)) in H3.
          subst φs. erewrite subst1_just_fv0 in H3. auto.
          eapply wf_tenv_subst; eauto. eapply wf_tenv_closed_subst; eauto.
          eapply closed_qual_subst1'; eauto.
    * (*x is in Γ0*) assert (Hx: 1 <= x); try lia. destruct x; try lia.
      apply t_var with (b:=b) (d:={0 |-> dx' }ᵈ d). change x with (pred (S x)).
      eapply indexr_subst1; eauto. erewrite subst1_just_fv.
      repeat eapply subst_qual_subqual_monotone. auto.
      eapply closed_qual_subst1'; eauto. simpl. eapply closed_ty_subst1; eauto.
      simpl. eapply closed_qual_subst1; eauto.
  - (* t_abs *) simpl. apply t_abs; auto. eapply closed_tm_subst1'; eauto.
    inversion H3. subst. constructor; try eapply closed_ty_subst1'; eauto; eapply closed_qual_subst1'; eauto.
    eapply closed_qual_subst1'; eauto. Search (_ ⊑↑ _ ⊔ {♦}). apply subst_qual_subqual_monotone_fresh; auto. apply subst_qual_subqual_monotone; auto. eauto.
    apply subst1_senv_saturated; auto.
    (* 1. instantiate the IH *)
    replace (length (Γ0 ++ [(bd, bx, Tx, dx)])) with (S (‖Γ0‖)) in IHHT.
    rewrite subst1_env_length. rewrite app_comm_cons in IHHT. rewrite app_comm_cons in IHHT.
    remember (df ⊔ $!(S (‖Γ0‖)) ⊔ $!(S (S (‖Γ0‖))) ⊔ {♦}) as DF.
    replace ({0 |-> dx' }ᵈ df ⊔ $!(‖Γ0‖) ⊔ $!(S (‖Γ0‖)) ⊔ {♦}) with ({0 |-> dx' }ᵈ DF).
    intuition. specialize IHHT with (Γ := (((bind_tm, false,T1, d1) :: (bind_tm, true, (TFun d1 d2 T1 T2), df) :: Γ0))).
    (* 2. reason about opening and subst, apply IH *)
    unfold open_tm' in *. unfold open_ty' in *. unfold open_ty in *.
    unfold openq' in *. unfold openq in *.
    rewrite app_length in IHHT. rewrite subst1_env_length. simpl in *.
    replace (‖Γ0‖ + 1) with (S (‖Γ0‖)) in IHHT; try lia.
    erewrite <- open_subst1_tm_comm in IHHT; eauto. erewrite <- open_subst1_tm_comm in IHHT; eauto.
    erewrite <- open_subst1_ty_comm in IHHT; eauto. erewrite <- open_subst1_ty_comm in IHHT; eauto.
    erewrite <- open_subst1_qual_comm in IHHT; eauto. erewrite <- open_subst1_qual_comm in IHHT; eauto. repeat erewrite subst1_qor_dist in IHHT. apply IHHT; auto.
    apply has_type_filter in HT as Hft.
    subst.
    inversion H3. subst. rewrite app_length in *. simpl in *. rewrite Nat.add_1_r in *.
    repeat rewrite <- q_trans_or_dist. repeat rewrite qand_qor_dist_l. assert (Hqn: closed_qenv_qn (S (‖ Γ0 ‖)) ((bind_ty, false, T1, d1) :: (bind_tm, true, TFun d1 d2 T1 T2, df) :: Γ0 ++ [(bd, bx, Tx, dx)])). {
      unfold closed_qenv_qn. intros.
    bdestruct (x =? (S (S (‖ Γ0 ‖)))). replace x with (‖ (bind_tm, true, TFun d1 d2 T1 T2, df) :: Γ0 ++ [(bd, bx, Tx, dx)] ‖) in *. rewrite indexr_head in H9. inversion H9. subst. simpl. Qcrush. subst. simpl. rewrite app_length. simpl. lia.
    bdestruct (x =? (S (‖ Γ0 ‖))). replace x with (‖ Γ0 ++ [(bd, bx, Tx, dx)] ‖) in *. rewrite indexr_skip in H9; auto. rewrite indexr_head in H9. inversion H9. subst. simpl. Qcrush. subst. simpl. rewrite app_length. simpl. lia.
    rewrite indexr_skip in H9; auto. rewrite indexr_skip in H9; auto. destruct a as [ [ [ b fr ] T' ] q']. eapply wf_tenv_prop in HwfΓ; eauto. simpl. apply indexr_var_some' in H9. rewrite app_length in *. simpl in *. rewrite Nat.add_1_r in *. eapply closed_Nats_mono; eauto. Qcrush. 1,2: subst; simpl; rewrite app_length; simpl; lia.
    }
    repeat apply Subq_qor_l. unfold q_trans,q_trans_tenv. repeat erewrite q_trans''_extend_closed_id'. rewrite q_trans''_fuel_max. eapply @Subq_trans with (d2:=(q_trans (Γ0 ++ [(bd, bx, Tx, dx)]) Σ dx' ⊓ q_trans (Γ0 ++ [(bd, bx, Tx, dx)]) Σ φ)); eauto. unfold q_trans,q_trans_tenv. eapply Subq_qand_split; eauto.
    repeat eapply q_trans''_subq; eauto. rewrite q_trans''_fuel_max. apply q_trans''_subq; auto. 1,2: simpl; lia.
    eapply closed_qenv_qn_monotone; eauto.
    1-3: simpl; rewrite app_length; simpl; rewrite Nat.add_1_r.
    Qcrush.
    eapply closed_qenv_qn_shrink in Hqn; eauto.
    Qcrush.
    eapply closed_qenv_qn_shrink in Hqn; eauto.
    eapply closed_Nats_mono with (n:=0). Qcrush. lia.
    eapply closed_qenv_qn_shrink in Hqn; eauto. simpl. eapply closed_qenv_qn_monotone; eauto. rewrite app_length. lia.
    eapply closed_Nats_mono with (n:=0). Qcrush. lia.
    erewrite q_trans_extend_tenv_closed_id' with (q':=$! (S (‖ Γ0 ‖))). replace (S (‖ Γ0 ‖)) with (‖ Γ0 ++ [(bd, bx, Tx, dx)] ‖). rewrite q_trans_fv. rewrite qand_qor_dist_l. erewrite qglb_disjoint_freshv; eauto. rewrite qor_empty_right. repeat erewrite q_trans_extend_tenv_closed_id'. eapply @Subq_trans with (d2:=(q_trans (Γ0 ++ [(bd, bx, Tx, dx)]) Σ dx' ⊓ q_trans (Γ0 ++ [(bd, bx, Tx, dx)]) Σ φ)); eauto. apply Subq_qand_split; auto.
    eapply closed_qenv_qn_shrink in Hqn; eauto.
    eapply closed_Nats_mono with (n:=0). Qcrush. lia.
    eapply closed_qenv_qn_shrink in Hqn; eauto.
    simpl. eapply closed_qenv_qn_monotone; eauto.
    rewrite app_length. simpl. lia.
    eapply closed_Nats_mono with (n:=0). Qcrush. lia.
    apply closed_Qual_q_trans''_monotone; eauto using wf_senv_closed_qenv.
    unfold q_trans_tenv. rewrite q_trans''_closed_id; auto. Qcrush.
    simpl; rewrite app_length; simpl; lia.
    1,2: simpl; rewrite app_length; simpl; rewrite Nat.add_1_r.
    eapply closed_qenv_qn_shrink in Hqn; eauto.
    Qcrush.
    replace (S (S (‖ Γ0 ‖))) with (‖ (bind_tm, true, TFun d1 d2 T1 T2, df) :: Γ0 ++ [(bd, bx, Tx, dx)] ‖). rewrite q_trans_fv. rewrite qand_qor_dist_l. erewrite qglb_disjoint_freshv; eauto. rewrite qor_empty_right. rewrite q_trans_extend_tenv_closed_id'.
    eapply @Subq_trans with (d2:=(q_trans ((bind_tm, true, TFun d1 d2 T1 T2, df) :: Γ0 ++ [(bd, bx, Tx, dx)]) Σ dx' ⊓ (q_trans ((bind_tm, true, TFun d1 d2 T1 T2, df) :: Γ0 ++ [(bd, bx, Tx, dx)]) Σ (φ ⊔ {♦})))); eauto.
    apply Subq_qand_split; auto.
    apply q_trans_subq. eapply Subq_trans; eauto.
    rewrite <- q_trans_or_dist. rewrite q_trans_freshv_id. rewrite qand_qor_dist_l. rewrite qand_diamond_r_non_fresh. rewrite qor_empty_right; auto.
    repeat rewrite q_trans_extend_tenv_closed_id'; auto.

    eapply closed_qenv_qn_shrink in Hqn; eauto.
    simpl; rewrite app_length; simpl; rewrite Nat.add_1_r. Qcrush.
    eapply closed_qenv_qn_shrink in Hqn; eauto.
    eapply closed_Nats_mono with (n:=0). Qcrush. lia.
    unfold q_trans. apply q_trans_senv_wf_senv_non_fresh; auto. unfold q_trans_tenv. rewrite q_trans''_closed_id; eauto. Qcrush.
    eapply closed_qenv_qn_shrink in Hqn; eauto.
    simpl. eapply closed_qenv_qn_monotone; eauto.
    rewrite app_length. simpl. lia.
    eapply closed_Nats_mono with (n:=0). Qcrush. lia.
    apply closed_Qual_q_trans''_monotone; eauto using wf_senv_closed_qenv.
    unfold q_trans_tenv. rewrite q_trans''_closed_id; auto. Qcrush.
    simpl. rewrite app_length. simpl. lia.
    inversion H3. subst. constructor. constructor; auto. eapply closed_Qual_monotone; eauto. eapply closed_ty_monotone; eauto. eapply closed_Qual_monotone; eauto.
    apply Substq_weaken. simpl; rewrite app_length; simpl. eapply closed_Qual_monotone; eauto. lia. eapply wf_tenv_closed_qenv_qn. econstructor; eauto.
    apply Substq_weaken; eauto. simpl; rewrite app_length; simpl. eapply closed_Qual_monotone; eauto. lia.
    subst DF. repeat rewrite subst1_qor_dist.
    erewrite <- @subst1_just_fv with (x:=(‖ Γ0 ‖)). erewrite <- @subst1_just_fv with (x:=(S (‖ Γ0 ‖))). rewrite subst1_fresh_id. auto. rewrite app_length. simpl. lia.

  - (* t_app *) intuition. rename H8 into IHHT1. rename H7 into IHHT2. simpl.
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
    * replace (∅) with ({0 |-> dx' }ᵈ ∅) by auto; unfold openq. repeat erewrite <- subst1_open_qual_comm; eauto. erewrite <- subst1_fresh_id. subst φs. rewrite <- subst1_qor_dist. apply subst_qual_subqual_monotone; auto.
    * replace (∅) with ({0 |-> dx' }ᵈ ∅) by auto; unfold openq. repeat erewrite <- subst1_open_qual_comm; eauto. apply subst1_senv_saturated; auto.
    * apply subst1_non_fresh; eauto.
    * erewrite <- not_free_subst1_ty_iff; eauto.
    * replace (∅) with ({0 |-> dx' }ᵈ ∅) at 1; auto. unfold open_ty. repeat erewrite subst1_open_ty_comm; eauto.
    * unfold openq. repeat erewrite <- subst1_open_qual_comm; eauto.

  - (* t_app_fresh *) intuition. rename H9 into IHHT1. rename H8 into IHHT2. simpl.
    replace ({ 0 |-> dx' }ᵈ (openq df d1 d2)) with
               (openq ({ 0 |-> dx' }ᵈ df) ({ 0 |-> dx' }ᵈ d1) ({ 0 |-> dx' }ᵈ d2)).
    replace ({0 |-> Tx ~ dx' }ᵀ (T2 <~ᵀ TUnit ~ ∅; T1 ~ d1)) with
               (({0 |-> Tx ~ dx' }ᵀ T2) <~ᵀ TUnit ~ ∅; ({0 |-> Tx ~ dx' }ᵀ T1) ~ ({0 |-> dx' }ᵈ d1)).
    (*separation/overap is preserved after substitution*)
    assert (Hoverlap: {0 |-> dx' }ᵈ (q_trans (Γ0 ++ [(bd, bx, Tx, dx)]) Σ df ⊓ q_trans (Γ0 ++ [(bd, bx, Tx, dx)]) Σ d1) = {0 |-> dx' }ᵈ (q_trans (Γ0 ++ [(bd, bx, Tx, dx)]) Σ df) ⊓ {0 |-> dx' }ᵈ (q_trans (Γ0 ++ [(bd, bx, Tx, dx)]) Σ d1)). {
      erewrite @subst1_qand_saturated' with (dx:=dx) (φ:=q_trans (Γ0 ++ [(bd, bx, Tx, dx)]) Σ φ). auto.
      eapply @Subq_trans with (d2:=q_trans (Γ0 ++ [(bd, bx, Tx, dx)]) Σ dx' ⊓ q_trans (Γ0 ++ [(bd, bx, Tx, dx)]) Σ φ); eauto.
      apply Subq_qand_split; auto.
      eauto. eauto. 1,2: eapply q_trans_subq_fresh; eapply has_type_filter; eauto.
      1,2: unfold q_trans; eapply q_trans_qenv_saturated_q''_tenv; eauto; eapply wf_senv_closed_qenv; eauto.
    }
    eapply t_app_fresh with (T1:= { 0 |-> Tx ~ dx' }ᵀ T1) (df:=({0 |-> dx' }ᵈ df)) (d1:=({0 |-> dx' }ᵈ d1)); eauto.
    apply t_sub with (T1:=({0 |-> Tx ~ dx' }ᵀ (TFun (q_trans (Γ0 ++ [(bd, bx, Tx, dx)]) Σ df
                  ⋒ q_trans (Γ0 ++ [(bd, bx, Tx, dx)]) Σ d1) d2 T1 T2))) (d1:=({0 |-> dx' }ᵈ df)). auto.
    simpl. rewrite subst1_qor_dist. rewrite Hoverlap. rewrite subst1_fresh_id. auto. unfold q_trans, q_trans_senv, q_trans_tenv.
(* stp *)
    { inversion HSubst. subst.
      -- repeat erewrite q_trans''_subst1_senv_comm with (T:=Tx); eauto. repeat erewrite q_trans''_subst1_tenv_comm with (Tx:=Tx); eauto. repeat rewrite q_trans''_fuel_max with (fuel:=(‖ Γ0 ++ [(bd, bx, Tx, dx')] ‖)). repeat rewrite subst1_env_length. repeat rewrite wf_senv_subst1_id; eauto. apply has_type_closed in HT1, HT2. intuition. inversion H11. subst. apply stp_refl.
        + rewrite subst1_env_length,app_length in *. simpl in *. try rewrite Nat.add_1_r in *. constructor.
          apply closed_Qual_qor; auto. apply closed_Qual_qand.
          apply closed_Qual_q_trans''_monotone. apply closed_Qual_q_trans''_monotone. eapply closed_qual_subst1; eauto.

          apply wf_tenv_subst in HwfΓ. apply wf_tenv_closed_qenv in HwfΓ. rewrite subst1_env_length in HwfΓ. auto.
          apply wf_senv_closed_qenv in HwfΣ. eapply closed_qenv_monotone; eauto. lia.
          apply closed_Qual_q_trans''_monotone. apply closed_Qual_q_trans''_monotone. eapply closed_qual_subst1; eauto.
          apply wf_tenv_subst in HwfΓ. apply wf_tenv_closed_qenv in HwfΓ. rewrite subst1_env_length in HwfΓ. auto.
          apply wf_senv_closed_qenv in HwfΣ. eapply closed_qenv_monotone; eauto. lia.
          eapply closed_qual_subst1; eauto.
          1,2: eapply closed_ty_subst1; eauto; eapply closed_ty_monotone; eauto.
        + apply qstp_refl. rewrite app_length,subst1_env_length in *; simpl in *; try rewrite Nat.add_1_r in *. eapply closed_qual_subst1; eauto.
        + rewrite app_length,subst1_env_length in *; simpl in *; try rewrite Nat.add_1_r in *. lia.
        + rewrite app_length,subst1_env_length in *; simpl in *; try rewrite Nat.add_1_r in *. lia.
      -- rename H11 into Heq. repeat erewrite q_trans''_subst1_senv_comm with (T:=Tx); eauto.
         apply has_type_closed in HT1 as Hcl,HT2 as Hcl2. intuition. inversion H15. subst. rewrite subst1_env_length,app_length in *. simpl in *. try rewrite Nat.add_1_r in *. constructor; repeat rewrite subst1_env_length.
          constructor. apply closed_Qual_qor; auto. apply closed_Qual_qand.
apply closed_Qual_q_trans''_monotone. eapply closed_qual_subst1; eauto. apply closed_Qual_q_trans''_monotone. eapply closed_Qual_monotone; eauto. rewrite Heq. apply wf_tenv_closed_qenv in HwfΓ. eapply closed_qenv_monotone; eauto. rewrite app_length. simpl. lia.
          apply wf_senv_closed_qenv in HwfΣ. eapply closed_qenv_subst1; eauto. eapply closed_qenv_monotone; eauto. lia. eapply closed_Qual_monotone; eauto. lia.
          apply closed_Qual_q_trans''_monotone. eapply closed_qual_subst1; eauto. apply closed_Qual_q_trans''_monotone. eapply closed_Qual_monotone; eauto. apply wf_tenv_closed_qenv in HwfΓ. eapply closed_qenv_monotone; eauto. rewrite Heq. eapply closed_qenv_monotone; eauto. rewrite app_length. simpl. lia.
          apply wf_senv_closed_qenv in HwfΣ. eapply closed_qenv_subst1; eauto. eapply closed_qenv_monotone; eauto. lia. eapply closed_Qual_monotone; eauto. lia.
          eapply closed_qual_subst1; eauto.
          eapply closed_ty_subst1; eauto.
          eapply closed_ty_subst1; eauto.
          constructor; auto. apply closed_Qual_qor; auto. apply closed_Qual_qand.
          apply closed_Qual_q_trans''_monotone. apply closed_Qual_q_trans''_monotone. eapply closed_qual_subst1; eauto.
rewrite <- Heq in HwfΓ. apply wf_tenv_subst' in HwfΓ; auto. apply wf_tenv_closed_qenv in HwfΓ. rewrite subst1_env_length in HwfΓ. eapply closed_qenv_subst1_monotone; eauto.
apply wf_senv_closed_qenv in HwfΣ. unfold q_trans,q_trans_tenv. rewrite q_trans''_closed_id. apply closed_Qual_q_trans''_monotone; eauto. Qcrush.
apply wf_senv_closed_qenv in HwfΣ. eapply closed_qenv_monotone; eauto. lia.
          apply closed_Qual_q_trans''_monotone. apply closed_Qual_q_trans''_monotone. eapply closed_qual_subst1; eauto.
rewrite <- Heq in HwfΓ. apply wf_tenv_subst' in HwfΓ; auto. apply wf_tenv_closed_qenv in HwfΓ. rewrite subst1_env_length in HwfΓ. auto.
          apply wf_senv_closed_qenv in HwfΣ. eapply closed_qenv_subst1_monotone; eauto.
apply wf_senv_closed_qenv in HwfΣ. unfold q_trans,q_trans_tenv. rewrite q_trans''_closed_id. apply closed_Qual_q_trans''_monotone; eauto. Qcrush.
          apply wf_senv_closed_qenv in HwfΣ. eapply closed_qenv_monotone; eauto. lia.
          eapply closed_qual_subst1; eauto.
          eapply closed_ty_subst1; eauto.
          eapply closed_ty_subst1; eauto.
        + constructor; auto. eapply closed_qual_subst1; eauto. eapply closed_Qual_monotone; eauto. rewrite subst1_env_length. lia.
        + eapply stp_refl'; eauto. eapply closed_ty_subst1; eauto. eapply closed_ty_monotone; eauto. rewrite subst1_env_length. lia. constructor. repeat rewrite wf_senv_subst1_id; eauto. apply Subq_qor. apply Subq_qand_split; eauto; apply q_trans''_subq. 1,2: rewrite Heq; eapply q_trans''_subst1_tenv_subq'; eauto.
          rewrite Heq. rewrite subst1_env_length. apply closed_Qual_qor; auto. apply closed_Qual_qand.
apply closed_Qual_q_trans''_monotone. eapply closed_qual_subst1; eauto. eapply closed_Qual_q_trans''_monotone; eauto. replace (S (‖ Γ0 ‖)) with (‖ Γ0 ++ [(bd, bx, Tx, dx)] ‖). apply wf_tenv_closed_qenv; auto. rewrite app_length. simpl. lia. apply closed_qenv_subst1. eapply closed_qenv_monotone. apply wf_senv_closed_qenv; auto. 1-3: lia. eapply closed_Qual_monotone; eauto. lia.
apply closed_Qual_q_trans''_monotone. eapply closed_qual_subst1; eauto. eapply closed_Qual_q_trans''_monotone; eauto. replace (S (‖ Γ0 ‖)) with (‖ Γ0 ++ [(bd, bx, Tx, dx)] ‖). apply wf_tenv_closed_qenv; auto. rewrite app_length. simpl. lia. apply closed_qenv_subst1. eapply closed_qenv_monotone. apply wf_senv_closed_qenv; auto. 1-3: lia. eapply closed_Qual_monotone; eauto. lia.
        + apply stp_refl. simpl. rewrite subst1_env_length. apply closed_ty_open2; try rewrite subst1_env_length; auto. eapply closed_ty_subst1; eauto. eapply closed_ty_monotone; eauto. 1,2: apply Q_lift_closed; Qcrush. apply qstp_refl. simpl. apply closed_Qual_open2; try rewrite subst1_env_length. eapply closed_qual_subst1; eauto. eapply closed_Qual_monotone; eauto. 1,2: Qcrush.
         }

    apply has_type_filter in HT1. subst φs. erewrite <- subst1_fresh_id. rewrite <- subst1_qor_dist. apply subst_qual_subqual_monotone; auto.
    eapply subst1_senv_saturated; eauto. eapply has_type_senv_saturated; eauto.
    erewrite <- not_free_subst1_ty_iff; eauto; apply Substq_non_fresh in HSubst.
    erewrite <- not_free_subst1_ty_iff; eauto; apply Substq_non_fresh in HSubst.
    unfold openq; replace (∅) with ({0 |-> dx' }ᵈ ∅) by solve [apply subst1_qual_empty]; repeat erewrite <- subst1_open_qual_comm; eauto. subst φs. erewrite <- subst1_fresh_id. rewrite <- subst1_qor_dist. apply subst_qual_subqual_monotone; auto.
    apply Subq_qor_l; eauto.
    eapply @Subq_trans with (d2:={0 |-> dx'}ᵈ (q_trans (Γ0 ++ [(bd, bx, Tx, dx)]) Σ d1 ⊓ q_trans (Γ0 ++ [(bd, bx, Tx, dx)]) Σ df)); eauto.
    assert (dx' ⊓ q_trans (Γ0 ++ [(bd, bx, Tx, dx)]) Σ φ ⊑↑ dx). eapply @Subq_trans with (d2:=q_trans (Γ0 ++ [(bd, bx, Tx, dx)]) Σ dx' ⊓ q_trans (Γ0 ++ [(bd, bx, Tx, dx)]) Σ φ); eauto. apply Subq_qand_split; auto.
    erewrite <- @subst1_qand_saturated' with (dx':=dx'); eauto. apply Subq_qand_split; unfold q_trans,q_trans_tenv,q_trans_senv; erewrite q_trans''_subst1_senv_comm'; eauto.
    apply q_trans''_subq. rewrite subst1_env_length,app_length. simpl. rewrite Nat.add_1_r. eapply q_trans''_subst1_tenv_subq'; eauto.
    apply q_trans''_subq. rewrite subst1_env_length,app_length. simpl. rewrite Nat.add_1_r. eapply q_trans''_subst1_tenv_subq'; eauto.
    1,2: apply q_trans_subq_fresh; eapply has_type_filter; eauto.
    unfold qenv_saturated_q''.  unfold q_trans, q_trans_senv, q_trans_tenv.
    1,2: unfold q_trans; eapply q_trans_qenv_saturated_q''_tenv; eauto; eapply wf_senv_closed_qenv; eauto.
    erewrite <- subst1_fresh_id. subst φs. rewrite <- subst1_qor_dist. apply subst_qual_subqual_monotone. Qcrush.
    unfold openq; rewrite <- @subst1_qual_empty with (dx:=dx').
    erewrite <- subst1_open_qual_comm; eauto; erewrite <- subst1_open_qual_comm; eauto. apply subst1_senv_saturated; auto.
    replace (∅) with ({0 |-> dx' }ᵈ ∅) at 1; auto. unfold open_ty. repeat erewrite subst1_open_ty_comm; eauto.
    unfold openq. repeat erewrite <- subst1_open_qual_comm; eauto.
  - (* t_loc *) rewrite subst1_qor_dist. erewrite @subst1_qual_id with (q:=(&!l)); eauto. simpl. erewrite subst1_ty_id; eauto.
    erewrite subst1_qual_id; eauto. apply t_loc; auto. eapply closed_qual_subst1'; eauto.
    erewrite <- @subst1_qual_id with (q:=(&!l)); eauto. eapply subst_qual_subqual_monotone; eauto.
    2 : erewrite <- @subst1_qual_id with (q:=q); eauto; eapply subst_qual_subqual_monotone; eauto.
    all : apply indexr_var_some' in H3; eapply just_loc_closed; eauto.
  - (* t_ref *) rewrite subst1_qor_dist. rewrite subst1_fresh_id. simpl. apply t_ref; auto.
    eapply closed_ty_subst1'; eauto. apply subst1_non_fresh; eauto.
  - (* t_deref *) simpl. apply t_deref with (d := { 0 |-> dx' }ᵈ d); auto.
    apply subst1_non_fresh; eauto. apply subst_qual_subqual_monotone. auto.
    apply subst1_senv_saturated; auto.
  - (* t_assign *) rewrite subst1_qual_empty in *. simpl. simpl in IHHT1.
    apply t_assign with (T:={0 |-> Tx ~ dx' }ᵀ T) (d:=({0 |-> dx' }ᵈ d)) (d1:=({0 |-> dx' }ᵈ d1)); auto.
    apply subst1_non_fresh; eauto.
  - (* t_sub *) apply t_sub with (T1:={ 0 |-> Tx ~ dx' }ᵀ T1) (d1:={ 0 |-> dx' }ᵈ d1).
    eapply IHHT; eauto. eapply subst_stp; eauto. erewrite <- subst1_fresh_id. subst φs. rewrite <- subst1_qor_dist. apply subst_qual_subqual_monotone; auto. apply subst1_senv_saturated; auto.
  Unshelve. apply bind_tm. all : auto.
Qed.

(* case for t_app and t_tapp *)
Lemma substitution1 : forall {t bdx bdf bf Tf df bx Tx dx Σ T d},
    has_type [(bdx, bx,Tx,dx) ; (bdf, bf,Tf,df)] (df ⊔ $!0 ⊔ $!1) Σ t T d ->
    wf_senv Σ ->
    forall {vf φ}, vtp Σ φ vf Tf df -> ♦∉ df ->
        forall {vx φ'}, vtp Σ φ' vx Tx dx -> ♦∉ dx ->
                    has_type [] (df ⊔ dx) Σ
                             ({ 0 |-> vf ; vx }ᵗ t)
                             ({ 0 |-> Tf ~ df ; Tx ~ dx }ᵀ T)
                             ({ 0 |-> df ; dx }ᵈ d).
  intros. specialize (vtp_closed H1) as Hclf. specialize (vtp_closed H3) as Hclx.
  intuition. replace ([(bdx, bx,Tx, dx); (bdf, bf,Tf, df)]) with ([(bdx, bx,Tx,dx)] ++ [(bdf, bf,Tf, df)]) in H; auto.
  (* substitute the first free variable df *)
  assert (Hsepf : (q_trans ([(bdx, bx, Tx, dx)] ++ [(bdf, bf, Tf, df)]) Σ df) ⊓ (q_trans ([(bdx, bx, Tx, dx)] ++ [(bdf, bf, Tf, df)]) Σ (df ⊔ $!0 ⊔ $!1)) ⊑↑ df). { unfold q_trans,q_trans_tenv,q_trans_senv. rewrite qenv_saturated_trans''_id; auto. rewrite q_trans''_closed_id. apply qand_Sub_l. Qcrush. pose proof (vtp_saturated H1). inversion H8. apply qenv_saturated_iff in H13. rewrite q_trans''_closed_id; auto. Qcrush. }
  eapply (substitution_gen Hsepf) in H; eauto.
  (* substitute the second free variable dx *)
  replace ({0 |-> Tf ~ df }ᴳ [(bdx, bx, Tx, dx)]) with ([] ++ [(bdx, bx, Tx, dx)]) in H.
  replace ({0 |-> df }ᵈ (df ⊔ $! 0 ⊔ $! 1)) with (df ⊔ $!0) in H.
  assert (Hsepf' : (q_trans ([] ++ [(bdx, bx, Tx, dx)]) Σ dx) ⊓ (q_trans ([] ++ [(bdx, bx, Tx, dx)]) Σ (df ⊔ $!0)) ⊑↑ dx). { unfold q_trans,q_trans_tenv,q_trans_senv. rewrite qenv_saturated_trans''_id; auto. rewrite q_trans''_closed_id. apply qand_Sub_l. Qcrush. pose proof (vtp_saturated H3). inversion H8. apply qenv_saturated_iff in H13. rewrite q_trans''_closed_id; auto. Qcrush. }
  eapply (substitution_gen Hsepf') in H; eauto.
  replace ({0 |-> dx }ᵈ (df ⊔ $!0)) with (df ⊔ dx) in H. simpl in H. apply H.
  repeat rewrite subst1_qor_dist. rewrite subst1_just_fv0. erewrite subst1_qual_id; eauto.
  constructor; auto.
  subst. repeat rewrite subst1_qor_dist. rewrite subst1_just_fv0. rewrite <- subst1_just_fv.
  erewrite subst1_qual_id; eauto.
  rewrite (@qor_assoc df df).
  rewrite qor_idem. auto.
  simpl. erewrite subst1_qual_id; eauto. erewrite subst1_ty_id; eauto.
  constructor; auto; simpl. eapply closed_ty_monotone; eauto. eapply closed_Qual_monotone; eauto.
Qed.

Lemma substitution_ty_gen :
  forall {t Γ φ bx Tx dx dx' Σ T d}, (q_trans (Γ ++ [(bind_ty, bx,Tx,dx)]) Σ dx') ⊓ (q_trans (Γ ++ [(bind_ty, bx,Tx,dx)]) Σ φ) ⊑↑ dx ->
  has_type (Γ ++ [(bind_ty, bx,Tx,dx)]) φ Σ t T d ->
  wf_tenv (Γ ++ [(bind_ty, bx,Tx,dx)]) Σ ->
  wf_senv Σ ->
  Substq (Γ ++ [(bind_ty, bx,Tx,dx)]) Σ dx dx' ->
  closed_ty 0 0 (length Σ) Tx ->
  closed_Qual 0 0 (length Σ) dx↑ ->
  closed_Qual 0 0 (length Σ) dx'↑ ->
  senv_saturated Σ dx' ->
  has_type ({ 0 |-> Tx ~ dx' }ᴳ Γ) ({ 0 |-> dx' }ᵈ φ) Σ
                                   ({ 0 |-> tunit  }ᵗ t)
                                   ({ 0 |-> Tx ~  dx' }ᵀ T)
                                   ({ 0 |-> dx' }ᵈ d).
  intros t Γ φ bx Tx dx dx' Σ T d Hsep (* φ Hphi *) HT HwfΓ HwfΣ HSubst Hcl Hcl' Hcl'' Hsat.
  remember (Γ ++ [(bind_ty, bx,Tx, dx)]) as Γ'.
  generalize dependent Γ.
  induction HT; intros; subst; pose (φs := {0 |-> dx' }ᵈ φ); replace ({0 |-> dx' }ᵈ φ) with φs in *; auto.
  - (* t_tabs *) simpl. apply t_tabs; auto. eapply closed_tm_subst1'; eauto.
    inversion H0. subst. constructor; try eapply closed_ty_subst1'; eauto; eapply closed_qual_subst1'; eauto.
    eapply closed_qual_subst1'; eauto. apply subst_qual_subqual_monotone_fresh; auto. apply subst_qual_subqual_monotone; auto. eauto.
    apply subst1_senv_saturated; auto.
    (* 1. instantiate the IH *)
    replace (length (Γ0 ++ [(bind_ty, bx, Tx, dx)])) with (S (‖Γ0‖)) in IHHT.
    rewrite subst1_env_length. rewrite app_comm_cons in IHHT. rewrite app_comm_cons in IHHT.
    remember (df ⊔ $!(S (‖Γ0‖)) ⊔ $!(S (S (‖Γ0‖)))) as DF.
    replace ({0 |-> dx' }ᵈ df ⊔ $!(‖Γ0‖) ⊔ $!(S (‖Γ0‖))) with ({0 |-> dx' }ᵈ DF).
    intuition. specialize IHHT with (Γ := (((bind_ty, false,T1, d1) :: (bind_tm, true, (TAll d1 d2 T1 T2), df) :: Γ0))).
    (* 2. reason about opening and subst, apply IH *)
    unfold open_tm' in *. unfold open_ty' in *. unfold open_ty in *.
    unfold openq' in *. unfold openq in *.
    rewrite app_length in IHHT. rewrite subst1_env_length. simpl in *.
    replace (‖Γ0‖ + 1) with (S (‖Γ0‖)) in IHHT; try lia.
    erewrite <- open_subst1_tm_comm in IHHT; eauto. erewrite <- open_subst1_tm_comm in IHHT; eauto.
    erewrite <- open_subst1_ty_comm in IHHT; eauto. erewrite <- open_subst1_ty_comm in IHHT; eauto.
    erewrite <- open_subst1_qual_comm in IHHT; eauto. erewrite <- open_subst1_qual_comm in IHHT; eauto. repeat erewrite subst1_qor_dist in IHHT. apply IHHT; auto.
    apply has_type_filter in HT as Hft.
    subst.
    inversion H0. subst. rewrite app_length in *. simpl in *. rewrite Nat.add_1_r in *.
    repeat rewrite <- q_trans_or_dist. repeat rewrite qand_qor_dist_l. assert (Hqn: closed_qenv_qn (S (‖ Γ0 ‖)) ((bind_ty, false, T1, d1) :: (bind_tm, true, TAll d1 d2 T1 T2, df) :: Γ0 ++ [(bind_ty, bx, Tx, dx)])). {
      unfold closed_qenv_qn. intros.
      bdestruct (x =? (S (S (‖ Γ0 ‖)))). replace x with (‖ (bind_tm, true, TAll d1 d2 T1 T2, df) :: Γ0 ++ [(bind_ty, bx, Tx, dx)] ‖) in *. rewrite indexr_head in H6. inversion H6. subst. simpl. Qcrush. subst. simpl. rewrite app_length. simpl. lia.
      bdestruct (x =? (S (‖ Γ0 ‖))). replace x with (‖ Γ0 ++ [(bind_ty, bx, Tx, dx)] ‖) in *. rewrite indexr_skip in H6; auto. rewrite indexr_head in H6. inversion H6. subst. simpl. Qcrush. subst. simpl. rewrite app_length. simpl. lia.
      rewrite indexr_skip in H6; auto. rewrite indexr_skip in H6; auto. destruct a as [ [ [ b fr ] T' ] q']. eapply wf_tenv_prop in HwfΓ; eauto. simpl. apply indexr_var_some' in H6. rewrite app_length in *. simpl in *. rewrite Nat.add_1_r in *. eapply closed_Nats_mono; eauto. Qcrush. 1,2: subst; simpl; rewrite app_length; simpl; lia.
    }
    repeat apply Subq_qor_l. unfold q_trans,q_trans_tenv. repeat erewrite q_trans''_extend_closed_id'. rewrite q_trans''_fuel_max. eapply @Subq_trans with (d2:=(q_trans (Γ0 ++ [(bind_ty, bx, Tx, dx)]) Σ dx' ⊓ q_trans (Γ0 ++ [(bind_ty, bx, Tx, dx)]) Σ φ)); eauto. unfold q_trans,q_trans_tenv.
    eapply Subq_qand_split; eauto.
    repeat eapply q_trans''_subq; eauto. rewrite q_trans''_fuel_max. apply q_trans''_subq; auto. 1,2: simpl; lia.
    eapply closed_qenv_qn_monotone; eauto.
    1-3: simpl; rewrite app_length; simpl; rewrite Nat.add_1_r.
    Qcrush.
    eapply closed_qenv_qn_shrink in Hqn; eauto.
    Qcrush.
    eapply closed_qenv_qn_shrink in Hqn; eauto.
    eapply closed_Nats_mono with (n:=0). Qcrush. lia.
    eapply closed_qenv_qn_shrink in Hqn; eauto. simpl. eapply closed_qenv_qn_monotone; eauto. rewrite app_length. lia.
    eapply closed_Nats_mono with (n:=0). Qcrush. lia.
    erewrite q_trans_extend_tenv_closed_id' with (q':=$! (S (‖ Γ0 ‖))). replace (S (‖ Γ0 ‖)) with (‖ Γ0 ++ [(bind_ty, bx, Tx, dx)] ‖). rewrite q_trans_fv. rewrite qand_qor_dist_l. erewrite qglb_disjoint_freshv; eauto. rewrite qor_empty_right. repeat erewrite q_trans_extend_tenv_closed_id'. eapply @Subq_trans with (d2:=(q_trans (Γ0 ++ [(bind_ty, bx, Tx, dx)]) Σ dx' ⊓ q_trans (Γ0 ++ [(bind_ty, bx, Tx, dx)]) Σ φ)); eauto. apply Subq_qand_split; auto.
    eapply closed_qenv_qn_shrink in Hqn; eauto.
    eapply closed_Nats_mono with (n:=0). Qcrush. lia.
    eapply closed_qenv_qn_shrink in Hqn; eauto.
    simpl. eapply closed_qenv_qn_monotone; eauto.
    rewrite app_length. simpl. lia.
    eapply closed_Nats_mono with (n:=0). Qcrush. lia.
    apply closed_Qual_q_trans''_monotone; eauto using wf_senv_closed_qenv.
    unfold q_trans_tenv. rewrite q_trans''_closed_id; auto. Qcrush.
    simpl; rewrite app_length; simpl; lia.
    1,2: simpl; rewrite app_length; simpl; rewrite Nat.add_1_r.
    eapply closed_qenv_qn_shrink in Hqn; eauto.
    Qcrush.
    replace (S (S (‖ Γ0 ‖))) with (‖ (bind_tm, true, TAll d1 d2 T1 T2, df) :: Γ0 ++ [(bind_ty, bx, Tx, dx)] ‖). rewrite q_trans_fv. rewrite qand_qor_dist_l.
    erewrite qglb_disjoint_freshv; eauto. rewrite qor_empty_right. rewrite q_trans_extend_tenv_closed_id'. rewrite q_trans_extend_tenv_closed_id'. rewrite q_trans_extend_tenv_closed_id'.
    eapply @Subq_trans with (d2:=(q_trans (Γ0 ++ [(bind_ty, bx, Tx, dx)]) Σ dx' ⊓ (q_trans (Γ0 ++ [(bind_ty, bx, Tx, dx)]) Σ (φ ⊔ {♦})))); eauto.
    apply Subq_qand_split; auto.
    apply q_trans_subq. eapply Subq_trans; eauto.
    rewrite <- q_trans_or_dist. rewrite q_trans_freshv_id. rewrite qand_qor_dist_l. rewrite qand_diamond_r_non_fresh. rewrite qor_empty_right; auto. unfold q_trans. apply q_trans_senv_wf_senv_non_fresh; auto. unfold q_trans_tenv. rewrite q_trans''_closed_id; eauto. Qcrush.
    eapply closed_qenv_qn_shrink in Hqn; eauto.
    rewrite app_length. simpl. rewrite Nat.add_1_r. Qcrush.
    eapply closed_qenv_qn_shrink in Hqn; eauto.
    eapply closed_Nats_mono with (n:=0). Qcrush. lia.
    eapply closed_qenv_qn_shrink in Hqn; eauto.
    eapply closed_qenv_qn_monotone; eauto. simpl. rewrite app_length. lia.
    eapply closed_Nats_mono with (n:=0). Qcrush. lia.
    unfold q_trans,q_trans_tenv. rewrite q_trans''_closed_id; auto.
    unfold q_trans_senv. apply closed_Qual_q_trans''_monotone; eauto. Qcrush.
    simpl. rewrite app_length. simpl. lia.
    inversion H0. subst. constructor. constructor; auto. eapply closed_Qual_monotone; eauto. eapply closed_ty_monotone; eauto. eapply closed_Qual_monotone; eauto.
    apply Substq_weaken. simpl; rewrite app_length; simpl. eapply closed_Qual_monotone; eauto. lia. eapply wf_tenv_closed_qenv_qn. econstructor; eauto.
    apply Substq_weaken; eauto. simpl; rewrite app_length; simpl. eapply closed_Qual_monotone; eauto. lia.
    subst DF. repeat rewrite subst1_qor_dist.
    erewrite <- @subst1_just_fv with (x:=(‖ Γ0 ‖)). erewrite <- @subst1_just_fv with (x:=(S (‖ Γ0 ‖))). auto. rewrite app_length. simpl. lia.
  - (* t_tapp *) intuition. rename H6 into IHHT. simpl.
    replace ({ 0 |-> dx' }ᵈ (openq df d1 d2)) with
               (openq ({ 0 |-> dx' }ᵈ df) ({ 0 |-> dx' }ᵈ d1) ({ 0 |-> dx' }ᵈ d2)).
    replace ({0 |-> Tx ~ dx' }ᵀ (T2 <~ᵀ TUnit ~ ∅; T1 ~ d1)) with
               (({0 |-> Tx ~ dx' }ᵀ T2) <~ᵀ TUnit ~ ∅; ({0 |-> Tx ~ dx' }ᵀ T1) ~ ({0 |-> dx' }ᵈ d1)).
    apply t_tapp with (T1:= { 0 |-> Tx ~ dx' }ᵀ T1) (df:=({0 |-> dx' }ᵈ df)).
    replace (TAll ({0 |-> dx' }ᵈ d1) ({0 |-> dx' }ᵈ d2) ({0 |-> Tx ~ dx' }ᵀ T1) ({0 |-> Tx ~ dx' }ᵀ T2))
            with ({ 0 |-> Tx ~ dx' }ᵀ (TAll d1 d2 T1 T2)); auto.
    * eapply closed_ty_subst1; eauto; eapply closed_ty_monotone; eauto. rewrite subst1_env_length,app_length. simpl. lia.
    * eapply closed_qual_subst1; eauto; eapply closed_Qual_monotone; eauto. rewrite subst1_env_length,app_length. simpl. lia.
    * replace (∅) with ({0 |-> dx' }ᵈ ∅) by auto; unfold openq. repeat erewrite <- subst1_open_qual_comm; eauto. erewrite <- subst1_fresh_id. subst φs. rewrite <- subst1_qor_dist. apply subst_qual_subqual_monotone; auto.
    * apply subst1_non_fresh; eauto.
    * apply subst_qual_subqual_monotone. auto.
    * replace (∅) with ({0 |-> dx' }ᵈ ∅) by auto; unfold openq. repeat erewrite <- subst1_open_qual_comm; eauto. apply subst1_senv_saturated; auto.
    * apply subst1_senv_saturated; auto.
    * erewrite <- not_free_subst1_ty_iff; eauto.
    * replace (∅) with ({0 |-> dx' }ᵈ ∅) at 1; auto. unfold open_ty. repeat erewrite subst1_open_ty_comm; eauto.
    * replace (∅) with ({0 |-> dx' }ᵈ ∅) by auto; unfold openq. repeat erewrite <- subst1_open_qual_comm; eauto.
  - (* t_tapp_fresh *) intuition. rename H9 into IHHT. simpl.
    replace ({ 0 |-> dx' }ᵈ (openq df d1 d2)) with
               (openq ({ 0 |-> dx' }ᵈ df) ({ 0 |-> dx' }ᵈ d1) ({ 0 |-> dx' }ᵈ d2)).
    replace ({0 |-> Tx ~ dx' }ᵀ (T2 <~ᵀ TUnit ~ ∅; T1 ~ d1)) with
               (({0 |-> Tx ~ dx' }ᵀ T2) <~ᵀ TUnit ~ ∅; ({0 |-> Tx ~ dx' }ᵀ T1) ~ ({0 |-> dx' }ᵈ d1)).
    (*separation/overap is preserved after substitution*)
    assert (Hoverlap: {0 |-> dx' }ᵈ (q_trans (Γ0 ++ [(bind_ty, bx, Tx, dx)]) Σ df ⊓ q_trans (Γ0 ++ [(bind_ty, bx, Tx, dx)]) Σ d1) = {0 |-> dx' }ᵈ (q_trans (Γ0 ++ [(bind_ty, bx, Tx, dx)]) Σ df) ⊓ {0 |-> dx' }ᵈ (q_trans (Γ0 ++ [(bind_ty, bx, Tx, dx)]) Σ d1)). {
      erewrite @subst1_qand_saturated' with (dx:=dx) (φ:=q_trans (Γ0 ++ [(bind_ty, bx, Tx, dx)]) Σ φ). auto. eapply @Subq_trans with (d2:=q_trans (Γ0 ++ [(bind_ty, bx, Tx, dx)]) Σ dx' ⊓ q_trans (Γ0 ++ [(bind_ty, bx, Tx, dx)]) Σ φ ); eauto.
apply Subq_qand_split; auto. 1,2: eauto. 1,2: eapply q_trans_subq_fresh; eauto. eapply has_type_filter; eauto. 1,2: unfold q_trans; eapply q_trans_qenv_saturated_q''_tenv; eauto; eapply wf_senv_closed_qenv; eauto.
    }
    eapply t_tapp_fresh with (T1:= { 0 |-> Tx ~ dx' }ᵀ T1) (df:=({0 |-> dx' }ᵈ df)) (d1:=({0 |-> dx' }ᵈ d1)); eauto.
    apply t_sub with (T1:=({0 |-> Tx ~ dx' }ᵀ (TAll (q_trans (Γ0 ++ [(bind_ty, bx, Tx, dx)]) Σ df
                  ⋒ q_trans (Γ0 ++ [(bind_ty, bx, Tx, dx)]) Σ d1) d2 T1 T2))) (d1:=({0 |-> dx' }ᵈ df)). auto.
    simpl. rewrite subst1_qor_dist. rewrite Hoverlap. rewrite subst1_fresh_id. auto. unfold q_trans, q_trans_senv, q_trans_tenv.
(* stp *)
    { inversion HSubst. subst.
      -- repeat erewrite q_trans''_subst1_senv_comm with (T:=Tx); eauto. repeat erewrite q_trans''_subst1_tenv_comm with (Tx:=Tx); eauto. repeat rewrite q_trans''_fuel_max with (fuel:=(‖ Γ0 ++ [(bind_ty, bx, Tx, dx')] ‖)). repeat rewrite subst1_env_length. repeat rewrite wf_senv_subst1_id; eauto. apply has_type_closed in HT. intuition. inversion H10. subst. apply stp_refl.
        + rewrite subst1_env_length,app_length in *. simpl in *. try rewrite Nat.add_1_r in *. constructor.
          apply closed_Qual_qor; auto. apply closed_Qual_qand.
          apply closed_Qual_q_trans''_monotone. apply closed_Qual_q_trans''_monotone. eapply closed_qual_subst1; eauto.

          apply wf_tenv_subst in HwfΓ. apply wf_tenv_closed_qenv in HwfΓ. rewrite subst1_env_length in HwfΓ. auto.
          apply wf_senv_closed_qenv in HwfΣ. eapply closed_qenv_monotone; eauto. lia.
          apply closed_Qual_q_trans''_monotone. apply closed_Qual_q_trans''_monotone. eapply closed_qual_subst1; eauto.
          apply wf_tenv_subst in HwfΓ. apply wf_tenv_closed_qenv in HwfΓ. rewrite subst1_env_length in HwfΓ. auto.
          apply wf_senv_closed_qenv in HwfΣ. eapply closed_qenv_monotone; eauto. lia.
          eapply closed_qual_subst1; eauto.
          1,2: eapply closed_ty_subst1; eauto; eapply closed_ty_monotone; eauto.
        + apply qstp_refl. rewrite app_length,subst1_env_length in *; simpl in *; try rewrite Nat.add_1_r in *. eapply closed_qual_subst1; eauto.
        + rewrite app_length,subst1_env_length in *; simpl in *; try rewrite Nat.add_1_r in *. lia.
        + rewrite app_length,subst1_env_length in *; simpl in *; try rewrite Nat.add_1_r in *. lia.
      -- rename H12 into Heq. repeat erewrite q_trans''_subst1_senv_comm with (T:=Tx); eauto.
         apply has_type_closed in HT as HTcl. intuition. inversion H14. subst. rewrite subst1_env_length,app_length in *. simpl in *. try rewrite Nat.add_1_r in *. constructor; repeat rewrite subst1_env_length.
          constructor. apply closed_Qual_qor; auto. apply closed_Qual_qand.
apply closed_Qual_q_trans''_monotone. eapply closed_qual_subst1; eauto. apply closed_Qual_q_trans''_monotone. eapply closed_Qual_monotone; eauto. rewrite Heq. apply wf_tenv_closed_qenv in HwfΓ. eapply closed_qenv_monotone; eauto. rewrite app_length. simpl. lia.
          apply wf_senv_closed_qenv in HwfΣ. eapply closed_qenv_subst1; eauto. eapply closed_qenv_monotone; eauto. lia. eapply closed_Qual_monotone; eauto. lia.
          apply closed_Qual_q_trans''_monotone. eapply closed_qual_subst1; eauto. apply closed_Qual_q_trans''_monotone. eapply closed_Qual_monotone; eauto. apply wf_tenv_closed_qenv in HwfΓ. eapply closed_qenv_monotone; eauto. rewrite Heq. eapply closed_qenv_monotone; eauto. rewrite app_length. simpl. lia.
          apply wf_senv_closed_qenv in HwfΣ. eapply closed_qenv_subst1; eauto. eapply closed_qenv_monotone; eauto. lia. eapply closed_Qual_monotone; eauto. lia.
          eapply closed_qual_subst1; eauto.
          eapply closed_ty_subst1; eauto.
          eapply closed_ty_subst1; eauto.
          constructor; auto. apply closed_Qual_qor; auto. apply closed_Qual_qand.
          apply closed_Qual_q_trans''_monotone. apply closed_Qual_q_trans''_monotone. eapply closed_qual_subst1; eauto.
rewrite <- Heq in HwfΓ. apply wf_tenv_subst' in HwfΓ; auto. apply wf_tenv_closed_qenv in HwfΓ. rewrite subst1_env_length in HwfΓ. eapply closed_qenv_subst1_monotone; eauto.
apply wf_senv_closed_qenv in HwfΣ. unfold q_trans,q_trans_tenv. rewrite q_trans''_closed_id. apply closed_Qual_q_trans''_monotone; eauto. Qcrush.
apply wf_senv_closed_qenv in HwfΣ. eapply closed_qenv_monotone; eauto. lia.
          apply closed_Qual_q_trans''_monotone. apply closed_Qual_q_trans''_monotone. eapply closed_qual_subst1; eauto.
rewrite <- Heq in HwfΓ. apply wf_tenv_subst' in HwfΓ; auto. apply wf_tenv_closed_qenv in HwfΓ. rewrite subst1_env_length in HwfΓ. auto.
          apply wf_senv_closed_qenv in HwfΣ. eapply closed_qenv_subst1_monotone; eauto.
apply wf_senv_closed_qenv in HwfΣ. unfold q_trans,q_trans_tenv. rewrite q_trans''_closed_id. apply closed_Qual_q_trans''_monotone; eauto. Qcrush.
          apply wf_senv_closed_qenv in HwfΣ. eapply closed_qenv_monotone; eauto. lia.
          eapply closed_qual_subst1; eauto.
          eapply closed_ty_subst1; eauto.
          eapply closed_ty_subst1; eauto.
        + constructor; auto. eapply closed_qual_subst1; eauto. eapply closed_Qual_monotone; eauto. rewrite subst1_env_length. lia.
        + eapply stp_refl'; eauto. eapply closed_ty_subst1; eauto. eapply closed_ty_monotone; eauto. rewrite subst1_env_length. lia. constructor. repeat rewrite wf_senv_subst1_id; eauto. apply Subq_qor. apply Subq_qand_split; eauto; apply q_trans''_subq. 1,2: rewrite Heq; eapply q_trans''_subst1_tenv_subq'; eauto.
          rewrite Heq. rewrite subst1_env_length. apply closed_Qual_qor; auto. apply closed_Qual_qand.
apply closed_Qual_q_trans''_monotone. eapply closed_qual_subst1; eauto. eapply closed_Qual_q_trans''_monotone; eauto. replace (S (‖ Γ0 ‖)) with (‖ Γ0 ++ [(bind_ty, bx, Tx, dx)] ‖). apply wf_tenv_closed_qenv; auto. rewrite app_length. simpl. lia. apply closed_qenv_subst1. eapply closed_qenv_monotone. apply wf_senv_closed_qenv; auto. 1-3: lia. eapply closed_Qual_monotone; eauto. lia.
apply closed_Qual_q_trans''_monotone. eapply closed_qual_subst1; eauto. eapply closed_Qual_q_trans''_monotone; eauto. replace (S (‖ Γ0 ‖)) with (‖ Γ0 ++ [(bind_ty, bx, Tx, dx)] ‖). apply wf_tenv_closed_qenv; auto. rewrite app_length. simpl. lia. apply closed_qenv_subst1. eapply closed_qenv_monotone. apply wf_senv_closed_qenv; auto. 1-3: lia. eapply closed_Qual_monotone; eauto. lia.
        + apply stp_refl. simpl. rewrite subst1_env_length. apply closed_ty_open2; try rewrite subst1_env_length; auto. eapply closed_ty_subst1; eauto. eapply closed_ty_monotone; eauto. 1,2: apply Q_lift_closed; Qcrush. apply qstp_refl. simpl. apply closed_Qual_open2; try rewrite subst1_env_length. eapply closed_qual_subst1; eauto. eapply closed_Qual_monotone; eauto. 1,2: Qcrush.
         }

    apply has_type_filter in HT. subst φs. erewrite <- subst1_fresh_id. rewrite <- subst1_qor_dist. apply subst_qual_subqual_monotone; auto.
    eapply subst1_senv_saturated; eauto. eapply has_type_senv_saturated; eauto.
    1,2 : rewrite subst1_env_length.
    eapply closed_ty_subst1; eauto. eapply closed_ty_monotone; eauto. rewrite app_length. simpl. lia.
    eapply closed_qual_subst1; eauto. eapply closed_Qual_monotone; eauto. rewrite app_length. simpl. lia.
    subst φs. erewrite <- subst1_fresh_id. rewrite <- subst1_qor_dist. apply subst_qual_subqual_monotone; auto.
    erewrite <- not_free_subst1_ty_iff; eauto; apply Substq_non_fresh in HSubst.
    apply subst1_senv_saturated; auto.
    erewrite <- not_free_subst1_ty_iff; eauto; apply Substq_non_fresh in HSubst.
    unfold openq; replace (∅) with ({0 |-> dx' }ᵈ ∅) by solve [apply subst1_qual_empty]; repeat erewrite <- subst1_open_qual_comm; eauto. subst φs. erewrite <- subst1_fresh_id. rewrite <- subst1_qor_dist. apply subst_qual_subqual_monotone; auto.
    apply Subq_qor_l; eauto.
    eapply @Subq_trans with (d2:={0 |-> dx'}ᵈ (q_trans (Γ0 ++ [(bind_ty, bx, Tx, dx)]) Σ d1 ⊓ q_trans (Γ0 ++ [(bind_ty, bx, Tx, dx)]) Σ df)); eauto.
    assert (dx' ⊓ q_trans (Γ0 ++ [(bind_ty, bx, Tx, dx)]) Σ φ ⊑↑ dx). eapply @Subq_trans with (d2:=q_trans (Γ0 ++ [(bind_ty, bx, Tx, dx)]) Σ dx' ⊓ q_trans (Γ0 ++ [(bind_ty, bx, Tx, dx)]) Σ φ); eauto. apply Subq_qand_split; auto.
    erewrite <- @subst1_qand_saturated' with (dx':=dx'); eauto. apply Subq_qand_split; unfold q_trans,q_trans_tenv,q_trans_senv; erewrite q_trans''_subst1_senv_comm'; eauto.
    apply q_trans''_subq. rewrite subst1_env_length,app_length. simpl. rewrite Nat.add_1_r. eapply q_trans''_subst1_tenv_subq'; eauto.
    apply q_trans''_subq. rewrite subst1_env_length,app_length. simpl. rewrite Nat.add_1_r. eapply q_trans''_subst1_tenv_subq'; eauto.
    1,2: apply q_trans_subq_fresh; eauto. eapply has_type_filter; eauto.
    unfold qenv_saturated_q''.  unfold q_trans, q_trans_senv, q_trans_tenv.
    1,2: unfold q_trans; eapply q_trans_qenv_saturated_q''_tenv; eauto; eapply wf_senv_closed_qenv; eauto.
    subst φs. erewrite <- subst1_fresh_id. rewrite <- subst1_qor_dist. apply subst_qual_subqual_monotone. Qcrush.
    unfold openq; rewrite <- @subst1_qual_empty with (dx:=dx');
    erewrite <- subst1_open_qual_comm; eauto; erewrite <- subst1_open_qual_comm; eauto. apply subst1_senv_saturated; auto.
    replace (∅) with ({0 |-> dx' }ᵈ ∅) at 1; auto. unfold open_ty. repeat erewrite subst1_open_ty_comm; eauto.
    unfold openq. repeat erewrite <- subst1_open_qual_comm; eauto.
  - (* t_base *) simpl. replace ({0 |-> dx' }ᵈ ∅) with (∅) by solve [symmetry; apply subst1_qual_empty].
    apply t_base; auto. eapply closed_qual_subst1'; eauto.
  - (* t_var *) simpl. (bdestruct (x =? 0)).
    + (*  x is 0 *)
      rewrite indexr_skips in H; simpl; auto; try lia. simpl in H. subst. simpl in H. inversion H.
    + (* x is in Γ0 *)
    assert (Hx: 1 <= x); try lia. destruct x; try lia.
    apply @indexr_subst1 with (Tx := Tx)(dx := dx') in H; auto.
    apply t_var with (b:=b) (d:={0 |-> dx' }ᵈ d)(φ  := ({0 |-> dx' }ᵈ φ)). change x with (pred (S x)). auto.
    erewrite subst1_just_fv.
    repeat eapply subst_qual_subqual_monotone. auto.
    eapply closed_qual_subst1'; eauto. simpl. eapply closed_ty_subst1; eauto.
    simpl. eapply closed_qual_subst1; eauto.
  - (* t_abs *) simpl. apply t_abs; auto. eapply closed_tm_subst1'; eauto.
    inversion H0. subst. constructor; try eapply closed_ty_subst1'; eauto; eapply closed_qual_subst1'; eauto.
    eapply closed_qual_subst1'; eauto. apply subst_qual_subqual_monotone_fresh; auto. apply subst_qual_subqual_monotone; auto. eauto.
    apply subst1_senv_saturated; auto.
    (* 1. instantiate the IH *)
    replace (length (Γ0 ++ [(bind_ty, bx, Tx, dx)])) with (S (‖Γ0‖)) in IHHT.
    rewrite subst1_env_length. rewrite app_comm_cons in IHHT. rewrite app_comm_cons in IHHT.
    remember (df ⊔ $!(S (‖Γ0‖)) ⊔ $!(S (S (‖Γ0‖))) ⊔ {♦}) as DF.
    replace ({0 |-> dx' }ᵈ df ⊔ $!(‖Γ0‖) ⊔ $!(S (‖Γ0‖)) ⊔ {♦}) with ({0 |-> dx' }ᵈ DF).
    intuition. specialize IHHT with (Γ := (((bind_tm, false,T1, d1) :: (bind_tm, true, (TFun d1 d2 T1 T2), df) :: Γ0))).
    (* 2. reason about opening and subst, apply IH *)
    unfold open_tm' in *. unfold open_ty' in *. unfold open_ty in *.
    unfold openq' in *. unfold openq in *.
    rewrite app_length in IHHT. rewrite subst1_env_length. simpl in *.
    replace (‖Γ0‖ + 1) with (S (‖Γ0‖)) in IHHT; try lia.
    erewrite <- open_subst1_tm_comm in IHHT; eauto. erewrite <- open_subst1_tm_comm in IHHT; eauto.
    erewrite <- open_subst1_ty_comm in IHHT; eauto. erewrite <- open_subst1_ty_comm in IHHT; eauto.
    erewrite <- open_subst1_qual_comm in IHHT; eauto. erewrite <- open_subst1_qual_comm in IHHT; eauto. repeat erewrite subst1_qor_dist in IHHT. apply IHHT; auto.
    apply has_type_filter in HT as Hft.
    subst.
    inversion H0. subst. rewrite app_length in *. simpl in *. rewrite Nat.add_1_r in *.
    repeat rewrite <- q_trans_or_dist. repeat rewrite qand_qor_dist_l. assert (Hqn: closed_qenv_qn (S (‖ Γ0 ‖)) ((bind_ty, false, T1, d1) :: (bind_tm, true, TFun d1 d2 T1 T2, df) :: Γ0 ++ [(bind_ty, bx, Tx, dx)])). {
      unfold closed_qenv_qn. intros.
      bdestruct (x =? (S (S (‖ Γ0 ‖)))). replace x with (‖ (bind_tm, true, TFun d1 d2 T1 T2, df) :: Γ0 ++ [(bind_ty, bx, Tx, dx)] ‖) in *. rewrite indexr_head in H6. inversion H6. subst. simpl. Qcrush. subst. simpl. rewrite app_length. simpl. lia.
      bdestruct (x =? (S (‖ Γ0 ‖))). replace x with (‖ Γ0 ++ [(bind_ty, bx, Tx, dx)] ‖) in *. rewrite indexr_skip in H6; auto. rewrite indexr_head in H6. inversion H6. subst. simpl. Qcrush. subst. simpl. rewrite app_length. simpl. lia.
      rewrite indexr_skip in H6; auto. rewrite indexr_skip in H6; auto. destruct a as [ [ [ b fr ] T' ] q']. eapply wf_tenv_prop in HwfΓ; eauto. simpl. apply indexr_var_some' in H6. rewrite app_length in *. simpl in *. rewrite Nat.add_1_r in *. eapply closed_Nats_mono; eauto. Qcrush. 1,2: subst; simpl; rewrite app_length; simpl; lia.
    }
    repeat apply Subq_qor_l. unfold q_trans,q_trans_tenv. repeat erewrite q_trans''_extend_closed_id'. rewrite q_trans''_fuel_max. eapply @Subq_trans with (d2:=(q_trans (Γ0 ++ [(bind_ty, bx, Tx, dx)]) Σ dx' ⊓ q_trans (Γ0 ++ [(bind_ty, bx, Tx, dx)]) Σ φ)); eauto. unfold q_trans,q_trans_tenv. eapply Subq_qand_split; eauto.
    repeat eapply q_trans''_subq; eauto. rewrite q_trans''_fuel_max. apply q_trans''_subq; auto. 1,2: simpl; lia.
    eapply closed_qenv_qn_monotone; eauto.
    1-3: simpl; rewrite app_length; simpl; rewrite Nat.add_1_r.
    Qcrush.
    eapply closed_qenv_qn_shrink in Hqn; eauto.
    Qcrush.
    eapply closed_qenv_qn_shrink in Hqn; eauto.
    eapply closed_Nats_mono with (n:=0). Qcrush. lia.
    eapply closed_qenv_qn_shrink in Hqn; eauto. simpl. eapply closed_qenv_qn_monotone; eauto. rewrite app_length. lia.
    eapply closed_Nats_mono with (n:=0). Qcrush. lia.
    erewrite q_trans_extend_tenv_closed_id' with (q':=$! (S (‖ Γ0 ‖))). replace (S (‖ Γ0 ‖)) with (‖ Γ0 ++ [(bind_ty, bx, Tx, dx)] ‖). rewrite q_trans_fv. rewrite qand_qor_dist_l. erewrite qglb_disjoint_freshv; eauto. rewrite qor_empty_right. repeat erewrite q_trans_extend_tenv_closed_id'. eapply @Subq_trans with (d2:=(q_trans (Γ0 ++ [(bind_ty, bx, Tx, dx)]) Σ dx' ⊓ q_trans (Γ0 ++ [(bind_ty, bx, Tx, dx)]) Σ φ)); eauto. apply Subq_qand_split; auto.
    eapply closed_qenv_qn_shrink in Hqn; eauto.
    eapply closed_Nats_mono with (n:=0). Qcrush. lia.
    eapply closed_qenv_qn_shrink in Hqn; eauto.
    simpl. eapply closed_qenv_qn_monotone; eauto.
    rewrite app_length. simpl. lia.
    eapply closed_Nats_mono with (n:=0). Qcrush. lia.
    apply closed_Qual_q_trans''_monotone; eauto using wf_senv_closed_qenv.
    unfold q_trans_tenv. rewrite q_trans''_closed_id; auto. Qcrush.
    simpl; rewrite app_length; simpl; lia.
    1,2: simpl; rewrite app_length; simpl; rewrite Nat.add_1_r.
    eapply closed_qenv_qn_shrink in Hqn; eauto.
    Qcrush.
    replace (S (S (‖ Γ0 ‖))) with (‖ (bind_tm, true, TFun d1 d2 T1 T2, df) :: Γ0 ++ [(bind_ty, bx, Tx, dx)] ‖). rewrite q_trans_fv. rewrite qand_qor_dist_l. erewrite qglb_disjoint_freshv; eauto. rewrite qor_empty_right. rewrite q_trans_extend_tenv_closed_id'.
    eapply @Subq_trans with (d2:=(q_trans ((bind_tm, true, TFun d1 d2 T1 T2, df) :: Γ0 ++ [(bind_ty, bx, Tx, dx)]) Σ dx' ⊓ (q_trans ((bind_tm, true, TFun d1 d2 T1 T2, df) :: Γ0 ++ [(bind_ty, bx, Tx, dx)]) Σ (φ ⊔ {♦})))); eauto.
    apply Subq_qand_split; auto.
    apply q_trans_subq. eapply Subq_trans; eauto.
    rewrite <- q_trans_or_dist. rewrite q_trans_freshv_id. rewrite qand_qor_dist_l. rewrite qand_diamond_r_non_fresh. rewrite qor_empty_right; auto.
    repeat rewrite q_trans_extend_tenv_closed_id'; auto.
    eapply closed_qenv_qn_shrink in Hqn; eauto.
    simpl; rewrite app_length; simpl; rewrite Nat.add_1_r. Qcrush.
    eapply closed_qenv_qn_shrink in Hqn; eauto.
    eapply closed_Nats_mono with (n:=0). Qcrush. lia.
    unfold q_trans. apply q_trans_senv_wf_senv_non_fresh; auto. unfold q_trans_tenv. rewrite q_trans''_closed_id; eauto. Qcrush.
    eapply closed_qenv_qn_shrink in Hqn; eauto.
    simpl. eapply closed_qenv_qn_monotone; eauto.
    rewrite app_length. simpl. lia.
    eapply closed_Nats_mono with (n:=0). Qcrush. lia.
    apply closed_Qual_q_trans''_monotone; eauto using wf_senv_closed_qenv.
    unfold q_trans_tenv. rewrite q_trans''_closed_id; auto. Qcrush.
    simpl. rewrite app_length. simpl. lia.
    inversion H0. subst. constructor. constructor; auto. eapply closed_Qual_monotone; eauto. eapply closed_ty_monotone; eauto. eapply closed_Qual_monotone; eauto.
    apply Substq_weaken. simpl; rewrite app_length; simpl. eapply closed_Qual_monotone; eauto. lia. eapply wf_tenv_closed_qenv_qn. econstructor; eauto.
    apply Substq_weaken; eauto. simpl; rewrite app_length; simpl. eapply closed_Qual_monotone; eauto. lia.
    subst DF. repeat rewrite subst1_qor_dist.
    erewrite <- @subst1_just_fv with (x:=(‖ Γ0 ‖)). erewrite <- @subst1_just_fv with (x:=(S (‖ Γ0 ‖))). rewrite subst1_fresh_id. auto. rewrite app_length. simpl. lia.
  - (* t_app *) intuition. rename H3 into IHHT1. rename H5 into IHHT2. simpl.
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
    * replace (∅) with ({0 |-> dx' }ᵈ ∅) by auto; unfold openq. repeat erewrite <- subst1_open_qual_comm; eauto. erewrite <- subst1_fresh_id. subst φs. rewrite <- subst1_qor_dist. apply subst_qual_subqual_monotone; auto.
    * replace (∅) with ({0 |-> dx' }ᵈ ∅) by auto; unfold openq. repeat erewrite <- subst1_open_qual_comm; eauto. apply subst1_senv_saturated; auto.
    * apply subst1_non_fresh; eauto.
    * erewrite <- not_free_subst1_ty_iff; eauto.
    * replace (∅) with ({0 |-> dx' }ᵈ ∅) at 1; auto. unfold open_ty. repeat erewrite subst1_open_ty_comm; eauto.
    * unfold openq. repeat erewrite <- subst1_open_qual_comm; eauto.

  - (* t_app_fresh *) intuition. rename H4 into IHHT1. rename H6 into IHHT2. simpl.
    replace ({ 0 |-> dx' }ᵈ (openq df d1 d2)) with
               (openq ({ 0 |-> dx' }ᵈ df) ({ 0 |-> dx' }ᵈ d1) ({ 0 |-> dx' }ᵈ d2)).
    replace ({0 |-> Tx ~ dx' }ᵀ (T2 <~ᵀ TUnit ~ ∅; T1 ~ d1)) with
               (({0 |-> Tx ~ dx' }ᵀ T2) <~ᵀ TUnit ~ ∅; ({0 |-> Tx ~ dx' }ᵀ T1) ~ ({0 |-> dx' }ᵈ d1)).
    (*separation/overap is preserved after substitution*)
    assert (Hoverlap: {0 |-> dx' }ᵈ (q_trans (Γ0 ++ [(bind_ty, bx, Tx, dx)]) Σ df ⊓ q_trans (Γ0 ++ [(bind_ty, bx, Tx, dx)]) Σ d1) = {0 |-> dx' }ᵈ (q_trans (Γ0 ++ [(bind_ty, bx, Tx, dx)]) Σ df) ⊓ {0 |-> dx' }ᵈ (q_trans (Γ0 ++ [(bind_ty, bx, Tx, dx)]) Σ d1)). {
      erewrite @subst1_qand_saturated' with (dx:=dx) (φ:=q_trans (Γ0 ++ [(bind_ty, bx, Tx, dx)]) Σ φ). auto.
      eapply @Subq_trans with (d2:=q_trans (Γ0 ++ [(bind_ty, bx, Tx, dx)]) Σ dx' ⊓ q_trans (Γ0 ++ [(bind_ty, bx, Tx, dx)]) Σ φ ); eauto.
      apply Subq_qand_split; auto.
      1,2: eauto. 1,2: eapply q_trans_subq_fresh; eapply has_type_filter; eauto.
      1,2: unfold q_trans; eapply q_trans_qenv_saturated_q''_tenv; eauto; eapply wf_senv_closed_qenv; eauto.
    }
    eapply t_app_fresh with (T1:= { 0 |-> Tx ~ dx' }ᵀ T1) (df:=({0 |-> dx' }ᵈ df)) (d1:=({0 |-> dx' }ᵈ d1)); eauto.
    apply t_sub with (T1:=({0 |-> Tx ~ dx' }ᵀ (TFun (q_trans (Γ0 ++ [(bind_ty, bx, Tx, dx)]) Σ df
                  ⋒ q_trans (Γ0 ++ [(bind_ty, bx, Tx, dx)]) Σ d1) d2 T1 T2))) (d1:=({0 |-> dx' }ᵈ df)). auto.
    simpl. rewrite subst1_qor_dist. rewrite Hoverlap. rewrite subst1_fresh_id. auto. unfold q_trans, q_trans_senv, q_trans_tenv.
(* stp *)
    { inversion HSubst. subst.
      -- repeat erewrite q_trans''_subst1_senv_comm with (T:=Tx); eauto. repeat erewrite q_trans''_subst1_tenv_comm with (Tx:=Tx); eauto. repeat rewrite q_trans''_fuel_max with (fuel:=(‖ Γ0 ++ [(bind_ty, bx, Tx, dx')] ‖)). repeat rewrite subst1_env_length. repeat rewrite wf_senv_subst1_id; eauto. apply has_type_closed in HT1, HT2. intuition. inversion H8. subst. apply stp_refl.
        + rewrite subst1_env_length,app_length in *. simpl in *. try rewrite Nat.add_1_r in *. constructor.
          apply closed_Qual_qor; auto. apply closed_Qual_qand.
          apply closed_Qual_q_trans''_monotone. apply closed_Qual_q_trans''_monotone. eapply closed_qual_subst1; eauto.

          apply wf_tenv_subst in HwfΓ. apply wf_tenv_closed_qenv in HwfΓ. rewrite subst1_env_length in HwfΓ. auto.
          apply wf_senv_closed_qenv in HwfΣ. eapply closed_qenv_monotone; eauto. lia.
          apply closed_Qual_q_trans''_monotone. apply closed_Qual_q_trans''_monotone. eapply closed_qual_subst1; eauto.
          apply wf_tenv_subst in HwfΓ. apply wf_tenv_closed_qenv in HwfΓ. rewrite subst1_env_length in HwfΓ. auto.
          apply wf_senv_closed_qenv in HwfΣ. eapply closed_qenv_monotone; eauto. lia.
          eapply closed_qual_subst1; eauto.
          1,2: eapply closed_ty_subst1; eauto; eapply closed_ty_monotone; eauto.
        + apply qstp_refl. rewrite app_length,subst1_env_length in *; simpl in *; try rewrite Nat.add_1_r in *. eapply closed_qual_subst1; eauto.
        + rewrite app_length,subst1_env_length in *; simpl in *; try rewrite Nat.add_1_r in *. lia.
        + rewrite app_length,subst1_env_length in *; simpl in *; try rewrite Nat.add_1_r in *. lia.
      -- rename H8 into Heq. repeat erewrite q_trans''_subst1_senv_comm with (T:=Tx); eauto.
         apply has_type_closed in HT1 as Hcl1,HT2 as Hcl2. intuition. inversion H12. subst. rewrite subst1_env_length,app_length in *. simpl in *. try rewrite Nat.add_1_r in *. constructor; repeat rewrite subst1_env_length.
          constructor. apply closed_Qual_qor; auto. apply closed_Qual_qand.
apply closed_Qual_q_trans''_monotone. eapply closed_qual_subst1; eauto. apply closed_Qual_q_trans''_monotone. eapply closed_Qual_monotone; eauto. rewrite Heq. apply wf_tenv_closed_qenv in HwfΓ. eapply closed_qenv_monotone; eauto. rewrite app_length. simpl. lia.
          apply wf_senv_closed_qenv in HwfΣ. eapply closed_qenv_subst1; eauto. eapply closed_qenv_monotone; eauto. lia. eapply closed_Qual_monotone; eauto. lia.
          apply closed_Qual_q_trans''_monotone. eapply closed_qual_subst1; eauto. apply closed_Qual_q_trans''_monotone. eapply closed_Qual_monotone; eauto. apply wf_tenv_closed_qenv in HwfΓ. eapply closed_qenv_monotone; eauto. rewrite Heq. eapply closed_qenv_monotone; eauto. rewrite app_length. simpl. lia.
          apply wf_senv_closed_qenv in HwfΣ. eapply closed_qenv_subst1; eauto. eapply closed_qenv_monotone; eauto. lia. eapply closed_Qual_monotone; eauto. lia.
          eapply closed_qual_subst1; eauto.
          eapply closed_ty_subst1; eauto.
          eapply closed_ty_subst1; eauto.
          constructor; auto. apply closed_Qual_qor; auto. apply closed_Qual_qand.
          apply closed_Qual_q_trans''_monotone. apply closed_Qual_q_trans''_monotone. eapply closed_qual_subst1; eauto.
rewrite <- Heq in HwfΓ. apply wf_tenv_subst' in HwfΓ; auto. apply wf_tenv_closed_qenv in HwfΓ. rewrite subst1_env_length in HwfΓ. eapply closed_qenv_subst1_monotone; eauto.
apply wf_senv_closed_qenv in HwfΣ. unfold q_trans,q_trans_tenv. rewrite q_trans''_closed_id. apply closed_Qual_q_trans''_monotone; eauto. Qcrush.
apply wf_senv_closed_qenv in HwfΣ. eapply closed_qenv_monotone; eauto. lia.
          apply closed_Qual_q_trans''_monotone. apply closed_Qual_q_trans''_monotone. eapply closed_qual_subst1; eauto.
rewrite <- Heq in HwfΓ. apply wf_tenv_subst' in HwfΓ; auto. apply wf_tenv_closed_qenv in HwfΓ. rewrite subst1_env_length in HwfΓ. auto.
          apply wf_senv_closed_qenv in HwfΣ. eapply closed_qenv_subst1_monotone; eauto.
apply wf_senv_closed_qenv in HwfΣ. unfold q_trans,q_trans_tenv. rewrite q_trans''_closed_id. apply closed_Qual_q_trans''_monotone; eauto. Qcrush.
          apply wf_senv_closed_qenv in HwfΣ. eapply closed_qenv_monotone; eauto. lia.
          eapply closed_qual_subst1; eauto.
          eapply closed_ty_subst1; eauto.
          eapply closed_ty_subst1; eauto.
        + constructor; auto. eapply closed_qual_subst1; eauto. eapply closed_Qual_monotone; eauto. rewrite subst1_env_length. lia.
        + eapply stp_refl'; eauto. eapply closed_ty_subst1; eauto. eapply closed_ty_monotone; eauto. rewrite subst1_env_length. lia. constructor. repeat rewrite wf_senv_subst1_id; eauto. apply Subq_qor. apply Subq_qand_split; eauto; apply q_trans''_subq. 1,2: rewrite Heq; eapply q_trans''_subst1_tenv_subq'; eauto.
          rewrite Heq. rewrite subst1_env_length. apply closed_Qual_qor; auto. apply closed_Qual_qand.
apply closed_Qual_q_trans''_monotone. eapply closed_qual_subst1; eauto. eapply closed_Qual_q_trans''_monotone; eauto. replace (S (‖ Γ0 ‖)) with (‖ Γ0 ++ [(bind_ty, bx, Tx, dx)] ‖). apply wf_tenv_closed_qenv; auto. rewrite app_length. simpl. lia. apply closed_qenv_subst1. eapply closed_qenv_monotone. apply wf_senv_closed_qenv; auto. 1-3: lia. eapply closed_Qual_monotone; eauto. lia.
apply closed_Qual_q_trans''_monotone. eapply closed_qual_subst1; eauto. eapply closed_Qual_q_trans''_monotone; eauto. replace (S (‖ Γ0 ‖)) with (‖ Γ0 ++ [(bind_ty, bx, Tx, dx)] ‖). apply wf_tenv_closed_qenv; auto. rewrite app_length. simpl. lia. apply closed_qenv_subst1. eapply closed_qenv_monotone. apply wf_senv_closed_qenv; auto. 1-3: lia. eapply closed_Qual_monotone; eauto. lia.
        + apply stp_refl. simpl. rewrite subst1_env_length. apply closed_ty_open2; try rewrite subst1_env_length; auto. eapply closed_ty_subst1; eauto. eapply closed_ty_monotone; eauto. 1,2: apply Q_lift_closed; Qcrush. apply qstp_refl. simpl. apply closed_Qual_open2; try rewrite subst1_env_length. eapply closed_qual_subst1; eauto. eapply closed_Qual_monotone; eauto. 1,2: Qcrush.
         }
    apply has_type_filter in HT1. subst φs. erewrite <- subst1_fresh_id. rewrite <- subst1_qor_dist. apply subst_qual_subqual_monotone; auto.
eapply subst1_senv_saturated; eauto. eapply has_type_senv_saturated; eauto.
1,2 : erewrite <- not_free_subst1_ty_iff; eauto; apply Substq_non_fresh in HSubst.
    unfold openq; replace (∅) with ({0 |-> dx' }ᵈ ∅) by solve [apply subst1_qual_empty];
    erewrite <- subst1_open_qual_comm; eauto; erewrite <- subst1_open_qual_comm; eauto.
    subst φs. erewrite <- subst1_fresh_id. rewrite <- subst1_qor_dist. apply subst_qual_subqual_monotone; auto.
    apply Subq_qor_l; auto.
    eapply @Subq_trans with (d2:={0 |-> dx'}ᵈ (q_trans (Γ0 ++ [(bind_ty, bx, Tx, dx)]) Σ d1 ⊓ q_trans (Γ0 ++ [(bind_ty, bx, Tx, dx)]) Σ df)); eauto.
    assert (dx' ⊓ q_trans (Γ0 ++ [(bind_ty, bx, Tx, dx)]) Σ φ ⊑↑ dx). eapply @Subq_trans with (d2:=q_trans (Γ0 ++ [(bind_ty, bx, Tx, dx)]) Σ dx' ⊓ q_trans (Γ0 ++ [(bind_ty, bx, Tx, dx)]) Σ φ); eauto. apply Subq_qand_split; auto.
    erewrite <- @subst1_qand_saturated' with (dx':=dx'); eauto. apply Subq_qand_split; unfold q_trans,q_trans_tenv,q_trans_senv; erewrite q_trans''_subst1_senv_comm'; eauto.
    apply q_trans''_subq. rewrite subst1_env_length,app_length. simpl. rewrite Nat.add_1_r. eapply q_trans''_subst1_tenv_subq'; eauto.
    apply q_trans''_subq. rewrite subst1_env_length,app_length. simpl. rewrite Nat.add_1_r. eapply q_trans''_subst1_tenv_subq'; eauto.
    1,2: apply q_trans_subq_fresh; eapply has_type_filter; eauto.
    unfold qenv_saturated_q''.  unfold q_trans, q_trans_senv, q_trans_tenv.
    1,2: unfold q_trans; eapply q_trans_qenv_saturated_q''_tenv; eauto; eapply wf_senv_closed_qenv; eauto.
    subst φs. erewrite <- subst1_fresh_id. rewrite <- subst1_qor_dist. apply subst_qual_subqual_monotone; auto. Qcrush.
    unfold openq; rewrite <- @subst1_qual_empty with (dx:=dx');
    erewrite <- subst1_open_qual_comm; eauto; erewrite <- subst1_open_qual_comm; eauto. apply subst1_senv_saturated; auto.
    replace (∅) with ({0 |-> dx' }ᵈ ∅) at 1; auto. unfold open_ty. repeat erewrite subst1_open_ty_comm; eauto.
    unfold openq. repeat erewrite <- subst1_open_qual_comm; eauto.
  - (* t_loc *) rewrite subst1_qor_dist. erewrite @subst1_qual_id with (q:=(&!l)); eauto. simpl. erewrite subst1_ty_id; eauto.
    erewrite subst1_qual_id; eauto. apply t_loc; auto. eapply closed_qual_subst1'; eauto.
    erewrite <- @subst1_qual_id with (q:=(&!l)); eauto. eapply subst_qual_subqual_monotone; eauto.
    2 : erewrite <- @subst1_qual_id with (q:=q); eauto; eapply subst_qual_subqual_monotone; eauto.
    all : apply indexr_var_some' in H0; eapply just_loc_closed; eauto.
  - (* t_ref *) rewrite subst1_qor_dist. rewrite subst1_fresh_id. simpl. apply t_ref; auto.
    eapply closed_ty_subst1'; eauto. apply subst1_non_fresh; eauto.
  - (* t_deref *) simpl. apply t_deref with (d := { 0 |-> dx' }ᵈ d); auto.
    apply subst1_non_fresh; eauto. apply subst_qual_subqual_monotone. auto.
    apply subst1_senv_saturated; auto.
  - (* t_assign *) rewrite subst1_qual_empty in *. simpl. simpl in IHHT1.
    apply t_assign with (T:={0 |-> Tx ~ dx' }ᵀ T) (d:=({0 |-> dx' }ᵈ d)) (d1:=({0 |-> dx' }ᵈ d1)); auto.
    apply subst1_non_fresh; eauto.
  - (* t_sub *) apply t_sub with (T1:={ 0 |-> Tx ~ dx' }ᵀ T1) (d1:={ 0 |-> dx' }ᵈ d1).
    eapply IHHT; eauto. eapply subst_stp; eauto. erewrite <- subst1_fresh_id. subst φs. rewrite <- subst1_qor_dist. apply subst_qual_subqual_monotone; auto. apply subst1_senv_saturated; auto.
  Unshelve. all : apply 0.
Qed.

(* case for t_tapp *)
Lemma substitution1_ty : forall {t bx bf Tx Tf dx df Σ T d},
     has_type [(bind_ty, bx, Tx, dx) ; (bind_tm, bf,Tf,df)] (df ⊔ $!0 ⊔ $!1) Σ t T d ->
     closed_ty 0 0 (length Σ) Tx ->
     closed_Qual 0 0 (length Σ) dx↑ -> ♦∉ dx ->  senv_saturated Σ dx ->
     wf_senv Σ ->
     forall {vt φ}, vtp Σ φ vt Tf df -> ♦∉ df ->
     has_type [] (df ⊔ dx) Σ  ( { 0 |-> vt; tunit  }ᵗ t)  ( { 0 |-> Tf ~ df; Tx ~ dx }ᵀ T) ({ 0 |-> df; dx }ᵈ d).
Proof.
  intros. subst. specialize (vtp_closed  H5) as HV_cl. specialize (has_type_closed H) as Hcl. intuition.
       intuition. replace ([(bind_ty, bx,Tx, dx); (bind_tm, bf,Tf, df)]) with ([(bind_ty, bx,Tx,dx)] ++ [(bind_tm, bf,Tf, df)]) in H; auto.
  assert (Hsepf : (q_trans ([(bind_ty, bx, Tx, dx)] ++ [(bind_tm, bf, Tf, df)]) Σ df) ⊓ (q_trans ([(bind_ty, bx, Tx, dx)] ++ [(bind_tm, bf, Tf, df)]) Σ (df ⊔ $!0 ⊔ $!1)) ⊑↑ df). { unfold q_trans,q_trans_tenv,q_trans_senv. rewrite qenv_saturated_trans''_id; auto. rewrite q_trans''_closed_id. apply qand_Sub_l. Qcrush. pose proof (vtp_saturated H5). inversion H13. apply qenv_saturated_iff in H16. rewrite q_trans''_closed_id; auto. Qcrush. }
  eapply (substitution_gen Hsepf) in H; eauto.
  (* substitute the second free variable dx *)
  replace ({0 |-> Tf ~ df }ᴳ [(bind_ty, bx, Tx, dx)]) with ([] ++ [(bind_ty, bx, Tx, dx)]) in H.
  replace ({0 |-> df }ᵈ (df ⊔ $! 0 ⊔ $! 1)) with (df ⊔ $!0) in H.
  assert (Hsepf' : (q_trans ([] ++ [(bind_ty, bx, Tx, dx)]) Σ dx) ⊓ (q_trans ([] ++ [(bind_ty, bx, Tx, dx)]) Σ (df ⊔ $!0)) ⊑↑ dx). { unfold q_trans,q_trans_tenv,q_trans_senv. rewrite qenv_saturated_trans''_id; auto. rewrite q_trans''_closed_id. apply qand_Sub_l. Qcrush. apply qenv_saturated_iff in H3. rewrite q_trans''_closed_id; auto. Qcrush. }
  eapply (substitution_ty_gen Hsepf') in H; eauto.
  replace ({0 |-> dx }ᵈ (df ⊔ $!0)) with (df ⊔ dx) in H. simpl in H. apply H.
  repeat rewrite subst1_qor_dist. rewrite subst1_just_fv0. erewrite subst1_qual_id; eauto.
  constructor; auto.
  subst. repeat rewrite subst1_qor_dist. rewrite subst1_just_fv0. rewrite <- subst1_just_fv.
  erewrite subst1_qual_id; eauto.
  rewrite (@qor_assoc df df).
  rewrite qor_idem. auto.
  simpl. erewrite subst1_qual_id; eauto. erewrite subst1_ty_id; eauto.
  constructor; auto; simpl. eapply closed_ty_monotone; eauto. eapply closed_Qual_monotone; eauto.
Qed.

(* t_app case *)
Lemma substitution_stp1 : forall{T1 T2},
    forall {bdx bdf bx Tx bf Tf df dx Σ d1 d2},
      stp ([(bdx, bx,Tx,dx); (bdf, bf,Tf,{♦})]) Σ T1 d1 T2 d2 ->
      wf_senv Σ ->
      closed_ty 0 0 (‖Σ‖) Tx ->
      closed_ty 0 0 (‖Σ‖) Tf ->
      closed_Qual 0 0 (‖Σ‖) df↑ -> closed_Qual 0 0 (‖Σ‖) dx↑ -> ♦∉ df -> ♦∉ dx ->
      stp [] Σ ({ 0 |-> Tf ~ df; Tx ~ dx }ᵀ T1) ({ 0 |-> df ; dx }ᵈ d1) ({ 0 |-> Tf ~ df ; Tx ~ dx }ᵀ T2) ({ 0 |-> df ; dx }ᵈ d2).
  intros. replace [(bdx, bx, Tx, dx); (bdf, bf, Tf,{♦})] with ([(bdx, bx, Tx, dx)] ++ [(bdf, bf, Tf,{♦})]) in H; auto.
  eapply @subst_stp with (df':=df) in H; auto.
  replace ({0 |-> Tf ~ df }ᴳ [(bdx, bx, Tx, dx)]) with ([(bdx, bx, Tx, dx)]) in H.
  replace ([(bdx, bx, Tx, dx)]) with ([] ++ [(bdx, bx, Tx, dx)]) in H; auto.
  eapply @subst_stp with (df':=dx) in H; auto.
  constructor; auto.
  simpl. erewrite subst1_ty_id; eauto. erewrite subst1_qual_id; eauto.
simpl. constructor; auto; simpl; auto. eapply closed_ty_monotone; eauto. eapply closed_Qual_monotone; eauto.
apply Substq_weaken; simpl; auto. eapply closed_Qual_monotone; eauto. eauto.
apply Substq_weaken; simpl; eauto. replace ({♦}) with (q_trans [] Σ ∅ ⋒ q_trans [] Σ df); auto. rewrite q_trans_empty_id; auto.
Qed.

(* case for t_app_fresh *)
Lemma substitution2 : forall {bdx bdf t bf Tf df df1 Tx dx Σ T d},
  has_type [(bdx, false, Tx, q_trans [] Σ df ⋒ q_trans [] Σ dx);
            (bdf, bf, Tf, df1)] (df1 ⊔ $! 0 ⊔ $! 1) Σ t T d ->
            df1 ⊑↑ df ->
            wf_senv Σ ->
            forall {vf φ}, vtp Σ φ vf Tf df -> ♦∉ df -> closed_Qual 0 0 (‖Σ‖) df↑ ->
                         vtp Σ φ vf Tf df1 -> ♦∉ df1 -> closed_Qual 0 0 (‖Σ‖) df1↑ ->
            forall {vx φ'}, vtp Σ φ' vx Tx dx -> ♦∉ dx -> closed_Qual 0 0 (‖Σ‖) dx↑ ->
            has_type [] (df1 ⊔ dx) Σ
                ({ 0 |-> vf ; vx }ᵗ t)
                ({ 0 |-> Tf ~ df1 ; Tx ~ dx }ᵀ T)
                ({ 0 |-> df1 ; dx }ᵈ d).
  intros. rename H2 into Hvf. rename H5 into Hvf1. rename H8 into Hvx.
  pose proof (vtp_closed Hvf). pose proof (vtp_closed Hvf1). pose proof (vtp_closed Hvx).
  assert (qenv_saturated_q'' Σ df /\ qenv_saturated_q'' Σ df1 /\ qenv_saturated_q'' Σ dx). {
    apply vtp_saturated in Hvf. inversion Hvf.
    apply vtp_saturated in Hvf1. inversion Hvf1.
    apply vtp_saturated in Hvx. inversion Hvx.
    intuition; apply qenv_saturated_iff; auto.
  }
  assert (Hcl : closed_Qual 0 0 (‖ Σ ‖) (q_trans [] Σ df ⋒ q_trans [] Σ dx)↑). { apply closed_Qual_qor; auto. apply closed_Qual_qand; repeat apply closed_Qual_q_trans''_monotone; auto. all: apply closed_qenv_empty; apply []. }
  intuition. replace ([(bdx, false,Tx, q_trans [] Σ df ⋒ q_trans [] Σ dx); (bdf, bf,Tf, df)]) with ([(bdx, false,Tx, q_trans [] Σ df ⋒ q_trans [] Σ dx)] ++ [(bdf, bf,Tf, df)]) in H; auto.
  remember (q_trans ([(bdx, false, Tx, q_trans [] Σ df ⋒ q_trans [] Σ dx)] ++ [(bdf, bf, Tf, df1)]) Σ df1) as DF. remember (q_trans ([(bdx, false, Tx, q_trans [] Σ df ⋒ q_trans [] Σ dx)] ++ [(bdf, bf, Tf, df1)]) Σ (df1 ⊔ $!0 ⊔ $!1)) as Φ.
  assert (Hsepf : DF ⊓ Φ ⊑↑ df1). {
    subst. unfold q_trans,q_trans_tenv,q_trans_senv. repeat rewrite qenv_saturated_trans''_id with (q:=df1); auto. apply qand_Sub_l. unfold qenv_saturated_q''. rewrite q_trans_one_closed_id; auto. Qcrush.
  }
  subst. eapply (substitution_gen Hsepf) in H; eauto.
  replace ({0 |-> df1 }ᵈ (df1 ⊔ $!0 ⊔ $!1)) with (df1 ⊔ $!0) in H.
  remember (q_trans ([] ++ [(bdx, false, Tx, q_trans [] Σ df ⋒ q_trans [] Σ dx)]) Σ (df1 ⊔ $! 0)) as DF. remember (q_trans ([] ++ [(bdx, false, Tx, q_trans [] Σ df ⋒ q_trans [] Σ dx)]) Σ dx) as DX.
  assert (Hsepf' : DX ⊓ DF ⊑↑ q_trans [] Σ df ⋒ q_trans [] Σ dx). {
    subst. repeat rewrite <- q_trans_or_dist. unfold q_trans,q_trans_tenv,q_trans_senv. repeat rewrite qenv_saturated_trans''_id with (q:=dx); auto. repeat rewrite qenv_saturated_trans''_id with (q:=df); auto. repeat rewrite qenv_saturated_trans''_id with (q:=df1); auto. simpl. ndestruct (qfvs df1 0). exfalso. Qcrush. eauto. rewrite <- q_trans''_or_dist. rewrite q_trans''_senv_fv_id. rewrite <- q_trans''_or_dist. pose proof q_trans''_qand_subq Σ df dx (‖ Σ ‖). erewrite q_trans''_senv_freshv_id; eauto. repeat rewrite <- qor_assoc.
eapply @Subq_trans with (d2:=dx ⊓ (df1 ⊔ $! 0 ⊔ q_trans'' Σ df (‖ Σ ‖) ⊓ q_trans'' Σ dx (‖ Σ ‖) ⊔ {♦})); eauto. apply Subq_qand_split; auto. repeat rewrite qenv_saturated_trans''_id; auto. unfold qenv_saturated_q''. repeat rewrite qand_qor_dist_l. replace (dx ⊓ $! 0) with (∅). Qcrush. apply Q_lift_eq. Qcrush. eauto. 1,2: unfold qenv_saturated_q''; rewrite q_trans_one_closed_id; auto; Qcrush.
  }
  remember (q_trans [] Σ df ⋒ q_trans [] Σ dx) as q.
  replace ([(bdx, false, Tx, q_trans [] Σ df ⋒ q_trans [] Σ dx)]) with ([] ++ [(bdx, false, Tx, q_trans [] Σ df ⋒ q_trans [] Σ dx)]) in H; auto.
  replace ({0 |-> Tf ~ df1 }ᴳ [(bdx, false, Tx, q)]) with ([] ++ [(bdx, false, Tx, q)]) in H.
  subst. eapply (substitution_gen Hsepf') in H; eauto; auto.
  replace ({0 |-> dx }ᵈ (df1 ⊔ $!0)) with (df1 ⊔ dx) in H. simpl in H. apply H.
  (*done, prove earlier replacements *)
  repeat rewrite subst1_qor_dist. rewrite subst1_just_fv0. erewrite subst1_qual_id; eauto.
  constructor; auto.
  apply Substq_weaken; auto. simpl. apply closed_qenv_qn_empty. apply [].
  simpl. erewrite subst1_qual_id; eauto. erewrite subst1_ty_id; eauto.
  repeat rewrite subst1_qor_dist. rewrite subst1_just_fv0. rewrite <- subst1_just_fv.
  erewrite subst1_qual_id; eauto. rewrite (@qor_assoc df1 df1). rewrite qor_idem. auto.
  constructor; auto; simpl. eapply closed_ty_monotone; eauto. eapply closed_Qual_monotone; eauto.
Qed.

Lemma substitution_stp2 : forall{T1 T2},
    forall {bdx bdf Tx bf Tf df0 dx0 df dx Σ d1 d2},
      stp ([(bdx, false,Tx,q_trans [] Σ df0 ⋒ q_trans [] Σ dx0); (bdf, bf,Tf,{♦})]) Σ T1 d1 T2 d2 ->
      wf_senv Σ ->
      closed_ty 0 0 (‖Σ‖) Tx ->
      closed_ty 0 0 (‖Σ‖) Tf ->
      df ⊑↑ df0 -> dx ⊑↑ dx0 ->
      closed_Qual 0 0 (‖Σ‖) df0↑ -> closed_Qual 0 0 (‖Σ‖) dx0↑ -> ♦∉ df -> ♦∉ dx ->
      stp [] Σ
          ({ 0 |-> Tf ~ df; Tx ~ dx }ᵀ T1)
          ({ 0 |-> df ; dx }ᵈ d1)
          ({ 0 |-> Tf ~ df ; Tx ~ dx }ᵀ T2)
          ({ 0 |-> df ; dx }ᵈ d2).
  intros.  assert (Hcl : closed_Qual 0 0 (‖ Σ ‖) (q_trans [] Σ df0 ⋒ q_trans [] Σ dx0)↑). { apply closed_Qual_qor; auto. apply closed_Qual_qand; auto. all: apply closed_Qual_q_trans''_monotone; eauto; apply wf_senv_closed_qenv; auto. }
  remember ([(bdx, false, Tx, q_trans [] Σ df0 ⋒ q_trans [] Σ dx0); (bdf, bf, Tf, {♦})]) as Γ.
replace Γ with ([(bdx, false, Tx, q_trans [] Σ df0 ⋒ q_trans [] Σ dx0)] ++ [(bdf, bf, Tf, q_trans Γ Σ ∅ ⋒ q_trans Γ Σ df)]) in H; auto.
  eapply @subst_stp with (df':=df) in H; eauto.
(* constructor. *)
  replace ({0 |-> Tf ~ df }ᴳ [(bdx, false, Tx, q_trans [] Σ df0 ⋒ q_trans [] Σ dx0 )]) with ([(bdx, false, Tx, q_trans [] Σ df0 ⋒ q_trans [] Σ dx0 )]) in H.
  assert (H' : stp [(bdx, false, Tx, q_trans [] Σ df ⋒ q_trans [] Σ dx)] Σ ({0 |-> Tf ~ df }ᵀ T1) ({0 |-> df }ᵈ d1) ({0 |-> Tf ~ df }ᵀ T2) ({0 |-> df }ᵈ d2)). {
    destruct bdx.
        + eapply narrowing_stp; eauto. intros. discriminate. apply stp_refl; auto. constructor; auto. apply Subq_qor. apply Subq_qand_split; apply q_trans_subq; auto.
        + eapply narrowing_stp_ty; eauto. eapply closed_Qual_sub; eauto. apply Subq_qor; eauto. apply Subq_qand_split; apply q_trans_subq; auto. apply stp_refl; auto. constructor; auto. apply Subq_qor. apply Subq_qand_split; apply q_trans_subq; auto.
  }
  replace ([(bdx, false, Tx, df ⋒ dx )]) with ([] ++ [(bdx, false, Tx, df ⋒ dx)]) in H'; auto.
  replace ([]:tenv) with ({0 |-> Tx ~ dx}ᴳ ([]:tenv)); auto.
eapply subst_stp ; eauto.
  simpl. constructor; auto.
eapply closed_Qual_sub; eauto. apply Subq_qor. apply Subq_qand_split; apply q_trans_subq; auto.
apply Substq_weaken; auto. eapply @closed_Qual_sub with (d:=dx0); eauto. constructor; auto. eapply @closed_Qual_sub with (d:=df0); eauto.
  simpl. erewrite subst1_ty_id; eauto. erewrite subst1_qual_id; eauto.
constructor. constructor; auto. apply closed_Qual_qor; auto. apply closed_Qual_qand_r; auto. unfold q_trans,q_trans_tenv,q_trans_senv. repeat rewrite q_trans''_empty_id; Qcrush.
simpl. eapply closed_ty_monotone; eauto. simpl. eapply closed_Qual_monotone; eauto.
replace ([(bdf, bf, Tf, q_trans Γ Σ ∅ ⋒ q_trans Γ Σ df)]) with ([(bdf, bf, Tf, {♦})]).
subst. constructor; auto. rewrite q_trans_empty_id; auto.
subst. rewrite q_trans_empty_id; auto.
Qed.

(* case for t_tapp_fresh *)
Lemma substitution2_ty : forall {t df1 df Tf Tx dx Σ T d},
    has_type [(bind_ty, false,Tx, q_trans [] Σ df ⋒ q_trans [] Σ dx); (bind_tm, true,Tf,df1)] (df1 ⊔ $!0 ⊔ $!1) Σ t T d ->
    senv_saturated Σ dx ->
    senv_saturated Σ df ->
    ♦∉ dx ->
    wf_senv Σ ->
    closed_ty 0 0 (‖ Σ ‖) Tx ->
    closed_Qual 0 0 (‖Σ‖) dx↑ ->
    senv_saturated Σ dx ->
    df1 ⊑↑ df ->
    ♦∉ df ->
    closed_Qual 0 0 (‖Σ‖) df ↑ ->
    forall {vt φ},
    vtp Σ φ vt Tf df1 ->
    has_type [] (df1 ⊔ dx) Σ
                ({ 0 |-> vt; tunit }ᵗ t)
                ({ 0 |-> Tf ~ df1; Tx ~ dx}ᵀ T)
                ({ 0 |-> df1 ; dx }ᵈ d).
  intros.
  assert (qenv_saturated_q'' Σ df /\ qenv_saturated_q'' Σ df1 /\ qenv_saturated_q'' Σ dx). {
    apply vtp_saturated in H10. inversion H10.
    intuition; apply qenv_saturated_iff; auto.
  }
  assert (Hcl : closed_Qual 0 0 (‖ Σ ‖) (q_trans [] Σ df ⋒ q_trans [] Σ dx)↑). { apply closed_Qual_qor; auto. apply closed_Qual_qand; repeat apply closed_Qual_q_trans''_monotone; auto. all: apply closed_qenv_empty; apply []. }
  intuition. replace ([(bind_ty, false,Tx, q_trans [] Σ df ⋒ q_trans [] Σ dx); (bind_tm, true,Tf, df)]) with ([(bind_ty, false,Tx, q_trans [] Σ df ⋒ q_trans [] Σ dx)] ++ [(bind_tm, true,Tf, df)]) in H; auto.
  remember (q_trans ([(bind_ty, false, Tx, q_trans [] Σ df ⋒ q_trans [] Σ dx)] ++ [(bind_tm, true, Tf, df1)]) Σ df1) as DF. remember (q_trans ([(bind_ty, false, Tx, q_trans [] Σ df ⋒ q_trans [] Σ dx)] ++ [(bind_tm, true, Tf, df1)]) Σ (df1 ⊔ $!0 ⊔ $!1)) as Φ.
  assert (Hsepf : DF ⊓ Φ ⊑↑ df1). {
    subst. unfold q_trans,q_trans_tenv,q_trans_senv. repeat rewrite qenv_saturated_trans''_id with (q:=df1); auto. apply qand_Sub_l. unfold qenv_saturated_q''. rewrite q_trans_one_closed_id; auto. Qcrush.
  }
  subst. eapply (substitution_gen Hsepf) in H; eauto.
  replace ({0 |-> df1 }ᵈ (df1 ⊔ $!0 ⊔ $!1)) with (df1 ⊔ $!0) in H.
  remember (q_trans ([] ++ [(bind_ty, false, Tx, q_trans [] Σ df ⋒ q_trans [] Σ dx)]) Σ (df1 ⊔ $! 0)) as DF. remember (q_trans ([] ++ [(bind_ty, false, Tx, q_trans [] Σ df ⋒ q_trans [] Σ dx)]) Σ dx) as DX.
  assert (Hsepf' : DX ⊓ DF ⊑↑ q_trans [] Σ df ⋒ q_trans [] Σ dx). {
    subst. repeat rewrite <- q_trans_or_dist. unfold q_trans,q_trans_tenv,q_trans_senv. repeat rewrite qenv_saturated_trans''_id with (q:=dx); auto. repeat rewrite qenv_saturated_trans''_id with (q:=df); auto. repeat rewrite qenv_saturated_trans''_id with (q:=df1); auto. simpl. ndestruct (qfvs df1 0). exfalso. Qcrush. eauto. rewrite <- q_trans''_or_dist. rewrite q_trans''_senv_fv_id. rewrite <- q_trans''_or_dist. pose proof q_trans''_qand_subq Σ df dx (‖ Σ ‖). erewrite q_trans''_senv_freshv_id; eauto. repeat rewrite <- qor_assoc.
eapply @Subq_trans with (d2:=dx ⊓ (df1 ⊔ $! 0 ⊔ q_trans'' Σ df (‖ Σ ‖) ⊓ q_trans'' Σ dx (‖ Σ ‖) ⊔ {♦})); eauto. apply Subq_qand_split; auto. repeat rewrite qenv_saturated_trans''_id; auto. unfold qenv_saturated_q''. repeat rewrite qand_qor_dist_l. replace (dx ⊓ $! 0) with (∅). Qcrush. apply Q_lift_eq. Qcrush. eauto. 1,2: unfold qenv_saturated_q''; rewrite q_trans_one_closed_id; auto; Qcrush.
  }
  remember (q_trans [] Σ df ⋒ q_trans [] Σ dx) as q.
  replace ([(bind_ty, false, Tx, q)]) with ([] ++ [(bind_ty, false, Tx, q)]) in H; auto.
  replace ({0 |-> Tf ~ df1 }ᴳ [(bind_ty, false, Tx, q)]) with ([] ++ [(bind_ty, false, Tx, q)]) in H.
  subst. eapply (substitution_ty_gen Hsepf') in H; eauto; auto.
  replace ({0 |-> dx }ᵈ (df1 ⊔ $!0)) with (df1 ⊔ dx) in H. simpl in H. apply H.
  (*done, prove earlier replacements *)
  repeat rewrite subst1_qor_dist. rewrite subst1_just_fv0. erewrite subst1_qual_id; eauto.
  constructor; auto.
  apply Substq_weaken; auto. simpl. apply closed_qenv_qn_empty. apply [].
  simpl. erewrite subst1_qual_id; eauto. erewrite subst1_ty_id; eauto.
  repeat rewrite subst1_qor_dist. rewrite subst1_just_fv0. rewrite <- subst1_just_fv.
  erewrite subst1_qual_id; eauto. rewrite (@qor_assoc df1 df1). rewrite qor_idem. auto.
  constructor; auto; simpl. constructor; auto; simpl. 1,2: apply vtp_closed in H10; intuition. eapply closed_ty_monotone; eauto. eapply closed_Qual_monotone; eauto. constructor. Qcrush.
Qed.

Lemma open_qual_mono : forall {d1 d1' d2 k}, d1 ⊑↑ d1' -> ([[ k ~> d1 ]]ᵈ d2) ⊑↑ ([[ k ~> d1' ]]ᵈ d2).
  intros. unfold_q. qual_destruct d2; qual_destruct d1'; qual_destruct d1. simpl. ndestruct (bvs k); Qcrush.
Qed.

Lemma open_qual_mono2 : forall {d1 d2 d2' k}, d2 ⊑↑ d2' -> ([[ k ~> d1 ]]ᵈ d2) ⊑↑ ([[ k ~> d1 ]]ᵈ d2').
  intros. unfold_q. qual_destruct d2; qual_destruct d2'; qual_destruct d1. simpl.
  ndestruct (bvs0 k); ndestruct (bvs k); Qcrush.
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

(* Some distributive laws about openq and qqplus, required in the type safety proof for function application t_app. *)
Lemma open_qual_duplicate_eq : forall {k d1 d2 d}, ♦∈ d1 ->
  ([[ k ~> d1 ]]ᵈ d2 ⋓ d) = ([[ k ~> d1 ⋓ d ]]ᵈ d2 ⋓ d).
  intros. apply Q_lift_eq. qual_destruct d1. qual_destruct d2. unfold_q. destruct fr; auto.
ndestruct (bvs0 k); destruct (fr0); Qcrush.
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
  intros. unfold openq. erewrite open_qual_commute''; eauto using closed_qual_open'.
Qed.

Lemma openQ_closed : forall {a b c f l},
    closed_Qual 2 f l c↑ -> closed_Qual 0 f l a↑ -> closed_Qual 0 f l b↑ -> closed_Qual 0 f l (openq a b c)↑.
  intros. apply Q_lift_closed'. unfold openq. erewrite open_qual_commute''; eauto using closed_qual_open'.
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
  intros. inversion H; subst. auto. econstructor; eauto using Subq_trans.
Qed.
#[global] Hint Resolve disjointq_scale : core.

Lemma qdom_fresh : forall {A} {Σ : list A}, {♦} ⊑↑ qdom Σ.
  intros. Qcrush.
Qed.
#[global] Hint Resolve qdom_fresh : core.

(* well-typed values belonging to each type *)

Lemma vtp_canonical_form_loc : forall {Σ φ t T q d},
   vtp Σ φ t (TRef q T) d -> value t -> exists (l : loc), t = tloc l.
Proof. intros. remember (TRef q T) as R. remember t as tt. generalize dependent T.
       induction H; intuition; try discriminate; inversion H0; subst. exists l. intuition.
Qed.

Lemma vtp_canonical_form_lam : forall {Σ φ t T1 T2 d1 d2 df},
    vtp Σ φ t (TFun d1 d2 T1 T2) df -> value t -> exists (t' : tm), t = tabs t'.
Proof. intros Σ φ t T1 T2 d1 d2 df H. remember (TFun d1 d2 T1 T2) as T.
       generalize dependent d1. generalize dependent d2. generalize dependent T1. generalize dependent T2.
       induction H; intuition; try discriminate; inversion H0; subst. exists t. intuition.
Qed.

Lemma qstp_delete_fresh : forall {Σ q1 q2}, qstp [] Σ q1 q2 -> ♦∉ q1 -> qstp [] Σ q1 (false, (qfvs q2), (qbvs q2), (qlocs q2)).
  intros. specialize (qstp_closed H) as Hcl. intuition. apply qstp_empty in H. apply qs_sq. Qcrush. Qcrush.
Qed.

Lemma senv_saturated_non_fresh : forall {Σ q}, wf_senv Σ -> senv_saturated Σ q -> senv_saturated Σ (false, (qfvs q), (qbvs q), (qlocs q)).
  intros. unfold senv_saturated,qenv_saturated_q in *. intros. specialize (H0 x a). simpl in *. intuition.
  destruct a. eapply wf_senv_prop with (l:=x) in H; eauto. intuition. Qcrush.
Qed.

Lemma vtp_non_fresh : forall {Σ φ v T q}, vtp Σ φ v T q -> wf_senv Σ -> vtp Σ φ v T (false, (qfvs q), (qbvs q), (qlocs q)).
Proof. intros. induction H.
  + apply qstp_closed in H5 as Hcl_qstp.  intuition. eapply vtp_tabs; eauto.
    apply qstp_empty in H5. econstructor; eauto. Qcrush.
    apply senv_saturated_non_fresh; auto.
  + inversion H. subst. econstructor; auto. apply senv_saturated_non_fresh; auto.
  + inversion H2. inversion H3. intuition.
    assert (♦∉ q2). eapply qstp_non_fresh; eauto.
    econstructor. Focus 6. eapply H5. all: eauto.
    apply qstp_delete_fresh; auto. Qcrush.
    apply senv_saturated_non_fresh. auto. auto.
  + inversion H2. subst. econstructor; eauto.
    apply qstp_delete_fresh; auto. Qcrush.
    apply senv_saturated_non_fresh; auto.
  + apply vtp_closed in IHvtp as Hcl_vtp; intuition. eapply vtp_top; eauto. apply senv_saturated_non_fresh; auto.
Qed.

Lemma stp_set_not_fresh : forall {d1 T Γ Σ}, closed_ty 0 (‖Γ‖) (‖Σ‖) T -> closed_Qual 0 (‖Γ‖) (‖Σ‖) d1↑ -> stp Γ Σ T (false, (qfvs d1), (qbvs d1), (qlocs d1)) T d1.
  intros. apply stp_refl; auto. constructor; auto. Qcrush.
Qed.
#[global] Hint Resolve stp_set_not_fresh : core.

Lemma openq_subqual_0 : forall {df d2 d1 l}, closed_Qual 0 0 l df↑ -> closed_Qual 0 0 l d1↑ -> N_lift (qbvs d2) 0 -> df ⊑↑ d2 <~ᵈ df; d1.
  intros.
qual_destruct d2. qual_destruct d1. qual_destruct df. unfold openq. unfold_q. clift. simpl.
ndestruct (n_or (n_diff bvs (n_one 0)) bvs1 1); Qcrush; exfalso; eauto.
Qed.

Lemma openq_subqual_0_false : forall {df d2 d1}, ~N_lift (qbvs d2) 0 -> forall {df'}, d2 <~ᵈ df; d1 = d2 <~ᵈ df'; d1.
  intros. unfold openq. unfold_q. clift. apply Q_lift_eq. Qcrush.
Qed.

Lemma openq_subqual_1 : forall {df d2 d1 l}, closed_Qual 0 0 l df↑ -> closed_Qual 0 0 l d1↑ -> N_lift (qbvs d2) 1 -> d1 ⊑↑ d2 <~ᵈ df; d1.
  intros.
  qual_destruct d2. unfold openq. unfold_q.
ndestruct (bvs 0); simpl; clift. ndestruct (n_or (n_diff bvs (n_one 0)) (snd (fst df)) 1).
all: Qcrush.
Qed.

Lemma openq_subqual_1_false : forall {df d2 d1 l}, closed_Qual 0 0 l df↑ -> ~N_lift (qbvs d2) 1 -> forall {d1'}, d2 <~ᵈ df; d1 = d2 <~ᵈ df; d1'.
intros. qual_destruct d2. qual_destruct df. unfold openq. unfold_q.
ndestruct (bvs 0); simpl; clift; auto.
ndestruct (n_or (n_diff bvs (n_one 0)) bvs0 1); auto.
exfalso. assert (~N_lift (n_diff bvs (n_one 0)) 1). Qcrush. assert (~N_lift bvs0 1). Qcrush. eauto. Qcrush.
Qed.

Lemma open_qual_not_free : forall {k q}, [[k ~> ∅ ]]ᵈ q = q -> forall {q'}, [[k ~> q' ]]ᵈ q = q.
  intros. qual_destruct q. qual_destruct q'. unfold_q.
ndestruct (bvs k); auto.
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

Lemma qqplus_upper_l : forall {d1 d2}, d1 ⊑ (d1 ⋓ d2).
  intros. apply Q_lift_subq. apply Qqplus_upper_l.
Qed.

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

Lemma subqual_qqplus : forall {d1 d2 d}, d1 ⊑ d2 -> d1 ⋓ d ⊑ d2 ⋓ d.
  intros. apply Q_lift_subq. apply Q_lift_subq' in H. apply Subqual_qqplus; auto.
Qed.

Lemma Subqual_qqplus_l : forall {d1 d2 d}, d1 ⊑↑ d2 -> d ⋓ d1 ⊑↑ d ⋓ d2.
  intros. qual_destruct d. qual_destruct d1. qual_destruct d2. unfold_q. destruct fr; destruct fr0; Qcrush.
Qed.

Lemma subqual_qqplus_l : forall {d1 d2 d}, d1 ⊑ d2 -> d ⋓ d1 ⊑ d ⋓ d2.
  intros. apply Q_lift_subq. apply Q_lift_subq' in H. apply Subqual_qqplus_l; auto.
Qed.

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

Lemma closed_qand_locs_empty : forall {b f l} q,
  closed_Qual b f l q↑ ->
  forall l', l' >= l ->
  q ⊓ &! l' = ∅.
intros. apply Q_lift_eq. Qcrush. subst. eauto.
Qed.

Lemma set_union_fresh : forall {fr : bool} {fvs bvs lcs : nats},
    ((fr, fvs, bvs, lcs) ⊔ ({♦})) = (true, fvs, bvs, lcs).
Proof.
  intros. cbv. Qcrush. destruct fr; auto.
  destruct (fvs x); intuition. destruct (bvs x); intuition. destruct (lcs x); intuition.
Qed.

Lemma Subqual_non_fresh : forall {d1 d2}, (♦∈ d1 -> False) -> d1 ⊑↑ d2 ⊔ {♦} -> d1 ⊑↑ d2.
Proof.
  intros.
  qual_destruct d1. destruct fr. Qcrush.
  qual_destruct d2. rewrite set_union_fresh in H0. destruct fr; Qcrush.
Qed.

Lemma vtp_store_loc_defined : forall {Σ φ σ l d T d'},
    CtxOK [] φ Σ σ ->
    vtp Σ φ (& l) (TRef d T) d' ->
    exists v, indexr l σ = Some (Some v).
Proof.
  intros. inversion H. inversion H0. subst. intuition.
  assert (l ∈ₗ qdom' σ). Qcrush. unfold qmem, N_lift in H4. simpl in H4.
  unfold n_dom' in H4. apply andb_true_iff in H4. destruct H4.
  destruct (indexr l σ) eqn:?. destruct o. exists t. auto. intuition. intuition.
Qed.
Lemma mem_subset_loc : forall {x q}, x ∈ₗ q <-> (&! x) ⊑↑ q.
Proof. split; intro. Qcrush. subst. auto. Qcrush. Qed.

Lemma openq_subqual_trans : forall {d1 d2 d3 φ φ' f l f' l'},
    closed_Qual 0 f l φ↑ ->
    closed_Qual 0 f' l' (φ' ⊔ {♦})↑ ->
    d2 <~ᵈ ∅; ∅ ⊑↑ (φ ⊔ {♦}) ->
    d1 ⊑↑ φ ->
    d3 ⊑↑ (φ ⊔ {♦}) ->
    φ ⊑↑ φ' ->
    d2 <~ᵈ d3; d1 ⊑↑ φ' ⊔ {♦}.
Proof.
  intros.
  assert (φ ⊑↑ φ' ⊔ {♦}). Qcrush.
  assert (φ ⊔ {♦} ⊑↑ φ' ⊔ {♦}). Qcrush.
  assert (d3 ⊑↑ φ' ⊔ {♦}). Qcrush.
  assert (d2 <~ᵈ ∅; ∅ ⊑↑ φ' ⊔ {♦}). eapply Subq_trans; eauto.
  assert (d1 ⊑↑ φ' ⊔ {♦}). eapply Subq_trans; eauto.
  eapply openq_subqual; eauto.
Qed.

Lemma openq_subqual_trans' : forall {df d1 d2 d' φ φ' f l f' l'},
    closed_Qual 0 f l φ↑ -> closed_Qual 0 f' l' (φ' ⊔ {♦})↑ ->
    df ⊑↑ φ ⊔ {♦} ->
    d2 <~ᵈ ∅; ∅ ⊑↑ φ ⊔ {♦} ->
    d1 ⊑↑ φ -> d' ⊑↑ φ' -> φ ⊑↑ φ' ->
    d2 <~ᵈ (df ⋓ d'); d1 ⊑↑ φ' ⊔ {♦}.
Proof.
  intros.
  assert (φ ⊑↑ φ' ⊔ {♦}). Qcrush.
  assert (φ ⊔ {♦} ⊑↑ φ' ⊔ {♦}). Qcrush.
  assert (df ⊑↑ φ' ⊔ {♦}). eapply Subq_trans; eauto.
  assert (df ⋓ d' ⊑↑ φ' ⊔ {♦}). eapply Qqplus_bound; eauto. Qcrush.
  assert (d2 <~ᵈ ∅; ∅ ⊑↑ φ' ⊔ {♦}). eapply Subq_trans; eauto.
  assert (d1 ⊑↑ φ' ⊔ {♦}). eapply Subq_trans; eauto.
  eapply openq_subqual; eauto.
Qed.

Lemma openq_subqual_trans'2 : forall {df d1 d2 d' φ φ' f l f' l'},
    closed_Qual 0 f l φ↑ -> closed_Qual 0 f' l' (φ' ⊔ {♦})↑ ->
    df ⊑↑ φ ⊔ {♦} ->
    d2 <~ᵈ ∅; ∅ ⊑↑ φ ⊔ {♦} ->
    d1 ⊑↑ (φ ⊔ {♦}) -> d' ⊑↑ φ' -> φ ⊑↑ φ' ->
    d2 <~ᵈ (df ⋓ d'); d1 ⊑↑ φ' ⊔ {♦}.
Proof.
  intros.
  assert (φ ⊑↑ φ' ⊔ {♦}). Qcrush.
  assert (φ ⊔ {♦} ⊑↑ φ' ⊔ {♦}). Qcrush.
  assert (df ⊑↑ φ' ⊔ {♦}). eapply Subq_trans; eauto.
  assert (df ⋓ d' ⊑↑ φ' ⊔ {♦}). eapply Qqplus_bound; eauto. Qcrush.
  assert (d2 <~ᵈ ∅; ∅ ⊑↑ φ' ⊔ {♦}). eapply Subq_trans; eauto.
  assert (d1 ⊑↑ φ' ⊔ {♦}). eapply Subq_trans; eauto.
  eapply openq_subqual; eauto.
Qed.

Lemma openq_subqual_trans'' : forall {df d1 d2 d' φ φ' f l f' l'},
    closed_Qual 0 f l φ↑ -> closed_Qual 0 f' l' (φ' ⊔ {♦})↑ ->
    d2 <~ᵈ ∅; ∅ ⊑↑ φ ⊔ {♦} ->
    df ⊑↑ φ ⊔ {♦} -> d1 ⊑↑ φ ⊔ {♦} ->
    d' ⊑↑ φ' -> φ ⊑↑ φ' ->
    d2 <~ᵈ df; (d1 ⋓ d') ⊑↑ φ' ⊔ {♦}.
Proof.
  intros.
  assert (φ ⊑↑ φ' ⊔ {♦}). Qcrush.
  assert (φ ⊔ {♦} ⊑↑ φ' ⊔ {♦}). Qcrush.
  assert (df ⊑↑ φ' ⊔ {♦}). eapply Subq_trans; eauto.
  assert (d1 ⊑↑ φ' ⊔ {♦}). eapply Subq_trans; eauto.
  assert (d1 ⋓ d' ⊑↑ φ' ⊔ {♦}). eapply Qqplus_bound; eauto. Qcrush.
  assert (d2 <~ᵈ ∅; ∅ ⊑↑ φ' ⊔ {♦}). eapply Subq_trans; eauto.
  eapply openq_subqual; eauto.
Qed.

Lemma closed_Qual_qor_fresh : forall {f l q}, closed_Qual 0 f l q↑ -> closed_Qual 0 f l (q ⊔ {♦})↑.
Proof. intros. eapply closed_Qual_qor; eauto. Qed.

Theorem type_safety: forall {Σ t T d φ},
  has_type [] φ Σ t T d -> wf_senv Σ -> (
    value t \/
    (forall {σ} , CtxOK [] φ Σ σ ->
      (exists t' σ',
        step t σ t' σ' /\ preserve [] Σ φ t' T d σ'
      )
    )
  ).
Proof.
  intros Σ t T d φ (* Hphifr *) H HwfSigma.
  specialize (has_type_closed H) as HX. remember [] as G. remember t as tt. remember T as TT. (* remember (qdom Σ) as φ. *)
  revert T t HeqTT Heqtt HeqG (* Heqφ *).
  induction H; try (left; constructor); intros.
  - (* ttapp *) right. subst. intuition.
     apply has_type_closed in H as HH. intuition.
     specialize (H13 (TAll d1 d2 T1 T2) t). intuition.
     + (* contraction *)
       (* turn has_type to vtp *)
       apply has_type_vtp in H as VH; intuition.
       pose (VHH := VH). inversion VH. subst.
       specialize (has_type_filter H) as Hflt0.
       apply has_type_vtp in H as VH0; intuition.
       exists (t0 <~ᵗ (ttabs t0); tunit). exists σ. intuition.
       * constructor.
       * apply (Preserve Σ ∅ φ); auto.  rewrite qqplus_qbot_right_neutral.
         apply qstp_closed in H27 as H27'; intuition.
         change (length []) with 0 in *. subst.
         pose (VH' := H25). eapply t_tabs with (φ:=df1) in VH'; eauto. apply has_type_vtp in VH'; auto.
         assert (HT' : has_type [(bind_ty, false, T1, d1) ; (bind_tm, true, TAll d0 d3 T0 T3, df1)] (df1 ⊔ $!0 ⊔ $!1) Σ (open_tm' ([]:tenv) t0) (open_ty' ([]:tenv) T3) (openq' ([]:tenv) d3)). {
           eapply narrowing. eapply H25. intuition. auto. apply stp_qstp_inv in H26. eapply qstp_empty; eauto. auto.
         }
         eapply @substitution1_ty in HT' as HT''; eauto; intuition.
         unfold open_tm' in HT''. unfold open_ty' in HT''. unfold openq' in HT''. simpl in HT''. inversion H23. inversion H24. subst.
         unfold open_ty in HT''. unfold openq in HT''.
         erewrite <- open_subst2_tm in HT''; eauto.
         erewrite <- open_subst2_ty in HT''; eauto.
         erewrite <- open_subst2_qual in HT''; eauto.
         fold (open_tm (ttabs t0) t0 t0) in HT''. fold (openq df1 d1 d3) in HT''. fold (open_ty (TAll d0 d3 T0 T3) df1 T1 d1 T3) in HT''.
         apply @weaken_flt with (φ':= φ) in HT''; auto; intuition.
         eapply t_sub; eauto.
         pose (Hsub:=H28). eapply @substitution_stp1 with (df:=df1) in Hsub; eauto.
         simpl in Hsub. unfold openq' in Hsub. unfold openq in Hsub. unfold open_ty' in Hsub. unfold open_ty in Hsub. simpl in Hsub.
         erewrite <- open_subst2_ty in Hsub; eauto. erewrite <- open_subst2_ty in Hsub; eauto.
         erewrite <- open_subst2_qual in Hsub; eauto. erewrite <- open_subst2_qual in Hsub; eauto.
         unfold open_ty. unfold openq.
         replace ([[0 ~> TUnit ~ ∅ ]]ᵀ T2) with ([[0 ~> TAll d0 d3 T0 T3 ~ df1 ]]ᵀ T2); auto. (* since not_free 0 T2 *)
         eapply s_trans; eauto. apply stp_refl; auto. apply closed_ty_open2; auto.
         constructor. eapply openq_mono; eauto. apply qstp_empty in H27. auto. apply openq_closed; auto.
         eapply openq_subqual; eauto using closed_Qual_qor. eapply Subq_trans; eauto.
         eapply senv_saturated_openq; eauto. repeat apply Qor_bound; auto.
         assert (df1  ⊑↑ φ ⊔ {♦}). eapply qstp_empty in H27. eapply Subq_trans; eauto.
         eapply Subqual_non_fresh; eauto.
     + (* left congruence *)
       specialize (H13 σ H11). destruct H13 as [t0' [σ' HH5]]. exists (ttapp t0'). exists σ'. intuition.
       constructor. intuition. destruct H17. ndestruct ((qbvs d2) 0).
       * (* d2 is dependent on f, so the growth in df might be observable  *)
         apply (Preserve Σ' d' φ'); auto.
         -- eapply disjointq_scale; eauto. eapply openq_subqual_0; eauto. (* this is the sole reason why need to distinguish whether d2 is dependent on f or not *)
         -- inversion H15. subst. destruct (♦∈? df) eqn:Hfresh.
            ** erewrite @openq_duplicate_eq_l with (f:=0) (l:=‖Σ'‖). 3,4 : eapply closed_Qual_monotone; eauto. 2,3 : eauto.
               eapply t_sub with (T1 := (T2 <~ᵀ TUnit ~ ∅; T1 ~ d1))(d1 := (openq (df ⋓ d') d1 d2)).
               --- apply t_tapp; auto; apply extends_length in H17 as H17'.
                   eapply closed_ty_monotone; eauto.
                   eapply closed_Qual_monotone; eauto.
                   eapply Subq_trans; eauto.
                   eapply Subq_trans; eauto.
                   eapply weaken_store_senv_saturated. eauto.
                   apply closed_Qual_open2; eauto. eauto.
                   eapply weaken_store_senv_saturated; eauto.
               --- apply stp_refl. simpl. eapply closed_ty_monotone; eauto.
                   constructor; auto. apply closed_Qual_qqplus; auto.
                   apply openQ_closed. 2 : apply closed_qual_qqplus.
                   1,2,4 : eapply closed_qual_monotone; eauto; lia. all: eapply disjointq_closed; eauto.
               --- apply has_type_filter in H. apply Qqplus_bound.
                   eapply openq_subqual_trans'. eapply H8. 2-7: eauto.
                   apply has_type_closed in H24. intuition. apply closed_Qual_qor_fresh in H26. eauto. Qcrush.
               --- apply senv_saturated_qqplus; eauto. eapply senv_saturated_openq.
                   apply senv_saturated_qqplus; eauto.
                   eapply weaken_store_senv_saturated; eauto.
                   eapply has_type_senv_saturated; eauto.
                   apply closed_Qual_qqplus; eapply closed_Qual_monotone; eauto.
                   eapply weaken_store_senv_saturated; eauto. eapply closed_Qual_monotone; eauto.
                   eapply weaken_store_senv_saturated. eauto. eapply closed_Qual_open2; eauto. eauto.
            ** rewrite not_fresh_qqplus in H24; auto. apply t_sub with (T1:=(T2 <~ᵀ TUnit ~ ∅; T1 ~ d1)) (d1:=d2 <~ᵈ df; d1).
               --- apply extends_length in H17 as H17'. apply t_tapp; auto.
                   eapply closed_ty_monotone; eauto.
                   eapply closed_Qual_monotone; eauto.
                   eapply Subq_trans; eauto. eapply Subq_trans; eauto.
                   eapply weaken_store_senv_saturated. eauto. eapply closed_Qual_open2; eauto. eauto.
                   eapply weaken_store_senv_saturated; eauto.
               --- apply stp_refl. simpl. eapply closed_ty_monotone; eauto.
                   constructor. auto. apply closed_qual_qqplus; auto.
                   apply openq_closed; try solve [eapply closed_qual_monotone; eauto]. eauto.
               --- apply Qqplus_bound. apply has_type_filter in H.
                   apply has_type_closed in H24. intuition. apply closed_Qual_qor_fresh in H26.
                   eapply openq_subqual_trans. eapply H8. all: eauto. Qcrush.
               --- apply senv_saturated_qqplus; eauto. eapply weaken_store_senv_saturated; eauto. eapply senv_saturated_openq.
                   eapply has_type_senv_saturated; eauto. apply has_type_closed in H. intuition. eauto. all : auto.
       * (* d2 is not dependent on f, so we don't observe the growth in df *)
         inversion H15. subst. apply (Preserve Σ' ∅ φ'); auto. rewrite qqplus_qbot_right_neutral.
         replace (d2 <~ᵈ df; d1) with (d2 <~ᵈ df ⋓ d'; d1). (* since f doesn't occur in d2 *)
         apply t_tapp; auto. eapply closed_ty_monotone; eauto.
         eapply closed_Qual_monotone; eauto.
         eapply Subq_trans; eauto. eapply Subq_trans; eauto.
         eapply weaken_store_senv_saturated. eauto. eapply closed_Qual_open2; eauto. eauto.
         eapply weaken_store_senv_saturated; eauto. apply openq_subqual_0_false; auto.
  - (* t_tapp_fresh *) right. subst. intuition.
     apply has_type_closed in H as HH. intuition.
     specialize (H14 (TAll (q_trans [] Σ df ⋒ q_trans [] Σ d1) d2 T1 T2) t). intuition.
     + (* contraction *)
       (* turn has_type to vtp *)
       apply has_type_vtp in H as VH; intuition.
       pose (VHH := VH). inversion VH. subst.
       exists (t0 <~ᵗ (ttabs t0); tunit). exists σ. intuition.
       * constructor.
       * apply (Preserve Σ ∅ φ); auto. rewrite qqplus_qbot_right_neutral.
         apply qstp_closed in H28 as H28'; intuition.
         change (length []) with 0 in *. subst.
         pose (VH' := H26). eapply t_tabs with (φ:=df1) in VH'; eauto. apply has_type_vtp in VH'; auto.
         (* remove potential freshness flag from the argument, in order to apply substitution lemma *)
         remember (false,(qfvs d1),(qbvs d1),(qlocs d1)) as d1''.
         remember (false,(qfvs df),(qbvs df),(qlocs df)) as df''.
         assert (Hd1'' : d1'' ⊑↑ d1). { subst. Qcrush. }
         assert (Hdf'' : df'' ⊑↑ df). { subst. Qcrush. }
         assert (Hdf1 : df1 ⊑↑ df). { apply qstp_empty in H28. Qcrush. }
         assert (Hd1''fr : ♦∉ d1''). { subst. auto. }
         assert (Hdf''fr : ♦∉ df''). { subst. auto. }
         assert (Hqand: (q_trans [] Σ df'' ⋒ q_trans [] Σ d1'') ⊑↑ (q_trans [] Σ df ⋒ q_trans [] Σ d1)). {
           apply Subq_qor. apply Subq_qand_split; auto. all: apply q_trans_subq; eauto.
         }
         assert (HT' : has_type [(bind_ty, false, T1, q_trans [] Σ df'' ⋒ q_trans [] Σ d1''); (bind_tm, true, TAll d0 d3 T0 T3, df1)] (df1 ⊔ $!0 ⊔ $!1) Σ (open_tm' ([]:tenv) t0) (open_ty' ([]:tenv) T3) (openq' ([]:tenv) d3)). {
           eapply narrowing. eapply H26. intuition. apply @s_trans with (T2:=T1) (d2:=q_trans [] Σ df ⋒ q_trans [] Σ d1); auto. apply stp_refl; auto. constructor; auto. apply closed_Qual_qor; auto. apply closed_Qual_qand; auto. 1,2: apply closed_Qual_q_trans''_monotone; auto; apply wf_senv_closed_qenv; auto.
           apply stp_qstp_inv in H27. apply qstp_empty in H27. eapply Subq_trans; eauto. auto.
         }
         eapply @substitution2_ty with (dx:=d1'') in HT' as HT''; eauto; intuition.
         unfold open_tm' in HT''. unfold open_ty' in HT''. unfold openq' in HT''. simpl in HT''. inversion H24; inversion H25; subst.
         unfold open_ty in HT''. unfold openq in HT''.
         erewrite <- open_subst2_tm in HT''; eauto.
         erewrite <- open_subst2_ty in HT''; eauto.
         erewrite <- open_subst2_qual in HT''; eauto.
         fold (open_tm (ttabs t0) tunit t0) in HT''. fold (openq df1 (false,(qfvs d1),(qbvs d1),(qlocs d1)) d3) in HT''.
         apply @weaken_flt with (φ':= φ) in HT''; auto; intuition.
         eapply t_sub; eauto. rename H29 into Hsub.
         eapply @substitution_stp2 in Hsub; eauto.
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
            intuition. replace (T2 <~ᵀ TUnit ~ ∅; T1 ~ d1) with T2. replace (T2 <~ᵀ (TAll d0 d3 T0 T3) ~ df1; T1 ~ (false,(qfvs d1),(qbvs d1),(qlocs d1))) with T2 in Hsub. (* since no dependence *)
            eapply s_trans; eauto. apply stp_refl; auto. apply not_free_prop3; auto. apply not_free_prop3; auto.
            constructor; auto. eapply openq_mono; eauto.
            all : unfold open_ty; rewrite not_free_prop1; auto. all : rewrite not_free_prop1; auto.
         ++ (* d1 non-fresh *)
            assert (Hd1 : (false,(qfvs d1),(qbvs d1),(qlocs d1))= d1). { apply Q_lift_eq. clear - Hfresh. Qcrush; eauto. }
            rewrite Hd1 in *. replace (T2 <~ᵀ TUnit ~ ∅; T1 ~ d1) with (T2 <~ᵀ (TAll d0 d3 T0 T3) ~ df1; T1 ~ d1). (* since no dependence *)
            eapply s_trans; eauto. apply stp_refl; auto. apply closed_ty_open2; auto. constructor; auto.
            eapply openq_mono; eauto.
            unfold open_ty. f_equal. auto.
         }
         eapply has_type_filter in H as dfFil. eapply openq_subqual; eauto using closed_Qual_qor.
         eapply senv_saturated_openq; eauto. eapply has_type_filter in H.
         assert (Hbdf1: df1 ⊑↑ φ ⊔ {♦}). eapply Subq_trans; eauto. assert (Hbd1: d1 ⊑↑ φ ⊔ {♦}). auto.
         qual_destruct φ. qual_destruct df1. qual_destruct d1.
         unfold_q. unfold_Q. apply Is_true_eq_false in H35; subst.
         unfold_N. destruct Hbdf1 as [? [? [? ?]]]. destruct Hbd1 as [? [? [? ?]]].
         repeat split; auto; intros ? Hpp; rewrite N_lift_or in Hpp; unfold N_lift in *;
           destruct Hpp; try rewrite <- N_lift_n_or_empty_right; intuition.
         1-3: subst; apply senv_saturated_non_fresh; eauto. subst. Qcrush.
     + (* left congruence *)
        apply has_type_closed in H as Hcl. intuition.
        specialize (H14 σ H12). destruct H14 as [t1' [σ' HH1]]. exists (ttapp t1'). exists σ'. intuition. apply step_c_tapp. intuition.
        inversion H16. subst. destruct H22. destruct (♦∈? df) eqn:Hfresh.
        * (* df fresh *)
          ndestruct (qbvs d2 0).
          -- (* d2 dependent on f *) apply (Preserve Σ' d' φ'); auto.
            eapply disjointq_scale; eauto. eapply openq_subqual_0; eauto.
            erewrite @openq_duplicate_eq_l with (l:=‖Σ'‖) (f:=0); auto. 2,3 : eapply closed_qual_monotone; eauto. 2: eauto.
            apply t_sub with (T1 := (T2 <~ᵀ TUnit ~ ∅; T1 ~ d1)) (d1 := (openq (df ⋓ d') d1 d2)).
             ** eapply t_tapp_fresh with (T1:=T1). erewrite <- @qqcap_fresh_l' with (Σ':=Σ'); eauto.
                unfold q_trans,q_trans_senv,q_trans_tenv in *. simpl in *.
                rewrite q_trans''_extend_closed_id with (E:=Σ) (q:=d1); auto. rewrite q_trans''_fuel_max with (q:=d1).
                rewrite q_trans''_extend_closed_id with (E:=Σ) (q:=df); auto. rewrite q_trans''_fuel_max with (q:=df).
                eapply weaken_flt. eapply weaken_store; eauto.
                apply closed_qenv_empty. apply [].
                all: auto. eapply has_type_closed in H29. Qcrush.
                1,2: Qcrush.
                eapply closed_ty_monotone; eauto. eapply closed_Qual_monotone; eauto.
                eauto using Subq_trans. eapply weaken_store_senv_saturated; eauto.
                eauto using Subq_trans. apply Qor_bound; auto. apply has_type_closed in H29. intuition.
                eapply @Subq_trans with (d2:=q_trans [] Σ' d1). Qcrush.
                unfold q_trans,q_trans_tenv,q_trans_senv. simpl. erewrite q_trans''_extend_closed_id; eauto.
                rewrite q_trans''_fuel_max; auto. rewrite qenv_saturated_trans''_id. eapply Subq_trans.
                eapply H2. Qcrush. unfold senv_saturated in H4. eapply qenv_saturated_iff; eauto.
                Qcrush. eapply weaken_store_senv_saturated. eauto. eapply closed_Qual_open2; eauto. eauto.
             ** apply has_type_closed in H29. intuition. inversion H20. subst.
                apply stp_refl. simpl. eapply closed_ty_monotone; eauto.
                constructor; auto. apply closed_Qual_qqplus; auto. apply openQ_closed.
                eauto using closed_Qual_monotone. apply closed_Qual_qqplus; eauto. 1,2: eapply closed_Qual_monotone; eauto.
             ** apply has_type_filter in H. apply Qqplus_bound.
                apply has_type_closed in H29. intuition. apply closed_Qual_qor_fresh in H35.
                eapply openq_subqual_trans'2. apply H15. all: eauto. eapply Subq_trans; eauto.
             ** apply senv_saturated_qqplus; eauto. eapply senv_saturated_openq. apply senv_saturated_qqplus.
                eapply weaken_store_senv_saturated. eapply has_type_senv_saturated; eauto. Qcrush. eauto.
                eapply weaken_store_senv_saturated; eauto.
                apply closed_qual_qqplus. 1,4 : eapply closed_qual_monotone; eauto. eauto.
                eapply weaken_store_senv_saturated; eauto.
                eapply weaken_store_senv_saturated. eapply H8.
                eapply closed_Qual_open2; eauto. eauto.
          -- (* d2 not dependent on f *)
             inversion H16. subst.
             apply (Preserve Σ' ∅ φ'); auto. rewrite qqplus_qbot_right_neutral.
             replace (d2 <~ᵈ df; d1) with (d2 <~ᵈ df ⋓ d'; d1).
             eapply t_tapp_fresh with (T1:=T1).
             erewrite <- @qqcap_fresh_l' with (Σ':=Σ'); eauto.
             unfold q_trans,q_trans_senv,q_trans_tenv in *. simpl in *.
             rewrite q_trans''_extend_closed_id with (E:=Σ) (q:=d1); auto. rewrite q_trans''_fuel_max with (q:=d1).
             rewrite q_trans''_extend_closed_id with (E:=Σ) (q:=df); auto. rewrite q_trans''_fuel_max with (q:=df).
             eapply weaken_store; eauto.
             apply closed_qenv_empty. apply [].
             all: auto.
             1,2: Qcrush.
             eapply closed_ty_monotone; eauto.
             eapply closed_Qual_monotone; eauto.
             eauto using Subq_trans.
             eapply weaken_store_senv_saturated; eauto.
             eauto using Subq_trans.
             apply Qor_bound; auto. apply has_type_closed in H29. intuition.
             eapply @Subq_trans with (d2:=q_trans [] Σ' d1). Qcrush. unfold q_trans,q_trans_tenv,q_trans_senv.
             simpl. erewrite q_trans''_extend_closed_id; eauto. rewrite q_trans''_fuel_max; auto.
             rewrite qenv_saturated_trans''_id. eapply Subq_trans.
             eapply H2. Qcrush. unfold senv_saturated in H4. eapply qenv_saturated_iff; eauto.
             Qcrush. eapply weaken_store_senv_saturated; eauto 2 using closed_Qual_open2.
             eapply openq_subqual_0_false; auto.
        * (* df not fresh *) rewrite not_fresh_qqplus in H29; auto. apply (Preserve Σ' ∅ φ'); auto.
          rewrite qqplus_qbot_right_neutral.
          eapply t_tapp_fresh with (T1:=T1).
          unfold q_trans,q_trans_senv,q_trans_tenv in *. simpl in *.
          rewrite q_trans''_extend_closed_id with (E:=Σ) (q:=d1); auto. rewrite q_trans''_fuel_max with (q:=d1).
          rewrite q_trans''_extend_closed_id with (E:=Σ) (q:=df); auto. rewrite q_trans''_fuel_max with (q:=df).
          eapply weaken_store; eauto. all: auto.
          apply closed_qenv_empty. apply [].
          1,2: Qcrush.
          eapply closed_ty_monotone; eauto.
          eapply closed_Qual_monotone; eauto.
          eauto using Subq_trans.
          eapply weaken_store_senv_saturated; eauto.
          eauto using Subq_trans.
          apply Qor_bound; auto. apply has_type_closed in H29. intuition.
          eapply @Subq_trans with (d2:=q_trans [] Σ' d1). Qcrush. unfold q_trans,q_trans_tenv,q_trans_senv. simpl.
          erewrite q_trans''_extend_closed_id; eauto. rewrite q_trans''_fuel_max; auto.
          rewrite qenv_saturated_trans''_id. eapply Subq_trans.
          eapply H2. Qcrush. unfold senv_saturated in H4. eapply qenv_saturated_iff; eauto.
          Qcrush. eapply weaken_store_senv_saturated; eauto 2 using closed_Qual_open2.
   - (* tvar *)  subst. inversion H.

   - (* tapp *) right. subst. intuition.
     apply has_type_closed in H as HH. intuition. apply has_type_closed in H0 as HH0. intuition.
     (* t1 *) specialize (H8 (TFun d1 d2 T1 T2) t1). intuition.

     (* t2 *) specialize (H11 T1 t2). intuition.
     + (* contraction *)
       (* turn has_type to vtp *)
       apply has_type_vtp in H as VH; intuition.
       pose (VHH := VH). inversion VH. subst.
       specialize (has_type_filter H0) as Hflt0.
       apply has_type_vtp in H0 as VH0; intuition.
       exists (open_tm (tabs t) t2 t). exists σ. intuition.
       * constructor. intuition.
       * apply (Preserve Σ ∅ φ); auto.  rewrite qqplus_qbot_right_neutral.
         apply qstp_closed in H30 as H30'; intuition.
         change (length []) with 0 in *. subst.
         pose (VH' := H28). eapply t_abs with (φ:=df1) in VH'; eauto. apply has_type_vtp in VH'; auto.
         assert (HT' : has_type [(bind_tm, false, T1, d1) ; (bind_tm, true, TFun d0 d3 T0 T3, df1)] (df1 ⊔ $!0 ⊔ $!1) Σ (open_tm' ([]:tenv) t) (open_ty' ([]:tenv) T3) (openq' ([]:tenv) d3)). {
           eapply narrowing. eapply H28. intuition. auto. apply stp_qstp_inv in H29. eapply qstp_empty; eauto. auto.
         }
         eapply @substitution1 with ( vx:= t2) in HT' as HT''; eauto; intuition.
         unfold open_tm' in HT''. unfold open_ty' in HT''. unfold openq' in HT''. simpl in HT''. inversion H26; subst. inversion H27. subst.
         unfold open_ty in HT''. unfold openq in HT''.
         erewrite <- open_subst2_tm in HT''; eauto.
         erewrite <- open_subst2_ty in HT''; eauto.
         erewrite <- open_subst2_qual in HT''; eauto.
         fold (open_tm (tabs t) t2 t) in HT''. fold (openq df1 d1 d3) in HT''. fold (open_ty (TFun d0 d3 T0 T3) df1 T1 d1 T3) in HT''.
         apply @weaken_flt with (φ':= φ) in HT''; auto; intuition.
         eapply t_sub; eauto.
         pose (Hsub:=H31). eapply @substitution_stp1 with (df:=df1) in Hsub; eauto.
         simpl in Hsub. unfold openq' in Hsub. unfold openq in Hsub. unfold open_ty' in Hsub. unfold open_ty in Hsub. simpl in Hsub.
         erewrite <- open_subst2_ty in Hsub; eauto. erewrite <- open_subst2_ty in Hsub; eauto.
         erewrite <- open_subst2_qual in Hsub; eauto. erewrite <- open_subst2_qual in Hsub; eauto.
         unfold open_ty. unfold openq.
         replace ([[0 ~> TUnit ~ ∅ ]]ᵀ T2) with ([[0 ~> TFun d0 d3 T0 T3 ~ df1 ]]ᵀ T2); auto. (* since not_free 0 T2 *)
         eapply s_trans; eauto. apply stp_refl; auto. apply closed_ty_open2; auto.
         constructor. eapply openq_mono; eauto. apply qstp_empty in H30. auto. apply openq_closed; auto.
         eapply has_type_closed in HT''. intuition. eapply closed_Qual_qor_fresh in H22.
         eapply openq_subqual; eauto. apply has_type_filter in H. eauto.
         eapply senv_saturated_openq; eauto. eapply has_type_senv_saturated; eauto.
         apply Qor_bound; auto. apply has_type_filter in H.
         apply qstp_empty in H30. assert (df1 ⊑↑ φ ⊔ {♦}). eapply Subq_trans; eauto.
         eapply Subqual_non_fresh; eauto. eapply Subqual_non_fresh; eauto.
     + (* right congruence *)
       apply has_type_vtp in H as VH; intuition. apply vtp_canonical_form_lam in VH as HH; intuition.
       pose (HH12 := H10). unfold CtxOK in HH12. specialize (H11 σ). intuition.
       destruct H23 as [t2' [σ' HH9]]. exists (tapp t1 t2'). exists σ'. intuition. constructor; intuition.
       (* d1 is not fresh, so we don't observe the growth *)
       destruct H23. apply (Preserve Σ' ∅ φ'); intuition.
       rewrite not_fresh_qqplus in H30; auto. rewrite qqplus_qbot_right_neutral.
       eapply t_app with (T1:=T1); eauto. eapply weaken_flt. eapply weaken_store. eapply H.
       eauto. apply closed_qenv_empty. apply [].
       eapply wf_senv_closed_qenv_qn; eauto. eauto.
       eapply has_type_closed in H30. intuition. eapply Subq_trans; eauto.
       inversion H13. subst. eapply weaken_store_senv_saturated; eauto 2 using closed_Qual_open2.
     + (* left congruence *)
       apply has_type_closed in H0 as Hcl. intuition.
       specialize (H8 σ H10). destruct H8 as [t1' [σ' HH7]]. exists (tapp t1' t2). exists σ'. intuition. apply step_c_app_l. intuition.
       destruct H23. ndestruct (qbvs d2 0).
       * (* d2 is dependent on f, so the growth in df might be observable  *)
         inversion H13. subst. apply (Preserve Σ' d' φ'); auto.
         -- eapply disjointq_scale; eauto. eapply openq_subqual_0; eauto. (* this is the sole reason why need to distinguish whether d2 is dependent on f or not *)
         -- destruct (♦∈? df) eqn:Hfresh.
            ** erewrite @openq_duplicate_eq_l with (f:=0) (l:=‖Σ'‖). 3,4 : eapply closed_qual_monotone; eauto. 2,3 : eauto.
               eapply t_sub with (T1 := (T2 <~ᵀ TUnit ~ ∅; T1 ~ d1))(d1 := (openq (df ⋓ d') d1 d2)).
               --- eapply t_app with (T1:=T1) (df:=(df ⋓ d')); eauto.
                   eapply weaken_flt. eapply weaken_store. eauto. eauto.
                   apply closed_qenv_empty; apply []. eapply wf_senv_closed_qenv_qn; eauto. eauto.
                   eapply has_type_closed in H30. intuition. eapply Subq_trans; eauto.
                   eapply weaken_store_senv_saturated; eauto 2 using closed_Qual_open2.
               --- apply stp_refl. simpl. eapply closed_ty_monotone; eauto.
                   constructor; auto. apply closed_qual_qqplus; auto.
                   apply openq_closed. 2 : apply closed_qual_qqplus.
                   1,2,4 : eapply closed_qual_monotone; eauto; lia. all: eapply disjointq_closed; eauto.
               --- apply has_type_filter in H0. apply has_type_filter in H. apply Qqplus_bound.
                   eapply has_type_closed in H30. intuition. eapply closed_Qual_qor_fresh in H32.
                   eapply openq_subqual_trans'. eapply H5. all: eauto.
                   eapply Subqual_non_fresh; eauto. Qcrush.
               --- apply senv_saturated_qqplus; eauto. eapply senv_saturated_openq.
                   apply senv_saturated_qqplus; eauto.
                   eapply weaken_store_senv_saturated; eauto.
                   eapply has_type_senv_saturated; eauto.
                   apply closed_Qual_qqplus; eapply closed_Qual_monotone; eauto.
                   eapply weaken_store_senv_saturated; eauto. eapply has_type_senv_saturated; eauto.
                   eapply closed_Qual_monotone; eauto.
                   eapply weaken_store_senv_saturated. eauto. eapply closed_Qual_open2; eauto. eauto.
            ** rewrite not_fresh_qqplus in H30; auto. apply t_sub with (T1:=(T2 <~ᵀ TUnit ~ ∅; T1 ~ d1)) (d1:=d2 <~ᵈ df; d1).
               --- eapply t_app with (T1:=T1); eauto. eapply weaken_flt. eapply weaken_store. eapply H0. eauto.
                   apply closed_qenv_empty; apply []. eapply wf_senv_closed_qenv_qn; eauto. eauto.
                   eapply has_type_closed in H30. intuition.
                   eapply Subq_trans; eauto. eapply weaken_store_senv_saturated; eauto 2 using closed_Qual_open2.
               --- apply stp_refl. simpl. eapply closed_ty_monotone; eauto.
                   constructor. auto. apply closed_qual_qqplus; auto.
                   apply openq_closed; try solve [eapply closed_qual_monotone; eauto]. eauto.
               --- apply has_type_filter in H0. apply has_type_filter in H. apply Qqplus_bound.
                   eapply has_type_closed in H30. intuition. eapply closed_Qual_qor_fresh in H32.
                   eapply openq_subqual_trans. eapply H5. all: eauto.
                   eapply Subqual_non_fresh; eauto. Qcrush.
               --- apply senv_saturated_qqplus; eauto. eapply weaken_store_senv_saturated; eauto. eapply senv_saturated_openq.
                   eapply has_type_senv_saturated; eauto. eauto.
                   eapply has_type_senv_saturated; eauto. apply has_type_closed in H0. intuition. eauto.
       * (* d2 is not dependent on f, so we don't observe the growth in df *)
         inversion H13. subst. apply (Preserve Σ' ∅ φ'); auto. rewrite qqplus_qbot_right_neutral.
         replace (d2 <~ᵈ df; d1) with (d2 <~ᵈ df ⋓ d'; d1). (* since f doesn't occur in d2 *)
         eapply t_app with (T1:=T1); eauto. eapply weaken_flt.
         eapply weaken_store. apply H0. eauto. apply closed_qenv_empty; apply []. eapply wf_senv_closed_qenv_qn; eauto. eauto.
         eapply has_type_closed in H30. intuition.
         eauto using Subq_trans. eapply weaken_store_senv_saturated; eauto 2 using closed_Qual_open2. apply openq_subqual_0_false; auto.
   - (* t_app_fresh *) right. subst. intuition.
     apply has_type_closed in H as HH. intuition. apply has_type_closed in H0 as HH0. intuition.
     (* t1 *) specialize (H9 (TFun (q_trans [] Σ df ⋒ q_trans [] Σ d1) d2 T1 T2) t1). intuition.
     (* t2 *) specialize (H12 T1 t2). intuition.
     + (* contraction *)
       (* turn has_type to vtp *)
       apply has_type_vtp in H as VH; intuition.
       pose (VHH := VH). inversion VH. subst.
       specialize (has_type_filter H0) as Hflt0.
       apply has_type_vtp in H0 as VH0; intuition.
       exists (open_tm (tabs t) t2 t). exists σ. intuition.
       * constructor. intuition.
       * apply (Preserve Σ ∅ φ); auto. rewrite qqplus_qbot_right_neutral.
         apply qstp_closed in H31 as H37'; intuition.
         change (length []) with 0 in *. subst.
         pose (VH' := H29). eapply t_abs with (φ:=df1) in VH'; eauto. apply has_type_vtp in VH'; auto.
         (* remove potential freshness flag from the argument, in order to apply substitution lemma *)
         apply vtp_non_fresh in VH0.
         remember (false,(qfvs d1),(qbvs d1),(qlocs d1)) as d1''.
         remember (false,(qfvs df),(qbvs df),(qlocs df)) as df''.
         assert (Hd1'' : d1'' ⊑↑ d1). { subst. Qcrush. }
         assert (Hdf'' : df'' ⊑↑ df). { subst. Qcrush. }
         assert (Hdf1 : df1 ⊑↑ df). { apply qstp_empty in H31. Qcrush. }
         assert (Hd1''fr : ♦∉ d1''). { subst. auto. }
         assert (Hdf''fr : ♦∉ df''). { subst. auto. }
         assert (Hqand: (q_trans [] Σ df'' ⋒ q_trans [] Σ d1'') ⊑↑ (q_trans [] Σ df ⋒ q_trans [] Σ d1)). {
           apply Subq_qor. apply Subq_qand_split; auto. all: apply q_trans_subq; eauto.
         }
         assert (HT' : has_type [(bind_tm, false, T1, q_trans [] Σ df'' ⋒ q_trans [] Σ d1''); (bind_tm, true, TFun d0 d3 T0 T3, df1)] (df1 ⊔ $!0 ⊔ $!1) Σ (open_tm' ([]:tenv) t) (open_ty' ([]:tenv) T3) (openq' ([]:tenv) d3)). {
           eapply narrowing. eapply H29. intuition. apply @s_trans with (T2:=T1) (d2:=q_trans [] Σ df ⋒ q_trans [] Σ d1); auto.
           apply stp_refl; auto. constructor; auto. apply closed_Qual_qor; auto. apply closed_Qual_qand; auto.
           1,2: apply closed_Qual_q_trans''_monotone; auto; apply wf_senv_closed_qenv; auto.
           apply stp_qstp_inv in H30. apply qstp_empty in H30. eapply Subq_trans; eauto. auto.
         }
         eapply @substitution2 with (vf:=tabs t) ( vx:= t2)  in HT' as HT''; intuition.
         unfold open_tm' in HT''. unfold open_ty' in HT''. unfold openq' in HT''. simpl in HT''. inversion H27; inversion H28; subst.
         unfold open_ty in HT''. unfold openq in HT''.
         erewrite <- open_subst2_tm in HT''; eauto.
         erewrite <- open_subst2_ty in HT''; eauto.
         erewrite <- open_subst2_qual in HT''; eauto.
         fold (open_tm (tabs t) t2 t) in HT''. fold (openq df1 (false,(qfvs d1),(qbvs d1),(qlocs d1)) d3) in HT''.
         apply @weaken_flt with (φ':=φ) in HT''; auto; intuition.
         eapply t_sub; eauto. rename H32 into Hsub.
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
            constructor; auto. eapply openq_mono; eauto.
            (* apply qstp_empty in H36. auto. *)
            all : unfold open_ty; rewrite not_free_prop1; auto. all : rewrite not_free_prop1; auto.
         ++ (* d1 non-fresh *)
            assert (Hd1 : (false,(qfvs d1),(qbvs d1),(qlocs d1))= d1). { apply Q_lift_eq. clear - Hfresh. Qcrush; eauto. }
            rewrite Hd1 in *. replace (T2 <~ᵀ TUnit ~ ∅; T1 ~ d1) with (T2 <~ᵀ (TFun d0 d3 T0 T3) ~ df1; T1 ~ d1). (* since no dependence *)
            eapply s_trans; eauto. apply stp_refl; auto. apply closed_ty_open2; auto. constructor; auto.
            eapply openq_mono; eauto.
            (* apply qstp_empty in H36. auto. *)
            unfold open_ty. f_equal. auto.
         }
         eapply has_type_filter in H as dfFil.
         eapply openq_subqual; eauto using closed_Qual_qor.
         eapply senv_saturated_openq; eauto.
         eapply has_type_senv_saturated; eauto.
         eapply has_type_filter in H as dfFil.
         assert (Hbdf1: df1 ⊑↑ φ ⊔ {♦}). eapply Subq_trans; eauto.
         assert (Hbd1: d1 ⊑↑ φ ⊔ {♦}). Qcrush.
         qual_destruct φ. qual_destruct df1. qual_destruct d1.
         unfold_q. unfold_Q. apply Is_true_eq_false in H38; subst.
         unfold_N. destruct Hbdf1 as [? [? [? ?]]]. destruct Hbd1 as [? [? [? ?]]].
         repeat split; auto; intros ? Hpp; rewrite N_lift_or in Hpp; unfold N_lift in *;
           destruct Hpp; try rewrite <- N_lift_n_or_empty_right; intuition.
         qual_destruct df1. subst. qual_destruct df. simpl in *. Qcrush.
         assert (stp [] Σ (TFun d0 d3 T0 T3) df1 (TFun d0 d3 T0 T3) df). { apply stp_refl; auto. } subst.
         apply vtp_non_fresh. eapply vtp_widening; eauto.
         all: subst; eauto.
     + (* right congruence *)
       inversion H14. subst.
       apply has_type_vtp in H as VH; intuition.
       apply vtp_canonical_form_lam in VH as HH; intuition.
       specialize (H12 σ). intuition.
       destruct H20 as [t2' [σ' HH22]]. exists (tapp t1 t2'). exists σ'. intuition. constructor; intuition.
       destruct H20. destruct (♦∈? d1) eqn:Hfresh.
       * (* d1 fresh *)
         inversion H14. subst. ndestruct (qbvs d2 1).
         -- (* d2 dependent on x *) apply (Preserve Σ' d' φ'); auto.
            eapply disjointq_scale; eauto. eapply openq_subqual_1; eauto.
            replace (T2 <~ᵀ TUnit ~ ∅; T1 ~ d1) with (T2 <~ᵀ TUnit ~ ∅; T1 ~ (d1 ⋓ d')). (* T2 not dependent on x *)
            rewrite openq_duplicate_eq_r; auto. apply t_sub with (T1 := (T2 <~ᵀ TUnit ~ ∅; T1 ~ (d1 ⋓ d'))) (d1 := (openq df (d1 ⋓ d') d2)).
            ** eapply t_app_fresh with (T1 := T1) (df:=df); eauto.
               replace (q_trans [] Σ' df ⋒ q_trans [] Σ' (d1 ⋓ d')) with (q_trans [] Σ' df ⋒ q_trans [] Σ' d1).
               eapply weaken_flt. unfold q_trans,q_trans_senv,q_trans_tenv in *. simpl in *.
               erewrite q_trans''_extend_closed_id with (q:=df); eauto.
               erewrite q_trans''_extend_closed_id with (q:=d1); eauto.
               rewrite q_trans''_fuel_max with (q:=df); auto.
               rewrite q_trans''_fuel_max with (q:=d1); auto.
               eapply weaken_store. eapply H. eauto.
               apply closed_qenv_empty. apply []. all : auto. 1,2: Qcrush.
               eapply has_type_closed in H27. intuition.
               { inversion H26; subst; simpl; destruct (♦∈? d1); auto.
                 ++ rewrite qor_empty_right; auto.
                 ++ repeat rewrite <- q_trans_or_dist. repeat rewrite qand_qor_dist_l. unfold q_trans, q_trans_tenv. simpl. rewrite q_trans_senv_locs. rewrite qand_qor_dist_l.
                    replace (q_trans_senv ((T, q) :: Σ) df ⊓ &! (‖ Σ ‖)) with (∅). rewrite qor_empty_right.
                    assert (q_trans_senv ((T, q) :: Σ) df ⊓ q_trans_senv Σ q ⊑↑ (q_trans_senv ((T, q) :: Σ) df ⊓ q_trans_senv ((T, q) :: Σ) d1)).
                    { apply Subq_qand_split; auto. eapply @Subq_trans with (d2:=q_trans_senv ((T, q) :: Σ) q).
                      unfold q_trans_senv. erewrite <- q_trans''_fuel_max with (E:=Σ).
                      eapply q_trans''_extend_subq; eauto. simpl. lia.
                      unfold q_trans_senv. apply q_trans''_subq; auto. }
                    assert (q_trans_senv ((T, q) :: Σ) df ⊓ q_trans_senv ((T, q) :: Σ) q ⊑↑ (q_trans_senv ((T, q) :: Σ) df ⊓ q_trans_senv ((T, q) :: Σ) d1)).
                    { apply Subq_qand_split; auto. eapply q_trans''_extend_subq; eauto. }
                    apply Q_lift_eq. Qcrush.
                    assert (closed_Qual 0 0 (‖ Σ ‖) (q_trans_senv ((T, q) :: Σ) df)↑).
                    { apply closed_Qual_q_trans''_monotone; auto. apply closed_qenv_extend; auto. }
                    erewrite closed_qand_locs_empty; eauto.
               }
               eauto using Subq_trans. apply Qor_bound; auto. apply has_type_closed in H27. intuition.
               eapply @Subq_trans with (d2:=q_trans [] Σ' df). Qcrush.
               unfold q_trans,q_trans_tenv,q_trans_senv. simpl. erewrite q_trans''_extend_closed_id; eauto.
               rewrite q_trans''_fuel_max; auto.
               eapply vtp_saturated in VH as VHSat. inversion VHSat. eapply has_type_filter in H as HF.
               rewrite qenv_saturated_trans''_id. eapply Subq_trans.
               eapply HF. Qcrush. unfold senv_saturated in H37. eapply qenv_saturated_iff; eauto.
               eapply closed_Qual_monotone; eauto.
               eapply weaken_store_senv_saturated; eauto 2 using closed_Qual_open2.
            ** apply has_type_closed in H27. intuition.
               apply stp_refl. unfold open_ty. eapply closed_ty_open2; eauto. eapply closed_ty_monotone; eauto.
               constructor; auto. apply closed_Qual_qqplus; auto.
               eapply openq_closed; try solve [eapply closed_qual_monotone; eauto]. eauto.
           **  apply has_type_filter in H0. apply has_type_filter in H. apply Qqplus_bound.
               apply has_type_closed in H27. intuition. eapply closed_Qual_qor_fresh in H33.
               eapply openq_subqual_trans''. apply H13. all: eauto. Qcrush.
           **  apply senv_saturated_qqplus; eauto. eapply senv_saturated_openq.
               1, 5 : eapply weaken_store_senv_saturated; eauto 2. 1,4 : eapply has_type_senv_saturated; eauto.
               3 : apply closed_qual_qqplus. 2,3 : eapply closed_qual_monotone; eauto. apply closed_Qual_open2; eauto. eauto.
           ** unfold open_ty. apply not_free_prop2. rewrite not_free_prop1; auto.
         -- (* d2 not dependent on x *) apply (Preserve Σ' ∅ φ'); auto. rewrite qqplus_qbot_right_neutral. intuition.
            replace (d2 <~ᵈ df; d1) with (d2 <~ᵈ df; (d1 ⋓ d')).
            replace (T2 <~ᵀ TUnit ~ ∅; T1 ~ d1) with (T2 <~ᵀ TUnit ~ ∅; T1 ~ (d1 ⋓ d')). (* T2 not dependent on x *)
            eapply t_app_fresh with (T1:=T1); eauto.
            erewrite <- @qqcap_fresh_r' with (Σ':=Σ'); eauto.
            eapply weaken_flt. eapply weaken_store; eauto.
            unfold q_trans,q_trans_senv,q_trans_tenv in *. simpl in *.
            rewrite q_trans''_extend_closed_id with (E:=Σ) (q:=d1); auto. rewrite q_trans''_fuel_max with (q:=d1).
            rewrite q_trans''_extend_closed_id with (E:=Σ) (q:=df); auto. rewrite q_trans''_fuel_max with (q:=df).
            eauto. eauto. Qcrush. eauto. Qcrush. apply closed_qenv_empty. apply []. eauto.
            eapply has_type_closed in H27. intuition. eauto using Subq_trans.
            apply Qor_bound; auto. apply has_type_closed in H27. intuition.
            eapply @Subq_trans with (d2:=q_trans [] Σ' df). Qcrush.
            unfold q_trans,q_trans_tenv,q_trans_senv. simpl. erewrite q_trans''_extend_closed_id; eauto.
            rewrite q_trans''_fuel_max; auto.
            eapply vtp_saturated in VH as VHSat. inversion VHSat. eapply has_type_filter in H as HF.
            rewrite qenv_saturated_trans''_id. eapply Subq_trans. eapply HF.
            Qcrush. unfold senv_saturated in H37. eapply qenv_saturated_iff; eauto.
            Qcrush. eapply weaken_store_senv_saturated; eauto 2 using closed_Qual_open2.
            unfold open_ty. repeat rewrite not_free_prop1; auto. eapply openq_subqual_1_false; eauto.
       * (* d1 not fresh *) rewrite not_fresh_qqplus in H27; auto. apply (Preserve Σ' ∅ φ'); auto.
         rewrite qqplus_qbot_right_neutral.
         eapply t_app_fresh with (T1:=T1); eauto. eapply weaken_flt. eapply weaken_store; eauto.
         unfold q_trans,q_trans_senv,q_trans_tenv in *. simpl in *.
         rewrite q_trans''_extend_closed_id with (E:=Σ) (q:=d1); auto. rewrite q_trans''_fuel_max with (q:=d1).
         rewrite q_trans''_extend_closed_id with (E:=Σ) (q:=df); auto. rewrite q_trans''_fuel_max with (q:=df).
         eauto. eauto. Qcrush. eauto. Qcrush. apply closed_qenv_empty. apply []. eauto.
         eapply has_type_closed in H27. intuition.
         eauto using Subq_trans. apply Qor_bound; auto. apply has_type_closed in H27. intuition.
         eapply @Subq_trans with (d2:=q_trans [] Σ' df). Qcrush.
         unfold q_trans,q_trans_tenv,q_trans_senv. simpl. erewrite q_trans''_extend_closed_id; eauto.
         rewrite q_trans''_fuel_max; auto.
         eapply vtp_saturated in VH as VHSat. inversion VHSat. eapply has_type_filter in H as HF.
         rewrite qenv_saturated_trans''_id. eapply Subq_trans.
         eapply HF. Qcrush. unfold senv_saturated in H36. eapply qenv_saturated_iff; eauto.
         Qcrush. eapply weaken_store_senv_saturated; eauto 2 using closed_Qual_open2.
     + (* left congruence *)
       inversion H14. subst. apply has_type_closed in H0 as Hcl. intuition.
       specialize (H9 σ H11). destruct H9 as [t1' [σ' HH1]]. exists (tapp t1' t2). exists σ'. intuition. apply step_c_app_l. intuition.
       destruct H24. destruct (♦∈? df) eqn:Hfresh.
       * (* df fresh *)
         ndestruct (qbvs d2 0).
         -- (* d2 dependent on f *) apply (Preserve Σ' d' φ'); auto.
            eapply disjointq_scale; eauto. eapply openq_subqual_0; eauto.
            erewrite @openq_duplicate_eq_l with (l:=‖Σ'‖) (f:=0); auto. 2,3 : eapply closed_qual_monotone; eauto. 2: eauto.
            apply t_sub with (T1 := (T2 <~ᵀ TUnit ~ ∅; T1 ~ d1)) (d1 := (openq (df ⋓ d') d1 d2)).
            ** eapply t_app_fresh with (T1 := T1) ; eauto. erewrite <- @qqcap_fresh_l' with (Σ':=Σ'); eauto.
               unfold q_trans,q_trans_senv,q_trans_tenv in *. simpl in *.
               rewrite q_trans''_extend_closed_id with (E:=Σ) (q:=d1); auto. rewrite q_trans''_fuel_max with (q:=d1).
               rewrite q_trans''_extend_closed_id with (E:=Σ) (q:=df); auto. rewrite q_trans''_fuel_max with (q:=df).
               eapply weaken_flt. eapply weaken_store; eauto.
               apply closed_qenv_empty. apply []. eauto. eapply has_type_closed in H35. intuition. eauto.
               Qcrush. eauto. Qcrush.
               eapply weaken_flt. eapply weaken_store; eauto.
               apply closed_qenv_empty. apply []. eauto. eapply has_type_closed in H35. intuition.
               eauto using Subq_trans. apply Qor_bound; auto. apply has_type_closed in H35. intuition.
               eapply @Subq_trans with (d2:=q_trans [] Σ' d1). Qcrush.
               unfold q_trans,q_trans_tenv,q_trans_senv. simpl. erewrite q_trans''_extend_closed_id; eauto.
               rewrite q_trans''_fuel_max; auto. eapply has_type_filter in H0 as HF.
               rewrite qenv_saturated_trans''_id. eapply Subq_trans.
               eapply HF. Qcrush. eapply has_type_senv_saturated in H0 as HSat.
               unfold senv_saturated in HSat. eapply qenv_saturated_iff; eauto.
               Qcrush. eapply weaken_store_senv_saturated; eauto 2 using closed_Qual_open2.
            ** apply has_type_closed in H35. intuition.
               apply stp_refl. simpl. eapply closed_ty_monotone; eauto.
               constructor; auto. apply closed_Qual_qqplus; auto.
               apply openQ_closed. eauto using closed_Qual_monotone. apply closed_Qual_qqplus; eauto.
               1,2: eapply closed_Qual_monotone; eauto.
            ** apply has_type_filter in H0. apply has_type_filter in H. apply Qqplus_bound.
               eapply openq_subqual; eauto 2 using closed_Qual_qor.
               eapply has_type_closed in H35. intuition. Qcrush.
               apply Qqplus_bound. eapply Subq_trans; eauto. Qcrush.
               eapply Subq_trans; eauto. eapply Subq_trans; eauto. Qcrush.
            ** apply senv_saturated_qqplus; eauto. eapply senv_saturated_openq. apply senv_saturated_qqplus.
               1,4,6 : eapply weaken_store_senv_saturated; eauto 2. 1,2 : eapply has_type_senv_saturated; eauto. apply closed_Qual_open2; eauto. eauto.
               apply closed_qual_qqplus. 1,3 : eapply closed_qual_monotone; eauto. eauto.
         -- (* d2 not dependent on f *) apply (Preserve Σ' ∅ φ'); auto. rewrite qqplus_qbot_right_neutral.
            replace (d2 <~ᵈ df; d1) with (d2 <~ᵈ df ⋓ d'; d1).
            eapply t_app_fresh with (T1:=T1); eauto.
            erewrite <- @qqcap_fresh_l' with (Σ':=Σ'); eauto.
            unfold q_trans,q_trans_senv,q_trans_tenv in *. simpl in *.
            rewrite q_trans''_extend_closed_id with (E:=Σ) (q:=d1); auto. rewrite q_trans''_fuel_max with (q:=d1).
            rewrite q_trans''_extend_closed_id with (E:=Σ) (q:=df); auto. rewrite q_trans''_fuel_max with (q:=df).
            eapply weaken_flt. eapply weaken_store; eauto.
            apply closed_qenv_empty. apply []. eauto.
            eapply has_type_closed in H35. intuition. eauto. Qcrush. eauto. Qcrush.
            eapply weaken_flt. eapply weaken_store. eauto. eauto. eapply closed_qenv_empty. apply []. eauto.
            eauto. eapply has_type_closed in H35. intuition. eauto using Subq_trans.
            apply Qor_bound; auto. apply has_type_closed in H35. intuition.
            eapply @Subq_trans with (d2:=q_trans [] Σ' d1). Qcrush. unfold q_trans,q_trans_tenv,q_trans_senv.
            simpl. erewrite q_trans''_extend_closed_id; eauto. rewrite q_trans''_fuel_max; auto.
            eapply has_type_filter in H0 as HF. rewrite qenv_saturated_trans''_id. eapply Subq_trans.
            eapply HF. Qcrush. eapply has_type_senv_saturated in H0 as HSat.
            unfold senv_saturated in HSat. eapply qenv_saturated_iff; eauto.
            Qcrush. eapply weaken_store_senv_saturated; eauto 2 using closed_Qual_open2. eapply openq_subqual_0_false; auto.
        * (* df not fresh *) rewrite not_fresh_qqplus in H35; auto. apply (Preserve Σ' ∅ φ'); auto.
          rewrite qqplus_qbot_right_neutral.
          eapply t_app_fresh with (T1:=T1); eauto.
          unfold q_trans,q_trans_senv,q_trans_tenv in *. simpl in *.
          rewrite q_trans''_extend_closed_id with (E:=Σ) (q:=d1); auto. rewrite q_trans''_fuel_max with (q:=d1).
          rewrite q_trans''_extend_closed_id with (E:=Σ) (q:=df); auto. rewrite q_trans''_fuel_max with (q:=df).
          eapply weaken_flt. eapply weaken_store; eauto. all: auto.
          apply closed_qenv_empty. apply []. eapply has_type_closed in H35. intuition. Qcrush. Qcrush.
          eapply weaken_flt. eapply weaken_store; eauto.
          apply closed_qenv_empty. apply []. eauto. eapply has_type_closed in H35. intuition.
          eauto using Subq_trans. apply Qor_bound; auto. apply has_type_closed in H35. intuition.
          eapply @Subq_trans with (d2:=q_trans [] Σ' d1). Qcrush.
          unfold q_trans,q_trans_tenv,q_trans_senv. simpl. erewrite q_trans''_extend_closed_id; eauto.
          rewrite q_trans''_fuel_max; auto.
          eapply has_type_filter in H0 as HF. rewrite qenv_saturated_trans''_id. eapply Subq_trans.
          eapply HF. Qcrush. eapply has_type_senv_saturated in H0 as HSat.
          unfold senv_saturated in HSat. eapply qenv_saturated_iff; eauto.
          Qcrush. eapply weaken_store_senv_saturated; eauto 2 using closed_Qual_open2.
   - (*tref*) subst. intuition. specialize (has_type_closed H) as HH. intuition. specialize (H7 T t). intuition.
     + (*contraction*) right. intros.
       exists (tloc (‖σ‖)). exists ((Some t) :: σ). intuition.
       econstructor; eauto. inversion H10. destruct H13.
       eapply has_type_filter in H as Hfl.
       assert ({♦} ⊑↑ d1 -> False). intros. Qcrush.
       assert (d1 ⊑↑ φ). eapply Subqual_non_fresh; eauto.
       apply (Preserve ((T,d1) :: Σ) (d1 ⊔ &!‖σ‖) (φ ⊔ &!‖σ‖)); auto.
       eapply CtxOK_weaken'; eauto.  rewrite H13.
       eapply disj_loc; eauto. Qcrush. eapply has_type_senv_saturated; eauto.
       inversion H14. rewrite qqplus_fresh; auto. rewrite qor_assoc. rewrite <- @qor_assoc with (q1:={♦}). rewrite qor_idem.
       apply t_sub with (T1:=TRef d1 T) (d1:=(d1 ⊔ &!‖σ‖)).
       apply t_loc; auto. rewrite H13. Qcrush. rewrite H13.
       apply indexr_head. simpl. eapply closed_ty_monotone; eauto.
       eapply closed_qual_monotone; eauto. eapply weaken_store_senv_saturated; eauto. eapply has_type_senv_saturated; eauto.
       Qcrush. apply stp_refl; auto. constructor; auto. simpl. eapply closed_ty_monotone; eauto.
       eapply closed_qual_monotone; eauto. constructor. clear. Qcrush.
       apply closed_Qual_qor. apply closed_Qual_qor; auto. simpl.
       eapply closed_Qual_monotone; eauto. simpl. rewrite H13. clear. Qcrush.
       rewrite H13. rewrite <- qor_assoc. Qcrush.
       rewrite <- qor_assoc. apply saturated_senv_qor; auto.
       eapply wf_senv_saturated_qplus. apply wf_senv_cons; eauto.
       rewrite H13. rewrite indexr_head. auto.
       eapply has_type_senv_saturated; eauto 2. eapply weaken_store; eauto.
       apply closed_qenv_empty. apply [].
    + (*congruence*) right. intros. specialize (H7 σ H10). destruct H7 as [t' [σ' HH10]].
      exists (tref t'). exists σ'. intuition. econstructor; eauto.
      destruct H12. apply (Preserve Σ' ∅ φ'); intuition. rewrite qqplus_qbot_right_neutral.
      rewrite not_fresh_qqplus in H18; auto. constructor; auto. apply has_type_closed in H18. intuition.
  - (*tderef*) subst. intuition. specialize (has_type_closed H) as HH. intuition. specialize (H8 (TRef d1 T0) t). intuition.
    + (* contraction *) right. intros. pose (HV := H). apply has_type_vtp in HV; intuition.
      specialize (vtp_canonical_form_loc HV) as Hcan. intuition. destruct H13 as [l HH10]. subst.
      pose (HHV := HV). inversion HHV. subst.  pose (HH3 := H11). inversion HH3. intuition.
      pose (HH14 := H21). apply indexr_var_some' in HH14.
      rewrite <- H15 in HH14. apply indexr_var_some in HH14.
      destruct HH14 as [v HHH14].
      specialize (vtp_store_loc_defined HH3 HV) as Hval. destruct Hval.
      exists x. exists σ. intuition. apply step_deref; intuition.
      apply (Preserve Σ ∅ φ); intuition. rewrite qqplus_qbot_right_neutral.
      specialize (H28 l x T q1). apply t_sub with (T1 := T)(d1:= q1); auto. intuition.
      assert (l ∈ₗ qdom Σ). { unfold qmem. unfold qdom. simpl. unfold N_lift.
                              apply indexr_var_some' in H21. unfold n_dom.  apply Nat.ltb_lt in H21. auto. }
      eapply stp_qual_irrelevance; eauto. eapply Subq_trans; eauto.
    + (*congruence *) right. intros. specialize (H8 σ H11).
      destruct H8 as [t' [σ' HH8]]. exists (tderef t'). exists σ'. intuition. constructor; auto.
      destruct H13. apply (Preserve Σ' ∅ φ'); intuition. rewrite qqplus_qbot_right_neutral. eapply t_deref; eauto.
      eapply Subq_trans; eauto.
      eapply weaken_store_senv_saturated; eauto.

  - (*tassign*) subst. intuition. rename H into Ht1. rename H0 into Ht2. intuition.
      apply has_type_closed in Ht1 as Ht1C. intuition.
      apply has_type_closed in Ht2 as Ht2C. intuition.
      specialize (H5 (TRef d1 T) t1). intuition.
      specialize (H8 T t2). intuition.
      + (* contraction *)
        right. intros.
        pose (Ht1' := Ht1). eapply has_type_vtp in Ht1'; eauto.
        pose (Hloc := Ht1'). apply vtp_canonical_form_loc in Hloc; auto.
        inversion Ht1'. destruct Hloc. subst.
        pose (Ht2' := Ht2). apply has_type_vtp in Ht2'; auto.
        exists tunit. exists (update σ x (Some t2)). inversion H31. subst.
        inversion H13. subst. specialize (indexr_var_some' H22) as HH22. intuition.
        econstructor; eauto. rewrite H29; auto. auto. apply (Preserve Σ ∅ φ); auto.
        eapply CtxOK_update; eauto. rewrite H29; auto. Qcrush. apply t_sub with (T1:=T) (d1:=d1); auto.
        eapply stp_qual_irrelevance; eauto.
        eapply has_type_filter in Ht2.
        eapply qstp_empty in H32. assert (q1 ⊑↑ d1 ⊔ {♦}). Qcrush.
        assert (d1 ⊔ {♦} ⊑↑ φ ⊔ {♦}). Qcrush. eapply Subq_trans; eauto.
      + (* right congruence *)
        right. intros. specialize (H8 σ H13). destruct H8 as [t' [σ' H4']].
        exists (tassign t1 t'). exists σ'. intuition. econstructor; eauto.
        pose (HV := Ht1). apply has_type_vtp in HV; intuition. inversion HV; subst.
        destruct H15. apply (Preserve Σ' ∅ φ'); eauto. rewrite not_fresh_qqplus in H34; auto. simpl.
        eapply t_assign; eauto. eapply weaken_flt. eapply weaken_store; eauto.
        apply closed_qenv_empty. apply []. auto. eapply has_type_closed in H34. Qcrush.
      + (* left congruence *)
        right. intros. specialize (H5 σ H13). destruct H5 as [t' [σ' H12']].
        exists (tassign t' t2). exists σ'. intuition. econstructor; eauto.
        destruct H15. apply (Preserve Σ' ∅ φ'); eauto. simpl.
        eapply t_assign; eauto. eapply weaken_flt. eapply weaken_store; eauto.
        apply closed_qenv_empty. apply []. auto. eapply has_type_closed in H21. Qcrush.

  - (*t_sub*) subst. intuition. specialize (stp_closed H0) as H00. intuition.
    specialize (H8 T1 t). intuition. right.
    intros. specialize (H8 σ H11). destruct H8 as [t' [σ' HH8]]. exists t'. exists σ'. intuition.
    destruct H13. apply (Preserve Σ' d' φ'); intuition. eapply disjointq_scale; eauto. apply stp_qstp_inv in H0.
    apply qstp_empty in H0. auto. eapply t_sub; eauto. apply stp_scale_qqplus.
    eapply weaken_stp_store_ext; eauto. eapply disjointq_closed; eauto.
    apply Qqplus_bound. eapply Subq_trans; eauto. eapply @Subq_trans with (d2:=φ'); eauto.
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

Lemma progress : forall {Σ t T d φ},
    has_type [] φ Σ t T d -> wf_senv Σ ->
    value t \/ forall {σ}, CtxOK [] φ Σ σ -> exists t' σ', step t σ t' σ'.
Proof.
  intros Σ t T d φ HT Hwf.
  specialize (type_safety HT). intuition. right. intros σ HCtxOK.
  specialize (H σ). intuition. destruct H0 as [t' [σ' [Hstep  HPreserve]]].
  exists t'. exists σ'. intuition.
Qed.

Lemma preservation : forall {Σ t T d φ},
    has_type [] φ Σ t T d -> wf_senv Σ ->
    forall{σ}, CtxOK [] φ Σ σ ->
    forall {t' σ'}, step t σ t' σ' ->
    preserve [] Σ φ t' T d σ'.
Proof.
  intros Σ t T d φ HT Hwf σ  HCtxOK t' σ' HStep.  specialize (type_safety HT). intuition.
  - inversion HStep; subst; inversion H.
  - specialize (H σ HCtxOK). destruct H as [t'' [σ'' [HStep2 HPreserve]]].
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
  specialize (preservation HT1 Hwf HOK Hstep1) as P1. destruct P1 as [Σ' d1 φ1 Hext1 Hpp Hdp Hwf' HOK' Hdisj1 HT1'].
  assert (HT2': has_type [] φ1 Σ' t2 T2 q2). {
    eapply weaken_flt. eapply weaken_store. all: eauto. eapply closed_qenv_empty. apply [].
    eapply closed_Qual_sub. apply closed_Qual_qdom.
    clear - HOK'. unfold CtxOK in *. Qcrush.
  }
  assert ({♦} ⊑↑ φ1) as Hfr. { eapply Subq_trans; eauto. }
  specialize (preservation HT2' Hwf' HOK' Hstep2) as P2. destruct P2 as [Σ'' d2 φ2 Hext2 Hpp' Hdp' Hwf'' HOK'' Hdisj2 HT2''].
  assert (HT1'': has_type [] (qdom Σ') Σ' t1' T1 (q1 ⋓ d1)). eapply weaken_flt. 1-3: eauto. unfold CtxOK in HOK'. Qcrush.
  assert (HT2''': has_type [] (qdom Σ'') Σ'' t2' T2 (q2 ⋓ d2)). eapply weaken_flt. 1-3: eauto. unfold CtxOK in HOK''. Qcrush.
  apply (Separate Σ' Σ'' (q1 ⋓ d1) (q2 ⋓ d2) Hext1 Hext2 HT1'' HT2''').
  (* now we just need to show that the disjointness is preserved. this is intuitively true from the disjointness
     of the heap effects d1 and d2. *)
  erewrite <- @qqcap_fresh_r; eauto. erewrite <- qqcap_fresh_l; eauto.
  apply has_type_closed in HT1. intuition. eauto.
  apply has_type_closed in HT2. intuition. eauto.
  apply closed_qual_qqplus. apply has_type_closed in HT1 as HC. intuition.
  eapply closed_qual_monotone; eauto. eapply disjointq_closed; eauto.
  apply has_type_closed in HT2. intuition. eapply closed_qual_monotone; eauto.
  (* finally, the qualifiers are completely saturated, i.e., the results indeed have fully disjoint object graphs  *)
  all : apply senv_saturated_qqplus; eauto.
  apply has_type_senv_saturated in HT1 as HS; auto. eapply weaken_store_senv_saturated; eauto.
  eapply has_type_closed in HT1. intuition. Qcrush.
  eapply weaken_store_senv_saturated; eauto.
  apply has_type_senv_saturated in HT2 as HS; auto. eapply weaken_store_senv_saturated; eauto.
  eapply has_type_closed in HT2. intuition. Qcrush.
Qed.

Fixpoint sfilter (σ: store) (φ: qual) : store :=
  match σ with
  | a :: σ' => (match a with
                | Some v => if ‖ σ' ‖ ∈?ₗ φ then Some v else None
                | _ => None
                end) :: (sfilter σ' φ)
  | nil => nil
  end.

Lemma sfilter_preserves_length: forall σ φ,
  ‖ sfilter σ φ ‖ = ‖ σ ‖.
Proof. intros. induction σ; simpl; auto. Qed.

Lemma sfilter_preserves_ctxok: forall σ φ Σ,
  CtxOK [] φ Σ σ -> CtxOK [] φ Σ (sfilter σ φ).
Proof.
  intros. unfold CtxOK in *.
  destruct H, H0, H1.
  split. 2: split. 3: split. 4: intros.
  - assert (qdom' (sfilter σ φ) ⊑↑ qdom' σ). 2: Qcrush. clear.
    induction σ. auto. Qcrush. specialize (H3 x). unfold N_lift in *. unfold n_dom' in *.
    simpl in *. rewrite sfilter_preserves_length in *.
    apply andb_true_iff in H. destruct H. rewrite H. simpl.
    bdestruct (x =? ‖ σ ‖). destruct a; intuition.
    assert (x < ‖ σ ‖). apply Nat.ltb_lt in H. lia. apply Nat.ltb_lt in H6.
    rewrite H6 in *. rewrite H0 in *. simpl in *. intuition.
  - rewrite <- H0. apply sfilter_preserves_length.
  - clear - H1. Qcrush. unfold N_lift in *. clear - H2 H3. specialize (H3 x H2).
    induction σ. auto. unfold n_dom' in *. simpl in *. rewrite sfilter_preserves_length in *.
    apply andb_true_iff in H3. destruct H3. rewrite H in *. simpl in *.
    bdestruct (x =? ‖ σ ‖). subst. unfold qlocs. rewrite H2. destruct a; intuition.
    assert (x < ‖ σ ‖). apply Nat.ltb_lt in H. lia. apply Nat.ltb_lt in H3. rewrite H3 in *. simpl in *.
    rewrite H0 in *. intuition.
  - eapply H2; eauto. clear - H5. induction σ. auto. simpl in *. rewrite sfilter_preserves_length in *.
    bdestruct (l =? ‖ σ ‖). subst. inversion H5. destruct a; auto. destruct (qlocs φ (‖ σ ‖)); inversion H0; intuition.
    intuition.
Qed.

Corollary parallel_progress_and_preservation: forall Σ φ1 φ2 t1 t2 T1 T2 q1 q2 σ,
  has_type [] φ1 Σ t1 T1 q1 -> has_type [] φ2 Σ t2 T2 q2 -> ~ value t1 -> ~ value t2 ->
  CtxOK [] φ1 Σ σ -> CtxOK [] φ2 Σ σ -> wf_senv Σ -> exists σ1 σ2 t1' t2' Σ1 Σ2 φ1' φ2' p1 p2,
  step t1 (sfilter σ φ1) t1' σ1 -> has_type [] φ1' Σ1 t1' T1 p1 -> Σ1 ⊇ Σ ->
  step t1 (sfilter σ φ2) t2' σ2 -> has_type [] φ2' Σ2 t2' T2 p2 -> Σ2 ⊇ Σ.
Proof.
  intros Σ φ1 φ2 t1 t2 T1 T2 q1 q2 σ Hht1 Hht2 Hnv1 Hnv2 Hctx1 Hctx2 Hwf.
  apply progress in Hht1 as ?; auto. destruct H; intuition.
  apply sfilter_preserves_ctxok in Hctx1. specialize (H _ Hctx1). destruct H as [ t1' [ σ1 ]].
  apply progress in Hht2 as ?; auto. destruct H0; intuition.
  apply sfilter_preserves_ctxok in Hctx2. specialize (H0 _ Hctx2). destruct H0 as [ t2' [ σ2 ]].
  exists σ1, σ2, t1', t2'.
  eapply preservation in Hht1; eauto. eapply preservation in Hht2; eauto.
  destruct Hht1 as [Σ1 d1 φ1']. destruct Hht2 as [Σ2 d2 φ2'].
  exists Σ1, Σ2, φ1', φ2', (q1 ⋓ d1), (q2 ⋓ d2). intuition.
Qed.

Fixpoint sextend (σ: store) (l: nat): store :=
  match l with
  | S n => None :: (sextend σ n)
  | 0 => σ
  end.

Lemma sextend_preserves_domain: forall l σ,
  ‖ sextend σ l ‖ = (‖ σ ‖ + l) /\ qdom' (sextend σ l) = qdom' σ.
Proof.
  intros. induction l. simpl. intuition.
  destruct IHl. simpl. rewrite H. simpl. rewrite <- H0. intuition.
  unfold qdom'. Qcrush. unfold n_dom'. simpl. bdestruct (x =? ‖ sextend σ l ‖).
  subst. rewrite Nat.ltb_irrefl. intuition. bdestruct (x <? S (‖ sextend σ l ‖)).
  replace (x <? ‖ sextend σ l ‖) with true. reflexivity. symmetry. apply Nat.ltb_lt. lia.
  replace (x <? ‖ sextend σ l ‖) with false. reflexivity. symmetry. apply Nat.ltb_nlt. lia.
Qed.

Lemma sextend_preserves_ctxok: forall Σ Σ1 σ φ,
  Σ1 ⊇ Σ -> CtxOK [] φ Σ σ -> wf_senv Σ -> CtxOK [] φ Σ1 (sextend σ (‖ Σ1 ‖ - ‖ Σ ‖)).
Proof.
  intros Σ Σ1 σ φ HE HC HWf. unfold CtxOK in *. destruct HC, H0, H1. unfold extends in *.
  destruct HE as [Σd]. subst. rewrite app_length. replace (‖ Σd ‖ + ‖ Σ ‖ - ‖ Σ ‖) with (‖ Σd ‖). 2: lia.
  specialize (sextend_preserves_domain (‖ Σd ‖) σ). intros. destruct H3. rewrite H4.
  split. 2: split. 3: split. 4: intros.
  assert (‖ Σ ‖ <= ‖ Σd ++ Σ ‖). rewrite app_length. lia.
  assert (qdom Σ ⊑↑ qdom (Σd ++ Σ)). Qcrush. Qcrush. lia. auto.
  assert (l ∈ₗ qdom Σ). Qcrush. unfold qmem, N_lift, qlocs, qdom, n_dom, snd in H8. apply Nat.ltb_lt in H8.
  rewrite indexr_skips in H6. 2: auto. rewrite <- H0 in H8. replace (indexr l (sextend σ (‖ Σd ‖))) with (indexr l σ) in H7.
  2: { clear - H8. induction (‖ Σd ‖). auto. simpl.
    bdestruct (l =? ‖ sextend σ n ‖). specialize (sextend_preserves_domain n σ). intro. lia. auto. }
  specialize (H2 l v T q). intuition. eapply weaken_store. eauto. exists Σd. auto.
  eapply closed_qenv_empty. apply []. eapply wf_senv_closed_qenv_qn; eauto.
Qed.

Definition srefine (σ: store) (φ: qual) (l: nat) :=
  sfilter (sextend σ l) φ.

Lemma Qand_bound : forall {q1 q2 φ1 φ2},
    q1 ⊑↑ φ1 ⊔ {♦} -> q2 ⊑↑ φ2 ⊔ {♦} -> q1 ⋒ q2 ⊑↑ φ1 ⋒ φ2.
Proof.
  intros.
  qual_destruct q1. qual_destruct q2. qual_destruct φ1. qual_destruct φ2.
  rewrite set_union_fresh in H. rewrite set_union_fresh in H0. Qcrush.
Qed.

Corollary parallel_progress_and_preservation': forall Σ φ1 φ2 t1 t2 T1 T2 q1 q2 σ,
  has_type [] φ1 Σ t1 T1 q1 -> has_type [] φ2 Σ t2 T2 q2 -> ~ value t1 -> ~ value t2 ->
  CtxOK [] φ1 Σ σ -> CtxOK [] φ2 Σ σ -> wf_senv Σ -> φ1 ⋒ φ2 ⊑↑ {♦} ->
  exists l1 l2 σ1' σ2' t1' t2' Σ1 Σ2 φ1' φ2' p1 p2,
  step t1 (srefine σ φ1 l1) t1' σ1' -> CtxOK [] φ1' Σ1 σ1' -> has_type [] φ1' Σ1 t1' T1 p1 -> Σ1 ⊇ Σ ->
  step t2 (srefine σ φ2 l2) t2' σ2' -> CtxOK [] φ2' Σ2 σ2' -> has_type [] φ2' Σ2 t2' T2 p2 -> Σ2 ⊇ Σ -> p1 ⋒ p2 ⊑↑ {♦}.
Proof.
  intros Σ φ1 φ2 t1 t2 T1 T2 q1 q2 σ Hht1 Hht2 Hnv1 Hnv2 Hctx1 Hctx2 Hwf Hoverlap.
  unfold srefine.
  apply sfilter_preserves_ctxok in Hctx1 as Hctx1'. apply progress in Hht1 as Hstep1; auto.
  destruct Hstep1 as [| Hstep1]; intuition.
  specialize (Hstep1 _ Hctx1'). destruct Hstep1 as [ t1' [ σ1' Hstep1 ]]. eapply preservation in Hht1 as Hpres1; eauto.
  destruct Hpres1 as [Σ1 d1 φ1' HΣ1 Hφ1 Hd1 Hwf1 Hok1 Hdisj1 H1']. eapply sextend_preserves_ctxok in Hctx2 as Hctx2'; eauto.
  apply sfilter_preserves_ctxok in Hctx2'. eapply weaken_store in Hht2 as Hht2'; eauto.
  apply progress in Hht2' as Hstep2; auto. destruct Hstep2 as [| Hstep2]; intuition. specialize (Hstep2 _ Hctx2').
  destruct Hstep2 as [ t2' [ σ2' Hstep2 ]]. eapply preservation in Hht2' as Hpres2; eauto.
  destruct Hpres2 as [Σ2 d2 φ2' HΣ2 Hφ2 Hd2 Hwf2 Hok2 Hdisj2 H2'']. remember ((sfilter σ φ1)) as σ1. remember ((sfilter (sextend σ (‖ Σ1 ‖ - ‖ Σ ‖)) φ2)) as σ2.
  exists 0, (‖ Σ1 ‖ - ‖ Σ ‖), σ1', σ2', t1', t2', Σ1, Σ2, φ1', φ2', (q1 ⋓ d1), (q2 ⋓ d2). intuition.
  erewrite <- @qqcap_fresh_r; eauto. erewrite <- qqcap_fresh_l; eauto.
  apply has_type_filter in Hht1. apply has_type_filter in Hht2. eapply Subq_trans. 2: eauto.
  eapply Qand_bound; eauto.
  apply has_type_closed in Hht1. intuition. eauto. apply has_type_closed in Hht2. intuition.
  apply closed_qual_qqplus. apply has_type_closed in Hht1. intuition.
  eapply closed_qual_monotone; eauto. eapply disjointq_closed; eauto.
  apply has_type_closed in Hht2. intuition. eapply closed_qual_monotone; eauto.
  eapply closed_qenv_empty. apply [].
Qed.

