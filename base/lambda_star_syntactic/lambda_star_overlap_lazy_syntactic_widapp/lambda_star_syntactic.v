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
Require Import lambda_star.
Require Import lambda_star_addition.


Require Import syntactic_qualifiers.
Import QualNotations.
Local Open Scope syntactic_qualifiers.

(* ============= Transition Functions ========= *)

Fixpoint syntactic_to_set (q : qual) : qualifiers.qual := 
  match q with 
  | qempty        => qualifiers.qset {}N {}N {}N 
  | qvar (varF x) => qualifiers.just_fv x 
  | qvar (varB x) => qualifiers.just_bv x
  | qloc l        => qualifiers.just_loc l
  | qor q1 q2     => qualifiers.qlub (syntactic_to_set q1) (syntactic_to_set q2)
  end.

Import NatSet.F.
Definition set_to_syntactic (d : qualifiers.qual) : qual := 
  match d with 
  | qualifiers.qset fvs bvs locs => qor
    (qor 
      (*fvs*) (fold (fun fv ls => qor (varF fv) (ls)) fvs qempty)
      (*bvs*) (fold (fun bv ls => qor (varB bv) (ls)) bvs qempty)
    )
    (*loc*) (fold (fun fv ls => qor (qloc fv) (ls)) locs qempty)
  end.

Example syntactic_qual_ex1 := qor (varF 1) (
  qor (varF 2) (qor (varB 1) (
    qor (varB 3) (qloc 1)
  ))
).
Eval compute in (syntactic_to_set syntactic_qual_ex1).

Example set_qual_ex1 := qualifiers.qlub (qualifiers.just_fv 1) (qualifiers.qlub (qualifiers.just_fv 2) (qualifiers.qlub (qualifiers.just_bv 1) (qualifiers.qlub (qualifiers.just_bv 3) (qualifiers.just_loc 1)))).
Eval compute in set_qual_ex1.
Example set_qual_ex2 := qset {}N {}N {}N.
Eval compute in (set_to_syntactic set_qual_ex2).


Fixpoint ty_syntactic_to_set (T : ty) : lambda_star.ty :=
  match T with
  | TUnit   => lambda_star.TUnit
  | TFun q1 q2 T1 T2  => lambda_star.TFun (syntactic_to_set q1) (syntactic_to_set q2) (ty_syntactic_to_set T1) (ty_syntactic_to_set T2)
  | TRef T  => lambda_star.TRef (ty_syntactic_to_set T)
  end.

Definition ctx_transfer (tq : ty * qual) : (lambda_star.ty * qualifiers.qual) := 
  match tq with 
  | (T, q) => (ty_syntactic_to_set T, syntactic_to_set q)
  end.

Definition ctx_syntactic_to_set (Γ : syntactic_qualifiers.tenv) : lambda_star.tenv :=
  map ctx_transfer Γ.

Definition store_syntactic_to_set (Σ : syntactic_qualifiers.senv) : lambda_star.senv :=
  map (fun (T : syntactic_qualifiers.ty) => (ty_syntactic_to_set T)) Σ.

(* ======== End of Transition Function ======== *)


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
    closed_tm (S b) f l tm ->
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

Inductive closed_ty : nat(*B*) -> nat(*F*) -> nat(*Loc*) -> ty -> Prop :=
| cl_TUnit : forall b f l,
    closed_ty b f l TUnit
| cl_TRef : forall b f l T,
    closed_ty 0 0 0 T ->
    closed_ty b f l (TRef T)
| cl_TFun : forall b f l d1 d2 T1 T2,
    closed_qual b f l d1 ->
    closed_qual (S b) f l d2 ->
    closed_ty b f l T1 ->
    closed_ty (S b) f l T2 ->
    closed_ty b f l (TFun d1 d2 T1 T2)
.
#[global] Hint Constructors closed_ty : core.

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
    stp ((T3,d3) :: Γ) Σ (open_ty' Γ T2) (openq' Γ d2) (open_ty' Γ T4) (openq' Γ d4) ->
    stp Γ Σ (TFun d1 d2 T1 T2) d5 (TFun d3 d4 T3 T4) d6
| s_trans : forall Γ Σ T1 d1 T2 d2 T3 d3,
    stp Γ Σ T1 d1 T2 d2 -> stp Γ Σ T2 d2 T3 d3 -> stp Γ Σ T1 d1 T3 d3
.
#[global] Hint Constructors stp : dsub.


(* Specifies that the variable x's qualifier is subsumed by q in context Γ *)
Inductive saturated_var (Γ : tenv) (Σ : senv) (x : id) (q : qual) : Prop :=
| sat_var : forall U q',
    indexr x Γ = Some (U, q') ->
    qstp Γ Σ q' q ->
    closed_qual 0 x (length Σ) q' ->
    saturated_var Γ Σ x q.
Arguments sat_var {Γ Σ x q}.
#[global] Hint Constructors saturated_var : core.

(* Specifies that q is transitively closed w.r.t. Γ, i.e., each variable x in q is a saturated variable in the above sense. *)
Definition saturated (Γ : tenv) (Σ : senv) (q: qual) : Prop := 
  forall x, (varF x) ∈ᵥ q -> saturated_var Γ Σ x q.


Inductive has_type : tenv -> qual -> senv -> tm -> ty -> qual -> Prop :=
| t_base : forall Γ Σ φ,
    closed_qual 0 (length Γ) (length Σ) φ ->
    has_type Γ φ Σ tunit TUnit ∅ (* use ∅ instead of bottom *)

| t_var : forall Γ φ Σ x T d,
    indexr x Γ = Some (T,d) ->
    qstp Γ Σ (just_fv x) φ ->
    (* closed_qual 0 (length Γ) (length Σ) φ -> *)
    closed_ty 0 x (length Σ) T ->
    closed_qual 0 x (length Σ) d ->
    has_type Γ φ Σ (tvar (varF x)) T (just_fv x)

| t_abs: forall Γ φ Σ T1 d1 T2 d2 df t,
    closed_tm 1 (length Γ) (length Σ) t ->
    closed_ty 0 (length Γ) (length Σ) (TFun d1 d2 T1 T2) ->
    (* closed_qual 0 (length Γ) (length Σ) φ -> *)
    qstp Γ Σ df φ ->
    has_type ((T1,d1) :: Γ) (df ⊔ (just_fv (length Γ))) Σ (open_tm' Γ t) (open_ty' Γ T2) (openq' Γ d2) ->
    has_type Γ φ Σ (tabs t) (TFun d1 d2 T1 T2) df

| t_app : forall Γ φ Σ t1 d1 t2 d2 df T1 T2 d1' df',
    (*
    Assumptions: 
    t1 : { T1 | dom } ==> { T2 | q2 } df
    t2 : T1 d1
    d1 <= d1*
    df <= df*
    d1* /\ df* = dom'
    dom' <= dom
    d1* /\ df* <= dom
    -------------------------
    For substitution lemma, we want to show that the invariants hold after substitution (i.e. assumptions work again)
    s(t1) : { s(T1) | s(dom) } ==> { s(T2) | s(q2) } s(df)
    s(t2) : s(T1) s(d1)
    s(d1) <= s(d1* )      //subst_qstp
    s(df) <= s(df* )
    s(d1* /\ df* ) <= s(dom)    //by saturation, intersection and substitution is commute
      -> s(d1* ) /\ s(df* ) <= s(dom)
    *)
    forall {ds'}, syntactic_to_set ds' = qualifiers.qglb (syntactic_to_set df') (syntactic_to_set d1') ->
    (* qstp Γ Σ ds' ds ->     *)
    (* contra-variant, by saturation, we know we can commute intersection and substitution. so after substitution, the result still saturated *)
    has_type Γ φ Σ t1 (TFun ds' d2 T1 T2) df ->
    has_type Γ φ Σ t2 T1 d1 ->
    closed_ty 0 (length Γ) (length Σ) T2 ->
    qstp Γ Σ (openq ∅ d2) φ ->
    qstp Γ Σ d1 d1' ->
    qstp Γ Σ df df' ->
    (* regulating still in the bound *)
    qstp Γ Σ d1' φ  ->
    qstp Γ Σ df' φ  ->
    (* saturation in set level *)
    lambda_star.saturated (ctx_syntactic_to_set Γ) (store_syntactic_to_set Σ) (syntactic_to_set d1') ->
    lambda_star.saturated (ctx_syntactic_to_set Γ) (store_syntactic_to_set Σ) (syntactic_to_set df') ->
    has_type Γ φ Σ (tapp t1 t2) T2 (openq d1 d2)

| t_loc : forall Γ φ Σ l T,
    closed_qual 0 (length Γ) (length Σ) φ ->
    indexr l Σ = Some T ->
    closed_ty 0 0 0 T ->
    qstp Γ Σ (just_loc l) φ ->
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
    qstp Γ Σ d2 φ ->
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
| SArg : forall df dx ds,
    syntactic_to_set ds = qualifiers.qglb (syntactic_to_set df) (syntactic_to_set dx)   ->
    Substq ds dx.
  (* we substitute an argument to a function call, note the difference.*)
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
  closed_tm 1 0 (length Σ) t ->
  closed_qual 0 0 (length Σ) df2 ->
  closed_ty 0 0 (length Σ) (TFun d3 d4 T3 T4) ->  (* sub type *)
  closed_ty 0 0 (length Σ) (TFun d1 d2 T1 T2) ->  (* super type *)
  has_type [(T1,d1)] (df1 ⊔ (just_fv 0)) Σ (open_tm' ([]: tenv) t) (open_ty' ([]: tenv) T2) (openq' ([]: tenv) d2) ->
  stp [] Σ T3 d3 T1 d1 ->
  qstp [] Σ df1 df2 ->
  stp [(T3, d3)] Σ (open_ty' ([]: tenv) T2) (openq' ([] : tenv) d2) (open_ty' ([]: tenv) T4) (openq' ([]: tenv) d4) ->
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
    has_type Γ (ldom Σ') Σ' t' T (qor d d') ->
    preserve Γ Σ t' T d σ'.
Arguments Preserve {Γ Σ t' T d σ'}.

(* deterministic relations (used to recover standard progress & preservation from the type safety theorem. ) *)
Definition relation (X : Type)(Y: Type) := X -> Y -> X ->  Y -> Prop.
Definition deterministic {X : Type}{Y: Type} (R : relation X Y) :=
  forall (x x1 x2 : X) (y y1 y2: Y), R x y x1 y1 -> R x y x2 y2 -> x1 = x2 /\ y1 = y2.

(* The concluding statement of the separation of preservation corollary, i.e., interleaving the execution of two well-typed
   terms with disjoint qualifiers preserves the types and keeps qualifiers disjoint.  *)
Inductive separate (Σ : senv) (t1' : tm) (T1 : ty) (t2' : tm) (T2 : ty) : Prop :=
| Separate : forall Σ' Σ'' q1' q2' s1' s2',
    Σ' ⊇ Σ ->
    Σ'' ⊇ Σ' ->
    has_type [] (ldom Σ') Σ' t1' T1 q1' ->
    has_type [] (ldom Σ'') Σ'' t2' T2 q2' ->
    s1' = syntactic_to_set q1' ->
    s2' = syntactic_to_set q2' ->
    qualifiers.subqual (qualifiers.qglb s1' s2') (qset {}N {}N {}N) ->
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
  induction t0; intros; simpl; eauto.
  destruct v. auto. destruct (Nat.eqb j i); auto.
Qed.

Lemma open_ty_preserves_size: forall T d j, ty_size T = ty_size (open_rec_ty j d T).
  induction T; intros; simpl; eauto.
Qed.

Lemma splice_qual_empty : forall {k}, splice_qual k ∅ = ∅.
  intros. simpl. auto.
Qed.
#[global] Hint Resolve splice_qual_empty : core.

Lemma closed_qual_empty : forall {b f l}, closed_qual b f l ∅.
  intros. constructor; rewrite bound_empty; lia.
Qed.
#[global] Hint Resolve closed_qual_empty : core.

Lemma closed_qual_monotone : forall {f b l d}, closed_qual b f l d -> forall {b' f' l'}, b <= b' -> f <= f' -> l <= l' -> closed_qual b' f' l' d.
Proof.
  intros. induction d; intuition.
  - destruct v; constructor. inversion H; lia. inversion H; lia.
  - constructor. inversion H; subst. lia.
  - inversion H; subst. constructor; intuition.
Qed.

Lemma qstp_closed : forall {Γ Σ d1 d2}, qstp Γ Σ d1 d2 -> closed_qual 0 (length Γ) (length Σ) d1 /\ closed_qual 0 (length Γ) (length Σ) d2.
Proof.
  intros. split.  
  - induction H; subst; try constructor; try auto. 
  - induction H; subst; try constructor; try auto.
Qed.

Lemma qstp_sub_or_inversion : forall {Γ Σ q1 q2 q}, qstp Γ Σ (qor q1 q2) q ->
  qstp Γ Σ q1 q /\ qstp Γ Σ q2 q.
Proof.
  intros. remember (qor q1 q2) as q'. generalize dependent q1. generalize dependent q2. induction H; intros; try discriminate; subst. 
  specialize (IHqstp q0 q4); intuition. 
  specialize (IHqstp q0 q4); intuition.
  inversion Heqq'; subst. intuition.
  specialize (IHqstp1 q0 q4). intuition.  
  all: eapply qstp_trans; eauto.
Qed.

Lemma qstp_loc_inversion : forall {Γ Σ l d}, qstp Γ Σ (just_loc l) d -> l < length Σ.
Proof.
  intros. remember (just_loc l) as q'. generalize dependent l. induction H; intros; try discriminate; unfold just_loc in *; subst; try intuition. inversion Heqq'; subst; intuition. 
Qed.

Lemma qstp_varF_inversion : forall {Γ Σ x d}, qstp Γ Σ $x d -> x < (length Γ).
Proof.
  intros. apply qstp_closed in H. remember ($x) as q'. generalize dependent x. induction H; intros; try discriminate; subst; try intuition. 
  inversion H; assumption.
Qed.

Lemma closed_qual_ldom : forall {Σ : senv}, closed_qual 0 0 (length Σ) (ldom Σ).
  intros. unfold ldom. induction (length Σ).
  - constructor.
  - simpl. constructor. constructor. lia. eapply closed_qual_monotone; eauto. 
Qed.
#[global] Hint Resolve closed_qual_ldom : core.

Lemma closed_qual_cong : forall {Γ Σ b d},
    closed_qual b (length Γ) (length Σ) d -> forall {d'}, eqqual Γ Σ d d' -> closed_qual b (length Γ) (length Σ) d'.
Proof.
  intros. inversion H0; apply qstp_closed in H1; destruct H1. 
  eapply closed_qual_monotone; eauto. lia.
Qed.

Lemma just_fv_closed : forall {x b f l}, x < f <-> closed_qual b f l (just_fv x).
Proof.
  split; intros.
  - unfold just_fv. constructor. assumption.
  - inversion H. subst. assumption.
Qed.


Lemma just_loc_closed : forall {x b f l}, x < l <-> closed_qual b f l (just_loc x).
Proof.
  split; intros.
  - unfold just_loc. constructor; assumption.
  - inversion H. subst. assumption.
Qed.

Lemma qstp_refl : forall {Γ Σ q}, 
    closed_qual 0 (length Γ) (length Σ) q -> 
    qstp Γ Σ q q.
Proof.
  intros. induction q. 
  - constructor; eauto.
  - inversion H. eapply qstp_varF_refl. assumption. lia.   
  - apply qstp_loc_refl. inversion H. assumption.
  - inversion H; subst. apply IHq1 in H5. apply IHq2 in H6. clear IHq1 IHq2. 
    eapply (@qstp_sub_or Γ Σ q1 q2 (qor q1 q2)). 
    eapply qstp_or_l_sub. assumption. inversion H; assumption. 
    eapply qstp_or_r_sub. assumption. inversion H; assumption.
Qed.
#[global] Hint Resolve qstp_refl : core.

Lemma qstp_trans : forall {Γ Σ d1 d2}, qstp Γ Σ d1 d2 -> forall {d3}, qstp Γ Σ d2 d3 -> qstp Γ Σ d1 d3.
Proof.
  intros. eapply qstp_trans; eauto.
Qed.

Lemma closed_qual_sub : forall {Γ Σ b d}, 
  closed_qual b (length Γ) (length Σ) d -> 
  forall {d'}, qstp Γ Σ d' d -> 
  closed_qual b (length Γ) (length Σ) d'.
Proof.
  intros. apply qstp_closed in H0; destruct H0. 
  eapply closed_qual_monotone; eauto. lia.
Qed.

Lemma splice_tenv_length : forall {n Γ}, length (splice_tenv n Γ) = length Γ.
  intros. unfold splice_tenv. rewrite map_length. auto.
Qed.

Lemma closed_tm_monotone : forall {t b l f}, closed_tm b f l t -> forall {b' f' l'}, b <= b' -> f <= f' -> l <= l' -> closed_tm b' f' l' t.
  intros T b f l H. induction H; intuition.
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
  intros. induction d; intuition. 
  - simpl. destruct v. reflexivity. inversion H; subst.  assert (i <> n) by lia. apply Nat.eqb_neq in H1. rewrite H1. reflexivity.
  - simpl. inversion H; subst. apply IHd1 in H6. apply IHd2 in H7. rewrite H6. rewrite H7. reflexivity.
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
  intros. unfold just_fv; simpl. induction d; simpl. 
  - constructor.
  - destruct v.
    + simpl. apply closed_qvar_f. inversion H; assumption.
    + simpl. inversion H; subst. destruct (i =? b) eqn:Eqib.
      constructor. assumption. constructor. apply Nat.eqb_neq in Eqib. lia.   
  - constructor. inversion H. assumption.
  - inversion H; subst. apply IHd1 in H6. apply IHd2 in H7. constructor; assumption.
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
  intros; induction d. 
  - constructor.
  - inversion H; subst. constructor. assumption. inversion H; subst. simpl. 
    destruct (x0 =? b) eqn: Heq. apply (@closed_qual_monotone x 0 l); try assumption; try lia. constructor. apply Nat.eqb_neq in Heq. lia.
  - constructor. inversion H; subst; assumption. 
  - constructor; fold open_qual. apply IHd1; inversion H; assumption. apply IHd2; inversion H; assumption.
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
  unfold just_fv in *. intros. inversion H; subst; simpl.
  - constructor.
  - constructor. lia.
  - destruct (x0 =? b) eqn: Hx0. constructor. lia. constructor. apply Nat.eqb_neq in Hx0. lia.
  - constructor. assumption.
  - constructor; fold open_qual. apply closed_qual_open. apply (@closed_qual_monotone f (S b) l q1); try lia. assumption. lia. apply closed_qual_open. apply (@closed_qual_monotone f (S b) l q2); try lia. assumption. lia.
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
  intros. unfold just_fv in *. induction d; simpl.
  - constructor.
  - inversion H; subst. constructor. lia. destruct (x =? j) eqn:Hx. constructor. lia. constructor. assumption.
  - inversion H; subst. constructor. assumption.
  - inversion H; subst. apply IHd1 in H5. apply IHd2 in H6. constructor; assumption.
Qed.

Lemma closed_ty_open_succ : forall {T b f l}, closed_ty b f l T -> forall {j}, closed_ty b (S f) l (open_rec_ty j (just_fv f) T).
  induction T; intros; simpl; intuition; inversion H; subst; try constructor;
    try solve [eapply IHT1; eauto | eapply IHT2; eauto | eapply IHT; eauto ].
  1,2:eapply closed_qual_open_succ; eauto.
  erewrite closed_ty_open_id; eauto. lia.
Qed.

Lemma open_rec_tm_commute : forall t i j x y, i <> j -> open_rec_tm i (varF x) (open_rec_tm j (varF y) t) = open_rec_tm j (varF y) (open_rec_tm i (varF x) t).
  intros t.
  induction t; intros; simpl; eauto;
    try solve [rewrite IHt1; eauto; rewrite IHt2; eauto | rewrite IHt; eauto].
  destruct v. intuition.
  destruct (Nat.eqb i i0) eqn:Hii0; destruct (Nat.eqb j i0) eqn:Hji0; simpl;
    try rewrite Hii0; try rewrite Hji0; auto.
  apply Nat.eqb_eq in Hii0. apply Nat.eqb_eq in Hji0. subst. contradiction.
Qed.

Lemma open_qual_commute : forall d i j x y, i <> j -> open_qual i (just_fv x) (open_qual j (just_fv y) d) = open_qual j (just_fv y) (open_qual i (just_fv x) d).
Proof.
  unfold just_fv. induction d; intros.
  - reflexivity.
  - destruct v. reflexivity.
    simpl. destruct (i0 =? j) eqn:Hi0_j.
    + assert ((i0 =? i) = false). apply Nat.eqb_neq. apply Nat.eqb_eq in Hi0_j. intuition. rewrite H0. simpl. rewrite Hi0_j. reflexivity.
    + destruct (i0 =? i) eqn:Hi0_i. simpl. rewrite Hi0_i. reflexivity. simpl. rewrite Hi0_i. rewrite Hi0_j. reflexivity.
  - reflexivity.
  - simpl. specialize (IHd1 i j x y H). specialize (IHd2 i j x y H). rewrite IHd1. rewrite IHd2. reflexivity.
Qed.

Lemma open_rec_ty_commute : forall T i j x y,
    i <> j -> open_rec_ty i (just_fv x) (open_rec_ty j (just_fv y) T) = open_rec_ty j (just_fv y) (open_rec_ty i (just_fv x) T).
  induction T; intros; simpl; eauto;
    try solve [erewrite IHT1; eauto; erewrite IHT2; eauto | erewrite IHT; eauto].
  erewrite open_qual_commute; eauto.
  erewrite open_qual_commute with (i:=(S i)); eauto.
  erewrite IHT1; eauto; erewrite IHT2; eauto.
Qed.

Lemma open_rec_tm_commute' : forall t i j x t' f l, i <> j -> closed_tm 0 f l t' -> open_rec_tm i (varF x) (open_rec_tm j t' t) = open_rec_tm j t' (open_rec_tm i (varF x) t).
  intros t.
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
  induction d; intros; auto.
  - destruct v; simpl; auto. bdestruct (i0 =? j); simpl.
    + bdestruct (i0 =? i); simpl. (*wrong assumption*) lia. apply Nat.eqb_eq in H1. rewrite H1. 
      induction d'; simpl; auto.
      * destruct v; auto. inversion H0; lia.
      * inversion H0; subst. rewrite IHd'1. rewrite IHd'2. all: auto.
    + bdestruct (i0 =? i); simpl; auto. apply Nat.eqb_neq in H1. rewrite H1; simpl. auto.
  - simpl. erewrite IHd1; eauto. erewrite IHd2; eauto.
Qed.

Lemma open_rec_ty_commute' : forall T i j x d f l, i <> j -> closed_qual 0 f l d -> open_rec_ty i (just_fv x) (open_rec_ty j d T) = open_rec_ty j d (open_rec_ty i (just_fv x) T).
  induction T; intros; simpl; eauto;
    try solve [erewrite IHT1; eauto; erewrite IHT2; eauto | erewrite IHT; eauto].
  erewrite open_qual_commute'; eauto. erewrite open_qual_commute'; eauto.
  erewrite IHT1; eauto; erewrite IHT2; eauto.
Qed.

Lemma open_rec_tm_commute'' : forall t i j t' t'' f l, i <> j -> closed_tm 0 f l t' -> closed_tm 0 f l t'' -> open_rec_tm i t'' (open_rec_tm j t' t) = open_rec_tm j t' (open_rec_tm i t'' t).
  intros t.
  induction t; intros; simpl; eauto;
    try solve [erewrite IHt1; eauto; erewrite IHt2; eauto | erewrite IHt; eauto].
  - destruct v. intuition.
    destruct (Nat.eqb i i0) eqn:Hii0; destruct (Nat.eqb j i0) eqn:Hji0; simpl;
      try rewrite Hii0; try rewrite Hji0; auto.
    apply Nat.eqb_eq in Hii0. apply Nat.eqb_eq in Hji0. subst. contradiction.
    symmetry. eapply closed_tm_open_id; eauto. lia. eapply closed_tm_open_id; eauto. lia.
Qed.

Lemma open_qual_commute'' : forall d i j d' d'' f l,
    i <> j -> closed_qual 0 f l d' -> closed_qual 0 f l d'' ->
    open_qual i d'' (open_qual j d' d) = open_qual j d' (open_qual i d'' d).
Proof.
  induction d; intros; auto.
  2: { simpl. erewrite IHd1; eauto. erewrite IHd2; eauto. }
  destruct v; simpl; auto.
  bdestruct (i0 =? j); bdestruct (i0 =? i); simpl; auto.
  - (* wrong assumption *) lia.
  - apply Nat.eqb_eq in H2. rewrite H2. 
    induction d'; auto.
    + destruct v; auto. inversion H0; subst; lia.
    + simpl. inversion H0; subst. rewrite IHd'1; auto. rewrite IHd'2; auto.
  - apply Nat.eqb_eq in H3. rewrite H3.
    induction d''; auto.
    + destruct v; auto. inversion H1; subst; lia.
    + simpl. inversion H1; subst. rewrite <- IHd''1; auto. rewrite <- IHd''2; auto.
  - apply Nat.eqb_neq in H2. apply Nat.eqb_neq in H3. rewrite H2. rewrite H3. auto.
Qed.

Lemma open_rec_ty_commute'' : forall T i j d' d'' f l, i <> j -> closed_qual 0 f l d' -> closed_qual 0 f l d'' -> open_rec_ty i d'' (open_rec_ty j d' T) = open_rec_ty j d' (open_rec_ty i d'' T).
  induction T; intros; simpl; eauto;
    try solve [erewrite IHT1; eauto; erewrite IHT2; eauto | erewrite IHT; eauto].
  erewrite open_qual_commute''; eauto.
  erewrite open_qual_commute'' with (i:= (S i)); eauto.
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

Lemma open_qual_id : forall {q k d l},
  closed_qual 0 0 l q ->
  q = [[k ~> d]]ᵈ q.
Proof.
  intros. induction q; intuition.
  - destruct v; simpl. reflexivity. inversion H; intuition.
  - inversion H; subst. intuition. simpl. rewrite H0 at 1. rewrite H1 at 1. reflexivity.
Qed.

Lemma open_qual_just_fv : forall i d x, open_qual i d (just_fv x) = (just_fv x).
  intros. compute. auto.
Qed.

Lemma open_qual_just_loc : forall i d x, open_qual i d (just_loc x) = (just_loc x).
  intros. compute. auto.
Qed.

Lemma open_rec_tm_bv : forall i t, open_rec_tm i t (#i) = t.
  intros. simpl. rewrite <- EqNat.beq_nat_refl_stt. auto.
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
  induction d; intros; intuition; inversion H; subst. 
  - unfold splice_qual. destruct (le_lt_dec f x). lia. reflexivity.
  - simpl. reflexivity.
  - simpl. apply IHd1 in H5. apply IHd2 in H6. rewrite H5; rewrite H6. reflexivity. 
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
  intros. unfold just_fv in *. induction d; intuition. 
  - destruct v.
    + unfold splice_qual. destruct (le_lt_dec n i); simpl. destruct (le_lt_dec n i). reflexivity. lia. destruct (le_lt_dec n i). lia. reflexivity.
    + simpl. destruct (i =? j). simpl. destruct (le_lt_dec n (m+n)). reflexivity. lia. simpl. reflexivity.
  - simpl. rewrite IHd1. rewrite IHd2. reflexivity.
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
  rewrite <- splice_open. auto.
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

Lemma splice_closed : forall {T b n m l}, closed_tm b (n + m) l T -> closed_tm b (S (n + m)) l (splice m T).
  induction T; simpl; intros; inversion H; subst; intuition.
  destruct (le_lt_dec m x) eqn:Heq; intuition.
Qed.

Lemma splice_qual_closed : forall {d b n m l},
    closed_qual b (n + m)     l d ->
    forall {i}, i <= m -> closed_qual b (S (n + m)) l (splice_qual i d).
Proof.
  intros. induction d; subst; intuition; simpl.
  - destruct v; simpl. 
    + inversion H; subst. destruct (le_lt_dec i i0). constructor. lia. constructor. lia.
    + inversion H; subst. constructor. assumption.
  - constructor. inversion H; subst. assumption.
  - inversion H; subst. apply IHd1 in H6. apply IHd2 in H7. constructor; assumption.   
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
Proof.
  intros. induction q; subst; intuition; simpl.
  - destruct v; simpl. 
    + inversion H; subst. destruct (le_lt_dec k i). constructor. lia. constructor. lia.
    + inversion H; subst. constructor. assumption.
  - constructor. inversion H; subst. assumption.
  - inversion H; subst. apply IHq1 in H6. apply IHq2 in H7. constructor; assumption.
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
  intros. unfold just_fv in *. induction d; intuition; simpl.
  - inversion H; subst; simpl.
    + destruct (le_lt_dec n x). lia. reflexivity.
    + destruct (x =? j) eqn:Hx. unfold splice_qual. destruct (le_lt_dec n n). reflexivity. lia. reflexivity.
  - inversion H; subst. apply IHd1 in H5. apply IHd2 in H6. rewrite H5. rewrite H6. reflexivity. 
Qed.

Lemma splice_ty_open_succ : forall {T b n l j}, closed_ty b n l T -> splice_ty n (open_rec_ty j (just_fv n) T) = open_rec_ty j (just_fv (S n)) T.
  induction T; simpl; intros; inversion H; subst; auto;
    try solve [erewrite IHT1; eauto; erewrite IHT2; eauto | erewrite IHT; eauto].
  erewrite splice_qual_open_succ; eauto. erewrite splice_qual_open_succ; eauto.
  erewrite IHT1; eauto. erewrite IHT2; eauto.
  erewrite closed_ty_open_id; eauto. erewrite closed_ty_open_id; eauto.
  erewrite splice_ty_id; eauto. eapply closed_ty_monotone; eauto. all : lia.
Qed.

Lemma splice_qual_open'' : forall {k df d},
    splice_qual k (openq df d) =
    openq (splice_qual k df) (splice_qual k d).
Proof.
  intros. unfold openq. induction d; auto.
  2:{ simpl. rewrite IHd1. rewrite IHd2. auto. }
  destruct v; simpl.
  - destruct (le_lt_dec k i); simpl; auto.
  - destruct i; simpl; auto.
Qed.

Lemma splice_qual_qplus_dist : forall {i k d},
    k <= i -> (splice_qual k d ⊕ S i) = splice_qual k (d ⊕ i).
Proof.
  intros. unfold qplus; unfold qlub; unfold just_fv. simpl. 
  destruct (le_lt_dec k i). reflexivity. induction d; intuition.
Qed.

Lemma splice_qual_qplus_id : forall {i k l d},
    closed_qual 0 i l d -> i < k -> splice_qual k (d ⊕ i) = (d ⊕ i).
Proof.
  intros. unfold qplus; unfold qlub; unfold just_fv. simpl.
  destruct (le_lt_dec k i). induction d; intuition. assert (splice_qual k d = d). rewrite (@splice_qual_id d i k l); try reflexivity. eapply closed_qual_monotone; eauto. lia. lia. rewrite H1. reflexivity.
Qed.

Lemma qplus_closed_qual : forall {d b f l x},
    closed_qual b f l d ->
    forall {f'}, f' >= f -> f' > x -> closed_qual b f' l (d ⊕ x).
Proof.
  intros. unfold qplus; unfold just_fv; unfold qlub. constructor.
  eapply closed_qual_monotone; eauto. constructor. lia.
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
Proof.
  induction n; try lia; destruct T; simpl; intros Hsize Γ Σ Hc d d' Hstp; inversion Hc; subst.
  - (*TUnit*) constructor. auto.
  - (*TFun*) constructor; auto. apply IHn. lia. auto. apply qstp_refl; assumption. 
    apply IHn. unfold open_ty'. unfold open_ty. rewrite <- open_ty_preserves_size. lia. simpl. unfold open_ty'. unfold open_ty. 
    eapply closed_ty_open' with (x:=S (length Γ)); eauto.
    eapply closed_ty_monotone; eauto.
    rewrite <- just_fv_closed. lia.
    apply qstp_refl. unfold openq'. unfold openq. 
    simpl. eapply closed_qual_open. eapply closed_qual_monotone; eauto.
    lia. 
  - (*TRef*) constructor. auto.
    all : apply IHn; try lia; auto.
Qed.

Lemma stp_refl : forall {T Γ Σ}, closed_ty 0 (length Γ) (length Σ) T -> forall {d d'}, qstp Γ Σ d d' -> stp Γ Σ T d T d'.
  intros. eapply stp_refl'; eauto.
Qed.

Lemma stp_qstp_inv : forall {Γ Σ T1 d1 T2 d2}, stp Γ Σ T1 d1 T2 d2 -> qstp Γ Σ d1 d2.
  intros Γ Σ T1 d1 T2 d2 HS. induction HS; intuition.  eapply qstp_trans; eauto.
Qed.

Lemma splice_qual_closed_helper : forall (Γ1 Γ2 : tenv) (Σ: senv) {X q},
  closed_qual 0 (length (Γ1 ++ Γ2)) (length Σ) q ->
  closed_qual 0 (length (splice_tenv (length Γ2) Γ1 ++ X :: Γ2)) 
  (length Σ) (splice_qual (length Γ2) q). 
Proof.
  intros. remember (length (Γ1 ++ Γ2)) as f. induction H; intros; intuition; subst; simpl. 
  - rewrite app_length. rewrite splice_tenv_length. rewrite app_length in H. destruct (le_lt_dec (length Γ2) x).  constructor. simpl. lia. constructor. simpl. lia. 
  - constructor. assumption.
  - constructor. assumption.
  - constructor. intuition. intuition.
Qed. 

Lemma weaken_qstp_gen : forall {Γ1 Γ2 Σ d1 d2},
    qstp (Γ1 ++ Γ2) Σ d1 d2 ->
    forall T', qstp ((splice_tenv (length Γ2) Γ1) ++ T' :: Γ2) Σ (splice_qual (length Γ2) d1) (splice_qual (length Γ2) d2).
Proof.
  intros. remember (Γ1 ++ Γ2) as Γ. generalize dependent Γ1. induction H; intros; intuition.
  - constructor. apply splice_qual_closed_helper. subst. auto.
  - apply qstp_refl. apply splice_qual_closed_helper. subst. constructor. auto.
  - apply qstp_refl. apply splice_qual_closed_helper. subst. constructor. auto.
  - simpl. apply qstp_or_l_sub. apply IHqstp; assumption. apply splice_qual_closed_helper. subst. auto.
  - simpl. apply qstp_or_r_sub. apply IHqstp; assumption. apply splice_qual_closed_helper. subst. auto.
  - simpl. apply qstp_sub_or. apply IHqstp1; assumption. apply IHqstp2; assumption.
  - eapply qstp_trans; eauto.
Qed.

Lemma weaken_qstp_store : forall {Γ Σ d1 d2}, qstp Γ Σ d1 d2 -> forall {Σ'}, qstp Γ (Σ' ++ Σ) d1 d2.
Proof.
  intros. induction H; try intuition. 
  - constructor. eapply closed_qual_monotone; eauto. rewrite app_length. lia.
  - constructor. rewrite app_length. lia.
  - constructor. assumption. eapply closed_qual_monotone; eauto. rewrite app_length. lia.
  - apply qstp_or_r_sub. assumption. eapply closed_qual_monotone; eauto. rewrite app_length. lia.
  - eapply qstp_trans; eauto.
Qed.

Lemma weaken_qstp_store_ext : forall {Γ Σ d1 d2}, qstp Γ Σ d1 d2 -> forall {Σ'}, Σ' ⊇ Σ -> qstp Γ Σ' d1 d2.
Proof.
  intros. unfold extends in H0. destruct H0. subst. apply weaken_qstp_store. auto.
Qed.

Lemma weaken_qstp : forall {Γ Σ d1 d2}, 
  qstp Γ Σ d1 d2 ->
  forall x, qstp (x ++ Γ) Σ d1 d2.
Proof.
  intros. induction H.
  - constructor. eapply closed_qual_monotone; eauto. rewrite app_length. lia.
  - constructor. rewrite app_length. lia.
  - apply qstp_refl. constructor. auto.
  - apply qstp_or_l_sub. auto. eapply closed_qual_monotone; eauto. rewrite app_length. lia.
  - apply qstp_or_r_sub. auto. eapply closed_qual_monotone; eauto. rewrite app_length. lia.
  - constructor; auto.
  - eapply qstp_trans; eauto.
Qed.

Lemma weaken_stp_gen : forall {Γ1 Γ2 Σ T1 d1 T2 d2},  stp (Γ1 ++ Γ2) Σ T1 d1 T2 d2 ->
    forall T', stp ((splice_tenv (length Γ2) Γ1) ++ T' :: Γ2) Σ (splice_ty (length Γ2) T1) (splice_qual (length Γ2) d1) (splice_ty (length Γ2) T2) (splice_qual (length Γ2) d2).
Proof.   
  intros Γ1 Γ2 Σ T1 d1 T2 d2  Hstp T'. remember (Γ1 ++ Γ2)  as Γ. generalize dependent Γ1.  induction Hstp. intros Γ1.
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
    constructor; try fold splice_ty. 1-2: constructor.
    1,2,5,6 : apply splice_qual_closed'. 5-8 : apply splice_ty_closed'.
    1-8: rewrite app_length in *; rewrite splice_tenv_length in *; auto.
    apply weaken_qstp_gen. assumption.
    specialize (IHHstp1 Γ1). intuition.
    specialize (IHHstp2 ((T3, d3) :: Γ1)). intuition.
    rewrite <- splice_ty_open'. rewrite <- splice_ty_open'. rewrite <- splice_qual_open'. rewrite <- splice_qual_open'.
    unfold open_ty' in *. unfold open_ty in *. unfold openq' in *. unfold openq in *.
    rewrite app_length in *. rewrite splice_tenv_length. auto.
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
Proof. intros Σ Γ T1 d1 T2 d2 HSTP. induction HSTP; intros.
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
Proof.
  intros Γ1 U du Γ2 Σ d1 d2 HQ V dv HSTP. remember (Γ1 ++ (U, du) :: Γ2) as Γ.
  induction HQ; subst. 
  - constructor. eapply closed_qual_monotone; eauto. do 2 rewrite app_length. simpl. lia.
  - constructor. rewrite app_length. rewrite app_length in H. simpl in *. assumption.
  - constructor. assumption.
  - constructor. intuition. eapply closed_qual_monotone; eauto. do 2 rewrite app_length. simpl. lia.
  - apply qstp_or_r_sub. intuition. eapply closed_qual_monotone; eauto. do 2 rewrite app_length. simpl. lia.
  - constructor. intuition. intuition.
  - intuition. eapply qstp_trans; eauto.
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
  intros. constructor; auto. 
Qed.

Lemma extends_ldom_helper : forall {T} {Σ : senv} {Γ}, qstp Γ (T::Σ) (ldom Σ) (ldom (T::Σ)).
Proof.
  intros. unfold ldom. unfold dom_l; simpl; fold dom_l.
  apply qstp_or_r_sub. apply qstp_refl. 
  assert (closed_qual 0 0 (length Σ) (ldom Σ)). apply closed_qual_ldom. eapply closed_qual_monotone; eauto. lia. simpl. lia.
  constructor. simpl; auto.
Qed.

Lemma extends_ldom : forall {Σ' Σ : senv} {Γ}, (Σ') ⊇ (Σ) -> qstp Γ Σ' (ldom Σ) (ldom Σ').
Proof.
  intros. inversion H. rewrite H0; clear H0. unfold ldom. induction x; simpl.
  - apply qstp_refl. assert (closed_qual 0 0 (length Σ) (ldom Σ)). apply closed_qual_ldom. eapply closed_qual_monotone; eauto. lia.
  - apply qstp_or_r_sub. replace (a :: x ++ Σ) with ([a] ++ (x ++ Σ)) by auto. apply weaken_qstp_store; auto.
    constructor. simpl. lia.
Qed.

Lemma subqual_plus : forall {Γ Σ d1 d2}, 
  qstp Γ Σ d1 d2 -> 
  forall {x}, x < length Γ ->
  qstp Γ Σ (d1 ⊕ x) (d2 ⊕ x).
Proof.
  intros. unfold qplus. 
  apply qstp_sub_or. 
  - apply qstp_or_l_sub. assumption. constructor. assumption.
  - apply qstp_or_r_sub. apply qstp_varF_refl. assumption. apply qstp_closed in H; destruct H; assumption.
Qed.

Lemma stp_scale_plus : forall {Γ Σ T1 d1 T2 d2}, stp Γ Σ T1 d1 T2 d2 -> forall {x}, x < length Γ -> stp Γ Σ T1 (d1 ⊕ x) T2 (d2 ⊕ x).
Proof.
  intros Γ Σ T1 d1 T2 d2 HSTP. induction HSTP; intros.
  - constructor. apply subqual_plus; assumption.
  - constructor; auto. apply subqual_plus. auto. assumption.
  - constructor; auto. apply subqual_plus. auto. assumption.  
  - econstructor; eauto.
Qed.

Lemma stp_scale_qqplus : forall {Γ Σ T1 d1 T2 d2}, stp Γ Σ T1 d1 T2 d2 -> forall {d}, closed_qual 0 (length Γ) (length Σ) d -> stp Γ Σ T1 (d1 ⋓ d) T2 (d2 ⋓ d).
Proof.
  intros Γ Σ T1 d1 T2 d2 HSTP. pose (H1:= HSTP). apply stp_closed in H1. intuition. induction HSTP; intros. 
  - constructor. apply qstp_sub_or. apply qstp_or_l_sub. auto. 2: apply qstp_or_r_sub. 2: apply qstp_refl. all: auto.
  - constructor; auto. intuition. 
  - constructor; auto. intuition.
  - apply stp_closed in HSTP1. intuition; econstructor; eauto.
Qed.

Lemma stp_shrink_var : forall {Γ Σ T1 d1 T2 d2}, stp Γ Σ T1 d1 T2 d2 -> forall {x}, x < length Γ -> stp Γ Σ T1 (just_fv x) T2 (just_fv x).
Proof.
  intros. induction H.
  - constructor. apply qstp_refl. constructor; auto.
  - constructor; auto. apply qstp_refl. constructor; auto.
  - constructor; auto. apply qstp_refl. constructor; auto.
  - econstructor; eauto. 
Qed.

Lemma saturated_empty : forall {Γ Σ}, saturated Γ Σ ∅.
  intros. unfold saturated. intros.
  simpl in H. contradiction.
Qed.
#[global] Hint Resolve saturated_empty : core.

Lemma saturated_empty_tenv : forall {q Σ}, closed_qual 0 0 (length Σ) q -> saturated [] Σ q.
Proof.
  intros. unfold saturated. intros.
  induction q. 
  - simpl in H0. contradiction. 
  - destruct v. inversion H. lia. inversion H. lia. 
  - inversion H0. 
  - inversion H; subst. inversion H0; subst; intuition. 
    inversion H4. econstructor; eauto. apply qstp_or_l_sub; auto. 
    inversion H4. econstructor; eauto. apply qstp_or_r_sub; auto.
Qed.
#[global] Hint Resolve saturated_empty_tenv : core.

Lemma saturated_cons : forall {Γ Σ q}, saturated Γ Σ q -> forall {T q'}, saturated ((T, q') :: Γ) Σ q.
Proof.
  intros. unfold saturated in *. intros. apply H in H0. inversion H0. subst.
  eapply sat_var with (q' := q'0); eauto. rewrite indexr_skip; eauto. apply indexr_var_some' in H1. lia.
  replace ((T, q') :: Γ) with ([(T, q')] ++ Γ) by auto.
  apply weaken_qstp. auto.
Qed.

Lemma saturated_app : forall {Γ' Γ Σ q}, saturated Γ Σ q -> saturated (Γ' ++ Γ) Σ q.
  induction Γ'; intros; simpl; intuition.
  apply saturated_cons; auto.
Qed.

Lemma qmem_plus_decomp : forall {x0 q x l}, $ (x0) ∈ᵥ q ⊕ x -> closed_qual 0 x l q -> $ (x0) ∈ᵥ q \/ x0 = x.
Proof.
  intros. simpl in *. destruct H. left; auto. right; auto. 
Qed.

Lemma saturated_qplus : forall {Γ Σ x T q}, indexr x Γ = Some (T, q) -> closed_qual 0 x (length Σ) q -> saturated Γ Σ q -> saturated Γ Σ (q ⊕ x).
Proof.
  unfold saturated. intros. specialize (qmem_plus_decomp H2 H0) as Hx. destruct Hx.
  - apply H1 in H3. inversion H3. subst. econstructor; eauto. unfold qplus. apply qstp_or_l_sub. auto. constructor. apply indexr_var_some' in H. auto.
  - subst. econstructor; eauto. apply indexr_var_some' in H. apply qstp_or_l_sub. apply qstp_refl. eapply closed_qual_monotone; eauto. lia. constructor. auto.
Qed.

Lemma saturated_qqplus : forall {Γ Σ q1 q2}, 
  saturated Γ Σ q1 -> 
  saturated Γ Σ q2 -> 
  (*add this constrain because don't know in q1 or q2*)
  closed_qual 0 (length Γ) (length Σ) q1 ->
  closed_qual 0 (length Γ) (length Σ) q2 ->
  saturated Γ Σ (q1 ⋓ q2).
Proof.
  intros. simpl in *. unfold saturated. intros.
  unfold saturated in H. unfold saturated in H0. destruct H3. 
  - apply H in H3. inversion H3. econstructor; eauto. apply qstp_or_l_sub. auto. auto.
  - apply H0 in H3. inversion H3. econstructor; eauto. apply qstp_or_r_sub. auto. auto. 
Qed.

Lemma saturated_just_loc : forall {Γ Σ l}, saturated Γ Σ (just_loc l).
  intros. unfold saturated. intros. simpl in *.
  contradiction.
Qed.
#[global] Hint Resolve saturated_just_loc : core.

Lemma weaken_store_saturated : forall {Γ Σ q}, saturated Γ Σ q -> forall {Σ'}, Σ' ⊇ Σ -> saturated Γ Σ' q.
  intros. unfold saturated in *. intros. specialize (H x H1).
  inversion H. subst. inversion H0. apply (sat_var U q'); auto. rewrite H5. eapply weaken_qstp_store; eauto.
  eapply closed_qual_monotone; eauto. rewrite H5. rewrite app_length. lia.
Qed.

Fixpoint has_type_closed  {Γ φ Σ t T d} (ht : has_type Γ φ Σ t T d) :
  closed_qual 0 (length Γ) (length Σ) φ /\
  closed_tm 0 (length Γ) (length Σ) t /\
  closed_ty 0 (length Γ) (length Σ) T /\
  closed_qual 0 (length Γ) (length Σ) d.
Proof.
  induction ht; intuition; try apply has_type_closed in ht; try apply has_type_closed in ht1;
    try apply has_type_closed in ht2; intuition.
  - apply qstp_closed in H0. intuition.
  - constructor. apply indexr_var_some' in H. assumption.
  - apply indexr_var_some' in H. eapply closed_ty_monotone; eauto. lia. 
  - apply qstp_closed in H0; destruct H0; assumption. 
  - apply qstp_closed in H1; destruct H1; assumption.
  - apply qstp_closed in H1; destruct H1; assumption.
  - unfold openq. eapply qstp_closed in H1; destruct H1. unfold openq in H1; simpl. eapply closed_qual_open'; eauto. inversion H11; assumption.
  - constructor. apply qstp_closed in H2. intuition. inversion H3; auto.
  - apply qstp_closed in H2. destruct H2. auto.
  - inversion H0; subst. eapply closed_ty_monotone; eauto; lia.
  - apply stp_closed in H. intuition. 
  - apply qstp_closed in H0. intuition.
Qed.

Lemma openq_subqual : forall {Γ Σ d1 d2 φ}, 
  qstp Γ Σ d1 φ -> 
  qstp Γ Σ (openq (∅) d2) φ -> 
  qstp Γ Σ (openq d1 d2) φ.
Proof.
  intros. unfold openq in *. induction d2; simpl; auto.
  2: { simpl in H0. apply qstp_sub_or_inversion in H0. destruct H0. constructor; auto. }
  destruct v; auto. simpl in H0. destruct i; simpl in *; auto.
Qed.

Fixpoint has_type_filter {Γ φ Σ t T d} (ht : has_type Γ φ Σ t T d) : 
  qstp Γ Σ d φ.
Proof.
  induction ht; intuition. apply openq_subqual. apply has_type_filter in ht2. auto.
  auto. all: constructor; try apply has_type_closed in ht; intuition. apply has_type_closed in ht1; intuition. 
Qed.

Lemma closed_qual_qmem_fv : forall {b f l q}, closed_qual b f l q -> forall {x}, $x ∈ᵥ q -> x < f.
Proof.
  intros. induction q; simpl in *; intuition.
  destruct v; subst. inversion H; subst; auto. contradiction. 
  all: inversion H; subst; intuition. 
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

Lemma splice_qual_lub_dist : forall {d1 d2 k}, splice_qual k (d1 ⊔ d2) = ((splice_qual k d1) ⊔ (splice_qual k d2)).
  intros. destruct d1; destruct d2; intuition.
Qed.

Lemma splice_qual_mem_lt : forall {x k d1}, x < k -> $x ∈ᵥ splice_qual k d1 -> $x ∈ᵥ d1.
Proof.
  intros. induction d1; simpl in *; auto.
  2:{ intuition. }
  destruct v; simpl in *. destruct (le_lt_dec k i). inversion H0. lia. inversion H0. lia. contradiction.
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
Proof.
  intros. induction d1; try destruct v; simpl in *; auto.
  destruct (le_lt_dec k i). inversion H0. reflexivity. inversion H0. lia.
  destruct H0; intuition.
Qed.

Lemma splice_qual_not_mem : forall {k d1}, $ (k) ∈ᵥ splice_qual k d1 -> False.
Proof.
  intros. induction d1; simpl in H; auto.
  - destruct v. destruct (le_lt_dec k i); inversion H; lia. inversion H; lia.
  - destruct H; intuition.
Qed.

Lemma splice_qual_just_fv_ge : forall {k j}, k <= j -> splice_qual k (just_fv j) = just_fv (S j).
  intros. unfold just_fv. simpl. destruct (le_lt_dec k j); intuition.
Qed.

Lemma splice_qual_just_fv_lt : forall {k j}, k > j -> splice_qual k (just_fv j) = just_fv j.
  intros. unfold just_fv. simpl. destruct (le_lt_dec k j); intuition.
Qed.

Lemma closed_qual_qplus : forall {b f l q x}, closed_qual b f l q -> x < f -> closed_qual b f l (q ⊕ x).
Proof.
  intros. constructor; auto. constructor; auto.
Qed.

Lemma weaken_saturated : forall {Γ1 Γ2 Σ d1},
    saturated (Γ1 ++ Γ2) Σ d1 ->
    let k := (length Γ2) in forall X, saturated ((splice_tenv k Γ1) ++ X :: Γ2) Σ (splice_qual k d1).
Proof.
  intros. unfold saturated. intros. bdestruct (x <? k).
  - specialize (H x). apply splice_qual_mem_lt in H0; auto. intuition. inversion H2.
    rewrite indexr_skips in H; try lia. apply (sat_var U q'); auto.
    rewrite indexr_skips. rewrite indexr_skip; auto. lia. simpl. lia.
    replace q' with (splice_qual k q'). apply weaken_qstp_gen. auto.
    eapply splice_qual_id. eapply closed_qual_monotone; eauto. lia.
  - bdestruct (x =? k).
    + subst. apply splice_qual_not_mem in H0. contradiction.
    + destruct x. lia. specialize (H x). assert (Hx : x >= k). lia.
      assert ($ (x) ∈ᵥ d1). apply (splice_qual_mem_ge Hx H0). intuition.
      inversion H4. subst. econstructor. rewrite <- indexr_insert_ge.
      eapply indexr_splice_tenv. eauto. lia. lia. lia. apply weaken_qstp_gen. auto.
      apply splice_qual_closed''; auto.
Qed.


(* ============== Transition Lemmas =============== *)

Lemma syntactic_to_set_qor : forall {q1 q2},
  syntactic_to_set (qor q1 q2) = qualifiers.qlub (syntactic_to_set q1) (syntactic_to_set q2).
Proof.
  intros. simpl. auto.
Qed.

Lemma syntactic_to_set_closed : forall {b f l q},
  closed_qual f b l q ->
  lambda_star.closed_qual f b l (syntactic_to_set q).
Proof.
  intros. induction H; simpl; auto.
  - constructor. rewrite setfacts.bound_singleton. lia. all: rewrite setfacts.bound_empty; lia.
  - constructor. 1,3: rewrite setfacts.bound_empty; lia. rewrite setfacts.bound_singleton. lia.
  - constructor. 1,2: rewrite setfacts.bound_empty; lia. rewrite setfacts.bound_singleton. lia.
  - apply lambda_star.closed_qual_qlub; auto.
Qed.


Lemma syntactic_to_set_splice_commute : forall {d k},
  syntactic_to_set (splice_qual k d) = lambda_star.splice_qual k (syntactic_to_set d).
Proof.
  intros. induction d; simpl; auto.
  - rewrite setfacts.splice_set_empty. auto.
  - destruct v.
    + destruct (le_lt_dec k i); simpl; unfold qualifiers.just_fv. rewrite setfacts.splice_set_singleton_inc; auto. rewrite setfacts.splice_set_singleton_inv; auto.
    + unfold qualifiers.just_bv. unfold syntactic_to_set. unfold qualifiers.just_bv. simpl. rewrite setfacts.splice_set_empty. auto.
  - unfold qualifiers.just_loc. rewrite setfacts.splice_set_empty. auto.
  - rewrite IHd1. rewrite IHd2. rewrite lambda_star.splice_qual_lub_dist. auto.
Qed.


Lemma syntactic_to_set_splice : forall {ds df d1 k}, 
  syntactic_to_set ds = qglb (syntactic_to_set df) (syntactic_to_set d1) ->
  syntactic_to_set (splice_qual k ds) = qglb (syntactic_to_set (splice_qual k df)) (syntactic_to_set (splice_qual k d1)).
Proof.
  intros. repeat rewrite syntactic_to_set_splice_commute. rewrite H. 
  rewrite lambda_star.splice_qual_glb_dist. auto.
Qed.



Lemma syntactic_to_set_subst_commute : forall {d k dx},
  syntactic_to_set (subst_q d k dx) = lambda_star.subst_q (syntactic_to_set d) k (syntactic_to_set dx).
Proof.
  intros. induction d; simpl; auto. 
  - rewrite setfacts.mem_empty. rewrite setfacts.remove_empty. rewrite setfacts.unsplice_set_empty. reflexivity.
  - destruct v.
    + bdestruct (i =? k); simpl; rewrite setfacts.mem_singleton.
      * symmetry in H. pose (H) as H0. apply Nat.eqb_eq in H0. rewrite H0. destruct (syntactic_to_set dx). do 2 rewrite setfacts.empty_union_left. subst.
        rewrite setfacts.remove_singleton_empty. rewrite setfacts.unsplice_set_empty. rewrite setfacts.empty_union_left. 
        reflexivity.
      * assert (k <> i) by auto. apply Nat.eqb_neq in H0. rewrite H0. unfold qualifiers.just_fv. f_equal.
        rewrite setfacts.remove_singleton_inv. 2: auto.
        rewrite setfacts.unsplice_set_singleton'. auto.
    + simpl. rewrite setfacts.mem_empty. unfold qualifiers.just_bv. rewrite setfacts.remove_empty. rewrite setfacts.unsplice_set_empty. reflexivity.
  - rewrite setfacts.mem_empty. rewrite setfacts.remove_empty. rewrite setfacts.unsplice_set_empty. reflexivity.
  - rewrite IHd1. rewrite IHd2.
Abort.

Lemma syntactic_to_set_subst1_commute : forall {d dx},
  syntactic_to_set (subst_q d 0 dx) = lambda_star.subst_q (syntactic_to_set d) 0 (syntactic_to_set dx).
Proof.
  intros. induction d; simpl; auto. 
  - rewrite setfacts.mem_empty. rewrite setfacts.remove_empty. rewrite setfacts.unsplice_set_empty. reflexivity.
  - destruct v.
    + bdestruct (i =? 0); simpl; rewrite setfacts.mem_singleton.
      * symmetry in H. pose (H) as H0. apply Nat.eqb_eq in H0. rewrite H0. destruct (syntactic_to_set dx). do 2 rewrite setfacts.empty_union_left. subst.
        rewrite setfacts.remove_singleton_empty. rewrite setfacts.unsplice_set_empty. rewrite setfacts.empty_union_left. 
        reflexivity.
      * assert (0 <> i) by auto. apply Nat.eqb_neq in H0. rewrite H0. unfold qualifiers.just_fv. f_equal.
        rewrite setfacts.remove_singleton_inv. 2: auto.
        rewrite setfacts.unsplice_set_singleton'. auto.
    + simpl. rewrite setfacts.mem_empty. unfold qualifiers.just_bv. rewrite setfacts.remove_empty. rewrite setfacts.unsplice_set_empty. reflexivity.
  - rewrite setfacts.mem_empty. rewrite setfacts.remove_empty. rewrite setfacts.unsplice_set_empty. reflexivity.
  - rewrite IHd1. rewrite IHd2. rewrite lambda_star.subst1_qlub_dist. auto.
Qed.

Lemma ty_syntactic_to_set_subst1_commute : forall {T dx},
  ty_syntactic_to_set (subst_ty T 0 dx) = lambda_star.subst_ty (ty_syntactic_to_set T) 0 (syntactic_to_set dx).
Proof.
  intros. induction T.
  - auto.
  - simpl. rewrite IHT1. rewrite IHT2. f_equal; auto. 1-2: apply syntactic_to_set_subst1_commute.
  - simpl. f_equal. auto.
Qed.



Lemma ty_syntactic_to_set_splice_commute : forall {T k},
  ty_syntactic_to_set (splice_ty k T) = lambda_star.splice_ty k (ty_syntactic_to_set T).
Proof.
  intros. induction T; auto.
  - simpl. rewrite IHT1. rewrite IHT2. repeat rewrite syntactic_to_set_splice_commute. auto.
  - simpl. rewrite IHT. auto.
Qed.

Lemma ctx_syntactic_to_set_ext_dist : forall {Γ1 Γ2},
  ctx_syntactic_to_set (Γ1 ++ Γ2) = (ctx_syntactic_to_set Γ1) ++ (ctx_syntactic_to_set Γ2).
Proof.
  intros. unfold ctx_syntactic_to_set. rewrite map_app; auto.
Qed.

Lemma ctx_syntactic_to_set_splice_commute : forall {Γ : tenv} {k},
  ctx_syntactic_to_set (splice_tenv k Γ) = lambda_star.splice_tenv k (ctx_syntactic_to_set Γ).
Proof.
  intros. induction Γ; simpl.
  - auto.
  - rewrite IHΓ. f_equal. rewrite syntactic_to_set_splice_commute. rewrite ty_syntactic_to_set_splice_commute. intuition.
Qed.

Lemma ctx_syntactic_to_set_subst1_commute : forall {Γ dx},
  ctx_syntactic_to_set ({0 |-> dx }ᴳ Γ) = lambda_star.subst_tenv (ctx_syntactic_to_set Γ) 0 (syntactic_to_set dx).
Proof.
  intros. induction Γ; simpl; auto.
  f_equal; auto.
  unfold ctx_transfer; simpl. destruct a. rewrite syntactic_to_set_subst1_commute. rewrite ty_syntactic_to_set_subst1_commute. auto.
Qed.

Lemma qstp_syntactic_to_set : forall Γ Σ q1 q2, 
  qstp Γ Σ q1 q2 ->
  lambda_star.qstp (ctx_syntactic_to_set Γ) (store_syntactic_to_set Σ) (syntactic_to_set q1) (syntactic_to_set q2).
Proof.
  intros. induction H; constructor; simpl; intuition.
  - destruct (syntactic_to_set q). intuition.
  - apply syntactic_to_set_closed. replace (length (ctx_syntactic_to_set Γ)) with (length Γ). replace (length (store_syntactic_to_set Σ)) with (length Σ). auto.
    unfold store_syntactic_to_set. 2: unfold ctx_syntactic_to_set. 1-2: rewrite map_length; auto.
  - replace (qualifiers.just_fv x) with (syntactic_to_set (just_fv x)) by auto. apply syntactic_to_set_closed. constructor. unfold ctx_syntactic_to_set. rewrite map_length. auto.
  - replace (qualifiers.just_loc x) with (syntactic_to_set (just_loc x)) by auto. apply syntactic_to_set_closed. constructor. unfold store_syntactic_to_set. rewrite map_length. auto.
  - inversion IHqstp; subst. apply qualifiers.subqual_or_sub_l. auto.
  - assert (closed_qual 0 (length Γ) (length Σ) (qor q2 q3)). apply qstp_closed in H. constructor; intuition. apply syntactic_to_set_closed in H1. replace (length Γ) with (length (ctx_syntactic_to_set Γ)) in H1. replace (length Σ) with (length (store_syntactic_to_set Σ)) in H1. simpl in H1. auto.
    unfold store_syntactic_to_set. 2: unfold ctx_syntactic_to_set. 1-2: apply map_length.
  - inversion IHqstp; subst. apply qualifiers.subqual_or_sub_r; auto.
  - assert (closed_qual 0 (length Γ) (length Σ) (qor q3 q2)). apply qstp_closed in H. constructor; intuition. apply syntactic_to_set_closed in H1. replace (length Γ) with (length (ctx_syntactic_to_set Γ)) in H1. replace (length Σ) with (length (store_syntactic_to_set Σ)) in H1. simpl in H1. auto.
    unfold store_syntactic_to_set. 2: unfold ctx_syntactic_to_set. 1-2: apply map_length.
  - inversion IHqstp1; subst. inversion IHqstp2; subst. eapply qualifiers.qqplus_bound; auto.
  - inversion IHqstp1; subst. auto.
  - inversion IHqstp1; subst. inversion IHqstp2; subst. eapply qualifiers.subqual_trans; eauto.
  - inversion IHqstp2; subst; auto.
Qed. 


Lemma syntactic_to_set_closed_inverse: forall f b l q,
  lambda_star.closed_qual f b l (syntactic_to_set q) -> 
  closed_qual f b l q.
Proof.
  intros. induction q; simpl in *.
  - constructor.
  - destruct v.
    + inversion H; subst. rewrite bound_singleton in H6. constructor. lia.
    + inversion H; subst. rewrite bound_singleton in H7. constructor. lia.
  - inversion H; subst. rewrite bound_singleton in H8. constructor. lia.
  - apply lambda_star_addition.closed_qual_qlub_inv in H. intuition. constructor; auto.
Qed.
  
Lemma syntactic_to_set_qstp_inverse : forall Γ Σ q1 q2, 
  lambda_star.qstp (ctx_syntactic_to_set Γ) (store_syntactic_to_set Σ) (syntactic_to_set q1) (syntactic_to_set q2) ->
  qstp Γ Σ q1 q2.
Proof.
  intros. inversion H; subst. clear H. apply syntactic_to_set_closed_inverse in H1.
  replace (length (ctx_syntactic_to_set Γ)) with (length Γ) in H1. 2: unfold ctx_syntactic_to_set; rewrite map_length; auto.
  replace (length (store_syntactic_to_set Σ)) with (length Σ) in H1. 2: unfold store_syntactic_to_set; rewrite map_length; auto.
  induction q1.
  - constructor. auto.
  - destruct v; induction q2.
    + inversion H0. apply setfacts.subset_of_empty in H. apply setfacts.singleton_nonempty in H. contradiction.
    + destruct v. 
      * inversion H0. apply setfacts.singleton_subset_in in H. bdestruct (i=?i0). subst; apply qstp_refl; auto. apply NatSetNotin.notin_singleton in H. contradiction. auto.
      * inversion H0. apply setfacts.subset_of_empty in H. apply setfacts.singleton_nonempty in H. contradiction.
    + inversion H0. apply setfacts.subset_of_empty in H. apply setfacts.singleton_nonempty in H. contradiction.
    + rewrite syntactic_to_set_qor in H0. apply lambda_star_addition.just_fv_subqual_qlub_inversion in H0. inversion H1; subst. destruct H0; intuition.
    + inversion H0. destruct H2. apply setfacts.subset_of_empty in H2. apply setfacts.singleton_nonempty in H2. contradiction.
    + destruct v.
      * inversion H0. destruct H2. apply setfacts.subset_of_empty in H2. apply setfacts.singleton_nonempty in H2. contradiction.
      * inversion H0. destruct H2. apply setfacts.singleton_subset_in in H2. bdestruct (i=?i0). subst; apply qstp_refl; auto. apply NatSetNotin.notin_singleton in H2. contradiction. auto.
    + inversion H0. destruct H2. apply setfacts.subset_of_empty in H2. apply setfacts.singleton_nonempty in H2. contradiction.
    + rewrite syntactic_to_set_qor in H0. apply lambda_star_addition.just_bv_subqual_qlub_inversion in H0. inversion H1; subst. destruct H0; intuition.
  - induction q2.
    + inversion H0. destruct H2. apply setfacts.subset_of_empty in H3. apply setfacts.singleton_nonempty in H3. contradiction.
    + destruct v.
      * inversion H0. destruct H2. apply setfacts.subset_of_empty in H3. apply setfacts.singleton_nonempty in H3. contradiction.
      * inversion H0. destruct H2. apply setfacts.subset_of_empty in H3. apply setfacts.singleton_nonempty in H3. contradiction.
    + inversion H0. destruct H2. apply setfacts.singleton_subset_in in H3. bdestruct (l=?l0). subst; apply qstp_refl; auto. apply NatSetNotin.notin_singleton in H3. contradiction. auto.
    + rewrite syntactic_to_set_qor in H0. apply lambda_star_addition.just_loc_subqual_qlub_inversion in H0. inversion H1; subst. destruct H0; intuition.
  - rewrite syntactic_to_set_qor in H0. apply qualifiers.qlub_is_lub_2 in H0. destruct H0. constructor; intuition.
Qed.

Lemma ty_syntactic_to_set_closed : forall {b f l T},
  closed_ty f b l T ->
  lambda_star.closed_ty f b l (ty_syntactic_to_set T).
Proof.
  intros. induction H.
  - constructor.
  - constructor. intuition. 
  - constructor; auto. 1-2: apply syntactic_to_set_closed; auto.
Qed. 

Lemma open_syntactic_to_set_commute : forall {k d q},
  syntactic_to_set (open_qual k d q) = lambda_star.open_qual k (syntactic_to_set d) (syntactic_to_set q).
Proof.
  intros. induction q; simpl; intuition.
  - rewrite setfacts.mem_empty. destruct (syntactic_to_set d); auto.
  - destruct v; simpl.
    + destruct (syntactic_to_set d). rewrite setfacts.mem_empty. auto.
    + bdestruct (i=?k); destruct (syntactic_to_set d); simpl.
      * rewrite setfacts.mem_singleton. subst. assert (k=?k = true). apply Nat.eqb_eq; auto. rewrite H. rewrite setfacts.remove_singleton_empty. do 3 rewrite setfacts.empty_union_left. auto.
      * rewrite setfacts.mem_singleton. assert (k=?i = false). apply Nat.eqb_neq; auto. rewrite H0. auto.
  - destruct (syntactic_to_set d). rewrite setfacts.mem_empty. auto.
  - rewrite IHq1. rewrite IHq2. rewrite lambda_star.open_qual_qqplus_dist. auto.
Qed.


Lemma openq'_syntactic_to_set_commute : forall {Γ d},
  syntactic_to_set (openq' Γ d) = lambda_star.openq' (ctx_syntactic_to_set Γ) (syntactic_to_set d).
Proof.
  intros. induction d; simpl; intuition.
  - rewrite setfacts.mem_empty; auto.
  - destruct v; simpl.
    + rewrite setfacts.mem_empty. auto.
    + rewrite setfacts.mem_singleton. destruct i; simpl. rewrite setfacts.empty_union_left. rewrite setfacts.remove_singleton_empty. rewrite setfacts.empty_union_left. unfold qualifiers.just_fv. f_equal.
      f_equal. unfold ctx_syntactic_to_set. rewrite map_length. auto.
      intuition.
  - rewrite setfacts.mem_empty; auto.
  - unfold openq' in *; unfold openq in *. rewrite IHd1. rewrite IHd2. unfold lambda_star.openq' in *. rewrite lambda_star.openq_u_distribute. auto.
Qed.

Lemma open_ty_syntactic_to_set_commute : forall {k d T},
  ty_syntactic_to_set (open_rec_ty k d T) = lambda_star.open_rec_ty k(syntactic_to_set d) (ty_syntactic_to_set T).
Proof.
  intros. generalize dependent k. induction T; simpl; intuition.
  - f_equal. apply open_syntactic_to_set_commute. apply open_syntactic_to_set_commute. auto. auto.
  - f_equal. auto.
Qed.

Lemma open_ty'_syntactic_to_set_commute : forall {Γ T},
  ty_syntactic_to_set (open_ty' Γ T) = lambda_star.open_ty' (ctx_syntactic_to_set Γ) (ty_syntactic_to_set T).
Proof.
  intros. induction T; simpl; intuition.
  - unfold open_ty' in *; unfold open_ty in *. unfold lambda_star.open_ty' in *. unfold lambda_star.open_ty in *. simpl.
    replace (qualifiers.just_fv (length (ctx_syntactic_to_set Γ))) with (syntactic_to_set (just_fv (length Γ))). 2:{unfold ctx_syntactic_to_set; rewrite map_length; auto. }
    f_equal; intuition. 
    apply open_syntactic_to_set_commute. 
    apply open_syntactic_to_set_commute.
    apply open_ty_syntactic_to_set_commute. apply open_ty_syntactic_to_set_commute.
  - unfold open_ty' in *; unfold open_ty in *. unfold lambda_star.open_ty' in *. unfold lambda_star.open_ty in *. simpl. f_equal.
    apply IHT.
Qed.

Lemma store_syntactic_to_set_extends : forall {Σ' Σ},
  (Σ') ⊇ (Σ) -> lambda_star.extends (store_syntactic_to_set Σ') (store_syntactic_to_set Σ).
Proof.
  intros. destruct H. unfold lambda_star.extends. rewrite H. unfold store_syntactic_to_set. rewrite map_app. exists (map (fun T : ty => ty_syntactic_to_set T) x). auto.
Qed.

Lemma stp_syntactic_to_set : forall Γ Σ T1 q1 T2 q2, 
  stp Γ Σ T1 q1 T2 q2 ->
  lambda_star.stp (ctx_syntactic_to_set Γ) (store_syntactic_to_set Σ) (ty_syntactic_to_set T1) (syntactic_to_set q1) (ty_syntactic_to_set T2) (syntactic_to_set q2).
Proof.
  intros. induction H; simpl; econstructor; eauto; intuition.
  - apply qstp_syntactic_to_set. auto.
  - apply qstp_syntactic_to_set. auto.
  - replace (length (ctx_syntactic_to_set Γ)) with (length Γ). replace (length (store_syntactic_to_set Σ)) with (length Σ). eapply ty_syntactic_to_set_closed in H; simpl in H; auto.
    unfold store_syntactic_to_set. 2: unfold ctx_syntactic_to_set. 1-2: rewrite map_length; auto.
  - replace (length (ctx_syntactic_to_set Γ)) with (length Γ). replace (length (store_syntactic_to_set Σ)) with (length Σ). eapply ty_syntactic_to_set_closed in H0; simpl in H0; auto.
    unfold store_syntactic_to_set. 2: unfold ctx_syntactic_to_set. 1-2: rewrite map_length; auto.
  - apply qstp_syntactic_to_set; auto.
  - replace (ctx_syntactic_to_set ((T3, d3) :: Γ)) with ((ctx_transfer (T3, d3)) :: (ctx_syntactic_to_set Γ)) in IHstp2 by auto. simpl in IHstp2.
    do 2 rewrite <- open_ty'_syntactic_to_set_commute. do 2 rewrite <- openq'_syntactic_to_set_commute. auto.
Qed.

Lemma qmem_syntactic_to_set : forall {x q},
  $ x ∈ᵥ q <-> qualifiers.qmem (inl $ x) (syntactic_to_set q).
Proof.
  intros. split.
  - induction q; simpl in *; intuition.
    + destruct v. subst. compute. apply NatSetNotin.in_singleton.
      contradiction.
    + apply qualifiers.qmem_lub_or_commute. left. auto.
    + apply qualifiers.qmem_lub_or_commute. right. auto.
  - induction q; simpl in *; intuition.
    + apply setfacts.in_non_empty in H. intuition.
    + destruct v; simpl in *. bdestruct (i=?x). auto. apply NatSetNotin.notin_singleton in H; intuition. 
      apply setfacts.in_non_empty in H. intuition.
    + apply setfacts.in_non_empty in H. intuition.
    + apply qualifiers.qmem_lub_or_commute in H; intuition.
Qed.

Lemma indexr_syntactic_to_set : forall {Γ x U q},
  indexr x Γ = Some(U, q)           ->
  indexr x (ctx_syntactic_to_set Γ) = Some(ctx_transfer (U, q)).
Proof.
  intros. induction Γ; simpl.
  - discriminate H.
  - replace (length (ctx_syntactic_to_set Γ)) with (length Γ) in *. 2: unfold ctx_syntactic_to_set; rewrite map_length; auto.
    bdestruct (x =? length (Γ)). 
    rewrite H0 in H.  rewrite indexr_head in H. inversion H. subst. auto.
    rewrite indexr_skip in H; auto.
Qed.

Lemma saturated_syntactic_to_set : forall {Γ Σ d},
  saturated Γ Σ d ->
  lambda_star.saturated (ctx_syntactic_to_set Γ) (store_syntactic_to_set Σ) (syntactic_to_set d).
Proof.
  intros. unfold saturated in H. unfold lambda_star.saturated. intros. assert (H1:=H0). apply qmem_syntactic_to_set in H1. specialize (H x H1). generalize dependent x. induction d; simpl.
  - intros. apply NatSetNotin.notin_empty in H0. intuition.
  - intros. destruct v. 
    + bdestruct (i=?x). subst. inversion H. econstructor.
      eapply indexr_syntactic_to_set; eauto.
      apply qstp_syntactic_to_set in H3. inversion H3; auto.
      apply syntactic_to_set_closed. eapply closed_qual_monotone; eauto. unfold store_syntactic_to_set; rewrite map_length; auto.
      intuition.
    + intuition.
  - intros. apply NatSetNotin.notin_empty in H0. intuition.
  - intros. inversion H. assert (saturated_var Γ Σ x d1). {
      econstructor; eauto. admit. 
    } 
    (* This is impossible!
      So, saturated transition is impossible because we can't handle or case. Similarly, we can't say that saturated (qor a b) -> saturated (a) /\ saturated (b) in either set or syntactic base. 
      In a similar way, This also rejects saturated (a ⊓ b) in set level, because we still need separated seturated ONLY for subst1_separation preservation (Hoverlap in substitution_gen)
      It means we definitely should saturate in the set level and separately
    *)
Abort.

(* TODO: we just want EXISTS an inverse function, so regardless the definition of set_to_syntactic, just make sure fit this definition is OK *)
Lemma syntactic_to_set_indentity : forall d,
  syntactic_to_set (set_to_syntactic d) = d.
Proof.
  induction d. unfold set_to_syntactic. unfold syntactic_to_set; simpl. compute.
Admitted.



Lemma syntactic_to_set_subqual_inverse : forall {Γ Σ d1 d1' df df'},
  forall {ds'}, syntactic_to_set ds' = qualifiers.qglb (syntactic_to_set d1') (syntactic_to_set df') ->
  qstp Γ Σ d1 d1' ->
  qstp Γ Σ df df' ->
  qstp Γ Σ (set_to_syntactic (qualifiers.qglb (syntactic_to_set d1) (syntactic_to_set df))) ds'.
Proof.
  intros.
  (* too hard, we only want exists ds *)
Abort.

Lemma syntactic_to_set_qstp_exists : forall {Γ Σ d1 d1' df df'},
  forall {ds'}, syntactic_to_set ds' = qualifiers.qglb (syntactic_to_set d1') (syntactic_to_set df') ->
  qstp Γ Σ d1 d1' ->
  qstp Γ Σ df df' ->
  exists ds, (syntactic_to_set ds =  qualifiers.qglb (syntactic_to_set d1) (syntactic_to_set df)) /\ 
  qstp Γ Σ ds ds'.
Proof.
  intros. exists (set_to_syntactic (qualifiers.qglb (syntactic_to_set d1) (syntactic_to_set df))). split.
  - rewrite syntactic_to_set_indentity; auto.
  - apply syntactic_to_set_qstp_inverse. constructor. rewrite H. rewrite syntactic_to_set_indentity. 
    apply qstp_syntactic_to_set in H0, H1. inversion H0; subst. inversion H1; subst.
    apply lambda_star_addition.subqual_qglb_lr; auto.
    apply qstp_closed in H0; destruct H0. apply qstp_closed in H1; destruct H1.
    rewrite H. apply lambda_star.closed_qual_qqcap. 1-2: apply syntactic_to_set_closed; eapply closed_qual_monotone; eauto.
    1,3: unfold ctx_syntactic_to_set. 3,4: unfold store_syntactic_to_set. all: rewrite map_length; auto.
Qed. 


(* =========== End of Transition Lemma ===========*)


(* Note: Notice that splice will never affect loc, so it means we can use similar method to prove the eqqual case in has_type *)
Lemma weaken_qstp_splice_loc_helper : forall {Γ1 Γ2 Σ l d2}, qstp (Γ1 ++ Γ2) Σ (just_loc l) d2 -> forall {X}, qstp (splice_tenv (length Γ2) Γ1 ++ X :: Γ2) Σ (just_loc l) (splice_qual (length Γ2) d2).
Proof.
  intros. remember (Γ1 ++ Γ2) as Γ. remember (just_loc l) as d1.  induction H; subst; try discriminate.
  - constructor. assumption. 
  - constructor; fold splice_qual. apply IHqstp; auto. apply splice_qual_closed'. eapply closed_qual_monotone; eauto. do 2 rewrite app_length. rewrite splice_tenv_length. auto.
  - intros. intuition. apply qstp_or_r_sub; fold splice_qual. apply H2. apply splice_qual_closed'. eapply closed_qual_monotone; eauto. do 2 rewrite app_length. rewrite splice_tenv_length. auto.
  - intuition. apply (@qstp_trans _ _ (just_loc l) (splice_qual (length Γ2) q2)). apply H3. apply weaken_qstp_gen. assumption.
Qed.

Lemma weaken_gen : forall {t Γ1 Γ2 φ Σ T d},
    has_type (Γ1 ++ Γ2) φ Σ t T d ->
    let k := (length Γ2) in
    forall X, has_type ((splice_tenv k Γ1) ++ X :: Γ2) (splice_qual k φ) Σ (splice k t) (splice_ty k T) (splice_qual k d).
Proof.
  intros t Γ1 Γ2 φ Σ T d HT. remember (Γ1 ++ Γ2) as Γ. generalize dependent Γ1. generalize dependent Γ2.
  induction HT; intros; subst.
  - (* tunit *) simpl. constructor. eapply splice_qual_closed'.
    rewrite app_length in *. rewrite splice_tenv_length. auto.
  - (* t_var *) simpl.
    destruct (le_lt_dec k x) eqn:Heq.
    * (* |Γ2| <= x < |Γ1|+|Γ2|*)
      apply t_var with (d:=(splice_qual k d)).
      rewrite <- indexr_insert_ge. erewrite indexr_splice_tenv; eauto. lia.
      erewrite <- splice_qual_just_fv_ge; eauto.
      apply weaken_qstp_gen. assumption.       
      eapply splice_ty_closed''; eauto. eapply splice_qual_closed''; eauto.
    * (* |Γ2| > x *)
      rewrite indexr_skips in H; auto. 
      apply t_var with (d:=d).
      rewrite <- indexr_insert_lt; auto. rewrite indexr_skips; auto.
      erewrite splice_ty_id. auto.
      eapply closed_ty_monotone; eauto. lia.
      erewrite <- splice_qual_just_fv_lt; eauto.
      apply weaken_qstp_gen. auto. 
      erewrite splice_ty_id; eauto. eapply closed_ty_monotone; eauto. lia. auto.
  - (* t_abs *) rewrite app_length in *. simpl. constructor.
    apply splice_closed'.
    1-2: rewrite app_length; rewrite splice_tenv_length; simpl;
      replace (length Γ1 + S (length Γ2)) with (S (length Γ1 + length Γ2)); eauto.
    inversion H0. subst. constructor. 1,2: apply splice_qual_closed; auto. 1,2 : apply splice_ty_closed; auto.
    apply weaken_qstp_gen. auto.
    rewrite app_comm_cons.
    replace ((splice_ty k T1, splice_qual k d1) :: splice_tenv k Γ1) with (splice_tenv k ((T1, d1) :: Γ1)); auto.
    replace (splice_qual k df ⊔ just_fv (length (splice_tenv k Γ1 ++ X :: Γ2)))
            with (splice_qual k (df ⊔ just_fv (length Γ1 + length Γ2))).
    subst k. rewrite <- splice_open'. rewrite <- splice_ty_open'. rewrite <- splice_qual_open'.
    rewrite @open_tm'_len with (Γ':=(Γ1 ++ Γ2)). rewrite @open_ty'_len with (Γ':=(Γ1 ++ Γ2)).
    rewrite @openq'_len with (Γ':=(Γ1 ++ Γ2)).
    apply IHHT; intuition. 1-4 : repeat rewrite app_length; rewrite splice_tenv_length; auto.
    simpl. repeat rewrite splice_qual_glb_dist. repeat rewrite splice_qual_lub_dist. unfold "⋓".
    f_equal. unfold just_fv. destruct (le_lt_dec k (length Γ1 + length Γ2)). assert (S (length Γ1 + length Γ2) = (length Γ1 + S (length Γ2))) by lia. rewrite H2. reflexivity. lia.
  - (* tapp *) simpl. rewrite splice_qual_open''. eapply t_app with (T1:=(splice_ty k T1)) (df:=(splice_qual k df)) (ds' := (splice_qual k ds')).
    eapply syntactic_to_set_splice; eauto. 
    replace (TFun (splice_qual k ds') (splice_qual k d2) (splice_ty k T1) (splice_ty k T2)) with
    (splice_ty k (TFun (ds') d2 T1 T2)); auto.
    apply IHHT1; auto. 
    apply IHHT2; auto.
    eapply splice_ty_closed'. rewrite app_length in *. rewrite splice_tenv_length. auto.
    subst k; rewrite <- @splice_qual_empty with (k := length Γ2); rewrite <- splice_qual_open''.
    eapply weaken_qstp_gen; eauto.
    1-2: eapply weaken_qstp_gen; eauto.    
    1-2: eapply weaken_qstp_gen; eauto.

    1-2: assert (k = length (ctx_syntactic_to_set Γ2)). 1,3:
      subst k; unfold ctx_syntactic_to_set; rewrite map_length; auto.

    all: rewrite ctx_syntactic_to_set_ext_dist; rewrite ctx_syntactic_to_set_splice_commute; simpl; rewrite syntactic_to_set_splice_commute.
    rewrite ctx_syntactic_to_set_ext_dist in H6. specialize (lambda_star.weaken_saturated H6). intros. replace (length Γ2) with k by auto. rewrite H8. apply H9.
    rewrite ctx_syntactic_to_set_ext_dist in H7. specialize (lambda_star.weaken_saturated H7). intros. replace (length Γ2) with k by auto. rewrite H8. apply H9. 
  - (* t_loc *) simpl. constructor. 
    eapply splice_qual_closed'. rewrite app_length in *. rewrite splice_tenv_length. auto.
    erewrite splice_ty_id; eauto. eapply closed_ty_monotone; eauto. lia.
    erewrite splice_ty_id; eauto. eapply closed_ty_monotone; eauto. lia.
    apply weaken_qstp_splice_loc_helper. assumption.
  - (* t_ref *) simpl. eapply t_ref. simpl in IHHT. specialize (IHHT Γ2 Γ1). intuition.    
  - (* t_deref *) simpl. econstructor. simpl in IHHT. subst k. apply IHHT; auto.
  - (* t_assign *) replace (splice_qual k ∅) with (∅) by auto. replace (splice_ty k TUnit) with (TUnit) by auto. simpl. eapply t_assign.
    1-2: replace (∅) with (splice_qual k ∅) by auto.
    replace (TRef TUnit) with (splice_ty k (TRef TUnit)) by auto. apply IHHT1; auto.
    replace (TUnit) with ((splice_ty k TUnit)) by auto. apply IHHT2; auto.  
  - (* t_sub *) eapply t_sub. eapply IHHT; auto.
    apply @weaken_stp_gen; eauto; lia. apply weaken_qstp_gen. auto. 
Qed.

Lemma weaken_flt : forall {Γ φ Σ t T d},
    has_type Γ φ Σ t T d ->
    forall {φ'}, qstp Γ Σ φ φ' ->
                 closed_qual 0 (length Γ) (length Σ) φ' ->
    has_type Γ φ' Σ t T d.
  intros Γ φ Σ t T d HT. induction HT; intros; econstructor; eauto; eapply qstp_trans; eauto.
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
    has_type [] φ Σ t T d -> forall {φ' Γ}, qstp Γ Σ φ φ' -> closed_qual 0 (length Γ) (length Σ) φ' -> has_type Γ φ' Σ t T d.
  intros. eapply weaken_flt; eauto. apply weaken. auto.
Qed.

Lemma qstp_weaken_store : forall {Γ Σ Σ' q1 q2},
  (Σ') ⊇ (Σ) ->
  qstp Γ Σ q1 q2 ->
  qstp Γ Σ' q1 q2.
Proof.
  intros. unfold extends in H. destruct H. induction H0; subst.
  - constructor. eapply closed_qual_monotone; eauto. rewrite app_length. lia.
  - constructor. assumption.
  - constructor. rewrite app_length. lia.
  - constructor. apply IHqstp; auto. eapply closed_qual_monotone; eauto. rewrite app_length. lia.
  - apply qstp_or_r_sub. apply IHqstp; auto. eapply closed_qual_monotone; eauto. rewrite app_length. lia.
  - constructor; intuition.
  - intuition. apply (@qstp_trans _ _ q1 q2); auto.
Qed.

Lemma weaken_store : forall {Γ φ Σ t T d}, has_type Γ φ Σ t T d -> forall {Σ'}, Σ' ⊇ Σ -> has_type Γ φ Σ' t T d.
  intros Γ φ Σ t T d HT.
Proof.
  induction HT; intros; intuition; econstructor; eauto;
    try solve [eapply closed_qual_monotone; eauto; apply extends_length; auto];
    try solve [eapply closed_tm_monotone; eauto; apply extends_length; auto];
    try solve [eapply closed_ty_monotone; eauto; apply extends_length; auto];
    try solve [eapply weaken_store_saturated; eauto];
    try solve [eapply qstp_weaken_store; eauto].
  - eapply lambda_star.weaken_store_saturated; eauto. 
    apply store_syntactic_to_set_extends; auto. 
  - eapply lambda_star.weaken_store_saturated; eauto. apply store_syntactic_to_set_extends; auto.
  - destruct H3. rewrite H3. rewrite <- H0. rewrite indexr_skips; auto. apply indexr_var_some' in H0. auto.
  - eapply weaken_stp_store_ext; eauto.
Qed.

Lemma narrowing_saturated : forall {Γ1 U du Γ2 Σ q},
    saturated (Γ1 ++ (U,du) :: Γ2) Σ q ->
    forall {V dv}, stp Γ2 Σ V dv U du -> saturated (Γ1 ++ (V,dv) :: Γ2) Σ q.
  intros. unfold saturated. intros.
  specialize (H x H1). inversion H. destruct (PeanoNat.Nat.lt_trichotomy x (length Γ2)) as [Hlen | [Hlen | Hlen] ].
  - apply (sat_var U0 q'); auto. rewrite indexr_skips in H2; simpl; auto.
    rewrite indexr_skips. rewrite indexr_skip in H2; try lia. rewrite indexr_skip; try lia.
    auto. simpl. auto. eapply narrowing_qstp_gen; eauto.
  - rewrite indexr_skips in H2; simpl; auto. subst. rewrite indexr_head in H2. inversion H2. subst.
    apply (sat_var V dv). rewrite indexr_skips; auto. rewrite indexr_head. auto.
    set (Hstp:=H0). apply stp_qstp_inv in Hstp. eapply narrowing_qstp_gen; eauto. eapply (@qstp_trans _ _ _ q'); eauto. replace (Γ1 ++ (U0, q') :: Γ2) with (Γ1 ++ [(U0, q')] ++ Γ2) by auto. apply weaken_qstp. apply weaken_qstp. auto.
    apply stp_closed in H0. intuition. lia.
  - destruct x. lia. rewrite <- indexr_insert_ge in H2; try lia.
    apply (sat_var U0 q'); auto. rewrite <- indexr_insert_ge; try lia. auto.
    eapply narrowing_qstp_gen; eauto. 
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
      eapply narrowing_qstp_gen; eauto.
    + subst. rewrite indexr_insert in H. inversion H. subst.
      apply t_sub with (T1:=V) (d1:=just_fv (length Γ2)); auto. apply t_var with (d:=dv).
      rewrite indexr_insert. auto. 
      eapply narrowing_qstp_gen; eauto. 
      1,2 : apply stp_closed in H3; intuition.
      eapply stp_shrink_var; eauto. eapply weaken_stp'; eauto. eapply weaken_stp; eauto. rewrite app_length. simpl. lia.
      eapply narrowing_qstp_gen; eauto.
    + apply t_var with (d:=d); auto. destruct x. lia. rewrite <- indexr_insert_ge; try lia.
      rewrite <- indexr_insert_ge in H; try lia. auto.
      eapply narrowing_qstp_gen; eauto.
  - repeat rewrite app_length in *; simpl in *; auto.
    constructor; auto. 1-2 : rewrite app_length in *; simpl in *; auto.
    eapply narrowing_qstp_gen; eauto.
    rewrite @open_tm'_len with (Γ' := (Γ1 ++ (U, du) :: Γ2)).
    rewrite @open_ty'_len with (Γ' := (Γ1 ++ (U, du) :: Γ2)).
    rewrite @openq'_len with (Γ' := (Γ1 ++ (U, du) :: Γ2)).
    2-4 : repeat rewrite app_length; simpl; auto.
    rewrite app_length. simpl.
    rewrite app_comm_cons.
    eapply IHHT; eauto. simpl. auto.
  - econstructor; eauto.
    repeat rewrite app_length in *; simpl in *; auto.
    rewrite app_length in *. simpl in *. auto.
    eapply narrowing_qstp_gen; eauto.
    1-2: eapply narrowing_qstp_gen; eauto.
    1-2: eapply narrowing_qstp_gen; eauto.
    rewrite ctx_syntactic_to_set_ext_dist in H6. rewrite ctx_syntactic_to_set_ext_dist. 
    replace (ctx_syntactic_to_set ((U, du) :: Γ2)) with ((ctx_transfer (U, du)) :: ctx_syntactic_to_set(Γ2)) in H2 by intuition. replace (ctx_syntactic_to_set ((V, dv) :: Γ2)) with ((ctx_transfer (V, dv)) :: ctx_syntactic_to_set(Γ2)) by intuition.
    eapply lambda_star.narrowing_saturated; eauto. apply stp_syntactic_to_set. auto. 
    rewrite ctx_syntactic_to_set_ext_dist in H7. rewrite ctx_syntactic_to_set_ext_dist. 
    replace (ctx_syntactic_to_set ((U, du) :: Γ2)) with ((ctx_transfer (U, du)) :: ctx_syntactic_to_set(Γ2)) in H2 by intuition. replace (ctx_syntactic_to_set ((V, dv) :: Γ2)) with ((ctx_transfer (V, dv)) :: ctx_syntactic_to_set(Γ2)) by intuition.
    eapply lambda_star.narrowing_saturated; eauto. apply stp_syntactic_to_set. auto. 
  - econstructor; eauto.
    repeat rewrite app_length in *; simpl in *; auto.
    eapply narrowing_qstp_gen; eauto.
  - eapply t_ref; eauto.
  - econstructor; eauto.
  - eapply t_assign; eauto.    
  - eapply t_sub; eauto. eapply narrowing_stp_gen; eauto.
    eapply narrowing_qstp_gen; eauto.
Qed.

Lemma narrowing : forall {Γ U du φ Σ t T d}, has_type ((U,du) :: Γ) φ Σ t T d -> forall {V dv}, stp Γ Σ V dv U du -> saturated Γ Σ du -> has_type ((V,dv) :: Γ) φ Σ t T d.
  intros. specialize (@narrowing_gen t0 [] U du Γ φ Σ T d) as narrow. simpl in *. eapply narrow; eauto.
Qed.

Lemma values_stuck : forall {v}, value v -> forall {t σ σ'}, step v σ t σ' -> False.
  intros. inversion H0; subst; inversion H.
Qed.

Lemma CtxOK_ext : forall {Γ φ Σ σ}, CtxOK Γ φ Σ σ -> forall {v T}, has_type Γ φ Σ v T ∅ -> value v -> CtxOK Γ φ (T :: Σ) (v :: σ).
  intros. unfold CtxOK in *. split. simpl. lia.
  intros. destruct H as [Hlen Hprev]. destruct (beq_nat l (length σ)) eqn:Heql.
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

Lemma CtxOK_weaken_flt : forall {Γ φ Σ σ}, CtxOK Γ φ Σ σ -> forall {φ'}, closed_qual 0 (length Γ) (length Σ) φ' -> qstp Γ Σ φ φ' -> CtxOK Γ φ' Σ σ.
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
  induction q; intros.
  - reflexivity.
  - destruct v; simpl. 2: reflexivity. destruct (i =? 0) eqn:Hi; inversion H; intuition.
  - reflexivity.
  - simpl. inversion H; subst. rewrite IHq1. rewrite IHq2. reflexivity. auto. auto.
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
  intros t.
  induction t; intros b loc Hc; inversion Hc; subst; intros; simpl; intuition;
                       try solve [erewrite IHt; eauto];
                       try solve [erewrite IHt1; eauto; erewrite IHt2; eauto].
Qed.

Lemma open_subst1_qual : forall {q b l},
    closed_qual b 0 l q ->
    forall {k d1},
      [[k ~> d1 ]]ᵈ q = { 0 |-> d1 }ᵈ ([[k ~> (just_fv 0)]]ᵈ q).
Proof.
  unfold just_fv in *. induction q; intros; try intuition; inversion H; subst; unfold just_fv; intuition.
  - unfold open_qual. destruct (x =? k) eqn:Hx; simpl; reflexivity.
  - simpl. erewrite IHq1. erewrite IHq2. intuition. eauto. eauto.
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
    forall {k b' l' t1},
      closed_tm b' 0 l' t1 ->
      [[k ~> t1 ]]ᵗ t = { 0 |-> t1 }ᵗ ([[k ~> $ 0]]ᵗ t).
  intro t.
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
Proof.
  intros. unfold just_fv. induction q. 
  - constructor.
  - destruct v. 
    + simpl. destruct i; simpl. 2: reflexivity. 
      remember (0) as b. induction H. constructor. constructor. intuition. constructor. 
      simpl. rewrite IHclosed_qual1. rewrite IHclosed_qual2. reflexivity. assumption. assumption. 
    + simpl. destruct (i=?k). auto. auto.
  - simpl. reflexivity. 
  - simpl. rewrite IHq1. rewrite IHq2. auto.
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
Proof.
  intros. induction q; simpl. 
  - constructor.
  - destruct v.
    + destruct i; simpl. eapply closed_qual_monotone; eauto. lia. lia. inversion H; subst. constructor. lia.
    + constructor. inversion H; subst. assumption.
  - constructor. inversion H; subst. lia.
  - inversion H; subst. constructor; intuition. 
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

Lemma subst1_qlub_dist : forall {q1 q2 df},
    ({ 0 |-> df }ᵈ (q1 ⊔ q2)) = (({ 0 |-> df }ᵈ q1) ⊔ ({ 0 |-> df }ᵈ q2)).
Proof.
  intros. unfold qlub. simpl. reflexivity.
Qed.


Lemma closed_0_subst_id: forall {l q d},
  closed_qual 0 0 l q ->
  {0 |-> d }ᵈ q = q.
Proof.
  intros. induction q; simpl; try reflexivity.
  - destruct v; simpl.
    inversion H; intuition. 
    reflexivity.
  - inversion H; subst; intuition. rewrite H0. rewrite H1. reflexivity.
Qed.

Lemma subst1_qual_plus : forall {Γ Σ du},
    closed_qual 0 0 (length Σ) du -> 
    eqqual Γ Σ du ({0 |-> du }ᵈ (du ⊕ 0)).
Proof.
  intros. simpl. constructor. 
  - induction du; simpl.
    + constructor. constructor. intuition. intuition.
    + destruct v; simpl. constructor. destruct i; simpl. apply qstp_refl. constructor. inversion H. intuition. inversion H. intuition. 
      eapply closed_qual_monotone; eauto. lia.
      constructor. apply qstp_refl. 1-2: eapply closed_qual_monotone; eauto; lia.
    + constructor. apply qstp_refl. 1-2: eapply closed_qual_monotone; eauto; lia.
    + simpl. apply qstp_or_r_sub. apply qstp_refl. eapply closed_qual_monotone; eauto; lia. inversion H; subst. constructor.
      (* this should be true because under closed_qual 0 0, then the substitution should be id *)
      eapply closed_qual_subst1; eauto. eapply closed_qual_monotone; eauto; lia.
      eapply closed_qual_subst1; eauto. eapply closed_qual_monotone; eauto; lia.
  - induction du; simpl. 
    + constructor; constructor. intuition. intuition.
    + destruct v; simpl. inversion H; intuition. inversion H; intuition.
    + inversion H; subst. constructor; apply qstp_refl; constructor; intuition.
    + apply qstp_sub_or. inversion H; subst; intuition. erewrite closed_0_subst_id; eauto. erewrite closed_0_subst_id; eauto. 1-2: apply qstp_refl; eapply closed_qual_monotone; eauto; lia.
Qed.

Lemma subst1_qual_plus' : forall {Σ du du'},
    qstp [] Σ du' du -> 
    eqqual [] Σ ({0 |-> du }ᵈ (du' ⊕ 0)) du.
Proof.
  intros. simpl. constructor. 
  2:{apply qstp_or_r_sub. apply qstp_refl. apply qstp_closed in H. intuition. apply qstp_closed in H. eapply closed_qual_subst1; eauto. destruct H. eapply closed_qual_monotone; eauto. intuition. }
  constructor. 2: {apply qstp_refl. apply qstp_closed in H. intuition. }
  remember ([]) as Γ.
  induction du'; simpl; subst.
  - constructor. apply qstp_closed in H; intuition.
  - assert (closed_qual 0 0 (length Σ) v). apply qstp_closed in H. eapply closed_qual_monotone; eauto. intuition. inversion H0; intuition.
  - assumption.
  - apply qstp_sub_or_inversion in H. constructor; intuition.
Qed.

Lemma subst1_qual_plus_dist : forall {x d df},
    1 <= x -> ({ 0 |-> df }ᵈ (d ⊕ x)) = (({ 0 |-> df }ᵈ d) ⊕ (pred x)).
Proof.
  intros. unfold qplus. unfold just_fv. simpl. destruct x; simpl. intuition. intuition.
Qed.

Lemma subst1_open_qual_comm : forall {k l d1 d2 q1},
    closed_qual 0 0 l q1 ->
    { 0 |-> q1 }ᵈ (open_qual k d1 d2) = open_qual k ({ 0 |-> q1 }ᵈ d1) ({ 0 |-> q1 }ᵈ d2).
Proof.
  intros. induction d2; simpl; intuition.
  2: rewrite IHd2_1; rewrite IHd2_2; reflexivity.
  destruct v.
  2: { simpl. destruct (i =? k). reflexivity. simpl. reflexivity. }
  destruct i; simpl. induction q1; intuition. destruct v; simpl. reflexivity.
  destruct (i=?k). inversion H; intuition. reflexivity. 2: reflexivity.
  + simpl. inversion H; subst. intuition.  
    assert (q1_1 = [[k ~> {0 |-> qor q1_1 q1_2 }ᵈ d1 ]]ᵈ q1_1). eapply open_qual_id; eauto. assert (q1_2 = [[k ~> {0 |-> qor q1_1 q1_2 }ᵈ d1 ]]ᵈ q1_2). eapply open_qual_id; eauto.
    rewrite H2 at 1. rewrite H3 at 2. auto.
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

(* The assumption is wrong in text, but it's still true. use subst_qstp instaed *)
Lemma subst_qual_subqual_monotone : forall {Γ Σ d1 d2}, 
  qstp Γ Σ d1 d2 -> 
  forall {df}, closed_qual 0 0 (length Σ) df ->
  qstp ({0 |-> df}ᴳ Γ) Σ ({0 |-> df }ᵈ d1) ({0 |-> df }ᵈ d2).
Proof.
  intros. induction H; simpl; intuition.
  - constructor. eapply closed_qual_subst1; eauto. eapply closed_qual_monotone; eauto. rewrite subst1_tenv_length. lia.
  - destruct x; simpl. apply qstp_refl. eapply closed_qual_monotone; eauto. lia. apply qstp_refl. constructor. rewrite subst1_tenv_length. lia.
  - constructor. apply H2. eapply closed_qual_subst1; eauto. eapply closed_qual_monotone; eauto. rewrite subst1_tenv_length. lia.
  - apply qstp_or_r_sub. apply H2. eapply closed_qual_subst1; eauto. eapply closed_qual_monotone; eauto. rewrite subst1_tenv_length. auto. 
  - eapply qstp_trans; eauto.
Qed.

Lemma subst1_just_fv : forall {x dy},
    just_fv x = {0 |-> dy }ᵈ (just_fv (S x)).
Proof.
  intros. unfold just_fv. simpl. reflexivity.
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
Proof.
  intros. remember (Γ ++ [(Tf, df)]) as Γ'. induction H; intuition.
  - simpl. constructor. eapply closed_qual_subst1'; eauto. rewrite HeqΓ' in H. eauto.
  - apply qstp_refl. eapply closed_qual_subst1'; eauto. constructor. rewrite HeqΓ' in H. eauto.
  - apply qstp_refl. eapply closed_qual_subst1'; eauto. constructor. auto.
  - simpl. constructor. apply H4. eapply closed_qual_subst1'; eauto. rewrite HeqΓ' in H2. eauto.
  - simpl. apply qstp_or_r_sub. apply H4. eapply closed_qual_subst1'; eauto. rewrite HeqΓ' in H2. eauto.
  - simpl. constructor; intuition.
  - apply (@qstp_trans _ _ _ ({0 |-> df' }ᵈ q2)). auto. auto.
    Unshelve. apply (Tf, df).
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
    specialize (IHHS2 Tf df ((T3, d3) :: Γ0)). simpl in IHHS2. intuition. rename H4 into IHHS2.
    erewrite <- open_subst1_ty_comm in IHHS2; eauto. erewrite <- open_subst1_ty_comm in IHHS2; eauto.
    erewrite <- open_subst1_qual_comm in IHHS2; eauto. erewrite <- open_subst1_qual_comm in IHHS2; eauto.
  - econstructor; eauto.
Qed.

Lemma substitution_stp : forall{T1 T2},
    forall {Tf df dx Σ d1 d2 ds} (Γ : tenv),
      (*actually we even don't need this constarin*)
      syntactic_to_set ds = qualifiers.qglb (syntactic_to_set df) (syntactic_to_set dx) ->
      closed_qual 0 (length Γ) (length Σ) ds ->
      stp ([(Tf,ds)]) Σ T1 d1 T2 d2 -> 
      closed_qual 0 0 (length Σ) dx ->
      stp [] Σ ({ 0 |-> dx }ᵀ T1) ({ 0 |-> dx }ᵈ d1) ({ 0 |-> dx }ᵀ T2) ({ 0 |-> dx }ᵈ d2).
Proof.
  intros. replace [(Tf, ds)] with ([] ++ [(Tf, ds)]) in H; auto.
  replace [] with ({0 |-> dx }ᴳ []); auto.
  eapply subst_stp; eauto.
Qed.


Lemma substitution_stp2 : forall{T1 T2},
    forall {Tf df df' dx dx' Σ d1 d2 ds'},
      syntactic_to_set ds' = qualifiers.qglb (syntactic_to_set df') (syntactic_to_set dx') ->
      closed_qual 0 0 (length Σ) ds' ->
      stp ([(Tf, ds')]) Σ T1 d1 T2 d2 ->
      closed_ty 0 0 (length Σ) Tf ->
      qstp [] Σ df df' ->
      qstp [] Σ dx dx' ->
      stp [] Σ ({ 0 |-> dx }ᵀ T1) ({ 0 |-> dx }ᵈ d1) ({ 0 |-> dx }ᵀ T2) ({ 0 |-> dx }ᵈ d2).
Proof.
  (* replace ds' by ds using narrowing_stp, then done *)
  intros. assert (H1' := H1). apply stp_closed in H1'; simpl in H1'; intuition.
  specialize (syntactic_to_set_qstp_exists H H3 H4). intros. destruct H8 as [ds Hds]. destruct Hds.
  assert (stp [(Tf, ds)] Σ T1 d1 T2 d2). {
    eapply narrowing_stp; eauto. apply stp_refl; auto.
  }
  replace ([(Tf, ds)]) with ([] ++ [(Tf, ds)]) in H11 by auto.
  eapply @subst_stp with (df':=dx) in H11; eauto.
  apply qstp_closed in H4; intuition.
Qed.

Lemma subst_filter0 : forall {d φ l} (Σ : senv), 
  closed_qual 0 0 l d -> 
  qstp [] Σ (d ⊕ 0) φ -> 
  qstp [] Σ d  ({ 0 |-> d }ᵈ φ).
Proof.
  intros. induction d; simpl in *; apply qstp_sub_or_inversion in H0; destruct H0. 
  - erewrite subst1_qual_id; eauto. apply qstp_closed in H1; simpl in H1; destruct H1; eauto. 
  - erewrite subst1_qual_id; eauto. apply qstp_closed in H1; simpl in H1; destruct H1; eauto.
  - erewrite subst1_qual_id; eauto. apply qstp_closed in H1; simpl in H1; destruct H1; eauto.
  - erewrite subst1_qual_id; eauto. apply qstp_closed in H1; simpl in H1; destruct H1; eauto.
Qed.

Lemma subst1_just_fv0 : forall {q}, {0 |-> q }ᵈ (just_fv 0) = q.
  intros. simpl. reflexivity. 
Qed.

Lemma subst1_just_fv0' : forall {Γ Σ q}, 
  closed_qual 0 (length Γ) (length Σ) q ->
  eqqual Γ Σ ({0 |-> q }ᵈ (just_fv 0)) (q ⊔ (∅)).
Proof.
  intros. simpl. unfold qlub. constructor; constructor. 
  apply qstp_refl. auto. constructor. apply qstp_refl. auto. constructor. auto.
Qed.


Lemma subst1_mem : forall {x dx df l}, closed_qual 0 0 l dx -> $ (x) ∈ᵥ {0 |-> dx }ᵈ df -> $ (S x) ∈ᵥ df.
Proof.
  intros. induction df; simpl in *; auto.
  2: { intuition. }
  destruct v; simpl in *; auto.
  destruct i; simpl in H0; auto. induction dx; simpl in *; intuition.
  destruct v; inversion H; intuition. 
  1-2: inversion H; subst; intuition.
Qed.


Lemma vtp_closed:
  forall {Σ t T d}, vtp Σ t T d ->
    closed_tm 0 0 (length Σ) t /\
    closed_ty 0 0 (length Σ) T /\
    closed_qual 0 0 (length Σ) d .
Proof.
  intros. induction H; intuition.
  + constructor. apply indexr_var_some' in H1; intuition.
  + constructor.  apply stp_closed in H2. intuition.
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
      { apply s_fun; intuition; eapply sstp_stp_inv; eauto.  }
      assert (stp [] Σ (TFun d0 d7 T0 T5) df1 (TFun d1 d2 T1 T2) d5).
      { apply s_fun; intuition; eapply sstp_stp_inv; eauto.  }
      assert (stp [] Σ (TFun d0 d7 T0 T5) df1 (TFun d3 d4 T3 T4) d6).
      { eapply s_trans; eauto. }
      assert (stp [] Σ T3 d3 T1 d1). { eauto. }
      specialize (@narrowing_stp_gen [] T1 d1 [] Σ (open_ty' ([]: tenv) T5)(openq' ([]:tenv) d7) (open_ty' ([]:tenv) T2) (openq' ([]: tenv) d2)) as narrow.
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
  intros. remember [] as Γ.  induction H0; eauto; subst; try inversion H.
  - (* tabs *) subst. eapply vtp_abs; eauto.
    + apply qstp_closed in H2; destruct H2. auto.
    + eapply stp_refl. inversion H1. subst. intuition.
      apply qstp_refl. inversion H1; auto. 
    + apply qstp_closed in H2; destruct H2. auto.
    + apply stp_refl. inversion H1. subst.
      * simpl in *. unfold open_ty'. unfold open_ty. simpl in *. apply closed_ty_open. eapply closed_ty_monotone; eauto. auto.
      * apply qstp_refl. apply has_type_closed in H3. intuition.
  - (* tloc *) eapply vtp_loc; eauto.
    + apply qstp_closed in H3. intuition. 
    + apply stp_refl. intuition. apply qstp_refl. apply closed_qual_empty.
    + apply stp_refl. intuition. constructor. intuition. 
    + apply qstp_refl. apply just_loc_closed. apply indexr_var_some' in H1. intuition.
  - subst. intuition. eapply vtp_widening; eauto.
  - subst. intuition. eapply vtp_widening; eauto.
  - subst. intuition. eapply vtp_widening; eauto.
Qed.

Lemma vtp_has_type: forall {Σ t T d}, vtp Σ t T d ->  has_type [] d Σ t T d.
Proof.
  intros. induction H.
  - econstructor; eauto. econstructor; eauto. constructor. auto. 
  - assert (has_type [] (just_loc l) Σ (tloc l) (TRef T) (just_loc l)). {
      econstructor; eauto. apply just_loc_closed. apply indexr_var_some' in H1. auto. apply qstp_refl. apply qstp_closed in H4. intuition. }
    eapply weaken_flt with (φ' := d) in H5; intuition. eapply t_sub; eauto.
    constructor; intuition. 
  - specialize (qstp_closed H5) as Hcl. intuition.
    assert (has_type [] df1 Σ (tabs t0) (TFun d1 d2 T1 T2) df1). {
    constructor; eauto. }
    eapply weaken_flt with (φ' := df2) in H9; eauto.
    eapply t_sub; eauto. constructor; intuition.
Qed.

Lemma substitution_gen :
  forall {t Γ φ' Tx dx dx' Σ T d}, 
    qualifiers.qglb (syntactic_to_set dx') (syntactic_to_set φ') = syntactic_to_set dx ->
    forall {φ}, qstp (Γ ++ [(Tx, dx)]) Σ φ φ' ->
      has_type (Γ ++ [(Tx,dx)]) φ Σ t T d -> Substq dx dx' ->
        forall {tx}, vtp Σ tx Tx dx' ->
                        has_type ({ 0 |-> dx' }ᴳ Γ) ({ 0 |-> dx' }ᵈ φ) Σ
                                 ({ 0 |-> tx  }ᵗ t)
                                 ({ 0 |-> dx' }ᵀ T)
                                 ({ 0 |-> dx' }ᵈ d).
Proof. 
  intros t Γ φ' Tx dx dx' Σ T d Hsep φ Hphi HT HSubst tx HTx. specialize (vtp_closed HTx) as Hclx.
  simpl in Hclx. intuition. remember (Γ ++ [(Tx, dx)]) as Γ'.
  generalize dependent Γ. generalize dependent φ'.
  induction HT; intros; subst; pose (φs := {0 |-> dx' }ᵈ φ); replace ({0 |-> dx' }ᵈ φ) with φs in *; auto.
  - simpl. apply t_base; auto. eapply closed_qual_subst1'; eauto.
  - simpl. (bdestruct (x =? 0)).
    + (*x is 0 *) rewrite indexr_skips in H0; simpl; auto; try lia. simpl in H0. subst. simpl in H0.
      inversion H0. subst. erewrite subst1_ty_id; eauto. inversion HSubst; subst.
      * (*subst arg, dx = df ⋒ dx = dx' ⋒ φ *)
        apply vtp_has_type in HTx. eapply weaken'; eauto.
        2: apply qstp_closed in H3; destruct H3; eapply closed_qual_subst1'; eauto. apply (@subst_qstp _ _ _ dx') in H3; simpl in H3; auto.
    + (*x is in Γ0*) assert (Hx: 1 <= x); try lia. destruct x; try lia.
      apply t_var with (d:={0 |-> dx' }ᵈ d). change x with (pred (S x)).
      eapply indexr_subst1; eauto. erewrite subst1_just_fv.
      eapply subst_qstp; eauto.
      eapply closed_ty_subst1; eauto.
      simpl. eapply closed_qual_subst1; eauto.
  - simpl. intuition. rename H6 into IHHT.
    apply t_abs; auto. eapply closed_tm_subst1'; eauto.
    inversion H3. subst. constructor; try eapply closed_ty_subst1'; eauto; eapply closed_qual_subst1'; eauto.
    eapply subst_qstp; eauto.
    (* 1. instantiate the IH *)
    replace (length (Γ0 ++ [(Tx, dx)])) with (S (length Γ0)) in IHHT.
    rewrite subst1_tenv_length. rewrite app_comm_cons in IHHT.
    remember (df ⊔ just_fv (S (length Γ0))) as DF.
    replace ({0 |-> dx' }ᵈ df ⊔ just_fv (length Γ0)) with ({0 |-> dx' }ᵈ DF).
    remember (φ' ⊔ just_fv (S (length Γ0))) as φ''.
    specialize IHHT with (φ' := φ'') (Γ := (T1, d1) :: Γ0).
    (* 2. reason about opening and subst, apply IH *)
    unfold open_tm' in *. unfold open_ty' in *. unfold open_ty in *.
    unfold openq' in *. unfold openq in *.
    rewrite app_length in IHHT. rewrite subst1_tenv_length. simpl in *.
    replace (length Γ0 + 1) with (S (length Γ0)) in IHHT; try lia.
    erewrite <- open_subst1_tm_comm in IHHT; eauto.
    erewrite <- open_subst1_ty_comm in IHHT; eauto.
    erewrite <- open_subst1_qual_comm in IHHT; eauto.
    apply IHHT; auto.
    (* done, prove some leftovers *)

    subst. rewrite syntactic_to_set_qor. simpl. eapply lambda_star_addition.qglb_increase_fresh_equal. auto. apply syntactic_to_set_closed; eauto.

    3: { rewrite app_length. simpl. lia. }
    2: { subst. simpl. auto. }
    subst. unfold qlub, just_fv. apply qstp_sub_or. 
    apply qstp_or_l_sub. replace ((T1, d1) :: Γ0 ++ [(Tx, dx)]) with ([(T1, d1)] ++ Γ0 ++ [(Tx, dx)]) by auto. apply weaken_qstp. eapply qstp_trans; eauto. constructor. simpl. rewrite app_length. simpl. lia.
    apply qstp_or_r_sub. apply qstp_refl. constructor. simpl. rewrite app_length. simpl. lia. apply qstp_closed in Hphi; destruct Hphi. eapply closed_qual_monotone; eauto. simpl. lia. 
  - intuition. rename H12 into IHHT1. rename H11 into IHHT2. simpl.
    replace ({ 0 |-> dx' }ᵈ (openq d1 d2)) with (openq ({ 0 |-> dx' }ᵈ d1) ({ 0 |-> dx' }ᵈ d2)).
    (*separation/overap is preserved after substitution*)
    assert (Hoverlap: syntactic_to_set ({0 |-> dx' }ᵈ ds') = qglb (syntactic_to_set ({0 |-> dx' }ᵈ df')) (syntactic_to_set ({0 |-> dx' }ᵈ d1'))). { (* transition lemmas needed, syntactic_to_set ({0 |-> dx' }ᵈ df) = {0 |-> dx' }ᵈ (syntactic_to_set df) *)
      (* several transition lemmas required
        1. qstp -> qstp / subqual
        2. context transfer (probably just use the lambda_star one) 
        3. saturated transfer ! this should be hard I think
      *)
      specialize (has_type_filter HT1). specialize (has_type_filter HT2).
      symmetry.
      do 3 rewrite syntactic_to_set_subst1_commute. 
      erewrite lambda_star_addition.subst1_preserves_separation_equal; eauto. rewrite H0. auto. 
      apply syntactic_to_set_closed. eapply closed_qual_monotone; eauto.
      assert (length Σ <= length (store_syntactic_to_set Σ)). unfold store_syntactic_to_set; rewrite map_length; auto. eauto.
      
      assert (Hqstp: qstp (Γ0 ++ [(Tx, dx)]) Σ df' φ'). eapply qstp_trans; eauto. apply qstp_syntactic_to_set in Hqstp; inversion Hqstp; subst; auto.
      assert (Hqstp: qstp (Γ0 ++ [(Tx, dx)]) Σ d1' φ'). eapply qstp_trans; eauto. apply qstp_syntactic_to_set in Hqstp; inversion Hqstp; subst; auto.

      replace (ctx_syntactic_to_set (Γ0 ++ [(Tx, dx)])) with ((ctx_syntactic_to_set Γ0) ++ [(ty_syntactic_to_set Tx, syntactic_to_set dx)]) in H9. eauto. rewrite ctx_syntactic_to_set_ext_dist. auto.
      replace (ctx_syntactic_to_set (Γ0 ++ [(Tx, dx)])) with ((ctx_syntactic_to_set Γ0) ++ [(ty_syntactic_to_set Tx, syntactic_to_set dx)]) in H10. eauto. rewrite ctx_syntactic_to_set_ext_dist. auto.
    }
    eapply t_app with (T1:= { 0 |-> dx' }ᵀ T1) (df:=({0 |-> dx' }ᵈ df)) (ds':= {0 |-> dx' }ᵈ ds').

    eauto.  
    eapply IHHT1; eauto. 
    eapply IHHT2; eauto.

    7-8: rewrite ctx_syntactic_to_set_ext_dist in H10; rewrite ctx_syntactic_to_set_ext_dist in H9; rewrite syntactic_to_set_subst1_commute; rewrite ctx_syntactic_to_set_subst1_commute; eapply lambda_star.subst1_saturated; eauto. 

    eapply closed_ty_subst1'; eauto.
    subst φs. unfold openq. rewrite <- @subst1_qual_empty with (dx:=dx'). erewrite <- subst1_open_qual_comm; eauto. eapply subst_qstp; eauto.

    5-6: apply syntactic_to_set_closed; eapply closed_qual_monotone; eauto; unfold store_syntactic_to_set; rewrite map_length; auto.

    1-4: eapply subst_qstp; eauto.

    unfold openq. repeat erewrite <- subst1_open_qual_comm; eauto.
  - erewrite @subst1_qual_id with (q:=(just_loc l)); eauto. simpl. erewrite subst1_ty_id; eauto.
    apply t_loc; auto. 
    subst φs. unfold just_loc in *. 
    eapply closed_qual_subst1; eauto. rewrite subst1_tenv_length. eapply closed_qual_monotone; eauto. rewrite app_length. simpl. lia. 
    replace (&& l) with ({0 |-> dx' }ᵈ (&& l)). 2: auto. eapply subst_qstp; eauto.
    constructor; intuition. 
  - replace ({0 |-> dx' }ᵈ ∅) with (∅) in * by auto.
    replace ({0 |-> dx' }ᵀ (TRef TUnit)) with (TRef TUnit) in * by auto.
    replace ({0 |-> dx' }ᵀ (TUnit)) with (TUnit) in * by auto.
    eapply t_ref. fold subst_tm. eapply IHHT; eauto.
  - simpl. apply t_deref with (d := { 0 |-> dx' }ᵈ d). eapply IHHT; eauto.     
  - replace ({0 |-> dx' }ᵈ ∅) with (∅) in * by auto.
    replace ({0 |-> dx' }ᵀ (TRef TUnit)) with (TRef TUnit) in * by auto.
    replace ({0 |-> dx' }ᵀ (TUnit)) with (TUnit) in * by auto.
    eapply t_assign; eauto.    
  - apply t_sub with (T1:={ 0 |-> dx' }ᵀ T1) (d1:={ 0 |-> dx' }ᵈ d1).
    eapply IHHT; eauto. eapply subst_stp; eauto. subst φs. 
    eapply subst_qstp; eauto.
    Unshelve. all : auto. 
Qed.


Lemma substitution : forall {t df Tx dx Σ T d ds},
    syntactic_to_set ds = qualifiers.qglb (syntactic_to_set df) (syntactic_to_set dx) ->
    has_type [(Tx,ds)] (df ⊔ (just_fv 0)) Σ t T d -> closed_qual 0 0 (length Σ) df ->
            forall {vx}, vtp Σ vx Tx dx ->
                    has_type [] (df ⊔ dx) Σ
                             ({ 0 |-> vx }ᵗ t)
                             ({ 0 |-> dx }ᵀ T)
                             ({ 0 |-> dx }ᵈ d).
Proof.
  intros. subst. specialize (vtp_closed H2) as Hclx. specialize (has_type_closed H0) as Hclt.
  intuition. replace ([(Tx, ds)]) with ([] ++ [(Tx, ds)]) in H; auto.
  remember (df ⊔ (just_fv 0)) as DF.
  assert (Hsepf : qualifiers.qglb (syntactic_to_set dx) (qualifiers.qlub (syntactic_to_set df) (syntactic_to_set (just_fv 0))) = syntactic_to_set ds). {
    rewrite H. apply syntactic_to_set_closed in H8.
    rewrite (@qualifiers.qglb_commute (syntactic_to_set df) (syntactic_to_set dx)). destruct (syntactic_to_set df). destruct (syntactic_to_set dx). simpl.
    do 2 rewrite setfacts.empty_union_right. f_equal.
    inversion H8; subst. apply setfacts.bound_0_empty in H16, H17. subst.
    do 2 rewrite setfacts.inter_empty_left. reflexivity.
  }
  assert (Hrefl : qstp ([] ++ [(Tx, ds)]) Σ DF DF). apply qstp_refl. subst. constructor. eapply closed_qual_monotone; eauto. lia. constructor. auto. subst DF.
  replace (qualifiers.qlub (syntactic_to_set df) (syntactic_to_set $$ 0)) with (syntactic_to_set (qor df $$0)) in Hsepf. 2:{ apply syntactic_to_set_qor. }
  eapply (substitution_gen Hsepf Hrefl) in H0; eauto. simpl in H0. 
  replace ({0 |-> dx }ᵈ df) with (df) in H0. apply H0.
  (*done, prove earlier replacements *)
  erewrite subst1_qual_id; eauto.
Qed.


Lemma substitution2 : forall {t df df' Tx dx dx' Σ T d ds'},
    syntactic_to_set ds' = qualifiers.qglb (syntactic_to_set df') (syntactic_to_set dx') ->
    has_type [(Tx,ds')] (df ⊔ $$0) Σ t T d ->
    qstp [] Σ df df' -> closed_qual 0 0 (length Σ) df' ->
        forall {vx}, vtp Σ vx Tx dx -> 
        qstp [] Σ dx dx' -> closed_qual 0 0 (length Σ) dx' ->
                    has_type [] (df ⊔ dx) Σ
                             ({ 0 |-> vx }ᵗ t)
                             ({ 0 |-> dx }ᵀ T)
                             ({ 0 |-> dx }ᵈ d).
Proof.
  intros. specialize (vtp_closed H3) as Hclx. specialize (has_type_closed H0) as Hclt.
  intuition. replace ([(Tx, ds')]) with ([] ++ [(Tx, ds')]) in H0; auto.
  remember (df ⊔ (just_fv 0)) as DF.

  (* since the constrains posted by the set intersection, we can't use the strategy of qploy substitution2, so we still need to use narrowing *)
  specialize (syntactic_to_set_qstp_exists H H1 H4). intros. destruct H12 as [ds [Hds Hdsqstp]]. 
  apply narrowing with (V:=Tx) (dv:=ds) in H0. 3: apply saturated_empty_tenv. 3: apply qstp_closed in Hdsqstp; intuition. 2: apply stp_refl; auto.

  assert (Hsepf : qualifiers.qglb (syntactic_to_set dx) (qualifiers.qlub (syntactic_to_set df) (syntactic_to_set (just_fv 0))) = syntactic_to_set ds). {
    rewrite Hds. apply syntactic_to_set_closed in H11.
    rewrite (@qualifiers.qglb_commute (syntactic_to_set df) (syntactic_to_set dx)). destruct (syntactic_to_set df). destruct (syntactic_to_set dx). simpl.
    do 2 rewrite setfacts.empty_union_right. f_equal.
    inversion H11; subst. simpl in H20. rewrite <- setfacts.disjoint_glb_lub_eq. fnsetdec. auto.
  }
  assert (Hrefl : qstp ([] ++ [(Tx, ds)]) Σ DF DF). apply qstp_refl. subst. constructor. apply qstp_closed in H1; destruct H1. eapply closed_qual_monotone; eauto. simpl; auto. constructor. auto. subst DF.
  replace (qualifiers.qlub (syntactic_to_set df) (syntactic_to_set $$ 0)) with (syntactic_to_set (qor df $$0)) in Hsepf. 2:{ apply syntactic_to_set_qor. }
  eapply (substitution_gen Hsepf Hrefl) in H0; eauto. simpl in H0. 
  replace ({0 |-> dx }ᵈ df) with (df) in H0. apply H0.
  (*done, prove earlier replacements *)
  apply qstp_closed in H1; destruct H1. erewrite subst1_qual_id; eauto.   
  (* t_app_fresh in qpoly *)
Qed.


Lemma open_qual_mono : forall {Γ Σ d1 d1' d2 k}, 
  qstp Γ Σ d1 d1' -> 
  closed_qual 0 (length Γ) (length Σ) d2 ->  
  qstp Γ Σ ([[ k ~> d1 ]]ᵈ d2) ([[ k ~> d1' ]]ᵈ d2).
Proof.
  intros. pose (He := H). apply qstp_closed in He. destruct He. induction d2; simpl; auto.
  - destruct v. constructor. inversion H0; auto.
    bdestruct (i =? k). auto. apply qstp_refl. auto.
  - inversion H0. intuition. 
    apply qstp_sub_or. apply qstp_or_l_sub. auto. apply qstp_closed in H11; intuition. apply qstp_or_r_sub. auto. apply qstp_closed in H10; intuition.
Qed.

Lemma openq_duplicate_eq : forall {d1 d2 l},
    (((openq (d1 ⋓ (just_loc l)) d2) ⋓ (just_loc l)) = ((openq d1 d2) ⋓ (just_loc l))).
Proof.
  intros. unfold openq. induction d2; simpl; auto. 
  - destruct v; auto.
    destruct i; simpl; auto.
Abort. 

Lemma openq_qstp_or_helper: forall {d1 d2 l Γ Σ},
  closed_qual 0 (length Γ) (length Σ) d1 -> 
  closed_qual 1 (length Γ) (length Σ) d2 ->
  closed_qual 0 (length Γ) (length Σ) &&l ->
  qstp Γ Σ (openq (d1 ⋓ && l) d2) (qor (openq d1 d2) && l).
Proof.
  intros. unfold qlub. unfold openq. induction d2; simpl; auto.
  - apply qstp_or_l_sub. constructor. auto. auto.
  - destruct v. apply qstp_or_l_sub. constructor. inversion H0; auto. auto.
    destruct i; simpl; auto. apply qstp_sub_or. 1,3: apply qstp_or_l_sub; auto. inversion H0; subst. lia.  apply qstp_or_r_sub; auto.
  - apply qstp_or_l_sub; auto. constructor. inversion H0; auto. 
  - inversion H0; subst; intuition. 
    apply qstp_sub_or.
    apply (@qstp_trans _ _ _ (qor ([[0 ~> d1 ]]ᵈ d2_1) && l)); auto.
    apply qstp_sub_or. apply qstp_or_l_sub; auto. apply qstp_or_l_sub; auto. apply qstp_refl. 
    3: apply qstp_or_r_sub; auto. 3: constructor.
    5: apply (@qstp_trans _ _ _ (qor ([[0 ~> d1 ]]ᵈ d2_2) && l)); auto. 5: apply qstp_sub_or. 5: apply qstp_or_l_sub. 5: apply qstp_or_r_sub. 5: apply qstp_refl. 7: auto. 
    7: apply qstp_or_r_sub. 7: auto. 7: constructor.
    all: eapply closed_qual_open'; eauto; eapply closed_qual_monotone; eauto.
Qed.


Lemma openq_closed : forall {a c f l},
    closed_qual 1 f l c -> closed_qual 0 f l a -> closed_qual 0 f l (openq a c).
Proof.
  intros. unfold openq.
  repeat eapply closed_qual_open'; eauto.
Qed.

Lemma freshness : forall {Σ Σ' l b f d1}, 
  disjointq Σ Σ' (just_loc l) -> 
  closed_qual b f (length Σ) d1 -> 
  qualifiers.qglb (syntactic_to_set (just_loc l)) (syntactic_to_set d1) = (syntactic_to_set ∅).
Proof.
  intros. inversion H; subst. discriminate H1. 
  inversion H3. subst.   
  apply syntactic_to_set_closed in H0. inversion H0; subst.
  unfold just_loc. simpl. destruct (syntactic_to_set d1). repeat rewrite inter_empty_left. f_equal. 
  assert (Hcontra : bound ls <= l0). lia. apply setfacts.bound_le_mem_false in Hcontra.
  rewrite <- NatSetFacts.not_mem_iff in Hcontra. fnsetdec.
Qed.

Lemma just_loc_ldom : forall {l} {Γ} {Σ : senv}, l < length Σ -> 
  qstp Γ Σ (just_loc l) (ldom Σ).
Proof.
  intros. unfold ldom. induction Σ; simpl in *. intuition.
  bdestruct (l=?(length Σ)). 
  - apply qstp_or_l_sub. rewrite H0. constructor. simpl; auto. assert (closed_qual 0 0 (length Σ) (ldom Σ)). apply closed_qual_ldom. eapply closed_qual_monotone; eauto. lia. simpl; auto.
  - assert (l < length Σ) by lia. intuition. apply qstp_or_r_sub. replace (a::Σ) with ([a]++Σ) by auto. apply weaken_qstp_store; auto. constructor. simpl; auto.
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
  induction H; intuition; try discriminate. exists t0. intuition.
Qed.

Lemma vtp_qstp : forall {Σ t T d d'},
  vtp Σ t T d ->
  qstp [] Σ d d' ->
  vtp Σ t T d'.
Proof.
  intros. induction H.
  - constructor. apply qstp_closed in H0; intuition. 
  - econstructor; eauto. apply qstp_closed in H0; intuition. eapply qstp_trans; eauto.
  - econstructor; eauto. eapply qstp_closed in H0; intuition. eapply qstp_trans; eauto.
Qed.

Lemma openq_qstp : forall {Γ Σ d1 d2 d},
  closed_qual 1 (length Γ) (length Σ) d ->
  closed_qual 0 (length Γ) (length Σ) d1 ->
  qstp Γ Σ d1 d2 ->
  qstp Γ Σ (openq d1 d) (openq d2 d).
Proof.
  intros. assert (closed_qual 0 (length Γ) (length Σ) (openq d1 d)). apply openq_closed; auto. unfold openq.
  induction d; simpl.
  - constructor; auto.
  - destruct v. 
    + apply qstp_refl; auto.
    + destruct i; simpl. auto. apply qstp_refl; auto.
  - apply qstp_refl; auto.
  - inversion H; subst. 
    assert (closed_qual 0 (length Γ) (length Σ) (openq d1 d3)). apply openq_closed; auto. assert (closed_qual 0 (length Γ) (length Σ) (openq d1 d4)). apply openq_closed; auto.
    intuition. apply qstp_sub_or.
    apply qstp_or_l_sub; auto. apply qstp_closed in H5; intuition.
    apply qstp_or_r_sub; auto. apply qstp_closed in H7; intuition.
Qed.



(* Main results: type soundness & preservation of separation *)

Theorem type_safety: forall {Σ t T d},
    has_type [] (ldom Σ) Σ t T d ->
    value t \/
    forall {σ}, CtxOK [] (ldom Σ) Σ σ ->
    exists t' σ', step t σ t' σ' /\ preserve [] Σ t' T d σ'.
Proof.
  intros Σ t T d H.
  specialize (has_type_closed H) as HX. remember [] as G. remember t as tt. remember T as TT. remember (ldom Σ) as φ.
  revert T t HeqTT Heqtt HeqG Heqφ.
  induction H; try (left; constructor); intros.
  - (* tvar *)  subst. inversion H.
  - (* tapp *) right. subst. intuition.
    apply has_type_closed in H0 as HH. intuition. apply has_type_closed in H1 as HH0. intuition.
    (* t1 *) specialize (H13 (TFun ds' d2 T1 T) t1). intuition.
    (* t2 *) specialize (H15 T1 t2). intuition.
    + (* beta *)
      (* turn has_type to vtp *)
      apply has_type_vtp in H0 as VH; intuition. 
      pose (VHH := VH). inversion VH. subst.
      specialize (has_type_filter H1) as Hflt0.
      apply has_type_vtp in H1 as VH0; intuition. 
      exists (open_tm t2 t0). exists σ. intuition.
      * constructor. intuition.
      * apply (Preserve Σ ∅); auto.  
        apply t_sub with (T1 := T) (d1 := (openq d1 d2)). 2: eapply stp_refl'; eauto. 2: apply qstp_or_l_sub. 2: apply qstp_refl. 3: constructor. 2: auto.
        apply qstp_closed in H38 as H38'; intuition.
        change (length []) with 0 in *. subst.
        assert (HT' : has_type [(T1, ds')] (df ⋓ just_fv 0) Σ (open_tm' ([]:tenv) t0) (open_ty' ([]:tenv) T2) (openq' ([]:tenv) d3)). {
          eapply narrowing; eauto. eapply weaken_flt; eauto. 
          apply qstp_sub_or. apply qstp_or_l_sub. replace ([(T0, d0)]) with ([(T0, d0)] ++ []). apply weaken_qstp. auto. auto.
          2: apply qstp_or_r_sub. 2: constructor; auto. 3: constructor. 1,4: constructor; auto. 1,2: eapply closed_qual_monotone; eauto; lia. 
          apply saturated_empty_tenv. apply stp_closed in H37; intuition.
        }

        specialize (syntactic_to_set_qstp_exists H H5 H4). intros. destruct H27 as [ds [Hds Hdsqstp]].
        apply narrowing_stp with (V:=T1) (dv:=ds) in H39. 2: apply stp_refl; auto.

        eapply @substitution2 with (vx:= t2) (df:=df) in HT' as HT''; eauto; intuition.
        unfold open_tm' in HT''. unfold open_ty' in HT''. unfold openq' in HT''. simpl in HT''. inversion H31; subst.
        unfold open_ty in HT''. unfold openq in HT''.
        erewrite <- open_subst1_tm in HT''; eauto. erewrite <- open_subst1_qual in HT''; eauto. erewrite <- open_subst1_ty in HT''; eauto.
        fold (open_tm t2 t0) in HT''. fold (openq d1' d3) in HT''.
        apply @weaken_flt with (φ':= (ldom Σ)) in HT''; auto; intuition.
        eapply t_sub; eauto.
        rename H39 into Hsub.
        eapply @subst_stp with (Γ := [])(df' := d1) in Hsub; eauto.
        replace (open_ty' ([] : tenv) T) with T in *. (* because T is closed *)
        simpl in Hsub. unfold openq' in Hsub. unfold openq in Hsub. simpl in Hsub.
        erewrite @subst1_ty_id with (T := T) in Hsub; eauto.
        unfold open_ty' in Hsub. unfold open_ty in Hsub.
        erewrite <- open_subst1_ty in Hsub; eauto.
        erewrite <- open_subst1_qual in Hsub; eauto.
        erewrite <- open_subst1_qual in Hsub; eauto.
        all: inversion H32; subst; simpl; eauto.
        unfold open_ty'. unfold open_ty. erewrite (@closed_ty_open_id _ 0); eauto.
        3: apply qstp_closed in H5; intuition. 3: apply qstp_closed in H4; intuition.

        2-3: apply qstp_sub_or. 5: constructor; auto. 1,4: eapply openq_subqual; auto. 
        apply has_type_filter in H0. auto. apply has_type_filter in H1. auto.
    + (* (tabs t) t2 -> (tabs t) t2' *)
      apply has_type_vtp in H0 as VH; intuition.
      apply vtp_canonical_form_lam in VH as HH; intuition.
      pose (HH16 := H16).
      unfold CtxOK in HH16. specialize (H13 σ). intuition.
      destruct H27 as [t2' [σ' HH27]]. exists (tapp t1 t2'). exists σ'. intuition. constructor; intuition.
      destruct H27.  apply (Preserve Σ' d'); intuition.
      inversion H29; subst.
      * assert (H30_alt: has_type [] (ldom Σ') Σ' t2' T1 d1). { apply t_sub with (T1:=T1) (d1:=(qor d1 ∅)). auto. apply stp_refl. eapply closed_ty_monotone; eauto. 2: constructor. 2: apply qstp_refl. 3: constructor. 
        4: apply (@qstp_trans _ _ _ (ldom Σ)); auto. 
        4: apply has_type_filter in H1; eapply qstp_weaken_store in H1; eauto. 4: eapply extends_ldom; auto.  
        2-3: eapply closed_qual_monotone; eauto. all: apply extends_length; auto.
        }
        apply t_sub with (T1:=T) (d1:=(openq (d1) d2)). eapply t_app with (df := df) (ds':=ds'); eauto. 
        eapply weaken_flt. eapply weaken_store; eauto; intuition. apply extends_ldom. all : auto.
        eapply closed_ty_monotone; eauto. apply extends_length. intuition.
        apply (@qstp_trans _ _ _ (ldom Σ)); auto. eapply qstp_weaken_store; eauto. apply extends_ldom; auto.
        
        1-2: eapply weaken_qstp_store_ext; eauto.
        1-2: eapply (@qstp_trans _ _ _ (ldom Σ)). 1,3: eapply weaken_qstp_store_ext; eauto. 1,2: apply extends_ldom; auto.
        1,2: eapply lambda_star.weaken_store_saturated; eauto. 
        1,2: apply store_syntactic_to_set_extends; auto.

        apply stp_refl. eapply closed_ty_monotone; eauto; apply extends_length; auto.
        apply qstp_or_l_sub. apply qstp_refl. apply openq_closed.
        3: constructor. 3: apply qstp_sub_or.
        inversion H18; intuition; eapply closed_qual_monotone; eauto; apply extends_length; auto.
        3: constructor. 2: apply openq_subqual. 4: auto. 2,3: apply (@qstp_trans _ _ _ (ldom Σ)). 3,5: apply extends_ldom; auto.
        eapply closed_qual_monotone; eauto; apply extends_length; auto.
        apply has_type_filter in H1. all: eapply weaken_qstp_store_ext; eauto.
      * specialize (has_type_closed H0). specialize (has_type_closed H30). intuition. inversion H38; subst. 
        apply t_sub with (T1 := T) (d1 := (openq (d1 ⋓ (just_loc l)) d2)).
        -- eapply t_app with (T1 := T1) (df:=df) (ds':=ds') (d1':=(d1' ⋓ && l)) (df':=df'); eauto.  

           rewrite H. rewrite syntactic_to_set_qor. replace ((syntactic_to_set && l)) with (qualifiers.just_loc l).  
           eapply lambda_star.qqcap_fresh_r; eauto. 
           1-2: apply syntactic_to_set_closed; eauto. apply qstp_closed in H5; destruct H5; eauto. apply qstp_closed in H6; destruct H6; eauto. auto. 

           eapply weaken_flt. eapply weaken_store; eauto.
           apply extends_ldom; auto. simpl. auto.
           simpl. eapply closed_ty_monotone in H2; eauto. apply extends_length; auto.
           apply (@qstp_trans _ _ _ (ldom Σ)); eauto. eapply weaken_qstp_store_ext; eauto. apply extends_ldom; auto.

           apply qstp_sub_or. apply qstp_or_l_sub. 3: apply qstp_or_r_sub. 3: apply qstp_refl. 2-3: inversion H40; auto. 
           4: apply qstp_sub_or. 5: apply just_loc_ldom; auto. 
           2: apply qstp_closed in H4; destruct H4; eapply closed_qual_monotone; eauto; apply extends_length; auto.
           1-2: eapply weaken_qstp_store_ext; eauto.
           1,2: apply (@qstp_trans _ _ _ (ldom Σ)). 1,3: eapply weaken_qstp_store_ext; eauto. 1,2: apply extends_ldom; auto.
           
           simpl. apply lambda_star.saturated_qqplus. 2: eapply lambda_star.saturated_just_loc. 
           1-2: eapply lambda_star.weaken_store_saturated; eauto.
           1-2: apply store_syntactic_to_set_extends; auto.
           
        -- apply stp_refl. simpl. eapply closed_ty_monotone in H2;  eauto. apply extends_length. auto.
           apply openq_qstp_or_helper.
           3: inversion H40; auto.
           all: eapply closed_qual_monotone; eauto. 1-2: apply extends_length; auto. 
        -- apply has_type_filter in H1. apply qstp_sub_or. apply openq_subqual. 3: apply just_loc_ldom; auto. 
           1,2: apply (@qstp_trans _ _ _ (ldom Σ)). 2,4: apply extends_ldom; auto.
           all: eapply qstp_weaken_store; eauto.
    + (* t t2 -> t' t2 *)
      apply has_type_closed in H1 as Hcl. intuition.
      specialize (H24 σ H16). destruct H24 as [t1' [σ' HH24]]. exists (tapp t1' t2). exists σ'. intuition. apply step_c_app_l. intuition.
      destruct H28. apply (Preserve Σ' d'); intuition. inversion H31; subst.
      * assert (H32_alt: has_type [] (ldom Σ') Σ' t1' (TFun ds' d2 T1 T) df). {
         apply t_sub with (T1:=TFun ds' d2 T1 T) (d1:=(qor df ∅)). auto. apply stp_refl. eapply closed_ty_monotone; eauto. 2: constructor. 2: apply qstp_refl. 3: constructor. 
         4: apply (@qstp_trans _ _ _ (ldom Σ)); auto.
         4: apply has_type_filter in H0; eapply qstp_weaken_store in H0; eauto. 4: eapply extends_ldom; auto.  
         2-3: eapply closed_qual_monotone; eauto. all: apply extends_length; auto.
        } 
        apply t_sub with (T1:=T) (d1:=(openq (d1) d2)). eapply t_app with (df := df) (ds':=ds') (df':=df'); eauto.
        eapply weaken_flt. eapply weaken_store; eauto. apply extends_ldom. auto. simpl. auto.
        eapply closed_ty_monotone; eauto. apply extends_length. auto.

        apply (@qstp_trans _ _ _ (ldom Σ)); auto. eapply qstp_weaken_store; eauto. apply extends_ldom; auto.

        3-4: apply (@qstp_trans _ _ _ (ldom Σ)). 4,6: apply extends_ldom; auto.
        1-4: eapply qstp_weaken_store; eauto.

        1,2: eapply lambda_star.weaken_store_saturated; eauto. 
        1,2: apply store_syntactic_to_set_extends; auto.

        apply stp_refl. eapply closed_ty_monotone; eauto. apply extends_length. intuition. 
        apply qstp_or_l_sub. apply qstp_refl. apply openq_closed.
        3: constructor. 3: apply qstp_sub_or.
        inversion H18; intuition; eapply closed_qual_monotone; eauto; apply extends_length; auto.
        3: constructor. 2: apply openq_subqual. 4: auto. 2,3: apply (@qstp_trans _ _ _ (ldom Σ)). 3,5: apply extends_ldom; auto.
        eapply closed_qual_monotone; eauto; apply extends_length; auto.
        apply has_type_filter in H1. all: eapply weaken_qstp_store_ext; eauto.
      * (* rewrite <- openq_u_distribute1. *)
        eapply t_sub with (T1 := T)(d1 := (openq d1 d2)).
        -- eapply t_app with (df:=(df ⋓ just_loc l)) (df':=(df' ⋓ just_loc l)) (d1':=d1'); eauto. 
           rewrite syntactic_to_set_qor. replace (syntactic_to_set && l) with (qualifiers.just_loc l) by auto. erewrite <- qqcap_fresh_l; eauto; eapply syntactic_to_set_closed. 
           apply qstp_closed in H5; destruct H5; eauto. apply qstp_closed in H4; destruct H4; eauto.
           eapply weaken_flt. eapply weaken_store. eauto. auto. apply extends_ldom; auto.
           auto. simpl. eapply closed_ty_monotone; eauto. apply extends_length; auto.
           eapply (@qstp_trans _ _ _ (ldom Σ)); eauto. 2: apply extends_ldom; auto. eapply weaken_qstp_store_ext; eauto.

           2: apply qstp_sub_or. 2: apply qstp_or_l_sub. 4: apply qstp_or_r_sub. 4: apply qstp_refl. 7: constructor. 8: apply just_loc_ldom. 3,4: constructor. 3,4,8: auto.
           3: apply qstp_closed in H5; destruct H5; eapply closed_qual_monotone; eauto; apply extends_length; auto.
           3-4: apply (@qstp_trans _ _ _ (ldom Σ)). 4,6: apply extends_ldom; auto.
           1-4: eapply qstp_weaken_store; eauto. 

           2: apply lambda_star.saturated_qqplus. 3: apply lambda_star.saturated_just_loc.
           1-2: eapply lambda_star.weaken_store_saturated; eauto.
           1-2: apply store_syntactic_to_set_extends; auto.
        -- apply stp_refl. simpl. eapply closed_ty_monotone; eauto. lia.
           constructor. apply qstp_refl. eapply closed_qual_monotone; eauto; apply extends_length; auto.
           constructor; auto.
        -- apply has_type_filter in H1. 
           apply qstp_sub_or. 
           apply openq_subqual. 1,2: apply (@qstp_trans _ _ _ (ldom Σ)). 2,4: apply extends_ldom; auto. 1,2: eapply weaken_qstp_store_ext; eauto.
           apply just_loc_ldom; auto.
  - (* t_ref *) subst. intuition. specialize (has_type_closed H) as HH. intuition. specialize (H3 TUnit t0). intuition.
    + right. intros.
      exists (tloc (length (σ))). exists (t0 :: σ). intuition.
      econstructor; eauto. apply (Preserve (TUnit :: Σ) (just_loc (length σ))). apply extends_cons. eapply CtxOK_weaken_flt.
      apply CtxOK_ext; auto. apply H3.
      pose (HV := H). apply has_type_vtp in HV; intuition. inversion HV; subst. constructor. auto.
      simpl. unfold ldom. unfold dom_l; simpl; fold dom_l. constructor. constructor; simpl; auto. eapply closed_qual_monotone; eauto. 
      unfold ldom. unfold dom_l; simpl; fold dom_l. apply qstp_or_r_sub. apply qstp_refl. eapply closed_qual_monotone; eauto; simpl; auto. constructor; simpl; auto.
      apply (disj_loc (length σ)); auto.
      1,2: unfold CtxOK in H3; simpl; intuition.
      apply t_sub with (T1:=(TRef TUnit)) (d1:=&&(length σ)).
      eapply t_loc; eauto. inversion H3. rewrite <- H10.
      apply indexr_head. simpl. intuition; try fnsetdec.
      unfold ldom. simpl. inversion H3. rewrite H10. unfold just_loc. apply qstp_or_l_sub. apply qstp_refl. 
      constructor; simpl. rewrite H10; auto. rewrite <- H10. eapply closed_qual_monotone; eauto; simpl; auto.
      apply stp_refl; auto. apply qstp_or_r_sub. apply qstp_refl. 1-2: auto. inversion H3; constructor; simpl; rewrite H10; auto.
      apply qstp_sub_or. constructor. unfold ldom. unfold dom_l; simpl; fold dom_l. constructor. constructor; auto. eapply closed_qual_monotone; eauto; simpl; auto. 
      unfold ldom. unfold dom_l; simpl; fold dom_l. inversion H3. apply qstp_or_l_sub. rewrite H10; constructor. simpl. rewrite H10; auto. eapply closed_qual_monotone; eauto; simpl; auto.
    + right. intros. specialize (H8 σ H3). destruct H8 as [t' [σ' HH8]]. exists (tref t'). exists σ'. intuition. econstructor; eauto.
      destruct H10. apply (Preserve Σ' ∅); intuition.
      apply t_sub with (T1:=TRef TUnit) (d1:=∅). eapply t_ref; eauto.
      apply stp_refl; auto. constructor; auto. constructor; auto. constructor; constructor; auto.
  - (* t_deref *) subst. intuition. specialize (has_type_closed H) as HH. intuition. specialize (H3 (TRef T0) t0). intuition.
    * right. intros. pose (HV := H). apply has_type_vtp in HV; intuition.
      specialize (vtp_canonical_form_loc HV) as Hcan. intuition. destruct H10 as [l HH10]. subst.
      pose (HHV := HV). inversion HHV. subst.  pose (HH3 := H3). destruct HH3. subst.
      pose (HH14 := H14). apply indexr_var_some' in HH14. rewrite H10 in HH14. apply indexr_var_some in HH14.
      destruct HH14 as [v HHH14].  exists v. exists σ. intuition. apply step_deref; intuition.
      apply (Preserve Σ ∅); intuition.
      apply t_sub with (T1 := T) (d1:= ∅); auto.
      specialize (H11 l v T). intuition.
      replace Σ with (Σ ++ []); intuition. eapply weaken_stp_store. econstructor; eauto. apply stp_refl.
      apply stp_closed in H15; intuition. constructor; constructor; auto. constructor; constructor; auto. 
    * right. intros. specialize (H8 σ H3).
      destruct H8 as [t' [σ' HH8]]. exists (tderef t'). exists σ'. intuition. constructor; auto.
      destruct H10. apply (Preserve Σ' ∅); intuition.
      apply t_sub with (T1 := T0) (d1:= ∅); auto.
      eapply t_deref; eauto. apply stp_refl.
      inversion H6; subst; intuition. eapply closed_ty_monotone; eauto; lia. constructor; constructor; auto. constructor; constructor; auto.
  - (* t_assign *) subst. intuition. rename H into Ht1. rename H0 into Ht2. intuition.
    apply has_type_closed in Ht1 as Ht1C. intuition.
    apply has_type_closed in Ht2 as Ht2C. intuition.
    specialize (H4 (TRef TUnit) t1). intuition.
    specialize (H6 TUnit t2). intuition.
    + (* both t1 and t2 are value *)
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
      constructor; auto. 
      apply t_sub with (T1:=TUnit) (d1:=∅). constructor; auto.
      apply stp_refl; auto. constructor; constructor; auto. constructor; constructor; auto.
    + (* t1 value, t2 steps *)
      right. intros. specialize (H4 σ H6). destruct H4 as [t' [σ' H4']].
      exists (tassign t1 t'). exists σ'. intuition. econstructor; eauto.
      pose (HV := Ht1). apply has_type_vtp in HV; intuition. inversion HV; subst.
      destruct H14. apply (Preserve Σ' ∅); eauto.
      apply t_sub with (T1:=TUnit) (d1:=∅). 
      eapply t_assign; eauto.
      assert (qstp [] Σ' (ldom Σ) (ldom Σ')). apply extends_ldom. auto.
      eapply weaken_store in Ht1; eauto. eapply weaken_flt in Ht1; eauto.
      apply stp_refl; auto. constructor; constructor; auto. constructor; constructor; auto.
    + (* t1 steps *)
      right. intros. specialize (H12 σ H4). destruct H12 as [t' [σ' H12']].
      exists (tassign t' t2). exists σ'. intuition. econstructor; eauto.
      destruct H14. apply (Preserve Σ' ∅); eauto. 
      apply t_sub with (T1:=TUnit) (d1:=∅).
      eapply t_assign; eauto. eapply weaken_store in Ht2; eauto. eapply weaken_flt; eauto. apply extends_ldom; auto.
      apply stp_refl; auto. constructor; constructor; auto. constructor; constructor; auto.
  - (* t_sub *) subst. intuition. specialize (stp_closed H0) as H00. intuition.
    specialize (H5 T1 t0). intuition. right.
    intros. specialize (H10 σ H5). destruct H10 as [t' [σ' HH9]]. exists t'. exists σ'. intuition.
    destruct H12. apply (Preserve Σ' d'); intuition. eapply t_sub; eauto. apply stp_scale_qqplus.
    eapply weaken_stp_store_ext; eauto. inversion H14; subst; intuition; constructor; intuition; try rewrite bound_singleton; try rewrite bound_empty; try lia; auto. 
    constructor. apply (@qstp_trans _ _ _ (ldom Σ)). eapply weaken_qstp_store_ext; eauto. apply extends_ldom; auto.
    inversion H14; subst. constructor; auto. apply just_loc_ldom; auto.
Qed.

Lemma step_deterministic:  deterministic step.
Proof.
  unfold deterministic. intros t t1 t2 σ σ1 σ2 Hstep1 Hstep2. generalize dependent σ2. generalize dependent t2.
  induction Hstep1; intros.
  - assert (step (tapp (tabs t0) v) σ (open_tm v t0) σ). { constructor; intuition. }
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
  has_type [] (ldom Σ) Σ t2 T2 q2 -> 
    qualifiers.qglb (syntactic_to_set q1) (syntactic_to_set q2) = (syntactic_to_set ∅) ->
    forall{σ}, CtxOK [] (ldom Σ) Σ σ ->
      forall {t1' σ'}, step t1 σ t1' σ' ->
      forall {t2' σ''}, step t2 σ' t2' σ'' -> separate Σ t1' T1 t2' T2.
Proof.
  intros Σ t1 T1 q1 t2 T2 q2 HT1 HT2 Hsep σ HOK t1' σ' Hstep1 t2' σ'' Hstep2.
  (* execute preservation in sequence *)
  specialize (preservation HT1 HOK Hstep1) as P1. destruct P1 as [Σ' d1 Hext1 HOK' Hdisj1 HT1'].
  assert (HT2': has_type [] (ldom Σ') Σ' t2 T2 q2). {
    eapply weaken_flt. eapply weaken_store. eauto. auto. apply extends_ldom; auto. auto.
  }
  specialize (preservation HT2' HOK' Hstep2) as P2. destruct P2 as [Σ'' d2 Hext2 HOK'' Hdisj2 HT2''].
  apply (Separate Σ' Σ'' (q1 ⋓ d1) (q2 ⋓ d2) (syntactic_to_set (q1 ⋓ d1)) (syntactic_to_set (q2 ⋓ d2)) Hext1 Hext2 HT1' HT2'').
  auto. auto.
  (* now we just need to show that the disjointness is preserved. this is intuitively true from the disjointness
     of the heap effects d1 and d2. *)
  simpl in Hsep.
  inversion Hdisj1; inversion Hdisj2; subst. 
  1-4 : repeat rewrite syntactic_to_set_qor; repeat rewrite qqplus_qbot_right_neutral; auto.
  - rewrite Hsep. auto. 
  - rewrite qualifiers.qglb_qlub_dist_l. rewrite (@qualifiers.qglb_commute (syntactic_to_set q1) (syntactic_to_set && l)). erewrite freshness; eauto.
    rewrite qlub_empty_right. rewrite Hsep. auto. apply has_type_closed in HT1. intuition. eapply closed_qual_monotone; eauto.
    apply extends_length. auto.
  - rewrite qglb_qlub_dist_r. erewrite freshness; eauto. rewrite qlub_empty_right. rewrite Hsep. auto.
    apply has_type_closed in HT2. intuition. eapply closed_qual_monotone; eauto.
  - rewrite qglb_qlub_dist_l. rewrite qglb_qlub_dist_r. rewrite qglb_qlub_dist_r.
    erewrite freshness; eauto. rewrite (@qglb_commute (syntactic_to_set && l) (syntactic_to_set && l0)).
    erewrite @freshness with (Σ := Σ'); eauto. repeat rewrite qlub_empty_right.
    rewrite (@qglb_commute (syntactic_to_set q1) (syntactic_to_set && l0)). erewrite freshness; eauto. rewrite qlub_empty_right. rewrite Hsep. auto.
    apply has_type_closed in HT1. 3 : apply has_type_closed in HT2. 1,3: intuition; eapply closed_qual_monotone; eauto;
    apply extends_length; auto. apply just_loc_closed. auto.
    Unshelve. all : auto.
Qed.
