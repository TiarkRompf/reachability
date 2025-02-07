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
| TSRef : qual -> ty -> ty (* TSRef q T = ux.Ref[T^(q,x)] *)
| TInt  : ty
| TBool : ty
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
| tsref   : tm  -> tm
| tderef  : tm  -> tm
| tassign : tm  -> tm -> tm
| tnat    : nat -> tm
| tsucc   : tm -> tm
| tmul    : tm -> tm -> tm
| tpred   : tm -> tm
| tiszero : tm -> tm
| tbool   : bool -> tm
| tif     : tm -> tm -> tm -> tm
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
  | tsref   t       => tsref   (open_rec_tm k u t)
  | tderef  t       => tderef  (open_rec_tm k u t)
  | tassign t1 t2   => tassign (open_rec_tm k u t1) (open_rec_tm k u t2)
  | tnat c          => tnat c
  | tsucc t         => tsucc (open_rec_tm k u t)
  | tmul t1 t2      => tmul (open_rec_tm k u t1) (open_rec_tm k u t2)
  | tpred t         => tpred (open_rec_tm k u t)
  | tiszero t       => tiszero (open_rec_tm k u t)
  | tbool c         => tbool c
  | tif t1 t2 t3    => tif (open_rec_tm k u t1) (open_rec_tm k u t2) (open_rec_tm k u t3)
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
  | TSRef d T         => TSRef (open_qual (S k) d' d) (open_rec_ty k U d' T)
      (* currently does not support μx.Ref[TVar x]. *)
  | TInt              => TInt
  | TBool             => TBool
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
  | TSRef _ T       => S (ty_size T)
  | TInt            => 0
  | TBool           => 0
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
  | tsref   t      => tsref   (splice n t)
  | tderef  t      => tderef  (splice n t)
  | tassign t1 t2  => tassign (splice n t1) (splice n t2)
  | tnat c          => tnat c
  | tsucc t         => tsucc (splice n t)
  | tmul t1 t2      => tmul (splice n t1) (splice n t2)
  | tpred t         => tpred (splice n t)
  | tiszero t       => tiszero (splice n t)
  | tbool c         => tbool c
  | tif t1 t2 t3    => tif (splice n t1) (splice n t2) (splice n t3)
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
  | TSRef d1 T       => TSRef (splice_qual n d1) (splice_ty n T)
  | TInt             => TInt
  | TBool            => TBool
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
  | TSRef d1 T       => TSRef (unsplice_qual n d1) (unsplice_ty n T)
  | TInt             => TInt
  | TBool            => TBool
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
| cl_tsref:  forall b f l tm,
    closed_tm b f l tm ->
    closed_tm b f l (tsref tm)
| cl_tderef:  forall b f l tm,
    closed_tm b f l tm ->
    closed_tm b f l (tderef tm)
| cl_tassign:  forall b f l tm1 tm2,
    closed_tm b f l tm1 ->
    closed_tm b f l tm2 ->
    closed_tm b f l (tassign tm1 tm2)
| cl_tnat :   forall b f l c,
    closed_tm b f l (tnat c)
| cl_tsucc : forall b f l t,
    closed_tm b f l t ->
    closed_tm b f l (tsucc t)
| cl_tmul : forall b f l t1 t2,
    closed_tm b f l t1 ->
    closed_tm b f l t2 ->
    closed_tm b f l (tmul t1 t2)
| cl_tpred : forall b f l t,
    closed_tm b f l t ->
    closed_tm b f l (tpred t)
| cl_tiszero : forall b f l t,
    closed_tm b f l t ->
    closed_tm b f l (tiszero t)
| cl_tbool : forall b f l c,
    closed_tm b f l (tbool c)
| cl_tif : forall b f l t1 t2 t3,
    closed_tm b f l t1 ->
    closed_tm b f l t2 ->
    closed_tm b f l t3 ->
    closed_tm b f l (tif t1 t2 t3)
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
| cl_TSRef : forall b f l T q,
    closed_ty b f l T ->
    closed_Qual (S b) f l q ↑ ->
    closed_ty b f l (TSRef q T)
| cl_TFun : forall b f l d1 d2 T1 T2,
    closed_Qual b f l d1 ↑ ->
    closed_Qual (S (S b)) f l d2 ↑ ->
    closed_ty b f l T1 ->
    closed_ty (S (S b)) f l T2 ->
    closed_ty b f l (TFun d1 d2 T1 T2)
| cl_TInt : forall b f l,
    closed_ty b f l TInt
| cl_TBool : forall b f l,
    closed_ty b f l TBool
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
  | TSRef d1 T       => qfvs d1 n || tfvs T n
  | _                => false
  end.

Fixpoint Tfvs (T : ty) (n : nat) {struct T} : Prop :=
  match T with
  | TVar (varF i)    => i = n
  | TAll d1 d2 T1 T2 => qfvs d1↑ n \/ qfvs d2↑ n \/ Tfvs T1 n \/ Tfvs T2 n
  | TFun d1 d2 T1 T2 => qfvs d1↑ n \/ qfvs d2↑ n \/ Tfvs T1 n \/ Tfvs T2 n
  | TRef d1 T        => qfvs d1↑ n \/ Tfvs T n
  | TSRef d1 T       => qfvs d1↑ n \/ Tfvs T n
  | _                => False
  end.

Lemma tfvs_reflect : forall {T n}, reflect (Tfvs T n) (tfvs T n).
intros. induction T; simpl; intuition. 
- destruct v; intuition.
- ndestruct (qfvs q n); ndestruct (qfvs q0 n); destruct (tfvs T1 n); destruct (tfvs T2 n); intuition. all: inversion IHT1; inversion IHT2; intuition. apply iff_reflect. intuition.
- ndestruct (qfvs q n); ndestruct (qfvs q0 n); destruct (tfvs T1 n); destruct (tfvs T2 n); intuition. all: inversion IHT1; inversion IHT2; intuition. apply iff_reflect. intuition.
- ndestruct (qfvs q n); destruct (tfvs T n); intuition. all: inversion IHT; intuition. apply iff_reflect. intuition.
- ndestruct (qfvs q n); destruct (tfvs T n); intuition. all: inversion IHT; intuition. apply iff_reflect. intuition.
Qed.

(**********
*  tbvs  *
**********)

Fixpoint tbvs (T : ty) (n : nat) {struct T} : bool :=
  match T with
  | TVar (varB i)    => i =? n
  | TAll d1 d2 T1 T2 => qbvs d1 n || qbvs d2 (S (S n)) || tbvs T1 n || tbvs T2 (S (S n))
  | TFun d1 d2 T1 T2 => qbvs d1 n || qbvs d2 (S (S n)) || tbvs T1 n || tbvs T2 (S (S n))
  | TRef d1 T        => qbvs d1 n || tbvs T n
  | TSRef d1 T       => qbvs d1 (S n) || tbvs T n
  | _                => false
  end.

Fixpoint Tbvs (T : ty) (n : nat) {struct T} : Prop :=
  match T with
  | TVar (varB i)    => i = n
  | TAll d1 d2 T1 T2 => qbvs d1↑ n \/ qbvs d2↑ (S (S n)) \/ Tbvs T1 n \/ Tbvs T2 (S (S n))
  | TFun d1 d2 T1 T2 => qbvs d1↑ n \/ qbvs d2↑ (S (S n)) \/ Tbvs T1 n \/ Tbvs T2 (S (S n))
  | TRef d1 T        => qbvs d1↑ n \/ Tbvs T n
  | TSRef d1 T       => qbvs d1↑ (S n) \/ Tbvs T n
  | _                => False
  end.

Lemma tbvs_reflect : forall {T n}, reflect (Tbvs T n) (tbvs T n).
intros. generalize dependent n. induction T; simpl; intuition. 
- destruct v; intuition.
- specialize (IHT1 n). specialize (IHT2 (S (S n))). ndestruct (qbvs q n); ndestruct (qbvs q0 (S (S n))); destruct (tbvs T1 n); destruct (tbvs T2 (S (S n))); intuition. all: inversion IHT1; inversion IHT2; intuition. apply iff_reflect. intuition.
- specialize (IHT1 n). specialize (IHT2 (S (S n))). ndestruct (qbvs q n); ndestruct (qbvs q0 (S (S n))); destruct (tbvs T1 n); destruct (tbvs T2 (S (S n))); intuition. all: inversion IHT1; inversion IHT2; intuition. apply iff_reflect. intuition.
- specialize (IHT n). ndestruct (qbvs q n); destruct (tbvs T n); intuition. all: inversion IHT; intuition. apply iff_reflect. intuition.
- specialize (IHT n). ndestruct (qbvs q (S n)); destruct (tbvs T n); intuition. all: inversion IHT; intuition. apply iff_reflect. intuition.
Qed.
