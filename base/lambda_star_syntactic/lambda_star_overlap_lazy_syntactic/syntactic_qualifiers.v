Require Export Arith.EqNat.
Require Export Arith.Le.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Program.Equality.
Require Import Coq.Lists.List.
Require Import Psatz. (* for lia *)
Require Import Coq.Arith.Compare_dec.
Import ListNotations.

Require Import vars.
Require Import env.


(** This syntactic qualifier definition don't contain qand.
  We throw all intersection related operations by tansfering to set-based qualifiers and use set-intersection instead
*)
Inductive qual : Type :=
| qempty  : qual 
| qvar    : var -> qual 
| qloc    : loc -> qual 
| qor     : qual -> qual -> qual
.

Coercion qvar : var >-> qual.



Fixpoint qmem (v : var + loc) (d : qual) : Prop :=
  match d with 
  | qempty => False
  | qvar (varB x) => match v with 
                    | inl (varF i) => False
                    | inl (varB i) => x = i 
                    | inr l => False
                    end
  | qvar (varF x) => match v with 
                    | inl (varF i) => x = i
                    | inl (varB i) => False
                    | inr l => False 
                    end
  | qloc x => match v with 
              | inl (varF i) => False
              | inl (varB i) => False
              | inr l => x = l 
              end
  | qor q1 q2 => (qmem v q1) \/ (qmem v q2)
  end.


Definition just_fv (x : id) : qual := qvar (varF x).
Definition just_bv (x : id) : qual := qvar (varB x).
Definition just_loc (l : loc) : qual := qloc l.




Inductive closed_qual : nat -> nat -> nat -> qual -> Prop :=
| closed_qempty : forall b f l, closed_qual b f l qempty
| closed_qvar_f : forall b f l x,
    x < f ->
    closed_qual b f l $x
| closed_qvar_b : forall b f l x,
    x < b ->
    closed_qual b f l #x
| closed_qloc : forall b f l x,
    x < l ->
    closed_qual b f l (qloc x)
| closed_qor : forall b f l q1 q2,
    closed_qual b f l q1 ->
    closed_qual b f l q2 ->
    closed_qual b f l (qor q1 q2)
.


(* post the type definition here *)
Inductive ty : Type :=
| TUnit : ty
| TFun  : qual -> qual -> ty -> ty -> ty
| TRef  : ty -> ty
.

Definition tenv := list (ty * qual).
Definition senv := list ty. (* Sigma store typing *)


Inductive tm : Type :=
| tunit   : tm
| tvar    : var -> tm
| tabs    : tm  -> tm (* convention: #0: self-ref #1: argument *)
| tapp    : tm  -> tm -> tm
| tloc    : loc -> tm
| tref    : tm  -> tm
| tderef  : tm  -> tm
| tassign : tm  -> tm -> tm
.

Notation "& l" := (tloc l) (at level 0).
Notation "! t" := (tderef t) (at level 0).
Coercion tvar : var >-> tm. (* lightens the notation of term variables *)


Inductive qstp : tenv -> senv -> qual -> qual -> Prop :=
| qstp_empty : forall Γ Σ q,
    closed_qual 0 (length Γ) (length Σ) q ->
    qstp Γ Σ (qempty) q 
| qstp_varF_refl: forall Γ Σ x,
    x < (length Γ) ->
    qstp Γ Σ $x $x
| qstp_loc_refl : forall Γ Σ x,
    x < (length Σ) ->
    qstp Γ Σ (qloc x) (qloc x)
| qstp_or_l_sub : forall Γ Σ q1 q2 q3,
    qstp Γ Σ q1 q2 ->
    closed_qual 0 (length Γ) (length Σ) q3 ->
    qstp Γ Σ q1 (qor q2 q3)
| qstp_or_r_sub : forall Γ Σ q1 q2 q3,
    qstp Γ Σ q1 q2 ->
    closed_qual 0 (length Γ) (length Σ) q3 ->
    qstp Γ Σ q1 (qor q3 q2)
| qstp_sub_or : forall Γ Σ q1 q2 q3,
    qstp Γ Σ q1 q3 ->
    qstp Γ Σ q2 q3 ->
    qstp Γ Σ (qor q1 q2) q3
| qstp_trans : forall Γ Σ q1 q2 q3, 
    qstp Γ Σ q1 q2 -> 
    qstp Γ Σ q2 q3 ->
    qstp Γ Σ q1 q3
.


#[global] Hint Constructors qstp : dsub.


(* equality
  use subqual relation to define the equality, so it will be an inductive definition *)
Inductive eqqual Γ Σ q1 q2 : Prop :=
| eqq:  qstp Γ Σ q1 q2 ->
        qstp Γ Σ q2 q1 ->
        eqqual Γ Σ q1 q2
.


(* lub, don't have glb because don't have qand *)
Definition qlub (d1 d2 : qual) : qual := qor d1 d2.



(* qplus 
    qplus can also be defined in a same way, or simpl version *)
Definition qplus (d : qual) (x : id) : qual := qor d (just_fv x).



Fixpoint splice_qual (n : nat) (d : qual) : qual := 
  match d with 
  | qempty => qempty 
  | qvar (varF i) => 
    if le_lt_dec n i then qvar (varF (S i)) 
    else qvar (varF i)
  | qvar (varB i) => qvar (varB i)
  | qloc l => qloc l 
  | qor q1 q2 => qor (splice_qual n q1) (splice_qual n q2)
  end.


Fixpoint open_qual (k : nat) (d' : qual) (d : qual) : qual :=
  match d with 
  | qempty      => qempty 
  | qvar ($ i)  => qvar ($ i)
  | qvar (# i)  => (*like subst_q, replace in-place*)
      if i =? k then d' else qvar (# i)
  | qloc l      => qloc l 
  | qor q1 q2   => qor (open_qual k d' q1) (open_qual k d' q2)
  end
.

(* Notation "[[ k ~> d' ]]ᵈ d" := (open_qual k d' d) (at level 10). *)


Definition openq (u d : qual) : qual := open_qual 0 u d.
Definition openq' {A} (env : list A) d :=
  openq (just_fv (length env)) d.


Fixpoint qual_size (q : qual) : nat :=
  match q with
  | qempty    => 0
  | qvar x    => 0
  | qloc x    => 0
  | qor  x x0 => S (qual_size x + qual_size x0)
  end
.

Fixpoint dom_l (n : nat) : qual :=
  match n with 
  | 0 => qempty 
  | S a => qor (qloc a) (dom_l a)
  end
.

Definition ldom {A} (Σ : list A) := dom_l (length Σ).

(* Notation "q1 ⋓ q2" := (qlub q1 q2) (at level 70, right associativity). *)



Fixpoint subst_q (q : qual) (v : nat) (q' : qual) : qual :=
  match q with
  | qempty        => qempty
  | qvar (# x)    => qvar (# x)
  (* already on the assumption that always subst variable 0, so put all variables by pred*)
  | qvar ($ x)    => if beq_nat x v then q' else (qvar $ (pred x))
  | qloc x        => qloc x
  | qor  q1 q2    => qor (subst_q q1 v q') (subst_q q2 v q')
  end.

(* Notation "{ v1 |-> q1 ; q2 }ᵈ q" := (subst_q (subst_q q v1 q1) v1 q2) (at level 10).
Notation "{ v1 |-> q1 }ᵈ q" := (subst_q q v1 q1) (at level 10). *)
  

Module QualNotations.
  Declare Scope syntactic_qualifiers.

  Notation "∅" := qempty (at level 9).

  Notation "l ∈ₗ d"  := (qmem (inr l) d) (at level 75) : syntactic_qualifiers.
  Notation "v ∈ᵥ d"  := (qmem (inl v) d) (at level 75) : syntactic_qualifiers.

  Notation "$$ x " := (just_fv x) (at level 0, right associativity) : syntactic_qualifiers.
  Notation "## x " := (just_bv x) (at level 0, right associativity) : syntactic_qualifiers.
  Notation "&& l " := (just_loc l) (at level 0, right associativity) : syntactic_qualifiers.

  Notation "d1 ⊔ d2" := (qlub d1 d2) (at level 70, right associativity) : syntactic_qualifiers.

  Notation "d1 ⊕ x" := (qplus d1 x) (at level 70) : syntactic_qualifiers. (* qor (varF x) d1 *)

  Notation "q1 ⋓ q2" := (qlub q1 q2) (at level 70, right associativity) : syntactic_qualifiers.

End QualNotations.
Import QualNotations.
Local Open Scope syntactic_qualifiers.
