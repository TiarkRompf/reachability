Require Export Arith.EqNat.
Require Export Arith.Le.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Program.Equality.
Require Import Coq.Lists.List.
Require Import Psatz.
Require Import Coq.Arith.Compare_dec.
Import ListNotations.

Require Import vars.
Require Import env.
Require Import tactics.
Require Import qualifiers.
Require Import lambda_star.

Require Import examples_infra.
Require Import NatSets.
Require Import setfacts.
Import NatSet.F.

Import OpeningNotations.
Open Scope opening.

Import QualNotations.
Local Open Scope qualifiers.

(* ### Examples ### *)

Notation " { a | b } ={ eu | ek }=> { c | d }"  := (TFun b d eu ek a c)
(at level 10, format "'[' '[hv' '{' a  '/' '|'  b '}' ']' '/  '  '={' eu '|' ek '}=>' '[hv' '{' c  '/' '|'  d '}' ']' ']'").

Definition seq (t1 t2 : tm): tm := (tapp (tapp (tabs (tabs #0)) t1) t2).
Notation "a ; b" := (seq a b) (at level 10).

(* well-typed sequences do not have use after kill *)
Example no_use_after_kill : forall Γ Σ φ t1 t2 T d u k,
  has_type Γ φ Σ (t1 ; t2) T d u k ->
  exists T1 d1 u1 k1 T2 d2 u2 k2, 
  has_type Γ φ Σ t1 T1 d1 u1 k1 /\
  has_type Γ φ Σ t2 T2 d2 u2 k2 /\
  k1 ⊓ u2 = ∅.
intros. remember (t1 ; t2) eqn:Eq0. unfold seq in *. induction H; try discriminate; eauto. 
inversion Eq0. subst.
remember (tapp (tabs (tabs # 0)) t1) eqn:Eq1. induction H; try discriminate; eauto.
inversion Eq1. subst. repeat eexists; eauto. 
unfold eff_seq_ok in *. qdisj. 
apply stp_qstp_invu in H11 as Hu. apply stp_qstp_invk in H11 as Hk. inversion Hu. inversion Hk. subst. 
apply IHhas_type; eauto; unfold eff_seq_ok in *.
- eapply qglb_empty_sub; eauto.
- qdisj. eapply qglb_empty_sub; eauto. 
Qed.
