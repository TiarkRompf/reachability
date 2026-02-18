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
Require Import rules.
Require Import weaken_narrow.
Require Import vtp_subst.
Require Import type_safety.
Require Import corollary.

Import QualNotations.
Local Open Scope qualifiers.
Import OpeningNotations.
Local Open Scope opening.


(************
*  Lemmas  *
************)

Lemma qand_diamond_r_fresh : forall q, ♦∈ q -> (q ⊓ {♦}) = {♦}.
intros. apply Q_lift_eq. Qcrush.
Qed.

Lemma t_var_lookup: forall Γ φ Σ v T q fr,
  indexr v Γ = Some (bind_tm, fr, T, q) ->
  closed_ty 0 v (‖ Σ ‖) T ->
  closed_Qual 0 v (‖ Σ ‖) q ↑ ->
  ♦∉ q ->
  q ⊑↑ φ ->
  has_type Γ φ Σ $ v T $! v ->
  has_type Γ φ Σ $ v T q.
intros. eapply t_sub; eauto. apply stp_refl.
apply has_type_closed in H4; intuition.
eapply qs_qvar; eauto. apply has_type_filter in H4. eapply Subq_trans; eauto. 
simpl. apply kill_sep_empty_kill.
Qed.

Lemma ts_var_lookup: forall Γ φ v T q fr,
  indexr v Γ = Some (bind_tm, fr, T, q) ->
  closed_ty 0 v (0) T ->
  closed_Qual 0 v (0) q ↑ ->
  ♦∉ q ->
  q ⊑↑ φ ->
  has_type_static Γ φ $ v T $! v ->
  has_type_static Γ φ $ v T q.
intros. eapply ts_sub; eauto. apply stp_refl. 
apply static_typing in H4. apply has_type_closed in H4; intuition.
eapply qs_qvar; eauto. apply static_typing in H4. apply has_type_filter in H4. eapply Subq_trans; eauto. 
Qed.


Lemma open_qual_fresh_id : forall q n,
([[n ~> q ]]ᵈ {♦}) = {♦}.
intros. Qcrush.
Qed.

Lemma open_qual_empty_id' : forall k q, [[ k ~> q]]ᵈ ∅ = ∅.
Qcrush.
Qed.

Lemma open_qual_bv: forall b q,
[[b ~> q ]]ᵈ #! b = q.
intros. qual_destruct q. unfold open_qual. ndestruct (qbvs #! b b).
- apply Q_lift_eq. Qcrush.
- exfalso. Qcrush.
Qed.

Lemma open_qual_bv_id: forall b b' q,
  b <> b' ->
  [[b ~> q ]]ᵈ #! b' = #! b'.
intros. qual_destruct q. unfold open_qual. ndestruct (qbvs #! b' b).
- apply Q_lift_eq. Qcrush.
- auto.
Qed.

Lemma open_qual_fv: forall b f q, [[b ~> q ]]ᵈ $! f = $!f.
intros. qual_destruct q. unfold open_qual. ndestruct (qbvs $! f b).
- apply Q_lift_eq. Qcrush.
- auto.
Qed.

Lemma diamond_qqcap_diamond_r : forall q, (q ⋒ {♦}) = {♦}.
#[local] Hint Resolve is_true_reflect : bdestruct.
  intros. unfold "⋒". bdestruct (♦∈? q).
#[local] Remove Hints is_true_reflect : bdestruct.
- rewrite qand_diamond_r_fresh. Qcrush. auto.
- rewrite qand_diamond_r_non_fresh. Qcrush. auto.
Qed.

Lemma qqcap_disjoint_diamond : forall q1 q2,
  q1 ⊓ q2 = ∅ -> (q1 ⋒ q2) = {♦}.
intros.
  intros. unfold "⋒". rewrite H.
destruct (♦∈? ∅); Qcrush.
Qed.

Lemma qand_fv_neq : forall n m ,
  n <> m -> $! n ⊓ $! m = ∅.
intros. apply Q_lift_eq. Qcrush.
Qed.

Lemma qdiff_qdiff_empty: forall a , qdiff a a = ∅.
intros. apply Q_lift_eq. rewrite Q_lift_diff. Qcrush.
Qed.

Lemma open_qual_qor_dist : forall a b c n, 
  [[n ~> c ]]ᵈ (a ⊔ b) = ([[n ~> c ]]ᵈ a ⊔ [[n ~> c ]]ᵈ b).
intros. unfold open_qual. rewrite qn_or_dist. apply Q_lift_eq. ndestruct (qbvs a n); ndestruct (qbvs b n); ndestruct (n_or (qbvs a) (qbvs b) n); Qcrush.
eauto.
eauto.
Qed.

Lemma qor_idem' : forall q1 q, ((q1 ⊔ q) ⊔ q) = (q1 ⊔ q).
intros. apply Q_lift_eq. Qcrush.
Qed.

(************************
*  Defs and Notations  *
************************)

Definition seq (t1 t2: tm) :=
  tapp (tabs ([[1 ~> tunit ]]ᵗ ([[0 ~> tunit ]]ᵗ t2))) t1.

Definition tlet (t1 t2 : tm) := tapp (tabs t2) t1.

Notation "t1 ';' t2" := (seq t1 t2) (at level 10).
Notation "t1 '::=' t2" := (tassign t1 t2) (at level 10).
Notation " 'λ' t" := (tabs t) (at level 10).
Notation " { a | b } ==> { c | d }"  := (TFun b d a c)
(at level 10, format "'[' '[hv' '{' a  '/' '|'  b '}' ']' '/  '  '==>'  '[hv' '{' c  '/' '|'  d '}' ']' ']'").
Notation "∀<:{ a | b }.{ c | d }"  := (TAll b d a c)
(at level 10, format "'[' '[hv' '∀<:{' a  '/' '|'  b '}.{' ']' '/  '  '[hv' c  '/' '|'  d '}' ']' ']'").

Example seq_type:
  has_type [] ∅ [] ((tref tunit ::= tunit) ; (tabs tunit))
  (TFun ∅ ∅ TUnit TUnit) ∅.
Proof.
  apply static_typing.
  unfold seq. replace (TFun ∅ ∅ TUnit TUnit) with ((TFun ∅ ∅ TUnit TUnit) <~ᵀ TUnit ~ ∅; TUnit ~ ∅). replace (∅) with (∅ <~ᵈ ∅ ; ∅).
  apply ts_app; eauto. apply ts_abs; auto.
  unfold openq',openq,open_ty',open_ty,open_tm',open_tm. simpl. constructor; auto.
  apply ts_abs; simpl; auto. Qcrush.
  unfold openq',openq,open_ty',open_ty,open_tm',open_tm. simpl.
  eapply ts_sub; eauto. apply ts_base; auto. Qcrush.
  eapply ts_assign; eauto.
  unfold not_free.
  all: eauto. 
Qed.

Ltac simp := unfold open_tm', open_ty', openq', open_tm, open_ty, openq; simpl; repeat rewrite open_qual_bv, open_qual_fv, open_qual_empty_id', open_qual_bv_id.

Ltac simps := unfold open_tm', open_ty', openq', open_tm, open_ty, openq; simpl; repeat rewrite open_qual_bv; repeat rewrite open_qual_fv; repeat rewrite open_qual_empty_id'; repeat rewrite open_qual_bv_id; repeat rewrite open_qual_fresh_id.

Inductive multi_step: tm -> store -> tm -> store -> Prop :=
| multi_step_nil : forall (t1 t2 : tm) (σ1 σ2 : store),
    step t1 σ1 t2 σ2 ->
    multi_step t1 σ1 t2 σ2
| multi_step_cons : forall (t1 t' t2 : tm) (σ1 σ' σ2 : store),
    step t1 σ1 t' σ' ->
    multi_step t' σ' t2 σ2 ->
    multi_step t1 σ1 t2 σ2
.

Lemma multi_step_trans: forall t1 t2 t' σ1 σ2 σ',
  multi_step t1 σ1 t' σ' ->
  multi_step t' σ' t2 σ2 ->
  multi_step t1 σ1 t2 σ2.
intros. induction H.
- eapply multi_step_cons; eauto. 
- intuition. eapply multi_step_cons; eauto. 
Qed.

Lemma η_reduction : forall f f' l, f = λ (tapp f' #1) -> closed_tm 0 0 l f' ->
  forall x σ, value x -> step (tapp f x) σ (tapp f' x) σ.
intros. subst.
replace (tapp f' x) with ((tapp f' # 1) <~ᵗ (λ (tapp f' #1)); x).
apply step_beta; auto. simp. repeat erewrite closed_tm_open_id; eauto.
Qed.

(* stepped result of applying f to v *)
Definition unwrap (f : tm) (v : tm) : tm := match f with
                                       | λ body => (body <~ᵗ (λ body); v)
                                       | _ => f 
                                            end.

(* unwraps when applied to a value *)
Definition unwraps (f : tm) := forall v σ, value v -> value (unwrap f v) /\ step (tapp f v) σ (unwrap f v) σ.

