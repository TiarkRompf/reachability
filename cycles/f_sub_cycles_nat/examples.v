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
Require Import lang.
Require Import qenv.

Import QualNotations.
Local Open Scope qualifiers.
Import OpeningNotations.
Local Open Scope opening.

Require Import f_sub_cycles_nat.

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

Definition seq (t1 t2: tm) :=
  tapp (tabs ([[1 ~> tunit ]]ᵗ ([[0 ~> tunit ]]ᵗ t2))) t1.

Notation "t1 ';ₜ' t2" := (seq t1 t2) (at level 10).
Notation "t1 ':=' t2" := (tassign t1 t2) (at level 10).

Definition tlet (t1 t2 : tm) := tapp (tabs t2) t1.

Notation " { a | b } ==> { c | d }"  := (TFun b d a c)
(at level 10, format "'[' '[hv' '{' a  '/' '|'  b '}' ']' '/  '  '==>'  '[hv' '{' c  '/' '|'  d '}' ']' ']'").

Notation "∀<:{ a | b }.{ c | d }"  := (TAll b d a c)
(at level 10, format "'[' '[hv' '∀<:{' a  '/' '|'  b '}.{' ']' '/  '  '[hv' c  '/' '|'  d '}' ']' ']'").

Notation " 'λ' t" := (tabs t) (at level 10). 

(* Definition fff : tm := tabs (tderef # 1). *)

(* Example f'_type: *)
(* has_type [] ∅ [] f' (TFun ∅ ∅ (TRef ∅ TUnit) TUnit) ∅. *)
(* Proof. *)
(*   constructor; simpl; eauto. *)
(*   unfold openq',openq,open_ty',open_ty,open_tm',open_rec_tm,open_tm. simpl. *)
(*   rewrite open_qual_empty_id'. rewrite qor_empty_left. *)
(*   eapply t_deref with (d:=$! 1); eauto. *)
(*   eapply t_var with (d:=∅); eauto. *)
(*   replace 1 with ((‖ [(bind_tm, true, TFun ∅ ∅ (TRef ∅ TUnit) TUnit, ∅)] ‖)). *)
(*   erewrite indexr_head; eauto. *)
(*   simpl. lia. *)
(*   Qcrush. *)
(* Qed. *)

(* Definition c : tm := *)
(*   tsref (f'). *)

(* Example c_type: *)
(*   has_type [] ∅ [] c (TSRef ∅ (TFun ∅ ∅ (TRef ∅ TUnit) TUnit)) {♦}. *)
(* Proof. *)
(*   constructor; simpl; eauto. *)
(*   apply f_type. *)
(* Qed. *)

Notation "t1 ';' t2" := (seq t1 t2) (at level 10).
Notation "t1 ':=' t2" := (tassign t1 t2) (at level 10).

Example seq_type:
  has_type [] ∅ [] ((tref tunit := tunit) ; (tabs tunit))
  (TFun ∅ ∅ TUnit TUnit) ∅.
Proof.
  unfold seq. replace (TFun ∅ ∅ TUnit TUnit) with ((TFun ∅ ∅ TUnit TUnit) <~ᵀ TUnit ~ ∅; TUnit ~ ∅). replace (∅) with (∅ <~ᵈ ∅ ; ∅). 
  apply t_app; eauto. apply t_abs; auto. 
  unfold openq',openq,open_ty',open_ty,open_tm',open_tm. simpl. constructor; auto.
  apply t_abs; simpl; auto. Qcrush.
  unfold openq',openq,open_ty',open_ty,open_tm',open_tm. simpl.
  eapply t_sub; eauto. apply t_base; auto. Qcrush.
  eapply t_assign; eauto.
  unfold not_free. 
  all: eauto. constructor.
Qed.

(* Landin's knot
let x = ref (λy. y) in (x := (λz. (!x)(z))) *)
Definition knot := tlet (tsref (tabs tunit)) (#1 := (tabs (tapp (! #3) #1))).

Example knot_typable:
  has_type [] ∅ [] knot TUnit ∅.
Proof.
  unfold knot, tlet.
  replace (∅) with (∅ <~ᵈ ∅; {♦}) at 2.
  replace TUnit with (TUnit <~ᵀ TUnit ~ ∅; (TSRef #!0 (TFun {♦} ∅ TUnit TUnit)) ~ {♦}).
  eapply t_app_fresh; eauto. unfold q_trans_tenv. simpl. rewrite qor_empty_left.
  eapply t_abs; eauto.
  simpl. repeat constructor; auto.
  simpl. constructor; auto. constructor; auto. Qcrush.
  simpl. unfold open_tm', open_ty', openq'; simpl.
  eapply t_sassign_v.
  eapply t_var.
  all: simpl; auto. Qcrush. Qcrush.
  constructor; auto. Qcrush.
  eapply t_abs; simpl; eauto. 
  constructor; auto. Qcrush.  Qcrush.
  unfold open_tm', open_ty', openq'; simpl.
  replace (∅ <~ᵈ $! 2; $! 3) with (∅ <~ᵈ ([[0 ~> $!1 ]]ᵈ #! 0) ; $!3).
  replace (TUnit <~ᵀ $ 2 ~ $! 2; $ 3 ~ $! 3) with (TUnit <~ᵀ TUnit ~ ∅; TUnit ~ $!3).
  apply t_app_fresh; auto.
  unfold q_trans_tenv. simpl.
  eapply t_sderef. eapply t_var. 
  simpl. rewrite open_qual_bv. 
  repeat rewrite <- qor_assoc, qor_idem. rewrite qor_qand_dist_r. 
  repeat rewrite <- qor_assoc, qor_idem. rewrite <- qor_qand_dist_r. 
  replace ($!1 ⋒ $!3) with ({♦}); auto. 
  replace ($!1 ⊓ $!3) with (∅); auto. unfold "∅". unfold qand. repeat f_equal. apply N_lift_eq. Qcrush.
  all: simpl; eauto. rewrite open_qual_bv. Qcrush. Qcrush.
  constructor; auto. constructor; auto. Qcrush. Qcrush. Qcrush.
  eapply t_var. simpl. eauto. Qcrush. 
  simpl; eauto. Qcrush.
  constructor; auto. 
  eauto. Qcrush. unfold not_free. simpl. auto. constructor.
  unfold q_trans_tenv. simpl. Qcrush.
  eapply t_sref; auto. apply t_abs; auto. Qcrush. 
  unfold open_tm', open_ty', openq'; simpl. apply t_base; auto. Qcrush.
  1-3: unfold not_free; auto.
Qed.

Notation " { a | b } ==> { c | d }"  := (TFun b d a c)
(at level 10, format "'[' '[hv' '{' a  '/' '|'  b '}' ']' '/  '  '==>'  '[hv' '{' c  '/' '|'  d '}' ']' ']'").

Notation "∀<:{ a | b }.{ c | d }"  := (TAll b d a c)
(at level 10, format "'[' '[hv' '∀<:{' a  '/' '|'  b '}.{' ']' '/  '  '[hv' c  '/' '|'  d '}' ']' ']'").

Notation " 'λ' t" := (tabs t) (at level 10). 

Notation "⊤" := TTop.

(* #3 is outer, #1 is inner *)

(* fix = f => let c = new Ref in c := f(x => !c x) ; m => !c m *)
Definition fixpoint := 
  λ (tapp (λ (tapp (λ ! #3) (#1 := (tapp #3 (λ (tapp (! #3) #1)))))) (tsref (λ tunit))).

Definition fac' := tabs (* f *) (tabs (* n *)
  (tif (tiszero #1) (tnat 1) (tapp #3 (tpred #1)))).

Definition fac := (tapp fixpoint fac').

Definition nested_abs := tabs (tabs #3).

Definition fresh_ref := tapp (λ (tref tunit)) tunit.

Ltac simp := unfold open_tm', open_ty', openq', open_tm, open_ty, openq; simpl; repeat rewrite open_qual_bv, open_qual_fv, open_qual_empty_id', open_qual_bv_id.

Ltac simps := unfold open_tm', open_ty', openq', open_tm, open_ty, openq; simpl; repeat rewrite open_qual_bv; repeat rewrite open_qual_fv; repeat rewrite open_qual_empty_id'; repeat rewrite open_qual_bv_id; repeat rewrite open_qual_fresh_id.

Lemma fresh_ref_typable: has_type [] {♦} [] fresh_ref (TRef ∅ TUnit) {♦}.
Proof.
  unfold fresh_ref. replace ({♦}) with ({♦} <~ᵈ ∅; ∅) at 2. replace (TRef ∅ TUnit) with ((TRef ∅ TUnit) <~ᵀ TUnit ~ ∅; TUnit ~ ∅). apply t_app_fresh; auto. apply t_abs; auto. apply t_ref; auto. autounfold. simpl. rewrite open_qual_empty_id'. apply t_base; auto. Qcrush. all: intuition. unfold not_free. simpl. rewrite open_qual_empty_id'; auto. constructor.
Qed.

Definition fresh_sref := (tsref (λ #1)).

Definition fresh_sref_ty := (TSRef #!0 ({TInt | ∅} ==> {TInt | ∅})).

Lemma fresh_sref_typable:
  has_type []
  ∅ [] fresh_sref fresh_sref_ty {♦}.
Proof.
  apply t_sref; auto. rewrite open_qual_bv. apply t_abs; auto. simpl. unfold open_tm',open_ty',openq'. simpl. 
  eapply t_var_lookup. simpl; eauto. 5: eapply t_var. 5: simpl; auto. 
  all: simps; eauto. Qcrush. Qcrush.
Qed.

Lemma fresh_sref_via_var_typable:
  has_type []
  {♦} [] (λ (tapp (λ (! #1)) fresh_sref))
  (* arg type *)
  ({ TInt | ∅ } ==>
  (* return type *)
  {({TInt | ∅} ==> {TInt | ∅}) | {♦}})
  (* capturing set *)
  ∅.
Proof.
  apply t_abs; auto. repeat constructor; auto.
  simp. repeat rewrite open_qual_empty_id'.
  replace ({TInt | ∅} ==> {TInt | ∅}) with (({TInt | ∅} ==> {TInt | ∅}) <~ᵀ TUnit ~ ∅; fresh_sref_ty ~ {♦}).
  replace ([[1 ~> $! 1 ]]ᵈ ([[0 ~> $! 0 ]]ᵈ {♦})) with (#!1 <~ᵈ ∅; {♦}).
  apply t_app_fresh. unfold q_trans_tenv; simpl; auto. apply t_abs; auto.
  constructor; eauto. Qcrush. constructor; eauto. Qcrush. Qcrush. Qcrush.
  simp. replace ([[1 ~> $! 3 ]]ᵈ ([[0 ~> $! 2 ]]ᵈ #! 1)) with (([[0 ~> $!3 ]]ᵈ #!0)).
  apply t_sderef; auto.
  eapply t_var. simpl. eauto. Qcrush. Qcrush.
  constructor; auto. Qcrush. Qcrush. Qcrush. repeat rewrite open_qual_bv; auto. 
  eapply weaken_flt. apply weaken; auto. apply fresh_sref_typable; auto. constructor; auto. constructor; auto. constructor; auto. constructor; auto. Qcrush. Qcrush. 1,2: unfold not_free; intuition. unfold not_free; auto. Qcrush. Qcrush.
  simps. Qcrush. auto. 
Qed.

Definition fix_body := (λ ((#1 := (tapp #3 (λ (tapp (! #3) #1)))); (! #3))).

Lemma fresh_ret_typable: forall c,
  has_type []
  {♦} [] (tapp (λ (tapp (λ (! #1)) fresh_sref)) (tnat c))
  ({TInt | ∅} ==> {TInt | ∅}) {♦}.
Proof.
  replace ({TInt | ∅} ==> {TInt | ∅}) with (({TInt | ∅} ==> {TInt | ∅}) <~ᵀ TUnit ~ ∅; TInt ~ ∅); auto.
  replace ({♦}) with ({♦} <~ᵈ ∅; ∅).
  intros. apply t_app; auto. apply fresh_sref_via_var_typable. constructor. constructor.
  simp. auto.
Qed.

Lemma open_qual_empty_id : forall k q, [[ k ~> q]]ᵈ ∅ = ∅.
  Qcrush.
Qed.

Lemma qand_diamond_r_non_fresh : forall q, ♦∉ q -> (q ⊓ {♦}) = ∅.
intros. apply Q_lift_eq. Qcrush.
Qed.

Lemma qand_diamond_r_fresh : forall q, ♦∈ q -> (q ⊓ {♦}) = {♦}.
intros. apply Q_lift_eq. Qcrush.
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

Definition loop_fix := (λ (λ (tapp #3 #1))).

(* y:(T=>T) => (T=>T)^y *)
Lemma loop_fix_typable : has_type [] ∅ [] loop_fix 
   ({ {TInt | ∅} ==> {TInt | ∅} | {♦} } ==> 
    { {TInt | ∅} ==> {TInt | ∅} | #!1 }) ∅.
Proof.
  unfold loop_fix. 
  apply t_abs; auto.
  constructor. constructor; auto. 
  constructor; Qcrush.
  simp. repeat rewrite open_qual_empty_id. rewrite open_qual_bv. 
  apply t_abs; auto.
  Qcrush. Qcrush.
  simp. repeat rewrite open_qual_empty_id.
  replace (∅) with (∅ <~ᵈ $!1; ∅).
  replace (TInt) with (TInt <~ᵀ TUnit ~ ∅; TInt ~ ∅); auto.
  apply t_app; auto.
  eapply t_var; simpl; eauto. Qcrush.
  simp. rewrite open_qual_empty_id. eapply t_sub with (d1:=$!3). 
  eapply t_var; simpl; eauto. Qcrush. Qcrush.
  apply stp_refl; auto. eapply qs_qvar; simpl; eauto. Qcrush.
  1-2:unfold not_free; auto. Qcrush.
Qed.

(*  f = λx. f(x) diverges and typable in the old system *)

Example f_div := tabs (tapp #0 #1).

Example Tf_div := TFun ∅ ∅ TUnit TUnit.

Example f_div_typeable : has_type [] ∅ [] f_div Tf_div ∅.
Proof.
  unfold f_div; unfold Tf_div. 
  eapply t_abs; eauto. constructor; simpl; auto.
  simpl. unfold open_ty'; unfold open_tm'; unfold openq'. simpl. replace (TUnit <~ᵀ $ 0 ~ $! 0; $ 1 ~ $! 1) with (TUnit <~ᵀ TUnit ~ ∅; TUnit ~ ∅). 2:{ unfold open_ty; simpl; auto. } replace (∅ <~ᵈ $! 0; $! 1) with (∅ <~ᵈ ∅; ∅). 2:{ unfold openq. Qcrush. }
  eapply t_app; eauto.
    eapply t_sub. eapply t_var. rewrite indexr_skip; simpl; eauto. Qcrush. simpl. Qcrush. constructor; auto. Qcrush. econstructor; eauto. eapply qs_qvar; simpl. eauto. constructor; auto. Qcrush. intuition. Qcrush. Qcrush.
    eapply t_sub. eapply t_var; simpl. eauto. Qcrush. Qcrush. constructor. Qcrush. econstructor; eauto. eapply qs_qvar; simpl; eauto. Qcrush. 
    constructor. constructor.
Qed.

Example f_div_diverge : step (tapp f_div tunit) [] (tapp f_div tunit) [].
Proof.
  unfold f_div. remember (tapp # 0 # 1) as t. replace (tapp (tabs t) tunit) with (t <~ᵗ (tabs t); tunit) at 2. apply step_beta. constructor.
  rewrite Heqt. unfold open_tm; simpl. auto.
Qed.

Example f_div_applicable : forall t, 
  has_type [] ∅ [] t Tf_div ∅ ->
  has_type [] ∅ [] (tapp t tunit) TUnit ∅.
Proof.
  intros. eapply t_sub. eapply t_app; eauto. constructor. constructor. constructor. Qcrush. Qcrush.
Qed.

(* Landin's knot

let x = ref (λy. y) in (x := (λz. (!x)(z))) *)

Definition knot1 := tlet (tsref (tabs tunit)) (#1 := (tabs (tapp (! #3) #1))).

Example knot1_typable:
  has_type [] ∅ [] knot1 TUnit ∅.
Proof.
  unfold knot1, tlet.
  replace (∅) with (∅ <~ᵈ ∅; {♦}) at 2.
  replace TUnit with (TUnit <~ᵀ TUnit ~ ∅; (TSRef #!0 (TFun {♦} ∅ TUnit TUnit)) ~ {♦}).
  eapply t_app_fresh; eauto. unfold q_trans_tenv. simpl. rewrite qor_empty_left.
  eapply t_abs; eauto.
  simpl. repeat constructor; auto.
  simpl. constructor; auto. constructor; auto. Qcrush.
  simpl. unfold open_tm', open_ty', openq'; simpl.
  eapply t_sassign_v.
  eapply t_var.
  all: simpl; auto. Qcrush. Qcrush.
  constructor; auto. Qcrush.
  eapply t_abs; simpl; eauto. 
  constructor; auto. Qcrush.  Qcrush.
  unfold open_tm', open_ty', openq'; simpl.
  replace (∅ <~ᵈ $! 2; $! 3) with (∅ <~ᵈ ([[0 ~> $!1 ]]ᵈ #! 0) ; $!3).
  replace (TUnit <~ᵀ $ 2 ~ $! 2; $ 3 ~ $! 3) with (TUnit <~ᵀ TUnit ~ ∅; TUnit ~ $!3).
  apply t_app_fresh; auto.
  unfold q_trans_tenv. simpl.
  eapply t_sderef. eapply t_var. 
  simpl. rewrite open_qual_bv. 
  repeat rewrite <- qor_assoc, qor_idem. rewrite qor_qand_dist_r. 
  repeat rewrite <- qor_assoc, qor_idem. rewrite <- qor_qand_dist_r. 
  replace ($!1 ⋒ $!3) with ({♦}); auto. 
  replace ($!1 ⊓ $!3) with (∅); auto. unfold "∅". unfold qand. repeat f_equal. apply N_lift_eq. Qcrush.
  all: simpl; eauto. rewrite open_qual_bv. Qcrush. Qcrush.
  constructor; auto. constructor; auto. Qcrush. Qcrush. Qcrush.
  eapply t_var. simpl. eauto. Qcrush. 
  simpl; eauto. Qcrush.
  constructor; auto. 
  eauto. Qcrush. unfold not_free. simpl. auto. unfold not_free; auto. 
  unfold q_trans_tenv. simpl. Qcrush.
  eapply t_sref; auto. apply t_abs; auto. Qcrush. 
  unfold open_tm', open_ty', openq'; simpl. apply t_base; auto. Qcrush.
  1-3: unfold not_free; auto.
Qed.

(* int version of fixpoint *)

Definition fixpoint2 := 
  λ (tapp (λ (tapp (λ ! #3) (#1 := (tapp #3 (λ (tapp (! #3) #1)))))) (tsref (λ #1))).

Lemma fixpoint2_typable:
  has_type [] ∅ [] fixpoint2
    (* argument type: f:(g:(Int => Int)♦ => (Int => Int)^g)^f *)
    ({ { {TInt | ∅} ==> {TInt | ∅} | {♦} } ==> (* function g *)
    { {TInt | ∅} ==> {TInt | ∅} | #!1 } | ∅ } ==> 
    (* return type: (Int => Int)^♦ *)
    { {TInt | ∅} ==> {TInt | ∅} | {♦} }) ∅.
Proof.
  unfold fixpoint2.
  apply t_abs; auto.
  repeat constructor; auto.
  constructor; auto. constructor; auto. Qcrush.
  simpl. unfold open_tm', open_ty', openq'; simpl.
  remember ({TInt | ∅} ==> {TInt | ∅}) as F.
  replace (F <~ᵀ $ 0 ~ $! 0; $ 1 ~ $! 1) with (F <~ᵀ TUnit ~ ∅; (TSRef #! 0 ({TInt | ∅} ==> {TInt | ∅})) ~ {♦}); auto.
  replace ({♦} <~ᵈ $! 0; $! 1) with (#!1 <~ᵈ $!1; {♦}).
  eapply t_app_fresh; auto. unfold q_trans_tenv. simpl. rewrite qor_empty_left. rewrite diamond_qqcap_diamond_r.
  apply t_abs; auto.
  simpl. repeat constructor; auto.
  simpl. constructor; auto. Qcrush. Qcrush. constructor; auto. Qcrush.
  subst. constructor; auto. Qcrush. Qcrush.
  2: {
    eapply weaken_flt. eapply weaken; auto. 
    pose proof fresh_sref_typable as HH. unfold fresh_sref, fresh_sref_ty in *.
    apply HH. constructor; auto. constructor; auto. constructor; auto. 
    constructor; auto. Qcrush. 1-3: subst F; auto. 
    constructor; auto. Qcrush. Qcrush. subst F. auto.
    subst F. constructor; auto. Qcrush. Qcrush.
  }
  subst. simp. repeat rewrite open_qual_empty_id. rewrite open_qual_bv.
  remember ({TInt | ∅} ==> {TInt | ∅}) as F.
  remember (∅ ⊔ $! 2 ⊔ $! 3) as φ.
  replace $! 3 with ($!3 <~ᵈ $!3; ∅).
  replace F with (F <~ᵀ TUnit ~ ∅; TUnit ~ ∅).
  apply t_app; auto.
  apply t_abs; subst; simp. constructor. constructor. auto.
  constructor; Qcrush. Qcrush. Qcrush. Qcrush. auto.
  repeat rewrite open_qual_fv. repeat rewrite open_qual_empty_id. 
  replace $! 3 with ([[0 ~> $!3 ]]ᵈ #!0).
  apply t_sderef.
  eapply t_var; auto. simp. auto.
  rewrite open_qual_bv. Qcrush. Qcrush.
  constructor; auto. Qcrush. Qcrush. Qcrush. rewrite open_qual_bv. auto.
  eapply t_sassign_v with (d1:=#!0) (T:=F) (d:=$!3). 
  eapply t_var; eauto. subst. simp. auto. Qcrush. subst φ. Qcrush. subst. Qcrush. 
  constructor; auto. subst. constructor; auto. Qcrush. constructor; auto; Qcrush.
  rewrite open_qual_bv. subst. simp. 
  repeat rewrite open_qual_empty_id. repeat rewrite open_qual_fv. 
  remember ({TInt | ∅} ==> {TInt | ∅}) as F. 
  remember ($! 1 ⊔ $! 2 ⊔ $! 3) as φ. 
  (* apply f to f2, a fresh application *)
  replace ($!3) with (#!1 <~ᵈ $!1; $!3).
  replace F with (F <~ᵀ TUnit ~ ∅; F ~ $!3).
  apply t_app_fresh. subst; simp; auto. repeat rewrite open_qual_empty_id. unfold q_trans_tenv, q_trans''. simpl. repeat rewrite qor_empty_right. repeat rewrite <- qor_assoc. repeat rewrite qor_idem. replace ($! 1 ⋒ $! 3 ⊔ {♦}) with ({♦}). 
  eapply t_var. simp. auto. Qcrush. Qcrush. constructor; auto. Qcrush. Qcrush.
  rewrite qqcap_disjoint_diamond; auto. rewrite qand_qor_dist_l. rewrite qand_diamond_r_non_fresh; auto. replace ($! 1 ⊓ $! 3) with (∅); auto. rewrite qand_fv_neq; auto. 
  (* typing f2 *)
  subst. apply t_abs; auto. Qcrush. Qcrush. simp. repeat rewrite open_qual_empty_id. 
  remember ({TInt | ∅} ==> {TInt | ∅}) as F. 
  replace TInt with (TInt <~ᵀ TUnit ~ ∅; TInt ~ ∅).
  replace (∅) with (∅ <~ᵈ $!3; ∅).
  apply t_app; auto. 
  replace ($!3) with ([[0 ~> $!3 ]]ᵈ #!0).
  apply t_sderef; auto. repeat rewrite open_qual_bv. eapply t_var; auto. simp. subst F. auto.
  Qcrush. constructor; auto. Qcrush. Qcrush. rewrite open_qual_bv. auto.
  eapply t_sub with (d1:=$!5). 
  eapply t_var. simp. auto. Qcrush. Qcrush. constructor. Qcrush. 
  apply stp_refl; auto. eapply qs_qvar. simp. all: auto. constructor. intuition.
  subst. constructor. Qcrush. subst. constructor. subst. constructor. Qcrush. 
  unfold q_trans_tenv, q_trans''. simpl. Qcrush. 
  subst. simp. repeat rewrite open_qual_empty_id. auto.
  simp. rewrite open_qual_bv. auto.
  Qcrush. subst. constructor. subst. constructor. 
	subst. simp. repeat rewrite open_qual_empty_id; auto.
  simpl. intros. 1-3: subst; constructor. 
	Qcrush.
  subst. simp. rewrite open_qual_bv. simps; auto. 
  subst. simps. auto.
Qed.

(*
  f = λg.λx.g(x) 
  fix f = f (fix f) = λg.λx.g(x) (fix f) = λx.(fix f)(x) 
  (fix f)(c) = (fix f)(c)
  loop = (fix f)
*)
Definition loop := tapp fixpoint2 (λ (λ (tapp #3 #1))).

Lemma loop_typable : forall c, has_type [] ∅ [] (tapp loop (tnat c)) TInt ∅.
Proof.
  unfold loop. intros. 
  replace (TInt) with (TInt <~ᵀ TUnit ~ ∅; TInt ~ ∅); auto.
  replace (∅) with (∅ <~ᵈ {♦}; ∅).
  apply t_app; auto.
  remember ({TInt | ∅} ==> {TInt | ∅}) as F.
  replace (F) with (F <~ᵀ TUnit ~ ∅; ({ F | {♦} } ==> 
    { F | #!1 }) ~ ∅); auto.
  remember (F <~ᵀ TUnit ~ ∅; ({ F | {♦} } ==> 
    { F | #!1 }) ~ ∅).
  remember (∅ <~ᵈ ∅; ∅).
  replace ({♦}) with ({♦} <~ᵈ ∅; ∅).
  subst.
  apply t_app.
  simp. rewrite open_qual_empty_id.
  apply fixpoint2_typable.
  apply loop_fix_typable. 
  all: auto.
  all: unfold not_free; auto. 
  subst. simps. auto.
Qed.

(* Computation: "fact" , and F is renamed into "fact_fix"
    F(f : Int => Int) : (Int => Int) := 
      x => if (iszero x) then 1 else x * f (pred x)   // F : (I -> I) -> I -> I
    fact = fixpoint F     // fact : I -> I
    fact n = (fixpoint F) n ~= F (fixpoint F) n ~= F (fact) n
      (F fact) expands to 
      x => if (iszero x) then 1 else x * fact (pred x) )
    so it's good
*)

Definition fact_fix := λ (*f=#1*) (λ (* f=#3, x=#1 *) (
  tif (tiszero #1) (tnat 1) (
    tmul (#1) (tapp (#3) (tpred #1))
  )
)).

Definition TF := ({TInt | ∅} ==> {TInt | ∅}).
Example TF_closed : closed_ty 0 0 0 TF.
Proof.
  unfold TF. constructor; auto.
Qed.

(* T of fact := TF^fresh => TF^#1 *)
Definition T_fact_fix := { TF | {♦}} ==> {TF | #!1 }.

Example fact_fix_typable : has_type [] ∅ [] fact_fix T_fact_fix ∅.
Proof. 
  unfold fact_fix, T_fact_fix.
  apply t_abs; auto.
  constructor. repeat constructor; auto. 
  constructor; Qcrush. 1-2: constructor; auto.
  simp. repeat rewrite open_qual_empty_id. rewrite open_qual_bv. 
  apply t_abs; simpl; auto.
  repeat constructor; auto. Qcrush. Qcrush.
  simp. repeat rewrite open_qual_empty_id.
  (* body parts *) replace (∅) with (∅ ⊔ ∅). 2: Qcrush. eapply t_if with (q1:=∅).
  eapply t_iszero. eapply t_var; simpl; eauto. Qcrush. Qcrush.
  eapply t_nat. simpl. Qcrush.
  apply t_mul with (q1:=∅) (q2:=∅). eapply t_var_lookup; simpl; eauto. eapply t_var; simpl; eauto. Qcrush. Qcrush.
    rewrite qor_empty_left. replace (∅) with (∅ <~ᵈ $!1; ∅). replace (TInt) with (TInt <~ᵀ TUnit ~ ∅; TInt ~ ∅); auto. 2: Qcrush.
    eapply t_app; auto. eapply t_var; simpl; eauto. Qcrush. 
    eapply t_pred. eapply t_var; simpl; eauto. Qcrush. Qcrush. 1-2: constructor. 
Qed.
 
Definition fact := tapp fixpoint2 (fact_fix).

Lemma fact_typable : forall c, has_type [] ∅ [] (tapp fact (tnat c)) TInt ∅.
Proof.
  unfold fact. intros. 
  replace (TInt) with (TInt <~ᵀ TUnit ~ ∅; TInt ~ ∅); auto.
  replace (∅) with (∅ <~ᵈ {♦}; ∅).
  apply t_app; auto.
  remember ({TInt | ∅} ==> {TInt | ∅}) as F.
  replace (F) with (F <~ᵀ TUnit ~ ∅; ({ F | {♦} } ==> 
    { F | #!1 }) ~ ∅); auto.
  remember (F <~ᵀ TUnit ~ ∅; ({ F | {♦} } ==> 
    { F | #!1 }) ~ ∅).
  remember (∅ <~ᵈ ∅; ∅).
  replace ({♦}) with ({♦} <~ᵈ ∅; ∅).
  subst.
  apply t_app.
  simp. rewrite open_qual_empty_id.
  apply fixpoint2_typable.
  apply fact_fix_typable. 
  all: auto.
  all: unfold not_free; auto. 
  subst. simps. auto.
Qed.
