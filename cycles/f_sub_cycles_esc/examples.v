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

Require Import f_sub_cycles_esc.
Require Import examples_infra.

(**************************************
*  Section 5.1: Fixpoint Combinator  *
**************************************)

Section fixed_point.

(* Landin’s Knot:
 let x = ref (λy. y) in
 x := (λz. (!x)(z)) *)
Let knot :=
  tlet
    (tsref (tabs tunit))                        (* x = ref (λy. y) *)
    (#1 ::=                                     (* x := *)
      (tabs                                     (*   λz. *)
        (tapp (! #3) #1)                        (*     (!x)(z) *)
      )
    ).

Example knot_typable:
  has_type [] ∅ [] knot TUnit ∅.
Proof.
  unfold knot, tlet.
  replace (∅) with (∅ <~ᵈ ∅; {♦}) at 2.
  replace TUnit with (TUnit <~ᵀ TUnit ~ ∅; (TSRef #!0 (TFun {♦} ∅ TUnit TUnit) #!0 (TFun {♦} ∅ TUnit TUnit)) ~ {♦}).
  eapply t_app_fresh; eauto. unfold q_trans_tenv. simpl. rewrite qor_empty_left.
  eapply t_abs; eauto.
  simpl. repeat constructor; auto.
  simpl. constructor; auto. constructor; auto. Qcrush. Qcrush.
  simpl. unfold open_tm', open_ty', openq'; simpl. 
  eapply t_sassign_v.
  eapply t_var.
  all: simpl; auto. Qcrush. Qcrush.
  constructor; auto. Qcrush. Qcrush.
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
  all: simpl; eauto. rewrite open_qual_bv. Qcrush. Qcrush. Qcrush.
  constructor; auto. Qcrush. constructor; auto. Qcrush. Qcrush. Qcrush.
  eapply t_var. simpl. eauto. Qcrush.
  simpl; eauto. Qcrush.
  constructor; auto.
  eauto. Qcrush. unfold not_free. simpl. auto. constructor.
  unfold q_trans_tenv. simpl. Qcrush.
  eapply t_sref; auto. apply t_abs; auto. Qcrush.
  unfold open_tm', open_ty', openq'; simpl. apply t_base; auto. Qcrush.
  1-3: unfold not_free; auto.
Qed.

(* Polymorphic version of fixpoint *)

Let fixpoint :=                             (* Polymorphic fixpoint operator *)
  ttabs (                                   (* Type abstraction: ∀T. ... *)
    λ (                                     (* The actual fix function: λf. ... *)
      tapp
        (λ (                                  
          tapp
            (λ ! #3)                        (* λm. (! #3)(m): apply dereferenced ref to argument *)
            (#1 ::=                         (* #1 is ref cell c, assignment: c := ... *)
              (tapp
                #3                          (* Apply f to... *)
                (λ (
                  tapp (! #3) #1            (* λm. (! #3)(m): recursive call using updated c *)
                )))
            )
        ))
        (tsref (λ #1))                      (* Initial value: ref (λx. x) *)
    )
  ).

Example fixpoint_typable:
  forall T,
  closed_ty 0 0 0 T ->
  has_type [] ∅ [] fixpoint
    (* type argument: TTop *)
    (TAll ∅ ∅ T
    (* function argument: f:(g:(Int => Int)♦ => (Int => Int)^g)^f *)
    ({ { {# 1 | ∅} ==> {# 3 | ∅} | {♦} } ==> (* function g *)
    { {# 3 | ∅} ==> {# 5 | ∅} | #!1 } | ∅ } ==>
    (* return type: (Int => Int)^♦ *)
    { {# 3 | ∅} ==> {# 5 | ∅} | {♦} }))
    (* type abstraction's captured variables *)
    ∅.
Proof.
  intros. apply t_tabs. repeat constructor; auto. constructor; auto.
  constructor; auto.
  constructor; auto. 1-5: Qcrush.
  unfold fixpoint.
  simp. apply t_abs; auto.
  repeat constructor; auto.
  constructor; auto. constructor; auto. Qcrush. Qcrush.
  simp. repeat rewrite open_qual_empty_id'. repeat rewrite open_qual_fresh_id. 
  repeat rewrite open_qual_bv_id; auto.
  remember ({$ 1 | ∅} ==> {$ 1 | ∅}) as F.
  replace ({♦}) with (#!1 <~ᵈ $!3; {♦}) at 6.
  replace F with (F <~ᵀ TUnit ~ ∅; (TSRef #! 0 ({$1 | ∅} ==> {$1 | ∅}) #! 0 ({$1 | ∅} ==> {$1 | ∅})) ~ {♦}) at 6; auto.
  eapply t_app_fresh; auto. unfold q_trans_tenv. simpl. rewrite qor_empty_left. rewrite diamond_qqcap_diamond_r.
  apply t_abs; auto.
  simpl. repeat constructor; auto.
  simpl. constructor; auto. Qcrush. 
  constructor; auto. constructor; auto. Qcrush.
  subst. constructor; auto. Qcrush. subst. constructor; auto. Qcrush.
  2: {
    apply t_sref. auto. rewrite open_qual_bv. apply t_abs; auto. simpl. constructor; auto. Qcrush.
    simp. eapply t_var_lookup. simpl; eauto. 5: eapply t_var. 5: simpl; auto.
    all: simps; eauto. Qcrush. Qcrush. Qcrush. constructor; auto.
    constructor; auto.
  }
  subst. simp. repeat rewrite open_qual_empty_id'. rewrite open_qual_bv.
  remember ({$ 1 | ∅} ==> {$ 1 | ∅}) as F.
  remember ($! 3 ⊔ $! 4 ⊔ $! 5) as φ.
  replace $! 5 with ($!5 <~ᵈ $!5; ∅).
  replace F with (F <~ᵀ TUnit ~ ∅; TUnit ~ ∅) at 11.
  apply t_app; auto.
  apply t_abs; subst; simp. constructor. constructor. auto.
  constructor; Qcrush. Qcrush. Qcrush. Qcrush. auto.
  repeat rewrite open_qual_fv. repeat rewrite open_qual_empty_id'.
  replace $! 5 with ([[0 ~> $!5 ]]ᵈ #!0).
  eapply t_sderef.
  eapply t_var; auto. simp. auto.
  rewrite open_qual_bv. Qcrush. Qcrush.
  constructor; auto. constructor; auto. 
  1,2: eapply closed_ty_monotone; eauto.
  Qcrush. Qcrush. Qcrush. Qcrush. Qcrush. rewrite open_qual_bv. auto.
  eapply t_sassign_v with (d1:=#!0) (T1:=F) (d:=$!5).
  eapply t_var; eauto. subst. simp. auto. Qcrush. subst φ. Qcrush. subst. Qcrush.
  constructor; auto. subst. constructor; auto. Qcrush. Qcrush. Qcrush. subst. constructor; auto; Qcrush. Qcrush.
  rewrite open_qual_bv. 
  (* apply f to f2, a fresh application *)
  replace ($!5) with (#!1 <~ᵈ $!3; $!5).
  replace F with (F <~ᵀ TUnit ~ ∅; F ~ $!5) at 11.
  apply t_app_fresh. subst; simp; auto. unfold q_trans_tenv, q_trans''. simpl. repeat rewrite qor_empty_right. repeat rewrite <- qor_assoc. repeat rewrite qor_idem. replace ($! 3 ⋒ $! 5 ⊔ {♦}) with ({♦}).
  eapply t_var. simp. auto. Qcrush. Qcrush. constructor; auto. Qcrush. Qcrush.
  rewrite qqcap_disjoint_diamond; auto. rewrite qand_qor_dist_l. rewrite qand_diamond_r_non_fresh; auto. replace ($! 3 ⊓ $! 5) with (∅); auto. rewrite qand_fv_neq; auto.
  (* typing f2 *)
  subst. apply t_abs; auto. Qcrush. Qcrush. Qcrush. simp. repeat rewrite open_qual_empty_id'.
  remember ({$ 1 | ∅} ==> {$ 1 | ∅}) as F.
  replace (TVar $ 1) with ($1 <~ᵀ TUnit ~ ∅; $1 ~ ∅).
  replace (∅) with (∅ <~ᵈ $!5; ∅).
  apply t_app; auto.
  replace ($!5) with ([[0 ~> $!5 ]]ᵈ #!0).
  eapply t_sderef; auto. repeat rewrite open_qual_bv. eapply t_var; auto. simp. subst F. auto.
  Qcrush. constructor; auto. Qcrush. Qcrush. Qcrush. subst. Qcrush. Qcrush. constructor; auto; Qcrush. Qcrush. Qcrush. rewrite open_qual_bv. Qcrush.
  eapply t_sub with (d1:=$!7).
  eapply t_var. simp. auto. Qcrush. Qcrush. constructor; lia. Qcrush.
  apply stp_refl; auto. Qcrush. eapply qs_qvar. simp. all: auto 2. constructor. intuition.
  subst. constructor. Qcrush. subst. constructor. subst. constructor. Qcrush.
  1,2: subst; constructor. Qcrush. 
  unfold q_trans_tenv, q_trans''. simpl. Qcrush.
  subst. constructor.
  simp. rewrite open_qual_bv. auto.
  subst. Qcrush.
  1-3: subst; constructor.
  simpl. intros.
  1-3: subst; constructor.
	Qcrush.
  subst. simp. Qcrush.
  subst. simps. auto.
  Qed.

(* Helper lemma to instantiate the type abstraction *)
Lemma fixpoint_instantiable : forall T, 
  closed_ty 0 0 0 T ->
  has_type [] ∅ [] (ttapp fixpoint)
    ({{{T | ∅} ==> {T | ∅} | {♦}} ==> {{T | ∅} ==> {T | ∅} | #! 1}
       | ∅} ==> {{T | ∅} ==> {T | ∅} | {♦}}) ∅.
intros. 
remember ({{{T | ∅} ==> {T | ∅} | {♦}} ==> {{T | ∅} ==> {T | ∅} | #! 1} | ∅}
      ==> {{T | ∅} ==> {T | ∅} | {♦}}) as TT.
replace (∅) with (∅ <~ᵈ ∅; ∅) at 2.
replace TT with
    (( ({ { {# 1 | ∅} ==> {# 3 | ∅} | {♦} } ==>
    { {# 3 | ∅} ==> {# 5 | ∅} | #!1 } | ∅ } ==>
    { {# 3 | ∅} ==> {# 5 | ∅} | {♦} })) <~ᵀ TUnit ~ ∅; T ~ ∅).
apply t_tapp; eauto.
apply fixpoint_typable; eauto.
constructor. auto.
Qed.

(* Landin-style fixpoint:
   y : (T → T) → (T → T)^y *)
Let loop_fix :=
  λ (                                     (* λy. *)
    λ (                                   (*   λx. *)
      tapp #3 #1                          (*     y x *)
    )
  ).

Example loop_fix_typable : has_type [] ∅ [] loop_fix
   ({ {TUnit | ∅} ==> {TUnit | ∅} | {♦} } ==>
    { {TUnit | ∅} ==> {TUnit | ∅} | #!1 }) ∅.
Proof.
  unfold loop_fix.
  apply t_abs; auto.
  constructor. constructor; auto.
  constructor; Qcrush.
  simp. repeat rewrite open_qual_empty_id'. rewrite open_qual_bv.
  apply t_abs; auto.
  Qcrush. Qcrush.
  simp. repeat rewrite open_qual_empty_id'.
  replace (∅) with (∅ <~ᵈ $!1; ∅).
  replace (TUnit) with (TUnit <~ᵀ TUnit ~ ∅; TUnit ~ ∅); auto.
  apply t_app; auto.
  eapply t_var; simpl; eauto. Qcrush.
  simp. rewrite open_qual_empty_id'. eapply t_sub with (d1:=$!3).
  eapply t_var; simpl; eauto. Qcrush. Qcrush.
  apply stp_refl; auto. eapply qs_qvar; simpl; eauto. Qcrush.
  1-2:unfold not_free; auto. Qcrush.
Qed.

(* recursion using built-in recursion (function self reference) *)
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

(*
  f = λg.λx.g(x)
  fix f = f (fix f) = λg.λx.g(x) (fix f) = λx.(fix f)(x)
  (fix f)(c) = (fix f)(c)
  loop = (fix f)
*)
Let loop := tapp (ttapp fixpoint) (λ (λ (tapp #3 #1))).

Example loop_typable : has_type [] ∅ [] (tapp loop tunit) TUnit ∅.
Proof.
  unfold loop. intros.
  replace (TUnit) with (TUnit <~ᵀ TUnit ~ ∅; TUnit ~ ∅); auto.
  replace (∅) with (∅ <~ᵈ {♦}; ∅).
  apply t_app; auto.
  remember ({TUnit | ∅} ==> {TUnit | ∅}) as F.
  replace (F) with (F <~ᵀ TUnit ~ ∅; ({ F | {♦} } ==>
    { F | #!1 }) ~ ∅); auto.
  remember (F <~ᵀ TUnit ~ ∅; ({ F | {♦} } ==>
    { F | #!1 }) ~ ∅).
  remember (∅ <~ᵈ ∅; ∅).
  replace ({♦}) with ({♦} <~ᵈ ∅; ∅).
  subst.
  apply t_app.
  simp. rewrite open_qual_empty_id'.
  apply fixpoint_instantiable; auto.
  fold loop_fix.
  apply loop_fix_typable.
  all: auto.
  all: unfold not_free; auto.
  subst. simps. auto.
Qed.

(* F : (Int → Int) → (Int → Int) 
   fact_fix = λf. λx.
     if x = 0 then 1 else x * f (x - 1)
*)

Let fact_fix :=
  λ (                       (* f = #1 *)
    λ (                     (* x = #1, f = #3 *)
      tif (tiszero #1)      (* if iszero x *)
          (tnat 1)          (* then 1 *)
          (tmul             (* else x * f (x - 1) *)
            #1
            (tapp #3 (tpred #1))
          )
    )
  ).

Let TF := ({TInt | ∅} ==> {TInt | ∅}).
Example TF_closed : closed_ty 0 0 0 TF.
Proof.
  unfold TF. constructor; auto.
Qed.

(* T of fact := TF^fresh => TF^#1 *)
Let T_fact_fix := { TF | {♦}} ==> {TF | #!1 }.

Example fact_fix_typable : has_type [] ∅ [] fact_fix T_fact_fix ∅.
Proof.
  unfold fact_fix, T_fact_fix.
  apply t_abs; auto.
  constructor. repeat constructor; auto.
  constructor; Qcrush. 1-2: constructor; auto.
  simp. repeat rewrite open_qual_empty_id'. rewrite open_qual_bv.
  apply t_abs; simpl; auto.
  repeat constructor; auto. Qcrush. Qcrush.
  simp. repeat rewrite open_qual_empty_id'.
  (* body parts *) replace (∅) with (∅ ⊔ ∅). 2: Qcrush. eapply t_if with (q1:=∅).
  eapply t_iszero. eapply t_var; simpl; eauto. Qcrush. Qcrush.
  eapply t_nat. simpl. Qcrush.
  apply t_mul with (q1:=∅) (q2:=∅). eapply t_var_lookup; simpl; eauto. eapply t_var; simpl; eauto. Qcrush. Qcrush.
    rewrite qor_empty_left. replace (∅) with (∅ <~ᵈ $!1; ∅). replace (TInt) with (TInt <~ᵀ TUnit ~ ∅; TInt ~ ∅); auto. 2: Qcrush.
    eapply t_app; auto. eapply t_var; simpl; eauto. Qcrush.
    eapply t_pred. eapply t_var; simpl; eauto. Qcrush. Qcrush. 1-2: constructor.
Qed.

Let fact := tapp (ttapp fixpoint) (fact_fix).

Example fact_typable : forall c, has_type [] ∅ [] (tapp fact (tnat c)) TInt ∅.
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
  simp. rewrite open_qual_empty_id'.
  apply fixpoint_instantiable. constructor.
  apply fact_fix_typable.
  all: auto.
  all: unfold not_free; auto.
  subst. simps. auto.
Qed.

(**************
*  Stepping  *
**************)

Example fixpoint_steps : forall f x σ, value x -> value f -> unwraps f -> closed_tm 0 0 0 f -> multi_step (tapp (tapp (ttapp fixpoint) f) x) σ (tapp ! & (‖ σ ‖) x) ((Some (unwrap f (λ (tapp ! & (‖ σ ‖) # 1)))) :: σ).
intros. unfold fixpoint.
eapply multi_step_cons. apply step_c_app_l. apply step_c_app_l. apply step_ttapp.
eapply multi_step_cons. apply step_c_app_l. apply step_beta. assumption. simp.
eapply multi_step_cons. apply step_c_app_l. apply step_c_app_r. constructor. apply step_sref. constructor.
(* make sure that f unwraps to a value before introducing uninstantiated variables *)
remember (λ (tapp ! & (‖ σ ‖) # 1)) as wrapper.
assert (Hval: value wrapper). { subst. constructor. } 
unfold unwraps in H1. 
specialize (H1 wrapper (Some (λ # 1) :: σ) Hval) as Hstep. 
(* keep stepping *)
eapply multi_step_cons. apply step_c_app_l. apply step_beta. constructor.
eapply multi_step_cons. apply step_c_app_l. simp.
  repeat erewrite closed_tm_open_id; eauto. eapply step_c_app_r. constructor. 
  eapply step_c_assign_r. constructor. subst. eapply Hstep.
eapply multi_step_cons. apply step_c_app_l. apply step_c_app_r. constructor. apply step_assign; auto. intuition.
eapply multi_step_nil. apply step_c_app_l. simp. rewrite Nat.eqb_refl. eapply step_beta. constructor.
Qed.

(* fact_fix when applied to a value *)
Lemma fact_fix_unwraps: unwraps fact_fix.
unfold unwraps, unwrap, fact_fix. intros. 
remember ((tif (tiszero # 1) (tnat 1) (tmul # 1 (tapp # 3 (tpred # 1))))) as t. 
subst t. simp. intuition. apply step_beta. assumption.
Qed.

Example fact_4 : forall σ,
  multi_step
    (tapp                               (* Apply the final fact function to 4 *)
      (tapp (ttapp fixpoint) fact_fix)  (* fact = fixpoint fact_fix *)
      (tnat 4))
    σ
    (tnat (4 * 3 * 2 * 1))              (* Expected result: 24 *)
    ((Some (unwrap fact_fix (λ (tapp ! & (‖ σ ‖) #1)))) :: σ).  (* Final store *)
intros. 
eapply multi_step_trans. apply fixpoint_steps; eauto.
unfold fact_fix. constructor.
apply fact_fix_unwraps.
unfold fact_fix. repeat constructor. 
(* fixpoint unwraps *)
eapply multi_step_cons. apply step_c_app_l. apply step_deref. simpl. rewrite Nat.eqb_refl. auto.
eapply multi_step_cons. apply step_beta. constructor. 
eapply multi_step_cons. apply step_c_if. apply step_iszero.
eapply multi_step_cons. apply step_if_false.
eapply multi_step_cons. apply step_c_mul_r. constructor. apply step_c_app_r. constructor. apply step_pred. 
eapply multi_step_cons. apply step_c_mul_r. constructor. apply step_beta. constructor.
eapply multi_step_cons. apply step_c_mul_r. constructor. apply step_c_app_l. apply step_deref. simpl. rewrite Nat.eqb_refl. auto.
eapply multi_step_cons. apply step_c_mul_r. constructor. apply step_beta. constructor.
eapply multi_step_cons. apply step_c_mul_r. constructor. apply step_c_if. apply step_iszero.
eapply multi_step_cons. apply step_c_mul_r. constructor. apply step_if_false.
eapply multi_step_cons. apply step_c_mul_r. constructor. apply step_c_mul_r. constructor. apply step_c_app_r. constructor. apply step_pred.
eapply multi_step_cons. apply step_c_mul_r. constructor. apply step_c_mul_r. constructor. apply step_beta. constructor. 
eapply multi_step_cons. apply step_c_mul_r. constructor. apply step_c_mul_r. constructor. apply step_c_app_l. apply step_deref. simpl. rewrite Nat.eqb_refl. auto.
eapply multi_step_cons. apply step_c_mul_r. constructor. apply step_c_mul_r. constructor. apply step_beta. constructor.
eapply multi_step_cons. apply step_c_mul_r. constructor. apply step_c_mul_r. constructor. simp. apply step_c_if. apply step_iszero. 
eapply multi_step_cons. apply step_c_mul_r. constructor. apply step_c_mul_r. constructor. simp. apply step_if_false.
eapply multi_step_cons. simp. apply step_c_mul_r. constructor. apply step_c_mul_r. constructor. apply step_c_mul_r. constructor. apply step_c_app_r. constructor. apply step_pred. 
eapply multi_step_cons. simp. apply step_c_mul_r. constructor. apply step_c_mul_r. constructor. apply step_c_mul_r. constructor. apply step_beta. constructor.
eapply multi_step_cons. simp. apply step_c_mul_r. constructor. apply step_c_mul_r. constructor. apply step_c_mul_r. constructor. apply step_c_app_l. apply step_deref. simpl. rewrite Nat.eqb_refl. auto.
eapply multi_step_cons. simp. apply step_c_mul_r. constructor. apply step_c_mul_r. constructor. apply step_c_mul_r. constructor. apply step_beta. constructor.
eapply multi_step_cons. simp. apply step_c_mul_r. constructor. apply step_c_mul_r. constructor. apply step_c_mul_r. constructor. apply step_c_if. apply step_iszero.
eapply multi_step_cons. apply step_c_mul_r. constructor. apply step_c_mul_r. constructor. apply step_c_mul_r. constructor. apply step_if_false.
eapply multi_step_cons. apply step_c_mul_r. constructor. apply step_c_mul_r. constructor. apply step_c_mul_r. constructor. apply step_c_mul_r. constructor. apply step_c_app_r. constructor. apply step_pred.

eapply multi_step_cons. simp. apply step_c_mul_r. constructor. apply step_c_mul_r. constructor. apply step_c_mul_r. constructor. apply step_c_mul_r. constructor. apply step_beta. constructor.
eapply multi_step_cons. simp. apply step_c_mul_r. constructor. apply step_c_mul_r. constructor. apply step_c_mul_r. constructor. apply step_c_mul_r. constructor. apply step_c_app_l. apply step_deref. simpl. rewrite Nat.eqb_refl. auto.
eapply multi_step_cons. simp. apply step_c_mul_r. constructor. apply step_c_mul_r. constructor. apply step_c_mul_r. constructor. apply step_c_mul_r. constructor. apply step_beta. constructor.
eapply multi_step_cons. apply step_c_mul_r. constructor. apply step_c_mul_r. constructor. apply step_c_mul_r. constructor. apply step_c_mul_r. constructor. apply step_c_if. apply step_iszero.
eapply multi_step_cons. simp. apply step_c_mul_r. constructor. apply step_c_mul_r. constructor. apply step_c_mul_r. constructor. apply step_c_mul_r. constructor. apply step_if_true.
eapply multi_step_cons. apply step_c_mul_r. constructor. apply step_c_mul_r. constructor. apply step_c_mul_r. constructor. apply step_mul.
eapply multi_step_cons. apply step_c_mul_r. constructor. apply step_c_mul_r. constructor. apply step_mul.
eapply multi_step_cons. apply step_c_mul_r. constructor. apply step_mul.
eapply multi_step_nil. simp. apply step_mul.
Qed.

End fixed_point.

(********************************
*  Shallow Reference Tracking  *
********************************)

Section shallow.

Let par : tm :=
(λ (λ (tapp (λ (tapp # 3 tunit)) (tapp # 1 tunit)))).

  (* λ (λ ( *)
  (*   (1* Assume b1 and b2 are functions taking Unit and producing Unit *1) *)
  (*   seq (tapp (# 1) tunit) (1* Execute b1 *1) *)
  (*   (1* Parallel execution would be modeled via an operational rule *1) *)
  (*   (1* Simulating parallel execution *1) *)
  (*   (tapp (# 3) tunit) (1* Execute b2 *1) *)
  (* )). *)

Axiom typing_par : forall (Γ : tenv) (φ : qual) (Σ : senv),
  has_type Γ φ Σ par
  ({{TUnit | ∅} ==> {TUnit | ∅} | {♦}} ==> (* b1 captures contextual fresh argument *)
  {{{TUnit | ∅} ==> {TUnit | ∅} | {♦}} ==> (* b2 captures contextual fresh argument *)
  {TUnit | {♦}} | ∅}) ∅.

Let parallel_update :=
  tlet (tref tunit) (* Allocate outer2 *)
    (tlet (tref #1) (* Allocate outer1, referencing outer2 *)
      (tapp (tapp par (λ (#3; tunit))) (* Access outer1 *)
           (λ (#5 ::= tunit)))). (* Modify outer2 to reference a different tunit value *)

Example typing_parallel_update : forall (Γ : tenv) (φ : qual) (Σ : senv),
  has_type [] ∅ [] parallel_update
    (TUnit <~ᵀ TUnit ~ ∅; (TRef ∅ TUnit) ~ {♦})
    ({♦} <~ᵈ ∅; {♦}).
Proof.
  intros.
  unfold parallel_update, tlet.
  apply t_app_fresh.
  apply t_abs; auto. 
  repeat constructor; auto. 
  simpl. unfold q_trans_tenv, q_trans''. simp. fold par.
  replace TUnit with (TUnit <~ᵀ TUnit ~ ∅; (TRef $!1 (TRef ∅ TUnit)) ~ {♦}) at 4.
  replace ({♦}) with ({♦} <~ᵈ ($!0 ⊔ $!1) ; {♦}) at 7.
  eapply t_app_fresh; eauto.
  2: { apply t_ref; auto. eapply t_var. simp; auto. Qcrush.
    repeat rewrite qor_empty_left. apply closed_Qual_qor. Qcrush. Qcrush.
    constructor; auto. Qcrush.
  }
  unfold q_trans_tenv. simpl. apply t_abs; auto.
  repeat constructor; auto. constructor; auto. Qcrush. constructor; auto. Qcrush. 
  Qcrush. Qcrush.
  simp; auto. fold par. repeat rewrite qor_empty_left. repeat rewrite qor_empty_right. repeat rewrite <- qor_assoc. rewrite qor_idem. rewrite open_qual_fresh_id. 
  replace TUnit with (TUnit <~ᵀ TUnit ~ ∅; ({TUnit | ∅} ==> {TUnit | ∅}) ~ $!1) at 7.
  replace ({♦}) with ({♦} <~ᵈ ∅ ; $!1) at 11.
  apply t_app_fresh; simpl; auto.
  unfold q_trans_tenv. simpl. 
  2: {
    apply t_abs; simpl. repeat constructor; auto.
    constructor; auto. 1-4: Qcrush. repeat rewrite open_qual_empty_id'. 
    eapply t_assign; eauto. eapply t_var. simpl. auto. Qcrush. Qcrush.
    constructor; auto. Qcrush. apply t_base. Qcrush. Qcrush.
  }
  repeat rewrite <- qor_assoc. repeat rewrite qor_idem. repeat rewrite qor_empty_left. 
  remember ({{TUnit | ∅} ==> {TUnit | ∅} | {♦}} ==> {TUnit | {♦}}) as TT. 
  replace TT with (TT <~ᵀ TUnit ~ ∅; ({TUnit | ∅} ==> {TUnit | ∅}) ~ $!3).
  replace (∅) with (∅ <~ᵈ ∅ ; $!3) at 9.
  apply t_app_fresh; auto. unfold q_trans_tenv. simp.
  subst. repeat rewrite <- qor_assoc. repeat rewrite qor_empty_left. 
  apply typing_par.
  apply t_abs. repeat constructor; auto. subst. constructor; auto. 1-4: Qcrush.
  repeat rewrite <- qor_assoc. repeat rewrite qor_idem. repeat rewrite qor_empty_left. subst. simp. repeat rewrite open_qual_empty_id'. 
  replace TUnit with (TUnit <~ᵀ TUnit ~ ∅; (TRef $! 1 (TRef ∅ TUnit)) ~ $!3) at 10.
  replace (∅) with (∅ <~ᵈ $!3 ; $!3) at 11.
  apply t_app; auto. apply t_abs. constructor; auto. constructor; auto. Qcrush.
  constructor; auto. 1-5: Qcrush.
  simp. apply t_base. Qcrush. eapply t_var. simpl. auto. 1-2: Qcrush.
  constructor; auto. 1,2: Qcrush.
  all: subst; unfold not_free; intuition eauto 4. 
  1,2: unfold q_trans_tenv; simp; Qcrush. 
Qed.

End shallow.


Section escape.

(************************
*  Escaping Reference  *
************************)

Definition escaping_example' : tm := 
  λ (tlet #1 (tlet (tsref #1) #1)).

Definition escaping_example : tm :=
  λ (                           (* function f = λx. ... *)
    tapp
      (λ (                      (* let a = x in ... *)
         tapp
           (λ #1)               (* let c = ref a in c *) 
           (tsref #1)            (* c = ref a *)
       ))
      #1                        (* a = x (argument) *)
  ).
  
Example equal : escaping_example = escaping_example'. 
unfold escaping_example, escaping_example', tlet. auto.
Qed.

Example escaping_example_typable : has_type [] ∅ [] escaping_example ({TInt | {♦}} ==> {TSRef ∅ TInt #!0 TInt | #!1 ⊔ {♦}}) ∅.
unfold escaping_example.
apply t_abs; auto. repeat constructor; auto.
constructor; auto. Qcrush. constructor; auto. Qcrush.
simp. repeat rewrite open_qual_qor_dist. repeat rewrite open_qual_bv; auto. repeat rewrite open_qual_bv_id; auto. repeat rewrite open_qual_empty_id'. rewrite open_qual_fresh_id. 
(* typing let a = x in let c = new Ref(a) in c *)
replace ($! 1 ⊔ {♦}) with (( #!1 ⊔ {♦} ) <~ᵈ $!1; $! 1) at 1.
replace (TSRef ∅ TInt #! 0 TInt) with ((TSRef ∅ TInt #! 0 TInt) <~ᵀ TUnit ~ ∅; TInt ~ $! 1) at 2; auto.
apply t_app; auto.
(* typing λ a. let c = new Ref(a) in c *)
apply t_abs; auto. repeat constructor; auto.
constructor; eauto 3. 1,2: Qcrush. constructor; auto. 1-3: Qcrush.
simp. repeat rewrite open_qual_qor_dist. rewrite open_qual_bv_id; auto. rewrite open_qual_fresh_id. rewrite open_qual_bv. rewrite open_qual_bv_id; auto. repeat rewrite open_qual_empty_id'.
(* escape now *)
replace #!0 with (∅ ⊔ #!0) at 3.
(* replace ($! 3 ⊔ {♦}) with ({♦} ⊔ $!3). *)
eapply t_esc with (d:={♦}) (d1':=∅) (d1:=$!3) (d2:=$!3); auto. 
apply qs_sq; auto.
eapply closed_Qual_open''; eauto. Qcrush.
unfold n_sub. intros. eauto.
apply qs_sq; auto.
rewrite open_qual_empty_id'. Qcrush.
apply qs_sq; auto. Qcrush. Qcrush.
(* apply the inner abstraction *)
replace ({♦}) with (( #!1 ) <~ᵈ ($!3); {♦}) at 5.
replace (TSRef $! 3 TInt $! 3 TInt) with ((TSRef $! 3 TInt $! 3 TInt) <~ᵀ TUnit ~ ∅; (TSRef $!3 TInt $!3 TInt) ~ {♦}).
(* typing let c = new Ref(a) in c, or (λ c.c) (new Ref(a)) *) 
(* new Ref(a) : Ref $!3 TInt $!3 TInt ^ ♦ <: Ref ∅ TInt #!0 TInt ^ $!3 <: Ref ∅ TInt #!0 TInt ^ ♦ *)

(* escaping through the function, capturing local variable a and the argument c *)
apply t_app_fresh; auto.
all: unfold q_trans_tenv; simp. apply t_abs; auto. constructor; auto. Qcrush.
constructor; auto. 1,2: Qcrush. constructor; auto. 1-3: Qcrush. constructor; auto. 1-5: Qcrush.
unfold q_trans_tenv; simp. repeat rewrite open_qual_bv. repeat rewrite open_qual_fv. eapply t_var; auto. simpl. rewrite diamond_qqcap_diamond_r; eauto.
1,2: Qcrush. constructor; Qcrush.
apply t_sref; auto. rewrite open_qual_fv. eapply t_var. simpl. eauto. 1-4: Qcrush.
1-3: unfold not_free; auto. Qcrush. simpl. Qcrush.
rewrite open_qual_bv. auto. Qcrush. rewrite qor_commute. auto. 
eapply t_var. simpl. eauto. 1-5: Qcrush. 1,2: unfold not_free; auto. 
unfold openq. 
repeat rewrite open_qual_qor_dist. 
rewrite open_qual_bv. 
rewrite open_qual_fresh_id. auto.
Qed.

Definition escape_nested_ref : tm :=
  tlet (tref tunit)              (* let inner = ref unit in *)
    (tlet (tsref #1)           (* let mid = ref inner in *)
        (tlet (tsref #1)       (* let ref = ref mid in *)
            (tapp (λ #1) #1))   (* (λ r. r) ref *)
    ).

Example nested_ref_type : has_type [] ∅ [] escape_nested_ref 
  (TSRef ∅ TBot #!0 (TSRef ∅ TBot #!0 (TRef ∅ TUnit))) {♦}
.
unfold escape_nested_ref, tlet. 
replace ({♦}) with (( #!1 ⊔ {♦} ) <~ᵈ ∅; {♦}).
replace (TSRef ∅ TBot #! 0 (TSRef ∅ TBot #! 0 (TRef ∅ TUnit))) with ((TSRef ∅ TBot #! 0 (TSRef ∅ TBot #! 0 (TRef ∅ TUnit))) <~ᵀ TUnit ~ ∅; (TRef ∅ TUnit) ~ {♦}). 
apply t_app_fresh; auto.
unfold q_trans_tenv, q_trans''. simpl. apply t_abs; auto. 
repeat constructor; auto. constructor; auto. Qcrush. constructor; auto. constructor; auto. 1,2: Qcrush.
simp. repeat rewrite open_qual_empty_id'. repeat rewrite open_qual_bv_id; auto. repeat rewrite open_qual_qor_dist. rewrite open_qual_fresh_id. rewrite open_qual_bv_id; auto. rewrite open_qual_bv. 

(* apply 1 *)
replace ($! 1 ⊔ {♦}) with ((#! 1 ⊔ {♦}) <~ᵈ $!1; ({♦} ⊔ $!1)).
remember (TSRef ∅ TBot #! 0 (TSRef ∅ TBot #! 0 (TRef ∅ TUnit))) as R.
replace R with (R <~ᵀ TUnit ~ ∅; (TSRef ∅ (TRef ∅ TUnit) #!0 (TRef ∅ TUnit)) ~ ({♦} ⊔ $!1)) at 2.
apply t_app_fresh; subst.
unfold q_trans_tenv, q_trans''. simpl. apply t_abs; auto.
repeat constructor; auto. constructor; auto. 1,2: Qcrush.
constructor; auto. 1,2: Qcrush.
constructor; auto. constructor; auto. 1,2: Qcrush. constructor; auto. 1-4: Qcrush.
simp. repeat rewrite open_qual_empty_id'. repeat rewrite open_qual_bv_id; auto. repeat rewrite open_qual_qor_dist. rewrite open_qual_fresh_id. rewrite open_qual_bv_id; auto. rewrite open_qual_bv; auto. repeat rewrite open_qual_fv. 
2: {
  (* esacpe 1 *)
  (* replace (TSRef ∅ (TRef ∅ TUnit) #! 0 (TRef ∅ TUnit)) with (TSRef ∅ (TRef ∅ TUnit) ($!1 ⊖ $!1 ⊔ #! 0) (TRef ∅ TUnit)). *)
  replace (TSRef ∅ (TRef ∅ TUnit) #! 0 (TRef ∅ TUnit)) with (TSRef ∅ (TRef ∅ TUnit) (∅ ⊔ #! 0) (TRef ∅ TUnit)).
  eapply t_esc with (d:={♦}) (d1:=$!1) (d2:=$!1).
  apply qs_sq; auto.
  eapply closed_Qual_open''; eauto. Qcrush.
  unfold n_sub. intros. eauto.
  apply qs_sq; auto.
  rewrite open_qual_empty_id'. Qcrush.
  rewrite open_qual_empty_id'. Qcrush.
  apply qs_sq; auto. Qcrush. Qcrush.
  apply t_sref; auto. rewrite open_qual_fv. eapply t_var. simpl.  eauto. all: Qcrush.
}
(* apply 2 *)
remember (TSRef ∅ TBot #! 0 (TSRef ∅ TBot #! 0 (TRef ∅ TUnit))) as R.
replace ($! 3 ⊔ {♦}) with ((#! 1 ⊔ {♦}) <~ᵈ ($!3 ⊔ $!1); ({♦} ⊔ $!3)).
replace R with (R <~ᵀ TUnit ~ ∅; TSRef ∅ TBot #! 0 (TSRef ∅ TBot #! 0 (TRef ∅ TUnit)) ~ ({♦} ⊔ $!3)).
apply t_app_fresh; subst.
unfold q_trans_tenv, q_trans''. simpl. rewrite qor_assoc. repeat rewrite qor_idem'. repeat rewrite qor_empty_left. repeat rewrite qor_assoc. repeat rewrite qor_idem'. repeat rewrite qor_empty_right. apply t_abs; auto.
repeat constructor; auto. constructor; auto. 1,2: Qcrush.
constructor; auto. 1,2: Qcrush.
constructor; auto. 1,2: Qcrush. constructor; auto. 1-3: Qcrush. constructor; auto. Qcrush. rewrite <- qor_assoc. repeat rewrite qor_empty_left. 1,2: Qcrush. simpl. 1,2: Qcrush. simp. 
simp. repeat rewrite open_qual_empty_id'. repeat rewrite open_qual_bv_id; auto. repeat rewrite open_qual_qor_dist. rewrite open_qual_fresh_id. rewrite open_qual_bv_id; auto. rewrite open_qual_bv; auto. repeat rewrite open_qual_fv.
2: {
  (* escape *)
  replace (TSRef ∅ TBot #! 0 (TSRef ∅ TBot #! 0 (TRef ∅ TUnit))) with (TSRef ∅ TBot (∅ ⊔ #!0) (TSRef ∅ TBot #! 0 (TRef ∅ TUnit))).
  eapply t_esc with (d1:=$!3) (d2:=$!3) (d:={♦}).
  apply qs_sq; auto.
  eapply closed_Qual_open''; eauto. Qcrush.
  unfold n_sub. intros. eauto.
  apply qs_sq; auto.
  rewrite open_qual_empty_id'. Qcrush.
  rewrite open_qual_empty_id'. Qcrush.
  apply qs_sq; auto. Qcrush. Qcrush.
  eapply t_sub with (T1:=(TSRef $! 3 (TSRef ∅ (TRef ∅ TUnit) #! 0 (TRef ∅ TUnit)) $! 3 (TSRef ∅ (TRef ∅ TUnit) #! 0 (TRef ∅ TUnit)))) (d1:=({♦})); auto. apply t_sref; auto. rewrite open_qual_fv. eapply t_var. simpl.  eauto. 1,2: Qcrush. constructor; auto. 1-3: Qcrush. constructor; auto. all: Qcrush.
  apply s_sref; auto. 
  apply s_bot. constructor; auto. Qcrush. constructor; auto. 
  apply s_sref; auto. Qcrush. unfold n_sub. intros. eauto.
  apply qs_sq; auto. Qcrush.
  unfold n_sub. intros. eauto.
  Qcrush. Qcrush.
  apply qs_sq; auto. Qcrush.
  unfold n_sub. intros. eauto.
  apply qs_sq; auto. Qcrush.
  unfold n_sub. intros. eauto.
}
(* apply 3 *)
remember (TSRef ∅ TBot #! 0 (TSRef ∅ TBot #! 0 (TRef ∅ TUnit))) as R.
replace ($! 5 ⊔ {♦}) with ((#! 1 ⊔ {♦}) <~ᵈ $!5; $!5).
replace R with (R <~ᵀ TUnit ~ ∅; (TSRef ∅ TBot #! 0 (TSRef ∅ TBot #! 0 (TRef ∅ TUnit))) ~ $!5).
apply t_app; subst; auto. apply t_abs; auto. constructor; auto. 1,2: Qcrush. constructor; auto. constructor; auto. 1-3: Qcrush. constructor; auto. 1-3: Qcrush. subst. constructor; auto. constructor; auto. 1-4: Qcrush.
simp. repeat rewrite open_qual_empty_id'. repeat rewrite open_qual_bv_id; auto. repeat rewrite open_qual_qor_dist. rewrite open_qual_fresh_id. rewrite open_qual_bv_id; auto. rewrite open_qual_bv; auto. repeat rewrite open_qual_fv. 
eapply t_sub. eapply t_var.  simpl. eauto. 1,2: Qcrush. constructor; auto. constructor; auto. 1-3: Qcrush. apply stp_refl; auto. 
constructor; auto. constructor; auto. 1-2: Qcrush. constructor. 1-3: Qcrush.
eapply t_var. simpl. eauto. 1,2: Qcrush. 
constructor; auto. 
constructor; auto.
1-4: Qcrush.
all: subst; unfold not_free; eauto 3.
1,2: simp; repeat rewrite open_qual_qor_dist; rewrite open_qual_bv_id, open_qual_bv; auto.
unfold q_trans_tenv. simpl. rewrite <- qor_assoc. repeat rewrite qor_empty_left. repeat rewrite qor_assoc. repeat rewrite qor_idem'. Qcrush.
1,2: simp; repeat rewrite open_qual_qor_dist; rewrite open_qual_bv_id, open_qual_bv; auto.
unfold q_trans_tenv. simpl. rewrite <- qor_assoc. repeat rewrite qor_empty_left. repeat rewrite qor_assoc. repeat rewrite qor_idem'. Qcrush.
1-3: simp; repeat rewrite open_qual_qor_dist; rewrite open_qual_bv_id, open_qual_bv; auto.
Qed.

(*************************
*  Readonly References  *
*************************)

Definition f_read : tm := λ (tderef # 1).

Example typing_read : has_type [] ∅ [] f_read ({TSRef ∅ TBot ∅ TInt | {♦}} ==> {TInt | ∅}) ∅.
intros. unfold f_read. apply t_abs; auto. simp.
replace ([[1 ~> $! 1 ]]ᵈ ([[0 ~> $! 0 ]]ᵈ ∅)) with ([[0 ~> $! 1 ]]ᵈ ∅).
eapply t_sderef with (d1:=∅) (T1:=TBot); auto.
eapply t_var; auto. simpl. eauto. Qcrush. Qcrush. Qcrush.
Qed.

Definition writable_ref : tm := tsref (tnat 0).

Example typing_ref : has_type [] ∅ [] writable_ref (TSRef ∅ TInt ∅ TInt) {♦}.
intros. unfold writable_ref. apply t_sref. constructor; auto. constructor. Qcrush.
Qed.

Definition use_writable_as_readonly : tm := tapp f_read writable_ref.

Example use_writable_as_readonly_typable : 
  has_type [] ∅ [] use_writable_as_readonly TInt ∅.
unfold use_writable_as_readonly, f_read, writable_ref.
replace (∅) with (∅ <~ᵈ ∅ ; {♦}) at 2.
replace TInt with (TInt <~ᵀ TUnit ~ ∅; TSRef ∅ TBot ∅ TInt ~ {♦}).
apply t_app_fresh; auto.
apply t_abs; auto. 
simp. replace ([[1 ~> $! 1 ]]ᵈ ([[0 ~> $! 0 ]]ᵈ ∅)) with ([[0 ~> $!1 ]]ᵈ ∅). 
eapply t_sderef; auto. eapply t_var. simpl. eauto. Qcrush. Qcrush. constructor; auto. Qcrush. Qcrush.
eapply t_sub with (T1:=(TSRef ∅ TInt ∅ TInt)) (d1:={♦}); eauto. 
apply s_sref; auto. 1,2: unfold n_sub; auto. intros. 1-3: unfold not_free; auto. Qcrush. Qcrush.
Qed.

End escape.
