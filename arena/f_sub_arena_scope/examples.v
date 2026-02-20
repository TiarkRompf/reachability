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

Require Import examples_infra.

Import QualNotations.
Local Open Scope qualifiers.
Import OpeningNotations.
Local Open Scope opening.

(*
  Explanation for the encoding:
  - We use Local Nameless encoding for variables, #x are bound variables, $x are free variables
  - In the function body, #0 is always the self-reference, #1 is always the argument
  - tlet is a syntactic sugar, please see examples_infra.v
*)


(**************************************
*  Section 6.1: Callback Registration  *
**************************************)

Section callback.

(* the closure of makeHandler *)
Let makeHandler := tlet
    (tref tunit)                (* val rp = new Ref() *)
    (tabs (trefat #1 #3))       (* (cb) => new Ref(cb) at rp *)
.

Let makeHandlerType :=
    { {TUnit | ∅} ==> {TUnit | ∅} | ∅ } ==>
    { TRef ∅ ({TUnit | ∅} ==> {TUnit | ∅}) | #!0 }
    (* #!0 is the self-ref of the function closure, i.e. makeHandler *)
.

(* fresh and bound to some binding *)
(*
  The qualifier is fresh, because it is not yet bound to a variable
    i.e. val 'makeHandler' = makeHandler;
  The closure captures a fresh arena, so we mark it as fresh
*)
Example makeHandler_typable_static :
  has_type_static [] {♦} makeHandler makeHandlerType {♦}.
Proof.
  unfold makeHandler. unfold makeHandlerType. unfold tlet.
  replace (({{TUnit | ∅} ==> {TUnit | ∅} | ∅}
      ==> {TRef ∅ ({TUnit | ∅} ==> {TUnit | ∅}) | #! 0})) with (({{TUnit | ∅} ==> {TUnit | ∅} | ∅}
      ==> {TRef ∅ ({TUnit | ∅} ==> {TUnit | ∅}) | #! 0}) <~ᵀ TUnit ~ ∅ ; TRef ∅ TUnit ~ {♦} ). 2: auto.
  replace ({♦}) with (#!1 <~ᵈ ∅ ; {♦}) at 3. 2: simps; auto.
  eapply ts_app_fresh; auto.
  eapply ts_abs; auto. repeat constructor; auto. constructor. Qcrush. Qcrush. constructor; auto. constructor; auto. Qcrush.
  simps. eapply ts_abs; auto. constructor; auto. Qcrush. Qcrush. Qcrush.
  simps. eapply ts_refat; auto. simps. eapply ts_var_lookup; simpl; auto. eapply ts_var; simpl; eauto. Qcrush. Qcrush.
  simps. eapply ts_sub with (d1 := $!1). eapply ts_var; simpl; eauto. Qcrush. eapply stp_refl. constructor; auto.
    eapply qs_trans with (d2:= ($!1 ⊔ $!2)). eapply qs_sq; Qcrush. eapply qs_self. simpl. eauto. Qcrush. Qcrush. Qcrush.
  1-2: auto. constructor. constructor. Qcrush.
Qed.

Example makeHandler_typable :
  has_type [] {♦} [] makeHandler makeHandlerType {♦}.
Proof.
  apply static_typing. apply makeHandler_typable_static.
Qed.


Let callbackRegistration :=
  tlet                          (* val makeHandler = ... *)
    makeHandler
    (tapp (#1) (tabs tunit))    (* makeHandler(x => ()) , f is inlined *)
.

(* we don't have Int here, so the function f is encoded as Unit => Unit *)
Example callbackRegistration_typable_static :
  has_type_static [] {♦} callbackRegistration (TRef ∅ ({TUnit | ∅} ==> {TUnit | ∅})) {♦}.
Proof.
  unfold callbackRegistration. unfold tlet.
  (* substitute the closure *)
  replace ({♦}) with (#!1 <~ᵈ ∅ ; {♦}) at 2. 2: unfold openq; simps; auto.
  replace ((TRef ∅ ({TUnit | ∅} ==> {TUnit | ∅}))) with ((TRef ∅ ({TUnit | ∅} ==> {TUnit | ∅})) <~ᵀ TUnit ~ ∅ ; makeHandlerType ~ {♦}). 2: auto.
  apply ts_app_fresh. 2: apply makeHandler_typable_static; auto.
  eapply ts_sub with (d1 := ∅); auto. 2: {eapply stp_refl; auto. constructor; auto. Qcrush. constructor; auto. Qcrush. }
  simps. apply ts_abs. Qcrush. constructor; auto. Qcrush. constructor; auto. 1-2: Qcrush. Qcrush. Qcrush. Qcrush.
  simps. unfold q_trans_tenv; simpl. replace (∅ ⋒ {♦}) with ({♦}). 2: Qcrush.
  (* apply makeHandler ($1) to f *)
  replace ($!1) with (#!0 <~ᵈ $!1 ; ∅ ) at 2. 2: { unfold openq. apply Q_lift_eq. Qcrush. }
  replace ((TRef ∅ ({TUnit | ∅} ==> {TUnit | ∅}))) with ((TRef ∅ ({TUnit | ∅} ==> {TUnit | ∅})) <~ᵀ TUnit ~ ∅ ; ({TUnit | ∅} ==> {TUnit | ∅}) ~ ∅ ) at 2. 2: auto.
  apply ts_app; auto. eapply ts_var; auto. simpl. unfold makeHandlerType. eauto. Qcrush. Qcrush. constructor; auto. Qcrush.
  apply ts_abs; auto. Qcrush. simps. constructor; auto. Qcrush.
  Qcrush. constructor. intros; constructor. constructor. Qcrush. unfold q_trans_tenv; auto.
Qed.

Example callbackRegistration_typable :
  has_type [] {♦} [] callbackRegistration (TRef ∅ ({TUnit | ∅} ==> {TUnit | ∅})) {♦}.
Proof.
  apply static_typing. apply callbackRegistration_typable_static.
Qed.

End callback.


(**************************************
*  Section 6.2: Multi-Hop Recursion  *
**************************************)

Section three_hop.

Let multi_hop :=
  twithr tunit (                                    (* val a = new Ref() scoped *)
    tlet (tabs tunit)                               (* val f = (x:unit) => unit *)
    (tlet (trefat #1 #3)                            (* val c1 = new Ref(f) at a *)
      (tlet (trefat #3 #5)                          (* val c2 = new Ref(f) at a *)
        (tlet (trefat #5 #7)                        (* val c3 = new Ref(f) at a *)
          (* now c1 = #5, c2 = #3, c3 = #1, in body + 2 *)
          (
            (tassign #5 (tabs (tapp (tderef #5) #1))) ;  (* c1 := (x) => (!c2)(x) *)
            (* now c1 = #7, c2 = #5, c3 = #3*)
            ((tassign #5 (tabs (tapp (tderef #5) #1))) ; (* c2 := (x) => (!c3)(x) *)
            (* now c1 = #9, c2 = #7, c3 = #5 *)
            (tassign #5 (tabs (tapp (tderef #11) #1))))  (* c3 := (x) => (!c1)(x) *)
          )
        )
      )
    )
  ).

Let TF := TFun ∅ ∅ TUnit TUnit.

Lemma multi_hop_typable : has_type [] ∅ [] multi_hop TUnit ∅.
Proof.
  eapply static_typing. unfold multi_hop.
  eapply ts_withr. eapply ts_base. auto. auto. auto. auto. repeat constructor; auto.
  unfold tlet. simps.
  replace (TUnit) with (TUnit <~ᵀ TUnit ~ ∅ ; TF ~ $!1 ) at 3 by auto. replace (∅) with (∅ <~ᵈ $!1 ; $!1 ) at 4 by auto.
  eapply ts_app; auto. simps. 2:{ eapply ts_abs; eauto. Qcrush. Qcrush. simps. apply ts_base. Qcrush. }
  eapply ts_abs; eauto. repeat constructor; auto. constructor. 1-2: Qcrush. 1-2: constructor; auto. Qcrush. 2: constructor. simps.
  replace (TUnit) with (TUnit <~ᵀ TUnit ~ ∅ ; TRef $!1 (TF) ~ ($!1)) at 4. 2: auto.
    replace (∅) with (∅ <~ᵈ ($!1 ⊔ $!3) ; ($!1)) by auto.
  eapply ts_app; auto. 3: constructor. 2:{ simps. eapply ts_refat; auto. eapply ts_var_lookup. simpl; eauto. all: auto. constructor; auto. Qcrush. eapply ts_var. simpl; eauto. Qcrush. Qcrush. constructor; auto. Qcrush.
    eapply ts_sub. eapply ts_var. simpl; eauto. Qcrush. Qcrush. constructor; auto. Qcrush.
    eapply stp_refl. constructor; auto. eapply qs_sq; eauto. Qcrush. Qcrush.
    }
  eapply ts_abs; eauto. repeat constructor; auto. constructor; auto. Qcrush. constructor; auto. constructor. 1-2: Qcrush. 1-2: constructor; auto. Qcrush. Qcrush. Qcrush. simps.
  (* === *)
  replace (TUnit) with (TUnit <~ᵀ TUnit ~ ∅ ; TRef $!1 (TF) ~ $!1) at 5. 2: auto.
    replace (∅) with (∅ <~ᵈ ($!1 ⊔ $!3 ⊔ $!5); $!1) by auto.
  eapply ts_app; auto. 3: constructor. 2:{ simps. eapply ts_refat; auto. eapply ts_var_lookup. simpl; eauto. all: auto. constructor; auto. Qcrush. Qcrush. eapply ts_var. simpl; eauto. Qcrush. Qcrush. constructor; auto. Qcrush.
  eapply ts_var. simpl; eauto. Qcrush. Qcrush. constructor; auto. Qcrush. }
  eapply ts_abs; eauto. repeat constructor; auto. constructor; auto. Qcrush. constructor; auto. constructor; auto. Qcrush. Qcrush. 1-2: Qcrush. simps.
  (* === *)
  replace (TUnit) with (TUnit <~ᵀ TUnit ~ ∅ ; TRef $!1 (TF) ~ $!1) at 6. 2: auto.
    replace (∅) with (∅ <~ᵈ ($!1 ⊔ $!3 ⊔ $!5 ⊔ $!7); $!1) by auto.
  eapply ts_app; auto. 3: constructor. 2:{ simps. eapply ts_refat; auto. eapply ts_var_lookup. simpl; eauto. all: auto. constructor; auto. Qcrush. Qcrush. eapply ts_var. simpl; eauto. Qcrush. Qcrush. constructor; auto. Qcrush.
    eapply ts_var. simpl; eauto. Qcrush. Qcrush. constructor; auto. Qcrush. }
  simps. eapply ts_abs; eauto. repeat constructor; auto. constructor; auto. Qcrush. constructor; auto. constructor; auto. Qcrush. Qcrush. 1-2: Qcrush. simps.
  (* ====  assignment *)
  simps. replace (TUnit) with (TUnit <~ᵀ TUnit ~ ∅ ; TUnit ~ ∅) at 7. 2: auto.
    replace (∅) with (∅ <~ᵈ ($!1 ⊔ $!3 ⊔ $!5 ⊔ $!7 ⊔ $!9); ∅) by auto.
  eapply ts_app; eauto. 3: constructor. 2:{ simps. eapply ts_assign with (d1:=$!1). eapply ts_var_lookup. simpl. eauto. constructor. constructor; auto. 1-4: Qcrush.
    eapply ts_var. simpl; eauto. Qcrush. Qcrush. constructor; auto. constructor; auto. 1-2: Qcrush.
    eapply ts_sub with (d1:=$!1 ⊔ $!7). 2:{ eapply stp_refl. constructor; auto. replace ($!1) with ($!1 ⊔ $!1) at 20. apply qs_cong. eapply qs_qvar. simpl. eauto.  Qcrush. constructor. constructor; auto. Qcrush. Qcrush. Qcrush. Qcrush. apply qor_idem. } 2: Qcrush. 2: Qcrush.
    eapply ts_abs; eauto. repeat constructor; auto. Qcrush. Qcrush. simps.
    replace TUnit with (TUnit <~ᵀ TUnit ~ ∅ ; TUnit ~ ∅) at 10 by auto. replace (∅) with (∅ <~ᵈ $!1 ; ∅ ) by auto.
    eapply ts_app. auto. eapply ts_deref. simps. eapply ts_var. simpl. eauto. Qcrush. Qcrush. constructor; Qcrush. Qcrush. Qcrush. Qcrush.
    simps. eapply ts_var_lookup; auto. simpl; eauto. eapply ts_var; simpl; eauto. Qcrush. Qcrush. Qcrush. Qcrush. constructor.
    }
  simps. eapply ts_abs. repeat constructor; eauto. constructor; auto. Qcrush. Qcrush. Qcrush. Qcrush.
  (* ======= *)
  simps. replace (TUnit) with (TUnit <~ᵀ TUnit ~ ∅ ; TUnit ~ ∅) at 10. 2: auto.
    replace (∅) with (∅ <~ᵈ ($!1 ⊔ $!3 ⊔ $!5 ⊔ $!7 ⊔ $!9); ∅) by auto.
  eapply ts_app; eauto. 3: constructor. 2:{ simps. eapply ts_assign with (d1:=$!1). eapply ts_var_lookup. simpl. eauto. constructor. constructor; auto. 1-4: Qcrush.
    eapply ts_var. simpl; eauto. Qcrush. Qcrush. constructor; auto. constructor; auto. 1-2: Qcrush.
    eapply ts_sub with (d1:=$!1 ⊔ $!9). 2:{ eapply stp_refl. constructor; auto. replace ($!1) with ($!1 ⊔ $!1) at 21. apply qs_cong. eapply qs_qvar. simpl. eauto.  Qcrush. constructor. constructor; auto. Qcrush. Qcrush. Qcrush. Qcrush. apply qor_idem. } 2: Qcrush. 2: Qcrush.
    eapply ts_abs; eauto. repeat constructor; auto. Qcrush. Qcrush. simps.
    replace TUnit with (TUnit <~ᵀ TUnit ~ ∅ ; TUnit ~ ∅) at 13 by auto. replace (∅) with (∅ <~ᵈ $!1 ; ∅ ) by auto.
    eapply ts_app. auto. eapply ts_deref. simps. eapply ts_var. simpl. eauto. Qcrush. Qcrush. constructor; Qcrush. Qcrush. Qcrush. Qcrush.
    simps. eapply ts_var_lookup; auto. simpl; eauto. eapply ts_var; simpl; eauto. Qcrush. Qcrush. Qcrush. Qcrush. constructor.
    }
  simps. eapply ts_abs. repeat constructor; eauto. constructor; auto. Qcrush. Qcrush. Qcrush. Qcrush. simps.
  (* ======= *)
  eapply ts_assign with (d1:=$!1). eapply ts_var_lookup. simpl. eauto. constructor. constructor; auto. 1-4: Qcrush.
  eapply ts_var. simpl; eauto. Qcrush. Qcrush. constructor; auto. constructor; auto. 1-2: Qcrush.
  eapply ts_sub with (d1:=$!1 ⊔ $!5). 2:{ eapply stp_refl. constructor; auto. replace ($!1) with ($!1 ⊔ $!1) at 22. apply qs_cong. eapply qs_qvar. simpl. eauto.  Qcrush. constructor. constructor; auto. Qcrush. Qcrush. Qcrush. Qcrush. apply qor_idem. } 2: Qcrush. 2: Qcrush.
  eapply ts_abs; eauto. repeat constructor; auto. Qcrush. Qcrush. simps.
  replace TUnit with (TUnit <~ᵀ TUnit ~ ∅ ; TUnit ~ ∅) at 16 by auto. replace (∅) with (∅ <~ᵈ $!1 ; ∅ ) by auto.
  eapply ts_app. auto. eapply ts_deref. simps. eapply ts_var. simpl. eauto. Qcrush. Qcrush. constructor; Qcrush. Qcrush. Qcrush. Qcrush.
  simps. eapply ts_var_lookup; auto. simpl; eauto. eapply ts_var; simpl; eauto. Qcrush. Qcrush. Qcrush. Qcrush. constructor.
Qed.

End three_hop.