Require Export PeanoNat.
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
Require Import f_sub_diamond.
Require Import examples_infra.

Require Import NatSets.
Require Import setfacts.
Import NatSet.F.

Import OpeningNotations.
Local Open Scope opening.
Import QualNotations.
Local Open Scope qualifiers.

(* This file demonstrates the pair data type based on Church encodings. We encode both _transparent_ and _opaque_ pairs.
   The former kind is used if the stored data reaches known resources in the context, whereas the latter can be used to
   return data capturing out-of-scope resources.

   As a warmup for opaque Church pairs, we recommend reviewing examples_cell_opaque.v first. *)

(* We make use of a few notations to make function and universal types more palatable: *)

Notation " { a | b } ==> { c | d }"  := (TFun b d a c)
(at level 10, format "'[' '[hv' '{' a  '/' '|'  b '}' ']' '/  '  '==>'  '[hv' '{' c  '/' '|'  d '}' ']' ']'").

Notation "∀<:{ a | b }.{ c | d }"  := (TAll b d a c)
(at level 10, format "'[' '[hv' '∀<:{' a  '/' '|'  b '}.{' ']' '/  '  '[hv' c  '/' '|'  d '}' ']' ']'").

Notation "⊤" := TTop.

(* shorthand if upper bound is the top type *)
Notation "∀<:{ a }.{ c | d }" := (TAll a d ⊤ c) (at level 10, only parsing).
(* even shorter *)
Notation "∀.{ c | d }" := (TAll {♦} d ⊤ c) (at level 10, only parsing).

Section DerivedSyntax.

  (* Let bindings as macros for abstraction and application. Due to this encoding, the let-bound variable's
     deBruijn index is #1, since the implicit function self reference is bound to #0.
  *)
  Definition tlet (t1 t2 : tm): tm := (tapp (tabs t2) t1).

  (* the typing rule combines the tabs and t_app_fresh cases (we could also have a non-fresh version) *)
  Lemma t_let_fresh : forall Γ φ df df' Σ t1 T1 q1 q1' t2 T2 q2,
    closed_tm 2 (length Γ) (length Σ) t2 ->
    closed_ty 0 (‖Γ‖) (‖Σ‖) (TFun q1 q2 T1 T2) ->
    closed_qual 2 (length Γ) (length Σ) q2 ->
    closed_qual 0 (length Γ) (length Σ) df ->
    has_type Γ φ Σ t1 T1 q1 ->
    q1 ⊑ q1' ->
    df ⊑ df' ->
    q1' ⊑ φ ->
    df' ⊑ φ ->
    df ⊑ φ ->
    (q2 <~ᵈ ∅ ; ∅) ⊑ φ ->
    ♦∉ df ->
    senv_saturated Σ df ->
    saturated Γ Σ df' ->
    saturated Γ Σ q1' ->
    senv_saturated Σ (q2 <~ᵈ ∅ ; ∅) ->
    not_free 0 T2 ->
    (♦∈ q1 -> not_free 1 T2) ->
    has_type (bind_tm(false, T1, (df' ⋒ q1')) :: bind_tm(true, {T1 | df' ⋒ q1'} ==> {T2 | q2}, df):: Γ) (df ⊔ $!(S (length Γ)) ⊔ {♦}) Σ (open_tm' Γ t2) (open_ty' Γ T2) (openq' Γ q2) ->
    has_type Γ φ Σ (tlet t1 t2) (T2 <~ᵀ TUnit ~ ∅ ; T1 ~ q1) (q2 <~ᵈ df ; q1).
  Proof.
    intros. unfold tlet. specialize (has_type_closed H3). intuition.
    eapply t_app_fresh with (d1':=q1') (df':=df'); ccrush.
    apply t_abs; ccrush. constructor; ccrush. inversion H0; subst. auto.
    unfold_open in H17. simpl in H17.
    eapply @weaken_flt with (φ:=df ⊔ $! (S (length Γ)) ⊔ {♦}); ccrush.
  Qed.

  Lemma open_tlet : forall {k t t1 t2}, open_rec_tm k t (tlet t1 t2) = (tlet (open_rec_tm k t t1) (open_rec_tm (S (S k)) t t2)).
  Proof.
    intros. unfold tlet. simpl. auto.
  Qed.

End DerivedSyntax.


(* Church pairs *)
(* Pair introduction: ΛA.ΛB.λx:A.λy:B.ΛC.λf.f x y *)
Example pair_mk := (ttabs (ttabs (tabs (tabs (ttabs (tabs (tapp (tapp #1 #7) #5))))))).
(* Pair destructors *)
(* fst = ΛA.ΛB.λp.p[A](x => y => x) *)
Example fst := (ttabs (ttabs (tabs (tapp (ttapp #1) (tabs (tabs #3)))))).
(* snd = ΛA.ΛB.λp.p[B](x => y => y)*)
Example snd := (ttabs (ttabs (tabs (tapp (ttapp #1) (tabs (tabs #1)))))).

Section PairTransparent.

  (* We first cover the _transparent_ pairs, which support precise data extraction thanks to type-and-qualifier polymorphism (paper Section 2.4).

     Pair[A^a,B^b] := ∀C^c<:⊤^a,b♦. (((x : A^a) -> ((y : B^b) -> C^c)^x)^{} -> C^c)^c,a,b

     Ignoring qualifiers, this type corresponds to the standard Church encoding in System F(sub).

     As explained in the paper, type-and-qualifier abstraction permits precise eliminations:

     p : Pair[A^a, B^b]^{a,b}
     p[A^a] : (((x : A^a) -> ((y : B^b) -> A^a)^x)^{} -> A^a)^a,b
     p[B^b] : (((x : A^a) -> ((y : B^b) -> B^b)^x)^{} -> B^b)^a,b

     It is important to permit the bound C^c<:⊤^a,b♦ so that the instantiation for c can overlap with a and b. Otherwise, it is impossible
     to instantiate the pair's elimination to A^a and B^b respectively.
  *)

  Variables (Γ : tenv) (φ : qual) (Σ : senv).
  Context (phiwf : closed_qual 0 (‖Γ‖) (‖Σ‖) φ).

  (* Pair[A^a,B^b] := ∀C^c<:⊤^a,b♦. (((x : A^a) -> ((y : B^b) -> C^c)^x)^{} -> C^c)^c,a,b
     Note: the number attached to each parameter indicates by how much it must be incremented if it is a deBruijn index.
    *)
  Example TPair A2 a0 a2 B4 b0 b2 b4 := ∀<:{ a0 ⊔ b0 ⊔ {♦} }.{ {{A2 | a2} ==> {{B4 | b4} ==> { #5 | #!5 } | #!1} | ∅ } ==> {#3 | #!3} | #!1 ⊔ a2 ⊔ b2 }.

  (* The transparent pair introduction's type:
     pair_mk: (∀A^a<:⊤^♦. (∀B^b<:⊤^a,♦. ( (x : A^a) -> ((y : B^b) -> (Pair[A^x,B^y])^x,y)^x))^∅)^∅
     Again, overlap is important here. We generally want to allow overlapping pair components, which is why the bound for b mentions a.
     If we didn't include this, then we could construct strictly disjoint pairs.
   *)
  Example t_pair1_ :
    has_type [] ∅ [] pair_mk (∀.{ ∀<:{ #♦1 }.{ {#3 | #!3} ==> {{#3 | #!3 } ==> (*A: #7, B: #5, x:#3, y:#1*) {TPair #9 #!3 #!5 #9 #!1 #!3 #!5 | (#!3 ⊔ #!1) } | #!1 } | ∅} | ∅ }) ∅.
    unfold pair_mk.
    apply t_tabs; ccrush. unfold TPair. ccrush. (* 0/1*)
    apply t_tabs; ccrush. (* 2/3 *)
    apply t_abs; ccrush. (* 4/5 *)
    apply t_abs; ccrush. (* 6/7 *)
    apply t_tabs; ccrush. (* 8/9 *)
    apply t_abs; ccrush.  (* 10/11 *)
    change_qual (openq $!5 $!7 $!9).
    change_type (open_ty TUnit (∅) ($3) $!7 $9).
    apply t_app; ccrush.
    * change_qual (openq $!11 $!5 #!1).
      change_type (open_ty TUnit (∅) $1 $!5 ({$ 3 | $! 7} ==> {$ 9 | $! 9})).
      apply t_app; ccrush.
      + eapply t_var; ccrush.
      + eapply t_sub. eapply t_var; ccrush.
        apply stp_refl; ccrush. apply qs_sq; ccrush. all : ccrush.
    * eapply t_var; ccrush.
  Qed.

  (* generalize to all contexts *)
  Example t_pair1 :
    has_type Γ φ Σ pair_mk (∀.{ ∀<:{ #♦1 }.{ {#3 | #!3} ==> {{#3 | #!3 } ==> (*A: #7, B: #5, x:#3, y:#1*) {TPair #9 #!3 #!5 #9 #!1 #!3 #!5 | (#!3 ⊔ #!1) } | #!1 }  | ∅ } | ∅ }) ∅.
    eapply weaken'. eapply weaken_store. apply t_pair1_. all : auto.
  Qed.

  (* Assert that the projection functions are compatible with each pair type (and extract the precise component qualifier!) *)
  (* fst : (∀A^a<:⊤^♦. (∀B^b<:⊤^a,♦. (Pair1[A^a,B^b]^{a,b,♦} -> A^a)^a,b)^a)^∅ *)
  Example t_fst1_ :
    has_type [] ∅ [] fst (∀.{ ∀<:{ #♦1 }.{ {TPair #5 #!3 #!5 #5 #!1 #!3 #!5 | #!1 ⊔ #!3 ⊔ {♦} } ==> { #5 | #!5 } | #!1 ⊔ #!3 } | #!1 }) ∅.
    unfold fst.
    apply t_tabs; ccrush. unfold TPair. ccrush.
    apply t_tabs; ccrush.
    apply t_abs; ccrush.
    change_qual (openq (qset false (union (singleton 1) (singleton 3)) {}N {}N) (∅) $!1).
    change_type (open_ty TUnit (∅) ({$ 1 | $! 1} ==> {{$ 3 | $! 3} ==> {$1 | $! 1} | #!1}) (∅) $1).
    apply t_app; ccrush.
    * change_qual (openq ($!5) $!1 (qset false (union (singleton 1) (singleton 3)) (singleton 1) {}N)).
      change_type (open_ty TUnit ∅ $1 $!1 ({{$ 1 | $! 1} ==> {{$ 3 | $! 3} ==> {# 5 | #! 5} | #! 1} | ∅} ==> {# 3 | #! 3})).
      eapply t_tapp_fresh with (d1':=$♦1) (df':=$♦1 ⊔ $♦3 ⊔ $♦5) ; try solve [ccrush].
      dom_equals ($♦ 1).
      eapply t_sub.
      eapply t_var; ccrush.
      apply s_all. ccrush. ccrush.
      apply qs_sq; ccrush.
      eapply s_tvar_trans; ccrush. cleanup. apply stp_refl; ccrush. apply qs_sq; ccrush.
      simpl. intuition. ccrush. auto.
      ccrush. econstructor. unfold tenv_saturated. intros.
      simpl in H. apply union_1 in H. destruct H. apply NatSetFacts.singleton_iff in H. subst.
      try solve [eapply sat_tvar; ccrush].
      apply union_1 in H; destruct H; apply NatSetFacts.singleton_iff in H; subst;
        try solve [eapply sat_tvar; ccrush].
      try solve [eapply sat_var; ccrush].
      ccrush.
    * eapply t_sub with (T1 := {$ 1 | $! 1} ==> {{$ 3 | $! 3} ==> { $1 | #!3 } | #! 1}) (d1:= ∅). 3,4: ccrush.
      - apply t_abs; ccrush.
        apply t_abs; ccrush.
        eapply t_var; ccrush.
      - apply s_fun; ccrush.
        apply stp_refl; ccrush. apply qs_sq; ccrush.
        apply s_fun; ccrush. apply qs_sq; ccrush.
        apply stp_refl; ccrush. apply qs_sq; ccrush.
        apply stp_refl; ccrush. eapply qs_qvar; ccrush.
  Qed.

  Example t_fst1 :
    has_type Γ φ Σ fst (∀.{ ∀<:{ #♦1 }.{ {TPair #5 #!3 #!5 #5 #!1 #!3 #!5 | #!1 ⊔ #!3 ⊔ {♦} } ==> { #5 | #!5 } | #!1 ⊔ #!3 } | #!1 }) ∅.
    eapply weaken'. eapply weaken_store. apply t_fst1_. all : auto.
  Qed.

  (* snd : (∀A^a<:⊤^♦. (∀B^b<:⊤^{a,♦}. (Pair1[A^a,B^b]^{a,b,♦} -> B^b)^a,b)^a)^∅ *)
  Example t_snd1_ :
    has_type [] ∅ [] snd (∀.{  ∀<:{ #♦1 }.{ {TPair #5 #!3 #!5 #5 #!1 #!3 #!5 | #!1 ⊔ #!3 ⊔ {♦} } ==> { #3 | #!3 } | #!1 ⊔ #!3 } | #!1 }) ∅.
    unfold snd.
    apply t_tabs; ccrush. unfold TPair. ccrush.
    apply t_tabs; ccrush.
    apply t_abs; ccrush.
    change_qual (openq (qset false (union (singleton 1) (singleton 3)) {}N {}N) (∅) $!3).
    change_type (open_ty TUnit (∅) ({$ 1 | $! 1} ==> {{$ 3 | $! 3} ==> {$3 | $! 3} | #!1}) (∅) $3).
    apply t_app; ccrush.
    * change_qual (openq ($!5) $!3 (qset false (union (singleton 1) (singleton 3)) (singleton 1) {}N)).
      change_type (open_ty TUnit ∅ $3 $!3 ({{$ 1 | $! 1} ==> {{$ 3 | $! 3} ==> {# 5 | #! 5} | #! 1} | ∅} ==> {# 3 | #! 3})).
      eapply t_tapp_fresh with (d1':=$♦1 ⊔ $♦3) (df':=$♦1 ⊔ $♦3 ⊔ $♦5) ; try solve [ccrush].
      dom_equals ($♦1 ⊔ $♦3).
      eapply t_sub.
      eapply t_var; ccrush.
      apply s_all. ccrush. ccrush.
      apply qs_sq; ccrush.
      eapply s_tvar_trans; ccrush. cleanup. apply stp_refl; ccrush. apply qs_sq; ccrush.
      simpl. intuition. ccrush. auto.
      econstructor; ccrush; unfold tenv_saturated; intros;
      simpl in H; apply union_1 in H; destruct H; apply NatSetFacts.singleton_iff in H; subst;
        try solve [eapply sat_tvar; ccrush].
      econstructor; ccrush; unfold tenv_saturated; intros;
      simpl in H; apply union_1 in H; destruct H. apply NatSetFacts.singleton_iff in H; subst;
        try solve [eapply sat_tvar; ccrush].
      apply union_1 in H. destruct H; apply NatSetFacts.singleton_iff in H; subst;
        try solve [eapply sat_tvar; ccrush]; try solve [eapply sat_var; ccrush].
    * eapply t_sub with (T1 := {$ 1 | $! 1} ==> {{$ 3 | $! 3} ==> { $3 | #!1 } | #! 1}) (d1:= ∅). 3,4: ccrush.
      - apply t_abs; ccrush.
        apply t_abs; ccrush.
        eapply t_var; ccrush.
      - apply s_fun; ccrush.
        apply stp_refl; ccrush. apply qs_sq; ccrush.
        apply s_fun; ccrush. apply qs_sq; ccrush.
        apply stp_refl; ccrush. apply qs_sq; ccrush.
        apply stp_refl; ccrush. eapply qs_qvar; ccrush.
  Qed.

  Example t_snd1 :
    has_type Γ φ Σ snd (∀.{  ∀<:{ #♦1 }.{ {TPair #5 #!3 #!5 #5 #!1 #!3 #!5 | #!1 ⊔ #!3 ⊔ {♦} } ==> { #3 | #!3 } | #!1 ⊔ #!3 } | #!1 }) ∅.
    eapply weaken'. eapply weaken_store. apply t_snd1_. all : auto.
  Qed.

End PairTransparent.

Section PairTransparentUse.

  (* a usage example over some arbitrary component types *)

  Variables (Γ : tenv) (φ : qual) (Σ : senv).
  Context (phiwf : closed_qual 0 (‖Γ‖) (‖Σ‖) φ).

  Context (A B : ty)
          (a b : qual)
          (nf_a  : ♦∉ a)
          (nf_b  : ♦∉ b)
          (sat_a : saturated Γ Σ (a ⊔ {♦}))
          (sat_b : saturated Γ Σ (b ⊔ {♦}))
          (cl_a : closed_qual 0 (length Γ) (length Σ) a)
          (cl_b : closed_qual 0 (length Γ) (length Σ) b)
          (cl_A : closed_ty 0 (length Γ) (length Σ) A)
          (cl_B : closed_ty 0 (length Γ) (length Σ) B)
          (a_obs : a ⊑ φ)
          (b_obs : b ⊑ φ)
          (phi_fr : {♦} ⊑ φ).

  (* Elimination on TPair *)
  Example inst_fst1 : has_type Γ φ Σ (ttapp (ttapp fst)) ({(TPair A a a B b b b) | a ⊔ b ⊔ {♦}} ==> { A | a }) (a ⊔ b).
    unfold TPair.
    change_qual (openq a b (a ⊔ #!1)).
    change_type (open_ty TUnit ∅ B b (
      {∀<:{⊤ | a ⊔ #!1 ⊔ {♦}}.{
        {{A | a} ==> {{#5 | #!5} ==> {# 5 | #! 5} | #! 1} | ∅} ==> {# 3 | #! 3} | #! 1 ⊔ a ⊔ #!3}
          | a ⊔ #!1 ⊔ {♦}} ==> {A | a})).
    apply t_tapp_fresh with (d1':=b ⊔ {♦}) (df':=a ⊔ {♦}); try solve [ccrush].
    (* change bound *)
    apply t_sub with (d1:=a) (T1:=(∀<:{⊤ | a ⊔ {♦}}.{
      {∀<:{⊤ | a ⊔ #! 1 ⊔ {♦}}.{
          {{A | a} ==> {{# 5 | #! 5} ==> {# 5 | #! 5} | #! 1} | ∅} ==> {# 3 | #! 3} | #! 1 ⊔ a ⊔ #! 3}
      | a ⊔ #! 1 ⊔ {♦}} ==> {A | a}
      | a ⊔ #! 1})); auto.
    * change_qual (openq ∅ a #!1).
      change_type (open_ty TUnit ∅ A a (∀<:{⊤ | #!1 ⊔ {♦}}.{
        {∀<:{⊤ | #!3 ⊔ #! 1 ⊔ {♦}}.{
            {{#5 | #!5} ==> {{# 5 | #! 5} ==> {# 5 | #! 5} | #! 1} | ∅} ==> {# 3 | #! 3} | #! 1 ⊔ #!5 ⊔ #! 3}
                      | #!3 ⊔ #! 1 ⊔ {♦}} ==> {#5 | #!5} | #!3 ⊔ #! 1})).
      apply t_tapp_fresh with (d1':=a ⊔ {♦}) (df':=∅); try solve [ccrush].
      dom_equals ({♦}).
      (* change bound *)
      replace (#! 1 ⊔ {♦}) with (#♦1) at 1; try solve [ccrush].
      replace (#! 3 ⊔ #! 1 ⊔ {♦}) with (#!1 ⊔ #!3 ⊔ {♦}) at 1; try solve [ccrush].
      replace (#! 3 ⊔ #! 1) with (#!1 ⊔ #!3) at 1; try solve [ccrush].
      eapply t_sub. eapply t_fst1. auto. unfold TPair. auto.
      apply s_all. 1-4: ccrush. apply stp_refl; ccrush. apply qs_sq; ccrush. auto. auto. qual_destruct. ccrush.
      intros. rewrite nf_a in H. discriminate. eauto.
      inversion cl_a. inversion cl_b. subst. apply bound_0_empty in H0, H7. simpl in nf_a, nf_b. subst. ccrush.
    * apply s_all. inversion cl_a. inversion cl_b. subst. apply bound_0_empty in H0, H7. simpl in nf_a, nf_b. subst. ccrush.
      constructor. ccrush. constructor; ccrush. bound_simpl. lia. ccrush. constructor; ccrush.
      constructor; ccrush. bound_simpl. lia. constructor; ccrush. constructor; ccrush. bound_simpl. lia.
      constructor; ccrush. bound_simpl. lia.
      inversion cl_a. inversion cl_b. subst. apply bound_0_empty in H0, H7. simpl in nf_a, nf_b. subst. ccrush.
      constructor. ccrush. constructor; ccrush. eapply Nat.le_trans. eapply inter_bound_min. lia. bound_simpl. lia.
      eapply Nat.le_trans. eapply inter_bound_min. lia. constructor; ccrush. bound_simpl. lia. ccrush.
      constructor; ccrush. constructor; ccrush. bound_simpl. lia. constructor; ccrush. constructor; ccrush.
      bound_simpl. lia. constructor; ccrush. bound_simpl. lia. ccrush. ccrush.
      apply stp_refl. qual_destruct. inversion cl_a. inversion cl_b. subst. apply bound_0_empty in H17, H7. simpl in nf_a, nf_b. subst. ccrush.
      constructor. ccrush. constructor; ccrush. bound_simpl. lia. bound_simpl. lia. ccrush.
      constructor; ccrush. constructor; ccrush. 1,2 : bound_simpl; lia. constructor; ccrush. 1,2: bound_simpl; lia. ccrush.
      apply qs_sq; ccrush.
    * eauto.
    * qual_destruct. inversion cl_a. inversion cl_b. subst. apply bound_0_empty in H7, H17. simpl in nf_a, nf_b. subst. ccrush.
    * intros. rewrite nf_b in H. discriminate.
    * opening. eauto.
    * eauto.
    * qual_destruct. inversion cl_a. inversion cl_b. subst. apply bound_0_empty in H7, H17. simpl in nf_a, nf_b. subst. ccrush.
  Qed.

  (* Elimination on TPair *)
  Example inst_snd1 : has_type Γ φ Σ (ttapp (ttapp snd)) ({(TPair A a a B b b b) | a ⊔ b ⊔ {♦}} ==> { B | b }) (a ⊔ b).
    unfold TPair.
    change_qual (openq a b (a ⊔ #!1)).
    change_type (open_ty TUnit ∅ B b (
      {∀<:{⊤ | a ⊔ #!1 ⊔ {♦}}.{
        {{A | a} ==> {{#5 | #!5} ==> {# 5 | #! 5} | #! 1} | ∅} ==> {# 3 | #! 3} | #! 1 ⊔ a ⊔ #!3}
          | a ⊔ #!1 ⊔ {♦}} ==> {#3 | #!3})).
    apply t_tapp_fresh with (d1':=b ⊔ {♦}) (df':=a ⊔ {♦}); try solve [ccrush].
    (* change bound *)
    apply t_sub with (d1:=a) (T1:=(∀<:{⊤ | a ⊔ {♦}}.{
      {∀<:{⊤ | a ⊔ #! 1 ⊔ {♦}}.{
          {{A | a} ==> {{# 5 | #! 5} ==> {# 5 | #! 5} | #! 1} | ∅} ==> {# 3 | #! 3} | #! 1 ⊔ a ⊔ #! 3}
      | a ⊔ #! 1 ⊔ {♦}} ==> {#3 | #!3}
      | a ⊔ #! 1})); auto.
    * change_qual (openq ∅ a #!1).
      change_type (open_ty TUnit ∅ A a (∀<:{⊤ | #!1 ⊔ {♦}}.{
        {∀<:{⊤ | #!3 ⊔ #! 1 ⊔ {♦}}.{
            {{#5 | #!5} ==> {{# 5 | #! 5} ==> {# 5 | #! 5} | #! 1} | ∅} ==> {# 3 | #! 3} | #! 1 ⊔ #!5 ⊔ #! 3}
                      | #!3 ⊔ #! 1 ⊔ {♦}} ==> {#3 | #!3} | #!3 ⊔ #! 1})).
      apply t_tapp_fresh with (d1':=a ⊔ {♦}) (df':=∅); try solve [ccrush].
      dom_equals ({♦}).
      (* change bound *)
      replace (#! 1 ⊔ {♦}) with (#♦1) at 1; try solve [ccrush].
      replace (#! 3 ⊔ #! 1 ⊔ {♦}) with (#!1 ⊔ #!3 ⊔ {♦}) at 1; try solve [ccrush].
      replace (#! 3 ⊔ #! 1) with (#!1 ⊔ #!3) at 1; try solve [ccrush].
      eapply t_sub. eapply t_snd1. auto. unfold TPair.
      apply s_all. 1-4: ccrush. apply stp_refl; ccrush. apply qs_sq; ccrush. auto. auto. qual_destruct. ccrush.
      intros. rewrite nf_a in H. discriminate. eauto.
      inversion cl_a. inversion cl_b. subst. apply bound_0_empty in H0, H7. simpl in nf_a, nf_b. subst. ccrush.
    * apply s_all. inversion cl_a. inversion cl_b. subst. apply bound_0_empty in H0, H7. simpl in nf_a, nf_b. subst. ccrush.
      constructor. ccrush. constructor; ccrush. bound_simpl. lia. ccrush. constructor; ccrush.
      constructor; ccrush. bound_simpl. lia. constructor; ccrush. constructor; ccrush. bound_simpl. lia.
      constructor; ccrush. bound_simpl. lia.
      inversion cl_a. inversion cl_b. subst. apply bound_0_empty in H0, H7. simpl in nf_a, nf_b. subst. ccrush.
      constructor. ccrush. constructor; ccrush. eapply Nat.le_trans. eapply inter_bound_min. lia. bound_simpl. lia.
      eapply Nat.le_trans. eapply inter_bound_min. lia. constructor; ccrush. bound_simpl. lia. ccrush.
      constructor; ccrush. constructor; ccrush. bound_simpl. lia. constructor; ccrush. constructor; ccrush.
      bound_simpl. lia. constructor; ccrush. bound_simpl. lia. ccrush. ccrush.
      apply stp_refl. qual_destruct. inversion cl_a. inversion cl_b. subst. apply bound_0_empty in H17, H7. simpl in nf_a, nf_b. subst. ccrush.
      constructor. ccrush. constructor; ccrush. bound_simpl. lia. bound_simpl. lia. ccrush.
      constructor; ccrush. constructor; ccrush. 1,2 : bound_simpl; lia. constructor; ccrush. 1,2: bound_simpl; lia. ccrush.
      apply qs_sq; ccrush.
    * eauto.
    * qual_destruct. inversion cl_a. inversion cl_b. subst. apply bound_0_empty in H7, H17. simpl in nf_a, nf_b. subst. ccrush.
    * intros. rewrite nf_b in H. discriminate.
    * opening. eauto.
    * eauto.
    * qual_destruct. inversion cl_a. inversion cl_b. subst. apply bound_0_empty in H7, H17. simpl in nf_a, nf_b. subst. ccrush.
  Qed.

  Example inst_pair1 : has_type Γ φ Σ (ttapp (ttapp pair_mk)) ({A | a} ==> {{B | b} ==> {TPair A #!3 #!5 B #!1 #!3 #!5 | #!1 ⊔ #!3 } | #!1 }) (∅).
    unfold TPair.
    change_qual (openq ∅ b ∅).
    change_type (open_ty TUnit ∅ B b
    ({A | a}
          ==> {{#3 | #!3}
                  ==> {∀<:{⊤ | #! 3 ⊔ #! 1 ⊔ {♦}}.{
                          {{A | #! 5} ==> {{#9 | #! 5} ==> {# 5 | #! 5} | #! 1} | ∅} ==> {# 3 | #! 3}
                          | #! 1 ⊔ #! 5 ⊔ #! 3}
                      | #! 1 ⊔ #! 3}
              | #! 1})).
    eapply t_tapp_fresh with (d1':=b ⊔ {♦}) (df':={♦}); try solve [ccrush].
    (* change the bound *)
    eapply t_sub with (T1:=(∀<:{⊤ | a ⊔ {♦}}.{
      {A | a}
         ==> {{# 3 | #! 3}
                 ==> {∀<:{⊤ | #! 3 ⊔ #! 1 ⊔ {♦}}.{
                         {{A | #! 5} ==> {{# 9 | #! 5} ==> {# 5 | #! 5} | #! 1} | ∅}
                            ==> {# 3 | #! 3}
                         | #! 1 ⊔ #! 5 ⊔ #! 3}
                     | #! 1 ⊔ #! 3}
             | #! 1}
      | ∅ }) ) (d1:=∅); auto.
    * change_qual (openq ∅ a ∅).
      change_type (open_ty TUnit (∅) A a (∀<:{⊤ | #!1 ⊔ {♦}}.{
        {#3 | #!3}
           ==> {{# 3 | #! 3}
                   ==> {∀<:{⊤ | #! 3 ⊔ #! 1 ⊔ {♦}}.{
                           {{#9 | #! 5} ==> {{# 9 | #! 5} ==> {# 5 | #! 5} | #! 1} | ∅}
                              ==> {# 3 | #! 3}
                           | #! 1 ⊔ #! 5 ⊔ #! 3}
                       | #! 1 ⊔ #! 3}
               | #! 1}
        | ∅ })).
      eapply t_tapp_fresh with (d1':=a ⊔ {♦}) (df':=∅); try solve [ccrush]. dom_equals ({♦}).
      (* change the bound *)
      eapply t_sub with (T1:=(∀<:{⊤ | {♦}}.{
        ∀<:{⊤ | #♦1}.{
           {# 3 | #! 3}
              ==> {{# 3 | #! 3}
                      ==> {∀<:{⊤ | #! 3 ⊔ #! 1 ⊔ {♦}}.{
                              {{# 9 | #! 5} ==> {{# 9 | #! 5} ==> {# 5 | #! 5} | #! 1} | ∅}
                                 ==> {# 3 | #! 3}
                              | #! 1 ⊔ #! 5 ⊔ #! 3}
                          | #! 3 ⊔ #! 1}
                  | #! 1}
           | ∅ }
        | ∅})) (d1:=∅); auto.
      apply t_pair1. auto.
      apply s_all. ccrush. ccrush. ccrush. ccrush. cleanup; try lia. apply s_all. ccrush. ccrush. apply qs_sq; ccrush.
      apply stp_refl; ccrush. apply qs_sq; ccrush. replace (union (singleton 1) (singleton 3)) with (union (singleton 3) (singleton 1)).
      apply stp_refl; ccrush. fnsetdec.
      qual_destruct. ccrush. intros. rewrite H in nf_a. discriminate. eauto.
      opening. ccrush. qual_destruct. cleanup. f_equal. qdec.
    * apply s_all. 1-4: ccrush. qual_destruct. ccrush. apply stp_refl; ccrush.
    * intros. rewrite H in nf_b. discriminate.
    * eauto.
    * cleanup. qual_destruct. repeat f_equal; fnsetdec. all : lia.
  Qed.

  Section IntroElimExample.

    Context (ta tb : tm)
            (ht_ta : has_type Γ φ Σ ta A a)
            (ht_tb : has_type Γ φ Σ tb B b).

    (* pair_mk[A,B](ta,tb) *)
    Example pair_ab := (tapp (tapp (ttapp (ttapp pair_mk)) ta) tb).

    Example pair_intro1 :
      has_type Γ φ Σ pair_ab (TPair A a a B b b b) (a ⊔ b).
      intros. unfold pair_ab. unfold TPair.
      change_qual (openq a b (a ⊔ #!1)).
      change_type (open_ty TUnit ∅ B b (∀<:{⊤ | a ⊔ #!1 ⊔ {♦}}.{
        {{A | a} ==> {{B | #!5} ==> {# 5 | #! 5} | #! 1} | ∅} ==> {# 3 | #! 3} | #! 1 ⊔ a ⊔ #!3})).
      apply t_app; try solve [ccrush].
      change_qual (openq ∅ a #!1). replace (a ⊔ #! 1) with (#!1 ⊔ a).
      change_type (open_ty TUnit ∅ A a (
        {B | b}
          ==> {∀<:{⊤ | #!3 ⊔ #! 1 ⊔ {♦}}.{
              {{A | #!5} ==> {{B | #! 5} ==> {# 5 | #! 5} | #! 1} | ∅} ==> {# 3 | #! 3}
              | #! 1 ⊔ #!5 ⊔ #! 3}
          | #!1 ⊔ #! 3})).
      apply t_app; auto. apply inst_pair1. ccrush. ccrush. ccrush. qual_destruct.
      inversion cl_b. inversion cl_a. subst. apply bound_0_empty in H7, H17. subst. opening. cleanup. simpl in nf_a. simpl in nf_b. subst.
      auto. 1-6: lia. rewrite qlub_commute. auto. qual_destruct. inversion cl_a. subst. apply bound_0_empty in H7. subst. simpl in nf_a. subst.
      ccrush. opening. eauto.
      opening. cleanup. qual_destruct. cleanup. inversion cl_a. subst. apply bound_0_empty in H7. subst. cleanup.
      simpl in nf_a. simpl in nf_b. subst. repeat f_equal. all: lia.
    Qed.

    (* fst[A,B](pair_ab) : A^a *)
    Example pair1_elim1 : has_type Γ φ Σ (tapp (ttapp (ttapp fst)) pair_ab) A a.
      change_qual (openq (a ⊔ b) (a ⊔ b) a).
      change_type (open_ty TUnit (∅) (TPair A a a B b b b) (a ⊔ b) A).
      apply t_app_fresh with (d1':=(a⊔ {♦})⊔(b⊔{♦})) (df':=(a⊔ {♦})⊔(b⊔{♦})) ; try solve [ccrush].
      * dom_equals (a ⊔ b ⊔ {♦}). apply inst_fst1. qual_destruct. simpl.
        simpl in nf_a, nf_b. subst. qdec.
      * apply pair_intro1.
      * intros. qual_destruct. simpl in *. rewrite nf_a in H. rewrite nf_b in H. simpl in H. discriminate.
    Qed.

    (* snd[A,B](pair_ab) : A^b *)
    Example pair1_elim2 : has_type Γ φ Σ (tapp (ttapp (ttapp snd)) pair_ab) B b.
      change_qual (openq (a ⊔ b) (a ⊔ b) b).
      change_type (open_ty TUnit (∅) (TPair A a a B b b b) (a ⊔ b) B).
      apply t_app_fresh with (d1':=(a⊔ {♦})⊔(b⊔{♦})) (df':=(a⊔ {♦})⊔(b⊔{♦})) ; try solve [ccrush].
      * dom_equals (a ⊔ b ⊔ {♦}). apply inst_snd1. qual_destruct. simpl.
        simpl in nf_a, nf_b. subst. qdec.
      * apply pair_intro1.
      * intros. qual_destruct. simpl in *. rewrite nf_a in H. rewrite nf_b in H. simpl in H. discriminate.
    Qed.

  End IntroElimExample.

End PairTransparentUse.

Section PairTransparentConcreteUse.
  (* A more concrete usage example, shown in Section 2.4 of the paper *)

  Variables (φ : qual) (Σ : senv).

  Definition TRefU := TRef ∅ TUnit.


  Definition Γ : tenv := [ bind_tm (false, TRefU, {♦}) ; bind_tm (false, TRefU, {♦}) ].

  Example u := $0.
  Example v := $1.
  Example qu := $! 0.
  Example qv := $! 1.

  Context (phiwf : closed_qual 0 (‖Γ‖) (‖Σ‖) φ)
          (qu_obs : qu ⊑ φ)
          (qv_obs : qv ⊑ φ)
          (phi_fr : {♦} ⊑ φ)
          (sat : senv_saturated Σ ∅).

   (* Section 2.4:
      (tlet (tref tunit) (* u*)
        (tlet (tref tunit) (* v *)
            (tlet (pair u v) (* p *)
              (fst p) ; (snd p)
   *)
  Example pair_uv := (tapp (tapp (ttapp (ttapp pair_mk)) u) v).

  (* pair_uv : Pair[Ref[Unit]^u, Ref[Unit]^v]^{u,v}*)
  Example pair_uv_ty : has_type Γ φ Σ pair_uv (TPair TRefU qu qu TRefU qv qv qv) (qu ⊔ qv).
  Proof.
    apply pair_intro1; ccrush.
    econstructor. auto. auto. econstructor. auto. auto.
    eapply t_var. simpl. auto. auto. auto. unfold TRefU.
    econstructor. auto. auto. auto.
    eapply t_var. simpl. auto. auto. auto. unfold TRefU.
    econstructor. auto. auto. auto.
  Qed.

  (*
     In context p : Pair[Ref[Unit]^u, Ref[Unit]^v]^p
     we have that fst(p): Ref[Unit]^u
  *)
  Example proj1_fst :
  has_type
    (bind_tm (false, TPair TRefU qu qu TRefU qv qv qv, qu ⊔ qv)
     :: bind_tm (true, {TPair TRefU qu qu TRefU qv qv qv | qu ⊔ qv} ==> {TRef ∅ TUnit | $! 0},
           qu ⊔ qv) :: Γ)
    (qset true (union (union (singleton 0) (singleton 1)) (union (singleton 2) (singleton 3))) {}N {}N)
    Σ
    (tapp (ttapp (ttapp fst)) $ 3)
    (TRef ∅ TUnit) $! 0.
  Proof.
    change_qual (openq (qu ⊔ qv) (qu ⊔ qv) qu).
    change_type (open_ty TUnit ∅ (TPair TRefU qu qu TRefU qv qv qv) (qu ⊔ qv) (TRef ∅ TUnit)).
    apply t_app_fresh with (d1':=(qu ⊔ {♦})⊔(qv ⊔{♦})) (df':=(qu ⊔ {♦})⊔(qv ⊔{♦})) ; try solve [ccrush].
    - dom_equals (qu ⊔ qv ⊔ {♦}). apply inst_fst1; ccrush. unfold qu. ccrush. unfold qv. ccrush.
      unfold TRefU. ccrush.
    - eapply t_sub. eapply t_var; ccrush. unfold TPair. unfold TRefU. unfold qu. unfold qv. ccrush.
      apply stp_refl; try solve [unfold TPair; unfold TRefU; unfold qu; unfold qv; ccrush].
      eapply qs_qvar; try solve [unfold TPair; unfold TRefU; unfold qu; unfold qv; ccrush].
      ccrush. ccrush.
    - constructor; eauto. unfold tenv_saturated. intros.
      repeat rewrite qmem_lub_or_commute in H. destruct H.
      simpl in H. destruct H. apply NatSetFacts.singleton_iff in H; subst.
      try solve [eapply sat_tvar; ccrush]; try solve [eapply sat_var; ccrush]. ccrush.
      simpl in H. destruct H. apply NatSetFacts.singleton_iff in H; subst.
      try solve [eapply sat_tvar; ccrush]; try solve [eapply sat_var; ccrush]. ccrush.
      unfold senv_saturated. intros.
      repeat rewrite qmem_lub_or_commute in H. destruct H.
      simpl in H. destruct H; ccrush. simpl in H. destruct H; ccrush.
    - constructor; eauto. unfold tenv_saturated. intros.
      repeat rewrite qmem_lub_or_commute in H. destruct H.
      simpl in H. destruct H. apply NatSetFacts.singleton_iff in H; subst.
      try solve [eapply sat_tvar; ccrush]; try solve [eapply sat_var; ccrush]. ccrush.
      simpl in H. destruct H. apply NatSetFacts.singleton_iff in H; subst.
      try solve [eapply sat_tvar; ccrush]; try solve [eapply sat_var; ccrush]. ccrush.
      unfold senv_saturated. intros.
      repeat rewrite qmem_lub_or_commute in H. destruct H.
      simpl in H. destruct H; ccrush. simpl in H. destruct H; ccrush.
  Qed.

  (*
  u: Ref^♦, v: Ref^♦ |- let p = pair u v in (fst p) : Ref^u
  *)
  Example proj1 : has_type Γ φ Σ (tlet pair_uv (tapp (ttapp (ttapp fst)) #1)) (TRef ∅ TUnit) qu.
  Proof.
    unfold pair_uv. unfold u. unfold v. unfold tlet.
    change_qual (openq (qu ⊔ qv) (qu ⊔ qv) qu).
    change_type (open_ty TUnit ∅ (TPair TRefU qu qu TRefU qv qv qv) (qu ⊔ qv) (TRef ∅ TUnit)).
    unfold qu. unfold qv.
    eapply t_app.
    - eapply t_abs; ccrush. econstructor; ccrush.
      econstructor; ccrush. econstructor; ccrush. econstructor; ccrush.
      econstructor; ccrush. econstructor; ccrush. econstructor; ccrush.
      fold fst. fold qu. fold qv.
      replace (qset false (union (singleton 0) (singleton 1)) {}N {}N) with (qu ⊔ qv).
      eapply proj1_fst. simpl. ccrush.
    - apply pair_uv_ty.
    - ccrush.
    - ccrush.
    - ccrush.
    - ccrush.
  Qed.

End PairTransparentConcreteUse.

Section PairOpaque.
  (*
      We now cover _opaque_ pairs with components reaching out-of-scope variables. It is recommended to review
      examples_cell_opaque.v first for the basic idea.

      Opaque pairs have the following shape:

      OPair[A,B] := p∀C^c<:⊤^∅. f(g(x:A^♦ -> (y:B^x,♦ -> C^x,y)^x)^∅ -> C^f)^p

      With the addition of a second datum, the extractor function is now a dependent function of the form

      g(x:A^♦ -> (y:B^x,♦ -> C^x,y)

      which accepts the two (contextually fresh) components. Note that we permit potential overlap at
      y with x. The result is C and may reach both x and y. Essentially, this encoding, due to ignoring
      the qualifier binder c, behaves like the "imprecise" pairs in Section 2.4.2 of the paper.
      Is this an issue? Not at all in the case of out-of-scope data, because all we know is that the
      data will reach the name of the pair anyway.
      Using the same "self-reference chain" trick introduced in examples_cell_opaque.v, we demonstrate
      this in the following:

      pair: (p∀C^c<:⊤^∅. f(g(x:A^♦ -> (y:B^x,♦ -> C^x,y)^x)^∅ -> C^f)^p)^pair ⊣ pair : OPair[A,B]^♦

      pair[A^∅]: f(g(x:A^♦ -> (y:B^x,♦ -> A^x,y)^x)^∅ -> A^f)^pair
      pair[B^∅]: f(g(x:A^♦ -> (y:B^x,♦ -> B^x,y)^x)^∅ -> B^f)^pair

      pair[A^∅](x => y => x) : A^pair
      pair[B^∅](x => y => x) : B^pair
  *)


  (*
    OPair[A,B] := p∀C^c<:⊤^∅. f(g(x:A^♦ -> (y:B^x,♦ -> C^x,y)^x)^∅ -> C^f)^p
    Note: the number attached to each parameter indicates by how much it must be incremented if it is a deBruijn index.
  *)
  Example TOPair A2 B4 := (∀<:{ ∅ }.{ { { A2 | {♦} } ==> { { B4 | #♦1 } ==> {  #5  | #!3 ⊔ #!1  } | #!1 } | ∅ } ==> { #3 | #!0 } | #!0 }).

  (* Opaque pair introduction typing
    ([A^a<:⊤^♦] => ([B^b<:⊤♦a] => (g(x: A^a) => (h(y: B^b) => TOPair[A,B]^x,y,a,b)^x,a,b )^a,b )^a )^∅ *)
  Example t_pair_mk_ :
    has_type [] ∅ [] pair_mk (∀.{ ∀<:{ #♦1 }.{ {#3 | #!3 } ==> { {#3 | #!3} ==> {TOPair #9 #9 | #!1 ⊔ #!3 ⊔ #!5 ⊔ #!7 } | #!1 ⊔ #!3 ⊔ #!5 } | #!1 ⊔ #!3 } | #!1  }) ∅.
  Proof.
    unfold pair_mk.
    apply t_tabs; ccrush. unfold TOPair. ccrush. (* 0/1*)
    apply t_tabs; ccrush. (* 2/3 *)
    apply t_abs; ccrush. (* 4/5 *)
    apply t_abs; ccrush. (* 6/7 *)
    apply t_tabs; ccrush. (* 8/9 *)
    (* p abstraction *)
    (* x,y,a,b <: p *)
    eapply t_sub with (d1:=$!1 ⊔ $!3 ⊔ $!5 ⊔ $!7).
    2: {
        eapply stp_refl; try solve [ccrush].
        apply qs_trans with (d2:=($! 1 ⊔ $! 3 ⊔ $! 5 ⊔ $! 7) ⊔ $!8).
        apply qs_sq; ccrush. eapply qs_self_all; ccrush.
        f_equal. f_equal. f_equal. qdec.
    } 2,3 : ccrush.
    apply t_abs; ccrush.  (* 10/11 *)
    (* f abstraction: *)
    (* a,y <: x,y,a,b <: f*)
    eapply t_sub with (d1:=$!1 ⊔ $!7).
    2 : {
        eapply stp_refl; try solve [ccrush].
        apply qs_trans with (d2:=($! 1 ⊔ $! 3 ⊔ $! 5 ⊔ $! 7) ⊔ $!10).
        apply qs_sq; ccrush. eapply qs_self; ccrush.
    } 2,3 : ccrush.
    change_qual (openq $!1 $!7 ($!1 ⊔ #!1)).
    change_type (open_ty TUnit (∅) ($3) $!7 $9).
    apply t_app_fresh with (d1':=$!7⊔$!3⊔$♦1) (df':=$♦1); try solve [ccrush].
    * dom_equals ($♦1).
      change_qual (openq $!11 $!1 #!1).
      change_type (open_ty TUnit (∅) $1 $!1 ({$ 3 | #♦1} ==> {$ 9 | #! 3 ⊔ #! 1})).
      eapply t_app_fresh with (d1':=$♦1) (df':=$!11); try solve [ccrush].
      + dom_equals ({♦}). eapply t_var; ccrush.
      + eapply t_sub. eapply t_var; ccrush.
        apply stp_refl; ccrush. eapply qs_qvar; ccrush. all : ccrush.
    * eapply t_var; ccrush.
    * (* show transitive reachability closure of this qualifier, could be further automated *)
      constructor; eauto. unfold tenv_saturated. intros.
      repeat rewrite qmem_lub_or_commute in H. destruct H as [  Hmem | [ Hmem  | Hmem] ];
      simpl in Hmem; apply NatSetFacts.singleton_iff in Hmem; subst;
      try solve [eapply sat_tvar; ccrush]; try solve [eapply sat_var; ccrush].
  Qed.

  (* generalize to all contexts *)
  Example t_pair_mk : forall {Γ φ Σ}, closed_qual 0 (‖Γ‖) (‖Σ‖) φ ->
    has_type Γ φ Σ pair_mk (∀.{ ∀<:{ #♦1 }.{ {#3 | #!3 } ==> { {#3 | #!3} ==> {TOPair #9 #9 | #!1 ⊔ #!3 ⊔ #!5 ⊔ #!7 } | #!1 ⊔ #!3 ⊔ #!5 } | #!1 ⊔ #!3 } | #!1  }) ∅.
  Proof.
    intros. eapply weaken'. eapply weaken_store. apply t_pair_mk_. all : auto.
  Qed.

  (* The extractors (Church booleans) are compatible with the extractor signature of OPair: *)
  (* λx.λy.x : (x:A^♦ => (y:B^♦,x => A^xy)^x)^∅ *)
  Example elim1 : forall Γ φ Σ A B,
    closed_qual 0 (‖ Γ ‖) (‖ Σ ‖) φ ->
    closed_ty 0 (‖ Γ ‖) (‖ Σ ‖) A ->
    closed_ty 0 (‖ Γ ‖) (‖ Σ ‖) B ->
    has_type Γ φ Σ (tabs (tabs #3)) ({ A | {♦} } ==> { {B | #♦1 } ==> {A | #!3 ⊔ #!1 } | #!1 }) ∅.
  Proof.
    intros.
    apply t_abs; ccrush.
    apply t_abs; ccrush.
    eapply t_sub. eapply t_var; ccrush.
    apply stp_refl; ccrush. apply qs_sq; ccrush. all : ccrush.
  Qed.

  (* λx.λy.y : (x:A^♦ => (y:B^♦,x => B^xy)^x)^∅ *)
  Example elim2 : forall Γ φ Σ A B,
    closed_qual 0 (‖ Γ ‖) (‖ Σ ‖) φ ->
    closed_ty 0 (‖ Γ ‖) (‖ Σ ‖) A ->
    closed_ty 0 (‖ Γ ‖) (‖ Σ ‖) B ->
    has_type Γ φ Σ (tabs (tabs #1)) ({ A | {♦} } ==> { {B | #♦1 } ==> {B | #!3 ⊔ #!1 } | #!1 }) ∅.
  Proof.
    intros.
    apply t_abs; ccrush.
    apply t_abs; ccrush.
    eapply t_sub. eapply t_var; ccrush.
    apply stp_refl; ccrush. apply qs_sq; ccrush. all : ccrush.
  Qed.

  (* OPair elimination typing
     fst: ([A^a <: ⊤^♦] => ([B^b <: ⊤^♦a] => (OPair[A,B]^{a,b} => A^a,b)^a,b)^a)^∅ *)
  Example t_fst_ :
    has_type [] ∅ [] fst (∀.{ ∀<:{ #♦1 }.{ {TOPair #5 #5 | #!1 ⊔ #!3 } ==> { #5 | #!3 ⊔ #!5 } | #!1 ⊔ #!3 } | #!1 }) ∅.
  Proof.
    unfold fst.
    apply t_tabs; ccrush. unfold TOPair. ccrush.
    apply t_tabs; ccrush.
    apply t_abs; ccrush.
    change_qual (openq (qset false (union (singleton 1) (singleton 3)) {}N {}N) (∅) #!0).
    change_type (open_ty TUnit (∅) ({$ 1 | {♦}} ==> {{$ 3 | #♦1 } ==> {$1 | #!3 ⊔ #!1 } | #!1}) (∅) $1).
    apply t_app; try solve [ccrush].
    * change_qual (openq (qset false (union (singleton 1) (singleton 3)) {}N {}N) ∅ #!0).
      change_type (open_ty TUnit ∅ $1 ∅ ({{$ 1 | {♦}} ==> {{$ 3 | #♦1 } ==> {# 5 | #!3 ⊔ #! 1 } | #!1 } | ∅ } ==> {# 3 | #! 0})).
      apply t_tapp; ccrush.
      eapply t_sub.
      eapply t_var; ccrush.
      apply s_all. ccrush. ccrush.
      eapply qs_qvar; ccrush.
      eapply s_tvar_trans; ccrush. cleanup. apply stp_refl; ccrush. eapply qs_sq; ccrush.
      all : ccrush.
    * apply elim1; ccrush.
  Qed.

  (* generalize to all contexts *)
  Example t_fst : forall {Γ φ Σ}, closed_qual 0 (‖Γ‖) (‖Σ‖) φ ->
    has_type Γ φ Σ fst (∀.{ ∀<:{ #♦1 }.{ {TOPair #5 #5 | #!1 ⊔ #!3 } ==> { #5 | #!3 ⊔ #!5 } | #!1 ⊔ #!3 } | #!1 }) ∅.
  Proof.
    intros. eapply weaken'. eapply weaken_store. apply t_fst_. all : auto.
  Qed.

   (* OPair elimination typing
      snd: ([A^a <: ⊤^♦] => ([B^b <: ⊤^♦a] => (OPair[A,B]^{a,b} => B^a,b)^a,b)^a)^∅ *)
  Example t_snd_ :
    has_type [] ∅ [] snd (∀.{ ∀<:{ #♦1 }.{ {TOPair #5 #5 | #!1 ⊔ #!3 } ==> { #3 | #!3 ⊔ #!5 } | #!1 ⊔ #!3 } | #!1 }) ∅.
  Proof.
    unfold snd.
    apply t_tabs; ccrush. unfold TOPair. ccrush.
    apply t_tabs; ccrush.
    apply t_abs; ccrush.
    change_qual (openq (qset false (union (singleton 1) (singleton 3)) {}N {}N) (∅) #!0).
    change_type (open_ty TUnit (∅) ({$ 1 | {♦}} ==> {{$ 3 | #♦1 } ==> {$3 | #!3 ⊔ #!1 } | #!1}) (∅) $3).
    apply t_app; try solve [ccrush].
    * change_qual (openq (qset false (union (singleton 1) (singleton 3)) {}N {}N) ∅ #!0).
      change_type (open_ty TUnit ∅ $3 ∅ ({{$ 1 | {♦}} ==> {{$ 3 | #♦1 } ==> {# 5 | #!3 ⊔ #! 1 } | #!1 } | ∅ } ==> {# 3 | #! 0})).
      apply t_tapp; ccrush.
      eapply t_sub.
      eapply t_var; ccrush.
      apply s_all. ccrush. ccrush.
      eapply qs_qvar; ccrush.
      eapply s_tvar_trans; ccrush. cleanup. apply stp_refl; ccrush. eapply qs_sq; ccrush.
      all : ccrush.
    * apply elim2; ccrush.
  Qed.

  (* generalize to all contexts *)
  Example t_snd : forall {Γ φ Σ}, closed_qual 0 (‖Γ‖) (‖Σ‖) φ ->
    has_type Γ φ Σ snd (∀.{ ∀<:{ #♦1 }.{ {TOPair #5 #5 | #!1 ⊔ #!3 } ==> { #3 | #!3 ⊔ #!5 } | #!1 ⊔ #!3 } | #!1 }) ∅.
  Proof.
    intros. eapply weaken'. eapply weaken_store. apply t_snd_. all : auto.
  Qed.

End PairOpaque.

Section OpaquePairUse.

  (* a concrete use of opaque pairs *)

  Context (Σ := [(TUnit, ∅); ({ TUnit | ∅} ==> {TUnit | ∅}, ∅)])
          (φ := ({♦} ⊔ &!0 ⊔ &!1)).

  (* pair_mk(&0,&1)    *)
  Example pair_of_refs := (tapp (tapp (ttapp (ttapp pair_mk)) &0) &1).
  Example fst_pair_of_refs := (tapp (ttapp (ttapp fst)) pair_of_refs).
  Example snd_pair_of_refs := (tapp (ttapp (ttapp snd)) pair_of_refs).

  (* some auxiliary lemmas stating that the singleton locations are transitively reachability closed. *)
  Lemma sat_loc_1: saturated [] Σ &!1.
  Proof.
    unfold Σ. constructor; eauto.
    unfold senv_saturated. intros. simpl in H; apply NatSetFacts.singleton_iff in H; subst.
    apply sat_loc with (U:=TUnit) (q':=∅); ccrush.
    Unshelve. auto.
  Qed.

  Lemma sat_loc_0: saturated [] Σ &!0.
  Proof.
    unfold Σ. constructor; eauto.
    unfold tenv_saturated. intros. simpl in H. fnsetdec.
    unfold senv_saturated. intros. simpl in H; apply NatSetFacts.singleton_iff in H; subst.
    eapply sat_loc; ccrush.
  Qed.

  (* Instantiation typing of fst for this example
     fst : OPair[Ref[Unit => Unit],Ref[Unit]]^{&0,&1} => Ref[Unit => Unit]^{&0,&1}
  *)
  Example t_fst_inst: has_type [] φ Σ (ttapp (ttapp fst)) ({TOPair (TRef ∅ ({TUnit | ∅} ==> {TUnit | ∅})) (TRef ∅ TUnit) | &!0 ⊔ &!1 } ==> { (TRef ∅ ({TUnit | ∅} ==> {TUnit | ∅})) | &!0 ⊔ &!1 }) (&!0 ⊔ &!1).
  Proof.
    change_qual (openq &!0 &!1 (&!0 ⊔ #!1)).
    change_type (open_ty TUnit ∅ (TRef ∅ TUnit) &!1
                  ({TOPair (TRef ∅ ({TUnit | ∅} ==> {TUnit | ∅})) #5 | #! 1 ⊔ &! 0} ==> {TRef ∅ ({TUnit | ∅} ==> {TUnit | ∅}) | &! 0 ⊔ #!3})).
    2 : unfold TOPair; cleanup.
    eapply t_tapp_fresh with (d1':=&!1) (df':=&!0) ; try solve [unfold TOPair; ccrush].
    dom_equals ({♦}). apply (t_sub_bound ⊤ &♦0); try solve [ccrush].
    change_qual (openq ∅ &!0 #!1).
    change_type (open_ty TUnit ∅ (TRef ∅ ({TUnit | ∅} ==> {TUnit | ∅})) &!0
                                 (∀<:{⊤ | #♦1}.{
                                      {TOPair #5 # 5 | #! 1 ⊔ #!3}
                                          ==> {#5 | #!5 ⊔ #! 3} | #!3 ⊔ #! 1})).
    2: unfold TOPair; ccrush.
    apply t_tapp_fresh with (d1':=&!0) (df':=∅); try solve [ccrush].
    dom_equals ({♦}). apply (t_sub_bound ⊤ {♦}); try solve [ccrush].
    replace (#! 5 ⊔ #! 3) with (#!3 ⊔ #!5); try solve [ccrush].
    replace (#! 3 ⊔ #! 1) with (#!1 ⊔ #!3); try solve [ccrush].
    apply t_fst; ccrush.
    all : ccrush. all: eauto using sat_loc_1, sat_loc_0.
  Qed.

  (* Instantiation typing of snd for this example
     snd : OPair[Ref[Unit => Unit],Ref[Unit]]^{&0,&1} => Ref[Unit]^{&0,&1}
  *)
  Example t_snd_inst: has_type [] φ Σ (ttapp (ttapp snd)) ({TOPair (TRef ∅ ({TUnit | ∅} ==> {TUnit | ∅})) (TRef ∅ TUnit) | &!0 ⊔ &!1 } ==> { (TRef ∅ TUnit) | &!0 ⊔ &!1 }) (&!0 ⊔ &!1).
  Proof.
    change_qual (openq &!0 &!1 (&!0 ⊔ #!1)).
    change_type (open_ty TUnit ∅ (TRef ∅ TUnit) &!1
                  ({TOPair (TRef ∅ ({TUnit | ∅} ==> {TUnit | ∅})) #5 | #! 1 ⊔ &! 0} ==> {#3 | &! 0 ⊔ #!3})).
    2 : unfold TOPair; cleanup.
    eapply t_tapp_fresh with (d1':=&!1) (df':=&!0) ; try solve [unfold TOPair; ccrush].
    dom_equals ({♦}). apply (t_sub_bound ⊤ &♦0); try solve [ccrush].
    change_qual (openq ∅ &!0 #!1).
    change_type (open_ty TUnit ∅ (TRef ∅ ({TUnit | ∅} ==> {TUnit | ∅})) &!0
                                 (∀<:{⊤ | #♦1}.{
                                      {TOPair #5 # 5 | #! 1 ⊔ #!3}
                                          ==> {#3 | #!5 ⊔ #! 3} | #!3 ⊔ #! 1})).
    2: unfold TOPair; ccrush.
    apply t_tapp_fresh with (d1':=&!0) (df':=∅); try solve [ccrush].
    dom_equals ({♦}). apply (t_sub_bound ⊤ {♦}); try solve [ccrush].
    replace (#! 5 ⊔ #! 3) with (#!3 ⊔ #!5); try solve [ccrush].
    replace (#! 3 ⊔ #! 1) with (#!1 ⊔ #!3); try solve [ccrush].
    apply t_snd; ccrush.
    all : ccrush. all: eauto using sat_loc_1, sat_loc_0.
  Qed.

  (* Instantiation typing of the pair constructor for this example
     pair_mk : Ref[Unit => Unit]^&0 => Ref[Unit]^&1 => OPair[Ref[Unit => Unit],Ref[Unit]]^{&0,&1}
  *)
  Example t_pair_mk_inst: has_type [] φ Σ (ttapp (ttapp pair_mk))
                                ( {(TRef ∅ ({TUnit | ∅} ==> {TUnit | ∅})) | &!0 }
                                   ==> { { (TRef ∅ TUnit) | &!1 }
                                          ==> { TOPair (TRef ∅ ({TUnit | ∅} ==> {TUnit | ∅})) (TRef ∅ TUnit) | #!1 ⊔ #!3 ⊔ &!1 ⊔ &!0 } | #!1 ⊔ &!1 ⊔ &!0 }) (&!1 ⊔ &!0).
  Proof.
    change_qual (openq &!0 &!1 (#!1 ⊔ &!0)).
    change_type (open_ty TUnit ∅ (TRef ∅ TUnit) &!1
                    ({TRef ∅ ({TUnit | ∅} ==> {TUnit | ∅}) | &! 0}
                         ==> {{#3 | #!3 }
                                ==> {TOPair (TRef ∅ ({TUnit | ∅} ==> {TUnit | ∅})) #9 | #! 1 ⊔ #! 3 ⊔ #!5 ⊔ &! 0} | #! 1 ⊔ #!3 ⊔ &!0 })).
    2 : { unfold TOPair; ccrush. f_equal. qdec. f_equal. qdec. }
    eapply t_tapp_fresh with (d1':=&!1) (df':=&!0) ; try solve [unfold TOPair; ccrush].
    dom_equals ({♦}). apply (t_sub_bound ⊤ &♦0); try solve [ccrush].
    change_qual (openq ∅ &!0 #!1).
    change_type (open_ty TUnit ∅ (TRef ∅ ({TUnit | ∅} ==> {TUnit | ∅})) &!0
                                 (∀<:{⊤ | #♦1}.{
                                      {#3 | #!3}
                                          ==> {{# 3 | #! 3}
                                               ==> {TOPair #9 # 9 | #! 1 ⊔ #! 3 ⊔ #!5 ⊔ #! 7} | #! 1 ⊔ #!3 ⊔ #!5 } | #!1 ⊔ #!3})).
    2 : unfold TOPair; ccrush.
    apply t_tapp_fresh with (d1':=&!0) (df':=∅); try solve [ccrush].
    dom_equals ({♦}). apply (t_sub_bound ⊤ {♦}); try solve [ccrush].
    apply t_pair_mk; ccrush.
    all : ccrush. all: eauto using sat_loc_1, sat_loc_0.
  Qed.

  (* pair_of_refs : OPair[Ref[Unit => Unit],Ref[Unit]]^{&0,&1} *)
  Example t_pair_of_refs: has_type [] φ Σ pair_of_refs (TOPair (TRef ∅ ({TUnit | ∅} ==> {TUnit | ∅})) (TRef ∅ TUnit)) (&!1 ⊔ &!0).
  Proof.
    unfold pair_of_refs.
    change_qual (&!1 ⊔ &!0 ⊔ &!1 ⊔ &!0).
    change_qual (openq (&!1 ⊔ &!0) &!1 (#!1 ⊔ &!0 ⊔ &!1 ⊔ &!0)).
    change_type (open_ty TUnit ∅ (TRef ∅ TUnit) &!1 (TOPair (TRef ∅ ({TUnit | ∅} ==> {TUnit | ∅})) (TRef ∅ TUnit))).
    2: unfold TOPair; ccrush.
    apply t_app; try solve [ccrush].
    * change_qual (openq (&!1 ⊔ &!0) &!0 (#!1 ⊔ &!1 ⊔ &!0)).
      change_type (open_ty TUnit ∅ (TRef ∅ ({TUnit | ∅} ==> {TUnit | ∅})) &!0
                           (({TRef ∅ TUnit | &! 1} ==> {TOPair (TRef ∅ ({TUnit | ∅} ==> {TUnit | ∅})) (TRef ∅ TUnit) | #!1 ⊔ #!3 ⊔ &!1 ⊔ &!0}))).
      2 : { unfold TOPair; ccrush. f_equal. qdec. }
      apply t_app; try solve [ccrush].
      + apply t_pair_mk_inst.
      + change_qual (∅ ⊔ &!0). apply t_loc; ccrush.
      + ccrush. replace (qset false {}N {}N (union (singleton 1) (singleton 0))) with (&!1 ⊔ &!0). eauto using sat_loc_0, sat_loc_1. ccrush.
    * change_qual (∅ ⊔ &!1). apply t_loc; ccrush.
    * ccrush. replace (qset false {}N {}N (union (singleton 0) (union (singleton 1) (singleton 0)))) with (&!1 ⊔ &!0). eauto using sat_loc_0, sat_loc_1. ccrush.
  Qed.

  Example t_fst_pair_of_refs : has_type [] φ Σ fst_pair_of_refs (TRef ∅ ({TUnit | ∅} ==> {TUnit | ∅})) (&!0 ⊔ &!1).
  Proof.
    unfold fst_pair_of_refs.
    change_qual (openq (&!0 ⊔ &!1) (&!1 ⊔ &!0) (&!0 ⊔ &!1)).
    change_type (open_ty TUnit ∅ (TOPair (TRef ∅ ({TUnit | ∅} ==> {TUnit | ∅})) (TRef ∅ TUnit)) (&!1 ⊔ &!0) (TRef ∅ ({TUnit | ∅} ==> {TUnit | ∅}))).
    apply t_app; try solve [ccrush].
    * replace (&! 1 ⊔ &! 0) with (&!0 ⊔ &!1). apply t_fst_inst. ccrush.
    * apply t_pair_of_refs.
    * ccrush. ccrush. replace (qset false {}N {}N (union (singleton 0) (singleton 1))) with (&!0 ⊔ &!1). eauto using sat_loc_0, sat_loc_1. ccrush.
  Qed.

  Example t_snd_pair_of_refs : has_type [] φ Σ snd_pair_of_refs (TRef ∅ TUnit) (&!0 ⊔ &!1).
  Proof.
    unfold snd_pair_of_refs.
    change_qual (openq (&!0 ⊔ &!1) (&!1 ⊔ &!0) (&!0 ⊔ &!1)).
    change_type (open_ty TUnit ∅ (TOPair (TRef ∅ ({TUnit | ∅} ==> {TUnit | ∅})) (TRef ∅ TUnit)) (&!1 ⊔ &!0) (TRef ∅ TUnit)).
    apply t_app; try solve [ccrush].
    * replace (&! 1 ⊔ &! 0) with (&!0 ⊔ &!1). apply t_snd_inst. ccrush.
    * apply t_pair_of_refs.
    * ccrush. ccrush. replace (qset false {}N {}N (union (singleton 0) (singleton 1))) with (&!0 ⊔ &!1). eauto using sat_loc_0, sat_loc_1. ccrush.
  Qed.

End OpaquePairUse.

Section OpaquePairEndToEnd.

  (* Now we demonstrate the "counter" example (Fig. 1 of the paper). *)

  Example TThunk := ({TUnit | ∅ } ==> {TUnit | ∅}).

  (* def counter() =
       let x = new Ref()
       pair_mk({() => x:=!x}, {() => x:=!x})
  *)
  Example counter := (tabs (tlet (tref tunit)
                                 (tapp (tapp (ttapp (ttapp pair_mk)) (tabs (tassign #3 (tderef #3))))
                                                                     (tabs (tassign #3 (tderef #3)))))).

  (* let ctr = counter()
     let i = fst(ctr)
     let d = fst(ctr)
  *)
  Example counter_use := (tlet (tapp counter tunit)
                                (tlet (tapp (ttapp (ttapp fst)) #1)
                                      (tapp (ttapp (ttapp snd)) #3))).


  (* Type of the pair constructor instantation in its usage context within counter. The concrete typing assumptions
     are unimportant and left abstract: *)
  Example t_counter_pair_mk_inst : forall {W X Y Z},
    has_type [bind_tm (false, W, {♦}); bind_tm (true, X, ∅); bind_tm (false, Y, ∅); bind_tm (true, Z, ∅)]
             $♦3 [] (* <- we have access to the local mutable reference cell x, bound to $3 *)
             (ttapp (ttapp pair_mk)) ({TThunk | $! 3} ==> {{TThunk | $! 3} ==> {TOPair TThunk TThunk | #! 1 ⊔ #! 3 ⊔ $! 3 ⊔ $! 3} | #! 1 ⊔ $! 3 ⊔ $! 3 }) $!3.
  Proof.
    intros. change_qual ($!3 ⊔ $!3).
    change_qual (openq $!3 $!3 (#!1 ⊔ $!3)).
    change_type (open_ty TUnit ∅ TThunk $!3 ({TThunk | $! 3} ==> {{#3 | #!3} ==> {TOPair TThunk #9 | #! 1 ⊔ #! 3 ⊔ #!5 ⊔ $! 3 } | #! 1 ⊔ #!3 ⊔ $! 3 })).
    2: unfold TThunk; unfold TOPair; ccrush.
    apply t_tapp_fresh with (d1':=$♦3) (df':=$♦3); try solve [unfold TThunk; ccrush].
    dom_equals ($♦3). apply (t_sub_bound ⊤ $♦3); try solve [ccrush].
    change_qual (openq ∅ $!3 #!1).
    change_type (open_ty TUnit ∅ TThunk $!3 (∀<:{⊤ | #♦1}.{ {#3 | #!3} ==> {{# 3 | #! 3} ==> {TOPair #9 # 9 | #! 1 ⊔ #! 3 ⊔ #! 5 ⊔ #!7} | #! 1 ⊔ #!3 ⊔ #!5} | #! 1 ⊔ #! 3})).
    2: unfold TThunk; unfold TOPair; ccrush.
    apply t_tapp_fresh with (d1':=$♦3) (df':=∅); try solve [unfold TThunk; ccrush].
    dom_equals ({♦}). apply (t_sub_bound ⊤ {♦}); try solve [ccrush].
    apply t_pair_mk; ccrush.
  Qed.

  (* counter : Unit => OPair[Thunk,Thunk]^{♦} *)
  Example t_counter : has_type [] ∅ [] counter ({TUnit | ∅ } ==> { (TOPair TThunk TThunk) | {♦} }) ∅.
  Proof.
    unfold counter.
    apply t_abs; try solve [ccrush]. unfold TThunk; unfold TOPair; ccrush.
    (* a little cleanup *)
    unfold_open. repeat rewrite open_let. cleanup. fold pair_mk. fold TThunk.
    replace (qset false {}N (union (singleton 3) (singleton 1)) {}N) with (#!3 ⊔ #!1); try solve [ccrush]. fold (TOPair TThunk TThunk).
    (* prepare dependent application/let rule *)
    change_qual (openq ∅ {♦} #!1).
    change_type ((TOPair TThunk TThunk) <~ᵀ TUnit ~ ∅; (TRef ∅ TUnit) ~ {♦}). 2: unfold TThunk; unfold TOPair; ccrush.
    apply t_let_fresh with (q1':={♦}) (df':=∅); ccrush. unfold TThunk; unfold TOPair. ccrush.
    * (* binding *) change_qual (∅ ⊔ {♦}). apply t_ref; ccrush. apply t_base; ccrush.
    * (* body *) fold pair_mk. fold TThunk.
      replace (qset false {}N (union (singleton 3) (singleton 1)) {}N) with (#!3 ⊔ #!1); try solve [ccrush]. fold (TOPair TThunk TThunk).
      change_qual (openq $!3 $!3 (#!1 ⊔ $!3)).
      change_type ((TOPair TThunk TThunk) <~ᵀ TUnit ~ ∅; TThunk ~  $! 3). 2: unfold TThunk; unfold TOPair; ccrush.
      apply t_app; try solve [ccrush].
      + change_qual (openq $!3 $!3 (#!1 ⊔ $!3 ⊔ $!3)).
        change_type (({TThunk | $! 3} ==> {TOPair TThunk TThunk | #!1 ⊔ #!3 ⊔ $!3 ⊔ $!3}) <~ᵀ TUnit ~ ∅; TThunk ~ $! 3).
        2: { unfold TThunk; unfold TOPair; ccrush. f_equal. qdec. }
        apply t_app; try solve [ccrush].
        - (* constructor*)
          apply t_counter_pair_mk_inst.
        - (* thunk *) apply t_abs; ccrush.
          eapply t_assign.
          ** eapply t_var; ccrush.
          ** eapply t_deref. eapply t_var; ccrush. all: ccrush.
          ** auto.
      + (* thunk *) apply t_abs; ccrush.
        eapply t_assign.
        ** eapply t_var; ccrush.
        ** eapply t_deref. eapply t_var; ccrush. all: ccrush.
        ** auto.
  Qed.

  (* Type of the first projection its usage context within counter_use. The concrete typing assumptions
     are unimportant and left abstract:
     fst: OPair[Thunk,Thunk]^ctr => Thunk^ctr
     *)
  Example t_counter_use_fst_inst : forall {X Y},
    has_type [bind_tm (false, X, {♦}); bind_tm (true, Y, ∅)] $♦ 1 [] (ttapp (ttapp fst)) ({TOPair TThunk TThunk | $! 1} ==> {TThunk | $! 1 ⊔ $! 1}) $!1.
  Proof.
    intros. change_qual (openq $!1 $!1 (#!1 ⊔ $!1)).
    change_type (open_ty TUnit ∅ TThunk $!1 ({TOPair TThunk #5 | #!1 ⊔ $! 1} ==> {TThunk | #!3 ⊔ $! 1})).
    2: { unfold TThunk; unfold TOPair; ccrush. f_equal. qdec. }
    apply t_tapp_fresh with (d1':=$♦1) (df':=$♦1); try solve [ccrush]. 2 : unfold TThunk; ccrush.
    dom_equals ($♦1). apply (t_sub_bound ⊤ ($♦1)); try solve [ccrush].
    change_qual (openq ∅ $!1 #!1).
    change_type (open_ty TUnit ∅ TThunk $!1 (∀<:{⊤ | #♦ 1}.{ {TOPair #5 # 5 | #! 1 ⊔ #!3} ==> {#5| #! 3 ⊔ #!5} | #! 1 ⊔ #!3})).
    2: unfold TThunk; unfold TOPair; ccrush.
    apply t_tapp_fresh with (d1':=$♦1) (df':=∅); try solve [ccrush]. 2 : unfold TThunk; ccrush.
    dom_equals ({♦}). apply (t_sub_bound ⊤ ({♦})); try solve [ccrush].
    apply t_fst; ccrush.
  Qed.

  (* Type of the second projection its usage context within counter_use. The concrete typing assumptions
     are unimportant and left abstract:
     snd: OPair[Thunk,Thunk]^ctr => Thunk^ctr*)
  Example t_counter_use_snd_inst : forall {W X Y Z},
    has_type [bind_tm (false, W, $♦ 1); bind_tm (true, X, $! 1); bind_tm (false, Y, {♦}); bind_tm (true, Z, ∅)]
             (qset true (union (singleton 1) (singleton 3)) {}N {}N) []
             (ttapp (ttapp snd)) ({TOPair TThunk TThunk | $! 1} ==> {TThunk | $! 1 ⊔ $! 1}) $!1.
  Proof.
    intros. change_qual (openq $!1 $!1 (#!1 ⊔ $!1)).
    change_type (open_ty TUnit ∅ TThunk $!1 ({TOPair TThunk #5 | #!1 ⊔ $! 1} ==> {#3 | #!3 ⊔ $! 1})).
    2: { unfold TThunk; unfold TOPair; ccrush. f_equal. qdec. }
    apply t_tapp_fresh with (d1':=$♦1) (df':=$♦1); try solve [ccrush]. 2 : unfold TThunk; ccrush.
    dom_equals ($♦1). apply (t_sub_bound ⊤ ($♦1)); try solve [ccrush].
    change_qual (openq ∅ $!1 #!1).
    change_type (open_ty TUnit ∅ TThunk $!1 (∀<:{⊤ | #♦ 1}.{ {TOPair #5 # 5 | #! 1 ⊔ #!3} ==> {#3| #! 3 ⊔ #!5} | #! 1 ⊔ #!3})).
    2: unfold TThunk; unfold TOPair; ccrush.
    apply t_tapp_fresh with (d1':=$♦1) (df':=∅); try solve [ccrush]. 2 : unfold TThunk; ccrush.
    dom_equals ({♦}). apply (t_sub_bound ⊤ ({♦})); try solve [ccrush].
    apply t_snd; ccrush.
  Qed.

  (* counter_use : Thunk^{♦}*)
  Example t_counter_use : has_type [] {♦} [] counter_use TThunk {♦}.
  Proof.
    unfold counter_use.
    change_qual (openq ∅ {♦} #!1).
    change_type (open_ty TUnit ∅ (TOPair TThunk TThunk) {♦} TThunk).
    apply t_let_fresh with (q1':={♦}) (df':={♦}); try solve [ccrush]. 1 : unfold TOPair; unfold TThunk; ccrush.
    * (* counter : OPair[Thunk,Thunk]^{♦} *) dep_app (∅) (∅). 2: unfold TOPair; unfold TThunk; ccrush.
      apply t_app; try solve [ccrush].
      eapply weaken_flt. apply t_counter. all: ccrush.
    * cleanup. fold TThunk. fold fst. fold snd.
      change_qual (openq $!1 $!1 $!1).
      change_type (open_ty TUnit ∅ TThunk $!1 TThunk).
      eapply t_let_fresh with (q1':=$♦1) (df':=$♦1); try solve [unfold TOPair; unfold TThunk; ccrush].
      + (* fst(counter) : Thunk^{counter} *)
        change_qual (openq $!1 $!1 ($!1 ⊔ $!1)).
        change_type (open_ty TUnit ∅ (TOPair TThunk TThunk) $!1 TThunk).
        apply t_app; try solve [ccrush].
        - apply t_counter_use_fst_inst.
        - eapply t_var; ccrush. unfold TOPair; unfold TThunk; ccrush.
      + (* snd(counter) : Thunk^{counter} *)
        cleanup. fold snd. fold TThunk.
        change_qual (openq $!1 $!1 ($!1 ⊔ $!1)).
        change_type (open_ty TUnit ∅ (TOPair TThunk TThunk) $!1 TThunk).
        apply t_app; try solve [ccrush].
        - apply t_counter_use_snd_inst.
        - eapply t_var; ccrush. unfold TOPair; unfold TThunk; ccrush.
  Qed.

End OpaquePairEndToEnd.

Section PairTransparentToOpaque.

  (* Finally, we assert that transparent pairs are convertible into opaque pairs by typing an eta expansion.
     If we take the Church encodings as a justification for data types, then we can use this eta expansion
     as an admissible subtyping rule linking the two encodings. We can then use this thereby justified subtyping rule
     for data types escaping their defining scope.

     We believe that we can alternatively replace this justification by eta expansion with a pure subtyping argument
     using self-type abstraction, which is yet to be mechanized.
  *)

  (* Convert a transparent pair to an opaque pair by eta expansion:
     pair_to_opair = ΛA.ΛB.λp.pair_mk(fst(p),snd(p))
  *)
  Example pair_to_opair := (ttabs (ttabs (tabs (tapp (tapp (ttapp (ttapp pair_mk)) (tapp (ttapp (ttapp fst)) #1)) (tapp (ttapp (ttapp snd)) #1))))).

  (* Instantiation of fst used in the function
     fst: Pair[A^a,B^b]^{a,b} => A^a
  *)
  Lemma fst_pair_to_opair_inst: forall {X0 X1 X2 X3 X4 X5}, has_type
      [bind_tm (false, X5, qset false (union (singleton 1) (singleton 3)) {}N {}N);
       bind_tm (true,  X4, qset false (union (singleton 1) (singleton 3)) {}N {}N);
       bind_ty (false, X3, $♦ 1);
       bind_tm (true,  X2, $! 1);
       bind_ty (false, X1, {♦});
       bind_tm (true,  X0, ∅)]
      (qset true (union (union (singleton 1) (singleton 3)) (union (singleton 4) (singleton 5))) {}N {}N)
      [] (ttapp (ttapp fst)) ({TPair $ 1 $! 1 $! 1 $ 3 $! 3 $! 3 $! 3 | $! 1 ⊔ $! 3} ==> {$ 1 | $! 1})  ($! 1 ⊔ $! 3).
  Proof.
    intros.
    apply t_sub with (T1:=({TPair $ 1 $! 1 $! 1 $ 3 $! 3 $! 3 $! 3 | $! 1 ⊔ $! 3 ⊔ {♦}} ==> {$ 1 | $! 1})) (d1:=($! 1 ⊔ $! 3)). 3,4 : ccrush.
    * change_qual (openq $!1 $!3 (#!1 ⊔ $!1)).
      change_type (open_ty TUnit ∅ $3 $!3
                         ({TPair $ 1 $! 1 $! 1 #5 #!1 #!3 #!5 | #!1 ⊔ $! 1 ⊔ {♦}} ==> {$ 1 | $! 1})). 2: unfold TPair; ccrush.
      apply t_tapp_fresh with (d1':=$♦3⊔$♦1) (df':=$♦1); try solve [ccrush].
      - dom_equals ($♦1). apply (t_sub_bound ⊤ $♦1); try solve [ccrush].
        change_qual (openq ∅ $!1 #!1).
        change_type (open_ty TUnit ∅ $1 $!1
             (∀<:{⊤ | #♦1}.{ {TPair #5 #!3 #!5 # 5 #! 1 #! 3 #! 5 | #! 1 ⊔ #!3 ⊔ {♦}} ==> {#5 | #!5} | #! 1 ⊔ #!3})).
        2: unfold TPair; ccrush.
        apply t_tapp_fresh with (d1':=$♦1) (df':=∅); try solve [ccrush].
        dom_equals ({♦}). apply (t_sub_bound ⊤ {♦}); try solve [ccrush].
        apply t_fst1; ccrush.
      - (* show transitive reachability closure of this qualifier, could be further automated *)
        constructor; eauto. unfold tenv_saturated. intros.
        repeat rewrite qmem_lub_or_commute in H. destruct H as [ Hmem  | Hmem];
        simpl in Hmem; apply NatSetFacts.singleton_iff in Hmem; subst;
        try solve [eapply sat_tvar; ccrush]; try solve [eapply sat_var; ccrush].
    * apply s_fun. 1,2: unfold TPair; ccrush.
      apply qs_sq; ccrush.
      apply stp_refl. unfold TPair; ccrush. apply qs_sq; ccrush.
      cleanup. apply stp_refl; ccrush. apply qs_sq; ccrush.
  Qed.

  (* Instantiation of snd used in the function
     snd: Pair[A^a,B^b]^{a,b} => B^b
  *)
  Lemma snd_pair_to_opair_inst: forall {X0 X1 X2 X3 X4 X5}, has_type
      [bind_tm (false, X5, qset false (union (singleton 1) (singleton 3)) {}N {}N);
       bind_tm (true,  X4, qset false (union (singleton 1) (singleton 3)) {}N {}N);
       bind_ty (false, X3, $♦ 1);
       bind_tm (true,  X2, $! 1);
       bind_ty (false, X1, {♦});
       bind_tm (true,  X0, ∅)]
      (qset true (union (union (singleton 1) (singleton 3)) (union (singleton 4) (singleton 5))) {}N {}N)
      [] (ttapp (ttapp snd)) ({TPair $ 1 $! 1 $! 1 $ 3 $! 3 $! 3 $! 3 | $! 1 ⊔ $! 3} ==> {$ 3 | $! 3})  ($! 1 ⊔ $! 3).
  Proof.
    intros.
    apply t_sub with (T1:=({TPair $ 1 $! 1 $! 1 $ 3 $! 3 $! 3 $! 3 | $! 1 ⊔ $! 3 ⊔ {♦}} ==> {$ 3 | $! 3})) (d1:=($! 1 ⊔ $! 3)). 3,4 : ccrush.
    * change_qual (openq $!1 $!3 (#!1 ⊔ $!1)).
      change_type (open_ty TUnit ∅ $3 $!3
                         ({TPair $ 1 $! 1 $! 1 #5 #!1 #!3 #!5 | #!1 ⊔ $! 1 ⊔ {♦}} ==> {#3 | #!3})). 2: unfold TPair; ccrush.
      apply t_tapp_fresh with (d1':=$♦3⊔$♦1) (df':=$♦1); try solve [ccrush].
      - dom_equals ($♦1). apply (t_sub_bound ⊤ $♦1); try solve [ccrush].
        change_qual (openq ∅ $!1 #!1).
        change_type (open_ty TUnit ∅ $1 $!1
             (∀<:{⊤ | #♦1}.{ {TPair #5 #!3 #!5 # 5 #! 1 #! 3 #! 5 | #! 1 ⊔ #!3 ⊔ {♦}} ==> {#3 | #!3} | #! 1 ⊔ #!3})).
        2: unfold TPair; ccrush.
        apply t_tapp_fresh with (d1':=$♦1) (df':=∅); try solve [ccrush].
        dom_equals ({♦}). apply (t_sub_bound ⊤ {♦}); try solve [ccrush].
        apply t_snd1; ccrush.
      - (* show transitive reachability closure of this qualifier, could be further automated *)
        constructor; eauto. unfold tenv_saturated. intros.
        repeat rewrite qmem_lub_or_commute in H. destruct H as [ Hmem  | Hmem];
        simpl in Hmem; apply NatSetFacts.singleton_iff in Hmem; subst;
        try solve [eapply sat_tvar; ccrush]; try solve [eapply sat_var; ccrush].
    * apply s_fun. 1,2: unfold TPair; ccrush.
      apply qs_sq; ccrush.
      apply stp_refl. unfold TPair; ccrush. apply qs_sq; ccrush.
      cleanup. apply stp_refl; ccrush. apply qs_sq; ccrush.
  Qed.

  (* The eta expansion is typable and justifies converting transparent pairs to opaque pairs:
     pair_to_opair : (∀A^a<:⊤♦. (∀B^b<:⊤♦a. (Pair[A^a,B^b] => OPair[A,B]^{a,b})^{a,b})^{a})^∅
   *)
  Example t_pair_to_opair : has_type [] ∅ [] pair_to_opair (∀.{ ∀<:{ #♦1 }.{ { TPair #5 #!3 #!5 #5 #!1 #!3 #!5 | #!3 ⊔ #!1 } ==> {TOPair #7 #7 | #!3 ⊔ #!5} | #!1 ⊔ #!3  } | #!1 }) ∅.
  Proof.
    unfold pair_to_opair.
    apply t_tabs; ccrush. (* 0/1 <- A^a *)
    unfold TPair; unfold TOPair; ccrush.
    apply t_tabs; ccrush. (* 2/3 <- B^b *)
    apply t_abs; ccrush.  (* 4/5 <- p *)
    (* a little cleanup *)
    fold pair_mk. fold fst. fold snd.
    change_type (TOPair $1 $3). 2: unfold TOPair; ccrush.
    change_qual (openq ($!1 ⊔ $!3 ⊔ $!1) $!3  (#!1 ⊔ $!1 ⊔ $!3 ⊔ $!1)).
    change_type (open_ty TUnit ∅ $3 $!3 (TOPair $1 $3)). 2 : unfold TOPair; ccrush.
    apply t_app; try solve [ccrush].
    * change_qual (openq ($!3 ⊔ $!1) $!1 (#!1 ⊔ $!3 ⊔ $!1)).
      change_type (open_ty TUnit ∅ $1 $!1
      ({$ 3 | $! 3} ==> {TOPair $1 $3 | #! 1 ⊔ #!3 ⊔ $! 3 ⊔ $! 1})).
      2 : { unfold TOPair; ccrush. f_equal. qdec. }
      apply t_app; try solve [ccrush].
      + change_qual (openq $!1 $!3 (#!1 ⊔ $!1)).
        change_type (open_ty TUnit ∅ $3 $!3 ({$ 1 | $! 1}
                                           ==> {{#3| #!3}
                                                     ==> {TOPair $1 #9 | #! 1 ⊔ #! 3 ⊔ #!5 ⊔ $! 1} | #! 1 ⊔ #! 3 ⊔ $! 1})).
        2 : { unfold TOPair; ccrush. f_equal. qdec. f_equal. qdec. }
        apply t_tapp_fresh with (d1':=$♦3⊔$♦1) (df':=$♦1); try solve [ccrush].
        - dom_equals ($♦1). apply (t_sub_bound ⊤ $♦1); try solve [ccrush].
          change_qual (openq ∅ $!1 #!1).
          change_type (open_ty TUnit ∅ $1 $!1 (∀<:{⊤ | #♦1}.{
            {#3| #!3}
               ==> {{# 3 | #! 3}
                       ==> {TOPair #9 #9
                           | #! 1 ⊔ #! 3 ⊔ #! 5 ⊔ #!7}
                   | #! 1 ⊔ #! 3 ⊔ #!5}
            | #! 1 ⊔ #!3})).
          2 : unfold TOPair; ccrush.
          apply t_tapp_fresh with (d1':=$♦1) (df':=∅); try solve [ccrush].
          dom_equals ({♦}).  apply (t_sub_bound ⊤ {♦}); try solve [ccrush].
          apply t_pair_mk; ccrush.
        - (* show transitive reachability closure of this qualifier, could be further automated *)
          constructor; eauto. unfold tenv_saturated. intros.
          repeat rewrite qmem_lub_or_commute in H. destruct H as [ Hmem  | Hmem];
          simpl in Hmem; apply NatSetFacts.singleton_iff in Hmem; subst;
          try solve [eapply sat_tvar; ccrush]; try solve [eapply sat_var; ccrush].
      + (* fst p*)
        change_qual (openq ($!1 ⊔ $!3) ($!1 ⊔ $!3) $!1).
        change_type (open_ty TUnit ∅ (TPair $1 $!1 $!1 $3 $!3 $!3 $!3) ($!1 ⊔ $!3) $1).
        apply t_app; try solve [ccrush].
        - apply fst_pair_to_opair_inst.
        - eapply t_sub.
          eapply t_var; ccrush. 2-3 : ccrush.
          unfold TPair. cleanup. apply stp_refl; ccrush.
          eapply qs_qvar; ccrush.
    * (* snd p*)
      change_qual (openq ($!1 ⊔ $!3) ($!1 ⊔ $!3) $!3).
      change_type (open_ty TUnit ∅ (TPair $1 $!1 $!1 $3 $!3 $!3 $!3) ($!1 ⊔ $!3) $3).
      apply t_app; try solve [ccrush].
      - apply snd_pair_to_opair_inst.
      - eapply t_sub.
        eapply t_var; ccrush. 2-3 : ccrush.
        unfold TPair. cleanup. apply stp_refl; ccrush.
        eapply qs_qvar; ccrush.
    Qed.

End PairTransparentToOpaque.
