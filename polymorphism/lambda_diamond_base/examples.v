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
Require Import lambda_diamond.
Require Import examples_infra.

(* Require Import examples_infra. *)
Require Import NatSets.
Require Import setfacts.
Import NatSet.F.

Import OpeningNotations.
Local Open Scope opening.
Import QualNotations.
Local Open Scope qualifiers.

(* ### Examples ### *)

Notation " { a | b } ==> { c | d }"  := (TFun b d a c)
(at level 10, format "'[' '[hv' '{' a  '/' '|'  b '}' ']' '/  '  '==>'  '[hv' '{' c  '/' '|'  d '}' ']' ']'").

Section QPoly.

  Example idfun := (tabs #1).

  Example idfun_ty : forall {T}, closed_ty 0 0 0 T -> has_type [] {♦} [] idfun ({ T | {♦} } ==> { T | #!1 }) ∅.
    intros. unfold idfun.
    apply t_abs; ccrush.
    eapply t_var; ccrush.
  Qed.

  Example idfun_app1 : has_type [] {♦} [] (tapp idfun tunit) TUnit ∅.
    dep_app (∅) (∅) #!1.
    eapply t_app_fresh with (d1':=∅) (df':=∅); ccrush.
    apply idfun_ty; auto.
  Qed.

  Example idfun_app2 : has_type [] {♦} [] (tapp idfun (tref tunit)) (TRef ∅ TUnit) {♦}.
    dep_app (∅) ({♦}) #!1.
    eapply t_app_fresh with (d1':={♦}) (df':=∅); eauto; ccrush.
    apply idfun_ty; auto.
    change_qual ({♦} ⊔ ∅).
  Qed.

  Section FakeId.
    Variable (alloc : tm).
    Context (t_alloc : forall {Γ φ Σ T},
                       closed_ty 0 (‖Γ‖) (‖Σ‖) T ->
                       has_type Γ φ Σ alloc T {♦})
            (cl_alloc : closed_tm 0 0 0 alloc).

    (* fakeid example cannot be typed the same as the identity function *)
    Example fakeid := (tabs alloc).

    (* fakeid can't be typed as id *)
    Example fakeid_nt : forall {T}, closed_ty 0 0 0 T -> has_type [] {♦} [] fakeid ({ T | {♦} } ==> { T | #!1 }) ∅.
      intros. unfold fakeid in *.
      apply t_abs; ccrush.
      (* we can't apply t_alloc *)
      Fail apply t_alloc.
      (* and neither can we use subtyping in this context to deduce T {♦} <: T $!1 *)
    Abort.

  End FakeId.

  (** Church encodings *)
  Section Church.

    Section Bool.
      (* Church true, respectively pi1: λa.λb.a *)
      Example church_true := (tabs (tabs #3)).
      (* Type scheme for pi1 := (x:A^a) -> ((y:B^b) -> A^x)^{x}. *)
      Example church_true_T A a B b := {A | a} ==> {{B | b} ==> {A | #! 3} | #! 1}.
      (* Church false, respectively pi2: λa.λb.b  *)
      Example church_false := (tabs (tabs #1)).
      (* Type scheme for pi2 := (x:A^a) -> ((y:B^b) -> B^y)^{}. *)
      Example church_false_T A a B b := {A | a} ==> {{B | b} ==> {B | #! 1} | ∅}.

      Variables (Γ : tenv) (φ : qual) (Σ : senv) (A B : ty) (a b : qual).
      Context (phiwf : closed_qual 0 (‖Γ‖) (‖Σ‖) φ)
              (Awf   : closed_ty 0 (‖Γ‖) (‖Σ‖) A)
              (Bwf   : closed_ty 0 (‖Γ‖) (‖Σ‖) B)
              (awf   : closed_qual 0 (‖Γ‖) (‖Σ‖) a)
              (bwf   : closed_qual 0 (‖Γ‖) (‖Σ‖) b)
              .

      (** Γ|Σ ⊢ᵠ λa.λb.a : (x:A^a) -> ((y:B^b) -> A^x)^{x} *)
      Example church_true_ht : has_type Γ φ Σ church_true (church_true_T A a B b) ∅.
        intros. unfold church_true. unfold church_true_T.
        apply t_abs; ccrush.
        apply t_abs; ccrush.
        eapply t_var; ccrush.
      Qed.

      (** Typing with the less precise A^a requires that a is not fresh!
          Γ|Σ ⊢ᵠ λa.λb.a : ((x:A^a) -> ((y:B^b) -> A^a)^{x})^{}
          This type is required for using it as a projection on the TPair1 type below *)
      Example church_true_ht' : ♦∉ a -> has_type Γ φ Σ church_true ({A | a} ==> {{B | b} ==> {A | a } | #! 1}) ∅.
        intros. unfold church_true. eapply t_sub; auto. eapply church_true_ht.
        unfold church_true_T.
        apply s_fun; ccrush.
        * apply stp_refl; ccrush.
        * apply s_fun; ccrush.
          apply qstp_refl; ccrush.
          apply stp_refl; ccrush. apply qstp_refl; ccrush.
          apply stp_refl; ccrush. eapply qs_qvar; ccrush.
      Qed.

      Example church_true_ht'' : ♦∉ a -> has_type Γ φ Σ church_true ({A | a} ==> {{B | b} ==> {A | a } | #! 1}) (∅).
        intros. eapply t_sub. eapply church_true_ht'; eauto.
        apply stp_refl; ccrush. all: auto.
      Qed.

      (* This type is used for the projection on the TPair2 type with implicitly reachability polymorphic eliminations below *)
      Example church_true_ht''' : ♦∉ a -> has_type Γ φ Σ church_true ({A | a} ==> {{B | b} ==> {A | a } | #!0 ⊔ #!1}) (∅).
        intros. eapply t_sub. eapply church_true_ht''; eauto.
        apply s_fun; ccrush; auto. apply stp_refl; ccrush.
        apply stp_refl; ccrush. apply qs_sq; ccrush. all: ccrush; auto.
      Qed.

      Example church_false_ht : has_type Γ φ Σ church_false (church_false_T A a B b) ∅.
        intros. unfold church_false. unfold church_false_T.
        apply t_abs; ccrush.
        apply t_abs; ccrush.
        eapply t_var; ccrush.
      Qed.

      (* This type is required for using it as a projection on the TPair1 type below *)
      Example church_false_ht' : ♦∉ b -> has_type Γ φ Σ church_false ({A | a} ==> {{B | b} ==> {B | b} | #!1 }) ∅.
        intros. unfold church_false. eapply t_sub; auto. eapply church_false_ht.
        unfold church_false_T.
        apply s_fun; ccrush.
        * apply stp_refl; ccrush.
        * apply s_fun; ccrush.
          apply qs_sq; ccrush.
          apply stp_refl; ccrush. apply qstp_refl; ccrush.
          apply stp_refl; ccrush. eapply qs_qvar; ccrush.
      Qed.

      (* This type is used for the projection on the TPair2 type with implicitly reachability polymorphic eliminations below *)
      Example church_false_ht''' : ♦∉ b -> has_type Γ φ Σ church_false ({A | a} ==> {{B | b} ==> {B | b } | #!0 ⊔ #!1}) (∅).
        intros. eapply t_sub. eapply church_false_ht'; eauto.
        apply s_fun; ccrush; auto.
        apply stp_refl; ccrush. apply stp_refl; ccrush. apply qs_sq; ccrush. all: ccrush; auto.
      Qed.
    End Bool.

    Section Pair.

      Variables (Γ : tenv) (φ : qual) (Σ : senv) (A B : ty) (a b : qual).
      Context (phiwf : closed_qual 0 (‖Γ‖) (‖Σ‖) φ)
              (Awf   : closed_ty 0 (‖Γ‖) (‖Σ‖) A)
              (Bwf   : closed_ty 0 (‖Γ‖) (‖Σ‖) B)
              (awf   : closed_qual 0 (‖Γ‖) (‖Σ‖) a)
              (bwf   : closed_qual 0 (‖Γ‖) (‖Σ‖) b)
              (aobs  : a ⊑ φ)
              (bobs  : b ⊑ φ)
              .

      (* Church pairs, to the extent we can model them without support for type abstraction *)
      (* Pair introduction *)
      Example pair := (tabs (tabs (tabs (tapp (tapp #1 #5) #3)))).
      (* Pair destructors *)
      Example fst := (tabs (tapp #1 church_true)).
      Example snd := (tabs (tapp #1 church_false)).

      (* Version constraining the elimination to {a,b}, effectively restricting it to the projections.
        Pair[A^a,B^b]_C^c := ((x : A^a) -> ((y : B^b) -> C^c)^x)^{} -> C^c *)
      Example TPair1 A a B b C c := {{A | a} ==> {{B | b} ==> {C | c} | #!1} | ∅ } ==> {C | c}.

      (* Version implicitly polymorphic over the elimination's captured variables, as in the paper:
          Pair[A^a,B^b]_C^c := (f(x : A^a) -> ((y : B^b) -> C^c)^f,x)^{a,b,♦} -> C^c *)
      Example TPair2 A a B b C c := {{A | a} ==> {{B | b} ==> {C | c} | #!0 ⊔ #!1} | a ⊔ b ⊔ {♦}} ==> {C | c}.

      (* Γ|Σ ⊢ᵠ pair : ( (x : A^a) -> ((y : B^b) -> (Pair1[A^x,B^y]_C^c)^c,x,y)^c,x)^c *)
      Example t_pair1 : forall {C c},
        closed_ty 0 (length Γ) (length Σ) C ->
        closed_qual 0 (length Γ) (length Σ) c ->
        c ⊑ φ -> ♦∉ a -> ♦∉ b -> ♦∉ c ->
        senv_saturated Σ a -> senv_saturated Σ b -> senv_saturated Σ c ->
        (* lacking object-level type abstraction, the elimination's qualifier c leaks into the outer layers of qualifiers in the constructor: *)
        has_type Γ φ Σ pair ({A | a} ==> {{B | b} ==> {TPair1 A #!3 B #!3 C c | (c ⊔ #!3 ⊔ #!1) } | (c ⊔ #!1) }) (c).
        intros. unfold pair.
        apply t_abs; ccrush. unfold TPair1. ccrush.
        apply t_abs; ccrush. auto.
        apply t_abs; ccrush.
        change_qual (c ⊔ $!(S (‖ Γ ‖)) ⊔ $!(S (S (S (‖ Γ ‖))))); auto.
        dep_app ($!(S (‖Γ‖))) ($!(S (S ( S (‖Γ‖))))).
        apply t_app with (T1:=B); ccrush.
        * dep_app ($! (S (S (S (S (S (‖ Γ ‖))))))) $!(S (‖Γ‖)) #!1.
          apply t_app with (T1:=A); ccrush.
          + eapply t_var; ccrush.
          + eapply t_var; ccrush.
        * eapply t_var; ccrush.
      Qed.

      (* Γ|Σ ⊢ᵠ pair : ( (x : A^a) -> ((y : B^b) -> (Pair1[A^a,B^b]_C^c)^a,b,c)^a,c)^c *)
      Example t_pair1' : forall {C c},
        closed_ty 0 (length Γ) (length Σ) C ->
        closed_qual 0 (length Γ) (length Σ) c ->
        c ⊑ φ -> ♦∉ a -> ♦∉ b -> ♦∉ c ->
        senv_saturated Σ a -> senv_saturated Σ b -> senv_saturated Σ c ->
        (* lacking object-level type abstraction, the elimination's qualifier c leaks into the outer layers of qualifiers in the constructor: *)
        has_type Γ φ Σ pair ({A | a} ==> {{B | b} ==> {TPair1 A a B b C c | (a ⊔ b ⊔ c) } | (a ⊔ c) }) (c).
        intros. eapply t_sub; auto.
        * eapply @t_pair1 with (C:=C) (c:=c); ccrush.
        * apply s_fun. 1, 2 : unfold TPair1; ccrush. ccrush. (* automate!*) apply stp_refl; ccrush.
          cleanup; try lia. apply s_fun. 1,2 : unfold TPair1; ccrush.
          + rewrite (@qlub_commute a). apply qs_cong; ccrush.
            eapply qs_qvar; ccrush.
          + (* automate *) apply stp_refl; ccrush. apply qs_sq; ccrush.
          + cleanup; try lia. apply s_fun; ccrush.
            - replace (c ⊔ qset false (union (singleton (S (‖ Γ ‖))) (singleton (S (S (S (‖ Γ ‖)))))) {}N {}N)
              with    (($!(S (‖Γ‖)) ⊔ $!(S (S (S (‖Γ‖))))) ⊔ c).
              rewrite (@qlub_assoc a b). apply qs_cong_r; crush.
              eapply qs_trans with (d2 := a ⊔ $!(S (S (S (‖Γ‖))))).
              ** apply qs_cong_r; ccrush. eapply qs_qvar; ccrush.
              ** apply qs_cong; ccrush. eapply qs_qvar; ccrush.
              ** destruct c. ccrush.
            - apply s_fun; ccrush.
              ** apply stp_refl; ccrush. eapply qs_qvar; ccrush.
              ** apply s_fun; ccrush. apply qstp_refl; ccrush.
                 apply stp_refl; ccrush. eapply qs_qvar; ccrush.
                 apply stp_refl; ccrush. apply qstp_refl; ccrush.
            - apply stp_refl; ccrush. apply qstp_refl; ccrush.
      Qed.

      Example TPair2_ A a B b v C c := {{A | a} ==> {{B | b} ==> {C | c} | #!0 ⊔ #!1} | v ⊔ {♦}} ==> {C | c}.

        (* Γ|Σ ⊢ᵠ pair : ( (x : A^a) -> ((y : B^b) -> (Pair2[A^x,B^y]_C^c)^x,y,c)^x,c)^c *)
      Example t_pair2 : forall {C c},
        closed_ty 0 (length Γ) (length Σ) C ->
        closed_qual 0 (length Γ) (length Σ) c ->
        c ⊑ φ -> ♦∉ a -> ♦∉ b -> ♦∉ c ->
        senv_saturated Σ a -> senv_saturated Σ b -> senv_saturated Σ c ->
        (* lacking object-level type abstraction, the elimination's qualifier c leaks into the outer layers of qualifiers in the constructor: *)
        has_type Γ φ Σ pair ({A | a} ==> {{B | b} ==> {TPair2_ A #!3 B #!3 (a ⊔ b) C c | (c ⊔ #!3 ⊔ #!1) } | (c ⊔ #!1) }) (c).
        intros. unfold pair.
        apply t_abs; ccrush. unfold TPair2_. ccrush.
        apply t_abs; ccrush. auto.
        apply t_abs; ccrush. change_qual (c ⊔ $!(S (‖ Γ ‖)) ⊔ $!(S (S (S (‖ Γ ‖))))); auto.
        dep_app ($!(S (S (S (S (S (‖ Γ ‖)))))) ⊔ $!(S (‖Γ‖))) ($!(S (S ( S (‖Γ‖))))).
        apply t_app with (T1:=B); ccrush.
        * dep_app ($!(S (S (S (S (S (‖ Γ ‖))))))) ($!(S (‖Γ‖))) (qset false {}N (union (singleton 0) (singleton 1)) {}N).
          apply t_app with (T1:=A); ccrush.
          + eapply t_var; ccrush.
          + eapply t_var; ccrush.
          + destruct c. ccrush.
        * eapply t_var; ccrush.
      Qed.

       (* Γ|Σ ⊢ᵠ pair : ( (x : A^a) -> ((y : B^b) -> (Pair2[A^a,B^b]_C^c)^a,b,c)^a,c)^c *)
      Example t_pair2' : forall {C c},
        closed_ty 0 (length Γ) (length Σ) C ->
        closed_qual 0 (length Γ) (length Σ) c ->
        c ⊑ φ -> ♦∉ a -> ♦∉ b -> ♦∉ c ->
        senv_saturated Σ a -> senv_saturated Σ b -> senv_saturated Σ c ->
        (* lacking object-level type abstraction, the elimination's qualifier c leaks into the outer layers of qualifiers in the constructor: *)
        has_type Γ φ Σ pair ({A | a} ==> {{B | b} ==> {TPair2 A a B b C c | (a ⊔ b ⊔ c) } | (a ⊔ c) }) (c).
        intros. eapply t_sub; auto.
        * eapply @t_pair2 with (C:=C) (c:=c); ccrush.
        * apply s_fun. 1, 2 : unfold TPair2; unfold TPair2_; ccrush. ccrush. (* automate!*) apply stp_refl; ccrush.
          cleanup; try lia. apply s_fun. 1,2 : unfold TPair2; unfold TPair2_; ccrush.
          + rewrite (@qlub_commute a c). apply qs_cong; ccrush.
            eapply qs_qvar; ccrush.
          + (* automate *) apply stp_refl; ccrush. apply qs_sq; ccrush.
          + cleanup; try lia. apply s_fun; ccrush.
            - replace (c ⊔ qset false (union (singleton (S (‖ Γ ‖))) (singleton (S (S (S (‖ Γ ‖)))))) {}N {}N)
              with    (($!(S (‖Γ‖)) ⊔ $!(S (S (S (‖Γ‖))))) ⊔ c).
              rewrite (@qlub_assoc a b). apply qs_cong_r; crush.
              eapply qs_trans with (d2 := a ⊔ $!(S (S (S (‖Γ‖))))).
              ** apply qs_cong_r; ccrush. eapply qs_qvar; ccrush.
              ** apply qs_cong; ccrush. eapply qs_qvar; ccrush.
              ** destruct c. ccrush.
            - apply s_fun; ccrush.
              ** apply qstp_refl; ccrush. rewrite (@qlub_assoc a b). auto.
              ** apply stp_refl; ccrush. eapply qs_qvar; ccrush.
              ** apply s_fun; ccrush. apply qstp_refl; ccrush.
                 apply stp_refl; ccrush. eapply qs_qvar; ccrush.
                 apply stp_refl; ccrush. apply qstp_refl; ccrush.
            - apply stp_refl; ccrush. apply qstp_refl; ccrush.
      Qed.

      (* Assert that the projection functions are compatible with each pair type *)
      Example t_fst1 : forall {q},
        closed_qual 0 (‖Γ‖) (‖Σ‖) q ->
        ♦∉ a ->
        senv_saturated Σ a ->
        (* lacking object-level type abstraction, we pre-instantiate the pair *)
        has_type Γ φ Σ fst ({(TPair1 A a B b A a) | q} ==> {A | a}) (a).
        intros. unfold fst. apply t_abs; ccrush; auto.
        unfold TPair1. ccrush.
        dep_app ($!(S(‖Γ‖))) (∅).
        eapply t_app. eapply t_var; ccrush.
        apply church_true_ht'; ccrush.
        all : ccrush.
      Qed.

      Example t_snd1 : forall {q},
        closed_qual 0 (‖Γ‖) (‖Σ‖) q ->
        ♦∉ b ->
        senv_saturated Σ b ->
        (* lacking object-level type abstraction, we pre-instantiate the pair *)
        has_type Γ φ Σ snd ({(TPair1 A a B b B b) | q} ==> {B | b}) (b).
        intros. unfold snd. apply t_abs; ccrush; auto.
        unfold TPair1. ccrush.
        dep_app ($!(S(‖Γ‖))) (∅).
        eapply t_app. eapply t_var; ccrush.
        apply church_false_ht'; ccrush.
        all : ccrush.
      Qed.

      Example t_fst2 : forall {q},
        closed_qual 0 (‖Γ‖) (‖Σ‖) q ->
        ♦∉ a ->
        ♦∉ b ->
        ♦∉ q ->
        q ⊑ φ ->
        saturated Γ Σ a ->
        saturated Γ Σ b ->
        saturated Γ Σ q ->
        (* lacking object-level type abstraction, we pre-instantiate the pair *)
        has_type Γ φ Σ fst ({(TPair2 A a B b A a) | q} ==> {A | a}) (q ⊔ a ⊔ b).
        intros. unfold fst. apply t_abs; ccrush; auto.
        unfold TPair2. ccrush.
        dep_app (q) (∅).
        eapply t_app_fresh with (T1:=({A | a} ==> {{B | b} ==> {A | a} | #! 0 ⊔ #! 1})) (d1':= ∅) (df':=q); try solve [ccrush].
        * dom_equals ({♦}). destruct q. qdec.
          eapply t_sub with (T1:=TPair2 A a B b A a) (d1:=$!(S (‖Γ‖))); ccrush.
          - unfold TPair2. eapply t_var; ccrush.
          - eapply s_fun; ccrush.
            unfold TPair2. eapply qs_qvar; ccrush.
            apply stp_refl; ccrush. apply qs_sq; ccrush.
            apply stp_refl; ccrush. apply qs_sq; ccrush.
        * apply church_true_ht'''; ccrush.
      Qed.

      Example t_snd2 : forall {q},
        closed_qual 0 (‖Γ‖) (‖Σ‖) q ->
        ♦∉ a ->
        ♦∉ b ->
        ♦∉ q ->
        q ⊑ φ ->
        saturated Γ Σ a ->
        saturated Γ Σ b ->
        saturated Γ Σ q ->
        (* lacking object-level type abstraction, we pre-instantiate the pair *)
        has_type Γ φ Σ snd ({(TPair2 A a B b B b) | q} ==> {B | b}) (q ⊔ a ⊔ b).
        intros. unfold snd. apply t_abs; ccrush; auto.
        unfold TPair2. ccrush.
        dep_app (q) (∅).
        eapply t_app_fresh with (T1:=({A | a} ==> {{B | b} ==> {B | b} | #! 0 ⊔ #! 1})) (d1':= ∅) (df':=q); try solve [ccrush].
        * dom_equals ({♦}). destruct q. qdec.
          eapply t_sub with (T1:=TPair2 A a B b B b) (d1:=$!(S (‖Γ‖))); ccrush.
          - unfold TPair2. eapply t_var; ccrush.
          - eapply s_fun; ccrush.
            unfold TPair2. eapply qs_qvar; ccrush.
            apply stp_refl; ccrush. apply qs_sq; ccrush.
            apply stp_refl; ccrush. apply qs_sq; ccrush.
        * apply church_false_ht'''; ccrush.
      Qed.

      Context (ta tb : tm)
              (ht_ta : has_type Γ φ Σ ta A a)
              (ht_tb : has_type Γ φ Σ tb B b)
              (nf_a  : ♦∉ a)
              (nf_b  : ♦∉ b)
              (sat_a : saturated Γ Σ a)
              (sat_b : saturated Γ Σ b).

      Example pair_ab := (tapp (tapp pair ta) tb).

      Example pair_intro1 : forall {C c},
        closed_ty 0 (length Γ) (length Σ) C ->
        closed_qual 0 (length Γ) (length Σ) c ->
        c ⊑ φ -> ♦∉ c -> senv_saturated Σ c ->
        has_type Γ φ Σ pair_ab (TPair1 A a B b C c) (a ⊔ b ⊔ c).
        intros. unfold TPair1. unfold pair_ab.
        dep_app (a ⊔ c) b.
        apply t_app with (T1:=B); ccrush.
        dep_app (c) (a).
        apply t_app with (T1:=A); ccrush; auto.
        fold (TPair1 A a B b C c). apply t_pair1'; ccrush.
      Qed.

      Example pair_intro2 : forall {C c},
        closed_ty 0 (length Γ) (length Σ) C ->
        closed_qual 0 (length Γ) (length Σ) c ->
        c ⊑ φ -> ♦∉ c -> senv_saturated Σ c ->
        has_type Γ φ Σ pair_ab (TPair2 A a B b C c) (a ⊔ b ⊔ c).
        intros. unfold TPair2. unfold pair_ab.
        dep_app (a ⊔ c) b.
        apply t_app with (T1:=B); crush; auto.
        dep_app (c) (a).
        apply t_app with (T1:=A); crush.
        fold (TPair2 A a B b C c). apply t_pair2'; ccrush. all : ccrush.
      Qed.

      (* Elimination on TPair1 *)
      Example pair1_elim1 : has_type Γ φ Σ (tapp fst pair_ab) A a.
        dep_app (a) (a ⊔ b ⊔ a).
        eapply t_app; try solve [ccrush].
        * eapply t_fst1; ccrush.
        * apply pair_intro1; ccrush.
      Qed.

      (* Elimination on TPair1 *)
      Example pair1_elim2 : has_type Γ φ Σ (tapp snd pair_ab) B b.
        dep_app (b) (a ⊔ b ⊔ b).
        eapply t_app; try solve [ccrush].
        * eapply t_snd1; ccrush.
        * apply pair_intro1; ccrush.
      Qed.

      (* Elimination on TPair2 *)
      Example pair2_elim1 : has_type Γ φ Σ (tapp fst pair_ab) A a.
        dep_app ((a ⊔ b ⊔ a) ⊔ a ⊔ b) (a ⊔ b ⊔ a).
        eapply t_app; try solve [ccrush].
        * eapply t_fst2; ccrush.
        * apply pair_intro2; ccrush.
      Qed.

      (* Elimination on TPair2 *)
      Example pair2_elim2 : has_type Γ φ Σ (tapp snd pair_ab) B b.
        dep_app ((a ⊔ b ⊔ b) ⊔ a ⊔ b)  (a ⊔ b ⊔ b).
        eapply t_app; try solve [ccrush].
        * eapply t_snd2; ccrush.
        * apply pair_intro2; ccrush.
      Qed.

      (* TPair2 elimination behaves like a case expression on the pair with arbitrary capabilities *)
      Section CapabilityPoly.
        Context (c0 c1 : id)
                (t_c1 : has_type Γ φ Σ $c1 ({B | b } ==> {TUnit | ∅ }) $!c1)
                (t_c0 : has_type Γ φ Σ $c0 ({A | a} ==> {TUnit | ∅}) $!c0)
                (t_c1' : forall {Γ φ}, has_type Γ φ Σ $c1 ({B | b } ==> {TUnit | ∅ }) $!c1)
                (t_c0' : forall {Γ φ}, has_type Γ φ Σ $c0 ({A | a} ==> {TUnit | ∅}) $!c0)
                (cl_c0 : closed_qual 0 (‖Γ‖) (‖Σ‖) $!c0)
                (cl_c1 : closed_qual 0 (‖Γ‖) (‖Σ‖) $!c1)
                (c0visible : $!c0 ⊑ φ)
                (c1visible : $!c1 ⊑ φ)
                (c0_overlap: (a ⊔ b ⊔ ∅) ⋒ $!c0 ⊑ (a ⊔ b ⊔ {♦}))
                (c1_overlap: (a ⊔ b ⊔ ∅) ⋒ $!c1 ⊑ (a ⊔ b ⊔ {♦}) )
                (* For simplicity, assume that those capabilities have an empty qualifier.*)
                (sat_c0 : saturated Γ Σ $!c0)
                (sat_c1 : saturated Γ Σ $!c1)
                .

        (** { a => b => c0(a) } *)
        Example use_pair_c0 := (tabs (tabs (tapp $c0 #3))).
        (** { a => b => c1(b) } *)
        Example use_pair_c1 := (tabs (tabs (tapp $c1 #1))).

        Example t_use_pair_c0 : has_type Γ φ Σ use_pair_c0 ({A | a} ==> {{B | b} ==> {TUnit | ∅ } | #!0 ⊔ #!1 }) ($!c0).
          unfold use_pair_c0. apply t_abs; ccrush. auto.
          (* self-type abstraction *)
          apply t_sub with (T1:= ({B | b} ==> {TUnit | ∅})) (d1:=(($!c0 ⊔ $!‖Γ‖) ⊔ $!(S (‖Γ‖)))).
          * assert (Hcl0: closed_qual 0 (S (S (‖Γ‖))) (‖Σ‖) $!c0). eapply closed_qual_monotone; eauto.
            apply t_abs; ccrush.
            change_qual ($♦c0 ⊔ $!(‖Γ‖) ⊔ $!(S (‖Γ‖))); ccrush.
            change_qual ($!c0 ⊔ $!(‖Γ‖) ⊔ $!(S (‖Γ‖))). auto.
            dep_app ($!c0) ($!(S (‖ Γ ‖))).
            apply t_app with (T1:=A); try solve [ccrush].
            + eapply t_sub. eapply t_c0'.
              apply s_fun; ccrush. apply qs_sq; auto; ccrush.
              apply stp_refl; ccrush. eapply qs_qvar; ccrush. ccrush. auto.
            + eapply t_var; ccrush.
              change_qual ($♦c0 ⊔ $!(‖Γ‖) ⊔ $!(S (‖Γ‖)) ⊔ $!(S (S (‖Γ‖))) ⊔ $!(S (S (S (‖Γ‖))))); ccrush.
          * apply stp_refl; crush.
            replace (($!c0 ⊔ $!‖Γ‖) ⊔ $!(S (‖Γ‖))) with ($!(S (‖Γ‖)) ⊔ (($!c0) ⊔ $!‖Γ‖)).
            replace (qset false (union (singleton (‖ Γ ‖)) (singleton (S (‖ Γ ‖)))) {}N {}N) with ($!(S(‖Γ‖)) ⊔ $!‖Γ‖).
            apply qs_cong; crush. eapply qs_self; ccrush. all : ccrush.
          * ccrush.
          * change_qual ($!(‖Γ‖) ⊔ $!(S (‖Γ‖))). auto.
        Qed.

        Example t_use_pair_c1 : has_type Γ φ Σ use_pair_c1 ({A | a} ==> {{B | b} ==> {TUnit | ∅ } | #!0 ⊔ #!1 }) ($!c1).
          unfold use_pair_c1. apply t_abs; ccrush. auto.
          (* self-type abstraction *)
          apply t_sub with (T1:= ({B | b} ==> {TUnit | ∅})) (d1:=(($!c1 ⊔ $!‖Γ‖) ⊔ $!(S (‖Γ‖)))).
          * assert (Hcl1: closed_qual 0 (S (S (‖Γ‖))) (‖Σ‖) $!c1). eapply closed_qual_monotone; eauto.
            apply t_abs; ccrush.
            change_qual ($♦c1 ⊔ $!(‖Γ‖) ⊔ $!(S (‖Γ‖))); ccrush.
            change_qual ($!c1 ⊔ $!(‖Γ‖) ⊔ $!(S (‖Γ‖))). auto.
            dep_app ($!c1) ($!(S (S (S (‖ Γ ‖))))).
            apply t_app with (T1:=B); try solve [ccrush].
            + eapply t_sub. eapply t_c1'.
              apply s_fun; ccrush. apply qs_sq; auto; ccrush.
              apply stp_refl; ccrush. eapply qs_qvar; ccrush. ccrush. auto.
            + eapply t_var; ccrush.
              change_qual ($♦c1 ⊔ $!(‖Γ‖) ⊔ $!(S (‖Γ‖)) ⊔ $!(S (S (‖Γ‖))) ⊔ $!(S (S (S (‖Γ‖))))); ccrush.
          * apply stp_refl; crush.
            replace (($!c1 ⊔ $!‖Γ‖) ⊔ $!(S (‖Γ‖))) with ($!(S (‖Γ‖)) ⊔ ($!c1 ⊔ $!‖Γ‖)).
            replace (qset false (union (singleton (‖ Γ ‖)) (singleton (S (‖ Γ ‖)))) {}N {}N) with ($!(S(‖Γ‖)) ⊔ $!‖Γ‖).
            apply qs_cong; crush. eapply qs_self; ccrush. all : ccrush.
          * ccrush.
          * change_qual ($!(‖Γ‖) ⊔ $!(S (‖Γ‖))). auto.
        Qed.

        Example elim_pair_c0 : has_type Γ φ Σ (tapp pair_ab use_pair_c0) TUnit (∅).
          dep_app (a ⊔ b ⊔ ∅) ($!c0).
          eapply t_app_fresh with (T1:={A | a} ==> {{B | b} ==> {TUnit | ∅} | #! 0 ⊔ #! 1}) (d1':=$! c0) (df':=a ⊔ b ⊔ ∅); try solve [ccrush].
          * specialize (@pair_intro2 TUnit (∅)) as t_p. unfold TPair2 in t_p.
            eapply t_sub. eapply t_p. 1-5,7,8 : ccrush.
            apply s_fun. ccrush. ccrush. apply qs_sq; ccrush.
            apply stp_refl; ccrush. apply qs_sq; ccrush.
            apply stp_refl; ccrush.
          * apply t_use_pair_c0.
        Qed.

        Example elim_pair_c1 : has_type Γ φ Σ (tapp pair_ab use_pair_c1) TUnit (∅).
          dep_app (a ⊔ b ⊔ ∅) ($!c1).
          eapply t_app_fresh with (T1:={A | a} ==> {{B | b} ==> {TUnit | ∅} | #! 0 ⊔ #! 1}) (d1':=$!c1) (df':=a ⊔ b ⊔ ∅); try solve [ccrush].
          * specialize (@pair_intro2 TUnit (∅)) as t_p. unfold TPair2 in t_p.
            eapply t_sub. eapply t_p. 1-5,7,8 : ccrush.
            apply s_fun. ccrush. ccrush. apply qs_sq; ccrush.
            apply stp_refl; ccrush. apply qs_sq; ccrush.
            apply stp_refl; ccrush.
          * apply t_use_pair_c1.
        Qed.

      End CapabilityPoly.
    End Pair.

  End Church.

  Section DerivedSyntax.

    (** Sequential composition *)
    Definition seq (t1 t2 : tm): tm := (tapp (tapp (tabs (tabs #1)) t1) t2).

    Lemma t_seq : forall Γ φ Σ t1 T1 q1 t2 T2 q2,
        has_type Γ φ Σ t1 T1 q1 ->
        has_type Γ φ Σ t2 T2 q2 ->
        ♦∉ q1 ->
        ♦∉ q2 ->
        senv_saturated Σ q1 ->
        senv_saturated Σ q2 ->
        has_type Γ φ Σ (seq t1 t2) T2 q2.
      intros. unfold seq.
      dep_app (∅) q2 #!1. apply t_app with (T1:=T2); eauto; ccrush.
      * dep_app (∅) (q1).
        eapply t_app with (T1:=T1); ccrush.
        - apply t_abs; ccrush.
          apply t_abs; ccrush.
          eapply t_var; ccrush.
    Qed.

    (** val/let bindings  *)
    Definition val (t1 t2 : tm): tm := (tapp (tabs t2) t1).

    Lemma t_val : forall Γ φ df Σ t1 T1 q1 t2 T2 q2,
      closed_tm 2 (length Γ) (length Σ) t2 ->
      closed_ty 0 (‖Γ‖) (‖Σ‖) (TFun q1 q2 T1 T2) ->
      closed_qual 2 (length Γ) (length Σ) q2 ->
      closed_qual 0 (length Γ) (length Σ) df ->
      has_type Γ φ Σ t1 T1 q1 ->
      df ⊑ φ ->
      (q2 <~ᵈ ∅ ; ∅) ⊑ φ ->
      ♦∉ df ->
      ♦∉ q1 ->
      (* senv_saturated Γ Σ q1 -> *)
      senv_saturated Σ df ->
      senv_saturated Σ (q2 <~ᵈ ∅ ; ∅) ->
      not_free 0 T2 ->
      has_type ((false, T1, q1) :: (true, {T1 | q1} ==> {T2 | q2}, df):: Γ) (df ⊔ $!(S (length Γ)) ⊔ {♦}) Σ (open_tm' Γ t2) (open_ty' Γ T2) (openq' Γ q2) ->
      has_type Γ φ Σ (val t1 t2) (T2 <~ᵀ ∅ ; q1) (q2 <~ᵈ df ; q1).
      intros. unfold val. specialize (has_type_closed H3). intuition.
      eapply t_app; eauto; crush.
      apply t_abs; ccrush.
      unfold_open in H11.
      eapply @weaken_flt with (φ:=df ⊔ $! (S (length Γ)) ⊔ {♦}); ccrush.
    Qed.

    Lemma t_val_fresh : forall Γ φ df Σ t1 T1 q1 t2 T2 q2,
      closed_tm 2 (length Γ) (length Σ) t2 ->
      closed_ty 0 (‖Γ‖) (‖Σ‖) (TFun q1 q2 T1 T2) ->
      closed_qual 2 (length Γ) (length Σ) q2 ->
      closed_qual 0 (length Γ) (length Σ) df ->
      has_type Γ φ Σ t1 T1 q1 ->
      df ⊑ φ ->
      (q2 <~ᵈ ∅ ; ∅) ⊑ φ ->
      ♦∉ df ->
      saturated Γ Σ df ->
      saturated Γ Σ q1 ->
      senv_saturated Σ (q2 <~ᵈ ∅ ; ∅) ->
      not_free 0 T2 ->
      (♦∈ q1 -> not_free 1 T2) ->
      has_type ((false, T1, df ⋒ q1) :: (true, {T1 | df ⋒ q1} ==> {T2 | q2}, df):: Γ) (df ⊔ $!(S (length Γ)) ⊔ {♦}) Σ (open_tm' Γ t2) (open_ty' Γ T2) (openq' Γ q2) ->
      has_type Γ φ Σ (val t1 t2) (T2 <~ᵀ ∅ ; q1) (q2 <~ᵈ df ; q1).
      intros. unfold val. specialize (has_type_closed H3). intuition.
      eapply t_app_fresh with (d1':=q1) (df':=df); eauto; ccrush.
      apply t_abs; ccrush. constructor; ccrush. inversion H0; subst. auto. inversion H7. auto.
      unfold_open in H12.
      eapply @weaken_flt with (φ:=df ⊔ $! (S (length Γ)) ⊔ {♦}); ccrush. eapply has_type_filter; eauto.
    Qed.

    Lemma open_val : forall {k t t1 t2}, open_rec_tm k t (val t1 t2) = (val (open_rec_tm k t t1) (open_rec_tm (S (S k)) t t2)).
      intros. unfold val. simpl. auto.
    Qed.

  End DerivedSyntax.

  Section Closures.
    (* { val y = new Ref(unit); { x => y } } *)
    Example escaping_closure := (tapp (tabs (tabs #3)) (tref tunit)).

    (* The type of the let binding's body:
        (val y = _; { x => y }) :: (y : Ref[Unit^{}]^{}) => f(Unit => Ref[Unit^{}]^f)^y
     *)
    Example esc_ty_let : has_type [] {♦} [] (tabs (tabs #3)) ({TRef ∅ TUnit | {♦}} ==> { {TUnit | ∅}  ==> {TRef ∅ TUnit | #!0 } | #! 1}) ∅.
      apply t_abs; ccrush. repeat (constructor; ccrush).
      apply t_abs; ccrush. repeat (constructor; ccrush).
      eapply t_sub with (d1:=$!1 ⊔ $!2).
      * eapply t_sub. eapply t_var; ccrush.
        eapply stp_refl; ccrush. eapply qs_sq; ccrush. ccrush. eauto.
      * apply stp_refl; crush.
        eapply qs_self; ccrush.
      * ccrush.
      * ccrush.
    Qed.

    (* escaping_closure :: f(Unit => Ref[Unit]^f)^{} *)
    Example esc_ty : has_type [] {♦} [] escaping_closure ({TUnit | ∅}  ==> {TRef ∅ TUnit | #!0}) {♦}.
      unfold escaping_closure. dep_app (∅) ({♦} ⊔ ∅) #!1.
      eapply t_app_fresh with (T1:=TRef ∅ TUnit) (d1':={♦}) (df':=∅); crush.
      * cleanup. apply esc_ty_let.
      * ccrush.
      * ccrush.
    Qed.

  End Closures.

  Section ScopedCapabilities.

    Section TryCatch.
      (** Assume a Nothing type, a.k.a. the empty type, being a subtype of all types: *)
      Variable (Nothing : ty).
      Context (s_nothing : forall Γ Σ T q1 q2, qstp Γ Σ q1 q2 -> stp Γ Σ Nothing q1 T q2)
              (cl_nothing : closed_ty 0 0 0 Nothing).
      (** Assume an effects as capabilities model. The capability type for throwing (Unit-valued) exceptions is a function Unit => Nothing: *)
      Context (CanThrow := {TUnit | ∅} ==> {Nothing | ∅})
              (cl_canthrow : closed_ty 0 0 0 CanThrow).
      (** Assume we can allocate fresh capabilities for throwing exceptions: *)
      Variable (mkThrow : tm).
      Context (t_mkThrow : forall Γ φ Σ, closed_qual 0 (length Γ) (length Σ) φ -> has_type Γ φ Σ mkThrow CanThrow ∅).

      (** The try combinator, this one allocates a fresh capability and passes it to the given block:
            def try_(block) = val throw = mkThrow; block(throw)
      *)
      Example try_ := (tabs (val mkThrow (tapp #3 #1))).

      (** The type of the try combinator, encoding polymorphism as metalevel quantification.
              try : forall A. ((CanThrow^♦ => A^a)^♦ => A^a)^∅
        *)
      Example try_ty : forall A a Γ φ Σ,
          closed_qual 0 (length Γ) (length Σ) φ ->
          closed_ty 0 (length Γ) (length Σ) A ->
          closed_qual 0 (length Γ) (length Σ) a ->
          saturated Γ Σ a ->
          a ⊑ φ -> ♦∉ a ->
          has_type Γ φ Σ try_ ({{CanThrow | {♦} } ==> {A | a} | {♦} } ==> {A | a}) a.
        intros. unfold try_. specialize (t_mkThrow _ _ _ H) as H'.
        apply t_abs; ccrush.
        dep_app (a ⊔ $!(S (‖Γ‖))) (∅).
        eapply t_val with (T1:=CanThrow); try solve [ccrush].
        * apply t_mkThrow; ccrush.
        * apply saturated_senv_qlub; ccrush.
        * cleanup. dep_app ($!(S (‖Γ‖))) ($!(S (S (S (‖Γ‖))))).
          eapply t_app_fresh
          with (T1:=CanThrow) (d1':= $! (S (S (S (‖ Γ ‖))))) (df' := $! (S (‖ Γ ‖)) ⊔ {♦}); ccrush.
          - eapply t_var; ccrush.
          - eapply t_var; ccrush.
      Qed.

      Variable (Σ : senv).
      Context (c1 := 0) (Γ := [((false,TRef ∅ TUnit),∅)]).
      (** This block
            { throw => !c1 ; throw () }
        demonstrates a legal use of capabilities. *)
      Example nonescaping := (tabs (seq !($c1) (tapp #1 tunit))).

      (** Using the nonescaping block with try is indeed well-typed. *)
      Example nonescaping_ok : has_type Γ $!c1 Σ (tapp try_ nonescaping) TUnit ∅.
        unfold nonescaping. subst c1.
        dep_app (∅) ($!0).
        assert (Hf : closed_qual 0 (length Γ) (length Σ) $!0); crush. apply t_mkThrow in Hf.
        eapply t_app_fresh with (d1':=$!0) (df':=∅); ccrush.
        * eapply try_ty; ccrush.
        * subst Γ. apply t_abs; ccrush.
          apply t_seq with (T1:=TUnit) (q1:=∅); ccrush.
          + apply t_deref with (d:=$!0); ccrush.
            eapply t_var; ccrush.
          + apply t_sub with (T1:=Nothing) (d1:=∅); ccrush.
            dep_app ($!2) (∅).
            eapply t_app with (T1:=TUnit); ccrush.
            - subst CanThrow. eapply t_var; ccrush.
            - apply t_base; ccrush.
      Qed.

      (** In contrast, this block
              { throw => !c1 ; { () => throw () } }
        returns a closure over the capability, which is rejected by try. *)
      Example escaping := (tabs (seq !($c1) (tabs (tapp #3 tunit)))).
      (** First, the type of escaping indeed leaks the capability:
              escaping : ((c: CanThrow^{♦}) => (Unit => Unit)^{c})^{c1}
        *)
      Example escaping_ty : has_type Γ $!c1 Σ escaping ({CanThrow | {♦}} ==> {{TUnit | ∅} ==> {TUnit | ∅} | #!1}) $!c1.
        unfold escaping. subst c1. subst Γ.
        apply t_abs; ccrush.
        apply t_seq with (T1:=TUnit) (q1:=∅); ccrush.
        * apply t_deref with (d:=$!0); ccrush.
          eapply t_var; ccrush.
        * apply t_abs; ccrush.
          apply t_sub with (T1:=Nothing) (d1:=∅); ccrush.
          dep_app ($!2) (∅).
          eapply t_app with (T1:=TUnit); ccrush.
          - subst CanThrow. eapply t_var; ccrush.
          - apply t_base; ccrush.
        Qed.
      (** Now suppose we could type the following application: *)
      Example escaping_bad : exists S q, has_type Γ $!c1 Σ (tapp try_ escaping) S q.
        eexists. eexists. eapply t_app_fresh with (df:=∅). 4: eapply escaping_ty. cleanup.
        * (* We have a typing mismatch: *)
          (* suppose we can pick those qualifiers so that they don't overlap *)
          dom_equals ({♦}). admit.
          Fail eapply try_ty.
          (* try_ requires that the block `escaping` returns a disjoint function, but the type of `escaping` is
            dependent on its capability argument.  *)
      Abort.
    End TryCatch.

    Section Borrowing.
      (**
          borrow[A^a,B^b] : ((x : A^a) => ((block: (A^a => B^b)^♦) => B^b)^{x,a,b})^a,b
      *)
      Example borrow := (tabs (tabs (tapp #1 #3))).
      Example TBorrow A a B b := ({A | a} ==> {{{A | a} ==> {B | b} | {♦}} ==> {B | b} | a ⊔ b ⊔ #!1}).
      Example t_borrow : forall {Γ φ Σ A a B b},
        closed_qual 0 (length Γ) (length Σ) φ ->
        closed_ty 0 (length Γ) (length Σ) A ->
        closed_qual 0 (length Γ) (length Σ) a ->
        senv_saturated Σ a -> ♦∉ a -> a ⊑ φ ->
        closed_ty 0 (length Γ) (length Σ) B ->
        closed_qual 0 (length Γ) (length Σ) b ->
        senv_saturated Σ b -> ♦∉ b -> b ⊑ φ ->
        has_type Γ φ Σ borrow (TBorrow A a B b) (a ⊔ b).
        intros. unfold borrow. unfold TBorrow.
        apply t_abs; ccrush. eauto.
        apply t_abs; ccrush. eauto.
        dep_app $!(S (S (S (length Γ)))) a.
        eapply t_app with (T1:=A); ccrush.
        * eapply t_var; ccrush.
        * eapply t_sub; ccrush. eapply t_var; ccrush.
          apply stp_refl; ccrush.
          eapply qs_qvar; ccrush.
      Qed.

      (* Γ = c1 : Ref[Unit]^{c1} *)
      Context (c1 := 0)
              (Γ := [(false, TRef ∅ TUnit, ∅)])
              (φ := $!c1)
              (Σ : senv).

      (** An OK use of borrow:
              borrow(c1) { c2 => !c2 }
        *)
      Example borrow_ok  := (tapp (tapp borrow $c1) (tabs !(#1))).
      Example borrow_ok_ty : has_type Γ φ Σ borrow_ok TUnit ∅.
        unfold borrow_ok. subst c1. subst Γ. subst φ.
        dep_app (∅ ⊔ ∅) (∅).
        eapply t_app_fresh with (T1:=({(TRef ∅ TUnit) | ∅} ==> {TUnit | ∅})) (df':=∅ ⊔ ∅) (d1':=∅); ccrush.
        * dep_app (∅ ⊔ ∅) (∅) (∅ ⊔ ∅ ⊔ #!1).
          apply t_app with (T1:=(TRef ∅ TUnit)); crush.
          + apply t_borrow; ccrush.
          + eapply t_sub. eapply t_var; ccrush. all : eauto.
            apply stp_refl; ccrush. eapply qs_qvar; ccrush.
          + ccrush.
        * apply t_abs; ccrush.
          eapply t_deref; ccrush.
          eapply t_var; ccrush.
      Qed.

      (** A bad use of borrow:
              borrow(c1) { c2 => !c1 } // error c1 not directly accessible
        *)
      Example borrow_bad := (tapp (tapp borrow $c1) (tabs !($c1))).
      (* first, consider the type of the block : *)
      Example borrow_bad_block_ty : has_type Γ φ Σ (tabs !($c1)) ({TRef ∅ TUnit | ∅} ==> {TUnit | ∅}) $!c1.
        subst c1. subst Γ. subst φ.
        apply t_abs; ccrush.
        eapply t_deref; ccrush.
        eapply t_var; ccrush.
      Qed.
      (* now suppose this is typable: *)
      Example borrow_bad_ty : exists S q, has_type Γ φ Σ borrow_bad S q.
        eexists. eexists. unfold borrow_bad.
        (* both the function and argument of the application alias c1... *)
        apply t_app_fresh with (T1:={(TRef ∅ TUnit) | ∅} ==> {TUnit | ∅}) (df':=$!c1) (d1':=$!c1). (* ... which means the block function expected by borrow(c1) must alias c1 too *)
        4 : eapply borrow_bad_block_ty. cleanup.
        (* Borrow's type requires that the block is separate having just the {♦} qualifier, but the current type
           demands the qualifier {♦,c1} (overlap with c1 allowed). We also cannot use subsumption to shrink this to {♦}, due to the negative occurrence.
           Hence, we are stuck. *)
      Abort.

    End Borrowing.

  End ScopedCapabilities.

End QPoly.
