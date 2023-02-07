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
Require Import f_sub_diamond.
Require Import examples_infra.

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

Notation "∀<:{ a | b }.{ c | d }"  := (TAll b d a c)
(at level 10, format "'[' '[hv' '∀<:{' a  '/' '|'  b '}.{' ']' '/  '  '[hv' c  '/' '|'  d '}' ']' ']'").

Notation "⊤" := TTop.

(* shorthand if upper bound is the top type *)
Notation "∀<:{ a }.{ c | d }" := (TAll a d ⊤ c) (at level 10, only parsing).
(* even shorter *)
Notation "∀.{ c | d }" := (TAll {♦} d ⊤ c) (at level 10, only parsing).

Section QPoly.

  Example idfun := (ttabs (tabs #1)).

  (* ∀X<:⊤^♦. ((x : X^♦) -> X^x)^∅ *)
  Example idfun_ty : has_type [] {♦} [] idfun (∀<:{ {♦} }.{ { #1 | {♦} } ==> { #3 | #!1 } | ∅ }) ∅.
    unfold idfun.
    apply t_tabs; ccrush.
    apply t_abs; ccrush.
    eapply t_var; ccrush.
  Qed.

  Example idfun_app1 : has_type [] {♦} [] (tapp (ttapp idfun) tunit) TUnit ∅.
    dep_app (∅) (∅) #!1.
    eapply t_app_fresh with (d1':=∅) (df':=∅); ccrush.
    replace (∅) with (openq ∅ ∅ ∅); try solve [opening; ccrush].
    replace ({TUnit | {♦}} ==> {TUnit | #! 1}) with (({ #1 | {♦} } ==> { #3 | #!1 }) <~ᵀ TUnit ~ ∅ ; TUnit ~ ∅); try solve [opening; ccrush].
    eapply t_tapp_fresh with (d1':=∅) (df':=∅); ccrush.
    eapply t_sub. apply idfun_ty; auto.
    apply s_all; ccrush.
    apply s_fun; ccrush.
    apply stp_refl; ccrush. apply stp_refl; ccrush. apply qs_sq; ccrush. all : crush.
  Qed.

  Example idfun_app2 : has_type [] {♦} [] (tapp (ttapp idfun) (tref tunit)) (TRef ∅ TUnit) {♦}.
    change_qual (openq ∅ {♦} #!1).
    replace (TRef ∅ TUnit) with ((TRef ∅ TUnit) <~ᵀ TUnit ~ ∅; (TRef ∅ TUnit) ~ {♦}); try solve [opening; ccrush].
    eapply t_app_fresh with (d1':={♦}) (df':=∅); eauto; ccrush.
    (* perhaps counterintuitively, we use a non-growing application here!*)
    change_qual (openq ∅ ∅ ∅).
    replace ({ (TRef ∅ TUnit)| {♦}} ==> { (TRef ∅ TUnit)| #! 1}) with (({ #1 | {♦} } ==> { #3 | #!1 }) <~ᵀ TUnit ~ ∅ ; (TRef ∅ TUnit) ~ ∅); try solve [opening; ccrush].
    eapply t_tapp; ccrush.
    * eapply t_sub. apply idfun_ty; auto.
      apply s_all; ccrush.
      apply s_fun; ccrush.
      apply stp_refl; ccrush. apply stp_refl; ccrush. apply qs_sq; ccrush. all : crush.
    * change_qual ({♦} ⊔ ∅). apply t_ref; auto.
  Qed.

  Section FakeId.
    Variable (alloc : tm).
    (* exercise for the reader: make alloc a proper object-language type abstraction *)
    Context (t_alloc : forall {Γ φ Σ T},
                       closed_ty 0 (‖Γ‖) (‖Σ‖) T ->
                       has_type Γ φ Σ alloc T {♦})
            (cl_alloc : closed_tm 0 0 0 alloc).

    (* fakeid example cannot be typed the same as the identity function *)
    Example fakeid := (ttabs (tabs alloc)).

    (* fakeid can't be typed as id *)
    Example fakeid_nt : forall {T}, closed_ty 0 0 0 T -> has_type [] {♦} [] fakeid (∀.{ { #1 | {♦} } ==> { #3 | #!1 } | ∅ }) ∅.
      intros. unfold fakeid in *.
      apply t_tabs; ccrush.
      apply t_abs; ccrush.
      (* we can't apply t_alloc *)
      Fail apply t_alloc.
      (* and neither can we use subtyping in this context to deduce T {♦} <: T $!3 *)
    Abort.

  End FakeId.

  (** Church (or rather: Boehm-Berarducci) encodings *)
  Section Church.

    Section Bool.
      (* Church true, respectively pi1: ΛA.ΛB.λa:A.λb:B.a *)
      Example church_true := (ttabs (ttabs (tabs (tabs #3)))).
      (* Type for pi1 := ∀A^a<:Top^♦. (∀B^b<:Top^♦. ((x:A^a) -> ((y:B^b) -> A^x)^{x})^a,b)^a. *)
      Example church_true_T := ∀.{ ∀.{ { #3 | #!3 } ==> {{#3 | #!3} ==> {#7 | #! 3} | #! 1} | #!1 ⊔ #!3 } | #!1 } .
      (* Church false, respectively pi2: ΛA.ΛB.λa:A.λb:B.b  *)
      Example church_false := (ttabs (ttabs (tabs (tabs #1)))).
      (* Type for pi2 := ∀A^a<:Top^♦. (∀B^b<:Top^♦. ((x:A^a) -> ((y:B^b) -> B^y)^{x})^a,b)^a. *)
      Example church_false_T := ∀.{ ∀.{ { #3 | #!3 } ==> {{#3 | #!3} ==> {#5 | #! 1} | #! 1} | #!1 ⊔ #!3 } | #!1 }.

      Variables (Γ : tenv) (φ : qual) (Σ : senv).
      Context (phiwf : closed_qual 0 (‖Γ‖) (‖Σ‖) φ).

      Example church_true_ht : has_type Γ φ Σ church_true church_true_T ∅.
        intros. unfold church_true. unfold church_true_T.
        apply t_tabs; ccrush.
        apply t_tabs; ccrush.
        apply t_abs; ccrush.
        apply t_abs; ccrush.
        eapply t_var; ccrush.
      Qed.

      Example church_false_ht : has_type Γ φ Σ church_false church_false_T ∅.
        intros. unfold church_false. unfold church_false_T.
        apply t_tabs; ccrush.
        apply t_tabs; ccrush.
        apply t_abs; ccrush.
        apply t_abs; ccrush.
        eapply t_var; ccrush.
      Qed.

    End Bool.

    Section Pair.

      Variables (Γ : tenv) (φ : qual) (Σ : senv).
      Context (phiwf : closed_qual 0 (‖Γ‖) (‖Σ‖) φ).

      (* Church pairs *)
      (* Pair introduction: ΛA.ΛB.λx:A.λy:B.ΛC.λf.f x y *)
      Example pair := (ttabs (ttabs (tabs (tabs (ttabs (tabs (tapp (tapp #1 #7) #5))))))).
      (* Pair destructors *)
      Example fst := (ttabs (ttabs (tabs (tapp (ttapp #1) (tabs (tabs #3)))))).
      Example snd := (ttabs (ttabs (tabs (tapp (ttapp #1) (tabs (tabs #1)))))).

      (* Version constraining the elimination to {a,b}, effectively restricting it to the projections.
        Pair[A^a,B^b] := ∀C^c<:⊤^♦. (((x : A^a) -> ((y : B^b) -> C^c)^x)^{} -> C^c)^c,a,b *)
      Example TPair1 A a a' B b b' := ∀.{ {{A | a} ==> {{B | b} ==> { #5 | #!5 } | #!1} | ∅ } ==> {#3 | #!3} | #!1 ⊔ a' ⊔ b' }.

      (* pair : (∀A^a<:⊤^♦. (∀B^b<:⊤^♦. ( (x : A^a) -> ((y : B^b) -> (Pair1[A^x,B^y])^x,y)^x))^a,b)^∅ *)
      Example t_pair1_ :
        has_type [] ∅ [] pair (∀.{ ∀.{ {#3 | #!3} ==> {{#3 | #!3 } ==> {TPair1 #9 #!5 #!5 #9 #!5 #!3 | (#!3 ⊔ #!1) } | #!1 }  | #!1 ⊔ #!3 }  | #!1 }) ∅.
        unfold pair.
        apply t_tabs; ccrush. unfold TPair1. ccrush. (* 0/1*)
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

      (* allows the component qualifier parameters to overlap *)
      (* pair : (∀A^a<:⊤^♦. (∀B^b<:⊤^{a,♦}. ( (x : A^a) -> ((y : B^b) -> (Pair1[A^x,B^y])^x,y)^x))^a,b)^∅ *)
      Example t_pair1__ :
        has_type [] ∅ [] pair (∀.{ ∀<:{ #♦1 }.{ {#3 | #!3} ==> {{#3 | #!3 } ==> {TPair1 #9 #!5 #!5 #9 #!5 #!3 | (#!3 ⊔ #!1) } | #!1 }  | #!1 ⊔ #!3 }  | #!1 }) ∅.
        unfold pair.
        apply t_tabs; ccrush. unfold TPair1. ccrush. (* 0/1*)
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

      Example t_pair1 :
        has_type Γ φ Σ pair (∀.{ ∀.{ {#3 | #!3} ==> {{#3 | #!3 } ==> {TPair1 #9 #!5 #!5 #9 #!5 #!3 | (#!3 ⊔ #!1) } | #!1 }  | #!1 ⊔ #!3 }  | #!1 }) ∅.
        eapply weaken'. eapply weaken_store. apply t_pair1_. all : auto.
      Qed.

      Example t_pair1' :
        has_type Γ φ Σ pair (∀.{ ∀<:{ #♦1 }.{ {#3 | #!3} ==> {{#3 | #!3 } ==> {TPair1 #9 #!5 #!5 #9 #!5 #!3 | (#!3 ⊔ #!1) } | #!1 }  | #!1 ⊔ #!3 }  | #!1 }) ∅.
        eapply weaken'. eapply weaken_store. apply t_pair1__. all : auto.
      Qed.

      (* Version implicitly polymorphic over the elimination's captured variables, as in the paper:
          Pair[A^a,B^b] := ∀C^c<:⊤^♦. ((f(x : A^a) -> ((y : B^b) -> C^c)^f,x)^{a,b,♦} -> C^c)^c,a,b *)
      Example TPair2 A a a' a'' B b b' b'' := ∀.{ {{A | a} ==> {{B | b} ==> { #5 | #!5} | #!0 ⊔ #!1} | a' ⊔ b' ⊔ {♦}} ==> {#3 | #!3 } | #!1 ⊔ a'' ⊔ b'' }.

      (* pair : (∀A^a<:⊤^♦. (∀B^b<:⊤^♦. ( (x : A^a) -> ((y : B^b) -> (Pair2[A^x,B^y])^x,y)^x))^a,b)^∅ *)
      Example t_pair2_ :
        has_type [] ∅ [] pair (∀.{ ∀.{ {#3 | #!3} ==> {{#3 | #!3 } ==> {TPair2 #9 #!5 #!7 #!5 #9 #!5 #!5 #!3 | (#!3 ⊔ #!1) } | #!1 }  | #!1 ⊔ #!3 }  | #!1 }) ∅.
        unfold pair.
        apply t_tabs; ccrush. unfold TPair2. ccrush. (* 0/1*)
        apply t_tabs; ccrush. (* 2/3 *)
        apply t_abs; ccrush. (* 4/5 *)
        apply t_abs; ccrush. (* 6/7 *)
        apply t_tabs; ccrush. (* 8/9 *)
        apply t_abs; ccrush.  (* 10/11 *)
        change_qual (openq ($!11 ⊔ $!5) $!7 $!9).
        change_type (open_ty TUnit (∅) ($3) $!7 $9).
        apply t_app; ccrush.
        * change_qual (openq $!11 $!5 (#!0 ⊔ #!1)).
          change_type (open_ty TUnit (∅) $1 $!5 ({$ 3 | $! 7} ==> {$ 9 | $! 9})).
          apply t_app; ccrush.
          + eapply t_var; ccrush.
          + eapply t_sub. eapply t_var; ccrush.
            apply stp_refl; ccrush. apply qs_sq; ccrush. all : ccrush.
        * eapply t_var; ccrush.
      Qed.

      Example t_pair2 :
        has_type Γ φ Σ pair (∀.{ ∀.{ {#3 | #!3} ==> {{#3 | #!3 } ==> {TPair2 #9 #!5 #!7 #!5 #9 #!5 #!5 #!3 | (#!3 ⊔ #!1) } | #!1 }  | #!1 ⊔ #!3 }  | #!1 }) ∅.
        eapply weaken'. eapply weaken_store. apply t_pair2_. all : auto.
      Qed.

      (* Assert that the projection functions are compatible with each pair type *)
      (* fst : (∀A^a<:⊤^♦. (∀B^b<:⊤^♦. (Pair1[A^a,B^b]^{♦} -> A^a)^a,b)^a)^∅ *)
      Example t_fst1 :
        has_type [] ∅ [] fst (∀.{ ∀.{ {TPair1 #5 #!5 #!5 #5 #!5 #!3 | {♦} } ==> { #5 | #!5 } | #!1 ⊔ #!3 } | #!1 }) ∅.
        unfold fst.
        apply t_tabs; ccrush. unfold TPair1. ccrush.
        apply t_tabs; ccrush.
        apply t_abs; ccrush.
        change_qual (openq (qset false (union (singleton 1) (singleton 3)) {}N {}N) (∅) $!1).
        change_type (open_ty TUnit (∅) ({$ 1 | $! 1} ==> {{$ 3 | $! 3} ==> {$1 | $! 1} | #!1}) (∅) $1).
        apply t_app; ccrush.
        * change_qual (openq ($!5) $!1 (qset false (union (singleton 1) (singleton 3)) (singleton 1) {}N)).
          change_type (open_ty TUnit ∅ $1 $!1 ({{$ 1 | $! 1} ==> {{$ 3 | $! 3} ==> {# 5 | #! 5} | #! 1} | ∅} ==> {# 3 | #! 3})).
          eapply t_tapp_fresh with (d1':=$♦1) (df':=$♦5) ; ccrush.
          eapply t_sub.
          eapply t_var; ccrush.
          apply s_all. ccrush. ccrush.
          apply qs_sq; ccrush.
          eapply s_tvar_trans; ccrush. cleanup. apply stp_refl; ccrush. apply qs_sq; ccrush.
          all : ccrush.
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

      (* snd : (∀A^a<:⊤^♦. (∀B^b<:⊤^♦. (Pair1[A^a,B^b]^{♦} -> B^b)^a,b)^a)^∅ *)
      Example t_snd1 :
        has_type [] ∅ [] snd (∀.{ ∀.{ {TPair1 #5 #!5 #!5 #5 #!5 #!3 | {♦} } ==> { #3 | #!3 } | #!1 ⊔ #!3 } | #!1 }) ∅.
        unfold snd.
        apply t_tabs; ccrush. unfold TPair1. ccrush.
        apply t_tabs; ccrush.
        apply t_abs; ccrush.
        change_qual (openq (qset false (union (singleton 1) (singleton 3)) {}N {}N) (∅) $!3).
        change_type (open_ty TUnit (∅) ({$ 1 | $! 1} ==> {{$ 3 | $! 3} ==> {$3 | $! 3} | #!1}) (∅) $3).
        apply t_app; ccrush.
        * change_qual (openq ($!5) $!3 (qset false (union (singleton 1) (singleton 3)) (singleton 1) {}N)).
          change_type (open_ty TUnit ∅ $3 $!3 ({{$ 1 | $! 1} ==> {{$ 3 | $! 3} ==> {# 5 | #! 5} | #! 1} | ∅} ==> {# 3 | #! 3})).
          eapply t_tapp_fresh with (d1':=$♦3) (df':=$♦5) ; ccrush.
          eapply t_sub.
          eapply t_var; ccrush.
          apply s_all. ccrush. ccrush.
          apply qs_sq; ccrush.
          eapply s_tvar_trans; ccrush. cleanup. apply stp_refl; ccrush. apply qs_sq; ccrush.
          all : ccrush.
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

      (* fst : (∀A^a<:⊤^♦. (∀B^b<:⊤^♦. (Pair2[A^a,B^b]^{♦} -> A^a)^a,b)^a)^∅ *)
      Example t_fst2 :
        has_type [] ∅ [] fst (∀.{ ∀.{ {TPair2 #5 #!5 #!5 #!5 #5 #!5 #!3 #!3 | {♦} } ==> { #5 | #!5 } | #!1 ⊔ #!3 } | #!1 }) ∅.
        unfold fst.
        apply t_tabs; ccrush. unfold TPair2. ccrush.
        apply t_tabs; ccrush.
        apply t_abs; ccrush.
        change_qual (openq ($!1⊔$!3) (∅) $!1).
        change_type (open_ty TUnit (∅) ({$ 1 | $! 1} ==> {{$ 3 | $! 3} ==> {$1 | $! 1} | #!0 ⊔ #!1}) (∅) $1).
        eapply t_app_fresh with (d1':=∅) (df':=$♦1⊔$♦3); ccrush.
        * change_qual (openq ($!5) $!1 (qset false (union (singleton 1) (singleton 3)) (singleton 1) {}N)).
          change_type (open_ty TUnit ∅ $1 $!1 ({{$ 1 | $! 1} ==> {{$ 3 | $! 3} ==> {# 5 | #! 5} | #!0 ⊔ #!1} | {♦}} ==> {# 3 | #! 3})).
          eapply t_tapp_fresh with (d1':=$♦1) (df':=$♦5) ; ccrush.
          eapply t_sub.
          eapply t_var; ccrush.
          apply s_all. ccrush. ccrush.
          apply qs_sq; ccrush.
          eapply s_tvar_trans; ccrush. cleanup.
          apply s_fun. ccrush. ccrush. apply qs_sq; ccrush.
          apply stp_refl; ccrush. apply qs_sq; ccrush.
          apply stp_refl; ccrush. apply qs_sq; ccrush.
          all : ccrush.
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

      (* snd : (∀A^a<:⊤^♦. (∀B^b<:⊤^♦. (Pair[A^a,B^b]^{♦} -> B^b)^a,b)^a)^∅ *)
      Example t_snd2 :
        has_type [] ∅ [] snd (∀.{ ∀.{ {TPair2 #5 #!5 #!5 #!5 #5 #!5 #!3 #!3 | {♦} } ==> { #3 | #!3 } | #!1 ⊔ #!3 } | #!1 }) ∅.
        unfold snd.
        apply t_tabs; ccrush. unfold TPair2. ccrush.
        apply t_tabs; ccrush.
        apply t_abs; ccrush.
        change_qual (openq ($!1⊔$!3) (∅) $!3).
        change_type (open_ty TUnit (∅) ({$ 1 | $! 1} ==> {{$ 3 | $! 3} ==> {$3 | $!3} | #!0 ⊔ #!1}) (∅) $3).
        eapply t_app_fresh with (d1':=∅) (df':=$♦1⊔$♦3); ccrush.
        * change_qual (openq ($!5) $!3 (qset false (union (singleton 1) (singleton 3)) (singleton 1) {}N)).
          change_type (open_ty TUnit ∅ $3 $!3 ({{$ 1 | $! 1} ==> {{$ 3 | $! 3} ==> {# 5 | #! 5} | #!0 ⊔ #!1} | {♦}} ==> {# 3 | #! 3})).
          eapply t_tapp_fresh with (d1':=$♦3) (df':=$♦5) ; ccrush.
          eapply t_sub.
          eapply t_var; ccrush.
          apply s_all. ccrush. ccrush.
          apply qs_sq; ccrush.
          eapply s_tvar_trans; ccrush. cleanup.
          apply s_fun. ccrush. ccrush. apply qs_sq; ccrush.
          apply stp_refl; ccrush. apply qs_sq; ccrush.
          apply stp_refl; ccrush. apply qs_sq; ccrush.
          all : ccrush.
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

    End Pair.

  End Church.

End QPoly.