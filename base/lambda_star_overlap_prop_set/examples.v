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
(* Require Import NatSets. *)
(* Require Import setfacts. *)
(* Import NatSet.F. *)

Import OpeningNotations.
Open Scope opening.

Import QualNotations.
Local Open Scope qualifiers.

(* ### Examples ### *)

Notation " { a | b } ==> { c | d }"  := (TFun b d a c)
(at level 10, format "'[' '[hv' '{' a  '/' '|'  b '}' ']' '/  '  '==>'  '[hv' '{' c  '/' '|'  d '}' ']' ']'").

(* Ltac lookup_solve := *)
(*   match goal with *)
(*   | [ |- (if (beq_nat ?n ?n) then _ else _) = _ ] => rewrite <- beq_nat_refl; auto; try lookup_solve *)
(*   | [ |- (if (beq_nat ?n ?m) then _ else _) = _ ] => *)
(*       let H := fresh "H" in *)
(*       destruct (beq_nat n m) eqn:H; *)
(*       try apply beq_nat_true in H; *)
(*       try apply beq_nat_false in H; *)
(*       try lia; lookup_solve *)
(*   | [ |- Some (_, _) = Some (_,_) ] => try solve [repeat f_equal; auto; apply Q_lift_eq; Qcrush] *)
(*   end. *)

(* Ltac lookup := *)
(*   match goal with *)
(*   | [ |- (@indexr _ _ _) = _ ] => try solve [lookup_solve | simpl; lookup_solve] *)
(*   end. *)

Section Warmup.

  (* identity fun *)
  Example idfun      := (tabs #0).

  (* example context with three bindings a b c (0 1 2) *)
  Context (Γ012 := [(TUnit,∅); (TUnit,∅); (TUnit,∅)]).
  (* example context filter, including 0 1 2. *)
  Context (φ012 := ($$0 ⊔ $$1 ⊔ $$2)).

  (* * Γ012|Σ |-ᵠ⁰¹² λx. x : ( x:T1^{} -> T1^{x} )^{} *)
  Example idfun_typing : forall T1 Σ,
      closed_ty 0 3 (length Σ) T1 ->
      has_type Γ012 φ012 Σ idfun ({T1 | ∅} ==> {T1 | ##0}) ∅.
    intros. unfold φ012. unfold Γ012. unfold idfun.
    apply t_abs; ccrush.
    apply t_var; ccrush. 
  Qed.

  (** Γ|Σ ⊢ᵠ⁰¹² λx.x : ((a : A^{}) -> A^a)^d1 *)
  Example idfun_ht : forall Γ φ Σ d1 A ,
      closed_Qual 0 (length Γ) (length Σ) (Q_lift φ) ->
      closed_Qual 0 (length Γ) (length Σ) (Q_lift d1) ->
      closed_ty 0 (length Γ) (length Σ) A ->
      saturated Γ Σ d1 ->
      d1 ⊑↑ φ ->
      has_type Γ φ Σ idfun ({A | ∅} ==> {A | ##0}) d1.
    intros. unfold idfun.
    apply t_abs; ccrush.
    apply t_var; ccrush.
    rewrite Nat.eqb_refl. f_equal. f_equal. apply Q_lift_eq. Qcrush. 
  Qed.

  (** Γ012|Σ ⊢ᵠ⁰¹² λx.x : ((x : A^a,b) -> A^a,b+x)^∅ cannot be typed this way. A function's qualifier should contain all its free variables and
    their qualifiers.  *)
  Example idfun_nt :
    let q := $$0 ⊔ $$1 in
      forall Σ A, has_type Γ012 φ012 Σ idfun ({A | q} ==> {A | q ⊔ ##0}) ∅.
    intros. subst q. unfold idfun.
    apply t_abs; ccrush.
    4 : { apply t_var; ccrush.
          2 : { simpl. intuition. admit. (* contradiction: {0,1,3} ⊈ {3} *)  }
  Abort.

  (** Church encodings *)
  Section Church.
    (* Church true, respectively pi1: λa.λb.a *)
    Example church_true := (tabs (tabs #1)).
    (* Type scheme for pi1 := (a:A^{}) -> ((b:B^{}) -> A^{a})^{a}. *)
    Example church_true_T A B := {A | ∅} ==> {{B | ∅} ==> {A | ##1} | ##0}.
    (* Church false, respectively pi2: λa.λb.b  *)
    Example church_false := (tabs (tabs #0)).
    (* Type scheme for pi2 := (a:A^{}) -> ((b:B^{}) -> B^{b})^{}. *)
    Example church_false_T A B := {A | ∅} ==> {{B | ∅} ==> {B | ##0} | ∅}.

    (* Church pairs *)
    Example pair := (tabs (tabs (tabs (tapp (tapp #0 #2) #1)))).

    (* Pair[A,B]^q_X := ((a : A^{}) -> ((b : B^{}) -> X^q)^q⊔{a})^{} -> X^q *)
    Example TPair A B X q := {{A | ∅} ==> {{B | ∅} ==> {X | q} | q ⊔ ##0} | ∅} ==> {X | q}.

    (* Pair destructors *)
    Example fst := (tabs (tapp #0 church_true)).
    Example snd := (tabs (tapp #0 church_false)).

    Variables (Γ : tenv) (φ : qual) (Σ : senv) (A B : ty).
    Context (phiwf : closed_Qual 0 (length Γ) (length Σ) (Q_lift φ))
            (Awf   : closed_ty 0 (length Γ) (length Σ) A)
            (Bwf   : closed_ty 0 (length Γ) (length Σ) B).

    (** Γ|Σ ⊢ᵠ λa.λb.a : ((a:A^{}) -> ((b:B^{}) -> A^{a})^{a})^{} *)
    Example church_true_ht : has_type Γ φ Σ church_true (church_true_T A B) ∅.
      intros. unfold church_true. unfold church_true_T.
      apply t_abs; Qcrush. 1,2: crush.
      apply t_abs; ccrush. 1,2: eapply closed_ty_open'; eauto; Qcrush.
      econstructor. exists (∅). Qcrush. subst. rewrite Nat.eqb_refl. eauto. 
      fold open_rec_ty. repeat erewrite closed_ty_open_id; eauto. erewrite closed_qual_open_id; eauto. constructor. rewrite indexr_skip; eauto. rewrite indexr_head; eauto. f_equal. f_equal. apply Q_lift_eq. Qcrush. Qcrush.
  Qcrush. auto. Qcrush. 
      Unshelve. all: apply 1. 
    Qed.

    (** Γ|Σ ⊢ᵠ λa.λb.b : ((a:A^{}) -> ((b:B^{}) -> B^{b})^{})^{} *)
    Example church_false_ht : has_type Γ φ Σ church_false (church_false_T A B) ∅.
      intros. unfold church_false. unfold church_false_T.
      apply t_abs; Qcrush. 1,2: crush.
      apply t_abs; ccrush. 1,2: eapply closed_ty_open'; eauto; Qcrush.
      fold open_rec_ty. repeat erewrite closed_ty_open_id; eauto. erewrite closed_qual_open_id; eauto. constructor. replace (S (length Γ)) with (length ((A, ∅) :: Γ)) by auto. rewrite indexr_head; eauto. f_equal. f_equal. apply Q_lift_eq. Qcrush. Qcrush.
  Qcrush. eauto. Qcrush. 
      Unshelve. all: apply 1. 
    Qed.

  End Church.

End Warmup.

(** Derived Syntax and Typing Rules *)
(** Sequential composition *)
Definition seq (t1 t2 : tm): tm := (tapp (tapp (tabs (tabs #0)) t1) t2).

Lemma t_seq : forall Γ φ Σ t1 T1 q1 t2 T2 q2,
    has_type Γ φ Σ t1 T1 q1 ->
    has_type Γ φ Σ t2 T2 q2 ->
    saturated Γ Σ q1 ->
    saturated Γ Σ q2 ->
    has_type Γ φ Σ (seq t1 t2) T2 q2.
intros. unfold seq.
replace q2 with (openq q2 ##0); try solve [opening; auto].
eapply t_app with (T1:=T2) (df:=(openq q1 ∅)); eauto; crush.
* eapply t_app with (T1:=T1) (df:=∅); ccrush.
  erewrite closed_qual_open_id; eauto. 
  apply has_type_closed in H. intuition. 
  apply t_abs; ccrush. 
  apply has_type_closed in H0. intuition. 
  repeat erewrite closed_ty_open_id; eauto. 
  repeat erewrite closed_qual_open_id; eauto; Qcrush. 
  apply t_abs; ccrush.
  apply t_var; ccrush.
  rewrite Nat.eqb_refl. f_equal. f_equal. apply Q_lift_eq. Qcrush.
* unfold openq. Qcrush. 
* econstructor. inversion H3.
* unfold openq, open_qual. simpl. apply Q_lift_eq. Qcrush.
  Unshelve. all: try apply 1; try apply TUnit.
Qed.

