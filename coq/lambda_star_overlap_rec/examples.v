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

Notation " { a | b } ==> { c | d }"  := (TFun b d a c)
(at level 10, format "'[' '[hv' '{' a  '/' '|'  b '}' ']' '/  '  '==>'  '[hv' '{' c  '/' '|'  d '}' ']' ']'").

Section Warmup.

  (* identity fun *)
  Example idfun      := (tabs #1).

  (* example context with three bindings a b c (0 1 2) *)
  Context (Γ012 := [(TUnit,∅); (TUnit,∅); (TUnit,∅)]).
  (* example context filter, including 0 1 2. *)
  Context (φ012 := ($$0 ⊔ $$1 ⊔ $$2)).

  (** Γ012|Σ |-ᵠ⁰¹² λx. x : ( x:T1^{} -> T1^{x} )^{} *)
  Example idfun_typing : forall T1 Σ,
      closed_ty 0 3 (length Σ) T1 ->
      has_type Γ012 φ012 Σ idfun ({T1 | ∅} ==> {T1 | ##1}) ∅.
    intros. unfold φ012. unfold Γ012. unfold idfun. compute.
    apply t_abs; ccrush.
    T_VAR; ccrush.
  Qed.

  (** Γ|Σ ⊢ᵠ⁰¹² λx.x : ((a : A^{}) -> A^a)^d1 *)
  Example idfun_ht : forall Γ φ Σ d1 A ,
      closed_qual 0 (length Γ) (length Σ) φ ->
      closed_qual 0 (length Γ) (length Σ) d1 ->
      closed_ty 0 (length Γ) (length Σ) A ->
      saturated Γ Σ d1 ->
      d1 ⊑ φ ->
      has_type Γ φ Σ idfun ({A | ∅} ==> {A | ##1}) d1.
    intros. unfold idfun. compute.
    apply t_abs; ccrush.
    T_VAR; ccrush.
  Qed.

  (** Γ012|Σ ⊢ᵠ⁰¹² λx.x : ((x : A^a,b) -> A^a,b+x)^∅ cannot be typed this way. A function's qualifier should contain all its free variables and
    their qualifiers.  *)
  Example idfun_nt :
    let q := $$0 ⊔ $$1 in
      forall Σ A, has_type Γ012 φ012 Σ idfun ({A | q} ==> {A | q ⊔ ##1}) ∅.
    intros. subst q. unfold idfun.
    apply t_abs; ccrush.
    2 : { eapply t_sub with (d1:= $$4). T_VAR. ccrush.
          6 : { simpl. intuition. admit. (* contradiction: {0,1,4} ⊈ {3,4} *)  }
  Abort.

  (** Church encodings *)
  Section Church.
    (* Church true, respectively pi1: λa.λb.a *)
    Example church_true := (tabs (tabs #3)).
    (* Type scheme for pi1 := (a:A^{}) -> ((b:B^{}) -> A^{a})^{a}. *)
    Example church_true_T A B := {A | ∅} ==> {{B | ∅} ==> {A | ##3} | ##1}.
    (* Church false, respectively pi2: λa.λb.b  *)
    Example church_false := (tabs (tabs #1)).
    (* Type scheme for pi2 := (a:A^{}) -> ((b:B^{}) -> B^{b})^{}. *)
    Example church_false_T A B := {A | ∅} ==> {{B | ∅} ==> {B | ##1} | ∅}.

    (* Church pairs *)
    Example pair := (tabs (tabs (tabs (tapp (tapp #1 #5) #3)))).

    (* Pair[A,B]^q_X := ((a : A^{}) -> ((b : B^{}) -> X^q)^q⊔{a})^{} -> X^q *)
    Example TPair A B X q := {{A | ∅} ==> {{B | ∅} ==> {X | q} | q ⊔ ##1} | ∅} ==> {X | q}.

    (* Pair destructors *)
    Example fst := (tabs (tapp #1 church_true)).
    Example snd := (tabs (tapp #1 church_false)).

    Variables (Γ : tenv) (φ : qual) (Σ : senv) (A B : ty).
    Context (phiwf : closed_qual 0 (length Γ) (length Σ) φ)
            (Awf   : closed_ty 0 (length Γ) (length Σ) A)
            (Bwf   : closed_ty 0 (length Γ) (length Σ) B).

    (** Γ|Σ ⊢ᵠ λa.λb.a : ((a:A^{}) -> ((b:B^{}) -> A^{a})^{a})^{} *)
    Example church_true_ht : has_type Γ φ Σ church_true (church_true_T A B) ∅.
      intros. unfold church_true. unfold church_true_T.
      apply t_abs; ccrush.
      apply t_abs; ccrush.
      T_VAR; ccrush.
    Qed.

    (** Γ|Σ ⊢ᵠ λa.λb.b : ((a:A^{}) -> ((b:B^{}) -> B^{b})^{})^{} *)
    Example church_false_ht : has_type Γ φ Σ church_false (church_false_T A B) ∅.
      intros. unfold church_false. unfold church_false_T.
      apply t_abs; ccrush.
      apply t_abs; ccrush.
      T_VAR; ccrush.
    Qed.

    (* Γ|Σ ⊢ᵠ pair : ( (a : A^{}) -> ((b : B^{}) -> (Pair[A,B]^q_X)^q⊔{a,b})^q⊔{a} )^q *)
    Example t_pair : forall {X q},
      closed_ty 0 (length Γ) (length Σ) X ->
      closed_qual 0 (length Γ) (length Σ) q ->
      saturated Γ Σ q -> (* required in the lazy system *)
      q ⊑ φ ->
      has_type Γ φ Σ pair ({A | ∅} ==> {{B | ∅} ==> {TPair A B X q | (q ⊔ ##1 ⊔ ##3) } | q ⊔ ##1}) q.
      intros. unfold pair. unfold TPair.
      apply t_abs; ccrush.
      apply t_abs; ccrush.
      apply t_abs; simpl; ccrush.
      replace q with (openq (q ⊔ $$ (S (length Γ))) ($$(S (S (S (length Γ))))) q) at 19; try solve [opening].
      apply t_app with (T1:=B); ccrush.
      * replace (q ⊔ $$ (S (length Γ)))
        with (openq $$(S (S (S (S (S (length Γ)))))) $$(S (length Γ)) (q ⊔ ##1)) at 3; try solve [opening; auto].
        apply t_app with (T1:=A); ccrush.
        + T_VAR; ccrush.
        + T_VAR; ccrush.
      * T_VAR; ccrush.
    Qed.

    (** These Church encodings cannot be applied to arguments, unless there is a form of dependent function application that
        permits "deep" dependency in the type, or abstraction with function self qualifiers. The standard application rule
        t_app rule forbids general dependency on the argument in a function's codomain. *)
    Variable (a b: tm).
    Context (a_ht : has_type Γ φ Σ a A ∅) (b_ht : has_type Γ φ Σ b B ∅).
    Example church_true_use_bad : exists S q, has_type Γ φ Σ (tapp church_true a) S q.
      eexists. eexists. eapply t_app with (T1:=A) (df:=∅) (d1:=∅). cleanup.
      eapply church_true_ht. eapply a_ht.
      (* This condition states that the codomain of church_true should not be dependent on the argument (zero bound variables).
         However, there is a dangling bound variable in the codomain's qualifier, and we cannot proceed. *)
      admit.
    Abort.

  End Church.

End Warmup.

(** Derived Syntax and Typing Rules *)
(** Sequential composition *)
Definition seq (t1 t2 : tm): tm := (tapp (tapp (tabs (tabs #1)) t1) t2).

Lemma t_seq : forall Γ φ Σ t1 T1 q1 t2 T2 q2,
    has_type Γ φ Σ t1 T1 q1 ->
    has_type Γ φ Σ t2 T2 q2 ->
    saturated Γ Σ q1 ->
    saturated Γ Σ q2 ->
    has_type Γ φ Σ (seq t1 t2) T2 q2.
  intros. unfold seq.
  replace q2 with (openq (openq ∅ q1 ∅) q2 ##1);
    try solve [opening; auto].
  eapply t_app with (T1:=T2) (df:=(openq ∅ q1 ∅)); eauto; crush.
  * qual_destruct. eapply t_app with (T1:=T1); ccrush.
    + apply t_abs; ccrush.
      apply t_abs; ccrush.
      T_VAR; ccrush.
Qed.

(** val/let bindings  *)
Definition val (t1 t2 : tm): tm := (tapp (tabs t2) t1).

Lemma t_val : forall Γ φ df Σ t1 T1 q1 t2 T2 q2,
    closed_tm 2 (length Γ) (length Σ) t2 ->
    closed_ty 0 (length Γ) (length Σ) T2 ->
    closed_qual 2 (length Γ) (length Σ) q2 ->
    closed_qual 0 (length Γ) (length Σ) df ->
    has_type Γ φ Σ t1 T1 q1 ->
    df ⊑ φ ->
    saturated Γ Σ (openq ∅ ∅ q2) ->
    saturated Γ Σ q1 ->
    saturated Γ Σ df ->
    has_type ((T1, df ⋒ q1) :: ({T1 | df ⋒ q1} ==> {T2 | q2}, df):: Γ) (df ⊔ $$(S (length Γ))) Σ (open_tm' Γ t2) (open_ty' Γ T2) (openq' Γ q2) ->
    has_type Γ φ Σ (val t1 t2) T2 (openq df q1 q2).
  intros. unfold val. specialize (has_type_closed H3). intuition.
  eapply t_app with (df:=df); eauto; crush.
  apply t_abs; ccrush.
  erewrite closed_ty_open'_id in H8; eauto.
  unfold_open in H8.
  eapply @weaken_flt with (φ:=(df ⊔ $$ (S (length Γ)))); ccrush.
  apply has_type_filter in H8. eapply unopen_subqual; eauto.
  unfold_open in H8. unfold_open. eapply subqual_trans; eauto. ccrush.
Qed.

Lemma open_val : forall {k t t1 t2}, open_rec_tm k t (val t1 t2) = (val (open_rec_tm k t t1) (open_rec_tm (S (S k)) t t2)).
  intros. unfold val. simpl. auto.
Qed.

(** Functional Abstraction (Sec. 2.2) *)
Section FunAbs.
  Variables (Σ : senv) (φ  : qual).

  Section IntroEx.
    Variables (q  : qual).
    Context (qwf : closed_qual 0 0 (length Σ) q)
            (satq : saturated [] Σ q)
            (phiwf: closed_qual 0 1 (length Σ) φ)
            (qwfphi : q ⊑ φ)
            (c := 0)
            (cvisible : $c ∈ᵥ φ).

    (** val c = ...                   // : Ref[Int] ^ q+c
        def deref(x : Unit) = { ! c } // : (Unit => Unit) ^ q+c   *)
    Example deref := (tabs (! $0)).
    Example deref_ty : has_type [(TRef TUnit, q)] φ Σ deref ({TUnit | ∅} ==> {TUnit | ∅}) (q ⊕ c).
      intros. unfold deref. subst c.
      apply t_abs; ccrush.
      apply t_deref with (d:=q ⊕ 0).
      T_VAR; ccrush.
    Qed.

    (** deref(unit) // : Unit *)
    Example deref_app : has_type [(TRef TUnit, q)] φ Σ (tapp deref tunit) TUnit ∅.
      intros. replace (∅) with (openq (q ⊕ c) ∅ ∅); try solve [opening; auto].
      eapply t_app; ccrush. rewrite qglb_empty_right.
      apply deref_ty.
    Qed.

  End IntroEx.

  (** Function Arguments (Sec. 2.2.1) *)
  Section FunArgs.
      Context (phiwf: closed_qual 0 2 (length Σ) φ)
              (c1 := 0)
              (c2 := 1)
              (c1visible : $c1 ∈ᵥ φ)
              (c2visible : $c2 ∈ᵥ φ)
              (Γ12 := [(TRef TUnit, ∅);(TRef TUnit, ∅)]).

      (**
          Note: this version of λ* lacks a ⊥ qualifier (and base type other than Unit).
          We replace the example shown in the paper by an equivalent one, which is typeable in this version.

          def addRef(c : Ref[Unit]^{}) = { !c1; !c } // : // (Ref[Unit]^{} => Unit)^{c1}
      *)
      Example addRef := (tabs (seq (! $c1) (! #1))).
      Example addRef_ty : has_type Γ12 φ Σ addRef ({TRef TUnit | ∅} ==> {TUnit | ∅}) $$c1.
        unfold addRef.
        apply t_abs; ccrush.
        eapply t_seq with (T1:=TUnit) (q1:=∅); crush.
        * apply t_deref with (d:=$$c1); crush.
          T_VAR; crush.
        * apply t_deref with (d:=$$3); crush.
          T_VAR; crush.
      Qed.

      (**
          The application addRef(c2) is legal, since c1 and c2 are different and hence do not overlap.
      *)
      Example addRef_app_ok : has_type Γ12 φ Σ (tapp addRef $c2) TUnit ∅.
        replace (∅) with (openq $$c1 $$c2 ∅); try solve [opening; auto].
        apply t_app with (T1:=(TRef TUnit)); ccrush.
        * apply addRef_ty.
        * T_VAR; crush.
      Qed.

      (* With the addRef_ty type assignment above, it is impossible to type the application addRef(c1), as expected. *)
      Example addRef_app_bad : exists S q, has_type Γ12 φ Σ (tapp addRef $c1) S q.
        eexists. eexists. (* note the (minimal!) qualifiers of addRef and $c1, which are both just c1. *)
        eapply t_app with (d1:=$$c1) (df:=$$c1); cleanup.
        (* The type of addRef above enforces strict separation between the function and its argument (i.e., the domain qualifier is ∅),
           but both addRef and $c1 contain $c1 in their qualifiers. Note that we end up needing to type addRef with the singleton set {c1} in the domain's qualifier.
           However, due to contravariance, no possible subsumption step could ever eliminate {c1}.  *)
        Abort.

      (* The paper shows the following alternative typing for addRef that would permit overlapping with $c1, and thus
         permit addRef_app_bad. *)
      Example addRef_alt_ty : has_type Γ12 φ Σ addRef ({TRef TUnit | $$c1} ==> {TUnit | ∅}) $$c1.
        unfold addRef.
        apply t_abs; ccrush.
        eapply t_seq with (T1:=TUnit) (q1:=∅); crush.
        * apply t_deref with (d:=$$c1); crush.
          T_VAR; crush.
        * apply t_deref with (d:=($$c1) ⊕ 3); crush.
          T_VAR; ccrush.
      Qed.

      Example addRef_alt_app_c1: has_type Γ12 φ Σ (tapp addRef $c1) TUnit ∅.
        replace (∅) with (openq $$c1 $$c1 ∅); try solve [opening; auto].
        apply t_app with (T1:=(TRef TUnit)); ccrush.
        * apply addRef_alt_ty.
        * T_VAR; crush.
      Qed.

  End FunArgs.

  (** Function Return Values (Sec. 2.2.2) *)
  Section FunRet.
    Context (Γ0 := [(TRef TUnit, ∅)])
            (phiwf: closed_qual 0 (length Γ0) (length Σ) φ)
            (c0 := 0)
            (c0visible : $c0 ∈ᵥ φ).

    (** def retunEnv(x) = { !c0; c0 } // : (Unit => Ref[Unit]^{c0})^{c0} *)
    Example returnEnv : has_type Γ0 φ Σ (tabs (seq ! ($c0) $c0)) ({TUnit | ∅} ==> {TRef TUnit | $$c0}) $$c0.
      subst c0. apply t_abs; ccrush.
      apply t_seq with (T1:=TUnit) (q1:=∅); ccrush.
      * apply t_deref with (d:=$$0).
        T_VAR; crush.
      * T_VAR; crush.
    Qed.

    (** def returnArg(x) = { !x; x } // : ((x : Ref[Unit]^∅) => Ref[Unit]^{x})^∅  *)
    Example returnArg : has_type Γ0 φ Σ (tabs (seq !(#1) #1)) ({TRef TUnit | ∅} ==> {TRef TUnit | ##1}) ∅.
      apply t_abs; ccrush.
      apply t_seq with (T1:=TUnit) (q1:=∅); ccrush.
      * apply t_deref with (d:=$$2).
        T_VAR; ccrush.
      * T_VAR; ccrush.
    Qed.

    (** Lacking the ⊥ qualifier for base types, this version of λ* cannot type the general reference allocation (tref t) for t of arbitrary type.
        Otherwise, reduction steps of the form (tref t) -> (tref t') could violate type preservation, i.e.,
        it is not clear if the argument is a non-reference type without adding further mechanisms (such as the ⊥ qualifier).
        Therefore, we adopt a limited reference allocation that enforces the type of reference is exactly Ref[Unit], then we can type the example:

           def returnFresh(x) = { val y = new Ref(x); !y; y } // : Unit => Ref[Unit]^∅
     *)
    Example returnFresh : has_type Γ0 φ Σ (tabs (val (tref #1) (seq !(#1) #1))) ({TUnit | ∅} ==> {TRef TUnit | ∅}) ∅.
      apply t_abs; ccrush.
      replace (∅) with (openq ∅ ∅ ##1); try solve [opening;ccrush].
      eapply t_val; ccrush.
      * eapply t_ref; ccrush. 
        eapply t_var; ccrush.
      * apply t_seq with (T1:=TUnit) (q1:=∅); ccrush.
      - apply t_deref with (d:=$$4).
        T_VAR; ccrush.
      - T_VAR; ccrush.
    Qed.

  End FunRet.
End FunAbs.

(** Escaping Closures (Sec. 2.3) *)
Section Escaping.
  Variables (Γ : tenv) (Σ : senv) (φ : qual).
  Context (phiwf : closed_qual 0 (length Γ) (length Σ) φ).

  (** The type of the closure

          val y = ...; { () => new Ref(unit) }

      at the point of its occurrence is

          (Unit => Ref[Unit]^∅)^∅.
   *)
  Example fresh_ty_internal : has_type Γ φ Σ (tabs (tref tunit)) ({TUnit | ∅} ==> {TRef TUnit | ∅}) ∅.
    apply t_abs; ccrush.
    apply t_ref with (d:=∅).
    apply t_base; crush.
  Qed.

  (** When escaping the lexical scope, the type of the closure

          val c = { val y = ...; { () => new Ref(unit) } }

      remains

          (Unit => Ref[Unit]^∅)^∅.
    *)
  Example fresh_ty_external : has_type Γ φ Σ (val tunit (tabs (tref tunit))) ({TUnit | ∅} ==> {TRef TUnit | ∅}) ∅.
    replace (∅) with (openq ∅ ∅ ∅); try solve [opening;crush].
    eapply t_val; ccrush.
    apply t_abs; ccrush.
    apply t_ref with (d:=∅). apply t_base. crush.
  Qed.

  Context (y := length Γ).

  (** The type of the closure in

           val y = new Ref(unit); { () => !y }

      at the point of its occurrence is

           (Unit => Unit)^{y}.
   *)
  Example closure_deref_internal : has_type (((TRef TUnit),∅) :: Γ) (φ ⊔ (just_fv y)) Σ (tabs !($y)) ({TUnit | ∅} ==> {TUnit | ∅}) $$y.
    subst y.
    apply t_abs; ccrush.
    apply t_deref with ($$(length Γ)); ccrush.
    T_VAR; ccrush.  
  Qed.

  (** When escaping the lexical scope, the type of the closure

          val c = { val y = new Ref(unit); { () => !y } }

      becomes

          (Unit => Unit)^∅.
   *)
  Example closure_deref_external : has_type Γ φ Σ (val (tref tunit) (tabs !(#3))) ({TUnit | ∅} ==> {TUnit | ∅}) ∅.
    replace (∅) with (openq ∅ ∅ ##1); try solve [opening;crush].
    eapply t_val; ccrush.
    apply t_ref with (d:=∅). apply t_base. crush.
    apply t_abs; ccrush.
    apply t_deref with ($$(S (length Γ))); ccrush.
    T_VAR; ccrush.
  Qed.

  (** The type of the closure in

           val y = new Ref(unit); { () => y }

      at the point of its occurrence is

           (Unit => Ref[Unit]^{y})^{y}.
   *)
  Example closure_ret_internal : has_type (((TRef TUnit),∅) :: Γ) (φ ⊔ $$y) Σ (tabs $y) ({TUnit | ∅} ==> {TRef TUnit | $$y}) $$y.
    subst y.
    apply t_abs; ccrush.
    T_VAR; ccrush.
  Qed.

  (** In order to assign a type to the escaping closure

          val c = { val y = new Ref(unit); { () => y } }

      we need abstraction by function self qualifiers.
  *)
  Example closure_escape := (val (tref tunit) (tabs #3)).
  (**
      This example also explains why the dependent function application in λ* is restricted, so that the argument variable may
      only occur in the function codomain's qualifier, but not within the codomain type:

      Using the standard encoding of let/val, we may desugar the above code into a function application:

          { val y = new Ref(unit); { () => y } } ~> ({ y => { () => y } })(new Ref(unit))

      where

          { y => { () => y } } : (y : Ref[Unit]^∅) => (Unit => Ref[Unit]^{y})^{y}
          new Ref(unit) :  Ref[Unit]^∅

      If we freely permitted applications of functions with dependency in the codomain type, then we would obtain

          ({ y => { () => y } })(new Ref(unit)) : ((Unit => Ref[Unit]^{y})^{y})[y ↦ ∅] = (Unit => Ref[Unit]^{∅})^{∅}

      But this is wrong! We would not be able to distinguish between this example and

          { val y = ...; { () => new Ref(unit) } }

      where the closure always returns a fresh reference. The solution is introducing function self-qualifiers.
  *)

End Escaping.

(** Key Higher-Order Programming Patterns (Sec. 2.4) *)
Section HigherOrder.

  (** Non-Interference (Sec. 2.4.2) *)
  Section NonInterference.
    (** For simplicity, we define par as a sequential execution of two thunks. *)
    Example par := (tabs (tabs (seq (tapp #3 tunit) (tapp #1 tunit)))).
    (** par inhabits the type shown in the paper, i.e.,

        par : ((a : (Unit => Unit)^{}) => ((b : (Unit => Unit)^{}) => Unit)^{a})^{}
     *)
    Example t_par : forall {Γ Σ φ}, closed_qual 0 (length Γ) (length Σ) φ ->
      has_type Γ φ Σ par ({{TUnit | ∅} ==> {TUnit | ∅} | ∅} ==> {{{TUnit | ∅} ==> {TUnit | ∅} | ∅} ==> {TUnit | ∅} | ##1}) ∅.
      intros. unfold par. apply t_abs; ccrush. apply t_abs; ccrush. eapply t_seq with (T1:=TUnit) (q1:=∅); ccrush.
      * replace (∅) with (openq $$(S (length Γ)) ∅ ∅); try solve [opening;crush].
        eapply t_app; ccrush; intuition.
        - T_VAR; ccrush.
        - apply t_base; ccrush.
      * replace (∅) with (openq $$(S (S (S (length Γ)))) ∅ ∅); try solve [opening;crush].
        eapply t_app; ccrush; intuition.
        - T_VAR; ccrush.
        - apply t_base; ccrush.
    Qed.

    Variables (Γ : tenv) (Σ : senv) (φ : qual).
    Context (phiwf : closed_qual 0 (length Γ) (length Σ) φ).

    (**
        OK use of par:
        val c1 = new Ref(unit); val c2 = new Ref(unit); par { !c1 } { ! c2 }
    *)
    Example noninterfering := (val (tref tunit)
                                  (val (tref tunit)
                                      (tapp (tapp par (tabs !(#5))) (tabs !(#3))))).

    Example noninterfering_ty : has_type Γ φ Σ noninterfering TUnit ∅.
      unfold noninterfering. replace (∅) with (openq ∅ ∅ ∅); try solve [opening;crush].
      eapply t_val with (T1:=TRef TUnit) (df:=∅); crush.
      apply t_ref with (d:=∅). apply t_base. crush.
      unfold open_tm'. repeat rewrite open_val. replace (openq' Γ ∅) with (openq $$(S (length Γ)) ∅ ∅); try solve [opening; crush].
      eapply t_val with (df:=$$(S (length Γ))) (T1:=TRef TUnit); ccrush.
      * eapply t_ref; ccrush. apply t_base; ccrush.
      * replace (∅) with (openq $$(S (length Γ)) $$(S (S (S (length Γ)))) ∅) at 8; try solve [opening;crush].
        eapply t_app with (T1:=({TUnit | ∅} ==> {TUnit | ∅})) (df:=$$(S (length Γ))); ccrush.
        + replace ($$(S (length Γ))) with (openq ∅ $$(S (length Γ)) ##1); try solve [opening;crush].
          eapply t_app with (df:=∅); ccrush.
          ** fold (seq (tapp #3 tunit) (tapp #1 tunit)). fold par. eapply t_par; ccrush.
          ** apply t_abs; ccrush. eapply t_deref with (d:=$$(S (length Γ))); T_VAR; ccrush.
        + apply t_abs; ccrush. eapply t_deref; T_VAR; ccrush.
        Unshelve. all : apply 0.
    Qed.

    (**
        Bad use of par:
        val c1 = new Ref(unit); val c2 = new Ref(unit); par { !c1; !c2 } { !c1; !c2 }
    *)
    Example interfering := (val (tref tunit)
                               (val (tref tunit)
                                   (tapp (tapp par (tabs (seq !(#5) !(#3)))) (tabs (seq !(#5) !(#3)))))).

    (** first, let's type the following subterm: *)
    Example aux1 : has_type [(TRef TUnit, ∅) ; (TRef TUnit, ∅)] ($$0 ⊔ $$1) [] (tabs (seq !($0) !($1))) ({TUnit | ∅} ==> {TUnit | ∅}) ($$0 ⋓ $$1).
      apply t_abs; ccrush. eapply t_seq with (q1:=∅); ccrush.
      * eapply t_deref. T_VAR; ccrush.
      * eapply t_deref. T_VAR; ccrush.
    Qed.

    (** now, show that interfering can't be typed *)
    Example interfering_bad : exists S q, has_type [(TRef TUnit, ∅) ; (TRef TUnit, ∅)] ($$0 ⊔ $$1) []
                                          (tapp (tapp par (tabs (seq !($0) !($1)))) (tabs (seq !($0) !($1)))) S q.
      eexists. eexists. eapply t_app. 2: eapply aux1.
      eapply t_app. 2: eapply aux1.
      (* from t_par we know 1) df = ∅ and 2) d20 = ##1, and
         3) openq ?df ($$ (0) ⊔ $$ (1)) ?d20 ⋒ ($$ (0) ⊔ $$ (1)) = ∅.

         However, 1), 2), and 3) together are unsatisfiable:
      *)
      assert (((openq ∅ ($$ (0) ⊔ $$ (1)) ##1) ⋒ ($$ (0) ⊔ $$ (1))) = ($$ (0) ⊔ $$ (1))). {
        opening. simpl. qdec.
      }
    Abort.

  End NonInterference.

  (** Non-Escaping (Sec. 2.4.3) *)
  Section NonEscape.
    (** Assume a Nothing type, a.k.a. the empty type, being a subtype of all types: *)
    Variable (Nothing : ty).
    Context (s_nothing : forall Γ Σ T q1 q2, qstp Γ Σ q1 q2 -> stp Γ Σ Nothing q1 T q2)
            (cl_nothing : closed_ty 0 0 0 Nothing).
    (** Assume an effects as capabilities model. The capability type for throwing (Unit-valued) exceptions is a function Unit => Nothing: *)
    Context (CanThrow := (TFun ∅ ∅ TUnit Nothing))
            (cl_canthrow : closed_ty 0 0 0 CanThrow).
    (** Assume we can allocate fresh capabilities for throwing exceptions: *)
    Variable (mkThrow : tm).
    Context (t_mkThrow : forall Γ φ Σ, closed_qual 0 (length Γ) (length Σ) φ -> has_type Γ φ Σ mkThrow CanThrow ∅).

    (** The try combinator, this one allocates a fresh capability and passes it to the given block:

           def try_(block) = val throw = mkThrow; block(throw)
     *)
    Example try_ := (tabs (val mkThrow (tapp #3 #1))).

    (** The type of the try combinator, encoding polymorphism as metalevel quantification.

            try : forall A. ((CanThrow^∅ => A^∅)^∅ => A^∅)^∅
       *)
    Example try_ty : forall A Γ φ Σ,
        closed_qual 0 (length Γ) (length Σ) φ ->
        closed_ty 0 (length Γ) (length Σ) A ->
        has_type Γ φ Σ try_ ({{CanThrow | ∅} ==> {A | ∅} | ∅} ==> {A | ∅}) ∅.
      intros. unfold try_. specialize (t_mkThrow _ _ _ H) as H'.
      apply t_abs; ccrush. replace (∅) with (openq $$(S (length Γ)) ∅ ∅) at 9; try solve [opening].
      eapply t_val; ccrush.
      * apply t_mkThrow; ccrush.
      * replace (∅) with (openq $$(S (length Γ)) $$(S (S (S (length Γ)))) ∅) at 12; try solve [opening].
        eapply t_app with (T1:=CanThrow); ccrush.
        - T_VAR; ccrush.
        - T_VAR; ccrush.
    Qed.

    Variable (Σ : senv).
    Context (c1 := 0) (Γ := [(TRef TUnit,∅)]).
    (** This block

           { throw => !c1 ; throw () }

       demonstrates a legal use of capabilities. *)
    Example nonescaping := (tabs (seq !($c1) (tapp #1 tunit))).

    (** Using the nonescaping block with try is indeed well-typed. *)
    Example nonescaping_ok : has_type Γ $$c1 Σ (tapp try_ nonescaping) TUnit ∅.
      unfold nonescaping. subst c1.
      replace (∅) with (openq ∅ $$0 ∅); try solve [opening; auto].
      assert (Hf : closed_qual 0 (length Γ) (length Σ) $$0); crush. apply t_mkThrow in Hf.
      eapply t_app; ccrush.
      * eapply try_ty; crush.
      * subst Γ. apply t_abs; ccrush.
        apply t_seq with (T1:=TUnit) (q1:=∅); ccrush.
        + apply t_deref with (d:=$$0); ccrush.
          T_VAR; ccrush.
        + replace (∅) with (openq $$2 ∅ ∅) at 5; try solve [opening; auto].
          eapply t_app with (T1:=TUnit); ccrush.
          - apply t_sub with (T1:=CanThrow) (d1:=$$2); ccrush.
            ** subst CanThrow. T_VAR; ccrush.
            ** subst CanThrow. repeat (constructor; ccrush).
          - apply t_base; ccrush.
    Qed.

    (** In constrast, this block

            { throw => !c1 ; { () => throw () } }

       returns a closure over the capability, which is rejected by try. *)
    Example escaping := (tabs (seq !($c1) (tabs (tapp #3 tunit)))).
    (** First, the type of escaping indeed leaks the capability:

            escaping : ((c: CanThrow^{}) => (Unit => Unit)^{c})^{c1}
      *)
    Example escaping_ty : has_type Γ $$c1 Σ escaping ({CanThrow | ∅} ==> {{TUnit | ∅} ==> {TUnit | ∅} | ##1}) $$c1.
      unfold escaping. subst c1. subst Γ.
      apply t_abs; ccrush.
      apply t_seq with (T1:=TUnit) (q1:=∅); ccrush.
      * apply t_deref with (d:=$$0); ccrush.
        T_VAR; ccrush.
      * apply t_abs; ccrush. replace (∅) with (openq $$2 ∅ ∅) at 9; try solve [opening; auto].
        eapply t_app with (T1:=TUnit); ccrush.
        + apply t_sub with (T1:=CanThrow) (d1:=$$2); ccrush.
          - T_VAR; ccrush.
          - unfold CanThrow. repeat (constructor; ccrush).
        + apply t_base; ccrush.
    Qed.
    (** Now suppose we could type the following application: *)
    Example escaping_bad : exists S q, has_type Γ $$c1 Σ (tapp try_ escaping) S q.
      eexists. eexists. eapply t_app with (df:=∅). 2: eapply escaping_ty. cleanup.
      * (* We have a typing mismatch: *)
        Fail eapply try_ty.
        (* try_ requires that the block `escaping` returns a disjoint function, but the type of `escaping` is
           dependent on its capability argument.  *)
    Abort.

  End NonEscape.

  (** Non-Accessibility (Sec. 2.4.4) *)
  Section NonAccess.
    (** Assume primitives for doing IO effects via a (global) capability. *)
    Variables (CanIO : ty) (doIO : tm).
    Context (cl_CanIO : closed_ty 0 0 0 CanIO)
            (t_doio  : forall Γ φ Σ, has_type Γ φ Σ doIO ({CanIO | ∅} ==> {TUnit | ∅}) ∅)
            (cl_doIO : closed_tm 0 0 0 doIO).

    Example withoutIO := (tabs (tabs (tapp #1 tunit))).
    (** The type of the withoutIO combinator, encoding polymorphism as metalevel quantification.

            withoutIO : forall A. ((cap: CanIO^∅) => ((block : (Unit => A^∅)^∅) => A^∅))^{cap})^∅
      *)
    Example t_withoutIO : forall A Γ φ Σ,
        closed_qual 0 (length Γ) (length Σ) φ ->
        closed_ty 0 (length Γ) (length Σ) A ->
        has_type Γ φ Σ withoutIO ({CanIO | ∅} ==> {{{TUnit | ∅} ==> {A | ∅} | ∅} ==> {A | ∅}| ## (1)}) ∅.
      intros. unfold withoutIO.
      apply t_abs; ccrush.
      apply t_abs; ccrush.
      replace (∅) with (openq $$(S (S (S (length Γ)))) ∅ ∅) at 15; try solve [opening; auto].
      apply t_app with (T1:=TUnit); ccrush.
      * T_VAR; ccrush.
      * apply t_base; ccrush.
    Qed.

    #[local] Hint Unfold just_fv : core.

    (* Γ := canIO : CanIO^{canIO}; c1 : Ref[Unit]^{c1} *)
    Context (canIO := 0)
            (c1 := 1)
            (Γ := [(TRef TUnit, ∅); (CanIO, ∅)])
            (φ := $$canIO ⊔ $$c1)
            (Σ : senv).
    (** An OK use of withoutIO.

            withoutIO(canIO) { !c1 }
      *)
    Example withoutIO_ok  := (tapp (tapp withoutIO $canIO) (tabs !($c1))).
    Example withoutIO_ok_ty : has_type Γ φ Σ withoutIO_ok TUnit ∅.
      unfold withoutIO_ok. subst c1. subst canIO. subst Γ. subst φ.
      replace (∅) with (openq $$0 $$1 ∅) at 3; try solve [opening; auto].
      apply t_app with (T1:=({TUnit | ∅} ==> {TUnit | ∅})); ccrush.
      * replace ($$0) with (openq ∅ $$0 ##1); try solve [opening; auto].
        apply t_app with (T1:=CanIO); ccrush.
        + apply t_withoutIO; ccrush.
        + T_VAR; ccrush.
      * apply t_abs; ccrush.
        eapply t_deref. T_VAR; ccrush.
    Qed.

    (** A bad use of withoutIO.

            withoutIO(canIO) { !c1; doIO(canIO) }
      *)
    Example withoutIO_bad := (tapp (tapp withoutIO $canIO) (tabs (seq !($c1) (tapp doIO $canIO)))).
    (* First, consider the block's type
           { !c1; doIO(canIO) } : (Unit => Unit)^{c1,canIO} *)
    Example withoutIO_bad_block_ty : has_type [(TRef TUnit, ∅); (CanIO, ∅)] ($$0 ⊔ $$1) Σ (tabs (seq !($1) (tapp doIO $0))) ({TUnit | ∅} ==> {TUnit | ∅}) ($$0 ⊔ $$1).
      apply t_abs; ccrush. apply t_seq with (T1:=TUnit) (q1:=∅); ccrush.
      * eapply t_deref. T_VAR; ccrush.
      * replace (∅) with (openq ∅ $$0 ∅) at 6; try solve [opening; auto].
        eapply t_app; ccrush.
        T_VAR; ccrush.
    Qed.
    (* then, suppose we can assign a type to withoutIO_bad: *)
    Example withoutIO_bad_ty : exists S q, has_type Γ φ Σ withoutIO_bad S q.
      specialize withoutIO_bad_block_ty as Hblk. eexists. eexists.
      unfold withoutIO_bad.
      eapply t_app. eapply t_app.
      (* first, let's type these subexpressions, which is easy: *)
      2: T_VAR; ccrush. 5: apply withoutIO_bad_block_ty.
      (* matching against t_withoutIO, we have
         1) df = ∅, 2) d20 = ##1, and 3) openq ?df (∅ ⊕ canIO) ?d20 ⋒ ($$ (0) ⋓ $$ (1)) = ∅
         However, these constraints are unsatisfiable, i.e., the overlap is not disjoint
      *)
      assert (openq ∅ (∅ ⊕ canIO) ##1 ⋒ ($$ (0) ⊔ $$ (1)) = $$canIO). {
        subst canIO. opening. ccrush. unfold just_fv. f_equal. fnsetdec.
      }
    Abort.

  End NonAccess.

  (** Borrowing (Sec. 2.4.5) *)
  Section Borrowing.
    (**
        borrow[A,B] : ((x : A^∅) => ((block: (A^∅ => B^∅)^∅) => B^∅)^{x})^∅
     *)
    Example borrow := (tabs (tabs (tapp #1 #3))).
    Example TBorrow A B := ({A | ∅} ==> {{{A | ∅} ==> {B | ∅} | ∅} ==> {B | ∅} | ##1}).
    Example t_borrow : forall {Γ φ Σ A B},
      closed_qual 0 (length Γ) (length Σ) φ ->
      closed_ty 0 (length Γ) (length Σ) A ->
      closed_ty 0 (length Γ) (length Σ) B ->
      has_type Γ φ Σ borrow (TBorrow A B) ∅.
      intros. unfold borrow. unfold TBorrow.
      apply t_abs; ccrush.
      apply t_abs; ccrush.
      replace (∅) with (openq $$(S (S (S (length Γ)))) $$(S (length Γ)) ∅) at 15; try solve [opening; ccrush; auto].
      eapply t_app with (T1:=A); ccrush.
      * T_VAR; ccrush.
      * T_VAR; ccrush.
    Qed.

    (* Γ = c1 : Ref[Unit]^{c1} *)
    Context (c1 := 0)
            (Γ := [(TRef TUnit, ∅)])
            (φ := (just_fv c1))
            (Σ : senv).

    (** An OK use of borrow:

            borrow(c1) { c2 => !c2 }
      *)
    Example borrow_ok  := (tapp (tapp borrow $c1) (tabs !(#1))).
    Example borrow_ok_ty : has_type Γ φ Σ borrow_ok TUnit ∅.
      unfold borrow_ok. subst c1. subst Γ. subst φ.
      replace (∅) with (openq $$0 ∅ ∅) at 2; try solve [opening; auto].
      apply t_app with (T1:=({(TRef TUnit) | ∅} ==> {TUnit | ∅})); ccrush; intuition.
      * replace $$0 with (openq ∅ $$0 ##1) at 2; try solve [opening; ccrush; auto].
        apply t_app with (T1:=(TRef TUnit)); ccrush.
        + apply t_borrow; ccrush.
        + T_VAR; ccrush.
      * apply t_abs; ccrush.
        eapply t_deref; ccrush.
        T_VAR; ccrush.
    Qed.

    (** A bad use of borrow:

            borrow(c1) { c2 => !c1 } // error c1 not directly accessible
      *)
    Example borrow_bad := (tapp (tapp borrow $c1) (tabs !($c1))).
    (* first, consider the type of the block : *)
    Example borrow_bad_block_ty : has_type Γ φ Σ (tabs !($c1)) ({TRef TUnit | ∅} ==> {TUnit | ∅}) $$c1.
      subst c1. subst Γ. subst φ.
      apply t_abs; ccrush.
      eapply t_deref.
      T_VAR; ccrush.
    Qed.
    (* now suppose this is typable: *)
    Example borrow_bad_ty : exists S q, has_type Γ φ Σ borrow_bad S q.
      eexists. eexists. unfold borrow_bad.
      (* both the function and argument of the application alias c1... *)
      apply t_app with (T1:={(TRef TUnit) | ∅} ==> {TUnit | ∅}) (df:=$$c1) (d1:=$$c1). (* ... which means the block function expected by borrow(c1) must alias c1 too *)
      2 : eapply borrow_bad_block_ty.
      replace $$c1 with (openq $$c1 $$c1 ##1); try solve [opening; auto].
      eapply t_app with (T1:=TRef TUnit).
      2 : T_VAR; ccrush. cleanup.
      (* However, instantiating borrow's type reveals that the block parameter needs to be separate (i.e. it is empty).*)
      specialize @t_borrow with (A:=(TRef TUnit)) (B:=TUnit) as HBorrow.
      unfold TBorrow in HBorrow. cleanup.
      (* Thus we cannot assign borrow's type (and neither use subsumption, due to the negative occurrence of c1) *)
      Fail eapply HBorrow.
    Abort.

  End Borrowing.

End HigherOrder.

(** Lightweight Reachability Polymorphism (Sec. 3.4) *)
Section LightweightPoly.

  (** Since this version of the calculus lacks numbers and reference assignment, we
      demonstrate reachability polymorphism on an equivalent example:

          def inclike(x) = { !x; x }
   *)
  Example inclike := (tabs (seq !(#1) #1)).
  (** inclike : ((x : Ref[Unit])^∅) => Ref[Unit]^{x })^∅ *)
  Example inclike_ty : forall Γ φ Σ,
      closed_qual 0 (length Γ) (length Σ) φ ->
      has_type Γ φ Σ inclike ({TRef TUnit | ∅} ==> {TRef TUnit | ##1}) ∅.
    intros. unfold inclike.
    apply t_abs; ccrush.
    eapply t_seq with (q1:=∅); ccrush.
    * eapply t_deref.
      T_VAR; ccrush.
    * T_VAR; ccrush.
  Qed.

  (** Γ := a : Ref[Unit]^{a };  b : Ref[Unit]^{b} ; c1 : Ref[Unit]^{a,b,c1} ; c2 : Ref[Unit]^{a,b,c1,c2} *)
  Context (a := 0) (b := 1) (c1 := 2) (c2 := 3)
          (Γ := [(TRef TUnit, ($$a ⊔ $$b ⊔ $$c1)) ;
                 (TRef TUnit, ($$a ⊔ $$b)) ;
                 (TRef TUnit, ∅) ;
                 (TRef TUnit, ∅)] )
          (φ := ($$a ⊔ $$b ⊔ $$c1 ⊔ $$c2)).
  Variable (Σ : senv).

  Lemma saturated_abc1 : saturated Γ Σ ($$a ⊔ $$b ⊔ $$c1).
    replace ($$ (a) ⊔ $$ (b) ⊔ $$ (c1)) with (($$ (a) ⊔ $$ (b)) ⊕ c1).
    eapply saturated_qplus; ccrush. ccrush.
  Qed.
  #[local] Hint Resolve saturated_abc1 : core.

  Lemma saturated_phi : saturated Γ Σ ($$a ⊔ $$b ⊔ $$c1 ⊔ $$c2).
    replace ($$ (a) ⋓ $$ (b) ⋓ $$ (c1) ⋓ $$ (c2)) with (($$ (a) ⋓ $$ (b) ⋓ $$ (c1)) ⊕ c2).
    eapply saturated_qplus; ccrush. ccrush.
  Qed.
  #[local] Hint Resolve saturated_phi : core.

  (** inclike(b) : Ref[Unit]^{b} *)
  Example inc1 : has_type Γ φ Σ (tapp inclike $b) (TRef TUnit) $$b.
    intros. replace $$b with (openq ∅ $$b ##1); try solve [opening; auto].
    eapply t_app; ccrush.
    * apply inclike_ty; crush.
    * T_VAR; ccrush.
  Qed.

  (** inclike(c1) : Ref[Unit]^{a,b,c1} *)
  Example inc2 : has_type Γ φ Σ (tapp inclike $c1) (TRef TUnit) ($$a ⊔ $$b ⊔ $$c1).
    intros. replace ($$a ⊔ $$b ⊔ $$c1) with (openq ∅ (($$a ⊔ $$b) ⊔ $$c1) ##1);
              try solve [opening;crush].
    eapply t_app with (df:=∅); crush.
    * cleanup. apply inclike_ty; crush.
    * T_VAR; ccrush.
  Qed.

  (** inclike(c2) :  Ref[Unit]^{a,b,c1,c2} *)
  Example inc3 : has_type Γ φ Σ (tapp inclike $c2) (TRef TUnit) ($$a ⊔ $$b ⊔ $$c1 ⊔ $$c2).
    intros. replace ($$a ⊔ $$b ⊔ $$c1 ⊔ $$c2)
            with (openq ∅ (($$a ⊔ $$b ⊔ $$c1) ⊔ $$c2) ##1);
              try solve [opening;crush].
    eapply t_app with (df:=∅); ccrush.
    * apply inclike_ty; crush.
    * T_VAR; ccrush.
  Qed.

End LightweightPoly.
