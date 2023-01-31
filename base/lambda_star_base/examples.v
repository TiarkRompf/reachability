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

Import QualNotations.
Local Open Scope qualifiers.

(* ### Examples ### *)

Notation " { a | b } ==> { c | d }"  := (TFun b d a c)
(at level 10, format "'[' '[hv' '{' a  '/' '|'  b '}' ']' '/  '  '==>'  '[hv' '{' c  '/' '|'  d '}' ']' ']'").

Section Warmup.

  (* identity fun *)
  Example idfun      := (tabs #0).

  (* example context with three bindings a b c (0 1 2) *)
  Context (Γ012 := [(TUnit,∅); (TUnit,∅); (TUnit,∅)]).
  (* example context filter, including 0 1 2. *)
  Context (φ012 := ($$0 ⊔ $$1 ⊔ $$2)).

  (** Γ012|Σ |-ᵠ⁰¹² λx. x : ( x:T1^{} -> T1^{x} )^{} *)
  Example idfun_typing : forall T1 Σ,
      closed_ty 0 3 (length Σ) T1 ->
      has_type Γ012 φ012 Σ idfun ({T1 | ∅} ==> {T1 | ##0}) ∅.
    intros. unfold φ012. unfold Γ012. unfold idfun. compute.
    apply t_abs; ccrush.
    T_VAR; ccrush.
  Qed.

  (** Γ|Σ ⊢ᵠ⁰¹² λx.x : ((a : A^{}) -> A^a)^d1 *)
  Example idfun_ht : forall Γ φ Σ d1 A ,
      closed_qual 0 (length Γ) (length Σ) φ ->
      closed_qual 0 (length Γ) (length Σ) d1 ->
      closed_ty 0 (length Γ) (length Σ) A ->
      d1 ⊑ φ ->
      has_type Γ φ Σ idfun ({A | ∅} ==> {A | ##0}) d1.
    intros. unfold idfun. compute.
    apply t_abs; ccrush.
    T_VAR; ccrush.
  Qed.

  (** Γ012|Σ ⊢ᵠ⁰¹² λx.x : ((x : A^a,b) -> A^a,b+x)^∅ cannot be typed this way.  *)
  Example idfun_nt :
    let q := $$0 ⊔ $$1 in
      forall Σ A, has_type Γ012 φ012 Σ idfun ({A | q} ==> {A | q ⊔ ##0}) ∅.
    intros. subst q. unfold idfun.
    (* First, the domain qualifier is non-empty, so t_abs fails. *)
    Fail apply t_abs.
    (* Suppose we could use subsumption *)
    eapply t_sub. eapply t_abs.
    7 : { (* Due to contravariance, qualifiers in function domains are flipped ... *)
          apply s_fun.
          (* ... leading to an obligation of the form: *)
          4 : { (* However, this version of λ* has the following property :*)
                About stp_subqual.
                (* i.e., the subtype's qualifier is included in the supertype's qualifier.
                   Ergo, we would have that {0,1} ⊑ ∅, which is impossible! *)
                admit. }  all : admit. }
  Abort.

  (** Church encodings *)
  Section Church.
    (* Church true, respectively pi1: λa.λb.a *)
    Example church_true := (tabs (tabs #1)).
    (* Type scheme for pi1 := (a:A^{}) -> ((b:B^{}) -> A^{a})^{a}. Note: less general than in version allowing overlap of arguments. *)
    Example church_true_T A B := {A | ∅} ==> {{B | ∅} ==> {A | ##1} | ##0}.
    (* Church false, respectively pi2: λa.λb.b  *)
    Example church_false := (tabs (tabs #0)).
    (* Type scheme for pi2 := (a:A^{}) -> ((b:B^{}) -> B^{b})^{}. Note: less general than in version allowing overlap of arguments. *)
    Example church_false_T A B := {A | ∅} ==> {{B | ∅} ==> {B | ##0} | ∅}.

    (* Church pairs *)
    Example pair := (tabs (tabs (tabs (tapp (tapp #0 #2) #1)))).

    (* Pair[A,B]^q_X := ((a : A^{}) -> ((b : B^{}) -> X^q)^q⊔{a})^{} -> X^q *)
    Example TPair A B X q := {{A | ∅} ==> {{B | ∅} ==> {X | q} | q ⊔ ##0} | ∅} ==> {X | q}.

    (* Pair destructors *)
    Example fst := (tabs (tapp #0 church_true)).
    Example snd := (tabs (tapp #0 church_false)).

    Variables (Γ : tenv) (φ : qual) (Σ : senv) (A B : ty).
    Context (phiwf : closed_qual 0 (length Γ) (length Σ) φ)
            (Awf   : closed_ty 0 (length Γ) (length Σ) A)
            (Bwf   : closed_ty 0 (length Γ) (length Σ) B).

    (** Γ|Σ ⊢ᵠ λa.λb.a : ((a:A^{}) -> ((b:B^{}) -> A^{a})^{a})^{} *)
    Example church_true_ht : has_type Γ φ Σ church_true (church_true_T A B) ∅.
      unfold church_true. unfold church_true_T.
      apply t_abs; ccrush.
      apply t_abs; ccrush.
      T_VAR; ccrush.
    Qed.

    (** Γ|Σ ⊢ᵠ λa.λb.b : ((a:A^{}) -> ((b:B^{}) -> B^{b})^{})^{} *)
    Example church_false_ht : has_type Γ φ Σ church_false (church_false_T A B) ∅.
      unfold church_false. unfold church_false_T.
      apply t_abs; ccrush.
      apply t_abs; ccrush.
      T_VAR; ccrush.
    Qed.

    (* Γ|Σ ⊢ᵠ pair : ( (a : A^{}) -> ((b : B^{}) -> (Pair[A,B]^q_X)^q⊔{a,b})^q⊔{a} )^q *)
    Example t_pair : forall {X q},
      closed_ty 0 (length Γ) (length Σ) X ->
      closed_qual 0 (length Γ) (length Σ) q ->
      q ⊑ φ ->
      has_type Γ φ Σ pair ({A | ∅} ==> {{B | ∅} ==> {TPair A B X q | (q ⊔ ##0 ⊔ ##1) } | q ⊔ ##0}) q.
      intros. unfold pair. unfold TPair.
      apply t_abs; ccrush.
      apply t_abs; ccrush.
      apply t_abs; ccrush.
      replace q with (openq $$(S (length Γ)) q) at 4; try solve [opening].
      apply t_app with (T1:=B) (df:=q⊔$$(length Γ)); ccrush.
      * replace (q ⊔ $$ (length Γ))
        with (openq $$(length Γ) (q ⊔ ##0)) at 1; try solve [opening; auto].
        apply t_app with (T1:=A) (df:=$$(S (S (length Γ)))); ccrush.
        + T_VAR; ccrush.
        + T_VAR; ccrush.
      * T_VAR; ccrush.
      * qual_destruct. closed_qual_invert. ccrush. bound_simpl. lia.
    Qed.

    (** The problem with these Church encodings is that they cannot be applied to any arguments, due to the
        t_app rule forbidding general dependency on the argument in a function's codomain. We can assign them
        types that make them usable, once we introduce function self-qualifiers which are lacking in this
        version of λ* (cf. discussion on escaping closures further below). *)
    Variable (a : tm).
    Context (a_ht : has_type Γ φ Σ a A ∅).
    Example church_true_use_bad : exists S q, has_type Γ φ Σ (tapp church_true a) S q.
      eexists. eexists. eapply t_app. eapply church_true_ht. eapply a_ht.
      (* This condition states that the codomain of church_true should not be dependent on the argument (zero bound variables).
         However, there is a dangling bound variable in the codomain's qualifier, and we cannot proceed. *)
      admit.
    Abort.

  End Church.

End Warmup.

(** Derived Syntax *)
(** Sequential composition *)
Definition seq (t1 t2 : tm): tm := (tapp (tapp (tabs (tabs #0)) t1) t2).

Lemma t_seq : forall Γ φ Σ t1 T1 q1 t2 T2 q2,
    has_type Γ φ Σ t1 T1 q1 ->
    has_type Γ φ Σ t2 T2 q2 ->
    has_type Γ φ Σ (seq t1 t2) T2 q2.
  intros. unfold seq.
  replace q2 with (openq q2 ##0);
    try solve [opening; auto].
  eapply t_app with (T1:=T2) (df:=(openq q1 ∅)); eauto; crush.
  eapply t_app with (df:=∅); eauto; crush.
  apply church_false_ht; ccrush.
  all : qual_destruct; ccrush; intuition.
Qed.

(** val/let bindings  *)
Definition val (t1 t2 : tm): tm := (tapp (tabs t2) t1).

Lemma t_val : forall Γ φ df Σ t1 T1 q1 t2 T2 q2,
    closed_tm 1 (length Γ) (length Σ) t2 ->
    closed_ty 0 (length Γ) (length Σ) T2 ->
    closed_qual 1 (length Γ) (length Σ) q2 ->
    has_type Γ φ Σ t1 T1 q1 ->
    df ⊑ φ ->
    df ⋒ q1 = ∅ -> (* this version requires strict separation of the bound expression and the body *)
    has_type ((T1, ∅) :: Γ) (df ⊔ (just_fv (length Γ))) Σ (open_tm' Γ t2) (open_ty' Γ T2) (openq' Γ q2) ->
    has_type Γ φ Σ (val t1 t2) T2 (openq q1 q2).
  intros. unfold val. specialize (has_type_closed H2). intuition.
  eapply t_app; eauto; crush.
  apply t_abs; ccrush.
  apply has_type_filter in H5. unfold openq' in *. eapply unopen_subqual; eauto.
  eapply subqual_trans; eauto. apply subqual_qlub. auto.
Qed.

Lemma open_val : forall {k t t1 t2}, open_rec_tm k t (val t1 t2) = (val (open_rec_tm k t t1) (open_rec_tm (S k) t t2)).
  intros. unfold val. simpl. auto.
Qed.

(** Functional Abstraction (Sec. 2.2) *)
Section FunAbs.
  Variables (Σ : senv) (φ  : qual).

  Section IntroEx.
    Variables (q  : qual).
    Context (qwf : closed_qual 0 0 (length Σ) q)
            (phiwf: closed_qual 0 1 (length Σ) φ)
            (qwfphi : q ⊑ φ)
            (c := 0)
            (cvisible : $c ∈ᵥ φ).

    (** val c = ...                   // : Ref[Int] ^ q+c
        def deref(x : Unit) = { ! c } // : (Unit => Unit) ^ q+c   *)
    Example deref := (tabs (! $0)).
    Example deref_ty : has_type [(TRef TUnit, q)] φ Σ deref ({TUnit | ∅} ==> {TUnit | ∅}) (q ⊕ c).
      unfold deref. subst c.
      apply t_abs; ccrush.
      apply t_deref with (d:=q ⊕ 0).
      apply t_var; crush.
    Qed.

    (** deref(unit) // : Unit *)
    Example deref_app : has_type [(TRef TUnit, q)] φ Σ (tapp deref tunit) TUnit ∅.
      replace (∅) with (openq ∅ ∅); try solve [opening; auto].
      eapply t_app with (df:=(q ⊔ $$c)); crush.
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
      Example addRef := (tabs (seq (! $c1) (! #0))).
      Example addRef_ty : has_type Γ12 φ Σ addRef ({TRef TUnit | ∅} ==> {TUnit | ∅}) $$c1.
        unfold addRef.
        apply t_abs; ccrush.
        eapply t_seq with (T1:=TUnit) (q1:=∅); crush.
        * apply t_deref with (d:=$$c1); crush.
          T_VAR; crush.
        * apply t_deref with (d:=$$2); crush.
          T_VAR; crush.
      Qed.

      (**
          The application addRef(c2) is legal, since c1 and c2 are different and hence do not overlap.
      *)
      Example addRef_app_ok : has_type Γ12 φ Σ (tapp addRef $c2) TUnit ∅.
        replace (∅) with (openq $$c2 ∅); try solve [opening; auto].
        apply t_app with (T1:=(TRef TUnit)) (df:=$$c1); ccrush.
        * apply addRef_ty.
        * T_VAR; crush.
      Qed.

      (* With the addRef_ty type assignment above, it is impossible to type the application addRef(c1), as expected. *)
      Example addRef_app_bad : exists S q, has_type Γ12 φ Σ (tapp addRef $c1) S q.
        eexists. eexists. eapply t_app. eapply addRef_ty. eapply t_var; crush.
        (* Application enforces strict separation between a function and its argument, but both addRef and $c1 contain
           $c1 in their rechability qualifiers: *)
        4 : { simpl. set_simpl. f_equal. (* we end up needing to show {c1} = ∅ *) admit. }
        Abort.

      (* The paper shows the following alternative typing for addRef that would permit overlapping with $c1, and thus
         permit addRef_app_bad. However, this judgment is not derivable in this version.  *)
      Example addRef_alt_ty : has_type Γ12 φ Σ addRef (TFun (just_fv c1) ∅ (TRef TUnit) TUnit) $$c1.
        unfold addRef.
        (* In this version of λ*, function implementations cannot observe anything about their argument,
           i.e., the domain's qualifier is always empty  (cf. t_abs in lambda_star.v) *)
        Fail apply t_abs.
        (* Using subsumption is also futile: *)
        eapply t_sub.
        (* i.e. we need a function type {?T1 | ?d10} ==> {?T2 | ?d2} which is a subtype of {TRef TUnit | $$ (c1)} ==> {TUnit | ∅}. *)
        2 : { econstructor.
          (* however, contravariance in the domain requires that the singleton set {c1} is included in the subtype's domain ?d10: *)
           4: {  admit. } (* this is impossible, because ?d10 must be the empty qualifier, according to t_abs. *)
           all : admit. }
       Abort.

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
    Example returnArg : has_type Γ0 φ Σ (tabs (seq !(#0) #0)) ({TRef TUnit | ∅} ==> {TRef TUnit | ##0}) ∅.
      apply t_abs; ccrush.
      apply t_seq with (T1:=TUnit) (q1:=∅); ccrush.
      * apply t_deref with (d:=$$1).
        T_VAR; ccrush.
      * T_VAR; ccrush.
    Qed.

    (** Lacking the ⊥ qualifier for base types, this version of λ* cannot type the general reference allocation (tref t) for t of arbitrary type.
        Otherwise, reduction steps of the form (tref t) -> (tref t') could violate type preservation, i.e.,
        it is not clear if the argument is a non-reference type without adding further mechanisms (such as the ⊥ qualifier).
        Therefore, we adopt a limited reference allocation that enforces the type of reference is exactly Ref[Unit], then we can type the example:

           def returnFresh(x) = { val y = new Ref(x); !y; y } // : Unit => Ref[Unit]^∅
     *)
    Example returnFresh : has_type Γ0 φ Σ (tabs (val (tref #0) (seq !(#0) #0))) ({TUnit | ∅} ==> {TRef TUnit | ∅}) ∅.
      apply t_abs; ccrush.
      replace (∅) with (openq ∅ ##0); try solve [opening;ccrush].
      eapply t_val; ccrush.
      * eapply t_ref; ccrush.
        T_VAR; ccrush.
      * apply t_seq with (T1:=TUnit) (q1:=∅); ccrush.
      - apply t_deref with (d:=$$2).
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
    replace (∅) with (openq ∅ ∅); try solve [opening;crush].
    eapply t_val with (df:=∅); ccrush.
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
  Example closure_deref_external : has_type Γ φ Σ (val (tref tunit) (tabs !(#1))) ({TUnit | ∅} ==> {TUnit | ∅}) ∅.
    replace (∅) with (openq ∅ ##0); try solve [opening;crush].
    eapply t_val with (df:=∅); ccrush.
    apply t_ref with (d:=∅). apply t_base. crush.
    apply t_abs; ccrush.
    apply t_deref with ($$(length Γ)); ccrush.
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
  Example closure_escape := (val (tref tunit) (tabs #1)).
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

      where the closure always returns a fresh reference. The solution is introducing function self-qualifiers, which
      are missing in this version of λ*.
  *)

End Escaping.

(** Key Higher-Order Programming Patterns (Sec. 2.4) *)
Section HigherOrder.

  (** Non-Interference (Sec. 2.4.2) *)
  Section NonInterference.
    (** For simplicity, we define par as a sequential execution of two thunks. *)
    Example par := (tabs (tabs (seq (tapp #1 tunit) (tapp #0 tunit)))).
    (** par inhabits the type shown in the paper, i.e.,

        par : ((a : (Unit => Unit)^{}) => ((b : (Unit => Unit)^{}) => Unit)^{a})^{}
     *)
    Example t_par : forall {Γ Σ φ}, closed_qual 0 (length Γ) (length Σ) φ ->
      has_type Γ φ Σ par ({{TUnit | ∅} ==> {TUnit | ∅} | ∅} ==> {{{TUnit | ∅} ==> {TUnit | ∅} | ∅} ==> {TUnit | ∅} | ##0}) ∅.
      intros. unfold par. apply t_abs; ccrush. apply t_abs; ccrush. eapply t_seq with (T1:=TUnit) (q1:=∅); ccrush.
      * replace (∅) with (openq ∅ ∅); try solve [opening;crush].
        eapply t_app with (df:=$$(length Γ)); ccrush; intuition.
        - T_VAR; ccrush.
        - apply t_base; ccrush.
      * replace (∅) with (openq ∅ ∅); try solve [opening;crush].
        eapply t_app with (df:=$$(S (length Γ))); ccrush; intuition.
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
                                      (tapp (tapp par (tabs !(#2))) (tabs !(#1))))).

    Example noninterfering_ty : has_type Γ φ Σ noninterfering TUnit ∅.
      unfold noninterfering. replace (∅) with (openq ∅ ∅); try solve [opening;crush].
      eapply t_val with (T1:=TRef TUnit) (df:=∅); crush.
      apply t_ref with (d:=∅). apply t_base. crush.
      unfold open_tm'. repeat rewrite open_val. replace (openq' Γ ∅) with (openq ∅ ∅); try solve [opening; crush].
      eapply t_val with (df:=$$(length Γ)) (T1:=TRef TUnit); ccrush.
      * eapply t_ref; ccrush. apply t_base; ccrush.
      * replace (∅) with (openq $$(S (length Γ)) ∅) at 3; try solve [opening;crush].
          eapply t_app with (T1:=({TUnit | ∅} ==> {TUnit | ∅})) (df:=$$(length Γ)); ccrush.
          + replace ($$(length Γ)) with (openq $$(length Γ) ##0); try solve [opening;crush].
            eapply t_app with (df:=∅); ccrush.
            ** fold (seq (tapp #1 tunit) (tapp #0 tunit)). fold par. eapply t_par; ccrush.
            ** apply t_abs; ccrush. eapply t_deref with (d:=$$(length Γ)); T_VAR; ccrush.
          + apply t_abs; ccrush. eapply t_deref with (d:=$$(S (length Γ))); T_VAR; ccrush.
        Unshelve. all : apply 0.
    Qed.

    (**
        Bad use of par:
        val c1 = new Ref(unit); val c2 = new Ref(unit); par { !c1; !c2 } { !c1; !c2 }
    *)
    Example interfering := (val (tref tunit)
                               (val (tref tunit)
                                   (tapp (tapp par (tabs (seq !(#2) !(#1)))) (tabs (seq !(#2) !(#1)))))).

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
      (* from t_par we know 1) df = ∅ and 2) d20 = ##0, and
         3) openq ($$ (0) ⊔ $$ (1)) ?d20 ⋒ ($$ (0) ⊔ $$ (1)) = ∅.

         However, 2), and 3) together are unsatisfiable:
      *)
      assert (((openq ($$ (0) ⊔ $$ (1)) ##0) ⋒ ($$ (0) ⊔ $$ (1))) = ($$ (0) ⊔ $$ (1))). {
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
    Example try_ := (tabs (val mkThrow (tapp #1 #0))).

    (** The type of the try combinator, encoding polymorphism as metalevel quantification.

            try : forall A. ((CanThrow^∅ => A^∅)^∅ => A^∅)^∅
       *)
    Example try_ty : forall A Γ φ Σ,
        closed_qual 0 (length Γ) (length Σ) φ ->
        closed_ty 0 (length Γ) (length Σ) A ->
        has_type Γ φ Σ try_ ({{CanThrow | ∅} ==> {A | ∅} | ∅} ==> {A | ∅}) ∅.
      intros. unfold try_. specialize (t_mkThrow _ _ _ H) as H'.
      apply t_abs; ccrush. replace (∅) with (openq ∅ ∅) at 4; try solve [opening].
      eapply t_val with (df:=$$(length Γ)); ccrush.
      * apply t_mkThrow; ccrush.
      * replace (∅) with (openq $$(S (length Γ)) ∅) at 5; try solve [opening].
        eapply t_app with (T1:=CanThrow) (df:=$$(length Γ)); ccrush.
        - T_VAR; ccrush.
        - T_VAR; ccrush.
    Qed.

    Variable (Σ : senv).
    Context (c1 := 0) (Γ := [(TRef TUnit,∅)]).
    (** This block

           { throw => !c1 ; throw () }

       demonstrates a legal use of capabilities. *)
    Example nonescaping := (tabs (seq !($c1) (tapp #0 tunit))).

    (** Using the nonescaping block with try is indeed well-typed. *)
    Example nonescaping_ok : has_type Γ $$c1 Σ (tapp try_ nonescaping) TUnit ∅.
      unfold nonescaping. subst c1.
      replace (∅) with (openq $$0 ∅); try solve [opening; auto].
      assert (Hf : closed_qual 0 (length Γ) (length Σ) $$0); crush. apply t_mkThrow in Hf.
      eapply t_app with (df:=∅); ccrush.
      * eapply try_ty; crush.
      * subst Γ. apply t_abs; ccrush.
        apply t_seq with (T1:=TUnit) (q1:=∅); ccrush.
        + apply t_deref with (d:=$$0); ccrush.
          T_VAR; ccrush.
        + replace (∅) with (openq ∅ ∅) at 3; try solve [opening; auto].
          eapply t_app with (T1:=TUnit) (df:=$$1); ccrush.
          - apply t_sub with (T1:=CanThrow) (d1:=$$1); ccrush.
            ** subst CanThrow. T_VAR; ccrush.
            ** subst CanThrow. repeat (constructor; ccrush).
          - apply t_base; ccrush.
    Qed.

    (** In constrast, this block

            { throw => !c1 ; { () => throw () } }

       returns a closure over the capability, which is rejected by try. *)
    Example escaping := (tabs (seq !($c1) (tabs (tapp #1 tunit)))).
    (** First, the type of escaping indeed leaks the capability:

            escaping : ((c: CanThrow^{}) => (Unit => Unit)^{c})^{c1}
      *)
    Example escaping_ty : has_type Γ $$c1 Σ escaping ({CanThrow | ∅} ==> {{TUnit | ∅} ==> {TUnit | ∅} | ##0}) $$c1.
      unfold escaping. subst c1. subst Γ.
      apply t_abs; ccrush.
      apply t_seq with (T1:=TUnit) (q1:=∅); ccrush.
      * apply t_deref with (d:=$$0); ccrush.
        T_VAR; ccrush.
      * apply t_abs; ccrush. replace (∅) with (openq ∅ ∅) at 4; try solve [opening; auto].
        eapply t_app with (T1:=TUnit) (df:=$$1); ccrush.
        + apply t_sub with (T1:=CanThrow) (d1:=$$1); ccrush.
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

    Example withoutIO := (tabs (tabs (tapp #0 tunit))).
    (** The type of the withoutIO combinator, encoding polymorphism as metalevel quantification.

            withoutIO : forall A. ((cap: CanIO^∅) => ((block : (Unit => A^∅)^∅) => A^∅))^{cap})^∅
      *)
    Example t_withoutIO : forall A Γ φ Σ,
        closed_qual 0 (length Γ) (length Σ) φ ->
        closed_ty 0 (length Γ) (length Σ) A ->
        has_type Γ φ Σ withoutIO ({CanIO | ∅} ==> {{{TUnit | ∅} ==> {A | ∅} | ∅} ==> {A | ∅}| ##0}) ∅.
      intros. unfold withoutIO.
      apply t_abs; ccrush.
      apply t_abs; ccrush.
      replace (∅) with (openq ∅ ∅) at 5; try solve [opening; auto].
      apply t_app with (T1:=TUnit) (df:=$$(S (length Γ))); ccrush.
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
      replace (∅) with (openq $$1 ∅) at 3; try solve [opening; auto].
      apply t_app with (T1:=({TUnit | ∅} ==> {TUnit | ∅})) (df:=$$0); ccrush.
      * replace ($$0) with (openq $$0 ##0); try solve [opening; auto].
        apply t_app with (T1:=CanIO) (df:=∅); ccrush.
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
      * replace (∅) with (openq $$0 ∅) at 4; try solve [opening; auto].
        eapply t_app with (df:=∅); ccrush.
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
         1) df = ∅, 2) d20 = ##0, and 3) openq (∅ ⊕ canIO) ?d20 ⋒ ($$ (0) ⋓ $$ (1)) = ∅
         However, these constraints are unsatisfiable, i.e., the overlap is not disjoint
      *)
      assert (openq  (∅ ⊕ canIO) ##0 ⋒ ($$ (0) ⊔ $$ (1)) = $$canIO). {
        subst canIO. opening. ccrush. unfold just_fv. f_equal. fnsetdec.
      }
    Abort.

  End NonAccess.

  (** Borrowing (Sec. 2.4.5) *)
  Section Borrowing.
    (**
        borrow[A,B] : ((x : A^∅) => ((block: (A^∅ => B^∅)^∅) => B^∅)^{x})^∅
     *)
    Example borrow := (tabs (tabs (tapp #0 #1))).
    Example TBorrow A B := ({A | ∅} ==> {{{A | ∅} ==> {B | ∅} | ∅} ==> {B | ∅} | ##0}).
    Example t_borrow : forall {Γ φ Σ A B},
      closed_qual 0 (length Γ) (length Σ) φ ->
      closed_ty 0 (length Γ) (length Σ) A ->
      closed_ty 0 (length Γ) (length Σ) B ->
      has_type Γ φ Σ borrow (TBorrow A B) ∅.
      intros. unfold borrow. unfold TBorrow.
      apply t_abs; ccrush.
      apply t_abs; ccrush.
      replace (∅) with (openq $$(length Γ) ∅) at 5; try solve [opening; ccrush; auto].
      eapply t_app with (T1:=A) (df:=$$(S (length Γ))); ccrush.
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
    Example borrow_ok  := (tapp (tapp borrow $c1) (tabs !(#0))).
    Example borrow_ok_ty : has_type Γ φ Σ borrow_ok TUnit ∅.
      unfold borrow_ok. subst c1. subst Γ. subst φ.
      replace (∅) with (openq ∅ ∅) at 2; try solve [opening; auto].
      apply t_app with (T1:=({(TRef TUnit) | ∅} ==> {TUnit | ∅})) (df:=$$0); ccrush; intuition.
      * replace $$0 with (openq $$0 ##0) at 2; try solve [opening; ccrush; auto].
        apply t_app with (T1:=(TRef TUnit)) (df:=∅); ccrush.
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
    (* now suppose this is typable: *)
    Example borrow_bad_ty : exists S q, has_type Γ φ Σ borrow_bad S q.
      eexists. eexists. specialize borrow_bad_block_ty as Hblk. unfold borrow_bad. subst c1. subst Γ. subst φ.
      apply t_app with (T1:={ TRef TUnit | ∅ } ==>  { TUnit | ∅}) (df:=$$0); ccrush; intuition.
      2 : { admit. (* from borrow_bad_block_ty above, we know that at least c1 ∈ ?d1 must hold*) }
      3 : { admit. (* however, this requirement states that ?d1 = ∅, i.e., the constraints are unsatisfiable. *) }
    Abort.

  End Borrowing.

End HigherOrder.

(** Lightweight Reachability Polymorphism (Sec. 3.4) *)
Section LightweightPoly.

  (** Since this version of the calculus lacks numbers, we
      demonstrate reachability polymorphism on an equivalent example:

          def inclike(x) = { x := !x; x }
   *)
  Example inclike := (tabs (seq (tassign (#0) !(#0)) #0)).
  (** inclike : ((x : Ref[Unit])^∅) => Ref[Unit]^{x})^∅ *)
  Example inclike_ty : forall Γ φ Σ,
      closed_qual 0 (length Γ) (length Σ) φ ->
      has_type Γ φ Σ inclike ({TRef TUnit | ∅} ==> {TRef TUnit | ##0}) ∅.
    intros. unfold inclike.
    apply t_abs; ccrush.
    eapply t_seq with (q1:=∅); ccrush.
    * eapply t_assign. T_VAR; ccrush. eapply t_deref.
      T_VAR; ccrush.
    * T_VAR; ccrush.
  Qed.

  (** Γ := a : Ref[Unit]^{a} ; b : Ref[Unit]^{b} ; c1 : Ref[Unit]^{a,b,c1} ; c2 : Ref[Unit]^{a,b,c1,c2} *)
  Context (a := 0) (b := 1) (c1 := 2) (c2 := 3)
          (Γ := [(TRef TUnit, ($$a ⊔ $$b ⊔ $$c1)) ;
                 (TRef TUnit, ($$a ⊔ $$b)) ;
                 (TRef TUnit, ∅) ;
                 (TRef TUnit, ∅)] )
          (φ := ($$a ⊔ $$b ⊔ $$c1 ⊔ $$c2)).
  Variable (Σ : senv).

  (** inclike(b) : Ref[Unit]^{b} *)
  Example inc1 : has_type Γ φ Σ (tapp inclike $b) (TRef TUnit) $$b.
    replace $$b with (openq $$b ##0); try solve [opening; auto].
    eapply t_app with (df:=∅); ccrush.
    * apply inclike_ty; crush.
    * T_VAR; ccrush.
  Qed.

  (** inclike(c1) : Ref[Unit]^{a,b,c1} *)
  Example inc2 : has_type Γ φ Σ (tapp inclike $c1) (TRef TUnit) ($$a ⊔ $$b ⊔ $$c1).
    replace ($$a ⊔ $$b ⊔ $$c1) with (openq (($$a ⊔ $$b) ⊔ $$c1) ##0);
            try solve [opening;crush].
    eapply t_app with (df:=∅); ccrush.
    * apply inclike_ty; crush.
    * T_VAR; ccrush.
  Qed.

  (** inclike(c2) :  Ref[Unit]^{a,b,c1,c2} *)
  Example inc3 : has_type Γ φ Σ (tapp inclike $c2) (TRef TUnit) ($$a ⊔ $$b ⊔ $$c1 ⊔ $$c2).
    replace ($$a ⊔ $$b ⊔ $$c1 ⊔ $$c2) with (openq (($$a ⊔ $$b ⊔ $$c1) ⊔ $$c2) ##0);
            try solve [opening;crush].
    eapply t_app with (df:=∅); ccrush.
    * apply inclike_ty; crush.
    * T_VAR; ccrush.
  Qed.

End LightweightPoly.