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

Section QPoly.

  (* λx.x *)
  Example idfun := (ttabs (tabs #1)).

  (* ∀X<:⊤^♦. ((x : X^♦) -> X^x)^∅ *)
  Example idfun_ty : has_type [] {♦} [] idfun (∀<:{ {♦} }.{ { #1 | {♦} } ==> { #3 | #!1 } | ∅ }) ∅.
    unfold idfun.
    apply t_tabs; ccrush.
    apply t_abs; ccrush.
    eapply t_var; ccrush.
  Qed.

  (* id(unit): Unit^∅*)
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

  (* id(new Ref(unit)): Ref[Unit]^{♦} *)
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
    * change_qual ({♦} ⊔ ∅).
  Qed.

  (* The fakeid function *)
  Section FakeId.
    (* assume a general allocation primitive *)
    Variable (alloc : tm).
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

End QPoly.


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
  Proof.
    intros. unfold seq.
    change_qual (openq ∅ q2 #!1).
    change_type (open_ty TUnit ∅ T2 q2 T2).
    apply t_app with (T1:=T2); eauto; ccrush.
    * change_qual (openq ∅ q1 ∅).
      change_type (open_ty TUnit ∅ T1 q1 ({T2 | q2} ==> {T2 | #! 1})).
      eapply t_app with (T1:=T1); ccrush.
      - apply t_abs; ccrush.
        apply t_abs; ccrush.
        eapply t_var; ccrush.
  Qed.

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

Section Closures.
  (* Two examples that Scala capture types would conflate *)

  (* { val y = new Ref(unit); { x => y } } *)
  Example escaping_closure := (tlet (tref tunit) (tabs #3)).

  (* escaping_closure : f(Unit => Ref[Unit]^f)^{♦} *)
  Example ret_const : has_type [] {♦} [] escaping_closure ({TUnit | ∅}  ==> {TRef ∅ TUnit | #!0}) {♦}.
  Proof.
    unfold escaping_closure.
    change_qual (openq ∅ ({♦} ⊔ ∅) #!1).
    change_type (({TUnit | ∅} ==> {TRef ∅ TUnit | #! 0}) <~ᵀ TUnit ~ ∅; TRef ∅ TUnit ~ ({♦} ⊔ ∅)).
    eapply t_let_fresh with (q1':={♦}) (df':=∅); try solve [ccrush].
    cleanup. apply t_abs; ccrush.
      (* now use subtyping for the f (= $2) self-ref abstraction *)
      eapply t_sub. eapply t_var; ccrush. 2,3 : ccrush.
      apply stp_refl; ccrush.
      (* x <: x,f <: f by qs_self in this context *)
      eapply qs_trans with (d2:=$!1 ⊔ $!2).
      + (* by ordinary set inclusion *) apply qs_sq; ccrush.
      + (* by qs_self abstraction rule *) eapply qs_self; ccrush.
  Qed.

  (* { () => new Ref() } : Unit^∅ => Ref[Unit]^{♦} *)
  Example ret_fresh : has_type [] ∅ [] (tabs (tref tunit)) ({TUnit | ∅}  ==> {TRef ∅ TUnit | {♦} }) ∅.
  Proof.
    apply t_abs; ccrush.
    change_qual ({♦} ⊔ ∅).
    apply t_ref; ccrush.
    apply t_base; ccrush.
  Qed.

  (* { () => let x = new Ref() in x } : Unit^∅ => Ref[Unit]^{♦} *)
  Example ret_fresh_let : has_type [] ∅ [] (tabs (tlet (tref tunit) #1)) ({TUnit | ∅}  ==> {TRef ∅ TUnit | {♦} }) ∅.
  Proof.
    apply t_abs; ccrush.
    (* prepare dependent application *)
    change_qual (openq ∅ {♦} #!1).
    change_type (open_ty TUnit ∅  (TRef ∅ TUnit) {♦} (TRef ∅ TUnit)).
    apply t_let_fresh with (q1':={♦}) (df':=∅); ccrush.
    * change_qual ({♦} ⊔ ∅).
      apply t_ref; ccrush.
      apply t_base; ccrush.
    * eapply t_var; ccrush.
  Qed.

End Closures.

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
  Context (t_mkThrow : has_type [] {♦} [] mkThrow CanThrow {♦}).

  (** The try combinator, this one allocates a fresh capability and passes it to the given block:
        def try_(block) = let throw = mkThrow; block(throw)
  *)
  Example try_ := (ttabs (tabs (tlet mkThrow (tapp #3 #1)))).

  (** A possible typing for the polymorphic try combinator
          try : (∀A^a<:⊤^♦. ((CanThrow^♦ => A^a)^♦ => A^a)^a)^∅
    *)
  Example try_ty_ :  has_type [] ∅ [] try_ (∀.{ {{CanThrow | {♦} } ==> {#3 | #!3} | {♦} } ==> {#3 | #!3} | #!1 }) ∅.
  Proof.
    intros. unfold try_.
    apply t_tabs; ccrush. (* $1 <- A *)
    apply t_abs; ccrush.  (* $3 <- block *)
    change_qual (openq ($!1 ⊔ $!3)  {♦} $!1).
    change_type (open_ty TUnit ∅ CanThrow {♦} $1).
    eapply t_let_fresh with (q1':={♦}) (df':=$♦1 ⊔ $♦3) ; try solve [ccrush].
    * eapply weaken'. eapply t_mkThrow. all: ccrush.
    * cleanup.
      change_qual (openq $!3 $!5 $!1).
      change_type (open_ty TUnit ∅ CanThrow $!5 $1).
      apply t_app_fresh with (d1':=$♦5) (df':=$♦3); ccrush.
      - eapply t_var; ccrush.
      - eapply t_var; ccrush.
  Qed.

  (* generalize to all contexts*)
  Example try_ty : forall {Γ φ Σ}, closed_qual 0 (‖Γ‖) (‖Σ‖) φ ->
    has_type Γ φ Σ try_ (∀.{ {{CanThrow | {♦} } ==> {#3 | #!3} | {♦} } ==> {#3 | #!3} | #!1 }) ∅.
  Proof.
    intros. eapply weaken'. eapply weaken_store. eapply try_ty_. all : ccrush.
  Qed.

  (* Consider this concrete context *)
  Variable (Σ : senv).
  Context (c1 := 0) (Γ := [bind_tm((false,TRef ∅ TUnit),∅)]) (wfS : wf_senv Σ).
  (** This block
        { throw => !c1 ; throw () }
    demonstrates a legal use of capabilities. *)
  Example nonescaping := (tabs (seq !($c1) (tapp #1 tunit))).

  (** Using the nonescaping block with try is indeed well-typed. *)
  Example nonescaping_ok : has_type Γ $!c1 Σ (tapp (ttapp try_) nonescaping) TUnit ∅.
  Proof.
    unfold nonescaping. subst c1.
    change_qual (openq ∅ $!0 ∅).
    change_type (open_ty TUnit ∅ ({CanThrow | {♦}} ==> {TUnit | ∅}) $!0 TUnit).
    eapply t_app_fresh with (d1':=$!0) (df':=∅); ccrush.
    * change_qual (openq ∅ ∅ #!1).
      change_type (open_ty TUnit ∅ TUnit ∅ ({{CanThrow | {♦}} ==> {#3 | #!3} | {♦}} ==> {#3 | #!3})).
      apply t_tapp_fresh with (d1':=∅) (df':=∅); ccrush. apply (t_sub_bound ⊤ {♦}); ccrush.
      apply try_ty; ccrush.
    * subst Γ. apply t_abs; ccrush.
      apply t_seq with (T1:=TUnit) (q1:=∅); ccrush.
      + apply t_deref with (d:=$!0); ccrush.
        eapply t_var; ccrush.
      + apply t_sub with (T1:=Nothing) (d1:=∅); ccrush.
        subst CanThrow.
        change_qual (∅ <~ᵈ $! 2; ∅).
        change_type (Nothing <~ᵀ TUnit ~ ∅; TUnit ~ ∅).
        eapply t_app with (T1:=TUnit); ccrush.
        - eapply t_var; ccrush.
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
  Example escaping_bad : exists S q, has_type Γ $!c1 Σ (tapp (ttapp try_) escaping) S q.
    eexists. eexists. eapply t_app_fresh with (df:=∅). 4: eapply escaping_ty.
    (* We have a typing mismatch: *)
    (* suppose we can pick those qualifiers so that they don't overlap *)
    dom_equals ({♦}).
    (* try_ requires that the block `escaping` returns a disjoint function, but the type of `escaping` is
       dependent on its capability argument. Hence, we need to be able to instantiate try_ in away that
       the block argument reaches the capability (indicated by #!1) in the type.
       No such parametric instantiation exists, and neither can we use subsumption to get rid of the dependency #!1,
       because it occurs negatively in the type.
       *)
  Abort.

  (* Examples that are rejected by Scala capture types, but legal in our type system *)
  (* fresh1 = try { () => new Ref() } *)
  Example fresh1 := (tapp (ttapp try_) (tabs (tref tunit))).
  (* fresh2 = try { () => { val y = new Ref(unit); { x => y } } }*)
  Example fresh2 := (tapp (ttapp try_) (tabs escaping_closure)).

  (* Return with the freshness marker makes it necessary to have this alternative typing
     explicitly attaching the ♦:
        try : (∀A^a<:⊤^♦. ((CanThrow^♦ => A^♦a)^♦ => A^♦a)^a)^∅
     An instantiation of the previous type with a fresh argument is not possible with the current typing rules.
  *)
  Example try_ty_alt :  has_type [] ∅ [] try_ (∀.{ {{CanThrow | {♦} } ==> {#3 | #♦3} | {♦} } ==> {#3 | #♦3} | #!1 }) ∅.
  Proof.
    intros. unfold try_.
    apply t_tabs; ccrush. (* $1 <- A *)
    apply t_abs; ccrush.  (* $3 <- block *)
    change_qual (openq ($!1 ⊔ $!3)  {♦} $♦1).
    change_type (open_ty TUnit ∅ CanThrow {♦} $1).
    eapply t_let_fresh with (q1':={♦}) (df':=$♦1 ⊔ $♦3) ; try solve [ccrush].
    * eapply weaken'. eapply t_mkThrow. all: ccrush.
    * cleanup.
      change_qual (openq $!3 $!5 $♦1).
      change_type (open_ty TUnit ∅ CanThrow $!5 $1).
      apply t_app_fresh with (d1':=$♦5) (df':=$♦3); ccrush.
      - eapply t_var; ccrush.
      - eapply t_var; ccrush.
  Qed.

  (* fresh1 : Ref[Unit]^{♦} *)
  Example fresh1_ty : has_type [] {♦} [] fresh1 (TRef ∅ TUnit) {♦}.
  Proof.
    unfold fresh1.
    change_qual (openq ∅ ∅ {♦}).
    change_type (open_ty TUnit ∅  ({CanThrow | {♦}} ==> {TRef ∅ TUnit | {♦} }) ∅ (TRef ∅ TUnit)).
    eapply t_app_fresh with (d1':=∅) (df':={♦}); try solve [ccrush].
    * (* try *)
      change_qual (openq ∅ ∅ #!1).
      change_type (open_ty TUnit ∅ (TRef ∅ TUnit) ∅ ({{CanThrow | {♦}} ==> {#3 | #♦3} | {♦}} ==> {#3 | #♦3})).
      apply t_tapp; ccrush.
      apply (t_sub_bound ⊤ {♦}); ccrush. eapply weaken_flt. apply try_ty_alt; ccrush. all: ccrush.
    * (* block *)
      apply t_abs; ccrush.
      change_qual ({♦} ⊔ ∅).
      apply t_ref; ccrush.
      apply t_base; ccrush.
  Qed.

  (* fresh2 : f(Unit => Ref[Unit]^f)^{♦}  *)
  Example fresh2_ty : has_type [] {♦} [] fresh2 ({TUnit | ∅}  ==> {TRef ∅ TUnit | #!0}) {♦}.
    unfold fresh2.
    change_qual (openq ∅ ∅ {♦}).
    change_type (open_ty TUnit ∅  ({CanThrow | {♦}} ==> { ({TUnit | ∅}  ==> {TRef ∅ TUnit | #!0}) | {♦} }) ∅ ({TUnit | ∅} ==> {TRef ∅ TUnit | #! 0})).
    eapply t_app_fresh with (d1':=∅) (df':={♦}); try solve [ccrush].
    * (* try *)
      cleanup.
      change_qual (openq ∅ ∅ #!1).
      change_type (open_ty TUnit ∅ ({TUnit | ∅} ==> {TRef ∅ TUnit | #! 0}) ∅ ({{CanThrow | {♦}} ==> {#3 | #♦3} | {♦}} ==> {#3 | #♦3})).
      apply t_tapp; ccrush.
      apply (t_sub_bound ⊤ {♦}); ccrush. eapply weaken_flt. apply try_ty_alt; ccrush. all: ccrush.
    * (* block *)
      apply t_abs; try solve [ccrush].
      unfold escaping_closure. cleanup.
      (* use the typing from above *)
      eapply weaken'. eapply ret_const. all : ccrush.
  Qed.

End TryCatch.
