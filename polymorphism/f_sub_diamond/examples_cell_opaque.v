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

(* This file demonstrates the general idea behind opaque typings for Church-encoded data types, which can be used when returning data that
     closes over tracked local resources. We will exemplify the idea on the Cell[A] type with the usual System F encoding ∀C.(A => C) => C.  *)

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
  Definition val (t1 t2 : tm): tm := (tapp (tabs t2) t1).

  (* the typing rule combines the tabs and t_app_fresh cases (we could also have a non-fresh version) *)
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
    has_type (bind_tm(false, T1, (df ⋒ q1)) :: bind_tm(true, {T1 | df ⋒ q1} ==> {T2 | q2}, df):: Γ) (df ⊔ $!(S (length Γ)) ⊔ {♦}) Σ (open_tm' Γ t2) (open_ty' Γ T2) (openq' Γ q2) ->
    has_type Γ φ Σ (val t1 t2) (T2 <~ᵀ TUnit ~ ∅ ; T1 ~ q1) (q2 <~ᵈ df ; q1).
    intros. unfold val. specialize (has_type_closed H3). intuition.
    eapply t_app_fresh with (d1':=q1) (df':=df); ccrush.
    apply t_abs; ccrush. constructor; ccrush. inversion H0; subst. auto.
    unfold_open in H12. simpl in H12.
    eapply @weaken_flt with (φ:=df ⊔ $! (S (length Γ)) ⊔ {♦}); ccrush.
    eapply has_type_filter; eauto.
  Qed.

  Lemma open_val : forall {k t t1 t2}, open_rec_tm k t (val t1 t2) = (val (open_rec_tm k t t1) (open_rec_tm (S (S k)) t t2)).
    intros. unfold val. simpl. auto.
  Qed.

End DerivedSyntax.

Section OpaqueCell.

(*  Below is an _opaque_ cell type containing a datum reaching out-of-scope variables.

    OCell[A] := p∀C^c<:⊤^∅. f(g(y:A^♦ -> C^y)^∅ -> C^f)^p

    If we erase qualifiers, then we obtain the usual F(sub) encoding.

    The intent is to be able to extract the (contextually fresh) datum of type A. As a first simplification, we do not make use
    of the quantified c qualifier, and can thus set its bound to the empty (non-fresh) qualifier.

    Using dependent function types, the extractor g(y:A^♦ -> C^y) specifies that the elimination's qualifier must come from the
    stored datum itself, which to the extractor appears contextually fresh. Furthermore, given such a g function, OCell promises to return
    a C^f, with some abstracted reachability set of the cell's computation f.

    The technique we see at play here is a "self-reference chain" starting from the outer universal type p's self-reference, attached
    to the inner function f, which then occurs in its codomain qualifier. That is to say, f reaches whatever p reaches, and we do not
    need a "deep" occurrence of self-references in types, such as p∀C^c<:⊤^{}. f(g(y:A^♦ -> C^y)^∅ -> C^p) where p deeply occurs in
    f's codomain.

    Let's see this in action:

    cell : (p∀C^c<:⊤^{}. f(g(y:A^♦ -> C^y)^∅ -> C^f)^p)^{cell}  ⊣ cell : OCell[A]^{♦}

    cell[A^∅] : f(g(y:A^♦ -> A^y)^∅ -> A^f)^{cell} // By type application: p ↦ {cell}

    let id: g(y:A^♦ -> A^y)^∅ = x => x // The extractor (identity) can be assigned this type

    cell[A^∅](id) : A^{cell} // By function application: f ↦ {cell}

    That is, we have propagated the name of the cell to the result's qualifier. And that is all we can really know
    about an opaque data type.

    In the remainder of this file, we fully mechanize opaque cells end to end in our calculus.
*)

  (* OCell[A] := p∀C^c<:⊤^{}. f(g(y:A^♦ -> C^y)^∅ -> C^f)^p
     Note: the number attached to the element type parameter indicates by how much it must be incremented if it is a deBruijn index.
    *)
  Example TOCell A2 := (∀<:{ ∅ }.{ { { A2 | {♦} } ==> { #3 | #!1 } | ∅ } ==> { #3 | #!0 } | #!0 }).

  (* Cell introduction: ΛA.λx.ΛC.λf.f(x) *)
  Example cell_mk := (ttabs (tabs (ttabs (tabs (tapp #1 #5))))).
  (* Cell elimination: ΛA.λc.c[A](id) *)
  Example cell_get := (ttabs (tabs (tapp (ttapp #1) (tabs #1)))).

  (* Cell introduction typing
     cell_mk : z[A^a<:⊤^♦] => (g(x: A^a) => (p[C^c<:⊤^{}] => f(h(y:A^♦ => C^y)^∅ => C^f)^p)^x,g)^a *)
  Example t_cell_chained2_abs_ :
    has_type [] ∅ [] cell_mk (∀.{ {#1 | #!1} ==> (*A:#3 x:#1 *) {TOCell #5 | #!0 ⊔ #!1 } | #!1 }) ∅.
    unfold cell_mk.
    apply t_tabs; ccrush. unfold TOCell. ccrush.
    apply t_abs; ccrush.
    (* g abstraction: *)
    (* x,a <: x,g *)
    eapply t_sub with (d1:=$!3 ⊔ $!1).
    2 : {
        eapply stp_refl; try solve [ccrush].
        replace (qset false (union (singleton 2) (singleton 3)) {}N {}N) with ($!3 ⊔ $!2); try solve [ccrush].
        apply qs_cong; try solve [ccrush].
        apply qs_trans with (d2:=$!1 ⊔ $!2).
        apply qs_sq; ccrush. eapply qs_self; ccrush.
    } 2,3 : ccrush.
    apply t_tabs; ccrush.
    (* p abstraction: *)
    (* x,a <: p  *)
    eapply t_sub with (d1:=$!3 ⊔ $!1).
    2: {
        eapply stp_refl; try solve [ccrush].
        apply qs_trans with (d2:=($!3 ⊔ $!1) ⊔ $!4).
        apply qs_sq; ccrush. eapply qs_self_all; ccrush.
    } 2,3 : ccrush.
    apply t_abs; ccrush.
    (* f abstraction: *)
    (* x <: x,a <: f*)
    apply t_sub with (T1:=$5) (d1:=$!3).
    2: {
        apply stp_refl; try solve [ccrush].
        apply qs_trans with (d2:=($!3 ⊔ $!1) ⊔ $!6).
        apply qs_sq; ccrush. eapply qs_self; ccrush.
    } 2-3: ccrush.
    change_qual (openq $!7 $!3 #!1).
    change_type (open_ty TUnit ∅ $1 $!3 $5).
    apply t_app_fresh with (df':=$!7) (d1':=$♦3 ⊔ $♦1); try solve [ccrush].
    * dom_equals ({♦}). cleanup.
      eapply t_var; ccrush. simpl. repeat f_equal; try fnsetdec. apply NatSet.eq_if_Equal.
      split; try fnsetdec. rewrite empty_union_right. intros.
      apply NatSetFacts.inter_iff in H. intuition.
      apply union_1 in H1. intuition. all: apply NatSetProperties.FM.singleton_iff in H0, H; subst; discriminate.
    * eapply t_var; ccrush.
    * constructor; auto. unfold tenv_saturated. intros.
        apply qmem_lub_or_commute in H. intuition.
        simpl in H0; apply NatSetFacts.singleton_iff in H0; subst.
        econstructor; ccrush. simpl in H0; apply NatSetFacts.singleton_iff in H0; subst.
        eapply sat_tvar. ccrush. all : ccrush.
  Qed.

  (* generalize to all contexts *)
  Example t_cell_chained2_abs : forall {Γ φ Σ}, closed_qual 0 (‖Γ‖) (‖Σ‖) φ ->
    has_type Γ φ Σ cell_mk (∀.{ {#1 | #!1} ==> (*A:#3 x:#1 *) {TOCell #5 | #!0 ⊔ #!1 } | #!1 }) ∅.
    intros. eapply weaken'. eapply weaken_store. apply t_cell_chained2_abs_. all : auto.
  Qed.

  (* The identity is a compatible extractor
     id : (y:A^♦ => A^y)^∅ *)
  Example id_elim2 : forall Γ φ Σ A,
    closed_qual 0 (‖ Γ ‖) (‖ Σ ‖) φ -> closed_ty 0 (‖ Γ ‖) (‖ Σ ‖) A ->
    has_type Γ φ Σ (tabs #1) ({ A | {♦} } ==> {A | #!1 }) ∅.
    intros.
    apply t_abs; ccrush.
    eapply t_var; ccrush.
  Qed.

  (* Cell elimination typing
     cell_get: (f[A^a <: ⊤^♦] => (OCell[A]^{a} => A^a)^a)^∅ *)
  Example t_cell_get_abs_ :
    has_type [] ∅ [] cell_get (∀.{ {TOCell #3 | #!1 } ==> { #3 | #!3 } | #!1 }) ∅.
    unfold cell_get.
    apply t_tabs; ccrush. unfold TOCell. ccrush.
    apply t_abs; ccrush.
    change_qual (openq $!1 ∅ (#!0)).
    change_type (open_ty TUnit ∅ ({$ 1 | {♦}} ==> {$1 | #!1}) ∅ $1).
    apply t_app; ccrush.
    * change_qual (openq $!1 ∅ (#!0)).
      change_type (open_ty TUnit ∅ $1 ∅ ({{$ 1 | {♦}} ==> {# 3 | #! 1} | ∅} ==> {# 3 | #!0 })).
      apply t_tapp; ccrush. (* it's sufficient to instantiate with precise, non-fresh bound *)
      eapply t_sub. eapply t_var; ccrush. apply s_all; ccrush.
      eapply qs_qvar; ccrush. apply stp_refl; ccrush. apply qs_sq; ccrush.
      all : ccrush.
    * apply id_elim2; ccrush.
  Qed.

  (* generalize to all contexts *)
  Example t_cell_get_abs : forall {Γ φ Σ}, closed_qual 0 (‖Γ‖) (‖Σ‖) φ ->
    has_type Γ φ Σ cell_get (∀.{ {TOCell #3 | #!1 } ==> { #3 | #!3 } | #!1 }) ∅.
    intros. eapply weaken'. eapply weaken_store. apply t_cell_get_abs_. all : auto.
  Qed.

End OpaqueCell.

Section OpaqueCellUse.

  (* A concrete usage example *)

  Context (Σ := [(TUnit, ∅); ({ TUnit | ∅} ==> {TUnit | ∅}, ∅)])
          (φ := ({♦} ⊔ &!0 ⊔ &!1)).

  (* cell_get[_](cell_mk[_](&1)) *)
  Example get_mk_cell := (tapp (ttapp cell_get) (tapp (ttapp cell_mk) &1)).

  Lemma sat_loc_1: saturated [] Σ &!1.
    unfold Σ. constructor; eauto.
    unfold senv_saturated. intros. simpl in H; apply NatSetFacts.singleton_iff in H; subst.
    apply sat_loc with (U:=TUnit) (q':=∅); ccrush.
    Unshelve. auto.
  Qed.

  (* Type instantiation of the extractor used in this example *)
  Example t_cell_get_abs_inst: has_type [] φ Σ (ttapp cell_get) ({TOCell (TRef ∅ TUnit) | &!1 } ==> { (TRef ∅ TUnit) | &!1 }) &!1.
    change_qual (openq ∅ &!1 #!1).
    change_type (open_ty TUnit ∅ (TRef ∅ TUnit) &!1 ({TOCell #3 | #!1 } ==> { #3 | #!3 })).
    apply t_tapp_fresh with (d1':=&!1) (df':=∅) ; try solve [unfold TOCell; ccrush].
    eapply t_sub. eapply t_cell_get_abs; ccrush.
    apply s_all. 1-4 : unfold TOCell; ccrush.
    cleanup. apply stp_refl; ccrush. apply qs_sq; ccrush.
    all : ccrush. all: eauto using sat_loc_1.
  Qed.

  (* Type instantiaion of the introduction used in this example *)
  Example t_cell_mk_abs_inst: has_type [] φ Σ (ttapp cell_mk) ({(TRef ∅ TUnit) | &!1 } ==> {TOCell (TRef ∅ TUnit) | #!0 ⊔ #!1 }) &!1.
    change_qual (openq ∅ &!1 #!1).
    change_type (open_ty TUnit ∅ (TRef ∅ TUnit) &!1 ({#1 | #!1} ==> {TOCell #5 | #!0 ⊔ #!1 })).
    apply t_tapp_fresh with (d1':=&!1) (df':=∅) ; try solve [unfold TOCell; ccrush].
    eapply t_sub. eapply t_cell_chained2_abs; ccrush.
    apply s_all. 1-4 : unfold TOCell; ccrush.
    cleanup. apply stp_refl; ccrush. apply qs_sq; ccrush.
    all : ccrush. all: eauto using sat_loc_1.
  Qed.

  (* Typing the example *)
  Example t_get_mk_cell_abs : has_type [] φ Σ get_mk_cell (TRef ∅ TUnit) &!1.
    unfold get_mk_cell.
    change_qual (openq &!1 &!1 &!1).
    change_type (open_ty TUnit ∅ (TOCell (TRef ∅ TUnit)) &!1 (TRef ∅ TUnit)).
    apply t_app; ccrush. 3 : eauto using sat_loc_1.
    * apply t_cell_get_abs_inst.
    * change_qual (openq &!1 &!1 (#!0 ⊔ #!1)).
      change_type (open_ty TUnit ∅ (TRef ∅ TUnit) &!1 (TOCell (TRef ∅ TUnit))).
      apply t_app; try solve [ccrush].
      - apply t_cell_mk_abs_inst.
      - change_qual (∅ ⊔ &!1). apply t_loc; ccrush.
  Qed.

End OpaqueCellUse.

Section OpaqueCellEndToEnd.

  (* Another example, mirroring the "counter" (Fig. 1 in the paper), just on a single cell *)

  (* Thunk type *)
  Example TThunk := ({TUnit | ∅ } ==> {TUnit | ∅}).

  (* A closure analogous to the counter:

    def cell_closure() =
      let x = new Ref()
      cell_mk(() => x:=!x)
  *)
  Example cell_closure := (tabs (val (tref tunit)
                                     (tapp (ttapp cell_mk) (tabs (tassign #3 (tderef #3)))))).

  (* Usage:

     let cell = cell_closure() // : OCell[TThunk]^{cell}
        cell_get(cell)         // : TThunk^{cell} within the let body, and TThunk^{♦} for the entire expression
  *)
  Example cell_closure_use := (val (tapp cell_closure tunit) (tapp (ttapp cell_get) #1)).

  (* cell_closure : Unit => OCell[Thunk]^{♦} *)
  Example t_cell_closure : has_type [] ∅ [] cell_closure ({TUnit | ∅ } ==> { (TOCell TThunk) | {♦} }) ∅.
    unfold cell_closure. unfold TOCell.
    apply t_abs; try solve [ccrush]. unfold TThunk; ccrush.
    unfold_open. repeat rewrite open_val. cleanup. fold cell_mk. fold TThunk.
    change_qual (openq ∅ {♦} #!1).
    change_type ((∀<:{⊤ | ∅ }.{ {{ TThunk | {♦}} ==> {# 3 | #!1 } | ∅} ==> {# 3 | #!0 } | #!0}) <~ᵀ TUnit ~ ∅; (TRef ∅ TUnit) ~ {♦}).
    apply t_val_fresh; ccrush. unfold TThunk. ccrush.
    * change_qual (∅ ⊔ {♦}). apply t_ref; ccrush. apply t_base; ccrush.
    * fold cell_mk. fold TThunk.
      change_qual (openq $!3 $!3 (#!0 ⊔ #!1)).
      change_type ((∀<:{⊤ | ∅}.{ {{TThunk | {♦}} ==> {# 3 | #! 1} | ∅} ==> {# 3 | #! 0} | #! 0}) <~ᵀ TUnit ~ ∅; TThunk ~  $! 3).
      apply t_app; try solve [ccrush].
      + change_qual (openq ∅ $!3 #!1).
        change_type (({#1 | #!1} ==> {∀<:{⊤ | ∅}.{ {{#5 | {♦}} ==> {# 3 | #! 1} | ∅} ==> {# 3 | #! 0} | #! 0} | #! 0 ⊔ #! 1}) <~ᵀ TUnit ~ ∅; TThunk ~ $! 3).
        eapply t_tapp_fresh with (d1':=$♦3) (df':=∅); ccrush. 2: unfold TThunk; ccrush.
        eapply t_sub. 3,4: ccrush.
        ** eapply t_cell_chained2_abs; ccrush.
        ** unfold TOCell. cleanup. eapply s_all. 1-4 : unfold TOCell; unfold TThunk; ccrush. cleanup.
           apply stp_refl; ccrush. apply qs_sq; ccrush.
      + apply t_abs; ccrush.
        eapply t_assign.
        ** eapply t_var; ccrush.
        ** eapply t_deref. eapply t_var; ccrush. all: ccrush.
        ** auto.
  Qed.

  (* cell_closure_use : TThunk^{♦} *)
  Example t_cell_closure_use : has_type [] {♦} [] cell_closure_use TThunk {♦}.
    unfold cell_closure_use.
    change_qual (openq ∅ {♦} #!1).
    change_type (open_ty TUnit ∅ (TOCell TThunk) {♦} TThunk).
    apply t_val_fresh; try solve [ccrush]. 1 : unfold TOCell; unfold TThunk; ccrush.
    * change_qual (openq ∅ ∅ {♦}).
      dep_app (∅) (∅).
      apply t_app; try solve [ccrush].
      cleanup. eapply weaken_flt. apply t_cell_closure. all: ccrush.
    * cleanup. fold cell_get. fold TThunk.
      change_qual (openq $!1 $!1 $!1).
      change_type (open_ty TUnit ∅ (TOCell TThunk) $!1 TThunk).
      apply t_app; ccrush.
      + change_qual (openq ∅ $!1 #!1).
        change_type (open_ty TUnit ∅ TThunk $!1 ({TOCell #3 | #!1 } ==> {#3 | #!3})).
        apply t_tapp_fresh with (d1':=$♦1) (df':=∅); ccrush. 2: unfold TThunk; ccrush.
        eapply t_sub. 3,4: ccrush.
        ** eapply t_cell_get_abs; ccrush.
        ** unfold TOCell. cleanup. apply s_all. 1-4: unfold TThunk; ccrush. cleanup.
           apply stp_refl; ccrush. apply qs_sq; ccrush.
      + eapply t_var; ccrush. unfold TOCell. unfold TThunk. ccrush.
  Qed.

End OpaqueCellEndToEnd.
