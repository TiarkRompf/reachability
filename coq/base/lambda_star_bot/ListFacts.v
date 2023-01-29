(** Assorted facts about lists.

    Author: Brian Aydemir.

    Implicit arguments are declared by default in this library. *)

Set Implicit Arguments.

Require Import Eqdep_dec.
Require Import List.
Require Import SetoidList.
Require Import Sorting.
Require Import Relations.


(* ********************************************************************** *)
(** * List membership *)

Lemma not_in_cons :
  forall (A : Type) (ys : list A) x y,
  x <> y -> ~ In x ys -> ~ In x (y :: ys).
Proof.
  induction ys; simpl; intuition.
Qed.

Lemma not_In_app :
  forall (A : Type) (xs ys : list A) x,
  ~ In x xs -> ~ In x ys -> ~ In x (xs ++ ys).
Proof.
  intros A xs ys x H J K.
  destruct (in_app_or _ _ _ K); auto.
Qed.

Lemma elim_not_In_cons :
  forall (A : Type) (y : A) (ys : list A) (x : A),
  ~ In x (y :: ys) -> x <> y /\ ~ In x ys.
Proof.
  intros. simpl in *. auto.
Qed.

Lemma elim_not_In_app :
  forall (A : Type) (xs ys : list A) (x : A),
  ~ In x (xs ++ ys) -> ~ In x xs /\ ~ In x ys.
Proof.
  split; auto using in_or_app.
Qed.


(* ********************************************************************** *)
(** * List inclusion *)

Lemma incl_nil :
  forall (A : Type) (xs : list A), incl nil xs.
Proof.
  unfold incl.
  intros A xs a H; inversion H.
Qed.

Lemma incl_trans :
  forall (A : Type) (xs ys zs : list A),
  incl xs ys -> incl ys zs -> incl xs zs.
Proof.
  unfold incl; firstorder.
Qed.

Lemma In_incl :
  forall (A : Type) (x : A) (ys zs : list A),
  In x ys -> incl ys zs -> In x zs.
Proof.
  unfold incl; auto.
Qed.

Lemma elim_incl_cons :
  forall (A : Type) (x : A) (xs zs : list A),
  incl (x :: xs) zs -> In x zs /\ incl xs zs.
Proof.
  unfold incl. auto with datatypes.
Qed.

Lemma elim_incl_app :
  forall (A : Type) (xs ys zs : list A),
  incl (xs ++ ys) zs -> incl xs zs /\ incl ys zs.
Proof.
  unfold incl. auto with datatypes.
Qed.


(* ********************************************************************** *)
(** * Setoid facts *)

Lemma InA_iff_In :
  forall (A : Set) x xs, InA (@eq A) x xs <-> In x xs.
Proof.
  split.
  2 : {
    apply In_InA.
    intuition.
  }
  induction xs as [ | y ys IH ].
    intros H. inversion H.
    intros H. inversion H; subst; auto with datatypes.
Qed.


(* ********************************************************************* *)
(** * Equality proofs for lists *)

Section EqRectList.

Variable A : Type.
Variable eq_A_dec : forall (x y : A), {x = y} + {x <> y}.

Lemma eq_rect_eq_list :
  forall (p : list A) (Q : list A -> Type) (x : Q p) (h : p = p),
  eq_rect p Q x p h = x.
Proof with auto.
  intros.
  apply K_dec with (p := h)...
  decide equality. destruct (eq_A_dec a a0)...
Qed.

End EqRectList.


(* ********************************************************************** *)
(** * Decidable sorting and uniqueness of proofs *)

Section DecidableSorting.

Variable A : Set.
Variable leA : relation A.
Hypothesis leA_dec : forall x y, {leA x y} + {~ leA x y}.

Theorem lelistA_dec :
  forall a xs, {lelistA leA a xs} + {~ lelistA leA a xs}.
Proof.
  induction xs as [ | x xs IH ]; auto with datatypes.
  destruct (leA_dec a x); auto with datatypes.
  right. intros J. inversion J. auto.
Qed.

Theorem sort_dec :
  forall xs, {sort leA xs} + {~ sort leA xs}.
Proof.
  induction xs as [ | x xs IH ]; auto with datatypes.
  destruct IH; destruct (lelistA_dec x xs); auto with datatypes.
  right. intros K. inversion K. auto.
  right. intros K. inversion K. auto.
  right. intros K. inversion K. auto.
Qed.

Section UniqueSortingProofs.

  Hypothesis eq_A_dec : forall (x y : A), {x = y} + {x <> y}.
  Hypothesis leA_unique : forall (x y : A) (p q : leA x y), p = q.

  Scheme lelistA_ind' := Induction for lelistA Sort Prop.
  Scheme sort_ind' := Induction for sort Sort Prop.

  Theorem lelistA_unique :
    forall (x : A) (xs : list A) (p q : lelistA leA x xs), p = q.
  Proof with auto.
    induction p using lelistA_ind'; intros q.
    (* case: nil_leA *)
    replace (nil_leA leA x) with (eq_rect _ (fun xs => lelistA leA x xs)
      (nil_leA leA x) _ (refl_equal (@nil A)))...
    generalize (refl_equal (@nil A)).
    pattern (@nil A) at 1 3 4 6, q. case q; [ | intros; discriminate ].
    intros. rewrite eq_rect_eq_list...
    (* case: cons_sort *)
    replace (cons_leA leA x b l r) with (eq_rect _ (fun xs => lelistA leA x xs)
      (cons_leA leA x b l r) _ (refl_equal (b :: l)))...
    generalize (refl_equal (b :: l)).
    pattern (b :: l) at 1 3 4 6, q. case q; [ intros; discriminate | ].
    intros. inversion e; subst.
    rewrite eq_rect_eq_list...
    rewrite (leA_unique r l1)...
  Qed.

  Theorem sort_unique :
    forall (xs : list A) (p q : sort leA xs), p = q.
  Proof with auto.
    induction p using sort_ind'; intros q.
    (* case: nil_sort *)
    replace (nil_sort leA) with (eq_rect _ (fun xs => sort leA xs)
      (nil_sort leA) _ (refl_equal (@nil A)))...
    generalize (refl_equal (@nil A)).
    pattern (@nil A) at 1 3 4 6, q. case q; [ | intros; discriminate ].
    intros. rewrite eq_rect_eq_list...
    (* case: cons_sort *)
    replace (cons_sort p h) with (eq_rect _ (fun xs => sort leA xs)
      (cons_sort p h) _ (refl_equal (a :: l)))...
    generalize (refl_equal (a :: l)).
    pattern (a :: l) at 1 3 4 6, q. case q; [ intros; discriminate | ].
    intros. inversion e; subst.
    rewrite eq_rect_eq_list...
    rewrite (lelistA_unique h h0).
    rewrite (IHp s)...
  Qed.

End UniqueSortingProofs.
End DecidableSorting.


(* ********************************************************************** *)
(** * Equality on sorted lists *)

Section Equality_ext.

Variable A : Type.
Variable ltA : relation A.
Hypothesis ltA_trans : forall x y z, ltA x y -> ltA y z -> ltA x z.
Hypothesis ltA_not_eqA : forall x y, ltA x y -> x <> y.
Hypothesis ltA_eqA : forall x y z, ltA x y -> y = z -> ltA x z.
Hypothesis eqA_ltA : forall x y z, x = y -> ltA y z -> ltA x z.

Hint Resolve ltA_trans : core.
Hint Immediate ltA_eqA eqA_ltA : core.

Notation Inf := (lelistA ltA).
Notation Sort := (sort ltA).

Lemma strictorder_irrel :
  forall a, (complement ltA) a a.
Proof.
  intros.
  unfold complement.
  specialize ltA_not_eqA with (x := a) (y := a).
  unfold not in ltA_not_eqA.
  auto.
Qed.

Instance strictorder_ltA : StrictOrder ltA :=
{
   StrictOrder_Irreflexive := strictorder_irrel;
   StrictOrder_Transitive := ltA_trans
}.

Lemma not_InA_if_Sort_Inf :
  forall xs a, Sort xs -> Inf a xs -> ~ InA (@eq A) a xs.
Proof.
  induction xs as [ | x xs IH ]; intros a Hsort Hinf H.
  inversion H.
  inversion H; subst.
    inversion Hinf; subst.
      assert (x <> x) by auto; intuition.
    inversion Hsort; inversion Hinf; subst.
      assert (Inf a xs).
      1 : {
       apply InfA_ltA with (y := x).
       2 : auto.
       2 : auto.
       intuition.
      }
      assert (~ InA (@eq A) a xs) by auto.
      intuition.
Qed.

Lemma Sort_eq_head :
  forall x xs y ys,
  Sort (x :: xs) ->
  Sort (y :: ys) ->
  (forall a, InA (@eq A) a (x :: xs) <-> InA (@eq A) a (y :: ys)) ->
  x = y.
Proof.
  intros x xs y ys SortXS SortYS H.
  inversion SortXS; inversion SortYS; subst.
  assert (Q3 : InA (@eq A) x (y :: ys)) by firstorder.
  assert (Q4 : InA (@eq A) y (x :: xs)) by firstorder.
  inversion Q3; subst; auto.
  inversion Q4; subst; auto.
  assert (ltA y x).
  1 : {
    apply (SortA_InfA_InA _ _ _ H6 H7).
    auto.
  }
  assert (ltA x y).
  1 : {
   apply (SortA_InfA_InA _ _ _ H2 H3).
   auto.
  }
  assert (y <> y) by eauto.
  intuition.
Qed.

Lemma Sort_InA_eq_ext :
  forall xs ys,
  Sort xs ->
  Sort ys ->
  (forall a, InA (@eq A) a xs <-> InA (@eq A) a ys) ->
  xs = ys.
Proof.
  induction xs as [ | x xs IHxs ]; induction ys as [ | y ys IHys ];
      intros SortXS SortYS H; auto.
  (* xs -> nil, ys -> y :: ys *)
  assert (Q : InA (@eq A) y nil) by firstorder.
  inversion Q.
  (* xs -> x :: xs, ys -> nil *)
  assert (Q : InA (@eq A) x nil) by firstorder.
  inversion Q.
  (* xs -> x :: xs, ys -> y :: ys *)
  inversion SortXS; inversion SortYS; subst.
  assert (x = y) by eauto using Sort_eq_head.
  cut (forall a, InA (@eq A) a xs <-> InA (@eq A) a ys).
  intros. assert (xs = ys) by auto. subst. auto.
  intros a; split; intros L.
    assert (Q2 : InA (@eq A) a (y :: ys)) by firstorder.
      inversion Q2; subst; auto.
      assert (Q5 : ~ InA (@eq A) y xs) by auto using not_InA_if_Sort_Inf.
      intuition.
    assert (Q2 : InA (@eq A) a (x :: xs)) by firstorder.
      inversion Q2; subst; auto.
      assert (Q5 : ~ InA (@eq A) y ys) by auto using not_InA_if_Sort_Inf.
      intuition.
Qed.

End Equality_ext.
