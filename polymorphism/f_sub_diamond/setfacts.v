Require Export Arith.EqNat.
Require Export Arith.Le.
Require Import Coq.Program.Equality.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import Psatz.
Require Import Coq.Arith.Compare_dec.
Import ListNotations.

Require Import Coq.Logic.ProofIrrelevance.

Require Import vars.
Require Import env.
Require Import tactics.
Require Import NatSets.

Import NatSet.F.

(** Some axioms connecting the internals of FSet with the standard library.
    These are obviously true. *)
Axiom nat_E_lt : forall {x y}, E.lt x y <-> x < y.
Axiom not_E_lt_nat_ge : forall {x y}, ~ E.lt x y <-> x >= y.
Axiom natset_eqb : forall {x n}, NatSetFacts.eqb n x = (x =? n).

Lemma Equal_if_eq : forall {s s'}, s = s' -> s [=] s'.
  intros. subst. apply NatSetProperties.equal_refl.
Qed.

(** Give an upper bound on the number of set elements.
    Used by locally nameless encoding for sets of variable names to determine
    well-scopedness. *)
Definition bound (N : nats) : nat :=
  match max_elt N with
  | Some n => S n
  | None => 0
  end.

(** Increase the elements of a set by one (apply succ elementwise). *)
Definition incfun (i : elt) (X : nats) := union X (singleton (S i)).
#[global] Hint Unfold incfun : core.
Definition inc (N : nats) : nats := fold incfun N empty.

(** Decrease the elements of a set (apply pred elementwise). *)
Definition decfun (i : elt) (X : nats) : nats := union X (singleton (pred i)).
#[global] Hint Unfold decfun : core.
Definition dec (N : nats) : nats := fold decfun N empty.

Definition ge_fun (n i : elt) := n <=? i.
#[global] Hint Unfold ge_fun : core.
Definition lt_fun (n i : elt) := i <? n.
#[global] Hint Unfold lt_fun : core.

(** Splicing a set (of variables), i.e., increment all elements above
    and including the splice point n. Used in weakening lemmas. *)
Definition splice_set (n : nat) (s : nats) : nats :=
  union (inc (filter (ge_fun n) s)) (filter (lt_fun n) s).

(** Opposite of splicing a set (of variables), i.e., decrement all elements
    above and including the unsplice point n, which is an
    effect of substituting a free variable. *)
Definition unsplice_set (n : nat) (s : nats) : nats :=
  union (dec (filter (ge_fun n) s)) (filter (lt_fun n) s).
Require Import Coq.Bool.Bool.

(** The set {0,..,n-1} *)
Fixpoint nset (n : nat) : nats :=
  match n with
  | O   => {}N
  | S n => add n (nset n)
  end.

(** Domain of an environment in the locally nameless encoding, i.e., the set
    {0,...,|env| - 1} *)
Definition dom {A} (env : list A) := nset (length env).
#[global] Hint Unfold dom : core.

(* properties *)

Lemma add_non_empty : forall {s x}, ~ Empty (add s x).
Proof.
  intros. intro F.
  assert (In s (add s x)). fnsetdec.
  apply NatSetProperties.empty_is_empty_1 in F.
  apply NatSet.eq_if_Equal in F.
  rewrite F in H. specialize (@NatSetNotin.notin_empty s) as F'. contradiction.
Qed.

Lemma max_elt_empty' : forall {s}, max_elt s = None -> s = {}N.
Proof.
  intros. apply max_elt_3 in H. fnsetdec.
Qed.

Lemma max_elt_empty : max_elt {}N = None.
Proof.
  intros. destruct (max_elt {}N) eqn:H; auto.
  apply max_elt_1 in H.
  pose (@NatSetNotin.notin_empty e). contradiction.
Qed.

Lemma subset_bound : forall {s1 s2 b}, Subset s1 s2 -> bound s2 <= b -> bound s1 <= b.
Proof.
  intros. unfold bound in *.
  destruct (max_elt s2) eqn:HS2.
  destruct (max_elt s1) eqn:HS1. 2: lia.
  specialize (@max_elt_1 _ _ HS2).
  specialize (@max_elt_1 _ _ HS1).
  intros. specialize (@H _ H1) as H'.
  specialize (@max_elt_2 _ _ _ HS2 H'). intros.
  assert (e >= e0). apply not_E_lt_nat_ge in H3. auto. lia.
  destruct (max_elt s1) eqn:HS1. 2: lia.
  unfold Subset in H. apply max_elt_empty' in HS2. subst.
  apply max_elt_1 in HS1. apply H in HS1. fnsetdec.
Qed.

Lemma subset_bound' : forall {s1 s2}, Subset s1 s2 -> bound s1 <= bound s2.
Proof.
  intros.
  specialize (@subset_bound s1 s2 (bound s2) H) as Hb.
  apply Hb. auto.
Qed.

Lemma set_eq_bound : forall {s1 s2 b}, Equal s1 s2 -> bound s1 <= b -> bound s2 <= b.
Proof.
  intros. apply NatSet.eq_if_Equal in H. subst. auto.
Qed.

Lemma max_elt_singleton : forall {x}, max_elt (singleton x) = Some x.
Proof.
  intros.
  specialize (@NatSetNotin.in_singleton x) as H.
  destruct (max_elt (singleton x)) eqn:H'.
  apply max_elt_1 in H'. apply NatSetFacts.singleton_iff in H'. subst. auto.
  apply max_elt_3 in H'.
  specialize (@NatSetProperties.singleton_cardinal x) as HC1.
  specialize (@NatSetProperties.cardinal_1 _ H') as HC2.
  lia.
Qed.

Lemma bound_singleton : forall {x}, bound (singleton x) = S x.
Proof.
  intros. unfold bound. rewrite max_elt_singleton. reflexivity.
Qed.

Lemma bound_singleton_iff : forall {x n}, bound (singleton x) <= n <-> S x <= n.
  intros. unfold bound. rewrite max_elt_singleton. lia.
Qed.

Lemma bound_0_empty : forall {s}, bound s <= 0 -> s = {}N.
Proof.
  intros. unfold bound in H.
  destruct (max_elt s) eqn: Hmax. inversion H.
  apply max_elt_empty' in Hmax. apply Hmax.
Qed.

Lemma bound_empty : bound {}N = 0.
Proof.
  unfold bound. rewrite max_elt_empty. reflexivity.
Qed.

Lemma max_gt_bound_not_in : forall {b n e s},
    b <= n -> S e <= b ->
    max_elt s = Some e ->
    ~ In n s.
Proof.
  intros. assert (e < n) by lia. intros Hin.
  specialize (@max_elt_2 s e n H1 Hin) as Hnotin.
  apply not_E_lt_nat_ge in Hnotin. lia.
Qed.

Lemma bound_gt_not_in : forall {b n s},
    b <= n -> bound s <= b -> ~ NatSet.F.In n s.
Proof.
  intros. unfold bound in H0.
  destruct (NatSet.F.max_elt s) eqn: Hmax.
  eapply max_gt_bound_not_in; eauto.
  apply max_elt_empty' in Hmax. subst. intro F. fnsetdec.
Qed.

Lemma empty_union_left : forall {s}, union {}N s = s.
Proof. intros. fnsetdec. Qed.

Lemma empty_union_right : forall {s}, union s {}N = s.
Proof. intros. fnsetdec. Qed.

Lemma max_elt_add_empty : forall {x}, max_elt (add x {}N) = Some x.
  intros. specialize (NatSetProperties.singleton_equal_add x).
  intros. apply NatSet.eq_if_Equal in H. rewrite <- H. apply max_elt_singleton.
Qed.

Lemma max_elt_non_empty : forall {s}, is_empty s = false -> max_elt s <> None.
  intros. intuition. apply max_elt_3 in H0. apply is_empty_1 in H0.
  rewrite H in H0. discriminate.
Qed.

Lemma max_elt_non_empty' : forall {s}, is_empty s = false -> exists n, max_elt s = Some n.
  intros. apply max_elt_non_empty in H. destruct (max_elt s). exists e. auto.
  contradiction.
Qed.

Lemma in_non_empty : forall {s x}, In x s -> ~ Empty s.
  intros. intuition. apply NatSetProperties.empty_is_empty_1 in H0.
  setoid_rewrite H0 in H. rewrite NatSetFacts.empty_iff in H. auto.
Qed.

Lemma non_empty_iff : forall {s}, ~ Empty s <-> is_empty s = false.
  intros. split; intros. rewrite NatSetFacts.is_empty_iff in H.
  destruct (is_empty s); intuition. intuition.
  rewrite NatSetFacts.is_empty_iff in H0. rewrite H in H0. discriminate.
Qed.

Lemma max_elt_iff : forall {s m}, max_elt s = Some m <-> (In m s /\ forall {m'}, In m' s -> m' <= m).
  intros. split; intros.
  - split. apply max_elt_1. auto.
    intros. specialize (max_elt_2 H H0) as Hin. rewrite not_E_lt_nat_ge in Hin. auto.
  - intuition. specialize (in_non_empty H0) as Hne. rewrite non_empty_iff in Hne.
    apply max_elt_non_empty' in Hne. destruct Hne.
    assert (x <= m). apply max_elt_1 in H. apply H1 in H. auto.
    assert (m <= x). specialize (max_elt_2 H H0) as Hl. rewrite not_E_lt_nat_ge in Hl. auto.
    assert (x = m). lia. subst. auto.
Qed.

Lemma max_elt_add_some : forall {s1 m1}, max_elt s1 = Some m1 -> forall {m2}, max_elt (add m2 s1) = Some (max m2 m1).
  intros. rewrite max_elt_iff. intuition.
  * apply Nat.max_case.
    - apply add_1. apply E.eq_refl.
    - apply add_2. apply max_elt_1. auto.
  * bdestruct (m' =? m2).
    - subst. lia.
    - specialize (NatSetProperties.Dec.FSetDecideTestCases.test_add_In _ _ _ H0 H1) as Hin.
      specialize (max_elt_2 H Hin) as Hmax. rewrite nat_E_lt in Hmax. lia.
Qed.

Lemma max_elt_union : forall {s1 s2 m1 m2}, max_elt s1 = Some m1 -> max_elt s2 = Some m2 -> max_elt (union s1 s2) = Some (max m1 m2).
  induction s1 using NatSetProperties.set_induction; intros.
  - apply NatSetProperties.empty_is_empty_1 in H.
    apply NatSet.eq_if_Equal in H. subst. rewrite max_elt_empty in H0.
    inversion H0.
  - rewrite NatSetProperties.Add_Equal in H0. apply NatSet.eq_if_Equal in H0. subst.
    assert ((union (add x s1_1) s2) = (add x (union s1_1 s2))). fnsetdec.
    rewrite H0. destruct (is_empty s1_1) eqn:Hempty.
    * apply is_empty_2 in Hempty. apply NatSetProperties.empty_is_empty_1 in Hempty.
      apply NatSet.eq_if_Equal in Hempty. subst. rewrite max_elt_add_empty in H1.
      inversion H1. subst. assert (Heq : (union {}N s2) = s2). fnsetdec.
      repeat rewrite Heq in *. erewrite max_elt_add_some; eauto.
    * apply max_elt_non_empty' in Hempty. destruct Hempty as [k Hmax].
      erewrite max_elt_add_some; eauto. erewrite max_elt_add_some in H1; eauto.
      inversion H1. f_equal. lia.
Qed.

Lemma union_bound_max' : forall {s1 s2},
    bound (union s1 s2) = Nat.max (bound s1) (bound s2).
  intros. unfold bound.
  destruct (max_elt s1) as [ m1 |] eqn:max1; destruct (max_elt s2) as [ m2 |] eqn:max2; simpl.
  erewrite max_elt_union; eauto.
  all: try apply max_elt_empty' in max1; try apply max_elt_empty' in max2; subst;
    try rewrite empty_union_left; try rewrite empty_union_right.
  rewrite max1. auto. rewrite max2. auto. rewrite max_elt_empty. auto.
Qed.

Lemma union_bound_max : forall {s1 s2},
    bound (union s1 s2) <= Nat.max (bound s1) (bound s2).
Proof.
  intros. rewrite union_bound_max'. lia.
Qed.

Lemma inter_empty_left : forall {s}, inter {}N s = {}N.
intros. fnsetdec. Qed.

Lemma inter_empty_right : forall {s}, inter s {}N = {}N.
intros. fnsetdec. Qed.

Lemma max_elt_inter_singleton : forall {m1 s2 n}, max_elt (inter (singleton m1) s2) = Some n -> n = m1 /\ In m1 s2.
  intros. specialize (max_elt_1 H) as H'.
  specialize (inter_1 H') as H''.  apply inter_2 in H'.
  rewrite NatSetFacts.singleton_iff in H''. subst. intuition.
Qed.

Lemma max_elt_inter_In : forall {s1 s2 n}, max_elt (inter s1 s2) = Some n ->
                                             In n s1 /\ In n s2.
  intros. specialize (max_elt_1 H) as H'. fnsetdec.
Qed.

Lemma max_elt_inter : forall {s1 s2 m1 m2}, max_elt s1 = Some m1 -> max_elt s2 = Some m2 -> forall n, max_elt (inter s1 s2) = Some n -> n <= min m1 m2.
  induction s1 using NatSetProperties.set_induction.
  - intros. apply NatSetProperties.empty_is_empty_1 in H.
    apply NatSet.eq_if_Equal in H. subst. rewrite max_elt_empty in H0. discriminate.
  - intros. destruct (is_empty s1_1) eqn:Hempty.
    * apply is_empty_2 in Hempty. apply NatSetProperties.empty_is_empty_1 in Hempty.
      rewrite NatSetProperties.Add_Equal in H0. setoid_rewrite Hempty in H0.
      setoid_rewrite <- NatSetProperties.singleton_equal_add in H0. apply NatSet.eq_if_Equal in H0.
      subst. rewrite max_elt_singleton in H1. inversion H1. subst.
      apply max_elt_inter_singleton in H3. intuition. specialize (max_elt_2 H2 H4) as H'.
      subst. rewrite not_E_lt_nat_ge in H'. lia.
    * rewrite NatSetProperties.Add_Equal in H0. apply NatSet.eq_if_Equal in H0. subst.
      apply max_elt_non_empty' in Hempty. destruct Hempty as [k Hmax].
      pose (H1':=H1). erewrite max_elt_add_some in H1'; eauto. inversion H1'. subst.
      clear H1'. apply max_elt_inter_In in H3. intuition.
      specialize (max_elt_2 H1 H0) as H'. specialize (max_elt_2 H2 H4) as H''.
      rewrite not_E_lt_nat_ge in H'. rewrite not_E_lt_nat_ge in H''. lia.
Qed.

Lemma inter_bound_min : forall {s1 s2}, bound (inter s1 s2) <= Init.Nat.min (bound s1) (bound s2).
  intros. unfold bound.
  destruct (max_elt (inter s1 s2)) as [m12 |] eqn:max12; try lia.
  destruct (max_elt s1) as [ m1 |] eqn:max1; destruct (max_elt s2) as [ m2 |] eqn:max2; simpl.
  apply le_n_S. eapply max_elt_inter; eauto.
  all: apply max_elt_inter_In in max12; destruct max12 as [X0 X1];
    try apply max_elt_empty' in max1; try apply max_elt_empty' in max2; subst; fnsetdec.
Qed.

Lemma bound_max_not_in : forall {s e},
    max_elt s = Some e ->
    forall {x : E.t}, E.lt e x -> ~ In x s.
Proof.
  intros. intros F. specialize (max_elt_2 H F). intros. contradiction.
Qed.

Lemma remove_nonexist_bound : forall {e1 e2 : nat} {b s},
    e1 < b ->
    max_elt s = Some e1 ->
    max_elt (remove b s) = Some e2 ->
    e2 < b.
Proof.
  intros. specialize (@bound_max_not_in _ _ H0) as H2.
  assert (H' := H). apply nat_E_lt in H. specialize (@H2 _ H).
  specialize (@NatSetProperties.remove_equal _ _ H2) as H3.
  apply NatSet.eq_if_Equal in H3. rewrite H3 in H1.
  rewrite H0 in H1. inversion H1. subst. auto.
Qed.

Lemma remove_max_bound : forall {s b e},
    max_elt s = Some b ->
    max_elt (remove b s) = Some e ->
    e < b.
Proof.
  intros. assert (H0' := H0). apply max_elt_1  in H0'.
  bdestruct (e <? b); auto.
  bdestruct (e =? b).
  - subst. assert (~ (In b (remove b s))). fnsetdec. contradiction.
  - assert (e > b) by lia. assert (In e s).
    eapply NatSetFacts.remove_neq_iff. assert (b <> e) by lia. apply H4.
    apply H0'. specialize (@max_elt_2 _ _ _ H H4) as Hlt.
    apply not_E_lt_nat_ge in Hlt. lia.
Qed.

Lemma remove_preserves_bound : forall {s b x},
    bound s <= b ->
    bound (remove x s) <= b.
Proof.
  intros. unfold bound in *.
  destruct (max_elt s) eqn:Hs.
  - assert (e < b) by lia.
    destruct (max_elt (remove x s)) eqn:Hm.
    + bdestruct (e <? e0); try lia.
      assert (Hs' := Hs). apply max_elt_1 in Hs'.
      assert (Hm' := Hm). apply max_elt_1 in Hm'.
      bdestruct (x =? e0).
      * subst. assert (~ (In e0 (remove e0 s))). fnsetdec. contradiction.
      * assert (In e0 s). eapply NatSetFacts.remove_neq_iff; eauto.
        specialize (@max_elt_2 _ _ _ Hs H3) as Hlt.
        apply not_E_lt_nat_ge in Hlt. lia.
    + lia.
  - apply max_elt_empty' in Hs. subst.
    assert (remove x {}N = {}N) by fnsetdec. rewrite H0.
    rewrite max_elt_empty. lia.
Qed.

Lemma union_remove_preserves_bound : forall {s1 s2 b1 b2 b3 x},
    bound s1 <= b1 ->
    bound s2 <= b2 ->
    b1 <= b3 -> b2 <= b3 ->
    bound (union (remove x s1) s2) <= b3.
  intros. rewrite union_bound_max'. apply @remove_preserves_bound with (x:=x) in H.
  lia.
Qed.

Lemma remove_max_bound' : forall {s e b},
    max_elt s = Some e ->
    mem b s = true ->
    e <= b ->
    bound (remove b s) <= b.
Proof.
  intros.
  apply mem_2 in H0.
  assert (H' := H). apply max_elt_1 in H'.
  specialize (@max_elt_2 _ _ _ H H0) as Hge.
  apply not_E_lt_nat_ge in Hge. assert (e = b) by lia.
  subst. clear Hge H' H1. unfold bound.
  destruct (max_elt (remove b s)) eqn:Hmax.
  - specialize (@remove_max_bound _ _ _ H Hmax) as Hlt. lia.
  - lia.
Qed.

Lemma max_elt_none_mem : forall {x s},
    max_elt s = None ->
    mem x s = true ->
    False.
Proof.
  intros. apply max_elt_empty' in H. subst. rewrite NatSetFacts.empty_b in H0. inversion H0.
Qed.

Lemma bound_increase : forall {f x s},
    f <= x -> bound s <= f ->
    bound (union s (singleton x)) <= S x.
  intros. rewrite union_bound_max'. rewrite bound_singleton. lia.
Qed.

Require Import Coq.Classes.Morphisms.

Lemma elt_fun_compat : forall {f : elt -> bool}, SetoidList.compat_bool Logic.eq f.
  intros. unfold SetoidList.compat_bool. solve_proper.
Qed.
#[global] Hint Resolve elt_fun_compat : core.

Lemma filter_empty : forall {f}, filter f {}N = {}N.
  intros. specialize (NatSetDecide.FSetDecideAuxiliary.D.choose (filter f {}N)) as H.
  destruct H. destruct s. apply filter_1 in i; auto. apply NatSetNotin.notin_empty in i. contradiction.
  apply NatSet.eq_if_Equal. apply NatSetProperties.empty_is_empty_1. auto.
Qed.

Lemma filter_subset : forall {s f}, filter f s [<=] s.
  intros. unfold Subset. intros x H.
  rewrite NatSetFacts.filter_iff in H; intuition.
Qed.

Lemma filter_lt : forall {e s f},
    e < f ->
    max_elt s = Some e ->
    (filter (fun i : elt => i <? f) s) = s.
  intros. apply NatSet.eq_if_Equal. split. apply filter_subset.
  intros. rewrite NatSetFacts.filter_iff; intuition.
  rewrite Nat.ltb_lt. specialize (max_elt_2 H0 H1) as Hlt.
  rewrite not_E_lt_nat_ge in Hlt. lia.
Qed.

Lemma filter_gt : forall {e s f},
    e < f ->
    max_elt s = Some e ->
    (filter (fun i : elt => f <=? i) s) = {}N.
  intros. apply NatSet.eq_if_Equal. split. intros.
  rewrite NatSetFacts.filter_iff in H1; auto. intuition. rewrite Nat.leb_le in H3.
  specialize (max_elt_2 H0 H2) as Hlt. rewrite not_E_lt_nat_ge in Hlt. lia.
  apply NatSetProperties.subset_empty.
Qed.

Lemma filter_union_dist : forall {s1 s2 f},
    filter f (union s1 s2) = union (filter f s1) (filter f s2).
  intros. apply NatSet.eq_if_Equal. split. intros.
  - rewrite NatSetFacts.filter_iff in H; intuition.
    rewrite NatSetFacts.union_iff in H0. intuition.
  - intros. rewrite NatSetFacts.union_iff in H.
    destruct H as [H | H]; rewrite NatSetFacts.filter_iff in H; auto;
    rewrite NatSetFacts.filter_iff; intuition.
Qed.

Lemma filter_inter_dist : forall {s1 s2 f}, filter f (inter s1 s2) = inter (filter f s1) (filter f s2).
  intros. apply NatSet.eq_if_Equal. split; intros.
  - rewrite NatSetFacts.filter_iff in H; intuition.
    rewrite NatSetFacts.inter_iff in H0. intuition.
  - intros. rewrite NatSetFacts.inter_iff in H. intuition.
    rewrite NatSetFacts.filter_iff in H0; auto.
    rewrite NatSetFacts.filter_iff in H1; auto.
    rewrite NatSetFacts.filter_iff; auto. intuition.
Qed.

(* those two are required by certain lemmas about fold on nats *)
Lemma incfun_compat_op : SetoidList.compat_op Logic.eq Equal incfun.
  unfold SetoidList.compat_op. unfold Proper. unfold respectful.
  intros. subst. apply NatSet.eq_if_Equal in H0. subst. intuition.
Qed.
#[global] Hint Resolve incfun_compat_op : core.

Lemma incfun_transpose : SetoidList.transpose Equal incfun.
  unfold SetoidList.transpose. intros. unfold incfun.
  fnsetdec.
Qed.
#[global] Hint Resolve incfun_transpose : core.

Lemma incfun_fold_add': forall {i s x}, ~ In x s -> (fold incfun (add x s) i) [=] (incfun x (fold incfun s i)).
  intros. apply NatSetProperties.fold_add; auto. apply NatSetFacts.Equal_ST.
Qed.

Lemma incfun_fold_add: forall {i s x}, ~ In x s -> (fold incfun (add x s) i) = (incfun x (fold incfun s i)).
  intros. apply NatSet.eq_if_Equal. apply incfun_fold_add'; auto.
Qed.

Lemma incfun_add_fold': forall {i s x}, In x s -> (fold incfun (add x s) i) [=] (fold incfun s i).
  intros. setoid_rewrite NatSetProperties.add_fold; auto. intuition. apply NatSetFacts.Equal_ST.
Qed.

Lemma incfun_add_fold: forall {i s x}, In x s -> (fold incfun (add x s) i) = (fold incfun s i).
  intros. apply NatSet.eq_if_Equal. apply incfun_add_fold'. auto.
Qed.

Lemma incfun_fold_union' : forall {s s' i}, (forall x : elt, ~ (In x s /\ In x s')) -> (fold incfun (union s s') i) [=] (fold incfun s (fold incfun s' i)).
  intros. apply NatSetProperties.fold_union; auto. apply NatSetFacts.Equal_ST.
Qed.

Lemma union_empty_inv' : forall {s1 s2}, {}N [=] union s1 s2 -> s1 [=] {}N /\ s2 [=] {}N.
  split; fnsetdec.
Qed.

Lemma union_empty_inv : forall {s1 s2}, {}N = union s1 s2 -> s1 = {}N /\ s2 = {}N.
  intros. assert ({}N [=] union s1 s2). rewrite H. intuition.
  apply union_empty_inv' in H0. intuition; apply NatSet.eq_if_Equal; auto.
Qed.

Lemma inc_union_dist : forall {s1 s2}, inc (union s1 s2) = union (inc s1) (inc s2).
  intros. unfold inc. remember (union s1 s2) as s. generalize dependent s2.
  generalize dependent s1. apply NatSetProperties.fold_rec.
  - intros. apply NatSetProperties.empty_is_empty_1 in H.
    apply NatSet.eq_if_Equal in H. subst. apply union_empty_inv in Heqs.
    intuition. subst. repeat rewrite NatSetProperties.fold_empty. fnsetdec.
  - intros. rewrite NatSetProperties.Add_Equal in H1. apply NatSet.eq_if_Equal in H1. rewrite H1 in *.
    assert (s' = union (remove x s1) (remove x s2)). {
      assert (add x s' [=] union s1 s2). rewrite Heqs. fnsetdec. fnsetdec. }
    specialize (H2 (remove x s1) (remove x s2)). intuition. rewrite H4.
    destruct (NatSetProperties.In_dec x s1); destruct (NatSetProperties.In_dec x s2).
    1,2 : replace (fold incfun s1 {}N) with (fold incfun (add x (remove x s1)) {}N).
    1,5 : replace (fold incfun s2 {}N) with (fold incfun (add x (remove x s2)) {}N).
    1,6 : rewrite incfun_fold_add; auto; try fnsetdec. 1,4 : rewrite incfun_fold_add; auto; try fnsetdec.
    2 : replace (fold incfun s1 {}N) with (fold incfun (remove x s1) {}N).
    4 : replace (fold incfun s2 {}N) with (fold incfun (remove x s2) {}N).
    1,2,4 : unfold incfun; fnsetdec.
    1-6 : f_equal; apply NatSet.eq_if_Equal; fnsetdec.
    assert (add x s' [=] union s1 s2). rewrite Heqs. fnsetdec.
    assert (In x s1 \/ In x s2). intuition; fnsetdec. intuition.
Qed.

Lemma inc_empty : inc {}N = {}N.
Proof.
  unfold inc. rewrite NatSetProperties.fold_empty. fnsetdec.
Qed.

Lemma inc_singleton : forall {x},
    inc (singleton x) =
    singleton (S x).
Proof.
  intros. unfold inc. unfold incfun.
  specialize (@NatSetProperties.singleton_equal_add x) as Heq.
  apply NatSet.eq_if_Equal in Heq. rewrite Heq.
  rewrite NatSetProperties.fold_add. rewrite NatSetProperties.fold_empty.
  fnsetdec. exists; auto. intuition. intuition. intros i j k. fnsetdec. fnsetdec.
Qed.

Lemma inc_add_aux : forall {s x}, ~ In x s -> inc (add x s) = add (S x) (inc s).
  intros. unfold inc. rewrite incfun_fold_add; auto.
  unfold incfun. fnsetdec.
Qed.

Lemma inc_in_iff : forall {s x}, In x s <-> In (S x) (inc s).
  induction s using NatSetProperties.set_induction.
  - apply NatSetProperties.empty_is_empty_1 in H.
    apply NatSet.eq_if_Equal in H. subst. rewrite inc_empty. fnsetdec.
  - intros. rewrite NatSetProperties.Add_Equal in H0. apply NatSet.eq_if_Equal in H0. rewrite H0 in *.
    rewrite inc_add_aux; auto. specialize (IHs1 x0).
    bdestruct (x =? x0). subst. fnsetdec.
    rewrite NatSetProperties.FM.add_neq_iff; auto.
    rewrite NatSetProperties.FM.add_neq_iff; auto.
Qed.

Lemma inc_add : forall {s x}, inc (add x s) = add (S x) (inc s).
  intros. destruct (NatSetProperties.In_dec x s).
  apply NatSet.eq_if_Equal. replace (add x s) with s.
  apply (@inc_in_iff s x) in i. replace (add (S x) (inc s)) with (inc s).
  fnsetdec. fnsetdec. fnsetdec.
  apply inc_add_aux. auto.
Qed.

Lemma inc_empty' : forall {s}, inc s = {}N -> s = {}N.
  induction s using NatSetProperties.set_induction; intros.
  - fnsetdec.
  - rewrite NatSetProperties.Add_Equal in H0. apply NatSet.eq_if_Equal in H0. rewrite H0 in *.
    rewrite inc_add in H1. assert (Empty (add (S x) (inc s1))). rewrite H1.
    fnsetdec. apply add_non_empty in H2. contradiction.
Qed.

Lemma inc_non_zero : forall {s}, ~ In 0 (inc s).
  induction s using NatSetProperties.set_induction.
  - intros. apply NatSetProperties.empty_is_empty_1 in H.
    apply NatSet.eq_if_Equal in H. subst. rewrite inc_empty. fnsetdec.
  - rewrite NatSetProperties.Add_Equal in H0. apply NatSet.eq_if_Equal in H0.
    rewrite H0 in *. rewrite inc_add. assert (0 <> S x). lia. fnsetdec.
Qed.

Lemma inc_max_elt : forall {s n}, max_elt s = Some n <-> max_elt (inc s) = Some (S n).
  intros. split; intros.
  - pose (H':=H). apply max_elt_iff in H'. apply max_elt_iff.
    intuition. rewrite <- inc_in_iff. auto. destruct m'.
    apply inc_non_zero in H2. contradiction.
    rewrite <- inc_in_iff in H2. intuition.
  - rewrite max_elt_iff. rewrite max_elt_iff in H. intuition.
    rewrite inc_in_iff. auto. rewrite inc_in_iff in H. apply H1 in H. lia.
Qed.

Lemma inc_max_elt_none : forall {s}, max_elt s = None <-> max_elt (inc s) = None.
  intros. split; intros.
  - apply max_elt_empty' in H. subst. rewrite inc_empty. apply max_elt_empty.
  - apply max_elt_empty' in H. apply inc_empty' in H. subst. apply max_elt_empty.
Qed.

Lemma inc_bound : forall {s n}, max_elt s = Some n -> bound (inc s) = S (bound s).
  intros. unfold bound. rewrite H. apply inc_max_elt in H. rewrite H. auto.
Qed.

Lemma inc_mono : forall {s1 s2}, s1 [<=] s2 <-> (inc s1) [<=] (inc s2).
  intros. split.
  - intros. unfold Subset. intros x. destruct x.
    intros. apply inc_non_zero in H0. contradiction.
    intros. rewrite <- inc_in_iff in H0. rewrite <- inc_in_iff. intuition.
  - intros. unfold Subset. intros x. intros.
    rewrite inc_in_iff in H0. rewrite inc_in_iff. intuition.
Qed.

Lemma inc_inter_dist : forall {s1 s2}, inc (inter s1 s2) = inter (inc s1) (inc s2).
  intros. unfold inc. remember (inter s1 s2) as s. generalize dependent s2.
  generalize dependent s1. apply NatSetProperties.fold_rec.
  - intros. apply NatSetProperties.empty_is_empty_1 in H. fold (inc s1). fold (inc s2).
    apply NatSet.eq_if_Equal in H. subst. apply NatSet.eq_if_Equal.
    split. intros. fnsetdec. intros. rewrite NatSetFacts.inter_iff in H.
    destruct a. intuition. apply inc_non_zero in H0. contradiction.
    repeat rewrite <- inc_in_iff in H. rewrite <- NatSetFacts.inter_iff in H.
    rewrite <- Heqs in H. fnsetdec.
  - intros. rewrite NatSetProperties.Add_Equal in H1. apply NatSet.eq_if_Equal in H1. rewrite H1 in *.
    assert (s' = inter (remove x s1) (remove x s2)). {
      assert (add x s' [=] inter s1 s2). rewrite Heqs. fnsetdec. fnsetdec. }
    specialize (H2 (remove x s1) (remove x s2)). intuition. rewrite H4.
    replace (fold incfun s1 {}N) with (fold incfun (add x (remove x s1)) {}N).
    replace (fold incfun s2 {}N) with (fold incfun (add x (remove x s2)) {}N).
    repeat rewrite incfun_fold_add; auto; try fnsetdec. unfold incfun. fnsetdec.
    f_equal. assert (add x s' [=] inter s1 s2). rewrite Heqs. fnsetdec. fnsetdec.
    f_equal. assert (add x s' [=] inter s1 s2). rewrite Heqs. fnsetdec. fnsetdec.
Qed.

Lemma union_assoc : forall {s1 s2 s3},
    union (union s1 s2) s3 =
    union s1 (union s2 s3).
Proof. intros. fnsetdec. Qed.

Lemma union_symmetry : forall {s1 s2},
    NatSet.F.union s1 s2 = NatSet.F.union s2 s1.
Proof. intros. fnsetdec. Qed.

Lemma filter_singleton_1 : forall {f x},
    f x = true ->
    filter f (singleton x) = singleton x.
  intros. apply NatSet.eq_if_Equal. split; intros.
  rewrite  NatSetFacts.filter_iff in H0; intuition.
  rewrite  NatSetFacts.filter_iff; intuition.
  rewrite NatSetFacts.singleton_iff in H0. subst. auto.
Qed.

Lemma filter_singleton_2 : forall {f x},
    f x = false ->
    filter f (singleton x) = {}N.
  intros.   intros. apply NatSet.eq_if_Equal. split; intros.
  rewrite  NatSetFacts.filter_iff in H0; intuition.
  rewrite NatSetFacts.singleton_iff in H1. subst. rewrite H in H2. discriminate.
  fnsetdec.
Qed.

Lemma filter_lt_fun_prop : forall {s k x}, In x (filter (lt_fun k) s) -> x < k.
  intros. apply filter_2 in H; auto. unfold lt_fun in H. rewrite Nat.ltb_lt in H. lia.
Qed.

Lemma filter_ge_fun_prop : forall {s k x}, In x (filter (ge_fun k) s) -> k <= x.
  intros. apply filter_2 in H; auto. unfold ge_fun in H. rewrite Nat.leb_le in H. lia.
Qed.

Lemma filter_lt_fun_bound : forall {s k}, (bound (filter (lt_fun k) s)) <= S k.
  intros. unfold bound. destruct (max_elt (filter (lt_fun k) s)) eqn:Hmax.
  rewrite max_elt_iff in Hmax. intuition. apply filter_lt_fun_prop in H. lia.
  lia.
Qed.

Lemma filter_ge_lt_disjoint : forall {s n x}, ~(In x (filter (ge_fun n) s) /\ In x (filter (lt_fun n) s)).
  intros. intuition. apply filter_2 in H0; auto. apply filter_2 in H1; auto.
  unfold ge_fun in *. unfold lt_fun in *. rewrite Nat.leb_le in H0.
  rewrite Nat.ltb_lt in H1. lia.
Qed.

Lemma filter_partition_id: forall {s n}, s [=] (union (filter (ge_fun n) s) (filter (lt_fun n) s)).
  intros. split; intros.
  - rewrite NatSetFacts.union_iff.
    bdestruct (n <=? a). left. apply filter_3; auto. unfold ge_fun. rewrite Nat.leb_le. auto.
    right. apply filter_3; auto. unfold lt_fun. rewrite Nat.ltb_lt. auto.
  - rewrite NatSetFacts.union_iff in H. intuition; apply filter_1 in H0; auto.
Qed.

Lemma splice_set_subset_dist : forall {i s1 s2},
    (splice_set i s1) [<=] (splice_set i s2) <-> s1 [<=] s2.
  intros. unfold splice_set in *. split; intros.
  - unfold Subset. intros x Hin. setoid_rewrite (@filter_partition_id s1 i) in Hin.
    rewrite NatSetFacts.union_iff in Hin. intuition.
    * assert (In (S x) (union (inc (filter (ge_fun i) s2)) (filter (lt_fun i) s2))). rewrite inc_in_iff in H0.
      fnsetdec. rewrite NatSetFacts.union_iff in H1. intuition.
      rewrite <- inc_in_iff in H2. apply filter_1 in H2; auto.
      apply filter_lt_fun_prop in H2. apply filter_ge_fun_prop in H0. lia.
    * assert (In x (union (inc (filter (ge_fun i) s2)) (filter (lt_fun i) s2))). fnsetdec.
      rewrite NatSetFacts.union_iff in H1. intuition.
      apply filter_lt_fun_prop in H0. destruct x. apply inc_non_zero in H2. contradiction.
      rewrite <- inc_in_iff in H2. apply filter_ge_fun_prop in H2. lia.
      apply filter_1 in H2; auto.
  - assert (Hinc : (inc (filter (ge_fun i) s1)) [<=] (inc (filter (ge_fun i) s2))). {
      rewrite <- inc_mono. apply NatSetFacts.filter_subset; auto. }
    assert (Hflt : ((filter (lt_fun i) s1) [<=] (filter (lt_fun i) s2))). {
      apply NatSetFacts.filter_subset; auto. }
    fnsetdec.
Qed.

Lemma splice_set_empty : forall {i}, splice_set i {}N = {}N.
  intros. unfold splice_set. rewrite filter_empty.
  rewrite filter_empty. rewrite inc_empty. fnsetdec.
Qed.
#[global] Hint Resolve splice_set_empty : core.

Lemma splice_set_inter_dist : forall {s1 s2 k}, splice_set k (inter s1 s2) = inter (splice_set k s1) (splice_set k s2).
  intros. unfold splice_set. repeat rewrite filter_inter_dist. apply NatSet.eq_if_Equal.
  remember (filter (ge_fun k) s1) as A1. remember (filter (lt_fun k) s1) as B1.
  remember (filter (ge_fun k) s2) as A2. remember (filter (lt_fun k) s2) as B2.
  repeat rewrite inc_inter_dist.
  split; try fnsetdec. rewrite <- inc_inter_dist. intros.
  rewrite NatSetFacts.inter_iff in H. intuition. rewrite NatSetFacts.union_iff.
  rewrite NatSetFacts.union_iff in *. intuition; subst; destruct a;
                                        try apply inc_non_zero in H; try apply inc_non_zero in H0; try contradiction.
  rewrite <- inc_in_iff in H. rewrite <- inc_in_iff in H0. rewrite <- inc_in_iff. intuition.
  rewrite <- inc_in_iff in H. apply filter_2 in H; auto. apply filter_2 in H0; auto.
  unfold ge_fun in H. unfold lt_fun in H0. rewrite Nat.ltb_lt in H0. rewrite Nat.leb_le in H. lia.
  rewrite <- inc_in_iff in H0. apply filter_2 in H; auto. apply filter_2 in H0; auto.
  unfold ge_fun in H0. unfold lt_fun in H. rewrite Nat.ltb_lt in H. rewrite Nat.leb_le in H0. lia.
Qed.

Lemma splice_set_union_dist : forall {s1 s2 k},
    splice_set k (union s1 s2) = union (splice_set k s1) (splice_set k s2).
  intros. unfold splice_set. repeat rewrite filter_union_dist.
  repeat rewrite inc_union_dist. fnsetdec.
Qed.

Lemma in_singleton_filter : forall {a f i}, In a (filter f (singleton i)) -> a = i /\ f a = true.
  intros. split. apply filter_1 in H; auto. rewrite NatSetFacts.singleton_iff in H. auto.
  apply filter_2 in H; auto.
Qed.

Lemma splice_set_singleton_inv : forall {i k},
    i < k ->
    splice_set k (singleton i) = singleton i.
  intros. apply NatSet.eq_if_Equal. unfold splice_set. split; intros.
  rewrite NatSetFacts.union_iff in H0. intuition.
  destruct a. apply inc_non_zero in H1. contradiction. rewrite <- inc_in_iff in H1.
  apply in_singleton_filter in H1. unfold ge_fun in *. intuition. subst.
  rewrite Nat.leb_le in H2. lia. apply filter_1 in H1; auto.
  rewrite NatSetFacts.union_iff. right. apply filter_3; auto.
  unfold lt_fun. rewrite Nat.ltb_lt. rewrite NatSetFacts.singleton_iff in H0. subst. lia.
Qed.

Lemma splice_set_id: forall {s n k}, max_elt s = Some n -> n < k -> (splice_set k s) = s.
Proof.
  intros. unfold splice_set.
  unfold ge_fun. erewrite filter_gt; eauto.
  unfold lt_fun. erewrite filter_lt; eauto.
  rewrite inc_empty. fnsetdec.
Qed.

Lemma splice_set_preserves_subset : forall {s1 s2 n m},
    s1 [<=] s2 -> bound s2 <= n + m -> (splice_set m s1) [<=] (splice_set m s2).
 intros. rewrite splice_set_subset_dist. auto.
Qed.

Lemma splice_set_preserves_bound : forall {n k s},
    max_elt s = Some n -> n < k -> bound s = bound (splice_set k s).
  intros. erewrite splice_set_id; eauto.
Qed.

Lemma filter_ge_fun_max_elt : forall {s n}, max_elt s = Some n -> forall {k}, k <= n -> max_elt (filter (ge_fun k) s) = Some n.
  intros. rewrite max_elt_iff. intuition. apply filter_3; auto. rewrite max_elt_iff in H. intuition.
  unfold ge_fun. rewrite Nat.leb_le. auto. apply filter_1 in H1; auto.
  specialize (max_elt_2 H H1). intros. rewrite not_E_lt_nat_ge in H2.  lia.
Qed.

Lemma splice_set_inc_bound : forall {n k s},
    max_elt s = Some n -> k <= n -> S (bound s) = bound (splice_set k s).
  intros. unfold splice_set. rewrite union_bound_max'.
  rewrite @inc_bound with (n:=n). replace (bound s) with (S n).
  apply @filter_ge_fun_max_elt with (k:=k) (n:=n) in H; auto.
  replace (bound (filter (ge_fun k) s)) with (S n).
  specialize (@filter_lt_fun_bound s k). lia.
  1,2: unfold bound; rewrite H; auto.
  eapply filter_ge_fun_max_elt; eauto.
Qed.

Lemma splice_set_preserves_superset_1 : forall {s1 s2 i f},
    f <= i -> bound s1 <= f -> s1 [<=] s2 -> s1 [<=] (splice_set i s2).
  intros. destruct (is_empty s1) eqn:Hempty.
  - apply is_empty_2 in Hempty. apply NatSetProperties.empty_is_empty_1 in Hempty. fnsetdec.
  - apply max_elt_non_empty' in Hempty. destruct Hempty as [n Hmax].
    unfold bound in H0. rewrite Hmax in H0.
    erewrite <- @splice_set_id with (s:=s1) (k:=i); eauto; try lia.
    rewrite splice_set_subset_dist. auto.
Qed.

Lemma splice_set_preserves_superset_2 : forall {s1 s2 i f},
    f <= i -> bound s1 <= f -> s1 [<=] (splice_set i s2) -> s1 [<=] s2.
  intros. destruct (is_empty s1) eqn:Hempty.
  - apply is_empty_2 in Hempty. apply NatSetProperties.empty_is_empty_1 in Hempty. fnsetdec.
  - apply max_elt_non_empty' in Hempty. destruct Hempty as [n Hmax].
    unfold bound in H0. rewrite Hmax in H0.
    erewrite <- @splice_set_id with (s:=s1) (k:=i) in H1; eauto; try lia.
    rewrite splice_set_subset_dist in H1. auto.
Qed.

Lemma decfun_compat_op : SetoidList.compat_op Logic.eq Equal decfun.
  unfold SetoidList.compat_op. unfold Proper. unfold respectful.
  intros. subst. apply NatSet.eq_if_Equal in H0. subst. intuition.
Qed.
#[global] Hint Resolve decfun_compat_op : core.

Lemma decfun_transpose : SetoidList.transpose Equal decfun.
  unfold SetoidList.transpose. intros. unfold decfun.
  fnsetdec.
Qed.
#[global] Hint Resolve decfun_transpose : core.

Lemma decfun_fold_add': forall {i s x}, ~ In x s -> (fold decfun (add x s) i) [=] (decfun x (fold decfun s i)).
  intros. apply NatSetProperties.fold_add; auto. apply NatSetFacts.Equal_ST.
Qed.

Lemma decfun_fold_add: forall {i s x}, ~ In x s -> (fold decfun (add x s) i) = (decfun x (fold decfun s i)).
  intros. apply NatSet.eq_if_Equal. apply decfun_fold_add'; auto.
Qed.

Lemma decfun_add_fold': forall {i s x}, In x s -> (fold decfun (add x s) i) [=] (fold decfun s i).
  intros. setoid_rewrite NatSetProperties.add_fold; auto. intuition. apply NatSetFacts.Equal_ST.
Qed.

Lemma decfun_add_fold: forall {i s x}, In x s -> (fold decfun (add x s) i) = (fold decfun s i).
  intros. apply NatSet.eq_if_Equal. apply decfun_add_fold'. auto.
Qed.

Lemma decfun_fold_union' : forall {s s' i}, (forall x : elt, ~ (In x s /\ In x s')) -> (fold decfun (union s s') i) [=] (fold decfun s (fold decfun s' i)).
  intros. apply NatSetProperties.fold_union; auto. apply NatSetFacts.Equal_ST.
Qed.

Lemma member_lower_bound : forall {s x},
    mem x s = true -> S x <= bound s.
Proof.
  intros. unfold bound. destruct (max_elt s) eqn:Hmax.
  - apply mem_2 in H. specialize (@max_elt_2 _ _ _ Hmax H) as Hgt.
    apply not_E_lt_nat_ge in Hgt. lia.
  - specialize (@max_elt_none_mem _ _ Hmax H) as F.  inversion F.
Qed.

Lemma dec_empty : dec {}N = {}N.
Proof.
  intros. unfold dec. unfold decfun. rewrite NatSetProperties.fold_empty. fnsetdec.
Qed.

Lemma dec_singleton : forall {x},
    dec (singleton x) =
    singleton (pred x).
Proof.
  intros. unfold dec. unfold decfun.
  specialize (@NatSetProperties.singleton_equal_add x) as Heq.
  apply NatSet.eq_if_Equal in Heq. rewrite Heq.
  rewrite NatSetProperties.fold_add. rewrite NatSetProperties.fold_empty.
  fnsetdec. exists; auto. intuition. intuition. intros i j k. fnsetdec. fnsetdec.
Qed.

Lemma dec_union_dist : forall {s1 s2}, dec (union s1 s2) = union (dec s1) (dec s2).
  intros. unfold dec. remember (union s1 s2) as s. generalize dependent s2.
  generalize dependent s1. apply NatSetProperties.fold_rec.
  - intros. apply NatSetProperties.empty_is_empty_1 in H.
    apply NatSet.eq_if_Equal in H. subst. apply union_empty_inv in Heqs.
    intuition. subst. repeat rewrite NatSetProperties.fold_empty. fnsetdec.
  - intros. rewrite NatSetProperties.Add_Equal in H1. apply NatSet.eq_if_Equal in H1. rewrite H1 in *.
    assert (s' = union (remove x s1) (remove x s2)). {
      assert (add x s' [=] union s1 s2). rewrite Heqs. fnsetdec. fnsetdec. }
    specialize (H2 (remove x s1) (remove x s2)). intuition. rewrite H4.
    destruct (NatSetProperties.In_dec x s1); destruct (NatSetProperties.In_dec x s2).
    1,2 : replace (fold decfun s1 {}N) with (fold decfun (add x (remove x s1)) {}N).
    1,5 : replace (fold decfun s2 {}N) with (fold decfun (add x (remove x s2)) {}N).
    1,6 : rewrite decfun_fold_add; auto; try fnsetdec. 1,4 : rewrite decfun_fold_add; auto; try fnsetdec.
    2 : replace (fold decfun s1 {}N) with (fold decfun (remove x s1) {}N).
    4 : replace (fold decfun s2 {}N) with (fold decfun (remove x s2) {}N).
    1,2,4 : unfold decfun; fnsetdec.
    1-6 : f_equal; apply NatSet.eq_if_Equal; fnsetdec.
    assert (add x s' [=] union s1 s2). rewrite Heqs. fnsetdec.
    assert (In x s1 \/ In x s2). intuition; fnsetdec. intuition.
Qed.

Lemma dec_add_aux : forall {s x}, ~ In x s -> dec (add x s) = add (pred x) (dec s).
  intros. unfold dec. rewrite decfun_fold_add; auto.
  unfold decfun. fnsetdec.
Qed.

Lemma dec_in1 : forall {s x}, In x s -> In (pred x) (dec s).
  induction s using NatSetProperties.set_induction.
  - apply NatSetProperties.empty_is_empty_1 in H.
    apply NatSet.eq_if_Equal in H. subst. rewrite dec_empty. fnsetdec.
  - intros. rewrite NatSetProperties.Add_Equal in H0. apply NatSet.eq_if_Equal in H0. rewrite H0 in *.
    rewrite dec_add_aux; auto. specialize (IHs1 x0). fnsetdec.
Qed.

Lemma dec_in_iff : forall {s x}, x > 1 -> In x s <-> In (pred x) (dec s).
  induction s using NatSetProperties.set_induction.
  - apply NatSetProperties.empty_is_empty_1 in H.
    apply NatSet.eq_if_Equal in H. subst. rewrite dec_empty. fnsetdec.
  - intros. rewrite NatSetProperties.Add_Equal in H0. apply NatSet.eq_if_Equal in H0. rewrite H0 in *.
    rewrite dec_add_aux; auto. specialize (IHs1 x0).
    bdestruct (x =? x0). subst. fnsetdec.
    rewrite NatSetProperties.FM.add_neq_iff; auto.
    rewrite NatSetProperties.FM.add_neq_iff; auto. lia.
Qed.

Lemma dec_in0 : forall {s}, ~ In 0 s -> In 0 (dec s) <-> In 1 s.
  induction s using NatSetProperties.set_induction.
  - apply NatSetProperties.empty_is_empty_1 in H.
    apply NatSet.eq_if_Equal in H. subst. rewrite dec_empty. fnsetdec.
  - intros. rewrite NatSetProperties.Add_Equal in H0. apply NatSet.eq_if_Equal in H0. rewrite H0 in *.
    rewrite dec_add_aux; auto. destruct x.
    simpl. fnsetdec. simpl. split. fnsetdec. assert (~ In 0 s1). fnsetdec.
    specialize (IHs1 H2). destruct x. fnsetdec. intros. apply add_3 in H3.
    rewrite <- IHs1 in H3. fnsetdec. auto.
Qed.

Lemma unsplice_set_inv : forall {vs f x},
    bound vs <= f ->
    f <= x ->
    unsplice_set x vs = vs.
Proof.
  intros. unfold unsplice_set. unfold decfun. unfold bound in H.
  destruct (max_elt vs) eqn: Hmax.
  - assert (e < x) by lia. autounfold. erewrite filter_lt; eauto.
    erewrite filter_gt; eauto. rewrite dec_empty. fnsetdec.
  - apply max_elt_empty' in Hmax. subst.
    rewrite filter_empty. rewrite filter_empty.
    rewrite dec_empty. fnsetdec.
Qed.

Lemma unsplice_set_union_dist : forall {x xs ys},
    unsplice_set x (union xs ys) = union (unsplice_set x xs) (unsplice_set x ys).
    intros. unfold unsplice_set. repeat rewrite filter_union_dist.
    repeat rewrite dec_union_dist. fnsetdec.
Qed.

Lemma unsplice_set_inv' : forall {vs x},
    bound vs <= x ->
    unsplice_set x vs = vs.
Proof.
  intros. unfold bound in H. destruct (max_elt vs) eqn:Hmax.
  - assert (e < x) by lia.
    unfold unsplice_set. erewrite filter_gt; eauto. autounfold.
    erewrite filter_lt; eauto. rewrite dec_empty. fnsetdec.
  - apply max_elt_empty' in Hmax. subst.
    unfold unsplice_set. rewrite filter_empty. rewrite filter_empty.
    rewrite dec_empty. fnsetdec.
Qed.

Lemma unsplice_set_singleton_dec : forall {x y}, x <= S y -> unsplice_set x (singleton (S y)) = singleton y.
  intros. unfold unsplice_set. rewrite filter_singleton_1. rewrite dec_singleton. simpl.
  rewrite filter_singleton_2. fnsetdec.
  unfold lt_fun. apply Nat.ltb_ge. auto.
  unfold ge_fun. apply Nat.leb_le. auto.
Qed.

Lemma union_bound : forall {xs ys f}, bound xs <= f -> bound ys <= f -> bound (union xs ys) <= f.
  intros. specialize (@union_bound_max xs ys). lia.
Qed.

Lemma remove_union_dist : forall {x xs ys},
    remove x (union xs ys) =
    union (remove x xs) (remove x ys).
Proof. intros. fnsetdec. Qed.

Lemma remove_singleton_empty : forall {n},
    remove n (singleton n) = {}N.
Proof. intros. fnsetdec. Qed.

Lemma remove_union_singleton_id : forall {s x},
    mem x s = false ->
    s = remove x (union s (singleton x)).
Proof.
  intros. rewrite remove_union_dist. rewrite remove_singleton_empty.
  apply NatSetProperties.FM.not_mem_iff in H.
  specialize (@NatSetProperties.remove_equal s x) as Heq.
  apply NatSet.eq_if_Equal in Heq; auto. rewrite Heq. fnsetdec.
Qed.

Lemma bound_le_mem_false : forall {x s},
    bound s <= x ->
    mem x s = false.
Proof.
  intros. unfold bound in H.
  destruct (max_elt s) eqn:Hmax.
  - assert (e < x) by lia. apply NatSetProperties.FM.not_mem_iff.
    eapply bound_max_not_in. apply Hmax. apply nat_E_lt. lia.
  - apply max_elt_empty' in Hmax. subst.
    apply NatSetProperties.FM.not_mem_iff. fnsetdec.
Qed.

Lemma bound_dec : forall {s}, bound (dec s) <= bound s.
Proof.
  intros. unfold dec.
  apply NatSetProperties.fold_rec; intros.
  - rewrite bound_empty. lia.
  - rewrite NatSetProperties.Add_Equal in H1.
    assert (s' [<=] s''). fnsetdec.
    specialize (@subset_bound' s' s'' H3) as Hb.
    assert (bound s'' <= bound s'') by lia.
    rewrite (@union_bound a (singleton (pred x))). apply H4. lia.
    assert (bound (singleton (pred x)) <= bound (singleton x)).
    rewrite bound_singleton. rewrite bound_singleton. lia.
    assert (singleton x [<=] s''). fnsetdec.
    specialize (@subset_bound' (singleton x) s'' H6) as Hb'.
    lia.
Qed.

Lemma unsplice_set_preserves_bound : forall {s x f},
    bound s <= f ->
    bound (unsplice_set x s) <= f.
Proof.
  intros. unfold unsplice_set.
  rewrite (@union_bound (dec (filter (fun i : elt => x <=? i) s)) (filter (fun i : elt => i <? x) s)). auto.
  - specialize (@filter_subset s (fun i => x <=? i)) as Hsub.
    specialize (@subset_bound' (filter (fun i : elt => x <=? i) s) s Hsub) as Hb.
    specialize (@bound_dec (filter (fun i : elt => x <=? i) s)) as Hdec.
    lia.
  - specialize (@filter_subset s (fun i => i <? x)) as Hsub.
    specialize (@subset_bound' (filter (fun i : elt => i <? x) s) s Hsub) as Hb.
    lia.
Qed.

Lemma unsplice_set_bound : forall {vs f},
      bound vs <= S f -> ~ In 0 vs ->
      bound (unsplice_set 0 vs) <= f.
  intros. unfold unsplice_set. unfold bound in H.
  destruct (max_elt vs) eqn: Hmax.
  - rewrite (@union_bound (dec (filter (fun i : elt => 0 <=? i) vs))
                          (filter (fun i : elt => i <? 0) vs) f); auto.
    + unfold dec. apply NatSetProperties.fold_rec; intros.
      * rewrite bound_empty. lia.
      * rewrite (@union_bound a (singleton (pred x)) f); auto.
        rewrite bound_singleton. assert (e <= f) by lia.
        apply filter_1 in H1; intuition.
        destruct x. contradiction. simpl.
        specialize (@max_elt_2 _ _ _ Hmax H1) as Hgt.
        apply not_E_lt_nat_ge in Hgt. lia.
    + assert (filter (fun i => i <? 0) vs= {}N).
      apply NatSet.eq_if_Equal. split; intros.
      apply filter_2 in H1. apply Nat.ltb_lt in H1. lia. intuition.
      pose (@NatSetNotin.notin_empty a). contradiction.
      rewrite H1. rewrite bound_empty. lia.
  - apply max_elt_empty' in Hmax. subst.
    rewrite filter_empty. rewrite filter_empty.
    rewrite dec_empty. rewrite empty_union_left. rewrite bound_empty. lia.
Qed.

Lemma unsplice_set_dec : forall {vs f},
      bound vs <= S f ->
      bound (unsplice_set 0 (remove 0 vs)) <= f.
Proof.
  intros. unfold unsplice_set. unfold bound in H.
  destruct (max_elt vs) eqn: Hmax.
  - rewrite (@union_bound (dec (filter (fun i : elt => 0 <=? i) (remove 0 vs)))
                          (filter (fun i : elt => i <? 0) (remove 0 vs)) f); auto.
    + unfold dec. apply NatSetProperties.fold_rec; intros.
      * rewrite bound_empty. lia.
      * rewrite (@union_bound a (singleton (pred x)) f); auto.
        rewrite bound_singleton. assert (e <= f) by lia.
        apply filter_1 in H0; intuition.
        apply NatSetDecide.FSetDecideAuxiliary.F.remove_iff in H0; intuition.
        assert (S (pred x) = x). lia. rewrite H0.
        specialize (@max_elt_2 _ _ _ Hmax H5) as Hgt.
        apply not_E_lt_nat_ge in Hgt. lia.
    + assert (filter (fun i => i <? 0) (remove 0 vs) = {}N).
      apply NatSet.eq_if_Equal. split; intros.
      apply filter_2 in H0. apply Nat.ltb_lt in H0. lia. intuition.
      pose (@NatSetNotin.notin_empty a). contradiction.
      rewrite H0. rewrite bound_empty. lia.
  - apply max_elt_empty' in Hmax. subst.
    assert (remove 0 {}N = {}N) by fnsetdec.
    rewrite H0. rewrite filter_empty. rewrite filter_empty.
    rewrite dec_empty. rewrite empty_union_left. rewrite bound_empty. lia.
Qed.

Lemma unsplice_set_empty : forall {n},
    unsplice_set n {}N = {}N.
Proof.
  intros. unfold unsplice_set. rewrite filter_empty. rewrite filter_empty.
  rewrite dec_empty. fnsetdec.
Qed.

Lemma remove_empty : forall {n},
    remove n {}N = {}N.
Proof. intros. fnsetdec. Qed.

Lemma mem_singleton : forall {n x : nat},
    mem x (singleton n) = (Nat.eqb x n).
Proof.
  intros. rewrite NatSetFacts.singleton_b. apply natset_eqb.
Qed.

Lemma remove_singleton_inv : forall {x y},
    x <> y ->
    remove x (singleton y) = singleton y.
Proof.
  intros. assert (~ In x (singleton y)). fnsetdec.
  specialize (@NatSetProperties.remove_equal _ _ H0). fnsetdec.
Qed.

Lemma subset_inclusion : forall {s1 s2 x},
    Subset s1 s2 ->
    mem x s1 = true ->
    mem x s2 = false -> False.
Proof.
  intros. apply mem_2 in H0.
  apply NatSetProperties.FM.not_mem_iff in H1.
  unfold Subset in H. apply H in H0. contradiction.
Qed.

Lemma subset_union_remove : forall {s1 s2 s3 x},
    Subset s1 s2 ->
    mem x s1 = false ->
    Subset s1 (union (remove x s2) s3).
Proof.
  intros. apply NatSetProperties.FM.not_mem_iff in H0.
  assert (remove x s1 [<=] remove x s2).
  apply NatSetProperties.Dec.F.remove_s_m; auto.
  erewrite <- (NatSetProperties.remove_equal H0). fnsetdec.
Qed.

Lemma remove_not_in : forall {x s}, mem x s = false -> remove x s = s.
Proof.
  intros. apply NatSetDecide.FSetDecideAuxiliary.F.not_mem_iff in H.
  specialize (@NatSetProperties.remove_equal _ _ H) as H3.
  fnsetdec.
Qed.

Lemma not_member_union : forall {x s1 s2},
    mem x s1 = false ->
    mem x s2 = false ->
    mem x (union s1 s2) = false.
Proof.
  intros. apply NatSetProperties.FM.not_mem_iff.
  apply NatSetProperties.FM.not_mem_iff in H.
  apply NatSetProperties.FM.not_mem_iff in H0. fnsetdec.
Qed.

Lemma disjoint_glb_lub_eq : forall {s1 s2 x},
    bound s1 <= x ->
    inter s1 s2 = inter s1 (union s2 (singleton x)).
Proof.
  intros. unfold bound in H.
  destruct (max_elt s1) eqn:Hmax.
  - assert (~ In x s1). eapply max_gt_bound_not_in. apply H. assert (S e <= S e) by lia.
    auto. auto.
    specialize (@NatSetProperties.inter_sym s1 (union s2 (singleton x))) as Hi.
    apply NatSet.eq_if_Equal in Hi. rewrite Hi.
    specialize (@NatSetProperties.union_inter_1 s2 (singleton x) s1) as Hi2.
    apply NatSet.eq_if_Equal in Hi2. rewrite Hi2.
    assert (inter (singleton x) s1 = {}N). fnsetdec. rewrite H1.
    rewrite empty_union_right. fnsetdec.
  - apply max_elt_empty' in Hmax. subst. fnsetdec.
Qed.

Lemma filter_ge0_id : forall {s}, (filter (ge_fun 0) s) = s.
  induction s using NatSetProperties.set_induction.
  - apply NatSetProperties.empty_is_empty_1 in H.
    apply NatSet.eq_if_Equal in H. subst. apply filter_empty.
  - rewrite NatSetProperties.Add_Equal in H0. apply NatSet.eq_if_Equal in H0. subst.
    replace (add x s1) with (union (singleton x) s1). rewrite filter_union_dist.
    rewrite IHs1. f_equal. rewrite filter_singleton_1. auto.
    unfold ge_fun. auto. apply NatSet.eq_if_Equal.
    setoid_rewrite NatSetProperties.add_union_singleton. intuition.
Qed.

Lemma unsplice_set_subset_monotone: forall {s1 s2},
    s1 [<=] s2 -> (unsplice_set 0 (remove 0 s1)) [<=] (unsplice_set 0 (remove 0 s2)).
  intros. unfold unsplice_set. unfold Subset.
  intros x Hx. rewrite NatSetFacts.union_iff in Hx. intuition.
  * rewrite NatSetFacts.union_iff. left.
    destruct x. rewrite filter_ge0_id. rewrite filter_ge0_id in H0.
    rewrite dec_in0 in H0. replace 0 with (pred 1); auto.
    apply dec_in1. simpl. apply NatSetFacts.remove_s_m with (x:=0) (y:=0) in H; auto.
    fnsetdec.
    replace (S x) with (pred (S (S x))) in *; auto.
    rewrite <- dec_in_iff in H0; auto; try lia.
    rewrite <- dec_in_iff; auto; try lia.
    apply filter_3; auto. apply filter_1 in H0; auto.
    apply NatSetFacts.remove_s_m with (x:=0) (y:=0) in H.
    unfold Subset in H. apply H. auto. auto.
  * rewrite NatSetFacts.union_iff. right. apply filter_3; auto.
    apply filter_1 in H0; auto. fnsetdec. apply filter_2 in H0; auto.
Qed.

Lemma bound_union: forall {xs ys : nats} {f : nat},
    bound (union xs ys) <= f  -> bound xs <= f /\ bound ys <= f.
Proof.
  intros. generalize dependent ys.
  induction xs using NatSetProperties.set_induction; intros.
  - apply NatSetProperties.empty_is_empty_1 in H. apply NatSet.eq_if_Equal in H. subst.
    rewrite empty_union_left in H0. split; auto.
    rewrite bound_empty. lia.
  - induction ys using NatSetProperties.set_induction.
    + apply NatSetProperties.empty_is_empty_1 in H2.
      apply NatSet.eq_if_Equal in H2. subst.
      rewrite empty_union_right in H1. split; auto.
      rewrite bound_empty. lia.
    + apply NatSetProperties.Add_Equal in H3.
      apply NatSetProperties.Add_Equal in H0.
      assert (Subset ys1 ys2). rewrite H3. fnsetdec.
      assert ((union xs2 ys1) [<=] (union xs2 ys2)) by fnsetdec.
      assert (bound (union xs2 ys1) <= f). eapply subset_bound. apply H5.
      apply H1. split. intuition.
      specialize (IHxs1 ys2).
      assert (Subset xs1 xs2). rewrite H0. fnsetdec.
      assert ((union xs1 ys2) [<=] (union xs2 ys2)) by fnsetdec.
      assert (bound (union xs1 ys2) <= f). eapply subset_bound. apply H8.
      apply H1. intuition.
Qed.

Lemma lt_mem_nset : forall {n m}, n < m -> In n (nset m).
  intros. generalize dependent n. induction m; intros.
  - inversion H.
  - simpl. assert (n <= m) by lia. bdestruct (n =? m).
    + subst. fnsetdec.
    + assert (n < m) by lia. specialize (IHm n H2). fnsetdec.
Qed.

Lemma bound_dom_sub : forall {X A} {Σ : list A}, bound X <= (length Σ) -> Subset X (dom Σ).
  induction X using NatSetProperties.set_induction; intros.
  - fnsetdec.
  - unfold dom in *. specialize (IHX1 A Σ).
    remember (length Σ) as L. assert (H1' := H1).
    unfold bound in H1.
    destruct (max_elt X2) eqn:Hmax. assert (e < L) by lia.
    + assert (X2 = (add x X1)). apply NatSet.eq_if_Equal.
      apply NatSetProperties.Add_Equal. auto.
      assert (Subset X1 X2). subst. fnsetdec.
      specialize (@subset_bound' _ _ H4) as Hb.
      assert (bound X1 <= L) by lia. specialize (IHX1 H5).
      assert (In x X2). subst. fnsetdec.
      assert (x <= e). specialize (@max_elt_2 _ _ _ Hmax H6) as Hlt.
      apply not_E_lt_nat_ge in Hlt. lia.
      assert (x < L) by lia.
      subst. specialize (@lt_mem_nset _ _ H8) as Hnset. fnsetdec.
    + apply max_elt_empty' in Hmax. subst. fnsetdec.
Qed.

Lemma nset_subset : forall {n m}, n <= m -> Subset (nset n) (nset m).
  intro n. induction n; intros.
  - simpl. fnsetdec.
  - simpl. inversion H.
    + simpl. fnsetdec.
    + simpl. assert (n <= m0). lia. assert (n < m0). lia.
      assert (In n (nset m0)). apply lt_mem_nset; auto.
      specialize (IHn m0 H2). apply NatSetProperties.subset_add_2.
      apply NatSetProperties.subset_add_3; auto.
Qed.

Lemma nset_0_max : max_elt (nset 0) = None.
  simpl. apply max_elt_empty.
Qed.

Lemma nset_s_max : forall {n}, max_elt (nset (S n)) = Some n.
  induction n; simpl.
  replace (add 0 {}N) with (singleton 0). rewrite max_elt_singleton. auto.
  fnsetdec. erewrite max_elt_add_some; eauto. f_equal. lia.
Qed.

Lemma bound_nset_succ: forall {n}, bound (nset (S n)) = S (bound (nset n)).
  intros. simpl. unfold bound. destruct n.
  simpl. destruct (max_elt {}N) eqn:Hmax0. rewrite max_elt_empty in Hmax0. discriminate.
  replace (add 0 {}N) with (singleton 0). rewrite max_elt_singleton.
  auto. fnsetdec. specialize (@nset_s_max n) as Hmax. rewrite Hmax.
  erewrite max_elt_add_some; eauto. lia.
Qed.

Lemma bound_nset: forall {n}, bound (nset n) = n.
  induction n. simpl. apply bound_empty.
  rewrite bound_nset_succ. intuition.
Qed.

Lemma bound_dom: forall {A} {Σ : list A}, bound (dom Σ) = (length Σ).
  intros. unfold dom. apply bound_nset.
Qed.

Lemma singleton_empty_neq : forall {x}, (singleton x) <> {}N.
  intros. intuition. assert (bound (singleton x) = 0).
  rewrite H. apply bound_empty. rewrite bound_singleton in H0. lia.
Qed.

Lemma filter_lt_0 : forall {s}, (filter (lt_fun 0) s) = {}N.
  intros. specialize (NatSetDecide.FSetDecideAuxiliary.D.choose (filter (lt_fun 0) s)) as H. destruct H.
  - destruct s0. specialize (filter_lt_fun_prop i). lia.
  - fnsetdec.
Qed.

Lemma inter_unsplice_0 : forall {ff f1},
  inter (unsplice_set 0 (remove 0 ff))
        (unsplice_set 0 (remove 0 f1)) [=] (unsplice_set 0 (remove 0 (inter ff f1))).
  split; intros.
  * specialize (inter_1 H) as Hff. specialize (inter_2 H) as Hf1.
    unfold unsplice_set in *. rewrite filter_lt_0 in Hff. rewrite filter_lt_0 in Hf1.
    rewrite filter_ge0_id in Hff. rewrite filter_ge0_id in Hf1. rewrite empty_union_right in Hff.
    rewrite empty_union_right in Hf1. rewrite filter_ge0_id. rewrite filter_lt_0.
    rewrite empty_union_right. destruct a.
    ** rewrite dec_in0 in Hff; try fnsetdec. rewrite dec_in0 in Hf1; try fnsetdec.
       rewrite dec_in0; fnsetdec.
    ** change (S a) with (pred (S (S a))) in *. rewrite <- dec_in_iff in Hff; try lia.
       rewrite <- dec_in_iff in Hf1; try lia. rewrite <- dec_in_iff. fnsetdec. lia.
  * apply inter_3; eapply unsplice_set_subset_monotone; eauto; fnsetdec.
Qed.

Lemma unsplice_set_singleton' : forall {g},
    NatSet.F.singleton (pred g) = unsplice_set 0 (NatSet.F.singleton g).
Proof.
  intro. unfold unsplice_set.
  unfold ge_fun. unfold lt_fun.
  rewrite filter_singleton_1. rewrite filter_singleton_2.
  rewrite empty_union_right. rewrite dec_singleton. simpl. auto.
  apply Nat.ltb_ge. lia. apply leb_correct. lia.
Qed.

Lemma unsplice_set_singleton : forall {g},
    NatSet.F.singleton g = unsplice_set 0 (NatSet.F.singleton (S g)).
Proof.
  intros. remember (S g) as g'. assert (g = pred g'). rewrite Heqg'. simpl. auto.
  rewrite H. apply unsplice_set_singleton'.
Qed.

Lemma singleton_nonempty : forall {x}, singleton x = {}N -> False.
  intros. specialize (NatSetNotin.in_singleton x) as Hmem.
  rewrite H in Hmem. apply NatSetNotin.notin_empty in Hmem. auto.
Qed.

Lemma singleton_injective : forall {x y}, singleton x = singleton y -> x = y.
  intros. specialize (NatSetNotin.in_singleton x) as Hmem.
  rewrite H in Hmem. rewrite NatSetFacts.singleton_iff in Hmem. auto.
Qed.

Lemma inter_singleton_eq : forall {x}, inter (singleton x) (singleton x) = singleton x.
  intros. fnsetdec.
Qed.

Lemma inter_singleton_neq : forall {x y}, x <> y -> inter (singleton x) (singleton y) = {}N.
  intros. fnsetdec.
Qed.

Lemma bound_le_not_in : forall {x : nat} {s : nats}, bound s <= x -> ~ In x s.
  intros. specialize (bound_le_mem_false H) as Hx.
  rewrite <- NatSetFacts.not_mem_iff in Hx. auto.
Qed.

Lemma bound_disjoint : forall {s x}, bound s <= x -> forall {y}, x <= y -> inter s (singleton y) = {}N.
  intros. assert (H' : bound s <= y). lia. apply bound_le_not_in in H'. fnsetdec.
Qed.

Lemma mem_empty : forall {n}, mem n {}N = false.
Proof.
  intros. apply NatSetProperties.FM.not_mem_iff. fnsetdec.
Qed.

Lemma remove_inter_dist : forall {x xs ys},
    remove x (inter xs ys) = inter (remove x xs) (remove x ys).
Proof. intros. fnsetdec. Qed.

Lemma singleton_subset_in : forall x s, singleton x [<=] s -> In x s.
Proof. intros. fnsetdec. Qed.

Lemma inter_comm : forall {s1 s2}, inter s1 s2 = inter s2 s1.
Proof.
  intros.
  specialize (@NatSetProperties.inter_sym s1 s2) as Hi.
  apply NatSet.eq_if_Equal in Hi. rewrite Hi. reflexivity.
Qed.

Lemma subset_of_empty : forall s, NatSet.F.Subset s {}N -> s = {}N.
Proof. intros. fnsetdec. Qed.
#[global] Hint Resolve subset_of_empty : core.

Lemma splice_set_singleton_inc : forall {i k},
    i >= k -> splice_set k (singleton i) = singleton (S i).
  intros. apply NatSet.eq_if_Equal. unfold splice_set. split; intros.
  * rewrite NatSetFacts.union_iff in H0. intuition.
    destruct a. apply inc_non_zero in H1. contradiction. rewrite <- inc_in_iff in H1.
    apply in_singleton_filter in H1. unfold ge_fun in *. intuition. subst. fnsetdec.
    apply in_singleton_filter in H1. unfold lt_fun in *. intuition. subst.
    rewrite Nat.ltb_lt in H2. lia.
  * rewrite NatSetFacts.singleton_iff in H0. rewrite <- H0.
    apply union_2. rewrite <- inc_in_iff.
    rewrite filter_singleton_1. fnsetdec. unfold ge_fun. rewrite Nat.leb_le. lia.
Qed.

Lemma max_elt_bound_mem : forall {s b}, bound s <= (S b) -> In b s -> max_elt s = Some b.
  intros. unfold bound in H. destruct (max_elt s) eqn:Hmax.
  specialize (max_elt_2 Hmax H0) as Hm. rewrite nat_E_lt in Hm.
  assert (e = b). lia. subst. auto.
  apply mem_1 in H0. specialize (max_elt_none_mem Hmax H0). contradiction.
Qed.

Lemma remove_equal : forall {x s}, ~ In x s -> remove x s = s.
  intros. apply NatSet.eq_if_Equal. apply NatSetProperties.remove_equal. auto.
Qed.

Lemma remove_bound : forall {s b}, bound s <= (S b) -> bound (remove b s) <= b.
  intros. destruct (mem b s) eqn:Hmem.
  * apply mem_2 in Hmem. specialize (max_elt_bound_mem H Hmem) as Hmax.
    destruct (max_elt (remove b s)) eqn:Hmax'.
    - specialize (remove_max_bound Hmax Hmax') as Hlt.
      unfold bound. rewrite Hmax'. lia.
    - unfold bound. rewrite Hmax'. lia.
  * rewrite <- NatSetFacts.not_mem_iff in Hmem.
    rewrite remove_equal; auto. unfold bound in *.
    destruct (max_elt s) eqn:Hmax; try lia.
    assert (e <> b). { apply max_elt_1 in Hmax. intuition. subst. contradiction. }
    lia.
Qed.

Lemma is_empty_means_empty : forall {s}, is_empty s = true -> s = {}N.
  intros. apply NatSet.F.is_empty_2 in H.
  apply NatSetProperties.empty_is_empty_1 in H.
  apply NatSet.eq_if_Equal. auto.
Qed.

Lemma is_empty_true : is_empty {}N = true.
  apply NatSet.F.is_empty_1. apply NatSet.F.empty_1.
Qed.

Lemma mem_singleton' : forall {n}, mem n (singleton n) = true.
  intros. rewrite mem_singleton. rewrite Nat.eqb_refl. auto.
Qed.

Lemma mem_singleton_neq : forall {m n}, m <> n -> mem n (singleton m) = false.
  intros. rewrite mem_singleton. rewrite Nat.eqb_neq. auto.
Qed.

Lemma In_bound_lt : forall {x s}, In x s -> x < bound s.
  intros. unfold bound. assert (is_empty s = false).
  rewrite <- non_empty_iff. eapply in_non_empty; eauto.
  apply max_elt_non_empty' in H0. destruct H0.
  rewrite H0. specialize (max_elt_2 H0 H) as Hlt.
  apply not_E_lt_nat_ge in Hlt. lia.
Qed.

Lemma splice_set_injective : forall {k s s'}, (splice_set k s) = (splice_set k s') -> s = s'.
  intros. unfold splice_set in H. apply NatSet.eq_if_Equal.
  rewrite (@filter_partition_id s k). rewrite (@filter_partition_id s' k).
  apply Equal_if_eq in H. split; intros.
  - apply NatSetProperties.subset_equal in H.
    apply union_1 in H0. intuition.
    * specialize (filter_ge_fun_prop H1) as Ha.
      apply inc_in_iff in H1. apply (union_2 (filter (lt_fun k) s)) in H1.
      apply H in H1. apply union_1 in H1. intuition.
      rewrite <- inc_in_iff in H0. fnsetdec.
      apply filter_lt_fun_prop in H0. lia.
    * specialize (filter_lt_fun_prop H1) as Ha.
      apply (union_3 (inc (filter (ge_fun k) s))) in H1.
      apply H in H1. apply union_1 in H1. intuition.
      destruct a. apply inc_non_zero in H0. contradiction.
      rewrite <- inc_in_iff in H0. apply filter_ge_fun_prop in H0. lia.
  - apply NatSetProperties.equal_sym in H. apply NatSetProperties.subset_equal in H.
    apply union_1 in H0. intuition.
    * specialize (filter_ge_fun_prop H1) as Ha.
      apply inc_in_iff in H1. apply (union_2 (filter (lt_fun k) s')) in H1.
      apply H in H1. apply union_1 in H1. intuition.
      rewrite <- inc_in_iff in H0. fnsetdec.
      apply filter_lt_fun_prop in H0. lia.
    * specialize (filter_lt_fun_prop H1) as Ha.
      apply (union_3 (inc (filter (ge_fun k) s'))) in H1.
      apply H in H1. apply union_1 in H1. intuition.
      destruct a. apply inc_non_zero in H0. contradiction.
      rewrite <- inc_in_iff in H0. apply filter_ge_fun_prop in H0. lia.
Qed.