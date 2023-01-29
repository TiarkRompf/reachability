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

Require Import NatSets.
Require Import setfacts.
Import NatSet.F.

Import OpeningNotations.
Local Open Scope opening.

Import QualNotations.
Local Open Scope qualifiers.

(* ### Infrastructure for examples file ### *)

(* iterating over each hypothesis once, inspired by https://stackoverflow.com/a/46536938: *)
(* marker for iterating over hypotheses *)
Inductive ltac_Mark : Type :=
| ltac_mark : ltac_Mark.

(* apply tac over all the premises in the goal until the marker*)
Ltac repeat_until_mark tac :=
  lazymatch goal with
  | [ |- ltac_Mark -> _ ] => intros _
  | [ |- _ ] => tac (); repeat_until_mark tac
  end.

(* apply tac on each hypothesis exactly once *)
Ltac for_each_hyp tac :=
  (* prepend the marker to the goal *)
  generalize (ltac_mark : ltac_Mark);
  repeat match goal with (* move all hypotheses from the context to the goal *)
  | [ H : _ |- _ ] => revert H
  end;
  (* successively move each hypothesis back into the context, applying tac on the way *)
  repeat_until_mark ltac:(fun _ => lazymatch goal with
                                   | [ |- ?F -> _ ] => intro; tac F
                                   | _ => intro
                                   end).

(* if an encountered hypothesis is a closed_qual, then invert it *)
Ltac try_invert_closed_qual F :=
  match F with
  | closed_qual _ _ _ _ =>
    match goal with
    | [ H : F |- _ ] => inversion H; subst
    end
  | _ => idtac
  end.

(* invert all the closed_qual hypotheses, exposing the bounds *)
Ltac closed_qual_invert := for_each_hyp try_invert_closed_qual.

Ltac set_simpl :=
  match goal with
  | [ |- context[union {}N ?s] ] => rewrite (@empty_union_left s); try set_simpl
  | [ |- context[union ?s {}N] ] => rewrite (@empty_union_right s); try set_simpl
  | [ H :  context[union {}N ?s] |- _ ] => rewrite (@empty_union_left s) in H; try set_simpl
  | [ H :  context[union ?s {}N] |- _ ] => rewrite (@empty_union_right s) in H; try set_simpl
  | [ |- context[inter {}N ?s] ] => rewrite (@inter_empty_left s); try set_simpl
  | [ |- context[inter ?s {}N] ] => rewrite (@inter_empty_right s); try set_simpl
  | [ H :  context[inter {}N ?s] |- _ ] => rewrite (@inter_empty_left s) in H; try set_simpl
  | [ H :  context[inter ?s {}N] |- _ ] => rewrite (@inter_empty_right s) in H; try set_simpl
  | [ |-  context[inter (singleton ?x) (singleton ?x)]  ] => rewrite (@inter_singleton_eq x); try set_simpl
  | [ |-  context[inter (singleton ?x) (singleton ?y)]  ] => rewrite (@inter_singleton_neq x y); try set_simpl
  | [ H : context[inter (singleton ?x) (singleton ?x)] |- _ ] => rewrite (@inter_singleton_eq x) in H; try set_simpl
  | [ H : context[inter (singleton ?x) (singleton ?y)] |- _ ] => rewrite (@inter_singleton_neq x y) in H; try set_simpl
  | [ |-  context[inter ?s (singleton ?y)] ] => erewrite (@bound_disjoint s y); eauto; try set_simpl
  | [ |- context[remove ?n (singleton ?n)] ] => rewrite (@remove_singleton_empty n); try set_simpl
  | [ H : context[remove ?n (singleton ?n)] |- _ ] => rewrite (@remove_singleton_empty n) in H; try set_simpl
  | [ |- context[remove ?n (singleton ?m)] ] => try (rewrite (@remove_singleton_inv n m); auto); try set_simpl
  | [ H : context[remove ?n (singleton ?m)] |- _ ] => try (rewrite (@remove_singleton_inv n m) in H; auto); try set_simpl
  | [ |- context[remove ?n {}N] ] => rewrite (@remove_empty n); try set_simpl
  | [ H : context[remove ?n {}N] |- _ ] => rewrite (@remove_empty n) in H; try set_simpl
  | [ H : context[remove ?n (union ?s1 ?s2)] |- _ ] => rewrite (@remove_union_dist n s1 s2) in H; try set_simpl
  | [ |- context[remove ?n (union ?s1 ?s2)] ] => rewrite (@remove_union_dist n s1 s2); try set_simpl
  end.

Ltac bound_simpl := try set_simpl;
  match goal with
  | [ |- context[bound (union _ _)] ] => rewrite union_bound_max'; try bound_simpl
  | [ |- context[bound (singleton _)] ] => rewrite bound_singleton; try bound_simpl
  | [ |- context[bound {}N] ] => rewrite bound_empty; try bound_simpl
  end.

Ltac closed_qual_solve :=
  match goal with
  | [ |- closed_qual _ _ _ ∅ ] => try solve [constructor; bound_simpl; lia]
  | [ |- closed_qual _ _ _ (_ ⋓ _) ] => try solve [apply closed_qual_qqplus; closed_qual_solve]
  | [ |- closed_qual _ _ _ (_ ⊔ _) ] => try solve [apply closed_qual_qlub; closed_qual_solve]
  | [ |- closed_qual _ _ _ (_ ⋒ _) ] => try solve [apply closed_qual_qqcap; closed_qual_solve]
  | [ |- closed_qual _ _ _ (_ ⊓ _) ] => try solve [apply closed_qual_qqcap; closed_qual_solve]
  | [ |- closed_qual _ _ _ (_ ⊕ _) ] => try solve [apply closed_qual_qplus; simpl; try lia; closed_qual_solve]
  | [ |- closed_qual _ _ _ (just_fv _) ] => try solve [apply just_fv_closed; simpl; lia | closed_qual_solve]
  | [ H : closed_qual _ _ _ ?q |- closed_qual _ _ _ ?q  ] => try solve [simpl in *; eapply closed_qual_monotone; eauto; try lia | (closed_qual_solve)]
  | [ H : has_type _ ?q _ _ _ _ |- closed_qual _ _ _ ?q  ] => try solve [apply has_type_closed in H; intuition; simpl in *; eapply closed_qual_monotone; eauto | (closed_qual_solve)]
  | [ H : has_type _ _ _ _ _ ?q |- closed_qual _ _ _ ?q  ] => try solve [apply has_type_closed in H; intuition; simpl in *; eapply closed_qual_monotone; eauto | (closed_qual_solve)]
  | [ H : stp _ _ _ ?q _ _ |- closed_qual _ _ _ ?q  ] => try solve [apply stp_closed in H; intuition; simpl in *; eapply closed_qual_monotone; eauto | (closed_qual_solve)]
  | [ H : stp _ _ _ _ _ ?q |- closed_qual _ _ _ ?q  ] => try solve [apply stp_closed in H; intuition; simpl in *; eapply closed_qual_monotone; eauto | (closed_qual_solve)]
  | [ H : qstp _ _ ?q _  |- closed_qual _ _ _ ?q  ] => try solve [apply qstp_closed in H; intuition; simpl in *; eapply closed_qual_monotone; eauto | (closed_qual_solve)]
  | [ H : qstp _ _ _ ?q  |- closed_qual _ _ _ ?q  ] => try solve [apply qstp_closed in H; intuition; simpl in *; eapply closed_qual_monotone; eauto | (closed_qual_solve)]
  | [ H1 : ?q ⊑ ?q', H2 : closed_qual _ _ _ ?q' |- closed_qual _ _ _ ?q ] => try solve [apply (closed_qual_sub H2 H1)]
  | [ |- closed_qual _ _ _ _ ] => try solve [simpl; constructor; bound_simpl; lia]
  end.

Ltac closed_ty_solve :=
  match goal with
  | [ H : closed_ty _ _ _ ?T |- closed_ty _ _ _ ?T  ] => try solve [simpl in *; eapply closed_ty_monotone; eauto; try lia | (closed_ty_solve)]
  | [ H : has_type _ _ _ _ ?T _ |- closed_ty _ _ _ ?T  ] => try solve [apply has_type_closed in H; intuition; simpl in *; eapply closed_ty_monotone; eauto | (closed_ty_solve)]
  | [ H : stp _ _ ?T _ _ _ |- closed_ty _ _ _ ?T  ] => try solve [apply stp_closed in H; intuition; simpl in *; eapply closed_ty_monotone; eauto | (closed_ty_solve)]
  | [ H : stp _ _ _ _ ?T _ |- closed_ty _ _ _ ?T  ] => try solve [apply stp_closed in H; intuition; simpl in *; eapply closed_ty_monotone; eauto | (closed_ty_solve)]
  | [ |- closed_ty _ _ _ (TFun _ _ _ _) ] => try solve [simpl; constructor; try closed_qual_solve; closed_ty_solve]
  | [ |- closed_ty _ _ _ (TRef _) ] => try solve [simpl; constructor; try closed_qual_solve; closed_ty_solve]
  | [ |- closed_ty _ _ _ _ ] => try solve [simpl; constructor; try closed_qual_solve]
  end.

Ltac closed_tm_solve :=
  match goal with
  | [ H : closed_tm _ _ _ ?T |- closed_tm _ _ _ ?T  ] => try solve [simpl in *; eapply closed_tm_monotone; eauto; try lia | (closed_tm_solve)]
  | [ H : has_type _ _ _ ?T _ _ |- closed_tm _ _ _ ?T  ] => try solve [apply has_type_closed in H; intuition; simpl in *; eapply closed_tm_monotone; eauto | (closed_tm_solve)]
  | [ |- closed_tm _ _ _ (tabs _) ] => try solve [simpl; constructor; try lia; closed_tm_solve]
  | [ |- closed_tm _ _ _ (tapp _) ] => try solve [simpl; constructor; try lia; closed_tm_solve]
  | [ |- closed_tm _ _ _ (tref _) ] => try solve [simpl; constructor; try lia; closed_tm_solve]
  | [ |- closed_tm _ _ _ (tderef _) ] => try solve [simpl; constructor; try lia; closed_tm_solve]
  | [ |- closed_tm _ _ _ (tassign _ _) ] => try solve [simpl; constructor; try lia; closed_tm_solve]
  | [ |- closed_tm _ _ _ _ ] => try solve [simpl; constructor; try lia; closed_tm_solve]
  end.

Lemma open_qual_empty_id : forall k q, [[ k ~> q]]ᵈ ∅ = ∅.
  intros. destruct q. compute. rewrite NatSetFacts.empty_b. auto.
Qed.

Lemma has_type_open_tm_id : forall {Γ φ Σ t T d k t'}, has_type Γ φ Σ t T d -> open_rec_tm k t' t = t.
  intros. apply has_type_closed in H. intuition. eapply closed_tm_open_id; eauto. lia.
Qed.

Lemma has_type_open_ty_id : forall {Γ φ Σ t T d k q}, has_type Γ φ Σ t T d -> open_rec_ty k q T = T.
  intros. apply has_type_closed in H. intuition. eapply closed_ty_open_id; eauto. lia.
Qed.

Lemma has_type_open_qual_id1 : forall {Γ φ Σ t T d k q}, has_type Γ φ Σ t T d -> open_qual k q φ = φ.
  intros. apply has_type_closed in H. intuition. eapply closed_qual_open_id; eauto. lia.
Qed.

Lemma has_type_open_qual_id2 : forall {Γ φ Σ t T d k q}, has_type Γ φ Σ t T d -> open_qual k q d = d.
  intros. apply has_type_closed in H. intuition. eapply closed_qual_open_id; eauto. lia.
Qed.

Lemma stp_open_ty_id1 : forall {Γ Σ T d S q k q'}, stp Γ Σ S q T d -> open_rec_ty k q' S = S.
  intros. apply stp_closed in H. intuition. eapply closed_ty_open_id; eauto. lia.
Qed.

Lemma stp_open_ty_id2 : forall {Γ Σ T d S q k q'}, stp Γ Σ S q T d -> open_rec_ty k q' T = T.
  intros. apply stp_closed in H. intuition. eapply closed_ty_open_id; eauto. lia.
Qed.

Lemma stp_open_qual_id1 : forall {Γ Σ T d S q k q'}, stp Γ Σ S q T d -> open_qual k q' q = q.
  intros. apply stp_closed in H. intuition. eapply closed_qual_open_id; eauto. lia.
Qed.

Lemma stp_open_qual_id2 : forall {Γ Σ T d S q k q'}, stp Γ Σ S q T d -> open_qual k q' d = d.
  intros. apply stp_closed in H. intuition. eapply closed_qual_open_id; eauto. lia.
Qed.

Lemma qstp_open_qual_id1 : forall {Γ Σ d q k q'}, qstp Γ Σ q d -> open_qual k q' q = q.
  intros. apply qstp_closed in H. intuition. eapply closed_qual_open_id; eauto. lia.
Qed.

Lemma qstp_open_qual_id2 : forall {Γ Σ d q k q'}, qstp Γ Σ q d -> open_qual k q' d = d.
  intros. apply qstp_closed in H. intuition. eapply closed_qual_open_id; eauto. lia.
Qed.

Lemma mem_singleton' : forall {n}, mem n (singleton n) = true.
  intros. rewrite mem_singleton. rewrite <- beq_nat_refl. auto.
Qed.

Lemma mem_singleton_neq : forall {m n}, m <> n -> mem n (singleton m) = false.
  intros. rewrite mem_singleton. rewrite Nat.eqb_neq. auto.
Qed.

Lemma unopen_subqual : forall {x q2 df l}, closed_qual 1 x l q2 -> closed_qual 0 x l df ->
  openq (just_fv x) q2 ⊑ df ⋓ just_fv x -> openq ∅ q2 ⊑ df.
  intros. unfold openq in *. destruct q2. destruct df. simpl in *.
  inversion H. subst. inversion H0. subst.
  apply bound_le_mem_false in H8, H11. rewrite <- NatSetFacts.not_mem_iff in H8, H11.
  destruct (NatSet.F.mem 0 t1) eqn:Hmem; simpl in *; intuition. all: fnsetdec.
Qed.

Ltac opening :=
  match goal with
  | [ H : closed_tm 0 _ _ ?t |- context[@open_tm' _ ?G ?t] ] => erewrite @closed_tm_open'_id with (t:=t); eauto; try opening
  | [ H : closed_ty 0 _ _ ?t |- context[@open_ty' _ _ ?t] ] => erewrite @closed_ty_open'_id with (T:=t); eauto; try opening
  | [ H : closed_qual 0 _ _ ?q |- context[@openq' _ ?G ?q] ] => erewrite @closed_qual_open'_id with (d:=q); eauto; try opening
  | [ |- context[@open_tm' ?T ?G (tvar (varB 0))] ] => rewrite (open_tm'_bv0 T G); try opening
  (* | [ |- context[@open_tm' ?T ?G (tvar (varB 1))] ] => rewrite (open_tm'_bv1 T G); try opening *)
  | [ |- context[@openq' ?T ?G (qset ?X (singleton 0) ?Y)] ] => rewrite (openq'_bv0 T G X Y); try opening
  (* | [ |- context[@openq' ?T ?G (qset ?X (singleton 1) ?Y)] ] => rewrite (openq'_bv1 T G X Y); try opening *)
  | [ |- context[@openq' _ _ _] ] => unfold openq'; unfold openq; try opening
  | [ |- context[@openq _ _] ] => unfold openq; try opening
  | [ |- context[@open_tm' _ _ _] ] => unfold open_tm'; try opening
  | [ |- context[@open_ty' _ _ _] ] => unfold open_ty'; unfold open_ty; try opening
  | [ |- context[@open_ty _ _] ] => unfold open_ty; try opening
  | [ |- context[open_qual _ _ (_ ⋓ _)] ] => rewrite open_qual_qqplus_dist; try opening
  | [ |- context[open_qual _ _ (_ ⊔ _)] ] => rewrite open_qual_qlub_dist; try opening
  | [ |- context[open_qual ?i ?d (just_fv ?x)] ] => rewrite (open_qual_just_fv i d x); try opening
  | [ |- context[open_qual ?i ?d (just_loc ?x)] ] => rewrite (open_qual_just_loc i d x); try opening
  | [ H : closed_qual 0 _ _ ?q |- context[open_qual _ _ ?q] ] => erewrite @closed_qual_open_id with (d:=q); eauto; try opening
  | [ H : has_type _ ?q _ _ _ _ |- context[open_qual _ _ ?q] ] => erewrite @has_type_open_qual_id1 with (φ:=q); eauto; try opening
  | [ H : has_type _ _ _ _ _ ?q |- context[open_qual _ _ ?q] ] => erewrite @has_type_open_qual_id2 with (d:=q); eauto; try opening
  | [ H : stp _ _ _ ?q _ _  |- context[open_qual _ _ ?q] ] => erewrite @stp_open_qual_id1 with (q:=q); eauto; try opening
  | [ H : stp _ _ _ _ _ ?q  |- context[open_qual _ _ ?q] ] => erewrite @stp_open_qual_id2 with (d:=q); eauto; try opening
  | [ H : qstp _ _ ?q _  |- context[open_qual _ _ ?q] ] => erewrite @qstp_open_qual_id1 with (q:=q); eauto; try opening
  | [ H : qstp _ _ _ ?q  |- context[open_qual _ _ ?q] ] => erewrite @qstp_open_qual_id2 with (d:=q); eauto; try opening
  | [ |- context[open_qual ?i ?d (just_bv ?i)] ] => try rewrite (@open_qual_just_bv i d); try opening
  | [ |- context[open_qual ?j ?d (just_bv ?i)] ] => try rewrite (@open_qual_just_bv_skip i j d); try lia; try opening
  | [ |- context[open_qual ?j ?d ∅] ] => try rewrite (@open_qual_empty_id j d); try lia; try opening
  (* | [ |- context[open_qual _ _ _] ] => simpl; try opening *)
  | [ H : closed_ty 0 _ _ ?x |- context[open_rec_ty _ _ ?x] ] => erewrite @closed_ty_open_id with (T:=x); eauto; try lia; try opening
  | [ H : has_type _ _ _ _ ?x _ |- context[open_rec_ty _ _ ?x] ] => erewrite @has_type_open_ty_id with (T:=x); eauto; try lia; try opening
  | [ H : stp _ _ ?x _ _ _ |- context[open_rec_ty _ _ ?x] ] => erewrite @stp_open_ty_id1 with (S:=x); eauto; try lia; try opening
  | [ H : stp _ _ _ _ ?x _ |- context[open_rec_ty _ _ ?x] ] => erewrite @stp_open_ty_id2 with (T:=x); eauto; try lia; try opening
  | [ |- context[open_rec_ty _ _ (TFun _ _ _ _)] ] => simpl; try opening
  | [ |- context[open_rec_ty _ _ (TRef _)] ] => simpl; try opening
  | [ |- context[open_rec_ty _ _ _] ] => simpl
  | [ H : closed_tm 0 _ _ ?x |- context[open_rec_tm _ _ ?x] ] => erewrite @closed_tm_open_id with (t:=x); eauto; try lia; try opening
  | [ H : has_type _ _ _ ?x _ _  |- context[open_rec_tm _ _ ?x] ] => erewrite @has_type_open_tm_id with (t:=x); eauto; try lia; try opening
  | [ |- context[open_rec_tm ?i ?x (tvar (varB ?i))] ] => rewrite (open_rec_tm_bv i x); try opening
  | [ |- context[open_rec_tm ?j ?x (tvar (varB ?i))] ] => rewrite (open_rec_tm_bv_skip j i x); try opening
  | [ |- context[open_rec_tm _ _ (tabs _)] ] => simpl; try opening
  | [ |- context[open_rec_tm _ _ (tapp _ _)] ] => simpl; try opening
  | [ |- context[open_rec_tm _ _ (tref _)] ] => simpl; try opening
  | [ |- context[open_rec_tm _ _ (tderef _)] ] => simpl; try opening
  | [ |- context[open_rec_tm _ _ (tassign _ _)] ] => simpl; try opening
  | [ |- context[open_rec_tm _ _ _] ] => simpl
  end.

Ltac qual_destruct :=
  match goal with
  | [ H : qual |- _ ] => destruct H; try clear H; try qual_destruct
  (* | [ H : closed_qual _ _ _ (qset _ _ _) |- _ ] => destruct H; try qual_destruct *)
  end.

Ltac subqual :=
  match goal with
  | [ |- openq _ _ ⊑ _ ] => try solve [try opening; try qual_destruct; simpl in *; try set_simpl; intuition; try fnsetdec]
  | [ |- _ ⊑ _ ] => try solve [try qual_destruct; simpl in *; try set_simpl; intuition; try fnsetdec]
  end.

Ltac set_bool_simpl :=
  match goal with
  |  [ |- context[mem ?n {}N] ] => rewrite (NatSetFacts.empty_b n); try set_bool_simpl
  |  [ |- context[mem ?n (singleton ?n)] ] => rewrite mem_singleton'; try set_bool_simpl
  |  [ |- context[mem ?n (singleton ?m)] ] => try (rewrite mem_singleton_neq; auto); try set_bool_simpl
  |  [ |- context[mem ?n (union ?s1 ?s2)]] => rewrite (NatSetProperties.FM.union_b s1 s2 n); try set_bool_simpl
  |  [ |- context[mem ?n (remove ?x ?s)]]  => rewrite (NatSetFacts.remove_b s x n); try set_bool_simpl
  |  [ |- context[NatSetFacts.eqb ?n ?x]]  => rewrite (@natset_eqb x n); try set_bool_simpl
  end.

Ltac lookup_solve :=
  match goal with
  | [ |- (if (beq_nat ?n ?n) then _ else _) = _ ] => rewrite <- beq_nat_refl; auto; try lookup_solve
  | [ |- (if (beq_nat ?n ?m) then _ else _) = _ ] =>
      let H := fresh "H" in
      destruct (beq_nat n m) eqn:H;
      try apply beq_nat_true in H;
      try apply beq_nat_false in H;
      try lia; lookup_solve
  | [ |- Some (_, _) = Some (_,_) ] => try solve [repeat f_equal; auto; qual_destruct; closed_qual_invert; simpl; f_equal; try set_simpl; try fnsetdec; try bound_simpl; try lia]
  end.

Ltac lookup :=
  match goal with
  | [ |- (@indexr _ _ _) = _ ] => try solve [lookup_solve | simpl; lookup_solve]
  end.

Ltac subtyping k :=
  match goal with
  | [ |- (stp _ _ _ _ _ _) ] => try solve [repeat (constructor ; k () )]
  end.

Ltac cleanup := repeat (try set_simpl; try opening; try set_bool_simpl; simpl).

Ltac crush :=
  try solve [closed_qual_solve];
  try solve [closed_ty_solve];
  try solve [closed_tm_solve];
  try solve [subqual];
  try solve [simpl; qdec];
  try solve [simpl; fnsetdec];
  try solve [lookup];
  try solve [subtyping ltac:(fun _ => repeat crush; try cleanup)];
  try solve intuition;
  try solve lia.

Ltac ccrush := repeat (crush; try cleanup).

Ltac unfold_open :=
  try unfold openq'; try unfold openq; try unfold open_tm'; try unfold open_ty'; try unfold open_ty.

Tactic Notation "unfold_open" "in" hyp(H) :=
  try unfold openq' in H; try unfold openq in H; try unfold open_tm' in H; try unfold open_ty' in H; try unfold open_ty in *.

(* Deal with cases where applying t_var might stumble. *)
Ltac T_VAR :=
  match goal with
  | [ |- has_type _ _ _ (tvar (varF ?x)) _ (_ ⊕ ?x) ] => apply t_var
  | [ |- has_type _ _ _ (tvar (varF ?x)) _ (qset (singleton ?x) {}N {}N) ] => replace (qset (singleton x) {}N {}N) with (∅ ⊕ x); try T_VAR
  | [ |- has_type _ _ _ (tvar (varF ?x)) _ (just_fv ?x) ] => rewrite <- qplus_empty; try T_VAR
  | [ |- has_type _ _ _ (tvar (varF ?x)) _ (qset (union ?s (singleton ?x)) {}N {}N) ] => replace (qset (union s (singleton x)) {}N {}N) with ((qset s {}N {}N) ⊕ x); try T_VAR
  | [ |- has_type _ _ _ (tvar (varF ?x)) _ _ ] => try solve [eapply t_var; ccrush]
  end.
