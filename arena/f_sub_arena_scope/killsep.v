Require Export Arith.EqNat.
Require Export PeanoNat.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Program.Equality.
Require Import Coq.Lists.List.
Require Import Psatz.
Require Import ZArith.
Require Import Coq.Arith.Compare_dec.
Import ListNotations.

Require Import vars.
Require Import env.
Require Import tactics.
Require Import nats.
Require Import qualifiers.
Require Import boolean.
Require Import lang.
Require Import qenv.
Require Import ops.
Require Import lemmas.

Import QualNotations.
Local Open Scope qualifiers.
Import OpeningNotations.
Local Open Scope opening.

Import SplicingNotations.
Local Open Scope splicing.
Import SubstitutionNotations.
Local Open Scope substitutions.



(*
  Defines the separation from a qualifier and killed locations or local locations
  In semantic typing, there is no freshness marker
*)
Definition kill_sep (ϰ : qual) (q : qual) : Prop :=
  q ⊓ ϰ ⊑↑ {♦}.



Lemma kill_sep_empty : forall (ϰ : qual),
  kill_sep ϰ ∅.
Proof.
  intros. unfold kill_sep. intros. Qcrush.
Qed.


Lemma kill_sep_empty_kill : forall d,
  kill_sep ∅ d.
Proof.
  intros. unfold kill_sep. Qcrush.
Qed.


Lemma kill_sep_var : forall (Σ : senv) (ϰ : qual) (v : nat),
  closed_Qual 0 0 (‖Σ‖) ϰ↑ ->
  kill_sep ϰ $!v.
Proof.
  intros. unfold kill_sep. Qcrush; subst. specialize (H0 v H4). lia.
Qed.

Lemma kill_sep_sub : forall (ϰ : qual) (q : qual) (q' : qual),
  q' ⊑↑ q -> kill_sep ϰ q ->
  kill_sep ϰ q'.
Proof.
  intros. unfold kill_sep in *. eapply Subq_trans. 2: eauto. apply Subq_qand_split. 2: Qcrush. auto.
Qed.

Lemma Qor_bound_rev : forall q1 q2 q3,
  (q1 ⊔ q2) ⊑↑ q3 -> q1 ⊑↑ q3 /\ q2 ⊑↑ q3.
Proof.
  intros. Qcrush.
Qed.

Lemma kill_sep_qor_rev : forall ϰ d1 d2,
  kill_sep ϰ (d1 ⊔ d2) -> kill_sep ϰ d1 /\ kill_sep ϰ d2.
Proof.
  intros. unfold kill_sep in *. rewrite qand_qor_dist_r in H. apply Qor_bound_rev in H; auto.
Qed.

Lemma kill_sep_qor : forall ϰ d1 d2,
  kill_sep ϰ d1 -> kill_sep ϰ d2 -> kill_sep ϰ (d1 ⊔ d2).
Proof.
  intros. unfold kill_sep in *. rewrite qand_qor_dist_r. apply Qor_bound; auto.
Qed.

(* This is equivalent to q_trans''_senv_freshv_id *)
Lemma q_trans''_fresh : forall E fuel,
  q_trans'' E {♦} fuel = {♦}.
Proof.
  intros. induction fuel; simpl; auto. replace (q_trans_one E {♦}) with ({♦}); auto. clear IHfuel. induction E; simpl; auto.
Qed.

Lemma kill_sep_fresh : forall (ϰ : qual),
  kill_sep ϰ {♦}.
Proof.
  intros. unfold kill_sep.  intros. Qcrush.
Qed.

Lemma kill_sep_sub_fresh : forall (ϰ : qual) (q : qual) (q' : qual),
  q' ⊑↑ q ⊔ {♦} -> kill_sep ϰ q ->
  kill_sep ϰ q'.
Proof.
  intros. cut (kill_sep ϰ (q ⊔ {♦})). intros. eapply kill_sep_sub; eauto. apply kill_sep_qor; auto. apply kill_sep_fresh.
Qed.

Lemma kill_sep_kill_sub : forall (ϰ : qual) (q : qual) (ϰ' : qual),
  ϰ' ⊑↑ ϰ -> kill_sep ϰ q ->
  kill_sep ϰ' q.
Proof.
  intros. unfold kill_sep in *. eapply Subq_trans. 2: eauto. apply Subq_qand_split. 2: Qcrush. Qcrush.
Qed.

Lemma kill_sep_kill_qor_rev : forall ϰ1 ϰ2 d,
  kill_sep (ϰ1 ⊔ ϰ2) (d) -> kill_sep ϰ1 d /\ kill_sep ϰ2 d.
Proof.
  intros. unfold kill_sep in *. rewrite qand_qor_dist_l in H. apply Qor_bound_rev in H; auto.
Qed.

Lemma kill_sep_kill_qor : forall ϰ1 ϰ2 d,
  kill_sep ϰ1 d -> kill_sep ϰ2 d -> kill_sep (ϰ1 ⊔ ϰ2) d.
Proof.
  intros. unfold kill_sep in *. rewrite qand_qor_dist_l. apply Qor_bound; auto.
Qed.

Lemma kill_sep_newkill : forall ϰ d l,
  kill_sep ϰ d ->
  kill_sep &! l d ->
  kill_sep (ϰ ⊔ &! l) d.
Proof.
  intros. unfold kill_sep in *. rewrite qand_qor_dist_l. apply Qor_bound; auto.
Qed.

Lemma kill_sep_outbound : forall (Σ:senv) ϰ l,
  l >= (‖Σ‖) -> closed_Qual 0 0 (‖Σ‖) ϰ↑ ->
  kill_sep ϰ &!l.
Proof.
  intros. unfold kill_sep.  Qcrush; subst. specialize (H3 l H5). lia.
Qed.

Lemma kill_sep_fresh_loc : forall (Σ : senv) ϰ,
  closed_Qual 0 0 (‖Σ‖) ϰ↑ -> kill_sep ϰ &! (‖ Σ ‖).
Proof.
  intros. unfold kill_sep. Qcrush; subst. specialize (H2 (‖Σ‖) H4). lia.
Qed.

Lemma kill_sep_newloc_kill : forall (Σ :senv) q,
  closed_Qual 0 0 (‖ Σ ‖) q ↑ ->
  kill_sep &!(‖ Σ ‖) q.
Proof.
  intros. unfold kill_sep. Qcrush. subst. specialize (H2 (‖Σ‖) H3). lia.
Qed.


Lemma Qand_bound_sub : forall d1 d2 d,
  d1 ⊓ d2 ⊑↑ d ->
  forall {d1' d2'}, d1' ⊑↑ d1 -> d2' ⊑↑ d2 ->
  d1' ⊓ d2' ⊑↑ d.
Proof.
  intros. Qcrush.
Qed.

Lemma kill_sep_qor_fresh : forall ϰ d,
  kill_sep ϰ (d ⊔ {♦}) -> kill_sep ϰ d.
Proof.
  intros. unfold kill_sep in *.  rewrite qand_qor_dist_r in H. apply Qor_bound_rev in H. destruct H; auto.
Qed.

Lemma kill_sep_kill_qor_fresh : forall ϰ d,
  kill_sep (ϰ ⊔ {♦}) (d) -> kill_sep ϰ d.
Proof.
  intros. unfold kill_sep in *.  rewrite qand_qor_dist_l in H. apply Qor_bound_rev in H. destruct H; auto.
Qed.


Lemma kill_sep_fresh_irrlevance: forall ϰ d,
  kill_sep ϰ d ->
  kill_sep ϰ (false, qfvs d, qbvs d, qlocs d).
Proof.
  intros. eapply kill_sep_sub with (q:=d ⊔ {♦}). Qcrush. unfold kill_sep in *. rewrite qand_qor_dist_r. apply Qor_bound; auto. Qcrush.
Qed.

Lemma kill_sep_in : forall ϰ d l,
  kill_sep ϰ d -> l ∈ₗ d ->
  kill_sep ϰ &!l.
Proof.
  intros. assert (d = (d ⊔ &!l)). clear H. apply Q_lift_eq. Qcrush; subst; auto. rewrite H1 in H. clear H1. apply kill_sep_qor_rev in H; intuition.
Qed.

Lemma kill_sep_not_in : forall ϰ d,
  kill_sep ϰ d ->
  forall l, l ∈ₗ ϰ -> ~l ∈ₗ d.
Proof.
  intros. unfold not in *; intros. Qcrush. unfold kill_sep in H. assert (d ⊓ ϰ ⊑↑ {♦}). { eapply Qand_bound_sub. eauto. Qcrush. Qcrush. } clear H. Qcrush. eapply (H5 l); eauto.
Qed.


Lemma kill_sep_only_locs : forall ϰ d L,
  closed_Qual 0 0 (L) ϰ↑ ->
  kill_sep ϰ d <-> kill_sep ϰ (false, n_empty, n_empty, qlocs d).
Proof.
  intros. replace d with ( (qfresh d, qfvs d, qbvs d, n_empty) ⊔ (false, n_empty, n_empty, qlocs d) ) at 1. unfold kill_sep.
  simpl.
  split; intros.
    rewrite qand_qor_dist_r in H0. apply Qor_bound_rev in H0; destruct H0; auto.
    rewrite qand_qor_dist_r. apply Qor_bound; auto. clear - H. Qcrush. specialize (H0 x H4); lia. specialize (H x H4); lia.
  clear. Qcrush.
  apply Q_lift_eq. Qcrush.
Qed.


Lemma kill_sep_open_empty : forall (Σ :senv) ϰ d k,
  closed_Qual 0 0 (‖Σ‖) ϰ↑ ->
  kill_sep ϰ (d) ->
  kill_sep ϰ ([[k ~> ∅ ]]ᵈ d).
Proof.
  intros. qual_destruct d. unfold openq. unfold_q. destruct (bvs k); simpl. rewrite kill_sep_only_locs; simpl. 2: eauto. rewrite kill_sep_only_locs in H0; eauto. simpl in H0. replace (n_or lcs n_empty) with lcs. auto.
  apply N_lift_eq; intros. split. Qcrush. Qcrush. auto.
Qed.

Lemma kill_sep_open_empty' : forall (Σ :senv) ϰ d,
  closed_Qual 0 0 (‖Σ‖) ϰ↑ ->
  kill_sep ϰ (d) ->
  kill_sep ϰ (d <~ᵈ ∅ ; ∅).
Proof.
  intros. unfold openq. eapply kill_sep_open_empty; eauto. eapply kill_sep_open_empty; eauto.
Qed.


Lemma kill_sep_qqplus_bound: forall ϰ d1 d2,
  kill_sep ϰ d1 -> kill_sep ϰ d2 ->
  kill_sep ϰ (d1 ⋓ d2).
Proof.
  intros. eapply kill_sep_sub with (q:=d1⊔d2). eapply Qqplus_bound; auto. apply kill_sep_qor; auto.
Qed.


(* remove l from the target qualifier
  an alternative to qdiff
*)
Fixpoint q_remove' (Σ : senv) (k : loc) (q : qual) (fuel : nat) : qual :=
  match fuel with
  | 0 => ∅
  | S x => if (qlocs q (x)) && negb (qlocs (&!x) k)  (* x in q, and k notin x* *)
      then qor (q_remove' Σ k q x) (&!x)
      else (q_remove' Σ k q x)
  end.

Definition q_remove (Σ : senv) (k : loc) (q : qual) : qual :=
  q_remove' Σ k q (‖Σ‖) ⊔ (qfresh q, qfvs q, qbvs q, n_empty).
#[global] Hint Unfold q_remove : core.


Lemma kill_sep_breflect : forall k l,
  kill_sep &!k &!l <-> qlocs (&!l) k = false.
Proof.
  split.
  intros. unfold kill_sep in H. remember (&! l) as q. clear Heqq. Qcrush. specialize (H3 k). qual_destruct q; simpl. simpl in H3. clear - H3. unfold N_lift in H3. destruct (lcs k); auto.
  intros. unfold kill_sep. remember (&! l) as q. clear Heqq. Qcrush. qual_destruct q; simpl. simpl in *; subst. assert (lcs k = true). Qcrush. rewrite H in H0. inversion H0.
Qed.

Lemma q_remove_fresh : forall Σ l,
  q_remove Σ l {♦} = {♦}.
Proof.
  intros. assert (forall fuel, q_remove' Σ l {♦} (fuel) = ∅).
  induction fuel; simpl; auto.
  unfold q_remove; simpl. rewrite H. Qcrush.
Qed.

Lemma q_remove'_in : forall (Σ : senv) (k : loc) (l : loc) (q : qual) (fuel : nat),
  l ∈ₗ q -> l < fuel -> qlocs ((&!l)) k = false -> l ∈ₗ (q_remove' Σ k q fuel).
Proof.
  intros. induction fuel; simpl. simpl. Qcrush.
  simpl in *. bdestruct (l =? fuel); subst.
  + clear IHfuel. assert ((qlocs q) (fuel) = true). Qcrush. rewrite H2. rewrite H1. simpl. Qcrush.
  + assert (l < fuel). lia. specialize (IHfuel H3). destruct (qlocs q fuel && negb (n_one fuel k)). Qcrush. Qcrush.
Qed.

Lemma q_remove'_onlylocs : forall Σ l d fuel,
  q_remove' Σ l d fuel = (false, n_empty, n_empty, qlocs (q_remove' Σ l d fuel)).
Proof.
  induction fuel; simpl. auto.
  destruct (qlocs d fuel && negb (n_one fuel l)); auto. rewrite IHfuel. simpl. clear IHfuel. Qcrush.
Qed.


Lemma q_remove_in : forall (Σ : senv) (k : loc) (l : loc) (q : qual),
  l ∈ₗ q -> l < ‖Σ‖ -> kill_sep &!k &!l -> l ∈ₗ (q_remove Σ k q).
Proof.
  intros. unfold q_remove. apply kill_sep_breflect in H1. eapply q_remove'_in with (Σ := Σ) in H1; eauto. Qcrush.
Qed.

Lemma q_remove'_in_sep : forall (Σ : senv) (k : loc) (l : loc) (q : qual) (fuel : nat),
  l ∈ₗ (q_remove' Σ k q fuel) -> qlocs ((&!l)) k = false.
Proof.
  intros. unfold q_remove. induction fuel; simpl. Qcrush.
  simpl in *. bdestruct (l =? fuel); subst.
  + destruct (qlocs q fuel && negb (n_one fuel k)) eqn:Hb. apply andb_true_iff in Hb; destruct Hb. apply negb_true_iff in H1; auto. auto.
  + remember ((q_remove' Σ k q fuel)) as qq. clear Heqqq. destruct (qlocs q fuel && negb (n_one fuel k)). Qcrush. Qcrush.
Qed.

Lemma q_remove_in_sep : forall (Σ : senv) (k : loc) (l : loc) (q : qual),
  l ∈ₗ (q_remove Σ k q) -> kill_sep &!k &!l.
Proof.
  intros. unfold q_remove. apply kill_sep_breflect; auto. unfold q_remove in H. eapply q_remove'_in_sep; eauto. Qcrush. eauto.
Qed.



(* this is just unfold N_lift *)
Lemma qlocs_lift_rev : forall (q : qual) x,
  N_lift (qlocs q) x -> qlocs q x = true .
Proof.
  intros. intros. Qcrush.
Qed.
Lemma qlocs_lift : forall (q : qual) x,
  qlocs q x = true -> N_lift (qlocs q) x.
Proof.
  intros. intros. Qcrush.
Qed.


Lemma q_remove'_smaller : forall Σ l q fuel,
  q_remove' Σ l q fuel ⊑↑ (false, n_empty, n_empty, (qlocs q)).
Proof.
  intros. induction fuel. simpl. Qcrush.
  simpl. destruct (qlocs q fuel && negb (n_one fuel l)) eqn:Hb; auto.
  apply andb_true_iff in Hb. destruct Hb. apply qlocs_lift in H. clear H0. apply Qor_bound; auto. clear IHfuel. Qcrush; subst; auto.
Qed.

Lemma q_remove_smaller : forall Σ l q,
  q_remove Σ l q ⊑↑ q.
Proof.
  intros. unfold q_remove. specialize (q_remove'_smaller Σ l q (‖Σ‖)); intros. remember (q_remove' Σ l q (‖ Σ ‖)) as q'. clear Heqq'. Qcrush.
  specialize (H x H4). lia. specialize (H1 x H4). lia.
Qed.


Lemma locs_diff_exists : forall d q l, d ⊑↑ q ⊔ &!l -> N_lift (qlocs d) l ->
  exists d', d = (d' ⊔ &!l) /\ d' ⊑↑ q.
Proof.
  intros. qual_destruct d. qual_destruct q. Qcrush. exists (fr, fvs, bvs, n_diff lcs (n_one l)). unfold qor; simpl. Qcrush. apply Q_lift_eq; Qcrush. bdestruct (x=?l). right; auto. left. split; auto. subst; auto.
  specialize (H x H3); Qcrush. specialize (H2 x H3); Qcrush. specialize (H4 x H5); Qcrush.
Qed.

Lemma subqual_exists : forall φ φ', φ ⊑↑ φ' -> exists dif, φ' = (φ ⊔ dif).
Proof.
  intros. Qcrush. exists (qdiff φ' φ). qual_destruct φ; qual_destruct φ'; simpl in *.   apply Q_lift_eq. Qcrush.
  destruct (fr) eqn:E. left; auto. right; split; auto.
  destruct (fvs x) eqn:E. left; auto. right; split; auto. unfold N_lift. intros. rewrite E in H4. lia.
  destruct (bvs x) eqn:E. left; auto. right; split; auto. unfold N_lift. intros. rewrite E in H4. lia.
  destruct (lcs x) eqn:E. left; auto. right; split; auto. unfold N_lift. intros. rewrite E in H4. lia.
Qed.


Lemma q_remove'_sub_sep : forall (Σ : senv) (k : loc) (d : qual) (q : qual) (fuel : nat),
  d ⊑↑ (q_remove' Σ k q fuel) -> kill_sep &!k d.
Proof.
  intros. unfold q_remove. generalize dependent d. induction fuel; intros; simpl. unfold kill_sep. unfold q_remove' in H. eapply Qand_bound_sub with (d1:=∅) (d2:=&!k). Qcrush.  Qcrush. Qcrush.
  simpl in *. destruct (qlocs q fuel && negb (n_one fuel k)) eqn:Hb. apply andb_true_iff in Hb; destruct Hb. apply negb_true_iff in H1; auto. auto.
  + destruct (qlocs d fuel) eqn:Eqd. apply qlocs_lift in Eqd. specialize (locs_diff_exists d (q_remove' Σ k q fuel) fuel H Eqd). intros. destruct H2 as [d' [? ?]]. subst. apply kill_sep_qor; auto. apply kill_sep_breflect; auto.
    assert (~N_lift (qlocs d) fuel). clear - Eqd. Qcrush. apply qlocs_lift_rev in H. qual_destruct d; simpl in *.  rewrite H in Eqd; inversion Eqd.
    assert (d ⊑↑ q_remove' Σ k q fuel). remember (q_remove' Σ k q fuel) as q'. clear - H2 H. Qcrush. specialize (H x H3). Qcrush. specialize (H1 x H3); Qcrush. specialize (H4 x H3). destruct H4; auto. subst. specialize (H2 H3). Qcrush.
    apply IHfuel; auto.
  + apply IHfuel; auto.
Qed.



Lemma q_remove_sub_sep : forall (Σ : senv) (k : loc) (d : qual) (q : qual),
  d ⊑↑ (q_remove Σ k q) -> kill_sep &!k d.
Proof.
  intros. unfold q_remove in H. eapply kill_sep_only_locs with (L:=(S k)). clear. Qcrush.
  replace d with ((false, n_empty, n_empty, qlocs d) ⊔ (qfresh d, qfvs d, qbvs d, n_empty)) in H. assert ((false, n_empty, n_empty, qlocs d) ⊑↑ q_remove' Σ k q (‖ Σ ‖)). rewrite q_remove'_onlylocs in *; simpl in *. Qcrush. specialize (H3 x). do 2 rewrite or_false_elim in H3. auto.
  eapply q_remove'_sub_sep; eauto.
  qual_destruct d; simpl. clear H. apply Q_lift_eq; simpl. Qcrush.
Qed.


Lemma subqual_cumulate: forall d q L,
  closed_Qual 0 0 L d↑ ->
  (forall l, l ∈ₗ d -> l ∈ₗ q) ->
  d ⊑↑ q ⊔ {♦}.
Proof.
  intros. Qcrush. specialize (H1 x H2). lia. specialize (H x H2). lia.
Qed.

(* may prove alternatively like other sub lemmas, to get a more precise one *)
Lemma q_remove_sub' : forall (Σ : senv) (k : loc) (d : qual) (q : qual),
  closed_Qual 0 0 (‖Σ‖) q↑ ->
  d ⊑↑ q ⊔ {♦} -> kill_sep &!k d -> d ⊑↑ (q_remove Σ k q) ⊔ {♦}.
Proof.
   intros. assert (closed_Qual 0 0 (‖ Σ ‖) (q ⊔ {♦}) ↑). apply closed_Qual_qor. Qcrush. Qcrush. eapply subqual_cumulate; eauto.  eauto. intros. eapply q_remove_in; auto. Qcrush. specialize (H11 l H3). Qcrush. Qcrush. eapply kill_sep_in; eauto.
Qed.

Lemma q_remove_sub : forall (Σ : senv) (k : loc) (d : qual) (q : qual),
  closed_Qual 0 0 (‖Σ‖) q↑ ->
  d ⊑↑ q -> kill_sep &!k d -> d ⊑↑ (q_remove Σ k q).
Proof.
  intros. unfold q_remove. specialize (q_remove_in Σ k) with (q:=q); intros. unfold q_remove in H2. remember (q_remove' Σ k q (‖ Σ ‖)) as q'. clear Heqq'.
  specialize (kill_sep_in &!k d); intros. Qcrush.
Qed.



Lemma q_remove_id : forall (Σ : senv) (k : loc) (q : qual),
  closed_Qual 0 0 (‖Σ‖) q↑ ->
  kill_sep &!k q -> q_remove Σ (k) q = q.
Proof.
  intros. specialize (q_remove_smaller Σ k q). eapply (q_remove_sub Σ k q q) in H; auto. intros. clear H0. apply Q_lift_eq. Qcrush.
Qed.


Lemma q_remove'_or_dist : forall (Σ : senv) (k : loc) (d1 : qual) (d2 : qual) fuel,
  (q_remove' Σ k (d1 ⊔ d2) fuel) = ((q_remove' Σ k d1 fuel) ⊔ (q_remove' Σ k d2 fuel)).
Proof.
  intros. induction fuel; simpl. Qcrush. replace (n_or (qlocs d1) (qlocs d2) fuel) with ((qlocs d1) fuel || (qlocs d2) fuel) by auto.
  destruct (negb (n_one fuel k)); destruct (qlocs d1 fuel); destruct (qlocs d2 fuel); simpl; auto; rewrite IHfuel; clear IHfuel.
  1-3: remember (q_remove' Σ k d1 fuel) as d1'; remember (q_remove' Σ k d2 fuel) as d2'; clear Heqd1'; clear Heqd2'.
  1-3: apply Q_lift_eq. Qcrush. Qcrush. Qcrush.
Qed.

Lemma q_remove_or_dist : forall (Σ : senv) (k : loc) (d1 : qual) (d2 : qual),
  (q_remove Σ k (d1 ⊔ d2)) = ((q_remove Σ k d1) ⊔ (q_remove Σ k d2)).
Proof.
  intros. unfold q_remove. specialize (q_remove'_or_dist Σ k d1 d2 (‖Σ‖)); intros. rewrite H. clear H. apply Q_lift_eq. Qcrush.
Qed.


Lemma q_remove'_hit : forall (Σ : senv) (k : loc) fuel,
  q_remove' Σ k (&!k) fuel = ∅.
Proof.
  induction fuel; simpl; auto. rewrite IHfuel. clear IHfuel. unfold n_one at 1. bdestruct (fuel =? k); subst.
  assert (N_lift (n_one k) k). Qcrush.
  unfold N_lift in H. rewrite H. simpl; auto. simpl; auto.
Qed.



Lemma q_remove_withref : forall (Σ : senv) (k : loc) (T:ty) (d : qual) (q : qual),
  wf_senv Σ ->
  closed_Qual 0 0 (‖Σ‖) d↑ -> closed_Qual 0 0 (‖Σ‖) q↑ ->
  q_remove ([(T,d)] :: Σ) (‖Σ‖) (q ⊔ &! (‖Σ‖)) = q.
Proof.
  intros. rewrite q_remove_or_dist. rewrite q_remove_id.
  replace (q_remove ([(T, d)] :: Σ) (‖ Σ ‖) &! (‖ Σ ‖)) with (∅). rewrite qor_empty_right; auto. unfold q_remove. rewrite q_remove'_hit. Qcrush.
  simpl. eapply closed_Qual_monotone; eauto.
  unfold kill_sep. clear H0. Qcrush. subst. specialize (H3 (‖Σ‖) H4). lia.
Qed.


Lemma q_remove_sep : forall (Σ : senv) (k : loc) (q : qual),
  kill_sep &!k (q_remove Σ k q).
Proof.
  intros. eapply q_remove_sub_sep; eauto.
Qed.