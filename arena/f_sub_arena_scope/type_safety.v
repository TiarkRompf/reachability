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
Require Import killsep.
Require Import rules.
Require Import weaken_narrow.
Require Import vtp_subst.

Import QualNotations.
Local Open Scope qualifiers.
Import OpeningNotations.
Local Open Scope opening.

Import SplicingNotations.
Local Open Scope splicing.
Import SubstitutionNotations.
Local Open Scope substitutions.


(* disjointq Σ Σ' q q' (in symbols: Σ → Σ' ∋ q ⊕ q') is an invariant propagated through the type safety proof.
   Given a reduction step starting in store typing Σ and resulting in Σ', and a qualifier q, then
   Σ → Σ' ∋ q ⊕ q' specifies that the step has increased q by q' (e.g., from allocation effects).
   q' is either empty (no observable change to q), or q' = (q'' ⊔ &!‖Σ‖) for some q'' where q'' ⊑ q.
   That is, q increases at most by a single fresh store location (&!‖Σ‖, the next free address), and this
   new location stores a value that is already aliased by q. *)
(* remove q here does not make any difference in the shallow model *)
Inductive disjointq (Σ Σ' : senv) : qual -> qual -> Prop :=
| disj_bot : forall q,
    disjointq Σ Σ' q ∅
| disj_loc : forall T q q',
    closed_ty 0 0 (‖Σ‖) T ->
    closed_Qual 0 0 (‖Σ‖) q↑ ->
    ♦∉ q ->
    Σ' = [(T,q)] :: Σ ->
    disjointq Σ Σ' q' (&!‖Σ‖)
.
Arguments disj_loc { Σ Σ' }.
#[global] Hint Constructors disjointq : core.
Notation " S → T ∋ q ⊕ q'" := (disjointq S T q q') (at level 10).



Lemma qqcap_fresh_r : forall {d1 df f Σ Σ' d'},
    closed_Qual 0 f (‖Σ‖) d1↑ -> closed_Qual 0 f (‖Σ‖) df↑ ->
    Σ → Σ' ∋ df ⊕ d' -> (d1 ⋒ df) = (d1 ⋒ (df ⋓ d')).
  intros. qual_destruct d1. qual_destruct df.
  inversion H1; subst.
  - unfold qqplus. destruct fr0; simpl. rewrite qor_empty_right. auto. auto.
  - assert (Hfresh: ~ N_lift lcs0 (‖Σ‖)). { inversion H0. unfold_N. unfold_q. intuition. eauto. }
     unfold_q. destruct fr0; auto; simpl. apply Q_lift_eq. Qcrush. exfalso; eauto.
Qed.

Lemma qqcap_fresh_l : forall {d1 df f Σ Σ' d'},
    closed_Qual 0 f (‖Σ‖) d1↑ -> closed_Qual 0 f (‖Σ‖) df↑ ->
    Σ → Σ' ∋ d1 ⊕ d' -> (d1 ⋒ df) = ((d1 ⋓ d') ⋒ df).
  intros. qual_destruct df. qual_destruct d1.
  inversion H1; subst.
  - unfold qqplus. destruct fr0; simpl. rewrite qor_empty_right. auto. auto.
  - assert (Hfresh: ~ N_lift lcs0 (‖Σ‖)). { inversion H0. unfold_N. unfold_Q. intuition. eauto. }
     unfold_q. destruct fr0; auto; simpl. apply Q_lift_eq. Qcrush. exfalso; eauto.
Qed.


Lemma disjointq_ndom : forall {X} s (a:X) x, x <= ‖s‖ -> N_lift (n_dom (a :: s)) x.
Proof.
  intros. unfold n_dom, N_lift. simpl. apply Nat.ltb_lt. lia.
Qed.

Lemma disjointq_Qdom : forall {Σ Σ' d d'}, Σ → Σ' ∋ d ⊕ d' -> d' ⊑↑ qdom Σ'.
intros. inversion H; subst; Qcrush; subst.  apply disjointq_ndom; auto.
Qed.
#[global] Hint Resolve disjointq_Qdom : core.

Lemma disjointq_qdom : forall {Σ Σ' d d'}, Σ → Σ' ∋ d ⊕ d' -> d' ⊑ qdom Σ'.
intros. apply Q_lift_subq. inversion H; subst; Qcrush; subst; eauto using Nat.lt_lt_succ_r. apply disjointq_ndom; auto.
Qed.
#[global] Hint Resolve disjointq_qdom : core.

Lemma disjointq_Qdom' : forall {Σ Σ' d d'}, Σ → Σ' ∋ d ⊕ d' -> {♦} ⊔ d' ⊑↑ qdom Σ'.
intros. inversion H; subst; Qcrush; subst; eauto using Nat.lt_lt_succ_r. apply disjointq_ndom; auto.
Qed.
#[global] Hint Resolve disjointq_Qdom' : core.

Lemma disjointq_qdom' : forall {Σ Σ' d d'}, Σ → Σ' ∋ d ⊕ d' -> {♦} ⊔ d' ⊑ qdom Σ'.
intros. apply Q_lift_subq. inversion H; subst; Qcrush; subst; eauto using Nat.lt_lt_succ_r. apply disjointq_ndom; auto.
Qed.
#[global] Hint Resolve disjointq_qdom' : core.

Lemma disjointq_closed : forall {Σ Σ' d d'}, Σ → Σ' ∋ d ⊕ d' -> closed_Qual 0 0 (‖Σ'‖) d'↑.
  intros. inversion H; subst; auto. simpl. eapply closed_qual_monotone; eauto.
Qed.
#[global] Hint Resolve disjointq_closed : core.

Lemma disjointq_scale : forall {Σ Σ' d d'}, Σ → Σ' ∋ d ⊕ d' -> forall {d''}, d ⊑↑ d'' -> Σ → Σ' ∋ d'' ⊕ d'.
  intros. inversion H; subst. auto. econstructor; eauto using Subq_trans.
Qed.
#[global] Hint Resolve disjointq_scale : core.

Lemma qdom_fresh : forall {A} {Σ : list A}, {♦} ⊑↑ qdom Σ.
  intros. Qcrush.
Qed.
#[global] Hint Resolve qdom_fresh : core.

(* well-typed values belonging to each type *)

Lemma vtp_canonical_form_loc : forall {Σ ϰ φ t T q d},
   vtp Σ ϰ φ t (TRef q T) d -> value t -> exists (l : loc) (o : offset), t = tloc l o.
Proof. intros. remember (TRef q T) as R. remember t as tt. generalize dependent T.
  induction H; intuition; try discriminate; inversion H0; subst. exists l. exists o. intuition.
Qed.

Lemma vtp_canonical_form_lam : forall {Σ ϰ φ t T1 T2 d1 d2 df},
    vtp Σ ϰ φ t (TFun d1 d2 T1 T2) df -> value t -> exists (t' : tm), t = tabs t'.
Proof. intros Σ ϰ φ t T1 T2 d1 d2 df H. remember (TFun d1 d2 T1 T2) as T.
       generalize dependent d1. generalize dependent d2. generalize dependent T1. generalize dependent T2.
       induction H; intuition; try discriminate; inversion H0; subst. exists t. intuition.
Qed.



Lemma stp_set_not_fresh : forall {d1 T Γ Σ}, closed_ty 0 (‖Γ‖) (‖Σ‖) T -> closed_Qual 0 (‖Γ‖) (‖Σ‖) d1↑ -> stp Γ Σ T (false, (qfvs d1), (qbvs d1), (qlocs d1)) T d1.
  intros. apply stp_refl; auto. destruct H0; auto. destruct H1. constructor; auto. Qcrush. Qcrush.
Qed.
#[global] Hint Resolve stp_set_not_fresh : core.


Lemma open_qual_not_free : forall {k q}, [[k ~> ∅ ]]ᵈ q = q -> forall {q'}, [[k ~> q' ]]ᵈ q = q.
  intros. qual_destruct q. qual_destruct q'. unfold_q.
  ndestruct (bvs k); auto.
  exfalso. inversion H. rewrite <- H4 in H0. Qcrush.
Qed.

Lemma not_free_prop1 : forall {T k}, not_free k T -> forall {U d}, ([[k ~> U ~ d ]]ᵀ T) = T.
  unfold not_free. induction T; intros; try destruct v; try solve [simpl; auto].
  simpl in *. destruct (k =? i) eqn:Heqki; intuition. inversion H.
  auto. simpl in H. inversion H.
  rewrite H1, H2, H3, H4. simpl. rewrite IHT1; auto. rewrite IHT2; auto.
  repeat rewrite open_qual_not_free; auto.
  simpl in H. inversion H.
  rewrite H1, H2, H3, H4. simpl. rewrite IHT1; auto. rewrite IHT2; auto.
  repeat rewrite open_qual_not_free; auto.
  simpl in H. inversion H. rewrite H1, H2. simpl. rewrite IHT; auto.
  rewrite open_qual_not_free; auto.
Qed.

Lemma not_free_prop2 : forall {T k}, not_free k T -> forall {U d V d'}, ([[k ~> U ~ d ]]ᵀ T) = ([[k ~> V ~ d' ]]ᵀ T).
  intros. repeat rewrite not_free_prop1; auto.
Qed.
#[global] Hint Resolve not_free_prop2 : core.

Lemma not_free_prop3 : forall {T k}, not_free k T -> forall {f l}, closed_ty (S k) f l T -> closed_ty k f l T.
  intros. rewrite <- (@not_free_prop1 _ _ H TUnit ∅). eapply closed_ty_open'; eauto.
Qed.



(* Main results: type soundness & preservation of separation *)

(* summarizing the design choice
  the problem of original design: we cannot represent existing but not dereferencable locations. That is, allowing vtp to type in a smaller flt requires the inner qualifier q to separate from l, which transitively require no mentioning.
    i.e. we should allow mentioning but only forbid use. In reflection, the t_deref requires q in φ, but t_loc does not, so we can permit some kind of loc mentioning, but not dereferencing
  Reflected in CtxOK, we only exactly kill l, which is a shallow kill. For these locs still in φ, they're not directly killed (cells not None), and we're able to mention them or dereference them, but we can only mention l which is exactly killed.
  Namely: l' = new Ref(l) whose inner qualifier is l. We should be able to mention this loc, but not dereference (or break qualifier separation).
  So the invariance should be: forall l ∈ φ, there exists a vtp type only if q is smaller than φ, otherwise we don't provide vtp witness (as it's not dereferenceable)
*)
Definition CtxOK (Γ : tenv) (φ : qual) (Σ : senv) (ϰ : qual) (σ : store) : Prop :=
  qdom' σ ⊑↑ qdom Σ /\ ‖ σ ‖ = ‖ Σ ‖ /\
  (* φ ⊑↑ (qdom' σ) /\  *)  φ ⊑↑ (qdom Σ) /\
  closed_Qual 0 0 (‖Σ‖) ϰ↑ /\
  kill_sep ϰ φ /\   (* observation must separate from kill *)
  forall l o cty T q,
  (l ∈ₗ ϰ -> indexr l σ = Some None) /\ (~(l∈ₗ ϰ) ->(* not yet killed locs *)
    l ∈ₗ φ ->
    indexr l Σ = Some cty ->
    (exists ctm, (indexr l σ = Some (Some ctm) /\ (‖ cty ‖) = (‖ ctm ‖)) /\
    (indexr o cty = Some (T,q) ->  (exists v, indexr o ctm = Some v /\
      value v /\ (q ⊑↑ φ -> vtp Σ ϰ φ v T q))))
      (* we only provide vtp for dereferencable locs *)
  )
.


Lemma CtxOK_weaken_store : forall {Σ ϰ σ T t d φ},
    CtxOK [] φ Σ ϰ σ ->
    value t ->
    vtp Σ ϰ φ t T d ->
    wf_senv Σ ->
    CtxOK [] (φ) ([(T, d)] :: Σ) ϰ (Some [t] :: σ).
Proof.
  unfold CtxOK in *. intros.
  destruct H as [Hdom [Hlen [Hflt [Hclϰ [Hwf H]]]]].
  split. clear - Hdom Hlen. Qcrush. unfold N_lift, n_dom', n_dom in *. apply andb_true_iff in H. destruct H. simpl in H. simpl. rewrite <- Hlen. auto.
  split. simpl. lia.
  split. clear - Hlen Hflt. Qcrush. simpl. specialize (H3 x H2). unfold N_lift, n_dom in *. apply Nat.ltb_lt in H3. apply Nat.ltb_lt. simpl. lia.
  split. simpl. eapply closed_Qual_monotone; eauto.
  split. auto.
  intros. specialize (H l o cty T0 q). destruct H as [Hk He]. split.
  intros. specialize (Hk H). assert (l < ‖σ‖). { apply indexr_var_some' in Hk; auto. } rewrite indexr_skip; auto. lia.
  intros. specialize (He H H3). bdestruct (l =? ‖σ‖); subst.
  - rewrite Hlen in H4. rewrite indexr_head in H4. inversion H4; subst.
    exists [t]. split; auto. split; auto. rewrite indexr_head; auto.
      intros. assert (o = 0). apply indexr_var_some' in H5; simpl in H5; lia. subst. exists t. split; auto. split; auto. intros. simpl in H5. inversion H5; subst. eapply vtp_weaken_store; eauto.
  - assert (l < ‖σ‖). {apply indexr_var_some' in H4; simpl in H4. lia. }
    rewrite indexr_skip. rewrite indexr_skip in H4. specialize (He H4). destruct He as [ctm ?]. intuition.
    exists ctm. split; auto. intros. specialize (H9 H8). destruct H9 as [v ?]. intuition. exists v. split; auto. split; auto. intros. eapply vtp_weaken_store; auto. apply vtp_closed in H1; intuition. lia. lia.
Qed.


(* fresh reference cannot be killed *)
Lemma CtxOK_weaken : forall {Σ ϰ σ T t d φ},
    CtxOK [] φ Σ ϰ σ ->
    value t ->
    vtp Σ ϰ φ t T d ->
    d ⊑↑ φ ->
    wf_senv Σ ->
    CtxOK [] (φ ⊔ &! (‖ σ ‖)) ([(T, d)] :: Σ) ϰ (Some [t] :: σ).
Proof.
  unfold CtxOK in *. intros.
  destruct H as [Hdom [Hlen [Hflt [Hclϰ [Hwf H]]]]].
  split. clear - Hdom Hlen. Qcrush. unfold N_lift, n_dom', n_dom in *. apply andb_true_iff in H. destruct H. simpl in H. simpl. rewrite <- Hlen. auto.
  split. simpl. lia.
  split. clear - Hlen Hflt. Qcrush. simpl. apply (H1 x H4). apply (H0 x H4). unfold N_lift, n_dom in *. specialize (H3 x H4). apply Nat.ltb_lt in H3. apply Nat.ltb_lt. simpl. lia. subst. unfold N_lift, n_dom. rewrite Hlen; simpl. apply Nat.ltb_lt. lia.
  split. simpl. eapply closed_Qual_monotone; eauto.
  split. rewrite Hlen. apply kill_sep_qor; auto. eapply kill_sep_outbound; eauto.
  intros. specialize (H l o cty T0 q). destruct H as [Hk He]. split.
  intros. specialize (Hk H). rewrite indexr_skip; auto. apply indexr_var_some' in Hk; lia.
  intros. apply qmem_plus_decomp in H4. 2:{ rewrite Hlen. eapply closed_Qual_sub. apply closed_Qual_qdom. Qcrush. } destruct H4.
  - (*not fresh*) specialize (He H H4). assert (l < ‖σ‖).
    { clear - H4 Hlen Hflt. Qcrush. specialize (H3 l H4). rewrite Hlen. unfold N_lift, n_dom in H3. apply Nat.ltb_lt in H3. lia. }
    rewrite indexr_skip. rewrite indexr_skip in H5. specialize (He H5). destruct He as [ctm ?]. intuition. exists ctm. split; auto. intros. specialize (H9 H8). destruct H9 as [v ?]. intuition. exists v. split; auto. split; auto.
    intros. rewrite Hlen. eapply vtp_weaken; auto. eapply H13. {
      erewrite <- sindexr_indexr_rewrite in H8. 2: eauto.
      (* we need use wf_senv to say: whatever already inside store is closed under old φ *)
      apply wf_senv_prop in H8; auto. intuition. rewrite Hlen in H12. clear - H8 H12. Qcrush. specialize (H3 x H4). rewrite or_false_elim in H3; auto. specialize (H2 x H4). rewrite or_false_elim in H2; auto. specialize (H6 x H4). destruct H6; auto; subst. specialize (H5 (‖ Σ ‖) H4). lia. } apply vtp_closed in H1; intuition. lia. lia.
  - (*l is fresh*) subst. clear He. exists [t]. rewrite Hlen in H5. rewrite indexr_head in H5. inversion H5; subst. rewrite indexr_head. split; auto.
    intros. apply indexr_var_some' in H4 as H6'. simpl in H6'. assert (o = 0) by lia; subst. simpl in H4; inversion H4; subst. exists t. split; simpl; auto. split; auto.
    intros. rewrite Hlen. eapply vtp_weaken; auto. apply vtp_closed in H1; intuition.
Qed.


Lemma CtxOK_refat : forall {Σ ϰ σ T t d φ l},
  CtxOK [] φ Σ ϰ σ ->
  value t ->
  vtp Σ ϰ φ t T d ->
  wf_senv Σ ->
  l < ‖Σ‖ ->
  CtxOK [] (φ) (sinsert Σ l (T,d)) ϰ (cinsert σ l t).
Proof.
  intros. unfold CtxOK in *. destruct H as [Hdom [Hlen [Hflt [Hclϰ [Hwf H]]]]].
  split. clear - Hlen Hdom H3. Qcrush. unfold N_lift, n_dom' in *. apply andb_true_iff in H. destruct H. apply Nat.ltb_lt in H. simpl in *. unfold n_dom. rewrite <- senv_length_coersion. rewrite sinsert_length. rewrite cinsert_length in H. rewrite Hlen in H. apply Nat.ltb_lt; auto.
  split. rewrite <- senv_length_coersion. rewrite sinsert_length. rewrite cinsert_length; auto.
  split. clear - H3 Hflt. Qcrush. unfold N_lift, n_dom. rewrite <- senv_length_coersion. rewrite sinsert_length. specialize (H4 x H2). unfold N_lift, n_dom in H4. auto.
  split; auto. rewrite <- senv_length_coersion. rewrite sinsert_length. auto.
  split; auto.
  intros. bdestruct (l =? l0); subst.
  - split; auto. specialize (H l0 o cty T0 q). destruct H as [Hk He].  intros. rewrite cinsert_indexr_None; auto.
    intros. intuition.
    apply sinsert_indexr' in H6 as H8'. destruct H8' as [cty' [H8' H8'']]. subst.
    specialize (H l0 o (cty') T0 q). destruct H. intuition. destruct H8 as [ctm ?]. intuition. exists (t :: ctm). split. split; auto. apply cinsert_indexr; auto. simpl; auto.
    bdestruct (o =? ‖cty'‖); subst.
    + intros. rewrite H10. exists t. rewrite indexr_head. split; auto. split; auto.
      intros. rewrite indexr_head in H8. inversion H8; subst. eapply vtp_weaken_2D_store. eauto. auto. apply sinsert_extends_2D; auto.
    + intros. apply indexr_var_some' in H11 as H11'; simpl in H11'. assert (o < (‖ cty' ‖)) by lia. rewrite indexr_skip. rewrite indexr_skip in H11. intuition. destruct (H13) as [v ?]. intuition.
      exists v. split; auto. split; auto. intros. specialize (H16 H15). eapply vtp_weaken_2D_store; eauto. apply sinsert_extends_2D; auto. lia. lia.
  - split; intros. specialize (H l0 o cty T0 q). destruct H as [Hk He]. specialize (Hk H5). rewrite cinsert_indexr_miss; auto.
    specialize (H l0 o cty T0 q). destruct H. intuition. assert (l0 <> l) by lia. eapply (@sinsert_indexr_miss (ty*qual) Σ l l0 (T,d)) in H9. assert (indexr l0 (Σ: list (list (ty*qual))) = Some cty). { rewrite <- H7. rewrite <- H9. auto. } specialize (H8 H10).
    destruct H8 as [ctm ?]. intuition. exists ctm. split. split; auto. rewrite cinsert_indexr_miss; auto.
    intros. specialize (H12 H11). destruct (H12) as [v ?]. exists v. intuition.
    eapply vtp_weaken_2D_store; eauto. eapply sinsert_extends_2D; eauto.
Qed.


Lemma update_preserve_qdom : forall {σ : store} {l v}, l ∈ₗ (qdom' σ) -> qdom' σ = qdom' (update σ l (Some v)).
Proof.
  intros. unfold qdom' in *. f_equal. unfold n_dom' in *. rewrite <- update_length.
  simpl in *. unfold N_lift in *. apply andb_true_iff in H. destruct H.
  destruct (indexr l σ) eqn:?. destruct o. all: intuition.
  apply FunctionalExtensionality.functional_extensionality. intro.
  bdestruct (x <? ‖ σ ‖); simpl; auto.
  bdestruct (x =? l). subst. rewrite update_indexr_hit. rewrite Heqo. auto. auto.
  rewrite update_indexr_miss. auto. auto.
Qed.

Lemma CtxOK_qdom' : forall {Γ φ Σ ϰ σ},
  CtxOK Γ φ Σ ϰ σ ->
  forall {l o T q}, l ∈ₗ φ -> ~ l ∈ₗ ϰ -> sindexr l o Σ = Some (T,q) -> l ∈ₗ (qdom' σ).
Proof.
  intros. destruct H as [Hdom [Hlen [Hflt [Hclϰ [Hwf H]]]]].
  apply sindexr_var_some' in H2 as H2'. destruct H2' as [H2' [cty [? ?]]].
  specialize (H l o cty T q). destruct H. intuition. destruct H6 as [ctm [?]]. intuition.
  clear - H7. Qcrush. unfold n_dom'. apply indexr_var_some' in H7 as ?. unfold N_lift. rewrite H7. bdestruct (l <? ‖ σ ‖). lia. lia.
Qed.


Lemma CtxOK_update : forall {Γ φ Σ ϰ σ},
  CtxOK Γ φ Σ ϰ σ ->
  forall {l o T q}, l < ‖σ‖ -> ~ l ∈ₗ ϰ -> sindexr l o Σ = Some (T,q) ->
  l ∈ₗ (qdom' σ) ->
  forall {v}, vtp Σ ϰ φ v T q -> value v -> q ⊑↑ φ -> CtxOK Γ φ Σ ϰ (supdate σ l o (v)).
Proof.
  intros. unfold CtxOK in *. destruct H as [Hdom [Hlen [Hflt [Hclϰ [Hwf H]]]]].
  split. rewrite <- supdate_preserve_qdom. auto. auto.
  split. rewrite <- supdate_length. lia.
  split. auto.
  split. auto.
  split. auto.
  intros. specialize (H l0 o0 cty T0 q0). destruct H as [Hk He].
  bdestruct (Nat.eqb l l0); subst.
  - split; intros. simpl in H1; unfold "~" in H1. apply H1 in H; lia.
    intuition. destruct H9 as [ctm ?]. intuition. exists (update ctm o v). split. split. rewrite supdate_indexr. unfold update'. rewrite H9; auto. auto. rewrite <- update_length; auto.
    intros. specialize (H11 H10). destruct H11 as [v' ?]. intuition.
    bdestruct (o=?o0); subst.
      exists v. split; auto. apply update_indexr_hit; auto. apply indexr_var_some' in H13; auto. split; auto.
        intros. erewrite sindexr_indexr_rewrite in H2; eauto. rewrite H10 in H2. inversion H2; subst; auto.
      exists v'. split; auto. rewrite update_indexr_miss; auto.
  - split; intros. intuition. erewrite supdate_indexr_miss; eauto.
    intuition. destruct H10 as [ctm ?]. intuition. exists ctm. split; auto. split; auto. erewrite supdate_indexr_miss; eauto.
Qed.


Lemma kill_shrink_qdom : forall {σ : store} {l}, qdom' (update σ l None) ⊑↑ qdom' σ.
Proof.
  intros. unfold qdom' in *. f_equal.
  simpl in *. apply Q_lift_subq'. unfold subq; simpl. split; auto. split. apply N_lift_sub; Qcrush. split. apply N_lift_sub; Qcrush. unfold n_dom' in *. rewrite <- update_length. unfold n_sub; intros.
  bdestruct (x <? ‖ σ ‖); simpl; auto.
  bdestruct (x =? l). subst. rewrite update_indexr_hit_None in H; auto. inversion H.
  rewrite update_indexr_miss in H; auto.
Qed.


Lemma CtxOK_kill : forall {Γ φ Σ ϰ σ l},
  CtxOK Γ φ Σ ϰ σ ->
  l < ‖Σ‖ -> wf_senv Σ -> closed_Qual 0 0 (‖ Σ ‖) φ ↑ ->
  CtxOK Γ (q_remove Σ l φ) Σ (ϰ ⊔ &! l) (update σ l None).
Proof.
  intros. unfold CtxOK in *. destruct H as [Hdom [Hlen [Hflt [Hclϰ [Hwf H]]]]].
  split. eapply Subq_trans. eapply kill_shrink_qdom; eauto. auto.
  split. rewrite <- update_length. lia.
  split. eapply Subq_trans. eapply q_remove_smaller; eauto. auto.
  split. apply closed_Qual_qor; auto. clear - H0. Qcrush.
  split. apply kill_sep_kill_qor. eapply kill_sep_sub. 2: eauto. apply q_remove_smaller. apply q_remove_sep.
  intros. specialize (H l0 o cty T q). destruct H as [Hk He]. bdestruct (Nat.eqb l l0); subst. (* new kill *)
  - split; intros. apply update_indexr_hit_None; rewrite Hlen. auto.
    clear - H. Qcrush.
  - split; intros. rewrite update_indexr_miss; auto. assert (l0 ∈ₗ ϰ). clear - H3 H. Qcrush. apply Hk; auto.
    assert (~ l0 ∈ₗ ϰ). clear - H3. Qcrush. assert (l0 ∈ₗ φ). clear - H4. eapply Subq_trans. 1: apply q_remove_smaller. 2: Qcrush; eauto. eauto.
    specialize (He H6 H7 H5). destruct He as [ctm ?]. intuition. exists ctm. split. split; auto. rewrite update_indexr_miss; auto.
    intros. specialize (H10 H9). destruct H10 as [v ?]. intuition. exists v. split; auto. split; auto.  intros.
    assert (q ⊑↑ φ). eapply Subq_trans. 2: eapply q_remove_smaller. eauto.
    eapply vtp_kill_retype; auto. eapply q_remove_sub_sep; eauto.
Qed.




Lemma vtp_store_loc_defined : forall {Σ ϰ φ σ l o d T d'},
    CtxOK [] φ Σ ϰ σ ->
    vtp Σ ϰ φ (& (l, o)) (TRef d T) d' ->
    exists ctm v, indexr l σ = Some (Some ctm) /\ indexr o ctm = Some (v).
Proof.
  intros. inversion H. inversion H0. subst. intuition.
  assert (l ∈ₗ ϰ -> False). { clear - H15 H23. apply qstp_empty in H15. unfold kill_sep in H23.  Qcrush. specialize (H7 l eq_refl). eapply H8; eauto. }
  apply sindexr_var_some' in H12 as H12'. destruct H12' as [? [cty [? ?]]].
  specialize (H16 l o cty T0 q1). destruct H16. specialize (H24 H6 H11 H18). erewrite sindexr_indexr_rewrite in H12; eauto.
  destruct H24 as [ctm ?]. intuition. destruct H25 as [v ?]. intuition.
  exists ctm. exists v. split; auto.
Qed.


Lemma CtxOK_kill_closed : forall {Γ φ Σ ϰ σ},
  CtxOK Γ φ Σ ϰ σ -> closed_Qual 0 0 (‖Σ‖) ϰ↑.
Proof.
  intros. destruct H; intuition.
Qed.

Lemma CtxOK_kill_sep : forall {Γ φ Σ ϰ σ},
  CtxOK Γ φ Σ ϰ σ -> kill_sep ϰ φ.
Proof.
  intros. destruct H; intuition.
Qed.



(* a rephrase of vtp_retype *)
Lemma has_type_value_retype : forall Σ φ t T d l,
  has_type [] φ Σ t T d ->
  value t -> kill_sep &! l d ->
  has_type [] (q_remove Σ l φ) Σ t T d.
Proof.
  intros. assert (closed_Qual 0 0 (‖Σ‖) (q_remove Σ l φ)↑). { apply has_type_closed in H; intuition. eapply closed_Qual_sub in H2. eapply H2. eapply q_remove_smaller. } remember ([]) as Γ.  induction H; inversion H0; subst.
  - eapply t_tabs; eauto. apply q_remove_sub; auto.
  - apply t_base; auto.
  - apply t_abs; eauto. apply q_remove_sub; auto.
  - eapply t_loc; eauto.  apply q_remove_sub; auto.
  - eapply t_sub; eauto. eapply IHhas_type; auto. apply stp_qstp_inv in H3. apply qstp_empty in H3. eapply kill_sep_sub; eauto. eapply q_remove_sub'; auto. apply has_type_closed in H; intuition.
  - eapply t_sub; eauto. eapply IHhas_type; auto. apply stp_qstp_inv in H3. apply qstp_empty in H3. eapply kill_sep_sub; eauto. eapply q_remove_sub'; auto. apply has_type_closed in H; intuition.
  - eapply t_sub. eapply IHhas_type; eauto. apply stp_qstp_inv in H3. apply qstp_empty in H3. eapply kill_sep_sub; eauto. auto. eapply q_remove_sub'; auto. apply has_type_closed in H; intuition. simpl; unfold kill_sep; auto.
  - eapply t_sub; eauto. eapply IHhas_type; auto. apply stp_qstp_inv in H3. apply qstp_empty in H3. eapply kill_sep_sub; eauto. eapply q_remove_sub'; auto. apply has_type_closed in H; intuition.
Qed.



(* the measurement how the terms are stepped:
  if a term is not yet stepped, then there must contain no local locs
  if a term is a value, then there must contain no local locs
*)
Fixpoint wf_step (t:tm) : Prop :=
  match t with
  | ttabs t1 => local_locs t1 = ∅
  | ttapp t1 => wf_step t1
  | tabs t1 => local_locs t1 = ∅
  | tapp t1 t2 => wf_step t1 /\ wf_step t2 /\ ((value t1) \/ local_locs t2 = ∅)
  | tref t1 => wf_step t1
  | trefat t1 t2 => wf_step t1 /\ wf_step t2 /\ (local_locs t1 = ∅ \/ (value t2))
  | tderef t1 => wf_step t1
  | tassign t1 t2 => wf_step t1 /\ wf_step t2 /\ ((value t1) \/ local_locs t2 = ∅)
  | twithr t1 t2 => wf_step t1 /\ wf_step t2 /\ (local_locs t2 = ∅) (* t2 is not stpped in twithr*)
  | twithc l t1 => wf_step t1
  | _ => True
  end.

(* the properties, it's required for wf_step *)
Definition wf_store (σ : store) : Prop :=
    forall l o v, sindexr' l o σ = Some (v) -> wf_step v /\ value v.

Lemma wf_store_app : forall σ v, wf_store σ ->
  wf_step v -> value v -> wf_store (Some [v] :: σ).
Proof.
  intros. unfold wf_store in *; intros. apply sindexr'_var_some' in H2 as H2'; destruct H2' as [? [y [? ?]]]; simpl in *. bdestruct (l =? ‖ σ ‖); subst.
  - inversion H4; subst. simpl in H5. assert (o = 0). simpl in H5; lia. subst. simpl in H2. inversion H2; subst. split; auto.
  - specialize (H l o v0 H2). auto.
Qed.

Lemma wf_store_cinsert : forall σ v, wf_store σ -> wf_step v -> value v ->
  forall l, wf_store (cinsert σ l v).
Proof.
  intros. unfold wf_store in *; intros. apply sindexr'_var_some' in H2 as H2'; destruct H2' as [? [y [? ?]]]; simpl in *. rewrite cinsert_length in H3. bdestruct (l =? l0); subst.
  - (*hit*) erewrite sindexr'_indexr_rewrite in H2; eauto. eapply cinsert_indexr' in H4. destruct H4 as [c' [? ?]]; subst. bdestruct (o =? ‖ c' ‖); subst.
    rewrite indexr_head in H2; inversion H2; subst. split; auto.
    apply (H l0 o). erewrite (@sindexr'_indexr_rewrite σ l0 o c'). 2: eauto. rewrite indexr_skip in H2. auto. simpl in H5. lia.
  - (*miss*) erewrite sindexr'_indexr_rewrite in H2; eauto. apply (H l0 o). erewrite sindexr'_indexr_rewrite; eauto. rewrite cinsert_indexr_miss in H4; auto.
Qed.

Lemma wf_store_supdate : forall σ v, wf_store σ -> wf_step v -> value v ->
  forall l o, wf_store (supdate σ l o v).
Proof.
  intros. unfold wf_store in *; intros. apply sindexr'_var_some' in H2 as H2'; destruct H2' as [? [y [? ?]]]; simpl in *. rewrite <- supdate_length in H3. bdestruct (l =? l0); subst.
  - (*hit*) pose H2 as H2'. erewrite sindexr'_indexr_rewrite in H2'; eauto. rewrite supdate_indexr in H4; auto. remember (indexr l0 σ) as x. destruct x. 2:{ inversion H4. } unfold update' in H4. destruct o1. 2:{ inversion H4. }
    inversion H4; subst. rewrite <- update_length in H5. bdestruct (o0 =? o); subst.
    + rewrite update_indexr_hit in H2'; auto. inversion H2'; subst. split; auto.
    + rewrite update_indexr_miss in H2'; auto. apply (H l0 o0). erewrite sindexr'_indexr_rewrite; eauto.
  - (*miss*) erewrite sindexr'_indexr_rewrite in H2; eauto. apply (H l0 o0). erewrite sindexr'_indexr_rewrite; eauto. erewrite supdate_indexr_miss in H4; auto.
Qed.

Lemma wf_store_update : forall σ, wf_store σ -> forall l, wf_store (update σ l None).
Proof.
  intros. unfold wf_store in *; intros. apply sindexr'_var_some' in H0 as H0'; destruct H0' as [? [y [? ?]]]; simpl in *. rewrite <- update_length in H1. bdestruct (l =? l0); subst.
  - (*hit*) rewrite update_indexr_hit_None in H2; auto. inversion H2.
  - (*miss*) rewrite update_indexr_miss in H2; auto. apply (H l0 o). erewrite sindexr'_indexr_rewrite; eauto. erewrite sindexr'_indexr_rewrite in H0; eauto. rewrite update_indexr_miss; auto.
Qed.



Lemma wf_step_value : forall t,
  wf_step t -> value t -> local_locs t = ∅.
Proof.
  intros. inversion H0; subst; simpl in *; auto.
Qed.

Lemma value_open_preserve: forall t k t',
  value t -> value ([[k ~> t']]ᵗ t).
Proof.
  intros. inversion H; subst; simpl; auto.
Qed.

Lemma qor_empty_inv : forall q1 q2,
  (q1 ⊔ q2) = ∅ -> q1 = ∅ /\ q2 = ∅.
Proof.
  intros. assert (q1 ⊑↑ ∅). rewrite <- H. Qcrush. assert (q2 ⊑↑ ∅). rewrite <- H. Qcrush.
  clear H. split; apply Q_lift_eq; Qcrush.
  apply (H1 x); auto. apply (H3 x); auto. apply (H6 x); auto.
  apply (H2 x); auto. apply (H4 x); auto. apply (H7 x); auto.
Qed.

Lemma local_locs_wf_step : forall t,
  local_locs t = ∅ -> wf_step t.
Proof.
  induction t; simpl; intros; auto.
  apply qor_empty_inv in H; destruct H; auto.
  apply qor_empty_inv in H; destruct H; auto.
  apply qor_empty_inv in H; destruct H; auto.
  apply qor_empty_inv in H; destruct H; auto.
  apply qor_empty_inv in H; destruct H; auto.
Qed.

Lemma wf_step_open : forall t t' k,
  wf_step t -> local_locs t' = ∅ ->
  wf_step ([[k ~> t']]ᵗ t).
Proof.
  intros. generalize dependent k. induction t; simpl in *; subst; intros; auto.
  rewrite <- (@qor_idem ∅). rewrite local_locs_open'; auto.
  destruct v; simpl; auto. bdestruct (k=?i); subst; auto. apply local_locs_wf_step; auto. rewrite local_locs_open'; auto.
  destruct H as [? [? ?]]. destruct H2.
    split; auto. split; auto. left. apply value_open_preserve; auto.
    split; auto. split; auto. right. rewrite local_locs_open'; auto.
  destruct H as [? [? ?]]. destruct H2.
    split; auto. split; auto. left. apply value_open_preserve; auto.
    split; auto. split; auto. right. rewrite local_locs_open'; auto.
  destruct H as [? [? ?]]. destruct H2.
    split; auto. split; auto. left. rewrite local_locs_open'; auto.
    split; auto. split; auto. right. apply value_open_preserve; auto.
  destruct H as [? [? ?]].
    split; auto. split; auto.  rewrite local_locs_open'; auto.
Qed.


Lemma value_unsteppable: forall v, value v ->
  forall σ t' σ', step v σ t' σ' -> False.
Proof.
  intros. induction H0; inversion H; auto.
Qed.

Lemma wf_step_preserve : forall t σ t' σ',
  wf_store σ ->
  wf_step t -> step t σ t' σ' -> wf_step t'.
Proof.
  intros. induction H1; simpl in *; auto.
  apply local_locs_wf_step. unfold open_tm. rewrite local_locs_open'; auto. rewrite local_locs_open'; auto.
  destruct H0 as [? [? ?]]. apply local_locs_wf_step. unfold open_tm. rewrite local_locs_open'; auto. rewrite local_locs_open'; auto. apply wf_step_value; auto.
  unfold wf_store in H. assert (sindexr' l o σ = Some v). { erewrite sindexr'_indexr_rewrite; eauto. } eapply (H); eauto.
  destruct H0 as [? [? ?]]. apply wf_step_open; auto. apply wf_step_open; auto.
  destruct H0 as [? [? ?]]. split; auto.
  destruct H0 as [? [? ?]]. split; auto. split; auto. destruct H3. left; auto. apply value_unsteppable in H1; auto. lia.
  destruct H0 as [? [? ?]]. split; auto. split; auto. destruct H3. left; auto. apply value_unsteppable in H1; auto. lia. right; auto.
  destruct H0 as [? [? ?]]. split; auto.
  destruct H0 as [? [? ?]]. split; auto. split; auto. destruct H3. left; auto. apply value_unsteppable in H1; auto. lia. right; auto.
  destruct H0 as [? [? ?]]. split; auto.
  destruct H0 as [? [? ?]]. split; auto.
Qed.

Lemma wf_store_preserve : forall t σ t' σ',
  wf_store σ ->
  wf_step t -> step t σ t' σ' -> wf_store σ'.
Proof.
  intros. pose H1 as H1'. apply wf_step_preserve in H1'; auto. induction H1; auto.
  - apply wf_store_app; auto.
  - apply wf_store_cinsert; auto. inversion H0; auto.
  - apply wf_store_supdate; auto. inversion H0; destruct H6; auto.
  - apply wf_store_app; auto. inversion H0; auto.
  - apply wf_store_update; auto.
  - inversion H0. destruct H4. apply IHstep; auto. apply wf_step_preserve in H2; auto.
  - inversion H0. destruct H3. apply IHstep; auto. apply wf_step_preserve in H1; auto.
  - inversion H0. destruct H3. apply IHstep; auto. apply wf_step_preserve in H1; auto.
  - inversion H0. destruct H4. apply IHstep; auto. apply wf_step_preserve in H2; auto.
  - inversion H0. destruct H3. apply IHstep; auto. apply wf_step_preserve in H1; auto.
  - inversion H0. destruct H4. apply IHstep; auto. apply wf_step_preserve in H2; auto.
  - inversion H0. destruct H3. apply IHstep; auto. apply wf_step_preserve in H1; auto.
Qed.


(* two ad-hoc lemmas to simplify the growth reasoning *)
Lemma local_locs_step_same : forall t σ t' σ',
  wf_store σ ->
  ‖σ‖ = ‖σ'‖ ->
  wf_step t ->
  step t σ t' σ' ->
  local_locs t' ⊑↑ local_locs t.
Proof.
  intros. pose t. induction H2; simpl in *; auto.
  - eapply Subq_trans. eapply local_locs_open. simpl; rewrite qor_empty_left. eapply Subq_trans. eapply local_locs_open. simpl. rewrite qor_idem; Qcrush.
  - eapply Subq_trans. eapply local_locs_open. rewrite wf_step_value. rewrite qor_empty_left. rewrite qor_empty_right. eapply Subq_trans. eapply local_locs_open. simpl. rewrite qor_idem; Qcrush. destruct H1 as [? [? ?]]; auto. auto.
  - rewrite wf_step_value; auto. eapply H; eauto. erewrite sindexr'_indexr_rewrite; eauto. eapply H. erewrite sindexr'_indexr_rewrite; eauto.
  - lia.
  - apply Subq_qor_l. eapply Subq_trans. eapply IHstep; auto. destruct H1; auto. Qcrush. clear. Qcrush.
  - apply Subq_qor_l. clear. Qcrush. eapply Subq_trans. eapply IHstep; auto. destruct H1 as [? [? ?]]; auto. clear. Qcrush.
  - destruct H1. specialize (IHstep H H0 H1). clear - IHstep. Qcrush.
  - destruct H1 as [? [? ?]]. specialize (IHstep H H0 H4). clear - IHstep. Qcrush.
  - destruct H1. specialize (IHstep H H0 H1). clear - IHstep. Qcrush.
  - destruct H1 as [? [? ?]]. specialize (IHstep H H0 H4). clear - IHstep. Qcrush.
  - destruct H1. specialize (IHstep H H0 H1). clear - IHstep. Qcrush.
Qed.


Lemma local_locs_step_grow : forall t σ t' σ',
  wf_store σ ->
  S (‖σ‖) = ‖σ'‖ ->
  wf_step t ->
  step t σ t' σ' ->
  local_locs t' ⊑↑ (local_locs t) ⊔ &!(‖σ‖).
Proof.
  intros. pose t. induction H2; simpl in *; auto; try lia.
  - rewrite qor_symm. apply Subq_qor.  eapply Subq_trans. eapply local_locs_open. simpl; rewrite qor_empty_left. eapply Subq_trans. eapply local_locs_open. simpl. rewrite qor_empty_left. Qcrush.
  - rewrite qor_assoc_23. Qcrush.
  - destruct H1 as [? [? ?]]. rewrite qor_assoc_23. apply Subq_qor. apply IHstep; auto.
  - rewrite <- qor_assoc. apply Subq_qor_l. Qcrush. eapply Subq_trans. eapply IHstep; auto. destruct H1 as [? [? ?]]; auto. Qcrush.
  - destruct H1. specialize (IHstep H H0 H1). rewrite qor_assoc_23. clear - IHstep. Qcrush.
  - destruct H1 as [? [? ?]]. specialize (IHstep H H0 H4). rewrite <- qor_assoc. clear - IHstep. Qcrush.
  - destruct H1. specialize (IHstep H H0 H1). rewrite qor_assoc_23. clear - IHstep. Qcrush.
  - destruct H1 as [? [? ?]]. specialize (IHstep H H0 H4). rewrite <- qor_assoc. clear - IHstep. Qcrush.
  - destruct H1. specialize (IHstep H H0 H1). rewrite qor_assoc_23. clear - IHstep. Qcrush.
  - specialize (IHstep H H0 H1). rewrite <- qor_assoc. clear - IHstep. Qcrush.
Qed.


Lemma app_eq_false : forall (Σ : senv) Σ',
  ‖Σ'‖ > 0 ->
  Σ = Σ' ++ Σ -> False.
Proof.
  unfold senv. intros. assert (‖Σ‖ = ‖Σ'‖ + ‖Σ‖). rewrite H0 at 1. rewrite app_length; auto. lia.
Qed.

Lemma cons_eq_false : forall (Σ Σ': senv) a,
  Σ' = a :: Σ -> ‖Σ‖ = ‖Σ'‖ -> False.
Proof.
  intros. replace (a :: Σ) with ([a] ++ Σ) in H by auto. subst. rewrite app_length in H0. simpl in H0. lia.
Qed.

Lemma disjointq_same : forall Σ Σ' σ σ' d d' φ φ' ϰ ϰ',
  Σ → Σ' ∋ d ⊕ d' ->
  CtxOK [] φ Σ ϰ σ ->
  CtxOK [] φ' Σ' ϰ' σ' ->
  ‖Σ‖ = ‖Σ'‖ ->
  ‖σ‖ = ‖σ'‖ /\ d' = ∅
.
Proof.
  intros. inversion H0. destruct H4. inversion H1. destruct H7. clear H5 H8. split. lia. inversion H; auto. exfalso. apply cons_eq_false in H10; auto.
Qed.

Lemma disjointq_grow : forall Σ T q σ σ' d d' φ φ' ϰ ϰ',
  Σ → [(T,q)] :: Σ ∋ d ⊕ d' ->
  CtxOK [] φ Σ ϰ σ ->
  CtxOK [] φ' ([(T,q)] :: Σ) ϰ' σ' ->
  S (‖σ‖) = ‖σ'‖.
Proof.
  intros. inversion H0. destruct H3. inversion H1. destruct H6. clear H4 H7. remember ([(T, q)] :: Σ ) as Σ'. rewrite HeqΣ' in *. simpl in *. lia.
Qed.


(* Some aulixary lemmas, so we don't need to inversion in the congruence cases *)

Lemma kill_sep_local_locs_base : forall t σ t' σ' q,
  step t σ t' σ' ->
  wf_store σ ->
  wf_step t ->
  ‖σ‖ = ‖σ'‖ ->
  kill_sep (local_locs t) q ->
  kill_sep (local_locs t') q.
Proof.
  intros. apply (local_locs_step_same) in H; auto. eapply kill_sep_kill_sub; eauto.
Qed.

Lemma kill_sep_local_locs_grow : forall t σ t' σ' q b f,
  step t σ t' σ' ->
  wf_store σ ->
  wf_step t ->
  S (‖σ‖) = ‖σ'‖ ->
  closed_Qual b f (‖σ‖) q↑ ->
  kill_sep (local_locs t) q ->
  kill_sep (local_locs t') q.
Proof.
  intros. apply (local_locs_step_grow) in H; auto. eapply kill_sep_kill_sub; eauto. clear - H4 H3. unfold kill_sep in *. rewrite qand_qor_dist_l. apply Qor_bound; auto. clear H4. Qcrush. subst. specialize (H2 (‖σ‖) H3). lia.
Qed.


Lemma kill_sep_local_locs_trans_tenv : forall t σ t' σ' d' d1 df Σ T q,
  step t σ t' σ' ->
  wf_store σ ->
  wf_step t ->
  (‖ σ ‖) = (‖Σ‖) ->
  S (‖σ‖) = ‖σ'‖ ->
  Σ → [(T, q)] :: Σ ∋ df ⊕ d' ->
  closed_Qual 0 0 (‖Σ‖) d1↑ ->  closed_Qual 0 0 (‖Σ‖) df↑ ->
  kill_sep (local_locs t) (q_trans_tenv [] d1 ⋒ q_trans_tenv [] df) ->
  kill_sep (local_locs t') (q_trans_tenv [] d1 ⋒ q_trans_tenv [] (df ⋓ d')).
Proof.
  intros. replace (q_trans_tenv [] (df ⋓ d')) with (df ⋓ d'); auto. replace (q_trans_tenv [] d1) with d1 in *; auto. replace (q_trans_tenv [] df) with df in *; auto.
  apply kill_sep_qor_rev in H7. destruct H7. apply kill_sep_qor. 2: apply kill_sep_fresh. simpl. destruct (♦∈? df) eqn:Eq.
  2: {eapply kill_sep_local_locs_grow; eauto. eapply closed_Qual_qand; eauto. rewrite H2; eauto. rewrite H2; eauto. }
  rewrite qand_qor_dist_l. apply kill_sep_qor. eapply kill_sep_local_locs_grow; eauto. eapply closed_Qual_qand; eauto. rewrite H2; eauto. rewrite H2; eauto.
  inversion H4; subst. replace (d1 ⊓ ∅) with (∅). apply kill_sep_empty. clear; apply Q_lift_eq; Qcrush.
    replace (d1 ⊓ &! (‖ Σ ‖)) with (∅). apply kill_sep_empty. clear - H5. apply Q_lift_eq. Qcrush. subst. specialize (H2 (‖Σ‖) H3). lia.
Qed.

Lemma CtxOK_shrink_flt : forall {Σ φ ϰ σ} φd,
  wf_senv Σ ->
  CtxOK [] φ Σ ϰ σ ->
  φd ⊑↑ φ ->
  CtxOK [] φd Σ ϰ σ.
Proof.
  intros. unfold CtxOK in *; intros. intuition.
  eapply Subq_trans; eauto. eapply kill_sep_sub; eauto.
  specialize (H7 l o cty T q); destruct H7. auto.
  specialize (H7 l o cty T q); destruct H7. assert (l ∈ₗ φ). clear - H8 H1. Qcrush. intuition.
    destruct H12 as [ctm ?]. intuition. exists ctm. intuition.
    destruct H15 as [v ?]. intuition. exists v. split; auto. split; auto.
    intros. assert (q ⊑↑ φ). eapply Subq_trans; eauto. specialize (H17 H18). eapply vtp_has_type in H17. eapply has_type_vtp; auto. eapply weaken_flt; eauto.
    eapply kill_sep_sub; eauto.
Qed.


(* wrapper of t_sub used in upcasting in tabs, ttabs *)
Lemma kill_sep_open2 : forall t d2 df d1 (Σ :senv),
  closed_Qual 2 0 (‖Σ‖) d2↑ ->
  closed_Qual 0 0 (‖Σ‖) df↑ ->
  closed_Qual 0 0 (‖Σ‖) d1↑ ->
  closed_tm 2 0 (‖Σ‖) t ->
  kill_sep (local_locs t) d2 -> kill_sep (local_locs t) d1 -> kill_sep (local_locs t) df ->
  kill_sep (local_locs t) (d2 <~ᵈ df; d1).
Proof.
  intros. eapply kill_sep_sub with (q:= df ⊔ d1 ⊔ (d2 <~ᵈ ∅; ∅) ).
  eapply openq_subqual. 2-4: clear; Qcrush. eapply closed_Qual_qor. eauto. eapply closed_Qual_qor; auto. apply closed_qual_open2; auto.
    eapply kill_sep_qor; auto. eapply kill_sep_qor; auto. unfold openq. eapply kill_sep_open_empty'. 2: eauto. eapply local_locs_closed; eauto.
Qed.




(* 
  Formalization of environment evolution
    we can only kill exactly one location each time
    t is the result before step
*)
Inductive envUpdate (Σ : senv) (φ : qual) (ϰ : qual) (LC : qual): senv -> qual -> qual -> Prop :=
| env_phi : forall Σ',
    (* In arena system, co-allocation does not change filter, but only update store *)
    Σ' ⊇₂ Σ ->
    ‖Σ'‖ = ‖Σ‖ ->
    envUpdate Σ φ ϰ LC Σ' φ ϰ
| env_fresh : forall T q, (* new allocation, cannot grow kill *)
    kill_sep ϰ q ->
    envUpdate Σ φ ϰ LC ([(T,q)] :: Σ) (φ ⊔ &!(‖Σ‖)) ϰ
| env_kill : forall l, (* kill, also shrink φ, cannot grow store *)
    l < (‖Σ‖) ->
    l ∈ₗ LC ->
    envUpdate Σ φ ϰ LC Σ (q_remove Σ l φ) (ϰ ⊔ &!l) (* don't need to shrink here, as already do in Preserve *)
.
#[global] Hint Constructors envUpdate : core.



(* Definition for preservation *)
Inductive preserve (Γ : tenv) (Σ : senv) (ϰ : qual) (φ : qual) (LC : qual) (t' : tm) (T : ty) (d : qual) (σ' : store) : Prop :=
| Preserve : forall Σ' d' φ' ϰ',
    Σ' ⊇₂ Σ -> (* store typing monotonically grow *)
    (*φ ⊑↑ φ' -> main difference from previous works, because we may shrink context filter φ on kill *)
    envUpdate Σ φ ϰ LC Σ' φ' ϰ' ->
    d' ⊑↑ φ' ->  (* qualifier within observation *)
    wf_senv Σ' ->
    CtxOK Γ φ' Σ' ϰ' σ' -> (* store typing describes the store *)
    Σ → Σ' ∋ d ⊕ d'  -> (* d' is either empty or only new location *)
    has_type Γ φ' Σ' t' T (d ⋓ d') -> (* ♦ in d is substituted with new location on store grow *)
    (* establish the well-formedness after stepping *)
    wf_store σ' ->
    wf_step t' ->
    preserve Γ Σ ϰ φ LC t' T d σ'.
Arguments Preserve {Γ Σ ϰ φ LC t' T d σ'}.



(* ================= Main soundness Proof ============== *)

Theorem type_safety: forall {Σ ϰ t T d φ},
  has_type [] φ Σ t T d -> wf_senv Σ -> wf_step t -> (
    value t \/
    (forall {σ} , CtxOK [] φ Σ ϰ σ -> wf_store σ ->
      (exists t' σ',
        step t σ t' σ' /\ preserve [] Σ ϰ φ (local_locs t) t' T d σ'
      )
    )
  ).
Proof.
  intros Σ ϰ t T d φ H HwfSigma Hwfstep.
  specialize (has_type_closed H) as HX. remember [] as G. remember t as tt. remember T as TT.
  revert T t HeqTT Heqtt HeqG.
  induction H; try (left; constructor); intros.

  - (* ttapp *) right. subst. intuition.
     apply (CtxOK_kill_closed) in H13 as Hclϰ. apply (CtxOK_kill_sep) in H13 as Hwfkill.
     apply has_type_closed in H as HH. intuition.
     specialize (H11 (TAll d1 d2 T1 T2) t). intuition.
     + (* contraction *)
       (* turn has_type to vtp *)
       apply (has_type_vtp Hclϰ) in H as VH; intuition.
       pose (VHH := VH). inversion VH. subst.
       specialize (has_type_filter H) as Hflt0.
       apply (has_type_vtp Hclϰ) in H as VH0; intuition.
       exists (t0 <~ᵗ (ttabs t0); tunit). exists σ. intuition.
       * constructor.
       * apply (Preserve Σ ∅ φ ϰ); auto.  rewrite qqplus_qbot_right_neutral.
         apply qstp_closed in H28 as H28'; intuition.
         change (length []) with 0 in *. subst.
         pose (VH' := H26). eapply t_tabs with (φ:=df1) in VH'; eauto. apply (has_type_vtp Hclϰ) in VH'; auto.
         assert (HT' : has_type [(bind_ty, false, T1, d1) ; (bind_tm, true, TAll d0 d3 T0 T3, df1)] (df1 ⊔ $!0 ⊔ $!1) Σ (open_tm' ([]:tenv) t0) (open_ty' ([]:tenv) T3) (openq' ([]:tenv) d3)). {
           eapply narrowing. eapply H26. intuition. auto. apply stp_qstp_inv in H27. eapply qstp_empty; eauto. auto.
         }
         eapply @substitution1_ty in HT' as HT''; eauto; intuition.
         unfold open_tm' in HT''. unfold open_ty' in HT''. unfold openq' in HT''. simpl in HT''. inversion H24. inversion H25. subst.
         unfold open_ty in HT''. unfold openq in HT''.
         erewrite <- open_subst2_tm in HT''; eauto.
         erewrite <- open_subst2_ty in HT''; eauto.
         erewrite <- open_subst2_qual in HT''; eauto.
         fold (open_tm (ttabs t0) t0 t0) in HT''. fold (openq df1 d1 d3) in HT''. fold (open_ty (TAll d0 d3 T0 T3) df1 T1 d1 T3) in HT''.
         apply @weaken_flt with (φ':= φ) in HT''; auto; intuition.
         eapply t_sub; eauto. 3:{ unfold open_tm. rewrite local_locs_open'; auto. rewrite local_locs_open'; auto. eapply kill_sep_open2; eauto.  }
         pose (Hsub:=H29). eapply @substitution_stp1 with (df:=df1) in Hsub; eauto.
         simpl in Hsub. unfold openq' in Hsub. unfold openq in Hsub. unfold open_ty' in Hsub. unfold open_ty in Hsub. simpl in Hsub.
         erewrite <- open_subst2_ty in Hsub; eauto. erewrite <- open_subst2_ty in Hsub; eauto.
         erewrite <- open_subst2_qual in Hsub; eauto. erewrite <- open_subst2_qual in Hsub; eauto.
         unfold open_ty. unfold openq.
         replace ([[0 ~> TUnit ~ ∅ ]]ᵀ T2) with ([[0 ~> TAll d0 d3 T0 T3 ~ df1 ]]ᵀ T2); auto. (* since not_free 0 T2 *)
         eapply s_trans; eauto. apply stp_refl; auto. apply closed_ty_open2; auto.
         constructor. eapply openq_mono; eauto. apply qstp_empty in H28. auto. apply openq_closed; auto.
         eapply openq_subqual; eauto using closed_Qual_qor. eapply Subq_trans; eauto.
         repeat apply Qor_bound; auto.
         assert (df1  ⊑↑ φ ⊔ {♦}). eapply qstp_empty in H28. eapply Subq_trans; eauto.
         eapply Subqual_non_fresh; eauto 3.
         unfold open_tm'. rewrite local_locs_open'; auto. rewrite local_locs_open'; auto.
         unfold open_tm'. rewrite local_locs_open'; auto. rewrite local_locs_open'; auto. simpl in Hwfstep. rewrite Hwfstep. unfold kill_sep; clear; Qcrush.
         eapply kill_sep_sub with (q:=df); eauto.  apply qstp_empty in H28. eapply Subq_trans; eauto.
         eapply kill_sep_sub with (q:=df); eauto.  apply qstp_empty in H28. eapply Subq_trans; eauto.
         eapply wf_step_preserve; eauto. econstructor; eauto.
     + (* left congruence *)
       specialize (H11 σ H13 H14). destruct H11 as [t0' [σ' HH5]]. exists (ttapp t0'). exists σ'. intuition.
       constructor. intuition. destruct H18. ndestruct ((qbvs d2) 0).
       * (* d2 is dependent on f, so the growth in df might be observable  *)
        (* this is the sole reason why need to distinguish whether d2 is dependent on f or not *)
        inversion H16. subst. destruct (♦∈? df) eqn:Hfresh.
        ** apply (Preserve Σ' d' φ' ϰ'); auto. eapply disjointq_scale; eauto. eapply openq_subqual_0; eauto.
          erewrite @openq_duplicate_eq_l with (f:=0) (l:=‖Σ'‖). 3,4 : eapply closed_Qual_monotone; eauto. 2,3 : eauto.
              inversion H20; subst.
          ++ (*base*) eapply disjointq_same in H24; auto. 2: eapply H13. 2: eapply H23. destruct H24. subst. repeat rewrite qqplus_qbot_right_neutral in *.
            apply t_tapp; auto. 1-2: rewrite H30; auto.
            eapply kill_sep_local_locs_base; eauto.
            eapply kill_sep_local_locs_base; eauto.
          ++ (*fresh*) eapply disjointq_grow in H24 as ?. 2: eapply H13. 2: eapply H23.
            eapply t_sub with (T1 := (T2 <~ᵀ TUnit ~ ∅; T1 ~ d1))(d1 := (openq (df ⋓ d') d1 d2)).
            --- apply t_tapp; auto; apply extends_2D_length in H18 as H15'.
                eapply closed_ty_monotone; eauto.
                eapply closed_Qual_monotone; eauto.
                (* prove using relation between d2, φ' from new has_type *) eapply Subq_trans; eauto.
                eapply Subq_trans; eauto.
                1-2: destruct H13 as [? [Hlen ?]]. 1-2: rewrite <- Hlen in H36, H37.
                eapply kill_sep_local_locs_grow; eauto. eapply kill_sep_local_locs_grow; eauto.
            --- apply stp_refl. simpl. eapply closed_ty_monotone; eauto.
                constructor; auto. apply closed_Qual_qqplus; auto.
                apply openQ_closed. 2 : apply closed_qual_qqplus.
                1,2,4 : eapply closed_qual_monotone; eauto; lia. all: eapply disjointq_closed; eauto.
            --- (* prove using H22 *)
                apply has_type_filter in H25 as ?. apply Qqplus_bound.
                eapply openq_subqual_trans'. eapply H8. all: eauto 3.
                apply has_type_closed in H25. intuition. apply closed_Qual_qor_fresh in H32. eauto.
                apply has_type_filter in H; auto.
                inversion H24; subst. clear; Qcrush. clear; Qcrush.
            --- (*t_sub requirement*) apply has_type_local_loc_sep in H25 as Hlc. replace ((df ⋓ d')) with (df ⊔ d') in *. 2: {clear - Hfresh; Qcrush. rewrite Hfresh; auto. }
              apply kill_sep_qor_rev in Hlc. destruct Hlc. apply kill_sep_qqplus_bound; auto. simpl.
              destruct H13 as [? [Hlen ?]].
              eapply kill_sep_open2. 2: apply closed_Qual_qor; auto. 3: eapply disjointq_closed; eauto. 1-3: eapply closed_Qual_monotone; eauto. apply has_type_closed in H25; intuition. eapply closed_tm_monotone; eauto.
              eapply kill_sep_local_locs_grow; eauto. rewrite Hlen; eauto. eapply kill_sep_local_locs_grow; eauto. rewrite Hlen; eauto. apply kill_sep_qor; auto.
          ++ (*kill*) eapply disjointq_same in H24; auto. 2: eapply H13. 2: eapply H23. destruct H24. subst. repeat rewrite qqplus_qbot_right_neutral in *.
            apply t_tapp; auto. simpl in Hwfstep.
            eapply q_remove_sub'; eauto. eapply kill_sep_open_empty' with (Σ := Σ'). clear - H29; Qcrush. eapply kill_sep_kill_sub. 2: eauto. clear - H30; Qcrush; subst; auto.
            eapply q_remove_sub; eauto. eapply kill_sep_kill_sub. 2: eauto. clear - H30; Qcrush; subst; auto.
            eapply kill_sep_local_locs_base; eauto. eapply kill_sep_local_locs_base; eauto.

        ** rewrite not_fresh_qqplus in H25; auto. apply (Preserve Σ' ∅ φ' ϰ'); auto. rewrite qqplus_qbot_right_neutral.
          inversion H20; subst.
          ++ (*base*) eapply disjointq_same in H24; auto. 2: eapply H13. 2: eapply H23. destruct H24. subst. repeat rewrite qqplus_qbot_right_neutral in *.
            apply t_tapp; auto. 1-2: rewrite H30; auto.
            eapply kill_sep_local_locs_base; eauto.
            eapply kill_sep_local_locs_base; eauto.
          ++ (*fresh*) eapply disjointq_grow in H24 as ?. 2: eapply H13. 2: eapply H23.
            apply extends_2D_length in H18 as H18'. apply t_tapp; auto.
            eapply closed_ty_monotone; eauto.
            eapply closed_Qual_monotone; eauto.
            eapply Subq_trans; eauto. eapply Subq_trans; eauto.
            1-2: destruct H13 as [? [Hlen ?]]. 1-2: rewrite <- Hlen in H36, H37.
            eapply kill_sep_local_locs_grow; eauto. eapply kill_sep_local_locs_grow; eauto.
          ++ (*kill*) eapply disjointq_same in H24; auto. 2: eapply H13. 2: eapply H23. destruct H24. subst. repeat rewrite qqplus_qbot_right_neutral in *.
            apply t_tapp; auto. simpl in Hwfstep.
            eapply q_remove_sub'; eauto. eapply kill_sep_open_empty' with (Σ:=Σ'). clear - H29; Qcrush. eapply kill_sep_kill_sub. 2: eauto. clear - H30; Qcrush; subst; auto.
            eapply q_remove_sub; eauto. eapply kill_sep_kill_sub. 2: eauto. clear - H30; Qcrush; subst; auto.
            eapply kill_sep_local_locs_base; eauto. eapply kill_sep_local_locs_base; eauto.
       * (* d2 is not dependent on f, so we don't observe the growth in df *)
         inversion H13. subst. apply (Preserve Σ' ∅ φ' ϰ'); auto. rewrite qqplus_qbot_right_neutral.
         replace (d2 <~ᵈ df; d1) with (d2 <~ᵈ df ⋓ d'; d1). (* since f doesn't occur in d2 *) 2: apply openq_subqual_0_false; auto.
         inversion H20; subst.
         ++ (*base*) eapply disjointq_same in H24; auto. 2: eapply H13. 2: eapply H23. destruct H24. subst. repeat rewrite qqplus_qbot_right_neutral in *.
          apply t_tapp; auto. 1-2: rewrite H32; auto.
          eapply kill_sep_local_locs_base; eauto.
          eapply kill_sep_local_locs_base; eauto.
         ++ (*fresh*) eapply disjointq_grow in H24. 2: eapply H13. 2: eapply H23.
            apply t_tapp; auto. eapply closed_ty_monotone; eauto.
            eapply closed_Qual_monotone; eauto.
            eapply Subq_trans; eauto. eapply Subq_trans; eauto.
            1-2: destruct H13 as [? [Hlen ?]]; apply has_type_closed in H25; intuition. 1-2: inversion H16; subst. 1-2: rewrite <- Hlen in H50, H51.
            eapply kill_sep_local_locs_grow; eauto. eapply kill_sep_local_locs_grow; eauto.
         ++ (*kill*) eapply disjointq_same in H24; auto. 2: eapply H13. 2: eapply H23. destruct H24. subst. repeat rewrite qqplus_qbot_right_neutral in *. inversion H16; subst.
            apply t_tapp; auto. simpl in Hwfstep.
            eapply q_remove_sub'; eauto. eapply kill_sep_open_empty' with (Σ:=Σ'). clear - H31; Qcrush. eapply kill_sep_kill_sub. 2: eauto. clear - H32; Qcrush; subst; auto.
            eapply q_remove_sub; eauto. eapply kill_sep_kill_sub. 2: eauto. clear - H32; Qcrush; subst; auto.
            eapply kill_sep_local_locs_base; eauto. eapply kill_sep_local_locs_base; eauto.

  - (* t_tapp_fresh *) right. subst. intuition.
     apply (CtxOK_kill_closed) in H15 as Hclϰ. apply (CtxOK_kill_sep) in H15 as Hwfkill.
     apply has_type_closed in H as HH. intuition.
     specialize (H13 (TAll (q_trans_tenv [] df ⋒ q_trans_tenv [] d1) d2 T1 T2) t). intuition.
     + (* contraction *)
       (* turn has_type to vtp *)
       apply (has_type_vtp Hclϰ) in H as VH; intuition.
       pose (VHH := VH). inversion VH. subst.
       exists (t0 <~ᵗ (ttabs t0); tunit). exists σ. intuition.
       * constructor.
       * apply (Preserve Σ ∅ φ ϰ); auto. rewrite qqplus_qbot_right_neutral. simpl in H7, H8.
         apply qstp_closed in H30 as H30'; intuition.
         change (length []) with 0 in *. subst.
         pose (VH' := H28). eapply t_tabs with (φ:=df1) in VH'; eauto. apply (has_type_vtp Hclϰ) in VH'; auto.
         (* remove potential freshness flag from the argument, in order to apply substitution lemma *)
         remember (false,(qfvs d1),(qbvs d1),(qlocs d1)) as d1''.
         remember (false,(qfvs df),(qbvs df),(qlocs df)) as df''.
         assert (Hd1'' : d1'' ⊑↑ d1). { subst. Qcrush. }
         assert (Hdf'' : df'' ⊑↑ df). { subst. Qcrush. }
         assert (Hdf1 : df1 ⊑↑ df). { apply qstp_empty in H30. Qcrush. }
         assert (Hd1''fr : ♦∉ d1''). { subst. auto. }
         assert (Hdf''fr : ♦∉ df''). { subst. auto. }
         assert (Hqand: (q_trans_tenv [] df'' ⋒ q_trans_tenv [] d1'') ⊑↑ (q_trans_tenv [] df ⋒ q_trans_tenv [] d1)). {
           apply Subq_qor. apply Subq_qand_split; auto. all: apply q_trans_subq; eauto.
         }
         assert (HT' : has_type [(bind_ty, false, T1, q_trans_tenv [] df'' ⋒ q_trans_tenv [] d1''); (bind_tm, true, TAll d0 d3 T0 T3, df1)] (df1 ⊔ $!0 ⊔ $!1) Σ (open_tm' ([]:tenv) t0) (open_ty' ([]:tenv) T3) (openq' ([]:tenv) d3)). {
           eapply narrowing. eapply H28. intuition. apply @s_trans with (T2:=T1) (d2:=q_trans_tenv [] df ⋒ q_trans_tenv [] d1); auto. apply stp_refl; auto. constructor; auto. apply closed_Qual_qor; auto. apply closed_Qual_qand; auto.
           apply stp_qstp_inv in H29. apply qstp_empty in H29. eapply Subq_trans; eauto. auto.
         }
         eapply @substitution2_ty with (dx:=d1'') in HT' as HT''; eauto; intuition.
         unfold open_tm' in HT''. unfold open_ty' in HT''. unfold openq' in HT''. simpl in HT''. inversion H26; inversion H27; subst.
         unfold open_ty in HT''. unfold openq in HT''.
         erewrite <- open_subst2_tm in HT''; eauto.
         erewrite <- open_subst2_ty in HT''; eauto.
         erewrite <- open_subst2_qual in HT''; eauto.
         fold (open_tm (ttabs t0) tunit t0) in HT''. fold (openq df1 (false,(qfvs d1),(qbvs d1),(qlocs d1)) d3) in HT''.
         apply @weaken_flt with (φ':= φ) in HT''; auto; intuition.
         eapply t_sub; eauto. rename H31 into Hsub. 3:{ unfold open_tm. rewrite local_locs_open'; auto. rewrite local_locs_open'; auto. eapply kill_sep_open2; eauto. }
         eapply @substitution_stp2 in Hsub; eauto.
         simpl in Hsub. unfold openq' in Hsub. unfold openq in Hsub. simpl in Hsub.
         unfold open_ty' in Hsub. unfold open_ty in Hsub.
         erewrite <- open_subst2_ty in Hsub; eauto. erewrite <- open_subst2_ty in Hsub; eauto.
         erewrite <- open_subst2_qual in Hsub; eauto. erewrite <- open_subst2_qual in Hsub; eauto.
         fold (openq df1 (false,(qfvs d1),(qbvs d1),(qlocs d1)) d3) in Hsub. fold (openq df1 (false,(qfvs d1),(qbvs d1),(qlocs d1)) d2) in Hsub.
         fold (open_ty (TAll d0 d3 T0 T3) df1 T1 (false,(qfvs d1),(qbvs d1),(qlocs d1)) T3) in Hsub. fold (open_ty (TAll d0 d3 T0 T3) df1 T1 (false,(qfvs d1),(qbvs d1),(qlocs d1)) T2) in Hsub.
         fold (open_ty (TAll d0 d3 T0 T3) df1 T1 (false,(qfvs d1),(qbvs d1),(qlocs d1)) T3).
         (* need to reason about growth of d1 *)
         { destruct (♦∈? d1) eqn:Hfresh.
         ++ (* d1 fresh, so the function can't be dependent on the argument *)
            intuition. replace (T2 <~ᵀ TUnit ~ ∅; T1 ~ d1) with T2. replace (T2 <~ᵀ (TAll d0 d3 T0 T3) ~ df1; T1 ~ (false,(qfvs d1),(qbvs d1),(qlocs d1))) with T2 in Hsub. (* since no dependence *)
            eapply s_trans; eauto. apply stp_refl; auto. apply not_free_prop3; auto. apply not_free_prop3; auto.
            constructor; auto. eapply openq_mono; eauto.
            all : unfold open_ty; rewrite not_free_prop1; auto. all : rewrite not_free_prop1; auto.
         ++ (* d1 non-fresh *)
            assert (Hd1 : (false,(qfvs d1),(qbvs d1),(qlocs d1))= d1). { apply Q_lift_eq. clear - Hfresh. Qcrush; eauto. }
            rewrite Hd1 in *. replace (T2 <~ᵀ TUnit ~ ∅; T1 ~ d1) with (T2 <~ᵀ (TAll d0 d3 T0 T3) ~ df1; T1 ~ d1). (* since no dependence *)
            eapply s_trans; eauto. apply stp_refl; auto. apply closed_ty_open2; auto. constructor; auto.
            eapply openq_mono; eauto.
            unfold open_ty. f_equal. auto.
         }
         eapply has_type_filter in H as dfFil. eapply openq_subqual; eauto using closed_Qual_qor.
         eapply has_type_filter in H.
         assert (Hbdf1: df1 ⊑↑ φ ⊔ {♦}). eapply Subq_trans; eauto. assert (Hbd1: d1 ⊑↑ φ ⊔ {♦}). auto.
         qual_destruct φ. qual_destruct df1. qual_destruct d1.
         unfold_q. unfold_Q. apply Is_true_eq_false in H38; subst.
         unfold_N. destruct Hbdf1 as [? [? [? ?]]]. destruct Hbd1 as [? [? [? ?]]].
         repeat split; auto; intros ? Hpp; rewrite N_lift_or in Hpp; unfold N_lift in *;
           destruct Hpp; try rewrite <- N_lift_n_or_empty_right; intuition.
         subst. Qcrush.
         unfold open_tm'. rewrite local_locs_open'; auto. rewrite local_locs_open'; auto. eapply kill_sep_sub; eauto.
         unfold open_tm'. rewrite local_locs_open'; auto. rewrite local_locs_open'; auto. simpl in Hwfstep. rewrite Hwfstep. unfold kill_sep; clear; Qcrush.
         apply qstp_empty in H30. apply has_type_filter in H; auto. eapply kill_sep_sub_fresh. eapply Subq_trans; eauto. auto.
         apply qstp_empty in H30. eapply kill_sep_sub; eauto.
         eapply wf_step_preserve; eauto. econstructor; eauto.
     + (* left congruence *)
        apply has_type_closed in H as Hcl. intuition.
        specialize (H13 σ H15 H16). destruct H13 as [t1' [σ' HH1]]. exists (ttapp t1'). exists σ'. intuition. apply step_c_tapp. intuition.
        inversion H15. subst. destruct H24. destruct (♦∈? df) eqn:Hfresh.
        * (* df fresh *)
          ndestruct (qbvs d2 0).
          -- (* d2 dependent on f *) apply (Preserve Σ' d' φ' ϰ'); auto.
            eapply disjointq_scale; eauto. eapply openq_subqual_0; eauto.
            erewrite @openq_duplicate_eq_l with (l:=‖Σ'‖) (f:=0); auto. 2,3 : eapply closed_qual_monotone; eauto. 2: eauto.
            inversion H28; subst.
            ++ (*base*) eapply disjointq_same in H32; auto. 2: eapply H15. 2: eapply H31. destruct H32. subst. repeat rewrite qqplus_qbot_right_neutral in *.
              apply t_tapp_fresh; auto. 1-2: rewrite H38; auto.
              eapply kill_sep_local_locs_base; eauto.
              eapply kill_sep_local_locs_base; eauto.
              eapply kill_sep_local_locs_base; eauto.
            ++ (*fresh*) eapply disjointq_grow in H32 as ?; auto. 2: eapply H15. 2: eapply H31.
              apply t_sub with (T1 := (T2 <~ᵀ TUnit ~ ∅; T1 ~ d1)) (d1 := (openq (df ⋓ d') d1 d2)).
              ** eapply t_tapp_fresh with (T1:=T1). replace (q_trans_tenv [] (df ⋓ d')) with (df ⋓ d'); auto. replace (q_trans_tenv [] d1) with d1; auto. erewrite <- @qqcap_fresh_l with (Σ':=([(T, q)] :: Σ)); eauto.
                unfold q_trans_tenv in *. simpl in *.
                eapply closed_ty_monotone; eauto. eapply closed_Qual_monotone; eauto.
                all: auto.
                eauto using Subq_trans.
                eauto using Subq_trans.
                apply Qor_bound; auto. apply has_type_closed in H33. intuition. eapply @Subq_trans with (d2:=q_trans_tenv [] d1). clear; Qcrush. unfold q_trans_tenv. simpl. eapply Subq_trans. eapply H2. clear; Qcrush.
                1-3: destruct H15 as [? [Hlen ?]]. 1-3: inversion H18; subst. 1-2: rewrite <- Hlen in H1, H47, H48.
                eapply kill_sep_local_locs_grow; eauto. eapply kill_sep_local_locs_grow; eauto.
                eapply kill_sep_local_locs_trans_tenv. 9: eauto. 1-6: eauto. auto. apply has_type_closed in H. intuition.
              ** apply has_type_closed in H33. intuition. inversion H22. subst.
                apply stp_refl. simpl. eapply closed_ty_monotone; eauto.
                constructor; auto. apply closed_Qual_qqplus; auto. apply openQ_closed.
                eauto using closed_Qual_monotone. apply closed_Qual_qqplus; eauto. 1,2: eapply closed_Qual_monotone; eauto.
              ** apply has_type_filter in H. apply Qqplus_bound.
                apply has_type_closed in H33. intuition. apply closed_Qual_qor_fresh in H39.
                eapply openq_subqual_trans'2. apply H17. all: eauto. eapply Subq_trans; eauto.
              ** (*t_sub requirement*) apply has_type_local_loc_sep in H33 as Hlc. replace ((df ⋓ d')) with (df ⊔ d') in *. 2: {clear - Hfresh; Qcrush. rewrite Hfresh; auto. }
                apply kill_sep_qor_rev in Hlc. destruct Hlc. apply kill_sep_qqplus_bound; auto. simpl.
                destruct H15 as [? [Hlen ?]]. inversion H18; subst.
                eapply kill_sep_open2. 2: apply closed_Qual_qor; auto. 3: eapply disjointq_closed; eauto. 1-3: eapply closed_Qual_monotone; eauto. apply has_type_closed in H33; intuition. eapply closed_tm_monotone; eauto.
                eapply kill_sep_local_locs_grow; eauto. rewrite Hlen; eauto. eapply kill_sep_local_locs_grow; eauto. rewrite Hlen; eauto. apply kill_sep_qor; auto.
            ++ (*kill*) eapply disjointq_same in H32; auto. 2: eapply H15. 2: eapply H31. destruct H32. subst. repeat rewrite qqplus_qbot_right_neutral in *.
              apply t_tapp_fresh; auto. simpl in Hwfstep.
              eapply q_remove_sub'; eauto. eapply kill_sep_kill_sub. 2: eauto. clear - H38; Qcrush; subst; auto.
              eapply q_remove_sub'; eauto. eapply kill_sep_open_empty' with (Σ:=Σ'). clear - H37; Qcrush. eapply kill_sep_kill_sub. 2: eauto. clear - H38; Qcrush; subst; auto.
              eapply q_remove_sub'; eauto. eapply kill_sep_kill_sub. 2: eauto. clear - H38; Qcrush; subst; auto.
              eapply kill_sep_local_locs_base; eauto. eapply kill_sep_local_locs_base; eauto.
              eapply kill_sep_local_locs_base; eauto.
          -- (* d2 not dependent on f *)
             inversion H18. subst.
             apply (Preserve Σ' ∅ φ' ϰ'); auto. rewrite qqplus_qbot_right_neutral.
             replace (d2 <~ᵈ df; d1) with (d2 <~ᵈ df ⋓ d'; d1). 2:eapply openq_subqual_0_false; auto.
             inversion H28; subst.
            ++ eapply disjointq_same in H32; auto. 2: eapply H15. 2: eapply H31. destruct H32. subst. repeat rewrite qqplus_qbot_right_neutral in *.
              apply t_tapp_fresh; auto. 1-2: rewrite H38; auto.
              eapply kill_sep_local_locs_base; eauto.
              eapply kill_sep_local_locs_base; eauto.
              eapply kill_sep_local_locs_base; eauto.
            ++ (*fresh*) eapply disjointq_grow in H32 as ?. 2: eapply H15. 2: eapply H31.
              eapply t_tapp_fresh with (T1:=T1). replace (q_trans_tenv [] (df ⋓ d')) with (df ⋓ d'); auto. replace (q_trans_tenv [] d1) with d1; auto. erewrite <- @qqcap_fresh_l with (Σ':=([(T, q)] :: Σ)); eauto.
              unfold q_trans_tenv in *. simpl in *.
              all: auto.
              eapply closed_ty_monotone; eauto.
              eapply closed_Qual_monotone; eauto.
              eauto using Subq_trans.
              eauto using Subq_trans.
              apply Qor_bound; auto. apply has_type_closed in H33. intuition. eapply @Subq_trans with (d2:=q_trans_tenv [] d1). Qcrush. unfold q_trans_tenv. simpl. eapply Subq_trans. eapply H2. rewrite qor_assoc_23. clear. Qcrush.
              1-3: destruct H15 as [? [Hlen ?]]. 1-3: inversion H18; subst. 1-2: rewrite <- Hlen in H1, H51, H52.
                  eapply kill_sep_local_locs_grow; eauto. eapply kill_sep_local_locs_grow; eauto.
                  eapply kill_sep_local_locs_trans_tenv. 9: eauto. 1-6: eauto. auto. apply has_type_closed in H. intuition.
            ++ (*kill*) eapply disjointq_same in H32; auto. 2: eapply H15. 2: eapply H31. destruct H32. subst. repeat rewrite qqplus_qbot_right_neutral in *.
              apply t_tapp_fresh; auto. simpl in Hwfstep.
              eapply q_remove_sub'; eauto. eapply kill_sep_kill_sub. 2: eauto. clear - H38; Qcrush; subst; auto.
              eapply q_remove_sub'; eauto. eapply kill_sep_open_empty' with (Σ:=Σ'). clear - H37; Qcrush. eapply kill_sep_kill_sub. 2: eauto. clear - H38; Qcrush; subst; auto.
              eapply q_remove_sub'; eauto. eapply kill_sep_kill_sub. 2: eauto. clear - H38; Qcrush; subst; auto.
              eapply kill_sep_local_locs_base; eauto. eapply kill_sep_local_locs_base; eauto.
              eapply kill_sep_local_locs_base; eauto.
        * (* df not fresh *) rewrite not_fresh_qqplus in H33; auto. apply (Preserve Σ' ∅ φ' ϰ'); auto.
          rewrite qqplus_qbot_right_neutral. inversion H28; subst.
          ++ eapply disjointq_same in H32; auto. 2: eapply H15. 2: eapply H31. destruct H32. subst. repeat rewrite qqplus_qbot_right_neutral in *.
            apply t_tapp_fresh; auto. 1-2: rewrite H37; auto.
            eapply kill_sep_local_locs_base; eauto.
            eapply kill_sep_local_locs_base; eauto.
            eapply kill_sep_local_locs_base; eauto.
          ++ eapply disjointq_grow in H32 as ?; auto. 2: eapply H15. 2: eapply H31.
            eapply t_tapp_fresh with (T1:=T1).
            unfold q_trans_tenv in *. simpl in *.
            eapply weaken_2D_store; eauto. all: auto.
            apply closed_qenv_empty. apply [].
            eapply closed_ty_monotone; eauto.
            eapply closed_Qual_monotone; eauto.
            eauto using Subq_trans.
            eauto using Subq_trans.
            apply Qor_bound; auto. apply has_type_closed in H33. intuition.
            eapply @Subq_trans with (d2:=q_trans_tenv [] d1). Qcrush. unfold q_trans_tenv. simpl.
            eapply Subq_trans. eapply H2. Qcrush. (*slow*)
            1-3: destruct H15 as [? [Hlen ?]]. 1-3: inversion H18; subst. 1-3: rewrite <- Hlen in H1, H46, H47.
            eapply kill_sep_local_locs_grow; eauto. eapply kill_sep_local_locs_grow; eauto.
            eapply kill_sep_local_locs_grow; eauto. rewrite qand_commute. eauto.
          ++ eapply disjointq_same in H32; auto. 2: eapply H15. 2: eapply H31. destruct H32. subst. repeat rewrite qqplus_qbot_right_neutral in *.
            apply t_tapp_fresh; auto. simpl in Hwfstep.
            eapply q_remove_sub'; eauto. eapply kill_sep_kill_sub. 2: eauto. clear - H37; Qcrush; subst; auto.
            eapply q_remove_sub'; eauto. eapply kill_sep_open_empty' with (Σ:=Σ'). clear - H36; Qcrush. eapply kill_sep_kill_sub. 2: eauto. clear - H37; Qcrush; subst; auto.
            eapply q_remove_sub'; eauto. eapply kill_sep_kill_sub. 2: eauto. clear - H37; Qcrush; subst; auto.
            eapply kill_sep_local_locs_base; eauto. eapply kill_sep_local_locs_base; eauto.
            eapply kill_sep_local_locs_base; eauto.

   - (* tvar *)  subst. inversion H.

   - (* tapp *) right. subst. intuition. remember (qdiff φ (local_locs t1)) as φd. symmetry in Heqφd. apply (qdiff_local_loc_prop) in Heqφd as Heqφd'; destruct Heqφd'.
     assert (Hwfs1: wf_step t1). {simpl in Hwfstep; intuition. } assert (Hwfs2: wf_step t2). {simpl in Hwfstep; intuition. }
     apply has_type_closed in H as HH. intuition. apply has_type_closed in H0 as HH0. intuition.
     apply (CtxOK_kill_closed) in H12 as Hclϰ. apply (CtxOK_kill_sep) in H12 as Hwfkill.
     (* t1 *) specialize (H11 (TFun d1 d2 T1 T2) t1). intuition.

     (* t2 *) specialize (H9 T1 t2). intuition.
     + (* contraction *)
       (* turn has_type to vtp *)
       apply (has_type_vtp Hclϰ) in H as VH; intuition.
       pose (VHH := VH). inversion VH. subst.
       specialize (has_type_filter H0) as Hflt0.
       apply (has_type_vtp Hclϰ) in H0 as VH0; intuition.
       exists (open_tm (tabs t) t2 t). exists σ. intuition.
       * constructor. intuition.
       * apply (Preserve Σ ∅ φ ϰ); auto.  rewrite qqplus_qbot_right_neutral.
         apply qstp_closed in H34 as H32'; intuition.
         change (length []) with 0 in *. subst.
         pose (VH' := H32). eapply t_abs with (φ:=df1) in VH'; eauto. apply (has_type_vtp Hclϰ) in VH'; auto.
         assert (HT' : has_type [(bind_tm, false, T1, d1) ; (bind_tm, true, TFun d0 d3 T0 T3, df1)] (df1 ⊔ $!0 ⊔ $!1) Σ (open_tm' ([]:tenv) t) (open_ty' ([]:tenv) T3) (openq' ([]:tenv) d3)). {
           eapply narrowing. eapply H32. intuition. auto. apply stp_qstp_inv in H33. eapply qstp_empty; eauto. auto.
         }
         eapply @substitution1 with ( vx:= t2) in HT' as HT''; eauto; intuition.
         unfold open_tm' in HT''. unfold open_ty' in HT''. unfold openq' in HT''. simpl in HT''. inversion H30; subst. inversion H31. subst.
         unfold open_ty in HT''. unfold openq in HT''.
         erewrite <- open_subst2_tm in HT''; eauto.
         erewrite <- open_subst2_ty in HT''; eauto.
         erewrite <- open_subst2_qual in HT''; eauto.
         fold (open_tm (tabs t) t2 t) in HT''. fold (openq df1 d1 d3) in HT''. fold (open_ty (TFun d0 d3 T0 T3) df1 T1 d1 T3) in HT''.
         apply @weaken_flt with (φ':= φ) in HT''; auto; intuition.
         eapply t_sub; eauto. 3:{ unfold open_tm. rewrite local_locs_open'; auto. rewrite local_locs_open'; auto. 2: apply wf_step_value; auto. eapply kill_sep_open2; eauto. apply kill_sep_kill_qor_rev in H6; destruct H6. auto.
          apply has_type_local_loc_sep in H0. eapply kill_sep_sub_fresh; eauto.  }
         pose (Hsub:=H35). eapply @substitution_stp1 with (df:=df1) in Hsub; eauto.
         simpl in Hsub. unfold openq' in Hsub. unfold openq in Hsub. unfold open_ty' in Hsub. unfold open_ty in Hsub. simpl in Hsub.
         erewrite <- open_subst2_ty in Hsub; eauto. erewrite <- open_subst2_ty in Hsub; eauto.
         erewrite <- open_subst2_qual in Hsub; eauto. erewrite <- open_subst2_qual in Hsub; eauto.
         unfold open_ty. unfold openq.
         replace ([[0 ~> TUnit ~ ∅ ]]ᵀ T2) with ([[0 ~> TFun d0 d3 T0 T3 ~ df1 ]]ᵀ T2); auto. (* since not_free 0 T2 *)
         eapply s_trans; eauto. apply stp_refl; auto. apply closed_ty_open2; auto.
         constructor. eapply openq_mono; eauto. apply qstp_empty in H34. auto. apply openq_closed; auto.
         eapply has_type_closed in HT''. intuition. eapply closed_Qual_qor_fresh in H26.
         eapply openq_subqual; eauto. apply has_type_filter in H. eauto. eapply Subq_trans; eauto.
         apply Qor_bound; auto. apply has_type_filter in H.
         apply qstp_empty in H34. assert (df1 ⊑↑ φ ⊔ {♦}). eapply Subq_trans; eauto.
         eapply Subqual_non_fresh; eauto. eapply Subqual_non_fresh; eauto. eapply Subq_trans; eauto.
         apply wf_step_value; auto. 1-2: simpl in H5, H6.
         unfold open_tm'. rewrite local_locs_open'; auto. rewrite local_locs_open'; auto. eapply kill_sep_sub_fresh; eauto.
         unfold open_tm'. rewrite local_locs_open'; auto. rewrite local_locs_open'; auto. apply qstp_empty in H34. apply wf_step_value in H11; auto. simpl in H11. rewrite H11. unfold kill_sep; clear; Qcrush.
         apply wf_step_value in H11; auto. simpl in H11. simpl. rewrite H11. clear; Qcrush.
         apply qstp_empty in H34. apply has_type_filter in H; auto. eapply kill_sep_sub_fresh. eapply Subq_trans; eauto. auto.
         apply qstp_empty in H34. eapply kill_sep_sub; eauto.
         eapply wf_step_preserve. 3: econstructor; eauto. eauto. auto.
       * simpl. eapply kill_sep_sub; eauto.
     + (* right congruence *)
       apply (has_type_vtp Hclϰ) in H as VH; intuition. apply vtp_canonical_form_lam in VH as HH; intuition. apply wf_step_value in H11 as Hllt1; auto. rewrite Hllt1 in Heqφd. rewrite qdiff_empty in Heqφd. symmetry in Heqφd; subst.
       pose (HH12 := H11). unfold CtxOK in HH12. specialize (H9 σ H12 H13). intuition.
       destruct H9 as [t2' [σ' HH9]]. exists (tapp t1 t2'). exists σ'. intuition. constructor; intuition.
       (* d1 is not fresh, so we don't observe the growth *)
       destruct H23. apply (Preserve Σ' ∅ (φ') ϰ'); auto. simpl. rewrite Hllt1. rewrite qor_empty_left; auto.
       inversion H25; subst.
       -- (*base*) eapply disjointq_same in H29 as H29'; auto. 2: eapply H12. 2: eapply H28. destruct H29'; subst.
        rewrite qqplus_qbot_right_neutral. eapply t_app; auto.
        eapply weaken_2D_store with (Σ':=Σ'); eauto. apply closed_qenv_empty; apply [].
        rewrite Hllt1. rewrite qdiff_empty; auto. rewrite qqplus_qbot_right_neutral in H30. auto.
        eapply kill_sep_local_locs_base; eauto.
        rewrite Hllt1 in *. rewrite qor_empty_left. rewrite qor_empty_left in H6. eapply kill_sep_local_locs_base; eauto.
       -- (*fresh*) eapply disjointq_grow in H29 as H29'. 2: eapply H12. 2: eapply H28.
          rewrite not_fresh_qqplus in H30; auto. rewrite qqplus_qbot_right_neutral.
          eapply t_app with (T1:=T1); eauto. eapply weaken_flt. eapply weaken_2D_store.  eapply H. all: auto.
          apply closed_qenv_empty. apply [].
          eapply closed_Qual_qor. eapply closed_Qual_monotone; eauto. simpl; clear; Qcrush.
          eapply Subq_trans; eauto.
          rewrite Hllt1. rewrite qdiff_empty; auto.
          eapply kill_sep_local_locs_grow; eauto. destruct H12 as [? [Hlen ?]]. rewrite Hlen. apply has_type_filter in H; intuition; eauto.
          rewrite Hllt1 in *. rewrite qor_empty_left. rewrite qor_empty_left in H6. eapply kill_sep_local_locs_grow; eauto. destruct H12 as [? [Hlen ?]]. rewrite Hlen. inversion H17; subst; eauto.
       -- (*kill*) eapply disjointq_same in H29 as H29'; auto. 2: eapply H12. 2: eapply H28. destruct H29'; subst.
          rewrite qqplus_qbot_right_neutral. rewrite qqplus_qbot_right_neutral in H30.
          assert (kill_sep &!l df). { eapply kill_sep_kill_sub. 2: eauto. clear - H34. Qcrush. subst; auto. }
          eapply t_app; eauto.
          { apply has_type_local_loc_sep in H as Hcl.
            apply has_type_filter in H as H'; intuition. eapply (has_type_vtp Hclϰ) in H; eauto. eapply weaken_flt. eapply vtp_non_fresh in H; auto. eapply t_sub with (d1:= (false, qfvs df, qbvs df, qlocs df)). 4: auto. eapply vtp_has_type; eauto. apply stp_refl; auto. apply qs_sq; auto.
           clear; Qcrush. clear; Qcrush.
           eapply q_remove_sub; auto.
            clear - H'; Qcrush. specialize (H1 x H2). rewrite or_false_elim in H1; auto. specialize (H0 x H2). rewrite or_false_elim in H0; auto. specialize (H3 x H2); rewrite or_false_elim in H3; auto.
            eapply kill_sep_sub. 2: eauto. clear; Qcrush.
            eapply closed_Qual_sub. 2: eapply q_remove_smaller; auto. auto. }
          eapply q_remove_sub'; eauto. eapply kill_sep_open_empty' with (Σ:=Σ'). clear - H33. Qcrush. apply kill_sep_kill_qor_rev in H6; destruct H6. eapply kill_sep_kill_sub. 2: eauto. clear - H34. Qcrush; subst; auto.
          rewrite Hllt1; rewrite qdiff_empty; auto.
          eapply kill_sep_local_locs_base; eauto.
          rewrite Hllt1. rewrite Hllt1 in H6. rewrite qor_empty_left in H6. rewrite qor_empty_left. eapply kill_sep_local_locs_base; eauto.
        -- (*wf_step*) constructor; auto.

     + (* left congruence *)
       apply has_type_closed in H0 as Hcl. intuition.
       specialize (H11 σ H12 H13). destruct H11 as [t1' [σ' HH7]]. exists (tapp t1' t2). exists σ'. intuition. apply step_c_app_l. intuition.
       simpl in Hwfstep. destruct Hwfstep as [Hwft1 [Hwft2 Hwfstep]]. destruct Hwfstep. apply value_unsteppable in H11; auto; lia. rename H29 into Hwfstep.
       destruct H27. ndestruct (qbvs d2 0).
       * (* d2 is dependent on f, so the growth in df might be observable  *)
         inversion H17. subst.  (* this is the sole reason why need to distinguish whether d2 is dependent on f or not *)
         destruct (♦∈? df) eqn:Hfresh.
        ** apply (Preserve Σ' d' φ' ϰ'); auto. simpl. rewrite Hwfstep. rewrite qor_empty_right. auto.
          eapply disjointq_scale; eauto. eapply openq_subqual_0; eauto.
          erewrite @openq_duplicate_eq_l with (f:=0) (l:=‖Σ'‖). 3,4 : eapply closed_qual_monotone; eauto. 2,3 : eauto.
          inversion H29; subst.
          ++ (*base*) eapply disjointq_same in H33; auto. 2: eapply H12. 2: eapply H32. destruct H33. subst. repeat rewrite qqplus_qbot_right_neutral in *.
            apply t_app with (φd:=(qdiff φ' (local_locs t1'))); auto.
            eapply weaken_2D_store with (Σ':=Σ'); eauto. 2: apply closed_qenv_empty; apply [].
            eapply weaken_flt. eauto. eapply qdiff_subqual_rev_monotone. eapply local_locs_step_same. 4: eauto. 1-3: auto.
            eapply closed_Qual_sub. eapply H16. (*φ'*) clear; Qcrush.
            rewrite Hwfstep. rewrite qor_empty_right. rewrite Hwfstep in H6. rewrite qor_empty_right in H6. eapply kill_sep_local_locs_base; eauto.
          ++ (*fresh*) eapply disjointq_grow in H33 as H33'; auto. 2: eapply H12. 2: eapply H32.
            eapply t_sub with (T1 := (T2 <~ᵀ TUnit ~ ∅; T1 ~ d1))(d1 := (openq (df ⋓ d') d1 d2)).
            --- eapply t_app with (T1:=T1) (df:=(df ⋓ d')); eauto.
                eapply weaken_flt. eapply weaken_2D_store. eauto. auto.
                apply closed_qenv_empty; apply []. eapply wf_senv_closed_qenv_qn; eauto.
                eapply (@Subq_trans _ (qdiff (φ ⊔ &! (‖ Σ ‖)) (local_locs t1 ⊔ &! (‖ Σ ‖)))). 2: eapply qdiff_subqual_rev_monotone. eapply qdiff_incr; eauto. destruct H12 as [? [Hlen ?]]. rewrite <- Hlen. eapply local_locs_step_grow; eauto.
                eapply closed_Qual_qdiff; simpl. eapply closed_Qual_qor. eapply closed_Qual_monotone; eauto. clear; Qcrush. eapply local_locs_closed. apply has_type_closed in H34; intuition; eauto.
                eapply Subq_trans; eauto.
                rewrite Hwfstep. unfold kill_sep. clear. Qcrush.
                rewrite Hwfstep. rewrite qor_empty_right. rewrite Hwfstep in H6. rewrite qor_empty_right in H6. eapply kill_sep_local_locs_grow; eauto. destruct H12 as [? [Hlen ?]]. rewrite Hlen. eauto.
            --- apply stp_refl. simpl. eapply closed_ty_monotone; eauto.
                constructor; auto. apply closed_qual_qqplus; auto.
                apply openq_closed. 2 : apply closed_qual_qqplus.
                1,2,4 : eapply closed_qual_monotone; eauto; lia. all: eapply disjointq_closed; eauto.
            --- apply has_type_filter in H0. apply has_type_filter in H. apply Qqplus_bound.
                eapply has_type_closed in H34. intuition. eapply closed_Qual_qor_fresh in H39.
                eapply openq_subqual_trans'. eapply H4. all: eauto.
                eapply Subqual_non_fresh; eauto. eapply Subq_trans; eauto. Qcrush. (*slow*)
            --- (*t_sub requirement*) apply has_type_local_loc_sep in H34 as Hlc. replace ((df ⋓ d')) with (df ⊔ d') in *. 2: {clear - Hfresh; Qcrush. rewrite Hfresh; auto. }
              apply kill_sep_qor_rev in Hlc. destruct Hlc. apply kill_sep_qqplus_bound; auto. simpl. rewrite Hwfstep. rewrite qor_empty_right.
              destruct H12 as [? [Hlen ?]].
              eapply kill_sep_open2. 2: apply closed_Qual_qor; auto. 3: eapply disjointq_closed; eauto. 1-3: eapply closed_Qual_monotone; eauto. apply has_type_closed in H34; intuition. eapply closed_tm_monotone; eauto.
              eapply kill_sep_local_locs_grow; eauto. rewrite Hlen; eauto. apply kill_sep_kill_qor_rev in H6; destruct H6; auto.
              eapply kill_sep_local_locs_grow; eauto. rewrite Hlen; eauto. apply has_type_filter in H0. eapply kill_sep_sub_fresh; eauto.
              apply kill_sep_qor; auto.
              simpl. rewrite Hwfstep. rewrite qor_empty_right; auto.
          ++ (*kill*) eapply disjointq_same in H33; auto. 2: eapply H12. 2: eapply H32. destruct H33. subst. repeat rewrite qqplus_qbot_right_neutral in *.
            apply t_app with (φd:=(qdiff (q_remove Σ' l φ) (local_locs t1'))); auto.
            eapply weaken_flt. eauto. { eapply (@Subq_trans _ (qdiff (q_remove Σ' l φ) (local_locs t1))). eapply qdiff_remove; auto. eauto. apply qdiff_subqual_rev_monotone. eapply local_locs_step_same. 4: eauto. 1-3: auto. }
            eapply closed_Qual_qdiff; simpl. eapply closed_Qual_sub. 2: eapply q_remove_smaller. auto. eapply local_locs_closed. apply has_type_closed in H34; intuition; eauto.
            eapply q_remove_sub'; eauto. apply kill_sep_open_empty' with (Σ:=Σ'); auto. clear - H38. Qcrush. eapply kill_sep_kill_sub. 2: eauto. rewrite Hwfstep. rewrite qor_empty_right. clear - H39. Qcrush; subst; auto.
            rewrite Hwfstep. rewrite qor_empty_right. rewrite Hwfstep in H6. rewrite qor_empty_right in H6. eapply kill_sep_local_locs_base; eauto.
          ++ (*wf_step*) constructor; auto.
        ** apply (Preserve Σ' ∅ φ' ϰ'); auto. simpl. rewrite Hwfstep. rewrite qor_empty_right. auto. rewrite qqplus_qbot_right_neutral.
          rewrite not_fresh_qqplus in H34; auto.
            inversion H29; subst.
          ++ (*base*) eapply disjointq_same in H33; auto. 2: eapply H12. 2: eapply H32. destruct H33. subst. repeat rewrite qqplus_qbot_right_neutral in *.
            apply t_app with (φd:=(qdiff φ' (local_locs t1'))); auto.
            eapply weaken_2D_store with (Σ':=Σ'); eauto. 2: apply closed_qenv_empty; apply [].
            eapply weaken_flt. eauto. eapply qdiff_subqual_rev_monotone. eapply local_locs_step_same with (σ:=σ); eauto.
            eapply closed_Qual_sub. eapply H16. (*φ'*) clear; Qcrush.
            rewrite Hwfstep. rewrite qor_empty_right. rewrite Hwfstep in H6. rewrite qor_empty_right in H6. eapply kill_sep_local_locs_base; eauto.
          ++ (*fresh*) eapply disjointq_grow in H33 as H33'. 2: eapply H12. 2: eapply H32.
            eapply t_app with (T1:=T1) (df:=(df)); eauto.
            eapply weaken_flt. eapply weaken_2D_store. 2: eauto. eauto. auto.
            apply closed_qenv_empty; apply []. eapply wf_senv_closed_qenv_qn; eauto.
            eapply (@Subq_trans _ (qdiff (φ ⊔ &! (‖ Σ ‖)) (local_locs t1 ⊔ &! (‖ Σ ‖)))). 2: eapply qdiff_subqual_rev_monotone. eapply qdiff_incr; eauto. destruct H12 as [? [Hlen ?]]. rewrite <- Hlen. eapply local_locs_step_grow; eauto.
            eapply closed_Qual_qdiff; simpl. eapply closed_Qual_qor. eapply closed_Qual_monotone; eauto. clear; Qcrush. eapply local_locs_closed. apply has_type_closed in H34; intuition; eauto.
            eapply Subq_trans; eauto.
            rewrite Hwfstep. rewrite qor_empty_right. rewrite Hwfstep in H6. rewrite qor_empty_right in H6. eapply kill_sep_local_locs_grow; eauto. destruct H12 as [? [Hlen ?]]. rewrite Hlen. eauto.
          ++ (*kill*) eapply disjointq_same in H33; auto. 2: eapply H12. 2: eapply H32. destruct H33. subst. repeat rewrite qqplus_qbot_right_neutral in *.
            apply t_app with (φd:=(qdiff (q_remove Σ' l φ) (local_locs t1'))); auto.
            eapply weaken_flt. eauto. { eapply (@Subq_trans _ (qdiff (q_remove Σ' l φ) (local_locs t1))). eapply qdiff_remove; auto. eauto. apply qdiff_subqual_rev_monotone. eapply local_locs_step_same with (σ:=σ); eauto. }
            eapply closed_Qual_qdiff; simpl. eapply closed_Qual_sub. 2: eapply q_remove_smaller. auto. eapply local_locs_closed. apply has_type_closed in H34; intuition; eauto.
            eapply q_remove_sub'; eauto. apply kill_sep_open_empty' with (Σ:=Σ'); auto. clear - H38. Qcrush. eapply kill_sep_kill_sub. 2: eauto. rewrite Hwfstep. rewrite qor_empty_right. clear - H39. Qcrush; subst; auto.
            rewrite Hwfstep. rewrite qor_empty_right. rewrite Hwfstep in H6. rewrite qor_empty_right in H6. eapply kill_sep_local_locs_base; eauto.
          ++ (*wf_step*) constructor; auto.
       * (* d2 is not dependent on f, so we don't observe the growth in df *)
         inversion H17. subst. apply (Preserve Σ' ∅ φ' ϰ'); auto. simpl. rewrite Hwfstep. rewrite qor_empty_right. auto. rewrite qqplus_qbot_right_neutral.
         replace (d2 <~ᵈ df; d1) with (d2 <~ᵈ df ⋓ d'; d1). (* since f doesn't occur in d2 *) 2: apply openq_subqual_0_false; auto.
         inversion H29; subst.
         ++ eapply disjointq_same in H33; auto. 2: eapply H12. 2: eapply H32. destruct H33. subst. repeat rewrite qqplus_qbot_right_neutral in *.
          apply t_app with (φd:=(qdiff φ' (local_locs t1'))); auto.
          eapply weaken_2D_store with (Σ':=Σ'); eauto. 2: apply closed_qenv_empty; apply [].
          eapply weaken_flt. eauto. eapply qdiff_subqual_rev_monotone. eapply local_locs_step_same with (σ:=σ); eauto.
          eapply closed_Qual_sub. eapply H16. (*φ'*) clear; Qcrush.
          rewrite Hwfstep. rewrite qor_empty_right. rewrite Hwfstep in H6. rewrite qor_empty_right in H6. eapply kill_sep_local_locs_base; eauto.
         ++ eapply disjointq_grow in H33 as H33'; auto. 2: eapply H12. 2: eapply H32.
            eapply t_app with (T1:=T1); eauto.
            eapply weaken_flt. eapply weaken_2D_store. 2: eauto. eauto. auto.
            apply closed_qenv_empty; apply []. eapply wf_senv_closed_qenv_qn; eauto.
            eapply (@Subq_trans _ (qdiff (φ ⊔ &! (‖ Σ ‖)) (local_locs t1 ⊔ &! (‖ Σ ‖)))). 2: eapply qdiff_subqual_rev_monotone. eapply qdiff_incr; eauto. destruct H12 as [? [Hlen ?]]. rewrite <- Hlen. eapply local_locs_step_grow; eauto.
            eapply closed_Qual_qdiff; simpl. eapply closed_Qual_qor. eapply closed_Qual_monotone; eauto. clear; Qcrush. eapply local_locs_closed. apply has_type_closed in H34; intuition; eauto.
            eapply Subq_trans; eauto.
            rewrite Hwfstep. unfold kill_sep. clear; Qcrush.
            rewrite Hwfstep. rewrite qor_empty_right. rewrite Hwfstep in H6. rewrite qor_empty_right in H6. eapply kill_sep_local_locs_grow; eauto. destruct H12 as [? [Hlen ?]]. rewrite Hlen. eauto.
         ++ eapply disjointq_same in H33; auto. 2: eapply H12. 2: eapply H32. destruct H33. subst. repeat rewrite qqplus_qbot_right_neutral in *.
          apply t_app with (φd:=(qdiff (q_remove Σ' l φ) (local_locs t1'))); auto.
          eapply weaken_flt. eauto. { eapply (@Subq_trans _ (qdiff (q_remove Σ' l φ) (local_locs t1))). eapply qdiff_remove; auto. eauto. apply qdiff_subqual_rev_monotone. eapply local_locs_step_same with (σ:=σ); eauto. }
          eapply closed_Qual_qdiff; simpl. eapply closed_Qual_sub. 2: eapply q_remove_smaller. auto. eapply local_locs_closed. apply has_type_closed in H34; intuition; eauto.
          eapply q_remove_sub'; eauto. apply kill_sep_open_empty' with (Σ:=Σ'); auto. clear - H38. Qcrush. eapply kill_sep_kill_sub. 2: eauto. rewrite Hwfstep. rewrite qor_empty_right. clear - H39. Qcrush; subst; auto.
          rewrite Hwfstep. rewrite qor_empty_right. rewrite Hwfstep in H6. rewrite qor_empty_right in H6. eapply kill_sep_local_locs_base; eauto.
         ++ (*wf_step*) constructor; auto.

   - (* t_app_fresh *) right. subst. intuition. remember (qdiff φ (local_locs t1)) as φd. symmetry in Heqφd. apply (qdiff_local_loc_prop) in Heqφd as Heqφd'; destruct Heqφd'.
     assert (Hwfs1: wf_step t1). {simpl in Hwfstep; intuition. } assert (Hwfs2: wf_step t2). {simpl in Hwfstep; intuition. }
     apply has_type_closed in H as HH. intuition. apply has_type_closed in H0 as HH0. intuition.
     apply (CtxOK_kill_closed) in H14 as Hclϰ. apply (CtxOK_kill_sep) in H14 as Hwfkill.
     (* t1 *) specialize (H13 (TFun (q_trans_tenv [] df ⋒ q_trans_tenv [] d1) d2 T1 T2) t1). intuition.
     (* t2 *) specialize (H11 T1 t2). intuition.
     + (* contraction *)
       (* turn has_type to vtp *)
       apply (has_type_vtp Hclϰ) in H as VH; intuition.
       pose (VHH := VH). inversion VH. subst.
       specialize (has_type_filter H0) as Hflt0.
       apply (has_type_vtp Hclϰ) in H0 as VH0; intuition.
       exists (open_tm (tabs t) t2 t). exists σ. intuition.
       * constructor. intuition.
       * apply (Preserve Σ ∅ φ ϰ); auto. rewrite qqplus_qbot_right_neutral.
         apply qstp_closed in H36 as H37'; intuition.
         change (length []) with 0 in *. subst.
         pose (VH' := H34). eapply t_abs with (φ:=df1) in VH'; eauto. apply (has_type_vtp Hclϰ) in VH'; auto.
         (* remove potential freshness flag from the argument, in order to apply substitution lemma *)
         apply vtp_non_fresh in VH0.
         remember (false,(qfvs d1),(qbvs d1),(qlocs d1)) as d1''.
         remember (false,(qfvs df),(qbvs df),(qlocs df)) as df''.
         assert (Hd1'' : d1'' ⊑↑ d1). { subst. Qcrush. }
         assert (Hdf'' : df'' ⊑↑ df). { subst. Qcrush. }
         assert (Hdf1 : df1 ⊑↑ df). { apply qstp_empty in H36. Qcrush. }
         assert (Hd1''fr : ♦∉ d1''). { subst. auto. }
         assert (Hdf''fr : ♦∉ df''). { subst. auto. }
         assert (Hqand: (q_trans_tenv [] df'' ⋒ q_trans_tenv [] d1'') ⊑↑ (q_trans_tenv [] df ⋒ q_trans_tenv [] d1)). {
           apply Subq_qor. apply Subq_qand_split; auto. all: apply q_trans_subq; eauto.
         }
         assert (HT' : has_type [(bind_tm, false, T1, q_trans_tenv [] df'' ⋒ q_trans_tenv [] d1''); (bind_tm, true, TFun d0 d3 T0 T3, df1)] (df1 ⊔ $!0 ⊔ $!1) Σ (open_tm' ([]:tenv) t) (open_ty' ([]:tenv) T3) (openq' ([]:tenv) d3)). {
           eapply narrowing. eapply H34. intuition. apply @s_trans with (T2:=T1) (d2:=q_trans_tenv [] df ⋒ q_trans_tenv [] d1); auto.
           apply stp_refl; auto. constructor; auto. apply closed_Qual_qor; auto. apply closed_Qual_qand; auto.
           apply stp_qstp_inv in H35. apply qstp_empty in H35. eapply Subq_trans; eauto. auto.
         }
         eapply @substitution2 with (vf:=tabs t) ( vx:= t2)  in HT' as HT''; intuition.
         unfold open_tm' in HT''. unfold open_ty' in HT''. unfold openq' in HT''. simpl in HT''. inversion H32; inversion H33; subst.
         unfold open_ty in HT''. unfold openq in HT''.
         erewrite <- open_subst2_tm in HT''; eauto.
         erewrite <- open_subst2_ty in HT''; eauto.
         erewrite <- open_subst2_qual in HT''; eauto.
         fold (open_tm (tabs t) t2 t) in HT''. fold (openq df1 (false,(qfvs d1),(qbvs d1),(qlocs d1)) d3) in HT''.
         apply @weaken_flt with (φ':=φ) in HT''; auto; intuition.
         eapply t_sub; eauto. 3:{ unfold open_tm. rewrite local_locs_open'; auto. rewrite local_locs_open'; auto. 2: apply wf_step_value; auto. eapply kill_sep_open2; eauto. apply kill_sep_kill_qor_rev in H7; destruct H7. auto.
          apply has_type_local_loc_sep in H0. eapply kill_sep_sub_fresh; eauto. }
         rename H37 into Hsub.
         eapply @substitution_stp2 with (dx := (false,(qfvs d1),(qbvs d1),(qlocs d1))) (df:=df1) in Hsub; eauto.
         simpl in Hsub. unfold openq' in Hsub. unfold openq in Hsub. simpl in Hsub.
         unfold open_ty' in Hsub. unfold open_ty in Hsub.
         erewrite <- open_subst2_ty in Hsub; eauto. erewrite <- open_subst2_ty in Hsub; eauto.
         erewrite <- open_subst2_qual in Hsub; eauto. erewrite <- open_subst2_qual in Hsub; eauto.
         fold (openq df1 (false,(qfvs d1),(qbvs d1),(qlocs d1)) d3) in Hsub. fold (openq df1 (false,(qfvs d1),(qbvs d1),(qlocs d1)) d2) in Hsub.
         fold (open_ty (TFun d0 d3 T0 T3) df1 T1 (false,(qfvs d1),(qbvs d1),(qlocs d1)) T3) in Hsub. fold (open_ty (TFun d0 d3 T0 T3) df1 T1 (false,(qfvs d1),(qbvs d1),(qlocs d1)) T2) in Hsub.
         fold (open_ty (TFun d0 d3 T0 T3) df1 T1 (false,(qfvs d1),(qbvs d1),(qlocs d1)) T3).
         (* need to reason about growth of d1 *)
         { destruct (♦∈? d1) eqn:Hfresh.
         ++ (* d1 fresh, so the function can't be dependent on the argument *)
            intuition. replace (T2 <~ᵀ TUnit ~ ∅; T1 ~ d1) with T2. replace (T2 <~ᵀ (TFun d0 d3 T0 T3) ~ df1; T1 ~ (false,(qfvs d1),(qbvs d1),(qlocs d1))) with T2 in Hsub. (* since no dependence *)
            eapply s_trans; eauto. apply stp_refl; auto. apply not_free_prop3; auto. apply not_free_prop3; auto.
            constructor; auto. eapply openq_mono; eauto.
            all : unfold open_ty; rewrite not_free_prop1; auto. all : rewrite not_free_prop1; auto.
         ++ (* d1 non-fresh *)
            assert (Hd1 : (false,(qfvs d1),(qbvs d1),(qlocs d1))= d1). { apply Q_lift_eq. clear - Hfresh. Qcrush; eauto. }
            rewrite Hd1 in *. replace (T2 <~ᵀ TUnit ~ ∅; T1 ~ d1) with (T2 <~ᵀ (TFun d0 d3 T0 T3) ~ df1; T1 ~ d1). (* since no dependence *)
            eapply s_trans; eauto. apply stp_refl; auto. apply closed_ty_open2; auto. constructor; auto.
            eapply openq_mono; eauto.
            unfold open_ty. f_equal. auto.
         }
         eapply has_type_filter in H as dfFil.
         eapply openq_subqual; eauto using closed_Qual_qor.
         apply has_type_filter in H0. eapply Subq_trans; eauto.
         eapply has_type_filter in H as dfFil.
         assert (Hbdf1: df1 ⊑↑ φ ⊔ {♦}). eapply Subq_trans; eauto.
         assert (Hbd1: d1 ⊑↑ φ ⊔ {♦}). apply has_type_closed in H0. eapply Subq_trans; eauto.
         qual_destruct φ. qual_destruct df1. qual_destruct d1.
         unfold_q. unfold_Q. apply Is_true_eq_false in H44; subst.
         unfold_N. destruct Hbdf1 as [? [? [? ?]]]. destruct Hbd1 as [? [? [? ?]]].
         repeat split; auto; intros ? Hpp; rewrite N_lift_or in Hpp; unfold N_lift in *;
           destruct Hpp; try rewrite <- N_lift_n_or_empty_right; intuition.
         qual_destruct df1. subst. qual_destruct df. simpl in *. Qcrush.
         assert (stp [] Σ (TFun d0 d3 T0 T3) df1 (TFun d0 d3 T0 T3) df). { apply stp_refl; auto. } subst.
         apply vtp_non_fresh. eapply vtp_widening. 4: eauto.
         all: subst; eauto.
         apply wf_step_value; auto. 1-2: simpl in H7, H8. 1-2: apply wf_step_value in H13; auto; simpl in H13.
         unfold open_tm'. rewrite local_locs_open'; auto. rewrite local_locs_open'; auto. eapply kill_sep_fresh_irrlevance; eauto. rewrite H13. unfold kill_sep; clear; Qcrush.
         unfold open_tm'. rewrite local_locs_open'; auto. rewrite local_locs_open'; auto. rewrite H13. unfold kill_sep; clear; Qcrush.
         apply qstp_empty in H36. apply has_type_filter in H; auto. eapply kill_sep_sub_fresh. eapply Subq_trans; eauto. auto.
         apply qstp_empty in H36. eapply kill_sep_sub; eauto.
         eapply wf_step_preserve. 3: econstructor; auto. eauto. auto.
       * simpl. eapply kill_sep_sub; eauto.
     + (* right congruence *)
       inversion H19. subst.
       apply (has_type_vtp Hclϰ) in H as VH; intuition.
       apply vtp_canonical_form_lam in VH as HH; intuition.
       remember (qdiff φ (local_locs t1)) as φd. apply wf_step_value in H13 as Hllt1; auto. rewrite Hllt1 in Heqφd. rewrite qdiff_empty in Heqφd. subst.
       specialize (H11 σ). intuition. destruct H11 as [t2' [σ' HH22]]. exists (tapp t1 t2'). exists σ'. intuition. constructor; intuition.
       destruct H25. destruct (♦∈? d1) eqn:Hfresh.
       * (* d1 fresh *)
         ndestruct (qbvs d2 1).
         -- (* d2 dependent on x *) apply (Preserve Σ' d' φ' ϰ'); auto. simpl. rewrite Hllt1. rewrite qor_empty_left; auto.
            eapply disjointq_scale; eauto. eapply openq_subqual_1; eauto.
            replace (T2 <~ᵀ TUnit ~ ∅; T1 ~ d1) with (T2 <~ᵀ TUnit ~ ∅; T1 ~ (d1 ⋓ d')). (* T2 not dependent on x *)
            rewrite openq_duplicate_eq_r; auto. 2:{ unfold open_ty. apply not_free_prop2. rewrite not_free_prop1; auto. }
          inversion H27; subst.
          ++ (*base*) eapply disjointq_same in H31; auto. 2: eapply H14. 2: eapply H30. destruct H31. subst. repeat rewrite qqplus_qbot_right_neutral in *.
            eapply t_app_fresh; auto.
            eapply weaken_2D_store with (Σ':=Σ'); eauto. apply closed_qenv_empty; apply [].
            rewrite Hllt1. rewrite qdiff_empty; auto.
            eapply kill_sep_local_locs_base; eauto.
            rewrite Hllt1 in *. rewrite qor_empty_left. rewrite qor_empty_left in H7. eapply kill_sep_local_locs_base; eauto.
          ++ (*fresh*) eapply disjointq_grow in H31 as H31'; auto. 2: eapply H14. 2: eapply H30.
            apply t_sub with (T1 := (T2 <~ᵀ TUnit ~ ∅; T1 ~ (d1 ⋓ d'))) (d1 := (openq df (d1 ⋓ d') d2)).
            ** eapply t_app_fresh with (T1 := T1) (df:=df); eauto.
               replace (q_trans_tenv [] df ⋒ q_trans_tenv [] (d1 ⋓ d')) with (q_trans_tenv [] df ⋒ q_trans_tenv [] d1).
               eapply weaken_flt. unfold q_trans_tenv in *. simpl in *.
               eapply weaken_2D_store. eapply H. auto. eauto.
               apply closed_qenv_empty. apply []. all : auto.
               eapply has_type_closed in H32. intuition.
               { inversion H31; subst; simpl; destruct (♦∈? d1); auto.
                 ++ rewrite qor_empty_right; auto.
                 ++ unfold q_trans_tenv. simpl. repeat rewrite qand_qor_dist_l.
                    assert (Hemp: df ⊓ &! (‖ Σ ‖) = ∅). { apply Q_lift_eq. clear - H22. Qcrush. subst. eauto 3. }
                    rewrite Hemp. rewrite qor_empty_right.
                    auto.
               }
               eauto using Subq_trans. apply Qor_bound; auto. apply has_type_closed in H32. intuition.
               eapply @Subq_trans with (d2:=q_trans_tenv [] df). Qcrush.
               unfold q_trans_tenv. simpl.
               eapply has_type_filter in H as HF. eapply Subq_trans.
               eapply HF. clear. rewrite qor_assoc_23. Qcrush.
               rewrite Hllt1. rewrite qdiff_empty; auto.
               eapply kill_sep_local_locs_grow; eauto. destruct H14 as [? [Hlen ?]]. rewrite Hlen. apply has_type_filter in H; intuition; eauto.
               rewrite Hllt1 in *. rewrite qor_empty_left. rewrite qor_empty_left in H7. eapply kill_sep_local_locs_grow; eauto. destruct H14 as [? [Hlen ?]]. rewrite Hlen. eauto.
               rewrite Hllt1 in *. unfold kill_sep. clear. Qcrush.
            ** apply has_type_closed in H32. intuition.
               apply stp_refl. unfold open_ty. eapply closed_ty_open2; eauto. eapply closed_ty_monotone; eauto.
               constructor; auto. apply closed_Qual_qqplus; auto.
               eapply openq_closed; try solve [eapply closed_qual_monotone; eauto]. eauto.
            ** apply has_type_filter in H0. apply has_type_filter in H. apply Qqplus_bound.
                apply has_type_closed in H32. intuition. eapply closed_Qual_qor_fresh in H41.
                eapply openq_subqual_trans''. apply H18. all: eauto. Qcrush.
            ** apply has_type_local_loc_sep in H32 as Hlc. replace ((d1 ⋓ d')) with (d1 ⊔ d') in *. 2: {clear - Hfresh; Qcrush. rewrite Hfresh; auto. }
              apply kill_sep_qor_rev in Hlc. destruct Hlc. apply kill_sep_qqplus_bound; auto. simpl. rewrite Hllt1. rewrite qor_empty_left.
              destruct H14 as [? [Hlen ?]].
              eapply kill_sep_open2. 3: apply closed_Qual_qor; auto. 4: eapply disjointq_closed; eauto. 1-3: eapply closed_Qual_monotone; eauto. apply has_type_closed in H32; intuition. eapply closed_tm_monotone; eauto.
              eapply kill_sep_local_locs_grow; eauto. rewrite Hlen; eauto. apply kill_sep_kill_qor_rev in H7; destruct H7; auto.
              apply kill_sep_qor; auto.
              eapply kill_sep_local_locs_grow; eauto. rewrite Hlen. eauto.
              simpl. rewrite Hllt1. rewrite qor_empty_left; auto.
          ++ (*kill*) eapply disjointq_same in H31 as H31'; auto. 2: eapply H14. 2: eapply H30. destruct H31'; subst.
            do 2 rewrite qqplus_qbot_right_neutral. rewrite qqplus_qbot_right_neutral in H32.
            assert (kill_sep &!l df). { eapply kill_sep_kill_sub. 2: eauto. clear - H41. Qcrush. subst; auto. }
            eapply t_app_fresh; eauto.
            {apply has_type_filter in H as H'; intuition. eapply (has_type_vtp Hclϰ) in H; eauto. eapply weaken_flt. eapply vtp_non_fresh in H; auto. eapply t_sub with (d1:= (false, qfvs df, qbvs df, qlocs df)). 4:{ eapply kill_sep_sub_fresh; eauto. }
            eapply vtp_has_type; eauto. apply stp_refl; auto. apply qs_sq; auto.
            clear; Qcrush. clear; Qcrush. eapply q_remove_sub; auto.
              clear - H'; Qcrush. specialize (H1 x H2). rewrite or_false_elim in H1; auto. specialize (H0 x H2). rewrite or_false_elim in H0; auto. specialize (H3 x H2); rewrite or_false_elim in H3; auto.
              eapply kill_sep_sub. 2: eauto. clear; Qcrush.
              eapply closed_Qual_sub. 2: eapply q_remove_smaller; auto. auto. }
            eapply q_remove_sub'; eauto. eapply kill_sep_open_empty' with (Σ:=Σ'). clear - H40. Qcrush. apply kill_sep_kill_qor_rev in H7; destruct H7. eapply kill_sep_kill_sub. 2: eauto. clear - H41. Qcrush; subst; auto.
            eapply (@Subq_trans _ ((q_trans_tenv [] df) ⊔ {♦})). clear; Qcrush. replace (q_trans_tenv [] df) with df by auto. eapply q_remove_sub'; eauto. apply has_type_filter in H. clear - H. Qcrush. apply kill_sep_qor; auto. apply kill_sep_fresh.
            rewrite Hllt1; rewrite qdiff_empty; auto.
            eapply kill_sep_local_locs_base; eauto.
            rewrite Hllt1. rewrite Hllt1 in H7. rewrite qor_empty_left in H7. rewrite qor_empty_left. eapply kill_sep_local_locs_base; eauto.
           ++ (*wf_step*) constructor; auto.
         -- (* d2 not dependent on x *) apply (Preserve Σ' ∅ φ' ϰ'); auto. simpl. rewrite Hllt1. rewrite qor_empty_left; auto.
            rewrite qqplus_qbot_right_neutral. intuition.
            replace (d2 <~ᵈ df; d1) with (d2 <~ᵈ df; (d1 ⋓ d')). 2: {unfold open_ty. repeat rewrite not_free_prop1; auto. eapply openq_subqual_1_false; eauto. }
            inversion H27; subst.
            ++ (*base*) eapply disjointq_same in H31; auto. 2: eapply H14. 2: eapply H30. destruct H31. subst. repeat rewrite qqplus_qbot_right_neutral in *.
              eapply t_app_fresh; auto.
              eapply weaken_2D_store with (Σ':=Σ'); eauto. apply closed_qenv_empty; apply [].
              rewrite Hllt1. rewrite qdiff_empty; auto.
              eapply kill_sep_local_locs_base; eauto.
              rewrite Hllt1 in *. rewrite qor_empty_left. rewrite qor_empty_left in H7. eapply kill_sep_local_locs_base; eauto.
            ++ (*fresh*) eapply disjointq_grow in H31 as H31'; auto. 2: eapply H14. 2: eapply H30.
              replace (T2 <~ᵀ TUnit ~ ∅; T1 ~ d1) with (T2 <~ᵀ TUnit ~ ∅; T1 ~ (d1 ⋓ d')). (* T2 not dependent on x *) 2:{ unfold open_ty. repeat rewrite not_free_prop1; auto. }
              eapply t_app_fresh with (T1:=T1); eauto.
              replace (q_trans_tenv [] (d1 ⋓ d')) with (d1 ⋓ d'); auto. replace (q_trans_tenv [] df) with df in *; auto. replace (q_trans_tenv [] (d1)) with (d1) in H; auto. erewrite <- @qqcap_fresh_r with (Σ':=[(T, q)] :: Σ); eauto.
              eapply weaken_flt. eapply weaken_2D_store. eauto. auto.
              apply closed_qenv_empty. apply []. eauto.
              eapply has_type_closed in H32. intuition. apply closed_Qual_qor. eapply closed_Qual_monotone; eauto. clear; simpl; Qcrush.
              eapply Subq_trans; eauto.
              eapply @Subq_trans with (d2:=q_trans_tenv [] df  ⊔ {♦}). clear. Qcrush.
              unfold q_trans_tenv. simpl. eapply has_type_filter in H as HF. clear - HF. rewrite qor_assoc_23. Qcrush.
              rewrite Hllt1. rewrite qdiff_empty; auto.
              eapply kill_sep_local_locs_grow; eauto. destruct H14 as [? [Hlen ?]]. rewrite Hlen. apply has_type_filter in H; intuition; eauto.
              rewrite Hllt1 in *. rewrite qor_empty_left. rewrite qor_empty_left in H7. eapply kill_sep_local_locs_grow; eauto. destruct H14 as [? [Hlen ?]]. rewrite Hlen. eauto.
              rewrite Hllt1. unfold kill_sep. clear. Qcrush.
            ++ (*kill*) eapply disjointq_same in H31 as H31'; auto. 2: eapply H14. 2: eapply H30. destruct H31'; subst.
              rewrite qqplus_qbot_right_neutral. rewrite qqplus_qbot_right_neutral in H32.
              assert (kill_sep &!l df). { eapply kill_sep_kill_sub. 2: eauto. clear - H41. Qcrush. subst; auto. }
              eapply t_app_fresh; eauto.
              {apply has_type_filter in H as H'; intuition. eapply (has_type_vtp Hclϰ) in H; eauto. eapply weaken_flt. eapply vtp_non_fresh in H; auto. eapply t_sub with (d1:= (false, qfvs df, qbvs df, qlocs df)). 4:{ eapply kill_sep_sub_fresh; eauto. } eapply vtp_has_type; eauto. apply stp_refl; auto. apply qs_sq; auto.
              clear; Qcrush. clear; Qcrush. eapply q_remove_sub; auto.
                clear - H'; Qcrush. specialize (H1 x H2). rewrite or_false_elim in H1; auto. specialize (H0 x H2). rewrite or_false_elim in H0; auto. specialize (H3 x H2); rewrite or_false_elim in H3; auto.
                eapply kill_sep_sub. 2: eauto. clear; Qcrush.
                eapply closed_Qual_sub. 2: eapply q_remove_smaller; auto. auto. }
              eapply q_remove_sub'; eauto. eapply kill_sep_open_empty' with (Σ:=Σ'). clear - H40. Qcrush. apply kill_sep_kill_qor_rev in H7; destruct H7. eapply kill_sep_kill_sub. 2: eauto. clear - H41. Qcrush; subst; auto.
              eapply (@Subq_trans _ ((q_trans_tenv [] df) ⊔ {♦})). clear; Qcrush. replace (q_trans_tenv [] df) with df by auto. eapply q_remove_sub'; eauto. apply has_type_filter in H. clear - H. Qcrush. apply kill_sep_qor; auto. apply kill_sep_fresh.
              rewrite Hllt1; rewrite qdiff_empty; auto.
              eapply kill_sep_local_locs_base; eauto.
              rewrite Hllt1. rewrite Hllt1 in H7. rewrite qor_empty_left in H7. rewrite qor_empty_left. eapply kill_sep_local_locs_base; eauto.
            ++ (*wf_step*) constructor; auto.

       * (* d1 not fresh *) rewrite not_fresh_qqplus in H32; auto. apply (Preserve Σ' ∅ φ' ϰ'); auto. simpl. rewrite Hllt1. rewrite qor_empty_left. auto.
         rewrite qqplus_qbot_right_neutral.
         inversion H27; subst.
         ++ eapply disjointq_same in H31; auto. 2: eapply H14. 2: eapply H30. destruct H31. subst. repeat rewrite qqplus_qbot_right_neutral in *.
          eapply t_app_fresh with (T1:=T1); auto.
          eapply weaken_2D_store with (Σ':=Σ'); eauto. apply closed_qenv_empty; apply [].
          rewrite Hllt1. rewrite qdiff_empty; auto. intros. clear - H41 Hfresh. rewrite Hfresh in H41. inversion H41.
          eapply kill_sep_local_locs_base; eauto.
          rewrite Hllt1 in *. rewrite qor_empty_left. rewrite qor_empty_left in H7. eapply kill_sep_local_locs_base; eauto.
         ++ eapply disjointq_grow in H31 as H31'; auto. 2: eapply H14. 2: eapply H30.
            eapply t_app_fresh with (T1:=T1); eauto.
            eapply weaken_flt. eapply weaken_2D_store. eauto. auto. auto.
            apply closed_qenv_empty. apply []. eauto.
            eapply has_type_closed in H32. intuition. apply closed_Qual_qor. eapply closed_Qual_monotone; eauto. clear; simpl; Qcrush.
            eapply Subq_trans; eauto.
            eapply @Subq_trans with (d2:=q_trans_tenv [] df  ⊔ {♦}). clear. Qcrush.
            unfold q_trans_tenv. simpl. eapply has_type_filter in H as HF. clear - HF. rewrite qor_assoc_23. Qcrush.
            rewrite Hllt1. rewrite qdiff_empty; auto.
            eapply kill_sep_local_locs_grow; eauto. destruct H14 as [? [Hlen ?]]. rewrite Hlen. apply has_type_filter in H; intuition; eauto.
            rewrite Hllt1 in *. rewrite qor_empty_left. rewrite qor_empty_left in H7. eapply kill_sep_local_locs_grow; eauto. destruct H14 as [? [Hlen ?]]. rewrite Hlen. eauto.
         ++ eapply disjointq_same in H31 as H31'; auto. 2: eapply H14. 2: eapply H30. destruct H31'; subst.
            assert (kill_sep &!l df). { eapply kill_sep_kill_sub. 2: eauto. clear - H40. Qcrush. subst; auto. }
            eapply t_app_fresh; eauto.
            {apply has_type_filter in H as H'; intuition. eapply (has_type_vtp Hclϰ) in H; eauto. eapply weaken_flt. eapply vtp_non_fresh in H; auto. eapply t_sub with (d1:= (false, qfvs df, qbvs df, qlocs df)). 4:{ eapply kill_sep_sub_fresh; eauto. } eapply vtp_has_type; eauto. apply stp_refl; auto. apply qs_sq; auto.
            clear; Qcrush. clear; Qcrush. eapply q_remove_sub; auto.
              clear - H'; Qcrush. specialize (H1 x H2). rewrite or_false_elim in H1; auto. specialize (H0 x H2). rewrite or_false_elim in H0; auto. specialize (H3 x H2); rewrite or_false_elim in H3; auto.
              eapply kill_sep_sub. 2: eauto. clear; Qcrush.
              eapply closed_Qual_sub. 2: eapply q_remove_smaller; auto. auto. }
            eapply q_remove_sub'; eauto. eapply kill_sep_open_empty' with (Σ:=Σ'). clear - H39. Qcrush. apply kill_sep_kill_qor_rev in H7; destruct H7. eapply kill_sep_kill_sub. 2: eauto. clear - H40. Qcrush; subst; auto.
            eapply (@Subq_trans _ ((q_trans_tenv [] df) ⊔ {♦})). clear; Qcrush. replace (q_trans_tenv [] df) with df by auto. eapply q_remove_sub'; eauto. apply has_type_filter in H. clear - H. Qcrush. apply kill_sep_qor; auto. apply kill_sep_fresh.
            rewrite Hllt1; rewrite qdiff_empty; auto.
            eapply kill_sep_local_locs_base; eauto.
            rewrite Hllt1. rewrite Hllt1 in H7. rewrite qor_empty_left in H7. rewrite qor_empty_left. eapply kill_sep_local_locs_base; eauto.
          ++ (*wf_step*) constructor; auto.
     + (* left congruence *)
       apply has_type_closed in H0 as Hcl. intuition.
       specialize (H13 σ H14 H15). destruct H13 as [t1' [σ' HH1]]. exists (tapp t1' t2). exists σ'. intuition. apply step_c_app_l. intuition.
       simpl in Hwfstep. destruct Hwfstep as [Hwft1 [Hwft2 Hwfstep]]. destruct Hwfstep. apply value_unsteppable in H13; auto; lia. rename H31 into Hwfstep.
       destruct H29. destruct (♦∈? df) eqn:Hfresh.
       * (* df fresh *)
         ndestruct (qbvs d2 0).
         -- (* d2 dependent on f *) apply (Preserve Σ' d' φ' ϰ'); auto. simpl. rewrite Hwfstep. rewrite qor_empty_right; auto.
          eapply disjointq_scale; eauto. eapply openq_subqual_0; eauto.
          erewrite @openq_duplicate_eq_l with (l:=‖Σ'‖) (f:=0); auto. 2,3 : eapply closed_qual_monotone; eauto. 2: eauto.
          inversion H31; subst.
          ++ (*base*) eapply disjointq_same in H35; auto. 2: eapply H14. 2: eapply H34. destruct H35. subst. repeat rewrite qqplus_qbot_right_neutral in *.
            apply t_app_fresh with (φd:=(qdiff φ' (local_locs t1'))); auto.
            eapply weaken_2D_store with (Σ':=Σ'); eauto. 2: apply closed_qenv_empty; apply [].
            eapply weaken_flt. eauto. eapply qdiff_subqual_rev_monotone. eapply local_locs_step_same with (σ:=σ); eauto.
            eapply closed_Qual_sub. eapply H18. (*φ'*) clear; Qcrush.
            rewrite Hwfstep. rewrite qor_empty_right. rewrite Hwfstep in H7. rewrite qor_empty_right in H7. eapply kill_sep_local_locs_base; eauto.
            eapply kill_sep_local_locs_base; eauto.
          ++ (*fresh*) eapply disjointq_grow in H35 as H35'; auto. 2: eapply H14. 2: eapply H34.
            apply t_sub with (T1 := (T2 <~ᵀ TUnit ~ ∅; T1 ~ d1)) (d1 := (openq (df ⋓ d') d1 d2)).
            ** eapply t_app_fresh with (T1 := T1) ; eauto.
              replace (q_trans_tenv [] (df ⋓ d')) with (df ⋓ d'); auto. replace (q_trans_tenv [] d1) with d1; auto. erewrite <- @qqcap_fresh_l with (Σ':=([(T, q)] :: Σ)); eauto.
              unfold q_trans_tenv in *. simpl in *.
              eapply weaken_flt. eapply weaken_2D_store. eauto. auto.
              apply closed_qenv_empty. apply []. eauto.
              eapply (@Subq_trans _ (qdiff (φ ⊔ &! (‖ Σ ‖)) (local_locs t1 ⊔ &! (‖ Σ ‖)))). 2: eapply qdiff_subqual_rev_monotone. eapply qdiff_incr; eauto. destruct H14 as [? [Hlen ?]]. rewrite <- Hlen. eapply local_locs_step_grow; eauto.
              eapply closed_Qual_qdiff; simpl. eapply closed_Qual_qor. eapply closed_Qual_monotone; eauto. clear; Qcrush. eapply local_locs_closed. apply has_type_closed in H36; intuition; eauto.
              eapply Subq_trans; eauto.
              replace (q_trans_tenv [] (df ⋓ d')) with (df ⋓ d'); auto. replace (q_trans_tenv [] d1) with d1; auto.
              eapply @Subq_trans with (d2:=d1 ⊔ {♦}). clear. Qcrush. simpl. eapply has_type_filter in H0 as HF. eapply (@Subq_trans _ (qdiff φ (local_locs t1) ⊔ {♦})). clear - HF. Qcrush. clear - H17. rewrite qor_assoc_23. Qcrush.
              rewrite Hwfstep. unfold kill_sep. clear. Qcrush.
              rewrite Hwfstep. rewrite qor_empty_right. rewrite Hwfstep in H7. rewrite qor_empty_right in H7. eapply kill_sep_local_locs_grow; eauto. destruct H14 as [? [Hlen ?]]. rewrite Hlen. inversion H19; subst; eauto.
              eapply kill_sep_local_locs_trans_tenv. 9: eauto. 1-6: eauto. destruct H14 as [? [Hlen ?]]. auto. auto. auto.
            ** apply has_type_closed in H36. intuition.
               apply stp_refl. simpl. eapply closed_ty_monotone; eauto.
               constructor; auto. apply closed_Qual_qqplus; auto.
               apply openQ_closed. inversion H42; subst. eapply closed_Qual_monotone; eauto. apply closed_Qual_qqplus; eauto.
               1,2: eapply closed_Qual_monotone; eauto.
            ** apply has_type_filter in H0. apply has_type_filter in H. apply Qqplus_bound.
               eapply openq_subqual; eauto 2 using closed_Qual_qor.
               eapply has_type_closed in H36. intuition. eapply closed_Qual_qor_fresh. eauto.
               apply Qqplus_bound. eapply Subq_trans; eauto. Qcrush.
               eapply Subq_trans; eauto. rewrite qor_assoc_23. clear - H17. Qcrush.
               eapply Subq_trans; eauto. eapply Subq_trans; eauto.
            ** apply has_type_local_loc_sep in H36 as Hlc. replace ((df ⋓ d')) with (df ⊔ d') in *. 2: {clear - Hfresh; Qcrush. rewrite Hfresh; auto. }
              apply kill_sep_qor_rev in Hlc. destruct Hlc. apply kill_sep_qqplus_bound; auto. simpl. rewrite Hwfstep. rewrite qor_empty_right.
              destruct H14 as [? [Hlen ?]]. inversion H19; subst.
              eapply kill_sep_open2. 2: apply closed_Qual_qor; auto. 3: eapply disjointq_closed; eauto. 1-3: eapply closed_Qual_monotone; eauto. apply has_type_closed in H36; intuition. eapply closed_tm_monotone; eauto.
              eapply kill_sep_local_locs_grow; eauto. rewrite Hlen; eauto. apply kill_sep_kill_qor_rev in H7; destruct H7; auto.
              eapply kill_sep_local_locs_grow; eauto. rewrite Hlen; eauto. apply has_type_filter in H0. eapply kill_sep_sub_fresh; eauto.
              apply kill_sep_qor; auto.
              simpl. rewrite Hwfstep. rewrite qor_empty_right; auto.
          ++ (*kill*) eapply disjointq_same in H35; auto. 2: eapply H14. 2: eapply H34. destruct H35. subst. repeat rewrite qqplus_qbot_right_neutral in *.
              apply t_app_fresh with (φd:=(qdiff (q_remove Σ' l φ) (local_locs t1'))); auto.
              eapply weaken_flt. eauto. { eapply (@Subq_trans _ (qdiff (q_remove Σ' l φ) (local_locs t1))). eapply qdiff_remove; auto. eauto. apply qdiff_subqual_rev_monotone. eapply local_locs_step_same with (σ:=σ); eauto. }
              eapply closed_Qual_qdiff; simpl. eapply closed_Qual_sub. 2: eapply q_remove_smaller. auto. eapply local_locs_closed. apply has_type_closed in H36; intuition; eauto.
              eapply q_remove_sub'; eauto. apply kill_sep_open_empty' with (Σ:=Σ'); auto. clear - H40. Qcrush. eapply kill_sep_kill_sub. 2: eauto. rewrite Hwfstep. rewrite qor_empty_right. clear - H41. Qcrush; subst; auto.
              eapply q_remove_sub'; eauto. eapply kill_sep_kill_sub. 2: eauto. clear - H41. Qcrush; subst; auto.
              rewrite Hwfstep. rewrite qor_empty_right. rewrite Hwfstep in H7. rewrite qor_empty_right in H7. eapply kill_sep_local_locs_base; eauto.
              eapply kill_sep_local_locs_base; eauto.
          ++ (*wf_step*) constructor; auto.
         -- (* d2 not dependent on f *) apply (Preserve Σ' ∅ φ' ϰ'); auto. simpl. rewrite Hwfstep. rewrite qor_empty_right. auto. rewrite qqplus_qbot_right_neutral.
            replace (d2 <~ᵈ df; d1) with (d2 <~ᵈ df ⋓ d'; d1). 2:{eapply openq_subqual_0_false; auto. }
          inversion H31; subst.
          ++ (*base*) eapply disjointq_same in H35; auto. 2: eapply H14. 2: eapply H34. destruct H35. subst. repeat rewrite qqplus_qbot_right_neutral in *.
            apply t_app_fresh with (φd:=(qdiff φ' (local_locs t1'))); auto.
            eapply weaken_2D_store with (Σ':=Σ'); eauto. 2: apply closed_qenv_empty; apply [].
            eapply weaken_flt. eauto. eapply qdiff_subqual_rev_monotone. eapply local_locs_step_same with (σ:=σ); eauto.
            eapply closed_Qual_sub. eapply H18. (*φ'*) clear; Qcrush.
            rewrite Hwfstep. rewrite qor_empty_right. rewrite Hwfstep in H7. rewrite qor_empty_right in H7. eapply kill_sep_local_locs_base; eauto.
            eapply kill_sep_local_locs_base; eauto.
          ++ (*fresh*) eapply disjointq_grow in H35 as H35'; auto. 2: eapply H14. 2: eapply H34.
            eapply t_app_fresh with (T1:=T1); eauto.
            replace (q_trans_tenv [] (df ⋓ d')) with (df ⋓ d'); auto. replace (q_trans_tenv [] d1) with d1; auto. erewrite <- @qqcap_fresh_l with (Σ':=[(T, q)] :: Σ); eauto.
            eapply weaken_flt. eapply weaken_2D_store. eauto. auto. all: auto.
            apply closed_qenv_empty. apply [].
            eapply (@Subq_trans _ (qdiff (φ ⊔ &! (‖ Σ ‖)) (local_locs t1 ⊔ &! (‖ Σ ‖)))). 2: eapply qdiff_subqual_rev_monotone. eapply qdiff_incr; eauto. destruct H14 as [? [Hlen ?]]. rewrite <- Hlen. eapply local_locs_step_grow; eauto.
            eapply closed_Qual_qdiff; simpl. eapply closed_Qual_qor. eapply closed_Qual_monotone; eauto. clear; Qcrush. eapply local_locs_closed. apply has_type_closed in H36; intuition; eauto.
            eapply Subq_trans; eauto.
            replace (q_trans_tenv [] (df ⋓ d')) with (df ⋓ d'); auto. replace (q_trans_tenv [] d1) with d1; auto.
            eapply @Subq_trans with (d2:=d1 ⊔ {♦}). clear. Qcrush. simpl. eapply has_type_filter in H0 as HF. eapply (@Subq_trans _ (qdiff φ (local_locs t1) ⊔ {♦})). clear - HF. Qcrush. clear - H17. rewrite qor_assoc_23. Qcrush.
            rewrite Hwfstep. unfold kill_sep. clear. Qcrush.
            rewrite Hwfstep. rewrite qor_empty_right. rewrite Hwfstep in H7. rewrite qor_empty_right in H7. eapply kill_sep_local_locs_grow; eauto. destruct H14 as [? [Hlen ?]]. rewrite Hlen. inversion H19; subst; eauto.
            eapply kill_sep_local_locs_trans_tenv. 9: eauto. 1-6: eauto. destruct H14 as [? [Hlen ?]]. auto. auto. auto.
          ++ (*kill*) eapply disjointq_same in H35; auto. 2: eapply H14. 2: eapply H34. destruct H35. subst. repeat rewrite qqplus_qbot_right_neutral in *.
              apply t_app_fresh with (φd:=(qdiff (q_remove Σ' l φ) (local_locs t1'))); auto.
              eapply weaken_flt. eauto. { eapply (@Subq_trans _ (qdiff (q_remove Σ' l φ) (local_locs t1))). eapply qdiff_remove; auto. eauto. apply qdiff_subqual_rev_monotone. eapply local_locs_step_same with (σ:=σ); eauto. }
              eapply closed_Qual_qdiff; simpl. eapply closed_Qual_sub. 2: eapply q_remove_smaller. auto. eapply local_locs_closed. apply has_type_closed in H36; intuition; eauto.
              eapply q_remove_sub'; eauto. apply kill_sep_open_empty' with (Σ:=Σ'); auto. clear - H40. Qcrush. eapply kill_sep_kill_sub. 2: eauto. rewrite Hwfstep. rewrite qor_empty_right. clear - H41. Qcrush; subst; auto.
              eapply q_remove_sub'; eauto. eapply kill_sep_kill_sub. 2: eauto. clear - H41. Qcrush; subst; auto.
              rewrite Hwfstep. rewrite qor_empty_right. rewrite Hwfstep in H7. rewrite qor_empty_right in H7. eapply kill_sep_local_locs_base; eauto.
              eapply kill_sep_local_locs_base; eauto.
          ++ (*wf_step*) constructor; auto.

        * (* df not fresh *) rewrite not_fresh_qqplus in H36; auto. apply (Preserve Σ' ∅ φ' ϰ'); auto. simpl. rewrite Hwfstep. rewrite qor_empty_right. auto. rewrite qqplus_qbot_right_neutral.
          inversion H31; subst.
          ++ (*base*) eapply disjointq_same in H35; auto. 2: eapply H14. 2: eapply H34. destruct H35. subst. repeat rewrite qqplus_qbot_right_neutral in *.
            apply t_app_fresh with (φd:=(qdiff φ' (local_locs t1'))); auto.
            eapply weaken_2D_store with (Σ':=Σ'); eauto. 2: apply closed_qenv_empty; apply [].
            eapply weaken_flt. eauto. eapply qdiff_subqual_rev_monotone. eapply local_locs_step_same with (σ:=σ); eauto.
            eapply closed_Qual_sub. eapply H18. (*φ'*) clear; Qcrush.
            rewrite Hwfstep. rewrite qor_empty_right. rewrite Hwfstep in H7. rewrite qor_empty_right in H7. eapply kill_sep_local_locs_base; eauto.
            eapply kill_sep_local_locs_base; eauto.
          ++ (*fresh*) eapply disjointq_grow in H35 as H35'; auto. 2: eapply H14. 2: eapply H34.
            eapply t_app_fresh with (T1:=T1); eauto.
            eapply weaken_flt. eapply weaken_2D_store. eauto. auto. all: auto.
            apply closed_qenv_empty. apply [].
            eapply (@Subq_trans _ (qdiff (φ ⊔ &! (‖ Σ ‖)) (local_locs t1 ⊔ &! (‖ Σ ‖)))). 2: eapply qdiff_subqual_rev_monotone. eapply qdiff_incr; eauto. destruct H14 as [? [Hlen ?]]. rewrite <- Hlen. eapply local_locs_step_grow; eauto.
            eapply closed_Qual_qdiff; simpl. eapply closed_Qual_qor. eapply closed_Qual_monotone; eauto. clear; Qcrush. eapply local_locs_closed. apply has_type_closed in H36; intuition; eauto.
            eapply Subq_trans; eauto.
            replace (q_trans_tenv [] (df ⋓ d')) with (df ⋓ d'); auto. replace (q_trans_tenv [] d1) with d1; auto.
            eapply @Subq_trans with (d2:=d1 ⊔ {♦}). clear. Qcrush. simpl. eapply has_type_filter in H0 as HF. eapply (@Subq_trans _ (qdiff φ (local_locs t1) ⊔ {♦})). clear - HF. Qcrush. clear - H17. rewrite qor_assoc_23. Qcrush.
            rewrite Hwfstep. rewrite qor_empty_right. rewrite Hwfstep in H7. rewrite qor_empty_right in H7. eapply kill_sep_local_locs_grow; eauto. destruct H14 as [? [Hlen ?]]. rewrite Hlen. inversion H19; subst; eauto.
            eapply kill_sep_local_locs_grow; eauto. inversion H19; subst. destruct H14 as [? [Hlen ?]]. rewrite Hlen. rewrite qand_commute. eauto.
          ++ (*kill*) eapply disjointq_same in H35; auto. 2: eapply H14. 2: eapply H34. destruct H35. subst. repeat rewrite qqplus_qbot_right_neutral in *.
              apply t_app_fresh with (φd:=(qdiff (q_remove Σ' l φ) (local_locs t1'))); auto.
              eapply weaken_flt. eauto. { eapply (@Subq_trans _ (qdiff (q_remove Σ' l φ) (local_locs t1))). eapply qdiff_remove; auto. eauto. apply qdiff_subqual_rev_monotone. eapply local_locs_step_same with (σ:=σ); eauto. }
              eapply closed_Qual_qdiff; simpl. eapply closed_Qual_sub. 2: eapply q_remove_smaller. auto. eapply local_locs_closed. apply has_type_closed in H36; intuition; eauto.
              eapply q_remove_sub'; eauto. apply kill_sep_open_empty' with (Σ:=Σ'); auto. clear - H39. Qcrush. eapply kill_sep_kill_sub. 2: eauto. rewrite Hwfstep. rewrite qor_empty_right. clear - H40. Qcrush; subst; auto.
              eapply q_remove_sub'; eauto. eapply kill_sep_kill_sub. 2: eauto. clear - H40. Qcrush; subst; auto.
              rewrite Hwfstep. rewrite qor_empty_right. rewrite Hwfstep in H7. rewrite qor_empty_right in H7. eapply kill_sep_local_locs_base; eauto.
              eapply kill_sep_local_locs_base; eauto.
          ++ (*wf_step*) constructor; auto.

  - (*tref*) subst. intuition. specialize (has_type_closed H) as HH. intuition.  specialize (H5 T t). intuition.
    + (*contraction*) right. intros.
      exists (tloc (‖σ‖) 0). exists ((Some [t]) :: σ). intuition.
      econstructor; eauto. inversion H10 as [? [Hlen ?]]. intuition.
      eapply has_type_filter in H as Hfl.
      assert ({♦} ⊑↑ d1 -> False). intros. Qcrush.
      assert (d1 ⊑↑ φ). eapply Subqual_non_fresh; eauto.
      apply (Preserve ([(T,d1)] :: Σ) (&!‖σ‖) (φ ⊔ &!‖σ‖) ϰ); auto.
      simpl. rewrite Hlen. apply env_fresh. eapply kill_sep_sub; eauto.
      apply wf_senv_after_ref; auto.
      eapply CtxOK_weaken; eauto. apply has_type_vtp; auto.
      rewrite Hlen. eapply disj_loc. 4: eauto. 1-3: auto.  rewrite Hlen.
      apply t_sub with (T1:=TRef d1 T) (d1:=(&!‖Σ‖)).
      apply t_loc; auto. apply closed_Qual_qor. eapply closed_Qual_monotone; eauto. clear; Qcrush. subst. auto.
      rewrite <- senv_length_coersion. rewrite sindexr_head. simpl. auto.
      eapply closed_ty_monotone; eauto.
      eapply closed_qual_monotone; eauto.
      apply stp_refl; auto. constructor; auto. simpl. eapply closed_ty_monotone; eauto.
      inversion H3; subst; auto. eapply closed_qual_monotone; eauto.
      constructor. clear. Qcrush.
      apply closed_Qual_qor; auto. simpl. clear. Qcrush.
      rewrite <- qor_assoc. clear; Qcrush.
      simpl. apply kill_sep_empty_kill.
      eapply wf_store_preserve. eauto. 2: econstructor; eauto. auto. constructor.
    + (*congruence*) right. intros. specialize (H5 σ H10 H12). destruct H5 as [t' [σ' HH10]].
      exists (tref t'). exists σ'. intuition. econstructor; eauto.
      destruct H13. simpl. apply (Preserve Σ' ∅ φ' ϰ'); intuition. rewrite qqplus_qbot_right_neutral. inversion H14; subst.
      * eapply disjointq_same in H18; auto. 2: eapply H10. 2: eapply H17. destruct H18. subst.
        apply t_ref; auto. rewrite qqplus_qbot_right_neutral in H19; auto. rewrite H23; auto.
      * eapply t_ref; eauto. rewrite not_fresh_qqplus in H19; auto. eapply closed_ty_monotone; eauto.
      * eapply disjointq_same in H18; auto. 2: eapply H10. 2: eapply H17. destruct H18. subst.
        apply t_ref; auto. rewrite qqplus_qbot_right_neutral in H19; auto.

  - (*trefat*) subst. intuition. rename H into Ht1. rename H1 into Ht2. intuition.
    assert (Hwfstep1: wf_step t1). simpl in Hwfstep; intuition. assert (Hwfstep2: wf_step t2). simpl in Hwfstep; intuition.
    apply has_type_closed in Ht1 as Ht1C. intuition.
    apply has_type_closed in Ht2 as Ht2C. intuition.
    remember (qdiff φ (local_locs t2)) as φd. symmetry in Heqφd. apply (qdiff_local_loc_prop) in Heqφd as Heqφd'; destruct Heqφd'.
    specialize (H6 (TRef d1 T1) t2). intuition.
    specialize (H8 T t1). intuition.
    + (* contraction *)
      right. intros.
      apply CtxOK_kill_closed in H17 as Hclϰ. apply CtxOK_kill_sep in H17 as Hwfkill.
      pose (Ht2' := Ht2). eapply (has_type_vtp Hclϰ) in Ht2'; eauto.
      pose (Hloc := Ht2'). inversion Ht2'. subst. apply (vtp_store_loc_defined H17) in Hloc; auto. destruct Hloc as [ctm [vb [? ?]]].
      pose (Ht1' := Ht1). apply (has_type_vtp Hclϰ) in Ht1'; auto.
      apply sindexr_var_some' in H26 as H27'. destruct H27' as [? [c [? ?]]].
      exists (tloc (l) (‖ctm‖)). exists (cinsert σ l (t1)). split.
      eapply step_refat; eauto.
      apply (Preserve (sinsert Σ l (T, d)) ∅ φ ϰ); auto.
      eapply sinsert_extends_2D; auto.
      apply env_phi; auto. eapply sinsert_extends_2D; eauto. rewrite <- senv_length_coersion. rewrite sinsert_length; auto.
      apply wf_senv_after_refat; auto.
      apply CtxOK_refat; auto. simpl in Ht1'. rewrite qdiff_empty in Ht1'; auto.
      rewrite qqplus_qbot_right_neutral. eapply t_sub.
      unfold CtxOK in H17; intuition. specialize (H42 l o c T0 q1). destruct H42 as [Hk He]. assert ((l ∈ₗ ϰ -> False)). { clear - H25 H40. intros. unfold kill_sep in H40. Qcrush. apply (H4 l); auto.  } specialize (He H41 H25 H33). erewrite sindexr_indexr_rewrite in H26; eauto. destruct He as [ctm' ?]. intuition. rewrite H42 in H19; inversion H19; subst. rename H45 into Hlen.
      eapply t_loc. 2:{ rewrite <- Hlen. eapply sinsert_sindexr; auto.  } all: auto.
      1-3: rewrite sinsert_length; auto.
      clear - H25. Qcrush. subst; auto.
      eapply weaken_2D_stp_store_ext. eapply stp_refl; eauto. apply extends_2D_length. apply sinsert_extends_2D; auto.
      apply has_type_filter in Ht2; auto.
      simpl. apply kill_sep_empty_kill.
      eapply wf_store_preserve. eauto. 2: econstructor; eauto. eauto.
      simpl. rewrite qdiff_empty; auto.

    + (* left congruence *)
      right. intros. apply wf_step_value in H6 as Hllt2; auto. rewrite Hllt2 in Heqφd. rewrite qdiff_empty in Heqφd. symmetry in Heqφd. subst.
      apply CtxOK_kill_closed in H17 as Hclϰ. apply CtxOK_kill_sep in H17 as Hwfkill.
      specialize (H8 σ H17 H18). destruct H8 as [t1' [σ' H4']].
      exists (trefat t1' t2). exists σ'. intuition. econstructor; eauto.
      pose (HV := Ht2). apply (has_type_vtp Hclϰ) in HV; intuition. inversion HV; subst.
      destruct H19. apply (Preserve Σ' ∅ φ' ϰ'); eauto. simpl. rewrite qor_empty_right. auto. rewrite not_fresh_qqplus in H36; auto. rewrite qqplus_qbot_right_neutral.
      inversion H20; subst.
      * eapply disjointq_same in H35; auto. 2: eapply H17. 2: eapply H34. destruct H35. subst.
        eapply t_refat. 4: eauto. all: eauto.
        simpl. rewrite qdiff_empty; auto.
        eapply weaken_2D_store; eauto. apply closed_qenv_empty. apply [].
        eapply kill_sep_local_locs_base; eauto.
      * eapply disjointq_grow in H35; auto. 2: eapply H17. 2: eapply H34.
        eapply t_refat. 4: eauto. all: auto.
        simpl. rewrite qdiff_empty. auto.
        eapply weaken_flt. eapply weaken_2D_store. eauto. all: auto. apply closed_qenv_empty. apply []. auto. apply closed_Qual_qor. eapply closed_Qual_monotone; eauto. clear; simpl; Qcrush.
        eapply kill_sep_local_locs_grow; eauto. destruct H17 as [? [Hlen ?]]. rewrite Hlen. eauto.
      * eapply disjointq_same in H35; auto. 2: eapply H17. 2: eapply H34. destruct H35. subst.
        eapply t_refat. 5: eauto. all: auto.
        simpl. rewrite qdiff_empty; auto.
        eapply weaken_2D_store with (Σ' := Σ').
        eapply has_type_value_retype; eauto. 2: auto. eapply kill_sep_kill_sub. 2: eapply H3. clear - H42. Qcrush; subst; auto.
        apply closed_qenv_empty. apply []. apply wf_senv_closed_qenv_qn; auto.
        eapply kill_sep_local_locs_base; eauto.
      * constructor; auto.
    + (* right congruence *)
      right. intros. specialize (H6 σ H17 H18). destruct H6 as [t2' [σ' H12']].
      exists (trefat t1 t2'). exists σ'. intuition. econstructor; eauto.
      pose H17 as H17'. destruct H17' as [_ [Hlen _]]. destruct Hwfstep as [_ [_ Hwfstep]]. destruct Hwfstep. 2: apply value_unsteppable in H6; auto; lia. rename H20 into Hwfstep.
      apply CtxOK_kill_closed in H17 as Hclϰ. apply CtxOK_kill_sep in H17 as Hwfkill.
      destruct H19. apply (Preserve Σ' d' φ' ϰ'); eauto. simpl. rewrite Hwfstep. rewrite qor_empty_left; auto.
      inversion H20; subst.
      * eapply disjointq_same in H24; auto. 2: eapply H17. 2: eapply H23. destruct H24. subst. rewrite qqplus_qbot_right_neutral. rewrite qqplus_qbot_right_neutral in H25.
        eapply t_refat. 3: eauto. all: auto.
        eapply weaken_flt. eapply weaken_2D_store; eauto. apply closed_qenv_empty. apply [].
        apply qdiff_subqual_rev_monotone. eapply local_locs_step_same with (σ:=σ); eauto. apply closed_Qual_qdiff; auto. apply has_type_closed in H25; intuition. eapply local_locs_closed. apply has_type_closed in H25; intuition; eauto.
      * eapply disjointq_grow in H24 as H25'. 2: eapply H17. 2: eapply H23.
        eapply t_refat. 3: eauto.  all: auto.
        eapply weaken_flt. eapply weaken_2D_store. eauto. auto. apply closed_qenv_empty. apply []. auto.  3: eauto.
        eapply (@Subq_trans _ (qdiff (φ ⊔ &! (‖ Σ ‖)) (local_locs t2 ⊔ &! (‖ Σ ‖)))). 2: eapply qdiff_subqual_rev_monotone. eapply qdiff_incr; eauto. rewrite <- Hlen. eapply local_locs_step_grow; eauto.
        apply closed_Qual_qdiff; auto. apply closed_Qual_qor. eapply closed_Qual_monotone; eauto. clear; Qcrush. eapply local_locs_closed. apply has_type_closed in H25; intuition; eauto.
        apply kill_sep_qqplus_bound; auto. inversion H24; subst. apply kill_sep_empty. eapply kill_sep_outbound; eauto. eapply local_locs_closed; eauto.
      * eapply disjointq_same in H24; auto. 2: eapply H17. 2: eapply H23. destruct H24. subst. rewrite qqplus_qbot_right_neutral. rewrite qqplus_qbot_right_neutral in H25.
        eapply t_refat. 5: eauto. all: auto. 2: eauto.
        eapply weaken_flt. eauto. { eapply (@Subq_trans _ (qdiff (q_remove Σ' l φ) (local_locs t2))). eapply qdiff_remove; auto. eauto. apply qdiff_subqual_rev_monotone. eapply local_locs_step_same with (σ:=σ); eauto. }
        apply closed_Qual_qdiff. eapply closed_Qual_sub. 2: eapply q_remove_smaller. auto. eapply local_locs_closed; eauto. apply has_type_closed in H25; intuition; eauto.
      * constructor; auto.

  - (*tderef*) subst. intuition. specialize (has_type_closed H) as HH. intuition. specialize (H6 (TRef d1 T0) t). intuition.
    + (* contraction *) right. intros. pose (HV := H). apply CtxOK_kill_closed in H11 as Hclϰ. apply CtxOK_kill_sep in H11 as Hwfkill.
      eapply (@has_type_vtp _ ϰ) in HV; intuition.
      specialize (vtp_canonical_form_loc HV) as Hcan. intuition. destruct H14 as [l HH10]. subst.
      pose (HHV := HV). inversion HHV. subst.  pose (HH3 := H11). inversion HH3. intuition.
      pose (HH14 := H21). apply sindexr_var_some' in HH14. destruct HH14 as [? [cty [? ?]]]. pose H21 as H21'. erewrite sindexr_indexr_rewrite in H21'; eauto. destruct HH10 as [o0 HH10]; inversion HH10; subst.
      specialize (vtp_store_loc_defined HH3 HV) as Hval. destruct Hval as [ctm [v [? ?]]].
      exists v. exists σ. intuition. eapply step_deref; eauto.
      apply (Preserve Σ ∅ φ ϰ); intuition. rewrite qqplus_qbot_right_neutral.
      specialize (H32 l o0 cty T q1). destruct H32 as [Hk He].
      assert (l ∈ₗ ϰ -> False). { clear - H24 H33. apply qstp_empty in H24. unfold kill_sep in H33. Qcrush. specialize (H7 l eq_refl). apply (H8 l); auto. }
      specialize (He H32 H20 H34). destruct He as [ctm' ?]. intuition. destruct H39 as [v' ?]. intuition.
      rewrite H38 in H36. inversion H36; subst. rewrite H40 in H37. inversion H37; subst.
      apply t_sub with (T1 := T)(d1:= q1); auto.
      eapply weaken_flt. eapply vtp_has_type; auto. eapply H43. 1-2: apply qstp_empty in H26; eapply Subq_trans; eauto. auto.
      eapply stp_qual_irrelevance; eauto. eapply Subq_trans; eauto.
      unfold wf_store in H13. assert (sindexr' l o0 σ = Some v ). { erewrite sindexr'_indexr_rewrite; eauto. } apply H13 in H42; destruct H42. apply wf_step_value in H44; auto. rewrite H44. apply kill_sep_empty_kill.
      eapply wf_step_preserve; eauto. econstructor; eauto.
    + (* congruence *) right; intros. specialize (H6 σ H11). destruct H6 as [t' [σ' H6]]. auto.
      destruct H6 as [Hstep Hpreserve].
      exists (! t'). exists (σ'). split. constructor; auto.
      inversion Hpreserve; subst. inversion H14; subst.
      * apply (Preserve Σ' ∅ φ' ϰ'); auto. eapply disjointq_same in H18; auto. 2: eapply H11. 2: eapply H17. destruct H18. subst. rewrite qqplus_qbot_right_neutral. rewrite qqplus_qbot_right_neutral in H19.
        eapply t_deref; eauto.
        eapply kill_sep_kill_sub. 2: eauto. eapply local_locs_step_same. 4: eauto. all: auto.
      * apply (Preserve ([(T, q)] :: Σ) (∅) (φ ⊔ &! (‖ Σ ‖)) ϰ'); auto. rewrite qqplus_qbot_right_neutral.
        eapply t_deref; eauto. eapply Subq_trans; eauto.
        eapply kill_sep_kill_sub with (ϰ:=local_locs t ⊔ &!‖σ‖). eapply local_locs_step_grow. auto. 3: eauto. 2: auto. eapply disjointq_grow; eauto.
          eapply kill_sep_kill_qor. auto. inversion H11. destruct H24. rewrite H24. eapply kill_sep_newloc_kill; auto.
      * eapply disjointq_same in H18; auto. 2: eapply H11. 2: eapply H17. destruct H18.
        apply (Preserve Σ' ∅ (q_remove Σ' l φ) (ϰ ⊔ &! l)); auto. rewrite qqplus_qbot_right_neutral. subst. rewrite qqplus_qbot_right_neutral in H19.
        eapply t_deref; eauto.
        (* l in local locs t, so l must have no impact on its qualifier *) eapply q_remove_sub; eauto. eapply kill_sep_kill_sub. 2: eauto. clear - H23. Qcrush; subst; auto.
        eapply kill_sep_kill_sub. 2: eauto. eapply local_locs_step_same. 4: eauto. all: auto.

  - (*tassign*) subst. intuition. rename H into Ht1. rename H0 into Ht2. intuition.
    assert (Hwfstep1: wf_step t1). simpl in Hwfstep; intuition. assert (Hwfstep2: wf_step t2). simpl in Hwfstep; intuition.
    apply has_type_closed in Ht1 as Ht1C. intuition.
    apply has_type_closed in Ht2 as Ht2C. intuition.
    remember (qdiff φ (local_locs t1)) as φd. symmetry in Heqφd. apply (qdiff_local_loc_prop) in Heqφd as Heqφd'; destruct Heqφd'.
    specialize (H8 (TRef d1 T) t1). intuition.
    specialize (H6 T t2). intuition.
    + (* contraction *)
      right. intros.
      apply CtxOK_kill_closed in H17 as Hclϰ. apply CtxOK_kill_sep in H17 as Hwfkill.
      pose (Ht1' := Ht1). eapply (has_type_vtp Hclϰ) in Ht1'; eauto.
      pose (Hloc := Ht1').
      inversion Ht1'. subst.
      pose (Ht2' := Ht2). apply (has_type_vtp Hclϰ) in Ht2'; auto.
      exists tunit. exists (supdate σ l o (t2)).
      pose H17 as H14'. destruct H14' as [? [Hlen ?]]. specialize (sindexr_var_some' H26) as HH22. destruct HH22 as [? [cty [? ?]]]. pose H26 as H26'. erewrite sindexr_indexr_rewrite in H26'; eauto.
      destruct H20 as [? [? [? ?]]]. specialize (H39 l o cty T0 q1). destruct H39 as [Hk He]. assert (~ l ∈ₗ ϰ). { clear - H37 H25. unfold kill_sep in H37. Qcrush. apply (H4 l). auto. } specialize (He H39 H25 H33). destruct He as [ctm ?]. intuition. destruct H41 as [v ?]. intuition.
      intuition. econstructor; eauto. rewrite Hlen; auto. lia.
      apply (Preserve Σ ∅ φ ϰ); auto.
      eapply CtxOK_update; eauto. rewrite Hlen; auto.
      eapply CtxOK_qdom'; eauto.
      apply weaken_flt with (φ':=φ) in Ht2; auto. apply (has_type_vtp Hclϰ) in Ht2 as Hvtp; auto. eapply vtp_widening. 4: eauto. auto.
      eapply kill_sep_sub_fresh. apply has_type_filter in Ht2. apply qstp_empty in H31. eapply Subq_trans; eauto. auto. eapply kill_sep_sub. apply qstp_empty in H31; eauto. apply has_type_local_loc_sep in Ht2; auto.
      eapply stp_qual_irrelevance; eauto.
      apply qstp_empty in H31. eapply Subq_trans; eauto. apply has_type_filter in Ht2. cut (d1 ⊑↑ φ ⊔ {♦}). intros. clear - H1 H42. Qcrush. specialize (H2 x H3); rewrite or_false_elim in H2; auto. specialize (H0 x H3); rewrite or_false_elim in H0; auto. specialize (H4 x H3); rewrite or_false_elim in H4; auto. eapply Subq_trans; eauto.
      apply wf_store_supdate; auto.
      simpl. rewrite qdiff_empty. auto.
    + (* right congruence *)
      right. intros. apply wf_step_value in H8 as Hllt1; auto. rewrite Hllt1 in Heqφd. rewrite qdiff_empty in Heqφd. symmetry in Heqφd. subst.
      apply CtxOK_kill_closed in H17 as Hclϰ. apply CtxOK_kill_sep in H17 as Hwfkill.
      specialize (H6 σ H17 H18). destruct H6 as [t' [σ' H4']].
      exists (tassign t1 t'). exists σ'. intuition. econstructor; eauto.
      pose (HV := Ht1). apply (has_type_vtp Hclϰ) in HV; intuition. inversion HV; subst.
      destruct H19. apply (Preserve Σ' ∅ φ' ϰ'); eauto. simpl. rewrite qor_empty_left. auto. rewrite not_fresh_qqplus in H36; auto. simpl.
      inversion H20; subst.
      * eapply disjointq_same in H35; auto. 2: eapply H17. 2: eapply H34. destruct H35. subst.
        eapply t_assign. 4: eauto.
        eapply weaken_2D_store. eauto. auto. apply closed_qenv_empty. apply []. eauto.
        simpl. rewrite qdiff_empty; auto. auto. eapply kill_sep_local_locs_base; eauto.
      * eapply disjointq_grow in H35; auto. 2: eapply H17. 2: eapply H34.
        eapply t_assign. 4: eauto.
        eapply weaken_flt. eapply weaken_2D_store. eauto. auto. all: auto. apply closed_qenv_empty. apply []. auto. apply closed_Qual_qor. eapply closed_Qual_monotone; eauto. clear; simpl; Qcrush.
        simpl. rewrite qdiff_empty. auto.
        eapply kill_sep_local_locs_grow; eauto. destruct H17 as [? [Hlen ?]]. rewrite Hlen. eauto.
      * eapply disjointq_same in H35; auto. 2: eapply H17. 2: eapply H34. destruct H35. subst.
        eapply t_assign. 4: eauto.
        eapply has_type_value_retype; eauto. eapply kill_sep_kill_sub. 2: eapply H3. clear - H42. Qcrush; subst; auto.
        simpl. rewrite qdiff_empty; auto. auto. eapply kill_sep_local_locs_base; eauto.
      * constructor; auto.
    + (* left congruence *)
      right. intros. specialize (H8 σ H17 H18). destruct H8 as [t' [σ' H12']].
      exists (tassign t' t2). exists σ'. intuition. econstructor; eauto.
      pose H17 as H17'. destruct H17' as [_ [Hlen _]]. destruct Hwfstep as [_ [_ Hwfstep]]. destruct Hwfstep. apply value_unsteppable in H8; auto; lia. rename H20 into Hwfstep.
      apply CtxOK_kill_closed in H17 as Hclϰ. apply CtxOK_kill_sep in H17 as Hwfkill.
      destruct H19. apply (Preserve Σ' ∅ φ' ϰ'); eauto. simpl. rewrite Hwfstep. rewrite qor_empty_right; auto.
      inversion H20; subst.
      * eapply disjointq_same in H24; auto. 2: eapply H17. 2: eapply H23. destruct H24. subst.
        eapply t_assign. 4: eauto. all: eauto.
        eapply weaken_flt. eapply weaken_2D_store. eauto. auto. apply closed_qenv_empty. apply []. auto.
        apply qdiff_subqual_rev_monotone. eapply local_locs_step_same with (σ:=σ); eauto. apply closed_Qual_qdiff; auto. apply has_type_closed in H25; intuition. eapply local_locs_closed. apply has_type_closed in H25; intuition; eauto.
        rewrite Hwfstep. unfold kill_sep. clear; Qcrush.
      * eapply disjointq_grow in H24 as H24'; auto. 2: eapply H17. 2: eapply H23.
        eapply t_assign. 4: eauto. eauto.
        eapply weaken_flt. eapply weaken_2D_store. eauto. all: auto. apply closed_qenv_empty. apply []. auto.
        eapply (@Subq_trans _ (qdiff (φ ⊔ &! (‖ Σ ‖)) (local_locs t1 ⊔ &! (‖ Σ ‖)))). 2: eapply qdiff_subqual_rev_monotone. eapply qdiff_incr; eauto. rewrite <- Hlen. eapply local_locs_step_grow; eauto.
        apply closed_Qual_qdiff; auto. apply closed_Qual_qor. eapply closed_Qual_monotone; eauto. clear; Qcrush. eapply local_locs_closed. apply has_type_closed in H25; intuition; eauto.
        rewrite Hwfstep. unfold kill_sep. clear; Qcrush.
      * eapply disjointq_same in H24; auto. 2: eapply H17. 2: eapply H23. destruct H24. subst.
        eapply t_assign. 4: eauto.
        eauto. eapply weaken_flt. eapply weaken_2D_store. eauto. auto. apply closed_qenv_empty. apply []. auto.
        { eapply (@Subq_trans _ (qdiff (q_remove Σ' l φ) (local_locs t1))). eapply qdiff_remove; auto. eauto. apply qdiff_subqual_rev_monotone. eapply local_locs_step_same with (σ:=σ); eauto. }
        apply closed_Qual_qdiff. eapply closed_Qual_sub. 2: eapply q_remove_smaller. auto. eapply local_locs_closed; eauto. apply has_type_closed in H25; intuition; eauto. auto.
        rewrite Hwfstep. unfold kill_sep. clear; Qcrush.
      * constructor; auto.

  - (*t_sub*) subst. intuition. specialize (stp_closed H0) as H00. intuition.
    specialize (H6 T1 t). intuition. right.
    intros. specialize (H6 σ H11 H13). destruct H6 as [t' [σ' HH8]]. exists t'. exists σ'. intuition.
    destruct H14.
    inversion H15; subst.
    + apply (Preserve Σ' d' φ' ϰ'); intuition. eapply disjointq_scale; eauto. apply stp_qstp_inv in H0. apply qstp_empty in H0; auto.
      eapply disjointq_same in H19 as H19'; auto. 2: eapply H11. 2: eapply H18. destruct H19'. subst.
      eapply t_sub. eauto. apply stp_scale_qqplus. eapply weaken_2D_stp_store_ext; eauto. eapply disjointq_closed; eauto. rewrite qqplus_qbot_right_neutral; auto.
      rewrite qqplus_qbot_right_neutral; auto. eapply kill_sep_local_locs_base; eauto.
    + eapply disjointq_grow in H19 as H19'; auto. 2: eapply H11. 2: eapply H18.
      destruct (♦∈?d1) eqn:Hfresh.
      * apply (Preserve ([(T0, q)] :: Σ) d' (φ ⊔ &! (‖ Σ ‖)) ϰ'); intuition. eapply disjointq_scale; eauto. apply stp_qstp_inv in H0. apply qstp_empty in H0; auto.
        eapply t_sub. eauto. apply stp_scale_qqplus. eapply weaken_stp_store_ext; eauto. eapply disjointq_closed; eauto. apply Qqplus_bound. rewrite qor_assoc_23. clear - H1. Qcrush. rewrite qor_assoc_23. inversion H19; subst. clear. Qcrush. clear. Qcrush.
        rewrite qqplus_fresh in H20. 2: auto. (* d' must be ∅ *)
        rewrite qqplus_fresh. 2:{ apply stp_qstp_inv in H0. apply qstp_empty in H0; auto. clear - H0 Hfresh. Qcrush. }
        apply has_type_local_loc_sep in H20. apply kill_sep_qor_rev in H20; destruct H20. apply kill_sep_qor. eapply kill_sep_local_locs_grow; eauto. destruct H11 as [? [Hlen ?]]. rewrite Hlen; eauto. auto.
      * replace ((d1 ⋓ d')) with d1 in H20. 2: { clear - Hfresh. Qcrush. rewrite Hfresh. auto. }
        apply (Preserve ([(T0, q)] :: Σ) ∅ (φ ⊔ &! (‖ Σ ‖)) ϰ'); intuition. rewrite qqplus_qbot_right_neutral.
        eapply t_sub. eauto. eapply weaken_stp_store_ext; eauto.
         rewrite qor_assoc_23. clear - H1. Qcrush.
        eapply kill_sep_local_locs_grow; eauto. destruct H11 as [? [Hlen ?]]. rewrite Hlen; eauto.
    + apply (Preserve Σ' d' (q_remove Σ' l φ) (ϰ ⊔ &! l)); intuition. eapply disjointq_scale; eauto. apply stp_qstp_inv in H0. apply qstp_empty in H0; auto.
      eapply disjointq_same in H19 as H19'; auto. 2: eapply H11. 2: eapply H18. destruct H19'. subst.
      eapply t_sub. eauto. apply stp_scale_qqplus. eapply weaken_stp_store_ext; eauto. eapply disjointq_closed; eauto. rewrite qqplus_qbot_right_neutral; auto.
      eapply q_remove_sub'; eauto. eapply kill_sep_kill_sub. 2: eauto. clear - H24. Qcrush; subst; auto.
      rewrite qqplus_qbot_right_neutral; auto. eapply kill_sep_local_locs_base; eauto.

  - (* t_withr *) right. subst. intuition.
    apply (CtxOK_kill_closed) in H13 as Hclϰ. apply CtxOK_kill_sep in H13 as Hwfkill.
    apply has_type_closed in H as HH. simpl in Hwfstep; destruct Hwfstep as [Hwfs1 [Hwfs2 Hll2]].
    intuition.
    specialize (H12 T1 t1). intuition.
    + (* contraction *)
      apply (has_type_vtp Hclϰ) in H as Hvtp; auto. specialize (has_type_filter H) as Hflt.
      exists (twithc (‖σ‖) (t2 <~ᵗ tunit; (&‖σ‖))). exists ((Some [t1]) :: σ). split. constructor; auto. (*ctxok*) inversion H13. intuition. rename H21 into Hlen.
      apply (Preserve ([(T1,d1)] :: Σ) ∅ (φ ⊔ &!‖Σ‖) ϰ); auto.
      eapply env_fresh; eauto. eapply kill_sep_sub_fresh; eauto.
      apply wf_senv_after_ref; auto.
      rewrite <- Hlen. eapply CtxOK_weaken; auto. clear - Hflt H0. eapply Subqual_non_fresh; auto.
      rewrite qqplus_qbot_right_neutral.
      (* has_type part *)
      rewrite Hlen. apply t_withc with (φ:=(φ ⊔ &! (‖ Σ ‖))); auto. rename H4 into HT. simpl in HT.
      assert (Hvtploc: vtp ([(T1, d1)] :: Σ) ϰ (φ ⊔ &! (‖ Σ ‖)) (tloc (‖Σ‖) 0) (TRef d1 T1) &!(‖Σ‖)). {rewrite <- senv_length_coersion.
        eapply vtp_loc. 6: {  rewrite sindexr_head; eauto. simpl. eauto. } 8,10,11: eapply qstp_refl; simpl. 6,7: eapply stp_refl; simpl; eauto. simpl; clear; Qcrush. 2,3: eapply closed_Qual_monotone; eauto. 1,3,4: eapply closed_ty_monotone; eauto. Qcrush. 1-3: eapply closed_qual_monotone; eauto. auto.
        eapply kill_sep_fresh_loc; eauto.
      }
      eapply substitution2_withr in HT; eauto. unfold open_tm' in HT; simpl in HT. erewrite <- open_subst2_tm in HT; eauto.
      eapply weaken_flt. eapply HT. clear - H5. Qcrush.
      eapply closed_Qual_qor. eapply closed_Qual_monotone; eauto. simpl; clear; Qcrush.
      apply wf_senv_after_ref; auto.
      (* local locs t2 is just empty *) unfold open_tm'. rewrite local_locs_open'; auto. rewrite local_locs_open'; auto. rewrite Hll2. unfold kill_sep; clear; Qcrush.
      eapply closed_ty_monotone; eauto.
      eapply closed_Qual_monotone; eauto.
      eapply kill_sep_newloc_kill; auto.
      apply wf_store_app; auto. eapply wf_step_preserve. 3: eapply step_twithr; eauto. auto. constructor; auto.

    + (* congrance *) specialize (H12 σ H13). destruct H12 as [t1' [σ' [Hstep Hpreserve]]]. auto.
      exists (twithr t1' t2). exists (σ'). split. constructor; auto.
      inversion Hpreserve; subst.
      assert (Heq: (d1 ⋓ d') = d1). { clear - H0. Qcrush. destruct (fst (fst (fst d1))); auto. simpl in H0. exfalso; auto. } rewrite Heq in H24.
      (* if φ' becomes smaller, we use weaken_flt to retype *)
      inversion H18; subst.
      * (* base *) eapply disjointq_same in H23; auto. 2: eapply H13. 2: eapply H22. destruct H23. subst.
        apply (Preserve Σ' ∅ φ' ϰ'); auto. rewrite qqplus_qbot_right_neutral.
        eapply t_withr with (φd := φd). eauto. clear - H0. Qcrush. eapply closed_ty_monotone; eauto. eapply closed_Qual_monotone; eauto. eapply closed_tm_monotone; eauto.
        eapply weaken_flt. eapply weaken_2D_store. eauto. auto.
        apply closed_qenv_extend; auto. apply closed_qenv_extend; auto. apply closed_qenv_empty. apply []. auto. Qcrush.
        apply has_type_closed in H4; rewrite H28; intuition; auto. auto.
        eapply kill_sep_kill_sub. 2: eauto. eapply local_locs_step_same. 4: eauto. all: auto.
        constructor; auto.
      * (* weaken *) eapply disjointq_grow in H23 as H23'; auto. 2: eauto. 2: eauto. remember ((φ ⊔ &! (‖ Σ ‖))) as φ'. remember ([(T0, q)] :: Σ) as Σ'.
        apply (Preserve Σ' ∅ φ' ϰ'); auto. simpl. rewrite Hll2. rewrite qor_empty_right. auto.
        replace (d1 ⋓ d') with d1 in H22. rewrite qqplus_qbot_right_neutral.
        eapply t_withr with (φd := φd ). eauto. clear - H0. Qcrush. eapply closed_ty_monotone; eauto. eapply closed_Qual_monotone; eauto. eapply closed_tm_monotone; eauto.
        subst. eapply weaken_flt. eapply weaken_2D_store. eauto. auto.
        apply closed_qenv_extend; auto. apply closed_qenv_extend; auto. apply closed_qenv_empty. apply []. apply wf_senv_closed_qenv_qn; auto.
        simpl. clear. Qcrush.
        apply closed_Qual_qor; simpl.  eapply closed_Qual_monotone; eauto. clear; Qcrush.
        subst φ'. clear - H5. Qcrush.
        {eapply kill_sep_kill_sub. eapply local_locs_step_grow. 4: eauto. all: auto. inversion H13. destruct H29. rename H29 into Hlen.
         rewrite Hlen. apply kill_sep_kill_qor. auto.
         eapply kill_sep_sub. eauto. subst Σ'. eapply kill_sep_newloc_kill; auto.  } (* it requires the new grow q is closed under Σ *)
        eapply wf_step_preserve. 3: eapply step_c_twithr_l; eauto. auto. constructor; auto.
      * (* kill *) remember (ϰ ⊔ &! l) as ϰ'. eapply disjointq_same in H23. 2: eapply H13. 2: eapply H22. apply (Preserve Σ' ∅ (q_remove Σ' l φ) ϰ'); auto. simpl. rewrite Hll2. rewrite qor_empty_right. auto.
        rewrite qqplus_qbot_right_neutral.
        eapply t_withr with (φd:=φd). eauto. clear - H0. Qcrush. eapply closed_ty_monotone; eauto. eapply closed_Qual_monotone; eauto. eapply closed_tm_monotone; eauto.
        eauto.
        eapply q_remove_sub; eauto. eapply kill_sep_kill_sub. 2: eauto. clear - H28. Qcrush. subst; auto.
        eapply kill_sep_kill_sub. 2: eauto. eapply local_locs_step_same. 4: eauto. all: auto. destruct H23; auto.
        eapply wf_step_preserve. 3: eapply step_c_twithr_l; eauto. auto. constructor; auto.

  - (* twithc *) subst. right. intuition. apply has_type_closed in H0 as ?. intuition.
    inversion H9; subst. intuition. rename H7 into IH. specialize (IH T0 t eq_refl eq_refl eq_refl). apply CtxOK_kill_closed in H9 as Hclϰ. destruct IH.
    + exists t. exists (update σ l None). split. constructor; auto. apply (Preserve Σ ∅ (q_remove Σ l φ) (ϰ ⊔ &!l)); auto.
      apply env_kill; auto. simpl. Qcrush.
      apply CtxOK_kill; auto.
      (* we can avoid these wf_senv_kill premises by directly proving has_type_retype, which make use of fact that d does not change *)
      rewrite qqplus_qbot_right_neutral. apply has_type_value_retype; auto.
      apply wf_store_update; auto.

    + (* congruence *) specialize (H7 σ H9 H10). destruct H7 as [t' [σ' H7]].
      destruct H7 as [Hstep Hpreserve].
      exists (twithc l t'). exists (σ'). split. constructor; auto.
      inversion Hpreserve; subst. inversion H20; subst.
      * apply (Preserve Σ' ∅ φ' ϰ'); auto. eapply disjointq_same in H25; auto. 2: eapply H9. 2: eapply H24. destruct H25; subst. rewrite qqplus_qbot_right_neutral. rewrite qqplus_qbot_right_neutral in H26.
        eapply t_withc; auto. lia. 1-2: rewrite H30; auto.
      * apply (Preserve ([(T, q)] :: Σ) (d') (φ ⊔ &! (‖ Σ ‖)) ϰ'); auto.
        eapply t_withc; auto.
        simpl; auto. eapply closed_ty_monotone; eauto. apply has_type_closed in H26; intuition.
        eapply kill_sep_sub. eapply (@Qqplus_bound _ _ (d ⊔ d')); eauto. eapply kill_sep_qor. auto.
          inversion H25; subst. eapply kill_sep_empty. unfold kill_sep. clear - H. Qcrush.
      * eapply disjointq_same in H25; auto. 2: eapply H9. 2: eapply H24. destruct H25; subst.
        apply (Preserve Σ' ∅ (q_remove Σ' l0 φ) (ϰ ⊔ &! l0)); auto.
        simpl. apply env_kill; auto. clear - H30. Qcrush.
        rewrite qqplus_qbot_right_neutral. rewrite qqplus_qbot_right_neutral in H26. eapply t_withc; auto.
  Unshelve.
Qed.
