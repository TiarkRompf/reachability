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

Import QualNotations.
Local Open Scope qualifiers.
Import OpeningNotations.
Local Open Scope opening.

Import SplicingNotations.
Local Open Scope splicing.
Import SubstitutionNotations.
Local Open Scope substitutions.



Lemma open_tm'_len : forall {A} {Γ Γ' : list A} {t}, ‖Γ‖ = ‖Γ'‖ -> open_tm' Γ t = open_tm' Γ' t.
  intros.  unfold open_tm'. rewrite H. auto.
Qed.

Lemma open_ty'_len : forall {A} {Γ Γ' : list A} {T}, ‖Γ‖ = ‖Γ'‖ -> open_ty' Γ T = open_ty' Γ' T.
  intros.  unfold open_ty'. rewrite H. auto.
Qed.

Lemma openq'_len : forall {A} {Γ Γ' : list A} {q}, ‖Γ‖ = ‖Γ'‖ -> openq' Γ q = openq' Γ' q.
  intros.  unfold openq'. rewrite H. auto.
Qed.

Lemma open_ty_preserves_size: forall T d j x, ty_size T = ty_size (open_rec_ty j (TVar (varF x)) d T).
Proof.  induction T; intros; simpl; eauto. destruct v. auto. destruct (Nat.eqb j i); auto.
Qed.

Lemma closed_Qual_qdom_squish : forall {Σ : senvs}, closed_Qual 0 0 (‖Σ‖) (qdom Σ)↑.
  intros. Qcrush.
Qed.
(* #[global] Hint Resolve closed_Qual_qdom_squish : core.
  By adding this, the compile time will increase
*)


Lemma closed_Qual_qdom : forall {Σ : senv}, closed_Qual 0 0 (‖Σ‖) (qdom Σ)↑.
  intros. rewrite qdom_squish. Qcrush. rewrite <- squish_length; auto.
Qed.
#[global] Hint Resolve closed_Qual_qdom : core.

Lemma closed_qual_qdom : forall {Σ : senv}, closed_qual 0 0 (‖Σ‖) (qdom Σ).
  intros. apply Q_lift_closed. auto.
Qed.
#[global] Hint Resolve closed_qual_qdom : core.


Lemma just_fv_closed : forall {x b f l fr}, x < f <-> closed_qual b f l (${ fr } x).
Proof.
  split; intros.
  - apply Q_lift_closed. Qcrush.
  - apply Q_lift_closed' in H. Qcrush.
Qed.

Lemma just_loc_closed : forall {x b f l fr}, x < l <-> closed_qual b f l (&{ fr } x).
Proof.
  split; intros.
  - apply Q_lift_closed. Qcrush.
  - apply Q_lift_closed' in H. Qcrush.
Qed.

Lemma subqual_qor_drop_loc : forall d q l,
  d ⊑↑ q ⊔ &!l -> ~(l ∈ₗ d) -> d ⊑↑ q.
Proof.
  intros. Qcrush. specialize (H x H3). destruct H; auto; intuition.
  specialize (H2 x H3). destruct H2; auto; intuition.
  specialize (H4 x H3). destruct H4; auto. subst. intuition.
Qed.

Lemma subqual_qor_drop_var : forall d q i,
  d ⊑↑ q ⊔ $!i -> ~($i ∈ᵥ d) -> d ⊑↑ q.
Proof.
  intros. Qcrush. specialize (H x H3). destruct H; auto. subst. intuition.
  specialize (H2 x H3). destruct H2; auto; intuition.
  specialize (H4 x H3). destruct H4; auto. intuition.
Qed.

Lemma qor_symm : forall q1 q2, (q1 ⊔ q2) = (q2 ⊔ q1).
Proof.
  intros. apply Q_lift_eq. Qcrush.
Qed.

Lemma qor_assoc_23 : forall {q1 q2 q3}, ((q1 ⊔ q2) ⊔ q3) = ((q1 ⊔ q3) ⊔ q2).
Proof.
  intros. apply Q_lift_eq. Qcrush.
Qed.


Lemma closed_tm_monotone : forall {t b l f}, closed_tm b f l t -> forall {b' f' l'}, b <= b' -> f <= f' -> l <= l' -> closed_tm b' f' l' t.
  intros T b f l H. induction H; intuition.
Qed.

Lemma closed_ty_monotone : forall {T b l f}, closed_ty b f l T -> forall {b' f' l'}, b <= b' -> f <= f' -> l <= l' -> closed_ty b' f' l' T.
  intros T b f l H. induction H; intuition.
  constructor. 1,2: eapply closed_qual_monotone; eauto; lia.
  eapply IHclosed_ty1; eauto. eapply IHclosed_ty2; eauto. lia.
  constructor; auto. eapply closed_qual_monotone; eauto.
  constructor. 1,2: eapply closed_qual_monotone; eauto; lia.
  eapply IHclosed_ty1; eauto. eapply IHclosed_ty2; eauto. lia.
Qed.

Lemma closed_tm_open_id : forall {t b f l}, closed_tm b f l t -> forall {n}, b <= n -> forall {x}, [[n ~> x ]]ᵗ t = t.
  intros t b f l H. induction H; intros; simpl; auto;
    try solve [erewrite IHclosed_tm1; eauto; erewrite IHclosed_tm2; eauto; lia | erewrite IHclosed_tm; eauto; lia].
  destruct (Nat.eqb n x) eqn:Heq; auto. apply Nat.eqb_eq in Heq. lia.
Qed.

Lemma closed_ty_open_id : forall {T b f l}, closed_ty b f l T -> forall {n}, b <= n -> forall {U d}, (open_rec_ty n U d T) = T.
  intros T b f l H. induction H; intros; simpl; auto;
    try solve [erewrite IHclosed_ty1; eauto; erewrite IHclosed_ty2; eauto; lia | erewrite IHclosed_ty; eauto; lia].
  destruct (Nat.eqb n x) eqn: Hnx; intuition.  apply Nat.eqb_eq in Hnx. intuition.
  erewrite IHclosed_ty1; eauto; erewrite IHclosed_ty2; eauto.
  erewrite closed_qual_open_id; eauto. erewrite closed_qual_open_id; eauto. lia. lia.
  erewrite IHclosed_ty; eauto. erewrite closed_qual_open_id; eauto.
  erewrite IHclosed_ty1; eauto; erewrite IHclosed_ty2; eauto.
  erewrite closed_qual_open_id; eauto. erewrite closed_qual_open_id; eauto.
  all : lia.
Qed.

Lemma closed_tm_open : forall {t b f l}, closed_tm (S b) f l t -> forall {x}, x < f -> closed_tm b f l ([[ b ~> $x ]]ᵗ t).
  induction t; intros; simpl; intuition; inversion H; subst; try constructor;
  try solve [apply IHt1; auto | apply IHt2; auto | apply IHt; auto ].
  destruct (Nat.eqb b x0) eqn:Heq; intuition.
  apply Nat.eqb_neq in Heq. constructor. lia. auto. auto. auto.
Qed.

Lemma closed_tm_open' : forall {t b f l}, closed_tm (S b) f l t -> forall {x}, x <= f -> forall {t'}, closed_tm 0 x l t' -> closed_tm b f l ([[ b ~> t' ]]ᵗ t).
  induction t; intros; simpl; intuition; inversion H; subst; try constructor;
  try solve [eapply IHt1; eauto | eapply IHt2; eauto | eapply IHt; eauto ].
  destruct (Nat.eqb b x0) eqn:Heq; intuition. eapply closed_tm_monotone; eauto; lia.
  apply Nat.eqb_neq in Heq. constructor. lia. auto. auto. auto.
Qed.

Lemma closed_ty_open' : forall {T b f l}, closed_ty (S b) f l T -> forall {x}, x <= f ->
  forall {U d}, closed_ty 0 x l U -> closed_qual 0 x l d -> closed_ty b f l ([[ b ~> U ~ d ]]ᵀ T).
  induction T; intros; simpl; intuition; inversion H; subst; try constructor;
    try solve [eapply IHT1; eauto | eapply IHT2; eauto | eapply IHT; eauto ]; intuition.
  destruct (b =? x0) eqn: Hbi; intuition. apply Nat.eqb_eq in Hbi. eapply closed_ty_monotone; eauto. lia.
  apply Nat.eqb_neq in Hbi. intuition.
  all : try eapply closed_qual_open'; eauto.
Qed.

Lemma closed_open_succ : forall {t b f l}, closed_tm b f l t -> forall {j}, closed_tm b (S f) l ([[ j ~> $f ]]ᵗ t).
  induction t; intros; simpl; intuition; inversion H; subst; try constructor;
    try solve [eapply IHt1; eauto | eapply IHt2; eauto | eapply IHt; eauto ].
    destruct (Nat.eqb j x) eqn:Heq. intuition.
    apply Nat.eqb_neq in Heq. inversion H. subst. intuition. lia. auto. auto.
Qed.

Lemma closed_ty_open_succ : forall {T fr b f l}, closed_ty b f l T -> forall {j}, closed_ty b (S f) l ([[ j ~>  (TVar (varF f))  ~  ${fr}f ]]ᵀ T).
  induction T; intros; simpl; intuition; inversion H; subst; try constructor;
    try solve [eapply IHT1; eauto | eapply IHT2; eauto | eapply IHT; eauto ]; try rewrite Q_lift_open_qual; intuition.
   destruct (j =? x) eqn: Heq. apply Nat.eqb_eq in Heq. intuition. apply Nat.eqb_neq in Heq. intuition.
all: eauto using closed_Qual_open_succ.
Qed.

Lemma closed_tm_open_succ : forall {t b f l}, closed_tm b f l t -> forall {j}, closed_tm b (S f) l ([[ j ~> $f ]]ᵗ t).
  induction t; intros; simpl; intuition; inversion H; subst; try constructor;
    try solve [eapply IHt1; eauto | eapply IHt2; eauto | eapply IHt; eauto ].
  bdestruct (j =? x); intuition. lia. auto. auto.
Qed.

Lemma open_rec_tm_commute : forall t i j x y, i <> j ->
  [[i ~> $ x ]]ᵗ ([[j ~> $ y ]]ᵗ t) = [[j ~> $ y ]]ᵗ ([[i ~> $ x ]]ᵗ t).
  induction t; intros; simpl; eauto;
    try solve [rewrite IHt1; eauto; rewrite IHt2; eauto | rewrite IHt; eauto].
  destruct v. intuition.
  destruct (Nat.eqb i i0) eqn:Hii0; destruct (Nat.eqb j i0) eqn:Hji0; simpl;
    try rewrite Hii0; try rewrite Hji0; auto.
  apply Nat.eqb_eq in Hii0. apply Nat.eqb_eq in Hji0. subst. contradiction.
Qed.

Lemma open_rec_ty_commute : forall T frx fry i j x y, i <> j ->
    [[i ~> (TVar (varF x)) ~ ${frx} x ]]ᵀ ([[j ~> (TVar (varF y)) ~ ${fry} y ]]ᵀ T)
  = [[j ~> (TVar (varF y)) ~ ${fry} y ]]ᵀ ([[i ~> (TVar (varF x)) ~ ${frx} x ]]ᵀ T).
  induction T; intros; simpl; eauto;
    try solve [erewrite IHT1; eauto; erewrite IHT2; eauto | erewrite IHT; eauto].
  destruct v. auto.
  destruct (Nat.eqb j i0) eqn:Hji0; simpl; try rewrite Hii0; try rewrite Hji0; auto.
  apply Nat.eqb_eq in Hji0. subst. rewrite <- Nat.eqb_neq in H. rewrite H. simpl.
  rewrite Nat.eqb_refl. auto.
  destruct (Nat.eqb i i0) eqn:Hii0; simpl. auto. rewrite Hji0. auto.
  all: f_equal; try erewrite open_qual_commute; eauto.
Qed.

Lemma open_rec_tm_commute' : forall t i j x t' f l, i <> j -> closed_tm 0 f l t' ->
  [[i ~> $ x ]]ᵗ ([[j ~> t' ]]ᵗ t) = [[j ~> t' ]]ᵗ ([[i ~> $ x ]]ᵗ t).
  induction t; intros; simpl; eauto;
    try solve [erewrite IHt1; eauto; erewrite IHt2; eauto | erewrite IHt; eauto].
  - destruct v. intuition.
    destruct (Nat.eqb i i0) eqn:Hii0; destruct (Nat.eqb j i0) eqn:Hji0; simpl;
      try rewrite Hii0; try rewrite Hji0; auto.
    apply Nat.eqb_eq in Hii0. apply Nat.eqb_eq in Hji0. subst. contradiction.
    eapply closed_tm_open_id; eauto. lia.
Qed.

Lemma open_rec_ty_commute' : forall T  U i j fr x d f l, i <> j -> closed_ty 0 f l U -> closed_qual 0 f l d ->
    [[ i ~> (TVar (varF x)) ~ ${fr}x ]]ᵀ ([[ j ~> U ~ d ]]ᵀ T)
  = [[ j ~> U ~ d ]]ᵀ ([[ i ~> (TVar (varF x)) ~ ${fr}x ]]ᵀ T).
  induction T; intros; simpl; eauto;
    try solve [erewrite IHT1; eauto; erewrite IHT2; eauto | erewrite IHT; eauto].
  destruct v eqn:Heqv; auto.
  destruct (Nat.eqb i0 i) eqn:Hii0; destruct (Nat.eqb j i) eqn:Hji0; simpl;
      try rewrite Hii0; try rewrite Hji0; auto.
  apply Nat.eqb_eq in Hii0. apply Nat.eqb_eq in Hji0. subst. contradiction.
  rewrite Nat.eqb_sym in Hii0. rewrite Hii0. rewrite Nat.eqb_eq in Hii0. subst. rewrite Hji0. simpl. rewrite Nat.eqb_refl. auto.
  rewrite Nat.eqb_eq in Hji0. lia. rewrite Nat.eqb_sym in Hii0. rewrite Hii0. simpl.
  destruct (j =? i0) eqn:Hji00; simpl. erewrite closed_ty_open_id; eauto. lia.
  rewrite Hii0. auto.
  all: f_equal; try erewrite open_qual_commute'; eauto.
Qed.

Lemma open_rec_tm_commute'' : forall t i j t' t'' f l, i <> j -> closed_tm 0 f l t' -> closed_tm 0 f l t'' ->
    [[ i ~> t'']]ᵗ ([[ j ~> t' ]]ᵗ t)
  = [[ j ~> t' ]]ᵗ ([[ i ~> t'' ]]ᵗ t).
  induction t; intros; simpl; eauto;
    try solve [erewrite IHt1; eauto; erewrite IHt2; eauto | erewrite IHt; eauto].
  - destruct v. intuition.
    destruct (Nat.eqb i i0) eqn:Hii0; destruct (Nat.eqb j i0) eqn:Hji0; simpl;
      try rewrite Hii0; try rewrite Hji0; auto.
    apply Nat.eqb_eq in Hii0. apply Nat.eqb_eq in Hji0. subst. contradiction.
    symmetry. eapply closed_tm_open_id; eauto. lia. eapply closed_tm_open_id; eauto. lia.
Qed.

Lemma open_rec_ty_commute'' : forall T i j U' U'' d' d'' f l, i <> j -> closed_ty 0 f l U' -> closed_ty 0 f l U'' -> closed_qual 0 f l d' -> closed_qual 0 f l d'' ->
    [[ i ~> U'' ~ d'']]ᵀ ([[ j ~> U' ~ d' ]]ᵀ T)
  = [[ j ~> U' ~ d' ]]ᵀ ([[ i ~> U'' ~  d'' ]]ᵀ T).
  induction T; intros; simpl; eauto;
    try solve [erewrite IHT1; eauto; erewrite IHT2; eauto | erewrite IHT; eauto].
  destruct v eqn:Heqv. auto.
  destruct (Nat.eqb i0 i) eqn:Hii0; destruct (Nat.eqb j i) eqn:Hji0; simpl;
      try rewrite Hii0; try rewrite Hji0; auto.
    apply Nat.eqb_eq in Hii0. apply Nat.eqb_eq in Hji0. subst. lia.
  rewrite Nat.eqb_sym in Hii0. rewrite Hii0. rewrite Nat.eqb_eq in Hii0. subst.
  rewrite Hji0. simpl. rewrite Nat.eqb_refl. erewrite closed_ty_open_id; eauto. lia.
  rewrite Nat.eqb_eq in Hji0. lia.
  rewrite Nat.eqb_sym in Hii0. rewrite Hii0. simpl.
  destruct (j =? i0) eqn:Hji00; simpl. erewrite closed_ty_open_id; eauto. lia.
  rewrite Hii0. auto.
  all: f_equal; try erewrite open_qual_commute''; eauto.
Qed.

Lemma open_qual_empty_id : forall k q fr, [[ k ~> q]]ᵈ ∅{ fr } = ∅{ fr }.
  Qcrush.
Qed.

Lemma closed_tm_open'_id : forall {t f l}, closed_tm 0 f l t -> forall {A} {G : list A}, t <~²ᵗ G = t.
  intros. unfold open_tm'. unfold open_tm. repeat erewrite closed_tm_open_id; eauto.
Qed.

Lemma closed_ty_open'_id : forall {T f l}, closed_ty 0 f l T -> forall {A} {G : list A}, T <~²ᵀ G = T.
  intros. unfold open_ty'. unfold open_ty. repeat erewrite closed_ty_open_id; eauto.
Qed.

Lemma closed_qual_open'_id : forall {q f l}, closed_qual 0 f l q -> forall {A} {G : list A}, q <~²ᵈ G = q.
  intros. unfold openq'. unfold openq. repeat erewrite closed_qual_open_id; eauto.
Qed.


Lemma splice_closed : forall {T b n m l}, closed_tm b (n + m) l T -> closed_tm b (S (n + m)) l (T ↑ᵗ m).
  induction T; simpl; intros; inversion H; subst; intuition.
  destruct (le_lt_dec m x) eqn:Heq; intuition.
Qed.

Lemma splice_Qual_closed : forall {d b n m l}, closed_Qual b (n + m) l d ↑ -> forall {i}, i <= m -> closed_Qual b (S (n + m)) l (d ↑ᵈ i) ↑.
intros. Qcrush. bdestruct (x <=? i); intuition. eauto using Nat.lt_pred_lt_succ.
Qed.

Lemma splice_qual_closed : forall {d b n m l}, closed_qual b (n + m) l d -> forall {i}, i <= m -> closed_qual b (S (n + m)) l (d ↑ᵈ i).
intros. apply Q_lift_closed. apply Q_lift_closed' in H. eauto using splice_Qual_closed.
Qed.

Lemma splice_ty_closed : forall {T b n m l}, closed_ty b (n + m) l T -> forall {i}, i <= m -> closed_ty b (S (n + m)) l (T ↑ᵀ i).
  induction T; simpl; intros; inversion H; subst; intuition.
  destruct (le_lt_dec i x); auto. intuition.
  all: constructor; try apply splice_qual_closed; auto.
Qed.

Lemma splice_closed' : forall {T b l} {A} {D : A} {ρ ρ'}, closed_tm b (‖ρ ++ ρ'‖) l T -> closed_tm b (‖ρ ++ D :: ρ'‖) l (T ↑ᵗ ‖ρ'‖).
  intros. rewrite app_length in H.
  replace (‖ ρ ++ D :: ρ' ‖) with (S (‖ρ‖ + ‖ρ'‖)).
  apply splice_closed. auto. simpl. rewrite app_length. simpl. lia.
Qed.

Lemma splice_qual_closed' : forall {d b l} {A} {D : A} {ρ ρ'}, closed_qual b (‖ρ ++ ρ'‖) l d -> closed_qual b (‖ρ ++ D :: ρ'‖) l (d ↑ᵈ ‖ρ'‖).
  intros. rewrite app_length in H.
  replace (‖ ρ ++ D :: ρ' ‖) with (S (‖ρ‖ + ‖ρ'‖)).
  eapply splice_qual_closed; eauto. simpl. rewrite app_length. simpl. lia.
Qed.

Lemma splice_ty_closed' : forall {T b l} {A} {D : A} {ρ ρ'}, closed_ty b (‖ρ ++ ρ'‖) l T -> closed_ty b (‖ρ ++ D :: ρ'‖) l (T ↑ᵀ ‖ρ'‖).
  intros. rewrite app_length in H.
  replace (‖ ρ ++ D :: ρ' ‖) with (S (‖ρ‖ + ‖ρ'‖)).
  eapply splice_ty_closed; eauto. simpl. rewrite app_length. simpl. lia.
Qed.

Lemma splice_Qual_closed'' : forall {q x b l k}, closed_Qual b x l q ↑ -> k <= x -> closed_Qual b (S x) l (q ↑ᵈ k) ↑.
intros. Qcrush. bdestruct (x0 <=? k); intuition. eauto using Nat.lt_pred_lt_succ.
Qed.

Lemma splice_qual_closed'' : forall {q x b l k}, closed_qual b x l q -> k <= x -> closed_qual b (S x) l (q ↑ᵈ k).
intros. apply Q_lift_closed. eauto using splice_Qual_closed''.
Qed.

Lemma splice_ty_closed'' : forall {T x b l k}, closed_ty b x l T -> k <= x -> closed_ty b (S x) l (T ↑ᵀ k).
  induction T; simpl; intros; inversion H; subst; try eapply closed_ty_monotone; eauto.
  destruct (le_lt_dec k x0); auto. intuition.
  all: constructor; try eapply splice_qual_closed''; eauto.
Qed.

Lemma splice_open_succ : forall {T b n l j}, closed_tm b n l T -> ([[ j ~> $n ]]ᵗ T) ↑ᵗ n = [[ j ~> $ (S n) ]]ᵗ T.
  induction T; simpl; intros; inversion H; subst; auto;
    try solve [erewrite IHT1; eauto; erewrite IHT2; eauto | erewrite IHT; eauto].
  destruct (PeanoNat.Nat.eqb j x) eqn:Heq; auto. simpl.
  destruct (le_lt_dec n n) eqn:Heq'; auto. lia.
  simpl. destruct (le_lt_dec n x) eqn:Heq; auto. lia.
Qed.

Lemma gt_n_lt_sn_absurd : forall {x n}, x > n -> x < S n -> False.
intros. lia.
Qed.

Lemma splice_Qual_open_succ : forall {d b fr n l j}, closed_Qual b n l d ↑ ->
  ([[j ~> ${fr}n ]]ᵈ d) ↑ᵈ n = [[j ~> ${fr}(S n) ]]ᵈ d.
intros. qual_destruct d. unfold_q.
#[local] Hint Resolve n_reflect_true : bdestruct.
bdestruct (bvs j); simpl; apply Q_lift_eq.
#[local] Remove Hints n_reflect_true : bdestruct.
all: Qcrush.
1,4: bdestruct (x <? n); intuition; bdestruct (x =? n); intuition; assert (x > n) by lia; intuition; exfalso; eauto using gt_n_lt_sn_absurd,Nat.lt_pred_lt_succ.
all: exfalso; eauto.
Qed.

Lemma splice_qual_open_succ : forall {d b fr n l j}, closed_qual b n l d ->
  ([[j ~> ${fr}n ]]ᵈ d) ↑ᵈ n = [[j ~> ${fr}(S n) ]]ᵈ d.
intros. apply Q_lift_closed' in H. eauto using splice_Qual_open_succ.
Qed.

Lemma splice_ty_open_succ : forall {T b fr n l j}, closed_ty b n l T -> ([[ j ~> $n ~ ${fr} n ]]ᵀ T) ↑ᵀ n = [[ j ~> $(S n) ~ ${fr} (S n) ]]ᵀ T.
  induction T; simpl; intros; inversion H; subst; auto;
    try solve [erewrite IHT1; eauto; erewrite IHT2; eauto | erewrite IHT; eauto]. simpl.
  destruct (le_lt_dec n x); auto. intuition.
  destruct (j =? x); auto. simpl. destruct (le_lt_dec n n); auto. intuition.
  erewrite splice_qual_open_succ; eauto.
  erewrite IHT1; eauto. erewrite IHT2; eauto.
  erewrite splice_qual_open_succ; eauto.
  erewrite IHT1; eauto. erewrite IHT2; eauto.
  erewrite splice_qual_open_succ; eauto.
  erewrite splice_qual_open_succ; eauto.
  erewrite IHT; eauto. erewrite splice_qual_open_succ; eauto.
Qed.


Lemma closed_ty_open2 : forall {f l d1 d2 T T1 T2}, closed_ty 2 f l T -> closed_ty 0 f l T1 -> closed_qual 0 f l d1 -> closed_ty 0 f l T2 -> closed_qual 0 f l d2 -> closed_ty 0 f l ([[1 ~> T1 ~ d1 ]]ᵀ ([[0 ~> T2 ~ d2 ]]ᵀ T)).
  intros. erewrite open_rec_ty_commute''; eauto. eapply closed_ty_open'; eauto. eapply closed_ty_open'; eauto.
Qed.



Lemma indexr_splice_tenv : forall {Γ1 i Γ2 b U du},
    indexr i (Γ1 ++ Γ2) = Some ((bind_tm, b, U, du)) -> forall {k}, ‖Γ2‖ <= i ->
    indexr i (Γ1 ↑ᴳ k ++ Γ2) = Some ((bind_tm, b, U ↑ᵀ k, du ↑ᵈ k)).
  induction Γ1; intros; simpl in *; intuition. apply indexr_var_some' in H. lia.
  rewrite app_length in *. erewrite splice_env_length; eauto.
  destruct (Nat.eqb i (‖ Γ1 ‖ + ‖ Γ2 ‖)) eqn:Heq. inversion H. subst.
  simpl.  intuition.   apply IHΓ1; eauto.
Qed.

Lemma indexr_splice_ty_tenv : forall {Γ1 i Γ2 b U du},  indexr i (Γ1 ++ Γ2) = Some ((bind_ty, b, U, du)) ->
forall {k}, k <= i -> (length Γ2) <= i -> indexr i (splice_tenv k Γ1 ++ Γ2) = Some ((bind_ty, b, splice_ty k U, splice_qual k du)).
Proof.  induction Γ1; intros; simpl in *; intuition. apply indexr_var_some' in H. lia.
  rewrite app_length in *. unfold splice_tenv. erewrite splice_env_length; eauto.
  destruct (Nat.eqb i (‖ Γ1 ‖ + ‖ Γ2 ‖)) eqn:Heq.  inversion H. subst.
  simpl. auto. apply IHΓ1; eauto.
Qed.

Lemma qqplus_fresh : forall {d d'}, ♦∈ d -> (d ⋓ d') = (d ⊔ d').
intros. unfold qqplus, qfresh in *. apply Is_true_eq_true in H. rewrite H. auto.
Qed.


Lemma wf_tenv_prop : forall {Γ Σ}, wf_tenv Γ Σ -> forall l bd fr T q, indexr l Γ = Some (bd, fr, T, q) -> (closed_ty 0 l (‖ Σ ‖) T /\ closed_Qual 0 l (‖ Σ ‖) q↑).
  intros Γ Σ Hwf. induction Hwf; intros. simpl in H0. discriminate. destruct (l =? ‖Γ‖) eqn:Heq.
  - simpl in H1. rewrite Heq in H1. inversion H1. subst. apply Nat.eqb_eq in Heq. subst. intuition; eauto using closed_Qual_monotone,closed_ty_monotone.
  - simpl in H1. rewrite Heq in H1. apply IHHwf in H1. intuition; eauto using closed_Qual_monotone,closed_ty_monotone.
Qed.

Lemma wf_tenv_wf_senv : forall {Γ Σ}, wf_tenv Γ Σ -> wf_senv Σ.
  intros Γ Σ Hwf. induction Hwf; intros; auto.
Qed.
#[global] Hint Resolve wf_tenv_wf_senv : core.

Lemma wf_tenv_closed_qenv :
  forall Γ Σ, wf_tenv Γ Σ -> closed_qenv 0 (‖ Γ ‖) (‖ Σ ‖) Γ.
intros. induction Γ; unfold closed_qenv.
- intros. simpl in *. discriminate.
- inversion H. subst. intros. bdestruct (x =? (‖ Γ ‖)). subst. rewrite indexr_head in H0. inversion H0. subst. simpl. eapply closed_Qual_monotone; eauto. auto. destruct a as [ [ [bd' fr'] T'] q']. simpl. specialize (wf_tenv_prop H x bd' fr' T' q'). intuition. eapply closed_Qual_monotone; eauto. apply indexr_var_some' in H0. simpl in H0. lia.
Qed.


Lemma wf_senv_prop : forall {Σ}, wf_senv Σ -> forall l o T q, sindexr l o Σ = Some (T, q) -> (closed_ty 0 0 (‖ Σ ‖) T /\ closed_Qual 0 0 (‖ Σ ‖) q ↑ /\ ♦∉ q).
  intros Σ Hwf. unfold wf_senv in Hwf. intros. apply sindexr_var_some' in H as H'. destruct H' as [H' [c [H1 H2]]].
  specialize (Hwf l c H1). unfold wf_senvc, wf_senvs in Hwf. destruct Hwf. erewrite sindexr_indexr_rewrite in H; eauto. specialize (H3 o T q H).  intuition.
Qed.

Lemma wf_senv_closed_qenv :
  forall Σ, wf_senv Σ -> closed_qenv 0 0 (‖ Σ ‖) (squish Σ).
  intros. unfold closed_qenv; intros. unfold wf_senv in *. destruct a as [T q]. apply indexr_squish_c_exists in H0 as H1. destruct H1 as [c [H1 [H2 H3]]]. subst.
  apply H in H1 as H'. unfold wf_senvc in H'. destruct H'. apply wf_senvs_qunify in H3; destruct H3. Qcrush.
Qed.
#[global] Hint Resolve wf_senv_closed_qenv : core.


Lemma closed_Qual_open2 : forall {f l d1 d2 d}, closed_Qual 2 f l d ↑ -> closed_Qual 0 f l d1 ↑ -> closed_Qual 0 f l d2 ↑ -> closed_Qual 0 f l ([[1 ~> d1 ]]ᵈ ([[0 ~> d2 ]]ᵈ d)) ↑.
  intros. apply Q_lift_closed'. erewrite open_qual_commute''; eauto using closed_qual_open'.
Qed.

Lemma open_qual_subqual : forall {d1 d2 φ}, d1 ⊑↑ φ -> forall {k}, ([[ k ~> ∅ ]]ᵈ d2) ⊑↑ φ -> ([[ k ~> d1 ]]ᵈ d2) ⊑↑ φ.
  intros. qual_destruct d2.
unfold_q. ndestruct (bvs k); simpl; auto. Qcrush.
Qed.

Lemma openq_subqual : forall {df d1 d2 φ f l}, closed_Qual 0 f l φ↑ -> df ⊑↑ φ -> d1 ⊑↑ φ -> d2 <~ᵈ ∅; ∅ ⊑↑ φ -> d2 <~ᵈ df; d1 ⊑↑ φ.
  intros. unfold openq in *. apply open_qual_subqual; auto. erewrite open_qual_commute''; eauto.
  erewrite open_qual_commute'' in H2; eauto. apply open_qual_subqual; auto.
  Unshelve. all : apply 0.
Qed.


Lemma qmem_plus_decomp : forall {x0 q x}, x0 ∈ₗ q ⊔ &!x -> closed_Qual 0 0 x q↑ -> x0 ∈ₗ q \/ x0 = x.
  intros. assert (x0 ∈ₗ q \/ x0 ∈ₗ &! x); Qcrush.
Qed.

Lemma closed_Qual_subq_qdom_squish : forall q (Σ: senv),
  closed_Qual 0 0 (‖ Σ ‖) q ↑ ->
  q ⊑↑ (qdom (squish Σ)).
intros. unfold qdom. Qcrush; eauto. rewrite squish_length. eauto.
Qed.

Lemma closed_Qual_subq_qdom : forall q (Σ: senv),
  closed_Qual 0 0 (‖ Σ ‖) q ↑ ->
  q ⊑↑ (qdom Σ).
  intros. rewrite qdom_squish. apply closed_Qual_subq_qdom_squish; auto.
Qed.

Lemma qdom_cons_qor: forall a (Σ : senv),
  (qdom (a :: Σ)) = (qdom Σ ⊔ &! (‖ Σ ‖)).
intros. apply Q_lift_eq. rewrite Q_lift_or. repeat rewrite Q_lift_qdom. Qcrush; simpl in *. lia. lia. bdestruct (x =? (‖ Σ ‖)); intuition.
Qed.


Lemma wf_tenv_splice_lower_id : forall Γ1 Γ2 Σ d,
  wf_tenv Γ2 Σ ->
  forall n, (‖ Γ2 ‖) <= n ->
  q_trans_tenv (Γ1 ++ Γ2 ↑ᴳ n) d =
  q_trans_tenv (Γ1 ++ Γ2) d.
intros. unfold q_trans_tenv. repeat rewrite app_length. erewrite splice_env_length; eauto. remember (‖ Γ1 ‖ + ‖ Γ2 ‖). generalize dependent Γ1. generalize dependent n. induction Γ2; intros; simpl; auto. inversion H. subst. simpl. erewrite splice_ty_id; eauto using closed_ty_monotone. erewrite splice_qual_id; eauto using closed_Qual_monotone. replace (Γ1 ++ (bd, fr, T, q) :: Γ2 ↑ᴳ n) with ((Γ1 ++ [(bd, fr, T, q)]) ++ Γ2 ↑ᴳ n) by intuition. replace (Γ1 ++ (bd, fr, T, q) :: Γ2) with ((Γ1 ++ [(bd, fr, T, q)]) ++ Γ2) by intuition. erewrite IHΓ2; eauto. simpl in H0. lia. simpl. rewrite app_length. simpl. lia.
Qed.

Lemma wf_tenv_splice_lower_id' : forall Γ1 Γ2 X Σ d,
  wf_tenv Γ2 Σ ->
  forall n, (‖ Γ2 ‖) <= n ->
  q_trans_tenv (Γ1 ++ X :: Γ2 ↑ᴳ n) d =
  q_trans_tenv (Γ1 ++ X :: Γ2) d.
intros. replace (Γ1 ++ X :: Γ2 ↑ᴳ n) with ((Γ1 ++ [X]) ++ Γ2 ↑ᴳ n) by intuition. erewrite wf_tenv_splice_lower_id; eauto. replace ((Γ1 ++ [X]) ++ Γ2) with (Γ1 ++ X :: Γ2) by intuition. auto.
Qed.

Lemma wf_senvs_splice_id : forall Σ n L,
  wf_senvs L Σ ->
  Σ ↑ᴳ n = Σ.
induction Σ; intros; simpl; auto. erewrite IHΣ. f_equal. unfold wf_senvs in H. destruct a as [T q]. specialize (H (‖Σ‖) T q). rewrite indexr_head in H. intuition. simpl. erewrite splice_ty_id. erewrite splice_qual_id; auto. eapply closed_Qual_monotone; eauto; lia. eapply closed_ty_monotone; eauto; lia.
apply wf_senvs_shrink in H. eauto.
Qed.

Lemma wf_senv_splice_id : forall Σ n,
  wf_senv Σ ->
  Σ s↑ᴳ n = Σ.
intros. cut (forall l c, indexr l Σ = Some c -> exists X, wf_senvs X c). intros. 2:{ intros. unfold wf_senv in H. apply H in H0. exists (‖ Σ ‖). unfold wf_senvc in H0. intuition. } clear H.
induction Σ; simpl; auto. rewrite IHΣ. f_equal. specialize (H0 (‖Σ‖) a). rewrite indexr_head in H0. intuition. destruct H. erewrite wf_senvs_splice_id; eauto.
  intros. specialize (H0 l c). rewrite indexr_skip in H0. auto. apply indexr_var_some' in H; lia.
Qed.

Lemma closed_qenv_qn_trans_one_closed : forall {p : Type} `{qenv p} (E : env p) q n,
  n >= (‖ E ‖) ->
  closed_qenv_qn n E ->
  closed_Nats n (qenv_Qn q ↑) ->
  closed_Nats n (qenv_Qn (q_trans_one E q) ↑).
intros. generalize dependent n. induction E; intros; simpl; auto. ndestruct (qenv_qn q (‖ E ‖)). erewrite <- @Q_lift_qn with (qn:=qenv_qn); eauto. erewrite qn_or_dist. assert (closed_Nats n (qenv_Qn (q_trans_one E q) ↑)). eapply IHE; eauto. simpl in *. lia. eapply closed_qenv_qn_shrink; eauto.
nlift. repeat erewrite Q_lift_qn; eauto. unfold closed_Nats in *. intros. destruct H5. apply H4. eauto. unfold closed_qenv_qn in H1. specialize (H1 (‖ E ‖) a). eapply H1; eauto. apply indexr_head. apply qenv_qn_prop. apply IHE; eauto. simpl in *. lia. eapply closed_qenv_qn_shrink; eauto. Unshelve. all: try apply qenv_qn_prop.
Qed.

Lemma q_trans''_extend_closed_id : forall {p : Type} `{qenv p} (E E' : env p) q fuel,
  E' ⊇ E ->
  closed_qenv_qn (‖ E ‖) E ->
  closed_Nats (‖ E ‖) (qenv_Qn q ↑) ->
  q_trans'' E' q fuel = q_trans'' E q fuel.
intros. generalize dependent q. induction fuel; intros; simpl; auto. erewrite q_trans_one_extend_closed_id; eauto. rewrite IHfuel; auto. apply closed_qenv_qn_trans_one_closed; auto.
Qed.

Lemma q_trans''_extend_closed_id' : forall {p : Type} `{qenv p} (a : p) (E : env p) q fuel,
  closed_qenv_qn (‖ E ‖) E ->
  closed_Nats (‖ E ‖) (qenv_Qn q ↑) ->
  q_trans'' (a::E) q fuel = q_trans'' E q fuel.
intros. generalize dependent q. induction fuel; intros. simpl; auto. replace (q_trans'' (a :: E) q (S fuel)) with (q_trans'' (a :: E) (q_trans_one (a :: E) q) (fuel)); auto. erewrite q_trans_one_extend_closed_id'; eauto. rewrite IHfuel; auto. apply closed_qenv_qn_trans_one_closed; auto.
Qed.



Lemma subst1_env_length : forall {p : Type} `{substitutable_env p} (E : env p) {v T q}, ‖ { v |-> T ~ q }ᴳ E ‖ = ‖E‖.
  intros. unfold subst_env. rewrite map_length. auto.
Qed.

Lemma closed_qual_subst1'' : forall {q b f l},
    closed_Qual b (S f) l q ↑ ->
    forall {d1 l1}, closed_Qual b f l1 d1 ↑ ->
    forall{l2},
      l <= l2 -> l1 <= l2 ->
      closed_Qual b f l2 (subst_qual q 0 d1) ↑.
Proof.
  intros. qual_destruct q. unfold_q.
  ndestruct (fvs 0); Qcrush; try solve [eauto using Arith_prebase.lt_S_n, Nat.lt_le_trans]; try solve [exfalso; eauto 3].
Qed.

Lemma subst_qual_subqual_monotone' : forall {d1 d2}, d1 ⊑↑ d2 -> forall {df}, ({0 |-> d1 }ᵈ df) ⊑↑ ({0 |-> d2 }ᵈ df).
intros. qual_destruct df. unfold_q. ndestruct (fvs 0). Qcrush. auto.
Qed.

Lemma closed_qenv_subst1_monotone : forall {p : Type} `{substitutable_env p} (E : env p) (b f l : nat) Tx d1 d2,
  d1 ⊑↑ d2 ->
  closed_qenv b f l ({0 |-> Tx ~ d2 }ᴳ E) ->
  closed_qenv b f l ({0 |-> Tx ~ d1 }ᴳ E).
intros. induction E; simpl; auto. unfold subst_env in *. simpl in *. eapply closed_qenv_shrink in H2 as H2'. eapply closed_qenv_extend; intuition. specialize (H2 (‖ E ‖) (env_subst 0 Tx d2 a)). erewrite <- map_length in H2. rewrite indexr_head in H2. intuition. rewrite <- env_subst_qenv_q_dist in *. apply subst_qual_subqual_monotone' with (df:=(qenv_q a)) in H1. Qcrush.
Qed.

Lemma subst_qual_subqual_monotone_fresh : forall {d1 d2}, d1 ⊑↑ d2 ⊔ {♦} -> forall {df}, ({0 |-> df }ᵈ d1) ⊑↑ ({0 |-> df }ᵈ d2) ⊔ {♦}.
Proof.
  intros. qual_destruct d1; qual_destruct d2; qual_destruct df; unfold_q.
  ndestruct (fvs0 0); simpl;
  ndestruct (fvs 0); simpl; Qcrush; eauto.
  all: try match goal with
  | [ H : forall x : nat, N_lift _ x -> _ ,
      H1 : N_lift _ _ |- _ ] =>
      apply H in H1
      end; intuition.
Qed.

Lemma closed_qenv_subst1 : forall {p : Type} `{substitutable_env p} (E : env p) (b f l : nat) Tx dx,
  closed_qenv b (S f) l E ->
  closed_Qual b f l dx ↑ ->
  closed_qenv b f l ({0 |-> Tx ~ dx }ᴳ E).
intros. induction E; simpl; auto. apply closed_qenv_empty. apply []. apply closed_qenv_extend. apply IHE. eapply closed_qenv_shrink; eauto. rewrite <- env_subst_qenv_q_dist. eapply closed_qual_subst1''; eauto. unfold closed_qenv in H1. specialize (H1 (‖ E ‖) a). rewrite indexr_head in H1. intuition.
Qed.

Lemma subst1_ty_id : forall {T b l}, closed_ty b 0 l T -> forall {T1  d1}, { 0 |-> T1 ~ d1 }ᵀ T = T.
  induction T; intros; inversion H; subst; simpl; intuition;
                       try solve [erewrite IHT; eauto];
                       try solve [erewrite IHT1; eauto; erewrite IHT2; eauto].
  erewrite IHT1; eauto. erewrite IHT2; eauto. erewrite subst1_qual_id; eauto.  erewrite subst1_qual_id; eauto.
  erewrite IHT1; eauto. erewrite IHT2; eauto. erewrite subst1_qual_id; eauto.  erewrite subst1_qual_id; eauto.
  erewrite IHT; eauto. erewrite subst1_qual_id; eauto.
Qed.

Lemma subst_ty_id : forall {b l T}, closed_ty b 0 l T -> forall {T1 T2 d1 d2}, { 0 |-> T1 ~ d1 ; T2 ~ d2 }ᵀ T = T.
  intros. repeat erewrite subst1_ty_id; eauto.
Qed.

Lemma subst1_tm_id : forall {t b l}, closed_tm b 0 l t -> forall {t1}, { 0 |-> t1 }ᵗ t = t.
  induction t; intros b loc Hc; inversion Hc; subst; intros; simpl; intuition;
                       try solve [erewrite IHt; eauto];
                       try solve [erewrite IHt1; eauto; erewrite IHt2; eauto].
Qed.

Lemma open_subst1_qual : forall {q b l},
    closed_Qual b 0 l q↑ ->
    forall {k d1},
      [[k ~> d1 ]]ᵈ q = { 0 |-> d1 }ᵈ ([[k ~> $!0 ]]ᵈ q).
  intros. qual_destruct q. qual_destruct d1. unfold_q.
#[local] Hint Resolve n_reflect_true : bdestruct.
bdestruct (bvs k); simpl.
bdestruct (n_or fvs (n_one 0) 0); simpl. apply Q_lift_eq. Qcrush; exfalso; eauto.
exfalso. Qcrush.
bdestruct (fvs 0). apply Q_lift_eq. Qcrush; exfalso; eauto.
apply Q_lift_eq. Qcrush; exfalso; eauto.
#[local] Remove Hints n_reflect_true : bdestruct.
Qed.

Lemma open_subst1_ty : forall {T b l},
    closed_ty b 0 l T ->
    forall {k T1 d1},
      [[k ~> T1 ~ d1 ]]ᵀ T = { 0 |-> T1 ~ d1 }ᵀ ([[k ~> $0 ~ $!0]]ᵀ T).
  induction T; intros; inversion H; subst; simpl; intuition.
  destruct (k =? x); auto.
  erewrite IHT1; eauto. erewrite IHT2; eauto.
  erewrite <- open_subst1_qual; eauto. erewrite <- open_subst1_qual; eauto.
  erewrite IHT1; eauto. erewrite IHT2; eauto.
  erewrite <- open_subst1_qual; eauto. erewrite <- open_subst1_qual; eauto.
  erewrite IHT; eauto. erewrite <- open_subst1_qual; eauto.
Qed.

Lemma open_subst1_tm : forall {t b l},
    closed_tm b 0 l t -> forall {k t1},
      [[k ~> t1 ]]ᵗ t = { 0 |-> t1 }ᵗ ([[k ~> $0]]ᵗ t).
  induction t; intros b loc Hc; inversion Hc; subst; intros; simpl; intuition;
    try solve [erewrite IHt; eauto];
    try solve [erewrite IHt1; eauto; erewrite IHt2; eauto].
  bdestruct (k =? x); simpl; intuition.
Qed.

Fixpoint open_subst1_tm_comm {t : tm} :
  forall {k  g tf ff lf}, closed_tm 0 ff lf tf ->
    [[k ~> $g ]]ᵗ ({0 |-> tf }ᵗ t) = {0 |-> tf }ᵗ ([[ k ~> $(S g) ]]ᵗ  t).
    destruct t; intros; simpl; intuition;
      try solve [repeat erewrite open_subst1_tm_comm; eauto].
    destruct v; simpl.
    bdestruct (i =? 0); simpl. eapply closed_tm_open_id; eauto. lia. auto.
    bdestruct (k =? i); simpl; auto.
Qed.

Fixpoint open_subst1_ty_comm {T : ty} :
  forall {k fr g Tf df ff lf}, closed_ty 0 ff lf Tf ->  closed_qual 0 ff lf df ->
    [[k ~> $g ~ ${fr}g ]]ᵀ ({0 |-> Tf ~ df }ᵀ T) = {0 |-> Tf ~ df }ᵀ ([[ k ~> $(S g) ~ ${fr}(S g) ]]ᵀ  T).
    destruct T; intros; try destruct v; simpl; intuition;
      try solve [repeat erewrite open_subst1_ty_comm; eauto].
    + destruct (i =? 0) eqn: Heq; intuition.  erewrite closed_ty_open_id; eauto. lia.
    + edestruct (k =? 0) eqn: Heq; intuition.
      destruct (k =? i); simpl; auto.  destruct (k =? i); simpl; auto.
    + erewrite open_subst1_qual_comm; eauto. erewrite open_subst1_qual_comm; eauto.
    erewrite open_subst1_ty_comm; eauto. erewrite open_subst1_ty_comm; eauto.
    + erewrite open_subst1_qual_comm; eauto. erewrite open_subst1_qual_comm; eauto.
    erewrite open_subst1_ty_comm; eauto.
    erewrite open_subst1_ty_comm; eauto.
    + erewrite open_subst1_ty_comm; eauto. erewrite open_subst1_qual_comm; eauto.
Qed.

Lemma closed_ty_subst1 : forall {T b f l},
    closed_ty b (S f) l T ->
    forall {T1 d1 l1}, closed_ty 0 0 l1 T1 -> closed_Qual 0 0 l1 d1↑ ->
    forall{l2},
      l <= l2 -> l1 <= l2 ->
      closed_ty b f l2 ({0 |-> T1 ~ d1}ᵀ T).
  intros T b f l Hc. remember (S f) as f'. generalize dependent f.
  induction Hc; intros; subst; simpl in *; intuition; try constructor;
    try solve [eapply IHHc; eauto; lia ];
    try solve [eapply IHHc1; eauto];
    try solve [eapply IHHc2; eauto; lia].
  destruct (x =? 0) eqn: Heq. eapply closed_ty_monotone; eauto; lia.
  constructor. inversion H. subst. eapply Nat.eqb_neq in  Heq. lia.  subst.  lia.
  all: eapply closed_qual_subst1; eauto.
Qed.

Lemma closed_tm_subst1 : forall {t b f l},
    closed_tm b (S f) l t ->
    forall {t1 l1}, closed_tm 0 0 l1 t1 ->
    forall{l2},
      l <= l2 -> l1 <= l2 ->
      closed_tm b f l2 ({0 |-> t1}ᵗ t).
  intros t b f l Hc. remember (S f) as f'.
  generalize dependent f.
  induction Hc; intros; subst; simpl in *; intuition; try constructor;
    try solve [eapply IHHc; eauto; lia ];
    try solve [eapply IHHc1; eauto];
    try solve [eapply IHHc2; eauto].
  bdestruct (x =? 0).
  eapply closed_tm_monotone; eauto; lia. intuition. lia.
Qed.

Lemma open_subst2_qual : forall {q l},
    closed_Qual 2 0 l q ↑ ->
    forall {d1 df}, closed_Qual 0 0 l d1 ↑ ->
    [[1~> df ]]ᵈ ([[0~> d1 ]]ᵈ q) = { 0 |-> d1; df }ᵈ ([[1 ~> $!1]]ᵈ ([[0 ~> $!0]]ᵈ q)).
  intros. erewrite <- open_subst1_qual_comm; eauto.
  erewrite open_subst1_qual; eauto. f_equal. f_equal.
  erewrite open_subst1_qual; eauto. erewrite open_subst1_qual; eauto.
  eapply closed_qual_subst1; eauto. eapply closed_qual_open_succ; eauto.
Qed.

Lemma open_subst2_ty : forall {T l},
    closed_ty 2 0 l T ->
    forall {T1 d1 Tf df}, closed_ty 0 0 l T1 -> closed_Qual 0 0 l d1 ↑ ->
    [[1~> Tf ~ df ]]ᵀ ([[0~> T1 ~ d1 ]]ᵀ T) = { 0 |-> T1 ~ d1; Tf ~ df }ᵀ ([[1 ~> $1 ~ $!1]]ᵀ ([[0 ~> $0 ~ $!0]]ᵀ T)).
  intros. erewrite <- open_subst1_ty_comm; eauto.
  erewrite open_subst1_ty; eauto. f_equal. f_equal.
  erewrite open_subst1_ty; eauto. erewrite open_subst1_ty; eauto.
  eapply closed_ty_subst1; eauto. eapply closed_ty_open_succ; eauto.
Qed.

Lemma open_subst2_tm : forall {t l},
    closed_tm 2 0 l t ->
    forall {t1 tf}, closed_tm 0 0 l t1 ->
    [[1~> tf ]]ᵗ ([[0~> t1 ]]ᵗ t) = { 0 |-> t1; tf }ᵗ ([[1 ~> $1 ]]ᵗ ([[0 ~> $0 ]]ᵗ t)).
  intros. erewrite <- open_subst1_tm_comm; eauto.
  erewrite open_subst1_tm; eauto. f_equal. f_equal.
  erewrite open_subst1_tm; eauto. erewrite open_subst1_tm; eauto.
  eapply closed_tm_subst1; eauto. eapply closed_tm_open_succ; eauto.
Qed.

Lemma indexr_subst1 : forall {x Γ bd b T U d Tx dx},
    x >= 1 ->
    indexr x (Γ ++ [U]) = Some ((bd, b, T, d)) ->
    indexr (pred x) ({ 0 |-> Tx ~ dx }ᴳ Γ) = Some ((bd, b, { 0 |-> Tx ~ dx }ᵀ T, { 0 |-> dx }ᵈ d)).
  intros. destruct x; try lia.
  rewrite <- indexr_insert_ge in H0; simpl; try lia.
  rewrite app_nil_r in H0. induction Γ; intros; simpl in *. discriminate.
  rewrite subst1_env_length. (bdestruct (x =? ‖Γ‖)); auto.
  inversion H0. auto.
Qed.

Lemma indexr_subst1' : forall {x Γ bd b b' T U d du},
    indexr x (Γ ++ [(bd, b, T, d)]) = Some ((bd, b', U, du)) ->
    (x = 0 /\ T = U  /\ d = du /\ b = b' \/
    x >  0  /\ indexr (pred x) ({ 0 |-> T ~ d }ᴳ Γ) = Some ((bd, b', { 0 |-> T ~ d }ᵀ U, { 0 |-> d }ᵈ du))).
Proof.   intros. induction  Γ; intros.
  + simpl  in H. destruct (x =? 0) eqn: Heqn.
    -  inversion H. subst. left.  intuition.  apply Nat.eqb_eq in Heqn. auto.
    -  inversion H.
  + remember (length (Γ ++ [(bd, b, T, d)])) as L.
     destruct (Nat.eqb x L) eqn: Heqn.
    - assert (x = L). eapply Nat.eqb_eq. eauto.
      eapply indexr_hit in H.
      right. split. rewrite app_length in HeqL. simpl in HeqL. lia.
       assert ((pred x) = (‖ ({ 0 |-> T ~  d }ᴳ Γ) ‖)).
       rewrite subst1_env_length. rewrite app_length in HeqL. simpl in HeqL.  lia.
       simpl. eapply Nat.eqb_eq in H1.  subst.
       destruct (pred (length (Γ ++ [(bd, b, T, d)])) =? length ({0 |-> T ~ d }ᴳ Γ)); auto.
       inversion H1.
       subst. eauto.
    - assert (x <> L). eapply Nat.eqb_neq. eauto.
       replace ((a :: Γ) ++ [(bd, b, T, d)]) with  (a :: (Γ ++ [(bd, b, T, d)])) in H.
       rewrite indexr_skip in H. intuition.
       right. split. eauto.
       simpl.
       assert ((pred x) <> ( ‖({ 0 |-> T ~  d }ᴳ Γ)‖)).
       rewrite app_length in HeqL. simpl in HeqL. rewrite subst1_env_length.
       unfold not. intros. subst L.
       unfold not in H0. eapply H0. rewrite <-H2. lia.
       eapply Nat.eqb_neq in H2. rewrite H2.
       eauto. subst. eauto.  intuition.
Qed.

Lemma subst1_open_ty_comm : forall {l Tc dc T3 d3 T k}, closed_ty 0 0 l Tc -> closed_qual 0 0 l dc ->
        ({0 |-> Tc ~ dc }ᵀ ([[k ~> T3 ~ d3 ]]ᵀ T) = ([[k ~> ({0 |-> Tc ~ dc }ᵀ T3) ~ ({0  |-> dc}ᵈ d3)]]ᵀ ({0 |-> Tc ~ dc }ᵀ T))).
Proof.  intros. generalize dependent k. induction T; try destruct v; intuition; simpl.
  + bdestruct (i =? 0); simpl; intuition. erewrite closed_ty_open_id; eauto. lia.
  + bdestruct (k =? i); simpl; auto.
  + f_equal. 1,2:erewrite subst1_open_qual_comm; eauto; erewrite subst1_qual_empty; eauto.  erewrite IHT1; eauto. erewrite IHT2; auto.
  + f_equal. 1,2: erewrite subst1_open_qual_comm; eauto; erewrite subst1_qual_empty; eauto.  erewrite IHT1; eauto. erewrite IHT2; auto.
  + f_equal. erewrite subst1_open_qual_comm; eauto. eapply IHT; eauto.
Qed.

Lemma subst_qual_subqual_monotone : forall {d1 d2}, d1 ⊑↑ d2 -> forall {df}, ({0 |-> df }ᵈ d1) ⊑↑ ({0 |-> df }ᵈ d2).
Proof.
  intros. qual_destruct d1; qual_destruct d2; qual_destruct df; unfold_q.
  ndestruct (fvs0 0); simpl;
  ndestruct (fvs 0); simpl; Qcrush.
Qed.

Lemma subst1_just_fv : forall {fr x dy},
    ${fr}x = {0 |-> dy }ᵈ ${fr}(S x).
  intros. apply Q_lift_eq. Qcrush.
Qed.

Lemma closed_qual_subst1' : forall {p : Type} `{substitutable_env p} (E : env p) {X l Tf df φ b},
    closed_ty 0 0 l Tf ->
    closed_Qual 0 0 l df ↑ ->
    closed_Qual b (‖ E ++ [X] ‖) l φ ↑ ->
    closed_Qual b (‖ {0 |-> Tf ~ df }ᴳ E ‖) l ({0 |-> df }ᵈ φ) ↑.
  intros. eapply closed_qual_subst1; eauto. rewrite subst1_env_length.
  rewrite app_length in *. simpl in *. rewrite <- plus_n_Sm in *. rewrite <- plus_n_O in *. auto.
Qed.

Lemma closed_ty_subst1' : forall {p : Type} `{substitutable_env p} (E : env p) {X l Tf df T b},
    closed_ty 0 0 l Tf ->
    closed_Qual 0 0 l df ↑ ->
    closed_ty b (‖ E ++ [X] ‖) l T ->
    closed_ty b (‖ {0 |-> Tf ~ df }ᴳ E ‖) l ({0 |-> Tf ~ df }ᵀ T).
  intros. repeat eapply closed_ty_subst1; eauto. rewrite subst1_env_length.
  rewrite app_length in *. simpl in *. replace (‖E‖ + 1) with (S (‖E‖)) in H0.
  eapply closed_ty_monotone; eauto. lia. lia.
Qed.

Lemma closed_tm_subst1' : forall {p : Type} `{substitutable_env p} (E : env p) {X l Tf df tx t b},
    closed_tm 0 0 l tx ->
    closed_tm b (‖ E ++ [X] ‖) l t ->
    closed_tm b (‖ {0 |-> Tf ~ df }ᴳ E ‖) l ({0 |-> tx }ᵗ t).
  intros. repeat eapply closed_tm_subst1; eauto. rewrite subst1_env_length.
  rewrite app_length in *. simpl in *. rewrite <- plus_n_Sm in *. rewrite <- plus_n_O in *. auto.
Qed.

Lemma subst1_qual_0 : forall {q' q}, q' ⊑↑ q -> forall {df}, $0 ∈ᵥ df -> q' ⊑↑ { 0 |-> q }ᵈ df.
  intros. qual_destruct df. qual_destruct q. qual_destruct q'. unfold_q. unfold N_lift in H0. rewrite H0. simpl. Qcrush.
Qed.

Lemma subst1_just_fv0 : forall {q}, {0 |-> q }ᵈ $!0 = q.
  intros. apply Q_lift_eq. Qcrush.
Qed.

Lemma qenv_saturated_q''_0 : forall {p : Type} `{qenv p} (E : env p) (a : p) q,
  N_lift (qenv_qn q) 0 ->
  qenv_saturated_q'' (E ++ [a]) q ->
  (qenv_q a) ⊑↑ q.
intros. unfold qenv_saturated_q'' in *. induction E; simpl in *.
  - unfold N_lift in H0. rewrite H0 in H1. rewrite <- H1. Qcrush.
  - ndestruct (qenv_qn q (‖ E ++ [a] ‖)); auto.
    apply IHE. pose proof (q_trans_one_subq' (E ++ [a]) q). assert ((q_trans_one (E ++ [a]) q ⊔ qenv_q a0) ⊑↑ q). rewrite H1. auto. apply Q_lift_eq. Qcrush.
Qed.

Lemma subst1_qand_saturated : forall {df d1 bd sx Tx dx dx'} {φ} {Γ : tenv} {Σ : senv},
    dx' ⊓ φ ⊑↑ dx ->
    closed_Qual 0 0 (‖Σ‖) dx'↑ ->
    df ⊑↑ φ -> d1 ⊑↑ φ ->
    qenv_saturated_q'' (Γ ++ [(bd, sx, Tx, dx)]) d1 ->
    qenv_saturated_q'' (Γ ++ [(bd, sx, Tx, dx)]) df ->
    {0 |-> dx' }ᵈ df ⊓ {0 |-> dx' }ᵈ d1 = {0 |-> dx' }ᵈ (df ⊓ d1).
  intros. qual_destruct df. qual_destruct d1.
  unfold_q. ndestruct (fvs 0); ndestruct (fvs0 0); clift.
  - apply Q_lift_eq; Qcrush.
  - (* 0 ∈ df, 0 ∉ d1 *)
    apply qenv_saturated_q''_0 in H4; auto. apply Q_lift_eq; Qcrush.
  - (* 0 ∉ df, 0 ∈ d1, analogous to the previous case *)
    apply qenv_saturated_q''_0 in H3; auto. apply Q_lift_eq; Qcrush.
Qed.

Lemma subst1_qand_saturated' : forall {df d1 bd sx Tx dx dx'} {φ} {Γ : tenv} {Σ : senv},
    dx' ⊓ φ ⊑↑ dx ->
    ♦∉ dx' ->
    closed_Qual 0 0 (‖Σ‖) dx'↑ ->
    df ⊑↑ φ ⊔ {♦} -> d1 ⊑↑ φ ⊔ {♦} ->
    qenv_saturated_q'' (Γ ++ [(bd, sx, Tx, dx)]) d1 ->
    qenv_saturated_q'' (Γ ++ [(bd, sx, Tx, dx)]) df ->
    {0 |-> dx' }ᵈ df ⊓ {0 |-> dx' }ᵈ d1 = {0 |-> dx' }ᵈ (df ⊓ d1).
  intros. qual_destruct df. qual_destruct d1.
  unfold_q. ndestruct (fvs 0); ndestruct (fvs0 0); clift.
  - apply Q_lift_eq; Qcrush.
  - (* 0 ∈ df, 0 ∉ d1 *)
    apply qenv_saturated_q''_0 in H5; auto. apply Q_lift_eq; Qcrush. destruct (H16 x); intuition. destruct (H21 x); intuition.
  - (* 0 ∉ df, 0 ∈ d1, analogous to the previous case *)
    apply qenv_saturated_q''_0 in H4; auto. apply Q_lift_eq; Qcrush. destruct (H14 x); intuition. destruct (H20 x); intuition.
Qed.

Lemma subst1_mem_loc : forall {dx df l}, l ∈ₗ {0 |-> dx }ᵈ df ->  (l ∈ₗ dx /\ $0 ∈ᵥ df) \/ l ∈ₗ df.
  intros. qual_destruct df. qual_destruct dx. unfold_q.
#[local] Hint Resolve n_reflect_true : bdestruct.
  bdestruct (fvs 0); Qcrush.
#[local] Remove Hints n_reflect_true : bdestruct.
Qed.


Lemma qglb_disjoint_freshv : forall {dx' l x},
  closed_Qual 0 0 l dx'↑ -> dx' ⊓ $!x = ∅.
  intros. apply Q_lift_eq. Qcrush. eauto.
Qed.


Lemma subQual_eq : forall {p q}, p ⊑↑ q -> q ⊑↑ p -> p = q.
Proof. intros. apply Q_lift_eq. Qcrush. Qed.

Lemma or_false_elim : forall A, (A \/ False) = A.
intros. apply PropExtensionality.propositional_extensionality. intuition.
Qed.

Lemma un_subst1_qual_open : forall {v dx q l}, closed_Qual 0 0 l dx↑ -> {0 |-> dx }ᵈ ([[v ~> ∅ ]]ᵈ q) = {0 |-> dx }ᵈ q -> [[v ~> ∅ ]]ᵈ q = q.
intros. qual_destruct q. qual_destruct dx. apply Q_lift_eq' in H0.
unfold_q. inversion H0. clear H0.
ndestruct (bvs v); eauto.
apply Q_lift_eq. Qcrush.
ndestruct (fvs 0); Qcrush; ndestruct (n_or fvs n_empty 0); Qcrush.
  - assert (notin: N_lift bvs0 x = False). { apply PropExtensionality.propositional_extensionality; intuition eauto. }
    eapply FunctionalExtensionality.equal_f with (x:=x) in H4; repeat rewrite or_false_elim in H4.
    rewrite notin in *. rewrite H4. eauto.
  - assert (notin: N_lift bvs0 x = False). { apply PropExtensionality.propositional_extensionality; intuition eauto. }
    eapply FunctionalExtensionality.equal_f with (x:=x) in H4; repeat rewrite or_false_elim in H4.
    rewrite H4. eauto.
Qed.

Lemma qor_empty_left : forall {d}, (q_empty ⊔ d) = d.
intros. apply Q_lift_eq. rewrite Q_lift_or. Qcrush.
Qed.

Lemma q_trans_one_subst1_tenv_comm : forall (Γ : tenv) (Σ : senv) bd bx Tx d dx',
  wf_tenv (Γ ++ [(bd,bx,Tx,dx')]) Σ ->
  wf_senv Σ ->
  closed_Qual 0 0 (‖ Σ ‖) dx' ↑ ->
  ({0 |-> dx' }ᵈ (q_trans_one (Γ ++ [(bd, bx, Tx, dx')]) d)) =
  (q_trans_one ({0 |-> Tx ~ dx' }ᴳ Γ) ({0 |-> dx' }ᵈ d)).
intros. generalize dependent d. induction Γ; intros. simpl. auto. ndestruct (qfvs d 0); auto. rewrite subst1_qor_dist. erewrite @subst1_qual_id with (q:=dx'); eauto. apply Q_lift_eq. rewrite Q_lift_or. rewrite Q_lift_subst_qual. Qcrush.
simpl. rewrite app_length, subst1_env_length. simpl. rewrite Nat.add_1_r. ndestruct (qfvs d (S (‖ Γ ‖))); simpl.
- assert (N_lift (qfvs ({0 |-> dx' }ᵈ d)) (‖ Γ ‖)). { unfold subst_qual. ndestruct (qfvs d 0); Qcrush. } clift. rewrite <- IHΓ. rewrite subst1_qor_dist. destruct a as [ [ [ bb b ] T ] q ]. simpl. auto. eauto.
- assert (~N_lift (qfvs ({0 |-> dx' }ᵈ d)) (‖ Γ ‖)). { unfold subst_qual. ndestruct (qfvs d 0); Qcrush. eauto. } clift. rewrite <- IHΓ; eauto.
Qed.

Lemma q_trans''_subst1_tenv_comm : forall (Γ : tenv) (Σ : senv) bd bx Tx d dx' fuel,
  wf_tenv (Γ ++ [(bd, bx,Tx,dx')]) Σ ->
  wf_senv Σ ->
  closed_Qual 0 0 (‖ Σ ‖) dx' ↑ ->
({0 |-> dx' }ᵈ (q_trans'' (Γ ++ [(bd, bx, Tx, dx')]) d fuel)) =
(q_trans'' ({0 |-> Tx ~ dx' }ᴳ Γ) ({0 |-> dx' }ᵈ d) fuel).
intros. generalize dependent d. induction fuel; intros; simpl; auto. rewrite IHfuel. erewrite q_trans_one_subst1_tenv_comm; eauto.
Qed.

Lemma q_trans_one_subst1_tenv_comm' : forall (Γ : tenv) (Σ : senv) bd bx Tx d dx' df0,
  wf_tenv (Γ ++ [(bd,bx,Tx,dx')]) Σ ->
  wf_senv Σ ->
  closed_Qual 0 0 (‖ Σ ‖) dx' ↑ ->
  ({0 |-> dx' }ᵈ (q_trans_one (Γ ++ [(bd, bx, Tx, df0 ⊓ dx')]) d)) =
  (q_trans_one ({0 |-> Tx ~ dx' }ᴳ Γ) ({0 |-> dx' }ᵈ d)).
intros. generalize dependent d. induction Γ; intros. simpl. auto. ndestruct (qfvs d 0); auto. rewrite subst1_qor_dist. erewrite @subst1_qual_id with (q:=(df0 ⊓ dx')); eauto. apply Q_lift_eq. rewrite Q_lift_or. rewrite Q_lift_subst_qual. Qcrush. Qcrush.
simpl. rewrite app_length, subst1_env_length. simpl. rewrite Nat.add_1_r. ndestruct (qfvs d (S (‖ Γ ‖))); simpl.
- assert (N_lift (qfvs ({0 |-> dx' }ᵈ d)) (‖ Γ ‖)). { unfold subst_qual. ndestruct (qfvs d 0); Qcrush. } clift. rewrite <- IHΓ. rewrite subst1_qor_dist. destruct a as [ [ [ bb b ] T ] q ]. simpl. auto. eauto.
- assert (~N_lift (qfvs ({0 |-> dx' }ᵈ d)) (‖ Γ ‖)). { unfold subst_qual. ndestruct (qfvs d 0); Qcrush. eauto. } clift. rewrite <- IHΓ; eauto.
Qed.

Lemma q_trans''_subst1_tenv_comm' : forall (Γ : tenv) (Σ : senv) bd bx Tx d dx' df0 fuel,
  wf_tenv (Γ ++ [(bd,bx,Tx,dx')]) Σ ->
  wf_senv Σ ->
  closed_Qual 0 0 (‖ Σ ‖) dx' ↑ ->
  ({0 |-> dx' }ᵈ (q_trans'' (Γ ++ [(bd, bx, Tx, df0 ⊓ dx')]) d fuel)) =
  (q_trans'' ({0 |-> Tx ~ dx' }ᴳ Γ) ({0 |-> dx' }ᵈ d) fuel).
intros. generalize dependent d. induction fuel; intros; simpl; auto. rewrite IHfuel. erewrite q_trans_one_subst1_tenv_comm'; eauto.
Qed.

Lemma wf_tenv_weaken : forall (Γ1 Γ2 : tenv) Σ bd bx Tx dx Tx' dx',
   wf_tenv (Γ1 ++ (bd, bx, Tx, dx) :: Γ2) Σ ->
   closed_ty 0 (‖ Γ2 ‖) (‖ Σ ‖) Tx' ->
   closed_Qual 0 (‖ Γ2 ‖) (‖ Σ ‖) dx' ↑ ->
   wf_tenv (Γ1 ++ (bd, bx, Tx', dx') :: Γ2) Σ.
intros. induction Γ1; simpl in *. constructor; auto. eapply wf_tenv_shrink; eauto.
destruct a as [ [ [ bd0 bx0 ] Tx0 ] dx0]. pose proof (wf_tenv_prop H (‖ Γ1 ++ (bd, bx, Tx, dx) :: Γ2 ‖) bd0 bx0 Tx0 dx0) as Hprop. rewrite indexr_head in Hprop. intuition. constructor; eauto. all: simpl in *; rewrite app_length in *; auto.
Qed.

Lemma wf_tenv_weaken' : forall (Γ1 Γ2 : tenv) Σ bd bx Tx dx dx',
   wf_tenv (Γ1 ++ (bd, bx, Tx, dx) :: Γ2) Σ ->
   closed_Qual 0 (‖ Γ2 ‖) (‖ Σ ‖) dx' ↑ ->
   wf_tenv (Γ1 ++ (bd, bx, Tx, dx') :: Γ2) Σ.
intros. eapply wf_tenv_weaken; eauto. pose proof (wf_tenv_prop H (‖ Γ2 ‖) bd bx Tx dx) as Hprop. rewrite indexr_insert in Hprop. intuition.
Qed.

Lemma q_trans''_subst1_tenv_subq'' : forall Γ0 Σ bd Tx dx' df0 df bx,
  wf_senv Σ ->
  wf_tenv (Γ0 ++ [(bd, bx, Tx, dx')]) Σ ->
  closed_Qual 0 0 (‖ Σ ‖) dx' ↑ ->
  (q_trans'' ({0 |-> Tx ~ dx' }ᴳ Γ0) ({0 |-> dx' }ᵈ df) (‖ Γ0 ‖)) ⊑↑
  ({0 |-> dx' }ᵈ (q_trans'' (Γ0 ++ [(bd, bx, Tx, df0 ⋒ dx')]) df (S (‖ Γ0 ‖)))).
intros. erewrite <- q_trans''_subst1_tenv_comm' with (df0:=df0); eauto. apply subst_qual_subqual_monotone. eapply Subq_trans. apply q_trans''_incr_subq. eapply q_trans_tenv_narrowing_subq; eauto.
Qed.


Lemma closed_Qual_q_trans_one_monotone : forall {p : Type} `{qenv p} (E : env p) q b f l,
  closed_Qual b f l q ↑ ->
  closed_qenv b f l E ->
  closed_Qual b f l (q_trans_one E q) ↑.
intros. induction E; simpl; auto. apply closed_qenv_shrink in H1 as H1'. intuition. ndestruct (qenv_qn q (‖ E ‖)); auto. apply closed_Qual_qor; auto. specialize (H1 (‖ E ‖) a). rewrite indexr_head in H1. intuition.
Qed.

Lemma closed_Qual_q_trans''_monotone : forall {p : Type} `{qenv p} (E : env p) q b f l fuel,
  closed_Qual b f l q ↑ ->
  closed_qenv b f l E ->
  closed_Qual b f l (q_trans'' E q fuel) ↑.
intros. generalize dependent q. induction fuel; intros; simpl; auto. apply IHfuel. apply closed_Qual_q_trans_one_monotone; auto.
Qed.



Lemma wf_tenv_closed_subst : forall Γ Σ a bd b T q,
  wf_tenv (Γ ++ [a]) Σ ->
  closed_ty 0 0 (‖ Σ ‖) T ->
  closed_Qual 0 0 (‖ Σ ‖) q↑ ->
  wf_tenv (Γ ++ [(bd, b, T, q)]) Σ.
intros. induction Γ; simpl in *.
- constructor; auto. constructor. eapply wf_tenv_wf_senv; eauto.
- inversion H. subst. constructor; auto. all: rewrite app_length in *; simpl in *; auto.
Qed.

Lemma wf_tenv_subst : forall Γ Σ bd b T q,
  wf_tenv (Γ ++ [(bd, b, T, q)]) Σ ->
  wf_tenv ({0 |-> T ~ q }ᴳ Γ) Σ.
intros. remember (Γ ++ [(bd, b, T, q)]) as Γ0. generalize dependent Γ. induction H; intros.
- destruct Γ; simpl in *; discriminate.
- destruct Γ0. simpl. apply wf_tenv_nil; auto. eapply wf_tenv_wf_senv; eauto.
  simpl in HeqΓ0. inversion HeqΓ0. subst. simpl. pose proof (@wf_tenv_prop _ Σ H). constructor; auto.
  eapply closed_ty_subst1; eauto. eapply closed_ty_monotone; eauto. rewrite app_length,subst1_env_length in *. simpl. lia.
  1,2: specialize (H2 (‖ ([]:tenv) ‖) bd b T q); rewrite indexr_insert in H2; intuition.
  eapply closed_qual_subst1; eauto. eapply closed_Qual_monotone; eauto. rewrite app_length,subst1_env_length in *. simpl. lia.
  specialize (H2 (‖ ([]:tenv) ‖) bd b T q). rewrite indexr_insert in H2. intuition.
Qed.

Lemma wf_tenv_subst' : forall Γ Σ bd b T q df,
  wf_tenv (Γ ++ [(bd, b, T, df ⋒ q)]) Σ ->
  closed_Qual 0 0 (‖ Σ ‖) q↑ ->
  wf_tenv ({0 |-> T ~ q }ᴳ Γ) Σ.
intros. remember (Γ ++ [(bd, b, T, df ⋒ q)]) as Γ0. generalize dependent Γ. induction H; intros.
- destruct Γ; simpl in *; discriminate.
- destruct Γ0. simpl. apply wf_tenv_nil; auto. eapply wf_tenv_wf_senv; eauto.
  simpl in HeqΓ0. inversion HeqΓ0. subst. simpl. pose proof (@wf_tenv_prop _ Σ H) as Hprop. constructor; auto.
  eapply closed_ty_subst1; eauto. eapply closed_ty_monotone; eauto. rewrite app_length,subst1_env_length in *. simpl. lia.
  1,2: specialize (Hprop (‖ ([]:tenv) ‖) bd b T (df ⋒ q)); rewrite indexr_insert in Hprop; intuition.
  eapply closed_qual_subst1; eauto. eapply closed_Qual_monotone; eauto. rewrite app_length,subst1_env_length in *. simpl. lia.
Qed.

Lemma fuel_max_qenv_saturated_q'': forall {p : Type} `{qenv p} (E : env p) (q : qual) (fuel : nat),
  qenv_saturated_q'' E (q_trans'' E q (‖ E ‖)).
intros. unfold qenv_saturated_q''. rewrite <- q_trans''_fuel_max with (fuel:=(S (‖ E ‖))) at 2; auto.
simpl. rewrite q_trans''_one_commute. auto.
Qed.

Lemma qenv_qn_qenv_saturated_q'': forall {p : Type} `{qenv p} (E : env p) (a b : qual),
  qenv_qn a = qenv_qn b ->
  a ⊑↑ b ->
  qenv_saturated_q'' E a ->
  qenv_saturated_q'' E b.
intros. unfold qenv_saturated_q'' in *. induction E; simpl in *; auto. rewrite <- H0. ndestruct (qenv_qn a (‖ E ‖)); auto.
pose proof (q_trans_one_subq' E a).
assert (q_trans_one E a ⊔ qenv_q a0 ⊑↑ a). { rewrite H2. auto. }
assert (qenv_q a0 ⊑↑ b). Qcrush.
rewrite IHE; auto. all: apply Q_lift_eq; Qcrush.
Qed.


(* ad-hoc lemma for substitution *)
Lemma q_trans_one_closed_qenv_qfvs: forall {p : Type} `{qenv p} (E : env p) b l d,
  closed_qenv b 0 l E ->
  qfvs (q_trans_one E d) = qfvs d.
intros. induction E; simpl; auto. ndestruct (qenv_qn d (‖ E ‖)).
- rewrite qn_or_dist. rewrite IHE. specialize (H0 (‖ E ‖) a). rewrite indexr_head in H0. intuition. apply N_lift_eq. Qcrush. exfalso; eauto. eapply closed_qenv_shrink; eauto.
- apply IHE. eapply closed_qenv_shrink; eauto.
Qed.

(* ad-hoc lemma for substitution *)
Lemma q_trans''_closed_qenv_qfvs: forall {p : Type} `{qenv p} (E : env p) b l fuel d,
  closed_qenv b 0 l E ->
  qfvs (q_trans'' E d fuel) = qfvs d.
intros. induction fuel; simpl; auto. rewrite <- IHfuel. rewrite <- q_trans''_one_commute. erewrite q_trans_one_closed_qenv_qfvs; eauto.
Qed.

Lemma q_trans''_tenv_saturated : forall Γ d,
qenv_saturated_q'' Γ (q_trans_tenv Γ d).
intros. apply fuel_max_qenv_saturated_q''. apply 1.
Qed.

Lemma q_trans_one_closed_id : forall {p : Type} `{qenv p} (E : env p) d,
  closed_Nats 0 (qenv_Qn d↑) ->
  q_trans_one E d = d.
intros. induction E; simpl; auto. ndestruct (qenv_qn d (‖ E ‖)). rewrite @Q_lift_qn with (Qn:=qenv_Qn) in H1. exfalso. eauto. apply qenv_qn_prop. apply IHE.
Qed.

Lemma q_trans''_closed_id : forall {p : Type} `{qenv p} (E : env p) fuel d,
  closed_Nats 0 (qenv_Qn d↑) ->
  q_trans'' E d fuel = d.
intros. induction fuel; simpl; auto. rewrite q_trans_one_closed_id; auto.
Qed.



Lemma open_qual_mono : forall {d1 d1' d2 k}, d1 ⊑↑ d1' -> ([[ k ~> d1 ]]ᵈ d2) ⊑↑ ([[ k ~> d1' ]]ᵈ d2).
  intros. unfold_q. qual_destruct d2; qual_destruct d1'; qual_destruct d1. simpl. ndestruct (bvs k); Qcrush.
Qed.

Lemma open_qual_mono2 : forall {d1 d2 d2' k}, d2 ⊑↑ d2' -> ([[ k ~> d1 ]]ᵈ d2) ⊑↑ ([[ k ~> d1 ]]ᵈ d2').
  intros. unfold_q. qual_destruct d2; qual_destruct d2'; qual_destruct d1. simpl.
  ndestruct (bvs0 k); ndestruct (bvs k); Qcrush.
  bdestruct (x =? k); Qcrush. exfalso; eauto.
Qed.

Lemma openq_mono : forall {d1 d1' d2 d2' d3 d3' f l},
    closed_Qual 0 f l d1'↑ -> closed_Qual 0 f l d2'↑ ->
    d1 ⊑↑ d1' -> d2 ⊑↑ d2' -> d3 ⊑↑ d3' -> (d3 <~ᵈ d1; d2) ⊑↑ (d3' <~ᵈ d1'; d2').
  intros. unfold openq.
  specialize (@open_qual_mono d1 d1' d3' 0 H1) as S1.
  specialize (@open_qual_mono2 d1 d3 d3' 0 H3) as S2.
  specialize (Subq_trans S2 S1) as S3. clear S1. clear S2.
  specialize (@open_qual_mono2 d2' _ _ 1 S3) as S4.
  eapply Subq_trans. 2: eauto. eapply open_qual_mono; eauto.
Qed.

(* Some distributive laws about openq and qqplus, required in the type safety proof for function application t_app. *)
Lemma open_qual_duplicate_eq : forall {k d1 d2 d}, ♦∈ d1 ->
  ([[ k ~> d1 ]]ᵈ d2 ⋓ d) = ([[ k ~> d1 ⋓ d ]]ᵈ d2 ⋓ d).
  intros. apply Q_lift_eq. qual_destruct d1. qual_destruct d2. unfold_q. destruct fr; auto.
ndestruct (bvs0 k); destruct (fr0); Qcrush.
Qed.

(* when the argument steps *)
Lemma openq_duplicate_eq_r : forall {df d1 d2 d}, ♦∈ d1 ->
  (d2 <~ᵈ df; d1 ⋓ d) = (d2 <~ᵈ df; (d1 ⋓ d) ⋓ d).
  intros. unfold openq. rewrite open_qual_duplicate_eq; auto.
Qed.

(* when the function steps *)
Lemma openq_duplicate_eq_l : forall {f l df d1 d2 d},
  ♦∈ df -> closed_qual 0 f l df -> closed_qual 0 f l d1 -> closed_qual 0 f l d ->
  (d2 <~ᵈ df; d1 ⋓ d) = ((d2 <~ᵈ df ⋓ d; d1) ⋓ d).
  intros. unfold openq. erewrite open_qual_commute''; eauto.
  erewrite @open_qual_commute'' with (i:=1); eauto.
  rewrite open_qual_duplicate_eq; auto.
  apply closed_qual_qqplus; auto.
Qed.


Lemma openq_closed : forall {a b c f l},
    closed_qual 2 f l c -> closed_qual 0 f l a -> closed_qual 0 f l b -> closed_qual 0 f l (openq a b c).
  intros. unfold openq. erewrite open_qual_commute''; eauto using closed_qual_open'.
Qed.

Lemma openQ_closed : forall {a b c f l},
    closed_Qual 2 f l c↑ -> closed_Qual 0 f l a↑ -> closed_Qual 0 f l b↑ -> closed_Qual 0 f l (openq a b c)↑.
  intros. apply Q_lift_closed'. unfold openq. erewrite open_qual_commute''; eauto using closed_qual_open'.
Qed.

Lemma openq_subqual_0 : forall {df d2 d1 l}, closed_Qual 0 0 l df↑ -> closed_Qual 0 0 l d1↑ -> N_lift (qbvs d2) 0 -> df ⊑↑ d2 <~ᵈ df; d1.
  intros.
qual_destruct d2. qual_destruct d1. qual_destruct df. unfold openq. unfold_q. clift. simpl.
ndestruct (n_or (n_diff bvs (n_one 0)) bvs1 1); Qcrush; exfalso; eauto.
Qed.

Lemma openq_subqual_0_false : forall {df d2 d1}, ~N_lift (qbvs d2) 0 -> forall {df'}, d2 <~ᵈ df; d1 = d2 <~ᵈ df'; d1.
  intros. unfold openq. unfold_q. clift. apply Q_lift_eq. Qcrush.
Qed.

Lemma openq_subqual_1 : forall {df d2 d1 l}, closed_Qual 0 0 l df↑ -> closed_Qual 0 0 l d1↑ -> N_lift (qbvs d2) 1 -> d1 ⊑↑ d2 <~ᵈ df; d1.
  intros.
  qual_destruct d2. unfold openq. unfold_q.
ndestruct (bvs 0); simpl; clift. ndestruct (n_or (n_diff bvs (n_one 0)) (snd (fst df)) 1).
all: Qcrush.
Qed.

Lemma openq_subqual_1_false : forall {df d2 d1 l}, closed_Qual 0 0 l df↑ -> ~N_lift (qbvs d2) 1 -> forall {d1'}, d2 <~ᵈ df; d1 = d2 <~ᵈ df; d1'.
intros. qual_destruct d2. qual_destruct df. unfold openq. unfold_q.
ndestruct (bvs 0); simpl; clift; auto.
ndestruct (n_or (n_diff bvs (n_one 0)) bvs0 1); auto.
exfalso. assert (~N_lift (n_diff bvs (n_one 0)) 1). Qcrush. assert (~N_lift bvs0 1). Qcrush. eauto. Qcrush.
Qed.


Lemma Qqplus_upper_l : forall {d1 d2}, d1 ⊑↑ (d1 ⋓ d2).
  intros. qual_destruct d1. unfold_q. destruct fr; auto. Qcrush.
Qed.

Lemma qqplus_upper_l : forall {d1 d2}, d1 ⊑ (d1 ⋓ d2).
  intros. apply Q_lift_subq. apply Qqplus_upper_l.
Qed.

Lemma qqplus_qbot_right_neutral : forall {d}, (d ⋓ ∅) = d.
intros. qual_destruct d. unfold_q. destruct fr; auto. apply Q_lift_eq. Qcrush.
Qed.
#[global] Hint Resolve qqplus_qbot_right_neutral : core.

Lemma qqplus_qbot_left_cancel : forall {d}, (∅ ⋓ d) = ∅.
intros. unfold_q. auto.
Qed.
#[global] Hint Resolve qqplus_qbot_left_cancel : core.

Lemma Subqual_qqplus : forall {d1 d2 d}, d1 ⊑↑ d2 -> d1 ⋓ d ⊑↑ d2 ⋓ d.
  intros. qual_destruct d1. qual_destruct d2. qual_destruct d. unfold_q. destruct fr; destruct fr0; Qcrush.
Qed.

Lemma subqual_qqplus : forall {d1 d2 d}, d1 ⊑ d2 -> d1 ⋓ d ⊑ d2 ⋓ d.
  intros. apply Q_lift_subq. apply Q_lift_subq' in H. apply Subqual_qqplus; auto.
Qed.

Lemma Subqual_qqplus_l : forall {d1 d2 d}, d1 ⊑↑ d2 -> d ⋓ d1 ⊑↑ d ⋓ d2.
  intros. qual_destruct d. qual_destruct d1. qual_destruct d2. unfold_q. destruct fr; destruct fr0; Qcrush.
Qed.

Lemma subqual_qqplus_l : forall {d1 d2 d}, d1 ⊑ d2 -> d ⋓ d1 ⊑ d ⋓ d2.
  intros. apply Q_lift_subq. apply Q_lift_subq' in H. apply Subqual_qqplus_l; auto.
Qed.

Lemma Qqplus_bound : forall {q1 q2 q3}, q1 ⊑↑ q3 -> q2 ⊑↑ q3 -> q1 ⋓ q2 ⊑↑ q3.
  intros. qual_destruct q1. unfold_q. destruct fr; Qcrush.
Qed.

Lemma qqplus_bound : forall {q1 q2 q3}, q1 ⊑ q3 -> q2 ⊑ q3 -> q1 ⋓ q2 ⊑ q3.
  intros. apply Q_lift_subq. apply Q_lift_subq' in H,H0. apply Qqplus_bound; auto.
Qed.

Lemma not_fresh_qqplus : forall {d1 d'}, ♦∉ d1 -> (d1 ⋓ d') = d1.
  intros. qual_destruct d1. unfold_q. destruct fr; Qcrush.
Qed.
#[global] Hint Resolve not_fresh_qqplus : core.

Lemma closed_qand_locs_empty : forall {b f l} q,
  closed_Qual b f l q↑ ->
  forall l', l' >= l ->
  q ⊓ &! l' = ∅.
intros. apply Q_lift_eq. Qcrush. subst. eauto.
Qed.

Lemma set_union_fresh : forall {fr : bool} {fvs bvs lcs : nats},
    ((fr, fvs, bvs, lcs) ⊔ ({♦})) = (true, fvs, bvs, lcs).
Proof.
  intros. cbv. Qcrush. destruct fr; auto.
  destruct (fvs x); intuition. destruct (bvs x); intuition. destruct (lcs x); intuition.
Qed.

Lemma Subqual_non_fresh : forall {d1 d2}, (♦∈ d1 -> False) -> d1 ⊑↑ d2 ⊔ {♦} -> d1 ⊑↑ d2.
Proof.
  intros.
  qual_destruct d1. destruct fr. Qcrush.
  qual_destruct d2. rewrite set_union_fresh in H0. destruct fr; Qcrush.
Qed.


Lemma mem_subset_loc : forall {x q}, x ∈ₗ q <-> (&! x) ⊑↑ q.
Proof. split; intro. Qcrush. subst. auto. Qcrush. Qed.

Lemma openq_subqual_trans : forall {d1 d2 d3 φ φ' f l f' l'},
    closed_Qual 0 f l φ↑ ->
    closed_Qual 0 f' l' (φ' ⊔ {♦})↑ ->
    d2 <~ᵈ ∅; ∅ ⊑↑ (φ ⊔ {♦}) ->
    d1 ⊑↑ φ ->
    d3 ⊑↑ (φ ⊔ {♦}) ->
    φ ⊑↑ φ' ->
    d2 <~ᵈ d3; d1 ⊑↑ φ' ⊔ {♦}.
Proof.
  intros.
  assert (φ ⊑↑ φ' ⊔ {♦}). Qcrush.
  assert (φ ⊔ {♦} ⊑↑ φ' ⊔ {♦}). Qcrush.
  assert (d3 ⊑↑ φ' ⊔ {♦}).  Qcrush.
  assert (d2 <~ᵈ ∅; ∅ ⊑↑ φ' ⊔ {♦}). eapply Subq_trans; eauto.
  assert (d1 ⊑↑ φ' ⊔ {♦}). eapply Subq_trans; eauto.
  eapply openq_subqual; eauto.
Qed.

Lemma openq_subqual_trans' : forall {df d1 d2 d' φ φ' f l f' l'},
    closed_Qual 0 f l φ↑ -> closed_Qual 0 f' l' (φ' ⊔ {♦})↑ ->
    df ⊑↑ φ ⊔ {♦} ->
    d2 <~ᵈ ∅; ∅ ⊑↑ φ ⊔ {♦} ->
    d1 ⊑↑ φ -> d' ⊑↑ φ' -> φ ⊑↑ φ' ->
    d2 <~ᵈ (df ⋓ d'); d1 ⊑↑ φ' ⊔ {♦}.
Proof.
  intros.
  assert (φ ⊑↑ φ' ⊔ {♦}). Qcrush.
  assert (φ ⊔ {♦} ⊑↑ φ' ⊔ {♦}). Qcrush.
  assert (df ⊑↑ φ' ⊔ {♦}). eapply Subq_trans; eauto.
  assert (df ⋓ d' ⊑↑ φ' ⊔ {♦}). eapply Qqplus_bound; eauto. Qcrush.
  assert (d2 <~ᵈ ∅; ∅ ⊑↑ φ' ⊔ {♦}). eapply Subq_trans; eauto.
  assert (d1 ⊑↑ φ' ⊔ {♦}). eapply Subq_trans; eauto.
  eapply openq_subqual; eauto.
Qed.

Lemma openq_subqual_trans'2 : forall {df d1 d2 d' φ φ' f l f' l'},
    closed_Qual 0 f l φ↑ -> closed_Qual 0 f' l' (φ' ⊔ {♦})↑ ->
    df ⊑↑ φ ⊔ {♦} ->
    d2 <~ᵈ ∅; ∅ ⊑↑ φ ⊔ {♦} ->
    d1 ⊑↑ (φ ⊔ {♦}) -> d' ⊑↑ φ' -> φ ⊑↑ φ' ->
    d2 <~ᵈ (df ⋓ d'); d1 ⊑↑ φ' ⊔ {♦}.
Proof.
  intros.
  assert (φ ⊑↑ φ' ⊔ {♦}). Qcrush.
  assert (φ ⊔ {♦} ⊑↑ φ' ⊔ {♦}). Qcrush.
  assert (df ⊑↑ φ' ⊔ {♦}). eapply Subq_trans; eauto.
  assert (df ⋓ d' ⊑↑ φ' ⊔ {♦}). eapply Qqplus_bound; eauto. Qcrush.
  assert (d2 <~ᵈ ∅; ∅ ⊑↑ φ' ⊔ {♦}). eapply Subq_trans; eauto.
  assert (d1 ⊑↑ φ' ⊔ {♦}). eapply Subq_trans; eauto.
  eapply openq_subqual; eauto.
Qed.

Lemma openq_subqual_trans'' : forall {df d1 d2 d' φ φ' f l f' l'},
    closed_Qual 0 f l φ↑ -> closed_Qual 0 f' l' (φ' ⊔ {♦})↑ ->
    d2 <~ᵈ ∅; ∅ ⊑↑ φ ⊔ {♦} ->
    df ⊑↑ φ ⊔ {♦} -> d1 ⊑↑ φ ⊔ {♦} ->
    d' ⊑↑ φ' -> φ ⊑↑ φ' ->
    d2 <~ᵈ df; (d1 ⋓ d') ⊑↑ φ' ⊔ {♦}.
Proof.
  intros.
  assert (φ ⊑↑ φ' ⊔ {♦}). Qcrush.
  assert (φ ⊔ {♦} ⊑↑ φ' ⊔ {♦}). Qcrush.
  assert (df ⊑↑ φ' ⊔ {♦}). eapply Subq_trans; eauto.
  assert (d1 ⊑↑ φ' ⊔ {♦}). eapply Subq_trans; eauto.
  assert (d1 ⋓ d' ⊑↑ φ' ⊔ {♦}). eapply Qqplus_bound; eauto. Qcrush.
  assert (d2 <~ᵈ ∅; ∅ ⊑↑ φ' ⊔ {♦}). eapply Subq_trans; eauto.
  eapply openq_subqual; eauto.
Qed.

Lemma closed_Qual_qor_fresh : forall {f l q}, closed_Qual 0 f l q↑ -> closed_Qual 0 f l (q ⊔ {♦})↑.
Proof. intros. eapply closed_Qual_qor; eauto. Qed.



Lemma wf_senvs_monotone : forall {L c}, wf_senvs L c ->
  forall L', L' >= L -> wf_senvs L' c.
Proof.
  intros. unfold wf_senvs in *; intros. specialize (H x T q H1). intuition. eapply closed_ty_monotone; eauto. eapply closed_Qual_monotone; eauto.
Qed.

Lemma wf_senvc_monotone : forall {L c}, wf_senvc L c ->
  forall L', L' >= L -> wf_senvc L' c.
Proof.
  intros. unfold wf_senvc in *. intuition. eapply wf_senvs_monotone; eauto.
Qed.

Lemma wf_senv_after_ref :  forall {Σ}, wf_senv Σ ->
  forall T q, ♦∉ q /\ closed_ty 0 0 (‖ Σ ‖) T /\ closed_Qual 0 0 (‖ Σ ‖) q ↑ ->
  wf_senv ([(T, q)] :: Σ).
Proof.
  intros. destruct H0. destruct H1. unfold wf_senv in *. intros; simpl. bdestruct (l =? ‖Σ‖); subst.
  - rewrite indexr_head in H3; inversion H3; subst. unfold wf_senvc; simpl; split; auto. unfold wf_senvs; intros. destruct x; simpl in *. inversion H4; subst. split; auto. split. eapply closed_ty_monotone; eauto. eapply closed_Qual_monotone; eauto. inversion H4.
  - rewrite indexr_skip in H3; auto. specialize (H l c H3). eapply wf_senvc_monotone; eauto.
Qed.

Lemma wf_senv_after_refat : forall {Σ}, wf_senv Σ ->
  forall T q, ♦∉ q /\ closed_ty 0 0 (‖ Σ ‖) T /\ closed_Qual 0 0 (‖ Σ ‖) q ↑ ->
  forall x, x < ‖Σ‖ -> wf_senv (sinsert Σ x (T,q)).
Proof.
  intros. destruct H0. destruct H2. unfold wf_senv in *; intros. rewrite <- senv_length_coersion. rewrite sinsert_length. bdestruct (l=?x); subst.
  - specialize (indexr_some_exists Σ x H1); intros. destruct H5 as [c' H5]. specialize (H x c' H5). eapply (@sinsert_indexr _ _ _ (T,q)) in H5. assert (Some c = Some ((T, q) :: c')). rewrite <- H4. rewrite <- H5. auto. inversion H6; subst. clear H4 H5 H6.
    unfold wf_senvc in *. simpl; intuition. unfold wf_senvs in *; intros. bdestruct (x0 =? ‖c'‖); subst. rewrite indexr_head in H; inversion H; subst. intuition.
      rewrite indexr_skip in H; auto. eapply H5; eauto.
  - rewrite (@sinsert_indexr_miss _ Σ x l) in H4; auto. eapply H; eauto.
Qed.