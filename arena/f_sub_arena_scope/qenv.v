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

Import QualNotations.
Local Open Scope qualifiers.

(**********
*  qenv  *
**********)

Definition env := fun (p : Type) => list p.

Definition tenv := env (binding * bool * ty * qual). (* (binding, isFunctionSelfRef, Type, Qual) , Gamma typing *)
Definition senvs := env (ty * qual). (* s for slice, the first row for closure lookup, or a column (as in type they're same) *)
Definition senv := env (senvs). (* Sigma store typing *)


(* This function unions a column to one single qualifier, to check the 'actual' qualifier of qualifier &l
  The squished or unified qualifier can only be used for qualifiers, so we always check the type as TUnit
*)
Definition getquals (p : ty * qual) : qual :=
  match p with
  | (_ , q) => q
  end.

Notation "p .q" := (map getquals p) (at level 75).

Fixpoint qunify (lq : list qual) : (qual) :=
  match lq with
  | [] => ∅ (* place holder *)
  | q :: tl => qor q (qunify tl)
  end.

(* squish a 2D store into a 1D list, each cell's qualifier represents the total observation of an arena *)
Definition squish (Σ : senv) : senvs := map (fun x => (TUnit, qunify (x.q))) Σ.


(* environment with qualifiers *)
Class qenv {p : Type} : Type := {
  (* how to retrieve the qualifier from an environment element *)
  qenv_q : p -> qual;
  (* which component of the qualifier should be used to do transitive lookup *)
  qenv_qn : qual -> nats;
  qenv_Qn : Qual -> Nats;
  qenv_qn_prop : qnmap qenv_qn qenv_Qn;
}.

#[export] Instance tenv_qenv : @qenv (binding * bool * ty * qual) := {
  qenv_q := snd; qenv_qn := qfvs; qenv_Qn := qfvs;
  qenv_qn_prop := qnmap_qfvs;
}.
#[global] Hint Resolve tenv_qenv : core.

#[export] Instance senv_qenv : @qenv (ty * qual) := {
  qenv_q := snd; qenv_qn := qlocs; qenv_Qn := qlocs;
  qenv_qn_prop := qnmap_qlocs;
}.
#[global] Hint Resolve senv_qenv : core.


(* Store typing contains closed types and well-scoped, saturated qualifiers. *)

(* For the squished senv, we only require closed under current store, because the feature of qunify.
  s for squished, c for column
*)
Definition wf_senvs (L : nat) (c : senvs) : Prop :=
  forall x T q, indexr x c = Some (T, q) -> ♦∉ q /\ closed_ty 0 0 L T /\ closed_Qual 0 0 L q↑
.

Definition wf_senvc (L : nat) (c : senvs) : Prop := ‖ c ‖ > 0 /\ wf_senvs L c.

(* We need encode two things here,
  1. wf_senvs (‖Σ‖) c for all c, and the same Σ as current store
  2. the first row has telescope.
    We remove the general telescope requirement, only enforcing all cells are closed
*)
Definition wf_senv (Σ : senv) : Prop := forall l c,
  indexr l Σ = Some c -> wf_senvc (‖Σ‖) c
.

Inductive wf_tenv : tenv -> senv -> Prop :=
  | wf_tenv_nil : forall Σ, wf_senv Σ -> wf_tenv [] Σ
  | wf_tenv_cons : forall Γ Σ bd fr T q,
      wf_tenv Γ Σ ->
      closed_ty 0 (‖Γ‖) (‖Σ‖) T ->
      closed_Qual 0 (‖Γ‖) (‖Σ‖) q↑ ->
      wf_tenv ((bd, fr, T, q) :: Γ) Σ
.
#[global] Hint Constructors wf_tenv : core.


Lemma wf_senvc_non_empty : forall L s, wf_senvc L s -> ‖s‖ > 0.
Proof.
  induction s; intros. inversion H; auto. simpl; auto. lia.
Qed.

Lemma wf_senv_column_notempty : forall {Σ}, wf_senv Σ -> forall l c, indexr l Σ = Some c -> ‖c‖ > 0.
Proof.
  intros. unfold wf_senv in *. specialize (H l c H0). unfold wf_senvs in H. destruct H; auto.
Qed.

(***************************
 *  wf_qenv: "Telescope" (in Gamma typing context) *
 **************************)

Inductive wf_qenv {p : Type} `{qenv p} : (env p) -> Prop :=
  | wf_qenv_nil : wf_qenv []
  | wf_qenv_cons : forall E a,
      wf_qenv E ->
      closed_Nats (‖E‖) (qenv_Qn (qenv_q a) ↑) ->
      wf_qenv (a :: E).
#[global] Hint Constructors wf_qenv : core.

Lemma wf_qenv_prop' : forall {p : Type} `{qenv p} (E : env p), wf_qenv E <-> (forall x a, indexr x E = Some a -> (closed_Nats x (qenv_Qn (qenv_q a)↑))).
split.
- intros Hwf x a Hidx. pose proof qenv_qn_prop as Hqn. induction Hwf; intros. simpl in H. discriminate. bdestruct (x =? ‖E‖); subst.
  + simpl in Hidx. rewrite Nat.eqb_refl in Hidx. inversion Hidx. subst. intuition.
  + simpl in Hidx. apply Nat.eqb_neq in H1. rewrite H1 in Hidx. apply IHHwf. auto.
- intros. induction E. auto. constructor. apply IHE. intros. specialize (H0 x a0). erewrite <- indexr_skip in H1; eauto using indexr_var_some',Nat.lt_neq. eapply H0. apply indexr_head.
Qed.

Lemma wf_qenv_prop : forall {p : Type} `{qenv p} (E : env p), wf_qenv E -> (forall x a, indexr x E = Some a -> (closed_Nats x (qenv_Qn ((qenv_q a)↑)))).
intros p ? E. pose proof (wf_qenv_prop' E) as Hwf. inversion Hwf. auto.
Qed.

Lemma wf_qenv_prop'' : forall {p : Type} `{qenv p} (E : env p), wf_qenv E -> (forall x a, indexr x E = Some a -> (closed_Nats (‖ E ‖) (qenv_Qn ((qenv_q a)↑)))).
intros p ? E. pose proof (wf_qenv_prop' E) as Hwf. inversion Hwf. intros. eapply closed_Nats_mono with (n:=x); eauto. apply indexr_extend1 in H3; eauto. lia.
Qed.

Lemma wf_qenv_shrink : forall {p : Type} `{qenv p} {E : env p} {a}, wf_qenv (a::E) -> wf_qenv E.
intros. inversion H0. auto.
Qed.
#[global] Hint Resolve wf_qenv_shrink : core.

Lemma wf_qenv_shrink' : forall {p : Type} `{qenv p} {E E' : env p} , wf_qenv (E'++E) -> wf_qenv E.
intros. induction E'; simpl; auto. apply IHE'. simpl in H0. eapply wf_qenv_shrink; eauto.
Qed.
#[global] Hint Resolve wf_qenv_shrink' : core.

Lemma wf_tenv_wf_qenv : forall Γ Σ,
  wf_tenv Γ Σ ->
  wf_qenv Γ.
intros. induction H; auto. constructor; auto. Qcrush.
Qed.
#[global] Hint Resolve wf_tenv_wf_qenv : core.


(*****************
*  closed_qenv  *
*****************)

Definition closed_qenv {p : Type} `{qenv p} (b f l : nat) (E : env p) : Prop :=
  forall x a, indexr x E = Some a -> closed_Qual b f l (qenv_q a) ↑.

Lemma closed_qenv_shrink : forall {p : Type} `{qenv p} (E : env p) (a : p) (b f l : nat),
  closed_qenv b f l (a :: E) -> closed_qenv b f l E.
intros. unfold closed_qenv in *. intros. eapply H0. apply indexr_extend1. eauto.
Qed.

Lemma closed_qenv_monotone : forall {p : Type} `{qenv p} (E : env p) {b f l : nat},
  closed_qenv b f l E -> forall b' f' l',
  b <= b' -> f <= f' -> l <= l' ->
  closed_qenv b' f' l' E.
intros. unfold closed_qenv in *. intros. eapply closed_Qual_monotone; eauto.
Qed.

Lemma closed_qenv_extend : forall {p : Type} `{qenv p} (E : env p) (a : p) {b f l : nat},
  closed_qenv b f l E ->
  closed_Qual b f l (qenv_q a) ↑ ->
  closed_qenv b f l (a :: E).
intros. unfold closed_qenv in *. intros. simpl in *. bdestruct (x =? (‖ E ‖)).
- inversion H2. subst. auto.
- apply H0 in H2. auto.
Qed.

Lemma closed_qenv_empty : forall {p : Type} `{qenv p} (b f l : nat) (E : env p),
  closed_qenv b f l [].
unfold closed_qenv. intros. simpl in H0. discriminate.
Qed.
#[global] Hint Resolve closed_qenv_empty : core.

(********************
*  closed_qenv_qn  *
********************)

Definition closed_qenv_qn {p : Type} `{qenv p} (n : nat) (E : env p) : Prop :=
  forall x a, indexr x E = Some a -> closed_Nats n (qenv_Qn (qenv_q a) ↑).

Lemma closed_qenv_qn_shrink : forall {p : Type} `{qenv p} (E : env p) (a : p) (n : nat),
  closed_qenv_qn n (a :: E) -> closed_qenv_qn n E.
intros. unfold closed_qenv_qn in *. intros. eapply H0. apply indexr_extend1. eauto.
Qed.

Lemma closed_qenv_qn_extend : forall {p : Type} `{qenv p} (E : env p) (a : p) {n : nat},
  closed_qenv_qn n E ->
  closed_Nats n (qenv_Qn (qenv_q a) ↑) ->
  closed_qenv_qn n (a :: E).
intros. unfold closed_qenv_qn in *. intros. simpl in *. bdestruct (x =? (‖ E ‖)).
- inversion H2. subst. auto.
- apply H0 in H2. auto.
Qed.

Lemma closed_qenv_qn_monotone : forall {p : Type} `{qenv p} (E : env p) {n : nat},
  closed_qenv_qn n E -> forall n',
  n <= n' ->
  closed_qenv_qn n' E.
intros. unfold closed_qenv_qn in *. intros. eapply closed_Nats_mono; eauto.
Qed.
#[global] Hint Resolve closed_qenv_qn_monotone : core.

Lemma closed_qenv_qn_empty : forall {p : Type} `{qenv p} (E : env p) (n : nat) ,
  closed_qenv_qn n [].
unfold closed_qenv_qn. intros. simpl in H0. discriminate.
Qed.
#[global] Hint Resolve closed_qenv_qn_empty : core.

Lemma wf_tenv_closed_qenv_qn : forall Γ Σ,
  wf_tenv Γ Σ ->
  closed_qenv_qn (‖ Γ ‖) Γ.
intros. induction H; simpl; auto. apply closed_qenv_qn_empty. apply ([]:tenv).
apply closed_qenv_qn_extend; eauto. Qcrush.
Qed.
#[global] Hint Resolve wf_tenv_closed_qenv_qn : core.



Lemma closed_tenv_closed_qn: forall b f l (Γ : tenv), closed_qenv b f l Γ -> closed_qenv_qn f Γ.
intros. unfold closed_qenv, closed_qenv_qn in *. intros. specialize (H x a H0). Qcrush.
Qed.

Lemma closed_senvs_closed_qn: forall b f l (s : senvs), closed_qenv b f l s -> closed_qenv_qn l s.
intros. unfold closed_qenv, closed_qenv_qn in *. intros. specialize (H x a H0). Qcrush.
Qed.

(* ================================= 
  additional lemmas of sindexr and senv
*)

(* This lemma is adhoc for type transform in Coq *)
Lemma senv_length_coersion : forall s, (@length (list (prod ty qual)) s) = (@length senvs s).
Proof.
  induction s; simpl. auto. lia.
Qed.

Lemma squish_length : forall s,
  ‖ squish s ‖ = ‖s‖.
Proof.
  induction s; simpl; auto.
Qed.

Lemma qunify_map : forall f c,
  ∅ = f ∅ ->
  (forall q1 q2, f (q1 ⊔ q2) = (f q1 ⊔ f q2)) ->
  f (qunify c) = qunify (map f c).
Proof.
  induction c; simpl; intros; auto.
  rewrite <- IHc; auto.
Qed.


Lemma sindexr_skip_senv : forall {c : senvs} {xs} {i} {o}, i <> length xs -> sindexr i o (c :: xs) = sindexr i o xs.
Proof.
  intros. simpl. rewrite <- PeanoNat.Nat.eqb_neq in H. rewrite senv_length_coersion. rewrite H. auto.
Qed.

Lemma squish_cons : forall s1 s2, squish (s1 ++ s2) = (squish s1) ++ (squish s2).
intros. unfold squish. rewrite map_app; auto.
Qed.

Lemma squish_app: forall a s, squish (a :: s) = (TUnit, qunify (a.q)) :: (squish s).
  intros. unfold squish. simpl. auto.
Qed.
#[global] Hint Resolve squish_app : core.

Lemma squish_indexr: forall {l c Σ},
  indexr l Σ = Some c ->
  indexr l (squish Σ) = Some (TUnit, qunify (c.q)).
Proof.
  intros. induction Σ. inversion H.
  bdestruct (l =? ‖Σ‖); subst. rewrite squish_app. rewrite <- squish_length. rewrite indexr_head in H. inversion H; subst. rewrite indexr_head; auto.
  rewrite squish_app. rewrite indexr_skip; auto. rewrite indexr_skip in H; auto. rewrite squish_length. auto.
Qed.


Lemma wf_senv_indexr : forall Σ L s,
  wf_senv Σ ->
  indexr L Σ = Some s ->
  wf_senvc (‖ Σ ‖) s.
Proof.
  intros. unfold wf_senv in *. eapply H; eauto.
Qed.


Lemma wf_senvs_indexr : forall {s L k T q},
  wf_senvs L s ->
  indexr k s = Some (T, q) ->
  closed_ty 0 0 L T /\ closed_Qual 0 0 (L) q ↑ /\ ♦∉ q.
Proof.
  intros. unfold wf_senvs in *. specialize (H k T q H0). intuition.
Qed.


Lemma sindexr_indexr_rewrite : forall {X} {Σ : list (list X) } {l o c}, indexr l Σ = Some c -> sindexr l o Σ = indexr o c.
Proof.
  induction Σ; intros; subst. inversion H.
  bdestruct (l =? ‖Σ‖); subst. rewrite indexr_head in H. inversion H; subst. rewrite sindexr_head; auto.
  rewrite sindexr_skip; auto. rewrite indexr_skip in H; auto.
Qed.

Lemma getquals_map : forall (c : senvs) (f : qual -> qual) (g : (ty * qual) -> (ty * qual)) {h},
  g = (fun X : ty * qual => let (T0 , q0) := X in (h T0, f q0)) ->
  map f (c .q) = ((map g c) .q) .
Proof.
  intros. subst. induction c; simpl; auto. rewrite IHc; f_equal.
  destruct a; simpl; auto.
Qed.

Lemma getquals_length : forall c,
  ‖ c.q ‖ = ‖ c ‖.
Proof.
  unfold getquals. intros. rewrite map_length; auto.
Qed.

Lemma getquals_app : forall T q c,
  ((T,q) :: c) .q = q :: (c.q).
Proof.
  intros. unfold getquals; simpl; auto.
Qed.

Lemma wf_senvs_shrink : forall {L a c},
  wf_senvs L (a :: c) ->
  wf_senvs L c.
Proof.
  intros. unfold wf_senvs in *. intros. eapply H. rewrite indexr_skip; eauto. apply indexr_var_some' in H0; lia.
Qed.

Lemma wf_senvs_getquals : forall {L c},
  wf_senvs L c ->
  (forall x q, indexr x (c.q) = Some q -> ♦∉ q /\  closed_Qual 0 0 L q ↑).
Proof.
  intros. induction c; simpl in *. inversion H0.
  rewrite getquals_length in *. bdestruct (x =? ‖c‖); subst. unfold wf_senvs in H. destruct a as [T' q']. specialize (H (‖c‖) T' q'). rewrite indexr_head in H. simpl in H0. inversion H0; subst. intuition.
  apply IHc; auto. eapply wf_senvs_shrink; eauto.
Qed.

Lemma wf_senvs_qunify : forall {L c},
  wf_senvs L c ->
  ♦∉ qunify (c.q) /\ closed_Qual 0 0 L (qunify (c.q))↑.
Proof.
  intros. specialize (wf_senvs_getquals H). clear H; intros. remember (c.q) as ls. generalize dependent c. induction ls; auto; intros.
  destruct c; simpl; auto. inversion Heqls. destruct p as [T q]. rewrite getquals_app in Heqls. inversion Heqls; subst.
  assert (forall (x : nat) (q0 : qual), indexr x ((c .q)) = Some q0 -> ♦∉ q0 /\ closed_Qual 0 0 L q0 ↑). { intros. specialize (H x q0). apply H. rewrite indexr_skip; auto. apply indexr_var_some' in H0; lia. }
  specialize (IHls H0 c eq_refl); clear H0. specialize (H (‖c.q‖) q). rewrite indexr_head in H. specialize (H eq_refl). destruct IHls; destruct H.
  split. Qcrush. apply closed_Qual_qor; auto.
Qed.


Lemma indexr_squish_c_exists : forall {Σ x T q},
  indexr x (squish Σ) = Some (T, q) ->
  exists c, indexr x Σ = Some c /\ q = qunify (c.q) /\ T = TUnit.
Proof.
  intros. induction Σ; simpl in *. inversion H.
  rewrite squish_length in H. bdestruct (x =? (‖Σ‖)); subst.
    inversion H; subst. exists a; auto.
    specialize (IHΣ H). auto.
Qed.


Lemma wf_senv_closed_qenv_qn : forall Σ,
  wf_senv Σ ->
  closed_qenv_qn (‖ Σ ‖) (squish Σ).
Proof.
  intros. unfold closed_qenv_qn; intros. unfold wf_senv in *. destruct a as [T q]. apply indexr_squish_c_exists in H0 as H1. destruct H1 as [c [H1 [H2 H3]]]. subst.
  apply H in H1 as H'. unfold wf_senvc in H'. destruct H'. apply wf_senvs_qunify in H3; destruct H3. Qcrush.
Qed.
#[global] Hint Resolve wf_senv_closed_qenv_qn : core.



Lemma sindexr_skips_senv : forall {xs' xs : senv} {i} {o}, i < length xs -> sindexr i o (xs' ++ xs) = sindexr i o xs.
  induction xs'; intros; intuition.
  replace ((a :: xs') ++ xs) with (a :: (xs' ++ xs)).
  rewrite sindexr_skip_senv. eauto. rewrite app_length. lia. auto.
Qed.

Lemma qdom_cons_qor: forall a (Σ : senv),
  (qdom (a :: Σ)) = (qdom Σ ⊔ &! (‖ Σ ‖)).
intros. apply Q_lift_eq. rewrite Q_lift_or. repeat rewrite Q_lift_qdom. Qcrush; simpl in *. lia. lia. bdestruct (x =? (‖ Σ ‖)); intuition.
Qed.

Lemma qdom_cons_qor_squish: forall a (Σ : senvs),
  (qdom (a :: Σ)) = (qdom Σ ⊔ &! (‖ Σ ‖)).
intros. apply Q_lift_eq. rewrite Q_lift_or. repeat rewrite Q_lift_qdom. Qcrush; simpl in *. lia. lia. bdestruct (x =? (‖ Σ ‖)); intuition.
Qed.

Lemma qdom_squish : forall (Σ : senv),
  qdom Σ = qdom (squish Σ).
Proof.
  induction Σ; simpl; auto.
  rewrite qdom_cons_qor. rewrite qdom_cons_qor_squish. f_equal; auto. rewrite squish_length; auto.
Qed.

Lemma update_preserve_qdom : forall {A} {σ : list (option (list A))} {l v}, l ∈ₗ (qdom' σ) -> qdom' σ = qdom' (update σ l (Some v)).
Proof.
  intros. unfold qdom' in *. f_equal. unfold n_dom' in *. rewrite <- update_length.
  simpl in *. unfold N_lift in *. apply andb_true_iff in H. destruct H.
  destruct (indexr l σ) eqn:?. destruct o. all: intuition.
  apply FunctionalExtensionality.functional_extensionality. intro.
  bdestruct (x <? ‖ σ ‖); simpl; auto.
  bdestruct (x =? l). subst. rewrite update_indexr_hit. rewrite Heqo. auto. auto.
  rewrite update_indexr_miss. auto. auto.
Qed.


Lemma supdate_preserve_qdom : forall {A} {σ : list (option (list A))} {l o v}, l ∈ₗ (qdom' σ) -> qdom' σ = qdom' (supdate σ l o (v)).
Proof.
  intros. unfold qdom' in *. f_equal. unfold n_dom' in *. rewrite <- supdate_length.
  simpl in *. unfold N_lift in *. auto. apply andb_true_iff in H. destruct H.
  destruct (indexr l σ) eqn:?; try discriminate H0. destruct o0. all: intuition.
  apply FunctionalExtensionality.functional_extensionality. intro.
  bdestruct (x <? ‖ σ ‖); simpl; auto.
  bdestruct (x =? l). subst. rewrite supdate_indexr; auto. rewrite Heqo0; simpl; auto.
    rewrite supdate_indexr_miss; auto.
Qed.


Lemma cinsert_preserve_qdom : forall {A} {σ } {l} {v : A}, l < length σ -> qdom' σ = qdom' (cinsert σ l (v)).
Proof.
  intros. unfold qdom' in *. f_equal. unfold n_dom' in *. rewrite cinsert_length.
  apply FunctionalExtensionality.functional_extensionality. intro.
  bdestruct (x <? ‖ σ ‖); simpl; auto.
  bdestruct (x =? l). subst.
  + specialize (indexr_some_exists σ l H); intros. destruct H1 as [c' H1]. rewrite H1. destruct c'. specialize (@cinsert_indexr _ σ l l0 v H1); intros. rewrite H2; auto. rewrite cinsert_indexr_None; auto.
  + rewrite cinsert_indexr_miss; auto.
Qed.

Lemma sinsert_sindexr : forall {A} {Σ l c} {v:A},
  indexr l Σ = Some c ->
  sindexr l ( length c ) (sinsert Σ l v) = Some v.
Proof.
  intros. erewrite sindexr_indexr_rewrite. 2: erewrite sinsert_indexr; eauto. rewrite indexr_head; auto.
Qed.
