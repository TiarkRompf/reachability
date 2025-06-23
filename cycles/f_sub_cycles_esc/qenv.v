Require Export Arith.EqNat.
Require Export Arith.Le.
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

Definition tenv := env (binding * bool * ty * qual). (* (binding, isFunctionSelfRef, Type, Qual) *)
Definition senv := env (bool * ty * qual). (* isSelfRef, Type, Qual *)

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

#[export] Instance senv_qenv : @qenv (bool * ty * qual) := {
  qenv_q := snd; qenv_qn := qlocs; qenv_Qn := qlocs;
  qenv_qn_prop := qnmap_qlocs;
}.
#[global] Hint Resolve senv_qenv : core.


(* Store typing contains closed types and well-scoped, saturated qualifiers. *)
Inductive wf_senv : senv -> Prop :=
| wf_senv_nil : wf_senv []
| wf_senv_cons : forall Σ T q,
    wf_senv Σ ->
    ♦∉ q ->
    closed_ty 0 0 (‖Σ‖) T ->
    closed_Qual 0 0 (‖Σ‖) q↑ ->
    wf_senv ((false, T, q) :: Σ)
| wf_senv_cons_self : forall Σ T q,
    wf_senv Σ ->
    ♦∉ q ->
    closed_ty 0 0 (‖Σ‖) T ->
    closed_Qual 1 0 (‖Σ‖) q↑ ->
    wf_senv ((true, T, q) :: Σ)
.
#[global] Hint Constructors wf_senv : core.

Inductive wf_tenv : tenv -> senv -> Prop :=
  | wf_tenv_nil : forall Σ, wf_senv Σ -> wf_tenv [] Σ
  | wf_tenv_cons : forall Γ Σ bd fr T q,
      wf_tenv Γ Σ ->
      closed_ty 0 (‖Γ‖) (‖Σ‖) T ->
      closed_Qual 0 (‖Γ‖) (‖Σ‖) q↑ ->
      wf_tenv ((bd, fr, T, q) :: Γ) Σ
.
#[global] Hint Constructors wf_tenv : core.


(***************************
 *  wf_qenv: "Telescope"  *
 **************************)

Inductive wf_qenv {p : Type} `{qenv p} : (env p) -> Prop :=
  | wf_qenv_nil : wf_qenv []
  | wf_qenv_cons : forall E a,
      wf_qenv E ->
      closed_Nats (‖E‖) (qenv_Qn (qenv_q a) ↑) ->
      wf_qenv (a :: E).
#[global] Hint Constructors wf_qenv : core.

(*****************
*  closed_qenv  *
*****************)

Definition closed_qenv {p : Type} `{qenv p} (b f l : nat) (E : env p) : Prop :=
  forall x a, indexr x E = Some a -> closed_Qual b f l (qenv_q a) ↑.

(********************
*  closed_qenv_qn  *
********************)

Definition closed_qenv_qn {p : Type} `{qenv p} (n : nat) (E : env p) : Prop :=
  forall x a, indexr x E = Some a -> closed_Nats n (qenv_Qn (qenv_q a) ↑).

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

Lemma wf_senv_wf_qenv : forall (Σ: senv),
  wf_senv Σ ->
  wf_qenv Σ.
intros. induction H; auto. all: constructor; auto; Qcrush.
Qed.
#[global] Hint Resolve wf_senv_wf_qenv : core.

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

Lemma wf_senv_closed_qenv_qn : forall Σ,
  wf_senv Σ ->
  closed_qenv_qn (‖ Σ ‖) Σ.
intros. induction H; simpl; auto. apply closed_qenv_qn_empty. apply ([]:senv).
all: apply closed_qenv_qn_extend; eauto; Qcrush.
Qed.
#[global] Hint Resolve wf_senv_closed_qenv_qn : core.

Lemma closed_tenv_closed_qn: forall b f l (Γ : tenv), closed_qenv b f l Γ -> closed_qenv_qn f Γ.
intros. unfold closed_qenv, closed_qenv_qn in *. intros. specialize (H x a H0). Qcrush.
Qed.

Lemma closed_senv_closed_qn: forall b f l (Σ : senv), closed_qenv b f l Σ -> closed_qenv_qn l Σ.
intros. unfold closed_qenv, closed_qenv_qn in *. intros. specialize (H x a H0). Qcrush.
Qed.

