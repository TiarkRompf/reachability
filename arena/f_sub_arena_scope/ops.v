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

Import QualNotations.
Local Open Scope qualifiers.
Import OpeningNotations.
Local Open Scope opening.


(******************
*  splicible_env  *
 ******************)

Class splicible_env {p : Type} `{@qenv p}: Type := {
  (* how to splice/unsplice an element in the environment *)
  env_splice : nat -> p -> p;
  env_unsplice : nat -> p -> p;
  env_elmt_fvs : p -> nat -> bool;
  env_splice_unsplice_id : forall {n : nat} {a : p}, (env_unsplice n (env_splice n a)) = a;
  (* env_unsplice_splice_id : forall {n : nat} {a : p}, ~N_lift (qfvs (qenv_q a)) n -> (env_splice n (env_unsplice n a)) = a; *)
}.

Definition splice_tenv_elmt := (fun n (X : (binding * bool * ty * qual)) =>
  match X with
  | (bd, b, T, q) => (bd, b, splice_ty n T, splice_qual n q)
  end).

Definition splice_senv_elmt := (fun n (X : (ty * qual)) =>
  match X with
  | (T, q) => (splice_ty n T, splice_qual n q)
  end).

Definition unsplice_tenv_elmt := (fun n (X : (binding * bool * ty * qual)) =>
  match X with
  | (bd, b, T, q) => (bd, b, unsplice_ty n T, unsplice_qual n q)
  end).

Definition unsplice_senv_elmt := (fun n (X : (ty * qual)) =>
  match X with
  | (T, q) => (unsplice_ty n T, unsplice_qual n q)
  end).

Lemma unsplice_splice_qual_id : forall {q k}, ~(varF k) ∈ᵥ q -> splice_qual k (unsplice_qual k q) = q.
intros.
apply Q_lift_eq. Qcrush.
- bdestruct (x <? k); intuition. assert (x > k); intuition. destruct x. lia. eauto.
- subst. eauto.
- destruct x. lia. eauto.
Qed.

Lemma unsplice_splice_Qual_id : forall {q k}, ~(qfvs q) k -> splice_Qual k (unsplice_Qual k q) = q.
intros. qual_destruct q. Qcrush.
- bdestruct (x <? k); intuition. assert (x > k); intuition. destruct x. lia. eauto.
- subst. eauto.
- destruct x. lia. eauto.
Qed.

Lemma unsplice_splice_ty_id : forall {T k}, ~Tfvs T k -> splice_ty k (unsplice_ty k T) = T.
intros. induction T; simpl in *; eauto.
- destruct v; auto. destruct (lt_dec k i); simpl. destruct (le_lt_dec k (pred i)); destruct i; eauto; lia. destruct (le_lt_dec k i); destruct i; eauto; lia.
- rewrite IHT1, IHT2. repeat rewrite unsplice_splice_qual_id. all: intuition.
- rewrite IHT1, IHT2. repeat rewrite unsplice_splice_qual_id. all: intuition.
- rewrite IHT, unsplice_splice_qual_id; intuition.
Qed.

Lemma splice_unsplice_qual_id : forall {q k}, unsplice_qual k (splice_qual k q) = q.
intros.
apply Q_lift_eq. Qcrush. bdestruct (x <? k); intuition.
Qed.

Lemma splice_unsplice_Qual_id : forall {q k}, unsplice_Qual k (splice_Qual k q) = q.
intros. qual_destruct q. unfold unsplice_Qual. Qcrush. bdestruct (x <? k); intuition.
Qed.

Lemma splice_unsplice_ty_id : forall {T k}, unsplice_ty k (splice_ty k T) = T.
intros. induction T; simpl; repeat rewrite splice_unsplice_qual_id ; repeat rewrite IHT; repeat rewrite IHT1; repeat rewrite IHT2; auto. destruct v; auto. destruct (le_lt_dec k i); simpl; auto. destruct (lt_dec k (S i)); auto. lia. destruct (lt_dec k i); auto. lia.
Qed.

Lemma splice_unsplice_tenv_elmt_id : forall n a, unsplice_tenv_elmt n (splice_tenv_elmt n a) = a.
intros. destruct a as [ [ [ bd b ] T] q]. simpl. rewrite splice_unsplice_qual_id, splice_unsplice_ty_id. auto.
Qed.

Lemma splice_unsplice_senv_elmt_id : forall n a, unsplice_senv_elmt n (splice_senv_elmt n a) = a.
intros. destruct a as [T q]. simpl. rewrite splice_unsplice_qual_id, splice_unsplice_ty_id. auto.
Qed.

#[export] Instance tenv_splicible : @splicible_env (binding * bool * ty * qual) tenv_qenv := {
  env_splice := splice_tenv_elmt;
  env_unsplice := unsplice_tenv_elmt;
  env_elmt_fvs := fun a n => tfvs (snd (fst a)) n || qfvs (snd a) n;
  env_splice_unsplice_id := splice_unsplice_tenv_elmt_id;
  (* env_unsplice_splice_id := unsplice_splice_tenv_elmt_id; *)
}.
#[global] Hint Resolve tenv_splicible : core.

#[export] Instance senv_splicible : @splicible_env (ty * qual) senv_qenv := {
  env_splice := splice_senv_elmt;
  env_unsplice := unsplice_senv_elmt;
  env_elmt_fvs := fun a n => tfvs (fst a) n || qfvs (snd a) n;
  env_splice_unsplice_id := splice_unsplice_senv_elmt_id;
  (* env_unsplice_splice_id := unsplice_splice_senv_elmt_id; *)
}.
#[global] Hint Resolve senv_splicible : core.

#[global] Hint Rewrite (@N_lift_dom (binding * bool * ty * qual)) : nlift_rewrite.
#[global] Hint Rewrite (@N_lift_dom (ty * qual)) : nlift_rewrite.

Definition splice_env {p : Type} `{splicible_env p} (n : nat) (E : env p) : env p := map (env_splice n) E.
Definition splice_tenv (n : nat) (Γ : tenv) : tenv := splice_env n Γ.
Definition splice_senvs (n : nat) (Σ : senvs) : senvs := splice_env n Σ.
Definition splice_senv (n : nat) (Σ : senv) : senv := map (splice_senvs n) Σ.


Module SplicingNotations.
  Declare Scope splicing.
  Notation "t ↑ᵗ n" := (splice n t) (at level 10) : splicing.
  Notation "T ↑ᵀ n" := (splice_ty n T) (at level 10) : splicing.
  Notation "q ↑ᵈ n" := (splice_qual n q) (at level 10) : splicing.
  Notation "g ↑ᴳ n" := (splice_env n g) (at level 10) : splicing.
  Notation "g s↑ᴳ n" := (splice_senv n g) (at level 10) : splicing.
End SplicingNotations.
Import SplicingNotations.
Local Open Scope splicing.


(* Substitutions

   It is assumed that substitution is always on the first two context entries, which
   is why other free variables are unconditionally decremented.
*)
Fixpoint subst_tm (t : tm) (v : nat) (u : tm) : tm :=
  match t with
  | ttabs t       => ttabs (subst_tm t v u)
  | ttapp t       => ttapp (subst_tm t v u)
  | tunit         => tunit
  | # x           => # x
  | $ x           => if Nat.eqb x v then u else $(pred x)
  | tabs t        => tabs (subst_tm t v u)
  | tapp t1 t2    => tapp (subst_tm t1 v u) (subst_tm t2 v u)
  | & (l, o)      => & (l, o)
  | tref t        => tref (subst_tm t v u)
  | trefat t1 t2  => trefat (subst_tm t1 v u) (subst_tm t2 v u)
  | ! t           => ! (subst_tm t v u)
  | tassign t1 t2 => tassign (subst_tm t1 v u) (subst_tm t2 v u)
  | twithr t1 t2  => twithr (subst_tm t1 v u) (subst_tm t2 v u)
  | twithc l t    => twithc l (subst_tm t v u)
  end.

Fixpoint subst_ty (T : ty) (v : nat) (U: ty) (q : qual) : ty :=
  match T with
  | TTop             => TTop
  | TVar (varF i)    => if Nat.eqb i v then U else (TVar (varF (pred i)))
  | TVar (varB i)    => TVar (varB i)
  | TAll q1 q2 T1 T2 => TAll (subst_qual q1 v q) (subst_qual q2 v q) (subst_ty T1 v U q) (subst_ty T2 v U q)
  | TUnit            => TUnit
  | TFun q1 q2 T1 T2 => TFun (subst_qual q1 v q) (subst_qual q2 v q) (subst_ty T1 v U q) (subst_ty T2 v U q)
  | TRef q1 T        => TRef (subst_qual q1 v q) (subst_ty T v U q)
  end.

(**********************
*  substitutable_env  *
 **********************)

Class substitutable_env {p : Type} `{@qenv p}: Type := {
  (* how to substitute an element in the environment *)
  env_subst : nat -> ty -> qual -> p -> p;
  env_subst_qenv_q_dist : forall a v T' q', subst_qual (qenv_q a) v q' = qenv_q (env_subst v T' q' a)
}.

Definition subst_tenv_elmt := (fun n T' q' (X : (binding * bool * ty * qual)) =>
  match X with
  | (bd, b, T, q) => (bd, b, subst_ty T n T' q', subst_qual q n q')
  end).

Definition subst_senv_elmt := (fun n T' q' (X : (ty * qual)) =>
  match X with
  | (T, q) => (subst_ty T n T' q', subst_qual q n q')
  end).


Lemma tenv_subst_qenv_q_dist : forall (a : (binding * bool * ty * qual)) v T' q', subst_qual (snd a) v q' = snd (subst_tenv_elmt v T' q' a).
intros. destruct a as [ [ [ ? ? ] ? ] ? ]. simpl. auto.
Qed.

Lemma senv_subst_qenv_q_dist : forall (a : (ty * qual)) v T' q', subst_qual (snd a) v q' = snd (subst_senv_elmt v T' q' a).
intros. destruct a as [ ? ? ]. simpl. auto.
Qed.

#[export] Instance tenv_substitutable : @substitutable_env (binding * bool * ty * qual) tenv_qenv := {
  env_subst := subst_tenv_elmt;
  env_subst_qenv_q_dist := tenv_subst_qenv_q_dist;
}.
#[global] Hint Resolve tenv_substitutable : core.

#[export] Instance senv_substitutable : @substitutable_env (ty * qual) senv_qenv := {
  env_subst := subst_senv_elmt;
  env_subst_qenv_q_dist := senv_subst_qenv_q_dist;
}.
#[global] Hint Resolve senv_substitutable : core.

Definition subst_env {p : Type} `{substitutable_env p} (n : nat) (T' : ty) (q' : qual)  (E : env p): env p := map (env_subst n T' q') E.

Definition subst_tenv (Γ : tenv) (v : nat) (U: ty)(q1 : qual) : tenv := subst_env v U q1 Γ.
Definition subst_senv (Σ : senv) (v : nat) (U: ty)(q1 : qual) : senv := map (subst_env v U q1) Σ.

Module SubstitutionNotations.
  Declare Scope substitutions.
  Notation "{ v1 |-> t1 ; t2 }ᵗ t"  := (subst_tm (subst_tm t v1 t1) v1 t2) (at level 10) : substitutions.
  Notation "{ v1 |-> t1 }ᵗ t"       := (subst_tm t v1 t1) (at level 10) : substitutions.
  Notation "{ v1 |-> q1 ; q2 }ᵈ q"  := (subst_qual (subst_qual q v1 q1) v1 q2) (at level 10) : substitutions.
  Notation "{ v1 |-> q1 }ᵈ q"       := (subst_qual q v1 q1) (at level 10) : substitutions.
  Notation "{ v1 |-> U1 ~ q1 ; U2 ~ q2  }ᵀ T" := (subst_ty (subst_ty T v1 U1 q1) v1 U2 q2) (at level 10) : substitutions.
  Notation "{ v1 |-> U1 ~ q1 }ᵀ T" := (subst_ty T v1 U1 q1) (at level 10) : substitutions.
  Notation "{ v1 |-> T1 ~ q1 }ᴳ G" := (subst_env v1 T1 q1 G) (at level 10) : substitutions.
  Notation "{ v1 |-> T1 ~ q1 ; T2 ~ q2 }ᴳ G" := (subst_env v1 T2 q2 (subst_env v1 T1 q1 G)) (at level 10) : substitutions.
End SubstitutionNotations.
Import SubstitutionNotations.
Local Open Scope substitutions.


(**********************
*  Tranitive Closures  *
 **********************)

Fixpoint q_trans_one {p : Type} `{qenv p} (E : env p) (q : qual) :=
  match E with
  | a :: E' => if (qenv_qn q (length E'))
      then qor (q_trans_one E' q) (qenv_q a)
      else (q_trans_one E' q)
  | [] => q
  end.

Definition N_trans_one {p : Type} `{qenv p} (E : env p) (q : Qual) (f : Qual -> Nats) (x : nat) : Prop :=
  f q x \/
    exists x',
      qenv_Qn q x' /\
        exists a, indexr x' E = Some a /\ f (Q_lift (qenv_q a)) x.

Fixpoint q_trans'' {p : Type} `{qenv p} (E : env p) (q : qual) (fuel : nat) {struct fuel} :=
  match fuel with
  | 0 => q
  | S fuel' => q_trans'' E (q_trans_one E q) fuel'
  end.
#[global] Hint Unfold q_trans'' : core.

(* the returning natset contains the component indicated by f, of the transitive closure of q expanding upon environment E *)
Definition N_trans'' {p : Type} `{qenv p} (E : env p) (q : Qual) (f : Qual -> Nats) (fuel : nat) (x : nat) : Prop :=
  f q x \/
  exists fuel', fuel = S fuel' /\
  exists x', qenv_Qn q x' /\
  exists a, indexr x' E = Some a /\ f (Q_lift (q_trans'' E (qenv_q a) fuel')) x.
#[global] Hint Unfold N_trans'' : core.


Definition q_trans_tenv (Γ : tenv) (q : qual) := q_trans'' Γ q (‖Γ‖).
#[global] Hint Unfold q_trans_tenv : core.

(* the free variable can point to something in the store, but not vise versa *)

(* The premise that a qualifier has been "saturated", which we don't require *)
Definition qenv_saturated_q'' {p : Type} `{qenv p} (E : env p) (q : qual) :=
  q_trans_one E q = q.
#[global] Hint Unfold qenv_saturated_q'' : core.


Fixpoint cardinality (q : qual) {p : Type} `{qenv p} (E : env p) : nat :=
  match E with
  | [] => 0
  | a :: E' => if qenv_qn q (‖ E' ‖) then S (cardinality q E') else cardinality q E'
  end.


Lemma N_lift_trans_one : forall {p : Type} `{qenv p} (E : env p) q (f : qual -> nats) (F : Qual -> Nats),
  @qnmap f F ->
  N_lift (f (q_trans_one E q)) = N_trans_one E (Q_lift q) F.
Proof.
  intros p H E q f F HfF. pose proof qenv_qn_prop as Hqenv. rewrite Q_lift_qn. generalize dependent q. induction E; intros.
- unfold N_trans_one. Qcrush. Ex. discriminate.
- apply FunctionalExtensionality.functional_extensionality. intros. apply PropExtensionality.propositional_extensionality. split.
  + intros. simpl in *.
    ndestruct (qenv_qn q (‖ E ‖)).
    ++ (* including a *)
      rewrite <- Q_lift_qn in H0. rewrite qn_or_dist in H0. nlift. repeat rewrite Q_lift_qn in H0. rewrite IHE in H0. destruct H0.
      -- (* in the rest of the environment E *)
         unfold N_trans_one in *. intuition. right. Ex. exists x0. intuition. exists x1. intuition. apply indexr_extend1. auto.
      -- (* in a *)
         unfold N_trans_one in *. intuition. right. Ex. exists (‖ E ‖). intuition. rewrite <- Q_lift_qn. auto. exists a. intuition. eapply indexr_head; eauto.
    ++ (* not including a *)
      rewrite <- Q_lift_qn in H0. rewrite Q_lift_qn in H0. rewrite IHE in H0. unfold N_trans_one in *. intuition. right. Ex. exists x0. intuition. exists x1. intuition. apply indexr_extend1. auto.
  + intros. simpl in *.
    ndestruct (qenv_qn q (‖ E ‖)).
    ++ (* including a *)
      rewrite <- Q_lift_qn. rewrite qn_or_dist. nlift. repeat rewrite Q_lift_qn. rewrite IHE. unfold N_trans_one. unfold N_trans_one in H0. destruct H0.
      (* q reaches x directly *)
      left. left. auto.
      (* q reaches x transitively *)
      Ex. bdestruct (x0 =? ‖ E ‖).
      -- (* q -> ‖ E ‖ -> x *)
         right. subst. rewrite indexr_head in H3. inversion H3. subst. auto.
      -- (* q -> x1 -> x *)
         left. right. exists x0. intuition. exists x1. intuition. erewrite <- indexr_skip; eauto.
    ++ (* not including a *)
      rewrite IHE. unfold N_trans_one in *. intuition. right. Ex. bdestruct (x0 =? ‖ E ‖).
      -- (* q reaches E, impossible *)
         subst. rewrite <- Q_lift_qn in H2. contradiction.
      -- (* q -> x1 -> x *)
         exists x0. intuition. exists x1. intuition. erewrite <- indexr_skip; eauto.
Qed.


(********************
*  N_lift_trans''  *
********************)

Lemma q_trans_one_extend_closed_id : forall {p : Type} `{qenv p} (E E' : env p) q,
  E' ⊇ E ->
  closed_Nats (‖ E ‖) (qenv_Qn q ↑) ->
  (q_trans_one E' q) = (q_trans_one E q).
intros. unfold extends in H0. destruct H0. subst. induction x; simpl; auto. rewrite app_length. ndestruct (qenv_qn q (‖ x ‖ + ‖ E ‖)). exfalso. unfold closed_Nats in *. specialize (H1 (‖ x ‖ + ‖ E ‖)). erewrite Q_lift_qn in H0; eauto. apply H1 in H0. lia. eauto. Unshelve. apply qenv_qn_prop.
Qed.

Lemma q_trans_one_extend_closed_id' : forall {p : Type} `{qenv p} (a : p) (E : env p) q,
  closed_Nats (‖ E ‖) (qenv_Qn q ↑) ->
  (q_trans_one (a::E) q) = (q_trans_one E q).
intros. simpl. ndestruct (qenv_qn q (‖ E ‖)). exfalso. unfold closed_Nats in *. specialize (H0 (‖ E ‖)). erewrite Q_lift_qn in H1; eauto. apply H0 in H1. lia. eauto. Unshelve. apply qenv_qn_prop.
Qed.

Lemma q_trans_one_subq' : forall {p : Type} `{qenv p} (E : env p) (q : qual),
  q ⊑↑ q_trans_one E q.
intros. induction E; auto. simpl. ndestruct (qenv_qn q (‖ E ‖)); Qcrush.
Qed.

Lemma q_trans''_incr_subq : forall {p : Type} `{qenv p} (E : env p) q (fuel : nat),
  q_trans'' E q fuel ⊑↑ q_trans'' E q (S fuel).
intros. generalize dependent q. induction fuel; intros; simpl in *.
- induction E; simpl in *; auto. ndestruct (qenv_qn q (‖ E ‖)); Qcrush.
- apply IHfuel.
Qed.

Lemma q_trans''_incr_subq' : forall {p : Type} `{qenv p} (E : env p) q (F : Qual -> Nats) (fuel x: nat),
  Qn_sub' F ->
  F (q_trans'' E q fuel) ↑ x ->
  F (q_trans'' E q (S fuel)) ↑ x.
intros. unfold Qn_sub', N_sub in H0. eapply H0 with (q1:=(q_trans'' E q fuel)↑); eauto. eapply q_trans''_incr_subq; eauto.
Qed.

Lemma q_trans''_incr_subq'' : forall {p : Type} `{qenv p} (E : env p) q (F : Qual -> Nats) (x: nat),
  Qn_sub' F ->
  F q ↑ x ->
  F (q_trans_one E q) ↑ x.
intros. unfold Qn_sub', N_sub in H0. eapply H0 with (q1:=q↑); eauto. apply q_trans_one_subq'.
Qed.

Lemma q_trans''_incr_subq''' : forall {p : Type} `{qenv p} (E : env p) q (F : Qual -> Nats) (fuel x: nat),
  Qn_sub' F ->
  F q ↑ x ->
  F (q_trans'' E q fuel) ↑ x.
intros. unfold Qn_sub', N_sub in H0. induction fuel; simpl; auto. eapply q_trans''_incr_subq'; eauto.
Qed.


Lemma N_lift_trans'': forall {p : Type} `{qenv p} (E : env p) q (f : qual -> nats) (F : Qual -> Nats) (fuel : nat),
  @qnmap f F ->
  N_lift (f (q_trans'' E q fuel)) = N_trans'' E (Q_lift q) F fuel.
Proof.
  intros p H E q f F fuel HfF. rewrite Q_lift_qn. generalize dependent q. pose proof qenv_qn_prop as Hqn. induction fuel; intros.
- simpl. unfold N_trans''. Qcrush. Ex.
- apply FunctionalExtensionality.functional_extensionality. intros. apply PropExtensionality.propositional_extensionality. split; intros.
  + (* N_trans'' (q_trans_one q) fuel -> N_trans'' q (S fuel) *)
    simpl in *. rewrite IHfuel in H0. unfold N_trans''. unfold N_trans'' in H0. destruct H0.
      -- (* q_trans_one q x *)
         rewrite <- Q_lift_qn in H0. erewrite N_lift_trans_one in H0; eauto. unfold N_trans_one in H0. destruct H0. intuition. right. Ex. exists fuel. intuition. exists x0. intuition. exists x1. intuition. rewrite IHfuel. unfold N_trans''. intuition.
      -- (* q_trans_one q -[fuel']-> x, need to show q -[S fuel']-> x *)
         destruct H0 as [fuel' H0]. right. exists fuel. intuition. rewrite <- Q_lift_qn in H2. erewrite N_lift_trans_one in H2; eauto. subst. Ex. unfold N_trans_one in H1. destruct H1.
exists x0. intuition. exists x1. intuition. eapply q_trans''_incr_subq'; eauto. eapply Qn_sub; eauto.
Ex. exists x2. intuition. exists x3. intuition. rewrite IHfuel. unfold N_trans''. right. exists fuel'. intuition. exists x0. intuition. exists x1. intuition.
  + (* N_trans'' (q_trans_one q) fuel -> N_trans'' q (S fuel) *)
    simpl. rewrite IHfuel. unfold N_trans''. unfold N_trans'' in H0. destruct H0.
      -- (* directly reachable *)
         left. intuition. simpl in *. eapply q_trans''_incr_subq''; eauto. eapply Qn_sub; eauto.
      -- (* reachable in S fuel steps *)
         Ex. inversion H1. subst. rename x0 into fuel. destruct fuel as [|fuel'].
         (* fuel = 0. reachable via one step *)
         * left. inversion H1. subst. simpl in *.
rewrite <- Q_lift_qn. erewrite N_lift_trans_one; eauto. unfold N_trans_one. right. exists x1. intuition. exists x2. intuition.
         (* fuel > 0. reachable via multiple steps *)
         * right. exists fuel'. intuition. rewrite IHfuel in H4. unfold N_trans'' in H4. destruct H4.
           ++ (* q -> x1 -> x2 -> x *)
              exists x1. intuition. eapply q_trans''_incr_subq''; eauto. apply qenv_qn_prop. exists x2. intuition. eapply q_trans''_incr_subq'''; eauto. apply Qn_sub.
           ++ (* q -> x1 -> x2 -> x3 -> x4 -> x *)
              Ex. exists x3. intuition. rewrite <- Q_lift_qn. erewrite N_lift_trans_one; eauto. unfold N_trans_one. right. exists x1. intuition. exists x2. intuition. exists x4. intuition. inversion H4. subst. auto.
Qed.

(******************
*  Q_lift_trans  *
******************)

Definition Q_trans'' {p : Type} `{qenv p} (E : env p) (q : Qual) (fuel : nat) : Qual :=
  (N_trans'' E q Qfr fuel 0, N_trans'' E q qfvs fuel, N_trans'' E q qbvs fuel, N_trans'' E q qlocs fuel).
#[global] Hint Unfold Q_trans'' : core.

Lemma Q_lift_trans'' : forall {p : Type} `{qenv p} (E : env p) q fuel,
  Q_lift (q_trans'' E q fuel) = Q_trans'' E (Q_lift q) fuel.
Proof.
  intros p Hp E q fuel. generalize dependent q. induction fuel. intros. unfold Q_trans'', N_trans''. Qcrush; Ex. intros. simpl. rewrite IHfuel. generalize dependent q. induction E; intros; simpl.
  - unfold Q_trans'', N_trans''. Qcrush; Ex; discriminate.
  - ndestruct (qenv_qn q (‖ E ‖)).
    + (* (‖ E ‖) in q *)
      unfold Q_trans'', Qor.
      f_equal. f_equal. f_equal.
      all: try apply FunctionalExtensionality.functional_extensionality;
      intros; try apply PropExtensionality.propositional_extensionality.
      -- repeat erewrite <- N_lift_trans'' with (f:=qfr); eauto. simpl. unfold N_lift in H. rewrite H. rewrite N_lift_trans'' with (F:=Qfr); eauto. erewrite Q_lift_or; eauto. intuition.
      -- repeat erewrite <- N_lift_trans'' with (f:=qfvs); eauto. simpl. unfold N_lift in H. rewrite H. rewrite N_lift_trans'' with (F:=qfvs); eauto. erewrite Q_lift_or; eauto. intuition.
      -- repeat erewrite <- N_lift_trans'' with (f:=qbvs); eauto. simpl. unfold N_lift in H. rewrite H. rewrite N_lift_trans'' with (F:=qbvs); eauto. erewrite Q_lift_or; eauto. intuition.
      -- repeat erewrite <- N_lift_trans'' with (f:=qlocs); eauto. simpl. unfold N_lift in H. rewrite H. rewrite N_lift_trans'' with (F:=qlocs); eauto. erewrite Q_lift_or; eauto. intuition.
    + unfold Q_trans'', Qor.
      f_equal. f_equal. f_equal.
      all: try apply FunctionalExtensionality.functional_extensionality;
      intros; try apply PropExtensionality.propositional_extensionality.
      -- repeat erewrite <- N_lift_trans'' with (f:=qfr); eauto. simpl. clift. intuition.
      -- repeat erewrite <- N_lift_trans'' with (f:=qfvs); eauto. simpl. clift. intuition.
      -- repeat erewrite <- N_lift_trans'' with (f:=qbvs); eauto. simpl. clift. intuition.
      -- repeat erewrite <- N_lift_trans'' with (f:=qlocs); eauto. simpl. clift. intuition.
Qed.

(**************
*  trans or  *
**************)

Lemma q_trans''_one_commute : forall {p : Type} `{qenv p} (E : env p) {q : qual} {fuel : nat},
  q_trans_one E (q_trans'' E q fuel) = q_trans'' E (q_trans_one E q) fuel.
intros. generalize dependent q. induction fuel; intros; simpl; auto.
Qed.

Lemma q_trans_one_or_dist : forall {p : Type} `{qenv p} (E : env p) q1 q2,
  (q_trans_one E q1 ⊔ q_trans_one E q2) = q_trans_one E (q1 ⊔ q2).
intros. induction E; simpl; auto. ndestruct (qenv_qn q1 (‖ E ‖)); ndestruct (qenv_qn q2 (‖ E ‖)); erewrite qn_or_dist; eauto using qenv_qn_prop; clift; rewrite <- IHE; apply Q_lift_eq; Qcrush. Unshelve. all: eauto using qenv_qn_prop.
Qed.

Lemma q_trans''_or_dist : forall {p : Type} `{qenv p} (E : env p) q1 q2 fuel,
  (q_trans'' E q1 fuel ⊔ q_trans'' E q2 fuel) = q_trans'' E (q1 ⊔ q2) fuel.
intros. generalize dependent q1. generalize dependent q2. induction fuel; intros; simpl; auto. rewrite IHfuel. rewrite q_trans_one_or_dist. auto.
Qed.


(*****************
*  trans fresh  *
*****************)

Lemma q_trans_one_tenv_freshv_id : forall (Γ : tenv), q_trans_one Γ ({♦}) = {♦}.
intros. induction Γ; simpl; auto.
Qed.

Lemma q_trans''_tenv_freshv_id : forall (Γ : tenv) n fuel, n >= (‖ Γ ‖) -> (q_trans'' Γ {♦} fuel) = {♦}.
intros. induction fuel; simpl; auto. rewrite q_trans_one_tenv_freshv_id; auto.
Qed.


(***************
*  trans sub  *
***************)

Lemma q_trans''_subq : forall {p : Type} `{qenv p} (E : env p) {q1 q2 : qual} {fuel : nat},
  q1 ⊑↑ q2 ->
  q_trans'' E q1 fuel ⊑↑ q_trans'' E q2 fuel.
intros. repeat rewrite Q_lift_trans''. unfold Q_trans'', N_trans''. pose proof qenv_qn_prop. Qcrush; Ex; right.
  - exists x. intuition. exists x0. intuition. eapply Qn_sub; eauto. Qcrush. exists x1. intuition.
  - exists x0. intuition. exists x1. intuition. eapply Qn_sub; eauto. Qcrush. exists x2. intuition.
  - exists x0. intuition. exists x1. intuition. eapply Qn_sub; eauto. Qcrush. exists x2. intuition.
  - exists x0. intuition. exists x1. intuition. eapply Qn_sub; eauto. Qcrush. exists x2. intuition.
Qed.

Lemma q_trans''_subq' : forall {p : Type} `{qenv p} (E : env p) (q : qual) (fuel : nat),
  q ⊑↑ q_trans'' E q fuel.
intros. repeat rewrite Q_lift_trans''. unfold Q_trans'', N_trans''. pose proof qenv_qn_prop. Qcrush; Ex; right.
Qed.

Definition Q_trans_one {p : Type} `{qenv p} (E : env p) (q : Qual) : Qual :=
  (N_trans_one E q Qfr 0, N_trans_one E q qfvs, N_trans_one E q qbvs, N_trans_one E q qlocs).
#[global] Hint Unfold Q_trans_one : core.

Lemma Q_lift_trans_one : forall {p : Type} `{qenv p} (E : env p) q,
  Q_lift (q_trans_one E q) = Q_trans_one E (Q_lift q).
  intros p Hp E q. unfold Q_lift. replace (♦∈ q_trans_one E q) with (N_lift (qfr (q_trans_one E q)) 0).
repeat erewrite N_lift_trans_one; eauto. unfold N_trans_one, Q_trans_one. Qcrush.
unfold qfr,qfresh,N_lift,Is_true. destruct (fst (fst (fst (q_trans_one E q)))); Qcrush.
Qed.

Lemma q_trans_one_extend_subq : forall {p : Type} `{qenv p} (E E' : env p) {q1 q2 : qual} {fuel : nat},
  E' ⊇ E ->
  q1 ⊑↑ q2 ->
  q_trans_one E q1 ⊑↑ q_trans_one E' q2.
intros. unfold extends in *. Ex. subst. repeat rewrite Q_lift_trans_one. unfold Q_trans_one, N_trans_one. pose proof qenv_qn_prop. Qcrush; right; Ex.
  - exists x0. intuition. eapply Qn_sub; eauto. Qcrush. exists x1. intuition. apply indexr_extend. auto.
  - exists x1. intuition. eapply Qn_sub; eauto. Qcrush. exists x2. intuition. apply indexr_extend. auto.
  - exists x1. intuition. eapply Qn_sub; eauto. Qcrush. exists x2. intuition. apply indexr_extend. auto.
  - exists x1. intuition. eapply Qn_sub; eauto. Qcrush. exists x2. intuition. apply indexr_extend. auto.
Qed.

Lemma q_trans''_extend_subq : forall {p : Type} `{qenv p} (E E' : env p) {q1 q2 : qual} {fuel : nat},
  E' ⊇ E ->
  q1 ⊑↑ q2 ->
  q_trans'' E q1 fuel ⊑↑ q_trans'' E' q2 fuel.
intros. generalize dependent q1. generalize dependent q2. generalize dependent E. generalize dependent E'. induction fuel; intros. simpl; auto. simpl. unfold extends in *. Ex. subst.
eapply IHfuel; eauto. eapply q_trans_one_extend_subq; eauto. unfold extends. eauto.
Qed.

(***********
*  trans fv  *
***********)

Lemma q_trans_one_tenv_fv_id : forall (Γ : tenv) n, n >= (‖ Γ ‖) -> q_trans_one Γ ($! n) = $! n.
intros. induction Γ; simpl; auto. ndestruct (qfvs $! n (‖ Γ ‖)). Qcrush. apply IHΓ. simpl in *. lia.
Qed.

Lemma q_trans''_tenv_fv_id : forall (Γ : tenv) n fuel, n >= (‖ Γ ‖) -> (q_trans'' Γ $! n fuel) = $! n.
intros. induction fuel; simpl; auto. rewrite q_trans_one_tenv_fv_id; auto.
Qed.


(********************
*  qenv_saturated  *
********************)

Lemma qenv_saturated_trans''_id : forall {p : Type} `{qenv p} (E : env p) (q : qual),
  qenv_saturated_q'' E q -> forall fuel, q_trans'' E q fuel = q.
intros. induction fuel; simpl; auto. unfold qenv_saturated_q'' in H0. rewrite H0. auto.
Qed.


(****************
*  trans fuel  *
****************)

Lemma cardinality_max : forall {p : Type} `{qenv p} (E : env p) q, cardinality q E <= (‖ E ‖).
intros. induction E; simpl; auto. ndestruct (qenv_qn q (‖ E ‖)); lia.
Qed.

Lemma cardinality_subq_le : forall {p : Type} `{qenv p} (E : env p) q1 q2,
  q1 ⊑↑ q2 ->
  cardinality q1 E <= cardinality q2 E.
Proof.
  intros. induction E; simpl; auto. ndestruct (qenv_qn q1 (‖ E ‖)).
  - assert (N_lift (qenv_qn q2) (‖ E ‖)). { erewrite @Q_lift_qn with (Qn:=qenv_Qn) in H1; eauto using qenv_qn_prop. erewrite @Q_lift_qn with (Qn:=qenv_Qn); eauto using qenv_qn_prop. eapply @Qn_sub with (qn:=qenv_qn); eauto using qenv_qn_prop. } clift. lia.
  - ndestruct (qenv_qn q2 (‖ E ‖)). lia. lia.
Qed.

Lemma cardinality_qor_trans : forall {p : Type} `{qenv p} (E : env p) q1 q2,
  cardinality q1 E = cardinality (q1 ⊔ q2) E ->
  (q_trans_one E q1 ⊔ q_trans_one E q2) = ((q_trans_one E q1) ⊔ q2).
Proof.
  intros. induction E; simpl; auto. ndestruct (qenv_qn q1 (‖ E ‖)).
  - assert (Hor: N_lift (qenv_qn (q1 ⊔ q2)) (‖ E ‖)). { erewrite qn_or_dist. Qcrush. }
    assert (cardinality q1 E = cardinality (q1 ⊔ q2) E). { simpl in H0. unfold N_lift in H1,Hor. rewrite H1,Hor in H0. auto. }
    ndestruct (qenv_qn q2 (‖ E ‖)).
    + (* both q1 and q2 reaches store location *)
      replace ((q_trans_one E q1 ⊔ qenv_q a) ⊔ q_trans_one E q2 ⊔ qenv_q a) with ((q_trans_one E q1 ⊔ q_trans_one E q2) ⊔ qenv_q a). rewrite IHE; auto. apply Q_lift_eq. Qcrush. apply Q_lift_eq. Qcrush.
    + (* only q1 reaches store location *)
      replace ((q_trans_one E q1 ⊔ qenv_q a) ⊔ q_trans_one E q2) with ((q_trans_one E q1 ⊔ q_trans_one E q2) ⊔ qenv_q a). rewrite IHE; auto. apply Q_lift_eq. Qcrush. apply Q_lift_eq. Qcrush.
  - ndestruct (qenv_qn q2 (‖ E ‖)).
    + (* impossible. q1 doesn't reach, but q2 reaches store location *)
      exfalso. simpl in H0. unfold N_lift in H1,H2. assert (Hor: N_lift (qenv_qn (q1 ⊔ q2)) (‖ E ‖)). { erewrite qn_or_dist. Qcrush. } apply not_true_is_false in H1. rewrite H1,Hor in H0. pose proof (cardinality_subq_le E q1 (q1 ⊔ q2)). assert (q1 ⊑↑ q1 ⊔ q2). Qcrush. intuition.
    + (* neither q1 nor q2 reaches store location *)
      simpl in H0. unfold N_lift in H1,H2. assert (Hor: ~N_lift (qenv_qn (q1 ⊔ q2)) (‖ E ‖)). { erewrite qn_or_dist. Qcrush. } apply not_true_is_false in H1,Hor. rewrite H1,Hor in H0. intuition.
Unshelve. all: try apply qenv_Qn; eauto using qenv_qn_prop.
Qed.

Lemma cardinality_eq_sat : forall {p : Type} `{qenv p} (E : env p) q,
  cardinality q E = cardinality (q_trans_one E q) E ->
  qenv_saturated_q'' E (q_trans_one E q). (* (q_trans_one E (q_trans_one E q)) = (q_trans_one E q). *)
unfold qenv_saturated_q''. intros. generalize dependent q. induction E; intros; simpl in *; auto. ndestruct (qenv_qn q (‖ E ‖)).
    + assert (N_lift (qenv_qn (q_trans_one E q ⊔ qenv_q a)) (‖ E ‖)). { erewrite qn_or_dist. Qcrush. left. erewrite @N_lift_trans_one with (F:=qenv_Qn); eauto. unfold N_trans_one. left. erewrite <- Q_lift_qn; eauto. apply qenv_qn_prop. }
      unfold N_lift in H2. rewrite H2 in *. inversion H0.
assert (cardinality q E <= cardinality (q_trans_one E q) E). { apply cardinality_subq_le. rewrite Q_lift_trans_one. unfold Q_trans_one, N_trans_one. Qcrush. }
assert (cardinality (q_trans_one E q) E <= cardinality q E). { rewrite H4. apply cardinality_subq_le. Qcrush. }
assert (cardinality q E = cardinality (q_trans_one E q) E). { lia. } intuition.
rewrite H6 in H4. apply cardinality_qor_trans in H4. rewrite IHE in H4; auto. rewrite <- q_trans_one_or_dist. rewrite IHE; auto. rewrite H4. apply Q_lift_eq. Qcrush.
    + ndestruct (qenv_qn (q_trans_one E q) (‖ E ‖)).
      -- (* impossible due to cardinality: q doesn't have (‖ E ‖), but trans q does *)
         exfalso. pose proof (cardinality_subq_le E q (q_trans_one E q) (q_trans_one_subq' _ _)). lia.
      -- (* neither q nor trans q have (‖ E ‖) *)
         apply IHE; auto.
Unshelve. apply qenv_Qn. all: eauto using qenv_qn_prop.
Qed.

Lemma cardinality_zero : forall {p : Type} `{qenv p} (E : env p) q,
  cardinality q E = 0 ->
  qenv_saturated_q'' E q. (* q_trans_one E q = q. *)
unfold qenv_saturated_q''. intros. induction E; auto. simpl in *. ndestruct (qenv_qn q (‖ E ‖)); eauto. lia.
Qed.

Lemma cardinality_inc_or_sat : forall {p : Type} `{qenv p} (E : env p) q q',
  q' = q_trans_one E q ->
  S (cardinality q E) <= cardinality q' E \/ qenv_saturated_q'' E q'.
unfold qenv_saturated_q''. intros. bdestruct (cardinality q E =? cardinality q' E).
  - (* cardinality is equal, no growth, must be saturated. *)
    subst. right. apply cardinality_eq_sat; auto.
  - (* cardinality not equal *)
    subst. left. pose proof (cardinality_subq_le E q (q_trans_one E q) (q_trans_one_subq' _ _)). intuition.
Qed.

Lemma cardinality_inc_or_sat' : forall {p : Type} `{qenv p} (E : env p) q q' fuel,
  q' = q_trans'' E q fuel ->
  cardinality q E + fuel <= cardinality q' E \/
  qenv_saturated_q'' E q'.
intros. generalize dependent q'. generalize dependent q. induction fuel; intros. left. simpl in *. subst. lia.
specialize (IHfuel (q_trans_one E q) (q_trans'' E (q_trans_one E q) fuel)).
pose proof (cardinality_inc_or_sat E q (q_trans_one E q)). destruct H1; auto.
  - (* cardinality increasing, q_trans_one not saturated *)
    intuition.
    + (* cardinality increasing, q_trans'' not saturated *)
      subst. left. simpl. lia.
    + (* q_trans'' saturated, the entire thing must be saturated *)
      subst. right. simpl. auto.
  - (* q_trans_one saturated *)
    subst. right. simpl. pose proof (qenv_saturated_trans''_id _ _ H1). rewrite H0. auto.
Qed.

Lemma q_trans''_fuel_max_gen : forall {p : Type} `{qenv p} (E : env p) (q : qual) (fuel : nat),
  ‖ E ‖ < S fuel ->
  q_trans'' E (q_trans_one E q) fuel = q_trans'' E q fuel.
intros. rewrite <- q_trans''_one_commute.
pose proof (cardinality_inc_or_sat' E q (q_trans'' E q fuel) fuel).
pose proof (cardinality_inc_or_sat E (q_trans'' E q fuel) (q_trans_one E (q_trans'' E q fuel))). intuition.
  - (* cardinality increasing, impossible *)
    pose proof (cardinality_max E (q_trans_one E (q_trans'' E q fuel))). lia.
  - bdestruct (cardinality q E =? 0).
    + (* cardinality is zero, already saturated *)
      apply cardinality_zero in H3. unfold qenv_saturated_q'' in H2, H3. rewrite q_trans''_one_commute. rewrite H3. auto.
    + (* cardinalty not zero, impossible because exceeds max bound *)
      pose proof (cardinality_max E (q_trans'' E q fuel)). lia.
Qed.

Lemma q_trans''_fuel_max : forall {p : Type} `{qenv p} (E : env p) (q : qual) (fuel : nat),
  fuel >= (‖ E ‖) ->
  q_trans'' E q fuel = q_trans'' E q (‖ E ‖).
intros. generalize dependent E. generalize dependent q. induction fuel; intros.
  - assert (Hl: (‖ E ‖) = 0). lia. rewrite Hl. auto.
  - simpl. bdestruct ((‖ E ‖) =? S fuel).
    + rewrite H1. simpl. eauto.
    + rewrite <- IHfuel; try lia.
      apply q_trans''_fuel_max_gen. lia.
Qed.


(**********************
*  q_trans'' splice  *
**********************)

Lemma splice_env_app : forall {p : Type} `{splicible_env p} (E1 E2 : env p) n,
  (E1 ↑ᴳ n ++ E2 ↑ᴳ n) = (E1 ++ E2) ↑ᴳ n.
intros. induction E1; simpl; auto. rewrite IHE1. auto.
Qed.

Lemma splice_env_length : forall {p : Type} `{splicible_env p} (E : env p) {n E}, ‖ E ↑ᴳ n ‖ = ‖E‖.
  intros. unfold splice_env. rewrite map_length. auto.
Qed.

Lemma splice_ty_not_in : forall T k, ~Tfvs (T ↑ᵀ k) k.
intros. induction T; simpl; auto.
  - destruct v; destruct (le_lt_dec k i); simpl; lia.
  - Qcrush.
  - Qcrush.
  - Qcrush.
Qed.


Lemma splice_id : forall {T b f l}, closed_tm b f l T -> T ↑ᵗ f = T.
  induction T; intros; inversion H; subst; simpl; auto;
    try solve [erewrite IHT1; eauto; erewrite IHT2; eauto | erewrite IHT; eauto].
    destruct (le_lt_dec f x) eqn:Heq. lia. auto.
Qed.

Lemma splice_ty_id : forall {T b f l}, closed_ty b f l T -> T ↑ᵀ f = T.
  induction T; intros; inversion H; subst; simpl; auto;
    try solve [erewrite IHT1; eauto; erewrite IHT2; eauto | erewrite IHT; eauto].
  repeat erewrite splice_qual_id; eauto.
  destruct (le_lt_dec f x) eqn: Heq; intuition.
  all: f_equal; try eapply splice_qual_id; eauto.
Qed.

Lemma splice_open : forall {T j n m}, ([[ j ~> $(m + n) ]]ᵗ T) ↑ᵗ n = [[ j ~> $(S (m + n)) ]]ᵗ (T ↑ᵗ n).
  induction T; intros; simpl; auto;
    try solve [erewrite IHT1; eauto; erewrite IHT2; eauto | erewrite IHT; eauto].
  destruct v; simpl. destruct (le_lt_dec n i) eqn:Heq; auto.
  destruct (PeanoNat.Nat.eqb j i) eqn:Heq; auto.
  simpl. destruct (le_lt_dec n (m + n)) eqn:Heq'. auto. lia.
Qed.

Lemma splice_ty_open : forall {T j fr n m},
  ([[j ~> $(m + n) ~ ${fr}(m + n) ]]ᵀ T) ↑ᵀ n =
  [[j ~> $(S (m + n)) ~ ${fr}(S (m + n)) ]]ᵀ (T ↑ᵀ n).
  induction T; intros; simpl; auto;
    try solve [erewrite IHT1; eauto; erewrite IHT2; eauto | erewrite IHT; eauto].
  destruct v; simpl.
  destruct (le_lt_dec n i ); simpl; auto.
  destruct (j =? i ); simpl; auto.
  f_equal. destruct (le_lt_dec n (m + n) ); simpl; auto. intuition.
  all: f_equal; try eapply splice_qual_open; eauto.
Qed.

Lemma splice_open' : forall {T} {A} {D : A} {ρ ρ'}, ((T <~²ᵗ (ρ ++ ρ')) ↑ᵗ ‖ρ'‖) = (T ↑ᵗ ‖ρ'‖) <~²ᵗ (ρ ++ D :: ρ').
  intros. unfold open_tm'.
  replace (‖ ρ ++ ρ' ‖) with (‖ρ‖ + ‖ρ'‖).
  replace (S (‖ ρ ++ D :: ρ' ‖)) with (S (S (‖ρ‖) + (‖ρ'‖))).
  replace (‖ ρ ++ D :: ρ' ‖) with (S (‖ρ‖ + ‖ρ'‖)).
  repeat rewrite <- splice_open. auto.
  all: rewrite app_length; simpl; lia.
Qed.

Lemma splice_qual_open' : forall {d} {A} {D : A} {ρ ρ'}, ((d <~²ᵈ (ρ ++ ρ')) ↑ᵈ ‖ρ'‖) = (d ↑ᵈ ‖ρ'‖) <~²ᵈ (ρ ++ D :: ρ').
  intros. unfold openq'. unfold openq.
  replace (‖ ρ ++ ρ' ‖) with (‖ρ‖ + ‖ρ'‖).
  replace (S (‖ ρ ++ D :: ρ' ‖)) with (S (S (‖ρ‖) + (‖ρ'‖))).
  replace (‖ ρ ++ D :: ρ' ‖) with (S (‖ρ‖ + ‖ρ'‖)).
  repeat rewrite <- splice_qual_open. auto.
  all: rewrite app_length; simpl; lia.
Qed.

Lemma splice_qual_open''': forall {k d i} {q}, ([[i ~> d ]]ᵈ q) ↑ᵈ k = [[i ~> (d ↑ᵈ k)]]ᵈ (q ↑ᵈ k ).
Proof. qual_destruct q. qual_destruct d. unfold_q.
#[local] Hint Resolve n_reflect_true : bdestruct.
bdestruct (bvs i); simpl; auto. Qcrush. unfold_n. bdestruct (x =? k); bdestruct (x <? k); auto.
#[local] Remove Hints n_reflect_true : bdestruct.
Qed.

Lemma splice_ty_open' : forall {T} {A} {D : A} {ρ ρ'}, ((T <~²ᵀ (ρ ++ ρ')) ↑ᵀ ‖ρ'‖) = (T ↑ᵀ ‖ρ'‖) <~²ᵀ (ρ ++ D :: ρ').
  intros. unfold open_ty'. unfold open_ty.
  replace (‖ ρ ++ ρ' ‖) with (‖ρ‖ + ‖ρ'‖).
  replace (S (‖ ρ ++ D :: ρ' ‖)) with (S (S (‖ρ‖) + (‖ρ'‖))).
  replace (‖ ρ ++ D :: ρ' ‖) with (S (‖ρ‖ + ‖ρ'‖)).
  repeat rewrite <- splice_ty_open. auto.
  all: rewrite app_length; simpl; lia.
Qed.

Lemma splice_ty_open_rec_ty: forall {T T1  d1} {k i},
  splice_ty k ([[i ~> T1 ~ d1 ]]ᵀ T) = [[ i ~> (splice_ty k T1) ~ (splice_qual k d1) ]]ᵀ (splice_ty k T) .
Proof. intros. generalize dependent k. generalize dependent i. induction T; intros; simpl; auto;
    try solve [erewrite IHT1; eauto; erewrite IHT2; eauto | erewrite IHT; eauto].
    destruct v; simpl.
    destruct (le_lt_dec k i0); auto.
    destruct (i =? i0); auto.
    rewrite IHT1. rewrite IHT2. f_equal. 1,2: rewrite splice_qual_open'''; auto.
    rewrite IHT1. rewrite IHT2. f_equal. 1,2: rewrite splice_qual_open'''; auto.
    rewrite IHT.  f_equal. rewrite splice_qual_open'''; auto.
Qed.

Lemma splice_qual_open'' : forall {k df d1 d2}, (d2 <~ᵈ df; d1) ↑ᵈ k = (d2 ↑ᵈ k) <~ᵈ (df ↑ᵈ k); (d1 ↑ᵈ k).
  intros. qual_destruct d2; qual_destruct d1; qual_destruct df; simpl.
unfold openq. unfold_q.
apply Q_lift_eq.
ndestruct (bvs 0); simpl.
- destruct (n_or (n_diff bvs (n_one 0)) bvs1 1); Qcrush; bdestruct (x <? k); intuition; assert (x > k) by lia; intuition.
- destruct (bvs 1); Qcrush. bdestruct (x <? k); intuition; assert (x > k) by lia; intuition.
Qed.

Lemma splice_ty_open'' : forall {T U V k df d1}, (T <~ᵀ U ~ df; V ~ d1) ↑ᵀ k = (T ↑ᵀ k) <~ᵀ (U ↑ᵀ k) ~ (df ↑ᵈ k); (V ↑ᵀ k) ~ (d1 ↑ᵈ k).
  intros. unfold open_ty. repeat rewrite splice_ty_open_rec_ty. auto.
Qed.

Lemma splice_qual_qor_dist : forall {k q1 q2}, (q1 ⊔ q2) ↑ᵈ k = ((q1 ↑ᵈ k) ⊔ (q2 ↑ᵈ k)).
  intros. apply Q_lift_eq. Qcrush. bdestruct (x <? k); intuition. assert (x > k) by lia. Qcrush.
Qed.

Lemma subqual_splice_lr' : forall {i du df}, du ↑ᵈ i ⊑↑ df ↑ᵈ i <-> du ⊑↑ df.
  intros. intuition.
  - Qcrush. bdestruct (x <? i); intuition. specialize (H x); intuition. assert (S x > i) by lia. specialize (H (S x)); intuition.
  - Qcrush.
Qed.
#[global] Hint Resolve subqual_splice_lr' : core.

Lemma splice_senv_squish : forall Σ n,
    squish (Σ s↑ᴳ n) = (squish Σ) ↑ᴳ n.
Proof.
  intros. induction Σ; simpl; auto.
  unfold splice_senvs. f_equal; auto. unfold "↑ᴳ". f_equal. rewrite qunify_map; auto. f_equal. unfold env_splice. simpl. unfold splice_senv_elmt. erewrite getquals_map; eauto.
  intros. rewrite splice_qual_lub_dist; auto.
Qed.

Lemma splice_senv_length : forall {n Σ}, ‖ Σ s↑ᴳ n ‖ = ‖Σ‖.
Proof.
  intros. unfold "s↑ᴳ". rewrite map_length. auto.
Qed.

Lemma q_trans_one_splice_tenv_gen : forall (Γ : tenv) d n,
  n >= (‖ Γ ‖) ->
  (q_trans_one Γ d) ↑ᵈ n = q_trans_one (Γ ↑ᴳ n) (d ↑ᵈ n).
intros. generalize dependent n. induction Γ; intros; simpl; auto. rewrite splice_env_length; auto. ndestruct (qfvs d (‖ Γ ‖)).
  - assert (N_lift (qfvs (d ↑ᵈ n)) (‖ Γ ‖)). Qcrush. clift. rewrite splice_qual_qor_dist. rewrite IHΓ. Qcrush. simpl in *. lia.
  - assert (~N_lift (qfvs (d ↑ᵈ n)) (‖ Γ ‖)). Qcrush. clift. Qcrush.
Qed.

Lemma q_trans_one_splice_tenv : forall (Γ1 Γ2 : tenv) X d,
  (q_trans_one (Γ1 ++ Γ2) d) ↑ᵈ (‖ Γ2 ‖) =
  (q_trans_one (Γ1 ↑ᴳ (‖ Γ2 ‖) ++ X :: Γ2 ↑ᴳ (‖ Γ2 ‖)) (d ↑ᵈ (‖ Γ2 ‖))).
intros. induction Γ1; simpl; try rewrite splice_env_length; auto.
  - ndestruct (qfvs (d ↑ᵈ (‖ Γ2 ‖)) (‖ Γ2 ‖)).
    + exfalso. Qcrush.
    + rewrite q_trans_one_splice_tenv_gen; eauto.
  - ndestruct (qfvs d (‖ Γ1 ++ Γ2 ‖)).
    + assert (N_lift (qfvs (d ↑ᵈ (‖ Γ2 ‖))) (‖ Γ1 ↑ᴳ (‖ Γ2 ‖) ++ X :: Γ2 ↑ᴳ (‖ Γ2 ‖) ‖)). { rewrite app_length,splice_env_length in *; auto. simpl. rewrite splice_env_length; auto. rewrite <- plus_n_Sm. Qcrush. } clift. rewrite <- IHΓ1. rewrite splice_qual_qor_dist. destruct a as [ [ [bd b] T] q]. simpl. auto.
    + assert (~N_lift (qfvs (d ↑ᵈ (‖ Γ2 ‖))) (‖ Γ1 ↑ᴳ (‖ Γ2 ‖) ++ X :: Γ2 ↑ᴳ (‖ Γ2 ‖) ‖)). { rewrite app_length,splice_env_length in *; auto. simpl. rewrite splice_env_length; auto. rewrite <- plus_n_Sm. Qcrush. } clift.
Qed.

Lemma q_trans''_splice_tenv_qfr_inv : forall (Γ1 Γ2 : tenv) X d fuel,
(qfr (q_trans'' (Γ1 ++ Γ2) d fuel)) =
(qfr (q_trans'' (Γ1 ↑ᴳ (‖ Γ2 ‖) ++ X :: Γ2 ↑ᴳ (‖ Γ2 ‖)) (d ↑ᵈ (‖ Γ2 ‖)) fuel)).
intros. generalize dependent d. induction fuel; intros; simpl; auto. rewrite IHfuel. erewrite q_trans_one_splice_tenv; eauto.
Qed.

Lemma q_trans''_splice_tenv_qfvs_dist : forall (Γ1 Γ2 : tenv) X d fuel,
qfvs ((q_trans'' (Γ1 ++ Γ2) d fuel) ↑ᵈ (‖ Γ2 ‖)) =
qfvs ((q_trans'' (Γ1 ↑ᴳ (‖ Γ2 ‖) ++ X :: Γ2 ↑ᴳ (‖ Γ2 ‖)) (d ↑ᵈ (‖ Γ2 ‖)) fuel)).
intros. generalize dependent d. induction fuel; intros; simpl; auto. rewrite IHfuel. erewrite q_trans_one_splice_tenv; eauto.
Qed.

Lemma q_trans''_splice_tenv_qbvs_inv : forall (Γ1 Γ2 : tenv) X d fuel,
(qbvs (q_trans'' (Γ1 ++ Γ2) d fuel)) =
(qbvs (q_trans'' (Γ1 ↑ᴳ (‖ Γ2 ‖) ++ X :: Γ2 ↑ᴳ (‖ Γ2 ‖)) (d ↑ᵈ (‖ Γ2 ‖)) fuel)).
intros. generalize dependent d. induction fuel; intros; simpl; auto. rewrite IHfuel. erewrite q_trans_one_splice_tenv; eauto.
Qed.

Lemma q_trans''_splice_tenv_qlocs_inv : forall (Γ1 Γ2 : tenv) X d fuel,
(qlocs (q_trans'' (Γ1 ++ Γ2) d fuel)) =
(qlocs (q_trans'' (Γ1 ↑ᴳ (‖ Γ2 ‖) ++ X :: Γ2 ↑ᴳ (‖ Γ2 ‖)) (d ↑ᵈ (‖ Γ2 ‖)) fuel)).
intros. generalize dependent d. induction fuel; intros; simpl; auto. rewrite IHfuel. erewrite q_trans_one_splice_tenv; eauto.
Qed.

Lemma splice_q_trans_tenv_comm : forall {Γ1 Γ2 X q},
(q_trans_tenv (Γ1 ↑ᴳ (‖ Γ2 ‖) ++ X :: Γ2 ↑ᴳ (‖ Γ2 ‖)) (q ↑ᵈ (‖ Γ2 ‖))) =
(q_trans_tenv (Γ1 ++ Γ2) q ↑ᵈ (‖ Γ2 ‖)).
intros. apply Q_lift_eq. unfold q_trans_tenv. rewrite Q_lift_splice_qual. repeat rewrite Q_lift_trans''. unfold splice_Qual, Q_trans''. unfold qfresh,qfvs,qbvs,qlocs; simpl. f_equal. f_equal. f_equal.
- repeat rewrite <- N_lift_trans'' with (f:=qfr); auto. rewrite app_length. simpl. rewrite <- plus_n_Sm. erewrite <- q_trans''_splice_tenv_qfr_inv; eauto. rewrite q_trans''_fuel_max. auto. rewrite app_length. repeat rewrite splice_env_length; auto.
- rewrite <- N_lift_trans'' with (f:=qfvs); auto. rewrite <- q_trans''_splice_tenv_qfvs_dist. rewrite Q_lift_qn. rewrite Q_lift_splice_qual. unfold splice_Qual. unfold qfvs. simpl. rewrite q_trans''_fuel_max. rewrite N_lift_trans'' with (F:=qfvs); eauto. repeat rewrite app_length. simpl. repeat rewrite splice_tenv_length. rewrite <- plus_n_Sm. repeat rewrite splice_env_length; auto.
- repeat rewrite <- N_lift_trans'' with (f:=qbvs); auto. rewrite app_length. simpl. rewrite <- plus_n_Sm. erewrite <- q_trans''_splice_tenv_qbvs_inv; eauto. rewrite q_trans''_fuel_max. auto. rewrite app_length. repeat rewrite splice_env_length; auto.
- repeat rewrite <- N_lift_trans'' with (f:=qlocs); auto. rewrite app_length. simpl. rewrite <- plus_n_Sm. erewrite <- q_trans''_splice_tenv_qlocs_inv; eauto. rewrite q_trans''_fuel_max. auto. rewrite app_length. repeat rewrite splice_env_length; auto.
Qed.


Lemma n_splice_injective : forall n n' k, n_splice k n = n_splice k n' -> n = n'.
Proof.
  intros. unfold_n. apply FunctionalExtensionality.functional_extensionality. intros. bdestruct (x <? k).
  - apply FunctionalExtensionality.equal_f with (x:=x) in H. bdestruct (x =? k). intuition. apply Nat.ltb_lt in H0. rewrite H0 in H. apply H.
  - apply FunctionalExtensionality.equal_f with (x:=S x) in H. bdestruct (S x =? k). lia. bdestruct (S x <? k). lia. simpl in *. apply H.
Qed.

Lemma n_splice_one_S : forall i k, i >= k -> n_splice k (n_one i) = n_one (S i).
intros. unfold_n. apply FunctionalExtensionality.functional_extensionality. intros. bdestruct (x =? k).
  - subst. bdestruct (k =? S i); intuition.
  - bdestruct (x <? k). bdestruct (x <? i); intuition. bdestruct (x =? i); intuition. bdestruct (x =? S i); intuition.
    bdestruct (pred x =? i); bdestruct (x =? S i); intuition.
Qed.

Lemma splice_ty_injective : forall {T T' k}, T ↑ᵀ k = T' ↑ᵀ k -> T = T'.
  induction T; intros; intuition; destruct T'; simpl in H; intuition; try destruct v; try destruct v0; try discriminate; auto;
  try match goal with
  | [ H: _ = (if le_lt_dec ?k ?i then _ else _) |- _ ] => destruct (le_lt_dec k i); discriminate
  | [ H: (if le_lt_dec ?k ?i then _ else _) = _ |- _ ] => destruct (le_lt_dec k i); discriminate
  end.
  - destruct (le_lt_dec k i) eqn:Hltki; destruct (le_lt_dec k i0) eqn:Hltk0; inversion H; subst; auto; try lia.
  - qual_destruct q. qual_destruct q0. qual_destruct q1. qual_destruct q2. inversion H. apply n_splice_injective in H2, H6. unfold_q. subst.
    specialize (IHT1 T'1 k). specialize (IHT2 T'2 k). intuition. subst. auto.
  - qual_destruct q. qual_destruct q0. qual_destruct q1. qual_destruct q2. inversion H. apply n_splice_injective in H2, H6. unfold_q. subst.
    specialize (IHT1 T'1 k). specialize (IHT2 T'2 k). intuition. subst. auto.
  - qual_destruct q. qual_destruct q0. inversion H. apply n_splice_injective in H2. unfold_q. subst.
    specialize (IHT T' k). intuition. subst. auto.
Qed.


(* Lemmas of transitive closures.
  transitive closures are context dependent
*)

Lemma wf_tenv_shrink : forall {Γ Σ a}, wf_tenv (a::Γ) Σ -> wf_tenv Γ Σ.
intros. inversion H. auto.
Qed.
#[global] Hint Resolve wf_tenv_shrink : core.

Lemma closed_qenv_q_trans_one_monotone : forall {p : Type} `{qenv p} (E : env p) (q : qual) (b f l : nat),
  closed_qenv b f l E -> closed_Qual b f l q ↑ -> closed_Qual b f l (q_trans_one E q)↑.
intros. induction E; simpl; auto. ndestruct (qenv_qn q (‖ E ‖)). apply closed_Qual_qor. apply IHE. eapply closed_qenv_shrink; eauto. apply H0 with (x:=(‖ E ‖)). apply indexr_head. apply IHE. eapply closed_qenv_shrink; eauto.
Qed.

Lemma closed_qenv_q_trans''_monotone : forall {p : Type} `{qenv p} (E : env p) (q : qual) (b f l fuel : nat),
  closed_qenv b f l E -> closed_Qual b f l q ↑ -> closed_Qual b f l (q_trans'' E q fuel)↑.
intros. generalize dependent q. induction fuel; intros; simpl; auto. apply IHfuel. apply closed_qenv_q_trans_one_monotone; auto.
Qed.


Lemma q_trans_one_weaken_subq : forall Γ d1 d2 bd b U du,
  d1 ⊑↑ d2 ->
  q_trans_one Γ d1 ⊑↑ q_trans_one ((bd, b, U, du) :: Γ) d2.
intros. induction Γ; simpl; auto.
ndestruct (qfvs d2 0); Qcrush.
assert (q_trans_one Γ d1 ⊑↑ q_trans_one Γ d2). { eapply q_trans_one_extend_subq; eauto. apply 0. unfold extends. exists []. auto. }
ndestruct (qfvs d2 (S (‖ Γ ‖))).
  - ndestruct (qfvs d1 (‖ Γ ‖)). ndestruct (qfvs d2 (‖ Γ ‖)). Qcrush. Qcrush. ndestruct (qfvs d2 (‖ Γ ‖)). Qcrush. Qcrush.
  - ndestruct (qfvs d1 (‖ Γ ‖)). ndestruct (qfvs d2 (‖ Γ ‖)). Qcrush. Qcrush. ndestruct (qfvs d2 (‖ Γ ‖)). Qcrush. Qcrush.
Qed.

Lemma q_trans''_weaken_subq : forall (Γ: tenv) d1 d2 a fuel,
  d1 ⊑↑ d2 ->
  q_trans'' Γ d1 fuel ⊑↑ q_trans'' (a :: Γ) d2 (S fuel).
intros. simpl. ndestruct (qfvs d2 (‖ Γ ‖)).
  - remember (q_trans_one Γ d2) as d2t. generalize dependent d2t. generalize dependent d2. generalize dependent d1. generalize dependent Γ. induction fuel; intros; simpl; auto. eapply @Subq_trans with (d2:=d2); auto. eapply @Subq_trans with (d2:=d2t); auto. subst. apply q_trans_one_subq'.
ndestruct (qfvs (d2t ⊔ (snd a)) (‖ Γ ‖)).
    + specialize (IHfuel Γ (q_trans_one Γ d1) (d2t ⊔ (snd a))). subst.
      assert (q_trans_one Γ d1 ⊑↑ q_trans_one Γ d2 ⊔ (snd a)). eapply @Subq_trans with (d2:=q_trans_one Γ d2); eauto. eapply q_trans_one_extend_subq; eauto. unfold extends. exists []. auto. intuition.
    + subst. exfalso.
      assert (d2 ⊑↑ q_trans_one Γ d2 ⊔ (snd a)). { eapply @Subq_trans with (d2:=q_trans_one Γ d2); eauto. apply q_trans_one_subq'. }
      assert (N_sub (N_lift (qfvs d2)) (N_lift (qfvs (q_trans_one Γ d2 ⊔ (snd a))))). { Qcrush. }
      eauto.
  - remember (q_trans_one Γ d2) as d2t. generalize dependent d2t. generalize dependent d2.
    generalize dependent d1. generalize dependent Γ. induction fuel; intros; simpl; auto. eapply @Subq_trans with (d2:=d2); auto. subst. apply q_trans_one_subq'. ndestruct (qfvs d2t (‖ Γ ‖)).
    + subst. eapply q_trans''_extend_subq; eauto.
      unfold extends. exists [a]. auto.
      eapply @Subq_trans with (d2:=q_trans_one Γ (q_trans_one Γ d2)); eauto.
      eapply @Subq_trans with (d2:=(q_trans_one Γ d2)); eauto.
      eapply q_trans_one_extend_subq; eauto. unfold extends. exists []. auto.
      apply q_trans_one_subq'.
    + subst. eapply IHfuel with (d1:=q_trans_one Γ d1) (d2:=q_trans_one Γ d2); eauto.
      apply q_trans_one_extend_subq; auto. unfold extends. exists []. auto.
Qed.


Lemma q_trans_one_narrowing_subq : forall Γ1 Γ2 d1 d2 bd b U du V dv,
  dv ⊑↑ du ->
  d1 ⊑↑ d2 ->
  q_trans_one (Γ1 ++ (bd, b, V, dv) :: Γ2) d1 ⊑↑ q_trans_one (Γ1 ++ (bd, b, U, du) :: Γ2) d2.
intros. repeat rewrite Q_lift_trans_one. unfold Subq, N_sub,Q_trans_one, N_trans_one. intuition; unfold_q.
  - intuition. left. Qcrush. right. Ex. exists x. intuition. Qcrush. bdestruct (x =? (‖ Γ2 ‖)). subst. rewrite indexr_insert in H3. inversion H3. subst. exists (bd, b, U, du). intuition. apply indexr_insert. Qcrush. exists x0. intuition. bdestruct (x <? (‖ Γ2 ‖)). rewrite <- indexr_insert_lt; auto. rewrite <- indexr_insert_lt in H3; auto. assert (x > (‖ Γ2 ‖)) by lia. destruct x. lia. rewrite <- indexr_insert_ge; intuition. rewrite <- indexr_insert_ge in H3; intuition.
  - intuition. left. Qcrush. right. Ex. exists x0. intuition. Qcrush. bdestruct (x0 =? (‖ Γ2 ‖)). subst. rewrite indexr_insert in H3. inversion H3. subst. exists (bd, b, U, du). intuition. apply indexr_insert. Qcrush. exists x1. intuition. bdestruct (x0 <? (‖ Γ2 ‖)). rewrite <- indexr_insert_lt; auto. rewrite <- indexr_insert_lt in H3; auto. assert (x0 > (‖ Γ2 ‖)) by lia. destruct x0. lia. rewrite <- indexr_insert_ge; intuition. rewrite <- indexr_insert_ge in H3; intuition.
  - intuition. left. Qcrush. right. Ex. exists x0. intuition. Qcrush. bdestruct (x0 =? (‖ Γ2 ‖)). subst. rewrite indexr_insert in H3. inversion H3. subst. exists (bd, b, U, du). intuition. apply indexr_insert. Qcrush. exists x1. intuition. bdestruct (x0 <? (‖ Γ2 ‖)). rewrite <- indexr_insert_lt; auto. rewrite <- indexr_insert_lt in H3; auto. assert (x0 > (‖ Γ2 ‖)) by lia. destruct x0. lia. rewrite <- indexr_insert_ge; intuition. rewrite <- indexr_insert_ge in H3; intuition.
  - intuition. left. Qcrush. right. Ex. exists x0. intuition. Qcrush. bdestruct (x0 =? (‖ Γ2 ‖)). subst. rewrite indexr_insert in H3. inversion H3. subst. exists (bd, b, U, du). intuition. apply indexr_insert. Qcrush. exists x1. intuition. bdestruct (x0 <? (‖ Γ2 ‖)). rewrite <- indexr_insert_lt; auto. rewrite <- indexr_insert_lt in H3; auto. assert (x0 > (‖ Γ2 ‖)) by lia. destruct x0. lia. rewrite <- indexr_insert_ge; intuition. rewrite <- indexr_insert_ge in H3; intuition.
Qed.

Lemma q_trans_tenv_narrowing_subq : forall Γ1 Γ2 d1 d2 bd b U du V dv fuel,
  dv ⊑↑ du ->
  d1 ⊑↑ d2 ->
  (q_trans'' (Γ1 ++ (bd, b, V, dv) :: Γ2) d1 fuel) ⊑↑ (q_trans'' (Γ1 ++ (bd, b, U, du) :: Γ2) d2 fuel).
intros. repeat rewrite Q_lift_trans''. generalize dependent d2. generalize dependent d1. induction fuel; intros. repeat rewrite <- Q_lift_trans''. simpl. auto.
repeat rewrite <- Q_lift_trans''. simpl. repeat rewrite Q_lift_trans''. apply IHfuel. apply q_trans_one_narrowing_subq; auto.
Qed.

Lemma q_trans_tenv_narrowing_subq' : forall Γ1 Γ2 d1 d2 bd b U du V dv,
  dv ⊑↑ du ->
  d1 ⊑↑ d2 ->
  (q_trans_tenv (Γ1 ++ (bd, b, V, dv) :: Γ2) d1) ⊑↑ (q_trans_tenv (Γ1 ++ (bd, b, U, du) :: Γ2) d2).
intros. unfold q_trans_tenv. replace (‖ Γ1 ++ (bd, b, U, du) :: Γ2 ‖) with (‖ Γ1 ++ (bd, b, V, dv) :: Γ2 ‖); auto using q_trans_tenv_narrowing_subq. repeat rewrite app_length. simpl. auto.
Qed.

Lemma q_trans_one_qand_subq : forall {p : Type} `{qenv p} (E : env p) q1 q2,
  q_trans_one E (q1 ⊓ q2) ⊑↑ q_trans_one E q1 ⊓ q_trans_one E q2.
intros. induction E; simpl; auto. ndestruct (qenv_qn (q1 ⊓ q2) (‖ E ‖)).
- assert (N_lift (qenv_qn q1) (‖ E ‖)). { erewrite @Q_lift_qn with (Qn:=qenv_Qn) in *; eauto. rewrite Q_lift_and in H0. erewrite @Qn_and_dist with (qn:=qenv_qn) (Qn:=qenv_Qn) in H0; eauto. Qcrush. all: apply qenv_qn_prop. }
  assert (N_lift (qenv_qn q2) (‖ E ‖)). { erewrite @Q_lift_qn with (Qn:=qenv_Qn) in *; eauto. rewrite Q_lift_and in H0. erewrite @Qn_and_dist with (qn:=qenv_qn) (Qn:=qenv_Qn) in H0; eauto. Qcrush. all: apply qenv_qn_prop. }
  clift. rewrite <- qor_qand_dist_r. eauto using Subq_qor.
- ndestruct (qenv_qn q1 (‖ E ‖)). assert (~N_lift (qenv_qn q2) (‖ E ‖)). { erewrite @Q_lift_qn with (Qn:=qenv_Qn) in *; eauto. rewrite Q_lift_and in H0. erewrite @Qn_and_dist with (qn:=qenv_qn) (Qn:=qenv_Qn) in H0; eauto. Qcrush. all: apply qenv_qn_prop. } clift. rewrite qand_qor_dist_r. eapply Subq_trans; eauto.
  ndestruct (qenv_qn q2 (‖ E ‖)). rewrite qand_qor_dist_l. eapply Subq_trans; eauto. auto.
Qed.

Lemma q_trans''_qand_subq : forall {p : Type} `{qenv p} (E : env p) q1 q2 fuel,
  q_trans'' E (q1 ⊓ q2) fuel ⊑↑ q_trans'' E q1 fuel ⊓ q_trans'' E q2 fuel.
intros. generalize dependent q2. generalize dependent q1. induction fuel; intros; simpl; auto. specialize (IHfuel (q_trans_one E q1) (q_trans_one E q2)). eapply @Subq_trans with (d2:=(q_trans'' E (q_trans_one E q1 ⊓ q_trans_one E q2) fuel)); eauto. apply q_trans''_subq. apply q_trans_one_qand_subq.
Qed.

Lemma q_trans_one_gt_id : forall {p : Type} `{qenv p} (E : env p) q,
  (forall n, n < (‖ E ‖) -> ~N_lift (qenv_qn q) n) ->
  (q_trans_one E q) = q.
intros. induction E; simpl; auto. ndestruct (qenv_qn q (‖ E ‖)).
- exfalso. specialize (H0 (‖ E ‖)). simpl in H0. intuition.
- rewrite IHE; auto. intros. apply H0. simpl. lia.
Qed.

Lemma q_trans''_gt_id : forall {p : Type} `{qenv p} (E : env p) q fuel,
  (forall n, n < (‖ E ‖) -> ~N_lift (qenv_qn q) n) ->
  (q_trans'' E q fuel) = q.
intros. induction fuel; simpl; auto. rewrite q_trans_one_gt_id; auto.
Qed.

Lemma q_trans_one_empty_id : forall {p : Type} `{qenv p} (E : env p) q,
  (forall n, ~N_lift (qenv_qn q) n) ->
  (q_trans_one E q) = q.
intros. induction E; simpl; auto. rewrite IHE. specialize (H0 (‖ E ‖)). unfold N_lift in H0. apply not_true_is_false in H0. rewrite H0. auto.
Qed.

Lemma q_trans''_empty_id : forall {p : Type} `{qenv p} (E : env p) q fuel,
  (forall n, ~N_lift (qenv_qn q) n) ->
  (q_trans'' E q fuel) = q.
intros. induction fuel; simpl; auto. rewrite q_trans_one_empty_id; auto.
Qed.


Lemma q_trans_one_qenv_swallow : forall {p : Type} `{qenv p} (a : p) (E : env p) q,
  (qenv_q a) ⊑↑ (q_trans_one E q) ->
  q_trans_one (a :: E) q = (q_trans_one E q).
intros. simpl. ndestruct (qenv_qn q (‖ E ‖)).
- apply Q_lift_eq. Qcrush.
- Qcrush.
Qed.

Lemma q_trans''_qenv_swallow : forall {p : Type} `{qenv p} (a : p) (E : env p) q fuel,
  (qenv_q a) ⊑↑ (q_trans_one E q) ->
  q_trans'' (a :: E) q fuel = (q_trans'' E q fuel).
intros. generalize dependent q. induction fuel; intros; auto.
simpl. ndestruct (qenv_qn q (‖ E ‖)).
- rewrite IHfuel. rewrite <- q_trans''_or_dist. assert (q_trans'' E (qenv_q a) fuel ⊑↑ q_trans'' E (q_trans_one E q) fuel). apply q_trans''_subq. auto. apply Q_lift_eq. Qcrush. rewrite <- q_trans_one_or_dist. eapply Subq_trans; eauto. eapply @Subq_trans with (d2:=q_trans_one E (q_trans_one E q)). apply q_trans_one_subq'. Qcrush.
- rewrite IHfuel; auto. eapply Subq_trans; eauto. apply q_trans_one_subq'.
Qed.

Lemma q_trans''_qenv_swallow' : forall {p : Type} `{qenv p} (a : p) (E : env p) q fuel,
  (qenv_q a) ⊑↑ q ->
  q_trans'' (a :: E) q fuel = (q_trans'' E q fuel).
intros. apply q_trans''_qenv_swallow. eapply Subq_trans; eauto. apply q_trans_one_subq'.
Qed.

Lemma q_trans_tenv_fv : forall Γ bd fr T q,
  q_trans_tenv ((bd, fr, T, q) :: Γ) $!(‖ Γ ‖) = ((q_trans_tenv Γ q) ⊔ $!(‖ Γ ‖)).
intros. unfold q_trans_tenv. simpl. assert (N_lift (qfvs $! (‖ Γ ‖)) (‖ Γ ‖)). Qcrush. clift. rewrite q_trans''_qenv_swallow'. rewrite <- q_trans''_or_dist. rewrite q_trans_one_gt_id. rewrite q_trans''_gt_id. apply Q_lift_eq. all: Qcrush.
Qed.


Lemma qor_non_fresh : forall q1 q2,
  ♦∉ q1 ->
  ♦∉ q2 ->
  ♦∉ q1 ⊔ q2.
intros. Qcrush.
Qed.

Lemma q_trans_one_non_fresh : forall {p : Type} `{qenv p} (E : env p) d,
  (forall (x : nat) (a : p), indexr x E = Some a -> ♦∉ (qenv_q a)) ->
  ♦∉ d ->
  ♦∉ q_trans_one E d.
intros. induction E; simpl; auto. ndestruct (qenv_qn d (‖ E ‖)).
- apply qor_non_fresh.
  apply IHE. intros. eapply H0 with (x:=x); eauto. rewrite indexr_skip; auto. apply indexr_var_some' in H3. lia.
eapply H0 with (x:=(‖ E ‖)). rewrite indexr_head. auto.
- apply IHE. intros. eapply H0 with (x:=x); eauto. rewrite indexr_skip; auto. apply indexr_var_some' in H3. lia.
Qed.

Lemma q_trans''_non_fresh : forall {p : Type} `{qenv p} (E : env p) fuel d,
  (forall (x : nat) (a : p), indexr x E = Some a -> ♦∉ (qenv_q a)) ->
  ♦∉ d ->
  ♦∉ q_trans'' E d fuel.
intros. generalize dependent d. induction fuel; intros; simpl; auto. apply IHfuel. apply q_trans_one_non_fresh; auto.
Qed.

Lemma qand_diamond_r_non_fresh : forall q, ♦∉ q -> (q ⊓ {♦}) = ∅.
intros. apply Q_lift_eq. Qcrush.
Qed.

Lemma qand_diamond_r_fresh : forall q, ♦∈ q -> (q ⊓ {♦}) = {♦}.
intros. apply Q_lift_eq. Qcrush.
Qed.

Lemma closed_qenv_shrink' : forall {p : Type} `{qenv p} (E1 E2 : env p)
  { b f l },
  closed_qenv b f l (E1 ++ E2) ->
  closed_qenv b f l E1.
intros. induction E1; auto. apply closed_qenv_extend. apply IHE1. all: simpl in H0. eapply closed_qenv_shrink; eauto. apply (H0 (‖ E1 ++ E2 ‖)). rewrite indexr_head; auto.
Qed.


Lemma q_trans_tenv_subq_fresh : forall Γ d1 d2,
d1 ⊑↑ d2 ⊔ {♦} ->
q_trans_tenv Γ d1 ⊑↑ q_trans_tenv Γ d2 ⊔ {♦}.
intros. unfold q_trans_tenv. erewrite <- q_trans''_tenv_freshv_id. rewrite q_trans''_or_dist. eapply q_trans''_subq; auto. eauto.
Qed.



(* ======= Extends_2D =======
  The lemmas are defined elsewhere, definition here for file dependency
*)

Definition extends_2D (Σ' Σ : senv) := forall l c, indexr l Σ = Some c -> exists c', indexr l Σ' = Some c' /\ c' ⊇ c.

Notation "x ⊇₂ y" := (extends_2D x y) (at level 75).

Lemma extends_refl : forall {A}, forall{l : list A}, l ⊇ l.
  intros. unfold extends. exists []. auto.
Qed.
#[global] Hint Resolve extends_refl : core.

Lemma extends_trans : forall {A}, forall{l1 l2 l3 : list A}, l2 ⊇ l1 -> l3 ⊇ l2 -> l3 ⊇ l1.
  intros. unfold extends in *. destruct H. destruct H0. subst. exists (x0 ++ x). rewrite app_assoc. auto.
Qed.
#[global] Hint Resolve extends_trans : core.

Lemma extends_empty : forall {A}, forall{l : list A}, l ⊇ [].
  intros. unfold extends. exists l. rewrite app_nil_r; auto.
Qed.
#[global] Hint Resolve extends_empty : core.

Lemma extends_cons : forall {A}, forall{l : list A}, forall{a:A}, (a :: l) ⊇ l.
  intros. unfold extends. exists [a]. auto.
Qed.
#[global] Hint Resolve extends_cons : core.

Lemma extends_length : forall {A}, forall{l1 l2 : list A}, l1 ⊇ l2 -> length l2 <= length l1.
  intros. unfold extends in H. destruct H as [l' Heq]. subst. rewrite app_length. lia.
Qed.
#[global] Hint Resolve extends_length : core.

Lemma extends_qdom : forall {Σ' Σ : senv}, Σ' ⊇ Σ -> qdom Σ ⊑↑ qdom Σ'.
intros. inversion H.
assert (‖Σ'‖ = ‖x‖ + ‖Σ‖). subst. rewrite app_length. auto. subst. unfold qdom, n_dom. rewrite H1. Qcrush; unfold N_lift in *. rewrite Nat.ltb_lt in H0. rewrite Nat.ltb_lt. lia.
Qed.
#[global] Hint Resolve extends_qdom: core.

Lemma extends_squish : forall Σ Σ',
    Σ' ⊇ Σ -> squish Σ' ⊇ squish Σ.
Proof.
  intros. inversion H. subst. rewrite squish_cons. econstructor; eauto.
Qed.
#[global] Hint Resolve extends_squish: core.

Lemma qdom_extends_subq : forall (Σ Σ' : senv), Σ' ⊇ Σ -> qdom Σ ⊑↑ qdom Σ'.
Proof.
  intros. apply extends_squish in H. apply extends_length in H. rewrite qdom_squish. rewrite qdom_squish. Qcrush.
Qed.

Lemma squish_extends_length : forall Σ' Σ,
  squish Σ' ⊇ squish Σ -> ‖ Σ ‖ <= ‖ Σ' ‖.
Proof.
  intros. rewrite <- squish_length. rewrite <- squish_length. apply extends_length; auto.
Qed.

Lemma qdom_extends_squish_subq : forall (Σ Σ' : senv), squish Σ' ⊇ squish Σ -> qdom Σ ⊑↑ qdom Σ'.
Proof.
  intros. apply extends_length in H. rewrite qdom_squish. rewrite qdom_squish. Qcrush.
Qed.

Lemma extends_equal : forall {A} (l' l : list A), ‖ l' ‖ = ‖ l ‖ -> l' ⊇ l -> l' = l.
  intros. unfold extends in H0. destruct H0 as [lx H0]; subst. destruct lx; auto. rewrite app_length in H; simpl in H. lia.
Qed.

Lemma indexr_exists_length : forall {A} (l : list A) , forall k, (forall x, x < k -> exists a, indexr x l = Some a) -> ‖l‖ >= k.
Proof.
  induction k; intros. lia. specialize (H k). assert (k < S k) by auto. specialize (H H0). destruct H as [a H]. apply indexr_var_some' in H. lia.
Qed.

Lemma indexr_extends_length : forall {A} (l' l : list A), (forall x : nat, x < ‖ l ‖ -> indexr x l = indexr x l') -> ‖ l' ‖ >= ‖ l ‖.
Proof.
  intros. apply indexr_exists_length. intros. specialize (indexr_some_exists l x H0); intros. destruct H1. specialize (H x H0). rewrite <- H. rewrite H1. eauto.
Qed.

Lemma indexr_extends : forall {A} (l': list A) l, (forall x, x < ‖l‖ -> indexr x l = indexr x l') -> l' ⊇ l.
Proof.
  induction l'; intros; simpl. destruct l; auto. simpl in H. assert ((‖ l ‖) < S (‖ l ‖)) by auto. apply H in H0. rewrite Nat.eqb_refl in H0; inversion H0.
  bdestruct (S (‖l'‖) =? ‖l‖).
  + destruct l. auto. simpl in H0. inversion H0. specialize (H (‖l‖)) as H'; simpl in H'. rewrite H2 in H'. rewrite Nat.eqb_refl in H'. assert (‖ l ‖ < S (‖ l ‖)) by auto. specialize (H' H1). inversion H'; subst. rewrite <- extends_equal with (l' := l') (l := l); auto. apply IHl'. intros. specialize (H x). assert (x < ‖ a :: l ‖). simpl; auto. specialize (H H4). do 2 rewrite indexr_skip in H; auto. all: lia.
  + assert ((‖ a :: l' ‖) >= ‖ l ‖). apply indexr_extends_length; auto. simpl in H1. assert ((‖ l' ‖) >= ‖ l ‖). lia. specialize (IHl' l). eapply extends_trans. 2: eapply extends_cons. apply IHl'. intros. specialize (H x H3). rewrite indexr_skip in H; auto. lia.
Qed.

Lemma extends_2D_app1 : forall {Σ c1 c2}, c1 ⊇ c2 -> c1 :: Σ ⊇₂ c2 :: Σ.
Proof.
  intros. unfold extends_2D. intros. bdestruct (l =? ‖Σ‖); subst. rewrite indexr_head in H0. inversion H0; subst. exists c1; auto. rewrite indexr_head; auto. rewrite indexr_skip in H0; auto. rewrite indexr_skip; auto. exists c; eauto.
Qed.

Lemma extends_2D_app2 : forall {Σ1 Σ2 c}, Σ1 ⊇₂ Σ2 -> ‖ Σ1 ‖ = ‖ Σ2 ‖ -> c :: Σ1 ⊇₂ c :: Σ2.
Proof.
  intros. unfold extends_2D in *; intros. bdestruct (l =? ‖Σ1‖); subst. rewrite H0 in H1. rewrite indexr_head in H1. inversion H1; subst. rewrite indexr_head. exists c0; auto.
  rewrite indexr_skip; auto. rewrite indexr_skip in H1. 2: lia. apply H in H1. auto.
Qed.

Lemma extends_2D_refl : forall{l}, l ⊇₂ l.
  intros. unfold extends_2D. intros. exists c; auto.
Qed.
#[global] Hint Resolve extends_2D_refl : core.

Lemma extends_2D_trans : forall {Σ1 Σ2 Σ3 : senv}, Σ2 ⊇₂ Σ1 -> Σ3 ⊇₂ Σ2 -> Σ3 ⊇₂ Σ1.
  intros. unfold extends_2D in *. intros. eapply H in H1. destruct H1 as [c1 [H1 H2]]. apply H0 in H1. destruct H1 as [c2 [H1 H3]]. exists c2. split; auto. eapply extends_trans; eauto.
Qed.
#[global] Hint Resolve extends_2D_trans : core.

Lemma extends_2D_empty : forall {l}, l ⊇₂ [].
  intros. unfold extends_2D; intros. inversion H.
Qed.

Lemma extends_2D_cons : forall{l : senv}, forall{a}, (a :: l) ⊇₂ l.
  intros. unfold extends_2D. intros. exists c. rewrite indexr_skip. auto. apply (indexr_var_some') in H. lia.
Qed.
#[global] Hint Resolve extends_2D_cons : core.

Lemma extends_2D_length : forall{l1 l2 : senv}, l1 ⊇₂ l2 -> length l2 <= length l1.
  intros. unfold extends_2D in H. cut (‖ l1 ‖ >= ‖ l2 ‖). intros; lia. eapply indexr_exists_length; intros. specialize (indexr_some_exists l2 x H0). intros. destruct H1 as [c H1]. specialize (H x c H1). destruct H as [c' [H H']]. exists c'; auto.
Qed.
#[global] Hint Resolve extends_2D_length : core.

Lemma sinsert_extends_2D : forall {Σ A}, forall l, l < ‖ Σ ‖ ->
  sinsert Σ l A ⊇₂ Σ.
Proof.
  induction Σ; intros; simpl. auto.
  bdestruct (l =? ‖Σ‖); subst. apply extends_2D_app1; auto. apply extends_2D_app2; auto. apply (sinsert_length Σ l A); auto.
Qed.


Lemma extends_2D_sindexr : forall {Σ' Σ : senv}, Σ' ⊇₂ Σ -> forall l o T q, sindexr l o Σ = Some (T, q) -> sindexr l o Σ' = Some (T, q).
Proof.
  unfold extends_2D.
  intros. apply sindexr_var_some' in H0 as H0'. destruct H0' as [H1 [c [H2 H3]]]. specialize (H l c H2). destruct H as [c' [H4 H5]].
    erewrite sindexr_indexr_rewrite. 2: eauto. unfold extends in H5. destruct H5. subst. erewrite sindexr_indexr_rewrite in H0. 2: eauto. rewrite indexr_skips; auto.
Qed.


Lemma extends_2D_qdom : forall {Σ' Σ : senv}, Σ' ⊇₂ Σ -> qdom Σ ⊑↑ qdom Σ'.
intros. apply extends_2D_length in H. Qcrush. rewrite N_lift_dom in *. unfold N_dom in *. lia.
Qed.