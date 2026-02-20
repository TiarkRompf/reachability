Require Export Arith.EqNat.
Require Export PeanoNat.
Require Import Coq.Arith.Arith.
Require Import Coq.Program.Equality.
Require Import Coq.Lists.List.
Require Import Psatz. (* for lia *)
Require Import Coq.Arith.Compare_dec.
Import ListNotations.

Require Import tactics.
Require Import vars.

(* Theory of envs as lists of deBruijn levels *)

(* update entry *)
Fixpoint update {A} (σ : list A) (l : nat) (v : A) : list A :=
  match σ with
  | [] => σ
  | a :: σ' =>
      if (Nat.eqb l (length σ')) then (v :: σ') else (a :: (update σ' l v ))
  end.

Fixpoint insert {A} (σ : list A) (l : nat) (v : A) : list A :=
  match σ with
  | [] => σ
  | a :: σ' =>
      if (Nat.eqb l (length σ')) then (a :: v :: σ') else (a :: (insert σ' l v ))
  end.

(* Look up a free variable (deBruijn level) in env   *)
Fixpoint indexr {X : Type} (n : nat) (l : list X) : option X :=
  match l with
    | [] => None
    | a :: l' =>
      if (Nat.eqb n (length l')) then Some a else indexr n l'
  end.

Lemma indexr_head : forall {A} {x : A} {xs}, indexr (length xs) (x :: xs) = Some x.
  intros. simpl. destruct (Nat.eqb (length xs) (length xs)) eqn:Heq. auto.
  apply Nat.eqb_neq in Heq. contradiction.
Qed.

Lemma indexr_length : forall {A B} {xs : list A} {ys : list B}, length xs = length ys -> forall {x}, indexr x xs = None <-> indexr x ys = None.
Proof.
  intros A B xs.
  induction xs; intros; destruct ys; split; simpl in *; intros; eauto; try lia.
  - inversion H. destruct (PeanoNat.Nat.eqb x (length xs)). discriminate.
    specialize (IHxs _ H2 x). destruct IHxs. auto.
  - inversion H. rewrite <- H2 in H0. destruct (PeanoNat.Nat.eqb x (length xs)). discriminate.
    specialize (IHxs _ H2 x). destruct IHxs. auto.
Qed.

Lemma indexr_skip : forall {A} {x : A} {xs : list A} {i}, i <> length xs -> indexr i (x :: xs) = indexr i xs.
Proof.
  intros.
  rewrite <- PeanoNat.Nat.eqb_neq in H. auto.
  simpl. rewrite H. reflexivity.
Qed.

Lemma indexr_skips : forall {A} {xs' xs : list A} {i}, i < length xs -> indexr i (xs' ++ xs) = indexr i xs.
  induction xs'; intros; intuition.
  replace ((a :: xs') ++ xs) with (a :: (xs' ++ xs)).
  rewrite indexr_skip. eauto. rewrite app_length. lia. auto.
Qed.

Lemma indexr_var_some :  forall {A} {xs : list A} {i}, (exists x, indexr i xs = Some x) <-> i < length xs.
Proof.
  induction xs; intros; split; intros. inversion H. inversion H0.
  inversion H. inversion H. simpl in H0. destruct (PeanoNat.Nat.eqb i (length xs)) eqn:Heq.
  apply Nat.eqb_eq in Heq. rewrite Heq. auto. inversion H.
  simpl in H. rewrite Heq in H. apply IHxs in H. simpl. lia.
  simpl. destruct (PeanoNat.Nat.eqb i (length xs)) eqn:Heq.
  exists a. reflexivity. apply Nat.eqb_neq in Heq. simpl in H.
  apply IHxs. lia.
Qed.

(* easier to use for assumptions without existential quantifier *)
Lemma indexr_var_some' :  forall {A} {xs : list A} {i x}, indexr i xs = Some x -> i < length xs.
Proof.
  intros. apply indexr_var_some. exists x. auto.
Qed.
Lemma indexr_var_same: forall {A}{xs' xs: list A}{i}{v X X' : A}, Nat.eqb i (length xs) = false ->
  indexr i (xs' ++ X :: xs) =  Some v -> indexr i (xs' ++ X' :: xs) =  Some v.
Proof. intros ? ? ? ? ? ? ? E H.  induction xs'.
  - simpl. rewrite E.  simpl in H. rewrite E in H. apply H.
  - simpl. rewrite app_length. simpl.
    destruct (Nat.eqb i  ((length xs')  + S (length xs))) eqn: E'.
      simpl in H. rewrite app_length in H. simpl in H. rewrite E' in H.
    rewrite H. reflexivity.
    simpl in H. rewrite app_length in H. simpl in H. rewrite E' in H.
    rewrite IHxs'. reflexivity. assumption.
  Qed.

Lemma indexr_var_none :  forall {A} {xs : list A} {i}, indexr i xs = None <-> i >= length xs.
Proof.
  induction xs; intros; split; intros.
  simpl in *. lia. auto.
  simpl in H.
  destruct (PeanoNat.Nat.eqb i (length xs)) eqn:Heq.
  discriminate. apply IHxs in H. apply Nat.eqb_neq in Heq. simpl. lia.
  assert (Hleq: i >= length xs). {
    simpl in H. lia.
  }
  apply IHxs in Hleq. rewrite <- Hleq.
  apply indexr_skip. simpl in H. lia.
Qed.

Lemma indexr_insert_ge : forall {A} {xs xs' : list A} {x} {y}, x >= (length xs') -> indexr x (xs ++ xs') = indexr (S x) (xs ++ y :: xs').
  induction xs; intros.
  - repeat rewrite app_nil_l. pose (H' := H).
    rewrite <- indexr_var_none in H'.
    rewrite H'. symmetry. apply indexr_var_none. simpl. lia.
  - replace ((a :: xs) ++ xs') with (a :: (xs ++ xs')); auto.
    replace ((a :: xs) ++ y :: xs') with (a :: (xs ++ y :: xs')); auto.
    simpl. replace (length (xs ++ y :: xs')) with (S (length (xs ++ xs'))).
    destruct (Nat.eqb x (length (xs ++ xs'))) eqn:Heq; auto.
    repeat rewrite app_length. simpl. lia.
Qed.

Lemma indexr_insert_lt : forall {A} {xs xs' : list A} {x} {y}, x < (length xs') -> indexr x (xs ++ xs') = indexr x (xs ++ y :: xs').
  intros.
  rewrite indexr_skips; auto.
  erewrite indexr_skips.
  erewrite indexr_skip. auto.
  lia. simpl. lia.
Qed.

Lemma indexr_insert:  forall {A} {xs xs' : list A} {y}, indexr (length xs') (xs ++ y :: xs') = Some y.
  intros. induction xs.
  - replace ([] ++ y :: xs') with (y :: xs'); auto. apply indexr_head.
  - simpl. rewrite IHxs. rewrite app_length. simpl.
    destruct (PeanoNat.Nat.eqb (length xs') (length xs + S (length xs'))) eqn:Heq; auto.
    apply Nat.eqb_eq in Heq. lia.
Qed.

Lemma indexr_extend : forall  {A} (H' H: list A) x (v:A),
    indexr x H = Some v <-> indexr x (H'++H) = Some v /\ x < length H. 
Proof.
    intros. split; intros; intuition; auto.
    apply indexr_var_some' in H0 as H0'.
    assert (Nat.eqb x (length H) = false) as E. eapply Nat.eqb_neq; eauto. lia.
    rewrite indexr_skips; auto.
    apply indexr_var_some' in H0. auto.
    rewrite <- H1. rewrite indexr_skips; auto.
 Qed.

Lemma indexr_extend1: forall {A} (H: list A) x v (vx: A),
    indexr x H = Some v <-> indexr x (vx::H) = Some v /\ x < length H. 
Proof. 
    intros. split; intros. 
    eapply indexr_extend with (H' := [vx]) in H0. intuition.
    erewrite indexr_extend with (H' := [vx]); eauto.
Qed.

Lemma indexr_at_index: forall {A}{xs xs': list A}{y}{i},
  Nat.eqb i (length(xs')) = true ->
  indexr i (xs ++ y :: xs') = Some y.
Proof.
  intros. apply Nat.eqb_eq in H. subst.
  induction xs.
  - simpl. rewrite Nat.eqb_refl. reflexivity.
  - simpl.
    rewrite app_length. simpl. rewrite <- plus_n_Sm. rewrite <- plus_Sn_m.
    replace (length xs' =? S (length xs) + length xs') with false.
    assumption. symmetry. rewrite Nat.eqb_neq. lia.
Qed.

Lemma indexr_hit: forall {A}(xs: list A){i}{x y}, indexr i (x :: xs) = Some y  -> i = length(xs) -> x = y.
  intros. unfold indexr in H.
  assert (Nat.eqb i (length xs) = true). eapply Nat.eqb_eq. eauto.
  rewrite H1 in H. inversion H. eauto.
Qed.

Lemma update_length : forall {A} {σ : list A} {l v}, length σ = length (update σ l v).
  induction σ; simpl; intuition.
  destruct (Nat.eqb l (length σ)) eqn:Heq; intuition.
  simpl. congruence.
Qed.

Lemma update_indexr_miss : forall {A} {σ : list A} {l v l'}, l <> l' ->  indexr l' (update σ l v) = indexr l' σ.
  induction σ; simpl; intuition.
  destruct (Nat.eqb l (length σ)) eqn:Hls; destruct (Nat.eqb l' (length σ)) eqn:Hl's.
  apply Nat.eqb_eq in Hls. apply Nat.eqb_eq in Hl's. rewrite <- Hl's in Hls. contradiction.
  simpl. rewrite Hl's. auto.
  simpl. rewrite <- update_length. rewrite Hl's. auto.
  simpl. rewrite <- update_length. rewrite Hl's. apply IHσ. auto.
Qed.

Lemma update_indexr_hit : forall {A} {σ : list A} {l v}, l < length σ -> indexr l (update σ l v) = Some v.
  induction σ; simpl; intuition.
  destruct (Nat.eqb l (length σ)) eqn:Hls.
  apply Nat.eqb_eq in Hls. rewrite Hls. apply indexr_head.
  simpl. rewrite <- update_length. rewrite Hls. apply Nat.eqb_neq in Hls.
  apply IHσ. lia.
Qed.

Lemma update_commute : forall {A} {σ : list A} {i j vi vj}, i <> j -> (update (update σ i vi) j vj) = (update (update σ j vj) i vi).
  induction σ; simpl; intuition.
  destruct (Nat.eqb i (length σ)) eqn:Heq.
  - assert (Heq' : Nat.eqb j (length σ) = false).
    apply Nat.eqb_eq in Heq. rewrite Nat.eqb_neq. lia.
    rewrite Heq'. simpl. rewrite Heq'. rewrite <- update_length.
    rewrite Heq. auto.
  - destruct (Nat.eqb j (length σ)) eqn:Heq'; simpl.
    all: repeat rewrite <- update_length.
    all: rewrite Heq. all: rewrite Heq'. auto.
    rewrite IHσ; auto.
Qed.

Lemma update_inv : forall {A} {l : list A} {i v}, i > length l -> update l i v = l.
Proof.
  induction l; intros; simpl; auto.
  bdestruct (i =? length l). simpl in H. lia.
  bdestruct (i <? length l). simpl in H. lia.
  assert (length l < i) by lia. f_equal. apply IHl. auto.
Qed.

Lemma indexr_skips' : forall {A} {xs xs' : list A} {i}, i >= length xs -> indexr i (xs' ++ xs) = indexr (i - length xs) xs'.
  induction xs; intros; intuition.
  - rewrite app_nil_r. simpl. rewrite Nat.sub_0_r. auto.
  - simpl in *. destruct i; try lia.
    rewrite <- indexr_insert_ge; try lia.
    rewrite IHxs. simpl. auto. lia.
Qed.

Fixpoint delete_nth (n : nat) {A} (l : list A) : list A :=
  match l with
  | nil       => nil
  | cons x xs => if (Nat.eqb n (length xs)) then xs else x :: (delete_nth n xs)
  end.


  
(* =============== lemmas for store ========== *)

Definition slength {A} (l : option (list A)) : nat :=
  match l with
  | None => 0
  | Some l' => length l'
  end.

(* update store entry *)
Definition update' {A} (s : option (list A)) (o : nat) (v : A) : option (list A) :=
  match s with
  | None => None
  | Some c => Some (update c o v)
  end.
  
Fixpoint supdate {A} (σ : list (option (list (A)))) (l : loc) (o : offset) (v : A) : list (option (list (A))) :=
  match σ with
  | [] => σ
  | a :: σ' =>
      if (Nat.eqb l (length σ')) then ( (update' a o v) :: σ') else (a :: (supdate σ' l o v ))
  end.

Definition insert' {A} (s : option (list A)) (v : A) : option (list A) :=
  match s with
  | None => None
  | Some c => Some (v :: c)
  end.

(* must insert at column *)
Fixpoint cinsert {A} (σ : list (option (list (A)))) (l : loc) (v : A) : list (option (list (A))) :=
  match σ with
  | [] => σ
  | a :: σ' =>
      if (Nat.eqb l (length σ')) then 
        insert' a v :: σ'
      else (a :: (cinsert σ' l v ))
  end.

(* Look up a free variable (deBruijn level) in env   *)
Fixpoint sindexr {X : Type} (l : loc) (o : offset) (σ : list (list X)) : option X :=
  match σ with
    | [] => None
    | a :: σ' =>
      if (Nat.eqb l (length σ')) then indexr o a else sindexr l o σ'
  end.

(* easier to use for assumptions without existential quantifier *)
Lemma sindexr_inv : forall {A} {σ : list (list A)} {l o x}, sindexr l o σ = Some x ->
  exists y, indexr l σ = Some y /\ indexr o y = Some x.
Proof.
  induction σ; intros; simpl. inversion H. simpl in H. destruct (l =? length σ). exists a; split; auto. eauto.
Qed.

Lemma sindexr_var_some' :  forall {A} {σ : list (list A)} {l o x}, sindexr l o σ = Some x -> (l < length σ) /\ (exists y, indexr l σ = Some y /\ (o < length y)).
Proof.
  intros. apply sindexr_inv in H as H'. destruct H'. destruct H0. split. apply indexr_var_some' in H0; auto. exists x0; auto. split; auto. apply indexr_var_some' in H1; auto.
Qed.

Lemma sindexr_head : forall {X} s (c : list X) o, sindexr (length s) o (c :: s) = indexr o c.
  simpl. intros. rewrite Nat.eqb_refl; auto.
Qed.

Lemma sindexr_skip : forall {A} {c : list A} {xs} {i} {o}, i <> length xs -> sindexr i o (c :: xs) = sindexr i o xs.
Proof.
  intros.
  rewrite <- PeanoNat.Nat.eqb_neq in H. auto.
  simpl. rewrite H. reflexivity.
Qed.

Lemma sindexr_skips : forall {A} {xs' xs : list (list A)} {i} {o}, i < length xs -> sindexr i o (xs' ++ xs) = sindexr i o xs.
  induction xs'; intros; intuition.
  replace ((a :: xs') ++ xs) with (a :: (xs' ++ xs)).
  rewrite sindexr_skip. eauto. rewrite app_length. lia. auto.
Qed.


Fixpoint sinsert {A} (s : list ((list (A)))) (l : loc) (x : A) : list (list (A)) :=
  match s with
  | [] => s
  | c :: s' =>
      if (Nat.eqb l (length s')) then 
        ((x :: c) :: s')
      else (c :: (sinsert s' l x ))
  end.

Lemma sinsert_length : forall {A} (s : list (list A)) l x, length (sinsert s l x) = length s.
Proof.
  induction s; intros; simpl; auto.
  bdestruct (l =?  length s ); simpl; auto.
Qed.

Lemma indexr_miss : forall {A} (s : list A) {x}, x > length s -> indexr x s = None.
Proof.
  induction s; intros; simpl; auto. simpl in H. bdestruct (x =? length s); try lia. apply IHs. lia.
Qed.

Lemma indexr_outrange : forall {A} {l : list A} {x}, x > length l -> indexr x l = None.
Proof. 
  induction l; simpl; intros; auto. bdestruct (x =? length l); auto; subst. lia. apply IHl. lia.
Qed.

Lemma indexr_some_exists : forall {A} (l : list A), forall x, x < length l -> exists t, indexr x l = Some t.
Proof.
  induction l; intros. inversion H. simpl in H. bdestruct (x =? length l); subst. exists a. apply indexr_head. rewrite indexr_skip; auto. apply IHl. lia.
Qed.


Lemma supdate_length : forall {A} {σ : list (option (list A))} {l o v}, length σ = length (supdate σ l o v).
  induction σ; simpl; intuition.
  destruct (Nat.eqb l (length σ)) eqn:Heq; intuition.
  simpl. congruence.
Qed.

Lemma supdate_indexr : forall {A} {σ : list (option (list A))} {l o v}, l < length σ -> indexr l (supdate σ l o v) = match (indexr l σ) with
                               | None => None
                               | Some c => Some (update' c o v)
                               end.
Proof.
  induction σ; simpl; intuition.
  destruct (Nat.eqb l (length σ)) eqn:Hls.
  apply Nat.eqb_eq in Hls. rewrite Hls. apply indexr_head.
  simpl. rewrite <- supdate_length. rewrite Hls. apply Nat.eqb_neq in Hls.
  apply IHσ. lia.
Qed.

Lemma supdate_indexr_miss : forall {A} {σ : list (option (list A))} {l o v l'}, l <> l' ->  indexr l' (supdate σ l o v) = indexr l' σ.
  induction σ; simpl; intuition.
  destruct (Nat.eqb l (length σ)) eqn:Hls; destruct (Nat.eqb l' (length σ)) eqn:Hl's.
  apply Nat.eqb_eq in Hls. apply Nat.eqb_eq in Hl's. rewrite <- Hl's in Hls. contradiction.
  simpl. rewrite Hl's. auto.
  simpl. rewrite <- supdate_length. rewrite Hl's. auto.
  simpl. rewrite <- supdate_length. rewrite Hl's. apply IHσ. auto.
Qed.


Lemma supdate_indexr_miss_l : forall {A} {σ : list (option (list A))} {l o v l0 c}, l <> l0 -> 
  indexr l (supdate σ l0 o v) = Some c -> indexr l σ = Some c.
Proof.
  induction σ; simpl; intuition.
  destruct (Nat.eqb l (length σ)) eqn:Hls.
  apply Nat.eqb_eq in Hls. bdestruct (l0 =? length σ ); try lia. subst. erewrite supdate_length in H0. rewrite indexr_head in H0; auto.
  simpl. apply Nat.eqb_neq in Hls. bdestruct (l0 =? length σ ); try lia; subst. rewrite indexr_skip in H0; auto. rewrite indexr_skip in H0; auto. eapply IHσ. 2: eauto. lia. rewrite <- supdate_length. lia.
Qed.


Lemma sinsert_indexr : forall {A} {Σ x v} {c : list A}, indexr x Σ = Some c ->
  indexr x (sinsert Σ x v) = Some (v :: c).
Proof.
  induction Σ; intros; simpl; auto. inversion H. destruct (x =? length Σ) eqn:Eqx; subst. 
  - apply Nat.eqb_eq in Eqx; subst. rewrite indexr_head in H; inversion H; subst. rewrite indexr_head; auto.
  - apply Nat.eqb_neq in Eqx; subst. rewrite indexr_skip in H; auto. rewrite indexr_skip. apply IHΣ; auto. rewrite sinsert_length; auto.
Qed.

Lemma sinsert_indexr_miss : forall {A} {Σ x x'} {v : A}, 
  x' <> x -> indexr x' (sinsert Σ x v) = indexr x' Σ.
Proof.
  induction Σ; intros; simpl. auto. destruct (x =? length Σ) eqn:Eqx; subst. 
  - apply Nat.eqb_eq in Eqx; subst. rewrite indexr_skip; auto. destruct (x' =? length Σ ) eqn:Eqx'. apply Nat.eqb_eq in Eqx'. lia. auto.
  - apply Nat.eqb_neq in Eqx; subst. destruct (x' =? length Σ) eqn:Eqx'. 
    apply Nat.eqb_eq in Eqx'; subst. erewrite <- sinsert_length. erewrite indexr_head; auto. 
    apply Nat.eqb_neq in Eqx'. rewrite indexr_skip. auto. rewrite sinsert_length; auto.
Qed.

Lemma sinsert_indexr' : forall {A} {Σ x v} {c : list A}, indexr x (sinsert Σ x v) = Some (c) ->
  exists c', indexr x Σ = Some c' /\ c = v :: c'.
Proof.
  intros. apply indexr_var_some' in H as H'. rewrite sinsert_length in H'. specialize (indexr_some_exists Σ x H'). intros. destruct H0.
  exists x0. split; auto. eapply (@sinsert_indexr _ _ _ v) in H0. rewrite H in H0. inversion H0; auto.
Qed. 


Lemma cinsert_length : forall {A} (c : list (option (list A))) l x, length (cinsert c l x) = length c.
Proof.
  induction c; intros; simpl; auto.
  bdestruct (l =?  length c ); simpl; auto.
Qed.


Lemma cinsert_indexr : forall {A} {σ} {x c} {v : A}, indexr x σ = Some (Some c) ->
  indexr x (cinsert σ x v) = Some ( Some (v :: c)).
Proof.
  induction σ; intros; simpl; auto. inversion H. destruct (x =? length σ) eqn:Eqx; subst. 
  - apply Nat.eqb_eq in Eqx; subst. rewrite indexr_head in H; inversion H; subst. rewrite indexr_head; auto.
  - apply Nat.eqb_neq in Eqx; subst. rewrite indexr_skip in H; auto. rewrite indexr_skip. apply IHσ; auto. rewrite cinsert_length; auto.
Qed.

Lemma cinsert_indexr_None : forall {A} {σ x} {v : A}, indexr x σ = Some (None) ->
  indexr x (cinsert σ x v) = Some (None).
Proof.
  induction σ; intros; simpl; auto. inversion H. destruct (x =? length σ) eqn:Eqx; subst. 
  - apply Nat.eqb_eq in Eqx; subst. rewrite indexr_head in H; inversion H; subst. rewrite indexr_head; auto.
  - apply Nat.eqb_neq in Eqx; subst. rewrite indexr_skip. rewrite H1. apply IHσ; auto. rewrite cinsert_length; auto.
Qed.

Lemma cinsert_indexr_miss : forall {A} {σ x x'} {v : A}, 
  x' <> x -> indexr x' (cinsert σ x v) = indexr x' σ.
Proof.
  induction σ; intros; simpl. auto. destruct (x =? length σ) eqn:Eqx; subst. 
  - apply Nat.eqb_eq in Eqx; subst. rewrite indexr_skip; auto. destruct (x' =? length σ ) eqn:Eqx'. apply Nat.eqb_eq in Eqx'. lia. auto.
  - apply Nat.eqb_neq in Eqx; subst. destruct (x' =? length σ) eqn:Eqx'. 
    apply Nat.eqb_eq in Eqx'; subst. erewrite <- cinsert_length. erewrite indexr_head; auto. 
    apply Nat.eqb_neq in Eqx'. rewrite indexr_skip. auto. rewrite cinsert_length; auto.
Qed.

Lemma cinsert_indexr' : forall {A} {σ x c} {v : A}, indexr x (cinsert σ x v) = Some (Some (c)) ->
  exists c', indexr x σ = Some (Some c') /\ c = v :: c'.
Proof.
  intros. apply indexr_var_some' in H as H'. rewrite cinsert_length in H'. specialize (indexr_some_exists σ x H'). intros. destruct H0. destruct x0.
  exists l. split; auto. eapply (@cinsert_indexr _ _ _ _ v) in H0. rewrite H in H0. inversion H0; auto.
  eapply (@cinsert_indexr_None _ _ _ v) in H0. rewrite H in H0. inversion H0.
Qed. 

