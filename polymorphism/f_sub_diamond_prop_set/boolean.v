Require Import Coq.Bool.Bool.
Require Import Coq.Program.Equality.
Require Import Coq.Logic.PropExtensionality.

#[global] Hint Resolve orb_prop_intro orb_prop_elim andb_prop_intro andb_prop_elim negb_prop_intro negb_prop_elim: core.

Lemma and_prop_l : forall b1 b2, Is_true (b1 && b2) -> Is_true b1.
intros. apply andb_prop_elim in H. intuition.
Qed.

Lemma and_prop_r : forall b1 b2, Is_true (b1 && b2) -> Is_true b2.
intros. apply andb_prop_elim in H. intuition.
Qed.

Lemma negb_prop : forall b1, Is_true (negb b1) -> Is_true b1 -> False.
intros. apply negb_prop_elim in H. intuition.
Qed.

Lemma implb_prop_intro : forall a b,
  (Is_true a -> Is_true b) -> Is_true (implb a b).
intros. destruct a; intuition.
Qed.

Lemma implb_prop_elim : forall a b,
  Is_true (implb a b) -> Is_true a -> Is_true b.
intros. destruct a; intuition.
Qed.

Lemma is_true_lift : forall a b, Is_true a = Is_true b -> a = b.
intros. destruct a; destruct b; simpl in *; auto.
  - exfalso. rewrite <- H. apply I.
  - exfalso. rewrite H. apply I.
Qed.
Lemma is_true_lift' : forall a b, a = b -> Is_true a = Is_true b.
intros. subst. auto.
Qed.

Lemma Is_true_eq_false : forall a,
  ~Is_true a -> a = false.
intros. unfold Is_true,not in H. destruct a; auto. exfalso. auto. 
Qed.

Lemma Is_true_eq_false_left : forall a,
  a = false -> ~Is_true a.
intros. unfold Is_true. rewrite H. auto.
Qed.

Lemma Is_true_eq_false_right : forall a,
  false = a -> ~Is_true a.
intros. unfold Is_true. rewrite <- H. auto.
Qed.

#[global] Hint Resolve Is_true_eq_true Is_true_eq_left Is_true_eq_right Is_true_eq_false Is_true_eq_false_left Is_true_eq_false_right and_prop_l and_prop_r negb_prop implb_prop_intro implb_prop_elim : core.

Lemma is_true_reflect : forall {b}, reflect (Is_true b) b.
intros. destruct b; constructor; auto.
Qed.

Lemma is_true_lift_or : forall a b ,
  Is_true (a || b) = (Is_true a \/ Is_true b).
intros. apply propositional_extensionality. intuition.
Qed.

Lemma is_true_lift_and : forall a b ,
  Is_true (a && b) = (Is_true a /\ Is_true b).
intros. apply propositional_extensionality. intuition eauto.
Qed.

Lemma is_true_lift_not : forall a ,
  Is_true (negb a) = ~Is_true a.
intros. apply propositional_extensionality. intuition eauto.
Qed.

Lemma is_true_lift_implb : forall a b,
  Is_true (implb a b) = (Is_true a -> Is_true b).
intros. apply propositional_extensionality. intuition eauto.
Qed.

#[global] Hint Rewrite is_true_lift_or is_true_lift_and is_true_lift_not is_true_lift_implb : blift_rewrite.

Ltac blift := autorewrite with blift_rewrite in *.
