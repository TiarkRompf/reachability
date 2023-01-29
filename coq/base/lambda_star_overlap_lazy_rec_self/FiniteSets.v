(** A library for finite sets with extensional equality.

    Author: Brian Aydemir. *)

Require Import FSets.
Require Import ListFacts.
Require Import Coq.Logic.ProofIrrelevance.


(* *********************************************************************** *)
(** * Interface *)

(** The following interface wraps the standard library's finite set
    interface with an additional property: extensional equality. *)

Module Type S.

  Declare Module E : UsualOrderedType.
  Declare Module F : FSetInterface.S with Module E := E.

  Parameter eq_if_Equal :
    forall s s' : F.t, F.Equal s s' -> s = s'.

End S.


(* *********************************************************************** *)
(** * Implementation *)

(** For documentation purposes, we hide the implementation of a
    functor implementing the above interface.  We note only that the
    implementation here assumes (as an axiom) that proof irrelevance
    holds. *)

Module Make (X : UsualOrderedType) <: S with Module E := X.

  (* begin hide *)

  Module E := X.
  Module F := FSetList.Make E.
  Module OFacts := OrderedType.OrderedTypeFacts E.

  Lemma eq_if_Equal :
    forall s s' : F.t, F.Equal s s' -> s = s'.
  Proof.
    intros [s1 pf1] [s2 pf2] Eq.
    assert (s1 = s2).
      unfold F.MSet.Raw.t in *.
      eapply Sort_InA_eq_ext; eauto with *.
      intros; eapply E.lt_trans; eauto with *.
      1 : {
        apply F.MSet.Raw.isok_iff.
        auto.
      }
      1 : {
        apply F.MSet.Raw.isok_iff.
        auto.
      }
    subst s1.
    assert (pf1 = pf2).
    apply proof_irrelevance.
    subst pf2.
    reflexivity.
  Qed.

  (* end hide *)

End Make.
