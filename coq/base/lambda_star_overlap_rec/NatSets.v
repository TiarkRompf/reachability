(* Instantiate FiniteSets with `nat` as members, adapted from  Boruch-Gruszecki et al.'s artifact *)

Require Import OrderedTypeEx.
Require Import OrderedType.
Require Import FSetFacts.
Require Import FiniteSets.
Require Import FSetDecide.
Require Import FSetNotin.

Module Type NATSET.
  Declare Module OT : UsualOrderedType with Definition t := nat.
  Parameter eq_nat_dec : forall x y : nat, {x = y} + {x <> y}.
End NATSET.

Module NatSetImpl : NATSET.
  Module OT := Nat_as_OT.
  Module Facts := OrderedTypeFacts OT.
  Definition eq_nat_dec : forall x y : nat, {x = y} + {x <> y} := Facts.eq_dec.
End NatSetImpl.

Module NatSet : FiniteSets.S with Module E := NatSetImpl.OT :=
  FiniteSets.Make NatSetImpl.OT.

Notation nats := NatSet.F.t.
Notation "{}N" := NatSet.F.empty.

Module NatSetDecide := FSetDecide.Decide NatSet.F.
Module NatSetNotin  := FSetNotin.Notin   NatSet.F.
Module NatSetFacts  := FSetFacts.Facts NatSet.F.
Module NatSetProperties := FSetProperties.Properties NatSet.F.

Ltac fnsetdec := try apply NatSet.eq_if_Equal; NatSetDecide.fsetdec.
