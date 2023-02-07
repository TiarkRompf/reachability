(* Full safety for STLC *)

(* based on stlc.v *)

(* 

Simply-typed lambda calculus, combined proof of termination and type 
soundness (using logical relations).

This version adds immutable references. The proof relies on a 
monotonically growing store. Since values in the store don't change, 
a separate store typing is not necessary (adding an assignment 
operator would require store typings).

There are no reachability qualifiers yet.

*)


Require Export Arith.EqNat.
Require Export Arith.Le.
Require Import Coq.Lists.List.
Require Import Psatz.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.Peano_dec.
Import ListNotations.

Require Import env.
Require Import tactics.

Module STLC.

Definition id := nat.  

Inductive ty : Type :=
  | TBool  : ty
  | TRef   : ty -> ty    
  | TFun   : ty -> ty -> ty
.

Inductive tm : Type :=
  | ttrue : tm
  | tfalse : tm
  | tvar : id -> tm
  | tref : tm -> tm
  | tget : tm -> tm
  (*| tput : tm -> tm -> tm  *)
  | tapp : tm -> tm -> tm (* f(x) *)
  | tabs : tm -> tm (* \f x.y *)
.

Inductive vl : Type :=
  | vbool : bool -> vl
  | vref  : id -> vl
  | vabs  : list vl -> tm -> vl
.

Definition venv := list vl.
Definition tenv := list ty.
Definition stor := list vl.
Definition stpe := list (vl -> Type).

#[global] Hint Unfold venv.
#[global] Hint Unfold tenv.
#[global] Hint Unfold stor.
#[global] Hint Unfold stpe.

Inductive has_type : tenv -> tm -> ty -> Prop :=
| t_true: forall env,
    has_type env ttrue TBool
| t_false: forall env,
    has_type env tfalse TBool
| t_var: forall x env T1,
    indexr x env = Some T1 ->
    has_type env (tvar x) T1
| t_ref: forall x env T1,
    has_type env x T1 ->
    has_type env (tref x) (TRef T1)
| t_app: forall env f x T1 T2,
    has_type env f (TFun T1 T2) ->
    has_type env x T1 ->
    has_type env (tapp f x) T2
| t_abs: forall env y T1 T2,
    has_type (T1::env) y T2 -> 
    has_type env (tabs y) (TFun T1 T2)
.


(*
None             means timeout
Some None        means stuck
Some (Some v))   means result v
*)

Fixpoint teval(n: nat)(M:stor)(env: venv)(t: tm){struct n}: stor * option (option vl) :=
  match n with
    | 0 => (M, None)
    | S n =>
      match t with
        | ttrue      => (M, Some (Some (vbool true)))
        | tfalse     => (M, Some (Some (vbool false)))
        | tvar x     => (M, Some (indexr x env))
        | tref ex    =>
          match teval n M env ex with
            | (M', None)           => (M', None)
            | (M', Some None)      => (M', Some None)
            | (M', Some (Some vx)) => (vx::M', Some (Some (vref (length M'))))
          end
        | tget ex    =>
          match teval n M env ex with
            | (M, None) => (M, None)
            | (M, Some None) => (M, Some None)
            | (M, Some (Some vx)) => (M, Some (Some vx))
          end
        | tabs y     => (M, Some (Some (vabs env y)))
        | tapp ef ex =>
          match teval n M env ef with
            | (M', None) => (M', None)
            | (M', Some None) => (M', Some None)
            | (M', Some (Some (vbool _))) => (M', Some None)
            | (M', Some (Some (vref _))) => (M', Some None)
            | (M', Some (Some (vabs env2 ey))) =>
              match teval n M' env ex with
                | (M'', None) => (M'', None)
                | (M'', Some None) => (M'', Some None)
                | (M'', Some (Some vx)) =>
                  teval n M'' (vx::env2) ey
              end
          end
      end
  end.


Definition tevaln M env e M' v :=
  exists nm,
  forall n,
    n > nm ->
    teval n M env e = (M', Some (Some v)).


Fixpoint val_type M v T : Prop :=
  match v, T with
  | vbool b, TBool =>
      True
  | vref l, TRef T =>
      exists vx,
      indexr l M = Some vx /\
        val_type M vx T
  | vabs G ty, TFun T1 T2 => 
      (forall M' M'' H tx vx,
          tevaln (M'++M) H tx (M''++M'++M) vx /\
            val_type (M''++M'++M) vx T1
          -> (* exp_type H tx vx T1 *)
            exists M''' vy,
              tevaln (M''++M'++M) (vx::G) ty (M'''++M''++M'++M) vy /\
                val_type (M'''++M''++M'++M) vy T2) (* exp_type (vx:env) ty vy T2 *)
  | _,_ =>
      False
end.

Definition exp_type M H t M' v T :=
  tevaln M H t (M'++M) v /\
    val_type (M'++M) v T.

Definition env_type M H G :=
  length H = length G /\
    forall x T,
      indexr x G = Some T ->
      exists v : vl,
        indexr x H = Some v /\
          val_type M v T.


Hint Constructors ty.
Hint Constructors tm.
Hint Constructors vl.


Hint Constructors has_type.

Hint Constructors option.
Hint Constructors list.

Import Coq.Arith.PeanoNat.



Lemma valt_store_extend: forall T M' M v,
  val_type M v T ->
  val_type (M'++M) v T.
Proof.
  intros T. induction T; intros; simpl; destruct v; simpl in H; eauto.
  - (* Ref*)
    destruct H as [v [HI HV]].
    apply indexr_extend with (H' := M') in HI; intuition.
    eexists. eauto.
  - (* Abs *)
    intros. specialize (H (M'0++M')).
    assert ((M'0 ++ M') ++ M = M'0 ++ M' ++ M). rewrite app_assoc. eauto.
    rewrite H2 in H.
    eapply H. eauto.
Qed.

Lemma envt_extend: forall M H G v T,
    env_type M H G ->
    val_type M v T ->
    env_type M (v::H) (T::G).
Proof.
  intros. destruct H0 as [L W]. 
  repeat split; auto.
  - simpl. eauto.
  - intros. simpl in *. rewrite <-L in *.
    bdestruct (x =? (length H)); intuition; subst.
    inversion H0. subst. exists v. intuition.
Qed.

Lemma envt_store_extend: forall M M' H G,
    env_type M H G ->
    env_type (M'++M) H G.
Proof.
  intros. destruct H0 as [L W].
  repeat split; auto.
  intros. simpl in *. specialize (W x T H0); intuition.
  destruct W as [v [IX VX]]; intuition.
  exists v; intuition. eapply valt_store_extend; eauto.
Qed.


(* if well-typed, then result is an actual value (not stuck and not a timeout),
   for large enough n *)

Theorem full_total_safety : forall e G T,
  has_type G e T -> forall M H, env_type M H G ->
  exists M' v, exp_type M H e M' v T.

Proof.
  intros ? ? ? W. 
  induction W; intros ? ? WFE.
  
  - (* Case "True". *) exists []. eexists. split. 
    exists 0. intros. destruct n. lia. simpl. eauto. simpl. eauto. 
  - (* Case "False". *) exists []. eexists. split.
    exists 0. intros. destruct n. lia. simpl. eauto. simpl. eauto. 

  - (* Case "Var". *)
    destruct WFE as [? WFE].
    destruct (WFE x T1 H) as [vx [? ?]].
    exists []. eexists.
    split. exists 0. intros. destruct n. lia. simpl. rewrite H2. reflexivity.
    eauto. 

  - (* Case "Ref" *)
    destruct (IHW M H WFE)  as [M1 [vx [IW1 HVX]]].
    exists (vx::M1). exists (vref (length (M1++M))). split.
    + destruct IW1 as [n1 IW1].
      exists (S n1).
      intros. destruct n. lia.
      simpl. rewrite IW1. eauto. lia.
    + simpl.
      bdestruct (length (M1++M) =? length (M1++M)); intuition.
      exists vx. split. eauto.
      assert (vx::M1++M = [vx]++(M1++M)). eauto.
      rewrite H1.
      eapply valt_store_extend. eauto.
    
  - (* Case "App". *)
    (* induction on both subexpressions: obtain vf, vx *)
    destruct (IHW1 M H WFE)  as [M1 [vf [IW1 HVF]]].
    assert (env_type (M1++M) H env) as WFE1. { eapply envt_store_extend. eauto. }
    destruct (IHW2 (M1++M) H WFE1) as [M2 [vx [IW2 HVX]]].
    (* vf is a function value: it can eval its body *)
    destruct vf; try solve [inversion HVF]. simpl in HVF.
    destruct (HVF [] M2 H x vx) as [M3 [vy [IW3 HVY]]]. eauto.
    (* assemble result *)
    (* exists v : vl, exp_type H (tapp f x) v T2 *)
    rewrite app_nil_l in *. 
    exists (M3++M2++M1). exists vy. split.
    + (* expression evaluates *)
      (* - initial fuel value *)
      destruct IW1 as [n1 IW1].
      destruct IW2 as [n2 IW2].
      destruct IW3 as [n3 IW3].
      exists (S (n1+n2+n3)).
      (* - forall greater fuel *)
      intros. destruct n. lia.
      (* - result computes *)
      simpl. rewrite IW1. rewrite IW2. rewrite IW3.
      repeat rewrite app_assoc. eauto.
      lia. lia. lia.
    + (* result well typed *)
      repeat rewrite app_assoc in *. eapply HVY. 

  - (* Case "Abs". *)
    exists []. exists (vabs H y). split.
    + (* term evaluates *)
      exists 0. intros. destruct n. lia. simpl. eauto.
    + (* result well typed *)
      simpl. intros ? ? ? ? ? HVX. 
      eapply IHW. rewrite app_assoc in *.
      eapply envt_extend. eapply envt_store_extend. eapply WFE.
      eapply HVX.
      
Qed.


End STLC.
