(* Full safety for STLC *)

(*

Simply-typed lambda calculus, combined proof of termination and type
soundness (using logical relations).

*)

Require Export Arith.EqNat.
Require Export Arith.Le.
Require Import Coq.Lists.List.
Require Import Psatz.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Arith.PeanoNat.

Require Import env.
Require Import tactics.

Import ListNotations.

Module STLC.

Definition id := nat.

Inductive ty : Type :=
  | TBool  : ty
  | TFun   : ty -> ty -> ty
.

Inductive tm : Type :=
  | ttrue : tm
  | tfalse : tm
  | tvar : id -> tm
  | tapp : tm -> tm -> tm (* f(x) *)
  | tabs : tm -> tm (* \f x.y *)
.

Inductive vl : Type :=
| vbool : bool -> vl
| vabs  : list vl -> tm -> vl
.

Definition venv := list vl.
Definition tenv := list ty.

#[global] Hint Unfold venv.
#[global] Hint Unfold tenv.


Inductive has_type : tenv -> tm -> ty -> Prop :=
| t_true: forall env,
           has_type env ttrue TBool
| t_false: forall env,
           has_type env tfalse TBool
| t_var: forall x env T1,
           indexr x env = Some T1 ->
           has_type env (tvar x) T1
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

Fixpoint teval(n: nat)(env: venv)(t: tm){struct n}: option (option vl) :=
  match n with
    | 0 => None
    | S n =>
      match t with
        | ttrue      => Some (Some (vbool true))
        | tfalse     => Some (Some (vbool false))
        | tvar x     => Some (indexr x env)
        | tabs y     => Some (Some (vabs env y))
        | tapp ef ex   =>
          match teval n env ef with
            | None => None
            | Some None => Some None
            | Some (Some (vbool _)) => Some None
            | Some (Some (vabs env2 ey)) =>
              match teval n env ex with
                | None => None
                | Some None => Some None
                | Some (Some vx) =>
                  teval n (vx::env2) ey
              end
          end
      end
  end.


Definition tevaln env e v := exists nm, forall n, n > nm -> teval n env e = Some (Some v).


(* need to use Fixpoint because of positivity restriction *)
Fixpoint val_type v T : Prop := match v, T with
| vbool b, TBool => True
| vabs G ty, TFun T1 T2 => 
  (forall H tx vx, tevaln H tx vx /\ val_type vx T1 -> (* exp_type H tx vx T1 *)
     exists vy, tevaln (vx::G) ty vy /\ val_type vy T2) (* exp_type (vx:env) ty vy T2 *)
| _,_ => False
end.

Definition exp_type H t v T := tevaln H t v /\ val_type v T.

Definition env_type H G :=
  length H = length G /\
 forall x T1, indexr x G = Some T1 ->
   exists v : vl, exp_type H (tvar x) v T1.


#[global] Hint Constructors ty.
#[global] Hint Constructors tm.
#[global] Hint Constructors vl.


#[global] Hint Constructors has_type.
(* Hint Constructors val_type. *)

#[global] Hint Constructors option.
#[global] Hint Constructors list.
  
Lemma expt_extend: forall H x v vx T,
    exp_type H (tvar x) v T ->
    exp_type (vx::H) (tvar x) v T.
Proof.
  intros.
  destruct H0. destruct H0. 
  split. exists x0. intros. specialize (H0 n H2). destruct n. lia. simpl in H0.
  simpl. inversion H0.
  bdestruct (x =? (length H)); intuition; subst.
  eapply indexr_var_some' in H4. lia.
  auto.
Qed.
  

Lemma envt_extend: forall H G v T,
    env_type H G ->
    val_type v T ->
    env_type (v::H) (T::G).
Proof.
  intros.
  destruct H0.
  split. simpl. eauto.
  intros. destruct (eq_nat_dec x (length G)).
  - (* last *)
    subst x. simpl in H3. unfold exp_type. simpl. exists v. split. exists 0. intros. destruct n. lia. simpl.
    rewrite H0. simpl.
    bdestruct ((length G) =? (length G)); intuition; subst.
    bdestruct ((length G) =? (length G)); intuition.
    inversion H3. subst. auto.
  - (* not last *)
    destruct (H2 x T1). simpl in H3.
    bdestruct (x =? (length G)); intuition.
    eexists. eapply expt_extend. eauto.
Qed.
  
  

(* if well-typed, then result is an actual value (not stuck and not a timeout),
   for large enough n *)

Theorem full_total_safety : forall e G T,
  has_type G e T -> forall H, env_type H G ->
  exists v, exp_type H e v T.

Proof.
  intros ? ? ? W. 
  induction W; intros ? WFE.
  
  - (* Case "True". *) eexists. split. 
    exists 0. intros. destruct n. lia. simpl. eauto. simpl. eauto. 
  - (* Case "False". *) eexists. split.
    exists 0. intros. destruct n. lia. simpl. eauto. simpl. eauto. 

  - (* Case "Var". *)
    eapply WFE. eauto.

  - (* Case "App". *)
    (* induction on both subexpressions: obtain vf, vx *)
    destruct (IHW1 H WFE) as [vf [IW1 HVF]].
    destruct (IHW2 H WFE) as [vx [IW2 HVX]].
    (* vf is a function value: it can eval its body *)
    destruct vf; try solve [inversion HVF]. simpl in HVF.
    destruct (HVF H x vx) as [vy [IW3 HVY]]. eauto.
    (* assemble result *)
    (* exists v : vl, exp_type H (tapp f x) v T2 *)
    exists vy. split.
    + (* expression evaluates *)
      (* - initial fuel value *)
      destruct IW1 as [n1 IW1].
      destruct IW2 as [n2 IW2].
      destruct IW3 as [n3 IW3].
      exists (S (n1+n2+n3)).
      (* - forall greater fuel *)
      intros. destruct n. lia.
      (* - result computes *)
      simpl. rewrite IW1. rewrite IW2. rewrite IW3. eauto.
      lia. lia. lia.
    + (* result well typed *)
      eapply HVY. 
    
  - (* Case "Abs". *)
    exists (vabs H y). split.
    + (* term evaluates *)
      exists 0. intros. destruct n. lia. simpl. eauto.
    + (* result well typed *)
      simpl. intros ? ? ? HVX. 
      eapply IHW.
      eapply envt_extend. eapply WFE. eapply HVX. 
Qed.

End STLC.



