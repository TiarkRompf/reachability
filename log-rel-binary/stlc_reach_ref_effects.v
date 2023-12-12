(* Full safety for STLC *)

(* based on stlc_reach.v and stlc_ref.v *)

(*
  WRITE OPERATION, BUT NO DEALLOCATION

  simpler model, no kill effects
 *)

(* 

Simply-typed lambda calculus, combined proof of termination and type 
soundness (using logical relations).

This version adds immutable references. The proof relies on a
monotonically growing store. Since values in the store don't change,
a separate store typing is not necessary (adding an assignment
operator would require store typings). Store entries are also
restricted to base types (TRef TBool) only.

This version adds reachability types. The type qualifiers are
modeled as functions that check set membership. Restrictions:
no argument overlap, no dependent app.

This version adds simple effects. Every dereference incurs
a use effect. Right now, there is no semantic interpretation
of effects, and hence no meaningful static checking.

*)



Require Import Coq.Lists.List.
Require Import Psatz.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import FunctionalExtensionality.
Require Import PropExtensionality.

Import ListNotations.

Require Import tactics.
Require Import env.
Require Import qualifiers.

Module STLC.

Definition id := nat.


Definition pl := nat -> Prop.

Definition pempty: pl := fun x => False.                            (* empty set *)

Definition pone (x:nat): pl := fun x' => x' = x.                    (* singleton set *)

Definition pand p1 p2 (x:nat) := p1 x /\ p2 x.                      (* intersection *)

Definition por p1 p2 (x:nat) := p1 x \/ p2 x.                       (* union *)

Definition pdom {X} (H: list X) := fun x' =>  x' < (length H).      (* domain of a list *)

Definition pnat n := fun x' =>  x' < n.                             (* smaller than n *)

Definition psub (p1 p2: pl): Prop := forall x:nat, p1 x -> p2 x.    (* subset inclusion *)

Definition plift (b: ql): pl := fun x => b x = true.                (* reflect nat->bool set *)


Inductive ty : Type :=
  | TBool  : ty
  | TRef   : ty -> ty
  | TFun   : ty -> (* qempty -> *) ty -> ql -> ql -> ty
.

Inductive tm : Type :=
  | ttrue : tm
  | tfalse : tm
  | tvar : id -> tm
  | tref : tm -> tm
  | tget : tm -> tm
  | tput : tm -> tm -> tm  
  | tapp : tm -> tm -> tm (* f(x) *)
  | tabs : ql -> tm -> tm (* \f x.t *)   (* XXX: record free vars *)
.


Inductive vl : Type :=
  | vbool : bool -> vl
  | vref  : id -> vl
  | vabs  : list vl -> ql -> tm -> vl    (* closure record  *)
                                         (* XX: record free vars *)
.

Definition venv := list vl.
Definition tenv := list ty.

Definition stor := list vl.


#[global] Hint Unfold venv.
#[global] Hint Unfold tenv.
#[global] Hint Unfold stor.


Definition closed_ql m q := (forall x, q x = true -> x < m).



Inductive closed_ty: nat -> ty -> Prop :=
| c_bool: forall m,
    closed_ty m TBool
| c_ref: forall m T,
    closed_ty m T ->
    closed_ty m (TRef T)
| c_fun: forall m T1 T2 q2 e2,
    closed_ty m T1 ->
    closed_ty m T2 ->   (* not dependent *)
    closed_ql m q2 ->
    closed_ql m e2 ->   
    closed_ty m (TFun T1 (* qempty *) T2 q2 e2)
.


(* assume no overlap *)
Inductive has_type : tenv -> tm -> ty -> ql -> ql -> ql -> Prop :=
| t_true: forall env p,
    has_type env ttrue TBool p qempty qempty    (* nothing reachable from a primitive *)
| t_false: forall env p,
    has_type env tfalse TBool p qempty qempty
| t_var: forall x env T  p,
    indexr x env = Some T ->
    (plift p) x ->                         (* x in phi *)
    has_type env (tvar x) T p (qone x) qempty  (* x can reach only itself (no overlap) *)
| t_ref: forall t env p q e,
    has_type env t TBool p q e ->
    has_type env (tref t) (TRef TBool) p q e
| t_get: forall t env p q e,
    has_type env t (TRef TBool) p q e ->
    has_type env (tget t) TBool p qempty (qor e q)
| t_put: forall t1 t2 env p q1 e1 q2 e2,
    has_type env t1 (TRef TBool) p q1 e1 ->
    has_type env t2 TBool p q2 e2 ->
    has_type env (tput t1 t2) TBool p qempty (qor e1 (qor e2 q1))
| t_app: forall env f t T1 T2 p qf q1 q2 ef e1 e2,
    has_type env f (TFun T1 (* qempty  *) T2 q2 e2) p qf ef ->  
    has_type env t T1 p q1 e1 ->
    psub (pand (plift qf) (plift q1)) pempty ->          (* no overlapping *)
    psub (plift q2) (plift p) ->
    psub (plift e2) (plift p) ->
    has_type env (tapp f t) T2 p (qor q2 q1) (qor ef (qor e1 e2))
| t_abs: forall env t T1 T2 p q2 qf e2,      (* assume argument is tracked *)
    has_type (T1::env) t T2 (qor (qand p qf) (qone (length env))) (qor q2 (qone (length env))) (qor e2 (qone (length env))) ->
    closed_ty (length env) T1 ->
    closed_ty (length env) T2 ->
    closed_ql (length env) q2 ->
    closed_ql (length env) qf ->
    closed_ql (length env) e2 ->
    has_type env (tabs (qand p qf) t) (TFun T1 T2 q2 e2) p qf qempty
| t_sub: forall env y T p q1 q2 e1 e2,
    has_type env y T p q1 e1 ->
    psub (plift q1) (plift q2) ->
    psub (plift q2) (pdom env)  ->
    psub (plift e1) (plift e2) ->
    psub (plift e2) (pdom env)  ->
    has_type env y T p q2 e2
.



(* NOTE: the definitions below could be defined as computable Fixpoint 
   but it would take some effort to convince Coq of termination. 
   Since we're recursing on vl, tm, and (list vl) simultaneously, 
   Coq would require these three types to be defined jointly to 
   recognize structural recursion across them. Other options would
   include custom size measures or a well-foundedness predicate.

   Since this is all rather cumbersome, and termination is evident
   as long as values can't be cyclic, we axiomatize the definition
   of rechability below, without proving termination. *)

Axiom val_locs : vl -> pl. (* set of store locs for given val *)

Definition var_locs E x l := exists vx, indexr x E = Some vx /\ val_locs vx l.

Definition vars_locs E q l := exists x, q x /\ var_locs E x l.


Axiom val_locs_bool: forall b,
    val_locs (vbool b) = pempty.

Axiom val_locs_ref: forall x,    
    val_locs (vref x) = pone x. (* no deep store indirection for now *)

Axiom val_locs_abs: forall H p t,
    val_locs (vabs H p t) = vars_locs H (plift p).



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
            | (M', None) => (M', None)
            | (M', Some None) => (M', Some None)
            | (M', Some (Some (vbool _))) => (M', Some None)
            | (M', Some (Some (vabs _ _ _))) => (M', Some None)
            | (M', Some (Some (vref x))) => (M', Some (indexr x M'))
          end
        | tput er ex    =>
          match teval n M env er with
            | (M', None) => (M', None)
            | (M', Some None) => (M', Some None)
            | (M', Some (Some (vbool _))) => (M', Some None)
            | (M', Some (Some (vabs _ _ _))) => (M', Some None)
            | (M', Some (Some (vref x))) =>
              match teval n M' env ex with
                | (M'', None) => (M'', None)
                | (M'', Some None) => (M'', Some None)
                | (M'', Some (Some vx)) =>
                    match indexr x M'' with
                    | Some v => (update M'' x vx, Some (Some (vbool true)))
                    | _ => (M'', Some None)
                    end
              end
          end
        | tabs p y     => (M, Some (Some (vabs env p y)))
        | tapp ef ex =>
          match teval n M env ef with
            | (M', None) => (M', None)
            | (M', Some None) => (M', Some None)
            | (M', Some (Some (vbool _))) => (M', Some None)
            | (M', Some (Some (vref _))) => (M', Some None)
            | (M', Some (Some (vabs env2 _ ey))) =>
              match teval n M' env ex with
                | (M'', None) => (M'', None)
                | (M'', Some None) => (M'', Some None)
                | (M'', Some (Some vx)) =>
                  teval n M'' (vx::env2) ey
              end
          end
      end
  end.

(* value interpretation of terms *)
Definition tevaln M env e M' v :=
  exists nm,
  forall n,
    n > nm ->
    teval n M env e = (M', Some (Some v)).


(* store typings / "worlds" *)

(* consists of:

    - length of S1
    - length of S2
    - binary relation between locations that
      are supposed to be equivalent

   we enforce that this relation is a partial bijection
*)

Definition stty: Type := (nat * nat * (nat -> nat -> Prop)).

Definition length1 (M: stty) := fst (fst M).
Definition length2 (M: stty) := snd (fst M).
Definition strel (M: stty) := snd M.

Definition store_type (S1 S2: stor) (M: stty) := 
  length S1 = length1 M /\
  length S2 = length2 M /\
    (forall l1 l2 ,
      strel M l1 l2 ->
      exists b1 b2, 
      indexr l1 S1 = Some (vbool b1) /\
      indexr l2 S2 = Some (vbool b2) /\
      b1 = b2) /\
    (* enforce that strel is a partial bijection *)
    (forall l1 l2 l2',
        strel M l1 l2 ->
        strel M l1 l2' ->
        l2 = l2') /\
    (forall l1 l1' l2,
        strel M l1 l2 ->
        strel M l1' l2 ->
        l1 = l1').


(* store typing/world extension -- monotonic *)

Definition stapp M1 M2: stty :=
  (length1 M1 + length1 M2,
   length2 M1 + length2 M2,
   fun l1 l2 => strel M1 l1 l2 \/ strel M2 l1 l2).

#[global] Hint Unfold length1.
#[global] Hint Unfold length2.
#[global] Hint Unfold stapp.

Lemma stapp_assoc: forall M1 M2 M3,
    stapp M1 (stapp M2 M3) = stapp (stapp M1 M2) M3.
Proof.
  intros. unfold stapp, length1, length2, strel. simpl.
  replace (fst (fst M1) + (fst (fst M2) + fst (fst M3)))
    with (fst (fst M1) + fst (fst M2) + fst (fst M3)).
  replace (snd (fst M1) + (snd (fst M2) + snd (fst M3)))
    with (snd (fst M1) + snd (fst M2) + snd (fst M3)).
  replace (fun l1 l2 : nat => (snd M1 l1 l2 \/ snd M2 l1 l2) \/ snd M3 l1 l2)
    with (fun l1 l2 : nat => snd M1 l1 l2 \/ snd M2 l1 l2 \/ snd M3 l1 l2).
  reflexivity.
  eapply functional_extensionality. intros.
  eapply functional_extensionality. intros.
  eapply propositional_extensionality. intuition. 
  intuition. intuition.
Qed.
  
Lemma stapp_length1: forall M1 M2,
    length1 (stapp M1 M2) = length1 M1 + length1 M2.
Proof.
  intros. unfold stapp, length1. simpl. eauto. 
Qed.

Lemma stapp_length2: forall M1 M2,
  length2 (stapp M1 M2) = length2 M1 + length2 M2.
Proof.
  intros. unfold stapp, length2. simpl. eauto. 
Qed.



(* value interpretation of types *)

Fixpoint val_type (M:stty) (H1 H2:venv) v1 v2 T : Prop :=
  match v1, v2, T with
  | vbool b1, vbool b2, TBool =>
      b1 = b2
  | vref l1, vref l2, TRef T => 
      T = TBool /\
      l1 < length1 M /\ l2 < length2 M /\ strel M l1 l2
  | vabs G1 py1 ty1, vabs G2 py2 ty2, TFun T1 (* qempty *) T2 q2 e2 =>
        closed_ty (length H1) T1 /\
        closed_ty (length H1) T2 /\
        closed_ty (length H2) T1 /\
        closed_ty (length H2) T2 /\
        (psub (plift q2) (pdom H1)) /\
        (psub (plift q2) (pdom H2)) /\
        (psub (plift e2) (pdom H1)) /\
        (psub (plift e2) (pdom H2)) /\
        (psub (val_locs v1) (pnat (length1 M))) /\
        (psub (val_locs v2) (pnat (length2 M))) /\
        (forall S1' S2' M' vx1 vx2,
            store_type S1' S2' (stapp M' M)
            ->
            val_type
              (stapp M' M)
              H1
              H2
              vx1
              vx2
              T1
            ->
              psub (pand (val_locs v1) (val_locs vx1)) pempty ->
              psub (pand (val_locs v2) (val_locs vx2)) pempty
            ->
              exists S1'' S2'' M'' vy1 vy2,
                tevaln
                  S1'
                  (vx1::G1)
                  ty1
                  S1''
                  vy1
                /\
                tevaln
                  S2'
                  (vx2::G2)
                  ty2
                  S2''
                  vy2
                /\
                  store_type S1'' S2'' (stapp M'' (stapp M' M))
                /\
                  val_type
                    (stapp M'' (stapp M' M))
                    H1
                    H2
                    vy1 
                    vy2
                    T2
                /\
                   psub
                    (pand (pnat (length1 (stapp M' M))) (val_locs vy1))
                    (por (pand (vars_locs H1 (plift q2)) (val_locs v1)) (val_locs vx1))
                /\
                  psub
                    (pand (pnat (length2 (stapp M' M))) (val_locs vy2))
                    (por (pand (vars_locs H2 (plift q2)) (val_locs v2)) (val_locs vx2)))
  | _,_,_ =>
      False
  end.


Definition val_qual (N: nat) H v p (q: pl) :=
  psub (pand (pnat N) (val_locs v)) (vars_locs H (pand p q)).


Definition exp_type S1 S2 M H1 H2 t1 t2 S1' S2' M' v1 v2 T p q (e: pl) :=
  tevaln S1 H1 t1 S1' v1 /\
  tevaln S2 H2 t2 S2' v2 /\
    store_type S1' S2' (stapp M' M) /\
    val_type (stapp M' M) H1 H2 v1 v2 T /\
    val_qual (length1 M) H1 v1 p q /\
    val_qual (length2 M) H2 v2 p q.

(* what to do to check e ? restrict store? *)


Definition env_type M H1 H2 G p :=
  length H1 = length G /\
  length H2 = length G /\
    psub p (pdom H1) /\
    psub p (pdom H2) /\
    (forall x T,
        indexr x G = Some T ->
        p x ->
        exists v1 v2 : vl,
          indexr x H1 = Some v1 /\
          indexr x H2 = Some v2 /\
          val_type M H1 H2 v1 v2 T) /\
    (forall l x0 x1,
        p x0 ->
        var_locs H1 x0 l ->
        p x1 ->
        var_locs H1 x1 l ->
        x0 = x1) /\
    (forall l x0 x1,
        p x0 ->
        var_locs H2 x0 l ->
        p x1 ->
        var_locs H2 x1 l ->
        x0 = x1)  
.



Hint Constructors ty.
Hint Constructors tm.
Hint Constructors vl.


Hint Constructors has_type.

Hint Constructors option.
Hint Constructors list.


(* ---------- qualifier reflection & tactics  ---------- *)


Ltac unfoldq := unfold val_qual, psub, pnat, pdom, pand, por, pempty, pone, var_locs, vars_locs in *.
Ltac unfoldq1 := unfold qsub, qdom, qand, qempty, qone in *.

Lemma plift_empty: 
    plift (qempty) = pempty.
Proof.
  intros. unfoldq. unfold plift.
  eapply functional_extensionality. intros.
  eapply propositional_extensionality. 
  bdestruct (qempty x); intuition. 
  lia. Unshelve. apply 0.  
Qed.

Lemma plift_one: forall x,
    plift (qone x) = pone x.
Proof.
  intros. unfoldq. unfold plift.
  eapply functional_extensionality. intros.
  eapply propositional_extensionality. 
  bdestruct (qone x x0); intuition.
Qed.

Lemma plift_and: forall a b,
    plift (qand a b) = pand (plift a) (plift b).
Proof.
  intros. unfoldq. unfold plift.
  eapply functional_extensionality. intros.
  eapply propositional_extensionality. 
  bdestruct (qand a b x); intuition.
Qed.

Lemma plift_or: forall a b,
    plift (qor a b) = por (plift a) (plift b).
Proof.
  intros. unfoldq. unfold plift.
  eapply functional_extensionality. intros.
  eapply propositional_extensionality. 
  bdestruct (qor a b x); intuition.
Qed.





(* ---------- closedness lemmas  ---------- *)

Lemma closedq_extend : forall {m q}, closed_ql m q -> 
  forall {m'}, m <= m' -> closed_ql m' q.
Proof.  
    intros. unfold closed_ql in *. intros. 
    specialize (H x). intuition.
Qed.

Lemma closedty_extend : forall {m T}, closed_ty m T -> 
  forall {m'}, m <= m' -> closed_ty m' T.
Proof. 
    intros. induction T; constructor.
    all: inversion H; subst; intuition.
    eapply closedq_extend; eauto.
    eapply closedq_extend; eauto.
Qed.

Lemma vars_locs_extend: forall H H' q,
    psub q (pdom H) ->
    vars_locs (H' ++ H) q = 
      vars_locs H q.
Proof. 
  intros. apply functional_extensionality.
  intros. apply propositional_extensionality.
  unfoldq. unfoldq. intuition.
  - destruct H1. exists x0. intuition.
    destruct H3. exists x1. intuition.
    eapply indexr_extend; eauto.
  - destruct H1. exists x0. intuition.
    destruct H3. exists x1. intuition.
    eapply indexr_extend in H3. eapply H3.
Qed.



(* ---------- val_type lemmas  ---------- *)

Lemma valt_wf: forall T M H1 H2 v1 v2,
    val_type M H1 H2 v1 v2 T ->
    ( psub (val_locs v1) (pnat (length1 M)) /\
      psub (val_locs v2) (pnat (length2 M))).
Proof. 
  intros T. induction T; intros; destruct v1; destruct v2; simpl in *; intuition.
  + rewrite val_locs_bool. auto. unfoldq. intuition.
  + rewrite val_locs_bool. auto. unfoldq. intuition.
  + rewrite val_locs_ref. unfoldq. intuition.
  + rewrite val_locs_ref. unfoldq. intuition.
Qed.

Lemma valt_closed: forall T M H1 H2 v1 v2,
    val_type M H1 H2 v1 v2 T ->
    ( closed_ty (length H1) T /\
      closed_ty (length H2) T) .
Proof. 
  intros T. induction T; intros; destruct v1; destruct v2; simpl in *; intuition.
  + econstructor.
  + econstructor; eauto.
  + subst. econstructor; eauto. econstructor; eauto.
  + subst. econstructor; eauto. econstructor; eauto.
  + econstructor; eauto.
  + econstructor; eauto.
Qed.


Lemma valt_store_extend: forall T M' M H1 H2 v1 v2,
    val_type M H1 H2 v1 v2 T ->
    val_type (stapp M' M) H1 H2 v1 v2 T.
Proof.  
  intros T. induction T; intros; destruct v1; destruct v2; simpl in *; intuition.
  + unfold length1, stapp. simpl. lia.
  + unfold length2, stapp. simpl. lia.
(*  + assert (store_type S1 S2 (stapp (stapp M'0 M')M)) as A. rewrite <- stapp_assoc.  auto.
    destruct (H6 (stapp M'0 M') S1 S2  A) as [v1 [v2 [IS1 [IS2 VT]]]].
    exists v1, v2; intuition. rewrite stapp_assoc. auto.
*)
  + unfold length1, stapp. simpl. unfoldq. intuition. eapply H9 in H11. lia.
  + unfold length2, stapp. simpl. unfoldq. intuition. eapply H10 in H11. lia.
  + destruct (H12 S1' S2' (stapp M'0 M') vx1 vx2) as [S1'' [S2''[M'' [vy1 [vy2  [IEY1 [IEY2 [SEY [HVY [HSEP1 HSEP2]]]]]]]]]].
    rewrite <- stapp_assoc. auto.
    rewrite <- stapp_assoc. auto.
    auto.
    auto. 
    exists S1'', S2'', M'', vy1, vy2. intuition.
    repeat erewrite <- stapp_assoc in SEY; eauto.
    repeat erewrite <- stapp_assoc in HVY; eauto.
    repeat erewrite <- stapp_assoc in HSEP1; eauto.
    repeat erewrite <- stapp_assoc in HSEP2; eauto.
Qed. 

Lemma valt_extend: forall T M H1' H1 H2' H2 v1 v2,
    closed_ty (length H1) T ->
    closed_ty (length H2) T ->
    val_type M (H1'++H1) (H2'++H2) v1 v2 T <-> 
    val_type M H1 H2 v1 v2 T.
Proof. 
  intros T. induction T; split; intros; destruct v1; destruct v2; simpl in *; intuition.
  (* - destruct (H8 M' S1 S2 H7) as [v1 [v2 [IS1 [IS2 VT]]]].
    exists v1, v2; intuition. eapply IHT. inversion H.  auto. inversion H0. auto. eapply VT.
  - destruct (H8 M' S1 S2 H7) as [v1 [v2 [IS1 [IS2 VT]]]].
    exists v1, v2; intuition. eapply IHT. inversion H.  auto. inversion H0. auto. eapply VT.
  *)
  - inversion H. auto. 
  - inversion H. auto.
  - inversion H0. auto.
  - inversion H0. auto.
  - inversion H. auto.
  - inversion H0. auto.
  - inversion H. auto.
  - inversion H0. auto.
  - (* Abs shrink *)
    inversion H0. subst. inversion H. subst.
    destruct (H14 S1' S2' M' vx1 vx2) as [S1'' [S2'' [M'' [vy1 [vy2 [HEY HVY]]]]]].
      eauto. 
      eapply IHT1; eauto.
      eauto. 
    eauto.
    exists S1'', S2'', M'', vy1, vy2. intuition.
    eapply IHT2; eauto.
    rewrite vars_locs_extend in H21; eauto.
    rewrite vars_locs_extend in H31; eauto.
  - eapply closedty_extend. apply H4. auto.
  - eapply closedty_extend. apply H3. auto.
  - eapply closedty_extend; eauto. 
  - eapply closedty_extend; eauto.
  - unfoldq. rewrite app_length. intuition. eapply H7 in H13. lia.
  - unfoldq. rewrite app_length. intuition. eapply H8 in H13. lia.
  - unfoldq. rewrite app_length. intuition. eapply H9 in H13. lia.
  - unfoldq. rewrite app_length. intuition. eapply H10 in H13. lia.
  - (* Abs grow *)
    inversion H0. subst.
    destruct (H14 S1' S2' M' vx1 vx2) as [S1'' [S2'' [M'' [vy1 [vy2 [HEY [HVY]]]]]]].
      eauto.
      eapply IHT1; eauto.
      eauto.  eauto.
    exists S1'',S2'', M'', vy1, vy2. intuition.
    eapply IHT2; eauto.
    rewrite vars_locs_extend; eauto. 
    rewrite vars_locs_extend; eauto.
Qed.

Lemma valt_extend1: forall T M H1 H2 v1 v2 vx1 vx2,
    closed_ty (length H1) T ->
    closed_ty (length H2) T ->
    val_type M (vx1::H1)(vx2::H2) v1 v2 T <-> 
    val_type M H1 H2 v1 v2 T.
Proof.
  intros. 
  replace (vx1 :: H1)  with ([vx1]  ++ H1); auto.
  replace (vx2 :: H2)  with ([vx2]  ++ H2); auto.
  eapply valt_extend; eauto.
Qed.


(* ---------- val_qual lemmas  ---------- *)

Lemma valq_bool: forall M H b p q,
    val_qual M H (vbool b) p q.
Proof.
  intros. unfoldq. rewrite val_locs_bool. intuition.
Qed.


Lemma valq_fresh1: forall M M' H p q,
    val_qual (length1 M) H (vref (length1 (stapp M' M))) p q.
Proof.
  intros. unfoldq.
  (* valq: index out of range*)
  rewrite stapp_length1.
  rewrite val_locs_ref.
  intuition. unfoldq. lia.
Qed.

Lemma valq_fresh2: forall M M' H p q,
    val_qual (length2 M) H (vref (length2 (stapp M' M))) p q.
Proof.
  intros. unfoldq.
  (* valq: index out of range*)
  rewrite stapp_length2.
  rewrite val_locs_ref.
  intuition. unfoldq. lia.
Qed.


Lemma valq_abs: forall M H t p q,
    val_qual M H (vabs H (qand p q) t) (plift p) (plift q).
Proof.
  intros. unfoldq.
  rewrite val_locs_abs.
  rewrite plift_and.
  intuition. 
Qed.


Lemma valq_sub: forall M H v p q q',
    val_qual M H v p q ->
    psub q q' ->
    psub q' (pdom H) ->
    val_qual M H v p q'.
Proof.
  intros. unfoldq. intuition.
  destruct (H0 x). intuition.
  exists x0. intuition.
Qed.


(* ---------- environment lemmas  ---------- *)

Lemma wf_env_type: forall M H1 H2 G p, 
  env_type M H1 H2 G p -> 
  (length H1 = length G /\
   length H2 = length G /\  
   pdom H1 = pdom G /\ 
   pdom H2 = pdom G /\ 
   psub p (pdom H1) /\
   psub p (pdom H2)
   ).
Proof.
    intros. unfold env_type in H. intuition.
    unfold pdom. rewrite H0. auto.
    unfold pdom. rewrite H. auto.
Qed.

Lemma envt_tighten: forall M H1 H2 G p p',
    env_type M H1 H2 G p ->
    psub p' p ->
    env_type M H1 H2 G p'.
Proof.
  intros. destruct H as [L1 [L2 [P1 [P2 W]]]].
  repeat split; auto.
  - unfoldq. intuition.
  - unfoldq. intuition.
  - intros.
    destruct W as [W ?].
    destruct (W x T); eauto. 
  - intros.
    destruct W as [? [W1 W2]].
    eauto.
  - intros.
    destruct W as [? [W1 W2]].
    eauto.
Qed.

Lemma aux1: forall v H l,
  var_locs (v :: H) (length H) l ->
  val_locs v l.
Proof. 
  intros. 
  destruct H0 as [vx [IVX VALVX]].
  
  assert (indexr (length H) (v :: H) = Some v). {
    replace (v :: H) with ([] ++ v :: H) in IVX; auto.
    rewrite indexr_insert in IVX; eauto.
    inversion IVX. subst.
    replace (vx :: H) with ([] ++ vx :: H); auto.
    rewrite indexr_insert; eauto.
  }
  rewrite H0 in IVX. inversion IVX. subst.
  auto.
Qed.


Lemma var_locs_shrink: forall v H x l,
  var_locs (v::H) x l ->
  x < length H ->
  var_locs H x l.
Proof.
  intros. unfoldq. 
  destruct H0 as [vx [IVX VALVX]].
  exists vx. split.
  erewrite <- indexr_skip; eauto. lia.
  auto.
Qed.


Lemma envt_extend: forall M H1 H2 G v1 v2 T q p,
    env_type M H1 H2 G p ->
    closed_ty (length G) T ->
    closed_ql (length G) q ->
    val_type M H1 H2 v1 v2 T ->
    (* separation *)
    (forall x l, val_locs v1 l -> p x -> var_locs H1 x l -> False) ->
    (forall x l, val_locs v2 l -> p x -> var_locs H2 x l -> False) ->
    env_type M (v1::H1)(v2::H2) (T::G) (por p (pone (length G))).
Proof. 
  intros. apply wf_env_type in H as HH.
  assert (length H1 = length H2). intuition.
  destruct H as [L1 [L2 [P1 [P2 [W1 [W2 W3]]]]]]. 
  repeat split; auto.
  - simpl. eauto.
  - simpl. auto.
  - unfoldq. simpl. intuition.
  - unfoldq. simpl. intuition.
  - intros. simpl in *. 
    rewrite L1 in *. rewrite L2 in *.
    
    bdestruct (x =? (length G)); intuition; subst.
    + inversion H. subst. exists v1, v2. intuition.
      eapply valt_extend1; eauto.
      assert (length H1 = length G). { auto. }
      rewrite H9. auto.
      assert (length H2 = length G). { auto. }
      rewrite H9. auto.
    + destruct (W1 _ _ H) as [v1' [v2' ?]]; eauto.
      unfoldq. intuition.
      exists v1', v2'. intuition. eauto.
      eapply valt_extend1; eauto.
      1,2: eapply valt_closed with (H2 := H2); eauto.   
  - intros.
    inversion H; inversion H9.
    + eapply W2; eauto.
      eapply var_locs_shrink. eauto. eapply P1; eauto.
      eapply var_locs_shrink. eauto. eapply P1; eauto.
    + destruct (H5 x0 l); eauto.
      assert (x1 = length H1). unfoldq. intuition.
      subst x1. eapply aux1; eauto.
      eapply var_locs_shrink. eauto. eapply P1; eauto.
    + destruct (H5 x1 l); eauto.
      assert (x0 = length H1). unfoldq. intuition.
      subst x0. eapply aux1; eauto.
      eapply var_locs_shrink. eauto. eapply P1; eauto.
    + unfoldq. lia.
  - intros.
    inversion H; inversion H9.
    + eapply W3; eauto.
      eapply var_locs_shrink. eauto. eapply P2; eauto.
      eapply var_locs_shrink. eauto. eapply P2; eauto.
    + destruct (H6 x0 l); eauto.
      assert (x1 = length H2). unfoldq. intuition.
      subst x1. eapply aux1; eauto.
      eapply var_locs_shrink. eauto. eapply P2; eauto.
    + destruct (H6 x1 l); eauto.
      assert (x0 = length H2). unfoldq. intuition.
      subst x0. eapply aux1; eauto.
      eapply var_locs_shrink. eauto. eapply P2; eauto.
    + unfoldq. lia.
Qed.


Lemma envt_store_extend: forall M M' H1 H2 G p,
    env_type M H1 H2 G p ->
    env_type (stapp M' M) H1 H2 G p.
Proof.
  intros. destruct H as [L1 [L2 [P1 [P2 [W1 [W2 W3]]]]]]. 
  repeat split; auto. intros.
  destruct (W1 _ _  H H0) as [vx1 [vx2 [IH1 [IH2 HVX]]]]; intuition.
  exists vx1, vx2; intuition.
  eapply valt_store_extend in HVX; eauto.
Qed.


Lemma envt_extend_all: forall M M1 H1 H2 G vx1 vx2 T1 p q1 qf,
    env_type M H1 H2 G p ->
    val_type (stapp M1 M) H1 H2 vx1 vx2 T1 ->
    psub (pand (vars_locs H1 (pand p qf)) (val_locs vx1)) pempty ->
    psub (pand (vars_locs H2 (pand p qf)) (val_locs vx2)) pempty ->
    closed_ty (length G) T1 ->
    closed_ql (length G) q1 ->
    env_type (stapp M1 M)(vx1 :: H1)(vx2 :: H2) (T1 :: G) (por (pand p qf) (pone (length G))).
Proof.
  intros.

  eapply envt_extend.
  eapply envt_tighten.
  eapply envt_store_extend.
  eauto.
  unfoldq. intuition.
  eauto.
  eauto.
  eauto.

  (* now prove separation on the first *) 
  intros.

  unfoldq. unfoldq.
  eapply H3. intuition.
  exists x. intuition.
  destruct H9.
  exists x0. intuition. eauto.
  destruct H9.
  eauto.


  (* now prove separation on the second *) 
  intros.

  unfoldq. unfoldq.
  eapply H4. intuition.
  exists x. intuition.
  destruct H9.
  exists x0. intuition. eauto.
  destruct H9.
  eauto.
Qed.



Lemma env_type_store_wf: forall M H1 H2 G p q,
    env_type M H1 H2 G p ->
    psub q p ->
    ( psub (vars_locs H1 q) (pnat (length1 M)) /\ 
      psub (vars_locs H2 q) (pnat (length2 M))).
Proof.
  unfoldq; intuition;
  intros; destruct H as [L1 [L2 [P1 [P2 [W1 [W2 W3]]]]]]; intuition;
  unfoldq; intuition.
  (* 1st *)
  destruct H3 as [? [? ?]].
  assert (p x0). eapply H0. eauto.
  assert (x0 < length H1). eauto.

  assert (exists T, indexr x0 G = Some T) as TY. 
  eapply indexr_var_some. rewrite <-L1. eauto.
  destruct TY as [T ?].
  destruct H3 as [? [? ?]].
  destruct (W1 x0 T) as [vx1 [vx2 [IX1 [IX2 IV ]]]]. eauto. eauto.
  rewrite H3 in IX1. inversion IX1. subst x1.

  eapply valt_wf in IV.  intuition. eapply H8; eauto.

  (* 2st *)
  destruct H3 as [? [? ?]].
  assert (p x0). eapply H0. eauto.
  assert (x0 < length H2). eauto.

  assert (exists T, indexr x0 G = Some T) as TY. eapply indexr_var_some. rewrite <-L2. eauto. 
  destruct TY as [T ?].
  destruct H3 as [? [? ?]].
  destruct (W1 x0 T) as [vx1 [vx2 [IX1 [IX2 IV ]]]]. eauto. eauto.
  rewrite H3 in IX2. inversion IX2. subst x1.

  eapply valt_wf in IV. eapply IV; eauto.
Qed.



(* NOTE: it may seem good enough if either q or q' are subsets of
         the filter p, because that rules out any overlap outside
         of the filter.

         Not true: consider

         E = { a -> l, b -> l }
         p = a
         q = b

         (locs q) & (locs p) = { l }
         q & p = {}
*)

(* XXX see if we can make this more liberal XXX *)

Lemma vars_locs_dist_and1: forall M E1 E2 env p q q'
    (WFE: env_type M E1 E2 env p),
    psub q p ->
    psub q' p ->
    pand (vars_locs E1 q) (vars_locs E1 q') = vars_locs E1 (pand q q').    
Proof.
  intros. 
  eapply functional_extensionality.
  intros. eapply propositional_extensionality.
  destruct WFE as [L1 [L2 [P1 [P2 [W [SEP1 SEP2]]]]]].
  intuition.
  - destruct H1 as [[? [? ?]]  [? [? ?]]].
    assert (x0 = x1). eapply SEP1; eauto. subst x1.
    exists x0. unfoldq. intuition.
  - destruct H1 as [? [? [? [? ?]]]].
    unfoldq. intuition.
    exists x0. intuition. exists x1. intuition.
      
    exists x0. intuition. exists x1. intuition.
Qed.

Lemma vars_locs_dist_and2: forall M E1 E2 env p q q'
    (WFE: env_type M E1 E2 env p),
    psub q p ->
    psub q' p ->
    pand (vars_locs E2 q) (vars_locs E2 q') = vars_locs E2 (pand q q'). 
Proof. 
  intros. eapply functional_extensionality.
  intros. eapply propositional_extensionality.
  destruct WFE as [L1 [L2 [P1 [P2 [W [SEP1 SEP2]]]]]].
  intuition.
  - destruct H1 as [[? [? ?]]  [? [? ?]]].
    assert (x0 = x1). eapply SEP2; eauto. subst x1.
    exists x0. unfoldq. intuition.
  - destruct H1 as [? [? [? [? ?]]]].
    unfoldq. intuition.
    exists x0. intuition. exists x1. intuition.
      
    exists x0. intuition. exists x1. intuition.  
Qed.



Lemma separation: forall M M' H1 H2 G p vf1 vf2 vx1 vx2 qf q1
    (WFE: env_type M H1 H2 G p)
    (HQF1: val_qual (length1 M) H1 vf1 p qf)
    (HQF2: val_qual (length2 M) H2 vf2 p qf)
    (HQX1: val_qual (length1 (stapp M' M)) H1 vx1 p q1)
    (HQX2: val_qual (length2 (stapp M' M)) H2 vx2 p q1)
    (PVF1: psub (val_locs vf1) (pnat (length1 (stapp M' M))))
    (PVF2: psub (val_locs vf2) (pnat (length2 (stapp M' M))))
    (QSEP: psub (pand qf q1) pempty),
    (
    psub (pand (val_locs vf1) (val_locs vx1)) pempty /\
    psub (pand (val_locs vf2) (val_locs vx2)) pempty
    ).
Proof. 
  intros. unfoldq. intuition.
  intros. unfoldq. intuition.
  1,2: remember WFE as WFE1; clear HeqWFE1;
  destruct WFE as [L1 [L2 [P1 [P2 [W [SEP1 SEP2]]]]]].
  (* 1st *)
  + bdestruct (x <? length1 M).
  - destruct (HQF1 x). intuition.
    destruct (HQX1 x). rewrite stapp_length1. intuition.
    assert (x0 = x1). eapply SEP1; intuition; eauto.
    eapply QSEP. subst x0. intuition; eauto.
  - bdestruct (x <? length1 (stapp M' M)).
    -- destruct (HQX1 x). intuition.
      (* fresh loc in vf, also occurs in vx --> can't happen *)
      assert (psub (vars_locs H1 (pone x0)) (pnat (length1 M))) as L. {
        eapply env_type_store_wf with (H2 := H2). eauto. unfoldq. intuition. subst x1. eauto.
      }
      assert (x < length1 M). {
        eapply L. unfoldq. exists x0. intuition.
      }
      lia.
    -- (* fresh loc in vx, bigger than vf *)
      eapply PVF1 in H0. lia.
  
  (* 2nd *)
  + bdestruct (x <? length2 M).
  - destruct (HQF2 x). intuition.
    destruct (HQX2 x). rewrite stapp_length2. intuition.
    assert (x0 = x1). eapply SEP2; intuition; eauto.
    eapply QSEP. subst x0. intuition; eauto.
  - bdestruct (x <? length2 (stapp M' M)).
    -- destruct (HQX2 x). intuition.
      (* fresh loc in vf, also occurs in vx --> can't happen *)
      assert (psub (vars_locs H2 (pone x0)) (pnat (length2 M))) as L. {
        eapply env_type_store_wf with (H2 := H2). eauto. unfoldq. intuition. subst x1. eauto.
      }
      assert (x < length2 M). {
        eapply L. unfoldq. exists x0. intuition.
      }
      lia.
    -- (* fresh loc in vx, bigger than vf *)
      eapply PVF2 in H0. lia.
Qed.

(* ---------- store typing lemmas ---------- *)


Lemma storet_length: forall S1 S2 M,
    store_type S1 S2 M ->
    (length S1 = length1 M /\
     length S2 = length2 M).
Proof.
  intros. destruct H; intuition.
Qed.


Lemma storet_extend: forall S1 S2 M H1 H2 b1 b2,
    store_type S1 S2 M ->
    val_type M H1 H2 (vbool b1)(vbool b2) TBool ->
    store_type ((vbool b1) :: S1) ((vbool b2) :: S2)
      (stapp (1, 1, fun l1 l2 => l1 = length S1 /\ l2 = length S2) M).
Proof.
  intros.
  unfold store_type in *. intuition.
  unfold length1. simpl. eauto.
  unfold length2. simpl. eauto.
  unfold strel in H6. simpl in H6.
  destruct H6.
  - (* hit *)
    destruct H6. 
    exists b1, b2. subst l1 l2.
    rewrite indexr_head.
    rewrite indexr_head.
    simpl in H0. intuition.
  - (* miss *)
    edestruct H4 as [? [? [? [? ?]]]]; eauto.
    exists x, x0. subst.
    rewrite indexr_extend1 in H8; try lia.
    rewrite indexr_extend1 in H9; try lia. 
    intuition; eauto.
  - (* right unique *)
    simpl in H6, H8.
    destruct H6; destruct H8.
    + destruct H6, H8. congruence.
    + edestruct H4 as [? [? [? [? ?]]]]; eauto.
      rewrite indexr_extend in H9. lia. 
    + edestruct H4 as [? [? [? [? ?]]]]; eauto.
      rewrite indexr_extend in H9. lia.
    + eapply H5; eauto.
  - (* left unique *)
    simpl in H6, H8.
    destruct H6; destruct H8.
    + destruct H6, H8. congruence.
    + edestruct H4 as [? [? [? [? ?]]]]; eauto.
      rewrite indexr_extend in H10. lia. 
    + edestruct H4 as [? [? [? [? ?]]]]; eauto.
      rewrite indexr_extend in H10. lia.
    + eapply H7; eauto.
      Unshelve.
      eapply [].
      eapply [].
      eapply [].
      eapply [].
Qed.

Lemma storet_update: forall S1 S2 M H1 H2 i1 i2 b1 b2,
    store_type S1 S2 M ->
    val_type M H1 H2 (vref i1) (vref i2) (TRef TBool) ->
    val_type M H1 H2 (vbool b1) (vbool b2) TBool -> 
    store_type (update S1 i1 (vbool b1)) (update S2 i2 (vbool b2)) M.
Proof.
  intros. destruct H as [L1 [L2 [ST [U2 U1]]]].
  repeat split. 
  (* length *)
  rewrite <-update_length. eauto.
  rewrite <-update_length. eauto.
  (* lookup *) {
    intros l1 l2 RL.
    destruct H0 as [? [? [? RI]]].
    bdestruct (i1 =? l1).
    - subst. assert (i2 = l2). eapply U2; eauto. subst. 
      assert (b1 = b2). simpl in H3. auto. 
      exists b1, b2. subst.
      rewrite update_indexr_hit; intuition. 
      rewrite update_indexr_hit; intuition. 
    - assert (i2 <> l2). intros ?. subst. eapply H5. eapply U1; eauto.
      rewrite update_indexr_miss; intuition.
      rewrite update_indexr_miss; intuition.
  }
  (* right/left unique *)
  eauto. eauto. 
Qed.

Lemma strel_inv: forall M' M i i0,
  strel M i i0 \/ strel M' i i0 ->
  strel (stapp M' M) i i0.
Proof.
  intros. unfold strel in *. simpl. intuition.
Qed.

Lemma storety_app0: forall S1 S2 M,
  store_type S1 S2 M ->
  store_type S1 S2 (stapp (0, 0, fun _ _:nat => False) M).
Proof. 
  intros. unfold store_type in *. unfold stapp. simpl. intuition.
  eapply H2; eauto. eapply H4; eauto.
Qed.


(* compatibility lemmas *)

Lemma bi_vtrue: forall S1 S2 M H1 H2 p q,
  store_type S1 S2 M -> 
  exp_type S1 S2 M H1 H2 ttrue ttrue S1 S2 (0, 0, fun l1 l2 => False) (vbool true) (vbool true) TBool p q pempty.
Proof.   
  intros. remember H as H''. clear HeqH''.
  destruct H as [SL1 [SL2  [SP1 SP2]]]. 
  split.
  exists 0. intros. destruct n. lia. simpl. eauto.
  split.
  exists 0. intros. destruct n. lia. simpl. eauto.
  split.
  (* store_typing*)
  eapply storety_app0; eauto.

  simpl. repeat split.
  apply valq_bool. apply valq_bool.
Qed.

Lemma bi_vfalse: forall S1 S2 M H1 H2 p q,
  store_type S1 S2 M -> 
  exp_type S1 S2 M H1 H2 tfalse tfalse S1 S2 (0, 0, fun l1 l2 => False) (vbool false) (vbool false) TBool p q pempty.
Proof.   
  intros.  remember H as H''. clear HeqH''.
  destruct H as [SL1 [SL2  [SP1 SP2]]]. 
  split.
  exists 0. intros. destruct n. lia. simpl. eauto.
  split.
  exists 0. intros. destruct n. lia. simpl. eauto.
  split.
  (* store_typing*)
  eapply storety_app0; eauto.

  simpl. repeat split.
  apply valq_bool. apply valq_bool.
Qed.

Lemma bi_tref: forall e1 e2 M M' S1 S2 S1' S2' H1 H2 v1 v2 p q e,
  exp_type S1 S2 M H1 H2 e1 e2 S1' S2' M' v1 v2 TBool p q e ->
  exists S1'' S2'' M''  v1 v2,
  exp_type S1 S2 M H1 H2 (tref e1) (tref e2) S1'' S2''  M'' v1 v2 (TRef TBool) p q e.
Proof.
  intros. 
  destruct H as [IE1 [IE2 [ST [HV [HQ1 HQ2]]]]].
  remember ST as ST'. clear HeqST'.
  destruct ST as [SL1 [SL2 [SP3 [SP4 SP5]]]].
  remember HV as  HV'. clear HeqHV'.
  remember ((1, 1, fun l1 l2 => l1 = length S1' /\ l2 = length S2')) as vt.
  destruct v1; destruct v2; try solve [inversion HV].
  exists ((vbool b)::S1'), ((vbool b0)::S2'), (stapp vt M').
  exists (vref (length S1')), (vref (length S2')).

  split.

  (* 1st term *)
  destruct IE1 as [n1 IE1].
  exists (S n1). intros. destruct n. lia. simpl. rewrite IE1.  auto. lia.

  split.
  (* 2nd term *)
  destruct IE2 as [n2 IE2].
  exists (S n2). intros. destruct n. lia. simpl. rewrite IE2. auto. lia.
  
  split.
  (* store_typing *)
  subst vt. rewrite <- stapp_assoc.  eapply storet_extend. eauto.
  auto.
  
  split.
  (* result type *)
  subst vt.
  constructor;  intuition.
  rewrite SL1. intuition.
  rewrite SL2. intuition.
  simpl. left. left. unfold strel. simpl. auto.
  
  split.

  rewrite SL1. apply valq_fresh1.
  rewrite SL2. apply valq_fresh2.
  Unshelve. apply []. apply [].
Qed.

Lemma bi_tget: forall t1 t2 S1 S2 S1' S2' M M'  H1 H2 p q e v1 v2,
  exp_type S1 S2 M H1 H2 t1 t2 S1' S2' M' v1 v2 (TRef (TBool)) p q e ->
  exists S1'' S2'' M'' v3 v4,
  exp_type S1 S2 M H1 H2 (tget t1) (tget t2)  S1'' S2''  M'' v3 v4 TBool p pempty e.
Proof. 
  intros.  
  destruct H as [EV1 [EV2 [STH [HV [HQ1 HQ2]]]]].
  destruct v1; destruct v2; try solve [inversion HV]. simpl in HV.
  
  destruct HV as [HT [LS1 [LS2 VT]]].
  remember STH as STH'. clear HeqSTH'.
  destruct STH as [STL1 [STL2 [SP1 [SP2 SP3]]]].

  assert (strel (stapp M' M) i i0) as A. eapply strel_inv. intuition.
 
  destruct (SP1 i i0 A) as [b1 [b2 [IY1 [IY2 EQ]]]]. 
    
  exists S1', S2', (stapp (0, 0, (fun v1 v2 => False))  M'), (vbool b1), (vbool b2). 
  split. 2: split. 3: split. 4: split. 5: split.
  + destruct EV1 as [n1 IW1].
    exists (S n1). intros. destruct n. lia. simpl.
    rewrite IW1. rewrite IY1. eauto. lia.
  + destruct EV2 as [n1 IW2].
    exists (S n1). intros. destruct n. lia. simpl.
    rewrite IW2. rewrite IY2. eauto. lia.
  + rewrite <- stapp_assoc. eapply storety_app0; eauto.
  + subst b2.
    assert (store_type S1' S2' (stapp (0, 0, fun _ _ : nat => False) (stapp M' M))) as B.
    eapply storety_app0; auto.
    constructor; eauto.
    
  + eapply valq_bool.
  + eapply valq_bool.
Qed.    
 
Lemma bi_put: forall S1 S2 M H1 H2 t1 t2 S1' S2' M' M'' S1'' S2'' v1 v2 v3 v4 p q1 q2 e1 e2 t3 t4
 (E1: exp_type S1 S2 M H1 H2 t1 t2 S1' S2' M' v1 v2 (TRef TBool) p q1 e1)
 (E2: exp_type S1' S2' (stapp M' M) H1 H2 t3 t4 S1'' S2'' M'' v3 v4 TBool p q2 e2),
 exists S1''' S2''' M'' v5 v6,
 exp_type S1 S2 M H1 H2 (tput t1 t3) (tput t2 t4) S1''' S2'''  M'' v5 v6 TBool p pempty (por e1 (por e2 q1)).
Proof.
  intros. 
  destruct E1 as [IE1 [IE2 [ST [HV [HQ1 HQ2]]]]].
  destruct v1; destruct v2; try solve [inversion HV]. simpl in HV.
  destruct HV as [HT [LS1 [LS2 VT]]].
  remember ST as ST'. clear HeqST'.
  destruct ST as [STL1 [STL2 [SP1 [SP2 SP3]]]].

  destruct E2 as [IE3 [IE4 [ST2 [HV1 [HQ3 HQ4]]]]].
  destruct v3; destruct v4; try solve [inversion HV1]. simpl in HV1.
  subst b0.
  remember ST2 as ST2'. clear HeqST2'.
  destruct ST2 as [STL3 [STL4 [SP4 [SP5 SP6]]]].

  exists (update S1'' i (vbool b)), (update S2'' i0 (vbool b)).
  exists (stapp M'' M'), (vbool true), (vbool true).
  split. 2: split. 3: split.
  (* first one *)
  destruct IE1 as [n1 IE1].
  destruct IE3 as [n3 IE3].
  exists (S(n1 + n3)). intros. destruct n. intuition.
  simpl. rewrite IE1. rewrite IE3.
  assert (i < length S1''). 
  rewrite STL3. rewrite stapp_length1. lia.
  apply indexr_var_some in H0. destruct H0. rewrite H0. auto. lia. lia.

  
  destruct IE2 as [n2 IE2].
  destruct IE4 as [n4 IE4].
  exists (S(n2 + n4)). intros. destruct n. intuition.
  simpl. rewrite IE2. rewrite IE4. 
  assert (i0 < length S2''). 
  rewrite STL4. rewrite stapp_length2. lia.
  apply indexr_var_some in H0. destruct H0. rewrite H0. auto. lia. lia.

  
  (* store typing *)
  eapply storet_update; eauto. rewrite stapp_assoc in ST2'. auto.
  assert (val_type (stapp M' M) H1 H2 (vref i) (vref i0) (TRef TBool)).
  constructor; intuition.
  eapply strel_inv. intuition. 
  eapply strel_inv. intuition.
  eapply valt_store_extend in H. rewrite stapp_assoc in H. eapply H.
  constructor.
  
  
  split. 
  eapply valt_store_extend. constructor.
  split.
  eapply valq_bool. eapply valq_bool.
Qed.

Lemma bi_var: forall G M S1 S2 H1 H2 x T1 p
  (WFE: env_type M H1 H2 G p)
  (ST: store_type S1 S2 M),
  indexr x G = Some T1 ->
  p x ->
  exists v1 v2,
  exp_type S1 S2 M H1 H2 (tvar x) (tvar x) S1 S2 (0, 0, fun l1 l2 => False)  v1 v2 T1 p (pone x) pempty.
Proof.
  intros. 
  eapply WFE in H; auto. remember ST as ST'. clear HeqST'.
  destruct ST as [SL1 [SL2 [SP1 [SP2 SP3]]]]. 
  destruct H as [v1 [v2 [IX1 [IX2 VT]]]].
  exists v1, v2. 
  split.
  exists 0. intros. destruct n. lia. simpl. congruence.
  split.
  exists 0. intros. destruct n. lia. simpl. congruence.
  split.
  eapply storety_app0; eauto.
  split.
  eapply valt_store_extend. auto.
  split.
  
  unfoldq. unfoldq. intuition.  exists x. intuition.
  exists v1. intuition.
  unfoldq. unfoldq. intuition.  exists x. intuition.
  exists v2. intuition.
Qed.

Lemma bi_tapp: forall M M' M'' S1 S2 S1' S2' S1'' S2'' vf1 vf2 vx1 vx2 G H1 H2 ef1 ef2 ex1 ex2 T1 T2 p qf ef q1 q2 e1 e2
   (WFE: env_type M H1 H2 G p)
   (ST: store_type S1 S2 M)
   (IEF: exp_type S1 S2 M H1 H2 ef1 ef2 S1' S2' M' vf1 vf2 (TFun T1 T2 q2 e2) p qf ef)  
   (IEX: exp_type S1' S2' (stapp M' M) H1 H2 ex1 ex2 S1'' S2'' M'' vx1 vx2 T1 p q1 e1)  
   (QSEP: psub (pand qf q1) pempty)
   (Q2: psub (plift q2) p)
   (E2: psub (plift e2) p),
   exists S1''' S2''' M''' v5 v6,
   exp_type S1 S2 M H1 H2 (tapp ef1 ex1)(tapp ef2 ex2) S1''' S2''' M''' v5 v6 T2 p (por (plift q2) q1) (por ef (por e1 (plift e2))).
Proof.
  intros. 
  destruct IEF as [IEF1 [IEF2 [ST1 [HVF [HQF1 HQF2]]]]].
  destruct IEX as [IEX1 [IEX2 [ST2 [HV2 [HQX1 HQX2]]]]].

  destruct vf1; destruct vf2; try solve [inversion HVF]; simpl in HVF; intuition.
  rename H12 into HVF.
  specialize (HVF S1'' S2'' M''  vx1 vx2); intuition.
  
  assert ( psub (pand (val_locs (vabs l q t)) (val_locs vx1)) pempty  /\
      psub (pand (val_locs (vabs l0 q0 t0)) (val_locs vx2)) pempty ). { 
       eapply separation; eauto.
  }
  intuition.   
  destruct H12 as [S1'''[S2''' [M''' [r1 [r2 [IAPP1 [IAPP2 [IAPPST [IVALY [HQY1 HQY2]]]]]]]]]]. 
  exists S1''', S2'''.
  exists (stapp (stapp M''' M'') M'). 
  exists r1. exists r2.

  split.
  (* 1st function *)
  destruct IEF1 as [n1 IEF1].
  destruct IEX1 as [n2 IEX1].
  destruct IAPP1 as [n3 IAPP1].
  exists (S (n1+n2+n3)). 
  (* - forall greater fuel *)
  intros. destruct n. lia.
  (* - result computes *)
  simpl. rewrite IEF1. rewrite IEX1. rewrite IAPP1. auto. lia. lia. lia.
  
  split.
  (* 2nd function *)
  destruct IEF2 as [n1 IEF2].
  destruct IEX2 as [n2 IEX2].
  destruct IAPP2 as [n3 IAPP2].
  exists (S (n1+n2+n3)). 
  (* - forall greater fuel *)
  intros. destruct n. lia.
  (* - result computes *)
  simpl. rewrite IEF2. rewrite IEX2. rewrite IAPP2. auto. lia. lia. lia.
  
  split.
  (* store typing *)
  repeat rewrite <- stapp_assoc. auto.

  split.
  (* result type *)
  repeat rewrite <- stapp_assoc. auto.
  
  split.
  (* 1st qual *)
  assert (val_qual (length1 M) H1 r1 p (pand p (por (plift q2) q1))) as A. {
    remember (vabs l q t) as vf1.
    unfold val_qual.
    rewrite <-(vars_locs_dist_and1 M H1 H2 G p); eauto. 
    2: {unfoldq. intuition. }
    2: {unfoldq. intuition. }
     
    unfoldq. intros.
    destruct (HQY1 x). repeat rewrite stapp_length1. intuition. 
    - (* part of function *)
      destruct (HQF1 x). intuition.
      destruct H12. destruct H12.
      split.
      exists x0. intuition. unfoldq. intuition.
      exists x1. intuition. 
  - (* part of argument *)
    destruct (HQX1 x). repeat rewrite stapp_length1. intuition. split.
    exists x0. intuition.
    exists x0. intuition.
  }
  unfoldq. intuition.
  destruct (A x). intuition.
  exists x0. intuition.

  (* 2nd qual *)

  assert (val_qual (length2 M) H2 r2 p (pand p (por (plift q2) q1))) as B. {
    remember (vabs l0 q0 t0) as vf2.
    unfold val_qual.
    rewrite <-(vars_locs_dist_and2 M H1 H2 G p); eauto. 
  2: {unfoldq. intuition. }
  2: {unfoldq. intuition. }
 
  unfoldq. intros.
  destruct (HQY2 x). repeat rewrite stapp_length2. intuition.  simpl.
  - (* part of function *)
    destruct (HQF2 x). intuition.
    destruct H12. destruct H12.
    split.
    exists x0. intuition. unfoldq. intuition.
    exists x1. intuition. 
  - (* part of argument *)
    destruct (HQX2 x). repeat rewrite stapp_length2. intuition. split.
    exists x0. intuition.
    exists x0. intuition.
  }
  unfoldq. intuition.
  destruct (B x). intuition.
  exists x0. intuition.
Qed.


Lemma bi_tabs: forall H1 H2 S1 S2 M G t1 t2 T1 T2 p q2 qf e2
  (WFE: env_type M H1 H2 G (plift p))
  (ST: store_type S1 S2 M)
  (EXP:  forall S1' S2' M' vx1 vx2,
      val_type (stapp M' M) H1 H2 vx1 vx2 T1  ->
      psub (pand (vars_locs H1 (pand (plift p) (plift qf))) (val_locs vx1)) pempty ->
      psub (pand (vars_locs H2 (pand (plift p) (plift qf))) (val_locs vx2)) pempty  -> 
      env_type (stapp M' M) (vx1::H1) (vx2:: H2) (T1::G) (plift (qor (qand p qf)(qone (length G)))) ->
      store_type S1' S2' (stapp M' M) ->
      exists S1'' S2'' M'' v1 v2,
        exp_type S1' S2' (stapp M' M) (vx1:: H1) (vx2:: H2) t1 t2  S1'' S2'' M'' v1 v2 T2 (plift (qor (qand p qf)(qone  (length G)))) (plift (qor q2 (qone (length G)))) (plift (qor e2 (qone (length G)))))
  (T1CL: closed_ty (length G) T1)      
  (T2CL: closed_ty (length G) T2)
  (HQ2: (psub (plift q2) (pdom G)))
  (HE2: (psub (plift e2) (pdom G)))
  (HCLQF: closed_ql (length G) qf),
  exists S1'' S2'' M'' v1'' v2'',
  exp_type S1 S2 M H1 H2 (tabs (qand p qf) t1) (tabs (qand p qf) t2) S1'' S2'' M''  v1'' v2'' (TFun T1 T2 q2 e2) (plift p) (plift qf) pempty.
Proof. 
  intros. 
  apply wf_env_type in WFE as WFE'. 
  destruct WFE' as [L1 [L2 [PD1 [PD2 [P1 P2]]]]].
  remember ST as ST'. clear HeqST'.
  destruct ST as [SL1 [SL2 [SP1 [SP2 SP3]]]].
  rewrite plift_or in *. rewrite plift_and in *.
  exists S1, S2, (0, 0, (fun v1 v2 => False)).
  exists (vabs H1 (qand p qf) t1). exists (vabs H2 (qand p qf) t2).
  split.
  
  (* 1st *)
    exists 0.  intros. destruct n. lia. simpl. eauto.
  split.
   (* 2nd *)
    exists 0.  intros. destruct n. lia. simpl. eauto.
  split.
   (* store typing *)  
   eapply storety_app0; eauto.
   
   (* results *)
   repeat split. 
   rewrite L1. auto.
   rewrite L1. auto.
   rewrite L2. auto.
   rewrite L2. auto.
   rewrite PD1. auto.
   rewrite PD2. auto.
   rewrite PD1. auto.
   rewrite PD2. auto.
   rewrite val_locs_abs.
   rewrite stapp_length1. simpl.
   eapply env_type_store_wf. eauto.
   rewrite plift_and. unfoldq. intuition.
   rewrite val_locs_abs.
   rewrite stapp_length2. simpl. 
   eapply env_type_store_wf. eauto.
   rewrite plift_and. unfoldq. intuition.
   intros.
   
   
   repeat rewrite stapp_assoc in H0.
   rewrite val_locs_abs in H3. rewrite plift_and in H3.
   rewrite val_locs_abs in H4. rewrite plift_and in H4.
   assert (env_type
        (stapp
           (stapp M'
              (0, 0,
               fun _ _ : nat => False)) M)
        (vx1 :: H1) (vx2 :: H2) 
        (T1 :: G)
        (plift
           (qor (qand p qf)
              (qone (length G))))) as WFE'.
   rewrite plift_or. rewrite plift_and. rewrite plift_one.
   eapply envt_extend_all in WFE; eauto.
   
   destruct (EXP S1' S2' 
      (stapp M' (0, 0,fun _ _ : nat => False)) vx1 vx2 H0) as [S1'' [S2'' [M'' [vy1 [vy2 IEY]]]]]; intuition.
   rewrite plift_or, plift_and in WFE'. auto.
   rewrite <- stapp_assoc. auto.

   destruct IEY as [IEY1 [IEY2 [YST [IVY [IYQ1 IYQ2]]]]].
   
   exists S1'', S2'', M'', vy1, vy2. intuition.
   repeat rewrite stapp_assoc.
   repeat rewrite stapp_assoc in YST. auto.
   repeat rewrite stapp_assoc. 
   repeat rewrite stapp_assoc in IVY. auto.
   eapply valt_extend; eauto.
   rewrite L1. auto. rewrite L2. auto.
   replace (vx1::H1) with ([vx1]++H1) in IVY; auto.
   replace (vx2::H2) with ([vx2]++H2) in IVY; auto.
   eapply IVY.


   (* qual *)
     
  rewrite val_locs_abs in *. rename H0 into HVX;
  apply valt_wf in HVX; apply valt_wf in IVY.
   rewrite plift_or, plift_one, plift_and in *. 
   
  unfoldq. intuition.
  destruct (IYQ1 x). eauto. intuition. 
  rewrite <- stapp_assoc. auto.
  unfoldq. 
  destruct H8.  destruct H8. 
  bdestruct (x0 =? length H1).
  (* from arg *)
    right. destruct H11 as [? [? ?]]. subst x0. 
    rewrite indexr_head in H11. inversion H11. eauto.
  (* from func *)
    left. split.
    exists x0. intuition. 
    destruct H11 as [? [? ?]]. 
    rewrite indexr_skip in H11. exists x1. split; eauto. lia.
    exists x0. split.
    destruct H8; try lia. eapply H8.
    destruct H11 as [? [? ?]]. rewrite indexr_skip in H11; eauto.

   (* 2nd *)

  rewrite val_locs_abs in *. rename H0 into HVX;
  apply valt_wf in HVX; apply valt_wf in IVY.
   rewrite plift_or, plift_one, plift_and in *. 
  
  unfoldq. intuition.
  destruct (IYQ2 x). eauto. intuition. 
  rewrite <- stapp_assoc. auto.
  unfoldq.
  destruct H8. destruct H8.
  bdestruct (x0 =? length H2).
  (* from arg *)
    right. destruct H11 as [? [? ?]]. subst x0. 
    rewrite indexr_head in H11. inversion H11. eauto.
  (* from func *)
    left. split.
    exists x0. intuition. 
    destruct H11 as [? [? ?]]. 
    rewrite indexr_skip in H11. exists x1. split; eauto. lia.
    exists x0. split.
    destruct H8; try lia. eapply H8.
    destruct H11 as [? [? ?]]. rewrite indexr_skip in H11; eauto.

  eapply valq_abs; eauto.
  eapply valq_abs; eauto.
Qed.

Lemma bi_qsub: forall S1 S2 S1' S2' M H1 H2 t1 t2 M' T p q q' e e' v1 v2,  
  exp_type S1 S2 M H1 H2 t1 t2 S1' S2' M' v1 v2 T p q e ->
  psub q q' ->
  psub e e' ->
  psub q' (pdom H1)  ->
  psub q' (pdom H2)  ->
  psub e' (pdom H1)  ->
  psub e' (pdom H2)  ->
  exists S1'' S2'' M'' v1' v2',
  exp_type S1 S2 M H1 H2 t1 t2 S1'' S2'' M'' v1' v2' T p q' e'.
Proof.  
  intros.
  exists S1', S2', M', v1, v2.
  destruct H as [IE1 [IE2 [IST[IVAL [IQ1 IQ2]]]]]. 
  split. eauto. split. eauto.
  split. eauto. split. eauto.
  unfold val_qual in IQ1; intuition.
  eapply valq_sub; eauto.
  unfold val_qual in IQ2; intuition.
  eapply valq_sub; eauto.
Qed.



Theorem fundamental_property : forall t G T p q e
  (W: has_type G t T p q e),
  forall M H1 H2, env_type M H1 H2 G (plift p) ->
  forall S1 S2, store_type S1 S2 M ->
  exists S1' S2' M' v1 v2,
  exp_type S1 S2 M H1 H2 t t S1' S2' M' v1 v2 T (plift p) (plift q)  (plift e).
Proof.
  intros ? ?  ? ? ? ? ?.
  induction W; intros ? ? ? WFE ? ? ST.

  - (* Case "True". *)
    exists S1. exists S2. exists (0, 0, fun l1 l2 => False). 
    exists (vbool true), (vbool true).
    eapply bi_vtrue; auto.
  - (* Case "False". *)
    exists S1. exists S2. exists (0, 0, fun l1 l2 => False). 
    exists (vbool false), (vbool false).
    eapply bi_vfalse; auto.
  - (* Case "Var". *)
    exists S1. exists S2. exists (0, 0, fun l1 l2 => False).
    rewrite plift_one. rewrite plift_empty.
    eapply bi_var; eauto. 
  - (* Case "Ref". *)
    specialize (IHW M  H1 H2); intuition.
    destruct (H S1 S2 ST) as [S1' [S2' [M' [v1 [v2 IE]]]]].
    eapply bi_tref; eauto.
  - (* Case "Get". *)
    specialize (IHW M  H1 H2); intuition.
    destruct (H S1 S2 ST) as [S1' [S2' [M' [v1 [v2 IE]]]]].
    rewrite plift_empty. rewrite plift_or.
    eapply bi_tget; eauto.
  - (* Case "Put". *)
    specialize (IHW1 M H1 H2 WFE S1 S2 ST) as [S1' [S2' [M' [v1 [v2 IE]]]]].
    assert (env_type (stapp M' M) H1 H2 env (plift p)) as WFE1. eapply envt_store_extend; eauto.
    assert (store_type S1' S2' (stapp M' M)) as ST'.
    eapply IE. 
    specialize (IHW2 (stapp M' M) H1 H2 WFE1 S1' S2' ST') as [S1'' [S2'' [M'' [v3 [v4 IE2]]]]].
    repeat rewrite plift_or. rewrite plift_empty. 
    eapply bi_put; eauto.
  - (* Case tapp *)
    specialize (IHW1 M H2 H3 WFE S1 S2 ST) as [S1' [S2' [M' [v1 [v2 IE]]]]].
    assert (env_type (stapp M' M) H2 H3 env (plift p)) as WFE1. eapply envt_store_extend; eauto.
    assert (store_type S1' S2' (stapp M' M)) as ST'. 
    eapply IE. 
    specialize (IHW2 (stapp M' M) H2 H3 WFE1 S1' S2' ST') as [S1'' [S2'' [M'' [v3 [v4 IE2]]]]].
    repeat rewrite plift_or. 
    eapply bi_tapp; eauto.
  - (* Case tabs *)
    eapply bi_tabs; eauto.
  - (* Case qsub  *)
    specialize (IHW M H3 H4 WFE S1 S2 ST) as [S1' [S2' [M' [v1 [v2 IE]]]]].
    eapply bi_qsub; eauto. 
    all: apply wf_env_type in WFE; intuition.
    1,3: rewrite H6. 1,2: unfoldq; intuition.
    1,2: rewrite H8. 1,2: unfoldq; intuition.  
Qed.

Definition sem_type G t1 t2 T p q e:=
  forall M H1 H2,
    env_type M H1 H2 G p ->
    forall S1 S2,
    store_type S1 S2 M ->
    exists S1' S2' M' v1 v2,
    exp_type S1 S2 M H1 H2 t1 t2 S1' S2' M' v1 v2 T p q e.

Lemma bi_vtrue2: forall G p,
  sem_type G ttrue ttrue TBool p (plift qempty) (plift qempty).
Proof. 
  intros G p M H1 H2 WFE S1 S2 ST.
  exists S1, S2, (0, 0, (fun v1 v2 => False)), (vbool true), (vbool true).
  eapply bi_vtrue. auto.
Qed.

Lemma bi_vfalse2: forall G p,
  sem_type G tfalse tfalse TBool p (plift qempty) (plift qempty).
Proof.
  intros G p M H1 H2 WFE S1 S2 ST.
  exists S1, S2, (0, 0, (fun v1 v2 => False)), (vbool false), (vbool false).
  eapply bi_vfalse; auto.
Qed.

Lemma bi_var2: forall G x T1 (p:pl),
  indexr x G = Some T1 ->
  p x ->
  sem_type G (tvar x) (tvar x) T1 p (plift (qone x)) (plift qempty).
Proof.
  intros G x T1 p ? ? M H1 H2 WFE S1 S2 ST.
  rewrite plift_one. rewrite plift_empty.
  exists S1, S2, (0, 0, (fun v1 v2 => False)).
  eapply bi_var; eauto.
Qed.

Lemma bi_tref2: forall G t1 t2 p q e,
  sem_type G t1 t2 TBool p q e ->
  sem_type G (tref t1) (tref t2) (TRef TBool) p q e.
Proof.
  intros. intros M H1 H2 WFE S1 S2 ST.
  unfold sem_type in H.
  destruct (H M H1 H2 WFE S1 S2 ST) as [S1' [S2' [M' [v1 [v2 IE]]]]].
  eapply bi_tref; eauto.
Qed.

Lemma bi_tget2: forall G t1 t2 p q e,
  sem_type G t1 t2 (TRef TBool) p q e ->
  sem_type G (tget t1) (tget t2) TBool p pempty (por e q).
Proof. 
  intros.
  intros M H1 H2 WFE S1 S2 ST.
  unfold sem_type in H.
  destruct (H M H1 H2 WFE S1 S2 ST) as [S1' [S2' [M' [v1 [v2 IE]]]]].
  eapply bi_tget; eauto.
Qed.

Lemma bi_tput2: forall G t1 t2 t3 t4 p q1 q2 e1 e2,
  sem_type G t1 t2 (TRef TBool) p q1 e1 ->
  sem_type G t3 t4 TBool p q2 e2 ->
  sem_type G (tput t1 t3) (tput t2 t4) TBool p pempty (por e1 (por e2 q1)).
Proof. 
  intros.
  intros M H1 H2 WFE S1 S2 ST.
  unfold sem_type in H. unfold sem_type in H0.
  destruct (H M H1 H2 WFE S1 S2 ST) as [S1' [S2' [M' [v1 [v2 IE]]]]].
  assert (env_type (stapp M' M) H1 H2 G p) as WFE1. eapply envt_store_extend; eauto.
  assert (store_type S1' S2' (stapp M' M)) as ST1. eapply IE.
  destruct (H0 (stapp M' M) H1 H2 WFE1 S1' S2' ST1) as [S1'' [S2'' [M'' [v3 [v4 IE2]]]]].
  eapply bi_put; eauto. 
Qed.

Lemma bi_tabs2: forall G t1 t2 T1 T2 p qf q2 e2
 (SEM: sem_type (T1 :: G) t1 t2 T2  (plift (qor (qand p qf)(qone (length G)))) (plift (qor q2 (qone (length G)))) (plift (qor e2 (qone (length G)))))
 (CLT1: closed_ty (length G) T1 )
 (CLT2: closed_ty (length G) T2 )  
 (QSUB: psub (plift q2) (pdom G) )
 (ESUB: psub (plift e2) (pdom G) )
 (CLQF: closed_ql (length G)  qf ),
 sem_type G (tabs (qand p qf) t1) (tabs (qand p qf) t2) (TFun T1 T2  q2 e2) (plift p) (plift qf) pempty.
Proof. 
  intros. intros M H1 H2 WFE S1 S2 ST.
  eapply bi_tabs; eauto.
Qed.

Lemma bi_qsub2: forall G t1 t2 T p q q' e e' 
  (SEM: sem_type G t1 t2 T p q e) 
  (PSUB1: psub q q')
  (ESUB1: psub e e')
  (PSUB2: psub q' (pdom G)) 
  (ESUB2: psub e' (pdom G)), 
  sem_type G t1 t2 T p q' e'.
Proof.
  intros. intros M H1 H2 WFE S1 S2 ST.
  unfold sem_type in SEM.
  destruct (SEM M H1 H2 WFE S1 S2 ST) as [S1' [S2' [M' [v1 [v2 IE]]]]].
  eapply bi_qsub; eauto.
  all: apply wf_env_type in WFE; intuition.
  rewrite H0. auto. rewrite H4. auto.
  rewrite H0. auto. rewrite H4. auto.
Qed.

Lemma bi_app2: forall G t1 t2 ex1 ex2 T1 T2 e1 e2 p qf ef q1 q2
  (SEMF: sem_type G t1 t2 (TFun T1 T2 q2 e2) p qf ef) 
  (SEMX: sem_type G ex1 ex2 T1 p q1 e1)
  (SEP: psub (pand  qf q1) pempty)
  (QSUB: psub (plift q2) p)
  (ESUB: psub (plift e2) p),
  sem_type G (tapp t1 ex1) (tapp t2 ex2) T2 p (por (plift q2) q1) (por ef (por e1 (plift e2))).
Proof.
  intros. intros M H1 H2 WFE S1 S2 ST.
  unfold sem_type in SEMF.  unfold sem_type in SEMX.
  destruct (SEMF M H1 H2 WFE S1 S2 ST) as [S1' [S2' [M' [vf1 [vf2 IEF]]]]].

  assert (env_type (stapp M' M) H1 H2 G p) as WFE1. { eapply envt_store_extend. eauto. }
  assert (store_type S1' S2' (stapp M' M)) as ST1. eapply IEF.
  
  destruct (SEMX (stapp M' M) H1 H2 WFE1 S1' S2' ST1) as [S1'' [S2'' [M'' [vx1 [vx2 IEX]]]]].
   
  eapply bi_tapp; eauto.
Qed.

Theorem fundamental_property2 : forall t G T p q e,
  has_type G t T p q e -> 
  sem_type G t t T (plift p) (plift q) (plift e).
Proof.
  intros. induction H. 
  - (* Case "True". *)
    eapply bi_vtrue2.
  - (* Case "False". *)
    eapply bi_vfalse2.
  - (* Case "Var". *)
    eapply bi_var2; eauto.
  - (* Case "tref" *)
    eapply bi_tref2; eauto.
  - (* Case "tget"  *)
    rewrite plift_empty.
    eapply bi_tget2; eauto.
  - (* Case "tput" *)
    rewrite plift_empty.
    eapply bi_tput2; eauto.
  - (* Case "App" *)
    rewrite plift_or.
    eapply bi_app2; eauto. 
  - (* Case "Abs" *)
    eapply bi_tabs2; eauto.
  - (* Case "qsub" *)
    eapply bi_qsub2; eauto.  
Qed.

Inductive ctx_type : (tm -> tm) -> tenv -> ty -> pl -> pl -> pl -> tenv -> ty -> pl -> pl -> pl -> Prop :=
| cx_top: forall G T p q e,
    ctx_type (fun x => x) G T p q e G T p q e
| cx_ref: forall G  p q e,
    ctx_type (fun x => tref x) G TBool p q e G (TRef TBool) p q e
| cx_get: forall G p q e,
    ctx_type (fun x => tget x) G (TRef TBool) p q e G TBool p pempty (por e q)
| cx_put1: forall G t1 p q1 e1 e2 q2,
    has_type G t1 (TRef TBool) p q1 e1 ->
    ctx_type (fun x => tput t1 x) G TBool (plift p) q2 e2 G TBool (plift p) pempty (por (plift e1) (por e2 (plift q1)))
| cx_put2: forall G t2 p q1 e1 e2 q2,
    has_type G t2 TBool p q2 e2 ->
    ctx_type (fun x => tput x t2) G (TRef TBool) (plift p) q1 e1 G TBool (plift p) pempty (por e1 (por (plift e2) q1))
| cx_app1: forall t2 G T1 T2 q1 q2 e1 e2 ef p qf,
    has_type G t2 T1 p q1 e1 ->
    psub (pand qf (plift q1)) pempty ->
    psub (plift q2) (plift p) ->
    psub (plift e2) (plift p) ->
    ctx_type (fun x => tapp x t2) G (TFun T1 T2 q2 e2) (plift p) qf ef G T2 (plift p) (por (plift q2) (plift q1)) (por ef (por (plift e1) (plift e2)))
| cx_app2: forall t1 G T1 T2 q2 e1 e2 p qf ef q1,
    has_type G t1 (TFun T1 T2 q2 e2) p qf ef ->
    psub (pand (plift qf) q1) pempty ->
    psub (plift q2) (plift p) ->
    psub (plift e2) (plift p) ->
    ctx_type (fun x => tapp t1 x) G T1 (plift p) q1 (plift e1)  G T2 (plift p) (por (plift q2) q1)(por (plift ef) (por (plift e1) (plift e2)))
| cx_abs: forall G T1 T2 q2 e2 p qf ef,
    closed_ty (length G) T1 ->
    closed_ty (length G) T2 ->
    psub (plift q2) (pdom G) ->
    psub (plift e2) (pdom G) ->
    closed_ql (length G) qf ->
    ctx_type (fun x => tabs (qand p qf) x) (T1::G) T2 (plift (qor (qand p qf)(qone (length G)))) (plift (qor q2 (qone (length G)))) (plift (qor e2 (qone (length G)))) G (TFun T1 T2 q2 e2) (plift p) (plift qf) (plift ef)
| cx_qsub: forall G T p q q' e e',
    psub q q' ->
    psub e e' ->
    psub q' (pdom G) -> 
    psub e' (pdom G) -> 
    ctx_type (fun x => x) G T p q e G T p q' e'
.

Theorem congr:
  forall C G1 T1 p q e G2 T2 p' q' e',
    ctx_type C G1 T1 p q e G2 T2 p' q' e' ->
  forall t t',
    sem_type G1 t t' T1 p q e->
    sem_type G2 (C t) (C t') T2 p' q' e'.
Proof.
  intros ? ? ? ? ? ? ? ? ? ? ? CX.
  induction CX; intros.
  - eauto.
  - eapply bi_tref2. eauto.
  - eapply bi_tget2. eauto.  
  - eapply bi_tput2; eauto. eapply fundamental_property2. eauto. 
  - eapply bi_tput2; eauto. eapply fundamental_property2. eauto. 
  - eapply bi_app2; eauto. eapply fundamental_property2. eauto.    
  - eapply bi_app2; eauto. eapply fundamental_property2. eauto. 
  - eapply bi_tabs2; eauto.
  - eapply bi_qsub2; eauto.
Qed.


Lemma adequacy: forall e e' T,
  sem_type [] e e' T pempty pempty pempty  ->
  (exists v M, tevaln [] [] e M v) <-> 
  (exists v' M', tevaln [] [] e' M' v').
Proof. 
  intros. 
  assert (env_type (0, 0, (fun x1 x2: nat => False)) [] [] [] pempty) as WFE. { 
    unfold env_type; intuition. 
    1,2: unfoldq; intros; intuition.
  }
  assert (store_type [] [] (0, 0, (fun x1 x2: nat => False))) as ST.
  unfold store_type; intuition.
  unfold sem_type in H. 
  specialize (H (0, 0, (fun x1 x2: nat => False)) [] [] WFE [] [] ST). 
  destruct H as [S1 [S2 [M [v1 [v2 IE]]]]].
  destruct IE as [? [? [? [? [? ?]]]]].
  split. 
  + intros. exists v2, S2. intuition.
  + intros. exists v1, S1. intuition.
Qed.

Definition context_equiv G t1 t2 T1 p q e:=
  has_type G t1 T1 p q e ->
  has_type G t2 T1 p q e ->
  forall C,
    ctx_type C G T1 (plift p) (plift q) (plift e) [] TBool (plift qempty) (plift qempty) (plift qempty) ->
    (exists v1 S1, tevaln [] [] (C t1) S1 v1) <->
    (exists v2 S2, tevaln [] [] (C t2) S2 v2).


(* soundness of binary logical relations *)
Theorem soundess: forall G t1 t2 T p q e,
  has_type G t1 T p q e ->
  has_type G t2 T p q e ->
    (sem_type G t1 t2 T (plift p) (plift q) (plift e) -> 
     context_equiv G t1 t2 T p q e).    
Proof. 
  intros. unfold context_equiv. intros.
  rewrite plift_empty in *.
  assert (sem_type [] (C t1)(C t2) TBool pempty pempty pempty). {
   specialize (congr C G  T (plift p) (plift q) (plift e) [] TBool pempty pempty pempty ); intuition.
   }

  eapply adequacy; eauto. 
Qed.  

End STLC.
