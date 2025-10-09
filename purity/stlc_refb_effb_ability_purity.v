(* Full safety for STLC *)

(*

An LR-based termination and semantic soundness proof for STLC.

Add first-order mutable references (restricted to TBool)

Binary logical relation with contextual equivalence.

Add simple yes/no effect tracking, prove store invariance.

Prove beta equivalence for pure function arguments.

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

(* ---------- qualifier sets ---------- *)

Definition qif (b:bool) q (x:nat) := if b then q x else false.


Definition pl := nat -> Prop.

Definition pempty: pl := fun x => False.                            (* empty set *)

Definition pone (x:nat): pl := fun x' => x' = x.                    (* singleton set *)

Definition pand p1 p2 (x:nat) := p1 x /\ p2 x.                      (* intersection *)

Definition por p1 p2 (x:nat) := p1 x \/ p2 x.                       (* union *)

Definition pnot p1 (x:nat) := ~ p1 x.                               (* complement *)

Definition pdiff p1 p2 (x:nat) := p1 x /\ ~ p2 x.                   (* difference *)

Definition pnat n := fun x' =>  x' < n.                             (* numeric bound *)

Definition pdom {X} (H: list X) := fun x' =>  x' < (length H).      (* domain of a list *)

Definition pif (b:bool) p (x:nat) := if b then p x else False.      (* conditional *)

Definition psub (p1 p2: pl): Prop := forall x:nat, p1 x -> p2 x.    (* subset inclusion *)

Definition plift (b: ql): pl := fun x => b x = true.                (* reflect nat->bool set *)

(* ---------- language syntax ---------- *)

Definition id := nat.

Inductive ty : Type :=
  | TBool  : ty
  | TRef   : ty
  | TFun   : ty -> bool -> bool -> ty -> bool -> bool -> bool -> ty
.

Inductive tm : Type :=
  | ttrue : tm
  | tfalse : tm
  | tvar : id -> tm
  | tref : tm -> tm
  | tget : tm -> tm
  | tput : tm -> tm -> tm
  | tapp : tm -> tm -> tm
  | tabs : tm -> tm
  | tnot : tm -> tm
  | tbin : tm -> tm -> tm
.

Inductive vl: Type :=
| vbool :  bool -> vl
| vref  :  id -> vl
| vabs  :  list vl -> tm -> vl 
.

Definition venv := list vl.
Definition tenv := list (ty * bool * bool).
Definition lenv := list ql.
Definition uenv := list bool.

Definition stor := list vl.

#[global] Hint Unfold venv.
#[global] Hint Unfold tenv.
#[global] Hint Unfold lenv.
#[global] Hint Unfold uenv.
#[global] Hint Unfold stor.


(* ---------- syntactic typing rules ---------- *)

Definition bsub b b' := b = true -> b' = true.

Definition env_cap (G:tenv) p a := forall x T1 fr1 a1,
    indexr x G = Some (T1, fr1, a1) -> p x = true -> bsub (fr1||a1) a.

(*
G |- t: T p fr a e
*)

Inductive has_type : tenv -> tm -> ty -> ql -> bool -> bool -> bool -> Prop :=
| t_true: forall env,
    has_type env ttrue TBool qempty false false false
| t_false: forall env,
    has_type env tfalse TBool qempty false false false
| t_var: forall x env T a fr,
    indexr x env = Some (T, fr, a) ->
    has_type env (tvar x) T (qone x) false (fr||a) false
| t_ref: forall t env p fr a e,
    has_type env t TBool p fr a e ->
    has_type env (tref t) TRef p true false e
| t_get: forall t env p fr a e,
    has_type env t TRef p fr a e ->
    has_type env (tget t) TBool p false false (e||a)
| t_put: forall t t2 env p1 p2 fr1 fr2 a1 a2 e1 e2,
    has_type env t TRef p1 fr1 a1 e1 ->
    has_type env t2 TBool p2 fr2 a2 e2 ->
    has_type env (tput t t2) TBool (qor p1 p2) false false (e1||e2||a1)
| t_app: forall env f t T1 T2 p1 p2 fr1 frf fr2 a1 af a2 e1 ef e2,
    has_type env f (TFun T1 fr1 a1 T2 fr2 a2 e2) p1 frf af ef ->
    has_type env t T1 p2 fr1 a1 e1 ->
    has_type env (tapp f t) T2 (qor p1 p2) ((frf||fr1)&&a2 || fr2) ((af||a1)&&a2) (e1 || ef || (af||a1)&&e2)
| t_abs: forall env t T1 T2 p2 pf fr1 fr2 af a1 a2 e2,
    has_type ((T1,fr1,a1)::env) t T2 p2 fr2 a2 e2 ->
    pf = (qdiff p2 (qone (length env))) ->
    env_cap env pf af ->
    has_type env (tabs t) (TFun T1 fr1 a1 T2 fr2 a2 e2) pf false ((e2||a2)&&af) false
| t_not: forall env t p e fr a,
    has_type env t TBool p fr a e ->
    has_type env (tnot t) TBool p false false e
| t_bin: forall env t1 t2 p1 p2 fr1 fr2 e1 e2 a1 a2,
    has_type env t1 TBool p1 fr1 a1 e1  ->
    has_type env t2 TBool p2 fr2 a2 e2 ->
    has_type env (tbin t1 t2) TBool (qor p1 p2) false false (e1 || e2)  
| t_sub_fresh: forall env t T p fr a e,
    has_type env t T p fr a e ->
    has_type env t T p true a e
| t_sub_cap: forall env t T p fr a e,
    has_type env t T p fr a e ->
    has_type env t T p fr true e
| t_sub_eff: forall env t T p fr a e,
    has_type env t T p fr a e ->
    has_type env t T p fr a true
.



Lemma indexr_map: forall {A B} (G: list A) (f: A -> B) x a,
    indexr x G = Some a ->
    indexr x (map f G) = Some (f a).
Proof.
  intros A B G. induction G.
  intros. inversion H.
  intros. simpl in *.
  rewrite map_length. 
  bdestruct (x =? length G). congruence.
  eauto.
Qed.



Fixpoint fv n t: ql :=
  match t with
  | ttrue => qempty
  | tfalse => qempty
  | tvar x => qone x
  | tref t => fv n t
  | tget t => fv n t
  | tput t1 t2 => qor (fv n t1) (fv n t2)
  | tapp t1 t2 => qor (fv n t1) (fv n t2)
  | tabs t => qdiff (fv (S n) t) (qone n)
  | tnot t => fv n t
  | tbin t1 t2 => qor (fv n t1) (fv n t2)
end.

Lemma hast_fv: forall G t T p fr a e,
    has_type G t T p fr a e -> p = fv (length G) t.
Proof.
  intros. induction H; simpl; eauto.
  - rewrite IHhas_type1, IHhas_type2. eauto.
  - rewrite IHhas_type1, IHhas_type2. eauto.
  - rewrite H0, IHhas_type. simpl. eauto.
  - rewrite IHhas_type1, IHhas_type2. eauto.
Qed.


(* ---------- operational semantics ---------- *)

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
            | (M', Some (Some (vabs _ _))) => (M', Some None)
            | (M', Some (Some (vref x))) => (M', Some (indexr x M'))
          end
        | tput er ex    =>
          match teval n M env er with
            | (M', None) => (M', None)
            | (M', Some None) => (M', Some None)
            | (M', Some (Some (vbool _))) => (M', Some None)
            | (M', Some (Some (vabs _ _))) => (M', Some None)
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
        | tnot e =>
          match teval n M env e with 
          | (M', None) => (M', None)
          | (M', Some None) => (M', Some None)
          | (M', Some (Some (vbool b))) => (M', Some (Some (vbool (negb b))))
          | (M', _)    => (M', Some None)
          end
        | tbin e1 e2   =>
          match teval n M env e1 with
          | (M', None) => (M', None)
          | (M', Some None) => (M', Some None)
          | (M', Some (Some (vbool b1))) => 
              match teval n M' env e2 with
              | (M'', None) => (M'', None)
              | (M'', Some None) => (M'', Some None)
              | (M'', Some (Some (vbool b2))) => (M'', Some (Some (vbool (b1 && b2))))
              | (M'', Some (Some (vref _))) => (M'', Some None)
              | (M'', Some (Some (vabs _ _))) => (M'', Some None)
              end
          | (M', Some (Some (vref _))) => (M', Some None)
          | (M', Some (Some (vabs _ _))) => (M', Some None)
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

(* value interpretation of terms *)
Definition tevaln M env e M' v :=
  exists nm,
  forall n,
    n > nm ->
    teval n M env e = (M', Some (Some v)).


(* ---------- LR definitions  ---------- *)

Fixpoint val_locs_fix (v: vl) (l: nat): bool :=
  match v with
  | vbool  _ => false
  | vref x   => x =? l
  | vabs H t  =>
      let fix vars_locs_fix (H: list vl) (q: ql) :=
        match H with
        | v :: H => (q (length H) && val_locs_fix v l) || vars_locs_fix H q
        | [] => false
        end
      in vars_locs_fix H (fv (length H) (tabs t))
  end.

Fixpoint vars_locs_fix (V: lenv) (q: ql) (l: nat): bool :=
  match V with
  | ls :: V => (q (length V) && ls l) || vars_locs_fix V q l
  | [] => false
  end.

Definition val_locs v := plift (val_locs_fix v). 

Definition var_locs (E: lenv) x l := exists ls, indexr x E = Some ls /\ plift ls l.

Definition vars_locs (E: lenv) q l := exists x, q x /\ var_locs E x l.

Definition exp_locs (E: lenv) (e:tm) := vars_locs E (plift (fv (length E) e)).

Definition exp_locs_fix (E: lenv) (e:tm) := vars_locs_fix E (fv (length E) e).

Definition exp_locsV (u: bool) (E: lenv) (e:tm) := pif u (exp_locs E e).


Definition stty: Type := (nat * nat * (nat -> nat -> Prop)). (* partial bijection *)

Definition strel (M: stty) := snd M.

Definition st_len1 (M: stty) := fst (fst M).
Definition st_len2 (M: stty) := snd (fst M).


Definition st_empty: stty := (0, 0, (fun i j => False)).

Definition st_extend' L1 L2 (M: stty): stty := (S L1, S L2, 
  fun l1 l2 =>
    (l1 = L1 /\ l2 = L2) \/
      (l1 < L1 /\ l2 < L2 /\ strel M l1 l2)).

Definition st_extend (M: stty): stty :=
  st_extend' (st_len1 M) (st_len2 M) M.


Definition st_pad L1 L2 (M: stty): stty :=
  (L1 + (st_len1 M), L2 + (st_len2 M), (strel M)).

Definition st_step (M M': stty) (fr: bool): stty :=
  if fr then M' else (st_len1 M', st_len2 M', (strel M)).

Definition st_prefix (L1 L2: nat) (M: stty): stty :=
  (L1, L2, (fun l1 l2 => (l1 < L1 \/ l2 < L2) /\ strel M l1 l2)).


Definition stty_wellformed (M: stty) :=
  (forall l1 l2,
      strel M l1 l2 ->
      l1 < st_len1 M /\
      l2 < st_len2 M) /\
  (* enforce that strel is a partial bijection *)
  (forall l1 l2 l2',
      strel M l1 l2 ->
      strel M l1 l2' ->
      l2 = l2') /\
  (forall l1 l1' l2,
      strel M l1 l2 ->
      strel M l1' l2 ->
      l1 = l1').

Definition store_type (S1 S2: stor) (M: stty) (p1 p2: pl) :=
  length S1 = st_len1 M /\
  length S2 = st_len2 M /\
  (forall l1 l2,
      strel M l1 l2 ->
      p1 l1 ->
      p2 l2 ->
      exists b,
        indexr l1 S1 = Some (vbool b) /\
        indexr l2 S2 = Some (vbool b)).

    
Definition st_chain (M:stty) (M1:stty) :=
  (forall l1 l2,
      strel M l1 l2 ->
      strel M1 l1 l2).

Definition st_chain_partial (M:stty) (M1:stty) (p1 p2: pl) :=
  (forall l1 l2,
      strel M l1 l2 ->
      p1 l1 ->
      p2 l2 ->
      strel M1 l1 l2).

Definition st_chain_reverse (M M1: stty) :=
  (forall l1 l2,
      strel M1 l1 l2 ->
      (l1 < st_len1 M \/ l2 < st_len2 M) ->
      strel M l1 l2).

Definition store_write (S1 S1': stor) p :=
  forall i, (pdiff (pdom S1) p) i -> indexr i S1 = indexr i S1'.


Fixpoint val_type M v1 v2 T (u: Prop) (ls1 ls2: ql): Prop :=
  match v1, v2, T with
  | vbool b1, vbool b2, TBool =>  
      b1 = b2
  | vref l1, vref l2, TRef => 
      (u -> strel M l1 l2 /\ plift ls1 l1 /\ plift ls2 l2)
  | vabs H1 ty1, vabs H2 ty2, TFun T1 fr1 a1 T2 fr a e => 
      forall S1' S2' M' p1 p2 vx1 vx2 (ux: bool) lsx1 lsx2 (uy uyv:bool),
        (e||uy&&a = true -> st_chain_partial M M' (plift ls1) (plift ls2)) ->
        (e||uy&&a = true -> u) ->
        (e||uy&&a = true -> ux=true) ->
        bsub e uyv -> 
        (uy = negb a||uyv) -> 
        (fr1||a1 = false -> ux = true) -> 
        stty_wellformed M' ->
        st_len1 M <= st_len1 M' -> 
        st_len2 M <= st_len2 M' ->
        store_type S1' S2' M' p1 p2 ->
        (psub (pif e (por (plift ls1) (plift lsx1))) p1) ->
        (psub (pif e (por (plift ls2) (plift lsx2))) p2) ->
        ((fr1||a1 = false \/ ux=false) -> psub (plift lsx1) pempty) ->
        ((fr1||a1 = false \/ ux=false) -> psub (plift lsx2) pempty) ->
        val_type M' vx1 vx2 T1 (ux=true) lsx1 lsx2 ->
        exists S1'' S2'' M'' vy1 vy2 lsy1 lsy2,
          st_chain M' M'' /\
          stty_wellformed M'' /\
          tevaln S1' (vx1::H1) ty1 S1'' vy1 /\
          tevaln S2' (vx2::H2) ty2 S2'' vy2 /\
          length S1' <= length S1'' /\
          length S2' <= length S2'' /\  
          store_type S1'' S2'' M''
            (por p1 (pdiff (pdom S1'') (pdom S1')))
            (por p2 (pdiff (pdom S2'') (pdom S2'))) /\
          (uy = false -> psub (plift lsy1) pempty) /\
          (uy = false -> psub (plift lsy2) pempty) /\
          val_type M'' vy1 vy2 T2 (uy=true) lsy1 lsy2 /\            
          psub (plift lsy1)
            (por (pif a (plift ls1))
               (por (pif a (plift lsx1))
                  (por (pif false (pnot pempty))
                     (pif fr (pdiff (pdom S1'') (pdom S1')))))) /\
          psub (plift lsy2)
            (por (pif a (plift ls2))
               (por (pif a (plift lsx2))
                  (por (pif false (pnot pempty))
                     (pif fr (pdiff (pdom S2'') (pdom S2')))))) /\
          store_write S1' S1''
            (pif e (por (plift ls1) (plift lsx1))) /\
          store_write S2' S2''
            (pif e (por (plift ls2) (plift lsx2))) /\
          (fr = false -> strel M'' = strel M')
  | _,_,_ =>
      False
  end.

Definition exp_type2 v1 v2 uv ls1 ls2 S1 S2 M H1 H2 V1 V2 t1 t2 S1' S2' M' T u p1 p2 fr a e :=
    st_chain M M' /\
    stty_wellformed M' /\
    tevaln S1 H1 t1 S1' v1 /\
    tevaln S2 H2 t2 S2' v2 /\
    length S1 <= length S1' /\
    length S2 <= length S2' /\ 
    store_type S1' S2' M'
      (por p1 (pdiff (pdom S1') (pdom S1)))
      (por p2 (pdiff (pdom S2') (pdom S2))) /\
    val_type M' v1 v2 T (u=true) ls1 ls2 /\
    u = (negb a || uv) /\ 
    True /\
    (u = false -> psub (plift ls1) pempty) /\
    (u = false -> psub (plift ls2) pempty) /\
    psub (plift ls1)
      (por (pif (a) (exp_locs V1 t1))
         (por (pif false (pnot pempty))
            (pif fr (pdiff (pdom S1') (pdom S1))))) /\
    psub (plift ls2)
      (por (pif (a) (exp_locs V2 t2))
         (por (pif false (pnot pempty)) 
            (pif fr (pdiff (pdom S2') (pdom S2))))) /\
    store_write S1 S1'
      (pif e (exp_locs V1 t1)) /\
    store_write S2 S2'
      (pif e (exp_locs V2 t2)) /\
    (fr = false -> strel M' = strel M).


Definition exp_type1 S1 S2 M H1 H2 V1 V2 t1 t2 S1' S2' M' T uv p1 p2 fr a e :=
    exists v1 v2 u ls1 ls2,
      exp_type2 v1 v2 uv ls1 ls2 S1 S2 M H1 H2 V1 V2 t1 t2 S1' S2' M' T u p1 p2 fr a e.


Definition exp_type S1 S2 M H1 H2 V1 V2 t1 t2 T u p1 p2 fr a e :=
  exists S1' S2' M',
    exp_type1 S1 S2 M H1 H2 V1 V2 t1 t2 S1' S2' M' T u p1 p2 fr a e.

Definition exp_type_eff M H1 H2 V1 V2 t1 t2 T u fr a e :=
  stty_wellformed M ->
  forall S1 S2 p1 p2,
    store_type S1 S2 M p1 p2 ->
    (psub (pif e (exp_locs V1 t1)) p1) ->
    (psub (pif e (exp_locs V2 t2)) p2) ->
    exp_type S1 S2 M H1 H2 V1 V2 t1 t2 T u p1 p2 fr a e.


Definition env_type M (H1 H2: venv) (V1 V2: lenv) (G: tenv) (u0: bool) (p: pl) :=
  length H1 = length G /\
  length H2 = length G /\
  length V1 = length G /\
  length V2 = length G /\
  True /\ 
  forall x T fr a,
    indexr x G = Some (T,fr,a) ->
    exists v1 v2 u ls1 ls2,
      indexr x H1 = Some v1 /\
      indexr x H2 = Some v2 /\
      ((fr||a = false \/ u0=true) -> indexr x V1 = Some ls1) /\
      ((fr||a = false \/ u0=true) -> indexr x V2 = Some ls2) /\
      True /\ 
      (u = negb(fr||a) || u0) /\
      (p x -> val_type M v1 v2 T (u = true) ls1 ls2) /\
      ((fr||a = false \/ u0 = false) -> psub (plift ls1) pempty) /\
      ((fr||a = false \/ u0 = false) -> psub (plift ls2) pempty).


#[export] Hint Constructors ty: core.
#[export] Hint Constructors tm: core.
#[export] Hint Constructors vl: core.

#[export] Hint Constructors has_type: core.

#[export] Hint Constructors option: core.
#[export] Hint Constructors list: core.

#[export] Hint Unfold exp_type2: core.

#[export] Hint Unfold st_len1: core.
#[export] Hint Unfold st_len2: core.
#[export] Hint Unfold strel: core.

(* ---------- qualifier reflection & tactics  ---------- *)

Ltac unfoldq := unfold psub, pdom, pnat, pdiff, pnot, pif, pand, por, pempty, pone, var_locs, vars_locs in *.
Ltac unfoldq1 := unfold qsub, qdom, qand, qempty, qone in *.

Lemma plift_qual_eq: forall q1 q2,
    (q1 = q2) = (plift q1 = plift q2).
  intros. eapply propositional_extensionality.
  remember (plift q1) as p1.
  remember (plift q2) as p2. 
  unfold plift in *. intuition.
  - subst. eauto.
  - eapply functional_extensionality. intros.
    remember (q1 x) as qx1. symmetry in Heqqx1.
    remember (q2 x) as qx2. symmetry in Heqqx2.
    destruct qx1; destruct qx2; try reflexivity.
    + replace (q1 x = true) with (p1 x) in *.
      rewrite H in Heqqx1. subst p2. eauto. subst p1. eauto. 
    + replace (q2 x = true) with (p2 x) in *. 
      rewrite <-H in Heqqx2. subst p1. eauto. subst p2. eauto.
Qed.

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

Lemma plift_if1: forall a b (c: bool),
    plift (if c then a else b) = if c then plift a else plift b.
Proof.
  intros. unfoldq. unfold plift.
  eapply functional_extensionality. intros.
  eapply propositional_extensionality.
  destruct c; intuition.
Qed.

Lemma plift_if: forall a (c: bool),
    plift (qif c a) = pif c (plift a).
Proof.
  intros. eapply functional_extensionality.
  intros. eapply propositional_extensionality.
  destruct c; intuition.
Qed.

Lemma plift_diff: forall a b,
    plift (qdiff a b) = pdiff (plift a) (plift b).
Proof.
  intros. unfoldq. unfold plift.
  eapply functional_extensionality. intros.
  eapply propositional_extensionality.
  unfold qdiff. destruct (a x); destruct (b x); intuition. 
Qed.

Lemma plift_dom: forall A (E: list A),
    plift (qdom E) = pdom E.
Proof.
  intros. unfoldq. unfold plift.
  eapply functional_extensionality. intros.
  eapply propositional_extensionality. 
  bdestruct (qdom E x); intuition. 
Qed.

Lemma pand_or_distribute: forall p q s, 
  pand s (por p q)  = (por (pand s p) (pand s q)).
Proof.
  intros. unfoldq.  eapply functional_extensionality. intros.
  eapply propositional_extensionality. split; intros; intuition.
Qed.

Lemma pand_or_distribute2: forall p q s, 
  pand s (por (plift p) q)  = (por (pand s  (plift p)) (pand s q)).
Proof.
  intros. unfoldq. unfold plift. eapply functional_extensionality. intros.
  eapply propositional_extensionality. split; intros; intuition.
Qed.

Lemma pdiff_same: forall p,
  pdiff p p = pempty.
Proof. 
  intros. eapply functional_extensionality.
  intros. eapply propositional_extensionality.
  unfoldq; intuition.
Qed.

Lemma pdiff_merge: forall (S1 S1' S1'': stor),
    length S1 <= length S1' ->
    length S1' <= length S1'' ->
    (por (pdiff (pdom S1') (pdom S1))
       (pdiff (pdom S1'') (pdom S1'))) = pdiff (pdom S1'') (pdom S1).
Proof.
  intros. eapply functional_extensionality.
  intros. eapply propositional_extensionality.
  unfold pdom, pdiff, por. intuition. lia. 
Qed.

Lemma pdiff_empty: forall (p: pl),
    pdiff pempty p = pempty.
Proof.
  intros. eapply functional_extensionality.
  intros. eapply propositional_extensionality.
  unfoldq. intuition. 
Qed.

Lemma pdiff_or: forall (p1 p2 p3: pl),
    (pdiff (por p1 p2) p3) = 
       (por (pdiff p1 p3) (pdiff p2 p3)).
Proof.
  intros. eapply functional_extensionality.
  intros. eapply propositional_extensionality.
  unfoldq. intuition. 
Qed.

Lemma por_assoc: forall (p1 p2 p3: pl),
    (por (por p1 p2) p3) = (por p1 (por p2 p3)).
Proof.
  intros. eapply functional_extensionality.
  intros. eapply propositional_extensionality.
  unfold pdom, pdiff, por. intuition. 
Qed.

Lemma por_empty_l: forall p, 
  por pempty p = p.
Proof.
  intros. eapply functional_extensionality.
  intros. eapply propositional_extensionality.
  unfoldq. intuition.
Qed.

Lemma por_empty_r: forall p,
  por p pempty = p.
Proof.
  intros. eapply functional_extensionality.
  intros. eapply propositional_extensionality.
  unfoldq. intuition.
Qed.

Lemma plift_vars_locs: forall V q,
    plift (vars_locs_fix V q) = vars_locs V (plift q).
Proof.
  intros. eapply functional_extensionality.
  intros. eapply propositional_extensionality.
  unfold vars_locs, var_locs, plift in *.
  intuition.
  - induction V. intuition.
    rename a into ls. 
    remember (q (length V)) as b1.
    remember (ls x) as b2.
    destruct b1. destruct b2. simpl in H.
    (* both true *)
    exists (length V). split. eauto.
    exists ls. rewrite indexr_head. intuition.
    (* one false *)
    simpl in H. rewrite <-Heqb1, <-Heqb2 in H. simpl in H. eapply IHV in H.
    destruct H. exists x0. intuition.
    destruct H1 as (ls' & ?). exists ls'. rewrite indexr_extend1 in H. intuition eauto. 
    (* other false *)
    simpl in H. rewrite <-Heqb1 in H. simpl in H. eapply IHV in H. 
    destruct H. exists x0. intuition.
    destruct H1 as (ls' & ?). exists ls'. rewrite indexr_extend1 in H. intuition eauto.
  - simpl. destruct H as [? [? ?]]. destruct H0 as (? & ? & ?).
    unfold indexr in H0. induction V.
    congruence.
    rename a into ls. 
    bdestruct (x0 =? length V).
    inversion H0. subst. simpl. rewrite H.
    unfold plift in H1. rewrite H1. simpl. eauto.
    simpl. rewrite IHV.
    destruct (q (length V) && ls x); simpl; eauto.
    eauto. 
Qed.

Lemma plift_exp_locs: forall V t,
    plift (exp_locs_fix V t) = exp_locs V t.
Proof.
  intros. unfold exp_locs_fix. rewrite plift_vars_locs. eauto. 
Qed.


(* ---------- Lemmas about qualifiers and locations  ---------- *)

Lemma vl_mono: forall H1 p p',
    psub p p' ->
    psub (vars_locs H1 p) (vars_locs H1 p').
Proof.
  intros. intros ??. destruct H0 as (? & ? & ? & ? & ?). 
  eexists. split. eauto. eexists. split; eauto.
Qed.

Lemma vl_empty: forall H1,
    vars_locs H1 pempty = pempty.
Proof.
  intros. eapply functional_extensionality.
  intros. eapply propositional_extensionality.
  split; intros.
  destruct H as (? & ? & ? & ? & ?). contradiction.
  contradiction.
Qed.

Lemma vl_dist_or: forall H1 p p',
    vars_locs H1 (por p p') = por (vars_locs H1 p) (vars_locs H1 p').
Proof.
  intros. eapply functional_extensionality.
  intros. eapply propositional_extensionality. split; intros.
  destruct H as (? & ? & ? & ? & ?). destruct H.
  left. eexists. split. eauto. eexists. split; eauto.
  right. eexists. split. eauto. eexists. split; eauto.
  destruct H. 
  destruct H as (? & ? & ? & ? & ?). 
  eexists. split. left. eauto. eexists. split; eauto.
  destruct H as (? & ? & ? & ? & ?). 
  eexists. split. right. eauto. eexists. split; eauto.
Qed.


Lemma exp_locs_empty: forall t,
    exp_locs [] t = pempty.
Proof.
  intros. eapply functional_extensionality.
  intros. eapply propositional_extensionality. split; intros.
  destruct H as (? & ? & ? & ? & ?). inversion H0. inversion H. 
Qed.

Lemma exp_locs_var: forall H x v1,
    indexr x H = Some v1 ->
    psub (plift v1) (exp_locs H (tvar x)).
Proof.
 intros. unfold exp_locs, psub, por. simpl. 
 exists x. split. rewrite plift_one. intuition. 
 exists v1. split; eauto. 
Qed.

Lemma exp_locs_ref: forall H t1,
    exp_locs H (tref t1) = exp_locs H t1.
Proof.
  intros. unfold exp_locs. unfoldq. simpl.
  eapply functional_extensionality. intros. 
  eapply propositional_extensionality. split; intros.
  destruct H0. destruct H0. 
  eexists. split; eauto.
  destruct H0. destruct H0.
  eexists. split; eauto.
Qed.

Lemma exp_locs_get: forall H t1,
    exp_locs H (tget t1) = exp_locs H t1.
Proof.
  intros. unfold exp_locs. unfoldq. simpl.
  eapply functional_extensionality. intros. 
  eapply propositional_extensionality. split; intros.
  destruct H0. destruct H0. 
  eexists. split; eauto.
  destruct H0. destruct H0.
  eexists. split; eauto.
Qed.

Lemma exp_locs_put: forall H t1 t2,
    exp_locs H (tput t1 t2) = por (exp_locs H t1) (exp_locs H t2).
Proof.
  intros. unfold exp_locs. unfoldq. simpl. rewrite plift_or. 
  eapply functional_extensionality. intros. 
  eapply propositional_extensionality. split; intros.
  destruct H0. destruct H0. destruct H0.
  left. eexists. split; eauto.
  right. eexists. split; eauto.
  destruct H0. destruct H0. destruct H0.
  eexists. split. left. eauto. eauto. 
  destruct H0. destruct H0. 
  eexists. split. right. eauto. eauto.   
Qed.

Lemma exp_locs_abs: forall H t1 v1,
    psub (exp_locs (v1::H) t1) (por (exp_locs H (tabs t1)) (plift v1)).
Proof.
  intros. intros ? Q.
  unfold exp_locs in *. simpl in Q.
  destruct Q as (? & ? & ? & ? & ?). bdestruct (x0 =? length H).
  subst x0. rewrite indexr_head in H1. inversion H1. subst x1.
  right. eauto.
  rewrite indexr_skip in H1. 2: eauto.
  left. simpl. eexists. split. rewrite plift_diff, plift_one. unfoldq. eauto.
  exists x1. split; eauto. 
Qed.

Lemma exp_locs_app: forall H t1 t2,
    exp_locs H (tapp t1 t2) = por (exp_locs H t1) (exp_locs H t2).
Proof.
  intros. unfold exp_locs. unfoldq. simpl. rewrite plift_or. 
  eapply functional_extensionality. intros. 
  eapply propositional_extensionality. split; intros.
  destruct H0. destruct H0. destruct H0.
  left. eexists. split; eauto.
  right. eexists. split; eauto.
  destruct H0. destruct H0. destruct H0.
  eexists. split. left. eauto. eauto. 
  destruct H0. destruct H0. 
  eexists. split. right. eauto. eauto.
Qed.

Lemma exp_locs_tnot: forall H t,
  exp_locs H (tnot t) = exp_locs H t.
Proof.
  intros. unfold exp_locs. simpl. auto.
Qed.

Lemma exp_locs_tbin: forall H t1 t2,
  exp_locs H (tbin t1 t2) = por (exp_locs H t1)(exp_locs H t2).
Proof.
  intros. unfold exp_locs. unfoldq. simpl. rewrite plift_or. 
  eapply functional_extensionality. intros. 
  eapply propositional_extensionality. split; intros.
  destruct H0. destruct H0. destruct H0.
  left. eexists. split; eauto.
  right. eexists. split; eauto.
  destruct H0. destruct H0. destruct H0.
  eexists. split. left. eauto. eauto. 
  destruct H0. destruct H0. 
  eexists. split. right. eauto. eauto.
Qed.

Lemma hast_closed: forall G t T p fr a e,
    has_type G t T p fr a e -> psub (plift p) (pdom G).
Proof.
  intros. induction H; simpl; eauto.
  - rewrite plift_empty. unfoldq. intuition.
  - rewrite plift_empty. unfoldq. intuition.
  - rewrite plift_one. eapply indexr_var_some' in H. unfoldq. intuition.
  - rewrite plift_or. unfoldq. intuition.
  - rewrite plift_or. unfoldq. intuition.
  - subst pf. rewrite plift_diff, plift_one.
    unfoldq. intuition. eapply IHhas_type in H2.
    simpl in H2. lia. 
  - rewrite plift_or. unfoldq. intuition.
Qed.

Definition env_type0 (H1 H2: lenv) (G: tenv) (p: pl) :=
  length H1 = length G /\
  length H2 = length G /\
  forall x T fr a,
    indexr x G = Some (T,fr,a) ->
    p x -> exists v1 v2,
      indexr x H1 = Some v1 /\
      indexr x H2 = Some v2 /\
      (fr||a = false -> psub (plift v1) pempty) /\
      (fr||a = false -> psub (plift v2) pempty).

Lemma fv_cap_empty: forall G t p H1 H2,
    p = fv (length G) t ->
    env_cap G p false ->
    env_type0 H1 H2 G (plift p) -> 
    psub (exp_locs H1 t) pempty /\ psub (exp_locs H2 t) pempty .
Proof.
  intros. unfold exp_locs. remember H as H4. 
  destruct H3 as (? & ? & ?). split. 
  - rewrite H3,<-H4. intros ? Q. destruct Q as (? & ? & ? & ? & ?).
    assert (exists T1 fr1 a1, indexr x0 G = Some (T1, fr1, a1)). {
      eapply indexr_var_some' in H8 as L. rewrite H3 in L.
      eapply indexr_var_some in L. destruct L, x2, p0.
      eexists _,_,_. eauto. }
    destruct H10 as (T1 & fr1 & a1 & L). eapply H6 in L as L1.
    destruct L1 as (v1 & v2 & ? & ? & ? & ?).
    eapply H0 in L as L1. 
    assert (fr1||a1 = false). { destruct (fr1||a1). assert (false = true). eapply L1. eauto. eauto. inversion H14. eauto. }
    rewrite H8 in H10. inversion H10. subst. intuition. eauto.
  - rewrite H5,<-H4. intros ? Q. destruct Q as (? & ? & ? & ? & ?).
    assert (exists T1 fr1 a1, indexr x0 G = Some (T1, fr1, a1)). {
      eapply indexr_var_some' in H8 as L. rewrite H5 in L.
      eapply indexr_var_some in L. destruct L, x2, p0.
      eexists _,_,_. eauto. }
    destruct H10 as (T1 & fr1 & a1 & L). eapply H6 in L as L1.
    destruct L1 as (v1 & v2 & ? & ? & ? & ?).
    eapply H0 in L as L1. 
    assert (fr1||a1 = false). { destruct (fr1||a1). assert (false = true). eapply L1. eauto. eauto. inversion H14. eauto. }
    rewrite H8 in H11. inversion H11. subst. intuition. eauto.
Qed.

Lemma hast_fv1': forall G t T p fr a e H1 H2,
    has_type G t T p fr a e ->
    env_cap G p false ->
    env_type0 H1 H2 G (plift p) -> 
    psub (exp_locs H1 t) pempty /\ psub (exp_locs H2 t) pempty .
Proof.
  intros. eapply fv_cap_empty. eapply hast_fv. eauto. eauto. eauto. 
Qed.

Lemma hast_fv1: forall G t T p fr a e M H1 H2 V1 V2 u,
    has_type G t T p fr a e ->
    env_cap G p false ->
    env_type M H1 H2 V1 V2 G u (plift p) -> 
    u=true -> psub (exp_locs V1 t) pempty /\ psub (exp_locs V2 t) pempty .
Proof.
  intros. eapply hast_fv1'. eauto. eauto.
  destruct H3 as (?&?&?&?&?&?). split. eauto. split. eauto.
  intros. edestruct H9 as (?&?&?&?&?&?&?&?&?&?&?&?&?&?). eauto.
  eapply H0 in H10. 
  eexists _,_. intuition eauto.
Qed.


(* ---------- LR helper lemmas  ---------- *)

Lemma stchain_refl: forall M,
    st_chain M M.
Proof.
  intros. unfold st_chain. eauto. 
Qed.

Lemma stchain_extend: forall M,
    stty_wellformed M ->
    st_chain M (st_extend M).
Proof.
  intros. unfold st_chain, st_extend, st_extend'. 
  - intros U. intros. unfold strel at 1.
    right. destruct H as (L1 & L2 & L3). 
    edestruct L1 as (? & ?). eauto. intuition. 
Qed.

Lemma stchain_pad: forall L1 L2 M,
    st_chain M (st_pad L1 L2 M).
Proof.
  intros. unfold st_chain, st_pad. 
  - intros. unfold strel at 1. simpl. eauto. 
Qed.

Lemma stchain_pad': forall L1 L2 M,
    st_chain (st_pad L1 L2 M) M.
Proof.
  intros. unfold st_chain, st_pad. 
  - intros. unfold strel at 1. simpl. eauto. 
Qed.

Lemma stchain_step: forall M M' b,
    st_chain M M' ->
    st_chain M (st_step M M' b).
Proof.
  intros. unfold st_chain, st_step. 
  - intros. destruct b. eauto. unfold strel at 1. simpl. eauto.
Qed.

Lemma stchain_chain: forall M1 M2 M3,
    st_chain M1 M2 ->
    st_chain M2 M3 ->
    st_chain M1 M3.
Proof.
  intros. unfold st_chain, st_chain in *. 
  intuition. 
Qed.


Lemma envt_empty: forall u p,
    env_type st_empty [] [] [] [] [] u p.
Proof.
  intros. split. 2: split. 3: split. 4: split. 5: split. 
  eauto. eauto. eauto. eauto. eauto.
  intros. inversion H. 
Qed.


Lemma envt_extend: forall M H1 H2 V1 V2 G v1 v2 T1 u u0 ls1 ls2 fr1 a1 p,
    env_type M H1 H2 V1 V2 G u0 p ->
    val_type M v1 v2 T1 (u=true) ls1 ls2 ->
    (u = negb(fr1||a1) || u0) ->
    ((fr1||a1 = false \/ u0=false) -> psub (plift ls1) pempty) ->
    ((fr1||a1 = false \/ u0=false) -> psub (plift ls2) pempty) ->
    env_type M (v1::H1) (v2::H2) (ls1::V1) (ls2::V2) ((T1,fr1,a1)::G) u0 (por p (pone (length G))).
Proof.
  intros. 
  remember H as WFE. clear HeqWFE.
  destruct H as (LH1 & LH2 & LV1 & LV2 & LW & ?). split. 2: split. 3: split. 4: split. 5: split. 
  simpl. eauto. simpl. eauto. simpl. eauto. simpl. eauto. simpl. eauto. 
  intros x T fr a IX. bdestruct (x =? length G).
  - subst x. rewrite indexr_head in IX. inversion IX. subst T1.
    exists v1, v2, u, ls1, ls2. split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 8: split. 
    rewrite <- LH1. rewrite indexr_head. eauto.
    rewrite <- LH2. rewrite indexr_head. eauto.
    rewrite <- LV1. rewrite indexr_head. eauto.
    rewrite <- LV2. rewrite indexr_head. eauto.
    eauto. 
    subst fr1 a1. eauto. 
    subst fr1 a1. eauto.
    subst fr1 a1. eauto. 
    subst fr1 a1. eauto.
  - rewrite indexr_skip in IX; eauto.
    eapply WFE in IX as IX. destruct IX as (v1' & v2' & u' & ls1' & ls2' & ? & ? & ? & ? & ? & ? & ? & ? & ?).
    exists v1', v2', u', ls1', ls2'. split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 8: split. 
    rewrite indexr_skip; eauto. lia.
    rewrite indexr_skip; eauto. lia.
    rewrite indexr_skip; eauto. lia.
    rewrite indexr_skip; eauto. lia.
    eauto. 
    eauto. 
    intros Q. destruct Q as [Q|Q]. eauto. inversion Q. lia.
    eauto.
    eauto.
Qed.


Lemma sttyw_empty:
    stty_wellformed st_empty.
Proof.
  intros. split. 2: split.
  - intros. inversion H.
  - intros. inversion H.
  - intros. inversion H. 
Qed.

Lemma storet_empty: forall p1 p2, 
    store_type [] [] st_empty p1 p2.
Proof.
  intros. split. 2: split.
  - eauto.
  - eauto.
  - intros. inversion H. 
Qed.

Lemma sttyw_extend: forall M,
    stty_wellformed M ->
    stty_wellformed (st_extend M).
Proof.
  intros. destruct H as (L1 & L2 & L3).
  split. 2: split. 
  - intros. unfold st_len1, st_len2, st_extend, st_extend'. simpl. destruct H; lia. 
  - intros. destruct H, H0; intuition. eapply L2; eauto.
  - intros. destruct H, H0; intuition. eapply L3; eauto. 
Qed.

Lemma storet_extend: forall S1 S2 M vx1 vx2 ux lsx1 lsx2 p1 p2,
    store_type S1 S2 M p1 p2 ->
    val_type M vx1 vx2 TBool ux lsx1 lsx2 ->
    store_type (vx1 :: S1) (vx2 :: S2) (st_extend M)
      (por p1 (pone (length S1))) (por p2 (pone (length S2))).
Proof.
  intros. destruct H as (L1 & L2 & L3).
  split. 2: split.
  - simpl. rewrite L1. unfold st_len1, st_extend, st_extend'. eauto.
  - simpl. rewrite L2. unfold st_len2, st_extend, st_extend'. eauto. 
  - intros. destruct vx1, vx2; inversion H0.
      subst b0. simpl in H. destruct H.
    + exists b. destruct H. subst l1 l2.
      rewrite <-L1, <-L2, indexr_head, indexr_head; eauto.
    + edestruct L3 as (? & ? & ?). eauto. eapply H.
      destruct H1. eauto. inversion H1. lia.
      destruct H2. eauto. inversion H2. lia. 
      exists x. rewrite indexr_skip, indexr_skip; intuition. 
Qed.

Lemma sttyw_pad: forall L1 L2 M,
    stty_wellformed M ->
    stty_wellformed (st_pad L1 L2 M).
Proof.
  intros. destruct H as (F1 & F2 & F3).
  split. 2: split. 
  - intros. unfold st_pad, st_len1, st_len2, st_pad, strel in *. simpl in *.
    edestruct F1. eauto. split; lia. 
  - intros. eapply F2; eauto.
  - intros. eapply F3; eauto. 
Qed.

Lemma sttyw_step: forall M M' b,
    stty_wellformed M ->
    stty_wellformed M' ->
    st_len1 M <= st_len1 M' ->
    st_len2 M <= st_len2 M' ->
    stty_wellformed (st_step M M' b).
Proof.
  intros. unfold st_step. destruct b. eauto.
  destruct H as (W1 & W2 & W3). 
  split. 2: split.
  - simpl. intros. eapply W1 in H.
    unfold st_len1 in *. simpl. intuition.
    unfold st_len2 in *. simpl. intuition.
  - simpl. intros. eapply W2; eauto.
  - simpl. intros. eapply W3; eauto. 
Qed.

Lemma storet_pad: forall SD1 SD2 S1 S2 M p1 p2,
    stty_wellformed M ->
    store_type S1 S2 M p1 p2 ->
    store_type (SD1++S1) (SD2++S2) (st_pad (length SD1) (length SD2) M)
      (por p1 (pdiff (pdom (SD1++S1)) (pdom S1)))
      (por p2 (pdiff (pdom (SD2++S2)) (pdom S2))).
Proof.
  intros ??????? SW ST.
  destruct SW as (SW & ? & ?).
  destruct ST as (F1 & F2 & F3).
  split. 2: split.
  - rewrite app_length. unfold st_pad, st_len1, st_len2 in *. simpl. lia.
  - rewrite app_length. unfold st_pad, st_len1, st_len2 in *. simpl. lia. 
  - intros. simpl in *. eapply SW in H1 as W. 
    destruct H2, H3.
    + eapply F3 in H1. destruct H1 as (b & IX1 & IX2).
      exists b. rewrite indexr_skips. rewrite indexr_skips. intuition.
      eapply indexr_var_some' in IX2. eauto.
      eapply indexr_var_some' in IX1. eauto.
      eauto. eauto.
    + unfoldq. intuition.
    + unfoldq. intuition.
    + unfoldq. intuition. 
Qed.

Lemma storet_pad': forall S1 S1' S2 S2' M p1 p2,
    stty_wellformed M ->
    store_type S1 S2 M p1 p2 ->
    length S1 <= length S1' ->
    length S2 <= length S2' ->
    store_write S1 S1' (pnot p1) ->  
    store_write S2 S2' (pnot p2) ->  
    store_type S1' S2' (length S1', length S2', strel M)
      (por p1 (pdiff (pdom S1') (pdom S1)))
      (por p2 (pdiff (pdom S2') (pdom S2))).
Proof.
  intros ??????? SW ST L1 L2 ES1 ES2.
  destruct SW as (SW & ? & ?).
  destruct ST as (F1 & F2 & F3).
  split. 2: split.
  - unfold st_len1, st_len2 in *. simpl. lia.
  - unfold st_len1, st_len2 in *. simpl. lia. 
  - intros. simpl in *. eapply SW in H1 as W. 
    destruct H2, H3.
    + eapply F3 in H1; eauto.
      destruct H1 as (b & IX1 & IX2).
      rewrite ES1 in IX1.
      rewrite ES2 in IX2. 
      exists b. intuition.
      unfoldq. intuition.
      unfoldq. intuition. 
    + unfoldq. intuition.
    + unfoldq. intuition.
    + unfoldq. intuition. 
Qed.

Lemma storet_step: forall S1 S2 M M' p1 p2 b,
    store_type S1 S2 M' p1 p2 ->
    st_chain M M' ->
    store_type S1 S2 (st_step M M' b) p1 p2.
Proof.
  intros. destruct b; simpl. eauto.
  destruct H as (?&?&?).
  split. eauto. split. eauto.
  intros. eapply H2; eauto.
Qed.


Lemma storet_update: forall S1 S2 M l1 l2 vx1 vx2 ux lsx1 lsx2 p1 p2,
    stty_wellformed M ->
    store_type S1 S2 M p1 p2 ->
    ((l1 < length S1 \/ l2 < length S2) -> strel M l1 l2) ->
    val_type M vx1 vx2 TBool ux lsx1 lsx2 ->
    store_type (update S1 l1 vx1) (update S2 l2 vx2) M p1 p2.
Proof.
  intros.
  destruct H as (F1 & F2 & F3 ).
  destruct H0 as (L1 & L2 & L3 ).
  destruct vx1, vx2; inversion H2.
  split. 2: split.
  - rewrite <-update_length. eauto.
  - rewrite <-update_length. eauto. 
  - intros.
    bdestruct (l0 =? l1); bdestruct (l3 =? l2).
    + subst l0 l3. eexists. rewrite update_indexr_hit, update_indexr_hit; intuition.
      eapply F1 in H0. rewrite L2. eapply H0.
      eapply F1 in H0. rewrite L1. eapply H0. 
    + destruct (L3 _ _ H0) as (b' & IX1 & IX2); eauto.
      eapply indexr_var_some' in IX1, IX2. 
      subst l0. destruct H6. eapply F2; eauto.
    + destruct (L3 _ _ H0) as (b' & IX1 & IX2); eauto.
      eapply indexr_var_some' in IX1, IX2.
      subst l3. destruct H5. eapply F3; eauto.
    + rewrite update_indexr_miss, update_indexr_miss; eauto.
Qed.

Lemma storet_tighten: forall S1 S2 M p1 p2 p1' p2', 
    store_type S1 S2 M p1 p2 ->
    psub p1' p1 ->
    psub p2' p2 ->
    store_type S1 S2 M p1' p2'.
Proof.
  intros. destruct H as (? & ? & ?). split. 2: split.
  - eauto.
  - eauto.
  - intros. eapply H3; eauto. 
Qed.


Lemma valt_store_change: forall M M' vx1 vx2 ux lsx1 lsx2 T,
    val_type M vx1 vx2 T ux lsx1 lsx2 ->
    (ux -> st_chain_partial M M' (plift lsx1) (plift lsx2)) ->
    st_len1 M <= st_len1 M' -> 
    st_len2 M <= st_len2 M' ->
    val_type M' vx1 vx2 T ux lsx1 lsx2.
Proof.
  intros. destruct vx1, vx2, T; simpl in H; try contradiction.
  - simpl. eauto.
  - simpl. intros. intuition. 
  - simpl. intros.
    destruct (H S1' S2' M'0 p1 p2 vx1 vx2 ux0 lsx0 lsx3 uy uyv) as (S1'' & S2'' & M'' &?&?&?&?&?); eauto.
    intros ??????. eapply H3. eauto.  eapply H0. eauto. eauto. eauto. eauto. eauto. eauto.
    lia. lia. 
    eexists S1'', S2'', M'', _,_,_,_. intuition. 5: eauto. all: eauto.
Qed.

Lemma valt_usable: forall M vx1 vx2 ux (ux': Prop) lsx1 lsx2 T,
    val_type M vx1 vx2 T ux lsx1 lsx2 ->
    (ux' -> ux) ->
    val_type M vx1 vx2 T ux' lsx1 lsx2.
Proof.
  intros. destruct vx1, vx2, T; simpl in H; try contradiction.
  - simpl. eauto.
  - simpl. intuition.
  - simpl. intros.
    destruct (H S1' S2' M' p1 p2 vx1 vx2 ux0 lsx0 lsx3 uy uyv) as (S1'' & S2'' & M'' &?&?&?&?&?); eauto.
Qed.


Lemma valt_reset_locs: forall T M vx1 vx2 ux lsx1 lsx2,
    val_type M vx1 vx2 T ux lsx1 lsx2 ->
    (ux -> False) ->
    val_type M vx1 vx2 T ux qempty qempty.
Proof.
  intros T. destruct T,vx1, vx2; simpl in *; try contradiction.
  - simpl. eauto.
  - simpl. intros.
    remember (b3||uy&&b2) as D. destruct D.
    + destruct (H S1' S2' M' p1 p2 vx1 vx2 ux0 lsx0 lsx3 uy uyv) as (S1'' & S2'' & M'' & vy1 & vy2 & lsy1 & lsy2 &?); eauto.
      intros. intuition.
      intros ? Q. destruct b3; intuition.
      intros ? Q. destruct b3; intuition.

      eexists S1'', S2'', M'', vy1, vy2, lsy1, lsy2.
      intuition.
    + assert (b3=false). destruct b3; intuition.
      assert (uy && b2=false). destruct b2,uy; simpl in *; intuition.
      assert (uy = false \/ b2 = false). destruct b2,uy; intuition.
      destruct H18.
      * destruct (H S1' S2' M' p1 p2 vx1 vx2 ux0 lsx0 lsx3 uy uyv) as (S1'' & S2'' & M'' & vy1 & vy2 & lsy1 & lsy2 &?); eauto.
        intros. rewrite H16, H17 in H19. inversion H19. 
        intros ? Q. destruct b3; intuition.
        intros ? Q. destruct b3; intuition.
        eexists S1'', S2'', M'', vy1, vy2, lsy1, lsy2.
        intuition.
        intros ? Q. eapply H33 in Q. contradiction.
        intros ? Q. eapply H26 in Q. contradiction.
        intros ? Q. destruct Q. destruct b3; intuition.
        eapply H31. split; intuition. 
        intros ? Q. destruct Q. destruct b3; intuition.
        eapply H32. split; intuition.
      * destruct (H S1' S2' M' p1 p2 vx1 vx2 ux0 lsx0 lsx3 uy uyv) as (S1'' & S2'' & M'' & vy1 & vy2 & lsy1 & lsy2 &?); eauto.
        intros. rewrite H16, H17 in H19. inversion H19. 
        intros ? Q. destruct b3; intuition.
        intros ? Q. destruct b3; intuition.
        eexists S1'', S2'', M'', vy1, vy2, lsy1, lsy2.
        intuition.
        intros ? Q. eapply H29 in Q. subst b2. intuition.
        intros ? Q. eapply H30 in Q. subst b2. intuition. 
        intros ? Q. destruct Q. destruct b3; intuition.
        eapply H31. split; intuition. 
        intros ? Q. destruct Q. destruct b3; intuition.
        eapply H32. split; intuition.
Qed.

Lemma valt_store_reset: forall M M' vx1 vx2 ux lsx1 lsx2 T,
    val_type M vx1 vx2 T ux lsx1 lsx2 ->
    (ux -> psub (plift lsx1) pempty) ->
    (ux -> psub (plift lsx2) pempty) ->
    st_len1 M <= st_len1 M' -> 
    st_len2 M <= st_len2 M' ->    
    val_type M' vx1 vx2 T ux lsx1 lsx2.
Proof.
  intros. destruct vx1, vx2, T; simpl in H; try contradiction.
  - simpl. eauto.
  - simpl. intuition. eapply H6 in H5. contradiction. 
  - simpl. intros.
    destruct (H S1' S2' M'0 p1 p2 vx1 vx2 ux0 lsx0 lsx3 uy uyv) as (S1'' & S2'' & M'' &?&?&?); eauto.
    intros ??????. eapply H0 in H21. contradiction. eauto. lia. lia. 

    eexists S1'', S2'', M'', _,_. intuition. all: eauto.
Qed.

Lemma envt_store_change: forall M M' H1 H2 V1 V2 G uw p,
    env_type M H1 H2 V1 V2 G uw p ->
    (st_chain_partial M M' (vars_locs V1 p) (vars_locs V2 p)) ->
    st_len1 M <= st_len1 M' -> 
    st_len2 M <= st_len2 M' ->
    env_type M' H1 H2 V1 V2 G uw p.
Proof.
  intros. destruct H as (LH1 & LH2 & LV1 & LV2 & LW & IX).
  split. 2: split. 3: split. 4: split. 5: split. 
  - eauto.
  - eauto.
  - eauto.
  - eauto.
  - eauto.
  - intros. edestruct IX as (v1 & v2 & u & ls1 & ls2 & IX1' & IX2' & IV1' & IV2' & IW' & UX & VX & VQ1 & VQ2). eauto.
    exists v1, v2, u, ls1, ls2. split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 8: split. 
    eauto. eauto. eauto. eauto. eauto. eauto. 
    intros. eapply valt_store_change. eauto. intros. 
    intros ?????.
    assert (uw=true). { subst u. destruct fr,a; simpl in H6; eauto. eapply VQ1 in H8. contradiction. eauto. }
    eapply H0. eauto.
    eexists. split. eauto. eexists. split. eauto. eauto.
    eexists. split. eauto. eexists. split. eauto. eauto.
    eauto. eauto. eauto. eauto.
Qed.

Lemma envt_store_reset: forall M M' H1 H2 V1 V2 G uw,
    env_type M H1 H2 V1 V2 G uw pempty ->
    st_len1 M <= st_len1 M' -> 
    st_len2 M <= st_len2 M' ->
    env_type M' H1 H2 V1 V2 G uw pempty.
Proof.
  intros. destruct H as (LH1 & LH2 & LV1 & LV2 & LW & IX).
  split. 2: split. 3: split. 4: split. 5: split. 
  - eauto.
  - eauto.
  - eauto.
  - eauto.
  - eauto.
  - intros. edestruct IX as (v1 & v2 & u & ls1 & ls2 & IX1' & IX2' & IV1' & IV2' & IW' & UX & VX & VQ1 & VQ2). eauto.
    exists v1, v2, u, ls1, ls2. split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 8: split.
    eauto. eauto. eauto. eauto. eauto. eauto.
    intros. contradiction.
    eauto. eauto. 
Qed.


Lemma storet_combine: forall S1 S2 M S1' S2' M' e,
    stty_wellformed M ->
    store_type S1 S2 M (pdom S1) (pdom S2) ->
    store_type S1' S2' M'
    (pdiff (pdom S1') (pif (negb e) (pdom S1)))
    (pdiff (pdom S2') (pif (negb e) (pdom S2))) ->
    (e = false ->
       exists SD1 SD2 : list vl,
         M' = st_pad (length SD1) (length SD2) M /\ S1' = SD1 ++ S1 /\ S2' = SD2 ++ S2) ->   
    store_type S1' S2' M' (pdom S1') (pdom S2').
Proof.
  intros ??????? SW ST ST' EX.
  destruct ST as (L1 & L2 & L3).
  destruct ST' as (L1' & L2' & L3').
  split. 2: split.
  eauto. eauto. intros.
  destruct e. eapply L3'. eauto.
  unfold pdiff, pdom, pif, negb. intuition.
  unfold pdiff, pdom, pif, negb. intuition.
  destruct EX as (SD1 & SD2 & MM & ? & ?). eauto. subst M'. 
  edestruct L3 as (b & ? & ?). eapply H.
  unfold pdom. rewrite L1. eapply SW. eapply H.
  unfold pdom. rewrite L2. eapply SW. eapply H.
  exists b. subst S1' S2'. split.
  rewrite indexr_skips. eauto. rewrite L1. eapply SW. eauto.
  rewrite indexr_skips. eauto. rewrite L2. eapply SW. eauto.
Qed.

Lemma storet_combine': forall S1 S2 M S1' S2' M' e,
    stty_wellformed M ->
    store_type S1 S2 M (pif true (pdom S1)) (pif true (pdom S2)) ->
    store_type S1' S2' M'
    (pdiff (pdom S1') (pif (negb e) (pdom S1)))
    (pdiff (pdom S2') (pif (negb e) (pdom S2))) ->
    (e = false ->
       exists SD1 SD2 : list vl,
         M' = st_pad (length SD1) (length SD2) M /\ S1' = SD1 ++ S1 /\ S2' = SD2 ++ S2) ->   
    store_type S1' S2' M' (pdom S1') (pdom S2').
Proof.
  intros. eapply storet_combine; eauto.
Qed.

Lemma storew_widen: forall S1 S1' p p',
    store_write S1 S1' p ->
    psub p p' ->
    store_write S1 S1' p'.
Proof.
  intros. intros ? Q. eapply H. unfoldq. intuition. 
Qed.

Lemma storew_trans: forall S1 S1' S1'' p,
    store_write S1 S1' p ->
    store_write S1' S1'' p ->
    length S1 <= length S1' ->
    store_write S1 S1'' p.
Proof.
  intros. intros ? (Q1 & Q2).
  rewrite H, H0. eauto. split; eauto.
  unfoldq. lia. split; eauto. 
Qed.

Lemma storew_refl: forall S1 p,
    store_write S1 S1 p.
Proof.
  intros. intros ? (Q&?). eauto. 
Qed.

Lemma storew_extend: forall S1 S1' v p,
    store_write S1 S1' p ->
    length S1 <= length S1' ->
    store_write S1 (v::S1') p.
Proof.
  intros. intros ? (Q&?).
  rewrite H. rewrite indexr_skip. eauto.
  unfoldq. lia. split; eauto. 
Qed.


Lemma valt_sub_locs: forall T M v1 v2 u ls1 ls2 ls1' ls2',
    val_type M v1 v2 T u ls1 ls2 ->
    psub (plift ls1) (plift ls1') ->
    psub (plift ls2) (plift ls2') ->
    val_type M v1 v2 T u ls1' ls2'.
Proof.
  intros T. induction T; intros; destruct v1, v2; simpl in *; try contradiction.
  - eauto.
  - intuition.
  - intros. destruct (H S1' S2' M' p1 p2 vx1 vx2 ux lsx1 lsx2 uy uyv) as (S1'' & S2'' & M'' & vy1 & vy2 & lsy1 & lsy2 &?&?&?&?&?&?&?&?&?&?& LY1 & LY2 &?&?&?).
    + intros ??????. eapply H2; eauto.
    + eauto.
    + eauto.
    + eauto.
    + eauto.
    + eauto.
    + eauto.
    + eauto.
    + eauto.
    + eauto.
    + unfoldq. destruct b3; intuition.
    + unfoldq. destruct b3; intuition.
    + eauto.
    + eauto.
    + eauto.
    + exists S1'', S2'', M'', vy1, vy2, lsy1, lsy2.
      split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 8: split. 9: split.
      10: split. 11: split. 12: split. 13: split. 14: split. 
      * eauto.
      * eauto.
      * eauto.
      * eauto.
      * eauto.
      * eauto.
      * eauto.
      * eauto.
      * eauto.
      * eauto.      
      * intros ? Q. eapply LY1 in Q. unfoldq. destruct b2; intuition.
      * intros ? Q. eapply LY2 in Q. unfoldq. destruct b2; intuition.
      * eapply storew_widen. eauto. unfoldq. destruct b3; intuition.
      * eapply storew_widen. eauto. unfoldq. destruct b3; intuition.
      * eauto. 
Qed.



(* ---------- LR compatibility lemmas  ---------- *)

Lemma exp_sub_eff1: forall S1 S2 M H1 H2 V1 V2 S1' S2' M' t1 t2 T u p1 p2 fr a e,
    stty_wellformed M ->
    store_type S1 S2 M p1 p2 -> 
    exp_type1 S1 S2 M H1 H2 V1 V2 t1 t2 S1' S2' M' T u p1 p2 fr a e ->
    exp_type1 S1 S2 M H1 H2 V1 V2 t1 t2 S1' S2' M' T u p1 p2 fr a true.
Proof.
  intros ??????????????????? SW ST HX. destruct e. eauto. 
  destruct HX as (v1 & v2 & uv & ls1 & ls2 & SC' & SW' & TX1 & TX2 & LS1 & LS2 & ST' & VX & UV1 & UV2 & LX1 & LX2 & ES1 & ES2 & ESM).
  exists v1, v2, uv, ls1, ls2. unfold exp_type2. intuition.
  eapply storew_widen. eauto. unfoldq. intuition.
  eapply storew_widen. eauto. unfoldq. intuition. 
Qed.

Lemma exp_sub_eff: forall S1 S2 M H1 H2 V1 V2 t1 t2 T u p1 p2 fr a e,
    stty_wellformed M ->
    store_type S1 S2 M p1 p2 -> 
    exp_type S1 S2 M H1 H2 V1 V2 t1 t2 T u p1 p2 fr a e ->
    exp_type S1 S2 M H1 H2 V1 V2 t1 t2 T u p1 p2 fr a true.
Proof.
  intros ???????????????? SW ST HX. destruct HX as (S1' & S2' & M' & REST). 
  exists S1', S2', M'. eapply exp_sub_eff1; eauto. 
Qed.

Lemma exp_sub_fresh1: forall S1 S2 M H1 H2 V1 V2 S1' S2' M' t1 t2 T u p1 p2 fr a e,
    stty_wellformed M ->
    store_type S1 S2 M p1 p2 -> 
    exp_type1 S1 S2 M H1 H2 V1 V2 t1 t2 S1' S2' M' T u p1 p2 fr a e ->
    exp_type1 S1 S2 M H1 H2 V1 V2 t1 t2 S1' S2' M' T u p1 p2 true a e.
Proof.
  intros ??????????????????? SW ST HX. destruct fr. eauto. 
  destruct HX as (v1 & v2 & uv & ls1 & ls2 & SC' & SW' & TX1 & TX2 & LS1 & LS2 & ST' & VX & UV1 & UV2 & LUX1 & LUX2 & LX1 & LX2 & ES1 & ES2 & ESM).
  exists v1, v2, uv, ls1, ls2. unfold exp_type2. intuition.
  intros ? Q. eapply LX1 in Q. unfoldq. intuition.
  intros ? Q. eapply LX2 in Q. unfoldq. intuition.
Qed.

Lemma exp_sub_fresh: forall S1 S2 M H1 H2 V1 V2 t1 t2 T u p1 p2 fr a e,
    stty_wellformed M ->
    store_type S1 S2 M p1 p2 -> 
    exp_type S1 S2 M H1 H2 V1 V2 t1 t2 T u p1 p2 fr a e ->
    exp_type S1 S2 M H1 H2 V1 V2 t1 t2 T u p1 p2 true a e.
Proof.
  intros ???????????????? SW ST HX. destruct HX as (S1' & S2' & M' & REST). 
  exists S1', S2', M'. eapply exp_sub_fresh1; eauto. 
Qed.

Lemma exp_sub_cap1: forall S1 S2 M H1 H2 V1 V2 S1' S2' M' t1 t2 T u p1 p2 fr a e,
    stty_wellformed M ->
    store_type S1 S2 M p1 p2 -> 
    exp_type1 S1 S2 M H1 H2 V1 V2 t1 t2 S1' S2' M' T u p1 p2 fr a e ->
    exp_type1 S1 S2 M H1 H2 V1 V2 t1 t2 S1' S2' M' T u p1 p2 fr true e.
Proof.
  intros ??????????????????? SW ST HX. destruct a. eauto. 
  destruct HX as (v1 & v2 & uv & ls1 & ls2 & SC' & SW' & TX1 & TX2 & LS1 & LS2 & ST' & VX & UV1 & UV2 & LUX1 & LUX2 & LX1 & LX2 & ES1 & ES2 & ESM).
  assert (uv = true). destruct u,uv; intuition. rewrite H in *.
  destruct u. 
  exists v1, v2, true, ls1, ls2. unfold exp_type2. intuition.

  intros ? Q. eapply LX1 in Q. unfoldq. intuition.
  intros ? Q. eapply LX2 in Q. unfoldq. intuition.

  exists v1, v2, false, qempty, qempty. unfold exp_type2. intuition.
  eapply valt_reset_locs. eapply valt_usable. eauto. eauto. intuition.
  rewrite plift_empty. unfoldq. intuition.
  rewrite plift_empty. unfoldq. intuition.
  rewrite plift_empty. unfoldq. intuition.
  rewrite plift_empty. unfoldq. intuition.   
Qed.

Lemma exp_sub_cap: forall S1 S2 M H1 H2 V1 V2 t1 t2 T u p1 p2 fr a e,
    stty_wellformed M ->
    store_type S1 S2 M p1 p2 -> 
    exp_type S1 S2 M H1 H2 V1 V2 t1 t2 T u p1 p2 fr a e ->
    exp_type S1 S2 M H1 H2 V1 V2 t1 t2 T u p1 p2 fr true e.
Proof.
  intros ???????????????? SW ST HX. destruct HX as (S1' & S2' & M' & REST). 
  exists S1', S2', M'. eapply exp_sub_cap1; eauto. 
Qed.


Lemma exp_sub1: forall S1 S2 M S1' S2' M' H1 H2 V1 V2 t1 t2 T u p1 p2 fr fr' a a' e e',
    stty_wellformed M ->
    store_type S1 S2 M p1 p2 ->
    exp_type1 S1 S2 M H1 H2 V1 V2 t1 t2 T S1' S2' M' u p1 p2 fr a e ->
    bsub fr fr' ->
    bsub a a' ->
    bsub e e' ->
    exp_type1 S1 S2 M H1 H2 V1 V2 t1 t2 T S1' S2' M' u p1 p2 fr' a' e'.
Proof.
  intros. destruct fr,fr',a,a',e,e'; unfold bsub in *; intuition;
  try eapply exp_sub_eff1; try eapply exp_sub_cap1; try eapply exp_sub_fresh1; eauto.
Qed.

Lemma exp_sub: forall S1 S2 M H1 H2 V1 V2 t1 t2 T u p1 p2 fr fr' a a' e e',
    stty_wellformed M ->
    store_type S1 S2 M p1 p2 ->
    exp_type S1 S2 M H1 H2 V1 V2 t1 t2 T u p1 p2 fr a e ->
    bsub fr fr' ->
    bsub a a' ->
    bsub e e' ->
    exp_type S1 S2 M H1 H2 V1 V2 t1 t2 T u p1 p2 fr' a' e'.
Proof.
  intros. destruct H3 as (?&?&?&?).
  eexists _,_,_. eapply exp_sub1; eauto. 
Qed.


Lemma exp_true: forall S1 S2 M H1 H2 V1 V2 p1 p2 uv,
    stty_wellformed M ->
    store_type S1 S2 M p1 p2 ->
    exp_type S1 S2 M H1 H2 V1 V2 ttrue ttrue TBool uv p1 p2 false false false.
Proof.
  intros ?????????? SW ST. 
  exists S1, S2, M, (vbool true), (vbool true), true, qempty, qempty.
  split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 8: split. 9: split. 10: split.
  11: split. 12: split. 13: split. 14: split. 15: split. 16: split. 
  - eapply stchain_refl.
  - eauto. 
  - exists 0. intros. destruct n. lia. simpl. eauto.
  - exists 0. intros. destruct n. lia. simpl. eauto.
  - eauto.
  - eauto. 
  - eapply storet_tighten. eauto.
    unfoldq. intuition.
    unfoldq. intuition. 
  - simpl. eauto.
  - destruct uv; eauto.
  - eauto.
  - unfoldq. intuition.
  - unfoldq. intuition. 
  - unfoldq. intuition.
  - unfoldq. intuition.
  - eapply storew_refl.
  - eapply storew_refl. 
  - eauto.
Qed.

Lemma exp_false: forall S1 S2 M H1 H2 V1 V2 p1 p2 uv,
    stty_wellformed M ->
    store_type S1 S2 M p1 p2 ->
    exp_type S1 S2 M H1 H2 V1 V2 tfalse tfalse TBool uv p1 p2 false false false.
Proof.
  intros ?????????? SW ST. 
  exists S1, S2, M, (vbool false), (vbool false), true, qempty, qempty.
  split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 8: split. 9: split. 10: split. 
  11: split. 12: split. 13: split. 14: split. 15: split. 16: split. 
  - eapply stchain_refl.
  - eauto. 
  - exists 0. intros. destruct n. lia. simpl. eauto.
  - exists 0. intros. destruct n. lia. simpl. eauto.
  - eauto.
  - eauto. 
  - eapply storet_tighten. eauto.
    unfoldq. intuition.
    unfoldq. intuition.
  - simpl. eauto.
  - destruct uv; eauto.
  - eauto. 
  - unfoldq. intuition.
  - unfoldq. intuition.
  - unfoldq. intuition.
  - unfoldq. intuition.
  - eapply storew_refl.
  - eapply storew_refl. 
  - eauto.
Qed.

Lemma exp_var: forall S1 S2 M H1 H2 V1 V2 x1 x2 v1 v2 ls1 ls2 T uv u p1 p2 a,
    indexr x1 H1 = Some v1 ->
    indexr x2 H2 = Some v2 ->
    (a = false \/ uv = true -> indexr x1 V1 = Some ls1) ->
    (a = false \/ uv = true -> indexr x2 V2 = Some ls2) ->
    val_type M v1 v2 T (u=true) ls1 ls2 ->
    (a = false \/ uv = false -> psub (plift ls1) pempty) ->
    (a = false \/ uv = false -> psub (plift ls2) pempty) ->
    stty_wellformed M ->
    store_type S1 S2 M p1 p2 ->
    u = negb a || uv ->
    exp_type S1 S2 M H1 H2 V1 V2 (tvar x1) (tvar x2) T uv p1 p2 false a false.
Proof.
  intros ??????????????????? IX1 IX2 IV1 IV2 VX VQ1 VQ2 SW ST UV. 
  exists S1, S2, M, v1, v2, u, ls1, ls2.
  split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 8: split. 9: split. 10: split. 
  11: split. 12: split. 13: split. 14: split. 15: split. 16: split. 
  - eapply stchain_refl.
  - eauto.
  - exists 0. intros. destruct n. lia. simpl. rewrite IX1. eauto.
  - exists 0. intros. destruct n. lia. simpl. rewrite IX2. eauto.
  - eauto.
  - eauto. 
  - eapply storet_tighten. eauto.
    unfoldq. intuition.
    unfoldq. intuition.
  - destruct M as ((?&?)&?). unfold st_pad, st_len1, st_len2. simpl. eauto.
  - simpl. eauto.
  - eauto.
  - destruct a,uv; eauto.
  - destruct a,uv; eauto. 
  - intros ??. destruct a. destruct uv. 
    left. eapply exp_locs_var; eauto.
    edestruct VQ1; eauto.
    edestruct VQ1; eauto.
  - intros ??. destruct a. destruct uv.
    left. eapply exp_locs_var; eauto.
    edestruct VQ2; eauto.
    edestruct VQ2; eauto.
  - eapply storew_refl.
  - eapply storew_refl. 
  - eauto.
Qed.

Lemma exp_ref: forall S1 S2 M H1 H2 V1 V2 t1 t2 p1 p2 fr a e uv,
    exp_type S1 S2 M H1 H2 V1 V2 t1 t2 TBool uv p1 p2 fr a e ->
    exp_type S1 S2 M H1 H2 V1 V2 (tref t1) (tref t2) TRef uv p1 p2 true false e.
Proof.
  intros ??????????????? HX. 
  destruct HX as (S1' & S2' & M' & vx1 & vx2 & ux & lsx1 & lsx2 & SC' & SW' & TX1 & TX2 & LS1 & LS2 & ST' & VX & UX1 & UX2 & LUX1 & LUX2 & LX1 & LX2 & ES1 & ES2 & ESM).
  exists (vx1::S1'), (vx2::S2'), (st_extend M').
  exists (vref (length S1')), (vref (length S2')).
  eexists true. 
  exists (qone (length S1')), (qone (length S2')).
  split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 8: split. 9: split. 10: split. 
  11: split. 12: split. 13: split. 14: split. 15: split. 16: split. 
  - eapply stchain_chain; eauto.
    eapply stchain_extend; eauto.
  - eapply sttyw_extend; eauto.
  - destruct TX1 as (n1 & TX).
    exists (1+n1). intros. destruct n. lia. simpl. rewrite TX. eauto. lia.
  - destruct TX2 as (n1 & TX).
    exists (1+n1). intros. destruct n. lia. simpl. rewrite TX. eauto. lia.
  - simpl. lia.
  - simpl. lia.      
  - eapply storet_tighten. eapply storet_extend. eauto. eauto.
    unfoldq. simpl. intros ? [Q|Q]. eauto. lia.
    unfoldq. simpl. intros ? [Q|Q]. eauto. lia.
  - simpl. destruct ST' as (L1 & L2 & L3).
    rewrite plift_one, plift_one. intuition.
  - destruct uv; eauto. 
  - eauto.
  - intuition.
  - intuition. 
  - rewrite plift_one. unfoldq. simpl. intuition.
  - rewrite plift_one. unfoldq. simpl. intuition.
  - rewrite exp_locs_ref. eapply storew_extend. eauto. eauto. 
  - rewrite exp_locs_ref. eapply storew_extend. eauto. eauto. 
  - intros C. inversion C.
Qed.

Lemma exp_get: forall S1 S2 M H1 H2 V1 V2 t1 t2 p1 p2 uv fr a e,
    stty_wellformed M ->
    store_type S1 S2 M p1 p2 ->
    psub (pif (e||a) (exp_locs V1 t1)) p1 ->
    psub (pif (e||a) (exp_locs V2 t2)) p2 ->
    bsub (e||a) uv ->
    exp_type S1 S2 M H1 H2 V1 V2 t1 t2 TRef uv p1 p2 fr a e ->
    exp_type S1 S2 M H1 H2 V1 V2 (tget t1) (tget t2) TBool uv p1 p2 false false (e||a).
Proof.
  intros ??????????????? SW ST P1 P2 E HX. 
  destruct HX as (S1' & S2' & M' & vx1 & vx2 & ux & lsx1 & lsx2 & SC' & SW' & TX1 & TX2 & LS1 & LS2 & ST' & VX & UX1 & UX2 & LUX1 & LUX2 & LX1 & LX2 & ES1 & ES2 & EM).
  destruct vx1, vx2; simpl in VX; try contradiction.
  destruct ux. 2: {
  assert (uv = false). destruct uv; intuition.
  assert (a = true). destruct uv,a; intuition.
  unfold bsub in *. destruct e,a,uv; intuition. }

  destruct VX as (VX & LV1 & LV2). eauto.
  destruct ST' as (L1 & L2 & L3).
  destruct (L3 _ _ VX) as (b & IX1 & IX2).
  edestruct (LX1 i) as [|[|]]. eauto. 
  destruct a. 2: simpl; contradiction. left. eapply P1. destruct e; eauto.
  contradiction.
  destruct fr. 2: contradiction. right. eauto.
  edestruct (LX2 i0) as [|[|]]. eauto. 
  destruct a. 2: contradiction. left. eapply P2. destruct e; eauto.
  contradiction.
  destruct fr. 2: contradiction. right. eauto. 
  exists S1', S2', (st_step M M' false).
  exists (vbool b), (vbool b).
  exists true. 
  exists qempty, qempty.
  split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 8: split. 9: split. 10: split.
  11: split. 12: split. 13: split. 14: split. 15: split. 16: split. 
  - eapply stchain_step; eauto. 
  - eapply sttyw_step; eauto. destruct ST as (?&?&?). lia. destruct ST as (?&?&?). lia. 
  - destruct TX1 as (n1 & TX).
    exists (1+n1). intros. destruct n. lia. simpl. rewrite TX. rewrite IX1. eauto. lia.
  - destruct TX2 as (n1 & TX).
    exists (1+n1). intros. destruct n. lia. simpl. rewrite TX. rewrite IX2. eauto. lia.
  - eauto.
  - eauto.
  - repeat split; eauto. 
  - simpl. eauto.
  - destruct uv; eauto.
  - eauto.
  - intuition.
  - intuition. 
  - simpl. intros ??. intuition.
  - simpl. intros ??. intuition.
  - rewrite exp_locs_get. eapply storew_widen. eauto. unfoldq. destruct a,e; intuition. 
  - rewrite exp_locs_get. eapply storew_widen. eauto. unfoldq. destruct a,e; intuition. 
  - intros C. intuition. 
Qed.

Lemma exp_put: forall S1 S2 M S1' S2' M' H1 H2 V1 V2 t1 t2 t1' t2' p1 p2 uv fr1 fr2 a1 a2 e1 e2,
    stty_wellformed M ->
    store_type S1 S2 M p1 p2 ->
    psub (pif (e1||e2||a1) (exp_locs V1 (tput t1 t1'))) p1 ->
    psub (pif (e1||e2||a1) (exp_locs V2 (tput t2 t2'))) p2 ->
    bsub (e1||e2||a1) uv ->
    exp_type1 S1 S2 M H1 H2 V1 V2 t1 t2 S1' S2' M' TRef uv p1 p2 fr1 a1 e1 ->
    exp_type S1' S2' M' H1 H2 V1 V2 t1' t2' TBool uv
      (por p1 (pdiff (pdom S1') (pdom S1)))
      (por p2 (pdiff (pdom S2') (pdom S2)))
      fr2 a2 e2 ->
    exp_type S1 S2 M H1 H2 V1 V2 (tput t1 t1') (tput t2 t2') TBool uv p1 p2 false false (e1||e2||a1).
Proof.
  intros ??????????????????????? SW ST P1 P2 E HX HY. 
  destruct HX as (vx1 & vx2 & uvx & lsx1 & lsx2 & SC' & SW' & TX1 & TX2 & LS1 & LS2 & ST' & VX & UX1 & UX2 & LUX1 & LUX2 & LX1 & LX2 & ES1 & ES2 & ESM).
  destruct HY as (S1'' & S2'' & M'' & vy1 & vy2 & uvy & lsy1 & lsy2 & SC'' & SW'' & TY1 & TY2 & LS1' & LS2' & ST'' & VY & UY1 & UY2 & LUY1 & LUY2 & LY1 & LY2 & ES1' & ES2' & ESM').
  eapply valt_store_change in VX. 2: { intros ??????. eapply SC''. eauto. }
  destruct vx1, vx2; simpl in VX; try contradiction.
  destruct uvx. 2: {
  assert (uv = false). destruct uv; intuition.
  assert (a1 = true). destruct uv,a1; intuition.
  unfold bsub in *. destruct e1,a1,uv; intuition. }
  
  destruct VX as (VX & LV1 & LV2). eauto. 
  destruct vy1, vy2; simpl in VY; try contradiction. 
  destruct ST'' as (L1 & L2 & L3).
  destruct (L3 _ _ VX) as (b1 & IX1 & IX2).
  edestruct (LX1 i) as [|[|]]. eauto. 
  destruct a1. 2: contradiction. left. left. eapply P1. rewrite exp_locs_put. unfoldq. destruct e1,e2; simpl; intuition.
  contradiction.
  destruct fr1. 2: contradiction. unfoldq. intuition. 
  edestruct (LX2 i0) as [|[|]]. eauto. 
  destruct a1. 2: contradiction. left. left. eapply P2. rewrite exp_locs_put. unfoldq. destruct e1,e2; simpl; intuition.
  contradiction.
  destruct fr1. 2: contradiction. unfoldq. intuition. 
  exists (update S1'' i (vbool b)), (update S2'' i0 (vbool b0)), (st_step M M'' false).
  exists (vbool true), (vbool true).
  exists true. 
  exists qempty, qempty.
  assert (st_len1 M <= st_len1 M''). destruct ST as (?&?&?). lia.
  assert (st_len2 M <= st_len2 M''). destruct ST as (?&?&?). lia.  
  split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 8: split. 9: split. 10: split.
  11: split. 12: split. 13: split. 14: split. 15: split. 16: split. 
  - eapply stchain_step. eapply stchain_chain; eauto.
  - eapply sttyw_step; eauto. 
  - destruct TX1 as (n1 & TX).
    destruct TY1 as (n2 & TY).
    exists (1+n1+n2). intros. destruct n. lia. simpl. rewrite TX, TY, IX1. eauto. lia. lia. 
  - destruct TX2 as (n1 & TX).
    destruct TY2 as (n2 & TY).
    exists (1+n1+n2). intros. destruct n. lia. simpl. rewrite TX, TY, IX2. eauto. lia. lia.
  - rewrite <-update_length. lia.
  - rewrite <-update_length. lia.
  - replace (pdom (update S1'' i (vbool b))) with (pdom S1'').
    replace (pdom (update S2'' i0 (vbool b0))) with (pdom S2'').
    rewrite por_assoc, pdiff_merge in L3.
    rewrite por_assoc, pdiff_merge in L3.
    eapply storet_step. 
    eapply storet_update. eauto. 
    repeat split; eauto. 
    intros. eauto. eauto. eapply stchain_chain; eauto. 
    eauto. eauto. eauto. eauto. 
    unfold pdom. erewrite update_length. eauto.
    unfold pdom. erewrite update_length. eauto. 
  - simpl. eauto.
  - destruct uv; eauto.
  - eauto.
  - intuition.
  - intuition. 
  - simpl. intros ??. intuition.
  - simpl. intros ??. intuition.
  - rewrite exp_locs_put.
    intros ? (Q1 & Q2). bdestruct (i =? i1). subst.
    + destruct (LX1 i1) as [|[|]]. eauto. 
      destruct a1. 2: contradiction. destruct Q2. destruct e1,e2; simpl; left; eauto.
      contradiction.
      destruct fr1. 2: contradiction. destruct H3. contradiction.
    + rewrite update_indexr_miss; eauto. rewrite ES1, ES1'. eauto.
      split. unfoldq. intuition. unfoldq. destruct e1,e2; simpl in *; intuition.
      split. unfoldq. intuition. unfoldq. destruct e1; simpl in *; intuition.
  - rewrite exp_locs_put.
    intros ? (Q1 & Q2). bdestruct (i0 =? i1). subst.
    + destruct (LX2 i1) as [|[|]]. eauto.
      destruct a1. 2: contradiction. destruct Q2. destruct e1,e2; simpl; left; eauto.
      contradiction.
      destruct fr1. 2: contradiction. destruct H3. contradiction.
    + rewrite update_indexr_miss; eauto. rewrite ES2, ES2'. eauto.
      split. unfoldq. intuition. unfoldq. destruct e1,e2; simpl in *; intuition.
      split. unfoldq. intuition. unfoldq. destruct e1; simpl in *; intuition.
  - intros C. intuition.
  - destruct ST' as (?&?&?). destruct ST'' as (?&?&?). lia.
  - destruct ST' as (?&?&?). destruct ST'' as (?&?&?). lia.
    Unshelve.
    apply True.
    apply qempty.
    apply qempty.
Qed.

Lemma envt_tighten: forall M H1 H2 V1 V2 G uw p p',
    env_type M H1 H2 V1 V2 G uw p ->
    psub p' p ->
    env_type M H1 H2 V1 V2 G uw p'.
Proof.
  intros. destruct H as (?&?&?&?&?&?).
  split. 2: split. 3: split. 4: split. 5: split. 
  eauto. eauto. eauto. eauto. eauto.
  intros. edestruct H7 as (?&?&?&?&?&?&?&?&?&?&?&?&?&?); eauto.
  eexists _,_,_,_,_. intuition.
  eauto. eauto. eauto. eauto. eauto. eauto. subst. eauto. 
  eauto. eauto. eauto. eauto.
Qed.



Lemma exp_app: forall S1 S2 M H1 H2 V1 V2 S1' S2' M' f1 f2 t1 t2 T1 T2 u uv p1 p2 fr2 fr1 frf a1 a2 af e1 ef e2,
    stty_wellformed M -> 
    store_type S1 S2 M p1 p2 ->
    psub (pif (e1||ef||(af||a1)&&e2) (exp_locs V1 (tapp f1 t1))) p1 ->
    psub (pif (e1||ef||(af||a1)&&e2) (exp_locs V2 (tapp f2 t2))) p2 ->
    exp_type1 S1 S2 M H1 H2 V1 V2 f1 f2 S1' S2' M' (TFun T1 fr1 a1 T2 fr2 a2 e2) uv p1 p2 frf af ef -> 
    exp_type S1' S2' M' H1 H2 V1 V2 t1 t2 T1 uv
      (por p1 (pdiff (pdom S1') (pdom S1)))
      (por p2 (pdiff (pdom S2') (pdom S2)))
      fr1 a1 e1 ->
    (e2 || u && a2 = true -> negb af || uv = true) -> 
    (e2 || u && a2 = true -> negb a1 || uv = true) -> 
    bsub ((af||a1)&&e2) uv ->
    (fr1||a1 = false -> negb a1 || uv = true) ->
    u = negb ((af||a1)&&a2) || uv ->
    exp_type S1 S2 M H1 H2 V1 V2 (tapp f1 t1) (tapp f2 t2) T2 (uv) p1 p2 ((frf||fr1)&&a2||fr2) ((af||a1)&&a2) (e1||ef||((af||a1)&&e2)).
Proof.
  intros ????????????????????????????? SW ST P1 P2 HF HX ???? UV. 
  edestruct HF as (vf1 & vf2 & uf & lsf1 & lsf2 & SC' & SW' & TF1 & TF2 & LS1 & LS2 & ST' & VF & UVF1 & UVF2 & LUF1 & LUF2 & LF1 & LF2 & ES1 & ES2 & ESM).
  edestruct HX as (S1'' & S2'' & M'' & vx1 & vx2 & ux & lsx1 & lsx2 & SC'' & SW'' & TX1 & TX2 & LS1' & LS2' & ST'' & VX & UVX1 & UVX2 & LUX1 & LUX2 & LX1 & LX2 & ES1' & ES2' & ESM').
  
  destruct vf1, vf2; simpl in VF; intuition.
  
  edestruct (VF S1'' S2'' M'') with (uy:=u) (uyv:=uv||negb(af||a1)) as (S1''' & S2''' & M''' & vy1 & vy2 & lsy1 & lsy2 & SC''' & SW''' & TY1 & TY2 & LS1'' & LS2'' & ST''' & VY & LUY1 & LUY2 & LY1 & LY2 & ES1'' & ES2'' & ESM''). 15: eapply VX. 
  intros ??????. eauto. 
  eauto.
  eauto.
  eauto.
  destruct uv,af,a1,e2; unfold bsub; simpl; intuition. 
  destruct uv,af,a1,a2; simpl; intuition. 
  eauto.
  eauto.
  destruct ST' as (?&?&?). destruct ST'' as (?&?&?). lia.
  destruct ST' as (?&?&?). destruct ST'' as (?&?&?). lia.
  eauto. 
  eauto. {
    intros ? Q. destruct e2. 2: contradiction.
    destruct Q as [HQF | HQX].
    + eapply LF1 in HQF. destruct HQF as [HQF | [HQU | HQFr]].
      * destruct af. 2: contradiction.
        left. left. eapply P1. rewrite exp_locs_app. destruct e1,ef; left; eauto.
      * contradiction. 
      * left. right. destruct frf; intuition.
    + destruct ux. 2: { eapply LUX1 in HQX. contradiction. eauto. }
      eapply LX1 in HQX. destruct HQX as [HQX | [HQU | HQFr]].
      * destruct a1. 2: contradiction.
        left. left. eapply P1. rewrite exp_locs_app. destruct e1,ef,af; right; eauto.
      * contradiction.
      * right. destruct fr1; intuition. 
  } {
    intros ? Q. destruct e2. 2: contradiction.
    destruct Q as [HQF | HQX].
    + eapply LF2 in HQF. destruct HQF as [HQF | [HQU | HQFr]].
      * destruct af. 2: contradiction.
        left. left. eapply P2. rewrite exp_locs_app. destruct e1,ef; left; eauto.
      * contradiction. 
      * destruct frf. 2: contradiction.
        left. right. eauto.
    + destruct ux. 2: { eapply LUX2 in HQX. contradiction. eauto. }
      eapply LX2 in HQX. destruct HQX as [HQX | [HQU | HQFr]].
      * destruct a1. 2: contradiction.
        left. left. eapply P2. rewrite exp_locs_app. destruct e1,ef,af; right; eauto.
      * contradiction.
      * destruct fr1. 2: contradiction.
        right. eauto.
  }
  destruct ux; subst. 2: intuition. 
  intros. intros ? Q. eapply LX1 in Q. unfoldq. destruct a1,fr1; intuition. 
  destruct ux; subst. 2: intuition. 
  intros. intros ? Q. eapply LX2 in Q. unfoldq. destruct a1,fr1; intuition. 

  exists S1''', S2''', (st_step M M''' ((frf||fr1)&&a2||fr2)).
  exists vy1, vy2.
  eexists.
  exists lsy1, lsy2.
  split. 2: split. 3: split. 4: split. 5: split. 6: split.
  7: split. 8: split. 9: split. 10: split.
  11: split. 12: split. 13: split. 14: split. 15: split. 16: split. 
  - eapply stchain_step. eapply stchain_chain. eauto. eapply stchain_chain; eauto.
  - destruct ST as (?&?&?). 
    destruct ST' as (?&?&?).
    destruct ST'' as (?&?&?).
    destruct ST''' as (?&?&?).
    eapply sttyw_step. eauto. eauto. lia. lia. 
  - destruct TF1 as (n1 & TF).
    destruct TX1 as (n2 & TX).
    destruct TY1 as (n3 & TY).
    exists (1+n1+n2+n3). intros. destruct n. lia.
    simpl. rewrite TF, TX, TY. 2,3,4: lia.
    eauto.
  - destruct TF2 as (n1 & TF).
    destruct TX2 as (n2 & TX).
    destruct TY2 as (n3 & TY).
    exists (1+n1+n2+n3). intros. destruct n. lia.
    simpl. rewrite TF, TX, TY. 2,3,4: lia.
    eauto.
  - lia.
  - lia.
  - repeat rewrite por_assoc in ST'''.
    rewrite pdiff_merge, pdiff_merge in ST'''.
    rewrite pdiff_merge, pdiff_merge in ST'''.
    all: eauto. 2: lia. 2: lia.
    split. 2: split.
    unfold st_step. destruct ((frf||fr1)&&a2||fr2); simpl; eapply ST'''.
    unfold st_step. destruct ((frf||fr1)&&a2||fr2); simpl; eapply ST'''.
    intros. eapply ST'''; eauto. destruct ((frf||fr1)&&a2||fr2); simpl in H; eauto.
  - remember (((frf || fr1) && a2 || fr2)) as b. destruct b. { 
      simpl. eauto.
    } { 
      destruct fr2. destruct fr1,frf,a2; simpl in Heqb; inversion Heqb.
      destruct a2. { destruct fr1,frf; simpl in Heqb; inversion Heqb.
      unfold st_step. rewrite <-ESM. rewrite <-ESM'. rewrite <-ESM''.
      destruct M''' as ((?&?)&?). unfold st_len1, st_len2; simpl. 
      eapply valt_usable. eauto. 
      destruct u,af,a1; simpl in *; inversion Heqb; eauto.
      eauto. eauto. eauto. }

      eapply valt_store_reset. eapply valt_usable. eauto.
      intuition. 
      intros ? ? Q. eapply LY1 in Q. unfoldq. destruct u; intuition.
      intros ? ? Q. eapply LY2 in Q. unfoldq. destruct u; intuition.
      unfold st_len1 at 2. simpl. eauto.
      unfold st_len2 at 2. simpl. eauto.
    }
    
  - eauto.
  - eauto.
  - eauto.
  - eauto. 
  - rewrite exp_locs_app. intros ? Q. eapply LY1 in Q. destruct Q as [HQF | [HQX | HQFr]].
    + destruct a2. 2: contradiction.
      eapply LF1 in HQF. destruct HQF as [HQF | [HQU | HQFr]].
      * destruct af. 2: contradiction. left. left. eauto.
      * destruct uf. 2: contradiction.
        destruct u. right. left. eauto.
        contradiction.
      * destruct frf. 2: contradiction. right. unfoldq. destruct fr1; simpl; lia.
    + destruct a2. 2: contradiction.
      destruct ux; subst. 
      2: { eapply LUX1 in HQX. contradiction. eauto. }
      eapply LX1 in HQX. destruct HQX as [HQX | [HQU | HQFr]].
      * destruct a1. 2: contradiction. left. destruct af; simpl; right; eauto. 
      * contradiction.
      * destruct fr1. 2: contradiction. right. unfoldq. simpl. destruct frf; simpl; lia.
    + right. unfoldq. destruct fr2,fr1,frf,a2; simpl; intuition.
  - rewrite exp_locs_app. intros ? Q. eapply LY2 in Q. destruct Q as [HQF | [HQX | HQFr]].
    + destruct a2. 2: contradiction.
      eapply LF2 in HQF. destruct HQF as [HQF | [HQU | HQFr]].
      * destruct af. 2: contradiction. left. left. eauto.
      * contradiction. 
      * destruct frf. 2: contradiction. right. unfoldq. destruct fr1; simpl; lia.
    + destruct a2. 2: contradiction.
      destruct ux; subst. 
      2: { eapply LUX2 in HQX. contradiction. eauto. }
      eapply LX2 in HQX. destruct HQX as [HQX | [HQU | HQFr]].
      * destruct a1. 2: contradiction. left. destruct af; simpl; right; eauto.
      * contradiction.
      * destruct fr1. 2: contradiction. right. unfoldq. simpl. destruct frf; simpl; lia.
    + right. unfoldq. destruct fr1,frf,fr2,a2; simpl; intuition.
  - rewrite exp_locs_app. intros ? (Q1 & Q2). rewrite ES1, ES1', ES1''. eauto.
    + split. unfoldq. intuition. intros C. eapply Q2. destruct e2. 2: contradiction. destruct C as [C|C]. 
      * eapply LF1 in C. destruct C as [HQF | [HQX | HQFr]].
        destruct af. 2: contradiction. destruct e1,ef; simpl; left; eauto.
        contradiction. 
        destruct frf, HQFr; intuition. 
      * destruct ux; subst. 
        2: { eapply LUX1 in C. contradiction. eauto. }
        eapply LX1 in C. destruct C as [HQF | [HQX | HQFr]].
        destruct a1. 2: contradiction. destruct e1,ef,af; simpl; right; eauto.
        contradiction. eauto. 
        destruct fr1, HQFr. unfoldq. intuition.
    + split. unfoldq. intuition. destruct e1; intuition. eapply Q2. simpl. right. eauto. 
    + split. unfoldq. intuition. destruct ef; intuition. eapply Q2. destruct e1; simpl; left; eauto.
  - rewrite exp_locs_app. intros ? (Q1 & Q2). rewrite ES2, ES2', ES2''. eauto.
    + split. unfoldq. intuition. destruct e2; intuition. eapply Q2. destruct H5 as [C | C].
      * eapply LF2 in C. destruct C as [HQF | [HQX | HQFr]].
        destruct af. 2: contradiction. destruct e1,ef; simpl; left; eauto.
        subst uf. contradiction. 
        destruct frf, HQFr. intuition.
      * destruct ux; subst. 
        2: { eapply LUX2 in C. contradiction. eauto. }
        eapply LX2 in C. destruct C as [HQF | [HQX | HQFr]].
        destruct a1. 2: contradiction. destruct e1,ef,af; simpl; right; eauto.
        contradiction.
        destruct fr1, HQFr. unfoldq. intuition.
    + split. unfoldq. intuition. destruct e1; intuition. eapply Q2. right. eauto.
    + split. unfoldq. intuition. destruct ef; intuition. eapply Q2. destruct e1; left; eauto. 
  - intuition. rewrite H5. simpl. eauto.
Qed.

Lemma exp_tnot: forall S1 S2 M H1 H2 V1 V2 t1 t2 p1 p2 uv fr a e,
  stty_wellformed M ->
  store_type S1 S2 M p1 p2 ->
  psub (pif e (exp_locs V1 (tnot t1))) p1 ->
  psub (pif e (exp_locs V2 (tnot t2))) p2 ->
  bsub e uv ->
  exp_type S1 S2 M H1 H2 V1 V2 t1 t2 TBool uv p1 p2 fr a e ->
  exp_type S1 S2 M H1 H2 V1 V2 (tnot t1) (tnot t2) TBool uv p1 p2 false false e.
Proof.
  intros ??????????????? SW ST P1 P2 E HX. 
  destruct HX as (S1' & S2' & M' & vx1 & vx2 & ux & lsx1 & lsx2 & SC' & SW' & TX1 & TX2 & LS1 & LS2 & ST' & VX & UX1 & UX2 & LUX1 & LUX2 & LX1 & LX2 & ES1 & ES2 & EM).
  destruct vx1, vx2; simpl in VX; try contradiction. subst b0.
  simpl in *. 
  destruct ST' as (L1 & L2 & L3).
  exists S1', S2', (st_step M M' false), (vbool (negb b)), (vbool (negb b)), true, qempty, qempty.
  split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 8: split. 9: split. 10: split.
  11: split. 12: split. 13: split. 14: split. 15: split. 16: split.
  - eapply stchain_step; eauto. 
  - eapply sttyw_step; eauto. destruct ST. lia. destruct ST. lia.
  - destruct TX1 as (n1 & TX).
    exists (1+n1). intros. destruct n. lia. simpl. rewrite TX. eauto. lia. 
  - destruct TX2 as (n1 & TX).
    exists (1+n1). intros. destruct n. lia. simpl. rewrite TX. eauto. lia. 
  - lia.
  - lia.
  - repeat split; eauto.
  - simpl. eauto.
  - simpl. auto.
  - auto.
  - intuition.
  - intuition.
  - rewrite plift_empty. unfoldq; intuition.
  - rewrite plift_empty. unfoldq; intuition.
  - auto.
  - auto.
  - intuition.
Qed.

 
Lemma exp_tbin: forall S1 S2 M S1' S2' M' H1 H2 V1 V2 t1 t2 t3 t4 p1 p2 uv fr1 fr2 a1 a2 e1 e2,
    stty_wellformed M ->
    store_type S1 S2 M p1 p2 ->
    psub (pif (e1||e2) (exp_locs V1 (tbin t1 t2))) p1 ->
    psub (pif (e1||e2) (exp_locs V2 (tbin t3 t4))) p2 ->
    bsub (e1||e2) uv ->
    exp_type1 S1 S2 M H1 H2 V1 V2 t1 t3 S1' S2' M' TBool uv p1 p2 fr1 a1 e1 ->
    exp_type S1' S2' M' H1 H2 V1 V2 t2 t4 TBool uv
      (por p1 (pdiff (pdom S1') (pdom S1)))
      (por p2 (pdiff (pdom S2') (pdom S2)))
      fr2 a2 e2 ->
    exp_type S1 S2 M H1 H2 V1 V2 (tbin t1 t2) (tbin t3 t4) TBool false p1 p2 false false (e1||e2).
Proof.
  intros ??????????????????????? SW ST P1 P2 E HX HY. 
  destruct HX as (vx1 & vx2 & uvx & lsx1 & lsx2 & SC' & SW' & TX1 & TX2 & LS1 & LS2 & ST' & VX & UX1 & UX2 & LUX1 & LUX2 & LX1 & LX2 & ES1 & ES2 & ESM).
  destruct HY as (S1'' & S2'' & M'' & vy1 & vy2 & uvy & lsy1 & lsy2 & SC'' & SW'' & TY1 & TY2 & LS1' & LS2' & ST'' & VY & UY1 & UY2 & LUY1 & LUY2 & LY1 & LY2 & ES1' & ES2' & ESM').
  
  destruct vx1, vx2; simpl in VX; try contradiction. subst b0.
  destruct vy1, vy2; simpl in VY; intuition. subst b0.
  
  exists S1'', S2'', (st_step M M'' false) , (vbool(b && b1)), (vbool(b && b1)).
  exists true. 
  exists qempty, qempty.
  split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 8: split. 9: split. 10: split.
  11: split. 12: split. 13: split. 14: split. 15: split. 16: split. 
  - eapply stchain_step. eapply stchain_chain; eauto.
  - eapply sttyw_step; eauto. destruct ST, ST', ST''. lia. destruct ST, ST', ST''. lia.
  - destruct TX1 as (n1 & TX).
    destruct TY1 as (n2 & TY).
    exists (1+n1+n2). intros. destruct n. lia. simpl. rewrite TX, TY. eauto. lia. lia.
  - destruct TX2 as (n1 & TX).
    destruct TY2 as (n2 & TY).
    exists (1+n1+n2). intros. destruct n. lia. simpl. rewrite TX, TY. eauto. lia. lia.
  - lia.
  - lia.
  - rewrite por_assoc, pdiff_merge in ST''. rewrite por_assoc, pdiff_merge in ST''. eapply storet_step. auto. 
    eapply stchain_chain. eauto. eauto. all: lia.
  - simpl. eauto.
  - eauto.
  - eauto. 
  - simpl. intros ??. intuition.
  - simpl. intros ??. intuition.
  - rewrite plift_empty. unfoldq. intuition.
  - rewrite plift_empty. unfoldq. intuition.
  - rewrite exp_locs_tbin. 
    eapply storew_trans. 
    eapply storew_widen. eapply ES1. intros ? ?. destruct e1; try contradiction. left. auto.  
    eapply storew_widen. eapply ES1'. intros ? ?. destruct e2; try contradiction. destruct e1; simpl; right; auto. lia.
  - rewrite exp_locs_tbin. 
    eapply storew_trans. 
    eapply storew_widen. eapply ES2. intros ? ?. destruct e1; try contradiction. left. auto.  
    eapply storew_widen. eapply ES2'. intros ? ?. destruct e2; try contradiction. destruct e1; simpl; right; auto. lia.
  - intros C. intuition.
Qed.

Lemma exp_strengthen1: forall S1 S2 M S1' S2' M' H1 H2 V1 V2 t1 t2 T p1 p2 fr a e,
    exp_type1 S1 S2 M H1 H2 V1 V2 t1 t2 S1' S2' M' T true p1 p2 fr a e ->
    psub (exp_locs V1 t1) pempty ->
    psub (exp_locs V2 t2) pempty ->
    exp_type1 S1 S2 M H1 H2 V1 V2 t1 t2 S1' S2' M' T true p1 p2 fr false false.
Proof.
  intros. destruct H as (?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?).
  eexists _,_,_,_,_. split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split.
  8: split. 9: split. 10: split. 11: split. 12: split. 13: split. 14: split. 15: split. 16: split. 
  all: eauto.
  destruct a; intuition.
  intros ? Q. eapply H15 in Q. destruct Q as [Q|[Q|Q]].
  destruct a. 2: contradiction. eapply H0 in Q. contradiction.
  contradiction.
  destruct fr. 2: contradiction. right. right. eauto.
  intros ? Q. eapply H16 in Q. destruct Q as [Q|[Q|Q]].
  destruct a. 2: contradiction. eapply H3 in Q. contradiction.
  contradiction.
  destruct fr. 2: contradiction. right. right. eauto.
  eapply storew_widen. eauto.
  intros ? Q. destruct e. 2: contradiction. eapply H0 in Q. contradiction.
  eapply storew_widen. eauto.
  intros ? Q. destruct e. 2: contradiction. eapply H3 in Q. contradiction.
Qed.

Lemma exp_strengthen1': forall S1 S2 M S1' S2' M' H1 H2 V1 V2 t1 t2 T p1 p2 fr a e b,
    exp_type1 S1 S2 M H1 H2 V1 V2 t1 t2 S1' S2' M' T true p1 p2 fr a e ->
    (b = false -> psub (exp_locs V1 t1) pempty) ->
    (b = false -> psub (exp_locs V2 t2) pempty) ->
    exp_type1 S1 S2 M H1 H2 V1 V2 t1 t2 S1' S2' M' T true p1 p2 fr (a&&b) (e&&b).
Proof.
  intros. destruct a,b,e; simpl; intuition.
  eapply exp_strengthen1; eauto.
  eapply exp_strengthen1; eauto.
  eapply exp_strengthen1; eauto.
Qed.

Lemma exp_usable1: forall S1 S2 M S1' S2' M' H1 H2 V1 V2 t1 t2 T (u u':bool) p1 p2 fr a e,
    exp_type1 S1 S2 M H1 H2 V1 V2 t1 t2 S1' S2' M' T u p1 p2 fr a e ->
    (u'=true -> u=true) ->
    exp_type1 S1 S2 M H1 H2 V1 V2 t1 t2 S1' S2' M' T u' p1 p2 fr a e.
Proof.
  intros. destruct H as (?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?).
  remember (negb a || u') as x1'.
  destruct x1'.
  - eexists _,_,true,_,_. split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split.
    8: split. 9: split. 10: split. 11: split. 12: split. 13: split. 14: split. 15: split. 16: split. 
    8: eapply valt_usable; eauto. 
    all: eauto.
    destruct u,u',a,x1; intuition.
    intuition. intuition.
  - eexists _,_,false,_,_. split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split.
    8: split. 9: split. 10: split. 11: split. 12: split. 13: split. 14: split. 15: split. 16: split. 
    8: { eapply valt_reset_locs. eapply valt_usable. eauto. intuition. intuition. }
    all: eauto.
    rewrite plift_empty. unfoldq. intuition.
    rewrite plift_empty. unfoldq. intuition.
    rewrite plift_empty. unfoldq. intuition.
    rewrite plift_empty. unfoldq. intuition.
Qed.

Lemma exp_usable: forall S1 S2 M H1 H2 V1 V2 t1 t2 T (u u':bool) p1 p2 fr a e,
    exp_type S1 S2 M H1 H2 V1 V2 t1 t2 T u p1 p2 fr a e ->
    (u'=true -> u=true) -> 
    exp_type S1 S2 M H1 H2 V1 V2 t1 t2 T u' p1 p2 fr a e.
Proof.
  intros. destruct H as (?&?&?&?).
  eexists _,_,_. eapply exp_usable1; eauto. 
Qed.

Lemma exp_usable': forall S1 S2 M H1 H2 V1 V2 t1 t2 T (u u':bool) p1 p2 fr a e,
    exp_type S1 S2 M H1 H2 V1 V2 t1 t2 T u p1 p2 fr a e ->
    bsub u' u ->
    exp_type S1 S2 M H1 H2 V1 V2 t1 t2 T u' p1 p2 fr a e.
Proof.
  intros. eapply exp_usable; eauto. 
Qed.

Lemma exp_mentionable1: forall S1 S2 M H1 H2 V1 V2 V1' V2' t1 t2 T (uv: bool) p1 p2 fr a e,
    exp_type S1 S2 M H1 H2 V1 V2 t1 t2 T false p1 p2 fr a e ->
    e = false ->
    a = false \/ uv = false ->
    exp_type S1 S2 M H1 H2 V1' V2' t1 t2 T uv p1 p2 fr a e.
Proof.
  intros. destruct H as (?&?&?&?&?&?&?&?&?&?).
  destruct H3. subst e a. eexists _,_,_,_,_,_,_,_. intuition.
  split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 8: split. 9: split. 10: split.
  11: split. 12: split. 13: split. 14: split. 15: split. 16: split. 
  all: eauto.
  subst uv.
  eexists _,_,_,_,_,_,_,_. intuition.
  split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 8: split. 9: split. 10: split.
  11: split. 12: split. 13: split. 14: split. 15: split. 16: split. 
  all: eauto.

  intros ? Q. destruct a. simpl in H10. eapply H12 in Q. contradiction. eauto. eauto.
  intros ? Q. destruct a. simpl in H10. eapply H13 in Q. contradiction. eauto. eauto.
  subst e. eauto.
  subst e. eauto. 
Qed.

Lemma exp_mentionable: forall S1 S2 M H1 H2 V1 V2 V1' V2' t1 t2 S1' S2' M' T (uv: bool) p1 p2 fr a e,
    exp_type1 S1 S2 M H1 H2 V1 V2 t1 t2 S1' S2' M' T false p1 p2 fr a e ->
    e = false ->
    a = false \/ uv = false ->
    exp_type1 S1 S2 M H1 H2 V1' V2' t1 t2 S1' S2' M' T uv p1 p2 fr a e.
Proof. 
  intros. destruct H as (?&?&?&?&?&?&?&?&?&?).
  destruct H3. subst e a. eexists _,_,_,_,_. intuition.
  split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 8: split. 9: split. 10: split.
  11: split. 12: split. 13: split. 14: split. 15: split. 16: split. 
  all: eauto.
  subst uv.
  eexists _,_,_,_,_. intuition.
  split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 8: split. 9: split. 10: split.
  11: split. 12: split. 13: split. 14: split. 15: split. 16: split. 
  all: eauto.

  intros ? Q. destruct a. simpl in H10. eapply H12 in Q. contradiction. eauto. eauto.
  intros ? Q. destruct a. simpl in H10. eapply H13 in Q. contradiction. eauto. eauto.
  subst e. eauto.
  subst e. eauto. 
Qed.


Lemma envc_tighten: forall G p p' a,
    env_cap G p a ->
    psub (plift p') (plift p) ->
    env_cap G p' a.
Proof.
  intros. intros ??????.
  eapply H. eauto. rewrite H0. eauto. eauto. 
Qed.

Lemma envc_extend: forall G p a a1 fr1 T1,
    env_cap G p a ->
    bsub (fr1||a1) a ->
    env_cap ((T1,fr1,a1)::G) (qor p (qone (length G))) a.
Proof.
  intros. intros ??????.
  bdestruct (x =? length G).
  subst x. rewrite indexr_head in H1. inversion H1. subst. eauto.
  rewrite indexr_skip in H1. eapply H. eauto.
  unfold qor in H2. destruct (p x). eauto. simpl in H2.
  unfold qone in H2. bdestruct (x =? length G); intuition.
  eauto. 
Qed.

Lemma envc_extend': forall G p a a1 fr1 T1,
    env_cap G p a ->
    (~ plift p (length G)) ->
    env_cap ((T1,fr1,a1)::G) p a.
Proof.
  intros. intros ??????.
  eapply H. rewrite indexr_skip in H1. eauto.
  intros C. eapply H0. subst. eauto. eauto. 
Qed.


(* ---------- LR fundamental property  ---------- *)


Fixpoint map2 {A B C} (f: A -> B -> C) (xs: list A) (ys: list B) {struct xs}: list C :=
  match xs, ys with
  | x::xs, y::ys => (f x y)::(map2 f xs ys)
  | _, _ => []
  end.

Lemma map2_length: forall {A B C} (xs: list A) (ys: list B) (f: A -> B -> C),
    length xs = length ys ->
    length (map2 f xs ys) = length xs.
Proof.
  intros A B C xs. induction xs.
  intros. simpl. eauto.
  intros. simpl. destruct ys. inversion H.
  simpl. eauto. 
Qed.

Lemma map2_length': forall {A B C} (xs: list A) (ys: list B) (f: A -> B -> C),
    length (map2 f xs ys) = length ys ->
    length ys <= length xs.
Proof.
  intros A B C xs. induction xs.
  intros. simpl in *. lia. 
  intros. simpl in *. destruct ys. simpl. lia. 
  simpl in *. assert (length ys <= length xs). eauto. lia. 
Qed.

Lemma indexr_map2: forall {A B C} (xs: list A) (ys: list B) (f: A -> B -> C) x a b,
    indexr x xs = Some a ->
    indexr x ys = Some b ->
    length xs = length ys ->
    indexr x (map2 f xs ys) = Some (f a b).
Proof.
  intros A B C G. induction G.
  intros. inversion H.
  intros. destruct ys. inversion H0. simpl. 
  bdestruct (x =? length (map2 f G ys)).
  replace x with (length G) in H.
  2: { rewrite map2_length in H2. 2: eauto. rewrite H2 in H. eauto. }
  rewrite indexr_head in H. inversion H. subst a.
  replace x with (length ys) in H0.
  2: { rewrite map2_length in H2. 2: eauto. simpl in H1. lia. }
  rewrite indexr_head in H0. inversion H0. subst b.
  eauto.
  simpl in H1. 
  rewrite map2_length in H2. 2: eauto.
  rewrite indexr_skip in H. 2: eauto.
  rewrite indexr_skip in H0. 2: lia.
  eapply IHG; eauto.
Qed.

Definition all_use (G: tenv): uenv := map (fun x => true) G. 

Definition not_a (p: (ty * bool * bool)): bool :=
  match p with
  | (T, fr, a) => negb (fr||a)
  end.

Definition restrictW (ae: bool) (W: uenv) (G: tenv) :=
  if ae then W else (map2 andb W (map not_a G)).

Definition restrictV (ae: bool) (V: lenv) :=
  if ae then V else (map (fun x => qempty) V).

Lemma restrictW_length: forall G W a,
    length W = length G ->
    length (restrictW a W G) = length G.
Proof.
  intros. destruct a; simpl. eauto.
  rewrite map2_length. eauto.
  rewrite map_length. eauto. 
Qed.

Lemma restrictV_length: forall{X} (G:list X) V a,
    length V = length G ->
    length (restrictV a V) = length G.
Proof.
  intros. destruct a; simpl. eauto.
  rewrite map_length. eauto. 
Qed.

Lemma indexr_restrictW: forall x G W T fr a u uw,
  indexr x G = Some (T, fr, a) ->
  indexr x W = Some u ->
  length W = length G ->
  indexr x (restrictW uw W G) = Some (u && (negb (fr || a) || uw)). 
Proof.
  intros.
  unfold restrictW, not_a in *.
  destruct uw. 
  destruct u,fr,a; simpl; intuition.
  erewrite indexr_map2. 2: eauto.
  2: erewrite indexr_map. 3: eauto.
  2: { simpl. eauto. }
  2: { rewrite map_length. eauto. }
  destruct u,fr,a; intuition.
Qed.

Lemma indexr_restrictV': forall x (G:tenv) V T fr a ls uw,
  indexr x G = Some (T, fr, a) ->
  indexr x V = Some ls ->
  length V = length G ->
  exists ls', indexr x (restrictV uw V) = Some ls' /\
  psub (plift ls') (plift ls).
Proof.
  intros.
  unfold restrictV.
  destruct uw.
  exists ls. split. auto. intros ?. auto.
  exists qempty. split.
  erewrite indexr_map. auto. eauto.
  unfoldq. intuition.
Qed.

Lemma aux1: forall q,
    psub (plift q) pempty ->
    qempty = q.
Proof.
  intros. eapply functional_extensionality.
  intros. remember (q x) as p. destruct p.
  symmetry in Heqp. eapply H in Heqp. contradiction.
  unfold qempty. eauto. 
Qed.

Lemma aux2: forall V t,
    psub (exp_locs (restrictV false V) t) pempty.
Proof.
  intros. 
  unfold exp_locs, restrictV.
  intros ? Q. destruct Q as (?&?&?&?&?).
  eapply indexr_var_some' in H0 as L. rewrite map_length in L.
  eapply indexr_var_some in L. destruct L. 
  erewrite indexr_map in H0; eauto. inversion H0. subst x1.
  intuition. 
Qed.

Lemma aux2': forall V q,
  psub (vars_locs (restrictV false V) q) pempty.
Proof.
  intros. unfold restrictV.
  intros ? Q. destruct Q as (?&?&?&?&?).
  eapply indexr_var_some' in H0 as L. rewrite map_length in L.
  eapply indexr_var_some in L. destruct L. 
  erewrite indexr_map in H0; eauto. inversion H0. subst x1.
  intuition.
Qed.


Lemma envt_strengthenW:  forall M H1 H2 V1 V2 G p uw uw',
    env_type M H1 H2 (restrictV uw V1) (restrictV uw V2) G uw (p) ->
    bsub uw' uw -> 
    env_type M H1 H2 (restrictV uw' V1) (restrictV uw' V2) G uw' (p).
Proof.
  intros. destruct H as (?&?&?&?&?&?).
  split. 2: split. 3: split. 4: split. 5: split. 
  eauto. eauto.
  subst. destruct uw,uw'; simpl in *; try erewrite map_length in *; eauto.
  subst. destruct uw,uw'; simpl in *; try erewrite map_length in *; eauto. 
  eauto. 
  intros. edestruct H7 as (?&?&?&?&?&?&?&?&?&?&?&?&?&?); eauto.
  destruct uw',uw; intuition. 
  simpl in *. 
  unfold all_use in H13. 
  eexists _,_,_,_,_. split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 8: split. 
  eauto. eauto.
  erewrite indexr_map. eauto. eauto. 
  erewrite indexr_map. eauto. eauto.
  eauto. eauto.  
  intros. simpl.
  remember (fr||a) as b. destruct b. 
  eapply valt_reset_locs. eapply valt_usable. eauto. eauto. intuition.
  erewrite aux1 at 1. 2: eapply H20; eauto.
  erewrite aux1 at 1. 2: eapply H16; eauto.
  subst. eauto. 
  rewrite plift_empty. unfoldq. intuition.
  rewrite plift_empty. unfoldq. intuition. 
Qed.

Lemma envt_strengthenWX': forall M H1 H2 V1 V2 G p um af,
    env_type M H1 H2 (V1) (V2) G um (plift p) ->
    env_cap G p af ->
    (um = false -> af = false) ->
    env_type M H1 H2 (V1) (V2) G true (plift p).
Proof. 
  intros. destruct H as (?&?&?&?&?&?).
  split. 2: split. 3: split. 4: split. 5: split. 
  eauto. eauto. eauto. eauto. eauto. 
  intros. edestruct H8 as (?&?&?&?&?&?&?&?&?&?&?&?&?&?); eauto.

  eapply indexr_var_some' in H10 as H10'.
  eapply indexr_var_some' in H11 as H11'.
  rewrite H,<-H5 in H10'.
  rewrite H4,<-H6 in H11'.
  eapply indexr_var_some in H10'.
  eapply indexr_var_some in H11'.
  destruct H10', H11'.
  
  eexists _,_,_,_,_. split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 8: split. 
  eauto. eauto. eauto. eauto. eauto. eauto.
  intros. subst x2. eapply H0 in H21 as AF. 2: eauto.
  remember (fr||a) as fra. 
  destruct fra; simpl in *.
  assert (af = true). unfold bsub in *. eauto. subst af.
  assert (um = true). destruct um; intuition. subst um.  
  rewrite H12 in H19. rewrite H13 in H20. inversion H19. inversion H20. subst. eauto. eauto. eauto.
  rewrite H12 in H19. rewrite H13 in H20. inversion H19. inversion H20. subst. eauto. eauto. eauto.
  intuition. rewrite H12 in H19. inversion H19. subst. eauto.
  intuition. rewrite H13 in H20. inversion H20. subst. eauto. 
Qed.


Lemma envt_strengthenWX:  forall M H1 H2 V1 V2 G p uw uw',
    env_type M H1 H2 (restrictV uw V1) (restrictV uw V2) G uw (plift p) ->
    bsub uw' uw -> 
    env_cap G p uw' ->
    env_type M H1 H2 (restrictV uw' V1) (restrictV uw' V2) G true (plift p).
Proof.
  intros. destruct H as (?&?&?&?&?&?).
  split. 2: split. 3: split. 4: split. 5: split. 
  eauto. eauto.
  subst. destruct uw,uw'; simpl in *; try erewrite map_length in *; eauto.
  subst. destruct uw,uw'; simpl in *; try erewrite map_length in *; eauto. 
  eauto. 
  intros. edestruct H8 as (?&?&?&?&?&?&?&?&?&?&?&?&?&?); eauto.
  destruct uw',uw; intuition.
  - simpl in *. 
  eauto. 
  eexists _,_,_,_,_. split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 8: split. 
  eauto. eauto.
  erewrite indexr_map. eauto. eauto. 
  erewrite indexr_map. eauto. eauto.
  eauto. 
  eauto.
  intros. 
  erewrite aux1 at 1. 2: eapply H21; eauto.
  erewrite aux1 at 1. 2: eapply H17; eauto.
  eauto.
  eapply H3 in H9. unfold bsub in *; destruct fr,a; intuition.
  eapply H3 in H9. unfold bsub in *; destruct fr,a; intuition. 
  rewrite plift_empty. unfoldq. intuition.
  rewrite plift_empty. unfoldq. intuition.
  - simpl in *. 
    simpl in H14. 
    remember (fr||a) as fra. 
    eexists _,_,_,_,_. split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split.
  eauto. eauto. eauto. eauto.
  intros. assert (x < length V1) as A. eapply indexr_var_some' in H10. rewrite map_length in *. lia.
  eapply indexr_var_some in A. destruct A as (ls1' & ?). erewrite indexr_map. eauto. eauto. 
  intros. assert (x < length V2) as A. eapply indexr_var_some' in H11. rewrite map_length in *. lia.
  eapply indexr_var_some in A. destruct A as (ls2' & ?). erewrite indexr_map. eauto. eauto. 
  eauto. 
  eauto.
  intros.
  assert (fra = false). {
  eapply H3 in H9. eapply H9 in H23 as XX.
  rewrite <-Heqfra in XX. unfold bsub in *. destruct fra; intuition. }
  subst fra x2. rewrite H24 in *. eauto. 
  intuition. 
  erewrite aux1 at 1.
  erewrite aux1 at 1.
  eauto. eauto. eauto. rewrite plift_empty. unfoldq. intuition. 
Qed.



Lemma envt_strengthenW1: forall M H1 H2 V1 V2 env pf,
    env_type M H1 H2 V1 V2 env true (plift pf) ->
    env_type M H1 H2 V1 V2 env false (plift pf).
Proof.
  intros. destruct H as (?&?&?&?&?&?).
  split. 2: split. 3: split. 4: split. 5: split. 
  eauto. eauto. eauto. eauto. eauto. 
  intros. edestruct H6 as (?&?&?&?&?&?&?&?&?&?&?&?&?&?); eauto.
  simpl in *. 
  eexists _,_,_,qempty,qempty. split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 8: split. 
  eauto. eauto.
  intuition. rewrite H10. rewrite (aux1 x3); eauto.
  intuition. rewrite H11. rewrite (aux1 x4); eauto. 
  eauto. eauto.
  intros. destruct (fr||a). simpl. eapply valt_reset_locs. eapply valt_usable. eauto.
  subst. eauto. intuition. simpl. subst x2. simpl in *.
  erewrite aux1 at 1.  erewrite aux1 at 1. eauto. eauto. eauto.
  rewrite plift_empty. unfoldq. eauto.
  rewrite plift_empty. unfoldq. eauto. 
Qed.


Lemma envt_strengthenW2: forall M H1 H2 V1 V2 env pf,
    env_type M H1 H2 V1 V2 env false (plift pf) ->
    env_cap env pf false ->
    env_type M H1 H2 V1 V2 env true (plift pf).
Proof.
  intros. destruct H as (?&?&?&?&?&?).
  split. 2: split. 3: split. 4: split. 5: split. 
  eauto. eauto. eauto. eauto. eauto. 
  intros. edestruct H7 as (?&?&?&?&?&?&?&?&?&?&?&?&?&?); eauto.
  simpl in *. 
  intros. assert (x < length V1) as A. eapply indexr_var_some' in H9. lia. 
  eapply indexr_var_some in A. destruct A as (ls1' & ?). 
  intros. assert (x < length V2) as A. eapply indexr_var_some' in H10. lia.
  eapply indexr_var_some in A. destruct A as (ls2' & ?). 
  eexists _,_,_,_,_. split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 8: split. 
  eauto. eauto. eauto. eauto.
  eauto. eauto. 
  subst x2. eapply H0 in H8. remember (fr||a) as u. intros.
  eapply H8 in H14 as H14'. destruct u; intuition. simpl in *.
  replace ls1' with x3. replace ls2' with x4. eauto.
  congruence. congruence. 
  intros. rewrite H11 in H18. inversion H18. subst. intuition. intuition.
  intros. rewrite H12 in H19. inversion H19. subst. intuition. intuition. 
Qed.

Lemma envt_strengthenW2': forall M H1 H2 V1 V2 env pf,
    env_type M H1 H2 V1 V2 env false (plift pf) ->
    env_cap env pf false ->
    env_type M H1 H2 (map (fun _ : ql => qempty) V1) (map (fun _ : ql => qempty) V2) env true (plift pf).
Proof.
  intros. destruct H as (?&?&?&?&?&?).
  split. 2: split. 3: split. 4: split. 5: split. 
  eauto. eauto. 
  rewrite map_length. lia.
  rewrite map_length. lia.
  eauto. 
  intros. edestruct H7 as (?&?&?&?&?&?&?&?&?&?&?&?&?&?); eauto.
  simpl in *. 
  intros. assert (x < length V1) as A. eapply indexr_var_some' in H9. lia. 
  eapply indexr_var_some in A. destruct A as (ls1' & ?). 
  intros. assert (x < length V2) as A. eapply indexr_var_some' in H10. lia.
  eapply indexr_var_some in A. destruct A as (ls2' & ?). 
  eexists _,_,_,_,_. split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 8: split. 
  eauto. eauto. 
  intros. eapply indexr_map. eauto.
  intros. eapply indexr_map. eauto.
  eauto. eauto. 
  subst x2. eapply H0 in H8. remember (fr||a) as u. intros.
  eapply H8 in H14 as H14'. destruct u; intuition. simpl in *. auto. 
  rewrite aux1 at 1. rewrite aux1 at 1. eauto.
  auto. auto.
  rewrite plift_empty. unfoldq; intuition.
  rewrite plift_empty. unfoldq; intuition.
Qed.

Lemma envt_store_changeV'': forall M M' H1 H2 V1 V2 G p,
    env_type M H1 H2 V1 V2 G true p ->
    st_len1 M <= st_len1 M' -> 
    st_len2 M <= st_len2 M' ->
    env_type M' H1 H2 (restrictV false V1) (restrictV false V2) G false p.
Proof.
  intros. destruct H as (LH1 & LH2 & LV1 & LV2 & LW & IX).
  split. 2: split. 3: split. 4: split. 5: split. 
  - eauto.
  - eauto.
  - eapply restrictV_length. eauto.
  - eapply restrictV_length. eauto. 
  - eauto.
  - intros. edestruct IX as (v1 & v2 & u & ls1 & ls2 & IX1' & IX2' & IV1' & IV2' & IW' & UX & VX & VQ1 & VQ2). eauto.
    exists v1, v2, (u&&negb(fr||a)), qempty, qempty. split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 8: split. 
    eauto. eauto.
    unfold restrictV. erewrite indexr_map. eauto. eauto.
    unfold restrictV. erewrite indexr_map. eauto. eauto.
    eauto. 
    subst u. destruct fr,a; eauto. 
    destruct u.
    2: {intros. eapply valt_store_reset. eapply valt_reset_locs. eauto.
    intuition. intuition. intuition. eauto. eauto. }
    intros. eapply valt_store_reset. simpl.
    remember (fr||a) as D. destruct D. 
    eapply valt_reset_locs. eapply valt_usable. eauto. eauto. intuition.
    rewrite aux1 at 1.
    rewrite aux1 at 1.
    eauto. eauto. eauto.
    rewrite plift_empty. unfoldq. intuition.
    rewrite plift_empty. unfoldq. intuition.
    eauto. eauto. 
    rewrite plift_empty. unfoldq. intuition.
    rewrite plift_empty. unfoldq. intuition.
Qed.

Lemma envt_store_changeV': forall M M' H1 H2 V1 V2 G p,
    env_type M H1 H2 (V1) (V2) G false p ->
    st_len1 M <= st_len1 M' -> 
    st_len2 M <= st_len2 M' ->
    env_type M' H1 H2 (V1) (V2)  G false p.
Proof.
  intros. destruct H as (LH1 & LH2 & LV1 & LV2 & LW & IX).
  split. 2: split. 3: split. 4: split. 5: split.
  - eauto. 
  - eauto.
  - eauto.
  - eauto.
  - eauto.
  - intros. edestruct IX as (v1 & v2 & u & ls1 & ls2 & IX1' & IX2' & IV1' & IV2' & IW' & UX & VX & VQ1 & VQ2). eauto.
    exists v1, v2, u, ls1, ls2. split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 8: split. 
    all: eauto.
    destruct u.
    2: { intros. eapply valt_store_reset. eauto.
    intuition. intuition. eauto. eauto. }
    intros. eapply valt_store_reset. eauto.
    intros. eapply VQ1. destruct fr,a; eauto.
    intros. eapply VQ2. destruct fr,a; eauto.
    eauto. eauto. 
Qed.

Lemma envt_store_changeV''': forall M M' H1 H2 V1 V2 G p,
    env_type M H1 H2 (V1) (V2) G false p ->
    st_len1 M <= st_len1 M' -> 
    st_len2 M <= st_len2 M' ->
    env_type M' H1 H2 (restrictV false V1) (restrictV false V2)  G false p.
Proof.
  intros. destruct H as (LH1 & LH2 & LV1 & LV2 & LW & IX).
  split. 2: split. 3: split. 4: split. 5: split.
  - eauto. 
  - eauto.
  - simpl. rewrite map_length. eauto.
  - simpl. rewrite map_length. eauto.
  - eauto.
  - intros. edestruct IX as (v1 & v2 & u & ls1 & ls2 & IX1' & IX2' & IV1' & IV2' & IW' & UX & VX & VQ1 & VQ2). eauto.
    exists v1, v2, u, ls1, ls2. split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 8: split. 
    all: eauto.
    3: { intros. eapply valt_store_reset. eauto.
    intuition. intuition. eauto. eauto. }    
    intros. intuition. 
    assert (ls1 = qempty). {
    eapply functional_extensionality. intros.
    simpl. unfold qempty. remember (ls1 x0). destruct b. 2: eauto.
    symmetry in Heqb. eapply H4 in Heqb. contradiction. }
    simpl. erewrite indexr_map. subst. eauto. eauto.
    
    intros. intuition. 
    assert (ls2 = qempty). {
    eapply functional_extensionality. intros.
    simpl. unfold qempty. remember (ls2 x0). destruct b. 2: eauto.
    symmetry in Heqb. eapply H10 in Heqb. contradiction. }
    simpl. erewrite indexr_map. subst. eauto. eauto.
Qed.


Definition env_typeV (u:bool) M H1 H2 V1' V2' G p :=
  exists V1 V2,
    env_type M H1 H2 V1' V2' G u p /\
    (V1' = restrictV u V1) /\
    (V2' = restrictV u V2).  
  

Lemma envt_tightenV: forall M H1 H2 V1 V2 G u p p',
    env_typeV u M H1 H2 V1 V2 G p ->
    psub p' p ->
    env_typeV u M H1 H2 V1 V2 G p'.
Proof.
  intros. destruct H as (?&?&?&?&?).
  eapply envt_tighten in H; eauto. subst.
  eexists _,_. intuition. 
Qed.

Lemma envt_usableV: forall M H1 H2 V1 V2 G u u' p,
    env_typeV u M H1 H2 (restrictV u V1) (restrictV u V2) G p ->
    bsub u' u ->
    env_typeV u' M H1 H2 (restrictV u' V1) (restrictV u' V2) G p.
Proof.
  intros. destruct H as (?&?&?&?&?).
  subst. eapply envt_strengthenW with (uw':=u') in H; eauto.
  eexists _,_. intuition. 
Qed.

Lemma envt_usableV': forall M H1 H2 V1 V2 G u u' p,
    env_typeV u M H1 H2 V1 V2 G p ->
    bsub u' u ->
    env_typeV u' M H1 H2 (restrictV u' V1) (restrictV u' V2) G p.
Proof.
  intros. unfold bsub in H0. destruct H as (?&?&?&?&?).
  subst. eapply envt_strengthenW with (uw':=u') in H; eauto.
  eexists _,_. intuition. eauto.
  destruct u,u'; eauto. unfold bsub in H0. intuition.
  simpl in *. rewrite map_map, map_map. eauto. 
Qed.


Lemma envt_store_changeV: forall M M' H1 H2 V1 V2 G u p,
    env_typeV u M H1 H2 V1 V2 G p ->
    (u = true -> st_chain_partial M M' (vars_locs V1 p) (vars_locs V2 p)) ->
    st_len1 M <= st_len1 M' -> 
    st_len2 M <= st_len2 M' ->
    env_typeV u M' H1 H2 V1 V2 G p.
Proof.
  intros. destruct H as (?&?&?&?&?).
  destruct u. 
  eapply envt_store_change in H; eauto.
  eexists _,_. eauto. eauto. simpl in *. subst. eauto. 
  eexists _,_. intuition. subst. eauto. 
  eapply envt_store_changeV' in H; eauto.
Qed.


Lemma envt_extendV: forall M H1 H2 V1 V2 G v1 v2 T1 u ls1 ls2 fr1 a1 p,
    env_typeV true M H1 H2 V1 V2 G p ->
    val_type M v1 v2 T1 (u=true) ls1 ls2 ->
    u = true ->
    ((fr1||a1 = false \/ u=false) -> psub (plift ls1) pempty) ->
    ((fr1||a1 = false \/ u=false) -> psub (plift ls2) pempty) ->
    env_typeV true M (v1::H1) (v2::H2) (ls1::V1) (ls2::V2) ((T1,fr1,a1)::G) (por p (pone (length G))).
Proof.
  intros. destruct H as (?&?&?&?&?).
  eapply envt_extend in H; eauto.
  eexists _,_. split. eauto. intuition.
  destruct fr1,a1; eauto. intuition. intuition. 
Qed.

Lemma envt_emptyV: forall p u,
    env_typeV u st_empty [] [] [] [] [] p.
Proof.
  intros. eexists _,_. split.
  eapply envt_empty. 
  destruct u; intuition.
Qed.


Definition sem_type_useU G t1 t2 T p fr a e :=
  forall M H1 H2 V1 V2,
    env_type M H1 H2 V1 V2 G true p ->
    exp_type_eff M H1 H2 V1 V2 t1 t2 T true fr a e.


Definition sem_type_mentionU G t1 t2 T p fr a e :=
  forall M H1 H2 V1 V2 V1' V2',
    env_type M H1 H2 V1' V2' G e p ->
    (V1' = restrictV e V1) ->
    (V2' = restrictV e V2) ->
    (e = false) -> 
    exp_type_eff M H1 H2 V1' V2' t1 t2 T false fr a e.

Definition sem_type_genericU (u: bool) G t1 t2 T p fr a e :=
  if u then sem_type_useU G t1 t2 T p fr a e
  else  sem_type_mentionU G t1 t2 T p fr a e.

Definition sem_type_genericV (u: bool) G t1 t2 T p fr a e :=
  forall M H1 H2 V1' V2',
    env_typeV u M H1 H2 V1' V2' G p ->    
    exp_type_eff M H1 H2 V1' V2' t1 t2 T u fr a e.


Lemma sem_type_equiv: forall u G t1 t2 T p fr a e,
    bsub e u ->
    sem_type_genericU u G t1 t2 T p fr a e <->
    sem_type_genericV u G t1 t2 T p fr a e.
Proof.
  intros. destruct u; simpl.
  - split.
    + intros ???????????????.
      destruct H3 as (?&?&?&?&?). simpl in *. subst. 
      edestruct H0 as (?&?&?&?); eauto.
      eexists _,_,_. eauto.
    + intros ???????????????.
      simpl in *. subst.
      eapply H0; eauto.
      edestruct H3 as (?&?&?&?); simpl; eauto. 
      eexists _,_. simpl in *. eauto.
  - split.
    + intros ???????????????. destruct e. intuition.
      edestruct H3 as (?&?&?&?&?). simpl in *. 
      eapply H0; eauto.      
    + intros ????????????????????. simpl in *. subst.
      eapply H0; eauto.
      edestruct H3 as (?&?&?&?); simpl; eauto.
      eexists _,_. simpl in *. intuition. 
Qed.


Definition sem_type G t1 t2 T p fr a e :=
  forall u, 
    bsub e u ->
    forall M H1 H2 V1 V2,
    env_type M H1 H2 V1 V2 G u p ->
    exp_type_eff M H1 H2 V1 V2 t1 t2 T u fr a e.


Lemma sem_type_strengthen: forall G T t1 t2 p fr a e af,
    has_type G t1 T p fr a e ->
    has_type G t2 T p fr a e ->
    env_cap G p af ->
    sem_type G t1 t2 T (plift p) fr a e ->
    sem_type G t1 t2 T (plift p) fr (a&&af) (e&&af).
Proof.
  intros. 
  destruct af. replace (a&&true) with a. replace (e&&true) with e.
  2: destruct e; eauto. 2: destruct a; eauto. eauto.
  intros ????????????????.
  assert (env_type M H4 H5 V1 V2 G true (plift p)) as WFE'. {
    destruct u. eauto. eapply envt_strengthenW2. 2: eauto. eauto. 
  }
  remember WFE' as WFE''. clear HeqWFE''.
  destruct WFE'' as (?&?&W'&?&?).
  eapply hast_fv1 with (u:=true) in H1 as HX1. 2: eapply H. 2: eauto. 2: eauto.
  eapply hast_fv1 with (u:=true) in H1 as HX2. 2: eapply H0. 2: eauto. 2: eauto. 
  destruct HX1 as (HX11 & HX12).
  destruct HX2 as (HX21 & HX22).
  edestruct H2 with (u:=true) as (?&?&?&?).
  unfold bsub. intuition.
  eauto. eauto. eauto. 
  intros ? Q. destruct e; eauto. edestruct HX11 in Q. eauto.
  intros ? Q. destruct e; eauto. edestruct HX22 in Q. eauto.
  eapply exp_strengthen1 in H15. 2: eauto. 2: eauto.
  eapply exp_sub; eauto.
  eexists _,_,_. eapply exp_usable1. eauto. eauto. 
  unfold bsub. intuition.
  unfold bsub. intuition.
  unfold bsub. intuition.
Qed.


Lemma exp_abs: forall S1 S2 M H1 H2 V1 V2 t1 t2 T1 T2 (uv u: bool) fr fr1 a1 af a e p1 p2,
    stty_wellformed M ->
    store_type S1 S2 M p1 p2 ->
    (forall S1' S2' M' p1' p2' vx1 vx2 (ux: bool) lsx1 lsx2 (uy uyv:bool),
        (e || uy && a = true -> st_chain_partial M M' (pif ((e||a)) (exp_locs (restrictV ((e||a)&&af&&u) V1) (tabs t1))) (pif ((e||a)) (exp_locs (restrictV ((e||a)&&af&&u) V2) (tabs t2)))) ->
        (e || uy && a = true -> u=true) ->
        (e || uy && a = true -> ux=true) ->
        bsub e uyv -> 
        (uy = negb a || uyv) -> 
        (fr1||a1=false -> ux=true) -> 
        stty_wellformed M' ->
        st_len1 M <= st_len1 M' -> 
        st_len2 M <= st_len2 M' ->
        store_type S1' S2' M' p1' p2' ->
        (psub (pif (((e||a)&&af)&&e) (exp_locs V1 (tabs t1))) p1') ->
        (psub (pif (((e||a)&&af)&&e) (exp_locs V2 (tabs t2))) p2') ->
        (psub (pif e (plift lsx1)) p1') ->
        (psub (pif e (plift lsx2)) p2') ->
        (fr1 || a1 = false \/ ux = false -> psub (plift lsx1) pempty) ->
        (fr1 || a1 = false \/ ux = false -> psub (plift lsx2) pempty) ->
        val_type M' vx1 vx2 T1 (ux = true) lsx1 lsx2->
        exp_type S1' S2' M' (vx1 :: H1) (vx2 :: H2) (lsx1 :: (restrictV ((e||a)&&af&&u) V1)) (lsx2 :: (restrictV ((e||a)&&af&&u) V2) ) t1 t2 T2 (uyv) p1' p2' fr a e) ->
    (((e||a)&&af) = false  \/ u = false  -> psub (pif ((e||a)) (exp_locs (restrictV ((e||a)&&af&&u) V1) (tabs t1))) pempty) ->
    (((e||a)&&af) = false  \/ u = false  -> psub (pif ((e||a)) (exp_locs (restrictV ((e||a)&&af&&u) V2) (tabs t2))) pempty) ->
    u = negb ((e||a)&&af) || uv ->
    exp_type S1 S2 M H1 H2 V1 V2 (tabs t1) (tabs t2) (TFun T1 fr1 a1 T2 fr a e) (uv) p1 p2 false ((e||a)&&af) false.
Proof.
  intros ????????????????????? SW ST HY VQF1 VQF2 UV.
  exists S1, S2, M.
  exists (vabs H1 t1), (vabs H2 t2).
  eexists (negb ((e || a) && af) || u).
  exists ((qif (((e||a)&&af)&&u) (exp_locs_fix (restrictV ((e||a)&&af) V1) (tabs t1)))), ((qif (((e||a)&&af)&&u) (exp_locs_fix (restrictV ((e||a)&&af) V2) (tabs t2)))).
  split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 8: split. 9: split. 10: split.
  11: split. 12: split. 13: split. 14: split. 15: split. 16: split. 
  - eapply stchain_refl.
  - eauto. 
  - exists 0. intros. destruct n. lia. simpl. eauto.
  - exists 0. intros. destruct n. lia. simpl. eauto.
  - eauto.
  - eauto.
  - eapply storet_tighten. eauto.
    unfoldq. intuition.
    unfoldq. intuition. 
  - simpl. intros.

    edestruct HY as (S1'' & S2'' & M'' & vy1 & vy2 & uvy & lsy1 & lsy2 & SC' & SW' & TY1 & TY2 & LS1' & LS2' & ST' & VY & UVY1 & UVY2 & LUY1 & LUY2 & LY1 & LY2 & ES1 & ES2 & ESM). eauto. eauto. 
    17: eauto. 10: eauto. all: eauto.
    intros ??????. eapply H. eauto. eauto. 
    rewrite plift_if, plift_exp_locs. destruct u,af,e,a; simpl in *; intuition; try eapply aux2 in H18; unfoldq; intuition.
    
    rewrite plift_if, plift_exp_locs. destruct u,af,e,a; simpl in *; intuition; try eapply aux2 in H18; unfoldq; intuition.
    
    intros. eapply H0 in H16. destruct e, a, af; simpl in *; auto. 

    rewrite plift_if, plift_exp_locs in *. unfoldq. destruct e,u,af,a; simpl in *; intuition. 
    rewrite plift_if, plift_exp_locs in *. unfoldq. destruct u,e,a,af; simpl in *; intuition. 
    unfoldq. destruct e; intuition.
    unfoldq. destruct e; intuition.

    assert (uy = uvy). destruct uvy, uyv, a; simpl in *; intuition.
    subst uvy uy. 

    exists S1'', S2'', M'', vy1, vy2, lsy1, lsy2. intuition.
    + intros ? Q. 
      eapply LY1 in Q. destruct Q as [HYQ | [HUQ | HFr]].
      * destruct a. 2: contradiction.
        rewrite <-por_assoc. left. rewrite plift_if, plift_exp_locs. eapply exp_locs_abs in HYQ. 
        destruct HYQ. {
          destruct e,af; simpl in *.  2: { eapply aux2 in H14. unfoldq; intuition. }
          rewrite H0; auto. left. destruct u. auto. eapply aux2 in H14; eauto. unfoldq; intuition.
          simpl. left. destruct u; auto.  eapply aux2 in H14. unfoldq; intuition.
          eapply aux2 in H14; eauto. unfoldq; intuition.
        } {
          right. auto.
        }
      * right. right. left. eauto. 
      * right. right. right. eauto.
    + intros ? Q. eapply LY2 in Q. destruct Q as [HYQ | [HUQ | HFr]].
      * destruct a. 2: contradiction.
        rewrite <-por_assoc. left. rewrite plift_if, plift_exp_locs. eapply exp_locs_abs in HYQ. 
        destruct HYQ. {
          destruct e,af; simpl in *. 2: { eapply aux2 in H14. unfoldq; intuition. }
          rewrite H0 in *; auto. left. auto.
          simpl. left. destruct u; simpl in *; auto; intuition. eapply aux2 in H14. unfoldq; intuition.
          eapply aux2 in H14; eauto. unfoldq; intuition.
        } {
          right. auto.
        }
      * right. right. left. eauto.
      * right. right. right. eauto. 
    + rewrite plift_if, plift_exp_locs. intros ? (Q1 & Q2). eapply ES1. split. eauto.
      destruct e; unfoldq; intuition. eapply exp_locs_abs in H14. 
      destruct H14. 2: { intuition. }
      destruct af. 2: { eapply aux2 in H14. unfoldq; intuition. }
      simpl in *. eapply H.  destruct u; simpl in *; intuition. 
    + rewrite plift_if, plift_exp_locs. intros ? (Q1 & Q2). eapply ES2. split. eauto.
      destruct e; unfoldq; intuition. eapply exp_locs_abs in H14. 
      destruct H14. 2: { intuition. }
      destruct af. 2: { eapply aux2 in H14. unfoldq; intuition. }
      simpl in *. eapply H.  destruct u; simpl in *; intuition. 
  - destruct e, a, af, u, uv; intuition.
  - eauto.
  - intros. rewrite plift_if, plift_exp_locs. 
    destruct af, u; simpl in *; intuition. destruct e, a; simpl; unfoldq; intuition.
  - intros. rewrite plift_if, plift_exp_locs. eauto.
    destruct af, u; simpl in *; intuition. destruct e, a; simpl; unfoldq; intuition.
  - rewrite plift_if, plift_exp_locs. intros ??. 
    left. destruct u; simpl in *. destruct e, a, af; simpl in *; auto.
    destruct e, a, af; simpl in *; unfoldq; intuition.
  - rewrite plift_if, plift_exp_locs. intros ??. 
    left. destruct u; simpl in *. destruct e, a, af; simpl in *; auto.
    destruct e, a, af; simpl in *; unfoldq; intuition.
  - eapply storew_refl.
  - eapply storew_refl.
  - intuition. 
Qed.

Lemma aux3: forall M H1 H2 V1' V2' env pf um,
    env_type M H1 H2 V1' V2' env um (plift pf) ->
    env_cap env pf false ->
    psub (vars_locs V1' (plift pf)) pempty.
Proof. 
  intros ???????? WFE' WCE'.
  intros ? Q. destruct Q as (?&?&?&IX&?).
  eapply indexr_var_some' in IX as IX'.
  replace (length V1') with (length env) in IX'. 2: symmetry; eapply WFE'.
  eapply indexr_var_some in IX'.
  destruct IX' as (((Tx & frx) & ax) & IX').
  eapply WFE' in IX' as IX''.
  destruct IX'' as (?&?&?&?&?&?&?&?&?&?&?&?&?&?).
  eapply WCE' in H as H'. 2: eauto. 
  remember (frx||ax) as frax. destruct frax. unfold bsub in H'. intuition.
  rewrite H5 in IX. inversion IX. subst x1. eapply H10 in H0. contradiction.
  eauto. eauto.
Qed.

Lemma aux3': forall M H1 H2 V1' V2' env pf um,
    env_type M H1 H2 V1' V2' env um (plift pf) ->
    env_cap env pf false ->
    psub (vars_locs V2' (plift pf)) pempty.
Proof. 
  intros ???????? WFE' WCE'.
  intros ? Q. destruct Q as (?&?&?&IX&?).
  eapply indexr_var_some' in IX as IX'.
  replace (length V2') with (length env) in IX'. 2: symmetry; eapply WFE'.
  eapply indexr_var_some in IX'.
  destruct IX' as (((Tx & frx) & ax) & IX').
  eapply WFE' in IX' as IX''.
  destruct IX'' as (?&?&?&?&?&?&?&?&?&?&?&?&?&?).
  eapply WCE' in H as H'. 2: eauto. 
  remember (frx||ax) as frax. destruct frax. unfold bsub in H'. intuition.
  rewrite H6 in IX. inversion IX. subst x1. eapply H11 in H0. contradiction.
  eauto. eauto.
Qed.


Lemma sem_abs: forall G t1 t2 T1 fr1 a1 T2 fr2 a2 e2 p2 pf af,
    sem_type ((T1,fr1,a1)::G) t1 t2 T2 (plift p2) fr2 a2 e2 ->
    pf = (qdiff p2 (qone (length G))) ->
    p2 = fv (S (length G)) t1 ->
    fv (S (length G)) t1 = fv (S (length G)) t2 ->
    env_cap G pf af ->
    sem_type G (tabs t1) (tabs t2) (TFun T1 fr1 a1 T2 fr2 a2 e2) (plift pf) false ((e2||a2)&&af) false.
Proof.
  intros.
  rename H into IHW.
  rename H0 into A1.
  rename H1 into A2.
  rename H2 into A3. 
  intros um E ? ? ? ? ? WFE. intros SW ?? ps1 ps2 ST P1 P2.

  assert True. eauto.
  assert True. eauto.
  assert True. eauto.

    eexists S1, S2, M.
    eexists (vabs H1 t1), (vabs H2 t2).
    eexists (negb ((e2 || a2) && af) || um).
  exists ((qif ((e2||a2)&&af&&um) (exp_locs_fix (V1) (tabs t1)))), ((qif ((e2||a2)&&af&&um) (exp_locs_fix (V2) (tabs t2)))).
    split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 8: split. 9: split. 10: split.
    11: split. 12: split. 13: split. 14: split. 15: split. 16: split.

    9: eauto. 9: eauto.
    
    + eapply stchain_refl.
    + eauto. 
    + exists 0. intros. destruct n. lia. simpl. eauto.
    + exists 0. intros. destruct n. lia. simpl. eauto.
    + eauto.
    + eauto.
    + eapply storet_tighten. eauto.
      unfoldq. intuition.
      unfoldq. intuition.

    + simpl. intros.

      remember (e2 || uy && a2) as D.
      destruct D.
      * (* use *)

        assert (um = false -> af = true -> e2 = false). destruct um,af,e2; intuition.
        assert (um = false -> af = true -> a2 = false). destruct um,af,a2; intuition.
        assert (um = false -> af = false). intros. destruct af. {
          replace a2 with false in *. 2: intuition.
          replace e2 with false in *. 2: intuition.
          destruct uy; inversion HeqD. } eauto. 

                
        assert (e2||a2 = true). destruct e2,a2; intuition. 

        edestruct (IHW true) as (S1'' & S2'' & M'' & EXP). unfold bsub. intuition. {
        eapply envt_tighten. eapply envt_extend.
        eapply envt_store_change with (M:=M) (p:=plift pf).
        eapply envt_strengthenWX'; eauto. 

        subst pf p2.
        rewrite A3 at 2.
        intros ?????. eapply H5. eauto. eauto.

        destruct af. destruct um. 2: intuition.
        rewrite H23. simpl. rewrite plift_if, plift_exp_locs. unfold exp_locs.
        destruct WFE as (?&?&L1&L2&?&?).
        rewrite L1. simpl. eauto.
        eapply aux3 in H25. contradiction.
        eauto. eauto. 

        destruct af. destruct um. 2: intuition.
        rewrite H23. simpl. rewrite plift_if, plift_exp_locs. unfold exp_locs.
        destruct WFE as (?&?&L1&L2&?&?).
        rewrite L2. simpl. eauto.
        eapply aux3' in H26. contradiction.
        rewrite <-A3. eauto.
        rewrite <-A3. eauto.

        eauto. eauto. eauto. rewrite H7. destruct fr1,a1; eauto. eauto.
        intuition. intuition.
        subst. rewrite plift_diff, plift_one. unfoldq. intuition. bdestruct (x =? length G); intuition. }

        eauto. eauto.

        { intros ? Q. destruct e2. 2: contradiction. eapply exp_locs_abs in Q. destruct Q; eauto.
        2: { eapply H15. right. eauto. }
        eapply H15. simpl in *. destruct af. left. rewrite plift_if, plift_exp_locs.
        destruct um. eauto. intuition. 

        subst pf p2. 
        eapply aux3 in H24. contradiction.
        replace (length V1) with (length G). 2: symmetry;eapply WFE. simpl. eapply WFE.
        replace (length V1) with (length G). 2: symmetry;eapply WFE. simpl. eauto. }

        { intros ? Q. destruct e2. 2: contradiction. eapply exp_locs_abs in Q. destruct Q; eauto.
        2: { eapply H16. right. eauto. }
        eapply H16. simpl in *. destruct af. left. rewrite plift_if, plift_exp_locs.
        destruct um. eauto. intuition. 

        subst pf p2. 
        eapply aux3' in H24. contradiction.
        replace (length V2) with (length G). 2: symmetry;eapply WFE. simpl. rewrite <-A3. eapply WFE.
        replace (length V2) with (length G). 2: symmetry;eapply WFE. simpl. rewrite <-A3. eauto. }

        eapply exp_usable1 with (u':=uyv) in EXP.

        destruct EXP as (vy1 & vy2 & uy0 & lsy1 & lsy2 & EXP).
        destruct EXP as (?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?).

        assert (uy0 = negb a2 || uyv). eapply H32. 
        
        eexists S1'', S2'', M'', vy1, vy2, lsy1, lsy2.
        split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 8: split. 9: split. 10: split.
        11: split. 12: split. 13: split. 14: split.
        1-7: eauto. 
        -- subst uy uy0. eauto.
        -- subst uy uy0. eauto. 
        -- subst uy uy0. eauto. 
        -- intros ? Q.
           destruct uy0. 2: { eapply H34 in Q. contradiction. eauto. }
           eapply H36 in Q. destruct Q as [? | [? | ?]].
           destruct a2. 2: contradiction.
           eapply exp_locs_abs in H42. destruct H42. 2: { right. left. eauto. }
           destruct af. left. rewrite plift_if, plift_exp_locs. destruct um. 2: intuition. destruct e2; eauto.
           subst pf p2. 
           eapply aux3 in H42. contradiction.
           replace (length V1) with (length G). eapply WFE. symmetry; eapply WFE.
           simpl. replace (length V1) with (length G). eauto. symmetry; eapply WFE.
           contradiction. right. right. right. eauto.
        -- intros ? Q.
           destruct uy0. 2: { eapply H35 in Q. contradiction. eauto. }
           eapply H37 in Q. destruct Q as [? | [? | ?]].
           destruct a2. 2: contradiction.
           eapply exp_locs_abs in H42. destruct H42. 2: { right. left. eauto. }
           destruct af. left. rewrite plift_if, plift_exp_locs. destruct um. 2: intuition. destruct e2; eauto.
           subst pf p2. 
           eapply aux3' in H42. contradiction.
           simpl. 
           replace (length V2) with (length G). 
           rewrite <-A3.
           eapply WFE. symmetry; eapply WFE.
           simpl. replace (length V2) with (length G). rewrite <-A3. eauto. symmetry; eapply WFE.
           contradiction. right. right. right. eauto.
        -- intros ??. eapply H38. destruct H42. split. eauto. intros C. eapply H43.
           destruct e2. 2: contradiction.
           eapply exp_locs_abs in C. destruct C. 2: { right. eauto. }
           destruct af. left. rewrite plift_if, plift_exp_locs. destruct um. 2: intuition. eauto.
           subst pf p2. 
           eapply aux3 in H44. contradiction.
           replace (length V1) with (length G). eapply WFE. symmetry; eapply WFE.
           simpl. replace (length V1) with (length G). eauto. symmetry; eapply WFE.
        -- intros ??. eapply H39. destruct H42. split. eauto. intros C. eapply H43.
           destruct e2. 2: contradiction.
           eapply exp_locs_abs in C. destruct C. 2: { right. eauto. }
           destruct af. left. rewrite plift_if, plift_exp_locs. destruct um. 2: intuition. eauto.
           subst pf p2. 
           eapply aux3' in H44. contradiction.
           replace (length V2) with (length G). simpl. rewrite <-A3. eapply WFE. symmetry; eapply WFE.
           simpl. replace (length V2) with (length G). rewrite <-A3. eauto. symmetry; eapply WFE.
        -- eauto.
        -- eauto.

      * (* mention *)
        assert (e2 = false). destruct e2,a2; intuition.
        assert (a2 = false \/ uyv = false). destruct e2,a2,uy; intuition.
        subst e2.

        edestruct (IHW false) as (S1'' & S2'' & M'' & EXP). unfold bsub. intuition. {
          eapply envt_tighten. eapply envt_extend.
          eapply envt_store_changeV' with (M:=M) (p:=plift pf).
          destruct um. eapply envt_strengthenW1; eauto. eauto. 
          eauto. eauto. 2: eauto.

          remember (fr1||a1) as D. destruct D. simpl. 
          subst. eapply valt_reset_locs. eapply valt_usable. eauto. intuition. intuition.
          subst. simpl. rewrite H10 in *; eauto.
          erewrite aux1 at 1.
          erewrite aux1 at 1.
          eauto. eauto. eauto. 
          subst. rewrite plift_empty. unfoldq. intuition.
          subst. rewrite plift_empty. unfoldq. intuition. 

          clear H21.
          subst pf. rewrite plift_diff, plift_one. unfoldq. intuition.
          bdestruct (x =? length G); intuition.
        }
        eauto. eauto.
        intuition. intuition. 

        eapply exp_mentionable with (uv:=uyv)
          (V1':=lsx1::restrictV um V1) (V2':=lsx2::restrictV um V2) in EXP.

        destruct EXP as (vy1 & vy2 & uy0 & lsy1 & lsy2 & EXP).
        destruct EXP as (?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?).

        eexists S1'', S2'', M'', vy1, vy2, lsy1, lsy2.
        split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 8: split. 9: split. 10: split.
        11: split. 12: split. 13: split. 14: split.
        1-7: eauto.
        -- subst uy uy0. eauto.
        -- subst uy uy0. eauto.
        -- subst uy uy0. eauto.
        -- intros ? Q. 
           eapply H33 in Q. destruct Q as [? | [? | ?]].
           destruct a2. 2: contradiction.
           eapply exp_locs_abs in H38. destruct H38. 2: { right. left. eauto. }
           destruct um. 2: { eapply aux2 in H38. contradiction. } simpl in H38. 
           destruct af. left. rewrite plift_if, plift_exp_locs. eauto.
           subst pf p2. 
           eapply aux3 in H38. contradiction.
           replace (length V1) with (length G). eapply WFE. symmetry; eapply WFE.
           simpl. replace (length V1) with (length G). eauto. symmetry; eapply WFE.
           contradiction. right. right. right. eauto.
        -- intros ? Q. 
           eapply H34 in Q. destruct Q as [? | [? | ?]].
           destruct a2. 2: contradiction.
           eapply exp_locs_abs in H38. destruct H38. 2: { right. left. eauto. }
           destruct um. 2: { eapply aux2 in H38. contradiction. } simpl in H38. 
           destruct af. left. rewrite plift_if, plift_exp_locs. eauto.
           subst pf p2. 
           eapply aux3' in H38. contradiction.
           replace (length V2) with (length G). simpl. rewrite <-A3. eapply WFE. symmetry; eapply WFE.
           simpl. replace (length V2) with (length G). rewrite <-A3. eauto. symmetry; eapply WFE.
           contradiction. right. right. right. eauto.
        -- intros ??. eapply H35. destruct H38. split. eauto. intros C. eapply H39.
           contradiction. 
        -- intros ??. eapply H36. destruct H38. split. eauto. intros C. eapply H39.
           contradiction.
        -- eauto.
        -- eauto.
        -- eauto.

    + intros. intros ? Q.
      assert ((e2 || a2) && af = true). destruct e2,a2,af,um; eauto.
      assert (um = false). destruct e2,a2,af,um; eauto.
      rewrite H6, H7 in *. rewrite plift_if in Q. contradiction.
    + intros. intros ? Q.
      assert ((e2 || a2) && af = true). destruct e2,a2,af,um; eauto.
      assert (um = false). destruct e2,a2,af,um; eauto.
      rewrite H6, H7 in *. rewrite plift_if in Q. contradiction.
    + rewrite plift_if, plift_exp_locs. intros ? Q.
      destruct um. left. destruct e2,a2,af; eauto.
      destruct e2,a2,af; contradiction.
    + rewrite plift_if, plift_exp_locs. intros ? Q.
      destruct um. left. destruct e2,a2,af; eauto.
      destruct e2,a2,af; contradiction.
    + intros ? Q. eauto.
    + intros ? Q. eauto.
    + eauto.

Qed.


Theorem fundamental: forall G t T p fr a e,
    has_type G t T p fr a e -> 
    sem_type G t t T (plift p) fr a e.
Proof.
  intros ? ? ? ? ? ? ? W. 
  induction W; intros um E; intros ????? WFE; intros SW ?? ps1 ps2 ST P1 P2.
  - (* true *)
    eapply exp_true; eauto.
  - (* false *)
    eapply exp_false; eauto. 
  - (* var *) 
    eapply WFE in H as H'. destruct H' as (v1 & v2 & uv & ls1 & ls2 & IX1 & IX2 & IV1 & IV2 & IW & UX & VX & VQ1 & VQ2).
    
    inversion IW. subst uv. 
    eapply exp_var; eauto. 
    eapply VX. rewrite plift_one. intuition.
  - (* ref *)
    eapply exp_ref; eauto. 
    eapply IHW; eauto.
  - (* get *)
    eapply exp_get; eauto.
    eapply IHW; eauto.
    destruct e; unfold bsub; intuition.
    destruct e; unfoldq; intuition.
    destruct e; unfoldq; intuition.
    
  - (* put *)
    rewrite plift_or in *.
    edestruct IHW1 with (u := um) as (S1' & S2' & M' & ?); eauto.
    unfold bsub. destruct e1; intuition.
    eapply envt_tighten. eapply WFE. unfoldq; intuition.
    intros ? ?. eapply P1. rewrite exp_locs_put. unfoldq. destruct e1; simpl in *; intuition. 
    intros ? ?. eapply P2. rewrite exp_locs_put. unfoldq. destruct e1; simpl in *; intuition.
    eapply exp_put; eauto.
    destruct H as (?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?). 
    eapply IHW2 with (u := um) (M := M').
    destruct e2; unfold bsub; intuition.        
    eapply envt_store_change. eapply envt_tighten. eapply WFE. unfoldq. intuition.
    intros ?????. eauto.
    destruct ST as (?&?&?). destruct s1 as (?&?&?). lia.
    destruct ST as (?&?&?). destruct s1 as (?&?&?). lia.
    eauto. eauto.  eauto.
    rewrite exp_locs_put in *. unfoldq. destruct e1,e2; simpl in *; intuition.
    rewrite exp_locs_put in *. unfoldq. destruct e1,e2; simpl in *; intuition.

  - (* app *)
    rewrite plift_or in *.
    edestruct IHW1 with (u := um) as (S1' & S2' & M' & ?); eauto.
    unfold bsub. destruct ef; intuition.
    eapply envt_tighten. eauto. unfoldq. intuition. 
    rewrite exp_locs_app in *. unfoldq. destruct e1,ef; simpl in *; intuition. 
    rewrite exp_locs_app in *. unfoldq. destruct e1,ef; simpl in *; intuition.    
    eapply exp_app; eauto.
    destruct H as (?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?).
    eapply IHW2 with (u :=um) (M := M').
    unfold bsub. destruct e1; intuition.            
    eapply envt_store_change. eapply envt_tighten. eauto. unfoldq; intuition.
    intros ?????. eauto.
    destruct ST as (?&?&?). destruct H7 as (?&?&?). lia.
    destruct ST as (?&?&?). destruct H7 as (?&?&?). lia.
    eauto. eauto. eauto. 
    rewrite exp_locs_app in *. unfoldq. destruct e1,e2; simpl in *; intuition.
    rewrite exp_locs_app in *. unfoldq. destruct e1,e2; simpl in *; intuition.

    unfold bsub in *. destruct e2, um, af, a1, a2; simpl in *; intuition.
    unfold bsub in *. destruct e2, um, af, a1, a2; simpl in *; intuition.
    unfold bsub in *. destruct e2, um, af, a1, a2; simpl in *; intuition.
    unfold bsub in *. destruct e2, um, af, a1, a2; simpl in *; intuition.
    
  - (* abs *)
    eapply exp_abs; eauto. {
      intros.

      assert (e2||uy&&a2 = (e2||a2)&&uyv) as EQ1. {
        destruct e2,a2,uy,uyv; intuition.
      }
      assert ((e2||a2)&&uyv = true -> af = false \/ um = true) as EQ2. {
        destruct e2,a2,af,uy,uyv; intuition.
      }
      assert ((e2||a2)&&uyv = false -> e2 = false /\ a2 = false \/ uyv = false) as EQ3. {
        destruct e2,a2,uyv; eauto.
      }

      remember (e2||uy&&a2) as D. destruct D.
      + (* use *)
        assert (um = false -> af = true -> e2 = false). destruct um,af,e2; intuition.
        assert (um = false -> af = true -> a2 = false). destruct um,af,a2; intuition.
        assert (um = false -> af = false). intros. destruct af. {
          replace a2 with false in *. 2: intuition.
          replace e2 with false in *. 2: intuition.
          destruct uy; inversion HeqD. } eauto. 

        assert (e2||a2 = true). destruct e2,a2; intuition. 

        eapply exp_usable. eapply (IHW true).
        3,4,7: simpl; eauto.
        unfold bsub. destruct e2; intuition.
        {
          rewrite H23 in *. simpl in *. rewrite H4 in *; auto; simpl in *.
          eapply envt_tighten. eapply envt_extend. eapply envt_store_change with (M:=M) (p:=plift pf).
          eapply envt_strengthenWX. 
          3: { destruct af; simpl; auto. }
          2: { unfold bsub in *. intros. destruct af; intuition.  }
          unfold restrictV. 
          destruct af; simpl in *. {
            rewrite H4 in *; auto.
          } {
            destruct um. {
              intuition.
            }{
              eapply envt_strengthenW2; auto.
            }
          } 
          eapply hast_fv in W. simpl in W. destruct WFE as (?&?&L1&L2&?). subst pf p2.
          intros ?????. eapply H3. eauto. eauto.

          unfold exp_locs. simpl. erewrite restrictV_length. rewrite L1. auto. auto. 
          unfold exp_locs. simpl. erewrite restrictV_length. rewrite L2. auto. auto.
          eauto. eauto.
          rewrite H5 in H19. eauto. eauto. 
          intuition. intuition. intuition. 
          subst pf. rewrite plift_diff, plift_one. unfoldq. intuition.
          bdestruct (x =? length env); intuition.
        }
        intros ? Q. destruct e2. 2: contradiction. eapply exp_locs_abs in Q. destruct Q; eauto.
        eapply H13. simpl in *. destruct af; eauto. simpl in *. rewrite H4 in H24; auto. simpl in *.
        eapply aux2 in H24. contradiction.
        intros ? Q. destruct e2. 2: contradiction. eapply exp_locs_abs in Q. destruct Q; eauto.
        eapply H14. simpl in *. destruct af. simpl in *. rewrite H4 in H24; auto.
        simpl in *. eapply aux2 in H24. contradiction.

      + (* mention *)
        assert (e2 = false). destruct e2,a2; intuition.
        assert (a2 = false \/ uyv = false). destruct e2,a2,uy; intuition.
        subst e2.

        eapply exp_mentionable1; eauto. eapply (IHW false) with
          (V1:=restrictV false (lsx1 :: V1))
          (V2:=restrictV false (lsx2 :: V2)).
          3,4,5,6: eauto.
        unfold bsub. intuition.
        {
          eapply envt_tighten. eapply envt_extend with (p := plift pf)(u := (negb (fr1||a1)) || false).
          destruct um. { eapply envt_store_changeV''. eauto. auto. auto. }
          {
            eapply envt_store_changeV'''. eauto. auto. auto.
          }
          remember (fr1||a1) as D. destruct D; simpl.
          eapply valt_reset_locs. eapply valt_usable. eauto.
          eauto. intuition. 
          erewrite aux1 at 1.
          erewrite aux1 at 1.
          rewrite H8 in H19. eapply H19. auto.
          eauto. eauto.
          auto. 
          rewrite plift_empty. unfoldq. intuition.
          rewrite plift_empty. unfoldq. intuition. 
          clear H21.
          subst pf. rewrite plift_diff, plift_one. unfoldq. intuition.
          bdestruct (x =? length env); intuition. 
        } 
    }

    replace (a2||e2) with (e2||a2). 2: eauto with bool. 
    destruct um. {
      intros. remember (e2||a2) as D. destruct D.
      intros. assert (af=false). destruct H3, af; eauto. subst af.
      simpl. eapply aux2. 
      simpl. unfoldq. intuition.
    } {      
      intros. intros ? Q. 
      destruct (e2||a2). 2: { contradiction. }
      destruct af. simpl in *. 
      eapply aux2; auto. eapply Q.
      simpl in *. eapply aux2; auto. eapply Q.
    }

    replace (a2||e2) with (e2||a2). 2: eauto with bool. 
    destruct um. {
      remember (e2||a2) as D. destruct D.
      intros. assert (af=false). destruct H3, af; eauto. subst af.
      simpl. eapply aux2. 
      simpl. unfoldq. intuition.
    } {
      intros. intros ? Q. 
      destruct (e2||a2). 2: { contradiction. }
      destruct af; simpl in *. 
      eapply aux2; auto. eapply Q.
      eapply aux2; auto. eapply Q.
    }
  - (* tnot *)
    eapply exp_tnot; eauto.
    eapply IHW; eauto.
  - (* tbin *)
    rewrite plift_or in *.
    edestruct IHW1 with (u := um) as (S1' & S2' & M' & ?); eauto. 
    unfold bsub. destruct e1; intuition.
    eapply envt_tighten. eapply WFE. unfoldq; intuition.
    intros ? ?. eapply P1. rewrite exp_locs_tbin. unfoldq. destruct e1; simpl in *; intuition. 
    intros ? ?. eapply P2. rewrite exp_locs_tbin. unfoldq. destruct e1; simpl in *; intuition.
    eapply exp_tbin; eauto. 
    destruct H as (?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?). 
    eapply IHW2 with (u := um) (M := M').
    destruct e2; unfold bsub; intuition.
    eapply envt_store_change. eapply envt_tighten. eapply WFE. unfoldq. intuition.
    intros ?????. eauto.
    destruct ST as (?&?&?). destruct s1 as (?&?&?). lia.
    destruct ST as (?&?&?). destruct s1 as (?&?&?). lia.
    eauto. eauto. eauto.
    rewrite exp_locs_tbin in *. unfoldq. destruct e1,e2; simpl in *; intuition.
    rewrite exp_locs_tbin in *. unfoldq. destruct e1,e2; simpl in *; intuition. 
    
  - (* sub_fresh *)
    destruct fr; try eapply exp_sub_fresh; eauto; eapply IHW; eauto.
  - (* sub_cap *)
    destruct um.
    destruct a; try eapply exp_sub_cap; eauto; eapply (IHW true); eauto.
    destruct a. eapply (IHW false); eauto.
    eapply exp_usable. eauto.
    eapply exp_sub_cap. eauto. eauto. 
    edestruct (IHW false); eauto. 
    exists x. eauto. eauto. 
  - (* sub_eff *)
    destruct um.
    destruct e; try eapply exp_sub_eff; eauto; eapply (IHW true); eauto.
    unfold bsub. intuition.
    unfoldq. intuition.
    unfoldq. intuition.
    destruct e. eapply (IHW false); eauto. unfold bsub in E. intuition.
Qed.

Theorem fundamental': forall G t T p fr a e af,
    has_type G t T p fr a e -> 
    env_cap G p af ->
    sem_type G t t T (plift p) fr (a&&af) (e&&af).
Proof.
  intros.
  eapply sem_type_strengthen. eauto. eauto. eauto. 
  eapply fundamental. eauto. 
Qed.


Corollary safety: forall t T p fr a e,
  has_type [] t T p fr a e ->
  exp_type [] [] st_empty [] [] [] [] t t T e pempty pempty fr a e.
Proof. 
  intros. eapply fundamental in H as ST; eauto.
  edestruct ST with (u:=e) (p1:=pempty) (p2:=pempty) as (S1' & S2' & M' & v1 & v2 & uy & ls1 & ls2 & ? & ? & ? & ? & ? & ?).
  unfold bsub. eauto. 
  eapply envt_empty.
  eapply sttyw_empty.
  eapply storet_empty.
  rewrite exp_locs_empty. unfoldq. destruct e; intuition.
  rewrite exp_locs_empty. unfoldq. destruct e; intuition.
  exists S1', S2', M', v1, v2, uy, ls1, ls2. split; intuition.
Qed.

Corollary safety_pure: forall t T p u,
  has_type [] t T p false false false ->
  exp_type [] [] st_empty [] [] [] [] t t T u pempty pempty false false false.
Proof. 
  intros. eapply fundamental in H as ST; eauto.
  edestruct ST with (u:=u) (p1:=pempty) (p2:=pempty) as (S1' & S2' & M' & v1 & v2 & uy & ls1 & ls2 & ? & ? & ?).
  unfold bsub. destruct u; eauto. 
  eapply envt_empty.
  eapply sttyw_empty.
  eapply storet_empty.
  intros ? Q. contradiction.
  intros ? Q. contradiction.
  exists S1', S2', M', v1, v2, uy, ls1, ls2. split; intuition.
Qed.




(* ---------- encoding 1: pure effect system  ---------- *)

Inductive ty_E : Type :=
| TBool_E  : ty_E
| TRef_E   : ty_E
| TFun_E   : ty_E -> ty_E -> bool -> ty_E  (* T1 -> T2 e *)
.

Definition tenv_E := list ty_E.

Fixpoint tty_E T :=
    match T with 
    | TBool_E => TBool
    | TRef_E => TRef 
    | TFun_E T1 T2 e => TFun (tty_E T1) true true (tty_E T2) true true e 
end.

Definition ttenv_E (G: tenv_E): tenv := map (fun p => (tty_E p, true, true)) G.

Inductive has_type_E: tenv_E -> tm -> ty_E -> ql -> bool -> Prop := 
| t_true_E: forall env,
    has_type_E env ttrue TBool_E qempty false
| t_false_E: forall env,
    has_type_E env tfalse TBool_E qempty false
| t_var_E: forall x env T,
    indexr x env = Some T ->
    has_type_E env (tvar x) T (qone x) false
| t_ref_E: forall t env p e,
    has_type_E env t TBool_E p e ->
    has_type_E env (tref t) TRef_E p true
| t_get_E: forall t env p e,
    has_type_E env t TRef_E p e ->
    has_type_E env (tget t) TBool_E p true
| t_put_E: forall t1 t2 env p1 p2 e1 e2,
    has_type_E env t1 TRef_E p1 e1 ->
    has_type_E env t2 TBool_E p2 e2 ->
    has_type_E env (tput t1 t2) TBool_E (qor p1 p2) true
| t_app_E: forall env f t T1 T2 pf p1 e1 e2 ef,
    has_type_E env f (TFun_E T1 T2 e2) pf ef ->
    has_type_E env t T1 p1 e1 ->
    has_type_E env (tapp f t) T2 (qor pf p1) (e1||ef||e2)
| t_abs_E: forall env t T1 T2 p2 pf e2,
    has_type_E (T1::env) t T2 p2 e2 ->
    pf = (qdiff p2 (qone (length env))) -> 
    env_cap (ttenv_E env) pf true -> 
    has_type_E env (tabs t) (TFun_E T1 T2 e2) pf false
| t_not_E: forall env t p e,
    has_type_E env t TBool_E p e ->
    has_type_E env (tnot t) TBool_E p e 
| t_bin_E: forall env t1 t2 p1 p2 e1 e2,
    has_type_E env t1 TBool_E p1 e1 ->
    has_type_E env t2 TBool_E p2 e2 ->
    has_type_E env (tbin t1 t2) TBool_E (qor p1 p2) (e1||e2)
| t_sub_eff_E: forall env t T p e,
    has_type_E env t T p e ->
    has_type_E env t T p true
.

Lemma hast_E_fv: forall G t T p e,
    has_type_E G t T p e -> p = fv (length G) t.
Proof.
  intros. induction H; simpl; eauto.
  - rewrite IHhas_type_E1, IHhas_type_E2. eauto.
  - rewrite IHhas_type_E1, IHhas_type_E2. eauto.
  - rewrite H0, IHhas_type_E. simpl. eauto.
  - rewrite IHhas_type_E1, IHhas_type_E2. eauto. 
Qed.

Lemma translate_E: forall G t T p e,
    has_type_E G t T p e ->
    has_type (ttenv_E G) t (tty_E T) p true true e.
Proof.
  intros. induction H.
  - eapply t_sub_fresh. eapply t_sub_cap. eapply t_true.
  - eapply t_sub_fresh. eapply t_sub_cap. eapply t_false.
  - assert (indexr x (ttenv_E env) = Some (tty_E T, true, true)). {
      unfold ttenv_E. erewrite indexr_map. 2: eauto. eauto. }
    eapply t_var in H0 as H2. replace true with (true||true) at 2. 2: auto.
    eapply t_sub_fresh; eauto.   
  - eapply t_ref in IHhas_type_E.
    eapply t_sub_eff. eapply t_sub_cap. eapply IHhas_type_E.
  - eapply t_get in IHhas_type_E. replace (e||true) with true in IHhas_type_E. 2: { destruct e; intuition. }
    eapply t_sub_fresh. eapply t_sub_cap. eauto.
  - eapply t_put in IHhas_type_E1. 2: eauto. 
    replace (e1||e2||true) with true in IHhas_type_E1. 2: { destruct e1,e2; intuition. }
    eapply t_sub_fresh. eapply t_sub_cap. eauto.   
  - simpl in *.
    eapply t_app in IHhas_type_E2 as HA.
    2: { eapply IHhas_type_E1. }
    replace ((true || true) && true || true) with true in HA. 2: { auto. }
    replace ((true || true) && true) with true in HA. 2: auto.
    replace (e1||ef||(true||true)&&e2) with (e1||ef||e2) in HA. 2: auto.
    auto.
  - simpl in *. eapply t_abs in IHhas_type_E as HA.
    2: eauto. 
    replace ((qor (qdiff p2 (qone (length (ttenv_E env))))(qdiff p2 (qone (length (ttenv_E env))))))
      with  pf in HA. 
    2: { unfold ttenv_E. rewrite map_length. rewrite qor_idempetic. auto.  }
    eapply t_sub_fresh. eauto. 
    rewrite qor_idempetic. unfold ttenv_E. rewrite map_length. subst pf. eapply H1.
  - eapply t_sub_fresh. eapply t_sub_cap. eapply t_not in IHhas_type_E; eauto.
  - eapply t_bin in IHhas_type_E2. 2: eapply IHhas_type_E1.
    eapply t_sub_fresh. eapply t_sub_cap. eauto.
  - eapply t_sub_eff. eauto.
Qed.

Theorem fundamental_E: forall G t T p e,
    has_type_E G t T p e ->
    sem_type (ttenv_E G)  t t (tty_E T) (plift p) true true e.
Proof.
  intros.
  eapply translate_E in H as H1.
  eapply fundamental in H1 as H2. 
  auto.
Qed.


(* ---------- encoding 2: pure ability system  ---------- *)

Inductive ty_A : Type :=
  | TBool_A  : ty_A
  | TRef_A   : ty_A
  | TFun_A   : ty_A -> bool -> ty_A -> bool -> ty_A (* T1^a1 -> T2^a2 *)
.

Definition tenv_A := list (ty_A * bool).

Fixpoint tty_A T :=
  match T with
  | TBool_A => TBool
  | TRef_A => TRef
  | TFun_A T1 a1 T2 a2 => TFun (tty_A T1) a1 a1 (tty_A T2) a2 a2 true
  end.

Definition ttenv_A (G: tenv_A): tenv := map (fun p => (tty_A (fst p), snd p, snd p)) G. 


Inductive has_type_A : tenv_A -> tm -> ty_A -> ql -> bool -> Prop :=
| t_true_A: forall env,
    has_type_A env ttrue TBool_A qempty false
| t_false_A: forall env,
    has_type_A env tfalse TBool_A qempty false
| t_var_A: forall x env T a,
    indexr x env = Some (T, a) ->
    has_type_A env (tvar x) T (qone x) a
| t_ref_A: forall t env p a,
    has_type_A env t TBool_A p a ->
    has_type_A env (tref t) TRef_A p true
| t_get_A: forall t env p a,
    has_type_A env t TRef_A p a ->
    has_type_A env (tget t) TBool_A p false
| t_put_A: forall t1 t2 env p1 p2 a1 a2,
    has_type_A env t1 TRef_A p1 a1 ->
    has_type_A env t2 TBool_A p2 a2 ->
    has_type_A env (tput t1 t2) TBool_A (qor p1 p2) false
| t_app_A: forall env f t T1 T2 pf p1 a1 a2 af,
    has_type_A env f (TFun_A T1 a1 T2 a2) pf af ->
    has_type_A env t T1 p1 a1 ->
    has_type_A env (tapp f t) T2 (qor pf p1) a2
| t_abs_A: forall env t T1 T2 p2 pf a1 a2 af,
    has_type_A ((T1, a1)::env) t T2 p2 a2 ->
    pf = (qdiff p2 (qone (length env))) ->
    env_cap (ttenv_A env) pf af ->
    has_type_A env (tabs t) (TFun_A T1 a1 T2 a2) pf af
| t_not_A: forall env t p a,
    has_type_A env t TBool_A p a ->
    has_type_A env (tnot t) TBool_A p a
| t_bin_A: forall env t1 t2 p1 p2 a1 a2,
    has_type_A env t1 TBool_A p1 a1 ->
    has_type_A env t2 TBool_A p2 a2 ->
    has_type_A env (tbin t1 t2) TBool_A (qor p1 p2) false
| t_sub_eff_A: forall env t T p a,
    has_type_A env t T p a ->
    has_type_A env t T p true
.

Lemma hast_A_fv: forall G t T p a,
    has_type_A G t T p a -> p = fv (length G) t.
Proof.
  intros. induction H; simpl; eauto.
  - rewrite IHhas_type_A1, IHhas_type_A2. eauto.
  - rewrite IHhas_type_A1, IHhas_type_A2. eauto.
  - rewrite H0, IHhas_type_A. simpl. eauto.
  - rewrite IHhas_type_A1, IHhas_type_A2. eauto.
Qed.

Lemma translate_A: forall G t T p a,
    has_type_A G t T p a ->
    has_type (ttenv_A G) t (tty_A T) p a a true.
Proof.
  intros. induction H.
  - eauto. 
  - eauto.
  - assert (indexr x (ttenv_A env) = Some (tty_A T, a, a)). {
      unfold ttenv_A. erewrite indexr_map. 2: eauto. eauto. }
    eapply t_var in H0 as H2.
    destruct a; eauto.
  - eauto. 
  - eauto. 
  - eauto.
  - simpl in *.
    eapply t_app in IHhas_type_A2 as HA.
    2: { replace (a1 || a1) with a1. 2: destruct a1; eauto. eauto. }
    destruct a1,af,a2; eauto. 
  - simpl in *. eapply t_abs in IHhas_type_A as HA.
    3: eauto. 2: { unfold ttenv_A. rewrite map_length. eauto. }
    destruct af; eauto.
  - eapply t_not in IHhas_type_A. 
    destruct a; auto. eapply t_sub_cap; eauto.
  - eauto.
  - eauto. 
Qed.

Theorem fundamental_A: forall G t T p a,
    has_type_A G t T p a ->
    forall e,
      env_cap (ttenv_A G) p e ->
      sem_type (ttenv_A G) t t (tty_A T) (plift p) a (a&&e) e.
Proof.
  intros.
  eapply translate_A in H as H1.
  eapply fundamental' in H1 as H2. eauto. eauto. 
Qed.


(* ---------- LR contextual equivalence  ---------- *)

(* Define typed contexts and prove that the binary logical
   relation implies contextual equivalence (congruency wrt
   putting expressions in context *)

Inductive ctx_type : (tm -> tm) -> tenv -> ty -> pl ->  bool -> bool -> bool -> tenv -> ty -> pl -> bool -> bool -> bool -> Prop :=
| c_top: forall G T p fr a e,
    ctx_type (fun x => x) G T p fr a e G T p fr a e
| c_ref: forall G t p fr a e,
   has_type G t TBool p fr a e ->
   ctx_type (fun x => tref x) G TBool (plift p) fr a e G TRef (plift p) true false e 
| c_get: forall G t p fr a e,
   has_type G t TRef p fr a e -> 
   ctx_type (fun x => tget x) G TRef (plift p) fr a e G TBool (plift p) false false (e||a)
| c_put1: forall G t1 p1 fr1 a1 e1 p2 fr2 a2 e2,
   has_type G t1 TRef p1 fr1 a1 e1 ->
   ctx_type (fun x => tput t1 x) G TBool (plift p2) fr2 a2 e2 G TBool (por (plift p1) (plift p2)) false false (e1||e2||a1)
| c_put2: forall G t2 p2 fr2 a2 e2 p1 fr1 a1 e1,
   has_type G t2 TBool p2 fr2 a2 e2 ->
   ctx_type (fun x => tput x t2) G TRef (plift p1) fr1 a1 e1 G TBool (por (plift p1)(plift p2)) false false (e1||e2||a1)
| c_app1: forall t G T1 p2 fr1 a1 e1 T2 fr2 a2 e2 p1 frf af ef,
    has_type G t T1 p2 fr1 a1 e1 ->
    ctx_type (fun x => tapp x t) G (TFun T1 fr1 a1 T2 fr2 a2 e2) (plift p1) frf af ef G T2 (por (plift p1)(plift p2)) ((frf||fr1)&&a2 || fr2) ((af||a1)&&a2) (e1 || ef || (af||a1)&&e2)
| c_app2: forall t1 G T1 p2 a1 e1 fr1 T2 fr2 a2 e2 p1 frf af ef,
    has_type G t1 (TFun T1 fr1 a1 T2 fr2 a2 e2) p1 frf af ef ->
    ctx_type (fun x => tapp t1 x) G T1 (plift p2) fr1 a1 e1 G T2 (por (plift p1)(plift p2)) ((frf||fr1)&&a2 || fr2) ((af||a1)&&a2) (e1 || ef || (af||a1)&&e2)
| c_abs: forall G T1 T2 p2 pf fr2 af fr1 a1 a2 e2,
    pf = (qdiff p2 (qone (length G))) ->
    env_cap G pf af ->
    ctx_type (fun x => tabs x) ((T1, fr1, a1)::G) T2 (plift p2) fr2 a2 e2 G (TFun T1 fr1 a1 T2 fr2 a2 e2) (plift pf) false ((e2||a2)&&af) false
| c_not: forall G t p fr a e,
  has_type G t TBool p fr a e -> 
  ctx_type (fun x => tnot x) G TBool (plift p) fr a e G TBool (plift p) false false e
| c_bin1: forall G t1 p1 fr1 a1 e1 p2 fr2 a2 e2,
    has_type G t1 TBool p1 fr1 a1 e1 ->
    ctx_type (fun x => tbin t1 x) G TBool (plift p2) fr2 a2 e2 G TBool (por (plift p1) (plift p2)) false false (e1||e2)
| c_bin2: forall G t2 p1 fr1 a1 e1 p2 fr2 a2 e2,
    has_type G t2 TBool p2 fr2 a2 e2 ->
    ctx_type (fun x => tbin x t2) G TBool (plift p1) fr1 a1 e1 G TBool (por (plift p1) (plift p2)) false false (e1||e2)    
| c_sub_fresh: forall G T p fr a e,
    ctx_type (fun x => x) G T p fr a e G T p true a e  
| c_sub_cap: forall G T p fr a e,
    ctx_type (fun x => x) G T p fr a e G T p fr true e  
| c_sub_eff: forall G T p fr a e,
    ctx_type (fun x => x) G T p fr a e G T p fr a true 
| cx_trans: forall f g G1 p1 T1 fr1 a1 e1 G2 p2 T2 fr2 a2 e2 G3 p3 T3 fr3 a3 e3,
    ctx_type f G1 T1 p1 fr1 a1 e1 G2 T2 p2 fr2 a2 e2 ->
    ctx_type g G2 T2 p2 fr2 a2 e2 G3 T3 p3 fr3 a3 e3 ->
    ctx_type (fun x => g (f x)) G1 T1 p1 fr1 a1 e1 G3 T3 p3 fr3 a3 e3
.


(* semantic equivalence between contexts *)
Definition sem_ctx_type C C' G1 T1 p1 fr1 a1 e1 G2 T2 p2 fr2 a2 e2 :=
  forall t t',
    p1 = plift (fv (length G1) t) ->
    p1 = plift (fv (length G1) t') ->
    sem_type G1 t t' T1 p1 fr1 a1 e1 ->
    p2 = plift (fv (length G2) (C t)) /\
    p2 = plift (fv (length G2) (C' t')) /\
    sem_type G2 (C t) (C' t') T2 p2 fr2 a2 e2.

(* congruence *)
Theorem congr:
  forall C G1 T1 p1 fr1 a1 e1 G2 T2 p2 fr2 a2 e2,
    ctx_type C G1 T1 p1 fr1 a1 e1 G2 T2 p2 fr2 a2 e2 ->
    sem_ctx_type C C G1 T1 p1 fr1 a1 e1 G2 T2 p2 fr2 a2 e2.
Proof. 
  intros ? ? ? ? ? ? ? ? ? ? ? ? ? CX.
  induction CX; intros ? ? PX1 PX2 ?.
  - split. 2: split.
    eauto. eauto. 
    eauto.
  - split. 2: split.
    eauto. eauto.
    intros u E ? ? ? ? ? WFE. 
    intros STWF S1 S2 p1 p2 ST LS1 LS2.
    eapply exp_ref; eauto. eapply H0; eauto.
  - split. 2: split.
    eauto. eauto.
    intros u E ? ? ? ? ? WFE. 
    intros STWF S1 S2 p1 p2 ST LS1 LS2.
    eapply exp_get; eauto. eapply H0; eauto.
    unfold bsub in *. intros ?. eapply E. destruct e; intuition. 
    rewrite exp_locs_get in LS1. intros ? ?. eapply LS1. destruct e; destruct a; intuition.
    rewrite exp_locs_get in LS2. intros ? ?. eapply LS2. destruct e; destruct a; intuition.
  - split. 2: split.
    simpl. eapply hast_fv in H. rewrite plift_or. congruence.
    simpl. eapply hast_fv in H. rewrite plift_or. congruence. 
    intros u E ? ? ? ? ? WFE. intros STWF S1 S2 q1 q2 ST LS1 LS2.
    
    eapply fundamental in H.  assert (env_type M H1 H2 V1 V2 G u (plift p1)) as WFE'. { eapply envt_tighten;eauto. unfoldq; intuition. }
    eapply H in WFE' as A.
    2: { unfold bsub in *. intros Q. eapply E. destruct e1; intuition. }
    edestruct A as (S1' & S2' & M' & v1 & v2 & ?). auto. eapply ST.
    intros ? ?. rewrite exp_locs_put in LS1. eapply LS1. destruct e1; try contradiction. simpl in *. left. auto. 
    intros ? ?. rewrite exp_locs_put in LS2. eapply LS2. destruct e1; try contradiction. simpl in *. left. auto.
    eapply exp_put; eauto. 
    exists v1, v2.  eapply H3. destruct H3 as (? & ? & ? & ? & ?). intuition.
    eapply H0.
    unfold bsub in *. intros Q. eapply E. destruct e1, e2, a1;intuition. 
    eapply envt_store_change. eapply envt_tighten. eapply WFE. unfoldq; intuition.
    intros ? ? ? ? ?. eapply s. auto. destruct ST. destruct H8. lia. destruct ST. destruct H8. lia. auto.
    auto.
    intros ? ?. left. eapply LS1. rewrite exp_locs_put. destruct e2; try contradiction; destruct e1, a1; simpl; right; auto.
    intros ? ?. left. eapply LS2. rewrite exp_locs_put. destruct e2; try contradiction; destruct e1, a1; simpl; right; auto.
    
  - split. 2: split.
    simpl. eapply hast_fv in H. rewrite plift_or. congruence.
    simpl. eapply hast_fv in H. rewrite plift_or. congruence. 
    intros u E ? ? ? ? ? WFE. intros STWF S1 S2 q1 q2 ST LS1 LS2.
    assert (env_type M H1 H2 V1 V2 G u (plift p1)) as WFE'. { eapply envt_tighten;eauto. unfoldq; intuition. }
    
    eapply H0 in WFE' as A. 
    2: { unfold bsub in *. intros. subst e1; intuition.  }
    edestruct A as (S1' & S2' & M' & v1 & v2 & ?). auto. eapply ST. 
    intros ? ?. rewrite exp_locs_put in LS1. eapply LS1. destruct e1; try contradiction. simpl in *. left. auto. 
    intros ? ?. rewrite exp_locs_put in LS2. eapply LS2. destruct e1; try contradiction. simpl in *. left. auto.
    eapply exp_put; eauto. exists v1, v2. eapply H3.
    destruct H3 as (? & ? & ? & ? & ?). intuition.
    eapply fundamental in H. eapply H. 
    unfold bsub in *. intros Q. eapply E. destruct e1, e2, a1; intuition.
    eapply envt_store_change. eapply envt_tighten. eapply WFE. unfoldq; intuition.
    intros ? ? ? ? ?. eapply s. auto. destruct ST, H8. lia. destruct ST, H8. lia. auto. auto.
    intros ? ?. left. eapply LS1. rewrite exp_locs_put. destruct e2; try contradiction; destruct e1, a1; simpl; right; auto.
    intros ? ?. left. eapply LS2. rewrite exp_locs_put. destruct e2; try contradiction; destruct e1, a1; simpl; right; auto.
  - split. 2: split.
    simpl. eapply hast_fv in H. rewrite plift_or. congruence.
    simpl. eapply hast_fv in H. rewrite plift_or. congruence. 

    intros u E ? ? ? ? ? WFE. intros STWF S1 S2 q1 q2 ST LS1 LS2.
    assert (env_type M H1 H2 V1 V2 G u (plift p1)) as WFE'. { eapply envt_tighten;eauto. unfoldq; intuition. }
    
    edestruct H0 with (u := u) as (S1' & S2' & M' & ?).
    unfold bsub in *. intros. eapply E. destruct e1, ef; intuition.
    eauto. auto. eauto. 
    intros ? ?. rewrite exp_locs_app in LS1. eapply LS1. destruct ef; try contradiction. destruct e1; simpl; left; auto.
    intros ? ?. rewrite exp_locs_app in LS2. eapply LS2. destruct ef; try contradiction. destruct e1; simpl; left; auto.
    eapply exp_app; eauto.  
    destruct H3 as (v1 & v2 & ? & ? & ? & ? & ?). intuition.
    eapply fundamental in H. eapply H.
    unfold bsub in *. intros ?. eapply E. destruct e1; intuition.
    eapply envt_store_change. eapply envt_tighten. eapply WFE.  unfoldq; intuition.
    intros ? ? ? ? ?. eapply H3. auto. destruct ST. destruct H9. lia. destruct ST. destruct H9. lia. auto. auto.
    intros ? ?. left. eapply LS1. rewrite exp_locs_app. destruct e1; try contradiction. simpl. right. auto.
    intros ? ?. left. eapply LS2. rewrite exp_locs_app. destruct e1; try contradiction. simpl. right. auto.
    unfold bsub in *. destruct e2, u, af, a1, a2; simpl in *; intuition.
    unfold bsub in *. destruct e2, u, af, a1, a2; simpl in *; intuition.
    unfold bsub in *. destruct e2, u, af, a1, a2; simpl in *; intuition.
    unfold bsub in *. destruct e2, u, af, a1, a2; simpl in *; intuition. 
  - split. 2: split.
    simpl. eapply hast_fv in H. rewrite plift_or. congruence.
    simpl. eapply hast_fv in H. rewrite plift_or. congruence. 

    intros u E ? ? ? ? ? WFE. intros STWF S1 S2 q1 q2 ST LS1 LS2.
    assert (env_type M H1 H2 V1 V2 G u (plift p2)) as WFE'. { eapply envt_tighten;eauto. unfoldq; intuition. }
    
    eapply fundamental in H. edestruct H with (u := u) as (S1' & S2' & M' & ?).  
    unfold bsub in *. intros. eapply E. destruct e1, ef; intuition.
    eapply envt_tighten. eapply WFE. unfoldq; intuition. auto. eauto.
    intros ? ?. rewrite exp_locs_app in LS1. eapply LS1. destruct ef; try contradiction. destruct e1; simpl; left; auto.
    intros ? ?. rewrite exp_locs_app in LS2. eapply LS2. destruct ef; try contradiction. destruct e1; simpl; left; auto.
    eapply exp_app. all: auto. eauto. 
    destruct H3 as (v1 & v2 & ? & ? & ? & ? & ?). intuition.
    eapply H0.
    unfold bsub in *. intros ?. eapply E. destruct e1; intuition.
    eapply envt_store_change. eapply envt_tighten; eauto. unfoldq; intuition.
    intros ? ? ? ? ?. eapply H3. auto. destruct ST, H9. lia. destruct ST, H9. lia. all: auto.
    intros ? ?. left. eapply LS1. rewrite exp_locs_app. destruct e1; try contradiction. simpl. right. auto.
    intros ? ?. left. eapply LS2. rewrite exp_locs_app. destruct e1; try contradiction. simpl. right. auto.
    unfold bsub in *. destruct e2, u, af, a1, a2; simpl in *; intuition.
    unfold bsub in *. destruct e2, u, af, a1, a2; simpl in *; intuition.
    unfold bsub in *. destruct e2, u, af, a1, a2; simpl in *; intuition.
    unfold bsub in *. destruct e2, u, af, a1, a2; simpl in *; intuition.  
  - split. 2: split.
    simpl. subst pf. rewrite plift_diff, plift_diff. simpl in *. congruence.
    simpl. subst pf. rewrite plift_diff, plift_diff. simpl in *. congruence.
   
    eapply sem_abs; eauto.
    simpl in *. rewrite plift_qual_eq. auto.
    simpl in *. rewrite plift_qual_eq. congruence.

  - split. 2: split.
    simpl. eapply hast_fv in H. congruence.
    simpl. eapply hast_fv in H. congruence.
    intros  u E  ? ? ? ? ?  WFE. intros STW S1 S2 q1 q2 ST LS1 LS2.
    eapply exp_tnot; eauto. eapply H0; eauto.
    
  - split. 2: split.
    simpl. eapply hast_fv in H. rewrite plift_or. congruence.
    simpl. eapply hast_fv in H. rewrite plift_or. congruence. 

    intros u E ? ? ? ? ?  WFE. intros STW S1 S2 q1 q2 ST LS1 LS2.
    eapply fundamental in H. 
    edestruct H with (u := u) as (S1' & S2' & M' & ?).
    unfold bsub in *. intros ?. eapply E. destruct e1; intuition. 
    eapply envt_tighten; eauto. unfoldq; intuition. auto. eauto.
    intros ? ?. eapply LS1. rewrite exp_locs_tbin. destruct e1; try contradiction. left. auto.
    intros ? ?. eapply LS2. rewrite exp_locs_tbin. destruct e1; try contradiction. left. auto.
    eapply exp_tbin; auto.
    unfold bsub in *. intros ?. eapply E. auto.
    eauto.
    destruct H3 as (v1 & v2 & ? & ? & ? & ? & ? & ? & ? & ? & ?& ? & ?). intuition. 
    eapply H0. 
    unfold bsub in *. intros. eapply E. destruct e1, e2; intuition.
    eapply envt_store_change. eapply envt_tighten. eapply WFE. unfoldq; intuition.
    intros ? ? ? ? ?. eapply s. auto. destruct ST, s1. lia. destruct ST, s1. lia. auto. auto. 
    intros ? ?. left. eapply LS1. rewrite exp_locs_tbin. destruct e2; try contradiction. destruct e1; simpl; right; auto.
    intros ? ?. left. eapply LS2. rewrite exp_locs_tbin. destruct e2; try contradiction. destruct e1; simpl; right; auto.
  - split. 2: split.
    simpl. eapply hast_fv in H. rewrite plift_or. congruence.
    simpl. eapply hast_fv in H. rewrite plift_or. congruence.

    intros u E ? ? ? ? ? WFE. intros STWF S1 S2 q1 q2 ST LS1 LS2.
    edestruct H0 as (S1' & S2' & M' & ?). 
    unfold bsub in *. intros. eapply E. destruct e1; intuition.
    eapply envt_tighten; eauto. unfoldq; intuition. auto. eauto.
    intros ? ?. eapply LS1. rewrite exp_locs_tbin. destruct e1; try contradiction. left. auto.
    intros ? ?. eapply LS2. rewrite exp_locs_tbin. destruct e1; try contradiction. left. auto.
    eapply exp_tbin; auto.
    unfold bsub in *. intros. eapply E. auto.
    eauto. 
    destruct H3 as (v1 & v2 & ? & ? & ? & ? & ? & ?). intuition.
    eapply fundamental in H. eapply H. 
    unfold bsub in *. intros. eapply E. destruct e1, e2; intuition.
    eapply envt_store_change. eapply envt_tighten. eapply WFE. unfoldq; intuition.
    intros ? ? ? ? ?. eapply s. auto. destruct ST, H7. lia. destruct ST, H7. lia. auto. auto. 
    intros ? ?. left. eapply LS1. rewrite exp_locs_tbin. destruct e2; try contradiction. destruct e1; simpl; right; auto.
    intros ? ?. left. eapply LS2. rewrite exp_locs_tbin. destruct e2; try contradiction. destruct e1; simpl; right; auto.
  - split. 2: split. eauto. eauto. 
    intros u E ? ? ? ? ? WFE. intros STWF S1 S2 q1 q2 ST LS1 LS2. eapply exp_sub_fresh; eauto. eapply H; eauto.
  - split. 2: split. eauto. eauto.
    intros u E ? ? ? ? ? WFE. intros STWF S1 S2 q1 q2 ST LS1 LS2. eapply exp_sub_cap; eauto. eapply H; eauto.
  - split. 2: split. eauto. eauto.
    intros u E ? ? ? ? ? WFE. intros STWF S1 S2 q1 q2 ST LS1 LS2. eapply exp_sub_eff; eauto. eapply H; eauto.
    unfold bsub in *. intros. eapply E. auto.
    intros ? ?. destruct e; try contradiction. eapply LS1. auto.   
    intros ? ?. destruct e; try contradiction. eapply LS2. auto.
  - edestruct IHCX1 as (PY1 & PY2 & ?). eapply PX1. eapply PX2. eauto.
    edestruct IHCX2 as (?&?&?). eapply PY1. eapply PY2. eauto. 
    split. 2: split. eauto. eauto.
    eauto.
Qed.


Lemma adequacy: forall t t' p fr a e,
  sem_type [] t t' TBool p fr a e ->
  exists S S' v,
    tevaln [] [] t S v /\
    tevaln [] [] t' S' v.
Proof.
  intros. edestruct H. unfold bsub. eauto. eapply envt_empty.
  eapply sttyw_empty. eapply storet_empty.
  rewrite exp_locs_empty. intros ? Q. destruct e. 2: contradiction. simpl in Q. eapply Q.
  rewrite exp_locs_empty. intros ? Q. destruct e. 2: contradiction. simpl in Q. eapply Q. 
  edestruct H0 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ?).
  destruct x2,x3; simpl in H8; inversion H8;  subst b0. 
  eexists. eexists. eexists. split; eauto.
Qed.

(* contextual equivalence: no boolean context can detect a difference *)
Definition contextual_equiv G t1 t2 T1 p1 fr1 a1 e1 :=
  forall C,
    ctx_type C G T1 p1 fr1 a1 e1 [] TBool pempty false true true ->
    exists S1 S2 v,
      tevaln [] [] (C t1) S1 v /\
      tevaln [] [] (C t2) S2 v.

(* soundness of binary logical relation: implies contextual equivalence *)
Theorem soundess: forall G t1 t2 T p fr a e,
  p = plift (fv (length G) t1) ->
  p = plift (fv (length G) t2) ->
  sem_type G t1 t2 T p fr a e ->
  contextual_equiv G t1 t2 T p fr a e.
Proof.
  intros. intros ? ?.
  eapply adequacy.
  eapply congr; eauto.
Qed. 


(* ---------- LR effect interpretation  ---------- *)

(* store invariance:
   - every pure expression can be evaluated in empty stores
     (in fact arbitrary S1, S2), to equivalent values.
   - the store has to be large enough, so that new
     allocations don't conflict
   - impure expressions tolerate changes to locations
     they can't observe
 *)


Theorem store_invariance2': forall t G T p fr a e
 (HT: has_type G t T p fr a e),
 forall uv, bsub e uv ->
 forall M H1 H2 V1 V2 S1 S2 p1 p2,
 env_type M H1 H2 V1 V2 G uv (plift p) ->
 stty_wellformed M ->
 store_type S1 S2 M p1 p2 ->
 (psub (pif e (exp_locs V1 t)) p1) ->
 (psub (pif e (exp_locs V2 t)) p2) ->
 forall S1',
   store_write S1 S1' (pnot p1) ->  
   length S1 <= length S1' ->
   exists S1'' S2' M' v1 v2 u ls1 ls2,
     exp_type2 v1 v2 uv ls1 ls2 S1' S2
       (st_pad (length S1'-length S1) 0 M)
       H1 H2 V1 V2 t t S1'' S2' M' T u p1 p2 fr a e.
Proof.
  intros ????????? E. 
  intros ????????? WFE SW ST P1 P2.
  intros S1' ES1' L1'.
  eapply fundamental; eauto.
  eapply envt_store_change. eauto.
  intros ?????. simpl. eauto.
  unfold st_pad, st_len1. simpl. lia.
  unfold st_pad, st_len2. simpl. lia.
  eapply sttyw_pad. eauto.
  eapply storet_tighten. unfold st_pad. simpl.
  destruct ST as (L1 & L2 & ST).
  rewrite <-L1, <-L2.
  replace (length S1' - length S1 + length S1) with (length S1'). 2: lia. 
  eapply storet_pad'; eauto.
  split; eauto.
  eapply storew_refl.
  unfoldq. intuition.
  unfoldq. intuition.
Qed. 


Theorem store_invariance3' : forall t G T p fr a e
  (W0: has_type G t T p fr a e),
  forall uv, bsub e uv ->
  forall M H1 H2 V1 V2 S1 S2 p1 p2,
    env_type M H1 H2 V1 V2 G uv (plift p) ->
    stty_wellformed M ->
    store_type S1 S2 M p1 p2 ->
    (psub (pif e (exp_locs V1 t)) p1) ->
    (psub (pif e (exp_locs V2 t)) p2) ->
    forall S2',
      store_write S2 S2' (pnot p2) ->  
      length S2 <= length S2' ->
      exists S1' S2'' M' v1 v2 u ls1 ls2,
        exp_type2 v1 v2 uv ls1 ls2 S1 S2'
          (st_pad 0 (length S2'-length S2) M)
          H1 H2 V1 V2 t t S1' S2'' M' T u p1 p2 fr a e.
Proof.
  intros ????????? E.
  intros ????????? WFE SW ST P1 P2.
  intros S2' ES2' L2'.
  eapply fundamental; eauto.
  eapply envt_store_change. eauto.
  intros ?????. simpl. eauto.
  unfold st_pad, st_len1. simpl. eauto.
  unfold st_pad, st_len2. simpl. lia.
  eapply sttyw_pad. eauto.
  eapply storet_tighten. unfold st_pad. simpl.
  destruct ST as (L1 & L2 & ST).
  rewrite <-L1, <-L2.
  replace (length S2' - length S2 + length S2) with (length S2'). 2: lia. 
  eapply storet_pad'; eauto.
  split; eauto.
  eapply storew_refl.
  unfoldq. intuition.
  unfoldq. intuition.
Qed.

Lemma pif_false: forall p,
  pif false p = pempty.
Proof.
  intros. eapply functional_extensionality. intros. simpl. auto.
Qed.

Lemma exp_locs_decide: forall V t l,
    exp_locs V t l \/ ~ exp_locs V t l.
Proof.
  intros. rewrite <-plift_exp_locs.  unfold exp_locs, plift.
  destruct (exp_locs_fix V t l); eauto.
Qed.

Theorem reorder_tbin_mention: forall G t1 t2 p1 p2 fr1 fr2 a1 a2
  (W1: has_type G t1 TBool p1 fr1 a1 false)
  (W2: has_type G t2 TBool p2 fr2 a2 false),
  sem_type G (tbin t1 t2) (tbin t2 t1) TBool (por (plift p1) (plift p2)) false false false.
Proof.
  intros. intros uv E M H1 H2 V1 V2 WFE.  
  intros STWF S1 S2 els1 els2 ST ELS1 ELS2.

  assert (length V1 = length G) as LV1. { destruct WFE as (? & ? & ? & ?). auto. }
  assert (length V2 = length G) as LV2. { destruct WFE as (? & ? & ? & ? & ?). auto. }

  (* t1 *)
  eapply fundamental in W1 as HE1.
  edestruct (HE1 false) as (S1' & S2' & M' & v1 & v1' & uv1 & lsv1 & lsv2 & STC' & STWF' & E1 & E1' & LS1 & LS2 & ST' & VT1 & UX1 & UX2 & LUX1 & LUX2 & VQ1 & VQ2 & SE1 & SE1' & STREL1).
  unfold bsub in *. intros. auto.                   
  eapply envt_tighten. destruct uv. eapply envt_strengthenW1. rewrite plift_or. eauto. 
  rewrite plift_or. auto. unfoldq; intuition.
  rewrite plift_or. unfoldq; intuition.
  auto.
  2: { intros ? ?. eapply H.  } 2: { intros ? ?. eapply H. }
  rewrite pif_false. rewrite pif_false. eapply storet_tighten. eauto.
  unfoldq; intuition. unfoldq; intuition.
  
  assert (st_len1 M <= st_len1 M') as L1. { destruct ST. destruct ST'. lia. }
  assert (st_len2 M <= st_len2 M') as L2. { destruct ST. destruct ST'. lia. }
  
  assert (env_type M' H1 H2 V1 V2 G uv (plift p2)) as  WFE'. { 
    eapply envt_store_change. eapply envt_tighten. eapply WFE. unfoldq; intuition. 
    intros ? ? ? ? ?. eapply STC'. auto. lia. lia. }

  (* t2 *)   
  eapply store_invariance2' with (uv := false) in W2 as W2'.
  2: { unfold bsub in *. auto.  }
  2: { eapply envt_tighten. rewrite <- plift_or in WFE. destruct uv. eapply envt_strengthenW1. eapply WFE. auto.  rewrite plift_or. unfoldq; intuition.  }
  2: auto.
  3: { intros ? ?. eapply H. }
  3: { intros ? ?. eapply H. }
  2: { rewrite pif_false. rewrite pif_false.
       eapply storet_tighten. eauto.  
       unfoldq; intuition.  unfoldq; intuition. }
  2: { eapply storew_widen. eapply SE1. intros ? ?. intuition.  }
  2: lia.
  destruct W2' as (S1'' & S2y'' & M'' & v2 & v2x & uv2 & lsv2' & lsv2x & STC'' & STWF2 & E2' & E2 & LS1' & LS2' & ST'' & VT'' & UX3 & UX4 & LUX3 & LUX4 & VQ3 & VQ4 & SE2' & SE2 & STREL2).
  
  (* t1 *)
  eapply store_invariance3' with (uv := false) in W1 as W1'.
  2: { unfold bsub in *. auto. }
  2: { eapply envt_tighten. rewrite <-plift_or in WFE. destruct uv. eapply envt_strengthenW1. eapply WFE. auto. rewrite plift_or. unfoldq; intuition.  }
  2: auto.
  3: { intros ? ?. eapply H. }
  3: { intros ? ?. eapply H. }
  2: { rewrite pif_false.  rewrite pif_false. eapply storet_tighten. eauto. unfoldq; intuition. unfoldq. intuition. }
  2: { eapply storew_widen. eapply SE2. intros ? ?. intuition. }
  2: lia.
  
  destruct W1' as (S1y' & S2'' & M''' & v1y & v1z & u1y & lsv1y & lsvz & STC''' &  STWF''' & E1y & E2'' & LS1y & LS2'' & ST'''  & VT''' & UX5 & UX6 & LUX5 & LUX6 & VQ5 & VQ6 & SE1y & SE2'' & STREL''').    

  assert (S1' = S1y' /\ v1 = v1y) as C. {
    destruct E1 as [n1 E1].
    destruct E1y as [n1x E1y].
    assert (1+n1+n1x > n1) as A1. lia.
    assert (1+n1+n1x > n1x) as A1x. lia. 
    specialize (E1 _ A1).
    specialize (E1y _ A1x).
    split; congruence.
  }
  destruct C. subst v1y S1y'.
  clear WFE'. 

  destruct v1; destruct v1'; destruct v1z; simpl in VT1; simpl in VT'''; intuition. subst b0 b1.
  destruct v2; destruct v2x; simpl in VT''; intuition. subst b0.
  
  assert (tevaln S1 H1 (tbin t1 t2) S1'' (vbool (b && b1))). {
    destruct E1 as [n1 E1].
    destruct E2' as [n1' E1''].
    exists (1+n1+n1'). intros.
    destruct n. lia. simpl.
    rewrite E1, E1''. eauto. lia. lia. 
  }
  assert (tevaln S2 H2 (tbin t2 t1) S2'' (vbool (b1 && b))). {
    destruct E2 as [n1 E2].
    destruct E2'' as [n1' E2''].
    exists (1+n1+n1'). intros.
    destruct n. lia. simpl.
    rewrite E2, E2''. eauto. lia. lia. 
  }

  assert (b && b1 = b1 && b). eauto with bool.
  rewrite H3 in *.

  remember ((st_len1 M''), (st_len2 M'''), 
     fun l1 l2 =>  strel M l1 l2 
     ) as MM. 

  assert (st_chain M MM). {
    subst MM. 
    intros ? ? ?. simpl.  auto.
  } 
  
  assert (length S1'' =  fst (fst M'')) as L1''. {
   destruct ST'' as (? & ? & ?). 
   unfold st_len1 in *. lia.
  }

  assert (length S2'' =  snd (fst M''')) as L2''. {
   destruct ST''' as (? & ? & ?). 
   unfold st_len2 in *. lia.
  }

  assert (store_type S1'' S2'' MM
         (por els1 (pdiff (pdom S1'') (pdom S1)))
         (por els2 (pdiff (pdom S2'') (pdom S2)))). {
    subst MM. destruct STWF as (STW & STR & STL).
    remember ST as STT. clear HeqSTT. 
    destruct ST as (STL1 & STL2 & ST).
    split. 2: split.
    + unfold st_len1, st_pad. simpl. lia. 
    + unfold st_len2, st_pad. simpl. lia.
    + unfold st_pad. simpl. intros.
      destruct H6; destruct H7.
      2: { destruct H7. eapply STW in H5. unfoldq. intuition. }
      2: { destruct H6.  eapply STW in H5. unfoldq. intuition. }
      2: { destruct H6.  eapply STW in H5. unfoldq. intuition. }
      edestruct ST as (b' & IS1  & IS2); eauto. 
      exists b'. split.
      rewrite <-SE2'. rewrite <- SE1. auto.
      split. eapply indexr_var_some' in IS1. unfoldq. lia. intros ?. intuition. 
      split. eapply indexr_var_some' in IS1. unfoldq. lia. intros ?. intuition.
      rewrite <-SE2''. rewrite <- SE2. auto. 
      split. eapply indexr_var_some' in IS2. unfoldq. lia. intros ?. intuition.
      split. eapply indexr_var_some' in IS2. unfoldq. lia. intros ?. intuition.
  }

  assert (stty_wellformed MM) as STWMM. {
    subst MM. destruct STWF as [WF1 [WF2 WF3]].
    destruct ST as (STL1 & STL2 & ST).
    destruct ST' as (STL1' & STL2' & ST'). 
    destruct ST'' as (STL1'' & STL2'' & ST''). 
    destruct ST''' as (STL1''' & STL2''' & ST'''). 
    unfold st_len1 in *. unfold st_len2 in *.
    simpl in *.
    split. 2: split.
    + unfold st_len1, st_len2. simpl. intros.
      eapply WF1 in H6. intuition. 
    + simpl. intros. eapply WF2. eauto. eauto.
    + simpl. intros. eapply WF3. eauto. eauto. 
  }
        
  exists S1'', S2''. exists MM. eexists. eexists. eexists. exists qempty. exists qempty. 
  split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 8: split. 9: split. 10: split. 11: split. 12: split.
  13: split. 14: split. 15: split. 16: split. 
  + eauto.
  + eauto.
  + eauto. 
  + eauto.
  + lia.
  + lia.
  + auto.
  + simpl. intuition.
  + simpl. intuition.
  + auto.
  + intuition.
  + intuition.
  + rewrite plift_empty. unfoldq. intuition.
  + rewrite plift_empty. unfoldq. intuition.
  + rewrite exp_locs_tbin. eapply storew_trans. eapply storew_widen. eauto.
    intros ? ?. contradiction. 
    eapply storew_widen. eauto. 
    intros ? ?. contradiction. 
    lia.
  + rewrite exp_locs_tbin. eapply storew_trans. eapply storew_widen. eauto.
    intros ? ?. contradiction. 
    eapply storew_widen. eauto. 
    intros ? ?. contradiction.  
    lia.
  + subst MM. simpl in *. intuition.
Qed.

Theorem reorder_tbin_eff: forall G t1 t2 p1 p2 a1 a2 fr1 fr2
  (W1: has_type G t1 TBool p1 fr1 a1 true)   
  (W2: has_type G t2 TBool p2 fr2 a2 false), 
  sem_type G (tbin t1 t2) (tbin t2 t1) TBool (por (plift p1) (plift p2)) false false true.
Proof.
  intros. intros uv E M H1 H2 V1 V2 WFE. intros SW ???? ST ELS1 ELS2.
  
  assert (length V1 = length G) as LV1. { destruct WFE as (? & ? & ? & ? & ?). auto. }
  assert (length V2 = length G) as LV2. { destruct WFE as (? & ? & ? & ? & ?). auto. }
  destruct uv; intuition. 
  
  (* t1 *)
  eapply fundamental in W1 as HE1.
  edestruct (HE1 true) as (S1' & S2' & M' & v1 & v1' & uv1 & lsv1 & lsv2 & STC' & STWF' & E1 & E1' & LS1 & LS2 & ST' & VT1 & UX1 & UX2 & LUX1 & LUX2 & VQ1 & VQ2 & SE1 & SE1' & STREL1).
  unfold bsub. intuition.
  eapply envt_tighten. eauto. unfoldq; intuition. eauto. eauto. eauto. 
  intros ? ?. eapply ELS1. rewrite exp_locs_tbin. left. eauto. 
  intros ? ?. eapply ELS2. rewrite exp_locs_tbin. right. eauto. 
  
  assert (st_len1 M <= st_len1 M') as L1. { destruct ST. destruct ST'. lia. }
  assert (st_len2 M <= st_len2 M') as L2. { destruct ST. destruct ST'. lia. }
  
  (* t2 *)
  eapply store_invariance2' with (uv:=false) (H1:=H1) (H2:=H2) (p1:=pempty) (p2:=pempty) in W2 as W2'.
  destruct W2' as (S1'' & S2y'' & M'' & v2 & v2x & uv2 & lsv2' & lsv2x & W2').
  4: { eapply SW. }
  4: { destruct ST as (?&?&?). split. eauto. split. eauto. intros. contradiction. }
  all: eauto.
  2: unfold bsub; eauto.
  2: { eapply envt_strengthenW1. eapply envt_tighten. eauto. unfoldq. intuition.  }
  2: unfoldq; intuition.
  2: unfoldq; intuition.
  2: { eapply storew_widen. eapply SE1. unfoldq. intuition. }

  destruct W2' as (STC'' & STWF2 & E2' & E2 & LS1' & LS2' & ST'' & VT'' & UX3 & UX4 & LUX3 & LUX4 & VQ3 & VQ4 & SE2' & SE2 & STREL2).
  
  (* t1 *)
  eapply store_invariance3' with (uv:=true) in W1 as W1'.
  destruct W1' as (S1y' & S2'' & M''' & v1y & v1z & u1y & lsv1y & lsvz & W1').
  4: eapply SW.
  4: { eauto. }
  all: eauto. 
  2: { eapply envt_store_change. eapply envt_tighten. eauto. unfoldq. intuition.
       intros ?????. eauto. eauto. eauto. }
  2: { intros ? ?. eapply ELS1. rewrite exp_locs_tbin. left. eauto. }
  2: { intros ? ?. eapply ELS2. rewrite exp_locs_tbin. right. eauto. }
  2: { eapply storew_widen. eapply SE2. intros ?; intuition. }

  destruct W1' as (STC''' &  STWF''' & E1y & E2'' & LS1y & LS2'' & ST''' & VT''' & UX5 & UX6 & LUX5 & LUX6 & VQ5 & VQ6 & SE1y & SE2'' & STREL''').

  assert (S1' = S1y' /\ v1 = v1y) as C. {
    destruct E1 as [n1 E1].
    destruct E1y as [n1x E1y].
    assert (1+n1+n1x > n1) as A1. lia.
    assert (1+n1+n1x > n1x) as A1x. lia. 
    specialize (E1 _ A1).
    specialize (E1y _ A1x).
    rewrite E1 in E1y. 
    split; congruence.
  }
  destruct C. subst v1y S1y'.

  destruct v1; destruct v1'; destruct v1z; simpl in VT1; simpl in VT'''; intuition. subst b0 b1.
  destruct v2; destruct v2x; simpl in VT''; intuition. subst b0.
  
  assert (tevaln S1 H1 (tbin t1 t2) S1'' (vbool (b && b1))). {
    destruct E1 as [n1 E1].
    destruct E2' as [n1' E1''].
    exists (1+n1+n1'). intros.
    destruct n. lia. simpl.
    rewrite E1, E1''. eauto. lia. lia. 
  }
  assert (tevaln S2 H2 (tbin t2 t1) S2'' (vbool (b1 && b))). {
    destruct E2 as [n1 E2].
    destruct E2'' as [n1' E2''].
    exists (1+n1+n1'). intros.
    destruct n. lia. simpl.
    rewrite E2, E2''. eauto. lia. lia. 
  }

  eexists S1'', S2'', (length S1'', length S2'', strel M), _, _, _, _, _.
  split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 8: split. 9: split. 10: split.
  11: split. 12: split. 13: split. 14: split. 15: split. 16: split. 17: split. 
  - intros ???. eauto. 
  - destruct SW as (SW1 & SW2 & SW3).
    destruct ST as (?&?&?).
    destruct ST' as (?&?&?).
    destruct ST'' as (?&?&?).
    unfold stty_wellformed. 
    unfold st_len1, st_len2. simpl. split. 2: split.
    intros ? ? C. eapply SW1 in C. destruct C. split; lia.
    eauto. eauto. 
  - eauto.
  - eauto.
  - lia.
  - lia.
  - destruct SW as (SW1 & SW2 & SW3).
    destruct ST as (?&?&ST).
    destruct ST' as (?&?&ST').
    destruct ST'' as (?&?&ST'').
    destruct ST''' as (?&?&ST''').
    unfold store_type.
    unfold st_len1, st_len2. simpl. split. 2: split. 
    eauto. eauto. simpl in H, H0, H3.
    intros ?? SR P0 P3.
    destruct P0 as [P0|P0]. 2: { eapply SW1 in SR. unfoldq. intuition. }
    destruct P3 as [P3|P3]. 2: { eapply SW1 in SR. unfoldq. intuition. }
    assert (strel M' l1 l2) as SR'. eauto.
    assert (strel M'' l1 l2) as SR''. eauto. 
    assert (strel M''' l1 l2) as SR'''. eauto. 
    edestruct ST as (?&?&?); eauto. 
    edestruct ST' as (?&?&?); eauto. left. eauto. left. eauto.
    edestruct ST''' as (?&?&?); eauto. left. eauto. left. eauto.
    rewrite H13 in H15. inversion H15. subst x0.
    erewrite SE2' in H13. 
    2: { unfoldq. intuition. eapply indexr_var_some'. eauto. }
    exists x1. intuition.
  - simpl. destruct b,b1; eauto.
  - eauto.
  - eauto.
  - intros ???. rewrite <-plift_empty. eauto.
  - intros ???. rewrite <-plift_empty. eauto.
  - rewrite plift_empty. unfoldq. intuition.
  - rewrite plift_empty. unfoldq. intuition. 
  - rewrite exp_locs_tbin. eapply storew_trans.
    eapply storew_widen. eauto. intros ??. left. eauto. 
    eapply storew_widen. eauto. unfoldq. intuition. eauto.
  - rewrite exp_locs_tbin. eapply storew_trans.
    eapply storew_widen. eauto. unfoldq. intuition. 
    eapply storew_widen. eauto. intros ??. right. eauto. eauto.
Qed.


Lemma pure_typing_ex1 : forall G p,
  sem_type G (tget (tref ttrue)) (tget (tref ttrue)) TBool p false false false.
Proof.
  intros. intros ? ? ? ? ? ? ? WFE. intros SW ?? ?? ST P1 P2.
  remember [vbool true] as SD.
  eexists (SD++S1), (SD++S2), (st_pad (length SD) (length SD) M).
  exists (vbool true), (vbool true). exists true.
  exists qempty, qempty.
  unfold exp_type2. intuition.
  - eapply stchain_pad.
  - eapply sttyw_pad. eauto.
  - exists 3. intros. destruct n. lia. destruct n. lia. destruct n. lia. simpl.
    bdestruct (length S1 =? length S1). subst SD. eauto. lia. 
  - exists 3. intros. destruct n. lia. destruct n. lia. destruct n. lia. simpl.
    bdestruct (length S2 =? length S2). subst SD. eauto. lia.
  - destruct ST as (L1 & L2 & L3). 
    split. 2: split.
    rewrite app_length, L1. unfold st_len1 at 2. simpl. eauto.
    rewrite app_length, L2. unfold st_len2 at 2. simpl. eauto.
    intros. simpl in H. destruct SW as (SW & ?). 
    destruct H3, H4.
    + edestruct (L3) as (? & ? & ?); eauto. eexists. split.
      rewrite indexr_skips. eauto. eapply indexr_var_some'. eauto.
      rewrite indexr_skips. eauto. eapply indexr_var_some'. eauto.
    + eapply SW in H0. unfoldq. intuition.
    + eapply SW in H0. unfoldq. intuition.
    + eapply SW in H0. unfoldq. intuition.
  - rewrite plift_empty. unfoldq. intuition.
  - rewrite plift_empty. unfoldq. intuition. 
  - intros ? Q. rewrite indexr_skips. eauto. unfoldq. intuition.
  - intros ? Q. rewrite indexr_skips. eauto. unfoldq. intuition. 
Qed.

Lemma pure_typing_ex1_static : forall G, 
  has_type G (tget (tref ttrue)) TBool qempty false false false.
Proof.
  intros. 
  replace false with (false||false) at 3.
  eapply t_get.
  eapply t_ref.
  eapply t_true.
  eauto. 
Qed.


(* ---------- LR beta-equivalence  ---------- *)


Fixpoint splice_tm (t: tm)(i: nat) (n:nat) : tm := 
  match t with 
  | ttrue         => ttrue
  | tfalse        => tfalse
  | tvar x        => tvar (if x <? i then x else x + n)
  | tref t        => tref (splice_tm t i n)
  | tget t        => tget (splice_tm t i n)
  | tput t1 t2    => tput (splice_tm t1 i n) (splice_tm t2 i n)
  | tapp t1 t2    => tapp (splice_tm t1 i n) (splice_tm t2 i n)
  | tabs t        => tabs (splice_tm t i n)
  | tnot t        => tnot (splice_tm t i n)
  | tbin t1 t2    => tbin (splice_tm t1 i n) (splice_tm t2 i n)
end.

Fixpoint subst_tm (t: tm)(i: nat) (u:tm) : tm := 
  match t with 
  | ttrue         => ttrue
  | tfalse        => tfalse
  | tvar x        => if i =? x then u else if i <? x then (tvar (pred x)) else (tvar x)   
  | tref t        => tref (subst_tm t i u)
  | tget t        => tget (subst_tm t i u)
  | tput t1 t2    => tput (subst_tm t1 i u) (subst_tm t2 i u)
  | tapp t1 t2    => tapp (subst_tm t1 i u) (subst_tm t2 i u)
  | tabs t        => tabs (subst_tm t i (splice_tm u i 1)) 
  | tnot t        => tnot (subst_tm t i u)
  | tbin t1 t2    => tbin (subst_tm t1 i u)(subst_tm t2 i u)
end.

(* We don't have locally nameless here, just regular DeBruijn levels. This 
   means substitution under binders (i.e. tabs) needs to shift the term by 1 *)

Definition subst_ql (p: pl) (i: nat) :=
  fun x => (if x <? i then p x else p (x + 1)).

Example ex1 := (subst_ql (fun x => match x with
                                   | 1 => True
                                   | 2 => True
                                   | 4 => True
                                   | 7 => True
                                   | _ => False
                                   end) 2).
Definition subst_qql (p: ql)(i: nat): ql := 
  fun x => (if x <? i then p x else p (x + 1)).

Compute (ex1 1).
Compute (ex1 2).
Compute (ex1 3).
Compute (ex1 4).
Compute (ex1 5).
Compute (ex1 6).
Compute (ex1 7).

Lemma subst_ql_qql: forall p i,
  subst_ql (plift p) i = (plift (subst_qql p i)).
Proof.
  intros. unfold subst_ql, subst_qql.
  eapply functional_extensionality. intros.
  eapply propositional_extensionality. unfold plift.
  split; intros; bdestruct (x <? i); intuition.
Qed. 

Lemma subst_ql_subst: forall p (G:tenv),
    psub (plift p) (pdom G) ->
    psub (subst_ql (por (plift p) (pone (length G))) (length G))
      (plift p).
Proof.
  intros. intros ? Q. unfold subst_ql in *.
  bdestruct (x <? length G). destruct Q. eauto. inversion H1. lia.
  bdestruct (x =? length G). 
  destruct Q. eapply H in H2. unfoldq. lia. inversion H2. lia. 
  destruct Q. eapply H in H2. unfoldq. lia. inversion H2. lia. 
Qed.

Lemma subst_ql_subst': forall p (G:tenv),
    psub (plift p) (pdom G) ->
    psub (plift p) (subst_ql (por (plift p) (pone (length G))) (length G)).
Proof.
  intros. intros ? Q. specialize (H x). unfold subst_ql in *.
  bdestruct (x <? length G). left. eauto.
  eapply H in Q. unfoldq. lia. 
Qed.

Lemma subst_ql_subst'': forall p (G:tenv),
    psub (plift p) (pdom G) ->
    psub (subst_ql (plift p) (length G)) (plift p).
Proof.
  intros. intros ? Q. unfold subst_ql in *.
  bdestruct (x <? length G). eauto. 
  bdestruct (x =? length G). 
  eapply H in Q. unfoldq. lia. eapply H in Q. unfoldq. lia.
Qed.

Lemma subst_ql_diff: forall p1 p2 x,
    subst_ql (pdiff p1 p2) x = pdiff (subst_ql p1 x) (subst_ql p2 x).
Proof.
  intros. eapply functional_extensionality.
  intros. eapply propositional_extensionality.
  unfoldq. unfold subst_ql in *.
  bdestruct (x0 <? x); intuition.
Qed.

Lemma subst_ql_one_hit: forall (G' G: tenv) T0 a0,
    subst_ql (pone (length (G' ++ (T0, a0) :: G))) (length G) = (pone (length (G' ++ G))).
Proof.
  intros. eapply functional_extensionality.
  intros. eapply propositional_extensionality.
  unfoldq. unfold subst_ql. rewrite app_length, app_length. simpl. 
  bdestruct (x <? length G); intuition.
Qed.
  
Lemma subst_ql_or: forall p1 p2 L,
    subst_ql (por p1 p2) L = por (subst_ql p1 L) (subst_ql p2 L).
Proof.
  intros. eapply functional_extensionality.
  intros. eapply propositional_extensionality.  
  unfoldq. unfold subst_ql. 
  bdestruct (x <? L); intuition.
Qed.


Lemma splice_acc: forall e1 a b c,
  splice_tm (splice_tm e1 a b) a c =
  splice_tm e1 a (c+b).
Proof.
  induction e1; intros; simpl; intuition.
  + bdestruct (i <? a); intuition.  
    bdestruct (i <? a); intuition.
    bdestruct (i + b <? a); intuition.
  + erewrite IHe1. eauto.
  + erewrite IHe1. eauto.
  + erewrite IHe1_1, IHe1_2. eauto.
  + erewrite IHe1_1, IHe1_2. eauto.
  + erewrite IHe1. eauto.
  + erewrite IHe1. eauto.
  + erewrite IHe1_1, IHe1_2. eauto.
Qed.
  
Lemma splice_zero: forall e1 a,
  (splice_tm e1 a 0) = e1.
Proof.
  intros e1. induction e1; simpl; intuition.
  + bdestruct (i <? a); intuition.
  + rewrite IHe1. eauto.
  + rewrite IHe1. eauto. 
  + rewrite IHe1_1. rewrite IHe1_2. auto.
  + rewrite IHe1_1. rewrite IHe1_2. auto.
  + rewrite IHe1. auto.
  + rewrite IHe1. auto.
  + rewrite IHe1_1. rewrite IHe1_2. auto.
Qed.

Lemma indexr_splice_gt: forall{X} x (G1 G3: list X) T ,
  indexr x (G3 ++ G1) = Some T ->
  x >= length G1 ->
  forall G2, 
  indexr (x + (length G2))(G3 ++ G2 ++ G1) = Some T.
Proof. 
  intros.
  induction G3; intros; simpl in *.
  + apply indexr_var_some' in H as H'. intuition.
  + bdestruct (x =? length (G3 ++ G1)); intuition.
    - subst. inversion H. subst.
      bdestruct (length (G3 ++ G1) + length G2 =? length (G3 ++ G2 ++ G1)); intuition.
      repeat rewrite app_length in H1.
      intuition.
    - bdestruct (x + length G2 =? length (G3 ++ G2 ++ G1)); intuition.
      apply indexr_var_some' in H2. intuition.
Qed.

Lemma indexr_splice: forall{X} (H2' H2 HX: list X) x,
  indexr (if x <? length H2 then x else x + length HX) (H2' ++ HX ++ H2) =
  indexr x (H2' ++ H2).
Proof.
  intros.
  bdestruct (x <? length H2); intuition.
  repeat rewrite indexr_skips; auto. rewrite app_length. lia.
  bdestruct (x <? length (H2' ++ H2)).
  apply indexr_var_some in H0 as H0'.
  destruct H0' as [T H0']; intuition.
  rewrite H0'. apply indexr_splice_gt; auto.
  apply indexr_var_none in H0 as H0'. rewrite H0'.
  assert (x + length HX >= (length (H2' ++ HX ++ H2))). {
    repeat rewrite app_length in *. lia.
  }
  rewrite indexr_var_none. auto.
Qed.

Lemma indexr_splice1: forall{X} (H2' H2: list X) x y,
  indexr (if x <? length H2 then x else (S x)) (H2' ++ y :: H2) =
  indexr x (H2' ++ H2).
Proof.
  intros.
  specialize (indexr_splice H2' H2 [y] x); intuition.
  simpl in *. replace (x +1) with (S x) in H. auto. lia.
Qed.


Lemma indexr_shift : forall{X} (H H': list X) x vx v,
  x > length H  ->
  indexr x (H' ++ vx :: H) = Some v <->
  indexr (pred x) (H' ++ H) = Some v.
Proof. 
  intros. split; intros.
  + destruct x; intuition.  simpl.
  rewrite <- indexr_insert_ge  in  H1; auto. lia.
  + destruct x; intuition. simpl in *.
    assert (x >= length H). lia.
    specialize (indexr_splice_gt x H H' v); intuition.
    specialize (H3  [vx]); intuition. simpl in H3.
    replace (x + 1) with (S x) in H3. auto. lia.
Qed. 

Lemma vars_locs_shift: forall t (H2' H2 HX: lenv) L,
  forall x : nat,
    vars_locs (H2' ++ HX ++ H2)
      (pdiff (plift (fv (L + length (H2' ++ HX ++ H2)) (splice_tm t (length H2) (length HX))))
         (pdiff (pnat (L + length (H2' ++ HX ++ H2))) (pnat (length (H2' ++ HX ++ H2))))) x
  <->
    vars_locs (H2' ++ H2)
      (pdiff (plift (fv (L + length (H2' ++ H2)) t))
         (pdiff (pnat (L + length (H2' ++ H2))) (pnat (length (H2' ++ H2))))) x.
Proof.
  induction t; simpl; intros.
  - rewrite plift_empty, pdiff_empty, pdiff_empty, vl_empty, vl_empty. intuition.
  - rewrite plift_empty, pdiff_empty, pdiff_empty, vl_empty, vl_empty. intuition.
  - rewrite plift_one, plift_one. intuition.
    + destruct H as (? & ? & ? & ? & ?).
      destruct H. inversion H. subst x0. rewrite indexr_splice in H0.
      eexists. split. 2: { exists x1. split; eauto. } unfoldq. intuition.
      repeat rewrite app_length in *. bdestruct (i <? length H2). lia. lia. 
    + destruct H as (? & ? & ? & ? & ?).
      destruct H. inversion H. subst x0. 
      eexists. split. 2: { exists x1. split; eauto. rewrite indexr_splice. eauto. }
      unfoldq. intuition. repeat rewrite app_length in *. bdestruct (i <? length H2). lia. lia.
  - eauto.
  - eauto.
  - repeat rewrite plift_or in *.
    repeat rewrite pdiff_or in *. 
    repeat rewrite vl_dist_or. intuition.
    + destruct H. eapply IHt1 in H. left. eauto.
      eapply IHt2 in H. right. eauto. 
    + destruct H. eapply IHt1 in H. left. eauto.
      eapply IHt2 in H. right. eauto. 
  - repeat rewrite plift_or in *.
    repeat rewrite pdiff_or in *. 
    repeat rewrite vl_dist_or. intuition.
    + destruct H. eapply IHt1 in H. left. eauto.
      eapply IHt2 in H. right. eauto. 
    + destruct H. eapply IHt1 in H. left. eauto.
      eapply IHt2 in H. right. eauto.
  - repeat rewrite plift_diff, plift_one.
    assert (forall A B, S (A + B) = (S A) + B) as R. lia. repeat rewrite R in *. intuition.
    + eapply vl_mono. 2: eapply IHt. intros ? Q. destruct Q. split. split. eauto.
      unfoldq. intuition. unfoldq. intuition.
      eapply vl_mono. 2: eapply H. intros ? Q. unfoldq. intuition. 
    + eapply vl_mono. 2: eapply IHt. intros ? Q. destruct Q. split. split. eauto.
      unfoldq. intuition. unfoldq. intuition.
      eapply vl_mono. 2: eapply H. intros ? Q. unfoldq. intuition. 
  - eapply IHt.
  - repeat rewrite plift_or in *.
    repeat rewrite pdiff_or in *. 
    repeat rewrite vl_dist_or. intuition.
    + destruct H. eapply IHt1 in H. left. eauto.
      eapply IHt2 in H. right. eauto. 
    + destruct H. eapply IHt1 in H. left. eauto.
      eapply IHt2 in H. right. eauto. 
Qed.

Lemma exp_locs_shift: forall t (H2' H2 HX: lenv),
  exp_locs (H2' ++ HX ++ H2) (splice_tm t (length H2) (length HX)) =
  exp_locs (H2' ++ H2) t.
Proof.
  intros. eapply functional_extensionality. 
  intros. eapply propositional_extensionality.
  revert H2' H2 HX x. unfold exp_locs. intuition.
  - eapply vl_mono. 2: eapply vars_locs_shift with (L:=0).
    simpl. intros ? Q. unfoldq. intuition. eauto. 
    eapply vl_mono. 2: eapply H. 
    simpl. intros ? Q. unfoldq. intuition. 
  - eapply vl_mono. 2: eapply vars_locs_shift with (L:=0).
    simpl. intros ? Q. unfoldq. intuition. eauto. 
    eapply vl_mono. 2: eapply H. 
    simpl. intros ? Q. unfoldq. intuition. 
Qed.


Lemma fv_change_bound: forall t1 a b x,
    plift (fv a t1) x ->
    x <= a ->
    x < b ->
    plift (fv b t1) x.
Proof.
  intros t1. induction t1; intros; simpl in *; eauto. 
  - rewrite plift_or in *. destruct H. left. eauto. right. eauto.
  - rewrite plift_or in *. destruct H. left. eauto. right. eauto.
  - rewrite plift_diff, plift_one in *.
    destruct H. split. eapply IHt1. eauto. lia. lia. unfold pone. lia.
  - rewrite plift_or in *. destruct H. left. eauto. right. eauto.
Qed.

Lemma fv_splice_miss: forall t1 a b x n,
    x < a ->
    x < b ->
    plift (fv a (splice_tm t1 b n)) x <->
    plift (fv a t1) x.
Proof.
  intros t1. induction t1; intros; simpl in *; eauto.
  - intuition.
  - intuition.
  - bdestruct (i <? b). intuition.
    rewrite plift_one in *. split; intros; inversion H2. subst. lia.
    rewrite plift_one in *. inversion H2. lia.     
  - split; intros.
    rewrite plift_or in *. 
    destruct H1. left. eapply IHt1_1; eauto. right. eapply IHt1_2; eauto.
    rewrite plift_or in *. 
    destruct H1. left. eapply IHt1_1; eauto. right. eapply IHt1_2; eauto.
  - split; intros.
    rewrite plift_or in *. 
    destruct H1. left. eapply IHt1_1; eauto. right. eapply IHt1_2; eauto.
    rewrite plift_or in *. 
    destruct H1. left. eapply IHt1_1; eauto. right. eapply IHt1_2; eauto.
  - split; intros.
    rewrite plift_diff, plift_one in *.
    destruct H1. split. eapply IHt1. eauto. eauto. eauto. eauto.
    rewrite plift_diff, plift_one in *.
    destruct H1. split. eapply IHt1. eauto. eauto. eauto. eauto. 
  - split; intros.
    rewrite plift_or in *. 
    destruct H1. left. eapply IHt1_1; eauto. right. eapply IHt1_2; eauto.
    rewrite plift_or in *. 
    destruct H1. left. eapply IHt1_1; eauto. right. eapply IHt1_2; eauto. 
Qed.

Lemma fv_subst': forall t2 t1 v (H2' H2: lenv) x,
    plift (fv (length H2) t1) x ->
    x < length H2 ->
    plift (fv (length (H2' ++ v::H2)) t2) (length H2) ->
    plift (fv (length (H2' ++ H2)) (subst_tm t2 (length H2) t1)) x.
Proof.
  intros t2. induction t2; intros; simpl in *.
  - rewrite plift_empty in *. contradiction.
  - rewrite plift_empty in *. contradiction.
  - rewrite plift_one in *. inversion H1.
    bdestruct (length H2 =? length H2).
    eapply fv_change_bound. eauto. lia. rewrite app_length. lia.
    contradiction.
  - eauto. 
  - eauto.
  - rewrite plift_or in *. destruct H1. left. eauto. right. eauto.
  - rewrite plift_or in *. destruct H1. left. eauto. right. eauto.
  - rewrite plift_diff, plift_one in *. destruct H1. split.
    replace (S (length (H2' ++ H2))) with (length ((H2'++[v])++H2)). eapply IHt2. eapply fv_splice_miss. eauto. eauto. eauto. eauto. rewrite app_length in *.
    rewrite app_length. replace ((length H2' + length [v] + length (v::H2))) with (S (length H2' + length (v::H2))). eauto. simpl. lia.
    repeat rewrite app_length. simpl. lia. rewrite app_length. unfold pone. lia.
  - eauto. 
  - rewrite plift_or in *. destruct H1. left. eauto. right. eauto. 
Qed.

Lemma subst_ql_fv_subst: forall t t1 (G G': tenv) T0 a0,
    psub
      (subst_ql
         (plift (fv (S (length (G' ++ (T0, a0) :: G))) t))
         (length G))
      (plift (fv (S (length (G' ++ G))) (subst_tm t (length G) t1))).
Proof.
  intros t. induction t; intros; intros ? Q; simpl in *; intuition.
  - unfold subst_ql in *. bdestruct (x <? length G); intuition.
  - unfold subst_ql in *. bdestruct (x <? length G); intuition.
  - unfold subst_ql in *. bdestruct (x <? length G).
    rewrite plift_one in *. inversion Q. subst i.
    bdestruct (length G =? x). lia.
    bdestruct (length G <? x). lia. simpl. rewrite plift_one. eauto.
    rewrite plift_one in *. inversion Q. subst i.
    bdestruct (length G =? x + 1). lia.
    bdestruct (length G <? x + 1). simpl. rewrite plift_one.
    destruct x. simpl. intuition. simpl. unfold pone. intuition.
    simpl. lia.
  - eapply IHt. eauto.
  - eapply IHt. eauto.
  - rewrite plift_or in *. rewrite subst_ql_or in *.
    destruct Q. left. eapply IHt1. eauto. right. eapply IHt2. eauto.
  - rewrite plift_or in *. rewrite subst_ql_or in *.
    destruct Q. left. eapply IHt1. eauto. right. eapply IHt2. eauto.
  - rewrite plift_diff in *. rewrite subst_ql_diff in *.
    destruct Q as (Q1 & Q2). split.
    specialize (IHt (splice_tm t1 (length G) 1) G ((T0,a0)::G') T0 a0).
    simpl in IHt. eapply IHt. eauto.
    rewrite plift_one in *. 
    replace (S (length (G' ++ (T0, a0) :: G))) with (length (((T0,a0)::G') ++ (T0, a0) :: G)) in Q2. rewrite subst_ql_one_hit in Q2. simpl in Q2. eapply Q2.
    simpl. eauto.
  - eapply IHt. eauto.
  - rewrite plift_or in *. rewrite subst_ql_or in *.
    destruct Q. left. eapply IHt1. eauto. right. eapply IHt2. eauto.
Qed.


Lemma exp_locs_subst': forall t2 t1 v (H2' H2: lenv) l2,
    exp_locs H2 t1 l2 ->
    plift (fv (length (H2' ++ v::H2)) t2) (length H2) ->
    exp_locs (H2' ++ H2)
      (subst_tm t2 (length H2)
         (splice_tm t1 (length H2) (length H2'))) l2.
Proof.
  intros. unfold exp_locs in *.
  destruct H as (?&?&?&?&?).
  assert (x < length H2). eapply indexr_var_some'. eauto. 
  eexists. split.
  eapply fv_subst'. rewrite fv_splice_miss. eauto. 1-3: eauto.
  eauto.
  eexists. split. rewrite indexr_skips. eauto. eauto. eauto. 
Qed.
  

Lemma exp_locs_subst'': forall t t1 v H2 H2',
    psub (exp_locs (H2'++ v::H2) t) pempty ->
    (plift (fv (length (H2'++ v::H2)) t) (length H2) ->
     psub (exp_locs H2 t1) pempty) ->
    psub (exp_locs (H2' ++ H2)
            (subst_tm t (length H2)
               (splice_tm t1 (length H2) (length H2')))) pempty.
Proof.
  intros t. induction t; eauto.
  - intros. unfold exp_locs in *. simpl in *.
    rewrite plift_empty, vl_empty. unfoldq. intuition. 
  - intros. unfold exp_locs in *. simpl in *.
    rewrite plift_empty, vl_empty. unfoldq. intuition. 
  - intros. simpl. bdestruct (length H2 =? i).
    + unfold exp_locs in H0 at 1. simpl in *.
      rewrite plift_one in *. intros ? Q. eapply H0. intuition.
      replace (H2'++H2) with ([]++H2'++H2) in Q. 
      rewrite exp_locs_shift in Q. 2: simpl; eauto. eapply Q.
    + bdestruct (length H2 <? i).
      * destruct i. lia.
        simpl in *. intros ? Q. eapply H. erewrite <-exp_locs_shift with (HX:=[v]) in Q.
        simpl in Q. bdestruct (i <? length H2). lia.
        replace (S i) with (i+1). eauto. lia.
      * intros ? Q. eapply H.
        erewrite <-exp_locs_shift with (HX:=[v]) in Q.
        simpl in Q. bdestruct (i <? length H2). 2: lia.
        eauto.
  - intros. simpl in *. rewrite plift_or in *.
    rewrite exp_locs_put in *. intros ? Q. destruct Q.
    eapply IHt1. intros ? Q. eapply H. left. eauto. intros.
    eapply H0. left. eauto. eauto. eauto. 
    eapply IHt2. intros ? Q. eapply H. right. eauto. intros.
    eapply H0. right. eauto. eauto.
  - intros. simpl in *. rewrite plift_or in *.
    rewrite exp_locs_app in *. intros ? Q. destruct Q.
    eapply IHt1. intros ? Q. eapply H. left. eauto. intros.
    eapply H0. left. eauto. eauto. eauto. 
    eapply IHt2. intros ? Q. eapply H. right. eauto. intros.
    eapply H0. right. eauto. eauto.
  - intros. simpl in *. rewrite plift_diff, plift_one in *.
    intros ? Q. eapply IHt with (H2':=qempty::H2'). simpl.
    intros ? Q1. eapply H. eapply exp_locs_abs in Q1.
    destruct Q1. eauto. rewrite plift_empty in H1. contradiction.
    intros. eapply H0. split. eapply H1. unfoldq.
    rewrite app_length. simpl. lia. 
    rewrite splice_acc in Q. simpl.
    unfold exp_locs in Q. unfold exp_locs. simpl in *.
    rewrite plift_diff, plift_one in Q. 
    destruct Q as (?&?&?).
    eexists. split. eapply H1. destruct H3 as (?&?&?).
    eexists. split. rewrite indexr_skip. eauto.
    eapply indexr_var_some' in H3. lia.
    eauto. 
  - intros. simpl in *. rewrite plift_or in *.
    rewrite exp_locs_tbin in *. intros ? Q. destruct Q.
    eapply IHt1. intros ? Q. eapply H. left. eauto. intros.
    eapply H0. left. eauto. eauto. eauto. 
    eapply IHt2. intros ? Q. eapply H. right. eauto. intros.
    eapply H0. right. eauto. eauto.
Qed.

Lemma encap_subst: forall G' T0 a0 G pf af, 
  env_cap (G' ++ (T0, false, a0) :: G) pf af ->
  env_cap (G' ++ G) (subst_qql pf (length G)) af.
Proof.
  intros.
  intros ? ? ? ? IX ?. 
  unfold subst_qql in H0.
  erewrite <-indexr_splice1 with (y := (T0, false, a0)) in IX.
  eapply H in IX. 
  bdestruct (x <? length G); intuition. 
  unfold bsub in *. intros ?. intuition.
  bdestruct (x <? length G); intuition. eapply IX.  
  replace (S x) with (x + 1). intuition. lia.
  auto.
Qed.


Lemma st_weaken: forall t1 p fr a e T1 G
  (W: has_type G t1 T1 p fr a e),
  forall u M H1 H2 H2' HX V1 V2 V2' VX,
    env_type M H1 (H2'++H2) V1 (V2'++V2) G u (plift p) ->
    length H2 = length V2 ->
    length HX = length VX ->
    length H2' = length V2' ->
    bsub e u ->
    exp_type_eff M H1 (H2'++HX++H2) V1 (V2'++VX++V2) t1 (splice_tm t1 (length V2) (length VX)) T1 u fr a e.
Proof.
  intros ? ? ? ? ? ? ? W. 
  induction W; intros ?????????? WFE LH2 LHX LH2'; intros E SW ???? ST P1 P2. 
  - eapply exp_true; eauto.
  - eapply exp_false; eauto.
  - eapply WFE in H as H'. destruct H' as (v1 & v2 & uv & ls1 & ls2 & IX1 & IX2 & IV1 & IV2 & IW & UX & VX' & VQ1 & VQ2).
    subst uv. 
    eapply exp_var with (ls1 := ls1)(ls2 := ls2); eauto.
    rewrite <-LH2, <-LHX. rewrite indexr_splice. eauto.
    rewrite indexr_splice. eauto.
    eapply VX'. rewrite plift_one. intuition.
  - eapply exp_ref; eauto. eapply IHW; eauto.
  - eapply exp_get; eauto. eapply IHW; eauto.
    unfold bsub in *. destruct e, u; intuition.
    unfoldq. destruct e; intuition.
    unfoldq. destruct e; intuition. 
  - simpl in *.
    edestruct (IHW1 u M H1 H2 H2' HX) as (S1' & S2' & M' & ?); eauto.
    eapply envt_tighten; eauto. rewrite plift_or. unfoldq. intuition.
    unfold bsub in *. destruct e1, u; intuition. 
    rewrite exp_locs_put in *. unfoldq. destruct e1,e2; simpl in *; intuition.
    rewrite exp_locs_put, exp_locs_shift in *. unfoldq. destruct e1,e2; simpl in *; intuition. 
    eapply exp_put; eauto.
    destruct H as (?&?&?&?&?&?&?&?&?&?&?&?&?).
    eapply IHW2; eauto.
    eapply envt_store_change. eapply envt_tighten; eauto. rewrite plift_or. unfoldq. intuition.
    intros ?????. eauto.
    destruct ST as (?&?&?). destruct s1 as (?&?&?). lia.
    destruct ST as (?&?&?). destruct s1 as (?&?&?). lia.
    unfold bsub in *. destruct e2, u; intuition.     
    rewrite exp_locs_put in *. unfoldq. destruct e1,e2; simpl in *; intuition.
    rewrite exp_locs_put in *. unfoldq. destruct e1,e2; simpl in *; intuition.
  - simpl in *.
    edestruct (IHW1 u M H1 H2 H2' HX) as (S1' & S2' & M' & ?); eauto.
    eapply envt_tighten; eauto. rewrite plift_or. unfoldq. intuition.
    unfold bsub in *. destruct ef, u; intuition.
    rewrite exp_locs_app in *. unfoldq. destruct e1,ef,e2; simpl in *; intuition.
    rewrite exp_locs_app, exp_locs_shift in *. unfoldq. destruct e1,ef,e2; simpl in *; intuition.
    eapply exp_app; eauto.
    destruct H as (?&?&?&?&?&?&?&?&?&?&?&?&?&?&?).
    eapply IHW2; eauto.
    eapply envt_store_change. eapply envt_tighten; eauto. rewrite plift_or. unfoldq. intuition.
    intros ?????. eauto. 
    destruct ST as (?&?&?). destruct H7 as (?&?&?). lia.
    destruct ST as (?&?&?). destruct H7 as (?&?&?). lia.
    unfold bsub in *. destruct e1, u; intuition. 
    rewrite exp_locs_app in *. unfoldq. destruct e1,ef,e2; simpl in *; intuition.
    rewrite exp_locs_app in *. unfoldq. destruct e1,ef,e2; simpl in *; intuition.
    intros. unfold bsub in *. destruct e1, ef, e2, af, a2, u; simpl in *; intuition.
    intros. unfold bsub in *. destruct a1, ef, e2, af, a2, u; simpl in *; intuition.
    intros. unfold bsub in *. destruct af, a1, e2; simpl in *; intuition.
    intros. destruct fr1, a1; intuition.
  - simpl in *.
    eapply exp_abs; eauto. {
      intros.
      assert (e2||uy&&a2 = (e2||a2)&&uyv) as EQ1. {
        destruct e2,a2,uy,uyv; intuition.
      }
      assert ((e2||a2)&&uyv = true -> af = false \/ u = true) as EQ2. {
        destruct e2,a2,af,uy,uyv; intuition.
      }
      assert ((e2||a2)&&uyv = false -> e2 = false /\ a2 = false \/ uyv = false) as EQ3. {
        destruct e2,a2,uyv; eauto.
      }
      remember (e2||uy&&a2) as D. destruct D.
      + (* use *)
        assert (u = false -> af = true -> e2 = false). destruct u,af,e2; intuition.
        assert (u = false -> af = true -> a2 = false). destruct u,af,a2; intuition.
        assert (u = false -> af = false). intros. destruct af. {
          replace a2 with false in *. 2: intuition.
          replace e2 with false in *. 2: intuition.
          destruct uy; inversion HeqD. } eauto. 

          assert (e2||a2 = true). destruct e2,a2; intuition. 
        
          eapply exp_usable with (u := true). 2: auto.
          edestruct (IHW true M' (vx1::H1) H2 (vx2::H2') HX (lsx1::(restrictV ((e2||a2)&&af&&u) V1)) (restrictV ((e2||a2)&&af&&u) V2) (lsx2:: (restrictV ((e2||a2)&&af&&u) V2'))
                                 (restrictV ((e2||a2)&&af&&u) VX)) as (S1'' & S2'' & M'' & HY).
          2: { erewrite restrictV_length; eauto. }
          2: { simpl. erewrite restrictV_length; eauto. }
          2: { simpl. erewrite restrictV_length; eauto. }
          all: eauto.
          2: { intros ?. auto. }
          {
            replace ((lsx2 :: restrictV ((e2 || a2) && af && u) V2') ++ restrictV ((e2 || a2) && af && u) V2)
              with  ((lsx2 :: restrictV ((e2 || a2) && af && u) (V2'++V2))).
            eapply envt_tighten.
            eapply envt_extend.
            eapply envt_store_change with (M := M)(p := (plift pf)).
            destruct u. {
              eapply envt_strengthenWX with (uw := true). unfold restrictV. auto.
              unfold bsub. intuition. rewrite H23 in *; eauto. simpl. destruct af; auto.
            } {
              eapply envt_strengthenW2. rewrite H22 in *; auto. rewrite H23 in *. simpl in *.
              eapply envt_store_changeV'''. eapply WFE.
              auto. auto. rewrite H22 in *; auto.
            } 

            eapply hast_fv in W. simpl in W. destruct WFE as (?&?&L1&L2&?). subst pf p2.
            intros ?????. eapply H3. eauto. eauto.

            unfold exp_locs. simpl. erewrite restrictV_length. rewrite L1. destruct e2,a2,af; simpl in *; intuition. eauto.
            unfold exp_locs. simpl. rewrite <-L2 in H28. rewrite plift_diff in *. rewrite plift_one in *.
            remember (e2||a2) as b. 
            destruct b; simpl in *. 2: { destruct H28 as (? & ? & ?).  destruct H29 as (? & ? & ?). 
              assert (x < length (V2'++V2)). eapply indexr_var_some' in H29. rewrite map_length in H29. lia. 
              eapply indexr_var_some in H31. destruct H31. eapply indexr_map in H31. rewrite H29 in H31. inversion H31. subst x0. rewrite plift_empty in H30. unfoldq; intuition. } 
            destruct af. 2: { assert False.  eapply aux2'. eauto. contradiction. }              
             
            simpl in *.
            replace (S (length (V2' ++ V2))) with (1 + (length (V2' ++ V2))) in H28.
            erewrite restrictV_length; eauto.
            replace (S (length (V2' ++ VX ++ V2))) with (1 + (length (V2' ++ VX ++ V2))).
            replace (pone (length (V2' ++ V2))) with (pdiff (pnat (1 + length (V2' ++ V2))) (pnat (length (V2' ++ V2)))) in H28.
            destruct u. 
            unfold restrictV in *. rewrite <- vars_locs_shift with (HX := VX) in H28.
            simpl in H28. 
            replace (pone (length (V2' ++ VX ++ V2))) with (pdiff (pnat (1 + length (V2' ++ VX ++ V2))) (pnat (length (V2' ++ VX ++ V2)))).
            auto.
            
            eapply functional_extensionality. intros. eapply propositional_extensionality. split; unfoldq; intuition.
            simpl in H28. eapply aux2' in H28; auto. unfoldq; intuition.
            eapply functional_extensionality. intros. eapply propositional_extensionality. split; unfoldq; intuition.
            simpl. lia. simpl. lia. eauto. eauto.

            rewrite H5 in H19. 3: eauto. destruct fr1,a1; auto. auto.
            intros ? ?. eapply H17. intuition.
            intros ? ?. eapply H18. intuition.

            subst pf. rewrite plift_diff, plift_one. unfoldq. intuition.
            bdestruct (x =? length env); intuition.
            simpl. remember ((e2||a2)&&af&&u) as b. 
            destruct b; simpl; auto. rewrite map_app. auto.
          }
          
          intros ? Q. destruct e2. 2: contradiction. eapply exp_locs_abs in Q. destruct Q; eauto.
          rewrite H23 in H24. simpl in H24. destruct af. 2: { assert False. eapply aux2. eauto. contradiction. }
          simpl in *. destruct u. 2: { eapply aux2 in H24. unfoldq; intuition. } eauto.

          intros ? Q. destruct e2. 2: contradiction. simpl in Q. eapply exp_locs_abs in Q. destruct Q; eauto.
          destruct af. 
          2: {  replace (false && u) with false  in H24. 
                replace (restrictV false V2' ++ restrictV false VX ++ restrictV false V2)
                with  (restrictV false (V2'++VX++V2)) in H24. eapply aux2' in H24. unfoldq; intuition.
                simpl. rewrite map_app. rewrite map_app. auto. auto.
             }
          destruct u. auto. 
          unfold exp_locs in H24. replace (true && false) with false in H24. 2: { auto. } 
          replace (restrictV false V2' ++ restrictV false VX ++ restrictV false V2)
            with  (restrictV false (V2'++VX++V2)) in H24. eapply aux2' in H24. unfoldq; intuition.
          simpl. rewrite map_app. rewrite map_app. auto.
            
          replace ((e2 || a2) && af && (negb ((e2 || a2) && af) || u)) with ((e2 || a2) && af && u).
          2:  { rewrite H23. simpl. destruct af, u; intuition. }
          simpl in *.
          eauto.
          eexists. eexists. eexists. eauto.  
          replace (restrictV ((e2 || a2) && af && u) V2' ++ restrictV ((e2 || a2) && af && u) VX ++ restrictV ((e2 || a2) && af && u) V2)
             with (restrictV ((e2 || a2) && af && u) (V2' ++ VX ++ V2)) in HY. 
          replace (length (restrictV ((e2 || a2) && af && u) V2))
             with (length V2) in HY.
          erewrite restrictV_length in HY. 2: eauto.  eapply HY.
          erewrite restrictV_length; eauto.
          destruct ((e2||a2)&&af&&u); simpl in *; auto. 
          rewrite map_app. rewrite map_app. auto.
      + (* mention *)  
        assert (e2 = false). destruct e2,a2; intuition.
        assert (a2 = false \/ uyv = false). destruct e2,a2,uy; intuition.
        subst e2.
        eapply exp_mentionable1; eauto. 
        edestruct (IHW false) with (V1:=restrictV false (lsx1 :: V1)) (V2':=restrictV false (lsx2 :: V2')) (V2 := restrictV false V2)(VX := restrictV false VX)
                                   (H1 := (vx1::H1))(H2 := H2) (H2' := vx2::H2') (HX := HX) as (S1'' & S2'' & M'' & HY). 
        
        2: { erewrite restrictV_length; eauto. }
        2: { erewrite restrictV_length; eauto. }
        2: { simpl. rewrite map_length. auto. }
        2: { unfold bsub. auto.  }
        all: eauto.
        {
         
          eapply envt_tighten. 
          replace (restrictV false (lsx2 :: V2') ++ restrictV false V2) with (qempty :: (restrictV false (V2' ++ V2))).
          2: { simpl. rewrite map_app. auto. }
          replace (restrictV false (lsx1 :: V1)) with (qempty :: (restrictV false V1)).
          2: { simpl. auto. }
          replace ((vx2::H2')++H2) with (vx2 :: (H2'++H2)).
          2: { simpl. auto. }
          eapply envt_extend with (p := (plift pf)). 
          destruct u. simpl. 
          eapply envt_store_changeV''. eauto. eauto. eauto.
          eapply envt_store_changeV'''. eauto. 
          eauto. eauto.
          2: eauto.

          remember (fr1||a1) as D. destruct D.
          eapply valt_reset_locs. eapply valt_usable. eauto.
          intuition. intuition.
          erewrite aux1 at 1.
          erewrite aux1 at 1.
          rewrite H8 in H19. eapply H19.
          eauto. eauto. eauto. eauto.
          rewrite plift_empty. unfoldq. intuition.
          rewrite plift_empty. unfoldq. intuition. 

          clear H21.
          subst pf. rewrite plift_diff, plift_one. unfoldq. intuition.
          bdestruct (x =? length env); intuition.
        }
        
        eexists. eexists. eexists. simpl in HY. rewrite map_length in HY. rewrite map_length in HY. eauto.
    }
    destruct u. {
      replace (a2||e2) with (e2||a2). 2: eauto with bool. 
      remember (e2||a2) as D. destruct D.
      intros. assert (af=false). destruct H3, af; eauto. subst af.
      simpl in *. unfold pif. eapply aux2'.
      simpl. unfoldq. intuition.
    } {
      intros. subst.
      replace (a2||e2) with (e2||a2). 2: eauto with bool.
      intros ? Q.
      remember (e2||a2) as b. 
      destruct b; try contradiction.
      simpl in *. destruct af.
      eapply aux2. eauto. eapply aux2. eauto. 
    }

    eapply hast_fv in W as A. subst p2 pf.
    replace (tabs (splice_tm t (length V2) (length VX))) with
      (splice_tm (tabs t) (length V2) (length VX)). 2: eauto. 
    
    destruct u. {
      replace (a2||e2) with (e2||a2). 2: eauto with bool. 
      remember (e2||a2) as D. destruct D.
      intros. assert (af=false). destruct H, af; eauto. subst af.
      simpl. eapply aux2.      
      intros. destruct af; simpl in *.
      intros ? ?. rewrite pif_false in H3. contradiction.
      replace (tabs (splice_tm t (length V2) (length VX))) with
      (splice_tm (tabs t) (length V2) (length VX)). 2: eauto.
      intros ? ?. rewrite pif_false in H3. auto.
    } {
      intros. 
      replace (a2||e2) with (e2||a2). 2: eauto with bool. 
      remember (e2||a2) as D. destruct D. 
      intros ? ?. destruct af. 
      simpl in H3. 
      replace (tabs (splice_tm t (length V2) (length VX)))  
         with (splice_tm (tabs t) (length V2)(length VX)) in H3. 2: { simpl; auto. }
      eapply aux2 in H3. auto. simpl in H3. eapply aux2 in H3. auto.
      unfoldq; intuition.
    } 
  - eapply exp_tnot; eauto. eapply IHW; eauto.
  - simpl in *. 
    edestruct (IHW1 u M H1 H2 H2' HX) as (S1' & S2' & M' & HX1); eauto. 
    eapply envt_tighten. eauto. rewrite plift_or. unfoldq; intuition.
    unfold bsub in *. destruct e1, e2; intuition. 
    rewrite exp_locs_tbin in *. unfoldq. destruct e1, e2; simpl in *; intuition. 
    rewrite exp_locs_tbin, exp_locs_shift in *. unfoldq. destruct e1, e2; simpl in *; intuition.
    eapply exp_tbin. eauto. eauto. eauto. eauto. eauto.
    eauto.
    destruct HX1 as (?&?&?&?&?&?&?&?&?&?&?&?&?).
    eapply IHW2.
    eapply envt_store_change. eapply envt_tighten. eauto. rewrite plift_or. unfoldq; intuition.
    intros ?????. eapply s. auto. 
    destruct ST, s1. lia. 
    destruct ST, s1. lia.
    all: eauto.
    unfold bsub in *. destruct e2; intuition.
    rewrite exp_locs_tbin in *. unfoldq. destruct e1,e2; simpl in *; intuition.
    rewrite exp_locs_tbin in *. unfoldq. destruct e1,e2; simpl in *; intuition.    
  - destruct fr; try eapply exp_sub_fresh; eauto; eapply IHW; eauto.
  - destruct a; try eapply exp_sub_cap; eauto; eapply IHW; eauto.
  - destruct e; try eapply exp_sub_eff; eauto; eapply IHW; eauto.
    unfold bsub in *. intuition. 
    unfoldq. intuition.
    unfoldq. intuition.
Qed.

Lemma tevaln_unique: forall S1 S1' S1'' H1 e1 v1 v1',
    tevaln S1 H1 e1 S1' v1 ->
    tevaln S1 H1 e1 S1'' v1' ->
    S1' = S1'' /\ v1 = v1'.
Proof.
  intros.
  destruct H as [n1 ?].
  destruct H0 as [n2 ?].
  assert (1+n1+n2 > n1) as A1. lia.
  assert (1+n1+n2 > n2) as A2. lia.
  specialize (H _ A1).
  specialize (H0 _ A2).
  split; congruence.
Qed.

Lemma split: forall {A} (xs: list A) i,
    i <= length xs ->
    exists xs1 xs2, length xs2 = i /\ xs = xs1 ++ xs2.
Proof.
  intros A xs. induction xs; intros.
  - simpl in H. eexists [],[]. intuition. 
  - simpl in H.
    bdestruct (i =? S (length xs)).
    + subst. exists [], (a::xs). intuition.
    + destruct (IHxs i) as (xs1 & xs2 & ? & ?). lia.
      exists (a::xs1), xs2. split. eauto. subst. eauto. 
Qed.

Lemma indexr_extensionality: forall (S S': stor),
    length S = length S' ->
    (forall i, i < length S -> indexr i S = indexr i S') ->
    S = S'.
Proof.
  intros S. induction S; intros; destruct S'.
  - eauto.
  - inversion H.
  - inversion H.
  - simpl in H, H0.
    assert (a = v). {
      assert (length S < Datatypes.S (length S)). lia.
      eapply H0 in H1.
      bdestruct (length S =? length S). 2: lia. 
      bdestruct (length S =? length S'). 2: lia. 
      inversion H1. eauto. }
    assert (S = S'). {
      eapply IHS. eauto. intros. 
      assert (i < Datatypes.S (length S)). lia.
      eapply H0 in H3. 
      bdestruct (i =? length S). lia. 
      bdestruct (i =? length S'). lia.
      eauto.
    }
    congruence.
Qed.

Lemma storew_length: forall S S',
    store_write S S' pempty ->
    length S <= length S'.
Proof.
  intros. unfold store_write in *.
  bdestruct (length S <=? length S'). eauto.
  destruct S. inversion H0.
  assert (pdiff (pdom (v::S)) pempty (length S)) as H1. unfoldq. simpl. lia.
  eapply H in H1.
  rewrite indexr_head in H1.
  symmetry in H1. eapply indexr_var_some' in H1. 
  simpl. lia. 
Qed.

Lemma storew_prefix: forall S S',
    store_write S S' pempty ->
    exists SD, S' = SD ++ S.
Proof.
  intros.
  eapply storew_length in H as HL.
  eapply split in HL as HS.
  destruct HS as (SX1 & SX2 & ? & ?).
  assert (S = SX2). {
    eapply indexr_extensionality. eauto.
    intros. rewrite H. 2: unfoldq; intuition. 
    subst. rewrite indexr_skips. eauto. lia. 
  }
  exists SX1. congruence. 
Qed.

Lemma st_weaken1: forall t1 T1 G p a e
  (W: has_type G t1 T1 p false a e),
  forall u M H1 H2 H2' V1 V2 V2' S01 S02 p1 p2,
    env_type M H1 (H2'++H2) V1 (V2'++V2) G u (plift p) ->
    length H2 = length V2 ->
    bsub e u ->
    stty_wellformed M ->
    store_type S01 S02 M p1 p2 ->
    (psub (pif e (exp_locs V1 t1)) p1) ->
    (psub (pif e (exp_locs (V2'++V2) t1)) p2) ->
    (u = false -> psub (exp_locs (V2'++V2) t1) pempty) -> 
    exists S1' v1 ls1,
      length S01 <= length S1' /\
      (tevaln S01 H1 t1 (S1') v1) /\
      psub (plift ls1)
        (por (pif a (exp_locs V1 t1))
           (pif false (pdiff (pdom (S1')) (pdom S01)))) /\
      store_write S01 (S1') 
        (pif e (exp_locs V1 t1)) /\
      forall HX VX S2X,
        length HX = length VX ->
        length S02 <= length S2X ->
        store_write S02 (S2X) 
          (pnot p2) ->
        exists uv S2' v2 ls2,
          (tevaln S2X (H2'++HX++H2) (splice_tm t1 (length H2) (length HX)) (S2') v2) /\
          length S2X <= length S2' /\  
          uv = (negb a || u) /\
          ((a = false \/ uv = false) -> psub (plift ls1) pempty) /\
          ((a = false \/ uv = false) -> psub (plift ls2) pempty) /\
          val_type (length S1', length S2', strel M) v1 v2 T1 (uv=true) ls1 ls2 /\
          psub (plift ls2)
            (por (pif a (exp_locs (restrictV u (V2'++VX++V2)) (splice_tm t1 (length V2) (length VX))))
               (pif false (pdiff (pdom (S2')) (pdom S2X)))) /\
          store_write S2X (S2') 
            (pif e (exp_locs (restrictV u (V2'++VX++V2)) (splice_tm t1 (length V2) (length VX)))).
Proof.
  intros ??????????????????? WFE LH2 E SW ST EP1 EP2.
  assert (exp_type S01 S02 M H1 (H2'++H2) V1 (V2'++V2) t1 t1 T1 u p1 p2 false a e) as HX. eapply fundamental; eauto.

  destruct ST as (L1 & L2 & ST).
  destruct HX as (S1' & S2' & M' & v1 & v2 & uv & ls1 & ls2 & HX).
  destruct HX as (SC' & SW' & TX1 & TX2 & LS1 & LS2 & ST' & VT & LX1 & LX2 & ES1 & ES2 & VQ1 & VQ2 & SE1 & SE2 & ESM).
  
  remember (qor (qif a (exp_locs_fix (restrictV (u&&a) V1) t1))
              (qif false (qdiff (qdom S1') (qdom S01)))) as lsu1. 
  
  exists S1', v1, lsu1. split. 2: split. 3: split. 4: split.
  eauto. eauto. 2: eauto.
  subst lsu1. rewrite plift_or, plift_if, plift_exp_locs, plift_if. unfoldq. intuition.
  destruct a. destruct u. 2: { eapply aux2 in H4. unfoldq; intuition. }
  auto. auto.  
  
  intros ??? LHX LSX2 SWX2.

  remember (length S01, length S2X, strel M) as MX'. 
  
  assert (env_type MX' H1 (H2' ++ H2) V1 (V2' ++ V2) G u (plift p)) as WFE'.
  eapply envt_store_change. eauto. 
  intros ?????. subst MX'. eauto. 
  subst MX'. unfold st_len1 at 2. simpl. lia. 
  subst MX'. unfold st_len2 at 2. simpl. lia. 

  assert (stty_wellformed MX') as SWX'. {
    subst MX'. split. 2: split.
    - simpl. unfold st_len1 at 1. unfold st_len2 at 1. simpl. intros. split.
      assert (l1 < st_len1 M). eapply SW. eauto. lia. 
      assert (l2 < st_len2 M). eapply SW. eauto. lia. 
    - simpl. eapply SW.
    - simpl. eapply SW.
  }
    
  assert (store_type S01 S2X MX' p1 p2) as STX'. {
    subst MX'. split. 2: split.
    - unfold st_len1 at 1. eauto. 
    - unfold st_len2 at 1. eauto. 
    - simpl. intros.
      edestruct ST as (b & ? & ?); eauto.
      eexists b. split. eauto. rewrite <-SWX2. eauto.
      split. eapply indexr_var_some' in H6. unfoldq. lia.
      intuition.
  }
  
  eapply st_weaken in W as W'; eauto. 
  edestruct W' as (S1X' & S2X' & MX'' & v1' & v2' & u' & ls1' & ls2' & W''). eauto. eauto. eauto.
  rewrite exp_locs_shift. eauto. 
  destruct W'' as (SC2' & SW2' & TX1' & TX2' & LS1' & LS2' & ST2' & VX' & LX1' & LX2' & ES1' & ES2' & VQ1' & VQ2' & SE1' & SE2' & ESM'). 

    
  exists u', S2X', v2', ls2'. 

  assert (S1' = S1X' /\ v1 = v1') as R. {
    eapply tevaln_unique. eauto. eauto. }

  destruct R as (R1 & R2). rewrite R2. 
  
  split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 

  rewrite LH2, LHX. eauto. 
  eauto.
  auto. 
  {
  intros ?.  subst. 
  rewrite plift_or, plift_if, plift_if.
  rewrite pif_false, por_empty_r.
  intros ? ?. 
  destruct a; try contradiction. destruct H0. inversion H0. simpl in *.
  subst u.
  rewrite plift_exp_locs in H3.
  eapply aux2 in H3. auto.
  
  }

  intros ? ? ?. destruct H0.
  eapply VQ2' in H3. subst a. repeat rewrite pif_false in H3.
  repeat rewrite por_empty_l in H3. auto. eapply ES2'. auto. auto. 
 

  eapply valt_store_change.
  eapply valt_sub_locs. eauto.
  subst lsu1. rewrite plift_or, plift_if, plift_exp_locs, plift_if, plift_diff, plift_dom. 
  rewrite pif_false in *. rewrite pif_false in *. rewrite por_empty_l in *. 
  destruct u,a; simpl in *; auto. 
  intros ? Q. eapply ES1' in Q; auto. unfoldq; intuition. 
  unfoldq; intuition.
  subst MX'. 
  intros ? ? ? Q ? ?. simpl in *. rewrite <-ESM'. eapply Q. eauto.
  destruct ST2' as (XL1&XL2&?). unfold st_len1 at 2. simpl. rewrite R1, XL1. eauto.
  destruct ST2' as (XL1&XL2&?). unfold st_len2 at 2. simpl. rewrite XL2. eauto. 

  rewrite pif_false in *. rewrite pif_false in *. rewrite por_empty_l in *. 
  destruct u. auto. destruct a; simpl in *. intros ? Q. eapply ES2' in Q; auto. unfoldq; intuition.
  rewrite pif_false.
  eauto.
  destruct u; auto. intros ? ?. eapply SE2'. 
  destruct H0. split; auto. intros ?. eapply H3. destruct e. unfold bsub in *. intuition.
  contradiction.
  destruct WFE as (?&?&?&?&?). rewrite app_length in *. lia. 
Qed.



Lemma vars_locs_empty: forall H,
  vars_locs H pempty = pempty.
Proof.
  intros. eapply functional_extensionality. intros.
  eapply propositional_extensionality. split; intros.
  destruct H0. unfoldq; intuition. unfoldq; intuition.
Qed.

Lemma exp_locs_subst''': forall t t1 ls2 V2' V2,
  psub (exp_locs (V2'++ls2::V2) t) pempty ->
  (~plift (fv (length (V2'++ls2::V2)) t) (length V2)) ->
  psub (exp_locs (V2'++V2) 
         (subst_tm t (length V2)
           (splice_tm t1 (length V2) (length V2')))) pempty.
Proof.
  intros t. induction t; eauto.
  - intros. unfold exp_locs in *. simpl in *.
    rewrite plift_empty.  rewrite vars_locs_empty. unfoldq; intuition.
  - intros. unfold exp_locs in *. simpl in *. rewrite plift_empty, vars_locs_empty. unfoldq; intuition.
  - intros. simpl in *. rewrite plift_one in H0. unfold pone in H0.
    bdestruct (length V2 =? i); intuition.
    bdestruct (length V2 <? i).
    + destruct i. lia.
      simpl in *. intros ? Q. eapply H.
      erewrite <- exp_locs_shift with (HX := [ls2]) in Q.
      simpl in Q. bdestruct (i <? length V2). lia.
      replace (S i) with (i+1). eauto. lia.
    + intros ? Q. eapply H.
      erewrite <- exp_locs_shift with (HX := [ls2]) in Q.
      simpl in Q. bdestruct (i <? length V2). 2: lia.
      eauto.
  - intros. simpl in *. rewrite plift_or in *.
    rewrite exp_locs_put in *. intros ? Q. destruct Q.
    eapply IHt1. intros ? Q. eapply H. left. eauto. intros ?.
    eapply H0. left. eauto. eauto.  
    eapply IHt2. intros ? Q. eapply H. right. eauto. intros ?.
    eapply H0. right. eauto. eauto.
  - intros. simpl in *. rewrite plift_or in *.
    rewrite exp_locs_app in *. intros ? Q. destruct Q.
    eapply IHt1. intros ? Q. eapply H. left. eauto. intros ?.
    eapply H0. left. eauto. eauto.  
    eapply IHt2. intros ? Q. eapply H. right. eauto. intros ?.
    eapply H0. right. eauto. eauto.
  - intros. simpl in *. rewrite plift_diff, plift_one in *.
    intros ? Q. eapply IHt with (V2':=qempty::V2'). simpl.
    intros ? Q1. eapply H. eapply exp_locs_abs in Q1.
    destruct Q1. eauto. rewrite plift_empty in H1. contradiction.
    intros ?. eapply H0. split. eapply H1. unfoldq.
    rewrite app_length. simpl. lia. 
    rewrite splice_acc in Q. simpl.
    unfold exp_locs in Q. unfold exp_locs. simpl in *.
    rewrite plift_diff, plift_one in Q. 
    destruct Q as (?&?&?).
    eexists. split. eapply H1. destruct H2 as (?&?&?).
    eexists. split. rewrite indexr_skip. eauto.
    eapply indexr_var_some' in H2. lia.
    eauto. 
  - intros. simpl in *. rewrite plift_or in *.
    rewrite exp_locs_tbin in *. intros ? Q. destruct Q.
    eapply IHt1. intros ? Q. eapply H. left. eauto. intros ?.
    eapply H0. left. eauto. eauto.  
    eapply IHt2. intros ? Q. eapply H. right. eauto. intros ?.
    eapply H0. right. eauto. eauto.
Qed.



(* Full substitution only works for pure expressions, which are store-invariant. *)


Lemma st_subst': forall t2 p fr a e T2 G0
  (W: has_type G0 t2 T2 p fr a e),
  forall G' G T1 a1, G0 = G'++(T1,false,a1)::G ->
  forall u M H1 H1' H2 H2' V1 V1' V2 V2' t1 v1 ls1,
    env_type M (H1'++H1) (H2'++H2) (V1'++V1) (V2'++V2) (G'++G) u (subst_ql (plift p) (length V2)) ->
    length H1 = length G ->
    length H2 = length G ->
    length V1 = length G ->
    length V2 = length G ->
    ((a1 = false \/ u = false) -> psub (plift ls1) pempty) ->
    ((u = false) -> psub (exp_locs (restrictV u V2) t1) pempty) ->
    (plift p (length G) ->
    forall HX VX S2X,
      length HX = length VX ->
      st_len2 M <= length S2X ->
      exists uv (S2':stor) v2 ls2, (* via st_weaken *)
        (tevaln S2X (HX++H2) (splice_tm t1 (length H2) (length HX)) (S2') v2) /\
        length S2X <= length S2' /\
        (uv = negb a1 || u) /\
        (a1 = false \/ uv = false -> psub (plift ls1) pempty) /\
        (a1 = false \/ uv = false -> psub (plift ls2) pempty) /\
        val_type (st_len1 M, length S2', strel M) v1 v2 T1 (uv=true) ls1 ls2 /\ 
        psub (plift ls2)
          (por (pif a1 (exp_locs (restrictV u (VX++ V2)) (splice_tm t1 (length V2) (length VX))))
             (pif false (pdiff (pdom (S2')) (pdom S2X)))) /\
        store_write S2X (S2') 
          (pif false (exp_locs (restrictV u (VX++ V2)) (splice_tm t1 (length V2) (length VX))))
    ) -> 
    bsub e u ->
    exp_type_eff M
      (H1'++v1::H1) (H2'++H2)
      (V1'++ls1::V1) (V2'++V2)
      t2 (subst_tm t2 (length V2) (splice_tm t1 (length V2) (length V2'))) T2 u fr a e.
Proof.  
  intros ? ? ? ? ? ? ? W. 
  induction W; simpl; intros ?????????????????? WFE LH1 LH2 LV1 LV2 LX1 LX2 WK; intros E SW ???? ST P1 P2.
  - eapply exp_true; eauto.
  - eapply exp_false; eauto.
  - bdestruct (length V2 =? x).
    + unfold exp_type, exp_type1, exp_type2. 
      assert (plift (qone x) (length G)) as A. subst. rewrite plift_one, LV2. intuition. 
      edestruct (WK A H2' V2' S2) as (u' & S2' & v2 & ls2 & TX2 & XL2 & LU1' & LU2' & LU3' & VX2 & LX2' & SEX2).
      destruct WFE as (?&?&?&?).  rewrite app_length in *. lia. 
      destruct ST as (?&?&?). lia.
      
      edestruct (storew_prefix S2 S2') as (SD2 & ?). eauto.

      exists S1, S2', (st_len1 M, length S2', strel M), v1, v2, u', ls1, ls2.
      split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 8: split.
      9: split. 10: split. 11: split. 12: split. 13: split. 14: split. 15: split. 16: split. 
      * intros ???. simpl. eauto. 
      * destruct SW as (SW1&?&?). split. 2: split.
        simpl. unfold st_len1 at 1. unfold st_len2 at 1. simpl.
        intros ?? R. eapply SW1 in R. destruct R. split. lia. destruct ST as (?&?&?). lia.
        eauto.
        eauto. 
      * exists 1. intros. destruct n. lia. simpl.
        subst x. rewrite LV2, <-LH1. rewrite indexr_insert. eauto.
      * replace (length V2) with (length H2).
        replace (length V2') with (length H2').
        eapply TX2. 
        destruct WFE as (?&?&?&?). rewrite app_length in *. lia. lia. 
      * eauto.
      * eapply storew_length. eauto. 
      * subst S2'.
        destruct ST as (L1 & L2 & L3).
        split. 2: split.
        simpl in *. unfold st_len1 at 1. simpl. eauto. unfold st_len2 at 1. simpl. eauto. 
        simpl. intros ?? SRL Q1 Q2. destruct SW as (SW & ? & ?). eapply SW in SRL as HH. destruct HH. 
        destruct Q1, Q2.
        -- edestruct L3 as (?&?&?); eauto. eexists. split. eauto. rewrite indexr_skips. eauto.
           eapply indexr_var_some'. eauto.
        -- unfoldq. lia. 
        -- unfoldq. lia. 
        -- unfoldq. lia. 
      * subst env x. rewrite LV2 in H. rewrite indexr_insert in H. inversion H. subst T1. subst fr a.
        eapply valt_usable. eauto. auto.
      * subst env x. rewrite LV2 in H. rewrite indexr_insert in H. inversion H. subst T1. subst fr a.
        simpl. auto.  
      * auto. 
      * intros ? ? ?. rewrite H5 in *. eapply LU2'. right. auto. auto. 
      * intros ? ? ?. rewrite H5 in *. eapply LU3'. right. auto. auto.  
      * subst env x. rewrite LV2 in H. rewrite indexr_insert in H. inversion H. subst T1. subst fr. subst a. simpl.
        intros ? ?. repeat rewrite pif_false. repeat rewrite por_empty_r.
        destruct a1. exists (length V2). split. simpl. rewrite plift_one. unfoldq; intuition.
        eexists. split. rewrite LV2. rewrite <- LV1. rewrite indexr_skips. rewrite indexr_head. eauto. simpl. lia. auto.
        simpl in *. eapply LX1. auto. eauto.
      * subst env x. rewrite LV2 in H. rewrite indexr_insert in H. inversion H. subst T1. subst fr. subst a. simpl. 
        intros ? ?. repeat rewrite pif_false. repeat rewrite por_empty_r.
        eapply LX2' in H0. destruct H0.
        destruct a1; try contradiction.
        destruct u. unfold restrictV in H0. auto.
        eapply aux2 in H0; auto. unfoldq; intuition.
        contradiction.
      * eapply storew_refl.
      * eapply SEX2.
      * eauto. 
    + bdestruct (length V2 <? x).
      * subst env. destruct x. lia. 
        erewrite <-indexr_insert_ge in H. 2: lia. simpl.
        eapply WFE in H as H'. destruct H' as (v1' & v2' & uv' & ls1' & ls2' & IX1 & IX2 & IV1 & IV2 & IUX & UT & VT & VQ1 & VQ2).
        eapply exp_var. rewrite <-indexr_insert_ge. eauto. lia. eauto.
        rewrite <-indexr_insert_ge. eauto. lia. eauto. eapply VT.
        simpl. rewrite plift_one. unfold subst_ql.
        bdestruct (x <? length V2). lia. unfold pone. lia. eauto. eauto. eauto. eauto. 
        subst uv'. destruct u,fr,a; eauto. 
      * subst env. rewrite <-indexr_insert_lt in H. 2: lia.
        eapply WFE in H as H'. destruct H' as (v1' & v2' & uv' & ls1' & ls2' & IX1 & IX2 & IV1 & IV2 & IUX & UT & VT & VQ1 & VQ2).
        eapply exp_var. rewrite <-indexr_insert_lt. eauto. lia. eauto.
        rewrite <-indexr_insert_lt. eauto. lia. eauto. eapply VT.
        simpl. rewrite plift_one. unfold subst_ql.
        bdestruct (x <? length V2). unfold pone. intuition. lia. eauto. eauto. eauto. eauto.
        subst uv'. destruct u,fr,a; eauto. 
  - eapply exp_ref; eauto. eapply IHW; eauto. 
  - eapply exp_get; eauto. eapply IHW; eauto.
     
    unfold bsub in *. intros ?. intuition.
    unfoldq. destruct e; intuition.
    unfoldq. destruct e; intuition. 

  - edestruct IHW1 as (S1' & S2' & M' & HEXP). eauto.
    eapply envt_tighten. eauto. 

    rewrite plift_or. unfold subst_ql. unfoldq. intuition. bdestruct (x <? length V2); eauto.
    all: eauto.
    intros A. eapply WK. rewrite plift_or. left. eauto.
    unfold bsub in *. intros. subst e1. simpl in E. auto.
    
    simpl in *. rewrite exp_locs_put in *. unfoldq. destruct e1,e2; simpl in *; intuition.
    simpl in *. rewrite exp_locs_put in *. unfoldq. destruct e1,e2; simpl in *; intuition. 
    eapply exp_put; eauto.
    destruct HEXP as (?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?).

    assert (st_len1 M <= st_len1 M').
    destruct ST as (?&?&?). destruct s1 as (?&?&?). lia.
    assert (st_len2 M <= st_len2 M').
    destruct ST as (?&?&?). destruct s1 as (?&?&?). lia.
    
    eapply IHW2; eauto.
    eapply envt_store_change. eapply envt_tighten. eauto.

    rewrite plift_or. unfold subst_ql. unfoldq. intuition. bdestruct (x4 <? length V2); eauto.

    intros ?????. eauto. eauto. eauto. 

    intros A HX VX S2X LHX SL2.
    assert (plift (qor p1 p2) (length G)) as A'.
    rewrite plift_or. right. eauto. 
    edestruct (WK A' HX VX S2X) as (u' & S2X' & v2 & ls2 & TVX2). lia. lia.  
    exists u', S2X', v2, ls2. intuition.
    eapply valt_store_change. eauto.
    intros ?????. simpl. eauto. eauto. eauto.
    unfold bsub in *. intros. subst e2. intuition. 
    rewrite exp_locs_put in *. unfoldq. destruct e1,e2; simpl in *; intuition.
    rewrite exp_locs_put in *. unfoldq. destruct e1,e2; simpl in *; intuition.
    
  - (* app *)
    edestruct IHW1 as (S1' & S2' & M' & HEXP). eauto.
    eapply envt_tighten. eauto. 

    rewrite plift_or. unfold subst_ql. unfoldq. intuition. bdestruct (x <? length V2); eauto.
    all: eauto.
    intros A. eapply WK. rewrite plift_or. left. eauto.
    
    unfold bsub in *. intros. subst ef. intuition.

    simpl in *. rewrite exp_locs_app in *. unfoldq. destruct e1,ef,e2; simpl in *; intuition.
    simpl in *. rewrite exp_locs_app in *. unfoldq. destruct e1,ef,e2; simpl in *; intuition. 
    eapply exp_app; eauto.
    destruct HEXP as (?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?).

    assert (st_len1 M <= st_len1 M').
    destruct ST as (?&?&?). destruct H8 as (?&?&?). lia.
    assert (st_len2 M <= st_len2 M').
    destruct ST as (?&?&?). destruct H8 as (?&?&?). lia.

    eapply IHW2; eauto.
    eapply envt_store_change. eapply envt_tighten. eauto.

    rewrite plift_or. unfold subst_ql. unfoldq. intuition. bdestruct (x4 <? length V2); eauto.

    intros ?????. eauto. eauto. eauto. 

    intros A HX VX S2X LHX SL2.
    assert (plift (qor p1 p2) (length G)) as A'.
    rewrite plift_or. right. eauto. 
    edestruct (WK A' HX VX S2X) as (u' & S2X' & v2 & ls2 & TVX2). lia. lia. auto.
    exists u', S2X', v2, ls2. intuition.
    eapply valt_store_change. eauto.
    intros ?????. simpl. eauto. eauto. eauto.
    unfold bsub in *. intros. subst e1. intuition.  
    rewrite exp_locs_app in *. unfoldq. destruct e1,e2; simpl in *; intuition.
    rewrite exp_locs_app in *. unfoldq. destruct e1,e2; simpl in *; intuition.

    unfold bsub in *. destruct e2, u, af, a1, a2; simpl in *; intuition.
    unfold bsub in *. destruct e2, u, af, a1, a2; simpl in *; intuition.
    unfold bsub in *. destruct e2, u, af, a1, a2; simpl in *; intuition.
    unfold bsub in *. destruct e2, u, af, a1, a2; simpl in *; intuition.
    
  - (* abs *)
   
    rename H1 into XX1. rename H2 into H1. rename H3 into H2.
    eapply exp_abs; eauto. {
      intros.
      assert (e2||uy&&a2 = (e2||a2)&&uyv) as EQ1. {
        destruct e2,a2,uy,uyv; intuition.
      }
      assert ((e2||a2)&&uyv = true -> af = false \/ u = true) as EQ2. {
        destruct e2,a2,af,uy,uyv; intuition.
      }
      assert ((e2||a2)&&uyv = false -> e2 = false /\ a2 = false \/ uyv = false) as EQ3. {
        destruct e2,a2,uyv; eauto.
      }
      remember (e2||uy&&a2) as D. destruct D.

      
      + (* use *)
        assert (u = false -> af = true -> e2 = false). destruct u,af,e2; intuition.
        assert (u = false -> af = true -> a2 = false). destruct u,af,a2; intuition.
        assert (u = false -> af = false). intros. destruct af. {
          replace a2 with false in *. 2: intuition.
          replace e2 with false in *. 2: intuition.
          destruct uy; inversion HeqD. } eauto.

        assert (e2||a2 = true). destruct e2,a2; intuition. 
        
        eapply exp_usable. 
        rewrite splice_acc.
        remember (if ((e2||a2)&&af&&u) then ls1 else qempty) as ls1'.
        edestruct IHW with (H1':=(vx1::H1')) (H2':=(vx2::H2')) (V1':=(lsx1::(restrictV ((e2 || a2) && af && (negb ((e2 || a2) && af) || u))V1')))
                           (V2':=(lsx2::(restrictV ((e2 || a2) && af && (negb ((e2 || a2) && af) || u)) V2')))(G':=((T1,fr1, a1)::G'))(u := true)
                           (V1 := (restrictV ((e2 || a2) && af && (negb ((e2 || a2) && af) || u)) V1))(V2 := (restrictV ((e2 || a2) && af && (negb ((e2 || a2) && af) || u)) V2)) 
                           (H1 := H1)(H2 := H2)(t1:=t1)(ls1 := ls1') as (? & ?). 
        subst env. simpl. all: eauto.
        2: { erewrite restrictV_length; eauto. lia. }
        2: { erewrite restrictV_length; eauto. }
        2: { intros [? | ?]. subst ls1'. rewrite H23. simpl. destruct af, u. eapply LX1. left. auto. 
        1-3: simpl; rewrite plift_empty; unfoldq; intuition. inversion H24. }
        2: { intros. intuition. } 
        3: { unfold bsub. auto. }
                
        {
          
        simpl.
        replace (lsx1 :: restrictV ((e2 || a2) && af && (negb ((e2 || a2) && af) || u)) V1' ++ restrictV ((e2 || a2) && af && (negb ((e2 || a2) && af) || u)) V1)
        with  ((lsx1 :: restrictV ((e2 || a2) && af && (negb ((e2 || a2) && af) || u)) (V1'++V1))).
        replace (lsx2 :: restrictV ((e2 || a2) && af && (negb ((e2 || a2) && af) || u)) V2' ++ restrictV ((e2 || a2) && af && (negb ((e2 || a2) && af) || u)) V2)
        with  ((lsx2 :: restrictV ((e2 || a2) && af && (negb ((e2 || a2) && af) || u)) (V2'++V2))).
        
        subst env. rewrite H23 in *. 
        eapply envt_tighten. eapply envt_extend. eapply envt_store_change with (M := M)(p := (plift (subst_qql pf (length V2)))).
        rewrite subst_ql_qql in *.
        destruct EQ2; auto. { 
          subst af. 
          destruct u. {
            eapply envt_strengthenWX; eauto. unfold restrictV. auto.
            simpl. rewrite LV2. eapply encap_subst; eauto.
          } {
            eapply envt_strengthenW2; eauto. eapply envt_store_changeV'''; eauto.
            rewrite LV2. eapply encap_subst; eauto.
          }
        } {
          subst u. simpl in *.
          destruct af. {
            simpl in *. auto.
          } {
            eapply envt_strengthenWX; eauto. unfold restrictV. auto.
            rewrite LV2. eapply encap_subst; eauto.
          }
        }
        
        

    {
      intros ?????. eapply H3. eauto. auto.
    
      rewrite <-subst_ql_qql in *. simpl in *.
      assert (length V1' = length G') as LV1'. destruct WFE as (?&?&?&?).
      repeat rewrite app_length in *. simpl in *. lia.
      eapply hast_fv in W. simpl. 
      destruct af. {
        simpl in *. 
        destruct u. 2: { eapply aux2' in H25. unfoldq; intuition. }
        subst pf p2. unfold exp_locs. simpl in *.
        rewrite app_length in *. rewrite plift_diff, plift_one in *.
        simpl in *. 
        destruct H25 as (?&?&?&?&?).
        unfold subst_ql in H.
        bdestruct (x <? length V2).
        eexists x. split. rewrite LV1, LV1'. eauto.
        eexists. rewrite indexr_skips in H25. split.
        rewrite indexr_skips. rewrite indexr_skip. eauto. lia. simpl. lia. eauto. lia.
        eexists. split. rewrite LV1, LV1'. eauto. 
        eexists. replace (x + 1) with (S x). 2: lia.
        erewrite <-indexr_insert_ge. split; eauto. lia.
      } {
         simpl in *. eapply aux2' in H25. unfoldq; intuition.
      }         

      rewrite <- subst_ql_qql in *. simpl in *.
      assert (length V2' = length G') as LV2'. destruct WFE as (?&?&?&?&?).
      repeat rewrite app_length in *. simpl in *. lia.
      eapply hast_fv in W. 
      subst pf p2.

      unfold exp_locs. simpl in *.
      rewrite plift_diff, plift_one in *.   

      rewrite subst_ql_diff in H26.
      rewrite LV2 in H26. rewrite LV2, LV2'.
      destruct H26 as (?&?&?&?&?). destruct H. 
      eapply subst_ql_fv_subst in H. 
      eexists x. split. split. 
      replace (length (restrictV (af && (negb af || u)) (V2' ++ V2))) with (length (G' ++ G)).
      eapply H. erewrite restrictV_length; eauto. rewrite app_length, app_length. lia.
      rewrite subst_ql_one_hit in H28. 
      replace (length (restrictV (af && (negb af || u)) (V2' ++ V2))) with (length (G' ++ G)).
      eauto. erewrite restrictV_length;eauto. rewrite app_length, app_length. lia.
      eexists. split. eauto. eauto. 
    }

    lia. lia. rewrite H5 in H19; auto. 2: eauto. destruct fr1,a1; eauto.
    intros. eapply H17. rewrite H5; auto. 
    intros. eapply H18. rewrite H5; auto. 

    erewrite restrictV_length with (G := G). 2: lia.
    rewrite <- subst_ql_qql. intros ? Q. subst pf. rewrite plift_diff.
    rewrite subst_ql_diff. rewrite plift_one.
    rewrite LV2. rewrite subst_ql_one_hit.
    bdestruct (x =? length (G'++G)).
    right. eauto. left. split. auto. 
    intuition. 

    remember ((e2 || a2) && af && (negb ((e2 || a2) && af) || u)) as b. destruct b; simpl; auto. rewrite map_app. auto.
    remember ((e2 || a2) && af && (negb ((e2 || a2) && af) || u)) as b. destruct b; simpl; auto. rewrite map_app. auto.
  }
  {
    (* weakening *)
    subst env.
    intros A HX VX S2X LHX SL2.
    assert (plift pf (length G)) as A'. subst pf.
    rewrite plift_diff, plift_one. split. eauto.
    rewrite app_length. simpl. unfoldq. lia.
    
    edestruct (WK A' HX VX S2X) as (u' & S2X' & v2 & ls2 & u2' & TVX2). lia. lia.
    
    exists true, S2X', v2, (if ((e2||a2)&&af&&u) then ls2 else qempty). 

    destruct TVX2 as (? & ? & ? & ? & ? & ? & ?).
    split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split.
    auto. lia.
    destruct a0; simpl; auto.
    intros ? ? ?. subst ls1'. rewrite H23 in H32. simpl in H32. 
    destruct af. destruct u. 2: { simpl in *. rewrite plift_empty in H32. auto. } 
    eapply H26. destruct H31. left. auto. inversion H31. auto. simpl in H32. rewrite plift_empty in H32. auto. 
    
    intros ? ? ?. rewrite H23 in H32. simpl in H32. 
    destruct af. destruct u. 2: { simpl in *. rewrite plift_empty in H32. auto. } 
    eapply H27. destruct H31. left. auto. inversion H31. auto. simpl in H32. rewrite plift_empty in H32. auto.
    
    {
      subst ls1'. rewrite H23. simpl.
      eapply valt_store_change. {
        destruct af; simpl. {
          destruct u; simpl. { 
            eapply valt_usable. eauto. destruct a0; simpl in *; auto. 
          } {
            assert (a0 = false). { 
              eapply H0 in A'. 2: { rewrite indexr_skips, indexr_head. eauto. simpl. lia. }
              unfold bsub in A'. destruct a0; intuition.
            } 
            subst a0. eapply aux1 in H26. 2: { left. auto. } 
            eapply aux1 in H27. 2: { left. auto. } subst ls1 ls2. 
            eapply valt_usable. eauto. eauto.
          }
      }{
        assert (a0 = false). { 
          eapply H0 in A'. 2: { rewrite indexr_skips, indexr_head. eauto. simpl. lia. }
          unfold bsub in A'. destruct a0; intuition.
        }
        subst a0. eapply aux1 in H26. 2: { left. auto. } 
        eapply aux1 in H27. 2: { left. auto. } subst ls1 ls2. 
        eapply valt_usable. eauto. eauto.
      }
    }{
        intros ??????. simpl. eapply H3.  eauto. auto.

        assert (length V1' = length G') as LV1'. destruct WFE as (?&?&?&?&?&?). 
        repeat rewrite app_length in *. simpl in *. lia.

        {
        rewrite H23.
        destruct af. {
          simpl. destruct u; simpl in *.
          eexists (length V1). split. simpl. rewrite plift_diff, plift_one.
          eapply hast_fv in W. subst p2. simpl in A. 
          split. rewrite LV1. rewrite app_length in *. simpl in *. congruence. 
          rewrite app_length. simpl. unfoldq. lia. 
          eexists. split. rewrite indexr_skips. rewrite indexr_head;eauto. simpl. lia. auto.
          rewrite plift_empty in H33. unfoldq; intuition.
        } { simpl. simpl in H33. rewrite plift_empty in H33. unfoldq; intuition. }
      }  
      { 
        assert (length V2' = length G') as LV2'. destruct WFE as (?&?&?&?&?&?). 
        repeat rewrite app_length in *. simpl in *. lia.
        rewrite H23 in *. simpl. 
        destruct af. {
          simpl in *. destruct u; simpl in *.
          destruct a0. 2: { eapply H29 in H34. repeat rewrite pif_false in H34. rewrite por_empty_l in H34. unfoldq; intuition. }  
          eapply H29 in H34. rewrite pif_false, por_empty_r in H34. 
          replace (VX ++ V2) with ([]++VX++V2) in H34. 2: simpl; auto.
          simpl. erewrite exp_locs_shift with (H2' := []) in H34. simpl in H34.
          eapply exp_locs_subst' with (t2 := tabs t) (v:=ls1) in H34. 
          eapply H34. simpl.
          rewrite plift_diff, plift_one. 
          eapply hast_fv in W. subst p2. simpl in A.
          split. rewrite LV2. rewrite app_length in *. simpl in *. congruence. 
          rewrite app_length. simpl. unfoldq. lia.
          rewrite plift_empty in H33. unfoldq; intuition. 
        } { intuition. }
      }
    }
    auto.
    auto.
  }
  
  { intros ? Q. rewrite H23 in *. 
    destruct af,u; simpl in *. 2:{ rewrite plift_empty in Q. unfoldq; intuition. } 
    2:{ rewrite plift_empty in Q. unfoldq; intuition. }
    2:{ rewrite plift_empty in Q. unfoldq; intuition. }  
    eapply H29 in Q. rewrite pif_false in Q. rewrite por_empty_r in Q.
    destruct a0. 2: { contradiction.  }
    simpl. rewrite pif_false. rewrite por_empty_r. auto.

  }   
  { intros ? Q. eapply H30. destruct Q. split; eauto. }
    
  }
  
  { intros ? Q. destruct e2. 2: contradiction. simpl in *.  eapply exp_locs_abs in Q. 
    destruct Q; eauto. subst ls1'. eapply H13. destruct af; simpl in *. destruct u; simpl. auto.
    replace (restrictV false V1' ++ qempty :: restrictV false V1) with (restrictV false (V1' ++ qempty :: V1)) in H24. 
    eapply aux2 in H24. unfoldq; intuition. unfold restrictV.  rewrite map_app. simpl. auto.
    replace (map (fun _ : ql => qempty) V1' ++ qempty :: map (fun _ : ql => qempty) V1)
        with (map (fun _ : ql => qempty) (V1' ++ qempty::V1)) in H24. eapply aux2; eauto.
    rewrite map_app. simpl. auto.    }
  { intros ? Q. rewrite H23 in *.  simpl in *. 
    destruct e2; try contradiction. simpl in *. 
    destruct af. {
      destruct u. {
        eapply exp_locs_abs in Q. destruct Q; eauto. eapply H14. rewrite splice_acc. 
        simpl. simpl in H24. auto. 
      } {
       simpl in H14. intuition.
      }
    }{
       destruct Q as (? & ? & ? & ? & ?).
       bdestruct (x0 =? length (restrictV false V2'++restrictV false V2)). {
         subst. rewrite indexr_head in H25. inversion H25. subst x1. eapply H16. auto.
       } {
         rewrite indexr_skip in H25. 
         replace (restrictV false V2'++ restrictV false V2)
            with (restrictV false (V2'++V2)) in H25. 
         apply indexr_var_some' in H25 as A. simpl in A. 
         replace (length (map (fun _ : ql => qempty) V2' ++ map (fun _ : ql => qempty) V2))
           with  (length (V2'++V2)) in A. 2: { rewrite app_length. rewrite app_length. rewrite map_length. rewrite map_length. lia.  }
         eapply indexr_var_some in A. destruct A. simpl in H25. eapply indexr_map in H28. rewrite map_app in H28.  
         erewrite H25 in H28. inversion H28. subst x1. rewrite plift_empty in H26. unfoldq; intuition.
         simpl. rewrite map_app. auto.
         simpl in *. lia. 
          
       }
    }
  }

  destruct H24 as (? & ? &? & ? & ? & ? & ? & ? & ?). intuition.
  eexists. eexists. eexists. eexists. eexists. eexists. eexists. eexists. 
  split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 8: split. 9: split. 10: split. 11: split. 
  12: split. 13: split. 14: split. 15: split. 16: split. 
  all: eauto. 
  erewrite restrictV_length with (G := V2) in H27. simpl in H27. erewrite restrictV_length with (G := V2') in H27.
  replace (1+length V2') with (S (length V2')). auto. all: auto.
  subst ux. simpl in *. rewrite H23 in *. simpl in *. subst uyv. auto.

  intros ? Q. eapply H36 in Q. rewrite pif_false in *. rewrite por_empty_l in *.
  destruct Q. 
  left. rewrite H23 in *. destruct a2; try contradiction. simpl in *.
  subst ls1'. destruct af. auto. unfold restrictV in *. rewrite map_app. simpl. 
  destruct u; simpl in *. auto.  auto. simpl in *. rewrite map_app. simpl. auto.  
  right. auto.

  intros ? Q. eapply H37 in Q. rewrite pif_false in *. rewrite por_empty_l in *.
  destruct Q. 
  left. rewrite H23 in *. destruct a2; try contradiction. simpl in *.
  erewrite restrictV_length with (G := V2) in H18. erewrite restrictV_length with (G := V2') in H18.
  destruct af. simpl in *. auto. destruct u; simpl in *. auto. unfold restrictV in *. rewrite map_app. simpl. auto.
  simpl in *. rewrite map_app. auto.  all: auto.
  right. auto.

  rewrite H23 in *. intros ? [? ?]. eapply H38. split; auto.
  intros ?. eapply H46. subst ls1'. destruct e2. 2: try contradiction.
  destruct af,u; simpl in *; auto; rewrite map_app; auto. 

  rewrite H23 in *. intros ? [? ?]. eapply H39. split; auto.
  intros ?. eapply H46. destruct e2. 2: try contradiction.
  destruct af,u; simpl in *; auto; rewrite map_app; auto. 
  rewrite map_length in H47. rewrite map_length in H47. auto. 
  rewrite map_length in H47. rewrite map_length in H47. auto.
  rewrite map_length in H47. rewrite map_length in H47. auto.  
     
 + (* mention *)  
    assert (e2 = false). destruct e2,a2; intuition.
    assert (a2 = false \/ uyv = false). destruct e2,a2,uy; intuition.
    subst e2.
    subst env.

    eapply exp_mentionable1; eauto.

    simpl in *.
    
    edestruct IHW with (M := M') (H1':=(vx1::H1')) (H2':=(vx2::H2')) (V1':=(restrictV false (lsx1 :: V1'))) (V2':=restrictV false (lsx2 :: V2')) (G':=((T1,fr1, a1)::G'))(u := false)
                       (V1 := (restrictV false V1))(V2 := (restrictV false V2))(H1 := H1)(ls1 := qempty)
    as (? & ? & ?). 
    simpl. eauto.
    all: eauto.
    
    2: { erewrite restrictV_length with (G := G). eauto. lia. }
    2: { erewrite restrictV_length. eauto. lia. }
    2: {
       rewrite plift_empty. unfoldq; intuition.  
      }
    
    2: { intros ? ? ?. eapply aux2. eauto. }
    3: { unfold bsub. auto. }
    {
      eapply envt_tighten. simpl. 
      rewrite <-map_app. rewrite <- map_app.
      eapply envt_extend with (p := (subst_ql (plift pf) (length V2)))(u := (negb (fr1||a1)) || false).
      
      destruct u.
      eapply envt_store_changeV''. eapply WFE.
      eauto. eauto.
      eapply envt_store_changeV'''. eauto.
      eauto. eauto.
      
      remember (fr1 || a1) as D. destruct D. 
      eapply valt_reset_locs. eapply valt_usable. eauto. 
      eauto. intuition.
      erewrite aux1 at 1. erewrite aux1 at 1.
      rewrite H8 in H19. eapply H19. auto.
      eapply H18. left. auto.
      eapply H17. left. auto.
      auto.
      rewrite plift_empty. unfoldq; intuition.
      rewrite plift_empty. unfoldq; intuition.
      
      rewrite restrictV_length with (G := V2); auto.

      {
      intros ? Q. subst pf. rewrite plift_diff, plift_one.
      rewrite subst_ql_diff.  rewrite LV2. rewrite subst_ql_one_hit.
      unfold subst_ql in *.
      bdestruct (x <? length V2). 
      left. split. bdestruct (x <? length G); intuition.
      intros ?. unfoldq. rewrite app_length in *. intuition.
      bdestruct (x =? length (G'++G)).
      right. unfoldq. auto.
      left. split. bdestruct (x <? length G); intuition. 
      intros ?. unfoldq. intuition.
      }
    }

    { (* weakening *)
    
    intros P'2 HX VX S2X LHX LS2X. edestruct WK with (S2X := S2X) as (u'' & S2'' & v2'' & ls2'' & ?). 
    subst pf. rewrite plift_diff, plift_one. 
    split. auto. rewrite app_length. simpl. unfoldq. lia.
    eapply LHX. destruct ST as (? & ? & ?). destruct H12 as (? & ? & ?). lia.
    
    exists (negb a0), S2'', v2'', qempty. 
    destruct H20 as (? & ? & ? & ? & ? & ? & ? & ?).
    split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split.
    all: eauto.
    
    destruct a0; simpl; auto.

    rewrite plift_empty. unfoldq; intuition.

    rewrite plift_empty. unfoldq; intuition.

    destruct a0. {
      simpl in *. subst u''.
      eapply valt_reset_locs.  
      eapply valt_store_reset.
      eapply valt_usable. eauto.
      intros ?. intuition.
      intros ?. intuition.
      intros ?. intuition.
  
      unfold st_len1 in *. simpl. lia.
      unfold st_len2. simpl. lia.
      intros ?. intuition.

   } {
     simpl in *. eapply aux1 in H24. 2: left; auto. 
     eapply aux1 in H25. 2: left; auto.
     subst ls1 ls2''. 
     eapply valt_store_reset. 
     eapply valt_usable. eauto.
     intros ?. auto.
     rewrite plift_empty. unfoldq; intuition.
     rewrite plift_empty. unfoldq; intuition.
     unfold st_len1 in *. simpl. lia.
     unfold st_len2. simpl. lia. 
    }
    
    rewrite plift_empty. unfoldq; intuition.

   }  
    {
    destruct H20 as (M'' & ?).
    exists x, x0, M''. rewrite restrictV_length with (G := V2) in H20; auto.
    rewrite restrictV_length with (G := (lsx2::V2')) in H20; auto.
    rewrite splice_acc. replace (length (lsx2::V2')) with (1+length V2') in H20.
    eauto.  simpl. lia.
    }
  }
  

  {
    remember WFE as WFE'. clear HeqWFE'. destruct WFE' as (LH1' & LH2' & LV1' & LV2' & TR & WFE').
    rewrite app_length in *.
    destruct u. {
      replace (a2||e2) with (e2||a2). 2: eauto with bool.
      remember (e2||a2) as D. destruct D. 
      intros. simpl in H3. assert (af = false). destruct af; simpl in H3; intuition.
      subst af. subst env.
      eapply t_abs in W.
      eapply hast_fv in W as W'''. simpl in W'''. rewrite app_length in W'''. simpl in W'''.
      simpl.
      eapply hast_fv1' in W as W'. destruct W'. eapply H4.
      eauto. 2: eauto. 2: eauto.

      
      assert (length (V2' ++ ls1 :: V2) = length (G'++ (T0, false, a0)::G)). { repeat rewrite app_length in *. simpl. lia. }
      split. 2: split. 
      repeat rewrite app_length in *. simpl in *. rewrite map_length. rewrite app_length. simpl. lia.
      eapply H4.
      
      intros. bdestruct (x =? (length G)).
      subst. rewrite indexr_skips in H5. 2: simpl; lia. rewrite indexr_head in H5.
      inversion H5. subst T fr a.
      exists qempty, ls1. split. 2: split. 3: split. 
      rewrite <-LV1. rewrite map_app.  simpl. rewrite indexr_skips. erewrite <-map_length. rewrite indexr_head. auto. simpl. 
      rewrite map_length. lia.
      rewrite <-LV2. rewrite indexr_skips. rewrite indexr_head. auto. simpl. lia. 
      rewrite plift_empty.  unfoldq; intuition. intros. eapply LX1. intuition.  

      edestruct WFE' with (x := if x <? length G then x else (x-1)) as (v1' & v2' & uv' & ls1' & ls2' &? &? &?).
      bdestruct (x <? length G). 
      rewrite indexr_skips. rewrite indexr_skips in H5. 2: simpl; lia. rewrite indexr_skip in H5. 2: lia.
      eauto. lia.
      erewrite <- indexr_splice1.
      bdestruct (x-1 <? length G). lia. 
      destruct x. lia. simpl. replace (x-0) with x. eauto. lia.
      exists qempty, ls2'. intuition.
      erewrite <- indexr_splice1 in H11.
      bdestruct (x <? length G). 
      bdestruct (x <? length V1). rewrite map_app. rewrite indexr_skips. 
      simpl. rewrite map_length. bdestruct (x =? length V1); intuition.
      rewrite indexr_skips in H11. rewrite indexr_skip in H11. eapply indexr_map in H11. eapply H11.
      lia. simpl. lia. rewrite map_length. simpl. lia. lia.
      bdestruct (x-1 <? length V1). lia. 
      replace (S (x-1)) with x in H11. 2:lia.
      eapply indexr_map in H11. eapply H11.

      bdestruct (x <? length G).
      rewrite indexr_skips in H10. rewrite indexr_skips. rewrite indexr_skip. auto.
      lia. simpl. lia. lia.
      erewrite <- indexr_splice1 in H10.
      bdestruct (x-1 <? length V2). lia.
      replace (S (x-1)) with x in H10. eauto. lia.

      rewrite plift_empty. unfoldq; intuition.
      rewrite pif_false. unfoldq; intuition.  
    } {
      
      intros. intros ? Q. 
      replace (a2||e2) with (e2||a2) in Q. 2: eauto with bool. 
      destruct (e2||a2); try contradiction.
      destruct af. 2: { simpl in Q. eapply aux2. eauto. }
      simpl in Q. eapply aux2 in Q. auto.
    }

  }
  
  {
    intros.
    unfold bsub in *.
    assert ((e2||a2)&&af = true -> u = false). {
      remember ((e2||a2)&&af) as b.
      destruct b; simpl in H3. destruct H3. intuition. auto.
      intuition.
    }
    remember ((e2||a2)&&af) as D. 
    destruct D. {
      intuition. subst u. 
      intros. intros ? Q. 
      replace (a2||e2) with (e2||a2) in Q. 2: eauto with bool. 
      destruct (e2||a2); try contradiction.
      eapply aux2. eauto.

    } {
      assert (e2||a2 = false \/ af = false). {
         destruct a2, e2, af; intuition.
      }
      destruct H5. {
        rewrite H5. rewrite pif_false. unfoldq; intuition.
      } {
        subst af. subst env.
        intros ? Q. destruct (e2||a2); try contradiction.
        eapply aux2. eauto.
      }
    }
  }
  - eapply exp_tnot; eauto. eapply IHW; eauto.
  - edestruct IHW1 as (S1' & S2' & M' & HEXP). eauto. 
    eapply envt_tighten. eauto. 
    rewrite plift_or. unfold subst_ql. unfoldq. intuition.
    bdestruct (x <? length V2); eauto.
    all: eauto.

    intros HP HX VX S2X LHX LS2. eapply WK. rewrite plift_or. left. auto.
    all: auto.

    unfold bsub in *. intros. eapply E. subst e1. simpl. auto.

    simpl in *. rewrite exp_locs_tbin in *. unfoldq. destruct e1, e2; simpl in *; intuition.
    simpl in *. rewrite exp_locs_tbin in *. unfoldq. destruct e1, e2; simpl in *; intuition.

    eapply exp_tbin; eauto.

    destruct HEXP as (?&?&?&?&?&?&?&?&?&?&?&?&?).
    assert (st_len1 M <= st_len1 M').
    destruct ST as (?&?&?). destruct s1 as (?&?&?). lia.
    assert (st_len2 M <= st_len2 M').
    destruct ST as (?&?&?). destruct s1 as (?&?&?). lia.

    eapply IHW2; eauto.
    eapply envt_store_change. eapply envt_tighten. eauto.

    rewrite plift_or. unfold subst_ql. unfoldq. intuition. bdestruct (x4 <? length V2); eauto.

    intros ?????. eauto. eauto. eauto. 

    intros A HX VX S2X LHX SL2.
    assert (plift (qor p1 p2) (length G)) as A'.
    rewrite plift_or. right. eauto.
    intros. 
    edestruct (WK A' HX VX S2X) as (u' & S2X' & v2 & ls2 & TVX2). lia. lia. 
    exists u', S2X', v2, ls2. intuition.
    eapply valt_store_change. eauto.
    intros ?????. simpl. eauto. eauto. eauto. eauto.
    unfold bsub in *. intros. eapply E. destruct e1, e2; intuition. 
    rewrite exp_locs_tbin in *. unfoldq. destruct e1,e2; simpl in *; intuition.
    rewrite exp_locs_tbin in *. unfoldq. destruct e1,e2; simpl in *; intuition.
    

  (* remaining subtyping cases *)
  - destruct fr; try eapply exp_sub_fresh; eauto; eapply IHW; eauto.
  - destruct a; try eapply exp_sub_cap; eauto; eapply IHW; eauto.
  - destruct e; try eapply exp_sub_eff; eauto; eapply IHW; eauto.
    unfold bsub. intuition.
    unfoldq. intuition.
    unfoldq. intuition.
Qed.



Lemma st_subst1 : forall u M t1 t2 G T1 T2 H1 H2 V1 V2 v1 ls1 p fr a a1 e,
    has_type ((T1,false,a1)::G) t2 T2 (qor p (qone (length G))) fr a e ->
    env_type M H1 H2 V1 V2 G u (plift p) ->
    psub (plift p) (pdom G) ->
    ((a1 = false \/ u = false) -> psub (plift ls1) pempty) ->
    ((u = false) -> psub (exp_locs (restrictV u V2) t1) pempty) ->
    (forall HX VX S2X,
      length HX = length VX ->
      st_len2 M <= length S2X ->
      exists uv S2' v2 ls2, (* via st_weaken *)
        (tevaln S2X (HX++H2) (splice_tm t1 (length H2) (length HX)) (S2') v2) /\
        length S2X <= length S2' /\
        (uv = negb a1 || u) /\
        ((a1 = false \/ uv = false) -> psub (plift ls1) pempty) /\
        ((a1 = false \/ uv = false) -> psub (plift ls2) pempty) /\
        val_type (st_len1 M, length S2', strel M) v1 v2 T1 (uv=true) ls1 ls2 /\
        psub (plift ls2)
          (por (pif a1 (exp_locs (restrictV u (VX++V2)) (splice_tm t1 (length V2) (length VX))))
             (pif false (pdiff (pdom (S2')) (pdom S2X)))) /\
        store_write S2X (S2') 
          (pif false (exp_locs (restrictV u (VX++V2)) (splice_tm t1 (length V2) (length VX))))
    ) ->
    bsub e u ->
    exp_type_eff M (v1::H1) H2 (ls1::V1) V2 t2 (subst_tm t2 (length V2) (splice_tm t1 (length V2) 0)) T2 u fr a e.
Proof. 
  intros. 
  remember H0 as WFE. clear HeqWFE.
  eapply st_subst' with (G':=[]) (H1':=[]) (H2':=[]) (V1':=[]) (V2':=[]); eauto. simpl. eauto.
  
  2,3,4,5: eapply WFE.

  simpl. 

  eapply envt_tighten. eauto. destruct WFE as (?&?&?&?&?&?).
  rewrite plift_or, plift_one, H11.
  eapply subst_ql_subst. eauto.
Qed.

Lemma xxx: forall (S1 S1': stor),
    S1 = S1' ++ S1 ->
    S1' = [].
Proof.
  intros. destruct S1'. eauto.
  assert (length S1 = length ((v :: S1') ++ S1)).
  congruence.
  simpl in H0. rewrite app_length in H0. lia. 
Qed.


(* unrestricted form: t1 allows mention of any capabilities.
   This no longer has the "p = empty" restriction in RT LR paper.
   (previously required by st_subst) *)

Lemma beta_equivalence: forall t1 t2 G T1 T2 pt1 pt2 fr a a1 e af,
  has_type ((T1,false,a1)::G) t2 T2 (qor pt1 (qone (length G))) fr a e -> 
  has_type G t1 T1 pt2 false a1 false -> 
  env_cap G pt1 af ->
  psub (plift pt1) (pdom G) ->
  psub (plift pt2) (pdom G) ->
  sem_type G (tapp (tabs t2) t1) (subst_tm t2 (length G) t1) T2 (por (plift pt1) (plift pt2)) fr a e.
Proof. 
  intros. rename H1 into ENV. rename H2 into XX1. rename H3 into XX2.  
  intros u E M H1 H2 V1 V2 WFE.
  assert (length H2 = length G) as LH2. destruct WFE as (?&?&?&?&?). auto.
  assert (length V2 = length G) as LV2. destruct WFE as (?&?&?&?&?). auto.

  intros SW ???? ST P1 P2. 
    
  assert (exp_type S1 S2 M H1 H2 V1 V2 (tabs t2) (tabs t2) (TFun T1 false a1 T2 fr a e) u p1 p2 false ((e||a)&&af) false) as C.
  eapply fundamental. econstructor. eauto. eauto.
  eapply envc_tighten. eauto. rewrite plift_or, plift_diff, plift_or, plift_one in *. unfoldq. intuition.
  unfold bsub. intuition.
  eapply envt_tighten. eauto. rewrite plift_or, plift_diff, plift_or, plift_one in *. unfoldq. intuition.
  
  eauto. eauto.  
  unfold psub, pif, pdom. intuition.
  unfold psub, pif, pdom. intuition. 
  
  destruct C as (S1' & S2' & MF' & vf1 & vf2 & uf & lsf1 & lsf2 & SC' & SW' & TF1 & TF2 & LS1 & LS2 & ST'& VF & UF1 & UF2 & LF1 & LF2 & VQF1 & VQF2 & ES1 & ES2 & EM).

  destruct (storew_prefix S1 S1') as (SDF1 & TFP1). eauto.
  destruct (storew_prefix S2 S2') as (SDF2 & TFP2). eauto.

  
  assert (SDF1 = [] /\ vf1 = (vabs H1 t2)). {
    destruct (TF1) as [n1 TF]. subst S1'. assert (S n1 > n1) as D. lia.
    specialize (TF (S n1) D). simpl in TF. inversion TF.
    split. eapply xxx. eauto. eauto. 
  }
  assert (SDF2 = [] /\ vf2 = (vabs H2 t2)). {
    destruct (TF2) as [n1 TF]. subst S2'. assert (S n1 > n1) as D. lia.
    specialize (TF (S n1) D). simpl in TF. inversion TF.
    split. eapply xxx. eauto. eauto. 
  }
  destruct H3, H4. subst SDF1 SDF2 vf1 vf2. simpl in TFP1, TFP2. 

  specialize st_weaken1 with (H2':=[]) (V2':=[])(M := M)(H1 := H1)(H2 := H2)(V1 := (restrictV u V1))(V2 := (restrictV u V2)) as A. 
  specialize (A _ _ _ _ _ _ H0).
  edestruct A with (u := u) as (SX1 & v1 & ls1 & LX1 & TX1 & QX1 & EX1 & WK2).
  simpl.

  eapply envt_tighten with (p := (por (plift pt1)(plift pt2))). 
  destruct u. { simpl. auto. }
  { eapply envt_store_changeV'''. eapply WFE. auto. auto.  }  
  unfoldq; intuition.
  erewrite restrictV_length; eauto.
  unfold bsub. intuition. auto. 

  2: { intros ? ?. eapply H3. }
  2: { intros ? ?. eapply H3. }
  rewrite pif_false. rewrite pif_false.
  eapply storet_tighten with (p1':=pempty) (p2':=pempty). eauto.
  unfoldq. intuition. unfoldq. intuition.
    
  intros. simpl. subst u. eapply aux2.

  destruct (storew_prefix S1 SX1) as (SDX1 & TFX1). eapply storew_widen. eauto.
  intros ? Q. intuition.


  specialize (st_subst1 u (st_pad (length (SDX1)) 0 M) t1 t2 G T1 T2 H1 H2 V1 V2 v1 ls1) as SUBST; eauto.
  edestruct (SUBST pt1 fr a a1 e H) with (S1:=(SDX1++S1)) (S2:=S2) as (S1'' & S2'' & M'' & REST). 
  eapply envt_store_change. eapply envt_tighten. eapply WFE. unfoldq. intuition.
  intros ?????. eauto. 
  unfold st_pad. unfold st_len1 at 2. simpl. lia.
  unfold st_pad. unfold st_len2 at 2. simpl. lia.
  eauto.
  
  intros ? ? Q. eapply QX1 in Q.
  rewrite pif_false in Q. rewrite por_empty_r in Q.
  destruct a1; try contradiction.
  simpl in *. destruct H3. inversion H3. subst. eapply aux2; eauto.

  {
  intros ? ? Q. subst u.
  eapply aux2. eauto.
  } 
  

  intros HX VX S2X LHX L2X.
  assert (length S2 <= length S2X).
  unfold st_pad in L2X. unfold st_len2 at 1 in L2X. simpl in L2X.
  destruct ST as (?&?&?). lia.
  edestruct (WK2 HX VX S2X) as (ux' & S2X' & v2 & ls2 & TX2 & LX2 & UX2 & UX2' & UX3' & VX2 & QX2 & EX2). 
  eauto. eauto. 
  intros ??. unfoldq. intuition. 
  exists ux', S2X', v2, ls2. split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split.
  eapply TX2. eauto.
  auto.
  auto.
  auto.

  simpl. unfold st_pad. unfold st_len1 at 1. simpl.
  replace (length SDX1 + st_len1 M) with (length SX1).
  2: { subst. rewrite app_length. destruct ST as (?&?&?). lia. }
  rewrite UX2 in VX2.
  eapply valt_usable. eauto. 
  intros. eauto.
  
  rewrite pif_false in *. rewrite por_empty_r in *. simpl in *. rewrite LV2. 
  destruct u. simpl. unfold restrictV in *.  rewrite <-LV2. auto. 
  destruct a1; try contradiction. intros ? ?. eapply aux2 in QX2; eauto. unfoldq; intuition. auto.

  rewrite pif_false in *. auto.
  auto.
  
  eapply sttyw_pad. eauto.

  
  eapply storet_pad with (SD2:=[]) in ST as ST1. 
  destruct ST1 as (L1 & L2 & L3). 
  split. 2: split.
  simpl. auto.
  rewrite L1. simpl. eauto.
  eapply L2.
  intros. simpl in H3. simpl in L3.
  destruct e. 2: { eapply L3. eauto. eapply H4. eapply H5. }
  simpl in H4, H5. 
  eapply L3. eauto. 2: eapply H5. 
  eapply H4.
  eauto. 
  intros ? Q. destruct e. 2: contradiction. eapply exp_locs_abs in Q. destruct Q.
  rewrite exp_locs_app in P1. left. eapply P1. left. eauto. 
  eapply QX1 in H3. destruct H3. destruct a1; try contradiction. left. eapply P1. 
  destruct u. 2: { eapply aux2 in H3; auto. unfoldq; intuition. } rewrite exp_locs_app. right. auto. intuition. intuition. 
     
  rewrite splice_zero. intros ? Q. left. eapply P2. rewrite <-LV2. eauto.


  destruct REST as (v1' & v2' & u' & ls1' & ls2' & ? & ? & TY1 & TY2 & ? & ? & ? & ? & ? & ? & LUY1 & LUY2 & QY1 & QY2 &  EYS1 & EYS2 & EYM).

  exists S1'', S2'', (st_step M M'' fr), v1', v2', u', ls1', ls2'. rewrite <- LV2.
  split. 2: split. 3: split. 4: split. 5: split. 6: split. 
  7: split. 8: split. 9: split. 10: split. 11: split. 12: split. 13: split. 14: split. 15: split. 16: split.
  + eapply stchain_step. eapply stchain_chain. 2: eauto. eapply stchain_pad.
  + destruct ST as (?&?&?).
    destruct ST' as (?&?&?).
    destruct H7 as (?&?&?).
    rewrite app_length in *. 
    eapply sttyw_step; eauto. lia. lia. 
  + destruct (TF1) as [n1 TF]. 
    destruct (TX1) as [n2 TX]. 
    destruct TY1 as [n3 TY]. 
    exists (S (n1+n2+n3)). intros.
    destruct n. lia. simpl. 
    rewrite TF. 2: lia. subst S1'. 
    rewrite TX. 2: lia. subst SX1.
    rewrite TY. 2: lia.
    eauto.
  + rewrite splice_zero in TY2. eauto.
  + rewrite app_length in *. lia.
  + rewrite app_length in *. lia.
  + eapply storet_tighten. eapply storet_step; eauto.
    rewrite por_assoc, pdiff_merge. intros ??. eauto. rewrite app_length. lia. lia.
    rewrite por_assoc, pdiff_merge. intros ??. eauto. eauto. eauto.  
  + destruct fr. simpl. eauto. simpl. intuition.
    destruct M'' as ((?&?)&?). unfold st_len1, st_len2. simpl. simpl in H12. congruence.
  + rewrite H9. destruct e, a, af, a1; intuition.
  + auto.
  + auto.
  + auto. 
  + rewrite exp_locs_app. intros ? Q. eapply QY1 in Q. destruct Q.
    2: { right. unfoldq. rewrite app_length in *. destruct fr; intuition. }
    destruct a. 2: contradiction.
    eapply exp_locs_abs in H11. destruct H11. left. left. auto.
    eapply QX1 in H11. rewrite pif_false in H11. rewrite por_empty_r in H11.
    destruct a1; try contradiction. left. right. destruct u. auto. eapply aux2 in H11. unfoldq; intuition. 
  + rewrite splice_zero in QY2. unfoldq. intuition. 
    + subst SX1. intros ? (Q1 & Q2). rewrite EX1. rewrite EYS1. eauto.
      * split. unfoldq. rewrite app_length. intuition. intros C. eapply Q2. clear Q2.
        destruct e. 2: contradiction. rewrite exp_locs_app. eapply exp_locs_abs in C.
        destruct C as [C|C]. left. eauto. eapply QX1 in C.
        destruct C as [C|C]. destruct a1. 2: contradiction. right. destruct u. auto. eapply aux2 in C. unfoldq; intuition.
        contradiction.
      * unfoldq. intuition.
    + intros ? (Q1 & Q2). rewrite EYS2. eauto. rewrite splice_zero. split; eauto. 
    + intuition. subst fr. eauto.
Qed.


End STLC.
