(*******************************************************************************
* Coq mechanization of the simply typed calculus with first-order mutable store (the λ$_{ae}$-calculus).
* - Syntactic definitions
* - Semantic definitions
* - Metatheory
*******************************************************************************)


(* Full safety for STLC *)


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

Definition pnat n := fun x' =>  x' < n.      (* numeric bound *)

Definition pdom {X} (H: list X) := fun x' =>  x' < (length H).      (* domain of a list *)

Definition pif (b:bool) p (x:nat) := if b then p x else False.      (* conditional *)

Definition psub (p1 p2: pl): Prop := forall x:nat, p1 x -> p2 x.    (* subset inclusion *)

Definition plift (b: ql): pl := fun x => b x = true.                (* reflect nat->bool set *)

(* ---------- language syntax ---------- *)

Definition id := nat.

Inductive ty : Type :=
  | TBool  : ty
  | TRef   : ty
  | TList  : ty -> ty
  | TFun   : ty -> bool -> bool -> ty -> bool -> bool -> bool -> ty
.

Inductive tm : Type :=
  | ttrue  : tm
  | tfalse : tm
  | tnil   : tm 
  | tvar   : id -> tm
  | tcons  : tm -> tm -> tm
  | tfold  : tm -> tm -> tm -> tm
  | tref   : tm -> tm
  | tget   : tm -> tm
  | tput   : tm -> tm -> tm
  | tapp   : tm -> tm -> tm
  | tabs   : tm -> tm
  | tnot   : tm -> tm
  | tbin   : tm -> tm -> tm
.

Inductive vl: Type :=
| vbool :  bool -> vl
| vref  :  id -> vl
| vlist :  list vl -> vl
| vabs  :  list vl -> tm -> vl 
.

Definition venv := list vl.
Definition tenv := list (ty * bool * bool).
Definition lenv := list ql.
Definition uenv := list bool.

Definition stor := list vl.

#[export] Hint Unfold venv : core.
#[export] Hint Unfold tenv : core.
#[export] Hint Unfold lenv : core.
#[export] Hint Unfold uenv : core.
#[export] Hint Unfold stor : core.


(* ---------- syntactic typing rules ---------- *)

Definition bsub b b' := b = true -> b' = true.

Definition env_cap (G:tenv) p a := forall x T1 fr1 a1,
    indexr x G = Some (T1, fr1, a1) -> p x = true -> bsub (fr1||a1) a.

Inductive stp: ty -> ty -> Prop := 
| s_bool : 
  stp TBool TBool 
| s_ref: 
  stp TRef TRef
| s_list: forall T1 T2, 
  stp T1 T2 ->
  stp (TList T1) (TList T2)
| s_fun: forall T1 fr1 a1 T2 fr2 a2 e2 T3 fr3 a3 T4 fr4 a4 e4, 
   stp T3 T1 ->
   stp T2 T4 ->
   bsub a3 a1 ->
   bsub fr3 fr1 ->
   bsub a2 a4 ->
   bsub fr2 fr4 ->
   bsub e2 e4 ->
   stp (TFun T1 fr1 a1 T2 fr2 a2 e2) (TFun T3 fr3 a3 T4 fr4 a4 e4)
.

Lemma stp_id: forall T,
  stp T T.
Proof.
  intros. induction T.
  eapply s_bool.
  eapply s_ref.
  eapply s_list. auto. 
  eapply s_fun; auto. 
  all: unfold bsub; auto.
Qed.

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
| t_nil: forall env T,
    has_type env tnil (TList T) qempty false false false
| t_cons: forall t1 t2 env T p1 p2 e1 e2 fr1 fr2 a1 a2,
    has_type env t1 T p1 fr1 a1 e1 ->
    has_type env t2 (TList T) p2 fr2 a2 e2 ->
    has_type env (tcons t1 t2) (TList T) (qor p1 p2) (fr1||fr2) (a1||a2) (e1 || e2)    
    (*
    Definition ex_fold_or (n:nat): tm :=
  tfold
    (tbin (tvar (n)) (tvar (S (n))))
    tfalse
    (tcons ttrue
      (tcons tfalse
        (tcons ttrue tnil))).
    *)
| t_fold: forall f z env T1 T2 al ez el p2 a2 e2 t p pz pl, 
    has_type ((T2, false, a2)::(T1, false, al)::env) f T2 p2 false a2 e2 ->
    has_type env z T2 pz false a2 ez  ->
    has_type env t (TList T1) pl false al el ->
    p = (qdiff p2 (qor (qone (S (length env)))(qone (length env)))) ->
    has_type env (tfold f z t) T2 (qor pz (qor pl p)) false a2 (ez||el||e2)
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
| t_sub_stp: forall env t T1 p fr1 a1 e1 T2 fr2 a2 e2,
    has_type env t T1 p fr1 a1 e1 ->
    stp T1 T2 ->
    bsub fr1 fr2 ->
    bsub a1 a2 ->
    bsub e1 e2 ->
    has_type env t T2 p fr2 a2 e2
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
  | ttrue       => qempty
  | tfalse      => qempty
  | tvar x      => qone x
  | tnil        => qempty
  | tcons t1 t2 => qor (fv n t1) (fv n t2) 
  | tfold f z t => (qor (qdiff (fv (S (S n)) f) (qor (qone (S n))(qone n))) (qor (fv n z) (fv n t)))
  | tref t      => fv n t
  | tget t      => fv n t
  | tput t1 t2  => qor (fv n t1) (fv n t2)
  | tapp t1 t2  => qor (fv n t1) (fv n t2)
  | tabs t      => qdiff (fv (S n) t) (qone n)
  | tnot t      => fv n t
  | tbin t1 t2  => qor (fv n t1) (fv n t2)
end.


(* ---------- operational semantics ---------- *)

Fixpoint teval(n: nat)(M:stor)(env: venv)(t: tm){struct n}: stor * option (option vl) :=
  match n with
    | 0 => (M, None)
    | S n =>
      match t with
        | ttrue      => (M, Some (Some (vbool true)))
        | tfalse     => (M, Some (Some (vbool false)))
        | tvar x     => (M, Some (indexr x env))
        | tnil        => (M, Some (Some (vlist nil)))
        | tcons ehd et1 =>
          match teval n M env ehd with
            | (M', None) => (M', None)
            | (M', Some None) => (M', Some None)
            | (M', Some (Some vh)) =>
              match teval n M' env et1 with
                | (M'', None) => (M'', None)
                | (M'', Some None) => (M'', Some None)
                | (M'', Some (Some (vbool _ )))    => (M'', Some None)
                | (M'', Some (Some (vref _)))      => (M'', Some None)
                | (M'', Some (Some (vabs _ _))) => (M'', Some None)
                | (M'', Some (Some (vlist vtl))) => (M'', Some (Some (vlist (vh::vtl))))
              end
          end
        | tfold ef ez els =>
          match teval n M env ez with 
            | (M', None) => (M', None)
            | (M', Some None) => (M', Some None)
            | (M', Some (Some vz)) => 
              match teval n M' env els with
                | (M'', None) => (M'', None)
                | (M'', Some None) => (M'', Some None)
                | (M'', Some (Some (vbool _))) => (M'', Some None)
                | (M'', Some (Some (vabs _ _))) => (M'', Some None)
                | (M'', Some (Some (vref _)))   => (M'', Some None)
                | (M'', Some (Some (vlist vls))) =>
                    let f := fun hd tl =>
                               match tl with
                               | (M'', None) => (M'', None)
                               | (M'', Some None) => (M'', Some None)
                               | (M'', Some (Some vtl)) =>
                                   teval n M'' (vtl::hd::env) ef
                               end in
                    fold_right f (M'', (Some (Some vz))) vls
              end 
          end 
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
            | (M', Some (Some (vlist _))) => (M', Some None)
            | (M', Some (Some (vabs _ _))) => (M', Some None)
            | (M', Some (Some (vref x))) => (M', Some (indexr x M'))
          end
        | tput er ex    =>
          match teval n M env er with
            | (M', None) => (M', None)
            | (M', Some None) => (M', Some None)
            | (M', Some (Some (vbool _))) => (M', Some None)
            | (M', Some (Some (vlist _))) => (M', Some None)
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
              | (M'', Some (Some (vlist _))) => (M'', Some None)
              | (M'', Some (Some (vref _))) => (M'', Some None)
              | (M'', Some (Some (vabs _ _))) => (M'', Some None)
              end
          | (M', Some (Some (vref _))) => (M', Some None)
          | (M', Some (Some (vlist _))) => (M', Some None)
          | (M', Some (Some (vabs _ _))) => (M', Some None)
          end    
        | tabs y     => (M, Some (Some (vabs env y)))
        | tapp ef ex =>
          match teval n M env ef with
            | (M', None) => (M', None)
            | (M', Some None) => (M', Some None)
            | (M', Some (Some (vbool _))) => (M', Some None)
            | (M', Some (Some (vlist _))) => (M', Some None)
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

Definition ex_fold_or (n:nat): tm :=
  tfold
    (tbin (tvar (n)) (tvar (S (n))))
    tfalse
    (tcons ttrue
      (tcons tfalse
        (tcons ttrue tnil))).

Lemma test: forall M n env M' v,
  teval n M env (ex_fold_or (length env)) = (M', Some (Some (v))) ->
  v = (vbool false).
Proof.
  intros. destruct n. simpl in *. inversion H. 
  simpl in H. 
  remember (teval n M env tfalse) as Ht. 
  symmetry in HeqHt. destruct Ht as [nt [rt|]]. 2: { inversion H. }
  destruct rt. 2: { inversion H. }
  remember (teval n nt env (tcons ttrue (tcons tfalse (tcons ttrue tnil)))) as Htcons. 
  symmetry in HeqHtcons. destruct Htcons as [ntcons [rtcons|]]. 2: { inversion H. }
  destruct rtcons. 2: { inversion H. }
  destruct v1. inversion H. inversion H. 2: { inversion H. }
  destruct n. simpl in *. inversion HeqHt. simpl in HeqHt. inversion HeqHt. subst v0 nt.   
  simpl in HeqHtcons. 
  remember (teval n M env ttrue) as Ht2. 
  symmetry in HeqHt2. destruct Ht2 as [nt2 [rt2|]]. 2: { inversion HeqHtcons. }
  destruct rt2. 2: { inversion HeqHtcons. }
  destruct n. simpl in *. inversion HeqHt2. simpl in HeqHt2. inversion HeqHt2. subst v0 nt2. 
  simpl in HeqHtcons. 
  remember (teval n M env tfalse) as Ht3. symmetry in HeqHt3. destruct Ht3 as [nt3 [rt3|]]. 2: { inversion HeqHtcons. }
  destruct n. simpl in HeqHt3. inversion HeqHt3. simpl in HeqHt3. inversion HeqHt3. subst rt3 nt3.
  simpl in HeqHtcons. 
  remember (teval n M env ttrue) as Ht4. symmetry in HeqHt4. destruct Ht4 as [nt4 [rt4|]]. 2: { inversion HeqHtcons. }
  destruct n. simpl in HeqHt4. inversion HeqHt4. simpl in HeqHt4. inversion HeqHt4. subst rt4 nt4. 
  simpl in HeqHtcons. inversion HeqHtcons. subst ntcons l.
  cbn [fold_right] in H.
  simpl in H.
  bdestruct (length env =? S (length env)). lia. 
  bdestruct (length env =? length env). 2: { lia. } 
  simpl in H. congruence.
Qed.
  


(* ---------- LR definitions  ---------- *)

Fixpoint vars_locs_fix (V: lenv) (q: ql) (l: nat): bool :=
  match V with
  | ls :: V => (q (length V) && ls l) || vars_locs_fix V q l
  | [] => false
  end.


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
  | vlist vs1, vlist vs2, TList T1 =>
      Forall2 (fun v1 v2 => val_type M v1 v2 T1 (u) ls1 ls2) vs1 vs2
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
    u = (negb a || uv) /\ (* top-level: uv = true --> use, false --> mention *)
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
  True /\ (* length W = length G /\ *)
  forall x T fr a,
    indexr x G = Some (T,fr,a) ->
    exists v1 v2 u ls1 ls2,
      indexr x H1 = Some v1 /\
      indexr x H2 = Some v2 /\
      ((fr||a = false \/ u0=true) -> indexr x V1 = Some ls1) /\
      ((fr||a = false \/ u0=true) -> indexr x V2 = Some ls2) /\
      True /\ (* indexr x W = Some u /\ *)
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

Lemma pif_false: forall p,
  pif false p = pempty.
Proof.
  intros. eapply functional_extensionality. intros. simpl. auto.
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

Lemma pdiff_empty_r: forall (p: pl),
    pdiff p pempty = p.
Proof.
  intros. eapply functional_extensionality.
  intros. eapply propositional_extensionality.
  unfoldq. intuition. 
Qed.

Lemma por_comm: forall (p1 p2: pl),
    (por p1 p2) = (por p2 p1).
Proof.
  intros. eapply functional_extensionality.
  intros. eapply propositional_extensionality.
  unfoldq. intuition. 
Qed.

Lemma por_same: forall (p1: pl),
    (por p1 p1) = p1.
Proof.
  intros. eapply functional_extensionality.
  intros. eapply propositional_extensionality.
  unfoldq. intuition. 
Qed.


Lemma hast_fv: forall G t T p fr a e,
    has_type G t T p fr a e -> p = fv (length G) t.
Proof.
  intros. induction H; simpl; eauto.
  - rewrite IHhas_type1, IHhas_type2. eauto.
  - rewrite <-IHhas_type2, <-IHhas_type3. subst pz pl0.
    assert (p = (qdiff (fv (S (S (length env))) f) (qor (qone (S (length env))) (qone (length env))))). {
      rewrite H2. rewrite IHhas_type1. simpl. auto.
    }
    rewrite <-H3. subst p. 
    rewrite plift_qual_eq. repeat rewrite plift_or.  repeat rewrite plift_diff.
    repeat rewrite plift_or. repeat rewrite plift_one.
    eapply functional_extensionality. intros. eapply propositional_extensionality. split; intros.
    unfoldq; intuition. unfoldq; intuition.
  - rewrite IHhas_type1, IHhas_type2. eauto.
  - rewrite IHhas_type1. rewrite IHhas_type2. eauto.
  - rewrite H0, IHhas_type. simpl. eauto.
  - rewrite IHhas_type1, IHhas_type2. eauto.
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

Lemma vars_locs_empty: forall H,
  vars_locs H pempty = pempty.
Proof.
  intros. eapply functional_extensionality. intros.
  eapply propositional_extensionality. split; intros.
  destruct H0. unfoldq; intuition. unfoldq; intuition.
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

Lemma exp_locs_nil: forall H,
    exp_locs H tnil = pempty.
Proof.
  intros. unfold exp_locs. simpl.
  rewrite plift_empty. rewrite vars_locs_empty. auto.
Qed.

Lemma exp_locs_cons: forall H t1 t2,
    exp_locs H (tcons t1 t2) = por (exp_locs H t1) (exp_locs H t2).
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

Lemma exp_locs_tfold: forall H f z t v1 v2,
   psub (exp_locs (v1::v2::H) f)
        (por (exp_locs H (tfold f z t)) (por (plift v1) (plift v2))).
Proof.
  intros. intros ? Q. unfold exp_locs in *. simpl in *.
  destruct Q as (? & ? & ? &? & ?). 
  bdestruct (x0 =? (length (v2::H))). 
  subst x0. rewrite indexr_head in H1. inversion H1. right. left. auto.
  rewrite indexr_skip in H1. 2: lia.
  bdestruct (x0 =? length H). 
  subst x0. rewrite indexr_head in H1. inversion H1. right. right. auto.
  rewrite indexr_skip in H1. 2: lia.
  left. rewrite plift_or, plift_diff. repeat rewrite plift_or. rewrite plift_one.
  eexists. split. left. split. eauto. rewrite plift_one. simpl in *. unfoldq; intuition.
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
  - rewrite plift_one. eapply indexr_var_some' in H. unfoldq. auto with *.
  - rewrite plift_empty. unfoldq. auto with *.
  - rewrite plift_or. unfoldq. intuition.
  - rewrite plift_or. rewrite plift_or.  unfoldq. intuition.
    subst p. rewrite plift_diff, plift_or, plift_one, plift_one in H3.
    unfoldq; intuition. eapply IHhas_type1 in H2. simpl in H2. lia.
  - rewrite plift_or. unfoldq. intuition.
  - rewrite plift_or. unfoldq. intuition.
  - subst pf. rewrite plift_diff, plift_one.
    unfoldq. intuition. eapply IHhas_type in H2.
    simpl in H2. lia. 
  - rewrite plift_or. unfoldq. intuition.
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


Lemma envc_extend2: forall G p a a1 fr1 T1 a2 fr2 T2,
    env_cap G p a ->
    bsub (fr1||a1) a ->
    bsub (fr2||a2) a ->
    env_cap ((T2,fr2,a2)::(T1,fr1,a1)::G)
      (qor (qor p (qone (length G))) (qone (S (length G)))) a.
Proof.
  intros G p a a1 fr1 T1 a2 fr2 T2 EC B1 B2.
  pose proof (envc_extend G p a a1 fr1 T1 EC B1) as EC1.
  replace (S (length G)) with (length ((T1,fr1,a1)::G)) by reflexivity.
  eapply envc_extend; eauto.
Qed.

Definition env_sub (G' G: tenv) :=
  length G' = length G /\
  (forall x T fr a, indexr x G = Some (T,fr,a) -> exists fr' a', indexr x G' = Some (T,fr',a') /\ bsub fr' fr /\ bsub a' a).

Lemma hast_narrow_strengthen: forall G T t1 p fr a e,
  has_type G t1 T p fr a e ->
  forall G' af,
    env_sub G' G ->
    env_cap G' p af ->
  has_type G' t1 T p fr (a&&af) (e&&af).
Proof.
  intros. revert G' af H0 H1. induction H; intros.
  - eauto.
  - eauto. 
  - simpl. edestruct H0 as (fr' & a' &?&?&?). eauto.
    eapply H1 in H2 as H2'. 
    destruct ((fr || a) && af) eqn:E1. eapply t_sub_cap. 
    eapply t_var. eauto.
    replace false with (a'||x0) at 2. eapply t_var. eauto.
    assert (bsub (a' || x0) af). eapply H2'. unfold qone. rewrite Nat.eqb_refl. eauto. 
    destruct fr,a,af,a',x0; simpl in *; intuition.
  - eapply t_nil. 
  - replace ((a1||a2)&&af) with (a1&&af || a2&&af). 2: destruct a1,a2,af; auto. 
    replace ((e1||e2)&&af) with (e1&&af || e2&&af). 2: destruct e1,e2,af; auto. 
    eapply t_cons.
    eapply IHhas_type1; eauto. eapply envc_tighten. eauto. rewrite plift_or. unfoldq. intuition.
    eapply IHhas_type2; eauto. eapply envc_tighten. eauto. rewrite plift_or. unfoldq. intuition. 
  - replace ((ez || el || e2) && af) with (ez&&af || el&&af || e2&&af). 2: destruct ez,el,e2,af; auto. 
    eapply t_fold.
    + eapply IHhas_type1.
      * destruct H3 as (HL&HX). split. simpl. eauto. intros. 
        bdestruct (x =? length ((T1, false, al)::env)).
        subst x. erewrite indexr_head in H3. inversion H3. subst T2 fr a2.
        eexists false, (a&&af). split. 2: split.
        replace (length ((T1, false, al)::env)) with (length ((T1, false, al&&af)::G')). 2: simpl; lia.
        erewrite indexr_head. eauto. unfold bsub. eauto. unfold bsub. destruct a; eauto.
        erewrite indexr_skip in H3.
        bdestruct (x =? length env).
        subst x. erewrite indexr_head in H3. inversion H3. subst T1 fr a.
        eexists false, (al&&af). split. 2: split. rewrite <-HL. 
        erewrite indexr_skip, indexr_head. eauto. eauto. unfold bsub. eauto. unfold bsub. destruct al; eauto.
        erewrite indexr_skip in H3. edestruct HX as (fr' & a' & ? & ? & ?). eauto.
        eexists fr', a'. split. 2: split. erewrite indexr_skip, indexr_skip; eauto. lia. simpl in *. lia.  eauto. eauto. eauto. eauto.
      * intros ???????.
        bdestruct (x =? length ((T1, false, al&&af)::G')).
        subst x. erewrite indexr_head in H5. inversion H5. subst T0 fr1 a1.
        destruct a2,af; eauto.
        bdestruct (x =? length G').
        subst x. erewrite indexr_skip, indexr_head in H5. inversion H5. subst T0 fr1 a1.
        destruct al,af; eauto. eauto.
        eapply H4. erewrite indexr_skip, indexr_skip in H5. eauto. eauto. eauto. 2: eauto.
        assert (plift p x). subst p. rewrite plift_diff, plift_or, plift_one, plift_one.
        destruct H3. 
        unfoldq. simpl in *. split. eauto. intuition.
        unfold qor. rewrite H10. eauto with bool.
    + eapply IHhas_type2. eauto. eapply envc_tighten. eauto. rewrite plift_or, plift_or. unfoldq. intuition.
    + eapply IHhas_type3. eauto. eapply envc_tighten. eauto. rewrite plift_or, plift_or. unfoldq. intuition.
    + destruct H3. congruence. 
  - eapply t_ref. eauto.
  - simpl. replace ((e||a)&&af) with (e&&af || a&&af). 2: destruct e,a,af; auto. 
    eapply t_get. eauto.
  - simpl. replace ((e1||e2||a1)&&af) with (e1&&af || e2&&af || a1&&af). 2: destruct e1,e2,a1,af; auto.
    eapply t_put.
    eapply IHhas_type1. eauto. eapply envc_tighten. eauto. rewrite plift_or. unfoldq. intuition.
    eapply IHhas_type2. eauto. eapply envc_tighten. eauto. rewrite plift_or. unfoldq. intuition. 
  - simpl. specialize t_app. intros.
    specialize H3 with (af:=af&&af0).
    specialize H3 with (ef:=ef&&af0).
    specialize H3 with (a1:=a1&&af0).
    specialize H3 with (e1:=e1&&af0).
    assert (has_type G' f (TFun T1 fr1 (a1&&af0) T2 fr2 a2 e2) p1 frf
              (af && af0) (ef && af0)) as HX. {
      eapply t_sub_stp. eapply IHhas_type1. eauto.
      eapply envc_tighten. eauto. rewrite plift_or. unfoldq. intuition.
      eapply s_fun. 1,2: apply stp_id. all: unfold bsub in *; auto.
      destruct a1; eauto. 
    }
    eapply H3 in HX as HXX.
    2: { destruct af0. eapply IHhas_type2. eauto.
         eapply envc_tighten. eauto. rewrite plift_or. unfoldq. intuition. 
         eapply IHhas_type2. eauto.
         eapply envc_tighten. eauto. rewrite plift_or. unfoldq. intuition. }
    replace ((af || a1) && a2 && af0) with ((af && af0 || a1 && af0) && a2).
    2: destruct af0,a1,a2,af; simpl; eauto.
    replace ((e1 || ef || (af || a1) && e2) && af0) with (e1 && af0 || ef && af0 || (af && af0 || a1 && af0) && e2).
    2: destruct e1,e2,ef,af0,a1,a2,af; simpl; eauto.
    eapply HXX.
  - assert (env_cap G' pf (af && af0)) as E12. intros ??????.
    eapply indexr_var_some' in H4 as IX. destruct H2. rewrite H2 in IX.
    eapply indexr_var_some in IX. destruct IX as (((?&?)&?)&?).    
    eapply H1 in H7 as E1; eauto.
    eapply H6 in H7 as E2; eauto.
    destruct E2 as (?&?&?&?&?). rewrite H4 in H8. inversion H8. subst t0 x0 x1. clear H8.
    eapply H3 in H4 as E3.
    unfold bsub in *. intuition. rewrite H11, H13. eauto.
    destruct fr0. rewrite H9. eauto. eauto. rewrite H10. destruct b; eauto. eauto.
    assert (has_type ((T1, fr1, a1) :: G') t T2 p2 fr2 (a2&&true) (e2&&true)). {
      eapply IHhas_type.
      destruct H2. split. simpl. eauto. intros.
      bdestruct (x =? length env).
      subst x. rewrite indexr_head in H5. inversion H5. subst T fr a.
      exists fr1, a1. rewrite <-H2, indexr_head; eauto. unfold bsub. intuition.
      rewrite indexr_skip in H5. rewrite indexr_skip. eapply H4; eauto. lia. eauto.
      intros ???????. eauto.
    }
    replace (a2 && true) with a2 in H4. 2: destruct a2; eauto.
    replace (e2 && true) with e2 in H4. 2: destruct e2; eauto. 
    eapply t_abs in H4. 2: { destruct H2. rewrite e. eapply H0. } 2: eapply E12.
    replace ((e2 || a2) && (af && af0)) with ((e2 || a2) && af && af0) in H4.
    2: destruct e2,a2,af0,af; simpl; eauto.
    simpl. eauto.
  - eapply t_not. eauto.
  - simpl. replace ((e1 || e2) && af) with (e1&&af || e2&&af).
    eapply t_bin.
    eapply IHhas_type1. eauto. eapply envc_tighten. eauto. rewrite plift_or. unfoldq. intuition.
    eapply IHhas_type2. eauto. eapply envc_tighten. eauto. rewrite plift_or. unfoldq. intuition. 
    destruct e1,e2,a1,af; eauto.
  - eauto.
  - destruct af. eapply t_sub_cap. eauto. eapply IHhas_type in H0.
    destruct a; eauto. eauto. 
  - destruct af. eapply t_sub_eff. eauto. eapply IHhas_type in H0.
    destruct e; eauto. eauto.
  - destruct af. eapply t_sub_stp. eapply IHhas_type. eauto. eauto. eauto. 
    all: unfold bsub in *. eauto. destruct a1,a2; simpl; auto. destruct e1,e2; simpl; auto.
    eapply IHhas_type in H5. 2: eauto. eapply t_sub_stp;eauto.
    all: unfold bsub. destruct a1; intuition. destruct e1; intuition.
Qed.

Lemma hast_narrow: forall G T t1 p fr a e,
  has_type G t1 T p fr a e ->
  forall G', env_sub G' G ->
  has_type G' t1 T p fr a e.
Proof.
  intros.
  replace a with (a&&true). 2: eauto with bool.
  replace e with (e&&true). 2: eauto with bool.
  eapply hast_narrow_strengthen. eauto. eauto. intros ???????. eauto.
Qed.

Lemma hast_strengthen: forall G T t1 p fr a e af,
  has_type G t1 T p fr a e ->
  env_cap G p af ->
  has_type G t1 T p fr (a&&af) (e&&af).
Proof.
  intros.
  eapply hast_narrow_strengthen; eauto. split. eauto.
  intros. unfold bsub. eexists _,_. split. 2: split. all: eauto.
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

Lemma Forall_store_change: forall T M M' L1 L2 u ls1 ls2 ux lsx1 lsx2,
  (forall v1 v2, val_type M v1 v2 T u ls1 ls2 -> val_type M' v1 v2 T u ls1 ls2) ->
  Forall2 (fun v1 v2 => val_type M v1 v2 T u ls1 ls2) L1 L2 -> 
  (ux -> st_chain_partial M M' (plift lsx1) (plift lsx2)) ->
  st_len1 M <= st_len1 M' -> 
  st_len2 M <= st_len2 M' ->
  Forall2 (fun v1 v2 => val_type M' v1 v2 T u ls1 ls2) L1 L2. 
Proof.
  intros T M M' L1 L2 u ls1 ls2 ux lsx1 lsx2 HT H HC HL1 HL2.
  induction H.
  - constructor.
  - constructor. eapply HT. eauto. eauto. 
Qed.

Lemma valt_store_change: forall T M M' vx1 vx2 ux lsx1 lsx2,
    val_type M vx1 vx2 T ux lsx1 lsx2 ->
    (ux -> st_chain_partial M M' (plift lsx1) (plift lsx2)) ->
    st_len1 M <= st_len1 M' -> 
    st_len2 M <= st_len2 M' ->
    val_type M' vx1 vx2 T ux lsx1 lsx2.
Proof.
  intros T.
  induction T; intros M M' vx1 vx2 ux lsx1 lsx2 HVT HC HL1 HL2;
  destruct vx1, vx2; simpl in HVT; try contradiction.
  - simpl. eauto.
  - simpl. intros. intuition. 
  - simpl. eapply Forall_store_change. intros ? ? ?. eapply IHT. eauto. all: eauto. 
  - simpl. intros.
    destruct (HVT S1' S2' M'0 p1 p2 vx1 vx2 ux0 lsx0 lsx3 uy uyv) as (S1'' & S2'' & M'' &?&?&?&?&?); eauto.
    intros ??????. eapply H. eauto. auto. eapply HC. eauto. eauto. eauto. eauto. eauto. eauto.
    lia. lia.
    eexists S1'', S2'', M'', _,_,_,_. intuition. 5: eauto. all: eauto.
Qed.

Lemma Forall_usable: forall T M L1 L2 u u' ls1 ls2,
  (forall v1 v2, val_type M v1 v2 T u ls1 ls2 -> val_type M v1 v2 T u' ls1 ls2) ->
  Forall2 (fun v1 v2 => val_type M v1 v2 T u ls1 ls2) L1 L2 -> 
  (u' -> u) ->
  Forall2 (fun v1 v2 => val_type M v1 v2 T u' ls1 ls2) L1 L2.
Proof.
  intros T M L1 L2 u u' ls1 ls2 HT H HU.
  induction H.
  - constructor.
  - constructor. eapply HT. eauto. eauto. 
Qed.

Lemma valt_usable: forall T M vx1 vx2 ux (ux': Prop) lsx1 lsx2,
    val_type M vx1 vx2 T ux lsx1 lsx2 ->
    (ux' -> ux) ->
    val_type M vx1 vx2 T ux' lsx1 lsx2.
Proof.
  intros T. 
  induction T; intros M vx1 vx2 ux ux' lsx1 lsx2 HVT HUX; destruct vx1, vx2; simpl in HVT; try contradiction.
  - simpl. eauto.
  - simpl. intuition.
  - simpl. eapply Forall_usable. intros ? ? ?. eapply IHT. eauto. all: eauto. 
  - simpl. intros.
    destruct (HVT S1' S2' M' p1 p2 vx1 vx2 ux0 lsx0 lsx3 uy uyv) as (S1'' & S2'' & M'' &?&?&?&?&?); eauto.
Qed.

Lemma Forall_reset_locs: forall T M L1 L2 u ls1 ls2,
  (forall v1 v2, val_type M v1 v2 T u ls1 ls2 -> val_type M v1 v2 T u qempty qempty) ->
  Forall2 (fun v1 v2 => val_type M v1 v2 T u ls1 ls2) L1 L2 -> 
  Forall2 (fun v1 v2 => val_type M v1 v2 T u qempty qempty) L1 L2. 
Proof.
  intros T M L1 L2 u ls1 ls2 HT H.
  induction H.
  - constructor.
  - constructor. eapply HT. eauto. eauto. 
Qed.


Lemma valt_reset_locs: forall T M vx1 vx2 ux lsx1 lsx2,
    val_type M vx1 vx2 T ux lsx1 lsx2 ->
    (ux -> False) ->
    val_type M vx1 vx2 T ux qempty qempty.
Proof.
  intros T. induction T; intros M vx1 vx2 ux lsx1 lsx2 HVT HUX; destruct vx1, vx2; simpl in *; try contradiction.
  - simpl. eauto.
  - eapply Forall_reset_locs. intros ???. eapply IHT. eauto. eauto. eauto.
  - simpl. intros.
    remember (b3||uy&&b2) as D. destruct D.
    + destruct (HVT S1' S2' M' p1 p2 vx1 vx2 ux0 lsx0 lsx3 uy uyv) as (S1'' & S2'' & M'' & vy1 & vy2 & lsy1 & lsy2 &?); eauto.
      intros. intuition.
      intros ? Q. destruct b3; intuition.
      intros ? Q. destruct b3; intuition.

      eexists S1'', S2'', M'', vy1, vy2, lsy1, lsy2.
      intuition.
    + assert (b3=false). destruct b3; intuition.
      assert (uy && b2=false). destruct b2,uy; simpl in *; intuition.
      assert (uy = false \/ b2 = false). destruct b2,uy; intuition.
      destruct H16.
      * (* uy = true *)
        destruct (HVT S1' S2' M' p1 p2 vx1 vx2 ux0 lsx0 lsx3 uy uyv) as (S1'' & S2'' & M'' & vy1 & vy2 & lsy1 & lsy2 &?); eauto.
        intros. rewrite H14, H15 in H17. inversion H17. 
        intros ? Q. destruct b3; intuition.
        intros ? Q. destruct b3; intuition.
        eexists S1'', S2'', M'', vy1, vy2, lsy1, lsy2.
        intuition.
        intros ? Q. eapply H31 in Q. contradiction.
        intros ? Q. eapply H24 in Q. contradiction.
        intros ? Q. destruct Q. destruct b3; intuition.
        eapply H29. split; intuition. 
        intros ? Q. destruct Q. destruct b3; intuition.
        eapply H30. split; intuition.
      * (* b3 = false  <--  a2 = false *)
        destruct (HVT S1' S2' M' p1 p2 vx1 vx2 ux0 lsx0 lsx3 uy uyv) as (S1'' & S2'' & M'' & vy1 & vy2 & lsy1 & lsy2 &?); eauto.
        intros. rewrite H14, H15 in H17. inversion H17. 
        intros ? Q. destruct b3; intuition.
        intros ? Q. destruct b3; intuition.
        eexists S1'', S2'', M'', vy1, vy2, lsy1, lsy2.
        intuition.
        intros ? Q. eapply H27 in Q. subst b2. intuition.
        intros ? Q. eapply H28 in Q. subst b2. intuition. 
        intros ? Q. destruct Q. destruct b3; intuition.
        eapply H29. split; intuition. 
        intros ? Q. destruct Q. destruct b3; intuition.
        eapply H30. split; intuition.
Qed.

Lemma valt_store_reset: forall T M M' vx1 vx2 ux lsx1 lsx2,
    val_type M vx1 vx2 T ux lsx1 lsx2 ->
    (ux -> psub (plift lsx1) pempty) ->
    (ux -> psub (plift lsx2) pempty) ->
    st_len1 M <= st_len1 M' -> 
    st_len2 M <= st_len2 M' ->    
    val_type M' vx1 vx2 T ux lsx1 lsx2.
Proof.
  intros T. induction T; intros M M' vx1 vx2 ux lsx1 lsx2 HVT UX1 UX2 L1 L2; destruct vx1, vx2; simpl in HVT; try contradiction.
  - simpl. eauto.
  - simpl. intuition. eapply H2 in H0. contradiction.
  - induction HVT.
    -- constructor.
    -- constructor. eapply IHT; eauto.  eauto.
  - simpl. intros.
    destruct (HVT S1' S2' M'0 p1 p2 vx1 vx2 ux0 lsx0 lsx3 uy uyv) as (S1'' & S2'' & M'' &?&?&?); eauto.
    intros ??????. eapply H0 in H14. eapply UX1 in H16; auto.  contradiction. lia. lia. 

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
  - induction H.
    -- constructor.
    -- constructor. eapply IHT; eauto. auto.    
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

Lemma exp_sub_fresh': forall S1 S2 M H1 H2 V1 V2 t1 t2 T u p1 p2 fr fr' a e,
    stty_wellformed M ->
    store_type S1 S2 M p1 p2 -> 
    bsub fr fr' ->
    exp_type S1 S2 M H1 H2 V1 V2 t1 t2 T u p1 p2 fr a e ->
    exp_type S1 S2 M H1 H2 V1 V2 t1 t2 T u p1 p2 fr' a e.
Proof.
  intros ?????????????????? SW ST HX. destruct HX as (S1' & S2' & M' & REST). 
  exists S1', S2', M'. 
  unfold bsub in *. 
  destruct fr, fr'; intuition.
  eapply exp_sub_fresh1; eauto. 
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

Lemma exp_sub_cap': forall S1 S2 M H1 H2 V1 V2 t1 t2 T u p1 p2 fr a e a',
    stty_wellformed M ->
    store_type S1 S2 M p1 p2 -> 
    bsub a a' ->
    exp_type S1 S2 M H1 H2 V1 V2 t1 t2 T u p1 p2 fr a e ->
    exp_type S1 S2 M H1 H2 V1 V2 t1 t2 T u p1 p2 fr a' e.
Proof.
  intros ?????????????????? SW ST HX. destruct HX as (S1' & S2' & M' & REST). 
  exists S1', S2', M'. 
  unfold bsub in *. destruct a, a'; intuition.
  eapply exp_sub_cap1; eauto. 
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

Lemma exp_nil: forall S1 S2 M H1 H2 V1 V2 p1 p2 T uv,
    stty_wellformed M ->
    store_type S1 S2 M p1 p2 ->
    exp_type S1 S2 M H1 H2 V1 V2 tnil tnil (TList T) uv p1 p2 false false false.
Proof.
    intros ??????????? SW ST.
    exists S1, S2, M, (vlist nil), (vlist nil), true, qempty, qempty.
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
    - simpl. auto.
    - eauto.
    - intros. rewrite plift_empty. unfoldq. intuition.
    - unfoldq. intuition.
    - unfoldq. intuition.
    - unfoldq. intuition.
    - eapply storew_refl.
    - eapply storew_refl. 
    - eauto.
Qed.

Lemma psub_empty: forall p,
  psub p pempty -> p = pempty.
Proof.
  intros. eapply functional_extensionality. intros x. eapply propositional_extensionality. split; intros Q.
  - eapply H in Q. unfold pempty in Q. contradiction.
  - unfold pempty. contradiction.
Qed.

Lemma psub_empty': forall p,
  psub (plift p) pempty -> p = qempty.
Proof.
  intros. rewrite plift_qual_eq. eapply functional_extensionality. intros x. eapply propositional_extensionality. split; intros Q.
  - eapply H in Q. unfold pempty in Q. contradiction.
  - rewrite plift_empty in Q.  unfold pempty. contradiction.
Qed.


Lemma exp_cons: forall S1 S2 M S1' S2' M' H1 H2 V1 V2 t1 t2 t1' t2' p1 p2 T uv e1 e2 (fr1:bool) a1 (fr2:bool) a2,
    stty_wellformed M ->
    store_type S1 S2 M p1 p2 ->
    psub (pif (e1||e2) (exp_locs V1 (tcons t1 t1'))) p1 ->
    psub (pif (e1||e2) (exp_locs V2 (tcons t2 t2'))) p2 ->
    bsub (e1||e2) uv ->
    exp_type1 S1 S2 M H1 H2 V1 V2 t1 t2 S1' S2' M' T uv p1 p2 fr1 a1 e1 ->
    exp_type S1' S2' M' H1 H2 V1 V2 t1' t2' (TList T) uv  
      (por p1 (pdiff (pdom S1') (pdom S1)))
      (por p2 (pdiff (pdom S2') (pdom S2))) fr2 a2 e2 ->
    exp_type S1 S2 M H1 H2 V1 V2 (tcons t1 t1') (tcons t2 t2') (TList T) (uv) p1 p2 (fr1||fr2) (a1||a2) (e1 || e2).
Proof. 
  intros ???????????????????????? SW ST P1 P2 E HX1 HX2.
  destruct HX1 as (vx1 & vx2 & ux & lsx1 & lsx2 & SC' & SW' & TX1 & TX2 & LS1 & LS2 & ST' & VX & UX1 & UX2 & LUX1 & LUX2 & LX1 & LX2 & ES1 & ES2 & ESM).
  destruct HX2 as (S1'' & S2'' & M'' & vl1 & vl2 & ul & lsl1 & lsl2 & SC'' & SW'' & TX1' & TX2' & LS1' & LS2' & ST'' & VL & UL1 & UL2 & LUL1 & LUL2 & LXL1 & LXL2 & ES1' & ES2' & ESM').
  destruct vl1, vl2; simpl in VL; try contradiction.

  destruct uv. {
    assert (ux = true) as UX. { destruct a1; simpl in *; auto. }
    assert (ul = true) as UL. { destruct a2; simpl in *; auto. }
    subst.
    replace (negb a1 || true) with true in *. 
    replace (negb a2 || true) with true in *. 
    exists S1'', S2'', (st_step M M'' true).
    exists (vlist (vx1:: l)), (vlist (vx2:: l0)).
    exists true.
    exists (qor lsx1 lsl1), (qor lsx2 lsl2).
    split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 8: split. 9: split. 10: split. 11: split. 12: split.  
    13: split. 14: split. 15: split. 16: split.
    - eapply stchain_step. eapply stchain_chain; eauto.
    - eapply sttyw_step; eauto. destruct ST, ST', ST''. lia. destruct ST, ST', ST''. lia.
    - destruct TX1 as (n1 & TX1). 
      destruct TX1' as (n1' & TX1').
      exists (1+n1+n1'). intros. destruct n. lia. simpl. rewrite TX1. rewrite TX1'. eauto. lia. lia.
    - destruct TX2 as (n1 & TX2). destruct TX2' as (n1' & TX2').
      exists (1+n1+n1'). intros. destruct n. lia. simpl. rewrite TX2. rewrite TX2'. eauto. lia. lia.
    - lia.
    - lia.
    - rewrite por_assoc, pdiff_merge in ST''. rewrite por_assoc, pdiff_merge in ST''. eapply storet_step. auto. 
      eapply stchain_chain. eauto. eauto. all: lia.
    - simpl. repeat rewrite pif_false in *. repeat rewrite por_empty_r in *. 
      clear TX1'. clear TX2'. 
      constructor. eapply valt_store_change. eapply valt_sub_locs. eapply VX. rewrite plift_or. unfoldq; intuition. rewrite plift_or. unfoldq; intuition.
      intros ??????. eapply SC''. auto. 
      destruct ST', ST''. unfold st_len1 in *. simpl. lia.
      destruct ST', ST''. unfold st_len2 in *. simpl. lia. 
      induction VL. 
      -- constructor.
      -- constructor. eapply valt_sub_locs. eapply valt_store_change. eauto. 
         intros ??????. simpl. auto. auto. auto. rewrite plift_or. unfoldq; intuition. rewrite plift_or. unfoldq; intuition.
         auto.
    - destruct a1, a2; simpl; auto.
    - auto.
    - intros. inversion H. 
    - intros. inversion H.
    - rewrite plift_or. repeat rewrite pif_false in *. repeat rewrite por_empty_l in *. rewrite exp_locs_cons.
      intros ? [? | ?]. destruct (LX1 x) as [H_q | H_fr]. auto.  destruct a1, a2; simpl; try contradiction. left. left. auto. left. left. auto. right. unfoldq; intuition.
      destruct fr1. 2: contradiction. simpl. split. lia. eapply H_fr. 
      eapply LXL1 in H. destruct H. destruct a1, a2; simpl. left. right. auto. contradiction. left. right. auto. contradiction. right. destruct fr2. 2: contradiction. destruct fr1; simpl; unfoldq; intuition.
    - rewrite plift_or. repeat rewrite pif_false in *. repeat rewrite por_empty_l in *. rewrite exp_locs_cons.
      intros ? [? | ?]. eapply LX2 in H. destruct H. destruct a1; simpl. left. left.  auto. contradiction.  right. unfoldq; intuition.
      destruct fr1. 2: contradiction. simpl. split. lia. eapply H. 
      eapply LXL2 in H. destruct H. destruct a1, a2; simpl. left. right. auto. contradiction. left. right. auto. contradiction. right. destruct fr1,fr2; simpl; unfoldq; intuition.
    - rewrite exp_locs_cons. 
      eapply storew_trans. 
      eapply storew_widen. eapply ES1. intros ? ?. destruct e1; try contradiction. left. auto.  
      eapply storew_widen. eapply ES1'. intros ? ?. destruct e2; try contradiction. destruct e1; simpl; right; auto. lia.
    - rewrite exp_locs_cons. 
      eapply storew_trans. 
      eapply storew_widen. eapply ES2. intros ? ?. destruct e1; try contradiction. left. auto.  
      eapply storew_widen. eapply ES2'. intros ? ?. destruct e2; try contradiction. destruct e1; simpl; right; auto. lia.
    - intros. simpl. auto. intuition. destruct fr1, fr2; try inversion H.
      intuition. congruence.
  } {
    assert (ux = negb a1) as UX. { destruct a1; simpl in *; auto. }
    assert (ul = negb a2) as UL. { destruct a2; simpl in *; auto. }
    subst. replace (negb a1 || false) with (negb a1) in *.  replace (negb a2 || false) with (negb a2) in *.
    exists S1'', S2'', (st_step M M'' true).
    exists (vlist (vx1:: l)), (vlist (vx2:: l0)).
    exists (negb (a1||a2)).
    exists (qif (negb (a1||a2)) (qor lsx1 lsl1)), (qif (negb(a1||a2)) (qor lsx2 lsl2)).
(*    exists (pif (fr1||fr2) (por (plift lsx1) (plift lsl1)). exists (pif (fr1||fr2) (por lsx2 lsl2)). *)
    split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 8: split. 9: split. 10: split. 11: split. 12: split.  
    13: split. 14: split. 15: split. 16: split.
    - eapply stchain_step. eapply stchain_chain; eauto.
    - eapply sttyw_step; eauto. destruct ST, ST', ST''. lia. destruct ST, ST', ST''. lia.
    - destruct TX1 as (n1 & TX1). 
      destruct TX1' as (n1' & TX1').
      exists (1+n1+n1'). intros. destruct n. lia. simpl. rewrite TX1. rewrite TX1'. eauto. lia. lia.
    - destruct TX2 as (n1 & TX2). destruct TX2' as (n1' & TX2').
      exists (1+n1+n1'). intros. destruct n. lia. simpl. rewrite TX2. rewrite TX2'. eauto. lia. lia.
    - lia.
    - lia.
    - rewrite por_assoc, pdiff_merge in ST''. rewrite por_assoc, pdiff_merge in ST''. eapply storet_step. auto. 
      eapply stchain_chain. eauto. eauto. all: lia.
    - simpl. repeat rewrite pif_false in *. repeat rewrite por_empty_r in *.
      clear TX1'. clear TX2'.
      destruct a1. { (* TODO: this could be simplified ... *)
        simpl in *. 
        constructor. eapply valt_store_change. eapply valt_reset_locs. eauto. intuition. intuition.
        destruct ST', ST''. unfold st_len1 in *. simpl. lia.
        destruct ST', ST''. unfold st_len2 in *. simpl. lia.
        simpl in *.
        induction VL. 
        -- constructor.
        -- constructor. 
           destruct a2. {
             simpl in *. eapply valt_reset_locs. eauto. intuition.
           } { 
             simpl in *. eapply valt_reset_locs. eapply valt_usable. eauto. intuition. intuition.
           }   
           eapply IHVL.
      } {
          simpl in *. constructor. eapply valt_store_change.
          destruct a2. {
            simpl in *. eapply valt_reset_locs. eapply valt_usable. eauto. eauto. intuition.
          } {
            simpl in *. eapply valt_sub_locs. eauto.
            1,2: rewrite plift_if, plift_or; unfoldq; intuition. 
          } 
          intros ??????. auto.
          destruct ST', ST''. unfold st_len1 in *. simpl. lia.
          destruct ST', ST''. unfold st_len2 in *. simpl. lia.
          simpl in *.
          induction VL. 
          -- constructor.
          -- constructor.
             destruct a2. {
               simpl in *. eapply valt_reset_locs. eauto. intuition.
             } {
               simpl in *. eapply valt_sub_locs; eauto.
               1,2: rewrite plift_if, plift_or; unfoldq; intuition.  
             }  
             eapply IHVL.
      } 
    - destruct a1, a2; simpl; auto.
    - auto.
    - intros. rewrite plift_if, plift_or. rewrite H. rewrite pif_false. unfoldq. intuition.
    - intros. rewrite plift_if, plift_or. rewrite H. rewrite pif_false. unfoldq. intuition.

    - rewrite plift_if, plift_or. intros ??. destruct a1,a2; try contradiction. simpl in *.
      rewrite exp_locs_cons. destruct H.
      destruct (LX1 _ H) as [Q|[Q|Q]]; destruct fr1; try contradiction. right. right. simpl. unfoldq. intuition. 
      destruct (LXL1 _ H) as [Q|[Q|Q]]; destruct fr2; try contradiction. right. right. simpl. unfoldq. destruct fr1; simpl; intuition. 
      
    - rewrite plift_if, plift_or. intros ??. destruct a1,a2; try contradiction. simpl in *.
      rewrite exp_locs_cons. destruct H.
      destruct (LX2 _ H) as [Q|[Q|Q]]; destruct fr1; try contradiction. right. right. simpl. unfoldq. intuition. 
      destruct (LXL2 _ H) as [Q|[Q|Q]]; destruct fr2; try contradiction. right. right. simpl. unfoldq. destruct fr1; simpl; intuition. 
      
    - rewrite exp_locs_cons. 
      eapply storew_trans. 
      eapply storew_widen. eapply ES1. intros ? ?. destruct e1; try contradiction. left. auto.  
      eapply storew_widen. eapply ES1'. intros ? ?. destruct e2; try contradiction. destruct e1; simpl; right; auto. lia.

    - rewrite exp_locs_cons. 
      eapply storew_trans. 
      eapply storew_widen. eapply ES2. intros ? ?. destruct e1; try contradiction. left. auto.  
      eapply storew_widen. eapply ES2'. intros ? ?. destruct e2; try contradiction. destruct e1; simpl; right; auto. lia.

    - intros. simpl. auto. destruct fr1,fr2; intuition. congruence. 
  }
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

Lemma valt_sub_fun_eff: forall v1 v2 M T1 T2 u ls1 ls2 fr1 a1 fr2 a2 ef,
    val_type M v1 v2 (TFun T1 fr1 a1 T2 fr2 a2 ef) u ls1 ls2 ->
    val_type M v1 v2 (TFun T1 fr1 a1 T2 fr2 a2 true) u ls1 ls2.
Proof.
  intros. destruct v1, v2; simpl in *; try contradiction; intuition.
  unfold bsub in *.
  edestruct H with (uyv := true) as (S1'' & S2'' & M'' & vy1 & vy2 & lsy1 & lsy2 & ? & ? & ?). 15: eauto. all: eauto.
  
  intros ??. destruct ef; intuition.
  intros ??. destruct ef; intuition.
  intros [? | ?]. eapply H2; auto. intuition.
  intros [? | ?]. eapply H12; auto. intuition.

  exists S1'', S2'', M'', vy1, vy2, lsy1, lsy2. intuition. 
  {
    subst. destruct a2, ef; simpl in *; intuition.
  }
  {
    subst. destruct a2, ef; simpl in *; intuition.
  }
  {
    subst. eapply valt_usable. eauto. 
    auto.
    
  }

  eapply storew_widen. eauto. unfoldq. destruct ef; intuition.
  eapply storew_widen. eauto. unfoldq. destruct ef; intuition. 
Qed.

Lemma valt_sub_fun_fresh: forall v1 v2 M T1 T2 u ls1 ls2 frf fr1 a1 af ef,
    val_type M v1 v2 (TFun T1 fr1 a1 T2 frf af ef) u ls1 ls2 ->
    val_type M v1 v2 (TFun T1 fr1 a1 T2 true af ef) u ls1 ls2.
Proof.
  intros. destruct v1, v2; simpl in *; try contradiction; intuition.
  edestruct H as (S1'' & S2'' & M'' & vy1 & vy2 & lsy1 & lsy2 & ? & ? & ?); eauto.
  intros [? | ?]. eapply H15; auto. intuition.
  intros [? | ?]. eapply H12; auto. intuition.
  exists S1'', S2'', M'', vy1, vy2, lsy1, lsy2. intuition.
  
  intros ? Q. eapply H27 in Q. unfoldq. destruct frf; intuition.
  intros ? Q. eapply H28 in Q. unfoldq. destruct frf; intuition.
Qed.



Lemma valt_sub_fun_cap1: forall v1 v2 M T1 T2 u ls1 ls2 fr1 a1 a2 e2,
    val_type M v1 v2 (TFun T1 fr1 a1 T2 false a2 e2) u ls1 ls2 ->
    val_type M v1 v2 (TFun T1 fr1 a1 T2 false true e2) u ls1 ls2.
Proof.
  intros. destruct v1, v2; simpl in *; try contradiction; intuition.
  unfold bsub in *.
  edestruct H as (S1'' & S2'' & M'' & vy1 & vy2 & lsy1 & lsy2 & ? & ? & ?). 15: eauto. 10: eauto. 4: eauto. all: auto.
  intros. eapply H0. destruct e2,uy,a2; simpl in *; eauto. subst uyv. simpl in H13. inversion H13.
  intros. eapply H1. destruct e2,uy,a2; simpl in *; eauto. subst uyv. simpl in H13. inversion H13.
  intros. eapply H2. destruct e2, a2, uyv; simpl in *; eauto; subst; simpl in *; auto.
  intros ? ? ?. destruct H13. eapply H15. auto. auto. eapply H16. auto. auto.
  intros ? ? ?. destruct H13. eapply H12. auto. auto. eapply H17. auto. auto.
  exists S1'', S2'', M'', vy1, vy2, lsy1, lsy2. subst uyv. intuition.
  {
  subst uy. destruct a2; simpl in *. eapply H23; auto. 
  intros ? Q. destruct (H26 x) as [? | [? | [? | ?]]]. auto. all: try contradiction.
  }
  {
  subst uy. destruct a2; simpl in *. eapply H24; auto. 
  intros ? Q. destruct (H27 x) as [? | [? | [? | ?]]]. auto. all: try contradiction.  
  }

  {
    destruct a2; simpl in *. auto.
    eapply valt_usable. eauto. auto.
  }
  {
    destruct a2; simpl in *. auto.
    repeat rewrite pif_false in *. repeat rewrite por_empty_l in *.
    intros ? ?. eapply H26 in H31. unfoldq; intuition.
  }

  {
    destruct a2; simpl in *. auto.
    repeat rewrite pif_false in *. repeat rewrite por_empty_l in *.
    intros ? ?. eapply H27 in H31. unfoldq; intuition.
  } 
Qed.



Lemma valt_sub_fun_cap2: forall v1 v2 M T1 T2 u ls1 ls2 fr1 a1 fr2 a2,
    val_type M v1 v2 (TFun T1 fr1 a1 T2 fr2 a2 true) u ls1 ls2 ->
    val_type M v1 v2 (TFun T1 fr1 a1 T2 fr2 true true) u ls1 ls2.
Proof.
  intros. destruct v1, v2; simpl in *; try contradiction; intuition.
  unfold bsub in *. subst uyv.
  edestruct H with (uy := uy) as (S1'' & S2'' & M'' & vy1 & vy2 & lsy1 & lsy2 & ? & ? & ?). 15: eauto. 10: eauto. 4: eauto. all: auto.
  
  rewrite H3; auto. destruct a2; simpl; auto.
  
  intros ? ? ?. destruct H4. eapply H2. auto. auto. eapply H16. auto. auto.
  intros ? ? ?. destruct H4. eapply H12. auto. auto. eapply H17. auto. auto.
  exists S1'', S2'', M'', vy1, vy2, lsy1, lsy2. intuition.

  {
    intros ? Q. edestruct H26 as [? | [? | [? | ?]]]. eauto.
    destruct a2; try contradiction. left. auto.
    destruct a2; try contradiction. right. left. auto.
    right. right. left. auto.
    destruct fr2; try contradiction. right. right. right. auto.
  }

  {
    intros ? Q. edestruct H27 as [? | [? | [? | ?]]]. eauto.
    destruct a2; try contradiction. left. auto.
    destruct a2; try contradiction. right. left. auto.
    right. right. left. auto.
    destruct fr2; try contradiction. right. right. right. auto.
  } 
Qed.

Lemma valt_sub_fun_cap3: forall v1 v2 M T1 T2 u ls1 ls2 fr1 a1 fr2 a2,
    val_type M v1 v2 (TFun T1 fr1 a1 T2 fr2 a2 false) u ls1 ls2 ->
    val_type M v1 v2 (TFun T1 fr1 a1 T2 fr2 true true) u ls1 ls2.
Proof.
  intros. destruct v1, v2; simpl in *; try contradiction; intuition.
  unfold bsub in *. subst uyv.

  edestruct H with (uy := true)(uyv := a2) as (S1'' & S2'' & M'' & vy1 & vy2 & lsy1 & lsy2 & ? & ? & ?). 15: eauto. 10: eauto. 4: eauto. all: auto.

  intuition. destruct a2; intuition.
  
  rewrite pif_false. unfoldq; intuition.
  rewrite pif_false. unfoldq; intuition.
  
  intros ? ? ?. destruct H4. eapply H2. auto. auto. eapply H16. auto. auto.
  intros ? ? ?. destruct H4. eapply H12. auto. auto. eapply H17. auto. auto.

  exists S1'', S2'', M'', vy1, vy2, lsy1, lsy2. intuition.
  rewrite H30 in H3. inversion H3.
  rewrite H30 in H3. inversion H3.

  eapply valt_usable. eauto. auto.
  {
    intros ? Q. edestruct H26 as [? | [? | [? | ?]]]. eauto.
    destruct a2; try contradiction. left. auto.
    destruct a2; try contradiction. right. left. auto.
    right. right. left. auto.
    destruct fr2; try contradiction. right. right. right. auto.
  }

  {
    intros ? Q. edestruct H27 as [? | [? | [? | ?]]]. eauto.
    destruct a2; try contradiction. left. auto.
    destruct a2; try contradiction. right. left. auto.
    right. right. left. auto.
    destruct fr2; try contradiction. right. right. right. auto.
  } 

  eapply storew_widen. eauto. unfoldq. intuition.
  eapply storew_widen. eauto. unfoldq. intuition. 
Qed.

Lemma valt_sub_fun_cap4: forall v1 v2 M T1 T2 u ls1 ls2 fr1 a1 fr2 a2,
    val_type M v1 v2 (TFun T1 fr1 a1 T2 fr2 a2 false) u ls1 ls2 ->
    val_type M v1 v2 (TFun T1 fr1 a1 T2 fr2 true false) u ls1 ls2.
Proof.
  intros. destruct v1, v2; simpl in *; try contradiction; intuition.
  unfold bsub in *. subst uyv.

  destruct uy. {
   edestruct H with (uy := true) as (S1'' & S2'' & M'' & vy1 & vy2 & lsy1 & lsy2 & ? & ? & ?). 15: eauto. 10: eauto. 4: eauto. all: auto.
   destruct a2; intuition.
   intros ? ? ?. destruct H4. eapply H15. auto. auto. eapply H16. auto. auto.
   intros ? ? ?. destruct H4. eapply H12. auto. auto. eapply H17. auto. auto.
 
    exists S1'', S2'', M'', vy1, vy2, lsy1, lsy2. intuition.
    
    {
      destruct a2; simpl in *. auto.
      repeat rewrite pif_false in *. repeat rewrite por_empty_l in *.
      intros ? ?. eapply H26 in H2. right. right. auto.
    }

    {
      destruct a2; simpl in *. auto.
      repeat rewrite pif_false in *. repeat rewrite por_empty_l in *.
      intros ? ?. eapply H27 in H2. right. right. auto.
    }
  } {
    destruct a2. {
      edestruct H with (uy := false) (uyv := false) as (S1'' & S2'' & M'' & vy1 & vy2 & lsy1 & lsy2 & ? & ? & ?). 15: eauto. 10: eauto. 4: eauto. all: auto.
      intros ? ? ?. destruct H4. eapply H15. auto. auto. eapply H16. auto. auto.
      intros ? ? ?. destruct H4. eapply H12. auto. auto. eapply H17. auto. auto.
      exists S1'', S2'', M'', vy1, vy2, lsy1, lsy2. intuition.
    } {
        edestruct H with (uy := true) (uyv := true) as (S1'' & S2'' & M'' & vy1 & vy2 & lsy1 & lsy2 & ? & ? & ?). all: simpl. 15: eauto. 10: eauto. 4: eauto. all: auto.
        intros ? ? ?. destruct H4. eapply H15. auto. auto. eapply H16. auto. auto.
        intros ? ? ?. destruct H4. eapply H12. auto. auto. eapply H17. auto. auto.
        
        exists S1'', S2'', M'', vy1, vy2, qempty, qempty. intuition.
        rewrite plift_empty. unfoldq; intuition.
        rewrite plift_empty. unfoldq; intuition.
        eapply valt_reset_locs.  
        eapply valt_usable. eauto. intuition. intuition.
        {
          repeat rewrite pif_false in *. rewrite plift_empty. unfoldq; intuition.
        }

        {
          repeat rewrite pif_false in *. rewrite plift_empty. unfoldq; intuition.
        }
    }
  }
Qed.


Lemma valt_sub_fun_cap: forall v1 v2 M T1 T2 u ls1 ls2 fr1 a1 fr2 a2 e2,
    val_type M v1 v2 (TFun T1 fr1 a1 T2 fr2 a2 e2) u ls1 ls2 ->
    val_type M v1 v2 (TFun T1 fr1 a1 T2 fr2 true e2) u ls1 ls2.
Proof.
  intros. 
  destruct e2. eapply valt_sub_fun_cap2; eauto. 
  destruct v1, v2; simpl in *; try contradiction; intuition.
  unfold bsub in *. subst uyv.
  destruct uy. {
   edestruct H with (uy := true) as (S1'' & S2'' & M'' & vy1 & vy2 & lsy1 & lsy2 & ? & ? & ?). 15: eauto. 10: eauto. 4: eauto. all: auto.
   destruct a2; intuition.
   intros ? ? ?. destruct H4. eapply H15. auto. auto. eapply H16. auto. auto.
   intros ? ? ?. destruct H4. eapply H12. auto. auto. eapply H17. auto. auto.

    exists S1'', S2'', M'', vy1, vy2, lsy1, lsy2. intuition.

    {
      destruct a2; simpl in *. auto.
      repeat rewrite pif_false in *. repeat rewrite por_empty_l in *.
      intros ? ?. eapply H26 in H2. right. right. auto.
    }

    {
      destruct a2; simpl in *. auto.
      repeat rewrite pif_false in *. repeat rewrite por_empty_l in *.
      intros ? ?. eapply H27 in H2. right. right. auto.
    }
  } {
    destruct a2. {
      edestruct H with (uy := false) (uyv := false) as (S1'' & S2'' & M'' & vy1 & vy2 & lsy1 & lsy2 & ? & ? & ?). 15: eauto. 10: eauto. 4: eauto. all: auto.
      intros ? ? ?. destruct H4. eapply H15. auto. auto. eapply H16. auto. auto.
      intros ? ? ?. destruct H4. eapply H12. auto. auto. eapply H17. auto. auto.
      exists S1'', S2'', M'', vy1, vy2, lsy1, lsy2. intuition.
    } {
        edestruct H with (uy := true) (uyv := true) as (S1'' & S2'' & M'' & vy1 & vy2 & lsy1 & lsy2 & ? & ? & ?). all: simpl. 15: eauto. 10: eauto. 4: eauto. all: auto.
        intros ? ? ?. destruct H4. eapply H15. auto. auto. eapply H16. auto. auto.
        intros ? ? ?. destruct H4. eapply H12. auto. auto. eapply H17. auto. auto.

        exists S1'', S2'', M'', vy1, vy2, qempty, qempty. intuition.
        rewrite plift_empty. unfoldq; intuition.
        rewrite plift_empty. unfoldq; intuition.
        eapply valt_reset_locs.  
        eapply valt_usable. eauto. intuition. intuition.
        {
          repeat rewrite pif_false in *. rewrite plift_empty. unfoldq; intuition.
        }

        {
          repeat rewrite pif_false in *. rewrite plift_empty. unfoldq; intuition.
        }
    }
  }
Qed.





Lemma exp_sub_fun_eff1: forall S1 S2 M S1' S2' M' H1 H2 V1 V2 t1 t2 T1 T2 u p1 p2 frf fr ef rf1 a1 af a e,
    exp_type1 S1 S2 M H1 H2 V1 V2 t1 t2 S1' S2' M' (TFun T1 rf1 a1 T2 frf af ef) u p1 p2 fr a e ->
    exp_type1 S1 S2 M H1 H2 V1 V2 t1 t2 S1' S2' M' (TFun T1 rf1 a1 T2 frf af true) u p1 p2 fr a e.
Proof.
  intros. destruct H as (v1 & v2 & uv & ls1 & ls2 & ?).
  eexists v1, v2, uv, ls1, ls2. unfold exp_type2 in *. intuition.
  eapply valt_sub_fun_eff; eauto.  
Qed.

Lemma exp_sub_fun_fresh1: forall S1 S2 M S1' S2' M' H1 H2 V1 V2 t1 t2 T1 T2 u p1 p2 frf fr a1 fr1 af a ef e,
    exp_type1 S1 S2 M H1 H2 V1 V2 t1 t2 S1' S2' M' (TFun T1 fr1 a1 T2 frf af ef) u p1 p2 fr a e ->
    exp_type1 S1 S2 M H1 H2 V1 V2 t1 t2 S1' S2' M' (TFun T1 fr1 a1 T2 true af ef) u p1 p2 fr a e.
Proof.
  intros. destruct H as (v1 & v2 & uv & ls1 & ls2 & ?).
  eexists v1, v2, uv, ls1, ls2. unfold exp_type2 in *. intuition.
  eapply valt_sub_fun_fresh; eauto.  
Qed.

Lemma exp_sub_fun_cap1: forall S1 S2 M S1' S2' M' H1 H2 V1 V2 t1 t2 T1 T2 u p1 p2 frf fr a1 rf1 af a ef e,
    exp_type1 S1 S2 M H1 H2 V1 V2 t1 t2 S1' S2' M' (TFun T1 rf1 a1 T2 frf af ef) u p1 p2 fr a e ->
    exp_type1 S1 S2 M H1 H2 V1 V2 t1 t2 S1' S2' M' (TFun T1 rf1 a1 T2 frf true ef) u p1 p2 fr a e.
Proof.
  intros. destruct H as (v1 & v2 & uv & ls1 & ls2 & ?).
  eexists v1, v2, uv, ls1, ls2. unfold exp_type2 in *. intuition.
  eapply valt_sub_fun_cap; eauto.
Qed.

Lemma exp_sub_fun1: forall S1 S2 M S1' S2' M' H1 H2 V1 V2 t1 t2 T1 T2 u p1 p2 frf frf' fr rf1 a1 af af' a ef ef' e,
    exp_type1 S1 S2 M H1 H2 V1 V2 t1 t2 S1' S2' M' (TFun T1 rf1 a1 T2 frf af ef) u p1 p2 fr a e ->
    bsub frf frf' ->
    bsub af af' ->
    bsub ef ef' ->
    exp_type1 S1 S2 M H1 H2 V1 V2 t1 t2 S1' S2' M' (TFun T1 rf1 a1 T2 frf' af' ef') u p1 p2 fr a e.
Proof.
  intros. destruct frf,frf',af,af',ef,ef'; unfold bsub in *; intuition;
  try eapply exp_sub_fun_eff1; try eapply exp_sub_fun_fresh1; try eapply exp_sub_fun_cap1; eauto.
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

(* env unrestricted: result always usable *)
Definition sem_type_useU G t1 t2 T p fr a e :=
  forall M H1 H2 V1 V2,
    env_type M H1 H2 V1 V2 G true p ->
    exp_type_eff M H1 H2 V1 V2 t1 t2 T true fr a e.

(* env restricted: can't have effect, result unusable if a *)
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

Lemma vars_locs_mono: forall q p H,
  psub q p ->
  psub (vars_locs H q) (vars_locs H p).
Proof.
  intros. intros ? ?. destruct H1 as (?&?&?).
  exists x0. split; auto.
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

  


Lemma sem_sub_fresh: forall G t1 t2 T fr a e p,
    sem_type G t1 t2 T p fr  a e ->
    sem_type G t1 t2 T p true a e.
Proof.
  intros. intros um E ? ? ? ? ? WFE. intros SW ?? ps1 ps2 ST P1 P2.
  eapply exp_sub_fresh; eauto. eapply H; auto.
Qed.

Lemma sem_sub_fresh': forall G t1 t2 T fr fr' a e p,
    sem_type G t1 t2 T p fr  a e ->
    bsub fr fr' ->
    sem_type G t1 t2 T p fr' a e.
Proof.
  intros. intros um E ? ? ? ? ? WFE. intros SW ?? ps1 ps2 ST P1 P2.
  unfold bsub in *. destruct fr, fr'; intuition. 
  eapply H; auto.
  eapply exp_sub_fresh; eauto. eapply H; auto.
  eapply H; auto.
Qed.

Lemma sem_sub_cap: forall G t1 t2 T fr a e p,
    sem_type G t1 t2 T p fr a e ->
    sem_type G t1 t2 T p fr true e.
Proof.
  intros. intros um E ? ? ? ? ? WFE. intros SW ?? ps1 ps2 ST P1 P2.
  eapply exp_sub_cap; eauto. eapply H; auto.
Qed.

Lemma sem_sub_cap': forall G t1 t2 T fr a e p a',
    sem_type G t1 t2 T p fr a e ->
    bsub a a' ->
    sem_type G t1 t2 T p fr a' e.
Proof.
  intros. intros um E ? ? ? ? ? WFE. intros SW ?? ps1 ps2 ST P1 P2.
  destruct a, a'; intuition.
  eapply H; eauto.
  eapply exp_sub_cap; eauto. eapply H; auto.
  eapply H; eauto.
Qed.

Lemma sem_sub_eff: forall G t1 t2 T fr a e p e',
    sem_type G t1 t2 T p fr a e ->
    bsub e e' ->
    sem_type G t1 t2 T p fr a e'.
Proof.
  intros. intros um E ? ? ? ? ? WFE. intros SW ?? ps1 ps2 ST P1 P2.
  destruct e, e'; intuition.
  eapply H; eauto.
  eapply exp_sub_eff; eauto. eapply H; auto. unfold bsub. intuition.
  rewrite pif_false. unfoldq; intuition. rewrite pif_false. unfoldq; intuition.
  eapply H; eauto.
Qed.

Lemma sem_tfold: forall f1 f2 z1 z2 G T1 T2 ez p el t1 t2 e2 p2 a az al (a2:bool) pz pl az' al'
  (X: a2 = az'), 
  sem_type G z1 z2 T2 (plift pz) false az' ez -> 
  sem_type G t1 t2 (TList T1) (plift pl) false al' el  ->
  bsub az' az ->
  bsub al' al ->
  sem_type ((T2, false, az)::(T1, false, al)::G) f1 f2 T2 (plift p2) false a2 e2  ->
  p = (qdiff p2 (qor (qone (S (length G))) (qone (length G)))) ->
  p2 = fv (S (S (length G))) f1 ->
  fv (S (S (length G))) f1 = fv (S (S (length G))) f2 ->
  env_cap G p a ->
  sem_type G (tfold f1 z1 t1) (tfold f2 z2 t2) T2 (por (plift pz) (por (plift pl) (plift p))) false ((az'||al'||((e2||a2) &&a))&& a2) (ez||el|| ((e2||a2) &&a || az'||al')&&e2). 
Proof.
    intros ???????????????????????. intros HZ HL BSZ BSL HF HP HP2 HFV ENC.
    intros u BE. intros M H1 H2 V1 V2 WFE STW S1 S2 P1 P2 ST EQ1 EQ2.
        
    edestruct HZ with (u := u)(V1 := V1)(V2 := V2) as (S1' & S2' & M' & vz1 & vz2 & uz & lsz1 & lsz2 & SC1 & STW1 & EZ1 & EZ2 & LS1' & LS2' & ST' & VZ & UZ & ZT & QZ1 & QZ2 & QZ3 & QZ4 & SW1 & SW2 & STREL1).
    unfold bsub in *. intros. eapply BE. subst ez. auto.
    { eapply envt_tighten. eapply WFE. unfoldq; intuition.  }  
    all:eauto.
    {
      intros ? ?. eapply EQ1. destruct ez; try contradiction. simpl.
      unfold exp_locs in *. eapply vars_locs_mono; eauto. simpl. rewrite plift_or, plift_or. unfoldq; intuition.
    }
    {
      intros ? ?. eapply EQ2. destruct ez; try contradiction. simpl. 
      unfold exp_locs in *. eapply vars_locs_mono; eauto. simpl. rewrite plift_or, plift_or. unfoldq; intuition.
    }
    
    edestruct HL with (u := u)(M := M') (V1 := V1)(V2 := V2) as (S1'' & S2'' & M'' & vl1 & vl2 & ul & lsl1 & lsl2 & SC2 & STW2 & EL1 & EL2 & LS1'' & LS2'' & ST'' & VL & UL & ZL & QL1 & QL2 & QL3 & QL4 & SW3 & SW4 & STREL2).
    unfold bsub in *. intros. eapply BE. destruct ez, el; simpl; auto. inversion H.
    { eapply envt_store_change. eapply envt_tighten. eapply WFE. unfoldq; intuition. intros ?????. eapply SC1. auto. destruct ST, ST'. lia.  destruct ST, ST'. lia. } 
    all: eauto. 
    {
      intros ? ?. left.  eapply EQ1. destruct el; try contradiction; simpl.
      unfold exp_locs in *.  
      replace (ez || true ||  ((e2 || a2) && a || az' || al') && e2) with true. 2:{ destruct ez; simpl; auto. }
      eapply vars_locs_mono; eauto. simpl. rewrite plift_or, plift_or. unfoldq; intuition.
    }
    {
      intros ? ?. left. eapply EQ2. destruct el; try contradiction; simpl.
      unfold exp_locs in *. 
      replace (ez || true || ((e2 || a2) && a || az' || al') && e2) with true. 2:{ destruct ez; simpl; auto. }
      eapply vars_locs_mono; eauto. simpl. rewrite plift_or, plift_or. unfoldq; intuition.
    }

    remember VL as VL'. clear HeqVL'.
    destruct vl1, vl2; simpl in VL; intuition.
   
    assert (forall vz1 vz2 lsz1' lsz2' ve1 ve2 lse1 lse2 SX SY MXY ur uf, 
      (ul = false  -> psub (plift lse1) pempty) ->
      (ul = false  -> psub (plift lse2) pempty) ->
      (uz = false  -> psub (plift lsz1') pempty) ->
      (uz = false  -> psub (plift lsz2') pempty) ->
      (* (psub (plift lsz1) (por (pif az (exp_locs V1 z1)) (por (pif false (pnot pempty))(pif false (pdiff (pdom S1') (pdom S1)))))) -> *)
      (psub (plift lsz1') (por (pif (az') (exp_locs V1 (tfold f1 z1 t1))) (por (pif false (pnot pempty))(pif false (pdiff (pdom S1') (pdom S1)))))) ->
      
      (psub (plift lsz2') (por (pif (az') (exp_locs V2 (tfold f2 z2 t2))) (por (pif false (pnot pempty))(pif false (pdiff (pdom S2') (pdom S2)))))) ->
      (psub (plift lse1) (por (pif al' (exp_locs V1 t1)) (por (pif false (pnot pempty))(pif false (pdiff (pdom S1'') (pdom S1')))))) ->
      (psub (plift lse2) (por (pif al' (exp_locs V2 t2)) (por (pif false (pnot pempty))(pif false (pdiff (pdom S2'') (pdom S2')))))) ->
      (uf = (negb a) ||u) ->
      (e2||ur&&a2 = true -> uf = true) -> 
      (e2||ur&&a2 = true -> uz = true) ->  
      (e2||ur&&a2 = true -> ul = true) ->
      (ur =(negb ((az'||al'||((e2||a2) &&a))&& a2)) || u) ->
     (* (false||(az||al) = false  -> uz = true) ->
      (false||al = false  -> ul = true) -> *)
      store_type SX SY MXY 
          (por (por (por P1 (pdiff (pdom S1') (pdom S1))) (pdiff (pdom S1'') (pdom S1'))) (pdiff (pdom SX)(pdom S1'')))
          (por (por (por P2 (pdiff (pdom S2') (pdom S2))) (pdiff (pdom S2'') (pdom S2'))) (pdiff (pdom SY)(pdom S2''))) ->
      length S1'' <= length SX ->
      length S2'' <= length SY ->    
      st_chain M'' MXY -> 
      stty_wellformed MXY ->
      val_type MXY ve1 ve2 T1 (ul = true) lse1 lse2 ->
      val_type MXY vz1 vz2 T2 (uz = true) lsz1' lsz2' ->
      exists vr1 vr2 lsr1 lsr2 SR1 SR2 MR, 
         tevaln SX (vz1 :: ve1::  H1) f1 SR1 vr1 /\
         tevaln SY (vz2 :: ve2::  H2) f2 SR2 vr2 /\
         length SX <= length SR1 /\
         length SY <= length SR2 /\
         store_type SR1 SR2 MR  
              (por (por (por (por P1 (pdiff (pdom S1') (pdom S1))) (pdiff (pdom S1'') (pdom S1'))) (pdiff (pdom SR1)(pdom S1''))) (pdiff (pdom SR1)(pdom SX))) 
              (por (por (por (por P2 (pdiff (pdom S2') (pdom S2))) (pdiff (pdom S2'') (pdom S2'))) (pdiff (pdom SR2)(pdom S2''))) (pdiff (pdom SR2)(pdom SY))) /\
         st_chain MXY MR /\
         stty_wellformed MR /\
         val_type MR vr1 vr2 T2 (ur = true) lsr1 lsr2 /\
         (* (ur = true (*(negb (a2) || u *)) /\ *)
         (ur = false -> psub (plift lsr1) pempty) /\
         (ur = false -> psub (plift lsr2) pempty) /\
         psub (plift lsr1) (por (pif a2 (exp_locs (lsz1'::lse1::(restrictV ((e2||a2) && a && u) V1)) f1))(por (pif false (pnot pempty)) (pif false (pdiff (pdom SR1)(pdom SX))))) /\
         psub (plift lsr2) (por (pif a2 (exp_locs (lsz2'::lse2::(restrictV ((e2||a2) && a && u) V2)) f2))(por (pif false (pnot pempty)) (pif false (pdiff (pdom SR2)(pdom SY))))) /\
         store_write SX SR1 (pif  (e2) (exp_locs (lsz1'::lse1::(restrictV ((e2||a2) && a && u) V1)) f1)) /\
         store_write SY SR2 (pif  (e2) (exp_locs (lsz2'::lse2::(restrictV ((e2||a2) && a && u) V2)) f2)) /\
         (false = false -> strel MR = strel MXY)
      ) as HFF. {
        intros. 
        
         remember (e2||ur&&a2) as D.
         destruct D.
         + (* use *)
          assert (u = false -> a = true -> e2 = false). destruct u,a,e2; intuition.
          assert (u = false -> a = true -> a2 = false). subst. unfold bsub in *. destruct u, a,az; simpl in *; intuition. 
          assert (u = false -> a = false). intros. destruct a. {
          replace a2 with false in *. 2: intuition.
          replace e2 with false in *. 2: intuition.
          destruct ur; inversion HeqD. } eauto. 
                
          assert (e2||a2 = true) as A. destruct e2,a2; intuition. 
          rewrite A in *.
          
         edestruct HF with (u := true)(M := MXY)(S1 := SX)(S2 := SY)(H1 := (vz0::ve1::H1))(H2 := (vz3::ve2 :: H2))
             (V1 := lsz1' ::lse1 :: (restrictV ((e2||a2) && a && u) V1)) (V2 := lsz2' ::lse2 :: (restrictV ((e2||a2) && a && u) V2))
          as (S1''' & S2''' & M''' & vf1 & vf2 & uf' & lsf1 & lsf2 & SC3 & STW3 & EF1 & EF2 & LSF1 & LSF2 & ST''' & VF & UF & ZF & QF1 & QF2 & QF3 & QF4 & SW1' & SW2' & STREL3). 
          
          { unfold bsub in *. intros. auto. }

          {
          eapply envt_tighten.
          eapply envt_extend. 
          eapply envt_extend.
          eapply envt_store_change with (M := M)(p := (plift p)). 
          rewrite A in *. simpl.
          remember (a&&u) as b.
          destruct b. {
            eapply envt_strengthenWX'. eapply envt_tighten. eapply WFE. unfoldq; intuition. eauto. eauto.
          }{
            destruct u. {
              eapply envt_strengthenWX with (uw := true). eapply envt_tighten. eapply WFE. unfoldq; intuition. unfold bsub. auto. 
              destruct a. simpl in Heqb. inversion Heqb. auto.
            }{
              eapply envt_strengthenW2'. eapply envt_tighten. eapply WFE. unfoldq; intuition. rewrite H25 in ENC; auto.
            }  
          }
          {
            intros ?????. eapply H19. eapply SC2. eapply SC1. auto.
          }
          destruct ST, ST', ST'', H16. lia.
          destruct ST, ST', ST'', H16. lia.
          eauto.
          simpl. unfold bsub in *. subst ul. subst a2. destruct al,a; simpl in *; intuition.
          {
            intros [Q | Q]. 
            - assert (al = false). { destruct a; simpl in *; auto. } 
              assert (al' = false). { unfold bsub in *. subst al. destruct al'; simpl in *; intuition. }
              subst al'.
              repeat rewrite pif_false in *. repeat rewrite por_empty_r in *. auto.
            - inversion Q.
          }
          {
            intros [Q | Q].  
            - assert (al = false). { destruct a; simpl in *; auto. } 
              assert (al' = false). { unfold bsub in *. subst al. destruct al'; simpl in *; intuition. } 
              subst al'.
              repeat rewrite pif_false in *. repeat rewrite por_empty_r in *. auto.
            - inversion Q.
          }
          
          eauto.

          { subst. unfold bsub in *. destruct az, az', al',u; simpl; auto. }
          { 
            intros [Q | Q].  destruct az; simpl in *. inversion Q.  simpl in *.
            unfold bsub in *. destruct az'; simpl in *; intuition. 
            repeat rewrite pif_false in *. repeat rewrite por_empty_r in *. auto.
            inversion Q.
          }
          { 
            intros [Q | Q].  destruct az; simpl in *. inversion Q.  simpl in *.
            unfold bsub in *. destruct az'; simpl in *; intuition. 
            repeat rewrite pif_false in *. repeat rewrite por_empty_r in *. auto.
            inversion Q.
          }

          intros ? ?. subst p p2. rewrite plift_diff.  rewrite plift_or, plift_one, plift_one.  unfoldq; intuition.
          bdestruct (x =? length G); intuition. simpl. bdestruct (x =? S (length G)); intuition.
          }  
          eauto.
          eauto.
          { 
            intros ? Q. left. left. left. simpl in Q. (* remember ((az||al)&&e2) as b. destruct b; try contradiction. *)
            eapply EQ1. 
            destruct e2; try contradiction. simpl in *.
            unfold bsub in *.  intuition. subst.            
            (* replace ((false||az||al)&&e2) with true.  *)         
            eapply exp_locs_tfold with (z := z1)(t := t1) in Q. 
            destruct Q as [Q | [Q | Q]].
            { destruct a; simpl in *. {
                replace (ez||el || true) with true. 2: { destruct ez, el; simpl in *; intuition. } 
                subst u. auto.
              } {
                eapply aux2 in Q. unfoldq; intuition.
              }
            } {
              eapply H7 in Q. repeat rewrite pif_false in *. rewrite por_empty_l in *.  destruct Q. 2:contradiction.
              destruct az'; simpl in *; try contradiction.
              replace (ez || el || (a || true || al') && true) with true. 2: { destruct ez, el, a; simpl in *; auto.  }
              unfold exp_locs in *. eapply vars_locs_mono; eauto. simpl. 
              rewrite plift_or, plift_diff. repeat rewrite plift_or. repeat rewrite plift_one.
              unfoldq; intuition.

            } {
              eapply H9 in Q. repeat rewrite pif_false in Q. rewrite por_empty_r in Q. destruct Q. 2: contradiction.
              destruct al'; try contradiction.
              replace (ez || el || (a || az' || true) && true) with true. 2: { destruct ez, el, a, az'; simpl in *; intuition. }
              unfold exp_locs in *. eapply vars_locs_mono; eauto. simpl. 
              rewrite plift_or, plift_diff. repeat rewrite plift_or. repeat rewrite plift_one.
              unfoldq; intuition.
            } 
          }
          { 
            intros ? Q. left. left. left. simpl in Q. (* remember ((az||al)&&e2) as b. destruct b; try contradiction. *)
            eapply EQ2. 
            destruct e2; try contradiction. simpl in *.
            unfold bsub in *.  intuition. subst.            
            (* replace ((false||az||al)&&e2) with true.  *)         
            eapply exp_locs_tfold with (z := z2)(t := t2) in Q. 
            destruct Q as [Q | [Q | Q]].
            { destruct a; simpl in *. {
                replace (ez||el || true) with true. 2: { destruct ez, el; simpl in *; intuition. } 
                subst u. auto.
              } {
                eapply aux2 in Q. unfoldq; intuition.
              }
            } {
              eapply H8 in Q. repeat rewrite pif_false in *. rewrite por_empty_l in *.  destruct Q. 2:contradiction.
              destruct az'; simpl in *; try contradiction. 
              replace (ez || el || (a || true || al') && true) with true. 2: { destruct ez, el, a; simpl in *; auto.  }
              unfold exp_locs in *. eapply vars_locs_mono; eauto. simpl. 
              rewrite plift_or, plift_diff. repeat rewrite plift_or. repeat rewrite plift_one.
              unfoldq; intuition.

            } {
              eapply H10 in Q. repeat rewrite pif_false in Q. rewrite por_empty_r in Q. destruct Q. 2: contradiction.
              destruct al'; try contradiction.
              replace (ez || el || (a || az' || true) && true) with true. 2: { destruct ez, el, a, az'; simpl in *; intuition. }
              unfold exp_locs in *. eapply vars_locs_mono; eauto. simpl. 
              rewrite plift_or, plift_diff. repeat rewrite plift_or. repeat rewrite plift_one.
              unfoldq; intuition.
            } 
          }

        rewrite A in *.
        assert (uf' = true). { destruct a2; simpl in *; auto. }
        assert (uf = true). { destruct a2; simpl in *; auto.  }
        assert (ur = true) as B. { subst ur. unfold bsub in *. destruct az', al', a, a2, u, ez, el, e2; simpl in *; intuition.  }
        rewrite B in *.
        eexists. eexists. exists  lsf1. exists lsf2.  exists S1'''. exists S2'''. exists M'''.
        split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 8: split. 9: split. 10: split. 
        11: split. 12: split. 13: split. 14: split. 
        1-7: eauto.
           
        eapply storet_tighten. eauto. 
        repeat rewrite por_assoc. rewrite pdiff_merge. rewrite pdiff_merge. 
        intros ? [? | [? | ?]]. left. auto. right. left. auto. rewrite por_comm. rewrite pdiff_merge.
        left. unfoldq; intuition. all: auto. lia. lia.

        repeat rewrite por_assoc. rewrite pdiff_merge. rewrite pdiff_merge. 
        intros ? [? | [? | ?]]. left. auto. right. left. auto. rewrite por_comm. rewrite pdiff_merge.
        left. unfoldq; intuition. all: auto. lia. lia.

        {
          rewrite H26 in VF. auto.  
        }
        {
            intros ? ? ?.  inversion H28.
        }
        {
            intros ? ? ?.  inversion H28.
        }
      + (* mention *) 
        assert (e2 = false). destruct e2,a2; intuition.
        assert (a2 = false \/ u = false). { unfold bsub in *. destruct e2,a2,ur, az,al,u; intuition. }
        subst e2.

        edestruct HF with (u := false)(M := MXY)(S1 := SX)(S2 := SY)(*(H1 := (vz0::ve1::H1))(H2 := (vz3::ve2 :: H2))
             (V1 := lsz0 ::lse1 :: (restrictV u V1)) (V2 := lsz3 ::lse2 :: (restrictV u V2))*)
          as (S1''' & S2''' & M''' & vf1 & vf2 & uf' & lsf1 & lsf2 & SC3 & STW3 & EF1 & EF2 & LSF1 & LSF2 & ST''' & VF & UF & ZF & QF1 & QF2 & QF3 & QF4 & SW1' & SW2' & STREL3). 
        
        { unfold bsub . auto. }
        {
          eapply envt_tighten. eapply envt_extend. eapply envt_extend.
          eapply envt_store_changeV' with (M:=M) (p:=plift p).
          destruct u. eapply envt_strengthenW1; eauto. eapply envt_tighten. eauto. unfoldq; intuition.
          eapply envt_tighten. eauto. unfoldq; intuition. 
          destruct ST, ST', ST'', H16. lia.
          destruct ST, ST', ST'', H16. lia.
          2: eauto. 5: eauto.

          destruct al; simpl. {
            eapply valt_reset_locs. eapply valt_usable. eauto. intuition. intuition.
          } {
            assert (al' = false). unfold bsub in *. destruct al'; simpl in *; intuition.
            subst al'. simpl in *. subst ul.
            repeat rewrite pif_false in *. repeat rewrite por_empty_r in *.
            eapply psub_empty' in H9; auto. eapply psub_empty' in H10; auto.
            subst. simpl in *. eauto.
          }
                  
          rewrite plift_empty. unfoldq; intuition.
          rewrite plift_empty. unfoldq; intuition.

          {
            subst a2. destruct H24.
            - subst az'. simpl in *. eapply valt_usable. eauto. auto.
            - subst u. simpl in *. 
               destruct az'; simpl in *. 
               -- rewrite UZ in *. assert (az = true). { unfold bsub in *. destruct az; simpl in *; intuition. } 
                  subst az. eauto. 
               -- eapply valt_usable. eauto. auto.
          } 

          { 
            subst a2. destruct H24.
            - subst az'. simpl in *. repeat rewrite pif_false in *. repeat rewrite por_empty_r in *.  intros. eapply psub_empty' in H7. subst lsz1'. unfoldq; intuition.
            - subst. destruct az'; simpl in *. eauto. repeat rewrite pif_false in *. repeat rewrite por_empty_r in *.  intros. eapply psub_empty' in H7. subst lsz1'. unfoldq; intuition.
          }
          
          { 
            subst a2. destruct H24.
            - subst az'. simpl in *. repeat rewrite pif_false in *. repeat rewrite por_empty_r in *.  intros. eapply psub_empty' in H8. subst lsz2'. unfoldq; intuition.
            - subst. destruct az'; simpl in *. eauto. repeat rewrite pif_false in *. repeat rewrite por_empty_r in *.  intros. eapply psub_empty' in H8. subst lsz2'. unfoldq; intuition.
          } 

          intros ? ?. subst p p2. rewrite plift_diff.  rewrite plift_or, plift_one, plift_one.  unfoldq; intuition.
          bdestruct (x =? length G); intuition. simpl. bdestruct (x =? S (length G)); intuition.
          simpl.
          bdestruct (x =? length G); intuition. simpl. bdestruct (x =? S (length G)); intuition.
          
        }

        all: eauto.
        rewrite pif_false. unfoldq; intuition.
        rewrite pif_false. unfoldq; intuition.
        eexists. eexists. exists (qif uf' lsf1). exists (qif uf' lsf2).  exists S1'''. exists S2'''. exists M'''.
        split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 8: split. 9: split. 10: split. 
        11: split. 12: split. 13: split. 14: split. 
        all:eauto.

        eapply storet_tighten. eauto. 
        repeat rewrite por_assoc. rewrite pdiff_merge. rewrite pdiff_merge. 
        intros ? [? | [? | ?]]. left. auto. right. left. auto. rewrite por_comm. rewrite pdiff_merge.
        left. unfoldq; intuition. all: auto. lia. lia.

        repeat rewrite por_assoc. rewrite pdiff_merge. rewrite pdiff_merge. 
        intros ? [? | [? | ?]]. left. auto. right. left. auto. rewrite por_comm. rewrite pdiff_merge.
        left. unfoldq; intuition. all: auto. lia. lia.

        {
          destruct a2; simpl in *. {
            assert (ur = false). {
              destruct ur; simpl in *. inversion HeqD. auto.
            }
            rewrite H23.
            subst uf'. 
            eapply valt_reset_locs. eauto. intuition.
          }{
            subst uf'.
            destruct ur. {
              eapply valt_sub_locs. eauto. rewrite plift_if. unfoldq; intuition. rewrite plift_if. unfoldq; intuition.
            } {
              eapply valt_usable. eapply valt_sub_locs. eauto. rewrite plift_if. unfoldq; intuition. rewrite plift_if. unfoldq; intuition.
              intuition.
            }
          }
        }  

        {
          destruct uf'. 
          2: { unfoldq; intuition. }
          simpl in *.
          assert (a2 = false). { destruct a2; simpl in *; intuition. }
          rewrite H23 in *.
          intros ???. eapply QF3 in H26. repeat rewrite pif_false in *. repeat rewrite por_empty_r in *. auto.
        }  
        
        { 
          destruct uf'. 
          2: { unfoldq; intuition. }
          simpl in *.
          assert (a2 = false). { destruct a2; simpl in *; intuition. }
          rewrite H23 in *.
          intros ???. eapply QF4 in H26. repeat rewrite pif_false in *. repeat rewrite por_empty_r in *. auto.
        }
        {
          rewrite plift_if. repeat rewrite pif_false in *. repeat rewrite por_empty_r in *. 
          intros ? Q.
          destruct a2; simpl in *. rewrite UF in *. contradiction.
          rewrite UF in *. eapply QF3. eauto.
        }

        {
          rewrite plift_if. repeat rewrite pif_false in *. repeat rewrite por_empty_r in *. 
          intros ? Q.
          destruct a2; simpl in *. rewrite UF in *. contradiction.
          rewrite UF in *. eapply QF4. eauto.
        }
   } 

   remember ((negb ((az'||al'||((e2||a2) &&a))&& a2)) || u) as ur.
   assert (e2||ur&&a2 = true -> negb (az'||al') || u = true) as A. {
     intros ?. subst ur. unfold bsub in *. destruct e2, az', al', a2, u; simpl in *; intuition.
   }

   assert (e2||ur&&a2 = true -> negb az' || u = true)  as B. {
     intros ?. subst ur. unfold bsub in *. destruct e2, az', al', a2, u; simpl in *; intuition.
   }

     assert (e2||ur&&a2 = true -> negb al' || u = true)  as B'. {
     intros ?. subst ur. unfold bsub in *. destruct e2, az', al', a2, u; simpl in *; intuition.
   }

   assert (e2||ur&&a2 = true -> negb a || u = true) as C. {
    intros ?. subst ur. unfold bsub in *. destruct e2, az', al', a, a2, u; simpl in *; intuition.
   } 
   
    remember (fun n => fun (hd:vl) (tl:stor * option (option vl)) =>
      match tl with
       | (S0, None) => (S0, None)
       | (S0, Some None) => (S0, Some None)
       | (S0, Some (Some vtl)) =>  teval n S0 (vtl::hd::H1) f1
    end) as ff1.

    remember (fun n => fun (hd:vl) (tl:stor * option (option vl)) =>
      match tl with
       | (S2''', None) => (S2''', None)
       | (S2''', Some None) => (S2''', Some None)
       | (S2''', Some (Some vtl)) =>  teval n S2''' (vtl::hd::H2) f2
    end) as ff2.

    assert (
      exists vr1 vr2 lsvr1 lsvr2 SR1 SR2 MR,
      (exists nm, forall n, n > nm ->
        fold_right (ff1 n) (S1'', Some (Some vz1)) l = (SR1, Some (Some vr1))) /\
      (exists nm, forall n, n > nm ->
        fold_right (ff2 n) (S2'', Some (Some vz2)) l0 = (SR2, Some (Some vr2))) /\  
      length S1'' <= length SR1 /\
      length S2'' <= length SR2 /\
      store_type SR1 SR2 MR 
              (por (por (por P1 (pdiff (pdom S1') (pdom S1))) (pdiff (pdom S1'') (pdom S1'))) (pdiff (pdom SR1)(pdom S1''))) 
              (por (por (por P2 (pdiff (pdom S2') (pdom S2))) (pdiff (pdom S2'') (pdom S2'))) (pdiff (pdom SR2)(pdom S2''))) /\
      st_chain M'' MR /\  
      stty_wellformed MR /\
      (* (e2||ur&&a2 = true -> uf = true) ->  *)
      (* (e2||ur&&a2 = true -> negb az || u = true) /\  
      (e2||ur&&a2 = true -> negb al || u = true) /\ *)
      val_type MR vr1 vr2 T2 (ur = true) lsvr1 lsvr2 /\
      (ur = false -> psub (plift lsvr1) pempty) /\
      (ur = false -> psub (plift lsvr2) pempty) /\
      (psub (plift lsvr1) (por (pif ((az'||al'||((e2||a2) &&a))&& a2) (exp_locs V1 (tfold f1 z1 t1))) (por (pif false (pnot pempty)) (pif false (pdiff (pdom S1'')(pdom SR1)))))) /\ 
      (psub (plift lsvr2) (por (pif ((az'||al'||((e2||a2) &&a))&& a2) (exp_locs V2 (tfold f2 z2 t2))) (por (pif false (pnot pempty)) (pif false (pdiff (pdom S2'')(pdom SR2)))))) /\ 
      store_write S1'' SR1 (pif (ez || el || ((e2 || a2) && a || az' || al') && e2)  (exp_locs V1 (tfold f1 z1 t1))) /\
      store_write S2'' SR2 (pif (ez || el || ((e2 || a2) && a || az' || al') && e2)  (exp_locs V2 (tfold f2 z2 t2))) /\
      (false = false -> strel MR = strel M'')
      ) as FOLD. {
    clear EL1. clear EL2. generalize dependent l0.
    induction l; intros; destruct l0.
    - remember (e2||ur&&a2) as D.
      destruct D.
      * (* use *)
        assert (u = false -> a = true -> e2 = false). destruct u,a,e2; intuition.
        assert (u = false -> a = true -> a2 = false). subst. unfold bsub in *. destruct u, a; simpl in *; intuition. 
        assert (u = false -> a = false). intros. destruct a. {
          replace a2 with false in *. 2: intuition.
          replace e2 with false in *. 2: intuition.
          destruct ur; inversion HeqD. } eauto. 
                
        assert (e2||a2 = true). destruct e2,a2; intuition. 
      
        exists vz1, vz2.  exists  (qor lsz1 (qif  ((az'||al'||((e2||a2) &&a))&& a2) lsl1)),  (qor lsz2 (qif  ((az'||al'||((e2||a2) &&a))&& a2) lsl2)), S1'', S2'', M''. 
        split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split.  8: split. 9: split. 10: split. 11: split. 12: split.
        13: split. 14: split. 
        exists 0. intros. simpl. eauto. 
        exists 0. intros. simpl. eauto.
        lia. lia.
        rewrite pdiff_same. rewrite pdiff_same. rewrite por_empty_r. rewrite por_empty_r. auto.
        eauto.
        eapply stchain_refl.
        eauto.
        {
          eapply valt_store_change.
          eapply valt_sub_locs. eapply valt_usable.  eapply VZ. destruct az', al'; simpl in *; intuition. subst uz. auto. subst uz. auto. subst uz. auto.
          rewrite plift_or. unfoldq; intuition. rewrite plift_or. unfoldq; intuition. 
          intros ??????. auto. destruct ST', ST''. lia. destruct ST', ST''. lia.
        }
        { 
          repeat rewrite pif_false in *. repeat rewrite por_empty_r in *.
          intros ? ? Q. rewrite H6 in *. rewrite plift_or in Q. rewrite X in *. 
          subst ur. simpl in *.
          destruct Q as [Q | Q].
          + destruct az'; try contradiction; simpl in *.
            ++ eapply QZ1; auto. rewrite UZ. congruence.
            ++ rewrite UZ in *. eapply QZ3 in Q. contradiction.
          + destruct az'; try contradiction; simpl in *.
            ++ subst u. subst uz. intuition.
            ++ destruct al'; simpl in *. inversion H7. destruct a; simpl in *; intuition.
        } 
        { 
          repeat rewrite pif_false in *. repeat rewrite por_empty_r in *.
          intros ? ? Q. rewrite H6 in *. rewrite plift_or in Q. rewrite X in *. 
          subst ur. simpl in *.
          destruct Q as [Q | Q].
          + destruct az'; try contradiction; simpl in *.
            ++ eapply QZ2; auto. rewrite UZ. congruence.
            ++ rewrite UZ in *. eapply QZ4 in Q. contradiction.
          + destruct az'; try contradiction; simpl in *.
            ++ subst u. subst uz. intuition.
            ++ destruct al'; simpl in *. inversion H7. destruct a; simpl in *; intuition.
        }

        {
          repeat rewrite pif_false in *. repeat rewrite por_empty_r in *.
          rewrite plift_or. rewrite X in *. 
          intros ? [Q| Q].
          + destruct az'; simpl in *.
            ++ eapply QZ3 in Q; auto. 
               unfold exp_locs in *. eapply vars_locs_mono; eauto.
               simpl. rewrite plift_or, plift_diff. repeat rewrite plift_or. repeat rewrite plift_one.
               unfoldq; intuition.
            ++ eapply QZ3 in Q. contradiction.
          + remember  ((az' || al' || (e2||az') && a) && az') as b.
            rewrite plift_if in Q. destruct b; try contradiction. eapply QL3 in Q.
            destruct al'; try contradiction.
            unfold exp_locs in *. eapply vars_locs_mono; eauto.
            simpl. rewrite plift_or, plift_diff. repeat rewrite plift_or. repeat rewrite plift_one.
            unfoldq; intuition.
        }

        {
          repeat rewrite pif_false in *. repeat rewrite por_empty_r in *.
          rewrite plift_or. rewrite X in *. 
          intros ? [Q| Q].
          + destruct az'; simpl in *.
            ++ eapply QZ4 in Q; auto. 
               unfold exp_locs in *. eapply vars_locs_mono; eauto.
               simpl. rewrite plift_or, plift_diff. repeat rewrite plift_or. repeat rewrite plift_one.
               unfoldq; intuition.
            ++ eapply QZ4 in Q. contradiction.
          + remember  ((az' || al' || (e2||az') && a) && az') as b.
            rewrite plift_if in Q. destruct b; try contradiction. eapply QL4 in Q.
            destruct al'; try contradiction.
            unfold exp_locs in *. eapply vars_locs_mono; eauto.
            simpl. rewrite plift_or, plift_diff. repeat rewrite plift_or. repeat rewrite plift_one.
            unfoldq; intuition.
        }
         
        eapply storew_refl; eauto.
        eapply storew_refl; eauto.

        auto.

      * assert (e2 = false). destruct e2,a2; intuition.
        assert (a2 = false \/ u = false). { unfold bsub in *. destruct e2,a2,ur, az',al',a,u; intuition. }
        subst e2. simpl in *.
        exists vz1, vz2.  exists (qor lsz1 (qif  ((az' || al' || a2 && a) && a2) lsl1)),  (qor lsz2 (qif  ((az' || al' || a2 && a) && a2) lsl2)), S1'', S2'', M''. 
        split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split.  8: split. 9: split. 10: split. 11: split. 12: split.
        13: split. 14: split. 
        exists 0. intros. simpl. eauto. 
        exists 0. intros. simpl. eauto.
        lia. lia.
        rewrite pdiff_same. rewrite pdiff_same. rewrite por_empty_r. rewrite por_empty_r. auto.
        eauto.
        eapply stchain_refl.
        eauto.
        auto.
        {
          eapply valt_store_change. subst a2.
          destruct H4. {
            subst az'. simpl in *. eapply valt_sub_locs. eapply valt_usable.  eapply VZ. intuition. 
            rewrite plift_or. unfoldq; intuition. rewrite plift_or. unfoldq; intuition.
          } {
            subst u. eapply valt_sub_locs. eapply valt_usable.  eapply VZ. intuition.  subst ur. destruct az'; simpl in *; intuition.
            rewrite plift_or. unfoldq; intuition. rewrite plift_or. unfoldq; intuition.
          }
                    
          intros ??????. auto. destruct ST', ST''. lia. destruct ST', ST''. lia.
        }
        { 
        
          repeat rewrite pif_false in *. repeat rewrite por_empty_r in *.
          intros ? ? Q. subst a2 ur. simpl in *. rewrite plift_or in Q. 
          destruct Q as [Q | Q].
          + destruct H4. 
            ++ subst az'. simpl in *.  assert False. destruct al'; simpl in *; intuition. contradiction.
            ++ subst u. destruct az'; simpl in *. eapply QZ1; auto. destruct al'; simpl in *. inversion H3. inversion H3.
          + destruct H4.
            ++ subst az'. simpl in *. destruct al'; simpl in *. inversion H3. inversion H3. 
            ++ subst u. destruct az'; simpl in *. destruct al'; simpl in *. eapply QL1; auto. rewrite pif_false in QL3. eapply QL3. auto.
               destruct al'; simpl in *. inversion H3. inversion H3.
        }    
        { 
        
          repeat rewrite pif_false in *. repeat rewrite por_empty_r in *.
          intros ? ? Q. subst a2 ur. simpl in *. rewrite plift_or in Q. 
          destruct Q as [Q | Q].
          + destruct H4. 
            ++ subst az'. simpl in *.  assert False. destruct al; simpl in *; intuition. contradiction.
            ++ subst u. destruct az'; simpl in *. eapply QZ2; auto. destruct al'; simpl in *. inversion H3. inversion H3.
          + destruct H4.
            ++ subst az'. simpl in *. destruct al'; simpl in *. inversion H3. inversion H3. 
            ++ subst u. destruct az'; simpl in *. destruct al'; simpl in *. eapply QL2; auto. rewrite pif_false in QL4. eapply QL4. auto.
               destruct al'; simpl in *. inversion H3. inversion H3.
        }

        {
          repeat rewrite pif_false in *. repeat rewrite por_empty_r in *.
          rewrite plift_or. 
          intros ? [Q| Q].
          + destruct H4.
            ++ subst a2. subst az'. simpl in *. eapply QZ3 in Q; eauto. contradiction.
            ++ subst u. simpl in *. subst a2. destruct az'; simpl in *. 
               { eapply QZ1 in Q. unfoldq; intuition. auto. }  
               { simpl in *. eapply QZ3 in Q. contradiction. }
          + destruct H4.
            ++ subst a2. subst az'. simpl in *. destruct al'; simpl in *; intuition. 
            ++ subst u. remember ((az' || al' || a2 && a) && a2) as b.
                destruct b; simpl in *; intuition. eapply QL3 in Q. destruct al'; try contradiction.
                unfold exp_locs in *. eapply vars_locs_mono; eauto.
                simpl. rewrite plift_or, plift_diff. repeat rewrite plift_or. repeat rewrite plift_one.
                unfoldq; intuition.
        }
        
        {
          repeat rewrite pif_false in *. repeat rewrite por_empty_r in *.
          rewrite plift_or. 
          intros ? [Q| Q].
          + destruct H4.
            ++ subst a2. subst az'. simpl in *. eapply QZ4 in Q; eauto. contradiction.
            ++ subst u. simpl in *. subst a2. destruct az'; simpl in *. 
               { eapply QZ2 in Q. unfoldq; intuition. auto. }  
               { simpl in *. eapply QZ4 in Q. contradiction. }
          + destruct H4.
            ++ subst a2. subst az'. simpl in *. destruct al'; simpl in *; intuition. 
            ++ subst u. remember ((az' || al' || a2 && a) && a2) as b.
                destruct b; simpl in *; intuition. eapply QL4 in Q. destruct al'; try contradiction.
                unfold exp_locs in *. eapply vars_locs_mono; eauto.
                simpl. rewrite plift_or, plift_diff. repeat rewrite plift_or. repeat rewrite plift_one.
                unfoldq; intuition.
        }

        
         
        eapply storew_refl; eauto.
        eapply storew_refl; eauto.
        
        auto.
 
    - inversion VL.
    - inversion VL.
    - inversion VL. subst x l1 y l'. 
      edestruct IHl as (vr1 & vr2 & lsr1 & lsr2 & SR1 & SR2 & MR &(nr1' & A') & (nr2' & B'') & LR1 & LR2 & STR & STCR & STWR & VR & QR1 & QR2 & QR3 & QR4 & STWR1 & STWR2 & STRELR). eauto. eauto.
      simpl. 
      remember (e2||ur&&a2) as D.
      destruct D.
         * (* use *)
           assert (u = false -> a = true -> e2 = false). destruct u,a,e2; intuition.
           assert (u = false -> a = true -> a2 = false). subst. unfold bsub in *. destruct u, a; simpl in *; intuition. 
           assert (u = false -> a = false). intros. destruct a. {
             replace a2 with false in *. 2: intuition.
             replace e2 with false in *. 2: intuition.
             destruct ur; inversion HeqD. } eauto. 
                   
           assert (e2||a2 = true). destruct e2,a2; intuition. 
   
           edestruct HFF with  (SX := SR1)(SY := SR2)(MXY := MR) 
           as (vr1' & vr2' & lsr1' & lsr2' & SR1' & SR2' & MR' & (n1' & E1) & (n2' & E2) & LSR1 & LSR2 & STR' & SCR' & STWR' & VTR' & QR1' & QR2' & QR3' & QR4' & STWR1' & STWR2' & STRELR').
           9: { eauto.  }
           9: { intros ?.  destruct a,u; simpl in *; intuition.   }
           9: { eauto. }
           9: { eauto. }
           9: { eauto. }
          15: { rewrite H7 in *.
                destruct az'.
                - subst uz.  rewrite X in *. simpl in *. subst ur.  eapply VR.
                - simpl in *.
                  assert (ur = true). { rewrite X in *. destruct al',a,u; simpl in *; intuition.  }
                  rewrite H9 in *. rewrite UZ. eapply VR.
          }      

          14: { eapply valt_store_change. eapply H6. 
                intros ? ? ? ? ? ?.  eapply STCR. auto.
                destruct ST'', STR. lia. destruct ST'', STR. lia. }
          {  
            intros Q. subst ul. eapply QL1. auto.
          }
          { 
            intros Q. eapply QL2. auto.
          }
          {

            intros Q. rewrite X in *. subst uz.
            rewrite B in Q.  inversion Q. auto.
          }
          {

            intros Q. rewrite X in *. subst uz.
            rewrite B in Q.  inversion Q. auto.
          }

          {

            repeat rewrite pif_false in *. repeat rewrite por_empty_r in *.
            rewrite H7 in *. simpl in *.
            remember  ((az' || al' ||  a) && a2)  as b.
            destruct b; simpl in *. {
              subst.
              intros ? Q.  eapply QR3 in Q.
              destruct az'. auto.
              intuition.
            }{
              rewrite pif_false in *. eapply psub_empty' in QR3. subst. unfoldq; intuition.
            }
          }

          {

            repeat rewrite pif_false in *. repeat rewrite por_empty_r in *.
            rewrite H7 in *. simpl in *.
            remember  ((az' || al' ||  a) && a2)  as b.
            destruct b; simpl in *. {
              subst.
              intros ? Q.  eapply QR4 in Q.
              destruct az'. auto. intuition.
            }{
              rewrite pif_false in *. eapply psub_empty' in QR4. subst. unfoldq; intuition.
            }
          }



          { repeat rewrite pif_false in *. repeat rewrite por_empty_r in *. auto.  }
          { repeat rewrite pif_false in *. repeat rewrite por_empty_r in *. auto.  }

          eauto.
          lia. lia.
          eauto.
          auto.

          exists vr1', vr2'. exists (qif ((negb a2)||u) lsr1'), (qif ((negb a2)||u) lsr2'), SR1', SR2', MR'. 
          split. 2: split.  3: split. 4: split. 5: split. 6: split. 7: split. 8: split. 9: split. 10: split. 11: split. 12: split. 13: split.
          14: split. 
          exists (nr1'+n1'). intros. rewrite A'. 2: lia.
          subst ff1. eapply E1. lia.
          exists (nr2'+n2'). intros. rewrite B''. 2: lia.
          subst ff2. eapply E2. lia.
          lia. lia.
          {
            repeat rewrite por_assoc in *. 
            rewrite pdiff_merge in *. rewrite pdiff_merge in *.  rewrite pdiff_merge in *.
            rewrite pdiff_merge in *. 
            all: eauto. 2: lia. 2: lia. 2: lia. 2: lia. 2: lia. 2: lia.
            eapply storet_tighten. eauto. 
            intros ? [?| ?]. left. auto. right. unfoldq. lia.
            intros ? [?| ?]. left. auto. right. unfoldq. lia.
          }

          eapply stchain_chain. eauto. auto.
          auto.
          eauto.

          { 
            subst ur.
            remember (negb ((az' || al' || (e2 || a2) && a) && a2) || u)  as b.
            destruct b. {
              eapply valt_usable. eapply valt_sub_locs. eapply VTR'. 3: { eauto. }
              destruct a2. simpl in *. {
                destruct u; simpl in *. {
                  unfoldq; intuition.
                } {
                  intros ? Q. eapply QR3' in Q. repeat rewrite pif_false in *. repeat rewrite por_empty_r in *.
                  eapply exp_locs_tfold with (z := z1)(t:= t1) in Q.
                  destruct Q as [Q| [Q|Q]].
                  - replace ((e2||true)&&a&&false) with false in Q. eapply aux2 in Q. unfoldq; intuition. destruct e2, a; simpl in *; intuition.
                  - rewrite H5 in *; auto. eapply QR1 in Q. unfoldq; intuition. destruct az', al', e2; simpl in *; intuition.
                  - destruct al'; simpl in *.  eapply QL1 in Q; auto. unfoldq; intuition. rewrite pif_false in *. eapply QL3 in Q. unfoldq; intuition.
                }
              } {
                simpl in *. unfoldq; intuition.
              }

              destruct a2. simpl in *. {
                destruct u; simpl in *. {
                  unfoldq; intuition.
                } {
                  intros ? Q. eapply QR4' in Q. repeat rewrite pif_false in *. repeat rewrite por_empty_r in *.
                  eapply exp_locs_tfold with (z := z1)(t:= t1) in Q.
                  destruct Q as [Q| [Q|Q]].
                  - replace ((e2||true)&&a&&false) with false in Q. eapply aux2 in Q. unfoldq; intuition. destruct e2, a; simpl in *; intuition.
                  - rewrite H5 in *; auto. eapply QR2 in Q. unfoldq; intuition. destruct az', al', e2; simpl in *; intuition.
                  - destruct al'; simpl in *.  eapply QL2 in Q; auto. unfoldq; intuition. rewrite pif_false in *. eapply QL4 in Q. unfoldq; intuition.
                }
              } {
                simpl in *. unfoldq; intuition.
              }
            } {
              assert (negb a2||u = false). { destruct a2, u; simpl in *; intuition. }
              rewrite H9.
              eapply valt_reset_locs. eauto. intuition.
            }
          }

         {
            intros Q. rewrite Q in *. rewrite plift_if.
            remember (negb a2 || u) as b. 
            destruct b. { eapply QR1'. auto. }
            { unfoldq; intuition. }
          }   
          {
            intros Q. rewrite Q in *. rewrite plift_if.
            remember (negb a2 || u) as b. 
            destruct b. { eapply QR2'. auto. }
            { unfoldq; intuition. }
          }
          {
            repeat rewrite pif_false in *. repeat rewrite por_empty_r in *.
            rewrite plift_if. 
            remember (negb a2||u) as b. 
            intros ? Q. destruct b; try contradiction. rewrite H7; auto. simpl.
            eapply QR3' in Q. destruct a2; try contradiction. 
            eapply exp_locs_tfold with (z := z1) (t := t1)  in Q. 
            assert (u = true).  { simpl in *; auto. } subst u. simpl in *.
            destruct Q as [Q | [Q | Q]].
            + replace ((e2||true)&&a&&true) with (a) in Q. 2: { destruct e2,a; simpl; auto. }
              destruct a; simpl in *. 2: { eapply aux2 in Q. unfoldq; intuition. }
              { 
                 replace ((az'||al'||true)&&true)  with true. 2: { destruct az', al'; simpl; auto. }
                 auto.
              }
            + eapply QR3 in Q. replace (az' || al' || (e2 || true) && a) with (az' || al' || a) in Q. auto. destruct e2; simpl; auto.
            + eapply QL3 in Q. destruct al'; try contradiction. 
              replace (az'||true||a) with true. 2: { destruct az'; simpl; auto. }
              simpl. unfold exp_locs. eapply vars_locs_mono; eauto. unfoldq; intuition. simpl in *. 
              rewrite plift_or, plift_diff, plift_or, plift_one, plift_one, plift_or. unfoldq; intuition.
          }
          {
            repeat rewrite pif_false in *. repeat rewrite por_empty_r in *.
            rewrite plift_if. 
            remember (negb a2||u) as b. 
            intros ? Q. destruct b; try contradiction. rewrite H7; auto. simpl.
            eapply QR4' in Q. destruct a2; try contradiction. 
            eapply exp_locs_tfold with (z := z2) (t := t2)  in Q. 
            assert (u = true).  { simpl in *; auto. } subst u. simpl in *.
            destruct Q as [Q | [Q | Q]].
            + replace ((e2||true)&&a&&true) with (a) in Q. 2: { destruct e2,a; simpl; auto. }
              destruct a; simpl in *. 2: { eapply aux2 in Q. unfoldq; intuition. }
              { 
                 replace ((az'||al'||true)&&true)  with true. 2: { destruct az', al'; simpl; auto. }
                 auto.
              }
            + eapply QR4 in Q. replace (az' || al' || (e2 || true) && a) with (az' || al' || a) in Q. auto. destruct e2; simpl; auto.
            + eapply QL4 in Q. destruct al'; try contradiction. 
              replace (az'||true||a) with true. 2: { destruct az'; simpl; auto. }
              simpl. unfold exp_locs. eapply vars_locs_mono; eauto. unfoldq; intuition. simpl in *. 
              rewrite plift_or, plift_diff, plift_or, plift_one, plift_one, plift_or. unfoldq; intuition.
          }

          {
            intros ? Q. destruct Q. rewrite <-STWR1'. rewrite STWR1. auto.
            split. auto. auto. split. destruct ST''. destruct STR. destruct STR'. unfoldq. lia.
            intros ?. eapply H10. rewrite H7; auto. destruct e2; try contradiction. simpl in *.
            eapply exp_locs_tfold with (z := z1)(t := t1) in H11.
            destruct H11 as [Q | [Q| Q]].
            - remember (a && u) as b. destruct b; simpl in *. 2: { eapply aux2 in Q. unfoldq; intuition. }  
              assert ((a || az' || al') && true  = true). { destruct a, az', al'; simpl in *; intuition. }
              rewrite H11.  destruct ez, el; simpl; auto.
            - remember ((az' || al' || a) && a2) as b. 
              destruct b; simpl in *. 
              -- eapply QR3 in Q. 
                 repeat rewrite pif_false in *. repeat rewrite por_empty_r in Q.
                 assert ((a || az' || al') && true  = true). { destruct a, az', al'; simpl in *; intuition. }
                 rewrite H11. destruct ez, el; simpl; auto.
              -- repeat rewrite pif_false in *. repeat rewrite por_empty_r in QR3. eapply QR3 in Q. unfoldq; intuition.
            - eapply QL3 in Q. repeat rewrite pif_false in *. repeat rewrite por_empty_r in Q.
              destruct al'; simpl in *; try contradiction. 
              replace ((a || az' || true) && true) with true. 2:{ destruct a, az'; simpl; auto. }
              replace (ez || el || true) with true. 2: { destruct ez, el; simpl; auto. }
              unfold exp_locs in *. eapply vars_locs_mono; eauto. unfoldq; intuition. simpl in *. 
              rewrite plift_or, plift_diff, plift_or, plift_one, plift_one, plift_or. unfoldq; intuition.
          }    

          {
            intros ? Q. destruct Q. rewrite <-STWR2'. rewrite STWR2. auto.
            split. auto. auto. split. destruct ST''. destruct STR. destruct STR'. unfoldq. lia.
            intros ?. eapply H10. rewrite H7; auto. destruct e2; try contradiction. simpl in *.
            eapply exp_locs_tfold with (z := z2)(t := t2) in H11.
            destruct H11 as [Q | [Q| Q]].
            - remember (a && u) as b. destruct b; simpl in *. 2: { eapply aux2 in Q. unfoldq; intuition. }  
              assert ((a || az' || al') && true  = true). { destruct a, az', al'; simpl in *; intuition. }
              rewrite H11. destruct ez, el; simpl; auto.
            - remember ((az' || al' || a) && a2) as b. 
              destruct b; simpl in *. 
              -- eapply QR4 in Q. 
                 repeat rewrite pif_false in *. repeat rewrite por_empty_r in Q.
                 assert ((a || az' || al') && true  = true). { destruct a, az', al'; simpl in *; intuition. }
                 rewrite H11. destruct ez, el; simpl; auto.
              -- repeat rewrite pif_false in *. repeat rewrite por_empty_r in QR4. eapply QR4 in Q. unfoldq; intuition.
            - eapply QL4 in Q. repeat rewrite pif_false in *. repeat rewrite por_empty_r in Q.
              destruct al'; simpl in *; try contradiction. 
              replace ((a || az' || true) && true) with true. 2:{ destruct a, az'; simpl; auto. }
              replace (ez || el || true) with true. 2: { destruct ez, el; simpl; auto. }
              unfold exp_locs in *. eapply vars_locs_mono; eauto. unfoldq; intuition. simpl in *. 
              rewrite plift_or, plift_diff, plift_or, plift_one, plift_one, plift_or. unfoldq; intuition.
          }    

          intros. intuition. congruence.
        * (* mention *)   
          assert (e2 = false). destruct e2,a2; intuition.
          assert (a2 = false \/ u = false). { unfold bsub in *. destruct e2,a2,ur, az,al,a,u; intuition. }
          subst e2.

          edestruct HFF with  (SX := SR1)(SY := SR2)(MXY := MR)(ur := ur) 
           as (vr1' & vr2' & lsr1' & lsr2' & SR1' & SR2' & MR' & (n1' & E1) & (n2' & E2) & LSR1 & LSR2 & STR' & SCR' & STWR' & VTR' & QR1' & QR2' & QR3' & QR4' & STWR1' & STWR2' & STRELR').
           9: { eauto.  }
           9: { intros ?. destruct a2, a,ur,u; simpl in *; intuition. }
           9: { eauto. }
           9: { eauto. }
           9: { auto. }
          15: {  
                 destruct H4. {
                  subst a2. subst ur.
                  eapply valt_usable. eapply VR. simpl. intros. subst uz. simpl in *. subst az'. destruct al'; simpl in *; auto.
                 } {
                  subst u. simpl in *. subst a2. simpl in *. 
                  subst ur. rewrite UZ.  destruct az'; simpl in *. auto. destruct al'; simpl in *; auto.
                 }
          }          

          14: { eapply valt_store_change. eapply H6. 
                intros ? ? ? ? ? ?.  eapply STCR. auto.
                destruct ST'', STR. lia. destruct ST'', STR. lia. }
          {  
            intros Q. subst ul. eapply QL1. auto.
          }
          { 
            intros Q. eapply QL2. auto.
          }

          {
            repeat rewrite pif_false in *. repeat rewrite por_empty_r in *.
            intros. subst uz. intros ? Q. subst a2. 
            destruct H4. {
              subst az'. simpl in *. inversion H3.
            }{
              subst u. simpl in *. destruct az'; simpl in *; intuition. 
            }
          }

          {
            repeat rewrite pif_false in *. repeat rewrite por_empty_r in *.
            intros. subst uz. intros ? Q. subst a2.
            destruct H4. {
              subst az'. simpl in *. inversion H3.
            }{
              subst u. simpl in *. destruct az'; simpl in *; intuition. 
            }
          }

          {
            repeat rewrite pif_false in *. repeat rewrite por_empty_r in *. subst a2. simpl in *. 
            destruct H4.
            - subst. simpl in *. destruct al'; simpl in *; intuition.
            - subst u. destruct az'; simpl in *; intuition. destruct al'; simpl in *; intuition.
          }

          {
            repeat rewrite pif_false in *. repeat rewrite por_empty_r in *. subst a2. simpl in *. 
            destruct H4.
            - subst. simpl in *. destruct al'; simpl in *; intuition.
            - subst u. destruct az'; simpl in *; intuition. destruct al'; simpl in *; intuition.
          }

          {
            repeat rewrite pif_false in *. repeat rewrite por_empty_r in *. auto.
          }

          {
            repeat rewrite pif_false in *. repeat rewrite por_empty_r in *. auto.
          }
          eauto.
          lia. lia. auto. auto.
     
          exists vr1', vr2'. exists (qif ((negb a2)||u) lsr1'), (qif ((negb a2)||u) lsr2'), SR1', SR2', MR'. 
          split. 2: split.  3: split. 4: split. 5: split. 6: split. 7: split. 8: split. 9: split. 10: split. 11: split. 12: split. 13: split.
          14: split. 
          exists (nr1'+n1'). intros. rewrite A'. 2: lia.
          subst ff1. eapply E1. lia.
          exists (nr2'+n2'). intros. rewrite B''. 2: lia.
          subst ff2. eapply E2. lia.
          lia. lia.
          {
            repeat rewrite por_assoc in *. 
            rewrite pdiff_merge in *. rewrite pdiff_merge in *.  rewrite pdiff_merge in *.
            rewrite pdiff_merge in *. 
            all: eauto. 2: lia. 2: lia. 2: lia. 2: lia. 2: lia. 2: lia.
            eapply storet_tighten. eauto. 
            intros ? [?| ?]. left. auto. right. unfoldq. lia.
            intros ? [?| ?]. left. auto. right. unfoldq. lia.
          }

          eapply stchain_chain. eauto. auto.
          auto.
          eauto.

          { 
            eapply valt_sub_locs. eapply VTR'.
            destruct H4. {
              subst a2. rewrite H3 in *. simpl. unfoldq; intuition.
            }{
              subst u. simpl in *. 
              destruct a2. {
                simpl in *.
                assert (ur = false). { destruct ur; simpl in *; intuition. }
                rewrite H3 in *. eapply psub_empty' in QR1'; auto. subst lsr1'.  unfoldq; intuition.
              } {
                simpl in *. unfoldq; intuition.
              }
            }

            destruct H4. {
              subst a2. rewrite H3 in *. simpl. unfoldq; intuition.
            }{
              subst u. simpl in *. 
              destruct a2. {
                simpl in *.
                assert (ur = false). { destruct ur; simpl in *; intuition. }
                rewrite H3 in *. eapply psub_empty' in QR2'; auto. subst lsr2'.  unfoldq; intuition.
              } {
                simpl in *. unfoldq; intuition.
              }
            }
          }
          

         {
            intros Q. rewrite Q in *. rewrite plift_if.
            remember (negb a2 || u) as b. 
            destruct b. { eapply QR1'. auto. }
            { unfoldq; intuition. }
          }   
          {
            intros Q. rewrite Q in *. rewrite plift_if.
            remember (negb a2 || u) as b. 
            destruct b. { eapply QR2'. auto. }
            { unfoldq; intuition. }
          }
          {
            repeat rewrite pif_false in *. repeat rewrite por_empty_r in *.
            rewrite plift_if. 
            remember (negb a2||u) as b. 
            intros ? Q. destruct b; try contradiction. 
            destruct H4.
            - subst a2. rewrite H3 in *. simpl in *. eapply QR3' in Q. contradiction.
            - subst u. simpl in *. assert (a2 = false). { destruct a2; simpl in *; auto. }
              subst a2. rewrite H3 in *. simpl in *. eapply QR3' in Q. contradiction.
          }   
          
          
          {
            repeat rewrite pif_false in *. repeat rewrite por_empty_r in *.
            rewrite plift_if. 
            remember (negb a2||u) as b. 
            intros ? Q. destruct b; try contradiction. 
            destruct H4.
            - subst a2. rewrite H3 in *. simpl in *. eapply QR4' in Q. contradiction.
            - subst u. simpl in *. assert (a2 = false). { destruct a2; simpl in *; auto. }
              subst a2. rewrite H3 in *. simpl in *. eapply QR4' in Q. contradiction.
          }

          {
            intros ? Q. destruct Q. rewrite <-STWR1'. rewrite STWR1. auto.
            split. auto. auto. split. destruct ST''. destruct STR. destruct STR'. unfoldq. lia.
            intros ?. eapply H5. simpl in *. 
            destruct H4.
            - subst a2. simpl in *.  contradiction.
            - subst u a2; simpl in *. contradiction. 
          }
          
          {
            intros ? Q. destruct Q. rewrite <-STWR2'. rewrite STWR2. auto.
            split. auto. auto. split. destruct ST''. destruct STR. destruct STR'. unfoldq. lia.
            intros ?. eapply H5. simpl in *. 
            destruct H4.
            - subst a2. simpl in *. contradiction.
            - subst u a2; simpl in *. contradiction. 
          }
          
          intros. intuition. congruence. congruence. 

  }

  destruct FOLD as (vr1 & vr2 & lsvr1 & lsvr2 & SR1 & SR2 & MR &? &? &? & ? &? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ?).
  
  exists SR1, SR2, MR, vr1, vr2. eexists. eexists. eexists.
  split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 8: split. 9:split. 10: split. 11: split.
  12: split. 13: split. 14: split. 15: split. 16: split.
  9: eauto.
  + eapply stchain_chain; eauto. eapply stchain_chain. eauto. eauto.
  + auto.
  + destruct EZ1 as (n1 & EZ1).
    destruct EL1 as (n2 & EL1).
    destruct H3 as (n3 & E2).
    exists (1+n1+n2+n3). intros. destruct n. lia.
    simpl. rewrite EZ1. rewrite EL1. 2,3: lia. 
    subst ff1. rewrite E2. auto. lia.
  + destruct EZ2 as (n1 & EZ2).
    destruct EL2 as (n2 & EL2).
    destruct H4 as (n3 & E2).
    exists (1+n1+n2+n3). intros. destruct n. lia.
    simpl. rewrite EZ2. rewrite EL2. 2,3: lia. 
    subst ff2. rewrite E2. auto. lia. 
  + lia.
  + lia.
  + repeat rewrite por_assoc in H7. 
    rewrite pdiff_merge, pdiff_merge in H7.
    rewrite pdiff_merge, pdiff_merge in H7.
    all: eauto. 2: lia. lia.
  + eauto.
  + auto.
  + auto.
  + auto. 
  + auto.
  + auto.
  + intros ? Q. destruct Q. rewrite <-H15. rewrite <-SW3. rewrite <-SW1. auto.
    split. auto. intros ?. eapply H19. destruct ez; simpl; try contradiction. 
    unfold exp_locs in *. eapply vars_locs_mono; eauto. unfoldq; intuition. simpl in *. 
    rewrite plift_or, plift_diff, plift_or, plift_one, plift_one, plift_or. unfoldq; intuition.
    split. destruct ST'. unfoldq. lia. 
    intros ?. eapply H19. destruct el; try contradiction. replace (ez || true || ((e2 || a2) && a || az' || al') && e2)  with true. 2: { destruct ez, e2; intuition. }
    unfold exp_locs in *. eapply vars_locs_mono; eauto. simpl in *. rewrite plift_or. rewrite plift_diff. repeat rewrite plift_or. 
    repeat rewrite plift_one. unfoldq; intuition.
    split. destruct ST', ST''. unfoldq. lia.  auto.
  + intros ? Q. destruct Q. rewrite <-H16. rewrite <-SW4. rewrite <-SW2. auto.
    split. auto. intros ?. eapply H19. destruct ez; simpl; try contradiction. 
    unfold exp_locs in *. eapply vars_locs_mono; eauto. unfoldq; intuition. simpl in *. 
    rewrite plift_or, plift_diff, plift_or, plift_one, plift_one, plift_or. unfoldq; intuition.
    split. destruct ST'. unfoldq. lia. 
    intros ?. eapply H19. destruct el; try contradiction. replace (ez || true || ((e2 || a2) && a || az' || al') && e2) with true. 2: { destruct ez, e2; intuition. }
    unfold exp_locs in *. eapply vars_locs_mono; eauto. simpl in *. rewrite plift_or. rewrite plift_diff. repeat rewrite plift_or. 
    repeat rewrite plift_one. unfoldq; intuition.
    split. destruct ST', ST''. unfoldq. lia. auto.
  + intros. intuition. congruence.
Qed.




Definition sem_stp T1 T2 :=
  forall M ,
    (forall v1 v2 ux lsv1 lsv2,
    val_type M v1 v2 T1 ux lsv1 lsv2 ->
    val_type M v1 v2 T2 ux lsv1 lsv2 )
.



Lemma exp_sub_stp2: forall S1 S2 M H1 H2 V1 V2 t1 t2 T1 T2 p1 p2 v1 v2 uv ls1 ls2 S1' S2' M' u fr fr' a a' e e',
  stty_wellformed M ->
  store_type S1 S2 M p1 p2 ->
  exp_type2 v1 v2 u ls1 ls2 S1 S2 M H1 H2 V1 V2 t1 t2 S1' S2' M' T1 uv p1 p2 fr a e ->
  bsub fr fr' ->
  bsub a a' ->
  bsub e e' ->
  sem_stp T1 T2 ->
  exp_type2 v1 v2 u (if (negb a' || u) then ls1 else qempty) 
                     (if (negb a' || u) then ls2 else qempty) 
                     S1 S2 M H1 H2 V1 V2 t1 t2 S1' S2' M' T2 (negb a' || u) p1 p2 fr' a' e'.
Proof.
  intros. unfold bsub in *.
  unfold exp_type2 in H3. unfold exp_type2.
  intuition.
  destruct a, a', uv,u; simpl in *; subst; intuition. 
  eapply valt_reset_locs. eapply valt_usable. eauto. intuition. intuition. 
  eapply valt_reset_locs. eapply valt_usable. eauto. intuition. intuition. 
  

  rewrite H23. rewrite plift_empty. unfoldq; intuition.
  rewrite H23. rewrite plift_empty. unfoldq; intuition.
  {
    remember (negb a' || u) as b. 
    destruct b. 2: { rewrite plift_empty. unfoldq; intuition. }
    intros ? ?. destruct (H19 x) as [H_a | [? | H_fr]]. auto.
    left. destruct a; simpl in *; try contradiction. rewrite H5; auto.
    contradiction.
    right. right. destruct fr, fr'; try contradiction; intuition.
  }
  {
    remember (negb a' || u) as b. 
    destruct b. 2: { rewrite plift_empty. unfoldq; intuition. }
    intros ? ?. destruct (H20 x) as [H_a | [? | H_fr]]. auto.
    left. destruct a; simpl in *; try contradiction. rewrite H5; auto.
    contradiction.
    right. right. destruct fr, fr'; try contradiction; intuition.
  }
  {
    eapply storew_widen; eauto. destruct e, e'; unfoldq; intuition.
  }
  {
    eapply storew_widen; eauto. destruct e, e'; unfoldq; intuition.
  }
  eapply H24. destruct fr, fr'; try contradiction; intuition. 
Qed.

Lemma sem_stp_bool: 
  sem_stp TBool TBool.
Proof.
  intros. intros M v1 v2 ux lsv1 lsv2. 
  intros. simpl in *. destruct v1,v2; try contradiction. auto.
Qed.

Lemma sem_stp_ref:
  sem_stp TRef TRef.
Proof.
  intros. intros M v1 v2 ux lsv1 lsv2. 
  intros. simpl in *. destruct v1,v2; try contradiction. auto.
Qed.

Lemma sem_stp_list: forall T1 T2,
  sem_stp T1 T2 ->
  sem_stp (TList T1) (TList T2).
Proof.
  intros T1 T2 HST. intros M v1 v2 ux lsv1 lsv2 HV.
  simpl in *. destruct v1,v2; try contradiction. 
  induction HV.
  - constructor. 
  - constructor. auto. eauto.
Qed.

Lemma sem_stp_fun1: forall T1 fr1 a1 T2 fr2 a2 e2 T3 fr3 a3 T4 fr4 e4,
  sem_stp T3 T1 ->
  sem_stp T2 T4 ->
  bsub a3 a1 ->
  bsub fr3 fr1 ->
  bsub fr2 fr4 ->
  bsub e2 e4 -> 
  sem_stp (TFun T1 fr1 a1 T2 fr2 a2 e2) (TFun T3 fr3 a3 T4 fr4 a2 e4).
Proof.
  intros T1 fr1 a1 T2 fr2 a2 e2 T3 fr3 a3 T4 fr4 e4. 
  intros HST1 HST2 HSA1 HSFR1 HSFR2 HSE.
  intros M v1 v2. 
  intros. 
  unfold bsub in *.
  simpl in *. destruct v1,v2; try contradiction. 
  intros. unfold bsub in *. 

  assert (e2 ||uy && a2 = true -> e4 || uy && a2 = true) as P1. {
    destruct e4, uy, e2, a2; simpl in *; auto.
  }
  edestruct H as (S1'' & S2'' & M'' & vy1 & vy2 & lsy1 & lsy2 & ?). 
  { intros. eapply H0. eauto. }
  { intros. eapply H1. eauto. }
  { intros. eapply H2. eauto. }
  { intros. eapply H3. auto. }
  {  auto.  }
  { intros. eapply H5. destruct fr1, a1, fr3, a3; intuition.  }
  auto. lia. lia. eauto. 
  { intros ? ?. eapply H10. destruct e2, e4; intuition; try contradiction. eauto. }
  { intros ? ?. eapply H11. destruct e2, e4; intuition; try contradiction. eauto. }
  { intros. eapply H12. destruct fr1, a1, fr3, a3; simpl in *; intuition. }
  { intros. eapply H13. destruct fr1, a1, fr3, a3; simpl in *; intuition. }
  { eapply HST1. eauto. }
  exists S1'', S2'', M'', vy1, vy2, lsy1, lsy2. intuition.
  {
    intros ? ?. destruct (H25 x) as [H_f | [H_x | [? | H_fr]]]. auto.
    left. destruct a2; try contradiction; intuition.
    right. left. destruct a2; try contradiction; intuition.
    right. right. left. auto.
    right. right. right. destruct fr2, fr4; try contradiction; intuition.
  }
  {
    intros ? ?. destruct (H26 x) as [H_f | [H_x | [? | H_fr]]]. auto.
    left. destruct a2; try contradiction; intuition.
    right. left. destruct a2; try contradiction; intuition.
    right. right. left. auto.
    right. right. right. destruct fr2, fr4; try contradiction; intuition.
  }
  {
    intros ? ?. eapply H27. destruct H13. split; auto.
    destruct e2, e4; try contradiction; intuition.
  }

  {
    intros ? ?. eapply H28. destruct H13. split; auto. 
    destruct e2, e4; try contradiction; intuition.
  }
  eapply H30. destruct fr2, fr4; intuition.
Qed.

Lemma sem_stp_fun2: forall T1 fr1 a1 T2 fr2 a2 e2 a4,
  bsub a2 a4 -> 
  sem_stp (TFun T1 fr1 a1 T2 fr2 a2 e2) (TFun T1 fr1 a1 T2 fr2 a4 e2).
Proof. 
  intros. intros M v1 v2 ux lsv1 lsv2 W.
  unfold bsub in *.
  destruct a2, a4; auto. intuition.
  eapply valt_sub_fun_cap. eauto.
Qed. 

Lemma sem_stp_fun: forall T1 fr1 a1 T2 fr2 a2 e2 T3 fr3 a3 T4 fr4 a4 e4,
  sem_stp T3 T1 ->
  sem_stp T2 T4 ->
  bsub a3 a1 ->
  bsub fr3 fr1 ->
  bsub a2 a4 ->
  bsub fr2 fr4 ->
  bsub e2 e4 -> 
  sem_stp (TFun T1 fr1 a1 T2 fr2 a2 e2) (TFun T3 fr3 a3 T4 fr4 a4 e4).
Proof.
  intros T1 fr1 a1 T2 fr2 a2 e2 T3 fr3 a3 T4 fr4 a4 e4. 
  intros HST1 HST2 HSA1 HSFR1 HSA2 HSFR2 HSE.
  intros M v1 v2. 
  intros.   
  simpl in *. destruct v1,v2; try contradiction. 
  intros. unfold bsub in *. 

  assert (e2 ||uy && a2 = true -> e4 || uy && a4 = true) as P1. {
    destruct e4, uy, a4, e2, a2; simpl in *; auto.
  }
  destruct uy. {
    edestruct H  with (uy := true) as (S1'' & S2'' & M'' & vy1 & vy2 & lsy1 & lsy2 & ?). 
    { intros. eapply H0. eauto. }
    { intros. eapply H1. eauto. }
    { intros. eapply H2. eauto. }
    { intros. eapply H3. auto. }
    {  destruct a2, uyv; simpl in *; intuition. subst a4. simpl in *. inversion H4.  }
    { intros. eapply H5. destruct fr1, a1, fr3, a3; intuition.  }
    auto. lia. lia. eauto. 
    { intros ? ?. eapply H10. destruct e2, e4; intuition; try contradiction. eauto. }
    { intros ? ?. eapply H11. destruct e2, e4; intuition; try contradiction. eauto. }
    { intros. eapply H12. destruct fr1, a1, fr3, a3; simpl in *; intuition. }
    { intros. eapply H13. destruct fr1, a1, fr3, a3; simpl in *; intuition. }
    { eapply HST1. eauto. }
    exists S1'', S2'', M'', vy1, vy2, lsy1, lsy2. intuition.
    {
      intros ? ?. destruct (H25 x) as [H_f | [H_x | [? | H_fr]]]. auto.
      left. destruct a2, a4; try contradiction; intuition.
      right. left. destruct a2, a4; try contradiction; intuition.
      right. right. left. auto.
      right. right. right. destruct fr2, fr4; try contradiction; intuition.
    }
    {
      intros ? ?. destruct (H26 x) as [H_f | [H_x | [? | H_fr]]]. auto.
      left. destruct a2, a4; try contradiction; intuition.
      right. left. destruct a2, a4; try contradiction; intuition.
      right. right. left. auto.
      right. right. right. destruct fr2, fr4; try contradiction; intuition.
    }
    {
      intros ? ?. eapply H27. destruct H13. split; auto.
      destruct e2, e4; try contradiction; intuition.
    }

    {
      intros ? ?. eapply H28. destruct H13. split; auto. 
      destruct e2, e4; try contradiction; intuition.
    }
    eapply H30. destruct fr2, fr4; intuition.
  } {
    destruct a2. {
      edestruct H with (uy := false)  as (S1'' & S2'' & M'' & vy1 & vy2 & lsy1 & lsy2 & ? & ? & ?). 15: eauto. 
      10: eauto. 4: eauto. all: auto.
      { destruct e4; simpl in *; intuition; subst; simpl in *; try inversion H4.  }
      { intros. eapply H5. destruct fr1, a1, fr3, a3; simpl in *; intuition.  }
      { intros ? ?. eapply H10. destruct e2; try contradiction. destruct e4; simpl in *; intuition.   }
      { intros ? ?. eapply H11. destruct e2; try contradiction. destruct e4; simpl in *; intuition.   }
      { intros. eapply H12. destruct fr1, a1, fr3, a3; simpl in *; intuition. }
      { intros. eapply H13. destruct fr1, a1, fr3, a3; simpl in *; intuition. }
      exists S1'', S2'', M'', vy1, vy2, lsy1, lsy2. intuition. 
      {
        intros ? ?. destruct (H25 x) as [H_f | [H_x | [? | H_fr]]]. auto.
        left. destruct a4; try contradiction; intuition.
        right. left. destruct a4; try contradiction; intuition.
        right. right. left. auto.
        right. right. right. destruct fr2, fr4; try contradiction; intuition.
      }
      {
        intros ? ?. destruct (H26 x) as [H_f | [H_x | [? | H_fr]]]. auto.
        left. destruct a4; try contradiction; intuition.
        right. left. destruct a4; try contradiction; intuition.
        right. right. left. auto.
        right. right. right. destruct fr2, fr4; try contradiction; intuition.
      }
      {
        intros ? ?. eapply H27. destruct H13. split; auto.
        destruct e2, e4; try contradiction; intuition.
      }

      {
        intros ? ?. eapply H28. destruct H13. split; auto. 
        destruct e2, e4; try contradiction; intuition.
      }
      eapply H30. destruct fr2, fr4; intuition.
    } {
      edestruct H with (uy := true) (uyv := true) as (S1'' & S2'' & M'' & vy1 & vy2 & lsy1 & lsy2 & ? & ? & ?). all: simpl. 15: eauto. 10: eauto. 4: eauto. all: auto.
      { intros. eapply H5. destruct fr1, a1, fr3, a3; intuition.  } 
      { intros ? ?. eapply H10. destruct e2; try contradiction. destruct e4; simpl in *; intuition.   }
      { intros ? ?. eapply H11. destruct e2; try contradiction. destruct e4; simpl in *; intuition.   }
      { intros. eapply H12. destruct fr1, a1, fr3, a3; simpl in *; intuition. }
      { intros. eapply H13. destruct fr1, a1, fr3, a3; simpl in *; intuition. }
      exists S1'', S2'', M'', vy1, vy2, qempty, qempty. intuition.
      rewrite plift_empty. unfoldq; intuition. 
      rewrite plift_empty. unfoldq; intuition.
      eapply valt_reset_locs. eapply valt_usable. eauto. intuition. intuition.
      rewrite plift_empty. unfoldq; intuition. 
      rewrite plift_empty. unfoldq; intuition.

      {
        intros ? ?. eapply H27. destruct H13. split; auto.
        destruct e2, e4; try contradiction; intuition.
      }

      {
        intros ? ?. eapply H28. destruct H13. split; auto. 
        destruct e2, e4; try contradiction; intuition.
      }
      eapply H30. destruct fr2, fr4; intuition.

    }
  }
Qed.



Theorem stp_fundamental: forall T1 T2,
  stp T1 T2 ->
  sem_stp T1 T2.
Proof.
  intros. induction H.
  + eapply sem_stp_bool.
  + eapply sem_stp_ref.
  + eapply sem_stp_list; eauto.
  + eapply sem_stp_fun; eauto.
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
  - (* nil *)
    eapply exp_nil; eauto.
  - (* cons *)
    edestruct IHW1 with (u := um) as (S1' & S2' & M' & ?); eauto. 
    unfold bsub. destruct e1; intuition.
    eapply envt_tighten. eapply WFE. unfoldq; intuition.
    rewrite plift_or. unfoldq; intuition.
    intros ? ?. eapply P1. rewrite exp_locs_cons. unfoldq. destruct e1; simpl in *; intuition. 
    intros ? ?. eapply P2. rewrite exp_locs_cons. unfoldq. destruct e1; simpl in *; intuition.
    eapply exp_cons; eauto. 
    destruct H as (?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?). 
    eapply IHW2 with (u := um) (M := M').
    destruct e2; unfold bsub; intuition.        
    eapply envt_store_change. eapply envt_tighten. eapply WFE. unfoldq. intuition.
    rewrite plift_or. right. auto.
    intros ?????. eauto.
    destruct ST as (?&?&?). destruct H7 as (?&?&?). lia.
    destruct ST as (?&?&?). destruct H7 as (?&?&?). lia.
    eauto. eauto. 
    rewrite exp_locs_cons in *. unfoldq. destruct e1,e2; simpl in *; intuition.
    rewrite exp_locs_cons in *. unfoldq. destruct e1,e2; simpl in *; intuition.
  - (* fold *)
    eapply exp_sub. eauto. eauto. {
      eapply sem_tfold. eauto. 
      eapply IHW2. eapply IHW3. 3: eapply IHW1.
      unfold bsub. eauto. unfold bsub. eauto. eauto. 
      eapply hast_fv in W1; eauto. repeat rewrite plift_or in WFE. auto.
      intros ???????. eauto.
      2: { rewrite plift_or, plift_or in WFE. eauto. }
      unfold bsub in *. destruct ez,el,e2,a2; intuition.
      eauto. eauto.
      intros ??. eapply P1. destruct ez,el,e2,al,a2; intuition.
      intros ??. eapply P2. destruct ez,el,e2,al,a2; intuition.
    }
    unfold bsub. eauto.
    unfold bsub. destruct a2; intuition.
    unfold bsub. destruct ez,el,e2; intuition.    
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
  - (* sub_stp *)
    unfold bsub in *. 
    eapply IHW in WFE as A. 2: { unfold bsub. destruct e1, e2, um; simpl in *; intuition. }
    unfold exp_type_eff, exp_type, exp_type1 in A.
    edestruct A as (S1'&S2'&M'&?&?&?&?&?&?). all: eauto.
    { intros ? ?. eapply P1. destruct e1, e2; try contradiction; intuition. }
    { intros ? ?. eapply P2. destruct e1, e2; try contradiction; intuition. }
    unfold exp_type. unfold exp_type1.
    exists S1', S2', M', x, x0, (negb a2 || um), (if (negb a2 || um) then x2 else qempty), (if (negb a2 || um) then x3 else qempty).
    eapply exp_sub_stp2; eauto. 
    eapply stp_fundamental in H. eapply H.
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
  (W1: has_type G t1 TBool p1 fr1 a1 true)   (* effect *)
  (W2: has_type G t2 TBool p2 fr2 a2 false), (* no eff *)
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

Theorem reorder_tbin_eff': forall G t1 t2 p1 p2 a1 a2 fr1 fr2
  (W1: has_type G t1 TBool p1 fr1 a1 false)   (* no eff *)
  (W2: has_type G t2 TBool p2 fr2 a2 true), (* effect *)
  sem_type G (tbin t1 t2) (tbin t2 t1) TBool (por (plift p1) (plift p2)) false false true.
Proof.
  intros. intros uv E M H1 H2 V1 V2 WFE. intros SW ???? ST ELS1 ELS2.

  assert (length V1 = length G) as LV1. { destruct WFE as (? & ? & ? & ? & ?). auto. }
  assert (length V2 = length G) as LV2. { destruct WFE as (? & ? & ? & ? & ?). auto. }
  destruct uv; intuition. 

  (* t1 *)
  eapply fundamental in W1 as HE1.
  edestruct (HE1 false) as (S1' & S2' & M' & v1 & v1' & uv1 & lsv1 & lsv2 & STC' & STWF' & E1 & E1' & LS1 & LS2 & ST' & VT1 & UX1 & UX2 & LUX1 & LUX2 & VQ1 & VQ2 & SE1 & SE1' & STREL1).
  unfold bsub. intuition.
  eapply envt_strengthenW1. eapply envt_tighten. eauto. unfoldq; intuition. eauto. eauto. 
  unfoldq; intuition. unfoldq; intuition.

  assert (st_len1 M <= st_len1 M') as L1. { destruct ST. destruct ST'. lia. }
  assert (st_len2 M <= st_len2 M') as L2. { destruct ST. destruct ST'. lia. }
 

  (* t2 *)
  eapply store_invariance2' with (uv:=true) in W2 as W2'.
  destruct W2' as (S1'' & S2y'' & M'' & v2 & v2x & uv2 & lsv2' & lsv2x & W2').
  4: eapply SW.
  4: { eauto. }
  all: eauto. 
  2: { eapply envt_store_change. eapply envt_tighten. eauto. unfoldq. intuition.
       intros ?????. eauto. eauto. eauto. }
  2: { intros ? ?. eapply ELS1. rewrite exp_locs_tbin. right. eauto. }
  2: { intros ? ?. eapply ELS2. rewrite exp_locs_tbin. left. eauto. }
  2: { eapply storew_widen. eapply SE1. intros ?; intuition. }

  destruct W2' as (STC'' & STWF2 & E2' & E2 & LS1' & LS2' & ST'' & VT'' & UX3 & UX4 & LUX3 & LUX4 & VQ3 & VQ4 & SE2' & SE2 & STREL2).

  (* t1 *)
  eapply store_invariance3' with (uv:=false)(H1:=H1) (H2:=H2) (p1:=pempty) (p2:=pempty) in W1 as W1'.
  destruct W1' as (S1y' & S2'' & M''' & v1y & v1z & u1y & lsv1y & lsvz & W1').
  4: eapply SW.
  4: { destruct ST as (?&?&?). split. eauto. split. eauto. intros. contradiction. }
  all: eauto. 
  2: { unfold bsub. intuition. }
  2: { eapply envt_store_change. eapply envt_strengthenW1. eapply envt_tighten. eauto. unfoldq. intuition.
       intros ?????. eauto. eauto. eauto. }
  2: { unfoldq; intuition. }
  2: { unfoldq; intuition. }
  2: { eapply storew_widen. eapply SE2. unfoldq; intuition. }

  destruct W1' as (STC''' &  STWF''' & E1y & E2'' & LS1y & LS2'' & ST''' & VT''' & UX5 & UX6 & LUX5 & LUX6 & VQ5 & VQ6 & SE1y & SE2'' & STREL''').


  assert (S1y' = S1' /\ v1 = v1y) as C. {
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
    edestruct ST'' as (?&?&?); eauto. left. eauto. left. eauto.
    rewrite SE1y in H11. 2: { unfoldq. intuition. eapply indexr_var_some'. eauto. }
    rewrite H11 in H13. inversion H13. subst x0.
    exists x1. intuition. 
    rewrite SE2'' in H16. auto.
    unfoldq. intuition. eapply indexr_var_some'. eauto.
  - simpl. destruct b,b1; eauto.
  - eauto.
  - eauto.
  - intros ???. rewrite <-plift_empty. eauto.
  - intros ???. rewrite <-plift_empty. eauto.
  - rewrite plift_empty. unfoldq. intuition.
  - rewrite plift_empty. unfoldq. intuition. 
  - rewrite exp_locs_tbin. eapply storew_trans.
    eapply storew_widen. eauto. intros ??. unfoldq; intuition.
    eapply storew_widen. eauto. unfoldq. intuition. eauto.
  - rewrite exp_locs_tbin. eapply storew_trans.
    eapply storew_widen. eauto. unfoldq. intuition. 
    eapply storew_widen. eauto. unfoldq; intuition. lia. 
Qed.


Theorem reorder_tbin: forall G t1 t2 p1 p2 a1 a2 fr1 fr2 e1 e2
  (W1: has_type G t1 TBool p1 fr1 a1 e1)   
  (W2: has_type G t2 TBool p2 fr2 a2 e2), 
  e1 && e2 = false ->
  sem_type G (tbin t1 t2) (tbin t2 t1) TBool (por (plift p1) (plift p2)) false false true.
Proof.
  intros.
  destruct e1, e2.
  - simpl in *. inversion H.
  - eapply reorder_tbin_eff; eauto.
  - eapply reorder_tbin_eff'; eauto.
  - assert (sem_type G (tbin t1 t2) (tbin t2 t1) TBool (por (plift p1) (plift p2)) false false false).
    eapply reorder_tbin_mention; eauto.
    eapply sem_sub_eff; eauto. unfold bsub. intuition.
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
  | tnil          => tnil 
  | tcons t1 t2   => tcons (splice_tm t1 i n) (splice_tm t2 i n)
  | tfold f z t   => tfold (splice_tm f i n) (splice_tm z i n) (splice_tm t i n)
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
  | tnil          => tnil
  | tcons t1 t2   => tcons (subst_tm t1 i u ) (subst_tm t2 i u)
  | tfold f z t   => tfold (subst_tm f i (splice_tm u i 2)) (subst_tm z i u)(subst_tm t i u)
  | tref t        => tref (subst_tm t i u)
  | tget t        => tget (subst_tm t i u)
  | tput t1 t2    => tput (subst_tm t1 i u) (subst_tm t2 i u)
  | tapp t1 t2    => tapp (subst_tm t1 i u) (subst_tm t2 i u)
  | tabs t        => tabs (subst_tm t i (splice_tm u i 1)) 
  | tnot t        => tnot (subst_tm t i u)
  | tbin t1 t2    => tbin (subst_tm t1 i u)(subst_tm t2 i u)
end.

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
  + erewrite IHe1_1. erewrite IHe1_2. eauto.
  + erewrite IHe1_1. erewrite IHe1_2. erewrite IHe1_3. eauto.
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
  + rewrite IHe1_1. rewrite IHe1_2. auto.
  + rewrite IHe1_1. rewrite IHe1_2. rewrite IHe1_3. auto.
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
  - repeat rewrite plift_or in *. 
    repeat rewrite pdiff_or in *. 
    repeat rewrite vl_dist_or. intuition. 
    + destruct H. eapply IHt1 in H. left. eauto.
      eapply IHt2 in H. right. eauto.
    + destruct H. eapply IHt1 in H. left. eauto.
      eapply IHt2 in H. right. eauto. 
  - repeat rewrite plift_or in *. repeat rewrite pdiff_or in *. 
    repeat rewrite vl_dist_or in *. repeat rewrite plift_diff in *. 
    repeat rewrite plift_or in *. repeat rewrite plft_one in *.
    assert (forall A B, S (A + B) = (S A) + B) as R. lia.
    repeat rewrite R in *.
    intuition.
    + destruct H as [Hf | [Hz | Ht]].
      * left.  eapply vl_mono. 2: eapply IHt1.
        intros y Q. destruct Q as [Hfv Hrng].
        split. split. eauto. repeat rewrite plift_one. unfoldq; intuition. unfoldq; intuition.
        eapply vl_mono. 2: eapply Hf.
        intros y Q. destruct Q as [[Hfv Hne] Hrng].
        split. eauto. repeat rewrite plift_one in *. unfoldq; intuition.
      * eapply IHt2 in Hz. right. left. eauto.
      * eapply IHt3 in Ht. right. right. eauto.
    + destruct H as [Hf | [Hz | Ht]].
      * left.
        eapply vl_mono. 2: eapply IHt1.
        intros y Q. destruct Q as [Hfv Hrng].
        split. split. eauto. repeat rewrite plift_one. unfoldq; intuition. unfoldq; intuition.
        eapply vl_mono. 2: eapply Hf.
        intros y Q. destruct Q as [[Hfv Hne] Hrng].
        split. eauto. repeat rewrite plift_one in *. unfoldq; intuition.
      * eapply IHt2 in Hz. right. left. eauto.
      * eapply IHt3 in Ht. right. right. eauto.
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
  - repeat rewrite plift_or in *. rewrite plift_diff in *. rewrite plift_or in *. 
    repeat rewrite plift_one in *.
    destruct H. destruct H.
    left. split. eapply IHt1_1. eauto. lia. lia. unfoldq; intuition.
    destruct H. right. left. eauto.
    right. right. eauto.
  - rewrite plift_or in *. destruct H. left. eauto. right. eauto.
  - rewrite plift_or in *. destruct H. left. eauto. right. eauto.
  - erewrite plift_diff in *. rewrite plift_one in *.
    destruct H. split; eauto. unfoldq; intuition.
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
  - intuition.
  - bdestruct (i <? b). intuition.
    rewrite plift_one in *. split; intros; inversion H2. subst. lia.
    rewrite plift_one in *. inversion H2. lia.     
  - split; intros.
    rewrite plift_or in *. 
    destruct H1. left. eapply IHt1_1; eauto. right. eapply IHt1_2; eauto.
    rewrite plift_or in *. 
    destruct H1. left. eapply IHt1_1; eauto. right. eapply IHt1_2; eauto.
  - repeat rewrite plift_or in *. repeat rewrite plift_diff in *. repeat rewrite plift_or in *. repeat rewrite plift_one in *. 
    split; intros.
    destruct H1. destruct H1. left. split. eapply IHt1_1; eauto. auto.
    destruct H1. right. left. eapply IHt1_2; eauto. 
    right. right. eapply IHt1_3; eauto.
    destruct H1. destruct H1. left. split. eapply IHt1_1; eauto. auto. 
    destruct H1. right. left. eapply IHt1_2; eauto.
    right. right. eapply IHt1_3; eauto.   
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
  - rewrite plift_empty in *. contradiction.
  - rewrite plift_one in *. inversion H1.
    bdestruct (length H2 =? length H2).
    eapply fv_change_bound. eauto. lia. rewrite app_length. lia.
    contradiction.
  - rewrite plift_or in *. destruct H1. left. eauto. right. eauto.
  - repeat rewrite plift_or in *. repeat rewrite plift_diff in *. repeat rewrite plift_or in *.  repeat rewrite plift_one in *.
    destruct H1 as [Hfp | Hzt].
    destruct Hfp as [Hf Hne].
    left. split.
    replace (S (S (length (H2' ++ H2)))) with (length (([v;v] ++ H2') ++ H2)).
    eapply IHt2_1.
    eapply fv_splice_miss; eauto. eauto.
    replace (length (([v;v] ++ H2') ++ v::H2)) with (S (S (length (H2' ++ v::H2)))).
    eauto.
    repeat rewrite app_length. simpl. lia.
    repeat rewrite app_length. simpl. lia.
    unfoldq. intros [Hx|Hx]; rewrite app_length in *; lia.
    destruct Hzt as [Hz | Ht].
    right. left.
    eapply IHt2_2. eauto. eauto. eauto.
    right. right.
    eapply IHt2_3. eauto. eauto. eauto.
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
  - rewrite plift_or in *. rewrite subst_ql_or in *.
    destruct Q. left. eapply IHt1. eauto. right. eapply IHt2. eauto.
  - rewrite plift_or in *. rewrite plift_diff in *. repeat rewrite plift_or in *. repeat rewrite plift_one in *.
    repeat rewrite subst_ql_or in *. rewrite subst_ql_diff in *.
    destruct Q as [(Qf & Qfne) | [Qz | Qt]].
    specialize (IHt1 (splice_tm t0 (length G) 2) G ((T0,a0)::(T0,a0)::G') T0 a0).
    simpl in IHt1. eapply IHt1 in Qf.    
    left. split. eauto.
    rewrite subst_ql_or in Qfne.
    replace (S (length (G' ++ (T0, a0) :: G))) with (length (((T0,a0)::G') ++ (T0, a0) :: G)) in Qfne.
    rewrite (subst_ql_one_hit ((T0,a0)::G') G T0 a0) in Qfne.
    intros [? | ?]. eapply Qfne. left.
    replace (pone (S (length (((T0, a0) :: G') ++ (T0, a0) :: G)))) with (pone (length (((T0, a0)::(T0, a0) :: G') ++ (T0, a0) :: G))).
    rewrite subst_ql_one_hit. simpl. auto. simpl. auto. 
    eapply Qfne. right. simpl. auto. simpl. auto.
    right. left. eapply IHt2. eauto.
    right. right. eapply IHt3. eauto.
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

Lemma exp_tfold: forall S1 S2 M H1 H2 V1 V2 S1' S2' M' S1'' S2'' M''
                        f1 f2 z1 z2 t1 t2 T1 T2 (u: bool)
                        P1 P2
                        (a2 az al e2 ez el: bool),
    a2 = az ->
    stty_wellformed M ->
    store_type S1 S2 M P1 P2 ->
    psub (pif (ez || el || ((e2 || a2) || az || al) && e2) (exp_locs V1 (tfold f1 z1 t1))) P1 ->
    psub (pif (ez || el || ((e2 || a2) || az || al) && e2) (exp_locs V2 (tfold f2 z2 t2))) P2 ->
    bsub (ez || el || ((e2 || a2) || az || al) && e2) u ->
    exp_type1 S1 S2 M H1 H2 V1 V2 z1 z2 S1' S2' M' T2 u P1 P2 false az ez ->
    exp_type1 S1' S2' M' H1 H2 V1 V2 t1 t2 S1'' S2'' M'' (TList T1) u
      (por P1 (pdiff (pdom S1') (pdom S1)))
      (por P2 (pdiff (pdom S2') (pdom S2))) false al el ->
    (forall SX SY MX p1x p2x vz1 vz2 lsz1 lsz2 ve1 ve2 lse1 lse2 uz ul ur,
        st_chain M MX ->
        stty_wellformed MX ->
        store_type SX SY MX p1x p2x ->
        psub (pif (ez || el || (e2 || a2 || az || al) && e2)(exp_locs V1 (tfold f1 z1 t1))) p1x ->
        psub (pif (ez || el || (e2 || a2 || az || al) && e2)(exp_locs V2 (tfold f2 z2 t2))) p2x ->
        st_len1 M <= st_len1 MX ->
        st_len2 M <= st_len2 MX ->
        (uz = ((negb az)||u)) ->
        (ul = ((negb al)||u)) ->
        (e2||ur&&a2 = true -> uz = true) ->  
        (e2||ur&&a2 = true -> ul = true) ->
        (ur =(negb ((az||al||((e2||a2) (* &&a *)))&& a2)) || u) ->
        val_type MX vz1 vz2 T2 (uz = true) lsz1 lsz2 ->
        val_type MX ve1 ve2 T1 (ul = true) lse1 lse2 ->
        (ul  = false -> psub (plift lse1) pempty) ->
        (ul  = false -> psub (plift lse2) pempty) ->
         (psub (plift lse1) (por (pif (al) (exp_locs V1 t1)) (por (pif false (pnot pempty))  (pif false (pdiff (pdom S1'') (pdom S1')))))) ->
         (psub (plift lse2) (por (pif (al) (exp_locs V2 t2)) (por (pif false (pnot pempty))  (pif false (pdiff (pdom S2'') (pdom S2')))))) ->
        (uz  = false -> psub (plift lsz1) pempty) ->
        (uz  = false -> psub (plift lsz2) pempty) ->
         (psub (plift lsz1) (por (pif (az) (exp_locs V1 (tfold f1 z1 t1))) (por (pif false (pnot pempty))  (pif false (pdiff (pdom S1') (pdom S1)))))) ->
         (psub (plift lsz2) (por (pif (az) (exp_locs V2 (tfold f2 z2 t2))) (por (pif false (pnot pempty))  (pif false (pdiff (pdom S2') (pdom S2)))))) ->
        exp_type SX SY MX
          (vz1 :: ve1 :: H1) (vz2 :: ve2 :: H2)
          (lsz1 :: lse1 :: V1) (lsz2 :: lse2 :: V2)
          f1 f2 T2 ur p1x p2x false a2 e2) ->
    exp_type S1 S2 M H1 H2 V1 V2 (tfold f1 z1 t1) (tfold f2 z2 t2) T2 u P1 P2
      false ((az || al || ((e2 || a2))) && a2) (ez || el || ((e2 || a2) || az || al) && e2).
Proof. 
  intros. rename H3 into ST. rename H4 into STP1. rename H5 into STP2. rename H9 into HF. 
  destruct H7 as (vz1 & vz2 & uz & lsz1 & lsz2 & SC1 & SWM1 & EZ1 & EZ2 & LS1 & LS2 & ST1 & VZ & UZ & TT1 & QZ1 & QZ2 & QZ3 & QZ4 & SW1 & SW2 & STRELZ).
  destruct H8 as (vl1 & vl2 & ul & lsl1 & lsl2 & SC2 & SWM2 & EL1 & EL2 & LS3 & LS4 & ST2 & VL & UL & TT2 & QL1 & QL2 & QL3 & QL4 & SW3 & SW4 & STRELL). 
  
  remember VL as VL'. clear HeqVL'.
  destruct vl1, vl2; simpl in VL; intuition.

 assert (forall vz1 vz2 lsz1' lsz2' ve1 ve2 lse1 lse2 SX SY MXY ur uf, 
      (ul = false  -> psub (plift lse1) pempty) ->
      (ul = false  -> psub (plift lse2) pempty) ->
      (uz = false  -> psub (plift lsz1') pempty) ->
      (uz = false  -> psub (plift lsz2') pempty) ->
      (* (psub (plift lsz1) (por (pif az (exp_locs V1 z1)) (por (pif false (pnot pempty))(pif false (pdiff (pdom S1') (pdom S1)))))) -> *)
      (psub (plift lsz1') (por (pif (az) (exp_locs V1 (tfold f1 z1 t1))) (por (pif false (pnot pempty))(pif false (pdiff (pdom S1') (pdom S1)))))) ->
      
      (psub (plift lsz2') (por (pif (az) (exp_locs V2 (tfold f2 z2 t2))) (por (pif false (pnot pempty))(pif false (pdiff (pdom S2') (pdom S2)))))) ->
      (psub (plift lse1) (por (pif al (exp_locs V1 t1)) (por (pif false (pnot pempty))(pif false (pdiff (pdom S1'') (pdom S1')))))) ->
      (psub (plift lse2) (por (pif al (exp_locs V2 t2)) (por (pif false (pnot pempty))(pif false (pdiff (pdom S2'') (pdom S2')))))) ->
      (* (uf = (negb a) ||u) -> *)
      (e2||ur&&a2 = true -> uf = true) -> 
      (e2||ur&&a2 = true -> uz = true) ->  
      (e2||ur&&a2 = true -> ul = true) ->
      (ur =(negb ((az||al||((e2||a2) (* &&a *)))&& a2)) || u) ->
     (* (false||(az||al) = false  -> uz = true) ->
      (false||al = false  -> ul = true) -> *)
      store_type SX SY MXY 
          (por (por (por P1 (pdiff (pdom S1') (pdom S1))) (pdiff (pdom S1'') (pdom S1'))) (pdiff (pdom SX)(pdom S1'')))
          (por (por (por P2 (pdiff (pdom S2') (pdom S2))) (pdiff (pdom S2'') (pdom S2'))) (pdiff (pdom SY)(pdom S2''))) ->
      length S1'' <= length SX ->
      length S2'' <= length SY ->    
      st_chain M'' MXY -> 
      stty_wellformed MXY ->
      val_type MXY ve1 ve2 T1 (ul = true) lse1 lse2 ->
      val_type MXY vz1 vz2 T2 (uz = true) lsz1' lsz2' ->
      exists vr1 vr2 lsr1 lsr2 SR1 SR2 MR, 
         tevaln SX (vz1 :: ve1::  H1) f1 SR1 vr1 /\
         tevaln SY (vz2 :: ve2::  H2) f2 SR2 vr2 /\
         length SX <= length SR1 /\
         length SY <= length SR2 /\
         store_type SR1 SR2 MR  
              (por (por (por (por P1 (pdiff (pdom S1') (pdom S1))) (pdiff (pdom S1'') (pdom S1'))) (pdiff (pdom SR1)(pdom S1''))) (pdiff (pdom SR1)(pdom SX))) 
              (por (por (por (por P2 (pdiff (pdom S2') (pdom S2))) (pdiff (pdom S2'') (pdom S2'))) (pdiff (pdom SR2)(pdom S2''))) (pdiff (pdom SR2)(pdom SY))) /\
         st_chain MXY MR /\
         stty_wellformed MR /\
         val_type MR vr1 vr2 T2 (ur = true) lsr1 lsr2 /\
         (* (ur = true (*(negb (a2) || u *)) /\ *)
         (ur = false -> psub (plift lsr1) pempty) /\
         (ur = false -> psub (plift lsr2) pempty) /\
         psub (plift lsr1) (por (pif a2 (exp_locs (lsz1'::lse1::(restrictV ((e2||a2) (* &&  a *) && u) V1)) f1))(por (pif false (pnot pempty)) (pif false (pdiff (pdom SR1)(pdom SX))))) /\
         psub (plift lsr2) (por (pif a2 (exp_locs (lsz2'::lse2::(restrictV ((e2||a2) (* &&  a *) && u) V2)) f2))(por (pif false (pnot pempty)) (pif false (pdiff (pdom SR2)(pdom SY))))) /\
         store_write SX SR1 (pif  (e2) (exp_locs (lsz1'::lse1::(restrictV ((e2||a2) (* &&  a *) && u) V1)) f1)) /\
         store_write SY SR2 (pif  (e2) (exp_locs (lsz2'::lse2::(restrictV ((e2||a2) (* &&  a *) && u) V2)) f2)) /\
         (false = false -> strel MR = strel MXY)
      ) as HFF. {
        intros. 
        
         remember (e2||ur&&a2) as D.
         destruct D.
         + (* use *)
          assert (u = false -> (* a = true -> *) e2 = false). destruct u,e2; intuition.
          assert (u = false -> (* a = true -> *) a2 = false). subst. unfold bsub in *. destruct u, az; simpl in *; intuition. 
          (* assert (u = false -> a = false). intros. destruct a. {
          replace a2 with false in *. 2: intuition.
          replace e2 with false in *. 2: intuition.
          destruct ur; inversion HeqD. } *) eauto. 
                
          assert (e2||a2 = true) as A. destruct e2,a2; intuition. 
          rewrite A in *.
          
          edestruct HF with (ur := true)(MX := MXY)(SX := SX)(SY := SY)
          as (S1''' & S2''' & M''' & vf1 & vf2 & uf' & lsf1 & lsf2 & SC3 & STW3 & EF1 & EF2 & LSF1 & LSF2 & ST''' & VF & UF & ZF & QF1 & QF2 & QF3 & QF4 & SW1' & SW2' & STREL3). 
          9: eauto. 9: eauto. 
          { eapply stchain_chain; eauto. eapply stchain_chain; eauto.  }
          eauto. eauto.
          { simpl in *. intros ? ?. left. left. left. eapply STP1. auto. } 
          { simpl in *. intros ? ?. left. left. left. eapply STP2. auto. } 
          { destruct ST, ST1, ST2, H18. lia. }
          { destruct ST, ST1, ST2, H18. lia. }
          { destruct e2, a2, az, u; simpl in *; auto.  }
          { eauto.  }
          { destruct az, al, a2, u; simpl in *; intuition. }
          { eapply valt_usable; eauto. }
          eauto. eauto. eauto. eauto. eauto. eauto. eauto. 
          eauto. eauto.

          assert (uf' = true). { destruct a2; simpl in *; auto. }
          assert (uf = true). { destruct a2; simpl in *; auto.  }
          assert (ur = true) as B. { subst ur. unfold bsub in *. destruct az, al, a2, u, ez, el, e2; simpl in *; intuition.  }
          rewrite B in *. simpl in *.
          eexists. eexists. exists  lsf1. exists lsf2.  exists S1'''. exists S2'''. exists M'''.
          split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 8: split. 9: split. 10: split. 
          11: split. 12: split. 13: split. 14: split. 
          all: eauto.

          eapply storet_tighten. eauto. 
          repeat rewrite por_assoc. rewrite pdiff_merge. rewrite pdiff_merge. 
          intros ? [? | [? | ?]]. left. auto. right. left. auto. rewrite por_comm. rewrite pdiff_merge.
          left. unfoldq; intuition. all: auto. lia. lia.

          repeat rewrite por_assoc. rewrite pdiff_merge. rewrite pdiff_merge. 
          intros ? [? | [? | ?]]. left. auto. right. left. auto. rewrite por_comm. rewrite pdiff_merge.
          left. unfoldq; intuition. all: auto. lia. lia.

          {
            rewrite H27 in VF. eauto.  
          }
          {
            repeat rewrite pif_false in *. repeat rewrite por_empty_r in *.
            intros ? Q. eapply QF3 in Q.
            destruct a2; try contradiction. 
            assert (u = true). { subst. simpl in *. eapply H15; auto. }
            subst u. auto.
          }
          {
            repeat rewrite pif_false in *. repeat rewrite por_empty_r in *.
            intros ? Q. eapply QF4 in Q.
            destruct a2; try contradiction. 
            assert (u = true). { subst. simpl in *. eapply H15; auto. }
            subst u. auto.

          }
          {
            intros ? ?. rewrite SW1'. auto. destruct H29. split; auto.
            intros Q. eapply H30. destruct e2; try contradiction.
            assert (u = true). { subst. simpl in *. destruct u; simpl; intuition.  }
            subst u. auto.
          }
          {
            intros ? ?. rewrite SW2'. auto. destruct H29. split; auto.
            intros Q. eapply H30. destruct e2; try contradiction.
            assert (u = true). { subst. simpl in *. destruct u; simpl; intuition.  }
            subst u. auto.
          }
          
      + (* mention *) 
        assert (e2 = false). destruct e2,a2; intuition.
        assert (a2 = false \/ u = false). { unfold bsub in *. destruct e2,a2,ur, az,al,u; intuition. }
        subst e2.

        edestruct HF with (ur := ur)(MX := MXY)(SX := SX)(SY := SY)(*(H1 := (vz0::ve1::H1))(H2 := (vz3::ve2 :: H2))
             (V1 := lsz0 ::lse1 :: (restrictV u V1)) (V2 := lsz3 ::lse2 :: (restrictV u V2))*)(lsz1 := lsz1')(lsz2 := lsz2')
          as (S1''' & S2''' & M''' & vf1 & vf2 & uf' & lsf1 & lsf2 & SC3 & STW3 & EF1 & EF2 & LSF1 & LSF2 & ST''' & VF & UF & ZF & QF1 & QF2 & QF3 & QF4 & SW1' & SW2' & STREL3). 
        
        { eapply stchain_chain; eauto. eapply stchain_chain; eauto.  }
        eauto. eauto. 
        { 
          intros ? Q. left. left. left. eapply STP1. auto.
        }
        { 
          intros ? Q. left. left. left. eapply STP2. auto.
        }
        { destruct ST, ST1, ST2, H18. lia. }
        { destruct ST, ST1, ST2, H18. lia. }
        { eauto. } eauto.
        eauto. eauto. 
        { destruct az, al, a2, u; simpl in *; intuition. }
        { eapply valt_usable. eapply H24. intros. subst a2. destruct az; simpl in *; intuition. }
        { eapply valt_usable. eapply H23. intros. auto.  }
        { intros. eapply H5; eauto. } 
        { intros. eapply H7; eauto. } 
        { auto. } 
        { auto. }
        all: auto. 
             
        eexists. eexists. exists  lsf1. exists lsf2.  exists S1'''. exists S2'''. exists M'''.
        split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 8: split. 9: split. 10: split. 
        11: split. 12: split. 13: split. 14: split. 
        all: eauto.

        eapply storet_tighten. eauto. 
        repeat rewrite por_assoc. rewrite pdiff_merge. rewrite pdiff_merge. 
        intros ? [? | [? | ?]]. left. auto. right. left. auto. rewrite por_comm. rewrite pdiff_merge.
        left. unfoldq; intuition. all: auto. lia. lia.
        repeat rewrite por_assoc. rewrite pdiff_merge. rewrite pdiff_merge. 
        intros ? [? | [? | ?]]. left. auto. right. left. auto. rewrite por_comm. rewrite pdiff_merge.
        left. unfoldq; intuition. all: auto. lia. lia.
        {
          destruct a2; simpl in *. {
            assert (ur = false). {
              destruct ur; simpl in *. inversion HeqD. auto.
            }
            rewrite H25.
            subst ur. destruct H26. inversion H17. subst u.
            assert (uf' = false). destruct az, al; simpl in *; intuition.
            rewrite H17 in VF. eauto.
          }{
            subst uf'.
            destruct ur. {
              auto.
            } {
              eapply valt_usable; eauto.
            }
          }
        }  
       {
        intros. subst ur. simpl in *.
        destruct H26. {
          subst a2. subst az. simpl in *. repeat rewrite pif_false in *. repeat rewrite por_empty_r in *. eauto.
        } {
          subst u. simpl in *. destruct a2; simpl in *. eapply QF1; eauto.
          repeat rewrite pif_false in *. repeat rewrite por_empty_r in *. eauto.
        }
       }
       {
        intros. subst ur. simpl in *.
        destruct H26. {
          subst a2. subst az. simpl in *. repeat rewrite pif_false in *. repeat rewrite por_empty_r in *. eauto.
        } {
          subst u. simpl in *. destruct a2; simpl in *. eapply QF2; eauto.
          repeat rewrite pif_false in *. repeat rewrite por_empty_r in *. eauto.
        }
       }
       {
          destruct H26. subst a2. subst az. repeat rewrite pif_false in *. repeat rewrite por_empty_r in *. 
          intros ? Q. eapply QF3 in Q. auto.
          subst a2. destruct az; simpl in *. subst. intros ? ?. eapply QF1 in H; eauto. unfoldq; intuition.
          rewrite UF in *. eapply QF3. 
        }

        {
          repeat rewrite pif_false in *. repeat rewrite por_empty_r in *. 
          intros ? Q.
          destruct a2; simpl in *. rewrite UF in *. eapply QF2 in Q; eauto. contradiction. 
          destruct H26. inversion H25. subst u. simpl in *. destruct ur; simpl in *; intuition.
          rewrite UF in *. eapply QF4. eauto.
        }
     }     

   remember ((negb ((az||al||((e2||a2)(*  &&a *) ))&& a2)) || u) as ur.
   assert (e2||ur&&a2 = true -> negb (az||al) || u = true) as A. {
     intros ?. subst ur. unfold bsub in *. destruct e2, az, al, a2, u; simpl in *; intuition.
   }

   assert (e2||ur&&a2 = true -> negb az || u = true)  as B. {
     intros ?. subst ur. unfold bsub in *. destruct e2, az, al, a2, u; simpl in *; intuition.
   }

     assert (e2||ur&&a2 = true -> negb al || u = true)  as B'. {
     intros ?. subst ur. unfold bsub in *. destruct e2, az, al, a2, u; simpl in *; intuition.
   }

   assert (e2||ur&&a2 = true -> (* negb a || *)  u = true) as C. {
    intros ?. subst ur. unfold bsub in *. destruct e2, az, al, a2, u; simpl in *; intuition.
   }


  remember (fun n => fun (hd:vl) (tl:stor * option (option vl)) =>
      match tl with
       | (S0, None) => (S0, None)
       | (S0, Some None) => (S0, Some None)
       | (S0, Some (Some vtl)) =>  teval n S0 (vtl::hd::H1) f1
  end) as ff1.

  remember (fun n => fun (hd:vl) (tl:stor * option (option vl)) =>
      match tl with
       | (S2''', None) => (S2''', None)
       | (S2''', Some None) => (S2''', Some None)
       | (S2''', Some (Some vtl)) =>  teval n S2''' (vtl::hd::H2) f2
  end) as ff2.

  assert (
      exists vr1 vr2 lsvr1 lsvr2 SR1 SR2 MR,
      (exists nm, forall n, n > nm ->
        fold_right (ff1 n) (S1'', Some (Some vz1)) l = (SR1, Some (Some vr1))) /\
      (exists nm, forall n, n > nm ->
        fold_right (ff2 n) (S2'', Some (Some vz2)) l0 = (SR2, Some (Some vr2))) /\  
      length S1'' <= length SR1 /\
      length S2'' <= length SR2 /\
      store_type SR1 SR2 MR 
              (por (por (por P1 (pdiff (pdom S1') (pdom S1))) (pdiff (pdom S1'') (pdom S1'))) (pdiff (pdom SR1)(pdom S1''))) 
              (por (por (por P2 (pdiff (pdom S2') (pdom S2))) (pdiff (pdom S2'') (pdom S2'))) (pdiff (pdom SR2)(pdom S2''))) /\
      st_chain M'' MR /\  
      stty_wellformed MR /\
      (* (e2||ur&&a2 = true -> uf = true) ->  *)
      (* (e2||ur&&a2 = true -> negb az || u = true) /\  
      (e2||ur&&a2 = true -> negb al || u = true) /\ *)
      val_type MR vr1 vr2 T2 (ur = true) lsvr1 lsvr2 /\
      (ur = false -> psub (plift lsvr1) pempty) /\
      (ur = false -> psub (plift lsvr2) pempty) /\
      (psub (plift lsvr1) (por (pif ((az||al||((e2||a2) (* &&a*)))&& a2) (exp_locs V1 (tfold f1 z1 t1))) (por (pif false (pnot pempty)) (pif false (pdiff (pdom S1'')(pdom SR1)))))) /\ 
      (psub (plift lsvr2) (por (pif ((az||al||((e2||a2) (* &&a *) ))&& a2) (exp_locs V2 (tfold f2 z2 t2))) (por (pif false (pnot pempty)) (pif false (pdiff (pdom S2'')(pdom SR2)))))) /\ 
      store_write S1'' SR1 (pif (ez || el || ((e2 || a2) (*&& a *) || az || al) && e2)  (exp_locs V1 (tfold f1 z1 t1))) /\
      store_write S2'' SR2 (pif (ez || el || ((e2 || a2) (* && a *) || az || al) && e2)  (exp_locs V2 (tfold f2 z2 t2))) /\
      (false = false -> strel MR = strel M'')
      ) as FOLD. {
    clear EL1. clear EL2. generalize dependent l0.
    induction l; intros; destruct l0.
    - remember (e2||ur&&a2) as D.
      destruct D.
      * (* use *)
        assert (u = false -> (* a = true -> *) e2 = false). destruct u,e2; intuition.
        assert (u = false -> (* a = true -> *) a2 = false). subst. unfold bsub in *. destruct u; simpl in *; intuition. 
        (*assert (u = false -> a = false). intros. destruct a. {
          replace a2 with false in *. 2: intuition.
          replace e2 with false in *. 2: intuition.
          destruct ur; inversion HeqD. } *) eauto. 
                
        assert (e2||a2 = true). destruct e2,a2; intuition. 
      
        exists vz1, vz2.  exists  (qor lsz1 (qif  ((az||al||((e2||a2) (* &&a *) ))&& a2) lsl1)),  (qor lsz2 (qif  ((az||al||((e2||a2) (* &&a *) ))&& a2) lsl2)), S1'', S2'', M''. 
        split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split.  8: split. 9: split. 10: split. 11: split. 12: split.
        13: split. 14: split. 
        exists 0. intros. simpl. eauto. 
        exists 0. intros. simpl. eauto.
        lia. lia.
        rewrite pdiff_same. rewrite pdiff_same. rewrite por_empty_r. rewrite por_empty_r. auto.
        eauto.
        eapply stchain_refl.
        eauto.
        {
          eapply valt_store_change.
          eapply valt_sub_locs. eapply valt_usable.  eapply VZ. destruct az, al; simpl in *; intuition. subst uz. auto. subst uz. auto. subst uz. auto.
          rewrite plift_or. unfoldq; intuition. rewrite plift_or. unfoldq; intuition. 
          intros ??????. auto. destruct ST1, ST2. lia. destruct ST1, ST2. lia.
        }
        { 
          repeat rewrite pif_false in *. repeat rewrite por_empty_r in *.
          intros ? ? Q. rewrite H9 in *. rewrite plift_or in Q. rewrite H in *. 
          subst ur. simpl in *. rewrite plift_if in Q.
          destruct Q as [Q | Q].
          + destruct az; try contradiction; simpl in *.
            ++ eapply QZ1; auto. rewrite UZ. congruence.
            ++ rewrite UZ in *. eapply QZ3 in Q. contradiction.
          + destruct az; try contradiction; simpl in *.
            ++ subst u. subst uz. intuition.
            ++ destruct al; simpl in *. contradiction. destruct e2; simpl in *; try contradiction. 
        } 
        { 
          repeat rewrite pif_false in *. repeat rewrite por_empty_r in *.
          intros ? ? Q. rewrite H9 in *. rewrite plift_or in Q. rewrite H in *. 
          subst ur. simpl in *. rewrite plift_if in Q.
          destruct Q as [Q | Q].
          + destruct az; try contradiction; simpl in *.
            ++ eapply QZ2; auto. rewrite UZ. congruence.
            ++ rewrite UZ in *. eapply QZ4 in Q. contradiction.
          + destruct az; try contradiction; simpl in *.
            ++ subst u. subst uz. intuition.
            ++ destruct al; simpl in *. contradiction. destruct e2; simpl in *; contradiction.
        }

        {
          repeat rewrite pif_false in *. repeat rewrite por_empty_r in *.
          rewrite plift_or. rewrite H in *. rewrite plift_if. 
          intros ? [Q| Q].
          + destruct az; simpl in *.
            ++ eapply QZ3 in Q; auto. 
               unfold exp_locs in *. eapply vars_locs_mono; eauto.
               simpl. rewrite plift_or, plift_diff. repeat rewrite plift_or. repeat rewrite plift_one.
               unfoldq; intuition.
            ++ eapply QZ3 in Q. contradiction.
          + remember  ((az || al || (e2||az) (* && a *) ) && az) as b.
            destruct b; try contradiction. eapply QL3 in Q.
            destruct al; try contradiction.
            unfold exp_locs in *. eapply vars_locs_mono; eauto.
            simpl. rewrite plift_or, plift_diff. repeat rewrite plift_or. repeat rewrite plift_one.
            unfoldq; intuition.
        }

        {
          repeat rewrite pif_false in *. repeat rewrite por_empty_r in *.
          rewrite plift_or. rewrite H in *. rewrite plift_if. 
          intros ? [Q| Q].
          + destruct az; simpl in *.
            ++ eapply QZ4 in Q; auto. 
               unfold exp_locs in *. eapply vars_locs_mono; eauto.
               simpl. rewrite plift_or, plift_diff. repeat rewrite plift_or. repeat rewrite plift_one.
               unfoldq; intuition.
            ++ eapply QZ4 in Q. contradiction.
          + remember  ((az || al || (e2||az) (* && a *)) && az) as b.
            destruct b; try contradiction. eapply QL4 in Q.
            destruct al; try contradiction.
            unfold exp_locs in *. eapply vars_locs_mono; eauto.
            simpl. rewrite plift_or, plift_diff. repeat rewrite plift_or. repeat rewrite plift_one.
            unfoldq; intuition.
        }
         
        eapply storew_refl; eauto.
        eapply storew_refl; eauto.

        auto.

      * assert (e2 = false). destruct e2,a2; intuition.
        assert (a2 = false \/ u = false). { unfold bsub in *. destruct e2,a2,ur, az,al,u; intuition. }
        subst e2. simpl in *.
        exists vz1, vz2.  exists (qor lsz1 (qif  ((az || al || a2 (* && a *) ) && a2) lsl1)),  (qor lsz2 (qif  ((az || al || a2 (* && a *) ) && a2) lsl2)), S1'', S2'', M''. 
        split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split.  8: split. 9: split. 10: split. 11: split. 12: split.
        13: split. 14: split. 
        exists 0. intros. simpl. eauto. 
        exists 0. intros. simpl. eauto.
        lia. lia.
        rewrite pdiff_same. rewrite pdiff_same. rewrite por_empty_r. rewrite por_empty_r. auto.
        eauto.
        eapply stchain_refl.
        eauto.
        auto.
        {
          eapply valt_store_change. subst a2.
          destruct H7. {
            subst az. simpl in *. eapply valt_sub_locs. eapply valt_usable.  eapply VZ. intuition. 
            rewrite plift_or. unfoldq; intuition. rewrite plift_or. unfoldq; intuition.
          } {
            subst u. eapply valt_sub_locs. eapply valt_usable.  eapply VZ. intuition.  subst ur. destruct az; simpl in *; intuition.
            rewrite plift_or. unfoldq; intuition. rewrite plift_or. unfoldq; intuition.
          }
                    
          intros ??????. auto. destruct ST1, ST2. lia. destruct ST1, ST2. lia.
        }
        { 
        
          repeat rewrite pif_false in *. repeat rewrite por_empty_r in *.
          intros ? ? Q. subst a2 ur. simpl in *. rewrite plift_or in Q. 
          destruct Q as [Q | Q].
          + destruct H7. 
            ++ subst az. simpl in *.  assert False. destruct al; simpl in *; intuition. contradiction.
            ++ subst u. destruct az; simpl in *. eapply QZ1; auto. destruct al; simpl in *. inversion H5. inversion H5.
          + destruct H7.
            ++ subst az. simpl in *. destruct al; simpl in *. inversion H5. inversion H5. 
            ++ subst u. destruct az; simpl in *. destruct al; simpl in *. eapply QL1; auto. rewrite pif_false in QL3. eapply QL3. auto.
               destruct al; simpl in *. inversion H5. inversion H5.
        }    
        { 
        
          repeat rewrite pif_false in *. repeat rewrite por_empty_r in *.
          intros ? ? Q. subst a2 ur. simpl in *. rewrite plift_or in Q. 
          destruct Q as [Q | Q].
          + destruct H7. 
            ++ subst az. simpl in *.  assert False. destruct al; simpl in *; intuition. contradiction.
            ++ subst u. destruct az; simpl in *. eapply QZ2; auto. destruct al; simpl in *. inversion H5. inversion H5.
          + destruct H7.
            ++ subst az. simpl in *. destruct al; simpl in *. inversion H5. inversion H5. 
            ++ subst u. destruct az; simpl in *. destruct al; simpl in *. eapply QL2; auto. rewrite pif_false in QL4. eapply QL4. auto.
               destruct al; simpl in *. inversion H5. inversion H5.
        }

        {
          repeat rewrite pif_false in *. repeat rewrite por_empty_r in *.
          rewrite plift_or. 
          intros ? [Q| Q].
          + destruct H7.
            ++ subst a2. subst az. simpl in *. eapply QZ3 in Q; eauto. contradiction.
            ++ subst u. simpl in *. subst a2. destruct az; simpl in *. 
               { eapply QZ1 in Q. unfoldq; intuition. auto. }  
               { simpl in *. eapply QZ3 in Q. contradiction. }
          + destruct H7.
            ++ subst a2. subst az. simpl in *. destruct al; simpl in *; intuition. 
            ++ subst u. remember ((az || al || a2 (*&& a *)) && a2) as b.
                destruct b; simpl in *; intuition. eapply QL3 in Q. destruct al; try contradiction.
                unfold exp_locs in *. eapply vars_locs_mono; eauto.
                simpl. rewrite plift_or, plift_diff. repeat rewrite plift_or. repeat rewrite plift_one.
                unfoldq; intuition.
        }
        
        {
          repeat rewrite pif_false in *. repeat rewrite por_empty_r in *.
          rewrite plift_or. 
          intros ? [Q| Q].
          + destruct H7.
            ++ subst a2. subst az. simpl in *. eapply QZ4 in Q; eauto. contradiction.
            ++ subst u. simpl in *. subst a2. destruct az; simpl in *. 
               { eapply QZ2 in Q. unfoldq; intuition. auto. }  
               { simpl in *. eapply QZ4 in Q. contradiction. }
          + destruct H7.
            ++ subst a2. subst az. simpl in *. destruct al; simpl in *; intuition. 
            ++ subst u. remember ((az || al || a2 (* && a *) ) && a2) as b.
                destruct b; simpl in *; intuition. eapply QL4 in Q. destruct al; try contradiction.
                unfold exp_locs in *. eapply vars_locs_mono; eauto.
                simpl. rewrite plift_or, plift_diff. repeat rewrite plift_or. repeat rewrite plift_one.
                unfoldq; intuition.
        }

        
         
        eapply storew_refl; eauto.
        eapply storew_refl; eauto.
        
        auto.
 
    - inversion VL.
    - inversion VL.
    - inversion VL. subst x l1 y l'. 
      edestruct IHl as (vr1 & vr2 & lsr1 & lsr2 & SR1 & SR2 & MR &(nr1' & A') & (nr2' & B'') & LR1 & LR2 & STR & STCR & STWR & VR & QR1 & QR2 & QR3 & QR4 & STWR1 & STWR2 & STRELR). eauto. eauto.
      simpl. 
      remember (e2||ur&&a2) as D.
      destruct D.
         * (* use *)
           assert (u = false -> (* a = true -> *) e2 = false). destruct u,e2; intuition.
           assert (u = false -> (* a = true -> *)  a2 = false). subst. unfold bsub in *. destruct u; simpl in *; intuition. 
           (* assert (u = false -> a = false). intros. destruct a. {
             replace a2 with false in *. 2: intuition.
             replace e2 with false in *. 2: intuition.
             destruct ur; inversion HeqD. } *) eauto. 
                   
           assert (e2||a2 = true). destruct e2,a2; intuition. 
   
           edestruct HFF with  (SX := SR1)(SY := SR2)(MXY := MR) 
           as (vr1' & vr2' & lsr1' & lsr2' & SR1' & SR2' & MR' & (n1' & E1) & (n2' & E2) & LSR1 & LSR2 & STR' & SCR' & STWR' & VTR' & QR1' & QR2' & QR3' & QR4' & STWR1' & STWR2' & STRELR').
           9: { eauto.  }
           9: { eauto. }
           9: { eauto. }
           9: { eauto. }
           9: { eauto. }
          14: { rewrite H8 in *.
                destruct az.
                - subst uz.  rewrite H in *. simpl in *. subst ur.  eapply VR.
                - simpl in *.
                  assert (ur = true). { rewrite H in *. destruct al,u; simpl in *; intuition.  }
                  rewrite H10 in *. rewrite UZ. eapply VR.
          }      

          13: { eapply valt_store_change. eapply H9. 
                intros ? ? ? ? ? ?.  eapply STCR. auto.
                destruct ST2, STR. lia. destruct ST2, STR. lia. }
          {  
            intros Q. subst ul. eapply QL1. auto.
          }
          { 
            intros Q. eapply QL2. auto.
          }
          {

            intros Q. rewrite H in *. subst uz.
            rewrite B in Q.  inversion Q. auto.
          }
          {

            intros Q. rewrite H in *. subst uz.
            rewrite B in Q.  inversion Q. auto.
          }

          {

            repeat rewrite pif_false in *. repeat rewrite por_empty_r in *.
            rewrite H8 in *. simpl in *.
            remember  ((az || al (* ||  a *)) && a2)  as b.
            destruct b; simpl in *. {
              subst.
              intros ? Q.  eapply QR3 in Q.
              destruct az. simpl in *.  auto.
              intuition.
            }{
              intros ? Q. eapply QR3 in Q.
              destruct az, al, a2; simpl in *; intuition.
            }
          }

          {

            repeat rewrite pif_false in *. repeat rewrite por_empty_r in *.
            rewrite H8 in *. simpl in *.
            remember  ((az || al (* ||  a *) ) && a2)  as b.
            destruct b; simpl in *. {
              subst.
              intros ? Q.  eapply QR4 in Q.
              destruct az. auto. intuition.
            }{
              intros ? Q. eapply QR4 in Q.
              destruct az, al, a2; simpl in *; intuition.
            }
          }



          { repeat rewrite pif_false in *. repeat rewrite por_empty_r in *. auto.  }
          { repeat rewrite pif_false in *. repeat rewrite por_empty_r in *. auto.  }

          lia. lia.
          eauto.
          auto.

          exists vr1', vr2'. exists (qif ((negb a2)||u) lsr1'), (qif ((negb a2)||u) lsr2'), SR1', SR2', MR'. 
          split. 2: split.  3: split. 4: split. 5: split. 6: split. 7: split. 8: split. 9: split. 10: split. 11: split. 12: split. 13: split.
          14: split. 
          exists (nr1'+n1'). intros. rewrite A'. 2: lia.
          subst ff1. eapply E1. lia.
          exists (nr2'+n2'). intros. rewrite B''. 2: lia.
          subst ff2. eapply E2. lia.
          lia. lia.
          {
            repeat rewrite por_assoc in *. 
            rewrite pdiff_merge in *. rewrite pdiff_merge in *.  rewrite pdiff_merge in *.
            rewrite pdiff_merge in *. 
            all: eauto. 2: lia. 2: lia. 2: lia. 2: lia. 2: lia. 2: lia.
            eapply storet_tighten. eauto. 
            intros ? [?| ?]. left. auto. right. unfoldq. lia.
            intros ? [?| ?]. left. auto. right. unfoldq. lia.
          }

          eapply stchain_chain. eauto. auto.
          auto.
          eauto.

          { 
            subst ur.
            remember (negb ((az || al || (e2 || a2) (* && a *) ) && a2) || u)  as b.
            destruct b. {
              eapply valt_usable. eapply valt_sub_locs. eapply VTR'. 3: { eauto. }
              destruct a2. simpl in *. {
                destruct u; simpl in *. {
                  unfoldq; intuition.
                } {
                  intros ? Q. eapply QR3' in Q. repeat rewrite pif_false in *. repeat rewrite por_empty_r in *.
                  eapply exp_locs_tfold with (z := z1)(t:= t1) in Q.
                  destruct Q as [Q| [Q|Q]].
                  - replace ((e2||true)&&false) with false in Q. eapply aux2 in Q. unfoldq; intuition. destruct e2; simpl in *; intuition.
                  - rewrite H5 in *; auto. eapply QR1 in Q. unfoldq; intuition. destruct az, al, e2; simpl in *; intuition.
                  - destruct al; simpl in *.  eapply QL1 in Q; auto. unfoldq; intuition. rewrite pif_false in *. eapply QL3 in Q. unfoldq; intuition.
                }
              } {
                simpl in *. unfoldq; intuition.
              }

              destruct a2. simpl in *. {
                destruct u; simpl in *. {
                  unfoldq; intuition.
                } {
                  intros ? Q. eapply QR4' in Q. repeat rewrite pif_false in *. repeat rewrite por_empty_r in *.
                  eapply exp_locs_tfold with (z := z1)(t:= t1) in Q.
                  destruct Q as [Q| [Q|Q]].
                  - replace ((e2||true)&&false) with false in Q. eapply aux2 in Q. unfoldq; intuition. destruct e2; simpl in *; intuition.
                  - rewrite H5 in *; auto. eapply QR2 in Q. unfoldq; intuition. destruct az, al, e2; simpl in *; intuition.
                  - destruct al; simpl in *.  eapply QL2 in Q; auto. unfoldq; intuition. rewrite pif_false in *. eapply QL4 in Q. unfoldq; intuition.
                }
              } {
                simpl in *. unfoldq; intuition.
              }
            } {
              assert (negb a2||u = false). { destruct a2, u; simpl in *; intuition. }
              rewrite H10.
              eapply valt_reset_locs. eauto. intuition.
            }
          }

         {
            intros Q. rewrite Q in *. rewrite plift_if.
            remember (negb a2 || u) as b. 
            destruct b. { eapply QR1'. auto. }
            { unfoldq; intuition. }
          }   
          {
            intros Q. rewrite Q in *. rewrite plift_if.
            remember (negb a2 || u) as b. 
            destruct b. { eapply QR2'. auto. }
            { unfoldq; intuition. }
          }
          {
            repeat rewrite pif_false in *. repeat rewrite por_empty_r in *.
            rewrite plift_if. 
            remember (negb a2||u) as b. 
            intros ? Q. destruct b; try contradiction. rewrite H8; auto. simpl.
            eapply QR3' in Q. destruct a2; try contradiction. 
            eapply exp_locs_tfold with (z := z1) (t := t1)  in Q. 
            assert (u = true).  { simpl in *; auto. } subst u. simpl in *.
            destruct Q as [Q | [Q | Q]].
            + replace ((e2||true)&&true) with true in Q. 2: { destruct e2; simpl; auto. }
              replace ((az||al||true)&&true)  with true. 2: { destruct az, al; simpl; auto. }
              auto.
            + eapply QR3 in Q. replace ((az || al || (e2 || true)) && true)  with true in Q. 
              replace ((az || al || true) && true) with true. auto.
              destruct az, al; simpl; auto. destruct az, al, e2; simpl; auto.
            + eapply QL3 in Q. destruct al; try contradiction. 
              replace (az||true||true) with true. 2: { destruct az; simpl; auto. }
              simpl. unfold exp_locs. eapply vars_locs_mono; eauto. unfoldq; intuition. simpl in *. 
              rewrite plift_or, plift_diff, plift_or, plift_one, plift_one, plift_or. unfoldq; intuition.
          }
          {
            repeat rewrite pif_false in *. repeat rewrite por_empty_r in *.
            rewrite plift_if. 
            remember (negb a2||u) as b. 
            intros ? Q. destruct b; try contradiction. rewrite H8; auto. simpl.
            eapply QR4' in Q. destruct a2; try contradiction. 
            eapply exp_locs_tfold with (z := z2) (t := t2)  in Q. 
            assert (u = true).  { simpl in *; auto. } subst u. simpl in *.
            destruct Q as [Q | [Q | Q]].
            + replace ((e2||true)&&true) with (true) in Q. 2: { destruct e2; simpl; auto. }
              replace ((az||al||true)&&true)  with true. 2: { destruct az, al; simpl; auto. }
              auto.
            + eapply QR4 in Q. replace  ((az || al || (e2 || true)) && true)  with true in Q. 
              replace ((az||al||true)&&true) with true.
              auto. destruct az, al; simpl; auto. destruct az, al, e2; simpl; auto.
            + eapply QL4 in Q. destruct al; try contradiction. 
              replace (az||true||true) with true. 2: { destruct az; simpl; auto. }
              simpl. unfold exp_locs. eapply vars_locs_mono; eauto. unfoldq; intuition. simpl in *. 
              rewrite plift_or, plift_diff, plift_or, plift_one, plift_one, plift_or. unfoldq; intuition.
          }

          {
            intros ? Q. destruct Q. rewrite <-STWR1'. rewrite STWR1. auto.
            split. auto. auto. split. destruct ST2. destruct STR. destruct STR'. unfoldq. lia.
            intros ?. eapply H12. rewrite H8; auto. destruct e2; try contradiction. simpl in *.
            eapply exp_locs_tfold with (z := z1)(t := t1) in H13.
            destruct H13 as [Q | [Q| Q]].
            - destruct u; simpl in *. 2: { eapply aux2 in Q. unfoldq; intuition. }  
              assert ((ez ||el || true) = true). { destruct ez, el; simpl in *; intuition. }
              rewrite H13 in *. auto. 
            - eapply QR3 in Q. repeat rewrite pif_false in *. repeat rewrite por_empty_r in Q.
              remember ((az||al||true)&&a2) as b.
              destruct b; try contradiction.
              replace (ez||el||true) with true. auto. destruct ez, el; simpl; auto.
            - eapply QL3 in Q. repeat rewrite pif_false in *. repeat rewrite por_empty_r in Q.
              destruct al; simpl in *; try contradiction.
              replace (ez || el || true) with true. 2: { destruct ez, el; simpl; auto. }
              unfold exp_locs in *. eapply vars_locs_mono; eauto. unfoldq; intuition. simpl in *. 
              rewrite plift_or, plift_diff, plift_or, plift_one, plift_one, plift_or. unfoldq; intuition.
          }    

          {
            intros ? Q. destruct Q. rewrite <-STWR2'. rewrite STWR2. auto.
            split. auto. auto. split. destruct ST2. destruct STR. destruct STR'. unfoldq. lia.
            intros ?. eapply H12. rewrite H8; auto. destruct e2; try contradiction. simpl in *.
            eapply exp_locs_tfold with (z := z2)(t := t2) in H13.
            destruct H13 as [Q | [Q| Q]].
            - destruct u; simpl in *. 2: { eapply aux2 in Q. unfoldq; intuition. }  
              replace (ez || el || true) with true. 2: { destruct ez, el; simpl; auto. }
              auto.
            - eapply QR4 in Q. 
              repeat rewrite pif_false in *. repeat rewrite por_empty_r in Q.
              remember ((az||al||true)&&a2) as b.
              destruct b; try contradiction.
              replace (ez||el||true) with true. auto. destruct ez, el; simpl; auto.
            - eapply QL4 in Q. repeat rewrite pif_false in *. repeat rewrite por_empty_r in Q.
              destruct al; simpl in *; try contradiction. 
              replace (ez || el || true) with true. 2: { destruct ez, el; simpl; auto. }
              unfold exp_locs in *. eapply vars_locs_mono; eauto. unfoldq; intuition. simpl in *. 
              rewrite plift_or, plift_diff, plift_or, plift_one, plift_one, plift_or. unfoldq; intuition.
          }    

          intros. intuition. congruence.
        * (* mention *)   
          assert (e2 = false). destruct e2,a2; intuition.
          assert (a2 = false \/ u = false). { unfold bsub in *. destruct e2,a2,ur, az,al,u; intuition. }
          subst e2.

          edestruct HFF with  (SX := SR1)(SY := SR2)(MXY := MR)(ur := ur) 
           as (vr1' & vr2' & lsr1' & lsr2' & SR1' & SR2' & MR' & (n1' & E1) & (n2' & E2) & LSR1 & LSR2 & STR' & SCR' & STWR' & VTR' & QR1' & QR2' & QR3' & QR4' & STWR1' & STWR2' & STRELR').
           9: { eauto.  }
           9: { eauto. }
           9: { eauto. }
           9: { eauto. }
           9: { auto. }
          14: {  
                 destruct H7. {
                  subst a2. subst ur.
                  eapply valt_usable. eapply VR. simpl. intros. subst uz. simpl in *. subst az. destruct al; simpl in *; auto.
                 } {
                  subst u. simpl in *. subst a2. simpl in *. 
                  subst ur. rewrite UZ.  destruct az; simpl in *. auto. destruct al; simpl in *; auto.
                 }
          }          

          13: { eapply valt_store_change. eapply H9. 
                intros ? ? ? ? ? ?.  eapply STCR. auto.
                destruct ST2, STR. lia. destruct ST2, STR. lia. }
          {  
            intros Q. subst ul. eapply QL1. auto.
          }
          { 
            intros Q. eapply QL2. auto.
          }

          {
            repeat rewrite pif_false in *. repeat rewrite por_empty_r in *.
            intros. subst uz. intros ? Q. subst a2. 
            destruct H7. {
              subst az. simpl in *. inversion H5.
            }{
              subst u. simpl in *. destruct az; simpl in *; intuition. 
            }
          }

          {
            repeat rewrite pif_false in *. repeat rewrite por_empty_r in *.
            intros. subst uz. intros ? Q. subst a2.
            destruct H7. {
              subst az. simpl in *. inversion H5.
            }{
              subst u. simpl in *. destruct az; simpl in *; intuition. 
            }
          }

          {
            repeat rewrite pif_false in *. repeat rewrite por_empty_r in *. subst a2. simpl in *. 
            destruct H7.
            - subst. simpl in *. destruct al; simpl in *; intuition.
            - subst u. destruct az; simpl in *; intuition. destruct al ; simpl in *; intuition.
          }

          {
            repeat rewrite pif_false in *. repeat rewrite por_empty_r in *. subst a2. simpl in *. 
            destruct H7.
            - subst. simpl in *. destruct al; simpl in *; intuition.
            - subst u. destruct az; simpl in *; intuition. destruct al ; simpl in *; intuition.
          }

          {
            repeat rewrite pif_false in *. repeat rewrite por_empty_r in *. auto.
          }

          {
            repeat rewrite pif_false in *. repeat rewrite por_empty_r in *. auto.
          }
          lia. lia. auto. auto.
     
          exists vr1', vr2'. exists (qif ((negb a2)||u) lsr1'), (qif ((negb a2)||u) lsr2'), SR1', SR2', MR'. 
          split. 2: split.  3: split. 4: split. 5: split. 6: split. 7: split. 8: split. 9: split. 10: split. 11: split. 12: split. 13: split.
          14: split. 
          exists (nr1'+n1'). intros. rewrite A'. 2: lia.
          subst ff1. eapply E1. lia.
          exists (nr2'+n2'). intros. rewrite B''. 2: lia.
          subst ff2. eapply E2. lia.
          lia. lia.
          {
            repeat rewrite por_assoc in *. 
            rewrite pdiff_merge in *. rewrite pdiff_merge in *.  rewrite pdiff_merge in *.
            rewrite pdiff_merge in *. 
            all: eauto. 2: lia. 2: lia. 2: lia. 2: lia. 2: lia. 2: lia.
            eapply storet_tighten. eauto. 
            intros ? [?| ?]. left. auto. right. unfoldq. lia.
            intros ? [?| ?]. left. auto. right. unfoldq. lia.
          }

          eapply stchain_chain. eauto. auto.
          auto.
          eauto.

          { 
            eapply valt_sub_locs. eapply VTR'.
            destruct H7. {
              subst a2. rewrite H5 in *. simpl. unfoldq; intuition.
            }{
              subst u. simpl in *. 
              destruct a2. {
                simpl in *.
                assert (ur = false). { destruct ur; simpl in *; intuition. }
                rewrite H5 in *. eapply psub_empty' in QR1'; auto. subst lsr1'.  unfoldq; intuition.
              } {
                simpl in *. unfoldq; intuition.
              }
            }

            destruct H7. {
              subst a2. rewrite H5 in *. simpl. unfoldq; intuition.
            }{
              subst u. simpl in *. 
              destruct a2. {
                simpl in *.
                assert (ur = false). { destruct ur; simpl in *; intuition. }
                rewrite H5 in *. eapply psub_empty' in QR2'; auto. subst lsr2'.  unfoldq; intuition.
              } {
                simpl in *. unfoldq; intuition.
              }
            }
          }
          

         {
            intros Q. rewrite Q in *. rewrite plift_if.
            remember (negb a2 || u) as b. 
            destruct b. { eapply QR1'. auto. }
            { unfoldq; intuition. }
          }   
          {
            intros Q. rewrite Q in *. rewrite plift_if.
            remember (negb a2 || u) as b. 
            destruct b. { eapply QR2'. auto. }
            { unfoldq; intuition. }
          }
          {
            repeat rewrite pif_false in *. repeat rewrite por_empty_r in *.
            rewrite plift_if. 
            remember (negb a2||u) as b. 
            intros ? Q. destruct b; try contradiction. 
            destruct H7.
            - subst a2. rewrite H5 in *. simpl in *. eapply QR3' in Q. contradiction.
            - subst u. simpl in *. assert (a2 = false). { destruct a2; simpl in *; auto. }
              subst a2. rewrite H5 in *. simpl in *. eapply QR3' in Q. contradiction.
          }   
          
          
          {
            repeat rewrite pif_false in *. repeat rewrite por_empty_r in *.
            rewrite plift_if. 
            remember (negb a2||u) as b. 
            intros ? Q. destruct b; try contradiction. 
            destruct H7.
            - subst a2. rewrite H5 in *. simpl in *. eapply QR4' in Q. contradiction.
            - subst u. simpl in *. assert (a2 = false). { destruct a2; simpl in *; auto. }
              subst a2. rewrite H5 in *. simpl in *. eapply QR4' in Q. contradiction.
          }

          {
            intros ? Q. destruct Q. rewrite <-STWR1'. rewrite STWR1. auto.
            split. auto. auto. split. destruct ST2. destruct STR. destruct STR'. unfoldq. lia.
            intros ?. eapply H8. simpl in *.  contradiction.
          }
          
          {
            intros ? Q. destruct Q. rewrite <-STWR2'. rewrite STWR2. auto.
            split. auto. auto. split. destruct ST2. destruct STR. destruct STR'. unfoldq. lia.
            intros ?. eapply H8. simpl in *.  contradiction.
          }
          
          intros. intuition. congruence. congruence. 

  }


  destruct FOLD as (vr1 & vr2 & lsvr1 & lsvr2 & SR1 & SR2 & MR &? &? &? & ? &? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ?).
  
  exists SR1, SR2, MR, vr1, vr2. eexists. eexists. eexists.
  split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 8: split. 9:split. 10: split. 11: split.
  12: split. 13: split. 14: split. 15: split. 16: split.
  9: eauto.
  + eapply stchain_chain; eauto. eapply stchain_chain. eauto. eauto.
  + auto.
  + destruct EZ1 as (n1 & EZ1).
    destruct EL1 as (n2 & EL1).
    destruct H5 as (n3 & E2).
    exists (1+n1+n2+n3). intros. destruct n. lia.
    simpl. rewrite EZ1. rewrite EL1. 2,3: lia. 
    subst ff1. rewrite E2. auto. lia.
  + destruct EZ2 as (n1 & EZ2).
    destruct EL2 as (n2 & EL2).
    destruct H7 as (n3 & E2).
    exists (1+n1+n2+n3). intros. destruct n. lia.
    simpl. rewrite EZ2. rewrite EL2. 2,3: lia. 
    subst ff2. rewrite E2. auto. lia. 
  + lia.
  + lia.
  + repeat rewrite por_assoc in H10. 
    rewrite pdiff_merge, pdiff_merge in H10.
    rewrite pdiff_merge, pdiff_merge in H10.
    all: eauto. 2: lia. lia.
  + eauto.
  + auto.
  + auto.
  + auto. 
  + auto.
  + auto.
  + intros ? Q. destruct Q. rewrite <-H18. rewrite <-SW3. rewrite <-SW1. auto.
    split. auto. intros ?. eapply H22. destruct ez; simpl; try contradiction. 
    unfold exp_locs in *. eapply vars_locs_mono; eauto. unfoldq; intuition. simpl in *. 
    rewrite plift_or, plift_diff, plift_or, plift_one, plift_one, plift_or. unfoldq; intuition.
    split. destruct ST1. unfoldq. lia. 
    intros ?. eapply H22. destruct el; try contradiction. replace (ez || true || (e2 || a2 || az || al) && e2)  with true. 2: { destruct ez, e2; intuition. }
    unfold exp_locs in *. eapply vars_locs_mono; eauto. simpl in *. rewrite plift_or. rewrite plift_diff. repeat rewrite plift_or. 
    repeat rewrite plift_one. unfoldq; intuition.
    split. destruct ST1, ST2. unfoldq. lia.  auto.
  + intros ? Q. destruct Q. rewrite <-H19. rewrite <-SW4. rewrite <-SW2. auto.
    split. auto. intros ?. eapply H22. destruct ez; simpl; try contradiction. 
    unfold exp_locs in *. eapply vars_locs_mono; eauto. unfoldq; intuition. simpl in *. 
    rewrite plift_or, plift_diff, plift_or, plift_one, plift_one, plift_or. unfoldq; intuition.
    split. destruct ST1. unfoldq. lia. 
    intros ?. eapply H22. destruct el; try contradiction. replace (ez || true || (e2 || a2 || az || al) && e2) with true. 2: { destruct ez, e2; intuition. }
    unfold exp_locs in *. eapply vars_locs_mono; eauto. simpl in *. rewrite plift_or. rewrite plift_diff. repeat rewrite plift_or. 
    repeat rewrite plift_one. unfoldq; intuition.
    split. destruct ST1, ST2. unfoldq. lia. auto.
  + intros. intuition. congruence.
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
  - eapply exp_nil; eauto.
  - simpl in *.
    edestruct (IHW1 u M H1 H2 H2' HX) as (S1' & S2' & M' & ?); eauto.
    eapply envt_tighten; eauto. rewrite plift_or. unfoldq. intuition.
    unfold bsub in *. destruct e1, u; intuition. 
    rewrite exp_locs_cons in *. unfoldq. destruct e1,e2; simpl in *; intuition.
    rewrite exp_locs_cons, exp_locs_shift in *. unfoldq. destruct e1,e2; simpl in *; intuition. 
    eapply exp_cons; eauto.
    destruct H as (?&?&?&?&?&?&?&?&?&?&?&?&?).
    eapply IHW2; eauto.
    eapply envt_store_change. eapply envt_tighten; eauto. rewrite plift_or. unfoldq. intuition.
    intros ?????. eauto.
    destruct ST as (?&?&?). destruct H7 as (?&?&?). lia.
    destruct ST as (?&?&?). destruct H7 as (?&?&?). lia.
    unfold bsub in *. destruct e2, u; intuition.     
    rewrite exp_locs_cons in *. unfoldq. destruct e1,e2; simpl in *; intuition.
    rewrite exp_locs_cons in *. unfoldq. destruct e1,e2; simpl in *; intuition.
  - eapply exp_sub. eauto. eauto. 
    simpl in *.
    edestruct (IHW2 u M H1 H2 H2' HX) as (S1' & S2' & M' & ?); eauto. 
    eapply envt_tighten; eauto. rewrite plift_or. unfoldq; intuition.
    unfold bsub in *. intros. subst ez. eapply E. simpl; auto.
    intros ? ?. eapply P1. destruct ez; try contradiction. simpl.
    unfold exp_locs in *. eapply vars_locs_mono; eauto. simpl. repeat rewrite plift_or, plift_diff.
    repeat rewrite plift_or. repeat rewrite plift_one. unfoldq; intuition.
    intros ? ?. eapply P2. destruct ez; try contradiction. simpl.
    unfold exp_locs in *. eapply vars_locs_mono; eauto. simpl. repeat rewrite plift_or, plift_diff.
    repeat rewrite plift_or. repeat rewrite plift_one. unfoldq; intuition.
    rename H0 into HZ. remember HZ as HZ'. clear HeqHZ'.
    destruct HZ as (?&?&?&?&?&?&?&?&?&?&?&?&?). intuition.

    edestruct (IHW3 u M' H1 H2 H2' HX) as (S1'' & S2'' & M'' & HL); eauto.
    eapply envt_store_change. eapply envt_tighten. eauto. repeat rewrite plift_or. unfoldq; intuition.
    intros ?????. eauto. 
    destruct ST. destruct H8. lia.
    destruct ST. destruct H8. lia.
    unfold bsub in *. intros. subst el. eapply E. destruct ez; simpl; auto.
    intros ? ?. destruct el; try contradiction. left. eapply P1. destruct ez; simpl; auto.
    1,2: unfold exp_locs; eapply vars_locs_mono; eauto; simpl; 
    rewrite plift_or, plift_diff; repeat rewrite plift_or; repeat rewrite plift_one; unfoldq; intuition.
    intros ? ?. destruct el; try contradiction. left. eapply P2. destruct ez; simpl; auto.
    1,2: unfold exp_locs; eapply vars_locs_mono; eauto; simpl;
    rewrite plift_or, plift_diff; repeat rewrite plift_or; repeat rewrite plift_one; unfoldq; intuition.
    remember HL as HL'. clear HeqHL'.
    destruct HL as (?&?&?&?&?&?&?&?&?&?&?&?&?). intuition.
    rename H27 into VL. remember VL as VL'. clear HeqVL'.
    destruct x4, x5; simpl in VL'; intuition.

    eapply exp_tfold with (e2 := e2). 7: eauto. 7: eauto. 
    all: eauto.
    
    {
      intros ? ?. eapply P1. destruct ez, el, e2; simpl in *; auto.
      destruct a2, al; simpl in *; try contradiction.
    }
    {
      intros ? ?. eapply P2. destruct ez, el, e2; simpl in *; auto.
      destruct a2, al; simpl in *; try contradiction.
    }
    {
      unfold bsub in *. intros. eapply E.
      destruct ez, el, e2; simpl in *; auto. destruct a2, al; simpl in *; auto.
    } 
    
    {
      intros SX SY MX p1x p2x vz1 vz2 lsz1 lsz2 ve1 ve2 lse1 lse2 uz' ul' ur SCX SWX STX SPX1 SPX2 STXL1 STXL2 UZ1 UL1 UZ2 UL2 UY VY VZ LXE1 LXE2 LEX3 LXE4 LXZ1 LXZ2 LXZ3 LXZ4.
      assert (e2||ur&&a2 = true -> negb (a2||al) || u = true) as A. {
        intros ?. subst ur. unfold bsub in *. destruct e2, al, a2, u; simpl in *; intuition.
      }

     assert (e2||ur&&a2 = true -> negb a2 || u = true)  as B. {
      intros ?. subst ur. unfold bsub in *. destruct e2, al, a2, u; simpl in *; intuition.
     }

     assert (e2||ur&&a2 = true -> negb al || u = true)  as B'. {
       intros ?. subst ur. unfold bsub in *. destruct e2, al, a2, u; simpl in *; intuition.
     }

     assert (e2||ur&&a2 = true -> (* negb a || *)  u = true) as C. {
       intros ?. subst ur. unfold bsub in *. destruct e2, al, a2, u; simpl in *; intuition.
     } 
     remember (e2||ur&&a2) as D.
      destruct D.
      * (* use *)
        assert (u = false -> (* a = true -> *) e2 = false). destruct u,e2; intuition.
        assert (u = false -> (* a = true -> *) a2 = false). subst. unfold bsub in *. destruct u; simpl in *; intuition. 
        assert (e2||a2 = true). destruct e2,a2; intuition. 
        edestruct (IHW1 true MX (vz1::ve1::H1) H2 (vz2::ve2::H2') HX (lsz1::lse1::V1) V2 (lsz2::lse2::V2') VX) 
          as (S1''' & S2''' & M''' & vf1 & vf2 & uf' & lsf1 & lsf2 & SC3 & STW3 & EF1 & EF2 & LSF1 & LSF2 & ST''' & VF & UF & ZF & QF1 & QF2 & QF3 & QF4 & SW1' & SW2' & STREL3); eauto.
          2: { simpl. lia. }
          {
            eapply envt_tighten.
            eapply envt_extend.
            eapply envt_extend.
            eapply envt_store_change with (M := M).
            destruct u. {  
              eapply WFE. 
            }{
              simpl in *. intuition. 
            }
            {
              intros ?????. eapply SCX. auto. 
            }
            lia. lia. 
            eauto. 
            { 
              simpl. rewrite H37 in *. subst. destruct al, u; simpl in *; intuition. 
            }
            {
              intros [Q | Q]. 2: { inversion Q. }
              simpl in Q. subst al. repeat rewrite pif_false in *. repeat rewrite por_empty_r in *. auto.
            }
            {
              intros [Q | Q]. 2: { inversion Q. }
              simpl in Q. subst al. repeat rewrite pif_false in *. repeat rewrite por_empty_r in *. auto.
            }
            eauto.
            { simpl. rewrite H37 in *. subst. destruct u; simpl in *; intuition. }
            {
              intros [Q | Q]. 2: { inversion Q. }
              simpl in Q. subst a2. simpl in *.  repeat rewrite pif_false in *. repeat rewrite por_empty_r in *. auto.
            }
            {
              intros [Q | Q]. 2: { inversion Q. }
              simpl in Q. subst a2. simpl in *.  repeat rewrite pif_false in *. repeat rewrite por_empty_r in *. auto.
            }
            intros ? ?. eapply hast_fv in W1. simpl in *. subst p p2. repeat rewrite plift_or. rewrite plift_diff.  rewrite plift_or, plift_one, plift_one.  unfoldq; intuition.
            bdestruct (x4 =? length env); intuition. simpl. bdestruct (x4 =? S (length env)); intuition.
          }  
          
          unfold bsub . auto.
          { 
            intros ? Q. eapply SPX1. destruct e2; try contradiction.
            rewrite H37 in *. simpl in *. 
            replace (ez||el||true) with true. 2: { destruct ez, el; simpl; auto. }
            unfold bsub in *.  intuition. subst.
            eapply exp_locs_tfold with (z := z)(t := t) in Q. 
            destruct Q as [Q | [Q | Q]].
            { 
              auto.
            } {
              eapply LXZ3 in Q. repeat rewrite pif_false in *. rewrite por_empty_l in *.  destruct Q. 2:contradiction.
              destruct a2; simpl in *; try contradiction.
              unfold exp_locs in *. eapply vars_locs_mono; eauto. simpl. repeat rewrite plift_or, plift_diff.
              repeat rewrite plift_or. repeat rewrite plift_one. unfoldq; intuition.
            } {
              eapply LEX3 in Q. repeat rewrite pif_false in Q. rewrite por_empty_r in Q. destruct Q. 2: contradiction.
              destruct al; try contradiction.
              unfold exp_locs in *. eapply vars_locs_mono; eauto. simpl. 
              rewrite plift_or, plift_diff. repeat rewrite plift_or. repeat rewrite plift_one.
              unfoldq; intuition.
            }
          }
          
          { 
            intros ? Q. eapply SPX2. destruct e2; try contradiction.
            rewrite H37 in *. simpl in *. 
            replace (ez||el||true) with true. 2: { destruct ez, el; simpl; auto. }
            unfold bsub in *.  intuition. subst.
            eapply exp_locs_tfold with (z := (splice_tm z (length V2) (length VX)))(t := (splice_tm t (length V2) (length VX))) in Q. 
            destruct Q as [Q | [Q | Q]].
            { 
              auto.
            } {
              eapply LXZ4 in Q. repeat rewrite pif_false in *. rewrite por_empty_l in *.  destruct Q. 2:contradiction.
              destruct a2; simpl in *; try contradiction.
              unfold exp_locs in *. eapply vars_locs_mono; eauto. simpl. repeat rewrite plift_or, plift_diff.
              repeat rewrite plift_or. repeat rewrite plift_one. unfoldq; intuition.
            } {
              eapply LXE4 in Q. repeat rewrite pif_false in Q. rewrite por_empty_r in Q. destruct Q. 2: contradiction.
              destruct al; try contradiction.
              unfold exp_locs in *. eapply vars_locs_mono; eauto. simpl. 
              rewrite plift_or, plift_diff. repeat rewrite plift_or. repeat rewrite plift_one.
              unfoldq; intuition.
            }
          }
        unfold exp_type. unfold exp_type1.  
        exists S1''', S2''', M'''.  eexists. eexists. eexists. exists (qif uf' lsf1). exists (qif uf' lsf2).
        split. 2:split. 3: split. 4: split. 5: split. 6: split. 7: split. 8: split. 9: split. 10: split. 11: split. 12: split. 
        13: split. 14: split. 15: split. 16: split.
        9: eauto.
        all: eauto.
        { 
          assert (uf' = true). { destruct a2; simpl in *; intuition. }
          rewrite H38 in *. eapply valt_usable. eauto. auto.
        }
        {
          rewrite plift_if. intros ? ? Q.  repeat rewrite pif_false in *. repeat rewrite por_empty_r in *.
          destruct uf'; try contradiction. eapply QF3 in Q.
          destruct a2; try contradiction. simpl in *. 
          assert (u = true). { subst. simpl in *. eapply A; auto. }
          subst u. subst ur. simpl in *; intuition. 
        }
        {
          rewrite plift_if. intros ? ? Q.  repeat rewrite pif_false in *. repeat rewrite por_empty_r in *.
          destruct uf'; try contradiction. eapply QF4 in Q.
          destruct a2; try contradiction. simpl in *. 
          assert (u = true). { subst. simpl in *. eapply A; auto. }
          subst u. subst ur. simpl in *; intuition.
        }
        rewrite plift_if. destruct uf'. eauto. unfoldq; intuition.
        rewrite plift_if. destruct uf'. eauto. unfoldq; intuition.

     * (* mention *) 
       assert (e2 = false). destruct e2,a2; intuition.
       assert (a2 = false \/ u = false). { unfold bsub in *. destruct e2,a2,ur,al,u; intuition. }
       subst e2.
       edestruct (IHW1 false MX (vz1::ve1::H1) H2 (vz2::ve2::H2') HX (qempty::qempty::V1) V2 (qempty::qempty::V2') VX) 
          as (S1''' & S2''' & M''' & vf1 & vf2 & uf' & lsf1 & lsf2 & SC3 & STW3 & EF1 & EF2 & LSF1 & LSF2 & ST''' & VF & UF & ZF & QF1 & QF2 & QF3 & QF4 & SW1' & SW2' & STREL3); eauto.

       {
          repeat rewrite plift_or in WFE.
          eapply envt_tighten. eapply envt_extend. eapply envt_extend.
          eapply envt_store_changeV' with (M:=M) (p:=plift p).
          destruct u. eapply envt_strengthenW1; eauto. eapply envt_tighten. eauto.  unfoldq; intuition.
          eapply envt_tighten. eauto. unfoldq; intuition. 
          destruct ST, H9, H26, STX. lia.
          destruct ST, H9, H26, STX. lia.
          2: eauto. 5: eauto.

          {
            destruct al; simpl. {
            eapply valt_reset_locs. eapply valt_usable. eauto. intuition. intuition.
            } {
              simpl in *. subst ul'.
              repeat rewrite pif_false in *. repeat rewrite por_empty_r in *.
              eapply psub_empty' in LEX3; auto. eapply psub_empty' in LXE4; auto.
              subst. simpl in *. eauto.
            }
          }
          {
            rewrite plift_empty. unfoldq; intuition.
          }
          {
            rewrite plift_empty. unfoldq; intuition.
          }
          {
            destruct H36.
            - subst a2. simpl in *. repeat rewrite pif_false in *. repeat rewrite por_empty_r in *.
              eapply psub_empty' in LXZ3; auto. eapply psub_empty' in LXZ4; auto. subst. eauto. 
            - subst u. simpl in *. 
               destruct a2; simpl in *. 
               -- rewrite UZ1 in *.  eapply psub_empty' in LXZ1; auto. eapply psub_empty' in LXZ2; auto. subst. eauto. 
               -- repeat rewrite pif_false in *. repeat rewrite por_empty_r in *.
                  eapply psub_empty' in LXZ3; auto. eapply psub_empty' in LXZ4; auto. subst. eauto. 
          } 
          {
            rewrite plift_empty. unfoldq; intuition.
          }
          {
            rewrite plift_empty. unfoldq; intuition.
          }
          
          eapply hast_fv in W1. intros ? ?. subst p p2. rewrite plift_diff.  rewrite plift_or, plift_one, plift_one.  unfoldq; intuition.
          simpl.
          bdestruct (x4 =? length env); intuition. simpl. bdestruct (x4 =? S (length env)); intuition.
          simpl.
          bdestruct (x4 =? length env); intuition. simpl. bdestruct (x4 =? S (length env)); intuition.
          
        }

        simpl. lia.
        unfold bsub; auto.
        unfoldq; intuition.
        unfoldq; intuition.
        
        exists S1'''. exists S2'''. exists M'''. eexists.  eexists. eexists. exists (qif uf' lsf1). exists (qif uf' lsf2).  
        split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 8: split. 9: split. 10: split. 
        11: split. 12: split. 13: split. 14: split. 
        all:eauto.
        {
          destruct a2; simpl in *. {
            assert (ur = false). {
              destruct ur; simpl in *. inversion HeqD. auto.
            }
            rewrite H27.
            subst uf'. 
            eapply valt_reset_locs. eauto. intuition.
          }{
            subst uf'.
            destruct ur. {
              eapply valt_sub_locs. eauto. rewrite plift_if. unfoldq; intuition. rewrite plift_if. unfoldq; intuition.
            } {
              eapply valt_usable. eapply valt_sub_locs. eauto. rewrite plift_if. unfoldq; intuition. rewrite plift_if. unfoldq; intuition.
              intuition.
            }
          }
        }  

        {
          destruct uf'. 
          2: { unfoldq; intuition. }
          simpl in *.
          assert (a2 = false). { destruct a2; simpl in *; intuition. }
          rewrite H27 in *.
          intros ???. eapply QF3 in H38. repeat rewrite pif_false in *. repeat rewrite por_empty_r in *. auto.
        }  
        
        { 
          destruct uf'. 
          2: { unfoldq; intuition. }
          simpl in *.
          assert (a2 = false). { destruct a2; simpl in *; intuition. }
          rewrite H27 in *.
          intros ???. eapply QF4 in H38. repeat rewrite pif_false in *. repeat rewrite por_empty_r in *. auto.
        }
        {
          rewrite plift_if. repeat rewrite pif_false in *. repeat rewrite por_empty_r in *. 
          intros ? Q.
          destruct a2; simpl in *. rewrite UF in *. contradiction.
          rewrite UF in *. eapply QF3. eauto.
        }

        {
          rewrite plift_if. repeat rewrite pif_false in *. repeat rewrite por_empty_r in *. 
          intros ? Q.
          destruct a2; simpl in *. rewrite UF in *. contradiction.
          rewrite UF in *. eapply QF4. eauto.
        }
       
    }
    all: unfold bsub; auto.
    intros ?. destruct a2, al, e2; simpl in *; auto.
    intros ?. destruct ez, el, e2, a2,al; simpl in *; auto.
    
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
  - unfold bsub in *. 

    edestruct (IHW u M H3 H4 H2') with (VX := VX) as (S1' & S2' & M' & HX1); eauto.
    {
      intros ? ?. eapply P1. destruct e1, e2; try contradiction; intuition.
    }

    {
      intros ? ?. eapply P2. destruct e1, e2; try contradiction; intuition.
    }
    destruct HX1 as (vy1 & vy2 & uy & lsy1 & lsy2 &?).
    exists S1', S2', M', vy1, vy2, (negb a2||u), (if (negb a2 || u) then lsy1 else qempty), (if (negb a2 || u) then lsy2 else qempty). 
    eapply exp_sub_stp2; eauto.
    eapply stp_fundamental in H. eapply H.  
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
  intros ??????????????????? WFE LH2 E SW ST EP1 EP2 (* LU2 *).
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


Lemma exp_type1_V_irrel_ff: forall S1 S2 M H1 H2 V1a V2a V1b V2b t1 t2 S1' S2' M' T u p1 p2 fr,
    exp_type1 S1 S2 M H1 H2 V1a V2a t1 t2 S1' S2' M' T u p1 p2 fr false false ->
    exp_type1 S1 S2 M H1 H2 V1b V2b t1 t2 S1' S2' M' T u p1 p2 fr false false.
Proof.
  intros. destruct H as (v1 & v2 & uv & ls1 & ls2 & H).
  exists v1, v2, uv, ls1, ls2.
  destruct H as (SC & SW & TV1 & TV2 & LS1 & LS2 & ST' & VT & UEQ & _ & PE1 & PE2 & PSL1 & PSL2 & SW1 & SW2 & FRM).
  split. 2: split. 3:split. 4: split. 5: split. 6: split. 7: split. 8: split. 9: split. 10: split.
  11: split. 12: split. 13: split. 14: split. 15: split. 16: split.
  all: eauto.
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
      exists uv (S2':stor) v2 ls2, 
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
  - eapply exp_nil; eauto.
  - edestruct IHW1 as (S1' & S2' & M' & HEXP). eauto.
    eapply envt_tighten. eauto. 

    rewrite plift_or. unfold subst_ql. unfoldq. intuition. bdestruct (x <? length V2); eauto.
    all: eauto.
    intros A. eapply WK. rewrite plift_or. left. eauto.
    unfold bsub in *. intros. subst e1. simpl in E. auto.
    
    simpl in *. rewrite exp_locs_cons in *. unfoldq. destruct e1,e2; simpl in *; intuition.
    simpl in *. rewrite exp_locs_cons in *. unfoldq. destruct e1,e2; simpl in *; intuition. 
    eapply exp_cons; eauto.
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
    edestruct (WK A' HX VX S2X) as (u' & S2X' & v2 & ls2 & TVX2). lia. lia.  
    exists u', S2X', v2, ls2. intuition.
    eapply valt_store_change. eauto.
    intros ?????. simpl. eauto. eauto. eauto.
    unfold bsub in *. intros. subst e2. intuition. 
    rewrite exp_locs_cons in *. unfoldq. destruct e1,e2; simpl in *; intuition.
    rewrite exp_locs_cons in *. unfoldq. destruct e1,e2; simpl in *; intuition.
  - simpl in *. repeat rewrite plift_or in *. subst env.
    edestruct IHW2 with (M := M)(t1 := t1) as (S1' & S2' & M' & ?).
    eauto. 
    eapply envt_tighten. eapply WFE. rewrite subst_ql_or. unfoldq; intuition.
    all: auto.
    {
      intros. eapply WK. 
      unfoldq; intuition. eapply H3. destruct ST. lia.
    }
    unfold bsub in *. intros. subst ez. eapply E. simpl; auto.
    eauto.
    intros ? ?. eapply P1. destruct ez; try contradiction. simpl.
    unfold exp_locs in *. eapply vars_locs_mono; eauto. simpl. repeat rewrite plift_or, plift_diff.
    repeat rewrite plift_or. repeat rewrite plift_one. unfoldq; intuition.
    intros ? ?. eapply P2. destruct ez; try contradiction. simpl.
    unfold exp_locs. eapply vars_locs_mono; eauto. simpl.
    repeat rewrite plift_or. rewrite plift_diff. repeat rewrite plift_or. repeat rewrite plift_one.
    unfoldq; intuition. eauto.

    rename H0 into HZ. remember HZ as HZ'. clear HeqHZ'.
    destruct HZ as (?&?&?&?&?&?&?&?&?&?&?&?&?). intuition.
    rename H8 into ST'.

    edestruct (IHW3) with (M := M') as (S1'' & S2'' & M'' & HL). 
    eauto.
    eapply envt_store_change with (M := M). eapply envt_tighten. eapply WFE. 
    repeat rewrite subst_ql_or. unfoldq; intuition.
    intros ?????. eauto. 
    destruct ST. destruct ST'. lia.
    destruct ST. destruct ST'. lia.
    all:auto. 
    { intros ?. destruct H8. eapply H19. auto. eapply H20; auto. }
    {
      intros. edestruct WK with (S2X := S2X) as (uv & S2X' & v2 & ls2 & ? & ? &? &? &? & ? &? &?).
      unfoldq; intuition. eapply H21. destruct ST, ST'. lia. 
      eexists. exists S2X', v2, ls2.
      split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split.
      all: eauto.
      eapply valt_store_change. eauto. intros ??????. simpl in *. auto.
      destruct ST, ST'. unfold st_len1 in *. simpl in *. lia.
      destruct ST, ST'. unfold st_len2 in *. simpl in *. lia.
    }
    unfold bsub in *. intros. subst el. eapply E. destruct ez; simpl; auto.
    eauto.
    intros ? ?. destruct el; try contradiction. left. eapply P1. destruct ez; simpl; auto.
    1,2: unfold exp_locs; eapply vars_locs_mono; eauto; simpl; 
    rewrite plift_or, plift_diff; repeat rewrite plift_or; repeat rewrite plift_one; unfoldq; intuition.
    intros ? ?. destruct el; try contradiction. left. eapply P2. destruct ez; simpl; auto.
    1,2: unfold exp_locs; eapply vars_locs_mono; eauto; simpl;
    rewrite plift_or, plift_diff; repeat rewrite plift_or; repeat rewrite plift_one; unfoldq; intuition.
    remember HL as HL'. clear HeqHL'.
    destruct HL as (?&?&?&?&?&?&?&?&?&?&?&?&?). intuition.
    rename H26 into ST''. rename H28 into VL. remember VL as VL'. clear HeqVL'.
    destruct x4, x5; simpl in VL'; intuition.

    eapply exp_sub. eauto. eauto.
    eapply exp_tfold with (e2 := e2). 7: eauto. 7: eauto. all: eauto. 
    {
      intros ? ?. eapply P1.
      destruct ez, el, e2, a2, al; simpl in *; auto.
    }
    {
      intros ? ?. eapply P2.
      destruct ez, el, e2, a2, al; simpl in *; auto.
    }
    {
      unfold bsub in *. intros. eapply E.
      destruct ez, el, e2, a2, al; simpl in *; auto.
    }
    
    {  
      intros SX SY MX p1x p2x vz1 vz2 lsz1 lsz2 ve1 ve2 lse1 lse2 uz' ul' ur SCX SWX STX SPX1 SPX2 STXL1 STXL2 UZ1 UL1 UZ2 UL2 UY VY VZ LXE1 LXE2 LEX3 LXE4 LXZ1 LXZ2 LXZ3 LXZ4.
      assert (e2||ur&&a2 = true -> negb (a2||al) || u = true) as A. {
        intros ?. subst ur. unfold bsub in *. destruct e2, al, a2, u; simpl in *; intuition.
      }

     assert (e2||ur&&a2 = true -> negb a2 || u = true)  as B. {
      intros ?. subst ur. unfold bsub in *. destruct e2, al, a2, u; simpl in *; intuition.
     }

     assert (e2||ur&&a2 = true -> negb al || u = true)  as B'. {
       intros ?. subst ur. unfold bsub in *. destruct e2, al, a2, u; simpl in *; intuition.
     }

     assert (e2||ur&&a2 = true -> (* negb a || *)  u = true) as C. {
       intros ?. subst ur. unfold bsub in *. destruct e2, al, a2, u; simpl in *; intuition.
     } 
     remember (e2||ur&&a2) as D.
      destruct D.
      * (* use *)
        assert (u = false -> (* a = true -> *) e2 = false). destruct u,e2; intuition.
        assert (u = false -> (* a = true -> *) a2 = false). subst. unfold bsub in *. destruct u; simpl in *; intuition. 
        assert (e2||a2 = true). destruct e2,a2; intuition. 
        edestruct IHW1 with (u := true)(M := MX) (H1' := (vz1::ve1::H1')) (H1 := H1) (H2' := (vz2::ve2::H2')) (H2 := H2)
              (V1' := (lsz1::lse1::V1')) (V1 := V1) (V2' := (lsz2::lse2::V2')) (V2 := V2) 
              (G := G)(G' := (T2, false, a2) :: (T1, false, al) ::G')
          as (S1''' & S2''' & M''' & vf1 & vf2 & uf' & lsf1 & lsf2 & SC3 & STW3 & EF1 & EF2 & LSF1 & LSF2 & ST''' & VF & UF & ZF & QF1 & QF2 & QF3 & QF4 & SW1' & SW2' & STREL3).
        { simpl. eauto. }
        2-5: auto.
        {
          simpl. eapply envt_tighten. eapply envt_extend. eapply envt_extend. 
          eapply envt_store_change with (M := M).
          destruct u. {  
            eapply WFE. 
          }{
            simpl in *. intuition. 
          }
          {
            intros ?????. eapply SCX. auto. 
          }
          lia. lia. 
          eauto. 
          { subst ul'. simpl. rewrite H37 in *. rewrite C; eauto. }
          all: eauto.
          { intros [Q|Q]. 
            - simpl in Q. subst al. repeat rewrite pif_false in *. repeat rewrite por_empty_r in *. eauto.
            - inversion Q. 
          }
          { intros [Q|Q]. 
            - simpl in Q. subst al. repeat rewrite pif_false in *. repeat rewrite por_empty_r in *. eauto.
            - inversion Q. 
          }
          { rewrite UZ1. simpl. rewrite C; auto.  }
          { intros [Q|Q]. 
            - simpl in Q. subst a2. repeat rewrite pif_false in *. repeat rewrite por_empty_r in *. eauto.
            - inversion Q. 
          }
          { intros [Q|Q]. 
            - simpl in Q. subst a2. repeat rewrite pif_false in *. repeat rewrite por_empty_r in *. eauto.
            - inversion Q. 
          }

          eapply hast_fv in W1 as X. subst p2 p.
          rewrite plift_diff. repeat rewrite plift_or. repeat rewrite subst_ql_or. simpl. repeat rewrite app_length in *. simpl in *.
          intros ? ?.
          unfold subst_ql in *. repeat rewrite plift_one. unfoldq; intuition. 
          bdestruct (x4 <? length V2); intuition.  bdestruct (x4 =?  length G'+ length G); intuition.
          bdestruct (x4 =?  S (length G'+ length G)); intuition.

        }
        all: auto.   
        {
          intros [Q | Q]. 2: { inversion Q. }
          simpl in Q. subst a1. repeat rewrite pif_false in *. repeat rewrite por_empty_r in *. auto.
        }
        intros Q. inversion Q.
        {
          intros. edestruct WK with (S2X := S2X) as (uv & S2X' & v2 & ls2 & ? & ? &? &? &? & ? &? &?).
          subst p. right. right. rewrite plift_diff. repeat rewrite plift_or. repeat rewrite plift_one.
          simpl. rewrite app_length. simpl. split. auto. unfoldq; intuition.
          eapply H39. destruct ST, ST'. lia. 
          eexists. exists S2X', v2, ls2.
          split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split.
          all: eauto.
          {
            intros [Q|Q].
            - eapply H44. left. auto.
            - destruct a1; simpl in Q. inversion Q. eapply H44; eauto.
          }
          {
            intros [Q|Q].
            - eapply H45. left. auto.
            - destruct a1; simpl in Q. inversion Q. eapply H45; eauto.
          }
          eapply valt_store_change. eapply valt_usable. eauto. 
          intros. destruct a1; simpl in *; intuition. congruence.
          intros ??????. simpl in *. auto.
          destruct ST, ST'. unfold st_len1 in *. simpl in *. lia.
          destruct ST, ST'. unfold st_len2 in *. simpl in *. lia.

          intros ? Q. eapply H47 in Q. repeat rewrite pif_false in *. rewrite por_empty_r in *.
          destruct a1; try contradiction. destruct u. auto. eapply aux2' in Q. unfoldq; intuition.
        }
        {
          unfold bsub in *. auto.
        }
        eauto.
        {
          intros ? Q. eapply SPX1. destruct e2; try contradiction. rewrite H37. simpl.
          replace (ez||el||true) with true. 2: { destruct ez, el; simpl; intuition. }
          eapply exp_locs_tfold in Q.
          destruct Q as [Q | [Q | Q]].
          { 
            eauto.
          } {
            eapply LXZ3 in Q. repeat rewrite pif_false in *. rewrite por_empty_l in *.  destruct Q. 2:contradiction.
            destruct a2; simpl in *; try contradiction.
            unfold exp_locs in *. eapply vars_locs_mono; eauto. simpl. repeat rewrite plift_or, plift_diff.
            repeat rewrite plift_or. repeat rewrite plift_one. unfoldq; intuition.
          } {
            eapply LEX3 in Q. repeat rewrite pif_false in Q. rewrite por_empty_r in Q. destruct Q. 2: contradiction.
            destruct al; try contradiction.
            unfold exp_locs in *. eapply vars_locs_mono; eauto. simpl. 
            rewrite plift_or, plift_diff. repeat rewrite plift_or. repeat rewrite plift_one.
            unfoldq; intuition.
          }
        }
        {
          intros ? Q.  eapply SPX2. destruct e2; try contradiction. rewrite H37. simpl.
          replace (ez||el||true) with true. 2: { destruct ez,el; simpl; intuition. }
          eapply exp_locs_tfold in Q. 
          destruct Q as [Q | [Q | Q]].
          { 
            simpl in Q. rewrite splice_acc. replace (2+ length V2') with (S (S (length V2'))). eauto. lia.
          } {
            eapply LXZ4 in Q. repeat rewrite pif_false in *. rewrite por_empty_l in *.  destruct Q. 2:contradiction.
            destruct a2; simpl in *; try contradiction.
            unfold exp_locs in *. eapply vars_locs_mono; eauto. simpl. repeat rewrite plift_or, plift_diff.
            repeat rewrite plift_or. repeat rewrite plift_one. unfoldq; intuition.
          } {
            eapply LXE4 in Q. repeat rewrite pif_false in Q. rewrite por_empty_r in Q. destruct Q. 2: contradiction.
            destruct al; try contradiction.
            unfold exp_locs in *. eapply vars_locs_mono; eauto. simpl. 
            rewrite plift_or, plift_diff. repeat rewrite plift_or. repeat rewrite plift_one.
            unfoldq; intuition.
          }
        }
        
        exists S1''', S2''', M'''.  eexists. eexists. eexists. exists (qif uf' lsf1). exists (qif uf' lsf2).
        split. 2:split. 3: split. 4: split. 5: split. 6: split. 7: split. 8: split. 9: split. 10: split. 11: split. 12: split. 
        13: split. 14: split. 15: split. 16: split.
        9: eauto.
        all: eauto.
        simpl in *. rewrite splice_acc. replace (2+length V2') with (S (S (length V2'))). eauto. lia.
        { 
          assert (uf' = true). { destruct a2; simpl in *; intuition. }
          rewrite H38 in *. eapply valt_usable. eauto. auto.
        }
        {
          rewrite plift_if. intros ? ? Q.  repeat rewrite pif_false in *. repeat rewrite por_empty_r in *.
          destruct uf'; try contradiction. eapply QF3 in Q.
          destruct a2; try contradiction. simpl in *. 
          assert (u = true). { subst. simpl in *. eapply A; auto. }
          subst u. subst ur. simpl in *; intuition. 
        }
        {
          rewrite plift_if. intros ? ? Q.  repeat rewrite pif_false in *. repeat rewrite por_empty_r in *.
          destruct uf'; try contradiction. eapply QF4 in Q.
          destruct a2; try contradiction. simpl in *. 
          assert (u = true). { subst. simpl in *. eapply A; auto. }
          subst u. subst ur. simpl in *; intuition.
        }
        simpl in *. rewrite plift_if. destruct uf'. eauto. unfoldq; intuition.
        simpl in *. rewrite plift_if. rewrite splice_acc. replace (2+length V2') with (S (S (length V2'))). 
        destruct uf'. eauto. unfoldq; intuition. lia.

        simpl in *. rewrite splice_acc. replace (2+length V2') with (S (S (length V2'))).  eauto. lia.
    * (* mention *) 
       assert (e2 = false). destruct e2,a2; intuition.
       assert (a2 = false \/ u = false). { unfold bsub in *. destruct e2,a2,ur, al,u; intuition. }
       subst e2. 
       eapply exp_mentionable1. 
       2: auto. 
       2: { destruct H28. left. auto. subst u. simpl in *.
            destruct ur, a2; simpl in HeqD; intuition.     
          }
       edestruct IHW1 with (u := false)(M := MX) (H1' := (vz1::ve1::H1')) (H1 := H1) (H2' := (vz2::ve2::H2')) (H2 := H2)
              (V1' := (qempty::qempty::V1')) (V1 := V1) (V2' := (qempty::qempty::V2')) (V2 := V2) 
              (G := G)(G' := (T2, false, a2) :: (T1, false, al) ::G')(ls1 := qempty)
       as (S1''' & S2''' & M''' & vf1 & vf2 & uf' & lsf1 & lsf2 & SC3 & STW3 & EF1 & EF2 & LSF1 & LSF2 & ST''' & VF & UF & ZF & QF1 & QF2 & QF3 & QF4 & SW1' & SW2' & STREL3); eauto.
       simpl. eauto.
       {
          simpl in *. eapply envt_tighten. eapply envt_extend. eapply envt_extend.
          eapply envt_store_changeV' with (M:=M).
          destruct u. eapply envt_strengthenW1; eauto. rewrite <- plift_or in WFE. rewrite <- plift_or in WFE. 
          rewrite subst_ql_qql in WFE. eapply WFE.
          eapply envt_tighten. eauto. rewrite <- subst_ql_qql. repeat rewrite plift_or. unfoldq; intuition. 
          destruct ST, ST', ST'', STX. lia.
          destruct ST, ST', ST'', STX. lia.
          2: eauto. 5: eauto.

          {
            destruct al; simpl. {
            eapply valt_reset_locs. eapply valt_usable. eauto. intuition. intuition.
            } {
              simpl in *. subst ul'.
              repeat rewrite pif_false in *. repeat rewrite por_empty_r in *.
              eapply psub_empty' in LEX3; auto. eapply psub_empty' in LXE4; auto.
              subst. simpl in *. eauto.
            }
          }
          {
            rewrite plift_empty. unfoldq; intuition.
          }
          {
            rewrite plift_empty. unfoldq; intuition.
          }
          {
            destruct H28.
            - subst a2. simpl in *. repeat rewrite pif_false in *. repeat rewrite por_empty_r in *.
              eapply psub_empty' in LXZ3; auto. eapply psub_empty' in LXZ4; auto. subst. eauto. 
            - subst u. simpl in *. 
               destruct a2; simpl in *. 
               -- rewrite UZ1 in *.  eapply psub_empty' in LXZ1; auto. eapply psub_empty' in LXZ2; auto. subst. eauto. 
               -- repeat rewrite pif_false in *. repeat rewrite por_empty_r in *.
                  eapply psub_empty' in LXZ3; auto. eapply psub_empty' in LXZ4; auto. subst. eauto. 
          } 
          {
            rewrite plift_empty. unfoldq; intuition.
          }
          {
            rewrite plift_empty. unfoldq; intuition.
          }
          
          eapply hast_fv in W1. rewrite <-subst_ql_qql. repeat rewrite plift_or. rewrite subst_ql_or. rewrite subst_ql_or.
          intros ? ?. subst p p2. rewrite plift_diff.  rewrite plift_or, plift_one, plift_one. simpl in *.  
          repeat rewrite app_length in *. simpl in *.
          unfold subst_ql in *.  unfoldq; intuition.
          bdestruct (x4 <? length V2); intuition.
          bdestruct (x4 =? length G'+ length G); intuition. bdestruct (x4 =? S (length G'+ length G)); intuition.
          bdestruct (x4 <? length V2); intuition.
          bdestruct (x4 =? length G'+ length G); intuition. bdestruct (x4 =? S (length G'+ length G)); intuition.
     }
      {
        rewrite plift_empty. unfoldq; intuition.
      }
      intros. eapply aux2'; eauto.
      {
        intros. edestruct WK with (S2X := S2X) as (uv & S2X' & v2 & ls2 & ? & ? &? &? &? & ? &? &?).
        subst p. right. right. rewrite plift_diff. repeat rewrite plift_or. repeat rewrite plift_one.
        simpl. rewrite app_length. simpl. split. auto. unfoldq; intuition.
        eapply H37. destruct ST, ST'. lia. 
        exists ((negb a1)). exists S2X', v2, qempty.
        split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split.
        all: eauto.
        {
          destruct a1; simpl; auto.
          
        }
        {
          rewrite plift_empty. unfoldq; intuition.
        }
        {
          rewrite plift_empty. unfoldq; intuition.
        }
        { 
          destruct a1. {
            simpl in *. subst uv.
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
            simpl in *. eapply aux1 in H42. 2: left; auto. 
            eapply aux1 in H43. 2: left; auto.
            subst ls1 ls2. 
            eapply valt_store_reset. 
            eapply valt_usable. eauto.
            intros ?. auto.
            rewrite plift_empty. unfoldq; intuition.
            rewrite plift_empty. unfoldq; intuition.
            unfold st_len1 in *. simpl. lia.
            unfold st_len2. simpl. lia. 
          }
        }   
        {
          rewrite plift_empty. unfoldq; intuition.
        }
     }   
     
     unfold bsub; auto.
     unfoldq; intuition.
     unfoldq; intuition.
      
     exists S1'''. exists S2'''. exists M'''. eexists.  eexists. eexists. exists (qif uf' lsf1). exists (qif uf' lsf2).  
     split. 2: split. 3: split. 4: split. 5: split. 6: split. 7: split. 8: split. 9: split. 10: split. 
     11: split. 12: split. 13: split. 14: split. 
     all:eauto. 
     simpl in *. rewrite splice_acc. replace (2+length V2') with (S (S (length V2'))). eauto. lia.
     {
       destruct a2; simpl in *. {
         assert (ur = false). {
           destruct ur; simpl in *. inversion HeqD. auto.
         }
         subst ur. subst uf'. 
         eapply valt_reset_locs. eauto. intuition.
       }{
         subst uf'.
         destruct ur. {
           eapply valt_sub_locs. eauto. rewrite plift_if. unfoldq; intuition. rewrite plift_if. unfoldq; intuition.
         } {
           eapply valt_usable. eapply valt_sub_locs. eauto. rewrite plift_if. unfoldq; intuition. rewrite plift_if. unfoldq; intuition.
           intuition.
         }
       }
     }  
     {
       intros. rewrite H26. rewrite plift_if. unfoldq; intuition.
     }  
     
     {
       intros. rewrite H26. rewrite plift_if. unfoldq; intuition.
     }
     {
       rewrite plift_if. repeat rewrite pif_false in *. repeat rewrite por_empty_r in *. 
       intros ? Q.
       destruct uf'; simpl in *; try contradiction.
       eapply QF3 in Q. eauto.
     }
     {
       rewrite plift_if. repeat rewrite pif_false in *. repeat rewrite por_empty_r in *. 
       intros ? Q.
       destruct a2; simpl in *. rewrite UF in *. contradiction.
       rewrite UF in *. eapply QF4. eauto.
     }
   }
   all: unfold bsub in *; auto.
   intros ?. destruct a2, al, e2; simpl in *; auto.
   intros ?. destruct a2, al, e2; simpl in *; auto.
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
  - unfold bsub in *. subst env.
     edestruct IHW as (S1'&S2'&M'&?&?&?&?&?&?). all: eauto.
     { intros ? ?. eapply P1. destruct e1, e2; try contradiction; intuition. }
     { intros ? ?. eapply P2. destruct e1, e2; try contradiction; intuition. }
     exists S1', S2', M', x, x0, (negb a2 || u), (if (negb a2 || u) then x2 else qempty), (if (negb a2 || u) then x3 else qempty).
     eapply exp_sub_stp2; eauto. 
     eapply stp_fundamental in H. eapply H. 
Unshelve. eauto.
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


Lemma beta_equivalence': forall t1 t2 G T1 T2 pt1 pt2 fr a a1 e af,
  has_type ((T1,false,a1)::G) t2 T2 (qor pt1 (qone (length G))) fr a e -> 
  has_type G t1 T1 pt2 false a1 false -> (* fr1 = false and e1 = false required! *)
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

Corollary beta_equivalence: forall t1 t2 G T1 T2 pt1 pt2 fr a a1 e,
  has_type ((T1,false,a1)::G) t2 T2 (qor pt1 (qone (length G))) fr a e -> 
  has_type G t1 T1 pt2 false a1 false -> (* fr1 = false and e1 = false required! *)
  psub (plift pt1) (pdom G) ->
  psub (plift pt2) (pdom G) ->
  sem_type G (tapp (tabs t2) t1) (subst_tm t2 (length G) t1) T2 (por (plift pt1) (plift pt2)) fr a e.
Proof. 
  intros. eapply beta_equivalence' with (af := true); eauto.
  intros ? ? ? ?. unfold bsub. auto.
Qed.  


End STLC.