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

Require Import f_sub_arena.

(* ======== Lemmas ========= *)
Lemma t_var_lookup: forall Γ φ Σ v T q fr,
  indexr v Γ = Some (bind_tm, fr, T, q) ->
  closed_ty 0 v (‖ Σ ‖) T ->
  closed_Qual 0 v (‖ Σ ‖) q ↑ ->
  ♦∉ q ->
  q ⊑↑ φ ->
  has_type Γ φ Σ $ v T $! v ->
  has_type Γ φ Σ $ v T q. 
intros. eapply t_sub; eauto. apply stp_refl. 
apply has_type_closed in H4; intuition.
eapply qs_qvar; eauto. apply has_type_filter in H4. eapply Subq_trans; eauto.
Qed.

Lemma t_subq : forall {Γ φ Σ t T q} q',
  has_type Γ φ Σ t T q' ->
  qstp Γ Σ q' q ->
  q ⊑↑ φ ⊔ {♦} ->
  has_type Γ φ Σ t T q.
Proof.
  intros. eapply t_sub; eauto. eapply stp_refl; eauto. apply has_type_closed in H; intuition. 
Qed.

Lemma open_qual_fresh_id : forall q n,
([[n ~> q ]]ᵈ {♦}) = {♦}.
intros. Qcrush.
Qed.

Lemma open_qual_empty_id' : forall k q, [[ k ~> q]]ᵈ ∅ = ∅.
Qcrush.
Qed.

Lemma open_qual_bv: forall b q,
[[b ~> q ]]ᵈ #! b = q.
intros. qual_destruct q. unfold open_qual. ndestruct (qbvs #! b b). 
- apply Q_lift_eq. Qcrush. 
- exfalso. Qcrush.
Qed.

Lemma open_qual_bv_id: forall b b' q,
  b <> b' ->
  [[b ~> q ]]ᵈ #! b' = #! b'.
intros. qual_destruct q. unfold open_qual. ndestruct (qbvs #! b' b). 
- apply Q_lift_eq. Qcrush. 
- auto.
Qed.

Lemma open_qual_fv: forall b f q,
[[b ~> q ]]ᵈ $! f = $!f.
intros. qual_destruct q. unfold open_qual. ndestruct (qbvs $! f b). 
- apply Q_lift_eq. Qcrush. 
- auto.
Qed.

Lemma open_qual_loc: forall b l q,
[[b ~> q ]]ᵈ &!l = &!l.
intros. qual_destruct q. unfold open_qual. ndestruct (qlocs &!l b). 
- apply Q_lift_eq. Qcrush. 
- auto.
Qed.

Lemma open_qual_empty_id : forall k q, [[ k ~> q]]ᵈ ∅ = ∅.
  Qcrush.
Qed.

Lemma qand_diamond_r_non_fresh : forall q, ♦∉ q -> (q ⊓ {♦}) = ∅.
intros. apply Q_lift_eq. Qcrush.
Qed.

Lemma qand_diamond_r_fresh : forall q, ♦∈ q -> (q ⊓ {♦}) = {♦}.
intros. apply Q_lift_eq. Qcrush.
Qed.

Lemma diamond_qqcap_diamond_r : forall q, (q ⋒ {♦}) = {♦}.
#[local] Hint Resolve is_true_reflect : bdestruct.
  intros. unfold "⋒". bdestruct (♦∈? q).
#[local] Remove Hints is_true_reflect : bdestruct.
- rewrite qand_diamond_r_fresh. Qcrush. auto.
- rewrite qand_diamond_r_non_fresh. Qcrush. auto.
Qed.

Lemma qqcap_disjoint_diamond : forall q1 q2,
  q1 ⊓ q2 = ∅ -> (q1 ⋒ q2) = {♦}.
intros. 
  intros. unfold "⋒". rewrite H. 
destruct (♦∈? ∅); Qcrush.
Qed.

Lemma qand_fv_neq : forall n m ,
  n <> m -> $! n ⊓ $! m = ∅.
intros. apply Q_lift_eq. Qcrush. 
Qed.

Lemma wf_senv_empty : wf_senv [].
  unfold wf_senv. intros. inversion H; auto.
Qed.

Lemma weaken_2 :forall {Γ φ t T d},
  wf_tenv Γ [] ->
  has_type Γ φ [] t T d -> forall {X1 X2},
  wf_tenv (X2 :: Γ) [] ->
  has_type (X1 :: X2 :: Γ) φ [] t T d.
intros Γ φ t T d wft HT X1 X2 Hwf.
apply has_type_closed in HT as Hcl. destruct Hcl as [Hcl1 [Hcl2 [Hcl3 Hcl4]]].
replace (X1 :: X2 :: Γ) with ((splice_tenv (‖X2::Γ‖) []) ++ X1 :: (X2 :: Γ)) by auto. erewrite <- (@splice_ty_id T 0 (‖ X2 :: Γ‖) 0). erewrite <- (@splice_id t 0 (‖ X2 :: Γ‖) 0). erewrite <- (@splice_qual_id φ 0 (‖ X2 :: Γ‖) 0). erewrite <- (@splice_qual_id d 0 (‖ X2 :: Γ‖) 0). eapply weaken_gen; auto. apply wf_senv_empty.
erewrite <- (@splice_ty_id T 0 (‖ Γ‖) 0). erewrite <- (@splice_id t 0 (‖ Γ‖) 0). erewrite <- (@splice_qual_id φ 0 (‖ Γ‖) 0). erewrite <- (@splice_qual_id d 0 (‖ Γ‖) 0). replace ([]:tenv) with (splice_tenv (‖Γ‖) []) by auto. eapply weaken_gen; auto. apply wf_senv_empty.
all : auto. 1-2: eapply closed_Qual_monotone; eauto. eapply closed_tm_monotone; eauto. eapply closed_ty_monotone; eauto.
Qed.

(* ============= defs ============= *)

Definition seq (t1 t2: tm) :=
  tapp (tabs ([[1 ~> tunit ]]ᵗ ([[0 ~> tunit ]]ᵗ t2))) t1.

Definition tlet (t1 t2 : tm) := tapp (tabs t2) t1.

Notation "t1 ';ₜ' t2" := (seq t1 t2) (at level 10).
Notation "t1 '::=' t2" := (tassign t1 t2) (at level 10).

Notation " { a | b } ==> { c | d }"  := (TFun b d a c)
(at level 10, format "'[' '[hv' '{' a  '/' '|'  b '}' ']' '/  '  '==>'  '[hv' '{' c  '/' '|'  d '}' ']' ']'").

Notation "∀<:{ a | b }.{ c | d }"  := (TAll b d a c)
(at level 10, format "'[' '[hv' '∀<:{' a  '/' '|'  b '}.{' ']' '/  '  '[hv' c  '/' '|'  d '}' ']' ']'").

Notation " 'λ' t" := (tabs t) (at level 10). 

(* We always use &!0 as the arena we'll allow recursion, so use this alias *)
Notation " 'refa' t" := (trefat t (tloc 0 0)) (at level 10).

Definition store_arena0 := [ [(TUnit, ∅)] ] .

(* tactics *)
Ltac simp := unfold open_tm', open_ty', openq', open_tm, open_ty, openq; simpl; repeat rewrite open_qual_bv, open_qual_fv, open_qual_empty_id', open_qual_bv_id.

Ltac simps := unfold open_tm', open_ty', openq', open_tm, open_ty, openq; simpl; repeat rewrite open_qual_bv; repeat rewrite open_qual_fv; repeat rewrite open_qual_empty_id'; repeat rewrite open_qual_bv_id; repeat rewrite open_qual_fresh_id.

(* ================== stepping ============= *)
Inductive multi_step: tm -> store -> tm -> store -> Prop :=
| multi_step_one : forall (t1 t2 : tm) (σ1 σ2 : store),
    step t1 σ1 t2 σ2 ->
    multi_step t1 σ1 t2 σ2
| multi_step_cons : forall (t1 t' t2 : tm) (σ1 σ' σ2 : store),
    step t1 σ1 t' σ' ->
    multi_step t' σ' t2 σ2 ->
    multi_step t1 σ1 t2 σ2
.

Lemma multi_step_trans: forall t1 t2 t' σ1 σ2 σ',
  multi_step t1 σ1 t' σ' ->
  multi_step t' σ' t2 σ2 ->
  multi_step t1 σ1 t2 σ2.
intros. induction H.
- eapply multi_step_cons; eauto. 
- intuition. eapply multi_step_cons; eauto. 
Qed.

Lemma η_reduction : forall f f' l, f = λ (tapp f' #1) -> closed_tm 0 0 l f' ->
  forall x σ, value x -> step (tapp f x) σ (tapp f' x) σ.
intros. subst.
replace (tapp f' x) with ((tapp f' # 1) <~ᵗ (λ (tapp f' #1)); x).
apply step_beta; auto. simp. repeat erewrite closed_tm_open_id; eauto.
Qed.

(* stepped result of applying f to v *)
Definition unwrap (f : tm) (v : tm) : tm := match f with
                                       | λ body => (body <~ᵗ (λ body); v)
                                       | _ => f 
                                            end.

(* unwraps when applied to a value *)
Definition unwraps (f : tm) := forall v σ, value v -> value (unwrap f v) /\ step (tapp f v) σ (unwrap f v) σ.



Section landin_knot.

(* Landin's knot

val x = ref(λy.y) at &0 : Ref[(TUnit => TUnit)^&0]^&0
def f(x: Unit) = {(!c)(x)} : (Unit => Unit)^&0
x := f

let x = ref (λy. y)   // (U -> U)
in (x := (λz. (!x)(z)))

*)

Definition knot := tlet (tref tunit) (tlet (trefat (tabs tunit) #1) (#1 ::= (tabs (tapp (! #3) #1)))).

Example knot_typable:
  has_type [] ∅ [] knot TUnit ∅.
Proof.
  unfold knot. remember (tlet (trefat (λ tunit) # 1) (# 1 ::= (λ (tapp ! # 3 # 1)))) as t. unfold tlet.
  replace (∅) with (∅ <~ᵈ ∅; {♦}) at 2.
  replace TUnit with (TUnit <~ᵀ TUnit ~ ∅; (TRef ∅ TUnit) ~ {♦}).
  apply t_app_fresh. unfold q_trans_tenv; simpl. rewrite diamond_qqcap_diamond_r. 
  2:{ apply t_ref; auto. } 2-7: simpl; auto; constructor; auto.
  apply t_abs. 1-6: auto. 
  (* starting to handle t *) subst. repeat constructor; auto.
  subst. unfold open_tm', open_ty', openq'; simpl. unfold open_ty, openq; simpl. repeat rewrite open_qual_empty_id.
  unfold knot, tlet.
  replace (∅) with (∅ <~ᵈ $!1; $!1) at 6.
  replace TUnit with (TUnit <~ᵀ TUnit ~ ∅; (TRef $!1 (TFun ∅ ∅ TUnit TUnit)) ~ $!1) at 4.
  eapply t_app; eauto. 
  eapply t_abs; eauto.
  simpl. repeat constructor; auto.
  simpl. constructor; auto. constructor; auto. Qcrush. simpl. Qcrush. constructor; auto. Qcrush. constructor; auto; Qcrush. Qcrush.
  simpl. unfold open_tm', open_ty', openq'; simpl.
  eapply t_assign.
  eapply t_var.
  all: simpl; auto. Qcrush. Qcrush.
  constructor; auto. Qcrush. Qcrush. 
  eapply t_sub with (T1 := ({TUnit | ∅} ==> {TUnit | ∅})) (d1 := $!1 ⊔ $!3). 2: apply stp_refl; auto. 2: {
    replace ($!1) with ($! 1 ⊔ $! 1) at 7. 2: apply qor_idem.
    apply qs_cong. 2: Qcrush.
    eapply qs_qvar; simpl; eauto. constructor; Qcrush. constructor; Qcrush. 
  } 2: Qcrush.
  eapply t_abs; simpl; eauto. 
  constructor; auto. Qcrush.
  unfold open_tm', open_ty', openq'; simpl.
  replace (∅ <~ᵈ $! 4; $! 5) with (∅ <~ᵈ $!1 ; ∅).
  replace (TUnit <~ᵀ $ 4 ~ $! 4; $ 5 ~ $! 5) with (TUnit <~ᵀ TUnit ~ ∅; TUnit ~ ∅).
  apply t_app; auto.
  eapply t_deref. eapply t_var. 
  simpl. eauto. Qcrush. Qcrush. constructor; Qcrush. Qcrush. Qcrush. Qcrush. 
  eapply t_sub. eapply t_var; simpl; eauto. Qcrush. Qcrush. 
  constructor; auto. eapply qs_qvar; simpl; eauto. Qcrush. constructor.
  simpl; auto. Qcrush. 
  {eapply t_refat. 2-3: Qcrush. apply t_abs; auto. Qcrush. Qcrush. 
  unfold open_tm', open_ty', openq'; simpl. replace (TUnit <~ᵀ $ 2 ~ $! 2; $ 3 ~ $! 3) with TUnit by auto. apply t_base. Qcrush.
  eapply t_var. simpl; auto. Qcrush. simpl; auto. Qcrush. constructor; auto. Qcrush. }
  constructor.
Qed.


End landin_knot.





(* ============ fixpoint ============== *)

Section fixpoint.

(*
  In order for simplicity of example, we manually reduced the definition of the fixpoint, namely using lambda instead of a name binding in the def
  Alternatively, we using stepping lemmas to check the reduced def is still a fixpoint
*)

(*
  id = 
  def fix(f : (g : (T -> T) -> (T -> T) )  ) -> (T -> T) = 
    let c = new Ref ( λx.x ) in
    def f2(n : T) -> T = (!c)(n) ;
    c := f(f2) ;
    m => (!c)(m)
*)


Example static_ctx := [(bind_tm, false, TRef ∅ TUnit, {♦}); (bind_tm, true, {TRef ∅ TUnit | {♦}} ==> {TInt | ∅}, ∅)].

Lemma wf_tenv_static_ctx : wf_tenv static_ctx [].
Proof.
  unfold static_ctx. constructor; auto. constructor; auto. constructor. apply wf_senv_empty.
Qed.

Definition fixpoint2 := λ (tapp (λ (tapp (λ ! #3) (#1 ::= (tapp #3 (λ (tapp (! #3) #1)))))) (trefat (λ #1) #3)).

Example fixpoint2_inner := λ (tapp (λ (tapp (λ ! #3) (#1 ::= (tapp #3 (λ (tapp (! #3) #1)))))) (trefat (λ #1) $1)).

(* here we can also wrap a polymorphism level to make a polymorphic fixpoint *)
Definition fixpoint := ttabs fixpoint2.

Definition fixpoint_T := 
  (* argument type: f:(g:(Int => Int)^&!0 => (Int => Int)^g)^f *)
  ({ { {# 1 | ∅} ==> {#3 | ∅} | $!1 } ==> (* function g *)
  { {# 3 | ∅} ==> {#5 | ∅} | #!1 } | $!1 } ==> 
  (* return type: (Int => Int)^&!0 *)
  { {#3 | ∅} ==> {#5 | ∅} | $!1 }).


Lemma fixpoint2_inner_open : open_tm' ([]:tenv) fixpoint2 = fixpoint2_inner.
Proof.
  unfold fixpoint2. unfold fixpoint2. unfold open_tm'; simpl. auto.
Qed. 

Definition refa_static := (trefat (λ #1) $1).

Definition refa_static_ty := (TRef $!1 ({TInt | ∅} ==> {TInt | ∅})).



Lemma refa_static_typable:
  has_type static_ctx ($! 1) [] refa_static refa_static_ty $!1.
Proof.
  eapply t_refat; eauto. apply t_abs; auto. simpl. Qcrush. Qcrush. unfold open_tm',open_ty',openq'. simpl. 
  eapply t_var_lookup. simpl; eauto. 5: eapply t_var. 5: simpl; auto. 
  all: simps; eauto. Qcrush. Qcrush.
  eapply t_var. simpl; eauto. Qcrush. 2: simpl; eauto. 1-2: Qcrush.
Qed.



Lemma refa_static_via_var_typable:
  has_type static_ctx
  ($!1 ⊔ {♦}) [] (λ (tapp (λ (! #1)) refa_static))
  (* arg type *)
  ({ TInt | ∅ } ==>
  (* return type *)
  {({TInt | ∅} ==> {TInt | ∅}) | $!1})
  (* capturing set *)
  $!1.
Proof.
  apply t_abs; auto. repeat constructor; auto. constructor; simpl; Qcrush. simpl. Qcrush.
  simp. repeat rewrite open_qual_empty_id'.
  replace ({TInt | ∅} ==> {TInt | ∅}) with (({TInt | ∅} ==> {TInt | ∅}) <~ᵀ TUnit ~ ∅; refa_static_ty ~ $!1).
  replace ([[1 ~> $! 3 ]]ᵈ ([[0 ~> $! 2 ]]ᵈ $!1)) with ($!1 <~ᵈ $!1; $!1).
  apply t_app. apply t_abs; auto.
  unfold refa_static_ty; constructor; simpl; auto. Qcrush. Qcrush. constructor; eauto. Qcrush. Qcrush.
  simp. replace ([[1 ~> $! 3 ]]ᵈ ([[0 ~> $! 2 ]]ᵈ $!1)) with ($!1). 
  eapply t_deref; auto. eapply t_var_lookup. simpl. eauto.
  constructor; simpl; auto. Qcrush. Qcrush. Qcrush. Qcrush.
  eapply t_var; simpl; eauto. Qcrush. Qcrush. constructor; simpl; auto. 1-3: Qcrush.
  eapply weaken_flt. eapply weaken_2. apply wf_tenv_static_ctx. eapply refa_static_typable; auto. constructor; auto. apply wf_tenv_static_ctx. constructor; auto. Qcrush. constructor; auto. 1-5: Qcrush. constructor. Qcrush. intuition.  
Qed.

Lemma ret_static_typable: forall c,
  has_type static_ctx
  ($!1 ⊔ {♦}) [] (tapp (λ (tapp (λ (! #1)) refa_static)) (tnat c))
  ({TInt | ∅} ==> {TInt | ∅}) $!1.
Proof.
  replace ({TInt | ∅} ==> {TInt | ∅}) with (({TInt | ∅} ==> {TInt | ∅}) <~ᵀ TUnit ~ ∅; TInt ~ ∅); auto.
  replace ($!1) with ($!1 <~ᵈ $!1; ∅).
  intros. apply t_app; auto. replace ($!1 <~ᵈ $!1; ∅ ⊔ {♦}) with ($!1 ⊔ {♦}). apply refa_static_via_var_typable. simp. rewrite open_qual_fv; auto. 
  constructor. Qcrush. Qcrush. constructor. Qcrush.
Qed.


Lemma fixpoint2_inner_typable:
  has_type static_ctx $!1 [] fixpoint2_inner
    (* argument type: f:(g:(Int => Int)^&!0 => (Int => Int)^g)^f *)
    ({ { {TInt | ∅} ==> {TInt | ∅} | $!1 } ==> (* function g *)
    { {TInt | ∅} ==> {TInt | ∅} | #!1 } | $!1 } ==> 
    (* return type: (Int => Int)^&!0 *)
    { {TInt | ∅} ==> {TInt | ∅} | $!1 }) $!1.
Proof.
  unfold fixpoint2_inner.
  apply t_abs; auto.
  repeat constructor; auto.
  constructor; auto. 1-2: Qcrush. constructor; auto. 1-4: Qcrush.
  simpl. unfold open_tm', open_ty', openq'; simpl.
  remember ({TInt | ∅} ==> {TInt | ∅}) as F.
  replace (F <~ᵀ $ 2 ~ $! 2; $ 3 ~ $!3) with (F <~ᵀ TUnit ~ ∅; (TRef $!1 ({TInt | ∅} ==> {TInt | ∅})) ~ $!1); auto.
  replace ($!1 <~ᵈ $! 2; $!3) with ($!1 <~ᵈ $!1; $!1).
  eapply t_app; auto. 
  (* enlarge with $3 *)
  apply t_subq with (q' := $!1 ⊔ $!3). 2: { replace $!1 with ($!1 ⊔ $!1) at 8. apply qs_cong. eapply qs_qvar; simpl. eauto. constructor; auto. 1-2: Qcrush. 1-2: subst F; constructor; auto. Qcrush. auto. Qcrush. rewrite qor_idem; auto. } 2: Qcrush.  
  apply t_abs; auto.
  simpl. repeat constructor; auto.
  simpl. constructor; auto. Qcrush. Qcrush. constructor; auto. Qcrush.
  subst. constructor; auto. Qcrush. Qcrush. simp.
  2: {
    eapply weaken_flt. eapply weaken_2; auto. apply wf_tenv_static_ctx.
    pose proof refa_static_typable as HH. unfold refa_static, refa_static_ty in *.
    apply HH. constructor; auto. apply wf_tenv_static_ctx. constructor; auto. 1-2: Qcrush. 1-2: subst; constructor; auto. 1-4: Qcrush. Qcrush. 
  }
  subst. simp. repeat rewrite open_qual_empty_id. repeat rewrite open_qual_fv.
  remember ({TInt | ∅} ==> {TInt | ∅}) as F.
  remember (($!1 ⊔ $! 3) ⊔ $! 4 ⊔ $! 5) as φ.
  replace $!1 with ($!1 <~ᵈ $!1; ∅) at 13.
  replace F with (F <~ᵀ TUnit ~ ∅; TUnit ~ ∅) at 9.
  apply t_app; auto.
  (* need to enlarge with $3 *)
  apply t_subq with (q' := $!1 ⊔ $!5). 2: { replace $!1 with ($!1 ⊔ $!1) at 14. apply qs_cong. eapply qs_qvar; simpl. eauto. constructor; auto. subst F. constructor; auto. 1-2: Qcrush. auto. Qcrush. rewrite qor_idem; auto. } 2: subst φ; Qcrush.
  apply t_abs; subst; simp. constructor. constructor. auto.
  constructor; Qcrush. Qcrush. Qcrush. Qcrush. auto. 
  repeat rewrite open_qual_fv. repeat rewrite open_qual_empty_id. 
  replace $! 5 with ([[0 ~> $!5 ]]ᵈ #!0).
  eapply t_deref.
  eapply t_var. simpl. eauto. Qcrush. simp. 
  rewrite open_qual_bv. Qcrush. simpl; constructor; auto. Qcrush. Qcrush. Qcrush. Qcrush. rewrite open_qual_bv; auto.
  eapply t_assign with (d1:=$!1) (T:=F) (d:=$!5). 
  eapply t_var; simpl; eauto. subst. Qcrush. subst. Qcrush. subst. constructor; simpl; auto. Qcrush. Qcrush.
  (* apply f to f2, a fresh application *)
  replace ($!1) with (#!1 <~ᵈ $!3; $!1) at 13.
  replace F with (F <~ᵀ TUnit ~ ∅; F ~ $!1) at 9.
  apply t_app. subst; simp; auto. repeat rewrite open_qual_empty_id. 
  eapply t_var. simp. auto. Qcrush. Qcrush. constructor; auto. Qcrush. Qcrush. Qcrush.
  (* typing f2 *)
  (* enlarge with $3 *)
  apply t_subq with (q' := $!1 ⊔ $!5). 2: { replace $!1 with ($!1 ⊔ $!1) at 14. apply qs_cong. eapply qs_qvar; simpl. eauto. constructor; auto. 1-2: Qcrush. 1-2: subst F; constructor; auto. Qcrush. auto. Qcrush. auto. Qcrush. rewrite qor_idem; auto. } 2: subst; Qcrush.    
  subst. apply t_abs; auto. Qcrush. Qcrush. simp. repeat rewrite open_qual_empty_id. 
  remember ({TInt | ∅} ==> {TInt | ∅}) as F. 
  replace TInt with (TInt <~ᵀ TUnit ~ ∅; TInt ~ ∅).
  replace (∅) with (∅ <~ᵈ $!1; ∅).
  apply t_app; auto. 
  eapply t_deref; auto. 
  eapply t_var. simpl. subst; eauto. Qcrush. Qcrush. constructor; auto. 1-2: Qcrush. Qcrush.
  eapply t_sub with (d1:=$!7). 
  eapply t_var. simp. auto. Qcrush. Qcrush. constructor. Qcrush. 
  apply stp_refl; auto. eapply qs_qvar. simp. all: auto.
  constructor. simp. rewrite open_qual_bv. Qcrush. subst. constructor. subst. intuition. simp. rewrite open_qual_bv; auto. simp. repeat rewrite open_qual_fv. subst. Qcrush. subst. constructor. subst. constructor. 
    simp. repeat rewrite open_qual_fv. Qcrush. 
    subst. constructor; auto. 
    subst. simp. repeat rewrite open_qual_empty_id; auto.
Qed.

(* λy.λx.(y x) *)
Definition loop_fix := (λ (λ (tapp #3 #1))).


(* y:(T=>T) => (T=>T)^y *)
Lemma loop_fix_typable : has_type static_ctx $!1 [] loop_fix 
   ({ {TInt | ∅} ==> {TInt | ∅} | $!1 } ==> 
    { {TInt | ∅} ==> {TInt | ∅} | #!1 }) $!1.
Proof.
  unfold loop_fix. 
  apply t_abs; auto.
  constructor. constructor; auto. 
  constructor; Qcrush. Qcrush.
  simp. repeat rewrite open_qual_empty_id. rewrite open_qual_bv. 
  apply t_abs; auto.
  Qcrush. Qcrush.
  simp. repeat rewrite open_qual_empty_id.
  replace (∅) with (∅ <~ᵈ $!3; ∅).
  replace (TInt) with (TInt <~ᵀ TUnit ~ ∅; TInt ~ ∅); auto.
  apply t_app; auto.
  eapply t_var; simpl; eauto. Qcrush. Qcrush.
  simp. rewrite open_qual_empty_id. eapply t_sub with (d1:=$!5). 
  eapply t_var; simpl; eauto. Qcrush. Qcrush.
  apply stp_refl; auto. eapply qs_qvar; simpl; eauto. Qcrush.
  1-2:unfold not_free; auto. 
Qed.


(*
  f = λg.λx.g(x) 
  fix f = f (fix f) = λg.λx.g(x) (fix f) = λx.(fix f)(x) 
  (fix f)(c) = (fix f)(c)
  loop = (fix f)
*)
Definition loop := (tapp fixpoint2 (λ (λ (tapp #3 #1)))).


(* The example must evaluate in a context where we pre-define a reference (just as base reference), so loop_static does not closed under 0 0
  After let x = ref tunit, loop_static will be opened to loop_inner in the context = static_ctx
*)
Lemma loop_typable : forall c, has_type [] ∅ [] (tlet (tref tunit) (tapp loop (tnat c))) TInt ∅.
Proof.
  intros.
  (* handle outer tlet *)
  unfold tlet at 1.
  replace (∅) with (∅ <~ᵈ ∅; {♦}) at 2.
  replace TInt with (TInt <~ᵀ TUnit ~ ∅; (TRef ∅ TUnit) ~ {♦}).
  apply t_app_fresh. unfold q_trans_tenv; simpl. rewrite diamond_qqcap_diamond_r. 
  2:{ apply t_ref; auto. } 2-7: subst; simpl; auto. 2,3: constructor; auto. 
  apply t_abs. 1-6: auto. 1: subst; constructor; auto. 1: unfold fixpoint2; repeat constructor; auto. simpl. 
  unfold open_ty', open_ty, openq', openq, open_tm', open_tm. simpl. fold fixpoint2_inner. (* convert to fixpoint2_inner *) repeat rewrite open_qual_empty_id. 
  (* normal step *)
  unfold loop.
  replace (∅) with (∅ <~ᵈ $!1; ∅) at 6.
  replace (TInt) with (TInt <~ᵀ TUnit ~ ∅; TInt ~ ∅); auto.
  apply t_app; auto. 
  (* then just normal proof *)
  remember ({TInt | ∅} ==> {TInt | ∅}) as F.
  replace ($!1) with ($!1 <~ᵈ $!1; $!1) at 2.  
  replace (F) with (F <~ᵀ TUnit ~ ∅; ({ F | $!1 } ==> 
    { F | #!1 }) ~ $!1) at 1; auto.
  apply t_app.
  simp. repeat rewrite open_qual_fv. subst. eapply weaken_flt. eapply fixpoint2_inner_typable. Qcrush. Qcrush.
  simp. repeat rewrite open_qual_fv. subst. eapply weaken_flt. apply loop_fix_typable. 
  all: subst; auto.
  all: unfold not_free; Qcrush; auto.
  constructor. Qcrush. 
Qed.

End fixpoint.

(* ================= factorial example ================== *)

(* Computation: "fact" , and F is renamed into "fact_fix"
    F(f : Int => Int) : (Int => Int) := 
      x => if (iszero x) then 1 else x * f (pred x)   // F : (I -> I) -> I -> I
    fact = fixpoint F     // fact : I -> I
    fact n = (fixpoint F) n ~= F (fixpoint F) n ~= F (fact) n
      (F fact) expands to 
      x => if (iszero x) then 1 else x * fact (pred x) )
    so it's good
*)

Section fact.

Definition fact_fix := λ (*f=#1*) (λ (* f=#3, x=#1 *) (
  tif (tiszero #1) (tnat 1) (
    tmul (#1) (tapp (#3) (tpred #1))
  )
)).

Definition TF := ({TInt | ∅} ==> {TInt | ∅}).
Example TF_closed : closed_ty 0 0 0 TF.
Proof.
  unfold TF. constructor; auto.
Qed.

Definition T_fact_fix := { TF | $!1 } ==> {TF | #!1 }.

Example fact_fix_typable : has_type static_ctx $!1 [] fact_fix T_fact_fix $!1.
Proof. 
  unfold fact_fix, T_fact_fix.
  apply t_abs; auto.
  constructor. repeat constructor; auto. 
  constructor; Qcrush. 1-2: constructor; auto. Qcrush.
  simp. repeat rewrite open_qual_empty_id. rewrite open_qual_bv. 
  apply t_abs; simpl; auto.
  repeat constructor; auto. Qcrush. Qcrush.
  simp. repeat rewrite open_qual_empty_id.
  (* body parts *) replace (∅) with (∅ ⊔ ∅). 2: Qcrush. eapply t_if with (q1:=∅).
  eapply t_iszero. eapply t_var; simpl; eauto. Qcrush. Qcrush.
  eapply t_nat. simpl. Qcrush.
  apply t_mul with (q1:=∅) (q2:=∅). eapply t_var_lookup; simpl; eauto. eapply t_var; simpl; eauto. Qcrush. Qcrush.
    rewrite qor_empty_left. replace (∅) with (∅ <~ᵈ $!3; ∅). replace (TInt) with (TInt <~ᵀ TUnit ~ ∅; TInt ~ ∅); auto. 2: Qcrush.
    eapply t_app; auto. eapply t_var; simpl; eauto. 1-2: Qcrush.
    eapply t_pred. eapply t_var; simpl; eauto. Qcrush. Qcrush. 1: constructor. 
Qed.


Definition fact := tapp fixpoint2 (fact_fix).

Lemma fact_typable : forall c, has_type [] ∅ [] (tlet (tref tunit) (tapp fact (tnat c)) ) TInt ∅.
Proof.
  intros. unfold tlet. 
  replace (∅) with (∅ <~ᵈ ∅; {♦}) at 2.
  replace TInt with (TInt <~ᵀ TUnit ~ ∅; (TRef ∅ TUnit) ~ {♦}).
  apply t_app_fresh. unfold q_trans_tenv; simpl. rewrite diamond_qqcap_diamond_r. 
  2:{ apply t_ref; auto. } 2-7: subst; simpl; auto. 2,3: constructor; auto. 
  apply t_abs. 1-6: auto. 1: subst; constructor; auto. 1: unfold fixpoint2; repeat constructor; auto. simpl. 
  unfold open_ty', open_ty, openq', openq, open_tm', open_tm. simpl. fold fixpoint2_inner. (* convert to fixpoint2_inner *) repeat rewrite open_qual_empty_id. 
  (* normal steps, just replace &!0 -> $!1 and splice fvs by 2 *)
  replace (TInt) with (TInt <~ᵀ TUnit ~ ∅; TInt ~ ∅); auto.
  replace (∅) with (∅ <~ᵈ $!1; ∅).
  apply t_app; auto.
  remember ({TInt | ∅} ==> {TInt | ∅}) as F.
  replace (F) with (F <~ᵀ TUnit ~ ∅; ({ F | $!1 } ==> 
    { F | #!1 }) ~ $!1); auto.
  replace ($!1) with ($!1 <~ᵈ $!1; $!1).
  apply t_app.
  simp. repeat rewrite open_qual_fv. repeat rewrite open_qual_empty_id. subst. eapply weaken_flt. apply fixpoint2_inner_typable. Qcrush. Qcrush.
  simp. repeat rewrite open_qual_fv. repeat rewrite open_qual_empty_id. subst. eapply weaken_flt. apply fact_fix_typable. 
  all: subst; auto.
  all: unfold not_free; auto.
  1-3: Qcrush.
  constructor. Qcrush. 
Qed.

End fact.