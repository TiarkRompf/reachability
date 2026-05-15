import Lean4.LangLemmas
import Aesop

-- [-simp] is local; redefine them
attribute [-simp] Set.setOf_subset_setOf Set.subset_inter_iff Set.union_subset_iff
attribute [-simp] Finset.union_insert
attribute [-simp] getElem?_pos Finset.singleton_union Finset.union_singleton

namespace Reachability

-- building syntactic system

inductive qtp: tenv → ql → ql → gfset → Prop where
| q_sub:
  q1 ⊆ q2 →
  closed_ql true 0 ‖G‖ q2 →
  qtp G q1 q2 gs
| q_cong:
  qtp G q1a q2a gs →
  qtp G q1b q2b gs →
  qtp G (q1a ∪ q1b) (q2a ∪ q2b) gs
| q_var:
  G[x]? = some (Tx, qx, bn) →
  x ∉ gs →
  closed_ql false 0 ‖G‖ qx →
  qtp G {%x} qx gs
| q_self:
  G[x]? = some (Tx, qx, .self) →
  closed_ql true 0 ‖G‖ qx →
  qtp G (qx \ {✦}) {%x} gs
| q_trans:
  qtp G q1 q2 gs →
  qtp G q2 q3 gs →
  qtp G q1 q3 gs

inductive stp: tenv → ty → ql → ty → ql → gfset → Prop where
| s_refl:
  qtp G q1 q2 gs →
  stp G T q1 T q2 gs
| s_trans:
  closed_ty 0 ‖G‖ T2 →
  stp G T1 q1 T2 q2 gs →
  stp G T2 q2 T3 q3 gs →
  stp G T1 q1 T3 q3 gs
| s_top:
  stp G T q0 .TTop q0 gs
| s_ref:
  stp (G++[(.TTop, q0, .self)]) ([#0 ↦ %‖G‖] T1b) {✦} ([#0 ↦ %‖G‖] T1a) ({✦} ∪ gr1) gs →
  stp (G++[(.TTop, q0, .self)]) ([#0 ↦ %‖G‖] T2a) {✦} ([#0 ↦ %‖G‖] T2b) ({✦} ∪ gr2) gs →
  qtp (G++[(.TTop, q0, .self)]) (gr1 ∪ q1b) q1a gs →
  qtp (G++[(.TTop, q0, .self)]) (gr2 ∪ [#0 ↦ %‖G‖] q2a) ([#0 ↦ %‖G‖] q2b) gs →
  gr1 ⊆ q0 ∪ {%‖G‖} → gr2 ⊆ q0 ∪ {%‖G‖} →
  stp G (.TRef2 T1a q1a T2a q2a) q0 (.TRef2 T1b q1b T2b q2b) q0 gs
| s_pair:
  stp (G++[(.TTop, q0, .self)]) ([#0 ↦ %‖G‖] T1a) {✦} ([#0 ↦ %‖G‖] T1b) ({✦} ∪ gr1) gs →
  stp (G++[(.TTop, q0, .self)]) ([#0 ↦ %‖G‖] T2a) {✦} ([#0 ↦ %‖G‖] T2b) ({✦} ∪ gr2) gs →
  qtp (G++[(.TTop, q0, .self)]) (gr1 ∪ [#0 ↦ %‖G‖] q1a) ([#0 ↦ %‖G‖] q1b) gs →
  qtp (G++[(.TTop, q0, .self)]) (gr2 ∪ [#0 ↦ %‖G‖] q2a) ([#0 ↦ %‖G‖] q2b) gs →
  gr1 ⊆ q0 ∪ {%‖G‖} → gr2 ⊆ q0 ∪ {%‖G‖} →
  stp G (.TProd T1a q1a T2a q2a) q0 (.TProd T1b q1b T2b q2b) q0 gs
| s_list:
  stp (G++[(.TTop, q0, .self)]) ([#0 ↦ %‖G‖] T1) {✦} ([#0 ↦ %‖G‖] T2) ({✦} ∪ gr) gs →
  gr ⊆ q0 ∪ {%‖G‖} →
  stp G (.TList T1) q0 (.TList T2) q0 gs
| s_fun:
  stp (G ++ [(.TTop, qf0, .self)])
    ([#0 ↦ %‖G‖] T1b) {✦}   ([#0 ↦ %‖G‖] T1a) ({✦} ∪ gr1) gs →
  {#0, ✦} ⊆ q1a ∨ qtp (G ++ [(.TTop, qf0, .self)])
    ([#0 ↦ %‖G‖] q1b ∪ gr1) ([#0 ↦ %‖G‖] q1a) gs →
  stp (G ++ [(.TTop, qf0, .self), ([#0 ↦ %‖G‖] T1b, [#0 ↦ %‖G‖] q1b, .var)])
    ([#0 ↦ %‖G‖] [#1 ↦ (%(‖G‖+1), gr1)] T2a) {✦}   ([#0 ↦ %‖G‖] [#1 ↦ %(‖G‖+1)] T2b) ({✦} ∪ gr2) gs →
  qtp (G ++ [(.TTop, qf0, .self), ([#0 ↦ %‖G‖] T1b, [#0 ↦ %‖G‖] q1b, .var)])
    ([#0 ↦ %‖G‖] [#1 ↦ (%(‖G‖+1), gr1)] q2a ∪ gr2) ([#0 ↦ %‖G‖] [#1 ↦ %(‖G‖+1)] q2b) gs →
  gr1 ⊆ qf0 ∪ {%‖G‖} → gr2 ⊆ qf0 ∪ {%‖G‖, %(‖G‖+1)} → ✦ ∉ gr1 →
  stp G (.TFun T1a q1a T2a q2a) qf0 (.TFun T1b q1b T2b q2b) qf0 gs
| s_tvar:
  G[x]? = some (Tx, qx, .tvar) →
  stp G (.TVar (%x)) q0 Tx q0 gs
| s_all:
  stp (G ++ [(.TTop, qf0, .self)])
    ([#0 ↦ %‖G‖] T1b) {✦} ([#0 ↦ %‖G‖] T1a) {✦} gs →
  {#0, ✦} ⊆ q1a ∨ qtp (G ++ [(.TTop, qf0, .self)])
    ([#0 ↦ %‖G‖] q1b)     ([#0 ↦ %‖G‖] q1a) gs →
  stp (G ++ [(.TTop, qf0, .self), ([#0 ↦ %‖G‖] T1b, [#0 ↦ %‖G‖] q1b, .tvar)])
    ([#0 ↦ %‖G‖] [#1 ↦ %(‖G‖+1)] T2a) {✦} ([#0 ↦ %‖G‖] [#1 ↦ %(‖G‖+1)] T2b) ({✦} ∪ gr2) gs →
  qtp (G ++ [(.TTop, qf0, .self), ([#0 ↦ %‖G‖] T1b, [#0 ↦ %‖G‖] q1b, .tvar)])
    ([#0 ↦ %‖G‖] [#1 ↦ %(‖G‖+1)] q2a ∪ gr2)       ([#0 ↦ %‖G‖] [#1 ↦ %(‖G‖+1)] q2b) gs →
  gr2 ⊆ qf0 ∪ {%‖G‖, %(‖G‖+1)} →
  stp G (.TAll T1a q1a T2a q2a) qf0 (.TAll T1b q1b T2b q2b) qf0 gs

def qapp G p qf qx q1 gs :=
  #0 ∈ q1 ∨ qtp G qx q1 gs ∨ ✦ ∈ q1 ∧
    qtp G (vars_trans G qf ∩ vars_trans G qx) q1 gs ∧
    vars_trans G qf ∩ vars_trans G qx ⊆ p ∪ {✦} ∧
    (∀i ∈ gs, %i ∉ vars_trans G qf ∧ %i ∉ vars_trans G qx)

inductive has_type: tenv → ql → tm → ty → ql → gfset → Prop where
| t_unit: has_type G p .tunit .TUnit ∅ gs
| t_nat: has_type G p (.tnat n) .TNat ∅ gs
| t_add:
  has_type G p t1 .TNat q1 gs →
  has_type G p t2 .TNat q2 gs →
  has_type G p (.tadd t1 t2) .TNat ∅ gs
| t_mul:
  has_type G p t1 .TNat q1 gs →
  has_type G p t2 .TNat q2 gs →
  has_type G p (.tmul t1 t2) .TNat ∅ gs
| t_var:
  G[x]? = some (T, q, bn) →
  bn ≠ .tvar →
  %x ∈ p →
  closed_ty 0 ‖G‖ T →
  has_type G p (.tvar x) T {%x} gs
| t_ref:
  has_type G p t T q gs →
  ✦ ∉ q →
  has_type G p (.tref t) (.TRef1 T q) {✦} gs
| t_get:
  has_type G p t (.TRef2 T1 q1 T2 q2) q gs →
  q2 ⊆ p ∪ {#0} →
  (✦ ∈ q → occurs .noneq T2 #0) →
  has_type G p (.tget t) ([#0 ↦ q] T2) ([#0 ↦ q] q2) gs
| t_put:
  has_type G p t1 (.TRef2 T1 q1 T2 q2) q gs →
  has_type G p t2 T1 q1 gs →
  has_type G p (.tput t1 t2) .TUnit ∅ gs
| t_pair:
  has_type G p t1 T1 q1 gs →
  has_type G p t2 T2 q2 gs →
  has_type G p (.tpair t1 t2) (.TProd T1 ([✦ ↦ #0] q1) T2 ([✦ ↦ #0] q2)) (q1 ∪ q2) gs
| t_fst:
  has_type G p t (.TProd T1 q1 T2 q2) q gs →
  q1 ⊆ p ∪ {#0} →
  (✦ ∈ q → occurs .noneq T1 #0) →
  has_type G p (.tfst t) ([#0 ↦ q] T1) ([#0 ↦ q] q1) gs
| t_snd:
  has_type G p t (.TProd T1 q1 T2 q2) q gs →
  q2 ⊆ p ∪ {#0} →
  (✦ ∈ q → occurs .noneq T2 #0) →
  has_type G p (.tsnd t) ([#0 ↦ q] T2) ([#0 ↦ q] q2) gs
| t_nil:
  closed_ty 0 ‖G‖ (.TList T) →
  has_type G p .tnil (.TList T) ∅ gs
| t_cons:
  has_type G p t0 T q0 gs →
  has_type G p t1 (.TList T) q1 gs →
  has_type G p (.tcons t0 t1) (.TList T) (q0 ∪ q1) gs
| t_fold:
  has_type G p tl (.TList T) q1 gs →
  has_type G p t0 U q2 gs →
  has_type (G++[(T, q1, .var), (U, q2, .var)]) (p ∪ {%‖G‖, %(‖G‖+1)}) t1 U q2 gs →
  closed_ty 0 ‖G‖ T → ✦ ∉ q1 → ✦ ∉ q2 →
  has_type G p (.tfold tl t0 t1) U q2 gs
| t_abs:
  has_type (G++[(.TTop, qf, .self), ([#0 ↦ %‖G‖] T1, [#0 ↦ %‖G‖] q1, .var)]) (qf ∪ {%‖G‖, %(‖G‖ + 1)})
    t ([#0 ↦ %‖G‖] [#1 ↦ %(‖G‖+1)] T2) ([#0 ↦ %‖G‖] [#1 ↦ %(‖G‖+1)] q2) gs →
  q1 ⊆ qf ∪ {✦, #0} →
  closed_ty 1 ‖G‖ T1 →
  closed_ty 2 ‖G‖ T2 →
  closed_ql true 1 ‖G‖ q1 →
  closed_ql true 2 ‖G‖ q2 →
  closed_ql false 0 ‖G‖ qf →
  (#0 ∈ q1 → ✦ ∈ q1) →
  occurs .no_covariant T1 #0 →
  occurs .no_contravariant T2 #0 →
  qf ⊆ p →
  has_type G p (.tabs none t) (.TFun T1 q1 T2 q2) qf gs
| t_absa:
  has_type G p (.tabs none t) (.TFun T1 q1 T2 q2) qf gs →
  has_type G p (.tabs (T1, q1) t) (.TFun T1 q1 T2 q2) qf gs
| t_tabs:
  has_type (G++[(.TTop, qf, .self), ([#0 ↦ %‖G‖] T1, [#0 ↦ %‖G‖] q1, .tvar)]) (qf ∪ {%‖G‖, %(‖G‖ + 1)})
    t ([#0 ↦ %‖G‖] [#1 ↦ %(‖G‖+1)] T2) ([#0 ↦ %‖G‖] [#1 ↦ %(‖G‖+1)] q2) gs →
  q1 ⊆ qf ∪ {✦, #0} →
  closed_ty 1 ‖G‖ T1 →
  closed_ty 2 ‖G‖ T2 →
  closed_ql true 1 ‖G‖ q1 →
  closed_ql true 2 ‖G‖ q2 →
  closed_ql false 0 ‖G‖ qf →
  (#0 ∈ q1 → ✦ ∈ q1) →
  occurs .no_covariant T1 #0 →
  occurs .no_contravariant T2 #0 →
  qf ⊆ p →
  has_type G p (.ttabs none t) (.TAll T1 q1 T2 q2) qf gs
| t_tabsa:
  has_type G p (.ttabs none t) (.TAll T1 q1 T2 q2) qf gs →
  has_type G p (.ttabs (T1, q1) t) (.TAll T1 q1 T2 q2) qf gs
| t_app:
  has_type G p f (.TFun T1 q1 T2 q2) qf gs →
  has_type G p t T1 qx gs →
  qapp G p qf qx q1 gs →
  q2 ⊆ p ∪ {✦, #0, #1} →
  (✦ ∈ qf → occurs .noneq T2 #0) →
  (✦ ∈ qx → occurs .noneq T2 #1) →
  has_type G p (.tapp f t) ([#0 ↦ qf] [#1 ↦ qx] T2) ([#0 ↦ qf] [#1 ↦ qx] q2) gs
| t_tapp:
  has_type G p f (.TAll T1 q1 T2 q2) qf gs →
  stp G Tx {✦} T1 {✦} gs →
  closed_ty 0 ‖G‖ Tx →
  closed_ty 0 ‖G‖ T1 →
  closed_ql true 0 ‖G‖ qx →
  qapp G p qf qx q1 gs →
  q2 ⊆ p ∪ {✦, #0, #1} →
  qx ⊆ p ∪ {✦} →
  (✦ ∈ qf → occurs .noneq T2 #0) →
  (✦ ∈ qx → occurs .noneq T2 #1) →
  has_type G p (.ttapp f Tx qx) ([#0 ↦ qf] [#1 ↦ (Tx, qx)] T2) ([#0 ↦ qf] [#1 ↦ qx] q2) gs
| t_sub:
  has_type G p t T1 q1 gs →
  stp G T1 q1 T2 q2 gs →
  closed_ty 0 ‖G‖ T2 →
  q2 ⊆ p ∪ {✦} →
  has_type G p t T2 q2 gs
| t_asc:
  has_type G p t T q gs →
  has_type G p (.tanno t T q) T q gs

-- closedness invariants

lemma qtp_closed:
  qtp G q1 q2 gs →
  closed_ql true 0 ‖G‖ q1 ∧ closed_ql true 0 ‖G‖ q2 :=
by
  intro h; induction h with
  | q_sub => split_ands'; tauto
  | q_cong => split_ands; simp [sets]; tauto; simp [sets]; tauto
  | q_var h _ =>
    split_ands; simp [sets]; apply List.getElem?_eq_some'; assumption; c_extend;
  | q_self h _ =>
    split_ands; simp [closed_ql]; trans; swap; assumption; simp; simp [sets]
    apply List.getElem?_eq_some'; assumption
  | q_trans => split_ands''

lemma stp_implies_qtp:
  closed_ql true 0 ‖G‖ q1 →
  stp G T1 q1 T2 q2 gs →
  qtp G q1 q2 gs :=
by
  intro C S; induction S
  case s_refl => assumption
  case s_trans IH1 IH2 =>
    specialize IH1 C; have C' := (qtp_closed IH1).2; specialize IH2 C'
    apply qtp.q_trans; assumption'
  case s_top => apply qtp.q_sub; simp; assumption
  case s_ref => apply qtp.q_sub; simp; assumption
  case s_pair => apply qtp.q_sub; simp; assumption
  case s_list => apply qtp.q_sub; simp; assumption
  case s_fun => apply qtp.q_sub; simp; assumption
  case s_tvar => apply qtp.q_sub; simp; assumption
  case s_all => apply qtp.q_sub; simp; assumption

lemma hast_closed:
  has_type G p t T q gs →
  q ⊆ p ∪ {✦} ∧ closed_ty 0 ‖G‖ T ∧ closed_ql true 0 ‖G‖ q :=
by
  intro H; induction H
  case t_unit => simp [closed_ql]; constructor
  case t_nat => simp [closed_ql]; constructor
  case t_add => simp [closed_ql]; constructor
  case t_mul => simp [closed_ql]; constructor
  case t_var h _ _ _ =>
    have := List.getElem?_eq_some' h
    split_ands; simpa; assumption; simpa [sets]
  case t_ref IH =>
    simp [closed_ql]; simp!; split_ands''
    c_extend; apply closedql_fr_tighten; assumption; c_extend; c_free; c_free; c_free;
  case t_get G p t T1 q1 T2 q2 q gs H1 H2 _ IH =>
    simp [closed_ty] at IH; split_ands''; rename q ⊆ p ∪ {✦} => H3
    intro a; specialize @H2 a; specialize @H3 a; simp [subst, sets] at H2 H3 ⊢
    clear *- H2 H3; tauto
    simp; rw [ty.subst_freefr]; assumption'; c_subst; assumption; split; simp
    apply closedql_fr_tighten; assumption'; c_subst; c_extend; assumption
  case t_pair IH =>
    simp [closed_ql]; simp!; split_ands'' <;> rename_i Cq1 _ Cq2
    apply Finset.union_subset; assumption'; c_extend; c_extend;
    c_subst; c_extend; c_subst; c_extend; c_free; c_free;
    apply Finset.union_subset; assumption'
  case t_fst G p t T1 q1 T2 q2 q gs H1 H2 _ IH =>
    simp [closed_ty] at IH; split_ands''; rename q ⊆ p ∪ {✦} => H3
    intro a; specialize @H2 a; specialize @H3 a; simp [subst, sets] at H2 H3 ⊢
    clear *- H2 H3; tauto
    simp; rw [ty.subst_freefr]; assumption'; c_subst; assumption; split; simp
    apply closedql_fr_tighten; assumption'; c_subst; c_extend; assumption
  case t_snd G p t T1 q1 T2 q2 q gs H1 H2 _ IH =>
    simp [closed_ty] at IH; split_ands''; rename q ⊆ p ∪ {✦} => H3
    intro a; specialize @H2 a; specialize @H3 a; simp [subst, sets] at H2 H3 ⊢
    clear *- H2 H3; tauto
    simp; rw [ty.subst_freefr]; assumption'; c_subst; assumption; split; simp
    apply closedql_fr_tighten; assumption'; c_subst; c_extend; assumption
  case t_put IH1 IH2 =>
    simp [sets]; constructor
  case t_nil => simpa
  case t_cons IH1 IH2 =>
    split_ands''; apply Finset.union_subset; assumption'
    apply Finset.union_subset; assumption'
  case t_fold IH1 IH2 => assumption
  case t_abs =>
    split_ands; trans; assumption; simp; simp!; split_ands'; c_extend;
  case t_absa => split_ands''
  case t_tabs =>
    split_ands; trans; assumption; simp; simp!; split_ands'; c_extend;
  case t_tabsa => split_ands''
  case t_app G _ _ T1 q1 T2 q2 qf _ _ qx _ _ _ Q2 Dqf Dqx IH1 IH2 =>
    obtain ⟨IH1a, IH1b, IH1c⟩ := IH1; obtain ⟨IH2a, IH2b, IH2c⟩ := IH2
    simp! at IH1b; split_ands''
    · clear *- Q2 IH1a IH2a; intro x; simp [sets, subst] at *
      specialize @Q2 x; specialize @IH1a x; specialize @IH2a x; tauto
    · simp; rw [ty.subst_freefr Dqx, ty.subst_freefr]; swap
      rw [occurs_subst]; simpa; simp; intros; c_free; simp!
      c_subst; assumption; split; simp; apply closedql_fr_tighten; assumption'
      split; simp; apply closedql_fr_tighten; assumption'
    · c_subst; assumption'; c_extend;
  case t_tapp G _ _ T1 q1 T2 q2 qf _ _ qx _ S1 _ _ _ Q2 QX Dqf Dqx IH2 =>
    obtain ⟨IH2a, IH2b, IH2c⟩ := IH2; simp! at IH2b; split_ands''
    · clear * - Q2 IH2a QX; intro x; simp [sets, subst] at *
      specialize @Q2 x; specialize @QX x; specialize @IH2a x; tauto
    · simp; rw [ty.subst_freefr Dqx, ty.subst_freefr]; swap
      rw [occurs_subst]; simpa; simp; intros; c_free; c_free;
      c_subst; assumption
      split_ands'; split; simp; apply closedql_fr_tighten; assumption'
      split; simp; apply closedql_fr_tighten; assumption'
    · c_subst; assumption'; c_extend;
  case t_sub S _ _ IH =>
    split_ands'; apply stp_implies_qtp at S
    apply (qtp_closed S).2; simp [IH]
  case t_asc => assumption

-- auxiliary rules

namespace qtp

lemma q_subst (C: closed_ql true 0 ‖G‖ q):
  qtp G {x} y gs →
  qtp G q ([x ↦ y] q) gs :=
by
  intro h; nth_rw 1 [←ql.subst_self x q]; simp [subst]
  apply q_cong
  · apply q_sub; simp; simp [closed_ql]; trans q; simp; assumption
  · split; apply h; apply q_sub; simp; simp [sets]

lemma q_cong':
  qtp G q1 q gs →
  qtp G q2 q gs →
  qtp G (q1 ∪ q2) q gs :=
by
  intros; rw [←Finset.union_self q]; apply q_cong; assumption'

lemma q_self':
  G[f]? = some (T, qf, .self) →
  q1 ⊆ qf \ {✦} →
  %f ∈ q2 →
  closed_ql true 0 ‖G‖ qf →
  closed_ql true 0 ‖G‖ q2 →
  qtp G q1 q2 gs :=
by
  intros; apply q_trans (q2 := {%f}); apply q_trans; swap
  apply q_self; assumption'
  apply q_sub; assumption; simp [closed_ql]; trans qf; simp; assumption
  apply q_sub; simpa; assumption

lemma gs_tighten:
  qtp G q1 q2 gs' →
  gs ⊆ gs' →
  qtp G q1 q2 gs :=
by
  intros H1 H2; induction H1 generalizing gs
  case q_sub => apply q_sub; assumption'
  case q_cong => apply q_cong; tauto; tauto
  case q_var => apply q_var; assumption'; tauto
  case q_self => apply q_self; assumption'
  case q_trans => apply q_trans; tauto; tauto

end qtp

namespace stp

lemma gs_tighten:
  stp G T1 q0 T2 q1 gs' →
  gs ⊆ gs' →
  stp G T1 q0 T2 q1 gs :=
by
  intros H1 H2; induction H1 generalizing gs
  case s_refl => apply s_refl; apply qtp.gs_tighten; assumption'
  case s_trans => apply s_trans; assumption; tauto; tauto
  case s_top => apply s_top
  case s_ref =>
    apply s_ref; tauto; tauto
    apply qtp.gs_tighten; assumption'; apply qtp.gs_tighten; assumption'
  case s_pair =>
    apply s_pair; tauto; tauto
    apply qtp.gs_tighten; assumption'; apply qtp.gs_tighten; assumption'
  case s_list =>
    apply s_list; tauto; assumption
  case s_fun ih1 ih2 =>
    apply s_fun; assumption'; apply ih1; assumption
    rename _ ∨ _ => h; obtain h | h := h; simp [h]; right
    apply qtp.gs_tighten; assumption'
    apply ih2; assumption; apply qtp.gs_tighten; assumption'
  case s_tvar =>
    apply s_tvar; assumption'
  case s_all ih1 ih2 =>
    apply s_all; assumption'; apply ih1; assumption
    rename _ ∨ _ => h; obtain h | h := h; simp [h]; right
    apply qtp.gs_tighten; assumption'
    apply ih2; assumption; apply qtp.gs_tighten; assumption'

end stp

namespace has_type

lemma t_abs':
  has_type (G++[(.TTop, qf, .self), ([#0 ↦ %‖G‖] T1, [#0 ↦ %‖G‖] q1, .var)])
    (qf ∪ {%‖G‖, %(‖G‖ + 1)}) t T2 q2 gs →
  closed_ty 1 ‖G‖ T1 →
  closed_ql true 1 ‖G‖ q1 →
  closed_ql false 0 ‖G‖ qf →
  q1 ⊆ qf ∪ {✦, #0} →
  (#0 ∈ q1 → ✦ ∈ q1) →
  occurs .no_covariant T1 #0 →
  occurs .no_contravariant T2 %‖G‖ →
  qf ⊆ p →
  has_type G p (.tabs none t) (.TFun' ‖G‖ T1 q1 T2 q2) qf gs :=
by
  intros h; intros; have ⟨_, _, _⟩ := hast_closed h
  simp at *; apply t_abs; assumption'
  · simp; rwa [ty.open_cancel, ql.subst_cancel, ty.open_cancel, ql.subst_cancel]
    c_free; c_free; simp [subst]; c_free; simp; c_free;
  · rw [ty.open_comm]; c_subst; c_extend; simp; simp; simp
  · rw [ql.subst_comm]; c_subst; c_extend; simp; simp; simp
  · simp; split_ands'; c_free;

lemma t_tabs':
  has_type (G++[(.TTop, qf, .self), ([#0 ↦ %‖G‖] T1, [#0 ↦ %‖G‖] q1, .tvar)])
    (qf ∪ {%‖G‖, %(‖G‖ + 1)}) t T2 q2 gs →
  closed_ty 1 ‖G‖ T1 →
  closed_ql true 1 ‖G‖ q1 →
  closed_ql false 0 ‖G‖ qf →
  q1 ⊆ qf ∪ {✦, #0} →
  (#0 ∈ q1 → ✦ ∈ q1) →
  occurs .no_covariant T1 #0 →
  occurs .no_contravariant T2 %‖G‖ →
  qf ⊆ p →
  has_type G p (.ttabs none t) (.TAll' ‖G‖ T1 q1 T2 q2) qf gs :=
by
  intros h; intros; have ⟨_, _, _⟩ := hast_closed h
  simp at *; apply t_tabs; assumption'
  · simp; rwa [ty.open_cancel, ql.subst_cancel, ty.open_cancel, ql.subst_cancel]
    c_free; c_free; simp [subst]; c_free; simp; c_free;
  · rw [ty.open_comm]; c_subst; c_extend; simp; simp; simp
  · rw [ql.subst_comm]; c_subst; c_extend; simp; simp; simp
  · simp; split_ands'; c_free;

lemma gs_tighten:
  has_type G p t T q gs' →
  gs ⊆ gs' →
  has_type G p t T q gs :=
by
  intros H H1; induction H generalizing gs
  case t_unit => apply t_unit
  case t_nat => apply t_nat
  case t_add => aesop (add safe t_add)
  case t_mul => aesop (add safe t_mul)
  case t_var => eapply t_var; assumption'
  case t_ref IH => apply t_ref; apply IH; assumption'
  case t_get IH => apply t_get; apply IH; assumption'
  case t_put IH1 IH2 => eapply t_put; apply IH1; swap; apply IH2; assumption'
  case t_pair => apply t_pair; aesop; aesop
  case t_fst => apply t_fst; aesop; assumption'
  case t_snd => apply t_snd; aesop; assumption'
  case t_nil => apply t_nil; assumption
  case t_cons => apply t_cons; aesop; aesop
  case t_fold => apply t_fold; aesop; aesop; aesop; assumption'
  case t_abs IH => eapply t_abs; apply IH; assumption'
  case t_absa IH => eapply t_absa; apply IH; assumption
  case t_tabs IH => eapply t_tabs; apply IH; assumption'
  case t_tabsa IH => eapply t_tabsa; apply IH; assumption
  case t_app IH1 IH2 =>
    eapply t_app; apply IH1; swap; apply IH2; assumption'; dsimp [qapp]
    rename _ ∨ _ ∨ _ => H; obtain H | H | H := H <;> try simp [H]
    replace H := H.gs_tighten H1; simp [H]
    right; right; obtain ⟨-, H2, -, H⟩ := H; replace H2 := H2.gs_tighten H1
    simp [H2]; clear *- H1 H; intro _ h; apply H; tauto
  case t_tapp IH1 IH2 =>
    eapply t_tapp; apply IH2; assumption'
    apply stp.gs_tighten; assumption'; dsimp [qapp]
    rename _ ∨ _ ∨ _ => H; obtain H | H | H := H <;> try simp [H]
    replace H := H.gs_tighten H1; simp [H]
    right; right; obtain ⟨-, H2, -, H⟩ := H; replace H2 := H2.gs_tighten H1
    simp [H2]; clear *- H1 H; intro _ h; apply H; tauto
  case t_sub IH =>
    eapply t_sub; apply IH; assumption'
    apply stp.gs_tighten; assumption'
  case t_asc IH => eapply t_asc; apply IH; assumption'

lemma filter_widen:
  has_type G p t T q gs →
  p ⊆ p' →
  has_type G p' t T q gs :=
by
  intro h P; induction h generalizing p'
  case t_unit => apply t_unit
  case t_nat => apply t_nat
  case t_add => apply t_add; aesop; aesop
  case t_mul => apply t_mul; aesop; aesop
  case t_var => apply t_var; assumption'; tauto
  case t_ref IH => apply t_ref; apply IH; assumption; tauto
  case t_get IH => apply t_get; apply IH; assumption'; trans; assumption; gcongr
  case t_put IH1 IH2 => eapply t_put; apply IH1; swap; apply IH2; assumption'
  case t_pair => apply t_pair; aesop; aesop
  case t_fst => apply t_fst; aesop; trans; assumption'; gcongr
  case t_snd => apply t_snd; aesop; trans; assumption'; gcongr
  case t_nil => apply t_nil; assumption
  case t_cons => apply t_cons; aesop; aesop
  case t_fold ih3 => apply t_fold; aesop; aesop; apply ih3; gcongr; assumption'
  case t_abs IH1 => eapply t_abs; assumption'; tauto
  case t_absa IH1 => eapply t_absa; tauto
  case t_tabs IH1 => eapply t_tabs; assumption'; tauto
  case t_tabsa IH1 => eapply t_tabsa; tauto
  case t_app IH1 IH2 =>
    eapply t_app; apply IH1; assumption; apply IH2; assumption'; dsimp [qapp]
    rename _ ∨ _ ∨ _ => H; obtain H | H | H := H <;> simp [H]
    right; right; split_ands''; all_goals trans; assumption; gcongr
  case t_tapp IH1 IH2 =>
    eapply t_tapp; apply IH2; assumption'; dsimp [qapp]
    rename _ ∨ _ ∨ _ => H; obtain H | H | H := H <;> simp [H]
    right; right; split_ands''; all_goals trans; assumption; gcongr
  case t_sub IH => eapply t_sub; apply IH; assumption'; trans; assumption; gcongr
  case t_asc IH => eapply t_asc; apply IH; assumption

end has_type

-- context growth

namespace ctx_grow

open qtp

lemma on_qtp:
  ctx_grow G G' gs →
  qtp G q1 q2 gs →
  qtp G' q1 q2 gs :=
by
  intros CG Q0; induction Q0 generalizing G'
  case q_sub =>
    apply q_sub; assumption; rwa [←CG.1]
  case q_cong =>
    apply q_cong; tauto; tauto
  case q_var G x Tx qx _ _ H1 _ H2 =>
    apply q_var; obtain (H | ⟨_, _, _, _, -, -, H, -⟩) := CG.2 x; rwa [←H]
    contradiction; assumption; rwa [←CG.1]
  case q_self G x Tx qx _ H1 H2 =>
    have := CG.1; have := List.getElem?_eq_some' H1
    obtain (H | ⟨-, _, _, qx', H, Cqx, H1', H1''⟩) := CG.2 x; apply q_self; rwa [←H]; rwa [←CG.1]
    rw [H1] at H1'; simp at H1'; rcases H1' with ⟨rfl, rfl⟩; apply q_trans; swap
    apply q_self H1''; simp [closed_ql]; trans; apply Cqx; simp; omega
    apply q_sub; simp [sets]; clear * - H; tauto; simp [closed_ql]; trans; trans; swap; exact Cqx
    simp; simp; omega
  case q_trans IH1 IH2 =>
    apply q_trans; apply IH1 CG; apply IH2 CG

open stp

lemma on_stp:
  ctx_grow G G' gs →
  stp G T1 q0 gr T2 gs →
  stp G' T1 q0 gr T2 gs :=
by
  intros CG S0; induction S0 generalizing G'
  case s_refl =>
    apply s_refl; apply CG.on_qtp; assumption
  case s_trans IH1 IH2 =>
    apply s_trans; rwa [←CG.1]; apply IH1 CG; apply IH2 CG
  case s_top =>
    apply s_top
  case s_ref G q0 _ _ _ _ _ _ _ _ _ _ _ _ _ Q1 Q2 G1 G2 IH1 IH2 =>
    simp only [CG.1] at Q2 G1 G2 IH1 IH2
    replace CG := CG.append (g := [(.TTop, q0, .self)])
    apply s_ref; tauto; tauto
    apply CG.on_qtp; assumption; apply CG.on_qtp; assumption'
  case s_pair G q0 _ _ _ _ _ _ _ _ _ _ _ _ _ Q1 Q2 G1 G2 IH1 IH2 =>
    simp only [CG.1] at Q1 Q2 G1 G2 IH1 IH2
    replace CG := CG.append (g := [(.TTop, q0, .self)])
    apply s_pair; tauto; tauto
    apply CG.on_qtp; assumption; apply CG.on_qtp; assumption'
  case s_list G q0 _ _ _ _ S1 G1 IH =>
    simp only [CG.1] at S1 G1 IH
    replace CG := CG.append (g := [(.TTop, q0, .self)])
    apply s_list; tauto; tauto
  case s_fun IH1 IH2 =>
    simp only [CG.1] at *; eapply s_fun; assumption'
    apply IH1; apply CG.append
    rename _ ∨ _ => h; obtain h | h := h; simp [h]; right
    apply on_qtp; swap; assumption; apply CG.append
    apply IH2; apply CG.append
    apply on_qtp; swap; assumption; apply CG.append
  case s_tvar x _ _ _ _ h =>
    apply s_tvar; obtain h1 | h1 := CG.2 x; rwa [←h1]; simp [h] at h1
  case s_all IH1 IH2 =>
    simp only [CG.1] at *; eapply s_all; assumption'
    apply IH1; apply CG.append
    rename _ ∨ _ => h; obtain h | h := h; simp [h]; right
    apply on_qtp; swap; assumption; apply CG.append
    apply IH2; apply CG.append
    apply on_qtp; swap; assumption; apply CG.append

lemma on_vars_trans:
  ctx_grow G G' gs →
  (∀i ∈ gs, %i ∉ vars_trans G q) →
  vars_trans G q = vars_trans G' q :=
by
  intros H1 H2; induction H1 using ctx_grow.induct generalizing q
  next => simp
  next G a G' a' H1 IH =>
    simp [vars_trans] at H2 ⊢; simp [←vars_trans.eq_1] at H2 ⊢
    have H1' := H1.shrink (by simp); simp [←H1'.1]; replace IH := @IH H1'
    congrm ?_ ∪ ?_; apply IH; intros _ h; exact (H2 _ h).1
    split; rename_i h; simp [h] at H2
    have: ‖G‖ ∉ gs := by
      contrapose! h; replace H2 := (H2 _ h).1; contrapose! H2; apply vt_closing H2
    have AA := H1.2 ‖G‖; simp [this] at AA; simp [H1'.1] at AA; subst a'
    apply IH; intros _ h; exact (H2 _ h).2; rfl

open has_type

lemma on_hastype:
  ctx_grow G G' gs →
  has_type G p t T q gs →
  has_type G' p t T q gs :=
by
  intros CG H1; induction H1 generalizing G'
  case t_unit => apply t_unit
  case t_nat => apply t_nat
  case t_add => apply t_add; aesop; aesop
  case t_mul => apply t_mul; aesop; aesop
  case t_var G x _ _ _ _ _ H _ _ _ =>
    simp [CG.1] at *; obtain HG | HG := CG.2 x
    eapply t_var; assumption'; rwa [←HG]
    obtain ⟨-, T, q, q', -, -, H', H1⟩ := HG
    simp [H] at H'; obtain ⟨rfl, rfl, rfl⟩ := H'
    eapply t_var; assumption'
  case t_get IH => apply t_get; apply IH; assumption'
  case t_put IH1 IH2 => apply t_put; apply IH1; assumption; apply IH2; assumption
  case t_ref IH => apply t_ref; apply IH; assumption'
  case t_pair => apply t_pair; aesop; aesop
  case t_fst => apply t_fst; aesop; assumption'
  case t_snd => apply t_snd; aesop; assumption'
  case t_nil => apply t_nil; rwa [←CG.1]
  case t_cons => apply t_cons; aesop; aesop
  case t_fold ih3 =>
    apply t_fold; aesop; aesop; rw [CG.1] at ih3
    apply ih3; apply CG.append; rwa [←CG.1]; assumption'
  case t_abs IH =>
    simp [CG.1] at *; eapply t_abs; assumption'; apply IH
    apply ctx_grow.append; assumption
  case t_absa IH =>
    simp at *; eapply t_absa; tauto
  case t_app IH1 IH2 =>
    rename _ ∨ _ ∨ _ => H
    eapply t_app; assumption'
    apply IH1; assumption; apply IH2; assumption
    dsimp [qapp]; obtain H | H | H := H; simp [H]
    · right; left; apply CG.on_qtp H
    · right; right; simp [H]
      have qfi := fun a h => (H.2.2.2 a h).1
      have qxi := fun a h => (H.2.2.2 a h).2
      simp only [←CG.on_vars_trans qfi, ←CG.on_vars_trans qxi]
      split_ands''; apply CG.on_qtp; assumption
  case t_tabs IH =>
    simp [CG.1] at *; eapply t_tabs; assumption'; apply IH
    apply ctx_grow.append; assumption
  case t_tabsa IH =>
    simp at *; eapply t_tabsa; tauto
  case t_tapp IH1 IH2 =>
    rename _ ∨ _ ∨ _ => H
    eapply t_tapp; assumption'
    apply IH2; assumption; apply CG.on_stp; assumption
    rwa [←CG.1]; rwa [←CG.1]; rwa [←CG.1]
    dsimp [qapp]; obtain H | H | H := H; simp [H]
    · right; left; apply CG.on_qtp H
    · right; right; simp [H]
      have qfi := fun a h => (H.2.2.2 a h).1
      have qxi := fun a h => (H.2.2.2 a h).2
      simp only [←CG.on_vars_trans qfi, ←CG.on_vars_trans qxi]
      split_ands''; apply CG.on_qtp; assumption
  case t_sub IH =>
    eapply t_sub; assumption'; apply IH; assumption
    apply CG.on_stp; assumption; rwa [←CG.1]
  case t_asc IH =>
    eapply t_asc; apply IH; assumption

end ctx_grow

-- equivalence rules

open qtp

lemma ql.self_subst_equiv (hf: G[f]? = some (Tf, qf, .self))
  (Cqf: closed_ql false 0 ‖G‖ qf) (C: closed_ql true 0 ‖G‖ q) (hgs: f ∉ gs):
  qtp G q ([%f ↦ qf] q) gs ∧ qtp G ([%f ↦ qf] q) q gs :=
by
  simp [subst]; split; swap
  next h =>
    simp [h, Finset.sdiff_singleton_eq_erase]; apply q_sub; simp; assumption
  next h =>
    have: qtp G (q \ {%f}) (q \ {%f}) gs := by
      apply q_sub; simp; simp [closed_ql]; trans q; simp; assumption
    have: q = q \ {%f} ∪ {%f} := (by simp [h]); split_ands
    · nth_rw 1 [this]; apply q_cong; assumption; apply q_var; assumption'
    · nth_rw 2 [this]; apply q_cong; assumption
      have: qf = qf \ {✦} := by ext; simp; rintro h rfl; absurd h; c_free;
      rw [this]; apply q_self; assumption'; c_extend;

open stp

lemma ty.self_subst_equiv (hf: G[f]? = some (Tf, qf, .self)) (hgs: f ∉ gs)
  (Cq0: closed_ql true 0 ‖G‖ q0) (Cqf: closed_ql false 0 ‖G‖ qf) (C: closed_ty 0 ‖G‖ T)
  (hocc: occurs .no_contravariant T %f ∨ occurs .no_covariant T %f):
  stp G T q0 ([%f ↦ qf] T) q0 gs ∧ stp G ([%f ↦ qf] T) q0 T q0 gs :=
by
  induction T using ty.induct' generalizing G q0
  case TTop => simp; apply s_refl; apply q_sub; simp; assumption
  case TUnit => simp; apply s_refl; apply q_sub; simp; assumption
  case TNat => simp; apply s_refl; apply q_sub; simp; assumption
  case TRef2 T1 q1 T2 q2 ih1 ih2 => -- TRef
    simp! at hocc; have L := List.getElem?_eq_some' hf
    have L1: f ≠ ‖G‖ := (by omega); have L2: f ≠ ‖G‖ + 1 := (by omega);
    -- T1
    let T1' := [#0 ↦ %‖G‖] T1
    replace ih1 := fun a => @ih1 T1' (by simp [T1']) (G++[a]) {✦}
      (by simpa [L]) (by simp [sets]) (by c_extend)
      (by c_subst; c_extend C.1) (by clear *- hocc L1; aesop)
    have HT1: [%f↦qf] T1' = [#0↦%‖G‖] [%f↦qf] T1 := by
      simp; rw [ty.open_subst_comm]; simp; omega; intro; c_free; simp!; simp
    rw [HT1] at ih1; simp only [instSubstTyQl, T1'] at ih1; clear HT1 T1'
    -- T2
    let T2' := [#0 ↦ %‖G‖] T2
    replace ih2 := fun a => @ih2 T2' (by simp [T2']) (G++[a]) {✦}
      (by simpa [L]) (by simp [sets]) (by c_extend)
      (by c_subst; c_extend C.2.1) (by clear *- hocc L1; aesop)
    have HT2: [%f↦qf] T2' = [#0↦%‖G‖] [%f↦qf] T2 := by
      simp; rw [ty.open_subst_comm]; simp; omega; intro; c_free; simp!; simp
    rw [HT2] at ih2; simp only [instSubstTyQl, T2'] at ih2; clear HT2 T2'
    -- q1
    have h1 := fun a => @ql.self_subst_equiv (G++[a]) f Tf qf q1 _ (by simpa [L])
      (by c_extend) (by obtain ⟨-, -, _, -, _, -⟩ := C; apply closedql_bv_tighten;
                        assumption; c_extend) hgs
    -- q2
    let q2' := [#0 ↦ %‖G‖] q2
    have h2 := fun a => @ql.self_subst_equiv (G++[a]) f Tf qf q2' _ (by simpa [L])
      (by c_extend) (by simp [q2']; c_subst; c_extend C.2.2.2.1) hgs
    have HQ2: [%f ↦ qf] q2' = [#0 ↦ %‖G‖] [%f ↦ qf] q2 := by
      simp [q2']; rw [ql.subst_comm (x1 := %f)]; c_free; simp; omega; simp
    rw [HQ2] at h2; simp only [instSubstQlId, q2'] at h2; clear HQ2 q2'
    -- final
    clear L L1 L2 hocc; simp; split_ands
    · apply s_ref (gr1 := ∅) (gr2 := ∅); rotate_left 4
      simp; simp; simp; apply (ih1 _).2; simp; apply (ih2 _).1
      simp; apply (h1 _).2; simp; apply (h2 _).1
    · apply s_ref (gr1 := ∅) (gr2 := ∅); rotate_left 4
      simp; simp; simp; apply (ih1 _).1; simp; apply (ih2 _).2
      simp; apply (h1 _).1; simp; apply (h2 _).2
  case TFun T1 q1 T2 q2 ih1 ih2 => -- TFun
    simp! at hocc; have L := List.getElem?_eq_some' hf
    have L1: f ≠ ‖G‖ := (by omega); have L2: f ≠ ‖G‖ + 1 := (by omega);
    -- T1
    let T1' := [#0 ↦ %‖G‖] T1
    replace ih1 := fun a => @ih1 T1' (by simp [T1']) (G++[a]) {✦}
      (by simpa [L]) (by simp [sets]) (by c_extend)
      (by c_subst; c_extend C.1) (by clear *- hocc L1; aesop)
    have HT1: [%f↦qf] T1' = [#0↦%‖G‖] [%f↦qf] T1 := by
      simp; rw [ty.open_subst_comm]; simp; omega; intro; c_free; simp!; simp
    rw [HT1] at ih1; simp only [instSubstTyQl, T1'] at ih1; clear HT1 T1'
    -- T2
    let T2' := [#0 ↦ %‖G‖] [#1 ↦ %(‖G‖ + 1)] T2
    replace ih2 := fun a b => @ih2 T2' (by simp [T2']) (G++[a,b]) {✦}
      (by simpa [L]) (by simp [sets]) (by c_extend)
      (by c_subst; c_extend C.2.1) (by clear *- hocc L1 L2; aesop)
    have HT2: [%f↦qf] T2' = [#0↦%‖G‖] [#1 ↦ %(‖G‖+1)] [%f↦qf] T2 := by
      simp; rw [ty.open_subst_comm, ty.open_subst_comm]
      simp; omega; intro; c_free; simp!; simp; simp; omega; intro; c_free; simp!; simp
    rw [HT2] at ih2; simp only [instSubstTyQl, T2'] at ih2; clear HT2 T2'
    -- q1
    let q1' := [#0 ↦ %‖G‖] q1
    have h1 := fun a => @ql.self_subst_equiv (G++[a]) f Tf qf q1' _ (by simpa [L])
      (by c_extend) (by simp [q1']; c_subst; c_extend C.2.2.1) hgs
    have HQ1: [%f ↦ qf] q1' = [#0 ↦ %‖G‖] [%f ↦ qf] q1 := by
      simp [q1']; rw [ql.subst_comm]; c_free; simp; omega; simp
    rw [HQ1] at h1; simp only [instSubstQlId, q1'] at h1; clear HQ1 q1'
    -- q2
    let q2' := [#0 ↦ %‖G‖] [#1 ↦ %(‖G‖+1)] q2
    have h2 := fun a b => @ql.self_subst_equiv (G++[a,b]) f Tf qf q2' gs (by simpa [L])
      (by c_extend) (by simp [q2']; c_subst; c_extend C.2.2.2.1) (by assumption)
    have HQ2: [%f ↦ qf] q2' = [#0 ↦ %‖G‖] [#1 ↦ %(‖G‖+1)] [%f ↦ qf] q2 := by
      simp [q2']; rw [ql.subst_comm (x1 := %f), ql.subst_comm (x1 := %f)]
      c_free; simp; omega; simp; c_free; simp; omega; simp
    rw [HQ2] at h2; simp only [instSubstQlId, q2'] at h2; clear HQ2 q2'
    -- final
    clear L L1 L2 hocc; simp; split_ands
    · apply s_fun (gr1 := ∅) (gr2 := ∅); rotate_left 4
      simp; simp; simp; apply (ih1 _).2; right; simp; apply (h1 _).2
      simp; apply (ih2 _ _).1; simp; apply (h2 _ _).1
    · apply s_fun (gr1 := ∅) (gr2 := ∅); rotate_left 4
      simp; simp; simp; apply (ih1 _).1; right; simp; apply (h1 _).1
      simp; apply (ih2 _ _).2; simp; apply (h2 _ _).2
  case TVar =>  -- TVar
    simp! at hocc; simp [hocc]; apply s_refl; apply q_sub; simp; assumption
  case TAll T1 q1 T2 q2 ih1 ih2 => -- TAll
    simp! at hocc; have L := List.getElem?_eq_some' hf
    have L1: f ≠ ‖G‖ := (by omega); have L2: f ≠ ‖G‖ + 1 := (by omega);
    -- T1
    let T1' := [#0 ↦ %‖G‖] T1
    replace ih1 := fun a => @ih1 T1' (by simp [T1']) (G++[a]) {✦}
      (by simpa [L]) (by simp [sets]) (by c_extend)
      (by c_subst; c_extend C.1) (by clear *- hocc L1; aesop)
    have HT1: [%f↦qf] T1' = [#0↦%‖G‖] [%f↦qf] T1 := by
      simp; rw [ty.open_subst_comm]; simp; omega; intro; c_free; simp!; simp
    rw [HT1] at ih1; simp only [instSubstTyQl, T1'] at ih1; clear HT1 T1'
    -- T2
    let T2' := [#0 ↦ %‖G‖] [#1 ↦ %(‖G‖ + 1)] T2
    replace ih2 := fun a b => @ih2 T2' (by simp [T2']) (G++[a,b]) {✦}
      (by simpa [L]) (by simp [sets]) (by c_extend)
      (by c_subst; c_extend C.2.1) (by clear *- hocc L1 L2; aesop)
    have HT2: [%f↦qf] T2' = [#0↦%‖G‖] [#1 ↦ %(‖G‖+1)] [%f↦qf] T2 := by
      simp; rw [ty.open_subst_comm, ty.open_subst_comm]
      simp; omega; intro; c_free; simp!; simp; simp; omega; intro; c_free; simp!; simp
    rw [HT2] at ih2; simp only [instSubstTyQl, T2'] at ih2; clear HT2 T2'
    -- q1
    let q1' := [#0 ↦ %‖G‖] q1
    have h1 := fun a => @ql.self_subst_equiv (G++[a]) f Tf qf q1' _ (by simpa [L])
      (by c_extend) (by simp [q1']; c_subst; c_extend C.2.2.1) hgs
    have HQ1: [%f ↦ qf] q1' = [#0 ↦ %‖G‖] [%f ↦ qf] q1 := by
      simp [q1']; rw [ql.subst_comm]; c_free; simp; omega; simp
    rw [HQ1] at h1; simp only [instSubstQlId, q1'] at h1; clear HQ1 q1'
    -- q2
    let q2' := [#0 ↦ %‖G‖] [#1 ↦ %(‖G‖+1)] q2
    have h2 := fun a b => @ql.self_subst_equiv (G++[a,b]) f Tf qf q2' _ (by simpa [L])
      (by c_extend) (by simp [q2']; c_subst; c_extend C.2.2.2.1) hgs
    have HQ2: [%f ↦ qf] q2' = [#0 ↦ %‖G‖] [#1 ↦ %(‖G‖+1)] [%f ↦ qf] q2 := by
      simp [q2']; rw [ql.subst_comm (x1 := %f), ql.subst_comm (x1 := %f)]
      c_free; simp; omega; simp; c_free; simp; omega; simp
    rw [HQ2] at h2; simp only [instSubstQlId, q2'] at h2; clear HQ2 q2'
    -- final
    clear L L1 L2 hocc; simp; split_ands
    · apply s_all (gr2 := ∅); rotate_left 4
      simp; apply (ih1 _).2; right; simp; apply (h1 _).2
      simp; apply (ih2 _ _).1; simp; apply (h2 _ _).1
    · apply s_all (gr2 := ∅); rotate_left 4
      simp; apply (ih1 _).1; right; simp; apply (h1 _).1
      simp; apply (ih2 _ _).2; simp; apply (h2 _ _).2
  case TProd T1 q1 T2 q2 ih1 ih2 => -- TProd
    simp! at hocc; have L := List.getElem?_eq_some' hf
    have L1: f ≠ ‖G‖ := (by omega); have L2: f ≠ ‖G‖ + 1 := (by omega);
    -- T1
    let T1' := [#0 ↦ %‖G‖] T1
    replace ih1 := fun a => @ih1 T1' (by simp [T1']) (G++[a]) {✦}
      (by simpa [L]) (by simp [sets]) (by c_extend)
      (by c_subst; c_extend C.1) (by clear *- hocc L1; aesop)
    have HT1: [%f↦qf] T1' = [#0↦%‖G‖] [%f↦qf] T1 := by
      simp; rw [ty.open_subst_comm]; simp; omega; intro; c_free; simp!; simp
    rw [HT1] at ih1; simp only [instSubstTyQl, T1'] at ih1; clear HT1 T1'
    -- T2
    let T2' := [#0 ↦ %‖G‖] T2
    replace ih2 := fun a => @ih2 T2' (by simp [T2']) (G++[a]) {✦}
      (by simpa [L]) (by simp [sets]) (by c_extend)
      (by c_subst; c_extend C.2.1) (by clear *- hocc L1; aesop)
    have HT2: [%f↦qf] T2' = [#0↦%‖G‖] [%f↦qf] T2 := by
      simp; rw [ty.open_subst_comm]; simp; omega; intro; c_free; simp!; simp
    rw [HT2] at ih2; simp only [instSubstTyQl, T2'] at ih2; clear HT2 T2'
    -- q1
    let q1' := [#0 ↦ %‖G‖] q1
    have h1 := fun a => @ql.self_subst_equiv (G++[a]) f Tf qf q1' _ (by simpa [L])
      (by c_extend) (by simp [q1']; c_subst; c_extend C.2.2.1) hgs
    have HQ2: [%f ↦ qf] q1' = [#0 ↦ %‖G‖] [%f ↦ qf] q1 := by
      simp [q1']; rw [ql.subst_comm (x1 := %f)]; c_free; simp; omega; simp
    rw [HQ2] at h1; simp only [instSubstQlId, q1'] at h1; clear HQ2 q1'
    -- q2
    let q2' := [#0 ↦ %‖G‖] q2
    have h2 := fun a => @ql.self_subst_equiv (G++[a]) f Tf qf q2' _ (by simpa [L])
      (by c_extend) (by simp [q2']; c_subst; c_extend C.2.2.2.1) hgs
    have HQ2: [%f ↦ qf] q2' = [#0 ↦ %‖G‖] [%f ↦ qf] q2 := by
      simp [q2']; rw [ql.subst_comm (x1 := %f)]; c_free; simp; omega; simp
    rw [HQ2] at h2; simp only [instSubstQlId, q2'] at h2; clear HQ2 q2'
    -- final
    clear L L1 L2 hocc; simp; split_ands
    · apply s_pair (gr1 := ∅) (gr2 := ∅); rotate_left 4
      simp; simp; simp; apply (ih1 _).1; simp; apply (ih2 _).1
      simp; apply (h1 _).1; simp; apply (h2 _).1
    · apply s_pair (gr1 := ∅) (gr2 := ∅); rotate_left 4
      simp; simp; simp; apply (ih1 _).2; simp; apply (ih2 _).2
      simp; apply (h1 _).2; simp; apply (h2 _).2
  case TList T1 ih1 => -- TList
    simp! at hocc; have L := List.getElem?_eq_some' hf
    have L1: f ≠ ‖G‖ := (by omega); have L2: f ≠ ‖G‖ + 1 := (by omega);
    -- T1
    let T1' := [#0 ↦ %‖G‖] T1
    replace ih1 := fun a => @ih1 T1' (by simp [T1']) (G++[a]) {✦}
      (by simpa [L]) (by simp [sets]) (by c_extend)
      (by c_subst; c_extend C.1) (by clear *- hocc L1; aesop)
    have HT1: [%f↦qf] T1' = [#0↦%‖G‖] [%f↦qf] T1 := by
      simp; rw [ty.open_subst_comm]; simp; omega; intro; c_free; simp!; simp
    rw [HT1] at ih1; simp only [instSubstTyQl, T1'] at ih1; clear HT1 T1'
    -- final
    clear L L1 L2 hocc; simp; split_ands
    · apply s_list (gr := ∅); swap; simp; simp; apply (ih1 _).1
    · apply s_list (gr := ∅); swap; simp; simp; apply (ih1 _).2
