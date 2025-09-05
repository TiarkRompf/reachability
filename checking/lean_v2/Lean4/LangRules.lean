import Lean4.LangLemmas

-- [-simp] is local; redefine them
attribute [-simp] Set.setOf_subset_setOf Set.subset_inter_iff Set.union_subset_iff
attribute [-simp] Finset.union_insert

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

inductive stp: tenv → ty → ql → ql → ty → gfset → Prop where
| s_refl:
  closed_ty 0 ‖G‖ T →
  stp G T q ∅ T gs
| s_trans:
  stp G T1 q0        g1 T2 gs →
  stp G T2 (q0 ∪ g1) g2 T3 gs →
  stp G T1 q0 (g1 ∪ g2) T3 gs
| s_top:
  closed_ty 0 ‖G‖ T →
  stp G T q0 ∅ .TTop gs
| s_ref:
  stp G T1 {✦} ∅ T2 gs →
  stp G T2 {✦} ∅ T1 gs →
  qtp G q1 q2 gs →
  qtp G q2 q1 gs →
  ✦ ∉ q1 → ✦ ∉ q2 →
  stp G (.TRef T1 q1) q0 ∅ (.TRef T2 q2) gs
| s_fun:
  stp (G ++ [(.TTop, qf0 ∪ grf, .self)])
    ([#0 ↦ %‖G‖] T1b) {✦} gr1 ([#0 ↦ %‖G‖] T1a) gs →
  {#0, ✦} ⊆ q1a ∨
  qtp (G ++ [(.TTop, qf0 ∪ grf, .self)])
    ([#0 ↦ %‖G‖] q1b ∪ gr1)   ([#0 ↦ %‖G‖] q1a) gs →
  stp (G ++ [(.TTop, qf0 ∪ grf, .self), ([#0 ↦ %‖G‖] T1b, [#0 ↦ %‖G‖] q1b, .var)])
    ([#0 ↦ %‖G‖] [#1 ↦ (%(‖G‖+1), gr1)] T2a) {✦} gr2 ([#0 ↦ %‖G‖] [#1 ↦ %(‖G‖+1)] T2b) gs →
  qtp (G ++ [(.TTop, qf0 ∪ grf, .self), ([#0 ↦ %‖G‖] T1b, [#0 ↦ %‖G‖] q1b, .var)])
    ([#0 ↦ %‖G‖] [#1 ↦ (%(‖G‖+1), gr1)] q2a ∪ gr2)   ([#0 ↦ %‖G‖] [#1 ↦ %(‖G‖+1)] q2b) gs →
  gr1 \ {%‖G‖} ⊆ grf → gr2 \ {%‖G‖, %(‖G‖+1)} ⊆ grf →
  closed_ql false 0 ‖G‖ grf →
  closed_ty 0 ‖G‖ (.TFun T1a q1a T2a q2a) →
  closed_ty 0 ‖G‖ (.TFun T1b q1b T2b q2b) →
  stp G (.TFun T1a q1a T2a q2a) qf0 grf (.TFun T1b q1b T2b q2b) gs
| s_tvar:
  G[x]? = some (Tx, qx, .tvar) →
  closed_ty 0 ‖G‖ Tx →
  stp G (.TVar (%x)) q0 ∅ Tx gs
| s_all:
  stp (G ++ [(.TTop, qf0 ∪ grf, .self)])
    ([#0 ↦ %‖G‖] T1b) {✦} ∅ ([#0 ↦ %‖G‖] T1a) gs →
  {#0, ✦} ⊆ q1a ∨
  qtp (G ++ [(.TTop, qf0 ∪ grf, .self)])
    ([#0 ↦ %‖G‖] q1b)       ([#0 ↦ %‖G‖] q1a) gs →
  stp (G ++ [(.TTop, qf0 ∪ grf, .self), ([#0 ↦ %‖G‖] T1b, [#0 ↦ %‖G‖] q1b, .tvar)])
    ([#0 ↦ %‖G‖] [#1 ↦ %(‖G‖+1)] T2a) {✦} gr2 ([#0 ↦ %‖G‖] [#1 ↦ %(‖G‖+1)] T2b) gs →
  qtp (G ++ [(.TTop, qf0 ∪ grf, .self), ([#0 ↦ %‖G‖] T1b, [#0 ↦ %‖G‖] q1b, .tvar)])
    ([#0 ↦ %‖G‖] [#1 ↦ %(‖G‖+1)] q2a ∪ gr2)   ([#0 ↦ %‖G‖] [#1 ↦ %(‖G‖+1)] q2b) gs →
  gr2 \ {%‖G‖, %(‖G‖+1)} ⊆ grf →
  closed_ql false 0 ‖G‖ grf →
  closed_ty 0 ‖G‖ (.TAll T1a q1a T2a q2a) →
  closed_ty 0 ‖G‖ (.TAll T1b q1b T2b q2b) →
  stp G (.TAll T1a q1a T2a q2a) qf0 grf (.TAll T1b q1b T2b q2b) gs

inductive has_type: tenv → ql → tm → ty → ql → gfset → Prop where
| t_true: has_type G p .ttrue .TBool ∅ gs
| t_false: has_type G p .tfalse .TBool ∅ gs
| t_var:
  G[x]? = some (T, q, bn) →
  bn ≠ .tvar →
  %x ∈ p →
  closed_ty 0 ‖G‖ T →
  has_type G p (.tvar x) T {%x} gs
| t_ref:
  has_type G p t T q gs →
  ✦ ∉ q →
  has_type G p (.tref t) (.TRef T q) {✦} gs
| t_get:
  has_type G p t (.TRef T q1) q gs →
  q1 ⊆ p → #0 ∉ q1 →
  has_type G p (.tget t) T q1 gs
| t_put:
  has_type G p t1 (.TRef T q1) q2 gs →
  has_type G p t2 T q1 gs →
  has_type G p (.tput t1 t2) .TBool ∅ gs
| t_abs:
  has_type (G++[(.TTop, qf, .self), ([#0 ↦ %‖G‖] T1, [#0 ↦ %‖G‖] q1, .var)]) (qf ∪ {%‖G‖, %(‖G‖ + 1)})
    t ([#0 ↦ %‖G‖] [#1 ↦ %(‖G‖+1)] T2) ([#0 ↦ %‖G‖] [#1 ↦ %(‖G‖+1)] q2) gs →
  q1 \ {✦, #0} ⊆ qf →
  closed_ty 1 ‖G‖ T1 →
  closed_ty 2 ‖G‖ T2 →
  closed_ql true 1 ‖G‖ q1 →
  closed_ql true 2 ‖G‖ q2 →
  closed_ql false 0 ‖G‖ qf →
  (#0 ∈ q1 → ✦ ∈ q1) →
  occurs .no_covariant T1 #0 →
  occurs .no_contravariant T2 #0 →
  qf ⊆ p →
  has_type G p (.tabs t) (.TFun T1 q1 T2 q2) qf gs
| t_absa:
  has_type G p (.tabs t) (.TFun T1 q1 T2 q2) qf gs →
  has_type G p (.tabsa T1 q1 t) (.TFun T1 q1 T2 q2) qf gs
| t_tabs:
  has_type (G++[(.TTop, qf, .self), ([#0 ↦ %‖G‖] T1, [#0 ↦ %‖G‖] q1, .tvar)]) (qf ∪ {%‖G‖, %(‖G‖ + 1)})
    t ([#0 ↦ %‖G‖] [#1 ↦ %(‖G‖+1)] T2) ([#0 ↦ %‖G‖] [#1 ↦ %(‖G‖+1)] q2) gs →
  q1 \ {✦, #0} ⊆ qf →
  closed_ty 1 ‖G‖ T1 →
  closed_ty 2 ‖G‖ T2 →
  closed_ql true 1 ‖G‖ q1 →
  closed_ql true 2 ‖G‖ q2 →
  closed_ql false 0 ‖G‖ qf →
  (#0 ∈ q1 → ✦ ∈ q1) →
  occurs .no_covariant T1 #0 →
  occurs .no_contravariant T2 #0 →
  qf ⊆ p →
  has_type G p (.ttabs T1 q1 t) (.TAll T1 q1 T2 q2) qf gs
| t_app:
  has_type G p f (.TFun T1 q1 T2 q2) qf gs →
  has_type G p t T1 qx gs →
  #0 ∈ q1 ∨ qtp G qx q1 gs ∨ ✦ ∈ q1 ∧
    qtp G ((vars_trans G qf) ∩ (vars_trans G qx)) q1 gs ∧
    (vars_trans G qf ∩ vars_trans G qx) \ {✦} ⊆ p ∧
    (∀i ∈ gs, %i ∉ vars_trans G qf ∧ %i ∉ vars_trans G qx) →
  q2 \ {✦, #0, #1} ⊆ p →
  (✦ ∈ qf → occurs .noneq T2 #0) →
  (✦ ∈ qx → occurs .noneq T2 #1) →
  has_type G p (.tapp f t) ([#0 ↦ qf] [#1 ↦ qx] T2) ([#0 ↦ qf] [#1 ↦ qx] q2) gs
| t_tapp:
  has_type G p f (.TAll T1 q1 T2 q2) qf gs →
  stp G Tx {✦} ∅ T1 gs →
  closed_ql true 0 ‖G‖ qx →
  #0 ∈ q1 ∨ qtp G qx q1 gs ∨ ✦ ∈ q1 ∧
    qtp G ((vars_trans G qf) ∩ (vars_trans G qx)) q1 gs ∧
    (vars_trans G qf ∩ vars_trans G qx) \ {✦} ⊆ p ∧
    (∀i ∈ gs, %i ∉ vars_trans G qf ∧ %i ∉ vars_trans G qx) →
  q2 \ {✦, #0, #1} ⊆ p →
  qx \ {✦} ⊆ p →
  (✦ ∈ qf → occurs .noneq T2 #0) →
  (✦ ∈ qx → occurs .noneq T2 #1) →
  has_type G p (.ttapp f Tx qx) ([#0 ↦ qf] [#1 ↦ (Tx, qx)] T2) ([#0 ↦ qf] [#1 ↦ qx] q2) gs
| t_sub:
  has_type G p t T1 q1 gs →
  stp G T1 q1 gr T2 gs →
  qtp G (q1 ∪ gr) q2 gs →
  q2 \ {✦} ⊆ p →
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
    split_ands; simp [sets]; rw [List.getElem?_eq_some] at h; exact h.1; c_extend;
  | q_self h _ =>
    split_ands; simp [closed_ql]; trans; swap; assumption; simp; simp [sets]
    rw [List.getElem?_eq_some] at h; exact h.1
  | q_trans => split_ands''

lemma stp_closed:
  stp G T1 q0 gr T2 gs →
  closed_ty 0 ‖G‖ T1 ∧ closed_ty 0 ‖G‖ T2 ∧ closed_ql false 0 ‖G‖ gr :=
by
  intro h; induction h
  case s_refl => split_ands'; simp [sets]
  case s_trans => split_ands''; apply Finset.union_subset; assumption'
  case s_top => split_ands'; simp [sets]
  case s_ref Q _ _ _ _ =>
    apply qtp_closed at Q; simp!; split_ands''
    apply closedql_fr_tighten; assumption; c_extend;
    apply closedql_fr_tighten; assumption; c_extend;
  case s_fun ha hb _ _ =>
    simp! at ha hb ⊢; split_ands''
  case s_tvar h _ =>
    simp!; split_ands'; rw [List.getElem?_eq_some] at h; apply h.1; simp [sets]
  case s_all ha hb _ _ =>
    simp! at ha hb ⊢; split_ands''

lemma hast_closed:
  has_type G p t T q gs →
  q \ {✦} ⊆ p ∧ closed_ty 0 ‖G‖ T ∧ closed_ql true 0 ‖G‖ q :=
by
  intro H; induction H
  case t_true => simp [closed_ql]; constructor
  case t_false => simp [closed_ql]; constructor
  case t_var h _ _ _ =>
    have := (List.getElem?_eq_some.1 h).1
    split_ands; simpa; assumption; simpa [sets]
  case t_ref IH =>
    simp [closed_ql]; simp!; split_ands''
    apply closedql_fr_tighten; assumption; c_extend;
  case t_get G p t T q1 q gs H1 H2 _ IH =>
    simp [closed_ty] at IH; split_ands''
    rename q \ _ ⊆ p => H3; simp [subst, sets] at H2 H3 ⊢; tauto
    apply closedql_bv_tighten; assumption; c_extend;
  case t_put IH1 IH2 =>
    simp [sets]; constructor
  case t_abs =>
    split_ands; trans; swap; assumption; simp; simp!; split_ands'; c_extend;
  case t_absa => split_ands''
  case t_tabs =>
    split_ands; trans; swap; assumption; simp; simp!; split_ands'; c_extend;
  case t_app G _ _ T1 q1 T2 q2 qf _ _ qx _ _ _ Q2 Dqf Dqx IH1 IH2 =>
    obtain ⟨IH1a, IH1b, IH1c⟩ := IH1; obtain ⟨IH2a, IH2b, IH2c⟩ := IH2
    simp! at IH1b; split_ands''
    · clear * - Q2 IH1a IH2a; simp [sets, subst] at Q2 IH1a IH2a ⊢; tauto
    · simp; repeat apply subst_tighten
      assumption; split_ands'; split_ands'
      rw [occurs_subst]; simpa; c_free; simp!
    · (repeat apply subst_tighten); assumption'; c_extend;
  case t_tapp G _ _ T1 q1 T2 q2 qf _ _ qx _ S1 _ _ Q2 QX Dqf Dqx IH2 =>
    obtain ⟨IH2a, IH2b, IH2c⟩ := IH2; simp! at IH2b; split_ands''
    · clear * - Q2 IH2a QX; simp [sets, subst] at Q2 QX IH2a ⊢; tauto
    · have := (stp_closed S1).1
      simp; repeat apply subst_tighten
      assumption; split_ands'; split_ands'
      rw [occurs_subst]; simpa; c_free; c_free;
    · (repeat apply subst_tighten); assumption'; c_extend;
  case t_sub S Q _ IH =>
    split_ands'; apply (stp_closed S).2.1; apply (qtp_closed Q).2
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
  stp G T1 q0 gr T2 gs' →
  gs ⊆ gs' →
  stp G T1 q0 gr T2 gs :=
by
  intros H1 H2; induction H1 generalizing gs
  case s_refl => apply s_refl; assumption
  case s_trans => apply s_trans; tauto; tauto
  case s_top => apply s_top; assumption
  case s_ref =>
    apply s_ref; tauto; tauto; assumption'
    apply qtp.gs_tighten; assumption'; apply qtp.gs_tighten; assumption'
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
  q1 \ {✦, #0} ⊆ qf →
  (#0 ∈ q1 → ✦ ∈ q1) →
  occurs .no_covariant T1 #0 →
  occurs .no_contravariant T2 %‖G‖ →
  qf ⊆ p →
  has_type G p (.tabs t) (.TFun' ‖G‖ T1 q1 T2 q2) qf gs :=
by
  intros h; intros; have ⟨_, _, _⟩ := hast_closed h
  simp at *; apply t_abs; assumption'
  · simp; rwa [ty.open_cancel, ql.subst_cancel, ty.open_cancel, ql.subst_cancel]
    c_free; c_free; simp [subst]; c_free; simp; c_free;
  · rw [ty.open_comm]; repeat apply subst_tighten
    c_extend; simp [sets]; simp [sets]; simp; simp; simp
  · rw [ql.subst_comm]; repeat apply subst_tighten
    c_extend; simp [sets]; simp [sets]; simp; simp; simp
  · simp; split_ands'; c_free;

lemma t_tabs':
  has_type (G++[(.TTop, qf, .self), ([#0 ↦ %‖G‖] T1, [#0 ↦ %‖G‖] q1, .tvar)])
    (qf ∪ {%‖G‖, %(‖G‖ + 1)}) t T2 q2 gs →
  closed_ty 1 ‖G‖ T1 →
  closed_ql true 1 ‖G‖ q1 →
  closed_ql false 0 ‖G‖ qf →
  q1 \ {✦, #0} ⊆ qf →
  (#0 ∈ q1 → ✦ ∈ q1) →
  occurs .no_covariant T1 #0 →
  occurs .no_contravariant T2 %‖G‖ →
  qf ⊆ p →
  has_type G p (.ttabs T1 q1 t) (.TAll' ‖G‖ T1 q1 T2 q2) qf gs :=
by
  intros h; intros; have ⟨_, _, _⟩ := hast_closed h
  simp at *; apply t_tabs; assumption'
  · simp; rwa [ty.open_cancel, ql.subst_cancel, ty.open_cancel, ql.subst_cancel]
    c_free; c_free; simp [subst]; c_free; simp; c_free;
  · rw [ty.open_comm]; repeat apply subst_tighten
    c_extend; simp [sets]; simp [sets]; simp; simp; simp
  · rw [ql.subst_comm]; repeat apply subst_tighten
    c_extend; simp [sets]; simp [sets]; simp; simp; simp
  · simp; split_ands'; c_free;

lemma gs_tighten:
  has_type G p t T q gs' →
  gs ⊆ gs' →
  has_type G p t T q gs :=
by
  intros H H1; induction H generalizing gs
  case t_true => apply t_true
  case t_false => apply t_false
  case t_var => eapply t_var; assumption'
  case t_ref IH => apply t_ref; apply IH; assumption'
  case t_get IH => apply t_get; apply IH; assumption'
  case t_put IH1 IH2 => eapply t_put; apply IH1; swap; apply IH2; assumption'
  case t_abs IH => eapply t_abs; apply IH; assumption'
  case t_absa IH => eapply t_absa; apply IH; assumption
  case t_tabs IH => eapply t_tabs; apply IH; assumption'
  case t_app IH1 IH2 =>
    eapply t_app; apply IH1; swap; apply IH2; assumption'
    rename _ ∨ _ ∨ _ => H; obtain H | H | H := H <;> try simp [H]
    replace H := H.gs_tighten H1; simp [H]
    right; right; obtain ⟨-, H2, -, H⟩ := H
    replace H2 := H2.gs_tighten H1; simp [H2]
    clear *- H1 H; intro _ h; apply H; tauto
  case t_tapp IH1 IH2 =>
    eapply t_tapp; apply IH2; assumption'
    apply stp.gs_tighten; assumption'
    rename _ ∨ _ ∨ _ => H; obtain H | H | H := H <;> try simp [H]
    replace H := H.gs_tighten H1; simp [H]
    right; right; obtain ⟨-, H2, -, H⟩ := H
    replace H2 := H2.gs_tighten H1; simp [H2]
    clear *- H1 H; intro _ h; apply H; tauto
  case t_sub IH =>
    eapply t_sub; apply IH; assumption'
    apply stp.gs_tighten; assumption'
    apply qtp.gs_tighten; assumption'
  case t_asc IH => eapply t_asc; apply IH; assumption'

lemma filter_widen:
  has_type G p t T q gs →
  p ⊆ p' →
  has_type G p' t T q gs :=
by
  intro h P; induction h
  case t_true => apply t_true
  case t_false => apply t_false
  case t_var => apply t_var; assumption'; tauto
  case t_ref IH => apply t_ref; apply IH; assumption; tauto
  case t_get IH => apply t_get; apply IH; assumption'; tauto
  case t_put IH1 IH2 => eapply t_put; apply IH1; swap; apply IH2; assumption'
  case t_abs IH1 => eapply t_abs; assumption'; tauto
  case t_absa IH1 => eapply t_absa; tauto
  case t_tabs IH1 => eapply t_tabs; assumption'; tauto
  case t_app IH1 IH2 =>
    eapply t_app; apply IH1; assumption; apply IH2; assumption'
    rename _ ∨ _ ∨ _ => H; obtain H | H | H := H <;> simp [H]
    right; right; split_ands''; trans; assumption'; trans; assumption'
  case t_tapp IH1 IH2 =>
    eapply t_tapp; apply IH2; assumption'
    rename _ ∨ _ ∨ _ => H; obtain H | H | H := H <;> simp [H]
    right; right; split_ands''
    trans; assumption'; trans; assumption'; trans; assumption'
  case t_sub IH => eapply t_sub; apply IH; assumption'; tauto
  case t_asc IH => eapply t_asc; apply IH; assumption

end has_type

-- context growth

namespace ctx_grow

open qtp

lemma on_qtp:
  qtp G q1 q2 gs →
  ctx_grow G G' gs →
  qtp G' q1 q2 gs :=
by
  intros Q0 CG; induction Q0 generalizing G'
  case q_sub =>
    apply q_sub; assumption; rwa [←CG.1]
  case q_cong =>
    apply q_cong; tauto; tauto
  case q_var G x Tx qx _ _ H1 _ H2 =>
    apply q_var; obtain (H | ⟨_, _, _, _, -, -, H, -⟩) := CG.2 x; rwa [←H]
    contradiction; assumption; rwa [←CG.1]
  case q_self G x Tx qx _ H1 H2 =>
    have := CG.1; have := (List.getElem?_eq_some.1 H1).1
    obtain (H | ⟨-, _, _, qx', H, Cqx, H1', H1''⟩) := CG.2 x; apply q_self; rwa [←H]; rwa [←CG.1]
    rw [H1] at H1'; simp at H1'; rcases H1' with ⟨rfl, rfl⟩; apply q_trans; swap
    apply q_self H1''; simp [closed_ql]; trans; apply Cqx; simp; omega
    apply q_sub; simp [sets]; clear * - H; tauto; simp [closed_ql]; trans; trans; swap; exact Cqx
    simp; simp; omega
  case q_trans IH1 IH2 =>
    apply q_trans; apply IH1 CG; apply IH2 CG

open stp

lemma on_stp:
  stp G T1 q0 gr T2 gs →
  ctx_grow G G' gs →
  stp G' T1 q0 gr T2 gs :=
by
  intros S0 CG; induction S0 generalizing G'
  case s_refl =>
    apply s_refl; rwa [←CG.1]
  case s_trans IH1 IH2 =>
    apply s_trans; apply IH1 CG; apply IH2 CG
  case s_top =>
    apply s_top; rwa [←CG.1]
  case s_ref =>
    apply s_ref; tauto; tauto; apply CG.on_qtp; assumption
    apply CG.on_qtp; assumption'
  case s_fun IH1 IH2 =>
    simp only [CG.1] at *; eapply s_fun; assumption'
    apply IH1; apply CG.append
    rename _ ∨ _ => h; obtain h | h := h; simp [h]; right
    apply on_qtp; assumption; apply CG.append
    apply IH2; apply CG.append
    apply on_qtp; assumption; apply CG.append
  case s_tvar x _ _ _ _ h _ =>
    apply s_tvar; obtain h1 | h1 := CG.2 x; rwa [←h1]
    simp [h] at h1; rwa [←CG.1]
  case s_all IH1 IH2 =>
    simp only [CG.1] at *; eapply s_all; assumption'
    apply IH1; apply CG.append
    rename _ ∨ _ => h; obtain h | h := h; simp [h]; right
    apply on_qtp; assumption; apply CG.append
    apply IH2; apply CG.append
    apply on_qtp; assumption; apply CG.append

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
  has_type G p t T q gs →
  ctx_grow G G' gs →
  has_type G' p t T q gs :=
by
  intros H1 CG; induction H1 generalizing G'
  case t_true => apply t_true
  case t_false => apply t_false
  case t_var G x _ _ _ _ _ H _ _ _ =>
    simp [CG.1] at *; obtain HG | HG := CG.2 x
    eapply t_var; assumption'; rwa [←HG]
    obtain ⟨-, T, q, q', -, -, H', H1⟩ := HG
    simp [H] at H'; obtain ⟨rfl, rfl, rfl⟩ := H'
    eapply t_var; assumption'
  case t_get IH =>
    apply t_get; apply IH; assumption'
  case t_put IH1 IH2 =>
    apply t_put; apply IH1; assumption; apply IH2; assumption
  case t_ref IH =>
    apply t_ref; apply IH; assumption'
  case t_abs IH =>
    simp [CG.1] at *; eapply t_abs; assumption'; apply IH
    apply ctx_grow.append; assumption
  case t_absa IH =>
    simp [CG.1] at *; eapply t_absa; tauto
  case t_app IH1 IH2 =>
    rename _ ∨ _ ∨ _ => H
    eapply t_app; assumption'
    apply IH1; assumption; apply IH2; assumption
    obtain H | H | H := H; simp [H]
    · right; left; apply CG.on_qtp H
    · right; right; simp [H]
      have qfi := fun a h => (H.2.2.2 a h).1
      have qxi := fun a h => (H.2.2.2 a h).2
      simp only [←CG.on_vars_trans qfi, ←CG.on_vars_trans qxi]
      split_ands''; apply CG.on_qtp; assumption
  case t_tabs IH =>
    simp [CG.1] at *; eapply t_tabs; assumption'; apply IH
    apply ctx_grow.append; assumption
  case t_tapp IH1 IH2 =>
    rename _ ∨ _ ∨ _ => H
    eapply t_tapp; assumption'
    apply IH2; assumption; apply CG.on_stp; assumption; rwa [←CG.1]
    obtain H | H | H := H; simp [H]
    · right; left; apply CG.on_qtp H
    · right; right; simp [H]
      have qfi := fun a h => (H.2.2.2 a h).1
      have qxi := fun a h => (H.2.2.2 a h).2
      simp only [←CG.on_vars_trans qfi, ←CG.on_vars_trans qxi]
      split_ands''; apply CG.on_qtp; assumption
  case t_sub IH =>
    eapply t_sub; assumption'; apply IH; assumption
    apply CG.on_stp; assumption
    apply CG.on_qtp; assumption
  case t_asc IH =>
    eapply t_asc; apply IH; assumption

end ctx_grow
