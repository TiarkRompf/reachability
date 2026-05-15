import Lean4.LR
import Lean4.LangRules

attribute [-simp] getElem?_pos Finset.singleton_union Finset.union_singleton

namespace Reachability

lemma qtp_fundamental:
  qtp G q1 q2 gs → sem_qtp G q1 q2 :=
by
  intros h; induction h with
  | q_sub => apply sem_qtp_sub; assumption'
  | q_cong => apply sem_qtp_congr; assumption'
  | q_var =>
    apply sem_qtp_var; assumption; c_free;
  | q_self => apply sem_qtp_self; assumption'
  | q_trans => apply sem_qtp_trans; assumption'

lemma stp_fundamental:
  closed_ql true 0 ‖G‖ q1 →
  closed_ty 0 ‖G‖ T1 →
  closed_ty 0 ‖G‖ T2 →
  stp G T1 q1 T2 q2 gs →
  sem_stp G T1 q1 T2 q2 :=
by
  intro C Ct1 Ct2 h; induction h
  case s_refl => apply sem_stp_refl; apply qtp_fundamental; assumption
  case s_trans Ct' S1 _ ih1 ih2 =>
    have Q := stp_implies_qtp C S1; apply qtp_closed at Q
    specialize ih1 C Ct1 Ct'; specialize ih2 Q.2 Ct' Ct2
    apply sem_stp_trans; assumption'
  case s_top => apply sem_stp_top
  case s_ref S1 S2 Q1 Q2 ih1 ih2 =>
    have Ct2' := Ct2; simp! at Ct1 Ct2'; casesm* _ ∧ _
    eapply sem_stp_ref2; rotate_right 2; exact Q1; exact Q2; assumption'
    apply ih1; simp [sets]; c_subst; c_extend; c_subst; c_extend;
    apply ih2; simp [sets]; c_subst; c_extend; c_subst; c_extend;
    apply qtp_fundamental; assumption; apply qtp_fundamental; assumption
  case s_pair S1 S2 Q1 Q2 ih1 ih2 =>
    have Ct2' := Ct2; simp! at Ct1 Ct2'; casesm* _ ∧ _
    eapply sem_stp_pair; rotate_right 2; exact Q1; exact Q2; assumption'
    apply ih1; simp [sets]; c_subst; c_extend; c_subst; c_extend;
    apply ih2; simp [sets]; c_subst; c_extend; c_subst; c_extend;
    apply qtp_fundamental; assumption; apply qtp_fundamental; assumption
  case s_list S1 ih1 =>
    have Ct2' := Ct2; simp! at Ct1 Ct2'; casesm* _ ∧ _
    eapply sem_stp_list; assumption'
    apply ih1; simp [sets]; c_subst; c_extend; c_subst; c_extend;
  case s_fun ih1 ih2 =>
    simp! at Ct1 Ct2; specialize ih1 _ _ _
    · simp [sets]
    · c_subst; c_extend Ct2.1
    · c_subst; c_extend Ct1.1
    specialize ih2 _ _ _
    · simp [sets]
    · simp; c_subst; c_extend Ct1.2.1; apply Finset.union_subset
      simp; apply closedql_fr_tighten; assumption; simp [closed_ql]
      trans; assumption; apply Finset.union_subset; c_extend; simp
    · c_subst; c_extend Ct2.2.1
    apply sem_stp_fun; assumption'
    rename _ ∨ _ => h; obtain h | _ := h; simp [h]; right
    rw [Finset.union_comm]; apply qtp_fundamental; assumption
    rw [Finset.union_comm]; apply qtp_fundamental; assumption
  case s_tvar =>
    apply sem_stp_tvar; assumption
  case s_all ih1 ih2 =>
    simp [-sem_stp, sets] at ih1 ih2; simp! at Ct1 Ct2; specialize ih1 _ _
    · c_subst; c_extend Ct2.1
    · c_subst; c_extend Ct1.1
    specialize ih2 _ _
    · c_subst; c_extend Ct1.2.1
    · c_subst; c_extend Ct2.2.1
    apply sem_stp_all; assumption'
    rename _ ∨ _ => h; obtain h | _ := h; simp [h]
    right; apply qtp_fundamental; assumption
    rw [Finset.union_comm]; apply qtp_fundamental; assumption

theorem fundamental:
  has_type G p t T q gs →
  sem_type G t T p q :=
by
  intro h; induction h
  · apply sem_unit
  · apply sem_nat
  · apply sem_add; assumption'
  · apply sem_mul; assumption'
  · apply sem_var; assumption'
  · apply sem_ref2; assumption'; rename_i h h1 _; replace h := (hast_closed h).1
    clear *- h h1; intro x; specialize @h x; aesop
  case t_get p _ _ _ _ _ q _ h2 h1 h ih =>
    apply sem_get2 at ih; specialize ih h1 h
    if hq: ✦ ∈ q then
      specialize h hq; simpa [-sem_type, ty.subst_freeq, h] using ih
    else
      have := (hast_closed h2).1; replace this: p ∩ q = q := by
        clear *- hq this; ext x; specialize @this x; aesop
      simpa [-sem_type, this] using ih
  case t_put h IH1 IH2 =>
    apply sem_put2; assumption'
  case t_pair h1 h2 _ _ =>
    apply sem_pair; assumption'; replace h1 := (hast_closed h1).1
    replace h2 := (hast_closed h2).1; apply Finset.union_subset; assumption'
  case t_fst p _ _ _ _ _ q _ h2 h1 h ih =>
    apply sem_fst at ih; specialize ih h1 h
    if hq: ✦ ∈ q then
      specialize h hq; simpa [-sem_type, ty.subst_freeq, h] using ih
    else
      have := (hast_closed h2).1; replace this: p ∩ q = q := by
        clear *- hq this; ext x; specialize @this x; aesop
      simpa [-sem_type, this] using ih
  case t_snd p _ _ _ _ _ q _ h2 h1 h ih =>
    apply sem_snd at ih; specialize ih h1 h
    if hq: ✦ ∈ q then
      specialize h hq; simpa [-sem_type, ty.subst_freeq, h] using ih
    else
      have := (hast_closed h2).1; replace this: p ∩ q = q := by
        clear *- hq this; ext x; specialize @this x; aesop
      simpa [-sem_type, this] using ih
  case t_nil => apply sem_nil; assumption
  case t_cons => apply sem_cons; assumption'
  case t_fold p _ _ q1 _ _ _ q2 _ h1 h2 _ _ h1b h2b _ _ _ =>
    have h1c := (hast_closed h1).1; have h2c := (hast_closed h2).1
    apply sem_fold; assumption'
    have h1': p ∩ q1 = q1 := by
      clear *- h1b h1c; ext i; specialize @h1c i; aesop
    have h2': p ∩ q2 = q2 := by
      clear *- h2b h2c; ext i; specialize @h2c i; aesop
    rwa [h1', h2']; apply closedql_fr_tighten; assumption
    apply (hast_closed h2).2.2
  case t_abs qf _ _ _ _ _ _ p _ _ _ _ _ _ _ _ _ _ P IH =>
    have: p ∩ qf = qf := by ext; simp; apply P
    apply sem_abs; assumption'; simpa only [this]; simpa only [this]
  case t_absa IH =>
    apply sem_absa; assumption'
  case t_tabs qf _ _ _ _ _ _ p _ _ _ _ _ _ _ _ _ _ P IH =>
    have: p ∩ qf = qf := by ext; simp; apply P
    apply sem_tabs; assumption'; simpa only [this]; simpa only [this]
  case t_tabsa IH =>
    apply sem_tabsa; assumption'
  case t_app G p _ _ _ T2 _ qf _ _ qx HF HX SEP _ Dqf Dqx IH1 IH2 =>
    simp only [instSubstTyQl]
    rw [ty.subst_qchange #0 (p ∩ qf), ty.subst_qchange #1 (p ∩ qx)]; rotate_left
    · if h: ✦ ∈ qx then
        aesop
      else
        left; have := (hast_closed HX).1; ext x; specialize @this x; clear *- h this; aesop
    · if h: ✦ ∈ qf then
        right; rw [occurs_subst]; simp; tauto; have := (hast_closed HX).2.2; c_free; simp!
      else
        left; have := (hast_closed HF).1; ext x; specialize @this x; clear *- h this; aesop
    apply sem_app_classic; assumption'
    · clear *- SEP; obtain _ | SEP | ⟨_, SEP, _⟩ := SEP
      tauto; apply qtp_fundamental at SEP; tauto
      apply qtp_fundamental at SEP; tauto
  case t_tapp G p _ _ _ T2 _ qf _ _ qx HF HX Ctx _ _ SEP _ _ Dqf Dqx IH2 =>
    simp only [instSubstTyQl]
    rw [ty.subst_qchange #0 (p ∩ qf), ty.subst_qchange #1 (p ∩ qx)]; rotate_left
    · if h: ✦ ∈ qx then
        aesop
      else
        left; rename_i this; ext x; specialize @this x; clear *- h this; aesop
    · if h: ✦ ∈ qf then
        right; rw [occurs_subst]; simp; tauto; c_free; c_free;
      else
        left; have := (hast_closed HF).1; ext x; specialize @this x; clear *- h this; aesop
    apply sem_tapp; assumption'
    · apply stp_fundamental; simp [sets]; assumption'
    · clear *- SEP; obtain _ | SEP | ⟨_, SEP, _⟩ := SEP
      tauto; apply qtp_fundamental at SEP; tauto
      apply qtp_fundamental at SEP; tauto
  case t_sub h _ _ _ IH =>
    obtain ⟨-, _, _⟩ := hast_closed h
    apply sem_sub; apply IH; apply stp_fundamental; assumption'
  case t_asc =>
    apply sem_ascript; assumption

theorem type_safety:
  has_type [] ∅ t T q ∅ →
  exp_type [] st_zero [] [] t T ∅ q :=
by
  intro h; apply fundamental at h; apply h
  · simp [env_type, env_type1, sets]; aesop
  · simp [store_type]
