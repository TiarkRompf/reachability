import Lean4.LR
import Lean4.LangRules

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
  closed_ql true 0 ‖G‖ q0 →
  stp G T1 q0 gr T2 gs →
  sem_stp G q0 gr T1 T2 :=
by
  intro C h; induction h
  case s_refl => apply sem_stp_refl
  case s_trans S1 _ ih1 ih2 =>
    specialize ih1 C; specialize ih2 _
    apply Finset.union_subset; assumption; c_extend (stp_closed S1).2.2
    apply sem_stp_trans; assumption'
  case s_top => apply sem_stp_top
  case s_ref q1 q2 _ S1 S2 Q1 Q2 _ _ ih1 ih2 =>
    have ⟨_, _⟩ := qtp_closed Q2; simp [-sem_stp, sets] at ih1 ih2
    have h1: q1 \ {#0} = q1 := by ext; simp; contrapose!; rintro rfl; c_free;
    have h2: q2 \ {#0} = q2 := by ext; simp; contrapose!; rintro rfl; c_free;
    apply sem_stp_ref; assumption'
    simp only [h1, h2]; apply qtp_fundamental; assumption
    simp only [h1, h2]; apply qtp_fundamental; assumption
    constructor <;> intro h <;> absurd h <;> c_free;
    apply stp_closed at S2; tauto
  case s_fun ih1 ih2 =>
    simp [-sem_stp, sets] at ih1 ih2; apply sem_stp_fun; assumption'
    rename _ ∨ _ => h; obtain h | _ := h; simp [h]; right
    nth_rw 2 [Finset.union_comm]; apply qtp_fundamental; assumption
    nth_rw 2 [Finset.union_comm]; apply qtp_fundamental; assumption
  case s_tvar =>
    apply sem_stp_tvar; assumption
  case s_all ih1 ih2 =>
    simp [-sem_stp, sets] at ih1 ih2; apply sem_stp_all; assumption'
    rename _ ∨ _ => h; obtain h | _ := h; simp [h]; right
    apply qtp_fundamental; assumption
    nth_rw 2 [Finset.union_comm]; apply qtp_fundamental; assumption

theorem fundamental:
  has_type G p t T q gs →
  sem_type G t T p q :=
by
  intro h; induction h
  · apply sem_true
  · apply sem_false
  · apply sem_var; assumption'
  · apply sem_ref; assumption'; rename_i h h1 _; replace h := (hast_closed h).1
    intros _ _; apply h; simp; split_ands'; rintro rfl; contradiction
  case t_get h1 h ih =>
    have := sem_get ih ?_; simpa [-sem_type, subst, h] using this
    trans; swap; assumption; simp
  case t_put h IH1 IH2 =>
    apply sem_put; assumption'; convert IH2; ext; simp; contrapose!
    rintro rfl; have := (hast_closed h).2.2; c_free;
  case t_abs P IH =>
    apply sem_abs; assumption'
    convert IH; ext; simp; apply P; ext; simp; apply P
    trans; assumption; clear * - P; simp [sets]; tauto
  case t_absa IH =>
    apply sem_absa; assumption'
  case t_tabs qf _ _ _ _ _ _ p _ _ _ _ _ _ _ _ _ _ P IH =>
    have: p ∩ qf = qf := by ext; simp; apply P
    apply sem_tabs; assumption'; simpa only [this]; simpa [this]
  case t_app G p _ _ _ T2 _ qf _ _ qx HF HX SEP _ Dqf Dqx IH1 IH2 =>
    simp only [instSubstTyQl]; rw [ty.subst_qchange #0 (p ∩ qf), ty.subst_qchange #1 (p ∩ qx)]
    rotate_left
    · if h: ✦ ∈ qx then
        right; exact Dqx h
      else
        left; have := (hast_closed HX).1; ext; simp; intro
        apply this; simp; split_ands'; rintro rfl; contradiction
    · if h: ✦ ∈ qf then
        right; rw [occurs_subst]; simp; tauto
        have := (hast_closed HX).2.2; c_free; simp!
      else
        left; have := (hast_closed HF).1; ext; simp; intro
        apply this; simp; split_ands'; rintro rfl; contradiction
    apply sem_app_classic; assumption'
    · clear *- SEP; obtain _ | SEP | ⟨_, SEP, _⟩ := SEP
      tauto; apply qtp_fundamental at SEP; tauto
      apply qtp_fundamental at SEP; tauto
  case t_tapp G p _ _ _ T2 _ qf _ _ qx HF HX _ SEP _ _ Dqf Dqx IH2 =>
    simp only [instSubstTyQl]; have Ctx := (stp_closed HX).1
    rw [ty.subst_qchange #0 (p ∩ qf), ty.subst_qchange #1 (p ∩ qx)]
    rotate_left
    · if h: ✦ ∈ qx then
        right; exact Dqx h
      else
        left; rename_i this; ext; simp; intro
        apply this; simp; split_ands'; rintro rfl; contradiction
    · if h: ✦ ∈ qf then
        right; rw [occurs_subst]; simp; tauto; c_free; c_free;
      else
        left; have := (hast_closed HF).1; ext; simp; intro
        apply this; simp; split_ands'; rintro rfl; contradiction
    apply sem_tapp; assumption'
    · apply stp_fundamental; simp [sets]; assumption
    · clear *- SEP; obtain _ | SEP | ⟨_, SEP, _⟩ := SEP
      tauto; apply qtp_fundamental at SEP; tauto
      apply qtp_fundamental at SEP; tauto
  case t_sub h _ _ _ IH =>
    apply sem_sub; apply IH; apply stp_fundamental
    have := hast_closed h; simp [this]; assumption
    apply qtp_fundamental; assumption'
  case t_asc =>
    apply sem_ascript; assumption

theorem type_safety:
  has_type [] ∅ t T q ∅ →
  exp_type [] st_zero [] [] t T ∅ q :=
by
  intro h; apply fundamental at h; apply h
  · simp [env_type, env_type1, sets]; rintro _ _ (rfl | rfl) (rfl | rfl) <;> simp
  · simp [store_type]
