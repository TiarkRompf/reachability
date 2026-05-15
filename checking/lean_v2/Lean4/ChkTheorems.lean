import Lean4.Checking
import Lean4.ChkThmSub
import Aesop

attribute [-simp] getElem?_pos Finset.singleton_union Finset.union_singleton

namespace Reachability

-- [-simp] is local; redefine them
attribute [-simp] Set.setOf_subset_setOf Set.subset_inter_iff Set.union_subset_iff
attribute [-simp] Finset.union_insert

open qtp
open stp
open has_type

-- unpack_argself

lemma unpack_argself_sound_gen:
  closed_ty 1 ‖G‖ T1 → closed_ql true 0 ‖G‖ qf → occurs .no_covariant T1 #0 →
  unpack_argself T1 qf σ1 = .ok T1' σ2 →
  gs ⊆ Finset.range ‖G‖ →
  closed_ty 0 ‖G‖ T1' ∧
    stp (G ++ [(.TTop, qf, .self)]) T1' {✦} ([#0 ↦ %‖G‖] T1) {✦} gs :=
by
  intro Ct Cq hocc h Hgs; simp only [unpack_argself] at h; split at h; swap
  simp only [excs] at h; obtain ⟨-, _, ⟨H2, rfl⟩, rfl, rfl⟩ := h
  next =>
    have: closed_ty 0 ‖G‖ T1 := by apply closedty_bv_tighten; assumption'
    split_ands'; rw [ty.open_free H2]; apply s_refl; apply q_sub; simp; simp [sets]
  next h1 =>
    simp only [excs] at h; obtain ⟨rfl, rfl⟩ := h
    apply closedql_fr_tighten at Cq; assumption'; split_ands
    simp; c_subst; assumption'
    have: (G ++ [(.TTop, qf, .self)])[‖G‖]? = some (.TTop, qf, .self) := by simp
    apply ty.self_subst_equiv (q0 := {✦}) (T := [#0 ↦ %‖G‖] T1) (gs := gs) at this
    specialize this _ _ _ _ _; intro h; specialize Hgs h; simp at Hgs;
    simp [sets]; c_extend; c_subst; c_extend; simp [hocc]; right; c_free;
    simp; rw [←ty.subst_open_chain #0 %‖G‖]; apply this.2; c_free;

lemma unpack_argself_sound_ref:
  has_type G p t (.TRef2 T1 q1 T2 q2) qf gs →
  unpack_argself T1 qf σ1 = .ok T1' σ2 →
  gs ⊆ Finset.range ‖G‖ →
  closed_ty 0 ‖G‖ T1' ∧
    has_type G p t (.TRef2 T1' q1 T2 q2) qf gs :=
by
  intro C h Hgs; obtain ⟨_, Ct, Cq⟩ := hast_closed C
  have Ct' := Ct; simp! at Ct'; obtain ⟨_, -, -, -, -, _, -⟩ := Ct'
  apply unpack_argself_sound_gen at h; specialize h Hgs; simp [h]; assumption'
  apply t_sub; assumption'; fapply s_ref; exact ∅; exact ∅
  · rw [ty.open_free]; simp [h.2]; c_free h.1
  · simp; apply s_refl; apply q_sub; simp; simp [sets]
  · apply q_sub; simp; obtain ⟨-,-,_,-,_,-⟩ := Ct
    apply closedql_bv_tighten; assumption; c_extend;
  · apply q_sub; simp; simp; c_subst; c_extend Ct.2.2.2.1
  simp; simp; clear *- h Ct; simp! at Ct ⊢; split_ands''; c_extend; c_free;

lemma unpack_self_sound_list:
  has_type G p t T1 qf gs →
  unpack_self T1 qf = .TList T1' →
  gs ⊆ Finset.range ‖G‖ →
  ✦ ∉ qf →
  closed_ty 0 ‖G‖ T1' ∧
    has_type G p t (.TList T1') qf gs :=
by
  intro C h Hgs Nfr; obtain ⟨_, Ct, Cq⟩ := hast_closed C
  obtain ⟨Ct', S, -⟩ := unpack_self_equiv _ _ h Hgs Ct Cq
  cases T1 <;> simp [unpack_self, Nfr] at h; split_ands
  · apply closedty_bv_tighten; subst T1'; rw [occurs_subst]; simp; c_free; simp!
    exact Ct'.1
  apply t_sub; assumption'

lemma unpack_argself_sound_fun:
  has_type G p t (.TFun T1 q1 T2 q2) qf gs →
  unpack_argself T1 qf σ1 = .ok T1' σ2 →
  gs ⊆ Finset.range ‖G‖ →
  closed_ty 0 ‖G‖ T1' ∧
    has_type G p t (.TFun T1' q1 T2 q2) qf gs :=
by
  intro C h Hgs; obtain ⟨_, Ct, Cq⟩ := hast_closed C
  have Ct' := Ct; simp! at Ct'; obtain ⟨_, -, -, -, -, _, -⟩ := Ct'
  apply unpack_argself_sound_gen at h; specialize h Hgs; simp [h]; assumption'
  apply t_sub; assumption'; fapply s_fun; exact ∅; exact ∅
  · rw [ty.open_free]; simp [h.2]; c_free h.1
  · right; apply q_sub; simp; simp; c_subst; c_extend Ct.2.2.1;
  · simp; apply s_refl; apply q_sub; simp; simp [sets]
  · apply q_sub; simp; simp; c_subst; c_extend Ct.2.2.2.1
  simp; simp; simp; clear *- h Ct; simp! at Ct ⊢; split_ands''; c_extend; c_free;

lemma unpack_argself_sound_all:
  has_type G p t (.TAll T1 q1 T2 q2) qf gs →
  unpack_argself T1 qf σ1 = .ok T1' σ2 →
  gs ⊆ Finset.range ‖G‖ →
  closed_ty 0 ‖G‖ T1' ∧
    has_type G p t (.TAll T1' q1 T2 q2) qf gs :=
by
  intro C h Hgs; obtain ⟨_, Ct, Cq⟩ := hast_closed C
  have Ct' := Ct; simp! at Ct'; obtain ⟨_, -, -, -, -, _, -⟩ := Ct'
  apply unpack_argself_sound_gen at h; specialize h Hgs; simp [h]; assumption'
  apply t_sub; assumption'; fapply s_all; exact ∅
  · rw [ty.open_free]; simp [h.2]; c_free h.1
  · right; apply q_sub; simp; simp; c_subst; c_extend Ct.2.2.1;
  · simp; apply s_refl; apply q_sub; simp; simp [sets]
  · apply q_sub; simp; simp; c_subst; c_extend Ct.2.2.2.1
  simp; clear *- h Ct; simp! at Ct ⊢; split_ands''; c_extend; c_free;

-- avoidance

lemma polsub_subst_comm a b (h1: x ≠ b ∧ y ≠ b) (h2: x = a → occurs .none t b):
  polsub pol t x y σ1 = .ok t' σ2 →
  polsub pol ([a ↦ b] t) ([a ↦ b] x) ([a ↦ b] y) σ1 = .ok ([a ↦ b] t') σ2 :=
by
  have heqxy: ∀{x y a b: id}, x ≠ b → y ≠ b → ([a ↦ b] x = [a ↦ b] y ↔ x = y) := by
    introv hx hy; by_cases h: x = y; subst y; simp; simp [h, subst]; split
    subst a; simp [h, hy.symm]; split <;> simp [hx, h]
  induction pol, t, x, y using polsub.induct generalizing t' a b σ1 σ2
  · simp [polsub, excs]; rintro rfl rfl; simp
  · simp [polsub, excs]; rintro rfl rfl; simp
  · simp [polsub, excs]; rintro rfl rfl; simp
  next x y x' =>
    simp; simp only [polsub, excs, and_assoc]; rintro ⟨-, _, h, rfl, rfl, rfl⟩
    simp [heqxy, h1]; rintro rfl; simp! at h2; simp [subst]
    split; subst a; simp [h, h2]; split; simp [h1]; simp [h]
  next pol x y T1 q1 T2 q2 IH1 IH2 =>
    intro h; simp! at h2; simp at h ⊢; simp only [polsub, excs] at h ⊢
    obtain ⟨T1', _, H1, T2', _, H2, h, rfl⟩ := h
    apply IH1 (a+1) (b+1) at H1; rotate_left; simpa; clear *- h2; aesop
    apply IH2 (a+1) (b+1) at H2; rotate_left; simpa; clear *- h2; aesop
    simp at H1 H2; simp [H1,H2]; clear IH1 H1 IH2 H2; simp [←h]; split_ands
    rw [ql.subst_comm']; congr; aesop (add simp subst); simp [h1]; aesop
    rw [ql.subst_comm']; congr; aesop (add simp subst); simp [h1]; aesop
  next pol x y T1 q1 T2 q2 IH1 IH2 =>
    intro h; simp! at h2; simp at h ⊢; simp only [polsub, excs] at h ⊢
    obtain ⟨T1', _, H1, T2', _, H2, h, rfl⟩ := h
    apply IH1 (a+1) (b+1) at H1; rotate_left; simpa; clear *- h2; aesop
    apply IH2 (a+1) (b+1) at H2; rotate_left; simpa; clear *- h2; aesop
    simp at H1 H2; simp [H1,H2]; clear IH1 H1 IH2 H2; simp [←h]; split_ands
    rw [ql.subst_comm']; congr; aesop (add simp subst); simp [h1]; aesop
    rw [ql.subst_comm']; congr; aesop (add simp subst); simp [h1]; aesop
  next pol x y T1 IH1 =>
    intro h; simp! at h2; simp at h ⊢; simp only [polsub, excs] at h ⊢
    obtain ⟨T1', _, H1, h, rfl⟩ := h
    apply IH1 (a+1) (b+1) at H1; rotate_left; simpa; clear *- h2; aesop
    simp at H1; simp [H1]; clear IH1 H1; simp [←h]
  next pol x y T1 q1 T2 q2 IH1 IH2 =>
    intro h; simp! at h2; simp at h ⊢; simp only [polsub, excs] at h ⊢
    obtain ⟨T1', _, H1, T2', _, H2, h, rfl⟩ := h
    apply IH1 (a+1) (b+1) at H1; rotate_left; simpa; clear *- h2; aesop
    apply IH2 (a+2) (b+2) at H2; rotate_left; simpa; clear *- h2; aesop
    simp at H1 H2; simp [H1,H2]; clear IH1 H1 IH2 H2; simp [←h]; split_ands
    rw [ql.subst_comm']; congr; aesop (add simp subst); simp [h1]; aesop
    rw [ql.subst_comm']; congr; aesop (add simp subst); simp [h1]; aesop
  next pol x y T1 q1 T2 q2 IH1 IH2 =>
    intro h; simp! at h2; simp at h ⊢; simp only [polsub, excs] at h ⊢
    obtain ⟨T1', _, H1, T2', _, H2, h, rfl⟩ := h
    apply IH1 (a+1) (b+1) at H1; rotate_left; simpa; clear *- h2; aesop
    apply IH2 (a+2) (b+2) at H2; rotate_left; simpa; clear *- h2; aesop
    simp at H1 H2; simp [H1,H2]; clear IH1 H1 IH2 H2; simp [←h]; split_ands
    rw [ql.subst_comm']; congr; aesop (add simp subst); simp [h1]; aesop
    rw [ql.subst_comm']; congr; aesop (add simp subst); simp [h1]; aesop

lemma polsub_preserves_closedness:
  closed_ty bvs fvs t → y ∈ qdom false bvs fvs → x ≠ ✦ →
  polsub pol t x y σ1 = .ok t' σ2 →
  let f0 := if pol then .no_contravariant else .no_covariant
  closed_ty bvs fvs t' ∧
    (∀ {f z}, z ≠ y → occurs f t z → occurs f t' z) ∧
    (x = y → occurs f0 t' x) ∧
    (x ≠ y → occurs .noneq t' x ∧ (occurs f0 t y → occurs f0 t' y)) :=
by
  intros C Cy XF H; induction t generalizing pol x y t' bvs σ1 σ2
  · simp! [excs] at H; obtain ⟨rfl, rfl⟩ := H; simp [C]; simp!
  · simp! [excs] at H; obtain ⟨rfl, rfl⟩ := H; simp [C]; simp!
  · simp! [excs] at H; obtain ⟨rfl, rfl⟩ := H; simp [C]; simp!
  next T1 q1 T2 q2 IH1 IH2 =>
    simp! only [excs] at H; simp! at C; obtain ⟨T1', _, HT1, T2', _, HT2, rfl, rfl⟩ := H
    apply IH1 (bvs := bvs+1) at HT1; rotate_left; tauto; simpa; simpa
    apply IH2 (bvs := bvs+1) at HT2; rotate_left; tauto; simpa; simpa
    clear IH1 IH2; simp at HT1 HT2 ⊢
    obtain ⟨H1c, H1z, H1a, H1b⟩ := HT1; obtain ⟨H2c, H2z, H2a, H2b⟩ := HT2; split_ands
    · clear H1a H1b H2a H2b; simp!; split_ands'
      apply Finset.union_subset; trans q1; simp; apply C.2.2.1; aesop
      apply Finset.union_subset; trans q2; simp; apply C.2.2.2.1; aesop
      aesop (add simp subst); aesop; aesop
    · clear *- H1z H2z; simp!; aesop (add simp subst)
    · clear *- H1a H2a; simp!; aesop (add simp subst)
    · clear *- H1b H2b; simp!; aesop (add simp subst)
  next T1 q1 T2 q2 IH1 IH2 =>
    simp! only [excs] at H; simp! at C; obtain ⟨T1', _, HT1, T2', _, HT2, rfl, rfl⟩ := H
    apply IH1 (bvs := bvs+1) at HT1; rotate_left; tauto; simpa; simpa
    apply IH2 (bvs := bvs+2) at HT2; rotate_left; tauto; simpa; simpa
    clear IH1 IH2; simp at HT1 HT2 ⊢
    obtain ⟨H1c, H1z, H1a, H1b⟩ := HT1; obtain ⟨H2c, H2z, H2a, H2b⟩ := HT2; split_ands
    · clear H1a H1b H2a H2b; simp!; split_ands'
      apply Finset.union_subset; trans q1; simp; apply C.2.2.1
      split; split; simp; c_extend; simp; simp
      apply Finset.union_subset; trans q2; simp; apply C.2.2.2.1
      split; split; simp; c_extend; simp; simp
      aesop (add simp subst); aesop; aesop
    · clear *- H1z H2z; simp!; aesop (add simp subst)
    · clear *- H1a H2a; simp!; aesop (add simp subst)
    · clear *- H1b H2b; simp!; aesop (add simp subst)
  · simp! only [excs, and_assoc] at H; aesop (add simp occurs)
  next T1 q1 T2 q2 IH1 IH2 =>
    simp! only [excs] at H; simp! at C; obtain ⟨T1', _, HT1, T2', _, HT2, rfl, rfl⟩ := H
    apply IH1 (bvs := bvs+1) at HT1; rotate_left; tauto; simpa; simpa
    apply IH2 (bvs := bvs+2) at HT2; rotate_left; tauto; simpa; simpa
    clear IH1 IH2; simp at HT1 HT2 ⊢
    obtain ⟨H1c, H1z, H1a, H1b⟩ := HT1; obtain ⟨H2c, H2z, H2a, H2b⟩ := HT2; split_ands
    · clear H1a H1b H2a H2b; simp!; split_ands'
      apply Finset.union_subset; trans q1; simp; apply C.2.2.1
      split; split; simp; c_extend; simp; simp
      apply Finset.union_subset; trans q2; simp; apply C.2.2.2.1
      split; split; simp; c_extend; simp; simp
      aesop (add simp subst); aesop; aesop
    · clear *- H1z H2z; simp!; aesop (add simp subst)
    · clear *- H1a H2a; simp!; aesop (add simp subst)
    · clear *- H1b H2b; simp!; aesop (add simp subst)
  next T1 q1 T2 q2 IH1 IH2 =>
    simp! only [excs] at H; simp! at C; obtain ⟨T1', _, HT1, T2', _, HT2, rfl, rfl⟩ := H
    apply IH1 (bvs := bvs+1) at HT1; rotate_left; tauto; simpa; simpa
    apply IH2 (bvs := bvs+1) at HT2; rotate_left; tauto; simpa; simpa
    clear IH1 IH2; simp at HT1 HT2 ⊢
    obtain ⟨H1c, H1z, H1a, H1b⟩ := HT1; obtain ⟨H2c, H2z, H2a, H2b⟩ := HT2; split_ands
    · clear H1a H1b H2a H2b; simp!; split_ands'
      apply Finset.union_subset; trans q1; simp; apply C.2.2.1; aesop
      apply Finset.union_subset; trans q2; simp; apply C.2.2.2.1; aesop
      aesop; aesop
    · clear *- H1z H2z; simp!; aesop (add simp subst)
    · clear *- H1a H2a; simp!; aesop (add simp subst)
    · clear *- H1b H2b; simp!; aesop (add simp subst)
  next T1 IH1 =>
    simp! only [excs] at H; simp! at C; obtain ⟨T1', _, HT1, rfl, rfl⟩ := H
    apply IH1 (bvs := bvs+1) at HT1; rotate_left; tauto; simpa; simpa
    clear IH1; simp at HT1 ⊢; obtain ⟨H1c, H1z, H1a, H1b⟩ := HT1
    split_ands
    · clear H1a H1b; simp!; split_ands'; aesop
    · clear *- H1z; simp!; aesop (add simp subst)
    · clear *- H1a; simp!; aesop (add simp subst)
    · clear *- H1b; simp!; aesop (add simp subst)

lemma polsub_sound:
  closed_ty 0 ‖G‖ t → closed_ql true 0 ‖G‖ q0 →
  (∀G', G <+: G' → qtp G' {%x} {%y} gs) →
  polsub pol t %x %y σ1 = .ok t' σ2 →
  if pol then stp G t q0 t' q0 gs else stp G t' q0 t q0 gs :=
by
  intros C C0 Q H; induction t using ty.induct' generalizing G t' pol q0 σ1 σ2
  · simp [polsub, excs] at H; obtain ⟨rfl, rfl⟩ := H; split
    all_goals apply s_refl; apply q_sub; simp; assumption
  · simp [polsub, excs] at H; obtain ⟨rfl, rfl⟩ := H; split
    all_goals apply s_refl; apply q_sub; simp; assumption
  · simp [polsub, excs] at H; obtain ⟨rfl, rfl⟩ := H; split
    all_goals apply s_refl; apply q_sub; simp; assumption
  next T1 q1 T2 q2 IH1 IH2 => -- TRef
    simp only [polsub, excs] at H; simp! at C
    have Cxy := by specialize Q G (by simp); apply qtp_closed at Q; simp [sets] at Q; exact Q
    obtain ⟨T1', _, HT1, T2', _, HT2, H, rfl⟩ := H; simp at HT1 HT2
    have HT1' := polsub_preserves_closedness C.1 (by simp [Cxy]) (by simp) HT1
    replace HT1 := fun a =>
      IH1 (G := G++[a]) (q0 := {✦}) _ (by simp) (by c_subst; c_extend C.1)
        (by simp [sets]) (by rintro _ ⟨_, rfl⟩; apply Q; simp)
        (polsub_subst_comm #0 %‖G‖ (by simp; omega) (by simp) HT1)
    clear IH1
    have HT2' := polsub_preserves_closedness C.2.1 (by simp [Cxy]) (by simp) (HT2)
    replace HT2 := fun a =>
      IH2 (G := G++[a]) (q0 := {✦}) _ (by simp) (by c_subst; c_extend C.2.1)
        (by simp [sets]) (by rintro _ ⟨_, rfl⟩; apply Q; simp)
        (polsub_subst_comm #0 %‖G‖ (by simp; omega) (by simp) HT2)
    clear IH2; obtain ⟨_, H1z, -⟩ := HT1'; obtain ⟨_, H2z, -⟩ := HT2'
    have: closed_ql true 0 (‖G‖+1) q1 := by
      apply closedql_bv_tighten; simp [C]; c_extend C.2.2.1
    have: closed_ql true 0 (‖G‖+1) [#0↦{%‖G‖}] q2 := by
      c_subst; c_extend C.2.2.2.1
    cases pol <;> simp at H HT1 HT2 ⊢ <;> subst t'
    · fapply s_ref; exact ∅; exact ∅; rotate_left 4; simp; simp
      simp; apply HT1; simp; apply HT2
      · simp; apply q_subst; simpa; apply Q; simp
      · apply q_sub; simp [subst, sets]; clear *-; tauto; simpa
    · fapply s_ref; exact ∅; exact ∅; rotate_left 4; simp; simp
      simp; apply HT1; simp; apply HT2
      · apply q_sub; simp [subst, sets]; simpa
      · have xg: x ≠ ‖G‖ := (by omega); have xg1: x ≠ ‖G‖+1 := (by omega)
        simp [ql.subst_comm (x2 := %x), xg]
        apply q_subst; simpa; apply Q; simp
  next T1 q1 T2 q2 IH1 IH2 => -- TFun
    simp only [polsub, excs] at H; simp! at C
    have Cxy := by specialize Q G (by simp); apply qtp_closed at Q; simp [sets] at Q; exact Q
    obtain ⟨T1', _, HT1, T2', _, HT2, H, rfl⟩ := H; simp at HT1 HT2
    have HT1' := polsub_preserves_closedness C.1 (by simp [Cxy]) (by simp) HT1
    replace HT1 := fun a =>
      IH1 (G := G++[a]) (q0 := {✦}) _ (by simp) (by c_subst; c_extend C.1)
        (by simp [sets]) (by rintro _ ⟨_, rfl⟩; apply Q; simp)
        (polsub_subst_comm #0 %‖G‖ (by simp; omega) (by simp) HT1)
    clear IH1
    have HT2' := polsub_preserves_closedness C.2.1 (by simp [Cxy]) (by simp) (HT2)
    replace HT2 := fun a b =>
      IH2 (G := G++[a, b]) (q0 := {✦}) _ (by simp) (by c_subst; c_extend C.2.1)
        (by simp [sets]) (by rintro _ ⟨_, rfl⟩; apply Q; simp)
        (polsub_subst_comm #0 %‖G‖ (by simp [subst]; omega)
          (by intro h; absurd h; simp [subst])
          (polsub_subst_comm #1 %(‖G‖+1) (by simp; omega) (by simp) HT2))
    clear IH2; obtain ⟨_, H1z, -⟩ := HT1'; obtain ⟨_, H2z, -⟩ := HT2'
    have: closed_ql true 0 (‖G‖+1) [#0↦{%‖G‖}] q1 := by
      c_subst; c_extend C.2.2.1
    have: closed_ql true 0 (‖G‖+2) [#0↦{%‖G‖}][#1↦{%(‖G‖ + 1)}] q2 := by
      c_subst; c_extend C.2.2.2.1
    cases pol <;> simp at H HT1 HT2 ⊢ <;> subst t'
    · fapply s_fun; exact ∅; exact ∅; rotate_left 4; simp; simp; simp
      simp; apply HT1; right; swap; simp; apply HT2
      · have: x≠‖G‖ := (by omega); simp [ql.subst_comm (x2:=%x), this]
        apply q_subst; simpa; apply Q; simp
      · apply q_sub; simp [subst, sets]; clear *-; tauto; simpa
    · fapply s_fun; exact ∅; exact ∅; rotate_left 4; simp; simp; simp
      simp; apply HT1; right; swap; simp; apply HT2
      · apply q_sub; simp [subst, sets]; clear *-; tauto; simpa
      · have xg: x ≠ ‖G‖ := (by omega); have xg1: x ≠ ‖G‖+1 := (by omega)
        simp [ql.subst_comm (x2 := %x), xg, xg1]
        apply q_subst; simpa; apply Q; simp
  · simp only [polsub, excs, and_assoc] at H; obtain ⟨-, _, _, rfl, rfl, rfl⟩ := H
    split; all_goals apply s_refl; apply q_sub; simp; assumption
  next T1 q1 T2 q2 IH1 IH2 => -- TAll
    simp only [polsub, excs] at H; simp! at C
    have Cxy := by specialize Q G (by simp); apply qtp_closed at Q; simp [sets] at Q; exact Q
    obtain ⟨T1', _, HT1, T2', _, HT2, H, rfl⟩ := H; simp at HT1 HT2
    have HT1' := polsub_preserves_closedness C.1 (by simp [Cxy]) (by simp) HT1
    replace HT1 := fun a =>
      IH1 (G := G++[a]) (q0 := {✦}) _ (by simp) (by c_subst; c_extend C.1)
        (by simp [sets]) (by rintro _ ⟨_, rfl⟩; apply Q; simp)
        (polsub_subst_comm #0 %‖G‖ (by simp; omega) (by simp) HT1)
    clear IH1
    have HT2' := polsub_preserves_closedness C.2.1 (by simp [Cxy]) (by simp) (HT2)
    replace HT2 := fun a b =>
      IH2 (G := G++[a, b]) (q0 := {✦}) _ (by simp) (by c_subst; c_extend C.2.1)
        (by simp [sets]) (by rintro _ ⟨_, rfl⟩; apply Q; simp)
        (polsub_subst_comm #0 %‖G‖ (by simp [subst]; omega)
          (by intro h; absurd h; simp [subst])
          (polsub_subst_comm #1 %(‖G‖+1) (by simp; omega) (by simp) HT2))
    clear IH2; obtain ⟨_, H1z, -⟩ := HT1'; obtain ⟨_, H2z, -⟩ := HT2'
    have: closed_ql true 0 (‖G‖+1) [#0↦{%‖G‖}] q1 := by
      c_subst; c_extend C.2.2.1
    have: closed_ql true 0 (‖G‖+2) [#0↦{%‖G‖}][#1↦{%(‖G‖ + 1)}] q2 := by
      c_subst; c_extend C.2.2.2.1
    cases pol <;> simp at H HT1 HT2 ⊢ <;> subst t'
    · fapply s_all; exact ∅; rotate_left 4; simp
      apply HT1; right; swap; simp; apply HT2
      · have: x≠‖G‖ := (by omega); simp [ql.subst_comm (x2:=%x), this]
        apply q_subst; simpa; apply Q; simp
      · apply q_sub; simp [subst, sets]; clear *-; tauto; simpa
    · fapply s_all; exact ∅; rotate_left 4; simp
      apply HT1; right; swap; simp; apply HT2
      · apply q_sub; simp [subst, sets]; clear *-; tauto; simpa
      · have xg: x ≠ ‖G‖ := (by omega); have xg1: x ≠ ‖G‖+1 := (by omega)
        simp [ql.subst_comm (x2 := %x), xg, xg1]
        apply q_subst; simpa; apply Q; simp
  next T1 q1 T2 q2 IH1 IH2 => -- TProd
    simp only [polsub, excs] at H; simp! at C
    have Cxy := by specialize Q G (by simp); apply qtp_closed at Q; simp [sets] at Q; exact Q
    obtain ⟨T1', _, HT1, T2', _, HT2, H, rfl⟩ := H; simp at HT1 HT2
    have HT1' := polsub_preserves_closedness C.1 (by simp [Cxy]) (by simp) HT1
    replace HT1 := fun a =>
      IH1 (G := G++[a]) (q0 := {✦}) _ (by simp) (by c_subst; c_extend C.1)
        (by simp [sets]) (by rintro _ ⟨_, rfl⟩; apply Q; simp)
        (polsub_subst_comm #0 %‖G‖ (by simp; omega) (by simp) HT1)
    clear IH1
    have HT2' := polsub_preserves_closedness C.2.1 (by simp [Cxy]) (by simp) (HT2)
    replace HT2 := fun a =>
      IH2 (G := G++[a]) (q0 := {✦}) _ (by simp) (by c_subst; c_extend C.2.1)
        (by simp [sets]) (by rintro _ ⟨_, rfl⟩; apply Q; simp)
        (polsub_subst_comm #0 %‖G‖ (by simp; omega) (by simp) HT2)
    clear IH2; obtain ⟨_, H1z, -⟩ := HT1'; obtain ⟨_, H2z, -⟩ := HT2'
    have: closed_ql true 0 (‖G‖+1) [#0↦{%‖G‖}] q1 := by
      c_subst; c_extend C.2.2.1
    have: closed_ql true 0 (‖G‖+1) [#0↦{%‖G‖}] q2 := by
      c_subst; c_extend C.2.2.2.1
    cases pol <;> simp at H HT1 HT2 ⊢ <;> subst t'
    · fapply s_pair; exact ∅; exact ∅; rotate_left 4; simp; simp
      simp; apply HT1; simp; apply HT2
      · apply q_sub; simp [subst, sets]; clear *-; tauto; simpa
      · apply q_sub; simp [subst, sets]; clear *-; tauto; simpa
    · fapply s_pair; exact ∅; exact ∅; rotate_left 4; simp; simp
      simp; apply HT1; simp; apply HT2
      · have xg: x ≠ ‖G‖ := (by omega); have xg1: x ≠ ‖G‖+1 := (by omega)
        simp [ql.subst_comm (x2 := %x), xg]
        apply q_subst; simpa; apply Q; simp
      · have xg: x ≠ ‖G‖ := (by omega); have xg1: x ≠ ‖G‖+1 := (by omega)
        simp [ql.subst_comm (x2 := %x), xg]
        apply q_subst; simpa; apply Q; simp
  next T1 IH1 => -- TList
    simp only [polsub, excs] at H; simp! at C
    have Cxy := by specialize Q G (by simp); apply qtp_closed at Q; simp [sets] at Q; exact Q
    obtain ⟨T1', _, HT1, H, rfl⟩ := H; simp at HT1
    have HT1' := polsub_preserves_closedness C.1 (by simp [Cxy]) (by simp) HT1
    replace HT1 := fun a =>
      IH1 (G := G++[a]) (q0 := {✦}) _ (by simp) (by c_subst; c_extend C.1)
        (by simp [sets]) (by rintro _ ⟨_, rfl⟩; apply Q; simp)
        (polsub_subst_comm #0 %‖G‖ (by simp; omega) (by simp) HT1)
    clear IH1; obtain ⟨_, H1z, -⟩ := HT1'
    cases pol <;> simp at H HT1 ⊢ <;> subst t'
    · fapply s_list; exact ∅; swap; simp; simp; apply HT1
    · fapply s_list; exact ∅; swap; simp; simp; apply HT1

lemma rm_contravariant_sound:
  closed_ty 0 ‖G‖ T2 → closed_ql true 0 ‖G‖ q0 → n < ‖G‖ →
  rm_contravariant T2 %n σ1 = .ok T2' σ2 →
  stp G T2 q0 T2' q0 gs ∧ closed_ty 0 ‖G‖ T2' ∧ occurs .no_contravariant T2' %n :=
by
  intro Ct2 Cq0 Hn h; simp [rm_contravariant] at h; split_ands
  · apply polsub_sound Ct2 at h; assumption'
    intro G' HG; apply q_sub; simp; simp [sets]
    obtain ⟨G', rfl⟩ := HG; simp; omega
  · apply polsub_preserves_closedness Ct2 at h; simp at h; simp [h]; simpa; simp
  · apply polsub_preserves_closedness Ct2 at h; simp at h; simp [h]; simpa; simp

lemma avoid_subst_comm (a b: id) (h1: x ≠ b) (h2: x = a → occurs .none t b):
  avoid t x σ1 = .ok (t', g) σ2 →
  avoid ([a ↦ b] t) ([a ↦ b] x) σ1 = .ok ([a ↦ b] t', [a ↦ b] g) σ2 :=
by
  intro h; simp only [avoid] at h ⊢
  have heq: occurs .noneq ([a ↦ b] t) ([a ↦ b] x) ↔ occurs .noneq t x := by
    simp; simp [subst]; split; subst a; simp [h1.symm]; rintro -
    apply occurs_none; simp [h2]; rename_i h'; simp [Ne.symm h', h1, h']
  simp only [heq]; clear heq; split at h <;> rename_i h0 <;> simp [h0, -bind_pure_comp]
  · simp [excs] at h; obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h; simp [excs]; simp [subst]
  simp only [excs] at h ⊢; obtain ⟨v1, _, h1, h⟩ := h; simp [h1, -bind_pure_comp]
  clear v1 h1; split at h <;> simp [excs, -bind_pure_comp] at h ⊢
  next T1 q1 T2 q2 => -- TRef
    obtain ⟨T1', _, h3, T2', h4, rfl, rfl⟩ := h; simp! at h2
    simp; apply polsub_subst_comm (a+1) (b+1) at h3
    rotate_left; simpa; simp; rintro rfl; simp [h2]; conv at h3 => enter [1, 4]; simp [subst]
    simp [h3]; apply polsub_subst_comm (a+1) (b+1) at h4
    rotate_left; simpa; simp; rintro rfl; simp [h2]; conv at h4 => enter [1, 4]; simp [subst]
    simp [h4]; split_ands
    · rw [ql.subst_comm' (a := a+1)]; congr; simp [h1]; simp; rintro rfl; simp [h2]
    · rw [ql.subst_comm' (a := a+1)]; congr; simp [subst]; simp [h1]; simp; rintro rfl; simp [h2]
  next T1 q1 T2 q2 => -- TProd
    obtain ⟨T1', _, h3, T2', h4, rfl, rfl⟩ := h; simp! at h2
    simp; apply polsub_subst_comm (a+1) (b+1) at h3
    rotate_left; simpa; simp; rintro rfl; simp [h2]; conv at h3 => enter [1, 4]; simp [subst]
    simp [h3]; apply polsub_subst_comm (a+1) (b+1) at h4
    rotate_left; simpa; simp; rintro rfl; simp [h2]; conv at h4 => enter [1, 4]; simp [subst]
    simp [h4]; split_ands
    · rw [ql.subst_comm' (a := a+1)]; congr; simp [subst]; simp [h1]; simp; rintro rfl; simp [h2]
    · rw [ql.subst_comm' (a := a+1)]; congr; simp [subst]; simp [h1]; simp; rintro rfl; simp [h2]
  next T1 => -- TProd
    obtain ⟨T1', h3, rfl, rfl⟩ := h; simp! at h2; simp; apply polsub_subst_comm (a+1) (b+1) at h3
    rotate_left; simpa; simp; rintro rfl; simp [h2]; conv at h3 => enter [1, 4]; simp [subst]
    simp [h3]
  next T1 q1 T2 q2 => -- TFun
    obtain ⟨T1', _, h3, T2', h4, rfl, rfl⟩ := h; simp! at h2
    simp; apply polsub_subst_comm (a+1) (b+1) at h3
    rotate_left; simpa; simp; rintro rfl; simp [h2]; conv at h3 => enter [1, 4]; simp [subst]
    simp [h3]; apply polsub_subst_comm (a+2) (b+2) at h4
    rotate_left; simpa; simp; rintro rfl; simp [h2]; conv at h4 => enter [1, 4]; simp [subst]
    simp [h4]; split_ands
    · rw [ql.subst_comm' (a := a+1)]; congr; simp [h1]; simp; rintro rfl; simp [h2]
    · rw [ql.subst_comm' (a := a+2)]; congr; simp [subst]; simp [h1]; simp; rintro rfl; simp [h2]
  next T1 q1 T2 q2 => -- TAll
    obtain ⟨T1', _, h3, T2', h4, rfl, rfl⟩ := h; simp! at h2
    simp; apply polsub_subst_comm (a+1) (b+1) at h3
    rotate_left; simpa; simp; rintro rfl; simp [h2]; conv at h3 => enter [1, 4]; simp [subst]
    simp [h3]; apply polsub_subst_comm (a+2) (b+2) at h4
    rotate_left; simpa; simp; rintro rfl; simp [h2]; conv at h4 => enter [1, 4]; simp [subst]
    simp [h4]; split_ands
    · rw [ql.subst_comm' (a := a+1)]; congr; simp [h1]; simp; rintro rfl; simp [h2]
    · rw [ql.subst_comm' (a := a+2)]; congr; simp [subst]; simp [h1]; simp; rintro rfl; simp [h2]

lemma avoid_preserves_closedness:
  closed_ty bvs fvs t → x ≠ ✦ →
  avoid t x σ1 = .ok (t', g) σ2 →
  closed_ty bvs fvs t' ∧ g ⊆ {x} ∧
    (∀x', x' = x ∨ occurs .noneq t x' → occurs .noneq t' x') ∧
    (∀x', occurs .no_contravariant t x' → occurs .no_contravariant t' x') :=
by
  intro c _ h; simp only [avoid] at h
  split at h; simp [excs] at h; obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
  simp; split_ands'; simp only [excs] at h; obtain ⟨-, _, -, h⟩ := h
  split at h; rotate_right 4
  simp [excs] at h; simp [excs] at h; simp [excs] at h; simp [excs] at h
  next => -- TRef
    simp only [excs] at h; obtain ⟨T1', _, h1, T2', _, h2, h, rfl⟩ := h
    simp at h; obtain ⟨rfl, rfl⟩ := h; simp; simp! at c
    apply polsub_preserves_closedness c.1 at h1; rotate_left; simp; simpa
    apply polsub_preserves_closedness c.2.1 at h2; rotate_left; simp; simpa
    simp [c] at h1 h2; obtain ⟨_, h1z, h1⟩ := h1; obtain ⟨_, h2z, h2⟩ := h2
    split_ands
    · simp!; split_ands'
      simp [closed_ql]; trans; swap; exact c.2.2.1; simp [subst]; simp [subst]
      apply Finset.union_subset; trans; swap; exact c.2.2.2.1; simp; simp [sets]
      simp [subst, c]; simp [h1]; simp [h2]
    · aesop (add simp subst, simp occurs)
    · aesop (add simp subst, simp occurs)
    · aesop (add simp subst, simp occurs)
  next => -- TProd
    simp only [excs] at h; obtain ⟨T1', _, h1, T2', _, h2, h, rfl⟩ := h
    simp at h; obtain ⟨rfl, rfl⟩ := h; simp; simp! at c
    apply polsub_preserves_closedness c.1 at h1; rotate_left; simp; simpa
    apply polsub_preserves_closedness c.2.1 at h2; rotate_left; simp; simpa
    simp [c] at h1 h2; obtain ⟨_, h1z, h1⟩ := h1; obtain ⟨_, h2z, h2⟩ := h2
    split_ands
    · simp!; split_ands'
      simp [subst]; apply Finset.union_subset; trans; swap; exact c.2.2.1; simp; simp [sets]
      simp [subst]; apply Finset.union_subset; trans; swap; exact c.2.2.2.1; simp; simp [sets]
      simp [h1]; simp [h2]
    · aesop (add simp subst, simp occurs)
    · aesop (add simp subst, simp occurs)
    · aesop (add simp subst, simp occurs)
  next => -- TList
    simp only [excs] at h; obtain ⟨T1', _, h1, h, rfl⟩ := h
    simp at h; obtain ⟨rfl, rfl⟩ := h; simp; simp! at c
    apply polsub_preserves_closedness c.1 at h1; rotate_left; simp; simpa
    simp [c] at h1; obtain ⟨_, h1z, h1⟩ := h1; split_ands
    · simp!; split_ands'; simp [h1]
    · aesop (add simp subst, simp occurs)
    · aesop (add simp subst, simp occurs)
    · aesop (add simp subst, simp occurs)
  next => -- TFun
    simp only [excs] at h; obtain ⟨T1', _, h1, T2', _, h2, h, rfl⟩ := h
    simp at h; obtain ⟨rfl, rfl⟩ := h; simp; simp! at c
    apply polsub_preserves_closedness c.1 at h1; rotate_left; simp; simpa
    apply polsub_preserves_closedness c.2.1 at h2; rotate_left; simp; simpa
    simp [c] at h1 h2; obtain ⟨_, h1z, h1⟩ := h1; obtain ⟨_, h2z, h2⟩ := h2
    split_ands
    · simp!; split_ands'
      simp [closed_ql]; trans; swap; exact c.2.2.1; simp [subst]; simp [subst]
      apply Finset.union_subset; trans; swap; exact c.2.2.2.1; simp; simp [sets]
      aesop (add simp subst); simp [h1]; simp [h2]
    · aesop (add simp subst, simp occurs)
    · aesop (add simp subst, simp occurs)
    · aesop (add simp subst, simp occurs)
  next => -- TAll
    simp only [excs] at h; obtain ⟨T1', _, h1, T2', _, h2, h, rfl⟩ := h
    simp at h; obtain ⟨rfl, rfl⟩ := h; simp; simp! at c
    apply polsub_preserves_closedness c.1 at h1; rotate_left; simp; simpa
    apply polsub_preserves_closedness c.2.1 at h2; rotate_left; simp; simpa
    simp [c] at h1 h2; obtain ⟨_, h1z, h1⟩ := h1; obtain ⟨_, h2z, h2⟩ := h2
    split_ands
    · simp!; split_ands'
      simp [closed_ql]; trans; swap; exact c.2.2.1; simp [subst]; simp [subst]
      apply Finset.union_subset; trans; swap; exact c.2.2.2.1; simp; simp [sets]
      aesop (add simp subst); simp [h1]; simp [h2]
    · aesop (add simp subst, simp occurs)
    · aesop (add simp subst, simp occurs)
    · aesop (add simp subst, simp occurs)

lemma avoid_sound:
  closed_ty 0 ‖G‖ t →
  closed_ql true 0 ‖G‖ q0 →
  avoid t %x σ1 = .ok (t', gr) σ2 →
  gr ⊆ q0 →
  stp G t q0 t' q0 gs :=
by
  intro C _ H _; simp only [avoid] at H; split at H
  · simp [excs] at H; obtain ⟨⟨rfl, rfl⟩, rfl⟩ := H; apply s_refl
    apply q_sub; simp; assumption
  have: x < ‖G‖ := by rename_i h; contrapose! h; c_free; assumption
  have: ∀G', %x ∈ gr → qtp (G ++ [(.TTop, q0, .self)] ++ G') {%x} {%‖G‖} gs := by
    intro G' h; apply q_self' (f := ‖G‖); simp
    exact ⟨rfl, rfl⟩; simp; generalize %x = x at h ⊢; revert x; assumption
    simp; c_extend; simp [sets]
  simp only [excs] at H; obtain ⟨-, _, -, H⟩ := H
  split at H; rotate_right 4
  simp [excs] at H; simp [excs] at H; simp [excs] at H; simp [excs] at H
  next T1 q1 T2 q2 _ => -- TRef
    simp [excs, -bind_pure_comp] at H
    obtain ⟨T1', _, HT1, T2', HT2, rfl, rfl⟩ := H; simp! at C
    have HT1' := polsub_preserves_closedness C.1 (by simp [sets]) (by simp) HT1
    have HT2' := polsub_preserves_closedness C.2.1 (by simp [sets]) (by simp) HT2
    simp [C] at HT1' HT2'; apply s_ref (gr1 := ∅) (gr2 := ∅)
    · apply polsub_subst_comm #0 %‖G‖ at HT1
      rotate_left; simp; omega; simp; generalize HG: G ++ _ = G'
      apply polsub_sound (G:=G') (q0:={✦}) (gs:=gs) at HT1; simpa using HT1
      subst G'; simp; c_subst; c_extend C.1; simp [sets]
      subst G'; rintro _ ⟨_, _, rfl⟩; tauto
    · apply polsub_subst_comm #0 %‖G‖ at HT2
      rotate_left; simp; omega; simp; generalize HG: G ++ _ = G'
      apply polsub_sound (G:=G') (q0:={✦}) (gs:=gs) at HT2; simpa using HT2
      subst G'; simp; c_subst; c_extend C.2.1; simp [sets]
      subst G'; rintro _ ⟨_, _, rfl⟩; tauto
    · apply q_sub; simp [sets, subst]
      apply closedql_bv_tighten; simp [C]; c_extend C.2.2.1
    · simp; generalize HG: G ++ _ = G'
      rw [ql.subst_comm' (x := %x)]; rotate_left; simp; omega; simp
      apply q_subst; subst G'; c_subst; c_extend C.2.2.2.1
      simp [subst]; subst G'; rw [List.append_cons]; tauto
    simp; simp
  next T1 q1 T2 q2 _ => -- TProd
    simp [excs, -bind_pure_comp] at H
    obtain ⟨T1', _, HT1, T2', HT2, rfl, rfl⟩ := H; simp! at C
    have HT1' := polsub_preserves_closedness C.1 (by simp [sets]) (by simp) HT1
    have HT2' := polsub_preserves_closedness C.2.1 (by simp [sets]) (by simp) HT2
    simp [C] at HT1' HT2'; apply s_pair (gr1 := ∅) (gr2 := ∅)
    · apply polsub_subst_comm #0 %‖G‖ at HT1
      rotate_left; simp; omega; simp; generalize HG: G ++ _ = G'
      apply polsub_sound (G:=G') (q0:={✦}) (gs:=gs) at HT1; simpa using HT1
      subst G'; simp; c_subst; c_extend C.1; simp [sets]
      subst G'; rintro _ ⟨_, _, rfl⟩; tauto
    · apply polsub_subst_comm #0 %‖G‖ at HT2
      rotate_left; simp; omega; simp; generalize HG: G ++ _ = G'
      apply polsub_sound (G:=G') (q0:={✦}) (gs:=gs) at HT2; simpa using HT2
      subst G'; simp; c_subst; c_extend C.2.1; simp [sets]
      subst G'; rintro _ ⟨_, _, rfl⟩; tauto
    · simp; generalize HG: G ++ _ = G'
      rw [ql.subst_comm' (x := %x)]; rotate_left; simp; omega; simp
      apply q_subst; subst G'; c_subst; c_extend C.2.2.1
      simp [subst]; subst G'; rw [List.append_cons]; tauto
    · simp; generalize HG: G ++ _ = G'
      rw [ql.subst_comm' (x := %x)]; rotate_left; simp; omega; simp
      apply q_subst; subst G'; c_subst; c_extend C.2.2.2.1
      simp [subst]; subst G'; rw [List.append_cons]; tauto
    simp; simp
  next T1 q1 T2 q2 _ => -- TList
    simp [excs, -bind_pure_comp] at H; obtain ⟨T1', HT1, rfl, rfl⟩ := H; simp! at C
    have HT1' := polsub_preserves_closedness C.1 (by simp [sets]) (by simp) HT1
    simp [C] at HT1'; apply s_list (gr := ∅)
    · apply polsub_subst_comm #0 %‖G‖ at HT1
      rotate_left; simp; omega; simp; generalize HG: G ++ _ = G'
      apply polsub_sound (G:=G') (q0:={✦}) (gs:=gs) at HT1; simpa using HT1
      subst G'; simp; c_subst; c_extend C.1; simp [sets]
      subst G'; rintro _ ⟨_, _, rfl⟩; tauto
    simp
  next T1 q1 T2 q2 _ => -- TFun
    simp [excs, -bind_pure_comp] at H
    obtain ⟨T1', _, HT1, T2', HT2, rfl, rfl⟩ := H; simp! at C
    have HT1' := polsub_preserves_closedness C.1 (by simp [sets]) (by simp) HT1
    have HT2' := polsub_preserves_closedness C.2.1 (by simp [sets]) (by simp) HT2
    simp [C] at HT1' HT2'; apply s_fun (gr1 := ∅) (gr2 := ∅)
    · apply polsub_subst_comm #0 %‖G‖ at HT1
      rotate_left; simp; omega; simp; generalize HG: G ++ _ = G'
      apply polsub_sound (G:=G') (q0:={✦}) (gs:=gs) at HT1; simpa using HT1
      subst G'; simp; c_subst; c_extend C.1; simp [sets]
      subst G'; rintro _ ⟨_, _, rfl⟩; tauto
    · right; apply q_sub; simp [sets, subst]; clear *-; tauto
      simp; c_subst; c_extend C.2.2.1
    · apply polsub_subst_comm #1 %(‖G‖+1) at HT2
      apply polsub_subst_comm #0 %‖G‖ at HT2
      rotate_left; simp [subst]; omega; simp [instSubstId]; simp; omega; simp; simp
      generalize HG: G ++ _ = G'; apply polsub_sound (G:=G') (q0:={✦}) (gs:=gs) at HT2
      simpa using HT2; subst G'; simp; c_subst; c_extend C.2.1; simp [sets]
      subst G'; rintro _ ⟨_, _, rfl⟩; simp; rw [List.append_cons]; tauto
    · simp; generalize HG: G ++ _ = G'
      rw [ql.subst_comm (x2 := %x), ql.subst_comm' (x := %x)]
      rotate_left; simp; omega; simp; simp; omega; simp; simp
      apply q_subst; subst G'; c_subst; c_extend C.2.2.2.1
      simp [subst]; subst G'; rw [List.append_cons]; tauto
    simp; simp; simp
  next T1 q1 T2 q2 _ => -- TAll
    simp [excs, -bind_pure_comp] at H
    obtain ⟨T1', _, HT1, T2', HT2, rfl, rfl⟩ := H; simp! at C
    have HT1' := polsub_preserves_closedness C.1 (by simp [sets]) (by simp) HT1
    have HT2' := polsub_preserves_closedness C.2.1 (by simp [sets]) (by simp) HT2
    simp [C] at HT1' HT2'; apply s_all (gr2 := ∅)
    · apply polsub_subst_comm #0 %‖G‖ at HT1
      rotate_left; simp; omega; simp; generalize HG: G ++ _ = G'
      apply polsub_sound (G:=G') (q0:={✦}) (gs:=gs) at HT1; simpa using HT1
      subst G'; simp; c_subst; c_extend C.1; simp [sets]
      subst G'; rintro _ ⟨_, _, rfl⟩; tauto
    · right; apply q_sub; simp [sets, subst]; clear *-; tauto
      simp; c_subst; c_extend C.2.2.1
    · apply polsub_subst_comm #1 %(‖G‖+1) at HT2
      apply polsub_subst_comm #0 %‖G‖ at HT2
      rotate_left; simp [subst]; omega; simp [instSubstId]; simp; omega; simp; simp
      generalize HG: G ++ _ = G'; apply polsub_sound (G:=G') (q0:={✦}) (gs:=gs) at HT2
      simpa using HT2; subst G'; simp; c_subst; c_extend C.2.1; simp [sets]
      subst G'; rintro _ ⟨_, _, rfl⟩; simp; rw [List.append_cons]; tauto
    · simp; generalize HG: G ++ _ = G'
      rw [ql.subst_comm (x2 := %x), ql.subst_comm' (x := %x)]
      rotate_left; simp; omega; simp; simp; omega; simp; simp
      apply q_subst; subst G'; c_subst; c_extend C.2.2.2.1
      simp [subst]; subst G'; rw [List.append_cons]; tauto
    simp

def avoid_fg_example: M Unit := do
  -- [x: Ref[Unit]^✦] ⊢ f() => (g() => Ref[Unit]^x)^x
  let G: tenv := [(.TRef1 .TUnit ∅, {✦}, .var)]
  let T := ty.TFun .TUnit ∅ (.TFun .TUnit ∅ (.TRef1 .TUnit ∅) {%0}) {%0}
  -- avoid using f: f() => (g() => Ref[Unit]^f)^f
  let T1 := ty.TFun .TUnit ∅ (.TFun .TUnit ∅ (.TRef1 .TUnit ∅) {#2}) {#0}
  let (T', gr) ← avoid T %0
  qassert (T' = T1 ∧ gr = {%0}) "not true"
  let (gr, _) ← check_stp G {✦} T T1 ∅
  qassert (gr = {%0}) "not true"
  -- avoid using g: f() => (g() => Ref[Unit]^g)^f
  let T2 := ty.TFun .TUnit ∅ (.TFun .TUnit ∅ (.TRef1 .TUnit ∅) {#0}) {#0}
  let (gr, _) ← check_stp G {✦} T T2 ∅
  qassert (gr = {%0}) "not true"
  let (gr, _) ← check_stp G {✦} T1 T2 ∅
  qassert (gr = ∅) "not true"

#eval avoid_fg_example

lemma avoid_app_sound_gen2:
  closed_ty 2 n T2 →
  ‖G‖ = n + 2 →
  occurs .no_contravariant T2 #0 →
  avoid_app T2 qf qx σ1 = .ok (T2', gr) σ2 →
  let gr' := [#0 ↦ %n] [#1 ↦ %(n+1)] gr
  gr ⊆ {#0, #1} ∧ gr' ⊆ {%n, %(n+1)} ∧
    closed_ty 2 n T2' ∧
    (✦ ∈ qf → occurs .noneq T2' #0) ∧
    (✦ ∈ qx → occurs .noneq T2' #1) ∧
    occurs .no_contravariant T2' #0 ∧
    stp G ([#0 ↦ %n] [#1 ↦ %(n+1)] T2) {✦} ([#0 ↦ %n] [#1 ↦ %(n+1)] T2') ({✦} ∪ gr') gs :=
by
  intro Ct2 Hn OC h gr'; simp only [avoid_app, excs] at h
  obtain ⟨⟨T2a, gr2a⟩, _, h1, ⟨T2b, gr2b⟩, _, h2, h, rfl⟩ := h
  simp at h2 h1 h; obtain ⟨rfl, rfl⟩ := h
  have h1a: closed_ty 2 n T2a ∧ gr2a ⊆ {#1} ∧
      (✦ ∈ qx → occurs .noneq T2a #1) ∧
      occurs .no_contravariant T2a #0 := by
    split at h1; apply avoid_preserves_closedness Ct2 at h1; tauto; simp
    simp [excs] at h1; obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h1; simp; tauto
  obtain ⟨Ct2a, hg2a, _, _⟩ := h1a
  have h2a: closed_ty 2 n T2b ∧ gr2b ⊆ {#0} ∧
      (✦ ∈ qx → occurs .noneq T2b #1) ∧
      (✦ ∈ qf → occurs .noneq T2b #0) ∧
      occurs .no_contravariant T2b #0 := by
    split at h2; apply avoid_preserves_closedness Ct2a at h2;
    obtain ⟨h2a, h2b, h2c, h2d⟩ := h2; split_ands'
    specialize h2c #1; tauto; tauto; tauto; simp
    simp [excs] at h2; obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h2; simp; tauto
  obtain ⟨Ct2b, hg2b, _, _, _⟩ := h2a
  have: gr2a∪gr2b ⊆ {#0,#1} := by trans ?_ ∪ ?_; gcongr; assumption'; simp [sets]
  have: gr'⊆{%n,%(n+1)} := by clear *- hg2a hg2b; aesop (add simp subst, simp sets)
  split_ands'; have: closed_ql true 0 ‖G‖ ({✦} ∪ gr') := by
    apply Finset.union_subset; simp; trans; assumption; simp [sets]; omega
  apply s_trans (q2 := {✦} ∪ gr'); swap
  · apply s_refl; apply q_sub; simp; assumption
  · c_subst; c_extend; omega; omega; omega
  apply s_trans (T2 := [#0 ↦ %n] [#1 ↦ %(n+1)] T2a) (q2 := {✦} ∪ gr')
  · simp [Hn]; c_subst; c_extend;
  split at h1
  · apply avoid_subst_comm #1 %(n+1) at h1; rotate_left; simp; simp; c_free;
    apply avoid_subst_comm #0 %n at h1; conv at h1 => enter [1,2]; simp [subst]
    rotate_left; simp [subst]; simp; simp [subst]
    apply avoid_sound (G := G) at h1; apply h1
    clear *- hg2a; aesop (add simp subst, simp sets)
    simp [Hn]; c_subst; c_extend; assumption
  · simp [excs] at h1; obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h1
    apply s_refl; apply q_sub; simp; assumption
  split at h2
  · apply avoid_subst_comm #1 %(n+1) at h2; conv at h2 => enter [1,2]; simp [subst]
    rotate_left; simp; simp
    apply avoid_subst_comm #0 %n at h2; conv at h2 => enter [1,2]; simp [subst]
    rotate_left; simp; simp; c_free;
    apply avoid_sound (G := G) at h2; apply h2
    clear *- hg2b; aesop (add simp subst, simp sets)
    simp [Hn]; c_subst; c_extend; assumption
  · simp [excs] at h2; obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h2
    apply s_refl; apply q_sub; simp; assumption

lemma avoid_app_sound_fun:
  has_type G p t (.TFun T1 q1 T2 q2) qf gs →
  avoid_app T2 qf qx σ1 = .ok (T2', gr) σ2 →
  has_type G p t (.TFun T1 q1 T2' (q2 ∪ gr)) qf gs ∧
    (✦ ∈ qf → occurs .noneq T2' #0) ∧
    (✦ ∈ qx → occurs .noneq T2' #1) :=
by
  intro C h; obtain ⟨_, Ct, _⟩ := hast_closed C; simp! at Ct
  let G2 := (G ++ [(.TTop, qf, .self), ([#0 ↦ %‖G‖] T1, [#0 ↦ %‖G‖] q1, .var)])
  casesm* _ ∧ _; apply avoid_app_sound_gen2 (n := ‖G‖) (G := G2) (gs := gs) at h
  assumption'; swap; simp [G2]; extract_lets at h; rename_i gr'; split_ands''
  have: closed_ql true 2 ‖G‖ (q2 ∪ gr) := by
    apply Finset.union_subset; assumption; trans; assumption; simp [sets]
  apply t_sub; assumption'; eapply s_fun (gr1 := ∅) (gr2 := gr')
  · apply s_refl; apply q_sub; simp; simp [sets]
  · right; simp; apply q_sub; simp; simp; c_subst; c_extend;
  · simp; assumption
  · apply q_sub; clear *-; aesop (add simp subst, simp sets)
    simp; c_subst; c_extend;
  simp; trans; assumption; simp; simp; simp!; split_ands'

lemma avoid_app_sound_all:
  has_type G p t (.TAll T1 q1 T2 q2) qf gs →
  avoid_app T2 qf qx σ1 = .ok (T2', gr) σ2 →
  has_type G p t (.TAll T1 q1 T2' (q2 ∪ gr)) qf gs ∧
    (✦ ∈ qf → occurs .noneq T2' #0) ∧
    (✦ ∈ qx → occurs .noneq T2' #1) :=
by
  intro C h; obtain ⟨_, Ct, _⟩ := hast_closed C; simp! at Ct
  let G2 := (G ++ [(.TTop, qf, .self), ([#0 ↦ %‖G‖] T1, [#0 ↦ %‖G‖] q1, .tvar)])
  casesm* _ ∧ _; apply avoid_app_sound_gen2 (n := ‖G‖) (G := G2) (gs := gs) at h
  assumption'; swap; simp [G2]; extract_lets at h; rename_i gr'; split_ands''
  have: closed_ql true 2 ‖G‖ (q2 ∪ gr) := by
    apply Finset.union_subset; assumption; trans; assumption; simp [sets]
  apply t_sub; assumption'; eapply s_all (gr2 := gr')
  · apply s_refl; apply q_sub; simp; simp [sets]
  · right; simp; apply q_sub; simp; simp; c_subst; c_extend;
  · simp; assumption
  · apply q_sub; clear *-; aesop (add simp subst, simp sets)
    simp; c_subst; c_extend;
  trans; assumption; simp; simp!; split_ands'

lemma avoid_app_sound_gen1:
  closed_ty 1 n T2 →
  ‖G‖ = n + 1 →
  occurs .no_contravariant T2 #0 →
  avoid_app T2 qf ∅ σ1 = .ok (T2', gr) σ2 →
  let gr' := [#0 ↦ %n] gr
  gr ⊆ {#0} ∧ gr' ⊆ {%n} ∧
    closed_ty 1 n T2' ∧
    (✦ ∈ qf → occurs .noneq T2' #0) ∧
    occurs .no_contravariant T2' #0 ∧
    stp G ([#0 ↦ %n] T2) {✦} ([#0 ↦ %n] T2') ({✦} ∪ gr') gs :=
by
  intro Ct2 Hn OC h gr'; simp only [avoid_app, excs] at h
  obtain ⟨⟨T2a, gr2a⟩, _, h1, ⟨T2b, gr2b⟩, _, h2, h, rfl⟩ := h
  simp at h2 h1 h; obtain ⟨rfl, rfl⟩ := h
  simp [excs] at h1; obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h1
  have h2a: closed_ty 1 n T2b ∧ gr2b ⊆ {#0} ∧
      (✦ ∈ qf → occurs .noneq T2b #0) ∧
      occurs .no_contravariant T2b #0 := by
    split at h2; apply avoid_preserves_closedness Ct2 at h2;
    obtain ⟨h2a, h2b, h2c, h2d⟩ := h2; split_ands'
    specialize h2c #0; tauto; tauto; tauto; simp
    simp [excs] at h2; obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h2; simp; tauto
  obtain ⟨Ct2b, hg2b, _, _⟩ := h2a
  have: gr' ⊆ {%n} := by clear *- hg2b; aesop
  split_ands'; simpa only [Finset.empty_union]
  have: closed_ql true 0 ‖G‖ ({✦} ∪ gr') := by
    apply Finset.union_subset; simp; trans; assumption; simp [sets]; omega
  apply s_trans (q2 := {✦} ∪ gr'); swap
  · apply s_refl; apply q_sub; simp; assumption
  · c_subst; c_extend; omega; omega
  split at h2
  · apply avoid_subst_comm #0 %n at h2; conv at h2 => enter [1,2]; simp [subst]
    rotate_left; simp; simp; c_free;
    apply avoid_sound (G := G) at h2; apply h2; simp [gr']
    c_subst; c_extend; omega; omega; assumption
  · simp [excs] at h2; obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h2
    apply s_refl; apply q_sub; simp; assumption

lemma avoid_app_sound_ref:
  has_type G p t (.TRef2 T1 q1 T2 q2) qf gs →
  avoid_app T2 qf ∅ σ1 = .ok (T2', gr) σ2 →
  has_type G p t (.TRef2 T1 q1 T2' (q2 ∪ gr)) qf gs ∧
    (✦ ∈ qf → occurs .noneq T2' #0) ∧ gr ⊆ {#0} :=
by
  intro C h; obtain ⟨_, Ct, _⟩ := hast_closed C; simp! at Ct
  let G2 := (G ++ [(.TTop, qf, .self)])
  casesm* _ ∧ _; apply avoid_app_sound_gen1 (n := ‖G‖) (G := G2) (gs := gs) at h
  assumption'; swap; simp [G2]; extract_lets at h; rename_i gr'; split_ands''
  have: closed_ql false 1 ‖G‖ (q2 ∪ gr) := by
    apply Finset.union_subset; assumption; trans; assumption; simp [sets]
  apply t_sub; assumption'; eapply s_ref (gr1 := ∅) (gr2 := gr')
  · apply s_refl; apply q_sub; simp; simp [sets]
  · assumption
  · simp; apply q_sub; simp; apply closedql_bv_tighten; assumption; c_extend;
  · apply q_sub; clear *-; aesop (add simp subst, simp sets)
    simp; c_subst; c_extend;
  simp; trans; assumption; simp; simp!; split_ands'

lemma avoid_app_sound_fst:
  has_type G p t (.TProd T1 q1 T2 q2) qf gs →
  avoid_app T1 qf ∅ σ1 = .ok (T1', gr) σ2 →
  has_type G p t (.TProd T1' (q1 ∪ gr) T2 q2) qf gs ∧
    (✦ ∈ qf → occurs .noneq T1' #0) ∧ gr ⊆ {#0} :=
by
  intro C h; obtain ⟨_, Ct, _⟩ := hast_closed C; simp! at Ct
  let G2 := (G ++ [(.TTop, qf, .self)])
  casesm* _ ∧ _; apply avoid_app_sound_gen1 (n := ‖G‖) (G := G2) (gs := gs) at h
  assumption'; swap; simp [G2]; extract_lets at h; rename_i gr'; split_ands''
  have: closed_ql false 1 ‖G‖ (q1 ∪ gr) := by
    apply Finset.union_subset; assumption; trans; assumption; simp [sets]
  apply t_sub; assumption'; eapply s_pair (gr1 := gr') (gr2 := ∅)
  · assumption
  · apply s_refl; apply q_sub; simp; simp [sets]
  · apply q_sub; clear *-; aesop (add simp subst, simp sets)
    simp; c_subst; c_extend;
  · simp; apply q_sub; simp; c_subst; c_extend;
  trans; assumption; simp; simp; simp!; split_ands'

lemma avoid_app_sound_snd:
  has_type G p t (.TProd T1 q1 T2 q2) qf gs →
  avoid_app T2 qf ∅ σ1 = .ok (T2', gr) σ2 →
  has_type G p t (.TProd T1 q1 T2' (q2 ∪ gr)) qf gs ∧
    (✦ ∈ qf → occurs .noneq T2' #0) ∧ gr ⊆ {#0} :=
by
  intro C h; obtain ⟨_, Ct, _⟩ := hast_closed C; simp! at Ct
  let G2 := (G ++ [(.TTop, qf, .self)])
  casesm* _ ∧ _; apply avoid_app_sound_gen1 (n := ‖G‖) (G := G2) (gs := gs) at h
  assumption'; swap; simp [G2]; extract_lets at h; rename_i gr'; split_ands''
  have: closed_ql false 1 ‖G‖ (q2 ∪ gr) := by
    apply Finset.union_subset; assumption; trans; assumption; simp [sets]
  apply t_sub; assumption'; eapply s_pair (gr1 := ∅) (gr2 := gr')
  · apply s_refl; apply q_sub; simp; simp [sets]
  · assumption
  · simp; apply q_sub; simp; c_subst; c_extend;
  · apply q_sub; clear *-; aesop (add simp subst, simp sets)
    simp; c_subst; c_extend;
  simp; trans; assumption; simp; simp!; split_ands'

-- type variable exposure

lemma texposure_sound (tl: telescope G) (C: closed_ty 0 ‖G‖ t) (C0: closed_ql true 0 ‖G‖ q0):
  texposure G t = t' →
  closed_ty 0 ‖G‖ t' ∧ stp G t q0 t' q0 gs :=
by
  intro h; generalize hG: G = G0 at h C; rw [←hG]
  replace hG: G0 <+: G := by simp [hG]
  induction G0, t using texposure.induct generalizing t'
  next G1 x _ _ h1 h2 ih1 =>
    conv at h => simp [texposure]; rw [h1]; simp
    obtain ⟨G1', rfl⟩ := hG; apply telescope_shrink at tl; replace tl := (tl h1).1
    specialize ih1 h _ _; c_extend; omega
    exists (G1.drop x) ++ G1'; simp [←List.append_assoc]; split_ands''
    apply s_trans; rotate_left 2; simpa; c_extend; omega
    apply s_tvar; simpa [List.getElem?_append_left, h2] using h1
  next =>
    simp [texposure] at h; subst t'; obtain ⟨G', rfl⟩ := hG
    split_ands; c_extend; apply s_refl; apply q_sub; simp; assumption
  next =>
    simp [texposure] at h; subst t'; obtain ⟨G', rfl⟩ := hG
    split_ands; c_extend; apply s_refl; apply q_sub; simp; assumption

-- bidirectional typing

@[simp]
def tinfer_spec t := ∀ G gs G' p T q σ1 σ2,
  telescope G → gs ⊆ Finset.range ‖G‖ →
  tinfer' G gs t σ1 = .ok (G', p, T, q) σ2 →
  ctx_grow G G' gs ∧ closed_ql false 0 ‖G‖ p ∧ has_type G' p t T q gs

@[simp]
def tcheck_spec t := ∀ G gs T G' p q σ1 σ2,
  telescope G → gs ⊆ Finset.range ‖G‖ →
  closed_ty 0 ‖G‖ T →
  tcheck' G gs t T σ1 = .ok (G', p, q) σ2 →
  ctx_grow G G' gs ∧ closed_ql false 0 ‖G‖ p ∧ has_type G' p t T q gs

@[simp]
def tcheckq_spec t := ∀ G gs T q G' p σ1 σ2,
  telescope G → gs ⊆ Finset.range ‖G‖ →
  closed_ty 0 ‖G‖ T →
  closed_ql true 0 ‖G‖ q →
  tcheckq G gs t T q σ1 = .ok (G', p) σ2 →
  ctx_grow G G' gs ∧ closed_ql false 0 ‖G‖ p ∧ has_type G' p t T q gs

@[simp]
def tinfer2_spec t := ∀ G gs G' p T q σ1 σ2,
  telescope G → gs ⊆ Finset.range ‖G‖ →
  tinfer2 G gs t σ1 = .ok (G', p, T, q) σ2 →
  ctx_grow G G' gs ∧ closed_ql false 0 ‖G‖ p ∧ has_type G' p t T q gs

@[simp]
def tinferexp_spec t := ∀ G gs G' p T q σ1 σ2,
  telescope G → gs ⊆ Finset.range ‖G‖ →
  tinferexp G gs t σ1 = .ok (G', p, T, q) σ2 →
  ctx_grow G G' gs ∧ closed_ql false 0 ‖G‖ p ∧ has_type G' p t T q gs

@[simp]
def tinferabs_spec t := ∀ G gs T1 q1 bn G' T2 q2 qf σ1 σ2,
  telescope G → gs ⊆ Finset.range ‖G‖ → bn ≠ .self →
  closed_ty 1 ‖G‖ T1 → closed_ql true 1 ‖G‖ q1 →
  occurs .no_covariant T1 #0 → (#0 ∈ q1 → ✦ ∈ q1) →
  tinferabs G gs T1 q1 bn t σ1 = .ok (G', qf, T2, q2) σ2 →
    ctx_grow G G' gs ∧ closed_ql false 0 ‖G‖ qf ∧
    match bn with
    | .var => has_type G' qf (.tabs none t) (.TFun T1 q1 T2 q2) qf gs
    | .tvar => has_type G' qf (.ttabs none t) (.TAll T1 q1 T2 q2) qf gs
    | _ => True

@[simp]
def tcheckabs_spec t := ∀ G gs T1 q1 bn T2 q2 G' qf σ1 σ2,
  telescope G → gs ⊆ Finset.range ‖G‖ → bn ≠ .self →
  closed_ty 1 ‖G‖ T1 → closed_ql true 1 ‖G‖ q1 →
  closed_ty 2 ‖G‖ T2 → closed_ql true 2 ‖G‖ q2 →
  occurs .no_covariant T1 #0 → (#0 ∈ q1 → ✦ ∈ q1) → occurs .no_contravariant T2 #0 →
  tcheckabs G gs T1 q1 bn t T2 q2 σ1 = .ok (G', qf) σ2 →
    ctx_grow G G' gs ∧ closed_ql false 0 ‖G‖ qf ∧
    match bn with
    | .var => has_type G' qf (.tabs none t) (.TFun T1 q1 T2 q2) qf gs
    | .tvar => has_type G' qf (.ttabs none t) (.TAll T1 q1 T2 q2) qf gs
    | _ => True

theorem tinfer_sound
  (IHC: ∀ t', sizeOf t' < sizeOf t → tcheck_spec t')
  (IHQ: ∀ t', sizeOf t' < sizeOf t → tcheckq_spec t')
  (IHF: tinfer2_spec t)
  (IHE: ∀ t', sizeOf t' < sizeOf t → tinferexp_spec t')
  (IHI: ∀ t', sizeOf t' < sizeOf t → tinfer_spec t'):
  tinfer_spec t :=
by
  simp; introv tl hgs h; simp [tinfer', excs] at h
  fun_cases tinfer G gs t <;> simp only [tinfer, excs] at h
  next => -- unit
    simp [and_assoc] at h; obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
    simp [ctx_grow]; apply t_unit
  next x => -- var
    obtain ⟨⟨_, _, _⟩, _, ⟨Gx, rfl⟩, h⟩ := h; simp at h
    obtain ⟨rfl, ⟨rfl, rfl, rfl, rfl⟩, rfl⟩ := h; simp [ctx_grow]
    have := List.getElem?_eq_some' Gx; simp [sets, this]
    apply t_var; assumption'; simp; simp; specialize tl Gx; c_extend tl.1; omega
  next => -- nat
    simp [and_assoc] at h; obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
    simp [sets, ctx_grow]; apply t_nat
  next => -- add
    obtain ⟨⟨G1, p1, q1⟩, _, h1, ⟨G2, p2, q2⟩, _, h2, h⟩ := h
    simp [and_assoc] at h h2; obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
    apply IHC at h1; rotate_left; simp; omega; assumption'; simp!
    apply IHC at h2; rotate_left; simp; omega; apply h1.1.on_telescope tl
    rwa [←h1.1.1]; simp!; split_ands; apply h1.1.trans h2.1
    apply Finset.union_subset h1.2.1 (h1.1.1 ▸ h2.2.1)
    apply t_add; apply h2.1.on_hastype; apply h1.2.2.filter_widen; simp
    apply h2.2.2.filter_widen; simp
  next => -- mul
    obtain ⟨⟨G1, p1, q1⟩, _, h1, ⟨G2, p2, q2⟩, _, h2, h⟩ := h
    simp [and_assoc] at h h2; obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
    apply IHC at h1; rotate_left; simp; omega; assumption'; simp!
    apply IHC at h2; rotate_left; simp; omega; apply h1.1.on_telescope tl
    rwa [←h1.1.1]; simp!; split_ands; apply h1.1.trans h2.1
    apply Finset.union_subset h1.2.1 (h1.1.1 ▸ h2.2.1)
    apply t_mul; apply h2.1.on_hastype; apply h1.2.2.filter_widen; simp
    apply h2.2.2.filter_widen; simp
  next => -- ref
    obtain ⟨⟨G', p, T, q⟩, _, h1, h⟩ := h; simp at h
    obtain ⟨_, ⟨rfl, rfl, rfl, rfl⟩, rfl⟩ := h
    apply IHI at h1; split_ands''; apply t_ref; assumption'; simp
  next => -- get
    obtain ⟨⟨G', p, T, q⟩, _, h1, h⟩ := h; simp only [excs] at h
    split at h <;> simp only [excs] at h; rename_i T2 q2; simp at h
    obtain ⟨T2', gr, h3, rfl, rfl, rfl, rfl⟩ := h
    apply IHE at h1; assumption'; swap; simp
    obtain ⟨cg, _, h2⟩ := h1; have C := (hast_closed h2).2.1
    apply avoid_app_sound_ref at h2; specialize h2 h3; simp [←cg.1] at C
    obtain ⟨h2, _, h3⟩ := h2; split_ands'
    · apply Finset.union_subset; assumption
      apply closedql_tighten; simp! at C; simp [C]
    · eapply t_get; assumption'; apply h2.filter_widen; simp
      clear *- h3; aesop (add simp sets)
  next => -- put
    obtain ⟨⟨G', p1, T, q⟩, _, h1, h⟩ := h; simp only at h
    split at h <;> simp only [excs] at h; rename_i T1 q1 _ _
    obtain ⟨T1', _, h4, ⟨G'', p2⟩, _, h3, h⟩ := h
    simp at h; obtain ⟨⟨rfl, rfl, rfl, rfl⟩, rfl⟩ := h
    apply IHE at h1; assumption'; swap; simp; omega
    have tl' := h1.1.on_telescope tl; have h2 := h1.2.2
    simp [h1.1.1] at hgs; apply unpack_argself_sound_ref at h2
    specialize h2 h4 hgs; obtain ⟨_, h2⟩ := h2; have C := (hast_closed h2).2.1
    apply IHQ at h3; assumption'; rotate_left; simp; omega
    obtain ⟨-,-,_,-,_,-⟩ := C; apply closedql_bv_tighten; assumption; c_extend;
    split_ands; apply h1.1.trans h3.1
    apply Finset.union_subset h1.2.1 (h1.1.1 ▸ h3.2.1)
    apply t_put; apply h3.1.on_hastype; apply h2.filter_widen; simp
    apply h3.2.2.filter_widen; simp
  next => -- pair
    obtain ⟨⟨G1, p1, T1, q1⟩, _, h1, ⟨G2, p2, T2, q2⟩, _, h2, h⟩ := h
    simp [and_assoc] at h2 h; obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
    apply IHI at h1; rotate_left; simp!; omega; assumption'
    apply IHI at h2; rotate_left; simp!; omega; apply h1.1.on_telescope tl
    rwa [←h1.1.1]; split_ands; apply h1.1.trans h2.1
    apply Finset.union_subset h1.2.1 (h1.1.1 ▸ h2.2.1)
    apply t_pair; apply h2.1.on_hastype; apply h1.2.2.filter_widen; simp
    apply h2.2.2.filter_widen; simp
  next => -- fst
    obtain ⟨⟨G1, p1, T, q⟩, _, h1, h⟩ := h; dsimp only at h
    split at h <;> simp only [excs] at h; obtain ⟨⟨T1', gr⟩, _, h2, h⟩ := h
    simp [and_assoc] at h; obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
    apply IHE at h1; rotate_left; simp!; omega; assumption'
    obtain ⟨cg, _, h1⟩ := h1; apply avoid_app_sound_fst h1 at h2
    replace h1 := hast_closed h1; have := cg.1 ▸ h1.2.1.2.2.1
    split_ands'; apply Finset.union_subset; assumption
    apply closedql_tighten; assumption
    apply t_fst; apply h2.1.filter_widen; simp
    have := h2.2.2; clear *- this; aesop (add simp sets); exact h2.2.1
  next => -- snd
    obtain ⟨⟨G1, p1, T, q⟩, _, h1, h⟩ := h; dsimp only at h
    split at h <;> simp only [excs] at h; obtain ⟨⟨T1', gr⟩, _, h2, h⟩ := h
    simp [and_assoc] at h; obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
    apply IHE at h1; rotate_left; simp!; omega; assumption'
    obtain ⟨cg, _, h1⟩ := h1; apply avoid_app_sound_snd h1 at h2
    replace h1 := hast_closed h1; have := cg.1 ▸ h1.2.1.2.2.2.1
    split_ands'; apply Finset.union_subset; assumption
    apply closedql_tighten; assumption
    apply t_snd; apply h2.1.filter_widen; simp
    have := h2.2.2; clear *- this; aesop (add simp sets); exact h2.2.1
  next => -- cons
    obtain ⟨⟨G1, p1, T1, q1⟩, _, h1, ⟨G2, p2, q2⟩, _, h2, h⟩ := h
    simp at h2 h; obtain ⟨⟨rfl, rfl, rfl, rfl⟩, rfl⟩ := h
    apply IHI at h1; rotate_left; simp; omega; assumption'
    apply IHC at h2; rotate_left; simp; omega; exact h1.1.on_telescope tl
    rwa [←h1.1.1]; have := (hast_closed h1.2.2).2.1; constructor; c_extend; c_free;
    obtain ⟨h1a, h1b, h1c⟩ := h1; obtain ⟨h2a, h2b, h2c⟩ := h2; split_ands
    exact h1a.trans h2a; apply Finset.union_subset; assumption; rwa [h1a.1]
    apply t_cons; apply h2a.on_hastype; apply h1c.filter_widen; simp
    apply h2c.filter_widen; simp
  next => -- fold
    obtain ⟨⟨G1,p1,T1,q1⟩, _, h1, ⟨G2,p2,T2,q2⟩, _, h2, -, _, ⟨h3, rfl⟩, h⟩ := h
    dsimp at h2 h3 h; generalize h4: unpack_self T1 q1 = T1' at h
    split at h <;> simp only [excs] at h; obtain ⟨⟨G3, p3⟩, _, h5, h⟩ := h
    simp at h; obtain ⟨⟨h6, h7, rfl, rfl⟩, rfl⟩ := h
    apply IHE at h1; rotate_left; simp; omega; assumption'; obtain ⟨cg1, cp1, h1⟩ := h1
    replace hgs := cg1.1 ▸ hgs; replace tl := cg1.on_telescope tl
    replace h4 := unpack_self_sound_list h1 h4 hgs h3.1; clear h1; obtain ⟨ct', h1⟩ := h4
    apply IHI at h2; rotate_left; simp; omega; assumption'; obtain ⟨cg2, cp2, h2⟩ := h2
    have C1 := And.intro ct' (hast_closed h1).2.2; have C2 := (hast_closed h2).2
    clear ct'; replace hgs := cg2.1 ▸ hgs; replace tl := cg2.on_telescope tl
    rw [←List.singleton_append, ←List.append_assoc] at h5
    apply IHQ at h5; rotate_left; simp; omega
    · (repeat' apply telescope_extend); assumption'
      c_extend C2.1; c_extend C2.2; exact cg2.1 ▸ C1.1; exact cg2.1 ▸ C1.2
    trans; assumption; simp; c_extend C2.1; c_extend C2.2
    have := h5.1.inversion; simp at this; obtain ⟨G3, rfl⟩ := this
    have := (h5.1.shrink rfl).inversion; simp at this; obtain ⟨G3, rfl⟩ := this
    cases h3; simp at h5; obtain ⟨cg3, cp3, h3⟩ := h5; replace cg3 := cg3.shrink rfl
    have cg := cg1.trans (cg2.trans cg3); simp [cg.1] at h6; subst G' p; split_ands'
    · (repeat' apply Finset.union_subset); apply cp1; apply cg1.1 ▸ cp2
      rw [Finset.sdiff_insert, ←Finset.sdiff_singleton_eq_erase]
      (repeat apply closedql_tighten); apply cg1.1 ▸ cg2.1 ▸ cp3
    apply t_fold
    · apply (cg2.trans cg3).on_hastype; apply h1.filter_widen; simp
    · apply cg3.on_hastype; apply h2.filter_widen; clear *-; aesop (add simp sets)
    · apply h3.filter_widen; have := cg.1; clear *- this; aesop (add simp sets)
    assumption'; apply cg3.1 ▸ cg2.1 ▸ C1.1
  next => -- anno
    obtain ⟨-, _, ⟨⟨_, _⟩, rfl⟩, ⟨G', p⟩, _, h1, h⟩ := h
    simp at h; obtain ⟨⟨rfl, rfl, rfl, rfl⟩, rfl⟩ := h
    apply IHQ at h1; assumption'; swap; simp; omega
    split_ands''; apply t_asc; assumption
  next => apply IHF; assumption'

theorem tinfer2_sound
  (IHC: ∀ t', sizeOf t' < sizeOf t → tcheck_spec t')
  (IHA: ∀ t', sizeOf t' < sizeOf t → tinferabs_spec t')
  (IHE: ∀ t', sizeOf t' < sizeOf t → tinferexp_spec t')
  (IHI: ∀ t', sizeOf t' < sizeOf t → tinfer_spec t'):
  tinfer2_spec t :=
by
  simp; introv tl hgs h
  fun_cases tinfer2 G gs t <;> simp only [tinfer2, excs] at h
  next => -- abs
    obtain ⟨-, _, ⟨⟨h1, h2, h3a, h3b⟩, rfl⟩, ⟨G', qf, T2, q2⟩, _, h4, h⟩ := h
    simp at h; obtain ⟨⟨rfl, rfl, rfl, rfl⟩, rfl⟩ := h
    apply IHA at h4; assumption'; rotate_left; simp; omega; simp
    have := (hast_closed h4.2.2).2.2
    split_ands; simp [h4]; apply h4.2.1; apply t_absa; apply h4.2.2
  next => -- tabs
    obtain ⟨-, _, ⟨⟨h1, h2, h3a, h3b⟩, rfl⟩, ⟨G', qf, T2, q2⟩, _, h4, h⟩ := h
    simp at h; obtain ⟨⟨rfl, rfl, rfl, rfl⟩, rfl⟩ := h
    apply IHA at h4; assumption'; rotate_left; simp; omega; simp
    have := (hast_closed h4.2.2).2.2
    split_ands; simp [h4]; apply h4.2.1; apply t_tabsa; apply h4.2.2
  next => -- let
    obtain ⟨⟨G1, p1, Tx, qx⟩, _, h1, h⟩ := h; simp at h
    obtain ⟨qf, T2, q2, _, h2, T2', gr, h3, rfl, rfl, rfl, rfl⟩ := h
    apply IHI at h1; assumption'; swap; simp; omega
    have tl1 := h1.1.on_telescope tl; have Cx := hast_closed h1.2.2
    apply IHA at h2; rotate_left; simp; omega; assumption; simpa [←h1.1.1]; simp
    c_extend Cx.2.1; c_extend Cx.2.2; c_free Cx.2.1; intro h; absurd h; c_free Cx.2.2;
    apply avoid_app_sound_fun h2.2.2 at h3
    have Cf := hast_closed h3.1; simp [h1.1.1, h2.1.1] at h1 Cx ⊢; split_ands
    · apply h1.1.trans h2.1
    · repeat' apply Finset.union_subset
      rw [←h2.1.1]; exact h2.2.1; exact h1.2.1
      have := Cf.2.1; simp! at this; replace this := this.2.2.2.1
      trans (((q2 ∪ gr) \ {✦}) \ {#1}) \ {#0}; clear *-; simp [sets]; tauto
      (repeat apply closedql_tighten); exact this
    · eapply t_app; apply h3.1.filter_widen; simp
      apply has_type.filter_widen; apply h2.1.on_hastype h1.2.2
      clear *-; simp [sets]; tauto; right; left; apply q_sub; simp; apply Cx.2.2
      clear *-; simp [sets]; tauto; apply h3.2.1; apply h3.2.2
  next => -- app
    obtain ⟨⟨G1, p, Tf, qf⟩, _, h0, h⟩ := h; simp only at h
    split at h; swap; simp only [excs] at h; rename_i T1 q1 T2 q2
    simp only [excs] at h; obtain ⟨T1', _, h2, ⟨G', p1, qx⟩, _, h3, h⟩ := h
    simp at h; obtain ⟨p2, _, h4, T2', gr, h5, h⟩ := h
    obtain ⟨h, rfl, rfl⟩ := h; rename_i p2' _ _ _ _ _ _ _ _
    apply IHE at h0; assumption'; swap; simp; omega
    replace tl := h0.1.on_telescope tl; have h1 := h0.2.2
    rw [h0.1.1] at hgs; apply unpack_argself_sound_fun h1 at h2; specialize h2 hgs
    obtain ⟨_, h2⟩ := h2; apply avoid_app_sound_fun h2 at h5; clear h1 h2
    have Cf := (hast_closed h5.1).2.1; simp! at Cf
    apply IHC at h3; assumption'; swap; simp; omega; replace tl := h3.1.on_telescope tl
    apply check_app_sound at h4; assumption'; swap; simp [←h3.1.1, Cf]
    have cg := h3.1.trans h4.1
    simp [h0.1.1, h3.1.1] at h0 h3 Cf ⊢; split_ands
    · apply h0.1.trans cg
    · subst p2'; repeat' apply Finset.union_subset
      exact h0.2.1; exact h3.2.1; exact h4.2.1
      trans (((q2 ∪ gr) \ {✦}) \ {#1}) \ {#0}; clear *-; simp [sets]; tauto
      (repeat apply closedql_tighten); simp [Cf]
    · obtain ⟨h5, _, _⟩ := h5; subst p2'
      eapply t_app; apply cg.on_hastype; apply h5.filter_widen; simp
      apply h4.1.on_hastype; apply h3.2.2.filter_widen; simp [sets]; clear *-; tauto
      apply h4.2.2; simp [sets]; clear *-; tauto
      simp [sets]; clear *-; tauto; assumption'
  next => -- tapp
    obtain ⟨-, _, ⟨⟨Ctx, Cqx⟩, rfl⟩, ⟨G1, p, Tf, qf⟩, _, h0, h⟩ := h; simp only at h
    split at h; swap; simp only [excs] at h; rename_i T1 q1 T2 q2
    simp only [excs] at h; obtain ⟨T1', _, h2, ⟨gr, G'⟩, _, h3, h⟩ := h
    simp at h; obtain ⟨rfl, p2, _, h4, T2', gr, h5, h⟩ := h
    obtain ⟨h, rfl, rfl⟩ := h; rename_i p2' _ _ _ _ _ _ _ _
    apply IHE at h0; assumption'; swap; simp; omega
    replace tl := h0.1.on_telescope tl; have h1 := h0.2.2
    rw [h0.1.1] at hgs; apply unpack_argself_sound_all h1 at h2; specialize h2 hgs
    obtain ⟨Ct1', h2⟩ := h2; apply avoid_app_sound_all h2 at h5; clear h1 h2
    have Cf := (hast_closed h5.1).2.1; simp! at Cf
    apply check_stp_sound at h3; assumption'
    specialize h3 (by simp [sets]) (h0.1.1 ▸ Ctx) (by assumption)
    obtain ⟨-, h3⟩ := h3; replace tl := h3.1.on_telescope tl
    apply check_app_sound at h4; assumption'; swap; simp [←h3.1.1, Cf]
    have cg := h3.1.trans h4.1
    simp [h0.1.1, h3.1.1, h4.1.1] at h0 Ctx Ct1' Cqx Cf h4 ⊢; split_ands
    · apply h0.1.trans cg
    · subst p2'; repeat' apply Finset.union_subset
      exact h0.2.1; apply closedql_tighten; assumption; exact h4.2.1
      trans (((q2 ∪ gr) \ {✦}) \ {#1}) \ {#0}; clear *-; simp [sets]; tauto
      (repeat apply closedql_tighten); simp [Cf]
    · obtain ⟨h5, _, _⟩ := h5; subst p2'
      eapply t_tapp; apply cg.on_hastype; apply h5.filter_widen; simp
      exact h4.1.on_stp h3.2; assumption'
      apply h4.2.2; simp [sets]; clear *-; tauto
      simp [sets]; clear *-; tauto; simp [sets]; clear *-; tauto

theorem tinferexp_sound:
  tinfer_spec t →
  tinferexp_spec t :=
by
  dsimp; introv ih tl hgs h; simp [tinferexp, excs, -bind_pure_comp] at h
  obtain ⟨T0, h2, h1⟩ := h; apply ih at h2; assumption'; split_ands''
  rename_i cg _ h2; have := cg.on_telescope tl; have ⟨_, _, _⟩ := hast_closed h2
  apply texposure_sound (q0 := q) (gs := gs) at h1; assumption'
  apply t_sub; assumption; apply h1.2; apply h1.1; assumption

theorem tinferabs_sound:
  tinfer_spec t →
  tinferabs_spec t :=
by
  dsimp; introv ih tl hgs _ Ct1 Cq1 _ _ h; simp only [tinferabs, excs] at h
  obtain ⟨-, _, -, ⟨G2, p2, T2a, q2b⟩, _, h1, T2b, _, h2, h⟩ := h; simp at h2 h
  obtain ⟨_, q, ⟨_, h3⟩, ⟨hG', hqf, rfl, rfl⟩, rfl⟩ := h
  let G1 := G ++ [(.TTop, ∅, .self), ([#0↦%‖G‖]T1, [#0↦%‖G‖]q1, bn)];
  have tl1: telescope G1 := by
    simp [G1]; rw [List.append_cons]
    apply telescope_extend; c_subst; c_extend; c_subst; c_extend;
    apply telescope_extend; simp!; simp [sets]; assumption
  apply ih at h1; assumption'; swap
  aesop (add safe Finset.union_subset, 50% Finset.Subset.trans)
  clear ih; obtain ⟨h1a, h1b, h1c⟩ := h1
  simp at h1a; have := h1a.inversion2 (by assumption)
  simp at this; obtain ⟨G', q', rfl, _⟩ := this; have L := h1a.1
  simp at L; simp [L] at h3 hG'; subst G'
  obtain ⟨rfl, rfl, rfl⟩ := h3; replace h1a := (h1a.shrink rfl).gs_shrink
  have Cqf: closed_ql false 0 ‖G‖ qf := by
    have: ∀ (q: ql) {x y}, q \ {y, x} = (q \ {x}) \ {y} := by
      simp [Finset.sdiff_insert, Finset.sdiff_singleton_eq_erase]
    subst qf; (repeat' apply Finset.union_subset); assumption
    rw [this]; (repeat apply closedql_tighten); aesop
    rw [this]; (repeat apply closedql_tighten); assumption
  rw [L] at Ct1 Cq1 Cqf h2; have: q1 ⊆ qf ∪ {✦, #0} := by aesop (add simp sets)
  let G1 := G' ++ [(.TTop, qf, .self), ([#0↦%‖G‖]T1, [#0↦%‖G‖]q1, bn)]
  replace h1c: has_type G1 p2 t T2a q2b gs := by
    apply has_type.gs_tighten; apply ctx_grow.on_hastype _ h1c; swap; simp
    simp [G1]; apply ctx_grow.set ‖G'‖; simp
    exact ⟨rfl, rfl⟩; simp; rfl; c_extend; simp; intro h; absurd h; c_free;
    subst qf; simp; simp [L]
  have C2 := hast_closed h1c; apply @rm_contravariant_sound G1 _ q2b _ _ _ _ gs at h2
  obtain ⟨h2a, h2b, h2c⟩ := h2; rotate_left; apply C2.2.1; apply C2.2.2; simp [G1, L]
  replace h1c: has_type G1 (qf ∪ {%‖G‖, %(‖G‖+1)}) t T2b q2b gs := by
    apply has_type.filter_widen; apply t_sub; apply h1c; apply h2a; apply h2b
    simp [C2]; subst qf; simp [sets]; clear *-; tauto
  simp [G1, L] at h1c ⊢; clear h2a h2b C2 G1; split_ands'; split
  · change has_type _ _ _ (.TFun' ‖G'‖ T1 q1 T2b q2b) _ _
    apply t_abs'; assumption'; simp
  · change has_type _ _ _ (.TAll' ‖G'‖ T1 q1 T2b q2b) _ _
    apply t_tabs'; assumption'; simp
  simp

theorem tcheck_sound
  (IHA: ∀ t', sizeOf t' < sizeOf t → tcheckabs_spec t')
  (IHI: tinfer_spec t):
  tcheck_spec t :=
by
  simp; introv tl hgs C0 h; simp only [tcheck', excs] at h
  fun_cases tcheck G gs t T <;> simp only [tcheck, excs] at h
  next => -- nil
    simp at h; obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := h
    simp [ctx_grow]; apply t_nil; assumption
  next => -- fun
    simp! at C0; casesm* _ ∧ _; obtain ⟨⟨G', qf⟩, _, h, h1⟩ := h
    simp [and_assoc] at h1; obtain ⟨rfl, rfl, rfl, rfl⟩ := h1
    apply IHA at h; simp at h; assumption'; simp; simp
  next => -- all
    simp! at C0; casesm* _ ∧ _; obtain ⟨⟨G', qf⟩, _, h, h1⟩ := h
    simp [and_assoc] at h1; obtain ⟨rfl, rfl, rfl, rfl⟩ := h1
    apply IHA at h; simp at h; assumption'; simp; simp
  next => -- sub
    obtain ⟨⟨G', p, T', q'⟩, _, h1, h⟩ := h
    apply IHI at h1; assumption'; simp at h; obtain ⟨gr, h2, h⟩ := h
    have C := (hast_closed h1.2.2).2
    apply check_stp_sound at h2; specialize h2 C.2 C.1 _; rwa [← h1.1.1]
    rotate_left; apply h1.1.on_telescope tl; rwa [←h1.1.1]
    obtain ⟨rfl, rfl, rfl⟩ := h; split_ands
    apply h1.1.trans h2.2.1; repeat' apply Finset.union_subset
    exact h1.2.1; rw [h1.1.1]; exact h2.1; apply t_sub
    apply h2.2.1.on_hastype; apply h1.2.2.filter_widen; simp
    exact h2.2.2; simpa [h1.1.1, h2.2.1.1] using C0
    apply Finset.union_subset; trans; apply (hast_closed h1.2.2).1
    all_goals clear *-; simp [sets] at *; tauto

theorem tcheckabs_sound:
  tcheckq_spec t →
  tcheckabs_spec t :=
by
  dsimp; introv ih tl hgs hns Ct1 Cq1 Ct2 Cq2 _ _ _ h; simp only [tcheckabs, excs] at h
  let G1 := G ++ [(.TTop, ∅, .self), ([#0↦%‖G‖]T1, [#0↦%‖G‖]q1, bn)];
  have tl1: telescope G1 := by
    simp [G1]; rw [List.append_cons]
    apply telescope_extend; c_subst; c_extend; c_subst; c_extend;
    apply telescope_extend; simp!; simp [sets]; assumption
  obtain ⟨-, _, -, ⟨G'', p0⟩, _, h1, h⟩ := h; simp at h
  apply ih at h1; assumption'; rotate_left
  · simp; apply Finset.union_subset; trans; assumption; simp; simp
  · simp; c_subst; c_extend;
  · simp; c_subst; c_extend;
  obtain ⟨T, qf, ⟨bn, hg⟩, h, rfl⟩ := h
  have := h1.1.inversion2; simp [hns] at this; obtain ⟨G', qf, rfl, cq1'⟩ := this
  have L := h1.1.1; simp at L; simp [L] at h hg
  obtain ⟨rfl, rfl, rfl⟩ := hg; obtain ⟨rfl, rfl, rfl⟩ := h
  let qf' := qf ∪ p0 \ {%‖G'‖, %(‖G'‖ + 1)} ∪ q1 \ {✦, #0}
  have cqf: closed_ql false 0 ‖G‖ qf' := by
    repeat' apply Finset.union_subset
    assumption; simp [←L]; replace h1 := h1.2.1; clear *- h1
    trans (p0 \ {%(‖G‖+1)}) \ {%‖G‖}; simp [sets]; tauto
    (repeat apply closedql_tighten); simpa using h1
    trans (q1 \ {✦}) \ {#0}; simp [sets]; tauto
    (repeat apply closedql_tighten); assumption
  clear ih; split_ands'
  · apply (h1.1.shrink rfl).gs_shrink
  · simpa [qf'] using cqf
  simp only [L] at h1 Ct1 Cq1 Ct2 Cq2 cqf; obtain ⟨-, _, h1⟩ := h1
  replace h1 := by
    apply ctx_grow.on_hastype; swap; apply h1; apply ctx_grow.set (q' := qf') ‖G'‖
    simp; exact ⟨rfl, rfl⟩; simp; rfl
    c_extend; simp; intro h; absurd h; c_free; simp [qf']; simp
  apply has_type.gs_tighten (gs := gs) at h1; specialize h1 (by simp)
  apply has_type.filter_widen (p' := qf' ∪ {%‖G'‖, %(‖G'‖+1)}) at h1
  specialize h1 _; simp [qf']; clear *-; simp [sets]; tauto
  have: q1 ⊆ qf' ∪ {✦, #0} := by simp [qf', sets]; clear *-; tauto
  simp [qf'] at h1 this cqf; cases bn <;> simp
  · apply t_abs; assumption'; simpa; simpa; simp
  · apply t_tabs; assumption'; simpa; simpa; simp

theorem tcheckq_sound:
  tcheck_spec t →
  tcheckq_spec t :=
by
  dsimp; introv ih tl hgs h1 h2 h; simp only [tcheckq, excs] at h
  obtain ⟨⟨G', p, q'⟩, _, h3, h⟩ := h; simp at h
  apply ih at h3; assumption'; obtain ⟨h4, h⟩ := h
  apply check_qtp_sound at h4; rotate_left; apply h3.1.on_telescope tl; rwa [←h3.1.1]
  obtain ⟨rfl, rfl⟩ := h; split_ands; apply h3.1.trans h4.1; apply Finset.union_subset
  exact h3.2.1; apply closedql_tighten; assumption
  apply t_sub; apply h4.1.on_hastype; apply h3.2.2.filter_widen; simp
  apply s_refl; simp [h4.2]; simpa [h3.1.1, h4.1.1] using h1; clear *-; simp [sets]; tauto

theorem bidirectional_sound:
  tinfer_spec t ∧
  tinfer2_spec t ∧
  tinferexp_spec t ∧
  tinferabs_spec t ∧
  tcheck_spec t ∧
  tcheckabs_spec t ∧
  tcheckq_spec t :=
by
  generalize Hsz: sizeOf t = sz; replace Hsz: sizeOf t < sz + 1 := by omega
  induction sz generalizing t; cases t <;> simp at Hsz; rename_i sz ih
  have: tinfer2_spec t := by
    apply tinfer2_sound
    all_goals intros t _; specialize @ih t (by omega); simp only [ih]
  have: tinfer_spec t := by
    apply tinfer_sound; assumption'
    all_goals intros t _; specialize @ih t (by omega); simp only [ih]
  have: tcheck_spec t := by
    apply tcheck_sound; assumption'
    intros t _; specialize @ih t _; omega; simp only [ih]
  have: tcheckq_spec t := by
    apply tcheckq_sound; assumption
  split_ands'
  apply tinferexp_sound; assumption
  apply tinferabs_sound; assumption
  apply tcheckabs_sound; assumption

-- user inferface

namespace embedding

theorem checking_sound:
  check_program e σ1 = .ok () σ2 →
  ∃ T q, has_type [] ∅ (e 0) T q ∅ :=
by
  intro h; simp only [check_program, excs] at h
  obtain ⟨⟨G, p, T, q⟩, _, h1, -, rfl⟩ := h; exists T, q
  apply bidirectional_sound.1 at h1; obtain ⟨h1, h2, h⟩ := h1
  simp [ctx_grow] at h1; replace h1 := h1.1; symm at h1; simp at h1; subst G
  simp [sets, qdom] at h2; subst p; assumption
  simp [telescope]; simp
