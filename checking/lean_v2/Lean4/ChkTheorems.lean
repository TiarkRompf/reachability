import Lean4.Checking

lemma List.getElem?_eq_getElem' {L: List α} {i: ℕ} (h: i < ‖L‖):
  ∃a, L[i]? = some a :=
by
  have := List.getElem?_eq_getElem h; exists L[i]

namespace Reachability

-- [-simp] is local; redefine them
attribute [-simp] Set.setOf_subset_setOf Set.subset_inter_iff Set.union_subset_iff
attribute [-simp] Finset.union_insert

open qtp
open stp
open has_type

-- qualifier checking

lemma qsatself_sound (tl: telescope G) (c: closed_ql true 0 ‖G‖ q2):
  qtp G (qsatself G q2) q2 gs :=
by
  simp [qsatself]; generalize hi: ‖G‖ = i; replace hi: i ≤ ‖G‖ := by omega
  induction i generalizing q2
  next =>
    simp!; apply q_sub; simp; assumption
  next i ih =>
    obtain ⟨⟨Ti, qi, bn⟩, helm⟩ := List.getElem?_eq_getElem' (by omega: i < ‖G‖)
    simp! [helm]; replace hi: i ≤ ‖G‖ := by omega
    split; swap; apply ih; assumption'; split; swap; simp; apply ih; assumption'
    replace tl: closed_ql true 0 ‖G‖ qi := by c_extend (tl helm).2; assumption
    subst bn; apply q_trans
    · apply ih; apply Finset.union_subset; assumption'
      trans qi; simp; assumption
    · apply q_cong'; apply q_sub; simp; assumption
      apply q_self'; assumption'; simp

namespace qsatself

lemma go_spec (cx: x1 ≤ ‖G‖):
  i ∈ go G x1 q2 ↔ i ∈ q2 ∨
    ∃ f < x1, %f ∈ q2 ∧ ∃ Tf qf, G[f]? = some (Tf, qf, .self) ∧ i ∈ go G f (qf \ {✦}) :=
by
  induction x1 generalizing q2
  next => simp!
  next x ih =>
    obtain ⟨⟨Tx, qx, bn⟩, helm⟩ := List.getElem?_eq_getElem' (by omega: x < ‖G‖)
    simp! [helm]; have: ∀ f, f < x + 1 ↔ f = x ∨ f < x := by omega
    simp [this, helm, and_assoc]; clear this; simp [ih (by omega)]
    by_cases h1: %x ∈ q2 <;> simp [h1]; by_cases h2: bn = .self <;> simp [h2]
    simp [@or_comm (_ ∈ q2), or_assoc]
    simp [or_and_right, and_or_left, exists_or, or_assoc]

lemma go_lift (h: f ≤ ‖G‖) (c: closed_ql true 0 f q):
  go G f q = go G ‖G‖ q :=
by
  ext x; simp [go_spec, h]; congrm _ ∨ ∃i, ?_; simp; rintro h1 - - - -
  specialize c h1; simp at c; simp [c]; omega

lemma spec (tl: telescope G):
  i ∈ qsatself G q2 ↔ i ∈ q2 ∨
    ∃ f, %f ∈ q2 ∧ ∃ Tf qf, G[f]? = some (Tf, qf, .self) ∧ i ∈ qsatself G (qf \ {✦}) :=
by
  simp [qsatself]; conv => left; simp [qsatself.go_spec]
  congrm _ ∨ ∃f, ?_; by_cases h: f < ‖G‖ <;> simp [h, -List.getElem?_eq_getElem]
  rintro -; congrm ∃ Tf qf, ?_; simp; intro h1; specialize tl h1
  rw [go_lift]; omega; simp [closed_ql]; trans qf; simp; apply tl.2
  introv _ h1 _; apply h; rw [List.getElem?_eq_some] at h1; apply h1.1

lemma sub (tl: telescope G):
  q ⊆ qsatself G q :=
by
  intro a h; rw [qsatself.spec tl]; simp [h]

lemma or_dist (tl: telescope G):
  qsatself G (q1 ∪ q2) = qsatself G q1 ∪ qsatself G q2 :=
by
  ext i; simp
  nth_rw 3 [qsatself.spec tl]; nth_rw 2 [qsatself.spec tl]; rw [qsatself.spec tl]
  simp [or_and_right, exists_or, or_assoc]; by_cases h: i ∈ q2 <;> simp [h]

lemma one (tl : telescope G)
  (h1 : G[f]? = some (Tf, qf, bn)):
  qsatself G {%f} = {%f} ∪ ?[bn = .self] qsatself G (qf \ {✦}) :=
by
  ext; rw [qsatself.spec tl]; simp [h1, and_assoc]

lemma none (tl: telescope G) (c: closed_ql true 0 0 q2):
  qsatself G q2 = q2 :=
by
  simp [sets, qdom] at c; ext a
  obtain rfl | rfl := c <;> rw [qsatself.spec tl] <;> simp

lemma mono (tl: telescope G) (h: q1 ⊆ q2):
  qsatself G q1 ⊆ qsatself G q2 :=
by
  intro a h; rw [qsatself.spec tl] at h ⊢; obtain h | ⟨f, h, _⟩ := h
  left; tauto; right; exists f; split_ands'; tauto

lemma sat (tl: telescope G) (c: closed_ql true 0 ‖G‖ q2):
  qsatself G (qsatself G q2) ⊆ qsatself G q2 :=
by
  generalize hi: ‖G‖ = i at c; replace hi: i ≤ ‖G‖ := by omega
  induction c using closed_ql.induct
  next q c => simp [none tl c]
  next i q c' ih c => apply ih; assumption'; omega
  next i q c' ih c =>
    simp [or_dist tl]; gcongr; apply ih; assumption'; omega
    obtain ⟨⟨Ti, qi, bn⟩, helm⟩ := List.getElem?_eq_getElem' (by omega: i < ‖G‖)
    have h1 := Eq.refl (qsatself G {%i}); conv at h1 =>
      right; rw [one tl helm]
    rw [h1, or_dist tl, h1]; split
    · apply Finset.union_subset; simp; subst bn; trans; swap
      apply Finset.subset_union_right; apply ih; simp [closed_ql]
      trans qi; simp; specialize tl helm; apply tl.2; omega
    · rw [none tl]; simp; simp [sets]

end qsatself

lemma qbounded_sound (tl: telescope G) (c: closed_ql true 0 ‖G‖ q2):
  qtp G (qbounded G gs q2) q2 gs :=
by
  simp [qbounded]; generalize hi: ‖G‖ = i; replace hi: i ≤ ‖G‖ := by omega
  induction i
  next => simp!; apply q_sub; simp; assumption
  next i ih =>
    obtain ⟨⟨Ti, qi, bn⟩, helm⟩ := List.getElem?_eq_getElem' (by omega: i < ‖G‖)
    simp! [helm]; replace hi: i ≤ ‖G‖ := (by omega); specialize ih hi
    split; assumption'; apply q_trans; swap; apply ih
    replace ih := (qtp_closed ih).1; rename_i h; obtain ⟨_, _, h⟩ := h
    apply q_cong'; apply q_sub; simp; assumption
    apply q_trans; apply q_var; assumption'
    apply closedql_fr_tighten; swap; specialize tl helm; c_extend tl.2; assumption'
    apply q_sub; assumption'

namespace qbounded

lemma go_spec (cx: x1 ≤ ‖G‖):
  i ∈ go G gs q2 x1 ↔ i ∈ q2 ∨
    ∃ x < x1, i = %x ∧ ∃ Tx qx bn, G[x]? = some (Tx, qx, bn) ∧
      x ∉ gs ∧ ✦ ∉ qx ∧ qx ⊆ go G gs q2 x :=
by
  induction x1
  next => simp!
  next x ih =>
    obtain ⟨⟨Tx, qx, bn⟩, helm⟩ := List.getElem?_eq_getElem' (by omega: x < ‖G‖)
    have: i ∈ go G gs q2 (x + 1) ↔ i ∈ go G gs q2 x ∨
        i = %x ∧ x ∉ gs ∧ ✦ ∉ qx ∧ qx ⊆ go G gs q2 x := by
      simp! [helm]; by_cases h: i ∈ go G gs q2 x <;> simp [h] <;> clear *- <;> tauto
    rw [this]; clear this; have: ∀i, i < x + 1 ↔ i = x ∨ i < x := by omega
    simp [this, -exists_and_right, helm, and_assoc]
    rw [ih]; swap; omega; simp [or_assoc]; conv => enter [1, 2]; rw [or_comm]

lemma go_lift (cx: x1 ≤ ‖G‖) (c: closed_ql true 0 x1 qx):
  qx ⊆ go G gs q2 x1 ↔ qx ⊆ go G gs q2 ‖G‖ :=
by
  simp [sets]; congrm ∀a h, ?_; simp [go_spec, cx, -exists_and_right]
  congrm _ ∨ ∃ x, ?_; simp; rintro rfl - - - - - - -
  specialize c h; simp at c; simp [c]; omega

lemma spec (tl: telescope G):
  i ∈ qbounded G gs q2 ↔ i ∈ q2 ∨
    ∃ x, i = %x ∧ ∃ Tx qx bn, G[x]? = some (Tx, qx, bn) ∧
      x ∉ gs ∧ ✦ ∉ qx ∧ qx ⊆ qbounded G gs q2 :=
by
  simp only [qbounded]; conv => left; simp [go_spec, -exists_and_right]
  congrm _ ∨ ∃x, ?_
  by_cases h1: x < ‖G‖ <;> simp [h1, -exists_and_right, -List.getElem?_eq_getElem]
  rintro rfl; congrm ∃ Tx qx bn, ?_; simp; rintro h - -
  apply go_lift; omega; specialize tl h; apply tl.2
  rintro rfl _ _ _ h - - -; apply h1; rw [List.getElem?_eq_some] at h; apply h.1

lemma sub (tl: telescope G):
  q ⊆ qbounded G gs q :=
by
  simp [sets]; intro a h; rw [qbounded.spec]; simp [h]; assumption

lemma one (tl: telescope G) (h1 : G[x]? = some (Tx, qx, bn)):
  x ∉ gs → ✦ ∉ qx →
  %x ∈ qbounded G gs qx :=
by
  intros; rw [qbounded.spec tl]; right; exists x; simp [h1, and_assoc]
  split_ands'; apply sub tl

lemma wild (tl: telescope G):
  i ∉ qdom false 0 ‖G‖ → i ∈ qbounded G gs q → i ∈ q :=
by
  intro h1 h2; cases i <;> simp [qbounded.spec tl] at h2; assumption'
  simp at h1; simp [h1, List.getElem?_eq_none] at h2; assumption

lemma mono (tl: telescope G) (h: q1 ⊆ q2):
  qbounded G gs q1 ⊆ qbounded G gs q2 :=
by
  intro a h1; by_cases c: a ∈ qdom false 0 ‖G‖; swap
  · apply sub tl; apply h; apply wild tl; assumption'
  simp only [← Finset.singleton_subset_iff] at *; generalize {a} = q at *
  generalize hi: ‖G‖ = i at c; replace hi: i ≤ ‖G‖ := by omega
  induction c using closed_ql.induct
  next q c => simp [sets, qdom] at c; simp [c]
  next i q c' ih c => apply ih; assumption'; omega
  next i q c' ih c =>
    simp [Finset.union_subset_iff] at h1 ⊢
    obtain ⟨_, h1⟩ := h1; split_ands; apply ih; assumption'; omega
    obtain ⟨⟨Tx, qx, bn⟩, helm⟩ := List.getElem?_eq_getElem' (by omega: i < ‖G‖)
    simp [qbounded.spec tl, helm, and_assoc] at h1 ⊢
    obtain h1 | ⟨_, _, h1⟩ := h1; left; apply h h1; right; split_ands'
    apply ih; apply closedql_fr_tighten; assumption'; apply (tl helm).2; omega

lemma or_dist (tl: telescope G):
  qbounded G gs q1 ∪ qbounded G gs q2 ⊆ qbounded G gs (q1 ∪ q2) :=
by
  apply Finset.union_subset; apply mono tl; simp; apply mono tl; simp

lemma sat (tl: telescope G):
  qbounded G gs (qbounded G gs q2) ⊆ qbounded G gs q2 :=
by
  intro a h1; by_cases c: a ∈ qdom false 0 ‖G‖; swap
  · apply wild tl c at h1; assumption
  simp only [← Finset.singleton_subset_iff] at *; generalize {a} = q at *
  generalize hi: ‖G‖ = i at c; replace hi: i ≤ ‖G‖ := by omega
  induction c using closed_ql.induct
  next q c => simp [sets, qdom] at c; simp [c]
  next i q c' ih c => apply ih; assumption'; omega
  next i q c' ih c =>
    simp [Finset.union_subset_iff] at h1 ⊢
    obtain ⟨_, h1⟩ := h1; split_ands; apply ih; assumption'; omega
    obtain ⟨⟨Tx, qx, bn⟩, helm⟩ := List.getElem?_eq_getElem' (by omega: i < ‖G‖)
    simp [qbounded.spec tl, helm, and_assoc] at h1 ⊢
    obtain h1 | ⟨_, _, h1⟩ := h1; assumption; right; split_ands'
    apply ih; apply closedql_fr_tighten; assumption'; apply (tl helm).2; omega

lemma trans (tl: telescope G):
  q1 ⊆ qbounded G gs q2 →
  q2 ⊆ qbounded G gs q3 →
  q1 ⊆ qbounded G gs q3 :=
by
  intro h1 h2; apply mono (gs := gs) tl at h2
  trans; assumption; trans; assumption; apply sat tl

end qbounded

theorem check_qtp0_sound (tl: telescope G):
  check_qtp0 G gs q1 q2 → qtp G q1 q2 gs :=
by
  intro h; simp [check_qtp0] at h; obtain ⟨c1, c2, h⟩ := h
  have h1 := qsatself_sound (gs := gs) tl c2; have c3 := (qtp_closed h1).1
  have h2 := qbounded_sound (gs := gs) tl c3; have c4 := (qtp_closed h2).1
  apply q_trans; assumption'; apply q_trans; assumption'; apply q_sub; assumption'

lemma complete_magic (tl: telescope G)
  (c: closed_ql true 0 ‖G‖ q1) (c2: closed_ql true 0 ‖G‖ q2):
  q1 ⊆ qbounded G gs (qsatself G q2) →
  qsatself G q1 ⊆ qbounded G gs (qsatself G q2) :=
by
  intro h; generalize hi: ‖G‖ = i at c; replace hi: i ≤ ‖G‖ := by omega
  induction c using closed_ql.induct
  next q1 c => trans q1; assumption'; rw [qsatself.none tl c]
  next i q1 c' ih c => apply ih; assumption'; omega
  next i q1 c' ih c =>
    simp [qsatself.or_dist tl, Finset.union_subset_iff] at h ⊢
    obtain ⟨_, h⟩ := h; split_ands; apply ih; assumption'; omega
    obtain ⟨⟨Tx, qx, bn⟩, helm⟩ := List.getElem?_eq_getElem' (by omega: i < ‖G‖)
    have h' := h; simp [qbounded.spec tl, helm, and_assoc] at h; obtain h | h := h
    · simp only [← Finset.singleton_subset_iff] at h
      apply qsatself.mono tl at h; trans; apply h
      trans; apply qsatself.sat tl c2; apply qbounded.sub tl
    rw [qsatself.one tl helm]; apply Finset.union_subset; simpa
    split; apply ih; simp [closed_ql]; trans qx; simp
    specialize tl helm; apply tl.2; trans qx; simp; simp [h]; omega; simp

theorem check_qtp0_complete (tl: telescope G):
  qtp G q1 q2 gs → check_qtp0 G gs q1 q2 :=
by
  intro h; have := qtp_closed h; simp [check_qtp0, this]; clear this
  induction h
  case q_sub q1 q2 G gs h h1 =>
    trans; apply h; trans; swap; apply qbounded.sub tl; apply qsatself.sub tl
  case q_cong G q1a q2a gs q1b q2b h1 h2 ih1 ih2 =>
    simp [qsatself.or_dist tl]; trans; swap; apply qbounded.or_dist tl; gcongr
    apply ih1 tl; apply ih2 tl
  case q_self G f Tf qf gs h1 _ =>
    trans; swap; apply qbounded.sub tl; simp [qsatself.one tl h1]
    trans; swap; apply Finset.subset_union_right; apply qsatself.sub tl
  case q_var G x Tx qx bn gs h1 _ _ =>
    trans; swap; apply qbounded.mono tl; apply qsatself.sub tl
    simp; apply qbounded.one tl; assumption'; c_free;
  case q_trans G q1 q2 gs q3 h1 h2 ih1 ih2 =>
    apply qbounded.trans tl; apply ih1 tl; obtain ⟨_, _⟩ := qtp_closed h2
    apply complete_magic tl; assumption'; apply ih2 tl

lemma qdiff_nonprincipal:
  let G := [(.TRef .TBool ∅, {✦}, .var), (.TRef .TBool ∅, {✦}, .var), ((.TRef .TBool ∅, {%0, %1}, .var))]
  qtp G {%2} ({%0} ∪ {%2}) ∅ ∧ qtp G {%2} ({%0} ∪ {%1}) ∅ ∧
    ¬ qtp G {%2} {%1} ∅ ∧ ¬ qtp G {%1} {%2} ∅ :=
by
  have := fun {α: Type} {x l} (h: ‖l‖ > 0) => Eq.symm (@List.singleton_append α x l)
  intro G; replace this: telescope G := by
    rw [←List.nil_append G]; simp_arith only [G, this, ←List.append_assoc]
    apply telescope_extend; simp! [sets]; simp [sets]
    apply telescope_extend; simp! [sets]; simp [sets]
    apply telescope_extend; simp! [sets]; simp [sets]; simp [telescope]
  simp [G]; split_ands
  apply check_qtp0_sound; assumption; decide
  apply check_qtp0_sound; assumption; decide
  intro h; apply check_qtp0_complete at h; revert h; decide; assumption
  intro h; apply check_qtp0_complete at h; revert h; decide; assumption

namespace M

@[excs]
lemma pure_ok:
  @pure M _ _ a s1 = .ok r s2 ↔ a = r ∧ s1 = s2 :=
by
  simp [pure, EStateM.pure]

@[excs]
lemma throw_ok:
  @throw _ M _ _ e s1 = .ok r s2 ↔ False :=
by
  simp [throw, throwThe, MonadExceptOf.throw, EStateM.throw]

@[excs]
lemma bind_ok {a: M α}:
  bind a f s1 = .ok r s2 ↔ ∃v s, a s1 = .ok v s ∧ f v s = .ok r s2 :=
by
  simp [bind, EStateM.bind]; constructor <;> intro h
  · split at h; rename_i a s h1; exists a, s; simp at h
  · obtain ⟨v, s, h1, h2⟩ := h; simp [h1, h2]

lemma trycatch_ok:
  @tryCatch _ M _ _ a f σ1 = .ok r σ2 →
    a σ1 = .ok r σ2 ∨
    ∃ e σ σ', a σ1 = .error e σ ∧ f e σ' = .ok r σ2 :=
by
  simp [tryCatch, tryCatchThe, MonadExceptOf.tryCatch, EStateM.tryCatch]
  intro h; split at h; right; rename_i e s h1; exists e; simp [h1, h]
  exists EStateM.Backtrackable.restore s (EStateM.Backtrackable.save σ1)
  left; assumption

@[excs]
lemma qassert_ok [Decidable b]:
  qassert b m s1 = .ok r s2 ↔ b ∧ s1 = s2 :=
by
  simp [qassert]; split <;> rename_i h; simp [pure_ok, h]; simp [h, throw_ok]

@[excs]
lemma qtrace_ok:
  qtrace msg act s1 = .ok r s2 ↔ act s1 = .ok r s2 :=
by
  simp [qtrace, EStateM.adaptExcept]; constructor <;> intro h
  split at h; simp at h; simp at h; obtain ⟨rfl, rfl⟩ := h; assumption; simp [h]

@[excs]
lemma liftM_ok:
  @liftM Option M _ _ a s1 = .ok r s2 ↔ a = some r ∧ s1 = s2 :=
by
  simp [liftM, monadLift, MonadLift.monadLift]; constructor <;> intro h
  · split at h; rename_i a; simp [pure_ok] at h; simp [h]; simp at h
  · simp [h]; simp [pure_ok]

end M

lemma qunify_wfctx' (TL: telescope G) (hgs: gs ⊆ gs0):
  qunify.go G q2 gs0 gs i q1 σ1 = .ok G' σ2 →
  ctx_grow G G' gs0 :=
by
  intro h; induction i generalizing q1 σ1 G' σ2 <;> simp! only at h
  · simp only [excs] at h; obtain ⟨-, _, ⟨_, rfl⟩, rfl, rfl⟩ := h; simp [ctx_grow]
  next x ih =>
    simp only [excs] at h; obtain ⟨⟨_, qx, _⟩, _, ⟨h1, rfl⟩, h⟩ := h
    split at h; apply ih h
    generalize hf: @Finset.min ℕ _ _ = f' at h; split at h
    next f =>
      apply Finset.mem_of_min at hf; simp at hf; simp only [excs] at h
      obtain ⟨-, _, -, G', _, h2, ⟨Tf, qf, bn⟩, _, ⟨h3, rfl⟩, h⟩ := h; simp at h
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h; apply ih at h2; apply h2.trans
      apply ctx_grow.set; apply h3; rfl; apply Finset.union_subset
      replace TL := h2.on_telescope TL; apply (TL h3).2; simp [hf]; simp; simp
      apply hgs; simp [hf]
    next =>
      simp only [excs] at h; obtain ⟨_, _, ⟨_, rfl⟩, h⟩ := h
      apply ih h

lemma qunify_wfctx:
  telescope G →
  qunify G q1 q2 gs σ1 = .ok G' σ2 →
  ctx_grow G G' gs :=
by
  intro tl h; simp [qunify] at h; apply qunify_wfctx'; assumption'; simp

lemma qunify_sound:
  telescope G → closed_ql true 0 ‖G‖ q2 →
  qunify G q1 q2 gs σ1 = .ok G' σ2 →
  qtp G' q1 q2 gs :=
by
  intros TL Cq2 H; simp [qunify] at H
  generalize hi: ‖G‖ = i at H; replace hi: i ≤ ‖G‖ := by omega
  induction i generalizing q1 G' σ1
  next =>
    simp! only [excs] at H; obtain ⟨-, _, ⟨_, rfl⟩, rfl, rfl⟩ := H
    apply q_sub; assumption'
  next x ih =>
    simp! only [excs] at H; replace hi: x ≤ ‖G‖ := by omega
    have H0: ∀G, qtp G (q1 \ {%x} ∪ {%x}) q2 gs → qtp G q1 q2 gs := by
      introv H; apply q_trans; swap; apply H; apply q_sub; simp; apply (qtp_closed H).1
    obtain ⟨⟨_, qx, _⟩, _, ⟨H1, rfl⟩, H⟩ := H; split at H
    next H2 =>
      have CG := qunify_wfctx' TL (by simp) H; apply ih at H; specialize H hi; assumption
    generalize hf: @Finset.min ℕ _ _ = f' at H; split at H
    next f =>
      apply Finset.mem_of_min at hf; simp at hf; simp only [excs] at H
      obtain ⟨-, _, -, G', _, H2, ⟨Tf, qf, bn⟩, _, ⟨H3, rfl⟩, H⟩ := H; simp at H
      have CG := qunify_wfctx' TL (by simp) H2
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := H; apply ih at H2; specialize H2 hi
      generalize hG: G'.set f _ = G''; symm at hG
      replace TL: closed_ql true 0 f (qf ∪ {%x}) := by
        apply Finset.union_subset; apply (CG.on_telescope TL H3).2; simp [hf]
      have CG1 := ctx_grow.set f H3 hG TL (by simp) (by simp) hf.1.1; apply H0
      apply q_cong'; apply CG1.on_qtp H2; have L := (List.getElem?_eq_some.1 H3).1
      apply q_self' (f := f); simp [hG, List.getElem?_set]; exact ⟨L, rfl, rfl⟩
      simp; simp [hf]; simp [hG]; c_extend; omega; simpa [hG, ← CG.1]
    next H2 _ =>
      simp only [excs] at H; obtain ⟨-, _, ⟨H3, rfl⟩, H⟩ := H; simp at H2
      have CG := qunify_wfctx' TL (by simp) H
      apply ih at H; specialize H hi; simp [subst, H2] at H; apply H0
      apply q_trans; swap; apply H; apply q_cong
      apply q_sub; simp; simp [closed_ql]; trans; swap; apply (qtp_closed H).1; simp
      apply q_var; have := CG.2 x; simp [H3] at this; rw [←this, H1]
      simp [H3]; rw [← CG.1]; apply closedql_fr_tighten; apply H3.1
      specialize TL H1; c_extend TL.2; have := (List.getElem?_eq_some.1 H1).1; omega

theorem check_qtp_wfctx (tl: telescope G):
  check_qtp G gs q1 q2 σ1 = .ok G' σ2 →
  ctx_grow G G' gs :=
by
  intro h; simp only [check_qtp, excs] at h; apply qunify_wfctx at h; assumption'

theorem check_qtp_sound (tl: telescope G):
  closed_ql true 0 ‖G‖ q2 →
  check_qtp G gs q1 q2 σ1 = .ok G' σ2 →
  ctx_grow G G' gs ∧ qtp G' q1 q2 gs :=
by
  intro c2 h; have CG := check_qtp_wfctx tl h; split_ands'
  simp only [check_qtp, excs] at h
  have hq2 := @qsatself_sound G q2 gs tl c2
  generalize qsatself G q2 = q2' at *; have := (qtp_closed hq2).1
  have hq1 := @qbounded_sound G q2' gs tl (by assumption)
  generalize qbounded G gs q2' = q2'' at *; have := (qtp_closed hq1).1
  apply qunify_sound at h; assumption'
  apply q_trans h; apply CG.on_qtp; apply q_trans; assumption'

lemma check_app_sound:
  telescope G → closed_ql true 1 ‖G‖ q1 →
  check_app G gs qf qx q1 σ1 = .ok (G', p) σ2 →
  ctx_grow G G' gs ∧ closed_ql false 0 ‖G‖ p ∧
  (∀ p', p ⊆ p' →
    #0 ∈ q1 ∨ qtp G' qx q1 gs ∨ ✦ ∈ q1 ∧
    qtp G' ((vars_trans G' qf) ∩ (vars_trans G' qx)) q1 gs ∧
    (vars_trans G' qf ∩ vars_trans G' qx) \ {✦} ⊆ p' ∧
    (∀i ∈ gs, %i ∉ vars_trans G' qf ∧ %i ∉ vars_trans G' qx)) :=
by
  intro tl Cq1 h; simp only [check_app, excs] at h; split at h
  · simp [excs] at h; obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h; split_ands
    simp [ctx_grow]; simp [sets]; intros; tauto
  apply closedql_bv_tighten at Cq1; assumption'
  simp only [excs] at h; obtain ⟨_, _, h, rfl, rfl⟩ := h; apply M.trycatch_ok at h
  obtain h | h := h; simp only [excs] at h
  · simp at h; obtain ⟨G', h, rfl, rfl⟩ := h; have := check_qtp_wfctx tl h
    split_ands'; simp [sets]; apply check_qtp_sound at h; assumption'; tauto
  obtain ⟨_, -, _, -, h⟩ := h; split at h <;> simp only [excs] at h; simp at h
  next h1 =>
    simp at h1; obtain ⟨-, -, -, -, _, -, -, _, ⟨h2, rfl⟩, G', _, h3, h⟩ := h
    simp at h; obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h; have CG := check_qtp_wfctx tl h3
    apply check_qtp_sound at h3; assumption'; replace h3 := h3.2
    split_ands'; apply closedql_tighten; rw [CG.1]; apply (qtp_closed h3).1
    simp [Finset.eq_empty_iff_forall_not_mem] at h2
    have h2a := fun x h => (h2 x h).1
    have h2b := fun x h => (h2 x h).2
    simp [←CG.on_vars_trans h2a, ←CG.on_vars_trans h2b]
    intro p' h4; right; right; split_ands'

-- subtype checking

lemma check_stp2_sound (TL: telescope G):
  check_stp2 fuel G q0 T1 T2 gs σ1 = .ok (gr, G') σ2 →
  closed_ql true 0 ‖G‖ q0 → closed_ty 0 ‖G‖ T1 → closed_ty 0 ‖G‖ T2 →
  closed_ql false 0 ‖G‖ gr ∧ ctx_grow G G' gs ∧ stp G' T1 q0 gr T2 gs :=
by
  intro h Cq0 Ct1 Ct2
  induction fuel, G, q0, T1, T2, gs using check_stp2.induct generalizing gr G' σ1 σ2
  next fuel G q0 T1 T2 gs =>
    exact ∀ {σ1 gr G' σ2}, telescope G →
      check_stp2.go fuel G q0 T1 T2 gs σ1 = .ok (gr, G') σ2 →
      closed_ql true 0 ‖G‖ q0 → closed_ty 0 ‖G‖ T1 → closed_ty 0 ‖G‖ T2 →
      closed_ql false 0 ‖G‖ gr ∧ ctx_grow G G' gs ∧ stp G' T1 q0 gr T2 gs
  rotate_right; next ih1 =>
    simp only [check_stp2, excs] at h; simp at h; obtain ⟨gr, G', _, h, -, rfl, rfl⟩ := h
    specialize ih1 TL h Cq0 Ct1 Ct2; assumption
  all_goals introv TL h Cq0 Ct1 Ct2
  next => -- bool
    simp only [check_stp2.go, excs] at h; simp at h; obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    simp [ctx_grow, closed_ql]; apply s_refl; simp!
  next => -- top
    simp only [check_stp2.go, excs] at h; simp at h; obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    simp [ctx_grow, closed_ql]; apply s_top; assumption
  next h1 => -- tvar refl
    simp only [check_stp2.go, excs] at h; obtain ⟨rfl, h1⟩ := h1; simp [h1, excs] at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h; simp [ctx_grow, closed_ql]; apply s_refl; assumption
  next x _ _ h1 ih => -- tvar exposure
    simp only [check_stp2.go, excs] at h; simp [h1, excs] at h
    obtain ⟨Tx, _, _, _, ⟨h2, rfl⟩, _, ⟨rfl, rfl⟩, h⟩ := h
    specialize ih _ TL h Cq0 _ Ct2; specialize TL h2; c_extend TL.1
    rw [List.getElem?_eq_some] at h2; replace h2 := h2.1; omega
    obtain ⟨_, cg, s2⟩ := ih; split_ands'; have: gr = ∅ ∪ gr := (by simp)
    rw [this]; clear this; apply s_trans; swap; simpa
    have h2' := cg.2 x; simp [h2] at h2'; symm at h2'; apply s_tvar; assumption'
    have := (cg.on_telescope TL) h2'; c_extend this.1
    rw [List.getElem?_eq_some] at h2'; replace h2' := h2'.1; omega
  next ih1 ih2 => -- tref
    simp only [check_stp2.go, excs] at h
    obtain ⟨-, _, ⟨h0, rfl⟩, ⟨gr1, G1⟩, _, h1, ⟨gr2, G2⟩, _, h2, h⟩ := h
    simp at h2 h; obtain ⟨_, ⟨⟨rfl, rfl⟩, rfl⟩, G3, _, h3, h4, rfl⟩ := h
    apply And.intro; simp [closed_ql]; simp! at Ct1 Ct2
    replace ih1 := (ih1 TL h1 (by simp [sets]) Ct1.1 Ct2.1).2; clear h1
    replace TL := ih1.1.on_telescope TL; simp [ih1.1.1] at Ct1 Ct2
    replace ih2 := (ih2 _ TL h2 (by simp [sets]) Ct2.1 Ct1.1).2; clear h2
    replace TL := ih2.1.on_telescope TL; simp [ih2.1.1] at Ct1 Ct2
    replace Ct2 := closedql_bv_tighten h0.2 Ct2.2
    apply check_qtp_sound at h3; assumption'; swap; c_extend;
    replace Ct1 := closedql_bv_tighten h0.1 Ct1.2
    replace TL := h3.1.on_telescope TL; simp [h3.1.1] at Ct1
    apply check_qtp_sound at h4; assumption'; swap; c_extend; obtain ⟨cg4, h4'⟩ := h4
    obtain ⟨cg3, h3'⟩ := And.intro (h3.1.trans cg4) (cg4.on_qtp h3.2)
    obtain ⟨cg2, ih2'⟩ := And.intro (ih2.1.trans cg3) (cg3.on_stp ih2.2)
    obtain ⟨cg1, ih1'⟩ := And.intro (ih1.1.trans cg2) (cg2.on_stp ih1.2)
    clear cg2 cg3 cg4 ih1 ih2 h3; split_ands'; apply s_ref; assumption'
    c_free; c_free;
  next G q0 gs _ _ q1a _ _ T1b q1b _ _ gs' ih1 ih2 => -- tfun
    simp only [check_stp2.go, excs] at h
    obtain ⟨⟨gr1, G1⟩, _, S1, G2, _, Q1, ⟨gr2, G3⟩, _, S2, G4, _, Q2, h⟩ := h
    simp at Q1 S2 Q2 h; obtain ⟨T0, _, ⟨⟨b0, h1⟩, rfl⟩, h, h2⟩ := h
    replace TL: telescope (G ++ [(.TTop, q0, .self)]) := by
      apply telescope_extend; simp!; assumption'
    specialize ih1 TL S1 _ _ _; simp [sets]
    · apply subst_tighten; c_extend Ct2.1; simp
    · apply subst_tighten; c_extend Ct1.1; simp
    replace S1 := ih1; clear ih1; simp at S1; replace TL := S1.2.1.on_telescope TL
    have LG := Eq.symm S1.2.1.1; simp at LG
    replace Q1: ctx_grow G1 G2 gs' ∧
        ({#0, ✦} ⊆ q1a ∨ qtp G2 ([#0 ↦ %‖G‖] q1b ∪ gr1) ([#0 ↦ %‖G‖] q1a) gs') := by
      split at Q1 <;> rename_i hq1a
      · simp [excs] at Q1; obtain ⟨rfl, rfl⟩ := Q1; simp [ctx_grow, hq1a]
      · apply check_qtp_sound at Q1; clear *- Q1; tauto; assumption
        simp [LG]; apply subst_tighten; c_extend Ct1.2.2.1; simp [sets]
    replace LG := Q1.1.1 ▸ LG
    replace TL: telescope (G2 ++ [([#0 ↦ %‖G‖] T1b, [#0 ↦ %‖G‖] q1b, .var)]) := by
      simp; apply telescope_extend; rotate_right; apply Q1.1.on_telescope TL
      simp [LG]; apply subst_tighten; c_extend Ct2.1; simp
      simp [LG]; apply subst_tighten; c_extend Ct2.2.2.1; simp [sets]
    specialize ih2 _ _ TL S2 _ _ _; simp [sets]
    · simp [LG]; repeat apply subst_tighten
      c_extend Ct1.2.1; omega; split_ands; simp!; apply Finset.union_subset; simp [sets]
      c_extend S1.1; simp; intro h; absurd h; c_free S1.1; simp; omega
    · simp [LG]; repeat apply subst_tighten
      c_extend Ct2.2.1; omega; simp; simp; omega
    replace S2 := ih2; clear ih2; simp [LG] at S2; replace TL := S2.2.1.on_telescope TL
    replace LG := by have := Eq.symm S2.2.1.1; simp [LG] at this; exact this
    apply check_qtp_sound at Q2; assumption'; swap
    · simp [LG]; repeat apply subst_tighten
      c_extend Ct2.2.2.2.1; omega; simp [sets]; simp [sets]; omega
    clear LG; replace TL := Q2.1.on_telescope TL
    -- list reasoning
    obtain ⟨CG, Q2⟩ := Q2; obtain ⟨Hgr2, CG3, S2⟩ := S2
    replace S2 := CG.on_stp S2; replace CG := CG3.trans CG; clear CG3
    obtain ⟨G4', q4', rfl, hq4⟩ := CG.inversion; simp at hq4; subst q4'
    replace CG := CG.shrink rfl; obtain ⟨CG2, Q1⟩ := Q1
    replace Q1 := Q1.elim (Or.inl ·) (Or.inr <| CG.on_qtp ·)
    replace CG := CG2.trans CG; clear CG2; obtain ⟨Hgr1, CG1, S1⟩ := S1
    replace S1 := CG.on_stp S1; replace CG := CG1.trans CG; clear CG1
    obtain ⟨G', gr0, rfl, hgr0⟩ := CG.inversion; simp [gs', -Finset.mem_sdiff] at hgr0
    simp only [gs'] at *; clear gs'; replace CG := CG.shrink (by simp)
    have := CG.1; simp only [this] at *; clear this G1 G2 G3
    simp [List.getElem_append_right] at h1 h2; subst G'; obtain ⟨rfl, rfl, rfl⟩ := h1
    -- start solving goals
    have: closed_ql false 0 ‖G'‖ gr := by
      subst gr; (repeat' apply Finset.union_subset)
      apply closedql_tighten; assumption
      convert_to (gr2 \ {%(‖G'‖+1)}) \ {%‖G'‖} ⊆ _; ext; simp; clear *-; tauto
      (repeat apply closedql_tighten); assumption
      apply closedql_fr_tighten; apply hgr0.2; simp [closed_ql]
      trans gr0; simp; specialize TL (x := ‖G'‖)
      simp [List.getElem_append_right] at TL; exact TL.2
    split_ands'; simp [←CG.1] at CG; apply CG.gs_shrink; clear TL CG G Hgr1 Hgr2
    have CG: ctx_grow (G' ++ [(.TTop, gr0, .self)])
                      (G' ++ [(.TTop, q0 ∪ gr, .self)]) (gs ∪ {‖G'‖}) := by
      apply ctx_grow.set ‖G'‖; simp; exact ⟨rfl, rfl⟩; simp; exact rfl
      apply Finset.union_subset; assumption; c_extend;
      have: ✦ ∉ gr := (by c_free;); simp [this]; apply hgr0.1
      subst gr; clear *-; simp [sets]; tauto; simp
    apply stp.gs_tighten (gs' := gs ∪ {‖G'‖}); swap; simp
    apply s_fun (gr1 := gr1) (gr2 := gr2)
    · apply CG.on_stp S1
    · obtain Q1 | Q1 := Q1; simp [Q1]; right; apply CG.on_qtp Q1
    · simp; rw [List.append_cons]; apply CG.append.on_stp S2
    · simp; rw [List.append_cons]; apply CG.append.on_qtp Q2
    · subst gr; simp
    · subst gr; clear * -; simp [sets]; tauto
    assumption'
  next G q0 gs _ T1b q1a _ _ _ q1b _ _ ih2 => -- tall
    simp only [check_stp2.go, excs] at h
    obtain ⟨-, _, ⟨rfl, rfl⟩, G2, _, Q1, ⟨gr2, G3⟩, _, S2, G4, _, Q2, h⟩ := h
    simp at S2 Q2 h; obtain ⟨T0, _, ⟨⟨b0, h1⟩, rfl⟩, h, h2⟩ := h
    let G1 := G ++ [(.TTop, q0, .self)]; let gs' := gs ∪ {‖G‖}
    replace TL: telescope G1 := by
      apply telescope_extend; simp!; assumption'
    replace Q1: ctx_grow G1 G2 gs' ∧
        ({#0, ✦} ⊆ q1a ∨ qtp G2 ([#0 ↦ %‖G‖] q1b) ([#0 ↦ %‖G‖] q1a) gs') := by
      split at Q1 <;> rename_i hq1a
      · simp [excs] at Q1; obtain ⟨rfl, rfl⟩ := Q1; simp [ctx_grow, hq1a, G1]
      · apply check_qtp_sound at Q1; clear *- Q1; tauto; assumption
        simp; apply subst_tighten; c_extend Ct1.2.2.1; simp [sets]
    have LG := Eq.symm Q1.1.1; simp [G1] at LG
    replace TL: telescope (G2 ++ [([#0 ↦ %‖G‖] T1b, [#0 ↦ %‖G‖] q1b, .tvar)]) := by
      simp; apply telescope_extend; rotate_right; apply Q1.1.on_telescope TL
      simp [LG]; apply subst_tighten; c_extend Ct2.1; simp
      simp [LG]; apply subst_tighten; c_extend Ct2.2.2.1; simp [sets]
    specialize ih2 _ TL S2 _ _ _; simp [sets]
    · simp [LG]; repeat apply subst_tighten
      c_extend Ct1.2.1; omega; simp; simp; omega
    · simp [LG]; repeat apply subst_tighten
      c_extend Ct2.2.1; omega; simp; simp; omega
    replace S2 := ih2; clear ih2; simp [LG] at S2; replace TL := S2.2.1.on_telescope TL
    replace LG := by have := Eq.symm S2.2.1.1; simp [LG] at this; exact this
    apply check_qtp_sound at Q2; assumption'; swap
    · simp [LG]; repeat apply subst_tighten
      c_extend Ct2.2.2.2.1; omega; simp [sets]; simp [sets]; omega
    clear LG; replace TL := Q2.1.on_telescope TL
    -- list reasoning
    obtain ⟨CG, Q2⟩ := Q2; obtain ⟨Hgr2, CG3, S2⟩ := S2
    replace S2 := CG.on_stp S2; replace CG := CG3.trans CG; clear CG3
    obtain ⟨G4', q4', rfl, hq4⟩ := CG.inversion; simp at hq4; subst q4'
    replace CG := CG.shrink rfl; obtain ⟨CG2, Q1⟩ := Q1
    replace Q1 := Q1.elim (Or.inl ·) (Or.inr <| CG.on_qtp ·)
    replace CG := CG2.trans CG; clear CG2
    obtain ⟨G', gr0, rfl, hgr0⟩ := CG.inversion; simp [gs', -Finset.mem_sdiff] at hgr0
    simp only [gs'] at *; clear gs'; replace CG := CG.shrink (by simp)
    have := CG.1; simp only [this] at *; clear this G1 G2 G3
    simp [List.getElem_append_right] at h1 h2; subst G'; obtain ⟨rfl, rfl, rfl⟩ := h1
    -- start solving goals
    have: closed_ql false 0 ‖G'‖ gr := by
      subst gr; (repeat' apply Finset.union_subset)
      convert_to (gr2 \ {%(‖G'‖+1)}) \ {%‖G'‖} ⊆ _; ext; simp; clear *-; tauto
      (repeat apply closedql_tighten); assumption
      apply closedql_fr_tighten; apply hgr0.2; simp [closed_ql]
      trans gr0; simp; specialize TL (x := ‖G'‖)
      simp [List.getElem_append_right] at TL; exact TL.2
    split_ands'; simp [←CG.1] at CG; apply CG.gs_shrink; clear TL CG G Hgr2
    have CG: ctx_grow (G' ++ [(.TTop, gr0, .self)])
                      (G' ++ [(.TTop, q0 ∪ gr, .self)]) (gs ∪ {‖G'‖}) := by
      apply ctx_grow.set ‖G'‖; simp; exact ⟨rfl, rfl⟩; simp; exact rfl
      apply Finset.union_subset; assumption; c_extend;
      have: ✦ ∉ gr := (by c_free;); simp [this]; apply hgr0.1
      subst gr; clear *-; simp [sets]; tauto; simp
    apply stp.gs_tighten (gs' := gs ∪ {‖G'‖}); swap; simp
    apply s_all (gr2 := gr2)
    · apply s_refl; simp; apply subst_tighten; c_extend Ct2.1; simp
    · obtain Q1 | Q1 := Q1; simp [Q1]; right; apply CG.on_qtp Q1
    · simp; rw [List.append_cons]; apply CG.append.on_stp S2
    · simp; rw [List.append_cons]; apply CG.append.on_qtp Q2
    · subst gr; simp
    assumption'
  next => simp only [check_stp2.go, excs] at h

-- alternative measurement

lemma subsize_splice (C: closed_ty 0 ‖G ++ G'‖ T):
  sub_size' (G ++ G0 ++ G') (T.splice ‖G‖ ‖G0‖) = sub_size' (G ++ G') T :=
by
  induction T using ty.induct' generalizing G' <;> simp! [sub_size', -List.append_assoc]
  case TRef IH =>
    rw [IH]; rfl; simp! at C; simp [C]
  case TVar x =>
    cases x <;> simp [sub_size']; split <;> rename_i h
    simp [sub_size', h, List.getElem?_append_left]
    simp! at C; simp at h; simp [sub_size']; repeat rw [List.getElem?_append_right]
    congr 2; omega; assumption; omega; omega
  case TFun ih1 ih2 =>
    simp! at C; obtain ⟨_, _, -⟩ := C; conv => right; simp
    rw [←ih1, ←ih2]; simp; split; exfalso; omega; split; exfalso; omega
    congr 4; simp; omega; omega; simp; omega; simp
    simp; repeat apply subst_tighten
    c_extend; simp; omega; simp; simp
    simp; apply subst_tighten; c_extend; simp
  case TAll ih1 ih2 =>
    simp! at C; obtain ⟨_, _, -⟩ := C; conv => right; simp
    rw [←ih2, ←ih1]; simp; split; exfalso; omega; split; exfalso; omega
    congr 3; congr 6; omega; omega; simp; omega; simp
    simp; apply subst_tighten; c_extend; simp
    simp; simp; repeat apply subst_tighten
    c_extend; simp; omega; simp

lemma subsize_prefix (C: closed_ty 0 x T):
  sub_size' (G.take x) T = sub_size' G T :=
by
  have := @subsize_splice (G.take x) [] T (G.drop x)
  simp at this; by_cases h: x ≤ ‖G‖
  simp [h, C, ty.splice_self C] at this; simp [this]
  replace h: ‖G‖ ≤ x := by omega
  rw [←List.take_self_eq_iff] at h; rw [← h]

lemma ty.subst_preserves_subsize {x: ℕ} {q: ql}:
  x < ‖G‖ → closed_ql false 0 ‖G‖ q →
  sub_size' G ([%x ↦ (ty.TVar %x, q)] T) = sub_size' G T :=
by
  intros c1 c2
  induction T using ty.induct' generalizing G <;> simp [sub_size']
  case TRef ih =>
    rw [ih]; rfl; assumption'
  case TFun ih1 ih2 =>
    (repeat rw [ty.open_subst_comm]); rw [ih1, ih2]
    simp; simp; omega; c_extend; simp; simp; omega; c_extend;
    simp; omega; c_free; simp!; simp
    simp; omega; c_free; simp!; simp
    simp; omega; c_free; simp!; simp
  case TAll ih1 ih2 =>
    (repeat rw [ty.open_subst_comm]); rw [ih2, ih1]
    simp; simp; omega; c_extend; simp; simp; omega; c_extend;
    simp; omega; c_free; simp!; simp
    simp; omega; c_free; simp!; simp
    simp; omega; c_free; simp!; simp
  case TVar =>
    split; subst_vars; rfl; rfl

@[simp]
lemma tenv.sub_size_length {G: tenv}:
  ‖G.sub_sizes‖ = ‖G‖ :=
by
  simp [tenv.sub_sizes]; induction G using List.reverseRecOn
  simp; simpa

@[simp]
lemma tenv.sub_sizes_append {G G1: tenv}:
  (G ++ G1).sub_sizes = G1.foldl
    (fun res (T, _, bn) =>
      res ++ [if bn = .tvar then sub_size' res T else 0])
    G.sub_sizes :=
by
  simp [sub_sizes]

lemma tenv.sub_sizes_spec {G: tenv}:
  G[x]? = some (T, q, .tvar) →
  G.sub_sizes[x]? = sub_size' (G.sub_sizes.take x) T :=
by
  intro H
  induction G using List.reverseRecOn; simp at H
  next G a H1 =>
    obtain ⟨T', q', bn⟩ := a; simp; generalize h: ite (bn = .tvar) _ _ = a
    simp [List.getElem?_append] at H; split at H <;> rename_i hx
    · rw [List.getElem?_append_left, List.take_append_of_le_length]
      exact H1 H; simp; omega; simpa
    · have := (List.getElem?_eq_some.1 H).1; simp at this
      replace hx: x = ‖G‖ := (by omega); clear this H1; subst x a; simp at H ⊢
      obtain ⟨rfl, rfl, rfl⟩ := H; simp

lemma ctx_grow.on_subsize (h: ctx_grow G1 G2 gs):
  sub_size G2 T = sub_size G1 T :=
by
  simp [sub_size]; congr 1
  induction h using ctx_grow.induct; simp
  next G' _ cg ih =>
    simp [cg.shrink, ih]; have := cg.2 ‖G'‖; simp at this
    have L := cg.1; simp at L; simp [←L] at this
    obtain rfl | ⟨-, _, _, _, -, -, rfl, rfl⟩ := this; rfl; rfl

lemma check_stp2_fuel (TL: telescope G):
  closed_ql true 0 ‖G‖ q0 → closed_ty 0 ‖G‖ T1 → closed_ty 0 ‖G‖ T2 →
  check_stp2 fuel G q0 T1 T2 gs σ1 = .ok (gr, G') σ2 →
  sub_size G T1 + sub_size G T2 ≤ fuel' →
  check_stp2 fuel' G q0 T1 T2 gs σ1 = .ok (gr, G') σ2 :=
by
  intro Cq0 Ct1 Ct2 h Hfuel
  induction fuel, G, q0, T1, T2, gs using check_stp2.induct generalizing gr G' fuel' σ1 σ2
  next fuel G q0 T1 T2 gs =>
    exact ∀ {gr G' fuel' σ1 σ2}, telescope G →
      closed_ql true 0 ‖G‖ q0 → closed_ty 0 ‖G‖ T1 → closed_ty 0 ‖G‖ T2 →
      check_stp2.go fuel G q0 T1 T2 gs σ1 = .ok (gr, G') σ2 →
      sub_size G T1 + sub_size G T2 ≤ fuel' →
      check_stp2.go fuel' G q0 T1 T2 gs σ1 = .ok (gr, G') σ2
  rotate_right; next ih =>
    simp only [check_stp2, excs] at h ⊢; simp at h ⊢
    obtain ⟨gr, G', σ', h, h1, rfl, rfl⟩ := h; exists gr, G', σ'; split_ands'
    apply ih; assumption'
  all_goals introv TL Cq0 Ct1 Ct2 h Hfuel
  rotate_right; next => simp only [check_stp2.go, excs] at h
  all_goals cases fuel' <;> simp [sub_size, sub_size'] at Hfuel; rename_i fuel'
  next => -- bool
    simpa [check_stp2.go] using h
  next => -- top
    simpa [check_stp2.go] using h
  next h1 => -- tvar refl
    simp only [check_stp2.go] at h ⊢; simpa [h1] using h
  next h1 h2 ih => -- tvar: exposure
    simp [check_stp2.go, h1, h2] at h ⊢; simp only [excs] at h ⊢
    obtain ⟨⟨Tx, qx, bn⟩, _, ⟨h3, rfl⟩, h⟩ := h; simp at h
    obtain ⟨_, ⟨rfl, rfl⟩, h⟩ := h; simp [h3, and_assoc]
    have h3' := TL h3; apply ih; assumption'
    · c_extend h3'.1; have := (List.getElem?_eq_some.1 h3).1; omega
    simp [sub_size, sub_size']; apply tenv.sub_sizes_spec at h3
    simp [h3] at Hfuel; rw [subsize_prefix h3'.1] at Hfuel; omega
  next ih1 ih2 => -- tref
    simp only [check_stp2.go, excs] at h ⊢
    obtain ⟨-, _, ⟨h1, rfl⟩, ⟨gr1, G1⟩, _, S1, ⟨gr2, G2⟩, _, S2, h⟩ := h
    simp [h1]; simp [and_assoc] at S2 h
    obtain ⟨rfl, rfl, G3, _, Q1, G4, _, Q2, rfl, rfl, rfl⟩ := h
    specialize ih1 (fuel' := fuel') TL _ Ct1.1 Ct2.1 S1 _
    simp [sets]; simp [sub_size]; omega; specialize @ih2 G1
    replace S1 := (check_stp2_sound TL S1 (by simp [sets]) Ct1.1 Ct2.1).2.1
    replace TL := S1.on_telescope TL; simp [←S1.1, S1.on_subsize] at ih2
    specialize ih2 (fuel' := fuel') TL _ Ct2.1 Ct1.1 S2 _
    simp [sets]; simp [sub_size]; omega; simp [ih1, and_assoc, ih2, Q1, Q2]
  next G q0 gs _ T1a _ _ _ T1b q1b _ _ _ ih1 ih2 => -- tfun
    simp only [check_stp2.go, excs] at h ⊢
    obtain ⟨⟨gr1, G1⟩, _, S1, G2, _, Q1, ⟨gr2, G3⟩, _, S2, G4, _, Q2, h⟩ := h
    simp at Q1 S2 Q2 h; obtain ⟨T0, _, ⟨⟨b0, h1⟩, rfl⟩, h⟩ := h
    replace TL: telescope (G ++ [(.TTop, q0, .self)]) := by
      apply telescope_extend; simp!; assumption'
    have Ct2: closed_ty 0 (‖G‖ + 1) [#0 ↦ %‖G‖] T1b := by apply subst_tighten; c_extend Ct2.1; simp
    have Ct1: closed_ty 0 (‖G‖ + 1) [#0 ↦ %‖G‖] T1a := by apply subst_tighten; c_extend Ct1.1; simp
    simp [sub_size] at ih1; specialize ih1 (fuel' := fuel') TL _ Ct2 Ct1 S1 _
    simp [sets]; omega; simp [ih1, and_assoc]; apply check_stp2_sound at S1
    assumption'; simp at S1; specialize S1 (by simp [sets]) Ct2 Ct1
    obtain ⟨Hgr1, S1, -⟩ := S1; simp [Q1, and_assoc]; replace TL := S1.on_telescope TL
    replace Q1: ctx_grow G1 G2 (gs ∪ {‖G‖}) := by
      split at Q1; simp [excs] at Q1; obtain ⟨rfl, rfl⟩ := Q1; simp [ctx_grow]
      apply check_qtp_wfctx at Q1; assumption'
    replace TL := Q1.on_telescope TL; replace Q1 := S1.trans Q1; clear S1 ih1
    specialize @ih2 gr1 G2; let elem := ([#0↦%‖G‖] T1b, [#0↦%‖G‖] q1b, binding.var)
    replace TL: telescope (G2 ++ [elem]) := by
      simp [elem]; apply telescope_extend; assumption'; simpa [←Q1.1]
      simp [←Q1.1]; apply subst_tighten; clear Ct2; c_extend Ct2.2.2.1; simp [sets]
    clear Ct1 Ct2; simp [←Q1.1] at ih2; replace Q1 := Q1.append (g := [elem])
    simp [elem] at TL Q1; clear elem; simp [Q1.on_subsize] at ih2
    specialize ih2 (fuel' := fuel') TL _ _ _ S2 _; simp [sets]
    · clear ih2; repeat apply subst_tighten
      c_extend Ct1.2.1; omega; split_ands; simp!; apply Finset.union_subset
      simp [sets]; c_extend; simp; intro h; absurd h; c_free; simp; omega
    · repeat apply subst_tighten
      c_extend Ct2.2.1; omega; simp; simp; omega
    · clear ih2; simp [sub_size]
      rw [←ty.subst_open_chain #1 %(‖G‖+1), ty.open_subst_comm, ty.subst_preserves_subsize]
      omega; simp; apply Finset.union_subset; simp [sets]; c_extend; simp
      simp; intro; c_free; simp!; simp; c_free Ct1.2.1
    simpa [ih2, and_assoc, Q2, h1]
  next G q0 gs _ T1a _ _ _ T1b q1b _ _ ih2 => -- tall
    simp only [check_stp2.go, excs] at h ⊢
    obtain ⟨-, _, ⟨rfl, rfl⟩, G2, _, Q1, ⟨gr2, G3⟩, _, S2, G4, _, Q2, h⟩ := h
    simp at Q1 S2 Q2 h; obtain ⟨T0, _, ⟨⟨b0, h1⟩, rfl⟩, h⟩ := h
    let G1 := G ++ [(.TTop, q0, .self)]; replace TL: telescope G1 := by
      apply telescope_extend; simp!; assumption'
    simp [and_assoc, Q1]; replace Q1: ctx_grow G1 G2 (gs ∪ {‖G‖}) := by
      split at Q1; simp [excs] at Q1; obtain ⟨rfl, rfl⟩ := Q1; simp [ctx_grow, G1]
      apply check_qtp_wfctx at Q1; assumption'
    replace TL := Q1.on_telescope TL
    specialize @ih2 G2; let elem := ([#0↦%‖G‖] T1a, [#0↦%‖G‖] q1b, binding.tvar)
    replace TL: telescope (G2 ++ [elem]) := by
      simp [elem]; apply telescope_extend; assumption'
      simp [←Q1.1, G1]; apply subst_tighten; c_extend Ct2.1; simp
      simp [←Q1.1, G1]; apply subst_tighten; c_extend Ct2.2.2.1; simp [sets]
    simp [←Q1.1] at ih2; replace Q1 := Q1.append (g := [elem])
    simp [elem] at TL Q1; clear elem; simp [Q1.on_subsize, G1] at ih2
    specialize ih2 (fuel' := fuel') TL _ _ _ S2 _; simp [sets]
    · clear ih2; repeat apply subst_tighten
      c_extend Ct1.2.1; omega; simp; simp; omega
    · clear ih2; repeat apply subst_tighten
      c_extend Ct2.2.1; omega; simp; simp; omega
    · clear ih2; simp [sub_size]; omega
    simpa [ih2, and_assoc, Q2, h1]

lemma ql.self_subst_equiv (hf: G[f]? = some (Tf, qf, .self))
  (Cqf: closed_ql false 0 ‖G‖ qf) (C: closed_ql true 0 ‖G‖ q) (hgs: f ∉ gs):
  qtp G q ([%f ↦ qf] q) gs ∧ qtp G ([%f ↦ qf] q) q gs :=
by
  simp [subst]; split; swap
  next h => simp [h]; apply q_sub; simp; assumption
  next h =>
    have: qtp G (q \ {%f}) (q \ {%f}) gs := by
      apply q_sub; simp; simp [closed_ql]; trans q; simp; assumption
    have: q = q \ {%f} ∪ {%f} := (by simp [h]); split_ands
    · nth_rw 1 [this]; apply q_cong; assumption; apply q_var; assumption'
    · nth_rw 2 [this]; apply q_cong; assumption
      have: qf = qf \ {✦} := by ext; simp; rintro h rfl; absurd h; c_free;
      rw [this]; apply q_self; assumption'; c_extend;

lemma ty.self_subst_equiv (hf: G[f]? = some (Tf, qf, .self))
  (Cqf: closed_ql false 0 ‖G‖ qf) (C: closed_ty 0 ‖G‖ T) (hgs: f ∉ gs)
  (hocc: occurs .no_contravariant T %f ∨ occurs .no_covariant T %f):
  stp G T q0 ∅ ([%f ↦ qf] T) gs ∧ stp G ([%f ↦ qf] T) q0 ∅ T gs :=
by
  induction T using ty.induct' generalizing G q0
  next => simp; apply s_refl; assumption
  next => simp; apply s_refl; assumption
  next T q ih => -- TRef
    replace hocc: occurs .none (.TRef T q) %f := by
      simp!; simp! at hocc; assumption
    simp only [instSubstTyQl, ty.subst_free' hocc]; simp
    apply s_refl; assumption
  next T1 q1 T2 q2 ih1 ih2 => -- TFun
    simp! at hocc; have L := (List.getElem?_eq_some.1 hf).1
    have L1: f ≠ ‖G‖ := (by omega); have L2: f ≠ ‖G‖ + 1 := (by omega);
    -- T1
    let T1' := [#0 ↦ %‖G‖] T1
    replace ih1: ∀ a, stp (G ++ [a]) T1' {✦} ∅ ([%f↦qf] T1') gs ∧
                      stp (G ++ [a]) ([%f↦qf] T1') {✦} ∅ T1' gs := by
      intros; simp [T1']; apply ih1; simp; simp only [L, List.getElem?_append_left, hf]
      c_extend; simp; apply subst_tighten; c_extend C.1; simp
      obtain h | h := hocc <;> simp [h, L1]
    have HT1: [%f↦qf] T1' = [#0↦%‖G‖] [%f↦qf] T1 := by
      simp; rw [ty.open_subst_comm]; simp; omega; intro; c_free; simp!; simp
    rw [HT1] at ih1; simp only [instSubstTyQl, T1'] at ih1; clear HT1 T1'
    -- T2
    let T2' := [#0 ↦ %‖G‖] [#1 ↦ %(‖G‖ + 1)] T2
    replace ih2: ∀ a b, stp (G ++ [a, b]) T2' {✦} ∅ ([%f↦qf] T2') gs ∧
                        stp (G ++ [a, b]) ([%f↦qf] T2') {✦} ∅ T2' gs := by
      intros; simp [T2']; apply ih2; simp; simp only [L, List.getElem?_append_left, hf]
      c_extend; simp; repeat apply subst_tighten
      c_extend C.2.1; simp; simp; obtain h | h := hocc <;> simp [h, L1, L2]
    have HT2: [%f↦qf] T2' = [#0↦%‖G‖] [#1 ↦ %(‖G‖+1)] [%f↦qf] T2 := by
      simp; rw [ty.open_subst_comm, ty.open_subst_comm]
      simp; omega; intro; c_free; simp!; simp; simp; omega; intro; c_free; simp!; simp
    rw [HT2] at ih2; simp only [instSubstTyQl, T2'] at ih2; clear HT2 T2'
    -- q1
    let q1' := [#0 ↦ %‖G‖] q1
    have h1: ∀ a, qtp (G ++ [a]) q1' ([%f ↦ qf] q1') gs ∧
                  qtp (G ++ [a]) ([%f ↦ qf] q1') q1' gs := by
      intros; simp [q1']; apply ql.self_subst_equiv; simp only [L, List.getElem?_append_left, hf]
      rfl; c_extend; apply subst_tighten; c_extend C.2.2.1; simp [sets]; assumption
    have HQ1: [%f ↦ qf] q1' = [#0 ↦ %‖G‖] [%f ↦ qf] q1 := by
      simp [q1']; rw [ql.subst_comm]; c_free; simp; omega; simp
    rw [HQ1] at h1; simp only [instSubstQlId, q1'] at h1; clear HQ1 q1'
    -- q2
    let q2' := [#0 ↦ %‖G‖] [#1 ↦ %(‖G‖+1)] q2
    have h2: ∀ a b, qtp (G ++ [a, b]) q2' ([%f ↦ qf] q2') gs ∧
                    qtp (G ++ [a, b]) ([%f ↦ qf] q2') q2' gs := by
      intros; simp [q2']; apply ql.self_subst_equiv; simp only [L, List.getElem?_append_left, hf]
      rfl; c_extend; repeat apply subst_tighten
      c_extend C.2.2.2.1; simp [sets]; simp [sets]; assumption
    have HQ2: [%f ↦ qf] q2' = [#0 ↦ %‖G‖] [#1 ↦ %(‖G‖+1)] [%f ↦ qf] q2 := by
      simp [q2']; rw [ql.subst_comm (x1 := %f), ql.subst_comm (x1 := %f)]
      c_free; simp; omega; simp; c_free; simp; omega; simp
    rw [HQ2] at h2; simp only [instSubstQlId, q2'] at h2; clear HQ2 q2'
    -- closedness
    have C': closed_ty 0 ‖G‖ ([%f ↦ qf] .TFun T1 q1 T2 q2) := by
      simp! at C ⊢; split_ands
      · rw [closedty_subst]; simp [C]; assumption; simp!; simpa
      · rw [closedty_subst]; simp [C]; assumption; simp!; simpa
      · rw [closedql_subst]; simp [C]; c_extend; simpa
      · rw [closedql_subst]; simp [C]; c_extend; simpa
      · simp [subst]; rintro (h | ⟨-, h⟩); simp [h] at C; simp [C]; absurd h; c_free;
      · rw [occurs_subst]; simp [C]; intro; c_free; simp!
      · rw [occurs_subst]; simp [C]; intro; c_free; simp!
    -- final
    clear L L1 L2 hocc; simp; split_ands
    · apply s_fun (gr1 := ∅) (gr2 := ∅); assumption'; rotate_left 4
      simp; simp; simp [sets]; apply (ih1 _).2; right; simp; apply (h1 _).2
      simp; apply (ih2 _ _).1; simp; apply (h2 _ _).1
    · apply s_fun (gr1 := ∅) (gr2 := ∅); assumption'; rotate_left 4
      simp; simp; simp [sets]; apply (ih1 _).1; right; simp; apply (h1 _).1
      simp; apply (ih2 _ _).2; simp; apply (h2 _ _).2
  next => simp! at hocc; simp [hocc]; apply s_refl; assumption
  next T1 q1 T2 q2 ih1 ih2 => -- TAll
    simp! at hocc; have L := (List.getElem?_eq_some.1 hf).1
    have L1: f ≠ ‖G‖ := (by omega); have L2: f ≠ ‖G‖ + 1 := (by omega);
    -- T1
    let T1' := [#0 ↦ %‖G‖] T1
    replace ih1: ∀ a, stp (G ++ [a]) T1' {✦} ∅ ([%f↦qf] T1') gs ∧
                      stp (G ++ [a]) ([%f↦qf] T1') {✦} ∅ T1' gs := by
      intros; simp [T1']; apply ih1; simp; simp only [L, List.getElem?_append_left, hf]
      c_extend; simp; apply subst_tighten; c_extend C.1; simp
      obtain h | h := hocc <;> simp [h, L1]
    have HT1: [%f↦qf] T1' = [#0↦%‖G‖] [%f↦qf] T1 := by
      simp; rw [ty.open_subst_comm]; simp; omega; intro; c_free; simp!; simp
    rw [HT1] at ih1; simp only [instSubstTyQl, T1'] at ih1; clear HT1 T1'
    -- T2
    let T2' := [#0 ↦ %‖G‖] [#1 ↦ %(‖G‖ + 1)] T2
    replace ih2: ∀ a b, stp (G ++ [a, b]) T2' {✦} ∅ ([%f↦qf] T2') gs ∧
                        stp (G ++ [a, b]) ([%f↦qf] T2') {✦} ∅ T2' gs := by
      intros; simp [T2']; apply ih2; simp; simp only [L, List.getElem?_append_left, hf]
      c_extend; simp; repeat apply subst_tighten
      c_extend C.2.1; simp; simp; obtain h | h := hocc <;> simp [h, L1, L2]
    have HT2: [%f↦qf] T2' = [#0↦%‖G‖] [#1 ↦ %(‖G‖+1)] [%f↦qf] T2 := by
      simp; rw [ty.open_subst_comm, ty.open_subst_comm]
      simp; omega; intro; c_free; simp!; simp; simp; omega; intro; c_free; simp!; simp
    rw [HT2] at ih2; simp only [instSubstTyQl, T2'] at ih2; clear HT2 T2'
    -- q1
    let q1' := [#0 ↦ %‖G‖] q1
    have h1: ∀ a, qtp (G ++ [a]) q1' ([%f ↦ qf] q1') gs ∧
                  qtp (G ++ [a]) ([%f ↦ qf] q1') q1' gs := by
      intros; simp [q1']; apply ql.self_subst_equiv; simp only [L, List.getElem?_append_left, hf]
      rfl; c_extend; apply subst_tighten; c_extend C.2.2.1; simp [sets]; assumption
    have HQ1: [%f ↦ qf] q1' = [#0 ↦ %‖G‖] [%f ↦ qf] q1 := by
      simp [q1']; rw [ql.subst_comm]; c_free; simp; omega; simp
    rw [HQ1] at h1; simp only [instSubstQlId, q1'] at h1; clear HQ1 q1'
    -- q2
    let q2' := [#0 ↦ %‖G‖] [#1 ↦ %(‖G‖+1)] q2
    have h2: ∀ a b, qtp (G ++ [a, b]) q2' ([%f ↦ qf] q2') gs ∧
                    qtp (G ++ [a, b]) ([%f ↦ qf] q2') q2' gs := by
      intros; simp [q2']; apply ql.self_subst_equiv; simp only [L, List.getElem?_append_left, hf]
      rfl; c_extend; repeat apply subst_tighten
      c_extend C.2.2.2.1; simp [sets]; simp [sets]; assumption
    have HQ2: [%f ↦ qf] q2' = [#0 ↦ %‖G‖] [#1 ↦ %(‖G‖+1)] [%f ↦ qf] q2 := by
      simp [q2']; rw [ql.subst_comm (x1 := %f), ql.subst_comm (x1 := %f)]
      c_free; simp; omega; simp; c_free; simp; omega; simp
    rw [HQ2] at h2; simp only [instSubstQlId, q2'] at h2; clear HQ2 q2'
    -- closedness
    have C': closed_ty 0 ‖G‖ ([%f ↦ qf] .TFun T1 q1 T2 q2) := by
      simp! at C ⊢; split_ands
      · rw [closedty_subst]; simp [C]; assumption; simp!; simpa
      · rw [closedty_subst]; simp [C]; assumption; simp!; simpa
      · rw [closedql_subst]; simp [C]; c_extend; simpa
      · rw [closedql_subst]; simp [C]; c_extend; simpa
      · simp [subst]; rintro (h | ⟨-, h⟩); simp [h] at C; simp [C]; absurd h; c_free;
      · rw [occurs_subst]; simp [C]; intro; c_free; simp!
      · rw [occurs_subst]; simp [C]; intro; c_free; simp!
    -- final
    clear L L1 L2 hocc; simp; split_ands
    · apply s_all (gr2 := ∅); assumption'; rotate_left 4
      simp; simp [sets]; apply (ih1 _).2; right; simp; apply (h1 _).2
      simp; apply (ih2 _ _).1; simp; apply (h2 _ _).1
    · apply s_all (gr2 := ∅); assumption'; rotate_left 4
      simp; simp [sets]; apply (ih1 _).1; right; simp; apply (h1 _).1
      simp; apply (ih2 _ _).2; simp; apply (h2 _ _).2

lemma unpack_self_equiv G gs:
  unpack_self T1 q0 = T1' → gs ⊆ Finset.range ‖G‖ →
  closed_ty 0 ‖G‖ T1 → closed_ql true 0 ‖G‖ q0 →
  stp G T1 q0 ∅ T1' gs ∧ stp G T1' q0 ∅ T1 gs :=
by
  intro h hgs C Cq0; simp [unpack_self] at h; split at h; subst T1'
  simp [C]; apply s_refl; assumption; apply closedql_fr_tighten at Cq0; assumption'
  split at h <;> subst T1'; rotate_right; simp [C]; apply s_refl; assumption
  next T1 q1 T2 q2 => -- TFun
    -- T1
    let T1' := [#0 ↦ %‖G‖] T1
    have h1: stp (G ++ [(.TTop, q0, .self)]) T1' {✦} ∅ ([%‖G‖ ↦ q0] T1') gs ∧
             stp (G ++ [(.TTop, q0, .self)]) ([%‖G‖ ↦ q0] T1') {✦} ∅ T1' gs := by
      simp [T1']; apply ty.self_subst_equiv; simp; rfl; c_extend;
      apply subst_tighten; c_extend C.1; simp; intro h; specialize hgs h; simp at hgs
      simp; right; simp! at C; simp [C]; c_free C.1
    have HT1: [%‖G‖ ↦ q0] T1' = [#0 ↦ %‖G‖] [#0 ↦ q0] T1 := by
      simp [T1']; rw [ty.subst_open_chain, ty.open_free]
      rw [occurs_subst]; simp; intro; c_free; simp!; c_free C.1
    rw [HT1] at h1; simp [T1'] at h1; clear HT1 T1'
    -- T1
    let T2' := [#0 ↦ %‖G‖] [#1 ↦ %(‖G‖+1)] T2
    have h2: ∀ a, stp (G ++ [(.TTop, q0, .self), a]) T2' {✦} ∅ ([%‖G‖ ↦ q0] T2') gs ∧
                  stp (G ++ [(.TTop, q0, .self), a]) ([%‖G‖ ↦ q0] T2') {✦} ∅ T2' gs := by
      intros; simp [T2']; apply ty.self_subst_equiv; simp [List.getElem_append_right]
      rfl; c_extend; repeat apply subst_tighten
      c_extend C.2.1; simp; simp; intro h; specialize hgs h; simp at hgs
      simp; left; simp! at C; simp [C]; c_free C.2.1
    have HT2: [%‖G‖ ↦ q0] T2' = [#0 ↦ %‖G‖] [#1 ↦ %(‖G‖+1)] [#0 ↦ q0] T2 := by
      simp [T2']; rw [ty.subst_open_chain, ty.open_subst_comm, ty.open_free (x := #0)]
      rw [occurs_subst]; simp; intro; c_free; simp!; simp; intro; c_free; simp!
      simp; simp; c_free C.2.1
    rw [HT2] at h2; simp only [instSubstTyQl, T2'] at h2; clear HT2 T2'
    -- q1
    have h3: ∀ a, qtp (G ++ [a]) ([#0 ↦ %‖G‖] q1) ([#0 ↦ %‖G‖] q1) gs := by
      intro; apply q_sub; simp; simp; apply subst_tighten; c_extend C.2.2.1; simp [sets]
    -- q2
    let q2' := [#0 ↦ %‖G‖] [#1 ↦ %(‖G‖+1)] q2
    have h4: ∀ a, qtp (G ++ [(.TTop, q0, .self), a]) q2' ([%‖G‖ ↦ q0] q2') gs ∧
                  qtp (G ++ [(.TTop, q0, .self), a]) ([%‖G‖ ↦ q0] q2') q2' gs := by
      intros; simp [q2']; apply ql.self_subst_equiv; simp [List.getElem_append_right]
      rfl; c_extend; repeat apply subst_tighten
      c_extend C.2.2.2.1; simp [sets]; simp [sets]; intro h; specialize hgs h; simp at hgs
    have HQ2: [%‖G‖ ↦ q0] q2' = [#0 ↦ %‖G‖] [#1 ↦ %(‖G‖+1)] [#0 ↦ q0] q2 := by
      simp [q2']; rw [ql.subst_chain, ql.subst_comm]; rotate_left
      c_free; simp; simp; simp [subst]; c_free C.2.2.2.1
      generalize hq2': [#1↦{%(‖G‖ + 1)}] [#0↦q0] q2 = q2'; simp [subst]
      have: #0 ∉ q2' := by subst q2'; simp [subst]; intro; c_free;
      simp [this]
    rw [HQ2] at h4; simp only [instSubstQlId, q2'] at h4; clear HQ2 q2'
    -- closedness
    have C': closed_ty 0 ‖G‖ (.TFun ([#0↦q0] T1) q1 ([#0↦q0] T2) ([#0↦q0] q2)) := by
      simp! at C ⊢; split_ands
      · rw [closedty_subst]; simp [C]; assumption; simp!; simp
      · rw [closedty_subst]; simp [C]; assumption; simp!; simp
      · simp [C]
      · rw [closedql_subst]; simp [C]; c_extend; simp
      · intro h; simp [h] at C; simp [C]
      · rw [occurs_subst]; simp; intro; c_free; simp!
      · rw [occurs_subst]; simp; intro; c_free; simp!
    -- final
    split_ands
    · apply s_fun (gr1 := ∅) (gr2 := ∅); rotate_left 4; simp; simp; simp [sets]; assumption'
      simp; apply h1.2; right; simp; apply h3; simp; apply (h2 _).1; simp; apply (h4 _).1
    · apply s_fun (gr1 := ∅) (gr2 := ∅); rotate_left 4; simp; simp; simp [sets]; assumption'
      simp; apply h1.1; right; simp; apply h3; simp; apply (h2 _).2; simp; apply (h4 _).2
  next T1 q1 T2 q2 => -- TAll
    -- T1
    let T1' := [#0 ↦ %‖G‖] T1
    have h1: stp (G ++ [(.TTop, q0, .self)]) T1' {✦} ∅ ([%‖G‖ ↦ q0] T1') gs ∧
             stp (G ++ [(.TTop, q0, .self)]) ([%‖G‖ ↦ q0] T1') {✦} ∅ T1' gs := by
      simp [T1']; apply ty.self_subst_equiv; simp; rfl; c_extend;
      apply subst_tighten; c_extend C.1; simp; intro h; specialize hgs h; simp at hgs
      simp; right; simp! at C; simp [C]; c_free C.1
    have HT1: [%‖G‖ ↦ q0] T1' = [#0 ↦ %‖G‖] [#0 ↦ q0] T1 := by
      simp [T1']; rw [ty.subst_open_chain, ty.open_free]
      rw [occurs_subst]; simp; intro; c_free; simp!; c_free C.1
    rw [HT1] at h1; simp [T1'] at h1; clear HT1 T1'
    -- T1
    let T2' := [#0 ↦ %‖G‖] [#1 ↦ %(‖G‖+1)] T2
    have h2: ∀ a, stp (G ++ [(.TTop, q0, .self), a]) T2' {✦} ∅ ([%‖G‖ ↦ q0] T2') gs ∧
                  stp (G ++ [(.TTop, q0, .self), a]) ([%‖G‖ ↦ q0] T2') {✦} ∅ T2' gs := by
      intros; simp [T2']; apply ty.self_subst_equiv; simp [List.getElem_append_right]
      rfl; c_extend; repeat apply subst_tighten
      c_extend C.2.1; simp; simp; intro h; specialize hgs h; simp at hgs
      simp; left; simp! at C; simp [C]; c_free C.2.1
    have HT2: [%‖G‖ ↦ q0] T2' = [#0 ↦ %‖G‖] [#1 ↦ %(‖G‖+1)] [#0 ↦ q0] T2 := by
      simp [T2']; rw [ty.subst_open_chain, ty.open_subst_comm, ty.open_free (x := #0)]
      rw [occurs_subst]; simp; intro; c_free; simp!; simp; intro; c_free; simp!
      simp; simp; c_free C.2.1
    rw [HT2] at h2; simp only [instSubstTyQl, T2'] at h2; clear HT2 T2'
    -- q1
    have h3: ∀ a, qtp (G ++ [a]) ([#0 ↦ %‖G‖] q1) ([#0 ↦ %‖G‖] q1) gs := by
      intro; apply q_sub; simp; simp; apply subst_tighten; c_extend C.2.2.1; simp [sets]
    -- q2
    let q2' := [#0 ↦ %‖G‖] [#1 ↦ %(‖G‖+1)] q2
    have h4: ∀ a, qtp (G ++ [(.TTop, q0, .self), a]) q2' ([%‖G‖ ↦ q0] q2') gs ∧
                  qtp (G ++ [(.TTop, q0, .self), a]) ([%‖G‖ ↦ q0] q2') q2' gs := by
      intros; simp [q2']; apply ql.self_subst_equiv; simp [List.getElem_append_right]
      rfl; c_extend; repeat apply subst_tighten
      c_extend C.2.2.2.1; simp [sets]; simp [sets]; intro h; specialize hgs h; simp at hgs
    have HQ2: [%‖G‖ ↦ q0] q2' = [#0 ↦ %‖G‖] [#1 ↦ %(‖G‖+1)] [#0 ↦ q0] q2 := by
      simp [q2']; rw [ql.subst_chain, ql.subst_comm]; rotate_left
      c_free; simp; simp; simp [subst]; c_free C.2.2.2.1
      generalize hq2': [#1↦{%(‖G‖ + 1)}] [#0↦q0] q2 = q2'; simp [subst]
      have: #0 ∉ q2' := by subst q2'; simp [subst]; intro; c_free;
      simp [this]
    rw [HQ2] at h4; simp only [instSubstQlId, q2'] at h4; clear HQ2 q2'
    -- closedness
    have C': closed_ty 0 ‖G‖ (.TFun ([#0↦q0] T1) q1 ([#0↦q0] T2) ([#0↦q0] q2)) := by
      simp! at C ⊢; split_ands
      · rw [closedty_subst]; simp [C]; assumption; simp!; simp
      · rw [closedty_subst]; simp [C]; assumption; simp!; simp
      · simp [C]
      · rw [closedql_subst]; simp [C]; c_extend; simp
      · intro h; simp [h] at C; simp [C]
      · rw [occurs_subst]; simp; intro; c_free; simp!
      · rw [occurs_subst]; simp; intro; c_free; simp!
    -- final
    split_ands
    · apply s_all (gr2 := ∅); rotate_left 4; simp; simp [sets]; assumption'
      simp; apply h1.2; right; simp; apply h3; simp; apply (h2 _).1; simp; apply (h4 _).1
    · apply s_all (gr2 := ∅); rotate_left 4; simp; simp [sets]; assumption'
      simp; apply h1.1; right; simp; apply h3; simp; apply (h2 _).2; simp; apply (h4 _).2

lemma check_stp_sound (TL: telescope G) (Hgs: gs ⊆ Finset.range ‖G‖):
  check_stp G q0 T1 T2 gs σ1 = .ok (gr, G') σ2 →
  closed_ql true 0 ‖G‖ q0 → closed_ty 0 ‖G‖ T1 → closed_ty 0 ‖G‖ T2 →
  closed_ql false 0 ‖G‖ gr ∧ ctx_grow G G' gs ∧ stp G' T1 q0 gr T2 gs :=
by
  intro h Cq0 Ct1 Ct2; simp only [check_stp, excs] at h
  generalize h1: unpack_self T1 q0 = T1' at h
  apply unpack_self_equiv at h1; specialize h1 Hgs Ct1 Cq0
  have Ct1' := (stp_closed h1.1).2.1
  apply check_stp2_sound at h; specialize h Cq0 Ct1' Ct2; simp [h]; assumption'
  convert_to stp _ _ _ (∅ ∪ gr) _ _; simp
  apply s_trans; apply h.2.1.on_stp h1.1; simp; apply h.2.2

-- unpack_argself

lemma unpack_argself_sound_gen:
  closed_ty 1 ‖G‖ T1 → closed_ql true 0 ‖G‖ qf → occurs .no_covariant T1 #0 →
  unpack_argself T1 qf σ1 = .ok T1' σ2 →
  gs ⊆ Finset.range ‖G‖ →
  closed_ty 0 ‖G‖ T1' ∧
    stp (G ++ [(.TTop, qf, .self)]) T1' {✦} ∅ ([#0 ↦ %‖G‖] T1) gs :=
by
  intro Ct Cq hocc h Hgs; simp only [unpack_argself] at h; split at h; swap
  simp only [excs] at h; obtain ⟨-, _, ⟨H2, rfl⟩, rfl, rfl⟩ := h
  next =>
    have: closed_ty 0 ‖G‖ T1 := by
      apply closedty_bv_tighten; assumption'
    split_ands'; rw [ty.open_free H2]; apply s_refl; c_extend;
  next h1 =>
    simp only [excs] at h; obtain ⟨rfl, rfl⟩ := h; split_ands
    simp; apply subst_tighten; assumption; simp! [Cq, h1]; simp
    rw [←ty.subst_open_chain #0 %‖G‖]; apply closedql_fr_tighten at Cq; assumption'
    have: (G ++ [(.TTop, qf, .self)])[‖G‖]? = some (.TTop, qf, .self) := by simp
    apply ty.self_subst_equiv (q0 := {✦}) (T := [#0 ↦ %‖G‖] T1) (gs := gs) at this
    specialize this _ _ _ _; c_extend; apply subst_tighten; c_extend; simp
    intro h; specialize Hgs h; simp at Hgs; simp [hocc]; right; c_free;
    simp at this; apply this.2; c_free;

lemma unpack_argself_sound_fun:
  closed_ty 0 ‖G‖ (.TFun T1 q1 T2 q2) →
  closed_ql true 0 ‖G‖ qf →
  unpack_argself T1 qf σ1 = .ok T1' σ2 →
  gs ⊆ Finset.range ‖G‖ →
  closed_ty 0 ‖G‖ T1' ∧
    stp G (.TFun T1 q1 T2 q2) qf ∅ (.TFun T1' q1 T2 q2) gs :=
by
  intro Ct Cq h Hgs; simp! at Ct; apply unpack_argself_sound_gen at h
  specialize h Hgs; simp [h]; fapply s_fun; exact ∅; exact ∅
  · rw [ty.open_free]; simp [h.2]; c_free h.1
  · right; apply q_sub; simp; simp; apply subst_tighten
    c_extend Ct.2.2.1; simp [sets]
  · simp; apply s_refl; repeat apply subst_tighten
    c_extend Ct.2.1; simp; simp
  · apply q_sub; simp; simp; repeat apply subst_tighten
    c_extend Ct.2.2.2.1; simp [sets]; simp [sets]
  simp; simp; simp [sets]; simpa!; simp!; split_ands''; c_extend; c_free;
  simp [Ct]; assumption; simp [Ct]

lemma unpack_argself_sound_all:
  closed_ty 0 ‖G‖ (.TAll T1 q1 T2 q2) →
  closed_ql true 0 ‖G‖ qf →
  unpack_argself T1 qf σ1 = .ok T1' σ2 →
  gs ⊆ Finset.range ‖G‖ →
  closed_ty 0 ‖G‖ T1' ∧
    stp G (.TAll T1 q1 T2 q2) qf ∅ (.TAll T1' q1 T2 q2) gs :=
by
  intro Ct Cq h Hgs; simp! at Ct; apply unpack_argself_sound_gen at h
  specialize h Hgs; simp [h]; fapply s_all; exact ∅
  · rw [ty.open_free]; simp [h.2]; c_free h.1
  · right; apply q_sub; simp; simp; apply subst_tighten
    c_extend Ct.2.2.1; simp [sets]
  · simp; apply s_refl; repeat apply subst_tighten
    c_extend Ct.2.1; simp; simp
  · apply q_sub; simp; simp; repeat apply subst_tighten
    c_extend Ct.2.2.2.1; simp [sets]; simp [sets]
  simp; simp [sets]; simpa!; simp!; split_ands''; c_extend; c_free;
  simp [Ct]; assumption; simp [Ct]

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
  next x y x' =>
    simp only [polsub, excs, and_assoc]; rintro ⟨-, _, h, rfl, rfl, rfl⟩; simp
    simp [heqxy, h1]; rintro rfl; simp! at h2; simp [subst]
    split; subst a; simp [h, h2]; split; simp [h1]; simp [h]
  next x _ T q =>
    simp! at h2; simp; simp only [polsub, excs]
    rintro ⟨-, _, ⟨h, rfl⟩, rfl, rfl⟩; simp [and_assoc, h1, h2, heqxy]; split_ands
    · intro h3; simp [subst] at h3; split at h3; subst a; simp [subst]
      apply occurs_none; simp [h2]; simp [subst, Ne.symm h3, h]
    · intro h3; simp [subst, h1] at h3; subst a; simp [h]
    · simp [subst]; split; subst a; simp [h1.1.symm]; simp [h, h2]
      rename_i h0; simp [h0, h1.1, Ne.symm h0, h]
  next pol x y T1 q1 T2 q2 IH1 IH2 =>
    intro h; simp! at h2; simp at h ⊢; simp only [polsub, excs] at h ⊢
    obtain ⟨T1', _, H1, T2', _, H2, h, rfl⟩ := h
    apply IH1 (a+1) (b+1) at H1; simp at H1; simp [H1]; clear IH1 H1
    rotate_left; simpa; simp; intro h; simp [h2 h]; simp [and_assoc]
    apply IH2 (a+2) (b+2) at H2; simp at H2; simp [H2]; clear IH2 H2
    rotate_left; simpa; simp; intro h; simp [h2 h]; simp [←h]; split_ands
    rw [ql.subst_comm']; congr; split; simp; simp [subst]; simp [h1]; simp; rintro rfl; simp [h2]
    rw [ql.subst_comm']; congr; split; simp; simp [subst]; simp [h1]; simp; rintro rfl; simp [h2]
  next pol x y T1 q1 T2 q2 IH1 IH2 =>
    intro h; simp! at h2; simp at h ⊢; simp only [polsub, excs] at h ⊢
    obtain ⟨T1', _, H1, T2', _, H2, h, rfl⟩ := h
    apply IH1 (a+1) (b+1) at H1; simp at H1; simp [H1]; clear IH1 H1
    rotate_left; simpa; simp; intro h; simp [h2 h]; simp [and_assoc]
    apply IH2 (a+2) (b+2) at H2; simp at H2; simp [H2]; clear IH2 H2
    rotate_left; simpa; simp; intro h; simp [h2 h]; simp [←h]; split_ands
    rw [ql.subst_comm']; congr; split; simp; simp [subst]; simp [h1]; simp; rintro rfl; simp [h2]
    rw [ql.subst_comm']; congr; split; simp; simp [subst]; simp [h1]; simp; rintro rfl; simp [h2]

lemma polsub_preserves_closedness:
  closed_ty bvs fvs t → y ∈ qdom true bvs fvs → x ≠ ✦ →
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
  · simp! only [excs] at H; obtain ⟨-, _, ⟨H, rfl⟩, rfl, rfl⟩ := H
    simp [C]; simp!; split_ands; rintro rfl; simp at H; split <;> simpa
    intro h; simpa [h] using H
  next T1 q1 T2 q2 IH1 IH2 =>
    simp! only [excs] at H; simp! at C; obtain ⟨T1', _, HT1, T2', _, HT2, rfl, rfl⟩ := H
    apply IH1 (bvs := bvs+1) at HT1; rotate_left; tauto; simpa; simpa
    apply IH2 (bvs := bvs+2) at HT2; rotate_left; tauto; simpa; simpa
    clear IH1 IH2; simp at HT1 HT2 ⊢
    obtain ⟨H1c, H1z, H1a, H1b⟩ := HT1; obtain ⟨H2c, H2z, H2a, H2b⟩ := HT2; split_ands
    · clear H1a H1b H2a H2b; simp!; split_ands'
      clear *- C Cy; simp [subst, sets]; rintro _ (⟨h, -⟩ | ⟨-, -, rfl⟩); tauto; simpa
      clear *- C Cy; simp [subst, sets]; rintro _ (⟨h, -⟩ | ⟨-, -, rfl⟩); tauto; simpa
      simp [subst, XF]; intro h; simp [h] at C; simp [C]
      apply H1z; simp; simp [C]; apply H2z; simp; simp [C]
    · simp!; introv hz h1 h2 h3 h4; clear H1a H1b H1c H2a H2b H2c; split_ands
      apply H1z; simpa; assumption
      obtain h2 | h2 := h2; simp [h2]; right; simp [subst]; simp [h2, hz]
      apply H2z; simpa; assumption
      obtain h4 | h4 := h4; simp [h4]; right; simp [subst]; simp [h4, hz]
    · rintro rfl; clear H1z H1b H2z H2b; simp at H1a H2a; simp!; cases pol
      all_goals simp at H1a H2a ⊢; split_ands'; simp [subst]
    · clear H1z H1a H2z H2a; intro h; obtain ⟨H1x, H1y⟩ := H1b h; obtain ⟨H2x, H2y⟩ := H2b h
      clear H1b H2b; split_ands; simp!; simp [H1x, H2x]; simp [subst, h]; clear H1x H2x
      cases pol <;> simp at H1y H2y ⊢ <;> simp!
      intro h1 h2 _; simp [H1y h1, H2y h2]; simpa [subst, Ne.symm h]
      intro h1 _ h2; simp [H1y h1, H2y h2]; simpa [subst, Ne.symm h]
  · simp! only [excs, and_assoc] at H; obtain ⟨-, _, H, rfl, rfl, rfl⟩ := H; simp [C]
    simp!; rintro rfl; simp [H]
  next T1 q1 T2 q2 IH1 IH2 =>
    simp! only [excs] at H; simp! at C; obtain ⟨T1', _, HT1, T2', _, HT2, rfl, rfl⟩ := H
    apply IH1 (bvs := bvs+1) at HT1; rotate_left; tauto; simpa; simpa
    apply IH2 (bvs := bvs+2) at HT2; rotate_left; tauto; simpa; simpa
    clear IH1 IH2; simp at HT1 HT2 ⊢
    obtain ⟨H1c, H1z, H1a, H1b⟩ := HT1; obtain ⟨H2c, H2z, H2a, H2b⟩ := HT2; split_ands
    · clear H1a H1b H2a H2b; simp!; split_ands'
      clear *- C Cy; simp [subst, sets]; rintro _ (⟨h, -⟩ | ⟨-, -, rfl⟩); tauto; simpa
      clear *- C Cy; simp [subst, sets]; rintro _ (⟨h, -⟩ | ⟨-, -, rfl⟩); tauto; simpa
      simp [subst, XF]; intro h; simp [h] at C; simp [C]
      apply H1z; simp; simp [C]; apply H2z; simp; simp [C]
    · simp!; introv hz h1 h2 h3 h4; clear H1a H1b H1c H2a H2b H2c; split_ands
      apply H1z; simpa; assumption
      obtain h2 | h2 := h2; simp [h2]; right; simp [subst]; simp [h2, hz]
      apply H2z; simpa; assumption
      obtain h4 | h4 := h4; simp [h4]; right; simp [subst]; simp [h4, hz]
    · rintro rfl; clear H1z H1b H2z H2b; simp at H1a H2a; simp!; cases pol
      all_goals simp at H1a H2a ⊢; split_ands'; simp [subst]
    · clear H1z H1a H2z H2a; intro h; obtain ⟨H1x, H1y⟩ := H1b h; obtain ⟨H2x, H2y⟩ := H2b h
      clear H1b H2b; split_ands; simp!; simp [H1x, H2x]; simp [subst, h]; clear H1x H2x
      cases pol <;> simp at H1y H2y ⊢ <;> simp!
      intro h1 h2 _; simp [H1y h1, H2y h2]; simpa [subst, Ne.symm h]
      intro h1 _ h2; simp [H1y h1, H2y h2]; simpa [subst, Ne.symm h]

lemma polsub_sound:
  closed_ty 0 ‖G‖ t →
  (∀G', G <+: G' → qtp G' {%x} {%y} gs) →
  polsub pol t %x %y σ1 = .ok t' σ2 →
  if pol then stp G t q0 ∅ t' gs else stp G t' q0 ∅ t gs :=
by
  intros C Q H; induction t using ty.induct' generalizing G t' pol q0 σ1 σ2
  · simp [polsub, excs] at H; obtain ⟨rfl, rfl⟩ := H
    split; apply s_refl; simp!; apply s_refl; simp!
  · simp [polsub, excs] at H; obtain ⟨rfl, rfl⟩ := H
    split; apply s_refl; simp!; apply s_refl; simp!
  · simp only [polsub, excs] at H; obtain ⟨-, _, ⟨H, rfl⟩, rfl, rfl⟩ := H
    split <;> apply s_refl <;> assumption
  next T1 q1 T2 q2 IH1 IH2 => -- TFun
    simp only [polsub, excs] at H; simp! at C
    have Cxy := by specialize Q G (by simp); apply qtp_closed at Q; simp [sets] at Q; exact Q
    obtain ⟨T1', _, HT1, T2', _, HT2, H, rfl⟩ := H; simp at HT1 HT2
    have HT1' := by
      apply polsub_preserves_closedness C.1 at HT1; exact HT1; simp [Cxy]; simp
    replace HT1 := fun a => by
      have := @IH1 (G := G ++ [a]) (q0 := {✦}); eapply this; rotate_right
      apply polsub_subst_comm #0 %‖G‖ at HT1
      convert HT1; simp; omega; simp; simp; apply subst_tighten
      c_extend C.1; simp; rintro _ ⟨_, rfl⟩; apply Q; simp
    clear IH1; have HT2' := by
      apply polsub_preserves_closedness C.2.1 at HT2; exact HT2; simp [Cxy]; simp
    replace HT2 := fun a b => by
      have := @IH2 (G := G ++ [a, b]) (q0 := {✦}); eapply this; rotate_right
      apply polsub_subst_comm #1 %(‖G‖+1) at HT2; apply polsub_subst_comm #0 %‖G‖ at HT2
      convert HT2; simp [subst]; omega; simp; simp [subst]; simp; omega; simp; simp
      repeat apply subst_tighten
      c_extend C.2.1; simp; simp; rintro _ ⟨_, rfl⟩; apply Q; simp
    clear IH2; obtain ⟨_, H1z, -⟩ := HT1'; obtain ⟨_, H2z, -⟩ := HT2'
    have C': closed_ty 0 ‖G‖ t' := by
      subst t'; clear HT1 HT2; simp!; split_ands''
      · rwa [closedql_subst]; split; simpa [sets]; simp [sets]; simpa
      · rwa [closedql_subst]; split; simpa [sets]; simp [sets]; simpa
      · simp [subst]; assumption
      · apply H1z; simp; assumption
      · apply H2z; simp; assumption
    have: closed_ql true 0 (‖G‖+1) [#0↦{%‖G‖}] q1 := by
      apply subst_tighten; c_extend C.2.2.1; simp [sets]
    have: closed_ql true 0 (‖G‖+2) [#0↦{%‖G‖}][#1↦{%(‖G‖ + 1)}] q2 := by
      (repeat apply subst_tighten); c_extend C.2.2.2.1; simp [sets]; simp [sets]
    cases pol <;> simp at H HT1 HT2 ⊢ <;> subst t'
    · fapply s_fun; exact ∅; exact ∅; rotate_left 4; simp; simp; simp [sets]; assumption'
      simp; apply HT1; right; swap; simp; apply HT2
      · have: x≠‖G‖ := (by omega); simp [ql.subst_comm (x2:=%x), this]
        apply q_subst; simpa; apply Q; simp
      · apply q_sub; simp [subst, sets]; clear *-; tauto; simpa
    · fapply s_fun; exact ∅; exact ∅; rotate_left 4; simp; simp; simp [sets]; assumption'
      simp; apply HT1; right; swap; simp; apply HT2
      · apply q_sub; simp [subst, sets]; clear *-; tauto; simpa
      · have xg: x ≠ ‖G‖ := (by omega); have xg1: x ≠ ‖G‖+1 := (by omega)
        simp [ql.subst_comm (x2 := %x), xg, xg1]
        apply q_subst; simpa; apply Q; simp
  · simp only [polsub, excs, and_assoc] at H; obtain ⟨-, _, _, rfl, rfl, rfl⟩ := H
    split <;> apply s_refl <;> assumption
  next T1 q1 T2 q2 IH1 IH2 => -- TAll
    simp only [polsub, excs] at H; simp! at C
    have Cxy := by specialize Q G (by simp); apply qtp_closed at Q; simp [sets] at Q; exact Q
    obtain ⟨T1', _, HT1, T2', _, HT2, H, rfl⟩ := H; simp at HT1 HT2
    have HT1' := by
      apply polsub_preserves_closedness C.1 at HT1; exact HT1; simp [Cxy]; simp
    replace HT1 := fun a => by
      have := @IH1 (G := G ++ [a]) (q0 := {✦}); eapply this; rotate_right
      apply polsub_subst_comm #0 %‖G‖ at HT1
      convert HT1; simp; omega; simp; simp; apply subst_tighten
      c_extend C.1; simp; rintro _ ⟨_, rfl⟩; apply Q; simp
    clear IH1; have HT2' := by
      apply polsub_preserves_closedness C.2.1 at HT2; exact HT2; simp [Cxy]; simp
    replace HT2 := fun a b => by
      have := @IH2 (G := G ++ [a, b]) (q0 := {✦}); eapply this; rotate_right
      apply polsub_subst_comm #1 %(‖G‖+1) at HT2; apply polsub_subst_comm #0 %‖G‖ at HT2
      convert HT2; simp [subst]; omega; simp; simp [subst]; simp; omega; simp; simp
      repeat apply subst_tighten
      c_extend C.2.1; simp; simp; rintro _ ⟨_, rfl⟩; apply Q; simp
    clear IH2; obtain ⟨_, H1z, -⟩ := HT1'; obtain ⟨_, H2z, -⟩ := HT2'
    have C': closed_ty 0 ‖G‖ t' := by
      subst t'; clear HT1 HT2; simp!; split_ands''
      · rwa [closedql_subst]; split; simpa [sets]; simp [sets]; simpa
      · rwa [closedql_subst]; split; simpa [sets]; simp [sets]; simpa
      · simp [subst]; assumption
      · apply H1z; simp; assumption
      · apply H2z; simp; assumption
    have: closed_ql true 0 (‖G‖+1) [#0↦{%‖G‖}] q1 := by
      apply subst_tighten; c_extend C.2.2.1; simp [sets]
    have: closed_ql true 0 (‖G‖+2) [#0↦{%‖G‖}][#1↦{%(‖G‖ + 1)}] q2 := by
      (repeat apply subst_tighten); c_extend C.2.2.2.1; simp [sets]; simp [sets]
    cases pol <;> simp at H HT1 HT2 ⊢ <;> subst t'
    · fapply s_all; exact ∅; rotate_left 4; simp; simp [sets]; assumption'
      simp; apply HT1; right; swap; simp; apply HT2
      · have: x≠‖G‖ := (by omega); simp [ql.subst_comm (x2:=%x), this]
        apply q_subst; simpa; apply Q; simp
      · apply q_sub; simp [subst, sets]; clear *-; tauto; simpa
    · fapply s_all; exact ∅; rotate_left 4; simp; simp [sets]; assumption'
      simp; apply HT1; right; swap; simp; apply HT2
      · apply q_sub; simp [subst, sets]; clear *-; tauto; simpa
      · have xg: x ≠ ‖G‖ := (by omega); have xg1: x ≠ ‖G‖+1 := (by omega)
        simp [ql.subst_comm (x2 := %x), xg, xg1]
        apply q_subst; simpa; apply Q; simp

lemma rm_contravariant_sound:
  closed_ty 0 ‖G‖ T2 → n < ‖G‖ →
  rm_contravariant T2 %n σ1 = .ok T2' σ2 →
  stp G T2 q0 ∅ T2' gs ∧ occurs .no_contravariant T2' %n :=
by
  intro Ct2 Hn h; simp [rm_contravariant] at h; split_ands
  · apply polsub_sound Ct2 at h; simpa
    intro G' HG; apply q_sub; simp; simp [sets]
    obtain ⟨G', rfl⟩ := HG; simp; omega
  · apply polsub_preserves_closedness Ct2 at h; simp at h
    simp [h]; simpa; simp

lemma avoid_subst_comm (a b: id) (h1: x ≠ b) (h2: x = a → occurs .none t b):
  avoid t x σ1 = .ok (t', g) σ2 →
  avoid ([a ↦ b] t) ([a ↦ b] x) σ1 = .ok ([a ↦ b] t', [a ↦ b] g) σ2 :=
by
  intro h; simp only [avoid] at h ⊢
  have heq: occurs .noneq ([a ↦ b] t) ([a ↦ b] x) ↔ occurs .noneq t x := by
    simp [h1, h2]; simp [subst]; split; subst a; simp [h2, h1.symm]; rintro -
    apply occurs_none; simp [h2]; rename_i h'; simp [Ne.symm h', h1, h']
  simp only [heq]; clear heq; split at h <;> rename_i h0 <;> simp [h0, -bind_pure_comp]
  · simp [excs] at h; obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h; simp [excs]; simp [subst]
  simp only [excs] at h ⊢; obtain ⟨v1, _, h1, h⟩ := h; simp [h1, -bind_pure_comp]
  clear v1 h1; split at h <;> simp [excs, -bind_pure_comp] at h ⊢
  next T1 q1 T2 q2 => -- TFun
    obtain ⟨T1', _, h3, T2', h4, rfl, rfl⟩ := h; simp! at h2
    simp; apply polsub_subst_comm (a+1) (b+1) at h3
    rotate_left; simpa; simp; rintro rfl; simp [h2]; conv at h3 => enter [1, 4]; simp [subst]
    simp [h3, and_assoc]; apply polsub_subst_comm (a+2) (b+2) at h4
    rotate_left; simpa; simp; rintro rfl; simp [h2]; conv at h4 => enter [1, 4]; simp [subst]
    simp [h4, and_assoc]; split_ands
    · rw [ql.subst_comm' (a := a+1)]; congr; simp [h1]; simp; rintro rfl; simp [h2]
    · rw [ql.subst_comm' (a := a+2)]; congr; simp [subst]; simp [h1]; simp; rintro rfl; simp [h2]
  next T1 q1 T2 q2 => -- TAll
    obtain ⟨T1', _, h3, T2', h4, rfl, rfl⟩ := h; simp! at h2
    simp; apply polsub_subst_comm (a+1) (b+1) at h3
    rotate_left; simpa; simp; rintro rfl; simp [h2]; conv at h3 => enter [1, 4]; simp [subst]
    simp [h3, and_assoc]; apply polsub_subst_comm (a+2) (b+2) at h4
    rotate_left; simpa; simp; rintro rfl; simp [h2]; conv at h4 => enter [1, 4]; simp [subst]
    simp [h4, and_assoc]; split_ands
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
  split at h; rotate_right; simp [excs] at h
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
      simp [subst]; intro h; simp [h] at c; simp [c]; assumption; simp [h1]; simp [h2]
    · simp!; split_ands; simp [h1]; simp [subst]; simp [h2]; simp [subst]
    · simp!; intros; split_ands
      apply h1z; simp; assumption; simp [subst]; tauto
      apply h2z; simp; assumption; simp [subst]; tauto
    · simp!; intros; split_ands
      apply h1z; simp; assumption; simp [subst]; tauto
      apply h2z; simp; assumption
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
      simp [subst]; intro h; simp [h] at c; simp [c]; assumption; simp [h1]; simp [h2]
    · simp!; split_ands; simp [h1]; simp [subst]; simp [h2]; simp [subst]
    · simp!; intros; split_ands
      apply h1z; simp; assumption; simp [subst]; tauto
      apply h2z; simp; assumption; simp [subst]; tauto
    · simp!; intros; split_ands
      apply h1z; simp; assumption; simp [subst]; tauto
      apply h2z; simp; assumption

lemma avoid_sound:
  closed_ty 0 ‖G‖ t →
  closed_ql true 0 ‖G‖ q0 →
  avoid t %x σ1 = .ok (t', gr) σ2 →
  stp G t q0 gr t' gs :=
by
  intro C _ H; simp only [avoid] at H; split at H
  · simp [excs] at H; obtain ⟨⟨rfl, rfl⟩, rfl⟩ := H; apply s_refl C
  have: x < ‖G‖ := by rename_i h; contrapose! h; c_free; assumption
  have: ∀G', qtp (G ++ [(.TTop, q0 ∪ {%x}, .self)] ++ G') {%x} {%‖G‖} gs := by
    intro; apply q_self' (f := ‖G‖); simp [List.getElem_append_right]
    exact ⟨rfl, rfl⟩; simp; simp; apply Finset.union_subset;
    c_extend; simp [sets]; omega; simp [sets]
  simp only [excs] at H; obtain ⟨-, _, -, H⟩ := H
  split at H; rotate_right; simp [excs] at H
  next T1 q1 T2 q2 _ => -- TFun
    simp [excs, -bind_pure_comp] at H
    obtain ⟨T1', _, HT1, T2', HT2, rfl, rfl⟩ := H; simp! at C
    have HT1' := by apply polsub_preserves_closedness C.1 at HT1; exact HT1; simp [sets]; simp
    have HT2' := by apply polsub_preserves_closedness C.2.1 at HT2; exact HT2; simp [sets]; simp
    simp [C] at HT1' HT2'; apply s_fun (gr1 := ∅) (gr2 := ∅)
    · apply polsub_subst_comm #0 %‖G‖ at HT1
      rotate_left; simp; omega; simp; generalize HG: G ++ _ = G'
      apply polsub_sound (G:=G') (q0:={✦}) (gs:=gs) at HT1; simpa using HT1
      subst G'; simp; apply subst_tighten; c_extend C.1; simp [sets]
      subst G'; rintro _ ⟨_, _, rfl⟩; tauto
    · right; apply q_sub; simp [sets, subst]; clear *-; tauto
      simp; apply subst_tighten; c_extend C.2.2.1; simp [sets]
    · apply polsub_subst_comm #1 %(‖G‖+1) at HT2
      apply polsub_subst_comm #0 %‖G‖ at HT2
      rotate_left; simp [subst]; omega; simp [instSubstId]; simp; omega; simp; simp
      generalize HG: G ++ _ = G'; apply polsub_sound (G:=G') (q0:={✦}) (gs:=gs) at HT2
      simpa using HT2; subst G'; simp; repeat apply subst_tighten
      c_extend C.2.1; simp [sets]; simp [sets]
      subst G'; rintro _ ⟨_, _, rfl⟩; simp; rw [List.append_cons]; tauto
    · simp; generalize HG: G ++ _ = G'
      rw [ql.subst_comm (x2 := %x), ql.subst_comm' (x := %x)]
      rotate_left; simp; omega; simp; simp; omega; simp; simp
      apply q_subst; subst G'; repeat apply subst_tighten
      c_extend C.2.2.2.1; simp [sets]; simp [sets]
      simp [subst]; subst G'; rw [List.append_cons]; tauto
    simp; simp; simpa [sets]; simp!; assumption; simp!; split_ands''
    · simp [closed_ql]; trans q1; simp [subst]; assumption
    · rwa [closedql_subst]; simp [sets]; simpa
    · simp [subst]; assumption
  next T1 q1 T2 q2 _ => -- TAll
    simp [excs, -bind_pure_comp] at H
    obtain ⟨T1', _, HT1, T2', HT2, rfl, rfl⟩ := H; simp! at C
    have HT1' := by apply polsub_preserves_closedness C.1 at HT1; exact HT1; simp [sets]; simp
    have HT2' := by apply polsub_preserves_closedness C.2.1 at HT2; exact HT2; simp [sets]; simp
    simp [C] at HT1' HT2'; apply s_all (gr2 := ∅)
    · apply polsub_subst_comm #0 %‖G‖ at HT1
      rotate_left; simp; omega; simp; generalize HG: G ++ _ = G'
      apply polsub_sound (G:=G') (q0:={✦}) (gs:=gs) at HT1; simpa using HT1
      subst G'; simp; apply subst_tighten; c_extend C.1; simp [sets]
      subst G'; rintro _ ⟨_, _, rfl⟩; tauto
    · right; apply q_sub; simp [sets, subst]; clear *-; tauto
      simp; apply subst_tighten; c_extend C.2.2.1; simp [sets]
    · apply polsub_subst_comm #1 %(‖G‖+1) at HT2
      apply polsub_subst_comm #0 %‖G‖ at HT2
      rotate_left; simp [subst]; omega; simp [instSubstId]; simp; omega; simp; simp
      generalize HG: G ++ _ = G'; apply polsub_sound (G:=G') (q0:={✦}) (gs:=gs) at HT2
      simpa using HT2; subst G'; simp; repeat apply subst_tighten
      c_extend C.2.1; simp [sets]; simp [sets]
      subst G'; rintro _ ⟨_, _, rfl⟩; simp; rw [List.append_cons]; tauto
    · simp; generalize HG: G ++ _ = G'
      rw [ql.subst_comm (x2 := %x), ql.subst_comm' (x := %x)]
      rotate_left; simp; omega; simp; simp; omega; simp; simp
      apply q_subst; subst G'; repeat apply subst_tighten
      c_extend C.2.2.2.1; simp [sets]; simp [sets]
      simp [subst]; subst G'; rw [List.append_cons]; tauto
    simp; simpa [sets]; simp!; assumption; simp!; split_ands''
    · simp [closed_ql]; trans q1; simp [subst]; assumption
    · rwa [closedql_subst]; simp [sets]; simpa
    · simp [subst]; assumption

def avoid_fg_example: M Unit := do
  -- [x: Ref[Bool]^✦] ⊢ f() => (g() => Ref[Bool]^x)^x
  let G: tenv := [(.TRef .TBool ∅, {✦}, .var)]
  let T := ty.TFun .TBool ∅ (.TFun .TBool ∅ (.TRef .TBool ∅) {%0}) {%0}
  -- avoid using f: f() => (g() => Ref[Bool]^f)^f
  let T1 := ty.TFun .TBool ∅ (.TFun .TBool ∅ (.TRef .TBool ∅) {#2}) {#0}
  let (T', gr) ← avoid T %0
  qassert (T' = T1 ∧ gr = {%0}) "not true"
  let (gr, _) ← check_stp G {✦} T T1 ∅
  qassert (gr = {%0}) "not true"
  -- avoid using g: f() => (g() => Ref[Bool]^g)^f
  let T2 := ty.TFun .TBool ∅ (.TFun .TBool ∅ (.TRef .TBool ∅) {#0}) {#0}
  let (gr, _) ← check_stp G {✦} T T2 ∅
  qassert (gr = {%0}) "not true"
  let (gr, _) ← check_stp G {✦} T1 T2 ∅
  qassert (gr = ∅) "not true"

#eval avoid_fg_example

lemma avoid_app_sound_gen:
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
    stp G ([#0 ↦ %n] [#1 ↦ %(n+1)] T2) {✦} gr' ([#0 ↦ %n] [#1 ↦ %(n+1)] T2') gs :=
by
  intro Ct2 Hn OC h; dsimp; simp only [avoid_app, excs] at h
  obtain ⟨⟨T2a, gr2a⟩, _, h1, ⟨T2b, gr2b⟩, _, h2, h, rfl⟩ := h
  simp at h2 h; obtain ⟨rfl, rfl⟩ := h
  have h1a: closed_ty 2 n T2a ∧ gr2a ⊆ {#1} ∧
      (✦ ∈ qx → occurs .noneq T2a #1) ∧
      occurs .no_contravariant T2a #0 := by
    split at h1; swap; apply avoid_preserves_closedness Ct2 at h1; tauto; simp
    simp [excs] at h1; obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h1; simp; tauto
  let gr2a' := [#0 ↦ %n] [#1 ↦ %(n+1)] gr2a
  have h1b: stp G
      ([#0 ↦ %n] [#1 ↦ %(n+1)] T2) {✦} gr2a'
      ([#0 ↦ %n] [#1 ↦ %(n+1)] T2a) gs := by
    simp [gr2a']; split at h1; swap
    · apply avoid_subst_comm #1 %(n+1) at h1; rotate_left; simp; simp; c_free;
      apply avoid_subst_comm #0 %n at h1; conv at h1 => left; arg 2; simp [subst]
      rotate_left; simp [subst]; simp; simp [subst]
      apply avoid_sound (G := G) at h1; assumption; simp [Hn]; repeat apply subst_tighten
      c_extend; simp [sets]; simp [sets]; simp [sets]
    · simp [excs] at h1; obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h1
      conv => arg 4; simp [subst]
      apply s_refl; simp [Hn]; repeat apply subst_tighten
      c_extend; simp [sets]; simp [sets]
  clear h1; obtain ⟨Ct2a, h1a⟩ := h1a
  have h2a: closed_ty 2 n T2b ∧ gr2b ⊆ {#0} ∧
      (✦ ∈ qx → occurs .noneq T2b #1) ∧
      (✦ ∈ qf → occurs .noneq T2b #0) ∧
      occurs .no_contravariant T2b #0 := by
    split at h2; apply avoid_preserves_closedness Ct2a at h2;
    obtain ⟨h2a, h2b, h2c, h2d⟩ := h2; split_ands'
    specialize h2c #1; tauto; tauto; tauto; simp
    simp [excs] at h2; obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h2; simp; tauto
  let gr2b' := [#0 ↦ %n] [#1 ↦ %(n+1)] gr2b
  have h2b: stp G
      ([#0 ↦ %n] [#1 ↦ %(n+1)] T2a) ({✦} ∪ gr2a') gr2b'
      ([#0 ↦ %n] [#1 ↦ %(n+1)] T2b) gs := by
    simp [gr2b']; split at h2
    · apply avoid_subst_comm #1 %(n+1) at h2; conv at h2 => left; arg 2; simp [subst]
      rotate_left; simp; simp
      apply avoid_subst_comm #0 %n at h2; conv at h2 => left; arg 2; simp [subst]
      rotate_left; simp; simp; c_free; apply avoid_sound (G := G) at h2; assumption
      simp [Hn]; repeat apply subst_tighten
      c_extend; simp [sets]; simp [sets]
      simp [sets]; apply closedql_extend (stp_closed h1b).2.2 <;> simp
    · simp [excs] at h2; obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h2
      conv => arg 4; simp [subst]
      apply s_refl; simp [Hn]; repeat apply subst_tighten
      c_extend; simp [sets]; simp [sets]
  clear h2; split_ands''
  all_goals rename gr2a ⊆ _ => h1; rename gr2b ⊆ _ => h2
  all_goals simp only [sets] at h1 h2; simp at h1 h2
  · clear *- h1 h2; simp [sets]; tauto
  · clear *- h1 h2; simp [subst, cnf, sets]; tauto
  · have := s_trans h1b h2b; convert this using 1
    ext; simp [gr2a', gr2b', subst, cnf]; clear *-; constructor
    rintro (h | h | h | h | h | h) <;> simp [h]
    rintro (h | h | h | h | h | h) <;> simp [h]

lemma avoid_app_sound_fun:
  closed_ty 0 ‖G‖ (.TFun T1 q1 T2 q2) →
  avoid_app T2 qf qx σ1 = .ok (T2', gr) σ2 →
  stp G (.TFun T1 q1 T2 q2) qf ∅ (.TFun T1 q1 T2' (q2 ∪ gr)) gs ∧
    (✦ ∈ qf → occurs .noneq T2' #0) ∧
    (✦ ∈ qx → occurs .noneq T2' #1) :=
by
  intro Ct h; simp! at Ct
  let G2 := (G ++ [(.TTop, qf, .self), ([#0 ↦ %‖G‖] T1, [#0 ↦ %‖G‖] q1, .var)])
  casesm* _ ∧ _; apply avoid_app_sound_gen (n := ‖G‖) (G := G2) (gs := gs) at h
  assumption'; swap; simp [G2]; extract_lets at h; rename_i gr'; split_ands''
  have: closed_ql true 2 ‖G‖ (q2 ∪ gr) := by
    apply Finset.union_subset; assumption; trans; assumption; simp [sets]
  eapply s_fun (gr1 := ∅) (gr2 := gr')
  apply s_refl; simp; apply subst_tighten; c_extend; simp
  right; simp; apply q_sub; simp; simp; apply subst_tighten; c_extend; simp [sets]
  simp; assumption; apply q_sub; simp [gr', sets, subst, cnf]
  clear *-; rintro _ (h | h | h | h | h | h) <;> simp [h]
  simp; repeat apply subst_tighten
  c_extend; simp [sets]; simp [sets]; simp; simpa; simp [sets]
  simp!; split_ands'; simp!; split_ands'

lemma avoid_app_sound_all:
  closed_ty 0 ‖G‖ (.TAll T1 q1 T2 q2) →
  avoid_app T2 qf qx σ1 = .ok (T2', gr) σ2 →
  stp G (.TAll T1 q1 T2 q2) qf ∅ (.TAll T1 q1 T2' (q2 ∪ gr)) gs ∧
    (✦ ∈ qf → occurs .noneq T2' #0) ∧
    (✦ ∈ qx → occurs .noneq T2' #1) :=
by
  intro Ct h; simp! at Ct
  let G2 := (G ++ [(.TTop, qf, .self), ([#0 ↦ %‖G‖] T1, [#0 ↦ %‖G‖] q1, .tvar)])
  casesm* _ ∧ _; apply avoid_app_sound_gen (n := ‖G‖) (G := G2) (gs := gs) at h
  assumption'; swap; simp [G2]; extract_lets at h; rename_i gr'; split_ands''
  have: closed_ql true 2 ‖G‖ (q2 ∪ gr) := by
    apply Finset.union_subset; assumption; trans; assumption; simp [sets]
  eapply s_all (gr2 := gr')
  apply s_refl; simp; apply subst_tighten; c_extend; simp
  right; simp; apply q_sub; simp; simp; apply subst_tighten; c_extend; simp [sets]
  simp; assumption; apply q_sub; simp [gr', sets, subst, cnf]
  clear *-; rintro _ (h | h | h | h | h | h) <;> simp [h]
  simp; repeat apply subst_tighten
  c_extend; simp [sets]; simp [sets]; simp; simpa; simp [sets]
  simp!; split_ands'; simp!; split_ands'

-- type variable exposure

lemma texposure_sound (tl: telescope G) (C: closed_ty 0 ‖G‖ t):
  texposure G t = t' →
  stp G t q0 ∅ t' gs :=
by
  intro h; generalize hG: G = G0 at h C; rw [←hG]
  replace hG: G0 <+: G := by simp [hG]
  induction G0, t using texposure.induct generalizing t'
  next G1 x _ _ h1 h2 ih1 =>
    conv at h => simp [texposure]; rw [h1]; simp
    obtain ⟨G1', rfl⟩ := hG; apply telescope_shrink at tl; specialize tl h1
    specialize ih1 h _ _; c_extend tl.1; omega
    exists (G1.drop x) ++ G1'; simp [←List.append_assoc]
    change stp _ _ _ (∅ ∪ ∅) _ _; apply s_trans; swap; simpa
    apply s_tvar; simpa [List.getElem?_append_left, h2] using h1
    c_extend tl.1; omega
  next =>
    simp [texposure] at h; subst t'; apply s_refl; obtain ⟨G', rfl⟩ := hG; c_extend;
  next =>
    simp [texposure] at h; subst t'; apply s_refl; obtain ⟨G', rfl⟩ := hG; c_extend;

lemma texposure_sound' (tl: telescope G):
  texposure G T = T' →
  has_type G p t T  q gs →
  has_type G p t T' q gs :=
by
  intro h1 h2; have := hast_closed h2; apply t_sub (gr := ∅); assumption
  apply texposure_sound; assumption'; simp [this]
  apply q_sub; simp; simp [this]; simp [this]

-- bidirectional typing

@[simp]
def tinfer_sound G gs t := ∀ G' p T q σ1 σ2,
  telescope G → gs ⊆ Finset.range ‖G‖ →
  tinfer G gs t σ1 = .ok (G', p, T, q) σ2 →
  ctx_grow G G' gs ∧ closed_ql false 0 ‖G‖ p ∧ has_type G' p t T q gs

@[simp]
def tinfer'_sound G gs t := ∀ G' p T q σ1 σ2,
  telescope G → gs ⊆ Finset.range ‖G‖ →
  tinfer' G gs t σ1 = .ok (G', p, T, q) σ2 →
  ctx_grow G G' gs ∧ closed_ql false 0 ‖G‖ p ∧ has_type G' p t T q gs

@[simp]
def tcheck_sound G gs t T := ∀ G' p q σ1 σ2,
  telescope G → gs ⊆ Finset.range ‖G‖ →
  closed_ty 0 ‖G‖ T →
  tcheck G gs t T σ1 = .ok (G', p, q) σ2 →
  ctx_grow G G' gs ∧ closed_ql false 0 ‖G‖ p ∧ has_type G' p t T q gs

@[simp]
def tcheck'_sound G gs t T := ∀ G' p q σ1 σ2,
  telescope G → gs ⊆ Finset.range ‖G‖ →
  closed_ty 0 ‖G‖ T →
  tcheck' G gs t T σ1 = .ok (G', p, q) σ2 →
  ctx_grow G G' gs ∧ closed_ql false 0 ‖G‖ p ∧ has_type G' p t T q gs

@[simp]
def tcheckq_sound G gs t T q := ∀ G' p σ1 σ2,
  telescope G → gs ⊆ Finset.range ‖G‖ →
  closed_ty 0 ‖G‖ T →
  closed_ql true 0 ‖G‖ q →
  tcheckq G gs t T q σ1 = .ok (G', p) σ2 →
  ctx_grow G G' gs ∧ closed_ql false 0 ‖G‖ p ∧ has_type G' p t T q gs

@[simp]
def tinferabs_sound G gs T1 q1 bn t := ∀ G' T2 q2 qf σ1 σ2,
  telescope G → gs ⊆ Finset.range ‖G‖ → bn ≠ .self →
  closed_ty 1 ‖G‖ T1 → closed_ql true 1 ‖G‖ q1 →
  occurs .no_covariant T1 #0 → (#0 ∈ q1 → ✦ ∈ q1) →
  tinferabs G gs T1 q1 bn t σ1 = .ok (G', qf, T2, q2) σ2 →
    ctx_grow G G' gs ∧ ✦ ∉ qf ∧
    match bn with
    | .var => has_type G' qf (.tabs t) (.TFun T1 q1 T2 q2) qf gs
    | .tvar => has_type G' qf (.ttabs T1 q1 t) (.TAll T1 q1 T2 q2) qf gs
    | _ => True

lemma tinferabs_proof {G gs T1 q1 bn t2}:
  let G1 := G ++ [(.TTop, ∅, .self), ([#0↦%‖G‖]T1, [#0↦%‖G‖]q1, bn)];
  tinfer'_sound G1 (gs ∪ {‖G‖}) t2 → tinferabs_sound G gs T1 q1 bn t2 :=
by
  unfold tinfer'_sound tinferabs_sound
  introv G1 ih tl hgs _ Ct1 Cq1 _ _ h; simp only [tinferabs, excs] at h
  obtain ⟨-, _, -, ⟨G2, p2, T2a, q2b⟩, _, h1, T2b, _, h2, h⟩ := h; simp at h2 h
  obtain ⟨_, q, ⟨⟨_, h3⟩, rfl⟩, hG', hqf, rfl, rfl⟩ := h
  have tl1: telescope G1 := by
    simp [G1]; rw [List.append_cons]; apply telescope_extend
    simp; apply subst_tighten; c_extend; simp
    simp; apply subst_tighten; c_extend; simp [sets]; apply telescope_extend
    simp!; simp [sets]; assumption
  apply ih at h1; assumption'; swap; simp [G1]; apply Finset.union_subset
  trans; assumption; simp; simp; clear ih; obtain ⟨h1a, h1b, h1c⟩ := h1
  simp [G1] at h1a; have := h1a.inversion2 (by assumption)
  simp at this; obtain ⟨G', q', rfl, _⟩ := this; have L := h1a.1
  simp [G1] at L; simp [L, List.getElem_append_right] at h3 hG'; subst G'
  obtain ⟨rfl, rfl, rfl⟩ := h3; replace h1a := (h1a.shrink rfl).gs_shrink
  have Cqf: closed_ql false 0 ‖G‖ qf := by
    subst qf; repeat' apply Finset.union_subset
    assumption; trans (p2 \ {%(‖G‖+1)}) \ {%‖G‖}; clear *-; simp [sets]; tauto
    (repeat apply closedql_tighten); simpa [G1] using h1b
    trans (q1 \ {✦}) \ {#0}; clear *-; simp [sets]; tauto
    (repeat apply closedql_tighten); assumption
  rw [L] at Ct1 Cq1 Cqf h2; have: q1 \ {✦, #0} ⊆ qf := by
    subst qf; simp [sets]; clear *-; tauto
  let G1 := G' ++ [(.TTop, qf, .self), ([#0↦%‖G‖]T1, [#0↦%‖G‖]q1, bn)]
  replace h1c: has_type G1 p2 t2 T2a q2b gs := by
    apply has_type.gs_tighten; apply ctx_grow.on_hastype h1c; swap; simp
    simp [G1]; apply ctx_grow.set ‖G'‖; simp [List.getElem_append_right]
    exact ⟨rfl, rfl⟩; simp; rfl; c_extend; simp; intro h; absurd h; c_free;
    subst qf; simp; simp [L]
  have C2 := hast_closed h1c; apply @rm_contravariant_sound G1 _ _ _ _ _ q2b gs at h2
  obtain ⟨h2a, h2b⟩ := h2; rotate_left; apply C2.2.1; simp [G1, L]
  replace h1c: has_type G1 (qf ∪ {%‖G‖, %(‖G‖+1)}) t2 T2b q2b gs := by
    apply has_type.filter_widen; apply t_sub; apply h1c; apply h2a
    apply q_sub; simp; simp [C2]; simp [C2]; subst qf
    simp [sets]; clear *-; tauto
  simp [G1, L] at h1c ⊢; clear h2a C2 G1; split_ands'; c_free; split
  · change has_type _ _ _ (.TFun' ‖G'‖ T1 q1 T2b q2b) _ _
    apply t_abs'; assumption'; simp
  · change has_type _ _ _ (.TAll' ‖G'‖ T1 q1 T2b q2b) _ _
    apply t_tabs'; assumption'; simp
  simp

lemma tcheck_tabs_proof {G gs t T1 q1 T2 q2}:
  let G' := G ++ [(.TTop, ∅, .self), ([#0↦%‖G‖]T1, [#0↦%‖G‖]q1, .var)];
  tcheckq_sound G' (gs ∪ {‖G‖}) t ([#0↦%‖G‖][#1↦%(‖G‖ + 1)]T2) [#0↦%‖G‖][#1↦%(‖G‖ + 1)]q2 →
  tcheck_sound G gs (.tabs t) (.TFun T1 q1 T2 q2) :=
by
  unfold tcheckq_sound tcheck_sound
  introv G1 ih tl hgs C h; simp only [tcheck, excs] at h
  have tl1: telescope G1 := by
    simp [G1]; rw [List.append_cons]; simp! at C; obtain ⟨_, -, _, -⟩ := C
    apply telescope_extend; apply subst_tighten; c_extend; simp
    apply subst_tighten; c_extend; simp [sets]
    apply telescope_extend; simp!; simp [sets]; assumption
  obtain ⟨-, _, -, ⟨G'', p0⟩, _, h1, h⟩ := h; simp at h
  apply ih at h1; assumption'; rotate_left
  · simp [G1]; apply Finset.union_subset; trans; assumption; simp; simp
  · simp [G1]; (repeat apply subst_tighten); c_extend C.2.1; simp; simp
  · simp [G1]; (repeat apply subst_tighten); c_extend C.2.2.2.1; simp [sets]; simp [sets]
  obtain ⟨T, qf, ⟨⟨bn, hg⟩, rfl⟩, h⟩ := h; simp [G1] at h1
  have := h1.1.inversion2; simp at this; obtain ⟨G', qf, rfl, cq1'⟩ := this
  have L := h1.1.1; simp at L; simp [L, List.getElem_append_right] at h hg
  obtain ⟨rfl, rfl, rfl⟩ := hg; obtain ⟨rfl, rfl, rfl⟩ := h
  let qf' := qf ∪ p0 \ {%‖G'‖, %(‖G'‖ + 1)} ∪ q1 \ {✦, #0}
  have cqf: closed_ql false 0 ‖G‖ qf' := by
    repeat' apply Finset.union_subset
    assumption; simp [←L]; replace h1 := h1.2.1; clear *- h1
    trans (p0 \ {%(‖G‖+1)}) \ {%‖G‖}; simp [sets]; tauto
    (repeat apply closedql_tighten); assumption; clear *- C
    simp! at C; obtain ⟨-, -, C, -⟩ := C
    trans (q1 \ {✦}) \ {#0}; simp [sets]; tauto
    (repeat apply closedql_tighten); assumption
  clear ih; split_ands'
  · apply (h1.1.shrink rfl).gs_shrink
  · simpa [qf'] using cqf
  · simp [L] at h1 C; simp! at C; casesm* _ ∧ _
    apply has_type.gs_tighten (gs' := gs ∪ {‖G'‖})
    apply t_abs; simp [L]; assumption'
    apply has_type.filter_widen; apply ctx_grow.on_hastype; assumption
    apply ctx_grow.set (q' := qf') ‖G'‖
    simp [List.getElem_append_right]; exact ⟨rfl, rfl⟩; simp [qf']
    c_extend; simp [L]; simp; intro h; absurd h; c_free; simp [qf']; simp
    simp [sets]; clear *-; tauto; simp [sets]; clear *-; tauto
    simpa [qf', L] using cqf; simp; simp

lemma tinfer_tlet_proof {G gs t2 t1}:
  tinfer'_sound G gs t1 → (∀ G1 Tx qx, tinferabs_sound G1 gs Tx qx .var t2) →
  tinfer_sound G gs (.tapp (.tabs t2) t1) :=
by
  dsimp; introv ih1 ih2 tl hgs h; simp only [tinfer, excs] at h
  obtain ⟨⟨G1, p1, Tx, qx⟩, _, h1, h⟩ := h; simp at h
  obtain ⟨G2, qf, T2, q2, _, h2, T2', gr, h3, rfl, rfl, rfl, rfl⟩ := h
  apply ih1 at h1; assumption'; clear ih1
  have tl1 := h1.1.on_telescope tl; have Cx := hast_closed h1.2.2
  apply ih2 at h2; rotate_left; assumption; simpa [←h1.1.1]; simp
  c_extend Cx.2.1; c_extend Cx.2.2; c_free Cx.2.1; intro h; absurd h; c_free Cx.2.2;
  clear ih2; have Cf := hast_closed h2.2.2
  apply @avoid_app_sound_fun G2 Tx qx T2 q2 qf _ _ _ _ _ gs at h3
  swap; apply Cf.2.1
  simp [h1.1.1, h2.1.1] at h1 Cx ⊢; split_ands
  · apply h1.1.trans h2.1
  · repeat' apply Finset.union_subset
    apply closedql_fr_tighten h2.2.1; exact Cf.2.2; exact h1.2.1
    have := (stp_closed h3.1).2.1; simp! at this; replace this := this.2.2.2.1
    trans (((q2 ∪ gr) \ {✦}) \ {#1}) \ {#0}; clear *-; simp [sets]; tauto
    (repeat apply closedql_tighten); exact this
  · eapply t_app; apply t_sub; apply h2.2.2.filter_widen; simp
    apply h3.1; apply q_sub; simp; apply Cf.2.2; trans qf; simp; simp
    apply has_type.filter_widen; apply h2.1.on_hastype h1.2.2; clear *-; simp [sets]; tauto
    right; left; apply q_sub; simp; apply Cx.2.2
    clear *-; simp [sets]; tauto; apply h3.2.1; apply h3.2.2

lemma tinfer_tapp_proof {G gs t1 t2}:
  (∀ t, t1 = .tabs t → False) →
  tinfer'_sound G gs t1 → (∀ G1 T1', tcheck'_sound G1 gs t2 T1') →
  tinfer_sound G gs (.tapp t1 t2) :=
by
  dsimp; introv _ ih1 ih2 tl hgs h; simp only [tinfer, excs] at h
  obtain ⟨⟨G1, p, Tf, qf⟩, _, h0, h⟩ := h; simp only at h
  generalize h1: texposure _ _ = Tf' at h
  split at h; swap; simp only [excs] at h; rename_i T1 q1 T2 q2
  simp only [excs] at h; obtain ⟨T1', _, h2, ⟨G', p1, qx⟩, _, h3, h⟩ := h
  simp at h; obtain ⟨G'', p2, _, h4, T2', gr, h5, h⟩ := h
  obtain ⟨rfl, h, rfl, rfl⟩ := h; rename_i p2' _ _ _ _ _
  apply ih1 at h0; assumption'; replace tl := h0.1.on_telescope tl
  apply texposure_sound' at h1; specialize h1 h0.2.2; assumption'
  have Cf := hast_closed h1; rw [h0.1.1] at hgs
  replace h2 := unpack_argself_sound_fun Cf.2.1 Cf.2.2 h2 hgs
  apply ih2 at h3; assumption'; swap; simp [h2]; clear ih1 ih2
  obtain ⟨_, h2⟩ := h2; replace tl := h3.1.on_telescope tl
  apply check_app_sound at h4; assumption'; swap
  apply h3.1.1 ▸ Cf.2.1.2.2.1; have cg := h3.1.trans h4.1
  apply @avoid_app_sound_fun G'' T1' q1 T2 q2 qf _ _ _ _ _ gs at h5
  swap; rw [←cg.1]; replace h2 := stp_closed h2; simp [h2]
  replace h2 := cg.on_stp h2; obtain ⟨h5, _, _⟩ := h5
  replace h2 := s_trans h2 (by simpa); simp at h2
  have h1 := cg.on_hastype h1
  apply t_sub (gr := ∅) (q2 := qf) at h1; specialize h1 h2 _ _
  apply q_sub; simp; simp [←cg.1, Cf]; simp [Cf]; clear h2 h5
  simp [h0.1.1, h3.1.1] at h0 h3 ⊢; split_ands
  · apply h0.1.trans cg
  · subst p2'; repeat' apply Finset.union_subset
    exact h0.2.1; exact h3.2.1; exact h4.2.1
    have := (hast_closed h1).2.1; simp! at this
    replace this := this.2.2.2.1; simp [h4.1.1]
    trans (((q2 ∪ gr) \ {✦}) \ {#1}) \ {#0}; clear *-; simp [sets]; tauto
    (repeat apply closedql_tighten); exact this
  · subst p2'; eapply t_app; apply h1.filter_widen; simp
    apply h4.1.on_hastype; apply h3.2.2.filter_widen; simp [sets]; clear *-; tauto
    apply h4.2.2; simp [sets]; clear *-; tauto
    simp [sets]; clear *-; tauto; assumption'

lemma tinfer_ttapp_proof {G gs t Tx qx}:
  tinfer'_sound G gs t → tinfer_sound G gs (.ttapp t Tx qx) :=
by
  dsimp; introv ih tl hgs h; simp only [tinfer, excs] at h
  obtain ⟨-, _, ⟨⟨Ctx, Cqx⟩, rfl⟩, ⟨G1, p, Tf, qf⟩, _, h0, h⟩ := h; simp only at h
  generalize h1: texposure _ _ = Tf' at h
  split at h; swap; simp only [excs] at h; rename_i T1 q1 T2 q2
  simp only [excs] at h; obtain ⟨T1', _, h2, ⟨gr, G'⟩, _, h3, h⟩ := h
  simp at h; obtain ⟨_, ⟨rfl, rfl⟩, G'', p2, _, h4, T2', gr, h5, h⟩ := h
  obtain ⟨rfl, h, rfl, rfl⟩ := h; rename_i p2' _ _ _ _ _
  apply ih at h0; assumption'
  replace tl := h0.1.on_telescope tl
  apply texposure_sound' at h1; specialize h1 h0.2.2; assumption'
  have Cf := hast_closed h1; rw [h0.1.1] at hgs
  replace h2 := unpack_argself_sound_all Cf.2.1 Cf.2.2 h2 hgs
  apply check_stp_sound at h3; assumption'
  specialize h3 (by simp [sets]) (h0.1.1 ▸ Ctx) h2.1
  obtain ⟨_, h2⟩ := h2; obtain ⟨-, h3⟩ := h3; replace tl := h3.1.on_telescope tl
  apply check_app_sound at h4; assumption'; swap
  apply h3.1.1 ▸ Cf.2.1.2.2.1; have cg := h3.1.trans h4.1
  apply @avoid_app_sound_all G'' T1' q1 T2 q2 qf _ _ _ _ _ gs at h5
  swap; rw [←cg.1]; replace h2 := stp_closed h2; simp [h2]
  replace h2 := cg.on_stp h2; obtain ⟨h5, _, _⟩ := h5
  replace h2 := s_trans h2 (by simpa); simp at h2
  have h1 := cg.on_hastype h1
  apply t_sub (gr := ∅) (q2 := qf) at h1; specialize h1 h2 _ _
  apply q_sub; simp; simp [←cg.1, Cf]; simp [Cf]; clear h2 h5
  rw [h0.1.1, h3.1.1] at h0 Cqx ⊢; split_ands
  · apply h0.1.trans cg
  · subst p2'; repeat' apply Finset.union_subset
    exact h0.2.1; apply closedql_tighten; assumption; exact h4.2.1
    have := (hast_closed h1).2.1; simp! at this
    replace this := this.2.2.2.1; simp [h4.1.1]
    trans (((q2 ∪ gr) \ {✦}) \ {#1}) \ {#0}; clear *-; simp [sets]; tauto
    (repeat apply closedql_tighten); exact this
  · subst p2'; eapply t_tapp; apply h1.filter_widen; simp
    exact h4.1.on_stp h3.2; rwa [←h4.1.1]
    apply h4.2.2; simp [sets]; clear *-; tauto
    simp [sets]; clear *-; tauto
    simp [sets]; clear *-; tauto; assumption'

theorem bidirectional_sound:
  (∀ G gs t, tinfer_sound G gs t) ∧
  (∀ G gs t T, tcheck'_sound G gs t T) ∧
  (∀ G gs t T, tcheck_sound G gs t T) ∧
  (∀ G gs t, tinfer'_sound G gs t) ∧
  (∀ G gs t T q, tcheckq_sound G gs t T q) ∧
  (∀ G gs T1 q1 bn t, tinferabs_sound G gs T1 q1 bn t) :=
by
  apply tinfer.mutual_induct
  -- tinfer: true, false
  · dsimp; introv tl hgs h; simp only [tinfer, excs] at h; simp at h
    obtain ⟨⟨rfl, rfl, rfl, rfl⟩, rfl⟩ := h; simp [ctx_grow]; simp [sets]; apply t_true
  · dsimp; introv tl hgs h; simp only [tinfer, excs] at h; simp at h
    obtain ⟨⟨rfl, rfl, rfl, rfl⟩, rfl⟩ := h; simp [ctx_grow]; simp [sets]; apply t_false
  -- tinfer: var
  · dsimp only [tinfer_sound]; introv tl hgs h; simp only [tinfer, excs] at h
    obtain ⟨⟨_, _, _⟩, _, ⟨Gx, rfl⟩, h⟩ := h; simp at h
    obtain ⟨⟨rfl, rfl⟩, rfl, rfl, rfl, rfl⟩ := h; simp [ctx_grow]
    have := (List.getElem?_eq_some.1 Gx).1; simp [sets, this]
    apply t_var; assumption'; simp; simp; specialize tl Gx; c_extend tl.1; omega
  -- tinfer: ref
  · dsimp; introv IH1 tl hgs h; simp only [tinfer, excs] at h
    obtain ⟨⟨G', p, T, q⟩, _, h1, h⟩ := h; simp at h
    obtain ⟨⟨_, rfl⟩, rfl, rfl, rfl, rfl⟩ := h
    apply IH1 at h1; split_ands''; apply t_ref; assumption'
  -- tinfer: get
  · dsimp; introv ih1 tl hgs h; simp only [tinfer, excs] at h
    obtain ⟨⟨G', p, T, q⟩, _, h1, h⟩ := h; simp only [excs] at h
    generalize h2: texposure _ _ = T' at h
    split at h <;> simp only [excs] at h; rename_i T1 q1; simp at h
    obtain ⟨⟨_, rfl⟩, rfl, rfl, rfl, rfl⟩ := h
    apply ih1 at h1; assumption'; simp [h1]
    apply texposure_sound' at h2; specialize h2 h1.2.2; swap
    apply h1.1.on_telescope tl
    split_ands; apply Finset.union_subset; exact h1.2.1
    rw [h1.1.1]; apply closedql_bv_tighten; assumption
    have := (hast_closed h2).2.1; simp! at this; c_extend this.2
    eapply t_get; assumption'; apply has_type.filter_widen; assumption; simp; simp
  -- tinfer: put
  · dsimp; introv IH1 IH2 tl hgs h; simp only [tinfer, excs] at h
    obtain ⟨⟨G', p1, T, q⟩, _, h1, h⟩ := h; simp only at h
    generalize h2: texposure _ _ = T' at h
    split at h <;> simp only [excs] at h; rename_i T1 q1
    obtain ⟨-, _, ⟨_, rfl⟩, ⟨G'', p2⟩, _, h3, h⟩ := h
    simp at h; obtain ⟨⟨rfl, rfl, rfl, rfl⟩, rfl⟩ := h
    apply IH1 at h1; assumption'; have tl' := h1.1.on_telescope tl
    apply texposure_sound' at h2; specialize h2 h1.2.2; assumption'
    have C := (hast_closed h2).2.1; apply IH2 at h3; assumption'
    split_ands
    apply h1.1.trans h3.1; apply Finset.union_subset; exact h1.2.1
    simp [h1.1.1]; exact h3.2.1; apply t_put
    apply h3.1.on_hastype; apply h2.filter_widen; simp
    apply h3.2.2.filter_widen; simp; simpa [h1.1.1] using hgs
    simp [C.1]; apply closedql_bv_tighten; assumption; c_extend C.2
  -- tinfer: abs with annotation
  · dsimp; introv ih tl hgs h; simp only [tinfer, excs] at h
    obtain ⟨-, _, ⟨⟨h1, h2, h3a, h3b⟩, rfl⟩, ⟨G', qf, T2, q2⟩, _, h4, h⟩ := h
    simp at h; obtain ⟨⟨rfl, rfl, rfl, rfl⟩, rfl⟩ := h
    apply ih at h4; assumption'; swap; simp; have := (hast_closed h4.2.2).2.2
    split_ands; simp [h4]; apply closedql_fr_tighten h4.2.1
    rwa [h4.1.1]; apply t_absa; apply h4.2.2
  -- tinfer: ttabs
  · dsimp; introv ih tl hgs h; simp only [tinfer, excs] at h
    obtain ⟨-, _, ⟨⟨h1, h2, h3a, h3b⟩, rfl⟩, ⟨G', qf, T2, q2⟩, _, h4, h⟩ := h
    simp at h; obtain ⟨⟨rfl, rfl, rfl, rfl⟩, rfl⟩ := h
    apply ih at h4; assumption'; swap; simp; have := (hast_closed h4.2.2).2.2
    split_ands; simp [h4]; apply closedql_fr_tighten h4.2.1
    rwa [h4.1.1]; apply h4.2.2
  -- tinfer: let
  · apply tinfer_tlet_proof
  -- tinfer: app
  · apply tinfer_tapp_proof
  -- tinfer: ttapp
  · apply tinfer_ttapp_proof
  -- tinfer: annotation/ascription
  · dsimp; introv IH tl hgs h; simp only [tinfer, excs] at h
    obtain ⟨-, _, ⟨⟨_, _⟩, rfl⟩, ⟨G', p⟩, _, h1, h⟩ := h
    simp at h; obtain ⟨⟨rfl, rfl, rfl, rfl⟩, rfl⟩ := h
    apply IH at h1; assumption'; split_ands''; apply t_asc; assumption
  -- tinfer: dead case
  · dsimp; introv tl hgs h; simp only [tinfer, excs] at h
  -- tcheck'
  · simp; introv ih tl hgs C h; simp [tcheck', excs] at h; apply ih; assumption'
  -- tcheck: fun
  · apply tcheck_tabs_proof
  -- tcheck: ref
  · dsimp; introv ih tl hgs C h; simp! at C; simp only [tcheck, excs] at h
    obtain ⟨-, _, ⟨_, rfl⟩, ⟨G', p, q'⟩, _, h1, h⟩ := h; simp at h; rename_i q1 _ _ _ _
    apply ih at h1; rotate_left; assumption'; exact C.1
    · obtain ⟨G'', h2, h⟩ := h; apply check_qtp_sound at h2; rotate_left
      apply h1.1.on_telescope tl; apply closedql_bv_tighten; assumption
      rw [←h1.1.1]; c_extend C.2; obtain ⟨rfl, rfl, rfl⟩ := h; split_ands
      apply h1.1.trans h2.1; apply Finset.union_subset; exact h1.2.1
      have: #0 ∉ q1 := by c_free (qtp_closed h2.2).2
      apply closedql_bv_tighten; assumption; exact C.2
      apply t_ref; apply t_sub (gr := ∅)
      apply h2.1.on_hastype; apply h1.2.2.filter_widen; simp
      apply s_refl; simp [←h2.1.1, ←h1.1.1]; exact C.1; simp [h2.2]
      trans q1; simp; simp; c_free C.2
  -- tcheck: subsumption
  · dsimp; introv _ _ ih tl hgs _ h; simp only [tcheck, excs] at h
    obtain ⟨⟨G', p, T', q'⟩, _, h1, h⟩ := h
    apply ih at h1; assumption'; simp at h; obtain ⟨gr, G'', h2, h⟩ := h
    have C := (hast_closed h1.2.2).2
    apply check_stp_sound at h2; specialize h2 C.2 C.1 _; rwa [← h1.1.1]
    rotate_left; apply h1.1.on_telescope tl; rwa [←h1.1.1]
    obtain ⟨rfl, rfl, rfl⟩ := h; split_ands
    apply h1.1.trans h2.2.1; repeat' apply Finset.union_subset
    exact h1.2.1; apply closedql_tighten; have := hast_closed h1.2.2
    simp [h1.1.1, this]; simp [h1.1.1]; exact h2.1; apply t_sub
    apply h2.2.1.on_hastype; apply h1.2.2.filter_widen; simp
    exact h2.2.2; apply q_sub; simp; simp [←h2.2.1.1]; apply Finset.union_subset
    exact (hast_closed h1.2.2).2.2; c_extend h2.1
    simp [sets]; clear *-; tauto
  -- tinfer'
  · simp; introv ih tl hgs h; simp [tinfer', excs] at h; apply ih; assumption'
  -- tcheckq: subsumption
  · dsimp; introv ih tl hgs h1 h2 h; simp only [tcheckq, excs] at h
    obtain ⟨⟨G', p, q'⟩, _, h3, h⟩ := h; simp at h
    apply ih at h3; assumption'; obtain ⟨G'', h4, h⟩ := h
    apply check_qtp_sound at h4; rotate_left; apply h3.1.on_telescope tl; rwa [←h3.1.1]
    obtain ⟨rfl, rfl⟩ := h; split_ands; apply h3.1.trans h4.1; apply Finset.union_subset
    exact h3.2.1; apply closedql_tighten; assumption
    apply t_sub (gr := ∅)
    apply h4.1.on_hastype; apply h3.2.2.filter_widen; simp
    apply s_refl; simpa [h3.1.1, h4.1.1] using h1
    simp [h4.2]; simp
  -- tinferabs
  · apply tinferabs_proof

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
