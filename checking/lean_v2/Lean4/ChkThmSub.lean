import Lean4.Checking
import Aesop

attribute [-simp] getElem?_pos Finset.singleton_union Finset.union_singleton

@[simp]
lemma Finset.sdiff_eq_self_of_notMem [DecidableEq α] {s: Finset α} {a: α}
  (h: a ∉ s): s \ ({a}) = s := by simp [Finset.sdiff_singleton_eq_erase, h]


lemma List.getElem?_eq_getElem' {L: List α} {i: ℕ} (h: i < ‖L‖):
  ∃a, L[i]? = some a :=
by
  have := List.getElem?_eq_getElem h; exists L[i]

namespace Reachability

-- [-simp] is local; redefine them
attribute [-simp] Set.setOf_subset_setOf Set.subset_inter_iff Set.union_subset_iff
attribute [-simp] Finset.union_insert

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
  intro h; split at h; right; rename_i e s h1; exists e; simp [h1]
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
  congrm _ ∨ ∃f, ?_; by_cases h: f < ‖G‖ <;> simp [h]
  rintro -; congrm ∃ Tf qf, ?_; simp; intro h1; specialize tl h1
  rw [go_lift]; omega; simp [closed_ql]; trans qf; simp; apply tl.2

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
  by_cases h1: x < ‖G‖ <;> simp [h1, -exists_and_right]
  rintro rfl; congrm ∃ Tx qx bn, ?_; simp; rintro h - -
  apply go_lift; omega; specialize tl h; apply tl.2

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
  simp at h1; simp [h1] at h2; assumption

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
  let G := [(.TRef1 .TUnit ∅, {✦}, .var), (.TRef1 .TUnit ∅, {✦}, .var), ((.TRef1 .TUnit ∅, {%0, %1}, .var))]
  qtp G {%2} ({%0} ∪ {%2}) ∅ ∧ qtp G {%2} ({%0} ∪ {%1}) ∅ ∧
    ¬ qtp G {%2} {%1} ∅ ∧ ¬ qtp G {%1} {%2} ∅ :=
by
  have := fun {α: Type} {x l} (h: ‖l‖ > 0) => Eq.symm (@List.singleton_append α x l)
  intro G; replace this: telescope G := by
    rw [←List.nil_append G]; simp +arith only [G, this,
      List.length_cons, List.length_nil, List.length_append, ←List.append_assoc]
    apply telescope_extend; simp! [sets]; simp [sets]
    apply telescope_extend; simp! [sets]; simp [sets]
    apply telescope_extend; simp! [sets]; simp [sets]; simp [telescope]
  simp [G]; split_ands
  apply check_qtp0_sound; assumption; decide
  apply check_qtp0_sound; assumption; decide
  intro h; apply check_qtp0_complete at h; revert h; decide; assumption
  intro h; apply check_qtp0_complete at h; revert h; decide; assumption

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
      obtain ⟨rfl, rfl, rfl⟩ := h; apply ih at h2; apply h2.trans
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
      obtain ⟨rfl, rfl, rfl⟩ := H; apply ih at H2; specialize H2 hi
      generalize hG: G'.set f _ = G''; symm at hG
      replace TL: closed_ql true 0 f (qf ∪ {%x}) := by
        apply Finset.union_subset; apply (CG.on_telescope TL H3).2; simp [hf]
      have CG1 := ctx_grow.set f H3 hG TL (by simp) (by simp) hf.1.1; apply H0
      apply q_cong'; apply CG1.on_qtp H2; have L := (List.getElem?_eq_some_iff.1 H3).1
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
      specialize TL H1; c_extend TL.2; have := (List.getElem?_eq_some_iff.1 H1).1; omega

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
  (∀ p', p ⊆ p' → qapp G' p' qf qx q1 gs) :=
by
  intro tl Cq1 h; simp only [check_app, excs] at h; split at h
  · simp [excs] at h; obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h; split_ands
    simp [ctx_grow]; simp [sets]; intros; tauto
  apply closedql_bv_tighten at Cq1; assumption'
  simp only [excs] at h; obtain ⟨_, _, h, rfl, rfl⟩ := h; apply M.trycatch_ok at h
  obtain h | h := h; simp only [excs] at h
  · simp at h; obtain ⟨h, rfl⟩ := h; have := check_qtp_wfctx tl h
    split_ands'; simp [sets]; apply check_qtp_sound at h; assumption'; tauto
  obtain ⟨_, -, _, -, h⟩ := h; split at h <;> simp only [excs] at h; simp at h
  next h1 =>
    simp at h1; obtain ⟨-, -, -, -, _, -, -, _, ⟨h2, rfl⟩, G', _, h3, h⟩ := h
    simp at h; obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h; have CG := check_qtp_wfctx tl h3
    apply check_qtp_sound at h3; assumption'; replace h3 := h3.2
    split_ands'; apply closedql_tighten; rw [CG.1]; apply (qtp_closed h3).1
    simp [Finset.eq_empty_iff_forall_notMem] at h2
    have h2a := fun x h => (h2 x h).1
    have h2b := fun x h => (h2 x h).2
    simp [←CG.on_vars_trans h2a, ←CG.on_vars_trans h2b, qapp]
    intro p' h4; right; right; split_ands'; clear *- h4
    intro x; specialize @h4 x; simp [sets] at *; tauto

-- subtyping spec rules

lemma s_ref_spec:
  let G' := G4.take ‖G‖
  let gs' := gs ∪ {‖G‖}
  let gr := gr1 \ {%‖G‖} ∪ gr2 \ {%‖G‖} ∪ qf \ q0
  ctx_grow (G++[(.TTop, q0, .self)]) G1 gs' →
  ctx_grow G1                        G2 gs' →
  ctx_grow G2                        G3 gs' →
  ctx_grow G3                        G4 gs' →
  stp G1 ([#0 ↦ %‖G‖] T1b) {✦}  ([#0 ↦ %‖G‖] T1a) ({✦} ∪ gr1) gs' →
  stp G3 ([#0 ↦ %‖G‖] T2a) {✦}  ([#0 ↦ %‖G‖] T2b) ({✦} ∪ gr2) gs' →
  qtp G2 (gr1 ∪ q1b)             q1a                           gs' →
  qtp G4 (gr2 ∪ [#0 ↦ %‖G‖] q2a) ([#0 ↦ %‖G‖] q2b)             gs' →
  G4[‖G‖]? = some (Tf, qf, bn) →
  closed_ql true 0 ‖G‖ q0 →
  closed_ql false 0 (‖G‖+1) gr1 →
  closed_ql false 0 (‖G‖+1) gr2 →
  closed_ty 0 ‖G‖ (.TRef2 T1a q1a T2a q2a) →
  closed_ty 0 ‖G‖ (.TRef2 T1b q1b T2b q2b) →
  closed_ql false 0 ‖G‖ gr ∧
  ctx_grow G G' gs ∧
  stp G' (.TRef2 T1a q1a T2a q2a) q0 (.TRef2 T1b q1b T2b q2b) (q0 ∪ gr) gs :=
by
  intros G' gs' gr CG1 CG2 CG3 CG4 S1 S2 Q1 Q2 Hqf Cq0 Cg1 Cg2 Cta Ctb
  -- list reasoning
  have CG := CG1.trans (CG2.trans (CG3.trans CG4))
  have CG' := CG.inversion; simp [gs'] at CG'
  obtain ⟨G', q0', rfl, Hq0, Hfr⟩ := CG'; replace CG := CG.shrink (by simp)
  have L := CG.1; simp [L] at Hqf; obtain ⟨rfl, rfl, rfl⟩ := Hqf; simp [G', L]
  clear G'; simp only [L] at S1 S2 Q1 Q2 Cq0 Cg1 Cg2 Hfr Cta Ctb
  -- aux goals
  have Cgr: closed_ql false 0 ‖G'‖ gr := by
    simp [gr, L]; repeat' (apply Finset.union_subset; change closed_ql _ _ _ _)
    apply closedql_tighten; assumption; apply closedql_tighten; assumption'
  split_ands'; apply CG.gs_shrink
  have: closed_ql true 0 ‖G'‖ (q0 ∪ gr) := by
    apply Finset.union_subset; assumption; c_extend;
  -- grow further
  have CG: ctx_grow (G' ++ [(.TTop, q0',     .self)])
                    (G' ++ [(.TTop, q0 ∪ gr, .self)]) gs' := by
    apply ctx_grow.set ‖G'‖; simp; exact ⟨rfl, rfl⟩; simp; rfl; assumption
    have: ✦ ∉ gr := (by c_free); simp [this]; apply Hq0
    simp [gr]; clear *-; intro; simp; tauto; simp [gs', L]
  -- tweak the goal
  apply s_trans; swap; apply s_refl (q2 := q0 ∪ gr); apply q_sub; simp
  assumption'; apply stp.gs_tighten (gs' := gs'); swap; simp [gs']
  apply s_ref
  · apply ctx_grow.on_stp; swap; assumption
    repeat first | assumption | (apply ctx_grow.trans; assumption)
  · apply ctx_grow.on_stp; swap; assumption
    repeat first | assumption | (apply ctx_grow.trans; assumption)
  · apply ctx_grow.on_qtp; swap; assumption
    repeat first | assumption | (apply ctx_grow.trans; assumption)
  · apply ctx_grow.on_qtp; swap; assumption'
  · simp [gr, L]; clear *-; intro _ h; simp [h]; tauto
  · simp [gr, L]; clear *-; intro _ h; simp [h]; tauto

lemma s_pair_spec:
  let G' := G4.take ‖G‖
  let gs' := gs ∪ {‖G‖}
  let gr := gr1 \ {%‖G‖} ∪ gr2 \ {%‖G‖} ∪ qf \ q0
  ctx_grow (G++[(.TTop, q0, .self)]) G1 gs' →
  ctx_grow G1                        G2 gs' →
  ctx_grow G2                        G3 gs' →
  ctx_grow G3                        G4 gs' →
  stp G1 ([#0 ↦ %‖G‖] T1a) {✦}  ([#0 ↦ %‖G‖] T1b) ({✦} ∪ gr1) gs' →
  stp G3 ([#0 ↦ %‖G‖] T2a) {✦}  ([#0 ↦ %‖G‖] T2b) ({✦} ∪ gr2) gs' →
  qtp G2 (gr1 ∪ [#0 ↦ %‖G‖] q1a) ([#0 ↦ %‖G‖] q1b)             gs' →
  qtp G4 (gr2 ∪ [#0 ↦ %‖G‖] q2a) ([#0 ↦ %‖G‖] q2b)             gs' →
  G4[‖G‖]? = some (Tf, qf, bn) →
  closed_ql true 0 ‖G‖ q0 →
  closed_ql false 0 (‖G‖+1) gr1 →
  closed_ql false 0 (‖G‖+1) gr2 →
  closed_ty 0 ‖G‖ (.TProd T1a q1a T2a q2a) →
  closed_ty 0 ‖G‖ (.TProd T1b q1b T2b q2b) →
  closed_ql false 0 ‖G‖ gr ∧
  ctx_grow G G' gs ∧
  stp G' (.TProd T1a q1a T2a q2a) q0 (.TProd T1b q1b T2b q2b) (q0 ∪ gr) gs :=
by
  intros G' gs' gr CG1 CG2 CG3 CG4 S1 S2 Q1 Q2 Hqf Cq0 Cg1 Cg2 Cta Ctb
  -- list reasoning
  have CG := CG1.trans (CG2.trans (CG3.trans CG4))
  have CG' := CG.inversion; simp [gs'] at CG'
  obtain ⟨G', q0', rfl, Hq0, Hfr⟩ := CG'; replace CG := CG.shrink (by simp)
  have L := CG.1; simp [L] at Hqf; obtain ⟨rfl, rfl, rfl⟩ := Hqf; simp [G', L]
  clear G'; simp only [L] at S1 S2 Q1 Q2 Cq0 Cg1 Cg2 Hfr Cta Ctb
  -- aux goals
  have Cgr: closed_ql false 0 ‖G'‖ gr := by
    simp [gr, L]; repeat' (apply Finset.union_subset; change closed_ql _ _ _ _)
    apply closedql_tighten; assumption; apply closedql_tighten; assumption'
  split_ands'; apply CG.gs_shrink
  have: closed_ql true 0 ‖G'‖ (q0 ∪ gr) := by
    apply Finset.union_subset; assumption; c_extend;
  -- grow further
  have CG: ctx_grow (G' ++ [(.TTop, q0',     .self)])
                    (G' ++ [(.TTop, q0 ∪ gr, .self)]) gs' := by
    apply ctx_grow.set ‖G'‖; simp; exact ⟨rfl, rfl⟩; simp; rfl; assumption
    have: ✦ ∉ gr := (by c_free); simp [this]; apply Hq0
    simp [gr]; clear *-; intro; simp; tauto; simp [gs', L]
  -- tweak the goal
  apply s_trans; swap; apply s_refl (q2 := q0 ∪ gr); apply q_sub; simp
  assumption'; apply stp.gs_tighten (gs' := gs'); swap; simp [gs']
  apply s_pair
  · apply ctx_grow.on_stp; swap; assumption
    repeat first | assumption | (apply ctx_grow.trans; assumption)
  · apply ctx_grow.on_stp; swap; assumption
    repeat first | assumption | (apply ctx_grow.trans; assumption)
  · apply ctx_grow.on_qtp; swap; assumption
    repeat first | assumption | (apply ctx_grow.trans; assumption)
  · apply ctx_grow.on_qtp; swap; assumption'
  · simp [gr, L]; clear *-; intro _ h; simp [h]; tauto
  · simp [gr, L]; clear *-; intro _ h; simp [h]; tauto

lemma s_list_spec:
  let G' := G1.take ‖G‖
  let gs' := gs ∪ {‖G‖}
  let gr := gr1 \ {%‖G‖} ∪ qf \ q0
  ctx_grow (G++[(.TTop, q0, .self)]) G1 gs' →
  stp G1 ([#0 ↦ %‖G‖] T1a) {✦}  ([#0 ↦ %‖G‖] T1b) ({✦} ∪ gr1) gs' →
  G1[‖G‖]? = some (Tf, qf, bn) →
  closed_ql true 0 ‖G‖ q0 →
  closed_ql false 0 (‖G‖+1) gr1 →
  closed_ty 0 ‖G‖ (.TList T1a) →
  closed_ty 0 ‖G‖ (.TList T1b) →
  closed_ql false 0 ‖G‖ gr ∧
  ctx_grow G G' gs ∧
  stp G' (.TList T1a) q0 (.TList T1b) (q0 ∪ gr) gs :=
by
  intros G' gs' gr CG S1 Hqf Cq0 Cg1 Cta Ctb
  -- list reasoning
  have CG' := CG.inversion; simp [gs'] at CG'
  obtain ⟨G', q0', rfl, Hq0, Hfr⟩ := CG'; replace CG := CG.shrink (by simp)
  have L := CG.1; simp [L] at Hqf; obtain ⟨rfl, rfl, rfl⟩ := Hqf; simp [G', L]
  clear G'; simp only [L] at S1 Cq0 Cg1 Hfr Cta Ctb
  -- aux goals
  have Cgr: closed_ql false 0 ‖G'‖ gr := by
    simp [gr, L]; repeat' (apply Finset.union_subset; change closed_ql _ _ _ _)
    apply closedql_tighten; assumption; assumption'
  split_ands'; apply CG.gs_shrink
  have: closed_ql true 0 ‖G'‖ (q0 ∪ gr) := by
    apply Finset.union_subset; assumption; c_extend;
  -- grow further
  have CG: ctx_grow (G' ++ [(.TTop, q0',     .self)])
                    (G' ++ [(.TTop, q0 ∪ gr, .self)]) gs' := by
    apply ctx_grow.set ‖G'‖; simp; exact ⟨rfl, rfl⟩; simp; rfl; assumption
    have: ✦ ∉ gr := (by c_free); simp [this]; apply Hq0
    simp [gr]; clear *-; intro; simp; tauto; simp [gs', L]
  -- tweak the goal
  apply s_trans; swap; apply s_refl (q2 := q0 ∪ gr); apply q_sub; simp
  assumption'; apply stp.gs_tighten (gs' := gs'); swap; simp [gs']
  apply s_list
  · apply ctx_grow.on_stp; assumption'
  · simp [gr, L]; clear *-; intro _ h; simp [h]; tauto

lemma s_fun_spec:
  let G' := G4.take ‖G‖
  let gs' := gs ∪ {‖G‖}
  let gr := gr1 \ {%‖G‖} ∪ gr2 \ {%‖G‖, %(‖G‖+1)} ∪ q0' \ q0
  ctx_grow (G ++[(.TTop,           q0,              .self)]) G1 gs' →
  ctx_grow G1                                                G2 gs' →
  ctx_grow (G2++[([#0 ↦ %‖G‖] T1b, [#0 ↦ %‖G‖] q1b, .var)]) G3 gs' →
  ctx_grow G3                                                G4 gs' →
  stp G1 ([#0 ↦ %‖G‖] T1b) {✦} ([#0 ↦ %‖G‖] T1a) ({✦} ∪ gr1) gs' →
  stp G3 ([#0 ↦ %‖G‖] [#1 ↦ (%(‖G‖+1), gr1)] T2a) {✦}
         ([#0 ↦ %‖G‖] [#1 ↦ %(‖G‖+1)]        T2b) ({✦} ∪ gr2) gs' →
  {#0, ✦} ⊆ q1a ∨
  qtp G2 ([#0 ↦ %‖G‖] q1b ∪ gr1) ([#0 ↦ %‖G‖] q1a)      gs' →
  qtp G4 ([#0 ↦ %‖G‖] [#1 ↦ (%(‖G‖+1), gr1)] q2a ∪ gr2)
         ([#0 ↦ %‖G‖] [#1 ↦ %(‖G‖+1)]        q2b)       gs' →
  G4[‖G‖]? = some (Tf, q0', bn) →
  closed_ql true 0 ‖G‖ q0 →
  closed_ql false 0 (‖G‖+1) gr1 →
  closed_ql false 0 (‖G‖+2) gr2 →
  closed_ty 0 ‖G‖ (.TFun T1a q1a T2a q2a) →
  closed_ty 0 ‖G‖ (.TFun T1b q1b T2b q2b) →
  closed_ql false 0 ‖G‖ gr ∧
  ctx_grow G G' gs ∧
  stp G' (.TFun T1a q1a T2a q2a) q0 (.TFun T1b q1b T2b q2b) (q0 ∪ gr) gs :=
by
  intros G' gs' gr CG1 CG2 CG3 CG4 S1 S2 Q1 Q2 Hqf Cq0 Cg1 Cg2 Cta Ctb
  -- list reasoning
  have CG := CG3.trans CG4; have CG' := CG.inversion; simp at CG'
  obtain ⟨G4, rfl⟩ := CG'; replace CG := CG.shrink (by simp)
  replace CG := CG1.trans (CG2.trans CG)
  have CG' := CG.inversion; simp [gs'] at CG'
  obtain ⟨G', q0', rfl, Hq0, Hfr⟩ := CG'; replace CG := CG.shrink (by simp)
  have L := CG.1; simp [L] at Hqf; obtain ⟨rfl, rfl, rfl⟩ := Hqf; simp [G', L]
  clear G'; simp only [L] at CG3 CG4 S1 S2 Q1 Q2 Cq0 Cg1 Cg2 Hfr Cta Ctb
  -- aux goals
  have Cgr: closed_ql false 0 ‖G'‖ gr := by
    simp [gr, L]; repeat' (apply Finset.union_subset; change closed_ql _ _ _ _)
    apply closedql_tighten; assumption
    rw [Finset.sdiff_insert, ←Finset.sdiff_singleton_eq_erase]
    (repeat apply closedql_tighten); assumption'
  split_ands'; apply CG.gs_shrink
  have: closed_ql true 0 ‖G'‖ (q0 ∪ gr) := by
    apply Finset.union_subset; assumption; c_extend;
  -- grow further
  have CG: ctx_grow (G' ++ [(.TTop, q0',     .self)])
                    (G' ++ [(.TTop, q0 ∪ gr, .self)]) gs' := by
    apply ctx_grow.set ‖G'‖; simp; exact ⟨rfl, rfl⟩; simp; rfl; assumption
    have: ✦ ∉ gr := (by c_free); simp [this]; apply Hq0
    simp [gr]; clear *-; intro; simp; tauto; simp [gs', L]
  -- tweak the goal
  apply s_trans; swap; apply s_refl (q2 := q0 ∪ gr); apply q_sub; simp
  assumption'; apply stp.gs_tighten (gs' := gs'); swap; simp [gs']
  have := (CG3.trans (CG4.trans CG.append)).shrink (by simp)
  apply s_fun
  · apply ctx_grow.on_stp; swap; assumption
    apply ctx_grow.trans; assumption'
  · obtain Q1 | Q1 := Q1; simp [Q1]; right
    apply ctx_grow.on_qtp; swap; assumption'
  · rw [List.append_cons]; apply ctx_grow.on_stp; swap; assumption
    apply CG4.trans; apply CG.append
  · rw [List.append_cons]; apply ctx_grow.on_qtp; swap; assumption
    apply CG.append
  · simp [gr, L]; clear *-; intro _ h; simp [h]; tauto
  · simp [gr, L]; clear *-; intro _ h; simp [h]; tauto
  · c_free;

lemma s_all_spec:
  let G' := G4.take ‖G‖
  let gs' := gs ∪ {‖G‖}
  let gr := gr2 \ {%‖G‖, %(‖G‖+1)} ∪ q0' \ q0
  ctx_grow (G ++[(.TTop,           q0,              .self)])  G2 gs' →
  ctx_grow (G2++[([#0 ↦ %‖G‖] T1b, [#0 ↦ %‖G‖] q1b, .tvar)]) G3 gs' →
  ctx_grow G3                                                 G4 gs' →
  stp G3 ([#0 ↦ %‖G‖] [#1 ↦ %(‖G‖+1)] T2a) {✦}
         ([#0 ↦ %‖G‖] [#1 ↦ %(‖G‖+1)] T2b) ({✦} ∪ gr2) gs' →
  {#0, ✦} ⊆ q1a ∨
  qtp G2 ([#0 ↦ %‖G‖] q1b) ([#0 ↦ %‖G‖] q1a)      gs' →
  qtp G4 ([#0 ↦ %‖G‖] [#1 ↦ %(‖G‖+1)] q2a ∪ gr2)
         ([#0 ↦ %‖G‖] [#1 ↦ %(‖G‖+1)]       q2b)  gs' →
  G4[‖G‖]? = some (Tf, q0', bn) →
  closed_ql true 0 ‖G‖ q0 →
  closed_ql false 0 (‖G‖+2) gr2 →
  closed_ty 0 ‖G‖ (.TAll T1b q1a T2a q2a) →
  closed_ty 0 ‖G‖ (.TAll T1b q1b T2b q2b) →
  closed_ql false 0 ‖G‖ gr ∧
  ctx_grow G G' gs ∧
  stp G' (.TAll T1b q1a T2a q2a) q0 (.TAll T1b q1b T2b q2b) (q0 ∪ gr) gs :=
by
  intros G' gs' gr CG2 CG3 CG4 S2 Q1 Q2 Hqf Cq0 Cg2 Cta Ctb
  -- list reasoning
  have CG := CG3.trans CG4; have CG' := CG.inversion; simp at CG'
  obtain ⟨G4, rfl⟩ := CG'; replace CG := CG.shrink (by simp)
  replace CG := CG2.trans CG; have CG' := CG.inversion; simp [gs'] at CG'
  obtain ⟨G', q0', rfl, Hq0, Hfr⟩ := CG'; replace CG := CG.shrink (by simp)
  have L := CG.1; simp [L] at Hqf; obtain ⟨rfl, rfl, rfl⟩ := Hqf; simp [G', L]
  clear G'; simp only [L] at CG3 CG4 S2 Q1 Q2 Cq0 Cg2 Hfr Cta Ctb
  -- aux goals
  have Cgr: closed_ql false 0 ‖G'‖ gr := by
    simp [gr, L]; repeat' (apply Finset.union_subset; change closed_ql _ _ _ _)
    rw [Finset.sdiff_insert, ←Finset.sdiff_singleton_eq_erase]
    (repeat apply closedql_tighten); assumption'
  split_ands'; apply CG.gs_shrink
  have: closed_ql true 0 ‖G'‖ (q0 ∪ gr) := by
    apply Finset.union_subset; assumption; c_extend;
  -- grow further
  have CG: ctx_grow (G' ++ [(.TTop, q0',     .self)])
                    (G' ++ [(.TTop, q0 ∪ gr, .self)]) gs' := by
    apply ctx_grow.set ‖G'‖; simp; exact ⟨rfl, rfl⟩; simp; rfl; assumption
    have: ✦ ∉ gr := (by c_free); simp [this]; apply Hq0
    simp [gr]; clear *-; intro; simp; tauto; simp [gs', L]
  -- tweak the goal
  apply s_trans; swap; apply s_refl (q2 := q0 ∪ gr); apply q_sub; simp
  assumption'; apply stp.gs_tighten (gs' := gs'); swap; simp [gs']
  have := (CG3.trans (CG4.trans CG.append)).shrink (by simp)
  apply s_all
  · apply s_refl; apply q_sub; simp; simp [sets]
  · obtain Q1 | Q1 := Q1; simp [Q1]; right
    apply ctx_grow.on_qtp; swap; assumption'
  · rw [List.append_cons]; apply ctx_grow.on_stp; swap; assumption
    apply CG4.trans; apply CG.append
  · rw [List.append_cons]; apply ctx_grow.on_qtp; swap; assumption
    apply CG.append
  · simp [gr, L]; clear *-; intro _ h; simp [h]; tauto

-- subtype checking

lemma check_stp2_sound (TL: telescope G):
  check_stp2 fuel G q0 T1 T2 gs σ1 = .ok (gr, G') σ2 →
  closed_ql true 0 ‖G‖ q0 → closed_ty 0 ‖G‖ T1 → closed_ty 0 ‖G‖ T2 →
  closed_ql false 0 ‖G‖ gr ∧ ctx_grow G G' gs ∧ stp G' T1 q0 T2 (q0 ∪ gr) gs :=
by
  intro h Cq0 Ct1 Ct2; induction fuel generalizing G q0 T1 T2 gs gr G' σ1 σ2
  · simp only [check_stp2, excs] at h; obtain ⟨_, _, h, -⟩ := h
    simp [check_stp2.go, excs] at h
  rename_i fuel ih; simp [check_stp2, excs, -bind_pure_comp] at h
  obtain ⟨σ2, h, -⟩ := h; generalize hfuel: fuel + 1 = fuel0 at h
  fun_cases check_stp2.go fuel0 G q0 T1 T2 gs
  rotate_right; next => simp only [check_stp2.go, excs] at h
  all_goals simp at hfuel; subst hfuel
  next => -- unit
    simp only [check_stp2.go, excs] at h; simp at h; obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    simp [ctx_grow, closed_ql]; apply s_refl; apply q_sub; simp; assumption
  next => -- nat
    simp only [check_stp2.go, excs] at h; simp at h; obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    simp [ctx_grow, closed_ql]; apply s_refl; apply q_sub; simp; assumption
  next => -- top
    simp only [check_stp2.go, excs] at h; simp at h; obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    simp [ctx_grow, closed_ql]; apply s_top
  next h1 => -- tvar refl
    simp only [check_stp2.go, excs] at h; obtain ⟨rfl, h1⟩ := h1; simp [h1, excs] at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h; simp [ctx_grow, closed_ql]; apply s_refl
    apply q_sub; simp; assumption
  next x _ h1 => -- tvar exposure
    simp only [check_stp2.go, excs] at h; simp [h1, excs] at h
    obtain ⟨Tx, ⟨_, h2⟩, h⟩ := h
    have Ctx: closed_ty 0 ‖G‖ Tx := by
      specialize TL h2; c_extend TL.1; rw [List.getElem?_eq_some_iff] at h2
      replace h2 := h2.1; omega
    specialize ih TL h Cq0 Ctx Ct2; obtain ⟨_, cg, s2⟩ := ih; split_ands'
    apply s_trans; rotate_left 2; simpa; rwa [←cg.1]
    have h2' := cg.2 x; simp [h2] at h2'; symm at h2'; apply s_tvar; assumption'
  next => -- tref
    simp only [check_stp2.go, excs] at h
    obtain ⟨⟨gr1, G1⟩, _, h1, G2, _, h2, ⟨gr2, G3⟩, _, h3, G4, _, h4, h⟩ := h
    simp [-Finset.union_assoc] at h2 h4 h
    obtain ⟨_, g, ⟨_, h5⟩, ⟨h6, h7⟩, rfl⟩ := h
    replace TL: telescope (G ++ [(.TTop, q0, .self)]) := by
      apply telescope_extend; simp!; assumption'
    apply ih at h1; assumption'; specialize h1 _ _ _; simp [sets]
    c_subst; c_extend Ct2.1; c_subst; c_extend Ct1.1; simp at h1
    have CG := h1.2.1; replace TL := CG.on_telescope TL
    apply check_qtp_sound at h2; assumption'; swap
    · simp [←CG.1]; obtain ⟨-, -, _, -, _, -⟩ := Ct1
      apply closedql_bv_tighten; assumption; c_extend;
    replace CG := CG.trans h2.1; replace TL := h2.1.on_telescope TL
    apply ih at h3; assumption'
    simp [←CG.1] at h3; specialize h3 _ _ _; simp [sets]
    c_subst; c_extend Ct1.2.1; c_subst; c_extend Ct2.2.1
    replace CG := CG.trans h3.2.1; replace TL := h3.2.1.on_telescope TL
    apply check_qtp_sound at h4; assumption'; swap
    · simp [←CG.1]; obtain ⟨-, -, -, _, -⟩ := Ct2; c_subst; c_extend;
    subst G' gr; casesm* _ ∧ _; apply s_ref_spec; assumption'
  next => -- tpair
    simp only [check_stp2.go, excs] at h
    obtain ⟨⟨gr1, G1⟩, _, h1, G2, _, h2, ⟨gr2, G3⟩, _, h3, G4, _, h4, h⟩ := h
    simp [-Finset.union_assoc] at h2 h4 h
    obtain ⟨_, g, ⟨_, h5⟩, ⟨h6, h7⟩, rfl⟩ := h
    replace TL: telescope (G ++ [(.TTop, q0, .self)]) := by
      apply telescope_extend; simp!; assumption'
    apply ih at h1; assumption'; specialize h1 _ _ _; simp [sets]
    c_subst; c_extend Ct1.1; c_subst; c_extend Ct2.1; simp at h1
    have CG := h1.2.1; replace TL := CG.on_telescope TL
    apply check_qtp_sound at h2; assumption'; swap
    · simp [←CG.1]; obtain ⟨-, -, _, -, _, -⟩ := Ct2; c_subst; c_extend;
    replace CG := CG.trans h2.1; replace TL := h2.1.on_telescope TL
    apply ih at h3; assumption'
    simp [←CG.1] at h3; specialize h3 _ _ _; simp [sets]
    c_subst; c_extend Ct1.2.1; c_subst; c_extend Ct2.2.1
    replace CG := CG.trans h3.2.1; replace TL := h3.2.1.on_telescope TL
    apply check_qtp_sound at h4; assumption'; swap
    · simp [←CG.1]; obtain ⟨-, -, -, _, -⟩ := Ct2; c_subst; c_extend;
    subst G' gr; casesm* _ ∧ _; apply s_pair_spec; assumption'
  next => -- tlist
    simp only [check_stp2.go, excs] at h; obtain ⟨⟨gr1, G1⟩, _, h1, h⟩ := h
    simp at h; obtain ⟨_, g, ⟨_, h5⟩, ⟨h6, h7⟩, rfl⟩ := h
    replace TL: telescope (G ++ [(.TTop, q0, .self)]) := by
      apply telescope_extend; simp!; assumption'
    apply ih at h1; assumption'; specialize h1 _ _ _; simp [sets]
    c_subst; c_extend Ct1.1; c_subst; c_extend Ct2.1; simp at h1
    subst G' gr; casesm* _ ∧ _; apply s_list_spec; assumption'
  next q1a _ _ T1b q1b _ _ gs' => -- tfun
    simp only [check_stp2.go, excs] at h
    obtain ⟨⟨gr1, G1⟩, _, S1, G2, _, Q1, ⟨gr2, G3⟩, _, S2, G4, _, Q2, h⟩ := h
    simp [-Finset.union_assoc] at Q1 S2 Q2 h; obtain ⟨T0, _, ⟨b0, h1⟩, ⟨h, h2⟩, rfl⟩ := h
    replace TL: telescope (G ++ [(.TTop, q0, .self)]) := by
      apply telescope_extend; simp!; assumption'
    have S1 := ih TL S1 ?_ ?_ ?_; rotate_left; simp [sets]
    · c_subst; c_extend Ct2.1
    · c_subst; c_extend Ct1.1
    simp at S1; replace TL := S1.2.1.on_telescope TL
    have LG := Eq.symm S1.2.1.1; simp at LG
    replace Q1: ctx_grow G1 G2 gs' ∧
        ({#0, ✦} ⊆ q1a ∨ qtp G2 ([#0 ↦ %‖G‖] q1b ∪ gr1) ([#0 ↦ %‖G‖] q1a) gs') := by
      split at Q1 <;> rename_i hq1a
      · simp [excs] at Q1; obtain ⟨rfl, rfl⟩ := Q1; simp [ctx_grow, hq1a]
      · apply check_qtp_sound at Q1; clear *- Q1; tauto; assumption
        simp [LG]; c_subst; c_extend Ct1.2.2.1;
    replace LG := Q1.1.1 ▸ LG
    replace TL: telescope (G2 ++ [([#0 ↦ %‖G‖] T1b, [#0 ↦ %‖G‖] q1b, .var)]) := by
      simp; apply telescope_extend; rotate_right; apply Q1.1.on_telescope TL
      simp [LG]; c_subst; c_extend Ct2.1
      simp [LG]; c_subst; c_extend Ct2.2.2.1
    have S2 := ih TL S2 ?_ ?_ ?_; rotate_left; simp [sets]
    · simp [LG]; c_subst; c_extend Ct1.2.1; omega
      apply Finset.union_subset; simp [sets]; c_extend S1.1
    · simp [LG]; c_subst; c_extend Ct2.2.1; omega
    simp [LG] at S2; replace TL := S2.2.1.on_telescope TL
    replace LG := by have := Eq.symm S2.2.1.1; simp [LG] at this; exact this
    apply check_qtp_sound at Q2; assumption'; swap
    · simp [LG]; c_subst; c_extend Ct2.2.2.2.1; omega
    clear LG; replace TL := Q2.1.on_telescope TL
    subst gr G'; casesm* _ ∧ _; apply s_fun_spec; assumption'
  next T1b q1a _ _ _ q1b _ _ => -- tall
    simp only [check_stp2.go, excs] at h
    obtain ⟨-, _, ⟨rfl, rfl⟩, G2, _, Q1, ⟨gr2, G3⟩, _, S2, G4, _, Q2, h⟩ := h
    simp [-Finset.union_assoc] at S2 Q2 h; obtain ⟨T0, _, ⟨b0, h1⟩, ⟨h, h2⟩, rfl⟩ := h
    let G1 := G ++ [(.TTop, q0, .self)]; let gs' := gs ∪ {‖G‖}
    replace TL: telescope G1 := by
      apply telescope_extend; simp!; assumption'
    replace Q1: ctx_grow G1 G2 gs' ∧
        ({#0, ✦} ⊆ q1a ∨ qtp G2 ([#0 ↦ %‖G‖] q1b) ([#0 ↦ %‖G‖] q1a) gs') := by
      split at Q1 <;> rename_i hq1a
      · simp [excs] at Q1; obtain ⟨rfl, rfl⟩ := Q1; simp [ctx_grow, hq1a, G1]
      · apply check_qtp_sound at Q1; clear *- Q1; tauto; assumption
        simp; c_subst; c_extend Ct1.2.2.1
    have LG := Eq.symm Q1.1.1; simp [G1] at LG
    replace TL: telescope (G2 ++ [([#0 ↦ %‖G‖] T1b, [#0 ↦ %‖G‖] q1b, .tvar)]) := by
      simp; apply telescope_extend; rotate_right; apply Q1.1.on_telescope TL
      simp [LG]; c_subst; c_extend Ct2.1
      simp [LG]; c_subst; c_extend Ct2.2.2.1
    have S2 := ih TL S2 ?_ ?_ ?_; rotate_left; simp [sets]
    · simp [LG]; c_subst; c_extend Ct1.2.1; omega
    · simp [LG]; c_subst; c_extend Ct2.2.1; omega
    simp [LG] at S2; replace TL := S2.2.1.on_telescope TL
    replace LG := by have := Eq.symm S2.2.1.1; simp [LG] at this; exact this
    apply check_qtp_sound at Q2; assumption'; swap
    · simp [LG]; c_subst; c_extend Ct2.2.2.2.1; omega
    clear LG; replace TL := Q2.1.on_telescope TL
    subst gr G'; casesm* _ ∧ _; apply s_all_spec; assumption'

lemma check_stp2_fuel (TL: telescope G):
  closed_ql true 0 ‖G‖ q0 → closed_ty 0 ‖G‖ T1 → closed_ty 0 ‖G‖ T2 →
  check_stp2 fuel G q0 T1 T2 gs σ1 = .ok (gr, G') σ2 →
  sub_size G T1 + sub_size G T2 ≤ fuel' →
  check_stp2 fuel' G q0 T1 T2 gs σ1 = .ok (gr, G') σ2 :=
by
  intro Cq0 Ct1 Ct2 h Hfuel
  induction fuel generalizing G q0 T1 T2 gs gr G' fuel' σ1 σ2
  · simp only [check_stp2, excs] at h; obtain ⟨_, _, h, -⟩ := h
    simp [check_stp2.go, excs] at h
  simp [check_stp2, excs, -bind_pure_comp] at h ⊢
  obtain ⟨σ2, h, h1⟩ := h; exists σ2; split_ands'; clear h1
  rename_i fuel ih _ ; generalize Hf0: fuel + 1 = fuel0 at h
  fun_cases check_stp2.go fuel0 G q0 T1 T2 gs
  rotate_right; next => simp [check_stp2.go, excs] at h
  all_goals simp at Hf0; subst Hf0
  all_goals cases fuel' <;> simp [sub_size, sub_size'] at Hfuel; rename_i fuel'
  next => -- unit
    simpa only [check_stp2.go] using h
  next => -- nat
    simpa only [check_stp2.go] using h
  next => -- top
    simpa only [check_stp2.go] using h
  next h1 => -- tvar refl
    simp only [check_stp2.go] at h ⊢; simpa only [h1] using h
  next h1 h2 => -- tvar: exposure
    simp only [check_stp2.go, h2, ↓reduceIte] at h ⊢; simp only [excs] at h ⊢
    obtain ⟨⟨Tx, qx, bn⟩, _, ⟨h3, rfl⟩, -, _, ⟨rfl, rfl⟩, h⟩ := h
    refine ⟨_, _, ⟨h3, rfl⟩, default, _, ⟨rfl, rfl⟩, ?_⟩; simp only at h ⊢
    have h3' := TL h3; apply ih; assumption'
    · c_extend h3'.1; have := List.getElem?_eq_some' h3; omega
    simp only [sub_size]; apply tenv.sub_sizes_spec at h3
    simp only [h3, Option.getD_some] at Hfuel
    rw [subsize_prefix h3'.1] at Hfuel; omega
  next T1a _ _ _ T1b _ _ _ _ => -- tref
    simp only [check_stp2.go, excs] at h ⊢
    obtain ⟨⟨gr1, G1⟩, _, h1, G2, _, h2, h⟩ := h
    let G' := G ++ [(.TTop, q0, .self)]; replace TL: telescope G' := by
      apply telescope_extend; simp!; assumption'
    have Cb: closed_ty 0 ‖G'‖ [#0↦%‖G‖] T1b := by simp [G']; c_subst; c_extend Ct2.1
    have Ca: closed_ty 0 ‖G'‖ [#0↦%‖G‖] T1a := by simp [G']; c_subst; c_extend Ct1.1
    have ih1 := ih (fuel':=fuel') TL (by simp [sets]) Cb Ca h1 ?_
    swap; simp [sub_size, G']; omega; refine ⟨_, _, ih1, _, _, h2, ?_⟩; clear ih1
    apply check_stp2_sound at h1; specialize h1 _ _ _; simp [sets]; assumption'
    have CG := h1.2.1; replace TL := h1.2.1.on_telescope TL; clear h1
    apply check_qtp_sound at h2; assumption'; swap
    · simp [←CG.1]; obtain ⟨-, -, _, -, _, -⟩ := Ct1
      apply closedql_bv_tighten; assumption; c_extend;
    replace TL := h2.1.on_telescope TL; replace CG := CG.trans h2.1; clear h2
    obtain ⟨⟨gr2, G3⟩, _, h3, h⟩ := h
    have ih2 := @ih G2; simp only [←CG.1] at ih2;
    specialize ih2 (fuel':=fuel') TL (by simp [sets])
      (by c_subst; c_extend Ct1.2.1) (by c_subst; c_extend Ct2.2.1) h3 _
    simp only [CG.on_subsize]; simp [sub_size]; omega
    refine ⟨_, _, ih2, h⟩
  next T1a _ _ _ T1b _ _ _ _ => -- tprod
    simp only [check_stp2.go, excs] at h ⊢
    obtain ⟨⟨gr1, G1⟩, _, h1, G2, _, h2, h⟩ := h
    let G' := G ++ [(.TTop, q0, .self)]; replace TL: telescope G' := by
      apply telescope_extend; simp!; assumption'
    have Cb: closed_ty 0 ‖G'‖ [#0↦%‖G‖] T1b := by simp [G']; c_subst; c_extend Ct2.1
    have Ca: closed_ty 0 ‖G'‖ [#0↦%‖G‖] T1a := by simp [G']; c_subst; c_extend Ct1.1
    have ih1 := ih (fuel' := fuel') TL (by simp [sets]) Ca Cb h1 ?_
    swap; simp [sub_size, G']; omega; refine ⟨_, _, ih1, _, _, h2, ?_⟩; clear ih1
    apply check_stp2_sound at h1; specialize h1 _ _ _; simp [sets]; assumption'
    have CG := h1.2.1; replace TL := h1.2.1.on_telescope TL; clear h1
    apply check_qtp_sound at h2; assumption'; swap
    · simp [←CG.1]; obtain ⟨-, -, _, -, _, -⟩ := Ct2; c_subst; c_extend;
    replace TL := h2.1.on_telescope TL; replace CG := CG.trans h2.1; clear h2
    obtain ⟨⟨gr2, G3⟩, _, h3, h⟩ := h
    have ih2 := @ih G2; simp only [←CG.1] at ih2;
    specialize ih2 (fuel':=fuel') TL (by simp [sets])
      (by c_subst; c_extend Ct1.2.1) (by c_subst; c_extend Ct2.2.1) h3 _
    simp only [CG.on_subsize]; simp [sub_size]; omega
    refine ⟨_, _, ih2, h⟩
  next T1 T2 _ => -- tlist
    simp only [check_stp2.go, excs] at h ⊢; obtain ⟨⟨gr1, G1⟩, _, h1, h⟩ := h
    let G' := G ++ [(.TTop, q0, .self)]; replace TL: telescope G' := by
      apply telescope_extend; simp!; assumption'
    have Cb: closed_ty 0 ‖G'‖ [#0↦%‖G‖] T2 := by simp [G']; c_subst; c_extend Ct2.1
    have Ca: closed_ty 0 ‖G'‖ [#0↦%‖G‖] T1 := by simp [G']; c_subst; c_extend Ct1.1
    have ih1 := ih (fuel' := fuel') TL (by simp [sets]) Ca Cb h1 ?_
    swap; simp [sub_size, G']; omega; refine ⟨_, _, ih1, h⟩
  next T1a _ _ _ T1b q1b _ _ _ => -- tfun
    simp only [check_stp2.go, excs] at h ⊢
    obtain ⟨⟨gr1, G1⟩, _, S1, G2, _, Q1, ⟨gr2, G3⟩, _, S2, h⟩ := h; simp at Q1 S2
    replace TL: telescope (G ++ [(.TTop, q0, .self)]) := by
      apply telescope_extend; simp!; assumption'
    have Ct2: closed_ty 0 (‖G‖ + 1) [#0 ↦ %‖G‖] T1b := by c_subst; c_extend Ct2.1
    have Ct1: closed_ty 0 (‖G‖ + 1) [#0 ↦ %‖G‖] T1a := by c_subst; c_extend Ct1.1
    have ih1 := ih (fuel' := fuel') TL ?_ (by simpa using Ct2) (by simpa using Ct1) S1 ?_
    rotate_left; simp [sets]; simp [sub_size]; omega; refine ⟨_, _, ih1, ?_⟩
    apply check_stp2_sound at S1; assumption'; simp at S1; specialize S1 (by simp [sets]) Ct2 Ct1
    obtain ⟨Hgr1, S1, -⟩ := S1; refine ⟨_, _, Q1, ?_⟩; replace TL := S1.on_telescope TL
    replace Q1: ctx_grow G1 G2 (gs ∪ {‖G‖}) := by
      split at Q1; simp [excs] at Q1; obtain ⟨rfl, rfl⟩ := Q1; simp [ctx_grow]
      apply check_qtp_wfctx at Q1; assumption'
    replace TL := Q1.on_telescope TL; replace Q1 := S1.trans Q1; clear S1 ih1
    let elem := ([#0↦%‖G‖] T1b, [#0↦%‖G‖] q1b, binding.var)
    have ih2 := fun {q0 T1 T2 gs σ1} => @ih (G2++[elem]) q0 T1 T2 gs σ1 gr2
    replace TL: telescope (G2 ++ [elem]) := by
      simp [elem]; apply telescope_extend; assumption'; simpa [←Q1.1]
      simp [←Q1.1]; c_subst; clear Ct2; c_extend Ct2.2.2.1
    clear Ct1 Ct2; simp [←Q1.1] at ih2; replace Q1 := Q1.append (g := [elem])
    simp [elem] at TL Q1 ih2; clear elem; simp [Q1.on_subsize] at ih2
    specialize ih2 (fuel' := fuel') TL _ _ _ S2 _; simp [sets]
    · clear ih2; c_subst; c_extend Ct1.2.1; omega
      apply Finset.union_subset; simp [sets]; c_extend;
    · c_subst; c_extend Ct2.2.1; omega
    · clear ih2; simp [sub_size]
      rw [←ty.subst_open_chain #1 %(‖G‖+1), ty.open_subst_comm, ty.subst_preserves_subsize]
      omega; simp; apply Finset.union_subset; simp [sets]; c_extend; simp
      simp; intro; c_free; simp!; simp; c_free Ct1.2.1
    refine ⟨_, _, ih2, h⟩
  next T1a _ _ _ T1b q1b _ _ => -- tall
    simp only [check_stp2.go, excs] at h ⊢
    obtain ⟨-, _, ⟨rfl, rfl⟩, G2, _, Q1, ⟨gr2, G3⟩, _, S2, h⟩ := h; simp at Q1 S2
    let G1 := G ++ [(.TTop, q0, .self)]; replace TL: telescope G1 := by
      apply telescope_extend; simp!; assumption'
    refine ⟨default, _, ⟨rfl, rfl⟩, _, _, Q1, ?_⟩
    replace Q1: ctx_grow G1 G2 (gs ∪ {‖G‖}) := by
      split at Q1; simp [excs] at Q1; obtain ⟨rfl, rfl⟩ := Q1; simp [ctx_grow, G1]
      apply check_qtp_wfctx at Q1; assumption'
    replace TL := Q1.on_telescope TL
    let elem := ([#0↦%‖G‖] T1a, [#0↦%‖G‖] q1b, binding.tvar)
    have ih2 := @ih (G2 ++ [elem])
    replace TL: telescope (G2 ++ [elem]) := by
      simp [elem]; apply telescope_extend; assumption'
      simp [←Q1.1, G1]; c_subst; c_extend Ct2.1
      simp [←Q1.1, G1]; c_subst; c_extend Ct2.2.2.1
    simp [←Q1.1] at ih2; replace Q1 := Q1.append (g := [elem])
    simp [elem] at TL Q1 ih2; clear elem; simp [Q1.on_subsize, G1] at ih2
    specialize ih2 (fuel' := fuel') TL _ _ _ S2 _; simp [sets]
    · clear ih2; c_subst; c_extend Ct1.2.1; omega
    · clear ih2; c_subst; c_extend Ct2.2.1; omega
    · clear ih2; simp [sub_size]; omega
    refine ⟨_, _, ih2, h⟩

lemma unpack_self_equiv G gs:
  unpack_self T1 q0 = T1' → gs ⊆ Finset.range ‖G‖ →
  closed_ty 0 ‖G‖ T1 → closed_ql true 0 ‖G‖ q0 →
  closed_ty 0 ‖G‖ T1' ∧ stp G T1 q0 T1' q0 gs ∧ stp G T1' q0 T1 q0 gs :=
by
  intro h hgs C Cq0; replace hgs: ‖G‖ ∉ gs := by
    intro h; specialize hgs h; simp at hgs
  simp [unpack_self] at h; split at h; subst T1'
  simp [C]; apply s_refl; apply q_sub; simp; assumption
  apply closedql_fr_tighten at Cq0; assumption'; split at h <;> subst T1'
  · simp [C]; apply s_refl; apply q_sub; simp; c_extend;
  · simp [C]; apply s_refl; apply q_sub; simp; c_extend;
  · simp [C]; apply s_refl; apply q_sub; simp; c_extend;
  · simp [C]; apply s_refl; apply q_sub; simp; c_extend;
  next T1 q1 T2 q2 => -- TRef
    -- T1
    let T1' := [#0 ↦ %‖G‖] T1
    have h1 := @ty.self_subst_equiv (G++[_]) ‖G‖ .TTop q0 _ {✦} T1' (by simp; rfl)
      hgs (by simp [sets]) (by c_extend) (by c_subst; c_extend C.1)
      (by simp [T1']; right; simp! at C; simp [C]; c_free C.1)
    have HT1: [%‖G‖ ↦ q0] T1' = [#0 ↦ %‖G‖] [#0 ↦ q0] T1 := by
      simp [T1']; rw [ty.subst_open_chain, ty.open_free]
      rw [occurs_subst]; simp; intro; c_free; simp!; c_free C.1
    rw [HT1] at h1; simp [T1'] at h1; clear HT1 T1'
    -- T1
    let T2' := [#0 ↦ %‖G‖] T2
    have h2 := @ty.self_subst_equiv (G++[_]) ‖G‖ .TTop q0 _ {✦} T2' (by simp; rfl)
      hgs (by simp [sets]) (by c_extend) (by c_subst; c_extend C.2.1)
      (by simp [T2']; left; simp! at C; simp [C]; c_free C.2.1)
    have HT2: [%‖G‖ ↦ q0] T2' = [#0 ↦ %‖G‖] [#0 ↦ q0] T2 := by
      simp [T2']; rw [ty.subst_open_chain, ty.open_free (x := #0)]
      rw [occurs_subst]; simp; intro; c_free; simp!; c_free C.2.1
    rw [HT2] at h2; simp only [instSubstTyQl, T2'] at h2; clear HT2 T2'
    -- q1
    have h3: ∀ a, qtp (G ++ [a]) q1 q1 gs := by
      intro; apply q_sub; simp; obtain ⟨-,-,_,-,_,-⟩ := C
      apply closedql_bv_tighten; assumption; c_extend;
    -- q2
    let q2' := [#0 ↦ %‖G‖] q2
    have h4 := @ql.self_subst_equiv (G ++ [_]) ‖G‖ .TTop q0 q2' _ (by simp; rfl)
      (by c_extend) (by simp [q2']; c_subst; c_extend C.2.2.2.1) hgs
    have HQ2: [%‖G‖ ↦ q0] q2' = [#0 ↦ %‖G‖] [#0 ↦ q0] q2 := by
      simp [q2']; rw [ql.subst_chain]; generalize hq2': [#0↦q0] q2 = q2'
      simp [subst]; have: #0 ∉ q2' := by subst q2'; simp [subst]; intro; c_free;
      simp [this]; c_free C.2.2.2.1
    rw [HQ2] at h4; simp only [instSubstQlId, q2'] at h4; clear HQ2 q2'
    -- final
    split_ands
    · simp! at C ⊢; split_ands
      · rw [closedty_subst]; simp [C]; assumption; simp!; simp
      · rw [closedty_subst]; simp [C]; assumption; simp!; simp
      · simp [C]
      · rw [closedql_subst]; simp [C]; c_extend; simp
      · simp [C]
      · rw [occurs_subst]; simp; intro; c_free; simp!
      · rw [occurs_subst]; simp; intro; c_free; simp!
    · apply s_ref (gr1 := ∅) (gr2 := ∅); rotate_left 4; simp; simp; simp
      apply h1.2; simp; apply h2.1; simp; apply h3; simp; apply h4.1
    · apply s_ref (gr1 := ∅) (gr2 := ∅); rotate_left 4; simp; simp; simp
      apply h1.1; simp; apply h2.2; simp; apply h3; simp; apply h4.2
  next T1 q1 T2 q2 => -- TFun
    -- T1
    let T1' := [#0 ↦ %‖G‖] T1
    have h1 := @ty.self_subst_equiv (G++[_]) ‖G‖ .TTop q0 gs {✦} T1' (by simp; rfl)
      hgs (by simp [sets]) (by c_extend) (by c_subst; c_extend C.1)
      (by simp [T1']; right; simp! at C; simp [C]; c_free C.1)
    have HT1: [%‖G‖ ↦ q0] T1' = [#0 ↦ %‖G‖] [#0 ↦ q0] T1 := by
      simp [T1']; rw [ty.subst_open_chain, ty.open_free]
      rw [occurs_subst]; simp; intro; c_free; simp!; c_free C.1
    rw [HT1] at h1; simp [T1'] at h1; clear HT1 T1'
    -- T1
    let T2' := [#0 ↦ %‖G‖] [#1 ↦ %(‖G‖+1)] T2
    have h2 := fun a => @ty.self_subst_equiv (G++[_,a]) ‖G‖ .TTop q0 gs {✦} T2'
      (by simp; rfl) hgs (by simp [sets]) (by c_extend) (by c_subst; c_extend C.2.1)
      (by simp [T2']; left; simp! at C; simp [C]; c_free C.2.1)
    have HT2: [%‖G‖ ↦ q0] T2' = [#0 ↦ %‖G‖] [#1 ↦ %(‖G‖+1)] [#0 ↦ q0] T2 := by
      simp [T2']; rw [ty.subst_open_chain, ty.open_subst_comm, ty.open_free (x := #0)]
      rw [occurs_subst]; simp; intro; c_free; simp!; simp; intro; c_free; simp!
      simp; simp; c_free C.2.1
    rw [HT2] at h2; simp only [instSubstTyQl, T2'] at h2; clear HT2 T2'
    -- q1
    have h3: ∀ a, qtp (G ++ [a]) ([#0 ↦ %‖G‖] q1) ([#0 ↦ %‖G‖] q1) gs := by
      intro; apply q_sub; simp; simp; c_subst; c_extend C.2.2.1
    -- q2
    let q2' := [#0 ↦ %‖G‖] [#1 ↦ %(‖G‖+1)] q2
    have h4 := fun a => @ql.self_subst_equiv (G++[_,a]) ‖G‖ .TTop q0 q2' gs
      (by simp; rfl) (by c_extend) (by simp [q2']; c_subst; c_extend C.2.2.2.1) hgs
    have HQ2: [%‖G‖ ↦ q0] q2' = [#0 ↦ %‖G‖] [#1 ↦ %(‖G‖+1)] [#0 ↦ q0] q2 := by
      simp [q2']; rw [ql.subst_chain, ql.subst_comm]
      generalize hq2': [#1↦{%(‖G‖ + 1)}] [#0↦q0] q2 = q2'; simp [subst]
      have: #0 ∉ q2' := by subst q2'; simp [subst]; intro; c_free;
      simp [this]; c_free; simp; simp; simp [subst]; c_free C.2.2.2.1
    rw [HQ2] at h4; simp only [instSubstQlId, q2'] at h4; clear HQ2 q2'
    -- final
    split_ands
    · simp! at C ⊢; split_ands
      · rw [closedty_subst]; simp [C]; assumption; simp!; simp
      · rw [closedty_subst]; simp [C]; assumption; simp!; simp
      · simp [C]
      · rw [closedql_subst]; simp [C]; c_extend; simp
      · intro h; simp [h] at C; simp [C]
      · rw [occurs_subst]; simp; intro; c_free; simp!
      · rw [occurs_subst]; simp; intro; c_free; simp!
    · apply s_fun (gr1 := ∅) (gr2 := ∅); rotate_left 4; simp; simp; simp
      apply h1.2; right; simp; apply h3; simp; apply (h2 _).1; simp; apply (h4 _).1
    · apply s_fun (gr1 := ∅) (gr2 := ∅); rotate_left 4; simp; simp; simp
      apply h1.1; right; simp; apply h3; simp; apply (h2 _).2; simp; apply (h4 _).2
  next T1 q1 T2 q2 => -- TAll
    -- T1
    let T1' := [#0 ↦ %‖G‖] T1
    have h1 := @ty.self_subst_equiv (G++[_]) ‖G‖ .TTop q0 gs {✦} T1' (by simp; rfl)
      hgs (by simp [sets]) (by c_extend) (by c_subst; c_extend C.1)
      (by simp [T1']; right; simp! at C; simp [C]; c_free C.1)
    have HT1: [%‖G‖ ↦ q0] T1' = [#0 ↦ %‖G‖] [#0 ↦ q0] T1 := by
      simp [T1']; rw [ty.subst_open_chain, ty.open_free]
      rw [occurs_subst]; simp; intro; c_free; simp!; c_free C.1
    rw [HT1] at h1; simp [T1'] at h1; clear HT1 T1'
    -- T1
    let T2' := [#0 ↦ %‖G‖] [#1 ↦ %(‖G‖+1)] T2
    have h2 := fun a => @ty.self_subst_equiv (G++[_,a]) ‖G‖ .TTop q0 gs {✦} T2'
      (by simp; rfl) hgs (by simp [sets]) (by c_extend) (by c_subst; c_extend C.2.1)
      (by simp [T2']; left; simp! at C; simp [C]; c_free C.2.1)
    have HT2: [%‖G‖ ↦ q0] T2' = [#0 ↦ %‖G‖] [#1 ↦ %(‖G‖+1)] [#0 ↦ q0] T2 := by
      simp [T2']; rw [ty.subst_open_chain, ty.open_subst_comm, ty.open_free (x := #0)]
      rw [occurs_subst]; simp; intro; c_free; simp!; simp; intro; c_free; simp!
      simp; simp; c_free C.2.1
    rw [HT2] at h2; simp only [instSubstTyQl, T2'] at h2; clear HT2 T2'
    -- q1
    have h3: ∀ a, qtp (G ++ [a]) ([#0 ↦ %‖G‖] q1) ([#0 ↦ %‖G‖] q1) gs := by
      intro; apply q_sub; simp; simp; c_subst; c_extend C.2.2.1
    -- q2
    let q2' := [#0 ↦ %‖G‖] [#1 ↦ %(‖G‖+1)] q2
    have h4 := fun a => @ql.self_subst_equiv (G++[_, a]) ‖G‖ .TTop q0 q2' gs
      (by simp; rfl) (by c_extend) (by simp [q2']; c_subst; c_extend C.2.2.2.1) hgs
    have HQ2: [%‖G‖ ↦ q0] q2' = [#0 ↦ %‖G‖] [#1 ↦ %(‖G‖+1)] [#0 ↦ q0] q2 := by
      simp [q2']; rw [ql.subst_chain, ql.subst_comm]
      generalize hq2': [#1↦{%(‖G‖ + 1)}] [#0↦q0] q2 = q2'; simp [subst]
      have: #0 ∉ q2' := by subst q2'; simp [subst]; intro; c_free;
      simp [this]; c_free; simp; simp; simp [subst]; c_free C.2.2.2.1
    rw [HQ2] at h4; simp only [instSubstQlId, q2'] at h4; clear HQ2 q2'
    -- final
    split_ands
    · simp! at C ⊢; split_ands
      · rw [closedty_subst]; simp [C]; assumption; simp!; simp
      · rw [closedty_subst]; simp [C]; assumption; simp!; simp
      · simp [C]
      · rw [closedql_subst]; simp [C]; c_extend; simp
      · intro h; simp [h] at C; simp [C]
      · rw [occurs_subst]; simp; intro; c_free; simp!
      · rw [occurs_subst]; simp; intro; c_free; simp!
    · apply s_all (gr2 := ∅); rotate_left 4; simp
      apply h1.2; right; simp; apply h3; simp; apply (h2 _).1; simp; apply (h4 _).1
    · apply s_all (gr2 := ∅); rotate_left 4; simp
      apply h1.1; right; simp; apply h3; simp; apply (h2 _).2; simp; apply (h4 _).2
  next T1 q1 T2 q2 => -- TProd
    -- T1
    let T1' := [#0 ↦ %‖G‖] T1
    have h1 := @ty.self_subst_equiv (G++[_]) ‖G‖ .TTop q0 gs {✦} T1' (by simp; rfl)
      hgs (by simp [sets]) (by c_extend) (by c_subst; c_extend C.1)
      (by simp [T1']; left; simp! at C; simp [C]; c_free C.1)
    have HT1: [%‖G‖ ↦ q0] T1' = [#0 ↦ %‖G‖] [#0 ↦ q0] T1 := by
      simp [T1']; rw [ty.subst_open_chain, ty.open_free]
      rw [occurs_subst]; simp; intro; c_free; simp!; c_free C.1
    rw [HT1] at h1; simp [T1'] at h1; clear HT1 T1'
    -- T1
    let T2' := [#0 ↦ %‖G‖] T2
    have h2 := @ty.self_subst_equiv (G++[_]) ‖G‖ .TTop q0 gs {✦} T2' (by simp; rfl)
      hgs (by simp [sets]) (by c_extend) (by c_subst; c_extend C.2.1)
      (by simp [T2']; left; simp! at C; simp [C]; c_free C.2.1)
    have HT2: [%‖G‖ ↦ q0] T2' = [#0 ↦ %‖G‖] [#0 ↦ q0] T2 := by
      simp [T2']; rw [ty.subst_open_chain, ty.open_free (x := #0)]
      rw [occurs_subst]; simp; intro; c_free; simp!; c_free C.2.1
    rw [HT2] at h2; simp only [instSubstTyQl, T2'] at h2; clear HT2 T2'
    -- q1
    let q1' := [#0 ↦ %‖G‖] q1
    have h3 := @ql.self_subst_equiv (G ++ [_]) ‖G‖ .TTop q0 q1' gs
      (by simp; rfl) (by c_extend) (by simp [q1']; c_subst; c_extend C.2.2.1) hgs
    have HQ1: [%‖G‖ ↦ q0] q1' = [#0 ↦ %‖G‖] [#0 ↦ q0] q1 := by
      simp [q1']; rw [ql.subst_chain]; generalize hq2': [#0↦q0] q1 = q1'
      simp [subst]; have: #0 ∉ q1' := by subst q1'; simp [subst]; intro; c_free;
      simp [this]; c_free C.2.2.1
    rw [HQ1] at h3; simp only [instSubstQlId, q1'] at h3; clear HQ1 q1'
    -- q2
    let q2' := [#0 ↦ %‖G‖] q2
    have h4 := @ql.self_subst_equiv (G ++ [_]) ‖G‖ .TTop q0 q2' gs
      (by simp; rfl) (by c_extend) (by simp [q2']; c_subst; c_extend C.2.2.2.1) hgs
    have HQ2: [%‖G‖ ↦ q0] q2' = [#0 ↦ %‖G‖] [#0 ↦ q0] q2 := by
      simp [q2']; rw [ql.subst_chain]; generalize hq2': [#0↦q0] q2 = q2'
      simp [subst]; have: #0 ∉ q2' := by subst q2'; simp [subst]; intro; c_free;
      simp [this]; c_free C.2.2.2.1
    rw [HQ2] at h4; simp only [instSubstQlId, q2'] at h4; clear HQ2 q2'
    -- final
    split_ands
    · simp! at C ⊢; split_ands
      · rw [closedty_subst]; simp [C]; assumption; simp!; simp
      · rw [closedty_subst]; simp [C]; assumption; simp!; simp
      · rw [closedql_subst]; simp [C]; c_extend; simp
      · rw [closedql_subst]; simp [C]; c_extend; simp
      · rw [occurs_subst]; simp; intro; c_free; simp!
      · rw [occurs_subst]; simp; intro; c_free; simp!
    · apply s_pair (gr1 := ∅) (gr2 := ∅); rotate_left 4; simp; simp; simp
      apply h1.1; simp; apply h2.1; simp; apply h3.1; simp; apply h4.1
    · apply s_pair (gr1 := ∅) (gr2 := ∅); rotate_left 4; simp; simp; simp
      apply h1.2; simp; apply h2.2; simp; apply h3.2; simp; apply h4.2
  next T1 => -- tlist
    -- T1
    let T1' := [#0 ↦ %‖G‖] T1
    have h1 := @ty.self_subst_equiv (G++[_]) ‖G‖ .TTop q0 gs {✦} T1' (by simp; rfl)
      hgs (by simp [sets]) (by c_extend) (by c_subst; c_extend C.1)
      (by simp [T1']; left; simp! at C; simp [C]; c_free C.1)
    have HT1: [%‖G‖ ↦ q0] T1' = [#0 ↦ %‖G‖] [#0 ↦ q0] T1 := by
      simp [T1']; rw [ty.subst_open_chain, ty.open_free]
      rw [occurs_subst]; simp; intro; c_free; simp!; c_free C.1
    rw [HT1] at h1; simp [T1'] at h1; clear HT1 T1'
    -- final
    split_ands
    · simp! at C ⊢; split_ands
      · rw [closedty_subst]; simp [C]; assumption; simp!; simp
      · rw [occurs_subst]; simp; intro; c_free; simp!
    · apply s_list (gr := ∅); swap; simp; apply h1.1
    · apply s_list (gr := ∅); swap; simp; apply h1.2

lemma check_stp_sound (TL: telescope G) (Hgs: gs ⊆ Finset.range ‖G‖):
  check_stp G q0 T1 T2 gs σ1 = .ok (gr, G') σ2 →
  closed_ql true 0 ‖G‖ q0 → closed_ty 0 ‖G‖ T1 → closed_ty 0 ‖G‖ T2 →
  closed_ql false 0 ‖G‖ gr ∧ ctx_grow G G' gs ∧ stp G' T1 q0 T2 (q0 ∪ gr) gs :=
by
  intro h Cq0 Ct1 Ct2; simp only [check_stp, excs] at h
  generalize h1: unpack_self T1 q0 = T1' at h
  apply unpack_self_equiv at h1; specialize h1 Hgs Ct1 Cq0
  apply check_stp2_sound at h; specialize h Cq0 h1.1 Ct2
  simp [h]; assumption'; rw [h.2.1.1] at h1
  apply s_trans; apply h1.1; apply h.2.1.on_stp h1.2.1; apply h.2.2
