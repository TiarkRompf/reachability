import Lean4.LangLemmas
import Aesop

attribute [-simp] Set.setOf_subset_setOf Set.subset_inter_iff Set.union_subset_iff
attribute [-simp] getElem?_pos Finset.singleton_union Finset.union_singleton

namespace Reachability

def tevaln M env e M' v :=
  ∃ nm, ∀ n, n > nm → teval n M env e = .ok (nm, M', v)

-- locations

abbrev pl := Set Nat
abbrev pnat (n: ℕ): pl := {i | i < n}
@[simp] abbrev pdom (l: List α): pl := pnat ‖l‖

@[sets]
theorem Set.subset_iff (a b: Set α):
  a ⊆ b ↔ (∀⦃x⦄, x ∈ a → x ∈ b) :=
by
  simp only [Subset, LE.le, Set.Subset]

@[simp]
lemma pnat_subset_pnat:
  pnat a ⊆ pnat b ↔ a ≤ b :=
by
  simp [sets]; apply Nat.le_of_forall_lt

abbrev stty := List ((vl → pl → Prop) × pl)
abbrev lenv := List ((stty → vl → pl → Prop) × pl)

def var_locs (E: lenv) (x: ℕ): pl :=
  match E[x]? with | some (_, vx) => vx | none => ∅

def vars_locs (E: lenv) (q: ql): pl :=
  {l | ∃ x, %x ∈ q ∧ l ∈ var_locs E x}

lemma vars_locs_monotonic:
  p ⊆ q →
  vars_locs V p ⊆ vars_locs V q :=
by
  introv H; simp [sets, vars_locs] at *; tauto

@[simp]
lemma vars_locs_or:
  vars_locs V (p ∪ q) = vars_locs V p ∪ vars_locs V q :=
by
  ext l; constructor <;> intro H <;> simp [vars_locs] at *
  · obtain ⟨x, P | Q, LV⟩ := H
    left; exists x; right; exists x
  · obtain ⟨x, P, LV⟩ | ⟨x, Q, LV⟩ := H
    exists x; tauto; exists x; tauto

@[simp]
lemma vars_locs_one (h: V[x]? = some e):
  vars_locs V {%x} = e.2 :=
by
  simp [vars_locs, var_locs, h]

@[simp]
lemma vars_locs_shrink:
  closed_ql.fvs ‖V‖ q →
  vars_locs (V ++ V') q = vars_locs V q :=
by
  intro H; ext l; simp [vars_locs, var_locs]
  congrm ∃ _, ?_; simp; intro H1; specialize H H1; simp [H]

lemma vars_locs_and:
  vars_locs V (p ∩ q) ⊆ vars_locs V p ∩ vars_locs V q :=
by
  simp [sets, vars_locs]; intros l x P Q H; split_ands
  exists x; exists x

@[simp]
lemma vars_locs_if [Decidable a]:
  vars_locs V (if a then b else c) = if a then vars_locs V b else vars_locs V c :=
by
  if h: a then simp [h] else simp [h]

@[simp]
lemma vars_locs_empty:
  vars_locs V ∅ = ∅ :=
by
  simp [vars_locs]

@[simp]
lemma vars_locs_fresh:
  vars_locs V {✦} = ∅ :=
by
  simp [vars_locs]

@[simp]
lemma vars_locs_bv:
  vars_locs V {#n} = ∅ :=
by
  simp [vars_locs]

@[simp]
lemma vars_locs_sdiff_empty (h: vars_locs V q' = ∅):
  vars_locs V (q \ q') = vars_locs V q :=
by
  simp only [Set.eq_empty_iff_forall_notMem] at h
  ext l; simp [vars_locs] at *; aesop

lemma vars_locs_change_skip:
  %x ∉ q →
  vars_locs (V.set x l) q = vars_locs V q :=
by
  intro h; ext; simp [vars_locs, var_locs]
  congrm ∃ x', ?_; simp; intro; have: x ≠ x' := (by aesop); simp [this]

lemma vars_locs_change_congr:
  V[x]? = some (vt, l) → l ⊆ l' →
  vars_locs V q ⊆ vars_locs (V.set x (vt, l')) q :=
by
  intros H1 H2; simp [vars_locs, var_locs, sets]; intros _ x1 h1 h2
  exists x1; split_ands'; by_cases h: x = x1
  · subst x1; rw [List.getElem?_set_self]; simp [H1] at *; tauto
    apply List.getElem?_eq_some' at H1; assumption
  · simpa [h]

lemma vars_locs_subst:
  x < ‖V‖ →
  closed_ql false 0 ‖V‖ q1 →
  vars_locs V [%x ↦ q1] q = vars_locs (V.set x (vt, vars_locs V q1)) q :=
by
  intro L C; simp [subst]; generalize vars_locs V q1 = q1'
  ext l; simp [vars_locs, var_locs]; constructor <;> intro H
  · obtain ⟨x1, ⟨H1, H2⟩, H3⟩ | ⟨H1, H2⟩ := H
    exists x1; split_ands'; simpa [(Ne.intro H2).symm]
    exists x; split_ands'; simpa [L]
  · obtain ⟨x1, H1, H2⟩ := H; by_cases x = x1 <;> aesop

lemma vars_locs_splice:
  vars_locs (V ++ (V1 ++ V')) (q.splice ‖V‖ ‖V1‖) = vars_locs (V ++ V') q :=
by
  ext l; simp [vars_locs, ql.splice, var_locs, id.splice]
  constructor <;> intro h
  · obtain ⟨x, ⟨a, h1a, h1b⟩, h2⟩ := h; split at h1b; swap; tauto
    rename_i x; exists x; split_ands'
    by_cases h1c: x < ‖V‖ <;> simp [h1c] at h1b <;> rw [←h1b] at h2
    · simpa [h1c] using h2
    · simp at h1c; rw [←List.append_assoc] at h2
      have h1c': ‖V ++ V1‖ ≤ x + ‖V1‖ := by simpa
      simp [h1c, -List.append_assoc] at *
      convert h2 using 3; omega
  · obtain ⟨x, h1, h2⟩ := h; exists if x < ‖V‖ then x else x + ‖V1‖; constructor
    exists %x; simp; split_ands'; split <;> rfl
    by_cases h: x < ‖V‖ <;> simp [h]
    · simpa [h] using h2
    · rw [←List.append_assoc]; simp at h
      have h': ‖V ++ V1‖ ≤ x + ‖V1‖ := by simpa
      simp [h, -List.append_assoc] at *
      convert h2 using 3; omega

-- store typing

def store_effect (S S1: stor) (p: pl) :=
  ∀ l v,
    l ∉ p → S[l]? = some v → S1[l]? = some v

lemma se_trans:
    store_effect S1 S2 p →
    store_effect S2 S3 p →
    store_effect S1 S3 p :=
by
  aesop (add simp store_effect)

lemma se_sub:
    store_effect S1 S2 p →
    p ⊆ p' →
    store_effect S1 S2 p' :=
by
  intros H1 _; simp [store_effect] at *; intros _ _ _; apply H1; tauto

lemma se_trans_sub:
  store_effect S1 S2 p' →
  store_effect S2 S3 p →
  p ⊆ p' ∪ (pdom S1)ᶜ →
  store_effect S1 S3 p' :=
by
  intros SE1 SE2 PP; simp [store_effect] at *
  intros _ _ H1 H2; specialize SE1 _ _ H1 H2; apply SE2; assumption'
  contrapose H1; apply PP at H1; simp at H1; rcases H1 with H1 | H1
  assumption; exfalso; apply List.getElem?_eq_some' at H2; omega

@[simp] abbrev st_types (M: stty) := M
@[simp] abbrev st_locs (M: stty): pl := pdom M

def store_type (S: stor) (M: stty) :=
  ‖M‖ = ‖S‖ ∧
    (∀ l,
      l ∈ st_locs M →
      ∃ vt qt v ls,
        M[l]? = some (vt, qt) ∧
          S[l]? = some v ∧
          vt v ls ∧
          ls ⊆ qt ∧
          qt ⊆ pnat l)

def store_type.byM (st: store_type S M) (h: M[l]? = some (vt, qt)):
  ∃ v ls, S[l]? = some v ∧ vt v ls ∧ ls ⊆ qt ∧ qt ⊆ pnat l :=
by
  obtain ⟨_, st⟩ := st; specialize st _ (List.getElem?_eq_some' h)
  obtain ⟨vt, qt, v, ls, h', st⟩ := st; exists v, ls
  rw [h] at h'; injections; subst_vars; split_ands''

@[simp] abbrev st_zero: stty := []

@[simp] abbrev st_extend (M1: stty) (vt: vl → pl → Prop) (qt: pl): stty :=
  M1++[(vt, qt)]

lemma storet_extend:
  store_type S M →
  ls ⊆ qt →
  vt v ls →
  qt ⊆ st_locs M →
  store_type (S++[v]) (st_extend M vt qt) :=
by
  rintro ⟨ST1, ST2⟩ LQ VT QM
  constructor; simp [ST1]; intros l H; simp at H
  if H: (l ∈ st_locs M) then
    specialize (ST2 _ H); simp at H
    simpa [H, (by omega: l < ‖S‖)] using ST2
  else
    have: l = ‖M‖ := by simp at H; omega
    subst l; simp [ST1.symm, and_assoc]; exists ls

def st_chain (M: stty) (M1: stty) q :=
  q ⊆ st_locs M ∧
  q ⊆ st_locs M1 ∧
  ∀ l, l ∈ q → M[l]? = M1[l]?

inductive locs_locs_stty: stty → pl → pl where
| lls_z: ∀M l ls,
    l ∈ ls →
    locs_locs_stty M ls l
| lls_s: ∀M l l' v ls' ls,
    l' ∈ ls →
    M[l']? = some (v, ls') →
    locs_locs_stty M ls' l →
    locs_locs_stty M ls l
open locs_locs_stty

@[simp] abbrev st_chain_deep (M: stty) (M1: stty) q := st_chain M M1 (locs_locs_stty M q)

@[simp] abbrev st_chain_full (M: stty) (M1: stty) := st_chain M M1 (st_locs M)

@[simp] abbrev pstdiff (M' M: stty) := (st_locs M') \ (st_locs M)

lemma stchain_chain:
  st_chain M1 M2 q1 →
  st_chain M2 M3 q2 →
  st_chain M1 M3 (q1 ∩ q2) :=
by
  intros; simp [st_chain] at *; split_ands''
  trans q1; simp; assumption; trans q2; simp; assumption; aesop

lemma stchain_tighten:
  st_chain M1 M2 q2 →
  q1 ⊆ q2 →
  st_chain M1 M2 q1 :=
by
  intros; simp [st_chain] at *; split_ands''; tauto; tauto; tauto

lemma stchain_symm:
  st_chain M1 M2 q1 →
  st_chain M2 M1 q1 :=
by
  intros; simp [st_chain] at *; aesop

@[simp]
lemma lls_empty:
  locs_locs_stty M ∅ = ∅ :=
by
  ext; simp; intro h; cases h <;> aesop

lemma lls_mono:
  q ⊆ q' →
  locs_locs_stty M q ⊆ locs_locs_stty M q' :=
by
  intro H; intros l H1; cases H1 with
  | lls_z => apply lls_z; tauto
  | lls_s _ l' _ ls' _ LQ ML LLS => apply H at LQ; apply lls_s; assumption'

lemma lls_or:
  locs_locs_stty M (p ∪ q) = locs_locs_stty M p ∪ locs_locs_stty M q :=
by
  ext; simp; constructor
  · intro h; cases h; rename_i h; obtain h | h := h
    left; apply lls_z; assumption; right; apply lls_z; assumption
    rename_i h _; obtain h | h := h
    left; eapply lls_s; assumption'; right; eapply lls_s; assumption'
  · rintro (h | h); apply lls_mono; assumption'; simp
    apply lls_mono; assumption'; simp

lemma lls_closed:
  store_type S M →
  locs_locs_stty M q1 ⊆ q1 ∪ st_locs M :=
by
  rintro ST; intros l LM; simp
  induction LM with
  | lls_z => tauto
  | lls_s l l' _ ls' ls _ ML LLS IH =>
    right; rcases IH with IH | IH; assumption'
    obtain ⟨-, -, -, -, -, LL⟩ := ST.byM ML
    trans l'; tauto; apply List.getElem?_eq_some'; assumption

lemma lls_closed':
  store_type S M →
  q1 ⊆ st_locs M →
  locs_locs_stty M q1 ⊆ st_locs M :=
by
  intros h1 h2; trans; apply lls_closed h1; apply Set.union_subset
  assumption; simp

lemma lls_change:
  st_chain_deep M M' q →
  locs_locs_stty M q = locs_locs_stty M' q :=
by
  intro H; obtain ⟨-, -, H⟩ := H
  ext l; constructor <;> intro H0
  · induction H0 with
    | lls_z => constructor; assumption
    | lls_s l l' _ ls' ls _ ML _ IH =>
      have: M[l']? = M'[l']? := by apply H; constructor; assumption
      apply lls_s; assumption; rw [←this]; assumption
      apply IH; intros; apply_rules [lls_s]
  · induction H0 with
    | lls_z => constructor; assumption
    | lls_s l l' _ ls' ls _ ML _ IH =>
      have: M[l']? = M'[l']? := by apply H; constructor; assumption
      apply lls_s; assumption; rw [this]; assumption
      apply IH; intros; apply_rules [lls_s]; rwa [this]

-- value interpretation

def vtnone (M: stty) (_: vl) (ls: pl): Prop := ls ⊆ st_locs M

def val_type (M:stty) (V:lenv) (v: vl) (T: ty) (ls: pl): Prop :=
  match v, T with
  | _, .TTop =>
    ls ⊆ st_locs M
  | .vnat _, .TUnit =>
    ls ⊆ st_locs M
  | .vnat _, .TNat =>
    ls ⊆ st_locs M
  | .vref l, .TRef2 T1 q1 T2 q2 =>
    closed_ty 1 ‖V‖ T1 ∧
    closed_ty 1 ‖V‖ T2 ∧
    closed_ql false 0 ‖V‖ q1 ∧
    closed_ql false 1 ‖V‖ q2 ∧
    occurs .no_covariant T1 #0 ∧
    occurs .no_contravariant T2 #0 ∧
    l ∈ ls ∧ ls ⊆ st_locs M ∧
    ∃ vt qt, M[l]? = some (vt, qt) ∧
    (∀ ⦃S' M'⦄,
      st_chain_deep M M' ls →
      store_type S' M' →
      (∀ v, ∀ lsv ⊆ vars_locs V q1,
        val_type M' (V ++ [(vtnone, ls)]) v ([#0 ↦ %‖V‖] T1) lsv →
        ∃ lsv' ⊆ qt, vt v lsv') ∧
      (∀ v, ∀ lsv ⊆ qt, vt v lsv →
        ∃ lsv' ⊆ vars_locs (V ++ [(vtnone, ls)]) [#0 ↦ %‖V‖] q2,
        val_type M' (V ++ [(vtnone, ls)]) v ([#0 ↦ %‖V‖] T2) lsv'))
  | .vabs G ty, .TFun T1 q1 T2 q2 =>
    closed_ty 1 ‖V‖ T1 ∧
    closed_ql true 1 ‖V‖ q1 ∧
    closed_ty 2 ‖V‖ T2 ∧
    closed_ql true 2 ‖V‖ q2 ∧
    (#0 ∈ q1 → ✦ ∈ q1) ∧
    occurs .no_covariant T1 #0 ∧
    occurs .no_contravariant T2 #0 ∧
    ls ⊆ st_locs M ∧
    -- vars_locs V q1 ⊆ ls ∧
    (∀ ⦃S' M' vx lsx⦄,
      st_chain_deep M M' ls →
      store_type S' M' →
      val_type M' (V ++ [(vtnone, ls)]) vx ([#0 ↦ %‖V‖] T1) lsx →
      lsx ⊆ vars_locs (V ++ [(vtnone, ls)]) [#0 ↦ %‖V‖] q1 ∪ ?[✦ ∈ q1] lsᶜ →
      ∃ S'' M'' vy lsy,
        tevaln S' (G ++ [v, vx]) ty S'' vy ∧
        st_chain_full M' M'' ∧
        store_type S'' M'' ∧
        store_effect S' S'' (ls ∪ lsx) ∧
        val_type M'' (V ++ [(vtnone, ls), (vtnone, lsx)]) vy
          ([#0 ↦ %‖V‖] [#1 ↦ %(‖V‖ + 1)] T2) lsy ∧
        lsy ⊆ vars_locs (V ++ [(vtnone, ls), (vtnone, lsx)])
          [#0 ↦ %‖V‖] [#1 ↦ %(‖V‖ + 1)] q2 ∪ ?[✦ ∈ q2] (st_locs M')ᶜ)
  | _, .TVar (%x) =>
    ls ⊆ st_locs M ∧ ∃ vt ls0, V[x]? = some (vt, ls0) ∧
    ∀ls' M', ls ⊆ ls' → st_chain_deep M M' ls → ls' ⊆ st_locs M' → vt M' v ls'
  | .vtabs G ty, .TAll T1 q1 T2 q2 =>
    closed_ty 1 ‖V‖ T1 ∧
    closed_ql true 1 ‖V‖ q1 ∧
    closed_ty 2 ‖V‖ T2 ∧
    closed_ql true 2 ‖V‖ q2 ∧
    (#0 ∈ q1 → ✦ ∈ q1) ∧
    occurs .no_covariant T1 #0 ∧
    occurs .no_contravariant T2 #0 ∧
    ls ⊆ st_locs M ∧
    (∀ ⦃S' M' vt lsx⦄,
      st_chain_deep M M' ls →
      store_type S' M' →
      (∀ ⦃S M v lsx⦄, store_type S M → vt M v lsx →
        val_type M (V ++ [(vtnone, ls)]) v ([#0 ↦ %‖V‖] T1) lsx) →
      lsx ⊆ st_locs M' →
      lsx ⊆ vars_locs (V ++ [(vtnone, ls)]) [#0 ↦ %‖V‖] q1 ∪ ?[✦ ∈ q1] lsᶜ →
      ∃ S'' M'' vy lsy,
        tevaln S' (G ++ [v, .vnat 0]) ty S'' vy ∧
        st_chain_full M' M'' ∧
        store_type S'' M'' ∧
        store_effect S' S'' (ls ∪ lsx) ∧
        val_type M'' (V ++ [(vtnone, ls), (vt, lsx)]) vy
          ([#0 ↦ %‖V‖] [#1 ↦ %(‖V‖ + 1)] T2) lsy ∧
        lsy ⊆ vars_locs (V ++ [(vtnone, ls), (vt, lsx)])
          [#0 ↦ %‖V‖] [#1 ↦ %(‖V‖ + 1)] q2 ∪ ?[✦ ∈ q2] (st_locs M')ᶜ)
  | .vpair v1 v2, .TProd T1 q1 T2 q2 =>
    closed_ty 1 ‖V‖ T1 ∧
    closed_ty 1 ‖V‖ T2 ∧
    closed_ql false 1 ‖V‖ q1 ∧
    closed_ql false 1 ‖V‖ q2 ∧
    occurs .no_contravariant T1 #0 ∧
    occurs .no_contravariant T2 #0 ∧
    ls ⊆ st_locs M ∧
    (∀ ⦃S' M'⦄,
      st_chain_deep M M' ls →
      store_type S' M' →
      ∃ ls1 ls2,
        ls1 ⊆ vars_locs (V ++ [(vtnone, ls)]) [#0 ↦ %‖V‖] q1 ∧
        val_type M' (V ++ [(vtnone, ls)]) v1 ([#0 ↦ %‖V‖] T1) ls1 ∧
        ls2 ⊆ vars_locs (V ++ [(vtnone, ls)]) [#0 ↦ %‖V‖] q2 ∧
        val_type M' (V ++ [(vtnone, ls)]) v2 ([#0 ↦ %‖V‖] T2) ls2)
  | .vlist vl, .TList T =>
    closed_ty 1 ‖V‖ T ∧
    occurs .no_contravariant T #0 ∧
    ls ⊆ st_locs M ∧
    ∀ v1 ∈ vl, ∃ ls1 ⊆ ls,
      val_type M (V ++ [(vtnone, ls)]) v1 ([#0 ↦ %‖V‖] T) ls1
  | _,_ =>
    False
termination_by ty_size T
decreasing_by all_goals simp_wf; simp! <;> omega

lemma valt_wf:
  val_type M V v T ls →
  ls ⊆ st_locs M ∧ closed_ty 0 ‖V‖ T :=
by
  intro VT; dsimp
  induction M, V, v, T, ls using val_type.induct <;> simp [val_type] at VT
  split_ands'; split_ands'; split_ands'; all_goals split_ands''
  · simp!; split_ands'; c_extend; c_free;
  · rename ∃_, _ => h; obtain ⟨_, ⟨_, h⟩, -⟩ := h
    apply List.getElem?_eq_some' at h; simp! [h]

lemma valt_store_change:
  val_type M V v T ls →
  st_chain_deep M M' ls →
  val_type M' V v T ls :=
by
  intros H1 H2
  have: ∀ M ls, ls ⊆ locs_locs_stty M ls := by
    intro M ls l H; constructor; assumption
  have M0 := M  -- trick: pre-generalize M for val_type.induct
  induction M0, V, v, T, ls using val_type.induct generalizing M M'
  all_goals simp only [val_type] at H1 ⊢
  · dsimp [st_chain] at H2; tauto
  · dsimp [st_chain] at H2; tauto
  · dsimp [st_chain] at H2; tauto
  next /-.vref-/ /-.TRef2-/ ls _ _ _ _ _ IH1 IH2 =>
    split_ands''; have := H2.2.1; clear *- this; tauto
    rename_i h; obtain ⟨vt, qt, h1, h⟩ := h; exists vt, qt; split_ands
    · have := H2.2.2; rwa [←this]; apply lls_z; assumption
    introv SC ST; apply h; assumption'; apply stchain_tighten
    apply stchain_chain; assumption'; rw [←lls_change H2]; simp
  next /-.vabs-/ /-.TFun-/ =>
    split_ands''; dsimp [st_chain] at H2; tauto
    rename_i H; intros; apply H; assumption'
    apply stchain_tighten; apply stchain_chain; assumption'
    rw [←lls_change H2]; solve_by_elim
  next /-.TVar-/ =>
    obtain ⟨H0, vt, ls0, VX, H1⟩ := H1; split_ands
    simp [st_chain] at H2; trans; apply this; swap; exact H2.2.1
    exists vt, ls0; simp [VX]; introv h1 h2 h3; apply H1; assumption'
    eapply stchain_tighten; eapply stchain_chain; assumption'
    apply Set.subset_inter; simp; rwa [lls_change]
  next /-.vtabs-/ /-.TAll-/ =>
    split_ands''; dsimp [st_chain] at H2; tauto
    rename_i H; intros; apply H; assumption'
    apply stchain_tighten; apply stchain_chain; assumption'
    rw [←lls_change H2]; simp
  next /-.vpair-/ /-.TProd-/ =>
    split_ands''; dsimp [st_chain] at H2; tauto
    rename_i H; intros; apply H; assumption'
    apply stchain_tighten; apply stchain_chain; assumption'
    rw [←lls_change H2]; simp
  next /-.vlist-/ /-.TList-/ =>
    split_ands''; dsimp [st_chain] at H2; tauto
    rename_i IH _ _ _ H; intros _ h; specialize H _ h
    obtain ⟨ls1, H1, H2⟩ := H; exists ls1; split_ands'; apply IH
    assumption; apply stchain_tighten; assumption; apply lls_mono; assumption

lemma valt_splice
  (C: closed_ty 0 ‖V ++ V'‖ T):
  val_type M (V ++ V0 ++ V') v (T.splice ‖V‖ ‖V0‖) ls ↔
    val_type M (V ++ V') v T ls :=
by
  simp; induction T using ty.induct' generalizing M V' v ls <;> simp!
  · simp only [val_type]
  · cases v <;> simp only [val_type]
  · cases v <;> simp only [val_type]
  case TRef2 IH1 IH2 =>
    cases v <;> simp only [val_type]
    simp! at C; obtain ⟨C1, C3, C2, C4, _, _, _⟩ := C
    apply closedql_bv_tighten at C2; assumption'
    congrm ?_ ∧ ?_ ∧ ?_ ∧ ?_ ∧ ?_ ∧ ?_ ∧ _ ∧ _ ∧ ?_
    · have C1' := closedty_splice C1 ‖V‖ ‖V0‖
      simp at C1 C1'; simp [C1]; convert C1' using 1; omega
    · have C3' := closedty_splice C3 ‖V‖ ‖V0‖
      simp at C3 C3'; simp [C3]; convert C3' using 1; omega
    · have C2' := closedql_splice C2 ‖V‖ ‖V0‖
      simp at C2 C2'; simp [C2]; convert C2' using 1; omega
    · have C4' := closedql_splice C4 ‖V‖ ‖V0‖
      simp at C4 C4'; simp [C4]; convert C4' using 1; omega
    simp; simp; simp [vars_locs_splice]; congrm ∃ vt qt, ?_
    simp only [and_congr_right_iff]; intro; congrm ∀ _ _ _ _, ?_ ∧ ?_
    · congr! 4; nth_rw 2 [←IH1]
      congr!; simp; split; omega; congr! 2; omega; simp; c_subst; c_extend;
    · congrm ∀ v lsv _ _, ∃ lsv', _ ⊆ ?_ ∧ ?_
      nth_rw 2 [←vars_locs_splice (V1 := V0)]; congr!; simp; split; omega
      congr! 3; omega; nth_rw 2 [←IH2]
      congr!; simp; split; omega; congr! 2; omega; simp; c_subst; c_extend;
  case TFun T1 q1 T2 q2 IH1 IH2 =>
    cases v <;> simp only [val_type]
    simp! at C; obtain ⟨C1, C3, C2, C4, _⟩ := C
    congrm ?_ ∧ ?_ ∧ ?_ ∧ ?_ ∧ ?_ ∧ ?_ ∧ ?_ ∧ _ ∧ ?_
    · have C1' := closedty_splice C1 ‖V‖ ‖V0‖
      simp at C1 C1'; simp [C1]; convert C1' using 1; omega
    · have C2' := closedql_splice C2 ‖V‖ ‖V0‖
      simp at C2 C2'; simp [C2]; convert C2' using 1; omega
    · have C3' := closedty_splice C3 ‖V‖ ‖V0‖
      simp at C3 C3'; simp [C3]; convert C3' using 1; omega
    · have C4' := closedql_splice C4 ‖V‖ ‖V0‖
      simp at C4 C4'; simp [C4]; convert C4' using 1; omega
    simp; simp; simp; congrm ∀ S' M' vx lsx _ _, ?_ → _ ⊆ ?_ → ?_
    · simp; rw [←IH1 (V' := V' ++ [(vtnone, ls)])]; simp; congr!
      split <;> simp <;> omega; simp; c_subst; c_extend;
    · simp; congr 1; conv => right; rw [←vars_locs_splice (V1 := V0)]
      simp; congr!; split <;> simp <;> omega
    congrm ∃ _ _ _ _, _ ∧ _ ∧ _ ∧ _ ∧ ?_ ∧ _ ⊆ ?_
    · simp; rw [←IH2 (V' := V' ++ [(vtnone, ls), (vtnone, lsx)])]; simp; congr!
      split <;> simp <;> omega; split <;> simp <;> omega; simp; c_subst; c_extend;
    · simp; congr 1; conv => right; rw [←vars_locs_splice (V1 := V0)]
      simp; congr!; split <;> simp <;> omega; split <;> simp <;> omega
  case TVar x =>
    cases x <;> simp [id.splice, val_type]; rename_i x
    split <;> rename_i h <;> simp [val_type] <;> intro <;> congr! 6
    simp [h]; simp [(by omega: ‖V‖ ≤ x), (by omega: ‖V‖ ≤ x + ‖V0‖)]
    rw [List.getElem?_append_right]; congr! 1; omega; omega
  case TAll T1 q1 T2 q2 IH1 IH2 =>
    cases v <;> simp only [val_type]
    simp! at C; obtain ⟨C1, C3, C2, C4, _⟩ := C
    congrm ?_ ∧ ?_ ∧ ?_ ∧ ?_ ∧ ?_ ∧ ?_ ∧ ?_ ∧ _ ∧ ?_
    · have C1' := closedty_splice C1 ‖V‖ ‖V0‖
      simp at C1 C1'; simp [C1]; convert C1' using 1; omega
    · have C2' := closedql_splice C2 ‖V‖ ‖V0‖
      simp at C2 C2'; simp [C2]; convert C2' using 1; omega
    · have C3' := closedty_splice C3 ‖V‖ ‖V0‖
      simp at C3 C3'; simp [C3]; convert C3' using 1; omega
    · have C4' := closedql_splice C4 ‖V‖ ‖V0‖
      simp at C4 C4'; simp [C4]; convert C4' using 1; omega
    simp; simp; simp; congrm ∀ S' M' vt lsx _ _, ?_ → _ → _ ⊆ ?_ → ?_
    · congrm ∀ S M v lsx, _ → _ → ?_
      simp; rw [←IH1 (V' := V' ++ [(vtnone, ls)])]; simp; congr!
      split <;> simp <;> omega; simp; c_subst; c_extend;
    · simp; congr 1; conv => right; rw [←vars_locs_splice (V1 := V0)]
      simp; congr!; split <;> simp <;> omega
    congrm ∃ _ _ _ _, _ ∧ _ ∧ _ ∧ _ ∧ ?_ ∧ _ ⊆ ?_
    · simp; rw [←IH2 (V' := V' ++ [(vtnone, ls), (vt, lsx)])]; simp; congr!
      split <;> simp <;> omega; split <;> simp <;> omega; simp; c_subst; c_extend;
    · simp; congr 1; conv => right; rw [←vars_locs_splice (V1 := V0)]
      simp; congr!; split <;> simp <;> omega; split <;> simp <;> omega
  case TProd T1 q1 T2 q2 IH1 IH2 =>
    cases v <;> simp only [val_type]
    simp! at C; obtain ⟨C1, C2, C3, C4, _⟩ := C
    congrm ?_ ∧ ?_ ∧ ?_ ∧ ?_ ∧ ?_ ∧ ?_ ∧ _ ∧ ?_
    · have C1' := closedty_splice C1 ‖V‖ ‖V0‖
      simp at C1 C1'; simp [C1]; convert C1' using 1; omega
    · have C2' := closedty_splice C2 ‖V‖ ‖V0‖
      simp at C2 C2'; simp [C2]; convert C2' using 1; omega
    · have C3' := closedql_splice C3 ‖V‖ ‖V0‖
      simp at C3 C3'; simp [C3]; convert C3' using 1; omega
    · have C4' := closedql_splice C4 ‖V‖ ‖V0‖
      simp at C4 C4'; simp [C4]; convert C4' using 1; omega
    simp; simp; congrm ∀ S' M' _ _, ∃ ls1 ls2, ?_ ∧ ?_ ∧ ?_ ∧ ?_
    · simp; conv => right; rw [←vars_locs_splice (V1 := V0)]
      simp; congr!; split <;> simp <;> omega
    · simp; rw [←IH1 (V' := V' ++ [(vtnone, ls)])]; simp; congr!
      split <;> simp <;> omega; simp; c_subst; c_extend;
    · simp; conv => right; rw [←vars_locs_splice (V1 := V0)]
      simp; congr!; split <;> simp <;> omega
    · simp; rw [←IH2 (V' := V' ++ [(vtnone, ls)])]; simp; congr!
      split <;> simp <;> omega; simp; c_subst; c_extend;
  case TList IH =>
    cases v <;> simp only [val_type]
    simp! at C; congrm ?_ ∧ ?_ ∧ _ ∧ ∀ _ _, ∃ _, _ ∧ ?_
    · have C' := closedty_splice C.1 ‖V‖ ‖V0‖
      simp at C C'; simp [C]; convert C' using 1; omega
    · simp
    · simp; rw [←IH (V' := V' ++ [(vtnone, ls)])]; simp; congr!
      split <;> simp <;> omega; simp; c_subst; c_extend C.1;

lemma valt_extend:
  closed_ty 0 ‖V‖ T →
  val_type M (V ++ V') v T ls = val_type M V v T ls :=
by
  intros C; have: V = V ++ [] := by simp
  have C': closed_ty 0 ‖V ++ []‖ T := by simpa
  conv => right; rw [this, ←valt_splice (V0 := V') C']
  simp; congr!; rw [ty.splice_self]; assumption

lemma valt_lenv_change:
  occurs .noneq T %x ∨
    occurs .no_contravariant T %x ∧ l ⊆ l' ∨
    occurs .no_covariant T %x ∧ l' ⊆ l →
  V[x]? = some (vt, l) →
  val_type M V v T ls →
  val_type M (V.set x (vt, l')) v T ls :=
by
  -- mutual_induct won't help this time: they aren't substq-aware
  intro H2 H1 H; induction T using ty.induct' generalizing M V v ls l l'
  case TTop =>
    simpa only [val_type] using H
  case TUnit =>
    cases v <;> simp only [val_type] at H ⊢; assumption
  case TNat =>
    cases v <;> simp only [val_type] at H ⊢; assumption
  case TRef2 IH1 IH2 =>
    cases v <;> simp only [val_type, List.length_set] at H ⊢
    simp! at H2; have H1' := List.getElem?_eq_some' H1
    split_ands''; rename_i H; obtain ⟨vt, qt, _, H⟩ := H
    exists vt, qt; split_ands'; introv SC ST; specialize H SC ST
    obtain ⟨h1, h2⟩ := H; split_ands
    · clear h2 IH2; introv h2 h3; apply h1; rotate_right; exact lsv
      · -- q1
        trans; assumption; obtain ⟨-, H2, -⟩ | ⟨⟨-, H2, -⟩, -⟩ | ⟨-, H2⟩ := H2
        simp [vars_locs_change_skip, H2]; simp [vars_locs_change_skip, H2]
        trans; apply vars_locs_change_congr (x := x)
        simp [H1']; exact ⟨rfl, rfl⟩; apply H2; simp [H1]
      · -- t1
        apply IH1 (l' := l) at h3; rotate_right
        simp [H1']; rfl; simpa [H1, H1'] using h3; simp
        replace H1': x ≠ ‖V‖ := (by omega); clear *- H1' H2; aesop
    · clear h1 IH1; introv h1 h3; specialize h2 _ _ h1 h3
      obtain ⟨lsv', h2, h4⟩ := h2; exists lsv'
      simp only [←List.set_append_left _ _ H1']; split_ands
      · -- q2
        obtain ⟨-, -, -, H2⟩ | ⟨-, H2⟩ | ⟨⟨-, -, H2⟩, -⟩ := H2
        · rwa [vars_locs_change_skip]; simp [subst, H2]; omega
        · trans; assumption; apply vars_locs_change_congr
          simp [H1, H1']; rfl; assumption
        · rwa [vars_locs_change_skip]; simp [subst, H2]; omega
      · -- t2
        eapply IH2; simp; rotate_left
        simp [H1', H1]; rfl; assumption; replace H1': x ≠ ‖V‖ := by omega
        simp [H1']; clear *- H2; tauto
  case TFun T1 q1 T2 q2 IH1 IH2 =>
    cases v <;> simp only [val_type, List.length_set] at H ⊢
    have H1' := List.getElem?_eq_some' H1; simp! at H2
    split_ands''; rename_i _ Cq1 _ Cq2 _ _ _ _ H; intros _ _ vx lsx CH ST VX QX
    specialize @H _ _ vx lsx CH ST _ _
    · -- VTX
      rw [←List.set_append_left] at VX; apply IH1 (l' := l) at VX; convert VX
      suffices (V ++ [(vtnone, ls)])[x]? = some (vt, l) by simp [this]
      simp [H1, H1']; simp; swap; suffices x < ‖V‖ + 1 by simp [this]; rfl
      omega; assumption'; clear *- H2 H1'; aesop
    · -- VQX
      trans; assumption; simp [subst, Cq1.hfvs]; gcongr; rcases H2 with H2 | H2 | H2
      · rw [vars_locs_change_skip]; clear *- H2; tauto
      · rw [vars_locs_change_skip]; clear *- H2; tauto
      · trans; apply vars_locs_change_congr (x := x); simp [H1']
        exact ⟨rfl, rfl⟩; exact H2.2; simp [H1]
    obtain ⟨S2, M2, vy, lsy, _⟩ := H; exists S2, M2, vy, lsy; split_ands''
    · -- VTY
      rw [←List.set_append_left]; apply IH2; simp; swap; simp [H1, H1']; rfl
      assumption'; clear *- H2 H1'; aesop (add safe (by omega))
    · -- VQY
      trans; assumption; simp [subst, Cq2.hfvs];
      gcongr; rcases H2 with H2 | H2 | H2
      · rw [vars_locs_change_skip]; clear *- H2; tauto
      · apply vars_locs_change_congr; assumption; tauto
      · rw [vars_locs_change_skip]; clear *- H2; tauto
  case TVar x =>
    cases x <;> simp only [val_type] at H ⊢; rename_i x'; simp! at H2
    obtain ⟨h1, vt0, ls0, H, h2⟩ := H; simp only [h1, true_and]
    by_cases h: x = x'; subst x'; simp [H1] at H; rcases H with ⟨rfl, rfl⟩
    exists vt, l'; split_ands'; simp [List.getElem?_eq_some' H1]; simpa [Ne.intro h, H]
  case TAll T1 q1 T2 q2 IH1 IH2 =>
    cases v <;> simp only [val_type, List.length_set] at H ⊢
    have H1' := List.getElem?_eq_some' H1; simp! at H2; split_ands''
    rename_i _ Cq1 _ Cq2 _ _ _ _ H; intros _ _ vx lsx CH ST VX VX' QX
    specialize @H _ _ vx lsx CH ST _ VX' _
    · -- VTX
      introv ST VT; specialize VX ST VT
      rw [←List.set_append_left] at VX; apply IH1 (l' := l) at VX; convert VX
      suffices (V ++ [(vtnone, ls)])[x]? = some (vt, l) by simp [this]
      simp [H1, H1']; simp; swap; suffices x < ‖V‖ + 1 by simp [this]; rfl
      omega; assumption'; clear *- H2 H1'; aesop
    · -- VQX
      trans; assumption; simp [subst, Cq1.hfvs]; gcongr; rcases H2 with H2 | H2 | H2
      · rw [vars_locs_change_skip]; clear *- H2; tauto
      · rw [vars_locs_change_skip]; clear *- H2; tauto
      · trans; apply vars_locs_change_congr (x := x); simp [H1']
        exact ⟨rfl, rfl⟩; exact H2.2; simp [H1]
    obtain ⟨S2, M2, vy, lsy, _⟩ := H; exists S2, M2, vy, lsy; split_ands''
    · -- VTY
      rw [←List.set_append_left]; apply IH2; simp; swap; simp [H1, H1']; rfl
      assumption'; clear *- H2 H1'; aesop (add safe (by omega))
    · -- VQY
      trans; assumption; simp [subst, Cq2.hfvs]
      gcongr; rcases H2 with H2 | H2 | H2
      · rw [vars_locs_change_skip]; clear *- H2; tauto
      · apply vars_locs_change_congr; assumption; tauto
      · rw [vars_locs_change_skip]; clear *- H2; tauto
  case TProd T1 q1 T2 q2 IH1 IH2 =>
    cases v <;> simp only [val_type, List.length_set] at H ⊢
    have H1' := List.getElem?_eq_some' H1; simp! at H2; split_ands''
    rename_i _ _ Cq1 Cq2 _ _ _ H; intros _ _ CH ST; specialize H CH ST
    obtain ⟨ls1, ls2, Hq1, Ht1, Hq2, Ht2⟩ := H; exists ls1, ls2; split_ands
    · -- VQ1
      trans; assumption; simp [subst, Cq1.hfvs]
      gcongr; rcases H2 with H2 | H2 | H2
      · rw [vars_locs_change_skip]; clear *- H2; tauto
      · apply vars_locs_change_congr; assumption; exact H2.2
      · rw [vars_locs_change_skip]; clear *- H2; tauto
    · -- VTX
      rw [←List.set_append_left]; apply IH1; simp; swap; simpa [H1']
      assumption'; clear *- H2 H1'; aesop
    · -- VQY
      trans; assumption; simp [subst, Cq2.hfvs]
      gcongr; rcases H2 with H2 | H2 | H2
      · rw [vars_locs_change_skip]; clear *- H2; tauto
      · apply vars_locs_change_congr; assumption; tauto
      · rw [vars_locs_change_skip]; clear *- H2; tauto
    · -- VTY
      rw [←List.set_append_left]; apply IH2; simp; swap; simpa [H1']
      assumption'; clear *- H2 H1'; aesop
  case TList T IH =>
    cases v <;> simp only [val_type, List.length_set] at H ⊢
    have H1' := List.getElem?_eq_some' H1; simp! at H2; split_ands''
    rename_i H; intro _ h; specialize H _ h; obtain ⟨ls1, h1, h2⟩ := H
    exists ls1; split_ands'
    rw [←List.set_append_left]; apply IH; simp; swap; simpa [H1']
    assumption'; clear *- H2 H1'; aesop

def valt_change_noneq {T l V M v ls} x vt l' h h1 :=
  @valt_lenv_change T x l l' V vt M v ls (.inl h) h1
def valt_change_no_contra {T l V M v ls} x vt l' h h2 h1 :=
  @valt_lenv_change T x l l' V vt M v ls (.inr (.inl ⟨h, h1⟩)) h2
def valt_change_no_covari {T l V M v ls} x vt l' h h2 h1 :=
  @valt_lenv_change T x l l' V vt M v ls (.inr (.inr ⟨h, h1⟩)) h2

lemma valt_grow:
  val_type M V v T ls →
  ls ⊆ ls' →
  ls' ⊆ st_locs M →
  val_type M V v T ls' :=
by
  intros H1 H2 H3; cases T
  case TTop =>
    simp only [val_type] at H1 ⊢; tauto
  case TUnit =>
    cases v <;> simp only [val_type] at H1 ⊢; tauto
  case TNat =>
    cases v <;> simp only [val_type] at H1 ⊢; tauto
  case TRef2 =>
    cases v <;> simp only [val_type] at H1 ⊢
    split_ands''; apply H2; assumption; rename_i H
    obtain ⟨vt, qt, _, H⟩ := H; exists vt, qt; split_ands'
    introv SC ST; specialize H _ ST
    · apply stchain_tighten; assumption; apply lls_mono; assumption
    obtain ⟨h1, h2⟩ := H; split_ands
    · introv _ h; specialize h1 v lsv (by assumption); apply h1
      apply valt_lenv_change (x:=‖V‖) (l':=ls) at h; rotate_right
      simp; exact ⟨rfl, rfl⟩; simpa using h; simp
      right; right; split_ands'; c_free;
    · introv h3 h4; specialize h2 _ _ h3 h4; obtain ⟨lsv', h5, h6⟩ := h2
      exists lsv'; split_ands
      · trans; assumption; trans;
        apply vars_locs_change_congr (x:=‖V‖) (l':=ls')
        simp; exact ⟨rfl, rfl⟩; assumption; simp
      · apply valt_lenv_change (x:=‖V‖) (l':=ls') at h6; rotate_right; simp
        exact ⟨rfl, rfl⟩; simpa using h6; simp; right; left; split_ands'; c_free;
  case TFun T1 q1 T2 q2 =>
    cases v <;> simp only [val_type] at H1 ⊢; split_ands''
    rename_i Ct1 Cq1 Ct2 Cq2 FF _ _ _ H; intros _ _ vx lsx CH ST VX QX
    specialize @H _ _ vx lsx _ ST _ _
    · apply stchain_tighten; assumption; apply lls_mono; assumption
    · apply valt_change_no_covari ‖V‖ vtnone ls at VX; simpa using VX
      simp; split_ands'; c_free; simp; rfl; assumption
    · trans; assumption; simp [subst, Cq1.hfvs, sets]; clear *- FF H2
      aesop (add safe (by tauto))
    obtain ⟨S2, M2, vy, lsy, H⟩ := H; exists S2, M2, vy, lsy; split_ands''
    · apply se_sub; assumption; gcongr
    · rename_i VY _; apply valt_change_no_contra ‖V‖ vtnone ls' at VY
      simpa using VY; simp; split_ands'; c_free; simp; rfl; assumption
    · trans; assumption; simp [subst, Cq2.hfvs]; gcongr; aesop
  case TVar x =>
    cases x <;> simp only [val_type] at H1 ⊢; split_ands''; rename_i H
    obtain ⟨vt0, ls0, _, H⟩ := H; exists vt0, ls0; split_ands'
    introv h1 h2 h3; apply H; assumption'; trans; exact H2; assumption
    apply stchain_tighten; assumption; apply lls_mono; assumption
  case TAll T1 q1 T2 q2 =>
    cases v <;> simp only [val_type] at H1 ⊢; split_ands''
    rename_i Ct1 Cq1 Ct2 Cq2 FF _ _ _ H; intros _ _ vx lsx CH ST VX VX' QX
    specialize @H _ _ vx lsx _ ST _ VX' _
    · apply stchain_tighten; assumption; apply lls_mono; assumption
    · introv ST VT; specialize VX ST VT
      apply valt_change_no_covari ‖V‖ vtnone ls at VX; simpa using VX
      simp; split_ands'; c_free; simp; rfl; assumption
    · trans; assumption; simp [subst, Cq1.hfvs, sets]; clear *- FF H2
      aesop (add safe (by tauto))
    obtain ⟨S2, M2, vy, lsy, H⟩ := H; exists S2, M2, vy, lsy; split_ands''
    · apply se_sub; assumption; gcongr
    · rename_i VY _; apply valt_change_no_contra ‖V‖ vtnone ls' at VY
      simpa using VY; simp; split_ands'; c_free; simp; rfl; assumption
    · trans; assumption; simp [subst, Cq2.hfvs]; gcongr; aesop
  case TProd T1 q1 T2 q2 =>
    cases v <;> simp only [val_type] at H1 ⊢; split_ands''
    rename_i Ct1 Ct2 Cq1 Cq2 _ _ _ H; intros _ _ CH ST; specialize H _ ST
    · apply stchain_tighten; assumption; apply lls_mono; assumption
    obtain ⟨ls1, ls2, Hq1, Ht1, Hq2, Ht2⟩ := H; exists ls1, ls2; split_ands
    · trans; assumption; simp [subst, Cq1.hfvs]; gcongr; aesop
    · apply valt_change_no_contra ‖V‖ vtnone ls' at Ht1
      simpa using Ht1; simp; split_ands'; c_free; simp; rfl; assumption
    · trans; assumption; simp [subst, Cq2.hfvs]; gcongr; aesop
    · apply valt_change_no_contra ‖V‖ vtnone ls' at Ht2
      simpa using Ht2; simp; split_ands'; c_free; simp; rfl; assumption
  case TList T =>
    cases v <;> simp only [val_type] at H1 ⊢; split_ands''
    rename_i Ct _ _ H; intro _ h; specialize H _ h; obtain ⟨ls1, _, H⟩ := H
    exists ls1; split_ands'
    · trans; assumption'
    · apply valt_change_no_contra ‖V‖ vtnone ls' at H
      simpa using H; simp; split_ands'; c_free; simp; rfl; assumption

lemma valt_subst:
  x < ‖V‖ →
  closed_ty 0 ‖V‖ t →
  closed_ql false 0 ‖V‖ q →
  store_type S M →
  (val_type M V v ([%x ↦ (t, q)] T) ls ↔
    val_type M (V.set x ((val_type · V · t ·), vars_locs V q)) v T ls) :=
by
  intros H1 H2t H2 ST; induction T using ty.induct' generalizing S M V v ls t q
  case TTop =>
    simp [val_type]
  case TUnit =>
    simp; cases v <;> simp [val_type]
  case TNat =>
    simp; cases v <;> simp [val_type]
  case TRef2 IH1 IH2 =>
    simp; cases v <;> simp only [val_type, List.length_set]
    congrm ?_ ∧ ?_ ∧ ?_ ∧ ?_ ∧ ?_ ∧ ?_ ∧ _ ∧ _ ∧ ?_
    · rw [closedty_subst]; assumption'; simpa
    · rw [closedty_subst]; assumption'; simpa
    · rwa [closedql_subst]; simpa
    · rw [closedql_subst]; c_extend; simpa
    · rw [occurs_subst]; simp; c_free; c_free;
    · rw [occurs_subst]; simp; c_free; c_free;
    congrm ∃ vt qt, _ ∧ (∀ S' M' SC ST, ?_ ∧ ?_)
    · congrm ∀ v lsv, _ ⊆ ?_ → ?_ → _
      · rw [vars_locs_subst]; assumption'
      · rw [ty.open_subst_comm]; rotate_left; simp; omega; c_free; c_free; simp
        rw [IH1]; rotate_right; assumption; simp [H1, H2.hfvs, H2t, valt_extend]
        simp; simp; omega; c_extend; c_extend;
    · congrm ∀ v lsv, _ → _ → ∃ lsv', _ ⊆ ?_ ∧ ?_
      · simp; rw [ql.subst_comm]; rotate_left; simp; omega; c_free; simp
        rw [vars_locs_subst]; simp [H2.hfvs, H1]; rfl; simp; omega; c_extend;
      · rw [ty.open_subst_comm]; rotate_left; simp; omega; c_free; c_free; simp
        rw [IH2]; rotate_right; assumption; simp [H1, H2.hfvs, H2t, valt_extend]
        simp; simp; omega; c_extend; c_extend;
  case TFun T1 q1 T2 q2 IH1 IH2 =>
    simp; cases v <;> simp only [val_type, List.length_set]
    have H2': closed_ql true 0 ‖V‖ q := by c_extend;
    congrm ?_ ∧ ?_ ∧ ?_ ∧ ?_ ∧ ?_ ∧ ?_ ∧ ?_ ∧ _ ∧ ?_
    · rw [closedty_subst]; assumption'; simpa
    · rw [closedql_subst]; c_extend; simpa
    · rw [closedty_subst]; assumption'; simpa
    · rw [closedql_subst]; c_extend; simpa
    · simp [subst, (by c_free H2: ✦ ∉ q), (by c_free: #0 ∉ q)]
    · rw [occurs_subst]; simp; c_free; c_free;
    · rw [occurs_subst]; simp; c_free; c_free;
    have Hx: x ≠ ‖V‖ := (by omega); have Hx1: x ≠ ‖V‖ + 1 := (by omega)
    have H2': ∀n, closed_ql false 0 (‖V‖ + n) q := by intros; c_extend H2
    congrm ∀ S' M' vx lsx _ ST', ?_ → _ ⊆ ?_ → ?_
    · rw [ty.open_subst_comm, IH1]; simp [H1, H2.hfvs, H2t, valt_extend]
      simp; exact S'; simp; omega; simp; c_extend; simp; c_extend H2; assumption
      simp [Hx]; c_free; c_free; simp
    · congr 1; simp [ql.subst_comm (x2 := %x), Hx, (by c_free: #0 ∉ q)]
      rw [vars_locs_subst]; simp [H2.hfvs, H1]; rfl; simp; omega; simp; apply H2'
      congr 1; simp [subst]; rintro - h; absurd h; c_free H2;
    congrm ∃ S'' M'' vy lsy, ?_; simp; intros; congrm ?_ ∧ _ ⊆ ?_
    · rw [ty.open_subst_comm, ty.open_subst_comm, IH2]; simp [H1, H2.hfvs]
      simp [H2t, valt_extend]; simp; exact S''; simp; omega; simp; c_extend;
      simp; c_extend H2; assumption; simp [Hx]; c_free; c_free; simp; simp [Hx1]
      c_free; c_free; simp
    · congr 1; simp [ql.subst_comm (x2 := %x), Hx, Hx1, (by intro; c_free: ∀n, #n ∉ q)]
      rw [vars_locs_subst]; simp [H2.hfvs, H1]; rfl; simp; omega; simp; apply H2'
      congr 1; simp [subst]; rintro - h; absurd h; c_free H2;
  case TVar x =>
    cases x <;> simp only [val_type]; simp [val_type]; simp [val_type]
    simp; split; subst x; simp [H1]; constructor
    · intro h; split_ands; apply valt_wf at h; simp [h]
      intros; apply valt_grow (ls := ls); apply valt_store_change; assumption'
    · rintro ⟨h1, h2⟩; specialize h2 ls M _ _ h1; simp
      simp [st_chain]; apply lls_closed'; assumption'
    simp only [val_type]; rename_i h; simp [h]
  case TAll T1 q1 T2 q2 IH1 IH2 =>
    simp; cases v <;> simp only [val_type, List.length_set]
    have H2': closed_ql true 0 ‖V‖ q := by c_extend;
    congrm ?_ ∧ ?_ ∧ ?_ ∧ ?_ ∧ ?_ ∧ ?_ ∧ ?_ ∧ _ ∧ ?_
    · rw [closedty_subst]; assumption'; simpa
    · rw [closedql_subst]; c_extend; simpa
    · rw [closedty_subst]; assumption'; simpa
    · rw [closedql_subst]; c_extend; simpa
    · simp [subst, (by c_free H2: ✦ ∉ q), (by c_free: #0 ∉ q)]
    · rw [occurs_subst]; simp; c_free; c_free;
    · rw [occurs_subst]; simp; c_free; c_free;
    have Hx: x ≠ ‖V‖ := (by omega); have Hx1: x ≠ ‖V‖ + 1 := (by omega)
    have H2': ∀n, closed_ql false 0 (‖V‖ + n) q := by intros; c_extend H2
    congrm ∀ S' M' vx lsx _ ST', ?_ → _ → _ ⊆ ?_ → ?_
    · congrm ∀ S' M' v lsx ST VT, ?_
      rw [ty.open_subst_comm, IH1]; simp [H1, H2.hfvs, H2t, valt_extend]
      simp; exact S'; simp; omega; simp; c_extend; simp; c_extend H2; assumption
      simp [Hx]; c_free; c_free; simp
    · congr 1; simp [ql.subst_comm (x2 := %x), Hx, (by c_free: #0 ∉ q)]
      rw [vars_locs_subst]; simp [H2.hfvs, H1]; rfl; simp; omega; simp; apply H2'
      congr 1; simp [subst]; rintro - h; absurd h; c_free H2;
    congrm ∃ S'' M'' vy lsy, ?_; simp; intros; congrm ?_ ∧ _ ⊆ ?_
    · rw [ty.open_subst_comm, ty.open_subst_comm, IH2]; simp [H1, H2.hfvs]
      simp [H2t, valt_extend]; simp; exact S''; simp; omega; simp; c_extend;
      simp; c_extend H2; assumption; simp [Hx]; c_free; c_free; simp; simp [Hx1]
      c_free; c_free; simp
    · congr 1; simp [ql.subst_comm (x2 := %x), Hx, Hx1, (by intro; c_free: ∀n, #n ∉ q)]
      rw [vars_locs_subst]; simp [H2.hfvs, H1]; rfl; simp; omega; simp; apply H2'
      congr 1; simp [subst]; rintro - h; absurd h; c_free H2;
  case TProd T1 q1 T2 q2 IH1 IH2 =>
    simp; cases v <;> simp only [val_type, List.length_set]
    congrm ?_ ∧ ?_ ∧ ?_ ∧ ?_ ∧ ?_ ∧ ?_ ∧ _ ∧ ?_
    · rw [closedty_subst]; assumption'; simpa
    · rw [closedty_subst]; assumption'; simpa
    · rw [closedql_subst]; c_extend; simpa
    · rw [closedql_subst]; c_extend; simpa
    · rw [occurs_subst]; simp; c_free; c_free;
    · rw [occurs_subst]; simp; c_free; c_free;
    have Hx: x ≠ ‖V‖ := (by omega); have Hx1: x ≠ ‖V‖ + 1 := (by omega)
    have H2': ∀n, closed_ql false 0 (‖V‖ + n) q := by intros; c_extend H2
    congrm ∀ S' M' _ ST', ∃ ls1 ls2, ?_ ∧ ?_ ∧ ?_ ∧ ?_
    · simp [ql.subst_comm (x2 := %x), Hx, (by intro; c_free: ∀n, #n ∉ q)]
      rw [vars_locs_subst]; simp [H2.hfvs, H1]; rfl; simp; omega; simp; apply H2'
    · rw [ty.open_subst_comm, IH1]; simp [H1, H2.hfvs]
      simp [H2t, valt_extend]; simp; exact S'; simp; omega; simp; c_extend;
      simp; c_extend H2; assumption; simp [Hx]; c_free; c_free; simp
    · simp [ql.subst_comm (x2 := %x), Hx, (by intro; c_free: ∀n, #n ∉ q)]
      rw [vars_locs_subst]; simp [H2.hfvs, H1]; rfl; simp; omega; simp; apply H2'
    · rw [ty.open_subst_comm, IH2]; simp [H1, H2.hfvs]
      simp [H2t, valt_extend]; simp; exact S'; simp; omega; simp; c_extend;
      simp; c_extend H2; assumption; simp [Hx]; c_free; c_free; simp
  case TList T IH =>
    simp; cases v <;> simp only [val_type, List.length_set]
    congrm ?_ ∧ ?_ ∧ _ ∧ ?_
    · rw [closedty_subst]; assumption'; simpa
    · rw [occurs_subst]; simp; c_free; c_free;
    have Hx: x ≠ ‖V‖ := (by omega); have Hx1: x ≠ ‖V‖ + 1 := (by omega)
    have H2': ∀n, closed_ql false 0 (‖V‖ + n) q := by intros; c_extend H2
    congrm ∀ v1 _, ∃ ls1, _ ∧ ?_
    · rw [ty.open_subst_comm, IH]; simp [H1, H2.hfvs]
      simp [H2t, valt_extend]; simp; exact S; simp; omega; simp; c_extend;
      simp; c_extend H2; assumption; simp [Hx]; c_free; c_free; simp

lemma valt_subst':
  V[x]? = some (vtx, lsx) →
  closed_ty 0 ‖V‖ t →
  closed_ql true 0 ‖V‖ q →
  store_type S M →
  vtx = (val_type · V · t ·) →
  occurs .noneq T %x ∨ ✦ ∉ q ∧ lsx = vars_locs V q →
  (val_type M V v ([%x ↦ (t, q)] T) ls ↔ val_type M V v T ls) :=
by
  intro VX CT CQ ST HT HQ; have := List.getElem?_eq_some' VX
  obtain HQ | ⟨h, HQ⟩ := HQ
  · rw [ty.subst_freeq HQ, valt_subst, ←HT]; simp; assumption'; swap; simp [sets]
    constructor <;> intro h
    · apply valt_change_noneq x vtx lsx at h
      simp [List.set_getElem?_self, VX] at h; assumption'
      simp [this]; rfl
    · apply valt_change_noneq; assumption'
  · subst vtx lsx; rw [valt_subst]; assumption'; congr!
    rwa [List.set_getElem?_self]; apply closedql_fr_tighten; assumption'

-- environment interpretation

@[simp]
def env_qual G V p :=
  ∀ q q',
    q ⊆ p ∪ {✦} →
    q' ⊆ p ∪ {✦} →
    (vars_trans G q) ∩ (vars_trans G q') ⊆ p ∪ {✦} →
    (vars_locs V q) ∩ (vars_locs V q') ⊆
      vars_locs V ((vars_trans G q) ∩ (vars_trans G q'))

@[simp]
def env_cell M V (p: ql) x T q (bn: binding) v (vt: stty → vl → pl → Prop) ls :=
  closed_ty 0 x T ∧
  closed_ql true 0 x q ∧
  (bn = .tvar → ∀ ⦃S M v ls⦄, store_type S M →
    vt M v ls → val_type M V v T ls) ∧
  (%x ∈ p →
    let T' := if bn = .tvar then .TTop else T
    val_type M V v T' ls) ∧
  (✦ ∉ q → ls ⊆ vars_locs V q) ∧
  (bn = .self → vars_locs V q ⊆ ls)

def env_type1 M H (G: tenv) V p :=
  ‖H‖ = ‖G‖ ∧
  ‖V‖ = ‖G‖ ∧
  closed_ql false 0 ‖H‖ p ∧
  (∀ ⦃x T q bn⦄,
      G[x]? = some (T, q, bn) →
      ∃ v vt ls,
        H[x]? = some v ∧
        V[x]? = some (vt, ls) ∧
        env_cell M V p x T q bn v vt ls)

def env_type M H G V p :=
  env_type1 M H G V p ∧
  env_qual G V p

def env_type1.v2t (et: env_type1 M H G V p) := et.1
def env_type1.t2l (et: env_type1 M H G V p) := Eq.symm et.2.1
def env_type1.v2l (et: env_type1 M H G V p) := Eq.trans et.v2t et.t2l

def env_type1.pclosed (et: env_type1 M H G V p) := by
  have et' := et; obtain ⟨-, -, et', -⟩ := et'; rwa [et.v2l] at et'

def env_type1.pclosed' (et: env_type1 M H G V p) (h: q ⊆ p): closed_ql false 0 ‖V‖ q := by
  simp [closed_ql]; trans; assumption; exact et.pclosed

def env_type1.byG {x: ℕ} (et: env_type1 M H G V p) (h: G[x]? = some (T, q, bn)) := by
  obtain ⟨-, -, -, et⟩ := et; exact et h

def env_type1.byV {x: ℕ} (et: env_type1 M H G V p) (vx: V[x]? = some (vt, ls))
  : ∃ T q bn v, G[x]? = some (T, q, bn) ∧ H[x]? = some v ∧
  env_cell M V p x T q bn v vt ls :=
by
  have gx := List.getElem?_eq_some' vx; rw [←et.t2l] at gx
  replace gx := List.getElem?_eq_getElem gx; generalize G[x] = e at gx
  obtain ⟨T, q, bn⟩ := e; have := et.byG gx; obtain ⟨v, _, ls', _, vx', _⟩ := this
  rw [vx] at vx'; injections; subst_vars; exists T, q, bn, v

section env_type_conv
variable (et: env_type M H G V p)
def env_type.v2t := et.1.v2t
def env_type.t2l := et.1.t2l
def env_type.v2l := et.1.v2l
def env_type.pclosed := et.1.pclosed
def env_type.pclosed' {q} := et.1.pclosed' (q := q)
def env_type.byG {x T q bn} := et.1.byG (x := x) (T := T) (q := q) (bn := bn)
def env_type.byV {x vt ls} := et.1.byV (x := x) (vt := vt) (ls := ls)
def env_type.sep := by replace et := et.2; simp at et; exact et
end env_type_conv

lemma env_type1_store_wf:
  env_type1 M H G V p →
  vars_locs V p ⊆ st_locs M :=
by
  introv WFE; simp [vars_locs, var_locs, sets]
  intros _ x H3 H2; split at H2; swap; cases H2; rename_i H0
  have := WFE.byV H0; dsimp at this
  obtain ⟨_, _, _, _, -, -, -, -, -, this, -⟩ := this
  obtain ⟨this, -⟩ := valt_wf (this H3)
  apply this at H2; simpa using H2

lemma env_type_store_wf (h: env_type M H G V p):
  vars_locs V p ⊆ st_locs M := env_type1_store_wf h.1

lemma env_type1_store_wf':
  env_type1 M H G V p →
  q ⊆ p →
  vars_locs V q ⊆ st_locs M :=
by
  intros WFE P; trans; swap; apply env_type1_store_wf WFE
  apply vars_locs_monotonic; assumption

lemma env_type_store_wf' (h: env_type M H G V p):
  q ⊆ p → vars_locs V q ⊆ st_locs M := env_type1_store_wf' h.1

lemma envt1_store_change:
  env_type1 M H G V p →
  st_chain_deep M M' (vars_locs V p) →
  env_type1 M' H G V p :=
by
  intros H1 H2; dsimp [env_type1] at H1 ⊢; split_ands''
  rename_i H1; introv H; obtain ⟨v, vt, ls, _, _, _, _, _, H1', _, _⟩ := H1 H; clear H1
  exists v, vt, ls; split_ands'; intros; apply valt_store_change; tauto
  apply stchain_tighten; assumption; apply lls_mono; intros _ _
  simp only [vars_locs, var_locs, Set.mem_setOf]; exists x; simp_all

lemma envt_store_change:
  env_type M H G V p →
  st_chain_deep M M' (vars_locs V p) →
  env_type M' H G V p :=
by
  intros H1 H2; dsimp [env_type] at H1 ⊢; split_ands''; apply_rules [envt1_store_change]

lemma envt1_tighten:
  env_type1 M H G V p →
  p' ⊆ p →
  env_type1 M H G V p' :=
by
  intros WFE PQ; dsimp [env_type1] at *
  obtain ⟨_, _, HP, GX⟩ := WFE; split_ands'
  · simp [closed_ql]; trans; exact PQ; assumption
  · intros _ _ _ _ gx; obtain ⟨v, vt, ls, GX⟩ := GX gx
    exists v, vt, ls; split_ands''; tauto

lemma envt_tighten:
  env_type M H G V p →
  p' ⊆ p →
  env_type M H G V p' :=
by
  intros WFE PQ; dsimp [env_type] at *
  obtain ⟨WFE1, QV⟩ := WFE; split_ands; apply_rules [envt1_tighten]
  intros; have: p' ∪ {✦} ⊆ p ∪ {✦} := by gcongr
  apply QV; tauto; tauto; tauto

lemma envt1_telescope:
  env_type1 M H G V p →
  telescope G :=
by
  intros H; dsimp [telescope]
  intros _ _ _ _ Gx; have := H.byG Gx; dsimp at this; tauto

lemma envt_telescope (h: env_type M H G V p):
  telescope G := envt1_telescope h.1
