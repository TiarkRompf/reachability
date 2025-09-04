import Lean4.LangLemmas

attribute [-simp] Set.setOf_subset_setOf Set.subset_inter_iff Set.union_subset_iff

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
lemma vars_locs_one (h: x < ‖V‖):
  vars_locs V {%x} = V[x].2 :=
by
  simp [vars_locs, var_locs, h]

@[simp]
lemma vars_locs_shrink:
  closed_ql.fvs ‖V‖ q →
  vars_locs (V ++ V') q = vars_locs V q :=
by
  intro H; ext l; simp [vars_locs, var_locs]
  congrm ∃ _, ?_; simp; intro H;
  rw [List.getElem?_append_left]; tauto

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
  simp only [Set.eq_empty_iff_forall_not_mem] at h
  ext l; simp [vars_locs] at *; specialize h l
  congrm ∃ _, ?_; simp; tauto

lemma vars_locs_change_skip:
  %x ∉ q →
  vars_locs (V.set x l) q = vars_locs V q :=
by
  intro h; ext; simp [vars_locs, var_locs]
  congrm ∃ _, ?_; simp; intro; rw [List.getElem?_set_ne]
  rintro rfl; contradiction

lemma vars_locs_change_congr:
  V[x]? = some (vt, l) → l ⊆ l' →
  vars_locs V q ⊆ vars_locs (V.set x (vt, l')) q :=
by
  intros H1 H2; simp [vars_locs, var_locs, sets]; intros _ x1 h1 h2
  exists x1; split_ands'; by_cases h: x = x1
  · subst x1; rw [List.getElem?_set_self]; simp [H1] at *; tauto
    rw [List.getElem?_eq_some] at H1; tauto
  · simpa [h]

lemma vars_locs_open:
  x < ‖V‖ →
  closed_ql false 0 ‖V‖ q1 →
  vars_locs V [%x ↦ q1] q = vars_locs (V.set x (vt, vars_locs V q1)) q :=
by
  intro L C; simp [subst]; generalize vars_locs V q1 = q1'
  ext l; simp [vars_locs, var_locs]; constructor <;> intro H
  · obtain ⟨x1, ⟨H1, H2⟩, H3⟩ | ⟨H1, H2⟩ := H
    exists x1; split_ands'; rwa [List.getElem?_set_ne]; omega
    exists x; split_ands'; simpa [L]
  · obtain ⟨x1, H1, H2⟩ := H; simp [List.getElem?_set, L] at H2
    if h: x = x1 then
      right; subst x1; simp at H2; tauto
    else
      left; exists x1; simp [h] at H2; split_ands'; omega

lemma vars_locs_splice:
  vars_locs (V ++ (V1 ++ V')) (q.splice ‖V‖ ‖V1‖) = vars_locs (V ++ V') q :=
by
  ext l; simp [vars_locs, ql.splice, var_locs, id.splice]
  constructor <;> intro h
  · obtain ⟨x, ⟨a, h1a, h1b⟩, h2⟩ := h; split at h1b; swap; tauto
    rename_i x; exists x; split_ands'
    by_cases h1c: x < ‖V‖ <;> simp [h1c] at h1b <;> rw [←h1b] at h2
    · simpa [List.getElem?_append, h1c] using h2
    · simp at h1c; rw [←List.append_assoc] at h2
      have h1c': ‖V ++ V1‖ ≤ x + ‖V1‖ := by simpa
      simp only [List.getElem?_append_right, h1c, h1c'] at *
      convert h2 using 3; simp; omega
  · obtain ⟨x, h1, h2⟩ := h; exists if x < ‖V‖ then x else x + ‖V1‖; constructor
    exists %x; simp; split_ands'; split <;> rfl
    by_cases h: x < ‖V‖ <;> simp [h]
    · simpa [List.getElem?_append, h] using h2
    · rw [←List.append_assoc]; simp at h
      have h': ‖V ++ V1‖ ≤ x + ‖V1‖ := by simpa
      simp only [List.getElem?_append_right, h, h'] at *
      convert h2 using 3; simp; omega

-- store typing

def store_effect (S S1: stor) (p: pl) :=
  ∀ l v,
    l ∉ p → S[l]? = some v → S1[l]? = some v

lemma se_trans:
    store_effect S1 S2 p →
    store_effect S2 S3 p →
    store_effect S1 S3 p :=
by
  intros; simp [store_effect] at *; tauto

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
  contrapose H1; simp at *; apply PP at H1; simp at H1; rcases H1 with H1 | H1
  assumption; exfalso; rw [List.getElem?_eq_some] at H2; obtain ⟨H2, -⟩ := H2
  omega

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
  obtain ⟨_, st⟩ := st; specialize st _ (List.getElem?_eq_some.1 h).1
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
    simpa only [List.getElem?_append_left, H, (by omega: l < ‖S‖)]
  else
    have: l = ‖M‖ := by simp at H; omega
    subst l; simp_arith only [ST1, List.length_append, List.length_singleton,
      List.getElem?_eq_getElem, List.getElem_concat_length]
    exists vt, qt, v, ls; split_ands'; simpa [ST1] using QM

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
  trans q1; simp; assumption
  trans q2; simp; assumption
  intros; simp_all

lemma stchain_tighten:
  st_chain M1 M2 q2 →
  q1 ⊆ q2 →
  st_chain M1 M2 q1 :=
by
  intros; simp [st_chain] at *; split_ands''
  tauto; tauto; tauto

lemma stchain_symm:
  st_chain M1 M2 q1 →
  st_chain M2 M1 q1 :=
by
  intros; simp [st_chain] at *
  split_ands''; intros; symm; tauto

@[simp]
lemma lls_empty:
  locs_locs_stty M ∅ = ∅ :=
by
  ext; simp; intro h; cases h
  next h => simp at h
  next h _ => simp at h

lemma lls_mono:
  q ⊆ q' →
  locs_locs_stty M q ⊆ locs_locs_stty M q' :=
by
  intro H; intros l H1; cases H1 with
  | lls_z => apply lls_z; tauto
  | lls_s _ l' _ ls' _ LQ ML LLS =>
    apply H at LQ; apply lls_s; assumption'

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
    trans l'; tauto; rw [List.getElem?_eq_some] at ML; tauto

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
  | .vbool _, .TBool =>
    ls ⊆ st_locs M
  | .vref l, .TRef T q =>
    closed_ty 0 ‖V‖ T ∧
    l ∈ ls ∧
    closed_ql false 1 ‖V‖ q ∧
    ls ⊆ st_locs M ∧
    ∃ vt qt,
      M[l]? = some (vt, qt) ∧
      qt ⊆ vars_locs (V ++ [(vtnone, ls)]) [#0 ↦ %‖V‖] q ∧
      vars_locs V q ⊆ qt ∧
      (∀ v lsv,
          lsv ⊆ qt →
          (vt v lsv ↔ val_type M V v T lsv))
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
        val_type M'' (V ++ [(vtnone, ls), (vtnone, lsx)]) vy ([#0 ↦ %‖V‖] [#1 ↦ %(‖V‖ + 1)] T2) lsy ∧
        lsy ⊆ vars_locs (V ++ [(vtnone, ls), (vtnone, lsx)]) [#0 ↦ %‖V‖] [#1 ↦ %(‖V‖ + 1)] q2 ∪ ?[✦ ∈ q2] (st_locs M')ᶜ)
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
        tevaln S' (G ++ [v, .vbool false]) ty S'' vy ∧
        st_chain_full M' M'' ∧
        store_type S'' M'' ∧
        store_effect S' S'' (ls ∪ lsx) ∧
        val_type M'' (V ++ [(vtnone, ls), (vt, lsx)]) vy ([#0 ↦ %‖V‖] [#1 ↦ %(‖V‖ + 1)] T2) lsy ∧
        lsy ⊆ vars_locs (V ++ [(vtnone, ls), (vt, lsx)]) [#0 ↦ %‖V‖] [#1 ↦ %(‖V‖ + 1)] q2 ∪ ?[✦ ∈ q2] (st_locs M')ᶜ)
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
  split_ands'; split_ands'; split_ands''; split_ands''
  split_ands''; rename ∃_, _ => h; obtain ⟨_, ⟨_, h⟩, -⟩ := h
  rw [List.getElem?_eq_some] at h; simp! [h.1]; split_ands''

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
  next _ V ls /-.vref-/ l /-.TRef-/ T q IH =>
    have H2' := H2; obtain ⟨-, _, H⟩ := H2'
    obtain ⟨_, _, _, _, H1⟩ := H1; split_ands'; tauto
    have: l ∈ locs_locs_stty M ls := by solve_by_elim
    rw [H] at H1; assumption'
    obtain ⟨vt, qt, ML, _, _, H1⟩ := H1; exists vt, qt; split_ands'
    intros _ lsv _; rw [H1]; assumption'
    have: st_chain_deep M M' lsv := by
      apply stchain_tighten; assumption
      trans; apply lls_mono; assumption
      intros _ _; apply lls_s; swap; rw [H]; assumption'
    constructor <;> intro V
    · apply IH; assumption'
    · apply IH; assumption'; apply stchain_symm
      rwa [←lls_change]; assumption
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

lemma valt_splice
  (C: closed_ty 0 ‖V ++ V'‖ T):
  val_type M (V ++ V0 ++ V') v (T.splice ‖V‖ ‖V0‖) ls ↔
    val_type M (V ++ V') v T ls :=
by
  simp; induction T using ty.induct' generalizing M V' v ls <;> simp!
  · simp only [val_type]
  · cases v <;> simp only [val_type]
  case TRef T q IH =>
    cases v <;> simp only [val_type]
    simp! at C; cases C; rename_i C1 C2
    congrm ?_ ∧ _ ∧ ?_ ∧ _ ∧ ?_
    · have C1' := closedty_splice C1 ‖V‖ ‖V0‖
      simp at C1 C1'; simp [C1]; convert C1' using 1; omega
    · have C2' := closedql_splice C2 ‖V‖ ‖V0‖
      simp at C2 C2'; simp [C2]; convert C2' using 1; omega
    simp; congrm ∃ vt qt, _ ∧ _ ⊆ ?_ ∧ ?_ ⊆ _ ∧ ∀ v lsx h, _ ↔ ?_
    · conv => right; rw [←vars_locs_splice (V1 := V0)]
      simp; congr!; split <;> simp <;> omega
    · simp [vars_locs_splice]
    · rw [IH]; simp; simpa
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
    simp; simp; simp
    congrm ∀ S' M' vx lsx _ _, ?_ → _ ⊆ ?_ → ?_
    · simp; rw [←IH1 (V' := V' ++ [(vtnone, ls)])]; simp; congr!
      split <;> simp <;> omega
      simp; apply subst_tighten; c_extend; simp [sets]
    · simp; congr; conv => right; rw [←vars_locs_splice (V1 := V0)]
      simp; congr!; split <;> simp <;> omega
    congrm ∃ _ _ _ _, _ ∧ _ ∧ _ ∧ _ ∧ ?_ ∧ _ ⊆ ?_
    · simp; rw [←IH2 (V' := V' ++ [(vtnone, ls), (vtnone, lsx)])]; simp; congr!
      split <;> simp <;> omega; split <;> simp <;> omega
      simp; repeat apply subst_tighten
      c_extend; simp [sets]; omega; simp [sets]
    · simp; congr; conv => right; rw [←vars_locs_splice (V1 := V0)]
      simp; congr!
      split <;> simp <;> omega; split <;> simp <;> omega
  case TVar x =>
    cases x <;> simp [id.splice, val_type]; rename_i x
    split <;> rename_i h <;> simp [val_type] <;> intro <;> congr! 6
    simp [List.getElem?_append_left, h]
    simp [List.getElem?_append_right, (by omega: ‖V‖ ≤ x), (by omega: ‖V‖ ≤ x + ‖V0‖)]
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
    simp; simp; simp
    congrm ∀ S' M' vt lsx _ _, ?_ → _ → _ ⊆ ?_ → ?_
    · congrm ∀ S M v lsx, _ → _ → ?_
      simp; rw [←IH1 (V' := V' ++ [(vtnone, ls)])]; simp; congr!
      split <;> simp <;> omega
      simp; apply subst_tighten; c_extend; simp [sets]
    · simp; congr; conv => right; rw [←vars_locs_splice (V1 := V0)]
      simp; congr!; split <;> simp <;> omega
    congrm ∃ _ _ _ _, _ ∧ _ ∧ _ ∧ _ ∧ ?_ ∧ _ ⊆ ?_
    · simp; rw [←IH2 (V' := V' ++ [(vtnone, ls), (vt, lsx)])]; simp; congr!
      split <;> simp <;> omega; split <;> simp <;> omega
      simp; repeat apply subst_tighten
      c_extend; simp [sets]; omega; simp [sets]
    · simp; congr; conv => right; rw [←vars_locs_splice (V1 := V0)]
      simp; congr!
      split <;> simp <;> omega; split <;> simp <;> omega

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
  case TBool =>
    cases v <;> simp only [val_type] at H ⊢; assumption
  case TRef T1 q1 IH =>
    cases v <;> simp only [val_type, List.length_set] at H ⊢
    have H1' := (List.getElem?_eq_some.1 H1).1
    replace H2: occurs .noneq T1 %x ∧ %x ∉ q1 := by
      simp! at H2; clear * - H2
      obtain h | h | h := H2 <;> simp [h] <;> apply occurs_none <;> simp [h]
    split_ands''; rename_i H
    rw [←List.set_append_left, vars_locs_change_skip, vars_locs_change_skip]
    assumption'; obtain ⟨vt, qt, H⟩ := H; exists vt, qt; split_ands''
    rename_i H; intros; rw [H]; assumption'; constructor <;> intro H
    · apply IH; simp; tauto; assumption'
    · apply IH (l' := l) at H; convert H; simp [H1]; simp; tauto
      rw [List.getElem?_set_self]; simpa
    · simp [subst]; split_ands'; omega
  case TFun T1 q1 T2 q2 IH1 IH2 =>
    cases v <;> simp only [val_type, List.length_set] at H ⊢
    have H1' := (List.getElem?_eq_some.1 H1).1
    simp! at H2
    split_ands''; rename_i _ Cq1 _ Cq2 _ _ _ _ H; intros _ _ vx lsx CH ST VX QX
    specialize @H _ _ vx lsx CH ST _ _
    · -- VTX
      rw [←List.set_append_left] at VX; apply IH1 (l' := l) at VX; convert VX
      suffices (V ++ [(vtnone, ls)])[x]? = some (vt, l) by simp [this]
      simp [H1, List.getElem?_append, H1']; simp; swap
      suffices x < ‖V‖ + 1 by simp [this]; rfl
      omega; assumption'; rcases H2 with ⟨_, -⟩ | ⟨⟨_, -⟩, _⟩ | ⟨⟨_, -⟩, _⟩
      · left; simp; split_ands'; clear * - H1'; omega
      · right; right; simp; split_ands'; clear * - H1'; omega
      · right; left; simp; split_ands'; clear * - H1'; omega
    · -- VQX
      trans; assumption; simp [subst, Cq1.hfvs]; gcongr; rcases H2 with H2 | H2 | H2
      · rw [vars_locs_change_skip]; clear *- H2; tauto
      · rw [vars_locs_change_skip]; clear *- H2; tauto
      · trans; apply vars_locs_change_congr (x := x); simp [H1']
        exact ⟨rfl, rfl⟩; exact H2.2; simp [H1]
    obtain ⟨S2, M2, vy, lsy, _⟩ := H; exists S2, M2, vy, lsy; split_ands''
    · -- VTY
      rw [←List.set_append_left]; apply IH2; simp; swap
      simp [List.getElem?_append, H1, H1']; rfl; assumption'
      rcases H2 with ⟨-, -, _, -⟩ | ⟨⟨-, -, _⟩, _⟩ | ⟨⟨-, _, -⟩, _⟩
      · left; simp; split_ands' <;> clear * - H1' <;> omega
      · right; left; simp; split_ands' <;> clear * - H1' <;> omega
      · right; right; simp; split_ands' <;> clear * - H1' <;> omega
    · -- VQY
      trans; assumption; simp [subst, List.getElem_append_right, Cq2.hfvs]
      gcongr; rcases H2 with H2 | H2 | H2
      · rw [vars_locs_change_skip]; clear *- H2; tauto
      · apply vars_locs_change_congr; assumption; tauto
      · rw [vars_locs_change_skip]; clear *- H2; tauto
  case TVar x =>
    cases x <;> simp only [val_type] at H ⊢; rename_i x'; simp! at H2
    obtain ⟨h1, vt0, ls0, H, h2⟩ := H; simp only [h1, true_and]
    by_cases h: x = x'; subst x'; simp [H1] at H; rcases H with ⟨rfl, rfl⟩
    exists vt, l'; split_ands'; rw [List.getElem?_set_self]
    rw [List.getElem?_eq_some] at H1; exact H1.1
    exists vt0, ls0; split_ands'; rwa [List.getElem?_set_ne]; simp [h]
  case TAll T1 q1 T2 q2 IH1 IH2 =>
    cases v <;> simp only [val_type, List.length_set] at H ⊢
    have H1' := (List.getElem?_eq_some.1 H1).1
    simp! at H2
    split_ands''; rename_i _ Cq1 _ Cq2 _ _ _ _ H; intros _ _ vx lsx CH ST VX VX' QX
    specialize @H _ _ vx lsx CH ST _ VX' _
    · -- VTX
      introv ST VT; specialize VX ST VT
      rw [←List.set_append_left] at VX; apply IH1 (l' := l) at VX; convert VX
      suffices (V ++ [(vtnone, ls)])[x]? = some (vt, l) by simp [this]
      simp [H1, List.getElem?_append, H1']; simp; swap
      suffices x < ‖V‖ + 1 by simp [this]; rfl
      omega; assumption'; rcases H2 with ⟨_, -⟩ | ⟨⟨_, -⟩, _⟩ | ⟨⟨_, -⟩, _⟩
      · left; simp; split_ands'; clear * - H1'; omega
      · right; right; simp; split_ands'; clear * - H1'; omega
      · right; left; simp; split_ands'; clear * - H1'; omega
    · -- VQX
      trans; assumption; simp [subst, Cq1.hfvs]; gcongr; rcases H2 with H2 | H2 | H2
      · rw [vars_locs_change_skip]; clear *- H2; tauto
      · rw [vars_locs_change_skip]; clear *- H2; tauto
      · trans; apply vars_locs_change_congr (x := x); simp [H1']
        exact ⟨rfl, rfl⟩; exact H2.2; simp [H1]
    obtain ⟨S2, M2, vy, lsy, _⟩ := H; exists S2, M2, vy, lsy; split_ands''
    · -- VTY
      rw [←List.set_append_left]; apply IH2; simp; swap
      simp [List.getElem?_append, H1, H1']; rfl; assumption'
      rcases H2 with ⟨-, -, _, -⟩ | ⟨⟨-, -, _⟩, _⟩ | ⟨⟨-, _, -⟩, _⟩
      · left; simp; split_ands' <;> clear * - H1' <;> omega
      · right; left; simp; split_ands' <;> clear * - H1' <;> omega
      · right; right; simp; split_ands' <;> clear * - H1' <;> omega
    · -- VQY
      trans; assumption; simp [subst, List.getElem_append_right, Cq2.hfvs]
      gcongr; rcases H2 with H2 | H2 | H2
      · rw [vars_locs_change_skip]; clear *- H2; tauto
      · apply vars_locs_change_congr; assumption; tauto
      · rw [vars_locs_change_skip]; clear *- H2; tauto

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
  case TBool =>
    cases v <;> simp only [val_type] at H1 ⊢; tauto
  case TRef T q =>
    cases v <;> simp only [val_type] at H1 ⊢
    split_ands''; tauto; rename_i C _ H
    obtain ⟨vt, qt, _⟩ := H; exists vt, qt; split_ands''
    rename_i H _ _; trans; assumption
    by_cases h: #0 ∈ q <;> simp [subst, h, C.hfvs]; gcongr
  case TFun T1 q1 T2 q2 =>
    cases v <;> simp only [val_type] at H1 ⊢
    split_ands''; rename_i Ct1 Cq1 Ct2 Cq2 FF _ _ _ H; intros _ _ vx lsx CH ST VX QX
    specialize @H _ _ vx lsx _ ST _ _
    · apply stchain_tighten; assumption; apply lls_mono; assumption
    · apply valt_change_no_covari ‖V‖ vtnone ls at VX; simpa using VX
      simp; split_ands'; c_free; simp; rfl; assumption
    · trans; assumption; apply Set.union_subset; simp [subst, Cq1.hfvs]
      by_cases h: #0 ∈ q1; swap; simp [h]
      specialize FF h; simp [FF, h]; intros _ _; simp; clear * -; tauto
      by_cases h: ✦ ∈ q1 <;> simp [h]; simp [sets]; clear * - H2; tauto
    obtain ⟨S2, M2, vy, lsy, H⟩ := H; exists S2, M2, vy, lsy; split_ands''
    · apply se_sub; assumption; gcongr
    · rename_i VY _; apply valt_change_no_contra ‖V‖ vtnone ls' at VY; simpa using VY
      simp; split_ands'; c_free; simp [List.getElem_append_right]; rfl; assumption
    · trans; assumption; simp [subst, List.getElem_append_right, Cq2.hfvs]
      gcongr; by_cases h: #0 ∈ q2 <;> simp [h]; assumption
  case TVar x =>
    cases x <;> simp only [val_type] at H1 ⊢; split_ands''; rename_i H
    obtain ⟨vt0, ls0, _, H⟩ := H; exists vt0, ls0; split_ands'
    introv h1 h2 h3; apply H; assumption'; trans; exact H2; assumption
    apply stchain_tighten; assumption; apply lls_mono; assumption
  case TAll T1 q1 T2 q2 =>
    cases v <;> simp only [val_type] at H1 ⊢
    split_ands''; rename_i Ct1 Cq1 Ct2 Cq2 FF _ _ _ H; intros _ _ vx lsx CH ST VX VX' QX
    specialize @H _ _ vx lsx _ ST _ VX' _
    · apply stchain_tighten; assumption; apply lls_mono; assumption
    · introv ST VT; specialize VX ST VT
      apply valt_change_no_covari ‖V‖ vtnone ls at VX; simpa using VX
      simp; split_ands'; c_free; simp; rfl; assumption
    · trans; assumption; apply Set.union_subset; simp [subst, Cq1.hfvs]
      by_cases h: #0 ∈ q1; swap; simp [h]
      specialize FF h; simp [FF, h]; intros _ _; simp; clear * -; tauto
      by_cases h: ✦ ∈ q1 <;> simp [h]; simp [sets]; clear * - H2; tauto
    obtain ⟨S2, M2, vy, lsy, H⟩ := H; exists S2, M2, vy, lsy; split_ands''
    · apply se_sub; assumption; gcongr
    · rename_i VY _; apply valt_change_no_contra ‖V‖ vtnone ls' at VY; simpa using VY
      simp; split_ands'; c_free; simp [List.getElem_append_right]; rfl; assumption
    · trans; assumption; simp [subst, List.getElem_append_right, Cq2.hfvs]
      gcongr; by_cases h: #0 ∈ q2 <;> simp [h]; assumption

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
  case TBool =>
    simp; cases v <;> simp [val_type]
  case TRef T1 q1 IH =>
    simp; cases v <;> simp only [val_type, List.length_set]
    congrm ?_ ∧ _ ∧ ?_ ∧ _ ∧ ∃ vt qt, _ ∧ qt ⊆ ?_ ∧ ?_ ⊆ qt ∧ ∀ v lsv h, _ ↔ ?_
    · rw [closedty_subst]; assumption'; simpa
    · rw [closedql_subst]; c_extend; simpa
    · simp; rw [ql.subst_comm]; rotate_left; simp; omega; c_free; simp
      rw [vars_locs_open]; simp [H1, H2.hfvs]; rfl; simp; omega; simp; c_extend;
    · rwa [vars_locs_open]; assumption
    · rw [IH]; simp; assumption'
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
    · congr 2; simp [ql.subst_comm (x2 := %x), Hx, (by c_free: #0 ∉ q)]
      rw [vars_locs_open]; simp [H2.hfvs, H1]; rfl; simp; omega; simp; apply H2'
      simp [subst]; rintro - h; absurd h; c_free H2;
    congrm ∃ S'' M'' vy lsy, ?_; simp; intros; congrm ?_ ∧ _ ⊆ ?_
    · rw [ty.open_subst_comm, ty.open_subst_comm, IH2]; simp [H1, H2.hfvs]
      simp [H2t, valt_extend]; simp; exact S''; simp; omega; simp; c_extend; simp; c_extend H2
      assumption; simp [Hx]; c_free; c_free; simp; simp [Hx1]
      c_free; c_free; simp
    · congr 2; simp [ql.subst_comm (x2 := %x), Hx, Hx1, (by intro; c_free: ∀n, #n ∉ q)]
      rw [vars_locs_open]; simp [H2.hfvs, H1]; rfl; simp; omega; simp; apply H2'
      simp [subst]; rintro - h; absurd h; c_free H2;
  case TVar x =>
    cases x <;> simp only [val_type]; simp [val_type]; simp [val_type]
    simp; split; subst x; simp [List.getElem?_set_self, H1]; constructor
    · intro h; split_ands; apply valt_wf at h; simp [h]
      intros; apply valt_grow (ls := ls); apply valt_store_change; assumption'
    · rintro ⟨h1, h2⟩; specialize h2 ls M _ _ h1; simp
      simp [st_chain]; apply lls_closed'; assumption'
    simp only [val_type]; rename_i h; simp [List.getElem?_set_ne, h]
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
    · congr 2; simp [ql.subst_comm (x2 := %x), Hx, (by c_free: #0 ∉ q)]
      rw [vars_locs_open]; simp [H2.hfvs, H1]; rfl; simp; omega; simp; apply H2'
      simp [subst]; rintro - h; absurd h; c_free H2;
    congrm ∃ S'' M'' vy lsy, ?_; simp; intros; congrm ?_ ∧ _ ⊆ ?_
    · rw [ty.open_subst_comm, ty.open_subst_comm, IH2]; simp [H1, H2.hfvs]
      simp [H2t, valt_extend]; simp; exact S''; simp; omega; simp; c_extend; simp; c_extend H2
      assumption; simp [Hx]; c_free; c_free; simp; simp [Hx1]
      c_free; c_free; simp
    · congr 2; simp [ql.subst_comm (x2 := %x), Hx, Hx1, (by intro; c_free: ∀n, #n ∉ q)]
      rw [vars_locs_open]; simp [H2.hfvs, H1]; rfl; simp; omega; simp; apply H2'
      simp [subst]; rintro - h; absurd h; c_free H2;

lemma valt_subst':
  V[x]? = some (vtx, lsx) →
  closed_ty 0 ‖V‖ t →
  closed_ql true 0 ‖V‖ q →
  store_type S M →
  vtx = (val_type · V · t ·) →
  occurs .noneq T %x ∨ ✦ ∉ q ∧ lsx = vars_locs V q →
  (val_type M V v ([%x ↦ (t, q)] T) ls ↔ val_type M V v T ls) :=
by
  intro VX CT CQ ST HT HQ; have := (List.getElem?_eq_some.1 VX).1
  obtain HQ | ⟨h, HQ⟩ := HQ
  · rw [ty.subst_free HQ, valt_subst, ←HT]; simp; assumption'; swap; simp [sets]
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
  have gx := (List.getElem?_eq_some.1 vx).1; rw [←et.t2l] at gx
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

-- semantic typing

@[simp]
def val_qual (M _: stty) H ls p q :=
  ls ⊆ vars_locs H (p ∩ q) ∪ ?[✦ ∈ q] (st_locs M)ᶜ

@[simp]
def exp_qual V (t: tm) ls :=
  match t with
  | .tvar x => vars_locs V {%x} ⊆ ls
  | _ => True

@[simp]
def exp_type S M H V t T p q :=
  ∃ S' M' v ls,
    tevaln S H t S' v ∧
    st_chain_full M M' ∧
    store_type S' M' ∧
    store_effect S S' (vars_locs V p) ∧
    val_type M' V v T ls ∧
    val_qual M M' V ls p q ∧
    exp_qual V t ls

@[simp]
def sem_type G t T p q :=
  ∀ ⦃S M E V⦄,
    env_type M E G V p →
    store_type S M  →
    exp_type S M E V t T p q

-- sub-qualifying

@[simp]
def sem_qtp G q1 q2 :=
  ∀ ⦃M E V p⦄,
    env_type1 M E G V p →
    (✦ ∈ q1 → ✦ ∈ q2) ∧
    closed_ql true 0 ‖G‖ q1 ∧
    closed_ql true 0 ‖G‖ q2 ∧
    vars_locs V q1 ⊆ vars_locs V q2

theorem sem_qtp_sub:
  q1 ⊆ q2 →
  closed_ql true 0 ‖G‖ q2 →
  sem_qtp G q1 q2 :=
by
  intros H C; simp [closed_ql]; intros; split_ands'
  apply H; trans; assumption'; apply vars_locs_monotonic; assumption

theorem sem_qtp_congr:
  sem_qtp G q1a q2a →
  sem_qtp G q1b q2b →
  sem_qtp G (q1a ∪ q1b) (q2a ∪ q2b) :=
by
  intros Ha Hb; simp [closed_ql] at *; intros _ _ _ _ WFE
  obtain ⟨Ha1, Ha2, Ha3, Ha4⟩ := Ha WFE; obtain ⟨Hb1, Hb2, Hb3, Hb4⟩ := Hb WFE
  split_ands'
  · clear * - Ha1 Hb1; tauto
  · trans (?_ ∪ ?_); gcongr; assumption'; simp
  · trans (?_ ∪ ?_); gcongr; assumption'; simp
  · gcongr

theorem sem_qtp_var:
  G[x]? = some (Tx, qx, bn) →
  ✦ ∉ qx →
  sem_qtp G {%x} qx :=
by
  intros H Qx _ _ _ _ WFE; obtain ⟨v, vt, ls, -, H1, _, _, -, -, _, _⟩ := WFE.byG H
  have := (List.getElem?_eq_some.1 H).1; simp [Qx, closed_ql] at *; split_ands'
  · trans; assumption; simp; omega
  · conv => left; simp [vars_locs, var_locs, H1]
    assumption

theorem sem_qtp_self:
  G[x]? = some (Tx, qx, .self) →
  sem_qtp G (qx \ {✦}) {%x} :=
by
  intros H _ _ _ _ WFE; obtain ⟨v, vt, ls, -, H1, _, _, -, -, _, _⟩ := WFE.byG H
  have := (List.getElem?_eq_some.1 H).1; simp [closed_ql] at *; split_ands'
  · trans qx; simp; trans; assumption; simp; omega
  · conv => right; simp [vars_locs, var_locs, H1]
    assumption

theorem sem_qtp_trans:
  sem_qtp G q1 q2 →
  sem_qtp G q2 q3 →
  sem_qtp G q1 q3 :=
by
  intros Ha Hb; simp at *; intros _ _ _ _ WFE
  obtain ⟨Ha1, Ha2, Ha3, Ha4⟩ := Ha WFE; obtain ⟨Hb1, Hb2, Hb3, Hb4⟩ := Hb WFE
  split_ands'; tauto; trans; assumption'

-- semantic typings

theorem sem_ascript:
  sem_type G t T p q →
  sem_type G (.tanno t T q) T p q :=
by
  intro h; dsimp at *; introv WFE ST; specialize h WFE ST
  obtain ⟨S', M', v, ls, h⟩ := h; exists S', M', v, ls; split_ands''
  rename tevaln _ _ _ _ _ => h; obtain ⟨n, h⟩ := h
  exists n+1; intros n' hn; cases n' <;> simp at hn
  simp! [bind]; simp [h, hn, Except.bind, pure, Except.pure]; omega

theorem sem_true:
  sem_type G .ttrue .TBool p ∅ :=
by
  dsimp; introv _ ST
  exists S, M, .vbool true, ∅; split_ands'
  · exists 1; intros n _; cases n; contradiction
    simp!; trivial
  · simp [st_chain, sets]
  · simp [store_effect]
  · simp [val_type]
  · simp

theorem sem_false:
  sem_type G .tfalse .TBool p ∅ :=
by
  dsimp; introv _ ST
  exists S, M, .vbool false, ∅; split_ands'
  · exists 1; intros n _; cases n; contradiction
    simp!; trivial
  · simp [st_chain, sets]
  · simp [store_effect]
  · simp [val_type]
  · simp

theorem sem_var:
  G[x]? = some (T, q, bn) →
  bn ≠ .tvar →
  %x ∈ p →
  sem_type G (.tvar x) T p {%x} :=
by
  introv H B P; dsimp; introv WFE ST
  obtain ⟨v, vt, ls, H, H0, H1⟩ := WFE.byG H; simp [B] at H1
  exists S, M, v, ls; split_ands'
  · simp [tevaln]; exists 1; intros n _; cases n; tauto; simp! [H]; rfl
  · simp [st_chain, sets]
  · simp [store_effect]
  · tauto
  · simp [vars_locs, var_locs]; intros _ _; exists x; simp [H0]; tauto
  · intros _; simp [vars_locs, var_locs, H0]

theorem sem_ref:
  sem_type G t T p q →
  q ⊆ p →  -- ✦ ∉ q
  sem_type G (.tref t) (.TRef T q) p {✦} :=
by
  introv H P; dsimp at *; introv WFE ST
  obtain ⟨S', M', vx, ls, HEV, MM, ST', SE, VT, VQ, _⟩ := H WFE ST; clear H
  let qt := vars_locs V q
  let vt := (val_type M' V · T ·)
  have MMs := MM; simp [st_chain] at MMs
  have Cq := WFE.pclosed' P
  exists S' ++ [vx], st_extend M' vt qt, .vref ‖S'‖, {‖S'‖}
  split_ands'
  · simp only [tevaln] at *; obtain ⟨n, HEV⟩ := HEV; exists n + 1
    intros n' _; cases n'; omega; simp! [bind]; rw [HEV]; simp!
    congr 2; omega; omega
  · simp [st_chain]; split_ands'; omega
    intros; rw [MMs.2, List.getElem?_append_left]; omega; trivial
  · apply storet_extend (ls := ls); assumption
    trans; simpa using VQ; split <;> rename_i NF
    specialize Cq NF; simp at Cq; simp; apply vars_locs_monotonic; simp [sets]
    simp [vt]; trivial; simp [qt]; trans; apply env_type_store_wf' WFE; assumption
    simp; tauto
  · apply se_trans; assumption; simp [store_effect]; intros _ _ _ H
    rwa [List.getElem?_append_left]; rw [List.getElem?_eq_some] at H; tauto
  · simp [val_type]; split_ands'
    · apply valt_wf at VT; tauto
    · simp only [store_type] at ST'; c_extend;
    · simp [store_type] at ST'; omega
    · exists vt, qt; have ST'1 := ST'.1; simp [List.getElem?_append_right, ST'1]
      split_ands'
      · simp [subst, Cq.hfvs]
      · intros _ lsv _; conv => left; simp [vt]
        have: lsv ⊆ st_locs M' := by
          trans; assumption; trans; apply env_type_store_wf' WFE P; simp; tauto
        have: locs_locs_stty M' lsv ⊆ st_locs M' := by
          apply lls_closed'; assumption; assumption
        have: st_chain_deep M' (M' ++ [(vt, qt)]) lsv := by
          simp [st_chain]; split_ands'; trans; assumption; simp
          intros _ H; rw [List.getElem?_append_left]; simp at this; tauto
        constructor <;> intro H0
        · apply valt_store_change; assumption'
        · have: st_chain_deep (M' ++ [(vt, qt)]) M' lsv := by
            apply stchain_symm; apply stchain_tighten; assumption; rwa [←lls_change]
          apply valt_store_change; assumption'
  · simp [store_type] at ST ST' ⊢; right; omega

theorem sem_get:
  sem_type env t (.TRef T q1) p q →
  q1 \ {#0} ⊆ p →
  sem_type env (.tget t) T p [#0 ↦ q] q1 :=
by
  intros H1 H2; dsimp at *; introv WFE ST
  obtain ⟨S', M', v, ls, EV, MM, ST', SE, VT, VQ, -⟩ := H1 WFE ST
  clear H1; cases v <;> simp only [val_type] at VT
  obtain ⟨_, _, Cq1, _, vt, qt, ML, QQ, _, VT⟩ := VT
  obtain ⟨v, ls, SL, VV, LQ, -⟩ := ST'.byM ML
  exists S', M', v, ls; split_ands'
  · dsimp only [tevaln] at *; obtain ⟨nm, EV⟩ := EV; exists nm + 1; intros n _
    cases n; omega; simp! only [bind]; rw [EV]; simp! only [SL]
    congr 2; omega; omega
  · rw [←VT] <;> trivial
  · trans; exact LQ; trans; exact QQ
    simp [Finset.inter_subst]; simp [subst, Cq1.hfvs]
    rw [Set.union_assoc]; gcongr
    · trans vars_locs V (q1 \ {#0}); simp [sets]; apply vars_locs_monotonic
      apply Finset.subset_inter; assumption; simp
    · by_cases h: #0 ∈ q1 <;> simp [h]
      trans; exact VQ; gcongr; by_cases h: ✦ ∈ q <;> simp [h]

theorem sem_put:
  sem_type env t1 (.TRef T q1) p q2 →
  sem_type env t2 T p (q1 \ {#0}) →
  sem_type env (.tput t1 t2) .TBool p ∅ :=
by
  intros H1 H2; dsimp at *; introv WFE ST
  obtain ⟨S', M', v1, ls1, EV1, MM', ST', SS', VT1, VQ1, -⟩ := H1 WFE ST
  have NF: ✦ ∉ q1 := by
    apply valt_wf at VT1; simp! at VT1; obtain ⟨-, -, Cq1⟩ := VT1; c_free;
  clear H1; have WFE' : env_type M' E env V p := by
    apply envt_store_change; assumption; apply stchain_tighten; assumption
    apply lls_closed'; assumption; apply env_type_store_wf WFE
  obtain ⟨S'', M'', v2, ls2, EV2, MM'', ST'', SS'', VT2, VQ2, -⟩ := H2 WFE' ST'
  clear H2; simp [NF] at VQ2; cases v1 <;> try solve | simp only [val_type] at VT1
  rename_i l; exists S''.set l v2, M'', .vbool true, ∅; split_ands'
  · dsimp [tevaln] at *; obtain ⟨nm1, EV1⟩ := EV1; obtain ⟨nm2, EV2⟩ := EV2
    exists 1 + nm1 + nm2; intros n _; rcases n with - | n; omega
    specialize EV1 n (by omega); specialize EV2 n (by omega)
    simp! [bind, EV1, EV2]; split; rfl
    rename_i H; absurd H; simp; have: l < ‖S''‖ := by
      apply lt_of_lt_of_le (b:=‖M'‖); simp only [val_type] at VT1
      simp only [sets] at VT1; tauto
      simp [st_chain, store_type] at MM'' ST''; omega
    exists S''[l]; simp [this]
  · apply stchain_tighten; apply stchain_chain; assumption'
    simp [st_chain] at MM'; simp [sets]; omega
  · simp [store_type]; split_ands; apply ST''.1; intro l0 L
    if h: l0 = l then
      subst l0; have VT1' := valt_store_change (M' := M'') VT1 ?_
      simp only [val_type] at VT1'; obtain ⟨-, -, -, -, vt, qt, ML, -, VQ1, VT1⟩ := VT1'
      exists vt, qt; split_ands'
      exists v2; split_ands; rw [List.getElem?_set_self]; simpa [←ST''.1]
      exists ls2; have: ls2 ⊆ qt := by
        trans; assumption; simp [←Finset.inter_sdiff_assoc]; trans; swap; assumption
        apply vars_locs_monotonic; simp [sets]
      split_ands'; rwa [VT1]; assumption; have := ST''.byM ML; tauto
      apply stchain_tighten; assumption; apply lls_closed'; assumption
      simp [sets]; intro _ H; simp only [val_type] at VT1; tauto
    else
      simp [store_type] at ST''; rw [List.getElem?_set_ne]; tauto; omega
  · apply se_trans_sub (p := {l}); apply se_trans; assumption'
    simp [store_effect]; intros; rwa [List.getElem?_set_ne]; omega
    have: l ∈ ls1 := by simp only [val_type] at VT1; tauto
    simp [sets, ←ST.1]; specialize VQ1 this; simp at VQ1
    rcases VQ1 with VQ1 | VQ1
    left; revert VQ1; apply vars_locs_monotonic; simp [sets]; tauto
  · simp [val_type]
  · simp

theorem envt1_extend_stub:
  env_type1 M H G V p →
  qf ⊆ p →
  st_chain_deep M M1 (vars_locs V qf) →
  x = ‖H‖ →
  env_cell M1 V {%x} x T1 q1 bn vx vt lsx →
  env_type1 M1 (H ++ [vx]) (G ++ [(T1, q1, bn)]) (V ++ [(vt, lsx)]) (qf ∪ {%x}) :=
by
  intros WFE _ _ _ EC; simp at EC; obtain ⟨_, Q1B, VT, _, _, _⟩ := EC; subst x
  have WFE': env_type1 M1 H G V qf := by
    apply envt1_store_change; apply envt1_tighten; assumption'
  obtain ⟨HG, VG, PH, GX⟩ := WFE'; split_ands; simpa; simpa; simp
  apply Finset.union_subset; trans; assumption; simp; simp; intros x _ q _ G0
  if h: x < ‖G‖ then
    simp [List.getElem?_append, h, HG, VG]
    simp only [reduceIte, List.getElem?_append, h] at G0
    specialize GX G0; dsimp at GX
    obtain ⟨v, vt, ls, HX, VX, _, XQ, VT, VP, _, _⟩ := GX
    exists vt, ls; simp_all [HX, VX]; split_ands'
    · introv h1 h2 h3; specialize VT h1 h2 h3
      rwa [valt_extend]; c_extend; omega
    · rintro (H1 | H1); specialize VP H1; rwa [valt_extend]
      apply valt_wf at VP; tauto; exfalso; omega
    · rwa [vars_locs_shrink]; intro; trans; apply XQ; simp; omega
    · rwa [vars_locs_shrink]; intro; trans; apply XQ; simp; omega
  else
    have: x = ‖G‖ := by
      rw [List.getElem?_eq_some] at G0; obtain ⟨G0, -⟩ := G0; simp at G0; omega
    subst x; simp [HG, VG] at G0 Q1B ⊢; rcases G0 with ⟨rfl, rfl, rfl⟩
    exists vt, lsx; split_ands'; rwa [←HG]
    introv h1 h2 h3; specialize VT h1 h2 h3; rwa [valt_extend]; rwa [VG, ←HG]
    rwa [valt_extend]; split; simp!; rwa [←WFE.v2l]
    rwa [vars_locs_shrink]; intro; trans; apply Q1B; simp; omega
    simpa [←WFE.t2l, Q1B.hfvs]

theorem envt_extend_full:
  env_type M H G V p →
  qf ⊆ p →
  q1 ⊆ qf ∪ {✦} →
  (vars_locs V qf) ∩ lsx ⊆ vars_locs V q1 →
  st_chain_deep M M1 (vars_locs V qf) →
  x = ‖H‖ →
  env_cell M1 V {%x} x T1 q1 bn vx vt lsx →
  env_type M1 (H ++ [vx]) (G ++ [(T1, q1, bn)]) (V ++ [(vt, lsx)]) (qf ∪ {%x}) :=
by
  intros WFE _ Q1F LB _ _ EC
  dsimp [env_type] at *; obtain ⟨WFE, QV⟩ := WFE; split_ands
  · apply envt1_extend_stub; assumption'
  subst x; simp at EC; obtain ⟨_, _, _, _, _, _⟩ := EC
  have TL := telescope_extend (T:=T1) (q:=q1) (bn := bn)
    (by rwa [←WFE.v2t]) (by rwa [←WFE.v2t]) (envt1_telescope WFE)
  intros qa qb HQa HQb H0; let qf' := qf ∪ {✦}; change q1 ⊆ qf' at Q1F
  have: qf ∪ {%‖H‖} ∪ {✦} = qf' ∪ {%‖G‖} := by
    ext; simp [sets, qf', WFE.v2t]; clear *-; tauto
  rw [this] at H0; clear this
  -- split qa qb
  have: ∀q x, q ⊆ qf ∪ {x} ∪ {✦} → q = q ∩ qf' ∪ ?[x ∈ q] {x} := by
    clear * -; intros _ _ H; ext; simp [sets, qf'] at *
    constructor <;> intro H1
    · specialize H H1; rcases H with _ | rfl | rfl <;> tauto
    · rcases H1 with _ | ⟨_, rfl⟩ <;> tauto
  apply this at HQa; apply this at HQb; clear this
  have QaF: qa ∩ qf' ⊆ qf' := by simp [sets]
  have QbF: qb ∩ qf' ⊆ qf' := by simp [sets]
  generalize qa ∩ qf' = qa' at *; generalize qb ∩ qf' = qb' at *
  -- simplify vars_locs & vars_trans
  have C: ∀ q ⊆ qf', closed_ql.fvs ‖V‖ q := by
    simp [closed_ql.fvs, qf', sets]; intro _ h _; trans; apply h; simp
    apply closed_ql.hfvs; apply WFE.pclosed' (by assumption)
  generalize hOV: vars_trans (G ++ [(T1, q1, bn)]) qa ∩ vars_trans (G ++ [(T1, q1, bn)]) qb = ov at *
  rw [HQa, HQb, WFE.v2l] at hOV ⊢; simp [C, QaF, QbF]
  simp [TL, WFE.t2l, C, Q1F, QaF, QbF] at hOV
  simp only [Set.union_inter_distrib_right, Set.inter_union_distrib_left, Set.union_assoc]
  simp only [Finset.union_inter_distrib_right, Finset.inter_union_distrib_left, Finset.union_assoc] at hOV
  subst ov; simp
  -- by congruence
  have CC: ∀ q ⊆ qf', closed_ql.fvs ‖G‖ (vars_trans G q) := by
    rw [←WFE.t2l] at C; clear * - C TL; intros; intro _ h
    apply vt_closed at h; simp at h; tauto; exact telescope_shrink TL
  replace QV: ∀ q q', q ⊆ qf' → q' ⊆ qf' →
    vars_trans G q ∩ vars_trans G q' ⊆ qf' ∪ {%‖G‖} →
    vars_locs V q ∩ vars_locs V q' ⊆ vars_locs (V ++ [(vt, lsx)]) (vars_trans G q ∩ vars_trans G q') :=
  by
    intros _ _ _ c2 h; rw [vars_locs_shrink]; apply QV
    trans; assumption; simp [qf']; gcongr
    trans; assumption; simp [qf']; gcongr
    intros _ h1; specialize h h1; simp [qf'] at h h1 ⊢
    rcases h with h | rfl | rfl
    tauto; simp; exfalso; specialize CC _ c2 h1.2; simp at CC
    rw [←WFE.t2l]; simp [closed_ql.fvs]; intros _ _ h; exact CC _ c2 h
  gcongr
  · apply QV; assumption'; trans; swap; assumption; simp [sets]
  · by_cases h: %‖V‖ ∈ qa <;> simp [h] at H0 ⊢
    trans; swap; trans; apply QV q1 qb'; assumption'
    trans; swap; assumption; simp [sets]
    intro _ h1 h2; right; left; exact ⟨.inr h1, h2⟩  -- tauto
    apply vars_locs_monotonic; simp [sets]; tauto
    simp [sets]; intros _ _ h; split_ands'; apply LB; simp; split_ands'
    revert h; trans; apply vars_locs_monotonic; assumption; simp [qf']
  · by_cases h: %‖V‖ ∈ qb <;> simp [h] at H0 ⊢
    trans; swap; trans; apply QV qa' q1; assumption'
    trans; swap; assumption; simp [sets]
    intro _ h1 h2; right; right; left; exact ⟨h1, .inr h2⟩  -- tauto
    apply vars_locs_monotonic; simp [sets]; tauto
    simp [sets]; intros _ h _; split_ands'; apply LB; simp; split_ands'
    revert h; trans; apply vars_locs_monotonic; assumption; simp [qf']
  · by_cases h: %‖V‖ ∈ qa <;> simp [h]
    by_cases h: %‖V‖ ∈ qb <;> simp [h]

theorem sem_abs:
  sem_type (env ++ [(.TTop, p ∩ qf, .self), ([#0 ↦ %‖env‖] T1, [#0 ↦ %‖env‖] q1, .var)])
    t ([#0 ↦ %‖env‖] [#1 ↦ %(‖env‖+1)] T2)
    (p ∩ qf ∪ {%‖env‖, %(‖env‖+1)})
    [#0 ↦ %‖env‖] [#1 ↦ %(‖env‖+1)] q2 →

  q1 \ {✦, #0} ⊆ p ∩ qf →
  closed_ty 1 ‖env‖ T1 →
  closed_ty 2 ‖env‖ T2 →
  closed_ql true 1 ‖env‖ q1 →
  closed_ql true 2 ‖env‖ q2 →
  closed_ql false 0 ‖env‖ qf →
  (#0 ∈ q1 → ✦ ∈ q1) →
  occurs .no_covariant T1 #0 →
  occurs .no_contravariant T2 #0 →
  sem_type env (.tabs t) (.TFun T1 q1 T2 q2) p qf :=
by
  intros H FF Ct1 Ct2 Cq1 Cq2 Cqf _ _ _ S M E V WFE ST
  rw [Finset.insert_eq, ←Finset.union_assoc] at H
  have Cqf': closed_ql false 0 ‖V‖ (p ∩ qf) := by
    simp [closed_ql]; trans qf; simp [sets]; rwa [←WFE.t2l]
  exists S, M, .vabs E t, vars_locs V (p ∩ qf); split_ands'
  · exists 1; intros n _; rcases n with - | n; omega; simp!; rfl
  · simp [st_chain]
  · simp [store_effect]
  · simp only [val_type]; rw [←WFE.t2l]; split_ands'; swap; introv MM _ _ HVQ1
    have ⟨S2, M2, vy, lsy, IHW1⟩ := @H S' M' (E ++ [.vabs E t, vx])
        (V ++ [(vtnone, vars_locs V (p ∩ qf)), (vtnone, lsx)]) ?_ (by assumption)
    clear H; exists S2, M2, vy, lsy; obtain ⟨_, _, _, _, HVT2, HVQ2, _⟩ := IHW1
    split_ands'
    · -- store_effect
      apply se_sub; assumption; simp [WFE.t2l, List.getElem_append_right]
      rw [vars_locs_shrink]; simp [sets]; exact Cqf'.hfvs
    · -- val_qual
      simp at HVQ2; trans; assumption; simp [WFE.t2l, st_locs]; gcongr
      apply vars_locs_monotonic; simp [sets]; simp [subst]
    · -- env_type extend
      have: ∀α (a: List α) (b c: α), a ++ [b, c] = a ++ [b] ++ [c] := by simp
      rw [this, this, this]; clear this
      apply envt_extend_full (M := M) (p := p ∩ qf ∪ {%‖env‖}); rotate_left
      · clear * -; tauto
      · simp [subst, sets] at FF ⊢; clear * - FF
        rintro _ (⟨h, _⟩ | ⟨_, rfl⟩); specialize FF h; tauto; simp
      · simp [Cqf'.hfvs, sets]; intros _ h1 h2; specialize HVQ1 h2
        simp at HVQ1; obtain h | ⟨-, h⟩ := HVQ1; assumption
        simp [WFE.t2l] at h1; contradiction
      · apply stchain_tighten; assumption; apply lls_mono
        simp [WFE.t2l, Cqf'.hfvs, sets]
      · simp [WFE.v2t]
      simp; split_ands'
      · apply subst_tighten; c_extend; simp
      · apply subst_tighten; c_extend; simp [sets]
      · intro h; simp [subst] at h; simpa [h] using HVQ1
      apply envt_extend_full WFE; simp; simp; simp
      simp [st_chain, MM.1]; simp [WFE.v2t]; simp; split_ands
      simp!; simp [WFE.t2l]; c_extend; simp [val_type]
      trans; swap; exact MM.1; intros _ h; exact lls_z _ _ _ h
    · -- vars_locs V qf' ⊆ st_locs M
      trans; apply vars_locs_monotonic; swap; exact p; simp [sets]
      apply env_type_store_wf WFE
  · simp

theorem sem_absa:
  sem_type env (.tabs t) (.TFun T1 q1 T2 q2) p q →
  sem_type env (.tabsa T1 q1 t) (.TFun T1 q1 T2 q2) p q :=
by
  intro h; dsimp at *; introv WFE ST; specialize h WFE ST
  obtain ⟨S', M', v, ls, h⟩ := h; exists S', M', v, ls; split_ands''
  rename tevaln _ _ _ _ _ => h; obtain ⟨nm, h⟩ := h; exists nm; intros n h1
  specialize h n h1; cases n; simp at h1; simpa [teval] using h

theorem sem_tabs:
  sem_type (env ++ [(.TTop, p ∩ qf, .self), ([#0 ↦ %‖env‖] T1, [#0 ↦ %‖env‖] q1, .tvar)])
    t ([#0 ↦ %‖env‖] [#1 ↦ %(‖env‖+1)] T2)
    (p ∩ qf ∪ {%‖env‖, %(‖env‖+1)})
    [#0 ↦ %‖env‖] [#1 ↦ %(‖env‖+1)] q2 →

  q1 \ {✦, #0} ⊆ p ∩ qf →
  closed_ty 1 ‖env‖ T1 →
  closed_ty 2 ‖env‖ T2 →
  closed_ql true 1 ‖env‖ q1 →
  closed_ql true 2 ‖env‖ q2 →
  closed_ql false 0 ‖env‖ qf →
  (#0 ∈ q1 → ✦ ∈ q1) →
  occurs .no_covariant T1 #0 →
  occurs .no_contravariant T2 #0 →
  sem_type env (.ttabs T1 q1 t) (.TAll T1 q1 T2 q2) p qf :=
by
  intros H FF Ct1 Ct2 Cq1 Cq2 Cqf _ _ _ S M E V WFE ST
  rw [Finset.insert_eq, ←Finset.union_assoc] at H
  have Cqf': closed_ql false 0 ‖V‖ (p ∩ qf) := by
    simp [closed_ql]; trans qf; simp [sets]; rwa [←WFE.t2l]
  exists S, M, .vtabs E t, vars_locs V (p ∩ qf); split_ands'
  · exists 1; intros n _; rcases n with - | n; omega; simp!; rfl
  · simp [st_chain]
  · simp [store_effect]
  · simp only [val_type]; rw [←WFE.t2l]; split_ands'; swap; introv MM _ HVT1 _ HVQ1
    have ⟨S2, M2, vy, lsy, IHW1⟩ := @H S' M' (E ++ [.vtabs E t, .vbool false])
        (V ++ [(vtnone, vars_locs V (p ∩ qf)), (vt, lsx)]) ?_ (by assumption)
    clear H; exists S2, M2, vy, lsy; obtain ⟨_, _, _, _, HVT2, HVQ2, _⟩ := IHW1
    split_ands'
    · -- store_effect
      apply se_sub; assumption; simp [WFE.t2l, List.getElem_append_right]
      rw [vars_locs_shrink]; simp [sets]; exact Cqf'.hfvs
    · -- val_qual
      simp at HVQ2; trans; assumption; simp [WFE.t2l, st_locs]; gcongr
      apply vars_locs_monotonic; simp [sets]; simp [subst]
    · -- env_type extend
      have: ∀α (a: List α) (b c: α), a ++ [b, c] = a ++ [b] ++ [c] := by simp
      rw [this, this, this]; clear this
      apply envt_extend_full (M := M) (p := p ∩ qf ∪ {%‖env‖}); rotate_left
      · clear * -; tauto
      · simp [subst, sets] at FF ⊢; clear * - FF
        rintro _ (⟨h, _⟩ | ⟨_, rfl⟩); specialize FF h; tauto; simp
      · simp [Cqf'.hfvs, sets]; intros _ h1 h2; specialize HVQ1 h2
        simp at HVQ1; obtain h | ⟨-, h⟩ := HVQ1; assumption
        simp [WFE.t2l] at h1; contradiction
      · apply stchain_tighten; assumption; apply lls_mono
        simp [WFE.t2l, Cqf'.hfvs, sets]
      · simp [WFE.v2t]
      simp; split_ands'
      · apply subst_tighten; c_extend; simp
      · apply subst_tighten; c_extend; simp [sets]
      · simpa [val_type]
      · intro h; simp [subst] at h; simpa [h] using HVQ1
      apply envt_extend_full WFE; simp; simp; simp
      simp [st_chain, MM.1]; simp [WFE.v2t]; simp; split_ands
      simp!; simp [WFE.t2l]; c_extend; simp [val_type]
      trans; swap; exact MM.1; intros _ h; exact lls_z _ _ _ h
    · -- vars_locs V qf' ⊆ st_locs M
      trans; apply vars_locs_monotonic; swap; exact p; simp [sets]
      apply env_type_store_wf WFE
  · simp

theorem overlapping
  (_ /- ST0 -/ : store_type S M)
  (_ /- ST -/ : store_type S' M')
  (WFE: env_type M H G V p)
  (_ /- CH1 -/: st_chain_full M M')
  (_ /- CH2 -/: st_chain_full M' M'')
  (HQF: val_qual M M' V lsf p qf)
  (HQX: val_qual M' M'' V lsx p qx):
  lsf ⊆ st_locs M' →
  q1 ⊆ p ∪ {✦} →
  (vars_trans G (p ∩ qf)) ∩ (vars_trans G (p ∩ qx)) ⊆ q1 →
  lsf ∩ lsx ⊆ vars_locs V q1 :=
by
  intros H1 H2 H3; have SEP := WFE.sep
  specialize SEP (p ∩ qf) (p ∩ qx) _ _ _
  simp [sets]; tauto; simp [sets]; tauto; trans; assumption'
  trans; swap; apply vars_locs_monotonic; assumption
  trans; swap; assumption; simp at HQF HQX
  simp [sets]; intros _ hl1 hl2
  specialize HQF hl1; specialize H1 hl1; specialize HQX hl2
  simp at HQF HQX H1; rcases HQX with HQX | HQX; swap; exfalso; omega
  split_ands'; apply env_type_store_wf' WFE at HQX; swap; simp [sets]
  simp at HQX; rcases HQF with HQF | HQF; trivial; exfalso; omega

theorem sem_app:
  sem_type env f (.TFun T1 q1 T2 q2) p qf →
  sem_type env t ([#0 ↦ p ∩ qf] T1) p qx →
  (if #0 ∈ q1 then
      True -- → ✦ ∈ q1
    else if ✦ ∈ q1 then
      sem_qtp env qx (q1 ∪ qx') ∧
      qx' ⊆ p ∧
      (vars_trans env qf) ∩ (vars_trans env qx') ⊆ {✦}
    else
      sem_qtp env qx q1) →

  q2 \ {✦, #0, #1} ⊆ p →
  (✦ ∈ qf → occurs .noneq T1 #0 ∧ occurs .noneq T2 #0) →
  (✦ ∈ qx → occurs .noneq T2 #1) →
  sem_type env (.tapp f t) ([#0 ↦ p ∩ qf] [#1 ↦ p ∩ qx] T2) p
    [#0 ↦ qf] [#1 ↦ qx] q2 :=
by
  intros TF TX SEP Cq2 FFr XFr; dsimp [-sem_qtp] at *; intros S M E V WFE ST
  obtain ⟨S1, M1, vf, lsf, EV1, MM1, ST1, _, VTF, VQF, EQF⟩ := TF WFE ST; clear TF
  have WFE1 := envt_store_change (M' := M1) WFE ?_; swap
  · apply stchain_tighten; assumption; apply lls_closed' ST
    apply env_type_store_wf WFE
  -- extend lsf & lsx
  let lsf' := if ✦ ∈ qf then lsf else vars_locs V (p ∩ qf)
  replace VTF := valt_grow (ls' := lsf') VTF ?_ ?_; rotate_left
  · simp [lsf']; split; simp; rename_i h; simpa [h] using VQF
  · simp [lsf']; split; exact (valt_wf VTF).1; apply env_type_store_wf' WFE1; simp
  replace VQF: lsf' ⊆ ?_ := by
    simp [lsf']; split; exact VQF; simp [sets]
  obtain ⟨S2, M2, vx, lsx, EV2, MM2, _, _, VTX, VQX, -⟩ := TX WFE1 ST1; clear TX
  let lsx' := if ✦ ∈ qx then lsx else vars_locs V (p ∩ qx)
  replace VTX := valt_grow (ls' := lsx') VTX ?_ ?_; rotate_left
  · simp [lsx']; split; simp; rename_i h; simpa [h] using VQX
  · simp [lsx']; split; exact (valt_wf VTX).1; trans
    apply env_type_store_wf' WFE1; simp; simp [st_chain] at MM2 ⊢; exact MM2.1
  replace VQX: lsx' ⊆ ?_ := by
    simp [lsx']; split; exact VQX; simp [sets]
  -- shape VTX for application
  replace VTX: val_type M2 (V ++ [(vtnone, lsf')]) vx ([#0↦%‖V‖]T1) lsx' := by
    have Cqf := WFE.pclosed' (by simp: p ∩ qf ⊆ p); have := (valt_wf VTX).2
    have Ct1 := by
      apply closedty_extend (mb' := 1) (mf' := ‖V‖) this (by simp) (by simp)
    rw [closedty_subst] at Ct1; rotate_left; assumption; simp!; simp
    rwa [←valt_extend (V' := [(vtnone, lsf')]), ←ty.subst_open_chain #0 %‖V‖, valt_subst'] at VTX
    simp; exact ⟨rfl, rfl⟩; simp!; c_extend; assumption; simp [val_type]; rfl
    simp [Cqf.hfvs]; by_cases h: ✦ ∈ qf; left; split_ands; c_free;
    simp [FFr h]; right; simp [h, lsf']; c_free; assumption
  -- time for application
  cases vf <;> simp only [val_type] at VTF
  obtain ⟨_, _, Ct2, _, _, _, _, FM1, VTF⟩ := VTF
  specialize VTF (S' := S2) _ _ VTX _
  apply stchain_tighten; assumption; apply lls_closed' ST1; assumption; assumption
  · -- argument qualifier
    clear VTF; have: closed_ql.fvs ‖V‖ q1 := by
      apply closed_ql.hfvs; assumption
    if fn1: #0 ∈ q1 then
      have fr1: ✦ ∈ q1 := by tauto
      simp [sets, fn1, fr1, subst]; clear * -; tauto
    else
      if fr1: ✦ ∈ q1 then
        simp [fn1, fr1, subst, this, -Finset.subset_singleton_iff] at SEP ⊢
        obtain ⟨EX, XP, SEP⟩ := SEP; obtain ⟨-, -, EX⟩ := EX WFE1.1
        replace SEP: vars_trans env (p ∩ qf) ∩ vars_trans env (p ∩ qx') ⊆ {✦} := by
          trans; swap; exact SEP; gcongr
          apply vt_mono; simp [sets]; apply vt_mono; simp [sets]
        apply overlapping (lsx := vars_locs V qx') ST ST1 at SEP; assumption'
        · simp at SEP; trans; assumption; trans (?_ ∪ ?_); gcongr
          trans; swap; exact EX; apply vars_locs_monotonic; simp [sets]
          intro _ h; exact h; rw [Set.union_assoc]; gcongr
          simp [Set.eq_empty_iff_forall_not_mem] at SEP
          simp [sets] at FM1 ⊢; rintro l (H1 | _) H; clear *- H1 H SEP; tauto
          specialize FM1 H; omega
        · suffices ✦ ∉ qx' by
            simp [this]; apply vars_locs_monotonic; simp [sets] at *; clear * - XP; tauto
          intro h; have := WFE.pclosed' XP h; simp at this
        · simp
      else
        simp [fn1, fr1, subst, this] at SEP ⊢
        specialize SEP WFE.1; simp [SEP.1] at VQX; obtain ⟨-, -, -, SEP⟩ := SEP
        trans; assumption; trans; swap; assumption; apply vars_locs_monotonic; simp [sets]
  obtain ⟨S3, M3, vy, lsy, EV3, MM3, _, _, VTY, VQY⟩ := VTF
  exists S3, M3, vy, lsy; split_ands'
  · simp [tevaln] at EV1 EV2 EV3 ⊢
    obtain ⟨nm1, EV1⟩ := EV1; obtain ⟨nm2, EV2⟩ := EV2; obtain ⟨nm3, EV3⟩ := EV3
    exists 1 + nm1 + nm2 + nm3; intro n _; rcases n with - | n; omega
    simp! [bind]; rw [EV1]; simp!; rw [EV2]; simp!; rw [EV3]; simp!; rfl
    omega; omega; omega
  · apply stchain_tighten; apply stchain_chain; assumption
    apply stchain_chain; assumption'
    simp [sets]; simp [st_chain] at MM1 MM2 MM3; omega
  · apply se_trans_sub; swap; assumption; apply se_trans; assumption'
    simp [sets, ←ST.1]; rintro _ (H | H)
    · specialize VQF H; simp at VQF; rcases VQF with VQF | _; swap; tauto
      left; revert VQF; apply vars_locs_monotonic; simp [sets]
    · specialize VQX H; simp at VQX; rcases VQX with VQX | _
      left; revert VQX; apply vars_locs_monotonic; simp [sets]
      right; simp [st_chain, sets] at MM1 ⊢; omega
  · -- result type
    have Cqf := WFE.pclosed' (by simp: p ∩ qf ⊆ p)
    have Cqx := WFE.pclosed' (by simp: p ∩ qx ⊆ p)
    have Cp := WFE.pclosed
    rw [←valt_extend (V' := [(vtnone, lsf'), (vtnone, lsx')]),
      ←ty.subst_open_chain #0 %‖V‖,
      ←ty.subst_open_chain #1 %(‖V‖ + 1),
      ty.open_subst_comm]; rotate_left
    simp; c_free; simp!; simp; c_free;
    rw [occurs_subst]; simp; c_free; c_free; simp!
    repeat apply subst_tighten
    assumption; split_ands; simp!; c_extend; intro h; absurd h; c_free;
    split_ands; simp!; c_extend; intro h; absurd h; c_free;
    rw [valt_subst']; rotate_left
    simp [List.getElem_append_right]; exact ⟨rfl, rfl⟩; simp!; c_extend; assumption
    simp [val_type]; rfl; simp [Cqf.hfvs]; rw [occurs_subst]; simp
    by_cases h: ✦ ∈ qf; left; split_ands; c_free;
    simp [FFr h]; right; simp [h, lsf']; c_free; simp; simp!
    rwa [valt_subst']
    simp [List.getElem_append_right]; exact ⟨rfl, rfl⟩; simp!; c_extend; assumption
    simp [val_type]; rfl; simp [Cqx.hfvs]
    by_cases h: ✦ ∈ qx; left; split_ands; c_free;
    simp [XFr h]; right; simp [h, lsx']
  · -- result qualifier
    trans; assumption; clear VQY
    have: closed_ql.fvs ‖V‖ q2 := by apply closed_ql.hfvs; assumption
    simp [Finset.inter_subst]; simp [subst, List.getElem_append_right]
    simp [this, sets, or_assoc]; clear this
    intros l VQY; simp [st_chain] at MM1 MM2
    rcases VQY with VQY | VQY | VQY | VQY
    · left; have: q2 \ {✦, #0, #1} ⊆ p ∩ q2 := by
        apply Finset.subset_inter; assumption; simp
      apply vars_locs_monotonic; assumption'; simpa [Finset.insert_eq]
    · clear * - VQY VQX MM1; rcases VQY with ⟨hx, VQY⟩; simp [hx]
      specialize VQX VQY; simp at VQX; rcases VQX with _ | ⟨hfr, _⟩; tauto
      simp [hfr]; right; right; right; omega
    · clear * - VQY VQF; rcases VQY with ⟨h, VQY⟩; simp [h]; specialize VQF VQY
      simp at VQF; right; right; tauto
    · simp [VQY.1]; right; right; right; omega

theorem sem_app_classic:
  sem_type env f (.TFun T1 q1 T2 q2) p qf →
  sem_type env t T1 p qx →
  #0 ∈ q1 ∨ sem_qtp env qx q1 ∨ ✦ ∈ q1 ∧
    sem_qtp env ((vars_trans env qf) ∩ (vars_trans env qx)) q1 ∧
    (vars_trans env qf ∩ vars_trans env qx) \ {✦} ⊆ p →

  q2 \ {✦, #0, #1} ⊆ p →
  (✦ ∈ qf → occurs .noneq T2 #0) →
  (✦ ∈ qx → occurs .noneq T2 #1) →
  sem_type env (.tapp f t) ([#0 ↦ p ∩ qf] [#1 ↦ p ∩ qx] T2) p
    [#0 ↦ qf] [#1 ↦ qx] q2 :=
by
  intros TF TX SEP Cq2 FFr XFr; dsimp [-sem_qtp] at *; intros S M E V WFE ST
  obtain ⟨S1, M1, vf, lsf, EV1, MM1, ST1, _, VTF, VQF, EQF⟩ := TF WFE ST; clear TF
  have WFE1 := envt_store_change (M' := M1) WFE ?_; swap
  · apply stchain_tighten; assumption; apply lls_closed' ST
    apply env_type_store_wf WFE
  -- extend lsf & lsx
  let lsf' := if ✦ ∈ qf then lsf else vars_locs V (p ∩ qf)
  replace VTF := valt_grow (ls' := lsf') VTF ?_ ?_; rotate_left
  · simp [lsf']; split; simp; rename_i h; simpa [h] using VQF
  · simp [lsf']; split; exact (valt_wf VTF).1; apply env_type_store_wf' WFE1; simp
  replace VQF: lsf' ⊆ ?_ := by
    simp [lsf']; split; exact VQF; simp [sets]
  obtain ⟨S2, M2, vx, lsx, EV2, MM2, _, _, VTX, VQX, -⟩ := TX WFE1 ST1; clear TX
  let lsx' := if ✦ ∈ qx then lsx else vars_locs V (p ∩ qx)
  replace VTX := valt_grow (ls' := lsx') VTX ?_ ?_; rotate_left
  · simp [lsx']; split; simp; rename_i h; simpa [h] using VQX
  · simp [lsx']; split; exact (valt_wf VTX).1; trans
    apply env_type_store_wf' WFE1; simp; simp [st_chain] at MM2 ⊢; exact MM2.1
  replace VQX: lsx' ⊆ ?_ := by
    simp [lsx']; split; exact VQX; simp [sets]
  -- shape VTX for application
  replace VTX: val_type M2 (V ++ [(vtnone, lsf')]) vx ([#0↦%‖V‖]T1) lsx' := by
    have Cqf := WFE.pclosed' (by simp: p ∩ qf ⊆ p); have := (valt_wf VTX).2
    rwa [ty.open_free, valt_extend]; assumption; c_free;
  -- time for application
  cases vf <;> simp only [val_type] at VTF
  obtain ⟨_, _, Ct2, _, _, _, _, FM1, VTF⟩ := VTF
  specialize VTF (S' := S2) _ _ VTX _
  apply stchain_tighten; assumption; apply lls_closed' ST1; assumption; assumption
  · -- argument qualifier
    clear VTF; have: closed_ql.fvs ‖V‖ q1 := by
      apply closed_ql.hfvs; assumption
    if fn1: #0 ∈ q1 then
      have fr1: ✦ ∈ q1 := by tauto
      simp [sets, fn1, fr1, subst]; clear * -; tauto
    else
      simp only [fn1, false_or] at SEP; simp [subst, fn1, this]
      obtain SEP | ⟨fr1, SEP, _⟩ := SEP
      · trans; exact VQX; specialize SEP WFE.1; gcongr
        trans; swap; exact SEP.2.2.2; apply vars_locs_monotonic; simp
        split; have := SEP.1 (by assumption); simpa [this]; simp
      · specialize SEP WFE.1; simp [fr1]
        suffices lsf' ∩ lsx' ⊆ vars_locs V q1 by
          clear *- this; simp [sets] at *; tauto
        trans; swap; exact SEP.2.2.2
        apply overlapping ST ST1; assumption'
        rename _ \ {✦} ⊆ p => h; clear *- h; simp [sets] at *
        have: ∀a b, (¬a → b) ↔ b ∨ a := (by tauto); simpa [this] using h
        gcongr; apply vt_mono; simp; apply vt_mono; simp
  obtain ⟨S3, M3, vy, lsy, EV3, MM3, _, _, VTY, VQY⟩ := VTF
  exists S3, M3, vy, lsy; split_ands'
  · simp [tevaln] at EV1 EV2 EV3 ⊢
    obtain ⟨nm1, EV1⟩ := EV1; obtain ⟨nm2, EV2⟩ := EV2; obtain ⟨nm3, EV3⟩ := EV3
    exists 1 + nm1 + nm2 + nm3; intro n _; rcases n with - | n; omega
    simp! [bind]; rw [EV1]; simp!; rw [EV2]; simp!; rw [EV3]; simp!; rfl
    omega; omega; omega
  · apply stchain_tighten; apply stchain_chain; assumption
    apply stchain_chain; assumption'
    simp [sets]; simp [st_chain] at MM1 MM2 MM3; omega
  · apply se_trans_sub; swap; assumption; apply se_trans; assumption'
    simp [sets, ←ST.1]; rintro _ (H | H)
    · specialize VQF H; simp at VQF; rcases VQF with VQF | _; swap; tauto
      left; revert VQF; apply vars_locs_monotonic; simp [sets]
    · specialize VQX H; simp at VQX; rcases VQX with VQX | _
      left; revert VQX; apply vars_locs_monotonic; simp [sets]
      right; simp [st_chain, sets] at MM1 ⊢; omega
  · -- result type
    have Cqf := WFE.pclosed' (by simp: p ∩ qf ⊆ p)
    have Cqx := WFE.pclosed' (by simp: p ∩ qx ⊆ p)
    have Cp := WFE.pclosed
    rw [←valt_extend (V' := [(vtnone, lsf'), (vtnone, lsx')]),
      ←ty.subst_open_chain #0 %‖V‖,
      ←ty.subst_open_chain #1 %(‖V‖ + 1),
      ty.open_subst_comm]; rotate_left
    simp; c_free; simp!; simp; c_free;
    rw [occurs_subst]; simp; c_free; c_free; simp!
    repeat apply subst_tighten
    assumption; split_ands; simp!; c_extend; intro h; absurd h; c_free;
    split_ands; simp!; c_extend; intro h; absurd h; c_free;
    rw [valt_subst']; rotate_left
    simp [List.getElem_append_right]; exact ⟨rfl, rfl⟩; simp!; c_extend; assumption
    simp [val_type]; rfl; simp [Cqf.hfvs]; rw [occurs_subst]; simp
    by_cases h: ✦ ∈ qf; left; split_ands; c_free;
    simp [FFr h]; right; simp [h, lsf']; c_free; simp; simp!
    rwa [valt_subst']
    simp [List.getElem_append_right]; exact ⟨rfl, rfl⟩; simp!; c_extend; assumption
    simp [val_type]; rfl; simp [Cqx.hfvs]
    by_cases h: ✦ ∈ qx; left; split_ands; c_free;
    simp [XFr h]; right; simp [h, lsx']
  · -- result qualifier
    trans; assumption; clear VQY
    have: closed_ql.fvs ‖V‖ q2 := by apply closed_ql.hfvs; assumption
    simp [Finset.inter_subst]; simp [subst, List.getElem_append_right]
    simp [this, sets, or_assoc]; clear this
    intros l VQY; simp [st_chain] at MM1 MM2
    rcases VQY with VQY | VQY | VQY | VQY
    · left; have: q2 \ {✦, #0, #1} ⊆ p ∩ q2 := by
        apply Finset.subset_inter; assumption; simp
      apply vars_locs_monotonic; assumption'; simpa [Finset.insert_eq]
    · clear * - VQY VQX MM1; rcases VQY with ⟨hx, VQY⟩; simp [hx]
      specialize VQX VQY; simp at VQX; rcases VQX with _ | ⟨hfr, _⟩; tauto
      simp [hfr]; right; right; right; omega
    · clear * - VQY VQF; rcases VQY with ⟨h, VQY⟩; simp [h]; specialize VQF VQY
      simp at VQF; right; right; tauto
    · simp [VQY.1]; right; right; right; omega

-- ttabs with fsub

@[simp]
def sem_stp G q0 gr T1 T2 :=
  ∀ ⦃S M E V p⦄,
    env_type1 M E G V p →
    store_type S M →
    vars_locs V (q0 ∪ gr) ⊆ vars_locs V p →
    ∀ ⦃v ls⦄,
      val_type M V v T1 ls →
      (✦ ∉ q0 → ls ⊆ vars_locs V q0) →
      ∃ gl ⊆ vars_locs V (q0 ∪ gr),
        val_type M V v T2 (ls ∪ gl)

theorem sem_tapp:
  sem_type env f (.TAll T1 q1 T2 q2) p qf →
  closed_ty 0 ‖env‖ Tx →
  sem_stp env {✦} ∅ Tx T1 →
  #0 ∈ q1 ∨ sem_qtp env qx q1 ∨ ✦ ∈ q1 ∧
    sem_qtp env ((vars_trans env qf) ∩ (vars_trans env qx)) q1 ∧
    (vars_trans env qf ∩ vars_trans env qx) \ {✦} ⊆ p →

  q2 \ {✦, #0, #1} ⊆ p →
  (✦ ∈ qf → occurs .noneq T2 #0) →
  (✦ ∈ qx → occurs .noneq T2 #1) →
  sem_type env (.ttapp f Tx qx) ([#0 ↦ p ∩ qf] [#1 ↦ (Tx, p ∩ qx)] T2) p
    [#0 ↦ qf] [#1 ↦ qx] q2 :=
by
  intros TF Ctx TX SEP Cq2 FFr XFr; dsimp [-sem_qtp] at *; intros S M E V WFE ST
  obtain ⟨S1, M1, vf, lsf, EV1, MM1, ST1, _, VTF, VQF, EQF⟩ := TF WFE ST; clear TF
  have WFE1 := envt_store_change (M' := M1) WFE ?_; swap
  · apply stchain_tighten; assumption; apply lls_closed' ST
    apply env_type_store_wf WFE
  -- extend lsf & lsx
  let lsf' := if ✦ ∈ qf then lsf else vars_locs V (p ∩ qf)
  replace VTF := valt_grow (ls' := lsf') VTF ?_ ?_; rotate_left
  · simp [lsf']; split; simp; rename_i h; simpa [h] using VQF
  · simp [lsf']; split; exact (valt_wf VTF).1; apply env_type_store_wf' WFE1; simp
  replace VQF: lsf' ⊆ ?_ := by
    simp [lsf']; split; exact VQF; simp [sets]
  simp at TX; let vtx := (val_type · V · Tx ·); let lsx' := vars_locs V (p ∩ qx)
  replace TX: ∀ ⦃S M v lsx⦄, store_type S M → vtx M v lsx →
      val_type M (V ++ [(vtnone, lsf')]) v ([#0↦%‖V‖]T1) lsx := by
    simp [vtx]; introv ST VX; specialize TX _ ST VX; rotate_right 2
    apply envt1_store_change; apply envt1_tighten (p' := ∅); exact WFE1.1
    simp; simp [st_chain]; have := (valt_wf TX).2
    rwa [ty.open_free, valt_extend]; assumption; c_free;
  cases vf <;> simp only [val_type] at VTF
  obtain ⟨_, _, Ct2, _, _, _, _, FM1, VTF⟩ := VTF
  specialize VTF (M' := M1) (lsx := lsx') _ (by assumption) TX _ _
  simp [st_chain]; apply lls_closed' ST1; assumption
  simp [lsx']; apply env_type_store_wf' WFE1; simp
  · -- argument qualifier
    clear VTF; have: closed_ql.fvs ‖V‖ q1 := by
      apply closed_ql.hfvs; assumption
    if fn1: #0 ∈ q1 then
      have fr1: ✦ ∈ q1 := by tauto
      simp [sets, fn1, fr1, subst]; clear * -; tauto
    else
      simp only [fn1, false_or] at SEP; simp [subst, fn1, this]
      obtain SEP | ⟨fr1, SEP, _⟩ := SEP
      · specialize SEP WFE.1; trans; trans; swap; exact SEP.2.2.2
        simp [lsx']; apply vars_locs_monotonic; simp; simp
      · specialize SEP WFE.1; simp [fr1]
        suffices lsf' ∩ lsx' ⊆ vars_locs V q1 by
          clear *- this; simp [sets] at *; tauto
        trans; swap; exact SEP.2.2.2
        apply overlapping ST ST1; assumption'
        simp [st_chain]; simp [lsx']
        rename _ \ {✦} ⊆ p => h; clear *- h; simp [sets] at *
        have: ∀a b, (¬a → b) ↔ b ∨ a := (by tauto); simpa [this] using h
        gcongr; apply vt_mono; simp; apply vt_mono; simp
  obtain ⟨S3, M3, vy, lsy, EV3, MM3, _, _, VTY, VQY⟩ := VTF
  exists S3, M3, vy, lsy; split_ands'
  · simp [tevaln] at EV1 EV3 ⊢
    obtain ⟨nm1, EV1⟩ := EV1; obtain ⟨nm3, EV3⟩ := EV3
    exists 1 + nm1 + nm3; intro n _; rcases n with - | n; omega
    simp! [bind]; rw [EV1]; simp!; rw [EV3]; simp!; rfl
    omega; omega
  · apply stchain_tighten; apply stchain_chain; assumption'
    simp [sets]; simp [st_chain] at MM1; omega
  · apply se_trans_sub; assumption'
    simp [sets, ←ST.1]; rintro _ (H | H)
    · specialize VQF H; simp at VQF; rcases VQF with VQF | _; swap; tauto
      left; revert VQF; apply vars_locs_monotonic; simp [sets]
    · simp [lsx'] at H; left; revert H; apply vars_locs_monotonic; simp [sets]
  · -- result type
    have Cqf := WFE.pclosed' (by simp: p ∩ qf ⊆ p)
    have Cqx := WFE.pclosed' (by simp: p ∩ qx ⊆ p)
    have Cp := WFE.pclosed; rw [WFE.t2l] at Ctx
    rw [←valt_extend (V' := [(vtnone, lsf'), (vtx, lsx')]),
      ←ty.subst_open_chain #0 %‖V‖,
      ←ty.subst_open_chain #1 %(‖V‖ + 1),
      ty.open_subst_comm]; rotate_left
    simp; c_free; c_free; simp; c_free;
    rw [occurs_subst]; simp; c_free; c_free; c_free;
    repeat apply subst_tighten
    assumption; split_ands'; c_extend; intro h; absurd h; c_free;
    split_ands; simp!; c_extend; intro h; absurd h; c_free;
    rw [valt_subst']; rotate_left
    simp [List.getElem_append_right]; exact ⟨rfl, rfl⟩; simp!; c_extend; assumption
    simp [val_type]; rfl; simp [Cqf.hfvs]; rw [occurs_subst]; simp
    by_cases h: ✦ ∈ qf; left; split_ands; c_free;
    simp [FFr h]; right; simp [h, lsf']; c_free; c_free;
    rwa [valt_subst']
    simp [List.getElem_append_right]; exact ⟨rfl, rfl⟩; c_extend; c_extend; assumption
    simp [vtx]; ext; rwa [valt_extend]
    by_cases h: ✦ ∈ qx; left; simp; split_ands; c_free;
    simp [XFr h]; right; simp [h, lsx', Cqx.hfvs]
  · -- result qualifier
    trans; assumption; clear VQY
    have: closed_ql.fvs ‖V‖ q2 := by apply closed_ql.hfvs; assumption
    simp [Finset.inter_subst]; simp [subst, List.getElem_append_right]
    simp [this, sets, or_assoc]; clear this
    intros l VQY; simp [st_chain] at MM1
    rcases VQY with VQY | VQY | VQY | VQY
    · left; have: q2 \ {✦, #0, #1} ⊆ p ∩ q2 := by
        apply Finset.subset_inter; assumption; simp
      apply vars_locs_monotonic; assumption'; simpa [Finset.insert_eq]
    · simp [lsx'] at VQY; simp [VQY]
    · clear * - VQY VQF; rcases VQY with ⟨h, VQY⟩; simp [h]; specialize VQF VQY
      simp at VQF; right; right; tauto
    · simp [VQY.1]; right; right; right; omega

-- subtyping

theorem sem_sub:
  sem_type G t T1 p q1 →
  sem_stp G q1 gr T1 T2 →
  sem_qtp G (q1 ∪ gr) q2 →
  q2 \ {✦} ⊆ p →
  sem_type G t T2 p q2 :=
by
  intros HT STP QTP Q2P; dsimp; introv WFE ST
  obtain ⟨S', M', v, ls, _, MM, ST', _, VT, VQ, EQ⟩ := HT WFE ST
  have WFE': env_type M' E G V p := by
    apply envt_store_change; assumption; apply stchain_tighten; assumption
    apply lls_closed' ST; apply env_type_store_wf WFE
  specialize QTP WFE'.1; obtain ⟨Q1, _, _, Q2⟩ := QTP
  have VL1: vars_locs V (p ∩ q1) ⊆ vars_locs V q1 := by
    apply vars_locs_monotonic; simp
  have VL2: vars_locs V q2 ⊆ vars_locs V (p ∩ q2) := by
    trans vars_locs V (q2 \ {✦}); simp; apply vars_locs_monotonic
    clear *- Q2P; simp [sets] at *; tauto
  specialize STP WFE'.1 ST' _ VT _
  · trans; assumption; trans; assumption; apply vars_locs_monotonic; simp
  · simp at VQ; intro h; simp [h] at VQ; trans; assumption'
  obtain ⟨ls', VQ', VT'⟩ := STP; exists S', M', v, ls ∪ ls'; split_ands'
  · simp at VQ; clear *- Q2 VQ VQ' Q1 VL1 VL2; rw [Set.union_comm]
    trans ?_ ∪ ?_; gcongr; assumption'; rw [←Set.union_assoc]; gcongr
    trans; trans ?_ ∪ ?_; gcongr; assumption'
    apply Set.union_subset; simp; trans; swap; assumption; simp
    simp [sets]; intro _ h1 h2; simp [Q1, h1, h2]
  · split <;> simp at EQ
    trans; assumption; simp; simp

theorem sem_stp_trans:
  sem_stp G q0 g1 T1 T2 →
  sem_stp G (q0 ∪ g1) g2 T2 T3 →
  sem_stp G q0 (g1 ∪ g2) T1 T3 :=
by
  intros S1 S2; dsimp; introv WFE ST C VT1 VQ1; simp at C
  specialize S1 WFE ST _ VT1 VQ1
  · trans; swap; assumption; simp [sets]; clear *-; tauto
  obtain ⟨gl1, VQ2, VT2⟩ := S1; specialize S2 WFE ST _ VT2 _
  · trans; swap; assumption; simp [sets]
  · intro h; simp at h; specialize VQ1 h.1
    apply Set.union_subset; trans; assumption; simp; assumption
  obtain ⟨gl2, VQ3, VT3⟩ := S2; exists gl1 ∪ gl2
  rw [←Set.union_assoc, ←Finset.union_assoc]; split_ands'
  apply Set.union_subset
  trans; assumption; simp [sets]; clear *-; tauto; assumption

theorem sem_stp_refl:
  sem_stp G q0 ∅ T T :=
by
  dsimp; introv WFE ST C VT VQ; exists ∅; simpa

theorem sem_stp_top:
  sem_stp G q0 ∅ T .TTop :=
by
  dsimp; introv WFE ST C VT VQ; exists ∅; simp [val_type]
  exact (valt_wf VT).1

theorem sem_stp_ref:
  sem_stp G {✦} ∅ T1 T2 →
  sem_stp G {✦} ∅ T2 T1 →
  sem_qtp G (q1 \ {#0}) (q2 \ {#0}) →
  sem_qtp G (q2 \ {#0}) (q1 \ {#0}) →
  (#0 ∈ q1 ↔ #0 ∈ q2) →
  ✦ ∉ q1 → ✦ ∉ q2 →
  closed_ty 0 ‖G‖ T2 →
  sem_stp G q0 ∅ (.TRef T1 q1) (.TRef T2 q2) :=
by
  intros S1 S2 Q1 Q2 Hself Hfr1 Hfr2 Ct2; dsimp; introv WFE ST QP; simp at QP
  specialize S1 WFE ST (by simp); specialize S2 WFE ST (by simp)
  obtain ⟨-, Cq1, Cq2, Q1⟩ := Q1 WFE; obtain ⟨-, -, -, Q2⟩ := Q2 WFE
  replace Cq1: closed_ql false 1 ‖G‖ q1 := by
    apply closedql_fr_tighten; assumption; apply closedql_bv_widen; assumption
  replace Cq2: closed_ql false 1 ‖G‖ q2 := by
    apply closedql_fr_tighten; assumption; apply closedql_bv_widen; assumption
  introv VT1 VQ1; cases v <;> simp [val_type] at VT1
  exists ∅; simp [val_type]; simp [WFE.t2l] at Ct2 Cq1 Cq2
  split_ands''; rename_i VT1; simp at Q1 Q2
  have: vars_locs V q1 = vars_locs V q2 := by
    clear * - Q1 Q2; ext; tauto
  simp [subst, WFE.t2l, Cq1.hfvs, Cq2.hfvs, Hself, this] at VT1 ⊢
  simp [subst, this, Hself, Hfr1, Hfr2] at S1 S2
  obtain ⟨vt, qt, HM, LQ1, LQ2, VT1⟩ := VT1; exists vt, qt; split_ands'
  introv _; rw [VT1]; constructor; apply S1; apply S2; assumption

theorem sem_stp_ref_grow:
  sem_stp G {✦} ∅ T1 T2 →
  sem_stp G {✦} ∅ T2 T1 →
  sem_qtp G (q2 \ {#0}) (q1 \ {#0}) →
  sem_qtp G (q1 \ {#0}) ([#0 ↦ g] q2) →
  #0 ∈ q2 →
  ✦ ∉ q1 → ✦ ∉ q2 →
  closed_ty 0 ‖G‖ T2 →
  sem_stp G q g (.TRef T1 q1) (.TRef T2 q2) :=
by
  intros S1 S2 Q1 Q2 Hself Hfr1 Hfr2 Ct2; dsimp; introv WFE ST QP; simp at QP
  specialize S1 WFE ST (by simp); specialize S2 WFE ST (by simp); simp at S1 S2
  obtain ⟨-, Cq2, Cq1, Q1⟩ := Q1 WFE; obtain ⟨-, -, -, Q2⟩ := Q2 WFE
  replace Cq1: closed_ql false 1 ‖G‖ q1 := by
    apply closedql_fr_tighten; assumption; apply closedql_bv_widen; assumption
  replace Cq2: closed_ql false 1 ‖G‖ q2 := by
    apply closedql_fr_tighten; assumption; apply closedql_bv_widen; assumption
  introv VT1 VQ1; cases v <;> simp [val_type] at VT1
  exists vars_locs V g; simp [val_type]; simp [WFE.t2l] at Ct2 Cq1 Cq2
  split_ands''; tauto
  · apply Set.union_subset; assumption; trans; swap; apply env_type1_store_wf WFE
    trans; swap; assumption; simp
  rename_i VT1; simp [subst, Hself, Cq1.hfvs, Cq2.hfvs] at Q1 Q2 VT1 ⊢
  obtain ⟨vt, qt, HM, LQ1, LQ2, VT1⟩ := VT1; exists vt, qt; split_ands'
  · trans; assumption; clear *- Q2; apply Set.union_subset; trans; assumption
    simp [sets]; tauto; simp [sets]; tauto
  · trans; assumption'
  · introv _; rw [VT1]; constructor; apply S1; apply S2; assumption

theorem sem_stp_fun:
  closed_ty 0 ‖G‖ (.TFun T1b q1b T2b q2b) →
  closed_ql true 0 ‖G‖ qf0 →
  closed_ql false 0 ‖G‖ grf →
  sem_stp (G ++ [(.TTop, qf0 ∪ grf, .self)]) {✦}
     gr1  ([#0 ↦ %‖G‖] T1b) ([#0 ↦ %‖G‖] T1a) →
  {#0, ✦} ⊆ q1a ∨ sem_qtp (G ++ [(.TTop, qf0 ∪ grf, .self)])
    (gr1 ∪ [#0 ↦ %‖G‖] q1b) ([#0 ↦ %‖G‖] q1a) →
  sem_stp (G ++ [(.TTop, qf0 ∪ grf, .self), ([#0 ↦ %‖G‖] T1b, [#0 ↦ %‖G‖] q1b, .var)]) {✦}
     gr2  ([#0 ↦ %‖G‖] [#1 ↦ (%(‖G‖+1), gr1)] T2a) ([#0 ↦ %‖G‖] [#1 ↦ %(‖G‖+1)] T2b) →
  sem_qtp (G ++ [(.TTop, qf0 ∪ grf, .self), ([#0 ↦ %‖G‖] T1b, [#0 ↦ %‖G‖] q1b, .var)])
    (gr2 ∪ [#0 ↦ %‖G‖] [#1 ↦ (%(‖G‖+1), gr1)] q2a) ([#0 ↦ %‖G‖] [#1 ↦ %(‖G‖+1)] q2b) →
  gr1 \ {%‖G‖} ⊆ grf →
  gr2 \ {%‖G‖, %(‖G‖+1)} ⊆ grf →
  sem_stp G qf0 grf (.TFun T1a q1a T2a q2a) (.TFun T1b q1b T2b q2b) :=
by
  intros Cb Cqf0 Cgrf S1 Q1 S2 Q2 _ _; dsimp; introv WFE ST PQF VT1 VQ1; rename' ls => lsf
  let grf' := vars_locs V (qf0 ∪ grf)
  have: lsf ∪ grf' ⊆ pnat ‖M‖ := by
    apply Set.union_subset; apply (valt_wf VT1).1; simp only [grf']
    trans; assumption; apply env_type1_store_wf WFE
  replace VT1 := by
    apply valt_grow (ls' := lsf ∪ grf') VT1; simp; assumption
  have WFE1 := by  -- extend by function
    have: env_cell M V {%‖V‖} ‖V‖ .TTop (qf0 ∪ grf) .self v vtnone (lsf ∪ grf') := by
      simp; split_ands; simp!; rw [←WFE.t2l]; apply Finset.union_subset
      assumption; c_extend; simpa [val_type]; intro h1 h2; apply Set.union_subset
      trans; apply VQ1 h1; simp; simp [grf']; simp [grf']
    apply envt1_extend_stub WFE _ _ _ this; exact ∅
    simp; simp [st_chain]; rw [WFE.v2l]
  cases v <;> simp only [val_type] at VT1; exists grf'; split_ands; simp [grf']
  rw [WFE.t2l] at Cb; cases Cb; simp only [val_type]; split_ands''
  rename_i VT1; introv CH ST' VX QX
  replace WFE1 := by  -- store change
    simp at WFE1; apply envt1_store_change (M' := M') WFE1; apply stchain_tighten CH
    apply lls_mono; simp [WFE.t2l]
  replace this: lsf ∪ grf' ⊆ pnat ‖M'‖ := by
    simp [st_chain] at CH; trans; swap; exact CH.2.1
    intro _ h; apply lls_z; exact h
  have Cgr1: closed_ql false 0 (‖G‖+1) gr1 := by
    apply Finset.Subset.trans (s₂ := gr1 \ {%‖G‖} ∪ {%‖G‖}); simp
    apply Finset.union_subset; trans; assumption; c_extend; simp
  -- apply the function
  simp only [WFE.t2l] at S1 Q1
  have Cgrn: ∀⦃g V'⦄, g ⊆ grf → vars_locs (V ++ V') g ⊆ vars_locs V grf := by
    introv h; rw [← vars_locs_shrink (q := grf) (V' := V')]; apply vars_locs_monotonic h
    rw [← WFE.t2l]; exact Cgrf.hfvs
  let gr1' := vars_locs (V ++ [(vtnone, lsf ∪ grf')]) gr1
  have Hgr1': gr1' ⊆ lsf ∪ grf' := by
    simp [gr1']; have: gr1 ⊆ gr1 \ {%‖V‖} ∪ {%‖V‖} := by simp [sets]
    trans; apply vars_locs_monotonic; exact this
    simp [-Finset.sdiff_union_self_eq_union]; apply Set.union_subset; trans
    apply Cgrn; simpa [← WFE.t2l]; simp [grf', sets]; clear *-; tauto; simp
  specialize S1 WFE1 ST' _ VX (by simp)
  · simp [WFE.t2l]; simpa [gr1'] using Hgr1'
  obtain ⟨gr1'', Hgr1'', VX'⟩ := S1; simp at Hgr1''
  replace VX' := valt_grow (ls' := lsx ∪ gr1') VX' ?_ ?_  -- make it larger, for valt_substq
  rotate_left; gcongr; apply Set.union_subset; apply (valt_wf VX).1; trans; assumption'
  specialize VT1 CH ST' VX' _; trans ?_ ∪ gr1'; gcongr; assumption; simp [gr1']
  obtain Q1 | Q1 := Q1
  · intro _ h; simp [sets] at Q1; simp [Q1, subst]; clear *-; tauto
  · obtain ⟨Q1a, -, -, Q1b⟩ := Q1 WFE1
    simp at Q1b; simp [subst] at Q1a; clear * - Q1a Q1b; simp [sets] at *
    rintro _ ((H | H) | H); left; exact Q1b (.inr H); right; tauto; left; tauto
  -- extend by argument
  clear Q1 VX' Hgr1'' gr1''
  have WFE2 := by
    have: env_cell M' (V ++ [(vtnone, lsf ∪ grf')]) {%(‖V‖+1)} (‖V‖+1)
        ([#0 ↦ %‖V‖] T1b) ([#0 ↦ %‖V‖] q1b) .var vx vtnone lsx := by
      simp; split_ands'; apply subst_tighten; c_extend; simp
      apply subst_tighten; c_extend; simp [sets]
      intro h; simp [subst] at h; simpa [h] using QX
    apply envt1_extend_stub WFE1 _ _ _ this; exact {%‖V‖}
    simp; simp [st_chain]; apply lls_closed'; assumption'; simp [WFE.v2l]
  obtain ⟨S'', M'', vy, lsy, _, _, ST2, SE2, VY, QY⟩ := VT1
  replace WFE2 := by
    apply envt1_store_change (M' := M'') WFE2
    apply stchain_tighten; assumption; apply lls_closed' ST'
    simp [WFE.t2l, List.getElem_append_right]
    apply Set.union_subset; assumption; apply (valt_wf VX).1
  -- convert valty, qualy
  simp only [WFE.t2l, List.append_assoc] at S2 Q2 WFE2; specialize Q2 WFE2
  have: vars_locs (V ++ [(vtnone, lsf ∪ grf')] ++ [(vtnone, lsx)]) gr1 = gr1' := by
    rw [vars_locs_shrink]; simp [← WFE.t2l]; exact Cgr1.hfvs
  simp at this; specialize S2 WFE2 ST2 _ (v := vy) (ls := lsy) _ _
  · simp [List.getElem_append_right]
    have: gr2 ⊆ gr2 \ {%‖G‖, %(‖G‖+1)} ∪ {%‖G‖, %(‖G‖+1)} := by simp [Finset.insert_eq]
    trans; apply vars_locs_monotonic; exact this
    simp [-Finset.sdiff_union_self_eq_union, -Finset.union_insert]
    apply Set.union_subset; trans; apply Cgrn; assumption
    simp [grf', sets]; clear *-; tauto
    simp [WFE.t2l, Finset.insert_eq, List.getElem_append_right]
  · simp; rw [←ty.subst_open_chain #1 %(‖V‖+1), ty.open_subst_comm, valt_subst]
    convert VY; simp [List.getElem_append_right, this, val_type, vtnone]
    rfl; simp; simp!
    simp [closed_ql, sets, ←WFE.t2l]; apply closedql_extend Cgr1 <;> simp
    assumption; simp; simp; intro; c_free; simp!; simp; c_free;
  · simp
  obtain ⟨gr2', Hgr2, VY'⟩ := S2; obtain ⟨Q2a, -, -, Q2b⟩ := Q2
  simp [subst] at Q2a; simp at Q2b Hgr2
  rw [←ql.subst_chain #1 %(‖V‖+1), ql.subst_comm, vars_locs_open (vt := vtnone)] at Q2b
  simp [List.getElem_append_right, this] at Q2b; rotate_left
  simp; simp [closed_ql, sets, ←WFE.t2l]; apply closedql_extend Cgr1 <;> simp
  simp; simp; c_free; simp; c_free;
  -- finally, supply all the witnesses
  exists S'', M'', vy, lsy ∪ gr2'; split_ands'
  · apply se_sub SE2; clear * - Hgr1'; simp [sets] at *; rintro _ (H | H | H)
    tauto; tauto; specialize Hgr1' H; tauto
  · trans ?_ ∪ ?_; gcongr <;> assumption
    clear * - Q2a Q2b; simp [sets] at *; rintro _ ((H | H) | H)
    specialize Q2b (.inr H); tauto; tauto; tauto

theorem sem_stp_tvar:
  G[x]? = some (Tx, qx, .tvar) →
  sem_stp G q ∅ (.TVar (%x)) Tx :=
by
  intro h; dsimp; introv WFE ST C VT VQ; exists ∅; simp; simp [val_type] at VT
  obtain ⟨_, vt, ⟨ls0, h1⟩, VT⟩ := VT; have := WFE.byV h1; simp [h] at this
  obtain ⟨_, _, _, ⟨rfl, rfl, rfl⟩, _, -, -, -, VT1, -⟩ := this
  apply VT1; rfl; assumption; apply VT; simp
  simp [st_chain]; apply lls_closed'; assumption'

theorem sem_stp_all:
  closed_ty 0 ‖G‖ (.TAll T1b q1b T2b q2b) →
  closed_ql true 0 ‖G‖ qf0 →
  closed_ql false 0 ‖G‖ grf →
  sem_stp (G ++ [(.TTop, qf0 ∪ grf, .self)]) {✦}
     ∅  ([#0 ↦ %‖G‖] T1b) ([#0 ↦ %‖G‖] T1a) →
  {#0, ✦} ⊆ q1a ∨ sem_qtp (G ++ [(.TTop, qf0 ∪ grf, .self)])
        ([#0 ↦ %‖G‖] q1b) ([#0 ↦ %‖G‖] q1a) →
  sem_stp (G ++ [(.TTop, qf0 ∪ grf, .self), ([#0 ↦ %‖G‖] T1b, [#0 ↦ %‖G‖] q1b, .tvar)]) {✦}
     gr2  ([#0 ↦ %‖G‖] [#1 ↦ %(‖G‖+1)] T2a) ([#0 ↦ %‖G‖] [#1 ↦ %(‖G‖+1)] T2b) →
  sem_qtp (G ++ [(.TTop, qf0 ∪ grf, .self), ([#0 ↦ %‖G‖] T1b, [#0 ↦ %‖G‖] q1b, .tvar)])
    (gr2 ∪ [#0 ↦ %‖G‖] [#1 ↦ %(‖G‖+1)] q2a) ([#0 ↦ %‖G‖] [#1 ↦ %(‖G‖+1)] q2b) →
  gr2 \ {%‖G‖, %(‖G‖+1)} ⊆ grf →
  sem_stp G qf0 grf (.TAll T1a q1a T2a q2a) (.TAll T1b q1b T2b q2b) :=
by
  intros Cb Cqf0 Cgrf S1 Q1 S2 Q2 _; dsimp; introv WFE ST PQF VT1 VQ1; rename' ls => lsf
  let grf' := vars_locs V (qf0 ∪ grf)
  have: lsf ∪ grf' ⊆ pnat ‖M‖ := by
    apply Set.union_subset; apply (valt_wf VT1).1; simp only [grf']
    trans; assumption; apply env_type1_store_wf WFE
  replace VT1 := by
    apply valt_grow (ls' := lsf ∪ grf') VT1; simp; assumption
  have WFE1 := by  -- extend by function
    have: env_cell M V {%‖V‖} ‖V‖ .TTop (qf0 ∪ grf) .self v vtnone (lsf ∪ grf') := by
      simp; split_ands; simp!; rw [←WFE.t2l]; apply Finset.union_subset
      assumption; c_extend; simpa [val_type]; intro h1 h2; apply Set.union_subset
      trans; apply VQ1 h1; simp; simp [grf']; simp [grf']
    apply envt1_extend_stub WFE _ _ _ this; exact ∅
    simp; simp [st_chain]; rw [WFE.v2l]
  cases v <;> simp only [val_type] at VT1; exists grf'; split_ands; simp [grf']
  rw [WFE.t2l] at Cb; cases Cb; simp only [val_type]; split_ands''
  rename_i VT1; introv CH ST' VX VX' QX
  replace WFE1 := by  -- store change
    simp at WFE1; apply envt1_store_change (M' := M') WFE1; apply stchain_tighten CH
    apply lls_mono; simp [WFE.t2l]
  replace this: lsf ∪ grf' ⊆ pnat ‖M'‖ := by
    simp [st_chain] at CH; trans; swap; exact CH.2.1
    intro _ h; apply lls_z; exact h
  -- apply the function
  simp only [WFE.t2l] at S1 Q1
  have Cgrn: ∀⦃g V'⦄, g ⊆ grf → vars_locs (V ++ V') g ⊆ vars_locs V grf := by
    introv h; rw [← vars_locs_shrink (q := grf) (V' := V')]; apply vars_locs_monotonic h
    rw [← WFE.t2l]; exact Cgrf.hfvs
  specialize VT1 (vt := vt) (lsx := lsx) CH ST' _ VX' _
  · introv ST VT; replace WFE1 := by
      apply envt1_store_change (M' := M); apply envt1_tighten (p' := ∅)
      exact WFE1; simp; simp [st_chain]
    specialize S1 WFE1 ST; simp at S1; apply S1; apply VX; assumption'
  · trans; exact QX; obtain Q1 | Q1 := Q1
    · intro _ h; simp [sets] at Q1; simp [Q1, subst]; clear *-; tauto
    · obtain ⟨Q1a, -, -, Q1b⟩ := Q1 WFE1
      gcongr; simp [sets]; simp [subst] at Q1a
      clear *- Q1a; tauto
  -- extend by argument
  clear Q1
  have WFE2 := by
    have: env_cell M' (V ++ [(vtnone, lsf ∪ grf')]) {%(‖V‖+1)} (‖V‖+1)
        ([#0 ↦ %‖V‖] T1b) ([#0 ↦ %‖V‖] q1b) .tvar (.vbool false) vt lsx := by
      simp; split_ands'; apply subst_tighten; c_extend; simp
      apply subst_tighten; c_extend; simp [sets]
      simpa [val_type]
      intro h; simp [subst] at h; simpa [h] using QX
    apply envt1_extend_stub WFE1 _ _ _ this; exact {%‖V‖}
    simp; simp [st_chain]; apply lls_closed'; assumption'; simp [WFE.v2l]
  obtain ⟨S'', M'', vy, lsy, _, _, ST2, SE2, VY, QY⟩ := VT1
  replace WFE2 := by
    apply envt1_store_change (M' := M'') WFE2
    apply stchain_tighten; assumption; apply lls_closed' ST'
    simp [WFE.t2l, List.getElem_append_right]
    apply Set.union_subset; assumption'
  -- convert valty, qualy
  simp only [WFE.t2l, List.append_assoc] at S2 Q2 WFE2; specialize Q2 WFE2
  simp at this; specialize S2 WFE2 ST2 _ (v := vy) (ls := lsy) _ _
  · simp [List.getElem_append_right]
    have: gr2 ⊆ gr2 \ {%‖G‖, %(‖G‖+1)} ∪ {%‖G‖, %(‖G‖+1)} := by simp [Finset.insert_eq]
    trans; apply vars_locs_monotonic; exact this
    simp [-Finset.sdiff_union_self_eq_union, -Finset.union_insert]
    apply Set.union_subset; trans; apply Cgrn; assumption
    simp [grf', sets]; clear *-; tauto
    simp [WFE.t2l, Finset.insert_eq, List.getElem_append_right]
  · simpa
  · simp
  obtain ⟨gr2', Hgr2, VY'⟩ := S2; obtain ⟨Q2a, -, -, Q2b⟩ := Q2
  simp [subst] at Q2a; simp at Q2b Hgr2
  -- finally, supply all the witnesses
  exists S'', M'', vy, lsy ∪ gr2'; split_ands'
  · trans ?_ ∪ ?_; gcongr <;> assumption
    clear * - Q2a Q2b; simp [sets] at *; rintro _ ((H | H) | H)
    specialize Q2b (.inr H); tauto; tauto; tauto
