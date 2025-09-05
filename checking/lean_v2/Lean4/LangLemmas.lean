import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image
import Lean4.LangDefs

syntax "split_ands'" : tactic
syntax "split_ands''" : tactic
macro_rules
| `(tactic| split_ands) => `(tactic| constructorm* _ ∧ _)
| `(tactic| split_ands') => `(tactic| constructorm* _ ∧ _ <;> try trivial)
| `(tactic| split_ands'') => `(tactic| casesm* _ ∧ _; split_ands')

attribute [cnf] and_or_left or_and_right and_assoc or_assoc

lemma Nat.le_of_forall_lt {a b: ℕ}:
  (∀x < a, x < b) ↔ a ≤ b :=
by
  constructor <;> intro H
  · apply Nat.le_of_not_lt; intro h; specialize H _ h; omega
  · omega

-- shim, to be removed
@[simp] lemma List.set_getElem?_self {as: List α} {i: Nat} {v: α} (h: as[i]? = some v):
  as.set i v = as :=
by
  apply List.ext_getElem; simp; intro n h₁ h₂; rw [List.getElem_set]; split <;> simp_all

namespace Reachability

-- qualifiers

@[simp]
lemma Finset.mem_ite [Decidable b] {x y: Finset α}:
  i ∈ (if b then x else y) ↔ b ∧ i ∈ x ∨ ¬b ∧ i ∈ y :=
by
  by_cases b <;> rename_i h <;> simp [h]

@[simp]
lemma qdom_subset {fr1 fr2: Bool}:
  qdom fr1 b1 f1 ⊆ qdom fr2 b2 f2 ↔
  fr1 ≤ fr2 ∧ b1 ≤ b2 ∧ f1 ≤ f2 :=
by
  constructor <;> intro H
  · simp [qdom] at H; split_ands
    specialize @H ✦; simpa using H
    rw [←Nat.le_of_forall_lt]; intro x; specialize @H (#x); simpa using H
    rw [←Nat.le_of_forall_lt]; intro x; specialize @H (%x); simpa using H
  · simp [qdom]; gcongr <;> simp [sets]
    tauto; omega; omega

@[simp] lemma qdom_mem_fr: ✦ ∈ qdom fr bvs fvs ↔ fr = true := by simp [qdom]
@[simp] lemma qdom_mem_bv: #x ∈ qdom fr bvs fvs ↔ x < bvs := by simp [qdom]
@[simp] lemma qdom_mem_fv: %x ∈ qdom fr bvs fvs ↔ x < fvs := by simp [qdom]

def closed_ql.hfvs (H: closed_ql r b f q):
  closed_ql.fvs f q :=
by
  intros x Q; specialize H Q; simpa using H

-- bv shiftings

@[simp] lemma bvshift_bv {n: ℕ}: #x + n = #(x + n) := by simp [bvShift]
@[simp] lemma bvshift_fv {n: ℕ}: %x + n = %x := by simp [bvShift]
@[simp] lemma bvshift_fr {n: ℕ}: ✦ + n = ✦ := by simp [bvShift]
@[simp] lemma bvShift_eq_fr {a: id} {n: ℕ}: a + n = ✦ ↔ a = ✦ := by cases a <;> simp
@[simp] lemma bvShift_eq_fr' {a: id} {n: ℕ}: ✦ = a + n ↔ a = ✦ := by rw [Eq.comm]; simp
@[simp] lemma bvShift_eq_bv: a + n = #x ↔ ∃ m, a = #m ∧ m + n = x := by cases a <;> simp
@[simp] lemma bvShift_eq_bv': #x = a + n ↔ ∃ m, a = #m ∧ m + n = x := by rw [Eq.comm]; simp
@[simp] lemma bvShift_eq_fv {a: id} {n m: ℕ}: a + n = %m ↔ a = %m := by cases a <;> simp

@[simp] lemma bvShift_assoc {x: id} {n1 n2: ℕ}:
  x + n1 + n2 = x + (n1 + n2) :=
by
  cases x <;> simp; omega

@[simp] lemma bvShift_add0 {x: id}: x + 0 = x := by cases x <;> simp

@[simp] lemma bvShift_inj {a b: id} {n: ℕ}: a + n = b + n ↔ a = b :=
  by cases a <;> cases b <;> simp

@[simp]
lemma closedql_bvsShift_singleton {x: id}:
  x + n ∈ qdom fr (mb + n) mf ↔ x ∈ qdom fr mb mf :=
by
  cases x <;> simp

@[simp]
lemma bvShift_ite {n: ℕ} {q1 q2: id} [Decidable b]:
  (ite b q1 q2) + n = ite b (q1+n) (q2+n) :=
by
  split <;> simp

@[simp]
lemma ql.bvshift_subst_comm {x: id} {y q: ql} {n: ℕ}:
  ([x ↦ y] q) + n = [x+n ↦ y+n] (q+n) :=
by
  ext i; simp [bvsShift, subst]; constructor
  · rintro ⟨a', h, rfl⟩; simpa
  · rintro (⟨⟨a, h1, rfl⟩, h2⟩ | ⟨h1, a, h2, rfl⟩)
    exists a; simp at h2; simp [h1, h2]
    exists a; simp [h1, h2]

@[simp]
lemma ql.bvshift_singleton {x: id} {n: ℕ}:
  ({x}: ql) + n = {x + n} :=
by
  simp [bvsShift]

@[simp]
lemma ql.bvshift_empty {n: ℕ}:
  (∅: ql) + n = ∅ :=
by
  simp [bvsShift]

@[simp]
lemma closedql_bvsshift:
  closed_ql fr (bv+n) fv (q+n) ↔ closed_ql fr bv fv q :=
by
  simp [sets, bvsShift]

@[simp]
lemma ql.bvsshift_if [Decidable b] {q1 q2: ql} {n: ℕ}:
  (ite b q1 q2) + n = ite b (q1+n) (q2+n) :=
by
  split <;> rfl

@[simp]
lemma ql.mem_bvsshift {x: id} {y: ql} {n: ℕ}:
  x + n ∈ y + n ↔ x ∈ y :=
by
  simp [bvsShift]

-- occurrences

@[simp]
lemma occ_flag.flip.inv_1:
  occ_flag.flip f = .none ↔ f = .none :=
by
  cases f <;> simp

@[simp]
lemma occ_flag.flip.inv_2:
  occ_flag.flip f = .no_contravariant ↔ f = .no_covariant :=
by
  cases f <;> simp

@[simp]
lemma occ_flag.flip.inv_3:
  occ_flag.flip f = .no_covariant ↔ f = .no_contravariant :=
by
  cases f <;> simp

lemma occurs_none (h: occurs .none T x):
  occurs f T x :=
by
  induction T generalizing x f <;> simp! at *
  tauto; tauto; tauto; tauto

-- closedness extension

lemma closedql_extend:
  closed_ql fr bvs fvs q →
  fr ≤ fr' →
  bvs ≤ bvs' →
  fvs ≤ fvs' →
  closed_ql fr' bvs' fvs' q :=
by
  intros H _ _ _; simp [closed_ql] at *; trans; apply H
  simp; tauto

lemma closedty_extend:
  closed_ty mb mf T →
  mb ≤ mb' →
  mf ≤ mf' →
  closed_ty mb' mf' T :=
by
  intros H1 H2 H3; induction mb, mf, T using closed_ty.induct generalizing mb' mf' with
  | case1 => simpa
  | case2 => simpa
  | case3 _ _ _ _ IH =>
    simp! at H1 ⊢; split_ands''; apply IH; assumption'
    apply closedql_extend; assumption'; simp; omega
  | case4 _ _ _ _ _ _ IH1 IH2 =>
    simp! at H1 ⊢; split_ands''
    apply IH1; assumption'; omega; apply IH2; assumption'; omega
    apply_rules [closedql_extend]; omega; apply_rules [closedql_extend]; omega
  | case5 =>
    simp! at H1 ⊢; apply closedql_extend (q := {_})
    simpa [sets]; assumption'; all_goals simp
  | case6 _ _ _ _ _ _ IH1 IH2 =>
    simp! at H1 ⊢; split_ands''
    apply IH1; assumption'; omega; apply IH2; assumption'; omega
    apply_rules [closedql_extend]; omega; apply_rules [closedql_extend]; omega

class ClosedExtend (α₁: outParam (Bool → ℕ → ℕ → Prop)) (α₂: outParam (Bool → Prop)) (α₃ α₄: outParam (ℕ → Prop)) (β: Prop) where
  c_extend: α₁ fr bv fv → α₂ fr → α₃ bv → α₄ fv → β

export ClosedExtend (c_extend)

instance: ClosedExtend (closed_ql · · · q) (· ≤ fr') (· ≤ mb') (· ≤ mf')
    (closed_ql fr' mb' mf' q) where
  c_extend := by
    intros; apply closedql_extend; assumption'

instance: ClosedExtend (closed_ql · · · q) (· ≤ fr') (· ≤ mb') (· ≤ mf')
    (q ⊆ qdom fr' mb' mf') where
  c_extend := by
    intros; apply closedql_extend; assumption'

instance: ClosedExtend (x ∈ qdom · · ·) (· ≤ fr') (· ≤ mb') (· ≤ mf')
    (x ∈ qdom fr' mb' mf') where
  c_extend := by
    intros; apply closedql_extend (q := {x}); simpa [closed_ql]; assumption'; simp

instance: ClosedExtend (x ∉ qdom · · ·) (fr' ≤ ·) (mb' ≤ ·) (mf' ≤ ·)
    (x ∉ qdom fr' mb' mf') where
  c_extend := by
    intros _ _ _ h; intros; contrapose h; simp at h ⊢
    apply closedql_extend (q := {x}); simpa [closed_ql]; assumption'; simp

instance: ClosedExtend (fun _ b f => closed_ty b f T) (fun _ => True) (· ≤ mb') (· ≤ mf')
    (closed_ty mb' mf' T) where
  c_extend := by
    intros; apply closedty_extend; assumption'

syntax "c_extend" term : tactic
syntax "c_extend": tactic
macro_rules
| `(tactic| c_extend $e) => `(tactic| (apply c_extend $e <;> first | exact false | simp | skip))
| `(tactic| c_extend) => `(tactic| c_extend (by assumption))

-- free from closedness

lemma closedql_free:
  closed_ql fr bv fv q → x ∉ qdom fr bv fv → x ∉ q :=
by
  intros h1 h2 h; specialize h1 h; contradiction

lemma closedty_free:
  closed_ty bv fv T →
  x ∉ qdom true bv fv →
  occurs .none T x :=
by
  intros H1 H2; induction T generalizing bv x <;> simp! at H1 ⊢
  case TRef IH =>
    split_ands''; apply IH; assumption'
    apply closedql_free; assumption; simp; c_extend;
  case TFun T1 q1 T2 q2 IH1 IH2 =>
    split_ands''
    apply IH1; assumption; simpa; apply closedql_free; assumption; simpa
    apply IH2; assumption; simpa; apply closedql_free; assumption; simpa
  case TVar =>
    rintro rfl; revert H1
    eapply closedql_free; assumption'; simp [closed_ql]
  case TAll T1 q1 T2 q2 IH1 IH2 =>
    split_ands''
    apply IH1; assumption; simpa; apply closedql_free; assumption; simpa
    apply IH2; assumption; simpa; apply closedql_free; assumption; simpa

class ClosedFree (α: outParam (Bool → ℕ → ℕ → Prop)) (β: outParam (Bool → ℕ → ℕ → Prop)) (γ: Prop) where
  c_free: α fr bv fv → β fr bv fv → γ

export ClosedFree (c_free)

instance: ClosedFree (closed_ql · · · q) (x ∉ qdom · · ·)
    (x ∉ q) where
  c_free := closedql_free

instance {x: id}: ClosedFree (closed_ql · · · q) (∀(n: ℕ), x+n ∉ qdom · · ·)
    (∀(n: ℕ), x+n ∉ q) where
  c_free := by intros; apply c_free; assumption; tauto

instance: ClosedFree (fun _ b f => closed_ty b f T) (fun _ b f => x ∉ qdom true b f)
    (occurs f T x) where
  c_free h1 h2 := (closedty_free h1 h2) |> occurs_none

instance {x: id}: ClosedFree (fun _ b f => closed_ty b f T) (fun _ b f => ∀(n: ℕ), x+n ∉ qdom true b f)
    (∀(n: ℕ), occurs f T (x+n)) where
  c_free h1 h2 := by intros; apply c_free; assumption; tauto; exact false

syntax "c_free" term : tactic
syntax "c_free": tactic
macro_rules
| `(tactic| c_free $e) => `(tactic| apply c_free $e <;> first | exact false | simp | skip)
| `(tactic| c_free) => `(tactic| c_free (by assumption))

-- closedness tighten

lemma closedql_fr_tighten:
  ✦ ∉ q →
  closed_ql true bv fv q →
  closed_ql false bv fv q :=
by
  intros h1 h2; intro a h; specialize h2 h
  cases a <;> simp at * <;> tauto

lemma closedql_bv_tighten:
  #bv ∉ q →
  closed_ql fr (bv+1) fv q →
  closed_ql fr bv fv q :=
by
  intros H1 H2; simp [sets] at *; intros a h; specialize H2 h
  cases a <;> simp at *
  assumption'; rename_i n; suffices n ≠ bv by omega
  rintro rfl; contradiction

lemma closedql_bv_widen:
  closed_ql fr bv fv (q \ {#bv}) →
  closed_ql fr (bv+1) fv q :=
by
  intros H1; simp [sets] at *; intros a h; specialize H1 h
  by_cases h1: a = #bv; subst a; simp
  specialize H1 h1; clear h1 h; revert a; apply qdom_subset.2; simp

lemma closedql_fv_tighten:
  %fv ∉ q →
  closed_ql fr bv (fv+1) q →
  closed_ql fr bv fv q :=
by
  intros H1 H2; simp [sets] at *; intros a h; specialize H2 h
  cases a <;> simp at *
  assumption'; rename_i n; suffices n ≠ fv by omega
  rintro rfl; contradiction

class ClosedQlTighten (α: outParam Prop) (β: Prop) where
  closedql_tighten: α → β

export ClosedQlTighten (closedql_tighten)

instance: ClosedQlTighten (closed_ql true bv fv q) (closed_ql false bv fv (q \ {✦})) where
  closedql_tighten := by
    intro h; apply closedql_fr_tighten; simp
    simp [closed_ql]; trans q; simp; assumption

instance: ClosedQlTighten (closed_ql fr (bv+1) fv q) (closed_ql fr bv fv (q \ {#bv})) where
  closedql_tighten := by
    intro h; apply closedql_bv_tighten; simp
    simp [closed_ql]; trans q; simp; assumption

instance: ClosedQlTighten (closed_ql fr bv (fv+1) q) (closed_ql fr bv fv (q \ {%fv})) where
  closedql_tighten := by
    intro h; apply closedql_fv_tighten; simp
    simp [closed_ql]; trans q; simp; assumption

instance [sup: ClosedQlTighten α (closed_ql fr bv fv (q \ {x}))]:
    ClosedQlTighten α (q \ {x} ⊆ qdom fr bv fv) where
  closedql_tighten := by
    rw [←closed_ql.eq_1]; exact sup.closedql_tighten

lemma closedty_bv_tighten:
  occurs .none T #bv →
  closed_ty (bv+1) fv T →
  closed_ty bv fv T :=
by
  intros H1 H2; induction T generalizing bv <;> simp! at H1 H2 ⊢
  case TRef =>
    split_ands''; tauto; apply closedql_bv_tighten; assumption'
  case TFun =>
    split_ands''; tauto; tauto
    apply closedql_bv_tighten; assumption'
    apply closedql_bv_tighten; assumption'
  case TVar x =>
    apply closedql_bv_tighten (q := {x}); simpa; simpa [closed_ql]; simp
  case TAll =>
    split_ands''; tauto; tauto
    apply closedql_bv_tighten; assumption'
    apply closedql_bv_tighten; assumption'

lemma closedty_fv_tighten:
  occurs .none T %fv →
  closed_ty bv (fv+1) T →
  closed_ty bv fv T :=
by
  intros H1 H2; induction T generalizing bv <;> simp! at H1 H2 ⊢
  case TRef =>
    split_ands''; tauto; apply closedql_fv_tighten; assumption'
  case TFun =>
    split_ands''; tauto; tauto
    apply closedql_fv_tighten; assumption'
    apply closedql_fv_tighten; assumption'
  case TVar x =>
    apply closedql_fv_tighten (q := {x}); simpa; simpa [closed_ql]; simp
  case TAll =>
    split_ands''; tauto; tauto
    apply closedql_fv_tighten; assumption'
    apply closedql_fv_tighten; assumption'

lemma closed_ql.induct (motive: ∀ {fv q}, closed_ql fr bv fv q → Prop)
  (case1: ∀ {q1} (c1: closed_ql fr bv 0 q1), motive c1)
  (case2: ∀ {i q1} (_: closed_ql fr bv i q1)
    (_: ∀ {q2} (c: closed_ql fr bv i q2), motive c)
    (c2: closed_ql fr bv (i + 1) q1), motive c2)
  (case3: ∀ {i q1} (_: closed_ql fr bv i q1)
    (_: ∀ {q2} (c: closed_ql fr bv i q2), motive c)
    (c2: closed_ql fr bv (i + 1) (q1 ∪ {%i})), motive c2)
  (c: closed_ql fr bv fv q): motive c :=
by
  induction fv generalizing q
  next => apply case1
  next i ih =>
    by_cases h: %i ∈ q; swap
    · apply case2; apply closedql_fv_tighten; assumption'
    have: q = q \ {%i} ∪ {%i} := by ext; simp; rintro rfl; assumption
    have c': closed_ql fr bv i (q \ {%i}) := closedql_tighten c
    generalize q \ {%i} = q' at *; subst q; clear h
    apply case3; assumption'

-- substitution

@[simp]
lemma id.subst_shift {a b x: id} {n: ℕ}:
  [a ↦ b] x + n = [a+n ↦ b+n] (x+n) :=
by
  simp [subst]

@[simp]
lemma ql.subst_singleton {a b x: id}:
  [a ↦ {b}] {x} = {[a ↦ b] x} :=
by
  ext; simp [subst]; split
  next h => simp [h]
  next h => simp [h]; rintro rfl; contrapose! h; subst a; simp

lemma Finset.inter_subst {p q q1: ql}:
  p ∩ [x ↦ q1] q = (p ∩ q) \ {x} ∪ ?[x ∈ q] p ∩ q1 :=
by
  ext i; simp [subst]; tauto

@[simp]
lemma occurs_open {n n' x: id}:
  occurs f ([n ↦ n'] T) x ↔ (x ≠ n → occurs f T x) ∧ (x = n' → occurs f T n) :=
by
  induction T generalizing f x n n' <;> simp!
  case TRef T1 q1 IH =>
    simp [IH]; simp [subst]; tauto
  case TFun T1 q1 T2 q2 IH1 IH2 =>
    simp [IH1, IH2]; simp [subst]; clear IH1 IH2
    by_cases h: x = n; subst n; simp
    by_cases h: x = n'; subst n'; simp; simp [h]; simp [h]
    by_cases h: x = n'; subst n'; simp; swap; simp [h]
    cases f <;> simp <;> constructor <;> intro <;> split_ands''
  case TVar a =>
    simp [subst]; split; subst n; tauto
    rename_i h; simp [h]; by_cases x = n; subst x; tauto; tauto
  case TAll T1 q1 T2 q2 IH1 IH2 =>
    simp [IH1, IH2]; simp [subst]; clear IH1 IH2
    by_cases h: x = n; subst n; simp
    by_cases h: x = n'; subst n'; simp; simp [h]; simp [h]
    by_cases h: x = n'; subst n'; simp; swap; simp [h]
    cases f <;> simp <;> constructor <;> intro <;> split_ands''

lemma occurs_subst {t: ty} {q : ql} {x: id}
  (h1: ∀{a: ℕ}, x + a ∉ q) (h3: ∀{a: ℕ}, occurs .none t (x+a)):
  occurs f ([n ↦ (t, q)] T) x ↔ (x ≠ n → occurs f T x) :=
by
  induction T generalizing f x n q <;> simp!
  case TRef T1 q1 IH =>
    simp [IH, h1, h3]; simp [subst, h1]
    by_cases h: x = n <;> simp [h]
  case TFun T1 q1 T2 q2 IH1 IH2 =>
    simp [IH1, IH2, h1, h3]; simp [subst, h1]
    by_cases h: x = n <;> simp [h]
  case TVar a =>
    split; subst a; constructor; intro _ h; simp [h]
    intros; apply occurs_none; specialize @h3 0; simpa using h3
    simp!; by_cases h: x = n <;> simp [h]; tauto
  case TAll T1 q1 T2 q2 IH1 IH2 =>
    simp [IH1, IH2, h1, h3]; simp [subst, h1]
    by_cases h: x = n <;> simp [h]

lemma closedql_subst (h1: closed_ql fr mb mf q') (h2: x ∈ qdom fr mb mf):
  closed_ql fr mb mf [x ↦ q'] q ↔ closed_ql fr mb mf q :=
by
  simp [subst, sets]; constructor
  intros h x1 _; by_cases x1 = x; subst x1; assumption; tauto; tauto

lemma closedty_open (h1: x' ∈ qdom false mb mf) (h2: x ∈ qdom false mb mf):
  closed_ty mb mf [x ↦ x'] T ↔ closed_ty mb mf T :=
by
  induction T generalizing x x' mb <;> simp!
  case TRef T1 q1 IH =>
    congrm ?_ ∧ ?_; rw [IH]; assumption'
    rw [closedql_subst]; simpa [closed_ql]; simpa
  case TFun T1 q1 T2 q2 IH1 IH2 =>
    congrm ?_ ∧ ?_ ∧ ?_ ∧ ?_ ∧ ?_ ∧ _ ∧ _
    · rw [IH1]; simpa; simpa
    · rw [IH2]; simpa; simpa
    · rw [closedql_subst]; simp [closed_ql]; c_extend; simp; c_extend;
    · rw [closedql_subst]; simp [closed_ql]; c_extend; simp; c_extend;
    · simp [subst]; congr!; by_cases h: ✦ ∈ q1 <;> simp [h]
      left; rintro rfl; simp at h2; rintro _ rfl; simp at h1
  case TVar a =>
    simp [subst]; split; subst x; simp [h1, h2]; simp
  case TAll T1 q1 T2 q2 IH1 IH2 =>
    congrm ?_ ∧ ?_ ∧ ?_ ∧ ?_ ∧ ?_ ∧ _ ∧ _
    · rw [IH1]; simpa; simpa
    · rw [IH2]; simpa; simpa
    · rw [closedql_subst]; simp [closed_ql]; c_extend; simp; c_extend;
    · rw [closedql_subst]; simp [closed_ql]; c_extend; simp; c_extend;
    · simp [subst]; congr!; by_cases h: ✦ ∈ q1 <;> simp [h]
      left; rintro rfl; simp at h2; rintro _ rfl; simp at h1

lemma closedty_subst {t: ty}
  (h1: closed_ql false 0 mf q)
  (h3: closed_ty 0 mf t) (h2: x ∈ qdom false mb mf):
  closed_ty mb mf [x ↦ (t, q)] T ↔ closed_ty mb mf T :=
by
  induction T generalizing x q mb <;> simp! at h1 ⊢
  case TRef T1 q1 IH =>
    congrm ?_ ∧ ?_; rw [IH]; assumption'
    rw [closedql_subst]; c_extend; simpa
  case TFun T1 q1 T2 q2 IH1 IH2 =>
    congrm ?_ ∧ ?_ ∧ ?_ ∧ ?_ ∧ ?_ ∧ ?_ ∧ ?_
    · rwa [IH1]; simpa
    · rwa [IH2]; simpa
    · rw [closedql_subst]; c_extend; simp; c_extend;
    · rw [closedql_subst]; c_extend; simp; c_extend;
    · simp [subst]; have: x ≠ ✦ := by rintro rfl; simp at h2
      simp [this]; simp [(by c_free: #0 ∉ q), (by c_free: ✦ ∉ q)]
    · rw [occurs_subst]; simp; c_free; c_free;
    · rw [occurs_subst]; simp; c_free; c_free;
  case TVar =>
    split; subst x; constructor <;> intro; assumption; c_extend; simp!
  case TAll T1 q1 T2 q2 IH1 IH2 =>
    congrm ?_ ∧ ?_ ∧ ?_ ∧ ?_ ∧ ?_ ∧ ?_ ∧ ?_
    · rwa [IH1]; simpa
    · rwa [IH2]; simpa
    · rw [closedql_subst]; c_extend; simp; c_extend;
    · rw [closedql_subst]; c_extend; simp; c_extend;
    · simp [subst]; have: x ≠ ✦ := by rintro rfl; simp at h2
      simp [this]; simp [(by c_free: #0 ∉ q), (by c_free: ✦ ∉ q)]
    · rw [occurs_subst]; simp; c_free; c_free;
    · rw [occurs_subst]; simp; c_free; c_free;

lemma ty.open_free {x x': id}:
  occurs .none T x →
  [x ↦ x'] T = T :=
by
  intro h; induction T generalizing x x' <;> simp <;> simp! at h
  case TRef IH =>
    simp [IH h.1]; ext; simp [subst, h.2]
  case TFun IH1 IH2 =>
    obtain ⟨h1, h2, h3, h4⟩ := h
    simp [IH1 h1, IH2 h3]; split_ands <;> ext
    simp [subst, h2]; simp [subst, h4]
  case TVar =>
    simp [subst]; tauto
  case TAll IH1 IH2 =>
    obtain ⟨h1, h2, h3, h4⟩ := h
    simp [IH1 h1, IH2 h3]; split_ands <;> ext
    simp [subst, h2]; simp [subst, h4]

lemma ty.subst_free {x: id} {t: ty} {q: ql}:
  occurs .noneq T x →
  [x ↦ (t, q)] T = [x ↦ (t, (∅: ql))] T :=
by
  intro h; induction T generalizing x t q <;> simp <;> simp! at h
  case TRef IH =>
    rw [IH]; simp; ext; simp [subst, h]; simp [h]
  case TFun IH1 IH2 =>
    obtain ⟨h1, h2, h3, h4⟩ := h
    simp [IH1 h1, IH2 h3]; split_ands <;> ext
    simp [subst, h2]; simp [subst, h4]
  case TAll IH1 IH2 =>
    obtain ⟨h1, h2, h3, h4⟩ := h
    simp [IH1 h1, IH2 h3]; split_ands <;> ext
    simp [subst, h2]; simp [subst, h4]

lemma ty.subst_free' {x: id} {t: ty} {q: ql}:
  occurs .none T x →
  [x ↦ (t, q)] T = T :=
by
  intro h; induction T generalizing x t q <;> simp <;> simp! at h
  case TRef IH =>
    rw [IH]; simp; ext; simp [subst, h]; simp [h]
  case TFun IH1 IH2 =>
    obtain ⟨h1, h2, h3, h4⟩ := h
    simp [IH1 h1, IH2 h3]; split_ands <;> ext
    simp [subst, h2]; simp [subst, h4]
  case TVar x => simp [h]
  case TAll IH1 IH2 =>
    obtain ⟨h1, h2, h3, h4⟩ := h
    simp [IH1 h1, IH2 h3]; split_ands <;> ext
    simp [subst, h2]; simp [subst, h4]

lemma closedty_subst' {t: ty}
  (h1: closed_ql true 0 mf q) (h1': ✦ ∈ q → occurs .noneq T x)
  (h3: closed_ty 0 mf t) (h2: x ∈ qdom false mb mf):
  closed_ty mb mf [x ↦ (t, q)] T ↔ closed_ty mb mf T :=
by
  if h: ✦ ∈ q then
    specialize h1' h; simp [ty.subst_free, h1']
    rw [closedty_subst]; simp [sets]; assumption'
  else
    rw [closedty_subst]; assumption'; apply closedql_fr_tighten h h1

lemma ty.subst_qchange (x: id) (q': ql) {t: ty} {q: ql}:
  q = q' ∨ occurs .noneq T x →
  [x ↦ (t, q)] T = [x ↦ (t, q')] T :=
by
  rintro (h | h); simp [h]; simp [ty.subst_free, h]

@[simp]
lemma ty.subst_open_eq {t: ty}:
  [x ↦ (ty.TVar %n, {%n})] t = [x ↦ %n] t :=
by
  induction t generalizing x <;> simp
  case TRef T q IH =>
    rw [IH]
  case TFun T1 q1 T2 q2 IH1 IH2 =>
    rw [IH1, IH2]; simp
  case TVar =>
    simp [subst]; split <;> simp
  case TAll T1 q1 T2 q2 IH1 IH2 =>
    rw [IH1, IH2]; simp

lemma ql.subst_self (x: id) (q: ql):
  [x ↦ {x}] q = q :=
by
  ext a; simp [subst]; by_cases h: a = x <;> simp [h]

lemma ql.subst_comm {q q1 q2: ql} (h1: x2 ∉ q1) (h2: x1 ∉ q2) (h3: x1 ≠ x2):
  [x1 ↦ q1] [x2 ↦ q2] q = [x2 ↦ q2] [x1 ↦ q1] q :=
by
  ext i; simp [subst, h1, h2, h3, Eq.comm (a := x2), cnf]; constructor
  · rintro (h | h | h); tauto; tauto
    right; left; split_ands''; rintro rfl; contradiction
  · rintro (h | h | h); tauto; tauto
    right; left; split_ands''; rintro rfl; contradiction

-- h1 could be: x ≠ a → x ≠ b; don't try to merge it into an ite
lemma ql.subst_comm' {q y: ql} (h1: x ≠ b) (h2: x = a → b ∉ q):
  [a ↦ {b}] [x ↦ y] q = [([a ↦ b] x) ↦ ([a ↦ {b}] y)] [a ↦ {b}] q :=
by
  ext i; simp [subst, cnf]; split
  · subst x; specialize h2 rfl; simp [h1, h2]; constructor
    rintro (h | h | h) <;> simp [h]; left; rintro rfl; tauto
    rintro (h | h | h) <;> simp [h]
  · rename_i h2; change a ≠ x at h2; simp [h1, h2, Ne.symm h2]; constructor
    rintro (h | h | h | h) <;> simp [h]; obtain ⟨h, rfl⟩ := h; simp [Ne.symm h1]
    rintro (h | h | h | h) <;> simp [h]

lemma ty.open_comm {t: ty} {q1 q2: id} (h1: x2 ≠ q1) (h2: x1 ≠ q2) (h3: x1 ≠ x2):
  [x1 ↦ q1] [x2 ↦ q2] t = [x2 ↦ q2] [x1 ↦ q1] t :=
by
  induction t generalizing x1 x2 q1 q2 <;> simp
  case TRef IH =>
    rw [IH, ql.subst_comm]; simp; simpa; simpa; simpa; assumption'
  case TFun IH1 IH2 =>
    rw [IH1, IH2]; simp; split_ands <;> rw [ql.subst_comm]
    simpa; simpa; simpa; simpa; simpa; simpa; simpa; simpa; simpa; simpa; simpa; simpa
  case TVar =>
    simp [subst]; split; subst x2; split; subst x1; contradiction
    simp; split; simp; simp
  case TAll IH1 IH2 =>
    rw [IH1, IH2]; simp; split_ands <;> rw [ql.subst_comm]
    simpa; simpa; simpa; simpa; simpa; simpa; simpa; simpa; simpa; simpa; simpa; simpa

lemma ty.open_subst_comm {x1 x2 x1': id} {t t2: ty} {q2: ql}
  (h1: x2 ≠ x1') (h2: ∀(n: ℕ), x1 + n ∉ q2) (h2t: ∀(n: ℕ), occurs .none t2 (x1+n)) (h3: x1 ≠ x2):
  [x1 ↦ x1'] [x2 ↦ (t2, q2)] t = [x2 ↦ (t2, q2)] [x1 ↦ x1'] t :=
by
  induction t generalizing x1 x1' x2 t2 q2
  simp; simp
  case TRef T q IH =>
    simp; split_ands
    · rw [IH]; simp [h1]; simp [h2]; assumption'
    · rw [ql.subst_comm]; simp [h1]; simp [h2]; simp [h3]
  case TFun T1 q1 T2 q2 IH1 IH2 =>
    simp; split_ands
    · rw [IH1]; simp [h1]; simp [h2]; simp [h2t]; simp [h3]
    · rw [ql.subst_comm]; simp [h1]; simp [h2]; simp [h3]
    · rw [IH2]; simp [h1]; simp [h2]; simp [h2t]; simp [h3]
    · rw [ql.subst_comm]; simp [h1]; simp [h2]; simp [h3]
  case TVar =>
    simp; split; subst_vars; split; rw [ty.open_free]
    convert_to occurs _ _ (x1 + 0); simp; apply h2t
    rename_i h; simp [subst, h3] at h
    split; rename_i h; simp [subst] at h; split at h <;> contradiction; simp
  case TAll T1 q1 T2 q2 IH1 IH2 =>
    simp; split_ands
    · rw [IH1]; simp [h1]; simp [h2]; simp [h2t]; simp [h3]
    · rw [ql.subst_comm]; simp [h1]; simp [h2]; simp [h3]
    · rw [IH2]; simp [h1]; simp [h2]; simp [h2t]; simp [h3]
    · rw [ql.subst_comm]; simp [h1]; simp [h2]; simp [h3]

lemma ql.subst_chain x1 x2 {q q2: ql} (h0: x2 ∉ q):
  [x2 ↦ q2] [x1 ↦ {x2}] q = [x1 ↦ q2] q :=
by
  ext i; simp [subst]; constructor; tauto
  rintro (h | h); swap; tauto
  left; split_ands; tauto; rintro rfl; tauto

lemma ty.subst_open_chain x1 x2 {t T: ty} {q: ql} (h0: occurs .none T x2):
  [x2 ↦ (t, q)] [x1 ↦ x2] T = [x1 ↦ (t, q)] T :=
by
  induction T generalizing x1 x2 t q <;> simp
  case TRef T q IH =>
    simp! at h0; rw [IH, ql.subst_chain]; simp; tauto; tauto
  case TFun T1 q1 T2 q2 IH1 IH2 =>
    simp! at h0; rw [IH1, IH2]; simp; split_ands <;> rw [ql.subst_chain]
    tauto; tauto; tauto; tauto
  case TVar x =>
    simp! at h0; simp [subst]; split; simp; simp
  case TAll T1 q1 T2 q2 IH1 IH2 =>
    simp! at h0; rw [IH1, IH2]; simp; split_ands <;> rw [ql.subst_chain]
    tauto; tauto; tauto; tauto

lemma ql.subst_cancel x1 x2 {q: ql} (h0: x2 ∉ q):
  [x2 ↦ {x1}] [x1 ↦ {x2}] q = q :=
by
  ext i; simp [subst, cnf, h0]; constructor
  rintro (⟨h, -⟩ | ⟨h, rfl⟩); assumption'
  intro h; simp [h]; by_cases h: i = x1 <;> simp [h]
  subst i; assumption; rintro rfl; contradiction

lemma ty.open_cancel {t: ty} (h0: occurs .none t x2):
  [x2 ↦ x1] [x1 ↦ x2] t = t :=
by
  induction t generalizing x1 x2 <;> simp! at h0 ⊢
  case TRef IH => simp [IH, ql.subst_cancel, h0]
  case TFun IH1 IH2 => simp [IH1, IH2, h0, ql.subst_cancel]
  case TVar => simp [subst]; split; subst x1; simp; simp
  case TAll IH1 IH2 => simp [IH1, IH2, h0, ql.subst_cancel]

class ClosedSubstTighten (α: outParam Prop) (β: outParam Prop) (γ: Prop) where
  subst_tighten: α → β → γ

export ClosedSubstTighten (subst_tighten)

instance: ClosedSubstTighten (closed_ql fr (bv+1) fv q) (closed_ql fr bv fv q1)
    (closed_ql fr bv fv [#bv ↦ q1] q) where
  subst_tighten := by
    intro h1 h2; apply closedql_bv_tighten; simp [subst]; intro; c_free;
    rwa [closedql_subst]; c_extend; simp

instance: ClosedSubstTighten (closed_ql fr bv (fv+1) q) (closed_ql fr bv fv q1)
    (closed_ql fr bv fv [%fv ↦ q1] q) where
  subst_tighten := by
    intro h1 h2; apply closedql_fv_tighten; simp [subst]; intro; c_free;
    rwa [closedql_subst]; c_extend; simp

instance [sup: ClosedSubstTighten α β (closed_ql fr bv fv q)]:
    ClosedSubstTighten α β (q ⊆ qdom fr bv fv) where
  subst_tighten := by
    rw [← closed_ql.eq_1]; exact sup.subst_tighten

instance: ClosedSubstTighten (closed_ty (bv+1) fv T) (q ∈ qdom false bv fv)
    (closed_ty bv fv [#bv ↦ q] T) where
  subst_tighten := by
    intro h1 h2; apply closedty_bv_tighten; simp; rintro rfl; simp at h2
    rwa [closedty_open]; c_extend; simp

instance: ClosedSubstTighten (closed_ty bv (fv+1) T) (q ∈ qdom false bv fv)
    (closed_ty bv fv [%fv ↦ q] T) where
  subst_tighten := by
    intro h1 h2; apply closedty_fv_tighten; simp; rintro rfl; simp at h2
    rwa [closedty_open]; c_extend; simp

instance {t: ty} {q: ql}: ClosedSubstTighten
    (closed_ty (bv+1) fv T)
    (closed_ty 0 fv t ∧ closed_ql true 0 fv q ∧ (✦ ∈ q → occurs .noneq T #bv))
    (closed_ty bv fv [#bv ↦ (t, q)] T) where
  subst_tighten := by
    rintro h1 ⟨h2, h3, h4⟩; apply closedty_bv_tighten
    rw [occurs_subst]; simp; c_free; c_free;
    rwa [closedty_subst']; assumption'; simp

instance {t: ty} {q: ql}: ClosedSubstTighten
    (closed_ty bv (fv+1) T)
    (closed_ty 0 fv t ∧ closed_ql false 0 fv q ∧ (✦ ∈ q → occurs .noneq T %fv))
    (closed_ty bv fv [%fv ↦ (t, q)] T) where
  subst_tighten := by
    rintro h1 ⟨h2, h3, h4⟩; apply closedty_fv_tighten
    rw [occurs_subst]; simp; c_free; c_free;
    rwa [closedty_subst']; c_extend; assumption; c_extend; simp

-- splicing

@[simp]
lemma id.splice_bv {x: id}:
  x.splice n d = #x' ↔ x = #x' :=
by
  cases x <;> simp; split <;> simp

@[simp]
lemma id.splice_fr {x: id}:
  x.splice n d = ✦ ↔ x = ✦ :=
by
  cases x <;> simp; split <;> simp

@[simp]
lemma id.splice_bvShift_comm {x: id} (m n d: ℕ):
  (x+m).splice n d = x.splice n d + m :=
by
  cases x <;> simp

@[simp]
lemma id.splice_subst_comm ⦃x' x: id⦄:
  ([#a ↦ x'] x).splice n δ = [#a ↦ x'.splice n δ] x.splice n δ :=
by
  simp [subst, splice]; symm; split <;> rename_i h
  · split at h; split at h <;> simp at h; subst x; simp
  · by_cases h: #a = x <;> simp [h]; subst x; simp at h

@[simp]
lemma ql.splice_singleton {x: id} (n d: ℕ):
  ql.splice {x} n d = {x.splice n d} :=
by
  simp [ql.splice]

@[simp]
lemma ql.splice_subst_comm ⦃x': id⦄ ⦃q: ql⦄:
  ([#x ↦ {x'}] q).splice n δ = [#x ↦ {x'.splice n δ}] q.splice n δ :=
by
  ext a; simp [subst, ql.splice]; constructor <;> intro h
  · obtain ⟨a', ⟨h1a, h1b⟩ | ⟨h1a, h1b⟩, h2⟩ := h
    · left; split_ands; exists a'; contrapose! h1b; subst a; simpa using h1b
    · right; split_ands'; subst x' a; rfl
  · obtain ⟨⟨a', h1a, h1b⟩, h1c⟩ | ⟨h1, h2⟩ := h
    · exists a'; split_ands'; left; split_ands'; contrapose! h1c; subst a a'; simp
    · exists x'; simp [h1, h2]

lemma ql.splice_self (h: closed_ql.fvs n q):
  q.splice n δ = q :=
by
  ext a; simp [ql.splice]; constructor <;> intro h0
  · obtain ⟨a', h1, h2⟩ := h0; subst a; simp [id.splice]; split; split; trivial
    specialize h h1; contradiction; trivial
  · exists a; split_ands'; cases a <;> simp; specialize h h0; omega

@[simp]
lemma ql.fr_mem_splice {q: ql}:
  ✦ ∈ q.splice n d ↔ ✦ ∈ q :=
by
  simp [ql.splice]

@[simp]
lemma ql.bv_mem_splice {q: ql}:
  #x ∈ q.splice n d ↔ #x ∈ q :=
by
  simp [ql.splice]

@[simp]
lemma ty.splice_open_comm ⦃x': id⦄ ⦃t: ty⦄:
  ([#x ↦ x'] t).splice n δ = [#x ↦ x'.splice n δ] t.splice n δ :=
by
  induction t generalizing x x' <;> simp!
  next _ _ IH => simp [IH]
  next _ _ _ _ IH1 IH2 => simp [IH1, IH2]
  next _ _ _ _ IH1 IH2 => simp [IH1, IH2]

lemma ty.splice_self (h: closed_ty n' n T):
  T.splice n δ = T :=
by
  induction T generalizing n' <;> simp! at h ⊢
  case TRef T q IH =>
    cases h; rename_i C1 C2; split_ands
    apply IH; assumption; apply ql.splice_self; exact C2.hfvs
  case TFun T1 q1 T2 q2 IH1 IH2 =>
    split_ands'' <;> rename_i C2 C4 _ _ _
    apply IH1; assumption; apply ql.splice_self; exact C2.hfvs
    apply IH2; assumption; apply ql.splice_self; exact C4.hfvs
  case TVar a =>
    cases a <;> simp; simp at h; omega
  case TAll T1 q1 T2 q2 IH1 IH2 =>
    split_ands'' <;> rename_i C2 C4 _ _ _
    apply IH1; assumption; apply ql.splice_self; exact C2.hfvs
    apply IH2; assumption; apply ql.splice_self; exact C4.hfvs

@[simp]
lemma occurs_bv_splice:
  occurs f (T.splice n d) #x = occurs f T #x :=
by
  induction T generalizing f x <;> simp!
  case TRef IH => rw [IH]; simp
  case TFun IH1 IH2 => rw [IH1, IH2]
  case TVar a => cases a <;> simp; split <;> simp
  case TAll IH1 IH2 => rw [IH1, IH2]

lemma closedql_splice (h: closed_ql fr mb mf q) (n d: ℕ):
  closed_ql fr mb (mf + d) (q.splice n d) :=
by
  simp [ql.splice, sets] at *; intro x h1
  specialize h h1; cases x <;> simp at *
  assumption'; split <;> simp <;> omega

lemma closedty_splice (h: closed_ty mb mf T) (n d: ℕ):
  closed_ty mb (mf + d) (T.splice n d) :=
by
  induction mb, mf, T using closed_ty.induct <;> simp! at h ⊢
  next =>
    split_ands''; tauto; apply closedql_splice; assumption
  next =>
    split_ands''; tauto; tauto
    apply closedql_splice; assumption
    apply closedql_splice; assumption
  next x =>
    cases x <;> simp at *; assumption; split <;> simp <;> omega
  next =>
    split_ands''; tauto; tauto
    apply closedql_splice; assumption
    apply closedql_splice; assumption

-- measurement

def ty_size (t: ty): ℕ :=
  match t with
  | .TRef T _ => 1 + ty_size T
  | .TFun T1 _ T2 _ => 1 + ty_size T1 + ty_size T2
  | .TAll T1 _ T2 _ => 1 + ty_size T1 + ty_size T2
  | _ => 1

@[simp]
lemma open_preserves_tysize {x x': id} {T: ty}:
  ty_size [x ↦ x'] T = ty_size T :=
by
  induction T generalizing x x' with
  | TTop => simp!
  | TBool => simp!
  | TRef _ _ IH => simp!; rw [IH]
  | TFun _ _ _ _ IH1 IH2 => simp!; rw [IH1, IH2]
  | TVar => simp!
  | TAll _ _ _ _ IH1 IH2 => simp!; rw [IH1, IH2]

@[simp]
lemma subst_preserves_tysize {x: id} {T t: ty} {q: ql} (h: ty_size t = 1):
  ty_size [x ↦ (t, q)] T = ty_size T :=
by
  induction T generalizing x with
  | TTop => simp!
  | TBool => simp!
  | TRef _ _ IH => simp!; rw [IH]
  | TFun _ _ _ _ IH1 IH2 => simp!; rw [IH1, IH2]
  | TVar => simp; split <;> simp [h, ty_size]
  | TAll _ _ _ _ IH1 IH2 => simp!; rw [IH1, IH2]

lemma ty.induct' (motive: ty → Prop)
  (TTop: motive .TTop)
  (TBool: motive .TBool)
  (TRef: ∀ T q, (∀ T', ty_size T = ty_size T' → motive T') → motive (.TRef T q))
  (TFun: ∀ T1 q1 T2 q2,
      (∀ T1', ty_size T1 = ty_size T1' → motive T1') →
      (∀ T2', ty_size T2 = ty_size T2' → motive T2') → motive (.TFun T1 q1 T2 q2))
  (TVar: ∀ x, motive (.TVar x))
  (TAll: ∀ T1 q1 T2 q2,
      (∀ T1', ty_size T1 = ty_size T1' → motive T1') →
      (∀ T2', ty_size T2 = ty_size T2' → motive T2') → motive (.TAll T1 q1 T2 q2))
  t: motive t :=
by
  generalize h: ty_size t = n; replace h: ty_size t ≤ n := by omega
  induction n generalizing t <;> cases t <;> simp! at h; assumption'
  next IH _ _ =>
    apply TRef; intros _ h; apply IH; omega
  next IH _ _ _ _ =>
    apply TFun <;> intros _ h <;> apply IH <;> omega
  next => apply TVar
  next IH _ _ _ _ =>
    apply TAll <;> intros _ h <;> apply IH <;> omega

-- telescope, transitive closures

lemma telescope_shrink:
  telescope (G ++ G') → telescope G :=
by
  intro T; simp only [telescope] at T ⊢; intros _ _ _ _ h
  rw [←List.getElem?_append_left] at h; specialize T h; assumption
  rw [List.getElem?_eq_some] at h; tauto

lemma telescope_extend (h1: closed_ty 0 ‖G‖ T) (h: closed_ql true 0 ‖G‖ q) (H: telescope G):
  telescope (G ++ [(T, q, bn)]) :=
by
  simp only [telescope] at *; intros x _ _ _ H1
  have := (List.getElem?_eq_some.1 H1).1; simp at this
  if h': x < ‖G‖ then
    rw [List.getElem?_append_left] at H1; apply H; assumption; assumption
  else
    have: x = ‖G‖ := by omega
    subst x; simp at H1; obtain ⟨rfl, rfl, rfl⟩ := H1; tauto

@[simp]
lemma vars_trans_if [Decidable a]:
  vars_trans G (if a then b else c) = if a then vars_trans G b else vars_trans G c :=
by
  if h: a then simp [h] else simp [h]

@[simp]
lemma vars_trans_empty:
  vars_trans G ∅ = ∅ :=
by
  induction G using List.reverseRecOn <;> simp [vars_trans]
  simpa [←vars_trans.eq_1]

@[simp]
lemma vars_trans_or:
  vars_trans G (p ∪ q) = vars_trans G p ∪ vars_trans G q :=
by
  induction G using List.reverseRecOn generalizing p q <;> simp [vars_trans]
  rw [←vars_trans.eq_1]; rename_i G e IH; obtain ⟨_, q', _⟩ := e; simp [IH]
  ext; simp; tauto

lemma vars_trans_one' (h: x ≥ ‖G‖):
  vars_trans G {%x} = {%x} :=
by
  induction G using List.reverseRecOn <;> simp [vars_trans]
  rw [←vars_trans.eq_1]; rename_i G e IH
  simp at h; specialize IH (by omega)
  simp [IH]; left; intro; exfalso; omega

@[simp]
lemma vars_trans_one (h: x < ‖G‖) (T: telescope G):
  vars_trans G {%x} = {%x} ∪ vars_trans G G[x].2.1 :=
by
  induction G using List.reverseRecOn <;> simp [vars_trans]
  simp at h; rw [←vars_trans.eq_1]; rename_i G e IH
  obtain ⟨_, q'⟩ := e; simp at h
  if h: ‖G‖ = x then
    simp [h, vars_trans_one']; split <;> simp
  else
    have: x < ‖G‖ := by omega
    apply telescope_shrink at T; simp [List.getElem_append, *]
    apply List.getElem?_eq_getElem at this; generalize G[x] = e at *
    replace T := (T this).2; simp [sets] at T; split
    case isTrue t => specialize T t; simp at T; exfalso; omega
    case isFalse => simp

lemma vt_mono (H: p ⊆ q):
  vars_trans G p ⊆ vars_trans G q :=
by
  induction G using List.reverseRecOn generalizing p q <;> simp [vars_trans]
  assumption; rw [←vars_trans.eq_1]; rename_i G e IH; simp
  specialize IH H; gcongr; split
  next h => specialize H h; simp [H]
  next => simp

lemma vt_closed:
  telescope G →
  vars_trans G q ⊆ q ∪ qdom true 0 ‖G‖ :=
by
  intro T; induction G using List.reverseRecOn generalizing q <;> simp [vars_trans]
  rw [←vars_trans.eq_1]; rename_i G e IH
  have: (G ++ [e])[‖G‖]? = some e := by simp
  apply T at this; simp [sets] at this; generalize e.2 = q' at *; simp
  apply telescope_shrink at T; rw [Finset.union_subset_iff]; split_ands
  · trans; apply IH; assumption; gcongr; simp
  · split; swap; simp; trans; apply IH; trivial; trans
    apply Finset.union_subset; exact this.2; simp
    trans; swap; apply Finset.subset_union_right; simp

lemma vt_closing:
  q ⊆ vars_trans G q :=
by
  induction G using List.reverseRecOn generalizing q
  next => simp [vars_trans]
  next G a IH =>
    simp [vars_trans]; simp [←vars_trans.eq_1]
    trans; apply IH; simp

@[simp]
lemma vt_shrink:
  closed_ql.fvs ‖G‖ q →
  vars_trans (G ++ [(T, q1)]) q = vars_trans G q :=
by
  intro H2; simp [vars_trans]; rw [←vars_trans.eq_1]; split
  case isTrue h => specialize H2 h; simp at H2
  case isFalse => simp

-- context growth

namespace ctx_grow

lemma inversion:
  ctx_grow (G ++ [(T, q, bn)]) G' gs →
  ∃ G'' q', G' = G'' ++ [(T, q', bn)] ∧
    if bn = .self ∧ ‖G‖ ∈ gs then q ⊆ q' ∧ ✦ ∉ q' \ q else q = q' :=
by
  intro h; generalize g1: G'.splitAt ‖G‖ = G1; simp at g1
  have: G1.1 ++ G1.2 = G' := by subst G1; simp
  have: (List.drop ‖G‖ G').length = 1 := by simp [←h.1]
  rw [List.length_eq_one] at this; obtain ⟨⟨T', q', bn'⟩, this⟩ := this
  rw [this] at g1; clear this; generalize List.take _ _ = G0 at g1
  subst G1; simp at this; subst G'; have := h.2 ‖G‖; simp at this
  have L := h.1; simp at L; simp [L] at this; exists G0, q'; simp
  obtain ⟨rfl, rfl, rfl⟩ | h := this; simp
  obtain ⟨h1, _, _, _, h2, C, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩⟩ := h
  simp [L, h1, h2]; intro h; specialize C h; simpa using C

lemma induct (motive: ∀⦃G G'⦄, ctx_grow G G' gs → Prop)
  (case1: ∀(h: ctx_grow [] [] gs), motive h)
  (case2: ∀⦃G a G' a'⦄ (h: ctx_grow (G ++ [a]) (G' ++ [a']) gs)
    (_: ∀ (h1: ctx_grow G G' gs), motive h1), motive h)
  (h: ctx_grow G G' gs): motive h :=
by
  induction G using List.reverseRecOn generalizing G'
  next => have := h.1; symm at this; simp at this; subst G'; apply case1
  next G' a' IH =>
    obtain ⟨G'', q', this, -⟩ := h.inversion
    revert h; simp [this]; intro h; change motive h; apply case2; apply IH

lemma append:
  ctx_grow G G' gs →
  ctx_grow (G++g) (G'++g) gs :=
by
  intros H; simp [ctx_grow] at *; obtain ⟨H1, H2⟩ := H; split_ands'
  intro i; if h: i < ‖G‖ then
    simp only [List.getElem?_append_left, h, ←H1]; apply H2
  else
    left; simp at h; simp [List.getElem?_append_right, h, ←H1]

lemma shrink:
  ctx_grow (G++g) (G'++g') gs →
  ‖g‖ = ‖g'‖ →
  ctx_grow G G' gs :=
by
  intro H H1; simp [ctx_grow] at *; simp [H1] at H; split_ands''
  intro i; rename_i H; specialize H i
  if h: i < ‖G‖ then
    simp only [h, (by omega: i < ‖G'‖), List.getElem?_append_left] at H; exact H
  else
    left; simp at h; simp [h, List.getElem?_eq_none]; omega

lemma gs_shrink:
  ctx_grow G G' (gs ∪ {‖G‖}) →
  ctx_grow G G' gs :=
by
  intro CG; simp [ctx_grow] at *; obtain ⟨h1, h2⟩ := CG
  simp [h1]; intro i; specialize h2 i; obtain h2 | h2 := h2; simp [h2]
  if h: i = ‖G'‖ then subst i; simp [h1] else right; simpa [h, h1] using h2

lemma inversion2:
  ctx_grow (G ++ [(T1, q1, .self), (T2, q2, bn2)]) G' gs → bn2 ≠ .self →
  ∃ G'' q1', G' = G'' ++ [(T1, q1', .self), (T2, q2, bn2)] ∧ q1 ⊆ q1' ∧
    (q1 = ∅ → closed_ql false 0 ‖G‖ q1') ∧ (‖G‖ ∉ gs → q1 = q1') :=
by
  intro CG h; rw [List.append_cons] at CG
  have := CG.inversion; simp [h] at this; obtain ⟨G'1, _, rfl, -, -, rfl⟩ := this
  have := (CG.shrink rfl).inversion; simp at this; obtain ⟨G', q1', rfl, h⟩ := this
  exists G', q1'; simp; split_ands'; rotate_right
  · intro h1; simp [h1] at h; assumption
  · split at h <;> simp [h]
  rintro rfl; simp at CG; have := CG.2 ‖G‖; simp [List.getElem_append_right] at this
  have L := CG.1; simp at L; simp [L, List.getElem_append_right] at this
  obtain rfl | ⟨-, _, _, _, -, _, ⟨-, rfl⟩, ⟨-, rfl⟩⟩ := this; simp [sets]
  rename_i h; simpa [L] using h

@[deprecated]
lemma gs_widen:
  ctx_grow G G' gs1 →
  gs1 ⊆ gs2 →
  ctx_grow G G' gs2 :=
by
  intros h1 h2; simp [ctx_grow] at *; simp [h1.1]; intro i; replace h1 := h1.2 i
  obtain h1 | h1 := h1; tauto; right; split_ands''; specialize @h2 i; tauto

lemma trans:
  ctx_grow G1 G2 gs →
  ctx_grow G2 G3 gs →
  ctx_grow G1 G3 gs :=
by
  intros h1 h2; simp [ctx_grow] at *; split_ands; omega; intro i
  replace h1 := h1.2 i; replace h2 := h2.2 i
  obtain h1 | h1 := h1; simpa [h1]; right
  obtain h2 | h2 := h2; simpa [←h2]; obtain ⟨_, T1, q1, q2, _⟩ := h1
  split_ands'; exists T1, q1; obtain ⟨-, T2, q2', q3, _⟩ := h2; exists q3
  casesm* _ ∧ _; rename_i h2 h2' _; simp [h2] at h2'; obtain ⟨rfl, rfl⟩ := h2'
  split_ands'; trans; assumption'; c_extend; simp [Bool.le_iff_imp]
  contrapose; intro; c_free; assumption

lemma on_telescope:
  telescope G →
  ctx_grow G G' gs →
  telescope G' :=
by
  intros T C; intros x _ _ _ h; obtain C | C := C.2 x
  apply T; rwa [C]; obtain ⟨-, _, _, _, -, _, h0, h'⟩ := C
  simp [h] at h'; obtain ⟨rfl, rfl, rfl⟩ := h'; specialize T h0; split_ands''
  c_extend;

lemma set (x: ℕ):
  G[x]? = some (T, q, .self) →
  G' = G.set x (T, q', .self) →
  closed_ql true 0 x q' →
  ✦ ∉ q' \ q →
  q ⊆ q' →
  x ∈ gs →
  ctx_grow G G' gs :=
by
  intros Gx G'x Cq' Fr QQ Hx; simp [ctx_grow, G'x]; intro i
  have := (List.getElem?_eq_some.1 Gx).1; simp at Fr
  if h: i = x then
    subst i; right; simp [Gx, Hx, this]; exists T, q, q'; simp [QQ]
    by_cases h: ✦ ∈ q <;> simp [h] at Fr ⊢; assumption
    apply closedql_fr_tighten; assumption'
  else
    left; rw [List.getElem?_set_ne]; omega

end ctx_grow
