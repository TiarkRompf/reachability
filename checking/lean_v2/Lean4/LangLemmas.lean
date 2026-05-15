import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image
import Lean4.LangDefs
import Aesop

syntax "split_ands'" : tactic
syntax "split_ands''" : tactic
macro_rules
| `(tactic| split_ands) => `(tactic| constructorm* _ ∧ _)
| `(tactic| split_ands') => `(tactic| constructorm* _ ∧ _ <;> try trivial)
| `(tactic| split_ands'') => `(tactic| casesm* _ ∧ _; split_ands')

attribute [cnf] and_or_left or_and_right and_assoc or_assoc
attribute [simp] List.getElem?_append_left List.getElem?_append_right
  List.getElem?_cons_zero List.getElem?_eq_none
attribute [-simp] getElem?_pos Finset.singleton_union

lemma Nat.le_of_forall_lt {a b: ℕ}:
  (∀x < a, x < b) ↔ a ≤ b :=
by
  constructor <;> intro H
  · apply Nat.le_of_not_lt; intro h; specialize H _ h; omega
  · omega

def List.getElem?_eq_some' {l: List α} {n: ℕ} (h: l[n]? = some a) := (List.getElem?_eq_some_iff.1 h).1

@[simp] lemma List.set_getElem?_self {as: List α} {i: Nat} {v: α} (h: as[i]? = some v):
  as.set i v = as :=
by
  ext i' v'; revert v'; simp [List.getElem?_set]; split; swap; simp
  subst_vars; simp [h]; apply List.getElem?_eq_some'; assumption

namespace Reachability

-- qualifiers

@[simp]
lemma Finset.mem_ite [Decidable b] {x y: Finset α}:
  i ∈ (if b then x else y) ↔ b ∧ i ∈ x ∨ ¬b ∧ i ∈ y :=
by aesop

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

@[simp] lemma qdom_mem_fr: ✦ ∈ qdom fr bvs fvs ↔ fr = true :=
  by simp [qdom]
@[simp] lemma qdom_mem_bv: #x ∈ qdom fr bvs fvs ↔ x < bvs :=
  by simp [qdom]
@[simp] lemma qdom_mem_fv: %x ∈ qdom fr bvs fvs ↔ x < fvs :=
  by simp [qdom]

def closed_ql.hfvs (H: closed_ql r b f q):
  closed_ql.fvs f q :=
by
  intros x Q; specialize H Q; simpa using H

@[simp]
lemma closedql_empty:
  closed_ql fr bvs fvs ∅ :=
by
  simp [sets]

lemma closedql_singleton:
  closed_ql fr bvs fvs {x} ↔ x ∈ qdom fr bvs fvs :=
by
  simp [sets]

-- bv shiftings

@[simp] lemma bvshift_bv {n: ℕ}: #x + n = #(x + n) :=
  by simp [bvShift]
@[simp] lemma bvshift_fv {n: ℕ}: %x + n = %x :=
  by simp [bvShift]
@[simp] lemma bvshift_fr {n: ℕ}: ✦ + n = ✦ :=
  by simp [bvShift]
@[simp] lemma bvShift_eq_fr {a: id} {n: ℕ}: a + n = ✦ ↔ a = ✦ :=
  by cases a <;> simp
@[simp] lemma bvShift_eq_fr' {a: id} {n: ℕ}: ✦ = a + n ↔ a = ✦ :=
  by rw [Eq.comm]; simp
@[simp] lemma bvShift_eq_bv: a + n = #x ↔ ∃ m, a = #m ∧ m + n = x :=
  by cases a <;> simp
@[simp] lemma bvShift_eq_bv': #x = a + n ↔ ∃ m, a = #m ∧ m + n = x :=
  by rw [Eq.comm]; simp
@[simp] lemma bvShift_eq_fv {a: id} {n m: ℕ}: a + n = %m ↔ a = %m :=
  by cases a <;> simp

@[simp] lemma bvShift_assoc {x: id} {n1 n2: ℕ}:
  x + n1 + n2 = x + (n1 + n2) :=
by
  cases x <;> simp; omega

@[simp] lemma bvShift_add0 {x: id}: x + 0 = x :=
  by cases x <;> simp

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
  ext i; simp [bvsShift, subst]; aesop

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
  induction T generalizing x f <;> aesop (simp_config := {autoUnfold := true})

-- closedness extension

class ClosedExtend (α₁: outParam (Bool → ℕ → ℕ → Prop)) (α₂: outParam (Bool → Prop)) (α₃ α₄: outParam (ℕ → Prop)) (β: Prop) where
  c_extend: α₁ fr bv fv → α₂ fr → α₃ bv → α₄ fv → β

export ClosedExtend (c_extend)
syntax "c_extend" term : tactic
syntax "c_extend": tactic
macro_rules
| `(tactic| c_extend $e) => `(tactic| (apply c_extend $e <;> first | exact false | simp | skip))
| `(tactic| c_extend) => `(tactic| c_extend (by assumption))

lemma closedql_extend:
  closed_ql fr bvs fvs q →
  fr ≤ fr' →
  bvs ≤ bvs' →
  fvs ≤ fvs' →
  closed_ql fr' bvs' fvs' q :=
by
  intros H _ _ _; simp [closed_ql] at *; trans; apply H; aesop

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
    intros _ _ _ h; intros; contrapose h
    apply closedql_extend (q := {x}); simpa [closed_ql]; assumption'; simp

lemma closedty_extend:
  closed_ty mb mf T →
  mb ≤ mb' →
  mf ≤ mf' →
  closed_ty mb' mf' T :=
by
  intros H1 H2 H3; fun_induction closed_ty mb mf T generalizing mb' mf'
  next => simpa
  next => simpa
  next => simpa
  next IH1 IH2 =>
    simp!; split_ands''
    aesop; aesop; c_extend; assumption'; c_extend; assumption'
  next IH1 IH2 =>
    simp!; split_ands''
    aesop; aesop; c_extend; assumption'; c_extend; assumption'
  next =>
    simp!; apply closedql_extend (q := {_})
    simpa [sets]; assumption'; all_goals simp
  next IH1 IH2 =>
    simp!; split_ands''
    aesop; aesop; c_extend; assumption'; c_extend; assumption'
  next IH1 IH2 =>
    simp!; split_ands''
    aesop; aesop; c_extend; assumption'; c_extend; assumption'
  next IH => simp!; aesop

instance: ClosedExtend (fun _ b f => closed_ty b f T) (fun _ => True) (· ≤ mb') (· ≤ mf')
    (closed_ty mb' mf' T) where
  c_extend := by
    intros; apply closedty_extend; assumption'

-- free from closedness

class ClosedFree (α: outParam (Bool → ℕ → ℕ → Prop)) (β: outParam (Bool → ℕ → ℕ → Prop)) (γ: Prop) where
  c_free: α fr bv fv → β fr bv fv → γ

export ClosedFree (c_free)
syntax "c_free" term : tactic
syntax "c_free": tactic
macro_rules
| `(tactic| c_free $e) => `(tactic| apply c_free $e <;> first | exact false | simp | skip)
| `(tactic| c_free) => `(tactic| c_free (by assumption))

lemma closedql_free:
  closed_ql fr bv fv q → x ∉ qdom fr bv fv → x ∉ q :=
by
  intros h1 h2 h; specialize h1 h; contradiction

instance: ClosedFree (closed_ql · · · q) (x ∉ qdom · · ·)
    (x ∉ q) where
  c_free := closedql_free

instance {x: id}: ClosedFree (closed_ql · · · q) (∀(n: ℕ), x+n ∉ qdom · · ·)
    (∀(n: ℕ), x+n ∉ q) where
  c_free := by intros; apply c_free; assumption; tauto

lemma closedty_free:
  closed_ty bv fv T →
  x ∉ qdom true bv fv →
  occurs .none T x :=
by
  intros H1 H2; induction T generalizing bv x <;> simp! at H1 ⊢
  case TRef2 T1 q1 T2 q2 IH1 IH2 =>
    have: x ∉ qdom false bv fv := by
      contrapose! H2; revert H2 x; change _ ⊆ (_: ql); simp
    split_ands''; aesop; c_free; assumption; aesop; c_free; assumption
  case TFun T1 q1 T2 q2 IH1 IH2 =>
    split_ands''; aesop; c_free; assumption; aesop; c_free; assumption
  case TVar =>
    rintro rfl; revert H1
    eapply closedql_free; assumption'; simp [closed_ql]
  case TAll T1 q1 T2 q2 IH1 IH2 =>
    split_ands''; aesop; c_free; assumption; aesop; c_free; assumption
  case TProd T1 q1 T2 q2 IH1 IH2 =>
    have: x ∉ qdom false bv fv := by clear *- H2; aesop (add simp qdom)
    split_ands''; aesop; c_free; assumption; aesop; c_free; assumption
  case TList T IH => aesop

instance: ClosedFree (fun _ b f => closed_ty b f T) (fun _ b f => x ∉ qdom true b f)
    (occurs f T x) where
  c_free h1 h2 := (closedty_free h1 h2) |> occurs_none

instance {x: id}: ClosedFree (fun _ b f => closed_ty b f T) (fun _ b f => ∀(n: ℕ), x+n ∉ qdom true b f)
    (∀(n: ℕ), occurs f T (x+n)) where
  c_free h1 h2 := by intros; apply c_free; assumption; tauto; exact false

-- closedness tighten

lemma closedql_fr_tighten:
  ✦ ∉ q →
  closed_ql true bv fv q →
  closed_ql false bv fv q :=
by
  intros h1 h2; intro a h; specialize h2 h
  aesop (add safe cases id)

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
  case TRef2 =>
    aesop (add safe closedql_bv_tighten)
  case TFun =>
    aesop (add safe closedql_bv_tighten)
  case TVar x =>
    apply closedql_bv_tighten (q := {x}); simpa; simpa [closed_ql]; simp
  case TAll =>
    aesop (add safe closedql_bv_tighten)
  case TProd =>
    aesop (add safe closedql_bv_tighten)
  case TList =>
    aesop (add safe closedql_bv_tighten)

lemma closedty_fv_tighten:
  occurs .none T %fv →
  closed_ty bv (fv+1) T →
  closed_ty bv fv T :=
by
  intros H1 H2; induction T generalizing bv <;> simp! at H1 H2 ⊢
  case TRef2 =>
    aesop (add safe closedql_fv_tighten)
  case TFun =>
    aesop (add safe closedql_fv_tighten)
  case TVar x =>
    apply closedql_fv_tighten (q := {x}); simpa; simpa [closed_ql]; simp
  case TAll =>
    aesop (add safe closedql_fv_tighten)
  case TProd =>
    aesop (add safe closedql_fv_tighten)
  case TList =>
    aesop (add safe closedql_fv_tighten)

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
    have: q = q \ {%i} ∪ {%i} := by
      ext x; by_cases h: x = %i <;> simp [h]; assumption
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
  ext; aesop (add simp subst)

lemma Finset.inter_subst {p q q1: ql}:
  p ∩ [x ↦ q1] q = (p ∩ q) \ {x} ∪ ?[x ∈ q] p ∩ q1 :=
by
  ext; aesop (add simp subst)

@[simp]
lemma occurs_open {n n' x: id}:
  occurs f ([n ↦ n'] T) x ↔ (x ≠ n → occurs f T x) ∧ (x = n' → occurs f T n) :=
by
  induction T generalizing f x n n' <;> simp!
  case TRef2 T1 q1 T2 q2 IH1 IH2 =>
    simp [IH1, IH2]; simp [subst]; clear IH1 IH2
    by_cases x = n <;> by_cases x = n' <;> aesop
  case TFun T1 q1 T2 q2 IH1 IH2 =>
    simp [IH1, IH2]; simp [subst]; clear IH1 IH2
    by_cases x = n <;> by_cases x = n' <;> aesop
  case TVar a =>
    simp [subst]; split; subst n; tauto
    rename_i h; simp [h]; by_cases x = n; subst x; tauto; tauto
  case TAll T1 q1 T2 q2 IH1 IH2 =>
    simp [IH1, IH2]; simp [subst]; clear IH1 IH2
    by_cases x = n <;> by_cases x = n' <;> aesop
  case TProd T1 q1 T2 q2 IH1 IH2 =>
    simp [IH1, IH2]; simp [subst]; clear IH1 IH2
    by_cases x = n <;> by_cases x = n' <;> aesop
  case TList T IH => simp [IH]

lemma occurs_subst {t: ty} {q : ql} {x: id}
  (h1: ∀{a: ℕ}, x + a ∉ q) (h3: ∀{a: ℕ}, occurs .none t (x+a)):
  occurs f ([n ↦ (t, q)] T) x ↔ (x ≠ n → occurs f T x) :=
by
  induction T generalizing f x n q <;> simp!
  case TRef2 T1 q1 T2 q2 IH1 IH2 =>
    simp [IH1, IH2, h1, h3]; simp [subst, h1]
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
  case TProd T1 q1 T2 q2 IH1 IH2 =>
    simp [IH1, IH2, h1, h3]; simp [subst, h1]
    by_cases h: x = n <;> simp [h]
  case TList T IH => simp [IH, h1, h3]

lemma closedql_subst (h1: closed_ql fr mb mf q') (h2: x ∈ qdom fr mb mf):
  closed_ql fr mb mf [x ↦ q'] q ↔ closed_ql fr mb mf q :=
by
  simp [subst, sets]; constructor
  intros h x1 _; by_cases x1 = x; subst x1; assumption; tauto; tauto

lemma closedty_open (h1: x' ∈ qdom false mb mf) (h2: x ∈ qdom false mb mf):
  closed_ty mb mf [x ↦ x'] T ↔ closed_ty mb mf T :=
by
  induction T generalizing x x' mb <;> simp!
  case TRef2 T1 q1 T2 q2 IH1 IH2 =>
    congrm ?_ ∧ ?_ ∧ ?_ ∧ ?_ ∧ ?_ ∧ _ ∧ _
    · rw [IH1]; simpa; simpa
    · rw [IH2]; simpa; simpa
    · rw [closedql_subst]; simp [closed_ql]; c_extend; simp; c_extend;
    · rw [closedql_subst]; simp [closed_ql]; c_extend; simp; c_extend;
    · simp [subst]
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
  case TProd T1 q1 T2 q2 IH1 IH2 =>
    congrm ?_ ∧ ?_ ∧ ?_ ∧ ?_ ∧ _ ∧ _
    · rw [IH1]; simpa; simpa
    · rw [IH2]; simpa; simpa
    · rw [closedql_subst]; simp [closed_ql]; c_extend; simp; c_extend;
    · rw [closedql_subst]; simp [closed_ql]; c_extend; simp; c_extend;
  case TList T IH =>
    rw [IH]; simp; simpa; simpa

lemma closedty_subst {t: ty}
  (h1: closed_ql false 0 mf q)
  (h3: closed_ty 0 mf t) (h2: x ∈ qdom false mb mf):
  closed_ty mb mf [x ↦ (t, q)] T ↔ closed_ty mb mf T :=
by
  induction T generalizing x q mb <;> simp! at h1 ⊢
  case TRef2 T1 q1 T2 q2 IH1 IH2 =>
    congrm ?_ ∧ ?_ ∧ ?_ ∧ ?_ ∧ ?_ ∧ ?_ ∧ ?_
    · rwa [IH1]; simpa
    · rwa [IH2]; simpa
    · rw [closedql_subst]; c_extend; simp; c_extend;
    · rw [closedql_subst]; c_extend; simp; c_extend;
    · simp [subst]; intros; c_free;
    · rw [occurs_subst]; simp; c_free; c_free;
    · rw [occurs_subst]; simp; c_free; c_free;
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
  case TProd T1 q1 T2 q2 IH1 IH2 =>
    congrm ?_ ∧ ?_ ∧ ?_ ∧ ?_ ∧ ?_ ∧ ?_
    · rwa [IH1]; simpa
    · rwa [IH2]; simpa
    · rw [closedql_subst]; c_extend; simp; c_extend;
    · rw [closedql_subst]; c_extend; simp; c_extend;
    · rw [occurs_subst]; simp; c_free; c_free;
    · rw [occurs_subst]; simp; c_free; c_free;
  case TList T IH =>
    rw [IH, occurs_subst]; simp; c_free; c_free; simpa; simpa

lemma ty.open_free {x x': id}:
  occurs .none T x →
  [x ↦ x'] T = T :=
by
  intro h; induction T generalizing x x' <;> simp <;> simp! at h
  case TRef2 IH1 IH2 =>
    obtain ⟨h1, h2, h3, h4⟩ := h
    simp [IH1 h1, IH2 h3]; clear IH1 IH2; aesop (add simp subst)
  case TFun IH1 IH2 =>
    obtain ⟨h1, h2, h3, h4⟩ := h
    simp [IH1 h1, IH2 h3]; clear IH1 IH2; aesop (add simp subst)
  case TVar =>
    simp [subst]; tauto
  case TAll IH1 IH2 =>
    obtain ⟨h1, h2, h3, h4⟩ := h
    simp [IH1 h1, IH2 h3]; clear IH1 IH2; aesop (add simp subst)
  case TProd IH1 IH2 =>
    obtain ⟨h1, h2, h3, h4⟩ := h
    simp [IH1 h1, IH2 h3]; clear IH1 IH2; aesop (add simp subst)
  case TList IH => simp [IH h]

lemma ty.subst_freeq {x: id} {t: ty} {q: ql}:
  occurs .noneq T x →
  [x ↦ (t, q)] T = [x ↦ (t, (∅: ql))] T :=
by
  intro h; induction T generalizing x t q <;> simp <;> simp! at h
  case TRef2 IH1 IH2 =>
    obtain ⟨h1, h2, h3, h4⟩ := h
    simp [IH1 h1, IH2 h3]; clear IH1 IH2; aesop (add simp subst)
  case TFun IH1 IH2 =>
    obtain ⟨h1, h2, h3, h4⟩ := h
    simp [IH1 h1, IH2 h3]; clear IH1 IH2; aesop (add simp subst)
  case TAll IH1 IH2 =>
    obtain ⟨h1, h2, h3, h4⟩ := h
    simp [IH1 h1, IH2 h3]; clear IH1 IH2; aesop (add simp subst)
  case TProd IH1 IH2 =>
    obtain ⟨h1, h2, h3, h4⟩ := h
    simp [IH1 h1, IH2 h3]; clear IH1 IH2; aesop (add simp subst)
  case TList IH => simp [IH h]

lemma ty.subst_freefr {x: id} {t: ty} {q: ql}:
  (✦ ∈ q → occurs .noneq T x) →
  [x ↦ (t, q)] T = [x ↦ (t, if ✦ ∈ q then ∅ else q)] T :=
by
  aesop (add simp ty.subst_freeq)

lemma ty.subst_free {x: id} {t: ty} {q: ql}:
  occurs .none T x →
  [x ↦ (t, q)] T = T :=
by
  intro h; induction T generalizing x t q <;> simp <;> simp! at h
  case TRef2 IH1 IH2 =>
    obtain ⟨h1, h2, h3, h4⟩ := h
    simp [IH1 h1, IH2 h3]; clear IH1 IH2; aesop (add simp subst)
  case TFun IH1 IH2 =>
    obtain ⟨h1, h2, h3, h4⟩ := h
    simp [IH1 h1, IH2 h3]; clear IH1 IH2; aesop (add simp subst)
  case TVar x => simp [h]
  case TAll IH1 IH2 =>
    obtain ⟨h1, h2, h3, h4⟩ := h
    simp [IH1 h1, IH2 h3]; clear IH1 IH2; aesop (add simp subst)
  case TProd IH1 IH2 =>
    obtain ⟨h1, h2, h3, h4⟩ := h
    simp [IH1 h1, IH2 h3]; clear IH1 IH2; aesop (add simp subst)
  case TList IH => simp [IH h]

lemma ty.subst_qchange (x: id) (q': ql) {t: ty} {q: ql}:
  q = q' ∨ occurs .noneq T x →
  [x ↦ (t, q)] T = [x ↦ (t, q')] T :=
by
  aesop (add simp ty.subst_freeq)

@[simp]
lemma ty.subst_open_eq {t: ty}:
  [x ↦ (ty.TVar %n, {%n})] t = [x ↦ %n] t :=
by
  induction t generalizing x <;> simp
  case TRef2 T1 q1 T2 q2 IH1 IH2 =>
    rw [IH1, IH2]; simp
  case TFun T1 q1 T2 q2 IH1 IH2 =>
    rw [IH1, IH2]; simp
  case TVar =>
    simp [subst]; split <;> simp
  case TAll T1 q1 T2 q2 IH1 IH2 =>
    rw [IH1, IH2]; simp
  case TProd T1 q1 T2 q2 IH1 IH2 =>
    rw [IH1, IH2]; simp
  case TList T IH => rw [IH]

lemma ql.subst_self (x: id) (q: ql):
  [x ↦ {x}] q = q :=
by
  ext a; simp [subst]; by_cases h: a = x <;> simp [h]

lemma ql.subst_comm {q q1 q2: ql} (h1: x2 ∉ q1) (h2: x1 ∉ q2) (h3: x1 ≠ x2):
  [x1 ↦ q1] [x2 ↦ q2] q = [x2 ↦ q2] [x1 ↦ q1] q :=
by
  ext i; simp [subst, h1, h2, h3, Eq.comm (a := x2), cnf]; aesop

-- h1 could be: x ≠ a → x ≠ b; don't try to merge it into an ite
lemma ql.subst_comm' {q y: ql} (h1: x ≠ b) (h2: x = a → b ∉ q):
  [a ↦ {b}] [x ↦ y] q = [([a ↦ b] x) ↦ ([a ↦ {b}] y)] [a ↦ {b}] q :=
by
  ext i; simp [subst, cnf]; aesop

lemma ty.open_comm {t: ty} {q1 q2: id} (h1: x2 ≠ q1) (h2: x1 ≠ q2) (h3: x1 ≠ x2):
  [x1 ↦ q1] [x2 ↦ q2] t = [x2 ↦ q2] [x1 ↦ q1] t :=
by
  induction t generalizing x1 x2 q1 q2 <;> simp
  case TRef2 IH1 IH2 => aesop (add simp ql.subst_comm)
  case TFun IH1 IH2 => aesop (add simp ql.subst_comm)
  case TVar => aesop (add simp subst)
  case TAll IH1 IH2 => aesop (add simp ql.subst_comm)
  case TProd IH1 IH2 => aesop (add simp ql.subst_comm)
  case TList IH => aesop (add simp ql.subst_comm)

lemma ty.open_subst_comm {x1 x2 x1': id} {t t2: ty} {q2: ql}
  (h1: x2 ≠ x1') (h2: ∀(n: ℕ), x1 + n ∉ q2) (h2t: ∀(n: ℕ), occurs .none t2 (x1+n)) (h3: x1 ≠ x2):
  [x1 ↦ x1'] [x2 ↦ (t2, q2)] t = [x2 ↦ (t2, q2)] [x1 ↦ x1'] t :=
by
  induction t generalizing x1 x1' x2 t2 q2
  simp; simp; simp
  case TRef2 T1 q1 T2 q2 IH1 IH2 =>
    aesop (add safe ql.subst_comm)
  case TFun T1 q1 T2 q2 IH1 IH2 =>
    aesop (add safe ql.subst_comm)
  case TVar =>
    simp; split; subst_vars; split; rw [ty.open_free]
    convert_to occurs _ _ (x1 + 0); simp
    apply h2t; rename_i h; simp [subst, h3] at h
    aesop (add simp subst)
  case TAll T1 q1 T2 q2 IH1 IH2 =>
    aesop (add safe ql.subst_comm)
  case TProd T1 q1 T2 q2 IH1 IH2 =>
    aesop (add safe ql.subst_comm)
  case TList T IH =>
    aesop (add safe ql.subst_comm)

lemma ql.subst_chain x1 x2 {q q2: ql} (h0: x2 ∉ q):
  [x2 ↦ q2] [x1 ↦ {x2}] q = [x1 ↦ q2] q :=
by
  aesop (add simp subst)

lemma ty.subst_open_chain x1 x2 {t T: ty} {q: ql} (h0: occurs .none T x2):
  [x2 ↦ (t, q)] [x1 ↦ x2] T = [x1 ↦ (t, q)] T :=
by
  induction T generalizing x1 x2 t q <;> simp
  case TRef2 T1 q1 T2 q2 IH1 IH2 =>
    aesop (add safe ql.subst_chain, simp occurs)
  case TFun T1 q1 T2 q2 IH1 IH2 =>
    aesop (add safe ql.subst_chain, simp occurs)
  case TVar x =>
    aesop (add simp subst, simp occurs)
  case TAll T1 q1 T2 q2 IH1 IH2 =>
    aesop (add safe ql.subst_chain, simp occurs)
  case TProd T1 q1 T2 q2 IH1 IH2 =>
    aesop (add safe ql.subst_chain, simp occurs)
  case TList T IH =>
    aesop (add safe ql.subst_chain, simp occurs)

lemma ql.subst_cancel x1 x2 {q: ql} (h0: x2 ∉ q):
  [x2 ↦ {x1}] [x1 ↦ {x2}] q = q :=
by
  ext i; simp [subst, cnf, h0]; constructor
  aesop; intro h; simp [h]; by_cases h: i = x1 <;> aesop

lemma ty.open_cancel {t: ty} (h0: occurs .none t x2):
  [x2 ↦ x1] [x1 ↦ x2] t = t :=
by
  induction t generalizing x1 x2 <;> simp! at h0 ⊢
  case TRef2 IH1 IH2 => simp [IH1, IH2, h0, ql.subst_cancel]
  case TFun IH1 IH2 => simp [IH1, IH2, h0, ql.subst_cancel]
  case TVar => simp [subst]; aesop
  case TAll IH1 IH2 => simp [IH1, IH2, h0, ql.subst_cancel]
  case TProd IH1 IH2 => simp [IH1, IH2, h0, ql.subst_cancel]
  case TList IH => simp [IH, h0]

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

instance: ClosedSubstTighten (closed_ql true bv fv q) (closed_ql false bv fv q1)
    (closed_ql false bv fv [✦ ↦ q1] q) where
  subst_tighten := by
    intro h1 h2; apply closedql_fr_tighten; simp [subst]; intro; c_free;
    rw [closedql_subst]; c_extend; c_extend; simp

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
    (closed_ty 0 fv t ∧ closed_ql false 0 fv q)
    (closed_ty bv fv [#bv ↦ (t, q)] T) where
  subst_tighten := by
    rintro h1 ⟨h2, h3⟩; apply closedty_bv_tighten
    rw [occurs_subst]; simp; c_free; c_free;
    rwa [closedty_subst]; c_extend; assumption; simp

instance {t: ty} {q: ql}: ClosedSubstTighten
    (closed_ty bv (fv+1) T)
    (closed_ty 0 fv t ∧ closed_ql false 0 fv q)
    (closed_ty bv fv [%fv ↦ (t, q)] T) where
  subst_tighten := by
    rintro h1 ⟨h2, h3⟩; apply closedty_fv_tighten
    rw [occurs_subst]; simp; c_free; c_free;
    rwa [closedty_subst]; c_extend; c_extend; simp

syntax "c_subst" : tactic
macro_rules
| `(tactic| c_subst) =>
  `(tactic| repeat1 (apply subst_tighten <;> [skip; try simp! +arith [closedql_singleton]]))

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
  simp [subst, splice]; symm; aesop

@[simp]
lemma ql.splice_singleton {x: id} (n d: ℕ):
  ql.splice {x} n d = {x.splice n d} :=
by
  simp [ql.splice]

@[simp]
lemma ql.splice_subst_comm ⦃x': id⦄ ⦃q: ql⦄:
  ([#x ↦ {x'}] q).splice n δ = [#x ↦ {x'.splice n δ}] q.splice n δ :=
by
  ext a; simp [subst, ql.splice]; aesop

lemma ql.splice_self (h: closed_ql.fvs n q):
  q.splice n δ = q :=
by
  ext a; aesop (add simp ql.splice, simp id.splice, simp closed_ql.fvs)

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
  induction t generalizing x x' <;> aesop (add simp ty.splice)

lemma ty.splice_self (h: closed_ty n' n T):
  T.splice n δ = T :=
by
  induction T generalizing n' <;> simp! at h ⊢
  case TRef2 T1 q1 T2 q2 IH1 IH2 =>
    aesop (add safe ql.splice_self, safe closed_ql.hfvs)
  case TFun T1 q1 T2 q2 IH1 IH2 =>
    aesop (add safe ql.splice_self, safe closed_ql.hfvs)
  case TVar a =>
    aesop (add safe cases id)
  case TAll T1 q1 T2 q2 IH1 IH2 =>
    aesop (add safe ql.splice_self, safe closed_ql.hfvs)
  case TProd T1 q1 T2 q2 IH1 IH2 =>
    aesop (add safe ql.splice_self, safe closed_ql.hfvs)
  case TList T IH => aesop

@[simp]
lemma occurs_bv_splice:
  occurs f (T.splice n d) #x = occurs f T #x :=
by
  induction T generalizing f x <;> simp!
  case TRef2 IH1 IH2 => rw [IH1, IH2]
  case TFun IH1 IH2 => rw [IH1, IH2]
  case TVar a => cases a <;> simp; split <;> simp
  case TAll IH1 IH2 => rw [IH1, IH2]
  case TProd IH1 IH2 => rw [IH1, IH2]
  case TList IH => rw [IH]

lemma closedql_splice (h: closed_ql fr mb mf q) (n d: ℕ):
  closed_ql fr mb (mf + d) (q.splice n d) :=
by
  simp [ql.splice, sets] at *; intro x h1
  specialize h h1; cases x <;> simp at *
  assumption'; split <;> simp <;> omega

lemma closedty_splice (h: closed_ty mb mf T) (n d: ℕ):
  closed_ty mb (mf + d) (T.splice n d) :=
by
  fun_induction closed_ty mb mf T <;> simp!
  next => aesop (add safe closedql_splice)
  next => aesop (add safe closedql_splice)
  next x => aesop (add safe cases id, safe (by omega))
  next => aesop (add safe closedql_splice)
  next => aesop (add safe closedql_splice)
  next => aesop (add safe closedql_splice)

-- measurement

@[simp]
lemma subst_preserves_tysize {x: id} {T t: ty} {q: ql} (h: ty_size t = 1):
  ty_size [x ↦ (t, q)] T = ty_size T :=
by
  induction T generalizing x <;> aesop (add simp ty_size)

lemma ty.induct' (motive: ty → Prop)
  (TTop: motive .TTop)
  (TUnit: motive .TUnit)
  (TNat: motive .TNat)
  (TRef2: ∀ T1 q1 T2 q2,
      (∀ T1', ty_size T1 = ty_size T1' → motive T1') →
      (∀ T2', ty_size T2 = ty_size T2' → motive T2') →
      motive (.TRef2 T1 q1 T2 q2))
  (TFun: ∀ T1 q1 T2 q2,
      (∀ T1', ty_size T1 = ty_size T1' → motive T1') →
      (∀ T2', ty_size T2 = ty_size T2' → motive T2') →
      motive (.TFun T1 q1 T2 q2))
  (TVar: ∀ x, motive (.TVar x))
  (TAll: ∀ T1 q1 T2 q2,
      (∀ T1', ty_size T1 = ty_size T1' → motive T1') →
      (∀ T2', ty_size T2 = ty_size T2' → motive T2') →
      motive (.TAll T1 q1 T2 q2))
  (TProd: ∀ T1 q1 T2 q2,
      (∀ T1', ty_size T1 = ty_size T1' → motive T1') →
      (∀ T2', ty_size T2 = ty_size T2' → motive T2') →
      motive (.TProd T1 q1 T2 q2))
  (TList: ∀ T,
      (∀ T', ty_size T = ty_size T' → motive T') →
      motive (.TList T))
  t: motive t :=
by
  generalize h: ty_size t = n; replace h: ty_size t ≤ n := by omega
  induction n generalizing t <;> cases t <;> simp! at h; assumption'
  next IH _ _ _ _ => apply TRef2 <;> intros _ h <;> apply IH <;> omega
  next IH _ _ _ _ => apply TFun <;> intros _ h <;> apply IH <;> omega
  next => apply TVar
  next IH _ _ _ _ => apply TAll <;> intros _ h <;> apply IH <;> omega
  next IH _ _ _ _ => apply TProd <;> intros _ h <;> apply IH <;> omega
  next IH _ => apply TList; intros _ h; apply IH; omega

lemma subsize_splice (C: closed_ty 0 ‖G ++ G'‖ T):
  sub_size' (G ++ G0 ++ G') (T.splice ‖G‖ ‖G0‖) = sub_size' (G ++ G') T :=
by
  induction T using ty.induct' generalizing G'
  all_goals simp! [sub_size', -List.append_assoc]
  case TRef2 ih1 ih2 =>
    simp! at C; obtain ⟨_, _, -⟩ := C; conv => right; simp
    rw [←ih1, ←ih2]; simp; split; exfalso; omega
    congr 4; simp; omega; omega; simp
    simp; c_subst; c_extend; simp; simp; c_subst; c_extend;
  case TVar x =>
    cases x <;> simp [sub_size']; split <;> rename_i h
    simp [sub_size', h, List.getElem?_append_left]
    simp! at C; simp at h; simp [sub_size']
    repeat rw [List.getElem?_append_right]
    congr 2; omega; assumption; omega; omega
  case TFun ih1 ih2 =>
    simp! at C; obtain ⟨_, _, -⟩ := C; conv => right; simp
    rw [←ih1, ←ih2]; simp; split; exfalso; omega; split; exfalso; omega
    congr 4; simp; omega; omega; simp; omega; simp
    simp; c_subst; c_extend; simp; simp; c_subst; c_extend;
  case TAll ih1 ih2 =>
    simp! at C; obtain ⟨_, _, -⟩ := C; conv => right; simp
    rw [←ih2, ←ih1]; simp; split; exfalso; omega; split; exfalso; omega
    congr 3; congr 6; omega; omega; simp; omega; simp
    simp; c_subst; c_extend; simp; c_subst; c_extend;
  case TProd ih1 ih2 =>
    simp! at C; obtain ⟨_, _, -⟩ := C; conv => right; simp
    rw [←ih1, ←ih2]; simp; split; exfalso; omega
    congr 3; congr 2; omega; simp; omega
    simp; c_subst; c_extend; simp; c_subst; c_extend;
  case TList ih =>
    simp! at C; obtain ⟨_, _⟩ := C; conv => right; simp
    rw [←ih]; simp; split; exfalso; omega
    congr 3; omega; simp; c_subst; c_extend;

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
  case TRef2 ih1 ih2 =>
    (repeat rw [ty.open_subst_comm]); rw [ih1, ih2]
    simp; simp; omega; c_extend; simp; simp; omega; c_extend;
    simp; omega; c_free; simp!; simp
    simp; omega; c_free; simp!; simp
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
  case TProd ih1 ih2 =>
    (repeat rw [ty.open_subst_comm]); rw [ih1, ih2]
    simp; simp; omega; c_extend; simp; simp; omega; c_extend;
    simp; omega; c_free; simp!; simp
    simp; omega; c_free; simp!; simp
  case TList ih =>
    (repeat rw [ty.open_subst_comm]); rw [ih]
    simp; simp; omega; c_extend; simp; omega; c_free; simp!; simp

@[simp]
lemma tenv.sub_size_length {G: tenv}:
  ‖G.sub_sizes‖ = ‖G‖ :=
by
  simp [tenv.sub_sizes]; induction G using List.reverseRecOn; simp; simpa

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
  intro H; induction G using List.reverseRecOn; simp at H
  next G a H1 =>
    obtain ⟨T', q', bn⟩ := a; simp; generalize h: ite (bn = .tvar) _ _ = a
    simp [List.getElem?_append] at H; split at H <;> rename_i hx
    · rw [List.getElem?_append_left, List.take_append_of_le_length]
      exact H1 H; simp; omega; simpa
    · have := (List.getElem?_eq_some_iff.1 H).1; simp at this
      replace hx: x = ‖G‖ := (by omega); clear this H1; subst x a; simp at H ⊢
      obtain ⟨rfl, rfl, rfl⟩ := H; simp

-- telescope, transitive closures

lemma telescope_shrink:
  telescope (G ++ G') → telescope G :=
by
  intro T; simp only [telescope] at T ⊢; intros _ _ _ _ h
  apply T; have := List.getElem?_eq_some' h; simpa [this]

lemma telescope_extend (h1: closed_ty 0 ‖G‖ T) (h: closed_ql true 0 ‖G‖ q) (H: telescope G):
  telescope (G ++ [(T, q, bn)]) :=
by
  simp only [telescope] at *; intros x _ _ _ H1
  have := List.getElem?_eq_some' H1; simp at this
  by_cases x < ‖G‖; apply H; aesop; have: x = ‖G‖ := (by omega); aesop

@[simp]
lemma vars_trans_if [Decidable a]:
  vars_trans G (if a then b else c) = if a then vars_trans G b else vars_trans G c :=
by
  aesop

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
  rw [←vars_trans.eq_1]; aesop

lemma vars_trans_one' (h: x ≥ ‖G‖):
  vars_trans G {%x} = {%x} :=
by
  induction G using List.reverseRecOn <;> simp [vars_trans]
  rw [←vars_trans.eq_1]; aesop (add safe (by omega))

@[simp]
lemma vars_trans_one (h': G[x]? = some e) (T: telescope G):
  vars_trans G {%x} = {%x} ∪ vars_trans G e.2.1 :=
by
  induction G using List.reverseRecOn generalizing e <;> simp [vars_trans]
  simp at h'; rw [←vars_trans.eq_1]; rename_i G _ IH
  if h: ‖G‖ = x then
    aesop (add simp vars_trans_one')
  else
    have h := List.getElem?_eq_some' h'; simp at h; have: x < ‖G‖ := by omega
    simp [this] at h'; clear h; replace h: ‖G‖ ≠ x := (by omega); simp [h]
    apply telescope_shrink at T; rw [IH]; assumption'
    replace T := (T h').2; simp [sets] at T; split
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
  next IH => simp [vars_trans]; simp [←vars_trans.eq_1]; trans; apply IH; simp

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
    if bn = .self ∧ ‖G‖ ∈ gs then
      q ⊆ q' ∧ closed_ql false 0 ‖G‖ (q' \ q)
    else q = q' :=
by
  intro h; generalize g1: G'.splitAt ‖G‖ = G1; simp at g1
  have: G1.1 ++ G1.2 = G' := by subst G1; simp
  have: (List.drop ‖G‖ G').length = 1 := by simp [←h.1]
  rw [List.length_eq_one_iff] at this; obtain ⟨⟨T', q', bn'⟩, this⟩ := this
  rw [this] at g1; clear this; generalize List.take _ _ = G0 at g1
  subst G1; simp at this; subst G'; have := h.2 ‖G‖; simp at this
  have L := h.1; simp at L; simp [L] at this; exists G0, q'; simp
  obtain ⟨rfl, rfl, rfl⟩ | h := this; simp
  obtain ⟨h1, h2, C, rfl, rfl, rfl⟩ := h
  simp [L, h1, h2]; by_cases h: ✦ ∈ q <;> simp [h] at C
  apply closedql_fr_tighten; simp [h]
  all_goals apply Finset.Subset.trans (by simp) C

lemma induct (motive: ∀⦃G G'⦄, ctx_grow G G' gs → Prop)
  (case1: ∀(h: ctx_grow [] [] gs), motive h)
  (case2: ∀⦃G a G' a'⦄ (h: ctx_grow (G ++ [a]) (G' ++ [a']) gs)
    (_: ∀ (h1: ctx_grow G G' gs), motive h1), motive h)
  (h: ctx_grow G G' gs): motive h :=
by
  induction G using List.reverseRecOn generalizing G'
  next => have := h.1.symm; aesop
  next G' a' IH => obtain ⟨G'', q', this, -⟩ := h.inversion; aesop

lemma append:
  ctx_grow G G' gs →
  ctx_grow (G++g) (G'++g) gs :=
by
  intros H; simp [ctx_grow] at *; obtain ⟨H1, H2⟩ := H; split_ands'
  intro i; by_cases i < ‖G‖ <;> aesop

lemma shrink:
  ctx_grow (G++g) (G'++g') gs →
  ‖g‖ = ‖g'‖ →
  ctx_grow G G' gs :=
by
  intro H H1; simp [ctx_grow] at *; simp [H1] at H; split_ands''
  intro i; rename_i H; specialize H i; by_cases i < ‖G‖ <;> aesop

lemma gs_shrink:
  ctx_grow G G' (gs ∪ {‖G‖}) →
  ctx_grow G G' gs :=
by
  intro CG; simp [ctx_grow] at *; obtain ⟨h1, h2⟩ := CG
  simp [h1]; intro i; specialize h2 i; aesop

lemma inversion2:
  ctx_grow (G ++ [(T1, q1, .self), (T2, q2, bn2)]) G' gs → bn2 ≠ .self →
  ∃ G'' q1', G' = G'' ++ [(T1, q1', .self), (T2, q2, bn2)] ∧ q1 ⊆ q1' ∧
    (q1 = ∅ → closed_ql false 0 ‖G‖ q1') ∧ (‖G‖ ∉ gs → q1 = q1') :=
by
  intro CG h; rw [List.append_cons] at CG
  have := CG.inversion; simp [h] at this; obtain ⟨G'1, _, rfl, -, -, rfl⟩ := this
  have := (CG.shrink rfl).inversion; simp at this; obtain ⟨G', q1', rfl, h⟩ := this
  exists G', q1'; simp; split_ands'; rotate_right; aesop; aesop
  rintro rfl; split at h; simpa using h; subst q1'; simp [sets]

@[deprecated "unused" (since := "2025-01-01")]
lemma gs_widen:
  ctx_grow G G' gs1 →
  gs1 ⊆ gs2 →
  ctx_grow G G' gs2 :=
by
  intros h1 h2; simp [ctx_grow] at *; simp [h1.1]; intro i
  replace h1 := h1.2 i; aesop

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
  intros T C; intros x _ _ _ h; obtain C | C := C.2 x; apply T; rwa [C]
  obtain ⟨-, _, _, _, -, _, h0, h'⟩ := C; simp [h] at h'
  obtain ⟨rfl, rfl, rfl⟩ := h'; specialize T h0; split_ands''; c_extend;

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
  have := List.getElem?_eq_some' Gx; simp at Fr
  if h: i = x then
    subst i; right; simp [Gx, Hx, this, QQ]
    by_cases h: ✦ ∈ q <;> simp [h] at Fr ⊢; assumption
    apply closedql_fr_tighten; assumption'
  else
    simp [(Ne.intro h).symm]

lemma on_subsize (h: ctx_grow G1 G2 gs):
  sub_size G2 T = sub_size G1 T :=
by
  simp [sub_size]; congr 1
  induction h using ctx_grow.induct; simp
  next G' _ cg ih =>
    simp [cg.shrink, ih]; have := cg.2 ‖G'‖; have := cg.1; aesop

end ctx_grow
