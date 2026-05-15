import Lean4.LangLemmas
import Lean4.LRDefs
import Aesop

attribute [-simp] Set.setOf_subset_setOf Set.subset_inter_iff Set.union_subset_iff
attribute [-simp] getElem?_pos Finset.singleton_union Finset.union_singleton

namespace Reachability
open locs_locs_stty

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
  · apply Finset.union_subset; assumption'
  · apply Finset.union_subset; assumption'
  · gcongr

theorem sem_qtp_var:
  G[x]? = some (Tx, qx, bn) →
  ✦ ∉ qx →
  sem_qtp G {%x} qx :=
by
  intros H Qx _ _ _ _ WFE; obtain ⟨v, vt, ls, -, H1, _, _, -, -, _, _⟩ := WFE.byG H
  have := List.getElem?_eq_some' H; simp [Qx, closed_ql] at *; split_ands'
  · trans; assumption; simp; omega
  · conv => left; simp [vars_locs, var_locs, H1]
    assumption

theorem sem_qtp_self:
  G[x]? = some (Tx, qx, .self) →
  sem_qtp G (qx \ {✦}) {%x} :=
by
  intros H _ _ _ _ WFE; obtain ⟨v, vt, ls, -, H1, _, _, -, -, _, _⟩ := WFE.byG H
  have := List.getElem?_eq_some' H; simp [closed_ql] at *; split_ands'
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

theorem sem_unit:
  sem_type G .tunit .TUnit p ∅ :=
by
  dsimp; introv _ ST
  exists S, M, .vnat 0, ∅; split_ands'
  · exists 1; intros n _; cases n; contradiction
    simp!; trivial
  · simp [st_chain, sets]
  · simp [store_effect]
  · simp [val_type]
  · simp

theorem sem_nat:
  sem_type G (.tnat n) .TNat p ∅ :=
by
  dsimp; introv _ ST
  exists S, M, .vnat n, ∅; split_ands'
  · exists 1; intros n _; cases n; contradiction
    simp!; trivial
  · simp [st_chain, sets]
  · simp [store_effect]
  · simp [val_type]
  · simp

theorem sem_add:
  sem_type G t1 .TNat p q1 →
  sem_type G t2 .TNat p q2 →
  sem_type G (.tadd t1 t2) .TNat p ∅ :=
by
  intro H1 H2; simp; introv WFE ST
  obtain ⟨S1, M1, v1, ls1, EV1, SC1, ST1, SE1, VT1, VQ1, -⟩ := H1 WFE ST
  cases v1 <;> simp only [val_type] at VT1; rename_i n1
  apply envt_store_change at WFE; specialize WFE _
  apply stchain_tighten; assumption; apply lls_closed'; assumption
  apply env_type_store_wf; assumption
  obtain ⟨S2, M2, v2, ls2, EV2, SC2, ST2, SE2, VT2, VQ2, -⟩ := H2 WFE ST1
  cases v2 <;> simp only [val_type] at VT2; rename_i n2
  exists S2, M2, .vnat (n1 + n2); split_ands'
  · obtain ⟨d1, EV1⟩ := EV1; obtain ⟨d2, EV2⟩ := EV2
    exists 1+d1+d2; intros n _; cases n; contradiction; simp! [bind]
    rw [EV1]; simp!; rw [EV2]; simp! [pure, Except.pure]; omega; omega
  · apply stchain_tighten; apply stchain_chain; assumption'
    clear *- SC1; simp [sets, st_chain] at *; omega
  · apply se_trans; assumption'
  · simp [val_type]

theorem sem_mul:
  sem_type G t1 .TNat p q1 →
  sem_type G t2 .TNat p q2 →
  sem_type G (.tmul t1 t2) .TNat p ∅ :=
by
  intro H1 H2; simp; introv WFE ST
  obtain ⟨S1, M1, v1, ls1, EV1, SC1, ST1, SE1, VT1, VQ1, -⟩ := H1 WFE ST
  cases v1 <;> simp only [val_type] at VT1; rename_i n1
  apply envt_store_change at WFE; specialize WFE _
  apply stchain_tighten; assumption; apply lls_closed'; assumption
  apply env_type_store_wf; assumption
  obtain ⟨S2, M2, v2, ls2, EV2, SC2, ST2, SE2, VT2, VQ2, -⟩ := H2 WFE ST1
  cases v2 <;> simp only [val_type] at VT2; rename_i n2
  exists S2, M2, .vnat (n1 * n2); split_ands'
  · obtain ⟨d1, EV1⟩ := EV1; obtain ⟨d2, EV2⟩ := EV2
    exists 1+d1+d2; intros n _; cases n; contradiction; simp! [bind]
    rw [EV1]; simp!; rw [EV2]; simp! [pure, Except.pure]; omega; omega
  · apply stchain_tighten; apply stchain_chain; assumption'
    clear *- SC1; simp [sets, st_chain] at *; omega
  · apply se_trans; assumption'
  · simp [val_type]

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
  · simp [vars_locs, var_locs]; intros _ _; simp [H0]; tauto
  · intros _; simp [vars_locs, var_locs, H0]

theorem sem_ref2:
  sem_type G t T p q →
  q ⊆ p →  -- ✦ ∉ q
  sem_type G (.tref t) (.TRef2 T q T q) p {✦} :=
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
  · simp [st_chain]; split_ands'; omega; intros l h; have: l < ‖M'‖ := by omega
    simp [h, this, MMs.2]
  · apply storet_extend (ls := ls); assumption
    trans; simpa using VQ; split <;> rename_i NF
    specialize Cq NF; simp at Cq; simp; apply vars_locs_monotonic; simp [sets]
    simp [vt]; trivial; simp [qt]; trans; apply env_type_store_wf' WFE; assumption
    simp; tauto
  · apply se_trans; assumption; simp [store_effect]; intros _ _ _ H
    simpa [List.getElem?_eq_some' H]
  · have Ct := (valt_wf VT).2; simp [val_type]; split_ands'
    c_extend; c_extend; c_free; c_free; simp [store_type] at ST'; omega
    exists vt, qt; have ST'1 := ST'.1; simp [←ST'1]
    have h0: st_chain_deep M' (M' ++ [(vt, qt)]) qt := by
      have: qt ⊆ st_locs M' := by
        trans; apply env_type_store_wf' WFE P; simp [MMs]
      have: locs_locs_stty M' qt ⊆ st_locs M' := by
        apply lls_closed'; assumption'
      simp [st_chain]; split_ands'; trans; assumption; simp
      intros _ H; specialize this H; simp at this; simp [this]
    rintro S'' M'' MM' -; simp [vt]
    replace h0: ∀ lsv ⊆ qt, st_chain_deep M' M'' lsv := by
      introv _; apply stchain_tighten; apply stchain_chain; assumption'
      apply Set.subset_inter; apply lls_mono; assumption
      simp [sets]; intros; apply lls_s; simp; rfl; simp; exact ⟨rfl, rfl⟩
      rw [←lls_change h0]; apply lls_mono; assumption'
    clear MM'; have: occurs .none T #0 := by c_free;
    simp [ty.open_free this, Ct, valt_extend]; split_ands
    · introv h1 h2; exists lsv; split_ands'; apply valt_store_change
      assumption; specialize h0 _ h1; apply stchain_symm; rwa [←lls_change h0]
    · introv h1 h2; exists lsv; split_ands
      simpa [subst, (by c_free: #0 ∉ q), Cq.hfvs]; apply valt_store_change
      assumption; apply h0; assumption
  · simp [store_type] at ST ST' ⊢; right; omega

theorem sem_get2:
  sem_type env t (.TRef2 T1 q1 T2 q2) p q →
  q2 ⊆ p ∪ {#0} →
  (✦ ∈ q → occurs .noneq T2 #0) →
  sem_type env (.tget t) ([#0 ↦ p ∩ q] T2) p ([#0 ↦ q] q2) :=
by
  intros H1 H2 H3; dsimp at *; introv WFE ST
  obtain ⟨S', M', v, lsf, EV, MM, ST', SE, VT, VQ, -⟩ := H1 WFE ST
  clear H1; cases v <;> simp only [val_type] at VT
  obtain ⟨-, Ct2, -, Cq2, -, _, _, _, vt, qt, ML, VT⟩ := VT
  specialize VT _ ST'; simp [st_chain]; apply lls_closed' ST'; assumption
  obtain ⟨v, ls, SL, VV, LQ, -⟩ := ST'.byM ML; apply VT.2 at VV; assumption'
  clear VT; obtain ⟨ls', _, VV⟩ := VV
  exists S', M', v, ls'; split_ands'
  · dsimp only [tevaln] at *; obtain ⟨nm, EV⟩ := EV; exists nm + 1; intros n _
    cases n; omega; simp! only [bind]; rw [EV]; simp! only [SL]
    congr 2; omega; omega
  · let lsf' := if ✦ ∈ q then lsf else vars_locs V (p ∩ q)
    have Cpq: closed_ql false 0 ‖V‖ (p ∩ q) := WFE.pclosed' (by simp)
    rw [←valt_extend (V':=[(vtnone, lsf')]), ←ty.subst_open_chain _ %‖V‖, valt_subst']
    rotate_left; simp; exact ⟨rfl, rfl⟩; simp!; c_extend; assumption
    simp [val_type]; rfl; simp [Cpq.hfvs, lsf']
    by_cases NF: ✦ ∈ q <;> simp [NF, H3]; left; c_free; c_free;
    c_subst; assumption'; simp [lsf']; split; assumption; rename_i h
    simp [h] at H3 VQ; apply valt_change_no_contra (x:=‖V‖) (l':=lsf') at VV
    rotate_right 2; simp; exact ⟨rfl, rfl⟩; simpa [lsf', h]
    simpa [lsf', h] using VV; simp; split_ands'; c_free;
  · trans; assumption; simp [Finset.inter_subst]; simp [subst, Cq2.hfvs]
    rw [Set.union_assoc]; gcongr
    · trans vars_locs V (q2 \ {#0}); simp [sets]; apply vars_locs_monotonic
      clear *- H2; intro x; specialize @H2 x; simp [sets] at *; tauto
    · by_cases h: #0 ∈ q2 <;> simp [h]
      trans; exact VQ; gcongr; by_cases h: ✦ ∈ q <;> simp [h]

theorem sem_put2:
  sem_type env t1 (.TRef2 T1 q1 T2 q2) p q →
  sem_type env t2 T1 p q1 →
  sem_type env (.tput t1 t2) .TUnit p ∅ :=
by
  intros H1 H2; dsimp at *; introv WFE ST
  obtain ⟨S', M', v1, ls1, EV1, MM', ST', SS', VT1, VQ1, -⟩ := H1 WFE ST
  clear H1; have VT1' := VT1; cases v1 <;> simp only [val_type] at VT1'
  rename_i l; obtain ⟨-, -, Cq1, -⟩ := VT1'
  have WFE' : env_type M' E env V p := by
    apply envt_store_change; assumption; apply stchain_tighten; assumption
    apply lls_closed'; assumption; apply env_type_store_wf WFE
  obtain ⟨S'', M'', v2, ls2, EV2, MM'', ST'', SS'', VT2, VQ2, -⟩ := H2 WFE' ST'
  clear H2; simp [(by c_free: ✦ ∉ q1)] at VQ2; have Ct1 := (valt_wf VT2).2
  exists S''.set l v2, M'', .vnat 0, ∅; split_ands'
  · dsimp [tevaln] at *; obtain ⟨nm1, EV1⟩ := EV1; obtain ⟨nm2, EV2⟩ := EV2
    exists 1 + nm1 + nm2; intros n _; rcases n with - | n; omega
    specialize EV1 n (by omega); specialize EV2 n (by omega)
    simp! [bind, EV1, EV2]; split; rfl
    rename_i H; absurd H; simp; have: l < ‖S''‖ := by
      apply lt_of_lt_of_le (b:=‖M'‖); simp only [val_type] at VT1
      simp only [sets] at VT1; tauto
      simp [st_chain, store_type] at MM'' ST''; omega
    exists S''[l]; simp
  · apply stchain_tighten; apply stchain_chain; assumption'
    simp [st_chain] at MM'; simp [sets]; omega
  · simp [store_type]; split_ands; apply ST''.1; intro l0 L
    if h: l0 = l then
      subst l0; have VT1' := valt_store_change (M' := M'') VT1 ?_
      simp only [val_type] at VT1'
      obtain ⟨-, -, -, -, -, -, -, -, vt, qt, ML, VT1'⟩ := VT1'
      specialize VT1' _ ST''
      · simp [st_chain]; apply lls_closed'; assumption
        trans; apply (valt_wf VT1).1; apply MM''.2.1
      obtain ⟨VT1', -⟩ := VT1'; have: occurs .none T1 #0 := by c_free;
      simp [ty.open_free this, valt_extend Ct1] at VT1'
      specialize VT1' _ _ _ VT2
      · trans; assumption; apply vars_locs_monotonic; simp
      exists vt, qt; split_ands'; exists v2; split_ands; simp [L, ←ST''.1]
      obtain ⟨ls2', _, _⟩ := VT1'; exists ls2'; split_ands'
      have := ST''.byM ML; tauto
      apply stchain_tighten; assumption; apply lls_closed'; assumption
      simp [sets]; intro _ H; simp only [val_type] at VT1; tauto
    else
      simp [store_type] at ST''; simp [(Ne.intro h).symm]; tauto
  · apply se_trans_sub (p := {l}); apply se_trans; assumption'
    simp [store_effect]; introv h; simp [(Ne.intro h).symm]
    have: l ∈ ls1 := by simp only [val_type] at VT1; tauto
    simp [sets, ←ST.1]; specialize VQ1 this; simp at VQ1
    rcases VQ1 with VQ1 | VQ1
    left; revert VQ1; apply vars_locs_monotonic; simp [sets]; tauto
  · simp [val_type]
  · simp

theorem sem_pair:
  sem_type G t1 T1 p q1 →
  sem_type G t2 T2 p q2 →
  q1 ∪ q2 ⊆ p ∪ {✦} →
  sem_type G (.tpair t1 t2) (.TProd T1 ([✦ ↦ #0] q1) T2 ([✦ ↦ #0] q2)) p (q1 ∪ q2) :=
by
  intro h1 h2 h3; dsimp; introv WFE ST
  obtain ⟨S1, M1, v1, ls1, EV1, SC1, ST1, SE1, VT1, VQ1, -⟩ := h1 WFE ST
  apply envt_store_change at WFE; specialize WFE _
  · apply stchain_tighten; assumption; apply lls_closed'; assumption
    apply env_type_store_wf; assumption
  obtain ⟨S2, M2, v2, ls2, EV2, SC2, ST2, SE2, VT2, VQ2, -⟩ := h2 WFE ST1
  exists S2, M2, .vpair v1 v2, ls1 ∪ ls2; split_ands'
  · obtain ⟨d1, EV1⟩ := EV1; obtain ⟨d2, EV2⟩ := EV2
    exists 1+d1+d2; intro n _; cases n; omega; rename_i n _
    specialize EV1 n (by omega); specialize EV2 n (by omega)
    simp! [bind, EV1, EV2, pure, Except.pure]
  · apply stchain_tighten; apply stchain_chain; assumption'
    clear *- SC1; simp [st_chain, sets] at *; omega
  · apply se_trans; assumption'
  · simp only [val_type]; have WT1 := valt_wf VT1; have WT2 := valt_wf VT2
    have Cq12: q1 ∪ q2 ⊆ qdom true 0 ‖V‖ := by
      trans; assumption; apply Finset.union_subset
      c_extend WFE.pclosed; simp [sets]
    rw [Finset.union_subset_iff] at Cq12
    split_ands; c_extend WT1.2; c_extend WT2.2;
    · apply closedql_fr_tighten; simp [subst]
      rw [closedql_subst]; rotate_left; simp [sets]; simp; c_extend Cq12.1
    · apply closedql_fr_tighten; simp [subst]
      rw [closedql_subst]; rotate_left; simp [sets]; simp; c_extend Cq12.2
    c_free WT1.2; c_free WT2.2;
    · intro x; have WT1 := @WT1.1 x; have WT2 := @WT2.1 x
      clear *- WT1 WT2 SC2; simp [st_chain] at *; aesop (add safe (by omega))
    introv SC3 ST3; exists ls1, ls2; split_ands
    · simp [subst]; split; clear *-; simp [sets]; tauto; rename_i h; simp at h
      simp [closed_ql.hfvs Cq12.1]; simp [h] at VQ1
      trans; assumption; apply vars_locs_monotonic; simp
    · rw [ty.open_free]; swap; c_free WT1.2
      rw [valt_extend WT1.2]; apply valt_store_change; assumption
      apply stchain_tighten; apply stchain_chain; assumption'
      have := lls_closed' ST1 WT1.1; apply Set.subset_inter; assumption
      rw [lls_change]; apply lls_mono; simp; apply stchain_tighten; assumption'
    · simp [subst]; split; clear *-; simp [sets]; tauto; rename_i h; simp at h
      simp [closed_ql.hfvs Cq12.2]; simp [h] at VQ2
      trans; assumption; apply vars_locs_monotonic; simp
    · rw [ty.open_free]; swap; c_free WT2.2
      rw [valt_extend WT2.2]; apply valt_store_change; assumption
      apply stchain_tighten; assumption; apply lls_mono; simp
  · clear *- VQ1 VQ2 SC1; intro l; specialize @VQ1 l; specialize @VQ2 l
    simp [Finset.inter_union_distrib_left, st_chain, sets] at *
    aesop (add safe (by omega))

theorem sem_fst:
  sem_type env t (.TProd T1 q1 T2 q2) p q →
  q1 ⊆ p ∪ {#0} →
  (✦ ∈ q → occurs .noneq T1 #0) →
  sem_type env (.tfst t) ([#0 ↦ p ∩ q] T1) p ([#0 ↦ q] q1) :=
by
  intro h1 h2 h3; dsimp; introv WFE ST
  obtain ⟨S', M', v, ls, EV, MM, ST, SE, VT, VQ, EQ⟩ := h1 WFE ST
  cases v <;> simp only [val_type] at VT; rename_i v1 _
  obtain ⟨Ct1, _, Cq1, _, _, _, _, VT⟩ := VT; specialize VT _ ST
  · simp [st_chain]; apply lls_closed'; assumption'
  obtain ⟨ls1, -, VQ1, VT1, -⟩ := VT; exists S', M', v1, ls1; split_ands'
  · obtain ⟨d, EV⟩ := EV; exists 1+d; intro n _; cases n; omega; rename_i n _
    specialize EV n (by omega); simp! [bind, EV, pure, Except.pure]
  · let ls' := if ✦ ∈ q then ls else vars_locs V (p ∩ q)
    rw [←valt_extend (V':=[(vtnone,ls')]), ←ty.subst_open_chain _ %‖V‖, valt_subst']
    · apply valt_change_no_contra ‖V‖ (l':=ls') at VT1; rotate_left 2
      simp; split_ands'; c_free; simp; exact ⟨rfl, rfl⟩
      simp [ls']; clear *- VQ; aesop; simpa using VT1
    simp; exact ⟨rfl, rfl⟩; simp!; c_extend (WFE.pclosed' (by simp)); assumption
    simp [val_type]; rfl; simp; rotate_left; c_free Ct1
    · c_subst; assumption; apply WFE.pclosed'; simp
    · by_cases h: ✦ ∈ q <;> simp [h]; left; simp [h3 h]; c_free;
      right; simp [ls', h]; rw [vars_locs_shrink]; apply closed_ql.hfvs
      apply WFE.pclosed'; simp
  · simp [Finset.inter_subst]; simp [subst, Cq1.hfvs] at VQ1 ⊢
    simp at VQ; have: q1 ⊆ p ∩ q1 ∪ {#0}:= by clear *- h2; aesop (add simp sets)
    apply vars_locs_monotonic (V:=V) at this; simp at this
    clear *- this VQ1 VQ; intro l; specialize @VQ l; specialize @VQ1 l
    specialize @this l; aesop (add simp sets)

theorem sem_snd:
  sem_type env t (.TProd T1 q1 T2 q2) p q →
  q2 ⊆ p ∪ {#0} →
  (✦ ∈ q → occurs .noneq T2 #0) →
  sem_type env (.tsnd t) ([#0 ↦ p ∩ q] T2) p ([#0 ↦ q] q2) :=
by
  intro h1 h2 h3; dsimp; introv WFE ST
  obtain ⟨S', M', v, ls, EV, MM, ST, SE, VT, VQ, EQ⟩ := h1 WFE ST
  cases v <;> simp only [val_type] at VT; rename_i _ v2
  obtain ⟨_, Ct2, _, Cq2, _, _, _, VT⟩ := VT; specialize VT _ ST
  · simp [st_chain]; apply lls_closed'; assumption'
  obtain ⟨-, ls2, -, -, VQ2, VT2⟩ := VT; exists S', M', v2, ls2; split_ands'
  · obtain ⟨d, EV⟩ := EV; exists 1+d; intro n _; cases n; omega; rename_i n _
    specialize EV n (by omega); simp! [bind, EV, pure, Except.pure]
  · let ls' := if ✦ ∈ q then ls else vars_locs V (p ∩ q)
    rw [←valt_extend (V':=[(vtnone,ls')]), ←ty.subst_open_chain _ %‖V‖, valt_subst']
    · apply valt_change_no_contra ‖V‖ (l':=ls') at VT2; rotate_left 2
      simp; split_ands'; c_free; simp; exact ⟨rfl, rfl⟩
      simp [ls']; clear *- VQ; aesop; simpa using VT2
    simp; exact ⟨rfl, rfl⟩; simp!; c_extend (WFE.pclosed' (by simp)); assumption
    simp [val_type]; rfl; simp; rotate_left; c_free Ct2
    · c_subst; assumption; apply WFE.pclosed'; simp
    · by_cases h: ✦ ∈ q <;> simp [h]; left; simp [h3 h]; c_free;
      right; simp [ls', h]; rw [vars_locs_shrink]; apply closed_ql.hfvs
      apply WFE.pclosed'; simp
  · simp [Finset.inter_subst]; simp [subst, Cq2.hfvs] at VQ2 ⊢
    simp at VQ; have: q2 ⊆ p ∩ q2 ∪ {#0}:= by clear *- h2; aesop (add simp sets)
    apply vars_locs_monotonic (V:=V) at this; simp at this
    clear *- this VQ2 VQ; intro l; specialize @VQ l; specialize @VQ2 l
    specialize @this l; aesop (add simp sets)

theorem sem_nil:
  closed_ty 0 ‖G‖ (.TList T) →
  sem_type G .tnil (.TList T) p q :=
by
  dsimp; introv C WFE ST; exists S, M, .vlist [], ∅; split_ands'
  · exists 1; intro n h; cases n; simp at h; simp! [pure, Except.pure]
  · simp [st_chain]
  · simp [store_effect]
  · simp [val_type, ←WFE.t2l]; assumption
  · simp

theorem sem_cons:
  sem_type G t0 T p q0 →
  sem_type G t1 (.TList T) p q1 →
  sem_type G (.tcons t0 t1) (.TList T) p (q0 ∪ q1) :=
by
  intro h1 h2; dsimp; introv WFE ST
  obtain ⟨S1, M1, v1, ls1, EV1, MM1, ST1, SE1, VT1, VQ1, -⟩ := h1 WFE ST
  have WFE1 := envt_store_change WFE (M':=M1) ?_; swap
  · apply stchain_tighten; assumption; apply lls_closed'; assumption
    apply env_type_store_wf WFE
  obtain ⟨S2, M2, v2, ls2, EV2, MM2, ST2, SE2, VT2, VQ2, -⟩ := h2 WFE1 ST1
  cases v2 <;> simp only [val_type] at VT2; rename_i v2
  have C1 := valt_wf VT1
  exists S2, M2, .vlist (v1::v2), ls1 ∪ ls2; split_ands'
  · obtain ⟨d1, EV1⟩ := EV1; obtain ⟨d2, EV2⟩ := EV2; exists 1+d1+d2
    intro n h; cases n; simp at h; rename_i n
    specialize EV1 n (by omega); specialize EV2 n (by omega)
    simp! [bind, EV1, EV2, pure, Except.pure]
  · apply stchain_tighten; apply stchain_chain; assumption'
    clear *- MM1; simp [st_chain] at *; simp [sets]; omega
  · apply se_trans; assumption'
  · simp [val_type]; obtain ⟨_, _, _, VT2⟩ := VT2; split_ands'
    · apply Set.union_subset; assumption'; trans; apply C1.1
      clear *- MM2; simp [st_chain] at *; omega
    · exists ls1; simp; rw [ty.open_free]; swap; c_free C1.2;
      rw [valt_extend C1.2]; apply valt_store_change; assumption
      apply stchain_tighten; assumption'; apply lls_closed' ST1 C1.1
    · intro _ h; specialize VT2 _ h; obtain ⟨ls, _, VT2⟩ := VT2
      exists ls; split_ands; trans; assumption; simp
      apply valt_change_no_contra ‖V‖ vtnone (ls1 ∪ ls2) at VT2
      simpa using VT2; simp; split_ands'; c_free; simp; rfl; simp
  · rw [Finset.inter_union_distrib_left]
    clear *- VQ1 VQ2 MM1; simp [st_chain] at *
    apply Set.union_subset <;> (trans; assumption)
    · simp [sets]; aesop
    · simp [sets]; aesop (add safe (by omega))

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
  apply Finset.union_subset; trans; assumption; simp; simp; intros x T q _ G0
  if h: x < ‖G‖ then
    have: x ≠ ‖G‖ := by omega
    simp [h, HG, VG, this]; simp [h] at G0; specialize GX G0; dsimp at GX
    obtain ⟨v, vt, ls, HX, VX, CT, CQ, GX⟩ := GX; simp [HX, VX, and_assoc]
    have CQ': closed_ql true 0 ‖V‖ q := by c_extend; omega
    have CT': closed_ty 0 ‖V‖ T := by c_extend; omega
    simp [CQ'.hfvs, valt_extend, CT']; split_ands''
    rwa [valt_extend]; split; simp!; assumption
  else
    have: x = ‖G‖ := by
      apply List.getElem?_eq_some' at G0; simp at G0; omega
    subst x; simp [HG, VG] at G0 Q1B ⊢; rcases G0 with ⟨rfl, rfl, rfl⟩
    split_ands'; rwa [←HG]
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
  intros WFE QfP Q1F LB _ _ EC
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
    clear * -; intros _ _ H; ext x; specialize @H x; aesop
  apply this at HQa; apply this at HQb; clear this
  have QaF: qa ∩ qf' ⊆ qf' := by simp [sets]
  have QbF: qb ∩ qf' ⊆ qf' := by simp [sets]
  generalize qa ∩ qf' = qa' at *; generalize qb ∩ qf' = qb' at *
  -- simplify vars_locs & vars_trans
  have C: ∀ q ⊆ qf', closed_ql.fvs ‖V‖ q := by
    simp [closed_ql.fvs, qf', sets]; intro _ h _; trans; apply h; simp
    apply closed_ql.hfvs; apply WFE.pclosed' (by assumption)
  generalize hOV: vars_trans (G ++ [(T1, q1, bn)]) qa ∩
                  vars_trans (G ++ [(T1, q1, bn)]) qb = ov at *
  rw [HQa, HQb, WFE.v2l] at hOV ⊢; simp [C, QaF, QbF]
  simp [TL, WFE.t2l, C, Q1F, QaF, QbF] at hOV
  simp only [Set.union_inter_distrib_right, Set.inter_union_distrib_left,
             Set.union_assoc]
  simp only [Finset.union_inter_distrib_right, Finset.inter_union_distrib_left,
             Finset.union_assoc] at hOV
  subst ov; simp
  -- by congruence
  have CC: ∀ q ⊆ qf', closed_ql.fvs ‖G‖ (vars_trans G q) := by
    rw [←WFE.t2l] at C; clear * - C TL; intros; intro _ h
    apply vt_closed at h; aesop; exact telescope_shrink TL
  replace QV: ∀ q q', q ⊆ qf' → q' ⊆ qf' →
    vars_trans G q ∩ vars_trans G q' ⊆ qf' ∪ {%‖G‖} →
    vars_locs V q ∩ vars_locs V q' ⊆
      vars_locs (V ++ [(vt, lsx)]) (vars_trans G q ∩ vars_trans G q') :=
  by
    intros _ _ _ c2 h; specialize CC _ c2; rw [vars_locs_shrink]; apply QV
    trans; assumption; simp [qf']; gcongr; trans; assumption; simp [qf']; gcongr
    intros _ h1; specialize h h1; simp [qf'] at h h1 ⊢
    clear *- CC h h1 QfP; specialize @CC ‖G‖; aesop (add simp sets)
    rw [←WFE.t2l]; simp [closed_ql.fvs]; intros _ _ h; apply CC; assumption
  gcongr
  · apply QV; assumption'; trans; swap; assumption; simp [sets]
  · by_cases h: %‖V‖ ∈ qa <;> simp [h] at H0 ⊢
    trans; swap; trans; apply QV q1 qb'; assumption'
    trans; swap; assumption; clear *-; aesop (add simp sets)
    apply vars_locs_monotonic; simp [sets]; tauto
    apply vars_locs_monotonic (V := V) at QbF; clear *- QbF LB; aesop (add simp sets)
  · by_cases h: %‖V‖ ∈ qb <;> simp [h] at H0 ⊢
    trans; swap; trans; apply QV qa' q1; assumption'
    trans; swap; assumption; clear *-; aesop (add simp sets)
    apply vars_locs_monotonic; simp [sets]; tauto
    apply vars_locs_monotonic (V := V) at QaF; clear *- QaF LB; aesop (add simp sets)
  · by_cases h: %‖V‖ ∈ qa <;> simp [h]
    by_cases h: %‖V‖ ∈ qb <;> simp [h]

theorem sem_fold:
  sem_type G tl (.TList T) p q1 →
  sem_type G t0 U p q2 →
  sem_type (G++[(T, p∩q1, .var), (U, p∩q2, .var)]) t1 U (p ∪ {%‖G‖, %(‖G‖+1)}) q2 →
  closed_ty 0 ‖G‖ T → ✦ ∉ q1 → closed_ql false 0 ‖G‖ q2 →
  sem_type G (.tfold tl t0 t1) U p q2 :=
by
  intro h1 h2 h3 Ct Nfr1 Cq2; dsimp; introv WFE ST
  have Nfr2: ✦ ∉ q2 := by c_free;
  obtain ⟨S1, M1, v1, ls1, EV1, MM1, ST1, SE1, VT1, VQ1, -⟩ := h1 WFE ST
  cases v1 <;> simp only [val_type] at VT1; rename_i vlst
  have WFE1 := envt_store_change WFE (M':=M1) ?_; swap
  · apply stchain_tighten; assumption; apply lls_closed'; assumption
    apply env_type_store_wf WFE
  obtain ⟨S2, M2, v2, ls2, EV2, MM2, ST2, SE2, VT2, VQ2, -⟩ := h2 WFE1 ST1
  obtain ⟨d1, EV1⟩ := EV1; obtain ⟨d2, EV2⟩ := EV2
  suffices ∃ S' M' v ls,
      (∃ nm > d1 + d2, ∀ n ≥ nm, vlst.foldr
        (fun v1 ev0 => do
          let (d0, S0, v0) ← ev0
          let (d1, S1, v1) ← teval n S0 (E++[v1,v0]) t1
          return (1+d0+d1, S1, v1))
        (.ok (1+d1+d2, S2, v2)) = Except.ok (nm, S', v)) ∧
      st_chain_full M2 M' ∧
      store_type S' M' ∧
      store_effect S2 S' (vars_locs V p) ∧
      val_type M' V v U ls ∧
      val_qual M1 M' V ls p q2 by
    obtain ⟨S', M', v, ls, this, _, _, _, _, _⟩ := this
    exists S', M', v, ls; split_ands'
    · obtain ⟨nm, hnm, this⟩ := this
      exists nm; intro n h; cases n; simp at h; rename_i n
      specialize EV1 n (by omega); specialize EV2 n (by omega)
      simp [bind] at this; specialize this n (by omega)
      simp! [bind, EV1, EV2, this]
    · apply stchain_tighten; apply stchain_chain; assumption
      apply stchain_chain; assumption'; clear *- MM1 MM2
      simp [st_chain, sets] at *; omega
    · apply se_trans; assumption; apply se_trans; assumption'
    · rename_i h; clear *- h MM1; simp [st_chain] at *
      trans; assumption; gcongr; split <;> simp; omega
  clear EV1 EV2 SE1 SE2 h1 h2; obtain ⟨-, -, _, VT1⟩ := VT1
  induction vlst
  · exists S2, M2, v2, ls2; split_ands'
    · exists 1+d1+d2; simp
    · simp [st_chain]
    · simp [store_effect]
  next vhd vtl ih =>
    specialize ih (by intro _ h; apply VT1; simp [h])
    specialize VT1 vhd (by simp); obtain ⟨ls1', _, VT1⟩ := VT1
    rw [ty.open_free, valt_extend] at VT1; rotate_left; rwa [←WFE.t2l]; c_free;
    apply valt_grow at VT1; specialize VT1 _ _; assumption'
    have: env_cell M1 V {%‖V‖} ‖V‖ T (p∩q1) .var vhd vtnone ls1 := by
      simp; split_ands; rwa [←WFE.t2l]; have := WFE.pclosed' (by simp: p∩q1 ⊆ p)
      c_extend; assumption; simp [Nfr1] at VQ1; intro; assumption
    replace WFE1 := envt_extend_full WFE1 (fun _ h => h)
      (by clear *-; aesop (add simp sets)) (by clear *- Nfr1 VQ1; aesop (add simp sets))
      (by simp [st_chain]; apply lls_closed' ST1; apply env_type_store_wf WFE1)
      WFE.v2l.symm this
    clear this; have := (valt_wf VT2).2
    have Cq2': ∀p, closed_ql.fvs ‖V‖ (p ∩ q2) := by
      intros _ _; simp; intro _; apply WFE.t2l ▸ Cq2.hfvs
    obtain ⟨S3, M3, v3, ls3, EV3, MM3, ST3, SE3, VT3, VQ3⟩ := ih
    have: env_cell M3 (V++[(vtnone, ls1)]) {%(‖V‖+1)} (‖V‖+1) U (p∩q2) .var v3 vtnone ls3 := by
      simp; split_ands; c_extend; have := WFE.pclosed' (by simp: p∩q2 ⊆ p);
      c_extend; rwa [valt_extend]; assumption; simp [Nfr2] at VQ3; intro
      rwa [vars_locs_shrink]; apply Cq2'
    have WFE2 := envt_extend_full WFE1 (fun _ h => h)
      (by clear *-; aesop (add simp sets))
      (by trans ls3; simp; rw [vars_locs_shrink]; swap; apply Cq2'
          clear *- VQ3 Nfr2; aesop (add simp sets))
      (by apply stchain_tighten; apply stchain_chain; assumption'
          trans st_locs M1; apply lls_closed' ST1; apply env_type_store_wf WFE1
          clear *- MM2; simp [sets, st_chain] at *; omega)
      (by simp [WFE.v2l]) this
    clear WFE1 this; simp [←WFE.t2l] at WFE2
    obtain ⟨S', M', v4, ls4, EV4, MM4, ST4, SE4, VT4, VQ4, -⟩ := h3 WFE2 ST3
    exists S', M', v4, ls4; split_ands'
    · obtain ⟨d3, _, EV3⟩ := EV3; obtain ⟨d4, EV4⟩ := EV4
      exists 1+d3+d4; split_ands; omega; intro n h; cases n; simp at h
      rename_i n; specialize EV3 (n+1) (by omega); specialize EV4 (n+1) (by omega)
      simp [-bind_pure_comp, EV3]; simp! [bind, EV4, pure, Except.pure]
    · apply stchain_tighten; apply stchain_chain; assumption'
      clear *- MM3; simp [sets, st_chain] at *; omega
    · apply se_trans_sub; assumption'; simp [WFE.t2l, Finset.insert_eq]
      rw [vars_locs_shrink]; swap; apply WFE.pclosed.hfvs
      trans vars_locs V p; swap; simp; apply Set.union_subset; simp
      clear *- Nfr1 Nfr2 VQ1 VQ3; simp [Nfr1, Nfr2] at VQ1 VQ3
      apply Set.union_subset <;> (trans; assumption) <;> apply vars_locs_monotonic <;> simp
    · rw [valt_extend] at VT4; assumption; assumption
    · simp [Nfr2, Finset.insert_eq] at VQ4 ⊢
      trans; exact VQ4; rw [vars_locs_shrink]; swap; apply Cq2'
      apply vars_locs_monotonic; clear *- Cq2
      replace Cq2 := Cq2.hfvs; intro x; cases x <;> simp
      rename_i x; specialize @Cq2 x; aesop (add safe (by omega))

theorem sem_abs:
  sem_type (env ++ [(.TTop, p ∩ qf, .self), ([#0 ↦ %‖env‖] T1, [#0 ↦ %‖env‖] q1, .var)])
    t ([#0 ↦ %‖env‖] [#1 ↦ %(‖env‖+1)] T2)
    (p ∩ qf ∪ {%‖env‖, %(‖env‖+1)})
    [#0 ↦ %‖env‖] [#1 ↦ %(‖env‖+1)] q2 →

  q1 ⊆ p ∩ qf ∪ {✦, #0} →
  closed_ty 1 ‖env‖ T1 →
  closed_ty 2 ‖env‖ T2 →
  closed_ql true 1 ‖env‖ q1 →
  closed_ql true 2 ‖env‖ q2 →
  closed_ql false 0 ‖env‖ qf →
  (#0 ∈ q1 → ✦ ∈ q1) →
  occurs .no_covariant T1 #0 →
  occurs .no_contravariant T2 #0 →
  sem_type env (.tabs none t) (.TFun T1 q1 T2 q2) p qf :=
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
      apply se_sub; assumption; simp [WFE.t2l]
      rw [vars_locs_shrink]; simp [sets]; exact Cqf'.hfvs
    · -- val_qual
      simp at HVQ2; trans; assumption; simp [WFE.t2l, st_locs]; gcongr
      apply vars_locs_monotonic; simp [sets]; simp [subst]
    · -- env_type extend
      have: ∀α (a: List α) (b c: α), a ++ [b, c] = a ++ [b] ++ [c] := by simp
      rw [this, this, this]; clear this
      apply envt_extend_full (M := M) (p := p ∩ qf ∪ {%‖env‖}); rotate_left
      · clear * -; tauto
      · clear * - FF; intro x; specialize @FF x; aesop (add simp [subst])
      · simp [Cqf'.hfvs]; simp [WFE.t2l] at HVQ1 ⊢; clear *- HVQ1
        intro x; specialize @HVQ1 x; aesop (add simp sets)
      · apply stchain_tighten; assumption; apply lls_mono
        simp [WFE.t2l, Cqf'.hfvs, sets]
      · simp [WFE.v2t]
      simp; split_ands'
      · c_subst; c_extend;
      · c_subst; c_extend;
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
  sem_type env (.tabs none t) (.TFun T1 q1 T2 q2) p q →
  sem_type env (.tabs (T1, q1) t) (.TFun T1 q1 T2 q2) p q :=
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

  q1 ⊆ p ∩ qf ∪ {✦, #0} →
  closed_ty 1 ‖env‖ T1 →
  closed_ty 2 ‖env‖ T2 →
  closed_ql true 1 ‖env‖ q1 →
  closed_ql true 2 ‖env‖ q2 →
  closed_ql false 0 ‖env‖ qf →
  (#0 ∈ q1 → ✦ ∈ q1) →
  occurs .no_covariant T1 #0 →
  occurs .no_contravariant T2 #0 →
  sem_type env (.ttabs none t) (.TAll T1 q1 T2 q2) p qf :=
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
    have ⟨S2, M2, vy, lsy, IHW1⟩ := @H S' M' (E ++ [.vtabs E t, .vnat 0])
        (V ++ [(vtnone, vars_locs V (p ∩ qf)), (vt, lsx)]) ?_ (by assumption)
    clear H; exists S2, M2, vy, lsy; obtain ⟨_, _, _, _, HVT2, HVQ2, _⟩ := IHW1
    split_ands'
    · -- store_effect
      apply se_sub; assumption; simp [WFE.t2l]
      rw [vars_locs_shrink]; simp [sets]; exact Cqf'.hfvs
    · -- val_qual
      simp at HVQ2; trans; assumption; simp [WFE.t2l, st_locs]; gcongr
      apply vars_locs_monotonic; simp [sets]; simp [subst]
    · -- env_type extend
      have: ∀α (a: List α) (b c: α), a ++ [b, c] = a ++ [b] ++ [c] := by simp
      rw [this, this, this]; clear this
      apply envt_extend_full (M := M) (p := p ∩ qf ∪ {%‖env‖}); rotate_left
      · clear * -; tauto
      · clear * - FF; intro x; specialize @FF x; aesop (add simp [subst])
      · simp [Cqf'.hfvs]; simp [WFE.t2l] at HVQ1 ⊢; clear *- HVQ1
        intro x; specialize @HVQ1 x; aesop (add simp sets)
      · apply stchain_tighten; assumption; apply lls_mono
        simp [WFE.t2l, Cqf'.hfvs, sets]
      · simp [WFE.v2t]
      simp; split_ands'
      · c_subst; c_extend;
      · c_subst; c_extend;
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

theorem sem_tabsa:
  sem_type env (.ttabs none t) (.TAll T1 q1 T2 q2) p q →
  sem_type env (.ttabs (T1, q1) t) (.TAll T1 q1 T2 q2) p q :=
by
  intro h; dsimp at *; introv WFE ST; specialize h WFE ST
  obtain ⟨S', M', v, ls, h⟩ := h; exists S', M', v, ls; split_ands''
  rename tevaln _ _ _ _ _ => h; obtain ⟨nm, h⟩ := h; exists nm; intros n h1
  specialize h n h1; cases n; simp at h1; simpa [teval] using h

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

  q2 ⊆ p ∪ {✦, #0, #1} →
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
    have Ct1 := closedty_extend (mb' := 1) (mf' := ‖V‖) this (by simp) (by simp)
    rw [closedty_subst] at Ct1; rotate_left; assumption; simp!; simp
    rwa [←valt_extend (V' := [(vtnone, lsf')]), ←ty.subst_open_chain #0 %‖V‖,
          valt_subst'] at VTX
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
        replace SEP: vars_trans env (p∩qf) ∩ vars_trans env (p∩qx') ⊆ {✦} := by
          trans; swap; exact SEP; gcongr
          apply vt_mono; simp [sets]; apply vt_mono; simp [sets]
        apply overlapping (lsx := vars_locs V qx') ST ST1 at SEP; assumption'
        · simp at SEP; trans; assumption; trans (?_ ∪ ?_); gcongr
          trans; swap; exact EX; apply vars_locs_monotonic; simp [sets]
          intro _ h; exact h; rw [Set.union_assoc]; gcongr
          simp [Set.eq_empty_iff_forall_notMem] at SEP
          clear *- FM1 SEP; intro x; specialize @FM1 x; specialize @SEP x
          aesop (add simp sets, safe (by omega))
        · suffices ✦ ∉ qx' by
            simp [this]; apply vars_locs_monotonic
            clear *- XP; aesop (add simp sets)
          intro h; have := WFE.pclosed' XP h; simp at this
        · simp
      else
        simp [fn1, fr1, subst, this] at SEP ⊢
        specialize SEP WFE.1; simp [SEP.1] at VQX; obtain ⟨-, -, -, SEP⟩ := SEP
        trans; assumption; trans; swap; assumption
        apply vars_locs_monotonic; simp [sets]
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
    simp [←ST.1]; simp [st_chain] at MM1; clear *- VQX VQF MM1
    intro x; specialize @VQX x; specialize @VQF x
    have := @vars_locs_monotonic _ _ V (by simp: p∩qx ⊆ p) x
    have := @vars_locs_monotonic _ _ V (by simp: p∩qf ⊆ p) x
    aesop (add simp sets, safe (by omega))
  · -- result type
    have Cqf := WFE.pclosed' (by simp: p ∩ qf ⊆ p)
    have Cqx := WFE.pclosed' (by simp: p ∩ qx ⊆ p)
    have Cp := WFE.pclosed
    rw [←valt_extend (V' := [(vtnone, lsf'), (vtnone, lsx')]),
      ←ty.subst_open_chain #0 %‖V‖,
      ←ty.subst_open_chain #1 %(‖V‖ + 1),
      ty.open_subst_comm]; rotate_left
    simp; c_free; simp!; simp; c_free;
    rw [occurs_subst]; simp; c_free; c_free; simp!; c_subst; assumption'
    rw [valt_subst']; rotate_left
    simp; exact ⟨rfl, rfl⟩; simp!; c_extend; assumption
    simp [val_type]; rfl; simp [Cqf.hfvs]; rw [occurs_subst]; simp
    by_cases h: ✦ ∈ qf; left; split_ands; c_free;
    simp [FFr h]; right; simp [h, lsf']; c_free; simp; simp!
    rwa [valt_subst']
    simp; exact ⟨rfl, rfl⟩; simp!; c_extend; assumption
    simp [val_type]; rfl; simp [Cqx.hfvs]
    by_cases h: ✦ ∈ qx; left; split_ands; c_free;
    simp [XFr h]; right; simp [h, lsx']
  · -- result qualifier
    trans; assumption; clear VQY
    have: closed_ql.fvs ‖V‖ q2 := by apply closed_ql.hfvs; assumption
    simp [Finset.inter_subst]; simp [subst]; simp [this]
    clear this; intros l; simp [st_chain] at MM1 MM2
    replace Cq2: q2 ⊆ p ∩ q2 ∪ {✦, #0, #1} := by
      clear *- Cq2; aesop (add simp sets)
    clear *- Cq2 VQF VQX MM1 MM2; specialize @VQF l; specialize @VQX l
    replace Cq2 := @vars_locs_monotonic _ _ V Cq2 l
    simp [Finset.insert_eq] at Cq2; aesop (add simp sets, safe (by omega))

theorem sem_app_classic:
  sem_type env f (.TFun T1 q1 T2 q2) p qf →
  sem_type env t T1 p qx →
  #0 ∈ q1 ∨ sem_qtp env qx q1 ∨ ✦ ∈ q1 ∧
    sem_qtp env ((vars_trans env qf) ∩ (vars_trans env qx)) q1 ∧
    (vars_trans env qf ∩ vars_trans env qx) ⊆ p ∪ {✦} →

  q2 ⊆ p ∪ {✦, #0, #1} →
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
    simp [←ST.1]; simp [st_chain] at MM1; clear *- VQX VQF MM1
    intro x; specialize @VQX x; specialize @VQF x
    have := @vars_locs_monotonic _ _ V (by simp: p∩qx ⊆ p) x
    have := @vars_locs_monotonic _ _ V (by simp: p∩qf ⊆ p) x
    aesop (add simp sets, safe (by omega))
  · -- result type
    have Cqf := WFE.pclosed' (by simp: p ∩ qf ⊆ p)
    have Cqx := WFE.pclosed' (by simp: p ∩ qx ⊆ p)
    have Cp := WFE.pclosed
    rw [←valt_extend (V' := [(vtnone, lsf'), (vtnone, lsx')]),
      ←ty.subst_open_chain #0 %‖V‖,
      ←ty.subst_open_chain #1 %(‖V‖ + 1),
      ty.open_subst_comm]; rotate_left
    simp; c_free; simp!; simp; c_free; rw [occurs_subst]; simp; c_free; c_free; simp!
    c_subst; assumption'; rw [valt_subst']; rotate_left
    simp; exact ⟨rfl, rfl⟩; simp!; c_extend; assumption
    simp [val_type]; rfl; simp [Cqf.hfvs]; rw [occurs_subst]; simp
    by_cases h: ✦ ∈ qf; left; split_ands; c_free;
    simp [FFr h]; right; simp [h, lsf']; c_free; simp; simp!
    rwa [valt_subst']
    simp; exact ⟨rfl, rfl⟩; simp!; c_extend; assumption
    simp [val_type]; rfl; simp [Cqx.hfvs]
    by_cases h: ✦ ∈ qx; left; split_ands; c_free;
    simp [XFr h]; right; simp [h, lsx']
  · -- result qualifier
    trans; assumption; clear VQY
    have: closed_ql.fvs ‖V‖ q2 := by apply closed_ql.hfvs; assumption
    simp [Finset.inter_subst]; simp [subst]; simp [this]
    clear this; intros l; simp [st_chain] at MM1 MM2
    replace Cq2: q2 ⊆ p ∩ q2 ∪ {✦, #0, #1} := by
      clear *- Cq2; aesop (add simp sets)
    clear *- Cq2 VQF VQX MM1 MM2; specialize @VQF l; specialize @VQX l
    replace Cq2 := @vars_locs_monotonic _ _ V Cq2 l
    simp [Finset.insert_eq] at Cq2; aesop (add simp sets, safe (by omega))

-- ttabs with fsub

@[simp]
def sem_stp G T1 q1 T2 q2 :=
  ∀ ⦃S M E V p⦄,
    env_type1 M E G V p →
    store_type S M →
    (✦ ∈ q1 → ✦ ∈ q2) ∧ vars_locs V q1 ⊆ vars_locs V q2 ∧
    (vars_locs V q2 ⊆ vars_locs V p →
    ∀ ⦃v ls⦄,
      val_type M V v T1 ls →
      (✦ ∉ q1 → ls ⊆ vars_locs V q1) →
      ∃ gl ⊆ vars_locs V q2,
        val_type M V v T2 (ls ∪ gl))

theorem sem_tapp:
  sem_type env f (.TAll T1 q1 T2 q2) p qf →
  closed_ty 0 ‖env‖ Tx →
  sem_stp env Tx {✦} T1 {✦} →
  #0 ∈ q1 ∨ sem_qtp env qx q1 ∨ ✦ ∈ q1 ∧
    sem_qtp env ((vars_trans env qf) ∩ (vars_trans env qx)) q1 ∧
    (vars_trans env qf ∩ vars_trans env qx) ⊆ p ∪ {✦} →

  q2 ⊆ p ∪ {✦, #0, #1} →
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
    simp [←ST.1]; simp [st_chain] at MM1; clear *- VQF MM1
    intro x; specialize @VQF x
    have := @vars_locs_monotonic _ _ V (by simp: p∩qx ⊆ p) x
    have := @vars_locs_monotonic _ _ V (by simp: p∩qf ⊆ p) x
    aesop (add simp sets, safe (by omega))
  · -- result type
    have Cqf := WFE.pclosed' (by simp: p ∩ qf ⊆ p)
    have Cqx := WFE.pclosed' (by simp: p ∩ qx ⊆ p)
    have Cp := WFE.pclosed; rw [WFE.t2l] at Ctx
    rw [←valt_extend (V' := [(vtnone, lsf'), (vtx, lsx')]),
      ←ty.subst_open_chain #0 %‖V‖,
      ←ty.subst_open_chain #1 %(‖V‖ + 1),
      ty.open_subst_comm]; rotate_left
    simp; c_free; c_free; simp; c_free; rw [occurs_subst]; simp; c_free; c_free; c_free;
    c_subst; assumption'; split_ands'; rw [valt_subst']; rotate_left
    simp; exact ⟨rfl, rfl⟩; simp!; c_extend; assumption
    simp [val_type]; rfl; simp [Cqf.hfvs]; rw [occurs_subst]; simp
    by_cases h: ✦ ∈ qf; left; split_ands; c_free;
    simp [FFr h]; right; simp [h, lsf']; c_free; c_free;
    rwa [valt_subst']
    simp; exact ⟨rfl, rfl⟩; c_extend; c_extend; assumption
    simp [vtx]; ext; rwa [valt_extend]
    by_cases h: ✦ ∈ qx; left; simp; split_ands; c_free;
    simp [XFr h]; right; simp [h, lsx', Cqx.hfvs]
  · -- result qualifier
    trans; assumption; clear VQY
    have: closed_ql.fvs ‖V‖ q2 := by apply closed_ql.hfvs; assumption
    simp [Finset.inter_subst]; simp [subst]; simp [this]
    clear this; intros l; simp [st_chain] at MM1
    replace Cq2: q2 ⊆ p ∩ q2 ∪ {✦, #0, #1} := by
      clear *- Cq2; aesop (add simp sets)
    clear *- Cq2 VQF MM1; specialize @VQF l
    replace Cq2 := @vars_locs_monotonic _ _ V Cq2 l
    simp [Finset.insert_eq] at Cq2; aesop (add simp sets, safe (by omega))

-- subtyping

theorem sem_sub:
  sem_type G t T1 p q1 →
  sem_stp G T1 q1 T2 q2 →
  q2 ⊆ p ∪ {✦} →
  sem_type G t T2 p q2 :=
by
  intros HT STP Q2P; dsimp; introv WFE ST
  obtain ⟨S', M', v, ls, _, MM, ST', _, VT, VQ, EQ⟩ := HT WFE ST
  have WFE': env_type M' E G V p := by
    apply envt_store_change; assumption; apply stchain_tighten; assumption
    apply lls_closed' ST; apply env_type_store_wf WFE
  have VL1: vars_locs V (p ∩ q1) ⊆ vars_locs V q1 := by
    apply vars_locs_monotonic; simp
  have VL2: vars_locs V q2 ⊆ vars_locs V (p ∩ q2) := by
    trans vars_locs V (p ∩ q2 ∪ {✦}); apply vars_locs_monotonic
    clear *- Q2P; intro x; specialize @Q2P x; simp [sets] at *; tauto; simp
  obtain ⟨Q1, Q2, STP⟩ := STP WFE'.1 ST'; specialize STP _ VT _
  · trans; assumption; apply vars_locs_monotonic; simp
  · simp at VQ; intro h; simp [h] at VQ; trans; assumption'
  obtain ⟨ls', VQ', VT'⟩ := STP; exists S', M', v, ls ∪ ls'; split_ands'
  · simp at VQ; clear *- Q2 VQ VQ' Q1 VL1 VL2; intro l
    specialize @VL1 l; specialize @VL2 l; specialize @Q2 l
    specialize @VQ' l; specialize @VQ l; aesop
  · split <;> simp at EQ; trans; assumption; simp; simp

theorem sem_stp_refl:
  sem_qtp G q1 q2 →
  sem_stp G T q1 T q2 :=
by
  intro QTP; dsimp; introv WFE ST; specialize QTP WFE; split_ands''
  intros; exists ∅; simpa

theorem sem_stp_trans:
  sem_stp G T1 q1 T2 q2 →
  sem_stp G T2 q2 T3 q3 →
  sem_stp G T1 q1 T3 q3 :=
by
  intros S1 S2; dsimp; introv WFE ST; specialize S1 WFE ST; specialize S2 WFE ST
  obtain ⟨Q1a, Q1b, S1⟩ := S1; obtain ⟨Q2a, Q2b, S2⟩ := S2; split_ands
  clear *- Q1a Q2a; tauto; trans; assumption'
  introv C3 VT1 VQ1; specialize S1 _ VT1 VQ1; trans; assumption'
  obtain ⟨gl1, VQ2, VT2⟩ := S1; specialize S2 C3 VT2 _
  · clear *- Q1a Q1b VQ1 VQ2; aesop (add simp sets)
  obtain ⟨gl2, VQ3, VT3⟩ := S2; exists gl1 ∪ gl2; split_ands
  · apply Set.union_subset; trans; assumption'
  convert VT3 using 1; ext; simp; clear *-; tauto

theorem sem_stp_top:
  sem_stp G T q .TTop q :=
by
  simp; introv WFE ST C VT VQ; exists ∅; simp [val_type]
  exact (valt_wf VT).1

theorem sem_stp_ref2:
  sem_stp (G ++ [(.TTop, q0, .self)]) ([#0 ↦ %‖G‖] T1b) {✦} ([#0 ↦ %‖G‖] T1a) ({✦} ∪ gr1) →
  sem_stp (G ++ [(.TTop, q0, .self)]) ([#0 ↦ %‖G‖] T2a) {✦} ([#0 ↦ %‖G‖] T2b) ({✦} ∪ gr2) →
  sem_qtp (G ++ [(.TTop, q0, .self)]) (gr1 ∪ q1b) q1a →
  sem_qtp (G ++ [(.TTop, q0, .self)]) (gr2 ∪ [#0 ↦ %‖G‖] q2a) ([#0 ↦ %‖G‖] q2b) →
  closed_ty 0 ‖G‖ (.TRef2 T1b q1b T2b q2b) →
  closed_ql true 0 ‖G‖ q0 →
  gr1 ⊆ q0 ∪ {%‖G‖} → gr2 ⊆ q0 ∪ {%‖G‖} →
  sem_stp G (.TRef2 T1a q1a T2a q2a) q0 (.TRef2 T1b q1b T2b q2b) q0 :=
by
  intros S1 S2 Q1 Q2 C Cq0 _ _; simp; introv WFE ST QP VT VQ
  let gl := vars_locs V q0; exists gl; simp! [WFE.t2l] at C Cq0
  obtain ⟨_, _, Cq1b, _, Cq1', _, _⟩ := C; apply closedql_bv_tighten at Cq1b
  assumption'; clear Cq1'; have h: ls ∪ gl ⊆ st_locs M := by
    apply Set.union_subset; apply (valt_wf VT).1; trans; assumption
    apply env_type1_store_wf WFE
  apply valt_grow at VT; specialize VT _ h; simp
  cases v <;> simp [val_type] at VT; rename_i l _; simp [val_type]
  obtain ⟨_, _, Cq1a, _, _, _, _, -, vt, qt, ML, VT⟩ := VT; split_ands'
  simp [ML, and_assoc]; introv SC ST; specialize VT SC ST
  have WFE1 := by
    have: env_cell M V {%‖V‖} ‖V‖ .TTop q0 .self (.vref l) vtnone (ls ∪ gl) := by
      simp [gl]; split_ands'; simpa [val_type]
      intro h; specialize VQ h; apply Set.union_subset; assumption; simp
    apply envt1_extend_stub WFE _ _ _ this; exact ∅
    simp; simp [st_chain]; simp [WFE.v2l]
  simp at WFE1; apply envt1_store_change (M':=M') at WFE1
  specialize WFE1 _; apply stchain_tighten; assumption; simp; split_ands
  · replace VT := VT.1; intros _ _ h1 h2; specialize S1 WFE1 ST
    simp [WFE.t2l] at S1; specialize S1 _ h2
    · trans; apply vars_locs_monotonic; assumption; simp [gl, Cq0.hfvs, WFE.t2l]
      clear *-; simp [sets]; tauto
    obtain ⟨gl1, S1a, S1b⟩ := S1; apply VT; assumption'
    specialize Q1 WFE1; simp at Q1; obtain ⟨-, -, -, Q1⟩ := Q1
    trans ?_ ∪ ?_; gcongr; assumption'; rw [Set.union_comm]
    simpa [Cq1a.hfvs, Cq1b.hfvs] using Q1
  · replace VT := VT.2; intro _ _ h1 h2; specialize VT _ _ h1 h2
    obtain ⟨lsv', h3, h4⟩ := VT; specialize S2 WFE1 ST; simp [WFE.t2l] at S2
    specialize S2 _ h4
    · trans; apply vars_locs_monotonic; assumption; simp [WFE.t2l, gl, Cq0.hfvs]
      clear *-; simp [sets]; tauto
    obtain ⟨gl2, _, _⟩ := S2; exists lsv' ∪ gl2; split_ands'
    specialize Q2 WFE1; simp [WFE.t2l] at Q2; rw [Set.union_comm]
    trans ?_ ∪ ?_; gcongr; assumption'; exact Q2.2.2.2

theorem sem_stp_pair:
  sem_stp (G ++ [(.TTop, q0, .self)]) ([#0 ↦ %‖G‖] T1a) {✦} ([#0 ↦ %‖G‖] T1b) ({✦} ∪ gr1) →
  sem_stp (G ++ [(.TTop, q0, .self)]) ([#0 ↦ %‖G‖] T2a) {✦} ([#0 ↦ %‖G‖] T2b) ({✦} ∪ gr2) →
  sem_qtp (G ++ [(.TTop, q0, .self)]) (gr1 ∪ [#0 ↦ %‖G‖] q1a) ([#0 ↦ %‖G‖] q1b) →
  sem_qtp (G ++ [(.TTop, q0, .self)]) (gr2 ∪ [#0 ↦ %‖G‖] q2a) ([#0 ↦ %‖G‖] q2b) →
  closed_ty 0 ‖G‖ (.TProd T1b q1b T2b q2b) →
  closed_ql true 0 ‖G‖ q0 →
  gr1 ⊆ q0 ∪ {%‖G‖} → gr2 ⊆ q0 ∪ {%‖G‖} →
  sem_stp G (.TProd T1a q1a T2a q2a) q0 (.TProd T1b q1b T2b q2b) q0 :=
by
  intros S1 S2 Q1 Q2 C Cq0 _ _; simp; introv WFE ST QP VT VQ
  let gl := vars_locs V q0; exists gl; simp! [WFE.t2l] at C Cq0
  obtain ⟨_, _, Cq1b, _, _, _⟩ := C; have h: ls ∪ gl ⊆ st_locs M := by
    apply Set.union_subset; apply (valt_wf VT).1; trans; assumption
    apply env_type1_store_wf WFE
  apply valt_grow at VT; specialize VT _ h; simp
  cases v <;> simp only [val_type] at VT; rename_i v1 v2 _; simp only [val_type]
  obtain ⟨_, _, Cq1a, _, _, _, -, VT⟩ := VT; split_ands'; introv SC ST
  specialize VT SC ST; have WFE1 := by
    have: env_cell M V {%‖V‖} ‖V‖ .TTop q0 .self (.vpair v1 v2) vtnone (ls ∪ gl) := by
      simp [gl]; split_ands'; simpa [val_type]
      intro h; specialize VQ h; apply Set.union_subset; assumption; simp
    apply envt1_extend_stub WFE _ _ _ this; exact ∅
    simp; simp [st_chain]; simp [WFE.v2l]
  simp at WFE1; apply envt1_store_change (M':=M') at WFE1
  specialize WFE1 _; apply stchain_tighten; assumption; simp
  obtain ⟨ls1, ls2, VQ1, VT1, VQ2, VT2⟩ := VT
  -- start subtyping
  simp only [WFE.t2l] at S1 S2 Q1 Q2
  specialize S1 WFE1 ST; simp at S1; specialize S1 _
  · trans; apply vars_locs_monotonic; assumption; simp [←WFE.t2l]
    simp [Cq0.hfvs, gl]; clear *-; aesop (add simp sets)
  specialize S1 VT1; obtain ⟨gl1, VT1', VQ1'⟩ := S1
  specialize S2 WFE1 ST; simp at S2; specialize S2 _
  · trans; apply vars_locs_monotonic; assumption; simp [←WFE.t2l]
    simp [Cq0.hfvs, gl]; clear *-; aesop (add simp sets)
  specialize S2 VT2; obtain ⟨gl2, VT2', VQ2'⟩ := S2
  exists ls1 ∪ gl1, ls2 ∪ gl2; split_ands'
  · obtain ⟨-, -, -, Q1⟩ := Q1 WFE1; trans; swap; assumption
    rw [Set.union_comm, vars_locs_or]; gcongr
  · obtain ⟨-, -, -, Q2⟩ := Q2 WFE1; trans; swap; assumption
    rw [Set.union_comm, vars_locs_or]; gcongr

theorem sem_stp_list:
  sem_stp (G ++ [(.TTop, q0, .self)]) ([#0 ↦ %‖G‖] T1) {✦} ([#0 ↦ %‖G‖] T2) ({✦} ∪ gr) →
  closed_ty 0 ‖G‖ (.TList T2) →
  closed_ql true 0 ‖G‖ q0 →
  gr ⊆ q0 ∪ {%‖G‖} →
  sem_stp G (.TList T1) q0 (.TList T2) q0 :=
by
  intros S C Cq0 _ _; simp; introv WFE ST QP VT VQ
  let gl := vars_locs V q0; exists gl; simp! [WFE.t2l] at C Cq0
  obtain ⟨_, _⟩ := C; have h: ls ∪ gl ⊆ st_locs M := by
    apply Set.union_subset; apply (valt_wf VT).1; trans; assumption
    apply env_type1_store_wf WFE
  apply valt_grow at VT; specialize VT _ h; simp
  cases v <;> simp only [val_type] at VT; rename_i lst _; simp only [val_type]
  obtain ⟨_, _, -, VT⟩ := VT; split_ands'; introv h
  specialize VT _ h; have WFE1 := by
    have: env_cell M V {%‖V‖} ‖V‖ .TTop q0 .self (.vlist lst) vtnone (ls ∪ gl) := by
      simp [gl]; split_ands'; simpa [val_type]
      intro h; specialize VQ h; apply Set.union_subset; assumption; simp
    apply envt1_extend_stub WFE _ _ _ this; exact ∅
    simp; simp [st_chain]; simp [WFE.v2l]
  simp at WFE1; obtain ⟨ls1, _, VT⟩ := VT
  -- start subtyping
  simp only [WFE.t2l] at S
  specialize S WFE1 ST; simp at S; specialize S _
  · trans; apply vars_locs_monotonic; assumption; simp [←WFE.t2l]
    simp [Cq0.hfvs, gl]; clear *-; aesop (add simp sets)
  specialize S VT; obtain ⟨gl1, VT1', VQ1'⟩ := S
  exists ls1 ∪ gl1; split_ands'; apply Set.union_subset; assumption
  trans; assumption; trans; apply vars_locs_monotonic; assumption
  simp [WFE.t2l, Cq0.hfvs, gl]; clear *-; aesop (add simp sets)

theorem sem_stp_fun:
  closed_ty 0 ‖G‖ (.TFun T1b q1b T2b q2b) →
  closed_ql true 0 ‖G‖ qf0 →
  ✦ ∉ gr1 →
  sem_stp (G ++ [(.TTop, qf0, .self)])
    ([#0 ↦ %‖G‖] T1b) {✦} ([#0 ↦ %‖G‖] T1a) ({✦} ∪ gr1) →
  {#0, ✦} ⊆ q1a ∨ sem_qtp (G ++ [(.TTop, qf0, .self)])
    (gr1 ∪ [#0 ↦ %‖G‖] q1b) ([#0 ↦ %‖G‖] q1a) →
  sem_stp (G ++ [(.TTop, qf0, .self), ([#0 ↦ %‖G‖] T1b, [#0 ↦ %‖G‖] q1b, .var)])
    ([#0 ↦ %‖G‖] [#1 ↦ (%(‖G‖+1), gr1)] T2a) {✦} ([#0 ↦ %‖G‖] [#1 ↦ %(‖G‖+1)] T2b) ({✦} ∪ gr2) →
  sem_qtp (G ++ [(.TTop, qf0, .self), ([#0 ↦ %‖G‖] T1b, [#0 ↦ %‖G‖] q1b, .var)])
    (gr2 ∪ [#0 ↦ %‖G‖] [#1 ↦ (%(‖G‖+1), gr1)] q2a) ([#0 ↦ %‖G‖] [#1 ↦ %(‖G‖+1)] q2b) →
  gr1 ⊆ qf0 ∪ {%‖G‖} →
  gr2 ⊆ qf0 ∪ {%‖G‖, %(‖G‖+1)} →
  sem_stp G (.TFun T1a q1a T2a q2a) qf0 (.TFun T1b q1b T2b q2b) qf0 :=
by
  intros Cb Cqf0 Cgrf S1 Q1 S2 Q2 _ _; dsimp; introv WFE ST
  split_ands; intro h; simp [h]; simp; introv PQF VT1 VQ1; rename' ls => lsf
  let grf' := vars_locs V qf0
  have: lsf ∪ grf' ⊆ pnat ‖M‖ := by
    apply Set.union_subset; apply (valt_wf VT1).1; simp only [grf']
    trans; assumption; apply env_type1_store_wf WFE
  replace VT1 := by
    apply valt_grow (ls' := lsf ∪ grf') VT1; simp; assumption
  have WFE1 := by  -- extend by function
    have: env_cell M V {%‖V‖} ‖V‖ .TTop qf0 .self v vtnone (lsf ∪ grf') := by
      simp; split_ands; simp!; rwa [←WFE.t2l]
      simpa [val_type]; intro h1 h2; apply Set.union_subset
      trans; apply VQ1 h1; simp; simp [grf']; simp [grf']
    apply envt1_extend_stub WFE _ _ _ this; exact ∅
    simp; simp [st_chain]; rw [WFE.v2l]
  cases v <;> simp only [val_type] at VT1; exists grf'; split_ands; simp [grf']
  rw [WFE.t2l] at Cb; cases Cb; simp only [val_type]; split_ands''
  rename_i VT1; introv CH ST' VX QX
  replace WFE1 := by  -- store change
    simp at WFE1; apply envt1_store_change (M' := M') WFE1; apply stchain_tighten CH
    apply lls_mono; simp
  replace this: lsf ∪ grf' ⊆ pnat ‖M'‖ := by
    simp [st_chain] at CH; trans; swap; exact CH.2.1
    intro _ h; apply lls_z; exact h
  have Cgr1: closed_ql false 0 (‖G‖+1) gr1 := by
    apply closedql_fr_tighten; assumption; simp [closed_ql]; trans; assumption
    apply Finset.union_subset; trans; assumption; simp; simp
  -- apply the function
  simp only [WFE.t2l] at S1 Q1
  let gr1' := vars_locs (V ++ [(vtnone, lsf ∪ grf')]) gr1
  have Hgr1': gr1' ⊆ lsf ∪ grf' := by
    simp [gr1']; trans; apply vars_locs_monotonic; change _ ⊆ qf0 ∪ ?_; assumption
    simp [WFE.t2l]; rw [vars_locs_shrink]; simp [grf', sets]; clear *-; tauto
    rw [←WFE.t2l]; apply Cqf0.hfvs
  simp at S1; specialize S1 WFE1 ST' _ VX
  · simp; simpa [gr1'] using Hgr1'
  obtain ⟨gr1'', Hgr1'', VX'⟩ := S1
  replace VX' := valt_grow (ls' := lsx ∪ gr1') VX' ?_ ?_  -- make it larger, for valt_substq
  rotate_left; gcongr; apply Set.union_subset; apply (valt_wf VX).1; trans; assumption'
  specialize VT1 CH ST' VX' _; trans ?_ ∪ gr1'; gcongr; assumption; simp [gr1']
  obtain Q1 | Q1 := Q1
  · intro _ h; simp [sets] at Q1; simp [Q1, subst]; clear *-; tauto
  · obtain ⟨Q1a, -, -, Q1b⟩ := Q1 WFE1
    simp at Q1b; simp [subst] at Q1a; clear * - Q1a Q1b; aesop (add simp sets)
  -- extend by argument
  clear Q1 VX' Hgr1'' gr1''
  have WFE2 := by
    have: env_cell M' (V ++ [(vtnone, lsf ∪ grf')]) {%(‖V‖+1)} (‖V‖+1)
        ([#0 ↦ %‖V‖] T1b) ([#0 ↦ %‖V‖] q1b) .var vx vtnone lsx := by
      simp; split_ands'; c_subst; c_extend; c_subst; c_extend;
      intro h; simp [subst] at h; simpa [h] using QX
    apply envt1_extend_stub WFE1 _ _ _ this; exact {%‖V‖}
    simp; simp [st_chain]; apply lls_closed'; assumption'; simp [WFE.v2l]
  obtain ⟨S'', M'', vy, lsy, _, _, ST2, SE2, VY, QY⟩ := VT1
  replace WFE2 := by
    apply envt1_store_change (M' := M'') WFE2
    apply stchain_tighten; assumption; apply lls_closed' ST'; simp
    apply Set.union_subset; assumption; apply (valt_wf VX).1
  -- convert valty, qualy
  simp only [WFE.t2l, List.append_assoc] at S2 Q2 WFE2; specialize Q2 WFE2
  have: vars_locs (V ++ [(vtnone, lsf ∪ grf')] ++ [(vtnone, lsx)]) gr1 = gr1' := by
    rw [vars_locs_shrink]; simp [← WFE.t2l]; exact Cgr1.hfvs
  simp at this S2; specialize S2 WFE2 ST2 _ (v := vy) (ls := lsy) _
  · trans; apply vars_locs_monotonic; assumption
    simp [Finset.insert_eq, WFE.t2l]; rw [vars_locs_shrink]
    simp [grf', sets]; clear *-; tauto; rw [←WFE.t2l]; apply Cqf0.hfvs
  · simp; rw [←ty.subst_open_chain #1 %(‖V‖+1), ty.open_subst_comm, valt_subst]
    convert VY; simp [this, val_type, vtnone]
    rfl; simp; simp!
    simp [closed_ql, sets, ←WFE.t2l]; apply closedql_extend Cgr1 <;> simp
    assumption; simp; simp; intro; c_free; simp!; simp; c_free;
  obtain ⟨gr2', Hgr2, VY'⟩ := S2; obtain ⟨Q2a, -, -, Q2b⟩ := Q2
  simp [subst] at Q2a; simp at Q2b Hgr2
  rw [←ql.subst_chain #1 %(‖V‖+1), ql.subst_comm, vars_locs_subst (vt := vtnone)] at Q2b
  simp [this] at Q2b; rotate_left
  simp; simp [closed_ql, sets, ←WFE.t2l]; apply closedql_extend Cgr1 <;> simp
  simp; simp; c_free; simp; c_free;
  -- finally, supply all the witnesses
  exists S'', M'', vy, lsy ∪ gr2'; split_ands'
  · apply se_sub SE2; clear * - Hgr1'; aesop (add simp sets)
  · trans ?_ ∪ ?_; gcongr <;> assumption; clear * - Q2a Q2b; aesop (add simp sets)

theorem sem_stp_tvar:
  G[x]? = some (Tx, qx, .tvar) →
  sem_stp G (.TVar (%x)) q Tx q :=
by
  intro h; simp; introv WFE ST C VT VQ; exists ∅; simp; simp [val_type] at VT
  obtain ⟨_, vt, ⟨ls0, h1⟩, VT⟩ := VT; have := WFE.byV h1; simp [h] at this
  obtain ⟨_, _, _, _, VT1, -⟩ := this
  apply VT1; assumption; apply VT; simp
  simp [st_chain]; apply lls_closed'; assumption'

theorem sem_stp_all:
  closed_ty 0 ‖G‖ (.TAll T1b q1b T2b q2b) →
  closed_ql true 0 ‖G‖ qf0 →
  sem_stp (G ++ [(.TTop, qf0, .self)])
    ([#0 ↦ %‖G‖] T1b) {✦} ([#0 ↦ %‖G‖] T1a) {✦} →
  {#0, ✦} ⊆ q1a ∨ sem_qtp (G ++ [(.TTop, qf0, .self)])
    ([#0 ↦ %‖G‖] q1b) ([#0 ↦ %‖G‖] q1a) →
  sem_stp (G ++ [(.TTop, qf0, .self), ([#0 ↦ %‖G‖] T1b, [#0 ↦ %‖G‖] q1b, .tvar)])
    ([#0 ↦ %‖G‖] [#1 ↦ %(‖G‖+1)] T2a) {✦} ([#0 ↦ %‖G‖] [#1 ↦ %(‖G‖+1)] T2b) ({✦} ∪ gr2) →
  sem_qtp (G ++ [(.TTop, qf0, .self), ([#0 ↦ %‖G‖] T1b, [#0 ↦ %‖G‖] q1b, .tvar)])
    (gr2 ∪ [#0 ↦ %‖G‖] [#1 ↦ %(‖G‖+1)] q2a) ([#0 ↦ %‖G‖] [#1 ↦ %(‖G‖+1)] q2b) →
  gr2 ⊆ qf0 ∪ {%‖G‖, %(‖G‖+1)} →
  sem_stp G (.TAll T1a q1a T2a q2a) qf0 (.TAll T1b q1b T2b q2b) qf0 :=
by
  intros Cb Cqf0 S1 Q1 S2 Q2 _; dsimp; introv WFE ST;
  split_ands; intro h; simp [h]; simp; introv PQF VT1 VQ1; rename' ls => lsf
  let grf' := vars_locs V qf0
  have: lsf ∪ grf' ⊆ pnat ‖M‖ := by
    apply Set.union_subset; apply (valt_wf VT1).1; simp only [grf']
    trans; assumption; apply env_type1_store_wf WFE
  replace VT1 := by
    apply valt_grow (ls' := lsf ∪ grf') VT1; simp; assumption
  have WFE1 := by  -- extend by function
    have: env_cell M V {%‖V‖} ‖V‖ .TTop qf0 .self v vtnone (lsf ∪ grf') := by
      simp; split_ands; simp!; rwa [←WFE.t2l]
      simpa [val_type]; intro h1 h2; apply Set.union_subset
      trans; apply VQ1 h1; simp; simp [grf']; simp [grf']
    apply envt1_extend_stub WFE _ _ _ this; exact ∅
    simp; simp [st_chain]; rw [WFE.v2l]
  cases v <;> simp only [val_type] at VT1; exists grf'; split_ands; simp [grf']
  rw [WFE.t2l] at Cb; cases Cb; simp only [val_type]; split_ands''
  rename_i VT1; introv CH ST' VX VX' QX
  replace WFE1 := by  -- store change
    simp at WFE1; apply envt1_store_change (M' := M') WFE1; apply stchain_tighten CH
    apply lls_mono; simp
  replace this: lsf ∪ grf' ⊆ pnat ‖M'‖ := by
    simp [st_chain] at CH; trans; swap; exact CH.2.1
    intro _ h; apply lls_z; exact h
  -- apply the function
  simp only [WFE.t2l] at S1 Q1
  specialize VT1 (vt := vt) (lsx := lsx) CH ST' _ VX' _
  · introv ST VT; replace WFE1 := by
      apply envt1_store_change (M' := M); apply envt1_tighten (p' := ∅)
      exact WFE1; simp; simp [st_chain]
    specialize S1 WFE1 ST; simp at S1; apply S1; apply VX; assumption'
  · trans; exact QX; obtain Q1 | Q1 := Q1
    · intro _ h; simp [sets] at Q1; simp [Q1, subst]; clear *-; tauto
    · obtain ⟨Q1a, -, -, Q1b⟩ := Q1 WFE1
      gcongr; simp [sets]; simp [subst] at Q1a; clear *- Q1a; tauto
  -- extend by argument
  have WFE2 := by
    have: env_cell M' (V ++ [(vtnone, lsf ∪ grf')]) {%(‖V‖+1)} (‖V‖+1)
        ([#0 ↦ %‖V‖] T1b) ([#0 ↦ %‖V‖] q1b) .tvar (.vnat 0) vt lsx := by
      simp; split_ands'; c_subst; c_extend; c_subst; c_extend;
      simpa [val_type]; intro h; simp [subst] at h; simpa [h] using QX
    apply envt1_extend_stub WFE1 _ _ _ this; exact {%‖V‖}
    simp; simp [st_chain]; apply lls_closed'; assumption'; simp [WFE.v2l]
  obtain ⟨S'', M'', vy, lsy, _, _, ST2, SE2, VY, QY⟩ := VT1
  replace WFE2 := by
    apply envt1_store_change (M' := M'') WFE2
    apply stchain_tighten; assumption; apply lls_closed' ST'
    simp; apply Set.union_subset; assumption'
  -- convert valty, qualy
  simp only [WFE.t2l, List.append_assoc] at S2 Q2 WFE2; specialize Q2 WFE2
  simp at this S2; specialize S2 WFE2 ST2 _ (v := vy) (ls := lsy) _
  · trans; apply vars_locs_monotonic; assumption
    simp [Finset.insert_eq, WFE.t2l]
    rw [vars_locs_shrink]; simp [grf', sets]; clear *-; tauto;
    rw [←WFE.t2l]; apply Cqf0.hfvs
  · simpa
  obtain ⟨gr2', Hgr2, VY'⟩ := S2; obtain ⟨Q2a, -, -, Q2b⟩ := Q2
  simp [subst] at Q2a; simp at Q2b Hgr2
  -- finally, supply all the witnesses
  exists S'', M'', vy, lsy ∪ gr2'; split_ands'
  trans ?_ ∪ ?_; gcongr <;> assumption; clear * - Q2a Q2b; aesop (add simp sets)
