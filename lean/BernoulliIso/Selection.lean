module

public import BernoulliIso.CompactExtraction

/-!
Adaptive finite-support selection. The support may depend arbitrarily on the
past. Freshness is tested against its countably many fibers, and no joint
independence between the selected-coordinate events is required.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace BernoulliIso

variable {Ω A : Type*} [MeasurableSpace Ω] [Countable A]

omit [Countable A] in
/-- A finite union estimate after restriction to any past event. -/
theorem finite_selection_bound (μ : Measure Ω) (s : Finset A)
    (past : Set Ω) (selected : A → Set Ω) {p : ℝ≥0∞}
    (hfresh : ∀ a ∈ s, μ (past ∩ selected a) ≤ p * μ past) :
    μ (past ∩ {ω | ∃ a ∈ s, ω ∈ selected a}) ≤
      s.card * p * μ past := by
  classical
  have heq : past ∩ {ω | ∃ a ∈ s, ω ∈ selected a} =
      ⋃ a ∈ s, past ∩ selected a := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_iUnion]
    aesop
  rw [heq]
  calc
    μ (⋃ a ∈ s, past ∩ selected a) ≤ ∑ a ∈ s, μ (past ∩ selected a) :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑ _a ∈ s, p * μ past := Finset.sum_le_sum hfresh
    _ = s.card * p * μ past := by simp [mul_assoc]

omit [Countable A] in
/-- Equal probabilities for all outcomes of a finite selector give the
exact reciprocal-cardinality law, even after restricting to a past event.
This makes the finite uniformity input explicit, including null past events. -/
theorem uniform_selection_on_event (μ : Measure Ω) {L : ℕ}
    (hL : 0 < L) (past : Set Ω) (choice : Ω → Fin L)
    (hmeas : ∀ j, MeasurableSet (past ∩ {ω | choice ω = j}))
    (hsym : ∀ j k, μ (past ∩ {ω | choice ω = j}) =
      μ (past ∩ {ω | choice ω = k})) (j : Fin L) :
    μ (past ∩ {ω | choice ω = j}) = (L : ℝ≥0∞)⁻¹ * μ past := by
  let fiber : Fin L → Set Ω := fun k => past ∩ {ω | choice ω = k}
  have hcover : past = ⋃ k, fiber k := by
    ext ω
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq, fiber]
    exact ⟨fun h => ⟨choice ω, h, rfl⟩, fun ⟨_, h, _⟩ => h⟩
  have hdisjoint : Pairwise (fun k l => Disjoint (fiber k) (fiber l)) := by
    intro k l hkl
    apply Set.disjoint_left.2
    intro ω hk hl
    exact hkl (hk.2.symm.trans hl.2)
  have hsum : μ past = (L : ℝ≥0∞) * μ (fiber j) := by
    rw [hcover, measure_iUnion hdisjoint hmeas, tsum_fintype]
    calc
      ∑ k : Fin L, μ (fiber k) = ∑ _k : Fin L, μ (fiber j) :=
        Finset.sum_congr rfl (fun k _ => hsym k j)
      _ = (L : ℝ≥0∞) * μ (fiber j) := by simp
  have heq : μ (fiber j) = μ past / (L : ℝ≥0∞) :=
    (ENNReal.eq_div_iff (by exact_mod_cast hL.ne') (by simp)).2 hsum.symm
  simpa [fiber, ENNReal.div_eq_inv_mul] using heq

/-- A countable-valued adaptive support has a one-step survival bound.
Freshness is only a single-coordinate bound on each support fiber, not an
assumption of the desired union bound or contraction. -/
theorem adaptive_selection_bound (μ : Measure Ω)
    (support : Ω → Finset A) (selected : A → Set Ω)
    (hmeas : ∀ s, MeasurableSet {ω | support ω = s})
    {R : ℕ} {p : ℝ≥0∞}
    (hcard : ∀ ω, (support ω).card ≤ R)
    (hfresh : ∀ s a, a ∈ s →
      μ ({ω | support ω = s} ∩ selected a) ≤ p * μ {ω | support ω = s}) :
    μ {ω | ∃ a ∈ support ω, ω ∈ selected a} ≤
      R * p * μ {ω | (support ω).Nonempty} := by
  classical
  let S := {s : Finset A // s.Nonempty}
  let fiber : S → Set Ω := fun s => {ω | support ω = s.val}
  let hit : S → Set Ω := fun s => fiber s ∩ {ω | ∃ a ∈ s.val, ω ∈ selected a}
  have hcover : {ω | ∃ a ∈ support ω, ω ∈ selected a} = ⋃ s : S, hit s := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, hit, fiber, Set.mem_inter_iff]
    constructor
    · rintro ⟨a, ha, hsel⟩
      exact ⟨⟨support ω, ⟨a, ha⟩⟩, rfl, a, ha, hsel⟩
    · rintro ⟨s, hs, a, ha, hsel⟩
      exact ⟨a, hs ▸ ha, hsel⟩
  have halive : {ω | (support ω).Nonempty} = ⋃ s : S, fiber s := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, fiber]
    constructor
    · intro h
      exact ⟨⟨support ω, h⟩, rfl⟩
    · rintro ⟨s, hs⟩
      exact hs ▸ s.property
  have hdisjoint : Pairwise (fun s t => Disjoint (fiber s) (fiber t)) := by
    intro s t hst
    apply Set.disjoint_left.2
    intro ω hs ht
    exact hst (Subtype.ext (hs.symm.trans ht))
  have hbound : ∀ s : S, μ (hit s) ≤ R * p * μ (fiber s) := by
    intro s
    by_cases hn : (fiber s).Nonempty
    · obtain ⟨ω, hω⟩ := hn
      have hc : s.val.card ≤ R := hω ▸ hcard ω
      have hcE : (s.val.card : ℝ≥0∞) ≤ (R : ℝ≥0∞) := by exact_mod_cast hc
      exact (finite_selection_bound μ s.val (fiber s) selected
        (fun a ha => hfresh s.val a ha)).trans
        (mul_le_mul' (mul_le_mul' hcE le_rfl) le_rfl)
    · have he : fiber s = ∅ := Set.not_nonempty_iff_eq_empty.1 hn
      simp [hit, he]
  calc
    μ {ω | ∃ a ∈ support ω, ω ∈ selected a} = μ (⋃ s : S, hit s) := by rw [hcover]
    _ ≤ ∑' s : S, μ (hit s) := measure_iUnion_le _
    _ ≤ ∑' s : S, R * p * μ (fiber s) := ENNReal.tsum_le_tsum hbound
    _ = R * p * ∑' s : S, μ (fiber s) := ENNReal.tsum_mul_left
    _ = R * p * μ {ω | (support ω).Nonempty} := by
      rw [halive, measure_iUnion hdisjoint (fun s => hmeas s.val)]

/-- A finite uniform-selector version of the adaptive bound. Symmetry
on every support fiber supplies freshness, so the reciprocal-cardinality
law is derived rather than assumed. -/
theorem adaptive_uniform_selection_bound (μ : Measure Ω)
    (support : Ω → Finset A) {L R : ℕ} (hL : 0 < L)
    (choice : A → Ω → Fin L) (target : A → Fin L)
    (hsupport : ∀ s, MeasurableSet {ω | support ω = s})
    (hchoice : ∀ s a j,
      MeasurableSet ({ω | support ω = s} ∩ {ω | choice a ω = j}))
    (hsym : ∀ s a j k,
      μ ({ω | support ω = s} ∩ {ω | choice a ω = j}) =
        μ ({ω | support ω = s} ∩ {ω | choice a ω = k}))
    (hcard : ∀ ω, (support ω).card ≤ R) :
    μ {ω | ∃ a ∈ support ω, choice a ω = target a} ≤
      R * (L : ℝ≥0∞)⁻¹ * μ {ω | (support ω).Nonempty} := by
  apply adaptive_selection_bound μ support (fun a => {ω | choice a ω = target a})
    hsupport hcard
  intro s a _ha
  exact (uniform_selection_on_event μ hL {ω | support ω = s} (choice a)
    (hchoice s a) (hsym s a) (target a)).le

omit [Countable A] in
/-- A nonzero finite row after insertion must use a selected site.
The post-insertion input is arbitrary: no subsequent algebraic operation
can revive a row killed by insertion. -/
theorem finite_row_survival_requires_selection {K V : Type*} [Semiring K]
    (s : Finset A) (coefficient : A → K) (insert : V → A → K)
    (selected : A → Prop)
    (hzero : ∀ a, ¬ selected a → ∀ v, insert v a = 0)
    (v : V) (hsurvive : ∑ a ∈ s, coefficient a * insert v a ≠ 0) :
    ∃ a ∈ s, selected a := by
  classical
  by_contra h
  apply hsurvive
  apply Finset.sum_eq_zero
  intro a ha
  have hn : ¬ selected a := fun hsel => h ⟨a, ha, hsel⟩
  rw [hzero a hn v, mul_zero]

/-- Event-level contraction derived from adaptive support selection. The
support need not have a deterministic location, and selected events may be
arbitrarily dependent on one another. -/
theorem survival_step_of_adaptive_selection (μ : Measure Ω)
    (support : Ω → Finset A) (selected : A → Set Ω)
    (current next : Set Ω)
    (hmeas : ∀ s, MeasurableSet {ω | support ω = s})
    {R : ℕ} {p c : ℝ≥0∞}
    (hcard : ∀ ω, (support ω).card ≤ R)
    (hfresh : ∀ s a, a ∈ s →
      μ ({ω | support ω = s} ∩ selected a) ≤ p * μ {ω | support ω = s})
    (hcurrent : {ω | (support ω).Nonempty} ⊆ current)
    (hnext : next ⊆ {ω | ∃ a ∈ support ω, ω ∈ selected a})
    (hratio : R * p ≤ c) :
    μ next ≤ c * μ current := by
  calc
    μ next ≤ μ {ω | ∃ a ∈ support ω, ω ∈ selected a} := measure_mono hnext
    _ ≤ R * p * μ {ω | (support ω).Nonempty} :=
      adaptive_selection_bound μ support selected hmeas hcard hfresh
    _ ≤ c * μ current := mul_le_mul' hratio (measure_mono hcurrent)

/-- Choosing at least twice as many sites as the row can meet forces
contraction by one half. -/
theorem selection_ratio_le_half {R L : ℕ} (hL : 0 < L) (hsize : 2 * R ≤ L) :
    (R : ℝ≥0∞) * (L : ℝ≥0∞)⁻¹ ≤ (2 : ℝ≥0∞)⁻¹ := by
  rw [← div_eq_mul_inv, ENNReal.div_le_iff (by exact_mod_cast hL.ne') (by simp)]
  rw [mul_comm, ← div_eq_mul_inv, ENNReal.le_div_iff_mul_le (by simp) (by simp)]
  exact_mod_cast (by omega : R * 2 ≤ L)

variable {I : Type*} [Countable I]
variable {K : Type*} [Ring K] {X Y : ℕ → Type*}
  [∀ n, AddCommGroup (X n)] [∀ n, AddCommGroup (Y n)]
  [∀ n, Module K (X n)] [∀ n, Module K (Y n)]
  [TopologicalSpace (X 0)] [CompactSpace (X 0)]
  [∀ n, TopologicalSpace (Y n)] [∀ n, T2Space (Y n)]

/-- The certified extraction theorem with its former contraction premise
replaced by finite-support geometry and one-site freshness. Concrete row
supports, fresh marker selection, and the tower are still inputs. -/
theorem ae_extract_bijective_of_adaptive_selection
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (tower : Ω → ExtractionTower K X Y)
    (hcont : ∀ ω n, Continuous ((tower ω).output n))
    (obs : I → X 0 →ₗ[K] K)
    (separates : ∀ x y : X 0, (∀ i, obs i x = obs i y) → x = y)
    (support : I → ℕ → Ω → Finset A)
    (selected : ℕ → A → Set Ω)
    (R L : ℕ → ℕ)
    (hL : ∀ n, 0 < L n)
    (hsize : ∀ n, 2 * R n ≤ L n)
    (hmeas : ∀ i n s, MeasurableSet {ω | support i n ω = s})
    (hcard : ∀ i n ω, (support i n ω).card ≤ R n)
    (hfresh : ∀ i n s a, a ∈ s →
      μ ({ω | support i n ω = s} ∩ selected n a) ≤
        (L n : ℝ≥0∞)⁻¹ * μ {ω | support i n ω = s})
    (hcurrent : ∀ i n ω, (support i n ω).Nonempty →
      ∃ z : X n, obs i ((tower ω).prefixSection n z) ≠ 0)
    (hnext : ∀ i n ω,
      (∃ z : X (n + 1), obs i ((tower ω).prefixSection (n + 1) z) ≠ 0) →
      ∃ a ∈ support i n ω, ω ∈ selected n a) :
    ∀ᵐ ω ∂μ, Function.Bijective (tower ω).extract := by
  apply ae_extract_bijective_of_contraction μ tower hcont obs separates
    (c := (2 : ℝ≥0∞)⁻¹) (by norm_num)
  intro i n
  exact survival_step_of_adaptive_selection μ (support i n) (selected n)
    _ _ (hmeas i n) (hcard i n) (hfresh i n) (hcurrent i n) (hnext i n)
    (selection_ratio_le_half (hL n) (hsize n))

end BernoulliIso
