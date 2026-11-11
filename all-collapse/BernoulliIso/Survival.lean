module

public import BernoulliIso.Recovery
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
Countably many coordinates are all recovered almost surely under a strict
uniform contraction of their survival probabilities. This proves the
probability-to-injectivity implication. The adaptive finite-support estimate
supplying the contraction is proved separately in Selection.lean; its
concrete marker-law inputs still need to be supplied.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace BernoulliIso

variable {Ω I : Type*} [MeasurableSpace Ω] [Countable I]

/-- A geometric upper bound forces eventual death for every member of a
countable family. Monotonicity of the bad events is not needed here. -/
theorem ae_all_eventually_good (μ : Measure Ω) (bad : I → ℕ → Set Ω)
    {c : ℝ≥0∞} (hc : c < 1)
    (hbound : ∀ i n, μ (bad i n) ≤ c ^ n) :
    ∀ᵐ ω ∂μ, ∀ i, ∃ n, ω ∉ bad i n := by
  apply ae_all_iff.2
  intro i
  have hz : μ (⋂ n, bad i n) = 0 := by
    apply le_antisymm _ zero_le
    apply ge_of_tendsto (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hc)
    exact Filter.Eventually.of_forall fun n =>
      (measure_mono (Set.iInter_subset (bad i) n)).trans (hbound i n)
  have ha : ∀ᵐ ω ∂μ, ω ∉ ⋂ n, bad i n :=
    (measure_eq_zero_iff_ae_notMem).1 hz
  simpa only [Set.mem_iInter, not_forall] using ha

omit [Countable I] in
/-- Derive geometric decay from a one-step contraction. -/
theorem survival_bound (μ : Measure Ω) [IsProbabilityMeasure μ]
    (bad : I → ℕ → Set Ω) {c : ℝ≥0∞}
    (hstep : ∀ i n, μ (bad i (n + 1)) ≤ c * μ (bad i n)) :
    ∀ i n, μ (bad i n) ≤ c ^ n := by
  intro i n
  induction n with
  | zero => simpa only [pow_zero] using (prob_le_one (μ := μ) (s := bad i 0))
  | succ n ih =>
    calc
      μ (bad i (n + 1)) ≤ c * μ (bad i n) := hstep i n
      _ ≤ c * c ^ n := mul_le_mul_right ih c
      _ = c ^ (n + 1) := (pow_succ' c n).symm

variable {K : Type*} [Ring K] {X Y : ℕ → Type*}
  [∀ n, AddCommGroup (X n)] [∀ n, AddCommGroup (Y n)]
  [∀ n, Module K (X n)] [∀ n, Module K (Y n)]

/-- Central conditional theorem: a random exact linear extraction tower
whose coordinate-survival probabilities contract has an injective infinite
extraction for almost every marker. Every missing probabilistic input is
visible in `hstep`; there is no assumed infinite injectivity. -/
theorem ae_extract_injective_of_contraction
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (tower : Ω → ExtractionTower K X Y)
    (obs : I → X 0 →ₗ[K] K)
    (separates : ∀ x y : X 0, (∀ i, obs i x = obs i y) → x = y)
    {c : ℝ≥0∞} (hc : c < 1)
    (hstep : ∀ i n,
      μ {ω | ∃ z : X (n + 1), obs i ((tower ω).prefixSection (n + 1) z) ≠ 0}
        ≤ c * μ {ω | ∃ z : X n, obs i ((tower ω).prefixSection n z) ≠ 0}) :
    ∀ᵐ ω ∂μ, Function.Injective (tower ω).extract := by
  let bad : I → ℕ → Set Ω := fun i n =>
    {ω | ∃ z : X n, obs i ((tower ω).prefixSection n z) ≠ 0}
  have hb : ∀ i n, μ (bad i n) ≤ c ^ n := survival_bound μ bad hstep
  have he := ae_all_eventually_good μ bad hc hb
  filter_upwards [he] with ω hω
  apply (tower ω).extract_injective_of_exhaustion obs separates
  intro i
  obtain ⟨n, hn⟩ := hω i
  refine ⟨n, ?_⟩
  intro z
  by_contra hz
  exact hn ⟨z, hz⟩

end BernoulliIso

#print axioms BernoulliIso.ae_all_eventually_good
#print axioms BernoulliIso.ae_extract_injective_of_contraction
