module

public import BernoulliIso.Survival
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Separation.Hausdorff

/-!
The compactness step upgrading finite-prefix surjectivity to surjectivity
of the full extraction, and its combination with almost-sure recovery.
No Haar-measure, joint-measurability, or equivariance conclusion is claimed.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace BernoulliIso

variable {K : Type*} [Ring K] {X Y : ℕ → Type*}
  [∀ n, AddCommGroup (X n)] [∀ n, AddCommGroup (Y n)]
  [∀ n, Module K (X n)] [∀ n, Module K (Y n)]
  [TopologicalSpace (X 0)] [CompactSpace (X 0)]
  [∀ n, TopologicalSpace (Y n)] [∀ n, T2Space (Y n)]

/-- A continuous exact extraction tower over a compact source is onto its
infinite output product, regardless of whether recovery holds. -/
theorem ExtractionTower.extract_surjective
    (t : ExtractionTower K X Y) (hcont : ∀ n, Continuous (t.output n)) :
    Function.Surjective t.extract := by
  intro y
  let S : ℕ → Set (X 0) := fun n => {x | ∀ m, m < n → t.output m x = y m}
  have hclosed : ∀ n, IsClosed (S n) := by
    intro n
    have hs : S n = ⋂ m, ⋂ (_ : m < n), {x | t.output m x = y m} := by
      ext x
      simp [S]
    rw [hs]
    exact isClosed_iInter fun m => isClosed_iInter fun _ =>
      isClosed_eq (hcont m) continuous_const
  have hnonempty : ∀ n, (S n).Nonempty := by
    intro n
    obtain ⟨x, _, hx⟩ := t.exists_remainder_and_prefix y n 0
    exact ⟨x, hx⟩
  have hdecreasing : ∀ n, S (n + 1) ⊆ S n := by
    intro n x hx m hm
    exact hx m (Nat.lt_trans hm (Nat.lt_succ_self n))
  obtain ⟨x, hx⟩ :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      S hdecreasing hnonempty (hclosed 0).isCompact hclosed
  refine ⟨x, ?_⟩
  funext m
  exact (Set.mem_iInter.1 hx (m + 1)) m (Nat.lt_succ_self m)

variable {Ω I : Type*} [MeasurableSpace Ω] [Countable I]

/-- The certified exhaustion theorem: under an explicit contraction bound,
the infinite extraction is bijective for almost every marker. The tower
and its continuous finite outputs are inputs; their realization by the
group construction remains outside this certified fragment. -/
theorem ae_extract_bijective_of_contraction
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (tower : Ω → ExtractionTower K X Y)
    (hcont : ∀ ω n, Continuous ((tower ω).output n))
    (obs : I → X 0 →ₗ[K] K)
    (separates : ∀ x y : X 0, (∀ i, obs i x = obs i y) → x = y)
    {c : ℝ≥0∞} (hc : c < 1)
    (hstep : ∀ i n,
      μ {ω | ∃ z : X (n + 1), obs i ((tower ω).prefixSection (n + 1) z) ≠ 0}
        ≤ c * μ {ω | ∃ z : X n, obs i ((tower ω).prefixSection n z) ≠ 0}) :
    ∀ᵐ ω ∂μ, Function.Bijective (tower ω).extract := by
  filter_upwards [ae_extract_injective_of_contraction μ tower obs separates hc hstep]
    with ω hω
  exact ⟨hω, (tower ω).extract_surjective (hcont ω)⟩

end BernoulliIso

#print axioms BernoulliIso.ExtractionTower.extract_surjective
#print axioms BernoulliIso.ae_extract_bijective_of_contraction
