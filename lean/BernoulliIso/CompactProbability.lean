module

public import BernoulliIso.InputOperators
public import Mathlib.MeasureTheory.Measure.Haar.Basic

/-! Actual normalized Haar laws for the compact residual groups. -/

@[expose] public section
noncomputable section
open MeasureTheory TopologicalSpace

namespace BernoulliIso

variable (Z : Type*) [AddCommGroup Z] [TopologicalSpace Z] [CompactSpace Z]
  [IsTopologicalAddGroup Z] [MeasurableSpace Z] [BorelSpace Z]

def compactHaar : Measure Z :=
  Measure.addHaarMeasure (⟨⟨Set.univ, isCompact_univ⟩, by simp⟩ : PositiveCompacts Z)

instance compactHaar_isProbabilityMeasure : IsProbabilityMeasure (compactHaar Z) where
  measure_univ := Measure.addHaarMeasure_self

instance compactHaar_isAddHaarMeasure : (compactHaar Z).IsAddHaarMeasure :=
  inferInstanceAs (Measure.IsAddHaarMeasure (Measure.addHaarMeasure _))

namespace AlgebraicInput

variable {K N I V G : Type*} [Field K] [Finite K]
  [Group N] [Countable N] [Fintype I] [Fintype V] [Nonempty I] [Nonempty V] [Group G]
variable (s : AlgebraicInput K N I V) (H : Subgroup G) (ι : N →* G)
  (commutes : ∀ h ∈ H, ∀ n, Commute h (ι n))
variable [TopologicalSpace K] [T2Space K] [IsTopologicalRing K]

theorem residual_isClosed :
    IsClosed ((s.concreteSplit H ι commutes).Q.range : Set (V → G ⧸ H → K)) := by
  have heq : ((s.concreteSplit H ι commutes).Q.range : Set (V → G ⧸ H → K)) =
      {f | (s.concreteSplit H ι commutes).Q f = f} := by
    ext f
    exact (s.concreteSplit H ι commutes).mem_Q_range_iff f
  rw [heq]
  exact isClosed_eq (s.continuous_Q H ι commutes) continuous_id

instance residual_compactSpace : CompactSpace (s.residual H ι commutes) :=
  isCompact_iff_compactSpace.mp (s.residual_isClosed H ι commutes).isCompact

variable [MeasurableSpace K] [BorelSpace K] [BorelSpace (V → G ⧸ H → K)]

def residualLaw : Measure (s.residual H ι commutes) := compactHaar _

instance residualLaw_isProbabilityMeasure : IsProbabilityMeasure (s.residualLaw H ι commutes) :=
  inferInstanceAs (IsProbabilityMeasure (compactHaar _))

instance residualLaw_isAddHaarMeasure : (s.residualLaw H ι commutes).IsAddHaarMeasure :=
  inferInstanceAs (Measure.IsAddHaarMeasure (compactHaar _))

end AlgebraicInput
end BernoulliIso
