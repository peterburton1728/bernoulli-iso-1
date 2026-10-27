module

public import BernoulliIso.ConcreteRecovery
public import BernoulliIso.ConcreteRegularity
public import BernoulliIso.ConcreteDynamics
public import BernoulliIso.MarkerDynamics
public import BernoulliIso.ConcreteReservoir

/-! The shared invariant conull recovery-marker domain and the concrete
relative extraction isomorphism over that domain. -/

@[expose] public section
noncomputable section
open MeasureTheory

namespace BernoulliIso.AlgebraicInput

variable {K N I V : Type*} [Field K] [Fintype K]
  [Group N] [Countable N] [Fintype I] [Fintype V] [Nonempty I] [Nonempty V]
variable (s : AlgebraicInput K N I V)
  [MeasurableSpace K] [MeasurableSingletonClass K] [LinearOrder K]

def shiftedMarker (g : Ambient.G N) (ω : s.markerSpace) : s.markerSpace :=
  ⟨MarkerGeometry.markerShift g ω.val, (Ambient.markerGeometry N).goodMarker_shift g ω.property⟩

theorem concreteMarkerLaw_preserving (g : Ambient.G N) :
    MeasurePreserving (s.shiftedMarker g) s.concreteMarkerLaw s.concreteMarkerLaw :=
  MarkerGeometry.measurePreserving_goodMarkerShift (Ambient.markerGeometry N) g

theorem exists_concreteRecoverySet :
    ∃ E : Set s.markerSpace, MeasurableSet E ∧ (∀ᵐ ω ∂s.concreteMarkerLaw, ω ∈ E) ∧
      (∀ (g : Ambient.G N) (ω : s.markerSpace), ω ∈ E → s.shiftedMarker g ω ∈ E) ∧
      (∀ ω ∈ E, Function.Injective (s.concreteTower ω).extract) := by
  letI := s.markerAction
  exact exists_invariant_conull_subset s.concreteMarkerLaw s.concreteMarkerLaw_preserving
    (fun ω => Function.Injective (s.concreteTower ω).extract)
    s.ae_concreteTower_extract_injective

def concreteRecoverySet : Set s.markerSpace := s.exists_concreteRecoverySet.choose

theorem measurable_concreteRecoverySet : MeasurableSet s.concreteRecoverySet :=
  s.exists_concreteRecoverySet.choose_spec.1

theorem ae_concreteRecoverySet : ∀ᵐ ω ∂s.concreteMarkerLaw, ω ∈ s.concreteRecoverySet :=
  s.exists_concreteRecoverySet.choose_spec.2.1

theorem concreteRecoverySet_invariant (g : Ambient.G N) (ω : s.markerSpace)
    (hω : ω ∈ s.concreteRecoverySet) : s.shiftedMarker g ω ∈ s.concreteRecoverySet :=
  s.exists_concreteRecoverySet.choose_spec.2.2.1 g ω hω

theorem concreteRecoverySet_injective (ω : s.concreteRecoverySet) :
    Function.Injective (s.concreteTower ω.val).extract :=
  s.exists_concreteRecoverySet.choose_spec.2.2.2 ω.val ω.property

def concreteRecoveryLaw : Measure s.concreteRecoverySet :=
  s.concreteMarkerLaw.comap Subtype.val

instance concreteRecoveryLaw_probability : IsProbabilityMeasure s.concreteRecoveryLaw :=
  (MeasurableEmbedding.subtype_coe s.measurable_concreteRecoverySet).isProbabilityMeasure_comap
    (by simpa using s.ae_concreteRecoverySet)

theorem concreteRecoveryLaw_inclusion :
    MeasurePreserving (Subtype.val : s.concreteRecoverySet → s.markerSpace)
      s.concreteRecoveryLaw s.concreteMarkerLaw :=
  measurePreserving_conullSubtype _ s.measurable_concreteRecoverySet s.ae_concreteRecoverySet

section Topology

attribute [local irreducible] outputSlots CosetCoordinates.sortedCosetChart
  expandedSplit rangeChart stageSplit stageRegroupChart Regroup.linearEquiv
  FiniteStages.regroupAndRepeat FiniteStages.iterateSplit concreteStage concreteTower
variable [TopologicalSpace K] [DiscreteTopology K] [BorelSpace K] [IsTopologicalRing K]
  [MeasurableSpace V] [MeasurableSingletonClass V]

local instance goodMarker_standardBorel : StandardBorelSpace s.markerSpace :=
  ((Ambient.markerGeometry N).measurable_goodMarker (K := K)).standardBorel

local instance recovery_standardBorel : StandardBorelSpace s.concreteRecoverySet :=
  s.measurable_concreteRecoverySet.standardBorel

local instance residual_standardBorel (H : Subgroup (Ambient.G N))
    (commutes : ∀ h ∈ H, ∀ n, Commute h (Ambient.includeN N n)) :
    StandardBorelSpace (s.residual H (Ambient.includeN N) commutes) :=
  (s.residual_isClosed H (Ambient.includeN N) commutes).measurableSet.standardBorel

local instance stageOutput_standardBorel (n : ℕ) : StandardBorelSpace (s.stageOutput n) := by
  letI := residual_standardBorel s (Ambient.Hseq N (s.stageLevel (n + 1)))
    (s.ambient_commutes (s.stageLevel (n + 1)))
  letI : StandardBorelSpace (s.ambientResiduals (s.stageLevel (n + 1))) := inferInstance
  letI : StandardBorelSpace (s.splitOutput n) := by
    change StandardBorelSpace
      ((Fin s.excess → Ambient.G N ⧸ s.stageH (n + 1) → K) ×
        s.ambientResiduals (s.stageLevel (n + 1)))
    infer_instance
  change StandardBorelSpace
    ((Fin (StageSchedule.repetitions s.rowConstant n) → s.splitOutput n) ×
      (Fin (StageSchedule.discarded s.rowConstant n) → s.stageSpace (n + 1)))
  infer_instance

/-- Restriction of the checked joint output map to the common recovery
marker; stated separately to keep the finite-stage formula opaque. -/
theorem measurable_recoveryOutput (n : ℕ) :
    Measurable (fun p : s.concreteRecoverySet × s.stageSpace 0 =>
      (s.concreteTower p.1.val).output n p.2) := by
  have hcoe : Measurable (fun p : s.concreteRecoverySet × s.stageSpace 0 =>
      ((p.1.val, p.2) : s.markerSpace × s.stageSpace 0)) :=
    (measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd
  exact (s.measurable_concreteOutput n).comp hcoe

/-- Actual relative extraction. Injectivity is supplied for every marker
by the common invariant conull restriction, rather than assumed a.e. here. -/
def concreteExtraction (μ : Measure K) [IsProbabilityMeasure μ] [μ.IsAddHaarMeasure] :
    RelativeProbabilityIso s.concreteRecoverySet (s.stageDataLaw 0 μ)
      (Measure.infinitePi (fun n => s.stageOutputLaw n μ)) := by
  letI (n : ℕ) : SecondCountableTopology (s.stageOutput n) :=
    s.stageOutput_secondCountable n
  letI (n : ℕ) : BorelSpace (s.stageOutput n) := s.stageOutput_borel n
  letI (n : ℕ) : MeasurableAdd (s.stageOutput n) := s.stageOutput_measurableAdd n
  letI (n : ℕ) : StandardBorelSpace (s.stageOutput n) := stageOutput_standardBorel s n
  letI := infinitePi_isAddHaarMeasure (fun n => s.stageOutputLaw n μ)
  exact RelativeProbabilityIso.extraction (K := K) (X := s.stageSpace) (Y := s.stageOutput)
    (fun ω : s.concreteRecoverySet => s.concreteTower ω.val)
    (fun ω n => s.continuous_concreteOutput ω.val n)
    s.measurable_recoveryOutput s.concreteRecoverySet_injective (s.stageDataLaw 0 μ)
    (Measure.infinitePi (fun n => s.stageOutputLaw n μ))

@[simp] theorem concreteExtraction_apply (μ : Measure K)
    [IsProbabilityMeasure μ] [μ.IsAddHaarMeasure]
    (ω : s.concreteRecoverySet) (x : s.stageSpace 0) :
    (s.concreteExtraction μ).equiv ω x = (s.concreteTower ω.val).extract x := rfl

/-- The actual extraction and absorption maps compose over exactly the same
restricted marker, giving the full data-to-reservoir probability family. -/
def finiteDataToReservoir (μ : Measure K)
    [IsProbabilityMeasure μ] [μ.IsAddHaarMeasure] :
    RelativeProbabilityIso s.concreteRecoverySet (s.stageDataLaw 0 μ)
      (s.infiniteBernoulliLaw μ) :=
  (s.concreteExtraction μ).trans
    ((s.allOutputsToBernoulli μ).pullback Subtype.val measurable_subtype_coe)

end Topology
end BernoulliIso.AlgebraicInput

#print axioms BernoulliIso.AlgebraicInput.exists_concreteRecoverySet
#print axioms BernoulliIso.AlgebraicInput.concreteExtraction

#print axioms BernoulliIso.AlgebraicInput.finiteDataToReservoir
