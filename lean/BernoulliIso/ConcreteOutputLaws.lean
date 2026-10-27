module

public import BernoulliIso.ConcreteAbsorption

/-! The exact product laws of the tower outputs, and their separation
into surplus iid coordinates and the concrete leftover family. -/

@[expose] public section
noncomputable section
open MeasureTheory

namespace BernoulliIso.AlgebraicInput

variable {K N I V : Type*} [Field K] [Fintype K]
  [Group N] [Countable N] [Fintype I] [Fintype V] [Nonempty I] [Nonempty V]
variable (s : AlgebraicInput K N I V)
  [MeasurableSpace V] [MeasurableSingletonClass V]
  [MeasurableSpace K] [MeasurableSingletonClass K] [LinearOrder K]
  [TopologicalSpace K] [DiscreteTopology K] [BorelSpace K] [IsTopologicalRing K]

def stageDataLaw (n : ℕ) (μ : Measure K) : Measure (s.stageSpace n) :=
  iidLaw (s.stageCoordinates n) μ

instance stageDataLaw_probability (n : ℕ) (μ : Measure K) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (s.stageDataLaw n μ) := by
  unfold stageDataLaw iidLaw
  infer_instance

instance stageDataLaw_haar (n : ℕ) (μ : Measure K)
    [IsProbabilityMeasure μ] [μ.IsAddHaarMeasure] :
    (s.stageDataLaw n μ).IsAddHaarMeasure := infinitePi_isAddHaarMeasure _

def surplusLaw (n : ℕ) (μ : Measure K) :
    Measure (Fin s.excess → Ambient.G N ⧸ s.stageH (n + 1) → K) :=
  iidLaw (Fin s.excess) (iidLaw (Ambient.G N ⧸ s.stageH (n + 1)) μ)

instance surplusLaw_probability (n : ℕ) (μ : Measure K) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (s.surplusLaw n μ) := by
  unfold surplusLaw iidLaw
  infer_instance

instance surplusLaw_haar (n : ℕ) (μ : Measure K)
    [IsProbabilityMeasure μ] [μ.IsAddHaarMeasure] : (s.surplusLaw n μ).IsAddHaarMeasure := by
  letI := infinitePi_isAddHaarMeasure (fun _ : Ambient.G N ⧸ s.stageH (n + 1) => μ)
  exact infinitePi_isAddHaarMeasure _

instance splitOutput_secondCountable (n : ℕ) :
    SecondCountableTopology (s.splitOutput n) := by
  change SecondCountableTopology
    ((Fin s.excess → Ambient.G N ⧸ s.stageH (n + 1) → K) ×
      s.ambientResiduals (s.stageLevel (n + 1)))
  letI := s.ambientResiduals_secondCountable (s.stageLevel (n + 1))
  infer_instance

instance splitOutput_borel (n : ℕ) : BorelSpace (s.splitOutput n) := by
  change BorelSpace
    ((Fin s.excess → Ambient.G N ⧸ s.stageH (n + 1) → K) ×
      s.ambientResiduals (s.stageLevel (n + 1)))
  letI := s.ambientResiduals_secondCountable (s.stageLevel (n + 1))
  letI := s.ambientResiduals_borel (s.stageLevel (n + 1))
  infer_instance

instance splitOutput_measurableAdd (n : ℕ) : MeasurableAdd (s.splitOutput n) := by
  letI := s.splitOutput_secondCountable n
  letI := s.splitOutput_borel n
  change MeasurableAdd
    ((Fin s.excess → Ambient.G N ⧸ s.stageH (n + 1) → K) ×
      s.ambientResiduals (s.stageLevel (n + 1)))
  letI := s.ambientResiduals_borel (s.stageLevel (n + 1))
  constructor
  · intro c
    exact (continuous_const.add continuous_id).measurable
  · intro c
    exact (continuous_id.add continuous_const).measurable

instance splitOutput_compact (n : ℕ) : CompactSpace (s.splitOutput n) := by
  change CompactSpace
    ((Fin s.excess → Ambient.G N ⧸ s.stageH (n + 1) → K) ×
      s.ambientResiduals (s.stageLevel (n + 1)))
  letI := s.residual_compactSpace (Ambient.Hseq N (s.stageLevel (n + 1)))
    (Ambient.includeN N) (s.ambient_commutes (s.stageLevel (n + 1)))
  infer_instance

def splitOutputLaw (n : ℕ) (μ : Measure K) : Measure (s.splitOutput n) :=
  (s.surplusLaw n μ).prod (s.ambientResidualsLaw (s.stageLevel (n + 1)))

instance splitOutputLaw_probability (n : ℕ) (μ : Measure K) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (s.splitOutputLaw n μ) := by
  letI := s.ambientResidualsLaw_probability (s.stageLevel (n + 1))
  letI := s.surplusLaw_probability n μ
  unfold splitOutputLaw
  exact @Measure.prod.instIsProbabilityMeasure
    (Fin s.excess → Ambient.G N ⧸ s.stageH (n + 1) → K)
    (s.ambientResiduals (s.stageLevel (n + 1))) inferInstance inferInstance
    (s.surplusLaw n μ) (s.ambientResidualsLaw (s.stageLevel (n + 1)))
    (s.surplusLaw_probability n μ) (s.ambientResidualsLaw_probability (s.stageLevel (n + 1)))

instance splitOutputLaw_haar (n : ℕ) (μ : Measure K)
    [IsProbabilityMeasure μ] [μ.IsAddHaarMeasure] : (s.splitOutputLaw n μ).IsAddHaarMeasure := by
  letI := s.ambientResiduals_borel (s.stageLevel (n + 1))
  letI := s.splitOutput_borel n
  letI := s.ambientResidualsLaw_haar (s.stageLevel (n + 1))
  letI := s.surplusLaw_haar n μ
  letI : MeasurableAdd (s.ambientResiduals (s.stageLevel (n + 1))) := inferInstance
  letI : MeasurableAdd (Fin s.excess → Ambient.G N ⧸ s.stageH (n + 1) → K) :=
    inferInstance
  unfold splitOutputLaw
  exact @Measure.prod.instIsAddHaarMeasure
    (Fin s.excess → Ambient.G N ⧸ s.stageH (n + 1) → K)
    inferInstance inferInstance inferInstance
    (s.ambientResiduals (s.stageLevel (n + 1))) inferInstance inferInstance inferInstance
    (s.surplusLaw n μ) (s.ambientResidualsLaw (s.stageLevel (n + 1)))
    (s.surplusLaw_haar n μ) (s.ambientResidualsLaw_haar (s.stageLevel (n + 1)))
    inferInstance inferInstance inferInstance

instance stageOutput_secondCountable (n : ℕ) :
    SecondCountableTopology (s.stageOutput n) := by
  letI := s.splitOutput_secondCountable n
  infer_instance

instance stageOutput_borel (n : ℕ) : BorelSpace (s.stageOutput n) := by
  letI := s.splitOutput_secondCountable n
  letI := s.splitOutput_borel n
  infer_instance

instance stageOutput_measurableAdd (n : ℕ) : MeasurableAdd (s.stageOutput n) := by
  letI := s.splitOutput_measurableAdd n
  infer_instance

def stageOutputLaw (n : ℕ) (μ : Measure K) : Measure (s.stageOutput n) :=
  (iidLaw (Fin (StageSchedule.repetitions s.rowConstant n)) (s.splitOutputLaw n μ)).prod
    (s.discardedLaw n μ)

instance stageOutputLaw_probability (n : ℕ) (μ : Measure K) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (s.stageOutputLaw n μ) := by
  unfold stageOutputLaw iidLaw
  infer_instance

instance stageOutputLaw_haar (n : ℕ) (μ : Measure K)
    [IsProbabilityMeasure μ] [μ.IsAddHaarMeasure] : (s.stageOutputLaw n μ).IsAddHaarMeasure := by
  letI := s.splitOutput_secondCountable n
  letI := s.splitOutput_borel n
  letI := s.splitOutput_measurableAdd n
  letI := s.splitOutput_compact n
  letI := s.stageOutput_borel n
  letI := infinitePi_isAddHaarMeasure
    (fun _ : Fin (StageSchedule.repetitions s.rowConstant n) => s.splitOutputLaw n μ)
  unfold stageOutputLaw
  infer_instance

abbrev stageSurplus (n : ℕ) :=
  Fin (StageSchedule.repetitions s.rowConstant n) →
    Fin s.excess → Ambient.G N ⧸ s.stageH (n + 1) → K

instance stageSurplus_secondCountable (n : ℕ) :
    SecondCountableTopology (s.stageSurplus n) := by
  change SecondCountableTopology
    (Fin (StageSchedule.repetitions s.rowConstant n) → Fin s.excess →
      Ambient.G N ⧸ Ambient.Hseq N (s.stageLevel (n + 1)) → K)
  infer_instance

instance stageSurplus_borel (n : ℕ) : BorelSpace (s.stageSurplus n) := by
  letI : BorelSpace (Ambient.G N ⧸ Ambient.Hseq N (s.stageLevel (n + 1)) → K) :=
    inferInstance
  letI : SecondCountableTopology
      (Ambient.G N ⧸ Ambient.Hseq N (s.stageLevel (n + 1)) → K) := inferInstance
  letI : BorelSpace (Fin s.excess →
      Ambient.G N ⧸ Ambient.Hseq N (s.stageLevel (n + 1)) → K) := inferInstance
  change BorelSpace
    (Fin (StageSchedule.repetitions s.rowConstant n) → Fin s.excess →
      Ambient.G N ⧸ Ambient.Hseq N (s.stageLevel (n + 1)) → K)
  infer_instance

def stageSurplusLaw (n : ℕ) (μ : Measure K) : Measure (s.stageSurplus n) :=
  iidLaw (Fin (StageSchedule.repetitions s.rowConstant n)) (s.surplusLaw n μ)

instance stageSurplusLaw_probability (n : ℕ) (μ : Measure K) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (s.stageSurplusLaw n μ) := by
  unfold stageSurplusLaw iidLaw
  infer_instance

instance stageSurplusLaw_haar (n : ℕ) (μ : Measure K)
    [IsProbabilityMeasure μ] [μ.IsAddHaarMeasure] :
    (s.stageSurplusLaw n μ).IsAddHaarMeasure := by
  letI := s.stageSurplus_borel n
  exact infinitePi_isAddHaarMeasure _

/-- Separate precisely the surplus and residual coordinates of each split,
leaving the discarded regroup coordinates in the declared leftover. -/
def separateStageOutput (n : ℕ) (μ : Measure K)
    [IsProbabilityMeasure μ] [μ.IsAddHaarMeasure] :
    ProbabilityIso (s.stageOutputLaw n μ)
      ((s.stageSurplusLaw n μ).prod (s.leftoverLaw n μ)) := by
  letI := s.ambientResiduals_secondCountable (s.stageLevel (n + 1))
  letI := s.ambientResiduals_borel (s.stageLevel (n + 1))
  exact ((ProbabilityIso.piProduct
    (fun _ : Fin (StageSchedule.repetitions s.rowConstant n) => s.surplusLaw n μ)
    (fun _ : Fin (StageSchedule.repetitions s.rowConstant n) =>
      s.ambientResidualsLaw (s.stageLevel (n + 1)))).prod
        (ProbabilityIso.refl (s.discardedLaw n μ))).trans
    (ProbabilityIso.assoc _ _ _)

@[simp] theorem separateStageOutput_apply (n : ℕ) (μ : Measure K)
    [IsProbabilityMeasure μ] [μ.IsAddHaarMeasure] (y : s.stageOutput n) :
    (s.separateStageOutput n μ).equiv y =
      (fun i => (y.1 i).1, (fun i => (y.1 i).2, y.2)) := rfl

/-- Separate all outputs into the actual surplus product and the actual
leftover product, preserving their independent laws. -/
def separateAllOutputs (μ : Measure K) [IsProbabilityMeasure μ] [μ.IsAddHaarMeasure] :
    RelativeProbabilityIso s.markerSpace
      (Measure.infinitePi (fun n => s.stageOutputLaw n μ))
      ((Measure.infinitePi (fun n => s.stageSurplusLaw n μ)).prod
        (Measure.infinitePi (fun n => s.leftoverLaw n μ))) := by
  letI (n : ℕ) : BorelSpace (s.leftover n) := s.leftover_borel n
  letI (n : ℕ) : SecondCountableTopology (s.leftover n) := s.leftover_secondCountable n
  letI (n : ℕ) : BorelSpace (s.stageSurplus n) := s.stageSurplus_borel n
  letI (n : ℕ) : SecondCountableTopology (s.stageSurplus n) := s.stageSurplus_secondCountable n
  exact (RelativeProbabilityIso.pi (fun n =>
    RelativeProbabilityIso.constant (s.separateStageOutput n μ))).trans
      (RelativeProbabilityIso.constant
        (ProbabilityIso.piProduct (fun n => s.stageSurplusLaw n μ)
          (fun n => s.leftoverLaw n μ)))

def stageSurplusAction (n : ℕ) : MulAction (Ambient.G N) (s.stageSurplus n) := by
  letI := CosetOperators.configurationAction (K := K) (J := Fin s.excess)
    (s.stageH (n + 1))
  infer_instance

def leftoverAction (n : ℕ) : MulAction (Ambient.G N) (s.leftover n) := by
  change MulAction (Ambient.G N)
    ((Fin (StageSchedule.repetitions s.rowConstant n) →
      s.ambientResiduals (s.stageLevel (n + 1))) ×
      (Fin (StageSchedule.discarded s.rowConstant n) → s.stageSpace (n + 1)))
  letI := s.residualAction (Ambient.Hseq N (s.stageLevel (n + 1))) (Ambient.includeN N)
    (s.ambient_commutes (s.stageLevel (n + 1)))
  letI := s.stageSpaceAction (n + 1)
  infer_instance

theorem separateAllOutputs_equivariant (μ : Measure K)
    [IsProbabilityMeasure μ] [μ.IsAddHaarMeasure] :
    letI := s.markerAction
    letI : ∀ n, MulAction (Ambient.G N) (s.stageOutput n) := s.stageOutputAction
    letI : ∀ n, MulAction (Ambient.G N) (s.stageSurplus n) := s.stageSurplusAction
    letI : ∀ n, MulAction (Ambient.G N) (s.leftover n) := s.leftoverAction
    (s.separateAllOutputs μ).Equivariant (G := Ambient.G N) := by
  letI := s.markerAction
  letI : ∀ n, MulAction (Ambient.G N) (s.stageOutput n) := s.stageOutputAction
  letI : ∀ n, MulAction (Ambient.G N) (s.stageSurplus n) := s.stageSurplusAction
  letI : ∀ n, MulAction (Ambient.G N) (s.leftover n) := s.leftoverAction
  apply RelativeProbabilityIso.Equivariant.trans
  · apply RelativeProbabilityIso.Equivariant.pi
    intro n g ω y
    rfl
  · intro g ω y
    rfl

end BernoulliIso.AlgebraicInput

#print axioms BernoulliIso.AlgebraicInput.separateAllOutputs
