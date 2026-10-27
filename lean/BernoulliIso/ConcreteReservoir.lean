module

public import BernoulliIso.ConcreteOutputLaws

/-! All surplus outputs form an ordinary infinite-track Bernoulli reservoir.
The finite within-coset slots are provided by the actual ranked site chart. -/

@[expose] public section
noncomputable section
open MeasureTheory

namespace BernoulliIso
namespace ConcreteInterleaving

def curryThree {K : Type*} [MeasurableSpace K] (A B C : Type*)
    (μ : Measure K) [IsProbabilityMeasure μ] :
    ProbabilityIso (iidLaw ((A × B) × C) μ)
      (iidLaw A (iidLaw B (iidLaw C μ))) :=
  (ProbabilityIso.curry (fun (_ : A × B) (_ : C) => μ)).trans
    (ProbabilityIso.curry (fun (_ : A) (_ : B) => iidLaw C μ))

end ConcreteInterleaving

namespace AlgebraicInput

variable {K N I V : Type*} [Field K] [Fintype K]
  [Group N] [Countable N] [Fintype I] [Fintype V] [Nonempty I] [Nonempty V]
variable (s : AlgebraicInput K N I V)
  [MeasurableSpace K] [MeasurableSingletonClass K] [LinearOrder K]
  [TopologicalSpace K] [DiscreteTopology K] [BorelSpace K] [IsTopologicalRing K]
  [MeasurableSpace V] [MeasurableSingletonClass V]

local instance reservoirAmbientMeasurable : MeasurableSpace (Ambient.G N) := ⊤
local instance reservoirAmbientMeasurableSingleton : MeasurableSingletonClass (Ambient.G N) :=
  ⟨fun _ => trivial⟩
local instance reservoirQuotientMeasurable (H : Subgroup (Ambient.G N)) :
    MeasurableSpace (Ambient.G N ⧸ H) := ⊤
local instance reservoirQuotientMeasurableSingleton (H : Subgroup (Ambient.G N)) :
    MeasurableSingletonClass (Ambient.G N ⧸ H) := ⟨fun _ => trivial⟩

theorem stageH_card_repetitions (n : ℕ) :
    Nat.card (s.stageH (n + 1)) = StageSchedule.repetitions s.rowConstant n := by
  change Nat.card (Ambient.Hseq N (s.stageLevel (n + 1))) = _
  rw [Ambient.Hseq_card]
  rfl

/-- The repetition count equals the finite lamp subgroup order, so its
copies of each coset track are exactly one ordinary group track. -/
def stageSurplusSlots (n : ℕ) (ω : s.markerSpace) :
    (Fin s.excess × Ambient.G N) ≃
      (Fin (StageSchedule.repetitions s.rowConstant n) × Fin s.excess) ×
        (Ambient.G N ⧸ s.stageH (n + 1)) :=
  (Equiv.prodCongr (Equiv.refl (Fin s.excess))
    (ConcreteInterleaving.siteChart (Ambient.markerGeometry N) (s.stageH (n + 1))
      (s.stageH_le_D (n + 1)) ω)).trans <|
    (ConcreteInterleaving.transposeLast (Fin s.excess)
      (Ambient.G N ⧸ s.stageH (n + 1)) (Fin (Nat.card (s.stageH (n + 1))))).trans <|
      Equiv.prodCongr
        ((Equiv.prodComm (Fin s.excess) (Fin (Nat.card (s.stageH (n + 1))))).trans
          (Equiv.prodCongr (finCongr (s.stageH_card_repetitions n))
            (Equiv.refl (Fin s.excess))))
        (Equiv.refl (Ambient.G N ⧸ s.stageH (n + 1)))

@[simp] theorem stageSurplusSlots_apply (n : ℕ) (ω : s.markerSpace)
    (w : Fin s.excess) (u : Ambient.G N) :
    s.stageSurplusSlots n ω (w, u) =
      ((finCongr (s.stageH_card_repetitions n)
        (ConcreteInterleaving.siteChart (Ambient.markerGeometry N) (s.stageH (n + 1))
          (s.stageH_le_D (n + 1)) ω u).2, w),
        (ConcreteInterleaving.siteChart (Ambient.markerGeometry N) (s.stageH (n + 1))
          (s.stageH_le_D (n + 1)) ω u).1) := rfl

theorem measurable_stageSurplusSlots (n : ℕ) :
    Measurable (fun p : s.markerSpace × (Fin s.excess × Ambient.G N) =>
      s.stageSurplusSlots n p.1 p.2) := by
  apply measurable_from_prod_countable_left
  intro p
  have h := (ConcreteInterleaving.measurable_siteChart (M := K)
    (Ambient.markerGeometry N) (s.stageH (n + 1)) (s.stageH_le_D (n + 1))).comp
      (measurable_id.prodMk (measurable_const (a := p.2)))
  exact (measurable_of_countable (fun q :
    (Ambient.G N ⧸ s.stageH (n + 1)) × Fin (Nat.card (s.stageH (n + 1))) =>
      ((finCongr (s.stageH_card_repetitions n) q.2, p.1), q.1))).comp h

theorem stageSurplusSlots_covariant (n : ℕ) (g : Ambient.G N)
    (ω : s.markerSpace) (w : Fin s.excess) (u : Ambient.G N) :
    s.stageSurplusSlots n
      ⟨MarkerGeometry.markerShift g ω.val, (Ambient.markerGeometry N).goodMarker_shift g ω.property⟩
      (w, g * u) =
        ((s.stageSurplusSlots n ω (w, u)).1, g • (s.stageSurplusSlots n ω (w, u)).2) := by
  exact congrArg
    (fun q : (Ambient.G N ⧸ s.stageH (n + 1)) × Fin (Nat.card (s.stageH (n + 1))) =>
      ((finCongr (s.stageH_card_repetitions n) q.2, w), q.1))
    (ConcreteInterleaving.siteChart_covariant (M := K) (Ambient.markerGeometry N)
      (s.stageH (n + 1)) (s.stageH_le_D (n + 1)) g ω u)

/-- All the actual finite-H copies at one stage, with their iid laws. -/
def ordinaryToStageSurplus (n : ℕ) (μ : Measure K) [IsProbabilityMeasure μ] :
    RelativeProbabilityIso s.markerSpace
      (iidLaw (Fin s.excess) (iidLaw (Ambient.G N) μ)) (s.stageSurplusLaw n μ) :=
  (RelativeProbabilityIso.constant
    (ProbabilityIso.curry (fun (_ : Fin s.excess) (_ : Ambient.G N) => μ)).symm).trans <|
    (CosetCoordinates.relativeReindexOfMeasurable μ (s.stageSurplusSlots n)
      (s.measurable_stageSurplusSlots n)).trans <|
      RelativeProbabilityIso.constant (ConcreteInterleaving.curryThree
        (Fin (StageSchedule.repetitions s.rowConstant n)) (Fin s.excess)
        (Ambient.G N ⧸ s.stageH (n + 1)) μ)

@[simp] theorem ordinaryToStageSurplus_apply (n : ℕ) (μ : Measure K)
    [IsProbabilityMeasure μ] (ω : s.markerSpace) (x : Fin s.excess → Ambient.G N → K)
    (i : Fin (StageSchedule.repetitions s.rowConstant n)) (w : Fin s.excess)
    (c : Ambient.G N ⧸ s.stageH (n + 1)) :
    (s.ordinaryToStageSurplus n μ).equiv ω x i w c =
      x ((s.stageSurplusSlots n ω).symm ((i, w), c)).1
        ((s.stageSurplusSlots n ω).symm ((i, w), c)).2 := by
  change (MeasurableEquiv.piCongrLeft
    (fun _ : (Fin (StageSchedule.repetitions s.rowConstant n) × Fin s.excess) ×
      (Ambient.G N ⧸ s.stageH (n + 1)) => K)
    (s.stageSurplusSlots n ω)) (fun q => x q.1 q.2) ((i, w), c) = _
  simpa using MeasurableEquiv.piCongrLeft_apply_apply (s.stageSurplusSlots n ω)
    (β := fun _ => K) (fun q => x q.1 q.2)
      ((s.stageSurplusSlots n ω).symm ((i, w), c))

theorem ordinaryToStageSurplus_covariant (n : ℕ) (μ : Measure K)
    [IsProbabilityMeasure μ] (g : Ambient.G N) (ω : s.markerSpace)
    (x : Fin s.excess → Ambient.G N → K) :
    (s.ordinaryToStageSurplus n μ).equiv
      ⟨MarkerGeometry.markerShift g ω.val, (Ambient.markerGeometry N).goodMarker_shift g ω.property⟩
      (fun w u => x w (g⁻¹ * u)) =
        fun i w c => (s.ordinaryToStageSurplus n μ).equiv ω x i w (g⁻¹ • c) := by
  funext i w c
  let ω' : s.markerSpace :=
    ⟨MarkerGeometry.markerShift g ω.val, (Ambient.markerGeometry N).goodMarker_shift g ω.property⟩
  let z := (s.stageSurplusSlots n ω).symm ((i, w), g⁻¹ • c)
  have hi : (s.stageSurplusSlots n ω').symm ((i, w), c) = (z.1, g * z.2) := by
    apply (s.stageSurplusSlots n ω').injective
    rw [Equiv.apply_symm_apply]
    change ((i, w), c) = s.stageSurplusSlots n ω' (z.1, g * z.2)
    rw [s.stageSurplusSlots_covariant]
    have hz : s.stageSurplusSlots n ω z = ((i, w), g⁻¹ • c) :=
      (s.stageSurplusSlots n ω).apply_symm_apply _
    rw [hz]
    simp
  simp only [s.ordinaryToStageSurplus_apply]
  change x ((s.stageSurplusSlots n ω').symm ((i, w), c)).1
    (g⁻¹ * ((s.stageSurplusSlots n ω').symm ((i, w), c)).2) = x z.1 z.2
  rw [hi]
  simp

def excessNonemptyWitness : Nonempty (Fin s.excess) := ⟨⟨0, s.excess_pos⟩⟩

/-- Positive surplus supplies infinitely many ordinary iid group tracks. -/
def allSurplusToBernoulli (μ : Measure K) [IsProbabilityMeasure μ] :
    RelativeProbabilityIso s.markerSpace
      (Measure.infinitePi (fun n => s.stageSurplusLaw n μ)) (s.infiniteBernoulliLaw μ) := by
  letI := s.excessNonemptyWitness
  exact (RelativeProbabilityIso.pi (fun n => (s.ordinaryToStageSurplus n μ).symm)).trans
    (RelativeProbabilityIso.constant
      (ConcreteInterleaving.copiesToInfinite (iidLaw (Ambient.G N) μ) (Fin s.excess)))

/-- Every output, including every residual and discarded track, is absorbed
by the actual positive-surplus Bernoulli reservoir. -/
def allOutputsToBernoulli (μ : Measure K)
    [IsProbabilityMeasure μ] [μ.IsAddHaarMeasure] :
    RelativeProbabilityIso s.markerSpace
      (Measure.infinitePi (fun n => s.stageOutputLaw n μ)) (s.infiniteBernoulliLaw μ) :=
  (s.separateAllOutputs μ).trans <|
    ((s.allSurplusToBernoulli μ).prod
      (RelativeProbabilityIso.refl (Measure.infinitePi (fun n => s.leftoverLaw n μ)))).trans
        (s.absorbAllLeftovers μ)

def ordinarySiteAction (_s : AlgebraicInput K N I V) :
    MulAction (Ambient.G N) (Ambient.G N → K) where
  smul g f u := f (g⁻¹ * u)
  one_smul f := by
    change (fun u => f ((1 : Ambient.G N)⁻¹ * u)) = f
    funext u
    simp
  mul_smul g h f := by
    change (fun u => f ((g * h)⁻¹ * u)) = (fun u => f (h⁻¹ * (g⁻¹ * u)))
    funext u
    simp [mul_assoc]

def ordinaryTracksAction (T : Type*) : MulAction (Ambient.G N) (T → Ambient.G N → K) := by
  letI := s.ordinarySiteAction
  infer_instance

theorem ordinaryToStageSurplus_equivariant (n : ℕ) (μ : Measure K)
    [IsProbabilityMeasure μ] :
    letI := s.markerAction
    letI := s.ordinaryTracksAction (Fin s.excess)
    letI := s.stageSurplusAction n
    (s.ordinaryToStageSurplus n μ).Equivariant (G := Ambient.G N) := by
  letI := s.markerAction
  letI := s.ordinaryTracksAction (Fin s.excess)
  letI := s.stageSurplusAction n
  intro g ω x
  exact s.ordinaryToStageSurplus_covariant n μ g ω x

theorem allSurplusToBernoulli_equivariant (μ : Measure K) [IsProbabilityMeasure μ] :
    letI := s.markerAction
    letI : ∀ n, MulAction (Ambient.G N) (s.stageSurplus n) := s.stageSurplusAction
    letI := s.infiniteBernoulliAction
    (s.allSurplusToBernoulli μ).Equivariant (G := Ambient.G N) := by
  letI := s.markerAction
  letI : ∀ n, MulAction (Ambient.G N) (s.stageSurplus n) := s.stageSurplusAction
  letI := s.ordinarySiteAction
  letI := s.ordinaryTracksAction (Fin s.excess)
  letI := s.infiniteBernoulliAction
  letI := s.excessNonemptyWitness
  apply RelativeProbabilityIso.Equivariant.trans
  · apply RelativeProbabilityIso.Equivariant.pi
    intro n
    exact (s.ordinaryToStageSurplus_equivariant n μ).symm
  · intro g ω x
    exact ConcreteInterleaving.copiesToInfinite_covariant
      (iidLaw (Ambient.G N) μ) (Fin s.excess) g x

theorem allOutputsToBernoulli_equivariant (μ : Measure K)
    [IsProbabilityMeasure μ] [μ.IsAddHaarMeasure] :
    letI := s.markerAction
    letI : ∀ n, MulAction (Ambient.G N) (s.stageOutput n) := s.stageOutputAction
    letI := s.infiniteBernoulliAction
    (s.allOutputsToBernoulli μ).Equivariant (G := Ambient.G N) := by
  letI := s.markerAction
  letI : ∀ n, MulAction (Ambient.G N) (s.stageOutput n) := s.stageOutputAction
  letI : ∀ n, MulAction (Ambient.G N) (s.stageSurplus n) := s.stageSurplusAction
  letI : ∀ n, MulAction (Ambient.G N) (s.leftover n) := s.leftoverAction
  letI := s.infiniteBernoulliAction
  letI (n : ℕ) : IsProbabilityMeasure (s.leftoverLaw n μ) :=
    s.leftoverLaw_probability n μ
  letI : IsProbabilityMeasure (Measure.infinitePi (fun n => s.leftoverLaw n μ)) :=
    inferInstance
  letI : IsFiniteMeasure (Measure.infinitePi (fun n => s.leftoverLaw n μ)) :=
    ⟨by simp⟩
  letI : SigmaFinite (Measure.infinitePi (fun n => s.leftoverLaw n μ)) :=
    IsFiniteMeasure.toSigmaFinite _
  letI : SFinite (Measure.infinitePi (fun n => s.leftoverLaw n μ)) := inferInstance
  have hid : (RelativeProbabilityIso.refl (Ω := s.markerSpace)
      (Measure.infinitePi (fun n => s.leftoverLaw n μ))).Equivariant
      (G := Ambient.G N) := by
    intro g ω x
    rfl
  exact (s.separateAllOutputs_equivariant μ).trans
    (((s.allSurplusToBernoulli_equivariant μ).prod hid).trans
      (s.absorbAllLeftovers_equivariant μ))

end AlgebraicInput
end BernoulliIso

#print axioms BernoulliIso.AlgebraicInput.allOutputsToBernoulli
