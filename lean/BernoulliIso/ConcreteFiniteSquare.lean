module

public import BernoulliIso.FullRecoveryDomain
public import BernoulliIso.FiniteBernoulliModels
public import BernoulliIso.ProbabilityTransport

/-! The finite-base square is absorbed by explicit relative maps over the
same recovery marker. No cancellation or factor-isomorphism principle is used. -/

@[expose] public section
noncomputable section
open MeasureTheory
open scoped Classical

attribute [local irreducible] BernoulliIso.AlgebraicInput.outputSlots
  BernoulliIso.CosetCoordinates.sortedCosetChart

namespace BernoulliIso.ProbabilityIso

def unitCopies {Z : Type*} [AddCommGroup Z] [TopologicalSpace Z]
    [CompactSpace Z] [SecondCountableTopology Z] [IsTopologicalAddGroup Z]
    [MeasurableSpace Z] [BorelSpace Z]
    (ν : Measure Z) [IsProbabilityMeasure ν] [ν.IsAddHaarMeasure] :
    ProbabilityIso ν (iidLaw Unit ν) := by
  letI := infinitePi_isAddHaarMeasure (fun _ : Unit => ν)
  let e : Z ≃ᵐ (Unit → Z) :=
    { toFun := fun z _ => z
      invFun := fun f => f ()
      left_inv := fun _ => rfl
      right_inv := fun f => by funext u; cases u; rfl
      measurable_toFun := Measurable.of_eval fun _ => measurable_id
      measurable_invFun := measurable_pi_apply () }
  let F : Z →+ (Unit → Z) :=
    { toFun := e
      map_zero' := rfl
      map_add' _ _ := rfl }
  exact ⟨e, F.measurePreserving (continuous_pi fun _ => continuous_id)
    e.surjective (by simp)⟩

end BernoulliIso.ProbabilityIso

namespace BernoulliIso.RelativeProbabilityIso

/-- Package a relative isomorphism directly as a conjugacy. Proving this
with an abstract fiber map keeps the concrete extraction formula opaque. -/
def conullConjugacy {G Ω X Y : Type*} [Group G]
    [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Y]
    [MulAction G Ω] [MulAction G X] [MulAction G Y]
    (μ : Measure Ω) (ν : Measure X) (ρ : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]
    {S : Set Ω} (hs : MeasurableSet S) (hfull : ∀ᵐ ω ∂μ, ω ∈ S)
    (hinv : ∀ (g : G) (ω : Ω), ω ∈ S → g • ω ∈ S)
    (e : RelativeProbabilityIso S ν ρ)
    (he : ∀ (g : G) (ω : S) (x : X),
      e.equiv ⟨g • ω.val, hinv g ω.val ω.property⟩ (g • x) = g • e.equiv ω x) :
    ConullConjugacy G (Ω × X) (Ω × Y) (μ.prod ν) (μ.prod ρ) := by
  letI : IsProbabilityMeasure (μ.comap (Subtype.val : S → Ω)) :=
    (MeasurableEmbedding.subtype_coe hs).isProbabilityMeasure_comap
      (by simpa using hfull)
  apply conullConjugacyOfRelativeIso μ ν ρ hs hfull hinv
    (e.retained (μ.comap (Subtype.val : S → Ω)))
  · intro p
    rfl
  · intro g ω x
    exact he g ω x

end BernoulliIso.RelativeProbabilityIso

namespace BernoulliIso.AlgebraicInput

variable {K N I V : Type*} [Field K] [Fintype K]
  [Group N] [Countable N] [Fintype I] [Fintype V] [Nonempty I] [Nonempty V]
variable (s : AlgebraicInput K N I V)
  [MeasurableSpace K] [MeasurableSingletonClass K] [LinearOrder K]
  [TopologicalSpace K] [DiscreteTopology K] [BorelSpace K] [IsTopologicalRing K]
  [MeasurableSpace V] [MeasurableSingletonClass V]

local instance uniformMarkerHaar : (MarkerGeometry.uniformBase K).IsAddHaarMeasure :=
  uniformFinite_isAddHaarMeasure

abbrev finiteSourceLaw := (MarkerGeometry.markerLaw (G := Ambient.G N) K).prod
  (s.stageDataLaw 0 (MarkerGeometry.uniformBase K))

theorem finiteDataToReservoir_equivariant :
    letI := s.recoveryMarkerAction
    letI := s.stageSpaceAction 0
    letI := s.infiniteBernoulliAction
    (s.finiteDataToReservoir (MarkerGeometry.uniformBase K)).Equivariant
      (G := Ambient.G N) := by
  letI := s.markerAction
  letI := s.recoveryMarkerAction
  letI : ∀ n, MulAction (Ambient.G N) (s.stageSpace n) := s.stageSpaceAction
  letI : ∀ n, MulAction (Ambient.G N) (s.stageOutput n) := s.stageOutputAction
  letI := s.infiniteBernoulliAction
  unfold finiteDataToReservoir
  apply RelativeProbabilityIso.Equivariant.trans
  · intro g ω x
    exact ExtractionTower.extract_covariant s.concreteTower s.concreteStage_covariant g ω.val x
  · intro g ω x
    exact s.allOutputsToBernoulli_equivariant (MarkerGeometry.uniformBase K) g ω.val x

/-- A single ordinary marker track is absorbed into the countable ordinary
track family by a fixed track interleaving, including its exact law. -/
def absorbFullMarker : ProbabilityIso
    ((s.infiniteBernoulliLaw (MarkerGeometry.uniformBase K)).prod
      (MarkerGeometry.markerLaw (G := Ambient.G N) K))
    (s.infiniteBernoulliLaw (MarkerGeometry.uniformBase K)) := by
  let ν := MarkerGeometry.markerLaw (G := Ambient.G N) K
  letI : ν.IsAddHaarMeasure :=
    infinitePi_isAddHaarMeasure (fun _ : Ambient.G N => MarkerGeometry.uniformBase K)
  exact ((ProbabilityIso.refl (iidLaw ℕ ν)).prod (ProbabilityIso.unitCopies ν)).trans
    (ProbabilityIso.interleave ν (ConcreteInterleaving.natPlus Unit))

/-- The retained recovery marker turns the extra stage-zero data into a
second countable reservoir, which is then interleaved into the first. -/
def absorbStageZero : RelativeProbabilityIso s.concreteRecoverySet
    ((s.infiniteBernoulliLaw (MarkerGeometry.uniformBase K)).prod
      (s.stageDataLaw 0 (MarkerGeometry.uniformBase K)))
    (s.infiniteBernoulliLaw (MarkerGeometry.uniformBase K)) :=
  ((RelativeProbabilityIso.refl (s.infiniteBernoulliLaw (MarkerGeometry.uniformBase K))).prod
    (s.finiteDataToReservoir (MarkerGeometry.uniformBase K))).trans
      (RelativeProbabilityIso.constant
        (ProbabilityIso.interleave (MarkerGeometry.markerLaw (G := Ambient.G N) K)
          (ConcreteInterleaving.natPlus ℕ)))

def absorbSecondFiniteSource : RelativeProbabilityIso s.concreteRecoverySet
    ((s.infiniteBernoulliLaw (MarkerGeometry.uniformBase K)).prod s.finiteSourceLaw)
    (s.infiniteBernoulliLaw (MarkerGeometry.uniformBase K)) :=
  RelativeProbabilityIso.absorbPair
    (RelativeProbabilityIso.constant s.absorbFullMarker) s.absorbStageZero

/-- The data part of two finite sources is isomorphic to the data part of
one source, while preserving the common marker. -/
def relativeFiniteSquare : RelativeProbabilityIso s.concreteRecoverySet
    ((s.stageDataLaw 0 (MarkerGeometry.uniformBase K)).prod s.finiteSourceLaw)
    (s.stageDataLaw 0 (MarkerGeometry.uniformBase K)) :=
  (((s.finiteDataToReservoir (MarkerGeometry.uniformBase K)).prod
    (RelativeProbabilityIso.refl s.finiteSourceLaw)).trans s.absorbSecondFiniteSource).trans
      (s.finiteDataToReservoir (MarkerGeometry.uniformBase K)).symm

theorem absorbFullMarker_covariant (g : Ambient.G N)
    (p : s.infiniteBernoulli × (Ambient.G N → K)) :
    s.absorbFullMarker.equiv
      ((s.infiniteBernoulliAction).smul g p.1, (s.fullMarkerAction).smul g p.2) =
        (s.infiniteBernoulliAction).smul g (s.absorbFullMarker.equiv p) := by
  letI := s.fullMarkerAction
  exact ProbabilityIso.interleave_covariant
    (MarkerGeometry.markerLaw (G := Ambient.G N) K)
    (ConcreteInterleaving.natPlus Unit) g (p.1, fun _ : Unit => p.2)

theorem relativeFiniteSquare_equivariant :
    letI := s.recoveryMarkerAction
    letI := s.stageSpaceAction 0
    letI := s.fullMarkerAction
    (s.relativeFiniteSquare).Equivariant (G := Ambient.G N) := by
  letI := s.recoveryMarkerAction
  letI := s.stageSpaceAction 0
  letI := s.fullMarkerAction
  letI := s.infiniteBernoulliAction
  have he := s.finiteDataToReservoir_equivariant
  have hmarker : (RelativeProbabilityIso.constant (Ω := s.concreteRecoverySet)
      s.absorbFullMarker).Equivariant (G := Ambient.G N) := by
    intro g ω p
    exact s.absorbFullMarker_covariant g p
  have hdata : s.absorbStageZero.Equivariant (G := Ambient.G N) := by
    unfold absorbStageZero
    apply RelativeProbabilityIso.Equivariant.trans
    · apply RelativeProbabilityIso.Equivariant.prod
      · intro g ω x
        rfl
      · exact he
    · intro g ω p
      exact ProbabilityIso.interleave_covariant
        (MarkerGeometry.markerLaw (G := Ambient.G N) K)
        (ConcreteInterleaving.natPlus ℕ) g p
  have haux : s.absorbSecondFiniteSource.Equivariant (G := Ambient.G N) :=
    RelativeProbabilityIso.absorbPair_equivariant _ _ hmarker hdata
  have hid : (RelativeProbabilityIso.refl (Ω := s.concreteRecoverySet)
      s.finiteSourceLaw).Equivariant (G := Ambient.G N) := by
    intro g ω x
    rfl
  exact ((he.prod hid).trans haux).trans he.symm

attribute [local irreducible] relativeFiniteSquare finiteDataToReservoir concreteExtraction

/-- The relative map gives an actual conull conjugacy on the full marker
spaces, with precisely their original Bernoulli probabilities. -/
def finiteSquareCore :
    letI := s.fullMarkerAction
    letI := s.stageSpaceAction 0
    ConullConjugacy (Ambient.G N)
      ((Ambient.G N → K) × (s.stageSpace 0 × ((Ambient.G N → K) × s.stageSpace 0)))
      ((Ambient.G N → K) × s.stageSpace 0)
      ((MarkerGeometry.markerLaw (G := Ambient.G N) K).prod
        ((s.stageDataLaw 0 (MarkerGeometry.uniformBase K)).prod s.finiteSourceLaw))
      s.finiteSourceLaw := by
  letI := s.fullMarkerAction
  letI := s.stageSpaceAction 0
  apply RelativeProbabilityIso.conullConjugacy (G := Ambient.G N)
    (MarkerGeometry.markerLaw (G := Ambient.G N) K)
    ((s.stageDataLaw 0 (MarkerGeometry.uniformBase K)).prod s.finiteSourceLaw)
    (s.stageDataLaw 0 (MarkerGeometry.uniformBase K))
    s.measurable_fullRecoverySet s.ae_fullRecoverySet s.fullRecoverySet_invariant
    (s.overFullRecovery s.relativeFiniteSquare)
  intro g ω x
  exact s.overFullRecovery_covariant s.relativeFiniteSquare
    s.relativeFiniteSquare_equivariant g ω x

/-- The finite uniform alphabet is isomorphic to its square as a Bernoulli
shift, via the actual construction rather than an assumed classification. -/
def finiteBaseSquareConjugacy :
    letI := bernoulliAction (Ambient.G N) (s.finiteBase × s.finiteBase)
    letI := bernoulliAction (Ambient.G N) s.finiteBase
    ConullConjugacy (Ambient.G N)
      (Ambient.G N → s.finiteBase × s.finiteBase) (Ambient.G N → s.finiteBase)
      (bernoulliLaw (Ambient.G N) (s.finiteBase × s.finiteBase))
      (bernoulliLaw (Ambient.G N) s.finiteBase) := by
  letI := s.fullMarkerAction
  letI := s.stageSpaceAction 0
  letI := bernoulliAction (Ambient.G N) (s.finiteBase × s.finiteBase)
  letI := bernoulliAction (Ambient.G N) s.finiteBase
  apply s.finiteSquareCore.transport s.doubleFiniteBernoulliIso.symm s.finiteBernoulliIso.symm
  · intro g y
    apply s.doubleFiniteBernoulliIso.equiv.injective
    change s.doubleFiniteBernoulliIso.equiv (s.doubleFiniteBernoulliIso.equiv.symm (g • y)) =
      s.doubleFiniteBernoulliIso.equiv (g • s.doubleFiniteBernoulliIso.equiv.symm y)
    rw [s.doubleFiniteBernoulliIso.equiv.apply_symm_apply]
    exact ((s.doubleFiniteBernoulliIso_covariant g
      (s.doubleFiniteBernoulliIso.equiv.symm y)).trans
        (congrArg ((bernoulliAction (Ambient.G N) (s.finiteBase × s.finiteBase)).smul g)
          (s.doubleFiniteBernoulliIso.equiv.apply_symm_apply y))).symm
  · intro g y
    apply s.finiteBernoulliIso.equiv.injective
    change s.finiteBernoulliIso.equiv (s.finiteBernoulliIso.equiv.symm (g • y)) =
      s.finiteBernoulliIso.equiv (g • s.finiteBernoulliIso.equiv.symm y)
    rw [s.finiteBernoulliIso.equiv.apply_symm_apply]
    exact ((s.finiteBernoulliEquiv_covariant g
      (s.finiteBernoulliIso.equiv.symm y)).trans
        (congrArg ((bernoulliAction (Ambient.G N) s.finiteBase).smul g)
          (s.finiteBernoulliIso.equiv.apply_symm_apply y))).symm

end BernoulliIso.AlgebraicInput

#print axioms BernoulliIso.AlgebraicInput.relativeFiniteSquare
#print axioms BernoulliIso.AlgebraicInput.finiteBaseSquareConjugacy
