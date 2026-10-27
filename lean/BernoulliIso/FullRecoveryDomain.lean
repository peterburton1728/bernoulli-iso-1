module

public import BernoulliIso.ConcreteMeasured

/-! Flatten the two conull marker restrictions into one invariant measurable
subset of the original finite Bernoulli marker. All measures below come
from that original law. -/

@[expose] public section
noncomputable section
open MeasureTheory
open scoped Classical

namespace BernoulliIso.AlgebraicInput

variable {K N I V : Type*} [Field K] [Fintype K]
  [Group N] [Countable N] [Fintype I] [Fintype V] [Nonempty I] [Nonempty V]
variable (s : AlgebraicInput K N I V)
  [MeasurableSpace K] [MeasurableSingletonClass K] [LinearOrder K]

/-- The actual recovery domain, viewed inside the original marker space. -/
def fullRecoverySet : Set (Ambient.G N → K) :=
  (Subtype.val : s.markerSpace → Ambient.G N → K) '' s.concreteRecoverySet

theorem measurable_fullRecoverySet : MeasurableSet s.fullRecoverySet :=
  (MeasurableEmbedding.subtype_coe
    ((Ambient.markerGeometry N).measurable_goodMarker (K := K))).measurableSet_image'
      s.measurable_concreteRecoverySet

theorem ae_fullRecoverySet :
    ∀ᵐ ω ∂MarkerGeometry.markerLaw (G := Ambient.G N) K, ω ∈ s.fullRecoverySet := by
  rw [← s.concreteMarkerLaw_inclusion.map_eq]
  apply (ae_map_iff s.concreteMarkerLaw_inclusion.aemeasurable
    s.measurable_fullRecoverySet).2
  exact s.ae_concreteRecoverySet.mono fun ω hω => ⟨ω, hω, rfl⟩

theorem fullRecoverySet_invariant (g : Ambient.G N) (ω : Ambient.G N → K)
    (hω : ω ∈ s.fullRecoverySet) : MarkerGeometry.markerShift g ω ∈ s.fullRecoverySet := by
  obtain ⟨η, hη, rfl⟩ := hω
  exact ⟨s.shiftedMarker g η, s.concreteRecoverySet_invariant g η hη, rfl⟩

/-- The action here is exactly the original Bernoulli shift. -/
def fullMarkerAction (_s : AlgebraicInput K N I V) : MulAction (Ambient.G N) (Ambient.G N → K) where
  smul := MarkerGeometry.markerShift
  one_smul ω := by
    change MarkerGeometry.markerShift (1 : Ambient.G N) ω = ω
    funext u
    simp [MarkerGeometry.markerShift]
  mul_smul g h ω := by
    change MarkerGeometry.markerShift (g * h) ω =
      MarkerGeometry.markerShift g (MarkerGeometry.markerShift h ω)
    funext u
    simp [MarkerGeometry.markerShift, mul_assoc]

/-- Restrict the action to the flattened invariant recovery domain. -/
def fullRecoveryAction : MulAction (Ambient.G N) s.fullRecoverySet where
  smul g ω := ⟨MarkerGeometry.markerShift g ω.val,
    s.fullRecoverySet_invariant g ω.val ω.property⟩
  one_smul ω := by
    apply Subtype.ext
    exact s.fullMarkerAction.one_smul ω.val
  mul_smul g h ω := by
    apply Subtype.ext
    exact s.fullMarkerAction.mul_smul g h ω.val

/-- The same restricted action before flattening the two subtypes. -/
def recoveryMarkerAction : MulAction (Ambient.G N) s.concreteRecoverySet where
  smul g ω := ⟨s.shiftedMarker g ω.val,
    s.concreteRecoverySet_invariant g ω.val ω.property⟩
  one_smul ω := by
    apply Subtype.ext
    exact s.markerAction.one_smul ω.val
  mul_smul g h ω := by
    apply Subtype.ext
    exact s.markerAction.mul_smul g h ω.val

/-- Flattening preserves the marker itself, and has an explicit measurable
inverse. The choice in the inverse supplies only a proof of membership. -/
def recoveryFullSetEquiv : s.concreteRecoverySet ≃ s.fullRecoverySet where
  toFun ω := ⟨ω.val.val, ⟨ω.val, ω.property, rfl⟩⟩
  invFun ω :=
    let η : s.markerSpace := ⟨ω.val, by
      obtain ⟨η, _, hη⟩ := ω.property
      exact hη ▸ η.property⟩
    ⟨η, by
      obtain ⟨η', hη', heq⟩ := ω.property
      have hη : η' = η := Subtype.ext heq
      exact hη ▸ hη'⟩
  left_inv ω := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv ω := by apply Subtype.ext; rfl

/-- The flattening equivalence, with both directions measurably realized
by their unchanged original marker coordinate. -/
def recoveryFullEquiv : s.concreteRecoverySet ≃ᵐ s.fullRecoverySet where
  toEquiv := s.recoveryFullSetEquiv
  measurable_toFun := by
    apply Measurable.subtype_mk
    exact measurable_subtype_coe.comp
      (measurable_subtype_coe : Measurable (Subtype.val : s.concreteRecoverySet → s.markerSpace))
  measurable_invFun := by
    apply Measurable.subtype_mk
    apply Measurable.subtype_mk
    exact (measurable_subtype_coe :
      Measurable (Subtype.val : s.fullRecoverySet → Ambient.G N → K))

@[simp] theorem recoveryFullEquiv_val (ω : s.concreteRecoverySet) :
    (s.recoveryFullEquiv ω).val = ω.val.val := rfl

@[simp] theorem recoveryFullEquiv_symm_val (ω : s.fullRecoverySet) :
    (s.recoveryFullEquiv.symm ω).val.val = ω.val := rfl

theorem recoveryFullEquiv_covariant (g : Ambient.G N) (ω : s.concreteRecoverySet) :
    s.recoveryFullEquiv (s.recoveryMarkerAction.smul g ω) =
      s.fullRecoveryAction.smul g (s.recoveryFullEquiv ω) := by
  apply Subtype.ext
  rfl

/-- The flattened law is induced directly from the full Bernoulli marker. -/
def fullRecoveryLaw : Measure s.fullRecoverySet :=
  (MarkerGeometry.markerLaw (G := Ambient.G N) K).comap Subtype.val

instance fullRecoveryLaw_probability : IsProbabilityMeasure s.fullRecoveryLaw :=
  (MeasurableEmbedding.subtype_coe s.measurable_fullRecoverySet).isProbabilityMeasure_comap
    (by simpa using s.ae_fullRecoverySet)

theorem fullRecoveryLaw_inclusion :
    MeasurePreserving (Subtype.val : s.fullRecoverySet → Ambient.G N → K)
      s.fullRecoveryLaw (MarkerGeometry.markerLaw (G := Ambient.G N) K) :=
  measurePreserving_conullSubtype _ s.measurable_fullRecoverySet s.ae_fullRecoverySet

/-- The nested and flattened induced probabilities agree under flattening. -/
theorem recoveryFullEquiv_preserving :
    MeasurePreserving s.recoveryFullEquiv s.concreteRecoveryLaw s.fullRecoveryLaw := by
  refine ⟨s.recoveryFullEquiv.measurable, ?_⟩
  apply (MeasurableEmbedding.subtype_coe s.measurable_fullRecoverySet).map_injective
  rw [Measure.map_map measurable_subtype_coe s.recoveryFullEquiv.measurable]
  exact (s.concreteMarkerLaw_inclusion.comp s.concreteRecoveryLaw_inclusion).map_eq.trans
    s.fullRecoveryLaw_inclusion.map_eq.symm

theorem fullRecoveryLaw_preserving (g : Ambient.G N) :
    MeasurePreserving (s.fullRecoveryAction.smul g) s.fullRecoveryLaw s.fullRecoveryLaw := by
  have hm : Measurable (s.fullRecoveryAction.smul g) :=
    ((MarkerGeometry.measurePreserving_markerShift (K := K) g).measurable.comp
      measurable_subtype_coe).subtype_mk
  refine ⟨hm, ?_⟩
  apply (MeasurableEmbedding.subtype_coe s.measurable_fullRecoverySet).map_injective
  rw [Measure.map_map measurable_subtype_coe hm]
  change Measure.map (MarkerGeometry.markerShift g ∘ Subtype.val) _ = _
  rw [← Measure.map_map
    (MarkerGeometry.measurePreserving_markerShift (K := K) g).measurable
    measurable_subtype_coe, s.fullRecoveryLaw_inclusion.map_eq,
    (MarkerGeometry.measurePreserving_markerShift (K := K) g).map_eq]

theorem fullRecovery_standardBorel [StandardBorelSpace (Ambient.G N → K)] :
    StandardBorelSpace s.fullRecoverySet := s.measurable_fullRecoverySet.standardBorel

/-- Any already constructed family over the common nested recovery marker
can be used over the single conull domain in the original marker space. -/
def overFullRecovery {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {ν : Measure X} {ρ : Measure Y}
    (e : RelativeProbabilityIso s.concreteRecoverySet ν ρ) :
    RelativeProbabilityIso s.fullRecoverySet ν ρ where
  equiv ω := e.equiv (s.recoveryFullEquiv.symm ω)
  jointlyMeasurable := e.jointlyMeasurable.comp
    ((s.recoveryFullEquiv.symm.measurable.comp measurable_fst).prodMk measurable_snd)
  jointlyMeasurable_symm := e.jointlyMeasurable_symm.comp
    ((s.recoveryFullEquiv.symm.measurable.comp measurable_fst).prodMk measurable_snd)
  measurePreserving ω := e.measurePreserving (s.recoveryFullEquiv.symm ω)

/-- Transport of covariance uses the same marker shift on both domains. -/
theorem overFullRecovery_covariant {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    [MulAction (Ambient.G N) X] [MulAction (Ambient.G N) Y]
    {ν : Measure X} {ρ : Measure Y}
    (e : RelativeProbabilityIso s.concreteRecoverySet ν ρ)
    (he : ∀ (g : Ambient.G N) (ω : s.concreteRecoverySet) (x : X),
      e.equiv (s.recoveryMarkerAction.smul g ω) (g • x) = g • e.equiv ω x)
    (g : Ambient.G N) (ω : s.fullRecoverySet) (x : X) :
    (s.overFullRecovery e).equiv (s.fullRecoveryAction.smul g ω) (g • x) =
      g • (s.overFullRecovery e).equiv ω x := by
  change e.equiv (s.recoveryFullEquiv.symm (s.fullRecoveryAction.smul g ω)) (g • x) = _
  have hω : s.recoveryFullEquiv.symm (s.fullRecoveryAction.smul g ω) =
      s.recoveryMarkerAction.smul g (s.recoveryFullEquiv.symm ω) := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  rw [hω]
  exact he g (s.recoveryFullEquiv.symm ω) x

end BernoulliIso.AlgebraicInput

#print axioms BernoulliIso.AlgebraicInput.ae_fullRecoverySet
#print axioms BernoulliIso.AlgebraicInput.recoveryFullEquiv_preserving
#print axioms BernoulliIso.AlgebraicInput.overFullRecovery
