module

public import BernoulliIso.ConcreteInterleaving
public import BernoulliIso.CompactProbability
public import BernoulliIso.AmbientCharts
public import BernoulliIso.SplitDynamics

/-!
The actual rectangle split needed for absorption of its residual subgroup.
It is derived from the given group-ring matrices and marker-sorted finite
cosets, with the residual carrying its normalized Haar probability.
-/

@[expose] public section
noncomputable section
open MeasureTheory

namespace BernoulliIso.AlgebraicInput

variable {K N I V G : Type*} [Field K] [Fintype K]
  [Group N] [Countable N] [Fintype I] [Fintype V] [Nonempty I] [Nonempty V] [Group G]
variable (s : AlgebraicInput K N I V) (H : Subgroup G) (ι : N →* G)
  (commutes : ∀ h ∈ H, ∀ n, Commute h (ι n))

/-- Before assigning primary tracks to retained/surplus slots, the actual
amplified rectangle splits d coset tracks into κm coset tracks and κ residuals. -/
def unexpandedSplit
    (charts : ∀ v, (G ⧸ H) ≃ (G ⧸ (H ⊔ (s.J v).map ι)) × Fin s.κ) :
    (V → G ⧸ H → K) ≃ₗ[K]
      (((Fin s.κ × I) → G ⧸ H → K) × (Fin s.κ → s.residual H ι commutes)) :=
  (s.rangeChart H ι commutes charts).symm.trans <|
    (FiniteStages.splitCopies (s.concreteSplit H ι commutes) (Fin s.κ)).trans <|
      (FiniteStages.uncurryLinear (Fin s.κ) I (G ⧸ H → K)).prodCongr (LinearEquiv.refl K _)

theorem unexpandedSplit_covariant
    (charts charts' : ∀ v, (G ⧸ H) ≃ (G ⧸ (H ⊔ (s.J v).map ι)) × Fin s.κ)
    (g : G)
    (hcharts : ∀ v c j, (charts' v).symm (g • c, j) = g • (charts v).symm (c, j))
    (f : V → G ⧸ H → K) :
    s.unexpandedSplit H ι commutes charts' (CosetOperators.trackShift H g f) =
      (CosetOperators.trackShift H g (s.unexpandedSplit H ι commutes charts f).1,
        fun c => s.residualShift H ι commutes g
          ((s.unexpandedSplit H ι commutes charts f).2 c)) := by
  have hcopy := s.rangeChart_symm_covariant H ι commutes charts charts' g hcharts f
  apply Prod.ext
  · funext c
    change (s.concreteSplit H ι commutes).U
      (((s.rangeChart H ι commutes charts').symm (CosetOperators.trackShift H g f) c.1).val)
      c.2 = _
    rw [congrFun hcopy c.1]
    exact congrFun (s.U_covariant H ι commutes g
      (((s.rangeChart H ι commutes charts).symm f c.1).val)) c.2
  · funext c
    apply Subtype.ext
    change (s.concreteSplit H ι commutes).Q
      (((s.rangeChart H ι commutes charts').symm (CosetOperators.trackShift H g f) c).val) = _
    rw [congrFun hcopy c]
    exact s.Q_covariant H ι commutes g
      (((s.rangeChart H ι commutes charts).symm f c).val)

section Topology
variable [TopologicalSpace K] [IsTopologicalRing K]

theorem continuous_unexpandedSplit
    (charts : ∀ v, (G ⧸ H) ≃ (G ⧸ (H ⊔ (s.J v).map ι)) × Fin s.κ) :
    Continuous (s.unexpandedSplit H ι commutes charts) := by
  have hcopy (c : Fin s.κ) : Continuous (fun f : V → G ⧸ H → K =>
      (((s.rangeChart H ι commutes charts).symm f c).val)) :=
    continuous_subtype_val.comp ((continuous_apply c).comp
      (s.continuous_rangeChart_symm H ι commutes charts))
  apply Continuous.prodMk
  · apply continuous_pi
    intro c
    exact (continuous_apply c.2).comp ((s.continuous_U H ι commutes).comp (hcopy c.1))
  · apply continuous_pi
    intro c
    exact ((s.continuous_Q H ι commutes).comp (hcopy c)).subtype_mk _

end Topology

section ActualAmbient
variable [MeasurableSpace K] [MeasurableSingletonClass K] [LinearOrder K]
  [TopologicalSpace K] [DiscreteTopology K] [BorelSpace K] [IsTopologicalRing K]

variable [MeasurableSpace V] [MeasurableSingletonClass V]

local instance quotientMeasurable (L : Subgroup (Ambient.G N)) :
    MeasurableSpace (Ambient.G N ⧸ L) := ⊤
local instance quotientMeasurableSingleton (L : Subgroup (Ambient.G N)) :
    MeasurableSingletonClass (Ambient.G N ⧸ L) := ⟨fun _ => trivial⟩

instance ambientResidual_secondCountable (a : ℕ) :
    SecondCountableTopology
      (s.residual (Ambient.Hseq N a) (Ambient.includeN N) (s.ambient_commutes a)) :=
  TopologicalSpace.secondCountableTopology_induced _ (V → Ambient.G N ⧸ Ambient.Hseq N a → K)
    Subtype.val

/-- The residual family extracted by one amplified split at lamp level a. -/
abbrev ambientResiduals (a : ℕ) :=
  Fin s.κ → s.residual (Ambient.Hseq N a) (Ambient.includeN N) (s.ambient_commutes a)

instance ambientResiduals_secondCountable (a : ℕ) :
    SecondCountableTopology (s.ambientResiduals a) := by
  letI := s.ambientResidual_secondCountable a
  infer_instance

instance ambientResiduals_borel (a : ℕ) : BorelSpace (s.ambientResiduals a) := by
  letI := s.ambientResidual_secondCountable a
  letI : BorelSpace
      (s.residual (Ambient.Hseq N a) (Ambient.includeN N) (s.ambient_commutes a)) :=
    inferInstance
  infer_instance

def ambientResidualsLaw (a : ℕ) : Measure (s.ambientResiduals a) :=
  iidLaw (Fin s.κ)
    (s.residualLaw (Ambient.Hseq N a) (Ambient.includeN N) (s.ambient_commutes a))

instance ambientResidualsLaw_probability (a : ℕ) :
    IsProbabilityMeasure (s.ambientResidualsLaw a) := by
  unfold ambientResidualsLaw iidLaw
  infer_instance

instance ambientResidualsLaw_haar (a : ℕ) :
    (s.ambientResidualsLaw a).IsAddHaarMeasure := by
  letI := s.ambientResiduals_borel a
  letI : MeasurableAdd
      (s.residual (Ambient.Hseq N a) (Ambient.includeN N) (s.ambient_commutes a)) :=
    inferInstance
  exact infinitePi_isAddHaarMeasure _

/-- Joint measurability for the concrete marker-dependent unexpanded split. -/
theorem measurable_ambientUnexpandedSplit (a r : ℕ) :
    Measurable (fun p : (Ambient.markerGeometry N).goodMarker (K := K) ×
      (V → Ambient.G N ⧸ Ambient.Hseq N a → K) =>
      s.unexpandedSplit (Ambient.Hseq N a) (Ambient.includeN N) (s.ambient_commutes a)
        (s.ambientSplitCharts a r p.1) p.2) := by
  let H := Ambient.Hseq N a
  let ι := Ambient.includeN N
  let commutes := s.ambient_commutes a
  let charts := s.ambientSplitCharts a r
  have hev : Measurable (fun p : (V → Ambient.G N ⧸ H → K) ×
      (V × (Ambient.G N ⧸ H)) => p.1 p.2.1 p.2.2) :=
    measurable_from_prod_countable_left fun c =>
      (measurable_pi_apply c.2).comp (measurable_pi_apply c.1)
  have hcopy (c : Fin s.κ) : Measurable
      (fun p : (Ambient.markerGeometry N).goodMarker (K := K) ×
        (V → Ambient.G N ⧸ H → K) =>
        ((s.rangeChart H ι commutes (charts p.1)).symm p.2 c).val) := by
    apply Measurable.of_eval
    intro v
    apply Measurable.of_eval
    intro x
    letI : Finite (H ⊔ s.ambientJ v : Subgroup (Ambient.G N)) :=
      s.ambient_join_finite a v
    have hi := CosetCoordinates.measurable_sortedCosetChart_symm (K := K)
      (Ambient.markerGeometry N) H (H ⊔ s.ambientJ v) le_sup_left
      (s.ambient_join_le_D a v) (s.ambient_join_quotient_card a v) r
    exact hev.comp (measurable_snd.prodMk
      (measurable_const.prodMk (hi.comp (measurable_fst.prodMk measurable_const))))
  apply Measurable.prodMk
  · apply Measurable.of_eval
    intro c
    exact (measurable_pi_apply c.2).comp
      ((s.continuous_U H ι commutes).measurable.comp (hcopy c.1))
  · apply Measurable.of_eval
    intro c
    exact ((s.continuous_Q H ι commutes).measurable.comp (hcopy c)).subtype_mk

/-- The actual unexpanded rectangle is a relative probability isomorphism.
The inverse's joint measurability is derived, and Haar preservation follows
from continuity and surjectivity of this concrete linear equivalence. -/
def relativeUnexpandedSplit (a r : ℕ) (μ : Measure K)
    [IsProbabilityMeasure μ] [μ.IsAddHaarMeasure] :
    RelativeProbabilityIso ((Ambient.markerGeometry N).goodMarker (K := K))
      (iidLaw V (iidLaw (Ambient.G N ⧸ Ambient.Hseq N a) μ))
      ((iidLaw (Fin s.κ × I) (iidLaw (Ambient.G N ⧸ Ambient.Hseq N a) μ)).prod
        (s.ambientResidualsLaw a)) := by
  letI : StandardBorelSpace ((Ambient.markerGeometry N).goodMarker (K := K)) :=
    (MarkerGeometry.measurable_goodMarker (Ambient.markerGeometry N)).standardBorel
  letI : StandardBorelSpace
      (s.residual (Ambient.Hseq N a) (Ambient.includeN N) (s.ambient_commutes a)) :=
    (s.residual_isClosed (Ambient.Hseq N a) (Ambient.includeN N)
      (s.ambient_commutes a)).measurableSet.standardBorel
  letI := s.ambientResiduals_secondCountable a
  letI := s.ambientResiduals_borel a
  letI := infinitePi_isAddHaarMeasure (fun _ : Ambient.G N ⧸ Ambient.Hseq N a => μ)
  letI := infinitePi_isAddHaarMeasure
    (fun _ : V => iidLaw (Ambient.G N ⧸ Ambient.Hseq N a) μ)
  letI := infinitePi_isAddHaarMeasure
    (fun _ : Fin s.κ × I => iidLaw (Ambient.G N ⧸ Ambient.Hseq N a) μ)
  refine RelativeProbabilityIso.ofFiberwise
    (fun ω => s.unexpandedSplit (Ambient.Hseq N a) (Ambient.includeN N)
      (s.ambient_commutes a) (s.ambientSplitCharts a r ω))
    (s.measurable_ambientUnexpandedSplit a r) (fun ω => LinearEquiv.bijective _) ?_
  intro ω
  exact (s.unexpandedSplit (Ambient.Hseq N a) (Ambient.includeN N)
    (s.ambient_commutes a) (s.ambientSplitCharts a r ω)).toAddEquiv.toAddMonoidHom.measurePreserving
      (s.continuous_unexpandedSplit _ _ _ _) (LinearEquiv.surjective _) (by simp)

@[simp] theorem relativeUnexpandedSplit_apply (a r : ℕ) (μ : Measure K)
    [IsProbabilityMeasure μ] [μ.IsAddHaarMeasure]
    (ω : (Ambient.markerGeometry N).goodMarker (K := K))
    (x : V → Ambient.G N ⧸ Ambient.Hseq N a → K) :
    (s.relativeUnexpandedSplit a r μ).equiv ω x =
      s.unexpandedSplit (Ambient.Hseq N a) (Ambient.includeN N) (s.ambient_commutes a)
        (s.ambientSplitCharts a r ω) x := rfl

theorem relativeUnexpandedSplit_covariant (a r : ℕ) (μ : Measure K)
    [IsProbabilityMeasure μ] [μ.IsAddHaarMeasure] (g : Ambient.G N)
    (ω : (Ambient.markerGeometry N).goodMarker (K := K))
    (x : V → Ambient.G N ⧸ Ambient.Hseq N a → K) :
    (s.relativeUnexpandedSplit a r μ).equiv
      ⟨MarkerGeometry.markerShift g ω.val, (Ambient.markerGeometry N).goodMarker_shift g ω.property⟩
      (CosetOperators.trackShift (Ambient.Hseq N a) g x) =
      (CosetOperators.trackShift (Ambient.Hseq N a) g
        ((s.relativeUnexpandedSplit a r μ).equiv ω x).1,
        fun c => s.residualShift (Ambient.Hseq N a) (Ambient.includeN N)
          (s.ambient_commutes a) g (((s.relativeUnexpandedSplit a r μ).equiv ω x).2 c)) := by
  exact s.unexpandedSplit_covariant _ _ _ _ _ g
    (fun v c j => s.ambientSplitCharts_symm_covariant a r g ω v c j) x

end ActualAmbient
end BernoulliIso.AlgebraicInput

#print axioms BernoulliIso.AlgebraicInput.relativeUnexpandedSplit
#print axioms BernoulliIso.AlgebraicInput.relativeUnexpandedSplit_covariant
