module

public import BernoulliIso.Marker
public import BernoulliIso.Conjugacy

/-! The concrete iid marker law is invariant under the actual shift,
including its conull tie-free restriction. -/

@[expose] public section
noncomputable section
open MeasureTheory

namespace BernoulliIso.MarkerGeometry

variable {G K : Type*} [Group G] [Countable G]
  [Fintype K] [Nonempty K] [MeasurableSpace K] [MeasurableSingletonClass K]

theorem measurePreserving_markerShift (g : G) :
    MeasurePreserving (markerShift (K := K) g) (markerLaw (G := G) K)
      (markerLaw (G := G) K) := by
  refine ⟨Measurable.of_eval (fun u => measurable_pi_apply (g⁻¹ * u)), ?_⟩
  exact Measure.map_infinitePi_infinitePi_of_inj
    (show Function.Injective (fun u : G => g⁻¹ * u) from fun _ _ h => mul_left_cancel h)

variable (a : MarkerGeometry G) [Nontrivial K]

theorem measurePreserving_goodMarkerShift (g : G) :
    MeasurePreserving
      (fun ω : a.goodMarker (K := K) =>
        (⟨markerShift g ω.val, a.goodMarker_shift g ω.property⟩ : a.goodMarker (K := K)))
      ((markerLaw (G := G) K).comap (Subtype.val : a.goodMarker (K := K) → G → K))
      ((markerLaw (G := G) K).comap (Subtype.val : a.goodMarker (K := K) → G → K)) := by
  have hs := a.measurable_goodMarker (K := K)
  have hcoe := measurePreserving_conullSubtype (markerLaw (G := G) K) hs a.ae_goodMarker
  have hshift := measurePreserving_markerShift (K := K) g
  have hm : Measurable
      (fun ω : a.goodMarker (K := K) =>
        (⟨markerShift g ω.val, a.goodMarker_shift g ω.property⟩ : a.goodMarker (K := K))) :=
    (hshift.measurable.comp measurable_subtype_coe).subtype_mk
  refine ⟨hm, ?_⟩
  apply (MeasurableEmbedding.subtype_coe hs).map_injective
  rw [Measure.map_map measurable_subtype_coe hm]
  change Measure.map (markerShift g ∘ Subtype.val) _ = Measure.map Subtype.val _
  rw [← Measure.map_map hshift.measurable measurable_subtype_coe,
    hcoe.map_eq, hshift.map_eq]

end BernoulliIso.MarkerGeometry

#print axioms BernoulliIso.MarkerGeometry.measurePreserving_goodMarkerShift
