module

public import BernoulliIso.ConcreteAdaptation
public import BernoulliIso.ConcreteLocality
public import BernoulliIso.CosetSelection
public import BernoulliIso.SparseTower
public import BernoulliIso.Conjugacy

/-!
Almost-sure recovery for the actual lamp-subgroup tower. The probability
measure is the actual finite-alphabet Bernoulli marker restricted to its
conull good-marker domain. All primitive inputs of sparse-row recovery
are discharged by the implemented stages, charts, and cardinality schedule.
-/

@[expose] public section
noncomputable section
open MeasureTheory
open scoped Classical ENNReal

namespace BernoulliIso.AlgebraicInput

variable {K N I V : Type*} [Field K] [Fintype K]
  [Group N] [Countable N] [Fintype I] [Fintype V] [Nonempty I] [Nonempty V]
  [MeasurableSpace K] [MeasurableSingletonClass K] [LinearOrder K]
variable (s : AlgebraicInput K N I V)

/-- The original uniform Bernoulli marker law, on its conull good domain. -/
def concreteMarkerLaw (s : AlgebraicInput K N I V) : Measure s.markerSpace :=
  (MarkerGeometry.markerLaw (G := Ambient.G N) K).comap Subtype.val

instance concreteMarkerLaw_isProbabilityMeasure : IsProbabilityMeasure s.concreteMarkerLaw :=
  (MeasurableEmbedding.subtype_coe
    ((Ambient.markerGeometry N).measurable_goodMarker (K := K))).isProbabilityMeasure_comap
      (by simpa using (Ambient.markerGeometry N).ae_goodMarker (K := K))

theorem concreteMarkerLaw_inclusion :
    MeasurePreserving (Subtype.val : s.markerSpace → Ambient.G N → K)
      s.concreteMarkerLaw (MarkerGeometry.markerLaw (G := Ambient.G N) K) :=
  measurePreserving_conullSubtype _
    ((Ambient.markerGeometry N).measurable_goodMarker (K := K))
    ((Ambient.markerGeometry N).ae_goodMarker (K := K))

/-- The actual arithmetic schedule is exactly the recursively derived row bound. -/
theorem concrete_rowBound (n : ℕ) :
    SparseTower.rowBound s.rowConstant (StageSchedule.repetitions s.rowConstant) n =
      StageSchedule.bound s.rowConstant n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [SparseTower.rowBound, ih, StageSchedule.bound_succ]

/-- The implemented Option selector is the concrete packet event, with
finite indices and all digits read from the fixed original D-component
center. The static packet enumeration is only a presentation of its law. -/
theorem stageSelection_packet (n : ℕ) (a : s.stageCoordinates n) :
    ∃ sites : (Fin (StageSchedule.discarded s.rowConstant n + 1) ×
        Fin (Nat.card (s.stageH n))) ↪ (Ambient.markerGeometry N).D,
      ∃ i : Fin (StageSchedule.discarded s.rowConstant n + 1),
        ∀ ω : s.markerSpace, s.stageSelection ω n a ≠ none ↔
          ω.val ∈ (Ambient.markerGeometry N).packetSelected
            (s.stageComponent n a).out (2 * n) sites i := by
  let H := s.stageH n
  let L := s.stageH (n + 1)
  let hHL : H ≤ L := s.stageH_step n
  let hLD : L ≤ (Ambient.markerGeometry N).D := s.stageH_le_D (n + 1)
  let c : Ambient.G N ⧸ L := Subgroup.quotientMapOfLE hHL a.2
  let g : Ambient.G N := c.out
  let base : Ambient.G N := (s.stageComponent n a).out
  let P := CosetCoordinates.Fiber (Subgroup.quotientMapOfLE hHL) (QuotientGroup.mk g)
  let : Fintype H := Fintype.ofFinite H
  let : Fintype P := Fintype.ofFinite P
  let z : P := ⟨a.2, (Quotient.out_eq' c).symm⟩
  have hp : Fintype.card P = StageSchedule.discarded s.rowConstant n + 1 := by
    rw [← Nat.card_eq_fintype_card,
      Nat.card_congr (CosetCoordinates.quotientFiberEquiv hHL (QuotientGroup.mk g))]
    exact s.stageH_quotient_card n
  let e : P ≃ Fin (StageSchedule.discarded s.rowConstant n + 1) :=
    (Fintype.equivFin P).trans (finCongr hp)
  let f : H ≃ Fin (Nat.card H) :=
    (Fintype.equivFin H).trans (finCongr (Nat.card_eq_fintype_card.symm))
  let sites₀ : (P × H) ↪ (Ambient.markerGeometry N).D :=
    CosetCoordinates.packetSites (Ambient.markerGeometry N) H L hHL hLD g
  let sites₁ : (Fin (StageSchedule.discarded s.rowConstant n + 1) × Fin (Nat.card H)) ↪
      (Ambient.markerGeometry N).D :=
    (e.symm.prodCongr f.symm).toEmbedding.trans sites₀
  have hg : (QuotientGroup.mk g : Ambient.G N ⧸ Ambient.D N) = s.stageComponent n a := by
    change Subgroup.quotientMapOfLE hLD (QuotientGroup.mk g) = _
    rw [show (QuotientGroup.mk g : Ambient.G N ⧸ L) = c from Quotient.out_eq' c]
    exact CosetCoordinates.quotientMap_comp hHL hLD a.2
  have hbase : base⁻¹ * g ∈ (Ambient.markerGeometry N).D :=
    QuotientGroup.eq.mp ((Quotient.out_eq' (s.stageComponent n a)).trans hg.symm)
  let sites₂ := sites₁.trans
    (Equiv.mulLeft (⟨base⁻¹ * g, hbase⟩ : (Ambient.markerGeometry N).D)).toEmbedding
  refine ⟨sites₂, e z, ?_⟩
  intro ω
  have hzero : s.stageSelection ω n a ≠ none ↔
      (CosetCoordinates.sortedCosetChart (Ambient.markerGeometry N) H L hHL hLD
        (s.stageH_quotient_card n) (2 * n) ω a.2).2 = 0 := by
    change (if (s.stageRegroupChart n ω a).2 = 0 then
      some (s.stageRegroupChart n ω a).1 else none) ≠ none ↔
        (s.stageRegroupChart n ω a).2 = 0
    by_cases h : (s.stageRegroupChart n ω a).2 = 0 <;> simp [h]

  have hz := CosetCoordinates.sortedCosetChart_zero_iff_packetSelected
    (Ambient.markerGeometry N) H L hHL hLD (s.stageH_quotient_card n) g (2 * n) ω z
  have hreindex := CosetCoordinates.packetSelected_reindex
    (Ambient.markerGeometry N) g (2 * n) sites₀ e f ω.val z
  have hcenter := CosetCoordinates.packetSelected_changeBase
    (Ambient.markerGeometry N) base g hbase (2 * n) sites₁ ω.val (e z)
  exact hzero.trans (hz.trans (hreindex.symm.trans hcenter.symm))

/-- Every original coordinate is recovered almost surely by the actual
specified tower. No contraction, exhaustion, selector law, local-row
adaptation, or stage-section identity is assumed in this theorem. -/
theorem ae_concreteTower_extract_injective :
    ∀ᵐ ω ∂s.concreteMarkerLaw, Function.Injective (s.concreteTower ω).extract := by
  let sites (n : ℕ) (a : s.stageCoordinates n) := (s.stageSelection_packet n a).choose
  let index (n : ℕ) (a : s.stageCoordinates n) :=
    (s.stageSelection_packet n a).choose_spec.choose
  have hselected (n : ℕ) (a : s.stageCoordinates n) :
      {ω : s.markerSpace | s.stageSelection ω n a ≠ none} =
        (Subtype.val : s.markerSpace → Ambient.G N → K) ⁻¹'
          (Ambient.markerGeometry N).packetSelected (s.stageComponent n a).out
            (2 * n) (sites n a) (index n a) := by
    ext ω
    exact (s.stageSelection_packet n a).choose_spec.choose_spec ω
  apply SparseTower.ae_extract_injective_of_packet_rows
    (Ambient.markerGeometry N) s.concreteMarkerLaw Subtype.val s.concreteMarkerLaw_inclusion
    s.stageComponent (fun c => c.out) s.stageSelection s.stageSplitRows
    (StageSchedule.repetitions s.rowConstant) s.rowConstant s.stageSplitRows_bound
    s.stageSelection_local s.stageSplitRows_local
    (L := fun n => StageSchedule.discarded s.rowConstant n + 1)
    (H := fun n => Nat.card (s.stageH n))
    (sites := sites) (packetIndex := index) (hselectedEvent := hselected)
    (tower := s.concreteTower)
  · intro n a b
    exact s.stageInsertion_coeff_fresh_measurable n a b (s.stageComponent n a).out
      (Quotient.out_eq' (s.stageComponent n a)).symm
  · intro n a b
    exact s.stageSplitRows_coeff_fresh_measurable n a b (s.stageComponent (n + 1) a).out
      (Quotient.out_eq' (s.stageComponent (n + 1) a)).symm
  · intro n
    exact Nat.zero_lt_succ _
  · intro n
    exact Nat.card_pos
  · intro n
    rw [s.concrete_rowBound, StageSchedule.discarded_succ]
    exact StageSchedule.twice_bound_le_packets s.rowConstant n
  · intro ω n f a
    exact s.concreteStage_section_rows ω n f a

end BernoulliIso.AlgebraicInput

#print axioms BernoulliIso.AlgebraicInput.stageSelection_packet
#print axioms BernoulliIso.AlgebraicInput.ae_concreteTower_extract_injective
