module

public import BernoulliIso.CosetCoordinates
public import BernoulliIso.MarkerAdaptation

/-!
The actual priority chart uses only its own D-coset's marker history.
Restricting to the global good-marker domain does not reveal later streams:
all measurability statements use the explicitly pulled-back history.
-/

@[expose] public section
noncomputable section
open MeasureTheory

namespace BernoulliIso.CosetCoordinates

variable {G K Ω : Type*} [Group G] (a : MarkerGeometry G)
  [Fintype K] [Nonempty K] [MeasurableSpace K] [MeasurableSingletonClass K] [LinearOrder K]

theorem siteStream_past_measurable (marker : Ω → G → K) (g u : G)
    (hu : g⁻¹ * u ∈ a.D) (r n : ℕ) (hr : r < n) :
    Measurable[MeasurableSpace.comap (a.pastRead g n ∘ marker) inferInstance]
      (fun ω => siteStream a r (marker ω) u) := by
  let : MeasurableSpace Ω := MeasurableSpace.comap (a.pastRead g n ∘ marker) inferInstance
  apply Measurable.of_eval
  intro j
  let i : a.pastIndices n := ⟨(⟨g⁻¹ * u, hu⟩, (r, j)), hr⟩
  have hm := (measurable_pi_apply i).comp (comap_measurable (a.pastRead g n ∘ marker))
  convert hm using 1
  funext ω
  simp [i, MarkerGeometry.pastRead, MarkerGeometry.digits,
    MarkerGeometry.address, siteStream, mul_assoc]

theorem cosetPriority_past_measurable (marker : Ω → G → K)
    (H : Subgroup G) [Finite H] (hHD : H ≤ a.D) (g : G) (c : G ⧸ H)
    (hc : Subgroup.quotientMapOfLE hHD c = QuotientGroup.mk g)
    (r n : ℕ) (hr : r < n) :
    Measurable[MeasurableSpace.comap (a.pastRead g n ∘ marker) inferInstance]
      (fun ω => cosetPriority a H r (marker ω) c) := by
  let : MeasurableSpace Ω := MeasurableSpace.comap (a.pastRead g n ∘ marker) inferInstance
  apply FiniteOrdering.measurable_minimumStream.comp
  apply Measurable.of_eval
  intro u
  have huD : (QuotientGroup.mk u.val : G ⧸ a.D) = QuotientGroup.mk g :=
    (congrArg (Subgroup.quotientMapOfLE hHD) u.property).trans hc
  exact siteStream_past_measurable a marker g u.val
    (QuotientGroup.eq.mp huD.symm) r n hr

theorem quotientMap_comp {H L D : Subgroup G} (hHL : H ≤ L) (hLD : L ≤ D)
    (x : G ⧸ H) :
    Subgroup.quotientMapOfLE hLD (Subgroup.quotientMapOfLE hHL x) =
      Subgroup.quotientMapOfLE (hHL.trans hLD) x := by
  induction x using QuotientGroup.induction_on with
  | H g => rfl

theorem sortedCosetChart_rank_past_measurable
    (H L : Subgroup G) [Finite H] [Finite L] (hHL : H ≤ L) (hLD : L ≤ a.D)
    {κ : ℕ} (hcard : Nat.card (L ⧸ H.subgroupOf L) = κ)
    (g : G) (x : G ⧸ H)
    (hx : Subgroup.quotientMapOfLE (hHL.trans hLD) x = QuotientGroup.mk g)
    (r n : ℕ) (hr : r < n) :
    Measurable[MeasurableSpace.comap
      (a.pastRead g n ∘ (Subtype.val : a.goodMarker (K := K) → G → K)) inferInstance]
      (fun ω => (sortedCosetChart a H L hHL hLD hcard r ω x).2) := by
  let : MeasurableSpace (a.goodMarker (K := K)) := MeasurableSpace.comap
    (a.pastRead g n ∘ Subtype.val) inferInstance
  let : ∀ c, Fintype (Fiber (Subgroup.quotientMapOfLE hHL) c) :=
    fun _ => Fintype.ofFinite _
  have hp (z : Fiber (Subgroup.quotientMapOfLE hHL)
      (Subgroup.quotientMapOfLE hHL x)) :
      Measurable (fun ω : a.goodMarker (K := K) => cosetPriority a H r ω.val z.val) := by
    apply cosetPriority_past_measurable a Subtype.val H (hHL.trans hLD) g z.val _ r n hr
    rw [← quotientMap_comp hHL hLD, z.property, quotientMap_comp hHL hLD, hx]
  have hm := (FiniteOrdering.measurable_rankNat
    (⟨x, rfl⟩ : Fiber (Subgroup.quotientMapOfLE hHL)
      (Subgroup.quotientMapOfLE hHL x))).comp (Measurable.of_eval hp)
  apply measurable_to_countable'
  intro j
  have heq : {ω : a.goodMarker (K := K) |
      (sortedCosetChart a H L hHL hLD hcard r ω x).2 = j} =
      {ω | FiniteOrdering.rankNat
        (fun z : Fiber (Subgroup.quotientMapOfLE hHL)
            (Subgroup.quotientMapOfLE hHL x) => cosetPriority a H r ω.val z.val)
        ⟨x, rfl⟩ = j.val} := by
    ext ω
    exact Fin.ext_iff
  change MeasurableSet {ω : a.goodMarker (K := K) |
    (sortedCosetChart a H L hHL hLD hcard r ω x).2 = j}
  rw [heq]
  exact measurableSet_eq_fun hm measurable_const

/-- The same locality holds in the exact current-stream field, before
any other stream is revealed. -/
theorem siteStream_fresh_measurable (marker : Ω → G → K) (g u : G)
    (hu : g⁻¹ * u ∈ a.D) (r : ℕ) :
    Measurable[MeasurableSpace.comap (a.freshRead g r ∘ marker) inferInstance]
      (fun ω => siteStream a r (marker ω) u) := by
  let : MeasurableSpace Ω := MeasurableSpace.comap (a.freshRead g r ∘ marker) inferInstance
  apply Measurable.of_eval
  intro j
  let i : a.freshIndices r := ⟨(⟨g⁻¹ * u, hu⟩, (r, j)), rfl⟩
  have hm := (measurable_pi_apply i).comp (comap_measurable (a.freshRead g r ∘ marker))
  convert hm using 1
  funext ω
  simp [i, MarkerGeometry.freshRead, MarkerGeometry.digits,
    MarkerGeometry.address, siteStream, mul_assoc]

theorem cosetPriority_fresh_measurable (marker : Ω → G → K)
    (H : Subgroup G) [Finite H] (hHD : H ≤ a.D) (g : G) (c : G ⧸ H)
    (hc : Subgroup.quotientMapOfLE hHD c = QuotientGroup.mk g)
    (r : ℕ) :
    Measurable[MeasurableSpace.comap (a.freshRead g r ∘ marker) inferInstance]
      (fun ω => cosetPriority a H r (marker ω) c) := by
  let : MeasurableSpace Ω := MeasurableSpace.comap (a.freshRead g r ∘ marker) inferInstance
  apply FiniteOrdering.measurable_minimumStream.comp
  apply Measurable.of_eval
  intro u
  have huD : (QuotientGroup.mk u.val : G ⧸ a.D) = QuotientGroup.mk g :=
    (congrArg (Subgroup.quotientMapOfLE hHD) u.property).trans hc
  exact siteStream_fresh_measurable a marker g u.val
    (QuotientGroup.eq.mp huD.symm) r

theorem sortedCosetChart_rank_fresh_measurable
    (H L : Subgroup G) [Finite H] [Finite L] (hHL : H ≤ L) (hLD : L ≤ a.D)
    {κ : ℕ} (hcard : Nat.card (L ⧸ H.subgroupOf L) = κ)
    (g : G) (x : G ⧸ H)
    (hx : Subgroup.quotientMapOfLE (hHL.trans hLD) x = QuotientGroup.mk g)
    (r : ℕ) :
    Measurable[MeasurableSpace.comap
      (a.freshRead g r ∘ (Subtype.val : a.goodMarker (K := K) → G → K)) inferInstance]
      (fun ω => (sortedCosetChart a H L hHL hLD hcard r ω x).2) := by
  let : MeasurableSpace (a.goodMarker (K := K)) := MeasurableSpace.comap
    (a.freshRead g r ∘ Subtype.val) inferInstance
  let : ∀ c, Fintype (Fiber (Subgroup.quotientMapOfLE hHL) c) :=
    fun _ => Fintype.ofFinite _
  have hp (z : Fiber (Subgroup.quotientMapOfLE hHL)
      (Subgroup.quotientMapOfLE hHL x)) :
      Measurable (fun ω : a.goodMarker (K := K) => cosetPriority a H r ω.val z.val) := by
    apply cosetPriority_fresh_measurable a Subtype.val H (hHL.trans hLD) g z.val _ r
    rw [← quotientMap_comp hHL hLD, z.property, quotientMap_comp hHL hLD, hx]
  have hm := (FiniteOrdering.measurable_rankNat
    (⟨x, rfl⟩ : Fiber (Subgroup.quotientMapOfLE hHL)
      (Subgroup.quotientMapOfLE hHL x))).comp (Measurable.of_eval hp)
  apply measurable_to_countable'
  intro j
  have heq : {ω : a.goodMarker (K := K) |
      (sortedCosetChart a H L hHL hLD hcard r ω x).2 = j} =
      {ω | FiniteOrdering.rankNat
        (fun z : Fiber (Subgroup.quotientMapOfLE hHL)
            (Subgroup.quotientMapOfLE hHL x) => cosetPriority a H r ω.val z.val)
        ⟨x, rfl⟩ = j.val} := by
    ext ω
    exact Fin.ext_iff
  change MeasurableSet {ω : a.goodMarker (K := K) |
    (sortedCosetChart a H L hHL hLD hcard r ω x).2 = j}
  rw [heq]
  exact measurableSet_eq_fun hm measurable_const

end BernoulliIso.CosetCoordinates

#print axioms BernoulliIso.CosetCoordinates.siteStream_fresh_measurable
#print axioms BernoulliIso.CosetCoordinates.cosetPriority_fresh_measurable
#print axioms BernoulliIso.CosetCoordinates.sortedCosetChart_rank_fresh_measurable
