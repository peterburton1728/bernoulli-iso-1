module

public import BernoulliIso.FiniteOrdering
public import BernoulliIso.SparseRows
public import Mathlib.Dynamics.Ergodic.MeasurePreserving

/-!
Adapted finite rows and conull marker models. All sigma-algebras below are
explicit. A conull restriction is handled by a measure-preserving marker
map, rather than by a global default extension that could reveal future
streams.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace BernoulliIso

namespace MarkerGeometry

variable {G K Ω I J A : Type*} [Group G] (a : MarkerGeometry G)
  [Fintype K] [Nonempty K] [Nontrivial K]
  [MeasurableSpace K] [MeasurableSingletonClass K] [LinearOrder K]
  [MeasurableSpace Ω] [Fintype I] [Nonempty I] [Fintype J] [Nonempty J]

/-- Concrete marker freshness transfers to every measure-preserving model
of the marker space, including its invariant conull good-marker subtype.
The support is adapted to the pulled-back past sigma-algebra. -/
theorem support_fiber_packet_bound_pullback (g : G) (r : ℕ)
    {μ : Measure Ω} (marker : Ω → G → K)
    (hm : MeasurePreserving marker μ (markerLaw (G := G) K))
    (support : Ω → Finset A) (s : Finset A)
    (hs : MeasurableSet[MeasurableSpace.comap (a.pastRead g r ∘ marker) inferInstance]
      {ω | support ω = s})
    (sites : (I × J) ↪ a.D) (i : I) :
    μ ({ω | support ω = s} ∩ marker ⁻¹' a.packetSelected g r sites i) ≤
      (Fintype.card I : ℝ≥0∞)⁻¹ * μ {ω | support ω = s} := by
  obtain ⟨B, hB, hEq⟩ := MeasurableSpace.measurableSet_comap.1 hs
  let E : Set (G → K) := a.pastRead g r ⁻¹' B
  have hEpast : MeasurableSet[a.pastSigma g r] E :=
    MeasurableSpace.measurableSet_comap.2 ⟨B, hB, rfl⟩
  have hE : MeasurableSet E := hB.preimage (a.measurable_pastRead g r)
  have hpre : marker ⁻¹' E = {ω | support ω = s} := hEq
  have hF : MeasurableSet (a.packetSelected (K := K) g r sites i) :=
    (FiniteOrdering.measurable_packetSet i).preimage (a.measurable_blockDigits g r sites)
  have hμE : μ {ω | support ω = s} = markerLaw (G := G) K E := by
    rw [← hpre, ← hm.map_eq, Measure.map_apply hm.measurable hE]
  calc
    μ ({ω | support ω = s} ∩ marker ⁻¹' a.packetSelected g r sites i) =
        μ (marker ⁻¹' (E ∩ a.packetSelected g r sites i)) := by
      rw [Set.preimage_inter, hpre]
    _ = markerLaw (G := G) K (E ∩ a.packetSelected g r sites i) := by
      rw [← hm.map_eq, Measure.map_apply hm.measurable (hE.inter hF)]
    _ = markerLaw (G := G) K (a.packetSelected g r sites i) *
        markerLaw (G := G) K E := by
      rw [a.past_inter_fresh g r hEpast (a.packetSelected_fresh g r sites i), mul_comm]
    _ ≤ (Fintype.card I : ℝ≥0∞)⁻¹ * markerLaw (G := G) K E :=
      mul_le_mul' (a.packetSelected_probability_le g r sites i) le_rfl
    _ = (Fintype.card I : ℝ≥0∞)⁻¹ * μ {ω | support ω = s} := by rw [hμE]

omit [Fintype K] [Nonempty K] [Nontrivial K] [MeasurableSingletonClass K] [LinearOrder K] in
/-- Earlier histories form an increasing filtration. -/
theorem pastSigma_mono (g : G) {m n : ℕ} (hmn : m ≤ n) :
    a.pastSigma (K := K) g m ≤ a.pastSigma g n := by
  let f : (a.pastIndices n → K) → a.pastIndices m → K :=
    fun η i => η ⟨i.val, Nat.lt_of_lt_of_le i.property hmn⟩
  apply MeasurableSpace.comap_le_comap_of_eq_comp f
  · exact Measurable.of_eval fun i =>
      measurable_pi_apply (⟨i.val, Nat.lt_of_lt_of_le i.property hmn⟩ : a.pastIndices n)
  · rfl

omit [Fintype K] [Nonempty K] [Nontrivial K] [MeasurableSingletonClass K] [LinearOrder K] in
/-- Once a stream has been used, all of its information lies in every later history. -/
theorem freshSigma_le_pastSigma (g : G) {r n : ℕ} (hrn : r < n) :
    a.freshSigma (K := K) g r ≤ a.pastSigma g n := by
  let f : (a.pastIndices n → K) → a.freshIndices r → K :=
    fun η i => η ⟨i.val, by change i.val.2.1 < n; rw [i.property]; exact hrn⟩
  apply MeasurableSpace.comap_le_comap_of_eq_comp f
  · exact Measurable.of_eval fun i =>
      measurable_pi_apply (⟨i.val, by change i.val.2.1 < n; rw [i.property]; exact hrn⟩ :
        a.pastIndices n)
  · rfl

end MarkerGeometry

namespace AdaptedRows

variable {Ω A K : Type*} [MeasurableSpace Ω] [Countable A]

/-- Finite-set fibers are measurable as soon as each membership test is
measurable. Countability of the ambient coordinates is the crucial point. -/
theorem finset_fiber_measurable (support : Ω → Finset A)
    (hmem : ∀ a, MeasurableSet {ω | a ∈ support ω}) (s : Finset A) :
    MeasurableSet {ω | support ω = s} := by
  classical
  have heq : {ω | support ω = s} =
      ⋂ a : A, (if a ∈ s then {ω | a ∈ support ω} else {ω | a ∉ support ω}) := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    constructor
    · intro h a
      subst s
      split <;> simp_all
    · intro h
      apply Finset.ext
      intro a
      by_cases ha : a ∈ s
      · have hh := h a
        simp only [ha, ↓reduceIte, Set.mem_ofPred_eq] at hh
        exact ⟨fun _ => ha, fun _ => hh⟩
      · have hh := h a
        simp only [ha, ↓reduceIte, Set.mem_ofPred_eq] at hh
        exact ⟨fun hmem => (hh hmem).elim, fun hmem => (ha hmem).elim⟩
  rw [heq]
  apply MeasurableSet.iInter
  intro a
  split
  · exact hmem a
  · exact (hmem a).compl

variable [Zero K] [MeasurableSpace K] [MeasurableSingletonClass K]

/-- Exact finite-row fibers follow from coefficientwise measurability;
no separately postulated measurable row-valued random variable is needed. -/
theorem row_fiber_measurable (row : Ω → A →₀ K)
    (hcoeff : ∀ a, Measurable (fun ω => row ω a)) (v : A →₀ K) :
    MeasurableSet {ω | row ω = v} := by
  have heq : {ω | row ω = v} = ⋂ a : A, {ω | row ω a = v a} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    exact ⟨fun h a => congrArg (fun r : A →₀ K => r a) h,
      fun h => Finsupp.ext h⟩
  rw [heq]
  exact MeasurableSet.iInter fun a => (measurableSet_singleton (v a)).preimage (hcoeff a)

/-- The actual support of a finite row has measurable fibers whenever its
coefficients are measurable. Cancellations and the empty support are retained. -/
theorem support_fiber_measurable (row : Ω → A →₀ K)
    (hcoeff : ∀ a, Measurable (fun ω => row ω a)) (s : Finset A) :
    MeasurableSet {ω | (row ω).support = s} := by
  apply finset_fiber_measurable (fun ω => (row ω).support) _ s
  intro a
  have h := ((measurableSet_singleton (0 : K)).preimage (hcoeff a)).compl
  change MeasurableSet {ω | row ω a ≠ 0} at h
  simpa only [Finsupp.mem_support_iff] using h

end AdaptedRows

namespace AdaptedRows

variable {Ω B C K : Type*} [MeasurableSpace Ω] [Countable B]
  [CommRing K] [Countable K] [MeasurableSpace K] [MeasurableSingletonClass K]

/-- Composition of actual finite coefficient rows preserves coefficientwise
measurability. We partition by the countably many finite supports, then use
an ordinary finite sum on each fiber. -/
theorem measurable_compose_coeff (row : Ω → B →₀ K) (next : Ω → B → C →₀ K)
    (hrow : ∀ b, Measurable (fun ω => row ω b))
    (hnext : ∀ b c, Measurable (fun ω => next ω b c)) (c : C) :
    Measurable (fun ω => SparseRows.compose (row ω) (next ω) c) := by
  classical
  have hcalc (ω : Ω) : SparseRows.compose (row ω) (next ω) c =
      ∑ b ∈ (row ω).support, row ω b * next ω b c := by
    simp [SparseRows.compose, Finsupp.sum]
  intro S hS
  have heq : (fun ω => SparseRows.compose (row ω) (next ω) c) ⁻¹' S =
      ⋃ s : Finset B, ({ω | (row ω).support = s} ∩
        {ω | (∑ b ∈ s, row ω b * next ω b c) ∈ S}) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · intro h
      exact ⟨(row ω).support, rfl, (hcalc ω) ▸ h⟩
    · rintro ⟨s, hs, h⟩
      rwa [hcalc, hs]
  rw [heq]
  apply MeasurableSet.iUnion
  intro s
  apply (support_fiber_measurable row hrow s).inter
  apply hS.preimage
  exact s.measurable_sum fun b _ => (hrow b).mul (hnext b c)

end AdaptedRows

namespace MarkerGeometry

variable {G K Ω I J A C : Type*} [Group G] (a : MarkerGeometry G)
  [Fintype K] [Nonempty K] [Nontrivial K]
  [MeasurableSpace K] [MeasurableSingletonClass K] [LinearOrder K]
  [MeasurableSpace Ω] [Fintype I] [Nonempty I] [Fintype J] [Nonempty J]
  [Countable A] [Zero C] [MeasurableSpace C] [MeasurableSingletonClass C]

/-- The concrete fresh-packet inequality for actual finite rows. The only
adaptation input is measurability of each coefficient in the inherited
past; measurability of every true-support fiber is a proved consequence. -/
theorem row_support_packet_bound_pullback (g : G) (r : ℕ)
    {μ : Measure Ω} (marker : Ω → G → K)
    (hm : MeasurePreserving marker μ (markerLaw (G := G) K))
    (row : Ω → A →₀ C)
    (hrow : ∀ b, Measurable[
      MeasurableSpace.comap (a.pastRead g r ∘ marker) inferInstance]
      (fun ω => row ω b))
    (s : Finset A) (sites : (I × J) ↪ a.D) (i : I) :
    μ ({ω | (row ω).support = s} ∩ marker ⁻¹' a.packetSelected g r sites i) ≤
      (Fintype.card I : ℝ≥0∞)⁻¹ * μ {ω | (row ω).support = s} := by
  have hs : MeasurableSet[
      MeasurableSpace.comap (a.pastRead g r ∘ marker) inferInstance]
      {ω | (row ω).support = s} := by
    letI : MeasurableSpace Ω :=
      MeasurableSpace.comap (a.pastRead g r ∘ marker) inferInstance
    exact AdaptedRows.support_fiber_measurable row hrow s
  exact a.support_fiber_packet_bound_pullback g r marker hm
    (fun ω => (row ω).support) s hs sites i

end MarkerGeometry
end BernoulliIso
