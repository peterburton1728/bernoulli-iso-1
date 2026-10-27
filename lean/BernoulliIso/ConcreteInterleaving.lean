module

public import BernoulliIso.CosetCoordinates
public import Mathlib.Basic.Denumerable

/-!
Actual marker-sorted finite-coset interleaving. No absorber is assumed:
finite H-cosets are ranked by the existing iid marker streams, and all
subsequent maps are coordinate permutations with their exact product laws.
-/

@[expose] public section
noncomputable section
open MeasureTheory

namespace BernoulliIso

abbrev iidLaw (S : Type*) {K : Type*} [MeasurableSpace K] (μ : Measure K) :
    Measure (S → K) := Measure.infinitePi (fun _ : S => μ)

namespace RelativeProbabilityIso

/-- Restrict every fiber to a common marker domain. In particular this is
used with the inclusion of the invariant conull recovery domain. -/
def pullback {Ω Ω' X Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure X} {ν : Measure Y}
    (e : RelativeProbabilityIso Ω μ ν) (f : Ω' → Ω) (hf : Measurable f) :
    RelativeProbabilityIso Ω' μ ν where
  equiv ω := e.equiv (f ω)
  jointlyMeasurable := e.jointlyMeasurable.comp ((hf.comp measurable_fst).prodMk measurable_snd)
  jointlyMeasurable_symm :=
    e.jointlyMeasurable_symm.comp ((hf.comp measurable_fst).prodMk measurable_snd)
  measurePreserving ω := e.measurePreserving (f ω)

theorem pullback_equivariant {G Ω Ω' X Y : Type*} [Group G]
    [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace X] [MeasurableSpace Y]
    [MulAction G Ω] [MulAction G Ω'] [MulAction G X] [MulAction G Y]
    {μ : Measure X} {ν : Measure Y} (e : RelativeProbabilityIso Ω μ ν)
    (he : e.Equivariant (G := G)) (f : Ω' → Ω) (hf : Measurable f)
    (hcov : ∀ (g : G) ω, f (g • ω) = g • f ω) :
    (e.pullback f hf).Equivariant (G := G) := by
  intro g ω x
  change e.equiv (f (g • ω)) (g • x) = g • e.equiv (f ω) x
  rw [hcov, he]

end RelativeProbabilityIso

namespace ConcreteInterleaving

/-- Fixed track coding; its choice is independent of the marker and space. -/
def natTimes (T : Type*) [Countable T] [Nonempty T] : ℕ × T ≃ ℕ :=
  Classical.choice (inferInstance : Nonempty ((ℕ × T) ≃ ℕ))

def natPlus (T : Type*) [Countable T] : ℕ ⊕ T ≃ ℕ :=
  Classical.choice (inferInstance : Nonempty ((ℕ ⊕ T) ≃ ℕ))

/-- Interchange just the finite within-coset slot and the coset coordinate. -/
def transposeLast (A B C : Type*) : A × (B × C) ≃ (A × C) × B where
  toFun p := ((p.1, p.2.2), p.2.1)
  invFun p := (p.1.1, (p.2, p.1.2))
  left_inv _ := rfl
  right_inv _ := rfl

variable {G M : Type*} [Group G] (a : MarkerGeometry G)
  [Fintype M] [Nonempty M] [MeasurableSpace M] [MeasurableSingletonClass M]
  [LinearOrder M]
variable (H : Subgroup G) [Finite H] (hHD : H ≤ a.D)

theorem site_card (c : G ⧸ H) :
    Fintype.card (CosetCoordinates.Fiber (QuotientGroup.mk : G → G ⧸ H) c) =
      Nat.card H := by
  rw [← Nat.card_eq_fintype_card, Nat.card_congr (CosetCoordinates.siteFiberEquiv H c)]

/-- Rank the actual individual sites in each finite H-coset, using stream 0. -/
def siteChart (ω : a.goodMarker (K := M)) : G ≃ (G ⧸ H) × Fin (Nat.card H) :=
  CosetCoordinates.rankChart (QuotientGroup.mk : G → G ⧸ H) (site_card H)
    (fun ω : a.goodMarker (K := M) => CosetCoordinates.siteStream a 0 ω.val)
    (fun ω c => CosetCoordinates.siteStream_injective_fiber a hHD 0 ω.property c) ω

@[simp] theorem siteChart_fst (ω : a.goodMarker (K := M)) (x : G) :
    (siteChart a H hHD ω x).1 = QuotientGroup.mk x := rfl

theorem siteChart_covariant (g : G) (ω : a.goodMarker (K := M)) (x : G) :
    siteChart a H hHD
      ⟨MarkerGeometry.markerShift g ω.val, a.goodMarker_shift g ω.property⟩ (g * x) =
        (g • (siteChart a H hHD ω x).1, (siteChart a H hHD ω x).2) := by
  exact CosetCoordinates.rankChart_covariant_at
    (QuotientGroup.mk : G → G ⧸ H) (site_card H)
    (fun ω : a.goodMarker (K := M) => CosetCoordinates.siteStream a 0 ω.val)
    (fun ω c => CosetCoordinates.siteStream_injective_fiber a hHD 0 ω.property c)
    (fun _ _ => rfl) g ω
    ⟨MarkerGeometry.markerShift g ω.val, a.goodMarker_shift g ω.property⟩
    (fun u => CosetCoordinates.siteStream_covariant a 0 g ω.val u) x

theorem measurable_siteChart [Countable G] [MeasurableSpace G]
    [MeasurableSingletonClass G] [MeasurableSpace (G ⧸ H)] :
    Measurable (fun p : a.goodMarker (K := M) × G => siteChart a H hHD p.1 p.2) := by
  unfold siteChart
  apply CosetCoordinates.measurable_rankChart
  intro u
  exact (CosetCoordinates.measurable_siteStream a 0 u).comp measurable_subtype_coe

instance finiteSlot_nonempty : Nonempty (Fin (Nat.card H)) :=
  ⟨⟨0, Nat.card_pos⟩⟩

/-- Infinitely many individual-site tracks are exactly infinitely many
finite-coset tracks. The marker only orders sites within each finite coset. -/
def infiniteSlots (ω : a.goodMarker (K := M)) : (ℕ × G) ≃ ℕ × (G ⧸ H) :=
  (Equiv.prodCongr (Equiv.refl ℕ) (siteChart a H hHD ω)).trans <|
    (transposeLast ℕ (G ⧸ H) (Fin (Nat.card H))).trans <|
      Equiv.prodCongr (natTimes (Fin (Nat.card H))) (Equiv.refl (G ⧸ H))

@[simp] theorem infiniteSlots_apply (ω : a.goodMarker (K := M)) (n : ℕ) (x : G) :
    infiniteSlots a H hHD ω (n, x) =
      (natTimes (Fin (Nat.card H)) (n, (siteChart a H hHD ω x).2),
        (siteChart a H hHD ω x).1) := rfl

theorem infiniteSlots_covariant (g : G) (ω : a.goodMarker (K := M)) (n : ℕ) (x : G) :
    infiniteSlots a H hHD
      ⟨MarkerGeometry.markerShift g ω.val, a.goodMarker_shift g ω.property⟩ (n, g * x) =
        ((infiniteSlots a H hHD ω (n, x)).1,
          g • (infiniteSlots a H hHD ω (n, x)).2) := by
  simp only [infiniteSlots_apply, siteChart_covariant]

theorem measurable_infiniteSlots [Countable G] [MeasurableSpace G]
    [MeasurableSingletonClass G] [MeasurableSpace (G ⧸ H)]
    [MeasurableSingletonClass (G ⧸ H)] :
    Measurable (fun p : a.goodMarker (K := M) × (ℕ × G) =>
      infiniteSlots a H hHD p.1 p.2) := by
  apply measurable_from_prod_countable_left
  intro p
  have hm := (measurable_siteChart (M := M) a H hHD).comp
    ((measurable_id : Measurable (fun ω : a.goodMarker (K := M) => ω)).prodMk
      (measurable_const : Measurable (fun _ : a.goodMarker (K := M) => p.2)))
  have ht := (measurable_of_countable (fun q : (G ⧸ H) × Fin (Nat.card H) =>
    (natTimes (Fin (Nat.card H)) (p.1, q.2), q.1))).comp hm
  exact ht

variable [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
  [MeasurableSpace (G ⧸ H)] [MeasurableSingletonClass (G ⧸ H)]
  {K : Type*} [MeasurableSpace K] (μ : Measure K) [IsProbabilityMeasure μ]

/-- The actual relative finite-coset interleaving with both joint
measurability directions and its conditional iid law. -/
def cosetInfinite : RelativeProbabilityIso (a.goodMarker (K := M))
    (iidLaw ℕ (iidLaw G μ)) (iidLaw ℕ (iidLaw (G ⧸ H) μ)) :=
  (RelativeProbabilityIso.constant
    (ProbabilityIso.curry (fun (_ : ℕ) (_ : G) => μ)).symm).trans <|
    (CosetCoordinates.relativeReindexOfMeasurable μ (infiniteSlots a H hHD)
      (measurable_infiniteSlots a H hHD)).trans <|
      RelativeProbabilityIso.constant
        (ProbabilityIso.curry (fun (_ : ℕ) (_ : G ⧸ H) => μ))

@[simp] theorem cosetInfinite_apply (ω : a.goodMarker (K := M))
    (x : ℕ → G → K) (n : ℕ) (c : G ⧸ H) :
    (cosetInfinite a H hHD μ).equiv ω x n c =
      x ((infiniteSlots a H hHD ω).symm (n, c)).1
        ((infiniteSlots a H hHD ω).symm (n, c)).2 := by
  change (MeasurableEquiv.piCongrLeft (fun _ : ℕ × (G ⧸ H) => K)
    (infiniteSlots a H hHD ω)) (fun q => x q.1 q.2) (n, c) = _
  simpa using MeasurableEquiv.piCongrLeft_apply_apply (infiniteSlots a H hHD ω)
    (β := fun _ => K) (fun q => x q.1 q.2) ((infiniteSlots a H hHD ω).symm (n, c))

theorem cosetInfinite_covariant (g : G) (ω : a.goodMarker (K := M)) (x : ℕ → G → K) :
    (cosetInfinite a H hHD μ).equiv
      ⟨MarkerGeometry.markerShift g ω.val, a.goodMarker_shift g ω.property⟩
      (fun n u => x n (g⁻¹ * u)) =
        fun n c => (cosetInfinite a H hHD μ).equiv ω x n (g⁻¹ • c) := by
  funext n c
  let ω' : a.goodMarker (K := M) :=
    ⟨MarkerGeometry.markerShift g ω.val, a.goodMarker_shift g ω.property⟩
  let z := (infiniteSlots a H hHD ω).symm (n, g⁻¹ • c)
  have hi : (infiniteSlots a H hHD ω').symm (n, c) = (z.1, g * z.2) := by
    apply (infiniteSlots a H hHD ω').injective
    rw [Equiv.apply_symm_apply]
    have hc := infiniteSlots_covariant a H hHD g ω z.1 z.2
    change (n, c) = infiniteSlots a H hHD ω' (z.1, g * z.2)
    rw [hc]
    have hz : infiniteSlots a H hHD ω z = (n, g⁻¹ • c) :=
      (infiniteSlots a H hHD ω).apply_symm_apply _
    rw [hz]
    simp
  simp only [cosetInfinite_apply]
  change x ((infiniteSlots a H hHD ω').symm (n, c)).1
    (g⁻¹ * ((infiniteSlots a H hHD ω').symm (n, c)).2) = x z.1 z.2
  rw [hi]
  simp

/-- Every finite (indeed countable) family of H-coset tracks is absorbed
by actual interleaving in the infinite coset-track representation. -/
def absorbCosetTracks (T : Type*) [Countable T] :
    RelativeProbabilityIso (a.goodMarker (K := M))
      ((iidLaw ℕ (iidLaw G μ)).prod (iidLaw T (iidLaw (G ⧸ H) μ)))
      (iidLaw ℕ (iidLaw G μ)) :=
  ((cosetInfinite a H hHD μ).prod (RelativeProbabilityIso.refl _)).trans <|
    (RelativeProbabilityIso.constant
      (ProbabilityIso.interleave (iidLaw (G ⧸ H) μ) (natPlus T))).trans
        (cosetInfinite a H hHD μ).symm

end ConcreteInterleaving
end BernoulliIso

#print axioms BernoulliIso.ConcreteInterleaving.cosetInfinite
#print axioms BernoulliIso.ConcreteInterleaving.absorbCosetTracks
