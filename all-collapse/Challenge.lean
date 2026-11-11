module

public import Mathlib.Probability.ProductMeasure
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

@[expose] public section

noncomputable section
open MeasureTheory

namespace AllCollapse

/-- The left shift of `G` on `G → B`: the letter at `h` after acting by `g` was at `g⁻¹ * h`. -/
def shift {G B : Type*} [Group G] (g : G) (x : G → B) : G → B :=
  fun h => x (g⁻¹ * h)

/-- The Bernoulli measure of `G` with base `μ`: independent letters with law `μ` at every
element of `G`, on the product σ-algebra. It is used below only for probability measures `μ`
(Mathlib's `Measure.infinitePi` is the zero measure otherwise). -/
def bernoulli (G : Type*) {B : Type*} [MeasurableSpace B] (μ : Measure B) : Measure (G → B) :=
  Measure.infinitePi (fun _ : G => μ)

/-- The shifts of `G` on `(G → X, μ)` and `(G → Y, ν)` are isomorphic: there is a bijection,
measurable in both directions, between shift-invariant measurable sets of full measure, which
carries `μ` to `ν` and commutes with the shift. The measures on the two subsets are the
restrictions of `μ` and `ν`. -/
def ShiftIsomorphic (G : Type*) [Group G] {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure (G → X)) (ν : Measure (G → Y)) : Prop :=
  ∃ (s : Set (G → X)) (t : Set (G → Y)),
    MeasurableSet s ∧ MeasurableSet t ∧
    (∀ᵐ x ∂μ, x ∈ s) ∧ (∀ᵐ y ∂ν, y ∈ t) ∧
    ∃ (hs : ∀ (g : G) (x : G → X), x ∈ s → shift g x ∈ s)
      (_ht : ∀ (g : G) (y : G → Y), y ∈ t → shift g y ∈ t)
      (e : s ≃ᵐ t),
      MeasurePreserving e
        (μ.comap (Subtype.val : s → (G → X))) (ν.comap (Subtype.val : t → (G → Y))) ∧
      ∀ (g : G) (x : s),
        (e ⟨shift g x.val, hs g x.val x.property⟩).val = shift g (e x).val

/-- **All Bernoulli shifts are isomorphic.** There is a countable group `G` such that the
Bernoulli shifts of `G` with bases `(L, lam)` and `(L', lam')` are isomorphic, for all standard
probability spaces `(L, lam)` and `(L', lam')` whose measures are not point masses. No condition
is put on the entropies of the bases, which may differ and may be infinite. -/
theorem all_bernoulli_shifts_isomorphic :
    ∃ (G : Type) (_ : Group G) (_ : Countable G),
      ∀ (L L' : Type) [MeasurableSpace L] [StandardBorelSpace L]
        [MeasurableSpace L'] [StandardBorelSpace L']
        (lam : Measure L) (lam' : Measure L') [IsProbabilityMeasure lam]
        [IsProbabilityMeasure lam'],
        (∀ a : L, lam ≠ Measure.dirac a) → (∀ a : L', lam' ≠ Measure.dirac a) →
        ShiftIsomorphic G (bernoulli G lam) (bernoulli G lam') := by
  sorry

end AllCollapse
