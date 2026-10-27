module

public import BernoulliIso.FiniteBaseCertificate
public import Mathlib.Probability.ProductMeasure
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Dynamics.Ergodic.MeasurePreserving

@[expose] public section

noncomputable section
open MeasureTheory

namespace BernoulliCertificate

/-- The usual left shift: the letter at h after acting by g was at g⁻¹h. -/
def shift {G B : Type*} [Group G] (g : G) (x : G → B) : G → B :=
  fun h => x (g⁻¹ * h)

/-- Independent uniform letters at every group site, with the product sigma algebra. -/
def uniformBernoulliLaw (G B : Type*) [Fintype B] [Nonempty B]
    [MeasurableSpace B] : Measure (G → B) :=
  Measure.infinitePi (fun _ : G => Measure.uniformOfFinset (Finset.univ : Finset B))

/-- An actual measurable, probability-preserving, equivariant bijection on
invariant conull subsets of the ordinary uniform Bernoulli shifts A² and A.
The subtype measures are induced from the full product probability measures. -/
def HasUniformSquareConjugacy (G A : Type*) [Group G]
    [Fintype A] [Nonempty A] [MeasurableSpace A] : Prop :=
  ∃ (s : Set (G → A × A)) (t : Set (G → A)),
    MeasurableSet s ∧ MeasurableSet t ∧
    (∀ᵐ x ∂uniformBernoulliLaw G (A × A), x ∈ s) ∧
    (∀ᵐ y ∂uniformBernoulliLaw G A, y ∈ t) ∧
    ∃ (hs : ∀ (g : G) (x : G → A × A), x ∈ s → shift g x ∈ s)
      (_ht : ∀ (g : G) (y : G → A), y ∈ t → shift g y ∈ t)
      (e : s ≃ᵐ t),
      MeasurePreserving e
        ((uniformBernoulliLaw G (A × A)).comap (Subtype.val : s → (G → A × A)))
        ((uniformBernoulliLaw G A).comap (Subtype.val : t → (G → A))) ∧
      ∀ (g : G) (x : s),
        (e ⟨shift g x.val, hs g x.val x.property⟩).val = shift g (e x).val

/-- There is a countable group with two unequal nontrivial finite uniform
Bernoulli bases whose ordinary shifts are measure-preservingly isomorphic.
Singleton measurability gives the full discrete sigma algebra on a finite base.
No algebraic existence or isomorphism hypothesis is assumed. -/
theorem unequal_finite_bernoulli_shifts :
  ∃ (G A : Type) (_ : Group G) (_ : Countable G) (_ : Fintype A)
    (_ : Nonempty A) (_ : MeasurableSpace A) (_ : MeasurableSingletonClass A),
    1 < Fintype.card A ∧ Fintype.card A < Fintype.card (A × A) ∧
      HasUniformSquareConjugacy G A := by
  letI := BernoulliIso.bernoulliAction
    BernoulliIso.FiniteBaseCertificate.G (BernoulliIso.FiniteBaseCertificate.A × BernoulliIso.FiniteBaseCertificate.A)
  letI := BernoulliIso.bernoulliAction
    BernoulliIso.FiniteBaseCertificate.G BernoulliIso.FiniteBaseCertificate.A
  refine ⟨BernoulliIso.FiniteBaseCertificate.G, BernoulliIso.FiniteBaseCertificate.A,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    BernoulliIso.FiniteBaseCertificate.base_nontrivial,
    BernoulliIso.FiniteBaseCertificate.bases_unequal, ?_⟩
  obtain ⟨c⟩ := BernoulliIso.FiniteBaseCertificate.unequal_finite_bernoulli_shifts.2.2
  refine ⟨c.source, c.target, c.measurable_source, c.measurable_target,
    c.conull_source, c.conull_target, c.invariant_source, c.invariant_target,
    c.iso.equiv, c.iso.measurePreserving, ?_⟩
  exact c.equivariant

end BernoulliCertificate

#print axioms BernoulliCertificate.unequal_finite_bernoulli_shifts
