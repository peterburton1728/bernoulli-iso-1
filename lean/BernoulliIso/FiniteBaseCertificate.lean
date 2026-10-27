module

public import BernoulliIso.ConcreteFiniteSquare
public import CertifiedInput

@[expose] public section

/-! The closed finite-base certificate. The algebraic witness in this file
is imported from the pinned upstream proofs, rather than assumed. -/

noncomputable section
open MeasureTheory
open scoped Classical

namespace BernoulliIso.FiniteBaseCertificate

/- Match the classical finite-function enumeration in the generic theorem. -/
instance (priority := 3000) columnDecidableEq : DecidableEq Upstream.V :=
  Classical.decEq _

instance scalarTopology : TopologicalSpace Upstream.K := ⊥
instance scalarDiscrete : DiscreteTopology Upstream.K := discreteTopology_bot _
instance scalarMeasurable : MeasurableSpace Upstream.K := ⊤
instance scalarMeasurableSingleton : MeasurableSingletonClass Upstream.K :=
  ⟨fun _ => trivial⟩
instance scalarBorel : BorelSpace Upstream.K :=
  ⟨borel_eq_top_of_discrete.symm⟩
instance scalarTopologicalRing : IsTopologicalRing Upstream.K := inferInstance

instance columnMeasurable : MeasurableSpace Upstream.V := ⊤
instance columnMeasurableSingleton : MeasurableSingletonClass Upstream.V :=
  ⟨fun _ => trivial⟩

/-- The actual countable ambient group built from the upstream early group. -/
abbrev G := Ambient.G Upstream.N

/-- One marker letter and the original finite family of data letters. -/
abbrev A := Upstream.algebraicInput.finiteBase

theorem group_countable : Countable G := inferInstance

theorem base_nontrivial : 1 < Fintype.card A :=
  Upstream.algebraicInput.finiteBase_card_gt_one

theorem bases_unequal : Fintype.card A < Fintype.card (A × A) :=
  Upstream.algebraicInput.finiteBase_square_card_gt

/-- A measure-preserving equivariant isomorphism on invariant conull sets
between the uniform Bernoulli shifts with bases A² and A. -/
def conjugacy :
    letI := bernoulliAction G (A × A)
    letI := bernoulliAction G A
    ConullConjugacy G (G → A × A) (G → A)
      (bernoulliLaw G (A × A)) (bernoulliLaw G A) :=
  Upstream.algebraicInput.finiteBaseSquareConjugacy

/-- The two finite uniform bases have different cardinalities, and their
Bernoulli actions over the same concrete countable group are isomorphic. -/
theorem unequal_finite_bernoulli_shifts :
    1 < Fintype.card A ∧ Fintype.card A < Fintype.card (A × A) ∧
      (letI := bernoulliAction G (A × A)
       letI := bernoulliAction G A
       Nonempty (ConullConjugacy G (G → A × A) (G → A)
         (bernoulliLaw G (A × A)) (bernoulliLaw G A))) :=
  ⟨base_nontrivial, bases_unequal, ⟨conjugacy⟩⟩

end BernoulliIso.FiniteBaseCertificate

#print axioms BernoulliIso.FiniteBaseCertificate.conjugacy
#print axioms BernoulliIso.FiniteBaseCertificate.unequal_finite_bernoulli_shifts
