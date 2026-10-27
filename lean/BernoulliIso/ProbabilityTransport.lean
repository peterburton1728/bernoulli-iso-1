module

public import BernoulliIso.Conjugacy

/-! Transport conull conjugacies through actual global probability
isomorphisms. The restricted measures are always induced from the original
measures by subtype inclusion. -/

@[expose] public section
noncomputable section
open MeasureTheory

namespace BernoulliIso
namespace ProbabilityIso

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {μ : Measure X} {ν : Measure Y}

/-- The given measurable equivalence restricted to a target subset. -/
def restrictionEquiv (e : ProbabilityIso μ ν) (t : Set Y) :
    (e.equiv ⁻¹' t) ≃ᵐ t where
  toEquiv := e.equiv.toEquiv.subtypeEquivOfSubtype
  measurable_toFun := by
    exact (e.equiv.measurable.comp
      (measurable_subtype_coe : Measurable (Subtype.val : (e.equiv ⁻¹' t) → X))).subtype_mk
  measurable_invFun := by
    exact (e.equiv.symm.measurable.comp
      (measurable_subtype_coe : Measurable (Subtype.val : t → Y))).subtype_mk

/-- A global probability isomorphism restricts to the preimage of any
specified measurable conull target domain. -/
def conullRestrict (e : ProbabilityIso μ ν) (t : Set Y)
    (ht : MeasurableSet t) (hfull : ∀ᵐ y ∂ν, y ∈ t) :
    ProbabilityIso (μ.comap (Subtype.val : (e.equiv ⁻¹' t) → X))
      (ν.comap (Subtype.val : t → Y)) where
  equiv := e.restrictionEquiv t
  measurePreserving := by
    refine ⟨(e.restrictionEquiv t).measurable, ?_⟩
    apply (MeasurableEmbedding.subtype_coe ht).map_injective
    rw [Measure.map_map measurable_subtype_coe (e.restrictionEquiv t).measurable]
    exact (e.measurePreserving.comp
      (measurePreserving_conullSubtype μ (ht.preimage e.equiv.measurable)
        (e.measurePreserving.quasiMeasurePreserving.ae hfull))).map_eq.trans
          (measurePreserving_conullSubtype ν ht hfull).map_eq.symm

@[simp] theorem conullRestrict_val (e : ProbabilityIso μ ν) (t : Set Y)
    (ht : MeasurableSet t) (hfull : ∀ᵐ y ∂ν, y ∈ t) (x : e.equiv ⁻¹' t) :
    ((e.conullRestrict t ht hfull).equiv x).val = e.equiv x.val := rfl

@[simp] theorem conullRestrict_symm_val (e : ProbabilityIso μ ν) (t : Set Y)
    (ht : MeasurableSet t) (hfull : ∀ᵐ y ∂ν, y ∈ t) (y : t) :
    ((e.conullRestrict t ht hfull).equiv.symm y).val = e.equiv.symm y.val := rfl

end ProbabilityIso

namespace ConullConjugacy

variable {G X Y X' Y' : Type*} [Group G]
  [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace X'] [MeasurableSpace Y']
  [MulAction G X] [MulAction G Y] [MulAction G X'] [MulAction G Y']
  {μ : Measure X} {ν : Measure Y} {μ' : Measure X'} {ν' : Measure Y'}

/-- Pull back a conull conjugacy through global equivariant probability
isomorphisms. This does not require an unproved composition principle for
arbitrary partially defined conjugacies. -/
def transport (c : ConullConjugacy G X Y μ ν)
    (e : ProbabilityIso μ' μ) (f : ProbabilityIso ν' ν)
    (he : ∀ (g : G) (x : X'), e.equiv (g • x) = g • e.equiv x)
    (hf : ∀ (g : G) (y : Y'), f.equiv (g • y) = g • f.equiv y) :
    ConullConjugacy G X' Y' μ' ν' where
  source := e.equiv ⁻¹' c.source
  target := f.equiv ⁻¹' c.target
  measurable_source := c.measurable_source.preimage e.equiv.measurable
  measurable_target := c.measurable_target.preimage f.equiv.measurable
  conull_source := e.measurePreserving.quasiMeasurePreserving.ae c.conull_source
  conull_target := f.measurePreserving.quasiMeasurePreserving.ae c.conull_target
  invariant_source g x hx := by
    change e.equiv (g • x) ∈ c.source
    rw [he]
    exact c.invariant_source g (e.equiv x) hx
  invariant_target g y hy := by
    change f.equiv (g • y) ∈ c.target
    rw [hf]
    exact c.invariant_target g (f.equiv y) hy
  iso := (e.conullRestrict c.source c.measurable_source c.conull_source).trans
    (c.iso.trans (f.conullRestrict c.target c.measurable_target c.conull_target).symm)
  equivariant := by
    intro g x
    apply f.equiv.injective
    change f.equiv (f.equiv.symm
      (c.iso.equiv ((e.conullRestrict c.source c.measurable_source c.conull_source).equiv
        ⟨g • x.val, _⟩)).val) =
      f.equiv (g • f.equiv.symm
        (c.iso.equiv ((e.conullRestrict c.source c.measurable_source c.conull_source).equiv x)).val)
    rw [f.equiv.apply_symm_apply, hf, f.equiv.apply_symm_apply]
    have harg (hx : e.equiv (g • x.val) ∈ c.source) :
      (e.conullRestrict c.source c.measurable_source c.conull_source).equiv
        ⟨g • x.val, hx⟩ =
      (⟨g • e.equiv x.val, c.invariant_source g (e.equiv x.val) x.property⟩ : c.source) := by
      apply Subtype.ext
      exact he g x.val
    rw [harg]
    exact c.equivariant g
      ((e.conullRestrict c.source c.measurable_source c.conull_source).equiv x)

end ConullConjugacy
end BernoulliIso

#print axioms BernoulliIso.ProbabilityIso.conullRestrict
#print axioms BernoulliIso.ConullConjugacy.transport
