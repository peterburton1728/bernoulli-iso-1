module

public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
Measure-preserving isomorphisms and genuine conjugacies on invariant conull sets.
The objects record measures and actions, not merely a bijection of underlying sets.
-/

@[expose] public section

open MeasureTheory

namespace BernoulliIso

/-- A measurable isomorphism together with its actual push-forward law. -/
structure ProbabilityIso {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) where
  equiv : X ≃ᵐ Y
  measurePreserving : MeasurePreserving equiv μ ν

namespace ProbabilityIso

variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
  {μ : Measure X} {ν : Measure Y} {ρ : Measure Z}

def refl (μ : Measure X) : ProbabilityIso μ μ :=
  ⟨MeasurableEquiv.refl X, MeasurePreserving.id μ⟩

def symm (e : ProbabilityIso μ ν) : ProbabilityIso ν μ :=
  ⟨e.equiv.symm, e.measurePreserving.symm e.equiv⟩

def trans (e : ProbabilityIso μ ν) (f : ProbabilityIso ν ρ) : ProbabilityIso μ ρ :=
  ⟨e.equiv.trans f.equiv, f.measurePreserving.comp e.measurePreserving⟩

def prod {X' Y' : Type*} [MeasurableSpace X'] [MeasurableSpace Y']
    {μ' : Measure X'} {ν' : Measure Y'} [SFinite μ] [SFinite μ']
    (e : ProbabilityIso μ ν) (f : ProbabilityIso μ' ν') :
    ProbabilityIso (μ.prod μ') (ν.prod ν') :=
  ⟨e.equiv.prodCongr f.equiv, e.measurePreserving.prod f.measurePreserving⟩

end ProbabilityIso

/-- A genuine measure-preserving equivariant isomorphism between invariant
conull measurable subsets. The subtype measures are induced by the original
probability measures via `Measure.comap Subtype.val`. -/
structure ConullConjugacy (G X Y : Type*) [Group G]
    [MeasurableSpace X] [MeasurableSpace Y] [MulAction G X] [MulAction G Y]
    (μ : Measure X) (ν : Measure Y) where
  source : Set X
  target : Set Y
  measurable_source : MeasurableSet source
  measurable_target : MeasurableSet target
  conull_source : ∀ᵐ x ∂μ, x ∈ source
  conull_target : ∀ᵐ y ∂ν, y ∈ target
  invariant_source : ∀ (g : G) (x : X), x ∈ source → g • x ∈ source
  invariant_target : ∀ (g : G) (y : Y), y ∈ target → g • y ∈ target
  iso : ProbabilityIso (μ.comap (Subtype.val : source → X))
    (ν.comap (Subtype.val : target → Y))
  equivariant : ∀ (g : G) (x : source),
    (iso.equiv ⟨g • x.val, invariant_source g x.val x.property⟩).val =
      g • (iso.equiv x).val

/-- A measurable bijection between standard Borel spaces has a measurable
inverse. We use the given forward map, rather than an unrelated classification
of standard Borel spaces. -/
noncomputable def measurableEquivOfBijective {X Y : Type*}
    [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace Y] [MeasurableSpace.CountablySeparated Y]
    (f : X → Y) (hm : Measurable f) (hb : Function.Bijective f) : X ≃ᵐ Y := by
  let e := Equiv.ofBijective f hb
  refine ⟨e, hm, ?_⟩
  have he := hm.measurableEmbedding hb.injective
  intro s hs
  have hset : e.symm ⁻¹' s = f '' s := by
    ext y
    constructor
    · intro hy
      exact ⟨e.symm y, hy, e.apply_symm_apply y⟩
    · rintro ⟨x, hx, rfl⟩
      simpa [e] using hx
  rw [hset]
  exact he.measurableSet_image' hs

@[simp] theorem measurableEquivOfBijective_apply {X Y : Type*}
    [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace Y] [MeasurableSpace.CountablySeparated Y]
    (f : X → Y) (hm : Measurable f) (hb : Function.Bijective f) (x : X) :
    measurableEquivOfBijective f hm hb x = f x := rfl

/-- Good markers times a fiber are exactly the corresponding measurable
subset of the full product. -/
def markerSubtypeEquiv {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (s : Set Ω) : (s × X) ≃ᵐ {p : Ω × X // p.1 ∈ s} where
  toFun p := ⟨(p.1.val, p.2), p.1.property⟩
  invFun p := (⟨p.val.1, p.property⟩, p.val.2)
  left_inv _ := rfl
  right_inv _ := rfl
  measurable_toFun :=
    ((measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd).subtype_mk
  measurable_invFun :=
    ((measurable_fst.comp measurable_subtype_coe).subtype_mk).prodMk
      (measurable_snd.comp measurable_subtype_coe)

/-- Restriction to a conull measurable subset loses no mass. -/
theorem measurePreserving_conullSubtype {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {s : Set Ω} (hs : MeasurableSet s) (hfull : ∀ᵐ ω ∂μ, ω ∈ s) :
    MeasurePreserving (Subtype.val : s → Ω) (μ.comap Subtype.val) μ := by
  simpa only [Measure.restrict_eq_self_of_ae_mem hfull] using
    (measurePreserving_subtype_coe (μa := μ) hs)

/-- The chart from good markers and fibers to the conull full-product subset
preserves precisely the measures induced from the original product. -/
def markerSubtypeIso {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) (ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {s : Set Ω} (hs : MeasurableSet s) (hfull : ∀ᵐ ω ∂μ, ω ∈ s) :
    ProbabilityIso ((μ.comap (Subtype.val : s → Ω)).prod ν)
      ((μ.prod ν).comap (Subtype.val : {p : Ω × X // p.1 ∈ s} → Ω × X)) where
  equiv := markerSubtypeEquiv s
  measurePreserving := by
    let : IsProbabilityMeasure (μ.comap (Subtype.val : s → Ω)) :=
      (MeasurableEmbedding.subtype_coe hs).isProbabilityMeasure_comap
        (by simpa using hfull)
    have hprod : ∀ᵐ p ∂μ.prod ν, p.1 ∈ s :=
      (Measure.ae_prod_iff_ae_ae (hs.preimage measurable_fst)).2
        (hfull.mono fun _ h => Filter.Eventually.of_forall fun _ => h)
    have hcoe := measurePreserving_conullSubtype (μ.prod ν) (s := {p : Ω × X | p.1 ∈ s})
      (hs.preimage measurable_fst) hprod
    refine ⟨(markerSubtypeEquiv s).measurable, ?_⟩
    apply (MeasurableEmbedding.subtype_coe
      (show MeasurableSet {p : Ω × X | p.1 ∈ s} from hs.preimage measurable_fst)).map_injective
    rw [Measure.map_map measurable_subtype_coe (markerSubtypeEquiv s).measurable]
    exact (((measurePreserving_conullSubtype μ hs hfull).prod
      (MeasurePreserving.id ν)).map_eq).trans hcoe.map_eq.symm

/-- A relative isomorphism over an invariant conull marker set induces a
genuine conjugacy of the full probability spaces modulo null sets. -/
noncomputable def conullConjugacyOfRelativeIso {G Ω X Y : Type*} [Group G]
    [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Y]
    [MulAction G Ω] [MulAction G X] [MulAction G Y]
    (μ : Measure Ω) (ν : Measure X) (ρ : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]
    {s : Set Ω} (hs : MeasurableSet s) (hfull : ∀ᵐ ω ∂μ, ω ∈ s)
    (hinv : ∀ (g : G) (ω : Ω), ω ∈ s → g • ω ∈ s)
    (e : ProbabilityIso ((μ.comap (Subtype.val : s → Ω)).prod ν)
      ((μ.comap (Subtype.val : s → Ω)).prod ρ))
    (hmarker : ∀ p : s × X, (e.equiv p).1 = p.1)
    (hcov : ∀ (g : G) (ω : s) (x : X),
      (e.equiv (⟨g • ω.val, hinv g ω.val ω.property⟩, g • x)).2 =
        g • (e.equiv (ω, x)).2) :
    ConullConjugacy G (Ω × X) (Ω × Y) (μ.prod ν) (μ.prod ρ) where
  source := {p | p.1 ∈ s}
  target := {p | p.1 ∈ s}
  measurable_source := hs.preimage measurable_fst
  measurable_target := hs.preimage measurable_fst
  conull_source := (Measure.ae_prod_iff_ae_ae (hs.preimage measurable_fst)).2
    (hfull.mono fun _ h => Filter.Eventually.of_forall fun _ => h)
  conull_target := (Measure.ae_prod_iff_ae_ae (hs.preimage measurable_fst)).2
    (hfull.mono fun _ h => Filter.Eventually.of_forall fun _ => h)
  invariant_source := fun g p hp => hinv g p.1 hp
  invariant_target := fun g p hp => hinv g p.1 hp
  iso := (markerSubtypeIso μ ν hs hfull).symm.trans
    (e.trans (markerSubtypeIso μ ρ hs hfull))
  equivariant := by
    intro g p
    change (((e.equiv (⟨g • p.val.1, _⟩, g • p.val.2)).1).val,
      (e.equiv (⟨g • p.val.1, _⟩, g • p.val.2)).2) =
      (g • ((e.equiv (⟨p.val.1, p.property⟩, p.val.2)).1).val,
        g • (e.equiv (⟨p.val.1, p.property⟩, p.val.2)).2)
    apply Prod.ext
    · rw [hmarker, hmarker]
    · exact hcov g ⟨p.val.1, p.property⟩ p.val.2

/-- Every almost-sure property for a probability-preserving countable-group
action holds on a measurable invariant conull subset. The property itself
need not have been proved measurable. -/
theorem exists_invariant_conull_subset {G Ω : Type*} [Group G] [Countable G]
    [MeasurableSpace Ω] [MulAction G Ω] (μ : Measure Ω)
    (hpres : ∀ g : G, MeasurePreserving (fun ω : Ω => g • ω) μ μ)
    (P : Ω → Prop) (hP : ∀ᵐ ω ∂μ, P ω) :
    ∃ s : Set Ω, MeasurableSet s ∧ (∀ᵐ ω ∂μ, ω ∈ s) ∧
      (∀ (g : G) (ω : Ω), ω ∈ s → g • ω ∈ s) ∧
      (∀ ω ∈ s, P ω) := by
  obtain ⟨bad, hbad, hbadm, hbadzero⟩ :=
    exists_measurable_superset_of_null (ae_iff.mp hP)
  let s : Set Ω := ⋂ g : G, (fun ω : Ω => g • ω) ⁻¹' badᶜ
  have hgood : ∀ᵐ ω ∂μ, ω ∈ badᶜ := by
    apply ae_iff.mpr
    simpa using hbadzero
  refine ⟨s, ?_, ?_, ?_, ?_⟩
  · exact MeasurableSet.iInter fun g => hbadm.compl.preimage (hpres g).measurable
  · have ha : ∀ᵐ ω ∂μ, ∀ g : G, g • ω ∈ badᶜ :=
      ae_all_iff.mpr fun g => (hpres g).quasiMeasurePreserving.ae hgood
    simpa [s] using ha
  · intro g ω hω
    apply Set.mem_iInter.mpr
    intro h
    have hh := Set.mem_iInter.mp hω (h * g)
    simpa only [Set.mem_preimage, mul_smul] using hh
  · intro ω hω
    have hz := Set.mem_iInter.mp hω (1 : G)
    have hn : ω ∉ bad := by simpa using hz
    by_contra hp
    exact hn (hbad hp)

end BernoulliIso

#print axioms BernoulliIso.measurableEquivOfBijective
#print axioms BernoulliIso.conullConjugacyOfRelativeIso
#print axioms BernoulliIso.exists_invariant_conull_subset
