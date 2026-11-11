module

public import Collapse.Kernel
public import BernoulliIso.Conjugacy
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# Systems

A system of `G` is a standard probability space with a
measure-preserving action. Isomorphism is the `ConullConjugacy` of the registered package: an
equivariant measure-preserving bijection, measurable in both directions, between invariant
measurable sets of full measure.
-/

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory

namespace Collapse

open BernoulliIso

section Aux

variable {G X Y : Type} [Group G] [MeasurableSpace X] [MeasurableSpace Y]

/-- A measure-preserving map sending one conull measurable set into another restricts to a
measure-preserving map between the subtype measures. -/
theorem mp_restrict {μ : Measure X} {ν : Measure Y}
    {s : Set X} {t : Set Y} (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hsc : ∀ᵐ x ∂μ, x ∈ s) (htc : ∀ᵐ y ∂ν, y ∈ t) {f : X → Y} (hf : MeasurePreserving f μ ν)
    (hmaps : ∀ x ∈ s, f x ∈ t) :
    MeasurePreserving (fun x : s => (⟨f x.1, hmaps x.1 x.2⟩ : t))
      (μ.comap Subtype.val) (ν.comap Subtype.val) := by
  have hm : Measurable (fun x : s => (⟨f x.1, hmaps x.1 x.2⟩ : t)) :=
    (hf.measurable.comp measurable_subtype_coe).subtype_mk
  refine ⟨hm, ?_⟩
  apply (MeasurableEmbedding.subtype_coe ht).map_injective
  rw [Measure.map_map measurable_subtype_coe hm, (measurePreserving_conullSubtype ν ht htc).map_eq]
  have : (Subtype.val ∘ fun x : s => (⟨f x.1, hmaps x.1 x.2⟩ : t)) = f ∘ Subtype.val := rfl
  rw [this, ← Measure.map_map hf.measurable measurable_subtype_coe,
    (measurePreserving_conullSubtype μ hs hsc).map_eq, hf.map_eq]

variable [MulAction G X] [MulAction G Y] {μ : Measure X} {ν : Measure Y}

/-- A conjugacy from a global measure-preserving map, bijective between conull sets. -/
def conjMk [StandardBorelSpace X] [StandardBorelSpace Y] (s : Set X) (t : Set Y)
    (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hsc : ∀ᵐ x ∂μ, x ∈ s) (htc : ∀ᵐ y ∂ν, y ∈ t)
    (hsi : ∀ (g : G) (x : X), x ∈ s → g • x ∈ s) (hti : ∀ (g : G) (y : Y), y ∈ t → g • y ∈ t)
    (f : X → Y) (hf : MeasurePreserving f μ ν) (hb : Set.BijOn f s t)
    (he : ∀ (g : G) (x : X), x ∈ s → f (g • x) = g • f x) : ConullConjugacy G X Y μ ν :=
  haveI := hs.standardBorel
  haveI := ht.standardBorel
  { source := s, target := t, measurable_source := hs, measurable_target := ht
    conull_source := hsc, conull_target := htc, invariant_source := hsi, invariant_target := hti
    iso := ⟨measurableEquivOfBijective (fun x : s => (⟨f x.1, hb.mapsTo x.2⟩ : t))
        (hf.measurable.comp measurable_subtype_coe).subtype_mk
        ⟨fun a b hab => Subtype.ext (hb.injOn a.2 b.2 (congrArg Subtype.val hab)),
         fun y => by
          obtain ⟨x, hx, hxy⟩ := hb.surjOn y.2
          exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩⟩,
        mp_restrict hs ht hsc htc hf (fun x hx => hb.mapsTo hx)⟩
    equivariant := fun g x => he g x.1 x.2 }

/-- The inverse conjugacy. -/
def conjSymm (c : ConullConjugacy G X Y μ ν) : ConullConjugacy G Y X ν μ where
  source := c.target
  target := c.source
  measurable_source := c.measurable_target
  measurable_target := c.measurable_source
  conull_source := c.conull_target
  conull_target := c.conull_source
  invariant_source := c.invariant_target
  invariant_target := c.invariant_source
  iso := c.iso.symm
  equivariant := by
    intro g y
    obtain ⟨x, rfl⟩ := c.iso.equiv.surjective y
    have h1 : (⟨g • (c.iso.equiv x).val, c.invariant_target g _ (c.iso.equiv x).property⟩ :
        c.target) = c.iso.equiv ⟨g • x.val, c.invariant_source g x.val x.property⟩ :=
      Subtype.ext (c.equivariant g x).symm
    change ((c.iso.equiv.symm _ : c.source) : X) =
      g • ((c.iso.equiv.symm (c.iso.equiv x) : c.source) : X)
    rw [h1, MeasurableEquiv.symm_apply_apply, MeasurableEquiv.symm_apply_apply]

open Classical in
/-- The global extension of a conjugacy. -/
def conjExt [Nonempty Y] (c : ConullConjugacy G X Y μ ν) (x : X) : Y :=
  if h : x ∈ c.source then (c.iso.equiv ⟨x, h⟩).val else Classical.arbitrary Y

variable [Nonempty X] [Nonempty Y] (c : ConullConjugacy G X Y μ ν)

theorem conjExt_of_mem {x : X} (h : x ∈ c.source) : conjExt c x = (c.iso.equiv ⟨x, h⟩).val := by
  simp [conjExt, h]

theorem conjExt_mem {x : X} (h : x ∈ c.source) : conjExt c x ∈ c.target := by
  rw [conjExt_of_mem c h]; exact (c.iso.equiv ⟨x, h⟩).2

open Classical in
theorem measurable_conjExt : Measurable (conjExt c) :=
  Measurable.dite (measurable_subtype_coe.comp c.iso.equiv.measurable) measurable_const
    c.measurable_source

theorem measurePreserving_conjExt : MeasurePreserving (conjExt c) μ ν := by
  refine ⟨measurable_conjExt c, ?_⟩
  have h1 : conjExt c ∘ Subtype.val = Subtype.val ∘ c.iso.equiv :=
    funext fun x => conjExt_of_mem c x.2
  have hS := (measurePreserving_conullSubtype μ c.measurable_source c.conull_source).map_eq
  have hT := (measurePreserving_conullSubtype ν c.measurable_target c.conull_target).map_eq
  calc Measure.map (conjExt c) μ
      = Measure.map (conjExt c) (Measure.map Subtype.val (μ.comap Subtype.val)) :=
        congrArg _ hS.symm
    _ = Measure.map (Subtype.val ∘ c.iso.equiv) (μ.comap Subtype.val) := by
        rw [Measure.map_map (measurable_conjExt c) measurable_subtype_coe, h1]
    _ = ν := by
        rw [← Measure.map_map measurable_subtype_coe c.iso.equiv.measurable,
          c.iso.measurePreserving.map_eq, hT]

theorem conjExt_smul (g : G) {x : X} (h : x ∈ c.source) :
    conjExt c (g • x) = g • conjExt c x := by
  rw [conjExt_of_mem c (c.invariant_source g x h), conjExt_of_mem c h]
  exact c.equivariant g ⟨x, h⟩

theorem conjExt_symm_conjExt {x : X} (h : x ∈ c.source) :
    conjExt (conjSymm c) (conjExt c x) = x := by
  have h' : conjExt c x ∈ c.target := conjExt_mem c h
  rw [conjExt_of_mem (conjSymm c) h']
  change ((c.iso.equiv.symm ⟨conjExt c x, h'⟩ : c.source) : X) = x
  have : (⟨conjExt c x, h'⟩ : c.target) = c.iso.equiv ⟨x, h⟩ := Subtype.ext (conjExt_of_mem c h)
  rw [this, MeasurableEquiv.symm_apply_apply]

theorem conjExt_conjExt_symm {y : Y} (h : y ∈ c.target) :
    conjExt c (conjExt (conjSymm c) y) = y := by
  have h' : conjExt (conjSymm c) y ∈ c.source := conjExt_mem (conjSymm c) h
  rw [conjExt_of_mem c h']
  have : (⟨conjExt (conjSymm c) y, h'⟩ : c.source) = c.iso.equiv.symm ⟨y, h⟩ :=
    Subtype.ext (conjExt_of_mem (conjSymm c) h)
  rw [this, MeasurableEquiv.apply_symm_apply]

theorem bijOn_conjExt : Set.BijOn (conjExt c) c.source c.target :=
  ⟨fun _ h => conjExt_mem c h,
   fun x hx x' hx' hxx => by
    rw [← conjExt_symm_conjExt c hx, hxx, conjExt_symm_conjExt c hx'],
   fun y hy => ⟨conjExt (conjSymm c) y, conjExt_mem (conjSymm c) hy, conjExt_conjExt_symm c hy⟩⟩

end Aux

/-- A system of the group `G`. -/
structure PSystem (G : Type) [Group G] where
  X : Type
  [mX : MeasurableSpace X]
  [sb : StandardBorelSpace X]
  [act : MulAction G X]
  μ : Measure X
  [prob : IsProbabilityMeasure μ]
  preserving : ∀ g : G, MeasurePreserving (fun x : X => g • x) μ μ

attribute [instance] PSystem.mX PSystem.sb PSystem.act PSystem.prob

namespace PSystem

variable {G : Type} [Group G]

/-- Isomorphism of systems. -/
def Iso (S T : PSystem G) : Prop :=
  Nonempty (BernoulliIso.ConullConjugacy G S.X T.X S.μ T.μ)

/-- A global equivariant measure-preserving bijection gives an isomorphism. -/
theorem iso_of_bijective {S T : PSystem G} (f : S.X → T.X) (hf : MeasurePreserving f S.μ T.μ)
    (hb : Function.Bijective f) (he : ∀ (g : G) (x : S.X), f (g • x) = g • f x) : S.Iso T :=
  ⟨conjMk Set.univ Set.univ MeasurableSet.univ MeasurableSet.univ
    (ae_of_all _ fun _ => trivial) (ae_of_all _ fun _ => trivial)
    (fun _ _ _ => trivial) (fun _ _ _ => trivial) f hf (Set.bijOn_univ.2 hb)
    (fun g x _ => he g x)⟩

theorem Iso.refl (S : PSystem G) : S.Iso S :=
  iso_of_bijective id (MeasurePreserving.id _) Function.bijective_id (fun _ _ => rfl)

theorem Iso.symm {S T : PSystem G} (h : S.Iso T) : T.Iso S :=
  h.elim fun c => ⟨conjSymm c⟩

theorem Iso.trans {S T R : PSystem G} (h : S.Iso T) (h' : T.Iso R) : S.Iso R := by
  obtain ⟨c₁⟩ := h
  obtain ⟨c₂⟩ := h'
  have := nonempty_of_isProbabilityMeasure S.μ
  have := nonempty_of_isProbabilityMeasure T.μ
  have := nonempty_of_isProbabilityMeasure R.μ
  have m₁ := measurePreserving_conjExt c₁
  have m₂ := measurePreserving_conjExt c₂
  have m₂' := measurePreserving_conjExt (conjSymm c₂)
  refine ⟨conjMk (c₁.source ∩ conjExt c₁ ⁻¹' c₂.source)
    (c₂.target ∩ conjExt (conjSymm c₂) ⁻¹' c₁.target)
    (c₁.measurable_source.inter (c₂.measurable_source.preimage m₁.measurable))
    (c₂.measurable_target.inter (c₁.measurable_target.preimage m₂'.measurable))
    (c₁.conull_source.and (m₁.quasiMeasurePreserving.ae c₂.conull_source))
    (c₂.conull_target.and (m₂'.quasiMeasurePreserving.ae c₁.conull_target))
    (fun g x hx => ⟨c₁.invariant_source g x hx.1, by
      rw [Set.mem_preimage, conjExt_smul c₁ g hx.1]; exact c₂.invariant_source g _ hx.2⟩)
    (fun g y hy => ⟨c₂.invariant_target g y hy.1, by
      rw [Set.mem_preimage, conjExt_smul (conjSymm c₂) g hy.1]
      exact c₁.invariant_target g _ hy.2⟩)
    (conjExt c₂ ∘ conjExt c₁) (m₂.comp m₁) ⟨?_, ?_, ?_⟩ ?_⟩
  · intro x hx
    refine ⟨conjExt_mem c₂ hx.2, ?_⟩
    rw [Set.mem_preimage, Function.comp_apply, conjExt_symm_conjExt c₂ hx.2]
    exact conjExt_mem c₁ hx.1
  · intro x hx x' hx' hxx
    have := congrArg (conjExt (conjSymm c₂)) hxx
    simp only [Function.comp_apply, conjExt_symm_conjExt c₂ hx.2,
      conjExt_symm_conjExt c₂ hx'.2] at this
    rw [← conjExt_symm_conjExt c₁ hx.1, this, conjExt_symm_conjExt c₁ hx'.1]
  · intro z hz
    refine ⟨conjExt (conjSymm c₁) (conjExt (conjSymm c₂) z),
      ⟨conjExt_mem (conjSymm c₁) hz.2, ?_⟩, ?_⟩
    · rw [Set.mem_preimage, conjExt_conjExt_symm c₁ hz.2]
      exact conjExt_mem (conjSymm c₂) hz.1
    · rw [Function.comp_apply, conjExt_conjExt_symm c₁ hz.2, conjExt_conjExt_symm c₂ hz.1]
  · intro g x hx
    rw [Function.comp_apply, Function.comp_apply, conjExt_smul c₁ g hx.1,
      conjExt_smul c₂ g hx.2]

/-- The product of two systems, with the diagonal action. -/
def prod (S T : PSystem G) : PSystem G where
  X := S.X × T.X
  μ := S.μ.prod T.μ
  preserving := fun g => (S.preserving g).prod (T.preserving g)

theorem Iso.prod_congr {S S' T T' : PSystem G} (h : S.Iso S') (h' : T.Iso T') :
    (S.prod T).Iso (S'.prod T') := by
  obtain ⟨c⟩ := h
  obtain ⟨c'⟩ := h'
  have := nonempty_of_isProbabilityMeasure S.μ
  have := nonempty_of_isProbabilityMeasure T.μ
  have := nonempty_of_isProbabilityMeasure S'.μ
  have := nonempty_of_isProbabilityMeasure T'.μ
  have hae : ∀ {A B : PSystem G} {s : Set A.X} {t : Set B.X}, (∀ᵐ x ∂A.μ, x ∈ s) →
      (∀ᵐ y ∂B.μ, y ∈ t) → ∀ᵐ p ∂(A.μ.prod B.μ), p ∈ s ×ˢ t := fun hs ht =>
    (measurePreserving_fst.quasiMeasurePreserving.ae hs).and
      (measurePreserving_snd.quasiMeasurePreserving.ae ht)
  exact ⟨conjMk (c.source ×ˢ c'.source) (c.target ×ˢ c'.target)
    (c.measurable_source.prod c'.measurable_source)
    (c.measurable_target.prod c'.measurable_target)
    (hae c.conull_source c'.conull_source) (hae c.conull_target c'.conull_target)
    (fun g x hx => ⟨c.invariant_source g _ hx.1, c'.invariant_source g _ hx.2⟩)
    (fun g y hy => ⟨c.invariant_target g _ hy.1, c'.invariant_target g _ hy.2⟩)
    (Prod.map (conjExt c) (conjExt c'))
    ((measurePreserving_conjExt c).prod (measurePreserving_conjExt c'))
    ((bijOn_conjExt c).prodMap (bijOn_conjExt c'))
    (fun g x hx => Prod.ext (conjExt_smul c g hx.1) (conjExt_smul c' g hx.2))⟩

theorem prod_comm (S T : PSystem G) : (S.prod T).Iso (T.prod S) :=
  iso_of_bijective Prod.swap (Measure.measurePreserving_swap) Prod.swap_bijective
    (fun _ _ => rfl)

theorem prod_assoc (S T R : PSystem G) : ((S.prod T).prod R).Iso (S.prod (T.prod R)) :=
  iso_of_bijective MeasurableEquiv.prodAssoc
    ⟨MeasurableEquiv.prodAssoc.measurable, Measure.prodAssoc_prod⟩
    MeasurableEquiv.prodAssoc.bijective (fun _ _ => rfl)

/-- The restriction of a system to an invariant measurable set of full measure. -/
def restrict (S : PSystem G) (s : Set S.X) (hs : MeasurableSet s)
    (hinv : ∀ (g : G) (x : S.X), x ∈ s → g • x ∈ s) (hfull : S.μ sᶜ = 0) : PSystem G where
  X := s
  sb := hs.standardBorel
  act :=
    { smul := fun g x => ⟨g • x.1, hinv g x.1 x.2⟩
      one_smul := fun x => Subtype.ext (one_smul G x.1)
      mul_smul := fun g h x => Subtype.ext (mul_smul g h x.1) }
  μ := S.μ.comap Subtype.val
  prob := (MeasurableEmbedding.subtype_coe hs).isProbabilityMeasure_comap
    (by simpa using (ae_iff.2 hfull : ∀ᵐ x ∂S.μ, x ∈ s))
  preserving := fun g => mp_restrict hs hs (ae_iff.2 hfull) (ae_iff.2 hfull) (S.preserving g)
    (hinv g)

theorem restrict_iso (S : PSystem G) (s : Set S.X) (hs : MeasurableSet s)
    (hinv : ∀ (g : G) (x : S.X), x ∈ s → g • x ∈ s) (hfull : S.μ sᶜ = 0) :
    (S.restrict s hs hinv hfull).Iso S :=
  ⟨conjMk (X := (S.restrict s hs hinv hfull).X) Set.univ s MeasurableSet.univ hs
    (ae_of_all _ fun _ => trivial) (ae_iff.2 hfull) (fun _ _ _ => trivial) hinv
    Subtype.val (measurePreserving_conullSubtype S.μ hs (ae_iff.2 hfull))
    ⟨fun x _ => x.2, Subtype.val_injective.injOn, fun y hy => ⟨⟨y, hy⟩, trivial, rfl⟩⟩
    (fun _ _ _ => rfl)⟩

/-- The system is free: no element other than `1` has a fixed point. -/
class IsFree (S : PSystem G) : Prop where
  free : ∀ (g : G) (x : S.X), g • x = x → g = 1

/-- The system is essentially free: the fixed points of every `g ≠ 1` form a null set. -/
def EssFree (S : PSystem G) : Prop :=
  ∀ g : G, g ≠ 1 → S.μ {x : S.X | g • x = x} = 0

instance borelFree [Countable G] (S : PSystem G) [S.IsFree] : BorelFree G S.X :=
  ⟨inferInstance, fun g => (S.preserving g).measurable, fun g x hx => IsFree.free (S := S) g x hx⟩

/-- The set of points with trivial stabilizer. -/
def freeSet (S : PSystem G) : Set S.X := {x | ∀ g : G, g • x = x → g = 1}

theorem measurableSet_freeSet [Countable G] (S : PSystem G) : MeasurableSet S.freeSet := by
  rw [freeSet, Set.ofPred_forall]
  refine MeasurableSet.iInter fun g => ?_
  by_cases hg : g = 1
  · simp [hg]
  · simp only [hg, imp_false]
    exact (measurableSet_eq_fun (S.preserving g).measurable measurable_id).compl

theorem freeSet_invariant (S : PSystem G) (g : G) (x : S.X) (hx : x ∈ S.freeSet) :
    g • x ∈ S.freeSet := by
  intro h hh
  have := hx (g⁻¹ * h * g) (by rw [mul_smul, mul_smul, hh, inv_smul_smul])
  calc h = g * (g⁻¹ * h * g) * g⁻¹ := by group
    _ = 1 := by rw [this]; group

theorem measure_freeSet_compl [Countable G] (S : PSystem G) (h : S.EssFree) :
    S.μ S.freeSetᶜ = 0 := by
  have hsub : S.freeSetᶜ ⊆ ⋃ g : G, ⋃ (_ : g ≠ 1), {x | g • x = x} := by
    intro x hx
    simp only [freeSet, Set.mem_compl_iff, Set.mem_ofPred_eq] at hx
    push Not at hx
    obtain ⟨g, hg, hne⟩ := hx
    exact Set.mem_iUnion₂.2 ⟨g, hne, hg⟩
  exact measure_mono_null hsub (measure_iUnion_null fun g => measure_iUnion_null fun hg => h g hg)

/-- The free part of an essentially free system. -/
def free [Countable G] (S : PSystem G) (h : S.EssFree) : PSystem G :=
  S.restrict S.freeSet S.measurableSet_freeSet S.freeSet_invariant (S.measure_freeSet_compl h)

instance free_isFree [Countable G] (S : PSystem G) (h : S.EssFree) : (S.free h).IsFree :=
  ⟨fun g x hx => by
    have hx' : g • (x : S.freeSet).1 = (x : S.freeSet).1 := congrArg Subtype.val hx
    exact (x : S.freeSet).2 g hx'⟩

theorem free_iso [Countable G] (S : PSystem G) (h : S.EssFree) : (S.free h).Iso S :=
  S.restrict_iso _ _ _ _

end PSystem

end Collapse
