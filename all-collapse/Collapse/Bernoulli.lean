module

public import Collapse.System
public import Mathlib.Probability.ProductMeasure
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal

/-!
# Bernoulli shifts and generalized Bernoulli shifts

Conventions: `bernoulli G L lam` is `Ber_G(L)` and `gb G F M mu` is `GB_G(F; M)`,
the shift on `M^(G/F)`. Isomorphic bases, in the sense of `AEIso`, give isomorphic systems.
-/

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory

namespace Collapse

instance quotient_countable (G : Type) [Group G] [Countable G] (F : Subgroup G) :
    Countable (G ⧸ F) :=
  Function.Surjective.countable (QuotientGroup.mk_surjective (s := F))

/-- Isomorphism of probability spaces modulo null sets. -/
def AEIso {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X)
    (ν : Measure Y) : Prop :=
  ∃ (s : Set X) (t : Set Y), MeasurableSet s ∧ MeasurableSet t ∧ μ sᶜ = 0 ∧ ν tᶜ = 0 ∧
    ∃ e : s ≃ᵐ t, MeasurePreserving e (μ.comap (Subtype.val : s → X))
      (ν.comap (Subtype.val : t → Y))

namespace AEIso

variable {X Y Z W : Type} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
  [MeasurableSpace W] {μ : Measure X} {ν : Measure Y} {ρ : Measure Z} {σ : Measure W}

/-- An `AEIso` from global maps, inverse to each other between conull measurable sets. -/
theorem of_global {s : Set X} {t : Set Y} (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hsc : ∀ᵐ x ∂μ, x ∈ s) (htc : ∀ᵐ y ∂ν, y ∈ t) {f : X → Y} {g : Y → X}
    (hf : MeasurePreserving f μ ν) (hg : Measurable g) (hfs : ∀ x ∈ s, f x ∈ t)
    (hgt : ∀ y ∈ t, g y ∈ s) (hgf : ∀ x ∈ s, g (f x) = x) (hfg : ∀ y ∈ t, f (g y) = y) :
    AEIso μ ν :=
  ⟨s, t, hs, ht, ae_iff.1 hsc, ae_iff.1 htc,
    { toFun := fun x => ⟨f x.1, hfs x.1 x.2⟩
      invFun := fun y => ⟨g y.1, hgt y.1 y.2⟩
      left_inv := fun x => Subtype.ext (hgf x.1 x.2)
      right_inv := fun y => Subtype.ext (hfg y.1 y.2)
      measurable_toFun := (hf.measurable.comp measurable_subtype_coe).subtype_mk
      measurable_invFun := (hg.comp measurable_subtype_coe).subtype_mk },
    mp_restrict hs ht hsc htc hf hfs⟩

open Classical in
/-- The global extension of an equivalence between subsets. -/
def globalMap [Nonempty Y] (s : Set X) (t : Set Y) (e : s ≃ᵐ t) (x : X) : Y :=
  if h : x ∈ s then (e ⟨x, h⟩ : Y) else Classical.arbitrary Y

theorem globalMap_of_mem [Nonempty Y] {s : Set X} {t : Set Y} (e : s ≃ᵐ t) {x : X} (h : x ∈ s) :
    globalMap s t e x = (e ⟨x, h⟩ : Y) := by
  simp [globalMap, h]

theorem mp_globalMap [Nonempty Y] {s : Set X} {t : Set Y} (hs : MeasurableSet s)
    (ht : MeasurableSet t) (hsc : ∀ᵐ x ∂μ, x ∈ s) (htc : ∀ᵐ y ∂ν, y ∈ t) (e : s ≃ᵐ t)
    (he : MeasurePreserving e (μ.comap Subtype.val) (ν.comap Subtype.val)) :
    MeasurePreserving (globalMap s t e) μ ν := by
  classical
  have hm : Measurable (globalMap s t e) :=
    Measurable.dite (measurable_subtype_coe.comp e.measurable) measurable_const hs
  refine ⟨hm, ?_⟩
  have h1 : globalMap s t e ∘ Subtype.val = Subtype.val ∘ e :=
    funext fun x => globalMap_of_mem e x.2
  have hS := (BernoulliIso.measurePreserving_conullSubtype μ hs hsc).map_eq
  have hT := (BernoulliIso.measurePreserving_conullSubtype ν ht htc).map_eq
  calc Measure.map (globalMap s t e) μ
      = Measure.map (globalMap s t e) (Measure.map Subtype.val (μ.comap Subtype.val)) := by
        rw [hS]
    _ = Measure.map (Subtype.val ∘ e) (μ.comap Subtype.val) := by
        rw [Measure.map_map hm measurable_subtype_coe, h1]
    _ = ν := by
        rw [← Measure.map_map measurable_subtype_coe e.measurable, he.map_eq, hT]

theorem exists_global [Nonempty X] [Nonempty Y] (h : AEIso μ ν) :
    ∃ (s : Set X) (t : Set Y), MeasurableSet s ∧ MeasurableSet t ∧ (∀ᵐ x ∂μ, x ∈ s) ∧
      (∀ᵐ y ∂ν, y ∈ t) ∧ ∃ (f : X → Y) (g : Y → X), MeasurePreserving f μ ν ∧
      MeasurePreserving g ν μ ∧ (∀ x ∈ s, f x ∈ t) ∧ (∀ y ∈ t, g y ∈ s) ∧
      (∀ x ∈ s, g (f x) = x) ∧ (∀ y ∈ t, f (g y) = y) := by
  obtain ⟨s, t, hs, ht, hsc, htc, e, he⟩ := h
  have hsc' : ∀ᵐ x ∂μ, x ∈ s := ae_iff.2 hsc
  have htc' : ∀ᵐ y ∂ν, y ∈ t := ae_iff.2 htc
  refine ⟨s, t, hs, ht, hsc', htc', globalMap s t e, globalMap t s e.symm,
    mp_globalMap hs ht hsc' htc' e he, mp_globalMap ht hs htc' hsc' e.symm (he.symm e),
    ?_, ?_, ?_, ?_⟩
  · intro x hx; rw [globalMap_of_mem _ hx]; exact (e _).2
  · intro y hy; rw [globalMap_of_mem _ hy]; exact (e.symm _).2
  · intro x hx; rw [globalMap_of_mem _ hx, globalMap_of_mem _ (e _).2]; simp
  · intro y hy; rw [globalMap_of_mem _ hy, globalMap_of_mem _ (e.symm _).2]; simp

theorem refl (μ : Measure X) : AEIso μ μ :=
  of_global MeasurableSet.univ MeasurableSet.univ (ae_of_all _ fun _ => trivial)
    (ae_of_all _ fun _ => trivial) (MeasurePreserving.id μ) measurable_id
    (fun _ _ => trivial) (fun _ _ => trivial) (fun _ _ => rfl) (fun _ _ => rfl)

theorem symm (h : AEIso μ ν) : AEIso ν μ := by
  obtain ⟨s, t, hs, ht, hsc, htc, e, he⟩ := h
  exact ⟨t, s, ht, hs, htc, hsc, e.symm, he.symm e⟩

theorem trans [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]
    (h : AEIso μ ν) (h' : AEIso ν ρ) : AEIso μ ρ := by
  have := nonempty_of_isProbabilityMeasure μ
  have := nonempty_of_isProbabilityMeasure ν
  have := nonempty_of_isProbabilityMeasure ρ
  obtain ⟨s₁, t₁, hs₁, ht₁, hsc₁, htc₁, f₁, g₁, hf₁, hg₁, m₁, n₁, l₁, r₁⟩ := h.exists_global
  obtain ⟨s₂, t₂, hs₂, ht₂, hsc₂, htc₂, f₂, g₂, hf₂, hg₂, m₂, n₂, l₂, r₂⟩ := h'.exists_global
  exact of_global (hs₁.inter (hs₂.preimage hf₁.measurable))
    (ht₂.inter (ht₁.preimage hg₂.measurable))
    (hsc₁.and (hf₁.quasiMeasurePreserving.ae hsc₂))
    (htc₂.and (hg₂.quasiMeasurePreserving.ae htc₁))
    (hf₂.comp hf₁) (hg₁.measurable.comp hg₂.measurable)
    (fun x hx => ⟨m₂ _ hx.2, by
      simp only [Set.mem_preimage, Function.comp_apply, l₂ _ hx.2]; exact m₁ _ hx.1⟩)
    (fun y hy => ⟨n₁ _ hy.2, by
      simp only [Set.mem_preimage, Function.comp_apply, r₁ _ hy.2]; exact n₂ _ hy.1⟩)
    (fun x hx => by simp only [Function.comp_apply]; rw [l₂ _ hx.2, l₁ _ hx.1])
    (fun y hy => by simp only [Function.comp_apply]; rw [r₁ _ hy.2, r₂ _ hy.1])

theorem prod [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]
    [IsProbabilityMeasure σ] (h : AEIso μ ν) (h' : AEIso ρ σ) :
    AEIso (μ.prod ρ) (ν.prod σ) := by
  have := nonempty_of_isProbabilityMeasure μ
  have := nonempty_of_isProbabilityMeasure ν
  have := nonempty_of_isProbabilityMeasure ρ
  have := nonempty_of_isProbabilityMeasure σ
  obtain ⟨s₁, t₁, hs₁, ht₁, hsc₁, htc₁, f₁, g₁, hf₁, hg₁, m₁, n₁, l₁, r₁⟩ := h.exists_global
  obtain ⟨s₂, t₂, hs₂, ht₂, hsc₂, htc₂, f₂, g₂, hf₂, hg₂, m₂, n₂, l₂, r₂⟩ := h'.exists_global
  exact of_global (hs₁.prod hs₂) (ht₁.prod ht₂)
    ((measurePreserving_fst.quasiMeasurePreserving.ae hsc₁).and
      (measurePreserving_snd.quasiMeasurePreserving.ae hsc₂))
    ((measurePreserving_fst.quasiMeasurePreserving.ae htc₁).and
      (measurePreserving_snd.quasiMeasurePreserving.ae htc₂))
    (hf₁.prod hf₂) (hg₁.measurable.prodMap hg₂.measurable)
    (fun x hx => ⟨m₁ _ hx.1, m₂ _ hx.2⟩) (fun y hy => ⟨n₁ _ hy.1, n₂ _ hy.2⟩)
    (fun x hx => Prod.ext (l₁ _ hx.1) (l₂ _ hx.2)) (fun y hy => Prod.ext (r₁ _ hy.1) (r₂ _ hy.2))

/-- A measurable embedding is an isomorphism onto its image measure. -/
theorem of_measurableEmbedding [IsProbabilityMeasure μ] (f : X → Y)
    (hf : MeasurableEmbedding f) : AEIso μ (μ.map f) := by
  have hX := nonempty_of_isProbabilityMeasure μ
  obtain ⟨g, hg, hgf⟩ := hf.exists_measurable_extend measurable_id (fun _ => hX)
  exact of_global MeasurableSet.univ hf.measurableSet_range (ae_of_all _ fun _ => trivial)
    (hf.ae_map_iff.2 (ae_of_all _ fun x => ⟨x, rfl⟩)) ⟨hf.measurable, rfl⟩ hg
    (fun x _ => ⟨x, rfl⟩) (fun _ _ => trivial) (fun x _ => congrFun hgf x)
    (by rintro _ ⟨x, rfl⟩; exact congrArg f (congrFun hgf x))

end AEIso

/-- Reindexing the coordinates by a bijection preserves the product measure. -/
theorem measurePreserving_reindex {ι L : Type} [MeasurableSpace L] (lam : Measure L)
    [IsProbabilityMeasure lam] (σ : ι → ι) (hσ : Function.Bijective σ) :
    MeasurePreserving (fun (x : ι → L) i => x (σ i)) (Measure.infinitePi fun _ => lam)
      (Measure.infinitePi fun _ => lam) := by
  let e := Equiv.ofBijective σ hσ
  have h1 : (fun (x : ι → L) i => x (σ i)) =
      ⇑(MeasurableEquiv.piCongrLeft (fun _ : ι => L) e.symm) := by
    funext x i
    simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast, e]
  have h2 := Measure.infinitePi_map_piCongrLeft (fun _ : ι => lam) e.symm
  rw [h1]
  exact ⟨MeasurableEquiv.measurable _, h2⟩

variable (G : Type) [Group G] [Countable G]

/-- The shift action of `G` on `G → L`: `(g • x) h = x (g⁻¹ * h)`. -/
@[reducible] def shiftAction (G L : Type) [Group G] : MulAction G (G → L) where
  smul g x := fun h => x (g⁻¹ * h)
  one_smul x := funext fun h => by
    show x ((1 : G)⁻¹ * h) = x h
    rw [inv_one, one_mul]
  mul_smul g k x := funext fun h => by
    show x ((g * k)⁻¹ * h) = x (k⁻¹ * (g⁻¹ * h))
    rw [mul_inv_rev, mul_assoc]

/-- The Bernoulli shift `Ber_G(L)`: the space `G → L` with the product measure and the action
`(g • x) h = x (g⁻¹ * h)`. -/
def PSystem.bernoulli (L : Type) [MeasurableSpace L] [StandardBorelSpace L] (lam : Measure L)
    [IsProbabilityMeasure lam] : PSystem G where
  X := G → L
  act := shiftAction G L
  μ := Measure.infinitePi (fun _ : G => lam)
  preserving g := measurePreserving_reindex lam (fun h : G => g⁻¹ * h) (MulAction.bijective g⁻¹)

/-- The generalized Bernoulli shift `GB_G(F; M)`: the space `G ⧸ F → M` with the product
measure and the action `(g • x) q = x (g⁻¹ • q)`. -/
def PSystem.gb (F : Subgroup G) (M : Type) [MeasurableSpace M] [StandardBorelSpace M]
    (mu : Measure M) [IsProbabilityMeasure mu] : PSystem G where
  X := G ⧸ F → M
  act :=
    { smul := fun g x q => x (g⁻¹ • q)
      one_smul := fun x => funext fun q => by
        show x ((1 : G)⁻¹ • q) = x q
        rw [inv_one, one_smul]
      mul_smul := fun g k x => funext fun q => by
        show x ((g * k)⁻¹ • q) = x (k⁻¹ • g⁻¹ • q)
        rw [mul_inv_rev, mul_smul] }
  μ := Measure.infinitePi (fun _ : G ⧸ F => mu)
  preserving g :=
    measurePreserving_reindex mu (fun q : G ⧸ F => g⁻¹ • q) (MulAction.bijective g⁻¹)

namespace PSystem

variable {G}
variable {L L' : Type} [MeasurableSpace L] [StandardBorelSpace L] [MeasurableSpace L']
  [StandardBorelSpace L'] {lam : Measure L} {lam' : Measure L'} [IsProbabilityMeasure lam]
  [IsProbabilityMeasure lam']

theorem bernoulli_smul_apply (g : G) (x : (bernoulli G L lam).X) (h : G) :
    (g • x) h = x (g⁻¹ * h) := rfl

theorem gb_smul_apply (F : Subgroup G) (g : G) (x : (gb G F L lam).X) (q : G ⧸ F) :
    (g • x) q = x (g⁻¹ • q) := rfl

/-- Isomorphic bases give conjugate product systems, for an action permuting coordinates. -/
theorem pi_conj {ι : Type} [Countable ι] {aL : MulAction G (ι → L)}
    {aL' : MulAction G (ι → L')} (σ : G → ι → ι)
    (hL : ∀ (g : G) (x : ι → L) i, (g • x) i = x (σ g i))
    (hL' : ∀ (g : G) (x : ι → L') i, (g • x) i = x (σ g i)) (h : AEIso lam lam') :
    Nonempty (BernoulliIso.ConullConjugacy G (ι → L) (ι → L')
      (Measure.infinitePi fun _ => lam) (Measure.infinitePi fun _ => lam')) := by
  have := nonempty_of_isProbabilityMeasure lam
  have := nonempty_of_isProbabilityMeasure lam'
  obtain ⟨s, t, hs, ht, hsc, htc, f, g, hf, hg, m, n, l, r⟩ := h.exists_global
  have hmeas : ∀ {M : Type} [MeasurableSpace M] {u : Set M}, MeasurableSet u →
      MeasurableSet {x : ι → M | ∀ i, x i ∈ u} := fun hu => by
    rw [Set.ofPred_forall]; exact MeasurableSet.iInter fun i => hu.preimage (measurable_pi_apply i)
  have hae : ∀ {M : Type} [MeasurableSpace M] {m : Measure M} [IsProbabilityMeasure m]
      {u : Set M}, (∀ᵐ a ∂m, a ∈ u) →
      ∀ᵐ x ∂(Measure.infinitePi fun _ : ι => m), x ∈ {x : ι → M | ∀ i, x i ∈ u} :=
    fun hu => ae_all_iff.2 fun i =>
      (measurePreserving_eval_infinitePi _ i).quasiMeasurePreserving.ae hu
  have hF : MeasurePreserving (fun (x : ι → L) i => f (x i)) (Measure.infinitePi fun _ => lam)
      (Measure.infinitePi fun _ => lam') :=
    have hfm := hf.measurable
    ⟨by fun_prop, by rw [Measure.infinitePi_map_pi _ (fun _ => hfm), hf.map_eq]⟩
  refine ⟨conjMk _ _ (hmeas hs) (hmeas ht) (hae hsc) (hae htc) ?_ ?_ _ hF ⟨?_, ?_, ?_⟩ ?_⟩
  · intro k x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    intro i; rw [hL]; exact hx _
  · intro k x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    intro i; rw [hL']; exact hx _
  · intro x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    exact fun i => m _ (hx i)
  · intro x hx x' hx' hxx
    simp only [Set.mem_ofPred_eq] at hx hx'
    funext i
    rw [← l _ (hx i), ← l _ (hx' i)]; exact congrArg g (congrFun hxx i)
  · intro y hy
    simp only [Set.mem_ofPred_eq] at hy
    exact ⟨fun i => g (y i), fun i => n _ (hy i), funext fun i => r _ (hy i)⟩
  · intro k x _
    funext i
    simp only [hL, hL']

/-- The coordinatewise pairing carries the product of product measures to the product measure
of the products. -/
theorem infinitePi_prod_map {ι : Type} :
    ((Measure.infinitePi fun _ : ι => lam).prod (Measure.infinitePi fun _ : ι => lam')).map
      (fun p : (ι → L) × (ι → L') => fun i => (p.1 i, p.2 i)) =
      Measure.infinitePi fun _ => lam.prod lam' := by
  refine IsProjectiveLimit.unique (fun I => ?_) (Measure.isProjectiveLimit_infinitePi _)
  have hZ : Measurable (fun p : (ι → L) × (ι → L') => fun i => (p.1 i, p.2 i)) := by fun_prop
  have hr : ∀ {M : Type} [MeasurableSpace M], Measurable (I.restrict (π := fun _ : ι => M)) := by
    intro M _; exact Finset.measurable_restrict _
  rw [Measure.map_map hr hZ]
  have : I.restrict ∘ (fun p : (ι → L) × (ι → L') => fun i => (p.1 i, p.2 i)) =
      (MeasurableEquiv.arrowProdEquivProdArrow L L' I).symm ∘
        Prod.map I.restrict I.restrict := rfl
  rw [this, ← Measure.map_map (MeasurableEquiv.measurable _) (hr.prodMap hr),
    ← Measure.map_prod_map _ _ hr hr, Measure.infinitePi_map_restrict,
    Measure.infinitePi_map_restrict]
  exact ((measurePreserving_arrowProdEquivProdArrow L L' I (fun _ => lam)
    (fun _ => lam')).symm _).map_eq

/-- The product of product systems is the product system of the products. -/
theorem pi_prod_conj {ι : Type} [Countable ι] {aL : MulAction G (ι → L)}
    {aL' : MulAction G (ι → L')} {aP : MulAction G (ι → L × L')} (σ : G → ι → ι)
    (hL : ∀ (g : G) (x : ι → L) i, (g • x) i = x (σ g i))
    (hL' : ∀ (g : G) (x : ι → L') i, (g • x) i = x (σ g i))
    (hP : ∀ (g : G) (x : ι → L × L') i, (g • x) i = x (σ g i)) :
    Nonempty (BernoulliIso.ConullConjugacy G ((ι → L) × (ι → L')) (ι → L × L')
      ((Measure.infinitePi fun _ => lam).prod (Measure.infinitePi fun _ => lam'))
      (Measure.infinitePi fun _ => lam.prod lam')) :=
  ⟨conjMk Set.univ Set.univ MeasurableSet.univ MeasurableSet.univ
    (ae_of_all _ fun _ => trivial) (ae_of_all _ fun _ => trivial)
    (fun _ _ _ => trivial) (fun _ _ _ => trivial)
    (fun p : (ι → L) × (ι → L') => fun i => (p.1 i, p.2 i))
    ⟨by fun_prop, infinitePi_prod_map⟩
    (Set.bijOn_univ.2 ⟨fun a b hab => Prod.ext (funext fun i => congrArg Prod.fst (congrFun hab i))
      (funext fun i => congrArg Prod.snd (congrFun hab i)),
      fun z => ⟨(fun i => (z i).1, fun i => (z i).2), rfl⟩⟩)
    (fun k x _ => funext fun i => by simp only [Prod.smul_fst, Prod.smul_snd, hL, hL', hP])⟩

/-- Isomorphic bases have isomorphic Bernoulli shifts. -/
theorem bernoulli_iso_of_aeIso (h : AEIso lam lam') :
    (bernoulli G L lam).Iso (bernoulli G L' lam') :=
  pi_conj (fun g h => g⁻¹ * h) (fun _ _ _ => rfl) (fun _ _ _ => rfl) h

/-- Isomorphic bases have isomorphic generalized Bernoulli shifts. -/
theorem gb_iso_of_aeIso (F : Subgroup G) (h : AEIso lam lam') :
    (gb G F L lam).Iso (gb G F L' lam') :=
  pi_conj (fun g q => g⁻¹ • q) (fun _ _ _ => rfl) (fun _ _ _ => rfl) h

/-- `Ber(L) × Ber(L') = Ber(L × L')`. -/
theorem bernoulli_prod :
    ((bernoulli G L lam).prod (bernoulli G L' lam')).Iso
      (bernoulli G (L × L') (lam.prod lam')) :=
  pi_prod_conj (fun g h => g⁻¹ * h) (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl)

/-- `GB(F; M) × GB(F; M') = GB(F; M × M')`. -/
theorem gb_prod (F : Subgroup G) :
    ((gb G F L lam).prod (gb G F L' lam')).Iso (gb G F (L × L') (lam.prod lam')) :=
  pi_prod_conj (fun g q => g⁻¹ • q) (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl)

end PSystem

end Collapse
