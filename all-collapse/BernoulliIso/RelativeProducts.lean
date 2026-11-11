module

public import BernoulliIso.MeasuredExtraction
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.Distributions.Uniform

/-!
Products and absorption over a single retained marker. Fiber laws are retained
explicitly, so taking countably many maps over the same marker does not assert
unconditional independence of their marker-dependent outputs.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace BernoulliIso

/-- A jointly measurable family of probability isomorphisms. All fibers use
the same source and target measures, and the marker is retained. -/
structure RelativeProbabilityIso (Ω : Type*) [MeasurableSpace Ω]
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (ν : Measure X) (ρ : Measure Y) where
  equiv : Ω → X ≃ᵐ Y
  jointlyMeasurable : Measurable (fun p : Ω × X => equiv p.1 p.2)
  jointlyMeasurable_symm : Measurable (fun p : Ω × Y => (equiv p.1).symm p.2)
  measurePreserving : ∀ ω, MeasurePreserving (equiv ω) ν ρ

namespace RelativeProbabilityIso

variable {Ω X Y Z : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  [MeasurableSpace Y] [MeasurableSpace Z]
  {ν : Measure X} {ρ : Measure Y} {σ : Measure Z}

/-- Assemble fiberwise bijections without assuming that their inverses depend
measurably on the marker. Joint inverse measurability is derived by applying
the standard Borel embedding theorem to the retained-marker map. -/
noncomputable def ofFiberwise [StandardBorelSpace Ω] [StandardBorelSpace X]
    [StandardBorelSpace Y] (f : Ω → X → Y)
    (hf : Measurable (Function.uncurry f)) (hb : ∀ ω, Function.Bijective (f ω))
    (hpres : ∀ ω, MeasurePreserving (f ω) ν ρ) : RelativeProbabilityIso Ω ν ρ := by
  let E : Ω × X ≃ᵐ Ω × Y := measurableEquivOfBijective
    (fun p => (p.1, f p.1 p.2)) (measurable_fst.prodMk hf) (by
      constructor
      · rintro ⟨ω, x⟩ ⟨ω', x'⟩ h
        have hω : ω = ω' := congrArg Prod.fst h
        subst ω'
        exact Prod.ext rfl ((hb ω).injective (congrArg Prod.snd h))
      · rintro ⟨ω, y⟩
        obtain ⟨x, hx⟩ := (hb ω).surjective y
        exact ⟨(ω, x), Prod.ext rfl hx⟩)
  let e : Ω → X ≃ᵐ Y := fun ω =>
    measurableEquivOfBijective (f ω) hf.of_uncurry_left (hb ω)
  have hinverse (p : Ω × Y) : (e p.1).symm p.2 = (E.symm p).2 := by
    apply (e p.1).injective
    rw [MeasurableEquiv.apply_symm_apply]
    have hm : (E.symm p).1 = p.1 := congrArg Prod.fst (E.apply_symm_apply p)
    have hd : f (E.symm p).1 (E.symm p).2 = p.2 := congrArg Prod.snd (E.apply_symm_apply p)
    change p.2 = f p.1 (E.symm p).2
    simpa only [hm] using hd.symm
  refine ⟨e, hf, ?_, hpres⟩
  have heq : (fun p : Ω × Y => (e p.1).symm p.2) = fun p => (E.symm p).2 :=
    funext hinverse
  rw [heq]
  exact measurable_snd.comp E.symm.measurable

def constant (e : ProbabilityIso ν ρ) : RelativeProbabilityIso Ω ν ρ where
  equiv _ := e.equiv
  jointlyMeasurable := e.equiv.measurable.comp measurable_snd
  jointlyMeasurable_symm := e.equiv.symm.measurable.comp measurable_snd
  measurePreserving _ := e.measurePreserving

def refl (ν : Measure X) : RelativeProbabilityIso Ω ν ν := constant (ProbabilityIso.refl ν)

def symm (e : RelativeProbabilityIso Ω ν ρ) : RelativeProbabilityIso Ω ρ ν where
  equiv ω := (e.equiv ω).symm
  jointlyMeasurable := e.jointlyMeasurable_symm
  jointlyMeasurable_symm := e.jointlyMeasurable
  measurePreserving ω := (e.measurePreserving ω).symm (e.equiv ω)

def trans (e : RelativeProbabilityIso Ω ν ρ) (f : RelativeProbabilityIso Ω ρ σ) :
    RelativeProbabilityIso Ω ν σ where
  equiv ω := (e.equiv ω).trans (f.equiv ω)
  jointlyMeasurable := f.jointlyMeasurable.comp
    (measurable_fst.prodMk e.jointlyMeasurable)
  jointlyMeasurable_symm := e.jointlyMeasurable_symm.comp
    (measurable_fst.prodMk f.jointlyMeasurable_symm)
  measurePreserving ω := (f.measurePreserving ω).comp (e.measurePreserving ω)

def prod {X' Y' : Type*} [MeasurableSpace X'] [MeasurableSpace Y']
    {ν' : Measure X'} {ρ' : Measure Y'} [SFinite ν] [SFinite ν']
    (e : RelativeProbabilityIso Ω ν ρ) (f : RelativeProbabilityIso Ω ν' ρ') :
    RelativeProbabilityIso Ω (ν.prod ν') (ρ.prod ρ') where
  equiv ω := (e.equiv ω).prodCongr (f.equiv ω)
  jointlyMeasurable :=
    (e.jointlyMeasurable.comp (measurable_fst.prodMk
      (measurable_fst.comp measurable_snd))).prodMk
    (f.jointlyMeasurable.comp (measurable_fst.prodMk
      (measurable_snd.comp measurable_snd)))
  jointlyMeasurable_symm :=
    (e.jointlyMeasurable_symm.comp (measurable_fst.prodMk
      (measurable_fst.comp measurable_snd))).prodMk
    (f.jointlyMeasurable_symm.comp (measurable_fst.prodMk
      (measurable_snd.comp measurable_snd)))
  measurePreserving ω := (e.measurePreserving ω).prod (f.measurePreserving ω)

/-- The family gives an actual isomorphism of joint product measures retaining
the marker exactly. -/
def retained (e : RelativeProbabilityIso Ω ν ρ) (μ : Measure Ω)
    [SFinite μ] [SFinite ν] : ProbabilityIso (μ.prod ν) (μ.prod ρ) where
  equiv :=
    { toFun p := (p.1, e.equiv p.1 p.2)
      invFun p := (p.1, (e.equiv p.1).symm p.2)
      left_inv p := by simp
      right_inv p := by simp
      measurable_toFun := measurable_fst.prodMk e.jointlyMeasurable
      measurable_invFun := measurable_fst.prodMk e.jointlyMeasurable_symm }
  measurePreserving := (MeasurePreserving.id μ).skew_product e.jointlyMeasurable
    (Filter.Eventually.of_forall fun ω => (e.measurePreserving ω).map_eq)

/-- Countable products over the same marker. In fact the construction works
for any index type carrying the product sigma algebra. -/
def pi {ι : Type*} {A B : ι → Type*} [∀ i, MeasurableSpace (A i)]
    [∀ i, MeasurableSpace (B i)] {α : ∀ i, Measure (A i)} {β : ∀ i, Measure (B i)}
    [∀ i, IsProbabilityMeasure (α i)] [∀ i, IsProbabilityMeasure (β i)]
    (e : ∀ i, RelativeProbabilityIso Ω (α i) (β i)) :
    RelativeProbabilityIso Ω (Measure.infinitePi α) (Measure.infinitePi β) where
  equiv ω := MeasurableEquiv.piCongrRight fun i => (e i).equiv ω
  jointlyMeasurable := Measurable.of_eval fun i =>
    (e i).jointlyMeasurable.comp
      (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))
  jointlyMeasurable_symm := Measurable.of_eval fun i =>
    (e i).jointlyMeasurable_symm.comp
      (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))
  measurePreserving ω := by
    refine ⟨(MeasurableEquiv.piCongrRight fun i => (e i).equiv ω).measurable, ?_⟩
    change Measure.map (fun x i => (e i).equiv ω (x i)) (Measure.infinitePi α) = _
    rw [Measure.infinitePi_map_pi α (fun i => ((e i).equiv ω).measurable)]
    congr 1
    funext i
    exact ((e i).measurePreserving ω).map_eq

/-- Covariance of a relative map includes its retained marker. -/
def Equivariant {G : Type*} [Group G] [MulAction G Ω] [MulAction G X] [MulAction G Y]
    (e : RelativeProbabilityIso Ω ν ρ) : Prop :=
  ∀ (g : G) (ω : Ω) (x : X), e.equiv (g • ω) (g • x) = g • e.equiv ω x

theorem Equivariant.symm {G : Type*} [Group G] [MulAction G Ω]
    [MulAction G X] [MulAction G Y] {e : RelativeProbabilityIso Ω ν ρ}
    (he : e.Equivariant (G := G)) : e.symm.Equivariant (G := G) := by
  intro g ω y
  apply (e.equiv (g • ω)).injective
  change e.equiv (g • ω) ((e.equiv (g • ω)).symm (g • y)) =
    e.equiv (g • ω) (g • (e.equiv ω).symm y)
  rw [MeasurableEquiv.apply_symm_apply]
  rw [he, MeasurableEquiv.apply_symm_apply]

theorem Equivariant.trans {G : Type*} [Group G] [MulAction G Ω]
    [MulAction G X] [MulAction G Y] [MulAction G Z]
    {e : RelativeProbabilityIso Ω ν ρ} {f : RelativeProbabilityIso Ω ρ σ}
    (he : e.Equivariant (G := G)) (hf : f.Equivariant (G := G)) :
    (e.trans f).Equivariant (G := G) := by
  intro g ω x
  change f.equiv (g • ω) (e.equiv (g • ω) (g • x)) = g • f.equiv ω (e.equiv ω x)
  rw [he, hf]

theorem Equivariant.prod {G : Type*} [Group G] [MulAction G Ω]
    [MulAction G X] [MulAction G Y]
    {X' Y' : Type*} [MeasurableSpace X'] [MeasurableSpace Y']
    [MulAction G X'] [MulAction G Y']
    {ν' : Measure X'} {ρ' : Measure Y'} [SFinite ν] [SFinite ν']
    {e : RelativeProbabilityIso Ω ν ρ} {f : RelativeProbabilityIso Ω ν' ρ'}
    (he : e.Equivariant (G := G)) (hf : f.Equivariant (G := G)) :
    (e.prod f).Equivariant (G := G) := by
  intro g ω p
  exact Prod.ext (he g ω p.1) (hf g ω p.2)

theorem Equivariant.pi {G ι : Type*} [Group G] [MulAction G Ω]
    {A B : ι → Type*} [∀ i, MeasurableSpace (A i)] [∀ i, MeasurableSpace (B i)]
    [∀ i, MulAction G (A i)] [∀ i, MulAction G (B i)]
    {α : ∀ i, Measure (A i)} {β : ∀ i, Measure (B i)}
    [∀ i, IsProbabilityMeasure (α i)] [∀ i, IsProbabilityMeasure (β i)]
    {e : ∀ i, RelativeProbabilityIso Ω (α i) (β i)}
    (he : ∀ i, (e i).Equivariant (G := G)) : (pi e).Equivariant (G := G) := by
  intro g ω x
  funext i
  exact he i g ω (x i)

end RelativeProbabilityIso

namespace ProbabilityIso

def assoc {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    (μ : Measure A) (ν : Measure B) (ρ : Measure C)
    [SFinite μ] [SFinite ν] [SFinite ρ] :
    ProbabilityIso ((μ.prod ν).prod ρ) (μ.prod (ν.prod ρ)) :=
  ⟨MeasurableEquiv.prodAssoc, measurePreserving_prodAssoc μ ν ρ⟩

/-- Reindexing independent probability coordinates preserves the product law. -/
def reindex {ι κ : Type*} {A : κ → Type*} [∀ i, MeasurableSpace (A i)]
    (μ : ∀ i, Measure (A i)) [∀ i, IsProbabilityMeasure (μ i)] (e : ι ≃ κ) :
    ProbabilityIso (Measure.infinitePi (fun i => μ (e i))) (Measure.infinitePi μ) :=
  ⟨MeasurableEquiv.piCongrLeft A e,
    ⟨(MeasurableEquiv.piCongrLeft A e).measurable, Measure.infinitePi_map_piCongrLeft μ e⟩⟩

/-- Reassociation of nested independent arrays, including genuinely
countably infinite rows and columns. -/
def curry {ι κ A : Type*} [MeasurableSpace A]
    (μ : ι → κ → Measure A) [∀ i j, IsProbabilityMeasure (μ i j)] :
    ProbabilityIso (Measure.infinitePi (fun p : ι × κ => μ p.1 p.2))
      (Measure.infinitePi (fun i => Measure.infinitePi (μ i))) :=
  ⟨MeasurableEquiv.curry ι κ A,
    ⟨(MeasurableEquiv.curry ι κ A).measurable, Measure.infinitePi_map_curry μ⟩⟩

/-- Splitting a product into disjoint families of independent coordinates. -/
def sumPi {ι κ : Type*} {A : ι ⊕ κ → Type*} [∀ i, MeasurableSpace (A i)]
    (μ : ∀ i, Measure (A i)) [∀ i, IsProbabilityMeasure (μ i)] :
    ProbabilityIso (Measure.infinitePi μ)
      ((Measure.infinitePi (fun i => μ (.inl i))).prod
        (Measure.infinitePi (fun i => μ (.inr i)))) where
  equiv := MeasurableEquiv.sumPiEquivProdPi A
  measurePreserving := by
    refine ⟨(MeasurableEquiv.sumPiEquivProdPi A).measurable, ?_⟩
    have hI : iIndepFun (fun i (x : ∀ j, A j) => x i) (Measure.infinitePi μ) :=
      iIndepFun_infinitePi (fun _ => measurable_id)
    have hd : Disjoint (Set.range (Sum.inl : ι → ι ⊕ κ)) (Set.range Sum.inr) := by
      apply Set.disjoint_left.mpr
      rintro z ⟨i, rfl⟩ ⟨j, h⟩
      exact Sum.inr_ne_inl h
    have hLR : IndepFun (fun x : ∀ j, A j => fun i => x (.inl i))
        (fun x : ∀ j, A j => fun i => x (.inr i)) (Measure.infinitePi μ) := by
      exact (hI.indepFun_set _ _ hd (fun i => measurable_pi_apply i)).comp
        (φ := fun (x : ∀ j : Set.range (Sum.inl : ι → ι ⊕ κ), A j.val) (i : ι) =>
          x ⟨Sum.inl i, ⟨i, rfl⟩⟩)
        (ψ := fun (x : ∀ j : Set.range (Sum.inr : κ → ι ⊕ κ), A j.val) (i : κ) =>
          x ⟨Sum.inr i, ⟨i, rfl⟩⟩)
        (Measurable.of_eval fun i : ι => measurable_pi_apply
          (X := fun j : Set.range (Sum.inl : ι → ι ⊕ κ) => A j.val)
          (⟨Sum.inl i, ⟨i, rfl⟩⟩ : Set.range (Sum.inl : ι → ι ⊕ κ)))
        (Measurable.of_eval fun i : κ => measurable_pi_apply
          (X := fun j : Set.range (Sum.inr : κ → ι ⊕ κ) => A j.val)
          (⟨Sum.inr i, ⟨i, rfl⟩⟩ : Set.range (Sum.inr : κ → ι ⊕ κ)))
    change Measure.map (fun x : ∀ j, A j => ((fun i => x (.inl i)), (fun i => x (.inr i))))
      (Measure.infinitePi μ) = _
    rw [hLR.map_prod_eq_prod_map_map
      (Measurable.of_eval fun i => measurable_pi_apply (Sum.inl i)).aemeasurable
      (Measurable.of_eval fun i => measurable_pi_apply (Sum.inr i)).aemeasurable]
    rw [Measure.map_infinitePi_infinitePi_of_inj Sum.inl_injective,
      Measure.map_infinitePi_infinitePi_of_inj Sum.inr_injective]

/-- An explicit interleaving of two independent families of the same factor. -/
noncomputable def interleave {ι κ Z : Type*} [MeasurableSpace Z]
    (μ : Measure Z) [IsProbabilityMeasure μ] (e : ι ⊕ κ ≃ ι) :
    ProbabilityIso ((Measure.infinitePi (fun _ : ι => μ)).prod
      (Measure.infinitePi (fun _ : κ => μ))) (Measure.infinitePi (fun _ : ι => μ)) :=
  (sumPi (fun _ : ι ⊕ κ => μ)).symm.trans (reindex (fun _ : ι => μ) e)

end ProbabilityIso

namespace RelativeProbabilityIso

/-- Marker-dependent coordinate permutations preserve the conditional iid
law. The two measurability premises concern only the coordinate reindexing;
the probability law is a conclusion. -/
def reindex {Ω ι κ Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    (μ : Measure Z) [IsProbabilityMeasure μ] (slots : Ω → ι ≃ κ)
    (hf : Measurable (fun p : Ω × (ι → Z) =>
      MeasurableEquiv.piCongrLeft (fun _ : κ => Z) (slots p.1) p.2))
    (hb : Measurable (fun p : Ω × (κ → Z) =>
      (MeasurableEquiv.piCongrLeft (fun _ : κ => Z) (slots p.1)).symm p.2)) :
    RelativeProbabilityIso Ω (Measure.infinitePi (fun _ : ι => μ))
      (Measure.infinitePi (fun _ : κ => μ)) where
  equiv ω := MeasurableEquiv.piCongrLeft (fun _ : κ => Z) (slots ω)
  jointlyMeasurable := hf
  jointlyMeasurable_symm := hb
  measurePreserving ω := (ProbabilityIso.reindex (fun _ : κ => μ) (slots ω)).measurePreserving

/-- The manuscript's explicit absorption composition. The only premise is
an actual relative isomorphism producing an infinite reservoir of `Z` factors;
no cancellation of a common factor is inferred. -/
noncomputable def absorb {Ω X Z ι κ : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [MeasurableSpace Z] (ν : Measure X) (σ : Measure Z)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure σ]
    (θ : RelativeProbabilityIso Ω ν (ν.prod (Measure.infinitePi (fun _ : ι => σ))))
    (slots : ι ⊕ κ ≃ ι) :
    RelativeProbabilityIso Ω (ν.prod (Measure.infinitePi (fun _ : κ => σ))) ν :=
  (θ.prod (refl _)).trans <|
    (constant (ProbabilityIso.assoc ν
      (Measure.infinitePi (fun _ : ι => σ)) (Measure.infinitePi (fun _ : κ => σ)))).trans <|
    ((refl ν).prod (constant (ProbabilityIso.interleave σ slots))).trans θ.symm

theorem absorb_equivariant {G Ω X Z ι κ : Type*} [Group G]
    [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Z]
    [MulAction G Ω] [MulAction G X] [MulAction G Z]
    (ν : Measure X) (σ : Measure Z)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure σ]
    (θ : RelativeProbabilityIso Ω ν (ν.prod (Measure.infinitePi (fun _ : ι => σ))))
    (hθ : θ.Equivariant (G := G)) (slots : ι ⊕ κ ≃ ι) :
    (absorb ν σ θ slots).Equivariant (G := G) := by
  unfold absorb
  apply Equivariant.trans (hθ.prod (by intro g ω x; rfl))
  apply Equivariant.trans (by intro g ω x; rfl)
  apply Equivariant.trans ?_ hθ.symm
  apply Equivariant.prod (by intro g ω x; rfl)
  intro g ω p
  funext i
  obtain ⟨j, rfl⟩ := slots.surjective i
  change (MeasurableEquiv.piCongrLeft (fun _ : ι => Z) slots)
      ((MeasurableEquiv.sumPiEquivProdPi (fun _ : ι ⊕ κ => Z)).symm (g • p)) (slots j) =
    g • (MeasurableEquiv.piCongrLeft (fun _ : ι => Z) slots)
      ((MeasurableEquiv.sumPiEquivProdPi (fun _ : ι ⊕ κ => Z)).symm p) (slots j)
  rw [MeasurableEquiv.piCongrLeft_apply_apply, MeasurableEquiv.piCongrLeft_apply_apply]
  cases j <;> rfl

end RelativeProbabilityIso

section HaarProducts

instance uniformFinite_isAddLeftInvariant {K : Type*} [AddCommGroup K] [Fintype K]
    [MeasurableSpace K] [MeasurableSingletonClass K] :
    Measure.IsAddLeftInvariant (Measure.uniformOfFinset (Finset.univ : Finset K)) where
  map_add_left_eq_self g := by
    apply Measure.ext_of_singleton
    intro a
    rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton a)]
    have hpre : (fun x : K => g + x) ⁻¹' {a} = {-g + a} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · intro h
        calc
          x = -g + (g + x) := by simp
          _ = -g + a := by rw [h]
      · intro h
        rw [h]
        simp
    rw [hpre]
    simp

/-- The finite uniform law used for marker digits and Bernoulli data is Haar. -/
theorem uniformFinite_isAddHaarMeasure {K : Type*} [AddCommGroup K] [Fintype K]
    [TopologicalSpace K] [IsTopologicalAddGroup K]
    [MeasurableSpace K] [BorelSpace K] [MeasurableSingletonClass K] :
    (Measure.uniformOfFinset (Finset.univ : Finset K)).IsAddHaarMeasure := by
  have hmass : Measure.uniformOfFinset (Finset.univ : Finset K) Set.univ = 1 := by
    have hn : (Fintype.card K : ℝ≥0∞) ≠ 0 := by
      exact_mod_cast (Fintype.card_ne_zero : Fintype.card K ≠ 0)
    simpa [Measure.uniformOfFinset_apply] using
      (ENNReal.div_self hn (by simp : (Fintype.card K : ℝ≥0∞) ≠ ∞))
  exact Measure.isAddHaarMeasure_of_isCompact_nonempty_interior
    _ Set.univ isCompact_univ (by simp) (by rw [hmass]; simp) (by rw [hmass]; simp)

variable {ι : Type*} {A : ι → Type*} [∀ i, AddCommGroup (A i)]
  [∀ i, MeasurableSpace (A i)] [∀ i, MeasurableAdd (A i)]
  (μ : ∀ i, Measure (A i)) [∀ i, IsProbabilityMeasure (μ i)]
  [∀ i, Measure.IsAddLeftInvariant (μ i)]

/-- Infinite products of translation-invariant probabilities are
translation-invariant. -/
instance infinitePi_isAddLeftInvariant : Measure.IsAddLeftInvariant (Measure.infinitePi μ) where
  map_add_left_eq_self x := by
    change Measure.map (fun y i => x i + y i) (Measure.infinitePi μ) = _
    rw [Measure.infinitePi_map_pi μ (fun i => measurable_const_add (x i))]
    simp only [map_add_left_eq_self]

/-- On compact additive groups, the infinite iid product really is Haar
probability. This connects the extractor's Haar theorem to Bernoulli laws. -/
theorem infinitePi_isAddHaarMeasure
    [∀ i, TopologicalSpace (A i)] [∀ i, CompactSpace (A i)]
    [∀ i, IsTopologicalAddGroup (A i)] [BorelSpace (∀ i, A i)] :
    (Measure.infinitePi μ).IsAddHaarMeasure := by
  exact Measure.isAddHaarMeasure_of_isCompact_nonempty_interior
    (Measure.infinitePi μ) Set.univ isCompact_univ (by simp) (by simp) (by simp)

end HaarProducts

/-- Reassociation of a family of pairs as a pair of families. -/
def piProdEquiv {ι : Type*} {A B : ι → Type*}
    [∀ i, MeasurableSpace (A i)] [∀ i, MeasurableSpace (B i)] :
    (∀ i, A i × B i) ≃ᵐ ((∀ i, A i) × (∀ i, B i)) where
  toFun x := ((fun i => (x i).1), (fun i => (x i).2))
  invFun p i := (p.1 i, p.2 i)
  left_inv _ := rfl
  right_inv _ := rfl
  measurable_toFun :=
    (Measurable.of_eval fun i => measurable_fst.comp (measurable_pi_apply i)).prodMk
      (Measurable.of_eval fun i => measurable_snd.comp (measurable_pi_apply i))
  measurable_invFun := Measurable.of_eval fun i =>
    ((measurable_pi_apply i).comp measurable_fst).prodMk
      ((measurable_pi_apply i).comp measurable_snd)

namespace ProbabilityIso

/-- The countable pair/family rearrangement preserves Haar product laws.
All factors occurring in the algebraic remainder construction satisfy these
compact-group hypotheses. -/
def piProduct {ι : Type*} [Countable ι] {A B : ι → Type*}
    [∀ i, AddCommGroup (A i)] [∀ i, AddCommGroup (B i)]
    [∀ i, TopologicalSpace (A i)] [∀ i, TopologicalSpace (B i)]
    [∀ i, IsTopologicalAddGroup (A i)] [∀ i, IsTopologicalAddGroup (B i)]
    [∀ i, CompactSpace (A i)] [∀ i, CompactSpace (B i)]
    [∀ i, SecondCountableTopology (A i)] [∀ i, SecondCountableTopology (B i)]
    [∀ i, MeasurableSpace (A i)] [∀ i, MeasurableSpace (B i)]
    [∀ i, BorelSpace (A i)] [∀ i, BorelSpace (B i)]
    (μ : ∀ i, Measure (A i)) (ν : ∀ i, Measure (B i))
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)]
    [∀ i, (μ i).IsAddHaarMeasure] [∀ i, (ν i).IsAddHaarMeasure] :
    ProbabilityIso (Measure.infinitePi (fun i => (μ i).prod (ν i)))
      ((Measure.infinitePi μ).prod (Measure.infinitePi ν)) := by
  letI := infinitePi_isAddHaarMeasure μ
  letI := infinitePi_isAddHaarMeasure ν
  letI := infinitePi_isAddHaarMeasure (fun i => (μ i).prod (ν i))
  let F : (∀ i, A i × B i) →+ ((∀ i, A i) × (∀ i, B i)) :=
    { toFun := piProdEquiv
      map_zero' := rfl
      map_add' _ _ := rfl }
  have hF : Continuous F :=
    (continuous_pi fun i => (continuous_apply i).fst).prodMk
      (continuous_pi fun i => (continuous_apply i).snd)
  exact ⟨piProdEquiv, F.measurePreserving hF piProdEquiv.surjective (by simp)⟩

end ProbabilityIso

namespace RelativeProbabilityIso

/-- The extraction family in the stronger fiber form needed for countable
products and absorption. Its joint inverse measurability and all Haar laws
are derived from the already certified extractor. -/
noncomputable def extraction {K : Type*} [Ring K] {Ω : Type*}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] {X Y : ℕ → Type*}
    [∀ n, AddCommGroup (X n)] [∀ n, AddCommGroup (Y n)]
    [∀ n, Module K (X n)] [∀ n, Module K (Y n)]
    [TopologicalSpace (X 0)] [CompactSpace (X 0)] [IsTopologicalAddGroup (X 0)]
    [MeasurableSpace (X 0)] [BorelSpace (X 0)] [StandardBorelSpace (X 0)]
    [∀ n, TopologicalSpace (Y n)] [∀ n, CompactSpace (Y n)]
    [∀ n, T2Space (Y n)] [∀ n, IsTopologicalAddGroup (Y n)]
    [∀ n, MeasurableSpace (Y n)] [BorelSpace (∀ n, Y n)]
    [∀ n, StandardBorelSpace (Y n)]
    (tower : Ω → ExtractionTower K X Y)
    (hcont : ∀ ω n, Continuous ((tower ω).output n))
    (hmeas : ∀ n, Measurable (fun p : Ω × X 0 => (tower p.1).output n p.2))
    (hinj : ∀ ω, Function.Injective (tower ω).extract)
    (ν : Measure (X 0)) (ρ : Measure (∀ n, Y n))
    [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]
    [ν.IsAddHaarMeasure] [ρ.IsAddHaarMeasure] : RelativeProbabilityIso Ω ν ρ :=
  ofFiberwise (fun ω => (tower ω).extract) (Measurable.of_eval hmeas)
    (fun ω => ⟨hinj ω, (tower ω).extract_surjective (hcont ω)⟩)
    (fun ω => (tower ω).measurePreserving_extract (hcont ω) ν ρ)

/-- Allocate one independent copy of the reservoir to each remainder, absorb
in each copy over the same marker, then recombine. `shuffle` is the explicit
pair/family rearrangement supplied by `ProbabilityIso.piProduct` for the
compact-group factors in the manuscript. -/
noncomputable def absorbFamily {Ω X ι : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    {Z : ι → Type*} [∀ i, MeasurableSpace (Z i)]
    (ν : Measure X) (ρ : ∀ i, Measure (Z i))
    [IsProbabilityMeasure ν] [∀ i, IsProbabilityMeasure (ρ i)]
    (θ : RelativeProbabilityIso Ω ν (Measure.infinitePi (fun _ : ι => ν)))
    (absorbers : ∀ i, RelativeProbabilityIso Ω (ν.prod (ρ i)) ν)
    (shuffle : ProbabilityIso (Measure.infinitePi (fun i => ν.prod (ρ i)))
      ((Measure.infinitePi (fun _ : ι => ν)).prod (Measure.infinitePi ρ))) :
    RelativeProbabilityIso Ω (ν.prod (Measure.infinitePi ρ)) ν :=
  (θ.prod (refl _)).trans <|
    (constant shuffle.symm).trans <|
    (pi absorbers).trans θ.symm

/-- Take independent copies of an exact split and identify both infinite
primary products with the same reservoir. This constructs the `θ` required
by `absorb`; it does not assume cancellation of the algebraic remainder. -/
noncomputable def reservoirFromSplit {Ω R A B Z ι : Type*}
    [MeasurableSpace Ω] [MeasurableSpace R] [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace Z]
    (μ : Measure R) (α : Measure A) (β : Measure B) (σ : Measure Z)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure α]
    [IsProbabilityMeasure β] [IsProbabilityMeasure σ]
    (split : RelativeProbabilityIso Ω α (β.prod σ))
    (left : RelativeProbabilityIso Ω μ (Measure.infinitePi (fun _ : ι => α)))
    (right : RelativeProbabilityIso Ω (Measure.infinitePi (fun _ : ι => β)) μ)
    (shuffle : ProbabilityIso (Measure.infinitePi (fun _ : ι => β.prod σ))
      ((Measure.infinitePi (fun _ : ι => β)).prod (Measure.infinitePi (fun _ : ι => σ)))) :
    RelativeProbabilityIso Ω μ (μ.prod (Measure.infinitePi (fun _ : ι => σ))) :=
  left.trans <| (pi (fun _ : ι => split)).trans <|
    (constant shuffle).trans (right.prod (refl _))

theorem absorbFamily_equivariant {G Ω X ι : Type*} [Group G]
    [MeasurableSpace Ω] [MeasurableSpace X] [MulAction G Ω] [MulAction G X]
    {Z : ι → Type*} [∀ i, MeasurableSpace (Z i)] [∀ i, MulAction G (Z i)]
    (ν : Measure X) (ρ : ∀ i, Measure (Z i))
    [IsProbabilityMeasure ν] [∀ i, IsProbabilityMeasure (ρ i)]
    (θ : RelativeProbabilityIso Ω ν (Measure.infinitePi (fun _ : ι => ν)))
    (hθ : θ.Equivariant (G := G))
    (absorbers : ∀ i, RelativeProbabilityIso Ω (ν.prod (ρ i)) ν)
    (ha : ∀ i, (absorbers i).Equivariant (G := G))
    (shuffle : ProbabilityIso (Measure.infinitePi (fun i => ν.prod (ρ i)))
      ((Measure.infinitePi (fun _ : ι => ν)).prod (Measure.infinitePi ρ)))
    (hs : ∀ (g : G) (p : (ι → X) × (∀ i, Z i)),
      shuffle.equiv.symm (g • p) = g • shuffle.equiv.symm p) :
    (absorbFamily ν ρ θ absorbers shuffle).Equivariant (G := G) := by
  exact (hθ.prod (by intro g ω x; rfl)).trans
    ((show (constant shuffle.symm : RelativeProbabilityIso Ω _ _).Equivariant (G := G)
      from fun g _ p => hs g p).trans ((Equivariant.pi ha).trans hθ.symm))

end RelativeProbabilityIso

end BernoulliIso

#print axioms BernoulliIso.RelativeProbabilityIso.pi
#print axioms BernoulliIso.ProbabilityIso.reindex
#print axioms BernoulliIso.RelativeProbabilityIso.absorb
#print axioms BernoulliIso.RelativeProbabilityIso.absorbFamily
#print axioms BernoulliIso.uniformFinite_isAddHaarMeasure
#print axioms BernoulliIso.infinitePi_isAddHaarMeasure
#print axioms BernoulliIso.ProbabilityIso.piProduct
