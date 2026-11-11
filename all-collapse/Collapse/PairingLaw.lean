module

public import Collapse.Bundle
public import Collapse.Atomless

/-!
# The pairing lemma

First part of the proof. Let `F = {1, f}` be a subgroup of order 2.
Pair the sites `γ` and `γ f`. The unordered pairs of letters form the generalized Bernoulli
shift `Ω₁ = GB(F; L⁽²⁾)`, a factor of `Ber(L)`. Given `Ω₁`, the order of every pair of distinct
letters is a fair bit, independent over the pairs. A transversal of the free action of `F` on
`Ω₁` picks a representative of each pair equivariantly and turns the orders into labels in
`ZMod 2`. So `Ber(L)` is the bundle over `Ω₁` of a set of positive measure. The base is `ℝ`,
which is no restriction for standard spaces; unordered pairs are the pairs `(min, max)`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory

namespace Collapse

/-- The law of the unordered pair of two independent points: the image of `lam ⊗ lam` under
`(a, b) ↦ (min a b, max a b)`. -/
def pairLaw (lam : Measure ℝ) : Measure (ℝ × ℝ) :=
  (lam.prod lam).map (fun p : ℝ × ℝ => (min p.1 p.2, max p.1 p.2))

theorem measurable_sort : Measurable (fun p : ℝ × ℝ => (min p.1 p.2, max p.1 p.2)) :=
  (measurable_fst.min measurable_snd).prodMk (measurable_fst.max measurable_snd)

instance pairLaw_isProbabilityMeasure (lam : Measure ℝ) [IsProbabilityMeasure lam] :
    IsProbabilityMeasure (pairLaw lam) := by
  unfold pairLaw; infer_instance

theorem pairLaw_singleton_le (lam : Measure ℝ) [IsProbabilityMeasure lam] (p : ℝ × ℝ) :
    pairLaw lam {p} ≤ lam {p.1} + lam {p.2} := by
  rw [pairLaw, Measure.map_apply measurable_sort (measurableSet_singleton p)]
  calc (lam.prod lam) (_ ⁻¹' {p}) ≤ (lam.prod lam) (({p.1} ∪ {p.2}) ×ˢ Set.univ) := by
        apply measure_mono
        rintro ⟨x, y⟩ hxy
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.ext_iff] at hxy
        simp only [Set.mem_prod, Set.mem_union, Set.mem_singleton_iff, Set.mem_univ, and_true]
        rcases le_total x y with h | h
        · left; rw [← hxy.1, min_eq_left h]
        · right; rw [← hxy.2, max_eq_left h]
    _ = lam ({p.1} ∪ {p.2}) := by rw [Measure.prod_prod, measure_univ, mul_one]
    _ ≤ _ := measure_union_le _ _

theorem pairLaw_diag (lam : Measure ℝ) [IsProbabilityMeasure lam] (a : ℝ) :
    pairLaw lam {(a, a)} = lam {a} * lam {a} := by
  rw [pairLaw, Measure.map_apply measurable_sort (measurableSet_singleton _),
    ← Measure.prod_prod]
  congr 1
  ext ⟨x, y⟩
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq, Set.mem_prod]
  constructor
  · rintro ⟨h1, h2⟩
    have := min_le_left x y; have := le_max_left x y
    have := min_le_right x y; have := le_max_right x y
    constructor <;> linarith
  · rintro ⟨rfl, rfl⟩; simp

theorem eq_dirac_of_compl (lam : Measure ℝ) [IsProbabilityMeasure lam] (a : ℝ)
    (h : lam {a}ᶜ = 0) : lam = Measure.dirac a := by
  ext s hs
  rw [Measure.dirac_apply' _ hs]
  by_cases ha : a ∈ s
  · rw [Set.indicator_of_mem ha]
    refine (prob_compl_eq_zero_iff hs).1 (measure_mono_null (fun x (hx : x ∈ sᶜ) => ?_) h)
    intro hxa; rw [Set.mem_singleton_iff.1 hxa] at hx; exact hx ha
  · rw [Set.indicator_of_notMem ha]
    refine measure_mono_null (fun x (hx : x ∈ s) => ?_) h
    intro hxa; rw [Set.mem_singleton_iff.1 hxa] at hx; exact ha hx

theorem pairLaw_ne_dirac (lam : Measure ℝ) [IsProbabilityMeasure lam]
    (h : ∀ a, lam ≠ Measure.dirac a) (p : ℝ × ℝ) : pairLaw lam ≠ Measure.dirac p := by
  intro hp
  obtain ⟨a, b⟩ := p
  have hd : ∀ c, lam {c} * lam {c} = Measure.dirac (a, b) {(c, c)} := fun c => by
    rw [← pairLaw_diag, hp]
  by_cases hab : a = b
  · subst hab
    have h1 : lam {a} * lam {a} = 1 := by rw [hd]; simp
    have h2 : lam {a} = 1 := by
      refine le_antisymm prob_le_one ?_
      calc (1 : ENNReal) = lam {a} * lam {a} := h1.symm
        _ ≤ lam {a} * 1 := by gcongr; exact prob_le_one
        _ = lam {a} := mul_one _
    exact h a (eq_dirac_of_compl lam a ((prob_compl_eq_zero_iff (measurableSet_singleton a)).2 h2))
  · have ha : lam {a} = 0 := by
      have := hd a
      rw [Measure.dirac_apply' _ (measurableSet_singleton _), Set.indicator_of_notMem
        (by simp [Ne.symm hab])] at this
      exact mul_self_eq_zero.1 this
    have hb : lam {b} = 0 := by
      have := hd b
      rw [Measure.dirac_apply' _ (measurableSet_singleton _), Set.indicator_of_notMem
        (by simp [hab])] at this
      exact mul_self_eq_zero.1 this
    have := pairLaw_singleton_le lam (a, b)
    rw [hp, ha, hb, Measure.dirac_apply_of_mem (Set.mem_singleton _)] at this
    simp at this

theorem pairLaw_singleton (lam : Measure ℝ) [IsProbabilityMeasure lam] (h : ∀ x, lam {x} = 0)
    (p : ℝ × ℝ) : pairLaw lam {p} = 0 :=
  nonpos_iff_eq_zero.1 ((pairLaw_singleton_le lam p).trans (by rw [h, h, add_zero]))

theorem prod_offDiag_ne_zero (lam : Measure ℝ) [IsProbabilityMeasure lam]
    (h : ∀ a, lam ≠ Measure.dirac a) : (lam.prod lam) {p : ℝ × ℝ | p.1 ≠ p.2} ≠ 0 := by
  intro H
  have hS : MeasurableSet {p : ℝ × ℝ | p.1 ≠ p.2} :=
    (measurableSet_eq_fun measurable_fst measurable_snd).compl
  rw [Measure.prod_apply hS, lintegral_eq_zero_iff (measurable_measure_prodMk_left hS)] at H
  obtain ⟨a, ha⟩ := H.exists
  refine h a (eq_dirac_of_compl lam a ?_)
  have : Prod.mk a ⁻¹' {p : ℝ × ℝ | p.1 ≠ p.2} = {a}ᶜ := by ext x; simp [eq_comm]
  rw [← this]; exact ha



/-! ### Auxiliary measure theory for the pairing lemma -/

theorem map_fiber {α β γ : Type} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure α) [IsProbabilityMeasure μ] (ν : Measure β) [SFinite ν] (ν' : Measure γ)
    [SFinite ν'] (g : α → β → γ) (hg : Measurable (Function.uncurry g))
    (h : ∀ a, ν.map (g a) = ν') : (μ.prod ν).map (fun p => g p.1 p.2) = ν' := by
  have hm := (MeasurePreserving.id μ).skew_product hg (ae_of_all _ h)
  calc (μ.prod ν).map (fun p => g p.1 p.2)
      = ((μ.prod ν).map (fun p => (id p.1, g p.1 p.2))).map Prod.snd := by
        rw [Measure.map_map measurable_snd hm.measurable]; rfl
    _ = ν' := by rw [hm.map_eq, Measure.map_snd_prod, measure_univ, one_smul]

theorem measurable_zmod2 {Y : Type} [MeasurableSpace Y] (h : ZMod 2 → Y) : Measurable h :=
  fun _ _ => DiscreteCoeff.discrete _

theorem zmod2_cases (d : ZMod 2) : d = 0 ∨ d = 1 := by revert d; decide

theorem map_add_uniformK (c : ZMod 2) :
    (uniformK (ZMod 2)).map (· + c) = uniformK (ZMod 2) := by
  rw [Measure.ext_iff_singleton]
  intro a
  rw [Measure.map_apply (measurable_zmod2 _) (DiscreteCoeff.discrete _)]
  have : (· + c) ⁻¹' ({a} : Set (ZMod 2)) = {a - c} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff]; exact eq_sub_iff_add_eq.symm
  rw [this]; simp [uniformK]

/-- Reindexing a product along `α × β ≃ ι`, then currying. -/
def reix {α β ι X : Type} [MeasurableSpace X] (e : α × β ≃ ι) : (ι → X) ≃ᵐ (α → β → X) :=
  (MeasurableEquiv.piCongrLeft (fun _ => X) e.symm).trans (MeasurableEquiv.curry α β X)

theorem reix_apply {α β ι X : Type} [MeasurableSpace X] (e : α × β ≃ ι) (x : ι → X) (a : α)
    (b : β) : reix e x a b = x (e (a, b)) := by
  simp [reix, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast,
    MeasurableEquiv.curry]

theorem reix_symm_apply {α β ι X : Type} [MeasurableSpace X] (e : α × β ≃ ι)
    (z : α → β → X) (a : α) (b : β) : (reix e).symm z (e (a, b)) = z a b := by
  have := congrFun (congrFun ((reix e).apply_symm_apply z) a) b
  rwa [reix_apply] at this

theorem mp_reix {α β ι X : Type} [MeasurableSpace X] (e : α × β ≃ ι) (ν : Measure X)
    [IsProbabilityMeasure ν] :
    MeasurePreserving (reix e) (Measure.infinitePi fun _ : ι => ν)
      (Measure.infinitePi fun _ : α => Measure.infinitePi fun _ : β => ν) := by
  refine ⟨(reix e).measurable, ?_⟩
  have h1 := Measure.infinitePi_map_piCongrLeft (fun _ : α × β => ν) e.symm
  have h2 := Measure.infinitePi_map_curry (fun (_ : α) (_ : β) => ν)
  rw [show (reix e : (ι → X) → (α → β → X)) = MeasurableEquiv.curry α β X ∘
      MeasurableEquiv.piCongrLeft (fun _ => X) e.symm from rfl,
    ← Measure.map_map (MeasurableEquiv.measurable _) (MeasurableEquiv.measurable _), h1]
  exact h2

open Classical in
/-- Ordering a pair by a bit: `((a, b), 1) ↦ (a, b)` and `((a, b), 0) ↦ (b, a)`. -/
def phiPair (x : (ℝ × ℝ) × ZMod 2) : ℝ × ℝ := if x.2 = 1 then x.1 else x.1.swap

theorem measurable_phiPair : Measurable phiPair :=
  Measurable.ite (p := {x : (ℝ × ℝ) × ZMod 2 | x.2 = 1})
    (measurable_snd (DiscreteCoeff.discrete {1})) measurable_fst
    (measurable_swap.comp measurable_fst)

theorem map_phiPair_prod (lam : Measure ℝ) [IsProbabilityMeasure lam] :
    ((lam.prod lam).prod (uniformK (ZMod 2))).map phiPair = lam.prod lam := by
  classical
  rw [← Measure.prod_swap (μ := uniformK (ZMod 2)),
    Measure.map_map measurable_phiPair measurable_swap]
  refine map_fiber (uniformK (ZMod 2)) (lam.prod lam) (lam.prod lam)
    (fun d p => if d = 1 then p else p.swap) ?_ ?_
  · exact Measurable.ite (p := {x : ZMod 2 × (ℝ × ℝ) | x.1 = 1})
      (measurable_fst (DiscreteCoeff.discrete {1})) measurable_snd
      (measurable_swap.comp measurable_snd)
  · intro d
    by_cases hd : d = 1
    · simp [hd]
    · simp only [hd, ite_false]; exact Measure.prod_swap

theorem map_phiPair_pairLaw (lam : Measure ℝ) [IsProbabilityMeasure lam] :
    ((pairLaw lam).prod (uniformK (ZMod 2))).map phiPair = lam.prod lam := by
  classical
  have hρm : Measurable (Function.uncurry fun (x : ℝ × ℝ) (d : ZMod 2) =>
      if x.1 ≤ x.2 then d else d + 1) :=
    Measurable.ite (p := {x : (ℝ × ℝ) × ZMod 2 | x.1.1 ≤ x.1.2})
      (measurableSet_le (measurable_fst.comp measurable_fst) (measurable_snd.comp measurable_fst))
      measurable_snd ((measurable_zmod2 (fun d : ZMod 2 => d + 1)).comp measurable_snd)
  have hρ := (MeasurePreserving.id (lam.prod lam)).skew_product
    (μc := uniformK (ZMod 2)) (μd := uniformK (ZMod 2)) hρm (ae_of_all _ fun x => by
      by_cases hx : x.1 ≤ x.2
      · simp [hx]
      · simp only [hx, ite_false]; exact map_add_uniformK 1)
  calc ((pairLaw lam).prod (uniformK (ZMod 2))).map phiPair
      = (((lam.prod lam).prod (uniformK (ZMod 2))).map (Prod.map
          (fun p : ℝ × ℝ => (min p.1 p.2, max p.1 p.2)) id)).map phiPair := by
        rw [← Measure.map_prod_map _ _ measurable_sort measurable_id, Measure.map_id]; rfl
    _ = (((lam.prod lam).prod (uniformK (ZMod 2))).map _).map (phiPair ∘ Prod.map
          (fun p : ℝ × ℝ => (min p.1 p.2, max p.1 p.2)) id) := by
        rw [hρ.map_eq, Measure.map_map measurable_phiPair (measurable_sort.prodMap measurable_id)]
    _ = ((lam.prod lam).prod (uniformK (ZMod 2))).map phiPair := by
        rw [Measure.map_map (measurable_phiPair.comp (measurable_sort.prodMap measurable_id))
          hρ.measurable]
        congr 1
        funext ⟨⟨a, b⟩, d⟩
        rcases le_or_gt a b with hab | hab
        · simp [phiPair, hab]
        · rcases zmod2_cases d with rfl | rfl
          · simp [phiPair, not_le.2 hab, min_eq_right hab.le, max_eq_left hab.le]
          · simp [phiPair, not_le.2 hab, min_eq_right hab.le, max_eq_left hab.le,
              show (1 : ZMod 2) + 1 = 0 from rfl]
    _ = lam.prod lam := map_phiPair_prod lam

end Collapse
