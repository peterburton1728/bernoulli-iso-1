module

public import Collapse.Bernoulli
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Probability.CDF
public import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal

/-!
# Atomless standard probability spaces

The classical isomorphism theorem for atomless standard probability spaces:
two standard probability spaces without atoms are isomorphic modulo null sets. The proof goes
through Lebesgue measure on `[0,1]` by the distribution function of an embedding in `ℝ`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory

namespace Collapse

/-- Lebesgue measure on `[0,1]`, as a measure on `ℝ`. -/
def lebI : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1)

instance lebI_isProbabilityMeasure : IsProbabilityMeasure lebI :=
  ⟨by simp [lebI, Measure.restrict_apply MeasurableSet.univ, Real.volume_Icc]⟩

theorem lebI_singleton (x : ℝ) : lebI {x} = 0 :=
  by rw [lebI, Measure.restrict_apply (measurableSet_singleton x)]
     exact measure_mono_null Set.inter_subset_left Real.volume_singleton

open ProbabilityTheory Filter Topology in
/-- The distribution function of an atomless probability measure on `ℝ` is continuous. -/
theorem continuous_cdf_of_noAtoms (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h : ∀ a, ν {a} = 0) : Continuous (cdf ν) := by
  refine continuous_iff_continuousAt.2 fun a => ?_
  rw [(cdf ν).mono.continuousAt_iff_leftLim_eq_rightLim, (cdf ν).rightLim_eq]
  have h1 := (cdf ν).measure_singleton a
  rw [measure_cdf, h a] at h1
  have h2 : cdf ν a - Function.leftLim (cdf ν) a ≤ 0 := ENNReal.ofReal_eq_zero.1 h1.symm
  exact le_antisymm ((cdf ν).mono.leftLim_le le_rfl) (by linarith)

open ProbabilityTheory Filter Topology in
/-- The image of an atomless probability measure on `ℝ` by its distribution function. -/
theorem map_cdf_eq_lebI (ν : Measure ℝ) [IsProbabilityMeasure ν] (hc : Continuous (cdf ν)) :
    ν.map (cdf ν) = lebI := by
  refine Measure.ext_of_Iic _ _ fun t => ?_
  rw [Measure.map_apply hc.measurable measurableSet_Iic, lebI,
    Measure.restrict_apply measurableSet_Iic]
  rcases lt_or_ge t 0 with ht0 | ht0
  · have e1 : cdf ν ⁻¹' Set.Iic t = ∅ := Set.eq_empty_of_forall_notMem fun x hx =>
      absurd ((cdf_nonneg ν x).trans hx) (not_le.2 ht0)
    have e2 : Set.Iic t ∩ Set.Icc 0 1 = ∅ := Set.eq_empty_of_forall_notMem fun x hx =>
      absurd (hx.2.1.trans hx.1) (not_le.2 ht0)
    simp [e1, e2]
  rcases le_or_gt 1 t with ht1 | ht1
  · have e1 : cdf ν ⁻¹' Set.Iic t = Set.univ :=
      Set.eq_univ_of_forall fun x => (cdf_le_one ν x).trans ht1
    have e2 : Set.Iic t ∩ Set.Icc 0 1 = Set.Icc 0 1 :=
      Set.inter_eq_right.2 fun x hx => hx.2.trans ht1
    simp [e1, e2, Real.volume_Icc]
  have e2 : Set.Iic t ∩ Set.Icc 0 1 = Set.Icc 0 t := by
    ext x; simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
    constructor
    · rintro ⟨h1, h2, -⟩; exact ⟨h2, h1⟩
    · rintro ⟨h1, h2⟩; exact ⟨h2, h1, by linarith⟩
  rw [e2, Real.volume_Icc, sub_zero]
  set S := cdf ν ⁻¹' Set.Iic t with hS
  rcases S.eq_empty_or_nonempty with hE | hne
  · have : t ≤ 0 := by
      by_contra hpos
      obtain ⟨x, hx⟩ := (tendsto_cdf_atBot (μ := ν)).eventually (gt_mem_nhds (not_le.1 hpos))
        |>.exists
      have : x ∈ S := show cdf ν x ≤ t from hx.le
      simp [hE] at this
    rw [hE, measure_empty, ENNReal.ofReal_of_nonpos this]
  obtain ⟨b, hb⟩ := ((tendsto_cdf_atTop (μ := ν)).eventually (lt_mem_nhds ht1)).exists_forall_of_atTop
  have hbdd : BddAbove S := ⟨b, fun x hx => by
    by_contra hxb
    exact absurd (hb x (not_le.1 hxb).le) (not_lt.2 hx)⟩
  have hcl : IsClosed S := isClosed_le hc continuous_const
  have hmem : sSup S ∈ S := hcl.csSup_mem hne hbdd
  have hSeq : S = Set.Iic (sSup S) := by
    ext x
    exact ⟨fun hx => le_csSup hbdd hx, fun hx => ((cdf ν).mono hx).trans hmem⟩
  have hval : cdf ν (sSup S) = t := by
    refine le_antisymm hmem (not_lt.1 fun hlt => ?_)
    have hev : ∀ᶠ x in 𝓝[>] (sSup S), cdf ν x < t :=
      nhdsWithin_le_nhds ((hc.tendsto _).eventually (gt_mem_nhds hlt))
    obtain ⟨x, hx1, hx2⟩ := (hev.and self_mem_nhdsWithin).exists
    exact absurd (le_csSup hbdd (show cdf ν x ≤ t from hx1.le)) (not_le.2 hx2)
  rw [hSeq, ← ofReal_cdf, hval]

/-- A standard probability space without atoms is isomorphic to `[0,1]` modulo null sets. -/
theorem aeIso_lebI {X : Type} [MeasurableSpace X] [StandardBorelSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] (hμ : ∀ x, μ {x} = 0) : AEIso μ lebI := by
  classical
  set φ := embeddingReal X
  have hφ : MeasurableEmbedding φ := measurableEmbedding_embeddingReal X
  set ν := μ.map φ
  have : IsProbabilityMeasure ν :=
    ⟨by rw [Measure.map_apply hφ.measurable MeasurableSet.univ]; simp⟩
  have hν : ∀ a, ν {a} = 0 := by
    intro a
    rw [Measure.map_apply hφ.measurable (measurableSet_singleton a)]
    by_cases ha : a ∈ Set.range φ
    · obtain ⟨x, rfl⟩ := ha
      have : φ ⁻¹' {φ x} = {x} := by
        ext y; simp only [Set.mem_preimage, Set.mem_singleton_iff]; exact hφ.injective.eq_iff
      rw [this, hμ]
    · have : φ ⁻¹' {a} = ∅ := Set.eq_empty_of_forall_notMem fun y hy => ha ⟨y, hy⟩
      rw [this, measure_empty]
  set F := ProbabilityTheory.cdf ν
  have hc : Continuous F := continuous_cdf_of_noAtoms ν hν
  set T₀ : Set ℝ := {t | ∃ x y, x < y ∧ F x = t ∧ F y = t}
  have hT : T₀.Countable := by
    refine (Set.countable_range fun q : ℚ => F q).mono ?_
    rintro t ⟨x, y, hxy, hx, hy⟩
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hxy
    exact ⟨q, le_antisymm (hy ▸ F.mono hq2.le) (hx ▸ F.mono hq1.le)⟩
  have hTm : MeasurableSet T₀ := hT.measurableSet
  have hT0 : lebI T₀ = 0 :=
    le_antisymm ((Measure.le_iff'.1 Measure.restrict_le_self T₀).trans
      (hT.measure_zero volume).le) bot_le
  set ψ : X → ℝ := fun x => F (φ x)
  have hψm : Measurable ψ := hc.measurable.comp hφ.measurable
  have hψ : MeasurePreserving ψ μ lebI := ⟨hψm, by
    rw [← map_cdf_eq_lebI ν hc, Measure.map_map hc.measurable hφ.measurable]; rfl⟩
  set s : Set X := ψ ⁻¹' T₀ᶜ
  have hs : MeasurableSet s := hψm hTm.compl
  have hsc : ∀ᵐ x ∂μ, x ∈ s := by
    refine ae_iff.2 ?_
    simp only [s, Set.mem_preimage, Set.mem_compl_iff, not_not]
    exact (hψ.measure_preimage hTm.nullMeasurableSet).trans hT0
  have hinj : Set.InjOn ψ s := by
    intro x hx y _ hxy
    refine hφ.injective ?_
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact hx ⟨_, _, h, rfl, hxy.symm⟩
    · exact hx ⟨_, _, h, hxy.symm, rfl⟩
  have := hs.standardBorel
  set ψs : s → ℝ := fun x => ψ x.1
  have he : MeasurableEmbedding ψs :=
    (hψm.comp measurable_subtype_coe).measurableEmbedding fun x y h => Subtype.ext (hinj x.2 y.2 h)
  have hne : Nonempty s := by
    obtain ⟨x, hx⟩ := hsc.exists
    exact ⟨⟨x, hx⟩⟩
  obtain ⟨g', hg', hgf⟩ := he.exists_measurable_extend measurable_id fun _ => hne
  have ht := he.measurableSet_range
  have htc : ∀ᵐ y ∂lebI, y ∈ Set.range ψs := by
    rw [← hψ.map_eq]
    exact (ae_map_iff hψm.aemeasurable ht).2 (hsc.mono fun x hx => ⟨⟨x, hx⟩, rfl⟩)
  refine AEIso.of_global hs ht hsc htc hψ (measurable_subtype_coe.comp hg')
    (fun x hx => ⟨⟨x, hx⟩, rfl⟩) (fun y _ => (g' y).2)
    (fun x hx => congrArg Subtype.val (congrFun hgf ⟨x, hx⟩)) ?_
  rintro _ ⟨x, rfl⟩
  exact congrArg ψs (congrFun hgf x)

/-- Two standard probability spaces without atoms are isomorphic modulo null sets. -/
theorem aeIso_of_noAtoms {X Y : Type} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace Y] [StandardBorelSpace Y] (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hμ : ∀ x, μ {x} = 0)
    (hν : ∀ y, ν {y} = 0) : AEIso μ ν :=
  (aeIso_lebI μ hμ).trans (aeIso_lebI ν hν).symm

/-- A product with a space without atoms has no atoms. -/
theorem prod_singleton_of_right {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSingletonClass X] [MeasurableSingletonClass Y] (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hν : ∀ y, ν {y} = 0) (p : X × Y) :
    (μ.prod ν) {p} = 0 := by
  have : ({p} : Set (X × Y)) = {p.1} ×ˢ {p.2} := by simp
  rw [this, Measure.prod_prod, hν, mul_zero]

end Collapse
