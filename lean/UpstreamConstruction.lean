module

public import UpstreamFoundation

-- Lean's supported migration option exports generated private simp helpers.
set_option backward.privateInPublic true

@[expose] public section

/- BEGIN PINNED MODULE OAI.RingTheory.DirectFiniteness.SlabAvoidance -/
section

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace KaplanskyCounterexample.FiniteLocalLemma

variable {Ω : Type u_1} {ι : Type u_2}

/-- Avoid a finite list of bad events. -/
def avoid (E : ι → Set Ω) (s : Finset ι) : Set Ω := ⋂ i ∈ s, (E i)ᶜ

@[simp] lemma mem_avoid {E : ι → Set Ω} {s : Finset ι} {ω : Ω} :
    ω ∈ avoid E s ↔ ∀ i ∈ s, ω ∉ E i := by simp [avoid]

@[simp] lemma avoid_empty (E : ι → Set Ω) : avoid E ∅ = Set.univ := by
  simp [avoid]

variable [DecidableEq ι]

lemma avoid_insert (E : ι → Set Ω) (s : Finset ι) (i : ι) :
    avoid E (insert i s) = avoid E s \ E i := by
  ext ω
  simp only [mem_avoid, Finset.mem_insert, forall_eq_or_imp, mem_sdiff]
  tauto

lemma avoid_union (E : ι → Set Ω) (s t : Finset ι) :
    avoid E (s ∪ t) = avoid E s ∩ avoid E t := by
  ext ω
  simp only [mem_avoid, Finset.mem_union, mem_inter_iff, or_imp, forall_and]

omit [DecidableEq ι] in
lemma avoid_anti (E : ι → Set Ω) {s t : Finset ι} (h : s ⊆ t) :
    avoid E t ⊆ avoid E s := by
  intro ω hω
  exact mem_avoid.mpr fun i hi => mem_avoid.mp hω i (h hi)

variable [MeasurableSpace Ω]

omit [DecidableEq ι] in
lemma measurable_avoid {E : ι → Set Ω} (hE : ∀ i, MeasurableSet (E i))
    (s : Finset ι) : MeasurableSet (avoid E s) :=
  s.measurableSet_biInter fun i _ => (hE i).compl

variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {E : ι → Set Ω}

lemma prob_avoid_insert (hE : ∀ i, MeasurableSet (E i)) (s : Finset ι) (i : ι) :
    μ.real (avoid E (insert i s)) =
      μ.real (avoid E s) - μ.real (E i ∩ avoid E s) := by
  rw [avoid_insert]
  have h := measureReal_inter_add_sdiff (μ := μ) (s := avoid E s) (hE i)
  rw [Set.inter_comm (avoid E s) (E i)] at h
  linarith

/-- Successive avoidance bounds, in multiplication form (no conditional measure
or division by a possibly zero probability). -/
lemma avoid_union_lower {x : ι → ℝ} (hE : ∀ i, MeasurableSet (E i))
    (hx : ∀ i, 0 ≤ 1 - x i) (s t : Finset ι) (hd : Disjoint s t)
    (hc : ∀ (u : Finset ι), u ⊆ s ∪ t → ∀ i ∈ t, i ∉ u →
      μ.real (E i ∩ avoid E u) ≤ x i * μ.real (avoid E u)) :
    (∏ i ∈ t, (1 - x i)) * μ.real (avoid E s) ≤ μ.real (avoid E (s ∪ t)) := by
  induction t using Finset.induction_on with
  | empty => simp
  | @insert i t hi ih =>
    have hdst : Disjoint s t := hd.mono_right (Finset.subset_insert _ _)
    have his : i ∉ s := fun his => Finset.disjoint_left.mp hd his (Finset.mem_insert_self _ _)
    have hit : i ∉ s ∪ t := by simp [his, hi]
    have hsub : s ∪ t ⊆ s ∪ insert i t :=
      Finset.union_subset_union_right (Finset.subset_insert _ _)
    have hct : ∀ u : Finset ι, u ⊆ s ∪ t → ∀ j ∈ t, j ∉ u →
        μ.real (E j ∩ avoid E u) ≤ x j * μ.real (avoid E u) := by
      intro u hu j hj hju
      exact hc u (hu.trans hsub) j (Finset.mem_insert_of_mem hj) hju
    have hlower := ih hdst hct
    have hlast := hc (s ∪ t) hsub i (Finset.mem_insert_self _ _) hit
    rw [Finset.prod_insert hi, mul_assoc]
    calc
      (1 - x i) * ((∏ j ∈ t, (1 - x j)) * μ.real (avoid E s))
          ≤ (1 - x i) * μ.real (avoid E (s ∪ t)) :=
        mul_le_mul_of_nonneg_left hlower (hx i)
      _ ≤ μ.real (avoid E (s ∪ insert i t)) := by
        rw [Finset.union_insert, prob_avoid_insert hE]
        nlinarith

/-- Product-form asymmetric Lovász local lemma on a finite event list.
The independence hypothesis is the usual independence from all non-neighbors
jointly, written directly as an equality of real probabilities. -/
theorem asymmetric {x : ι → ℝ} (hE : ∀ i, MeasurableSet (E i))
    (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i < 1)
    (Γ : ι → Finset ι)
    (hind : ∀ i (s : Finset ι), i ∉ s → Disjoint s (Γ i) →
      μ.real (E i ∩ avoid E s) = μ.real (E i) * μ.real (avoid E s))
    (hprob : ∀ i, μ.real (E i) ≤ x i * ∏ j ∈ Γ i, (1 - x j)) :
    ∀ s : Finset ι, 0 < μ.real (avoid E s) ∧
      ∀ i ∉ s, μ.real (E i ∩ avoid E s) ≤ x i * μ.real (avoid E s) := by
  intro s
  induction s using Finset.strongInductionOn with | _ s ih
  have hxp : ∀ i, 0 < 1 - x i := fun i => sub_pos.mpr (hx1 i)
  have hxn : ∀ i, 0 ≤ 1 - x i := fun i => (hxp i).le
  have hpos : 0 < μ.real (avoid E s) := by
    by_cases hs : s = ∅
    · simp [hs, probReal_univ]
    · obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hs
      have ht : s.erase i ⊂ s := Finset.erase_ssubset hi
      obtain ⟨hprev, hcond⟩ := ih (s.erase i) ht
      have hc := hcond i (Finset.notMem_erase i s)
      have hins : insert i (s.erase i) = s := Finset.insert_erase hi
      rw [← hins, prob_avoid_insert hE]
      have hm := mul_pos (hxp i) hprev
      nlinarith
  refine ⟨hpos, ?_⟩
  intro i his
  let t := s \ Γ i
  let u := s ∩ Γ i
  have hts : t ⊆ s := Finset.sdiff_subset
  have hus : u ⊆ s := Finset.inter_subset_left
  have htu : Disjoint t u := by
    apply Finset.disjoint_left.mpr
    intro j hjt hju
    exact (Finset.mem_sdiff.mp hjt).2 (Finset.mem_inter.mp hju).2
  have hsu : t ∪ u = s := by
    ext j
    simp only [t, u, Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
    tauto
  have htg : Disjoint t (Γ i) := by
    apply Finset.disjoint_left.mpr
    intro j hjt hjg
    exact (Finset.mem_sdiff.mp hjt).2 hjg
  have hit : i ∉ t := fun h => his (hts h)
  have heq := hind i t hit htg
  have hnum : μ.real (E i ∩ avoid E s) ≤ μ.real (E i) * μ.real (avoid E t) := by
    rw [← heq]
    exact measureReal_mono (Set.inter_subset_inter_right _ (avoid_anti E hts))
  have hchain : (∏ j ∈ u, (1 - x j)) * μ.real (avoid E t) ≤ μ.real (avoid E s) := by
    rw [← hsu]
    apply avoid_union_lower hE hxn t u htu
    intro v hv j hju hjv
    have hvs : v ⊂ s := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
      · simpa [hsu] using hv
      · intro he
        exact hjv (he.symm ▸ hus hju)
    exact (ih v hvs).2 j hjv
  have hprod : (∏ j ∈ Γ i, (1 - x j)) ≤ ∏ j ∈ u, (1 - x j) := by
    apply Finset.prod_le_prod_of_subset_of_le_one₀ Finset.inter_subset_right
    · intro j _; exact hxn j
    · intro j _ _; linarith [hx0 j]
  calc
    μ.real (E i ∩ avoid E s) ≤ μ.real (E i) * μ.real (avoid E t) := hnum
    _ ≤ (x i * ∏ j ∈ u, (1 - x j)) * μ.real (avoid E t) := by
      apply mul_le_mul_of_nonneg_right _ measureReal_nonneg
      exact (hprob i).trans (mul_le_mul_of_nonneg_left hprod (hx0 i))
    _ = x i * ((∏ j ∈ u, (1 - x j)) * μ.real (avoid E t)) := mul_assoc _ _ _
    _ ≤ x i * μ.real (avoid E s) := mul_le_mul_of_nonneg_left hchain (hx0 i)

/-- The elementary product bound used in the weighted local lemma. -/
lemma one_sub_sum_le_prod {x : ι → ℝ} (hx0 : ∀ i, 0 ≤ x i)
    (hx1 : ∀ i, x i ≤ 1) (s : Finset ι) :
    1 - ∑ i ∈ s, x i ≤ ∏ i ∈ s, (1 - x i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    have hsum : 0 ≤ ∑ j ∈ s, x j := Finset.sum_nonneg fun j _ => hx0 j
    have hm := mul_nonneg (hx0 i) hsum
    have hp := mul_le_mul_of_nonneg_left ih (sub_nonneg.mpr (hx1 i))
    nlinarith

section Weighted
variable {κ : Type u_3} [DecidableEq κ] [Fintype ι]

/-- The dependency graph obtained by sharing one of the assigned variables. -/
def neighbors (deps : ι → Finset κ) (i : ι) : Finset ι :=
  Finset.univ.filter fun j => j ≠ i ∧ ¬Disjoint (deps i) (deps j)

/-- Total event weight at a random variable. -/
def load (deps : ι → Finset κ) (w : ι → ℝ) (v : κ) : ℝ :=
  ∑ i, if v ∈ deps i then w i else 0

omit [DecidableEq ι] in
lemma weight_le_load (deps : ι → Finset κ) {w : ι → ℝ}
    (hw : ∀ i, 0 ≤ w i) {i : ι} {v : κ} (hv : v ∈ deps i) :
    w i ≤ load deps w v := by
  have h := Finset.single_le_sum (s := Finset.univ)
    (f := fun j => if v ∈ deps j then w j else 0)
    (fun j _ => by split_ifs; exact hw j; exact le_rfl) (Finset.mem_univ i)
  simpa [load, hv] using h

lemma neighbor_weight_le_loads (deps : ι → Finset κ) {w : ι → ℝ}
    (hw : ∀ i, 0 ≤ w i) (i : ι) :
    ∑ j ∈ neighbors deps i, w j ≤ ∑ v ∈ deps i, load deps w v := by
  calc
    ∑ j ∈ neighbors deps i, w j
      ≤ ∑ j ∈ neighbors deps i, ∑ v ∈ deps i, if v ∈ deps j then w j else 0 := by
        apply Finset.sum_le_sum
        intro j hj
        have hnd := (Finset.mem_filter.mp hj).2.2
        obtain ⟨v, hvi, hvj⟩ := Finset.not_disjoint_iff.mp hnd
        have hh := Finset.single_le_sum (s := deps i)
          (f := fun v => if v ∈ deps j then w j else 0)
          (fun v _ => by split_ifs; exact hw j; exact le_rfl) hvi
        simpa [hvj] using hh
    _ ≤ ∑ j : ι, ∑ v ∈ deps i, if v ∈ deps j then w j else 0 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        intro j _ _
        exact Finset.sum_nonneg fun v _ => by split_ifs; exact hw j; exact le_rfl
    _ = ∑ v ∈ deps i, load deps w v := by rw [Finset.sum_comm]; rfl

theorem weighted_four (hE : ∀ i, MeasurableSet (E i))
    (deps : ι → Finset κ) (hne : ∀ i, (deps i).Nonempty)
    (hcard : ∀ i, (deps i).card ≤ 4)
    (hload : ∀ v, load deps (fun i => μ.real (E i)) v ≤ 1 / 16)
    (hind : ∀ i (s : Finset ι), i ∉ s → Disjoint s (neighbors deps i) →
      μ.real (E i ∩ avoid E s) = μ.real (E i) * μ.real (avoid E s)) :
    0 < μ.real (avoid E Finset.univ) ∧ ∃ ω : Ω, ∀ i, ω ∉ E i := by
  let p : ι → ℝ := fun i => μ.real (E i)
  let x : ι → ℝ := fun i => 2 * p i
  have hp : ∀ i, 0 ≤ p i := fun _ => measureReal_nonneg
  have hpbound : ∀ i, p i ≤ 1 / 16 := by
    intro i
    obtain ⟨v, hv⟩ := hne i
    exact (weight_le_load deps hp hv).trans (hload v)
  have hx0 : ∀ i, 0 ≤ x i := fun i => mul_nonneg (by norm_num) (hp i)
  have hx1 : ∀ i, x i < 1 := by intro i; dsimp [x]; linarith [hpbound i]
  have hsum : ∀ i, ∑ j ∈ neighbors deps i, x j ≤ 1 / 2 := by
    intro i
    have hweights := neighbor_weight_le_loads deps hp i
    have hloads : (∑ v ∈ deps i, load deps p v) ≤ (deps i).card * (1 / 16 : ℝ) := by
      calc
        ∑ v ∈ deps i, load deps p v ≤ ∑ v ∈ deps i, (1 / 16 : ℝ) :=
          Finset.sum_le_sum fun v _ => hload v
        _ = _ := by simp
    have hcnt : ((deps i).card : ℝ) ≤ 4 := by exact_mod_cast hcard i
    simp only [x, ← Finset.mul_sum]
    nlinarith
  have hprob : ∀ i, μ.real (E i) ≤ x i * ∏ j ∈ neighbors deps i, (1 - x j) := by
    intro i
    have hprod := one_sub_sum_le_prod hx0 (fun j => (hx1 j).le) (neighbors deps i)
    have hhalf : (1 / 2 : ℝ) ≤ ∏ j ∈ neighbors deps i, (1 - x j) := by
      linarith [hsum i]
    have hm := mul_le_mul_of_nonneg_left hhalf (hx0 i)
    dsimp [x, p] at hm
    nlinarith
  have hh := (asymmetric hE hx0 hx1 (neighbors deps) hind hprob Finset.univ).1
  refine ⟨hh, ?_⟩
  have hset : (avoid E Finset.univ).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty.mp h, measureReal_empty] at hh
    exact lt_irrefl 0 hh
  obtain ⟨ω, hω⟩ := hset
  exact ⟨ω, fun i => mem_avoid.mp hω i (Finset.mem_univ i)⟩

end Weighted

section IndependentVariables
variable {κ : Type u_4} {β : Type u_5} [DecidableEq κ]

/-- An event is determined by a finite set of coordinates. -/
def DeterminedBy (f : κ → Ω → β) (s : Finset κ) (A : Set Ω) : Prop :=
  ∀ ω ω', (∀ v ∈ s, f v ω = f v ω') → (ω ∈ A ↔ ω' ∈ A)

omit [MeasurableSpace Ω] [DecidableEq κ] in
lemma preimage_image_of_determined {f : κ → Ω → β} {s : Finset κ} {A : Set Ω}
    (h : DeterminedBy f s A) :
    (fun ω (v : s) => f v ω) ⁻¹' ((fun ω (v : s) => f v ω) '' A) = A := by
  ext ω
  constructor
  · rintro ⟨ω', hω', heq⟩
    exact (h ω' ω (fun v hv => congrFun heq ⟨v, hv⟩)).mp hω'
  · intro hω
    exact ⟨ω, hω, rfl⟩

omit [DecidableEq ι] [MeasurableSpace Ω] in
lemma determined_avoid {f : κ → Ω → β} (deps : ι → Finset κ)
    (hdep : ∀ i, DeterminedBy f (deps i) (E i)) (s : Finset ι) :
    DeterminedBy f (s.biUnion deps) (avoid E s) := by
  intro ω ω' hω
  simp only [mem_avoid]
  have heq : ∀ i ∈ s, (ω ∈ E i ↔ ω' ∈ E i) := by
    intro i hi
    exact hdep i ω ω' fun v hv => hω v (Finset.mem_biUnion.mpr ⟨i, hi, hv⟩)
  exact ⟨fun h i hi => (heq i hi).not.mp (h i hi),
    fun h i hi => (heq i hi).not.mpr (h i hi)⟩

variable [MeasurableSpace β] [MeasurableSingletonClass β] [Finite β]

omit [DecidableEq κ] in
lemma measurable_of_determined {f : κ → Ω → β} (hf : ∀ v, Measurable (f v))
    {s : Finset κ} {A : Set Ω} (h : DeterminedBy f s A) : MeasurableSet A := by
  rw [← preimage_image_of_determined h]
  apply MeasurableSet.preimage
  · exact (Set.toFinite _).countable.measurableSet
  · exact Measurable.of_eval fun v => hf v

omit [IsProbabilityMeasure μ] in
lemma independent_of_non_neighbors [Fintype ι] {f : κ → Ω → β}
    (hf : ∀ v, Measurable (f v)) (hf_ind : iIndepFun f μ)
    (deps : ι → Finset κ) (hdep : ∀ i, DeterminedBy f (deps i) (E i))
    (i : ι) (s : Finset ι) (his : i ∉ s) (hd : Disjoint s (neighbors deps i)) :
    μ.real (E i ∩ avoid E s) = μ.real (E i) * μ.real (avoid E s) := by
  have hdv : Disjoint (deps i) (s.biUnion deps) := by
    apply Finset.disjoint_left.mpr
    intro v hvi hvs
    obtain ⟨j, hjs, hvj⟩ := Finset.mem_biUnion.mp hvs
    have hji : j ≠ i := by intro h; exact his (h ▸ hjs)
    have hjn : j ∈ neighbors deps i := by
      simp only [neighbors, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hji, Finset.not_disjoint_iff.mpr ⟨v, hvi, hvj⟩⟩
    exact Finset.disjoint_left.mp hd hjs hjn
  have hp := hf_ind.indepFun_finset (deps i) (s.biUnion deps) hdv hf
  have heq := hp.measure_inter_preimage_eq_mul
    ((fun ω (v : deps i) => f v ω) '' E i)
    ((fun ω (v : s.biUnion deps) => f v ω) '' avoid E s)
    ((Set.toFinite _).countable.measurableSet)
    ((Set.toFinite _).countable.measurableSet)
  rw [preimage_image_of_determined (hdep i),
    preimage_image_of_determined (determined_avoid deps hdep s)] at heq
  simpa only [Measure.real, ENNReal.toReal_mul] using congrArg ENNReal.toReal heq

theorem weighted_four_independent [Fintype ι] {f : κ → Ω → β}
    (hf : ∀ v, Measurable (f v)) (hf_ind : iIndepFun f μ)
    (deps : ι → Finset κ) (hdep : ∀ i, DeterminedBy f (deps i) (E i))
    (hne : ∀ i, (deps i).Nonempty) (hcard : ∀ i, (deps i).card ≤ 4)
    (hload : ∀ v, load deps (fun i => μ.real (E i)) v ≤ 1 / 16) :
    0 < μ.real (avoid E Finset.univ) ∧ ∃ ω : Ω, ∀ i, ω ∉ E i := by
  apply weighted_four (fun i => measurable_of_determined hf (hdep i)) deps hne hcard hload
  exact independent_of_non_neighbors hf hf_ind deps hdep

end IndependentVariables

end KaplanskyCounterexample.FiniteLocalLemma

noncomputable section
open scoped Classical
namespace KaplanskyCounterexample.FiniteGeometry
open Module MeasureTheory

variable {Q : Type u_6} {E : Type u_7} [Field Q] [AddCommGroup E] [Module Q E]

/-- Transitivity on nonzero vectors, proved by extending an isomorphism of
one-dimensional subspaces. -/
theorem exists_linearEquiv_apply_eq {x y : E} (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ g : E ≃ₗ[Q] E, g x = y := by
  let ex := LinearEquiv.toSpanNonzeroSingleton Q E x hx
  let ey := LinearEquiv.toSpanNonzeroSingleton Q E y hy
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq (ex.symm.trans ey)
  refine ⟨g, ?_⟩
  have h := hg (ex 1)
  rw [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply] at h
  simpa [ex, ey] using h.symm

abbrev Plane (Q : Type u_8) (E : Type u_9) [Field Q] [AddCommGroup E] [Module Q E] :=
  {P : Submodule Q E // finrank Q P = 2}

instance [Finite E] : Finite (Plane Q E) := by
  unfold Plane
  infer_instance

instance [Fintype E] : Fintype (Plane Q E) := Fintype.ofFinite _

local instance identityRingHomSurjective : RingHomSurjective (RingHom.id Q) := inferInstance

/-- An ambient automorphism permutes the plane sample space. -/
def mapPlane (g : E ≃ₗ[Q] E) : Plane Q E ≃ Plane Q E where
  toFun P := ⟨P.val.map g.toLinearMap, by rw [g.finrank_map_eq]; exact P.property⟩
  invFun P := ⟨P.val.map g.symm.toLinearMap, by rw [g.symm.finrank_map_eq]; exact P.property⟩
  left_inv P := by
    apply Subtype.ext
    ext x
    simp
  right_inv P := by
    apply Subtype.ext
    ext x
    simp

@[simp] theorem mem_mapPlane (g : E ≃ₗ[Q] E) (P : Plane Q E) (x : E) :
    g x ∈ (mapPlane g P).val ↔ x ∈ P.val := by
  change g x ∈ P.val.map g.toLinearMap ↔ x ∈ P.val
  simp

/-- The number of planes through a nonzero vector is independent of it. -/
def planesThroughEquiv {x y : E} (g : E ≃ₗ[Q] E) (h : g x = y) :
    {P : Plane Q E // x ∈ P.val} ≃ {P : Plane Q E // y ∈ P.val} where
  toFun P := ⟨mapPlane g P.val, by rw [← h, mem_mapPlane]; exact P.property⟩
  invFun P := ⟨mapPlane g.symm P.val, by
    have hg : g.symm y = x := by rw [← h]; simp
    rw [← hg, mem_mapPlane]; exact P.property⟩
  left_inv P := by
    apply Subtype.ext
    apply Subtype.ext
    change (P.val.val.map g.toLinearMap).map g.symm.toLinearMap = P.val.val
    ext x
    simp
  right_inv P := by
    apply Subtype.ext
    apply Subtype.ext
    change (P.val.val.map g.symm.toLinearMap).map g.toLinearMap = P.val.val
    ext x
    simp

variable [Fintype Q] [Fintype E]

/-- Nonzero elements of a plane are precisely its ambient nonzero vectors. -/
def planeNonzeroEquiv (P : Plane Q E) :
    {x : P.val // x ≠ 0} ≃ {x : {x : E // x ≠ 0} // x.val ∈ P.val} where
  toFun x := ⟨⟨x.val.val, by
    intro h
    exact x.property (Subtype.ext h)⟩,
    x.val.property⟩
  invFun x := ⟨⟨x.val.val, x.property⟩, by
    intro h
    exact x.val.property (congrArg Subtype.val h)⟩
  left_inv _ := rfl
  right_inv _ := rfl

lemma card_plane_nonzero (P : Plane Q E) :
    Fintype.card {x : {x : E // x ≠ 0} // x.val ∈ P.val} = Fintype.card Q ^ 2 - 1 := by
  rw [← Fintype.card_congr (planeNonzeroEquiv P)]
  have heq : Fintype.card {x : P.val // x = 0} = 1 := Fintype.card_unique
  rw [Fintype.card_subtype_compl, heq,
    Module.card_eq_pow_finrank (K := Q) (V := P.val), P.property]

/-- Double counting of a finite relation. -/
lemma card_relation {α : Type u_10} {β : Type u_11} [Fintype α] [Fintype β] (R : α → β → Prop) :
    (∑ a, Fintype.card {b // R a b}) = ∑ b, Fintype.card {a // R a b} := by
  classical
  let e : (Σ a, {b // R a b}) ≃ (Σ b, {a // R a b}) :=
    ⟨fun ⟨a, b, h⟩ => ⟨b, a, h⟩, fun ⟨b, a, h⟩ => ⟨a, b, h⟩,
      fun _ => rfl, fun _ => rfl⟩
  simpa only [Fintype.card_sigma] using Fintype.card_congr e

lemma card_planesThrough_mul {x : E} (hx : x ≠ 0) :
    Fintype.card {P : Plane Q E // x ∈ P.val} * (Fintype.card E - 1) =
      Fintype.card (Plane Q E) * (Fintype.card Q ^ 2 - 1) := by
  classical
  have h := card_relation (fun (P : Plane Q E) (y : {y : E // y ≠ 0}) => y.val ∈ P.val)
  have hxcard (y : {y : E // y ≠ 0}) :
      Fintype.card {P : Plane Q E // y.val ∈ P.val} =
        Fintype.card {P : Plane Q E // x ∈ P.val} := by
    obtain ⟨g, hg⟩ := exists_linearEquiv_apply_eq (Q := Q) y.property hx
    exact Fintype.card_congr (planesThroughEquiv g hg)
  simp only [card_plane_nonzero, hxcard, Finset.sum_const, Finset.card_univ,
    smul_eq_mul, Fintype.card_subtype_compl, Fintype.card_unique] at h
  simpa only [mul_comm] using h.symm

omit [Fintype Q] [Fintype E] in
lemma plane_nonempty (h : 2 ≤ finrank Q E) : Nonempty (Plane Q E) := by
  obtain ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank (R := Q) (M := E) h
  refine ⟨⟨Submodule.span Q (Set.range f), ?_⟩⟩
  simpa using finrank_span_eq_card hf

/-- Pure counting form of the inclusion probability. -/
lemma planesThrough_ratio [Nonempty (Plane Q E)] {x : E} (hx : x ≠ 0) :
    (Fintype.card {P : Plane Q E // x ∈ P.val} : ℝ) / Fintype.card (Plane Q E) =
      (Fintype.card Q ^ 2 - 1 : ℕ) / (Fintype.card E - 1 : ℕ) := by
  let : Nontrivial E := ⟨⟨x, 0, hx⟩⟩
  have hP : (Fintype.card (Plane Q E) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Fintype.card_ne_zero)
  have hE : ((Fintype.card E - 1 : ℕ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (by have := Fintype.one_lt_card (α := E); omega)
  apply (div_eq_div_iff hP hE).mpr
  exact_mod_cast (card_planesThrough_mul (Q := Q) hx).trans (Nat.mul_comm _ _)

theorem probability_mem_plane [Nonempty (Plane Q E)]
    [MeasurableSpace (Plane Q E)] [MeasurableSingletonClass (Plane Q E)]
    {x : E} (hx : x ≠ 0) :
    (Measure.uniformOfFinset (Finset.univ : Finset (Plane Q E))).real {P | x ∈ P.val} =
      ((Fintype.card Q : ℝ) ^ 2 - 1) /
        ((Fintype.card Q : ℝ) ^ finrank Q E - 1) := by
  rw [Measure.real, Measure.uniformOfFinset_apply]
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast, Finset.card_univ,
    ← Fintype.card_subtype, Set.mem_setOf_eq]
  change (Fintype.card {P : Plane Q E // x ∈ P.val} : ℝ) / Fintype.card (Plane Q E) = _
  rw [planesThrough_ratio (Q := Q) hx]
  have hQ : 1 ≤ Fintype.card Q ^ 2 := Nat.one_le_pow _ _ Fintype.card_pos
  have hE : 1 ≤ Fintype.card E := Fintype.card_pos
  rw [Nat.cast_sub hQ, Nat.cast_sub hE, Nat.cast_pow, Nat.cast_one,
    Module.card_eq_pow_finrank (K := Q) (V := E), Nat.cast_pow]

end KaplanskyCounterexample.FiniteGeometry

namespace KaplanskyCounterexample.FiniteGeometry
open Module MeasureTheory ProbabilityTheory
open KaplanskyCounterexample.FiniteLocalLemma

variable {Q : Type u_12} {E : Type u_13} {κ : Type u_14} {ι : Type u_15} [Field Q] [AddCommGroup E] [Module Q E]
  [Fintype Q] [Fintype E] [Fintype κ] [Nonempty (Plane Q E)]
  [MeasurableSpace (Plane Q E)] [MeasurableSingletonClass (Plane Q E)]

/-- The common one-vector inclusion probability. -/
def inclusionProbability (Q : Type u_16) (E : Type u_17) [Field Q] [AddCommGroup E] [Module Q E]
    [Fintype Q] : ℝ :=
  ((Fintype.card Q : ℝ) ^ 2 - 1) / ((Fintype.card Q : ℝ) ^ finrank Q E - 1)

/-- The replacement finite uniform measure has the same unit total mass. -/
local instance uniformPlaneProbability :
    IsProbabilityMeasure (Measure.uniformOfFinset (Finset.univ : Finset (Plane Q E))) where
  measure_univ := by
    rw [Measure.uniformOfFinset_apply]
    simp only [Set.mem_univ, Finset.filter_true, Finset.card_univ]
    exact ENNReal.div_self (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) (by simp)

/-- Independent choices of uniformly distributed slab direction planes. -/
def slabMeasure : Measure (κ → Plane Q E) :=
  Measure.pi fun _ => (Measure.uniformOfFinset (Finset.univ : Finset (Plane Q E)))

instance : IsProbabilityMeasure (slabMeasure (Q := Q) (E := E) (κ := κ)) := by
  unfold slabMeasure
  infer_instance

/-- Each bad event requires one specified nonzero vector in each of its
specified direction planes. -/
def includesAll (s : Finset κ) (w : κ → E) : Set (κ → Plane Q E) :=
  {P | ∀ v ∈ s, w v ∈ (P v).val}

lemma probability_includesAll (s : Finset κ) (w : κ → E)
    (hw : ∀ v ∈ s, w v ≠ 0) :
    (slabMeasure (Q := Q) (E := E) (κ := κ)).real (includesAll s w) =
      inclusionProbability Q E ^ s.card := by
  change (Measure.pi (fun _ : κ => (Measure.uniformOfFinset (Finset.univ : Finset (Plane Q E))))).real
    ((s : Set κ).pi fun v => {P | w v ∈ P.val}) = _
  rw [Measure.real, Measure.pi_pi_finset, ENNReal.toReal_prod]
  calc
    _ = ∏ _v ∈ s, inclusionProbability Q E := by
      apply Finset.prod_congr rfl
      intro v hv
      exact probability_mem_plane (hw v hv)
    _ = _ := by simp

theorem exists_slab_assignment [Fintype ι] (deps : ι → Finset κ) (w : ι → κ → E)
    (hw : ∀ i v, v ∈ deps i → w i v ≠ 0)
    (hne : ∀ i, (deps i).Nonempty) (hcard : ∀ i, (deps i).card ≤ 4)
    (hload : ∀ v, load deps (fun i => inclusionProbability Q E ^ (deps i).card) v ≤ 1 / 16) :
    ∃ P : κ → Plane Q E, ∀ i, ∃ v ∈ deps i, w i v ∉ (P v).val := by
  let μ := slabMeasure (Q := Q) (E := E) (κ := κ)
  have hind : iIndepFun (fun v (P : κ → Plane Q E) => P v) μ :=
    iIndepFun_pi (fun _ => measurable_id.aemeasurable)
  have hdet : ∀ i, DeterminedBy (fun v (P : κ → Plane Q E) => P v)
      (deps i) (includesAll (deps i) (w i)) := by
    intro i P P' heq
    change (∀ v ∈ deps i, w i v ∈ (P v).val) ↔ ∀ v ∈ deps i, w i v ∈ (P' v).val
    simp only at heq
    constructor <;> intro h v hv
    · rw [← heq v hv]; exact h v hv
    · rw [heq v hv]; exact h v hv
  have hpr (i : ι) : μ.real (includesAll (deps i) (w i)) =
      inclusionProbability Q E ^ (deps i).card := probability_includesAll _ _ (hw i)
  obtain ⟨_, P, hP⟩ := weighted_four_independent (μ := μ)
    (fun v => measurable_pi_apply v) hind deps hdet hne hcard (by simpa only [hpr] using hload)
  refine ⟨P, ?_⟩
  intro i
  simpa [includesAll] using hP i

end KaplanskyCounterexample.FiniteGeometry
end

end OAI
end
/- CHECKPOINT: OAI.RingTheory.DirectFiniteness.SlabAvoidance -/

/- BEGIN PINNED MODULE OAI.RingTheory.DirectFiniteness.EventLoad -/
section

namespace OAI

universe u_1 u_2 u_3 u_4 u_5

noncomputable section
open scoped Classical BigOperators
open KaplanskyCounterexample.FiniteLocalLemma
namespace KaplanskyCounterexample.FiniteGeometry

lemma sum_indicator_card {α : Type u_1} [Fintype α] (P : α → Prop) [DecidablePred P] (x : ℝ) :
    (∑ a : α, if P a then x else 0) = Fintype.card {a // P a} * x := by
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  congr 1
  exact_mod_cast (Fintype.card_subtype P).symm

variable {Q : Type u_2} {A : Type u_3} {R : Type u_4} {E : Type u_5} [Field Q] [AddCommGroup A] [Module Q A]
  [AddCommGroup E] [Module Q E] [Fintype A] [Fintype Q] [Fintype R] [Fintype E]
namespace Candidate
variable (F : DirectionFrame Q A R E) (T : R → Finset A) (k : ℕ)

lemma load_eq (hk3 : 3 ≤ k) (hk5 : k ≤ 5) (p : ℝ) (v : SlabVariable F) :
    load (fun c : Candidate F T k => c.deps F T) (fun c => p^(c.deps F T).card) v =
    Fintype.card {c : Candidate F T k // c.labels.card=1 ∧ v ∈ c.deps F T} * p^2 +
    Fintype.card {c : Candidate F T k // c.labels.card=2 ∧ v ∈ c.deps F T} * p^4 := by
  rw [load]
  calc
    _ = ∑ c : Candidate F T k,
      ((if c.labels.card=1 ∧ v ∈ c.deps F T then p^2 else 0) +
       (if c.labels.card=2 ∧ v ∈ c.deps F T then p^4 else 0)) := by
      apply Finset.sum_congr rfl
      intro c _
      have hb := c.labels_card_bounds F T hk5
      have hc : c.labels.card=1 ∨ c.labels.card=2 := by
        rcases eq_or_lt_of_le hb.1 with hcount | hcount
        · exact Or.inl hcount.symm
        · exact Or.inr (Nat.le_antisymm hb.2 (Nat.succ_le_of_lt hcount))
      rw [c.deps_card F T hk3 hk5]
      rcases hc with hc | hc <;> by_cases hv : v ∈ c.deps F T <;> simp [hc,hv]
    _ = _ := by
      rw [Finset.sum_add_distrib]
      exact congrArg₂ (· + ·)
        (sum_indicator_card (fun c : Candidate F T k => c.labels.card=1 ∧ v ∈ c.deps F T) (p^2))
        (sum_indicator_card (fun c : Candidate F T k => c.labels.card=2 ∧ v ∈ c.deps F T) (p^4))

lemma load_le (hk3 : 3 ≤ k) (hk5 : k ≤ 5) (M : ℕ)
    (hM : ∀ j (C : AffineCoset (F.U j)) r, (C.val ∩ T r).card ≤ M) (p : ℝ) (v : SlabVariable F) :
    load (fun c : Candidate F T k => c.deps F T) (fun c => p^(c.deps F T).card) v ≤
    (Fintype.card R*k^2*2^k*M^2*Fintype.card Q^k : ℕ)*p^2 +
    ((Fintype.card R*Fintype.card Q)*k^4*3^k*(Fintype.card Q*Fintype.card E)*
      (Fintype.card Q*Fintype.card E)^2*Fintype.card Q^k : ℕ)*p^4 := by
  rw [load_eq F T k hk3 hk5 p v]
  apply add_le_add
  · apply mul_le_mul_of_nonneg_right _ (sq_nonneg p)
    exact_mod_cast local_one_card_le F T k v.1 v.2 hk3 hk5 M (hM v.1 v.2)
  · apply mul_le_mul_of_nonneg_right _ ((even_two.mul_right 2).pow_nonneg p)
    have h := local_two_card_le F T k v.1 v.2 hk5
    rw [AffineCoset.card,F.card_U] at h
    exact_mod_cast h

end Candidate
end KaplanskyCounterexample.FiniteGeometry
end

end OAI
end
/- CHECKPOINT: OAI.RingTheory.DirectFiniteness.EventLoad -/

/- BEGIN PINNED MODULE OAI.RingTheory.DirectFiniteness.SlabHoleEvents -/
section

namespace OAI

universe u_1 u_2 u_3 u_4

noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample.FiniteGeometry
variable {Q : Type u_1} {A : Type u_2} {R : Type u_3} {E : Type u_4} [Field Q] [AddCommGroup A] [Module Q A]
  [AddCommGroup E] [Module Q E] [Fintype A]
namespace DirectionFrame
variable (F : DirectionFrame Q A R E) (S O : Finset A)

lemma diff_mem_coset {j : R × Q} (C : AffineCoset (F.U j)) {x y : A}
    (hx : x ∈ C.val) (hy : y ∈ C.val) : y-x ∈ F.U j := by
  have he := (AffineCoset.eq_of_mem _ hy).trans (AffineCoset.eq_of_mem _ hx).symm
  exact (AffineCoset.of_eq_iff _ _ _).mp he

abbrev LocalHolePair (v : SlabVariable F) :=
  {xy : ↥(O ∩ v.2.val) × ↥(O ∩ v.2.val) // xy.1 ≠ xy.2}

lemma localHolePair_card (hO : HoleEvents.GoodHoles S F.W F.U (fun r t => F.exc r t) O)
    (v : SlabVariable F) : Fintype.card (F.LocalHolePair O v) ≤ 100^2 := by
  apply le_trans (Fintype.card_subtype_le _)
  simp only [Fintype.card_prod,Fintype.card_coe]
  simpa only [pow_two] using Nat.mul_self_le_mul_self (F.holes_in_coset_card S O hO v.1 v.2)

def localHolePairVector (v : SlabVariable F) (p : F.LocalHolePair O v) : Q × E :=
  (F.diff_mem_coset v.2 (Finset.mem_inter.mp p.val.1.property).2
    (Finset.mem_inter.mp p.val.2.property).2).choose

lemma localHolePairVector_eq (v : SlabVariable F) (p : F.LocalHolePair O v) :
    F.u v.1 (F.localHolePairVector O v p) = p.val.2.val-p.val.1.val :=
  (F.diff_mem_coset v.2 (Finset.mem_inter.mp p.val.1.property).2
    (Finset.mem_inter.mp p.val.2.property).2).choose_spec

lemma localHolePairVector_nonzero
    (hO : HoleEvents.GoodHoles S F.W F.U (fun r t => F.exc r t) O)
    (v : SlabVariable F) (p : F.LocalHolePair O v) : (F.localHolePairVector O v p).2 ≠ 0 := by
  apply F.different_holes_nonzero_component S O hO v.1
    (Finset.mem_inter.mp p.val.1.property).1 (Finset.mem_inter.mp p.val.2.property).1
    (fun h => p.property (Subtype.ext h.symm))
  exact F.localHolePairVector_eq O v p

end DirectionFrame
end KaplanskyCounterexample.FiniteGeometry
end

end OAI
end
/- CHECKPOINT: OAI.RingTheory.DirectFiniteness.SlabHoleEvents -/

/- BEGIN PINNED MODULE OAI.RingTheory.DirectFiniteness.SlabEvents -/
section

namespace OAI

universe u_1 u_2 u_3 u_4

noncomputable section
open scoped Classical BigOperators
open KaplanskyCounterexample.FiniteLocalLemma
namespace KaplanskyCounterexample.FiniteGeometry
variable {Q : Type u_1} {A : Type u_2} {R : Type u_3} {E : Type u_4} [Field Q] [AddCommGroup A] [Module Q A]
  [AddCommGroup E] [Module Q E] [Fintype A] [Fintype Q] [Fintype R] [Fintype E]
namespace DirectionFrame
variable (F : DirectionFrame Q A R E) (S O : Finset A)

abbrev ShortCandidate := Σ i : Fin 3, Candidate F (F.replacementRegion O) (i.val+3)
abbrev SlabEvent := (Σ v : SlabVariable F, F.LocalHolePair O v) ⊕ F.ShortCandidate O

instance : Fintype (F.ShortCandidate O) := by unfold ShortCandidate; infer_instance
instance : Fintype (F.SlabEvent O) := by unfold SlabEvent; infer_instance

def eventDeps : F.SlabEvent O → Finset (SlabVariable F)
  | .inl p => {p.1}
  | .inr c => c.2.deps F (F.replacementRegion O)

def eventVector : F.SlabEvent O → SlabVariable F → E
  | .inl p => fun _ => (F.localHolePairVector O p.1 p.2).2
  | .inr c => c.2.constraintVector F (F.replacementRegion O)

omit [Fintype Q] [Fintype R] [Fintype E] in
lemma eventDeps_nonempty (i : F.SlabEvent O) : (F.eventDeps O i).Nonempty := by
  cases i with
  | inl p => exact Finset.singleton_nonempty _
  | inr c => exact c.2.deps_nonempty F (F.replacementRegion O)

omit [Fintype Q] [Fintype R] [Fintype E] in
lemma eventDeps_card (i : F.SlabEvent O) : (F.eventDeps O i).card ≤ 4 := by
  cases i with
  | inl p => simp [eventDeps]
  | inr c => exact c.2.deps_card_le_four F (F.replacementRegion O) (by omega) (by omega)

omit [Fintype Q] [Fintype R] [Fintype E] in
lemma eventVector_nonzero (hO : HoleEvents.GoodHoles S F.W F.U (fun r t => F.exc r t) O)
    (i : F.SlabEvent O) (v : SlabVariable F) (hv : v ∈ F.eventDeps O i) :
    F.eventVector O i v ≠ 0 := by
  cases i with
  | inl p => exact F.localHolePairVector_nonzero S O hO p.1 p.2
  | inr c => exact c.2.constraintVector_nonzero F (F.replacementRegion O) v hv

omit [Fintype E] in
lemma holeEvent_load (p : ℝ) (v : SlabVariable F) :
    load (fun z : Σ t : SlabVariable F, F.LocalHolePair O t => {z.1})
      (fun _ => p) v = Fintype.card (F.LocalHolePair O v) * p := by
  rw [load,Fintype.sum_sigma]
  calc
    _ = ∑ slab : SlabVariable F,
        if v = slab then Fintype.card (F.LocalHolePair O slab) * p else 0 := by
      apply Finset.sum_congr rfl
      intro slab _
      change (∑ _ : F.LocalHolePair O slab,
        if v ∈ ({slab} : Finset (SlabVariable F)) then p else 0) = _
      rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_ite,mul_zero]
      exact ite_congr (propext Finset.mem_singleton) (fun _ => rfl) (fun _ => rfl)
    _ = _ := by rw [Finset.sum_ite_eq,ite_eq_left (Finset.mem_univ v)]

/-- A convenient literal finite arithmetic load bound, prior to specializing q. -/
def slabLoadBound (_F : DirectionFrame Q A R E) (p : ℝ) : ℝ := 100^2*p + ∑ i : Fin 3,
    ((Fintype.card R*(i.val+3)^2*2^(i.val+3)*(100*Fintype.card Q)^2*Fintype.card Q^(i.val+3) : ℕ)*p^2 +
    ((Fintype.card R*Fintype.card Q)*(i.val+3)^4*3^(i.val+3)*(Fintype.card Q*Fintype.card E)*
      (Fintype.card Q*Fintype.card E)^2*Fintype.card Q^(i.val+3) : ℕ)*p^4)

lemma event_load_le (hO : HoleEvents.GoodHoles S F.W F.U (fun r t => F.exc r t) O)
    (p : ℝ) (hp : 0 ≤ p) (v : SlabVariable F) :
    load (F.eventDeps O) (fun i => p^(F.eventDeps O i).card) v ≤
      F.slabLoadBound p := by
  rw [load,Fintype.sum_sum_type]
  simp only [eventDeps,Finset.card_singleton,pow_one]
  change
    load (fun z : Σ t : SlabVariable F, F.LocalHolePair O t => {z.1}) (fun _ => p) v +
    (∑ c : F.ShortCandidate O,
      if v ∈ c.2.deps F (F.replacementRegion O) then p^(c.2.deps F (F.replacementRegion O)).card else 0) ≤ _
  rw [F.holeEvent_load,Fintype.sum_sigma]
  change Fintype.card (F.LocalHolePair O v)*p +
    (∑ i : Fin 3, load (fun c : Candidate F (F.replacementRegion O) (i.val+3) => c.deps F (F.replacementRegion O))
      (fun c => p^(c.deps F (F.replacementRegion O)).card) v) ≤ _
  apply add_le_add
  · exact mul_le_mul_of_nonneg_right (by exact_mod_cast F.localHolePair_card S O hO v) hp
  · apply Finset.sum_le_sum
    intro i _
    exact Candidate.load_le F (F.replacementRegion O) (i.val+3)
      (Nat.le_add_left 3 i.val) (Nat.add_le_add_right (Nat.le_of_lt_succ i.isLt) 3)
      (100*Fintype.card Q) (F.generic_region_card S O hO) p v

structure SuccessfulSlabs (P : SlabVariable F → Plane Q E) : Prop where
  holes : ∀ v (p : F.LocalHolePair O v), (F.localHolePairVector O v p).2 ∉ (P v).val
  candidates : ∀ k, 3 ≤ k → k ≤ 5 → ∀ c : Candidate F (F.replacementRegion O) k,
    ∃ v ∈ c.deps F (F.replacementRegion O), c.constraintVector F (F.replacementRegion O) v ∉ (P v).val

lemma exists_eventPlanes [Nonempty (Plane Q E)]
    (hO : HoleEvents.GoodHoles S F.W F.U (fun r t => F.exc r t) O)
    (hp : 0 ≤ inclusionProbability Q E)
    (hload : F.slabLoadBound (inclusionProbability Q E) ≤ 1/16) :
    ∃ P : SlabVariable F → Plane Q E, ∀ i, ∃ v ∈ F.eventDeps O i, F.eventVector O i v ∉ (P v).val := by
  let : MeasurableSpace (Plane Q E) := ⊤
  let : MeasurableSingletonClass (Plane Q E) := ⟨fun _ => trivial⟩
  apply exists_slab_assignment (F.eventDeps O) (F.eventVector O)
  · exact F.eventVector_nonzero S O hO
  · exact F.eventDeps_nonempty O
  · exact F.eventDeps_card O
  · intro v
    convert (F.event_load_le S O hO _ hp v).trans hload using 1
    unfold load
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> rfl

omit [Fintype Q] [Fintype R] [Fintype E] in
lemma successful_of_eventPlanes (P : SlabVariable F → Plane Q E)
    (hP : ∀ i, ∃ v ∈ F.eventDeps O i, F.eventVector O i v ∉ (P v).val) :
    F.SuccessfulSlabs O P := by
  constructor
  · intro v p
    obtain ⟨v',hv',hn⟩ := hP (.inl ⟨v,p⟩)
    have he : v'=v := Finset.mem_singleton.mp hv'
    simpa only [he,eventVector] using hn
  · intro k hk3 hk5 c
    rcases (show k=3 ∨ k=4 ∨ k=5 by omega) with rfl | rfl | rfl
    · exact hP (.inr ⟨0,c⟩)
    · exact hP (.inr ⟨1,c⟩)
    · exact hP (.inr ⟨2,c⟩)

lemma exists_successfulSlabs [Nonempty (Plane Q E)]
    (hO : HoleEvents.GoodHoles S F.W F.U (fun r t => F.exc r t) O)
    (hp : 0 ≤ inclusionProbability Q E)
    (hload : F.slabLoadBound (inclusionProbability Q E) ≤ 1/16) :
    ∃ P : SlabVariable F → Plane Q E, F.SuccessfulSlabs O P := by
  obtain ⟨P,hP⟩ := F.exists_eventPlanes S O hO hp hload
  exact ⟨P,F.successful_of_eventPlanes O P hP⟩

end DirectionFrame
end KaplanskyCounterexample.FiniteGeometry
end

end OAI
end
/- CHECKPOINT: OAI.RingTheory.DirectFiniteness.SlabEvents -/

/- BEGIN PINNED MODULE OAI.RingTheory.DirectFiniteness.SlabNumerics -/
section

namespace OAI

noncomputable section
namespace KaplanskyCounterexample.FiniteGeometry

lemma slab_probability_bound {q : ℝ} (hq : 2 ≤ q) :
    0 ≤ (q^2-1)/(q^119-1) ∧ (q^2-1)/(q^119-1) ≤ 2/q^117 := by
  have hq0 : 0 < q := by linarith
  have hq1 : 1 ≤ q := by linarith
  have hpow119 : 2 ≤ q^119 := hq.trans (by simpa using pow_le_pow_right₀ hq1 (show 1 ≤ 119 by decide))
  have hpow117 : 1 ≤ q^117 := one_le_pow₀ hq1
  have hd : 0 < q^119-1 := by linarith
  refine ⟨div_nonneg (by nlinarith) (le_of_lt hd),?_⟩
  apply (div_le_div_iff₀ hd (pow_pos hq0 _)).mpr
  have he : (q^2-1)*q^117 = q^119-q^117 := by ring
  rw [he]
  linarith

lemma slab_two_count_bound {q r : ℝ} {k : ℕ}
    (hq : 1 ≤ q) (hr : r ≤ 2*q^100) (hk : k ≤ 5) :
    r*(k:ℝ)^2*2^k*(100*q)^2*q^k ≤ 16000000*q^107 := by
  have hq0 : 0 ≤ q := by linarith
  have hk' : (k:ℝ) ≤ 5 := by exact_mod_cast hk
  have htwo : (2:ℝ)^k ≤ 32 := (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hk).trans_eq (by norm_num)
  have hqk : q^k ≤ q^5 := pow_le_pow_right₀ hq hk
  calc
    _ ≤ (2*q^100)*5^2*32*(100*q)^2*q^5 := by gcongr
    _ = 16000000*q^107 := by ring

lemma slab_four_count_bound {q r : ℝ} {k : ℕ}
    (hq : 1 ≤ q) (hr : r ≤ 2*q^100) (hk : k ≤ 5) :
    (r*q)*(k:ℝ)^4*3^k*(q*q^119)*(q*q^119)^2*q^k ≤ 303750*q^466 := by
  have hq0 : 0 ≤ q := by linarith
  have hk' : (k:ℝ) ≤ 5 := by exact_mod_cast hk
  have hthree : (3:ℝ)^k ≤ 243 := (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 3) hk).trans_eq (by norm_num)
  have hqk : q^k ≤ q^5 := pow_le_pow_right₀ hq hk
  calc
    _ ≤ ((2*q^100)*q)*5^4*243*(q*q^119)*(q*q^119)^2*q^5 := by gcongr
    _ = 303750*q^466 := by ring

lemma slab_weighted_bounds {q p : ℝ} (hq : 2 ≤ q) (hp0 : 0 ≤ p) (hp : p ≤ 2/q^117) :
    10000*p ≤ 20000/q ∧
    (16000000*q^107)*p^2 ≤ 64000000/q ∧
    (303750*q^466)*p^4 ≤ 4860000/q := by
  have hq0 : 0 < q := by linarith
  have hq1 : 1 ≤ q := by linarith
  have hqne : q ≠ 0 := ne_of_gt hq0
  have hm (n : ℕ) (hn : 1 ≤ n) : q ≤ q^n := by simpa using pow_le_pow_right₀ hq1 hn
  refine ⟨?_,?_,?_⟩
  · calc
      _ ≤ 10000*(2/q^117) := mul_le_mul_of_nonneg_left hp (by norm_num)
      _ = 20000/q^117 := by ring
      _ ≤ 20000/q := div_le_div_of_nonneg_left (by norm_num) hq0 (hm _ (by decide))
  · calc
      _ ≤ (16000000*q^107)*(2/q^117)^2 := by gcongr
      _ = 64000000/q^127 := by field_simp; norm_num
      _ ≤ 64000000/q := div_le_div_of_nonneg_left (by norm_num) hq0 (hm _ (by decide))
  · calc
      _ ≤ (303750*q^466)*(2/q^117)^4 := by gcongr
      _ = 4860000/q^2 := by field_simp; norm_num
      _ ≤ 4860000/q := div_le_div_of_nonneg_left (by norm_num) hq0 (hm _ (by decide))

end KaplanskyCounterexample.FiniteGeometry
end

end OAI
end
/- CHECKPOINT: OAI.RingTheory.DirectFiniteness.SlabNumerics -/

/- BEGIN PINNED MODULE OAI.RingTheory.DirectFiniteness.SlabLoad -/
section

namespace OAI

universe u_1 u_2 u_3 u_4

noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample.FiniteGeometry
namespace DirectionFrame
variable {Q : Type u_1} {A : Type u_2} {R : Type u_3} {E : Type u_4} [Field Q] [AddCommGroup A] [Module Q A]
  [AddCommGroup E] [Module Q E] [Fintype A] [Fintype Q] [Fintype R] [Fintype E]

omit [Fintype A] in
lemma slabLoadBound_small (F : DirectionFrame Q A R E)
    (hq : 3305600000 ≤ Fintype.card Q)
    (hR : Fintype.card R ≤ 2*(Fintype.card Q)^100)
    (hE : Fintype.card E=(Fintype.card Q)^119)
    {p : ℝ} (hp0 : 0 ≤ p) (hp : p ≤ 2/(Fintype.card Q:ℝ)^117) :
    F.slabLoadBound p ≤ 1/16 := by
  let q : ℝ := Fintype.card Q
  have hqbig : 3305600000 ≤ q := by dsimp [q]; exact_mod_cast hq
  have hq2 : 2 ≤ q := by linarith
  have hq1 : 1 ≤ q := by linarith
  have hq0 : 0 < q := by linarith
  have hr : (Fintype.card R:ℝ) ≤ 2*q^100 := by dsimp [q]; exact_mod_cast hR
  obtain ⟨hhole,htwo,hfour⟩ := slab_weighted_bounds hq2 hp0 hp
  have hterm (i : Fin 3) :
      ((Fintype.card R*(i.val+3)^2*2^(i.val+3)*(100*Fintype.card Q)^2*Fintype.card Q^(i.val+3) : ℕ):ℝ)*p^2 +
      (((Fintype.card R*Fintype.card Q)*(i.val+3)^4*3^(i.val+3)*(Fintype.card Q*Fintype.card E)*
        (Fintype.card Q*Fintype.card E)^2*Fintype.card Q^(i.val+3) : ℕ):ℝ)*p^4
      ≤ 64000000/q+4860000/q := by
    have h2 := slab_two_count_bound hq1 hr (by omega : i.val+3 ≤ 5)
    have h4 := slab_four_count_bound hq1 hr (by omega : i.val+3 ≤ 5)
    have h2' := (mul_le_mul_of_nonneg_right h2 (sq_nonneg p)).trans htwo
    have h4' := (mul_le_mul_of_nonneg_right h4 (pow_nonneg hp0 4)).trans hfour
    rw [hE]
    push_cast at h2' h4' ⊢
    exact add_le_add h2' h4'
  calc
    F.slabLoadBound p ≤ 20000/q + ∑ _i : Fin 3, (64000000/q+4860000/q) := by
      apply add_le_add
      · simpa only [show (100:ℝ)^2=10000 by norm_num] using hhole
      · exact Finset.sum_le_sum (fun i _ => hterm i)
    _ = 206600000/q := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; ring
    _ ≤ 1/16 := (div_le_iff₀ hq0).mpr (by linarith)

lemma exists_successfulSlabs_large (F : DirectionFrame Q A R E) (S O : Finset A)
    (hO : HoleEvents.GoodHoles S F.W F.U (fun r t => F.exc r t) O)
    (hq : 3305600000 ≤ Fintype.card Q)
    (hR : Fintype.card R ≤ 2*(Fintype.card Q)^100)
    (hE : Module.finrank Q E=119) :
    ∃ P : SlabVariable F → Plane Q E, F.SuccessfulSlabs O P := by
  let : Nonempty (Plane Q E) := plane_nonempty (by rw [hE]; decide)
  have hq2 : (2:ℝ) ≤ Fintype.card Q := by exact_mod_cast (by omega : 2 ≤ Fintype.card Q)
  obtain ⟨hp0,hp⟩ := slab_probability_bound hq2
  have he : inclusionProbability Q E = ((Fintype.card Q:ℝ)^2-1)/((Fintype.card Q:ℝ)^119-1) := by
    rw [inclusionProbability,hE]
  rw [← he] at hp0 hp
  refine F.exists_successfulSlabs S O hO hp0 (F.slabLoadBound_small hq hR ?_ hp0 hp)
  rw [Module.card_eq_pow_finrank (K := Q),hE]

end DirectionFrame
end KaplanskyCounterexample.FiniteGeometry
end

end OAI
end
/- CHECKPOINT: OAI.RingTheory.DirectFiniteness.SlabLoad -/

/- BEGIN PINNED MODULE OAI.RingTheory.DirectFiniteness.AffineLines -/
section

namespace OAI

universe u_1 u_2

noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample.FiniteGeometry
variable {Q : Type u_1} {A : Type u_2} [Field Q] [AddCommGroup A] [Module Q A] [Fintype Q] [Fintype A]

omit [Fintype A] in
@[simp] lemma mem_linePoints (x v y : A) :
    y ∈ linePoints (Q := Q) x v ↔ ∃ t : Q, x + t • v = y := by
  simp [linePoints]

lemma linePoints_rebase {x v y : A} (hy : y ∈ linePoints (Q := Q) x v) :
    linePoints (Q := Q) y v = linePoints (Q := Q) x v := by
  rw [linePoints_eq_coset] at hy ⊢
  rw [linePoints_eq_coset]
  exact cosetPoints_eq ((mem_cosetPoints _ _ _).mp hy)

lemma linePoints_scale (x v : A) {t : Q} (ht : t ≠ 0) :
    linePoints (Q := Q) x (t • v) = linePoints (Q := Q) x v := by
  ext y
  simp only [mem_linePoints]
  constructor
  · rintro ⟨s,rfl⟩; exact ⟨s*t,by simp [smul_smul]⟩
  · rintro ⟨s,rfl⟩; exact ⟨s/t,by simp [smul_smul,ht]⟩

lemma FullLine.eq_linePoints_sub {l : Finset A} (hl : FullLine (Q := Q) l)
    {x y : A} (hx : x ∈ l) (hy : y ∈ l) (hne : y ≠ x) :
    l = linePoints (Q := Q) x (y-x) := by
  obtain ⟨a,v,hv,he⟩ := hl
  have he' : l = linePoints (Q := Q) x v := by
    rw [he]
    exact (linePoints_rebase (he ▸ hx)).symm
  rw [he'] at hy
  obtain ⟨t,ht⟩ := mem_linePoints _ _ _ |>.mp hy
  have ht0 : t ≠ 0 := by intro h; exact hne (by simpa [h] using ht.symm)
  have hdiff : y-x=t • v := by rw [← ht]; abel
  rw [he',hdiff,linePoints_scale _ _ ht0]

lemma FullLine.eq_of_two_mem {l m : Finset A} (hl : FullLine (Q := Q) l)
    (hm : FullLine (Q := Q) m) {x y : A} (hx : x ∈ l) (hy : y ∈ l)
    (hx' : x ∈ m) (hy' : y ∈ m) (hne : y ≠ x) : l=m := by
  rw [hl.eq_linePoints_sub hx hy hne,hm.eq_linePoints_sub hx' hy' hne]

omit [Fintype A] in
lemma direction_sub_mem {U : Submodule Q A} {a v x y : A} (hv : v ∈ U)
    (hx : x ∈ linePoints (Q := Q) a v) (hy : y ∈ linePoints (Q := Q) a v) :
    y-x ∈ U := by
  obtain ⟨s,rfl⟩ := (mem_linePoints _ _ _).mp hx
  obtain ⟨t,rfl⟩ := (mem_linePoints _ _ _).mp hy
  convert U.smul_mem (t-s) hv using 1
  simp only [sub_smul]
  abel

/-- A partition by full lines, represented without arbitrary labels or duplicates. -/
structure LinePartition where
  through : A → Finset A
  self : ∀ x, x ∈ through x
  full : ∀ x, FullLine (Q := Q) (through x)
  stable : ∀ x y, y ∈ through x → through y = through x

namespace LinePartition
variable (L : LinePartition (Q := Q) (A := A))
omit [Fintype A] in
lemma mem_iff (x y : A) : y ∈ L.through x ↔ L.through y = L.through x := by
  exact ⟨L.stable x y, fun h => h ▸ L.self y⟩
omit [Fintype A] in
lemma disjoint_or_eq (x y : A) : Disjoint (L.through x) (L.through y) ∨ L.through x=L.through y := by
  by_cases h : Disjoint (L.through x) (L.through y)
  · exact Or.inl h
  · obtain ⟨z,hz,hz'⟩ := Finset.not_disjoint_iff.mp h
    exact Or.inr ((L.stable x z hz).symm.trans (L.stable y z hz'))
end LinePartition
end KaplanskyCounterexample.FiniteGeometry
end

end OAI
end
/- CHECKPOINT: OAI.RingTheory.DirectFiniteness.AffineLines -/

/- BEGIN PINNED MODULE OAI.RingTheory.DirectFiniteness.PartialPartition -/
section

namespace OAI

universe u_1 u_2 u_3 u_4

noncomputable section
open scoped Classical
namespace KaplanskyCounterexample.FiniteGeometry
variable {Q : Type u_1} {A : Type u_2} {B : Type u_3} [Field Q] [AddCommGroup A] [Module Q A]
  [AddCommGroup B] [Module Q B] [Fintype Q] [Fintype A] [Fintype B]

omit [Fintype A] [Fintype B] in
lemma image_linePoints (f : B →ₗ[Q] A) (o x v : B) :
    (linePoints (Q := Q) x v).image (fun z => f (o+z)) =
      linePoints (Q := Q) (f (o+x)) (f v) := by
  ext y
  simp only [Finset.mem_image,mem_linePoints]
  constructor
  · rintro ⟨z,⟨t,rfl⟩,rfl⟩
    exact ⟨t,by simp [map_add,add_assoc]⟩
  · rintro ⟨t,rfl⟩
    exact ⟨x+t • v,⟨t,rfl⟩,by simp [map_add,add_assoc]⟩

omit [Fintype A] [Fintype B] in
lemma image_affine_linePoints (f : B →ₗ[Q] A) (o : A) (x v : B) :
    (linePoints (Q := Q) x v).image (fun z => o + f z) =
      linePoints (Q := Q) (o+f x) (f v) := by
  ext point
  constructor
  · intro membership
    obtain ⟨preimage, preimage_mem, rfl⟩ := Finset.mem_image.mp membership
    obtain ⟨scalar, rfl⟩ := (mem_linePoints _ _ _).mp preimage_mem
    exact (mem_linePoints _ _ _).mpr ⟨scalar, by simp only [map_add, map_smul, add_assoc]⟩
  · intro membership
    obtain ⟨scalar, rfl⟩ := (mem_linePoints _ _ _).mp membership
    exact Finset.mem_image.mpr ⟨x + scalar • v, (mem_linePoints _ _ _).mpr ⟨scalar, rfl⟩,
      by simp only [map_add, map_smul, add_assoc]⟩

omit [Fintype A] [Fintype B] in
lemma FullLine.image_affine {s : Finset B} (hs : FullLine (Q := Q) s)
    (f : B →ₗ[Q] A) (hf : Function.Injective f) (o : A) :
    FullLine (Q := Q) (s.image (fun z => o+f z)) := by
  obtain ⟨x,v,hv,rfl⟩ := hs
  rw [image_affine_linePoints]
  exact ⟨o+f x,f v,fun he => hv (hf (he.trans f.map_zero.symm)),rfl⟩

/-- A full-line partition of one finite affine slab. -/
structure PartitionOn (S : Finset A) where
  through : S → Finset A
  subset : ∀ x, through x ⊆ S
  self : ∀ x, x.val ∈ through x
  full : ∀ x, FullLine (Q := Q) (through x)
  stable : ∀ x y, y.val ∈ through x → through y = through x

namespace PartitionOn
variable (f : B →ₗ[Q] A) (hf : Function.Injective f) (o : A)

local instance identityRingHomSurjective : RingHomSurjective (RingHom.id Q) := inferInstance

def parametrization : B ≃ ↥(cosetPoints f.range o) :=
  Equiv.ofBijective (fun x => ⟨o+f x,by simp⟩) (by
    constructor
    · intro x y h; exact hf (add_left_cancel (congrArg Subtype.val h))
    · rintro ⟨y,hy⟩
      obtain ⟨x,hx⟩ := (mem_cosetPoints _ _ _).mp hy
      exact ⟨x,Subtype.ext (by change o+f x=y; rw [hx]; abel)⟩)

omit [Fintype Q] [Fintype B] in
@[simp] lemma parametrization_val (x : B) : (parametrization f hf o x).val = o+f x := rfl

omit [Fintype Q] [Fintype B] in
@[simp] lemma parametrization_symm_apply (x : ↥(cosetPoints f.range o)) :
    o+f ((parametrization f hf o).symm x)=x.val := by
  exact congrArg Subtype.val ((parametrization f hf o).apply_symm_apply x)

def image (L : LinePartition (Q := Q) (A := B)) : PartitionOn (Q := Q) (cosetPoints f.range o) where
  through x := (L.through ((parametrization f hf o).symm x)).image (fun z => o+f z)
  subset x := by
    rintro y hy
    obtain ⟨z,_,rfl⟩ := Finset.mem_image.mp hy
    simp
  self x := Finset.mem_image.mpr ⟨_,L.self _,parametrization_symm_apply f hf o x⟩
  full x := (L.full _).image_affine f hf o
  stable x y hy := by
    obtain ⟨z,hz,hzy⟩ := Finset.mem_image.mp hy
    have he : z=(parametrization f hf o).symm y := by
      apply (parametrization f hf o).injective
      apply Subtype.ext
      simpa using hzy
    rw [he] at hz
    rw [L.stable _ _ hz]

omit [Fintype B] in
lemma image_through (L : LinePartition (Q := Q) (A := B)) (x : B) :
    (image f hf o L).through (parametrization f hf o x) =
      (L.through x).image (fun z => o+f z) := by
  simp [image]

end PartitionOn

section Glue
variable {ι : Type u_4} (S : ι → Finset A) (key : A → ι)
  (hmem : ∀ x, x ∈ S (key x))
  (hkey : ∀ x y, y ∈ S (key x) → key y=key x)
  (L : ∀ i, PartitionOn (Q := Q) (S i))

def gluePartition : LinePartition (Q := Q) (A := A) where
  through x := (L (key x)).through ⟨x,hmem x⟩
  self x := (L (key x)).self ⟨x,hmem x⟩
  full x := (L (key x)).full ⟨x,hmem x⟩
  stable x y hy := by
    have hyS := (L (key x)).subset ⟨x,hmem x⟩ hy
    have he := hkey x y hyS
    have transport (i i' : ι) (heq : i=i') (hi : y ∈ S i) (hi' : y ∈ S i') :
        (L i).through ⟨y,hi⟩ = (L i').through ⟨y,hi'⟩ := by subst i'; rfl
    exact (transport _ _ he (hmem y) hyS).trans
      ((L (key x)).stable ⟨x,hmem x⟩ ⟨y,hyS⟩ hy)

end Glue
end KaplanskyCounterexample.FiniteGeometry
end

end OAI
end
/- CHECKPOINT: OAI.RingTheory.DirectFiniteness.PartialPartition -/

/- BEGIN PINNED MODULE OAI.RingTheory.DirectFiniteness.SlabKeys -/
section

namespace OAI

universe u_1 u_2 u_3 u_4

noncomputable section
open scoped Classical
namespace KaplanskyCounterexample.FiniteGeometry
variable {Q : Type u_1} {A : Type u_2} {R : Type u_3} {E : Type u_4} [Field Q] [AddCommGroup A] [Module Q A]
  [AddCommGroup E] [Module Q E] [Fintype A]
namespace DirectionFrame
variable (F : DirectionFrame Q A R E)

local instance identityRingHomSurjective : RingHomSurjective (RingHom.id Q) := inferInstance

def slabMap (j : R × Q) (P : Plane Q E) : (P.val × Q) →ₗ[Q] A where
  toFun x := F.u j (x.2,x.1.val)
  map_add' x y := by simpa using (F.u j).map_add (x.2,x.1.val) (y.2,y.1.val)
  map_smul' c x := by simpa using (F.u j).map_smul c (x.2,x.1.val)

omit [Fintype A] in
lemma slabMap_injective (j : R × Q) (P : Plane Q E) : Function.Injective (F.slabMap j P) := by
  intro x y h
  have h' := F.u_injective j h
  exact Prod.ext (Subtype.ext (congrArg Prod.snd h')) (congrArg Prod.fst h')

omit [Fintype A] in
lemma slabMap_range_le (j : R × Q) (P : Plane Q E) : (F.slabMap j P).range ≤ F.U j := by
  rintro x ⟨z,rfl⟩
  exact ⟨(z.2,z.1.val),rfl⟩

omit [Fintype A] in
@[simp] lemma slabMap_axis (j : R × Q) (P : Plane Q E) (t : Q) :
    F.slabMap j P (0,t) = F.d j t := by simp [slabMap]

variable (P : SlabVariable F → Plane Q E) (j : R × Q)

def SlabKey := Σ C : AffineCoset (F.U j),
  {B : AffineCoset (F.slabMap j (P ⟨j,C⟩)).range // B.val ⊆ C.val}

def SlabKey.points (k : F.SlabKey P j) : Finset A := k.2.val.val

lemma SlabKey.nonempty (k : F.SlabKey P j) : (k.points F P j).Nonempty := k.2.val.nonempty _

def slabKeyOf (x : A) : F.SlabKey P j :=
  ⟨AffineCoset.of (F.U j) x,AffineCoset.of (F.slabMap j (P ⟨j,AffineCoset.of (F.U j) x⟩)).range x,by
    intro y hy
    exact (mem_cosetPoints _ _ _).mpr (F.slabMap_range_le j _ ((mem_cosetPoints _ _ _).mp hy))⟩

lemma mem_slabKeyOf (x : A) : x ∈ (F.slabKeyOf P j x).points F P j := self_mem_cosetPoints _ _

lemma SlabKey.unique {k k' : F.SlabKey P j} {x : A}
    (hx : x ∈ k.points F P j) (hx' : x ∈ k'.points F P j) : k=k' := by
  obtain ⟨C,⟨B,hB⟩⟩ := k
  obtain ⟨C',⟨B',hB'⟩⟩ := k'
  have hc : C=C' := (AffineCoset.eq_of_mem _ (hB hx)).symm.trans (AffineCoset.eq_of_mem _ (hB' hx'))
  subst C'
  have hb : B=B' := (AffineCoset.eq_of_mem _ hx).symm.trans (AffineCoset.eq_of_mem _ hx')
  subst B'
  rfl

lemma slabKeyOf_eq_of_mem {k : F.SlabKey P j} {x : A} (hx : x ∈ k.points F P j) :
    F.slabKeyOf P j x=k := SlabKey.unique F P j (F.mem_slabKeyOf P j x) hx

lemma slabKeyOf_stable (x y : A) (hy : y ∈ (F.slabKeyOf P j x).points F P j) :
    F.slabKeyOf P j y=F.slabKeyOf P j x := F.slabKeyOf_eq_of_mem P j hy

lemma SlabKey.diff {k : F.SlabKey P j} {x y : A} (hx : x ∈ k.points F P j)
    (hy : y ∈ k.points F P j) : y-x ∈ (F.slabMap j (P ⟨j,k.1⟩)).range := by
  exact (AffineCoset.of_eq_iff _ _ _).mp ((AffineCoset.eq_of_mem _ hy).trans (AffineCoset.eq_of_mem _ hx).symm)

lemma SlabKey.holes_unique (O : Finset A) (hP : F.SuccessfulSlabs O P)
    (k : F.SlabKey P j) {x y : A} (hxO : x ∈ O) (hyO : y ∈ O)
    (hx : x ∈ k.points F P j) (hy : y ∈ k.points F P j) : x=y := by
  by_contra hne
  let p : F.LocalHolePair O ⟨j,k.1⟩ := ⟨(⟨x,Finset.mem_inter.mpr ⟨hxO,k.2.property hx⟩⟩,
    ⟨y,Finset.mem_inter.mpr ⟨hyO,k.2.property hy⟩⟩),fun h => hne (congrArg Subtype.val h)⟩
  obtain ⟨z,hz⟩ := k.diff F P j hx hy
  have he : F.localHolePairVector O ⟨j,k.1⟩ p = (z.2,z.1.val) :=
    F.u_injective j ((F.localHolePairVector_eq O _ p).trans hz.symm)
  apply hP.holes _ p
  rw [he]
  exact z.1.property

end DirectionFrame
end KaplanskyCounterexample.FiniteGeometry
end

end OAI
end
/- CHECKPOINT: OAI.RingTheory.DirectFiniteness.SlabKeys -/

/- BEGIN PINNED MODULE OAI.RingTheory.DirectFiniteness.SlabPartition -/
section

namespace OAI

universe u_1 u_2 u_3

noncomputable section
open scoped Classical
open Module
namespace KaplanskyCounterexample.FiniteGeometry

variable {Q : Type u_1} {P : Type u_2} [Field Q] [AddCommGroup P] [Module Q P]

def NoEigenvector (J : P →ₗ[Q] P) : Prop :=
  ∀ x : P, x ≠ 0 → ∀ c : Q, J x ≠ c • x

lemma independent_pair_of_noEigenvector (J : P →ₗ[Q] P) (hJ : NoEigenvector J)
    (x : P) (hx : x ≠ 0) : LinearIndependent Q ![J x, x] := by
  rw [linearIndependent_fin2]
  exact ⟨hx, fun c h => hJ x hx c h.symm⟩

theorem existsUnique_slab_functional [FiniteDimensional Q P]
    (hd : finrank Q P = 2) (J : P →ₗ[Q] P) (hJ : NoEigenvector J)
    (x : P) (hx : x ≠ 0) (c : Q) :
    ∃! γ : P →ₗ[Q] Q, γ x = 1 ∧ γ (J x) = c := by
  let B : Basis (Fin 2) Q P := basisOfLinearIndependentOfCardEqFinrank
    (independent_pair_of_noEigenvector J hJ x hx) (by simp [hd])
  have hB (i : Fin 2) : B i = ![J x, x] i := by
    simp [B]
  let γ : P →ₗ[Q] Q := B.constr Q ![c, 1]
  have hγ (i : Fin 2) : γ (B i) = ![c, 1] i := by simp [γ]
  have hγx : γ x = 1 := by simpa [hB] using hγ 1
  have hγJx : γ (J x) = c := by simpa [hB] using hγ 0
  refine ⟨γ, ⟨hγx, hγJx⟩, ?_⟩
  intro δ hδ
  apply B.ext
  intro i
  fin_cases i <;> simp_all

def slabLine (J : P →ₗ[Q] P) (γ : P →ₗ[Q] Q) : Set (P × Q) :=
  {p | γ p.1 = 1 ∧ p.2 = γ (J p.1)}

lemma slabLine_off_axis (J : P →ₗ[Q] P) (γ : P →ₗ[Q] Q)
    {p : P × Q} (hp : p ∈ slabLine J γ) : p.1 ≠ 0 := by
  intro h
  have h' := hp.1
  rw [h, map_zero] at h'
  exact zero_ne_one h'

lemma slabLine_functional_ne_zero (J : P →ₗ[Q] P) (γ : P →ₗ[Q] Q)
    {p : P × Q} (hp : p ∈ slabLine J γ) : γ ≠ 0 := by
  intro h
  have h' := hp.1
  rw [h] at h'
  exact zero_ne_one h'

/-- The axis and the displayed lifted lines partition the slab. -/
theorem slab_partition [FiniteDimensional Q P] (hd : finrank Q P = 2)
    (J : P →ₗ[Q] P) (hJ : NoEigenvector J) (p : P × Q) :
    p.1 = 0 ∨ ∃! γ : {γ : P →ₗ[Q] Q // γ ≠ 0}, p ∈ slabLine J γ.val := by
  by_cases hx : p.1 = 0
  · exact Or.inl hx
  · right
    obtain ⟨γ, hγ, hu⟩ := existsUnique_slab_functional hd J hJ p.1 hx p.2
    have hp : p ∈ slabLine J γ := ⟨hγ.1, hγ.2.symm⟩
    refine ⟨⟨γ, slabLine_functional_ne_zero J γ hp⟩, hp, ?_⟩
    intro δ hδ
    apply Subtype.ext
    exact hu δ.val ⟨hδ.1, hδ.2.symm⟩

/-- The displayed set is a full affine line, not merely an arbitrary part
of the partition; its direction has nonzero projection to the plane. -/
theorem slabLine_is_line [FiniteDimensional Q P] (hd : finrank Q P = 2)
    (J : P →ₗ[Q] P) (γ : P →ₗ[Q] Q) (hγ : γ ≠ 0) :
    ∃ u v : P × Q, v.1 ≠ 0 ∧
      slabLine J γ = Set.range (fun t : Q => u + t • v) := by
  have hex : ∃ x : P, γ x ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hγ (LinearMap.ext hn)
  obtain ⟨x, hx⟩ := hex
  let x₀ := (γ x)⁻¹ • x
  have hx₀ : γ x₀ = 1 := by simp [x₀, hx]
  have hsurj : Function.Surjective γ := by
    intro c
    exact ⟨c • x₀, by simp [hx₀]⟩
  have hker : finrank Q γ.ker = 1 := by
    have h := LinearMap.finrank_range_add_finrank_ker γ
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, finrank_self, hd] at h
    omega
  have hkn : γ.ker ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hker
    omega
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hkn
  let y' : γ.ker := ⟨y, hy⟩
  have hy' : y' ≠ 0 := by
    intro h
    exact hy0 (congrArg Subtype.val h)
  have hgen : ∀ z : γ.ker, ∃ t : Q, t • y' = z :=
    (finrank_eq_one_iff_of_nonzero' y' hy').mp hker
  have hγy : γ y = 0 := hy
  refine ⟨(x₀, γ (J x₀)), (y, γ (J y)), hy0, ?_⟩
  ext p
  constructor
  · intro hp
    have hz : p.1 - x₀ ∈ γ.ker := by
      change γ (p.1 - x₀) = 0
      rw [map_sub, hp.1, hx₀, sub_self]
    obtain ⟨t, ht⟩ := hgen ⟨p.1 - x₀, hz⟩
    have hty : t • y = p.1 - x₀ := congrArg Subtype.val ht
    have hxp : x₀ + t • y = p.1 := eq_sub_iff_add_eq.mp hty |>.symm ▸ add_comm _ _
    refine ⟨t, ?_⟩
    apply Prod.ext
    · exact hxp
    · change γ (J x₀) + t * γ (J y) = p.2
      rw [hp.2, ← hxp]
      simp
  · rintro ⟨t, rfl⟩
    constructor
    · change γ (x₀ + t • y) = 1
      simp [hx₀, hγy]
    · change γ (J x₀) + t * γ (J y) = γ (J (x₀ + t • y))
      simp

variable {F : Type u_3} [Field F] [Algebra Q F]

/-- A quadratic extension supplies the operator without eigenvectors. -/
theorem exists_noEigenvector_of_quadratic (hd : finrank Q F = 2) :
    ∃ J : F →ₗ[Q] F, NoEigenvector J := by
  have hn : ¬ Function.Surjective (algebraMap Q F) := by
    intro hs
    have h := Module.finrank_of_bijective_algebraMap ⟨(algebraMap Q F).injective, hs⟩
    omega
  have hn' : ∃ η : F, ∀ c : Q, algebraMap Q F c ≠ η := by
    simpa only [Function.Surjective, not_forall, not_exists] using hn
  obtain ⟨η, hη⟩ := hn'
  refine ⟨LinearMap.mulLeft Q η, ?_⟩
  intro x hx c h
  apply hη c
  apply mul_right_cancel₀ hx
  simpa [Algebra.smul_def] using h.symm

end KaplanskyCounterexample.FiniteGeometry
end

end OAI
end
/- CHECKPOINT: OAI.RingTheory.DirectFiniteness.SlabPartition -/

/- BEGIN PINNED MODULE OAI.RingTheory.DirectFiniteness.ModelPartition -/
section

namespace OAI

universe u_1 u_2

noncomputable section
open scoped Classical
open Module
namespace KaplanskyCounterexample.FiniteGeometry
variable {Q : Type u_1} {P : Type u_2} [Field Q] [AddCommGroup P] [Module Q P] [Fintype Q] [Fintype P]

def slabLinePoints (J : P →ₗ[Q] P) (γ : P →ₗ[Q] Q) : Finset (P × Q) :=
  Finset.univ.filter (fun p => p ∈ slabLine J γ)

@[simp] lemma mem_slabLinePoints (J : P →ₗ[Q] P) (γ : P →ₗ[Q] Q) (p : P × Q) :
    p ∈ slabLinePoints J γ ↔ p ∈ slabLine J γ := by simp [slabLinePoints]

lemma slabLinePoints_full [FiniteDimensional Q P] (hd : finrank Q P = 2)
    (J : P →ₗ[Q] P) (γ : P →ₗ[Q] Q) (hγ : γ ≠ 0) : FullLine (Q := Q) (slabLinePoints J γ) := by
  obtain ⟨u,v,hv,he⟩ := slabLine_is_line hd J γ hγ
  refine ⟨u,v,fun h => hv (congrArg Prod.fst h),?_⟩
  ext z
  rw [mem_slabLinePoints,he,Set.mem_range,mem_linePoints]

def modelAxis : Finset (P × Q) := linePoints (Q := Q) 0 (0,1)

omit [Fintype P] in
@[simp] lemma mem_modelAxis (p : P × Q) : p ∈ modelAxis (Q := Q) (P := P) ↔ p.1=0 := by
  change p ∈ linePoints (Q := Q) 0 (0,1) ↔ p.1=0
  constructor
  · intro membership
    obtain ⟨scalar,rfl⟩ := (mem_linePoints _ _ _).mp membership
    exact (zero_add (scalar • (0 : P))).trans (smul_zero scalar)
  · intro first_zero
    apply (mem_linePoints _ _ _).mpr
    refine ⟨p.2,Prod.ext ?_ ?_⟩
    · exact ((zero_add _).trans (smul_zero p.2)).trans first_zero.symm
    · exact (zero_add _).trans (mul_one p.2)

omit [Fintype P] in
lemma modelAxis_full : FullLine (Q := Q) (modelAxis (Q := Q) (P := P)) :=
  ⟨0,(0,1),fun h => one_ne_zero (congrArg Prod.snd h),rfl⟩

variable [FiniteDimensional Q P] (hd : finrank Q P = 2) (J : P →ₗ[Q] P) (hJ : NoEigenvector J)

def modelFunctional (x : P × Q) (hx : x.1 ≠ 0) : P →ₗ[Q] Q :=
  (existsUnique_slab_functional hd J hJ x.1 hx x.2).choose

omit [Fintype Q] [Fintype P] in
lemma modelFunctional_spec (x : P × Q) (hx : x.1 ≠ 0) :
    x ∈ slabLine J (modelFunctional hd J hJ x hx) := by
  have h := (existsUnique_slab_functional hd J hJ x.1 hx x.2).choose_spec.1
  exact ⟨h.1,h.2.symm⟩

omit [Fintype Q] [Fintype P] in
lemma modelFunctional_unique (x : P × Q) (hx : x.1 ≠ 0) (γ : P →ₗ[Q] Q)
    (hγ : x ∈ slabLine J γ) : γ=modelFunctional hd J hJ x hx :=
  (existsUnique_slab_functional hd J hJ x.1 hx x.2).choose_spec.2 γ ⟨hγ.1,hγ.2.symm⟩

def modelThrough (x : P × Q) : Finset (P × Q) :=
  if hx : x.1=0 then modelAxis else slabLinePoints J (modelFunctional hd J hJ x hx)

lemma modelThrough_self (x : P × Q) : x ∈ modelThrough hd J hJ x := by
  unfold modelThrough
  split_ifs with hx
  · exact (mem_modelAxis x).mpr hx
  · exact (mem_slabLinePoints _ _ _).mpr (modelFunctional_spec hd J hJ x hx)

lemma modelThrough_full (x : P × Q) : FullLine (Q := Q) (modelThrough hd J hJ x) := by
  unfold modelThrough
  split_ifs with hx
  · exact modelAxis_full
  · exact slabLinePoints_full hd J _ (slabLine_functional_ne_zero J _ (modelFunctional_spec hd J hJ x hx))

lemma modelThrough_stable (x y : P × Q) (hy : y ∈ modelThrough hd J hJ x) :
    modelThrough hd J hJ y=modelThrough hd J hJ x := by
  by_cases hx : x.1=0
  · rw [modelThrough,dite_eq_left hx] at hy
    conv_rhs => rw [modelThrough,dite_eq_left hx]
    rw [modelThrough,dite_eq_left ((mem_modelAxis y).mp hy)]
  · rw [modelThrough,dite_eq_right hx] at hy
    conv_rhs => rw [modelThrough,dite_eq_right hx]
    have hy' := (mem_slabLinePoints _ _ _).mp hy
    have hy0 := slabLine_off_axis J _ hy'
    rw [modelThrough,dite_eq_right hy0]
    rw [← modelFunctional_unique hd J hJ y hy0 _ hy']

def axisPartition : LinePartition (Q := Q) (A := P × Q) :=
  ⟨modelThrough hd J hJ,modelThrough_self hd J hJ,modelThrough_full hd J hJ,modelThrough_stable hd J hJ⟩

lemma axisPartition_through_zero : (axisPartition hd J hJ).through 0 = modelAxis := by
  simp [axisPartition,modelThrough]

lemma axisPartition_projection {x y z : P × Q} (hx : x.1 ≠ 0)
    (hy : y ∈ (axisPartition hd J hJ).through x) (hz : z ∈ (axisPartition hd J hJ).through x)
    (hne : z ≠ y) : z.1-y.1 ≠ 0 := by
  change y ∈ modelThrough hd J hJ x at hy
  change z ∈ modelThrough hd J hJ x at hz
  rw [modelThrough,dite_eq_right hx,mem_slabLinePoints] at hy hz
  intro h
  have he : z.1=y.1 := sub_eq_zero.mp h
  apply hne
  exact Prod.ext he (by rw [hz.2,hy.2,he])

lemma axisPartition_zero_mem_iff (x : P × Q) :
    (0 : P × Q) ∈ (axisPartition hd J hJ).through x ↔ x.1=0 := by
  change 0 ∈ modelThrough hd J hJ x ↔ _
  by_cases hx : x.1=0
  · simp [modelThrough,hx]
  · rw [modelThrough,dite_eq_right hx,mem_slabLinePoints]
    constructor
    · intro h
      exact False.elim (slabLine_off_axis J _ h rfl)
    · exact False.elim ∘ hx

omit [FiniteDimensional Q P] in
def parallelPlanePartition (v : P) (hv : v ≠ 0) : LinePartition (Q := Q) (A := P × Q) where
  through x := linePoints (Q := Q) x (v,0)
  self x := base_mem_linePoints x _
  full x := ⟨x,(v,0),fun h => hv (congrArg Prod.fst h),rfl⟩
  stable _ _ h := linePoints_rebase h

omit [FiniteDimensional Q P] in
lemma parallelPlanePartition_projection (v : P) (hv : v ≠ 0) {x y z : P × Q}
    (hy : y ∈ (parallelPlanePartition v hv).through x)
    (hz : z ∈ (parallelPlanePartition v hv).through x) (hne : z ≠ y) : z.1-y.1 ≠ 0 := by
  obtain ⟨t,rfl⟩ := (mem_linePoints _ _ _).mp hy
  obtain ⟨s,rfl⟩ := (mem_linePoints _ _ _).mp hz
  intro he
  have he' : s • v=t • v := add_left_cancel (sub_eq_zero.mp he)
  have hst := (smul_left_injective Q hv) he'
  exact hne (by rw [hst])

end KaplanskyCounterexample.FiniteGeometry
end

end OAI
end
/- CHECKPOINT: OAI.RingTheory.DirectFiniteness.ModelPartition -/

/- BEGIN PINNED MODULE OAI.RingTheory.DirectFiniteness.SlabPatch -/
section

namespace OAI

universe u_1 u_2 u_3 u_4

noncomputable section
open scoped Classical
open Module
namespace KaplanskyCounterexample.FiniteGeometry
variable {Q : Type u_1} {A : Type u_2} {R : Type u_3} {E : Type u_4} [Field Q] [AddCommGroup A] [Module Q A]
  [AddCommGroup E] [Module Q E] [Fintype A] [Fintype Q] [Fintype E]
namespace DirectionFrame
variable (F : DirectionFrame Q A R E) (j : R × Q) (P : Plane Q E)

def slabImage (o : A) (l : Finset (P.val × Q)) : Finset A :=
  l.image (fun x => o+F.slabMap j P x)

omit [Fintype E] in
lemma slabImage_axis (o : A) : F.slabImage j P o modelAxis = cosetPoints (F.D j) o := by
  ext point
  rw [slabImage,Finset.mem_image,mem_cosetPoints]
  constructor
  · rintro ⟨⟨vector,scalar⟩,membership,rfl⟩
    have vector_zero : vector = 0 := (mem_modelAxis _).mp membership
    subst vector
    exact ⟨scalar,by rw [F.slabMap_axis,add_sub_cancel_left]⟩
  · rintro ⟨scalar,scalar_spec⟩
    refine ⟨(0,scalar),(mem_modelAxis _).mpr rfl,?_⟩
    rw [F.slabMap_axis,scalar_spec,add_comm,sub_add_cancel]

omit [Fintype A] [Fintype Q] [Fintype E] in
lemma slabImage_pair (o : A) (l : Finset (P.val × Q))
    (hproj : ∀ x ∈ l, ∀ y ∈ l, y ≠ x → y.1-x.1 ≠ 0)
    {x y : A} (hx : x ∈ F.slabImage j P o l) (hy : y ∈ F.slabImage j P o l) (hne : y ≠ x) :
    ∃ c : Q, ∃ e : E, e ≠ 0 ∧ e ∈ P.val ∧ F.u j (c,e)=y-x := by
  obtain ⟨x',hx',rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨y',hy',rfl⟩ := Finset.mem_image.mp hy
  have hne' : y' ≠ x' := fun h => hne (h ▸ rfl)
  refine ⟨y'.2-x'.2,y'.1.val-x'.1.val,?_,P.val.sub_mem y'.1.property x'.1.property,?_⟩
  · intro h
    exact hproj x' hx' y' hy' hne' (Subtype.ext h)
  · change F.slabMap j P (y'-x') = _
    rw [map_sub]
    abel

structure SlabPatch (O S : Finset A) where
  partition : PartitionOn (Q := Q) S
  axis : ∀ o : S, o.val ∈ O → partition.through o = cosetPoints (F.D j) o.val
  generic : ∀ x : S, Disjoint (partition.through x) O →
    ∀ y ∈ partition.through x, ∀ z ∈ partition.through x, z ≠ y →
    ∃ c : Q, ∃ e : E, e ≠ 0 ∧ e ∈ P.val ∧ F.u j (c,e)=z-y

lemma axisSlabPatch (o : A) (O : Finset A) (ho : o ∈ O)
    (hu : ∀ x ∈ O, x ∈ cosetPoints (F.slabMap j P).range o → x=o)
    (J : P.val →ₗ[Q] P.val) (hJ : NoEigenvector J) :
    Nonempty (F.SlabPatch j P O (cosetPoints (F.slabMap j P).range o)) := by
  let m := F.slabMap j P
  let hm := F.slabMap_injective j P
  let L := axisPartition P.property J hJ
  let e := PartitionOn.parametrization m hm o
  let T := PartitionOn.image m hm o L
  refine ⟨⟨T,?_,?_⟩⟩
  · intro x hx
    have hxv : x.val=o := hu x.val hx x.property
    have hxe : x=e 0 := Subtype.ext (by simpa [e,PartitionOn.parametrization_val] using hxv)
    rw [hxe]
    change (PartitionOn.image m hm o L).through (PartitionOn.parametrization m hm o 0) = _
    rw [PartitionOn.image_through]
    change F.slabImage j P o ((axisPartition P.property J hJ).through 0) = _
    rw [axisPartition_through_zero,F.slabImage_axis]
    simp [e,PartitionOn.parametrization_val]
  · intro x hx y hy z hz hne
    let x' := e.symm x
    have hxp : x'.1 ≠ 0 := by
      intro he
      have hmem : (0 : P.val × Q) ∈ L.through x' :=
        (axisPartition_zero_mem_iff P.property J hJ x').mpr he
      have hoT : o ∈ T.through x := by
        refine Finset.mem_image.mpr ⟨0,hmem,?_⟩
        simp
      exact Finset.disjoint_left.mp hx hoT ho
    apply F.slabImage_pair j P o (L.through x') _ hy hz hne
    intro a ha b hb hba
    exact axisPartition_projection P.property J hJ hxp ha hb hba

lemma emptySlabPatch (o : A) (O : Finset A)
    (hu : Disjoint O (cosetPoints (F.slabMap j P).range o)) :
    Nonempty (F.SlabPatch j P O (cosetPoints (F.slabMap j P).range o)) := by
  have hn : Nontrivial P.val := Module.nontrivial_of_finrank_pos (by rw [P.property]; decide : 0 < finrank Q P.val)
  obtain ⟨v,hv⟩ := exists_ne (0 : P.val)
  let m := F.slabMap j P
  let hm := F.slabMap_injective j P
  let L := parallelPlanePartition (Q := Q) v hv
  let e := PartitionOn.parametrization m hm o
  let T := PartitionOn.image m hm o L
  refine ⟨⟨T,?_,?_⟩⟩
  · intro x hx
    exact False.elim (Finset.disjoint_left.mp hu hx x.property)
  · intro x _ y hy z hz hne
    apply F.slabImage_pair j P o (L.through (e.symm x)) _ hy hz hne
    intro a ha b hb hba
    exact parallelPlanePartition_projection (Q := Q) v hv ha hb hba

end DirectionFrame
end KaplanskyCounterexample.FiniteGeometry
end

end OAI
end
/- CHECKPOINT: OAI.RingTheory.DirectFiniteness.SlabPatch -/

/- BEGIN PINNED MODULE OAI.RingTheory.DirectFiniteness.PlaneOperators -/
section

namespace OAI

noncomputable section
open Module
namespace KaplanskyCounterexample.FiniteGeometry

lemma exists_plane_operator (Q E : Type) [Field Q] [Fintype Q] [CharP Q 2]
    [AddCommGroup E] [Module Q E] [Fintype E] (P : Plane Q E) :
    ∃ J : P.val →ₗ[Q] P.val, NoEigenvector J := by
  obtain ⟨F,hF,hA,hfin,hD⟩ := exists_finite_extension Q 2 (by decide)
  let _ := hF
  let _ := hA
  let _ := hfin
  have hdP : finrank Q P.val=2 := P.property
  let e : P.val ≃ₗ[Q] F := LinearEquiv.ofFinrankEq _ _ (hdP.trans hD.symm)
  obtain ⟨J,hJ⟩ := exists_noEigenvector_of_quadratic hD
  refine ⟨e.symm.toLinearMap.comp (J.comp e.toLinearMap),?_⟩
  intro x hx c hc
  apply hJ (e x) (fun h => hx (e.injective (h.trans e.map_zero.symm))) c
  have he := congrArg e hc
  simpa only [LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply,map_smul] using he

end KaplanskyCounterexample.FiniteGeometry
end

end OAI
end
/- CHECKPOINT: OAI.RingTheory.DirectFiniteness.PlaneOperators -/

/- BEGIN PINNED MODULE OAI.RingTheory.DirectFiniteness.SlabAssembly -/
section

namespace OAI

noncomputable section
open scoped Classical
namespace KaplanskyCounterexample.FiniteGeometry
variable {Q A R E : Type} [Field Q] [CharP Q 2] [AddCommGroup A] [Module Q A]
  [AddCommGroup E] [Module Q E] [Fintype A] [Fintype Q] [Fintype E]
namespace DirectionFrame
variable (F : DirectionFrame Q A R E) (O : Finset A)
  (P : SlabVariable F → Plane Q E) (hP : F.SuccessfulSlabs O P)

include hP in
lemma SlabKey.exists_patch (j : R × Q) (k : F.SlabKey P j) :
    Nonempty (F.SlabPatch j (P ⟨j,k.1⟩) O (k.points F P j)) := by
  by_cases hh : ∃ o ∈ O, o ∈ k.points F P j
  · obtain ⟨o,ho,hob⟩ := hh
    have he : k.points F P j = cosetPoints (F.slabMap j (P ⟨j,k.1⟩)).range o :=
      (congrArg Subtype.val (AffineCoset.eq_of_mem _ hob)).symm
    rw [he]
    obtain ⟨J,hJ⟩ := exists_plane_operator Q E (P ⟨j,k.1⟩)
    apply F.axisSlabPatch j (P ⟨j,k.1⟩) o O ho _ J hJ
    intro x hx hxb
    exact (k.holes_unique F P j O hP ho hx hob (he ▸ hxb)).symm
  · obtain ⟨o,ho⟩ := k.nonempty F P j
    have he : k.points F P j = cosetPoints (F.slabMap j (P ⟨j,k.1⟩)).range o :=
      (congrArg Subtype.val (AffineCoset.eq_of_mem _ ho)).symm
    rw [he]
    apply F.emptySlabPatch j (P ⟨j,k.1⟩) o O
    rw [Finset.disjoint_left]
    intro x hx hxb
    exact hh ⟨x,hx,he ▸ hxb⟩

structure Preliminary where
  part : R × Q → LinePartition (Q := Q) (A := A)
  axis : ∀ j o, o ∈ O → (part j).through o = cosetPoints (F.D j) o
  generic : ∀ j x, Disjoint ((part j).through x) O →
    ∀ y ∈ (part j).through x, ∀ z ∈ (part j).through x, z ≠ y →
    ∃ c : Q, ∃ e : E, e ≠ 0 ∧ e ∈ (P ⟨j,AffineCoset.of (F.U j) y⟩).val ∧ F.u j (c,e)=z-y

include hP in
lemma exists_preliminary : Nonempty (F.Preliminary O P) := by
  let T : ∀ j (k : F.SlabKey P j), F.SlabPatch j (P ⟨j,k.1⟩) O (k.points F P j) :=
    fun j k => (k.exists_patch F O P hP j).some
  let L (j : R × Q) : LinePartition (Q := Q) (A := A) :=
    gluePartition (fun k : F.SlabKey P j => k.points F P j) (F.slabKeyOf P j)
      (F.mem_slabKeyOf P j) (F.slabKeyOf_stable P j) (fun k => (T j k).partition)
  refine ⟨⟨L,?_,?_⟩⟩
  · intro j o ho
    exact (T j (F.slabKeyOf P j o)).axis ⟨o,F.mem_slabKeyOf P j o⟩ ho
  · intro j x hx y hy z hz hne
    let k := F.slabKeyOf P j x
    have hh := (T j k).generic ⟨x,F.mem_slabKeyOf P j x⟩ hx y hy z hz hne
    have hyC : y ∈ k.1.val := k.2.property ((T j k).partition.subset _ hy)
    have he : AffineCoset.of (F.U j) y = k.1 := AffineCoset.eq_of_mem _ hyC
    simpa only [he] using hh

end DirectionFrame
end KaplanskyCounterexample.FiniteGeometry
end

end OAI
end
/- CHECKPOINT: OAI.RingTheory.DirectFiniteness.SlabAssembly -/

/- BEGIN PINNED MODULE OAI.RingTheory.DirectFiniteness.TradeLines -/
section

namespace OAI

universe u_1 u_2 u_3 u_4

noncomputable section
open scoped Classical
namespace KaplanskyCounterexample.FiniteGeometry
variable {Q : Type u_1} {A : Type u_2} {R : Type u_3} {E : Type u_4} [Field Q] [AddCommGroup A] [Module Q A]
  [AddCommGroup E] [Module Q E] [Fintype A] [Fintype Q]
namespace DirectionFrame
variable (F : DirectionFrame Q A R E)

lemma coset_range_eq_line (f : Q →ₗ[Q] A) (o : A) :
    cosetPoints f.range o = linePoints (Q := Q) o (f 1) := by
  ext y
  rw [mem_cosetPoints,mem_linePoints]
  constructor
  · rintro ⟨t,ht⟩
    exact ⟨t,by rw [← f.map_smul]; simpa using (eq_add_of_sub_eq' ht.symm).symm⟩
  · rintro ⟨t,rfl⟩
    exact ⟨t,by simp [← map_smul]⟩

lemma coset_range_full (f : Q →ₗ[Q] A) (hf : Function.Injective f) (o : A) :
    FullLine (Q := Q) (cosetPoints f.range o) := by
  rw [coset_range_eq_line]
  exact ⟨o,f 1,fun h => one_ne_zero (hf (h.trans f.map_zero.symm)),rfl⟩

def replacementLine (r : R) (o : A) (a : Q) : Finset A :=
  cosetPoints (F.exceptional r) (o+F.w r (a,0))

omit [Fintype Q] in
lemma mem_replacementLine (r : R) (o x : A) (a : Q) :
    x ∈ F.replacementLine r o a ↔ ∃ b : Q, F.w r (a,b)=x-o := by
  rw [replacementLine, mem_cosetPoints]
  change (∃ b : Q, F.exc r b = x - (o + F.w r (a, 0))) ↔ _
  constructor
  · rintro ⟨b,hb⟩
    refine ⟨b,?_⟩
    have he : (a,b)=(a,0)+(0,b) := by simp
    rw [he,map_add,← F.exc_apply,hb]
    abel
  · rintro ⟨b,hb⟩
    refine ⟨b,?_⟩
    have he : (0,b)=(a,b)-(a,0) := by simp
    rw [exc_apply,he,map_sub,hb]
    abel

lemma replacementLine_full (r : R) (o : A) (a : Q) :
    FullLine (Q := Q) (F.replacementLine r o a) := coset_range_full (F.exc r) (F.exc_injective r) _

omit [Fintype Q] in
lemma replacementLine_subset (r : R) (o : A) (a : Q) :
    F.replacementLine r o a ⊆ cosetPoints (F.W r) o := by
  intro x hx
  obtain ⟨b,hb⟩ := (F.mem_replacementLine r o x a).mp hx
  exact (mem_cosetPoints _ _ _).mpr ⟨(a,b),hb⟩

omit [Fintype Q] in
lemma replacementLine_hole_free (S O : Finset A)
    (hO : HoleEvents.GoodHoles S F.W F.U (fun r t => F.exc r t) O)
    (r : R) (o : O) (a : Q) (ha : a ≠ 0) : Disjoint (F.replacementLine r o.val a) O := by
  rw [Finset.disjoint_left]
  intro x hx hxO
  have hxo := hO.collision r o.val o.property x hxO ((mem_cosetPoints _ _ _).mp (F.replacementLine_subset r o.val a hx))
  obtain ⟨b,hb⟩ := (F.mem_replacementLine r o.val x a).mp hx
  rw [hxo,sub_self] at hb
  have he := F.winj r (hb.trans (F.w r).map_zero.symm)
  exact ha (congrArg Prod.fst he)

omit [Fintype Q] in
lemma replacementLine_same_label (S O : Finset A)
    (hO : HoleEvents.GoodHoles S F.W F.U (fun r t => F.exc r t) O)
    {r : R} {o o' : O} {a a' : Q} {x : A}
    (hx : x ∈ F.replacementLine r o.val a) (hx' : x ∈ F.replacementLine r o'.val a') :
    o=o' ∧ a=a' := by
  obtain ⟨b,hb⟩ := (F.mem_replacementLine r o.val x a).mp hx
  obtain ⟨b',hb'⟩ := (F.mem_replacementLine r o'.val x a').mp hx'
  have hdiff : o'.val-o.val ∈ F.W r := by
    convert (F.W r).sub_mem (show x-o.val ∈ F.W r from ⟨(a,b),hb⟩)
      (show x-o'.val ∈ F.W r from ⟨(a',b'),hb'⟩) using 1; abel
  have hoo' : o'=o := Subtype.ext (hO.collision r o.val o.property o'.val o'.property hdiff)
  subst o'
  exact ⟨rfl,congrArg Prod.fst (F.winj r (hb.trans hb'.symm))⟩

omit [Fintype Q] in
lemma replacementLine_step {r : R} {o x y : A} {a : Q}
    (hx : x ∈ F.replacementLine r o a) (hy : y ∈ F.replacementLine r o a)
    (hne : y ≠ x) : ∃ t : Q, t ≠ 0 ∧ F.exc r t=y-x := by
  obtain ⟨b,hb⟩ := (F.mem_replacementLine r o x a).mp hx
  obtain ⟨c,hc⟩ := (F.mem_replacementLine r o y a).mp hy
  have he : F.exc r (c-b)=y-x := by
    change F.w r (0,c-b)=_
    have he' : (0,c-b)=(a,c)-(a,b) := by simp
    rw [he',map_sub,hc,hb]
    abel
  refine ⟨c-b,?_,he⟩
  intro hz
  rw [hz,map_zero] at he
  exact hne (sub_eq_zero.mp he.symm)

end DirectionFrame
end KaplanskyCounterexample.FiniteGeometry
end

end OAI
end
/- CHECKPOINT: OAI.RingTheory.DirectFiniteness.TradeLines -/

/- BEGIN PINNED MODULE OAI.RingTheory.DirectFiniteness.TradeFamily -/
section

namespace OAI

noncomputable section
open scoped Classical
namespace KaplanskyCounterexample.FiniteGeometry
variable {Q A R E : Type} [Field Q] [AddCommGroup A] [Module Q A]
  [AddCommGroup E] [Module Q E] [Fintype A] [Fintype Q]
namespace DirectionFrame
variable (F : DirectionFrame Q A R E) (S O : Finset A)
  (P : SlabVariable F → Plane Q E) (T : F.Preliminary O P)

def LiveLine (j : R × Q) := {l : Finset A // (∃ x, (T.part j).through x=l) ∧ Disjoint l O}
def LiveIndex := Σ j, F.LiveLine O P T j
def NewIndex := R × O × {a : Q // a ≠ 0}
def TradeIndex := F.LiveIndex O P T ⊕ NewIndex (Q := Q) (R := R) O

def tradeLine : F.TradeIndex O P T → Finset A
  | .inl g => g.2.val
  | .inr h => F.replacementLine h.1 h.2.1.val h.2.2.val

def tradeLabel : F.TradeIndex O P T → (R × Q) ⊕ R
  | .inl g => .inl g.1
  | .inr h => .inr h.1

instance [Fintype R] : Fintype (F.LiveIndex O P T) := by unfold LiveIndex LiveLine; infer_instance
instance [Fintype R] : Fintype (F.TradeIndex O P T) := by unfold TradeIndex NewIndex; infer_instance

lemma live_through {j : R × Q} (l : F.LiveLine O P T j) {x : A} (hx : x ∈ l.val) :
    (T.part j).through x=l.val := by
  obtain ⟨a,ha⟩ := l.property.1
  exact ((T.part j).stable a x (ha ▸ hx)).trans ha

lemma live_full {j : R × Q} (l : F.LiveLine O P T j) : FullLine (Q := Q) l.val := by
  obtain ⟨x,hx⟩ := l.property.1
  rw [← hx]
  exact (T.part j).full x

lemma tradeLine_full (i : F.TradeIndex O P T) : FullLine (Q := Q) (F.tradeLine O P T i) := by
  cases i with
  | inl l => exact F.live_full O P T l.2
  | inr h => exact F.replacementLine_full h.1 h.2.1.val h.2.2.val

lemma tradeLine_avoid (hO : HoleEvents.GoodHoles S F.W F.U (fun r t => F.exc r t) O)
    (i : F.TradeIndex O P T) : Disjoint (F.tradeLine O P T i) O := by
  cases i with
  | inl g => exact g.2.property.2
  | inr h => exact F.replacementLine_hole_free S O hO h.1 h.2.1 h.2.2.val h.2.2.property

lemma same_label_eq (hO : HoleEvents.GoodHoles S F.W F.U (fun r t => F.exc r t) O)
    {i i' : F.TradeIndex O P T} (hl : F.tradeLabel O P T i=F.tradeLabel O P T i')
    {x : A} (hx : x ∈ F.tradeLine O P T i) (hx' : x ∈ F.tradeLine O P T i') : i=i' := by
  cases i with
  | inl g => cases i' with
    | inl g' =>
      obtain ⟨j,l⟩ := g
      obtain ⟨j',l'⟩ := g'
      have hj := Sum.inl.inj hl
      change j=j' at hj
      subst j'
      have he : l=l' := Subtype.ext ((F.live_through O P T l hx).symm.trans (F.live_through O P T l' hx'))
      subst l'
      rfl
    | inr h => cases hl
  | inr h => cases i' with
    | inl g => cases hl
    | inr h' =>
      obtain ⟨r,o,a⟩ := h
      obtain ⟨r',o',a'⟩ := h'
      have hr := Sum.inr.inj hl
      change r=r' at hr
      subst r'
      obtain ⟨ho,ha⟩ := F.replacementLine_same_label S O hO hx hx'
      exact congrArg Sum.inr (Prod.ext rfl (Prod.ext ho (Subtype.ext ha)))

lemma live_step {j : R × Q} (l : F.LiveLine O P T j) {x y : A}
    (hx : x ∈ l.val) (hy : y ∈ l.val) (hne : y ≠ x) :
    ∃ c : Q, ∃ e : E, e ≠ 0 ∧ e ∈ (P ⟨j,AffineCoset.of (F.U j) x⟩).val ∧ F.u j (c,e)=y-x := by
  have he := F.live_through O P T l hx
  exact T.generic j x (he ▸ l.property.2) x (he ▸ hx) y (he ▸ hy) hne

lemma tradeLine_step_mem (i : F.TradeIndex O P T) {x y : A}
    (hx : x ∈ F.tradeLine O P T i) (hy : y ∈ F.tradeLine O P T i) :
    y-x ∈ Sum.elim F.U F.exceptional (F.tradeLabel O P T i) := by
  by_cases hne : y=x
  · simp [hne]
  cases i with
  | inl g =>
    obtain ⟨c,e,_,_,he⟩ := F.live_step O P T g.2 hx hy hne
    exact ⟨(c,e),he⟩
  | inr h =>
    obtain ⟨t,_,ht⟩ := F.replacementLine_step hx hy hne
    exact ⟨t,ht⟩

lemma removed_iff (j : R × Q) (x : A) :
    ¬ Disjoint ((T.part j).through x) O ↔ ∃ o ∈ O, x ∈ cosetPoints (F.D j) o := by
  rw [Finset.not_disjoint_iff]
  constructor
  · rintro ⟨o,ho,hoO⟩
    refine ⟨o,hoO,?_⟩
    have he := (T.part j).stable x o ho
    rw [T.axis j o hoO] at he
    rw [he]
    exact (T.part j).self x
  · rintro ⟨o,ho,hx⟩
    have hh : x ∈ (T.part j).through o := (T.axis j o ho) ▸ hx
    have he := (T.part j).stable o x hh
    exact ⟨o,he ▸ (T.part j).self o,ho⟩

end DirectionFrame
end KaplanskyCounterexample.FiniteGeometry
end

end OAI
end
/- CHECKPOINT: OAI.RingTheory.DirectFiniteness.TradeFamily -/

/- BEGIN PINNED MODULE OAI.RingTheory.DirectFiniteness.TradeDegree -/
section

namespace OAI

noncomputable section
open scoped Classical
namespace KaplanskyCounterexample.FiniteGeometry
variable {Q A R E : Type} [Field Q] [AddCommGroup A] [Module Q A]
  [AddCommGroup E] [Module Q E] [Fintype A] [Fintype Q] [Fintype R]
namespace DirectionFrame
variable (F : DirectionFrame Q A R E) (S O : Finset A)
  (P : SlabVariable F → Plane Q E) (T : F.Preliminary O P)

def KeptAt (x : A) := {j : R × Q // Disjoint ((T.part j).through x) O}
def RemovedAt (x : A) := {j : R × Q // ¬ Disjoint ((T.part j).through x) O}
def NewAt (x : A) := {i : NewIndex (Q := Q) (R := R) O //
  x ∈ F.replacementLine i.1 i.2.1.val i.2.2.val}
def LiveAt (x : A) := {i : F.LiveIndex O P T // x ∈ i.2.val}

instance (x : A) : Fintype (F.NewAt O x) := by unfold NewAt NewIndex; infer_instance
instance (x : A) : Fintype (F.LiveAt O P T x) := by unfold LiveAt; infer_instance
instance (x : A) : Fintype (F.KeptAt O P T x) := by unfold KeptAt; infer_instance
instance (x : A) : Fintype (F.RemovedAt O P T x) := by unfold RemovedAt; infer_instance

lemma liveAt_card (x : A) : Fintype.card (F.LiveAt O P T x) = Fintype.card (F.KeptAt O P T x) := by
  let f : F.LiveAt O P T x → F.KeptAt O P T x := fun g =>
    ⟨g.val.1,by rw [F.live_through O P T g.val.2 g.property]; exact g.val.2.property.2⟩
  apply Fintype.card_congr (Equiv.ofBijective f ?_)
  constructor
  · rintro ⟨⟨j,l⟩,hx⟩ ⟨⟨j',l'⟩,hx'⟩ he
    have hj : j=j' := congrArg Subtype.val he
    subst j'
    have hl : l=l' := Subtype.ext ((F.live_through O P T l hx).symm.trans (F.live_through O P T l' hx'))
    subst l'
    rfl
  · intro j
    refine ⟨⟨⟨j.val,⟨(T.part j.val).through x,⟨⟨x,rfl⟩,j.property⟩⟩⟩,(T.part j.val).self x⟩,?_⟩
    rfl

/-- The second coordinate of a point on a replacement line. -/
def newCoord {x : A} (i : F.NewAt O x) : Q :=
  ((F.mem_replacementLine i.val.1 i.val.2.1.val x i.val.2.2.val).mp i.property).choose

omit [Fintype Q] [Fintype R] in
lemma newCoord_spec {x : A} (i : F.NewAt O x) :
    F.w i.val.1 (i.val.2.2.val,F.newCoord O i)=x-i.val.2.1.val :=
  ((F.mem_replacementLine i.val.1 i.val.2.1.val x i.val.2.2.val).mp i.property).choose_spec

def newLabel {x : A} (i : F.NewAt O x) : R × Q :=
  (i.val.1, F.newCoord O i / i.val.2.2.val)

omit [Fintype Q] [Fintype R] in
lemma newLabel_axis {x : A} (i : F.NewAt O x) :
    x ∈ cosetPoints (F.D (F.newLabel O i)) i.val.2.1.val := by
  apply (mem_cosetPoints _ _ _).mpr
  refine ⟨i.val.2.2.val,?_⟩
  change F.w i.val.1 (i.val.2.2.val,i.val.2.2.val*(F.newCoord O i / i.val.2.2.val)) = _
  rw [mul_div_cancel₀ _ i.val.2.2.property]
  exact F.newCoord_spec O i

omit [Fintype Q] [Fintype R] in
lemma newLabel_injective (hO : HoleEvents.GoodHoles S F.W F.U (fun r t => F.exc r t) O)
    (x : A) : Function.Injective (F.newLabel O (x := x)) := by
  intro i i' he
  have hr := congrArg (fun j : R × Q => j.1) he
  change i.val.1=i'.val.1 at hr
  have hx := F.replacementLine_same_label S O hO i.property
    (show x ∈ F.replacementLine i.val.1 i'.val.2.1.val i'.val.2.2.val by rw [hr]; exact i'.property)
  apply Subtype.ext
  exact Prod.ext hr (Prod.ext hx.1 (Subtype.ext hx.2))

omit [Fintype R] in
lemma newLabel_surjective (x : A) (hx : x ∉ O) (j : F.RemovedAt O P T x) :
    ∃ i : F.NewAt O x, F.newLabel O i=j.val := by
  obtain ⟨o,ho,haxis⟩ := (F.removed_iff O P T j.val x).mp j.property
  obtain ⟨a,ha⟩ := (mem_cosetPoints _ _ _).mp haxis
  have han : a ≠ 0 := by
    intro hz
    subst a
    rw [map_zero] at ha
    have hxo : x=o := sub_eq_zero.mp ha.symm
    exact hx (hxo ▸ ho)
  let i : F.NewAt O x := ⟨(j.val.1,⟨o,ho⟩,⟨a,han⟩),
    (F.mem_replacementLine j.val.1 o x a).mpr ⟨a*j.val.2,ha⟩⟩
  refine ⟨i,Prod.ext rfl ?_⟩
  have hc : F.newCoord O i=a*j.val.2 := congrArg Prod.snd (F.winj j.val.1 ((F.newCoord_spec O i).trans ha.symm))
  change F.newCoord O i / a=j.val.2
  rw [hc,mul_div_cancel_left₀ _ han]

lemma newAt_card (hO : HoleEvents.GoodHoles S F.W F.U (fun r t => F.exc r t) O)
    (x : A) (hx : x ∉ O) : Fintype.card (F.NewAt O x) = Fintype.card (F.RemovedAt O P T x) := by
  let f : F.NewAt O x → F.RemovedAt O P T x := fun i =>
    ⟨F.newLabel O i,(F.removed_iff O P T _ x).mpr ⟨i.val.2.1.val,i.val.2.1.property,F.newLabel_axis O i⟩⟩
  apply Fintype.card_congr (Equiv.ofBijective f ?_)
  constructor
  · intro i i' he
    exact F.newLabel_injective S O hO x (congrArg Subtype.val he)
  · intro j
    obtain ⟨i,hi⟩ := F.newLabel_surjective O P T x hx j
    exact ⟨i,Subtype.ext hi⟩

lemma trade_degree (hO : HoleEvents.GoodHoles S F.W F.U (fun r t => F.exc r t) O)
    (x : A) (hx : x ∉ O) :
    Fintype.card {i : F.TradeIndex O P T // x ∈ F.tradeLine O P T i} = Fintype.card R*Fintype.card Q := by
  let : Fintype (NewIndex (Q := Q) (R := R) O) := by unfold NewIndex; infer_instance
  have he : Fintype.card {i : F.TradeIndex O P T // x ∈ F.tradeLine O P T i} =
      Fintype.card (F.LiveAt O P T x)+Fintype.card (F.NewAt O x) := by
    let e : {i : F.TradeIndex O P T // x ∈ F.tradeLine O P T i} ≃
        F.LiveAt O P T x ⊕ F.NewAt O x := {
      toFun := fun i => match i with
        | ⟨.inl g,hg⟩ => .inl ⟨g,hg⟩
        | ⟨.inr h,hh⟩ => .inr ⟨h,hh⟩
      invFun := fun i => match i with
        | .inl g => ⟨.inl g.val,g.property⟩
        | .inr h => ⟨.inr h.val,h.property⟩
      left_inv := by rintro ⟨g,hg⟩; cases g <;> rfl
      right_inv := by intro g; cases g <;> rfl }
    exact (Fintype.card_congr e).trans Fintype.card_sum
  rw [he,F.liveAt_card O P T x,F.newAt_card S O P T hO x hx]
  change Fintype.card {j : R × Q // Disjoint ((T.part j).through x) O} +
    Fintype.card {j : R × Q // ¬ Disjoint ((T.part j).through x) O} = _
  rw [Fintype.card_subtype_compl, Nat.add_sub_of_le (Fintype.card_subtype_le _),Fintype.card_prod]

end DirectionFrame
end KaplanskyCounterexample.FiniteGeometry
end

end OAI
end
/- CHECKPOINT: OAI.RingTheory.DirectFiniteness.TradeDegree -/

/- BEGIN PINNED MODULE OAI.RingTheory.DirectFiniteness.TradePolygon -/
section

namespace OAI

universe u_1

noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample.FiniteGeometry
variable {Q A R E : Type} [Field Q] [AddCommGroup A] [Module Q A]
  [AddCommGroup E] [Module Q E] [Fintype A] [Fintype Q]
namespace DirectionFrame
variable (F : DirectionFrame Q A R E) (O : Finset A)
  (P : SlabVariable F → Plane Q E) (T : F.Preliminary O P)

lemma exists_trade_step (i : F.TradeIndex O P T) {x y : A}
    (hx : x ∈ F.tradeLine O P T i) (hy : y ∈ F.tradeLine O P T i) (hne : y ≠ x) :
    ∃ s : PolygonStep Q R E, s.label=F.tradeLabel O P T i ∧ s.vector F=y-x ∧
      (∀ g : GenericStep Q R E, s=.inl g → g.component ∈ (P ⟨g.label,AffineCoset.of (F.U g.label) x⟩).val) ∧
      (∀ e : ExceptionalStep Q R, s=.inr e → x ∈ F.replacementRegion O e.label ∧ y ∈ F.replacementRegion O e.label) := by
  cases i with
  | inl l =>
    obtain ⟨c,e,he,hP,hv⟩ := F.live_step O P T l.2 hx hy hne
    refine ⟨.inl ⟨l.1,c,e,he⟩,rfl,hv,?_,?_⟩
    · intro g hg
      cases Sum.inl.inj hg
      exact hP
    · intro g hg; cases hg
  | inr h =>
    obtain ⟨t,ht,hv⟩ := F.replacementLine_step hx hy hne
    refine ⟨.inr ⟨h.1,t,ht⟩,rfl,hv,?_,?_⟩
    · intro g hg; cases hg
    · intro g hg
      cases Sum.inr.inj hg
      constructor
      · exact (F.mem_replacementRegion O _ _).mpr ⟨h.2.1.val,h.2.1.property,
          (mem_cosetPoints _ _ _).mp (F.replacementLine_subset _ _ _ hx)⟩
      · exact (F.mem_replacementRegion O _ _).mpr ⟨h.2.1.val,h.2.1.property,
          (mem_cosetPoints _ _ _).mp (F.replacementLine_subset _ _ _ hy)⟩

lemma no_generic_trade_polygon (hP : F.SuccessfulSlabs O P) {k : ℕ} (hk3 : 3 ≤ k) (hk5 : k ≤ 5)
    (point : Fin k → A) (line : Fin k → F.TradeIndex O P T)
    (hne : ∀ i, point (finRotate k i) ≠ point i)
    (hadj : ∀ i, F.tradeLabel O P T (line i) ≠ F.tradeLabel O P T (line (finRotate k i)))
    (hx : ∀ i, point i ∈ F.tradeLine O P T (line i))
    (hy : ∀ i, point (finRotate k i) ∈ F.tradeLine O P T (line i))
    (hg : ∃ i j, F.tradeLabel O P T (line i)=.inl j) : False := by
  choose step hlabel hvec hplane hexc using fun i => F.exists_trade_step O P T (line i) (hx i) (hy i) (hne i)
  let c : Candidate F (F.replacementRegion O) k := {
    step := step
    point := point
    shift := fun i => (hvec i).symm
    adjacent := fun i => by rw [hlabel,hlabel]; exact hadj i
    exceptional := hexc
    generic := by obtain ⟨i,j,hj⟩ := hg; exact ⟨i,j,(hlabel i).trans hj⟩ }
  obtain ⟨v,hv,hn⟩ := hP.candidates k hk3 hk5 c
  obtain ⟨p,rfl⟩ := (c.mem_deps_iff F (F.replacementRegion O) v).mp hv
  rw [c.constraintVector_at F (F.replacementRegion O) hk3 hk5 p] at hn
  exact hn (hplane p.val.1 p.val.2 p.property)

end DirectionFrame

lemma four_labels_alternate {L : Type u_1} [DecidableEq L] (lab : Fin 4 → L)
    (hadj : ∀ i, lab i ≠ lab (finRotate 4 i))
    (hc : ∀ l, (∃ i, lab i=l) → (Finset.univ.filter (fun i => lab i=l)).card=2) :
    lab 0=lab 2 ∧ lab 1=lab 3 := by
  have h01 : lab 0 ≠ lab 1 := hadj 0
  have h12 : lab 1 ≠ lab 2 := hadj 1
  have h23 : lab 2 ≠ lab 3 := hadj 2
  have h30 : lab 3 ≠ lab 0 := hadj 3
  constructor
  · by_contra hh
    have ht := hc (lab 0) ⟨0,rfl⟩
    have he : (∑ i : Fin 4, if lab i=lab 0 then (1:ℕ) else 0)=2 := by simpa using ht
    simp only [Fin.sum_univ_succ,Fin.sum_univ_zero] at he
    change ((if True then 1 else 0) + ((if lab 1=lab 0 then 1 else 0) + ((if lab 2=lab 0 then 1 else 0) + ((if lab 3=lab 0 then 1 else 0) + 0))))=2 at he
    norm_num [h01.symm,Ne.symm hh,h30] at he
  · by_contra hh
    have ht := hc (lab 1) ⟨1,rfl⟩
    have he : (∑ i : Fin 4, if lab i=lab 1 then (1:ℕ) else 0)=2 := by simpa using ht
    simp only [Fin.sum_univ_succ,Fin.sum_univ_zero] at he
    change ((if lab 0=lab 1 then 1 else 0) + ((if lab 1=lab 1 then 1 else 0) + ((if lab 2=lab 1 then 1 else 0) + ((if lab 3=lab 1 then 1 else 0) + 0))))=2 at he
    norm_num [h01,h12.symm,Ne.symm hh] at he

end KaplanskyCounterexample.FiniteGeometry
end

end OAI
end
/- CHECKPOINT: OAI.RingTheory.DirectFiniteness.TradePolygon -/

/- BEGIN PINNED MODULE OAI.RingTheory.DirectFiniteness.ReplacementPolygon -/
section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample.FiniteGeometry
variable {Q A R E : Type} [Field Q] [AddCommGroup A] [Module Q A]
  [AddCommGroup E] [Module Q E] [Fintype A] [Fintype Q]
namespace DirectionFrame
variable (F : DirectionFrame Q A R E) (S O : Finset A)

omit [Fintype Q] in
lemma replacement_adj_holes_ne
    (hO : HoleEvents.GoodHoles S F.W F.U (fun r t => F.exc r t) O)
    {r s : R} (hrs : r ≠ s) {o o' : O} {a b : Q} (ha : a ≠ 0) {x : A}
    (hx : x ∈ F.replacementLine r o.val a) (hy : x ∈ F.replacementLine s o'.val b) : o ≠ o' := by
  intro he
  subst o'
  have hxW := (mem_cosetPoints _ _ _).mp (F.replacementLine_subset _ _ _ hx)
  have hyW := (mem_cosetPoints _ _ _).mp (F.replacementLine_subset _ _ _ hy)
  have hz := Submodule.disjoint_def.mp (F.W_disjoint hrs) (x-o.val) hxW hyW
  have hxo := sub_eq_zero.mp hz
  exact Finset.disjoint_left.mp (F.replacementLine_hole_free S O hO r o a ha) hx (hxo ▸ o.property)

omit [Fintype Q] in
lemma replacement_opposite_holes_ne {r s : R} (hrs : r ≠ s)
    {o o' : O} {a b : Q} {x y : A}
    (hx : x ∈ F.replacementLine r o.val a) (hy : y ∈ F.replacementLine r o'.val b)
    (hxy : y-x ∈ F.W s) (hne : y ≠ x) : o ≠ o' := by
  intro he
  subst o'
  have hxW := (mem_cosetPoints _ _ _).mp (F.replacementLine_subset _ _ _ hx)
  have hyW := (mem_cosetPoints _ _ _).mp (F.replacementLine_subset _ _ _ hy)
  have hW : y-x ∈ F.W r := by convert (F.W r).sub_mem hyW hxW using 1; abel
  exact hne (sub_eq_zero.mp (Submodule.disjoint_def.mp (F.W_disjoint hrs) _ hW hxy))

omit [Fintype Q] in
lemma no_replacement_quad
    (hO : HoleEvents.GoodHoles S F.W F.U (fun r t => F.exc r t) O)
    (point : Fin 4 → A) (line : Fin 4 → NewIndex (Q := Q) (R := R) O)
    (hne : ∀ i, point (finRotate 4 i) ≠ point i)
    (hadj : ∀ i, (line i).1 ≠ (line (finRotate 4 i)).1)
    (halt : (line 0).1=(line 2).1 ∧ (line 1).1=(line 3).1)
    (hx : ∀ i, point i ∈ F.replacementLine (line i).1 (line i).2.1.val (line i).2.2.val)
    (hy : ∀ i, point (finRotate 4 i) ∈ F.replacementLine (line i).1 (line i).2.1.val (line i).2.2.val) : False := by
  have h01 : (line 0).1 ≠ (line 1).1 := hadj 0
  have h12 : (line 1).1 ≠ (line 2).1 := hadj 1
  have h23 : (line 2).1 ≠ (line 3).1 := hadj 2
  have h30 : (line 3).1 ≠ (line 0).1 := hadj 3
  have hw (i : Fin 4) : point (finRotate 4 i)-point i ∈ F.W (line i).1 := by
    convert (F.W (line i).1).sub_mem
      ((mem_cosetPoints _ _ _).mp (F.replacementLine_subset _ _ _ (hy i)))
      ((mem_cosetPoints _ _ _).mp (F.replacementLine_subset _ _ _ (hx i))) using 1; abel
  have ho01 := F.replacement_adj_holes_ne S O hO h01 (line 0).2.2.property (hy 0) (hx 1)
  have ho12 := F.replacement_adj_holes_ne S O hO h12 (line 1).2.2.property (hy 1) (hx 2)
  have ho23 := F.replacement_adj_holes_ne S O hO h23 (line 2).2.2.property (hy 2) (hx 3)
  have ho30 := F.replacement_adj_holes_ne S O hO h30 (line 3).2.2.property (hy 3) (hx 0)
  have ho02 : (line 0).2.1 ≠ (line 2).2.1 := by
    apply F.replacement_opposite_holes_ne O h01 (hy 0)
      (show point 2 ∈ F.replacementLine (line 0).1 (line 2).2.1.val (line 2).2.2.val by rw [halt.1]; exact hx 2)
      (hw 1) (hne 1)
  have ho13 : (line 1).2.1 ≠ (line 3).2.1 := by
    apply F.replacement_opposite_holes_ne O h12 (hy 1)
      (show point 3 ∈ F.replacementLine (line 1).1 (line 3).2.1.val (line 3).2.2.val by rw [halt.2]; exact hx 3)
      (hw 2) (hne 2)
  have hinj : Function.Injective (fun i : Fin 4 => (line i).2.1.val) := by
    intro i j hij
    have he : (line i).2.1=(line j).2.1 := Subtype.ext hij
    fin_cases i <;> fin_cases j <;> simp_all
  obtain ⟨u,_,hu⟩ := F.replacementLine_step (hx 0) (hy 0) (hne 0)
  obtain ⟨v,_,hv⟩ := F.replacementLine_step (hx 1) (hy 1) (hne 1)
  change F.exc (line 0).1 u=point 1-point 0 at hu
  change F.exc (line 1).1 v=point 2-point 1 at hv
  have hp1 : point 1=point 0+F.exc (line 0).1 u := eq_add_of_sub_eq' hu.symm
  have hp2 : point 2=point 0+F.exc (line 0).1 u+F.exc (line 1).1 v := by
    rw [← hp1]
    exact eq_add_of_sub_eq' hv.symm
  have hw0 : point 1-point 0 ∈ F.W (line 0).1 := hw 0
  have hw1 : point 2-point 1 ∈ F.W (line 1).1 := hw 1
  have hw2 : point 3-point 2 ∈ F.W (line 0).1 := by
    rw [halt.1]; exact hw 2
  have hw3 : point 0-point 3 ∈ F.W (line 1).1 := by
    rw [halt.2]; exact hw 3
  have hd : (point 3-point 0)-(point 2-point 1)=0 := by
    apply Submodule.disjoint_def.mp (F.W_disjoint h01)
    · have hh := (F.W (line 0).1).add_mem hw2 hw0
      convert hh using 1; abel
    · have hh := (F.W (line 1).1).sub_mem ((F.W (line 1).1).neg_mem hw3) hw1
      convert hh using 1; abel
  have hp3 : point 3=point 0+F.exc (line 1).1 v := by
    change F.exc (line 1).1 v=point 2-point 1 at hv
    rw [← hv] at hd
    exact (sub_eq_iff_eq_add.mp (sub_eq_zero.mp hd)).trans (add_comm _ _)
  apply hO.rectangles (line 0).1 (line 1).1 (point 0) u v (fun i => (line i).2.1.val) hinj
    (fun i => (line i).2.1.property)
  intro i
  have hm := (F.W (line i).1).neg_mem ((mem_cosetPoints _ _ _).mp (F.replacementLine_subset _ _ _ (hx i)))
  have he : -(point i-(line i).2.1.val)=(line i).2.1.val-point i := by abel
  rw [he] at hm
  fin_cases i
  · exact hm
  · change (line 1).2.1.val-(point 0+F.exc (line 0).1 u) ∈ F.W (line 1).1
    rw [← hp1]
    exact hm
  · change (line 2).2.1.val-(point 0+F.exc (line 0).1 u+F.exc (line 1).1 v) ∈ F.W (line 0).1
    rw [← hp2,halt.1]
    exact hm
  · change (line 3).2.1.val-(point 0+F.exc (line 1).1 v) ∈ F.W (line 1).1
    rw [← hp3,halt.2]
    exact hm

omit [Fintype Q] in
lemma no_replacement_polygon
    (hO : HoleEvents.GoodHoles S F.W F.U (fun r t => F.exc r t) O)
    {k : ℕ} (hk3 : 3 ≤ k) (hk5 : k ≤ 5)
    (point : Fin k → A) (line : Fin k → NewIndex (Q := Q) (R := R) O)
    (hne : ∀ i, point (finRotate k i) ≠ point i)
    (hadj : ∀ i, (line i).1 ≠ (line (finRotate k i)).1)
    (hx : ∀ i, point i ∈ F.replacementLine (line i).1 (line i).2.1.val (line i).2.2.val)
    (hy : ∀ i, point (finRotate k i) ∈ F.replacementLine (line i).1 (line i).2.1.val (line i).2.2.val) : False := by
  choose u hu hv using fun i => F.replacementLine_step (hx i) (hy i) (hne i)
  let step (i : Fin k) : PolygonStep Q R E := .inr ⟨(line i).1,u i,hu i⟩
  have hz := F.closed_of_points step point (fun i => (hv i).symm)
  have hs : ∀ i, (step i).label ≠ (step (finRotate k i)).label := by
    intro i he
    exact hadj i (Sum.inr.inj he)
  have hc (r : R) (hr : ∃ i, (line i).1=r) :
      (Finset.univ.filter (fun i => (line i).1=r)).card=2 := by
    have he := F.exceptional_occurs_twice_single_slope step hk5 hz hs r
      (by obtain ⟨i,hi⟩ := hr; exact ⟨i,congrArg Sum.inr hi⟩) 0
      (by intro i g hg; cases hg)
    simpa only [step,PolygonStep.label,Sum.inr.injEq] using he
  have hk4 := (all_labels_twice_length (fun i => (line i).1) hk3 hk5 (by
    intro r hr
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hr
    exact hc r ⟨i,hi⟩)).1
  subst k
  exact F.no_replacement_quad S O hO point line hne hadj
    (four_labels_alternate (fun i => (line i).1) hadj hc) hx hy

end DirectionFrame
end KaplanskyCounterexample.FiniteGeometry
end

end OAI
end
/- CHECKPOINT: OAI.RingTheory.DirectFiniteness.ReplacementPolygon -/

/- BEGIN PINNED MODULE OAI.RingTheory.DirectFiniteness.ReducedWalks -/
section

namespace OAI

universe u_1

noncomputable section
open scoped Classical
namespace SimpleGraph
open scoped _root_.SimpleGraph
open _root_.SimpleGraph _root_.OAI.SimpleGraph Walk
variable {V : Type u_1} {G : _root_.SimpleGraph V}

/-- A walk has no immediate backtracking when it has no closed subwalk
of length two. This formulation is hereditary under taking subwalks. -/
def Walk.Reduced {u v : V} (p : G.Walk u v) : Prop :=
  ∀ (w : V) (q : G.Walk w w), q.IsSubwalk p → q.length ≠ 2

lemma Walk.Reduced.of_isSubwalk {u v w x : V} {p : G.Walk u v} {q : G.Walk w x}
    (hp : _root_.OAI.SimpleGraph.Walk.Reduced p) (hq : q.IsSubwalk p) : _root_.OAI.SimpleGraph.Walk.Reduced q := by
  intro z r hr
  exact hp z r (hr.trans hq)

lemma Walk.Reduced.copy {u v u' v' : V} {p : G.Walk u v}
    (hp : _root_.OAI.SimpleGraph.Walk.Reduced p) (hu : u = u') (hv : v = v') : _root_.OAI.SimpleGraph.Walk.Reduced (p.copy hu hv) := by
  subst u' v'
  exact hp

/-- A nonempty closed walk with no immediate backtracking contains a cycle
no longer than itself. This is the girth fact used for facial boundaries. -/
theorem Walk.Reduced.exists_cycle {u : V} {p : G.Walk u u}
    (hp : _root_.OAI.SimpleGraph.Walk.Reduced p) (hne : ¬ p.Nil) :
    ∃ (v : V) (q : G.Walk v v), q.IsCycle ∧ q.length ≤ p.length := by
  classical
  generalize hn : p.length = n
  induction n using Nat.strong_induction_on generalizing u p with
  | h n ih =>
    by_cases ht : p.tail.IsPath
    · have hlen : 3 ≤ p.length := by
        have hpos : 0 < p.length := Nat.pos_of_ne_zero (fun h => hne (length_eq_zero_iff.mp h))
        have hnotone : p.length ≠ 1 := by
          intro h
          exact G.irrefl (p.adj_of_length_eq_one h)
        have hnottwo := hp u p p.isSubwalk_rfl
        omega
      exact ⟨u, p, (isCycle_iff_isPath_tail_and_le_length).mpr ⟨ht, hlen⟩, by omega⟩
    · rw [isPath_iff_isSubwalk_imp_nil] at ht
      push Not at ht
      obtain ⟨v, q, hsub, hq⟩ := ht
      have hqt : q.IsSubwalk p := hsub.trans p.isSubwalk_rfl.tail
      have hqred : _root_.OAI.SimpleGraph.Walk.Reduced q := hp.of_isSubwalk hqt
      have hlt : q.length < n := by
        have := length_le_of_isSubwalk hsub
        have htlen := p.length_tail
        have hpos : 0 < p.length := Nat.pos_of_ne_zero (fun h => hne (length_eq_zero_iff.mp h))
        omega
      obtain ⟨w, r, hr, hlen⟩ := ih q.length hlt hqred hq rfl
      exact ⟨w, r, hr, hlen.trans (by simpa only [hn] using length_le_of_isSubwalk hqt)⟩

lemma Walk.Reduced.egirth_le {u : V} {p : G.Walk u u}
    (hp : _root_.OAI.SimpleGraph.Walk.Reduced p) (hne : ¬ p.Nil) : G.egirth ≤ p.length := by
  obtain ⟨v, q, hq, hlen⟩ := hp.exists_cycle hne
  exact hq.egirth_le_length.trans (by exact_mod_cast hlen)

/-- The elementary vertex-index criterion for no immediate backtracking. -/
lemma Walk.reduced_of_getVert {u v : V} (p : G.Walk u v)
    (h : ∀ i, i + 2 ≤ p.length → p.getVert i ≠ p.getVert (i + 2)) : _root_.OAI.SimpleGraph.Walk.Reduced p := by
  intro w q hq hlen
  obtain ⟨r, s, rfl⟩ := hq
  have hi : r.length + 2 ≤ ((r.append q).append s).length := by
    simp only [length_append, hlen]
    omega
  have hstart : ((r.append q).append s).getVert r.length = w := by
    rw [getVert_append', ite_eq_left (by simp only [length_append]; omega),
      getVert_append', ite_eq_left le_rfl, getVert_length]
  have hend : ((r.append q).append s).getVert (r.length + 2) = w := by
    rw [getVert_append', ite_eq_left (by simp [hlen]),
      getVert_append, ite_eq_right (by omega)]
    simpa [hlen] using q.getVert_length
  exact h r.length hi (hstart.trans hend.symm)

end SimpleGraph

end

end OAI
end
/- CHECKPOINT: OAI.RingTheory.DirectFiniteness.ReducedWalks -/

/- BEGIN PINNED MODULE OAI.RingTheory.DirectFiniteness.RibbonGeometry -/
section

namespace OAI

universe u_1 u_2 u_3

noncomputable section
open scoped Classical
open scoped BigOperators
open Equiv Equiv.Perm
namespace KaplanskyCounterexample.Planar
attribute [local simp] SameCycle.rfl

variable {α : Type u_1} [Fintype α]

/-- Vertex cycles of a rotation, including the cycles of length one. -/
abbrev Cycles (p : Perm α) := Quotient (SameCycle.setoid p)

def cycleClass (p : Perm α) (x : α) : Cycles p := Quotient.mk _ x

def cycleSet (p : Perm α) (c : Cycles p) : Finset α :=
  Finset.univ.filter fun x => cycleClass p x = c

lemma mem_cycleSet (p : Perm α) (c : Cycles p) (x : α) :
    x ∈ cycleSet p c ↔ cycleClass p x = c := by simp [cycleSet]

omit [Fintype α] in
lemma cycleClass_eq (p : Perm α) (x y : α) :
    cycleClass p x = cycleClass p y ↔ p.SameCycle x y := Quotient.eq

lemma cycleSet_nonempty (p : Perm α) (c : Cycles p) : (cycleSet p c).Nonempty := by
  induction c using Quotient.inductionOn with
  | h x => exact ⟨x, (mem_cycleSet p _ x).mpr rfl⟩

lemma cycles_sum_card (p : Perm α) :
    ∑ c : Cycles p, (cycleSet p c).card = Fintype.card α := by
  classical
  simpa [cycleSet] using Finset.sum_card_fiberwise_eq_card_filter
    (s := Finset.univ) (t := Finset.univ) (g := cycleClass p)

/-- A bipartite rotation system. Each edge is oriented from black to white;
rotations at its two endpoints are permutations of the whole edge set. -/
structure Ribbon (α : Type u_2) where
  black : Perm α
  white : Perm α

def Ribbon.face (R : Ribbon α) : Perm α := R.white * R.black

def Ribbon.Spherical (R : Ribbon α) : Prop :=
  Nat.card (Cycles R.black) + Nat.card (Cycles R.white) +
    Nat.card (Cycles R.face) = Fintype.card α + 2

/-- Local surgery merging two white vertices along consecutive black edges.
The newly created digon is a one-cycle of the face permutation. -/
def Ribbon.mergeWhite (R : Ribbon α) (e : α) : Ribbon α where
  black := R.black
  white := swap e (R.face e) * R.white

omit [Fintype α] in
lemma mergeWhite_face (R : Ribbon α) (e : α) :
    (R.mergeWhite e).face = swap e (R.face e) * R.face := by
  simp [Ribbon.mergeWhite, Ribbon.face, mul_assoc]

omit [Fintype α] in
lemma mergeWhite_face_fixed (R : Ribbon α) (e : α) : (R.mergeWhite e).face e = e := by
  rw [mergeWhite_face]
  simp

/-- A map taking steps of one permutation to cycles of another takes whole
cycles to cycles. -/
lemma sameCycle_map {β : Type u_3} (p : Perm α) (q : Perm β) (f : α → β)
    (hstep : ∀ x, q.SameCycle (f x) (f (p x))) {x y : α}
    (hxy : p.SameCycle x y) : q.SameCycle (f x) (f y) := by
  obtain ⟨n, rfl⟩ := hxy.exists_nat_pow_eq
  clear hxy
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Perm.mul_apply]
    exact ih.trans (hstep _)

/-- Unplug an edge from its face cycle; the edge becomes a singleton cycle. -/
def unplug (p : Perm α) (a : α) : Perm α := swap a (p a) * p

def bypass (p : Perm α) (a x : α) : α := if x = a then p a else x

omit [Fintype α] in
lemma unplug_fixed (p : Perm α) (a : α) : unplug p a a = a := by
  simp [unplug]

lemma unplug_sameCycle (p : Perm α) (a : α) {x y : α}
    (h : (unplug p a).SameCycle x y) : p.SameCycle x y := by
  apply sameCycle_map (unplug p a) p id _ h
  intro x
  change p.SameCycle x (swap a (p a) (p x))
  by_cases hx : x = a
  · subst x
    simp
  · by_cases hxa : p x = a
    · simp only [hxa, swap_apply_left]
      exact (show p.SameCycle x a by rw [← hxa]; simp).trans (by simp)
    · have hxp : p x ≠ p a := p.injective.ne hx
      rw [swap_apply_of_ne_of_ne hxa hxp]
      simp

lemma sameCycle_bypass (p : Perm α) (a : α) (ha : p a ≠ a) {x y : α}
    (h : p.SameCycle x y) :
    (unplug p a).SameCycle (bypass p a x) (bypass p a y) := by
  apply sameCycle_map p (unplug p a) (bypass p a) _ h
  intro x
  by_cases hx : x = a
  · subst x
    simp [bypass, ha]
  · by_cases hxa : p x = a
    · have hq : unplug p a x = p a := by simp [unplug, hxa]
      simp only [bypass, hx, hxa, ite_false, ite_true]
      rw [← hq]
      simp
    · have hxp : p x ≠ p a := p.injective.ne hx
      have hq : unplug p a x = p x := by
        simp only [unplug, Perm.mul_apply]
        exact swap_apply_of_ne_of_ne hxa hxp
      simp only [bypass, hx, hxa, ite_false]
      rw [← hq]
      simp

lemma unplug_sameCycle_iff (p : Perm α) (a : α) (ha : p a ≠ a)
    {x y : α} (hx : x ≠ a) (hy : y ≠ a) :
    (unplug p a).SameCycle x y ↔ p.SameCycle x y := by
  refine ⟨unplug_sameCycle p a, fun h => ?_⟩
  simpa [bypass, hx, hy] using sameCycle_bypass p a ha h

omit [Fintype α] in
lemma bypass_ne (p : Perm α) (a : α) (ha : p a ≠ a) (x : α) :
    bypass p a x ≠ a := by
  by_cases hx : x = a <;> simp [bypass, hx, ha]

/-- Splicing a nontrivial cycle at a point adds exactly one singleton cycle. -/
def unplugCycleEquiv (p : Perm α) (a : α) (ha : p a ≠ a) :
    Cycles p ≃ {c : Cycles (unplug p a) // c ≠ cycleClass (unplug p a) a} where
  toFun := Quotient.lift (fun x =>
    ⟨cycleClass (unplug p a) (bypass p a x), by
      intro h
      have he := (cycleClass_eq _ _ _).mp h
      exact bypass_ne p a ha x (he.eq_of_right (unplug_fixed p a))⟩)
    (fun x y h => Subtype.ext ((cycleClass_eq _ _ _).mpr (sameCycle_bypass p a ha h)))
  invFun c := Quotient.map' id (fun _ _ h => unplug_sameCycle p a h) c.val
  left_inv c := by
    induction c using Quotient.inductionOn with
    | h x =>
      change cycleClass p (bypass p a x) = cycleClass p x
      apply (cycleClass_eq _ _ _).mpr
      by_cases hx : x = a <;> simp [bypass, hx]
  right_inv c := by
    rcases c with ⟨c, hc⟩
    apply Subtype.ext
    induction c using Quotient.inductionOn with
    | h x =>
      have hx : x ≠ a := by
        intro h
        apply hc
        exact congrArg (cycleClass _) h
      change cycleClass (unplug p a) (bypass p a x) = cycleClass (unplug p a) x
      simp [bypass, hx]

lemma unplug_cycles_card (p : Perm α) (a : α) (ha : p a ≠ a) :
    Nat.card (Cycles (unplug p a)) = Nat.card (Cycles p) + 1 := by
  have h := Fintype.card_congr (unplugCycleEquiv p a ha)
  rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq] at h
  have hp : 0 < Fintype.card (Cycles (unplug p a)) :=
    Fintype.card_pos_iff.mpr ⟨cycleClass (unplug p a) a⟩
  simp only [Nat.card_eq_fintype_card]
  omega

/-- A transposition between two different cycles joins them. The orbit link is
proved directly by following the first return in one of the old cycles. -/
lemma swap_mul_sameCycle (p : Perm α) (a b : α) (hab : ¬ p.SameCycle a b) :
    (swap a b * p).SameCycle a b := by
  have hret : ∃ n : ℕ, 0 < n ∧ (p ^ n) b = b := by
    exact ⟨orderOf p, orderOf_pos p, by simp⟩
  let n := Nat.find hret
  have hn : 0 < n ∧ (p ^ n) b = b := Nat.find_spec hret
  have hmin : ∀ k, 0 < k → k < n → (p ^ k) b ≠ b := by
    intro k hk hkn heq
    exact Nat.find_min hret hkn ⟨hk, heq⟩
  have hneq : ∀ k : ℕ, (p ^ k) b ≠ a := by
    intro k heq
    apply hab
    exact (show p.SameCycle b a from ⟨k, by simpa using heq⟩).symm
  have hiter : ∀ k, k < n → ((swap a b * p) ^ k) b = (p ^ k) b := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro hk
      rw [pow_succ', Perm.mul_apply, ih (by omega), Perm.mul_apply]
      have heq : p ((p ^ k) b) = (p ^ (k + 1)) b := by
        rw [pow_succ', Perm.mul_apply]
      rw [heq, swap_apply_of_ne_of_ne (hneq _) (hmin _ (by omega) hk)]
  have hn' : n - 1 + 1 = n := by omega
  have hstep : ((swap a b * p) ^ n) b = a := by
    rw [← hn', pow_succ', Perm.mul_apply, hiter _ (by omega), Perm.mul_apply]
    have heq : p ((p ^ (n - 1)) b) = b := by
      calc
        p ((p ^ (n - 1)) b) = (p ^ (n - 1 + 1)) b := by rw [pow_succ', Perm.mul_apply]
        _ = b := by rw [hn']; exact hn.2
    rw [heq, swap_apply_right]
  exact (show (swap a b * p).SameCycle b a from ⟨n, by simpa using hstep⟩).symm

/-- Old cycles remain connected after a transposition joining distinct cycles. -/
lemma sameCycle_swap_mul (p : Perm α) (a b : α) (hab : ¬ p.SameCycle a b)
    {x y : α} (hxy : p.SameCycle x y) : (swap a b * p).SameCycle x y := by
  have hlink := swap_mul_sameCycle p a b hab
  apply sameCycle_map p (swap a b * p) id _ hxy
  intro x
  have hx : (swap a b * p).SameCycle x (swap a b (p x)) := by
    change (swap a b * p).SameCycle x ((swap a b * p) x)
    exact SameCycle.apply_right SameCycle.rfl
  by_cases hxa : p x = a
  · rw [hxa, swap_apply_left] at hx
    exact hx.trans (hxa ▸ hlink.symm)
  · by_cases hxb : p x = b
    · rw [hxb, swap_apply_right] at hx
      exact hx.trans (hxb ▸ hlink)
    · rwa [swap_apply_of_ne_of_ne hxa hxb] at hx

/-- The quotient of the old vertex set that identifies precisely the two
vertices joined by the transposition. -/
def mergedClass (p : Perm α) (a b : α) (x : α) : Cycles p :=
  if cycleClass p x = cycleClass p b then cycleClass p a else cycleClass p x

omit [Fintype α] in
lemma cycleClass_apply (p : Perm α) (x : α) : cycleClass p (p x) = cycleClass p x := by
  apply (cycleClass_eq _ _ _).mpr
  exact SameCycle.apply_left SameCycle.rfl

omit [Fintype α] in
lemma mergedClass_step (p : Perm α) (a b : α) (hab : ¬ p.SameCycle a b) (x : α) :
    mergedClass p a b ((swap a b * p) x) = mergedClass p a b x := by
  have hne : cycleClass p a ≠ cycleClass p b := mt (cycleClass_eq p a b).mp hab
  change mergedClass p a b (swap a b (p x)) = _
  by_cases hxa : p x = a
  · have hx : cycleClass p x = cycleClass p a := by
      rw [← cycleClass_apply, hxa]
    simp [mergedClass, hxa, hx, hne]
  · by_cases hxb : p x = b
    · have hx : cycleClass p x = cycleClass p b := by
        rw [← cycleClass_apply, hxb]
      simp [mergedClass, hxb, hx, hne]
    · simp [swap_apply_of_ne_of_ne hxa hxb, mergedClass, cycleClass_apply]

lemma mergedClass_cycle (p : Perm α) (a b : α) (hab : ¬ p.SameCycle a b)
    {x y : α} (hxy : (swap a b * p).SameCycle x y) :
    mergedClass p a b x = mergedClass p a b y := by
  obtain ⟨n, rfl⟩ := hxy.exists_nat_pow_eq
  clear hxy
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Perm.mul_apply, mergedClass_step p a b hab]
    exact ih

/-- Joining two different cycles deletes exactly one vertex. -/
def mergeCycleEquiv (p : Perm α) (a b : α) (hab : ¬ p.SameCycle a b) :
    Cycles (swap a b * p) ≃ {c : Cycles p // c ≠ cycleClass p b} where
  toFun := Quotient.lift (fun x => ⟨mergedClass p a b x, by
    have hne : cycleClass p a ≠ cycleClass p b := mt (cycleClass_eq p a b).mp hab
    simp only [mergedClass]
    split_ifs with h <;> assumption⟩)
    (fun _ _ h => Subtype.ext (mergedClass_cycle p a b hab h))
  invFun c := Quotient.map' id (fun _ _ h => sameCycle_swap_mul p a b hab h) c.val
  left_inv c := by
    induction c using Quotient.inductionOn with
    | h x =>
      change Quotient.map' id _ (mergedClass p a b x) = cycleClass (swap a b * p) x
      unfold mergedClass
      split_ifs with hx
      · apply (cycleClass_eq _ _ _).mpr
        exact (swap_mul_sameCycle p a b hab).trans
          (sameCycle_swap_mul p a b hab ((cycleClass_eq _ _ _).mp hx).symm)
      · rfl
  right_inv c := by
    apply Subtype.ext
    rcases c with ⟨c, hc⟩
    induction c using Quotient.inductionOn with
    | h x =>
      change mergedClass p a b x = cycleClass p x
      change cycleClass p x ≠ cycleClass p b at hc
      simp [mergedClass, hc]

lemma swap_mul_cycles_card (p : Perm α) (a b : α) (hab : ¬ p.SameCycle a b) :
    Nat.card (Cycles (swap a b * p)) + 1 = Nat.card (Cycles p) := by
  have h := Fintype.card_congr (mergeCycleEquiv p a b hab)
  rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq] at h
  have hp : 0 < Fintype.card (Cycles p) := Fintype.card_pos_iff.mpr ⟨cycleClass p a⟩
  simp only [Nat.card_eq_fintype_card]
  omega

lemma mergeWhite_spherical (R : Ribbon α) (hR : R.Spherical) (e : α)
    (he : ¬ R.white.SameCycle e (R.black e)) : (R.mergeWhite e).Spherical := by
  have hn : ¬ R.white.SameCycle e (R.face e) := by
    simpa [Ribbon.face] using he
  have hne : R.face e ≠ e := by
    intro h
    apply hn
    rw [h]
  have hw := swap_mul_cycles_card R.white e (R.face e) hn
  have hf := unplug_cycles_card R.face e hne
  unfold Ribbon.Spherical at *
  change Nat.card (Cycles R.black) +
    Nat.card (Cycles (swap e (R.face e) * R.white)) + _ = _
  rw [mergeWhite_face]
  change Nat.card (Cycles R.black) +
    Nat.card (Cycles (swap e (R.face e) * R.white)) +
    Nat.card (Cycles (unplug R.face e)) = Fintype.card α + 2
  omega

theorem euler_contradiction (R : Ribbon α) (hR : R.Spherical)
    (w : Cycles R.white) (f : Cycles R.face)
    (hb : ∀ c : Cycles R.black, 3 ≤ (cycleSet R.black c).card)
    (hw : ∀ c : Cycles R.white, 2 ≤ (cycleSet R.white c).card + if c = w then 1 else 0)
    (hf : ∀ c : Cycles R.face, 6 ≤ (cycleSet R.face c).card + if c = f then 6 else 0) :
    False := by
  have hb' := Finset.sum_le_sum (fun c (_ : c ∈ (Finset.univ : Finset (Cycles R.black))) => hb c)
  have hw' := Finset.sum_le_sum (fun c (_ : c ∈ (Finset.univ : Finset (Cycles R.white))) => hw c)
  have hf' := Finset.sum_le_sum (fun c (_ : c ∈ (Finset.univ : Finset (Cycles R.face))) => hf c)
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, cycles_sum_card] at hb'
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, Finset.sum_add_distrib,
    cycles_sum_card, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at hw' hf'
  unfold Ribbon.Spherical at hR
  simp only [Nat.card_eq_fintype_card] at hR
  omega

end KaplanskyCounterexample.Planar

end

end OAI
end
/- CHECKPOINT: OAI.RingTheory.DirectFiniteness.RibbonGeometry -/

/- BEGIN PINNED MODULE OAI.RingTheory.DirectFiniteness.CycleFactorization -/
section

namespace OAI

universe u_1

noncomputable section
open scoped Classical
open scoped BigOperators
open Equiv Equiv.Perm
namespace KaplanskyCounterexample.Planar
open Equiv Equiv.Perm
attribute [local simp] SameCycle.rfl
variable {α : Type u_1} [Fintype α]

lemma sameCycle_map_quotient {p q : Perm α}
    (h : ∀ {x y}, p.SameCycle x y → q.SameCycle x y) :
    Nat.card (Cycles q) ≤ Nat.card (Cycles p) := by
  exact Nat.card_le_card_of_surjective (Quotient.map id (fun _ _ hxy => h hxy))
    (Quotient.map_surjective _ Function.surjective_id)

lemma swap_cycles_card_le (p : Perm α) (a b : α) :
    Nat.card (Cycles (swap a b * p)) ≤ Nat.card (Cycles p) + 1 := by
  let q := swap a b * p
  have hrev : swap a b * q = p := by simp [q, ← mul_assoc]
  by_cases hab : q.SameCycle a b
  · have href : ∀ {x y}, p.SameCycle x y → q.SameCycle x y := by
      intro x y h
      apply sameCycle_map p q id _ h
      intro x
      have hx : q.SameCycle x (q x) := SameCycle.rfl.apply_right
      have hp : p x = swap a b (q x) := by
        rw [← Perm.mul_apply, hrev]
      rw [hp]
      by_cases hxa : q x = a
      · rw [hxa] at hx
        simpa [hxa] using hx.trans hab
      · by_cases hxb : q x = b
        · rw [hxb] at hx
          simpa [hxb] using hx.trans hab.symm
        · rwa [swap_apply_of_ne_of_ne hxa hxb]
    exact (sameCycle_map_quotient href).trans (Nat.le_succ _)
  · have h := swap_mul_cycles_card q a b hab
    rw [hrev] at h
    change Nat.card (Cycles q) ≤ _
    omega

lemma cycles_card_le (p : Perm α) : Nat.card (Cycles p) ≤ Fintype.card α := by
  simpa using Nat.card_le_card_of_surjective (cycleClass p) Quotient.mk_surjective

lemma cycles_one_card : Nat.card (Cycles (1 : Perm α)) = Fintype.card α := by
  have heq : SameCycle.setoid (1 : Perm α) = ⊥ := by
    ext x y
    exact sameCycle_one
  rw [Cycles, heq]
  exact (Nat.card_congr Setoid.quotientBotEquiv).trans (Nat.card_eq_fintype_card)

/-- A minimal transposition factorization, with each transposition contained in
one of the original cycles. -/
lemma exists_cycle_factorization (p : Perm α) :
    ∃ l : List (α × α),
      (l.map fun ab => swap ab.1 ab.2).prod = p ∧
      l.length + Nat.card (Cycles p) = Fintype.card α ∧
      ∀ ab ∈ l, ab.1 ≠ ab.2 ∧ p.SameCycle ab.1 ab.2 := by
  have hmain : ∀ n : ℕ, ∀ p : Perm α,
      Fintype.card α - Nat.card (Cycles p) = n →
      ∃ l : List (α × α),
        (l.map fun ab => swap ab.1 ab.2).prod = p ∧
        l.length + Nat.card (Cycles p) = Fintype.card α ∧
        ∀ ab ∈ l, ab.1 ≠ ab.2 ∧ p.SameCycle ab.1 ab.2 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro p hn
      by_cases hp : p = 1
      · subst p
        exact ⟨[], rfl, (Nat.zero_add _).trans (cycles_one_card (α := α)),
          fun _ membership => False.elim (List.not_mem_nil membership)⟩
      · have hex : ∃ a, p a ≠ a :=
          not_forall.mp (fun fixed => hp (Equiv.ext fixed))
        obtain ⟨a, ha⟩ := hex
        have hc := unplug_cycles_card p a ha
        have hle := cycles_card_le (unplug p a)
        have hlt : Fintype.card α - Nat.card (Cycles (unplug p a)) < n := by omega
        obtain ⟨l, hl, hlen, hmem⟩ := ih _ hlt (unplug p a) rfl
        refine ⟨(a, p a) :: l, ?_, ?_, ?_⟩
        · simp only [List.map_cons, List.prod_cons, hl]
          exact swap_mul_self_mul a (p a) p
        · simp only [List.length_cons]
          omega
        · intro ab hab
          rcases List.mem_cons.mp hab with rfl | hab
          · exact ⟨Ne.symm ha, SameCycle.rfl.apply_right⟩
          · exact ⟨(hmem ab hab).1, unplug_sameCycle p a (hmem ab hab).2⟩
  exact hmain _ p rfl

end KaplanskyCounterexample.Planar

end

end OAI
end
/- CHECKPOINT: OAI.RingTheory.DirectFiniteness.CycleFactorization -/

/- BEGIN PINNED MODULE OAI.RingTheory.DirectFiniteness.PartitionMerging -/
section

namespace OAI

universe u_1

noncomputable section
open scoped Classical
open scoped BigOperators
open Equiv Equiv.Perm
namespace KaplanskyCounterexample.Planar
open Equiv Equiv.Perm
variable {α : Type u_1}

/-- Identify two classes of a partition, by redirecting the second to the first. -/
def mergeClass (s : Setoid α) (a b x : α) : Quotient s :=
  if Quotient.mk s x = Quotient.mk s b then Quotient.mk s a else Quotient.mk s x

def joinPair (s : Setoid α) (a b : α) : Setoid α := Setoid.ker (mergeClass s a b)

lemma le_joinPair (s : Setoid α) (a b : α) : s ≤ joinPair s a b := by
  intro x y hxy
  change mergeClass s a b x = mergeClass s a b y
  simp only [mergeClass, Quotient.sound hxy]

lemma joinPair_related (s : Setoid α) (a b : α) : (joinPair s a b).r a b := by
  change mergeClass s a b a = mergeClass s a b b
  simp [mergeClass]

lemma joinPair_eq_of_related (s : Setoid α) {a b : α} (hab : s.r a b) :
    joinPair s a b = s := by
  ext x y
  have h : ∀ x, mergeClass s a b x = Quotient.mk s x := by
    intro x
    simp only [mergeClass, ← Quotient.sound hab]
    split_ifs with hx
    · exact hx.symm
    · rfl
  change mergeClass s a b x = mergeClass s a b y ↔ s.r x y
  rw [h, h, Quotient.eq]

lemma joinPair_le (s t : Setoid α) (a b : α) (hst : s ≤ t) (hab : t.r a b) :
    joinPair s a b ≤ t := by
  intro x y hxy
  change mergeClass s a b x = mergeClass s a b y at hxy
  by_cases hx : Quotient.mk s x = Quotient.mk s b
  · by_cases hy : Quotient.mk s y = Quotient.mk s b
    · exact t.iseqv.trans (hst (Quotient.exact hx)) (t.iseqv.symm (hst (Quotient.exact hy)))
    · simp only [mergeClass, hx, hy, ite_true, ite_false] at hxy
      exact t.iseqv.trans (t.iseqv.trans (hst (Quotient.exact hx)) (t.iseqv.symm hab)) (hst (Quotient.exact hxy))
  · by_cases hy : Quotient.mk s y = Quotient.mk s b
    · simp only [mergeClass, hx, hy, ite_true, ite_false] at hxy
      exact t.iseqv.trans (t.iseqv.trans (hst (Quotient.exact hxy)) hab) (t.iseqv.symm (hst (Quotient.exact hy)))
    · simp only [mergeClass, hx, hy, ite_false] at hxy
      exact hst (Quotient.exact hxy)

/-- When the two old classes are distinct, joining them removes exactly one. -/
def joinPairEquiv (s : Setoid α) (a b : α) (hab : ¬ s.r a b) :
    Quotient (joinPair s a b) ≃ {c : Quotient s // c ≠ Quotient.mk s b} where
  toFun := Quotient.lift (fun x => ⟨mergeClass s a b x, by
    have hne : Quotient.mk s a ≠ Quotient.mk s b := fun h => hab (Quotient.exact h)
    simp only [mergeClass]
    split_ifs with hx <;> assumption⟩) (fun _ _ h => Subtype.ext h)
  invFun c := Quotient.map id (fun _ _ h => le_joinPair s a b h) c.val
  left_inv c := by
    induction c using Quotient.inductionOn with
    | h x =>
      change Quotient.map id _ (mergeClass s a b x) = Quotient.mk _ x
      unfold mergeClass
      split_ifs with hx
      · apply Quotient.sound
        exact (joinPair s a b).iseqv.trans (joinPair_related s a b) (le_joinPair s a b (s.iseqv.symm (Quotient.exact hx)))
      · rfl
  right_inv c := by
    rcases c with ⟨c, hc⟩
    apply Subtype.ext
    induction c using Quotient.inductionOn with
    | h x =>
      change mergeClass s a b x = Quotient.mk s x
      simp [mergeClass, hc]

lemma joinPair_card [Fintype α] (s : Setoid α) (a b : α) (hab : ¬ s.r a b) :
    Nat.card (Quotient (joinPair s a b)) + 1 = Nat.card (Quotient s) := by
  have h := Fintype.card_congr (joinPairEquiv s a b hab)
  rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq] at h
  have hp : 0 < Fintype.card (Quotient s) := Fintype.card_pos_iff.mpr ⟨Quotient.mk s a⟩
  simp only [Nat.card_eq_fintype_card]
  omega

lemma setoid_swap_related (s : Setoid α) {a b : α} (hab : s.r a b) (x : α) :
    s.r x (swap a b x) := by
  by_cases ha : x = a
  · subst x
    simpa using hab
  · by_cases hb : x = b
    · subst x
      simpa using s.iseqv.symm hab
    · rw [swap_apply_of_ne_of_ne ha hb]

lemma setoid_sameCycle_of_step [Fintype α] (s : Setoid α) (p : Perm α)
    (hstep : ∀ x, s.r x (p x)) {x y : α} (hxy : p.SameCycle x y) : s.r x y := by
  obtain ⟨n, rfl⟩ := hxy.exists_nat_pow_eq
  clear hxy
  induction n with
  | zero => exact s.iseqv.refl _
  | succ n ih =>
    rw [pow_succ', Perm.mul_apply]
    exact s.iseqv.trans ih (hstep _)

/-- Connected components of a graph presented as a list of edges. -/
def edgePartition : List (α × α) → Setoid α
  | [] => ⊥
  | (a, b) :: l => joinPair (edgePartition l) a b

lemma edgePartition_le {l : List (α × α)} {s : Setoid α}
    (h : ∀ ab ∈ l, s.r ab.1 ab.2) : edgePartition l ≤ s := by
  induction l with
  | nil => exact bot_le
  | cons ab l ih =>
    exact joinPair_le _ _ _ _ (ih fun ab hab => h ab (List.mem_cons_of_mem _ hab))
      (h ab List.mem_cons_self)

lemma edgePartition_pair {l : List (α × α)} {ab : α × α} (h : ab ∈ l) :
    (edgePartition l).r ab.1 ab.2 := by
  induction l with
  | nil => simp at h
  | cons cd l ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact joinPair_related _ _ _
    · exact le_joinPair _ _ _ (ih h)

lemma edgePartition_prod (l : List (α × α)) (x : α) :
    (edgePartition l).r x ((l.map fun ab => swap ab.1 ab.2).prod x) := by
  induction l with
  | nil => exact (⊥ : Setoid α).iseqv.refl x
  | cons ab l ih =>
    simp only [List.map_cons, List.prod_cons, Perm.mul_apply]
    exact (edgePartition (ab :: l)).iseqv.trans (le_joinPair _ _ _ ih)
      (setoid_swap_related (edgePartition (ab :: l)) (joinPair_related _ _ _) _)

lemma transposition_euler_bound [Fintype α] (l : List (α × α)) :
    Fintype.card α + Nat.card (Cycles (l.map fun ab => swap ab.1 ab.2).prod) ≤
      l.length + 2 * Nat.card (Quotient (edgePartition l)) := by
  induction l with
  | nil =>
    change Fintype.card α + Nat.card (Cycles (1 : Perm α)) ≤
      0 + 2 * Nat.card (Quotient (⊥ : Setoid α))
    rw [cycles_one_card, Nat.card_congr Setoid.quotientBotEquiv, Nat.card_eq_fintype_card]
    omega
  | cons ab l ih =>
    let p := (l.map fun ab => swap ab.1 ab.2).prod
    change Fintype.card α + Nat.card (Cycles (swap ab.1 ab.2 * p)) ≤
      (l.length + 1) + 2 * Nat.card (Quotient (joinPair (edgePartition l) ab.1 ab.2))
    by_cases h : (edgePartition l).r ab.1 ab.2
    · rw [joinPair_eq_of_related _ h]
      have hc := swap_cycles_card_le p ab.1 ab.2
      change Fintype.card α + Nat.card (Cycles p) ≤ _ at ih
      omega
    · have hab : ¬ p.SameCycle ab.1 ab.2 := by
        intro hc
        exact h (setoid_sameCycle_of_step (edgePartition l) p (edgePartition_prod l) hc)
      have hc := swap_mul_cycles_card p ab.1 ab.2 hab
      have hs := joinPair_card (edgePartition l) ab.1 ab.2 h
      change Fintype.card α + Nat.card (Cycles p) ≤ _ at ih
      omega

end KaplanskyCounterexample.Planar

end

end OAI
end
/- CHECKPOINT: OAI.RingTheory.DirectFiniteness.PartitionMerging -/

/- BEGIN PINNED MODULE OAI.RingTheory.DirectFiniteness.EulerBound -/
section

namespace OAI

universe u_1

noncomputable section
open scoped Classical
open scoped BigOperators
open Equiv Equiv.Perm
namespace KaplanskyCounterexample.Planar
open Equiv Equiv.Perm
variable {α : Type u_1} [Fintype α]

lemma quotient_card_antitone {s t : Setoid α} (h : s ≤ t) :
    Nat.card (Quotient t) ≤ Nat.card (Quotient s) := by
  exact Nat.card_le_card_of_surjective (Quotient.map id (fun _ _ hxy => h hxy))
    (Quotient.map_surjective _ Function.surjective_id)

/-- Connected components of a bipartite rotation system, including edge
components consisting of a single edge. Isolated vertices are not encoded. -/
def Ribbon.components (R : Ribbon α) : Setoid α :=
  SameCycle.setoid R.black ⊔ SameCycle.setoid R.white

omit [Fintype α] in
lemma cycles_inv_card (p : Perm α) : Nat.card (Cycles p⁻¹) = Nat.card (Cycles p) := by
  have h : SameCycle.setoid p⁻¹ = SameCycle.setoid p := by
    ext a b
    exact sameCycle_inv
  unfold Cycles
  rw [h]

/-- The elementary genus inequality for an arbitrary finite ribbon system.
This supplies the topological constraint needed when components are discarded
in the planar minimality argument; it is not assumed as an extra hypothesis. -/
theorem Ribbon.euler_le (R : Ribbon α) :
    Nat.card (Cycles R.black) + Nat.card (Cycles R.white) + Nat.card (Cycles R.face) ≤
      Fintype.card α + 2 * Nat.card (Quotient R.components) := by
  obtain ⟨lb, hb, hblen, _⟩ := exists_cycle_factorization R.black
  obtain ⟨lw, hw, hwlen, _⟩ := exists_cycle_factorization R.white
  obtain ⟨lf, hf, hflen, _⟩ := exists_cycle_factorization R.face⁻¹
  rw [cycles_inv_card] at hflen
  let l := lw ++ lb ++ lf
  have hl : (l.map fun ab => swap ab.1 ab.2).prod = 1 := by
    simp only [l, List.map_append, List.prod_append, hb, hw, hf]
    change R.face * R.face⁻¹ = 1
    exact mul_inv_cancel _
  have hbl : edgePartition lb ≤ edgePartition l := by
    apply edgePartition_le
    intro ab hab
    apply edgePartition_pair
    simp [l, hab]
  have hwl : edgePartition lw ≤ edgePartition l := by
    apply edgePartition_le
    intro ab hab
    apply edgePartition_pair
    simp [l, hab]
  have hcomp : R.components ≤ edgePartition l := by
    apply sup_le
    · intro x y hxy
      apply setoid_sameCycle_of_step (edgePartition l) R.black _ hxy
      intro x
      rw [← hb]
      exact hbl (edgePartition_prod lb x)
    · intro x y hxy
      apply setoid_sameCycle_of_step (edgePartition l) R.white _ hxy
      intro x
      rw [← hw]
      exact hwl (edgePartition_prod lw x)
  have hc := quotient_card_antitone hcomp
  have hbound := transposition_euler_bound l
  rw [hl, cycles_one_card] at hbound
  have hlen : l.length = lw.length + lb.length + lf.length := by simp [l, Nat.add_assoc]
  omega

end KaplanskyCounterexample.Planar

end

end OAI
end
/- CHECKPOINT: OAI.RingTheory.DirectFiniteness.EulerBound -/

/- BEGIN PINNED MODULE OAI.RingTheory.DirectFiniteness.RibbonRestriction -/
section

namespace OAI

universe u_1

noncomputable section
open scoped Classical
open scoped BigOperators
open Equiv Equiv.Perm
namespace KaplanskyCounterexample.Planar
open Equiv Equiv.Perm
variable {α : Type u_1}

def restrictQuotient (s : Setoid α) (P : α → Prop) :
    Quotient (s.comap (Subtype.val : {x // P x} → α)) → Quotient s :=
  Quotient.map Subtype.val (fun _ _ h => h)

lemma restrictQuotient_injective (s : Setoid α) (P : α → Prop) :
    Function.Injective (restrictQuotient s P) := by
  intro x y
  induction x, y using Quotient.inductionOn₂ with
  | h x y =>
    intro h
    change Quotient.mk s x.val = Quotient.mk s y.val at h
    apply Quotient.sound
    change s.r x.val y.val
    exact Quotient.exact h

/-- Components of an invariant subset and of its complement partition the
components of the original finite set. -/
def quotientRestrictSumEquiv (s : Setoid α) (P : α → Prop)
    (hP : ∀ {x y}, s.r x y → (P x ↔ P y)) :
    (Quotient (s.comap (Subtype.val : {x // P x} → α)) ⊕
      Quotient (s.comap (Subtype.val : {x // ¬ P x} → α))) ≃ Quotient s :=
  Equiv.ofBijective (Sum.elim (restrictQuotient s P) (restrictQuotient s (fun x => ¬ P x))) (by
    constructor
    · intro a b hab
      cases a with
      | inl a =>
        cases b with
        | inl b => exact congrArg Sum.inl (restrictQuotient_injective s P hab)
        | inr b =>
          induction a, b using Quotient.inductionOn₂ with
          | h a b => exact (b.prop ((hP (Quotient.exact hab)).mp a.prop)).elim
      | inr a =>
        cases b with
        | inl b =>
          induction a, b using Quotient.inductionOn₂ with
          | h a b => exact (a.prop ((hP (Quotient.exact hab)).mpr b.prop)).elim
        | inr b => exact congrArg Sum.inr (restrictQuotient_injective s _ hab)
    · intro c
      induction c using Quotient.inductionOn with
      | h x =>
        by_cases hx : P x
        · exact ⟨Sum.inl (Quotient.mk _ ⟨x, hx⟩), rfl⟩
        · exact ⟨Sum.inr (Quotient.mk _ ⟨x, hx⟩), rfl⟩)

lemma quotient_restrict_card_split [Fintype α] (s : Setoid α) (P : α → Prop)
    (hP : ∀ {x y}, s.r x y → (P x ↔ P y)) :
    Nat.card (Quotient (s.comap (Subtype.val : {x // P x} → α))) +
      Nat.card (Quotient (s.comap (Subtype.val : {x // ¬ P x} → α))) =
      Nat.card (Quotient s) := by
  simpa only [Nat.card_sum] using Nat.card_congr (quotientRestrictSumEquiv s P hP)

variable [Fintype α]

lemma perm_invariant_cycle (p : Perm α) (P : α → Prop) (hP : ∀ x, P (p x) ↔ P x)
    {x y : α} (hxy : p.SameCycle x y) : P x ↔ P y := by
  exact Iff.of_eq (setoid_sameCycle_of_step (Setoid.ker P) p
    (fun x => propext (hP x).symm) hxy)

omit [Fintype α] in
lemma subtype_cycles_setoid (p : Perm α) (P : α → Prop) (hP : ∀ x, P (p x) ↔ P x) :
    SameCycle.setoid (p.subtypePerm hP) =
      (SameCycle.setoid p).comap (Subtype.val : {x // P x} → α) := by
  ext x y
  exact sameCycle_subtypePerm

lemma cycles_restrict_card_split (p : Perm α) (P : α → Prop) (hP : ∀ x, P (p x) ↔ P x) :
    Nat.card (Cycles (p.subtypePerm hP)) +
      Nat.card (Cycles (p.subtypePerm (p := fun x => ¬ P x) fun x => not_congr (hP x))) = Nat.card (Cycles p) := by
  unfold Cycles
  rw [subtype_cycles_setoid, subtype_cycles_setoid]
  exact quotient_restrict_card_split _ P (perm_invariant_cycle p P hP)

/-- Restrict a ribbon to a union of its connected components. -/
def Ribbon.restrict (R : Ribbon α) (P : α → Prop)
    (hb : ∀ x, P (R.black x) ↔ P x) (hw : ∀ x, P (R.white x) ↔ P x) :
    Ribbon {x // P x} where
  black := R.black.subtypePerm hb
  white := R.white.subtypePerm hw

omit [Fintype α] in
lemma Ribbon.restrict_face (R : Ribbon α) (P : α → Prop) (hb hw) :
    (R.restrict P hb hw).face = R.face.subtypePerm (fun x => (hw _).trans (hb x)) := rfl

lemma Ribbon.invariant_components (R : Ribbon α) (P : α → Prop)
    (hb : ∀ x, P (R.black x) ↔ P x) (hw : ∀ x, P (R.white x) ↔ P x)
    {x y : α} (hxy : R.components.r x y) : P x ↔ P y := by
  have h : R.components ≤ Setoid.ker P := by
    apply sup_le
    · exact fun _ _ h => propext (perm_invariant_cycle R.black P hb h)
    · exact fun _ _ h => propext (perm_invariant_cycle R.white P hw h)
  exact Iff.of_eq (h hxy)

lemma Ribbon.restrict_components (R : Ribbon α) (P : α → Prop) (hb hw) :
    (R.restrict P hb hw).components =
      R.components.comap (Subtype.val : {x // P x} → α) := by
  apply le_antisymm
  · apply sup_le
    · intro x y h
      exact (show SameCycle.setoid R.black ≤ R.components from le_sup_left) ((sameCycle_subtypePerm (h := hb)).mp h)
    · intro x y h
      exact (show SameCycle.setoid R.white ≤ R.components from le_sup_right) ((sameCycle_subtypePerm (h := hw)).mp h)
  · intro x y hxy
    change R.components.r x.val y.val at hxy
    have hmain : ∀ {a b : α}, R.components.r a b → ∀ (ha : P a) (hb' : P b),
        (R.restrict P hb hw).components.r ⟨a, ha⟩ ⟨b, hb'⟩ := by
      intro a b h
      rw [Ribbon.components, Setoid.sup_def] at h
      change Relation.EqvGen (fun a b => R.black.SameCycle a b ∨ R.white.SameCycle a b) a b at h
      induction h with
      | rel a b hab =>
        intro ha hb'
        rcases hab with hab | hab
        · exact (show SameCycle.setoid (R.restrict P hb hw).black ≤ (R.restrict P hb hw).components from le_sup_left) ((sameCycle_subtypePerm (h := hb)).mpr hab)
        · exact (show SameCycle.setoid (R.restrict P hb hw).white ≤ (R.restrict P hb hw).components from le_sup_right) ((sameCycle_subtypePerm (h := hw)).mpr hab)
      | refl a => exact fun _ _ => (R.restrict P hb hw).components.iseqv.refl _
      | symm a b hab ih =>
        intro ha hb'
        exact (R.restrict P hb hw).components.iseqv.symm (ih hb' ha)
      | trans a b c hab hbc ihab ihbc =>
        intro ha hc
        have hab' : R.components.r a b := by
          rw [Ribbon.components, Setoid.sup_def]
          exact hab
        have hb' : P b := (R.invariant_components P hb hw hab').mp ha
        exact (R.restrict P hb hw).components.iseqv.trans (ihab ha hb') (ihbc hb' hc)
    exact hmain hxy x.prop y.prop

/-- Euler equality componentwise, i.e., genus zero for all components. -/
def Ribbon.GenusZero (R : Ribbon α) : Prop :=
  Nat.card (Cycles R.black) + Nat.card (Cycles R.white) + Nat.card (Cycles R.face) =
    Fintype.card α + 2 * Nat.card (Quotient R.components)

lemma Ribbon.planar_restrict (R : Ribbon α) (hR : R.GenusZero) (P : α → Prop) (hb hw) :
    (R.restrict P hb hw).GenusZero := by
  let S := R.restrict P hb hw
  let T := R.restrict (fun x => ¬ P x) (fun x => not_congr (hb x)) (fun x => not_congr (hw x))
  have hs := S.euler_le
  have ht := T.euler_le
  have hbc := cycles_restrict_card_split R.black P hb
  have hwc := cycles_restrict_card_split R.white P hw
  have hfc := cycles_restrict_card_split R.face P (fun x => (hw _).trans (hb x))
  have hcc := quotient_restrict_card_split R.components P (R.invariant_components P hb hw)
  rw [← R.restrict_components P hb hw,
    ← R.restrict_components (fun x => ¬ P x) (fun x => not_congr (hb x))
      (fun x => not_congr (hw x))] at hcc
  have hec : Fintype.card {x // P x} + Fintype.card {x // ¬ P x} = Fintype.card α := by
    have h := Fintype.card_subtype_compl P
    have hle := Fintype.card_subtype_le P
    omega
  change Nat.card (Cycles S.black) + Nat.card (Cycles T.black) = _ at hbc
  change Nat.card (Cycles S.white) + Nat.card (Cycles T.white) = _ at hwc
  change Nat.card (Cycles S.face) + Nat.card (Cycles T.face) = _ at hfc
  change Nat.card (Quotient S.components) + Nat.card (Quotient T.components) = _ at hcc
  unfold Ribbon.GenusZero at hR ⊢
  change Nat.card (Cycles S.black) + Nat.card (Cycles S.white) + Nat.card (Cycles S.face) =
    Fintype.card {x // P x} + 2 * Nat.card (Quotient S.components)
  omega

end KaplanskyCounterexample.Planar

end

end OAI
end
/- CHECKPOINT: OAI.RingTheory.DirectFiniteness.RibbonRestriction -/

/- BEGIN PINNED MODULE OAI.RingTheory.DirectFiniteness.RibbonDetachment -/
section

namespace OAI

universe u_1

noncomputable section
open scoped Classical
open scoped BigOperators
open Equiv Equiv.Perm
namespace KaplanskyCounterexample.Planar
open Equiv Equiv.Perm
attribute [local simp] SameCycle.rfl
variable {α : Type u_1} [Fintype α]

omit [Fintype α] in
lemma Ribbon.black_step (R : Ribbon α) (x : α) : R.components.r x (R.black x) :=
  (show SameCycle.setoid R.black ≤ R.components from le_sup_left) (show R.black.SameCycle x (R.black x) from SameCycle.apply_right SameCycle.rfl)

omit [Fintype α] in
lemma Ribbon.white_step (R : Ribbon α) (x : α) : R.components.r x (R.white x) :=
  (show SameCycle.setoid R.white ≤ R.components from le_sup_right) (show R.white.SameCycle x (R.white x) from SameCycle.apply_right SameCycle.rfl)

lemma Ribbon.components_le_of_steps (R : Ribbon α) (s : Setoid α)
    (hb : ∀ x, s.r x (R.black x)) (hw : ∀ x, s.r x (R.white x)) : R.components ≤ s := by
  exact sup_le (fun _ _ h => setoid_sameCycle_of_step s R.black hb h)
    (fun _ _ h => setoid_sameCycle_of_step s R.white hw h)

omit [Fintype α] in
lemma Ribbon.black_component_invariant (R : Ribbon α) (a x : α) :
    R.components.r (R.black x) a ↔ R.components.r x a := by
  constructor
  · exact R.components.iseqv.trans (R.black_step x)
  · exact R.components.iseqv.trans (R.components.iseqv.symm (R.black_step x))

omit [Fintype α] in
lemma Ribbon.white_component_invariant (R : Ribbon α) (a x : α) :
    R.components.r (R.white x) a ↔ R.components.r x a := by
  constructor
  · exact R.components.iseqv.trans (R.white_step x)
  · exact R.components.iseqv.trans (R.components.iseqv.symm (R.white_step x))

/-- Retain the connected component of an edge. -/
def Ribbon.keepComponent (R : Ribbon α) (a : α) : Ribbon {x // R.components.r x a} :=
  R.restrict (fun x => R.components.r x a) (R.black_component_invariant a)
    (R.white_component_invariant a)

lemma Ribbon.keepComponent_card (R : Ribbon α) (a : α) :
    Nat.card (Quotient (R.keepComponent a).components) = 1 := by
  apply Nat.card_eq_one_iff_exists.mpr
  refine ⟨Quotient.mk _ ⟨a, R.components.iseqv.refl a⟩, ?_⟩
  intro c
  induction c using Quotient.inductionOn with
  | h x =>
    apply Quotient.sound
    change (R.restrict _ _ _).components.r x ⟨a, _⟩
    rw [R.restrict_components]
    exact x.prop

lemma Ribbon.spherical_keepComponent (R : Ribbon α) (hR : R.GenusZero) (a : α) :
    (R.keepComponent a).Spherical := by
  have h := R.planar_restrict hR (fun x => R.components.r x a)
    (R.black_component_invariant a) (R.white_component_invariant a)
  change (R.keepComponent a).GenusZero at h
  unfold Ribbon.GenusZero at h
  rw [R.keepComponent_card] at h
  exact h

omit [Fintype α] in
lemma joinPair_left_iff (s : Setoid α) (a b y : α) :
    (joinPair s a b).r a y ↔ s.r a y ∨ s.r b y := by
  change mergeClass s a b a = mergeClass s a b y ↔ _
  have ha : mergeClass s a b a = Quotient.mk s a := by simp [mergeClass]
  rw [ha]
  by_cases hy : Quotient.mk s y = Quotient.mk s b
  · simp only [mergeClass, hy, ite_true, true_iff]
    exact Or.inr (s.iseqv.symm (Quotient.exact hy))
  · simp only [mergeClass, hy, ite_false, Quotient.eq]
    exact or_iff_left (fun h => hy (Quotient.sound (s.iseqv.symm h))) |>.symm

/-- Detach an edge from both endpoint rotations. It then forms a separate
one-edge component and can be discarded by restricting to its complement. -/
def Ribbon.detach (R : Ribbon α) (a : α) : Ribbon α where
  black := unplug R.black a
  white := unplug R.white a

omit [Fintype α] in
lemma Ribbon.detach_fixed_black (R : Ribbon α) (a : α) : (R.detach a).black a = a :=
  unplug_fixed _ _
omit [Fintype α] in
lemma Ribbon.detach_fixed_white (R : Ribbon α) (a : α) : (R.detach a).white a = a :=
  unplug_fixed _ _

lemma Ribbon.detach_isolated (R : Ribbon α) (a : α) {x : α}
    (h : (R.detach a).components.r a x) : x = a := by
  have hb : ∀ x, (R.detach a).black x = a ↔ x = a := by
    intro x
    constructor
    · intro h
      apply (R.detach a).black.injective
      simpa only [R.detach_fixed_black] using h
    · intro hx
      simpa only [hx] using R.detach_fixed_black a
  have hw : ∀ x, (R.detach a).white x = a ↔ x = a := by
    intro x
    constructor
    · intro h
      apply (R.detach a).white.injective
      simpa only [R.detach_fixed_white] using h
    · intro hx
      simpa only [hx] using R.detach_fixed_white a
  exact ((R.detach a).invariant_components (fun x => x = a) hb hw h).mp rfl

lemma Ribbon.detach_components_le (R : Ribbon α) (a : α) :
    (R.detach a).components ≤ R.components := by
  apply sup_le
  · exact fun _ _ h => (show SameCycle.setoid R.black ≤ R.components from le_sup_left)
      (unplug_sameCycle R.black a h)
  · exact fun _ _ h => (show SameCycle.setoid R.white ≤ R.components from le_sup_right)
      (unplug_sameCycle R.white a h)

lemma Ribbon.components_detach (R : Ribbon α) (a : α) :
    R.components = joinPair (joinPair (R.detach a).components a (R.black a)) a (R.white a) := by
  let s := (R.detach a).components
  let t := joinPair (joinPair s a (R.black a)) a (R.white a)
  apply le_antisymm
  · apply R.components_le_of_steps t
    · intro x
      have hstep : t.r x ((R.detach a).black x) :=
        le_joinPair _ _ _ (le_joinPair _ _ _ ((R.detach a).black_step x))
      have hab : t.r a (R.black a) := le_joinPair _ _ _ (joinPair_related _ _ _)
      have hback : swap a (R.black a) ((R.detach a).black x) = R.black x := by
        simp [Ribbon.detach, unplug]
      rw [← hback]
      exact t.iseqv.trans hstep (setoid_swap_related t hab _)
    · intro x
      have hstep : t.r x ((R.detach a).white x) :=
        le_joinPair _ _ _ (le_joinPair _ _ _ ((R.detach a).white_step x))
      have hab : t.r a (R.white a) := joinPair_related _ _ _
      have hback : swap a (R.white a) ((R.detach a).white x) = R.white x := by
        simp [Ribbon.detach, unplug]
      rw [← hback]
      exact t.iseqv.trans hstep (setoid_swap_related t hab _)
  · apply joinPair_le
    · exact joinPair_le _ _ _ _ (R.detach_components_le a) (R.black_step a)
    · exact R.white_step a

omit [Fintype α] in
lemma Ribbon.detach_face (R : Ribbon α) (a : α) :
    (R.detach a).face = swap a (R.white a) * swap (R.white a) (R.face a) * R.face := by
  simp only [Ribbon.detach, Ribbon.face, unplug, mul_assoc]
  rw [← mul_assoc R.white (swap a (R.black a)), mul_swap_eq_swap_mul]
  simp only [Perm.mul_apply, mul_assoc]

omit [Fintype α] in
lemma Ribbon.detach_face_of_face_fixed (R : Ribbon α) (a : α) (ha : R.face a = a) :
    (R.detach a).face = R.face := by
  rw [R.detach_face, ha, swap_comm (R.white a) a]
  simp

omit [Fintype α] in
lemma Ribbon.detach_face_unplug (R : Ribbon α) (a : α)
    (hw : R.white a ≠ a) (hf : R.face a ≠ a) :
    (R.detach a).face = swap (R.white a) (R.face a) * unplug R.face a := by
  rw [R.detach_face, swap_mul_eq_mul_swap]
  have ha : swap (R.white a) (R.face a) a = a := swap_apply_of_ne_of_ne hw.symm hf.symm
  simp only [swap_inv, ha, swap_apply_left, unplug, mul_assoc]

lemma Ribbon.detach_face_card_le (R : Ribbon α) (a : α) (hw : R.white a ≠ a) :
    Nat.card (Cycles R.face) ≤ Nat.card (Cycles (R.detach a).face) := by
  by_cases hf : R.face a = a
  · rw [R.detach_face_of_face_fixed a hf]
  · have h := swap_cycles_card_le (R.detach a).face (R.white a) (R.face a)
    rw [R.detach_face_unplug a hw hf] at h
    simp only [← mul_assoc, swap_mul_self, one_mul] at h
    have hc := unplug_cycles_card R.face a hf
    rw [R.detach_face_unplug a hw hf]
    omega

end KaplanskyCounterexample.Planar

end

end OAI
end
/- CHECKPOINT: OAI.RingTheory.DirectFiniteness.RibbonDetachment -/

/- BEGIN PINNED MODULE OAI.RingTheory.DirectFiniteness.DetachmentGenus -/
section

namespace OAI

universe u_1

noncomputable section
open scoped Classical
open scoped BigOperators
open Equiv Equiv.Perm
namespace KaplanskyCounterexample.Planar
open Equiv Equiv.Perm
variable {α : Type u_1} [Fintype α]

omit [Fintype α] in
lemma Ribbon.face_step (R : Ribbon α) (x : α) : R.components.r x (R.face x) :=
  R.components.iseqv.trans (R.black_step x) (R.white_step (R.black x))

lemma Ribbon.sameCycle_face_components (R : Ribbon α) {x y : α} (h : R.face.SameCycle x y) :
    R.components.r x y := setoid_sameCycle_of_step R.components R.face R.face_step h

lemma Ribbon.detach_components_card (R : Ribbon α) (a : α)
    (hb : R.black a ≠ a) (hw : R.white a ≠ a) :
    Nat.card (Quotient (R.detach a).components) = Nat.card (Quotient R.components) +
      if (R.detach a).components.r (R.black a) (R.white a) then 1 else 2 := by
  let s := (R.detach a).components
  let t := joinPair s a (R.black a)
  have hb' : ¬ s.r a (R.black a) := fun h => hb (R.detach_isolated a h)
  have hw' : ¬ s.r a (R.white a) := fun h => hw (R.detach_isolated a h)
  have ht : Nat.card (Quotient t) + 1 = Nat.card (Quotient s) := joinPair_card s _ _ hb'
  have heq : R.components = joinPair t a (R.white a) := R.components_detach a
  by_cases h : s.r (R.black a) (R.white a)
  · have h' : t.r a (R.white a) := (joinPair_left_iff s _ _ _).mpr (Or.inr h)
    rw [joinPair_eq_of_related _ h'] at heq
    change Nat.card (Quotient s) = Nat.card (Quotient R.components) + if s.r (R.black a) (R.white a) then 1 else 2
    simp only [h, ite_true, heq]
    omega
  · have h' : ¬ t.r a (R.white a) := by
      rw [joinPair_left_iff]
      exact not_or.mpr ⟨hw', h⟩
    have ht' := joinPair_card t a (R.white a) h'
    rw [← heq] at ht'
    change Nat.card (Quotient s) = Nat.card (Quotient R.components) + if s.r (R.black a) (R.white a) then 1 else 2
    simp only [h, ite_false]
    omega

lemma Ribbon.detach_components_card_black_fixed (R : Ribbon α) (a : α)
    (hb : R.black a = a) (hw : R.white a ≠ a) :
    Nat.card (Quotient (R.detach a).components) = Nat.card (Quotient R.components) + 1 := by
  have hn : ¬ (R.detach a).components.r a (R.white a) := fun h => hw (R.detach_isolated a h)
  have heq := R.components_detach a
  rw [hb, joinPair_eq_of_related _ ((R.detach a).components.iseqv.refl a)] at heq
  have hc := joinPair_card (R.detach a).components a (R.white a) hn
  rw [← heq] at hc
  omega

lemma Ribbon.detach_components_card_white_fixed (R : Ribbon α) (a : α)
    (hb : R.black a ≠ a) (hw : R.white a = a) :
    Nat.card (Quotient (R.detach a).components) = Nat.card (Quotient R.components) + 1 := by
  have hn : ¬ (R.detach a).components.r a (R.black a) := fun h => hb (R.detach_isolated a h)
  have heq := R.components_detach a
  rw [hw, joinPair_eq_of_related _ ((joinPair (R.detach a).components a (R.black a)).iseqv.refl a)] at heq
  have hc := joinPair_card (R.detach a).components a (R.black a) hn
  rw [← heq] at hc
  omega

omit [Fintype α] in
lemma Ribbon.detach_face_black_fixed (R : Ribbon α) (a : α) (hb : R.black a = a) :
    (R.detach a).face = unplug R.face a := by
  rw [R.detach_face]
  have hf : R.face a = R.white a := by simp [Ribbon.face, hb]
  simp [hf, unplug]
  rfl

omit [Fintype α] in
lemma Ribbon.detach_face_white_fixed (R : Ribbon α) (a : α) (hw : R.white a = a) :
    (R.detach a).face = unplug R.face a := by
  rw [R.detach_face, hw]
  simp [unplug]
  rfl

lemma Ribbon.detach_face_card_separating (R : Ribbon α) (a : α)
    (hb : R.black a ≠ a) (hw : R.white a ≠ a)
    (hsep : ¬ (R.detach a).components.r (R.black a) (R.white a)) :
    Nat.card (Cycles (R.detach a).face) = Nat.card (Cycles R.face) + 2 := by
  have hf : R.face a ≠ a := by
    intro hf
    have hs : (R.detach a).white (R.black a) = R.white a := by
      change swap a (R.white a) (R.face a) = R.white a
      simp [hf]
    exact hsep (hs ▸ (R.detach a).white_step (R.black a))
  have hs : (R.detach a).white (R.black a) = R.face a := by
    change swap a (R.white a) (R.face a) = R.face a
    exact swap_apply_of_ne_of_ne hf (R.white.injective.ne hb)
  have hnot : ¬ (R.detach a).face.SameCycle (R.white a) (R.face a) := by
    intro h
    have hc := (R.detach a).sameCycle_face_components h
    have hs' := (R.detach a).white_step (R.black a)
    rw [hs] at hs'
    exact hsep ((R.detach a).components.iseqv.trans hs'
      ((R.detach a).components.iseqv.symm hc))
  have hcard := swap_mul_cycles_card (R.detach a).face (R.white a) (R.face a) hnot
  have heq : swap (R.white a) (R.face a) * (R.detach a).face = unplug R.face a := by
    rw [R.detach_face_unplug a hw hf]
    simp [← mul_assoc]
  rw [heq, unplug_cycles_card R.face a hf] at hcard
  omega

/-- Edge deletion preserves genus zero, including when deletion separates a
component or removes a vertex of degree one. The detached edge is represented
as an isolated one-edge component until restriction discards it. -/
theorem Ribbon.genusZero_detach (R : Ribbon α) (hR : R.GenusZero) (a : α) :
    (R.detach a).GenusZero := by
  by_cases hb : R.black a = a
  · have hblack : (R.detach a).black = R.black := by
      simp [Ribbon.detach, unplug, hb]
      rfl
    by_cases hw : R.white a = a
    · have heq : R.detach a = R := by
        cases R
        simp_all [Ribbon.detach, unplug]
      rwa [heq]
    · have hwc := unplug_cycles_card R.white a hw
      have hcc := R.detach_components_card_black_fixed a hb hw
      have hf : R.face a ≠ a := by simpa [Ribbon.face, hb] using hw
      have hfc := unplug_cycles_card R.face a hf
      rw [← R.detach_face_black_fixed a hb] at hfc
      change Nat.card (Cycles (R.detach a).white) = _ at hwc
      unfold Ribbon.GenusZero at hR ⊢
      rw [hblack, hwc, hfc, hcc]
      simp only [Nat.mul_add, Nat.mul_one]
      repeat rw [← Nat.add_assoc]
      rw [Nat.add_right_comm (Nat.card (Cycles R.black) + Nat.card (Cycles R.white))
        1 (Nat.card (Cycles R.face))]
      exact congrArg (· + 2) hR
  · have hbc := unplug_cycles_card R.black a hb
    change Nat.card (Cycles (R.detach a).black) = _ at hbc
    by_cases hw : R.white a = a
    · have hwhite : (R.detach a).white = R.white := by
        simp [Ribbon.detach, unplug, hw]
        rfl
      have hcc := R.detach_components_card_white_fixed a hb hw
      have hf : R.face a ≠ a := by
        intro hf
        apply hb
        apply R.white.injective
        simpa [Ribbon.face, hw] using hf
      have hfc := unplug_cycles_card R.face a hf
      rw [← R.detach_face_white_fixed a hw] at hfc
      unfold Ribbon.GenusZero at hR ⊢
      rw [hwhite, hbc, hfc, hcc]
      simp only [Nat.mul_add, Nat.mul_one]
      repeat rw [← Nat.add_assoc]
      rw [Nat.add_right_comm (Nat.card (Cycles R.black)) 1 (Nat.card (Cycles R.white)),
        Nat.add_right_comm (Nat.card (Cycles R.black) + Nat.card (Cycles R.white))
          1 (Nat.card (Cycles R.face))]
      exact congrArg (· + 2) hR
    · have hwc := unplug_cycles_card R.white a hw
      change Nat.card (Cycles (R.detach a).white) = _ at hwc
      have hcc := R.detach_components_card a hb hw
      by_cases hs : (R.detach a).components.r (R.black a) (R.white a)
      · rw [ite_eq_left hs] at hcc
        have hfc := R.detach_face_card_le a hw
        have hbound := (R.detach a).euler_le
        unfold Ribbon.GenusZero at hR ⊢
        apply le_antisymm hbound
        rw [hbc, hwc, hcc]
        simp only [Nat.mul_add, Nat.mul_one]
        repeat rw [← Nat.add_assoc]
        rw [Nat.add_right_comm (Nat.card (Cycles R.black)) 1 (Nat.card (Cycles R.white)),
          Nat.add_right_comm (Nat.card (Cycles R.black) + Nat.card (Cycles R.white) + 1)
            1 (Nat.card (Cycles (R.detach a).face)),
          Nat.add_right_comm (Nat.card (Cycles R.black) + Nat.card (Cycles R.white))
            1 (Nat.card (Cycles (R.detach a).face)), ← hR]
        exact Nat.add_le_add_right (Nat.add_le_add_left hfc _) 2
      · rw [ite_eq_right hs] at hcc
        have hfc := R.detach_face_card_separating a hb hw hs
        unfold Ribbon.GenusZero at hR ⊢
        rw [hbc, hwc, hfc, hcc]
        simp only [Nat.mul_add]
        repeat rw [← Nat.add_assoc]
        rw [Nat.add_right_comm (Nat.card (Cycles R.black)) 1 (Nat.card (Cycles R.white)),
          Nat.add_right_comm (Nat.card (Cycles R.black) + Nat.card (Cycles R.white) + 1)
            1 (Nat.card (Cycles R.face)),
          Nat.add_right_comm (Nat.card (Cycles R.black) + Nat.card (Cycles R.white))
            1 (Nat.card (Cycles R.face))]
        exact congrArg (· + 4) hR

end KaplanskyCounterexample.Planar

end

end OAI
end
/- CHECKPOINT: OAI.RingTheory.DirectFiniteness.DetachmentGenus -/

/- BEGIN PINNED MODULE OAI.RingTheory.DirectFiniteness.PlanarBalance -/
section

namespace OAI

universe u_1 u_2 u_3 u_4 u_5

noncomputable section
open scoped Classical
open scoped BigOperators
open Equiv Equiv.Perm
namespace KaplanskyCounterexample.Planar
open Equiv Equiv.Perm
variable {α : Type u_1} {V : Type u_2} {F : Type u_3} {A : Type u_4} {B : Type u_5} [Fintype α] [AddCommGroup A] [AddCommGroup B]

structure Balanced (R : Ribbon α) (Inc : V → F → Prop)
    (ι : V → F → (A →+ B)) where
  blackLabel : α → V
  whiteLabel : α → F
  blackLabel_rot : ∀ a, blackLabel (R.black a) = blackLabel a
  whiteLabel_rot : ∀ a, whiteLabel (R.white a) = whiteLabel a
  incident : ∀ a, Inc (blackLabel a) (whiteLabel a)
  weight : α → A
  weight_ne : ∀ a, weight a ≠ 0
  exception : Cycles R.white
  black_sum : ∀ c : Cycles R.black,
    ∑ a ∈ cycleSet R.black c, ι (blackLabel a) (whiteLabel a) (weight a) = 0
  white_sum : ∀ c : Cycles R.white, c ≠ exception →
    ∑ a ∈ cycleSet R.white c, weight a = 0
  exceptional_sum : (∑ a ∈ cycleSet R.white exception, weight a) ≠ 0

def Balanced.Reduced {R : Ribbon α} {Inc : V → F → Prop} {ι : V → F → (A →+ B)}
    (D : Balanced R Inc ι) : Prop :=
  (∀ a, R.black a ≠ a → D.whiteLabel (R.black a) ≠ D.whiteLabel a) ∧
  (∀ a, R.white a ≠ a → D.blackLabel (R.white a) ≠ D.blackLabel a)

omit [Fintype α] in
lemma cycleClass_perm (p : Perm α) (a : α) : cycleClass p (p a) = cycleClass p a := by
  apply (cycleClass_eq p _ _).mpr
  exact (SameCycle.refl p a).apply_left

lemma mem_cycleSet_perm (p : Perm α) (c : Cycles p) {a : α}
    (ha : a ∈ cycleSet p c) : p a ∈ cycleSet p c := by
  rw [mem_cycleSet, cycleClass_perm]
  exact (mem_cycleSet p c a).mp ha

lemma cycleSet_pair_perm {p : Perm α} {c : Cycles p} {a b : α}
    (hab : a ≠ b) (hc : cycleSet p c = {a, b}) : p a = b := by
  have ha : a ∈ cycleSet p c := by simp [hc]
  have hb : b ∈ cycleSet p c := by simp [hc]
  have hcycle : p.SameCycle a b := by
    apply (cycleClass_eq p a b).mp
    exact ((mem_cycleSet p c a).mp ha).trans ((mem_cycleSet p c b).mp hb).symm
  have hnofix : p a ≠ a := fun h => hab (hcycle.eq_of_left h)
  have hh := mem_cycleSet_perm p c ha
  simpa [hc, hnofix] using hh

lemma Balanced.white_degree {R : Ribbon α} {Inc : V → F → Prop}
    {ι : V → F → (A →+ B)} (D : Balanced R Inc ι) (c : Cycles R.white) :
    2 ≤ (cycleSet R.white c).card + if c = D.exception then 1 else 0 := by
  classical
  have hpos := (cycleSet_nonempty R.white c).card_pos
  by_cases he : c = D.exception
  · rw [ite_eq_left he]
    omega
  · rw [ite_eq_right he, add_zero]
    by_contra! h
    have hc : (cycleSet R.white c).card = 1 := by omega
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hc
    have hz := D.white_sum c he
    rw [ha] at hz
    simp only [Finset.sum_singleton] at hz
    exact D.weight_ne a hz

lemma Balanced.black_degree {R : Ribbon α} {Inc : V → F → Prop}
    {ι : V → F → (A →+ B)} (D : Balanced R Inc ι) (hred : D.Reduced)
    (hinj : ∀ v f, Inc v f → Function.Injective (ι v f))
    (hind : ∀ v f g, Inc v f → Inc v g → f ≠ g → ∀ x y,
      ι v f x + ι v g y = 0 → x = 0) (c : Cycles R.black) :
    3 ≤ (cycleSet R.black c).card := by
  classical
  have hpos := (cycleSet_nonempty R.black c).card_pos
  by_contra! h
  have hsmall : (cycleSet R.black c).card = 1 ∨ (cycleSet R.black c).card = 2 := by omega
  rcases hsmall with h1 | h2
  · obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h1
    have hz := D.black_sum c
    rw [ha] at hz
    simp only [Finset.sum_singleton] at hz
    exact D.weight_ne a (hinj _ _ (D.incident a) (hz.trans (map_zero _).symm))
  · obtain ⟨a, b, hab, hc⟩ := Finset.card_eq_two.mp h2
    have hp := cycleSet_pair_perm hab hc
    have hbl : D.blackLabel b = D.blackLabel a := by
      simpa only [hp] using D.blackLabel_rot a
    have hwl : D.whiteLabel a ≠ D.whiteLabel b := by
      have hn : R.black a ≠ a := by simpa [hp] using hab.symm
      have hh : D.whiteLabel b ≠ D.whiteLabel a := by simpa only [hp] using hred.1 a hn
      exact hh.symm
    have hiz : Inc (D.blackLabel a) (D.whiteLabel b) := by
      rw [← hbl]
      exact D.incident b
    have hz := D.black_sum c
    rw [hc] at hz
    simp only [Finset.sum_pair hab] at hz
    rw [hbl] at hz
    exact D.weight_ne a (hind _ _ _ (D.incident a) hiz hwl _ _ hz)

lemma cycleSet_singleton_of_fixed (p : Perm α) (a : α) (h : p a = a) :
    cycleSet p (cycleClass p a) = {a} := by
  classical
  ext b
  rw [mem_cycleSet, cycleClass_eq, Finset.mem_singleton]
  exact ⟨fun hb => hb.eq_of_right h, fun hb => hb ▸ SameCycle.refl p a⟩

lemma cycleSet_card_pow (p : Perm α) (a : α) :
    (p ^ (cycleSet p (cycleClass p a)).card) a = a := by
  classical
  by_cases h : p a = a
  · rw [cycleSet_singleton_of_fixed p a h, Finset.card_singleton, pow_one, h]
  · have heq : cycleSet p (cycleClass p a) = (p.cycleOf a).support := by
      ext b
      rw [mem_cycleSet, cycleClass_eq, mem_support_cycleOf_iff' h, sameCycle_comm]
    rw [heq, ← p.pow_mod_card_support_cycleOf_self_apply]
    simp

/-- The bipartite incidence graph; its extended girth is infinite for a forest. -/
def incidenceGraph (Inc : V → F → Prop) : SimpleGraph (Sum V F) where
  Adj x y := match x, y with
    | .inl v, .inr f => Inc v f
    | .inr f, .inl v => Inc v f
    | _, _ => False
  symm := ⟨by intro x y; cases x <;> cases y <;> simp⟩
  loopless := ⟨by intro x; cases x <;> simp⟩

variable {R : Ribbon α} {Inc : V → F → Prop} {ι : V → F → (A →+ B)}

lemma Balanced.black_not_fixed (_D : Balanced R Inc ι)
    (hdeg : ∀ c, 3 ≤ (cycleSet R.black c).card) (a : α) : R.black a ≠ a := by
  intro ha
  have h := hdeg (cycleClass R.black a)
  rw [cycleSet_singleton_of_fixed R.black a ha, Finset.card_singleton] at h
  omega

lemma Balanced.white_fixed_exception (D : Balanced R Inc ι) (a : α)
    (ha : R.white a = a) : cycleClass R.white a = D.exception := by
  classical
  by_contra he
  have h := D.white_sum _ he
  rw [cycleSet_singleton_of_fixed R.white a ha, Finset.sum_singleton] at h
  exact D.weight_ne a h

noncomputable def Balanced.exceptionEdge (D : Balanced R Inc ι) : α :=
  (cycleSet_nonempty R.white D.exception).choose

lemma Balanced.exceptionEdge_mem (D : Balanced R Inc ι) :
    D.exceptionEdge ∈ cycleSet R.white D.exception :=
  (cycleSet_nonempty R.white D.exception).choose_spec

def Balanced.exceptionFace (D : Balanced R Inc ι) : Cycles R.face :=
  cycleClass R.face D.exceptionEdge

lemma Balanced.white_not_fixed_on_other_face (D : Balanced R Inc ι) {a : α}
    (ha : cycleClass R.face a ≠ D.exceptionFace) : R.white (R.black a) ≠ R.black a := by
  intro hf
  have hc := D.white_fixed_exception (R.black a) hf
  have he : D.exceptionEdge = R.black a := by
    have hm := D.exceptionEdge_mem
    rw [← hc, cycleSet_singleton_of_fixed R.white (R.black a) hf,
      Finset.mem_singleton] at hm
    exact hm
  apply ha
  unfold Balanced.exceptionFace
  rw [he, ← hf]
  exact (cycleClass_perm R.face a).symm

/-- Traversing one black turn and then the following white turn of a face. -/
def Balanced.halfStep (D : Balanced R Inc ι) (a : α) :
    (incidenceGraph Inc).Walk (.inr (D.whiteLabel a)) (.inr (D.whiteLabel (R.face a))) :=
  .cons (v := .inl (D.blackLabel a)) (by exact D.incident a) (.cons (by
    change Inc (D.blackLabel a) (D.whiteLabel (R.white (R.black a)))
    rw [D.whiteLabel_rot, ← D.blackLabel_rot a]
    exact D.incident (R.black a)) .nil)

lemma Balanced.halfStep_length (D : Balanced R Inc ι) (a : α) :
    (D.halfStep a).length = 2 := rfl

/-- An initial segment of the facial boundary, with two edge sides per step. -/
def Balanced.boundary (D : Balanced R Inc ι) (a : α) : (n : ℕ) →
    (incidenceGraph Inc).Walk (.inr (D.whiteLabel a))
      (.inr (D.whiteLabel ((R.face ^ n) a)))
  | 0 => .nil
  | n + 1 => (D.halfStep a).append ((D.boundary (R.face a) n).copy rfl (by
      simp only [pow_succ, Perm.mul_apply]))

lemma Balanced.boundary_length (D : Balanced R Inc ι) (a : α) (n : ℕ) :
    (D.boundary a n).length = 2 * n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    simp only [Balanced.boundary, SimpleGraph.Walk.length_append,
      SimpleGraph.Walk.length_copy, Balanced.halfStep_length, ih]
    omega

lemma Balanced.boundary_getVert_even (D : Balanced R Inc ι) (n k : ℕ) (hk : k ≤ n)
    (a : α) : (D.boundary a n).getVert (2 * k) =
      .inr (D.whiteLabel ((R.face ^ k) a)) := by
  induction n generalizing a k with
  | zero => have : k = 0 := Nat.le_zero.mp hk
            subst k
            rfl
  | succ n ih =>
    cases k with
    | zero => simp
    | succ k =>
      simp only [Balanced.boundary, SimpleGraph.Walk.getVert_append]
      rw [ite_eq_right (by simp only [Balanced.halfStep_length]; omega),
        SimpleGraph.Walk.getVert_copy, Balanced.halfStep_length]
      have heq : 2 * (k + 1) - 2 = 2 * k := by omega
      rw [heq, ih k (by omega)]
      simp only [pow_succ, Perm.mul_apply]

lemma Balanced.boundary_getVert_odd (D : Balanced R Inc ι) (n k : ℕ) (hk : k < n)
    (a : α) : (D.boundary a n).getVert (2 * k + 1) =
      .inl (D.blackLabel ((R.face ^ k) a)) := by
  induction n generalizing a k with
  | zero => omega
  | succ n ih =>
    cases k with
    | zero => rfl
    | succ k =>
      simp only [Balanced.boundary, SimpleGraph.Walk.getVert_append]
      rw [ite_eq_right (by simp only [Balanced.halfStep_length]; omega),
        SimpleGraph.Walk.getVert_copy, Balanced.halfStep_length]
      have heq : 2 * (k + 1) + 1 - 2 = 2 * k + 1 := by omega
      rw [heq, ih k (by omega)]
      simp only [pow_succ, Perm.mul_apply]

omit [Fintype α] in
lemma cycleClass_pow (p : Perm α) (a : α) (n : ℕ) :
    cycleClass p ((p ^ n) a) = cycleClass p a :=
  (cycleClass_eq _ _ _).mpr ((SameCycle.refl p a).pow_left)

lemma Balanced.boundary_reduced (D : Balanced R Inc ι) (hred : D.Reduced)
    (hdeg : ∀ c, 3 ≤ (cycleSet R.black c).card) {a : α}
    (ha : cycleClass R.face a ≠ D.exceptionFace) (n : ℕ) :
    _root_.OAI.SimpleGraph.Walk.Reduced (D.boundary a n) := by
  apply SimpleGraph.Walk.reduced_of_getVert
  intro i hi
  rw [D.boundary_length] at hi
  have he : i = 2 * (i / 2) ∨ i = 2 * (i / 2) + 1 := by omega
  rcases he with he | he
  · rw [he, D.boundary_getVert_even n (i / 2) (by omega)]
    have hk : 2 * (i / 2) + 2 = 2 * (i / 2 + 1) := by omega
    rw [hk, D.boundary_getVert_even n (i / 2 + 1) (by omega)]
    intro h
    have hh := Sum.inr.inj h
    rw [pow_succ', Perm.mul_apply] at hh
    change D.whiteLabel ((R.face ^ (i / 2)) a) =
      D.whiteLabel (R.white (R.black ((R.face ^ (i / 2)) a))) at hh
    rw [D.whiteLabel_rot] at hh
    exact hred.1 _ (D.black_not_fixed hdeg _) hh.symm
  · rw [he, D.boundary_getVert_odd n (i / 2) (by omega)]
    have hk : 2 * (i / 2) + 1 + 2 = 2 * (i / 2 + 1) + 1 := by omega
    rw [hk, D.boundary_getVert_odd n (i / 2 + 1) (by omega)]
    intro h
    have hh := Sum.inl.inj h
    rw [pow_succ', Perm.mul_apply] at hh
    change D.blackLabel ((R.face ^ (i / 2)) a) =
      D.blackLabel (R.white (R.black ((R.face ^ (i / 2)) a))) at hh
    have hn : R.white (R.black ((R.face ^ (i / 2)) a)) ≠
        R.black ((R.face ^ (i / 2)) a) :=
      D.white_not_fixed_on_other_face (by rwa [cycleClass_pow])
    exact hred.2 _ hn (hh.symm.trans (D.blackLabel_rot _).symm)

lemma Balanced.face_degree (D : Balanced R Inc ι) (hred : D.Reduced)
    (hdeg : ∀ c, 3 ≤ (cycleSet R.black c).card)
    (hgirth : 12 ≤ (incidenceGraph Inc).egirth) (c : Cycles R.face) :
    6 ≤ (cycleSet R.face c).card + if c = D.exceptionFace then 6 else 0 := by
  classical
  by_cases hc : c = D.exceptionFace
  · rw [ite_eq_left hc]; omega
  rw [ite_eq_right hc, add_zero]
  obtain ⟨a, ha⟩ := cycleSet_nonempty R.face c
  have hac : cycleClass R.face a = c := (mem_cycleSet _ _ _).mp ha
  let n := (cycleSet R.face c).card
  have hpa : (R.face ^ n) a = a := by
    change (R.face ^ (cycleSet R.face c).card) a = a
    rw [← hac]
    exact cycleSet_card_pow R.face a
  let p : (incidenceGraph Inc).Walk (.inr (D.whiteLabel a)) (.inr (D.whiteLabel a)) :=
    (D.boundary a n).copy rfl (by rw [hpa])
  have hp : _root_.OAI.SimpleGraph.Walk.Reduced p := by
    exact (D.boundary_reduced hred hdeg (by rwa [hac]) n).copy _ _
  have hlen : p.length = 2 * n := by simp only [p, SimpleGraph.Walk.length_copy,
    D.boundary_length]
  have hne : ¬ p.Nil := by
    intro h
    have := SimpleGraph.Walk.Nil.length_eq_zero h
    have hn : 0 < n := (cycleSet_nonempty R.face c).card_pos
    omega
  have hg := hgirth.trans (hp.egirth_le hne)
  rw [hlen] at hg
  have hnat : 12 ≤ 2 * n := by exact_mod_cast hg
  change 6 ≤ n
  omega

/-- The curvature obstruction in the local-subgroup embedding proof, with every
facial girth bound derived rather than assumed. -/
theorem Balanced.not_spherical (D : Balanced R Inc ι) (hred : D.Reduced)
    (hinj : ∀ v f, Inc v f → Function.Injective (ι v f))
    (hind : ∀ v f g, Inc v f → Inc v g → f ≠ g → ∀ x y,
      ι v f x + ι v g y = 0 → x = 0)
    (hgirth : 12 ≤ (incidenceGraph Inc).egirth) : ¬ R.Spherical := by
  intro hR
  have hb := D.black_degree hred hinj hind
  exact euler_contradiction R hR D.exception D.exceptionFace hb D.white_degree
    (D.face_degree hred hb hgirth)

end KaplanskyCounterexample.Planar

end

end OAI
end
/- CHECKPOINT: OAI.RingTheory.DirectFiniteness.PlanarBalance -/

/- BEGIN PINNED MODULE OAI.RingTheory.DirectFiniteness.BalanceCoarsening -/
section

namespace OAI

universe u_1 u_2 u_3 u_4 u_5

noncomputable section
open scoped Classical
open scoped BigOperators
open Equiv Equiv.Perm
namespace KaplanskyCounterexample.Planar
open Equiv Equiv.Perm
variable {α : Type u_1} {V : Type u_2} {F : Type u_3} {A : Type u_4} {B : Type u_5} [Fintype α] [AddCommGroup A] [AddCommGroup B]

/-- Cycles map under a coarsening of the orbit partition. -/
def cycleMap {p q : Perm α} (h : ∀ {x y}, p.SameCycle x y → q.SameCycle x y) :
    Cycles p → Cycles q := Quotient.map id (fun _ _ hxy => h hxy)

omit [Fintype α] in
lemma cycleMap_class {p q : Perm α} (h : ∀ {x y}, p.SameCycle x y → q.SameCycle x y)
    (a : α) : cycleMap h (cycleClass p a) = cycleClass q a := rfl

lemma sum_cycle_coarsen {p q : Perm α}
    (h : ∀ {x y}, p.SameCycle x y → q.SameCycle x y) (c : Cycles q) (f : α → A) :
    ∑ a ∈ cycleSet q c, f a =
      ∑ d ∈ Finset.univ.filter (fun d : Cycles p => cycleMap h d = c),
        ∑ a ∈ cycleSet p d, f a := by
  classical
  have hh := Finset.sum_fiberwise_eq_sum_filter (Finset.univ : Finset α)
    (Finset.univ.filter (fun d : Cycles p => cycleMap h d = c)) (cycleClass p) f
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and, cycleMap_class, cycleSet]
    using hh.symm

lemma sum_cycle_coarsen_zero {p q : Perm α}
    (h : ∀ {x y}, p.SameCycle x y → q.SameCycle x y) (f : α → A)
    (hf : ∀ c : Cycles p, ∑ a ∈ cycleSet p c, f a = 0) (c : Cycles q) :
    ∑ a ∈ cycleSet q c, f a = 0 := by
  rw [sum_cycle_coarsen h]
  simp only [hf, Finset.sum_const_zero]

lemma sum_cycle_coarsen_exception {p q : Perm α}
    (h : ∀ {x y}, p.SameCycle x y → q.SameCycle x y) (f : α → A)
    (e : Cycles p) (hf : ∀ c : Cycles p, c ≠ e → ∑ a ∈ cycleSet p c, f a = 0)
    (c : Cycles q) :
    ∑ a ∈ cycleSet q c, f a =
      if cycleMap h e = c then ∑ a ∈ cycleSet p e, f a else 0 := by
  classical
  rw [sum_cycle_coarsen h]
  have hz : ∀ d : Cycles p, (∑ a ∈ cycleSet p d, f a) =
      if d = e then ∑ a ∈ cycleSet p e, f a else 0 := by
    intro d
    split_ifs with hd
    · rw [hd]
    · exact hf d hd
  calc
    _ = ∑ d ∈ Finset.univ.filter (fun d : Cycles p => cycleMap h d = c),
        if d = e then ∑ a ∈ cycleSet p e, f a else 0 := by
      apply Finset.sum_congr rfl
      intro d _
      exact hz d
    _ = _ := by simp only [Finset.sum_ite_eq', Finset.mem_filter, Finset.mem_univ, true_and]

/-- The same balances, allowing temporary zero edges during cancellation. -/
structure WeakBalanced (R : Ribbon α) (Inc : V → F → Prop)
    (ι : V → F → (A →+ B)) where
  blackLabel : α → V
  whiteLabel : α → F
  blackLabel_rot : ∀ a, blackLabel (R.black a) = blackLabel a
  whiteLabel_rot : ∀ a, whiteLabel (R.white a) = whiteLabel a
  incident : ∀ a, Inc (blackLabel a) (whiteLabel a)
  weight : α → A
  exception : Cycles R.white
  black_sum : ∀ c : Cycles R.black,
    ∑ a ∈ cycleSet R.black c, ι (blackLabel a) (whiteLabel a) (weight a) = 0
  white_sum : ∀ c : Cycles R.white, c ≠ exception →
    ∑ a ∈ cycleSet R.white c, weight a = 0
  exceptional_sum : (∑ a ∈ cycleSet R.white exception, weight a) ≠ 0

variable {R : Ribbon α} {Inc : V → F → Prop} {ι : V → F → (A →+ B)}

def Balanced.weak (D : Balanced R Inc ι) : WeakBalanced R Inc ι where
  blackLabel := D.blackLabel
  whiteLabel := D.whiteLabel
  blackLabel_rot := D.blackLabel_rot
  whiteLabel_rot := D.whiteLabel_rot
  incident := D.incident
  weight := D.weight
  exception := D.exception
  black_sum := D.black_sum
  white_sum := D.white_sum
  exceptional_sum := D.exceptional_sum

def WeakBalanced.strong (D : WeakBalanced R Inc ι) (h : ∀ a, D.weight a ≠ 0) :
    Balanced R Inc ι where
  blackLabel := D.blackLabel
  whiteLabel := D.whiteLabel
  blackLabel_rot := D.blackLabel_rot
  whiteLabel_rot := D.whiteLabel_rot
  incident := D.incident
  weight := D.weight
  weight_ne := h
  exception := D.exception
  black_sum := D.black_sum
  white_sum := D.white_sum
  exceptional_sum := D.exceptional_sum

def WeakBalanced.coarsen (D : WeakBalanced R Inc ι) (S : Ribbon α)
    (hb : ∀ {x y}, R.black.SameCycle x y → S.black.SameCycle x y)
    (hw : ∀ {x y}, R.white.SameCycle x y → S.white.SameCycle x y)
    (hbl : ∀ a, D.blackLabel (S.black a) = D.blackLabel a)
    (hwl : ∀ a, D.whiteLabel (S.white a) = D.whiteLabel a) :
    WeakBalanced S Inc ι where
  blackLabel := D.blackLabel
  whiteLabel := D.whiteLabel
  blackLabel_rot := hbl
  whiteLabel_rot := hwl
  incident := D.incident
  weight := D.weight
  exception := cycleMap hw D.exception
  black_sum := sum_cycle_coarsen_zero hb _ D.black_sum
  white_sum c hc := by
    rw [sum_cycle_coarsen_exception hw _ D.exception D.white_sum, ite_eq_right (Ne.symm hc)]
  exceptional_sum := by
    rw [sum_cycle_coarsen_exception hw _ D.exception D.white_sum, ite_eq_left rfl]
    exact D.exceptional_sum

end KaplanskyCounterexample.Planar
end

end OAI
end
/- CHECKPOINT: OAI.RingTheory.DirectFiniteness.BalanceCoarsening -/

/- BEGIN PINNED MODULE OAI.RingTheory.DirectFiniteness.BalanceDetachment -/
section

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6

noncomputable section
open scoped Classical
open scoped BigOperators
open Equiv Equiv.Perm
namespace KaplanskyCounterexample.Planar
open Equiv Equiv.Perm
variable {α : Type u_1} {β : Type u_2} {V : Type u_3} {F : Type u_4} {A : Type u_5} {B : Type u_6} [Fintype α] [AddCommGroup A] [AddCommGroup B]

lemma label_sameCycle (p : Perm α) (f : α → β) (hf : ∀ a, f (p a) = f a)
    {x y : α} (hxy : p.SameCycle x y) : f x = f y :=
  setoid_sameCycle_of_step (Setoid.ker f) p (fun x => (hf x).symm) hxy

lemma label_unplug (p : Perm α) (f : α → β) (hf : ∀ a, f (p a) = f a) (a x : α) :
    f (unplug p a x) = f x :=
  (label_sameCycle p f hf (unplug_sameCycle p a ((SameCycle.refl _ x).apply_right))).symm

lemma sameCycle_unplug_iff_of_ne (p : Perm α) (a : α) {x y : α}
    (hx : x ≠ a) (hy : y ≠ a) : (unplug p a).SameCycle x y ↔ p.SameCycle x y := by
  by_cases ha : p a = a
  · simp only [unplug, ha, swap_self]
    rfl
  · exact unplug_sameCycle_iff p a ha hx hy

lemma cycleSet_unplug (p : Perm α) (a x : α) (hx : x ≠ a) :
    cycleSet (unplug p a) (cycleClass (unplug p a) x) =
      (cycleSet p (cycleClass p x)).erase a := by
  classical
  ext y
  rw [mem_cycleSet, cycleClass_eq, Finset.mem_erase, mem_cycleSet, cycleClass_eq]
  constructor
  · intro hy
    refine ⟨?_, unplug_sameCycle p a hy⟩
    intro hya
    subst y
    exact hx (hy.symm.eq_of_right (unplug_fixed p a))
  · rintro ⟨hya, hy⟩
    exact (sameCycle_unplug_iff_of_ne p a hya hx).mpr hy

omit [Fintype α] in
lemma sum_erase_of_zero (s : Finset α) (a : α) (f : α → A) (ha : f a = 0) :
    ∑ x ∈ s.erase a, f x = ∑ x ∈ s, f x := by
  classical
  apply Finset.sum_subset (Finset.erase_subset _ _)
  intro x hx hxa
  have : x = a := by simpa [hx] using hxa
  simpa [this] using ha

lemma sum_cycle_unplug (p : Perm α) (a x : α) (hx : x ≠ a)
    (f : α → A) (ha : f a = 0) :
    ∑ y ∈ cycleSet (unplug p a) (cycleClass (unplug p a) x), f y =
      ∑ y ∈ cycleSet p (cycleClass p x), f y := by
  rw [cycleSet_unplug p a x hx]
  exact sum_erase_of_zero _ a f ha

variable {R : Ribbon α} {Inc : V → F → Prop} {ι : V → F → (A →+ B)}

lemma WeakBalanced.exists_exception_nonzero (D : WeakBalanced R Inc ι) :
    ∃ e ∈ cycleSet R.white D.exception, D.weight e ≠ 0 := by
  classical
  by_contra! h
  exact D.exceptional_sum (Finset.sum_eq_zero h)

/-- A zero-weight edge can be detached without changing any nonzero balance. -/
def WeakBalanced.detach (D : WeakBalanced R Inc ι) (a : α) (ha : D.weight a = 0) :
    WeakBalanced (R.detach a) Inc ι := by
  classical
  let e := D.exists_exception_nonzero.choose
  have he := D.exists_exception_nonzero.choose_spec.1
  have hwe := D.exists_exception_nonzero.choose_spec.2
  have hea : e ≠ a := by rintro rfl; exact hwe ha
  have hec := (mem_cycleSet R.white D.exception e).mp he
  refine {
    blackLabel := D.blackLabel
    whiteLabel := D.whiteLabel
    blackLabel_rot := label_unplug R.black D.blackLabel D.blackLabel_rot a
    whiteLabel_rot := label_unplug R.white D.whiteLabel D.whiteLabel_rot a
    incident := D.incident
    weight := D.weight
    exception := cycleClass (unplug R.white a) e
    black_sum := ?_
    white_sum := ?_
    exceptional_sum := ?_ }
  · dsimp only [Ribbon.detach]
    intro c
    induction c using Quotient.inductionOn with
    | h x =>
      change (∑ y ∈ cycleSet (unplug R.black a) (cycleClass (unplug R.black a) x),
        ι (D.blackLabel y) (D.whiteLabel y) (D.weight y)) = 0
      by_cases hx : x = a
      · subst x
        rw [cycleSet_singleton_of_fixed _ _ (unplug_fixed R.black a)]
        simp [ha]
      · rw [sum_cycle_unplug R.black a x hx
          (fun y => ι (D.blackLabel y) (D.whiteLabel y) (D.weight y)) (by simp [ha])]
        exact D.black_sum _
  · dsimp only [Ribbon.detach]
    intro c hc
    induction c using Quotient.inductionOn with
    | h x =>
      change (∑ y ∈ cycleSet (unplug R.white a) (cycleClass (unplug R.white a) x),
        D.weight y) = 0
      by_cases hx : x = a
      · subst x
        rw [cycleSet_singleton_of_fixed _ _ (unplug_fixed R.white a)]
        simpa using ha
      · rw [sum_cycle_unplug R.white a x hx _ ha]
        apply D.white_sum
        intro hxc
        apply hc
        apply (cycleClass_eq _ _ _).mpr
        apply (sameCycle_unplug_iff_of_ne R.white a hx hea).mpr
        exact (cycleClass_eq _ _ _).mp (hxc.trans hec.symm)
  · dsimp only [Ribbon.detach]
    rw [sum_cycle_unplug R.white a e hea _ ha, hec]
    exact D.exceptional_sum

end KaplanskyCounterexample.Planar
end

end OAI
end
/- CHECKPOINT: OAI.RingTheory.DirectFiniteness.BalanceDetachment -/

/- BEGIN PINNED MODULE OAI.RingTheory.DirectFiniteness.BalanceRestriction -/
section

namespace OAI

universe u_1 u_2 u_3 u_4 u_5

noncomputable section
open scoped Classical
open scoped BigOperators
open Equiv Equiv.Perm
namespace KaplanskyCounterexample.Planar
open Equiv Equiv.Perm
variable {α : Type u_1} {V : Type u_2} {F : Type u_3} {A : Type u_4} {B : Type u_5} [Fintype α] [AddCommGroup A] [AddCommGroup B]

/-- The inclusion of the cycles of an invariant subset. -/
def cycleSubtypeMap (p : Perm α) (P : α → Prop) (hP : ∀ x, P (p x) ↔ P x) :
    Cycles (p.subtypePerm hP) → Cycles p :=
  Quotient.map Subtype.val (fun _ _ h => (sameCycle_subtypePerm (h := hP)).mp h)

omit [Fintype α] in
lemma cycleSubtypeMap_injective (p : Perm α) (P : α → Prop) (hP : ∀ x, P (p x) ↔ P x) :
    Function.Injective (cycleSubtypeMap p P hP) := by
  intro c d
  induction c using Quotient.inductionOn with
  | h x =>
    induction d using Quotient.inductionOn with
    | h y =>
      intro h
      exact Quotient.sound ((sameCycle_subtypePerm (h := hP)).mpr (Quotient.exact h))

lemma sum_cycle_subtype (p : Perm α) (P : α → Prop) (hP : ∀ x, P (p x) ↔ P x)
    (c : Cycles (p.subtypePerm hP)) (f : α → A) :
    ∑ a ∈ cycleSet (p.subtypePerm hP) c, f a.val =
      ∑ a ∈ cycleSet p (cycleSubtypeMap p P hP c), f a := by
  classical
  induction c using Quotient.inductionOn with
  | h x =>
    apply Finset.sum_bij (fun y _ => y.val)
    · intro y hy
      apply (mem_cycleSet _ _ _).mpr
      exact Quotient.sound ((sameCycle_subtypePerm (h := hP)).mp
        (Quotient.exact ((mem_cycleSet _ _ _).mp hy)))
    · intro y _ z _ h
      exact Subtype.ext h
    · intro y hy
      have hcycle : p.SameCycle y x.val := (cycleClass_eq _ _ _).mp ((mem_cycleSet _ _ _).mp hy)
      have hPy : P y := (perm_invariant_cycle p P hP hcycle).mpr x.property
      refine ⟨⟨y, hPy⟩, ?_, rfl⟩
      apply (mem_cycleSet _ _ _).mpr
      exact Quotient.sound ((sameCycle_subtypePerm (h := hP)).mpr hcycle)
    · intro _ _
      rfl

variable {R : Ribbon α} {Inc : V → F → Prop} {ι : V → F → (A →+ B)}

/-- Discard components not containing the exception. -/
def WeakBalanced.restrict (D : WeakBalanced R Inc ι) (P : α → Prop)
    (hb : ∀ x, P (R.black x) ↔ P x) (hw : ∀ x, P (R.white x) ↔ P x)
    (e : α) (he : cycleClass R.white e = D.exception) (hPe : P e) :
    WeakBalanced (R.restrict P hb hw) Inc ι where
  blackLabel a := D.blackLabel a.val
  whiteLabel a := D.whiteLabel a.val
  blackLabel_rot a := D.blackLabel_rot a.val
  whiteLabel_rot a := D.whiteLabel_rot a.val
  incident a := D.incident a.val
  weight a := D.weight a.val
  exception := cycleClass (R.white.subtypePerm hw) ⟨e, hPe⟩
  black_sum c := by
    dsimp only [Ribbon.restrict] at c ⊢
    rw [sum_cycle_subtype R.black P hb c
      (fun x => ι (D.blackLabel x) (D.whiteLabel x) (D.weight x))]
    exact D.black_sum _
  white_sum c hc := by
    dsimp only [Ribbon.restrict] at c hc ⊢
    rw [sum_cycle_subtype]
    apply D.white_sum
    intro h
    apply hc
    apply cycleSubtypeMap_injective R.white P hw
    exact h.trans he.symm
  exceptional_sum := by
    change (∑ a ∈ cycleSet (R.white.subtypePerm hw)
      (cycleClass (R.white.subtypePerm hw) ⟨e, hPe⟩), D.weight a.val) ≠ 0
    rw [sum_cycle_subtype]
    change (∑ a ∈ cycleSet R.white (cycleClass R.white e), D.weight a) ≠ 0
    rw [he]
    exact D.exceptional_sum

end KaplanskyCounterexample.Planar
end

end OAI
end
/- CHECKPOINT: OAI.RingTheory.DirectFiniteness.BalanceRestriction -/

/- BEGIN PINNED MODULE OAI.RingTheory.DirectFiniteness.WeightTransfer -/
section

namespace OAI

universe u_1 u_2 u_3 u_4 u_5

noncomputable section
open scoped Classical
open scoped BigOperators
open Equiv Equiv.Perm
namespace KaplanskyCounterexample.Planar
open Equiv Equiv.Perm
variable {α : Type u_1} {V : Type u_2} {F : Type u_3} {A : Type u_4} {B : Type u_5} [Fintype α] [AddCommGroup A] [AddCommGroup B]

/-- Add the weight at `a` to the parallel edge `b`, leaving a temporary zero. -/
def transferWeight (w : α → A) (a b x : α) : A :=
  w x + (if x = b then w a else 0) - (if x = a then w a else 0)

omit [Fintype α] in
lemma transferWeight_zero (w : α → A) (a b : α) (hab : a ≠ b) :
    transferWeight w a b a = 0 := by simp [transferWeight, hab]

omit [Fintype α] in
lemma sum_transferWeight (s : Finset α) (w : α → A) (a b : α)
    (hmem : a ∈ s ↔ b ∈ s) : ∑ x ∈ s, transferWeight w a b x = ∑ x ∈ s, w x := by
  classical
  simp only [transferWeight, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_ite_eq']
  simp only [hmem, add_sub_cancel_right]

omit [Fintype α] in
lemma sum_transferWeight_map (s : Finset α) (w : α → A) (a b : α)
    (f : α → (A →+ B)) (hab : f a = f b)
    (hmem : a ∈ s ↔ b ∈ s) :
    ∑ x ∈ s, f x (transferWeight w a b x) = ∑ x ∈ s, f x (w x) := by
  classical
  have hf : ∀ x, f x (transferWeight w a b x) =
      f x (w x) + (if x = b then f b (w a) else 0) -
        (if x = a then f a (w a) else 0) := by
    intro x
    simp only [transferWeight, map_sub, map_add]
    congr 1
    · congr 1
      split_ifs with h
      · subst x; rfl
      · exact map_zero _
    · split_ifs with h
      · subst x; rfl
      · exact map_zero _
  simp only [hf, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp only [hmem, hab, add_sub_cancel_right]

lemma cycleSet_mem_iff_of_sameCycle (p : Perm α) {a b : α} (hab : p.SameCycle a b)
    (c : Cycles p) : a ∈ cycleSet p c ↔ b ∈ cycleSet p c := by
  rw [mem_cycleSet, mem_cycleSet, (cycleClass_eq p a b).mpr hab]

variable {R : Ribbon α} {Inc : V → F → Prop} {ι : V → F → (A →+ B)}

def WeakBalanced.transfer (D : WeakBalanced R Inc ι) (a b : α)
    (hb : R.black.SameCycle a b) (hw : R.white.SameCycle a b) :
    WeakBalanced R Inc ι where
  blackLabel := D.blackLabel
  whiteLabel := D.whiteLabel
  blackLabel_rot := D.blackLabel_rot
  whiteLabel_rot := D.whiteLabel_rot
  incident := D.incident
  weight := transferWeight D.weight a b
  exception := D.exception
  black_sum c := by
    rw [sum_transferWeight_map]
    · exact D.black_sum c
    · rw [label_sameCycle R.black D.blackLabel D.blackLabel_rot hb,
        label_sameCycle R.white D.whiteLabel D.whiteLabel_rot hw]
    · exact cycleSet_mem_iff_of_sameCycle _ hb c
  white_sum c hc := by
    rw [sum_transferWeight _ _ _ _ (cycleSet_mem_iff_of_sameCycle _ hw c)]
    exact D.white_sum c hc
  exceptional_sum := by
    rw [sum_transferWeight _ _ _ _ (cycleSet_mem_iff_of_sameCycle _ hw D.exception)]
    exact D.exceptional_sum

end KaplanskyCounterexample.Planar
end

end OAI
end
/- CHECKPOINT: OAI.RingTheory.DirectFiniteness.WeightTransfer -/

/- BEGIN PINNED MODULE OAI.RingTheory.DirectFiniteness.VertexMerging -/
section

namespace OAI

universe u_1 u_2 u_3 u_4 u_5

noncomputable section
open scoped Classical
open scoped BigOperators
open Equiv Equiv.Perm
namespace KaplanskyCounterexample.Planar
open Equiv Equiv.Perm
attribute [local simp] SameCycle.rfl
variable {α : Type u_1} {V : Type u_2} {F : Type u_3} {A : Type u_4} {B : Type u_5} [Fintype α] [AddCommGroup A] [AddCommGroup B]

lemma Ribbon.mergeWhite_components (R : Ribbon α) (a : α)
    (ha : ¬ R.white.SameCycle a (R.black a)) : (R.mergeWhite a).components = R.components := by
  have hn : ¬ R.white.SameCycle a (R.face a) := by simpa [Ribbon.face] using ha
  apply le_antisymm
  · apply (R.mergeWhite a).components_le_of_steps
    · exact R.black_step
    · intro x
      exact R.components.iseqv.trans (R.white_step x)
        (setoid_swap_related R.components (R.face_step a) (R.white x))
  · apply sup_le
    · exact le_sup_left
    · intro x y h
      exact (show SameCycle.setoid (R.mergeWhite a).white ≤ (R.mergeWhite a).components
        from le_sup_right) (sameCycle_swap_mul R.white a (R.face a) hn h)

lemma Ribbon.genusZero_mergeWhite (R : Ribbon α) (hR : R.GenusZero) (a : α)
    (ha : ¬ R.white.SameCycle a (R.black a)) : (R.mergeWhite a).GenusZero := by
  have hn : ¬ R.white.SameCycle a (R.face a) := by simpa [Ribbon.face] using ha
  have hne : R.face a ≠ a := by intro h; exact hn (by rw [h])
  have hw := swap_mul_cycles_card R.white a (R.face a) hn
  have hf := unplug_cycles_card R.face a hne
  unfold Ribbon.GenusZero at *
  rw [R.mergeWhite_components a ha, mergeWhite_face]
  change Nat.card (Cycles R.black) + Nat.card (Cycles (swap a (R.face a) * R.white)) +
    Nat.card (Cycles (unplug R.face a)) = _
  rw [hf, Nat.add_comm (Nat.card (Cycles R.face)) 1, ← Nat.add_assoc,
    Nat.add_assoc _ _ 1, hw]
  exact hR

/-- The color-reversed local surgery. -/
def Ribbon.mergeBlack (R : Ribbon α) (a : α) : Ribbon α where
  black := swap a (R.black (R.white a)) * R.black
  white := R.white

omit [Fintype α] in
lemma Ribbon.mergeBlack_face (R : Ribbon α) (a : α) :
    (R.mergeBlack a).face = unplug R.face (R.white a) := by
  change R.white * (swap a (R.black (R.white a)) * R.black) =
    swap (R.white a) (R.white (R.black (R.white a))) * (R.white * R.black)
  rw [← mul_assoc, mul_swap_eq_swap_mul, mul_assoc]

lemma Ribbon.mergeBlack_components (R : Ribbon α) (a : α)
    (ha : ¬ R.black.SameCycle a (R.white a)) : (R.mergeBlack a).components = R.components := by
  have hn : ¬ R.black.SameCycle a (R.black (R.white a)) := by simpa using ha
  apply le_antisymm
  · apply (R.mergeBlack a).components_le_of_steps
    · intro x
      exact R.components.iseqv.trans (R.black_step x)
        (setoid_swap_related R.components
          (R.components.iseqv.trans (R.white_step a) (R.black_step (R.white a))) (R.black x))
    · exact R.white_step
  · apply sup_le
    · intro x y h
      exact (show SameCycle.setoid (R.mergeBlack a).black ≤ (R.mergeBlack a).components
        from le_sup_left) (sameCycle_swap_mul R.black a (R.black (R.white a)) hn h)
    · exact le_sup_right

lemma Ribbon.genusZero_mergeBlack (R : Ribbon α) (hR : R.GenusZero) (a : α)
    (ha : ¬ R.black.SameCycle a (R.white a)) : (R.mergeBlack a).GenusZero := by
  have hn : ¬ R.black.SameCycle a (R.black (R.white a)) := by simpa using ha
  have hne : R.face (R.white a) ≠ R.white a := by
    intro h
    have h' : R.black (R.white a) = a := R.white.injective h
    exact hn (by rw [h'])
  have hb := swap_mul_cycles_card R.black a (R.black (R.white a)) hn
  have hf := unplug_cycles_card R.face (R.white a) hne
  unfold Ribbon.GenusZero at *
  rw [R.mergeBlack_components a ha, R.mergeBlack_face]
  change Nat.card (Cycles (swap a (R.black (R.white a)) * R.black)) +
    Nat.card (Cycles R.white) + Nat.card (Cycles (unplug R.face (R.white a))) = _
  omega

omit [Fintype α] in
lemma label_swap (f : α → V) (a b : α) (hab : f a = f b) (x : α) :
    f (swap a b x) = f x := by
  by_cases hxa : x = a
  · subst x
    simpa using hab.symm
  · by_cases hxb : x = b
    · subst x
      simpa using hab
    · rw [swap_apply_of_ne_of_ne hxa hxb]

variable {R : Ribbon α} {Inc : V → F → Prop} {ι : V → F → (A →+ B)}

def WeakBalanced.mergeWhite (D : WeakBalanced R Inc ι) (a : α)
    (ha : ¬ R.white.SameCycle a (R.black a))
    (hl : D.whiteLabel (R.black a) = D.whiteLabel a) :
    WeakBalanced (R.mergeWhite a) Inc ι := by
  have hn : ¬ R.white.SameCycle a (R.face a) := by simpa [Ribbon.face] using ha
  apply D.coarsen (R.mergeWhite a) (fun h => h) (sameCycle_swap_mul _ _ _ hn)
    D.blackLabel_rot
  intro x
  change D.whiteLabel (swap a (R.face a) (R.white x)) = D.whiteLabel x
  rw [label_swap D.whiteLabel a (R.face a)]
  · exact D.whiteLabel_rot x
  · exact (hl.symm).trans (D.whiteLabel_rot (R.black a)).symm

def WeakBalanced.mergeBlack (D : WeakBalanced R Inc ι) (a : α)
    (ha : ¬ R.black.SameCycle a (R.white a))
    (hl : D.blackLabel (R.white a) = D.blackLabel a) :
    WeakBalanced (R.mergeBlack a) Inc ι := by
  have hn : ¬ R.black.SameCycle a (R.black (R.white a)) := by simpa using ha
  apply D.coarsen (R.mergeBlack a) (sameCycle_swap_mul _ _ _ hn) (fun h => h)
    _ D.whiteLabel_rot
  intro x
  change D.blackLabel (swap a (R.black (R.white a)) (R.black x)) = D.blackLabel x
  rw [label_swap D.blackLabel a (R.black (R.white a))]
  · exact D.blackLabel_rot x
  · exact (hl.symm).trans (D.blackLabel_rot (R.white a)).symm

end KaplanskyCounterexample.Planar
end

end OAI
end
/- CHECKPOINT: OAI.RingTheory.DirectFiniteness.VertexMerging -/

/- BEGIN PINNED MODULE OAI.RingTheory.DirectFiniteness.PlanarDiagrams -/
section

namespace OAI

universe u u_1 u_2 u_3 u_4

noncomputable section
open scoped Classical
open scoped BigOperators
open Equiv Equiv.Perm
namespace KaplanskyCounterexample.Planar
open Equiv Equiv.Perm
variable {α : Type u} {V : Type u_1} {F : Type u_2} {A : Type u_3} {B : Type u_4} [Fintype α] [AddCommGroup A] [AddCommGroup B]

omit [Fintype α] in
lemma fixed_compl_invariant (p : Perm α) (a : α) (ha : p a = a) (x : α) :
    p x ≠ a ↔ x ≠ a := by
  constructor
  · intro h hxa; subst x; exact h ha
  · intro h hpx; exact h (p.injective (hpx.trans ha.symm))

variable {R : Ribbon α} {Inc : V → F → Prop} {ι : V → F → (A →+ B)}

/-- Deleting a zero edge, including its now isolated endpoints, strictly
reduces the finite edge set and preserves all required balances. -/
lemma WeakBalanced.exists_smaller (D : WeakBalanced R Inc ι) (hR : R.GenusZero)
    (a : α) (ha : D.weight a = 0) :
    ∃ (β : Type u) (iβ : Fintype β) (S : Ribbon β),
      @Fintype.card β iβ < Fintype.card α ∧ @Ribbon.GenusZero β iβ S ∧
        Nonempty (@WeakBalanced β V F A B iβ _ _ S Inc ι) := by
  classical
  let D' := D.detach a ha
  obtain ⟨e, he, hwe⟩ := D'.exists_exception_nonzero
  have hea : e ≠ a := by
    intro h
    subst e
    exact hwe ha
  let hb := fixed_compl_invariant (R.detach a).black a (R.detach_fixed_black a)
  let hw := fixed_compl_invariant (R.detach a).white a (R.detach_fixed_white a)
  let S := (R.detach a).restrict (fun x => x ≠ a) hb hw
  have hcard : Fintype.card {x : α // x ≠ a} < Fintype.card α :=
    Fintype.card_subtype_lt (x := a) (by simp)
  refine ⟨{x : α // x ≠ a}, _, S, ?_,
    (R.detach a).planar_restrict (R.genusZero_detach hR a) (fun x : α => x ≠ a) hb hw, ?_⟩
  · convert hcard
  · exact ⟨D'.restrict (fun x => x ≠ a) hb hw e ((mem_cycleSet _ _ _).mp he) hea⟩

/-- A finite genus-zero comparison diagram, with its edge type retained. -/
structure PlanarDiagram (Inc : V → F → Prop) (ι : V → F → (A →+ B)) where
  Edge : Type u
  fintype : Fintype Edge
  ribbon : Ribbon Edge
  balanced : @WeakBalanced Edge V F A B fintype _ _ ribbon Inc ι
  genusZero : @Ribbon.GenusZero Edge fintype ribbon

attribute [instance] PlanarDiagram.fintype

def PlanarDiagram.edges (D : PlanarDiagram.{u} Inc ι) : ℕ := Fintype.card D.Edge

def PlanarDiagram.vertices (D : PlanarDiagram.{u} Inc ι) : ℕ :=
  Nat.card (Cycles D.ribbon.black) + Nat.card (Cycles D.ribbon.white)

lemma PlanarDiagram.exists_minimal (C : PlanarDiagram.{u} Inc ι) :
    ∃ D : PlanarDiagram.{u} Inc ι,
      (∀ E : PlanarDiagram.{u} Inc ι, D.edges ≤ E.edges) ∧
      (∀ E : PlanarDiagram.{u} Inc ι, E.edges = D.edges → D.vertices ≤ E.vertices) := by
  classical
  have hex : ∃ n : ℕ, ∃ D : PlanarDiagram.{u} Inc ι, D.edges = n := ⟨C.edges, C, rfl⟩
  obtain ⟨D, hD⟩ := Nat.find_spec hex
  have hv : ∃ v : ℕ, ∃ E : PlanarDiagram.{u} Inc ι,
      E.edges = Nat.find hex ∧ E.vertices = v := ⟨D.vertices, D, hD, rfl⟩
  obtain ⟨E, hE, hEv⟩ := Nat.find_spec hv
  refine ⟨E, ?_, ?_⟩
  · intro F
    rw [hE]
    exact Nat.find_min' hex ⟨F, rfl⟩
  · intro F hF
    rw [hEv]
    exact Nat.find_min' hv ⟨F, hF.trans hE, rfl⟩

/-- Curvature also rules out a disconnected comparison system: its Euler
characteristic is twice its positive number of components. -/
lemma Balanced.not_genusZero (D : Balanced R Inc ι) (hred : D.Reduced)
    (hinj : ∀ v f, Inc v f → Function.Injective (ι v f))
    (hind : ∀ v f g, Inc v f → Inc v g → f ≠ g →
      ∀ a b, ι v f a + ι v g b = 0 → a = 0)
    (hgirth : 12 ≤ (incidenceGraph Inc).egirth) : ¬ R.GenusZero := by
  classical
  intro hR
  have hb := D.black_degree hred hinj hind
  have hw := D.white_degree
  have hf := D.face_degree hred hb hgirth
  have hb' := Finset.sum_le_sum (fun c (_ : c ∈ (Finset.univ : Finset (Cycles R.black))) => hb c)
  have hw' := Finset.sum_le_sum (fun c (_ : c ∈ (Finset.univ : Finset (Cycles R.white))) => hw c)
  have hf' := Finset.sum_le_sum (fun c (_ : c ∈ (Finset.univ : Finset (Cycles R.face))) => hf c)
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, cycles_sum_card] at hb'
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, Finset.sum_add_distrib,
    cycles_sum_card, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at hw' hf'
  have hc : 0 < Nat.card (Quotient R.components) := by
    have : Nonempty (Quotient R.components) := ⟨Quotient.mk _ D.exceptionEdge⟩
    exact Nat.card_pos
  unfold Ribbon.GenusZero at hR
  simp only [Nat.card_eq_fintype_card] at hR hc
  omega

end KaplanskyCounterexample.Planar
end

end OAI
end
/- CHECKPOINT: OAI.RingTheory.DirectFiniteness.PlanarDiagrams -/

/- BEGIN PINNED MODULE OAI.RingTheory.DirectFiniteness.BalanceObstruction -/
section

namespace OAI

universe u_1 u_2 u_3 u_4

noncomputable section
open scoped Classical
open scoped BigOperators
open Equiv Equiv.Perm
namespace KaplanskyCounterexample.Planar
open Equiv Equiv.Perm
attribute [local simp] SameCycle.rfl
universe u
variable {α : Type u} {V : Type u_1} {F : Type u_2} {A : Type u_3} {B : Type u_4} [Fintype α] [AddCommGroup A] [AddCommGroup B]
variable {R : Ribbon α} {Inc : V → F → Prop} {ι : V → F → (A →+ B)}

theorem WeakBalanced.not_genusZero (D : WeakBalanced R Inc ι)
    (hinj : ∀ v f, Inc v f → Function.Injective (ι v f))
    (hind : ∀ v f g, Inc v f → Inc v g → f ≠ g →
      ∀ a b, ι v f a + ι v g b = 0 → a = 0)
    (hgirth : 12 ≤ (incidenceGraph Inc).egirth) : ¬ R.GenusZero := by
  classical
  intro hR
  let C : PlanarDiagram.{u} Inc ι := ⟨α, inferInstance, R, D, hR⟩
  obtain ⟨M, hmin, hvmin⟩ := C.exists_minimal
  have hnz : ∀ E : PlanarDiagram.{u} Inc ι, E.edges = M.edges →
      ∀ a, E.balanced.weight a ≠ 0 := by
    intro E hE a ha
    obtain ⟨β, iβ, S, hcard, hS, hD⟩ := E.balanced.exists_smaller E.genusZero a ha
    let E' : PlanarDiagram.{u} Inc ι := ⟨β, iβ, S, hD.some, hS⟩
    have h := hmin E'
    change M.edges ≤ Fintype.card β at h
    change Fintype.card E.Edge = M.edges at hE
    omega
  have hparallel : ∀ a b : M.Edge, M.ribbon.black.SameCycle a b →
      M.ribbon.white.SameCycle a b → a = b := by
    intro a b hb hw
    by_contra hab
    let E : PlanarDiagram.{u} Inc ι :=
      ⟨M.Edge, inferInstance, M.ribbon, M.balanced.transfer a b hb hw, M.genusZero⟩
    exact hnz E rfl a (transferWeight_zero M.balanced.weight a b hab)
  let D' := M.balanced.strong (hnz M rfl)
  have hred : D'.Reduced := by
    constructor
    · intro a ha hl
      have hw : ¬ M.ribbon.white.SameCycle a (M.ribbon.black a) := by
        intro h
        exact ha (hparallel a _ SameCycle.rfl.apply_right h).symm
      let E : PlanarDiagram.{u} Inc ι :=
        ⟨M.Edge, inferInstance, M.ribbon.mergeWhite a,
          M.balanced.mergeWhite a hw hl, M.ribbon.genusZero_mergeWhite M.genusZero a hw⟩
      have h := hvmin E rfl
      have hn : ¬ M.ribbon.white.SameCycle a (M.ribbon.face a) := by
        simpa [Ribbon.face] using hw
      have hc := swap_mul_cycles_card M.ribbon.white a (M.ribbon.face a) hn
      change Nat.card (Cycles M.ribbon.black) + Nat.card (Cycles M.ribbon.white) ≤
        Nat.card (Cycles M.ribbon.black) +
          Nat.card (Cycles (swap a (M.ribbon.face a) * M.ribbon.white)) at h
      omega
    · intro a ha hl
      have hb : ¬ M.ribbon.black.SameCycle a (M.ribbon.white a) := by
        intro h
        exact ha (hparallel a _ h SameCycle.rfl.apply_right).symm
      let E : PlanarDiagram.{u} Inc ι :=
        ⟨M.Edge, inferInstance, M.ribbon.mergeBlack a,
          M.balanced.mergeBlack a hb hl, M.ribbon.genusZero_mergeBlack M.genusZero a hb⟩
      have h := hvmin E rfl
      have hn : ¬ M.ribbon.black.SameCycle a (M.ribbon.black (M.ribbon.white a)) := by
        simpa using hb
      have hc := swap_mul_cycles_card M.ribbon.black a (M.ribbon.black (M.ribbon.white a)) hn
      change Nat.card (Cycles M.ribbon.black) + Nat.card (Cycles M.ribbon.white) ≤
        Nat.card (Cycles (swap a (M.ribbon.black (M.ribbon.white a)) * M.ribbon.black)) +
          Nat.card (Cycles M.ribbon.white) at h
      omega
  exact D'.not_genusZero hred hinj hind hgirth M.genusZero

end KaplanskyCounterexample.Planar

end

end OAI
end
/- CHECKPOINT: OAI.RingTheory.DirectFiniteness.BalanceObstruction -/

/- BEGIN PINNED MODULE OAI.RingTheory.DirectFiniteness.CycleSplitting -/
section

namespace OAI

universe u_1

noncomputable section
open scoped Classical
open scoped BigOperators
open Equiv Equiv.Perm
namespace KaplanskyCounterexample.Planar
open Equiv Equiv.Perm
variable {α : Type u_1} [Fintype α]

lemma sameCycle_after_swap {p : Perm α} {a b x y : α} (hab : p.SameCycle a b)
    (hxy : (swap a b * p).SameCycle x y) : p.SameCycle x y := by
  apply setoid_sameCycle_of_step (SameCycle.setoid p) (swap a b * p) _ hxy
  intro z
  exact (SameCycle.apply_right SameCycle.rfl).trans
    (setoid_swap_related (SameCycle.setoid p) hab (p z))

lemma sign_eq_cycles (p : Perm α) :
    sign p = (-1 : ℤˣ) ^ (Fintype.card α - Nat.card (Cycles p)) := by
  classical
  obtain ⟨l, hl, hlen, hmem⟩ := exists_cycle_factorization p
  have hs := sign_prod_list_swap (l := l.map fun ab => swap ab.1 ab.2) (by
    intro g hg
    obtain ⟨ab, hab, rfl⟩ := List.mem_map.mp hg
    exact ⟨ab.1, ab.2, (hmem ab hab).1, rfl⟩)
  rw [hl, List.length_map] at hs
  have hn : Fintype.card α - Nat.card (Cycles p) = l.length := by omega
  rwa [hn]

lemma not_sameCycle_swap_of_sameCycle (p : Perm α) (a b : α)
    (hne : a ≠ b) (hab : p.SameCycle a b) : ¬ (swap a b * p).SameCycle a b := by
  classical
  intro hq
  let q := swap a b * p
  have hrev : swap a b * q = p := by simp [q, ← mul_assoc]
  have heq : SameCycle.setoid p = SameCycle.setoid q := by
    ext x y
    constructor
    · intro h
      apply sameCycle_after_swap hq
      rwa [hrev]
    · exact sameCycle_after_swap hab
  have hc : Nat.card (Cycles p) = Nat.card (Cycles q) := by rw [Cycles, heq]
  have hs : sign p = sign q := by rw [sign_eq_cycles, sign_eq_cycles, hc]
  have hsign : (-1 : ℤˣ) = 1 := by
    have := hs
    change sign p = sign (swap a b * p) at this
    rw [Perm.sign_mul, sign_swap hne] at this
    exact mul_right_cancel (b := sign p) (by simpa using this.symm)
  norm_num at hsign

lemma swap_mul_cycles_card_split (p : Perm α) (a b : α)
    (hne : a ≠ b) (hab : p.SameCycle a b) :
    Nat.card (Cycles (swap a b * p)) = Nat.card (Cycles p) + 1 := by
  have h := swap_mul_cycles_card (swap a b * p) a b
    (not_sameCycle_swap_of_sameCycle p a b hne hab)
  simpa [← mul_assoc] using h.symm

end KaplanskyCounterexample.Planar

end

end OAI
end
/- CHECKPOINT: OAI.RingTheory.DirectFiniteness.CycleSplitting -/

/- BEGIN PINNED MODULE OAI.RingTheory.DirectFiniteness.RibbonSplitting -/
section

namespace OAI

universe u_1

noncomputable section
open scoped Classical
open scoped BigOperators
open Equiv Equiv.Perm
namespace KaplanskyCounterexample.Planar
open Equiv Equiv.Perm
variable {α : Type u_1} [Fintype α]

def Ribbon.swapBlack (R : Ribbon α) (a b : α) : Ribbon α :=
  ⟨swap a b * R.black, R.white⟩

omit [Fintype α] in
lemma Ribbon.swapBlack_twice (R : Ribbon α) (a b : α) :
    (R.swapBlack a b).swapBlack a b = R := by
  cases R
  simp [Ribbon.swapBlack, ← mul_assoc]

omit [Fintype α] in
lemma Ribbon.swapBlack_face (R : Ribbon α) (a b : α) :
    (R.swapBlack a b).face = swap (R.white a) (R.white b) * R.face := by
  simp only [Ribbon.face, Ribbon.swapBlack, ← mul_assoc]
  rw [mul_swap_eq_swap_mul]

lemma Ribbon.swapBlack_components_merge (R : Ribbon α) (a b : α)
    (hab : ¬ R.black.SameCycle a b) :
    (R.swapBlack a b).components = joinPair R.components a b := by
  apply le_antisymm
  · apply (R.swapBlack a b).components_le_of_steps
    · intro x
      exact (joinPair R.components a b).iseqv.trans
        (le_joinPair _ _ _ (R.black_step x))
        (setoid_swap_related _ (joinPair_related _ _ _) _)
    · intro x
      exact le_joinPair _ _ _ (R.white_step x)
  · apply joinPair_le
    · apply sup_le
      · intro x y hxy
        exact (show SameCycle.setoid (R.swapBlack a b).black ≤
            (R.swapBlack a b).components from le_sup_left)
          (sameCycle_swap_mul R.black a b hab hxy)
      · exact le_sup_right
    · exact (show SameCycle.setoid (R.swapBlack a b).black ≤
          (R.swapBlack a b).components from le_sup_left)
        (swap_mul_sameCycle R.black a b hab)

omit [Fintype α] in
lemma Ribbon.not_blackCycle_of_not_component (R : Ribbon α) {a b : α}
    (h : ¬ R.components.r a b) : ¬ R.black.SameCycle a b :=
  fun hab => h ((show SameCycle.setoid R.black ≤ R.components from le_sup_left) hab)

lemma Ribbon.not_white_faceCycle_of_not_component (R : Ribbon α) {a b : α}
    (h : ¬ R.components.r a b) : ¬ R.face.SameCycle (R.white a) (R.white b) := by
  intro hab
  exact h (R.components.iseqv.trans (R.white_step a)
    (R.components.iseqv.trans (R.sameCycle_face_components hab)
      (R.components.iseqv.symm (R.white_step b))))

/-- Gluing black vertices from distinct connected components preserves genus zero. -/
lemma Ribbon.genusZero_swapBlack_merge (R : Ribbon α) (hR : R.GenusZero) (a b : α)
    (hab : ¬ R.components.r a b) : (R.swapBlack a b).GenusZero := by
  have hb := R.not_blackCycle_of_not_component hab
  have hbc := swap_mul_cycles_card R.black a b hb
  have hfc := swap_mul_cycles_card R.face (R.white a) (R.white b)
    (R.not_white_faceCycle_of_not_component hab)
  have hcc := joinPair_card R.components a b hab
  rw [← R.swapBlack_components_merge a b hb] at hcc
  rw [← R.swapBlack_face a b] at hfc
  change Nat.card (Cycles (R.swapBlack a b).black) + 1 = _ at hbc
  have hw : (R.swapBlack a b).white = R.white := rfl
  unfold Ribbon.GenusZero at hR ⊢
  rw [hw]
  omega

/-- Splitting one black vertex preserves genus zero, even when the split
separates its connected component into two. -/
lemma Ribbon.genusZero_swapBlack_split (R : Ribbon α) (hR : R.GenusZero) (a b : α)
    (hne : a ≠ b) (hab : R.black.SameCycle a b) : (R.swapBlack a b).GenusZero := by
  let S := R.swapBlack a b
  have hback : S.swapBlack a b = R := R.swapBlack_twice a b
  have hn : ¬ S.black.SameCycle a b := not_sameCycle_swap_of_sameCycle R.black a b hne hab
  have hbc := swap_mul_cycles_card_split R.black a b hne hab
  change Nat.card (Cycles S.black) = Nat.card (Cycles R.black) + 1 at hbc
  have hw : S.white = R.white := rfl
  have hcomp := S.swapBlack_components_merge a b hn
  rw [hback] at hcomp
  by_cases hc : S.components.r a b
  · rw [joinPair_eq_of_related S.components hc] at hcomp
    have hfc := swap_cycles_card_le S.face (S.white a) (S.white b)
    rw [← S.swapBlack_face a b, hback] at hfc
    have hbnd := S.euler_le
    unfold Ribbon.GenusZero at hR ⊢
    change Nat.card (Cycles S.black) + Nat.card (Cycles S.white) +
      Nat.card (Cycles S.face) = Fintype.card α + 2 * Nat.card (Quotient S.components)
    rw [hw] at hbnd ⊢
    rw [hcomp] at hR
    omega
  · have hcc := joinPair_card S.components a b hc
    rw [← hcomp] at hcc
    have hfc := swap_mul_cycles_card S.face (S.white a) (S.white b)
      (S.not_white_faceCycle_of_not_component hc)
    rw [← S.swapBlack_face a b, hback] at hfc
    unfold Ribbon.GenusZero at hR ⊢
    change Nat.card (Cycles S.black) + Nat.card (Cycles S.white) +
      Nat.card (Cycles S.face) = Fintype.card α + 2 * Nat.card (Quotient S.components)
    rw [hw]
    omega

end KaplanskyCounterexample.Planar

end

end OAI
end
/- CHECKPOINT: OAI.RingTheory.DirectFiniteness.RibbonSplitting -/

/- BEGIN PINNED MODULE OAI.RingTheory.DirectFiniteness.RibbonSums -/
section

namespace OAI

universe u_1 u_2

noncomputable section
open scoped Classical
open scoped BigOperators
open Equiv Equiv.Perm
namespace KaplanskyCounterexample.Planar
open Equiv Equiv.Perm
variable {α : Type u_1} {β : Type u_2}

def sumSetoid (s : Setoid α) (t : Setoid β) : Setoid (α ⊕ β) :=
  Setoid.ker (Sum.map (Quotient.mk s) (Quotient.mk t))

@[simp] lemma sumSetoid_inl (s : Setoid α) (t : Setoid β) (x y : α) :
    (sumSetoid s t).r (.inl x) (.inl y) ↔ s.r x y := by
  change (Sum.inl (Quotient.mk s x) : Quotient s ⊕ Quotient t) = .inl (Quotient.mk s y) ↔ _
  simp only [Sum.inl.injEq, Quotient.eq]

@[simp] lemma sumSetoid_inr (s : Setoid α) (t : Setoid β) (x y : β) :
    (sumSetoid s t).r (.inr x) (.inr y) ↔ t.r x y := by
  change (Sum.inr (Quotient.mk t x) : Quotient s ⊕ Quotient t) = .inr (Quotient.mk t y) ↔ _
  simp only [Sum.inr.injEq, Quotient.eq]

@[simp] lemma sumSetoid_cross (s : Setoid α) (t : Setoid β) (x : α) (y : β) :
    ¬ (sumSetoid s t).r (.inl x) (.inr y) := by
  change ¬ (Sum.inl (Quotient.mk s x) : Quotient s ⊕ Quotient t) = .inr (Quotient.mk t y)
  simp

def sumSetoidEquiv (s : Setoid α) (t : Setoid β) :
    Quotient (sumSetoid s t) ≃ Quotient s ⊕ Quotient t :=
  Setoid.quotientKerEquivOfSurjective (Sum.map (Quotient.mk s) (Quotient.mk t)) (by
    rintro (x | y)
    · induction x using Quotient.inductionOn with
      | h x => exact ⟨.inl x, rfl⟩
    · induction y using Quotient.inductionOn with
      | h y => exact ⟨.inr y, rfl⟩)

lemma sumSetoid_card [Fintype α] [Fintype β] (s : Setoid α) (t : Setoid β) :
    Nat.card (Quotient (sumSetoid s t)) = Nat.card (Quotient s) + Nat.card (Quotient t) := by
  rw [Nat.card_congr (sumSetoidEquiv s t), Nat.card_sum]

lemma sumSetoid_le {s : Setoid α} {t : Setoid β} {r : Setoid (α ⊕ β)}
    (hl : ∀ x y, s.r x y → r.r (.inl x) (.inl y))
    (hr : ∀ x y, t.r x y → r.r (.inr x) (.inr y)) : sumSetoid s t ≤ r := by
  rintro (x | x) (y | y) h
  · exact hl x y ((sumSetoid_inl _ _ _ _).mp h)
  · exact False.elim (sumSetoid_cross _ _ _ _ h)
  · exact False.elim (sumSetoid_cross _ _ _ _ ((sumSetoid s t).iseqv.symm h))
  · exact hr x y ((sumSetoid_inr _ _ _ _).mp h)

variable [Fintype α] [Fintype β]

lemma sumCongr_cycles_setoid (p : Perm α) (q : Perm β) :
    SameCycle.setoid (Equiv.sumCongr p q) = sumSetoid (SameCycle.setoid p) (SameCycle.setoid q) := by
  apply le_antisymm
  · intro x y h
    apply setoid_sameCycle_of_step _ (Equiv.sumCongr p q) _ h
    rintro (z | z) <;> simp only [Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr,
      sumSetoid_inl, sumSetoid_inr]
    · exact SameCycle.apply_right SameCycle.rfl
    · exact SameCycle.apply_right SameCycle.rfl
  · apply sumSetoid_le
    · intro x y h
      exact sameCycle_map p (Equiv.sumCongr p q) Sum.inl
        (fun z => SameCycle.apply_right SameCycle.rfl) h
    · intro x y h
      exact sameCycle_map q (Equiv.sumCongr p q) Sum.inr
        (fun z => SameCycle.apply_right SameCycle.rfl) h

lemma sumCongr_cycles_card (p : Perm α) (q : Perm β) :
    Nat.card (Cycles (Equiv.sumCongr p q)) = Nat.card (Cycles p) + Nat.card (Cycles q) := by
  rw [Cycles, sumCongr_cycles_setoid]
  exact sumSetoid_card _ _

def Ribbon.sum (R : Ribbon α) (S : Ribbon β) : Ribbon (α ⊕ β) :=
  ⟨Equiv.sumCongr R.black S.black, Equiv.sumCongr R.white S.white⟩

omit [Fintype α] [Fintype β] in
lemma Ribbon.sum_face (R : Ribbon α) (S : Ribbon β) :
    (R.sum S).face = Equiv.sumCongr R.face S.face := by
  ext x
  cases x <;> rfl

lemma Ribbon.sum_components (R : Ribbon α) (S : Ribbon β) :
    (R.sum S).components = sumSetoid R.components S.components := by
  apply le_antisymm
  · apply (R.sum S).components_le_of_steps
    · rintro (x | x)
      · exact (sumSetoid_inl _ _ _ _).mpr (R.black_step x)
      · exact (sumSetoid_inr _ _ _ _).mpr (S.black_step x)
    · rintro (x | x)
      · exact (sumSetoid_inl _ _ _ _).mpr (R.white_step x)
      · exact (sumSetoid_inr _ _ _ _).mpr (S.white_step x)
  · apply sumSetoid_le
    · have h := R.components_le_of_steps ((R.sum S).components.comap Sum.inl)
        (fun x => (R.sum S).black_step (.inl x))
        (fun x => (R.sum S).white_step (.inl x))
      exact fun x y hxy => h hxy
    · have h := S.components_le_of_steps ((R.sum S).components.comap Sum.inr)
        (fun x => (R.sum S).black_step (.inr x))
        (fun x => (R.sum S).white_step (.inr x))
      exact fun x y hxy => h hxy

lemma Ribbon.genusZero_sum (R : Ribbon α) (S : Ribbon β)
    (hR : R.GenusZero) (hS : S.GenusZero) : (R.sum S).GenusZero := by
  unfold Ribbon.GenusZero at *
  rw [R.sum_face, R.sum_components, sumSetoid_card, Fintype.card_sum]
  change Nat.card (Cycles (Equiv.sumCongr R.black S.black)) +
    Nat.card (Cycles (Equiv.sumCongr R.white S.white)) + _ = _
  rw [sumCongr_cycles_card, sumCongr_cycles_card, sumCongr_cycles_card]
  omega

omit [Fintype α] [Fintype β] in
lemma formPerm_append_nonempty [DecidableEq α] (a b : α) (l m : List α)
    (hb : b ∉ a :: l) :
    ((a :: l) ++ (b :: m)).formPerm = swap a b * (a :: l).formPerm * (b :: m).formPerm := by
  induction l generalizing a with
  | nil => simp
  | cons c l ih =>
    have hba : b ≠ a := fun h => hb (by simp [h])
    have hbc : b ≠ c := fun h => hb (by simp [h])
    have hc : b ∉ c :: l := fun h => hb (List.mem_cons_of_mem _ h)
    have hs : swap a c * swap c b = swap a b * swap a c := by
      rw [mul_swap_eq_swap_mul]
      simp [swap_apply_of_ne_of_ne hba hbc]
    simp only [List.cons_append, List.formPerm_cons_cons]
    rw [show c :: (l ++ b :: m) = (c :: l) ++ (b :: m) from rfl, ih c hc]
    simp only [← mul_assoc, hs]

end KaplanskyCounterexample.Planar

end

end OAI
end
/- CHECKPOINT: OAI.RingTheory.DirectFiniteness.RibbonSums -/

/- BEGIN PINNED MODULE OAI.RingTheory.DirectFiniteness.RibbonWheels -/
section

namespace OAI

universe u_1

noncomputable section
open scoped Classical
open scoped BigOperators
open Equiv Equiv.Perm
namespace KaplanskyCounterexample.Planar
open Equiv Equiv.Perm
variable {α : Type u_1} [Fintype α]

/-- A planar two-vertex wheel: opposite rotations and matching white bivalent
vertices. Empty and singleton rotations are included. -/
def Ribbon.wheel (p : Perm α) : Ribbon (α ⊕ α) :=
  ⟨Equiv.sumCongr p p⁻¹, Equiv.sumComm α α⟩

def sumIndex : α ⊕ α → α := Sum.elim id id

def wheelFaceIndex (p : Perm α) : α ⊕ α → α := Sum.elim id (fun x => p⁻¹ x)

omit [Fintype α] in
@[simp] lemma wheel_white_index (p : Perm α) (x : α ⊕ α) :
    sumIndex ((Ribbon.wheel p).white x) = sumIndex x := by cases x <;> rfl

omit [Fintype α] in
@[simp] lemma wheel_face_index (p : Perm α) (x : α ⊕ α) :
    wheelFaceIndex p ((Ribbon.wheel p).face x) = wheelFaceIndex p x := by
  cases x <;> simp [Ribbon.wheel, Ribbon.face, wheelFaceIndex]

lemma wheel_white_setoid (p : Perm α) :
    SameCycle.setoid (Ribbon.wheel p).white = Setoid.ker sumIndex := by
  apply le_antisymm
  · intro x y h
    apply setoid_sameCycle_of_step _ (Ribbon.wheel p).white _ h
    exact fun z => (wheel_white_index p z).symm
  · rintro (x | x) (y | y) h <;> change x = y at h <;> subst y
    · exact SameCycle.rfl
    · exact SameCycle.apply_right SameCycle.rfl
    · exact SameCycle.apply_right SameCycle.rfl
    · exact SameCycle.rfl

lemma wheel_face_setoid (p : Perm α) :
    SameCycle.setoid (Ribbon.wheel p).face = Setoid.ker (wheelFaceIndex p) := by
  apply le_antisymm
  · intro x y h
    apply setoid_sameCycle_of_step _ (Ribbon.wheel p).face _ h
    exact fun z => (wheel_face_index p z).symm
  · rintro (x | x) (y | y) h
    · change x = y at h
      subst y
      exact SameCycle.rfl
    · change x = p⁻¹ y at h
      subst x
      change (Ribbon.wheel p).face.SameCycle (.inl (p⁻¹ y)) (.inr y)
      convert (SameCycle.apply_right
        (SameCycle.rfl (f := (Ribbon.wheel p).face) (x := Sum.inl (p⁻¹ y)))) using 1
      simp [Ribbon.wheel, Ribbon.face]
    · change p⁻¹ x = y at h
      subst y
      exact SameCycle.apply_right SameCycle.rfl
    · change p⁻¹ x = p⁻¹ y at h
      have := p.symm.injective h
      subst y
      exact SameCycle.rfl

lemma wheel_component_index (p : Perm α) :
    (Ribbon.wheel p).components = Setoid.ker (cycleClass p ∘ sumIndex) := by
  let R := Ribbon.wheel p
  apply le_antisymm
  · apply R.components_le_of_steps
    · rintro (x | x)
      · exact (cycleClass_apply p x).symm
      · change cycleClass p x = cycleClass p (p⁻¹ x)
        exact (cycleClass_eq _ _ _).mpr SameCycle.rfl.symm_apply_right
    · intro x
      change cycleClass p (sumIndex x) = cycleClass p (sumIndex (R.white x))
      rw [wheel_white_index]
  · intro x y h
    have hx : R.components.r x (.inl (sumIndex x)) := by
      cases x with
      | inl x => exact R.components.iseqv.refl _
      | inr x => exact R.white_step (.inr x)
    have hy : R.components.r y (.inl (sumIndex y)) := by
      cases y with
      | inl y => exact R.components.iseqv.refl _
      | inr y => exact R.white_step (.inr y)
    have hxy : p.SameCycle (sumIndex x) (sumIndex y) := (cycleClass_eq _ _ _).mp h
    have hp : R.black.SameCycle (.inl (sumIndex x)) (.inl (sumIndex y)) :=
      sameCycle_map p R.black Sum.inl (fun z => SameCycle.apply_right SameCycle.rfl) hxy
    exact R.components.iseqv.trans hx (R.components.iseqv.trans
      ((show SameCycle.setoid R.black ≤ R.components from le_sup_left) hp)
      (R.components.iseqv.symm hy))

lemma wheel_white_card (p : Perm α) :
    Nat.card (Cycles (Ribbon.wheel p).white) = Fintype.card α := by
  rw [Cycles, wheel_white_setoid]
  exact (Nat.card_congr (Setoid.quotientKerEquivOfSurjective sumIndex
    (fun x => ⟨.inl x, rfl⟩))).trans Nat.card_eq_fintype_card

lemma wheel_face_card (p : Perm α) :
    Nat.card (Cycles (Ribbon.wheel p).face) = Fintype.card α := by
  rw [Cycles, wheel_face_setoid]
  exact (Nat.card_congr (Setoid.quotientKerEquivOfSurjective (wheelFaceIndex p)
    (fun x => ⟨.inl x, rfl⟩))).trans Nat.card_eq_fintype_card

lemma wheel_component_card (p : Perm α) :
    Nat.card (Quotient (Ribbon.wheel p).components) = Nat.card (Cycles p) := by
  rw [wheel_component_index]
  apply Nat.card_congr
  apply Setoid.quotientKerEquivOfSurjective
  intro c
  induction c using Quotient.inductionOn with
  | h x => exact ⟨.inl x, rfl⟩

lemma Ribbon.genusZero_wheel (p : Perm α) : (Ribbon.wheel p).GenusZero := by
  unfold Ribbon.GenusZero
  rw [wheel_white_card, wheel_face_card, wheel_component_card, Fintype.card_sum]
  change Nat.card (Cycles (Equiv.sumCongr p p⁻¹)) + _ + _ = _
  rw [sumCongr_cycles_card, cycles_inv_card]
  omega

end KaplanskyCounterexample.Planar

end

end OAI
end
/- CHECKPOINT: OAI.RingTheory.DirectFiniteness.RibbonWheels -/

/- BEGIN PINNED MODULE OAI.RingTheory.DirectFiniteness.BoundaryCycles -/
section

namespace OAI

universe u_1 u_2 u_3

noncomputable section
open scoped Classical
open scoped BigOperators
open Equiv Equiv.Perm
namespace KaplanskyCounterexample.Planar
open Equiv Equiv.Perm
variable {α : Type u_1} {β : Type u_2} {A : Type u_3} [Fintype α]

/-- The listed distinct edges constitute a whole rotation cycle. -/
def Follows (p : Perm α) (l : List α) : Prop := ∀ x ∈ l, p x = l.formPerm x

omit [Fintype α] in
lemma Follows.invariant {p : Perm α} {l : List α} (h : Follows p l) (x : α) :
    p x ∈ l ↔ x ∈ l := by
  classical
  constructor
  · intro hx
    let y := l.formPerm⁻¹ (p x)
    have hy : y ∈ l := by
      apply l.mem_of_formPerm_apply_mem
      simpa [y] using hx
    have he : p y = p x := by rw [h y hy]; simp [y]
    simpa [p.injective he] using hy
  · intro hx
    rw [h x hx]
    exact l.formPerm_apply_mem_of_mem hx

lemma Follows.sameCycle {p : Perm α} {l : List α} (h : Follows p l)
    (hd : l.Nodup) {x y : α} (hx : x ∈ l) (hy : y ∈ l) : p.SameCycle x y := by
  apply sameCycle_map l.formPerm p id _ (hd.isCycleOn_formPerm.2 hx hy)
  intro z
  by_cases hz : z ∈ l
  · change p.SameCycle z (l.formPerm z)
    rw [← h z hz]
    exact SameCycle.apply_right SameCycle.rfl
  · simp only [id_eq, List.formPerm_apply_of_notMem hz]
    exact SameCycle.rfl

lemma Follows.cycleSet {p : Perm α} {l : List α} (h : Follows p l)
    (hd : l.Nodup) {x : α} (hx : x ∈ l) :
    cycleSet p (cycleClass p x) = l.toFinset := by
  classical
  ext y
  rw [mem_cycleSet, cycleClass_eq, List.mem_toFinset]
  constructor
  · intro hy
    exact (perm_invariant_cycle p (fun z => z ∈ l) h.invariant hy).mpr hx
  · exact fun hy => h.sameCycle hd hy hx

lemma sameCycle_iff_of_eqOn_cycle (p q : Perm α) (x : α)
    (heq : ∀ z, p.SameCycle x z → q z = p z) (y : α) :
    q.SameCycle x y ↔ p.SameCycle x y := by
  have hp : ∀ n : ℕ, (q ^ n) x = (p ^ n) x := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ', pow_succ', Perm.mul_apply, Perm.mul_apply, ih]
      exact heq _ SameCycle.rfl.pow_right
  constructor
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    rw [hp] at hn
    exact ⟨n, by simpa only [zpow_natCast] using hn⟩
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    exact ⟨n, by simpa only [zpow_natCast, hp n] using hn⟩

lemma cycleSet_eq_of_eqOn_cycle (p q : Perm α) (x : α)
    (heq : ∀ z, p.SameCycle x z → q z = p z) :
    cycleSet q (cycleClass q x) = cycleSet p (cycleClass p x) := by
  ext y
  simp only [mem_cycleSet, cycleClass_eq, sameCycle_comm (x := y)]
  exact sameCycle_iff_of_eqOn_cycle p q x heq y

omit [Fintype α] in
lemma formPerm_map_apply [DecidableEq α] [DecidableEq β] (f : α → β)
    (hf : Function.Injective f) (l : List α) (x : α) :
    (l.map f).formPerm (f x) = f (l.formPerm x) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    cases l with
    | nil => simp
    | cons b l =>
      change swap (f a) (f b) (((b :: l).map f).formPerm (f x)) =
        f (swap a b ((b :: l).formPerm x))
      rw [ih]
      exact (hf.map_swap a b _).symm

omit [Fintype α] in
lemma Follows.map_sum_left {p : Perm α} {q : Perm β} {l : List α}
    (h : Follows p l) : Follows (Equiv.sumCongr p q) (l.map Sum.inl) := by
  classical
  intro y hy
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
  simpa only [Equiv.sumCongr_apply, Sum.map_inl,
    formPerm_map_apply Sum.inl Sum.inl_injective] using congrArg Sum.inl (h x hx)

end KaplanskyCounterexample.Planar

end

end OAI
end
/- CHECKPOINT: OAI.RingTheory.DirectFiniteness.BoundaryCycles -/

/- BEGIN PINNED MODULE OAI.RingTheory.DirectFiniteness.CycleSums -/
section

namespace OAI

universe u_1 u_2 u_3

noncomputable section
open scoped Classical
open scoped BigOperators
open Equiv Equiv.Perm
namespace KaplanskyCounterexample.Planar
open Equiv Equiv.Perm
variable {α : Type u_1} {β : Type u_2} {A : Type u_3} [Fintype α] [Fintype β] [AddCommGroup A]

@[simp] lemma sumCongr_sameCycle_inl (p : Perm α) (q : Perm β) (x y : α) :
    SameCycle (Equiv.sumCongr p q) (.inl x) (.inl y) ↔ p.SameCycle x y := by
  change (SameCycle.setoid (Equiv.sumCongr p q)).r _ _ ↔ _
  rw [sumCongr_cycles_setoid]
  exact sumSetoid_inl _ _ _ _

@[simp] lemma sumCongr_sameCycle_inr (p : Perm α) (q : Perm β) (x y : β) :
    SameCycle (Equiv.sumCongr p q) (.inr x) (.inr y) ↔ q.SameCycle x y := by
  change (SameCycle.setoid (Equiv.sumCongr p q)).r _ _ ↔ _
  rw [sumCongr_cycles_setoid]
  exact sumSetoid_inr _ _ _ _

@[simp] lemma sumCongr_not_sameCycle (p : Perm α) (q : Perm β) (x : α) (y : β) :
    ¬ SameCycle (Equiv.sumCongr p q) (.inl x) (.inr y) := by
  change ¬ (SameCycle.setoid (Equiv.sumCongr p q)).r _ _
  rw [sumCongr_cycles_setoid]
  exact sumSetoid_cross _ _ _ _

lemma sum_cycle_sum_left (p : Perm α) (q : Perm β) (x : α) (f : α ⊕ β → A) :
    ∑ y ∈ cycleSet (Equiv.sumCongr p q) (cycleClass _ (.inl x)), f y =
      ∑ y ∈ cycleSet p (cycleClass p x), f (.inl y) := by
  symm
  refine Finset.sum_bij (fun value _ => Sum.inl value) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro value member
    apply (mem_cycleSet _ _ _).mpr
    apply (cycleClass_eq _ _ _).mpr
    apply (sumCongr_sameCycle_inl p q value x).mpr
    exact (cycleClass_eq p value x).mp ((mem_cycleSet p _ value).mp member)
  · intro left _ right _ equality
    exact Sum.inl.inj equality
  · intro value member
    have related := (cycleClass_eq _ _ _).mp ((mem_cycleSet _ _ _).mp member)
    cases value with
    | inl value =>
      exact ⟨value, (mem_cycleSet p _ value).mpr
        ((cycleClass_eq p value x).mpr
          ((sumCongr_sameCycle_inl p q value x).mp related)), rfl⟩
    | inr value =>
      exact False.elim (sumCongr_not_sameCycle p q x value related.symm)

lemma sum_cycle_sum_right (p : Perm α) (q : Perm β) (x : β) (f : α ⊕ β → A) :
    ∑ y ∈ cycleSet (Equiv.sumCongr p q) (cycleClass _ (.inr x)), f y =
      ∑ y ∈ cycleSet q (cycleClass q x), f (.inr y) := by
  symm
  refine Finset.sum_bij (fun value _ => Sum.inr value) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro value member
    apply (mem_cycleSet _ _ _).mpr
    apply (cycleClass_eq _ _ _).mpr
    apply (sumCongr_sameCycle_inr p q value x).mpr
    exact (cycleClass_eq q value x).mp ((mem_cycleSet q _ value).mp member)
  · intro left _ right _ equality
    exact Sum.inr.inj equality
  · intro value member
    have related := (cycleClass_eq _ _ _).mp ((mem_cycleSet _ _ _).mp member)
    cases value with
    | inl value =>
      exact False.elim (sumCongr_not_sameCycle p q value x related)
    | inr value =>
      exact ⟨value, (mem_cycleSet q _ value).mpr
        ((cycleClass_eq q value x).mpr
          ((sumCongr_sameCycle_inr p q value x).mp related)), rfl⟩

def cycleInl (p : Perm α) (q : Perm β) : Cycles p → Cycles (Equiv.sumCongr p q) :=
  Quotient.map Sum.inl (fun _ _ h => (sumCongr_sameCycle_inl p q _ _).mpr h)

@[simp] lemma cycleInl_class (p : Perm α) (q : Perm β) (x : α) :
    cycleInl p q (cycleClass p x) = cycleClass _ (.inl x) := rfl

lemma cycleInl_injective (p : Perm α) (q : Perm β) :
    Function.Injective (cycleInl p q) := by
  intro x y
  induction x using Quotient.inductionOn with
  | h x =>
    induction y using Quotient.inductionOn with
    | h y =>
      change cycleClass (Equiv.sumCongr p q) (.inl x) = cycleClass _ (.inl y) →
        cycleClass p x = cycleClass p y
      simp only [cycleClass_eq, sumCongr_sameCycle_inl, imp_self]

lemma cycleInl_ne_inr (p : Perm α) (q : Perm β) (c : Cycles p) (y : β) :
    cycleInl p q c ≠ cycleClass _ (.inr y) := by
  induction c using Quotient.inductionOn with
  | h x =>
    change cycleClass (Equiv.sumCongr p q) (.inl x) ≠ cycleClass _ (.inr y)
    simp only [ne_eq, cycleClass_eq, sumCongr_not_sameCycle, not_false_eq_true]

end KaplanskyCounterexample.Planar

end

end OAI
end
/- CHECKPOINT: OAI.RingTheory.DirectFiniteness.CycleSums -/

/- BEGIN PINNED MODULE OAI.RingTheory.DirectFiniteness.OpenDiagrams -/
section

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6

noncomputable section
open scoped Classical
open scoped BigOperators
open Equiv Equiv.Perm
namespace KaplanskyCounterexample.Planar
open Equiv Equiv.Perm
variable {α : Type u_1} {β : Type u_2} {V : Type u_3} {F : Type u_4} {A : Type u_5} {B : Type u_6} [Fintype α] [Fintype β]
variable [AddCommGroup A] [AddCommGroup B]

/-- An auxiliary balanced component, without an exceptional white vertex. -/
structure ZeroBalanced (R : Ribbon α) (Inc : V → F → Prop)
    (ι : V → F → (A →+ B)) where
  blackLabel : α → V
  whiteLabel : α → F
  blackLabel_rot : ∀ a, blackLabel (R.black a) = blackLabel a
  whiteLabel_rot : ∀ a, whiteLabel (R.white a) = whiteLabel a
  incident : ∀ a, Inc (blackLabel a) (whiteLabel a)
  weight : α → A
  black_sum : ∀ c : Cycles R.black,
    ∑ a ∈ cycleSet R.black c, ι (blackLabel a) (whiteLabel a) (weight a) = 0
  white_sum : ∀ c : Cycles R.white, ∑ a ∈ cycleSet R.white c, weight a = 0

variable {R : Ribbon α} {S : Ribbon β} {Inc : V → F → Prop} {ι : V → F → (A →+ B)}

def WeakBalanced.sumZero (D : WeakBalanced R Inc ι) (E : ZeroBalanced S Inc ι) :
    WeakBalanced (R.sum S) Inc ι where
  blackLabel := Sum.elim D.blackLabel E.blackLabel
  whiteLabel := Sum.elim D.whiteLabel E.whiteLabel
  blackLabel_rot := by rintro (x | x); exact D.blackLabel_rot x; exact E.blackLabel_rot x
  whiteLabel_rot := by rintro (x | x); exact D.whiteLabel_rot x; exact E.whiteLabel_rot x
  incident := by rintro (x | x); exact D.incident x; exact E.incident x
  weight := Sum.elim D.weight E.weight
  exception := cycleInl R.white S.white D.exception
  black_sum c := by
    dsimp only [Ribbon.sum] at c ⊢
    induction c using Quotient.inductionOn with
    | h x =>
      cases x with
      | inl x =>
        change (∑ a ∈ cycleSet (Equiv.sumCongr R.black S.black) (cycleClass _ (.inl x)), _) = 0
        rw [sum_cycle_sum_left]
        exact D.black_sum _
      | inr x =>
        change (∑ a ∈ cycleSet (Equiv.sumCongr R.black S.black) (cycleClass _ (.inr x)), _) = 0
        rw [sum_cycle_sum_right]
        exact E.black_sum _
  white_sum c hc := by
    dsimp only [Ribbon.sum] at c hc ⊢
    induction c using Quotient.inductionOn with
    | h x =>
      cases x with
      | inl x =>
        have hne : cycleClass R.white x ≠ D.exception := by
          intro he
          exact hc (congrArg (cycleInl R.white S.white) he)
        change (∑ a ∈ cycleSet (Equiv.sumCongr R.white S.white) (cycleClass _ (.inl x)), _) = 0
        rw [sum_cycle_sum_left]
        exact D.white_sum _ hne
      | inr x =>
        change (∑ a ∈ cycleSet (Equiv.sumCongr R.white S.white) (cycleClass _ (.inr x)), _) = 0
        rw [sum_cycle_sum_right]
        exact E.white_sum _
  exceptional_sum := by
    generalize he : D.exception = e at *
    induction e using Quotient.inductionOn with
    | h x =>
      change (∑ a ∈ cycleSet (Equiv.sumCongr R.white S.white)
        (cycleClass _ (.inl x)), Sum.elim D.weight E.weight a) ≠ 0
      rw [sum_cycle_sum_left]
      change (∑ y ∈ cycleSet R.white ⟦x⟧, D.weight y) ≠ 0
      rw [← he]
      exact D.exceptional_sum

/-- The temporary boundary is an unlabelled black vertex. -/
def augInc (Inc : V → F → Prop) : Option V → F → Prop
  | none, _ => True
  | some v, f => Inc v f

def augMap (ι : V → F → (A →+ B)) : Option V → F → (A →+ B)
  | none, _ => 0
  | some v, f => ι v f

/-- A planar partially exposed lifetime diagram. The anchor has zero weight
and merely keeps a distinguished boundary rotation available at the empty word. -/
structure OpenDiagram (Inc : V → F → Prop) (ι : V → F → (A →+ B))
    (f₀ : F) (w : List (F × A)) where
  Edge : Type
  fintype : Fintype Edge
  ribbon : Ribbon Edge
  balanced : @WeakBalanced Edge (Option V) F A B fintype _ _ ribbon (augInc Inc) (augMap ι)
  planar : @Ribbon.GenusZero Edge fintype ribbon
  anchor : Edge
  boundary : List Edge
  nodup : (anchor :: boundary).Nodup
  rotation : Follows ribbon.black (anchor :: boundary)
  exposed : ∀ x, balanced.blackLabel x = none ↔ x ∈ anchor :: boundary
  anchor_weight : balanced.weight anchor = 0
  anchor_label : balanced.whiteLabel anchor = f₀
  word : boundary.map (fun x => (balanced.whiteLabel x, balanced.weight x)) = w

attribute [instance] OpenDiagram.fintype

end KaplanskyCounterexample.Planar

end

end OAI
end
/- CHECKPOINT: OAI.RingTheory.DirectFiniteness.OpenDiagrams -/

/- BEGIN PINNED MODULE OAI.RingTheory.DirectFiniteness.DiagramObstruction -/
section

namespace OAI

universe u_1 u_2 u_3 u_4 u_5

noncomputable section
open scoped Classical
open scoped BigOperators
open Equiv Equiv.Perm
namespace KaplanskyCounterexample.Planar
open Equiv Equiv.Perm
variable {α : Type u_1} {V : Type u_2} {F : Type u_3} {A : Type u_4} {B : Type u_5} [Fintype α] [AddCommGroup A] [AddCommGroup B]

lemma Ribbon.genusZero_white_one (p : Perm α) : (Ribbon.mk p 1).GenusZero := by
  have hcomp : (Ribbon.mk p 1).components = SameCycle.setoid p := by
    unfold Ribbon.components
    apply sup_eq_left.mpr
    intro x y h
    exact (sameCycle_one.mp h).sameCycle p
  unfold Ribbon.GenusZero
  simp only [Ribbon.face, one_mul, hcomp, cycles_one_card]
  dsimp only [Cycles]
  omega

variable (Inc : V → F → Prop) (ι : V → F → (A →+ B))

omit [Fintype α] in
def OpenDiagram.initial (f₀ : F) (c : A) (hc : c ≠ 0) :
    OpenDiagram Inc ι f₀ [(f₀, c)] where
  Edge := Bool
  fintype := inferInstance
  ribbon := ⟨@List.formPerm Bool (fun a b => Classical.propDecidable (a = b)) [false, true], 1⟩
  balanced := {
    blackLabel := fun _ => none
    whiteLabel := fun _ => f₀
    blackLabel_rot := fun _ => rfl
    whiteLabel_rot := fun _ => rfl
    incident := fun _ => trivial
    weight := fun x => if x then c else 0
    exception := cycleClass 1 true
    black_sum := by intro d; simp [augMap]
    white_sum := by
      intro d hd
      induction d using Quotient.inductionOn with
      | h x =>
        change (∑ a ∈ cycleSet 1 (cycleClass 1 x), if a then c else 0) = 0
        rw [cycleSet_singleton_of_fixed 1 x rfl, Finset.sum_singleton]
        cases x
        · rfl
        · exact (hd rfl).elim
    exceptional_sum := by
      rw [cycleSet_singleton_of_fixed 1 true rfl, Finset.sum_singleton]
      exact hc }
  planar := Ribbon.genusZero_white_one _
  anchor := false
  boundary := [true]
  nodup := by decide
  rotation := fun _ _ => rfl
  exposed := by intro x; cases x <;> simp
  anchor_weight := rfl
  anchor_label := rfl
  word := rfl

variable {Inc ι}

omit [Fintype α] in
def OpenDiagram.close (f₀ : F) (D : OpenDiagram Inc ι f₀ [])
    (v₀ : V) (hv : Inc v₀ f₀) : WeakBalanced D.ribbon Inc ι := by
  have hb : D.boundary = [] := List.map_eq_nil_iff.mp D.word
  have hn (x : D.Edge) : D.balanced.blackLabel x = none ↔ x = D.anchor := by
    simpa [hb] using D.exposed x
  let bl : D.Edge → V := fun x => (D.balanced.blackLabel x).getD v₀
  have heval (x : D.Edge) : ι (bl x) (D.balanced.whiteLabel x) (D.balanced.weight x) =
      augMap ι (D.balanced.blackLabel x) (D.balanced.whiteLabel x) (D.balanced.weight x) := by
    cases h : D.balanced.blackLabel x with
    | none =>
      have hx := (hn x).mp h
      rw [hx, D.anchor_weight]
      simp
    | some v => simp [bl, h, augMap]
  exact {
    blackLabel := bl
    whiteLabel := D.balanced.whiteLabel
    blackLabel_rot := fun x => congrArg (fun v => v.getD v₀) (D.balanced.blackLabel_rot x)
    whiteLabel_rot := D.balanced.whiteLabel_rot
    incident := fun x => by
      cases h : D.balanced.blackLabel x with
      | none =>
        have hx := (hn x).mp h
        have hanc := (hn D.anchor).mpr rfl
        simpa [bl, hx, hanc, D.anchor_label] using hv
      | some v =>
        have hi := D.balanced.incident x
        simpa [augInc, bl, h] using hi
    weight := D.balanced.weight
    exception := D.balanced.exception
    black_sum := fun d => by simpa only [heval] using D.balanced.black_sum d
    white_sum := D.balanced.white_sum
    exceptional_sum := D.balanced.exceptional_sum }

omit [Fintype α] in
theorem OpenDiagram.not_empty (f₀ : F) (D : OpenDiagram Inc ι f₀ [])
    (v₀ : V) (hv : Inc v₀ f₀)
    (hinj : ∀ v f, Inc v f → Function.Injective (ι v f))
    (hind : ∀ v f g, Inc v f → Inc v g → f ≠ g →
      ∀ a b, ι v f a + ι v g b = 0 → a = 0)
    (hgirth : 12 ≤ (incidenceGraph Inc).egirth) : False :=
  (D.close f₀ v₀ hv).not_genusZero hinj hind hgirth D.planar

end KaplanskyCounterexample.Planar

end

end OAI
end
/- CHECKPOINT: OAI.RingTheory.DirectFiniteness.DiagramObstruction -/

/- BEGIN PINNED MODULE OAI.RingTheory.DirectFiniteness.BoundaryFilling -/
section

namespace OAI

universe u_1 u_2 u_3 u_4 u_5

noncomputable section
open scoped Classical
open scoped BigOperators
open Equiv Equiv.Perm
namespace KaplanskyCounterexample.Planar
open Equiv Equiv.Perm
variable {α : Type u_1} {V : Type u_2} {F : Type u_3} {A : Type u_4} {B : Type u_5} [Fintype α] [AddCommGroup A] [AddCommGroup B]
variable {R : Ribbon α} {Inc : V → F → Prop} {ι : V → F → (A →+ B)}

def WeakBalanced.split_none (D : WeakBalanced R (augInc Inc) (augMap ι))
    (a b : α) (ha : D.blackLabel a = none) (hb : D.blackLabel b = none)
    (hab : R.black.SameCycle a b) : WeakBalanced (R.swapBlack a b) (augInc Inc) (augMap ι) where
  blackLabel := D.blackLabel
  whiteLabel := D.whiteLabel
  blackLabel_rot x := by
    apply label_sameCycle R.black D.blackLabel D.blackLabel_rot
    exact sameCycle_after_swap hab (SameCycle.apply_left SameCycle.rfl)
  whiteLabel_rot := D.whiteLabel_rot
  incident := D.incident
  weight := D.weight
  exception := D.exception
  black_sum c := by
    induction c using Quotient.inductionOn with
    | h x =>
      by_cases hx : D.blackLabel x = none
      · apply Finset.sum_eq_zero
        intro y hy
        have hyx : R.black.SameCycle y x := sameCycle_after_swap hab
          ((cycleClass_eq _ _ _).mp ((mem_cycleSet _ _ _).mp hy))
        have hl := label_sameCycle R.black D.blackLabel D.blackLabel_rot hyx
        simp only [hl, hx, augMap, AddMonoidHom.zero_apply]
      · have heq (z : α) (hz : R.black.SameCycle x z) :
            (R.swapBlack a b).black z = R.black z := by
          change swap a b (R.black z) = R.black z
          apply swap_apply_of_ne_of_ne
          · intro hz'
            have hl := label_sameCycle R.black D.blackLabel D.blackLabel_rot
              hz.apply_right
            rw [hz', ha] at hl
            exact hx hl
          · intro hz'
            have hl := label_sameCycle R.black D.blackLabel D.blackLabel_rot
              hz.apply_right
            rw [hz', hb] at hl
            exact hx hl
        change (∑ y ∈ cycleSet (R.swapBlack a b).black
          (cycleClass _ x), augMap ι (D.blackLabel y) (D.whiteLabel y) (D.weight y)) = 0
        rw [cycleSet_eq_of_eqOn_cycle R.black (R.swapBlack a b).black x heq]
        exact D.black_sum _
  white_sum := D.white_sum
  exceptional_sum := D.exceptional_sum

def WeakBalanced.fill (D : WeakBalanced R (augInc Inc) (augMap ι))
    (l : List α) (hd : l.Nodup) (hrot : Follows R.black l) (v : V)
    (hinc : ∀ x ∈ l, Inc v (D.whiteLabel x))
    (hsum : (∑ x ∈ l.toFinset, ι v (D.whiteLabel x) (D.weight x)) = 0) :
    WeakBalanced R (augInc Inc) (augMap ι) where
  blackLabel x := if x ∈ l then some v else D.blackLabel x
  whiteLabel := D.whiteLabel
  blackLabel_rot x := by simp only [hrot.invariant, D.blackLabel_rot]
  whiteLabel_rot := D.whiteLabel_rot
  incident x := by
    by_cases hx : x ∈ l
    · simpa only [ite_eq_left hx, augInc] using hinc x hx
    · simpa only [ite_eq_right hx] using D.incident x
  weight := D.weight
  exception := D.exception
  black_sum c := by
    induction c using Quotient.inductionOn with
    | h x =>
      by_cases hx : x ∈ l
      · change (∑ y ∈ cycleSet R.black (cycleClass R.black x), _) = 0
        rw [hrot.cycleSet hd hx]
        calc
          _ = ∑ y ∈ l.toFinset, ι v (D.whiteLabel y) (D.weight y) := by
            apply Finset.sum_congr rfl
            intro y hy
            simp only [List.mem_toFinset.mp hy, ↓reduceIte, augMap]
          _ = 0 := hsum
      · calc
          _ = ∑ y ∈ cycleSet R.black ⟦x⟧,
              augMap ι (D.blackLabel y) (D.whiteLabel y) (D.weight y) := by
            apply Finset.sum_congr rfl
            intro y hy
            have hxy : R.black.SameCycle y x :=
              (cycleClass_eq _ _ _).mp ((mem_cycleSet _ _ _).mp hy)
            have hy' : y ∉ l := fun hy' => hx
              ((perm_invariant_cycle R.black (fun z => z ∈ l) hrot.invariant hxy).mp hy')
            rw [ite_eq_right hy']
          _ = 0 := D.black_sum _
  white_sum := D.white_sum
  exceptional_sum := D.exceptional_sum

end KaplanskyCounterexample.Planar

end

end OAI
end
/- CHECKPOINT: OAI.RingTheory.DirectFiniteness.BoundaryFilling -/

/- BEGIN PINNED MODULE OAI.RingTheory.DirectFiniteness.BoundarySplitting -/
section

namespace OAI

universe u_1

noncomputable section
open scoped Classical
open scoped BigOperators
open Equiv Equiv.Perm
namespace KaplanskyCounterexample.Planar
open Equiv Equiv.Perm
variable {α : Type u_1}

lemma Follows.append_rotate {p : Perm α} {l m : List α} (h : Follows p (l ++ m))
    (hd : (l ++ m).Nodup) : Follows p (m ++ l) := by
  intro x hx
  have hx' : x ∈ l ++ m := by simpa only [List.mem_append, or_comm] using hx
  rw [h x hx', List.formPerm_eq_of_isRotated hd List.isRotated_append]

lemma Follows.split {p : Perm α} {a b : α} {l m : List α}
    (h : Follows p ((a :: l) ++ (b :: m))) (hd : ((a :: l) ++ (b :: m)).Nodup) :
    Follows (swap a b * p) (a :: l) ∧ Follows (swap a b * p) (b :: m) := by
  classical
  have hdis : List.Disjoint (a :: l) (b :: m) := by
    intro x hx hy
    exact (List.nodup_append.mp hd).2.2 x hx x hy rfl
  have hb : b ∉ a :: l := fun hb => hdis hb (by simp)
  have heq (x : α) (hx : x ∈ (a :: l) ++ (b :: m)) :
      (swap a b * p) x = (a :: l).formPerm ((b :: m).formPerm x) := by
    rw [Perm.mul_apply, h x hx, formPerm_append_nonempty a b l m hb]
    simp only [Perm.mul_apply, swap_apply_self]
  constructor
  · intro x hx
    have hx' : x ∉ b :: m := fun hx' => hdis hx hx'
    rw [heq x (List.mem_append_left _ hx), List.formPerm_apply_of_notMem hx']
  · intro x hx
    rw [heq x (List.mem_append_right _ hx)]
    apply List.formPerm_apply_of_notMem
    exact fun hx' => hdis hx' ((b :: m).formPerm_apply_mem_of_mem hx)

end KaplanskyCounterexample.Planar

end

end OAI
end
/- CHECKPOINT: OAI.RingTheory.DirectFiniteness.BoundarySplitting -/

/- BEGIN PINNED MODULE OAI.RingTheory.DirectFiniteness.DiagramDeletion -/
section

namespace OAI

universe u_1 u_2 u_3 u_4

noncomputable section
open scoped Classical
open scoped BigOperators
open Equiv Equiv.Perm
namespace KaplanskyCounterexample.Planar
open Equiv Equiv.Perm
variable {V : Type u_1} {F : Type u_2} {A : Type u_3} {B : Type u_4} [AddCommGroup A] [AddCommGroup B]
variable {Inc : V → F → Prop} {ι : V → F → (A →+ B)} {f₀ : F} {w : List (F × A)}

theorem OpenDiagram.deleteBlock (D : OpenDiagram Inc ι f₀ w)
    (pre r post : List D.Edge) (hboundary : D.boundary = pre ++ r ++ post)
    (v : V) (hinc : ∀ x ∈ r, Inc v (D.balanced.whiteLabel x))
    (hsum : (∑ x ∈ r.toFinset, ι v (D.balanced.whiteLabel x) (D.balanced.weight x)) = 0) :
    Nonempty (OpenDiagram Inc ι f₀ ((pre ++ post).map
      (fun x => (D.balanced.whiteLabel x, D.balanced.weight x)))) := by
  classical
  cases r with
  | nil =>
    have hw : w = (pre ++ post).map (fun x => (D.balanced.whiteLabel x, D.balanced.weight x)) := by
      exact D.word.symm.trans (congrArg _ (by simpa only [List.append_nil] using hboundary))
    exact ⟨hw ▸ D⟩
  | cons a r =>
    let M := post ++ D.anchor :: pre
    have hM : M ≠ [] := by
      intro empty
      have member : D.anchor ∈ M := List.mem_append_right post (List.mem_cons_self ..)
      rw [empty] at member
      exact List.not_mem_nil member
    obtain ⟨b, m, hbm⟩ := List.exists_cons_of_ne_nil hM
    have hrot : Follows D.ribbon.black ((D.anchor :: pre) ++ ((a :: r) ++ post)) := by
      simpa only [hboundary, List.cons_append, List.append_assoc] using D.rotation
    have hnd : (((D.anchor :: pre) ++ ((a :: r) ++ post))).Nodup := by
      simpa only [hboundary, List.cons_append, List.append_assoc] using D.nodup
    have hrot' : Follows D.ribbon.black ((a :: r) ++ (b :: m)) := by
      simpa only [List.append_assoc, ← hbm] using hrot.append_rotate hnd
    have hnd' : ((a :: r) ++ (b :: m)).Nodup := by
      have hn := (List.nodup_append_comm).mp hnd
      simpa only [List.append_assoc, ← hbm] using hn
    have hmem (x : D.Edge) : x ∈ D.anchor :: D.boundary ↔ x ∈ (a :: r) ++ (b :: m) := by
      simp only [hboundary, ← hbm, M, List.mem_cons, List.mem_append]
      constructor
      · rintro (anchor | ((before | (head | tail)) | suffix))
        · exact Or.inr (Or.inr (Or.inl anchor))
        · exact Or.inr (Or.inr (Or.inr before))
        · exact Or.inl (Or.inl head)
        · exact Or.inl (Or.inr tail)
        · exact Or.inr (Or.inl suffix)
      · rintro ((head | tail) | (suffix | anchor | before))
        · exact Or.inr (Or.inl (Or.inr (Or.inl head)))
        · exact Or.inr (Or.inl (Or.inr (Or.inr tail)))
        · exact Or.inr (Or.inr suffix)
        · exact Or.inl anchor
        · exact Or.inr (Or.inl (Or.inl before))
    have hab : D.ribbon.black.SameCycle a b := hrot'.sameCycle hnd'
      (List.mem_append_left _ (List.mem_cons_self ..))
      (List.mem_append_right _ (List.mem_cons_self ..))
    have habne : a ≠ b := by
      intro h
      exact (List.nodup_append.mp hnd').2.2 a (List.mem_cons_self ..)
        b (List.mem_cons_self ..) h
    have ha : D.balanced.blackLabel a = none :=
      (D.exposed a).mpr ((hmem a).mpr
        (List.mem_append_left _ (List.mem_cons_self ..)))
    have hb : D.balanced.blackLabel b = none :=
      (D.exposed b).mpr ((hmem b).mpr
        (List.mem_append_right _ (List.mem_cons_self ..)))
    let S := D.ribbon.swapBlack a b
    have hsplit := hrot'.split hnd'
    let E := (D.balanced.split_none a b ha hb hab).fill (a :: r)
      (List.nodup_append.mp hnd').1 hsplit.1 v hinc hsum
    have hmrot : Follows S.black (D.anchor :: (pre ++ post)) := by
      have hh : Follows S.black (post ++ (D.anchor :: pre)) := by
        simpa only [← hbm, S, Ribbon.swapBlack, M] using hsplit.2
      have hn : (post ++ (D.anchor :: pre)).Nodup := by
        simpa only [← hbm] using (List.nodup_append.mp hnd').2.1
      simpa only [List.cons_append] using hh.append_rotate hn
    have hmnd : (D.anchor :: (pre ++ post)).Nodup := by
      have hn : (post ++ (D.anchor :: pre)).Nodup := by
        simpa only [← hbm] using (List.nodup_append.mp hnd').2.1
      simpa only [List.cons_append] using List.nodup_append_comm.mp hn
    have hrem (x : D.Edge) : x ∈ b :: m ↔ x ∈ D.anchor :: (pre ++ post) := by
      simp only [← hbm, M, List.mem_append, List.mem_cons]
      constructor
      · rintro (suffix | anchor | before)
        · exact Or.inr (Or.inr suffix)
        · exact Or.inl anchor
        · exact Or.inr (Or.inl before)
      · rintro (anchor | before | suffix)
        · exact Or.inr (Or.inl anchor)
        · exact Or.inr (Or.inr before)
        · exact Or.inl suffix
    exact ⟨{
      Edge := D.Edge
      fintype := inferInstance
      ribbon := S
      balanced := E
      planar := D.ribbon.genusZero_swapBlack_split D.planar a b habne hab
      anchor := D.anchor
      boundary := pre ++ post
      nodup := hmnd
      rotation := hmrot
      exposed := fun x => by
        change (if x ∈ a :: r then some v else D.balanced.blackLabel x) = none ↔ _
        by_cases hx : x ∈ a :: r
        · rw [ite_eq_left hx]
          constructor
          · exact fun impossible => False.elim (Option.some_ne_none v impossible)
          · intro retained
            exact False.elim
              ((List.nodup_append.mp hnd').2.2 x hx x ((hrem x).mpr retained) rfl)
        · rw [ite_eq_right hx]
          constructor
          · intro exposed
            rcases List.mem_append.mp ((hmem x).mp ((D.exposed x).mp exposed)) with
              removed | retained
            · exact False.elim (hx removed)
            · exact (hrem x).mp retained
          · intro retained
            exact (D.exposed x).mpr ((hmem x).mpr
              (List.mem_append_right _ ((hrem x).mpr retained)))
      anchor_weight := D.anchor_weight
      anchor_label := D.anchor_label
      word := rfl }⟩

end KaplanskyCounterexample.Planar

end

end OAI
end
/- CHECKPOINT: OAI.RingTheory.DirectFiniteness.DiagramDeletion -/

/- BEGIN PINNED MODULE OAI.RingTheory.DirectFiniteness.WordWheels -/
section

namespace OAI

universe u_1 u_2 u_3 u_4 u_5

noncomputable section
open scoped Classical
open scoped BigOperators
open Equiv Equiv.Perm
namespace KaplanskyCounterexample.Planar
open Equiv Equiv.Perm
variable {α : Type u_1} {V : Type u_2} {F : Type u_3} {A : Type u_4} {B : Type u_5} [Fintype α] [AddCommGroup A] [AddCommGroup B]

lemma cycleSet_wheel_white (p : Perm α) (x : α ⊕ α) :
    cycleSet (Ribbon.wheel p).white (cycleClass _ x) =
      {Sum.inl (sumIndex x), Sum.inr (sumIndex x)} := by
  ext y
  rw [mem_cycleSet, cycleClass_eq]
  change (SameCycle.setoid (Ribbon.wheel p).white).r y x ↔ _
  rw [wheel_white_setoid]
  cases x <;> cases y <;> simp [sumIndex]

variable {Inc : V → F → Prop} {ι : V → F → (A →+ B)}

def ZeroBalanced.wheel (p : Perm α) (v : V) (fl : α → F) (w : α → A)
    (hinc : ∀ x, Inc v (fl x))
    (hsum : ∀ c : Cycles p⁻¹, (∑ x ∈ cycleSet p⁻¹ c, ι v (fl x) (w x)) = 0) :
    ZeroBalanced (Ribbon.wheel p) (augInc Inc) (augMap ι) where
  blackLabel := Sum.elim (fun _ => none) (fun _ => some v)
  whiteLabel := Sum.elim fl fl
  blackLabel_rot := by rintro (x | x) <;> rfl
  whiteLabel_rot := by rintro (x | x) <;> rfl
  incident := by rintro (x | x); trivial; exact hinc x
  weight := Sum.elim w (fun x => -w x)
  black_sum c := by
    dsimp only [Ribbon.wheel] at c ⊢
    induction c using Quotient.inductionOn with
    | h x =>
      cases x with
      | inl x =>
        change (∑ y ∈ cycleSet (Equiv.sumCongr p p⁻¹) (cycleClass _ (.inl x)), _) = 0
        rw [sum_cycle_sum_left]
        simp [augMap]
      | inr x =>
        change (∑ y ∈ cycleSet (Equiv.sumCongr p p⁻¹) (cycleClass _ (.inr x)), _) = 0
        rw [sum_cycle_sum_right]
        simpa only [Sum.elim_inr, augMap, map_neg, Finset.sum_neg_distrib, neg_eq_zero] using hsum (cycleClass p⁻¹ x)
  white_sum c := by
    induction c using Quotient.inductionOn with
    | h x =>
      change (∑ y ∈ cycleSet (Ribbon.wheel p).white (cycleClass _ x), _) = 0
      rw [cycleSet_wheel_white, Finset.sum_pair (by simp)]
      simp only [Sum.elim_inl, Sum.elim_inr, add_neg_cancel]

lemma cycleSet_finRange_inv (n : ℕ) (c : Cycles (List.finRange n).formPerm⁻¹) :
    cycleSet (List.finRange n).formPerm⁻¹ c = Finset.univ := by
  induction c using Quotient.inductionOn with
  | h x =>
    ext y
    simp only [mem_cycleSet, Finset.mem_univ, iff_true]
    apply (cycleClass_eq _ _ _).mpr
    apply sameCycle_inv.mpr
    exact (List.nodup_finRange n).isCycleOn_formPerm.2 (by simp) (by simp)

omit [Fintype α] in
def wordWheel (r : List (F × A)) (v : V)
    (hinc : ∀ t ∈ r, Inc v t.1)
    (hsum : (r.map (fun t => ι v t.1 t.2)).sum = 0) :
    ZeroBalanced (Ribbon.wheel (List.finRange r.length).formPerm) (augInc Inc) (augMap ι) :=
  ZeroBalanced.wheel _ v (fun i => (r.get i).1) (fun i => (r.get i).2)
    (fun i => hinc _ (List.get_mem r i)) (by
      intro c
      rw [cycleSet_finRange_inv]
      rw [← List.sum_ofFn]
      change (List.ofFn ((fun t : F × A => ι v t.1 t.2) ∘ r.get)).sum = 0
      rw [← List.map_ofFn, List.ofFn_get]
      exact hsum)

end KaplanskyCounterexample.Planar

end

end OAI
end
/- CHECKPOINT: OAI.RingTheory.DirectFiniteness.WordWheels -/

/- BEGIN PINNED MODULE OAI.RingTheory.DirectFiniteness.DiagramJoining -/
section

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6

noncomputable section
open scoped Classical
open scoped BigOperators
open Equiv Equiv.Perm
namespace KaplanskyCounterexample.Planar
open Equiv Equiv.Perm
variable {α : Type u_1} {β : Type u_2}

lemma Follows.map_sum_right {p : Perm α} {q : Perm β} {l : List β}
    (h : Follows q l) : Follows (Equiv.sumCongr p q) (l.map Sum.inr) := by
  classical
  intro y hy
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
  simpa only [Equiv.sumCongr_apply, Sum.map_inr,
    formPerm_map_apply Sum.inr Sum.inr_injective] using congrArg Sum.inr (h x hx)

lemma Follows.merge {p : Perm α} {a b : α} {l m : List α}
    (hl : Follows p (a :: l)) (hm : Follows p (b :: m))
    (hdis : List.Disjoint (a :: l) (b :: m)) :
    Follows (swap a b * p) ((a :: l) ++ (b :: m)) := by
  classical
  have hb : b ∉ a :: l := fun hb => hdis hb (by simp)
  intro x hx
  rw [formPerm_append_nonempty a b l m hb]
  simp only [Perm.mul_apply]
  apply congrArg (swap a b)
  rcases List.mem_append.mp hx with hx | hx
  · rw [List.formPerm_apply_of_notMem (fun h => hdis hx h)]
    exact hl x hx
  · rw [List.formPerm_apply_of_notMem (fun h => hdis h ((b :: m).formPerm_apply_mem_of_mem hx))]
    exact hm x hx

variable [Fintype α]
variable {V : Type u_3} {F : Type u_4} {A : Type u_5} {B : Type u_6} [AddCommGroup A] [AddCommGroup B]
variable {R : Ribbon α} {Inc : V → F → Prop} {ι : V → F → (A →+ B)}

def WeakBalanced.joinBlack (D : WeakBalanced R Inc ι) (a b : α)
    (hcycle : ¬ R.black.SameCycle a b) (hlabel : D.blackLabel a = D.blackLabel b) :
    WeakBalanced (R.swapBlack a b) Inc ι :=
  D.coarsen (R.swapBlack a b) (sameCycle_swap_mul R.black a b hcycle) (fun h => h)
    (fun x => by
      change D.blackLabel (swap a b (R.black x)) = D.blackLabel x
      rw [label_swap D.blackLabel a b hlabel, D.blackLabel_rot]) D.whiteLabel_rot

end KaplanskyCounterexample.Planar

end

end OAI
end
/- CHECKPOINT: OAI.RingTheory.DirectFiniteness.DiagramJoining -/

/- BEGIN PINNED MODULE OAI.RingTheory.DirectFiniteness.WordCycles -/
section

namespace OAI

universe u_1

noncomputable section
open scoped Classical
open scoped BigOperators
open Equiv Equiv.Perm
namespace KaplanskyCounterexample.Planar
open Equiv Equiv.Perm
variable {α : Type u_1}

lemma follows_formPerm [DecidableEq α] (l : List α) : Follows l.formPerm l := by
  intro x _
  exact congrArg (fun d : DecidableEq α => @List.formPerm α d l x)
    (Subsingleton.elim _ _)

end KaplanskyCounterexample.Planar

end

end OAI
end
/- CHECKPOINT: OAI.RingTheory.DirectFiniteness.WordCycles -/

/- BEGIN PINNED MODULE OAI.RingTheory.DirectFiniteness.DiagramInsertion -/
section

namespace OAI

noncomputable section
open scoped Classical
open scoped BigOperators
open Equiv Equiv.Perm
namespace KaplanskyCounterexample.Planar
open Equiv Equiv.Perm
variable {V F A B : Type} [AddCommGroup A] [AddCommGroup B]
variable {Inc : V → F → Prop} {ι : V → F → (A →+ B)}
variable {f₀ : F} {w : List (F × A)}

theorem OpenDiagram.insertBlock (D : OpenDiagram Inc ι f₀ w)
    (pre post : List D.Edge) (hboundary : D.boundary = pre ++ post)
    (r : List (F × A)) (v : V) (hinc : ∀ t ∈ r, Inc v t.1)
    (hsum : (r.map (fun t => ι v t.1 t.2)).sum = 0) :
    Nonempty (OpenDiagram Inc ι f₀
      (pre.map (fun x => (D.balanced.whiteLabel x, D.balanced.weight x)) ++ r ++
        post.map (fun x => (D.balanced.whiteLabel x, D.balanced.weight x)))) := by
  classical
  by_cases hr : r = []
  · subst r
    have hw : w = pre.map (fun x => (D.balanced.whiteLabel x, D.balanced.weight x)) ++
        [] ++ post.map (fun x => (D.balanced.whiteLabel x, D.balanced.weight x)) := by
      exact D.word.symm.trans (by rw [hboundary, List.map_append, List.append_nil])
    exact ⟨hw ▸ D⟩
  let p := (List.finRange r.length).formPerm
  let W := wordWheel r v hinc hsum
  let T := D.ribbon.sum (Ribbon.wheel p)
  let E := D.balanced.sumZero W
  let f : D.Edge → D.Edge ⊕ (Fin r.length ⊕ Fin r.length) := Sum.inl
  let g : Fin r.length → D.Edge ⊕ (Fin r.length ⊕ Fin r.length) := Sum.inr ∘ Sum.inl
  let Q := (List.finRange r.length).map g
  let M := (post ++ D.anchor :: pre).map f
  have hqn : Q ≠ [] := by
    intro he
    have hh : r.length = 0 := by simpa only [Q, List.length_map, List.length_finRange, List.length_nil] using congrArg List.length he
    exact hr (List.length_eq_zero_iff.mp hh)
  have hmn : M ≠ [] := by simp [M]
  obtain ⟨a, l, hqa⟩ := List.exists_cons_of_ne_nil hqn
  obtain ⟨b, m, hmb⟩ := List.exists_cons_of_ne_nil hmn
  have hnd₀ : ((D.anchor :: pre) ++ post).Nodup := by
    simpa only [hboundary, List.cons_append] using D.nodup
  have hrot₀ : Follows D.ribbon.black ((D.anchor :: pre) ++ post) := by
    simpa only [hboundary, List.cons_append] using D.rotation
  have hndM : M.Nodup := (List.nodup_append_comm.mp hnd₀).map Sum.inl_injective
  have hndQ : Q.Nodup := (List.nodup_finRange _).map (Sum.inr_injective.comp Sum.inl_injective)
  have hM : Follows T.black M := by
    exact (hrot₀.append_rotate hnd₀).map_sum_left
  have hQ : Follows T.black Q := by
    have h : Follows (Ribbon.wheel p).black ((List.finRange r.length).map Sum.inl) :=
      (follows_formPerm (List.finRange r.length)).map_sum_left
    simpa only [List.map_map, T, Ribbon.sum, Q, g] using h.map_sum_right (p := D.ribbon.black)
  have hdis : List.Disjoint Q M := by
    intro x hx hy
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
    obtain ⟨j, _, hj⟩ := List.mem_map.mp hy
    exact Sum.inl_ne_inr (show (Sum.inl j : D.Edge ⊕ (Fin r.length ⊕ Fin r.length)) = Sum.inr (Sum.inl i) from hj)
  have hnd : (Q ++ M).Nodup := List.Nodup.append hndQ hndM hdis
  have hac : a ∈ Q := by rw [hqa]; simp
  have hbc : b ∈ M := by rw [hmb]; simp
  have hcomp : ¬ T.components.r a b := by
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hac
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hbc
    rw [Ribbon.sum_components]
    exact fun h => sumSetoid_cross _ _ j (Sum.inl i)
      ((sumSetoid D.ribbon.components (Ribbon.wheel p).components).iseqv.symm h)
  have hal : E.blackLabel a = none := by
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hac
    rfl
  have hbl : E.blackLabel b = none := by
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hbc
    apply (D.exposed j).mpr
    simpa only [hboundary, List.mem_append, List.mem_cons, or_assoc, or_left_comm, or_comm] using hj
  let S := T.swapBlack a b
  let Z := E.joinBlack a b (T.not_blackCycle_of_not_component hcomp) (hal.trans hbl.symm)
  have hrot : Follows S.black (Q ++ M) := by
    simp only [hqa, hmb] at hQ hM hdis ⊢
    exact hQ.merge hM hdis
  have hrot' : Follows S.black (f D.anchor :: (pre.map f ++ Q ++ post.map f)) := by
    have hh : Follows S.black ((Q ++ post.map f) ++ (f D.anchor :: pre.map f)) := by
      simpa only [M, List.map_append, List.map_cons, List.append_assoc] using hrot
    have hn : ((Q ++ post.map f) ++ (f D.anchor :: pre.map f)).Nodup := by
      simpa only [M, List.map_append, List.map_cons, List.append_assoc] using hnd
    simpa only [List.cons_append, List.append_assoc] using hh.append_rotate hn
  have hnd' : (f D.anchor :: (pre.map f ++ Q ++ post.map f)).Nodup := by
    have hn : ((Q ++ post.map f) ++ (f D.anchor :: pre.map f)).Nodup := by
      simpa only [M, List.map_append, List.map_cons, List.append_assoc] using hnd
    simpa only [List.cons_append, List.append_assoc] using List.nodup_append_comm.mp hn
  refine ⟨{
    Edge := D.Edge ⊕ (Fin r.length ⊕ Fin r.length)
    fintype := inferInstance
    ribbon := S
    balanced := Z
    planar := T.genusZero_swapBlack_merge (D.ribbon.genusZero_sum (Ribbon.wheel p) D.planar
      (Ribbon.genusZero_wheel p)) a b hcomp
    anchor := f D.anchor
    boundary := pre.map f ++ Q ++ post.map f
    nodup := hnd'
    rotation := hrot'
    exposed := ?_
    anchor_weight := D.anchor_weight
    anchor_label := D.anchor_label
    word := ?_ }⟩
  · rintro (x | (i | i))
    · change D.balanced.blackLabel x = none ↔ _
      rw [D.exposed, hboundary]
      simp [f, Q, g, List.mem_map, Function.comp_def, List.mem_append, List.mem_cons]
    · change (none : Option V) = none ↔ _
      simp [f, Q, g, List.mem_map, Function.comp_def]
    · change (some v : Option V) = none ↔ _
      simp [f, Q, g, List.mem_map, Function.comp_def]
  · change (pre.map f ++ Q ++ post.map f).map
        (fun x => (E.whiteLabel x, E.weight x)) = _
    simp only [List.map_append, List.map_map]
    congr 2
    dsimp only [Q]
    rw [List.map_map]
    change ((List.finRange r.length).map (fun i => r.get i)) = r
    exact List.map_get_finRange r

end KaplanskyCounterexample.Planar

end

end OAI
end
/- CHECKPOINT: OAI.RingTheory.DirectFiniteness.DiagramInsertion -/

/- BEGIN PINNED MODULE OAI.RingTheory.DirectFiniteness.WordDiagrams -/
section

namespace OAI

noncomputable section
open scoped Classical
open scoped BigOperators
open Equiv Equiv.Perm
namespace KaplanskyCounterexample.Planar
variable {V F A B : Type} [AddCommGroup A] [AddCommGroup B]
variable {Inc : V → F → Prop} {ι : V → F → (A →+ B)} {f₀ : F}

theorem OpenDiagram.deleteWordBlock (pre r post : List (F × A))
    (v : V) (hinc : ∀ t ∈ r, Inc v t.1)
    (hsum : (r.map (fun t => ι v t.1 t.2)).sum = 0)
    (D : OpenDiagram Inc ι f₀ (pre ++ r ++ post)) :
    Nonempty (OpenDiagram Inc ι f₀ (pre ++ post)) := by
  classical
  obtain ⟨p, q, hpq, hp, hq⟩ := List.map_eq_append_iff.mp
    (D.word.trans (List.append_assoc pre r post))
  obtain ⟨s, t, hst, hs, ht⟩ := List.map_eq_append_iff.mp hq
  have hboundary : D.boundary = p ++ s ++ t := by
    exact hpq.trans ((congrArg (p ++ ·) hst).trans (List.append_assoc p s t).symm)
  have hnd : s.Nodup := by
    have hh := D.nodup.tail
    rw [hboundary] at hh
    exact (List.nodup_append.mp (List.nodup_append.mp hh).1).2.1
  have hinc' : ∀ x ∈ s, Inc v (D.balanced.whiteLabel x) := by
    intro x hx
    apply hinc (D.balanced.whiteLabel x, D.balanced.weight x)
    simpa only [hs] using (List.mem_map_of_mem (f := fun x =>
      (D.balanced.whiteLabel x, D.balanced.weight x)) hx)
  have hsum' : (∑ x ∈ s.toFinset,
      ι v (D.balanced.whiteLabel x) (D.balanced.weight x)) = 0 := by
    rw [List.sum_toFinset _ hnd]
    have hh := hsum
    rw [← hs, List.map_map] at hh
    exact hh
  obtain ⟨E⟩ := D.deleteBlock p s t hboundary v hinc' hsum'
  have he : (p ++ t).map (fun x => (D.balanced.whiteLabel x, D.balanced.weight x)) =
      pre ++ post := by rw [List.map_append, hp, ht]
  exact ⟨he ▸ E⟩

theorem OpenDiagram.insertWordBlock (pre r post : List (F × A))
    (v : V) (hinc : ∀ t ∈ r, Inc v t.1)
    (hsum : (r.map (fun t => ι v t.1 t.2)).sum = 0)
    (D : OpenDiagram Inc ι f₀ (pre ++ post)) :
    Nonempty (OpenDiagram Inc ι f₀ (pre ++ r ++ post)) := by
  obtain ⟨p, q, hpq, hp, hq⟩ := List.map_eq_append_iff.mp D.word
  obtain ⟨E⟩ := D.insertBlock p q hpq r v hinc hsum
  rw [hp, hq] at E
  exact ⟨E⟩

end KaplanskyCounterexample.Planar

end

end OAI
end
/- CHECKPOINT: OAI.RingTheory.DirectFiniteness.WordDiagrams -/

/- BEGIN PINNED MODULE OAI.RingTheory.DirectFiniteness.WordReduction -/
section

namespace OAI

universe u_1 u_2

noncomputable section
open scoped Classical
open scoped BigOperators
open Equiv Equiv.Perm
namespace KaplanskyCounterexample.WordReduction
variable {α : Type u_1}
abbrev Word (α : Type u_2) := List (α × Bool)

inductive Delete (Allowed : Word α → Prop) : Word α → Word α → Prop
  | block (pre r post : Word α) (hr : Allowed r) :
      Delete Allowed (pre ++ r ++ post) (pre ++ post)

abbrev Related (Allowed : Word α → Prop) := Relation.EqvGen (Delete Allowed)

variable {Allowed : Word α → Prop}

lemma rel_trans {u v w : Word α} (h₁ : Related Allowed u v) (h₂ : Related Allowed v w) :
    Related Allowed u w := Relation.EqvGen.trans _ _ _ h₁ h₂

lemma rel_symm {u v : Word α} (h : Related Allowed u v) :
    Related Allowed v u := Relation.EqvGen.symm _ _ h

lemma Related.append_left {u v : Word α} (h : Related Allowed u v) (w : Word α) :
    Related Allowed (w ++ u) (w ++ v) := by
  induction h with
  | rel x y h =>
    cases h with
    | block pre r post hr =>
      simpa only [List.append_assoc] using Relation.EqvGen.rel _ _ (Delete.block (w ++ pre) r post hr)
  | refl x => exact .refl _
  | symm _ _ _ ih => exact rel_symm ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact rel_trans ih₁ ih₂

lemma Related.append_right {u v : Word α} (h : Related Allowed u v) (w : Word α) :
    Related Allowed (u ++ w) (v ++ w) := by
  induction h with
  | rel x y h =>
    cases h with
    | block pre r post hr =>
      simpa only [List.append_assoc] using Relation.EqvGen.rel _ _ (Delete.block pre r (post ++ w) hr)
  | refl x => exact .refl _
  | symm _ _ _ ih => exact rel_symm ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact rel_trans ih₁ ih₂

lemma Related.inv (hinv : ∀ w, Allowed w → Allowed (FreeGroup.invRev w))
    {u v : Word α} (h : Related Allowed u v) :
    Related Allowed (FreeGroup.invRev u) (FreeGroup.invRev v) := by
  induction h with
  | rel x y h =>
    cases h with
    | block pre r post hr =>
      simpa only [FreeGroup.invRev_append, List.append_assoc] using
        Relation.EqvGen.rel _ _ (Delete.block (FreeGroup.invRev post) (FreeGroup.invRev r)
          (FreeGroup.invRev pre) (hinv r hr))
  | refl x => exact .refl _
  | symm _ _ _ ih => exact rel_symm ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact rel_trans ih₁ ih₂

lemma related_of_red_step
    (hcancel : ∀ a b, Allowed [(a, b), (a, !b)])
    {u v : Word α} (h : FreeGroup.Red.Step u v) : Related Allowed u v := by
  cases h with
  | @not pre post a b =>
    simpa using Relation.EqvGen.rel _ _ (Delete.block pre [(a, b), (a, !b)] post (hcancel a b))

lemma related_of_red
    (hcancel : ∀ a b, Allowed [(a, b), (a, !b)])
    {u v : Word α} (h : FreeGroup.Red u v) : Related Allowed u v := by
  induction h with
  | refl => exact .refl _
  | tail h hstep ih => exact rel_trans ih (related_of_red_step hcancel hstep)

lemma related_of_mk_eq
    (hcancel : ∀ a b, Allowed [(a, b), (a, !b)])
    {u v : Word α} (h : FreeGroup.mk u = FreeGroup.mk v) : Related Allowed u v := by
  obtain ⟨w, huw, hvw⟩ := FreeGroup.Red.exact.mp h
  exact rel_trans (related_of_red hcancel huw) (rel_symm (related_of_red hcancel hvw))

lemma related_append_null {u v : Word α} (hu : Related Allowed u [])
    (hv : Related Allowed v []) : Related Allowed (u ++ v) [] := by
  exact rel_trans (hu.append_right v) (by simpa using hv)

/-- Words reducible to the empty word form a subgroup of the free group. -/
def nullSubgroup (Allowed : Word α → Prop)
    (hinv : ∀ w, Allowed w → Allowed (FreeGroup.invRev w)) : Subgroup (FreeGroup α) where
  carrier g := ∃ w : Word α, FreeGroup.mk w = g ∧ Related Allowed w []
  one_mem' := ⟨[], rfl, .refl _⟩
  mul_mem' := by
    rintro _ _ ⟨u, rfl, hu⟩ ⟨v, rfl, hv⟩
    exact ⟨u ++ v, FreeGroup.mul_mk.symm, related_append_null hu hv⟩
  inv_mem' := by
    rintro _ ⟨w, rfl, hw⟩
    exact ⟨FreeGroup.invRev w, FreeGroup.inv_mk.symm, by simpa using hw.inv hinv⟩

lemma nullSubgroup_normal
    (hinv : ∀ w, Allowed w → Allowed (FreeGroup.invRev w))
    (hcancel : ∀ a b, Allowed [(a, b), (a, !b)]) :
    (nullSubgroup Allowed hinv).Normal := by
  constructor
  rintro g ⟨w, rfl, hw⟩ u
  induction u using Quot.inductionOn with
  | h v =>
    change ∃ z, FreeGroup.mk z = FreeGroup.mk v * FreeGroup.mk w * (FreeGroup.mk v)⁻¹ ∧ _
    refine ⟨v ++ w ++ FreeGroup.invRev v, ?_, ?_⟩
    · rw [← FreeGroup.mul_mk, ← FreeGroup.mul_mk, ← FreeGroup.inv_mk]
    · have h₁ := (hw.append_left v).append_right (FreeGroup.invRev v)
      simp only [List.append_nil] at h₁
      apply rel_trans h₁
      apply related_of_mk_eq hcancel
      rw [← FreeGroup.mul_mk, ← FreeGroup.inv_mk]
      simp only [mul_inv_cancel, ← FreeGroup.one_eq_mk]

/-- Equality with the identity in the actual presentation gives a finite
sequence of contiguous relator insertions/deletions, with no assumed diagrams. -/
theorem of_presented_eq_one (rels : Set (FreeGroup α))
    (hinv : ∀ w, Allowed w → Allowed (FreeGroup.invRev w))
    (hcancel : ∀ a b, Allowed [(a, b), (a, !b)])
    (hrels : ∀ g ∈ rels, ∃ w : Word α, FreeGroup.mk w = g ∧ Allowed w)
    (w : Word α) (hw : PresentedGroup.mk rels (FreeGroup.mk w) = 1) :
    Related Allowed w [] := by
  let H := nullSubgroup Allowed hinv
  let : H.Normal := nullSubgroup_normal hinv hcancel
  have hle : Subgroup.normalClosure rels ≤ H := by
    apply Subgroup.normalClosure_le_normal
    intro g hg
    obtain ⟨v, hv, hA⟩ := hrels g hg
    refine ⟨v, hv, ?_⟩
    simpa using Relation.EqvGen.rel _ _ (Delete.block [] v [] hA)
  obtain ⟨v, hv, hnull⟩ := hle (PresentedGroup.mk_eq_one_iff.mp hw)
  exact rel_trans (related_of_mk_eq hcancel hv.symm) hnull

end KaplanskyCounterexample.WordReduction

end

end OAI
end
/- CHECKPOINT: OAI.RingTheory.DirectFiniteness.WordReduction -/

/- BEGIN PINNED MODULE OAI.RingTheory.DirectFiniteness.GluedGroup -/
section

namespace OAI

universe u_1 u_2

noncomputable section
open scoped Classical
open scoped BigOperators
open Equiv Equiv.Perm
namespace KaplanskyCounterexample.GluedGroup

variable {V : Type u_1} {F : Type u_2} (Inc : F → Finset V) (ℓ : ℕ)

abbrev Generator := F × {c : ZMod ℓ // c ≠ 0}

/-- Generators belonging to a prescribed local point group. -/
abbrev LocalGenerator (v : V) := {g : Generator (F := F) ℓ // v ∈ Inc g.1}

abbrev PointGroup := Multiplicative (Fin 2 → ZMod ℓ)

variable (incMap : ∀ v : V, {f : F // v ∈ Inc f} → (ZMod ℓ →+ (Fin 2 → ZMod ℓ)))

def localEvaluation (v : V) : FreeGroup (LocalGenerator Inc ℓ v) →* PointGroup ℓ :=
  FreeGroup.lift fun g => Multiplicative.ofAdd
    (incMap v ⟨g.val.1, g.property⟩ g.val.2.val)

def includeLocal (v : V) : FreeGroup (LocalGenerator Inc ℓ v) →*
    FreeGroup (Generator (F := F) ℓ) := FreeGroup.map Subtype.val

def relators : Set (FreeGroup (Generator (F := F) ℓ)) :=
  {w | ∃ v : V, ∃ r : FreeGroup (LocalGenerator Inc ℓ v),
    localEvaluation Inc ℓ incMap v r = 1 ∧ includeLocal Inc ℓ v r = w}

abbrev N := PresentedGroup (relators Inc ℓ incMap)

def fromLocal (v : V) : FreeGroup (LocalGenerator Inc ℓ v) →* N Inc ℓ incMap :=
  (PresentedGroup.mk (relators Inc ℓ incMap)).comp (includeLocal Inc ℓ v)

lemma local_kernel_le (v : V) : (localEvaluation Inc ℓ incMap v).ker ≤
    (fromLocal Inc ℓ incMap v).ker := by
  intro r hr
  exact PresentedGroup.one_of_mem ⟨v, r, hr, rfl⟩

/-- The direction partition covers every nonzero element of each point group. -/
def CoversPoints : Prop := ∀ (v : V) (a : Fin 2 → ZMod ℓ), a ≠ 0 →
  ∃ (f : F) (hf : v ∈ Inc f) (c : ZMod ℓ), c ≠ 0 ∧ incMap v ⟨f, hf⟩ c = a

lemma localEvaluation_surjective (hc : CoversPoints Inc ℓ incMap) (v : V) :
    Function.Surjective (localEvaluation Inc ℓ incMap v) := by
  intro a
  by_cases ha : a.toAdd = 0
  · refine ⟨1, ?_⟩
    simpa using congrArg Multiplicative.ofAdd ha.symm
  · obtain ⟨f, hf, c, hc, hca⟩ := hc v a.toAdd ha
    refine ⟨FreeGroup.of ⟨(f, ⟨c, hc⟩), hf⟩, ?_⟩
    simpa [localEvaluation] using congrArg Multiplicative.ofAdd hca

def theta (hc : CoversPoints Inc ℓ incMap) (v : V) : PointGroup ℓ →* N Inc ℓ incMap :=
  (localEvaluation Inc ℓ incMap v).liftOfSurjective
    (localEvaluation_surjective Inc ℓ incMap hc v)
    ⟨fromLocal Inc ℓ incMap v, local_kernel_le Inc ℓ incMap v⟩

lemma theta_localEvaluation (hc : CoversPoints Inc ℓ incMap) (v : V)
    (w : FreeGroup (LocalGenerator Inc ℓ v)) :
    theta Inc ℓ incMap hc v (localEvaluation Inc ℓ incMap v w) =
      fromLocal Inc ℓ incMap v w := by
  simp [theta]

lemma theta_generator (hc : CoversPoints Inc ℓ incMap) (v : V)
    (f : F) (hf : v ∈ Inc f) (c : ZMod ℓ) (hc0 : c ≠ 0) :
    theta Inc ℓ incMap hc v (Multiplicative.ofAdd (incMap v ⟨f, hf⟩ c)) =
      PresentedGroup.of (rels := relators Inc ℓ incMap) (f, ⟨c, hc0⟩) := by
  have h := theta_localEvaluation Inc ℓ incMap hc v (FreeGroup.of ⟨(f, ⟨c, hc0⟩), hf⟩)
  simpa [localEvaluation, fromLocal, includeLocal, PresentedGroup.of] using h

instance [Finite F] [NeZero ℓ] : Group.FG (N Inc ℓ incMap) := by
  exact Group.fg_of_surjective (PresentedGroup.mk_surjective (relators Inc ℓ incMap))

def EmbeddingClaim (hc : CoversPoints Inc ℓ incMap) : Prop :=
  ∀ v : V, Function.Injective (theta Inc ℓ incMap hc v)

end KaplanskyCounterexample.GluedGroup

end

end OAI
end
/- CHECKPOINT: OAI.RingTheory.DirectFiniteness.GluedGroup -/

/- BEGIN PINNED MODULE OAI.RingTheory.DirectFiniteness.DiagramReduction -/
section

namespace OAI

noncomputable section
open scoped Classical
open scoped BigOperators
open Equiv Equiv.Perm
namespace KaplanskyCounterexample.Planar
variable {V F A B X : Type} [AddCommGroup A] [AddCommGroup B]
variable {Inc : V → F → Prop} {ι : V → F → (A →+ B)} {f₀ : F}

/-- Insertions and deletions preserve the existence of the anchored lifetime drawing. -/
theorem OpenDiagram.related_iff (token : X × Bool → F × A)
    (Allowed : List (X × Bool) → Prop)
    (hA : ∀ r, Allowed r → ∃ v, (∀ t ∈ r.map token, Inc v t.1) ∧
      ((r.map token).map (fun t => ι v t.1 t.2)).sum = 0)
    {u w : List (X × Bool)} (h : WordReduction.Related Allowed u w) :
    Nonempty (OpenDiagram Inc ι f₀ (u.map token)) ↔
      Nonempty (OpenDiagram Inc ι f₀ (w.map token)) := by
  induction h with
  | rel u w h =>
    cases h with
    | block pre r post hr =>
      obtain ⟨v, hi, hs⟩ := hA r hr
      simp only [List.map_append]
      constructor
      · rintro ⟨D⟩
        exact D.deleteWordBlock _ _ _ v hi hs
      · rintro ⟨D⟩
        exact D.insertWordBlock _ _ _ v hi hs
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

end KaplanskyCounterexample.Planar

end

end OAI
end
/- CHECKPOINT: OAI.RingTheory.DirectFiniteness.DiagramReduction -/

/- BEGIN PINNED MODULE OAI.RingTheory.DirectFiniteness.GluedWords -/
section

namespace OAI

noncomputable section
open scoped Classical
open scoped BigOperators
open Equiv Equiv.Perm
namespace KaplanskyCounterexample.GluedGroup
variable {V F : Type} (Inc : F → Finset V) (ℓ : ℕ)
variable (incMap : ∀ v : V, {f : F // v ∈ Inc f} → (ZMod ℓ →+ (Fin 2 → ZMod ℓ)))

def totalMap (v : V) (f : F) : ZMod ℓ →+ (Fin 2 → ZMod ℓ) :=
  if h : v ∈ Inc f then incMap v ⟨f, h⟩ else 0

@[simp] lemma totalMap_of_mem (v : V) (f : F) (h : v ∈ Inc f) :
    totalMap Inc ℓ incMap v f = incMap v ⟨f, h⟩ := dite_eq_left h

def signedToken (s : Generator (F := F) ℓ × Bool) : F × ZMod ℓ :=
  (s.1.1, if s.2 then s.1.2.val else -s.1.2.val)

def Allowed (w : List (Generator (F := F) ℓ × Bool)) : Prop :=
  ∃ v : V, (∀ t ∈ w.map (signedToken ℓ), v ∈ Inc t.1) ∧
    ((w.map (signedToken ℓ)).map (fun t => totalMap Inc ℓ incMap v t.1 t.2)).sum = 0

lemma signedToken_inv (s : Generator (F := F) ℓ × Bool) :
    signedToken ℓ (s.1, !s.2) = ((signedToken ℓ s).1, -(signedToken ℓ s).2) := by
  rcases s with ⟨s, b⟩
  cases b <;> simp [signedToken]

lemma allowed_inv (w : List (Generator (F := F) ℓ × Bool))
    (h : Allowed Inc ℓ incMap w) : Allowed Inc ℓ incMap (FreeGroup.invRev w) := by
  obtain ⟨v, hi, hs⟩ := h
  refine ⟨v, ?_, ?_⟩
  · intro t ht
    simp only [FreeGroup.invRev, List.map_reverse, List.map_map, List.mem_reverse,
      List.mem_map] at ht
    obtain ⟨s, hs', rfl⟩ := ht
    change v ∈ Inc (signedToken ℓ (s.1, !s.2)).1
    rw [signedToken_inv]
    exact hi (signedToken ℓ s) (List.mem_map_of_mem hs')
  · let weight := fun token : Generator (F := F) ℓ × Bool =>
      totalMap Inc ℓ incMap v (signedToken ℓ token).1 (signedToken ℓ token).2
    have inverse_weight (token : Generator (F := F) ℓ × Bool) :
        weight (token.1, !token.2) = -weight token := by
      dsimp only [weight]
      rw [signedToken_inv]
      exact map_neg _ _
    have weights : (FreeGroup.invRev w).map weight =
        ((w.map weight).map Neg.neg).reverse := by
      rw [FreeGroup.invRev, List.map_reverse, List.map_map, List.map_map]
      exact congrArg List.reverse (List.map_congr_left fun token _ => inverse_weight token)
    have total : (w.map weight).sum = 0 := by
      rw [List.map_map] at hs
      exact hs
    rw [List.map_map]
    change ((FreeGroup.invRev w).map weight).sum = 0
    rw [weights, List.sum_reverse, ← List.sum_neg, total, neg_zero]

lemma allowed_cancel (hInc : ∀ f, (Inc f).Nonempty)
    (g : Generator (F := F) ℓ) (b : Bool) :
    Allowed Inc ℓ incMap [(g, b), (g, !b)] := by
  obtain ⟨v, hv⟩ := hInc g.1
  refine ⟨v, ?_, ?_⟩
  · intro t ht
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl <;> exact hv
  · cases b <;> simp [signedToken]

end KaplanskyCounterexample.GluedGroup

end

end OAI
end
/- CHECKPOINT: OAI.RingTheory.DirectFiniteness.GluedWords -/

/- BEGIN PINNED MODULE OAI.RingTheory.DirectFiniteness.GroupEmbedding -/
section

namespace OAI

noncomputable section
open scoped Classical
open scoped BigOperators
open Equiv Equiv.Perm
namespace KaplanskyCounterexample.GluedGroup
variable {V F : Type} (Inc : F → Finset V) (ℓ : ℕ)
variable (incMap : ∀ v : V, {f : F // v ∈ Inc f} → (ZMod ℓ →+ (Fin 2 → ZMod ℓ)))

lemma localEvaluation_word (v : V) (w : List (LocalGenerator Inc ℓ v × Bool)) :
    (localEvaluation Inc ℓ incMap v (FreeGroup.mk w)).toAdd =
      ((w.map (fun s => (s.1.val, s.2))).map (fun s =>
        totalMap Inc ℓ incMap v (signedToken ℓ s).1 (signedToken ℓ s).2)).sum := by
  rw [localEvaluation, FreeGroup.lift_mk, toAdd_list_sum,
    List.map_map, List.map_map]
  congr 1
  apply List.map_congr_left
  intro s _
  rcases s with ⟨s, b⟩
  cases b <;> simp [signedToken, totalMap_of_mem, s.property]

lemma relators_allowed (g : FreeGroup (Generator (F := F) ℓ))
    (hg : g ∈ relators Inc ℓ incMap) :
    ∃ w, FreeGroup.mk w = g ∧ Allowed Inc ℓ incMap w := by
  obtain ⟨v, r, he, rfl⟩ := hg
  induction r using Quot.inductionOn with
  | h w =>
    refine ⟨w.map (fun s => (s.1.val, s.2)), rfl, v, ?_, ?_⟩
    · intro t ht
      simp only [List.map_map, List.mem_map] at ht
      obtain ⟨s, _, rfl⟩ := ht
      exact s.1.property
    · rw [List.map_map]
      have hh := congrArg Multiplicative.toAdd he
      change (localEvaluation Inc ℓ incMap v (FreeGroup.mk w)).toAdd = 0 at hh
      rw [localEvaluation_word] at hh
      exact hh

/-- No nonzero line generator collapses in the actual all-word presentation. -/
theorem generator_ne_one (hInc : ∀ f, (Inc f).Nonempty)
    (hinj : ∀ v f, v ∈ Inc f → Function.Injective (totalMap Inc ℓ incMap v f))
    (hind : ∀ v f g, v ∈ Inc f → v ∈ Inc g → f ≠ g →
      ∀ a b, totalMap Inc ℓ incMap v f a + totalMap Inc ℓ incMap v g b = 0 → a = 0)
    (hgirth : 12 ≤ (Planar.incidenceGraph (fun v f => v ∈ Inc f)).egirth)
    (g : Generator (F := F) ℓ) :
    PresentedGroup.of (rels := relators Inc ℓ incMap) g ≠ 1 := by
  intro he
  have h : WordReduction.Related (Allowed Inc ℓ incMap) [(g, true)] [] :=
    WordReduction.of_presented_eq_one (relators Inc ℓ incMap)
      (allowed_inv Inc ℓ incMap) (allowed_cancel Inc ℓ incMap hInc)
      (relators_allowed Inc ℓ incMap) [(g, true)] he
  have hi : Nonempty (Planar.OpenDiagram (fun v f => v ∈ Inc f)
      (totalMap Inc ℓ incMap) g.1 ([(g, true)].map (signedToken ℓ))) := by
    exact ⟨Planar.OpenDiagram.initial (fun v f => v ∈ Inc f) (totalMap Inc ℓ incMap)
      g.1 g.2.val g.2.property⟩
  have hf := (Planar.OpenDiagram.related_iff (Inc := fun v f => v ∈ Inc f)
    (ι := totalMap Inc ℓ incMap) (f₀ := g.1) (signedToken ℓ)
    (Allowed Inc ℓ incMap) (fun _ h => h) h).mp hi
  obtain ⟨D⟩ := hf
  obtain ⟨v, hv⟩ := hInc g.1
  exact D.not_empty g.1 v hv hinj hind hgirth

theorem theta_injective (hc : CoversPoints Inc ℓ incMap)
    (hInc : ∀ f, (Inc f).Nonempty)
    (hinj : ∀ v f, v ∈ Inc f → Function.Injective (totalMap Inc ℓ incMap v f))
    (hind : ∀ v f g, v ∈ Inc f → v ∈ Inc g → f ≠ g →
      ∀ a b, totalMap Inc ℓ incMap v f a + totalMap Inc ℓ incMap v g b = 0 → a = 0)
    (hgirth : 12 ≤ (Planar.incidenceGraph (fun v f => v ∈ Inc f)).egirth)
    (v : V) : Function.Injective (theta Inc ℓ incMap hc v) := by
  apply (theta Inc ℓ incMap hc v).ker_eq_bot_iff.mp
  apply bot_unique
  intro a ha
  change a = 1
  change theta Inc ℓ incMap hc v a = 1 at ha
  by_contra he
  have ha0 : a.toAdd ≠ 0 := by
    exact fun hh => he (by simpa only [ofAdd_toAdd, ofAdd_zero] using congrArg Multiplicative.ofAdd hh)
  obtain ⟨f, hf, c, hc0, hca⟩ := hc v a.toAdd ha0
  have ht := theta_generator Inc ℓ incMap hc v f hf c hc0
  have hv : Multiplicative.ofAdd (incMap v ⟨f, hf⟩ c) = a := congrArg Multiplicative.ofAdd hca
  rw [hv, ha] at ht
  exact generator_ne_one Inc ℓ incMap hInc hinj hind hgirth (f, ⟨c, hc0⟩) ht.symm

end KaplanskyCounterexample.GluedGroup
end

end OAI
end
/- CHECKPOINT: OAI.RingTheory.DirectFiniteness.GroupEmbedding -/

/- BEGIN PINNED MODULE OAI.RingTheory.DirectFiniteness.IncidenceCycles -/
section

namespace OAI

universe u_1 u_2

noncomputable section
open scoped Classical
namespace KaplanskyCounterexample.Planar
variable {V : Type u_1} {F : Type u_2} (Inc : V → F → Prop)

def incidenceColoring : (incidenceGraph Inc).Coloring Bool :=
  SimpleGraph.Coloring.mk Sum.isLeft (by
    intro x y h
    cases x <;> cases y <;> simp_all [incidenceGraph])

lemma incidence_walk_even {u : V ⊕ F} (w : (incidenceGraph Inc).Walk u u) : Even w.length := by
  exact ((incidenceColoring Inc).even_length_iff_congr w).mpr Iff.rfl

lemma getVert_even_left {v : V} {z : V ⊕ F} (w : (incidenceGraph Inc).Walk (.inl v) z)
    (i : ℕ) (hi : 2*i ≤ w.length) : ∃ x : V, w.getVert (2*i)=.inl x := by
  have he : Even (w.take (2*i)).length := by rw [SimpleGraph.Walk.take_length,inf_eq_left.mpr hi]; exact even_two_mul i
  have hc := ((incidenceColoring Inc).even_length_iff_congr (w.take (2*i))).mp he
  cases hx : w.getVert (2*i) with
  | inl x => exact ⟨x,rfl⟩
  | inr f =>
    change (true = true ↔ Sum.isLeft (w.getVert (2*i)) = true) at hc
    rw [hx] at hc
    exact False.elim (Bool.noConfusion (hc.mp rfl))

lemma getVert_odd_right {v : V} {z : V ⊕ F} (w : (incidenceGraph Inc).Walk (.inl v) z)
    (i : ℕ) (hi : 2*i+1 ≤ w.length) : ∃ f : F, w.getVert (2*i+1)=.inr f := by
  obtain ⟨x,hx⟩ := getVert_even_left Inc w i (by omega)
  have ha := w.adj_getVert_succ (by omega : 2*i < w.length)
  rw [hx] at ha
  cases hf : w.getVert (2*i+1) with
  | inl y =>
    rw [hf] at ha
    exact False.elim ha
  | inr f => exact ⟨f,rfl⟩

/-- A cycle based at a point yields its literal cyclic list of point and
line vertices, without repeated vertices on either side. -/
lemma cycle_polygon_left {v : V} (w : (incidenceGraph Inc).Walk (.inl v) (.inl v))
    (hw : w.IsCycle) {k : ℕ} (hk : w.length=2*k) :
    ∃ (point : Fin k → V) (line : Fin k → F), Function.Injective point ∧ Function.Injective line ∧
      (∀ i, Inc (point i) (line i)) ∧ (∀ i, Inc (point (finRotate k i)) (line i)) := by
  have hkp : 0 < k := by have := hw.three_le_length; omega
  have hp (i : Fin k) := getVert_even_left Inc w i.val (by omega)
  have hl (i : Fin k) := getVert_odd_right Inc w i.val (by omega)
  let point (i : Fin k) := (hp i).choose
  let line (i : Fin k) := (hl i).choose
  have hpoint (i : Fin k) : w.getVert (2*i.val)=.inl (point i) := (hp i).choose_spec
  have hline (i : Fin k) : w.getVert (2*i.val+1)=.inr (line i) := (hl i).choose_spec
  have hnext (i : Fin k) : w.getVert (2*i.val+2)=.inl (point (finRotate k i)) := by
    have hk2 : 2 ≤ k := by have := hw.three_le_length; omega
    by_cases hi : i.val+1 < k
    · have hh : (finRotate k i).val=i.val+1 := by
        rw [finRotate_apply]
        exact Fin.val_add_one_of_lt' hi
      rw [show 2*i.val+2=2*(finRotate k i).val by omega]
      exact hpoint _
    · have hi' : i.val=k-1 := by omega
      have hrot : finRotate k i=⟨0,hkp⟩ := by
        apply Fin.ext
        rw [finRotate_apply,Fin.val_add]
        simp [hi',Nat.sub_add_cancel (by omega : 1 ≤ k)]
      rw [show 2*i.val+2=w.length by omega,SimpleGraph.Walk.getVert_length,hrot]
      simpa using (hpoint ⟨0,hkp⟩)
  refine ⟨point,line,?_,?_,?_,?_⟩
  · intro i j hij
    apply Fin.ext
    have he := hw.getVert_injOn' (show 2*i.val ≤ w.length-1 by omega)
      (show 2*j.val ≤ w.length-1 by omega) ((hpoint i).trans ((congrArg Sum.inl hij).trans (hpoint j).symm))
    omega
  · intro i j hij
    apply Fin.ext
    have he := hw.getVert_injOn' (show 2*i.val+1 ≤ w.length-1 by omega)
      (show 2*j.val+1 ≤ w.length-1 by omega) ((hline i).trans ((congrArg Sum.inr hij).trans (hline j).symm))
    omega
  · intro i
    have ha := w.adj_getVert_succ (by omega : 2*i.val < w.length)
    rw [hpoint,hline] at ha
    exact ha
  · intro i
    have ha := w.adj_getVert_succ (by omega : 2*i.val+1 < w.length)
    rw [hline,show 2*i.val+1+1=2*i.val+2 by omega,hnext] at ha
    exact ha

lemma cycle_polygon {z : V ⊕ F} (w : (incidenceGraph Inc).Walk z z) (hw : w.IsCycle) :
    ∃ k, w.length=2*k ∧ 2 ≤ k ∧ ∃ (point : Fin k → V) (line : Fin k → F),
      Function.Injective point ∧ Function.Injective line ∧
      (∀ i, Inc (point i) (line i)) ∧ (∀ i, Inc (point (finRotate k i)) (line i)) := by
  obtain ⟨k,hk⟩ := incidence_walk_even Inc w
  have hk' : w.length=2*k := by omega
  refine ⟨k,hk',by have := hw.three_le_length; omega,?_⟩
  cases z with
  | inl v => exact cycle_polygon_left Inc w hw hk'
  | inr f =>
    have ha := w.adj_getVert_succ (by have := hw.three_le_length; omega : 0 < w.length)
    simp only [SimpleGraph.Walk.getVert_zero,zero_add] at ha
    cases hz : w.getVert 1 with
    | inr g =>
      rw [hz] at ha
      exact False.elim ha
    | inl v =>
      have hm : (.inl v : V ⊕ F) ∈ w.support := hz ▸ w.getVert_mem_support 1
      exact cycle_polygon_left Inc (w.rotate (.inl v) hm) (hw.rotate hm)
        ((w.length_rotate _ _).trans hk')

/-- A convenient girth criterion phrased in the actual incidence lists. -/
lemma incidence_girth_of_no_short_polygon
    (h : ∀ k, 2 ≤ k → k ≤ 5 → ∀ (point : Fin k → V) (line : Fin k → F),
      Function.Injective point → Function.Injective line →
      (∀ i, Inc (point i) (line i)) → (∀ i, Inc (point (finRotate k i)) (line i)) → False) :
    12 ≤ (incidenceGraph Inc).egirth := by
  apply SimpleGraph.le_egirth.mpr
  intro z w hw
  obtain ⟨k,hk,hk2,point,line,hp,hl,hinc,hnext⟩ := cycle_polygon Inc w hw
  have hn : 6 ≤ k := by
    by_contra hh
    exact h k hk2 (by omega) point line hp hl hinc hnext
  exact_mod_cast (show 12 ≤ w.length by omega)

end KaplanskyCounterexample.Planar
end

end OAI
end
/- CHECKPOINT: OAI.RingTheory.DirectFiniteness.IncidenceCycles -/

/- BEGIN PINNED MODULE OAI.RingTheory.DirectFiniteness.TradeGirth -/
section

namespace OAI

noncomputable section
open scoped Classical
namespace KaplanskyCounterexample.FiniteGeometry
variable {Q A R E : Type} [Field Q] [AddCommGroup A] [Module Q A]
  [AddCommGroup E] [Module Q E] [Fintype A] [Fintype Q]

lemma finRotate_ne_self_large {k : ℕ} (hk : 2 ≤ k) (i : Fin k) : finRotate k i ≠ i := by
  let : NeZero k := ⟨by omega⟩
  intro he
  have hval := congrArg Fin.val he
  rw [finRotate_apply,Fin.val_add] at hval
  have hone : (1 : Fin k).val=1 := by
    change 1 % k=1
    exact Nat.mod_eq_of_lt (by omega)
  rw [hone] at hval
  by_cases hi : i.val+1 < k
  · rw [Nat.mod_eq_of_lt hi] at hval
    omega
  · have hh : i.val+1=k := by omega
    rw [hh,Nat.mod_self] at hval
    omega

namespace DirectionFrame
variable (F : DirectionFrame Q A R E) (S O : Finset A)
  (P : SlabVariable F → Plane Q E) (T : F.Preliminary O P)

omit [Fintype Q] [Fintype A] in
lemma label_spaces_disjoint {l l' : (R × Q) ⊕ R} (hne : l ≠ l') :
    Disjoint (Sum.elim F.U F.exceptional l) (Sum.elim F.U F.exceptional l') := by
  cases l with
  | inl j => cases l' with
    | inl j' => exact F.U_disjoint (fun h => hne (congrArg Sum.inl h))
    | inr r => exact F.U_exceptional_disjoint j r
  | inr r => cases l' with
    | inl j => exact (F.U_exceptional_disjoint j r).symm
    | inr r' => exact F.exceptional_disjoint (fun h => hne (congrArg Sum.inr h))

lemma no_short_trade_polygon
    (hO : HoleEvents.GoodHoles S F.W F.U (fun r t => F.exc r t) O)
    (hP : F.SuccessfulSlabs O P)
    {k : ℕ} (hk2 : 2 ≤ k) (hk5 : k ≤ 5)
    (point : Fin k → A) (line : Fin k → F.TradeIndex O P T)
    (hpoint : Function.Injective point) (hline : Function.Injective line)
    (hx : ∀ i, point i ∈ F.tradeLine O P T (line i))
    (hy : ∀ i, point (finRotate k i) ∈ F.tradeLine O P T (line i)) : False := by
  have hne (i : Fin k) : point (finRotate k i) ≠ point i :=
    fun he => finRotate_ne_self_large hk2 i (hpoint he)
  have hadj (i : Fin k) : F.tradeLabel O P T (line i) ≠ F.tradeLabel O P T (line (finRotate k i)) := by
    intro he
    have hi := hline (F.same_label_eq S O P T hO he (hy i) (hx (finRotate k i)))
    exact finRotate_ne_self_large hk2 i hi.symm
  by_cases hk : k=2
  · subst k
    have hm0 : point 1-point 0 ∈ Sum.elim F.U F.exceptional (F.tradeLabel O P T (line 0)) :=
      F.tradeLine_step_mem O P T (line 0) (hx 0) (hy 0)
    have hm1 : point 1-point 0 ∈ Sum.elim F.U F.exceptional (F.tradeLabel O P T (line 1)) :=
      F.tradeLine_step_mem O P T (line 1) (hy 1) (hx 1)
    exact hne 0 (sub_eq_zero.mp (Submodule.disjoint_def.mp (F.label_spaces_disjoint (hadj 0)) _ hm0 hm1))
  have hk3 : 3 ≤ k := by omega
  by_cases hg : ∃ i j, F.tradeLabel O P T (line i)=.inl j
  · exact F.no_generic_trade_polygon O P T hP hk3 hk5 point line hne hadj hx hy hg
  have hn (i : Fin k) : ∃ t : NewIndex (Q := Q) (R := R) O, line i=.inr t := by
    cases ht : line i with
    | inl t => exact False.elim (hg ⟨i,t.1,by rw [ht]; rfl⟩)
    | inr t => exact ⟨t,rfl⟩
  choose new hnew using hn
  apply F.no_replacement_polygon S O hO hk3 hk5 point new hne
  · intro i he
    apply hadj i
    rw [hnew,hnew]
    exact congrArg Sum.inr he
  · intro i
    simpa only [hnew,tradeLine] using hx i
  · intro i
    simpa only [hnew,tradeLine] using hy i

lemma trade_incidence_girth
    (hO : HoleEvents.GoodHoles S F.W F.U (fun r t => F.exc r t) O)
    (hP : F.SuccessfulSlabs O P) :
    12 ≤ (Planar.incidenceGraph
      (fun (x : {x : A // x ∉ O}) (i : F.TradeIndex O P T) => x.val ∈ F.tradeLine O P T i)).egirth := by
  apply Planar.incidence_girth_of_no_short_polygon
  intro k hk2 hk5 point line hp hl hx hy
  exact F.no_short_trade_polygon S O P T hO hP hk2 hk5 (fun i => (point i).val) line
    (Subtype.val_injective.comp hp) hl hx hy

end DirectionFrame
end KaplanskyCounterexample.FiniteGeometry
end

end OAI
end
/- CHECKPOINT: OAI.RingTheory.DirectFiniteness.TradeGirth -/

/- BEGIN PINNED MODULE OAI.RingTheory.DirectFiniteness.Pairing -/
section

namespace OAI

universe u_1 u_2 u_3 u_4 u_5

noncomputable section
open scoped BigOperators Classical
open MvPolynomial
namespace KaplanskyCounterexample.PolynomialPairing

variable {Q : Type u_1} [Field Q] {n q d : ℕ}

abbrev Simplex (n q d : ℕ) := {k : Fin n → Fin q // ∑ i, (k i).val ≤ d}

def point (a : Fin q ≃ Q) (k : Fin n → Fin q) : Fin n → Q := fun i => a (k i)

def newton (a : Fin q ≃ Q) (k : Fin n → Fin q) : MvPolynomial (Fin n) Q :=
  ∏ i, ∏ u : Fin (k i).val, (X i - C (a ⟨u.val, u.isLt.trans (k i).isLt⟩))

lemma newton_degree (a : Fin q ≃ Q) (k : Fin n → Fin q) :
    (newton a k).totalDegree ≤ ∑ i, (k i).val := by
  apply (totalDegree_finsetProd _ _).trans
  apply Finset.sum_le_sum
  intro i _
  apply (totalDegree_finsetProd _ _).trans
  have h : ∀ u : Fin (k i).val,
      (X i - C (a ⟨u.val, u.isLt.trans (k i).isLt⟩) : MvPolynomial (Fin n) Q).totalDegree ≤ 1 := by
    intro u
    exact (totalDegree_sub_C_le _ _).trans (by simp)
  simpa using Finset.sum_le_sum (fun u (_ : u ∈ Finset.univ) => h u)

lemma newton_eval_zero (a : Fin q ≃ Q) (k j : Fin n → Fin q)
    (h : ¬ k ≤ j) : eval (point a j) (newton a k) = 0 := by
  have hi : ∃ i, (j i).val < (k i).val := by
    simpa only [Pi.le_def, not_forall, not_le, Fin.lt_def] using h
  obtain ⟨i, hi⟩ := hi
  simp only [newton, map_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  apply Finset.prod_eq_zero (Finset.mem_univ (⟨(j i).val, hi⟩ : Fin (k i).val))
  simp [point]

lemma newton_eval_diag_ne_zero (a : Fin q ≃ Q) (k : Fin n → Fin q) :
    eval (point a k) (newton a k) ≠ 0 := by
  simp only [newton, map_prod, map_sub, eval_X, eval_C]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  apply Finset.prod_ne_zero_iff.mpr
  intro u _
  apply sub_ne_zero.mpr
  intro h
  have h' := congrArg Fin.val (a.injective h)
  exact (Nat.ne_of_gt u.isLt) h'

/-- Triangular interpolation on the exact index simplex. The proof provides
its total-degree bound, rather than using unrestricted finite-set interpolation. -/
theorem exists_interpolation (a : Fin q ≃ Q) (values : Simplex n q d → Q) :
    ∃ f : MvPolynomial (Fin n) Q, f.totalDegree ≤ d ∧
      ∀ k : Simplex n q d, eval (point a k.val) f = values k := by
  let I := LinearExtension (Simplex n q d)
  let : Fintype (LinearExtension (Simplex n q d)) := inferInstanceAs (Fintype (Simplex n q d))
  let B : Matrix I I Q := fun j k => eval (point a j.val) (newton a k.val)
  have htri : B.IsLowerTriangular := by
    intro j k hjk
    apply newton_eval_zero
    intro hle
    have hh : (k : I) ≤ j := (toLinearExtension (α := Simplex n q d)).monotone hle
    exact (not_le_of_gt hjk) hh
  have hdet : B.det ≠ 0 := by
    rw [Matrix.det_of_isLowerTriangular B htri]
    exact Finset.prod_ne_zero_iff.mpr (fun k _ => newton_eval_diag_ne_zero a k.val)
  have hunit : IsUnit B := (Matrix.isUnit_iff_isUnit_det B).mpr (isUnit_iff_ne_zero.mpr hdet)
  obtain ⟨c, hc⟩ := (Matrix.mulVec_surjective_iff_isUnit.mpr hunit) values
  refine ⟨∑ k : I, c k • newton a k.val, ?_, ?_⟩
  · apply (totalDegree_finsetSum _ _).trans
    apply Finset.sup_le
    intro k _
    exact (totalDegree_smul_le _ _).trans ((newton_degree a k.val).trans k.property)
  · intro k
    have h := congrFun hc k
    simpa [B, Matrix.mulVec, dotProduct, smul_eq_C_mul, mul_comm] using h

end KaplanskyCounterexample.PolynomialPairing

noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample.PolynomialPairing

variable {Q : Type u_2} {σ : Type u_3} [Field Q]

/-- Restriction to the full parametrized affine line. -/
def lineRestriction (u v : σ → Q) (P : MvPolynomial σ Q) : Polynomial Q :=
  MvPolynomial.eval₂ Polynomial.C (fun i => Polynomial.C (u i) + Polynomial.C (v i) * Polynomial.X) P

lemma lineRestriction_eval (u v : σ → Q) (P : MvPolynomial σ Q) (t : Q) :
    (lineRestriction u v P).eval t = MvPolynomial.eval (fun i => u i + t * v i) P := by
  unfold lineRestriction
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add P R hP hR => simp [hP, hR]
  | mul_X P i hP => simp [hP, mul_comm t]

lemma lineRestriction_degree (u v : σ → Q) (P : MvPolynomial σ Q) :
    (lineRestriction u v P).natDegree ≤ P.totalDegree := by
  rw [lineRestriction, MvPolynomial.eval₂_eq]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro d hd
  apply (Polynomial.natDegree_mul_le).trans
  simp only [Polynomial.natDegree_C, zero_add]
  apply (Polynomial.natDegree_prod_le _ _).trans
  apply le_trans _ (MvPolynomial.le_totalDegree hd)
  change (∑ i ∈ d.support, _) ≤ ∑ i ∈ d.support, d i
  apply Finset.sum_le_sum
  intro i _
  apply (Polynomial.natDegree_pow_le).trans
  have hc : (Polynomial.C (u i) + Polynomial.C (v i) * Polynomial.X).natDegree ≤ 1 := by
    apply (Polynomial.natDegree_add_le _ _).trans
    simp only [Polynomial.natDegree_C, max_le_iff, zero_le, true_and]
    simpa using Polynomial.natDegree_C_mul_X_pow_le (v i) 1
  simpa using Nat.mul_le_mul_left (d i) hc

/-- The exact finite-field power-sum consequence used on every line. -/
lemma sum_polynomial_eval [Fintype Q] (P : Polynomial Q)
    (hP : P.natDegree < Fintype.card Q - 1) : ∑ t : Q, P.eval t = 0 := by
  simp only [Polynomial.eval_eq_sum, Polynomial.sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro k hk
  rw [← Finset.mul_sum]
  have hk' : k < Fintype.card Q - 1 := lt_of_le_of_lt (Polynomial.le_natDegree_of_mem_supp k hk) hP
  rw [FiniteField.sum_pow_lt_card_sub_one Q k hk', mul_zero]

theorem line_sum_zero [Fintype Q] (u v : σ → Q) (P : MvPolynomial σ Q)
    (hP : P.totalDegree < Fintype.card Q - 1) :
    ∑ t : Q, MvPolynomial.eval (fun i => u i + t * v i) P = 0 := by
  simpa only [lineRestriction_eval] using sum_polynomial_eval (lineRestriction u v P)
    (lt_of_le_of_lt (lineRestriction_degree u v P) hP)

/-- Partitioning the entire affine space into coordinate-parallel lines. -/
theorem affine_space_sum_zero [Fintype Q] [Fintype σ] (i : σ) (P : MvPolynomial σ Q)
    (hP : P.totalDegree < Fintype.card Q - 1) :
    ∑ x : σ → Q, MvPolynomial.eval x P = 0 := by
  rw [← (Equiv.funSplitAt i Q).symm.sum_comp (fun x => MvPolynomial.eval x P)]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro x _
  let u : σ → Q := fun j => if h : j = i then 0 else x ⟨j, h⟩
  let v : σ → Q := fun j => if j = i then 1 else 0
  have hparam (t : Q) : (Equiv.funSplitAt i Q).symm (t, x) = fun j => u j + t * v j := by
    funext j
    by_cases h : j = i <;> simp [Equiv.funSplitAt, u, v, h]
  simpa only [hparam] using line_sum_zero u v P hP

end KaplanskyCounterexample.PolynomialPairing

namespace KaplanskyCounterexample.PolynomialPairing

variable {Q : Type u_4} [Field Q] [Fintype Q] {n q : ℕ}

def simplexPoints (a : Fin q ≃ Q) (n d : ℕ) : Finset (Fin n → Q) :=
  Finset.univ.image (fun k : Simplex n q d => point a k.val)

omit [Field Q] [Fintype Q] in
lemma mem_simplexPoints (a : Fin q ≃ Q) {d : ℕ} {x : Fin n → Q} :
    x ∈ simplexPoints a n d ↔ ∃ k : Simplex n q d, point a k.val = x := by
  simp [simplexPoints]

/-- The interpolation choice is constrained by the exact degree cutoff. -/
def holePolynomial (a : Fin q ≃ Q) (d : ℕ) (o : Fin n → Q) :
    MvPolynomial (Fin n) Q :=
  (exists_interpolation a (fun k : Simplex n q d => if point a k.val = o then 1 else 0)).choose

omit [Fintype Q] in
lemma holePolynomial_degree (a : Fin q ≃ Q) (d : ℕ) (o : Fin n → Q) :
    (holePolynomial a d o).totalDegree ≤ d :=
  (exists_interpolation a (fun k : Simplex n q d => if point a k.val = o then 1 else 0)).choose_spec.1

omit [Fintype Q] in
lemma holePolynomial_eval (a : Fin q ≃ Q) (d : ℕ) (o x : Fin n → Q)
    (hx : x ∈ simplexPoints a n d) :
    MvPolynomial.eval x (holePolynomial a d o) = if x = o then 1 else 0 := by
  obtain ⟨k, rfl⟩ := (mem_simplexPoints a).mp hx
  exact (exists_interpolation a (fun k : Simplex n q d => if point a k.val = o then 1 else 0)).choose_spec.2 k

/-- The exact column vector x_v, indexed by the chosen holes. -/
def column (a : Fin q ≃ Q) (d : ℕ) (O : Finset (Fin n → Q)) (v : Fin n → Q) : O → Q :=
  fun o => MvPolynomial.eval v (holePolynomial a d o.val)

def gramColumn (a : Fin q ≃ Q) (d : ℕ) (O : Finset (Fin n → Q)) (v : Fin n → Q) :
    Matrix O O Q := fun o o' => column a d O v o * column a d O v o'

omit [Fintype Q] in
lemma sum_holes_gram (a : Fin q ≃ Q) {d : ℕ} (O : Finset (Fin n → Q))
    (hO : O ⊆ simplexPoints a n d) :
    ∑ v ∈ O, gramColumn a d O v = 1 := by
  ext o o'
  simp only [Matrix.sum_apply, gramColumn, column]
  calc
    _ = ∑ v ∈ O, (if v = o.val then (1 : Q) else 0) *
        (if v = o'.val then (1 : Q) else 0) := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [holePolynomial_eval a d _ _ (hO hv), holePolynomial_eval a d _ _ (hO hv)]
    _ = _ := by
      rw [Finset.sum_eq_single_of_mem o.val o.property]
      · simp only [ite_true, one_mul, Matrix.one_apply]
        congr 1
        exact propext Subtype.val_inj
      · intro v _ hv
        rw [ite_eq_right hv, zero_mul]

omit [Fintype Q] in
lemma gram_degree (a : Fin q ≃ Q) (d : ℕ) (o o' : Fin n → Q) :
    (holePolynomial a d o * holePolynomial a d o').totalDegree ≤ 2 * d := by
  exact (MvPolynomial.totalDegree_mul _ _).trans
    (by simpa [two_mul] using (Nat.add_le_add (holePolynomial_degree a d o)
      (holePolynomial_degree a d o')))

lemma cutoff_degree (q : ℕ) (hq : 2 ≤ q) : 2 * ((q - 2) / 2) < q - 1 := by
  have h := Nat.mul_div_le (q - 2) 2
  omega

/-- All entries of the Gram column sum vanish on the full affine space. -/
lemma sum_all_gram (a : Fin q ≃ Q) (hq : q = Fintype.card Q) (hn : 0 < n)
    (O : Finset (Fin n → Q)) :
    ∑ v : Fin n → Q, gramColumn a ((q - 2) / 2) O v = 0 := by
  ext o o'
  simp only [Matrix.sum_apply, Matrix.zero_apply, gramColumn, column]
  have hq2 : 2 ≤ q := hq ▸ Nat.succ_le_iff.mpr (Fintype.one_lt_card (α := Q))
  convert! (affine_space_sum_zero (⟨0, hn⟩ : Fin n)
    (holePolynomial a ((q - 2) / 2) o.val * holePolynomial a ((q - 2) / 2) o'.val)
    ((gram_degree a _ _ _).trans_lt (hq ▸ cutoff_degree q hq2))) using 1
  simp only [map_mul]
  exact Finset.sum_congr (by ext; simp) (fun _ _ => rfl)

/-- The precise global identity on V, with no characteristic simplification. -/
theorem sum_complement_gram (a : Fin q ≃ Q) (hq : q = Fintype.card Q) (hn : 0 < n)
    (O : Finset (Fin n → Q)) (hO : O ⊆ simplexPoints a n ((q - 2) / 2)) :
    ∑ v ∈ Finset.univ \ O, gramColumn a ((q - 2) / 2) O v = -1 := by
  have h := Finset.sum_sdiff (f := gramColumn a ((q - 2) / 2) O) (Finset.subset_univ O)
  rw [sum_holes_gram a O hO, sum_all_gram a hq hn O] at h
  exact eq_neg_of_add_eq_zero_left h

/-- A full affine line, not a segment or a subset of one. -/
structure AffineLine (Q : Type u_5) [Field Q] (n : ℕ) where
  base : Fin n → Q
  direction : Fin n → Q
  direction_ne_zero : direction ≠ 0

def AffineLine.param (L : AffineLine Q n) (t : Q) : Fin n → Q :=
  fun i => L.base i + t * L.direction i

omit [Fintype Q] in
lemma AffineLine.param_injective (L : AffineLine Q n) : Function.Injective L.param := by
  intro t u h
  have hi : ∃ i, L.direction i ≠ 0 := by
    by_contra! h
    exact L.direction_ne_zero (funext h)
  obtain ⟨i, hi⟩ := hi
  have he := congrFun h i
  exact mul_right_cancel₀ hi (add_left_cancel he)

def AffineLine.points (L : AffineLine Q n) : Finset (Fin n → Q) :=
  Finset.univ.image L.param

lemma AffineLine.card_points (L : AffineLine Q n) : L.points.card = Fintype.card Q := by
  rw [AffineLine.points, Finset.card_image_of_injective _ L.param_injective, Finset.card_univ]

theorem sum_line_gram (a : Fin q ≃ Q) (hq : q = Fintype.card Q)
    (O : Finset (Fin n → Q)) (L : AffineLine Q n) :
    ∑ v ∈ L.points, gramColumn a ((q - 2) / 2) O v = 0 := by
  rw [AffineLine.points, Finset.sum_image (L.param_injective.injOn)]
  ext o o'
  simp only [Matrix.sum_apply, Matrix.zero_apply, gramColumn, column]
  have hq2 : 2 ≤ q := hq ▸ Nat.succ_le_iff.mpr (Fintype.one_lt_card (α := Q))
  convert! (line_sum_zero L.base L.direction
    (holePolynomial a ((q - 2) / 2) o.val * holePolynomial a ((q - 2) / 2) o'.val)
    ((gram_degree a _ _ _).trans_lt (hq ▸ cutoff_degree q hq2))) using 1
  simp only [map_mul]
  apply Finset.sum_congr rfl
  intro t _
  rfl

end KaplanskyCounterexample.PolynomialPairing
end
end

end OAI
end
/- CHECKPOINT: OAI.RingTheory.DirectFiniteness.Pairing -/

/- BEGIN PINNED MODULE OAI.RingTheory.DirectFiniteness.SimplexBound -/
section

namespace OAI

universe u_1

noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample.PolynomialPairing
variable {Q : Type u_1} [Field Q] [Fintype Q] {q n d t : ℕ}

omit [Field Q] [Fintype Q] in
lemma cube_card_le_simplex (a : Fin q ≃ Q) (htq : t ≤ q)
    (hcut : n * (t-1) ≤ d) : t^n ≤ (simplexPoints a n d).card := by
  let f : (Fin n → Fin t) → Simplex n q d := fun x => ⟨fun i =>
    ⟨(x i).val,(x i).isLt.trans_le htq⟩,by
      apply le_trans _ hcut
      calc
        (∑ i : Fin n, (x i).val) ≤ ∑ _i : Fin n, (t-1) := by
          apply Finset.sum_le_sum
          intro i _
          have := (x i).isLt
          omega
        _ = n*(t-1) := by simp⟩
  let g : (Fin n → Fin t) → simplexPoints a n d := fun x =>
    ⟨point a (f x).val,(mem_simplexPoints a).mpr ⟨f x,rfl⟩⟩
  have hg : Function.Injective g := by
    intro x y h
    funext i
    apply Fin.ext
    have hh := a.injective (congrFun (congrArg Subtype.val h) i)
    change (x i).val = (y i).val
    exact congrArg (fun z : Fin q => z.val) hh
  simpa only [Fintype.card_fun,Fintype.card_fin,Fintype.card_coe] using
    Fintype.card_le_of_injective g hg

lemma small_cube_cutoff (hn : 0 < n) (hq : 2*n ≤ q) :
    n * (q/(2*n)-1) ≤ (q-2)/2 ∧ q ≤ 4*n*(q/(2*n)) := by
  have hd : 0 < 2*n := by omega
  have ht : 0 < q/(2*n) := Nat.div_pos hq hd
  have hm := Nat.div_mul_le_self q (2*n)
  have hr := Nat.mod_lt q hd
  have he := Nat.mod_add_div q (2*n)
  have hs := Nat.sub_add_cancel (show 1 ≤ q/(2*n) by omega)
  constructor
  · apply (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mpr
    have hq2 : 2 ≤ q := by omega
    have hsub := Nat.sub_add_cancel hq2
    nlinarith
  · nlinarith

omit [Field Q] [Fintype Q] in
lemma simplex_density_bound (a : Fin q ≃ Q) (hn : 0 < n) (hq : 2*n ≤ q) :
    q^n ≤ (4*n)^n * (simplexPoints a n ((q-2)/2)).card := by
  obtain ⟨hcut,hfloor⟩ := small_cube_cutoff hn hq
  have hc := cube_card_le_simplex a (Nat.div_le_self q (2*n)) hcut
  calc
    q^n ≤ (4*n*(q/(2*n)))^n := Nat.pow_le_pow_left hfloor n
    _ = (4*n)^n * (q/(2*n))^n := mul_pow _ _ _
    _ ≤ (4*n)^n * (simplexPoints a n ((q-2)/2)).card := Nat.mul_le_mul_left _ hc

end KaplanskyCounterexample.PolynomialPairing
end

end OAI
end
/- CHECKPOINT: OAI.RingTheory.DirectFiniteness.SimplexBound -/

/- BEGIN PINNED MODULE OAI.RingTheory.DirectFiniteness.PrescribedIncidence -/
section

namespace OAI

noncomputable section
open scoped Classical
namespace KaplanskyCounterexample.Prescription
open FiniteGeometry PolynomialPairing

structure Successful {Q : Type} [Field Q] [Fintype Q] {q n : ℕ}
    (a : Fin q ≃ Q) (ℓ : ℕ)
    (pair : Finset (Fin n → Q) × Finset (Finset (Fin n → Q))) : Prop where
  holes_subset : pair.1 ⊆ simplexPoints a n ((q-2)/2)
  lower : 2*q^n ≤ pair.1.card*(ℓ+1)^2
  upper : pair.1.card*(ℓ+1)^2 ≤ 7*q^n
  full : ∀ L ∈ pair.2, FullLine (Q := Q) L
  avoid : ∀ L ∈ pair.2, ∀ v ∈ L, v ∉ pair.1
  regular : ∀ v : {v : Fin n → Q // v ∉ pair.1},
    Fintype.card {L : pair.2 // v.val ∈ L.val}=ℓ+1
  girth : 12 ≤ (Planar.incidenceGraph
    (fun (v : {v : Fin n → Q // v ∉ pair.1}) (L : pair.2) => v.val ∈ L.val)).egirth

namespace DirectionFrame
variable {Q A R E : Type} [Field Q] [AddCommGroup A] [Module Q A]
  [AddCommGroup E] [Module Q E] [Fintype A] [Fintype Q]
  (F : FiniteGeometry.DirectionFrame Q A R E) (S O : Finset A)
  (P : SlabVariable F → Plane Q E) (T : F.Preliminary O P)

lemma tradeLine_injective
    (hO : HoleEvents.GoodHoles S F.W F.U (fun r t => F.exc r t) O) :
    Function.Injective (F.tradeLine O P T) := by
  intro i j hij
  obtain ⟨x,hx,y,hy,hxy⟩ := Finset.one_lt_card.mp
    ((F.tradeLine_full O P T i).card ▸ Fintype.one_lt_card (α := Q))
  have hxj : x ∈ F.tradeLine O P T j := hij ▸ hx
  have hyj : y ∈ F.tradeLine O P T j := hij ▸ hy
  have hl : F.tradeLabel O P T i=F.tradeLabel O P T j := by
    by_contra hne
    have hz := Submodule.disjoint_def.mp (F.label_spaces_disjoint hne) (y-x)
      (F.tradeLine_step_mem O P T i hx hy) (F.tradeLine_step_mem O P T j hxj hyj)
    exact hxy (sub_eq_zero.mp hz).symm
  exact F.same_label_eq S O P T hO hl hx hxj

end DirectionFrame

/-- A faithful set of full lines from the successful geometric trade; the
bijection retains degrees and ordinary incidence girth exactly. -/
lemma successful_of_indexed {Q : Type} [Field Q] [Fintype Q] {q n ℓ : ℕ}
    (a : Fin q ≃ Q) (O : Finset (Fin n → Q))
    (hO : O ⊆ simplexPoints a n ((q-2)/2))
    (hlow : 2*q^n ≤ O.card*(ℓ+1)^2) (hhigh : O.card*(ℓ+1)^2 ≤ 7*q^n)
    {I : Type} [Fintype I] (L : I → Finset (Fin n → Q)) (hinj : Function.Injective L)
    (hfull : ∀ i, FullLine (Q := Q) (L i))
    (havoid : ∀ i v, v ∈ L i → v ∉ O)
    (hdeg : ∀ v : {v : Fin n → Q // v ∉ O}, Fintype.card {i : I // v.val ∈ L i}=ℓ+1)
    (hgirth : 12 ≤ (Planar.incidenceGraph
      (fun (v : {v : Fin n → Q // v ∉ O}) (i : I) => v.val ∈ L i)).egirth) :
    ∃ pair, Successful (n := n) a ℓ pair := by
  let lines := Finset.univ.image L
  let f (i : I) : lines := ⟨L i,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j h
      exact hinj (congrArg Subtype.val h)
    · intro l
      obtain ⟨i,_,hi⟩ := Finset.mem_image.mp l.property
      exact ⟨i,Subtype.ext hi⟩
  let e := Equiv.ofBijective f hf
  refine ⟨(O,lines),⟨hO,hlow,hhigh,?_,?_,?_,?_⟩⟩
  · intro l hl
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hl
    exact hfull i
  · intro l hl v hv
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hl
    exact havoid i v hv
  · intro v
    have ec := e.subtypeEquiv (p := fun i => v.val ∈ L i)
      (q := fun l => v.val ∈ l.val) (fun _ => Iff.rfl)
    exact (Fintype.card_congr ec).symm.trans (hdeg v)
  · let g : (Planar.incidenceGraph (fun (v : {v : Fin n → Q // v ∉ O}) (i : I) => v.val ∈ L i)) ≃g
        (Planar.incidenceGraph (fun (v : {v : Fin n → Q // v ∉ O}) (l : lines) => v.val ∈ l.val)) :=
      { toEquiv := Equiv.sumCongr (Equiv.refl _) e
        map_rel_iff' := by intro v w; cases v <;> cases w <;> rfl }
    exact g.egirth_eq ▸ hgirth

/-- Uniformity in every enumeration and realization of F_(2^217), required
by the literal outer search (whose field is the lexicographic quotient). -/
lemma succeeds_217 (Q : Type) [Field Q] [Fintype Q] [CharP Q 2]
    (hq : Fintype.card Q=sourceQ) (a : Fin sourceQ ≃ Q) :
    ∃ pair : Finset (Fin 1200 → Q) × Finset (Finset (Fin 1200 → Q)),
      Successful a sourcePrime pair := by
  let R := Fin (sourceD/sourceQ)
  let E := Fin 119 → Q
  have hRcard : Fintype.card R=sourceD/sourceQ := Fintype.card_fin _
  have hr : Fintype.card R*sourceQ=sourceD := by
    rw [hRcard]
    exact Nat.div_mul_cancel sourceD_q_dvd
  obtain ⟨F⟩ := exists_coordinate_frame Q R (by
    simpa only [R,Fintype.card_fin,hq] using source_frame_size)
  let S := simplexPoints a 1200 ((sourceQ-2)/2)
  have hn : Fintype.card (Fin 1200 → Q)=sourceQ^1200 := by
    simp only [Fintype.card_fun,Fintype.card_fin,hq]
  have hE : Fintype.card E=sourceQ^119 := by
    simp only [E,Fintype.card_fun,Fintype.card_fin,hq]
  have hdensity : Fintype.card (Fin 1200 → Q) ≤ sourceQ^72*S.card := by
    rw [hn]
    have hs := simplex_density_bound (n := 1200) a (by decide) (by have := sourceQ_large; omega)
    rw [show 4*1200=4800 from rfl] at hs
    exact hs.trans (Nat.mul_le_mul_right S.card sourceQ_density)
  obtain ⟨O,hO,hlo,hhi⟩ := F.exists_sized_goodHoles S hq hE
    (sourceQ_large.trans' (by decide)) sourceD_bounds.1 (le_of_eq hr)
    hdensity (by rw [hn]; exact sourceD_square_le)
  have hRbound : Fintype.card R ≤ 2*(Fintype.card Q)^100 := by
    rw [hq,hRcard]
    exact (Nat.div_le_self sourceD sourceQ).trans sourceD_bounds.2
  obtain ⟨P,hP⟩ := F.exists_successfulSlabs_large S O hO (by rw [hq]; exact sourceQ_very_large)
    hRbound (by simp only [Module.finrank_pi,Fintype.card_fin])
  obtain ⟨T⟩ := F.exists_preliminary O P hP
  refine successful_of_indexed a O hO.source ?_ ?_ (F.tradeLine O P T)
    (DirectionFrame.tradeLine_injective F S O P T hO) (F.tradeLine_full O P T)
    (fun i v hv ho => Finset.disjoint_left.mp (F.tradeLine_avoid S O P T hO i) hv ho)
    ?_ (F.trade_incidence_girth S O P T hO hP)
  · simpa only [hn,sourceD] using hlo
  · have hb := hhi.trans (Nat.mul_le_mul_right (Fintype.card (Fin 1200 → Q)) (by decide : 3 ≤ 7))
    simpa only [hn,sourceD] using hb
  · intro v
    have hd := F.trade_degree S O P T hO v.val v.property
    rw [hq,hr] at hd
    simpa only [Fintype.card_eq_nat_card,sourceD] using hd

end KaplanskyCounterexample.Prescription
end

end OAI
end
/- CHECKPOINT: OAI.RingTheory.DirectFiniteness.PrescribedIncidence -/

/- BEGIN PINNED MODULE OAI.RingTheory.DirectFiniteness.PrescribedSearch -/
section

namespace OAI

noncomputable section
open scoped Classical
namespace KaplanskyCounterexample.Prescription

abbrev Affine (h : Input) := Fin (dimension h.val) → Q h
abbrev Pair (h : Input) := Finset (Affine h) × Finset (Finset (Affine h))

/-- Coordinate-lex order, then indicator order for points and lines,
then indicator order for families, finally lexicographic order of the pair.
Discarding the non-full-line candidates does not change relative order. -/
@[instance_reducible] def pairOrder (h : Input) : LinearOrder (Pair h) :=
  letI : LinearOrder (Affine h) := vectorOrder
  letI : LinearOrder (Finset (Affine h)) := subsetOrder _
  letI : LinearOrder (Finset (Finset (Affine h))) := subsetOrder _
  LinearOrder.lift' (toLex : Pair h → Lex (Pair h)) (fun _ _ he => he)

def Test (h : Input) (p : Pair h) : Prop :=
  Successful (enumeration h) (prime h.val) p

def Succeeds (h : ℕ) : Prop := ∃ hh : 2 ≤ h, ∃ p, Test ⟨h,hh⟩ p

lemma succeeds217 : Succeeds 217 := by
  refine ⟨by decide,?_⟩
  let h : Input := ⟨217,by decide⟩
  have hs := succeeds_217 (Q h) (Q_card h) (enumeration h)
  have hn : dimension h.val=1200 := dimension_217
  have hp : prime h.val=FiniteGeometry.sourcePrime := prime_217
  unfold Test
  change ∃ p : Finset (Fin (dimension h.val) → Q h) ×
    Finset (Finset (Fin (dimension h.val) → Q h)), Successful (enumeration h) (prime h.val) p
  rw [hn,hp]
  exact hs

local instance : DecidablePred Succeeds := Classical.decPred _

/-- The exact least successful outer input, not the convenient existence bound 217. -/
def selectedH : ℕ := Nat.find (show ∃ h, Succeeds h from ⟨217,succeeds217⟩)
lemma selectedH_spec : Succeeds selectedH := Nat.find_spec _
lemma selectedH_le (h : ℕ) (hh : Succeeds h) : selectedH ≤ h := Nat.find_min' _ hh
lemma selectedH_ge : 2 ≤ selectedH := selectedH_spec.choose
lemma selectedH_le217 : selectedH ≤ 217 := selectedH_le 217 succeeds217

def selectedInput : Input := ⟨selectedH,selectedH_ge⟩
lemma selectedInput_success : ∃ p, Test selectedInput p := selectedH_spec.choose_spec

/-- The first successful pair in the literal finite lexicographic search. -/
def selectedPair : Pair selectedInput :=
  letI := pairOrder selectedInput
  first (Test selectedInput) selectedInput_success

lemma selectedPair_spec : Test selectedInput selectedPair := by
  let _ := pairOrder selectedInput
  exact first_spec (Test selectedInput) selectedInput_success
lemma selectedPair_minimal (p : Pair selectedInput) (hp : Test selectedInput p) :
    @LE.le _ (pairOrder selectedInput).toLE selectedPair p := by
  let _ := pairOrder selectedInput
  exact first_le (Test selectedInput) selectedInput_success p hp

/-- Formal termination certificate for both the outer loop and its finite inner loop. -/
theorem finite_search_terminates :
    2 ≤ selectedH ∧ selectedH ≤ 217 ∧ Test selectedInput selectedPair ∧
      (∀ h, Succeeds h → selectedH ≤ h) ∧
      (∀ p, Test selectedInput p → @LE.le _ (pairOrder selectedInput).toLE selectedPair p) :=
  ⟨selectedH_ge,selectedH_le217,selectedPair_spec,selectedH_le,selectedPair_minimal⟩

end KaplanskyCounterexample.Prescription
end

end OAI
end
/- CHECKPOINT: OAI.RingTheory.DirectFiniteness.PrescribedSearch -/

/- BEGIN PINNED MODULE OAI.RingTheory.DirectFiniteness.IncidenceDirections -/
section

namespace OAI

universe u_1 u_2 u_3 u_4

noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample.IncidenceDirections
variable {K : Type u_1} [Field K]

def directionMap : Option K → K →ₗ[K] (Fin 2 → K)
  | none =>
    { toFun := fun c => ![0, c]
      map_add' := by intros; ext i; fin_cases i <;> simp
      map_smul' := by intros; ext i; fin_cases i <;> simp }
  | some a =>
    { toFun := fun c => ![c, a * c]
      map_add' := by intros; ext i; fin_cases i <;> simp [mul_add]
      map_smul' := by intros; ext i; fin_cases i <;> simp; ring }

lemma directionMap_injective (d : Option K) : Function.Injective (directionMap d) := by
  cases d with
  | none => intro x y h; simpa [directionMap] using congrFun h 1
  | some a => intro x y h; simpa [directionMap] using congrFun h 0

lemma directionMap_independent {d e : Option K} (hne : d ≠ e) (c b : K)
    (h : directionMap d c + directionMap e b = 0) : c = 0 ∧ b = 0 := by
  have h₀ := congrFun h 0
  have h₁ := congrFun h 1
  cases d <;> cases e <;> simp_all [directionMap]
  rename_i d e
  have hde : d - e ≠ 0 := sub_ne_zero.mpr hne
  have hc : (d - e) * c = 0 := by linear_combination h.2 - e * h.1
  have hz := (mul_eq_zero.mp hc).resolve_left hde
  exact ⟨hz, by simpa [hz] using h.1⟩

lemma directionMap_covers (a : Fin 2 → K) (ha : a ≠ 0) :
    ∃ d : Option K, ∃ c : K, c ≠ 0 ∧ directionMap d c = a := by
  by_cases h₀ : a 0 = 0
  · have h₁ : a 1 ≠ 0 := by
      intro h₁
      apply ha
      ext i
      fin_cases i <;> assumption
    refine ⟨none, a 1, h₁, ?_⟩
    ext i
    fin_cases i <;> simp [directionMap, h₀]
  · refine ⟨some (a 1 / a 0), a 0, h₀, ?_⟩
    ext i
    fin_cases i <;> simp [directionMap, h₀]

/-- Every nonzero vector lies on exactly one of these parametrized lines. -/
def nonzeroEquiv : (Option K × {c : K // c ≠ 0}) ≃ {a : Fin 2 → K // a ≠ 0} :=
  Equiv.ofBijective
    (fun p => ⟨directionMap p.1 p.2.val, fun h =>
      p.2.property ((directionMap_injective p.1) (h.trans (map_zero _).symm))⟩) (by
      constructor
      · rintro ⟨d, c, hc⟩ ⟨e, b, hb⟩ h
        have heq : directionMap d c = directionMap e b := congrArg Subtype.val h
        have hde : d = e := by
          by_contra hne
          apply hc
          exact (directionMap_independent hne c (-b) (by simpa [sub_eq_add_neg] using sub_eq_zero.mpr heq)).1
        subst e
        exact Prod.ext rfl (Subtype.ext (directionMap_injective d heq))
      · rintro ⟨a, ha⟩
        obtain ⟨d, c, hc, hca⟩ := directionMap_covers a ha
        exact ⟨(d, ⟨c, hc⟩), Subtype.ext hca⟩)

@[simp] lemma nonzeroEquiv_apply (d : Option K) (c : {c : K // c ≠ 0}) :
    (nonzeroEquiv (d, c)).val = directionMap d c := rfl

/-- The local subgroup decomposition, before applying a group-ring map. -/
lemma sum_directions [Fintype K] {M : Type u_2} [AddCommGroup M]
    (f : (Fin 2 → K) → M) :
    ∑ a : Fin 2 → K, f a = f 0 + ∑ d : Option K, (∑ c : K, f (directionMap d c) - f 0) := by
  rw [Fintype.sum_eq_add_sum_subtype_ne f 0]
  congr 1
  rw [← Equiv.sum_comp nonzeroEquiv (fun a => f a.val), Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro d _
  rw [Fintype.sum_eq_add_sum_subtype_ne (fun c : K => f (directionMap d c)) 0]
  simp

variable {V : Type u_3} {F : Type u_4} [Fintype F] (Inc : F → Finset V) (ℓ : ℕ) [Fact ℓ.Prime]

/-- At a point, assign the incident lines bijectively to all slopes. -/
def incidenceEquiv (hdeg : ∀ v, Fintype.card {f : F // v ∈ Inc f} = ℓ + 1)
    (v : V) : {f : F // v ∈ Inc f} ≃ Option (ZMod ℓ) :=
  Fintype.equivOfCardEq (by simpa using hdeg v)

def incidenceMap (hdeg : ∀ v, Fintype.card {f : F // v ∈ Inc f} = ℓ + 1)
    (v : V) (f : {f : F // v ∈ Inc f}) : ZMod ℓ →+ (Fin 2 → ZMod ℓ) :=
  (directionMap (incidenceEquiv Inc ℓ hdeg v f)).toAddMonoidHom

lemma incidenceMap_injective (hdeg : ∀ v, Fintype.card {f : F // v ∈ Inc f} = ℓ + 1)
    (v : V) (f : {f : F // v ∈ Inc f}) : Function.Injective (incidenceMap Inc ℓ hdeg v f) :=
  directionMap_injective _

lemma incidenceMap_independent (hdeg : ∀ v, Fintype.card {f : F // v ∈ Inc f} = ℓ + 1)
    (v : V) (f g : {f : F // v ∈ Inc f}) (hne : f ≠ g) (a b : ZMod ℓ)
    (h : incidenceMap Inc ℓ hdeg v f a + incidenceMap Inc ℓ hdeg v g b = 0) :
    a = 0 ∧ b = 0 :=
  directionMap_independent ((incidenceEquiv Inc ℓ hdeg v).injective.ne hne) a b h

lemma incidenceMap_covers (hdeg : ∀ v, Fintype.card {f : F // v ∈ Inc f} = ℓ + 1)
    (v : V) (a : Fin 2 → ZMod ℓ) (ha : a ≠ 0) :
    ∃ (f : F) (hf : v ∈ Inc f) (c : ZMod ℓ), c ≠ 0 ∧ incidenceMap Inc ℓ hdeg v ⟨f, hf⟩ c = a := by
  obtain ⟨d, c, hc, hca⟩ := directionMap_covers a ha
  obtain ⟨f, hf⟩ := (incidenceEquiv Inc ℓ hdeg v).surjective d
  exact ⟨f.val, f.property, c, hc, by simpa [incidenceMap, hf] using hca⟩

end KaplanskyCounterexample.IncidenceDirections
end

end OAI
end
/- CHECKPOINT: OAI.RingTheory.DirectFiniteness.IncidenceDirections -/

/- BEGIN PINNED MODULE OAI.RingTheory.DirectFiniteness.AssignedDevelopment -/
section

namespace OAI

universe u_1 u_2 u_3

noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample.AssignedDirections
open IncidenceDirections
variable {V : Type u_1} {F : Type u_2} (Inc : F → Finset V) (ℓ : ℕ) [Fact ℓ.Prime]
variable (assign : ∀ v, {f : F // v ∈ Inc f} ≃ Option (ZMod ℓ))

def incidenceMap (v : V) (f : {f : F // v ∈ Inc f}) : ZMod ℓ →+ (Fin 2 → ZMod ℓ) :=
  (directionMap (assign v f)).toAddMonoidHom

lemma incidenceMap_injective (v : V) (f : {f : F // v ∈ Inc f}) :
    Function.Injective (incidenceMap Inc ℓ assign v f) := directionMap_injective _

lemma incidenceMap_independent (v : V) (f g : {f : F // v ∈ Inc f}) (hne : f ≠ g)
    (a b : ZMod ℓ) (h : incidenceMap Inc ℓ assign v f a + incidenceMap Inc ℓ assign v g b = 0) :
    a = 0 ∧ b = 0 := directionMap_independent ((assign v).injective.ne hne) a b h

lemma incidenceMap_covers (v : V) (a : Fin 2 → ZMod ℓ) (ha : a ≠ 0) :
    ∃ (f : F) (hf : v ∈ Inc f) (c : ZMod ℓ), c ≠ 0 ∧ incidenceMap Inc ℓ assign v ⟨f,hf⟩ c = a := by
  obtain ⟨d,c,hc,hca⟩ := directionMap_covers a ha
  obtain ⟨f,hf⟩ := (assign v).surjective d
  exact ⟨f.val,f.property,c,hc,by simpa [incidenceMap,hf] using hca⟩

end KaplanskyCounterexample.AssignedDirections

namespace KaplanskyCounterexample.AssignedDevelopment
open GluedGroup AssignedDirections IncidenceDirections
variable {V F : Type} (Inc : F → Finset V) (ℓ : ℕ) [Fact ℓ.Prime]
variable (assign : ∀ v, {f : F // v ∈ Inc f} ≃ Option (ZMod ℓ))
variable (hInc : ∀ f, (Inc f).Nonempty)

abbrev maps := AssignedDirections.incidenceMap Inc ℓ assign

lemma covers : CoversPoints Inc ℓ (maps Inc ℓ assign) :=
  AssignedDirections.incidenceMap_covers Inc ℓ assign

abbrev Base := N Inc ℓ (maps Inc ℓ assign)

def point (v : V) : PointGroup ℓ →* Base Inc ℓ assign :=
  theta Inc ℓ (maps Inc ℓ assign) (covers Inc ℓ assign) v

include hInc in
lemma point_injective
    (hg : 12 ≤ (Planar.incidenceGraph (fun v f => v ∈ Inc f)).egirth) (v : V) :
    Function.Injective (point Inc ℓ assign v) := by
  apply theta_injective _ _ _ _ hInc _ _ hg v
  · intro v f hv
    rw [totalMap_of_mem _ _ _ v f hv]
    exact AssignedDirections.incidenceMap_injective Inc ℓ assign v ⟨f, hv⟩
  · intro v f g hf hg hne a b hab
    rw [totalMap_of_mem _ _ _ v f hf, totalMap_of_mem _ _ _ v g hg] at hab
    exact (AssignedDirections.incidenceMap_independent Inc ℓ assign v ⟨f, hf⟩ ⟨g, hg⟩
      (fun h => hne (congrArg Subtype.val h)) a b hab).1

def line (f : F) : Multiplicative (ZMod ℓ) →* Base Inc ℓ assign :=
  (point Inc ℓ assign ((hInc f).choose)).comp
    (AddMonoidHom.toMultiplicative (maps Inc ℓ assign (hInc f).choose
      ⟨f, (hInc f).choose_spec⟩))

lemma point_direction (v : V) (f : F) (hf : v ∈ Inc f) (c : ZMod ℓ) :
    point Inc ℓ assign v (Multiplicative.ofAdd (maps Inc ℓ assign v ⟨f, hf⟩ c)) =
      line Inc ℓ assign hInc f (Multiplicative.ofAdd c) := by
  by_cases hc : c = 0
  · subst c
    simp
  · exact (theta_generator Inc ℓ (maps Inc ℓ assign) (covers Inc ℓ assign) v f hf c hc).trans
      (theta_generator Inc ℓ (maps Inc ℓ assign) (covers Inc ℓ assign) (hInc f).choose f (hInc f).choose_spec c hc).symm

lemma line_injective
    (hg : 12 ≤ (Planar.incidenceGraph (fun v f => v ∈ Inc f)).egirth) (f : F) :
    Function.Injective (line Inc ℓ assign hInc f) := by
  apply (point_injective Inc ℓ assign hInc hg (hInc f).choose).comp
  exact AssignedDirections.incidenceMap_injective Inc ℓ assign _ _

variable [Fintype F]

lemma subgroup_decomposition {K : Type u_3} [CommRing K] (v : V) :
    ∑ a : PointGroup ℓ, MonoidAlgebra.single (point Inc ℓ assign v a) (1 : K) =
      1 + ∑ f : {f : F // v ∈ Inc f},
        ((∑ c : Multiplicative (ZMod ℓ), MonoidAlgebra.single (line Inc ℓ assign hInc f.val c) (1 : K)) - 1) := by
  have h := sum_directions (K := ZMod ℓ) (fun a =>
    MonoidAlgebra.single (point Inc ℓ assign v (Multiplicative.ofAdd a)) (1 : K))
  rw [← Equiv.sum_comp Multiplicative.ofAdd
    (fun a : PointGroup ℓ => MonoidAlgebra.single (point Inc ℓ assign v a) (1 : K))]
  rw [h]
  simp only [ofAdd_zero, map_one, ← MonoidAlgebra.one_def]
  congr 1
  rw [← Equiv.sum_comp (assign v)
    (fun d : Option (ZMod ℓ) =>
      (∑ c : ZMod ℓ, MonoidAlgebra.single
        (point Inc ℓ assign v (Multiplicative.ofAdd (directionMap d c))) (1 : K)) - 1)]
  apply Finset.sum_congr rfl
  intro f _
  congr 1
  rw [← Equiv.sum_comp Multiplicative.ofAdd
    (fun c : Multiplicative (ZMod ℓ) => MonoidAlgebra.single (line Inc ℓ assign hInc f.val c) (1 : K))]
  apply Finset.sum_congr rfl
  intro c _
  exact congrArg (fun g => MonoidAlgebra.single g (1 : K))
    (point_direction Inc ℓ assign hInc v f.val f.property c)

end KaplanskyCounterexample.AssignedDevelopment
end

end OAI
end
/- CHECKPOINT: OAI.RingTheory.DirectFiniteness.AssignedDevelopment -/

/- BEGIN PINNED MODULE OAI.RingTheory.DirectFiniteness.PrescribedDirections -/
section

namespace OAI

noncomputable section
open scoped Classical
namespace KaplanskyCounterexample.Prescription
open IncidenceDirections
variable (ℓ : ℕ) [Fact ℓ.Prime]

local instance directionModulusNeZero : NeZero ℓ := inferInstance

/-- A direction is ordered by its full underlying point set. Slopes are just
coordinates for all of the one-dimensional subspaces, including the vertical one. -/
def directionSet (d : Option (ZMod ℓ)) : Finset (Fin 2 → ZMod ℓ) :=
  Finset.univ.image (directionMap d)

lemma directionSet_injective : Function.Injective (directionSet ℓ) := by
  intro d e he
  by_contra hne
  have hm : directionMap d 1 ∈ directionSet ℓ e := he ▸ Finset.mem_image.mpr ⟨1,Finset.mem_univ _,rfl⟩
  obtain ⟨c,_,hc⟩ := Finset.mem_image.mp hm
  have hh := directionMap_independent hne 1 (-c) (by simp [hc])
  exact one_ne_zero hh.1

local instance directionResidueOrder : LinearOrder (ZMod ℓ) := residueOrder ℓ

@[instance_reducible] def directionOrder : LinearOrder (Option (ZMod ℓ)) :=
  letI : LinearOrder (Fin 2 → ZMod ℓ) := vectorOrder
  letI : LinearOrder (Finset (Fin 2 → ZMod ℓ)) := subsetOrder _
  LinearOrder.lift' (directionSet ℓ) (directionSet_injective ℓ)

lemma direction_first (d : Option (ZMod ℓ)) (x : Fin 2 → ZMod ℓ)
    (hx : x ∈ directionSet ℓ d) (hne : x ≠ 0) :
    toLex (directionMap d 1) ≤ toLex x := by
  obtain ⟨c,_,rfl⟩ := Finset.mem_image.mp hx
  have hc : c ≠ 0 := by intro hc; apply hne; simp [hc]
  by_cases hc1 : c=1
  · subst c; exact le_refl _
  have hc0 : c.val ≠ 0 := by simpa using hc
  have hc1' : c.val ≠ 1 := by
    intro he
    apply hc1
    apply ZMod.val_injective ℓ
    simpa only [ZMod.val_one] using he
  have hl : (1:ZMod ℓ) < c := by
    change (1:ZMod ℓ).val < c.val
    rw [ZMod.val_one]
    omega
  apply le_of_lt
  cases d with
  | none =>
    refine ⟨1,?_,?_⟩
    · intro j hj
      have hj0 : j=0 := by omega
      subst j
      rfl
    · exact hl
  | some d =>
    refine ⟨0,?_,?_⟩
    · intro j hj; have : ¬ j < 0 := Fin.not_lt_zero j; exact (this hj).elim
    · exact hl

lemma direction_first_nonzero (d : Option (ZMod ℓ)) : directionMap d (1:ZMod ℓ) ≠ 0 := by
  intro hz
  exact one_ne_zero (directionMap_injective d (hz.trans (map_zero _).symm))

lemma direction_range_finrank (d : Option (ZMod ℓ)) :
    Module.finrank (ZMod ℓ) (LinearMap.range (directionMap d))=1 := by
  rw [LinearMap.finrank_range_of_inj (directionMap_injective d),Module.finrank_self]

def orderedAssignment {V F : Type} [Fintype F] [LinearOrder F] (Inc : F → Finset V)
    (hdeg : ∀ v, Fintype.card {f : F // v ∈ Inc f}=ℓ+1)
    (v : V) : {f : F // v ∈ Inc f} ≃ Option (ZMod ℓ) :=
  letI := directionOrder ℓ
  ((Fintype.orderIsoFinOfCardEq {f : F // v ∈ Inc f} (hdeg v)).toEquiv.symm.trans
    (Fintype.orderIsoFinOfCardEq (Option (ZMod ℓ)) (by simp)).toEquiv)

end KaplanskyCounterexample.Prescription
end

end OAI
end
/- CHECKPOINT: OAI.RingTheory.DirectFiniteness.PrescribedDirections -/

/- BEGIN PINNED MODULE OAI.RingTheory.DirectFiniteness.CoordinateCharacters -/
section

namespace OAI

universe u_1 u_2 u_3

noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample.CoordinateCharacters
variable (ℓ : ℕ) [Fact ℓ.Prime]

local instance modulusNeZero : NeZero ℓ := inferInstance

abbrev Plane := Multiplicative (Fin 2 → ZMod ℓ)
abbrev Cyclic := Multiplicative (ZMod ℓ)

def form (a : Fin 2 → ZMod ℓ) : Plane ℓ →* Cyclic ℓ :=
  AddMonoidHom.toMultiplicative
    ({ toFun := fun x => ∑ i : Fin 2, a i * x i
       map_zero' := by simp
       map_add' := by intro x y; simp [mul_add, Finset.sum_add_distrib] } :
      (Fin 2 → ZMod ℓ) →+ ZMod ℓ)

lemma form_injective : Function.Injective (form ℓ) := by
  intro a b hab
  funext i
  have hi := congrArg (fun φ : Plane ℓ →* Cyclic ℓ =>
    Multiplicative.toAdd (φ (Multiplicative.ofAdd (Pi.single i 1)))) hab
  fin_cases i <;> simpa [form, Pi.single_apply] using hi

lemma exists_slot_forms {V : Type u_1} {m : Type u_2} [Fintype V] [Fintype m]
    (hcard : Fintype.card V ≤ Fintype.card m * ℓ ^ 2) :
    ∃ (slot : V → m) (α : V → Plane ℓ →* Cyclic ℓ),
      ∀ v w, v ≠ w → slot v = slot w → α v ≠ α w := by
  have hc : Fintype.card V ≤ Fintype.card (m × (Fin 2 → ZMod ℓ)) := by
    simpa using hcard
  obtain ⟨f⟩ : Nonempty (V ↪ m × (Fin 2 → ZMod ℓ)) := Function.Embedding.nonempty_of_card_le hc
  refine ⟨fun v => (f v).1, fun v => form ℓ (f v).2, ?_⟩
  intro v w hvw hs ha
  exact hvw (f.injective (Prod.ext hs (form_injective ℓ ha)))

variable {K : Type u_3} [Field K]

def cyclicCharacter {ζ : K} (hζ : IsPrimitiveRoot ζ ℓ) : Cyclic ℓ →* Kˣ :=
  (AddChar.zmodChar ℓ hζ.pow_eq_one).toMonoidHom.toHomUnits

lemma cyclicCharacter_injective {ζ : K} (hζ : IsPrimitiveRoot ζ ℓ) :
    Function.Injective (cyclicCharacter ℓ hζ) := by
  intro a b hab
  apply Multiplicative.toAdd.injective
  apply ZMod.val_injective ℓ
  apply hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _)
  exact congrArg (fun u : Kˣ => (u : K)) hab

lemma cyclicCharacter_ne_one {ζ : K} (hζ : IsPrimitiveRoot ζ ℓ) :
    cyclicCharacter ℓ hζ ≠ 1 := by
  intro h
  have he : Multiplicative.ofAdd (1 : ZMod ℓ) = 1 :=
    (cyclicCharacter_injective ℓ hζ) (by simp [h])
  exact (one_ne_zero : (1 : ZMod ℓ) ≠ 0) (congrArg Multiplicative.toAdd he)

end KaplanskyCounterexample.CoordinateCharacters
end

end OAI
end
/- CHECKPOINT: OAI.RingTheory.DirectFiniteness.CoordinateCharacters -/

/- BEGIN PINNED MODULE OAI.RingTheory.DirectFiniteness.PrescribedSlots -/
section

namespace OAI

noncomputable section
open scoped Classical
namespace KaplanskyCounterexample.Prescription
variable (ℓ : ℕ) [Fact ℓ.Prime]
variable {V m : Type} [Fintype V] [Fintype m] [LinearOrder V] [LinearOrder m]

local instance slotModulusNeZero : NeZero ℓ := inferInstance

local instance slotIndexWellFounded : WellFoundedLT (Fin 2) := inferInstance

@[instance_reducible] def slotPairOrder : LinearOrder (m × (Fin 2 → ZMod ℓ)) :=
  letI : LinearOrder (ZMod ℓ) := residueOrder ℓ
  letI : LinearOrder (Fin 2 → ZMod ℓ) := vectorOrder
  LinearOrder.lift' (toLex : (m × (Fin 2 → ZMod ℓ)) → Lex (m × (Fin 2 → ZMod ℓ)))
    (fun _ _ he => he)

def slotAssignment (hsize : Fintype.card V ≤ Fintype.card m * ℓ^2) :
    V ↪ m × (Fin 2 → ZMod ℓ) :=
  letI := slotPairOrder (m := m) ℓ
  let e := Fintype.orderIsoFinOfCardEq (m × (Fin 2 → ZMod ℓ)) rfl
  let r := (Fintype.orderIsoFinOfCardEq V rfl).symm
  { toFun := fun v => e ⟨(r v).val, by
      have hc : Fintype.card (m × (Fin 2 → ZMod ℓ))=Fintype.card m * ℓ^2 := by simp
      rw [hc]
      exact (r v).isLt.trans_le hsize⟩
    inj' := by
      intro v w he
      apply r.injective
      apply Fin.ext
      have hh := e.injective he
      exact congrArg (fun z => z.val) hh }

/-- The assigned pair has exactly the point's rank in the finite order, so the
image consists of the first t pairs, with none skipped or repeated. -/
lemma slotAssignment_rank (hsize : Fintype.card V ≤ Fintype.card m * ℓ^2) (v : V) :
    letI := slotPairOrder (m := m) ℓ
    ((Fintype.orderIsoFinOfCardEq (m × (Fin 2 → ZMod ℓ)) rfl).symm
      (slotAssignment ℓ hsize v)).val =
      ((Fintype.orderIsoFinOfCardEq V rfl).symm v).val := by
  let := slotPairOrder (m := m) ℓ
  exact congrArg Fin.val (OrderIso.symm_apply_apply _ _)

lemma slotAssignment_first_pairs (hsize : Fintype.card V ≤ Fintype.card m * ℓ^2)
    (p : m × (Fin 2 → ZMod ℓ)) :
    letI := slotPairOrder (m := m) ℓ
    p ∈ Set.range (slotAssignment ℓ hsize) ↔
      ((Fintype.orderIsoFinOfCardEq (m × (Fin 2 → ZMod ℓ)) rfl).symm p).val < Fintype.card V := by
  let := slotPairOrder (m := m) ℓ
  let e := Fintype.orderIsoFinOfCardEq (m × (Fin 2 → ZMod ℓ)) rfl
  let r := Fintype.orderIsoFinOfCardEq V rfl
  constructor
  · rintro ⟨v,rfl⟩
    rw [slotAssignment_rank]
    exact (r.symm v).isLt
  · intro hp
    refine ⟨r ⟨(e.symm p).val,hp⟩,?_⟩
    apply e.symm.injective
    apply Fin.ext
    rw [slotAssignment_rank]
    exact congrArg Fin.val (r.symm_apply_apply _)

def assignedSlot (hsize : Fintype.card V ≤ Fintype.card m * ℓ^2) (v : V) : m :=
  (slotAssignment ℓ hsize v).1

def assignedForm (hsize : Fintype.card V ≤ Fintype.card m * ℓ^2) (v : V) :
    CoordinateCharacters.Plane ℓ →* CoordinateCharacters.Cyclic ℓ :=
  CoordinateCharacters.form ℓ (slotAssignment ℓ hsize v).2

lemma assignedForm_distinct (hsize : Fintype.card V ≤ Fintype.card m * ℓ^2)
    (v w : V) (hvw : v ≠ w) (hs : assignedSlot ℓ hsize v=assignedSlot ℓ hsize w) :
    assignedForm ℓ hsize v ≠ assignedForm ℓ hsize w := by
  intro he
  exact hvw ((slotAssignment ℓ hsize).injective
    (Prod.ext hs (CoordinateCharacters.form_injective ℓ he)))

end KaplanskyCounterexample.Prescription
end

end OAI
end
/- CHECKPOINT: OAI.RingTheory.DirectFiniteness.PrescribedSlots -/

/- BEGIN PINNED MODULE OAI.RingTheory.DirectFiniteness.PrescribedPairing -/
section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample
open PolynomialPairing FiniteGeometry

/-- The numerical interval for the holes gives exactly the strict rectangular
inequality and the ell-squared packing bound, without rounding assumptions. -/
lemma hole_size_inequalities {N m ℓ : ℕ} (hN : 0 < N) (hmN : m ≤ N)
    (hℓ : 3 ≤ ℓ) (hlo : 2 * N ≤ m * (ℓ+1)^2)
    (hhi : m * (ℓ+1)^2 ≤ 7 * N) :
    0 < m ∧ m < N-m ∧ N-m ≤ m * ℓ^2 := by
  have hm : 0 < m := by
    by_contra hh
    have he : m = 0 := by omega
    rw [he,zero_mul] at hlo
    omega
  have hsq : 16 ≤ (ℓ+1)^2 := by nlinarith
  have hmb : 16*m ≤ 7*N := (by nlinarith : 16*m ≤ m*(ℓ+1)^2).trans hhi
  have hsmall : 2*m < N := by nlinarith
  have hs : (ℓ+1)^2 ≤ 2*(ℓ^2+1) := by nlinarith [sq_nonneg (ℓ-1 : ℤ)]
  have hn : N ≤ m*ℓ^2 + m := by nlinarith
  exact ⟨hm,by omega,by omega⟩

namespace PolynomialPairing
variable {Q K : Type} [Field Q] [Fintype Q] [Field K] [Algebra Q K]
  {q n : ℕ}

def complementMatrix (a : Fin q ≃ Q) (O : Finset (Fin n → Q)) :
    Matrix O {v : Fin n → Q // v ∉ O} K :=
  fun i v => algebraMap Q K (column a ((q-2)/2) O v.val i)

lemma complementMatrix_global (a : Fin q ≃ Q) (hq : q = Fintype.card Q)
    (hn : 0 < n) (O : Finset (Fin n → Q))
    (hO : O ⊆ simplexPoints a n ((q-2)/2)) :
    complementMatrix (K := K) a O * (complementMatrix (K := K) a O).transpose = -1 := by
  ext i j
  have hh := congrFun (congrFun (sum_complement_gram a hq hn O hO) i) j
  simp only [Matrix.sum_apply,gramColumn,Matrix.neg_apply,Matrix.one_apply] at hh
  have hs : ∑ v : {v : Fin n → Q // v ∉ O},
      column a ((q-2)/2) O v.val i * column a ((q-2)/2) O v.val j =
      ∑ v ∈ Finset.univ \ O, column a ((q-2)/2) O v i * column a ((q-2)/2) O v j := by
    symm
    exact Finset.sum_subtype _ (by simp) _
  change (∑ v : {v : Fin n → Q // v ∉ O},
    algebraMap Q K (column a ((q-2)/2) O v.val i) *
    algebraMap Q K (column a ((q-2)/2) O v.val j)) = -(if i = j then 1 else 0)
  simp_rw [← map_mul]
  rw [← map_sum,hs,hh]
  simp

lemma sum_fullLine_gram (a : Fin q ≃ Q) (hq : q = Fintype.card Q)
    (O : Finset (Fin n → Q)) {s : Finset (Fin n → Q)} (hs : FullLine (Q := Q) s) :
    ∑ v ∈ s, gramColumn a ((q-2)/2) O v = 0 := by
  obtain ⟨x,w,hw,rfl⟩ := hs
  let l : PolynomialPairing.AffineLine Q n := ⟨x,w,hw⟩
  have hl : l.points = linePoints (Q := Q) x w := by
    ext z
    simp only [PolynomialPairing.AffineLine.points,linePoints,Finset.mem_image,
      Finset.mem_univ,true_and]
    rfl
  rw [← hl]
  exact sum_line_gram a hq O l

lemma complementMatrix_local (a : Fin q ≃ Q) (hq : q = Fintype.card Q)
    (O : Finset (Fin n → Q)) {s : Finset (Fin n → Q)}
    (hs : FullLine (Q := Q) s) (ha : ∀ v ∈ s, v ∉ O) (i j : O) :
    ∑ v ∈ s.subtype (fun v => v ∉ O),
      complementMatrix (K := K) a O i v * complementMatrix a O j v = 0 := by
  have hh := congrFun (congrFun (sum_fullLine_gram a hq O hs) i) j
  simp only [Matrix.sum_apply,gramColumn,Matrix.zero_apply] at hh
  change ∑ v ∈ s.subtype (fun v => v ∉ O),
    algebraMap Q K (column a ((q-2)/2) O v.val i) *
    algebraMap Q K (column a ((q-2)/2) O v.val j) = 0
  simp_rw [← map_mul]
  rw [← map_sum]
  have he : (∑ v ∈ s.subtype (fun v => v ∉ O),
      column a ((q-2)/2) O v.val i * column a ((q-2)/2) O v.val j) =
      ∑ v ∈ s, column a ((q-2)/2) O v i * column a ((q-2)/2) O v j := by
    exact Finset.sum_subtype_of_mem (fun v => column a ((q-2)/2) O v i * column a ((q-2)/2) O v j) ha
  rw [he,hh,map_zero]

end PolynomialPairing

end KaplanskyCounterexample
end

end OAI
end
/- CHECKPOINT: OAI.RingTheory.DirectFiniteness.PrescribedPairing -/

/- BEGIN PINNED MODULE OAI.RingTheory.DirectFiniteness.PrescribedData -/
section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample.Prescription.Output
open PolynomialPairing

abbrev h := selectedInput
abbrev q := Qcard h.val
abbrev ell := prime h.val
abbrev n := dimension h.val
abbrev Coeff := K h
abbrev Subfield := Q h
abbrev Ambient := Affine h
abbrev holes : Finset Ambient := selectedPair.1
abbrev family : Finset (Finset Ambient) := selectedPair.2
abbrev V := {v : Ambient // v ∉ holes}
abbrev F := ↥family
abbrev Slots := ↥holes

instance ell_prime : Fact ell.Prime := ⟨prime_prime h.val⟩
local instance (priority := 3000) : DecidableEq Subfield := Classical.decEq _
@[instance_reducible] instance ambient_order : LinearOrder Ambient := vectorOrder
@[instance_reducible] instance subsets_order : LinearOrder (Finset Ambient) := subsetOrder _
instance (priority := 2000) ambient_le : LE Ambient := ambient_order.toLE
instance (priority := 2000) ambient_lt : LT Ambient := ambient_order.toLT
instance (priority := 2000) subsets_le : LE (Finset Ambient) := subsets_order.toLE
instance (priority := 2000) subsets_lt : LT (Finset Ambient) := subsets_order.toLT
local instance (priority := 3000) : DecidableEq V := Classical.decEq _

lemma success : Successful (enumeration h) ell selectedPair := selectedPair_spec

def Inc (f : F) : Finset V := f.val.subtype (fun v => v ∉ holes)
lemma mem_Inc (v : V) (f : F) : v ∈ Inc f ↔ v.val ∈ f.val := Finset.mem_subtype

lemma nonempty_Inc (f : F) : (Inc f).Nonempty := by
  obtain ⟨v,hv⟩ := (success.full f.val f.property).nonempty
  exact ⟨⟨v,success.avoid f.val f.property v hv⟩,(mem_Inc _ _).mpr hv⟩
lemma degree_Inc (v : V) : Fintype.card {f : F // v ∈ Inc f}=ell+1 := by
  rw [Fintype.card_eq_nat_card]
  have hr := success.regular v
  rw [Fintype.card_eq_nat_card] at hr
  exact (Nat.card_congr (Equiv.subtypeEquivRight (fun f => mem_Inc v f))).trans hr
lemma girth_Inc : 12 ≤ (Planar.incidenceGraph (fun (v : V) (f : F) => v ∈ Inc f)).egirth := by
  have he : (fun (v : V) (f : F) => v ∈ Inc f) = (fun (v : V) (f : F) => v.val ∈ f.val) := by
    funext v f
    exact propext (mem_Inc v f)
  rw [he]
  exact success.girth

lemma ambient_card : Fintype.card Ambient=q^n := by
  change Fintype.card (Fin n → Q h)=q^n
  rw [Fintype.card_fun,Fintype.card_fin,Q_card]
lemma V_card : Fintype.card V=q^n-holes.card := by
  simp only [V,Fintype.card_subtype_compl,Fintype.card_coe,ambient_card]
lemma sizes : 0 < Fintype.card Slots ∧ Fintype.card Slots < Fintype.card V ∧
    Fintype.card V ≤ Fintype.card Slots*ell^2 := by
  rw [V_card,Fintype.card_coe]
  exact hole_size_inequalities (by rw [← ambient_card]; exact Fintype.card_pos)
    ((Finset.card_le_univ holes).trans_eq ambient_card) (prime_ge h.val h.property)
    success.lower success.upper

/-- The specified first point and first matrix coordinate in their inherited orders. -/
def v0 : V := first (fun _ => True) (by
  obtain ⟨v⟩ := Fintype.card_pos_iff.mp (sizes.1.trans sizes.2.1)
  exact ⟨v,trivial⟩)
def i0 : Slots := first (fun _ => True) (by
  obtain ⟨i⟩ := Fintype.card_pos_iff.mp sizes.1
  exact ⟨i,trivial⟩)
lemma v0_first (v : V) : v0 ≤ v := by exact first_le (fun _ : V => True) _ v trivial
lemma i0_first (i : Slots) : i0 ≤ i := by exact first_le (fun _ : Slots => True) _ i trivial

def assignment : ∀ v, {f : F // v ∈ Inc f} ≃ Option (ZMod ell) :=
  orderedAssignment ell Inc degree_Inc

def slot : V → Slots := assignedSlot ell sizes.2.2
def form : V → GluedGroup.PointGroup ell →* Multiplicative (ZMod ell) :=
  assignedForm ell sizes.2.2
lemma forms_distinct (v w : V) (hne : v ≠ w) (hs : slot v=slot w) : form v ≠ form w :=
  assignedForm_distinct ell sizes.2.2 v w hne hs

/-- The unique interpolation columns over the actual prescribed root subfield. -/
def X : Matrix Slots V Coeff := complementMatrix (enumeration h) holes
lemma X_global : X * X.transpose = -1 :=
  complementMatrix_global _ (Q_card h).symm (dimension_pos h.val) _ success.holes_subset
lemma X_local (f : F) (i j : Slots) : ∑ v ∈ Inc f, X i v * X j v=0 :=
  complementMatrix_local _ (Q_card h).symm holes (success.full f.val f.property)
    (success.avoid f.val f.property) i j

end KaplanskyCounterexample.Prescription.Output
end

end OAI
end
/- CHECKPOINT: OAI.RingTheory.DirectFiniteness.PrescribedData -/

/- BEGIN PINNED MODULE OAI.RingTheory.DirectFiniteness.MultiHNN -/
section

namespace OAI

universe u_1 u_2 u_3

noncomputable section
open scoped Classical
open Monoid Function
namespace KaplanskyCounterexample.MultipleHNN

universe u v
variable {H : Type u} [Group H] {I : Type v}
variable (A B : I → Subgroup H) (φ : ∀ i, A i ≃* B i)

def con : Con (Monoid.Coprod H (FreeGroup I)) := conGen fun x y =>
  ∃ (i : I) (a : A i), x = Coprod.inr (FreeGroup.of i) * Coprod.inl (a : H) ∧
    y = Coprod.inl (φ i a : H) * Coprod.inr (FreeGroup.of i)

abbrev Extension := (con A B φ).Quotient

instance : Group (Extension A B φ) := by delta Extension; infer_instance

def of : H →* Extension A B φ := (con A B φ).mk'.comp Coprod.inl

def letter (i : I) : Extension A B φ := (con A B φ).mk' (Coprod.inr (FreeGroup.of i))

lemma letter_mul_of (i : I) (a : A i) :
    letter A B φ i * of A B φ a = of A B φ (φ i a) * letter A B φ i :=
  (Con.eq _).mpr <| ConGen.Rel.of _ _ ⟨i, a, rfl, rfl⟩

def lift {G : Type u_1} [Group G] (f : H →* G) (t : I → G)
    (ht : ∀ i (a : A i), t i * f a = f (φ i a) * t i) : Extension A B φ →* G :=
  Con.lift _ (Coprod.lift f (FreeGroup.lift t)) (Con.conGen_le.mpr (by
    rintro _ _ ⟨i, a, rfl, rfl⟩
    simp [ht]))

@[simp] lemma lift_of {G : Type u_2} [Group G] (f : H →* G) (t : I → G)
    (ht : ∀ i (a : A i), t i * f a = f (φ i a) * t i) (h : H) :
    lift A B φ f t ht (of A B φ h) = f h := by
  change Coprod.lift f (FreeGroup.lift t) (Coprod.inl h) = f h
  simp

@[simp] lemma lift_letter {G : Type u_3} [Group G] (f : H →* G) (t : I → G)
    (ht : ∀ i (a : A i), t i * f a = f (φ i a) * t i) (i : I) :
    lift A B φ f t ht (letter A B φ i) = t i := by
  change Coprod.lift f (FreeGroup.lift t) (Coprod.inr (FreeGroup.of i)) = t i
  simp

/-- Extend any finite sublist of the required conjugacies one at a time.
Mathlib's complete Britton-lemma proof supplies the embedding at each step. -/
theorem finite_partial_realization (S : Finset I) :
    ∃ (G : Type (max u v)) (_ : Group G) (f : H →* G),
      Function.Injective f ∧ ∃ t : I → G,
        ∀ i ∈ S, ∀ a : A i, t i * f a = f (φ i a) * t i := by
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨ULift.{v} H, inferInstance, (MulEquiv.ulift : ULift.{v} H ≃* H).symm.toMonoidHom,
      (MulEquiv.ulift : ULift.{v} H ≃* H).symm.injective, fun _ => 1, ?_⟩
    simp
  | @insert i S hi ih =>
    obtain ⟨G, hG, f, hf, t, ht⟩ := ih
    let fA := (A i).equivMapOfInjective f hf
    let fB := (B i).equivMapOfInjective f hf
    let ψ : (A i).map f ≃* (B i).map f := fA.symm.trans ((φ i).trans fB)
    let E := HNNExtension G ((A i).map f) ((B i).map f) ψ
    let emb : G →* E := HNNExtension.of
    let t' : I → E := fun j => if j = i then HNNExtension.t else emb (t j)
    refine ⟨E, inferInstance, emb.comp f,
      (HNNExtension.of_injective ψ).comp hf, t', ?_⟩
    intro j hj a
    rcases Finset.mem_insert.mp hj with rfl | hj
    · have h := HNNExtension.t_mul_of (φ := ψ) (fA a)
      simpa [t', fA, fB, ψ, emb] using h
    · by_cases hji : j = i
      · subst j
        have h := HNNExtension.t_mul_of (φ := ψ) (fA a)
        simpa [t', fA, fB, ψ, emb] using h
      · simpa [t', hji, ← map_mul] using congrArg emb (ht j hj a)

theorem of_injective [Fintype I] : Function.Injective (of A B φ) := by
  obtain ⟨G, hG, f, hf, t, ht⟩ := finite_partial_realization A B φ Finset.univ
  intro x y h
  apply hf
  have h' := congrArg (lift A B φ f t (fun i a => ht i (Finset.mem_univ i) a)) h
  simpa using h'

/-- The presentation is generated by the base group and the stable letters. -/
@[elab_as_elim]
theorem induction_on {P : Extension A B φ → Prop} (x : Extension A B φ)
    (hof : ∀ h, P (of A B φ h)) (ht : ∀ i, P (letter A B φ i))
    (hmul : ∀ x y, P x → P y → P (x * y)) (hinv : ∀ x, P x → P x⁻¹) : P x := by
  obtain ⟨w, rfl⟩ := (Con.mk'_surjective (c := con A B φ)) x
  induction w using Coprod.induction_on with
  | inl h => exact hof h
  | inr w =>
    induction w using FreeGroup.induction_on with
    | one => simpa only [map_one] using hof 1
    | of i => exact ht i
    | inv_of i ih => simpa only [map_inv] using hinv _ ih
    | mul a b ha hb => simpa only [map_mul] using hmul _ _ ha hb
  | mul a b ha hb => simpa only [map_mul] using hmul _ _ ha hb

/-- A central base element fixed in every associated subgroup stays central. -/
theorem of_central (z : H) (hz : ∀ h : H, Commute h z)
    (ha : ∀ i, z ∈ A i) (hφ : ∀ i, (φ i ⟨z, ha i⟩ : H) = z) :
    ∀ x : Extension A B φ, Commute x (of A B φ z) := by
  intro x
  induction x using induction_on A B φ with
  | hof h => exact (hz h).map (of A B φ)
  | ht i =>
    have h := letter_mul_of A B φ i ⟨z, ha i⟩
    rw [hφ i] at h
    exact h
  | hmul x y hx hy => exact hx.mul_left hy
  | hinv x hx => exact hx.inv_left

/-- Finite generation of the exact multiple-HNN presentation. -/
instance [Finite I] [Group.FG H] : Group.FG (Extension A B φ) := by
  obtain ⟨S, hS, hfin⟩ := Group.fg_iff.mp (inferInstance : Group.FG H)
  let T : Set (Extension A B φ) := of A B φ '' S ∪ Set.range (letter A B φ)
  apply Group.fg_iff.mpr
  refine ⟨T, ?_, (hfin.image _).union (Set.finite_range _)⟩
  apply top_unique
  intro x hxTop
  clear hxTop
  induction x using induction_on A B φ with
  | hof h =>
    have hh : h ∈ Subgroup.closure S := hS ▸ Subgroup.mem_top h
    induction hh using Subgroup.closure_induction with
    | mem h hh => exact Subgroup.subset_closure (Or.inl ⟨h, hh, rfl⟩)
    | one => simp
    | mul h k _ _ hh hk => simpa using (Subgroup.closure T).mul_mem hh hk
    | inv h _ hh => simpa using (Subgroup.closure T).inv_mem hh
  | ht i => exact Subgroup.subset_closure (Or.inr ⟨i, rfl⟩)
  | hmul x y hx hy => exact (Subgroup.closure T).mul_mem hx hy
  | hinv x hx => exact (Subgroup.closure T).inv_mem hx

end KaplanskyCounterexample.MultipleHNN
end

end OAI
end
/- CHECKPOINT: OAI.RingTheory.DirectFiniteness.MultiHNN -/

/- BEGIN PINNED MODULE OAI.RingTheory.DirectFiniteness.CharacterIdempotents -/
section

namespace OAI

universe u_1 u_2 u_3

noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample.CharacterIdempotents
variable {K : Type u_1} {A : Type u_2} {G : Type u_3} [Field K] [Group A] [Fintype A] [Group G]

def projector (χ : A →* Kˣ) : MonoidAlgebra K A :=
  (Fintype.card A : K)⁻¹ • ∑ a : A, MonoidAlgebra.single a ((χ a : K)⁻¹)

lemma sum_character_eq_zero (χ : A →* Kˣ) (hχ : χ ≠ 1) :
    ∑ a : A, (χ a : K) = 0 := by
  have hn : ∃ b : A, (χ b : K) ≠ 1 := by
    by_contra! h
    apply hχ
    ext b
    exact h b
  obtain ⟨b, hb⟩ := hn
  have hh : (χ b : K) * ∑ a : A, (χ a : K) = ∑ a : A, (χ a : K) := by
    rw [Finset.mul_sum]
    simp only [← Units.val_mul, ← map_mul]
    exact Equiv.sum_comp (Equiv.mulLeft b) (fun a => (χ a : K))
  by_contra hs
  exact hb ((mul_eq_right₀ hs).mp hh)

lemma projector_mul_single (χ : A →* Kˣ) (b : A) :
    projector χ * MonoidAlgebra.single b 1 = (χ b : K) • projector χ := by
  unfold projector
  rw [smul_mul_assoc, Finset.sum_mul, smul_smul]
  rw [mul_comm (χ b : K), ← smul_smul]
  congr 1
  rw [Finset.smul_sum]
  calc
    (∑ a : A, MonoidAlgebra.single a ((χ a : K)⁻¹) * MonoidAlgebra.single b 1) =
        ∑ a : A, (χ b : K) • MonoidAlgebra.single (a * b) ((χ (a * b) : K)⁻¹) := by
      apply Finset.sum_congr rfl
      intro a _
      simp [MonoidAlgebra.single_mul_single, mul_comm]
    _ = _ := Equiv.sum_comp (Equiv.mulRight b)
      (fun a : A => (χ b : K) • MonoidAlgebra.single a ((χ a : K)⁻¹))

lemma projector_mul (χ ψ : A →* Kˣ) :
    projector χ * projector ψ =
      ((Fintype.card A : K)⁻¹ * ∑ b : A, ((χ b : K) * (ψ b : K)⁻¹)) •
        projector χ := by
  conv_lhs => rhs; unfold projector
  rw [mul_smul_comm, Finset.mul_sum]
  have hh (b : A) : projector χ * MonoidAlgebra.single b ((ψ b : K)⁻¹) =
      ((χ b : K) * (ψ b : K)⁻¹) • projector χ := by
    rw [show MonoidAlgebra.single b ((ψ b : K)⁻¹) =
      (ψ b : K)⁻¹ • MonoidAlgebra.single b 1 by simp]
    rw [mul_smul_comm, projector_mul_single, smul_smul, mul_comm]
  simp_rw [hh]
  rw [← Finset.sum_smul, smul_smul]

lemma projector_idempotent (χ : A →* Kˣ) (hcard : (Fintype.card A : K) ≠ 0) :
    IsIdempotentElem (projector χ) := by
  change projector χ * projector χ = projector χ
  rw [projector_mul]
  simp [hcard]

lemma projector_orthogonal (χ ψ : A →* Kˣ) (hne : χ ≠ ψ) :
    projector χ * projector ψ = 0 := by
  rw [projector_mul]
  have hn : χ * ψ⁻¹ ≠ 1 := by
    intro h
    apply hne
    apply MonoidHom.ext
    intro a
    have hh := congrArg (fun f : A →* Kˣ => f a) h
    exact mul_inv_eq_one.mp hh
  have h := sum_character_eq_zero (χ * ψ⁻¹) hn
  simpa using congrArg (fun c : K => ((Fintype.card A : K)⁻¹ * c) • projector χ) h

lemma projector_one_coeff (χ : A →* Kˣ) :
    (projector χ).coeff 1 = (Fintype.card A : K)⁻¹ := by
  simp [projector, MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_smul, Finsupp.single_apply]

lemma projector_ne_zero (χ : A →* Kˣ) (hcard : (Fintype.card A : K) ≠ 0) :
    projector χ ≠ 0 := by
  intro h
  have := congrArg (fun p : MonoidAlgebra K A => p.coeff 1) h
  rw [projector_one_coeff] at this
  exact (inv_ne_zero hcard) this

/-- Transport the character projector along an actual subgroup embedding. -/
def pushed (f : A →* G) (χ : A →* Kˣ) : MonoidAlgebra K G :=
  MonoidAlgebra.mapDomainAlgHom K K f (projector χ)

lemma pushed_eq_sum (f : A →* G) (χ : A →* Kˣ) :
    pushed f χ = (Fintype.card A : K)⁻¹ •
      ∑ a : A, MonoidAlgebra.single (f a) ((χ a : K)⁻¹) := by
  simp [pushed, projector, map_sum]

lemma pushed_idempotent (f : A →* G) (χ : A →* Kˣ)
    (hc : (Fintype.card A : K) ≠ 0) :
    pushed f χ * pushed f χ = pushed f χ := by
  unfold pushed
  rw [← map_mul, projector_idempotent χ hc]

lemma pushed_orthogonal (f : A →* G) (χ ψ : A →* Kˣ) (hne : χ ≠ ψ) :
    pushed f χ * pushed f ψ = 0 := by
  unfold pushed
  rw [← map_mul, projector_orthogonal χ ψ hne, map_zero]

lemma pushed_ne_zero (f : A →* G) (hf : Function.Injective f) (χ : A →* Kˣ)
    (hc : (Fintype.card A : K) ≠ 0) : pushed f χ ≠ 0 := by
  intro h
  exact projector_ne_zero χ hc ((MonoidAlgebra.mapDomain_injective hf) (h.trans (MonoidAlgebra.mapDomain_zero f).symm))

lemma pushed_mul_single (f : A →* G) (χ : A →* Kˣ) (b : A) :
    pushed f χ * MonoidAlgebra.single (f b) 1 = (χ b : K) • pushed f χ := by
  have h := congrArg (MonoidAlgebra.mapDomainAlgHom K K f) (projector_mul_single χ b)
  rw [map_mul, map_smul] at h
  simpa only [pushed, MonoidAlgebra.mapDomainAlgHom_apply, MonoidAlgebra.mapDomain_single] using h

lemma pushed_central (f : A →* G) (χ : A →* Kˣ)
    (hf : ∀ a g, Commute (f a) g) (x : MonoidAlgebra K G) :
    Commute (pushed f χ) x := by
  induction x using MonoidAlgebra.induction_on with
  | of g =>
    change pushed f χ * MonoidAlgebra.single g 1 = _
    rw [pushed_eq_sum, smul_mul_assoc, mul_smul_comm]
    congr 1
    rw [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    simp only [MonoidAlgebra.of_apply, MonoidAlgebra.single_mul_single, mul_one, one_mul,
      (hf a g).eq]
  | add x y hx hy => exact hx.add_right hy
  | smul r x hx => exact hx.smul_right r

lemma lift_pushed (f : A →* G) (χ : A →* Kˣ) (ρ : G →* K)
    (hρ : ∀ a, ρ (f a) = (χ a : K)) (hc : (Fintype.card A : K) ≠ 0) :
    MonoidAlgebra.lift K K G ρ (pushed f χ) = 1 := by
  rw [pushed_eq_sum]
  simp [map_sum, MonoidAlgebra.lift_single, hρ, hc]

end KaplanskyCounterexample.CharacterIdempotents

end

end OAI
end
/- CHECKPOINT: OAI.RingTheory.DirectFiniteness.CharacterIdempotents -/

/- BEGIN PINNED MODULE OAI.RingTheory.DirectFiniteness.CharacterTwist -/
section

namespace OAI

universe u_1 u_2 u_3 u_4 u_5

noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample.CharacterTwist
open MultipleHNN CharacterIdempotents
variable {A : Type u_1} {N : Type u_2} {C : Type u_3} {V : Type u_4} [CommGroup A] [Group N] [CommGroup C]
variable (ι : V → A →* N) (hi : ∀ v, Function.Injective (ι v)) (v₀ : V)
variable (α : V → A →* C)

abbrev H := N × C

def src (v : V) : (A × C) →* H (N := N) (C := C) :=
  (ι v).prodMap (MonoidHom.id C)

def dst (v : V) : (A × C) →* H (N := N) (C := C) where
  toFun a := (ι v₀ a.1, a.2 * α v a.1)
  map_one' := by simp
  map_mul' a b := by ext <;> simp [map_mul]; ac_rfl

include hi in
lemma src_injective (v : V) : Function.Injective (src (C := C) ι v) := by
  rintro ⟨a,c⟩ ⟨b,d⟩ h
  exact Prod.ext (hi v (congrArg Prod.fst h)) (congrArg (fun p : N × C => p.2) h)

include hi in
lemma dst_injective (v : V) : Function.Injective (dst ι v₀ α v) := by
  rintro ⟨a,c⟩ ⟨b,d⟩ h
  have hab : a = b := hi v₀ (congrArg Prod.fst h)
  subst b
  exact Prod.ext rfl (mul_right_cancel (congrArg (fun p : N × C => p.2) h))

abbrev source (v : V) := (src (C := C) ι v).range
abbrev target (v : V) := (dst ι v₀ α v).range

def edgeIso (v : V) : source (C := C) ι v ≃* target ι v₀ α v :=
  (MonoidHom.ofInjective (src_injective ι hi v)).symm.trans
    (MonoidHom.ofInjective (dst_injective ι hi v₀ α v))

abbrev L := Extension (source (C := C) ι) (target ι v₀ α) (edgeIso ι hi v₀ α)
abbrev emb : H (N := N) (C := C) →* L ι hi v₀ α :=
  of (source (C := C) ι) (target ι v₀ α) (edgeIso ι hi v₀ α)
abbrev τ (v : V) : L ι hi v₀ α :=
  letter (source (C := C) ι) (target ι v₀ α) (edgeIso ι hi v₀ α) v

lemma emb_injective [Fintype V] : Function.Injective (emb ι hi v₀ α) :=
  of_injective _ _ _

lemma conjugacy (v : V) (a : A) (c : C) :
    τ ι hi v₀ α v * emb ι hi v₀ α (ι v a, c) =
      emb ι hi v₀ α (ι v₀ a, c * α v a) * τ ι hi v₀ α v := by
  have h := letter_mul_of (source (C := C) ι) (target ι v₀ α) (edgeIso ι hi v₀ α)
    v (MonoidHom.ofInjective (src_injective ι hi v) (a,c))
  have he : edgeIso ι hi v₀ α v (MonoidHom.ofInjective (src_injective ι hi v) (a,c)) =
      MonoidHom.ofInjective (dst_injective ι hi v₀ α v) (a,c) := by
    exact congrArg (MonoidHom.ofInjective (dst_injective ι hi v₀ α v))
      ((MonoidHom.ofInjective (src_injective ι hi v)).symm_apply_apply (a,c))
  rw [he] at h
  exact h

lemma central_cyclic (c : C) (x : L ι hi v₀ α) :
    Commute (emb ι hi v₀ α (1,c)) x := by
  apply Commute.symm
  exact of_central (source (C := C) ι) (target ι v₀ α) (edgeIso ι hi v₀ α) (1,c)
    (by
      rintro ⟨n,d⟩
      change (n,d) * (1,c) = (1,c) * (n,d)
      ext <;> simp [mul_comm]) (by
      intro v
      exact ⟨(1,c), by simp [src]⟩) (by
      intro v
      change (dst ι v₀ α v) ((MonoidHom.ofInjective (src_injective ι hi v)).symm _) = _
      have he : (⟨(1,c), ⟨(1,c), by simp [src]⟩⟩ : source (C := C) ι v) =
          MonoidHom.ofInjective (src_injective ι hi v) (1,c) := by
        apply Subtype.ext
        change (1,c) = (src (C := C) ι v) (1,c)
        simp [src]
      rw [he, MulEquiv.symm_apply_apply]
      simp [dst]) x

variable {K : Type u_5} [Field K] [Fintype A] [Fintype C]
variable (ξ : C →* Kˣ)

def zHom : C →* L ι hi v₀ α := (emb ι hi v₀ α).comp (MonoidHom.inr N C)
def localHom (v : V) : A →* L ι hi v₀ α :=
  (emb ι hi v₀ α).comp ((MonoidHom.inl N C).comp (ι v))
def e : MonoidAlgebra K (L ι hi v₀ α) := pushed (zHom ι hi v₀ α) ξ
def P (v : V) : MonoidAlgebra K (L ι hi v₀ α) := pushed (localHom ι hi v₀ α v) 1
def Q (v : V) : MonoidAlgebra K (L ι hi v₀ α) :=
  pushed (localHom ι hi v₀ α v₀) (ξ.comp (α v))⁻¹

def u (v : V) : MonoidAlgebra K (L ι hi v₀ α) :=
  MonoidAlgebra.of K _ (τ ι hi v₀ α v)
def uInv (v : V) : MonoidAlgebra K (L ι hi v₀ α) :=
  MonoidAlgebra.of K _ (τ ι hi v₀ α v)⁻¹

omit [Fintype A] [Fintype C] in
lemma uInv_mul_u (v : V) : uInv (K := K) ι hi v₀ α v * u ι hi v₀ α v = 1 := by
  simp [uInv, u, ← MonoidAlgebra.one_def]
omit [Fintype A] [Fintype C] in
lemma u_mul_uInv (v : V) : u (K := K) ι hi v₀ α v * uInv ι hi v₀ α v = 1 := by
  simp [uInv, u, ← MonoidAlgebra.one_def]

omit [Fintype A] in
lemma e_central (x : MonoidAlgebra K (L ι hi v₀ α)) : Commute (e ι hi v₀ α ξ) x :=
  pushed_central _ _ (central_cyclic ι hi v₀ α) x

omit [Fintype A] in
lemma cyclic_weight (n : N) (c : C) :
    e ι hi v₀ α ξ * MonoidAlgebra.of K _ (emb ι hi v₀ α (n,c)) =
      (ξ c : K) • (e ι hi v₀ α ξ * MonoidAlgebra.of K _ (emb ι hi v₀ α (n,1))) := by
  have hfac : emb ι hi v₀ α (n,c) =
      zHom ι hi v₀ α c * emb ι hi v₀ α (n,1) := by
    change _ = emb ι hi v₀ α (1,c) * _
    rw [← map_mul]
    congr 1
    ext <;> simp
  rw [hfac, map_mul, ← mul_assoc]
  rw [show e ι hi v₀ α ξ * MonoidAlgebra.of K _ (zHom ι hi v₀ α c) =
    (ξ c : K) • e ι hi v₀ α ξ from pushed_mul_single _ _ c]
  rw [smul_mul_assoc]

omit [Fintype A] [Fintype C] in
lemma twisted_single (v : V) (a : A) :
    u (K := K) ι hi v₀ α v * MonoidAlgebra.of K _ (localHom ι hi v₀ α v a) *
        uInv ι hi v₀ α v =
      MonoidAlgebra.of K _ (emb ι hi v₀ α (ι v₀ a, α v a)) := by
  simp only [u, uInv, localHom, MonoidHom.comp_apply, MonoidHom.inl_apply, ← map_mul]
  congr 1
  rw [conjugacy, mul_assoc, mul_inv_cancel, mul_one, one_mul]

lemma twisted_average (v : V) :
    e ι hi v₀ α ξ * (u ι hi v₀ α v * P (K := K) ι hi v₀ α v * uInv ι hi v₀ α v) =
      e ι hi v₀ α ξ * Q ι hi v₀ α ξ v := by
  unfold P Q
  rw [pushed_eq_sum, pushed_eq_sum]
  simp only [MonoidHom.one_apply, Units.val_one, inv_one, MonoidHom.inv_apply,
    MonoidHom.comp_apply, Units.val_inv_eq_inv_val, inv_inv]
  simp only [mul_smul_comm, smul_mul_assoc, Finset.mul_sum, Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  change e ι hi v₀ α ξ * (u ι hi v₀ α v * MonoidAlgebra.of K _ (localHom ι hi v₀ α v a) *
      uInv ι hi v₀ α v) = _
  rw [twisted_single, cyclic_weight]
  simp [localHom, MonoidAlgebra.of_apply, ← mul_smul_comm]

lemma conjugate_projection (v : V) :
    u ι hi v₀ α v * (e ι hi v₀ α ξ * P (K := K) ι hi v₀ α v) * uInv ι hi v₀ α v =
      e ι hi v₀ α ξ * Q ι hi v₀ α ξ v := by
  rw [← mul_assoc, (e_central ι hi v₀ α ξ (u ι hi v₀ α v)).eq.symm,
    mul_assoc, mul_assoc, ← mul_assoc (u ι hi v₀ α v)]
  exact twisted_average ι hi v₀ α ξ v

end KaplanskyCounterexample.CharacterTwist

end

end OAI
end
/- CHECKPOINT: OAI.RingTheory.DirectFiniteness.CharacterTwist -/

/- BEGIN PINNED MODULE OAI.RingTheory.DirectFiniteness.AlgebraicPacking -/
section

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6

noncomputable section
open scoped Classical
namespace KaplanskyCounterexample.AlgebraicPacking

variable {R : Type u_1} {m : Type u_2} {t : Type u_3} [Ring R] [Fintype m] [Fintype t]

def aMat (U : Matrix m t R) (J : Matrix t m R) (E : Matrix m m R) : Matrix m m R :=
  U * J + (1 - E)

def bMat (C : Matrix m t R) (T : Matrix t m R) (E : Matrix m m R) : Matrix m m R :=
  C * T + (1 - E)

theorem packing_identities
    (U C : Matrix m t R) (T J : Matrix t m R) (P F : Matrix t t R)
    (E : Matrix m m R)
    (hUP : U * P = U) (hPT : P * T = T) (hUT : U * T = 1)
    (hJC : J * C = F * P) (hEE : E * E = E) (hFF : F * F = F)
    (hEU : E * U = U * F) (hFT : F * T = T * E)
    (hJE : J * E = J) (hEC : E * C = C)
    (hCF : C * F = C) (hFJ : F * J = J) :
    aMat U J E * bMat C T E = 1 ∧
      J * (bMat C T E * aMat U J E - 1) * C = F * (T * U - P) := by
  have hUJCT : U * J * (C * T) = E := by
    calc
      U * J * (C * T) = U * (J * C) * T := by simp only [Matrix.mul_assoc]
      _ = U * (F * P) * T := by rw [hJC]
      _ = E * (U * (P * T)) := by rw [← Matrix.mul_assoc U, ← hEU]; simp only [Matrix.mul_assoc]
      _ = E := by rw [hPT, hUT, Matrix.mul_one]
  have hUJE : (U * J) * E = U * J := by rw [Matrix.mul_assoc, hJE]
  have hECT : E * (C * T) = C * T := by rw [← Matrix.mul_assoc, hEC]
  have hproj : (1 - E) * (1 - E) = 1 - E := by
    noncomm_ring [hEE]
  constructor
  · unfold aMat bMat
    rw [mul_add, add_mul, add_mul, hUJCT, mul_sub, Matrix.mul_one,
      hUJE, sub_self, sub_mul, Matrix.one_mul, hECT, sub_self, hproj]
    abel
  · have hCTE : C * T * E = C * T := by
      rw [Matrix.mul_assoc, ← hFT, ← Matrix.mul_assoc, hCF]
    have hEUJ : E * (U * J) = U * J := by
      rw [← Matrix.mul_assoc, hEU, Matrix.mul_assoc, hFJ]
    have hdelta : bMat C T E * aMat U J E - 1 = C * T * (U * J) - E := by
      unfold aMat bMat
      rw [mul_add, add_mul, add_mul, mul_sub, Matrix.mul_one, hCTE,
        sub_self, sub_mul, Matrix.one_mul, hEUJ, sub_self, hproj]
      abel
    have hsandwich : J * (C * T * (U * J)) * C = F * (T * U) := by
      calc
        J * (C * T * (U * J)) * C = (J * C) * T * U * (J * C) := by
          simp only [Matrix.mul_assoc]
        _ = (F * P) * T * U * (F * P) := by rw [hJC]
        _ = F * T * (U * F) * P := by
          rw [Matrix.mul_assoc F P T, hPT]
          simp only [Matrix.mul_assoc]
        _ = F * (T * E) * (U * P) := by
          rw [← hEU]
          simp only [Matrix.mul_assoc]
        _ = F * (F * T) * U := by rw [hUP, ← hFT]
        _ = F * (T * U) := by
          rw [← Matrix.mul_assoc F F T, hFF, Matrix.mul_assoc]
    rw [hdelta, Matrix.mul_sub, Matrix.sub_mul, hsandwich, hJE, hJC, Matrix.mul_sub]

/-- The rank defect used after specialization to the subgroup algebra. -/
theorem transpose_mul_ne_one {K : Type u_4} {m : Type u_5} {t : Type u_6} [Field K] [Fintype m] [Fintype t]
    (X : Matrix m t K) (hlt : Fintype.card m < Fintype.card t) :
    X.transpose * X ≠ 1 := by
  intro heq
  have h := (Matrix.rank_mul_le_right X.transpose X).trans (Matrix.rank_le_card_height X)
  rw [heq, Matrix.rank_one] at h
  omega

def Cpack (slot : t → m) (u D : t → R) : Matrix m t R :=
  fun i v => if slot v = i then u v * D v else 0

def Jpack (slot : t → m) (uInv D : t → R) : Matrix t m R :=
  fun v i => if slot v = i then D v * uInv v else 0

omit [Fintype t] in
lemma Jpack_mul_Cpack (slot : t → m) (u uInv D Q : t → R)
    (hlu : ∀ v, uInv v * u v = 1)
    (hD : ∀ v, D v * D v = D v)
    (hconj : ∀ v, u v * D v * uInv v = Q v)
    (horth : ∀ v w, v ≠ w → slot v = slot w → Q v * Q w = 0) :
    Jpack slot uInv D * Cpack slot u D = Matrix.diagonal D := by
  have hleft (v : t) : D v * uInv v = uInv v * Q v := by
    rw [← hconj, ← mul_assoc, ← mul_assoc, hlu, one_mul]
  have hright (v : t) : u v * D v = Q v * u v := by
    rw [← hconj, mul_assoc (u v * D v), hlu, mul_one]
  ext v w
  rw [Matrix.mul_apply]
  by_cases hvw : v = w
  · subst w
    rw [Matrix.diagonal_apply_eq]
    rw [Finset.sum_eq_single (slot v)]
    · simp only [Jpack, Cpack, ite_true]
      rw [mul_assoc, ← mul_assoc (uInv v), hlu, one_mul, hD]
    · intro i _ hi
      simp [Jpack, Cpack, Ne.symm hi]
    · simp
  · rw [Matrix.diagonal_apply_ne _ hvw]
    apply Finset.sum_eq_zero
    intro i _
    by_cases hvi : slot v = i <;> by_cases hwi : slot w = i <;>
      simp only [Jpack, Cpack, hvi, hwi, ite_true, ite_false, mul_zero, zero_mul]
    rw [hleft, hright, mul_assoc, ← mul_assoc (Q v), horth v w hvw (hvi.trans hwi.symm),
      zero_mul, mul_zero]

theorem square_of_projections (U : Matrix m t R) (T : Matrix t m R)
    (p q u uInv : t → R) (slot : t → m) (e : R)
    (he : e * e = e) (hc : ∀ x : R, Commute e x)
    (hp : ∀ v, p v * p v = p v)
    (hUP : U * Matrix.diagonal p = U) (hPT : Matrix.diagonal p * T = T)
    (hUT : U * T = 1)
    (hlu : ∀ v, uInv v * u v = 1)
    (hconj : ∀ v, u v * (e * p v) * uInv v = e * q v)
    (horth : ∀ v w, v ≠ w → slot v = slot w → q v * q w = 0)
    (hdefect : Matrix.diagonal (fun _ : t => e) * (T * U - Matrix.diagonal p) ≠ 0) :
    ∃ a b : Matrix m m R, a * b = 1 ∧ b * a ≠ 1 := by
  let D : t → R := fun v => e * p v
  let C := Cpack slot u D
  let J := Jpack slot uInv D
  let E : Matrix m m R := Matrix.diagonal (fun _ => e)
  let F : Matrix t t R := Matrix.diagonal (fun _ => e)
  have hD (v : t) : D v * D v = D v := by
    dsimp [D]
    calc
      e * p v * (e * p v) = e * (e * p v) * p v := by
        rw [mul_assoc, ← mul_assoc (p v), (hc (p v)).eq.symm]; simp only [mul_assoc]
      _ = e * p v := by rw [← mul_assoc e e, he, mul_assoc, hp]
  have horth' (v w : t) (hne : v ≠ w) (hs : slot v = slot w) :
      (e * q v) * (e * q w) = 0 := by
    calc
      e * q v * (e * q w) = (e * e) * (q v * q w) := by
        rw [mul_assoc, ← mul_assoc (q v), (hc (q v)).eq.symm]; simp only [mul_assoc]
      _ = 0 := by rw [horth v w hne hs, mul_zero]
  have hJC : J * C = F * Matrix.diagonal p := by
    rw [show F * Matrix.diagonal p = Matrix.diagonal D by
      simp [F, D, Matrix.diagonal_mul_diagonal]]
    exact Jpack_mul_Cpack slot u uInv D (fun v => e * q v) hlu hD hconj horth'
  have hEE : E * E = E := by simp [E, Matrix.diagonal_mul_diagonal, he]
  have hFF : F * F = F := by simp [F, Matrix.diagonal_mul_diagonal, he]
  have hEU : E * U = U * F := by
    ext i v
    simpa [E, F, Matrix.diagonal_mul, Matrix.mul_diagonal] using (hc (U i v)).eq
  have hFT : F * T = T * E := by
    ext v i
    simpa [E, F, Matrix.diagonal_mul, Matrix.mul_diagonal] using (hc (T v i)).eq
  have hC (i : m) (v : t) : e * C i v = C i v := by
    dsimp [C, Cpack, D]
    split_ifs
    · rw [← mul_assoc, (hc (u v)).eq, mul_assoc, ← mul_assoc e e, he]
    · exact mul_zero e
  have hJ (v : t) (i : m) : e * J v i = J v i := by
    dsimp [J, Jpack, D]
    split_ifs
    · rw [← mul_assoc, ← mul_assoc e e, he]
    · exact mul_zero e
  have hJE : J * E = J := by
    ext v i
    simp only [E, Matrix.mul_diagonal]
    rw [← (hc (J v i)).eq, hJ]
  have hEC : E * C = C := by ext i v; simpa [E, Matrix.diagonal_mul] using hC i v
  have hCF : C * F = C := by
    ext i v
    simp only [F, Matrix.mul_diagonal]
    rw [← (hc (C i v)).eq, hC]
  have hFJ : F * J = J := by ext v i; simpa [F, Matrix.diagonal_mul] using hJ v i
  obtain ⟨hab, hdelta⟩ := packing_identities U C T J (Matrix.diagonal p) F E
    hUP hPT hUT hJC hEE hFF hEU hFT hJE hEC hCF hFJ
  refine ⟨aMat U J E, bMat C T E, hab, ?_⟩
  intro hba
  apply hdefect
  rw [hba, sub_self, Matrix.mul_zero, Matrix.zero_mul] at hdelta
  exact hdelta.symm

end KaplanskyCounterexample.AlgebraicPacking

end

end OAI
end
/- CHECKPOINT: OAI.RingTheory.DirectFiniteness.AlgebraicPacking -/

/- BEGIN PINNED MODULE OAI.RingTheory.DirectFiniteness.Rectangular -/
section

namespace OAI

universe u_1 u_2 u_3 u_4 u_5

noncomputable section
open scoped BigOperators Classical
namespace KaplanskyCounterexample.Rectangular
variable {K : Type u_1} {R : Type u_2} {V : Type u_3} {F : Type u_4} {m : Type u_5} [CommRing K] [Ring R] [Algebra K R]
variable [Fintype V] [Fintype F] [Fintype m]

def U (X : Matrix m V K) (P : V → R) : Matrix m V R := fun i v => X i v • P v
def T (X : Matrix m V K) (P : V → R) : Matrix V m R := fun v i => X i v • P v

omit [Fintype m] in
theorem identities (X : Matrix m V K) (P : V → R) (L : F → R)
    (Inc : F → Finset V)
    (hP : ∀ v, P v * P v = P v)
    (hdec : ∀ v, P v = 1 + ∑ f : {f : F // v ∈ Inc f}, (L f - 1))
    (hglobal : X * X.transpose = 1)
    (hlocal : ∀ f i j, ∑ v ∈ Inc f, X i v * X j v = 0) :
    U X P * Matrix.diagonal P = U X P ∧
      Matrix.diagonal P * T X P = T X P ∧ U X P * T X P = 1 := by
  constructor
  · ext i v
    simp [U, Matrix.mul_diagonal, hP]
  constructor
  · ext v i
    simp [T, Matrix.diagonal_mul, hP]
  · ext i j
    change (∑ v, (X i v • P v) * (X j v • P v)) = (1 : Matrix m m R) i j
    simp_rw [smul_mul_smul_comm, hP, hdec, smul_add, Finset.smul_sum]
    rw [Finset.sum_add_distrib, ← Finset.sum_smul]
    have hh := congrFun (congrFun hglobal i) j
    change ∑ v, X i v * X j v = (1 : Matrix m m K) i j at hh
    rw [hh]
    have hzero : ∑ v : V, ∑ f : {f : F // v ∈ Inc f},
        (X i v * X j v) • (L f.val - 1) = 0 := by
      have hv (v : V) : (∑ f : {f : F // v ∈ Inc f},
          (X i v * X j v) • (L f.val - 1)) =
          ∑ f : F, if v ∈ Inc f then (X i v * X j v) • (L f - 1) else 0 := by
        rw [← Finset.sum_filter]
        exact (Finset.sum_subtype (p := fun f : F => v ∈ Inc f)
          (Finset.univ.filter (fun f : F => v ∈ Inc f)) (by simp)
          (fun f : F => (X i v * X j v) • (L f - 1))).symm
      simp_rw [hv]
      rw [Finset.sum_comm]
      apply Finset.sum_eq_zero
      intro f _
      rw [← Finset.sum_filter]
      have hf : Finset.univ.filter (fun v => v ∈ Inc f) = Inc f := by ext; simp
      rw [hf, ← Finset.sum_smul, hlocal, zero_smul]
    rw [hzero, add_zero]
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

end KaplanskyCounterexample.Rectangular
end

end OAI
end
/- CHECKPOINT: OAI.RingTheory.DirectFiniteness.Rectangular -/

#print axioms OAI.KaplanskyCounterexample.AssignedDevelopment.point_injective
#print axioms OAI.KaplanskyCounterexample.Rectangular.identities
#print axioms OAI.KaplanskyCounterexample.Prescription.Output.success
#print axioms OAI.KaplanskyCounterexample.Prescription.Output.X_global
#print axioms OAI.KaplanskyCounterexample.Prescription.Output.X_local
