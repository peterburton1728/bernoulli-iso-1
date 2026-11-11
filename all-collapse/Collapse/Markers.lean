module

public import Collapse.Tower
public import Collapse.Equidecomp
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.Dynamics.Ergodic.MeasurePreserving

/-!
# Markers

The marker sets live in an
invariant measurable set `U` of a free Borel action; `D k` meets every `H k`-orbit in `U`
exactly once, `Dv k v` meets every `J_v H_k`-orbit exactly once, and the `D k` have empty
intersection. Such a tower exists after discarding a null set.
-/

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory

namespace Collapse

variable {N G X V : Type} [Group N] [Group G] [MulAction G X] [MeasurableSpace X]

/-- A tower of marker sets in the invariant set `U`, for the subgroups `Jv v` of `N`. -/
structure MarkerTower (τ : TowerSetting N G) (Jv : V → Subgroup N) (U : Set X) where
  U_measurable : MeasurableSet U
  U_invariant : ∀ (g : G) (x : X), x ∈ U → g • x ∈ U
  D : ℕ → Set X
  Dv : ℕ → V → Set X
  measurable_D : ∀ k, MeasurableSet (D k)
  measurable_Dv : ∀ k v, MeasurableSet (Dv k v)
  D_zero : D 0 = U
  D_anti : Antitone D
  D_sub : ∀ k, D k ⊆ U
  /-- `D k` meets every `H k`-orbit in `U` exactly once. -/
  D_trans : ∀ k, ∀ x ∈ U, ∃! h : τ.H k, (h : G) • x ∈ D k
  Dv_sub : ∀ k v, Dv k v ⊆ D k
  /-- `Dv k v` meets every `J_v H_k`-orbit in `U` exactly once. -/
  Dv_trans : ∀ k v, ∀ x ∈ U, ∃! u : τ.JH (Jv v) k, (u : G) • x ∈ Dv k v
  iInter_D : ⋂ k, D k = ∅

/-- If `S ⊆ U` meets every `F`-orbit in the invariant set `U` exactly once, then
`|F| μ S = μ U`. -/
theorem card_mul_measure_of_trans [BorelFree G X] (μ : Measure X)
    (hμ : ∀ g : G, MeasurePreserving (fun x : X => g • x) μ μ) (F : Subgroup G) [Finite F]
    (U S : Set X) (hS : MeasurableSet S) (hSU : S ⊆ U)
    (hUinv : ∀ (g : G) (x : X), x ∈ U → g • x ∈ U)
    (htrans : ∀ x ∈ U, ∃! h : F, (h : G) • x ∈ S) :
    (Nat.card F : ENNReal) * μ S = μ U := by
  have hset : U = ⋃ h : F, (fun x => (h : G) • x) ⁻¹' S := by
    ext x
    constructor
    · intro hx
      obtain ⟨h, hh, -⟩ := htrans x hx
      exact Set.mem_iUnion.2 ⟨h, hh⟩
    · intro hx
      obtain ⟨h, hh⟩ := Set.mem_iUnion.1 hx
      simpa using hUinv (h : G)⁻¹ _ (hSU hh)
  rw [hset, measure_iUnion]
  · simp_rw [(hμ _).measure_preimage hS.nullMeasurableSet]
    have := Fintype.ofFinite F
    rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      Nat.card_eq_fintype_card]
  · intro a b hab
    rw [Function.onFun, Set.disjoint_left]
    intro x ha hb
    have hx : x ∈ U := by simpa using hUinv (a : G)⁻¹ _ (hSU ha)
    exact hab ((htrans x hx).unique ha hb)
  · exact fun h => BorelFree.measurable_smul (h : G) hS

/-- The points minimizing `f` on their `F`-orbit. -/
def minT (f : X → ℝ) (F : Subgroup G) : Set X := {x | ∀ u ∈ F, f x ≤ f ((u : G) • x)}

theorem measurableSet_minT [BorelFree G X] {f : X → ℝ} (hf : Measurable f) (F : Subgroup G)
    [Finite F] : MeasurableSet (minT f F) := by
  have : minT f F = ⋂ u : F, {x | f x ≤ f ((u : G) • x)} := by
    ext x; simp [minT]
  rw [this]
  exact MeasurableSet.iInter fun u =>
    measurableSet_le hf (hf.comp (BorelFree.measurable_smul (u : G)))

theorem minT_anti {f : X → ℝ} {F F' : Subgroup G} (h : F ≤ F') : minT f F' ⊆ minT f F :=
  fun _ hx u hu => hx u (h hu)

theorem minT_unique [BorelFree G X] {f : X → ℝ} (hf : Function.Injective f) (F : Subgroup G)
    [Finite F] (x : X) : ∃! h : F, (h : G) • x ∈ minT f F := by
  obtain ⟨h, hh⟩ := Finite.exists_min (fun u : F => f ((u : G) • x))
  have hmem : (h : G) • x ∈ minT f F := by
    intro u hu
    have := hh ⟨u * h, F.mul_mem hu h.2⟩
    simpa [mul_smul] using this
  refine ⟨h, hmem, fun h' hh' => ?_⟩
  have h1 := hh' ((h : G) * (h' : G)⁻¹) (F.mul_mem h.2 (F.inv_mem h'.2))
  have h2 := hmem ((h' : G) * (h : G)⁻¹) (F.mul_mem h'.2 (F.inv_mem h.2))
  simp only [mul_smul, inv_smul_smul] at h1 h2
  have heq : (h' : G) • x = (h : G) • x := hf (le_antisymm h1 h2)
  have h3 : ((h : G)⁻¹ * h') • x = x := by rw [mul_smul, heq, inv_smul_smul]
  have h4 := BorelFree.free _ _ h3
  exact Subtype.ext (by rw [inv_mul_eq_one] at h4; exact h4.symm)

namespace MarkerTower

variable {τ : TowerSetting N G} {Jv : V → Subgroup N} {U : Set X}

/-- A marker tower restricts to a smaller invariant measurable set. -/
def restrict (T : MarkerTower τ Jv U) (U' : Set X) (hU' : MeasurableSet U') (hsub : U' ⊆ U)
    (hinv : ∀ (g : G) (x : X), x ∈ U' → g • x ∈ U') : MarkerTower τ Jv U' where
  U_measurable := hU'
  U_invariant := hinv
  D k := T.D k ∩ U'
  Dv k v := T.Dv k v ∩ U'
  measurable_D k := (T.measurable_D k).inter hU'
  measurable_Dv k v := (T.measurable_Dv k v).inter hU'
  D_zero := by
    show T.D 0 ∩ U' = U'
    rw [T.D_zero]; exact Set.inter_eq_right.2 hsub
  D_anti a b hab := Set.inter_subset_inter_left _ (T.D_anti hab)
  D_sub k := Set.inter_subset_right
  D_trans k x hx := by
    obtain ⟨h, hh, hu⟩ := T.D_trans k x (hsub hx)
    exact ⟨h, ⟨hh, hinv _ _ hx⟩, fun h' hh' => hu h' hh'.1⟩
  Dv_sub k v := Set.inter_subset_inter_left _ (T.Dv_sub k v)
  Dv_trans k v x hx := by
    obtain ⟨h, hh, hu⟩ := T.Dv_trans k v x (hsub hx)
    exact ⟨h, ⟨hh, hinv _ _ hx⟩, fun h' hh' => hu h' hh'.1⟩
  iInter_D := Set.subset_empty_iff.1 fun x hx => by
    rw [← T.iInter_D]; exact Set.mem_iInter.2 fun k => (Set.mem_iInter.1 hx k).1

/-- The measure of `D k` is `2⁻ᵏ` if `U` has full measure. -/
theorem measure_D [BorelFree G X] (T : MarkerTower τ Jv U) (μ : Measure X)
    [IsProbabilityMeasure μ] (hμ : ∀ g : G, MeasurePreserving (fun x : X => g • x) μ μ)
    (hU : μ Uᶜ = 0) (k : ℕ) : μ (T.D k) = ((2 : ENNReal) ^ k)⁻¹ := by
  have := τ.H_finite k
  have h := card_mul_measure_of_trans μ hμ (τ.H k) U (T.D k) (T.measurable_D k) (T.D_sub k)
    T.U_invariant (T.D_trans k)
  rw [(prob_compl_eq_zero_iff T.U_measurable).1 hU, τ.H_card] at h
  push_cast at h
  exact ENNReal.eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact h)

end MarkerTower

/-- Markers exist on an invariant set of full measure (the intersection of
the `D k` is null and is discarded). -/
theorem exists_markerTower [BorelFree G X] [StandardBorelSpace X] (τ : TowerSetting N G)
    (Jv : V → Subgroup N) (hJ : ∀ v, Finite (Jv v)) (μ : Measure X) [IsProbabilityMeasure μ]
    (hμ : ∀ g : G, MeasurePreserving (fun x : X => g • x) μ μ) :
    ∃ U : Set X, μ Uᶜ = 0 ∧ Nonempty (MarkerTower τ Jv U) := by
  have hGc : Countable G := BorelFree.countable (X := X)
  set f := embeddingReal X
  have hfm : Measurable f := measurable_embeddingReal X
  have hfi : Function.Injective f := (measurableEmbedding_embeddingReal X).injective
  have hHf := τ.H_finite
  have hJHf : ∀ k v, Finite (τ.JH (Jv v) k) := fun k v => by
    have := hJ v; exact τ.JH_finite (Jv v) k
  set Z := ⋂ k, minT f (τ.H k) with hZdef
  have hZ : MeasurableSet Z := MeasurableSet.iInter fun k => measurableSet_minT hfm _
  have hD₀ : ∀ k, μ (minT f (τ.H k)) = ((2 : ENNReal) ^ k)⁻¹ := fun k => by
    have h := card_mul_measure_of_trans μ hμ (τ.H k) Set.univ (minT f (τ.H k))
      (measurableSet_minT hfm _) (Set.subset_univ _) (fun _ _ _ => Set.mem_univ _)
      (fun x _ => minT_unique hfi _ x)
    rw [measure_univ, τ.H_card] at h
    push_cast at h
    exact ENNReal.eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact h)
  have hZ0 : μ Z = 0 := by
    by_contra hne
    obtain ⟨n, hn⟩ := ENNReal.exists_inv_two_pow_lt hne
    have := measure_mono (μ := μ) (Set.iInter_subset (fun k => minT f (τ.H k)) n)
    rw [hD₀, ENNReal.inv_pow] at this
    exact absurd (this.trans_lt hn) (lt_irrefl _)
  set U := {x : X | ∀ g : G, g • x ∉ Z} with hUdef
  have hUeq : U = ⋂ g : G, (fun x => g • x) ⁻¹' Zᶜ := by ext x; simp [U]
  have hUm : MeasurableSet U := by
    rw [hUeq]; exact MeasurableSet.iInter fun g => BorelFree.measurable_smul g hZ.compl
  have hUinv : ∀ (g : G) (x : X), x ∈ U → g • x ∈ U := by
    intro g x hx g'
    rw [← mul_smul]; exact hx _
  have hUc : μ Uᶜ = 0 := by
    rw [hUeq, Set.compl_iInter]
    refine measure_iUnion_null fun g => ?_
    rw [← Set.preimage_compl, compl_compl, (hμ g).measure_preimage hZ.nullMeasurableSet, hZ0]
  have hD0 : minT f (τ.H 0) = Set.univ := by
    ext x
    simp only [minT, τ.H_zero, Subgroup.mem_bot, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    rintro u rfl; simp
  refine ⟨U, hUc, ⟨{
    U_measurable := hUm
    U_invariant := hUinv
    D := fun k => minT f (τ.H k) ∩ U
    Dv := fun k v => minT f (τ.JH (Jv v) k) ∩ U
    measurable_D := fun k => (measurableSet_minT hfm _).inter hUm
    measurable_Dv := fun k v => by
      have := hJHf k v; exact (measurableSet_minT hfm _).inter hUm
    D_zero := by simp only [hD0, Set.univ_inter]
    D_anti := fun a b hab => Set.inter_subset_inter_left _ (minT_anti (τ.H_mono hab))
    D_sub := fun k => Set.inter_subset_right
    D_trans := fun k x hx => by
      obtain ⟨h, hh, hu⟩ := minT_unique hfi (τ.H k) x
      exact ⟨h, ⟨hh, hUinv _ _ hx⟩, fun h' hh' => hu h' hh'.1⟩
    Dv_sub := fun k v => Set.inter_subset_inter_left _ (minT_anti (τ.H_le_JH _ _))
    Dv_trans := fun k v x hx => by
      have := hJHf k v
      obtain ⟨h, hh, hu⟩ := minT_unique hfi (τ.JH (Jv v) k) x
      exact ⟨h, ⟨hh, hUinv _ _ hx⟩, fun h' hh' => hu h' hh'.1⟩
    iInter_D := Set.subset_empty_iff.1 fun x hx => by
      have hx' := Set.mem_iInter.1 hx
      exact (hx' 0).2 1 (by rw [one_smul]; exact Set.mem_iInter.2 fun k => (hx' k).1) }⟩⟩

end Collapse
