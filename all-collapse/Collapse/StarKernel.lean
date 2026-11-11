module

public import Collapse.StarAction

/-!
# The kernel of a matrix over `K[N]` on a marker set

The action `⋆` of `N` on `D k` and the multiplicativity of `M ↦ starKernel k M`
(second part of the material for relation (S3); the definitions are in `Collapse.StarAction`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

open scoped Classical

namespace Collapse

open LocalSpace BernoulliIso

variable {N G X K I V : Type} [Group N] [Countable N] [Group G] [MulAction G X]
  [MeasurableSpace X] [BorelFree G X] [Field K] [Finite K] [MeasurableSpace K]
  [DiscreteCoeff K] [Fintype I] [Fintype V] [Nonempty I] [Nonempty V]

namespace MarkerTower

variable {τ : TowerSetting N G} {Jv : V → Subgroup N} {U : Set X}

section

variable (T : MarkerTower τ Jv U)

theorem ret_mem (k : ℕ) (x : X) (hx : x ∈ U) : T.ret k x ∈ T.D k := T.ret_mem' k hx

theorem ret_eq_self (k : ℕ) (x : X) (hx : x ∈ T.D k) : T.ret k x = x := T.ret_self k hx

theorem star_mem (k : ℕ) (n : N) (x : X) (hx : x ∈ U) : T.star k n x ∈ T.D k :=
  T.star_mem' k n hx

theorem star_one (k : ℕ) (x : X) (hx : x ∈ T.D k) : T.star k 1 x = x := T.star_one' k hx

theorem star_mul (k : ℕ) (n n' : N) (x : X) (hx : x ∈ U) :
    T.star k (n * n') x = T.star k n (T.star k n' x) := T.star_mul' k n n' hx

/-- A nontrivial element of `N` has no fixed point under `⋆`. -/
theorem star_free (k : ℕ) (n : N) (x : X) (hx : x ∈ T.D k) (h : T.star k n x = x) : n = 1 :=
  T.star_free' k n hx h

theorem starKernel_mul {A B C : Type} [Finite A] [Fintype B] [Finite C] (k : ℕ)
    (M : Matrix A B (MonoidAlgebra K N)) (M' : Matrix B C (MonoidAlgebra K N)) :
    T.starKernel K k (M * M') = (T.starKernel K k M).comp (T.starKernel K k M') := by
  refine LKernel.ext fun z w => ?_
  rw [LKernel.comp_toFun]
  by_cases hz : z.1 ∈ T.D k
  swap
  · rw [T.starKernel_apply_of_not_mem k _ hz]
    exact (finsum_eq_zero_of_forall_eq_zero fun y => by
      rw [T.starKernel_apply_of_not_mem k _ hz, zero_mul]).symm
  have hU := T.D_sub k hz
  by_cases hw : ∃ m, T.star k m⁻¹ z.1 = w.1
  swap
  · push_neg at hw
    rw [T.starKernel_apply_eq_zero k _ hw]
    refine (finsum_eq_zero_of_forall_eq_zero fun y => ?_).symm
    by_cases h1 : (T.starKernel K k M).toFun z y = 0
    · rw [h1, zero_mul]
    · obtain ⟨-, n, -, hn⟩ := starEntry_ne_zero T K k M z y h1
      rw [T.starKernel_apply_eq_zero k M' (z := y) (y := w) fun n' hn' => hw (n * n') ?_, mul_zero]
      rw [← hn', ← hn, ← T.star_mul' k _ _ hU, mul_inv_rev]
  obtain ⟨m, hm⟩ := hw
  obtain ⟨w1, w2⟩ := w
  dsimp only at hm
  subst hm
  rw [T.starKernel_apply_star k (M * M') hz]
  let e : (Σ _ : B, N) → X × B := fun p => (T.star k p.2⁻¹ z.1, p.1)
  have he : Function.Injective e := by
    rintro ⟨b, n⟩ ⟨b', n'⟩ h
    simp only [e, Prod.mk.injEq] at h
    obtain ⟨h1, rfl⟩ := h
    have := inv_injective (T.star_inj k hz h1)
    subst this
    rfl
  let P : Finset (Σ _ : B, N) := Finset.univ.sigma fun b => (M z.2 b).coeff.support
  rw [finsum_eq_sum_of_support_subset _ (s := P.image e) ?_]
  swap
  · intro y hy
    obtain ⟨-, n, hn, he'⟩ := starEntry_ne_zero T K k M z y (left_ne_zero_of_mul hy)
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
    exact ⟨⟨y.2, n⟩, Finset.mem_sigma.2 ⟨Finset.mem_univ _, hn⟩, Prod.ext he' rfl⟩
  rw [Finset.sum_image fun p _ q _ h => he h, Finset.sum_sigma, Matrix.mul_apply,
    MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [coeff_mul_inv]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp only [e]
  rw [T.starKernel_apply_star k M hz]
  have h2 : T.star k m⁻¹ z.1 = T.star k (n⁻¹ * m)⁻¹ (T.star k n⁻¹ z.1) := by
    rw [← T.star_mul' k _ _ hU]
    congr 1
    group
  rw [h2, T.starKernel_apply_star k M' (z := (T.star k n⁻¹ z.1, b)) (T.star_mem' k _ hU)]

theorem starKernel_one {A : Type} [Finite A] (k : ℕ) :
    T.starKernel K k (1 : Matrix A A (MonoidAlgebra K N)) =
      LKernel.diag (fun _ : A => T.D k) (fun _ => T.measurable_D k) := by
  refine LKernel.ext fun z w => ?_
  rw [LKernel.diag_toFun]
  by_cases hz : z.1 ∈ T.D k
  swap
  · rw [T.starKernel_apply_of_not_mem k _ hz, if_neg]
    rintro ⟨rfl, h⟩
    exact hz h
  by_cases hw : ∃ m, T.star k m⁻¹ z.1 = w.1
  swap
  · push_neg at hw
    rw [T.starKernel_apply_eq_zero k _ hw, if_neg]
    rintro ⟨rfl, -⟩
    exact hw 1 (by rw [inv_one, T.star_one' k hz])
  obtain ⟨m, hm⟩ := hw
  obtain ⟨w1, w2⟩ := w
  dsimp only at hm
  subst hm
  rw [T.starKernel_apply_star k _ hz]
  obtain ⟨z1, z2⟩ := z
  dsimp only at hz ⊢
  by_cases hm1 : m = 1
  · subst hm1
    simp only [inv_one, T.star_one' k hz, Matrix.one_apply, Prod.mk.injEq, true_and, hz, and_true]
    split_ifs <;> simp [MonoidAlgebra.one_def]
  · have hne : T.star k m⁻¹ z1 ≠ z1 := fun h => hm1 (inv_eq_one.1 (T.star_free' k _ hz h))
    rw [if_neg (by rintro ⟨h, -⟩; exact hne (congrArg Prod.fst h).symm), Matrix.one_apply]
    split_ifs
    · rw [MonoidAlgebra.one_def, MonoidAlgebra.coeff_single, Finsupp.single_apply,
        if_neg (Ne.symm hm1)]
    · simp

theorem starKernel_sub {A B : Type} [Finite A] [Finite B] (k : ℕ)
    (M M' : Matrix A B (MonoidAlgebra K N)) :
    T.starKernel K k (M - M') = T.starKernel K k M - T.starKernel K k M' := by
  refine LKernel.ext fun z w => ?_
  rw [LKernel.sub_toFun]
  simp only [starKernel_toFun]
  split_ifs with h
  · set s := (M z.2 w.2).coeff.support ∪ (M' z.2 w.2).coeff.support
    rw [sum_ite_support (M z.2 w.2) _ s Finset.subset_union_left,
      sum_ite_support (M' z.2 w.2) _ s Finset.subset_union_right,
      sum_ite_support ((M - M') z.2 w.2) _ s (by
        rw [Matrix.sub_apply, MonoidAlgebra.coeff_sub]; exact Finsupp.support_sub),
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [Matrix.sub_apply, MonoidAlgebra.coeff_sub, Finsupp.sub_apply]
    split_ifs <;> simp
  · rw [sub_zero]

/-- The `J v`-orbit of a point of `D k` under `⋆` meets `Dv k v`. -/
theorem exists_star_mem_Dv (k : ℕ) (v : V) {z : X} (hz : z ∈ T.D k) :
    ∃ m ∈ Jv v, T.star k m z ∈ T.Dv k v := by
  have hU := T.D_sub k hz
  obtain ⟨⟨u, hu⟩, hmem, -⟩ := T.Dv_trans k v z hU
  have hu' := hu
  rw [← τ.JHmul_range] at hu'
  obtain ⟨⟨a, h⟩, hah⟩ := hu'
  have e : τ.ι a * h = u := hah
  have hc : τ.ι a * h = h * τ.ι a := (τ.H_comm k h h.2 a).eq
  change u • z ∈ T.Dv k v at hmem
  rw [← e, hc, mul_smul] at hmem
  refine ⟨a, a.2, ?_⟩
  rw [star, T.ret_eq_of k (T.U_invariant _ _ hU) h.2 (T.Dv_sub k v hmem)]
  exact hmem

/-- The `J v`-orbit of a point of `D k` under `⋆` meets `Dv k v` at most once. -/
theorem star_eq_of_mem_Dv (k : ℕ) (v : V) {z : X} (hz : z ∈ T.D k) {m m' : N} (hm : m ∈ Jv v)
    (hm' : m' ∈ Jv v) (h1 : T.star k m z ∈ T.Dv k v) (h2 : T.star k m' z ∈ T.Dv k v) :
    T.star k m z = T.star k m' z := by
  have hU := T.D_sub k hz
  obtain ⟨g, hg, e, -⟩ := T.star_spec k m hU
  obtain ⟨g', hg', e', -⟩ := T.star_spec k m' hU
  have mem : ∀ {g : G} {n : N}, g ∈ τ.H k → n ∈ Jv v → g * τ.ι n ∈ τ.JH (Jv v) k :=
    fun hg hn => mul_mem (Subgroup.mem_sup_right hg)
      (Subgroup.mem_sup_left (Subgroup.mem_map_of_mem _ hn))
  rw [e] at h1 ⊢
  rw [e'] at h2 ⊢
  have := (T.Dv_trans k v z hU).unique (y₁ := ⟨_, mem hg hm⟩) (y₂ := ⟨_, mem hg' hm'⟩) h1 h2
  have h' : g * τ.ι m = g' * τ.ι m' := congrArg Subtype.val this
  rw [h']

theorem star_orbit_iff (k : ℕ) (v : V) {z : X} (hz : z ∈ T.D k) {m0 : N} (hm0 : m0 ∈ Jv v)
    (y : X) :
    (∃ m ∈ Jv v, T.star k m (T.star k m0 z) = y) ↔ ∃ m ∈ Jv v, T.star k m z = y := by
  have hU := T.D_sub k hz
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact ⟨m * m0, mul_mem hm hm0, T.star_mul' k _ _ hU⟩
  · rintro ⟨m, hm, rfl⟩
    refine ⟨m * m0⁻¹, mul_mem hm (inv_mem hm0), ?_⟩
    rw [← T.star_mul' k _ _ hU, inv_mul_cancel_right]

/-- `D k` is the disjoint union of the translates `m ⋆ Dv k v`, `m ∈ J v`. -/
def orbitEq (k : ℕ) (v : V) :
    Equidecomp τ.Λ (fun _ : Jv v => T.Dv k v) (fun _ : Unit => T.D k) where
  piece g j _ := {x | x ∈ T.Dv k v ∧ (g : G) • x ∈ T.D k ∧ ∃ h ∈ τ.H k, (g : G) = h * τ.ι j}
  measurable_piece g j _ := by
    have : {x | x ∈ T.Dv k v ∧ (g : G) • x ∈ T.D k ∧ ∃ h ∈ τ.H k, (g : G) = h * τ.ι j} =
        T.Dv k v ∩ ((fun x => (g : G) • x) ⁻¹' T.D k ∩
          {_x | ∃ h ∈ τ.H k, (g : G) = h * τ.ι j}) := rfl
    rw [this]
    exact (T.measurable_Dv k v).inter
      ((BorelFree.measurable_smul _ (T.measurable_D k)).inter (MeasurableSet.const _))
  piece_subset g j _ x hx := hx.1
  existsUnique_piece j x hx := by
    have hxU := T.D_sub k (T.Dv_sub k v hx)
    obtain ⟨h, hh, -, hm⟩ := T.star_spec k j hxU
    refine ⟨(⟨h * τ.ι j, mul_mem (τ.H_le_Λ k hh)
      (τ.range_le_Λ (MonoidHom.mem_range.2 ⟨_, rfl⟩))⟩, ()), ⟨hx, hm, h, hh, rfl⟩, ?_⟩
    rintro ⟨g, ⟨⟩⟩ ⟨-, hg, h', hh', hgh⟩
    have hU : τ.ι j • x ∈ U := T.U_invariant _ _ hxU
    have hm' : h • τ.ι j • x ∈ T.D k := by rwa [← mul_smul]
    have hg' : h' • τ.ι j • x ∈ T.D k := by rw [← mul_smul, ← hgh]; exact hg
    have := (T.D_trans k _ hU).unique (y₁ := ⟨h, hh⟩) (y₂ := ⟨h', hh'⟩) hm' hg'
    have hhh : h = h' := congrArg Subtype.val this
    refine Prod.ext (Subtype.ext ?_) rfl
    show (g : G) = h * τ.ι j
    rw [hgh, hhh]
  mapsTo g j _ x hx := hx.2.1
  existsUnique_source _ y hy := by
    have hU := T.D_sub k hy
    obtain ⟨⟨u, hu⟩, hmem, huniq⟩ := T.Dv_trans k v y hU
    have hu' := hu
    rw [← τ.JHmul_range] at hu'
    obtain ⟨⟨a, h⟩, hah⟩ := hu'
    have e : τ.ι a * h = u := hah
    change u • y ∈ T.Dv k v at hmem
    have hΛ : u⁻¹ ∈ τ.Λ := τ.JH_le_Λ (Jv v) k (inv_mem hu)
    refine ⟨(⟨u⁻¹, hΛ⟩, a⁻¹), ⟨?_, ?_, h⁻¹, inv_mem h.2, ?_⟩, ?_⟩
    · simpa [Subgroup.smul_def] using hmem
    · simpa [Subgroup.smul_def] using hy
    · show u⁻¹ = (h : G)⁻¹ * τ.ι ((a⁻¹ : Jv v) : N)
      rw [← e]
      simp
    · rintro ⟨g', j'⟩ ⟨h1, -, h', hh', hg'⟩
      have mem : (g' : G)⁻¹ ∈ τ.JH (Jv v) k := by
        rw [hg', mul_inv_rev, ← map_inv]
        exact mul_mem (Subgroup.mem_sup_left (Subgroup.mem_map_of_mem _ (inv_mem j'.2)))
          (Subgroup.mem_sup_right (inv_mem hh'))
      have h1' : ((⟨(g' : G)⁻¹, mem⟩ : τ.JH (Jv v) k) : G) • y ∈ T.Dv k v := by
        simpa [Subgroup.smul_def] using h1
      have hgu : (g' : G)⁻¹ = u := congrArg Subtype.val (huniq _ h1')
      have hgu' : (g' : G) = u⁻¹ := by rw [← hgu, inv_inv]
      refine Prod.ext (Subtype.ext hgu') (Subtype.ext ?_)
      have hι : τ.ι ((a : N)⁻¹ * (j' : N)⁻¹) = h * h' := by
        have e2 : h' = u⁻¹ * (τ.ι j')⁻¹ := by rw [← hgu', hg', mul_inv_cancel_right]
        rw [e2, ← e, map_mul, map_inv, map_inv]
        group
      have hmemH : τ.ι ((a : N)⁻¹ * (j' : N)⁻¹) ∈ τ.H k := by
        rw [hι]; exact mul_mem h.2 hh'
      have h3 := (Subgroup.disjoint_def.1 (τ.H_disjoint k)) hmemH
        (MonoidHom.mem_range.2 ⟨_, rfl⟩)
      have h4 : (a : N)⁻¹ * (j' : N)⁻¹ = 1 := τ.ι_injective (h3.trans (map_one τ.ι).symm)
      have h5 := mul_eq_one_iff_eq_inv.1 h4
      rw [inv_inv] at h5
      simp [h5]

end

end MarkerTower

end Collapse
