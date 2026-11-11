module

public import Collapse.Relations
public import BernoulliIso.AlgebraicInput

/-!
# The transform on a marker set: relation (S3)

The transform and relation (S3), in the form of
the registered `AlgebraicInput`: matrices `U`, `T` over `K[N]` and the averages `p v`.

`N` acts on `D k` by `n ⋆ z = ` the point of `H k • (n • z)` in `D k`. A matrix `M` over `K[N]`
acts on functions on `D k × B` by `(M φ)(z, a) = ∑ b, ∑ n, M a b n * φ (n⁻¹ ⋆ z, b)`; this is
the kernel `starKernel k M`, and `M ↦ starKernel k M` is multiplicative.
-/

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

open scoped Classical

namespace Collapse

open LocalSpace BernoulliIso

/-- The identity equidecomposition of a set with levels `A j`. -/
def Equidecomp.refl' {Λ' Y J : Type} [Group Λ'] [MulAction Λ' Y] [MeasurableSpace Y]
    (A : J → Set Y) (hA : ∀ j, MeasurableSet (A j)) : Equidecomp Λ' A A where
  piece g j j' := {x | g = 1 ∧ j = j' ∧ x ∈ A j}
  measurable_piece g j j' := by
    by_cases h : g = 1 ∧ j = j'
    · obtain ⟨rfl, rfl⟩ := h
      simpa using hA j
    · convert MeasurableSet.empty
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact fun h' => h ⟨h'.1, h'.2.1⟩
  piece_subset _ _ _ _ hx := hx.2.2
  existsUnique_piece j x hx := by
    refine ⟨(1, j), ⟨rfl, rfl, hx⟩, ?_⟩
    rintro ⟨g, j'⟩ ⟨rfl, rfl, -⟩
    rfl
  mapsTo g j j' x hx := by
    obtain ⟨rfl, rfl, hx⟩ := hx
    simpa using hx
  existsUnique_source j' y hy := by
    refine ⟨(1, j'), ⟨rfl, rfl, by simpa using hy⟩, ?_⟩
    rintro ⟨g, j⟩ ⟨rfl, rfl, -⟩
    rfl

theorem sum_const_card {M : Type*} [SigmaMonoid M] {ι : Type} [Fintype ι] (a : M) :
    SigmaMonoid.sum (fun _ : ι => a) = Fintype.card ι • a := by
  rw [SigmaMonoid.nsmul_def]
  exact SigmaMonoid.sum_equiv (Fintype.equivFin ι) (fun _ => a)

theorem sum_const_natCard {M : Type*} [SigmaMonoid M] {ι : Type} [Finite ι] (a : M) :
    SigmaMonoid.sum (fun _ : ι => a) = Nat.card ι • a := by
  rw [SigmaMonoid.nsmul_def]
  exact SigmaMonoid.sum_equiv (Finite.equivFin ι) (fun _ => a)

section KernelAux

variable {Λ' Y R : Type} [Group Λ'] [MulAction Λ' Y] [MeasurableSpace Y] [BorelFree Λ' Y]
  [Ring R] [MeasurableSpace R] [DiscreteCoeff R] {J J' J₂ : Type}

theorem nsmul_toFun (n : ℕ) (c : LKernel Λ' Y R J J') (b : Y × J') (a : Y × J) :
    (n • c).toFun b a = n • c.toFun b a := rfl

theorem nsmul_comp [Countable J'] (n : ℕ) (c : LKernel Λ' Y R J' J₂) (d : LKernel Λ' Y R J J') :
    (n • c).comp d = n • c.comp d := by
  induction n with
  | zero => rw [zero_nsmul, zero_nsmul, LKernel.zero_comp]
  | succ n ih => rw [succ_nsmul, succ_nsmul, LKernel.add_comp, ih]

theorem comp_nsmul [Countable J'] (n : ℕ) (c : LKernel Λ' Y R J' J₂) (d : LKernel Λ' Y R J J') :
    c.comp (n • d) = n • c.comp d := by
  induction n with
  | zero => rw [zero_nsmul, zero_nsmul, LKernel.comp_zero]
  | succ n ih => rw [succ_nsmul, succ_nsmul, LKernel.comp_add, ih]

theorem diag_comp_apply [Countable J'] (A : J' → Set Y) (hA : ∀ j, MeasurableSet (A j))
    (c : LKernel Λ' Y R J J') (b : Y × J') (a : Y × J) :
    ((LKernel.diag A hA).comp c).toFun b a = if b.1 ∈ A b.2 then c.toFun b a else 0 := by
  rw [LKernel.comp_toFun, finsum_eq_single _ b fun w hw => by
    rw [LKernel.diag_toFun, if_neg (fun h => hw h.1.symm), zero_mul]]
  rw [LKernel.diag_toFun]
  by_cases h : b.1 ∈ A b.2 <;> simp [h]

theorem comp_diag_apply [Countable J'] (A : J' → Set Y) (hA : ∀ j, MeasurableSet (A j))
    (c : LKernel Λ' Y R J' J₂) (b : Y × J₂) (a : Y × J') :
    (c.comp (LKernel.diag A hA)).toFun b a = if a.1 ∈ A a.2 then c.toFun b a else 0 := by
  rw [LKernel.comp_toFun, finsum_eq_single _ a fun w hw => by
    rw [LKernel.diag_toFun, if_neg (fun h => hw h.1), mul_zero]]
  rw [LKernel.diag_toFun]
  by_cases h : a.1 ∈ A a.2 <;> simp [h]

theorem diag_idem [Countable J'] (A : J' → Set Y) (hA : ∀ j, MeasurableSet (A j)) :
    (LKernel.diag (Λ := Λ') (K := R) A hA).comp (LKernel.diag A hA) = LKernel.diag A hA := by
  refine LKernel.ext fun b a => ?_
  rw [diag_comp_apply, LKernel.diag_toFun]
  by_cases h : b.1 ∈ A b.2
  · rw [if_pos h]
  · rw [if_neg h, if_neg]
    rintro ⟨rfl, h'⟩
    exact h h'

end KernelAux

variable {N G X K I V : Type} [Group N] [Countable N] [Group G] [MulAction G X]
  [MeasurableSpace X] [BorelFree G X] [Field K] [Finite K] [MeasurableSpace K]
  [DiscreteCoeff K] [Fintype I] [Fintype V] [Nonempty I] [Nonempty V]

theorem coeff_mul_inv {R : Type} [Ring R] (x y : MonoidAlgebra R N) (m : N) :
    (x * y).coeff m = ∑ n ∈ x.coeff.support, x.coeff n * y.coeff (n⁻¹ * m) := by
  rw [MonoidAlgebra.coeff_mul, Finsupp.sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Finsupp.sum]
  simp_rw [← eq_inv_mul_iff_mul_eq]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [Finsupp.notMem_support_iff.1 h, mul_zero]

theorem sum_ite_support {R : Type} [Ring R] (f : MonoidAlgebra R N) (p : N → Prop) (s : Finset N)
    (hs : f.coeff.support ⊆ s) :
    ∑ n ∈ f.coeff.support, (if p n then f.coeff n else 0) =
      ∑ n ∈ s, (if p n then f.coeff n else 0) :=
  Finset.sum_subset hs fun n _ hn => by rw [Finsupp.notMem_support_iff.1 hn, ite_self]

namespace MarkerTower

variable {τ : TowerSetting N G} {Jv : V → Subgroup N} {U : Set X}

/-- The point of the `H k`-orbit of `x` in `D k`, for `x ∈ U`; `x` itself otherwise. -/
def ret (T : MarkerTower τ Jv U) (k : ℕ) (x : X) : X :=
  if hx : x ∈ U then ((T.D_trans k x hx).exists.choose : G) • x else x

/-- The action `⋆` of `N` on `D k`. -/
def star (T : MarkerTower τ Jv U) (k : ℕ) (n : N) (x : X) : X := T.ret k (τ.ι n • x)

theorem ret_eq_of (T : MarkerTower τ Jv U) (k : ℕ) {x : X} (hx : x ∈ U) {g : G}
    (hg : g ∈ τ.H k) (hgx : g • x ∈ T.D k) : T.ret k x = g • x := by
  unfold ret
  rw [dif_pos hx]
  have := (T.D_trans k x hx).unique (T.D_trans k x hx).exists.choose_spec (y₂ := ⟨g, hg⟩) hgx
  rw [this]

theorem ret_spec (T : MarkerTower τ Jv U) (k : ℕ) {x : X} (hx : x ∈ U) :
    ∃ h ∈ τ.H k, T.ret k x = h • x ∧ h • x ∈ T.D k := by
  refine ⟨_, ((T.D_trans k x hx).exists.choose).2, ?_, (T.D_trans k x hx).exists.choose_spec⟩
  unfold ret
  rw [dif_pos hx]

theorem ret_mem' (T : MarkerTower τ Jv U) (k : ℕ) {x : X} (hx : x ∈ U) : T.ret k x ∈ T.D k := by
  obtain ⟨h, -, e, hm⟩ := T.ret_spec k hx
  rw [e]
  exact hm

theorem ret_smul (T : MarkerTower τ Jv U) (k : ℕ) {x : X} (hx : x ∈ U) {h : G}
    (hh : h ∈ τ.H k) : T.ret k (h • x) = T.ret k x := by
  obtain ⟨h0, hh0, e, hm⟩ := T.ret_spec k hx
  have key : (h0 * h⁻¹) • h • x = h0 • x := by rw [← mul_smul, inv_mul_cancel_right]
  rw [e, T.ret_eq_of k (T.U_invariant h x hx) (mul_mem hh0 (inv_mem hh)) (by rw [key]; exact hm),
    key]

theorem ret_self (T : MarkerTower τ Jv U) (k : ℕ) {x : X} (hx : x ∈ T.D k) : T.ret k x = x :=
  (T.ret_eq_of k (T.D_sub k hx) (one_mem _) (by rwa [one_smul])).trans (one_smul _ _)

theorem star_spec (T : MarkerTower τ Jv U) (k : ℕ) (n : N) {x : X} (hx : x ∈ U) :
    ∃ h ∈ τ.H k, T.star k n x = (h * τ.ι n) • x ∧ (h * τ.ι n) • x ∈ T.D k := by
  obtain ⟨h, hh, e, hm⟩ := T.ret_spec k (T.U_invariant (τ.ι n) x hx)
  exact ⟨h, hh, by rw [star, e, mul_smul], by rw [mul_smul]; exact hm⟩

theorem star_mem' (T : MarkerTower τ Jv U) (k : ℕ) (n : N) {x : X} (hx : x ∈ U) :
    T.star k n x ∈ T.D k :=
  T.ret_mem' k (T.U_invariant _ _ hx)

theorem star_mul' (T : MarkerTower τ Jv U) (k : ℕ) (n n' : N) {x : X} (hx : x ∈ U) :
    T.star k (n * n') x = T.star k n (T.star k n' x) := by
  obtain ⟨h, hh, e, -⟩ := T.ret_spec k (T.U_invariant (τ.ι n') x hx)
  have hx' : τ.ι n • τ.ι n' • x ∈ U := T.U_invariant _ _ (T.U_invariant _ _ hx)
  simp only [star]
  rw [e, ← mul_smul (τ.ι n) h, (τ.H_comm k h hh n).eq, mul_smul, T.ret_smul k hx' hh, map_mul,
    mul_smul]

theorem star_one' (T : MarkerTower τ Jv U) (k : ℕ) {x : X} (hx : x ∈ T.D k) :
    T.star k 1 x = x := by
  simp only [star, map_one, one_smul]
  exact T.ret_self k hx

theorem star_free' (T : MarkerTower τ Jv U) (k : ℕ) (n : N) {x : X} (hx : x ∈ T.D k)
    (hst : T.star k n x = x) : n = 1 := by
  obtain ⟨h, hh, e, -⟩ := T.star_spec k n (T.D_sub k hx)
  rw [e] at hst
  have h1 := BorelFree.free _ _ hst
  have h2 : τ.ι n ∈ τ.H k := by
    rw [eq_inv_of_mul_eq_one_right h1]
    exact inv_mem hh
  have h3 := (Subgroup.disjoint_def.1 (τ.H_disjoint k)) h2 (MonoidHom.mem_range.2 ⟨n, rfl⟩)
  exact τ.ι_injective (h3.trans (map_one τ.ι).symm)

theorem star_inj (T : MarkerTower τ Jv U) (k : ℕ) {z : X} (hz : z ∈ T.D k) {a b : N}
    (h : T.star k a z = T.star k b z) : a = b := by
  have hu := T.D_sub k hz
  have : T.star k (b⁻¹ * a) z = z := by
    rw [T.star_mul' k _ _ hu, h, ← T.star_mul' k _ _ hu, inv_mul_cancel, T.star_one' k hz]
  exact (inv_mul_eq_one.1 (T.star_free' k _ hz this)).symm

theorem measurableSet_star_eq (T : MarkerTower τ Jv U) (k : ℕ) (u : N) (g : G) :
    MeasurableSet {x | T.star k u x = g • x} := by
  have e : {x | T.star k u x = g • x} =
      (U ∩ ⋃ h : τ.H k, (fun x => ((h : G) * τ.ι u) • x) ⁻¹' T.D k ∩
        {_x | (h : G) * τ.ι u = g}) ∪ (Uᶜ ∩ {_x | τ.ι u = g}) := by
    ext x
    by_cases hx : x ∈ U
    · simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_inter_iff, Set.mem_iUnion,
        Set.mem_preimage, Set.mem_compl_iff, hx, true_and, not_true_eq_false, false_and, or_false]
      constructor
      · intro hst
        obtain ⟨h, hh, e, hm⟩ := T.star_spec k u hx
        refine ⟨⟨h, hh⟩, hm, ?_⟩
        rw [e] at hst
        have := BorelFree.free (g⁻¹ * (h * τ.ι u)) x (by rw [mul_smul, hst, inv_smul_smul])
        exact (inv_mul_eq_one.1 this).symm
      · rintro ⟨⟨h, hh⟩, hm, rfl⟩
        simp only [star]
        rw [T.ret_eq_of k (T.U_invariant _ _ hx) hh (by rwa [← mul_smul]), mul_smul]
    · have hux : τ.ι u • x ∉ U := fun h => hx (by simpa using T.U_invariant (τ.ι u)⁻¹ _ h)
      have hs : T.star k u x = τ.ι u • x := by simp only [star, ret, dif_neg hux]
      simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff, hx,
        false_and, not_false_eq_true, true_and, false_or, hs]
      constructor
      · intro h
        have := BorelFree.free (g⁻¹ * τ.ι u) x (by rw [mul_smul, h, inv_smul_smul])
        exact (inv_mul_eq_one.1 this).symm
      · intro h
        rw [h]
  rw [e]
  have := τ.H_finite k
  refine (T.U_measurable.inter (MeasurableSet.iUnion fun h => ?_)).union
    (T.U_measurable.compl.inter (MeasurableSet.const _))
  exact (BorelFree.measurable_smul _ (T.measurable_D k)).inter (MeasurableSet.const _)

theorem starEntry_ne_zero (T : MarkerTower τ Jv U) (R : Type) [Ring R] {A B : Type} (k : ℕ)
    (M : Matrix A B (MonoidAlgebra R N)) (z : X × A) (y : X × B)
    (h : (if z.1 ∈ T.D k ∧ y.1 ∈ T.D k then
      ∑ n ∈ (M z.2 y.2).coeff.support, if T.star k n⁻¹ z.1 = y.1 then (M z.2 y.2).coeff n else 0
      else 0) ≠ 0) :
    z.1 ∈ T.D k ∧ ∃ n ∈ (M z.2 y.2).coeff.support, T.star k n⁻¹ z.1 = y.1 := by
  split_ifs at h with hc
  · obtain ⟨n, hn, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    refine ⟨hc.1, n, hn, ?_⟩
    by_contra hc'
    exact hne (if_neg hc')
  · exact absurd rfl h

/-- The kernel on `D k` of a matrix over `K[N]`, from `X × B` to `X × A`. The index types are
finite, so that the rows and columns of the kernel are finite. -/
def starKernel (T : MarkerTower τ Jv U) (K : Type) [Ring K] [MeasurableSpace K]
    [DiscreteCoeff K] {A B : Type} [Finite A] [Finite B] (k : ℕ)
    (M : Matrix A B (MonoidAlgebra K N)) : LKernel τ.Λ X K B A where
  toFun z y :=
    if z.1 ∈ T.D k ∧ y.1 ∈ T.D k then
      ∑ n ∈ (M z.2 y.2).coeff.support, if T.star k n⁻¹ z.1 = y.1 then (M z.2 y.2).coeff n else 0
    else 0
  rel z y h := by
    obtain ⟨hz, n, -, hn⟩ := starEntry_ne_zero T K k M z y h
    obtain ⟨g, hg, e, -⟩ := T.star_spec k n⁻¹ (T.D_sub k hz)
    refine ⟨⟨(g * τ.ι n⁻¹)⁻¹, inv_mem (mul_mem (τ.H_le_Λ k hg)
      (τ.range_le_Λ (MonoidHom.mem_range.2 ⟨_, rfl⟩)))⟩, ?_⟩
    show (g * τ.ι n⁻¹)⁻¹ • y.1 = z.1
    rw [← hn, e, inv_smul_smul]
  rowFinite z := by
    refine (Set.finite_iUnion fun b : B => ((M z.2 b).coeff.support.finite_toSet.image
      fun n => (T.star k n⁻¹ z.1, b))).subset ?_
    intro y hy
    obtain ⟨-, n, hn, he⟩ := starEntry_ne_zero T K k M z y hy
    exact Set.mem_iUnion.2 ⟨y.2, n, hn, Prod.ext he rfl⟩
  colFinite y := by
    refine (Set.finite_iUnion fun a : A => ((M a y.2).coeff.support.finite_toSet.image
      fun n => (T.star k n y.1, a))).subset ?_
    intro z hz
    obtain ⟨hz1, n, hn, he⟩ := starEntry_ne_zero T K k M z y hz
    refine Set.mem_iUnion.2 ⟨z.2, n, hn, Prod.ext ?_ rfl⟩
    show T.star k n y.1 = z.1
    rw [← he, ← T.star_mul' k _ _ (T.D_sub k hz1), mul_inv_cancel, T.star_one' k hz1]
  measurable g a b := by
    have : MeasurableAdd₂ K := ⟨measurable_of_countable (fun p : K × K => p.1 + p.2)⟩
    refine Measurable.ite ((T.measurable_D k).inter
      (BorelFree.measurable_smul g (T.measurable_D k))) ?_ measurable_const
    show Measurable fun x => ∑ n ∈ (M a b).coeff.support,
      if T.star k n⁻¹ x = (g : G) • x then (M a b).coeff n else 0
    exact Finset.measurable_sum _ fun n _ =>
      Measurable.ite (T.measurableSet_star_eq k n⁻¹ (g : G)) measurable_const measurable_const

section StarKernelAux

variable (T : MarkerTower τ Jv U) {R : Type} [Ring R] [MeasurableSpace R] [DiscreteCoeff R]
  {A B : Type} [Finite A] [Finite B] (k : ℕ)

theorem starKernel_toFun (M : Matrix A B (MonoidAlgebra R N)) (z : X × A) (y : X × B) :
    (T.starKernel R k M).toFun z y =
      if z.1 ∈ T.D k ∧ y.1 ∈ T.D k then
        ∑ n ∈ (M z.2 y.2).coeff.support,
          if T.star k n⁻¹ z.1 = y.1 then (M z.2 y.2).coeff n else 0
      else 0 := rfl

theorem starKernel_apply_of_not_mem (M : Matrix A B (MonoidAlgebra R N)) {z : X × A}
    (hz : z.1 ∉ T.D k) (y : X × B) : (T.starKernel R k M).toFun z y = 0 := by
  rw [starKernel_toFun, if_neg (fun h => hz h.1)]

theorem starKernel_apply_eq_zero (M : Matrix A B (MonoidAlgebra R N)) {z : X × A} {y : X × B}
    (h : ∀ n : N, T.star k n⁻¹ z.1 ≠ y.1) : (T.starKernel R k M).toFun z y = 0 := by
  by_contra hne
  obtain ⟨-, n, -, hn⟩ := starEntry_ne_zero T R k M z y hne
  exact h n hn

theorem starKernel_apply_star (M : Matrix A B (MonoidAlgebra R N)) {z : X × A}
    (hz : z.1 ∈ T.D k) (m : N) (b : B) :
    (T.starKernel R k M).toFun z (T.star k m⁻¹ z.1, b) = (M z.2 b).coeff m := by
  simp only [starKernel_toFun]
  rw [if_pos ⟨hz, T.star_mem' k _ (T.D_sub k hz)⟩, Finset.sum_eq_single m]
  · rw [if_pos rfl]
  · intro n _ hn
    rw [if_neg]
    intro h
    exact hn (inv_injective (T.star_inj k hz h))
  · intro hm
    rw [if_pos rfl]
    exact Finsupp.notMem_support_iff.1 hm

end StarKernelAux

end MarkerTower

end Collapse
