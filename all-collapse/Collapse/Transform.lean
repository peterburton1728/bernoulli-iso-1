module

public import Collapse.StarKernel

/-!
# The transform on a marker set: relation (S3)

The transform and relation (S3), in the form of
the registered `AlgebraicInput`: matrices `U`, `T` over `K[N]` and the averages `p v`. The
action `⋆`, the kernel `starKernel` and its multiplicativity are in `Collapse.StarAction` and
`Collapse.StarKernel`.
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

variable (s : AlgebraicInput K N I V) (T : MarkerTower τ s.J U)

/-- The local space `(D k × V, Π)`, where `Π` is the kernel of `diagonal p`: on the level `v` it
averages over the `⋆`-orbits of `J v`. -/
def avgSpace (k : ℕ) : LocalSpace τ.Λ X K where
  J := V
  e := T.starKernel K k (Matrix.diagonal s.p)
  idem := by rw [← T.starKernel_mul, s.PP]

theorem p_coeff (v : V) (m : N) :
    (s.p v).coeff m = if m ∈ s.J v then (s.κ : K)⁻¹ else 0 := by
  letI := s.finiteJ v
  letI := Fintype.ofFinite (s.J v)
  rw [s.p_average v, MonoidAlgebra.coeff_smul_apply, MonoidAlgebra.coeff_sum,
    Finsupp.finsetSum_apply]
  simp only [MonoidAlgebra.coeff_single, Finsupp.single_apply]
  split_ifs with hm
  · rw [Finset.sum_eq_single ⟨m, hm⟩ (fun g _ hg => if_neg fun h => hg (Subtype.ext h))
      (fun h => absurd (Finset.mem_univ _) h), if_pos rfl, smul_eq_mul, mul_one]
  · rw [Finset.sum_eq_zero fun g _ => if_neg fun h => hm (by rw [← h]; exact g.2), smul_zero]

theorem avg_toFun (k : ℕ) {z : X} (hz : z ∈ T.D k) (v v' : V) (y : X) :
    (T.starKernel K k (Matrix.diagonal s.p)).toFun (z, v) (y, v') =
      if v = v' ∧ ∃ m ∈ s.J v, T.star k m z = y then (s.κ : K)⁻¹ else 0 := by
  by_cases hy : ∃ m, T.star k m⁻¹ z = y
  · obtain ⟨m, rfl⟩ := hy
    rw [T.starKernel_apply_star k _ (z := (z, v)) hz]
    by_cases hv : v = v'
    · subst hv
      rw [Matrix.diagonal_apply_eq, p_coeff]
      have : (∃ m' ∈ s.J v, T.star k m' z = T.star k m⁻¹ z) ↔ m ∈ s.J v :=
        ⟨fun ⟨m', hm', h⟩ => by rw [T.star_inj k hz h] at hm'; exact inv_mem_iff.1 hm',
          fun h => ⟨_, inv_mem h, rfl⟩⟩
      simp only [true_and, this]
    · rw [Matrix.diagonal_apply_ne _ hv, if_neg (fun h => hv h.1)]
      simp
  · push_neg at hy
    rw [T.starKernel_apply_eq_zero k _ (z := (z, v)) (y := (y, v')) hy, if_neg]
    rintro ⟨-, m, -, rfl⟩
    exact hy m⁻¹ (by rw [inv_inv])

theorem avg_R_avg (k : ℕ) :
    s.κ • (T.starKernel K k (Matrix.diagonal s.p)).comp
      ((LKernel.diag (fun v => T.Dv k v) (T.measurable_Dv k)).comp
        (T.starKernel K k (Matrix.diagonal s.p))) =
      T.starKernel K k (Matrix.diagonal s.p) := by
  refine LKernel.ext fun b a => ?_
  rw [nsmul_toFun, LKernel.comp_toFun]
  obtain ⟨z, v⟩ := b
  by_cases hz : z ∈ T.D k
  swap
  · simp only [T.starKernel_apply_of_not_mem k (Matrix.diagonal s.p)
      (show (z, v).1 ∉ T.D k from hz), zero_mul, finsum_zero, smul_zero]
  obtain ⟨m0, hm0, hD⟩ := T.exists_star_mem_Dv k v hz
  rw [finsum_eq_single _ (T.star k m0 z, v) ?_]
  · rw [diag_comp_apply, if_pos hD, T.avg_toFun s k hz, if_pos ⟨rfl, m0, hm0, rfl⟩]
    obtain ⟨y, v'⟩ := a
    rw [T.avg_toFun s k (T.star_mem' k _ (T.D_sub k hz)), T.avg_toFun s k hz,
      T.star_orbit_iff k v hz hm0]
    split_ifs
    · rw [nsmul_eq_mul, ← mul_assoc, mul_inv_cancel₀ s.κ_ne_zero, one_mul]
    · simp
  · rintro ⟨y, v'⟩ hw
    rw [diag_comp_apply]
    split_ifs with hy
    · rw [T.avg_toFun s k hz]
      split_ifs with hc
      · exfalso
        obtain ⟨rfl, m, hm, rfl⟩ := hc
        exact hw (Prod.ext (T.star_eq_of_mem_Dv k v hz hm hm0 hy hD) rfl)
      · rw [zero_mul]
    · rw [mul_zero]

theorem R_avg_R (k : ℕ) :
    s.κ • (LKernel.diag (fun v => T.Dv k v) (T.measurable_Dv k)).comp
      ((T.starKernel K k (Matrix.diagonal s.p)).comp
        (LKernel.diag (fun v => T.Dv k v) (T.measurable_Dv k))) =
      LKernel.diag (Λ := τ.Λ) (K := K) (fun v => T.Dv k v) (T.measurable_Dv k) := by
  refine LKernel.ext fun b a => ?_
  rw [nsmul_toFun, diag_comp_apply, comp_diag_apply, LKernel.diag_toFun]
  obtain ⟨z, v⟩ := b
  obtain ⟨y, v'⟩ := a
  dsimp only
  by_cases hz : z ∈ T.Dv k v
  · by_cases hy : y ∈ T.Dv k v'
    · have hzD := T.Dv_sub k v hz
      rw [if_pos hz, if_pos hy, T.avg_toFun s k hzD]
      by_cases he : (z, v) = (y, v')
      · simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        rw [if_pos ⟨rfl, 1, one_mem _, T.star_one' k hzD⟩, if_pos ⟨rfl, hy⟩, nsmul_eq_mul,
          mul_inv_cancel₀ s.κ_ne_zero]
      · rw [if_neg (show ¬((z, v) = (y, v') ∧ y ∈ T.Dv k v') from fun h => he h.1), if_neg]
        · simp
        rintro ⟨rfl, m, hm, rfl⟩
        apply he
        have := T.star_eq_of_mem_Dv k v hzD hm (one_mem _) hy
          (by rwa [T.star_one' k hzD])
        rw [this, T.star_one' k hzD]
    · rw [if_pos hz, if_neg hy, smul_zero, if_neg (fun h => hy h.2)]
  · rw [if_neg hz, smul_zero, if_neg]
    rintro ⟨h1, h2⟩
    simp only [Prod.mk.injEq] at h1
    obtain ⟨rfl, rfl⟩ := h1
    exact hz h2

/-- A function invariant under `J v` is a function on the transversal `Dv k v`. -/
theorem toClass_avgSpace (k : ℕ) :
    toClass (T.avgSpace s k) =
      SigmaMonoid.sum (fun v : V => toClass (single (T.Dv k v) (T.measurable_Dv k v))) := by
  set P := T.starKernel K k (Matrix.diagonal s.p) with hPdef
  set R := LKernel.diag (Λ := τ.Λ) (K := K) (fun v => T.Dv k v) (T.measurable_Dv k) with hRdef
  have hPP : P.comp P = P := (T.avgSpace s k).idem
  have hRR : R.comp R = R := diag_idem _ _
  have h1 : s.κ • P.comp (R.comp P) = P := T.avg_R_avg s k
  have h2 : s.κ • R.comp (P.comp R) = R := T.R_avg_R s k
  have iso : Iso (T.avgSpace s k) (ofSet (Λ := τ.Λ) (K := K) (fun v => T.Dv k v)
      (T.measurable_Dv k)) :=
    { c := R.comp P
      c' := s.κ • P.comp R
      c_mor := show R.comp ((R.comp P).comp P) = R.comp P by
        rw [LKernel.comp_assoc, hPP, ← LKernel.comp_assoc, hRR]
      c'_mor := show P.comp ((s.κ • P.comp R).comp R) = s.κ • P.comp R by
        rw [nsmul_comp, comp_nsmul, LKernel.comp_assoc, hRR, ← LKernel.comp_assoc, hPP]
      left := show (s.κ • P.comp R).comp (R.comp P) = P by
        rw [nsmul_comp, LKernel.comp_assoc, ← LKernel.comp_assoc R R P, hRR]
        exact h1
      right := show (R.comp P).comp (s.κ • P.comp R) = R by
        rw [comp_nsmul, LKernel.comp_assoc, ← LKernel.comp_assoc P P R, hPP]
        exact h2 }
  have hre := ((Equidecomp.refl' (Λ' := τ.Λ) (fun v => T.Dv k v) (T.measurable_Dv k)).reindexSrc
    (Equiv.sigmaPUnit V)).toClass_eq (K := K) (fun p => T.measurable_Dv k p.1) (T.measurable_Dv k)
  calc toClass (T.avgSpace s k)
      = toClass (ofSet (Λ := τ.Λ) (K := K) (fun v => T.Dv k v) (T.measurable_Dv k)) :=
        toClass_eq_iff.2 ⟨iso⟩
    _ = _ := hre.symm
    _ = _ := toClass_ofSet_sigma (fun v (_ : PUnit) => T.Dv k v) (fun v _ => T.measurable_Dv k v)

/-- `D k` is the disjoint union of the `κ` translates of `Dv k v` under `J v`. -/
theorem M_eq_kappa_nsmul (k : ℕ) (v : V) :
    T.M K k = s.κ • toClass (single (T.Dv k v) (T.measurable_Dv k v)) := by
  have := s.finiteJ v
  have h1 := ((T.orbitEq k v).reindexSrc (Equiv.prodPUnit (s.J v))).toClass_eq (K := K)
    (fun _ => T.measurable_Dv k v) (fun _ => T.measurable_D k)
  have h2 := toClass_ofSet_prod (Λ := τ.Λ) (K := K) (ι := s.J v)
    (fun _ : Unit => T.Dv k v) (fun _ => T.measurable_Dv k v)
  rw [← s.cardJ v]
  exact h1.symm.trans (h2.trans (sum_const_natCard _))

/-- The identities `U * T = 1`, `U * diagonal p = U`, `diagonal p * T = T` split off `m` copies
of `(D k)` from `(D k × V, Π)`. -/
theorem toClass_avgSpace_split (k : ℕ) :
    ∃ Q : LocalSpace.Class τ.Λ X K,
      toClass (T.avgSpace s k) = Fintype.card I • T.M K k + Q := by
  obtain ⟨Q, hQ⟩ := exists_complement (T.avgSpace s k)
    (ofSet (Λ := τ.Λ) (K := K) (fun _ : I => T.D k) (fun _ => T.measurable_D k))
    (T.starKernel K k s.T : LKernel τ.Λ X K I V) (T.starKernel K k s.U : LKernel τ.Λ X K V I)
    (by
      show (T.starKernel K k (Matrix.diagonal s.p)).comp ((T.starKernel K k s.T).comp
        (LKernel.diag (fun _ : I => T.D k) (fun _ => T.measurable_D k))) = T.starKernel K k s.T
      rw [← T.starKernel_one, ← T.starKernel_mul, ← T.starKernel_mul, Matrix.mul_one, s.PT])
    (by
      show (LKernel.diag (fun _ : I => T.D k) (fun _ => T.measurable_D k)).comp
        ((T.starKernel K k s.U).comp (T.starKernel K k (Matrix.diagonal s.p))) =
          T.starKernel K k s.U
      rw [← T.starKernel_one, ← T.starKernel_mul, ← T.starKernel_mul, Matrix.one_mul, s.UP])
    (by
      show (T.starKernel K k s.U).comp (T.starKernel K k s.T) =
        LKernel.diag (fun _ : I => T.D k) (fun _ => T.measurable_D k)
      rw [← T.starKernel_one, ← T.starKernel_mul, s.UT])
  refine ⟨Q, hQ.trans ?_⟩
  congr 1
  have h1 := ((Equidecomp.refl' (Λ' := τ.Λ) (fun _ : I => T.D k) (fun _ => T.measurable_D k)
    ).reindexSrc (Equiv.prodPUnit I)).toClass_eq (K := K)
    (fun _ => T.measurable_D k) (fun _ => T.measurable_D k)
  have h2 := toClass_ofSet_prod (Λ := τ.Λ) (K := K) (ι := I)
    (fun _ : Unit => T.D k) (fun _ => T.measurable_D k)
  exact h1.symm.trans (h2.trans (sum_const_card _))

/-- (S3): `d · M k = κ m · M k + G k`, with `d = |V|` and `m = |I|`. -/
theorem S3 (k : ℕ) :
    ∃ Q : LocalSpace.Class τ.Λ X K,
      Fintype.card V • T.M K k = (s.κ * Fintype.card I) • T.M K k + Q := by
  obtain ⟨Q, hQ⟩ := T.toClass_avgSpace_split s k
  refine ⟨s.κ • Q, ?_⟩
  calc Fintype.card V • T.M K k = SigmaMonoid.sum (fun _ : V => T.M K k) :=
        (sum_const_card _).symm
    _ = SigmaMonoid.sum (fun v : V =>
          s.κ • toClass (single (Λ := τ.Λ) (K := K) (T.Dv k v) (T.measurable_Dv k v))) :=
        SigmaMonoid.sum_congr' fun v => T.M_eq_kappa_nsmul s k v
    _ = s.κ • toClass (T.avgSpace s k) := by
        rw [SigmaMonoid.sum_nsmul, T.toClass_avgSpace s k]
    _ = _ := by rw [hQ, nsmul_add, smul_smul]

end

end MarkerTower

end Collapse
