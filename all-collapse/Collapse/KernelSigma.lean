module

public import Collapse.Kernel

/-!
# Block-diagonal kernels and changes of index

The kernel of a countable sum of local spaces, and the kernels of bijections of index types.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Collapse

namespace LKernel

variable {Λ X K : Type} [Group Λ] [MulAction Λ X] [MeasurableSpace X] [BorelFree Λ X]
  [Ring K] [MeasurableSpace K] [DiscreteCoeff K] {J J' J₂ J₃ : Type}

open Classical in
/-- The block-diagonal kernel of a family: it is `c i` on the `i`-th summand and vanishes
between different summands. -/
noncomputable def sigma {ι : Type} {J J' : ι → Type} (c : ∀ i, LKernel Λ X K (J i) (J' i)) :
    LKernel Λ X K (Σ i, J i) (Σ i, J' i) where
  toFun b a := if h : a.2.1 = b.2.1 then (c b.2.1).toFun (b.1, b.2.2) (a.1, h ▸ a.2.2) else 0
  rel := by
    rintro ⟨y, i', j'⟩ ⟨x, i, j⟩ h
    by_cases hi : i = i'
    · subst hi; rw [dite_eq_left rfl] at h; exact (c i).rel (y, j') (x, j) h
    · exact (h (dite_eq_right hi)).elim
  rowFinite := by
    rintro ⟨y, i', j'⟩
    refine (((c i').rowFinite (y, j')).image
      fun p : X × J i' => (p.1, (⟨i', p.2⟩ : Σ i, J i))).subset ?_
    rintro ⟨x, i, j⟩ h
    by_cases hi : i = i'
    · subst hi; rw [Set.mem_ofPred_eq, dite_eq_left rfl] at h; exact ⟨(x, j), h, rfl⟩
    · exact (h (dite_eq_right hi)).elim
  colFinite := by
    rintro ⟨x, i, j⟩
    refine (((c i).colFinite (x, j)).image
      fun p : X × J' i => (p.1, (⟨i, p.2⟩ : Σ i, J' i))).subset ?_
    rintro ⟨y, i', j'⟩ h
    by_cases hi : i = i'
    · subst hi; rw [Set.mem_ofPred_eq, dite_eq_left rfl] at h; exact ⟨(y, j'), h, rfl⟩
    · exact (h (dite_eq_right hi)).elim
  measurable := by
    rintro g ⟨i', j'⟩ ⟨i, j⟩
    by_cases hi : i = i'
    · subst hi
      convert (c i).measurable g j' j using 2 with x
      exact dite_eq_left rfl
    · convert measurable_const (a := (0 : K)) using 1
      funext x; exact dite_eq_right hi

theorem sigma_toFun_mk {ι : Type} {J J' : ι → Type} (c : ∀ i, LKernel Λ X K (J i) (J' i))
    (y x : X) (i : ι) (j' : J' i) (j : J i) :
    (sigma c).toFun (y, ⟨i, j'⟩) (x, ⟨i, j⟩) = (c i).toFun (y, j') (x, j) := dite_eq_left rfl

theorem sigma_toFun_ne {ι : Type} {J J' : ι → Type} (c : ∀ i, LKernel Λ X K (J i) (J' i))
    (y x : X) {i i' : ι} (j' : J' i') (j : J i) (h : i ≠ i') :
    (sigma c).toFun (y, ⟨i', j'⟩) (x, ⟨i, j⟩) = 0 := dite_eq_right h

open Classical in
/-- The kernel of a bijection of index types: the point `(x, j)` goes to `(x, e j)`. -/
noncomputable def ofEquiv (e : J ≃ J') : LKernel Λ X K J J' where
  toFun b a := if b.1 = a.1 ∧ b.2 = e a.2 then 1 else 0
  rel := by
    intro b a h
    by_cases hh : b.1 = a.1 ∧ b.2 = e a.2
    · rw [hh.1]; exact MulAction.mem_orbit_self _
    · exact (h (ite_eq_right hh)).elim
  rowFinite b := (Set.finite_singleton (b.1, e.symm b.2)).subset fun a ha => by
    by_contra h'
    exact ha (ite_eq_right fun hh => h' (Prod.ext hh.1.symm (by simp [hh.2])))
  colFinite a := (Set.finite_singleton (a.1, e a.2)).subset fun b hb => by
    by_contra h'
    exact hb (ite_eq_right fun hh => h' (Prod.ext hh.1 hh.2))
  measurable g j' j := by
    by_cases hg : g = 1
    · subst hg
      convert measurable_const (a := if j' = e j then (1 : K) else 0) using 1
      funext x; simp
    · convert measurable_const (a := (0 : K)) using 1
      funext x; exact ite_eq_right fun hh => hg (BorelFree.free g x hh.1.symm)

open Classical in
theorem ofEquiv_toFun (e : J ≃ J') (b : X × J') (a : X × J) :
    (ofEquiv (Λ := Λ) (K := K) e).toFun b a = if b.1 = a.1 ∧ b.2 = e a.2 then 1 else 0 := rfl

theorem sigma_comp_sigma {ι : Type} {J J' J₂ : ι → Type} [Countable ι] [∀ i, Countable (J' i)]
    (c' : ∀ i, LKernel Λ X K (J' i) (J₂ i)) (c : ∀ i, LKernel Λ X K (J i) (J' i)) :
    (sigma c').comp (sigma c) = sigma (fun i => (c' i).comp (c i)) := by
  refine ext fun ⟨z, i₂, k⟩ ⟨x, i, j⟩ => ?_
  rw [comp_toFun]
  by_cases hi : i = i₂
  · subst hi
    rw [sigma_toFun_mk, comp_toFun,
      finsum_eq_finsum_comp (fun p : X × J' i => (p.1, (⟨i, p.2⟩ : Σ i, J' i))) ?_ ?_]
    · simp only [sigma_toFun_mk]
    · rintro ⟨y, l⟩ ⟨y', l'⟩ h
      simp only [Prod.mk.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and] at h
      rw [h.1, h.2]
    · rintro ⟨y, i', j'⟩ hb
      by_cases h' : i' = i
      · subst h'; exact ⟨(y, j'), rfl⟩
      · exact (left_ne_zero_of_mul hb (sigma_toFun_ne c' _ _ _ _ h')).elim
  · rw [sigma_toFun_ne _ _ _ _ _ hi]
    refine finsum_eq_zero_of_forall_eq_zero fun ⟨y, i', j'⟩ => ?_
    by_cases h' : i' = i₂
    · subst h'; rw [sigma_toFun_ne c _ _ _ _ hi, mul_zero]
    · rw [sigma_toFun_ne c' _ _ _ _ h', zero_mul]

theorem sigma_diag {ι : Type} {J : ι → Type} (A : ∀ i, J i → Set X)
    (hA : ∀ i j, MeasurableSet (A i j)) :
    sigma (fun i => diag (Λ := Λ) (K := K) (A i) (hA i)) =
      diag (fun p : Σ i, J i => A p.1 p.2) (fun p => hA p.1 p.2) := by
  refine ext fun ⟨y, i', j'⟩ ⟨x, i, j⟩ => ?_
  by_cases hi : i = i'
  · subst hi
    simp only [sigma_toFun_mk, diag_toFun]
    split_ifs <;> simp_all [Prod.ext_iff]
  · rw [sigma_toFun_ne _ _ _ _ _ hi, diag_toFun, ite_eq_right]
    rintro ⟨h, -⟩
    exact hi (congrArg (fun p : X × (Σ i, J i) => p.2.1) h).symm

theorem ofEquiv_comp_ofEquiv [Countable J'] (e : J ≃ J') (e' : J' ≃ J₂) :
    (ofEquiv (Λ := Λ) (X := X) (K := K) e').comp (ofEquiv e) = ofEquiv (e.trans e') := by
  refine ext fun z a => ?_
  rw [comp_toFun, finsum_eq_single _ (a.1, e a.2) fun b hb => by
    rw [ofEquiv_toFun e, ite_eq_right fun hh => hb (Prod.ext hh.1 hh.2), mul_zero]]
  simp only [ofEquiv_toFun, and_self, ite_true, mul_one, Equiv.trans_apply]
  classical exact if_congr Iff.rfl rfl rfl

theorem ofEquiv_refl : ofEquiv (Λ := Λ) (X := X) (K := K) (Equiv.refl J) = id J := by
  refine ext fun b a => ?_
  simp only [id, diag_toFun, ofEquiv_toFun]
  by_cases h : b = a
  · subst h; simp
  · rw [ite_eq_right (fun hh => h (Prod.ext hh.1 hh.2)), ite_eq_right (fun hh => h hh.1)]

end LKernel

end Collapse
