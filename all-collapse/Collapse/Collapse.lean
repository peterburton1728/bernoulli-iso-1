module

public import Collapse.Transform

/-!
# The collapse

The collapse theorem and the algebra of the ergodic case.
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
  {τ : TowerSetting N G} {U : Set X}

/-- The class of a disjoint union of two measurable sets is the sum of the classes. -/
theorem toClass_single_union (B₁ B₂ : Set X) (h₁ : MeasurableSet B₁) (h₂ : MeasurableSet B₂)
    (hd : Disjoint B₁ B₂) :
    toClass (single (Λ := τ.Λ) (K := K) (B₁ ∪ B₂) (h₁.union h₂)) =
      toClass (single (Λ := τ.Λ) (K := K) B₁ h₁) + toClass (single (Λ := τ.Λ) (K := K) B₂ h₂) := by
  have hm : ∀ (i : Bool) (_ : Unit), MeasurableSet (bif i then B₂ else B₁) := fun i _ => by
    cases i <;> assumption
  have hdisj : ∀ _ : Unit, Pairwise fun i i' : Bool =>
      Disjoint (bif i then B₂ else B₁) (bif i' then B₂ else B₁) := by
    intro _ i i' hii'
    cases i <;> cases i' <;> simp_all [hd.symm]
  have h := toClass_ofSet_iUnion (Λ := τ.Λ) (K := K)
    (fun (i : Bool) (_ : Unit) => bif i then B₂ else B₁) hm hdisj
  rw [SigmaMonoid.add_def]
  refine (toClass_ofSet_congr ?_ _ _).trans (h.trans (SigmaMonoid.sum_congr' fun i => ?_))
  · funext j
    ext x
    simp
  · cases i <;> rfl

namespace MarkerTower

/-- **Collapse**: `a · (D n) ≅ ∞ · (U)` for all `n` and all `a ≥ 1`. -/
theorem collapse (s : AlgebraicInput K N I V) (T : MarkerTower τ s.J U) (n a : ℕ)
    (ha : 1 ≤ a) : a • T.M K n = SigmaMonoid.infty (T.top K) := by
  choose Q hQ using fun k => T.S3 s k
  have h := SigmaMonoid.absorption (T.M K) (fun _ => 2) (fun _ => le_rfl)
    (d := Fintype.card V) (e := s.κ * Fintype.card I) Fintype.card_pos s.surplus Q
    (fun k => T.S1 K k) (fun n => by simpa using T.S2 K n) hQ n a ha
  rwa [T.M_zero K] at h

/-- The algebra of the ergodic case: a subset of `U` which contains
a set equidecomposable with some `D n` has the class of `∞ · (U)`. -/
theorem toClass_single_eq_infty (s : AlgebraicInput K N I V) (T : MarkerTower τ s.J U)
    (A : Set X) (hA : MeasurableSet A) (hAU : A ⊆ U) (n : ℕ) (A' : Set X)
    (hA' : MeasurableSet A') (hsub : A' ⊆ A)
    (E : Nonempty (Equidecomp τ.Λ (fun _ : Unit => T.D n) (fun _ : Unit => A'))) :
    toClass (single (K := K) A hA) = SigmaMonoid.infty (T.top K) := by
  set u := SigmaMonoid.infty (T.top K)
  have hsplit : ∀ (B C : Set X) (hB : MeasurableSet B) (hC : MeasurableSet C), C ⊆ B →
      toClass (single (Λ := τ.Λ) (K := K) B hB) =
        toClass (single (Λ := τ.Λ) (K := K) C hC) + toClass (single (B \ C) (hB.diff hC)) := by
    intro B C hB hC hCB
    rw [← toClass_single_union C (B \ C) hC (hB.diff hC) Set.disjoint_sdiff_right]
    exact toClass_ofSet_congr (funext fun _ => (Set.union_sdiff_cancel hCB).symm) _ _
  have h2 : toClass (single (Λ := τ.Λ) (K := K) A' hA') = u := by
    have := Equidecomp.toClass_eq (K := K) E.some (fun _ => T.measurable_D n) (fun _ => hA')
    have hc := T.collapse s n 1 le_rfl
    rw [one_smul] at hc
    exact this.symm.trans hc
  have hAD : A \ A' ⊆ U := Set.sdiff_subset.trans hAU
  have hT := hsplit U (A \ A') T.U_measurable (hA.diff hA') hAD
  have hu : u = toClass (single (Λ := τ.Λ) (K := K) (A \ A') (hA.diff hA')) +
      (toClass (single (Λ := τ.Λ) (K := K) (U \ (A \ A')) (T.U_measurable.diff (hA.diff hA'))) + u) := by
    rw [← add_assoc, ← hT, add_comm]
    exact (SigmaMonoid.infty_add_self (T.top K)).symm
  rw [hsplit A A' hA hA' hsub, h2]
  exact SigmaMonoid.add_eq_of_infty (SigmaMonoid.infty_infty _).symm hu

end MarkerTower

end Collapse
