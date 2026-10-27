module

public import BernoulliIso.InputOperators
public import BernoulliIso.AverageRange

/-! The concrete diagonal range is the product of larger-coset configuration spaces. -/

@[expose] public section
noncomputable section
open scoped BigOperators Classical

namespace BernoulliIso
namespace CosetOperators

variable {K N G V : Type*} [Field K] [Group N] [Group G] [Fintype V]
variable (H : Subgroup G) (ι : N →* G)
  (commutes : ∀ h ∈ H, ∀ n, Commute h (ι n))

theorem matrix_diagonal_apply (p : V → MonoidAlgebra K N)
    (f : V → G ⧸ H → K) (v : V) :
    matrix H ι commutes (Matrix.diagonal p) f v = groupRing H ι commutes (p v) (f v) := by
  rw [matrix_apply, Finset.sum_eq_single v]
  · simp
  · intro j _ hj
    simp [Matrix.diagonal_apply, Ne.symm hj]
  · simp

theorem mem_diagonal_range_iff (p : V → MonoidAlgebra K N) (f : V → G ⧸ H → K) :
    f ∈ (matrix H ι commutes (Matrix.diagonal p)).range ↔
      ∀ v, f v ∈ (groupRing H ι commutes (p v)).range := by
  constructor
  · rintro ⟨x, rfl⟩ v
    rw [matrix_diagonal_apply]
    exact LinearMap.mem_range_self _ _
  · intro hf
    choose x hx using hf
    exact ⟨x, funext fun v => (matrix_diagonal_apply H ι commutes p x v).trans (hx v)⟩

def diagonalRangeEquiv (p : V → MonoidAlgebra K N) :
    (matrix H ι commutes (Matrix.diagonal p)).range ≃ₗ[K]
      (∀ v, (groupRing H ι commutes (p v)).range) where
  toFun f v := ⟨f.val v, (mem_diagonal_range_iff H ι commutes p f).1 f.property v⟩
  invFun f := ⟨fun v => (f v).val,
    (mem_diagonal_range_iff H ι commutes p _).2 (fun v => (f v).property)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end CosetOperators
namespace AlgebraicInput

variable {K N I V G : Type*} [Field K] [Finite K]
  [Group N] [Countable N] [Fintype I] [Fintype V] [Nonempty I] [Nonempty V] [Group G]
variable (s : AlgebraicInput K N I V)

instance subgroupFintype (v : V) : Fintype (s.J v) :=
  @Fintype.ofFinite (s.J v) (s.finiteJ v)

theorem subgroup_card (v : V) : Fintype.card (s.J v) = s.κ := by
  rw [← Nat.card_eq_fintype_card]
  exact s.cardJ v

theorem subgroup_card_ne_zero (v : V) : (Fintype.card (s.J v) : K) ≠ 0 := by
  rw [s.subgroup_card]
  exact s.κ_ne_zero

theorem p_eq_subgroupAverage (v : V) : s.p v = subgroupAverage (s.J v) := by
  rw [s.p_average]
  simp only [subgroupAverage, s.subgroup_card]

variable (H : Subgroup G) (ι : N →* G)
  (commutes : ∀ h ∈ H, ∀ n, Commute h (ι n))

def scalarCosetRangeEquiv (v : V) :
    (G ⧸ (H ⊔ (s.J v).map ι) → K) ≃ₗ[K]
      (CosetOperators.groupRing H ι commutes (s.p v)).range where
  toFun f := ⟨CosetOperators.pullback H ι (s.J v) f, by
    rw [s.p_eq_subgroupAverage]
    exact CosetOperators.pullback_mem_average_range H ι commutes (s.J v)
      (s.subgroup_card_ne_zero v) f⟩
  invFun f := CosetOperators.descend H ι commutes (s.J v) f
    ((CosetOperators.mem_subgroupAverage_range_iff H ι commutes (s.J v)
      (s.subgroup_card_ne_zero v) f).1 (by
        rw [← s.p_eq_subgroupAverage]
        exact f.property))
  left_inv f := by
    funext x
    induction x using QuotientGroup.induction_on with
    | H g => rfl
  right_inv f := by
    apply Subtype.ext
    funext x
    induction x using QuotientGroup.induction_on with
    | H g => rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- This is the manuscript's space V_H, identified with the actual matrix range. -/
def cosetProductRangeEquiv :
    (∀ v, G ⧸ (H ⊔ (s.J v).map ι) → K) ≃ₗ[K]
      (s.concreteSplit H ι commutes).P.range :=
  (LinearEquiv.piCongrRight fun v => s.scalarCosetRangeEquiv H ι commutes v).trans
    (CosetOperators.diagonalRangeEquiv H ι commutes s.p).symm

/-- Evaluation after quotient descent agrees with the original invariant
configuration, at every representative of the larger coset. -/
theorem cosetProductRangeEquiv_symm_apply
    (f : (s.concreteSplit H ι commutes).P.range) (v : V) (x : G ⧸ H) :
    (s.cosetProductRangeEquiv H ι commutes).symm f v
      (Subgroup.quotientMapOfLE (show H ≤ H ⊔ (s.J v).map ι from le_sup_left) x) =
        f.val v x := by
  induction x using QuotientGroup.induction_on with
  | H g => rfl

end AlgebraicInput
end BernoulliIso
