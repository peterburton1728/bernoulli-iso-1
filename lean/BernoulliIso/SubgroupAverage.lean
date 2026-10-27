module

public import BernoulliIso.GroupRingAction

/-! Normalized finite-subgroup averages and their actual configuration ranges. -/

@[expose] public section
noncomputable section
open scoped BigOperators Classical

namespace BernoulliIso

variable {K N G : Type*} [Field K] [Group N] [Group G]

def subgroupAverage (J : Subgroup N) [Fintype J] : MonoidAlgebra K N :=
  (Fintype.card J : K)⁻¹ • ∑ j : J, MonoidAlgebra.single (j : N) 1

theorem single_mul_subgroupAverage (J : Subgroup N) [Fintype J] (j : J) :
    MonoidAlgebra.single (j : N) (1 : K) * subgroupAverage J = subgroupAverage J := by
  simp only [subgroupAverage, mul_smul_comm, Finset.mul_sum,
    MonoidAlgebra.single_mul_single, one_mul]
  congr 1
  exact Equiv.sum_comp (Equiv.mulLeft j)
    (fun x : J => MonoidAlgebra.single (x : N) (1 : K))

namespace CosetOperators

variable (H : Subgroup G) (ι : N →* G)
  (commutes : ∀ h ∈ H, ∀ n, Commute h (ι n))

theorem subgroupAverage_apply (J : Subgroup N) [Fintype J]
    (f : G ⧸ H → K) (x : G ⧸ H) :
    groupRing H ι commutes (subgroupAverage J) f x =
      (Fintype.card J : K)⁻¹ * ∑ j : J, f (rightCoset H ι commutes j x) := by
  simp [subgroupAverage, map_smul, LinearMap.sum_apply, Finset.sum_apply,
    groupRing_single, Finset.mul_sum]

/-- Averaging really produces functions constant on each finite right orbit. -/
theorem subgroupAverage_invariant (J : Subgroup N) [Fintype J]
    (f : G ⧸ H → K) (j : J) (x : G ⧸ H) :
    groupRing H ι commutes (subgroupAverage J) f (rightCoset H ι commutes j x) =
      groupRing H ι commutes (subgroupAverage J) f x := by
  have h := congrArg (fun a : MonoidAlgebra K N => groupRing H ι commutes a f x)
    (single_mul_subgroupAverage (K := K) J j)
  simpa only [map_mul, Module.End.mul_apply, groupRing_single, one_mul] using h

theorem subgroupAverage_fixes (J : Subgroup N) [Fintype J]
    (hcard : (Fintype.card J : K) ≠ 0) (f : G ⧸ H → K)
    (hinv : ∀ (j : J) (x : G ⧸ H), f (rightCoset H ι commutes j x) = f x) :
    groupRing H ι commutes (subgroupAverage J) f = f := by
  funext x
  rw [subgroupAverage_apply]
  simp_rw [hinv]
  simp [nsmul_eq_mul, ← mul_assoc, hcard]

/-- The range is exactly the finite-orbit-constant functions, rather than
    an abstract unspecified summand. -/
theorem mem_subgroupAverage_range_iff (J : Subgroup N) [Fintype J]
    (hcard : (Fintype.card J : K) ≠ 0) (f : G ⧸ H → K) :
    f ∈ (groupRing H ι commutes (subgroupAverage J)).range ↔
      ∀ (j : J) (x : G ⧸ H), f (rightCoset H ι commutes j x) = f x := by
  constructor
  · rintro ⟨v, rfl⟩
    exact subgroupAverage_invariant H ι commutes J v
  · intro hinv
    exact ⟨f, subgroupAverage_fixes H ι commutes J hcard f hinv⟩

end CosetOperators
end BernoulliIso
