module

public import BernoulliIso.SubgroupAverage

/-!
The range of the subgroup average is the actual larger-coset configuration
space. No unspecified identification of compact groups is assumed.
-/

@[expose] public section
noncomputable section
open scoped Classical

namespace BernoulliIso

variable {K N G : Type*} [Group G]

/-- Right periods of a function form a subgroup. -/
def rightPeriods (f : G → K) : Subgroup G where
  carrier := {h | ∀ g, f (g * h) = f g}
  one_mem' := by intro g; simp
  mul_mem' := by
    intro a b ha hb g
    rw [← mul_assoc, hb, ha]
  inv_mem' := by
    intro a ha g
    have h := ha (g * a⁻¹)
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using h.symm

namespace CosetOperators

variable [Field K] [Group N]
variable (H : Subgroup G) (ι : N →* G)
  (commutes : ∀ h ∈ H, ∀ n, Commute h (ι n))

theorem sup_le_rightPeriods (J : Subgroup N) (f : G ⧸ H → K)
    (hinv : ∀ (j : J) (x : G ⧸ H), f (rightCoset H ι commutes j x) = f x) :
    H ⊔ J.map ι ≤ rightPeriods (fun g => f (QuotientGroup.mk g)) := by
  apply sup_le
  · intro h hh g
    exact congrArg f (QuotientGroup.mk_mul_of_mem g hh)
  · rintro _ ⟨n, hn, rfl⟩ g
    exact hinv ⟨n, hn⟩ (QuotientGroup.mk g)

def descend (J : Subgroup N) (f : G ⧸ H → K)
    (hinv : ∀ (j : J) (x : G ⧸ H), f (rightCoset H ι commutes j x) = f x) :
    G ⧸ (H ⊔ J.map ι) → K :=
  Quotient.lift (fun g => f (QuotientGroup.mk g)) (by
    intro a b hab
    have h := (sup_le_rightPeriods H ι commutes J f hinv)
      (QuotientGroup.leftRel_apply.mp hab) a
    simpa only [mul_inv_cancel_left] using h.symm)

@[simp] theorem descend_mk (J : Subgroup N) (f : G ⧸ H → K)
    (hinv : ∀ (j : J) (x : G ⧸ H), f (rightCoset H ι commutes j x) = f x) (g : G) :
    descend H ι commutes J f hinv (QuotientGroup.mk g) = f (QuotientGroup.mk g) := rfl

def pullback (J : Subgroup N) (f : G ⧸ (H ⊔ J.map ι) → K) : G ⧸ H → K :=
  fun x => f (Subgroup.quotientMapOfLE le_sup_left x)

theorem pullback_mem_average_range (J : Subgroup N) [Fintype J]
    (hcard : (Fintype.card J : K) ≠ 0) (f : G ⧸ (H ⊔ J.map ι) → K) :
    pullback H ι J f ∈ (groupRing H ι commutes (subgroupAverage J)).range := by
  apply (mem_subgroupAverage_range_iff H ι commutes J hcard _).2
  intro j x
  induction x using QuotientGroup.induction_on with
  | H g =>
    change f (QuotientGroup.mk (g * ι j)) = f (QuotientGroup.mk g)
    exact congrArg f (QuotientGroup.mk_mul_of_mem g
      ((show J.map ι ≤ H ⊔ J.map ι from le_sup_right)
        (Subgroup.mem_map_of_mem ι j.property)))

/-- Larger-coset configurations and the average range are exactly linearly
isomorphic, by pullback and quotient descent. -/
def averageRangeEquiv (J : Subgroup N) [Fintype J]
    (hcard : (Fintype.card J : K) ≠ 0) :
    (G ⧸ (H ⊔ J.map ι) → K) ≃ₗ[K]
      (groupRing (K := K) H ι commutes (subgroupAverage J)).range where
  toFun f := ⟨pullback H ι J f, pullback_mem_average_range H ι commutes J hcard f⟩
  invFun f := descend H ι commutes J f
    ((mem_subgroupAverage_range_iff H ι commutes J hcard f).1 f.property)
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

section Topology

variable [TopologicalSpace K]

theorem continuous_averageRangeEquiv (J : Subgroup N) [Fintype J]
    (hcard : (Fintype.card J : K) ≠ 0) :
    Continuous (averageRangeEquiv H ι commutes J hcard) := by
  exact (continuous_pi fun x => continuous_apply
    (Subgroup.quotientMapOfLE le_sup_left x)).subtype_mk _

theorem continuous_averageRangeEquiv_symm (J : Subgroup N) [Fintype J]
    (hcard : (Fintype.card J : K) ≠ 0) :
    Continuous (averageRangeEquiv H ι commutes J hcard).symm := by
  apply continuous_pi
  intro x
  induction x using QuotientGroup.induction_on with
  | H g =>
    change Continuous (fun f : (groupRing (K := K) H ι commutes
      (subgroupAverage J)).range => f.val (QuotientGroup.mk g))
    exact (continuous_apply (QuotientGroup.mk g)).comp continuous_subtype_val

end Topology
end CosetOperators
end BernoulliIso
