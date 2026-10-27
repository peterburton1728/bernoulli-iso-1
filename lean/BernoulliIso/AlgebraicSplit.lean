module

public import Mathlib.LinearAlgebra.Prod

/-!
Exact algebraic splitting, at the level of modules.

This file proves the elementary module lemma used in the manuscript.
It does not assert existence of the required group-algebra matrices and
does not yet formalize their action on coset spaces or Haar measures.
-/

@[expose] public section

namespace BernoulliIso

variable {K V W : Type*} [Ring K] [AddCommGroup V] [AddCommGroup W]
  [Module K V] [Module K W]

/-- The algebraic input to the splitting lemma, including idempotence of `P`.
The manuscript derives idempotence from finite-subgroup averages. -/
structure SplitData (K V W : Type*) [Ring K] [AddCommGroup V] [AddCommGroup W]
    [Module K V] [Module K W] where
  P : V →ₗ[K] V
  U : V →ₗ[K] W
  T : W →ₗ[K] V
  PP : ∀ x, P (P x) = P x
  UP : ∀ x, U (P x) = U x
  PT : ∀ y, P (T y) = T y
  UT : ∀ y, U (T y) = y

namespace SplitData

variable (s : SplitData K V W)

/-- The residual projection, exactly `P - T U`. -/
def Q : V →ₗ[K] V := s.P - s.T.comp s.U

@[simp] theorem Q_apply (x : V) : s.Q x = s.P x - s.T (s.U x) := rfl

theorem PQ (x : V) : s.P (s.Q x) = s.Q x := by
  simp only [Q_apply, map_sub, s.PP, s.PT]

theorem UQ (x : V) : s.U (s.Q x) = 0 := by
  simp only [Q_apply, map_sub, s.UP, s.UT, sub_self]

theorem QT (y : W) : s.Q (s.T y) = 0 := by
  simp only [Q_apply, s.PT, s.UT, sub_self]

theorem QQ (x : V) : s.Q (s.Q x) = s.Q x := by
  rw [Q_apply, s.PQ, s.UQ, map_zero, sub_zero]

/-- The image of an idempotent is its fixed-point space. -/
theorem mem_P_range_iff (x : V) : x ∈ s.P.range ↔ s.P x = x := by
  constructor
  · rintro ⟨v, rfl⟩
    exact s.PP v
  · intro h
    exact ⟨x, h⟩

theorem mem_Q_range_iff (x : V) : x ∈ s.Q.range ↔ s.Q x = x := by
  constructor
  · rintro ⟨v, rfl⟩
    exact s.QQ v
  · intro h
    exact ⟨x, h⟩

theorem P_of_mem_Q_range {z : V} (hz : z ∈ s.Q.range) : s.P z = z := by
  rcases hz with ⟨x, rfl⟩
  exact s.PQ x

theorem U_of_mem_Q_range {z : V} (hz : z ∈ s.Q.range) : s.U z = 0 := by
  rcases hz with ⟨x, rfl⟩
  exact s.UQ x

/-- The actual linear equivalence `im P ≃ W × im(P - TU)`.
Its inverse is `(y,z) ↦ Ty + z`, as in the manuscript. -/
def linearEquiv : s.P.range ≃ₗ[K] (W × s.Q.range) where
  toFun v := (s.U v, ⟨s.Q v, LinearMap.mem_range_self s.Q v⟩)
  invFun yz := ⟨s.T yz.1 + yz.2, (s.mem_P_range_iff _).2 (by
    rw [map_add, s.PT, s.P_of_mem_Q_range yz.2.property])⟩
  left_inv v := by
    apply Subtype.ext
    change s.T (s.U v) + (s.P v - s.T (s.U v)) = v
    rw [(s.mem_P_range_iff _).1 v.property]
    rw [add_comm, sub_add_cancel]
  right_inv yz := by
    apply Prod.ext
    · change s.U (s.T yz.1 + (yz.2 : V)) = yz.1
      rw [map_add, s.UT, s.U_of_mem_Q_range yz.2.property, add_zero]
    · apply Subtype.ext
      change s.Q (s.T yz.1 + (yz.2 : V)) = yz.2
      rw [map_add, s.QT, zero_add, (s.mem_Q_range_iff _).1 yz.2.property]
  map_add' x y := by
    apply Prod.ext
    · exact map_add s.U _ _
    · apply Subtype.ext
      exact map_add s.Q _ _
  map_smul' a x := by
    apply Prod.ext
    · exact map_smul s.U _ _
    · apply Subtype.ext
      exact map_smul s.Q _ _

end SplitData
end BernoulliIso

#print axioms BernoulliIso.SplitData.QQ
#print axioms BernoulliIso.SplitData.linearEquiv
