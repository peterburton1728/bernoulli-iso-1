module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.SetTheory.Cardinal.Finite

@[expose] public section

noncomputable section
open scoped BigOperators Classical

namespace BernoulliIso

/-- The precise finite subgroup rectangle needed by the dynamical construction.
This is a data interface, not an existence theorem. -/
structure AlgebraicInput (K N I V : Type*) [Field K] [Finite K]
    [Group N] [Countable N] [Fintype I] [Fintype V]
    [Nonempty I] [Nonempty V] where
  κ : ℕ
  J : V → Subgroup N
  finiteJ : ∀ v, Finite (J v)
  cardJ : ∀ v, Nat.card (J v) = κ
  κ_ne_zero : (κ : K) ≠ 0
  p : V → MonoidAlgebra K N
  p_average : ∀ v, p v = (κ : K)⁻¹ •
    (letI := finiteJ v
     letI := Fintype.ofFinite (J v)
     ∑ g : J v, MonoidAlgebra.single (g : N) 1)
  p_idempotent : ∀ v, p v * p v = p v
  U : Matrix I V (MonoidAlgebra K N)
  T : Matrix V I (MonoidAlgebra K N)
  UP : U * Matrix.diagonal p = U
  PT : Matrix.diagonal p * T = T
  UT : U * T = 1
  surplus : Fintype.card V < κ * Fintype.card I

namespace AlgebraicInput

variable {K N I V : Type*} [Field K] [Finite K]
  [Group N] [Countable N] [Fintype I] [Fintype V]
  [Nonempty I] [Nonempty V]

theorem PP (s : AlgebraicInput K N I V) :
    Matrix.diagonal s.p * Matrix.diagonal s.p = Matrix.diagonal s.p := by
  classical
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext v
  exact s.p_idempotent v

end AlgebraicInput
end BernoulliIso

#print axioms BernoulliIso.AlgebraicInput.PP
