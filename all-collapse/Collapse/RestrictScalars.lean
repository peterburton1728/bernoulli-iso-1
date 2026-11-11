module

public import BernoulliIso.AlgebraicInput
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Restriction of scalars of an algebraic input

Let `F ⊆ K` be finite fields and `b` an `F`-basis of `K`. The
regular representation `ρ : K → Mat(F)` in the basis `b` is a ring homomorphism; applying it to
the coefficients of the matrices `U` and `T` gives an algebraic input over `F` with index sets
`I × ι` and `V × ι`, the same subgroups and the same `κ`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

open scoped BigOperators Classical

namespace Collapse

open BernoulliIso

variable {K N I V : Type} [Field K] [Finite K] [Group N] [Countable N] [Fintype I] [Fintype V]
  [Nonempty I] [Nonempty V]

/-- Apply the entry `(a, c)` of the regular representation to every coefficient. -/
def restrictCoeff {F ι : Type} [Field F] [Algebra F K] [Fintype ι] (b : Module.Basis ι F K)
    (a c : ι) (x : MonoidAlgebra K N) : MonoidAlgebra F N :=
  MonoidAlgebra.ofCoeff (x.coeff.mapRange (fun k => Algebra.leftMulMatrix b k a c) (by simp))

section RestrictAux

variable {F ι : Type} [Field F] [Algebra F K] [Fintype ι] (b : Module.Basis ι F K)

theorem restrictCoeff_coeff (a c : ι) (x : MonoidAlgebra K N) (n : N) :
    (restrictCoeff b a c x).coeff n = Algebra.leftMulMatrix b (x.coeff n) a c := by
  simp [restrictCoeff]

/-- `restrictCoeff` as an `F`-linear map. -/
def restrictLin (a c : ι) : MonoidAlgebra K N →ₗ[F] MonoidAlgebra F N where
  toFun := restrictCoeff b a c
  map_add' x y := by
    ext n; simp [restrictCoeff_coeff, MonoidAlgebra.coeff_add]
  map_smul' r x := by
    ext n; simp [restrictCoeff_coeff]

theorem restrictLin_apply (a c : ι) (x : MonoidAlgebra K N) :
    restrictLin (N := N) b a c x = restrictCoeff b a c x := rfl

theorem restrictCoeff_single (a c : ι) (n : N) (k : K) :
    restrictCoeff b a c (MonoidAlgebra.single n k) =
      MonoidAlgebra.single n (Algebra.leftMulMatrix b k a c) := by
  ext m; simp [restrictCoeff_coeff, MonoidAlgebra.coeff_single, Finsupp.single_apply]
  split_ifs <;> simp

theorem restrictCoeff_mul (a c : ι) (x y : MonoidAlgebra K N) :
    restrictCoeff b a c (x * y) = ∑ d, restrictCoeff b a d x * restrictCoeff b d c y := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp [← restrictLin_apply]
  | add x x' hx hx' =>
    simp only [add_mul, ← restrictLin_apply, map_add] at *
    rw [hx, hx', ← Finset.sum_add_distrib]
  | single n k =>
    induction y using MonoidAlgebra.induction_linear with
    | zero => simp [← restrictLin_apply]
    | add y y' hy hy' =>
      simp only [mul_add, ← restrictLin_apply, map_add] at *
      rw [hy, hy', ← Finset.sum_add_distrib]
    | single n' l =>
      simp only [MonoidAlgebra.single_mul_single, restrictCoeff_single, map_mul,
        Matrix.mul_apply]
      exact map_sum (MonoidAlgebra.singleAddHom (n * n')) _ _

theorem restrictCoeff_zero (a c : ι) :
    restrictCoeff b a c (0 : MonoidAlgebra K N) = 0 := map_zero (restrictLin b a c)

theorem restrictCoeff_one (a c : ι) :
    restrictCoeff b a c (1 : MonoidAlgebra K N) = if a = c then 1 else 0 := by
  rw [MonoidAlgebra.one_def, restrictCoeff_single, map_one, Matrix.one_apply]
  split_ifs <;> simp [MonoidAlgebra.one_def]

theorem restrictCoeff_p (s : AlgebraicInput K N I V) (v : V) (a c : ι) :
    restrictCoeff b a c (s.p v) = if a = c then (s.κ : F)⁻¹ •
      (letI := s.finiteJ v
       letI := Fintype.ofFinite (s.J v)
       ∑ g : s.J v, MonoidAlgebra.single (g : N) 1) else 0 := by
  rw [s.p_average v]
  have h : ((s.κ : K)⁻¹) = algebraMap F K (s.κ : F)⁻¹ := by simp
  rw [h, algebraMap_smul, ← restrictLin_apply, map_smul, map_sum]
  simp only [restrictLin_apply, restrictCoeff_single, map_one, Matrix.one_apply]
  split_ifs <;> simp

end RestrictAux

/-- **Restriction of scalars.** The algebraic input over the subfield `F` obtained from `s`. -/
def restrictScalars {F ι : Type} [Field F] [Finite F] [Algebra F K] [Fintype ι] [Nonempty ι]
    (b : Module.Basis ι F K) (s : AlgebraicInput K N I V) :
    AlgebraicInput F N (I × ι) (V × ι) where
  κ := s.κ
  J := fun vj => s.J vj.1
  finiteJ := fun vj => s.finiteJ vj.1
  cardJ := fun vj => s.cardJ vj.1
  κ_ne_zero := by
    intro h
    apply s.κ_ne_zero
    simpa using congrArg (algebraMap F K) h
  p := fun vj => (s.κ : F)⁻¹ •
    (letI := s.finiteJ vj.1
     letI := Fintype.ofFinite (s.J vj.1)
     ∑ g : s.J vj.1, MonoidAlgebra.single (g : N) 1)
  p_average := fun _ => rfl
  p_idempotent := by
    intro vj
    obtain ⟨v, a⟩ := vj
    have h := congrArg (restrictCoeff b a a) (s.p_idempotent v)
    rw [restrictCoeff_mul] at h
    simpa [restrictCoeff_p] using h
  U := fun ia vc => restrictCoeff b ia.2 vc.2 (s.U ia.1 vc.1)
  T := fun vc ia => restrictCoeff b vc.2 ia.2 (s.T vc.1 ia.1)
  UP := by
    refine Matrix.ext fun ⟨i, a⟩ ⟨v, c⟩ => ?_
    refine Matrix.mul_apply.trans ?_
    have h := congrFun (congrFun s.UP i) v
    rw [Matrix.mul_apply] at h
    simp only [Matrix.diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true] at h ⊢
    conv_rhs => rw [← h]
    rw [restrictCoeff_mul]
    simp [restrictCoeff_p]
  PT := by
    refine Matrix.ext fun ⟨v, c⟩ ⟨i, a⟩ => ?_
    refine Matrix.mul_apply.trans ?_
    have h := congrFun (congrFun s.PT v) i
    rw [Matrix.mul_apply] at h
    simp only [Matrix.diagonal_apply, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
      ite_true] at h ⊢
    conv_rhs => rw [← h]
    rw [restrictCoeff_mul]
    simp [restrictCoeff_p]
  UT := by
    refine Matrix.ext fun ⟨i, a⟩ ⟨i', a'⟩ => ?_
    refine Matrix.mul_apply.trans ?_
    rw [Fintype.sum_prod_type]
    have h := congrFun (congrFun s.UT i) i'
    rw [Matrix.mul_apply] at h
    dsimp only
    have key : ∀ v, ∑ c, restrictCoeff b a c (s.U i v) * restrictCoeff b c a' (s.T v i') =
        restrictLin b a a' (s.U i v * s.T v i') := fun v => (restrictCoeff_mul b a a' _ _).symm
    simp only [key]
    rw [← map_sum, h, restrictLin_apply]
    simp only [Matrix.one_apply, Prod.mk.injEq]
    by_cases hi : i = i' <;> by_cases ha : a = a' <;> simp [hi, ha, restrictCoeff_one, restrictCoeff_zero]
  surplus := by
    rw [Fintype.card_prod, Fintype.card_prod, ← mul_assoc]
    exact Nat.mul_lt_mul_of_pos_right s.surplus Fintype.card_pos

@[simp] theorem restrictScalars_J {F ι : Type} [Field F] [Finite F] [Algebra F K] [Fintype ι]
    [Nonempty ι] (b : Module.Basis ι F K) (s : AlgebraicInput K N I V) (vj : V × ι) :
    (restrictScalars b s).J vj = s.J vj.1 := rfl

end Collapse
