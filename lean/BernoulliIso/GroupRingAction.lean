module

public import BernoulliIso.AlgebraicSplit
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.GroupTheory.Coset.Basic
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Topology.Algebra.Module.Basic

/-!
The actual right group-algebra operators on left coset configurations.
The ambient subgroup need not be normal: commutation with the source
group is precisely the hypothesis that makes the right operators descend.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace BernoulliIso

variable {K N G : Type*} [CommRing K] [Group N] [Group G]

namespace CosetOperators

variable (H : Subgroup G) (ι : N →* G)
  (commutes : ∀ h ∈ H, ∀ n, Commute h (ι n))

/-- Right translation of cosets by a source-group element. -/
def rightCoset (n : N) : G ⧸ H → G ⧸ H :=
  Quotient.map' (fun g => g * ι n) (by
    intro a b hab
    apply QuotientGroup.leftRel_apply.mpr
    have hh := QuotientGroup.leftRel_apply.mp hab
    have heq : (a * ι n)⁻¹ * (b * ι n) = a⁻¹ * b := by
      calc
        (a * ι n)⁻¹ * (b * ι n) = (ι n)⁻¹ * ((a⁻¹ * b) * ι n) := by
          simp only [mul_inv_rev, mul_assoc]
        _ = (ι n)⁻¹ * (ι n * (a⁻¹ * b)) := by rw [(commutes _ hh n).eq]
        _ = a⁻¹ * b := by simp
    simpa only [heq] using hh)

@[simp] theorem rightCoset_mk (n : N) (g : G) :
    rightCoset H ι commutes n (QuotientGroup.mk g) = QuotientGroup.mk (g * ι n) := rfl

@[simp] theorem rightCoset_one (x : G ⧸ H) :
    rightCoset H ι commutes 1 x = x := by
  induction x using QuotientGroup.induction_on with
  | H g => simp

theorem rightCoset_mul (n m : N) (x : G ⧸ H) :
    rightCoset H ι commutes (n * m) x =
      rightCoset H ι commutes m (rightCoset H ι commutes n x) := by
  induction x using QuotientGroup.induction_on with
  | H g => simp [mul_assoc]

theorem rightCoset_smul (a : G) (n : N) (x : G ⧸ H) :
    rightCoset H ι commutes n (a • x) = a • rightCoset H ι commutes n x := by
  induction x using QuotientGroup.induction_on with
  | H g => simp [mul_assoc]

/-- Pullback along right translation, as a linear endomorphism. -/
def rightTranslation (n : N) : Module.End K (G ⧸ H → K) where
  toFun f x := f (rightCoset H ι commutes n x)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem rightTranslation_apply (n : N) (f : G ⧸ H → K) (x : G ⧸ H) :
    rightTranslation H ι commutes n f x = f (rightCoset H ι commutes n x) := rfl

/-- The order of multiplication agrees with the manuscript's right-convolution convention. -/
def rightRepresentation : N →* Module.End K (G ⧸ H → K) where
  toFun := rightTranslation H ι commutes
  map_one' := by ext f x; simp
  map_mul' n m := by ext f x; simp [rightCoset_mul, Module.End.mul_apply]

/-- Finite right convolution on the actual coset configuration space. -/
def groupRing : MonoidAlgebra K N →ₐ[K] Module.End K (G ⧸ H → K) :=
  MonoidAlgebra.lift K _ N (rightRepresentation H ι commutes)

theorem groupRing_apply (a : MonoidAlgebra K N) (f : G ⧸ H → K) (x : G ⧸ H) :
    groupRing H ι commutes a f x =
      a.coeff.sum (fun n c => c * f (rightCoset H ι commutes n x)) := by
  simp [groupRing, MonoidAlgebra.lift_apply, Finsupp.sum, rightRepresentation,
    rightTranslation, LinearMap.sum_apply, Finset.sum_apply]

@[simp] theorem groupRing_single (n : N) (c : K) (f : G ⧸ H → K) (x : G ⧸ H) :
    groupRing H ι commutes (MonoidAlgebra.single n c) f x =
      c * f (rightCoset H ι commutes n x) := by
  simp [groupRing, rightRepresentation, rightTranslation]

/-- The left shift on coset configurations. -/
def leftShift (a : G) (f : G ⧸ H → K) (x : G ⧸ H) : K := f (a⁻¹ • x)

theorem groupRing_equivariant (a : MonoidAlgebra K N) (g : G) (f : G ⧸ H → K) :
    groupRing H ι commutes a (leftShift H g f) =
      leftShift H g (groupRing H ι commutes a f) := by
  funext x
  simp only [groupRing_apply, leftShift, rightCoset_smul]

section Matrix

variable {I J L : Type*}

/-- A finite matrix of group-ring elements acting on actual configuration tracks. -/
def matrix [Fintype J] (B : Matrix I J (MonoidAlgebra K N)) :
    (J → G ⧸ H → K) →ₗ[K] (I → G ⧸ H → K) where
  toFun f i := ∑ j, groupRing H ι commutes (B i j) (f j)
  map_add' f g := by
    funext i
    simp only [Pi.add_apply, map_add, Finset.sum_add_distrib]
  map_smul' c f := by
    funext i
    simp only [Pi.smul_apply, map_smul, Finset.smul_sum, RingHom.id_apply]

@[simp] theorem matrix_apply [Fintype J] (B : Matrix I J (MonoidAlgebra K N))
    (f : J → G ⧸ H → K) (i : I) :
    matrix H ι commutes B f i = ∑ j, groupRing H ι commutes (B i j) (f j) := rfl

theorem matrix_mul [Fintype J] [Fintype L]
    (B : Matrix I J (MonoidAlgebra K N)) (C : Matrix J L (MonoidAlgebra K N)) :
    matrix H ι commutes (B * C) =
      (matrix H ι commutes B).comp (matrix H ι commutes C) := by
  apply LinearMap.ext
  intro f
  funext i x
  simp only [LinearMap.comp_apply, matrix_apply, Matrix.mul_apply, map_sum, map_mul,
    LinearMap.sum_apply, Finset.sum_apply, Module.End.mul_apply]
  rw [Finset.sum_comm]

@[simp] theorem matrix_one [Fintype I] [DecidableEq I] :
    matrix (K := K) H ι commutes (1 : Matrix I I (MonoidAlgebra K N)) =
      LinearMap.id := by
  apply LinearMap.ext
  intro f
  funext i x
  simp only [matrix_apply, Finset.sum_apply, LinearMap.id_apply]
  rw [Finset.sum_eq_single i]
  · simp [Matrix.one_apply]
  · intro j _ hji
    simp [Matrix.one_apply, Ne.symm hji]
  · simp

theorem matrix_equivariant [Fintype J] (B : Matrix I J (MonoidAlgebra K N))
    (g : G) (f : J → G ⧸ H → K) :
    matrix H ι commutes B (fun j => leftShift H g (f j)) =
      fun i => leftShift H g (matrix H ι commutes B f i) := by
  funext i x
  simp only [matrix_apply, Finset.sum_apply, groupRing_equivariant, leftShift]

/-- The rectangle identities produce the concrete splitting data, with no
    extra operator-identity assumptions. -/
def splitData [Fintype I] [Fintype J] [DecidableEq I]
    (P : Matrix J J (MonoidAlgebra K N))
    (U : Matrix I J (MonoidAlgebra K N))
    (T : Matrix J I (MonoidAlgebra K N))
    (hPP : P * P = P) (hUP : U * P = U) (hPT : P * T = T) (hUT : U * T = 1) :
    SplitData K (J → G ⧸ H → K) (I → G ⧸ H → K) where
  P := matrix H ι commutes P
  U := matrix H ι commutes U
  T := matrix H ι commutes T
  PP x := by
    change ((matrix H ι commutes P).comp (matrix H ι commutes P)) x = _
    rw [← matrix_mul, hPP]
  UP x := by
    change ((matrix H ι commutes U).comp (matrix H ι commutes P)) x = _
    rw [← matrix_mul, hUP]
  PT x := by
    change ((matrix H ι commutes P).comp (matrix H ι commutes T)) x = _
    rw [← matrix_mul, hPT]
  UT x := by
    change ((matrix H ι commutes U).comp (matrix H ι commutes T)) x = _
    rw [← matrix_mul, hUT, matrix_one]
    rfl

end Matrix

section Topology

variable [TopologicalSpace K] [IsTopologicalRing K]

theorem continuous_groupRing (a : MonoidAlgebra K N) :
    Continuous (groupRing (K := K) H ι commutes a) := by
  apply continuous_pi
  intro x
  simp only [groupRing_apply, Finsupp.sum]
  exact continuous_finsetSum _ fun n _ => continuous_const.mul (continuous_apply _)

theorem continuous_matrix {I J : Type*} [Fintype J]
    (B : Matrix I J (MonoidAlgebra K N)) :
    Continuous (matrix H ι commutes B) := by
  apply continuous_pi
  intro i
  exact continuous_finsetSum _ fun j _ =>
    (continuous_groupRing H ι commutes (B i j)).comp (continuous_apply j)

end Topology

end CosetOperators
end BernoulliIso
