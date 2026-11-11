module

public import UpstreamConstruction

@[expose] public section

section

/-!
Adapter from the pinned upstream construction to the exact subgroup-average
rectangle. The group here is the early glued group, before the HNN extension.
-/

noncomputable section
open scoped Classical BigOperators

namespace BernoulliIso.Upstream
open OAI.KaplanskyCounterexample
open Prescription.Output

abbrev K := Coeff
abbrev N := AssignedDevelopment.Base Inc ell assignment
abbrev A := GluedGroup.PointGroup ell
abbrev I := Slots
abbrev V := Prescription.Output.V

/- Match the concrete subtype enumeration context in PrescribedData.  Its
local classical subfield equality affects the finite subtype enumerations
appearing in matrix sums.  Export these same enumerations so downstream
uses of the closed input have a single coherent instance. -/
local instance (priority := 3000) : DecidableEq Subfield := Classical.decEq _
local instance (priority := 3000) : DecidableEq V := Classical.decEq _

instance (priority := 3000) finiteSlots : Fintype I := inferInstance
instance (priority := 3000) finiteColumns : Fintype V := inferInstance

instance : Countable N := by
  exact Function.Surjective.countable (PresentedGroup.mk_surjective _)

instance : Nonempty I := ⟨i0⟩
instance : Nonempty V := ⟨v0⟩

def point (v : V) : A →* N := AssignedDevelopment.point Inc ell assignment v

theorem point_injective (v : V) : Function.Injective (point v) :=
  AssignedDevelopment.point_injective Inc ell assignment nonempty_Inc girth_Inc v

def J (v : V) : Subgroup N := (point v).range

instance finiteJ (v : V) : Finite (J v) :=
  Finite.of_surjective (point v).rangeRestrict (point v).rangeRestrict_surjective

def pointEquiv (v : V) : A ≃* J v := MonoidHom.ofInjective (point_injective v)

theorem cardJ (v : V) : Nat.card (J v) = ell ^ 2 := by
  rw [← Nat.card_congr (pointEquiv v).toEquiv, Nat.card_eq_fintype_card]
  simp [A, GluedGroup.PointGroup]

theorem ell_cast : (ell : K) = 1 :=
  natCast_eq_one_of_odd_of_two_eq_zero
    (Prescription.prime_odd h.val h.property) CharTwo.two_eq_zero

theorem κ_cast : (ell ^ 2 : K) = 1 := by simp [ell_cast]

theorem cardA_cast : (Fintype.card A : K) = 1 := by
  simp [A, GluedGroup.PointGroup, ell_cast]

def p (v : V) : MonoidAlgebra K N := CharacterIdempotents.pushed (point v) 1

theorem p_sum (v : V) : p v = ∑ a : A, MonoidAlgebra.single (point v a) 1 := by
  unfold p
  rw [CharacterIdempotents.pushed_eq_sum, cardA_cast]
  simp

theorem p_average (v : V) : p v = ((ell ^ 2 : ℕ) : K)⁻¹ •
    (letI := Fintype.ofFinite (J v)
     ∑ g : J v, MonoidAlgebra.single (g : N) 1) := by
  letI := Fintype.ofFinite (J v)
  rw [p_sum]
  simp only [Nat.cast_pow, κ_cast, inv_one, one_smul]
  exact Equiv.sum_comp (pointEquiv v).toEquiv
    (fun g : J v => MonoidAlgebra.single (g : N) (1 : K))

theorem p_idempotent (v : V) : p v * p v = p v :=
  CharacterIdempotents.pushed_idempotent (point v) 1 (by
    rw [cardA_cast]
    exact one_ne_zero)

def lineSum (f : F) : MonoidAlgebra K N :=
  ∑ c : Multiplicative (ZMod ell),
    MonoidAlgebra.single (AssignedDevelopment.line Inc ell assignment nonempty_Inc f c) 1

theorem p_decomposition (v : V) :
    p v = 1 + ∑ f : { f : F // v ∈ Inc f }, (lineSum f.val - 1) := by
  rw [p_sum]
  simpa only [lineSum, point, N] using
    (AssignedDevelopment.subgroup_decomposition (K := K)
      Inc ell assignment nonempty_Inc v)

theorem X_global_one : X * X.transpose = 1 := by
  rw [X_global]
  ext i j
  exact CharTwo.neg_eq _

theorem rectangle_identities :
    Rectangular.U X p * Matrix.diagonal p = Rectangular.U X p ∧
    Matrix.diagonal p * Rectangular.T X p = Rectangular.T X p ∧
    Rectangular.U X p * Rectangular.T X p = 1 := by
  have hrect := Rectangular.identities X p lineSum Inc p_idempotent p_decomposition
    (by
      ext i j
      have hentry := congrFun (congrFun X_global_one i) j
      by_cases hij : i = j <;> simpa [Matrix.one_apply, hij] using hentry) X_local
  refine ⟨hrect.1, hrect.2.1, ?_⟩
  apply Matrix.ext
  intro i j
  have hentry := congrFun (congrFun hrect.2.2 i) j
  by_cases hij : i = j <;> simpa [Matrix.one_apply, hij] using hentry

theorem strict_surplus_arithmetic {Q m ell : ℕ} (hm : 0 < m) (hmQ : m ≤ Q)
    (hell : 3 ≤ ell) (lower : 2 * Q ≤ m * (ell + 1) ^ 2) :
    Q - m < m * ell ^ 2 := by
  have hsq : (ell + 1) ^ 2 < 2 * (ell ^ 2 + 1) := by
    have hmul : 2 * ell ≤ ell * ell := Nat.mul_le_mul_right ell (by omega)
    nlinarith
  have hscaled := Nat.mul_lt_mul_of_pos_left hsq hm
  have htotal : Q < m * ell ^ 2 + m := by nlinarith
  omega

theorem strict_surplus : Fintype.card V < ell ^ 2 * Fintype.card I := by
  rw [V_card, Fintype.card_coe, Nat.mul_comm]
  apply strict_surplus_arithmetic
  · simpa only [Fintype.card_coe] using sizes.1
  · exact (Finset.card_le_univ holes).trans_eq ambient_card
  · exact Prescription.prime_ge h.val h.property
  · exact success.lower

/-- The entire algebraic input, assembled from checked upstream proof terms. -/
def algebraicInput : BernoulliIso.AlgebraicInput K N I V where
  κ := ell ^ 2
  J := J
  finiteJ := finiteJ
  cardJ := cardJ
  κ_ne_zero := by simpa only [Nat.cast_pow, κ_cast] using (one_ne_zero : (1 : K) ≠ 0)
  p := p
  p_average := p_average
  p_idempotent := p_idempotent
  U := Rectangular.U X p
  T := Rectangular.T X p
  UP := rectangle_identities.1
  PT := rectangle_identities.2.1
  UT := by
    apply Matrix.ext
    intro i j
    have hentry := congrFun (congrFun rectangle_identities.2.2 i) j
    by_cases hij : i = j <;> simpa [Matrix.one_apply, hij] using hentry
  surplus := strict_surplus

#print axioms point_injective
#print axioms rectangle_identities
#print axioms strict_surplus
#print axioms algebraicInput

end BernoulliIso.Upstream
end
