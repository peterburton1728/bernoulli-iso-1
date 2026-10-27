module

public import BernoulliIso.InputRange
public import BernoulliIso.FiniteStages
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
The manuscript's amplified split, on the actual configuration spaces.
The only marker input here is a family of finite coset-coordinate charts.
-/

@[expose] public section
noncomputable section
open scoped Classical

namespace BernoulliIso.AlgebraicInput

variable {K N I V G : Type*} [Field K] [Finite K]
  [Group N] [Countable N] [Fintype I] [Fintype V] [Nonempty I] [Nonempty V] [Group G]
variable (s : AlgebraicInput K N I V)

def excess : ℕ := s.κ * Fintype.card I - Fintype.card V

theorem excess_pos : 0 < s.excess := Nat.sub_pos_of_lt s.surplus

def outputSlots : (Fin s.κ × I) ≃ V ⊕ Fin s.excess :=
  (Equiv.prodCongr (Equiv.refl (Fin s.κ)) (Fintype.equivFin I)).trans <|
    finProdFinEquiv.trans <|
    (finCongr (show s.κ * Fintype.card I = Fintype.card V + s.excess from
      (Nat.add_sub_of_le s.surplus.le).symm)).trans <|
    finSumFinEquiv.symm.trans <|
    Equiv.sumCongr (Fintype.equivFin V).symm (Equiv.refl (Fin s.excess))

variable (H : Subgroup G) (ι : N →* G)
  (commutes : ∀ h ∈ H, ∀ n, Commute h (ι n))

/-- A literal rearrangement of scalar coordinates, using the finite coset charts. -/
def reorderCosets
    (charts : ∀ v, (G ⧸ H) ≃ (G ⧸ (H ⊔ (s.J v).map ι)) × Fin s.κ) :
    (Fin s.κ → ∀ v, G ⧸ (H ⊔ (s.J v).map ι) → K) ≃ₗ[K] (V → G ⧸ H → K) where
  toFun f v x := f ((charts v x).2) v ((charts v x).1)
  invFun f c v x := f v ((charts v).symm (x, c))
  left_inv f := by
    funext c v x
    change f ((charts v ((charts v).symm (x, c))).2) v
      ((charts v ((charts v).symm (x, c))).1) = f c v x
    rw [Equiv.apply_symm_apply]
  right_inv f := by
    funext v x
    change f v ((charts v).symm ((charts v x).1, (charts v x).2)) = f v x
    rw [Prod.mk.eta, Equiv.symm_apply_apply]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def rangeChart
    (charts : ∀ v, (G ⧸ H) ≃ (G ⧸ (H ⊔ (s.J v).map ι)) × Fin s.κ) :
    (Fin s.κ → (s.concreteSplit H ι commutes).P.range) ≃ₗ[K] (V → G ⧸ H → K) :=
  (LinearEquiv.piCongrRight fun _ : Fin s.κ =>
    (s.cosetProductRangeEquiv H ι commutes).symm).trans (s.reorderCosets H ι charts)

/-- A chart only chooses the copy; it evaluates the invariant function at
the original site. This is the finite-row bound's crucial formula. -/
theorem rangeChart_apply
    (charts : ∀ v, (G ⧸ H) ≃ (G ⧸ (H ⊔ (s.J v).map ι)) × Fin s.κ)
    (hfirst : ∀ v x, (charts v x).1 =
      Subgroup.quotientMapOfLE (show H ≤ H ⊔ (s.J v).map ι from le_sup_left) x)
    (f : Fin s.κ → (s.concreteSplit H ι commutes).P.range) (v : V) (x : G ⧸ H) :
    s.rangeChart H ι commutes charts f v x = (f ((charts v x).2)).val v x := by
  change (s.cosetProductRangeEquiv H ι commutes).symm (f ((charts v x).2)) v
    (charts v x).1 = _
  rw [hfirst, s.cosetProductRangeEquiv_symm_apply]

/-- The exact split X_H(d) ≃ X_H(d) × X_H(κm-d) × Z_H. -/
def expandedSplit
    (charts : ∀ v, (G ⧸ H) ≃ (G ⧸ (H ⊔ (s.J v).map ι)) × Fin s.κ) :
    (V → G ⧸ H → K) ≃ₗ[K]
      ((V → G ⧸ H → K) × ((Fin s.excess → G ⧸ H → K) ×
        (Fin s.κ → s.residual H ι commutes))) :=
  FiniteStages.amplifiedSplit (s.concreteSplit H ι commutes)
    (s.rangeChart H ι commutes charts) s.outputSlots

section Topology

variable [TopologicalSpace K]

theorem continuous_reorderCosets
    (charts : ∀ v, (G ⧸ H) ≃ (G ⧸ (H ⊔ (s.J v).map ι)) × Fin s.κ) :
    Continuous (s.reorderCosets H ι charts) := by
  apply continuous_pi
  intro v
  apply continuous_pi
  intro x
  exact (continuous_apply ((charts v x).1)).comp
    ((continuous_apply v).comp (continuous_apply ((charts v x).2)))

theorem continuous_reorderCosets_symm
    (charts : ∀ v, (G ⧸ H) ≃ (G ⧸ (H ⊔ (s.J v).map ι)) × Fin s.κ) :
    Continuous (s.reorderCosets H ι charts).symm := by
  apply continuous_pi
  intro c
  apply continuous_pi
  intro v
  apply continuous_pi
  intro x
  exact (continuous_apply ((charts v).symm (x, c))).comp (continuous_apply v)

end Topology
end BernoulliIso.AlgebraicInput
