module

public import BernoulliIso.GroupRingAction
public import BernoulliIso.SparseRows

/-!
The actual finite rows of right convolution and rectangular group-ring
operators. Coefficients at colliding cosets are added, so these are genuine
rows even when the source-group action on cosets is not free.
-/

@[expose] public section

noncomputable section
open scoped BigOperators

namespace BernoulliIso.CosetOperators

variable {K N G : Type*} [CommRing K] [Group N] [Group G]
variable (H : Subgroup G) (ι : N →* G)
  (commutes : ∀ h ∈ H, ∀ n, Commute h (ι n))

def groupRingRow (a : MonoidAlgebra K N) (x : G ⧸ H) : (G ⧸ H) →₀ K :=
  a.coeff.mapDomain (fun n => rightCoset H ι commutes n x)

theorem eval_groupRingRow (a : MonoidAlgebra K N) (x : G ⧸ H) (f : G ⧸ H → K) :
    SparseRows.eval (groupRingRow H ι commutes a x) f = groupRing H ι commutes a f x := by
  rw [SparseRows.eval, groupRingRow,
    Finsupp.sum_mapDomain_index (fun _ => zero_mul _) (fun _ _ _ => add_mul ..)]
  exact (groupRing_apply H ι commutes a f x).symm

theorem card_support_groupRingRow_le (a : MonoidAlgebra K N) (x : G ⧸ H) :
    (groupRingRow H ι commutes a x).support.card ≤ a.coeff.support.card := by
  classical
  exact (Finset.card_le_card Finsupp.mapDomain_support).trans (Finset.card_image_le)

def matrixRow {I J : Type*} [Fintype J] (B : Matrix I J (MonoidAlgebra K N))
    (i : I) (x : G ⧸ H) : (J × (G ⧸ H)) →₀ K :=
  ∑ j, (B i j).coeff.mapDomain (fun n => (j, rightCoset H ι commutes n x))

theorem eval_matrixRow {I J : Type*} [Fintype J]
    (B : Matrix I J (MonoidAlgebra K N)) (i : I) (x : G ⧸ H)
    (f : J → G ⧸ H → K) :
    SparseRows.eval (matrixRow H ι commutes B i x) (fun p => f p.1 p.2) =
      matrix H ι commutes B f i x := by
  change SparseRows.evalHom (fun p : J × (G ⧸ H) => f p.1 p.2)
    (matrixRow H ι commutes B i x) = _
  rw [matrixRow, map_sum]
  simp only [matrix_apply, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  change SparseRows.eval ((B i j).coeff.mapDomain
    (fun n => (j, rightCoset H ι commutes n x))) (fun p => f p.1 p.2) = _
  rw [SparseRows.eval,
    Finsupp.sum_mapDomain_index (fun _ => zero_mul _) (fun _ _ _ => add_mul ..)]
  exact (groupRing_apply H ι commutes (B i j) (f j) x).symm

/-- One deterministic bound for every spatial translate of a matrix row. -/
theorem card_support_matrixRow_le {I J : Type*} [Fintype J]
    (B : Matrix I J (MonoidAlgebra K N)) (i : I) (x : G ⧸ H) :
    (matrixRow H ι commutes B i x).support.card ≤ ∑ j, (B i j).coeff.support.card := by
  classical
  calc
    (matrixRow H ι commutes B i x).support.card ≤
        (Finset.univ.biUnion fun j =>
          ((B i j).coeff.mapDomain
            (fun n => (j, rightCoset H ι commutes n x))).support).card :=
      Finset.card_le_card Finsupp.support_finsetSum
    _ ≤ ∑ j, ((B i j).coeff.mapDomain
        (fun n => (j, rightCoset H ι commutes n x))).support.card :=
      Finset.card_biUnion_le
    _ ≤ ∑ j, (B i j).coeff.support.card := by
      apply Finset.sum_le_sum
      intro j _
      exact (Finset.card_le_card Finsupp.mapDomain_support).trans Finset.card_image_le

/-- The bound may be chosen simultaneously for all track rows and sites. -/
theorem card_support_matrixRow_uniform {I J : Type*} [Fintype I] [Fintype J]
    (B : Matrix I J (MonoidAlgebra K N)) (i : I) (x : G ⧸ H) :
    (matrixRow H ι commutes B i x).support.card ≤
      ∑ i, ∑ j, (B i j).coeff.support.card := by
  exact (card_support_matrixRow_le H ι commutes B i x).trans
    (Finset.single_le_sum (f := fun i : I => ∑ j, (B i j).coeff.support.card)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))

end BernoulliIso.CosetOperators
