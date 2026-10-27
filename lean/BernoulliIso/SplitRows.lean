module

public import BernoulliIso.ConcreteSplit
public import BernoulliIso.ConcreteRows

/-! The finite rows of the amplified split's actual zero-output inverse section. -/

@[expose] public section
noncomputable section
open scoped BigOperators Classical

namespace BernoulliIso.AlgebraicInput

variable {K N I V G : Type*} [Field K] [Finite K]
  [Group N] [Countable N] [Fintype I] [Fintype V] [Nonempty I] [Nonempty V] [Group G]
variable (s : AlgebraicInput K N I V) (H : Subgroup G) (ι : N →* G)
  (commutes : ∀ h ∈ H, ∀ n, Commute h (ι n))

def keepTracks (f : V → G ⧸ H → K) (c : Fin s.κ) (i : I) : G ⧸ H → K :=
  match s.outputSlots (c, i) with
  | Sum.inl v => f v
  | Sum.inr _ => 0

def splitSection
    (charts : ∀ v, (G ⧸ H) ≃ (G ⧸ (H ⊔ (s.J v).map ι)) × Fin s.κ) :
    Module.End K (V → G ⧸ H → K) :=
  FiniteStages.inverseSection (s.expandedSplit H ι commutes charts)

theorem splitSection_apply
    (charts : ∀ v, (G ⧸ H) ≃ (G ⧸ (H ⊔ (s.J v).map ι)) × Fin s.κ)
    (hfirst : ∀ v x, (charts v x).1 =
      Subgroup.quotientMapOfLE (show H ≤ H ⊔ (s.J v).map ι from le_sup_left) x)
    (f : V → G ⧸ H → K) (v : V) (x : G ⧸ H) :
    s.splitSection H ι commutes charts f v x =
      CosetOperators.matrix H ι commutes s.T
        (s.keepTracks H f ((charts v x).2)) v x := by
  have htracks :
      (FiniteStages.splitTracks (K := K) (S := G ⧸ H) s.outputSlots).symm (f, 0) =
        s.keepTracks H f := by
    funext c i
    change Sum.elim f (0 : Fin s.excess → G ⧸ H → K) (s.outputSlots (c, i)) = _
    unfold keepTracks
    cases s.outputSlots (c, i) <;> rfl
  change s.rangeChart H ι commutes charts
    (fun c => (s.concreteSplit H ι commutes).linearEquiv.symm
      ((FiniteStages.splitTracks (K := K) (S := G ⧸ H) s.outputSlots).symm (f, 0) c,
        0)) v x = _
  rw [htracks]
  rw [s.rangeChart_apply H ι commutes charts hfirst]
  change ((s.concreteSplit H ι commutes).T
    (s.keepTracks H f ((charts v x).2)) + 0) v x = _
  rw [add_zero]
  rfl

def splitSectionRow
    (charts : ∀ v, (G ⧸ H) ≃ (G ⧸ (H ⊔ (s.J v).map ι)) × Fin s.κ)
    (v : V) (x : G ⧸ H) : (V × (G ⧸ H)) →₀ K :=
  ∑ i : I, match s.outputSlots ((charts v x).2, i) with
    | Sum.inl w => (s.T v i).coeff.mapDomain
        (fun n => (w, CosetOperators.rightCoset H ι commutes n x))
    | Sum.inr _ => 0

theorem eval_splitSectionRow
    (charts : ∀ v, (G ⧸ H) ≃ (G ⧸ (H ⊔ (s.J v).map ι)) × Fin s.κ)
    (hfirst : ∀ v x, (charts v x).1 =
      Subgroup.quotientMapOfLE (show H ≤ H ⊔ (s.J v).map ι from le_sup_left) x)
    (f : V → G ⧸ H → K) (v : V) (x : G ⧸ H) :
    SparseRows.eval (s.splitSectionRow H ι commutes charts v x) (fun p => f p.1 p.2) =
      s.splitSection H ι commutes charts f v x := by
  rw [s.splitSection_apply H ι commutes charts hfirst]
  change SparseRows.evalHom (fun p : V × (G ⧸ H) => f p.1 p.2)
    (s.splitSectionRow H ι commutes charts v x) = _
  rw [splitSectionRow, map_sum]
  simp only [CosetOperators.matrix_apply, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  cases hs : s.outputSlots ((charts v x).2, i) with
  | inl w =>
    change SparseRows.eval ((s.T v i).coeff.mapDomain
      (fun n => (w, CosetOperators.rightCoset H ι commutes n x)))
        (fun p => f p.1 p.2) = _
    rw [SparseRows.eval, Finsupp.sum_mapDomain_index
      (fun _ => zero_mul _) (fun _ _ _ => add_mul ..)]
    simp only [keepTracks, hs, CosetOperators.groupRing_apply]
  | inr w => simp [SparseRows.evalHom, keepTracks, hs]

set_option maxHeartbeats 800000 in
theorem card_support_splitSectionRow_le
    (charts : ∀ v, (G ⧸ H) ≃ (G ⧸ (H ⊔ (s.J v).map ι)) × Fin s.κ)
    (v : V) (x : G ⧸ H) :
    (s.splitSectionRow H ι commutes charts v x).support.card ≤
      ∑ i, (s.T v i).coeff.support.card := by
  unfold splitSectionRow
  calc
    _ ≤ (Finset.univ.biUnion fun i : I =>
        (match s.outputSlots ((charts v x).2, i) with
        | Sum.inl w => (s.T v i).coeff.mapDomain
            (fun n => (w, CosetOperators.rightCoset H ι commutes n x))
        | Sum.inr _ => 0).support).card :=
      Finset.card_le_card Finsupp.support_finsetSum
    _ ≤ ∑ i : I, (match s.outputSlots ((charts v x).2, i) with
        | Sum.inl w => (s.T v i).coeff.mapDomain
            (fun n => (w, CosetOperators.rightCoset H ι commutes n x))
        | Sum.inr _ => 0).support.card := Finset.card_biUnion_le
    _ ≤ ∑ i, (s.T v i).coeff.support.card := by
      apply Finset.sum_le_sum
      intro i _
      cases s.outputSlots ((charts v x).2, i) with
      | inl w => exact (Finset.card_le_card Finsupp.mapDomain_support).trans Finset.card_image_le
      | inr w => simp

end BernoulliIso.AlgebraicInput
