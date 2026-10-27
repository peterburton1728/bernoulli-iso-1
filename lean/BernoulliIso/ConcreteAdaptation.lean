module

public import BernoulliIso.ConcreteTower
public import BernoulliIso.LocalChartMeasurability

/-!
The primitive inverse rows of the actual construction use only the
specified fresh stream in the original D-component. No adaptation premise
is imposed on these rows: it is derived from their explicit rank formulas.
-/

@[expose] public section
noncomputable section
open MeasureTheory
open scoped BigOperators Classical

namespace BernoulliIso.AlgebraicInput

variable {K N I V : Type*} [Field K] [Fintype K]
  [Group N] [Countable N] [Fintype I] [Fintype V] [Nonempty I] [Nonempty V]
variable (s : AlgebraicInput K N I V)
  [MeasurableSpace K] [MeasurableSingletonClass K] [LinearOrder K]

/-- An insertion coefficient is a fixed function of the actual fresh rank.
Its possible nonzero location is the deterministic quotient image. -/
theorem stageInsertion_coeff_fresh_measurable (n : ℕ)
    (a : s.stageCoordinates n) (b : s.stageCoordinates (n + 1))
    (g : Ambient.G N)
    (ha : Subgroup.quotientMapOfLE (s.stageH_le_D n) a.2 = QuotientGroup.mk g) :
    Measurable[MeasurableSpace.comap
      ((Ambient.markerGeometry N).freshRead g (2 * n) ∘
        (Subtype.val : s.markerSpace → Ambient.G N → K)) inferInstance]
      (fun ω => SparseRows.insertionRows (K := K) (s.stageSelection ω n) a b) := by
  let : MeasurableSpace s.markerSpace := MeasurableSpace.comap
    ((Ambient.markerGeometry N).freshRead g (2 * n) ∘ Subtype.val) inferInstance
  let target : s.stageCoordinates (n + 1) :=
    (a.1, Subgroup.quotientMapOfLE (s.stageH_step n) a.2)
  let f : Fin (StageSchedule.discarded s.rowConstant n + 1) → K := fun j =>
    if j = 0 then (Finsupp.single target (1 : K)) b else 0
  have hr := CosetCoordinates.sortedCosetChart_rank_fresh_measurable (K := K)
    (Ambient.markerGeometry N) (s.stageH n) (s.stageH (n + 1))
    (s.stageH_step n) (s.stageH_le_D (n + 1)) (s.stageH_quotient_card n)
    g a.2 ha (2 * n)
  have hf := (measurable_of_countable f).comp hr
  convert hf using 1
  funext ω
  by_cases h : (CosetCoordinates.sortedCosetChart (Ambient.markerGeometry N)
      (s.stageH n) (s.stageH (n + 1)) (s.stageH_step n)
      (s.stageH_le_D (n + 1)) (s.stageH_quotient_card n) (2 * n) ω a.2).2 = 0
  · simp [stageSelection, Regroup.selected, stageRegroupChart,
      SparseRows.insertionRows, f, target, h]
    rfl
  · simp [stageSelection, Regroup.selected, stageRegroupChart,
      SparseRows.insertionRows, f, target, h]

/-- Every coefficient of the actual algebraic split section is a fixed
function of its one fresh chart rank. Its finite group-ring coefficients
and right-coset moves are deterministic. -/
theorem stageSplitRows_coeff_fresh_measurable (n : ℕ)
    (a b : s.stageCoordinates (n + 1)) (g : Ambient.G N)
    (ha : Subgroup.quotientMapOfLE (s.stageH_le_D (n + 1)) a.2 = QuotientGroup.mk g) :
    Measurable[MeasurableSpace.comap
      ((Ambient.markerGeometry N).freshRead g (2 * n + 1) ∘
        (Subtype.val : s.markerSpace → Ambient.G N → K)) inferInstance]
      (fun ω => s.stageSplitRows ω n a b) := by
  let : MeasurableSpace s.markerSpace := MeasurableSpace.comap
    ((Ambient.markerGeometry N).freshRead g (2 * n + 1) ∘ Subtype.val) inferInstance
  let f : Fin s.κ → K := fun j =>
    (∑ i : I, Sum.casesOn (motive := fun _ => s.stageCoordinates (n + 1) →₀ K)
      (s.outputSlots (j, i))
      (fun w => (s.T a.1 i).coeff.mapDomain
          (fun u => (w, CosetOperators.rightCoset (s.stageH (n + 1)) (Ambient.includeN N)
            (s.ambient_commutes (s.stageLevel (n + 1))) u a.2)))
      (fun _ => 0)) b
  have hr := CosetCoordinates.sortedCosetChart_rank_fresh_measurable (K := K)
    (Ambient.markerGeometry N) (Ambient.Hseq N (s.stageLevel (n + 1)))
    (Ambient.Hseq N (s.stageLevel (n + 1)) ⊔ s.ambientJ a.1) le_sup_left
    (s.ambient_join_le_D (s.stageLevel (n + 1)) a.1)
    (s.ambient_join_quotient_card (s.stageLevel (n + 1)) a.1)
    g a.2 ha (2 * n + 1)
  have hf := (measurable_of_countable f).comp hr
  convert hf using 1
  funext ω
  dsimp only [stageSplitRows, splitSectionRow, ambientSplitCharts,
    Function.comp_apply, f, stageH, Ambient.markerGeometry]
  unfold keepTracks.match_1
  rfl

end BernoulliIso.AlgebraicInput

#print axioms BernoulliIso.AlgebraicInput.stageInsertion_coeff_fresh_measurable
#print axioms BernoulliIso.AlgebraicInput.stageSplitRows_coeff_fresh_measurable
