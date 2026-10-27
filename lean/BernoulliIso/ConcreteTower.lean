module

public import BernoulliIso.AmbientCharts
public import BernoulliIso.SplitRows
public import BernoulliIso.SplitDynamics
public import BernoulliIso.StageSchedule
public import BernoulliIso.Regroup

/-!
The actual extraction tower, with the lamp subgroups, marker ranks, rectangle
operators, retained slot, and repetition counts all specified by definitions.
-/

@[expose] public section
noncomputable section
open scoped BigOperators Classical

namespace BernoulliIso.AlgebraicInput

variable {K N I V : Type*} [Field K] [Fintype K]
  [Group N] [Countable N] [Fintype I] [Fintype V] [Nonempty I] [Nonempty V]
variable (s : AlgebraicInput K N I V)

def rowConstant : ℕ := 1 + ∑ v : V, ∑ i : I, (s.T v i).coeff.support.card

def stageLevel (n : ℕ) : ℕ := StageSchedule.level s.rowConstant n
def stageH (n : ℕ) : Subgroup (Ambient.G N) := Ambient.Hseq N (s.stageLevel n)
abbrev stageCoordinates (n : ℕ) := V × (Ambient.G N ⧸ s.stageH n)
abbrev stageSpace (n : ℕ) := s.stageCoordinates n → K

instance stageH_finite (n : ℕ) : Finite (s.stageH n) :=
  inferInstanceAs (Finite (Ambient.Hseq N (s.stageLevel n)))

theorem stageH_step (n : ℕ) : s.stageH n ≤ s.stageH (n + 1) :=
  Ambient.Hseq_mono N (StageSchedule.level_step s.rowConstant n)

theorem stageH_le_D (n : ℕ) : s.stageH n ≤ Ambient.D N :=
  Ambient.H_le_D N (Ambient.sites (s.stageLevel n))

theorem stageH_quotient_card (n : ℕ) :
    Nat.card (s.stageH (n + 1) ⧸ (s.stageH n).subgroupOf (s.stageH (n + 1))) =
      StageSchedule.discarded s.rowConstant n + 1 := by
  rw [StageSchedule.discarded_succ]
  change Nat.card (Ambient.Hseq N (StageSchedule.level s.rowConstant (n + 1)) ⧸
    (Ambient.Hseq N (StageSchedule.level s.rowConstant n)).subgroupOf
      (Ambient.Hseq N (StageSchedule.level s.rowConstant (n + 1)))) = _
  rw [StageSchedule.level_succ, Ambient.Hseq_quotient_card]
  rfl

variable [MeasurableSpace K] [MeasurableSingletonClass K] [LinearOrder K]

abbrev markerSpace (_s : AlgebraicInput K N I V) :=
  (Ambient.markerGeometry N).goodMarker (K := K)

def stageRegroupChart (n : ℕ) (ω : s.markerSpace) :
    s.stageCoordinates n ≃ s.stageCoordinates (n + 1) ×
      Fin (StageSchedule.discarded s.rowConstant n + 1) :=
  (Equiv.prodCongr (Equiv.refl V)
    (CosetCoordinates.sortedCosetChart (Ambient.markerGeometry N)
      (s.stageH n) (s.stageH (n + 1)) (s.stageH_step n) (s.stageH_le_D (n + 1))
      (s.stageH_quotient_card n) (2 * n) ω)).trans
    (Equiv.prodAssoc V _ _).symm

abbrev splitOutput (n : ℕ) :=
  (Fin s.excess → Ambient.G N ⧸ s.stageH (n + 1) → K) ×
    (Fin s.κ → s.residual (s.stageH (n + 1)) (Ambient.includeN N)
      (s.ambient_commutes (s.stageLevel (n + 1))))

def stageSplit (n : ℕ) (ω : s.markerSpace) :
    s.stageSpace (n + 1) ≃ₗ[K] (s.stageSpace (n + 1) × s.splitOutput n) :=
  (FiniteStages.uncurryLinear V (Ambient.G N ⧸ s.stageH (n + 1)) K).symm.trans <|
    (s.expandedSplit (s.stageH (n + 1)) (Ambient.includeN N)
      (s.ambient_commutes (s.stageLevel (n + 1)))
      (s.ambientSplitCharts (s.stageLevel (n + 1)) (2 * n + 1) ω)).trans <|
    (FiniteStages.uncurryLinear V (Ambient.G N ⧸ s.stageH (n + 1)) K).prodCongr
      (LinearEquiv.refl K _)

abbrev stageOutput (n : ℕ) :=
  (Fin (StageSchedule.repetitions s.rowConstant n) → s.splitOutput n) ×
    (Fin (StageSchedule.discarded s.rowConstant n) → s.stageSpace (n + 1))

def concreteStage (n : ℕ) (ω : s.markerSpace) :
    s.stageSpace n ≃ₗ[K] (s.stageSpace (n + 1) × s.stageOutput n) :=
  FiniteStages.regroupAndRepeat (Regroup.linearEquiv (s.stageRegroupChart n ω))
    (s.stageSplit n ω) (StageSchedule.repetitions s.rowConstant n)

def concreteTower (ω : s.markerSpace) : ExtractionTower K s.stageSpace s.stageOutput where
  stage n := s.concreteStage n ω

def stageSelection (ω : s.markerSpace) (n : ℕ) :
    s.stageCoordinates n → Option (s.stageCoordinates (n + 1)) :=
  Regroup.selected (s.stageRegroupChart n ω)

def stageSplitRows (ω : s.markerSpace) (n : ℕ)
    (a : s.stageCoordinates (n + 1)) : s.stageCoordinates (n + 1) →₀ K :=
  s.splitSectionRow (s.stageH (n + 1)) (Ambient.includeN N)
    (s.ambient_commutes (s.stageLevel (n + 1)))
    (s.ambientSplitCharts (s.stageLevel (n + 1)) (2 * n + 1) ω) a.1 a.2

theorem stageSplitRows_bound (ω : s.markerSpace) (n : ℕ)
    (a : s.stageCoordinates (n + 1)) :
    (s.stageSplitRows ω n a).support.card ≤ s.rowConstant := by
  refine (s.card_support_splitSectionRow_le _ _ _ _ a.1 a.2).trans ?_
  change (∑ i : I, (s.T a.1 i).coeff.support.card) ≤
    1 + ∑ v : V, ∑ i : I, (s.T v i).coeff.support.card
  have h : (∑ i : I, (s.T a.1 i).coeff.support.card) ≤
      ∑ v : V, ∑ i : I, (s.T v i).coeff.support.card :=
    Finset.single_le_sum (f := fun v : V => ∑ i : I, (s.T v i).coeff.support.card)
      (fun v _ => Nat.zero_le _) (Finset.mem_univ a.1)
  omega

theorem stageSplit_section_rows (ω : s.markerSpace) (n : ℕ) :
    FiniteStages.inverseSection (s.stageSplit n ω) = SparseRows.operator (s.stageSplitRows ω n) := by
  apply LinearMap.ext
  intro f
  funext a
  exact (s.eval_splitSectionRow _ _ _ _
    (s.ambientSplitCharts_fst (s.stageLevel (n + 1)) (2 * n + 1) ω)
    (fun v x => f (v, x)) a.1 a.2).symm

theorem concreteStage_section_rows (ω : s.markerSpace) (n : ℕ)
    (f : s.stageSpace (n + 1)) (a : s.stageCoordinates n) :
    (s.concreteTower ω).sectionMap n f a =
      SparseRows.eval (SparseRows.compose
        (SparseRows.insertionRows (s.stageSelection ω n) a)
        (SparseRows.iterateRows (s.stageSplitRows ω n)
          (StageSchedule.repetitions s.rowConstant n))) f := by
  change ((s.concreteStage n ω).symm (f, 0)) a = _
  rw [concreteStage, FiniteStages.regroupAndRepeat_symm_zero,
    Regroup.symm_zero_rows, s.stageSplit_section_rows]
  rw [SparseRows.eval_compose]
  congr 1
  funext b
  exact (SparseRows.eval_iterateRows _ _ f b).symm

end BernoulliIso.AlgebraicInput
