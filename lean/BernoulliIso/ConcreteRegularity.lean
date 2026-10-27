module

public import BernoulliIso.ConcreteTower
public import BernoulliIso.FiniteRegularity

/-! Continuity and joint measurability of the literal finite-stage tower. -/

@[expose] public section
noncomputable section
open MeasureTheory
open scoped Classical

set_option maxHeartbeats 400000

attribute [local irreducible] BernoulliIso.AlgebraicInput.outputSlots
  BernoulliIso.CosetCoordinates.sortedCosetChart

namespace BernoulliIso.AlgebraicInput

variable {K N I V : Type*} [Field K] [Fintype K]
  [Group N] [Countable N] [Fintype I] [Fintype V] [Nonempty I] [Nonempty V]
variable (s : AlgebraicInput K N I V)
  [MeasurableSpace K] [MeasurableSingletonClass K] [LinearOrder K]

section Topology
variable [TopologicalSpace K] [IsTopologicalRing K]

attribute [local irreducible] expandedSplit rangeChart

theorem continuous_stageSplit (n : ℕ) (ω : s.markerSpace) :
    Continuous (s.stageSplit n ω) := by
  have h := (s.continuous_expandedSplit (s.stageH (n + 1)) (Ambient.includeN N)
    (s.ambient_commutes (s.stageLevel (n + 1)))
    (s.ambientSplitCharts (s.stageLevel (n + 1)) (2 * n + 1) ω)).comp
    (show Continuous (fun f : s.stageSpace (n + 1) => fun v c => f (v, c)) from
      continuous_pi fun v => continuous_pi fun c => continuous_apply (v, c))
  exact (continuous_pi fun a : s.stageCoordinates (n + 1) => (continuous_apply a.2).comp
    ((continuous_apply a.1).comp h.fst)).prodMk h.snd

attribute [local irreducible] stageSplit stageRegroupChart Regroup.linearEquiv
  FiniteStages.regroupAndRepeat FiniteStages.iterateSplit

theorem continuous_concreteStage (n : ℕ) (ω : s.markerSpace) :
    Continuous (s.concreteStage n ω) := by
  exact FiniteStages.continuous_regroupAndRepeat
    (K := K) (X := s.stageSpace (n + 1)) (Y := s.splitOutput n)
    (X₀ := s.stageSpace n)
    (W := Fin (StageSchedule.discarded s.rowConstant n) → s.stageSpace (n + 1))
    (Regroup.linearEquiv (K := K) (s.stageRegroupChart n ω)) (s.stageSplit n ω)
    (Regroup.continuous_linearEquiv (K := K) (s.stageRegroupChart n ω))
    (s.continuous_stageSplit n ω) (StageSchedule.repetitions s.rowConstant n)

theorem continuous_concreteOutput (ω : s.markerSpace) (n : ℕ) :
    Continuous ((s.concreteTower ω).output n) :=
  ExtractionTower.continuous_output _ (fun n => s.continuous_concreteStage n ω) n

end Topology

section Measurability
variable [TopologicalSpace K] [DiscreteTopology K] [BorelSpace K]
  [IsTopologicalRing K]

variable [MeasurableSpace V] [MeasurableSingletonClass V]
local instance regularityQuotientMeasurable (H : Subgroup (Ambient.G N)) :
    MeasurableSpace (Ambient.G N ⧸ H) := ⊤
local instance regularityQuotientMeasurableSingleton (H : Subgroup (Ambient.G N)) :
    MeasurableSingletonClass (Ambient.G N ⧸ H) := ⟨fun _ => trivial⟩

theorem measurable_stageRegroupChart_symm (n : ℕ) :
    Measurable (fun p : s.markerSpace ×
      (s.stageCoordinates (n + 1) × Fin (StageSchedule.discarded s.rowConstant n + 1)) =>
      (s.stageRegroupChart n p.1).symm p.2) := by
  have h := CosetCoordinates.measurable_sortedCosetChart_symm (K := K)
    (Ambient.markerGeometry N) (s.stageH n) (s.stageH (n + 1))
    (s.stageH_step n) (s.stageH_le_D (n + 1)) (s.stageH_quotient_card n) (2 * n)
  change Measurable (fun p : s.markerSpace ×
      (s.stageCoordinates (n + 1) × Fin (StageSchedule.discarded s.rowConstant n + 1)) =>
    (p.2.1.1, (CosetCoordinates.sortedCosetChart (Ambient.markerGeometry N)
      (s.stageH n) (s.stageH (n + 1)) (s.stageH_step n) (s.stageH_le_D (n + 1))
      (s.stageH_quotient_card n) (2 * n) p.1).symm (p.2.1.2, p.2.2)))
  apply Measurable.prodMk
  · exact measurable_snd.fst.fst
  · exact h.comp (measurable_fst.prodMk
      (measurable_snd.fst.snd.prodMk measurable_snd.snd))

theorem measurable_stageRegroup (n : ℕ) :
    Measurable (fun p : s.markerSpace × s.stageSpace n =>
      Regroup.linearEquiv (s.stageRegroupChart n p.1) p.2) := by
  have hev : Measurable (fun p : s.stageSpace n × s.stageCoordinates n => p.1 p.2) :=
    measurable_from_prod_countable_left fun a => measurable_pi_apply a
  have hx (a : s.stageCoordinates (n + 1))
      (i : Fin (StageSchedule.discarded s.rowConstant n + 1)) :
      Measurable (fun p : s.markerSpace × s.stageSpace n =>
        p.2 ((s.stageRegroupChart n p.1).symm (a, i))) :=
    hev.comp (measurable_snd.prodMk
      ((s.measurable_stageRegroupChart_symm n).comp
        (measurable_fst.prodMk measurable_const)))
  exact (Measurable.of_eval fun a => hx a 0).prodMk
    (Measurable.of_eval fun i => Measurable.of_eval fun a => hx a i.succ)

theorem measurable_stageSplit (n : ℕ) :
    Measurable (fun p : s.markerSpace × s.stageSpace (n + 1) =>
      s.stageSplit n p.1 p.2) := by
  let H : Subgroup (Ambient.G N) := s.stageH (n + 1)
  let ι := Ambient.includeN N
  let commutes := s.ambient_commutes (s.stageLevel (n + 1))
  let charts := s.ambientSplitCharts (s.stageLevel (n + 1)) (2 * n + 1)
  have hev : Measurable (fun p : s.stageSpace (n + 1) ×
      s.stageCoordinates (n + 1) => p.1 p.2) :=
    measurable_from_prod_countable_left fun a => measurable_pi_apply a
  have hcopy (c : Fin s.κ) : Measurable
      (fun p : s.markerSpace × s.stageSpace (n + 1) =>
        ((s.rangeChart H ι commutes (charts p.1)).symm
          (fun v x => p.2 (v, x)) c).val) := by
    apply Measurable.of_eval
    intro v
    apply Measurable.of_eval
    intro x
    letI : Finite (H ⊔ s.ambientJ v : Subgroup (Ambient.G N)) :=
      s.ambient_join_finite (s.stageLevel (n + 1)) v
    have hi := CosetCoordinates.measurable_sortedCosetChart_symm (K := K)
      (Ambient.markerGeometry N) H (H ⊔ s.ambientJ v) le_sup_left
      (s.ambient_join_le_D (s.stageLevel (n + 1)) v)
      (s.ambient_join_quotient_card (s.stageLevel (n + 1)) v) (2 * n + 1)
    exact hev.comp (measurable_snd.prodMk
      (measurable_const.prodMk (hi.comp (measurable_fst.prodMk measurable_const))))
  have hu (c : Fin s.κ) := (s.continuous_U H ι commutes).measurable.comp (hcopy c)
  have hq (c : Fin s.κ) := (s.continuous_Q H ι commutes).measurable.comp (hcopy c)
  apply Measurable.prodMk
  · apply Measurable.of_eval
    intro a
    exact (measurable_pi_apply a.2).comp
      ((measurable_pi_apply (s.outputSlots.symm (Sum.inl a.1)).2).comp
        (hu (s.outputSlots.symm (Sum.inl a.1)).1))
  · apply Measurable.prodMk
    · apply Measurable.of_eval
      intro w
      apply Measurable.of_eval
      intro x
      exact (measurable_pi_apply x).comp
        ((measurable_pi_apply (s.outputSlots.symm (Sum.inr w)).2).comp
          (hu (s.outputSlots.symm (Sum.inr w)).1))
    · apply Measurable.of_eval
      intro c
      exact (hq c).subtype_mk

theorem measurable_concreteStage (n : ℕ) :
    Measurable (fun p : s.markerSpace × s.stageSpace n => s.concreteStage n p.1 p.2) := by
  exact FiniteStages.measurable_regroupAndRepeat
    (K := K) (Ω := s.markerSpace) (X := s.stageSpace (n + 1)) (Y := s.splitOutput n)
    (X₀ := s.stageSpace n)
    (W := Fin (StageSchedule.discarded s.rowConstant n) → s.stageSpace (n + 1))
    (fun ω => Regroup.linearEquiv (K := K) (s.stageRegroupChart n ω))
    (s.stageSplit n) (s.measurable_stageRegroup n) (s.measurable_stageSplit n)
    (StageSchedule.repetitions s.rowConstant n)

theorem measurable_concreteOutput (n : ℕ) :
    Measurable (fun p : s.markerSpace × s.stageSpace 0 =>
      (s.concreteTower p.1).output n p.2) :=
  ExtractionTower.measurable_output s.concreteTower s.measurable_concreteStage n

end Measurability
end BernoulliIso.AlgebraicInput

#print axioms BernoulliIso.AlgebraicInput.continuous_concreteOutput
#print axioms BernoulliIso.AlgebraicInput.measurable_concreteOutput
