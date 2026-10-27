module

public import BernoulliIso.ConcreteTower

/-! The actual actions, with covariance of every stage and the full extraction. -/

@[expose] public section
noncomputable section

namespace BernoulliIso
namespace FiniteStages

variable {K X Y G : Type*} [CommRing K]
  [AddCommGroup X] [AddCommGroup Y] [Module K X] [Module K Y]
  [Group G] [MulAction G X] [MulAction G Y]

theorem iterateSplit_covariant (e e' : X ≃ₗ[K] (X × Y)) (g : G)
    (he : ∀ x, e' (g • x) = g • e x) (k : ℕ) (x : X) :
    iterateSplit e' k (g • x) = g • iterateSplit e k x := by
  induction k with
  | zero =>
    apply Prod.ext
    · rfl
    · funext i; exact Fin.elim0 i
  | succ k ih =>
    change ((e' (iterateSplit e' k (g • x)).1).1,
      Fin.cons (α := fun _ : Fin (k + 1) => Y) (e' (iterateSplit e' k (g • x)).1).2
        (iterateSplit e' k (g • x)).2) = _
    rw [ih]
    change ((e' (g • (iterateSplit e k x).1)).1,
      Fin.cons (α := fun _ : Fin (k + 1) => Y) (e' (g • (iterateSplit e k x).1)).2
        (g • (iterateSplit e k x).2)) = _
    rw [he]
    apply Prod.ext
    · rfl
    · funext i
      cases i using Fin.cases <;> rfl

theorem regroupAndRepeat_covariant {X₀ W : Type*}
    [AddCommGroup X₀] [AddCommGroup W] [Module K X₀] [Module K W]
    [MulAction G X₀] [MulAction G W]
    (r r' : X₀ ≃ₗ[K] (X × W)) (e e' : X ≃ₗ[K] (X × Y)) (g : G)
    (hr : ∀ x, r' (g • x) = g • r x)
    (he : ∀ x, e' (g • x) = g • e x) (k : ℕ) (x : X₀) :
    regroupAndRepeat r' e' k (g • x) = g • regroupAndRepeat r e k x := by
  change ((iterateSplit e' k (r' (g • x)).1).1,
    ((iterateSplit e' k (r' (g • x)).1).2, (r' (g • x)).2)) = _
  rw [hr]
  change ((iterateSplit e' k (g • (r x).1)).1,
    ((iterateSplit e' k (g • (r x).1)).2, g • (r x).2)) = _
  rw [iterateSplit_covariant e e' g he]
  rfl

end FiniteStages

namespace AlgebraicInput

variable {K N I V : Type*} [Field K] [Fintype K]
  [Group N] [Countable N] [Fintype I] [Fintype V] [Nonempty I] [Nonempty V]
variable (s : AlgebraicInput K N I V)
  [MeasurableSpace K] [MeasurableSingletonClass K] [LinearOrder K]

def markerAction : MulAction (Ambient.G N) s.markerSpace where
  smul g ω := ⟨MarkerGeometry.markerShift g ω.val,
    (Ambient.markerGeometry N).goodMarker_shift g ω.property⟩
  one_smul ω := by
    apply Subtype.ext
    change MarkerGeometry.markerShift 1 ω.val = ω.val
    funext u
    simp [MarkerGeometry.markerShift]
  mul_smul g h ω := by
    apply Subtype.ext
    change MarkerGeometry.markerShift (g * h) ω.val =
      MarkerGeometry.markerShift g (MarkerGeometry.markerShift h ω.val)
    funext u
    simp [MarkerGeometry.markerShift, mul_assoc]

def stageCoordinateAction (n : ℕ) : MulAction (Ambient.G N) (s.stageCoordinates n) where
  smul g a := (a.1, g • a.2)
  one_smul a := by
    change (a.1, (1 : Ambient.G N) • a.2) = a
    simp
  mul_smul g h a := by
    change (a.1, (g * h) • a.2) = (a.1, g • h • a.2)
    simp [mul_smul]

def stageSpaceAction (n : ℕ) : MulAction (Ambient.G N) (s.stageSpace n) where
  smul g f a := f (a.1, g⁻¹ • a.2)
  one_smul f := by
    change (fun a : s.stageCoordinates n => f (a.1, (1 : Ambient.G N)⁻¹ • a.2)) = f
    funext a
    simp
  mul_smul g h f := by
    change (fun a : s.stageCoordinates n => f (a.1, (g * h)⁻¹ • a.2)) =
      (fun a : s.stageCoordinates n => f (a.1, h⁻¹ • g⁻¹ • a.2))
    funext a
    simp [mul_smul]

def splitOutputAction (n : ℕ) : MulAction (Ambient.G N) (s.splitOutput n) := by
  letI := CosetOperators.configurationAction (K := K) (J := Fin s.excess)
    (s.stageH (n + 1))
  letI := s.residualAction (s.stageH (n + 1)) (Ambient.includeN N)
    (s.ambient_commutes (s.stageLevel (n + 1)))
  infer_instance

def stageOutputAction (n : ℕ) : MulAction (Ambient.G N) (s.stageOutput n) := by
  letI := s.stageSpaceAction (n + 1)
  letI := s.splitOutputAction n
  infer_instance

attribute [local instance] markerAction stageCoordinateAction stageSpaceAction
  splitOutputAction stageOutputAction

theorem stageRegroupChart_covariant (n : ℕ) (g : Ambient.G N)
    (ω : s.markerSpace) (a : s.stageCoordinates n) :
    s.stageRegroupChart n (g • ω) (a.1, g • a.2) =
      (((s.stageRegroupChart n ω a).1.1, g • (s.stageRegroupChart n ω a).1.2),
        (s.stageRegroupChart n ω a).2) := by
  exact congrArg
    (fun p : (Ambient.G N ⧸ s.stageH (n + 1)) ×
        Fin (StageSchedule.discarded s.rowConstant n + 1) => ((a.1, p.1), p.2))
    (CosetCoordinates.sortedCosetChart_covariant (Ambient.markerGeometry N)
      (s.stageH n) (s.stageH (n + 1)) (s.stageH_step n) (s.stageH_le_D (n + 1))
      (s.stageH_quotient_card n) (2 * n) g ω a.2)

theorem stageRegroup_covariant (n : ℕ) (g : Ambient.G N)
    (ω : s.markerSpace) (f : s.stageSpace n) :
    Regroup.linearEquiv (s.stageRegroupChart n (g • ω)) (g • f) =
      g • Regroup.linearEquiv (s.stageRegroupChart n ω) f := by
  exact Regroup.linearEquiv_covariant _ _ g
    (fun a => s.stageRegroupChart_covariant n g ω a) f

theorem stageSplit_covariant (n : ℕ) (g : Ambient.G N)
    (ω : s.markerSpace) (f : s.stageSpace (n + 1)) :
    s.stageSplit n (g • ω) (g • f) = g • s.stageSplit n ω f := by
  have h := s.expandedSplit_covariant (s.stageH (n + 1)) (Ambient.includeN N)
    (s.ambient_commutes (s.stageLevel (n + 1)))
    (s.ambientSplitCharts (s.stageLevel (n + 1)) (2 * n + 1) ω)
    (s.ambientSplitCharts (s.stageLevel (n + 1)) (2 * n + 1) (g • ω)) g
    (s.ambientSplitCharts_symm_covariant (s.stageLevel (n + 1)) (2 * n + 1) g ω)
    (fun v c => f (v, c))
  apply Prod.ext
  · funext a
    exact congrFun (congrFun (congrArg Prod.fst h) a.1) a.2
  · have hs := congrArg Prod.snd h
    exact hs

theorem concreteStage_covariant (g : Ambient.G N) (ω : s.markerSpace)
    (n : ℕ) (f : s.stageSpace n) :
    s.concreteStage n (g • ω) (g • f) = g • s.concreteStage n ω f :=
  FiniteStages.regroupAndRepeat_covariant _ _ _ _ g
    (s.stageRegroup_covariant n g ω) (s.stageSplit_covariant n g ω) _ f

end AlgebraicInput
end BernoulliIso

#print axioms BernoulliIso.AlgebraicInput.concreteStage_covariant
