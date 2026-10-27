module

public import BernoulliIso.ConcreteTower
public import BernoulliIso.LocalChartMeasurability

/-! Actual group-ring rows and retained coset coordinates stay in one D-coset. -/

@[expose] public section
noncomputable section
open scoped BigOperators Classical

namespace BernoulliIso.CosetOperators

variable {N G : Type*} [Group N] [Group G]

theorem rightCoset_projection {H D : Subgroup G} (hHD : H ≤ D) (ι : N →* G)
    (commutes : ∀ h ∈ H, ∀ n, Commute h (ι n))
    (hιD : ∀ n, ι n ∈ D) (n : N) (x : G ⧸ H) :
    Subgroup.quotientMapOfLE hHD (rightCoset H ι commutes n x) =
      Subgroup.quotientMapOfLE hHD x := by
  induction x using QuotientGroup.induction_on with
  | H g =>
    apply QuotientGroup.eq.mpr
    simpa using D.inv_mem (hιD n)

end BernoulliIso.CosetOperators

namespace BernoulliIso.AlgebraicInput

variable {K N I V G : Type*} [Field K] [Finite K]
  [Group N] [Countable N] [Fintype I] [Fintype V] [Nonempty I] [Nonempty V] [Group G]
variable (s : AlgebraicInput K N I V)

theorem splitSectionRow_support_local {H D : Subgroup G} (hHD : H ≤ D)
    (ι : N →* G) (commutes : ∀ h ∈ H, ∀ n, Commute h (ι n))
    (hιD : ∀ n, ι n ∈ D)
    (charts : ∀ v, (G ⧸ H) ≃ (G ⧸ (H ⊔ (s.J v).map ι)) × Fin s.κ)
    (v : V) (x : G ⧸ H) (b : V × (G ⧸ H))
    (hb : b ∈ (s.splitSectionRow H ι commutes charts v x).support) :
    Subgroup.quotientMapOfLE hHD b.2 = Subgroup.quotientMapOfLE hHD x := by
  unfold splitSectionRow at hb
  obtain ⟨i, hi, hb⟩ := Finset.mem_biUnion.mp (Finsupp.support_finsetSum hb)
  cases hs : s.outputSlots ((charts v x).2, i) with
  | inl w =>
    simp only [hs] at hb
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hb)
    exact CosetOperators.rightCoset_projection hHD ι commutes hιD n x
  | inr w => simp only [hs, Finsupp.support_zero, Finset.notMem_empty] at hb

variable [Fintype K] [MeasurableSpace K] [MeasurableSingletonClass K] [LinearOrder K]

def stageComponent (n : ℕ) (a : s.stageCoordinates n) : Ambient.G N ⧸ Ambient.D N :=
  Subgroup.quotientMapOfLE (s.stageH_le_D n) a.2

theorem stageSelection_local (ω : s.markerSpace) (n : ℕ)
    (a : s.stageCoordinates n) (b : s.stageCoordinates (n + 1))
    (hab : s.stageSelection ω n a = some b) :
    s.stageComponent (n + 1) b = s.stageComponent n a := by
  change Regroup.selected (s.stageRegroupChart n ω) a = some b at hab
  unfold Regroup.selected at hab
  split at hab
  · have hb := Option.some.inj hab
    rw [← hb]
    change Subgroup.quotientMapOfLE (s.stageH_le_D (n + 1))
      (Subgroup.quotientMapOfLE (s.stageH_step n) a.2) = _
    exact CosetCoordinates.quotientMap_comp (s.stageH_step n) (s.stageH_le_D (n + 1)) a.2
  · contradiction

theorem stageSplitRows_local (ω : s.markerSpace) (n : ℕ)
    (a b : s.stageCoordinates (n + 1)) (hb : b ∈ (s.stageSplitRows ω n a).support) :
    s.stageComponent (n + 1) b = s.stageComponent (n + 1) a :=
  s.splitSectionRow_support_local (s.stageH_le_D (n + 1)) (Ambient.includeN N)
    (s.ambient_commutes (s.stageLevel (n + 1))) (Ambient.height_includeN N)
    _ a.1 a.2 b hb

end BernoulliIso.AlgebraicInput
