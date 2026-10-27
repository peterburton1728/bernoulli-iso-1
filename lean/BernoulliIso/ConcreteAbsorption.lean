module

public import BernoulliIso.ConcreteResidualSplit
public import BernoulliIso.ConcreteTower
public import BernoulliIso.ConcreteDynamics

/-!
Concrete absorbers for every leftover in the extraction tower. Residual
reservoirs are built from countably many copies of the actual rectangle;
no residual absorber or cancellation principle is an input.
-/

@[expose] public section
noncomputable section
open MeasureTheory

namespace BernoulliIso
namespace ConcreteInterleaving

/-- Reindex countably many nonempty finite (or countable) rows into one row. -/
def copiesToInfinite {Z : Type*} [MeasurableSpace Z] (ν : Measure Z)
    [IsProbabilityMeasure ν] (T : Type*) [Countable T] [Nonempty T] :
    ProbabilityIso (iidLaw ℕ (iidLaw T ν)) (iidLaw ℕ ν) :=
  (ProbabilityIso.curry (fun (_ : ℕ) (_ : T) => ν)).symm.trans
    (ProbabilityIso.reindex (fun _ : ℕ => ν) (natTimes T))

theorem copiesToInfinite_covariant {Z G : Type*} [Group G]
    [MeasurableSpace Z] [MulAction G Z] (ν : Measure Z)
    [IsProbabilityMeasure ν] (T : Type*) [Countable T] [Nonempty T]
    (g : G) (x : ℕ → T → Z) :
    (copiesToInfinite ν T).equiv (g • x) = g • (copiesToInfinite ν T).equiv x := by
  funext n
  obtain ⟨j, rfl⟩ := (natTimes T).surjective n
  change (MeasurableEquiv.piCongrLeft (fun _ : ℕ => Z) (natTimes T))
      (fun p => g • x p.1 p.2) (natTimes T j) =
    g • (MeasurableEquiv.piCongrLeft (fun _ : ℕ => Z) (natTimes T))
      (fun p => x p.1 p.2) (natTimes T j)
  rw [MeasurableEquiv.piCongrLeft_apply_apply, MeasurableEquiv.piCongrLeft_apply_apply]

end ConcreteInterleaving

namespace ProbabilityIso

theorem interleave_covariant {G Z A B : Type*} [Group G]
    [MeasurableSpace Z] [MulAction G Z] (ν : Measure Z)
    [IsProbabilityMeasure ν] (slots : A ⊕ B ≃ A) (g : G) (x : (A → Z) × (B → Z)) :
    (interleave ν slots).equiv (g • x) = g • (interleave ν slots).equiv x := by
  funext a
  obtain ⟨j, rfl⟩ := slots.surjective a
  change (MeasurableEquiv.piCongrLeft (fun _ : A => Z) slots)
      ((MeasurableEquiv.sumPiEquivProdPi (fun _ : A ⊕ B => Z)).symm (g • x)) (slots j) =
    g • (MeasurableEquiv.piCongrLeft (fun _ : A => Z) slots)
      ((MeasurableEquiv.sumPiEquivProdPi (fun _ : A ⊕ B => Z)).symm x) (slots j)
  rw [MeasurableEquiv.piCongrLeft_apply_apply, MeasurableEquiv.piCongrLeft_apply_apply]
  cases j <;> rfl

end ProbabilityIso

namespace RelativeProbabilityIso

/-- Absorb a pair by the explicit reassociation and two given maps.
The concrete uses below construct both maps from actual coordinates/splits. -/
def absorbPair {Ω R A B : Type*} [MeasurableSpace Ω] [MeasurableSpace R]
    [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure R} {α : Measure A} {β : Measure B}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (f : RelativeProbabilityIso Ω (μ.prod α) μ)
    (g : RelativeProbabilityIso Ω (μ.prod β) μ) :
    RelativeProbabilityIso Ω (μ.prod (α.prod β)) μ :=
  (constant (ProbabilityIso.assoc μ α β).symm).trans <|
    (f.prod (refl β)).trans g

theorem absorbPair_equivariant {G Ω R A B : Type*} [Group G]
    [MeasurableSpace Ω] [MeasurableSpace R] [MeasurableSpace A] [MeasurableSpace B]
    [MulAction G Ω] [MulAction G R] [MulAction G A] [MulAction G B]
    {μ : Measure R} {α : Measure A} {β : Measure B}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (f : RelativeProbabilityIso Ω (μ.prod α) μ)
    (g : RelativeProbabilityIso Ω (μ.prod β) μ)
    (hf : f.Equivariant (G := G)) (hg : g.Equivariant (G := G)) :
    (absorbPair f g).Equivariant (G := G) :=
  (show (constant (ProbabilityIso.assoc μ α β).symm : RelativeProbabilityIso Ω _ _).Equivariant
    (G := G) from fun _ _ _ => rfl).trans
      ((hf.prod (by intro _ _ _; rfl)).trans hg)

theorem reservoirFromSplit_equivariant {G Ω R A B Z ι : Type*} [Group G]
    [MeasurableSpace Ω] [MeasurableSpace R] [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace Z]
    [MulAction G Ω] [MulAction G R] [MulAction G A] [MulAction G B] [MulAction G Z]
    (μ : Measure R) (α : Measure A) (β : Measure B) (σ : Measure Z)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure α]
    [IsProbabilityMeasure β] [IsProbabilityMeasure σ]
    (split : RelativeProbabilityIso Ω α (β.prod σ))
    (left : RelativeProbabilityIso Ω μ (Measure.infinitePi (fun _ : ι => α)))
    (right : RelativeProbabilityIso Ω (Measure.infinitePi (fun _ : ι => β)) μ)
    (shuffle : ProbabilityIso (Measure.infinitePi (fun _ : ι => β.prod σ))
      ((Measure.infinitePi (fun _ : ι => β)).prod (Measure.infinitePi (fun _ : ι => σ))))
    (hsplit : split.Equivariant (G := G)) (hleft : left.Equivariant (G := G))
    (hright : right.Equivariant (G := G))
    (hshuffle : ∀ (g : G) x, shuffle.equiv (g • x) = g • shuffle.equiv x) :
    (reservoirFromSplit μ α β σ split left right shuffle).Equivariant (G := G) :=
  hleft.trans <| (Equivariant.pi (fun _ => hsplit)).trans <|
    (show (constant shuffle : RelativeProbabilityIso Ω _ _).Equivariant (G := G)
      from fun g _ x => hshuffle g x).trans (hright.prod (by intro _ _ _; rfl))

end RelativeProbabilityIso

namespace AlgebraicInput

variable {K N I V : Type*} [Field K] [Fintype K]
  [Group N] [Countable N] [Fintype I] [Fintype V] [Nonempty I] [Nonempty V]
variable (s : AlgebraicInput K N I V)
  [MeasurableSpace V] [MeasurableSingletonClass V]
  [MeasurableSpace K] [MeasurableSingletonClass K] [LinearOrder K]
  [TopologicalSpace K] [DiscreteTopology K] [BorelSpace K] [IsTopologicalRing K]

local instance ambientMeasurable : MeasurableSpace (Ambient.G N) := ⊤
local instance ambientMeasurableSingleton : MeasurableSingletonClass (Ambient.G N) :=
  ⟨fun _ => trivial⟩
local instance absorptionQuotientMeasurable (L : Subgroup (Ambient.G N)) :
    MeasurableSpace (Ambient.G N ⧸ L) := ⊤
local instance absorptionQuotientMeasurableSingleton (L : Subgroup (Ambient.G N)) :
    MeasurableSingletonClass (Ambient.G N ⧸ L) := ⟨fun _ => trivial⟩

theorem kappaNonempty : Nonempty (Fin s.κ) := by
  have hk : s.κ ≠ 0 := fun h => s.κ_ne_zero (by simp [h])
  exact ⟨⟨0, Nat.pos_of_ne_zero hk⟩⟩

abbrev infiniteBernoulli (_s : AlgebraicInput K N I V) := ℕ → Ambient.G N → K

def infiniteBernoulliAction : MulAction (Ambient.G N) s.infiniteBernoulli where
  smul g x n u := x n (g⁻¹ * u)
  one_smul x := by
    change (fun (n : ℕ) (u : Ambient.G N) => x n ((1 : Ambient.G N)⁻¹ * u)) = x
    funext n u
    simp
  mul_smul g h x := by
    change (fun (n : ℕ) (u : Ambient.G N) => x n ((g * h)⁻¹ * u)) =
      (fun n u => x n (h⁻¹ * (g⁻¹ * u)))
    funext n u
    simp [mul_assoc]

def infiniteBernoulliLaw (_s : AlgebraicInput K N I V) (μ : Measure K) :
    Measure _s.infiniteBernoulli := iidLaw ℕ (iidLaw (Ambient.G N) μ)

instance infiniteBernoulliLaw_probability (μ : Measure K) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (s.infiniteBernoulliLaw μ) := by
  unfold infiniteBernoulliLaw iidLaw
  infer_instance

instance infiniteBernoulliLaw_haar (μ : Measure K) [IsProbabilityMeasure μ]
    [μ.IsAddHaarMeasure] : (s.infiniteBernoulliLaw μ).IsAddHaarMeasure := by
  letI := infinitePi_isAddHaarMeasure (fun _ : Ambient.G N => μ)
  exact infinitePi_isAddHaarMeasure _

/-- Actual finite-coset interleaving at every lamp level. -/
def ambientCosetInfinite (a : ℕ) (μ : Measure K) [IsProbabilityMeasure μ] :
    RelativeProbabilityIso s.markerSpace (s.infiniteBernoulliLaw μ)
      (iidLaw ℕ (iidLaw (Ambient.G N ⧸ Ambient.Hseq N a) μ)) :=
  ConcreteInterleaving.cosetInfinite (Ambient.markerGeometry N) (Ambient.Hseq N a)
    (Ambient.H_le_D N (Ambient.sites a)) μ

/-- Countable copies of d finite-coset tracks are exactly the ordinary
infinite-track Bernoulli reservoir, by an actual marker coordinate map. -/
def infiniteToCosetCopies (a : ℕ) (T : Type*) [Countable T] [Nonempty T]
    (μ : Measure K) [IsProbabilityMeasure μ] :
    RelativeProbabilityIso s.markerSpace (s.infiniteBernoulliLaw μ)
      (iidLaw ℕ (iidLaw T (iidLaw (Ambient.G N ⧸ Ambient.Hseq N a) μ))) :=
  (s.ambientCosetInfinite a μ).trans <|
    RelativeProbabilityIso.constant
      (ConcreteInterleaving.copiesToInfinite
        (iidLaw (Ambient.G N ⧸ Ambient.Hseq N a) μ) T).symm

/-- The actual algebraic residual reservoir. Both infinite primary products
are converted to B∞ by explicit finite-coset and track interleavings. -/
def residualReservoir (a : ℕ) (μ : Measure K)
    [IsProbabilityMeasure μ] [μ.IsAddHaarMeasure] :
    RelativeProbabilityIso s.markerSpace (s.infiniteBernoulliLaw μ)
      ((s.infiniteBernoulliLaw μ).prod (iidLaw ℕ (s.ambientResidualsLaw a))) := by
  letI := s.kappaNonempty
  letI := s.ambientResiduals_secondCountable a
  letI := s.ambientResiduals_borel a
  let β := iidLaw (Fin s.κ × I) (iidLaw (Ambient.G N ⧸ Ambient.Hseq N a) μ)
  let σ := s.ambientResidualsLaw a
  letI := infinitePi_isAddHaarMeasure (fun _ : Ambient.G N ⧸ Ambient.Hseq N a => μ)
  letI := infinitePi_isAddHaarMeasure
    (fun _ : Fin s.κ × I => iidLaw (Ambient.G N ⧸ Ambient.Hseq N a) μ)
  exact RelativeProbabilityIso.reservoirFromSplit
    (s.infiniteBernoulliLaw μ)
    (iidLaw V (iidLaw (Ambient.G N ⧸ Ambient.Hseq N a) μ)) β σ
    (s.relativeUnexpandedSplit a 0 μ)
    (s.infiniteToCosetCopies a V μ)
    (s.infiniteToCosetCopies a (Fin s.κ × I) μ).symm
    (ProbabilityIso.piProduct (fun _ : ℕ => β) (fun _ : ℕ => σ))

/-- Absorption of any finite or countable number of the actual residual
families. This is θ × id, interleaving, θ⁻¹, with θ constructed above. -/
def absorbResiduals (a : ℕ) (T : Type*) [Countable T] (μ : Measure K)
    [IsProbabilityMeasure μ] [μ.IsAddHaarMeasure] :
    RelativeProbabilityIso s.markerSpace
      ((s.infiniteBernoulliLaw μ).prod (iidLaw T (s.ambientResidualsLaw a)))
      (s.infiniteBernoulliLaw μ) :=
  RelativeProbabilityIso.absorb (s.infiniteBernoulliLaw μ) (s.ambientResidualsLaw a)
    (s.residualReservoir a μ) (ConcreteInterleaving.natPlus T)

/-- The exact discarded factor at extraction stage n, with its iid law. -/
def discardedLaw (n : ℕ) (μ : Measure K) :
    Measure (Fin (StageSchedule.discarded s.rowConstant n) → s.stageSpace (n + 1)) :=
  iidLaw (Fin (StageSchedule.discarded s.rowConstant n))
    (iidLaw (s.stageCoordinates (n + 1)) μ)

instance discardedLaw_probability (n : ℕ) (μ : Measure K) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (s.discardedLaw n μ) := by
  unfold discardedLaw iidLaw
  infer_instance

instance discardedLaw_haar (n : ℕ) (μ : Measure K)
    [IsProbabilityMeasure μ] [μ.IsAddHaarMeasure] : (s.discardedLaw n μ).IsAddHaarMeasure := by
  letI := infinitePi_isAddHaarMeasure (fun _ : s.stageCoordinates (n + 1) => μ)
  exact infinitePi_isAddHaarMeasure _

/-- The discarded factor is first uncurried into literal coset tracks,
then absorbed by the actual finite-coset coordinate interleaving. -/
def absorbDiscarded (n : ℕ) (μ : Measure K) [IsProbabilityMeasure μ] :
    RelativeProbabilityIso s.markerSpace
      ((s.infiniteBernoulliLaw μ).prod (s.discardedLaw n μ))
      (s.infiniteBernoulliLaw μ) := by
  let h := s.stageH (n + 1)
  let W := Fin (StageSchedule.discarded s.rowConstant n)
  let first : RelativeProbabilityIso s.markerSpace (s.discardedLaw n μ)
      (iidLaw W (iidLaw V (iidLaw (Ambient.G N ⧸ h) μ))) :=
    RelativeProbabilityIso.pi (fun _ : W => RelativeProbabilityIso.constant
      (ProbabilityIso.curry (fun (_ : V) (_ : Ambient.G N ⧸ h) => μ)))
  let flatten : ProbabilityIso (iidLaw W (iidLaw V (iidLaw (Ambient.G N ⧸ h) μ)))
      (iidLaw (W × V) (iidLaw (Ambient.G N ⧸ h) μ)) :=
    (ProbabilityIso.curry (fun (_ : W) (_ : V) => iidLaw (Ambient.G N ⧸ h) μ)).symm
  exact ((RelativeProbabilityIso.refl (s.infiniteBernoulliLaw μ)).prod
    (first.trans (RelativeProbabilityIso.constant flatten))).trans <|
      ConcreteInterleaving.absorbCosetTracks (Ambient.markerGeometry N) h
        (s.stageH_le_D (n + 1)) μ (W × V)

/-- After separating the surplus Bernoulli tracks, these are precisely the
remaining factors at stage n: repeated algebraic residuals and discarded tracks. -/
abbrev leftover (n : ℕ) :=
  (Fin (StageSchedule.repetitions s.rowConstant n) → s.ambientResiduals (s.stageLevel (n + 1))) ×
    (Fin (StageSchedule.discarded s.rowConstant n) → s.stageSpace (n + 1))

instance leftover_secondCountable (n : ℕ) : SecondCountableTopology (s.leftover n) := by
  letI := s.ambientResiduals_secondCountable (s.stageLevel (n + 1))
  infer_instance

instance leftover_borel (n : ℕ) : BorelSpace (s.leftover n) := by
  letI := s.ambientResiduals_secondCountable (s.stageLevel (n + 1))
  letI := s.ambientResiduals_borel (s.stageLevel (n + 1))
  infer_instance

def leftoverLaw (n : ℕ) (μ : Measure K) : Measure (s.leftover n) :=
  (iidLaw (Fin (StageSchedule.repetitions s.rowConstant n))
    (s.ambientResidualsLaw (s.stageLevel (n + 1)))).prod (s.discardedLaw n μ)

instance leftoverLaw_probability (n : ℕ) (μ : Measure K) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (s.leftoverLaw n μ) := by
  unfold leftoverLaw
  infer_instance

instance leftoverLaw_haar (n : ℕ) (μ : Measure K)
    [IsProbabilityMeasure μ] [μ.IsAddHaarMeasure] : (s.leftoverLaw n μ).IsAddHaarMeasure := by
  letI := s.ambientResiduals_secondCountable (s.stageLevel (n + 1))
  letI := s.ambientResiduals_borel (s.stageLevel (n + 1))
  letI : MeasurableAdd (s.ambientResiduals (s.stageLevel (n + 1))) := inferInstance
  letI := s.leftover_borel n
  letI := infinitePi_isAddHaarMeasure
    (fun _ : Fin (StageSchedule.repetitions s.rowConstant n) =>
      s.ambientResidualsLaw (s.stageLevel (n + 1)))
  unfold leftoverLaw
  infer_instance

/-- Every concrete leftover has its constructed absorber. -/
def absorbLeftover (n : ℕ) (μ : Measure K)
    [IsProbabilityMeasure μ] [μ.IsAddHaarMeasure] :
    RelativeProbabilityIso s.markerSpace
      ((s.infiniteBernoulliLaw μ).prod (s.leftoverLaw n μ))
      (s.infiniteBernoulliLaw μ) :=
  RelativeProbabilityIso.absorbPair
    (s.absorbResiduals (s.stageLevel (n + 1))
      (Fin (StageSchedule.repetitions s.rowConstant n)) μ)
    (s.absorbDiscarded n μ)

/-- Allocate countably many B∞ reservoirs, use every concrete leftover
absorber, then recombine. This is the manuscript's full leftover absorption,
with the actual leftover spaces and probability laws throughout. -/
def absorbAllLeftovers (μ : Measure K)
    [IsProbabilityMeasure μ] [μ.IsAddHaarMeasure] :
    RelativeProbabilityIso s.markerSpace
      ((s.infiniteBernoulliLaw μ).prod (Measure.infinitePi (fun n => s.leftoverLaw n μ)))
      (s.infiniteBernoulliLaw μ) := by
  letI (n : ℕ) : BorelSpace (s.leftover n) := s.leftover_borel n
  letI (n : ℕ) : SecondCountableTopology (s.leftover n) := s.leftover_secondCountable n
  exact RelativeProbabilityIso.absorbFamily (s.infiniteBernoulliLaw μ) (fun n => s.leftoverLaw n μ)
    (RelativeProbabilityIso.constant
      (ConcreteInterleaving.copiesToInfinite (iidLaw (Ambient.G N) μ) ℕ).symm)
    (fun n => s.absorbLeftover n μ)
    (ProbabilityIso.piProduct (fun _ : ℕ => s.infiniteBernoulliLaw μ)
      (fun n => s.leftoverLaw n μ))

section Covariance

local instance markerMulAction : MulAction (Ambient.G N) s.markerSpace := s.markerAction
local instance siteMulAction : MulAction (Ambient.G N) (Ambient.G N → K) where
  smul g x u := x (g⁻¹ * u)
  one_smul x := by
    change (fun (u : Ambient.G N) => x ((1 : Ambient.G N)⁻¹ * u)) = x
    funext u
    simp
  mul_smul g h x := by
    change (fun (u : Ambient.G N) => x ((g * h)⁻¹ * u)) =
      (fun u => x (h⁻¹ * (g⁻¹ * u)))
    funext u
    simp [mul_assoc]
local instance bernoulliMulAction : MulAction (Ambient.G N) s.infiniteBernoulli :=
  s.infiniteBernoulliAction
local instance cosetScalarAction (a : ℕ) :
    MulAction (Ambient.G N) (Ambient.G N ⧸ Ambient.Hseq N a → K) where
  smul g x c := x (g⁻¹ • c)
  one_smul x := by
    change (fun (c : Ambient.G N ⧸ Ambient.Hseq N a) => x ((1 : Ambient.G N)⁻¹ • c)) = x
    funext c
    simp
  mul_smul g h x := by
    change (fun (c : Ambient.G N ⧸ Ambient.Hseq N a) => x ((g * h)⁻¹ • c)) =
      (fun c => x (h⁻¹ • (g⁻¹ • c)))
    funext c
    simp [mul_smul]
local instance cosetMulAction (a : ℕ) (T : Type*) :
    MulAction (Ambient.G N) (T → Ambient.G N ⧸ Ambient.Hseq N a → K) :=
  CosetOperators.configurationAction (Ambient.Hseq N a)
local instance stageCosetScalarAction (n : ℕ) :
    MulAction (Ambient.G N) (Ambient.G N ⧸ s.stageH n → K) :=
  cosetScalarAction (K := K) (s.stageLevel n)
local instance stageCosetMulAction (n : ℕ) (T : Type*) :
    MulAction (Ambient.G N) (T → Ambient.G N ⧸ s.stageH n → K) :=
  CosetOperators.configurationAction (s.stageH n)
local instance residualMulAction (a : ℕ) :
    MulAction (Ambient.G N)
      (s.residual (Ambient.Hseq N a) (Ambient.includeN N) (s.ambient_commutes a)) :=
  s.residualAction (Ambient.Hseq N a) (Ambient.includeN N) (s.ambient_commutes a)
local instance stageMulAction (n : ℕ) : MulAction (Ambient.G N) (s.stageSpace n) :=
  s.stageSpaceAction n

theorem ambientCosetInfinite_equivariant (a : ℕ) (μ : Measure K)
    [IsProbabilityMeasure μ] :
    (s.ambientCosetInfinite a μ).Equivariant (G := Ambient.G N) := by
  intro g ω x
  exact ConcreteInterleaving.cosetInfinite_covariant (Ambient.markerGeometry N)
    (Ambient.Hseq N a) (Ambient.H_le_D N (Ambient.sites a)) μ g ω x

theorem infiniteToCosetCopies_equivariant (a : ℕ) (T : Type*)
    [Countable T] [Nonempty T] (μ : Measure K) [IsProbabilityMeasure μ] :
    (s.infiniteToCosetCopies a T μ).Equivariant (G := Ambient.G N) := by
  unfold infiniteToCosetCopies
  apply (s.ambientCosetInfinite_equivariant a μ).trans
  exact (show (RelativeProbabilityIso.constant
    (ConcreteInterleaving.copiesToInfinite
      (iidLaw (Ambient.G N ⧸ Ambient.Hseq N a) μ) T) :
      RelativeProbabilityIso s.markerSpace _ _).Equivariant (G := Ambient.G N) from
    fun g _ x => ConcreteInterleaving.copiesToInfinite_covariant _ T g x).symm

theorem residualReservoir_equivariant (a : ℕ) (μ : Measure K)
    [IsProbabilityMeasure μ] [μ.IsAddHaarMeasure] :
    (s.residualReservoir a μ).Equivariant (G := Ambient.G N) := by
  letI := s.kappaNonempty
  unfold residualReservoir
  apply RelativeProbabilityIso.reservoirFromSplit_equivariant
  · intro g ω x
    exact s.relativeUnexpandedSplit_covariant a 0 μ g ω x
  · exact s.infiniteToCosetCopies_equivariant a V μ
  · exact (s.infiniteToCosetCopies_equivariant a (Fin s.κ × I) μ).symm
  · intro g x
    rfl

theorem absorbResiduals_equivariant (a : ℕ) (T : Type*) [Countable T]
    (μ : Measure K) [IsProbabilityMeasure μ] [μ.IsAddHaarMeasure] :
    (s.absorbResiduals a T μ).Equivariant (G := Ambient.G N) :=
  RelativeProbabilityIso.absorb_equivariant _ _ _
    (s.residualReservoir_equivariant a μ) _

theorem absorbDiscarded_equivariant (n : ℕ) (μ : Measure K)
    [IsProbabilityMeasure μ] :
    (s.absorbDiscarded n μ).Equivariant (G := Ambient.G N) := by
  letI : IsProbabilityMeasure (iidLaw (Ambient.G N ⧸ s.stageH (n + 1)) μ) := by
    unfold iidLaw
    infer_instance
  unfold absorbDiscarded
  apply RelativeProbabilityIso.Equivariant.trans (by intro g ω x; rfl)
  unfold ConcreteInterleaving.absorbCosetTracks
  apply RelativeProbabilityIso.Equivariant.trans
    ((s.ambientCosetInfinite_equivariant (s.stageLevel (n + 1)) μ).prod
      (by intro g ω x; rfl))
  apply RelativeProbabilityIso.Equivariant.trans ?_
    (s.ambientCosetInfinite_equivariant (s.stageLevel (n + 1)) μ).symm
  intro g ω x
  exact @ProbabilityIso.interleave_covariant
    (Ambient.G N) (Ambient.G N ⧸ s.stageH (n + 1) → K) ℕ
    (Fin (StageSchedule.discarded s.rowConstant n) × V)
    inferInstance inferInstance (s.stageCosetScalarAction (n + 1))
    (iidLaw (Ambient.G N ⧸ s.stageH (n + 1)) μ)
    (by unfold iidLaw; infer_instance) (ConcreteInterleaving.natPlus _) g x

theorem absorbLeftover_equivariant (n : ℕ) (μ : Measure K)
    [IsProbabilityMeasure μ] [μ.IsAddHaarMeasure] :
    (s.absorbLeftover n μ).Equivariant (G := Ambient.G N) :=
  RelativeProbabilityIso.absorbPair_equivariant _ _
    (s.absorbResiduals_equivariant (s.stageLevel (n + 1)) _ μ)
    (s.absorbDiscarded_equivariant n μ)

theorem absorbAllLeftovers_equivariant (μ : Measure K)
    [IsProbabilityMeasure μ] [μ.IsAddHaarMeasure] :
    (s.absorbAllLeftovers μ).Equivariant (G := Ambient.G N) := by
  letI : MulAction (Ambient.G N) (Ambient.G N → K) := siteMulAction
  letI : MulAction (Ambient.G N) (ℕ → Ambient.G N → K) := s.infiniteBernoulliAction
  letI : MulAction (Ambient.G N) (ℕ → s.infiniteBernoulli) :=
    @Pi.mulAction ℕ (fun _ => s.infiniteBernoulli) (Ambient.G N) _
      (fun _ => s.infiniteBernoulliAction)
  unfold absorbAllLeftovers
  apply RelativeProbabilityIso.absorbFamily_equivariant
  · exact (show (RelativeProbabilityIso.constant
      (ConcreteInterleaving.copiesToInfinite (iidLaw (Ambient.G N) μ) ℕ) :
        RelativeProbabilityIso s.markerSpace _ _).Equivariant (G := Ambient.G N) from
      fun g _ x => ConcreteInterleaving.copiesToInfinite_covariant _ ℕ g x).symm
  · intro n
    exact s.absorbLeftover_equivariant n μ
  · intro g x
    rfl

end Covariance

end AlgebraicInput
end BernoulliIso

#print axioms BernoulliIso.AlgebraicInput.residualReservoir
#print axioms BernoulliIso.AlgebraicInput.absorbAllLeftovers

#print axioms BernoulliIso.AlgebraicInput.absorbAllLeftovers_equivariant
