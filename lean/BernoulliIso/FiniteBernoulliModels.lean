module

public import BernoulliIso.ConcreteOutputLaws
public import BernoulliIso.MarkerDynamics
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-! The actual finite Bernoulli model for the initial marker and data.
The coordinate identification uses the canonical quotient map at H₀ = 1. -/

@[expose] public section
noncomputable section
open MeasureTheory
open scoped Classical

namespace BernoulliIso

/-- The ordinary Bernoulli action with arbitrary finite alphabet. -/
def bernoulliAction (G A : Type*) [Group G] : MulAction G (G → A) where
  smul g f u := f (g⁻¹ * u)
  one_smul f := by
    change (fun u : G => f ((1 : G)⁻¹ * u)) = f
    funext u
    simp
  mul_smul g h f := by
    change (fun u : G => f ((g * h)⁻¹ * u)) =
      (fun u : G => f (h⁻¹ * (g⁻¹ * u)))
    funext u
    simp [mul_assoc]

/-- Each alphabet point has mass 1 / |A|, independently at every group site. -/
def bernoulliLaw (G A : Type*) [Fintype A] [Nonempty A]
    [MeasurableSpace A] : Measure (G → A) :=
  Measure.infinitePi (fun _ : G => Measure.uniformOfFinset (Finset.univ : Finset A))

instance bernoulliLaw_probability (G A : Type*) [Fintype A] [Nonempty A]
    [MeasurableSpace A] [MeasurableSingletonClass A] :
    IsProbabilityMeasure (bernoulliLaw G A) := by
  letI : IsProbabilityMeasure
      (Measure.uniformOfFinset (Finset.univ : Finset A)) :=
    MarkerGeometry.uniformBase_probability A
  unfold bernoulliLaw
  infer_instance

theorem bernoulliLaw_preserving {G A : Type*} [Group G] [Countable G]
    [Fintype A] [Nonempty A] [MeasurableSpace A] [MeasurableSingletonClass A]
    (g : G) : MeasurePreserving ((bernoulliAction G A).smul g)
      (bernoulliLaw G A) (bernoulliLaw G A) :=
  MarkerGeometry.measurePreserving_markerShift (K := A) g

/-- Zip two ordinary group tracks into the product alphabet, site by site. -/
def bernoulliZipEquiv (G A : Type*) [MeasurableSpace A] :
    ((G → A) × (G → A)) ≃ᵐ (G → A × A) where
  toFun p u := (p.1 u, p.2 u)
  invFun f := (fun u => (f u).1, fun u => (f u).2)
  left_inv _ := rfl
  right_inv _ := rfl
  measurable_toFun := Measurable.of_eval fun u =>
    ((measurable_pi_apply u).comp measurable_fst).prodMk
      ((measurable_pi_apply u).comp measurable_snd)
  measurable_invFun :=
    (Measurable.of_eval fun u => measurable_fst.comp (measurable_pi_apply u)).prodMk
      (Measurable.of_eval fun u => measurable_snd.comp (measurable_pi_apply u))

/-- For finite compact additive alphabets the sitewise zip preserves the
actual uniform Bernoulli laws by normalized Haar uniqueness. -/
def bernoulliZipIso (G A : Type*) [Countable G] [AddCommGroup A] [Fintype A]
    [TopologicalSpace A] [IsTopologicalAddGroup A]
    [MeasurableSpace A] [BorelSpace A] [MeasurableSingletonClass A] :
    ProbabilityIso ((bernoulliLaw G A).prod (bernoulliLaw G A))
      (bernoulliLaw G (A × A)) := by
  letI : IsProbabilityMeasure (Measure.uniformOfFinset (Finset.univ : Finset A)) :=
    MarkerGeometry.uniformBase_probability A
  letI : IsProbabilityMeasure (Measure.uniformOfFinset (Finset.univ : Finset (A × A))) :=
    MarkerGeometry.uniformBase_probability (A × A)
  letI : (Measure.uniformOfFinset (Finset.univ : Finset A)).IsAddHaarMeasure :=
    uniformFinite_isAddHaarMeasure
  letI : (bernoulliLaw G A).IsAddHaarMeasure :=
    infinitePi_isAddHaarMeasure
      (fun _ : G => Measure.uniformOfFinset (Finset.univ : Finset A))
  letI : (Measure.uniformOfFinset (Finset.univ : Finset (A × A))).IsAddHaarMeasure :=
    uniformFinite_isAddHaarMeasure
  letI : (bernoulliLaw G (A × A)).IsAddHaarMeasure :=
    infinitePi_isAddHaarMeasure
      (fun _ : G => Measure.uniformOfFinset (Finset.univ : Finset (A × A)))
  let F : ((G → A) × (G → A)) →+ (G → A × A) :=
    { toFun := bernoulliZipEquiv G A
      map_zero' := rfl
      map_add' _ _ := rfl }
  have hF : Continuous F := continuous_pi fun u =>
    ((continuous_apply u).comp continuous_fst).prodMk
      ((continuous_apply u).comp continuous_snd)
  exact ⟨bernoulliZipEquiv G A,
    F.measurePreserving hF (bernoulliZipEquiv G A).surjective (by simp)⟩

theorem bernoulliZipEquiv_covariant {G A : Type*} [Group G] [MeasurableSpace A]
    (g : G) (p : (G → A) × (G → A)) :
    bernoulliZipEquiv G A
      ((bernoulliAction G A).smul g p.1, (bernoulliAction G A).smul g p.2) =
      (bernoulliAction G (A × A)).smul g (bernoulliZipEquiv G A p) := rfl

namespace AlgebraicInput

variable {K N I V : Type*} [Field K] [Fintype K]
  [Group N] [Countable N] [Fintype I] [Fintype V] [Nonempty I] [Nonempty V]
variable (s : AlgebraicInput K N I V)
  [MeasurableSpace K] [MeasurableSingletonClass K] [LinearOrder K]

abbrev finiteBase (_s : AlgebraicInput K N I V) := K × (V → K)

theorem stageH_zero_eq_bot : s.stageH 0 = ⊥ := by
  simp only [stageH, stageLevel, StageSchedule.level_zero, Ambient.Hseq_zero_eq_bot]

/-- The quotient map itself is bijective at stage zero. No representative
of a nontrivial coset is selected in the finite Bernoulli identification. -/
theorem stageZero_mk_bijective :
    Function.Bijective (QuotientGroup.mk : Ambient.G N → Ambient.G N ⧸ s.stageH 0) := by
  constructor
  · intro g h hgh
    have hmem := QuotientGroup.eq.mp hgh
    rw [s.stageH_zero_eq_bot] at hmem
    simpa only [Subgroup.mem_bot, inv_mul_eq_one] using hmem
  · exact QuotientGroup.mk_surjective

def stageZeroCosetEquiv : Ambient.G N ≃ Ambient.G N ⧸ s.stageH 0 :=
  Equiv.ofBijective QuotientGroup.mk s.stageZero_mk_bijective

@[simp] theorem stageZeroCosetEquiv_apply (g : Ambient.G N) :
    s.stageZeroCosetEquiv g = QuotientGroup.mk g := rfl

/-- The initial marker and d data tracks become one finite alphabet at each
ordinary group site. The formula is exactly (ω(g), (x(v,gH₀))ᵥ). -/
def finiteBernoulliEquiv : ((Ambient.G N → K) × s.stageSpace 0) ≃ᵐ
    (Ambient.G N → s.finiteBase) where
  toFun p g := (p.1 g, fun v => p.2 (v, s.stageZeroCosetEquiv g))
  invFun f := (fun g => (f g).1,
    fun a => (f (s.stageZeroCosetEquiv.symm a.2)).2 a.1)
  left_inv p := by
    apply Prod.ext
    · rfl
    · funext a
      simp only [Equiv.apply_symm_apply]
  right_inv f := by
    funext g
    simp only [Equiv.symm_apply_apply]
  measurable_toFun := Measurable.of_eval fun g =>
    ((measurable_pi_apply g).comp measurable_fst).prodMk
      (Measurable.of_eval fun v =>
        (measurable_pi_apply (v, s.stageZeroCosetEquiv g)).comp measurable_snd)
  measurable_invFun :=
    (Measurable.of_eval fun g => measurable_fst.comp (measurable_pi_apply g)).prodMk
      (Measurable.of_eval fun a =>
        (measurable_pi_apply a.1).comp
          (measurable_snd.comp (measurable_pi_apply (s.stageZeroCosetEquiv.symm a.2))))

@[simp] theorem finiteBernoulliEquiv_apply
    (p : (Ambient.G N → K) × s.stageSpace 0) (g : Ambient.G N) :
    s.finiteBernoulliEquiv p g = (p.1 g, fun v => p.2 (v, QuotientGroup.mk g)) := rfl

/-- Coordinate equivariance is literal left translation, including stage 0. -/
theorem finiteBernoulliEquiv_covariant (g : Ambient.G N)
    (p : (Ambient.G N → K) × s.stageSpace 0) :
    s.finiteBernoulliEquiv
      (MarkerGeometry.markerShift g p.1, (s.stageSpaceAction 0).smul g p.2) =
      (bernoulliAction (Ambient.G N) s.finiteBase).smul g (s.finiteBernoulliEquiv p) := by
  funext u
  apply Prod.ext
  · rfl
  · funext v
    rfl

section Probability
variable [TopologicalSpace K] [DiscreteTopology K] [BorelSpace K] [IsTopologicalRing K]

/-- This is a global probability isomorphism with the uniform finite-base
Bernoulli law, rather than merely an identification of underlying sets. -/
def finiteBernoulliIso :
    ProbabilityIso
      ((MarkerGeometry.markerLaw (G := Ambient.G N) K).prod
        (s.stageDataLaw 0 (MarkerGeometry.uniformBase K)))
      (bernoulliLaw (Ambient.G N) s.finiteBase) := by
  let μ := MarkerGeometry.uniformBase K
  letI : μ.IsAddHaarMeasure := uniformFinite_isAddHaarMeasure
  letI : (MarkerGeometry.markerLaw (G := Ambient.G N) K).IsAddHaarMeasure :=
    infinitePi_isAddHaarMeasure (fun _ : Ambient.G N => μ)
  letI : IsProbabilityMeasure
      (Measure.uniformOfFinset (Finset.univ : Finset s.finiteBase)) :=
    MarkerGeometry.uniformBase_probability s.finiteBase
  letI : (Measure.uniformOfFinset (Finset.univ : Finset s.finiteBase)).IsAddHaarMeasure :=
    uniformFinite_isAddHaarMeasure
  letI : (bernoulliLaw (Ambient.G N) s.finiteBase).IsAddHaarMeasure :=
    infinitePi_isAddHaarMeasure
      (fun _ : Ambient.G N => Measure.uniformOfFinset (Finset.univ : Finset s.finiteBase))
  let F : ((Ambient.G N → K) × s.stageSpace 0) →+ (Ambient.G N → s.finiteBase) :=
    { toFun := s.finiteBernoulliEquiv
      map_zero' := rfl
      map_add' _ _ := rfl }
  have hF : Continuous F := continuous_pi fun g =>
    ((continuous_apply g).comp continuous_fst).prodMk
      (continuous_pi fun v =>
        (continuous_apply (v, s.stageZeroCosetEquiv g)).comp continuous_snd)
  refine ⟨s.finiteBernoulliEquiv, ?_⟩
  exact F.measurePreserving hF s.finiteBernoulliEquiv.surjective (by simp)

/-- The exact law of one full initial marker together with stage-zero data. -/
abbrev finiteModelLaw :=
  (MarkerGeometry.markerLaw (G := Ambient.G N) K).prod
    (s.stageDataLaw 0 (MarkerGeometry.uniformBase K))

/-- Reassociate two initial finite sources, identify each with its finite
Bernoulli model, and zip the resulting tracks into the square alphabet. -/
def doubleFiniteBernoulliIso :
    ProbabilityIso
      ((MarkerGeometry.markerLaw (G := Ambient.G N) K).prod
        ((s.stageDataLaw 0 (MarkerGeometry.uniformBase K)).prod s.finiteModelLaw))
      (bernoulliLaw (Ambient.G N) (s.finiteBase × s.finiteBase)) :=
  (ProbabilityIso.assoc (MarkerGeometry.markerLaw (G := Ambient.G N) K)
    (s.stageDataLaw 0 (MarkerGeometry.uniformBase K)) s.finiteModelLaw).symm.trans
      ((s.finiteBernoulliIso.prod s.finiteBernoulliIso).trans
        (bernoulliZipIso (Ambient.G N) s.finiteBase))

@[simp] theorem doubleFiniteBernoulliIso_apply
    (p : (Ambient.G N → K) × (s.stageSpace 0 × ((Ambient.G N → K) × s.stageSpace 0)))
    (u : Ambient.G N) :
    s.doubleFiniteBernoulliIso.equiv p u =
      ((p.1 u, fun v => p.2.1 (v, QuotientGroup.mk u)),
        (p.2.2.1 u, fun v => p.2.2.2 (v, QuotientGroup.mk u))) := rfl

/-- The double model respects the same shift on all four input tracks. -/
theorem doubleFiniteBernoulliIso_covariant (g : Ambient.G N)
    (p : (Ambient.G N → K) × (s.stageSpace 0 × ((Ambient.G N → K) × s.stageSpace 0))) :
    s.doubleFiniteBernoulliIso.equiv
      (MarkerGeometry.markerShift g p.1,
        ((s.stageSpaceAction 0).smul g p.2.1,
          (MarkerGeometry.markerShift g p.2.2.1, (s.stageSpaceAction 0).smul g p.2.2.2))) =
      (bernoulliAction (Ambient.G N) (s.finiteBase × s.finiteBase)).smul g
        (s.doubleFiniteBernoulliIso.equiv p) := by
  funext u
  apply Prod.ext
  · exact congrFun (s.finiteBernoulliEquiv_covariant g (p.1, p.2.1)) u
  · exact congrFun (s.finiteBernoulliEquiv_covariant g p.2.2) u

end Probability

theorem finiteBase_card :
    Fintype.card s.finiteBase = Fintype.card K ^ (Fintype.card V + 1) := by
  simp [finiteBase, Fintype.card_prod, Fintype.card_fun, pow_succ, Nat.mul_comm]

theorem finiteBase_card_gt_one : 1 < Fintype.card s.finiteBase :=
  Fintype.one_lt_card

theorem finiteBase_square_card :
    Fintype.card (s.finiteBase × s.finiteBase) =
      Fintype.card K ^ (2 * (Fintype.card V + 1)) := by
  rw [Fintype.card_prod, s.finiteBase_card, ← pow_add]
  congr 1
  omega

theorem finiteBase_square_card_gt :
    Fintype.card s.finiteBase < Fintype.card (s.finiteBase × s.finiteBase) := by
  simp only [Fintype.card_prod]
  have h := s.finiteBase_card_gt_one
  simp only [Fintype.card_prod] at h
  nlinarith

end AlgebraicInput
end BernoulliIso

#print axioms BernoulliIso.AlgebraicInput.finiteBernoulliIso
#print axioms BernoulliIso.AlgebraicInput.finiteBernoulliEquiv_covariant
#print axioms BernoulliIso.AlgebraicInput.finiteBase_square_card_gt

#print axioms BernoulliIso.AlgebraicInput.doubleFiniteBernoulliIso
#print axioms BernoulliIso.AlgebraicInput.doubleFiniteBernoulliIso_covariant
