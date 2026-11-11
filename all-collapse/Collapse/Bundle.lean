module

public import Collapse.Bernoulli
public import Collapse.LocalSpace
public import Mathlib.Algebra.Field.ZMod

/-!
# The bundle of a set

For a system `S` and a set with levels
`A j ⊆ S.X`, the bundle is the system on `S.X × (G × J → K)` whose measure is the image of
`μ ⊗ uniform` under masking: the coordinate `(γ, j)` is kept if `γ⁻¹ • ω ∈ A j` and set to `0`
otherwise. The group acts by `g • (ω, ξ) = (g • ω, fun (γ, j) => ξ (g⁻¹ * γ, j))`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory

open scoped Classical

namespace Collapse

/-- The uniform probability measure on a finite type. -/
def uniformK (K : Type) [Fintype K] [MeasurableSpace K] : Measure K :=
  Measure.uniformOfFinset Finset.univ

instance uniformK_isProbabilityMeasure (K : Type) [Fintype K] [Nonempty K] [MeasurableSpace K]
    [DiscreteCoeff K] : IsProbabilityMeasure (uniformK K) := by
  constructor
  have hn : (Fintype.card K : ENNReal) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card K ≠ 0)
  simpa [uniformK, Measure.uniformOfFinset_apply] using
    (ENNReal.div_self hn (by simp : (Fintype.card K : ENNReal) ≠ ⊤))

/-- The product of the uniform measures on `ℕ → K`; for `K = ZMod 2` this is the space `C`. -/
def cantorK (K : Type) [Fintype K] [MeasurableSpace K] : Measure (ℕ → K) :=
  Measure.infinitePi (fun _ : ℕ => uniformK K)

instance cantorK_isProbabilityMeasure (K : Type) [Fintype K] [Nonempty K] [MeasurableSpace K]
    [DiscreteCoeff K] : IsProbabilityMeasure (cantorK K) := by
  unfold cantorK; infer_instance

instance : DiscreteCoeff (ZMod 2) := DiscreteCoeff.of_finite _

namespace PSystem

variable {G : Type} [Group G] [Countable G]

/-- Masking: keep the coordinate `(γ, j)` if `γ⁻¹ • ω ∈ A j`, and put `0` otherwise. -/
def maskMap (S : PSystem G) (K : Type) [Zero K] {J : Type} (A : J → Set S.X) :
    S.X × (G × J → K) → S.X × (G × J → K) :=
  fun p => (p.1, fun q => if q.1⁻¹ • p.1 ∈ A q.2 then p.2 q else 0)

theorem measurable_maskMap_aux (S : PSystem G) (K : Type) [Zero K] [MeasurableSpace K] {J : Type}
    (A : J → Set S.X) (hA : ∀ j, MeasurableSet (A j)) : Measurable (maskMap S K A) := by
  refine measurable_fst.prodMk (measurable_pi_iff.2 fun q => ?_)
  exact Measurable.ite ((hA q.2).preimage ((S.preserving q.1⁻¹).measurable.comp measurable_fst))
    ((measurable_pi_apply q).comp measurable_snd) measurable_const

theorem measurePreserving_map_of_comm {α : Type} [MeasurableSpace α] {ν : Measure α}
    {T m : α → α} (hT : MeasurePreserving T ν ν) (hm : Measurable m)
    (hc : ∀ x, m (T x) = T (m x)) : MeasurePreserving T (ν.map m) (ν.map m) := by
  refine ⟨hT.measurable, ?_⟩
  have : T ∘ m = m ∘ T := funext fun x => (hc x).symm
  rw [Measure.map_map hT.measurable hm, this, ← Measure.map_map hm hT.measurable, hT.map_eq]

/-- The bundle `𝔅(A)` over `S`, with coefficients in the finite field `K`. -/
def bundle (S : PSystem G) (K : Type) [Field K] [Fintype K] [MeasurableSpace K]
    [DiscreteCoeff K] (J : Type) [Countable J] (A : J → Set S.X)
    (hA : ∀ j, MeasurableSet (A j)) : PSystem G where
  X := S.X × (G × J → K)
  act :=
    { smul := fun g p => (g • p.1, fun q => p.2 (g⁻¹ * q.1, q.2))
      one_smul := fun p => Prod.ext (one_smul G p.1) (funext fun q =>
        show p.2 ((1 : G)⁻¹ * q.1, q.2) = p.2 q by rw [inv_one, one_mul])
      mul_smul := fun g h p => Prod.ext (mul_smul g h p.1) (funext fun q =>
        show p.2 ((g * h)⁻¹ * q.1, q.2) = p.2 (h⁻¹ * (g⁻¹ * q.1), q.2) by
          rw [mul_inv_rev, mul_assoc]) }
  μ := (S.μ.prod (Measure.infinitePi fun _ : G × J => uniformK K)).map (maskMap S K A)
  prob := ⟨by rw [Measure.map_apply (measurable_maskMap_aux S K A hA) MeasurableSet.univ]; simp⟩
  preserving := fun g => by
    refine measurePreserving_map_of_comm
      (T := fun p : S.X × (G × J → K) => (g • p.1, fun q => p.2 (g⁻¹ * q.1, q.2)))
      ((S.preserving g).prod (measurePreserving_reindex (uniformK K)
        (fun q : G × J => (g⁻¹ * q.1, q.2))
        ⟨fun a b hab => ?_, fun b => ⟨(g * b.1, b.2), by simp⟩⟩))
      (measurable_maskMap_aux S K A hA) fun p => ?_
    · simp only [Prod.mk.injEq, mul_right_inj] at hab; exact Prod.ext hab.1 hab.2
    · simp only [maskMap]
      congr 1
      funext q
      rw [mul_inv_rev, inv_inv, mul_smul]

variable (S : PSystem G) (K : Type) [Field K] [Fintype K] [MeasurableSpace K] [DiscreteCoeff K]
  {J J' : Type} [Countable J] [Countable J']

theorem measurable_maskMap (A : J → Set S.X) (hA : ∀ j, MeasurableSet (A j)) :
    Measurable (maskMap S K A) := measurable_maskMap_aux S K A hA

/-- The bundle depends on the set only up to an invariant null set. -/
theorem bundle_iso_of_inter_eq (U : Set S.X) (hU : MeasurableSet U)
    (hinv : ∀ (g : G) (x : S.X), x ∈ U → g • x ∈ U) (hfull : S.μ Uᶜ = 0)
    (A A' : J → Set S.X) (hA : ∀ j, MeasurableSet (A j)) (hA' : ∀ j, MeasurableSet (A' j))
    (h : ∀ j, A j ∩ U = A' j ∩ U) : (S.bundle K J A hA).Iso (S.bundle K J A' hA') := by
  refine iso_of_bijective id ⟨measurable_id, ?_⟩ Function.bijective_id (fun _ _ => rfl)
  show Measure.map id (Measure.map (maskMap S K A) _) = Measure.map (maskMap S K A') _
  rw [Measure.map_id]
  refine Measure.map_congr ?_
  have hU : ∀ᵐ p ∂(S.μ.prod (Measure.infinitePi fun _ : G × J => uniformK K)), p.1 ∈ U :=
    measurePreserving_fst.quasiMeasurePreserving.ae (ae_iff.2 hfull)
  filter_upwards [hU] with p hp
  refine Prod.ext rfl (funext fun q => ?_)
  have hx := hinv q.1⁻¹ p.1 hp
  have hiff : q.1⁻¹ • p.1 ∈ A q.2 ↔ q.1⁻¹ • p.1 ∈ A' q.2 :=
    ⟨fun ha => ((h q.2 ▸ ⟨ha, hx⟩ : q.1⁻¹ • p.1 ∈ A' q.2 ∩ U)).1,
     fun ha => (((h q.2).symm ▸ ⟨ha, hx⟩ : q.1⁻¹ • p.1 ∈ A q.2 ∩ U)).1⟩
  simp only [maskMap, hiff]

/-- The bundle of countably infinitely many copies of the whole space
is `S × Ber(K^ℕ)`. -/
theorem bundle_univ_iso (J : Type) [Countable J] [Infinite J] :
    (S.bundle K J (fun _ => Set.univ) (fun _ => MeasurableSet.univ)).Iso
      (S.prod (bernoulli G (ℕ → K) (cantorK K))) := by
  obtain ⟨e⟩ : Nonempty (ℕ ≃ J) := nonempty_equiv_of_countable
  let e' : G × J ≃ G × ℕ := (Equiv.prodCongr (Equiv.refl G) e).symm
  let F : (G × J → K) ≃ᵐ (G → ℕ → K) :=
    (MeasurableEquiv.piCongrLeft (fun _ => K) e').trans (MeasurableEquiv.curry G ℕ K)
  have hF : ∀ ξ : G × J → K, F ξ = fun γ n => ξ (γ, e n) := by
    intro ξ; funext γ n
    simp [F, e', MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast,
      MeasurableEquiv.curry]
  have hFm : MeasurePreserving F (Measure.infinitePi fun _ : G × J => uniformK K)
      (Measure.infinitePi fun _ : G => cantorK K) := by
    refine ⟨F.measurable, ?_⟩
    have h1 := Measure.infinitePi_map_piCongrLeft (fun _ : G × ℕ => uniformK K) e'
    have h2 := Measure.infinitePi_map_curry (fun (_ : G) (_ : ℕ) => uniformK K)
    rw [show (F : (G × J → K) → (G → ℕ → K)) = MeasurableEquiv.curry G ℕ K ∘
      MeasurableEquiv.piCongrLeft (fun _ => K) e' from rfl,
      ← Measure.map_map (MeasurableEquiv.measurable _) (MeasurableEquiv.measurable _)]
    rw [h1]
    exact h2
  have hmask : maskMap S K (fun _ : J => (Set.univ : Set S.X)) = id := by
    funext p; simp [maskMap]
  refine iso_of_bijective (Prod.map id F) ?_
    (Function.bijective_id.prodMap F.bijective) fun g p => ?_
  · show MeasurePreserving _ (Measure.map (maskMap S K _) _) _
    rw [hmask, Measure.map_id]
    exact (MeasurePreserving.id S.μ).prod hFm
  · refine Prod.ext rfl ?_
    show F _ = fun h => F p.2 (g⁻¹ * h)
    rw [hF, hF]

end PSystem

end Collapse
