module

public import Collapse.Bundle
public import Collapse.Tower
public import BernoulliIso.RelativeProducts

/-!
# The dictionary

A kernel of the orbit relation of a
subgroup `Λ` acts on the fibres of the bundles, commuting with the action of `G`. Mutually
inverse kernels give mutually inverse continuous homomorphisms of the fibres, which preserve
Haar measure. Hence isomorphic sets have isomorphic bundles.
-/

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory

open scoped Classical

namespace Collapse

namespace PSystem

variable {G : Type} [Group G] [Countable G] (S : PSystem G) [S.IsFree] (Λ : Subgroup G)
  (K : Type) [Field K] [Fintype K] [MeasurableSpace K] [DiscreteCoeff K]
  {J J' J₂ : Type} [Countable J] [Countable J'] [Countable J₂]

/-- The action of a kernel on the fibre over `ω`, in the coordinates of the bundle:
`(𝔅(c) ξ)(γ, j') = ∑ (γ', j), c (γ⁻¹ • ω, j') (γ'⁻¹ • ω, j) * ξ (γ', j)`. -/
def kernelMap (c : LKernel Λ S.X K J J') (ω : S.X) (ξ : G × J → K) : G × J' → K :=
  fun q => ∑ᶠ p : G × J, c.toFun (q.1⁻¹ • ω, q.2) (p.1⁻¹ • ω, p.2) * ξ p

/-- `𝔅(c)` as a map of the total spaces. -/
def bundleMap (c : LKernel Λ S.X K J J') : S.X × (G × J → K) → S.X × (G × J' → K) :=
  fun p => (p.1, kernelMap S Λ K c p.1 p.2)

theorem inv_smul_inj {ω : S.X} {p p' : G × J} (h : (p.1⁻¹ • ω, p.2) = (p'.1⁻¹ • ω, p'.2)) :
    p = p' := by
  simp only [Prod.mk.injEq] at h
  have hfix : (p'.1 * p.1⁻¹) • ω = ω := by rw [mul_smul, h.1, smul_inv_smul]
  have := IsFree.free (S := S) _ _ hfix
  rw [mul_inv_eq_one] at this
  exact Prod.ext this.symm h.2

theorem inv_smul_injective (ω : S.X) : Function.Injective fun p : G × J => (p.1⁻¹ • ω, p.2) :=
  fun _ _ h => inv_smul_inj S h

theorem exists_of_mem_orbit {ω y : S.X} {γ : G} (h : y ∈ MulAction.orbit Λ (γ⁻¹ • ω)) :
    ∃ γ' : G, y = γ'⁻¹ • ω := by
  obtain ⟨l, rfl⟩ := h
  exact ⟨γ * ((l : G))⁻¹, by show (l : G) • γ⁻¹ • ω = _; rw [mul_inv_rev, inv_inv, mul_smul]⟩

theorem kernel_support_finite (c : LKernel Λ S.X K J J') (ω : S.X) (b : S.X × J')
    (ξ : G × J → K) :
    (Function.support fun p : G × J => c.toFun b (p.1⁻¹ • ω, p.2) * ξ p).Finite :=
  ((c.rowFinite b).preimage (inv_smul_injective S ω).injOn).subset fun _ hp =>
    left_ne_zero_of_mul hp

theorem measurable_entry (c : LKernel Λ S.X K J J') (γ γ' : G) (j' : J') (j : J) :
    Measurable fun ω : S.X => c.toFun (γ⁻¹ • ω, j') (γ'⁻¹ • ω, j) := by
  by_cases h : γ'⁻¹ * γ ∈ Λ
  · have e : (fun ω : S.X => c.toFun (γ⁻¹ • ω, j') (γ'⁻¹ • ω, j)) =
        (fun x => c.toFun (x, j') ((⟨γ'⁻¹ * γ, h⟩ : Λ) • x, j)) ∘ fun ω => γ⁻¹ • ω := by
      funext ω
      simp only [Function.comp_apply, Subgroup.smul_def, smul_smul, mul_inv_cancel_right]
    rw [e]
    exact (c.measurable _ j' j).comp (S.preserving γ⁻¹).measurable
  · have e : (fun ω : S.X => c.toFun (γ⁻¹ • ω, j') (γ'⁻¹ • ω, j)) = fun _ => 0 := by
      funext ω
      by_contra hne
      obtain ⟨l, hl⟩ := c.rel _ _ hne
      have hl' : (l : G) • γ'⁻¹ • ω = γ⁻¹ • ω := hl
      have hfix : (γ * (l : G) * γ'⁻¹) • ω = ω := by
        rw [mul_smul, mul_smul, hl', smul_inv_smul]
      have h1 := IsFree.free (S := S) _ _ hfix
      apply h
      have : γ'⁻¹ * γ = (l : G)⁻¹ := by
        calc γ'⁻¹ * γ = γ'⁻¹ * (γ * l * γ'⁻¹) * γ' * (l : G)⁻¹ := by group
          _ = (l : G)⁻¹ := by rw [h1]; group
      rw [this]; exact Λ.inv_mem l.2
    rw [e]; exact measurable_const

theorem measurable_bundleMap (c : LKernel Λ S.X K J J') : Measurable (bundleMap S Λ K c) := by
  show Measurable fun p : S.X × (G × J → K) => (p.1, kernelMap S Λ K c p.1 p.2)
  refine measurable_fst.prodMk (measurable_pi_iff.2 fun q => ?_)
  show Measurable fun p : S.X × (G × J → K) =>
    ∑ᶠ r : G × J, c.toFun (q.1⁻¹ • p.1, q.2) (r.1⁻¹ • p.1, r.2) * p.2 r
  exact LKernel.measurable_finsum
    (fun r => LKernel.measurable_op₂ (· * ·)
      ((measurable_entry S Λ K c q.1 r.1 q.2 r.2).comp measurable_fst)
      ((measurable_pi_apply r).comp measurable_snd))
    fun p => kernel_support_finite S Λ K c p.1 _ p.2

/-- `𝔅(c)` commutes with the action of `G`. -/
theorem bundleMap_smul (c : LKernel Λ S.X K J J') (A : J → Set S.X)
    (hA : ∀ j, MeasurableSet (A j)) (B : J' → Set S.X) (hB : ∀ j, MeasurableSet (B j)) (g : G)
    (p : (S.bundle K J A hA).X) :
    bundleMap S Λ K c (g • p) = (g • (show (S.bundle K J' B hB).X from bundleMap S Λ K c p)) := by
  obtain ⟨ω, ξ⟩ := p
  refine Prod.ext rfl (funext fun q => ?_)
  show ∑ᶠ p' : G × J, c.toFun (q.1⁻¹ • g • ω, q.2) (p'.1⁻¹ • g • ω, p'.2) * ξ (g⁻¹ * p'.1, p'.2) =
    ∑ᶠ p' : G × J, c.toFun ((g⁻¹ * q.1)⁻¹ • ω, q.2) (p'.1⁻¹ • ω, p'.2) * ξ p'
  conv_lhs => rw [← finsum_comp_equiv (Equiv.prodCongr (Equiv.mulLeft g) (Equiv.refl J))]
  refine finsum_congr fun r => ?_
  simp only [Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, Equiv.coe_mulLeft,
    Equiv.refl_apply, mul_inv_rev, inv_inv, mul_smul, inv_smul_smul, inv_mul_cancel_left,
    Prod.mk.eta]

theorem finsum_exchange {α β : Type} (f : α → K) (g : α → β → K) (ξ : β → K) (R : Finset α)
    (P : Finset β) (hR : ∀ r, f r ≠ 0 → r ∈ R) (hP : ∀ r p, r ∈ R → g r p ≠ 0 → p ∈ P) :
    ∑ᶠ p, (∑ᶠ r, f r * g r p) * ξ p = ∑ᶠ r, f r * ∑ᶠ p, g r p * ξ p := by
  have h1 : ∀ p, ∑ᶠ r, f r * g r p = ∑ r ∈ R, f r * g r p := fun p =>
    finsum_eq_sum_of_support_subset _ fun r hr => hR r (left_ne_zero_of_mul hr)
  calc ∑ᶠ p, (∑ᶠ r, f r * g r p) * ξ p = ∑ p ∈ P, (∑ r ∈ R, f r * g r p) * ξ p := by
        rw [finsum_eq_sum_of_support_subset _ (s := P) fun p hp => by
          obtain ⟨r, hr1, hr2⟩ :=
            LKernel.exists_mul_ne_zero_of_finsum_ne_zero (left_ne_zero_of_mul hp)
          exact hP r p (hR r hr1) hr2]
        exact Finset.sum_congr rfl fun p _ => by rw [h1 p]
    _ = ∑ r ∈ R, f r * ∑ p ∈ P, g r p * ξ p := by
        simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
        exact Finset.sum_comm
    _ = ∑ᶠ r, f r * ∑ᶠ p, g r p * ξ p := by
        rw [finsum_eq_sum_of_support_subset _ (s := R) fun r hr => hR r (left_ne_zero_of_mul hr)]
        refine Finset.sum_congr rfl fun r hr => ?_
        rw [finsum_eq_sum_of_support_subset _ (s := P) fun p hp =>
          hP r p hr (left_ne_zero_of_mul hp)]

theorem kernelMap_comp (c' : LKernel Λ S.X K J' J₂) (c : LKernel Λ S.X K J J') (ω : S.X)
    (ξ : G × J → K) :
    kernelMap S Λ K (c'.comp c) ω ξ = kernelMap S Λ K c' ω (kernelMap S Λ K c ω ξ) := by
  funext q
  simp only [kernelMap, LKernel.comp_toFun]
  have heJ := inv_smul_injective S ω (J := J)
  have heJ' := inv_smul_injective S ω (J := J')
  have h1 : ∀ p : G × J, ∑ᶠ b, c'.toFun (q.1⁻¹ • ω, q.2) b * c.toFun b (p.1⁻¹ • ω, p.2) =
      ∑ᶠ r : G × J', c'.toFun (q.1⁻¹ • ω, q.2) (r.1⁻¹ • ω, r.2) *
        c.toFun (r.1⁻¹ • ω, r.2) (p.1⁻¹ • ω, p.2) := fun p =>
    LKernel.finsum_eq_finsum_comp (fun r : G × J' => (r.1⁻¹ • ω, r.2)) heJ' fun b hb => by
      obtain ⟨γ', h⟩ := exists_of_mem_orbit S Λ
        (MulAction.mem_orbit_symm.1 (c'.rel _ b (left_ne_zero_of_mul hb)))
      exact ⟨(γ', b.2), Prod.ext h.symm rfl⟩
  simp only [h1]
  exact finsum_exchange K (fun r : G × J' => c'.toFun (q.1⁻¹ • ω, q.2) (r.1⁻¹ • ω, r.2))
    (fun r p => c.toFun (r.1⁻¹ • ω, r.2) (p.1⁻¹ • ω, p.2)) ξ
    ((c'.rowFinite (q.1⁻¹ • ω, q.2)).preimage heJ'.injOn).toFinset
    (((c'.rowFinite (q.1⁻¹ • ω, q.2)).preimage heJ'.injOn).toFinset.biUnion fun r =>
      ((c.rowFinite (r.1⁻¹ • ω, r.2)).preimage heJ.injOn).toFinset)
    (fun r hr => by simpa using hr)
    (fun r p hr hp => Finset.mem_biUnion.2 ⟨r, hr, by simpa using hp⟩)

/-- The kernel `δ_A` acts on the fibres by masking. -/
theorem bundleMap_diag (A : J → Set S.X) (hA : ∀ j, MeasurableSet (A j)) :
    bundleMap S Λ K (LKernel.diag A hA) = maskMap S K A := by
  funext p
  refine Prod.ext rfl (funext fun q => ?_)
  show ∑ᶠ p' : G × J, (LKernel.diag (Λ := Λ) (K := K) A hA).toFun (q.1⁻¹ • p.1, q.2)
      (p'.1⁻¹ • p.1, p'.2) * p.2 p' = if q.1⁻¹ • p.1 ∈ A q.2 then p.2 q else 0
  rw [finsum_eq_single _ q fun p' hp' => by
    rw [LKernel.diag_toFun, if_neg (fun hh => hp' (inv_smul_inj S hh.1).symm), zero_mul]]
  by_cases h : q.1⁻¹ • p.1 ∈ A q.2 <;> simp [LKernel.diag_toFun, h]

theorem bundleMap_comp (c' : LKernel Λ S.X K J' J₂) (c : LKernel Λ S.X K J J')
    (p : S.X × (G × J → K)) :
    bundleMap S Λ K (c'.comp c) p = bundleMap S Λ K c' (bundleMap S Λ K c p) :=
  Prod.ext rfl (kernelMap_comp S Λ K c' c p.1 p.2)

theorem kernelMap_diag (A : J → Set S.X) (hA : ∀ j, MeasurableSet (A j)) (ω : S.X)
    (ξ : G × J → K) :
    kernelMap S Λ K (LKernel.diag A hA) ω ξ = (maskMap S K A (ω, ξ)).2 :=
  congrArg Prod.snd (congrFun (bundleMap_diag S Λ K A hA) (ω, ξ))

/-- `𝔅(c)` on the fibre over `ω`, as an additive homomorphism. -/
def kernelMapHom (c : LKernel Λ S.X K J J') (ω : S.X) : (G × J → K) →+ (G × J' → K) where
  toFun := kernelMap S Λ K c ω
  map_zero' := funext fun q => by simp [kernelMap]
  map_add' ξ η := funext fun q => by
    simp only [kernelMap, Pi.add_apply, mul_add]
    exact finsum_add_distrib (kernel_support_finite S Λ K c ω _ ξ)
      (kernel_support_finite S Λ K c ω _ η)

theorem continuous_kernelMap [TopologicalSpace K] [ContinuousAdd K] [ContinuousMul K]
    (c : LKernel Λ S.X K J J') (ω : S.X) : Continuous (kernelMap S Λ K c ω) := by
  refine continuous_pi fun q => ?_
  have hF := (c.rowFinite (q.1⁻¹ • ω, q.2)).preimage (inv_smul_injective S ω (J := J)).injOn
  have e : (fun ξ : G × J → K => kernelMap S Λ K c ω ξ q) = fun ξ =>
      ∑ p ∈ hF.toFinset, c.toFun (q.1⁻¹ • ω, q.2) (p.1⁻¹ • ω, p.2) * ξ p := by
    funext ξ
    exact finsum_eq_sum_of_support_subset _ fun p hp => hF.mem_toFinset.2 (left_ne_zero_of_mul hp)
  rw [e]
  exact continuous_finsetSum _ fun p _ => continuous_const.mul (continuous_apply p)

/-- Fibrewise: `𝔅(c)` carries the uniform measure to the masked uniform measure. -/
theorem map_kernelMap_eq (c : LKernel Λ S.X K J J') (c' : LKernel Λ S.X K J' J)
    (B : J' → Set S.X) (hB : ∀ j, MeasurableSet (B j))
    (h1 : c.comp c' = LKernel.diag B hB) (h2 : (LKernel.diag B hB).comp c = c) (ω : S.X) :
    (Measure.infinitePi fun _ : G × J => uniformK K).map (kernelMap S Λ K c ω) =
      (Measure.infinitePi fun _ : G × J' => uniformK K).map
        (fun ξ => (maskMap S K B (ω, ξ)).2) := by
  let _ : TopologicalSpace K := ⊥
  haveI : DiscreteTopology K := ⟨rfl⟩
  haveI hU : (uniformK K).IsAddHaarMeasure := BernoulliIso.uniformFinite_isAddHaarMeasure
  haveI hJ : (Measure.infinitePi fun _ : G × J => uniformK K).IsAddHaarMeasure :=
    BernoulliIso.infinitePi_isAddHaarMeasure _
  haveI hJ' : (Measure.infinitePi fun _ : G × J' => uniformK K).IsAddHaarMeasure :=
    BernoulliIso.infinitePi_isAddHaarMeasure _
  let s : Set (G × J') := {q | q.1⁻¹ • ω ∈ B q.2}
  haveI hs : (Measure.infinitePi fun _ : s => uniformK K).IsAddHaarMeasure :=
    BernoulliIso.infinitePi_isAddHaarMeasure _
  let r : (G × J' → K) →+ (s → K) :=
    { toFun := fun ξ i => ξ i, map_zero' := rfl, map_add' := fun _ _ => rfl }
  let x : (s → K) → (G × J' → K) := fun η q => if h : q ∈ s then η ⟨q, h⟩ else 0
  have hrx : ∀ η, r (x η) = η := fun η => funext fun i => by
    show (if h : (i : G × J') ∈ s then η ⟨i, h⟩ else 0) = η i
    rw [dif_pos i.2]
  have hM : ∀ ξ, (maskMap S K B (ω, ξ)).2 = x (r ξ) := fun ξ => funext fun q => by
    show (if q.1⁻¹ • ω ∈ B q.2 then ξ q else 0) = if h : q ∈ s then ξ q else 0
    rw [dif_eq_if]; rfl
  have hx : Measurable x := measurable_pi_iff.2 fun q => by
    by_cases h : q ∈ s
    · have e : (fun η : s → K => x η q) = fun η => η ⟨q, h⟩ := funext fun η => dif_pos h
      rw [e]; exact measurable_pi_apply _
    · have e : (fun η : s → K => x η q) = fun _ => 0 := funext fun η => dif_neg h
      rw [e]; exact measurable_const
  let T : (G × J → K) →+ (s → K) := r.comp (kernelMapHom S Λ K c ω)
  have hTc : Continuous T := by
    show Continuous fun ξ => fun i : s => kernelMap S Λ K c ω ξ i
    exact continuous_pi fun i =>
      (continuous_apply (i : G × J')).comp (continuous_kernelMap S Λ K c ω)
  have hTs : Function.Surjective T := fun η => ⟨kernelMap S Λ K c' ω (x η), by
    show r (kernelMap S Λ K c ω (kernelMap S Λ K c' ω (x η))) = η
    rw [← kernelMap_comp, h1, kernelMap_diag, hM, hrx, hrx]⟩
  have hrc : Continuous r := continuous_pi fun i => continuous_apply (i : G × J')
  have hrs : Function.Surjective r := fun η => ⟨x η, hrx η⟩
  have hT := T.measurePreserving (μ := Measure.infinitePi fun _ : G × J => uniformK K)
    (ν := Measure.infinitePi fun _ : s => uniformK K) hTc hTs (by simp)
  have hr := r.measurePreserving (μ := Measure.infinitePi fun _ : G × J' => uniformK K)
    (ν := Measure.infinitePi fun _ : s => uniformK K) hrc hrs (by simp)
  have hfix : ∀ ξ, x (T ξ) = kernelMap S Λ K c ω ξ := fun ξ => by
    show x (r (kernelMap S Λ K c ω ξ)) = _
    rw [← hM, ← kernelMap_diag S Λ K B hB, ← kernelMap_comp, h2]
  calc (Measure.infinitePi fun _ : G × J => uniformK K).map (kernelMap S Λ K c ω)
      = (Measure.infinitePi fun _ : G × J => uniformK K).map (x ∘ T) := by
        congr 1; funext ξ; exact (hfix ξ).symm
    _ = ((Measure.infinitePi fun _ : G × J => uniformK K).map T).map x :=
        (Measure.map_map hx hT.measurable).symm
    _ = ((Measure.infinitePi fun _ : G × J' => uniformK K).map r).map x := by
        rw [hT.map_eq, hr.map_eq]
    _ = (Measure.infinitePi fun _ : G × J' => uniformK K).map (x ∘ r) :=
        Measure.map_map hx hr.measurable
    _ = _ := by congr 1

theorem map_bundleMap_eq (c : LKernel Λ S.X K J J') (c' : LKernel Λ S.X K J' J)
    (B : J' → Set S.X) (hB : ∀ j, MeasurableSet (B j))
    (h1 : c.comp c' = LKernel.diag B hB) (h2 : (LKernel.diag B hB).comp c = c) :
    (S.μ.prod (Measure.infinitePi fun _ : G × J => uniformK K)).map (bundleMap S Λ K c) =
      (S.μ.prod (Measure.infinitePi fun _ : G × J' => uniformK K)).map (maskMap S K B) := by
  have hmB := measurable_maskMap S K B hB
  have hΦ := measurable_bundleMap S Λ K c
  ext E hE
  rw [Measure.map_apply hΦ hE, Measure.map_apply hmB hE, Measure.prod_apply (hΦ hE),
    Measure.prod_apply (hmB hE)]
  refine lintegral_congr fun ω => ?_
  have hfib := map_kernelMap_eq S Λ K c c' B hB h1 h2 ω
  have hL : Measurable (kernelMap S Λ K c ω) :=
    measurable_snd.comp (hΦ.comp measurable_prodMk_left)
  have hM : Measurable fun ξ : G × J' → K => (maskMap S K B (ω, ξ)).2 :=
    measurable_snd.comp (hmB.comp measurable_prodMk_left)
  have : ((Measure.infinitePi fun _ : G × J => uniformK K).map (kernelMap S Λ K c ω))
      (Prod.mk ω ⁻¹' E) = ((Measure.infinitePi fun _ : G × J' => uniformK K).map
        (fun ξ => (maskMap S K B (ω, ξ)).2)) (Prod.mk ω ⁻¹' E) := by rw [hfib]
  rw [Measure.map_apply hL (measurable_prodMk_left hE),
    Measure.map_apply hM (measurable_prodMk_left hE)] at this
  exact this

theorem bundle_iso_of_kernels (A : J → Set S.X) (hA : ∀ j, MeasurableSet (A j))
    (B : J' → Set S.X) (hB : ∀ j, MeasurableSet (B j))
    (c : LKernel Λ S.X K J J') (c' : LKernel Λ S.X K J' J)
    (hl : c'.comp c = LKernel.diag A hA) (hr : c.comp c' = LKernel.diag B hB)
    (hBc : (LKernel.diag B hB).comp c = c) (hcA : c.comp (LKernel.diag A hA) = c)
    (hAc' : (LKernel.diag A hA).comp c' = c') :
    (S.bundle K J A hA).Iso (S.bundle K J' B hB) := by
  have hΨΦ : ∀ p, bundleMap S Λ K c' (bundleMap S Λ K c p) = maskMap S K A p := fun p => by
    rw [← bundleMap_comp, hl, bundleMap_diag]
  have hΦΨ : ∀ p, bundleMap S Λ K c (bundleMap S Λ K c' p) = maskMap S K B p := fun p => by
    rw [← bundleMap_comp, hr, bundleMap_diag]
  have hBΦ : ∀ p, maskMap S K B (bundleMap S Λ K c p) = bundleMap S Λ K c p := fun p => by
    rw [← bundleMap_diag S Λ K B hB, ← bundleMap_comp, hBc]
  have hΦA : ∀ p, bundleMap S Λ K c (maskMap S K A p) = bundleMap S Λ K c p := fun p => by
    rw [← bundleMap_diag S Λ K A hA, ← bundleMap_comp, hcA]
  have hAΨ : ∀ p, maskMap S K A (bundleMap S Λ K c' p) = bundleMap S Λ K c' p := fun p => by
    rw [← bundleMap_diag S Λ K A hA, ← bundleMap_comp, hAc']
  have hidA : (LKernel.diag (Λ := Λ) (K := K) A hA).comp (LKernel.diag A hA) =
      LKernel.diag A hA := (LocalSpace.ofSet (Λ := Λ) (K := K) A hA).idem
  have hidB : (LKernel.diag (Λ := Λ) (K := K) B hB).comp (LKernel.diag B hB) =
      LKernel.diag B hB := (LocalSpace.ofSet (Λ := Λ) (K := K) B hB).idem
  have hmmA : ∀ p, maskMap S K A (maskMap S K A p) = maskMap S K A p := fun p => by
    rw [← bundleMap_diag S Λ K A hA, ← bundleMap_comp, hidA]
  have hmmB : ∀ p, maskMap S K B (maskMap S K B p) = maskMap S K B p := fun p => by
    rw [← bundleMap_diag S Λ K B hB, ← bundleMap_comp, hidB]
  have hsmA : ∀ (g : G) (p : (S.bundle K J A hA).X),
      maskMap S K A (g • p) = g • (show (S.bundle K J A hA).X from maskMap S K A p) := fun g p => by
    have := bundleMap_smul S Λ K (LKernel.diag A hA) A hA A hA g p
    rw [bundleMap_diag] at this
    exact this
  have hsmB : ∀ (g : G) (p : (S.bundle K J' B hB).X),
      maskMap S K B (g • p) = g • (show (S.bundle K J' B hB).X from maskMap S K B p) := fun g p => by
    have := bundleMap_smul S Λ K (LKernel.diag B hB) B hB B hB g p
    rw [bundleMap_diag] at this
    exact this
  have hmA := measurable_maskMap S K A hA
  have hmB := measurable_maskMap S K B hB
  have hsA : MeasurableSet {p : S.X × (G × J → K) | maskMap S K A p = p} :=
    measurableSet_eq_fun hmA measurable_id
  have hsB : MeasurableSet {p : S.X × (G × J' → K) | maskMap S K B p = p} :=
    measurableSet_eq_fun hmB measurable_id
  refine ⟨conjMk (μ := (S.bundle K J A hA).μ) (ν := (S.bundle K J' B hB).μ)
    {p | maskMap S K A p = p} {p | maskMap S K B p = p} hsA hsB ?_ ?_ ?_ ?_
    (bundleMap S Λ K c) ?_ ?_ ?_⟩
  · exact (ae_map_iff hmA.aemeasurable hsA).2 (ae_of_all _ hmmA)
  · exact (ae_map_iff hmB.aemeasurable hsB).2 (ae_of_all _ hmmB)
  · intro g p hp
    have hp' : maskMap S K A p = p := hp
    show maskMap S K A (g • p) = g • p
    rw [hsmA]
    exact congrArg (g • · : (S.bundle K J A hA).X → (S.bundle K J A hA).X) hp'
  · intro g p hp
    have hp' : maskMap S K B p = p := hp
    show maskMap S K B (g • p) = g • p
    rw [hsmB]
    exact congrArg (g • · : (S.bundle K J' B hB).X → (S.bundle K J' B hB).X) hp'
  · refine ⟨measurable_bundleMap S Λ K c, ?_⟩
    show Measure.map (bundleMap S Λ K c) (Measure.map (maskMap S K A)
        (S.μ.prod (Measure.infinitePi fun _ : G × J => uniformK K))) =
      Measure.map (maskMap S K B) (S.μ.prod (Measure.infinitePi fun _ : G × J' => uniformK K))
    rw [Measure.map_map (measurable_bundleMap S Λ K c) hmA,
      show bundleMap S Λ K c ∘ maskMap S K A = bundleMap S Λ K c from funext hΦA]
    exact map_bundleMap_eq S Λ K c c' B hB hr hBc
  · refine ⟨fun p _ => hBΦ p, fun (p : S.X × (G × J → K)) hp (p' : S.X × (G × J → K)) hp' hpp => ?_, fun y hy => ⟨bundleMap S Λ K c' y,
      hAΨ y, (hΦΨ y).trans hy⟩⟩
    have h1 : maskMap S K A p = p := hp
    have h2 : maskMap S K A p' = p' := hp'
    exact h1.symm.trans ((hΨΦ p).symm.trans
      ((congrArg (bundleMap S Λ K c') hpp).trans ((hΨΦ p').trans h2)))
  · intro g p _
    exact bundleMap_smul S Λ K c A hA B hB g p

/-- **Dictionary**: sets with isomorphic local spaces have isomorphic
bundles. -/
theorem bundle_iso_of_toClass_eq (A : J → Set S.X) (hA : ∀ j, MeasurableSet (A j))
    (B : J' → Set S.X) (hB : ∀ j, MeasurableSet (B j))
    (h : LocalSpace.toClass (LocalSpace.ofSet (Λ := Λ) (K := K) A hA) =
      LocalSpace.toClass (LocalSpace.ofSet B hB)) :
    (S.bundle K J A hA).Iso (S.bundle K J' B hB) := by
  obtain ⟨I⟩ := LocalSpace.toClass_eq_iff.1 h
  exact bundle_iso_of_kernels S Λ K A hA B hB I.c I.c' I.left I.right
    (LocalSpace.mor_left (LocalSpace.ofSet B hB).idem I.c_mor)
    (LocalSpace.mor_right (LocalSpace.ofSet A hA).idem I.c_mor)
    (LocalSpace.mor_left (LocalSpace.ofSet A hA).idem I.c'_mor)

end PSystem

end Collapse
