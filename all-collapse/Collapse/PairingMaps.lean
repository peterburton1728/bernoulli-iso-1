module

public import Collapse.PairingConstruction

/-!
# The pairing lemma: the maps between the bundle and the Bernoulli shift

Third part of the proof of the pairing lemma.
-/

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory

namespace Collapse

namespace PSystem

variable {G : Type} [Group G] [Countable G]

section PairingMaps

variable (F : Subgroup G) (lam : Measure ℝ) [IsProbabilityMeasure lam] (f : G)

theorem measurable_bigPhi (hb : Function.Bijective (eFun F f)) :
    Measurable (bigPhi F lam f hb) := by
  have : Measurable (fun (p : (gbP F lam).X × (G ⧸ F → ZMod 2)) (q : G ⧸ F) =>
      MeasurableEquiv.finTwoArrow.symm (phiPair (p.1 q, p.2 q))) :=
    measurable_pi_iff.mpr fun q => MeasurableEquiv.finTwoArrow.symm.measurable.comp
      (measurable_phiPair.comp (((measurable_pi_apply q).comp measurable_fst).prodMk
        ((measurable_pi_apply q).comp measurable_snd)))
  exact (reix (eG F f hb)).symm.measurable.comp this

variable {F f} in
theorem piMap_mk (hff : f * f = 1) (hFf : ∀ k ∈ F, k = 1 ∨ k = f) (x : G → ℝ) (γ : G) :
    piMap F lam f x (γ : G ⧸ F) = (min (x γ) (x (γ * f)), max (x γ) (x (γ * f))) := by
  rcases out_cases hFf γ with h | h
  · simp only [piMap, h]
  · simp only [piMap, h, mul_assoc, hff, mul_one]; rw [min_comm, max_comm]

variable {F f} in
theorem piMap_smul (hff : f * f = 1) (hFf : ∀ k ∈ F, k = 1 ∨ k = f) (g : G)
    (x : (bernoulli G ℝ lam).X) : piMap F lam f (g • x) = g • piMap F lam f x := by
  suffices h : ∀ y : G → ℝ, piMap F lam f (fun h => y (g⁻¹ * h)) =
      fun q => piMap F lam f y (g⁻¹ • q) from h x
  intro y; funext q
  obtain ⟨γ, rfl⟩ := QuotientGroup.mk_surjective q
  change _ = piMap F lam f y ((g⁻¹ * γ : G) : G ⧸ F)
  rw [piMap_mk lam hff hFf, piMap_mk lam hff hFf]
  simp only [mul_assoc]

open Classical in
variable {F lam f} in
theorem xiMap_mul_f (hfF : f ∈ F) (hf1 : f ≠ 1) (hff : f * f = 1) {ω : (gbP F lam).X}
    (hω : ω ∈ (gbP F lam).freeSet) (ξ : G × Unit → ZMod 2) (γ : G) :
    xiMap F lam f (ω, ξ) (γ * f) = if γ⁻¹ • ω ∈ dSet F lam f then
      (if ξ (γ, ()) = 1 then (ω (γ : G ⧸ F)).2 else (ω (γ : G ⧸ F)).1)
    else (if ξ (γ * f, ()) = 1 then (ω (γ : G ⧸ F)).1 else (ω (γ : G ⧸ F)).2) := by
  have hfi : f⁻¹ = f := inv_eq_of_mul_eq_one_right hff
  have h1 : (γ * f)⁻¹ • ω = f • γ⁻¹ • ω := by rw [mul_inv_rev, hfi, mul_smul]
  have hD := mem_dSet_smul hff hf1 ((gbP F lam).freeSet_invariant γ⁻¹ ω hω)
  simp only [xiMap, h1, mk_mul_f hfF, mul_assoc, hff, mul_one]
  by_cases h : γ⁻¹ • ω ∈ dSet F lam f
  · rw [if_neg (fun h' => hD.1 h' h), if_pos h]
  · rw [if_pos (hD.2 h), if_neg h]

variable {F lam f} in
theorem piMap_xiMap (hfF : f ∈ F) (hf1 : f ≠ 1) (hff : f * f = 1)
    (hFf : ∀ k ∈ F, k = 1 ∨ k = f) {ω : (gbP F lam).X} (hω : ω ∈ (gbP F lam).freeSet)
    (hs : ω ∈ sortedSet F lam) (ξ : G × Unit → ZMod 2) :
    piMap F lam f (xiMap F lam f (ω, ξ)) = ω := by
  funext q
  obtain ⟨γ, rfl⟩ := QuotientGroup.mk_surjective q
  have hab : (ω (γ : G ⧸ F)).1 ≤ (ω (γ : G ⧸ F)).2 := hs _
  rw [piMap_mk lam hff hFf, xiMap_mul_f hfF hf1 hff hω]
  simp only [xiMap]
  split_ifs <;> simp [min_eq_left hab, max_eq_right hab, min_eq_right hab, max_eq_left hab]

variable {F lam f} in
theorem xiMap_of_eq (ω : (gbP F lam).X) (ξ : G × Unit → ZMod 2) (γ : G)
    (h : (ω (γ : G ⧸ F)).1 = (ω (γ : G ⧸ F)).2) :
    xiMap F lam f (ω, ξ) γ = (ω (γ : G ⧸ F)).1 := by
  simp only [xiMap]; split_ifs <;> simp [h]

theorem xiMap_smul (g : G) (ω : (gbP F lam).X) (ξ : G × Unit → ZMod 2) (γ : G) :
    xiMap F lam f (g • ω, fun q => ξ (g⁻¹ * q.1, q.2)) γ = xiMap F lam f (ω, ξ) (g⁻¹ * γ) := by
  simp only [xiMap]
  rw [show (g⁻¹ * γ)⁻¹ • ω = γ⁻¹ • g • ω by rw [mul_inv_rev, inv_inv, mul_smul], mul_assoc]
  rfl

variable {F lam f} in
theorem xiMap_eq_bigPhi (hfF : f ∈ F) (hf1 : f ≠ 1) (hff : f * f = 1)
    (hb : Function.Bijective (eFun F f)) {ω : (gbP F lam).X} (hω : ω ∈ (gbP F lam).freeSet)
    (ξ : G × Unit → ZMod 2) :
    xiMap F lam f (ω, ξ) = bigPhi F lam f hb (ω, deltaMap F lam f (ω, ξ)) := by
  have h01 : (0 : ZMod 2) ≠ 1 := by decide
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  funext γ
  obtain ⟨⟨q, i⟩, rfl⟩ := (eG F f hb).surjective γ
  rw [bigPhi, reix_symm_apply]
  have e0 : eG F f hb (q, 0) = q.out := by simp [eG, eFun]
  have e1 : eG F f hb (q, 1) = q.out * f := by simp [eG, eFun]
  have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
  rcases hi with rfl | rfl
  · rw [e0, finTwoArrow_symm_zero]
    simp only [xiMap, deltaMap, phiPair, QuotientGroup.out_eq']
    by_cases h : q.out⁻¹ • ω ∈ dSet F lam f
    · simp only [h, if_true]; split_ifs <;> rfl
    · simp only [h, if_false]
      rcases zmod2_cases (ξ (q.out * f, ())) with h1 | h1 <;> simp [h1, h01, h11]
  · rw [e1, finTwoArrow_symm_one, xiMap_mul_f hfF hf1 hff hω]
    simp only [deltaMap, phiPair, QuotientGroup.out_eq']
    by_cases h : q.out⁻¹ • ω ∈ dSet F lam f
    · simp only [h, if_true]; split_ifs <;> rfl
    · simp only [h, if_false]
      rcases zmod2_cases (ξ (q.out * f, ())) with h1 | h1 <;> simp [h1, h01, h11]

theorem map_delta_fiber (hb : Function.Bijective (eFun F f)) (ω : (gbP F lam).X) :
    (Measure.infinitePi fun _ : G × Unit => uniformK (ZMod 2)).map
      (fun ξ => deltaMap F lam f (ω, ξ)) = Measure.infinitePi fun _ : G ⧸ F => uniformK (ZMod 2) := by
  classical
  let h : G ⧸ F → (Fin 2 → ZMod 2) → ZMod 2 := fun q β =>
    if q.out⁻¹ • ω ∈ dSet F lam f then β 0 else β 1 + 1
  have hm : ∀ q, Measurable (h q) := fun q => by
    by_cases hq : q.out⁻¹ • ω ∈ dSet F lam f
    · simp only [h, hq, if_true]; exact measurable_pi_apply 0
    · simp only [h, hq, ite_false]
      exact (measurable_zmod2 (fun d : ZMod 2 => d + 1)).comp (measurable_pi_apply 1)
  have hfun : (fun ξ => deltaMap F lam f (ω, ξ)) = (fun z q => h q (z q)) ∘ reix (eGU F f hb) := by
    funext ξ q
    simp [h, deltaMap, reix_apply, eGU, eG, eFun]
  have hmz : Measurable (fun (z : G ⧸ F → Fin 2 → ZMod 2) (q : G ⧸ F) => h q (z q)) :=
    measurable_pi_iff.mpr fun q => (hm q).comp (measurable_pi_apply q)
  rw [hfun, ← Measure.map_map hmz (reix _).measurable,
    (mp_reix (eGU F f hb) (uniformK (ZMod 2))).map_eq, Measure.infinitePi_map_pi _ hm]
  congr 1; funext q
  by_cases hq : q.out⁻¹ • ω ∈ dSet F lam f
  · simp only [h, hq, if_true]; exact (measurePreserving_eval_infinitePi _ 0).map_eq
  · simp only [h, hq, ite_false]
    show Measure.map ((fun d : ZMod 2 => d + 1) ∘ (fun β : Fin 2 → ZMod 2 => β 1)) _ = _
    rw [← Measure.map_map (measurable_zmod2 (fun d : ZMod 2 => d + 1)) (measurable_pi_apply 1),
      show (Measure.infinitePi fun _ : Fin 2 => uniformK (ZMod 2)).map (fun β => β 1) =
        uniformK (ZMod 2) from (measurePreserving_eval_infinitePi _ 1).map_eq]
    exact map_add_uniformK 1

theorem mp_delta (hb : Function.Bijective (eFun F f)) :
    MeasurePreserving (fun p : (gbP F lam).X × (G × Unit → ZMod 2) => (p.1, deltaMap F lam f p))
      ((gbP F lam).μ.prod (Measure.infinitePi fun _ : G × Unit => uniformK (ZMod 2)))
      ((gbP F lam).μ.prod (Measure.infinitePi fun _ : G ⧸ F => uniformK (ZMod 2))) :=
  (MeasurePreserving.id _).skew_product (g := fun ω ξ => deltaMap F lam f (ω, ξ))
    (measurable_deltaMap F lam f) (ae_of_all _ fun ω => map_delta_fiber F lam f hb ω)

theorem map_bigPhi (hb : Function.Bijective (eFun F f)) :
    ((gbP F lam).μ.prod (Measure.infinitePi fun _ : G ⧸ F => uniformK (ZMod 2))).map
      (bigPhi F lam f hb) = Measure.infinitePi fun _ : G => lam := by
  have hzip : ((Measure.infinitePi fun _ : G ⧸ F => pairLaw lam).prod
      (Measure.infinitePi fun _ : G ⧸ F => uniformK (ZMod 2))).map
      (fun p : (G ⧸ F → ℝ × ℝ) × (G ⧸ F → ZMod 2) => fun q => (p.1 q, p.2 q)) =
      Measure.infinitePi fun _ : G ⧸ F => (pairLaw lam).prod (uniformK (ZMod 2)) :=
    infinitePi_prod_map
  have hm1 : Measurable (fun (y : G ⧸ F → (ℝ × ℝ) × ZMod 2) (q : G ⧸ F) =>
      MeasurableEquiv.finTwoArrow.symm (phiPair (y q))) :=
    measurable_pi_iff.mpr fun q => (MeasurableEquiv.finTwoArrow.symm.measurable.comp
      measurable_phiPair).comp (measurable_pi_apply q)
  have hW : (Measure.infinitePi fun _ : G ⧸ F => (pairLaw lam).prod (uniformK (ZMod 2))).map
      (fun (y : G ⧸ F → (ℝ × ℝ) × ZMod 2) (q : G ⧸ F) =>
        MeasurableEquiv.finTwoArrow.symm (phiPair (y q))) =
      Measure.infinitePi fun _ : G ⧸ F => Measure.infinitePi fun _ : Fin 2 => lam := by
    refine (Measure.infinitePi_map_pi (fun _ : G ⧸ F => (pairLaw lam).prod (uniformK (ZMod 2)))
      (f := fun _ y => MeasurableEquiv.finTwoArrow.symm (phiPair y))
      (fun _ => MeasurableEquiv.finTwoArrow.symm.measurable.comp measurable_phiPair)).trans ?_
    congr 1; funext q
    change Measure.map (⇑MeasurableEquiv.finTwoArrow.symm ∘ phiPair) _ = _
    rw [← Measure.map_map MeasurableEquiv.finTwoArrow.symm.measurable measurable_phiPair,
      map_phiPair_pairLaw, ((measurePreserving_finTwoArrow lam).symm _).map_eq,
      Measure.infinitePi_eq_pi]
  have hzm : Measurable (fun p : (G ⧸ F → ℝ × ℝ) × (G ⧸ F → ZMod 2) =>
      fun q => (p.1 q, p.2 q)) := by fun_prop
  calc ((gbP F lam).μ.prod (Measure.infinitePi fun _ : G ⧸ F => uniformK (ZMod 2))).map
        (bigPhi F lam f hb)
      = ((((Measure.infinitePi fun _ : G ⧸ F => pairLaw lam).prod
          (Measure.infinitePi fun _ : G ⧸ F => uniformK (ZMod 2))).map
          (fun p : (G ⧸ F → ℝ × ℝ) × (G ⧸ F → ZMod 2) => fun q => (p.1 q, p.2 q))).map
          (fun (y : G ⧸ F → (ℝ × ℝ) × ZMod 2) (q : G ⧸ F) =>
            MeasurableEquiv.finTwoArrow.symm (phiPair (y q)))).map (reix (eG F f hb)).symm := by
        rw [Measure.map_map hm1 hzm, Measure.map_map (reix _).symm.measurable (hm1.comp hzm)]
        rfl
    _ = Measure.infinitePi fun _ : G => lam := by
        rw [hzip, hW]; exact ((mp_reix (eG F f hb) lam).symm _).map_eq

variable {F f} in
theorem mp_xiMap (hfF : f ∈ F) (hf1 : f ≠ 1) (hff : f * f = 1)
    (hb : Function.Bijective (eFun F f)) (hess : (gbP F lam).EssFree) :
    MeasurePreserving (xiMap F lam f)
      ((gbP F lam).μ.prod (Measure.infinitePi fun _ : G × Unit => uniformK (ZMod 2)))
      (Measure.infinitePi fun _ : G => lam) := by
  refine ⟨measurable_xiMap F lam f, ?_⟩
  have hfree : ∀ᵐ ω ∂(gbP F lam).μ, ω ∈ (gbP F lam).freeSet :=
    ae_iff.2 (measure_freeSet_compl _ hess)
  have hae : xiMap F lam f =ᵐ[(gbP F lam).μ.prod
      (Measure.infinitePi fun _ : G × Unit => uniformK (ZMod 2))]
      (bigPhi F lam f hb ∘ fun p => (p.1, deltaMap F lam f p)) := by
    filter_upwards [measurePreserving_fst.quasiMeasurePreserving.ae hfree] with p hp
    exact xiMap_eq_bigPhi hfF hf1 hff hb hp p.2
  rw [Measure.map_congr hae, ← Measure.map_map (measurable_bigPhi F lam f hb)
    (mp_delta F lam f hb).measurable, (mp_delta F lam f hb).map_eq, map_bigPhi]

end PairingMaps

end PSystem

end Collapse
