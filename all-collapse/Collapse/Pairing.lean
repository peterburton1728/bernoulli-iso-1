module

public import Collapse.PairingMaps

/-!
# The pairing lemma

The pairing lemma: for a subgroup `F` of order 2 and a base on
`ℝ` which is not a point mass, `Ber(lam)` is isomorphic to the bundle, with coefficients in
`ZMod 2`, of a set of positive measure over the free part of `GB(F; pairLaw lam)`. The
definitions and the earlier steps are in `PairingLaw`, `PairingConstruction`, `PairingMaps`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory

namespace Collapse

namespace PSystem

variable {G : Type} [Group G] [Countable G]

section PairingBundle

variable (F : Subgroup G) (lam : Measure ℝ) [IsProbabilityMeasure lam] (f : G)
  (hess : (gbP F lam).EssFree)

/-- The bundle of the pairing lemma. -/
abbrev bunP : PSystem G :=
  ((gbP F lam).free hess).bundle (ZMod 2) Unit (fun _ => aBun F lam f hess)
    (fun _ => measurableSet_aBun F lam f hess)

/-- The map from the bundle to the Bernoulli shift. -/
def xiB (p : (bunP F lam f hess).X) : (bernoulli G ℝ lam).X := xiMap F lam f (p.1.1, p.2)

/-- The mask-fixed points with sorted pairs. -/
def sSet : Set (bunP F lam f hess).X :=
  {p | maskMap ((gbP F lam).free hess) (ZMod 2) (fun _ : Unit => aBun F lam f hess) p = p ∧
    p.1.1 ∈ sortedSet F lam}

/-- The configurations whose unordered pairs form a free point. -/
def tSet : Set (bernoulli G ℝ lam).X := {x | piMap F lam f x ∈ (gbP F lam).freeSet}

theorem measurable_xiB : Measurable (xiB F lam f hess) :=
  (measurable_xiMap F lam f).comp
    ((measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd)

variable {F f} in
theorem xiB_mask (hfF : f ∈ F) (hf1 : f ≠ 1) (hff : f * f = 1) (p : (bunP F lam f hess).X) :
    xiB F lam f hess (maskMap ((gbP F lam).free hess) (ZMod 2)
      (fun _ : Unit => aBun F lam f hess) p) = xiB F lam f hess p := by
  classical
  funext γ
  show xiMap F lam f (p.1.1, fun q => if q.1⁻¹ • p.1 ∈ aBun F lam f hess then p.2 q else 0) γ =
    xiMap F lam f (p.1.1, p.2) γ
  have hω := p.1.2
  by_cases hab : (p.1.1 (γ : G ⧸ F)).1 = (p.1.1 (γ : G ⧸ F)).2
  · rw [xiMap_of_eq _ _ _ hab, xiMap_of_eq _ _ _ hab]
  · have hγ : ∀ g : G, g⁻¹ • p.1.1 ∈ dSet F lam f → p.1.1 (g : G ⧸ F) = p.1.1 (γ : G ⧸ F) →
        g⁻¹ • p.1 ∈ aBun F lam f hess := fun g hg he =>
      Set.mem_preimage.2 (Set.mem_inter hg ((inv_smul_mem_aSet p.1.1 g).2 (by rw [he]; exact hab)))
    simp only [xiMap]
    by_cases h : γ⁻¹ • p.1.1 ∈ dSet F lam f
    · rw [if_pos h, if_pos h, if_pos (hγ γ h rfl)]
    · have h' : (γ * f)⁻¹ • p.1.1 ∈ dSet F lam f := by
        rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hff, mul_smul]
        exact (mem_dSet_smul hff hf1 ((gbP F lam).freeSet_invariant γ⁻¹ _ hω)).2 h
      rw [if_neg h, if_neg h, if_pos (hγ (γ * f) h' (by rw [mk_mul_f hfF]))]

theorem xiB_smul (g : G) (p : (bunP F lam f hess).X) :
    xiB F lam f hess (g • p) = g • xiB F lam f hess p := by
  funext γ
  exact xiMap_smul F lam f g p.1.1 p.2 γ

variable {F f} in
theorem mp_xiB (hfF : f ∈ F) (hf1 : f ≠ 1) (hff : f * f = 1)
    (hb : Function.Bijective (eFun F f)) :
    MeasurePreserving (xiB F lam f hess) (bunP F lam f hess).μ (bernoulli G ℝ lam).μ := by
  have hmask := measurable_maskMap ((gbP F lam).free hess) (ZMod 2)
    (fun _ : Unit => aBun F lam f hess) (fun _ => measurableSet_aBun F lam f hess)
  refine ⟨measurable_xiB F lam f hess, ?_⟩
  have hv : MeasurePreserving
      (fun p : ((gbP F lam).free hess).X × (G × Unit → ZMod 2) => (p.1.1, p.2))
      (((gbP F lam).free hess).μ.prod (Measure.infinitePi fun _ : G × Unit => uniformK (ZMod 2)))
      ((gbP F lam).μ.prod (Measure.infinitePi fun _ : G × Unit => uniformK (ZMod 2))) :=
    (mp_val_free F lam hess).prod (MeasurePreserving.id _)
  show Measure.map (xiB F lam f hess) (Measure.map (maskMap _ _ _) _) = _
  rw [Measure.map_map (measurable_xiB F lam f hess) hmask]
  have : xiB F lam f hess ∘ maskMap ((gbP F lam).free hess) (ZMod 2)
      (fun _ : Unit => aBun F lam f hess) = xiMap F lam f ∘ (fun p => (p.1.1, p.2)) :=
    funext fun p => xiB_mask lam hess hfF hf1 hff p
  rw [this]
  exact ((mp_xiMap lam hfF hf1 hff hb hess).comp hv).map_eq

variable {F f} in
theorem xiB_injOn (hfF : f ∈ F) (hf1 : f ≠ 1) (hff : f * f = 1)
    (hFf : ∀ k ∈ F, k = 1 ∨ k = f) : Set.InjOn (xiB F lam f hess) (sSet F lam f hess) := by
  have h01 : (0 : ZMod 2) ≠ 1 := by decide
  rintro ⟨w, ξ⟩ ⟨hm, hs⟩ ⟨w', ξ'⟩ ⟨hm', hs'⟩ heq
  have hww : w = w' := by
    have := congrArg (piMap F lam f) heq
    change piMap F lam f (xiMap F lam f (w.1, ξ)) = piMap F lam f (xiMap F lam f (w'.1, ξ'))
      at this
    rw [piMap_xiMap hfF hf1 hff hFf w.2 hs, piMap_xiMap hfF hf1 hff hFf w'.2 hs'] at this
    exact Subtype.ext this
  subst hww
  refine Prod.ext rfl (funext fun ⟨γ, u⟩ => ?_)
  have e1 := congrFun (congrArg Prod.snd hm) (γ, u)
  have e2 := congrFun (congrArg Prod.snd hm') (γ, u)
  simp only [maskMap] at e1 e2
  by_cases hA : γ⁻¹ • w ∈ aBun F lam f hess
  · obtain ⟨hD, hA0⟩ := hA
    have hD' : γ⁻¹ • w.1 ∈ dSet F lam f := hD
    have hab := (inv_smul_mem_aSet w.1 γ).1 hA0
    have hx := congrFun heq γ
    change xiMap F lam f (w.1, ξ) γ = xiMap F lam f (w.1, ξ') γ at hx
    simp only [xiMap, if_pos hD'] at hx
    cases u
    rcases zmod2_cases (ξ (γ, ())) with h1 | h1 <;> rcases zmod2_cases (ξ' (γ, ())) with h2 | h2 <;>
      simp_all
  · rw [if_neg hA] at e1 e2
    show ξ (γ, u) = ξ' (γ, u)
    rw [← e1, ← e2]

variable {F f} in
theorem xiB_surjOn (hfF : f ∈ F) (hf1 : f ≠ 1) (hff : f * f = 1)
    (hFf : ∀ k ∈ F, k = 1 ∨ k = f) :
    Set.SurjOn (xiB F lam f hess) (sSet F lam f hess) (tSet F lam f) := by
  classical
  intro x hx
  have hx' : piMap F lam f x ∈ (gbP F lam).freeSet := hx
  let ω0 : ((gbP F lam).free hess).X := ⟨piMap F lam f x, hx'⟩
  let ξ : G × Unit → ZMod 2 := fun q => if q.1⁻¹ • ω0 ∈ aBun F lam f hess then
      (if x q.1 = (piMap F lam f x (q.1 : G ⧸ F)).1 then 1 else 0) else 0
  refine ⟨(ω0, ξ), And.intro ?_ ?_, ?_⟩
  · refine Prod.ext rfl (funext fun q => ?_)
    show (if q.1⁻¹ • ω0 ∈ aBun F lam f hess then ξ q else 0) = ξ q
    split_ifs with h
    · rfl
    · simp only [ξ, if_neg h]
  · intro q; exact min_le_max
  · funext γ
    show xiMap F lam f (piMap F lam f x, ξ) γ = x γ
    have hw := piMap_mk lam hff hFf x γ
    have hAiff : ∀ g : G, g⁻¹ • piMap F lam f x ∈ dSet F lam f →
        piMap F lam f x (g : G ⧸ F) = piMap F lam f x (γ : G ⧸ F) →
        (g⁻¹ • ω0 ∈ aBun F lam f hess ↔
          (piMap F lam f x (γ : G ⧸ F)).1 ≠ (piMap F lam f x (γ : G ⧸ F)).2) := by
      intro g hg he
      rw [← he]
      exact ⟨fun h => by
        obtain ⟨_, h2⟩ := h
        exact (inv_smul_mem_aSet (piMap F lam f x) g).1 h2,
        fun h => Set.mem_preimage.2 (Set.mem_inter hg ((inv_smul_mem_aSet _ g).2 h))⟩
    simp only [xiMap]
    by_cases hD : γ⁻¹ • piMap F lam f x ∈ dSet F lam f
    · rw [if_pos hD]
      exact pick_one (x γ) (x (γ * f)) _ hw _ (hAiff γ hD rfl)
    · rw [if_neg hD]
      have hD' : (γ * f)⁻¹ • piMap F lam f x ∈ dSet F lam f := by
        rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hff, mul_smul]
        exact (mem_dSet_smul hff hf1 ((gbP F lam).freeSet_invariant γ⁻¹ _ hx')).2 hD
      have he : piMap F lam f x ((γ * f : G) : G ⧸ F) = piMap F lam f x (γ : G ⧸ F) := by
        rw [mk_mul_f hfF]
      show (if (if (γ * f)⁻¹ • ω0 ∈ aBun F lam f hess then
        (if x (γ * f) = (piMap F lam f x ((γ * f : G) : G ⧸ F)).1 then (1 : ZMod 2) else 0)
          else 0) = 1 then (piMap F lam f x (γ : G ⧸ F)).2 else
        (piMap F lam f x (γ : G ⧸ F)).1) = x γ
      rw [he]
      exact pick_two (x γ) (x (γ * f)) _ hw _ (hAiff (γ * f) hD' he)

variable {F f} in
theorem iso_main (hfF : f ∈ F) (hf1 : f ≠ 1) (hFf : ∀ k ∈ F, k = 1 ∨ k = f) :
    (bunP F lam f hess).Iso (bernoulli G ℝ lam) := by
  classical
  have hff := mul_self_of_involution hfF hf1 hFf
  have hb := eFun_bijective hfF hf1 hFf
  have hmask := measurable_maskMap ((gbP F lam).free hess) (ZMod 2)
    (fun _ : Unit => aBun F lam f hess) (fun _ => measurableSet_aBun F lam f hess)
  have hs : MeasurableSet (sSet F lam f hess) :=
    (measurableSet_eq_fun hmask measurable_id).inter
      ((measurableSet_sortedSet F lam).preimage (measurable_subtype_coe.comp measurable_fst))
  have ht : MeasurableSet (tSet F lam f) :=
    (measurableSet_freeSet _).preimage (measurable_piMap F lam f)
  have hmp := mp_xiB lam hess hfF hf1 hff hb
  have hsc : ∀ᵐ p ∂(bunP F lam f hess).μ, p ∈ sSet F lam f hess := by
    show ∀ᵐ p ∂(Measure.map (maskMap ((gbP F lam).free hess) (ZMod 2)
      (fun _ : Unit => aBun F lam f hess)) (((gbP F lam).free hess).μ.prod
        (Measure.infinitePi fun _ : G × Unit => uniformK (ZMod 2)))), p ∈ sSet F lam f hess
    refine (ae_map_iff hmask.aemeasurable hs).2 ?_
    have h1 : ∀ᵐ ω ∂((gbP F lam).free hess).μ, ω.1 ∈ sortedSet F lam :=
      (mp_val_free F lam hess).quasiMeasurePreserving.ae (ae_sortedSet F lam)
    filter_upwards [measurePreserving_fst.quasiMeasurePreserving.ae h1] with p hp
    refine And.intro ?_ hp
    refine Prod.ext rfl (funext fun q => ?_)
    simp only [maskMap]; split_ifs <;> simp
  have hmaps : Set.MapsTo (xiB F lam f hess) (sSet F lam f hess) (tSet F lam f) := by
    intro p hp
    obtain ⟨_, hps⟩ := hp
    show piMap F lam f (xiMap F lam f (p.1.1, p.2)) ∈ (gbP F lam).freeSet
    rw [piMap_xiMap hfF hf1 hff hFf p.1.2 hps]; exact p.1.2
  have htc : ∀ᵐ x ∂(bernoulli G ℝ lam).μ, x ∈ tSet F lam f := by
    refine ae_iff.2 ?_
    have h := hmp.measure_preimage ht.compl.nullMeasurableSet
    show (bernoulli G ℝ lam).μ (tSet F lam f)ᶜ = 0
    rw [← h]
    exact measure_mono_null (fun p hp hps => hp (hmaps hps)) (ae_iff.1 hsc)
  have hsi : ∀ (g : G) (p : (bunP F lam f hess).X), p ∈ sSet F lam f hess →
      g • p ∈ sSet F lam f hess := by
    intro g p hp
    obtain ⟨w, ξ⟩ := p
    obtain ⟨hm, hsort⟩ := hp
    refine And.intro ?_ ?_
    · refine Prod.ext rfl (funext fun q => ?_)
      have e := congrFun (congrArg Prod.snd hm) (g⁻¹ * q.1, q.2)
      show (if q.1⁻¹ • (g • w) ∈ aBun F lam f hess then
        ξ (g⁻¹ * q.1, q.2) else 0) = ξ (g⁻¹ * q.1, q.2)
      simp only [maskMap] at e
      rw [mul_inv_rev, inv_inv, mul_smul] at e
      split_ifs with h
      · rfl
      · rw [if_neg h] at e; exact e
    · intro q; exact hsort (g⁻¹ • q)
  have hti : ∀ (g : G) (x : (bernoulli G ℝ lam).X), x ∈ tSet F lam f → g • x ∈ tSet F lam f := by
    intro g x hx
    show piMap F lam f (g • x) ∈ (gbP F lam).freeSet
    rw [piMap_smul lam hff hFf g x]
    exact (gbP F lam).freeSet_invariant g _ hx
  exact ⟨conjMk (sSet F lam f hess) (tSet F lam f) hs ht hsc htc hsi hti (xiB F lam f hess) hmp
    ⟨hmaps, xiB_injOn lam hess hfF hf1 hff hFf, xiB_surjOn lam hess hfF hf1 hff hFf⟩
    (fun g p _ => xiB_smul F lam f hess g p)⟩

end PairingBundle

/-- **Pairing.** For a subgroup `F` of order 2 and a base `lam` on `ℝ` which is not a point
mass, `Ber(lam)` is isomorphic to the bundle, with coefficients in `ZMod 2`, of a set of
positive measure over the free part of `GB(F; pairLaw lam)`. -/
theorem pairing (F : Subgroup G) (hF : Nat.card F = 2) (lam : Measure ℝ)
    [IsProbabilityMeasure lam] (hlam : ∀ a, lam ≠ Measure.dirac a)
    (hess : (gb G F (ℝ × ℝ) (pairLaw lam)).EssFree) :
    ∃ (A : Set ((gb G F (ℝ × ℝ) (pairLaw lam)).free hess).X) (hA : MeasurableSet A),
      0 < ((gb G F (ℝ × ℝ) (pairLaw lam)).free hess).μ A ∧
      (bernoulli G ℝ lam).Iso
        (((gb G F (ℝ × ℝ) (pairLaw lam)).free hess).bundle (ZMod 2) Unit (fun _ => A)
          (fun _ => hA)) := by
  obtain ⟨f, hfF, hf1, hFf⟩ := exists_involution F hF
  have hff := mul_self_of_involution hfF hf1 hFf
  exact ⟨aBun F lam f hess, measurableSet_aBun F lam f hess, aBun_pos lam hfF hf1 hff hess hlam,
    (iso_main lam hess hfF hf1 hFf).symm⟩

end PSystem

end Collapse
