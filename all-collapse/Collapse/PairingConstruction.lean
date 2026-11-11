module

public import Collapse.PairingLaw

/-!
# The pairing lemma: the factor of unordered pairs, the transversal and the label set

Second part of the proof of the pairing lemma.
-/

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory

namespace Collapse

namespace PSystem

variable {G : Type} [Group G] [Countable G]

section PairingConstruction

variable (F : Subgroup G) (lam : Measure ℝ) [IsProbabilityMeasure lam] (f : G)

/-- The generalized Bernoulli shift of pairs. -/
abbrev gbP : PSystem G := gb G F (ℝ × ℝ) (pairLaw lam)

theorem exists_involution (hF : Nat.card F = 2) :
    ∃ f : G, f ∈ F ∧ f ≠ 1 ∧ ∀ k ∈ F, k = 1 ∨ k = f := by
  obtain ⟨y, hy, huniq⟩ := (Nat.card_eq_two_iff' (1 : F)).1 hF
  refine ⟨y.1, y.2, fun h => hy (Subtype.ext h), fun k hk => ?_⟩
  by_cases h1 : k = 1
  · exact Or.inl h1
  · exact Or.inr (congrArg Subtype.val (huniq ⟨k, hk⟩ (fun h => h1 (congrArg Subtype.val h))))

variable {F f} in
theorem mul_self_of_involution (hfF : f ∈ F) (hf1 : f ≠ 1) (hFf : ∀ k ∈ F, k = 1 ∨ k = f) :
    f * f = 1 := by
  rcases hFf (f * f) (F.mul_mem hfF hfF) with h | h
  · exact h
  · exact absurd (by simpa using h) hf1

variable {F f} in
theorem mk_mul_f (hfF : f ∈ F) (γ : G) : ((γ * f : G) : G ⧸ F) = (γ : G ⧸ F) :=
  QuotientGroup.eq.2 (by rw [mul_inv_rev, inv_mul_cancel_right]; exact F.inv_mem hfF)

variable {F f} in
theorem out_cases (hFf : ∀ k ∈ F, k = 1 ∨ k = f) (γ : G) :
    (γ : G ⧸ F).out = γ ∨ (γ : G ⧸ F).out = γ * f := by
  have h : γ⁻¹ * (γ : G ⧸ F).out ∈ F :=
    QuotientGroup.eq.1 (QuotientGroup.out_eq' (γ : G ⧸ F)).symm
  rcases hFf _ h with h1 | h1
  · left; exact (inv_mul_eq_one.1 h1).symm
  · right; exact inv_mul_eq_iff_eq_mul.1 h1

open Classical in
/-- The sites of a coset: `(q, 0) ↦ q.out` and `(q, 1) ↦ q.out * f`. -/
def eFun (x : (G ⧸ F) × Fin 2) : G := if x.2 = 0 then x.1.out else x.1.out * f

variable {F f} in
theorem eFun_bijective (hfF : f ∈ F) (hf1 : f ≠ 1) (hFf : ∀ k ∈ F, k = 1 ∨ k = f) :
    Function.Bijective (eFun F f) := by
  have hff := mul_self_of_involution hfF hf1 hFf
  constructor
  · rintro ⟨q, i⟩ ⟨q', i'⟩ h
    have hq : q = q' := by
      have := congrArg (fun g : G => (g : G ⧸ F)) h
      fin_cases i <;> fin_cases i' <;>
        simpa [eFun, mk_mul_f hfF, QuotientGroup.out_eq'] using this
    subst hq
    fin_cases i <;> fin_cases i' <;> simp_all [eFun]
  · intro γ
    rcases out_cases hFf γ with h | h
    · exact ⟨((γ : G ⧸ F), 0), by simp [eFun, h]⟩
    · exact ⟨((γ : G ⧸ F), 1), by simp [eFun, h, mul_assoc, hff]⟩

/-- The pairing of the sites as an equivalence. -/
def eG (hb : Function.Bijective (eFun F f)) : (G ⧸ F) × Fin 2 ≃ G := Equiv.ofBijective _ hb

/-- The pairing of the sites of the bundle coordinates. -/
def eGU (hb : Function.Bijective (eFun F f)) : (G ⧸ F) × Fin 2 ≃ G × Unit :=
  (eG F f hb).trans (Equiv.prodPUnit G).symm

/-- The transversal: `ω` is the representative of `{ω, f • ω}` if `emb ω ≤ emb (f • ω)`. -/
def dSet : Set (gbP F lam).X :=
  {ω | embeddingReal _ ω ≤ embeddingReal _ (f • ω)}

/-- The pair at the coset of `1` consists of two distinct points. -/
def aSet : Set (gbP F lam).X := {ω | (ω ((1 : G) : G ⧸ F)).1 ≠ (ω ((1 : G) : G ⧸ F)).2}

/-- All pairs are sorted. -/
def sortedSet : Set (gbP F lam).X := {ω | ∀ q, (ω q).1 ≤ (ω q).2}

theorem measurable_smul_gbP (g : G) : Measurable (fun ω : (gbP F lam).X => g • ω) :=
  ((gbP F lam).preserving g).measurable

theorem measurableSet_dSet : MeasurableSet (dSet F lam f) :=
  measurableSet_le (measurable_embeddingReal _)
    ((measurable_embeddingReal _).comp (measurable_smul_gbP F lam f))

theorem measurableSet_aSet : MeasurableSet (aSet F lam) := by
  have hS : MeasurableSet {p : ℝ × ℝ | p.1 ≠ p.2} :=
    (measurableSet_eq_fun measurable_fst measurable_snd).compl
  exact hS.preimage (measurable_pi_apply _)

theorem measurableSet_sortedSet : MeasurableSet (sortedSet F lam) := by
  have : sortedSet F lam = ⋂ q, {ω : (gbP F lam).X | (ω q).1 ≤ (ω q).2} := by
    ext; simp only [sortedSet, Set.mem_iInter, Set.mem_ofPred_eq]
  rw [this]
  exact MeasurableSet.iInter fun q =>
    measurableSet_le (measurable_pi_apply q).fst (measurable_pi_apply q).snd

theorem ae_sortedSet : ∀ᵐ ω ∂(gbP F lam).μ, ω ∈ sortedSet F lam := by
  have h1 : ∀ᵐ y ∂(pairLaw lam), y ∈ {y : ℝ × ℝ | y.1 ≤ y.2} :=
    (ae_map_iff measurable_sort.aemeasurable (measurableSet_le measurable_fst measurable_snd)).2
      (ae_of_all _ fun p => min_le_max)
  exact ae_all_iff.2 fun q =>
    (measurePreserving_eval_infinitePi (fun _ : G ⧸ F => pairLaw lam) q).quasiMeasurePreserving.ae h1

variable {F lam f} in
theorem mem_dSet_smul (hff : f * f = 1) (hf1 : f ≠ 1) {ω : (gbP F lam).X}
    (hω : ω ∈ (gbP F lam).freeSet) : f • ω ∈ dSet F lam f ↔ ω ∉ dSet F lam f := by
  show embeddingReal _ (f • ω) ≤ embeddingReal _ (f • f • ω) ↔
    ¬ embeddingReal _ ω ≤ embeddingReal _ (f • ω)
  rw [smul_smul, hff, one_smul]
  constructor
  · intro h h'
    exact hf1 (hω f ((measurableEmbedding_embeddingReal _).injective (le_antisymm h' h)).symm)
  · intro h; exact (not_le.1 h).le

variable {F lam} in
theorem inv_smul_mem_aSet (ω : (gbP F lam).X) (γ : G) :
    γ⁻¹ • ω ∈ aSet F lam ↔ (ω (γ : G ⧸ F)).1 ≠ (ω (γ : G ⧸ F)).2 := by
  show (ω ((γ⁻¹⁻¹ * 1 : G) : G ⧸ F)).1 ≠ (ω ((γ⁻¹⁻¹ * 1 : G) : G ⧸ F)).2 ↔ _
  rw [inv_inv, mul_one]

variable {F lam f} in
theorem smul_mem_aSet (hfF : f ∈ F) (ω : (gbP F lam).X) : f • ω ∈ aSet F lam ↔ ω ∈ aSet F lam := by
  have : ((f⁻¹ * 1 : G) : G ⧸ F) = ((1 : G) : G ⧸ F) := QuotientGroup.eq.2 (by simpa using hfF)
  show (ω ((f⁻¹ * 1 : G) : G ⧸ F)).1 ≠ (ω ((f⁻¹ * 1 : G) : G ⧸ F)).2 ↔ _
  rw [this]; rfl

theorem aSet_measure_ne_zero (hlam : ∀ a, lam ≠ Measure.dirac a) :
    (gbP F lam).μ (aSet F lam) ≠ 0 := by
  have hS : MeasurableSet {p : ℝ × ℝ | p.1 ≠ p.2} :=
    (measurableSet_eq_fun measurable_fst measurable_snd).compl
  have h1 : (gbP F lam).μ (aSet F lam) = pairLaw lam {p | p.1 ≠ p.2} :=
    (measurePreserving_eval_infinitePi (fun _ : G ⧸ F => pairLaw lam)
      ((1 : G) : G ⧸ F)).measure_preimage hS.nullMeasurableSet
  rw [h1, pairLaw, Measure.map_apply measurable_sort hS]
  convert prod_offDiag_ne_zero lam hlam using 2
  ext ⟨a, b⟩
  simp only [Set.mem_preimage, Set.mem_ofPred_eq]
  constructor
  · intro h heq; apply h; rw [heq, min_self, max_self]
  · intro h heq; apply h
    rcases le_total a b with hab | hab
    · rw [min_eq_left hab, max_eq_right hab] at heq; exact heq
    · rw [min_eq_right hab, max_eq_left hab] at heq; exact heq.symm

/-- The set of the bundle: the point is the representative of its `F`-orbit, and its pair at
the coset of `1` consists of two distinct points. -/
def aBun (hess : (gbP F lam).EssFree) : Set ((gbP F lam).free hess).X :=
  Subtype.val ⁻¹' (dSet F lam f ∩ aSet F lam)

theorem measurableSet_aBun (hess : (gbP F lam).EssFree) : MeasurableSet (aBun F lam f hess) :=
  measurable_subtype_coe ((measurableSet_dSet F lam f).inter (measurableSet_aSet F lam))

theorem mp_val_free (hess : (gbP F lam).EssFree) :
    MeasurePreserving (fun x : ((gbP F lam).free hess).X => x.1) ((gbP F lam).free hess).μ
      (gbP F lam).μ :=
  BernoulliIso.measurePreserving_conullSubtype _ (measurableSet_freeSet _)
    (ae_iff.2 (measure_freeSet_compl _ hess))

variable {F f} in
theorem aBun_pos (hfF : f ∈ F) (hf1 : f ≠ 1) (hff : f * f = 1) (hess : (gbP F lam).EssFree)
    (hlam : ∀ a, lam ≠ Measure.dirac a) :
    0 < ((gbP F lam).free hess).μ (aBun F lam f hess) := by
  have hDA := (measurableSet_dSet F lam f).inter (measurableSet_aSet F lam)
  rw [show ((gbP F lam).free hess).μ (aBun F lam f hess) = (gbP F lam).μ (dSet F lam f ∩ aSet F lam)
    from (mp_val_free F lam hess).measure_preimage hDA.nullMeasurableSet]
  refine pos_iff_ne_zero.2 fun h0 => aSet_measure_ne_zero F lam hlam ?_
  have hsub : aSet F lam ⊆ (dSet F lam f ∩ aSet F lam ∪
      (fun ω => f • ω) ⁻¹' (dSet F lam f ∩ aSet F lam)) ∪ (gbP F lam).freeSetᶜ := by
    intro ω hω
    by_cases hfr : ω ∈ (gbP F lam).freeSet
    · by_cases hD : ω ∈ dSet F lam f
      · exact Or.inl (Or.inl ⟨hD, hω⟩)
      · exact Or.inl (Or.inr ⟨(mem_dSet_smul hff hf1 hfr).2 hD, (smul_mem_aSet hfF ω).2 hω⟩)
    · exact Or.inr hfr
  refine measure_mono_null hsub (measure_union_null (measure_union_null h0 ?_)
    (measure_freeSet_compl _ hess))
  rw [((gbP F lam).preserving f).measure_preimage hDA.nullMeasurableSet]; exact h0

open Classical in
/-- The inverse of the pairing map: the order of each pair is read from the bundle bit at
the representative. -/
def xiMap (p : (gbP F lam).X × (G × Unit → ZMod 2)) : G → ℝ := fun γ =>
  if γ⁻¹ • p.1 ∈ dSet F lam f then
    (if p.2 (γ, ()) = 1 then (p.1 (γ : G ⧸ F)).1 else (p.1 (γ : G ⧸ F)).2)
  else (if p.2 (γ * f, ()) = 1 then (p.1 (γ : G ⧸ F)).2 else (p.1 (γ : G ⧸ F)).1)

open Classical in
/-- The order bits of the pairs, read at the canonical representatives `q.out`. -/
def deltaMap (p : (gbP F lam).X × (G × Unit → ZMod 2)) : G ⧸ F → ZMod 2 := fun q =>
  if q.out⁻¹ • p.1 ∈ dSet F lam f then p.2 (q.out, ()) else p.2 (q.out * f, ()) + 1

/-- Ordering the pairs by the bits and spreading them over the sites. -/
def bigPhi (hb : Function.Bijective (eFun F f)) (p : (gbP F lam).X × (G ⧸ F → ZMod 2)) :
    G → ℝ :=
  (reix (eG F f hb)).symm (fun q => MeasurableEquiv.finTwoArrow.symm (phiPair (p.1 q, p.2 q)))

/-- The unordered pairs of a configuration. -/
def piMap (x : G → ℝ) : (gbP F lam).X := fun q =>
  (min (x q.out) (x (q.out * f)), max (x q.out) (x (q.out * f)))

theorem measurable_xiMap : Measurable (xiMap F lam f) := by
  classical
  rw [measurable_pi_iff]; intro γ
  have h1 : ∀ g : G, MeasurableSet
      {p : (gbP F lam).X × (G × Unit → ZMod 2) | p.2 (g, ()) = 1} := fun g =>
    ((measurable_pi_apply _).comp measurable_snd) (DiscreteCoeff.discrete {1})
  have hω : Measurable (fun p : (gbP F lam).X × (G × Unit → ZMod 2) => p.1 (γ : G ⧸ F)) :=
    (measurable_pi_apply _).comp measurable_fst
  exact Measurable.ite
    (p := {p : (gbP F lam).X × (G × Unit → ZMod 2) | γ⁻¹ • p.1 ∈ dSet F lam f})
    ((measurableSet_dSet F lam f).preimage ((measurable_smul_gbP F lam γ⁻¹).comp measurable_fst))
    (Measurable.ite (h1 γ) hω.fst hω.snd) (Measurable.ite (h1 (γ * f)) hω.snd hω.fst)

theorem measurable_deltaMap : Measurable (deltaMap F lam f) := by
  classical
  rw [measurable_pi_iff]; intro q
  exact Measurable.ite
    (p := {p : (gbP F lam).X × (G × Unit → ZMod 2) | q.out⁻¹ • p.1 ∈ dSet F lam f})
    ((measurableSet_dSet F lam f).preimage ((measurable_smul_gbP F lam _).comp measurable_fst))
    ((measurable_pi_apply _).comp measurable_snd)
    ((measurable_zmod2 (fun d : ZMod 2 => d + 1)).comp
      ((measurable_pi_apply (q.out * f, ())).comp measurable_snd))

theorem measurable_piMap : Measurable (piMap F lam f) := by
  have : Measurable (fun (x : G → ℝ) (q : G ⧸ F) =>
      (min (x q.out) (x (q.out * f)), max (x q.out) (x (q.out * f)))) := by
    exact measurable_pi_iff.mpr fun q =>
      ((measurable_pi_apply q.out).min (measurable_pi_apply (q.out * f))).prodMk
      ((measurable_pi_apply q.out).max (measurable_pi_apply (q.out * f)))
  exact this

end PairingConstruction

theorem finTwoArrow_symm_zero (x : ℝ × ℝ) : MeasurableEquiv.finTwoArrow.symm x 0 = x.1 := rfl

theorem finTwoArrow_symm_one (x : ℝ × ℝ) : MeasurableEquiv.finTwoArrow.symm x 1 = x.2 := rfl

theorem pick_one (u v : ℝ) (w : ℝ × ℝ) (hw : w = (min u v, max u v)) (P : Prop) [Decidable P]
    (hP : P ↔ w.1 ≠ w.2) :
    (if (if P then (if u = w.1 then (1 : ZMod 2) else 0) else 0) = 1 then w.1 else w.2) = u := by
  have h01 : (0 : ZMod 2) ≠ 1 := by decide
  subst hw
  simp only at hP ⊢
  rcases le_total u v with h | h
  · simp only [min_eq_left h, max_eq_right h] at hP ⊢
    by_cases hp : P
    · simp [hp]
    · have : u = v := by simpa [hp] using hP
      simp [hp, h01, this]
  · simp only [min_eq_right h, max_eq_left h] at hP ⊢
    by_cases hp : P
    · have : u ≠ v := fun e => (hP.1 hp) e.symm
      simp [hp, h01, this]
    · simp [hp, h01]

theorem pick_two (u v : ℝ) (w : ℝ × ℝ) (hw : w = (min u v, max u v)) (P : Prop) [Decidable P]
    (hP : P ↔ w.1 ≠ w.2) :
    (if (if P then (if v = w.1 then (1 : ZMod 2) else 0) else 0) = 1 then w.2 else w.1) = u := by
  have h01 : (0 : ZMod 2) ≠ 1 := by decide
  subst hw
  simp only at hP ⊢
  rcases le_total u v with h | h
  · simp only [min_eq_left h, max_eq_right h] at hP ⊢
    by_cases hp : P
    · have : v ≠ u := fun e => hP.1 hp e.symm
      simp [hp, h01, this]
    · simp [hp, h01]
  · simp only [min_eq_right h, max_eq_left h] at hP ⊢
    by_cases hp : P
    · simp [hp]
    · have : v = u := by simpa [hp] using hP
      simp [hp, h01, this]

end PSystem

end Collapse
