module

public import Collapse.Collapse
public import Collapse.Dictionary
public import Collapse.Hopf

/-!
# Collapse of extensions

Collapse of extensions: over a free system on which `NP` acts
ergodically, the bundle of a set of positive measure is isomorphic to the product with
`Ber(K^ℕ)`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory

open scoped Classical

namespace Collapse

open LocalSpace BernoulliIso

variable {N G K I V : Type} [Group N] [Countable N] [Group G] [Countable G] [Field K]
  [Fintype K] [MeasurableSpace K] [DiscreteCoeff K] [Fintype I] [Fintype V] [Nonempty I]
  [Nonempty V]

/-- The ergodic case, on an invariant set `U` of full measure:
`(A ∩ U) ≅ ∞ · (U)` for every set `A` of positive measure. -/
theorem exists_toClass_eq_infty (τ : TowerSetting N G) (s : AlgebraicInput K N I V)
    (S : PSystem G) [S.IsFree] [ErgodicSMul τ.Λ S.X S.μ] (A : Set S.X) (hA : MeasurableSet A)
    (hpos : 0 < S.μ A) :
    ∃ (U : Set S.X) (hU : MeasurableSet U), (∀ (g : G) (x : S.X), x ∈ U → g • x ∈ U) ∧
      S.μ Uᶜ = 0 ∧
      toClass (single (Λ := τ.Λ) (K := K) (A ∩ U) (hA.inter hU)) =
        SigmaMonoid.infty (toClass (single U hU)) := by
  obtain ⟨U₀, hU₀, ⟨T₀⟩⟩ := exists_markerTower τ s.J s.finiteJ S.μ S.preserving
  obtain ⟨n, hn⟩ := ENNReal.exists_inv_two_pow_lt hpos.ne'
  have hDn : S.μ (T₀.D n) ≤ S.μ A := by
    rw [T₀.measure_D S.μ S.preserving hU₀ n]; rw [ENNReal.inv_pow]; exact hn.le
  obtain ⟨U₁, hU₁m, hU₁i, hU₁, B', hB'm, hB'sub, ⟨E⟩⟩ :=
    exists_equidecomp_of_ergodic S τ.Λ (T₀.D n) A (T₀.measurable_D n) hA hDn
  set U := U₀ ∩ U₁ with hUdef
  have hUm : MeasurableSet U := T₀.U_measurable.inter hU₁m
  have hUi : ∀ (g : G) (x : S.X), x ∈ U → g • x ∈ U :=
    fun g x hx => ⟨T₀.U_invariant g x hx.1, hU₁i g x hx.2⟩
  have hUc : S.μ Uᶜ = 0 := by
    rw [Set.compl_inter]; exact measure_union_null hU₀ hU₁
  let T := T₀.restrict U hUm Set.inter_subset_left hUi
  have E' := E.restrict U hUm (fun g x hx => hUi (g : G) x hx)
  have hsrc : (fun _ : Unit => T₀.D n ∩ U₁ ∩ U) = (fun _ : Unit => T.D n) := by
    funext _
    show T₀.D n ∩ U₁ ∩ (U₀ ∩ U₁) = T₀.D n ∩ (U₀ ∩ U₁)
    ext x; simp only [Set.mem_inter_iff]; tauto
  rw [hsrc] at E'
  refine ⟨U, hUm, hUi, hUc, ?_⟩
  exact T.toClass_single_eq_infty s (A ∩ U) (hA.inter hUm) Set.inter_subset_right n (B' ∩ U)
    (hB'm.inter hUm) (fun x hx => ⟨(hB'sub hx.1).1, hx.2⟩) ⟨E'⟩

/-- **Collapse of extensions**. -/
theorem bundle_iso_prod (τ : TowerSetting N G) (s : AlgebraicInput K N I V) (S : PSystem G)
    [S.IsFree] [ErgodicSMul τ.Λ S.X S.μ] (A : Set S.X) (hA : MeasurableSet A)
    (hpos : 0 < S.μ A) :
    (S.bundle K Unit (fun _ => A) (fun _ => hA)).Iso
      (S.prod (PSystem.bernoulli G (ℕ → K) (cantorK K))) := by
  obtain ⟨U, hU, hinv, hfull, h⟩ := exists_toClass_eq_infty τ s S A hA hpos
  have h1 : toClass (ofSet (Λ := τ.Λ) (K := K) (fun _ : Unit => A ∩ U) (fun _ => hA.inter hU)) =
      toClass (ofSet (fun _ : ℕ × Unit => U) (fun _ => hU)) := by
    exact h.trans (toClass_ofSet_prod (Λ := τ.Λ) (K := K) (ι := ℕ) (fun _ : Unit => U)
      (fun _ => hU)).symm
  have i0 : (S.bundle K Unit (fun _ => A) (fun _ => hA)).Iso
      (S.bundle K Unit (fun _ => A ∩ U) (fun _ => hA.inter hU)) :=
    S.bundle_iso_of_inter_eq K U hU hinv hfull _ _ _ _ (fun _ => by simp [Set.inter_assoc])
  have i1 := S.bundle_iso_of_toClass_eq τ.Λ K _ _ _ _ h1
  have i2 : (S.bundle K (ℕ × Unit) (fun _ => U) (fun _ => hU)).Iso
      (S.bundle K (ℕ × Unit) (fun _ => Set.univ) (fun _ => MeasurableSet.univ)) :=
    S.bundle_iso_of_inter_eq K U hU hinv hfull _ _ _ _ (fun _ => by simp)
  exact i0.trans (i1.trans (i2.trans (S.bundle_univ_iso K (ℕ × Unit))))

end Collapse
