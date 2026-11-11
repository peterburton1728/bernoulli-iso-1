module

public import Collapse.Markers

/-!
# The relations (S1) and (S2)

Local spaces are taken for the action of the
subgroup `τ.Λ` (the group `NP`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Collapse

open LocalSpace

/-- Equal level families give equal classes. -/
theorem toClass_ofSet_congr {Λ' Y K' : Type} [Group Λ'] [MulAction Λ' Y] [MeasurableSpace Y]
    [BorelFree Λ' Y] [Ring K'] [MeasurableSpace K'] [DiscreteCoeff K'] {J : Type} [Countable J]
    {A B : J → Set Y} (h : A = B) (hA : ∀ j, MeasurableSet (A j))
    (hB : ∀ j, MeasurableSet (B j)) :
    toClass (ofSet (Λ := Λ') (K := K') A hA) = toClass (ofSet B hB) := by
  subst h; rfl

/-- Reindexing the source levels of an equidecomposition along an equivalence. -/
def Equidecomp.reindexSrc {Λ' Y J₀ J J' : Type} [Group Λ'] [MulAction Λ' Y] [MeasurableSpace Y]
    {A : J → Set Y} {B : J' → Set Y} (E : Equidecomp Λ' A B) (e : J₀ ≃ J) :
    Equidecomp Λ' (fun j => A (e j)) B where
  piece g j j' := E.piece g (e j) j'
  measurable_piece g j j' := E.measurable_piece g (e j) j'
  piece_subset g j j' := E.piece_subset g (e j) j'
  existsUnique_piece j x hx := E.existsUnique_piece (e j) x hx
  mapsTo g j j' := E.mapsTo g (e j) j'
  existsUnique_source j' y hy := by
    obtain ⟨⟨g, j⟩, h1, h2⟩ := E.existsUnique_source j' y hy
    refine ⟨(g, e.symm j), by simpa using h1, fun q hq => ?_⟩
    have := h2 (q.1, e q.2) hq
    simp only [Prod.mk.injEq] at this
    obtain ⟨rfl, rfl⟩ := this
    simp

variable {N G X V : Type} [Group N] [Group G] [MulAction G X] [MeasurableSpace X]
  [BorelFree G X]

namespace MarkerTower

variable {τ : TowerSetting N G} {Jv : V → Subgroup N} {U : Set X}

/-- The class `M k` of the local space `(D k)`. -/
def M (T : MarkerTower τ Jv U) (K : Type) [Ring K] [MeasurableSpace K] [DiscreteCoeff K]
    (k : ℕ) : LocalSpace.Class τ.Λ X K :=
  toClass (single (T.D k) (T.measurable_D k))

/-- The class of the local space `(U)`. -/
def top (T : MarkerTower τ Jv U) (K : Type) [Ring K] [MeasurableSpace K] [DiscreteCoeff K] :
    LocalSpace.Class τ.Λ X K :=
  toClass (single U T.U_measurable)

variable (T : MarkerTower τ Jv U) (K : Type) [Ring K] [MeasurableSpace K] [DiscreteCoeff K]

theorem relIndex_H_succ (k : ℕ) : (τ.H k).relIndex (τ.H (k + 1)) = 2 := by
  have h := Subgroup.relIndex_mul_card (H := τ.H k) (K := τ.H (k + 1))
  rw [inf_of_le_left (τ.H_mono (Nat.le_succ k)), τ.H_card, τ.H_card, pow_succ'] at h
  exact Nat.eq_of_mul_eq_mul_right (by positivity) h

theorem eq_one_of_mem (k : ℕ) {g : G} (hg : g ∈ τ.H k) {x : X} (hx : x ∈ T.D k)
    (hgx : g • x ∈ T.D k) : g = 1 := by
  obtain ⟨h, -, hu⟩ := T.D_trans k x (T.D_sub k hx)
  have h1 := hu ⟨g, hg⟩ hgx
  have h2 := hu 1 (by simpa using hx)
  exact congrArg Subtype.val (h1.trans h2.symm)

/-- The map `σ` from `D (k + 1)` onto `D k \ D (k + 1)`, as an equidecomposition. -/
def diffEq (k : ℕ) :
    Equidecomp τ.Λ (fun _ : Unit => T.D (k + 1)) (fun _ : Unit => T.D k \ T.D (k + 1)) where
  piece g _ _ :=
    {z | ((g : G) ∈ τ.H (k + 1) ∧ (g : G) ∉ τ.H k) ∧ z ∈ T.D (k + 1) ∧ (g : G) • z ∈ T.D k}
  measurable_piece g _ _ := by
    by_cases hp : (g : G) ∈ τ.H (k + 1) ∧ (g : G) ∉ τ.H k
    · convert (T.measurable_D (k + 1)).inter
        (BorelFree.measurable_smul (g : G) (T.measurable_D k)) using 1
      ext z
      exact ⟨fun h => h.2, fun h => ⟨hp, h⟩⟩
    · simp [hp]
  piece_subset g _ _ z hz := hz.2.1
  existsUnique_piece _ z hz := by
    obtain ⟨t, ht, hX⟩ := Subgroup.relIndex_eq_two_iff.1 (relIndex_H_succ (τ := τ) k)
    have htk : t ∉ τ.H k := by
      have := hX 1 (one_mem _); simpa [Xor] using this
    obtain ⟨h, hh, hu⟩ := T.D_trans k ((t : G) • z) (T.U_invariant t z (T.D_sub _ hz))
    have hht : (h : G) * t ∈ τ.H (k + 1) := mul_mem (τ.H_mono (Nat.le_succ k) h.2) ht
    have hhtk : (h : G) * t ∉ τ.H k := fun hm => htk (by simpa using mul_mem (inv_mem h.2) hm)
    refine ⟨(⟨(h : G) * t, τ.H_le_Λ (k + 1) hht⟩, ()), ⟨⟨hht, hhtk⟩, hz, by simpa [mul_smul] using hh⟩, ?_⟩
    rintro ⟨g, ⟨⟩⟩ ⟨⟨hg1, hg2⟩, -, hg3⟩
    have hgt : (g : G) * t⁻¹ ∈ τ.H k := by
      have := hX ((g : G) * t⁻¹) (mul_mem hg1 (inv_mem ht))
      simp only [inv_mul_cancel_right] at this
      simpa [hg2] using this
    have := hu ⟨_, hgt⟩ (by simpa [mul_smul] using hg3)
    subst this
    exact Prod.ext (Subtype.ext (by simp)) rfl
  mapsTo g _ _ z hz := by
    obtain ⟨⟨hg1, hg2⟩, hz1, hz2⟩ := hz
    rw [Subgroup.smul_def]
    refine ⟨hz2, fun h => hg2 ?_⟩
    rw [T.eq_one_of_mem (k + 1) hg1 hz1 h]
    exact one_mem _
  existsUnique_source _ y hy := by
    obtain ⟨hy1, hy2⟩ := hy
    obtain ⟨u, hu1, hu2⟩ := T.D_trans (k + 1) y (T.D_sub k hy1)
    have huk : (u : G) ∉ τ.H k := fun hm => hy2 (by
      have := T.eq_one_of_mem k hm hy1 (T.D_anti (Nat.le_succ k) hu1)
      simpa [this] using hu1)
    refine ⟨(⟨(u : G)⁻¹, τ.H_le_Λ (k + 1) (inv_mem u.2)⟩, ()), ?_, ?_⟩
    · refine ⟨⟨inv_mem u.2, fun hm => huk (by simpa using inv_mem hm)⟩, ?_, ?_⟩
      · simpa [Subgroup.smul_def] using hu1
      · simpa [Subgroup.smul_def] using hy1
    · rintro ⟨g, ⟨⟩⟩ ⟨⟨hg1, hg2⟩, hg3, -⟩
      have := hu2 ⟨(g : G)⁻¹, inv_mem hg1⟩ (by simpa [Subgroup.smul_def] using hg3)
      subst this
      exact Prod.ext (Subtype.ext (by simp)) rfl

/-- Two copies of `D (k + 1)` onto `D k`: the identity on one copy, `σ` on the other. -/
def stepEq (k : ℕ) :
    Equidecomp τ.Λ (fun _ : Bool => T.D (k + 1)) (fun _ : Unit => T.D k) where
  piece g b _ := cond b ((T.diffEq k).piece g () ()) {z | g = 1 ∧ z ∈ T.D (k + 1)}
  measurable_piece g b _ := by
    cases b
    · by_cases hg : g = 1 <;> simp [hg, T.measurable_D]
    · exact (T.diffEq k).measurable_piece g () ()
  piece_subset g b _ z hz := by
    cases b
    · exact hz.2
    · exact (T.diffEq k).piece_subset g () () hz
  existsUnique_piece b z hz := by
    cases b
    · refine ⟨(1, ()), ⟨rfl, hz⟩, ?_⟩
      rintro ⟨g, ⟨⟩⟩ ⟨rfl, -⟩
      rfl
    · exact (T.diffEq k).existsUnique_piece () z hz
  mapsTo g b _ z hz := by
    cases b
    · obtain ⟨rfl, hz⟩ := hz
      simpa using T.D_anti (Nat.le_succ k) hz
    · exact ((T.diffEq k).mapsTo g () () z hz).1
  existsUnique_source _ y hy := by
    by_cases hy' : y ∈ T.D (k + 1)
    · refine ⟨(1, false), ⟨rfl, by simpa using hy'⟩, ?_⟩
      rintro ⟨g, b⟩ hq
      cases b
      · obtain ⟨rfl, -⟩ := hq
        rfl
      · have := ((T.diffEq k).mapsTo g () () _ hq).2
        simp at this
        exact absurd hy' this
    · obtain ⟨⟨g, ⟨⟩⟩, h1, h2⟩ := (T.diffEq k).existsUnique_source () y ⟨hy, hy'⟩
      refine ⟨(g, true), h1, ?_⟩
      rintro ⟨g', b⟩ hq
      cases b
      · obtain ⟨rfl, h⟩ := hq
        exact absurd (by simpa using h) hy'
      · have := h2 (g', ()) hq
        simp only [Prod.mk.injEq] at this
        rw [this.1]

theorem M_zero : T.M K 0 = T.top K :=
  toClass_ofSet_congr (funext fun _ => T.D_zero) _ _

/-- Two copies of `D (k + 1)` are equidecomposable with `D k`. -/
theorem equidecomp_step (k : ℕ) :
    Nonempty (Equidecomp τ.Λ (fun _ : Bool => T.D (k + 1)) (fun _ : Unit => T.D k)) := ⟨T.stepEq k⟩

/-- `D (k + 1)` is equidecomposable with `D k \ D (k + 1)`. -/
theorem equidecomp_diff (k : ℕ) :
    Nonempty (Equidecomp τ.Λ (fun _ : Unit => T.D (k + 1))
      (fun _ : Unit => T.D k \ T.D (k + 1))) := ⟨T.diffEq k⟩

/-- (S1): `M k = 2 · M (k + 1)`. -/
theorem S1 (k : ℕ) : T.M K k = 2 • T.M K (k + 1) := by
  have h1 := ((T.stepEq k).reindexSrc (Equiv.prodPUnit Bool)).toClass_eq (K := K)
    (fun _ => T.measurable_D (k + 1)) (fun _ => T.measurable_D k)
  have h2 := toClass_ofSet_prod (Λ := τ.Λ) (K := K) (ι := Bool)
    (fun _ : Unit => T.D (k + 1)) (fun _ => T.measurable_D (k + 1))
  rw [two_nsmul, SigmaMonoid.add_def]
  refine h1.symm.trans (h2.trans ?_)
  congr 1
  funext i
  cases i <;> rfl

/-- (S2): `M n` is the sum of the `M k` over `k > n`. -/
theorem S2 (n : ℕ) : T.M K n = SigmaMonoid.sum (fun k : ℕ => T.M K (n + k + 1)) := by
  have hA : ∀ (i : ℕ) (_ : Unit), MeasurableSet (T.D (n + i) \ T.D (n + i + 1)) :=
    fun i _ => (T.measurable_D _).diff (T.measurable_D _)
  have hdisj : ∀ _ : Unit, Pairwise fun i i' =>
      Disjoint (T.D (n + i) \ T.D (n + i + 1)) (T.D (n + i') \ T.D (n + i' + 1)) := by
    intro _ i i' hne
    have key : ∀ a b : ℕ, a < b →
        Disjoint (T.D (n + a) \ T.D (n + a + 1)) (T.D (n + b) \ T.D (n + b + 1)) := by
      intro a b hab
      rw [Set.disjoint_left]
      intro x hx hx'
      exact hx.2 (T.D_anti (by omega : n + a + 1 ≤ n + b) hx'.1)
    rcases lt_or_gt_of_ne hne with h | h
    · exact key _ _ h
    · exact (key _ _ h).symm
  have hU : (fun _ : Unit => T.D n) = fun _ => ⋃ i, T.D (n + i) \ T.D (n + i + 1) := by
    funext _
    ext x
    simp only [Set.mem_iUnion, Set.mem_sdiff]
    constructor
    · intro hx
      have hex : ∃ m, x ∉ T.D (n + m) := by
        by_contra hc
        push Not at hc
        have : x ∈ ⋂ k, T.D k :=
          Set.mem_iInter.2 fun k => T.D_anti (by omega : k ≤ n + k) (hc k)
        rw [T.iInter_D] at this
        exact this
      classical
      have hm := Nat.find_spec hex
      obtain ⟨i, hi⟩ : ∃ i, Nat.find hex = i + 1 :=
        Nat.exists_eq_succ_of_ne_zero (by intro h0; rw [h0] at hm; exact hm hx)
      refine ⟨i, ?_, ?_⟩
      · by_contra hc
        exact Nat.find_min hex (by omega : i < Nat.find hex) hc
      · rw [hi] at hm
        exact hm
    · rintro ⟨i, hi, -⟩
      exact T.D_anti (by omega : n ≤ n + i) hi
  calc T.M K n = toClass (ofSet (Λ := τ.Λ) (K := K)
        (fun _ : Unit => ⋃ i, T.D (n + i) \ T.D (n + i + 1))
        (fun _ => MeasurableSet.iUnion fun i => hA i ())) := toClass_ofSet_congr hU _ _
    _ = _ := toClass_ofSet_iUnion (Λ := τ.Λ) (K := K)
        (fun i (_ : Unit) => T.D (n + i) \ T.D (n + i + 1)) hA hdisj
    _ = _ := SigmaMonoid.sum_congr' fun i => ((T.diffEq (n + i)).toClass_eq (K := K)
        (fun _ => T.measurable_D _) (fun _ => hA i ())).symm

end MarkerTower

end Collapse
