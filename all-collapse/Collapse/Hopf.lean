module

public import Collapse.Equidecomp
public import Collapse.System
public import Mathlib.Dynamics.Ergodic.Action.Basic

/-!
# Embedding of sets in an ergodic relation

A classical fact (E. Hopf): in an ergodic
measure-preserving action of a countable group, a set embeds piecewise in every set of at
least its measure, up to a null set. The null set is discarded by passing to an invariant set
of full measure.
-/

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory

namespace Collapse

section HopfAux

variable {Λ X : Type} [Group Λ] [MulAction Λ X]

/-- The exhaustion sequence of E. Hopf: the parts of `A` and `B` not yet matched. -/
def hopfSeq (e : ℕ → Λ) (A B : Set X) : ℕ → Set X × Set X
  | 0 => (A, B)
  | n + 1 => ((hopfSeq e A B n).1 \ {x | e n • x ∈ (hopfSeq e A B n).2},
      (hopfSeq e A B n).2 \ {y | (e n)⁻¹ • y ∈ (hopfSeq e A B n).1})

/-- The piece matched at step `n`. -/
def hopfPiece (e : ℕ → Λ) (A B : Set X) (n : ℕ) : Set X :=
  (hopfSeq e A B n).1 ∩ {x | e n • x ∈ (hopfSeq e A B n).2}

/-- The image of the piece matched at step `n`. -/
def hopfImage (e : ℕ → Λ) (A B : Set X) (n : ℕ) : Set X :=
  {y | (e n)⁻¹ • y ∈ hopfPiece e A B n}

variable (e : ℕ → Λ) (A B : Set X)

theorem antitone_hopfSeq_fst : Antitone fun n => (hopfSeq e A B n).1 :=
  antitone_nat_of_succ_le fun _ => Set.sdiff_subset

theorem antitone_hopfSeq_snd : Antitone fun n => (hopfSeq e A B n).2 :=
  antitone_nat_of_succ_le fun _ => Set.sdiff_subset

theorem hopfPiece_subset (n : ℕ) : hopfPiece e A B n ⊆ (hopfSeq e A B n).1 :=
  Set.inter_subset_left

theorem hopfPiece_not_mem (n : ℕ) : ∀ x ∈ hopfPiece e A B n, x ∉ (hopfSeq e A B (n + 1)).1 :=
  fun _ hx h' => h'.2 hx.2

theorem mem_hopfPiece (n : ℕ) {x : X} (h : x ∈ (hopfSeq e A B n).1)
    (h' : x ∉ (hopfSeq e A B (n + 1)).1) : x ∈ hopfPiece e A B n :=
  ⟨h, by_contra fun hc => h' ⟨h, hc⟩⟩

theorem hopfImage_subset (n : ℕ) : hopfImage e A B n ⊆ (hopfSeq e A B n).2 := by
  intro y hy
  have := hy.2
  simp only [Set.mem_ofPred_eq, smul_inv_smul] at this
  exact this

theorem hopfImage_not_mem (n : ℕ) : ∀ y ∈ hopfImage e A B n, y ∉ (hopfSeq e A B (n + 1)).2 :=
  fun _ hy h' => h'.2 hy.1

theorem mem_hopfImage (n : ℕ) {y : X} (h : y ∈ (hopfSeq e A B n).2)
    (h' : y ∉ (hopfSeq e A B (n + 1)).2) : y ∈ hopfImage e A B n := by
  have h1 : (e n)⁻¹ • y ∈ (hopfSeq e A B n).1 := by_contra fun hc => h' ⟨h, hc⟩
  refine ⟨h1, ?_⟩
  simp only [Set.mem_ofPred_eq, smul_inv_smul]
  exact h

theorem hopf_no_move {x : X} (hx : x ∈ ⋂ n, (hopfSeq e A B n).1) (n : ℕ)
    (hy : e n • x ∈ ⋂ n, (hopfSeq e A B n).2) : False :=
  (Set.mem_iInter.1 hx (n + 1)).2 (Set.mem_iInter.1 hy n)

theorem measurableSet_hopfSeq [MeasurableSpace X] (hmeas : ∀ g : Λ, Measurable fun x : X => g • x)
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    ∀ n, MeasurableSet (hopfSeq e A B n).1 ∧ MeasurableSet (hopfSeq e A B n).2
  | 0 => ⟨hA, hB⟩
  | n + 1 => by
    obtain ⟨h1, h2⟩ := measurableSet_hopfSeq hmeas hA hB n
    exact ⟨h1.diff (hmeas (e n) h2), h2.diff (hmeas (e n)⁻¹ h1)⟩

omit [Group Λ] [MulAction Λ X] in
theorem eq_of_mem_of_mem_aux {C D : ℕ → Set X} (hC : Antitone C) (hD : ∀ n, D n ⊆ C n)
    (hD' : ∀ n, ∀ x ∈ D n, x ∉ C (n + 1)) {m n : ℕ} {x : X} (hm : x ∈ D m) (hn : x ∈ D n) :
    m = n := by
  rcases lt_trichotomy m n with h | h | h
  · exact absurd (hC (Nat.succ_le_of_lt h) (hD n hn)) (hD' m x hm)
  · exact h
  · exact absurd (hC (Nat.succ_le_of_lt h) (hD m hm)) (hD' n x hn)

omit [Group Λ] [MulAction Λ X] in
theorem exists_mem_not_mem_aux {C : ℕ → Set X} {x : X} (h0 : x ∈ C 0) (h : x ∉ ⋂ n, C n) :
    ∃ n, x ∈ C n ∧ x ∉ C (n + 1) := by
  by_contra hc
  simp only [not_exists, not_and, not_not] at hc
  exact h (Set.mem_iInter.2 fun n => Nat.rec h0 (fun n ih => hc n ih) n)

end HopfAux

/-- If `Λ` acts ergodically and `μ A ≤ μ B`, then on an invariant set `U` of full measure the
set `A ∩ U` is equidecomposable with a measurable subset of `B ∩ U`. -/
theorem exists_equidecomp_of_ergodic {G : Type} [Group G] [Countable G] (S : PSystem G)
    [S.IsFree] (Λ : Subgroup G) [ErgodicSMul Λ S.X S.μ] (A B : Set S.X) (hA : MeasurableSet A)
    (hB : MeasurableSet B) (h : S.μ A ≤ S.μ B) :
    ∃ U : Set S.X, MeasurableSet U ∧ (∀ (g : G) (x : S.X), x ∈ U → g • x ∈ U) ∧ S.μ Uᶜ = 0 ∧
      ∃ B' : Set S.X, MeasurableSet B' ∧ B' ⊆ B ∩ U ∧
        Nonempty (Equidecomp Λ (fun _ : Unit => A ∩ U) (fun _ : Unit => B')) := by
  classical
  obtain ⟨e, he⟩ := exists_surjective_nat Λ
  have hmeas : ∀ g : Λ, Measurable fun x : S.X => g • x :=
    fun g => (S.preserving (g : G)).measurable
  have hpres : ∀ g : Λ, MeasurePreserving (fun x : S.X => g • x) S.μ S.μ :=
    fun g => S.preserving (g : G)
  have hm := measurableSet_hopfSeq e A B hmeas hA hB
  have hPm : ∀ n, MeasurableSet (hopfPiece e A B n) :=
    fun n => (hm n).1.inter (hmeas (e n) (hm n).2)
  have hQm : ∀ n, MeasurableSet (hopfImage e A B n) := fun n => hmeas (e n)⁻¹ (hPm n)
  set Ai := ⋂ n, (hopfSeq e A B n).1 with hAi
  set Bi := ⋂ n, (hopfSeq e A B n).2 with hBi
  have hAim : MeasurableSet Ai := MeasurableSet.iInter fun n => (hm n).1
  have hPdisj : Pairwise (Function.onFun Disjoint (hopfPiece e A B)) := fun m n hmn =>
    Set.disjoint_left.2 fun x hx hx' => hmn (eq_of_mem_of_mem_aux (antitone_hopfSeq_fst e A B)
      (hopfPiece_subset e A B) (hopfPiece_not_mem e A B) hx hx')
  have hQdisj : Pairwise (Function.onFun Disjoint (hopfImage e A B)) := fun m n hmn =>
    Set.disjoint_left.2 fun x hx hx' => hmn (eq_of_mem_of_mem_aux (antitone_hopfSeq_snd e A B)
      (hopfImage_subset e A B) (hopfImage_not_mem e A B) hx hx')
  have hQμ : ∀ n, S.μ (hopfImage e A B n) = S.μ (hopfPiece e A B n) :=
    fun n => (hpres (e n)⁻¹).measure_preimage (hPm n).nullMeasurableSet
  have hAi0 : S.μ Ai = 0 := by
    have key : S.μ Bi = 0 → S.μ Ai = 0 := by
      intro hB0
      have h1 : S.μ Ai + S.μ (⋃ n, hopfPiece e A B n) ≤ 0 + S.μ (⋃ n, hopfPiece e A B n) := by
        calc S.μ Ai + S.μ (⋃ n, hopfPiece e A B n) = S.μ (Ai ∪ ⋃ n, hopfPiece e A B n) := by
              refine (measure_union (Set.disjoint_left.2 fun x hx hx' => ?_)
                (MeasurableSet.iUnion hPm)).symm
              obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hx'
              exact hopfPiece_not_mem e A B n x hn (Set.mem_iInter.1 hx (n + 1))
          _ ≤ S.μ A := measure_mono (Set.union_subset (fun x hx => Set.mem_iInter.1 hx 0)
              (Set.iUnion_subset fun n => (hopfPiece_subset e A B n).trans
                (antitone_hopfSeq_fst e A B (Nat.zero_le n))))
          _ ≤ S.μ B := h
          _ ≤ S.μ (Bi ∪ ⋃ n, hopfImage e A B n) := measure_mono (fun y hy => by
              by_cases hy' : y ∈ Bi
              · exact Or.inl hy'
              · obtain ⟨n, h1, h2⟩ :=
                  exists_mem_not_mem_aux (C := fun n => (hopfSeq e A B n).2) hy hy'
                exact Or.inr (Set.mem_iUnion.2 ⟨n, mem_hopfImage e A B n h1 h2⟩))
          _ ≤ S.μ Bi + S.μ (⋃ n, hopfImage e A B n) := measure_union_le _ _
          _ = 0 + S.μ (⋃ n, hopfPiece e A B n) := by
              rw [hB0, measure_iUnion hQdisj hQm, measure_iUnion hPdisj hPm]
              simp_rw [hQμ]
      exact nonpos_iff_eq_zero.1 (ENNReal.le_of_add_le_add_right (measure_ne_top _ _) h1)
    let Sat : Set S.X := ⋃ g : Λ, (fun x => g • x) ⁻¹' Ai
    have hSatm : MeasurableSet Sat := MeasurableSet.iUnion fun g => hmeas g hAim
    have hSatinv : ∀ g : Λ, (fun x : S.X => g • x) ⁻¹' Sat =ᵐ[S.μ] Sat := by
      intro g
      have : (fun x : S.X => g • x) ⁻¹' Sat = Sat := by
        ext x
        simp only [Sat, Set.mem_preimage, Set.mem_iUnion]
        constructor
        · rintro ⟨k, hk⟩; exact ⟨k * g, by rwa [mul_smul]⟩
        · rintro ⟨k, hk⟩; exact ⟨k * g⁻¹, by rwa [mul_smul, inv_smul_smul]⟩
      exact Filter.EventuallyEq.of_eq this
    rcases Filter.eventuallyEmptyOrUniv_iff'.1
      (ErgodicSMul.aeconst_of_forall_preimage_smul_ae_eq hSatm hSatinv) with h0 | h0
    · refine measure_mono_null (fun x hx => Set.mem_iUnion.2 ⟨1, ?_⟩) (ae_eq_empty.1 h0)
      simp only [Set.mem_preimage, one_smul]; exact hx
    · refine key (measure_mono_null (show Bi ⊆ Satᶜ from fun y hy hy' => ?_) (ae_eq_univ.1 h0))
      obtain ⟨g, hg⟩ := Set.mem_iUnion.1 hy'
      obtain ⟨n, hn⟩ := he g⁻¹
      refine hopf_no_move e A B hg n ?_
      rw [hn, inv_smul_smul]; exact hy
  let U : Set S.X := {x | ∀ g : G, g • x ∉ Ai}
  have hUm : MeasurableSet U := by
    have : U = ⋂ g : G, ((fun x => g • x) ⁻¹' Ai)ᶜ := by ext; simp [U]
    rw [this]; exact MeasurableSet.iInter fun g => ((S.preserving g).measurable hAim).compl
  have hUinv : ∀ (g : G) (x : S.X), x ∈ U → g • x ∈ U := by
    intro g x hx
    show ∀ k : G, k • g • x ∉ Ai
    intro k
    rw [← mul_smul]; exact hx (k * g)
  have hUc : S.μ Uᶜ = 0 := by
    have : Uᶜ = ⋃ g : G, (fun x => g • x) ⁻¹' Ai := by ext; simp [U]
    rw [this]
    exact measure_iUnion_null fun g =>
      ((S.preserving g).measure_preimage hAim.nullMeasurableSet).trans hAi0
  have hUΛ : ∀ (g : Λ) (x : S.X), x ∈ U → g • x ∈ U := fun g x hx => hUinv (g : G) x hx
  refine ⟨U, hUm, hUinv, hUc, ⋃ n, (fun y => (e n)⁻¹ • y) ⁻¹' (hopfPiece e A B n ∩ U),
    MeasurableSet.iUnion fun n => hmeas _ ((hPm n).inter hUm), ?_, ⟨?_⟩⟩
  · intro y hy
    obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hy
    refine ⟨antitone_hopfSeq_snd e A B (Nat.zero_le n) (hopfImage_subset e A B n hn.1), ?_⟩
    have := hUΛ (e n) _ hn.2
    rwa [smul_inv_smul] at this
  · exact {
      piece := fun g _ _ => (⋃ n, ⋃ (_ : e n = g), hopfPiece e A B n) ∩ U
      measurable_piece := fun g _ _ =>
        (MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun _ => hPm n).inter hUm
      piece_subset := fun g _ _ x hx => by
        obtain ⟨n, -, hn⟩ := Set.mem_iUnion₂.1 hx.1
        exact ⟨antitone_hopfSeq_fst e A B (Nat.zero_le n) (hopfPiece_subset e A B n hn), hx.2⟩
      existsUnique_piece := fun _ x hx => by
        have hx' : x ∉ Ai := by have := hx.2 1; rwa [one_smul] at this
        obtain ⟨n, h1, h2⟩ :=
          exists_mem_not_mem_aux (C := fun n => (hopfSeq e A B n).1) hx.1 hx'
        refine ⟨(e n, ()), ⟨Set.mem_iUnion₂.2 ⟨n, rfl, mem_hopfPiece e A B n h1 h2⟩, hx.2⟩, ?_⟩
        rintro ⟨g, ⟨⟩⟩ ⟨hg, -⟩
        obtain ⟨m, rfl, hm⟩ := Set.mem_iUnion₂.1 hg
        rw [eq_of_mem_of_mem_aux (antitone_hopfSeq_fst e A B) (hopfPiece_subset e A B)
          (hopfPiece_not_mem e A B) hm (mem_hopfPiece e A B n h1 h2)]
      mapsTo := fun g _ _ x hx => by
        obtain ⟨n, rfl, hn⟩ := Set.mem_iUnion₂.1 hx.1
        refine Set.mem_iUnion.2 ⟨n, ?_⟩
        simp only [Set.mem_preimage, inv_smul_smul]
        exact ⟨hn, hx.2⟩
      existsUnique_source := fun _ y hy => by
        obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hy
        refine ⟨(e n, ()), ⟨Set.mem_iUnion₂.2 ⟨n, rfl, hn.1⟩, hn.2⟩, ?_⟩
        rintro ⟨g, ⟨⟩⟩ ⟨hg, -⟩
        obtain ⟨m, rfl, hm⟩ := Set.mem_iUnion₂.1 hg
        rw [eq_of_mem_of_mem_aux (antitone_hopfSeq_snd e A B) (hopfImage_subset e A B)
          (hopfImage_not_mem e A B) (x := y) hm hn.1] }

end Collapse
