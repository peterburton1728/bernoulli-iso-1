module

public import BernoulliIso.Marker
public import Mathlib.Order.PiLex
public import Mathlib.Data.Fintype.Lattice

/-!
Finite blocks ordered by the lexicographic order of actual iid digit streams.
Uniform selection is obtained from exchangeability and the proved null-tie
bound; no uniform real-valued priority is assumed.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace BernoulliIso
namespace FiniteOrdering

variable {K I : Type*} [Fintype K] [Nonempty K]
  [MeasurableSpace K] [MeasurableSingletonClass K] [LinearOrder K]
  [Fintype I]

def Winner (x : I → ℕ → K) (i : I) : Prop :=
  ∀ j, j ≠ i → toLex (x i) < toLex (x j)

def winnerSet (i : I) : Set (I → ℕ → K) := {x | Winner x i}

omit [Nonempty K] in
/-- Lexicographic comparison is a countable union of finite digit tests. -/
theorem measurable_lex_comparison {Ω : Type*} [MeasurableSpace Ω]
    (x y : Ω → ℕ → K) (hx : Measurable x) (hy : Measurable y) :
    MeasurableSet {ω | toLex (x ω) < toLex (y ω)} := by
  have heq : {ω | toLex (x ω) < toLex (y ω)} =
      ⋃ n : ℕ, ({ω | ∀ j, j < n → x ω j = y ω j} ∩ {ω | x ω n < y ω n}) := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
    rfl
  rw [heq]
  apply MeasurableSet.iUnion
  intro n
  apply MeasurableSet.inter
  · have heq' : {ω | ∀ j, j < n → x ω j = y ω j} =
        ⋂ j : ℕ, ⋂ (_ : j < n), {ω | x ω j = y ω j} := by
      ext ω
      simp
    rw [heq']
    exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
      measurableSet_eq_fun ((measurable_pi_apply j).comp hx) ((measurable_pi_apply j).comp hy)
  · exact (Set.to_countable {p : K × K | p.1 < p.2}).measurableSet.preimage
      (((measurable_pi_apply n).comp hx).prodMk ((measurable_pi_apply n).comp hy))

omit [Nonempty K] in
theorem measurable_winnerSet (i : I) : MeasurableSet (winnerSet (K := K) i) := by
  have heq : winnerSet (K := K) i =
      ⋂ j : I, ⋂ (_ : j ≠ i), {x | toLex (x i) < toLex (x j)} := by
    ext x
    simp [winnerSet, Winner]
  rw [heq]
  exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
    measurable_lex_comparison _ _ (measurable_pi_apply i) (measurable_pi_apply j)

omit [Fintype K] [Nonempty K] [MeasurableSpace K] [MeasurableSingletonClass K] [Fintype I] in
theorem winner_disjoint : Pairwise (fun i j : I =>
    Disjoint (winnerSet (K := K) i) (winnerSet j)) := by
  intro i j hij
  apply Set.disjoint_left.2
  intro x hi hj
  exact lt_asymm (hi j hij.symm) (hj i hij)

omit [Fintype K] [Nonempty K] [MeasurableSpace K] [MeasurableSingletonClass K] in
theorem exists_winner_of_injective [Nonempty I] {x : I → ℕ → K}
    (hx : Function.Injective x) : ∃ i, Winner x i := by
  obtain ⟨i, hi⟩ := Finite.exists_min (fun j => toLex (x j))
  refine ⟨i, fun j hji => ?_⟩
  apply lt_of_le_of_ne (hi j)
  intro h
  exact hji (hx (toLex_inj.1 h)).symm

omit [Fintype K] [Nonempty K] [MeasurableSpace K] [MeasurableSingletonClass K] [Fintype I] in
theorem winner_precomp (e : Equiv.Perm I) (x : I → ℕ → K) (i : I) :
    Winner (fun j => x (e j)) i ↔ Winner x (e i) := by
  constructor
  · intro h j hji
    obtain ⟨k, rfl⟩ := e.surjective j
    exact h k (fun heq => hji (congrArg e heq))
  · intro h j hji
    exact h (e j) (fun heq => hji (e.injective heq))

noncomputable def law : Measure (I → ℕ → K) :=
  Measure.infinitePi (fun _ : I => MarkerGeometry.streamLaw (K := K))

instance law_probability : IsProbabilityMeasure (law (I := I) (K := K)) := by
  unfold law
  infer_instance

omit [LinearOrder K] [Fintype I] in
/-- The iid stream field is invariant under arbitrary site permutations. -/
theorem permutation_law (e : Equiv.Perm I) :
    (law (I := I) (K := K)).map (fun x i => x (e i)) = law := by
  exact Measure.map_infinitePi_infinitePi_of_inj e.injective

theorem winner_equiprobable (i j : I) :
    law (K := K) (winnerSet i) = law (K := K) (winnerSet j) := by
  classical
  let e := Equiv.swap i j
  have heq : (fun x k => x (e k)) ⁻¹' winnerSet (K := K) i = winnerSet j := by
    ext x
    change Winner (fun k => x (e k)) i ↔ Winner x j
    rw [winner_precomp]
    simp [e]
  calc
    law (K := K) (winnerSet i) =
        ((law (K := K)).map (fun x k => x (e k))) (winnerSet i) := by
      rw [permutation_law]
    _ = law (K := K) ((fun x k => x (e k)) ⁻¹' winnerSet i) :=
      Measure.map_apply (by fun_prop) (measurable_winnerSet i)
    _ = law (K := K) (winnerSet j) := by rw [heq]

/-- The finite block has a unique smallest digit sequence almost surely. -/
theorem ae_exists_winner [Nonempty I] [Nontrivial K] :
    ∀ᵐ x ∂law (I := I) (K := K), ∃ i, Winner x i := by
  have h : ∀ i j : I, ∀ᵐ x ∂law (I := I) (K := K), i ≠ j → x i ≠ x j := by
    intro i j
    by_cases hij : i = j
    · simp [hij]
    · have hz := MarkerGeometry.independent_streams_tie_zero (K := K) hij
      have ha := (measure_eq_zero_iff_ae_notMem).1 hz
      filter_upwards [ha] with x hx
      exact fun _ => hx
  have hall : ∀ᵐ x ∂law (I := I) (K := K), ∀ i j : I, i ≠ j → x i ≠ x j :=
    ae_all_iff.2 fun i => ae_all_iff.2 fun j => h i j
  filter_upwards [hall] with x hx
  apply exists_winner_of_injective
  intro i j hij
  by_contra hne
  exact hx i j hne hij

/-- Exact reciprocal block-size probability for the concrete lexicographic minimum. -/
theorem winner_probability [Nonempty I] [Nontrivial K] (i : I) :
    law (K := K) (winnerSet i) = (Fintype.card I : ℝ≥0∞)⁻¹ := by
  have hfull : law (K := K) (⋃ j : I, winnerSet j) = 1 := by
    apply (mem_ae_iff_prob_eq_one (MeasurableSet.iUnion measurable_winnerSet)).1
    filter_upwards [ae_exists_winner (I := I) (K := K)] with x hx
    exact Set.mem_iUnion.2 hx
  have hsum := measure_iUnion (μ := law (I := I) (K := K))
    (winner_disjoint (I := I) (K := K)) (measurable_winnerSet (I := I) (K := K))
  rw [hfull, tsum_fintype] at hsum
  have heqsum : ∑ j : I, law (K := K) (winnerSet j) =
      (Fintype.card I : ℝ≥0∞) * law (K := K) (winnerSet i) := by
    calc
      ∑ j : I, law (K := K) (winnerSet j) =
          ∑ _j : I, law (K := K) (winnerSet i) := by
        exact Finset.sum_congr rfl (fun j _ => winner_equiprobable j i)
      _ = _ := by simp
  rw [heqsum] at hsum
  have hn : (Fintype.card I : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card I ≠ 0)
  have heq : law (K := K) (winnerSet i) = 1 / (Fintype.card I : ℝ≥0∞) :=
    (ENNReal.eq_div_iff hn (by simp)).2 hsum.symm
  simpa only [one_div] using heq

/-- A packet is selected when its minimum is the minimum of the whole
block. Packets all have the same finite size. -/
def packetSet {J : Type*} (i : I) : Set ((I × J) → ℕ → K) :=
  ⋃ j : J, winnerSet (i, j)

omit [Nonempty K] in
theorem measurable_packetSet {J : Type*} [Fintype J] (i : I) :
    MeasurableSet (packetSet (K := K) (J := J) i) :=
  MeasurableSet.iUnion fun _ => measurable_winnerSet _

/-- The probability of selecting a packet is at most the reciprocal of
the number of packets, independently of their common finite size. -/
theorem packet_probability_le {J : Type*} [Fintype J] [Nonempty J]
    [Nonempty I] [Nontrivial K] (i : I) :
    law (K := K) (packetSet (J := J) i) ≤ (Fintype.card I : ℝ≥0∞)⁻¹ := by
  have hI : (Fintype.card I : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card I ≠ 0)
  have hIJ : (Fintype.card (I × J) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (I × J) ≠ 0)
  have hratio : (Fintype.card J : ℝ≥0∞) *
      (Fintype.card (I × J) : ℝ≥0∞)⁻¹ = (Fintype.card I : ℝ≥0∞)⁻¹ := by
    have heq : (Fintype.card J : ℝ≥0∞) * (Fintype.card (I × J) : ℝ≥0∞)⁻¹ =
        1 / (Fintype.card I : ℝ≥0∞) := by
      apply (ENNReal.eq_div_iff hI (by simp)).2
      rw [← mul_assoc, ← Nat.cast_mul, ← Fintype.card_prod]
      exact ENNReal.mul_inv_cancel hIJ (ENNReal.natCast_ne_top _)
    simpa only [one_div] using heq
  calc
    law (K := K) (packetSet (J := J) i) ≤ ∑ j : J, law (K := K) (winnerSet (i, j)) :=
      measure_iUnion_fintype_le _ _
    _ = (Fintype.card J : ℝ≥0∞) * (Fintype.card (I × J) : ℝ≥0∞)⁻¹ := by
      simp [winner_probability]
    _ = (Fintype.card I : ℝ≥0∞)⁻¹ := hratio

/-- The number of streams strictly preceding a given stream. -/
noncomputable def rankNat (x : I → ℕ → K) (i : I) : ℕ := by
  classical
  exact (Finset.univ.filter fun j => toLex (x j) < toLex (x i)).card

omit [Fintype K] [Nonempty K] [MeasurableSpace K] [MeasurableSingletonClass K] in
theorem rankNat_lt_card (x : I → ℕ → K) (i : I) :
    rankNat x i < Fintype.card I := by
  classical
  unfold rankNat
  change _ < Finset.univ.card
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.2
  refine ⟨Finset.filter_subset _ _, ?_⟩
  intro h
  have hi : i ∈ Finset.univ.filter fun j => toLex (x j) < toLex (x i) := by
    rw [h]
    exact Finset.mem_univ i
  exact (lt_irrefl _) (Finset.mem_filter.1 hi).2

omit [Fintype K] [Nonempty K] [MeasurableSpace K] [MeasurableSingletonClass K] in
theorem rankNat_lt_of_lt (x : I → ℕ → K) {i j : I}
    (hij : toLex (x i) < toLex (x j)) : rankNat x i < rankNat x j := by
  classical
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.2
  refine ⟨?_, ?_⟩
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    exact lt_trans hk hij
  · intro h
    have hi : i ∈ Finset.univ.filter fun k => toLex (x k) < toLex (x j) := by
      simp [hij]
    rw [← h] at hi
    exact (lt_irrefl _) (Finset.mem_filter.1 hi).2

omit [Fintype K] [Nonempty K] [MeasurableSpace K] [MeasurableSingletonClass K] in
theorem rankNat_injective {x : I → ℕ → K} (hx : Function.Injective x) :
    Function.Injective (rankNat x) := by
  intro i j h
  have hxij : toLex (x i) = toLex (x j) := by
    apply le_antisymm
    · by_contra hn
      exact (ne_of_lt (rankNat_lt_of_lt x (lt_of_not_ge hn))) h.symm
    · by_contra hn
      exact (ne_of_lt (rankNat_lt_of_lt x (lt_of_not_ge hn))) h
  exact hx (toLex_inj.1 hxij)

omit [Fintype K] [Nonempty K] [MeasurableSpace K] [MeasurableSingletonClass K] in
/-- Rank is natural under every equivalence of the underlying site types. -/
theorem rankNat_precomp {J : Type*} [Fintype J]
    (e : I ≃ J) (x : J → ℕ → K) (i : I) :
    rankNat (fun j => x (e j)) i = rankNat x (e i) := by
  classical
  unfold rankNat
  apply Finset.card_bijective e e.bijective
  intro j
  simp

/-- A genuine enumeration by ranks on every tie-free finite block. -/
noncomputable def rankEquiv (x : I → ℕ → K) (hx : Function.Injective x) :
    I ≃ Fin (Fintype.card I) :=
  Equiv.ofBijective (fun i => ⟨rankNat x i, rankNat_lt_card x i⟩)
    ((Fintype.bijective_iff_injective_and_card _).2
      ⟨fun i j h => rankNat_injective hx (congrArg Fin.val h), by simp⟩)

omit [Fintype K] [Nonempty K] [MeasurableSpace K] [MeasurableSingletonClass K] in
theorem rankEquiv_precomp (e : Equiv.Perm I) (x : I → ℕ → K)
    (hx : Function.Injective x) (i : I) :
    rankEquiv (fun j => x (e j)) (hx.comp e.injective) i = rankEquiv x hx (e i) := by
  apply Fin.ext
  exact rankNat_precomp e x i

omit [Fintype K] [Nonempty K] [MeasurableSpace K] [MeasurableSingletonClass K] in
theorem rankEquiv_symm_precomp (e : Equiv.Perm I) (x : I → ℕ → K)
    (hx : Function.Injective x) (k : Fin (Fintype.card I)) :
    e ((rankEquiv (fun j => x (e j)) (hx.comp e.injective)).symm k) =
      (rankEquiv x hx).symm k := by
  apply (rankEquiv x hx).injective
  rw [← rankEquiv_precomp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- Rank enumeration with the common fiber cardinality made explicit. -/
noncomputable def rankEquivOfCard (x : I → ℕ → K) (hx : Function.Injective x)
    {κ : ℕ} (hcard : Fintype.card I = κ) : I ≃ Fin κ :=
  (rankEquiv x hx).trans (finCongr hcard)

omit [Fintype K] [Nonempty K] [MeasurableSpace K] [MeasurableSingletonClass K] in
/-- Fiber types may differ: a common cardinality gives covariance without
any casts in the resulting coordinate labels. -/
theorem rankEquivOfCard_precomp {J : Type*} [Fintype J]
    (e : I ≃ J) (x : J → ℕ → K) (hx : Function.Injective x)
    {κ : ℕ} (hI : Fintype.card I = κ) (hJ : Fintype.card J = κ) (i : I) :
    rankEquivOfCard (fun j => x (e j)) (hx.comp e.injective) hI i =
      rankEquivOfCard x hx hJ (e i) := by
  apply Fin.ext
  exact rankNat_precomp e x i

omit [Fintype K] [Nonempty K] [MeasurableSpace K] [MeasurableSingletonClass K] in
theorem rankEquivOfCard_symm_precomp {J : Type*} [Fintype J]
    (e : I ≃ J) (x : J → ℕ → K) (hx : Function.Injective x)
    {κ : ℕ} (hI : Fintype.card I = κ) (hJ : Fintype.card J = κ) (k : Fin κ) :
    e ((rankEquivOfCard (fun j => x (e j)) (hx.comp e.injective) hI).symm k) =
      (rankEquivOfCard x hx hJ).symm k := by
  apply (rankEquivOfCard x hx hJ).injective
  rw [← rankEquivOfCard_precomp e x hx hI hJ,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply]

omit [Nonempty K] in
/-- Ranks are measurable even before restricting to the tie-free domain. -/
theorem measurable_rankNat (i : I) : Measurable (fun x : I → ℕ → K => rankNat x i) := by
  classical
  have heq : (fun x : I → ℕ → K => rankNat x i) =
      (fun x => ∑ j : I, if toLex (x j) < toLex (x i) then (1 : ℕ) else 0) := by
    funext x
    exact Finset.card_filter _ _
  rw [heq]
  apply Finset.measurable_sum
  intro j _
  exact Measurable.ite
    (measurable_lex_comparison _ _ (measurable_pi_apply j) (measurable_pi_apply i))
    measurable_const measurable_const

/-- The smallest stream value in a nonempty finite packet. The value does
not depend on how a minimizing site is chosen, even on ties. -/
noncomputable def minimumStream [Nonempty I] (x : I → ℕ → K) : ℕ → K :=
  x (Classical.choose (Finite.exists_min (fun i => toLex (x i))))

omit [Fintype K] [Nonempty K] [MeasurableSpace K] [MeasurableSingletonClass K] in
theorem minimumStream_mem [Nonempty I] (x : I → ℕ → K) :
    ∃ i, minimumStream x = x i :=
  ⟨Classical.choose (Finite.exists_min (fun i => toLex (x i))), rfl⟩

omit [Fintype K] [Nonempty K] [MeasurableSpace K] [MeasurableSingletonClass K] in
theorem minimumStream_le [Nonempty I] (x : I → ℕ → K) (i : I) :
    toLex (minimumStream x) ≤ toLex (x i) :=
  Classical.choose_spec (Finite.exists_min (fun j => toLex (x j))) i

omit [Fintype K] [Nonempty K] [MeasurableSpace K] [MeasurableSingletonClass K] in
theorem minimumStream_eq_iff [Nonempty I] (x : I → ℕ → K) (i : I) :
    minimumStream x = x i ↔ ∀ j, toLex (x i) ≤ toLex (x j) := by
  constructor
  · intro h j
    rw [← h]
    exact minimumStream_le x j
  · intro h
    apply toLex_inj.1
    apply le_antisymm (minimumStream_le x i)
    obtain ⟨j, hj⟩ := minimumStream_mem x
    rw [hj]
    exact h j

omit [Fintype K] [Nonempty K] [MeasurableSpace K] [MeasurableSingletonClass K] in
theorem minimumStream_precomp {J : Type*} [Fintype J] [Nonempty I] [Nonempty J]
    (e : I ≃ J) (x : J → ℕ → K) :
    minimumStream (fun i => x (e i)) = minimumStream x := by
  apply toLex_inj.1
  apply le_antisymm
  · obtain ⟨j, hj⟩ := minimumStream_mem x
    obtain ⟨i, rfl⟩ := e.surjective j
    rw [hj]
    exact minimumStream_le (fun i => x (e i)) i
  · obtain ⟨i, hi⟩ := minimumStream_mem (fun i => x (e i))
    rw [hi]
    exact minimumStream_le x (e i)

omit [Nonempty K] in
/-- Measurability uses the finite union of measurable minimizing-site
events; it does not assume a measurable arbitrary choice operation. -/
theorem measurable_minimumStream [Nonempty I] :
    Measurable (minimumStream (I := I) (K := K)) := by
  intro S hS
  have heq : minimumStream (I := I) (K := K) ⁻¹' S =
      ⋃ i : I, ({x | ∀ j, toLex (x i) ≤ toLex (x j)} ∩ {x | x i ∈ S}) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · intro h
      obtain ⟨i, hi⟩ := minimumStream_mem x
      exact ⟨i, (minimumStream_eq_iff x i).1 hi, hi ▸ h⟩
    · rintro ⟨i, hi, hS⟩
      rwa [(minimumStream_eq_iff x i).2 hi]
  rw [heq]
  apply MeasurableSet.iUnion
  intro i
  apply MeasurableSet.inter
  · have heq' : {x : I → ℕ → K | ∀ j, toLex (x i) ≤ toLex (x j)} =
        ⋂ j : I, {x | ¬ toLex (x j) < toLex (x i)} := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_iInter]
      constructor
      · intro h j
        exact not_lt_of_ge (h j)
      · intro h j
        exact le_of_not_gt (h j)
    rw [heq']
    exact MeasurableSet.iInter fun j =>
      (measurable_lex_comparison _ _ (measurable_pi_apply j) (measurable_pi_apply i)).compl
  · exact hS.preimage (measurable_pi_apply i)

/-- Packet priorities represented as their actual minimum digit streams.
The packet types may vary with the packet index. -/
noncomputable def packetMinima {J : I → Type*}
    [∀ i, Fintype (J i)] [∀ i, Nonempty (J i)]
    (x : ∀ i, J i → ℕ → K) (i : I) : ℕ → K := minimumStream (x i)

omit [Nonempty K] [Fintype I] in
theorem measurable_packetMinima {J : I → Type*}
    [∀ i, Fintype (J i)] [∀ i, Nonempty (J i)] :
    Measurable (packetMinima (K := K) (J := J)) :=
  Measurable.of_eval fun i => measurable_minimumStream.comp (measurable_pi_apply i)

omit [Fintype K] [Nonempty K] [MeasurableSpace K] [MeasurableSingletonClass K] [Fintype I] in
/-- Disjoint packets of globally distinct streams have distinct minima. -/
theorem packetMinima_injective {J : I → Type*}
    [∀ i, Fintype (J i)] [∀ i, Nonempty (J i)]
    (x : ∀ i, J i → ℕ → K)
    (hx : Function.Injective (fun p : Σ i, J i => x p.1 p.2)) :
    Function.Injective (packetMinima x) := by
  intro i j hij
  obtain ⟨u, hu⟩ := minimumStream_mem (x i)
  obtain ⟨v, hv⟩ := minimumStream_mem (x j)
  have h : x i u = x j v := hu.symm.trans (hij.trans hv)
  exact congrArg Sigma.fst (@hx ⟨i, u⟩ ⟨j, v⟩ h)

omit [Fintype K] [Nonempty K] [MeasurableSpace K] [MeasurableSingletonClass K] [Fintype I] in
theorem packetMinima_precomp {I' : Type*}
    {J : I → Type*} {J' : I' → Type*}
    [∀ i, Fintype (J i)] [∀ i, Nonempty (J i)]
    [∀ i, Fintype (J' i)] [∀ i, Nonempty (J' i)]
    (e : I ≃ I') (f : ∀ i, J i ≃ J' (e i)) (x : ∀ i, J' i → ℕ → K) (i : I) :
    packetMinima (fun j u => x (e j) (f j u)) i = packetMinima x (e i) :=
  minimumStream_precomp (f i) (x (e i))

end FiniteOrdering

namespace MarkerGeometry

variable {G K I J A : Type*} [Group G] (a : MarkerGeometry G)
  [Fintype K] [Nonempty K] [Nontrivial K]
  [MeasurableSpace K] [MeasurableSingletonClass K] [LinearOrder K]
  [Fintype I] [Nonempty I] [Fintype J] [Nonempty J]

omit [Fintype K] [Nonempty K] [Nontrivial K] [MeasurableSpace K]
  [MeasurableSingletonClass K] [LinearOrder K] [Fintype I] [Nonempty I] in
/-- The global good-marker domain gives injective streams on every block
of distinct D-sites. -/
theorem blockDigits_injective_of_goodMarker (g : G) (r : ℕ) (sites : I ↪ a.D)
    {ω : G → K} (hω : ω ∈ a.goodMarker) :
    Function.Injective (a.blockDigits g r sites ω) := by
  intro i j hij
  by_contra hne
  apply hω g r (sites i) (sites j) (fun h => hne (sites.injective h))
  exact hij

/-- The selected-packet event for the actual finite-alphabet marker. -/
def packetSelected (g : G) (r : ℕ) (sites : (I × J) ↪ a.D) (i : I) : Set (G → K) :=
  a.blockDigits g r sites ⁻¹' FiniteOrdering.packetSet i

omit [Fintype K] [Nonempty K] [Nontrivial K] [MeasurableSpace K]
  [MeasurableSingletonClass K] [Fintype I] [Nonempty I] [Fintype J] [Nonempty J] in
/-- Translating the coset and shifting the marker preserves the chosen packet. -/
theorem packetSelected_covariant (b g : G) (r : ℕ) (sites : (I × J) ↪ a.D)
    (i : I) (ω : G → K) :
    markerShift b ω ∈ a.packetSelected (b * g) r sites i ↔
      ω ∈ a.packetSelected g r sites i := by
  change a.blockDigits (b * g) r sites (markerShift b ω) ∈
      FiniteOrdering.packetSet i ↔ a.blockDigits g r sites ω ∈ FiniteOrdering.packetSet i
  rw [a.blockDigits_covariant]

omit [Nontrivial K] [Nonempty I] [Nonempty J] in
/-- Selection depends only on the current digit stream. -/
theorem packetSelected_fresh (g : G) (r : ℕ) (sites : (I × J) ↪ a.D) (i : I) :
    MeasurableSet[a.freshSigma g r] (a.packetSelected (K := K) g r sites i) := by
  let f : (a.freshIndices r → K) → (I × J) → ℕ → K := fun η z n =>
    η ⟨(sites z, (r, n)), rfl⟩
  have hf : Measurable f := Measurable.of_eval fun z => Measurable.of_eval fun n =>
    measurable_pi_apply (⟨(sites z, (r, n)), rfl⟩ : a.freshIndices r)
  apply MeasurableSpace.measurableSet_comap.2
  refine ⟨f ⁻¹' FiniteOrdering.packetSet i, (FiniteOrdering.measurable_packetSet i).preimage hf, ?_⟩
  rfl

/-- Unconditional uniform packet bound derived from actual iid marker digits. -/
theorem packetSelected_probability_le (g : G) (r : ℕ)
    (sites : (I × J) ↪ a.D) (i : I) :
    markerLaw (G := G) K (a.packetSelected g r sites i) ≤
      (Fintype.card I : ℝ≥0∞)⁻¹ := by
  rw [packetSelected, ← Measure.map_apply (a.measurable_blockDigits g r sites)
    (FiniteOrdering.measurable_packetSet i), a.blockDigits_joint_law]
  exact FiniteOrdering.packet_probability_le i

/-- The former `hfresh` premise, now supplied by the concrete finite
uniform marker and lexicographic packet selection. The support may depend
arbitrarily on all earlier streams in this D-coset. -/
theorem support_fiber_packet_bound (g : G) (r : ℕ)
    (support : (G → K) → Finset A) (s : Finset A)
    (hs : MeasurableSet[a.pastSigma g r] {ω | support ω = s})
    (sites : (I × J) ↪ a.D) (i : I) :
    markerLaw (G := G) K ({ω | support ω = s} ∩ a.packetSelected g r sites i) ≤
      (Fintype.card I : ℝ≥0∞)⁻¹ * markerLaw (G := G) K {ω | support ω = s} := by
  rw [a.support_fiber_fresh g r support s hs (a.packetSelected_fresh g r sites i)]
  exact mul_le_mul' (a.packetSelected_probability_le g r sites i) le_rfl

end MarkerGeometry
end BernoulliIso
