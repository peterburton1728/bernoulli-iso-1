module

public import BernoulliIso.CosetCoordinates
public import BernoulliIso.Regroup

/-!
Identification of the actual zero-rank coset selected by regrouping with
the finite equal-packet minimum event used by the selection estimates.
-/

@[expose] public section
noncomputable section
open scoped Classical

namespace BernoulliIso
namespace FiniteOrdering

variable {I J K : Type*} [Fintype I] [Fintype J] [Nonempty J] [LinearOrder K]

/-- Rank zero is precisely the minimum-stream condition. -/
theorem rankNat_eq_zero_iff (x : I → ℕ → K) (i : I) :
    rankNat x i = 0 ↔ ∀ j, toLex (x i) ≤ toLex (x j) := by
  simp only [rankNat, Finset.card_eq_zero, Finset.filter_eq_empty_iff, Finset.mem_univ,
    true_implies]
  constructor
  · intro h j
    exact le_of_not_gt (@h j)
  · intro h j
    exact not_lt_of_ge (h j)

/-- The packet with minimum priority contains the unique minimum site. -/
theorem packetMinima_rank_zero_iff (x : (I × J) → ℕ → K)
    (hx : Function.Injective x) (i : I) :
    rankNat (packetMinima (fun i j => x (i, j))) i = 0 ↔ x ∈ packetSet i := by
  rw [rankNat_eq_zero_iff]
  simp only [packetSet, Set.mem_iUnion, winnerSet, Set.mem_ofPred_eq]
  change (∀ k, toLex (minimumStream (fun j => x (i, j))) ≤
      toLex (minimumStream (fun j => x (k, j)))) ↔ ∃ j, Winner x (i, j)
  constructor
  · intro hm
    obtain ⟨j, hj⟩ := minimumStream_mem (fun j => x (i, j))
    refine ⟨j, ?_⟩
    intro p hp
    have hle := (hm p.1).trans (minimumStream_le (fun j => x (p.1, j)) p.2)
    rw [hj] at hle
    apply lt_of_le_of_ne hle
    intro heq
    exact hp (hx (toLex_inj.1 heq)).symm
  · rintro ⟨j, hj⟩ k
    obtain ⟨l, hl⟩ := minimumStream_mem (fun l => x (k, l))
    rw [hl]
    apply (minimumStream_le (fun l => x (i, l)) j).trans
    by_cases h : (k, l) = (i, j)
    · simpa only [h] using (le_rfl : toLex (x (i, j)) ≤ toLex (x (i, j)))
    · exact le_of_lt (hj (k, l) h)


/-- The winner event is natural under arbitrary equivalences of site types. -/
theorem winner_precomp_equiv {I' : Type*} (e : I ≃ I') (x : I' → ℕ → K) (i : I) :
    Winner (fun j => x (e j)) i ↔ Winner x (e i) := by
  constructor
  · intro h j hji
    obtain ⟨k, rfl⟩ := e.surjective j
    exact h k (fun hk => hji (congrArg e hk))
  · intro h j hji
    exact h (e j) (fun hj => hji (e.injective hj))

/-- Constant relabelling of packets and sites does not change selection. -/
theorem packetSet_precomp {I' J' : Type*} (e : I ≃ I') (f : J ≃ J')
    (x : (I' × J') → ℕ → K) (i : I) :
    (fun p : I × J => x (e p.1, f p.2)) ∈ packetSet i ↔ x ∈ packetSet (e i) := by
  simp only [packetSet, Set.mem_iUnion, winnerSet, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨j, hj⟩
    exact ⟨f j, (winner_precomp_equiv (e.prodCongr f) x (i, j)).1 hj⟩
  · rintro ⟨j, hj⟩
    obtain ⟨k, rfl⟩ := f.surjective j
    exact ⟨k, (winner_precomp_equiv (e.prodCongr f) x (i, k)).2 hj⟩

end FiniteOrdering
namespace CosetCoordinates

instance quotientFiber_nonempty {G : Type*} [Group G] {H L : Subgroup G}
    (hHL : H ≤ L) (c : G ⧸ L) : Nonempty (Fiber (Subgroup.quotientMapOfLE hHL) c) :=
  ⟨(quotientFiberEquiv hHL c).symm (QuotientGroup.mk 1)⟩

noncomputable instance quotientFiber_fintype {G : Type*} [Group G] {H L : Subgroup G}
    [Finite L] (hHL : H ≤ L) (c : G ⧸ L) :
    Fintype (Fiber (Subgroup.quotientMapOfLE hHL) c) := Fintype.ofFinite _

section Packets

variable {G K : Type*} [Group G] (a : MarkerGeometry G)
  (H L : Subgroup G) (hHL : H ≤ L) (hLD : L ≤ a.D)

/-- Actual sites, with each H-coset packet parametrized by H. The arbitrary
packet parametrization is used only to identify its iid law. -/
def packetLocation (g : G)
    (p : Fiber (Subgroup.quotientMapOfLE hHL) (QuotientGroup.mk g) × H) : G :=
  ((siteFiberEquiv H p.1.val).symm p.2).val

theorem packetLocation_quotient (g : G)
    (p : Fiber (Subgroup.quotientMapOfLE hHL) (QuotientGroup.mk g) × H) :
    (QuotientGroup.mk (packetLocation H L hHL g p) : G ⧸ L) = QuotientGroup.mk g := by
  have h := congrArg (Subgroup.quotientMapOfLE hHL)
    ((siteFiberEquiv H p.1.val).symm p.2).property
  exact h.trans p.1.property

theorem packetLocation_injective (g : G) : Function.Injective (packetLocation H L hHL g) := by
  rintro ⟨z, h⟩ ⟨w, k⟩ hsite
  have hzw : z = w := by
    apply Subtype.ext
    exact ((siteFiberEquiv H z.val).symm h).property.symm.trans
      ((congrArg QuotientGroup.mk hsite).trans ((siteFiberEquiv H w.val).symm k).property)
  subst w
  apply Prod.ext
  · rfl
  apply (siteFiberEquiv H z.val).symm.injective
  exact Subtype.ext hsite

/-- These equal-size packets lie inside one actual D-coset. -/
def packetSites (g : G) :
    (Fiber (Subgroup.quotientMapOfLE hHL) (QuotientGroup.mk g) × H) ↪ a.D where
  toFun p := ⟨g⁻¹ * packetLocation H L hHL g p,
    hLD (QuotientGroup.eq.mp (packetLocation_quotient H L hHL g p).symm)⟩
  inj' := by
    intro p q hpq
    apply packetLocation_injective H L hHL g
    exact mul_left_cancel (congrArg Subtype.val hpq)

theorem blockDigits_packetSites [Fintype K] [Nonempty K]
    [MeasurableSpace K] [MeasurableSingletonClass K] [LinearOrder K]
    (g : G) (r : ℕ) (ω : G → K)
    (p : Fiber (Subgroup.quotientMapOfLE hHL) (QuotientGroup.mk g) × H) :
    a.blockDigits g r (packetSites a H L hHL hLD g) ω p =
      siteStream a r ω (packetLocation H L hHL g p) := by
  funext n
  simp [MarkerGeometry.blockDigits, MarkerGeometry.digits, MarkerGeometry.address,
    packetSites, siteStream, mul_assoc]

theorem cosetPriority_eq_packetMinimum [Fintype H] [Fintype K] [Nonempty K]
    [MeasurableSpace K] [MeasurableSingletonClass K] [LinearOrder K]
    (g : G) (r : ℕ) (ω : G → K)
    (z : Fiber (Subgroup.quotientMapOfLE hHL) (QuotientGroup.mk g)) :
    cosetPriority a H r ω z.val =
      FiniteOrdering.minimumStream
        (fun h : H => a.blockDigits g r (packetSites a H L hHL hLD g) ω (z, h)) := by
  have hp := FiniteOrdering.minimumStream_precomp (siteFiberEquiv H z.val).symm
    (fun u => siteStream a r ω u.val)
  simp only [blockDigits_packetSites]
  exact hp.symm

end Packets


section SelectedEvent

variable {G K : Type*} [Group G] (a : MarkerGeometry G)
  [Fintype K] [Nonempty K] [MeasurableSpace K] [MeasurableSingletonClass K] [LinearOrder K]
  (H L : Subgroup G) [Fintype H] [Finite L]
  (hHL : H ≤ L) (hLD : L ≤ a.D)
  {κ : ℕ} [NeZero κ] (hcard : Nat.card (L ⧸ H.subgroupOf L) = κ)

theorem sortedCosetChart_rank_fiber (r : ℕ) (ω : a.goodMarker (K := K))
    (b : G ⧸ L) (z : Fiber (Subgroup.quotientMapOfLE hHL) b) :
    (sortedCosetChart a H L hHL hLD hcard r ω z.val).2.val =
      FiniteOrdering.rankNat (fun w : Fiber (Subgroup.quotientMapOfLE hHL) b =>
        cosetPriority a H r ω.val w.val) z := by
  rcases z with ⟨c, hc⟩
  subst b
  rfl

/-- Exact identification with the equal-packet minimum event, on the actual
invariant conull marker domain. -/
theorem sortedCosetChart_zero_iff_packetSelected (g : G) (r : ℕ)
    (ω : a.goodMarker (K := K))
    (z : Fiber (Subgroup.quotientMapOfLE hHL) (QuotientGroup.mk g)) :
    (sortedCosetChart a H L hHL hLD hcard r ω z.val).2 = 0 ↔
      ω.val ∈ a.packetSelected g r (packetSites a H L hHL hLD g) z := by
  rw [Fin.ext_iff, sortedCosetChart_rank_fiber]
  change FiniteOrdering.rankNat
    (fun w : Fiber (Subgroup.quotientMapOfLE hHL) (QuotientGroup.mk g) =>
      cosetPriority a H r ω.val w.val) z = 0 ↔
        a.blockDigits g r (packetSites a H L hHL hLD g) ω.val ∈ FiniteOrdering.packetSet z
  have hm : (fun w : Fiber (Subgroup.quotientMapOfLE hHL) (QuotientGroup.mk g) =>
      cosetPriority a H r ω.val w.val) =
      FiniteOrdering.packetMinima (fun w h =>
        a.blockDigits g r (packetSites a H L hHL hLD g) ω.val (w, h)) := by
    funext w
    exact cosetPriority_eq_packetMinimum a H L hHL hLD g r ω.val w
  rw [hm]
  exact FiniteOrdering.packetMinima_rank_zero_iff _
    (a.blockDigits_injective_of_goodMarker g r _ ω.property) z

end SelectedEvent

section InsertionEvent

variable {G K R : Type*} [Group G] (a : MarkerGeometry G)
  [Fintype K] [Nonempty K] [MeasurableSpace K] [MeasurableSingletonClass K] [LinearOrder K]
  [CommRing R] (H L : Subgroup G) [Fintype H] [Finite L]
  (hHL : H ≤ L) (hLD : L ≤ a.D)
  {n : ℕ} (hcard : Nat.card (L ⧸ H.subgroupOf L) = n + 1)

/-- Every regroup insertion row depends only on the fresh local packet
selection event. The retained coarse coordinate is fixed in advance. -/
theorem insertionRows_sortedCosetChart (g : G) (r : ℕ)
    (ω : a.goodMarker (K := K))
    (z : Fiber (Subgroup.quotientMapOfLE hHL) (QuotientGroup.mk g)) :
    SparseRows.insertionRows (K := R)
      (Regroup.selected (sortedCosetChart a H L hHL hLD hcard r ω)) z.val =
      if ω.val ∈ a.packetSelected g r (packetSites a H L hHL hLD g) z then
        Finsupp.single (Subgroup.quotientMapOfLE hHL z.val) 1 else 0 := by
  classical
  by_cases h : ω.val ∈ a.packetSelected g r (packetSites a H L hHL hLD g) z
  · have hz := (sortedCosetChart_zero_iff_packetSelected a H L hHL hLD hcard g r ω z).2 h
    simp [Regroup.selected, hz, h, sortedCosetChart_fst, SparseRows.insertionRows]
  · have hz : (sortedCosetChart a H L hHL hLD hcard r ω z.val).2 ≠ 0 := by
      intro hz
      exact h ((sortedCosetChart_zero_iff_packetSelected a H L hHL hLD hcard g r ω z).1 hz)
    simp [Regroup.selected, hz, h, SparseRows.insertionRows]

end InsertionEvent


section RelabelPackets

variable {G K I J I' J' : Type*} [Group G] (a : MarkerGeometry G)
  [Fintype K] [Nonempty K] [MeasurableSpace K] [MeasurableSingletonClass K] [LinearOrder K]
  [Fintype I] [Fintype J] [Nonempty J] [Fintype I'] [Fintype J'] [Nonempty J']

/-- This specializes to `Fintype.equivFin` for the static Fin-index packet
interface used by the sparse tower. -/
theorem packetSelected_reindex (g : G) (r : ℕ) (sites : (I × J) ↪ a.D)
    (e : I ≃ I') (f : J ≃ J') (ω : G → K) (i : I) :
    ω ∈ a.packetSelected g r
      ((e.symm.prodCongr f.symm).toEmbedding.trans sites) (e i) ↔
      ω ∈ a.packetSelected g r sites i := by
  change a.blockDigits g r ((e.symm.prodCongr f.symm).toEmbedding.trans sites) ω ∈
    FiniteOrdering.packetSet (e i) ↔ a.blockDigits g r sites ω ∈ FiniteOrdering.packetSet i
  have hb : a.blockDigits g r ((e.symm.prodCongr f.symm).toEmbedding.trans sites) ω =
      (fun p : I' × J' => a.blockDigits g r sites ω (e.symm p.1, f.symm p.2)) := by
    funext p n
    rfl
  rw [hb]
  simpa using FiniteOrdering.packetSet_precomp e.symm f.symm
    (a.blockDigits g r sites ω) (e i)


/-- Moving the base within the same D-coset only translates the static
D-site embedding. It does not change which marker digits are read. -/
theorem blockDigits_rebase (g : G) (d : a.D) (r : ℕ) (sites : (I × J) ↪ a.D)
    (ω : G → K) :
    a.blockDigits g r (sites.trans (Equiv.mulLeft d).toEmbedding) ω =
      a.blockDigits (g * d.val) r sites ω := by
  funext p n
  simp [MarkerGeometry.blockDigits, MarkerGeometry.digits, MarkerGeometry.address, mul_assoc]

/-- A packet can be read from the fixed base of its D-component, so its
fresh sigma-algebra is the one used by the sparse-tower locality argument. -/
theorem packetSelected_changeBase (base g : G) (hbase : base⁻¹ * g ∈ a.D)
    (r : ℕ) (sites : (I × J) ↪ a.D) (ω : G → K) (i : I) :
    ω ∈ a.packetSelected base r
      (sites.trans (Equiv.mulLeft (⟨base⁻¹ * g, hbase⟩ : a.D)).toEmbedding) i ↔
      ω ∈ a.packetSelected g r sites i := by
  change a.blockDigits base r
    (sites.trans (Equiv.mulLeft (⟨base⁻¹ * g, hbase⟩ : a.D)).toEmbedding) ω ∈
      FiniteOrdering.packetSet i ↔ a.blockDigits g r sites ω ∈ FiniteOrdering.packetSet i
  rw [blockDigits_rebase]
  simp

end RelabelPackets

end CosetCoordinates
end BernoulliIso

#print axioms BernoulliIso.CosetCoordinates.sortedCosetChart_zero_iff_packetSelected
#print axioms BernoulliIso.CosetCoordinates.insertionRows_sortedCosetChart
#print axioms BernoulliIso.CosetCoordinates.packetSelected_reindex
#print axioms BernoulliIso.CosetCoordinates.packetSelected_changeBase
