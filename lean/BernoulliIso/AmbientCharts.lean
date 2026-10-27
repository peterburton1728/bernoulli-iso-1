module

public import BernoulliIso.AmbientGroup
public import BernoulliIso.InputRange
public import BernoulliIso.CosetCoordinates

/-! The finite coset charts instantiated on the actual lamplighter group. -/

@[expose] public section
noncomputable section

namespace BernoulliIso.AlgebraicInput

variable {K N I V : Type*} [Field K] [Fintype K]
  [Group N] [Countable N] [Fintype I] [Fintype V] [Nonempty I] [Nonempty V]
variable (s : AlgebraicInput K N I V)

def ambientJ (v : V) : Subgroup (Ambient.G N) := (s.J v).map (Ambient.includeN N)

def ambientJEquiv (v : V) : (s.J v) ≃* s.ambientJ v :=
  (s.J v).equivMapOfInjective (Ambient.includeN N) (Ambient.includeN_injective N)

instance ambientJ_finite (v : V) : Finite (s.ambientJ v) :=
  Finite.of_equiv (s.J v) (s.ambientJEquiv v).toEquiv

theorem ambientJ_card (v : V) : Nat.card (s.ambientJ v) = s.κ := by
  rw [← Nat.card_congr (s.ambientJEquiv v).toEquiv]
  exact s.cardJ v

theorem ambientJ_le_D (v : V) : s.ambientJ v ≤ Ambient.D N := by
  rintro g ⟨n, hn, rfl⟩
  exact Ambient.height_includeN N n

theorem ambient_commutes (_s : AlgebraicInput K N I V) (a : ℕ) :
    ∀ h ∈ Ambient.Hseq N a, ∀ n, Commute h (Ambient.includeN N n) := by
  intro h hh n
  exact (Ambient.commute_H N (Ambient.sites a) n ⟨h, hh⟩).symm

theorem ambient_join_commutes (a : ℕ) (v : V) :
    ∀ h ∈ Ambient.Hseq N a, ∀ j ∈ s.ambientJ v, Commute h j := by
  intro h hh j hj
  obtain ⟨n, hn, rfl⟩ := hj
  exact s.ambient_commutes a h hh n

theorem ambient_join_disjoint (a : ℕ) (v : V) :
    Disjoint (Ambient.Hseq N a) (s.ambientJ v) :=
  Ambient.H_disjoint_N N (Ambient.sites a) (s.J v)

instance ambient_join_finite (a : ℕ) (v : V) :
    Finite (Ambient.Hseq N a ⊔ s.ambientJ v : Subgroup (Ambient.G N)) :=
  CosetCoordinates.finite_sup_of_disjoint_commute _ _
    (s.ambient_join_commutes a v) (s.ambient_join_disjoint a v)

theorem ambient_join_le_D (a : ℕ) (v : V) :
    Ambient.Hseq N a ⊔ s.ambientJ v ≤ Ambient.D N :=
  sup_le (Ambient.H_le_D N (Ambient.sites a)) (s.ambientJ_le_D v)

theorem ambient_join_quotient_card (a : ℕ) (v : V) :
    Nat.card ((Ambient.Hseq N a ⊔ s.ambientJ v : Subgroup (Ambient.G N)) ⧸
      (Ambient.Hseq N a).subgroupOf (Ambient.Hseq N a ⊔ s.ambientJ v)) = s.κ := by
  rw [CosetCoordinates.card_quotient_sup_of_disjoint_commute _ _
    (s.ambient_join_commutes a v) (s.ambient_join_disjoint a v)]
  exact s.ambientJ_card v

variable [MeasurableSpace K] [MeasurableSingletonClass K] [LinearOrder K]

def ambientSplitCharts (a r : ℕ)
    (ω : (Ambient.markerGeometry N).goodMarker (K := K)) (v : V) :
    (Ambient.G N ⧸ Ambient.Hseq N a) ≃
      (Ambient.G N ⧸ (Ambient.Hseq N a ⊔ s.ambientJ v)) × Fin s.κ :=
  CosetCoordinates.sortedCosetChart (Ambient.markerGeometry N) _ _ le_sup_left
    (s.ambient_join_le_D a v) (s.ambient_join_quotient_card a v) r ω

theorem ambientSplitCharts_fst (a r : ℕ)
    (ω : (Ambient.markerGeometry N).goodMarker (K := K)) (v : V)
    (x : Ambient.G N ⧸ Ambient.Hseq N a) :
    (s.ambientSplitCharts a r ω v x).1 =
      Subgroup.quotientMapOfLE (show Ambient.Hseq N a ≤
        Ambient.Hseq N a ⊔ s.ambientJ v from le_sup_left) x := rfl

theorem ambientSplitCharts_covariant (a r : ℕ) (g : Ambient.G N)
    (ω : (Ambient.markerGeometry N).goodMarker (K := K)) (v : V)
    (x : Ambient.G N ⧸ Ambient.Hseq N a) :
    s.ambientSplitCharts a r
        ⟨MarkerGeometry.markerShift g ω.val,
          (Ambient.markerGeometry N).goodMarker_shift g ω.property⟩ v (g • x) =
      (g • (s.ambientSplitCharts a r ω v x).1,
        (s.ambientSplitCharts a r ω v x).2) :=
  CosetCoordinates.sortedCosetChart_covariant _ _ _ _ _ _ _ _ _ _

theorem ambientSplitCharts_symm_covariant (a r : ℕ) (g : Ambient.G N)
    (ω : (Ambient.markerGeometry N).goodMarker (K := K)) (v : V)
    (x : Ambient.G N ⧸ (Ambient.Hseq N a ⊔ s.ambientJ v)) (i : Fin s.κ) :
    (s.ambientSplitCharts a r
        ⟨MarkerGeometry.markerShift g ω.val,
          (Ambient.markerGeometry N).goodMarker_shift g ω.property⟩ v).symm (g • x, i) =
      g • (s.ambientSplitCharts a r ω v).symm (x, i) :=
  CosetCoordinates.sortedCosetChart_symm_covariant _ _ _ _ _ _ _ _ _ _ _

end BernoulliIso.AlgebraicInput
