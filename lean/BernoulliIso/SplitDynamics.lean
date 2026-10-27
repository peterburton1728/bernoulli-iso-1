module

public import BernoulliIso.ConcreteSplit

/-! Actual shift actions and covariance of the amplified algebraic split. -/

@[expose] public section
noncomputable section

namespace BernoulliIso

namespace CosetOperators

variable {G K J : Type*} [Group G] (H : Subgroup G)

def trackShift (g : G) (f : J → G ⧸ H → K) : J → G ⧸ H → K :=
  fun j x => f j (g⁻¹ • x)

def configurationAction : MulAction G (J → G ⧸ H → K) where
  smul := trackShift (K := K) (J := J) H
  one_smul f := by
    change trackShift H 1 f = f
    funext j x
    simp [trackShift]
  mul_smul g h f := by
    change trackShift H (g * h) f = trackShift H g (trackShift H h f)
    funext j x
    simp [trackShift, mul_smul]

@[simp] theorem trackShift_one (f : J → G ⧸ H → K) : trackShift H 1 f = f := by
  funext j x
  simp [trackShift]

theorem trackShift_mul (g h : G) (f : J → G ⧸ H → K) :
    trackShift H (g * h) f = trackShift H g (trackShift H h f) := by
  funext j x
  simp [trackShift, mul_smul]

end CosetOperators

namespace AlgebraicInput

variable {K N I V G : Type*} [Field K] [Finite K]
  [Group N] [Countable N] [Fintype I] [Fintype V] [Nonempty I] [Nonempty V] [Group G]
variable (s : AlgebraicInput K N I V) (H : Subgroup G) (ι : N →* G)
  (commutes : ∀ h ∈ H, ∀ n, Commute h (ι n))

theorem P_covariant (g : G) (f : V → G ⧸ H → K) :
    (s.concreteSplit H ι commutes).P (CosetOperators.trackShift H g f) =
      CosetOperators.trackShift H g ((s.concreteSplit H ι commutes).P f) :=
  CosetOperators.matrix_equivariant H ι commutes _ g f

theorem U_covariant (g : G) (f : V → G ⧸ H → K) :
    (s.concreteSplit H ι commutes).U (CosetOperators.trackShift H g f) =
      CosetOperators.trackShift H g ((s.concreteSplit H ι commutes).U f) :=
  CosetOperators.matrix_equivariant H ι commutes _ g f

theorem T_covariant (g : G) (f : I → G ⧸ H → K) :
    (s.concreteSplit H ι commutes).T (CosetOperators.trackShift H g f) =
      CosetOperators.trackShift H g ((s.concreteSplit H ι commutes).T f) :=
  CosetOperators.matrix_equivariant H ι commutes _ g f

theorem Q_covariant (g : G) (f : V → G ⧸ H → K) :
    (s.concreteSplit H ι commutes).Q (CosetOperators.trackShift H g f) =
      CosetOperators.trackShift H g ((s.concreteSplit H ι commutes).Q f) := by
  simp only [SplitData.Q_apply, s.P_covariant, s.U_covariant, s.T_covariant]
  rfl

def rangeShift (g : G) (f : (s.concreteSplit H ι commutes).P.range) :
    (s.concreteSplit H ι commutes).P.range :=
  ⟨CosetOperators.trackShift H g f.val, by
    apply ((s.concreteSplit H ι commutes).mem_P_range_iff _).mpr
    rw [s.P_covariant, ((s.concreteSplit H ι commutes).mem_P_range_iff _).mp f.property]⟩

def residualShift (g : G) (f : s.residual H ι commutes) : s.residual H ι commutes :=
  ⟨CosetOperators.trackShift H g f.val, by
    apply ((s.concreteSplit H ι commutes).mem_Q_range_iff _).mpr
    rw [s.Q_covariant, ((s.concreteSplit H ι commutes).mem_Q_range_iff _).mp f.property]⟩

def residualAction : MulAction G (s.residual H ι commutes) where
  smul := s.residualShift H ι commutes
  one_smul f := Subtype.ext (CosetOperators.trackShift_one H f.val)
  mul_smul g h f := Subtype.ext (CosetOperators.trackShift_mul H g h f.val)

theorem rangeChart_symm_apply
    (charts : ∀ v, (G ⧸ H) ≃ (G ⧸ (H ⊔ (s.J v).map ι)) × Fin s.κ)
    (f : V → G ⧸ H → K) (c : Fin s.κ) (v : V) (x : G ⧸ H) :
    ((s.rangeChart H ι commutes charts).symm f c).val v x =
      f v ((charts v).symm
        (Subgroup.quotientMapOfLE (show H ≤ H ⊔ (s.J v).map ι from le_sup_left) x, c)) :=
  rfl

theorem rangeChart_symm_covariant
    (charts charts' : ∀ v, (G ⧸ H) ≃ (G ⧸ (H ⊔ (s.J v).map ι)) × Fin s.κ)
    (g : G)
    (hcharts : ∀ v c j, (charts' v).symm (g • c, j) = g • (charts v).symm (c, j))
    (f : V → G ⧸ H → K) :
    (s.rangeChart H ι commutes charts').symm (CosetOperators.trackShift H g f) =
      fun c => s.rangeShift H ι commutes g ((s.rangeChart H ι commutes charts).symm f c) := by
  funext c
  apply Subtype.ext
  funext v x
  rw [s.rangeChart_symm_apply]
  change f v (g⁻¹ • (charts' v).symm
    (Subgroup.quotientMapOfLE (show H ≤ H ⊔ (s.J v).map ι from le_sup_left) x, c)) =
      ((s.rangeChart H ι commutes charts).symm f c).val v (g⁻¹ • x)
  rw [s.rangeChart_symm_apply]
  have hmap : Subgroup.quotientMapOfLE
      (show H ≤ H ⊔ (s.J v).map ι from le_sup_left) (g⁻¹ • x) =
        g⁻¹ • Subgroup.quotientMapOfLE
          (show H ≤ H ⊔ (s.J v).map ι from le_sup_left) x := by
    induction x using QuotientGroup.induction_on with
    | H x => rfl
  rw [hmap]
  have h := hcharts v (g⁻¹ • Subgroup.quotientMapOfLE
    (show H ≤ H ⊔ (s.J v).map ι from le_sup_left) x) c
  simp only [smul_inv_smul] at h
  rw [h, inv_smul_smul]

theorem expandedSplit_covariant
    (charts charts' : ∀ v, (G ⧸ H) ≃ (G ⧸ (H ⊔ (s.J v).map ι)) × Fin s.κ)
    (g : G)
    (hcharts : ∀ v c j, (charts' v).symm (g • c, j) = g • (charts v).symm (c, j))
    (f : V → G ⧸ H → K) :
    s.expandedSplit H ι commutes charts' (CosetOperators.trackShift H g f) =
      (CosetOperators.trackShift H g (s.expandedSplit H ι commutes charts f).1,
        (CosetOperators.trackShift H g (s.expandedSplit H ι commutes charts f).2.1,
          fun c => s.residualShift H ι commutes g
            ((s.expandedSplit H ι commutes charts f).2.2 c))) := by
  have hcopy := s.rangeChart_symm_covariant H ι commutes charts charts' g hcharts f
  have hu (c : Fin s.κ) :
      (s.concreteSplit H ι commutes).U
          (((s.rangeChart H ι commutes charts').symm
            (CosetOperators.trackShift H g f) c).val) =
        CosetOperators.trackShift H g
          ((s.concreteSplit H ι commutes).U
            (((s.rangeChart H ι commutes charts).symm f c).val)) := by
    rw [congrFun hcopy c]
    exact s.U_covariant H ι commutes g
      (((s.rangeChart H ι commutes charts).symm f c).val)
  have hq (c : Fin s.κ) :
      (s.concreteSplit H ι commutes).Q
          (((s.rangeChart H ι commutes charts').symm
            (CosetOperators.trackShift H g f) c).val) =
        CosetOperators.trackShift H g
          ((s.concreteSplit H ι commutes).Q
            (((s.rangeChart H ι commutes charts).symm f c).val)) := by
    rw [congrFun hcopy c]
    exact s.Q_covariant H ι commutes g
      (((s.rangeChart H ι commutes charts).symm f c).val)
  apply Prod.ext
  · funext v x
    exact congrFun (congrFun (hu (s.outputSlots.symm (Sum.inl v)).1)
      (s.outputSlots.symm (Sum.inl v)).2) x
  · apply Prod.ext
    · funext w x
      exact congrFun (congrFun (hu (s.outputSlots.symm (Sum.inr w)).1)
        (s.outputSlots.symm (Sum.inr w)).2) x
    · funext c
      exact Subtype.ext (hq c)

section Topology

variable [TopologicalSpace K] [IsTopologicalRing K]

theorem continuous_rangeChart_symm
    (charts : ∀ v, (G ⧸ H) ≃ (G ⧸ (H ⊔ (s.J v).map ι)) × Fin s.κ) :
    Continuous (s.rangeChart H ι commutes charts).symm := by
  apply continuous_pi
  intro c
  apply Continuous.subtype_mk
  apply continuous_pi
  intro v
  apply continuous_pi
  intro x
  exact (continuous_apply ((charts v).symm
    (Subgroup.quotientMapOfLE (show H ≤ H ⊔ (s.J v).map ι from le_sup_left) x, c))).comp
      (continuous_apply v)

theorem continuous_expandedSplit
    (charts : ∀ v, (G ⧸ H) ≃ (G ⧸ (H ⊔ (s.J v).map ι)) × Fin s.κ) :
    Continuous (s.expandedSplit H ι commutes charts) := by
  have hcopy (c : Fin s.κ) : Continuous (fun f : V → G ⧸ H → K =>
      (((s.rangeChart H ι commutes charts).symm f c).val)) :=
    continuous_subtype_val.comp ((continuous_apply c).comp
      (s.continuous_rangeChart_symm H ι commutes charts))
  apply Continuous.prodMk
  · apply continuous_pi
    intro v
    exact (continuous_apply (s.outputSlots.symm (Sum.inl v)).2).comp
      ((s.continuous_U H ι commutes).comp (hcopy (s.outputSlots.symm (Sum.inl v)).1))
  · apply Continuous.prodMk
    · apply continuous_pi
      intro w
      exact (continuous_apply (s.outputSlots.symm (Sum.inr w)).2).comp
        ((s.continuous_U H ι commutes).comp (hcopy (s.outputSlots.symm (Sum.inr w)).1))
    · apply continuous_pi
      intro c
      exact ((s.continuous_Q H ι commutes).comp (hcopy c)).subtype_mk _

end Topology
end AlgebraicInput
end BernoulliIso
